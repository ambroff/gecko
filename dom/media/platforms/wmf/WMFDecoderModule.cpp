/* -*- Mode: C++; tab-width: 2; indent-tabs-mode: nil; c-basic-offset: 2 -*- */
/* vim:set ts=2 sw=2 sts=2 et cindent: */
/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "WMFDecoderModule.h"

#include <algorithm>
#include <vector>

#include "DriverCrashGuard.h"
#include "GfxDriverInfo.h"
#include "MFTDecoder.h"
#include "MP4Decoder.h"
#include "MediaInfo.h"
#include "VPXDecoder.h"
#include "WMF.h"
#include "WMFAudioMFTManager.h"
#include "WMFMediaDataDecoder.h"
#include "WMFVideoMFTManager.h"
#include "mozilla/DebugOnly.h"
#include "mozilla/Maybe.h"
#include "mozilla/StaticMutex.h"
#include "mozilla/StaticPrefs_media.h"
#include "mozilla/WindowsVersion.h"
#include "mozilla/gfx/gfxVars.h"
#include "mozilla/mscom/EnsureMTA.h"
#include "nsComponentManagerUtils.h"
#include "nsIXULRuntime.h"
#include "nsServiceManagerUtils.h"
#include "nsWindowsHelpers.h"
#include "prsystem.h"

#ifdef MOZ_GECKO_PROFILER
#  include "ProfilerMarkerPayload.h"
#  define WFM_DECODER_MODULE_STATUS_MARKER(tag, text, markerTime)            \
    PROFILER_ADD_MARKER_WITH_PAYLOAD(tag, MEDIA_PLAYBACK, TextMarkerPayload, \
                                     (text, markerTime))
#else
#  define WFM_DECODER_MODULE_STATUS_MARKER(tag, text, markerTime)
#endif

extern const GUID CLSID_WebmMfVpxDec;

namespace mozilla {

static Atomic<bool> sDXVAEnabled(false);
static Atomic<bool> sUsableVPXMFT(false);

/* static */
already_AddRefed<PlatformDecoderModule> WMFDecoderModule::Create() {
  return MakeAndAddRef<WMFDecoderModule>();
}

WMFDecoderModule::~WMFDecoderModule() {
  if (mWMFInitialized) {
    DebugOnly<HRESULT> hr = wmf::MFShutdown();
    NS_ASSERTION(SUCCEEDED(hr), "MFShutdown failed");
  }
}

static bool IsRemoteAcceleratedCompositor(const SupportDecoderParams& aParams) {
  if (!aParams.mKnowsCompositor) {
    return false;
  }

  TextureFactoryIdentifier ident =
      aParams.mKnowsCompositor->GetTextureFactoryIdentifier();
  return ident.mParentBackend != LayersBackend::LAYERS_BASIC &&
         !ident.mUsingSoftwareWebRender &&
         ident.mParentProcessType == GeckoProcessType_GPU;
}

static bool CanCreateMFTDecoder(const GUID& aGuid) {
  // The IMFTransform interface used by MFTDecoder is documented to require to
  // run on an MTA thread.
  // https://msdn.microsoft.com/en-us/library/windows/desktop/ee892371(v=vs.85).aspx#components
  // Note: our normal SharedThreadPool task queues are initialized to MTA, but
  // the main thread (which calls in here from our CanPlayType implementation)
  // is not.
  bool canCreateDecoder = false;
  mozilla::mscom::EnsureMTA([&]() -> void {
    if (FAILED(wmf::MFStartup())) {
      return;
    }
    RefPtr<MFTDecoder> decoder(new MFTDecoder());
    canCreateDecoder = SUCCEEDED(decoder->Create(aGuid));
    wmf::MFShutdown();
  });
  return canCreateDecoder;
}

/* static */
void WMFDecoderModule::Init() {
  MOZ_DIAGNOSTIC_ASSERT(NS_IsMainThread());
  bool testForVPx;
  if (XRE_IsContentProcess()) {
    // If we're in the content process and the UseGPUDecoder pref is set, it
    // means that we've given up on the GPU process (it's been crashing) so we
    // should disable DXVA
    sDXVAEnabled = !StaticPrefs::media_gpu_process_decoder();
    // We need to test for VPX in the content process as the GPUDecoderModule
    // directly calls WMFDecoderModule::Supports in the content process.
    // This unnecessary requirement will be fixed in bug 1534815.
    testForVPx = true;
  } else if (XRE_IsGPUProcess() || XRE_IsRDDProcess()) {
    // Always allow DXVA in the GPU or RDD process.
    testForVPx = sDXVAEnabled = true;
  } else {
    // Only allow DXVA in the UI process if we aren't in e10s Firefox
    testForVPx = sDXVAEnabled = !mozilla::BrowserTabsRemoteAutostart();
  }

  sDXVAEnabled = sDXVAEnabled && gfx::gfxVars::CanUseHardwareVideoDecoding();
  testForVPx = testForVPx && gfx::gfxVars::CanUseHardwareVideoDecoding();
  if (testForVPx && StaticPrefs::media_wmf_vp9_enabled_AtStartup()) {
    gfx::WMFVPXVideoCrashGuard guard;
    if (!guard.Crashed()) {
      sUsableVPXMFT = CanCreateMFTDecoder(CLSID_WebmMfVpxDec);
    }
  }
}

/* static */
int WMFDecoderModule::GetNumDecoderThreads() {
  int32_t numCores = PR_GetNumberOfProcessors();

  // If we have more than 4 cores, let the decoder decide how many threads.
  // On an 8 core machine, WMF chooses 4 decoder threads.
  static const int WMF_DECODER_DEFAULT = -1;
  if (numCores > 4) {
    return WMF_DECODER_DEFAULT;
  }
  return std::max(numCores - 1, 1);
}

nsresult WMFDecoderModule::Startup() {
  mWMFInitialized = SUCCEEDED(wmf::MFStartup());
  return mWMFInitialized ? NS_OK : NS_ERROR_FAILURE;
}

already_AddRefed<MediaDataDecoder> WMFDecoderModule::CreateVideoDecoder(
    const CreateDecoderParams& aParams) {
  UniquePtr<WMFVideoMFTManager> manager(new WMFVideoMFTManager(
      aParams.VideoConfig(), aParams.mKnowsCompositor, aParams.mImageContainer,
      aParams.mRate.mValue, aParams.mOptions, sDXVAEnabled));

  MediaResult result = manager->Init();
  if (NS_FAILED(result)) {
    if (aParams.mError) {
      *aParams.mError = result;
    }
    nsPrintfCString markerString(
        "WMFDecoderModule::CreateVideoDecoder failed for manager with "
        "description %s with result: %s",
        manager->GetDescriptionName().get(), result.Description().get());
    LOG(markerString.get());
    WFM_DECODER_MODULE_STATUS_MARKER("WMFVDecoderCreation Failure",
                                     markerString, TimeStamp::NowUnfuzzed());
    return nullptr;
  }

  nsPrintfCString markerString(
      "WMFDecoderModule::CreateVideoDecoder success for manager with "
      "description %s",
      manager->GetDescriptionName().get());
  LOG(markerString.get());
  WFM_DECODER_MODULE_STATUS_MARKER("WMFVDecoderCreation Success", markerString,
                                   TimeStamp::NowUnfuzzed());

  RefPtr<MediaDataDecoder> decoder = new WMFMediaDataDecoder(manager.release());
  return decoder.forget();
}

already_AddRefed<MediaDataDecoder> WMFDecoderModule::CreateAudioDecoder(
    const CreateDecoderParams& aParams) {
  UniquePtr<WMFAudioMFTManager> manager(
      new WMFAudioMFTManager(aParams.AudioConfig()));

  if (!manager->Init()) {
    nsPrintfCString markerString(
        "WMFDecoderModule::CreateAudioDecoder failed for manager with "
        "description %s",
        manager->GetDescriptionName().get());
    LOG(markerString.get());
    WFM_DECODER_MODULE_STATUS_MARKER("WMFADecoderCreation Failure",
                                     markerString, TimeStamp::NowUnfuzzed());
    return nullptr;
  }

  nsPrintfCString markerString(
      "WMFDecoderModule::CreateAudioDecoder success for manager with "
      "description %s",
      manager->GetDescriptionName().get());
  LOG(markerString.get());
  WFM_DECODER_MODULE_STATUS_MARKER("WMFADecoderCreation Success", markerString,
                                   TimeStamp::NowUnfuzzed());

  RefPtr<MediaDataDecoder> decoder = new WMFMediaDataDecoder(manager.release());
  return decoder.forget();
}

template <const GUID& aGuid>
static bool CanCreateWMFDecoder() {
  static StaticMutex sMutex;
  StaticMutexAutoLock lock(sMutex);
  static Maybe<bool> result;
  if (result.isNothing()) {
    result.emplace(CanCreateMFTDecoder(aGuid));
  }
  return result.value();
}

/* static */
bool WMFDecoderModule::HasH264() {
  return CanCreateWMFDecoder<CLSID_CMSH264DecoderMFT>();
}

/* static */
bool WMFDecoderModule::HasAAC() {
  return CanCreateWMFDecoder<CLSID_CMSAACDecMFT>();
}

bool WMFDecoderModule::SupportsMimeType(
    const nsACString& aMimeType, DecoderDoctorDiagnostics* aDiagnostics) const {
  UniquePtr<TrackInfo> trackInfo = CreateTrackInfoWithMIMEType(aMimeType);
  if (!trackInfo) {
    return false;
  }
  return Supports(SupportDecoderParams(*trackInfo), aDiagnostics);
}

bool WMFDecoderModule::Supports(const SupportDecoderParams& aParams,
                                DecoderDoctorDiagnostics* aDiagnostics) const {
  // In GPU process, only support decoding if an accelerated compositor is
  // known.
  if (XRE_IsGPUProcess() && !IsRemoteAcceleratedCompositor(aParams)) {
    return false;
  }

  const auto& trackInfo = aParams.mConfig;
  const auto* videoInfo = trackInfo.GetAsVideoInfo();
  // Temporary - forces use of VPXDecoder when alpha is present.
  // Bug 1263836 will handle alpha scenario once implemented. It will shift
  // the check for alpha to PDMFactory but not itself remove the need for a
  // check.
  if (videoInfo && (!SupportsColorDepth(videoInfo->mColorDepth, aDiagnostics) ||
                    videoInfo->HasAlpha())) {
    return false;
  }

  if ((trackInfo.mMimeType.EqualsLiteral("audio/mp4a-latm") ||
       trackInfo.mMimeType.EqualsLiteral("audio/mp4")) &&
      WMFDecoderModule::HasAAC()) {
    const auto audioInfo = trackInfo.GetAsAudioInfo();
    if (audioInfo && audioInfo->mRate > 0) {
      // Supported sampling rates per:
      // https://msdn.microsoft.com/en-us/library/windows/desktop/dd742784(v=vs.85).aspx
      const std::vector<uint32_t> frequencies = {
          8000, 11025, 12000, 16000, 22050, 24000, 32000, 44100, 48000,
      };
      return std::find(frequencies.begin(), frequencies.end(),
                       audioInfo->mRate) != frequencies.end();
    }
    return true;
  }
  if (MP4Decoder::IsH264(trackInfo.mMimeType) && WMFDecoderModule::HasH264()) {
    return true;
  }
  if (trackInfo.mMimeType.EqualsLiteral("audio/mpeg") &&
      !StaticPrefs::media_ffvpx_mp3_enabled() &&
      CanCreateWMFDecoder<CLSID_CMP3DecMediaObject>()) {
    return true;
  }
  if (sUsableVPXMFT) {
    static const uint32_t VP8_USABLE_BUILD = 16287;
    if ((VPXDecoder::IsVP8(trackInfo.mMimeType) &&
         IsWindowsBuildOrLater(VP8_USABLE_BUILD)) ||
        VPXDecoder::IsVP9(trackInfo.mMimeType)) {
      return CanCreateWMFDecoder<CLSID_WebmMfVpxDec>();
    }
  }

  // Some unsupported codec.
  return false;
}

}  // namespace mozilla
