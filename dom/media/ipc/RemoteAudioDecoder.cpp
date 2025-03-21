/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*- */
/* vim: set ts=8 sts=2 et sw=2 tw=80: */
/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
#include "RemoteAudioDecoder.h"

#include "MediaDataDecoderProxy.h"
#include "PDMFactory.h"
#include "RemoteDecoderManagerChild.h"
#include "RemoteDecoderManagerParent.h"
#include "mozilla/PodOperations.h"

namespace mozilla {

RemoteAudioDecoderChild::RemoteAudioDecoderChild() : RemoteDecoderChild() {}

MediaResult RemoteAudioDecoderChild::ProcessOutput(
    DecodedOutputIPDL&& aDecodedData) {
  AssertOnManagerThread();

  MOZ_ASSERT(aDecodedData.type() == DecodedOutputIPDL::TArrayOfRemoteAudioData);
  RefPtr<ArrayOfRemoteAudioData> arrayData =
      aDecodedData.get_ArrayOfRemoteAudioData();

  for (size_t i = 0; i < arrayData->Count(); i++) {
    RefPtr<AudioData> data = arrayData->ElementAt(i);
    if (!data) {
      // OOM
      return MediaResult(NS_ERROR_OUT_OF_MEMORY, __func__);
    }
    mDecodedData.AppendElement(data);
  }
  return NS_OK;
}

MediaResult RemoteAudioDecoderChild::InitIPDL(
    const AudioInfo& aAudioInfo,
    const CreateDecoderParams::OptionSet& aOptions) {
  RefPtr<RemoteDecoderManagerChild> manager =
      RemoteDecoderManagerChild::GetSingleton(RemoteDecodeIn::RddProcess);

  // The manager isn't available because RemoteDecoderManagerChild has been
  // initialized with null end points and we don't want to decode video on RDD
  // process anymore. Return false here so that we can fallback to other PDMs.
  if (!manager) {
    return MediaResult(NS_ERROR_DOM_MEDIA_FATAL_ERR,
                       RESULT_DETAIL("RemoteDecoderManager is not available."));
  }

  if (!manager->CanSend()) {
    return MediaResult(NS_ERROR_DOM_MEDIA_FATAL_ERR,
                       RESULT_DETAIL("RemoteDecoderManager unable to send."));
  }

  mIPDLSelfRef = this;
  bool success = false;
  nsCString errorDescription;
  Unused << manager->SendPRemoteDecoderConstructor(
      this, aAudioInfo, aOptions, Nothing(), &success, &errorDescription);
  return success ? MediaResult(NS_OK)
                 : MediaResult(NS_ERROR_DOM_MEDIA_FATAL_ERR, errorDescription);
}

RemoteAudioDecoderParent::RemoteAudioDecoderParent(
    RemoteDecoderManagerParent* aParent, const AudioInfo& aAudioInfo,
    const CreateDecoderParams::OptionSet& aOptions,
    nsISerialEventTarget* aManagerThread, TaskQueue* aDecodeTaskQueue,
    bool* aSuccess, nsCString* aErrorDescription)
    : RemoteDecoderParent(aParent, aManagerThread, aDecodeTaskQueue),
      mAudioInfo(aAudioInfo) {
  MediaResult error(NS_OK);
  auto params = CreateDecoderParams{
      mAudioInfo, aOptions, CreateDecoderParams::NoWrapper(true), &error};

  auto& factory = aParent->EnsurePDMFactory();
  RefPtr<MediaDataDecoder> decoder = factory.CreateDecoder(params);

  if (NS_FAILED(error)) {
    MOZ_ASSERT(aErrorDescription);
    *aErrorDescription = error.Description();
  }

  if (decoder) {
    mDecoder = new MediaDataDecoderProxy(decoder.forget(),
                                         do_AddRef(mDecodeTaskQueue.get()));
  }

  *aSuccess = !!mDecoder;
}

MediaResult RemoteAudioDecoderParent::ProcessDecodedData(
    MediaDataDecoder::DecodedData&& aData, DecodedOutputIPDL& aDecodedData) {
  MOZ_ASSERT(OnManagerThread());

  // Converted array to array of RefPtr<AudioData>
  nsTArray<RefPtr<AudioData>> data(aData.Length());
  for (auto&& element : aData) {
    MOZ_ASSERT(element->mType == MediaData::Type::AUDIO_DATA,
               "Can only decode audio using RemoteAudioDecoderParent!");
    AudioData* audio = static_cast<AudioData*>(element.get());
    data.AppendElement(audio);
  }
  auto array = MakeRefPtr<ArrayOfRemoteAudioData>();
  if (!array->Fill(std::move(data),
                   [&](size_t aSize) { return AllocateBuffer(aSize); })) {
    return MediaResult(
        NS_ERROR_OUT_OF_MEMORY,
        "Failed in RemoteAudioDecoderParent::ProcessDecodedData");
  }
  aDecodedData = std::move(array);
  return NS_OK;
}

}  // namespace mozilla
