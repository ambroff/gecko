/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*- */
/* vim: set ts=8 sts=2 et sw=2 tw=80: */
/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef GFX_LAYERSTYPES_H
#define GFX_LAYERSTYPES_H

#include <iosfwd>    // for ostream
#include <stdint.h>  // for uint32_t
#include <stdio.h>   // FILE

#include "Units.h"
#include "mozilla/DefineEnum.h"  // for MOZ_DEFINE_ENUM_CLASS_WITH_BASE
#include "mozilla/Maybe.h"
#include "mozilla/TimeStamp.h"  // for TimeStamp
#include "nsRegion.h"
#include "mozilla/EnumSet.h"

#ifndef MOZ_LAYERS_HAVE_LOG
#  define MOZ_LAYERS_HAVE_LOG
#endif
#define MOZ_LAYERS_LOG(_args) \
  MOZ_LOG(LayerManager::GetLog(), LogLevel::Debug, _args)
#define MOZ_LAYERS_LOG_IF_SHADOWABLE(layer, _args)             \
  do {                                                         \
    if (layer->AsShadowableLayer()) {                          \
      MOZ_LOG(LayerManager::GetLog(), LogLevel::Debug, _args); \
    }                                                          \
  } while (0)

#define INVALID_OVERLAY -1

//#define ENABLE_FRAME_LATENCY_LOG

namespace IPC {
template <typename T>
struct ParamTraits;
}  // namespace IPC

namespace mozilla {

enum class StyleBorderStyle : uint8_t;

namespace layers {

class TextureHost;

#undef NONE
#undef OPAQUE

struct LayersId {
  uint64_t mId = 0;

  bool IsValid() const { return mId != 0; }

  // Allow explicit cast to a uint64_t for now
  explicit operator uint64_t() const { return mId; }

  // Implement some operators so this class can be used as a key in
  // stdlib classes.
  bool operator<(const LayersId& aOther) const { return mId < aOther.mId; }

  bool operator==(const LayersId& aOther) const { return mId == aOther.mId; }

  bool operator!=(const LayersId& aOther) const { return !(*this == aOther); }

  friend std::ostream& operator<<(std::ostream& aStream, const LayersId& aId);

  // Helper struct that allow this class to be used as a key in
  // std::unordered_map like so:
  //   std::unordered_map<LayersId, ValueType, LayersId::HashFn> myMap;
  struct HashFn {
    std::size_t operator()(const LayersId& aKey) const {
      return std::hash<uint64_t>{}(aKey.mId);
    }
  };
};

template <typename T>
struct BaseTransactionId {
  uint64_t mId = 0;

  bool IsValid() const { return mId != 0; }

  [[nodiscard]] BaseTransactionId<T> Next() const {
    return BaseTransactionId<T>{mId + 1};
  }

  [[nodiscard]] BaseTransactionId<T> Prev() const {
    return BaseTransactionId<T>{mId - 1};
  }

  int64_t operator-(const BaseTransactionId<T>& aOther) const {
    return mId - aOther.mId;
  }

  // Allow explicit cast to a uint64_t for now
  explicit operator uint64_t() const { return mId; }

  bool operator<(const BaseTransactionId<T>& aOther) const {
    return mId < aOther.mId;
  }

  bool operator<=(const BaseTransactionId<T>& aOther) const {
    return mId <= aOther.mId;
  }

  bool operator>(const BaseTransactionId<T>& aOther) const {
    return mId > aOther.mId;
  }

  bool operator>=(const BaseTransactionId<T>& aOther) const {
    return mId >= aOther.mId;
  }

  bool operator==(const BaseTransactionId<T>& aOther) const {
    return mId == aOther.mId;
  }

  bool operator!=(const BaseTransactionId<T>& aOther) const {
    return mId != aOther.mId;
  }
};

class TransactionIdType {};
typedef BaseTransactionId<TransactionIdType> TransactionId;

struct LayersObserverEpoch {
  uint64_t mId;

  [[nodiscard]] LayersObserverEpoch Next() const {
    return LayersObserverEpoch{mId + 1};
  }

  bool operator<=(const LayersObserverEpoch& aOther) const {
    return mId <= aOther.mId;
  }

  bool operator>=(const LayersObserverEpoch& aOther) const {
    return mId >= aOther.mId;
  }

  bool operator==(const LayersObserverEpoch& aOther) const {
    return mId == aOther.mId;
  }

  bool operator!=(const LayersObserverEpoch& aOther) const {
    return mId != aOther.mId;
  }
};

// CompositionOpportunityId is a counter that goes up every time we have an
// opportunity to composite. It increments even on no-op composites (if nothing
// has changed) and while compositing is paused. It does not skip values if a
// composite is delayed. It is meaningful per window.
// This counter is used to differentiate intentionally-skipped video frames from
// unintentionally-skipped video frames: If CompositionOpportunityIds are
// observed by the video in +1 increments, then the video was onscreen the
// entire time and compositing was not paused. But if gaps in
// CompositionOpportunityIds are observed, that must mean that the video was not
// considered during some composition opportunities, because compositing was
// paused or because the video was not part of the on-screen scene.
class CompositionOpportunityType {};
typedef BaseTransactionId<CompositionOpportunityType> CompositionOpportunityId;

enum class LayersBackend : int8_t {
  LAYERS_NONE = 0,
  LAYERS_BASIC,
  LAYERS_OPENGL,
  LAYERS_D3D11,
  LAYERS_CLIENT,
  LAYERS_WR,
  LAYERS_LAST
};

const char* GetLayersBackendName(LayersBackend aBackend);

enum class TextureType : int8_t {
  Unknown = 0,
  D3D11,
  DIB,
  X11,
  MacIOSurface,
  AndroidNativeWindow,
  AndroidHardwareBuffer,
  DMABUF,
  EGLImage,
  Last
};

enum class BufferMode : int8_t { BUFFER_NONE, BUFFERED };

enum class DrawRegionClip : int8_t { DRAW, NONE };

enum class SurfaceMode : int8_t {
  SURFACE_NONE = 0,
  SURFACE_OPAQUE,
  SURFACE_SINGLE_CHANNEL_ALPHA,
  SURFACE_COMPONENT_ALPHA
};

// clang-format off
MOZ_DEFINE_ENUM_CLASS_WITH_BASE(
  ScaleMode, int8_t, (
    SCALE_NONE,
    STRETCH
// Unimplemented - PRESERVE_ASPECT_RATIO_CONTAIN
));
// clang-format on

struct EventRegions {
  // The hit region for a layer contains all areas on the layer that are
  // sensitive to events. This region is an over-approximation and may
  // contain regions that are not actually sensitive, but any such regions
  // will be included in the mDispatchToContentHitRegion.
  nsIntRegion mHitRegion;
  // The mDispatchToContentHitRegion for a layer contains all areas for
  // which the main-thread must be consulted before responding to events.
  // This region will be a subregion of mHitRegion.
  nsIntRegion mDispatchToContentHitRegion;

  // The following regions represent the touch-action areas of this layer.
  // All of these regions are approximations to the true region, but any
  // variance between the approximation and the true region is guaranteed
  // to be included in the mDispatchToContentHitRegion.
  nsIntRegion mNoActionRegion;
  nsIntRegion mHorizontalPanRegion;
  nsIntRegion mVerticalPanRegion;

  // Set to true if events targeting the dispatch-to-content region
  // require target confirmation.
  // See CompositorHitTestFlags::eRequiresTargetConfirmation.
  // We don't bother tracking a separate region for this (which would
  // be a sub-region of the dispatch-to-content region), because the added
  // overhead of region computations is not worth it, and because
  // EventRegions are going to be deprecated anyways.
  bool mDTCRequiresTargetConfirmation;

  EventRegions();

  explicit EventRegions(nsIntRegion aHitRegion);

  // This constructor takes the maybe-hit region and uses it to update the
  // hit region and dispatch-to-content region. It is useful from converting
  // from the display item representation to the layer representation.
  EventRegions(const nsIntRegion& aHitRegion,
               const nsIntRegion& aMaybeHitRegion,
               const nsIntRegion& aDispatchToContentRegion,
               const nsIntRegion& aNoActionRegion,
               const nsIntRegion& aHorizontalPanRegion,
               const nsIntRegion& aVerticalPanRegion,
               bool aDTCRequiresTargetConfirmation);

  bool operator==(const EventRegions& aRegions) const;
  bool operator!=(const EventRegions& aRegions) const;
  friend std::ostream& operator<<(std::ostream& aStream, const EventRegions& e);

  void ApplyTranslationAndScale(float aXTrans, float aYTrans, float aXScale,
                                float aYScale);
  void Transform(const gfx::Matrix4x4& aTransform);
  void OrWith(const EventRegions& aOther);

  bool IsEmpty() const;
  void SetEmpty();
};

// Bit flags that go on a RefLayer and override the
// event regions in the entire subtree below. This is needed for propagating
// various flags across processes since the child-process layout code doesn't
// know about parent-process listeners or CSS rules.
enum EventRegionsOverride {
  // The default, no flags set
  NoOverride = 0,
  // Treat all hit regions in the subtree as dispatch-to-content
  ForceDispatchToContent = (1 << 0),
  // Treat all hit regions in the subtree as empty
  ForceEmptyHitRegion = (1 << 1),
  // OR union of all valid bit flags, for use in BitFlagsEnumSerializer
  ALL_BITS = (1 << 2) - 1
};

MOZ_ALWAYS_INLINE EventRegionsOverride operator|(EventRegionsOverride a,
                                                 EventRegionsOverride b) {
  return (EventRegionsOverride)((int)a | (int)b);
}

MOZ_ALWAYS_INLINE EventRegionsOverride& operator|=(EventRegionsOverride& a,
                                                   EventRegionsOverride b) {
  a = a | b;
  return a;
}

// Flags used as an argument to functions that dump textures.
enum TextureDumpMode {
  Compress,      // dump texture with LZ4 compression
  DoNotCompress  // dump texture uncompressed
};

typedef uint32_t TouchBehaviorFlags;

// Some specialized typedefs of Matrix4x4Typed.
typedef gfx::Matrix4x4Typed<LayerPixel, CSSTransformedLayerPixel>
    CSSTransformMatrix;
// Several different async transforms can contribute to a layer's transform
// (specifically, an async animation can contribute a transform, and each APZC
// that scrolls a layer can contribute async scroll/zoom and overscroll
// transforms).
// To try to model this with typed units, we represent individual async
// transforms as ParentLayer -> ParentLayer transforms (aliased as
// AsyncTransformComponentMatrix), and we represent the product of all of them
// as a CSSTransformLayer -> ParentLayer transform (aliased as
// AsyncTransformMatrix). To create an AsyncTransformMatrix from component
// matrices, a ViewAs operation is needed. A MultipleAsyncTransforms
// PixelCastJustification is provided for this purpose.
typedef gfx::Matrix4x4Typed<ParentLayerPixel, ParentLayerPixel>
    AsyncTransformComponentMatrix;
typedef gfx::Matrix4x4Typed<CSSTransformedLayerPixel, ParentLayerPixel>
    AsyncTransformMatrix;

typedef Array<gfx::DeviceColor, 4> BorderColors;
typedef Array<LayerSize, 4> BorderCorners;
typedef Array<LayerCoord, 4> BorderWidths;
typedef Array<StyleBorderStyle, 4> BorderStyles;

typedef Maybe<LayerRect> MaybeLayerRect;

// This is used to communicate Layers across IPC channels. The Handle is valid
// for layers in the same PLayerTransaction. Handles are created by
// ClientLayerManager, and are cached in LayerTransactionParent on first use.
class LayerHandle final {
  friend struct IPC::ParamTraits<mozilla::layers::LayerHandle>;

 public:
  LayerHandle() : mHandle(0) {}
  LayerHandle(const LayerHandle& aOther) = default;
  explicit LayerHandle(uint64_t aHandle) : mHandle(aHandle) {}
  bool IsValid() const { return mHandle != 0; }
  explicit operator bool() const { return IsValid(); }
  bool operator==(const LayerHandle& aOther) const {
    return mHandle == aOther.mHandle;
  }
  uint64_t Value() const { return mHandle; }

 private:
  uint64_t mHandle;
};

// This is used to communicate Compositables across IPC channels. The Handle is
// valid for layers in the same PLayerTransaction or PImageBridge. Handles are
// created by ClientLayerManager or ImageBridgeChild, and are cached in the
// parent side on first use.
class CompositableHandle final {
  friend struct IPC::ParamTraits<mozilla::layers::CompositableHandle>;

 public:
  CompositableHandle() : mHandle(0) {}
  CompositableHandle(const CompositableHandle& aOther) = default;
  explicit CompositableHandle(uint64_t aHandle) : mHandle(aHandle) {}
  bool IsValid() const { return mHandle != 0; }
  explicit operator bool() const { return IsValid(); }
  bool operator==(const CompositableHandle& aOther) const {
    return mHandle == aOther.mHandle;
  }
  uint64_t Value() const { return mHandle; }

 private:
  uint64_t mHandle;
};

// clang-format off
MOZ_DEFINE_ENUM_CLASS_WITH_BASE(ScrollDirection, uint32_t, (
  eVertical,
  eHorizontal
));

typedef EnumSet<ScrollDirection> ScrollDirections;

constexpr ScrollDirections EitherScrollDirection(ScrollDirection::eVertical,ScrollDirection::eHorizontal);
constexpr ScrollDirections HorizontalScrollDirection(ScrollDirection::eHorizontal);
constexpr ScrollDirections VerticalScollDirection(ScrollDirection::eVertical);


MOZ_DEFINE_ENUM_CLASS_WITH_BASE(CompositionPayloadType, uint8_t, (
  /**
   * A |CompositionPayload| with this type indicates a key press happened
   * before composition and will be used to determine latency between key press
   * and presentation in |mozilla::Telemetry::KEYPRESS_PRESENT_LATENCY|
   */
  eKeyPress,

  /**
   * A |CompositionPayload| with this type indicates that an APZ scroll event
   * occurred that will be included in the composition.
   */
  eAPZScroll,

  /**
   * A |CompositionPayload| with this type indicates that an APZ pinch-to-zoom
   * event occurred that will be included in the composition.
   */
  eAPZPinchZoom,

  /**
   * A |CompositionPayload| with this type indicates that content was painted
   * that will be included in the composition.
   */
  eContentPaint
));
// clang-format on

extern const char* kCompositionPayloadTypeNames[kCompositionPayloadTypeCount];

struct CompositionPayload {
  bool operator==(const CompositionPayload& aOther) const {
    return mType == aOther.mType && mTimeStamp == aOther.mTimeStamp;
  }
  /* The type of payload that is in this composition */
  CompositionPayloadType mType;
  /* When this payload was generated */
  TimeStamp mTimeStamp;
};

}  // namespace layers
}  // namespace mozilla

#endif /* GFX_LAYERSTYPES_H */
