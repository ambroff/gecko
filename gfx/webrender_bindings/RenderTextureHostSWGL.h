/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*- */
/* vim: set ts=8 sts=2 et sw=2 tw=80: */
/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef MOZILLA_GFX_RENDERTEXTUREHOSTSWGL_H
#define MOZILLA_GFX_RENDERTEXTUREHOSTSWGL_H

#include "RenderTextureHost.h"

namespace mozilla {
namespace wr {

class RenderTextureHostSWGL : public RenderTextureHost {
 public:
  RenderTextureHostSWGL() {}

  wr::WrExternalImage LockSWGL(uint8_t aChannelIndex, void* aContext,
                               wr::ImageRendering aRendering) override;

  void UnlockSWGL() override;

  RenderTextureHostSWGL* AsRenderTextureHostSWGL() override { return this; }

  virtual size_t GetPlaneCount() const = 0;

  virtual gfx::SurfaceFormat GetFormat() const {
    return gfx::SurfaceFormat::UNKNOWN;
  }

  virtual gfx::ColorDepth GetColorDepth() const {
    return gfx::ColorDepth::UNKNOWN;
  }

  virtual gfx::YUVColorSpace GetYUVColorSpace() const {
    return gfx::YUVColorSpace::UNKNOWN;
  }

  struct PlaneInfo {
    explicit PlaneInfo(GLuint aTexture) : mTexture(aTexture) {}

    GLuint mTexture = 0;
    void* mData = nullptr;
    int32_t mStride = 0;
    gfx::IntSize mSize;
  };

  virtual bool MapPlane(uint8_t aChannelIndex, PlaneInfo& aPlaneInfo) = 0;

  virtual void UnmapPlanes() = 0;

  // Lock this texture host as an attached external image for a SWGL compositor
  // surface. See swgl_bindings.rs for a description of the resulting
  // WrSWGLCompositeSurfaceInfo. This is paired with a call to UnlockSWGL when
  // composition is done.
  bool LockSWGLCompositeSurface(void* aContext,
                                wr::WrSWGLCompositeSurfaceInfo* aInfo);

 protected:
  bool mLocked = false;
  void* mContext = nullptr;
  std::vector<PlaneInfo> mPlanes;

  bool SetContext(void* aContext);

  bool UpdatePlanes(wr::ImageRendering aRendering);

  void CleanupPlanes();

  virtual ~RenderTextureHostSWGL();
};

}  // namespace wr
}  // namespace mozilla

#endif  // MOZILLA_GFX_RENDERTEXTUREHOSTSWGL_H
