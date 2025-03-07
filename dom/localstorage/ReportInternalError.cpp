/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*- */
/* vim: set ts=8 sts=2 et sw=2 tw=80: */
/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "ReportInternalError.h"

#include <cinttypes>
#include "nsContentUtils.h"
#include "nsPrintfCString.h"
#include "nsString.h"

namespace mozilla {
namespace dom {
namespace localstorage {

void ReportInternalError(const char* aFile, uint32_t aLine, const char* aStr) {
  // Get leaf of file path
  for (const char* p = aFile; *p; ++p) {
    if (*p == '/' && *(p + 1)) {
      aFile = p + 1;
    }
  }

  nsContentUtils::LogSimpleConsoleError(
      NS_ConvertUTF8toUTF16(
          nsPrintfCString("LocalStorage %s: %s:%" PRIu32, aStr, aFile, aLine)),
      "localstorage", false, true /* Internal errors are chrome context only*/);
}

}  // namespace localstorage
}  // namespace dom
}  // namespace mozilla
