/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "nsPrinterListCUPS.h"

#include "mozilla/IntegerRange.h"
#include "nsCUPSShim.h"
#include "nsPrinterCUPS.h"
#include "nsString.h"
#include "prenv.h"

static nsCUPSShim sCupsShim;
using PrinterInfo = nsPrinterListBase::PrinterInfo;

/**
 * Retrieves a human-readable name for the printer from CUPS.
 * https://www.cups.org/doc/cupspm.html#basic-destination-information
 */
static void GetDisplayNameForPrinter(const cups_dest_t& aDest,
                                     nsAString& aName) {
// macOS clients expect prettified printer names
// while GTK clients expect non-prettified names.
// If you change this, please change NamedPrinter accordingly.
#ifdef XP_MACOSX
  const char* displayName =
      sCupsShim.cupsGetOption("printer-info", aDest.num_options, aDest.options);
  if (displayName) {
    CopyUTF8toUTF16(MakeStringSpan(displayName), aName);
  }
#endif
}

NS_IMETHODIMP
nsPrinterListCUPS::InitPrintSettingsFromPrinter(
    const nsAString& aPrinterName, nsIPrintSettings* aPrintSettings) {
  MOZ_ASSERT(aPrintSettings);

  // Set a default file name.
  nsAutoString filename;
  nsresult rv = aPrintSettings->GetToFileName(filename);
  if (NS_FAILED(rv) || filename.IsEmpty()) {
    const char* path = PR_GetEnv("PWD");
    if (!path) {
      path = PR_GetEnv("HOME");
    }

    if (path) {
      CopyUTF8toUTF16(mozilla::MakeStringSpan(path), filename);
      filename.AppendLiteral("/mozilla.pdf");
    } else {
      filename.AssignLiteral("mozilla.pdf");
    }

    aPrintSettings->SetToFileName(filename);
  }

  aPrintSettings->SetIsInitializedFromPrinter(true);
  return NS_OK;
}

static int CupsDestCallback(void* user_data, unsigned aFlags,
                            cups_dest_t* aDest) {
  MOZ_ASSERT(user_data);
  nsTArray<PrinterInfo>* printerInfoList =
      reinterpret_cast<nsTArray<PrinterInfo>*>(user_data);

  cups_dest_t* ownedDest = nullptr;
  mozilla::DebugOnly<const int> numCopied =
      sCupsShim.cupsCopyDest(aDest, 0, &ownedDest);
  MOZ_ASSERT(numCopied == 1);

  nsString name;
  GetDisplayNameForPrinter(*aDest, name);

  printerInfoList->AppendElement(PrinterInfo{std::move(name), ownedDest});

  return aFlags == CUPS_DEST_FLAGS_MORE ? 1 : 0;
}

nsTArray<PrinterInfo> nsPrinterListCUPS::Printers() const {
  if (!sCupsShim.EnsureInitialized()) {
    return {};
  }

  nsTArray<PrinterInfo> printerInfoList;
  if (!sCupsShim.cupsEnumDests(
          CUPS_DEST_FLAGS_NONE,
          0 /* timeout, 0 timeout shouldn't be a problem since we are masking
               CUPS_PRINTER_DISCOVERED */
          ,
          nullptr /* cancel* */, CUPS_PRINTER_LOCAL,
          CUPS_PRINTER_FAX | CUPS_PRINTER_SCANNER | CUPS_PRINTER_DISCOVERED,
          &CupsDestCallback, &printerInfoList)) {
    return {};
  }

  return printerInfoList;
}

RefPtr<nsIPrinter> nsPrinterListCUPS::CreatePrinter(PrinterInfo aInfo) const {
  return mozilla::MakeRefPtr<nsPrinterCUPS>(
      mCommonPaperInfo, sCupsShim, std::move(aInfo.mName),
      static_cast<cups_dest_t*>(aInfo.mCupsHandle));
}

Maybe<PrinterInfo> nsPrinterListCUPS::PrinterByName(
    nsString aPrinterName) const {
  Maybe<PrinterInfo> rv;
  if (!sCupsShim.EnsureInitialized()) {
    return rv;
  }

  // Will contain the printer, if found. This must be fully owned, and not a
  // member of another array of printers.
  cups_dest_t* printer = nullptr;

#ifdef XP_MACOSX
  // On OS X the printer name given to this function is the readable/display
  // name and not the CUPS name, so we iterate over all the printers for now.
  // See bug 1659807 for one approach to improve perf here.
  {
    nsAutoCString printerName;
    CopyUTF16toUTF8(aPrinterName, printerName);
    cups_dest_t* printers = nullptr;
    const auto numPrinters = sCupsShim.cupsGetDests(&printers);
    for (auto i : mozilla::IntegerRange(0, numPrinters)) {
      const char* const displayName = sCupsShim.cupsGetOption(
          "printer-info", printers[i].num_options, printers[i].options);
      if (printerName == displayName) {
        // The second arg to sCupsShim.cupsCopyDest is called num_dests, but
        // it actually copies num_dests + 1 elements.
        sCupsShim.cupsCopyDest(printers + i, 0, &printer);
        break;
      }
    }
    sCupsShim.cupsFreeDests(numPrinters, printers);
  }
#else
  // On GTK, we only ever show the CUPS name of printers, so we can use
  // cupsGetNamedDest directly.
  {
    const auto printerName = NS_ConvertUTF16toUTF8(aPrinterName);
    printer = sCupsShim.cupsGetNamedDest(CUPS_HTTP_DEFAULT, printerName.get(),
                                         nullptr);
  }
#endif

  if (printer) {
    // Since the printer name had to be passed by-value, we can move the
    // name from that.
    rv.emplace(PrinterInfo{std::move(aPrinterName), printer});
  }
  return rv;
}

Maybe<PrinterInfo> nsPrinterListCUPS::PrinterBySystemName(
    nsString aPrinterName) const {
  Maybe<PrinterInfo> rv;
  if (!sCupsShim.EnsureInitialized()) {
    return rv;
  }

  const auto printerName = NS_ConvertUTF16toUTF8(aPrinterName);
  if (cups_dest_t* const printer = sCupsShim.cupsGetNamedDest(
          CUPS_HTTP_DEFAULT, printerName.get(), nullptr)) {
    rv.emplace(PrinterInfo{std::move(aPrinterName), printer});
  }
  return rv;
}

nsresult nsPrinterListCUPS::SystemDefaultPrinterName(nsAString& aName) const {
  aName.Truncate();

  if (!sCupsShim.EnsureInitialized()) {
    return NS_ERROR_FAILURE;
  }

  // Passing in nullptr for the name will return the default, if any.
  cups_dest_t* dest =
      sCupsShim.cupsGetNamedDest(CUPS_HTTP_DEFAULT, /* name */ nullptr,
                                 /* instance */ nullptr);
  if (!dest) {
    return NS_OK;
  }

  GetDisplayNameForPrinter(*dest, aName);
  if (aName.IsEmpty()) {
    CopyUTF8toUTF16(mozilla::MakeStringSpan(dest->name), aName);
  }

  sCupsShim.cupsFreeDests(1, dest);
  return NS_OK;
}
