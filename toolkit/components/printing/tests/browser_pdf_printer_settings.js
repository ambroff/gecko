/* Any copyright is dedicated to the Public Domain.
   http://creativecommons.org/publicdomain/zero/1.0/ */

"use strict";

add_task(async function testPDFPrinterSettings() {
  await PrintHelper.withTestPage(async helper => {
    // Set some bad prefs
    await SpecialPowers.pushPrefEnv({
      set: [
        ["print.print_to_file", false],
        ["print.print_in_color", false],
        ["print.printer_Mozilla_Save_to_PDF.print_to_file", false],
        ["print.printer_Mozilla_Save_to_PDF.print_in_color", false],
      ],
    });

    await helper.startPrint();
    await helper.awaitAnimationFrame();

    // Verify we end up with sane settings
    let { settings } = helper;

    ok(
      settings.printToFile,
      "Check the current settings have a truthy printToFile for the PDF printer"
    );
    ok(
      settings.printInColor,
      "Check the current settings have a truthy printInColor for the PDF printer"
    );
    is(
      settings.outputFormat,
      Ci.nsIPrintSettings.kOutputFormatPDF,
      "The PDF printer has the correct outputFormat"
    );

    await helper.closeDialog();
    await SpecialPowers.popPrefEnv();
  });
});

add_task(async function testPDFCancel() {
  await PrintHelper.withTestPage(async helper => {
    await helper.startPrint();
    helper.mockFilePickerCancel();
    let form = helper.doc.querySelector("#print");
    let getDisabledStates = () => [...form.elements].map(el => el.disabled);
    let initialDisabledStates = getDisabledStates();

    ok(
      initialDisabledStates.some(disabled => !disabled),
      "At least one enabled form element before submitting"
    );
    let getShownDisabledStates = new Promise(resolve => {
      MockFilePicker.showCallback = () => resolve(getDisabledStates());
    });

    EventUtils.sendKey("return", helper.win);

    let shownDisabledStates = await getShownDisabledStates;
    ok(shownDisabledStates, "Got disabled states while shown");
    ok(
      shownDisabledStates.every(disabled => disabled),
      "All elements were disabled when showing picker"
    );

    let saveButton = form.querySelector("#print-button");
    await BrowserTestUtils.waitForAttributeRemoval("disabled", saveButton);
    helper.assertDialogOpen();

    is(
      getDisabledStates().every(
        (disabledState, index) => disabledState === initialDisabledStates[index]
      ),
      true,
      "Previous disabled states match after returning to preview"
    );

    // Close the dialog with Escape.
    await helper.withClosingFn(() => {
      EventUtils.synthesizeKey("VK_ESCAPE", {}, helper.win);
    });

    helper.assertDialogClosed();
  });
});
