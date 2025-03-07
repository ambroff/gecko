/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

"use strict";

/**
 * Test AXIndexForChildUIElement
 */
addAccessibleTask(
  `<p id="p">Hello <a href="#" id="link">strange</a> world`,
  (browser, accDoc) => {
    let p = getNativeInterface(accDoc, "p");

    let children = p.getAttributeValue("AXChildren");
    is(children.length, 3, "p has 3 children");
    is(
      children[1].getAttributeValue("AXDOMIdentifier"),
      "link",
      "second child is link"
    );

    let index = p.getParameterizedAttributeValue(
      "AXIndexForChildUIElement",
      children[1]
    );
    is(index, 1, "link is second child");
  }
);
