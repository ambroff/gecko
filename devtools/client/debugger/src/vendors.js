/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at <http://mozilla.org/MPL/2.0/>. */

// @flow

/**
 * Vendors.js is a file used to bundle and expose all dependencies needed to run
 * the transpiled debugger modules when running in Firefox.
 *
 * To make transpilation easier, a vendored module should always be imported in
 * same way:
 * - always with destructuring (import { a } from "modA";)
 * - always without destructuring (import modB from "modB")
 *
 * Both are fine, but cannot be mixed for the same module.
 */

// $FlowIgnore
import * as devtoolsEnvironment from "devtools-environment";
import * as devtoolsUtils from "devtools-utils";
import * as fuzzaldrinPlus from "fuzzaldrin-plus";
import * as transition from "react-transition-group/Transition";
import * as reactAriaComponentsTabs from "react-aria-components/src/tabs";

// Modules imported without destructuring
import classnames from "classnames";
import devtoolsSplitter from "devtools-splitter";
import move from "lodash-move";

// We cannot directly export literals containing special characters
// (eg. "my-module/Test") which is why they are nested in "vendored".
// The keys of the vendored object should match the module names
// !!! Should remain synchronized with .babel/transform-mc.js !!!
export const vendored = {
  classnames,
  "devtools-environment": devtoolsEnvironment,
  "devtools-splitter": devtoolsSplitter,
  "devtools-utils": devtoolsUtils,
  "fuzzaldrin-plus": fuzzaldrinPlus,
  "lodash-move": move,
  "react-aria-components/src/tabs": reactAriaComponentsTabs,
  "react-transition-group/Transition": transition,
};
