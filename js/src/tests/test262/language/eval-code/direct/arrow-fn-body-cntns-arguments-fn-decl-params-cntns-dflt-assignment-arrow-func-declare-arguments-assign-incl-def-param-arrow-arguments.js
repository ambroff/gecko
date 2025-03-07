// This file was procedurally generated from the following sources:
// - src/direct-eval-code/arrow-func-declare-arguments-assign-incl-def-param-arrow-arguments.case
// - src/direct-eval-code/arrow-func/fn-body-cntns-arguments-fn-decl-params-cntns-dflt-assignment.template
/*---
description: Declare "arguments" and assign to it in direct eval code (Declare |arguments| when the function body contains an |arguments| function declaration.)
esid: sec-evaldeclarationinstantiation
flags: [generated, noStrict]
---*/

const oldArguments = globalThis.arguments;
let count = 0;
const f = (p = eval("var arguments = 'param'"), q = () => arguments) => {
  function arguments() {}
  assert.sameValue(typeof arguments, "function");
  assert.sameValue(q(), "param");
  count++;
}
f();
assert.sameValue(count, 1);
assert.sameValue(globalThis.arguments, oldArguments, "globalThis.arguments unchanged");

reportCompare(0, 0);
