const { element, ReferenceStore, WebElement } = ChromeUtils.import(
  "chrome://marionette/content/element.js"
);
const { evaluate } = ChromeUtils.import(
  "chrome://marionette/content/evaluate.js"
);

const SVG_NS = "http://www.w3.org/2000/svg";
const XHTML_NS = "http://www.w3.org/1999/xhtml";
const XUL_NS = "http://www.mozilla.org/keymaster/gatekeeper/there.is.only.xul";

class Element {
  constructor(tagName, attrs = {}) {
    this.tagName = tagName;
    this.localName = tagName;

    // Set default properties
    this.isConnected = true;
    this.ownerDocument = {};
    this.ownerGlobal = { document: this.ownerDocument };

    for (let attr in attrs) {
      this[attr] = attrs[attr];
    }
  }

  get nodeType() {
    return 1;
  }
  get ELEMENT_NODE() {
    return 1;
  }
}

class DOMElement extends Element {
  constructor(tagName, attrs = {}) {
    super(tagName, attrs);
    this.namespaceURI = XHTML_NS;
  }
}

class SVGElement extends Element {
  constructor(tagName, attrs = {}) {
    super(tagName, attrs);
    this.namespaceURI = SVG_NS;
  }
}

class XULElement extends Element {
  constructor(tagName, attrs = {}) {
    super(tagName, attrs);
    this.namespaceURI = XUL_NS;
  }
}

const domEl = new DOMElement("p");
const svgEl = new SVGElement("rect");
const xulEl = new XULElement("browser");

const domWebEl = WebElement.from(domEl);
const svgWebEl = WebElement.from(svgEl);
const xulWebEl = WebElement.from(xulEl);

const domElId = { id: 1, browsingContextId: 4, webElRef: domWebEl.toJSON() };
const svgElId = { id: 2, browsingContextId: 5, webElRef: svgWebEl.toJSON() };
const xulElId = { id: 3, browsingContextId: 6, webElRef: xulWebEl.toJSON() };

const seenEls = new element.Store();
const elementIdCache = new element.ReferenceStore();

add_test(function test_toJSON_types() {
  // null
  equal(null, evaluate.toJSON(undefined));
  equal(null, evaluate.toJSON(null));

  // primitives
  equal(true, evaluate.toJSON(true));
  equal(42, evaluate.toJSON(42));
  equal("foo", evaluate.toJSON("foo"));

  // collections
  deepEqual([], evaluate.toJSON([]));

  // elements
  ok(evaluate.toJSON(domEl, seenEls) instanceof WebElement);
  ok(evaluate.toJSON(svgEl, seenEls) instanceof WebElement);
  ok(evaluate.toJSON(xulEl, seenEls) instanceof WebElement);

  // toJSON
  equal(
    "foo",
    evaluate.toJSON({
      toJSON() {
        return "foo";
      },
    })
  );

  // arbitrary object
  deepEqual({ foo: "bar" }, evaluate.toJSON({ foo: "bar" }));

  run_next_test();
});

add_test(function test_toJSON_types_ReferenceStore() {
  // Temporarily add custom elements until xpcshell tests
  // have access to real DOM nodes (including the Window Proxy)
  elementIdCache.add(domElId);
  elementIdCache.add(svgElId);
  elementIdCache.add(xulElId);

  deepEqual(evaluate.toJSON(domWebEl, elementIdCache), domElId);
  deepEqual(evaluate.toJSON(svgWebEl, elementIdCache), svgElId);
  deepEqual(evaluate.toJSON(xulWebEl, elementIdCache), xulElId);

  Assert.throws(
    () => evaluate.toJSON(domEl, elementIdCache),
    /TypeError/,
    "Reference store not usable for elements"
  );

  elementIdCache.clear();

  run_next_test();
});

add_test(function test_toJSON_sequences() {
  const input = [
    null,
    true,
    [],
    domEl,
    {
      toJSON() {
        return "foo";
      },
    },
    { bar: "baz" },
  ];
  const actual = evaluate.toJSON(input, seenEls);

  equal(null, actual[0]);
  equal(true, actual[1]);
  deepEqual([], actual[2]);
  ok(actual[3] instanceof WebElement);
  equal("foo", actual[4]);
  deepEqual({ bar: "baz" }, actual[5]);

  run_next_test();
});

add_test(function test_toJSON_sequences_ReferenceStore() {
  const input = [
    null,
    true,
    [],
    domWebEl,
    {
      toJSON() {
        return "foo";
      },
    },
    { bar: "baz" },
  ];

  Assert.throws(
    () => evaluate.toJSON(input, elementIdCache),
    /NoSuchElementError/,
    "Expected no element"
  );

  elementIdCache.add(domElId);

  const actual = evaluate.toJSON(input, elementIdCache);

  equal(null, actual[0]);
  equal(true, actual[1]);
  deepEqual([], actual[2]);
  deepEqual(actual[3], domElId);
  equal("foo", actual[4]);
  deepEqual({ bar: "baz" }, actual[5]);

  elementIdCache.clear();

  run_next_test();
});

add_test(function test_toJSON_objects() {
  const input = {
    null: null,
    boolean: true,
    array: [],
    webElement: domEl,
    elementId: domElId,
    toJSON: {
      toJSON() {
        return "foo";
      },
    },
    object: { bar: "baz" },
  };
  const actual = evaluate.toJSON(input, seenEls);

  equal(null, actual.null);
  equal(true, actual.boolean);
  deepEqual([], actual.array);
  ok(actual.webElement instanceof WebElement);
  ok(actual.elementId instanceof WebElement);
  equal("foo", actual.toJSON);
  deepEqual({ bar: "baz" }, actual.object);

  run_next_test();
});

add_test(function test_toJSON_objects_ReferenceStore() {
  const input = {
    null: null,
    boolean: true,
    array: [],
    webElement: domWebEl,
    elementId: domElId,
    toJSON: {
      toJSON() {
        return "foo";
      },
    },
    object: { bar: "baz" },
  };

  Assert.throws(
    () => evaluate.toJSON(input, elementIdCache),
    /NoSuchElementError/,
    "Expected no element"
  );

  elementIdCache.add(domElId);

  const actual = evaluate.toJSON(input, elementIdCache);

  equal(null, actual.null);
  equal(true, actual.boolean);
  deepEqual([], actual.array);
  deepEqual(actual.webElement, domElId);
  deepEqual(actual.elementId, domElId);
  equal("foo", actual.toJSON);
  deepEqual({ bar: "baz" }, actual.object);

  elementIdCache.clear();

  run_next_test();
});

add_test(function test_fromJSON_ReferenceStore() {
  // Add unknown element to reference store
  let webEl = evaluate.fromJSON(domElId, elementIdCache);
  deepEqual(webEl, domWebEl);
  deepEqual(elementIdCache.get(webEl), domElId);

  // Previously seen element is associated with original web element reference
  const domElId2 = {
    id: 1,
    browsingContextId: 4,
    webElRef: WebElement.from(domEl).toJSON(),
  };
  webEl = evaluate.fromJSON(domElId2, elementIdCache);
  deepEqual(webEl, domWebEl);
  deepEqual(elementIdCache.get(webEl), domElId);

  // Store doesn't contain ElementIdentifiers
  Assert.throws(
    () => evaluate.fromJSON(domElId, seenEls),
    /TypeError/,
    "Expected element.ReferenceStore"
  );

  elementIdCache.clear();

  run_next_test();
});

add_test(function test_fromJSON_Store() {
  // Pass-through WebElements without adding it to the element store
  let webEl = evaluate.fromJSON(domWebEl.toJSON());
  deepEqual(webEl, domWebEl);
  ok(!seenEls.has(domWebEl));

  // Find element in the element store
  webEl = seenEls.add(domEl);
  const el = evaluate.fromJSON(webEl.toJSON(), seenEls);
  deepEqual(el, domEl);

  // Reference store doesn't contain web elements
  Assert.throws(
    () => evaluate.fromJSON(domWebEl.toJSON(), elementIdCache),
    /TypeError/,
    "Expected element.Store"
  );

  seenEls.clear();

  run_next_test();
});

add_test(function test_isCyclic_noncyclic() {
  for (let type of [true, 42, "foo", [], {}, null, undefined]) {
    ok(!evaluate.isCyclic(type));
  }

  run_next_test();
});

add_test(function test_isCyclic_object() {
  let obj = {};
  obj.reference = obj;
  ok(evaluate.isCyclic(obj));

  run_next_test();
});

add_test(function test_isCyclic_array() {
  let arr = [];
  arr.push(arr);
  ok(evaluate.isCyclic(arr));

  run_next_test();
});

add_test(function test_isCyclic_arrayInObject() {
  let arr = [];
  arr.push(arr);
  ok(evaluate.isCyclic({ arr }));

  run_next_test();
});

add_test(function test_isCyclic_objectInArray() {
  let obj = {};
  obj.reference = obj;
  ok(evaluate.isCyclic([obj]));

  run_next_test();
});
