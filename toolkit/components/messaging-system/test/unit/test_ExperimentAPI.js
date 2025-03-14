"use strict";

const { ExperimentAPI } = ChromeUtils.import(
  "resource://messaging-system/experiments/ExperimentAPI.jsm"
);
const { ExperimentFakes } = ChromeUtils.import(
  "resource://testing-common/MSTestUtils.jsm"
);
const { TestUtils } = ChromeUtils.import(
  "resource://testing-common/TestUtils.jsm"
);

/**
 * #getExperiment
 */
add_task(async function test_getExperiment_slug() {
  const sandbox = sinon.createSandbox();
  const manager = ExperimentFakes.manager();
  const expected = ExperimentFakes.experiment("foo");

  await manager.onStartup();

  sandbox.stub(ExperimentAPI, "_store").get(() => ExperimentFakes.childStore());

  manager.store.addExperiment(expected);

  // Wait to sync to child
  await TestUtils.waitForCondition(
    () => ExperimentAPI.getExperiment({ slug: "foo" }),
    "Wait for child to sync"
  );

  Assert.deepEqual(
    ExperimentAPI.getExperiment({ slug: "foo" }),
    expected,
    "should return an experiment by slug"
  );

  sandbox.restore();
});

add_task(async function test_getExperiment_feature() {
  const sandbox = sinon.createSandbox();
  const manager = ExperimentFakes.manager();
  const expected = ExperimentFakes.experiment("foo", {
    branch: {
      slug: "treatment",
      value: { title: "hi" },
      feature: { featureId: "cfr", enabled: true },
    },
  });

  await manager.onStartup();

  sandbox.stub(ExperimentAPI, "_store").get(() => ExperimentFakes.childStore());

  manager.store.addExperiment(expected);

  // Wait to sync to child
  await TestUtils.waitForCondition(
    () => ExperimentAPI.getExperiment({ featureId: "cfr" }),
    "Wait for child to sync"
  );

  Assert.deepEqual(
    ExperimentAPI.getExperiment({ featureId: "cfr" }),
    expected,
    "should return an experiment by slug"
  );

  sandbox.restore();
});

/**
 * #getValue
 */
add_task(async function test_getValue() {
  const sandbox = sinon.createSandbox();
  const manager = ExperimentFakes.manager();
  const feature = {
    featureId: "aboutwelcome",
    enabled: true,
    value: { title: "hi" },
  };
  const expected = ExperimentFakes.experiment("foo", {
    branch: { slug: "treatment", feature },
  });

  await manager.onStartup();

  sandbox.stub(ExperimentAPI, "_store").get(() => ExperimentFakes.childStore());

  manager.store.addExperiment(expected);

  await TestUtils.waitForCondition(
    () => ExperimentAPI.getExperiment({ slug: "foo" }),
    "Wait for child to sync"
  );

  Assert.deepEqual(
    ExperimentAPI.getFeatureValue("aboutwelcome"),
    feature.value,
    "should return an experiment value by slug"
  );

  Assert.equal(
    ExperimentAPI.getFeatureValue("doesnotexist"),
    undefined,
    "should return undefined if the experiment is not found"
  );

  sandbox.restore();
});

/**
 * #isFeatureEnabled
 */

add_task(async function test_isFeatureEnabledDefault() {
  const sandbox = sinon.createSandbox();
  const manager = ExperimentFakes.manager();
  const FEATURE_ENABLED_DEFAULT = true;
  const expected = ExperimentFakes.experiment("foo");

  await manager.onStartup();

  sandbox.stub(ExperimentAPI, "_store").get(() => manager.store);

  manager.store.addExperiment(expected);

  Assert.deepEqual(
    ExperimentAPI.isFeatureEnabled("aboutwelcome", FEATURE_ENABLED_DEFAULT),
    FEATURE_ENABLED_DEFAULT,
    "should return enabled true as default"
  );
  sandbox.restore();
});

add_task(async function test_isFeatureEnabled() {
  const sandbox = sinon.createSandbox();
  const manager = ExperimentFakes.manager();
  const feature = {
    featureId: "aboutwelcome",
    enabled: false,
    value: null,
  };
  const expected = ExperimentFakes.experiment("foo", {
    branch: { slug: "treatment", feature },
  });

  await manager.onStartup();

  sandbox.stub(ExperimentAPI, "_store").get(() => manager.store);

  manager.store.addExperiment(expected);

  Assert.deepEqual(
    ExperimentAPI.isFeatureEnabled("aboutwelcome", true),
    feature.enabled,
    "should return feature as disabled"
  );
  sandbox.restore();
});

/**
 * #getRecipe
 */
add_task(async function test_getRecipe() {
  const sandbox = sinon.createSandbox();
  const RECIPE = ExperimentFakes.recipe("foo");
  sandbox.stub(ExperimentAPI._remoteSettingsClient, "get").resolves([RECIPE]);

  const recipe = await ExperimentAPI.getRecipe("foo");
  Assert.deepEqual(
    recipe,
    RECIPE,
    "should return an experiment recipe if found"
  );

  sandbox.restore();
});

add_task(async function test_getRecipe_Failure() {
  const sandbox = sinon.createSandbox();
  sandbox.stub(ExperimentAPI._remoteSettingsClient, "get").throws();

  const recipe = await ExperimentAPI.getRecipe("foo");
  Assert.equal(recipe, undefined, "should return undefined if RS throws");

  sandbox.restore();
});

/**
 * #getAllBranches
 */
add_task(async function test_getAllBranches() {
  const sandbox = sinon.createSandbox();
  const RECIPE = ExperimentFakes.recipe("foo");
  sandbox.stub(ExperimentAPI._remoteSettingsClient, "get").resolves([RECIPE]);

  const branches = await ExperimentAPI.getAllBranches("foo");
  Assert.deepEqual(
    branches,
    RECIPE.branches,
    "should return all branches if found a recipe"
  );

  sandbox.restore();
});

add_task(async function test_getAllBranches_Failure() {
  const sandbox = sinon.createSandbox();
  sandbox.stub(ExperimentAPI._remoteSettingsClient, "get").throws();

  const branches = await ExperimentAPI.getAllBranches("foo");
  Assert.equal(branches, undefined, "should return undefined if RS throws");

  sandbox.restore();
});

/**
 * #on
 * #off
 */
add_task(async function test_event_updates_content() {
  const sandbox = sinon.createSandbox();
  const manager = ExperimentFakes.manager();
  const expected = ExperimentFakes.experiment("foo");
  const updateEventCbStub = sandbox.stub();

  // Setup ExperimentManager and child store for ExperimentAPI
  await manager.onStartup();
  sandbox.stub(ExperimentAPI, "_store").get(() => ExperimentFakes.childStore());

  // Set update cb
  ExperimentAPI.on("child-store-update:foo", updateEventCbStub);

  // Add some data
  manager.store.addExperiment(expected);

  // Wait to sync
  await TestUtils.waitForCondition(
    () => ExperimentAPI.getExperiment({ slug: "foo" }),
    "Wait for child to sync"
  );

  let baselineCallCount = updateEventCbStub.callCount;

  // Trigger an update
  manager.store.updateExperiment("foo", { active: false });

  // Wait for update to child store
  await TestUtils.waitForCondition(
    () => updateEventCbStub.callCount === baselineCallCount + 1,
    "An `update` event was not sent"
  );

  // Remove the update listener
  ExperimentAPI.off("child-store-update:foo", updateEventCbStub);
  // Trigger another change
  manager.store.updateExperiment("foo", { active: true });

  const [, cbExperimentValue] = updateEventCbStub.firstCall.args;

  Assert.deepEqual(
    expected.slug,
    cbExperimentValue.slug,
    "should return the updated experiment"
  );

  Assert.equal(
    updateEventCbStub.callCount,
    baselineCallCount + 1,
    "Should only have seen 1 update"
  );

  sandbox.restore();
});

/**
 * #on
 * #off
 */
add_task(async function test_event_updates_main() {
  const sandbox = sinon.createSandbox();
  const manager = ExperimentFakes.manager();
  const expected = ExperimentFakes.experiment("foo");
  const updateEventCbStub = sandbox.stub();

  // Setup ExperimentManager and child store for ExperimentAPI
  await manager.onStartup();
  sandbox.stub(ExperimentAPI, "_store").get(() => manager.store);

  // Set update cb
  ExperimentAPI.on("parent-store-update:foo", updateEventCbStub);

  // Add some data
  manager.store.addExperiment(expected);

  let baselineCallCount = updateEventCbStub.callCount;

  // Trigger an update
  manager.store.updateExperiment("foo", { active: false });

  // Wait for update to child store
  await TestUtils.waitForCondition(
    () => updateEventCbStub.callCount === baselineCallCount + 1,
    "An `update` event was not sent"
  );

  // Remove the update listener
  ExperimentAPI.off("parent-store-update:foo", updateEventCbStub);
  // Trigger another change
  manager.store.updateExperiment("foo", { active: true });

  const [, cbExperimentValue] = updateEventCbStub.firstCall.args;

  Assert.deepEqual(
    expected.slug,
    cbExperimentValue.slug,
    "should return the updated experiment"
  );

  Assert.equal(
    updateEventCbStub.callCount,
    baselineCallCount + 1,
    "Should only have seen 1 update"
  );

  sandbox.restore();
});
