=======
History
=======

Unreleased
----------

1.28.5 (2020-09-14)
-------------------

* Fix deploy step to update pip before deploying to pypi.

1.28.4 (2020-09-14)
-------------------

* The `SUPERFLUOUS_NO_LINT` warning has been removed from the glinter.
  It likely did more harm than good, and makes it hard to make
  `metrics.yaml` files that pass across different versions of `glean_parser`.
* Expired metrics will now produce a linter warning, `EXPIRED_METRIC`.
* Expiry dates that are more than 730 days (~2 years) in the future will produce a linter warning,
  `EXPIRATION_DATE_TOO_FAR`.
* Allow using the Quantity metric type outside of Gecko.
* New parser configs `custom_is_expired` and `custom_validate_expires` added.
  These are both functions that take the `expires` value of the metric and return a bool.
  (See `Metric.is_expired` and `Metric.validate_expires`).
  These will allow FOG to provide custom validation for its version-based `expires` values.

1.28.3 (2020-07-28)
-------------------

* BUGFIX: Support HashSet and Dictionary in the C# generated code.

1.28.2 (2020-07-28)
-------------------

* BUGFIX: Generate valid C# code when using Labeled metric types.

1.28.1 (2020-07-24)
-------------------

* BUGFIX: Add missing column to correctly render markdown tables in generated documentation.

1.28.0 (2020-07-23)
-------------------

* **Breaking change:** The internal ping `deletion-request` was misnamed in pings.py causing the linter to not allow use of the correctly named ping for adding legacy ids to. Consuming apps will need to update their metrics.yaml if they are using `deletion_request` in any `send_in_pings` to `deletion-request` after updating.

1.27.0 (2020-07-21)
-------------------

* Rename the `data_category` field to `data_sensitivity` to be clearer.

1.26.0 (2020-07-21)
-------------------

* Add support for JWE metric types.
* Add a `data_sensitivity` field to all metrics for specifying the type of data collected in the field.

1.25.0 (2020-07-17)
-------------------

* Add support for generating C# code.
* BUGFIX: The memory unit is now correctly passed to the MemoryDistribution
  metric type in Swift.

1.24.0 (2020-06-30)
-------------------

* BUGFIX: look for metrics in send_if_empty pings. Metrics for these kinds of pings were being ignored.

1.23.0 (2020-06-27)
-------------------

* Support for Python 3.5 has been dropped.
* BUGFIX: The ordering of event extra keys will now match with their enum, fixing a serious bug where keys of extras may not match the correct values in the data payload.  See https://bugzilla.mozilla.org/show_bug.cgi?id=1648768.

1.22.0 (2020-05-28)
-------------------

* **Breaking change:** (Swift only) Combine all metrics and pings into a single generated file `Metrics.swift`.

1.21.0 (2020-05-25)
-------------------

* `glinter` messages have been improved with more details and to be more
  actionable.
* A maximum of 10 `extra_keys` is now enforced for `event` metric types.
* BUGFIX: the `Lifetime` enum values now match the values of the implementation in mozilla/glean.

1.20.4 (2020-05-07)
-------------------

* BUGFIX: yamllint errors are now reported using the correct file name.

1.20.3 (2020-05-06)
-------------------

* Support for using `timing_distribution`'s `time_unit` parameter to control the range of acceptable values is documented. The default unit for this use case is `nanosecond` to avoid creating a breaking change.  See [bug 1630997](https://bugzilla.mozilla.org/show_bug.cgi?id=1630997) for more information.

1.20.2 (2020-04-24)
-------------------

* Dependencies that depend on the version of Python being used are now specified using the `Declaring platform specific dependencies syntax in setuptools <https://setuptools.readthedocs.io/en/latest/setuptools.html#declaring-platform-specific-dependencies>`__. This means that more recent versions of dependencies are likely to be installed on Python 3.6 and later, and unnecessary backport libraries won't be installed on more recent Python versions.

1.20.1 (2020-04-21)
-------------------

* The minimum version of the runtime dependencies has been lowered to increase compatibility with other tools.  These minimum versions are now tested in CI, in addition to testing the latest versions of the dependencies that was already happening in CI.

1.20.0 (2020-04-15)
-------------------

* **Breaking change:** glinter errors found during the `translate` command will now return an error code. glinter warnings will be displayed, but not return an error code.
* `glean_parser` now produces a linter warning when `user` lifetime metrics are
  set to expire. See [bug 1604854](https://bugzilla.mozilla.org/show_bug.cgi?id=1604854)
  for additional context.

1.19.0 (2020-03-18)
-------------------

* **Breaking change:** The regular expression used to validate labels is
  stricter and more correct.
* Add more information about pings to markdown documentation:
  * State whether the ping includes client id;
  * Add list of data review links;
  * Add list of related bugs links.
* `glean_parser` now makes it easier to write external translation functions for
  different language targets.
* BUGFIX: glean_parser now works on 32-bit Windows.

1.18.3 (2020-02-24)
-------------------

* Dropped the 'inflection' dependency.
* Constrained the 'zipp' and 'MarkupSafe' transitive dependencies to versions that
  support Python 3.5.

1.18.2 (2020-02-14)
-------------------

* BUGFIX: Fix rendering of first element of reason list.

1.18.1 (2020-02-14)
-------------------

* BUGFIX: Reason codes are displayed in markdown output for built-in pings as
  well.
* BUGFIX: Reason descriptions are indented correctly in markdown output.
* BUGFIX: To avoid a compiler error, the @JvmName annotation isn't added to
  private members.

1.18.0 (2020-02-13)
-------------------

* **Breaking Change (Java API)** Have the metrics names in Java match the names in Kotlin.
  See [Bug 1588060](https://bugzilla.mozilla.org/show_bug.cgi?id=1588060).
* The reasons a ping are sent are now included in the generated markdown documentation.

1.17.3 (2020-02-05)
-------------------

* BUGFIX: The version of Jinja2 now specifies < 3.0, since that version no
  longer supports Python 3.5.

1.17.2 (2020-02-05)
-------------------

* BUGFIX: Fixes an import error in generated Kotlin code.

1.17.1 (2020-02-05)
-------------------

* BUGFIX: Generated Swift code now includes `import Glean`, unless generating
  for a Glean-internal build.

1.17.0 (2020-02-03)
-------------------

* Remove default schema URL from `validate_ping`
* Make `schema` argument required for CLI
* BUGFIX: Avoid default import in Swift code for Glean itself
* BUGFIX: Restore order of fields in generated Swift code

1.16.0 (2020-01-15)
-------------------

* Support for `reason` codes on pings was added.

1.15.6 (2020-02-06)
-------------------

* BUGFIX: The version of Jinja2 now specifies < 3.0, since that version no
  longer supports Python 3.5 (backported from 1.17.3).

1.15.5 (2019-12-19)
-------------------

* BUGFIX: Also allow the legacy name `all_pings` for `send_in_pings` parameter on metrics

1.15.4 (2019-12-19)
-------------------

* BUGFIX: Also allow the legacy name `all_pings`

1.15.3 (2019-12-13)
-------------------

* Add project title to markdown template.
* Remove "Sorry about that" from markdown template.
* BUGFIX: Replace dashes in variable names to force proper naming

1.15.2 (2019-12-12)
-------------------

* BUGFIX: Use a pure Python library for iso8601 so there is no compilation required.

1.15.1 (2019-12-12)
-------------------

* BUGFIX: Add some additional ping names to the non-kebab-case allow list.

1.15.0 (2019-12-12)
-------------------

* Restrict new pings names to be kebab-case and change `all_pings` to `all-pings`

1.14.0 (2019-12-06)
-------------------

* glean_parser now supports Python versions 3.5, 3.6, 3.7 and 3.8.

1.13.0 (2019-12-04)
-------------------

* The `translate` command will no longer clear extra files in the output directory.
* BUGFIX: Ensure all newlines in comments are prefixed with comment markers
* BUGFIX: Escape Swift keywords in variable names in generated code
* Generate documentation for pings that are sent if empty

1.12.0 (2019-11-27)
-------------------

* Reserve the `deletion_request` ping name
* Added a new flag `send_if_empty` for pings

1.11.0 (2019-11-13)
-------------------

* The `glinter` command now performs `yamllint` validation on registry files.

1.10.0 (2019-11-11)
-------------------

* The Kotlin linter `detekt` is now run during CI, and for local
  testing if installed.

* Python 3.8 is now tested in CI (in addition to Python 3.7).
  Using `tox` for this doesn't work in modern versions of CircleCI, so
  the `tox` configuration has been removed.

* `yamllint` has been added to test the YAML files on CI.

* ⚠ Metric types that don't yet have implementations in glean-core have been
  removed. This includes `enumeration`, `rate`, `usage`, and `use_counter`, as
  well as many labeled metrics that don't exist.

1.9.5 (2019-10-22)
------------------

* Allow a Swift lint for generated code

* New lint: Restrict what metric can go into the 'baseline' ping

* New lint: Warn for slight misspellings in ping names

* BUGFIX: change Labeled types labels from lists to sets.

1.9.4 (2019-10-16)
------------------

* Use lists instead of sets in Labeled types labels to ensure that
  the order of the labels passed to the `metrics.yaml` is kept.

* `glinter` will now check for duplicate labels and error if there are any.

1.9.3 (2019-10-09)
------------------

* Add labels from Labeled types to the Extra column in the Markdown template.

1.9.2 (2019-10-08)
------------------

* BUGFIX: Don't call `is_internal_metric` on `Ping` objects.

1.9.1 (2019-10-07)
------------------

* Don't include Glean internal metrics in the generated markdown.

1.9.0 (2019-10-04)
------------------

* Glinter now warns when bug numbers (rather than URLs) are used.

* BUGFIX: add `HistogramType` and `MemoryUnit` imports in Kotlin generated code.

1.8.4 (2019-10-02)
------------------

* Removed unsupported labeled metric types.

1.8.3 (2019-10-02)
------------------

* Fix indentation for generated Swift code

1.8.2 (2019-10-01)
------------------

* Created labeled metrics and events in Swift code and wrap it in a configured namespace

1.8.1 (2019-09-27)
------------------

* BUGFIX: `memory_unit` is now passed to the Kotlin generator.

1.8.0 (2019-09-26)
------------------

* A new parser config, `do_not_disable_expired`, was added to turn off the
  feature that expired metrics are automatically disabled. This is useful if you
  want to retain the disabled value that is explicitly in the `metrics.yaml`
  file.

* `glinter` will now report about superfluous `no_lint` entries.

1.7.0 (2019-09-24)
------------------

* A "`glinter`" tool is now included to find common mistakes in metric naming and setup.
  This check is run during `translate` and warnings will be displayed.
  ⚠ These warnings will be treated as errors in a future revision.

1.6.1 (2019-09-17)
------------------

* BUGFIX: `GleanGeckoMetricsMapping` must include `LabeledMetricType` and `CounterMetricType`.

1.6.0 (2019-09-17)
------------------

* NEW: Support for outputting metrics in Swift.

* BUGFIX: Provides a helpful error message when `geckoview_datapoint` is used on an metric type that doesn't support GeckoView exfiltration.

* Generate a lookup table for Gecko categorical histograms in `GleanGeckoMetricsMapping`.

* Introduce a 'Swift' output generator.

1.4.1 (2019-08-28)
------------------

* Documentation only.

1.4.0 (2019-08-27)
------------------

* Added support for generating markdown documentation from `metrics.yaml` files.

1.3.0 (2019-08-22)
------------------

* `quantity` metric type has been added.

1.2.1 (2019-08-13)
------------------

* BUGFIX: `includeClientId` was not being output for PingType.

1.2.0 (2019-08-13)
------------------

* `memory_distribution` metric type has been added.

* `custom_distribution` metric type has been added.

* `labeled_timespan` is no longer an allowed metric type.

1.1.0 (2019-08-05)
------------------

* Add a special `all_pings` value to `send_in_pings`.

1.0.0 (2019-07-29)
------------------

* First release to start following strict semver.

0.1.0 (2018-10-15)
------------------

* First release on PyPI.
