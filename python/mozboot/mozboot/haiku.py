# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this file,
# You can obtain one at http://mozilla.org/MPL/2.0/.

from __future__ import absolute_import, print_function, unicode_literals

import subprocess

from mozboot.base import BaseBootstrapper


class HaikuBootstrapper(BaseBootstrapper):
    def __init__(self, version, **kwargs):
        BaseBootstrapper.__init__(self, **kwargs)

        self.packages = [
            'haiku_devel',
            'gcc',
            'rust_bin',
        ]

        self.browser_packages = [
            'llvm9',
            'llvm9_clang',
            'llvm9_lld',
            'nasm',
            'yasm',
        ]

    def install_system_packages(self):
        self.run_as_root(['pkgman', 'install'] + self.packages)

    def install_browser_packages(self, mozconfig_builder):
        self.ensure_browser_packages(mozconfig_builder)

    def ensure_browser_packages(self, mozconfig_builder):
        self.run_as_root(['pkgman', 'install'] + self.browser_packages)

    def install_browser_artifact_mode_packages(self, mozconfig_builder):
        self.ensure_browser_packages(mozconfig_builder)

    def ensure_clang_static_analysis_package(self, state_dir, checkout_root):
        # TODO: we don't ship clang base static analysis for this platform
        pass

    def ensure_stylo_packages(self, state_dir, checkout_root):
        # Clang / llvm already installed as browser package
        self.run_as_root(['cargo', 'install', 'cbindgen'])

    def ensure_nasm_packages(self, state_dir, checkout_root):
        # installed via ensure_browser_packages
        pass

    def ensure_node_packages(self, state_dir, checkout_root):
        self.run_as_root(['pkgman', 'install', 'nodejs'])
