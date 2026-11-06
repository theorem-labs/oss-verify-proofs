# Copyright 2026 Pau Aliagas <linuxnow@gmail.com>
# SPDX-License-Identifier: Apache-2.0
# Modified 2026 by Theorem Labs, PBC: copies in this directory's fuzz_preset.c and alloc.c for fuzz_preset, and its test.
#
# omx-clap-core on the OSS Verify builder. tools/check passes REPO, COMMIT and BASE_BUILDER.
# The fuzz targets are omx-clap-core's own, in fuzz/ of the checkout. fuzz_preset is built from this directory's
# fuzz_preset.c and alloc.c instead, omx-clap-core's fuzz/fuzz_preset.c and fuzz/alloc.c at COMMIT with one change
# (their first comments say which), copied in to $SRC/fuzz_preset/ with build.sh.
ARG BASE_BUILDER=oss-verify-base-builder
FROM ${BASE_BUILDER}
ARG REPO
ARG COMMIT
RUN fetch-commit $SRC/omx-clap-core
COPY build.sh $SRC/
COPY fuzz_preset.c alloc.c fuzz_preset_oom.c $SRC/fuzz_preset/
WORKDIR $SRC/omx-clap-core
