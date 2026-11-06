# Copyright 2026 Pau Aliagas <linuxnow@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# reac-pw on the OSS Verify builder. tools/check passes REPO, COMMIT and BASE_BUILDER.
# The fuzz targets are reac-pw's own, in fuzz/ of the checkout. Its two dependencies are
# headers only, pinned by the sources file: libreac 1.8.0 and SPA of PipeWire 1.6.10.
ARG BASE_BUILDER=oss-verify-base-builder
FROM ${BASE_BUILDER}
ARG REPO
ARG COMMIT
RUN fetch-commit $SRC/reac-pw
COPY sources build.sh $SRC/
RUN lay-out-sources $SRC/sources
WORKDIR $SRC/reac-pw
