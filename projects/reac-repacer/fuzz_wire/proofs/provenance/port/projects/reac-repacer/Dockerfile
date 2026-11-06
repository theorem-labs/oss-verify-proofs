# Copyright 2026 Pau Aliagas <linuxnow@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# reac-repacer on the OSS Verify builder. tools/check passes REPO, COMMIT and BASE_BUILDER.
# The fuzz targets are reac-repacer's own, in fuzz/ of the checkout. The one dependency is libreac, whose src/reac.c
# the readers call into and whose headers they include: the sources file pins its v1.8.0 commit.
ARG BASE_BUILDER=oss-verify-base-builder
FROM ${BASE_BUILDER}
ARG REPO
ARG COMMIT
RUN fetch-commit $SRC/reac-repacer
COPY sources build.sh $SRC/
RUN lay-out-sources $SRC/sources
WORKDIR $SRC/reac-repacer
