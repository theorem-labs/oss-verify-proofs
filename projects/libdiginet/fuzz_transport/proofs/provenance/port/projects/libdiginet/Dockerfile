# Copyright 2026 Pau Aliagas <linuxnow@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# libdiginet on the OSS Verify builder. tools/check passes REPO, COMMIT and BASE_BUILDER.
# The fuzz targets are libdiginet's own, in fuzz/ of the checkout. fuzz_transport is built from this directory's
# fuzz_transport.c instead: libdiginet's fuzz/fuzz_transport.c at COMMIT with one change (io_recv() runs the model on
# each frame poll's recv hands over, and receive() no longer runs it before the poll), copied over
# fuzz/fuzz_transport.c of the checkout, so that build.sh builds it as it builds the other three.
ARG BASE_BUILDER=oss-verify-base-builder
FROM ${BASE_BUILDER}
ARG REPO
ARG COMMIT
RUN fetch-commit $SRC/libdiginet
COPY build.sh $SRC/
COPY fuzz_transport.c $SRC/libdiginet/fuzz/
WORKDIR $SRC/libdiginet
