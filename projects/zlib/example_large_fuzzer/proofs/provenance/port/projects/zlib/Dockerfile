# Generated from the build recipe of the oss-fuzz-theorems 2026.10 release; do not edit.
#
# zlib on the OSS Verify builder, laid out as the release built it (lay-out-sources reads the sources file).
# oss-verify check passes REPO, COMMIT and BASE_BUILDER.
ARG BASE_BUILDER=oss-verify-base-builder
FROM ${BASE_BUILDER}
ARG REPO
ARG COMMIT
RUN fetch-commit $SRC/upstream/zlib
COPY . $SRC/project/
RUN lay-out-sources $SRC/project/sources $WORK && cp $SRC/project/build.sh $SRC/build.sh
WORKDIR $SRC
