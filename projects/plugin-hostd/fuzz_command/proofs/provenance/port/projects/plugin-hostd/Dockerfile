# Copyright 2026 Pau Aliagas <linuxnow@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# plugin-hostd on the OSS Verify builder. tools/check passes REPO, COMMIT and BASE_BUILDER.
# The fuzz targets are plugin-hostd's own, in fuzz/ of the checkout. The one dependency is mod-host's protocol headers
# as FreeMixer ships them: the sources file pins FreeMixer/.github and the mod-host commit its mod-host.spec names, and
# the spec's patches are applied here in the spec's order, as packaging/mod-host/prepare-source.sh applies them.
ARG BASE_BUILDER=oss-verify-base-builder
FROM ${BASE_BUILDER}
ARG REPO
ARG COMMIT
RUN fetch-commit $SRC/plugin-hostd
COPY sources build.sh $SRC/
RUN lay-out-sources $SRC/sources && \
    spec=$SRC/freemixer/packaging/mod-host/mod-host.spec && \
    grep -q "^git	mod-host	.*	$(sed -n 's/^%global commit0 *//p' "$spec")\$" $SRC/sources && \
    for p in $(sed -n 's/^Patch[0-9]*: *//p' "$spec"); do \
        git -C $SRC/mod-host apply --whitespace=nowarn "$SRC/freemixer/packaging/mod-host/$p" || exit 1; \
    done
WORKDIR $SRC/plugin-hostd
