#!/bin/sh
# cmpkit-86da41d3ef68-scans.sh -- the exposure scans of cmpkit 86da41d3ef68 over this slice's re-run on cmpkit
# 4bbd3a74be89 (records/cmpkit-4bbd3a74be89-*.out, written by cmpkit-sm1.py):
#   luiscan   rule 8 (lui-built absolute values) exposure of the 13 functions that re-run compared, in both images;
#             `exposure` 0 in BOTH images = rule 8 leaves the old verdict unchanged
#   ambiscan  every by-name compare in the 4bbd3a74be89 outputs: a name several sized FUNC copies carry in either image
#             (the old tools took the lowest-address copy); `ambiguous hits 0` = none
# usage: cmpkit-86da41d3ef68-scans.sh KIT P R OUT
#   KIT  the kit directory tools/cmpkit/86da41d3ef68/: SHA256SUMS and the nine files it pins
#   P    libreac's pinned image tree: unstripped/fuzz_grant/fuzz_grant.asan (twin 57c26f993615)
#   R    reac-repacer's pinned image tree: result/unstripped/fuzz_uci/fuzz_uci.asan (twin 56822e263d76)
#   OUT  output directory
# Needs python3 with pyelftools and capstone importable (PYTHONPATH). The two twins are linked by role name, and the
# kit's SHA256SUMS with the nine files it pins (alone in kit/) and this slice's records/cmpkit-4bbd3a74be89-*.out (in
# old/) are copied, into a scratch directory under OUT; every tool runs there from the copies, so the outputs name
# images by role and sha256 and files by relative path. The scratch directory is removed on exit.
# The function list is cmpkit-sm1.py's: its 12 NAMED functions, and the MemToShadow copy that __asan_stack_malloc_1
# +0x144 calls (compared there by address, 0x3d410 / 0x3c348), here by NAME{FILE}. RegisterCommonFlags is scanned
# whole, which covers the 8 bytes at +0x358 the 4bbd3a74be89 re-run also compared by address.
set -eu
[ $# -eq 4 ] || { sed -n '8,12p' "$0" >&2; exit 2; }
HERE=$(cd "$(dirname "$0")" && pwd)
KIT=$(cd "$1" && pwd); P=$(cd "$2" && pwd); R=$(cd "$3" && pwd)
mkdir -p "$4"; OUT=$(cd "$4" && pwd)
IN=$(mktemp -d "$OUT/in.XXXXXX")
trap 'rm -rf "$IN"' EXIT
ln -s "$P/unstripped/fuzz_grant/fuzz_grant.asan" "$IN/fuzz_grant.asan"
ln -s "$R/result/unstripped/fuzz_uci/fuzz_uci.asan" "$IN/fuzz_uci.asan"
mkdir "$IN/kit" "$IN/old"
cp "$KIT/SHA256SUMS" "$IN/kit/"
for f in $(awk '{print $2}' "$KIT/SHA256SUMS"); do cp "$KIT/$f" "$IN/kit/$f"; done
cp "$HERE"/records/cmpkit-4bbd3a74be89-*.out "$IN/old/"
cd "$IN"
export PYTHONDONTWRITEBYTECODE=1

# run FILE CMD...: CMD's stdout and stderr in OUT/FILE, the command as its first line, its exit status as its last
run() { f=$1; shift; rc=0; { echo "\$ $*"; "$@" 2>&1 || rc=$?; echo "rc=$rc"; } > "$OUT/$f"; }

# 0. the kit: every member's sha256, the kit id (first 12 hex of sha256(SHA256SUMS)), the python modules
{ echo '$ (cd kit && sha256sum -c SHA256SUMS && sha256sum SHA256SUMS)'
  (cd kit && sha256sum -c SHA256SUMS && sha256sum SHA256SUMS)
  python3 -c 'import sys, elftools, capstone; print("python", sys.version.split()[0], "pyelftools", elftools.__version__, "capstone", capstone.__version__)'
} > "$OUT/cmpkit-86da41d3ef68-kit.out"
[ "$(sha256sum kit/SHA256SUMS | cut -c1-12)" = 86da41d3ef68 ] || { echo 'scans: KIT is not cmpkit 86da41d3ef68' >&2; exit 1; }

FNS=__asan_stack_malloc_1,__interceptor_trampoline___tls_get_addr,___interceptor___tls_get_addr
FNS=$FNS,_ZN6__asan18TryAsanInitFromRtlEv,__tls_get_addr,_ZN6__asan16GetCurrentThreadEv,_ZN6__asan10AsanTSDGetEv
FNS=$FNS,__pthread_getspecific,_ZN11__sanitizer20DTLS_on_tls_get_addrEPvS0_mm
FNS=$FNS,_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE,_ZN6__asan9FakeStack2GCEm
FNS=$FNS,_ZN6__asan10AsanThread32AsyncSignalSafeLazyInitFakeStackEv,'_ZN6__asanL11MemToShadowEm{asan_fake_stack.cpp}'

# 1. luiscan 9ae61e4a0e01: one row per function (--all: also the functions with no lui), both images
run cmpkit-86da41d3ef68-luiscan.out python3 kit/luiscan.py --all --fns "$FNS" fuzz_grant.asan fuzz_uci.asan

# 2. ambiscan 9f61b4cee422: every 4bbd3a74be89 output of this slice (the controls compared file copies of fuzz_uci.asan
#    with its .symtab unchanged)
run cmpkit-86da41d3ef68-ambiscan.out python3 kit/ambiscan.py fuzz_grant.asan fuzz_uci.asan old
