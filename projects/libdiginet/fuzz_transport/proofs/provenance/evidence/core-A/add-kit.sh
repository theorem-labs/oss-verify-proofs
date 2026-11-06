#!/bin/bash
# Add to fuzz_transport's trunk lib what fuzz_frame's trunk seed (TRUNK-SEED.md, sha256 62d9ae661937; internal record) added and the
# transport lib lacks: port_core's composition kit (YK0j YK0t YK18 YK1e YK1g YM08 YM09 YQ00..YQ06 and A/RelimCut.v) as
# released in libreac/fuzz_grant at recipes 25e3d17bdb50, and Reusable/HaltsKitB.v, Reusable/YJ00.v of libreac/fuzz_decode
# at recipes bf7779f81ed7. One change per file: the module path becomes libdiginet.fuzz_transport. Writes kit-table.tsv.
#   HUB=<hub repository> add-kit.sh <lib-dir> <table-out>
# (row TCA's preparation script, sha256 1cfe18d70bfd, with the hub path taken from HUB instead of written in; behaviour unchanged)
set -euo pipefail
LIB=${1:?lib}; TAB=${2:?table}
H=${HUB:?set HUB to the hub repository}
G=25e3d17bdb50; D=bf7779f81ed7
: > "$TAB"
put() { # <dest rel path> <commit> <donor path> <donor module>
  local dst=$1 c=$2 src=$3 mod=$4
  mkdir -p "$(dirname "$LIB/$dst")"
  git -C "$H" show "$c:$src" | sed "s/libreac\\.$mod/libdiginet.fuzz_transport/g" > "$LIB/$dst"
  local n; n=$(git -C "$H" show "$c:$src" | grep -o "libreac\\.$mod" | wc -l)
  printf '%s\t%s @ %s\t%s\t%s\t%s\n' "$dst" "$src" "$c" "$(git -C "$H" rev-parse "$c:$src")" \
    "$(git -C "$H" hash-object "$LIB/$dst")" "$n" >> "$TAB"
}
put A/RelimCut.v $G proofs/libreac/fuzz_grant/lib/A/RelimCut.v fuzz_grant
for f in YK0j YK0t YK18 YK1e YK1g YM08 YM09 YQ00 YQ01 YQ02 YQ03 YQ04 YQ05 YQ06; do
  put "Reusable/$f.v" $G "proofs/libreac/fuzz_grant/lib/Reusable/$f.v" fuzz_grant
done
for f in HaltsKitB YJ00; do put "Reusable/$f.v" $D "proofs/libreac/fuzz_decode/lib/Reusable/$f.v" fuzz_decode; done
wc -l < "$TAB"
