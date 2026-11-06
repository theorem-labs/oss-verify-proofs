#!/usr/bin/env bash
# d9e0589898fd --dry (no --apply) on the inputs of the untagged port_core runs of record.
# Usage: run.sh NAME FILES
set -u
name=$1; files=$2
P=$D9E0/port_core.py
[ "$(sha256sum < $P | cut -c1-12)" = d9e0589898fd ] || { echo "not d9e0589898fd" >&2; exit 2; }
cd $W/d9run || exit 2
rm -rf "w-$name"
start=$(date -u +%FT%TZ)
python3 $P \
  --src-lib $DONOR/proofs/cgif/cgif_file_fuzzer/lib \
  --old-elf $IMG/cgif.A.pin --old-prog 80490:86bcc \
  --target-lib $W/d9run/tl/proofs/plugin-hostd/fuzz_command/lib \
  --target-mod OssFuzzTheorems.Proofs.plugin_hostd.fuzz_command.lib \
  --target-images OssFuzzTheorems.plugin_hostd.fuzz_command.images \
  --target-name plugin-hostd/fuzz_command \
  --target-elf $IMG/cmd.A.pin --target-syms $IMG/cmd.A.twin \
  --files "$files" --work "w-$name" \
  --rename TfibSyms=CmdSyms --rename TfibB=CmdB --rename TfibB_syms=CmdB_syms --rename TfibB_ok=CmdB_ok \
  > "$name.out" 2> "$name.err"
rc=$?
echo "rc=$rc start=$start end=$(date -u +%FT%TZ)" > "$name.rc"
