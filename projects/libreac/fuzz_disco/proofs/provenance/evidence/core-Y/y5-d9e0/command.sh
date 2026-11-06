#!/bin/sh
# The dry run of port_core tag d9e0589898fd (best available, not of record) on the same inputs as run.sh's Y5 block,
# then the per-file classification, the four registry checks and their planted controls. Called by run.sh after its
# Y5 block, from this slice's directory, when D9E0 is set.
# Inputs (variables; no host path is written in this file):
#   D9E0        a directory holding the tag's files (tools/pg-reloc/d9e0589898fd of the shared tool tree; cited, not
#               copied). They are pinned by one sha256 over the sha256sum listing of its 14 .py files (sorted paths),
#               d4d78dd98a21...; port_core.py alone is d9e0589898fd12f8...
#   PIN TWIN OLD_PIN KERNEL_PIN KNOWN_PIN REPO OUT   as run.sh; WORK = run.sh's Y5 work directory ($OUT/y5), whose
#               donor/ and target/ trees and run/stage-out (the abfd17f8b3d2 re-run) this script reads
# Dry run: the tag has no --dry flag; without --apply it only stages into --work and never writes the target lib.
# Two inputs take the tag's own formats, with the same content as the Y5 run's: --old-syms is the Y5 donor extract
# as `name addr size` lines (syms_txt.py, the rows abfd17f8b3d2 reads from it), and --target-syms is the unstripped
# twin itself (its sized symbols are the rows of extract/symbols-asan-ubsan.tsv; the tag reads its size-0 FUNC names
# only from an ELF, for the 'no twin' rule).
set -eu
export PYTHONDONTWRITEBYTECODE=1
test "$(cd "$D9E0" && sha256sum port_core.py | cut -c1-64)" = d9e0589898fd12f83fd76e086a3d7ddf3d1a43a7008dd59a73f442bff30388aa
test "$(cd "$D9E0" && find . -name '*.py' -not -path '*/__pycache__/*' | LC_ALL=C sort | xargs sha256sum | sha256sum | cut -c1-64)" \
  = d4d78dd98a21c2b1f7692f771b9d139df5023fe08da0ab66c6e4d65400d8d3fe
D="$OUT/y5-d9e0"
rm -rf "$D"
mkdir -p "$D"
python3 y5-d9e0/syms_txt.py y5-g8g7/symbols-cgif-asan-ubsan.tsv > "$D/old-syms.txt"
python3 "$D9E0/port_core.py" \
  --src-lib "$WORK/donor/proofs/cgif/cgif_file_fuzzer/lib" \
  --old-elf "$OLD_PIN" --old-prog 804c0:86e40 \
  --old-syms "$D/old-syms.txt" \
  --target-lib "$WORK/target/proofs/libreac/fuzz_disco/lib" \
  --target-mod OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib \
  --target-images OssFuzzTheorems.libreac.fuzz_disco.images \
  --target-name libreac/fuzz_disco \
  --target-elf "$PIN" --target-syms "$TWIN" \
  --files y5-g8g7/files.txt \
  --work "$D/run" \
  --reusable-dir Reusable \
  --remap-images \
  --kernel-image "$KERNEL_PIN" \
  --known-elf "$KNOWN_PIN" \
  --rename tfib_A_musl_memcmp=tfib_A_memcmp_libc \
  --rename tfib_A_musl_memset=tfib_A_memset_libc \
  --override y5-g8g7/overrides.tsv \
  --no-gate > "$D/run.log" 2>&1
set -- --abfd "$WORK/run/stage-out" --shipped "$REPO/proofs/libreac/fuzz_disco/lib" --pin "$PIN" \
  --symbols extract/symbols-asan-ubsan.tsv --files y5-g8g7/files.txt --log "$D/run.log"
python3 y5-d9e0/checks.py --work "$D/run" --out-dir "$D" "$@"
cmp "$D/classify.tsv" y5-d9e0/classify.tsv
cmp "$D/checks.tsv" y5-d9e0/checks.tsv
python3 y5-d9e0/controls.py --work "$D/run" --scratch "$D/controls" "$@"
