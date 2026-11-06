#!/usr/bin/env python3
"""Run the shared binmatch.py UNCHANGED on reac-repacer/fuzz_wire (NEW) vs cgif_file_fuzzer (OTHER), asan-ubsan build.

Same driver shape as the fuzz_uci image-B lane's run_binmatch_uciB.py: only binmatch's module globals are rebound
(images, target names, output dir). Every path comes from the lane's env.sh:
  binmatch.py   $UCI/sub/exitdrv/tools/binmatch.py (sha256 0e042d7f8220..., asserted below), imported read-only
  NEW (pinned)  $UB  = fuzz_wire.asan-ubsan pin, sha256 af4534831a4528320c7dc74ca3f64bb96e8232ed2e313f01126d10879f3417d6
  NEW (twin)    $UBs = its unstripped twin, sha256 51eb4bef24252e4df6e11baa89f653d20d74e38ae684f61bc94f4fb339ac97c3
  OTHER         $CB  = cgif donor clone (25e3d17bdb50) cgif_file_fuzzer.asan-ubsan, sha256 1c29845fe6058de6e1db...
  output        $LT/exitdrv/binmatch/
TARGET / TARGET_FILES only label rows (kind); they do not change a match.
Usage: run_binmatch_wireB.py --other cgif --builds asan-ubsan
"""
import hashlib
import os
import sys

sys.dont_write_bytecode = True
E = os.environ
BUILD = 'asan-ubsan'
assert E['UB'].endswith('.' + BUILD) and E['UBs'].endswith('.' + BUILD) and E['CB'].endswith('.' + BUILD)
BM = E['UCI'] + '/sub/exitdrv/tools/binmatch.py'          # the copy the brief names; its bytes are pinned here
assert hashlib.sha256(open(BM, 'rb').read()).hexdigest() == \
    '0e042d7f82208595d7cb5c11026d80f8b645fb0e847ae6b53ff804e80ebc6e11', 'binmatch.py is not the pinned copy'
sys.path.insert(0, os.path.dirname(BM))
import binmatch as bm  # noqa: E402

bm.FM = E['UB'][:-len(BUILD)]
bm.FMU = E['UBs'][:-len(BUILD)]
bm.OTHERS['cgif'] = E['CB'][:-len(BUILD)]
bm.OUT = E['LT'] + '/exitdrv/binmatch/'
os.makedirs(bm.OUT, exist_ok=True)
bm.TARGET = {'LLVMFuzzerTestOneInput', '__wrap_getenv', '__wrap_getpid'}
bm.TARGET_FILES = {'fuzz_wire.c', 'repace_wire.c'}

if __name__ == '__main__':
    bm.main()
