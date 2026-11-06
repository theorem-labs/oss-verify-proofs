#!/usr/bin/env python3
"""Run the cited binmatch.py UNCHANGED on reac-repacer/fuzz_uci (NEW) vs cgif_file_fuzzer (OTHER), asan-ubsan build.

Same driver shape as the image-A driver uci-sg/exitdrv/run_binmatch_uci.py and decode's
startdecode/tools/run_binmatch_decode.py: only binmatch's module globals are rebound (images, target names, output dir).
  NEW (pinned)  fuzz_uci.asan-ubsan ($UCIB_UB)
                sha256 a1b86e424adde6f65d345459822690a6c21e9e606446b91b4ad25e9f3ef6e7fc
  NEW (twin)    result/unstripped/fuzz_uci/fuzz_uci.asan-ubsan sha256 8d07ffcf5948... (names only)
  OTHER         cgif donor clone (25e3d17bdb50) projects/cgif/bin/cgif_file_fuzzer/cgif_file_fuzzer.asan-ubsan
                sha256 1c29845fe6058de6e1dbf3f6ec6abd566ea612d76b65ea5435d7ff77c63e08ef
TARGET / TARGET_FILES only label rows (kind); they do not change a match (a9's labels, unchanged).
Usage: run_binmatch_uciB.py --other cgif --builds asan-ubsan      (output: $UCIB_EXITWORK/binmatch/)
"""
import os
import sys

import os
sys.path.insert(0, os.environ['UCIB_BINMATCH'])   # the cited binmatch.py (not shipped)
import binmatch as bm  # noqa: E402

R = os.environ['UCIB_UROOT'].rstrip('/') + '/'   # the reac-repacer build result root (bin/, unstripped/)
bm.FM = R + 'bin/fuzz_uci/fuzz_uci.'
bm.FMU = R + 'unstripped/fuzz_uci/fuzz_uci.'
bm.OTHERS['cgif'] = os.environ['UCIB_CB'][:-len('asan-ubsan')]
bm.OUT = os.environ['UCIB_EXITWORK'] + '/binmatch/'
os.makedirs(bm.OUT, exist_ok=True)
bm.TARGET = {'LLVMFuzzerTestOneInput', 'check_no_overread', 'check_value', 'check_clamp', 'rp_hot_clamp',
             'rp_uci_int', '__wrap_getenv', '__wrap_getpid'}
bm.TARGET_FILES = {'fuzz_uci.c', 'repace_conf.c'}

if __name__ == '__main__':
    bm.main()
