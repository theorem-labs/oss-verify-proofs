#!/usr/bin/env python3
"""made_from.py of libreac/fuzz_scene: this unit's data for the rule of dev/licence/made_from.py, which decides which
of the unit's proof files were made from a file that carries Anthropic's licence lines and the lines each takes."""
# the fuzz targets whose proof files this unit's history copied or relocated: a file's text came into the repository
# when the file first came at its path in this unit or in one of them
# Measured, not guessed: every `proofs/<project>/<harness>/` path the unit's own licence lines and header comments
# cite (1,681 cgif/cgif_file_fuzzer, 103 libreac/fuzz_grant, 27 varnish/esi_parse_fuzzer, 18 openssl/ct,
# 11 cgif/cgif_rgb_fuzzer, 6 libreac/fuzz_decode, 6 libreac/fuzz_ctrl, 6 boost-beast/http_request,
# 2 libreac/fuzz_boxreg, 2 jsoncons/fuzz_ubjson_encoder, 1 jsoncons/fuzz_bigint), and the three more its headers
# name in prose alone, without a proofs/ path: libreac/fuzz_pcap, whose lib/A/PcapClose.v gave G_Close.v its form;
# libreac/fuzz_disco; and zlib/checksum_fuzzer, which four headers name ("written for zlib/checksum_fuzzer") and
# which a first reading of this list missed, since the measurement read proofs/ paths and fuzz_<name> words and
# that name is neither (PR #2279's review).  Adding it moves 274 rows of first-added.tsv to an earlier time and
# changes no decision: the run still finds 0 made from.
DONORS = ("cgif/cgif_file_fuzzer", "libreac/fuzz_grant", "varnish/esi_parse_fuzzer", "openssl/ct",
          "cgif/cgif_rgb_fuzzer", "libreac/fuzz_decode", "libreac/fuzz_ctrl", "boost-beast/http_request",
          "libreac/fuzz_boxreg", "jsoncons/fuzz_ubjson_encoder", "jsoncons/fuzz_bigint",
          "libreac/fuzz_pcap", "libreac/fuzz_disco", "zlib/checksum_fuzzer")
HISTORY = "history-named.tsv"   # the --history the record was made with

# The fixed block: the same text, byte for byte, in every unit's made_from.py, to the end of the file.  It loads
# dev/licence/made_from.py from the checkout this file is in and calls it with this file, whose data it reads.
import importlib.util
import os
import sys

_GENERATOR = os.path.join(os.path.dirname(os.path.abspath(__file__)), *[os.pardir] * 7, "dev", "licence",
                          "made_from.py")
try:
    _SPEC = importlib.util.spec_from_file_location("licence_made_from", _GENERATOR)
    _MODULE = importlib.util.module_from_spec(_SPEC)
    _SPEC.loader.exec_module(_MODULE)
    _MAIN = _MODULE.main
except (Exception, SystemExit) as _ERROR:   # a load that fails is exit 4, never 1 (the record differs) or 2 (a warning)
    print("made_from.py: cannot load the shared generator %s: %r" % (os.path.normpath(_GENERATOR), _ERROR),
          file=sys.stderr)
    sys.exit(4)
_MAIN(__file__)
