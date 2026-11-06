#!/usr/bin/env python3
"""mk_yb05_uci.py DONOR_YB05 TAIL_PLAN OUT -- fuzz_uci image-B YB05.v by fuzz_decode B's mk_yb05.py rule (commit 7eb81ddb186
proofs/libreac/fuzz_decode/provenance/startup-gen/B/mk_yb05.py): the frozen hsform's header of the donor plan (hsform.header, a93ebaea058f, one --modified
line; donor module paths kept, nsB.py rewrites them) followed by the body of the plan the collected pass 2 ran
(the donor plan relocated by the plan-relocation tool + itabranges, with plantail.py's measured tail inserted:
<donor ws>/ZReplyB/YB05.v).
hsform.py is read from $UCIB_FROZEN (cited, not shipped)."""
import hashlib, os, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ucib_env import need  # noqa: E402
sys.path.insert(0, need('UCIB_FROZEN'))
import hsform  # noqa: E402

donor, tail, out = sys.argv[1:4]
# the relocation tools are named by role and sha256 (their internal names are not shipped)
MOD = ("generated for reac-repacer/fuzz_uci image B: the donor plan relocated to this image (the image address map "
       "(map tool sha256 4d51ec1c0069) + the plan-relocation tool (sha256 2d846496640d) of "
       "cgif_file_fuzzer.asan-ubsan -> fuzz_uci.asan-ubsan, itabranges whole-text rule: 1 range (0x2fbf0, 104424 words)) "
       "with the measured tail inserted (plantail.py probef + insert --replace-tail: 2 XMemset nodes, x_memset 0x9085c, "
       "before every PRun [main 0x7ee48]); the plan the collected pass 2 ran. Image: the pinned "
       "fuzz_uci.asan-ubsan, sha256 a1b86e424adde6f65d345459822690a6c21e9e606446b91b4ad25e9f3ef6e7fc.")
hdr = hsform.header(donor, [], None, MOD)
t = open(tail).read()
i = t.find('\nDefinition ')
txt = '\n'.join(hdr) + '\n' + t[i + 1:]
open(out, 'w').write(txt)
print('mk_yb05_uci: wrote %s %d bytes sha256 %s' % (out, len(txt), hashlib.sha256(txt.encode()).hexdigest()))
