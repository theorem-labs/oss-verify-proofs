#!/usr/bin/env python3
"""mk_yb05_wire.py DONOR_YB05 PLAN OUT -- fuzz_wire image-B YB05.v by fuzz_decode B's mk_yb05.py rule (mk_yb05.py, sha256 908e201feeb3, is not in the published tree):
the frozen hsform's header of the donor plan
(hsform.header, the start-up set of record's a6de3be38c53 read from $FT, one --modified line; donor module paths kept,
nsW.py rewrites them) followed by the body of the plan the collected pass 2 ran (the donor plan relocated by the
plan-relocation tool + itabranges, with the registration arm removed by plantail.py drop-registration + drop-nodes,
the 0-descriptor route: <donor ws>/ZReplyB/YB05.v). Fail-closed: the text it would write (the donor's copied header,
the plan's body) passes textguard.py first; a forbidden token stops it with exit 2 and nothing is written."""
import hashlib, os, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.environ['FT'])
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hsform  # noqa: E402
import textguard  # noqa: E402

donor, plan, out = sys.argv[1:4]
# the relocation tools are named by role and sha256 (their internal names are not shipped)
MOD = ("generated for reac-repacer/fuzz_wire image B: the donor plan relocated to this image (the image address map "
       "(map tool sha256 4d51ec1c0069) + the plan-relocation tool (sha256 2d846496640d) of "
       "cgif_file_fuzzer.asan-ubsan -> fuzz_wire.asan-ubsan, itabranges whole-text rule: 1 range (0x2ff5c, 105697 words)) "
       "with the registration arm removed (the image registers 0 ASan globals: plantail.py drop-registration from the "
       "registration loop head 0x3e1cc in all 50 arms, then drop-nodes of the 30 PRun [0x72650] and 30 PBump 500 nodes, "
       "the PCase2 split kept, so no tail node precedes PRun [main 0x7f758]); the plan the collected pass 2 ran. Image: "
       "the pinned fuzz_wire.asan-ubsan, sha256 af4534831a4528320c7dc74ca3f64bb96e8232ed2e313f01126d10879f3417d6.")
hdr = hsform.header(donor, [], None, MOD)
t = open(plan).read()
i = t.find('\nDefinition ')
txt = '\n'.join(hdr) + '\n' + t[i + 1:]
textguard.refuse(txt, out)
open(out, 'w').write(txt)
print('mk_yb05_wire: wrote %s %d bytes sha256 %s' % (out, len(txt), hashlib.sha256(txt.encode()).hexdigest()))
