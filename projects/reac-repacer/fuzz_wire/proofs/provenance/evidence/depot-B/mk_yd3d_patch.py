"""mk_yd3d_patch.py YD3D > yd3d-env.patch -- the port_core --patch of image B's B/YD3d.v: its one Require of B.YF0r (knock's
class-1 walk, out by ruling (B)) names the glue B.YD3dEnv instead (mk_glue_ad3d.py --image B), the image-B twin of the image-A core's
image-A patch ad3d-env.patch (A/AD3d.v: AF0r -> AD3dEnv). YD3D: B/YD3d.v as port_core stages it out without the patch
(step 1's stage-out). The patch has no context line, as the image-A core's; the script refuses unless exactly one code line Requires
YF0r from lib.B."""
import os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from depot_classify import decomment

t = open(sys.argv[1]).read()
lines, code = t.split('\n'), decomment(t).split('\n')
hits = [i for i, c in enumerate(code) if re.search(r'\.lib\.B\s+Require\b', c) and re.search(r'\bYF0r\b', c)]
if len(hits) != 1 or code[hits[0]] != lines[hits[0]]:
    sys.exit('mk_yd3d_patch: %d code lines Require YF0r (or the line holds a comment)' % len(hits))
i = hits[0]
new = re.sub(r'\bYF0r\b', 'YD3dEnv', lines[i])
sys.stdout.write('--- B/YD3d.v\n+++ B/YD3d.v\n@@ -%d +%d @@\n-%s\n+%s\n' % (i + 1, i + 1, lines[i], new))
