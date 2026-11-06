#!/usr/bin/env python3
"""ad1g_guard.py AD1g.v -- the one recorded edit of lib/A/AD1g.v after depot_apply.py lays it: the dead arm.

The xcell width-0 guard is NOT written here: it is knock's registered form, taken as two hunks of consumer-classes
(AD1g hunk 84, `| Some (rb, rk), AV v => if Nat.eqb (c_w c) 0 then true else match xval v, ..` in xcell, and hunk 86,
xcell_sound's `destruct (Nat.eqb w 0) eqn:Hw0. { .. lia. }` branch), so xcell / xcell_sound are knock's released lines.

dead arm (the ruling relayed for wire and egress): the image-bound proof line's tail
    `apply Z_mod_mult || (change N with (K * 4096); apply Z_mod_mult).`  becomes  `apply Z_mod_mult.`
when N is not K * 4096 (port_core moved the image bound N but not the factor K, so the second arm can never apply); a
live arm (N = K * 4096) is refused, not removed. The file is rewritten in place; the run refuses (exit 1) unless the
anchor occurs exactly once. Prints the unified diff."""
import difflib, re, sys

p = sys.argv[1]
old = open(p).read()
DEAD = re.compile(r'apply Z_mod_mult \|\| \(change (\d+) with \((\d+) \* 4096\); apply Z_mod_mult\)\.')
arms = DEAD.findall(old)
if len(arms) != 1:
    sys.exit('ad1g_guard: dead-arm anchor found %d times' % len(arms))
n, k = map(int, arms[0])
if n == k * 4096:
    sys.exit('ad1g_guard: the arm `change %d with (%d * 4096)` is live: refused' % (n, k))
new = DEAD.sub('apply Z_mod_mult.', old)
print('ad1g_guard: dead arm removed: %d is not %d * 4096 (= %d)' % (n, k, k * 4096))
open(p, 'w').write(new)
sys.stdout.writelines(difflib.unified_diff(old.splitlines(True), new.splitlines(True), 'a/A/AD1g.v', 'b/A/AD1g.v'))
