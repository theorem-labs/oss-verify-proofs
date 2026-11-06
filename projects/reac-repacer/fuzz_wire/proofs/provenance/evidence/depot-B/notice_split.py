#!/usr/bin/env python3
"""notice_split.py FILE... -- split an inherited `Modified by` notice from the documentation it runs on into.

The knock-only closure files of image B (lib/B/YD3i.v, YD3j.v, YD3k.v) carry fuzz_knock's released lib/AU text, whose
line 3 opens a `Modified by Theorem Labs, 2026-10: new file, written by <attribution>` notice that runs on into the
file's documentation in the same comment, so the licence tool cannot bound the notice (`embedded notice: cannot bound
<file>:3`). This script gives the notice its own one-line comment and puts the documentation in a second comment right
after it (the unit owner's ruling, 2026-10-31 15:33Z), changing no other byte:

  - the notice is line 3 up to the first `: ` after `written by` (the attribution), closed with ` *)`; the rest of
    line 3 becomes the second comment's first line, opened with `(* `;
  - when line 3 holds no `: ` after `written by` (the attribution runs on into line 4), line 3 is the notice, closed
    with ` *)`, and the second comment opens on a new line `(*` before line 4;
  - every other line, the Copyright and SPDX lines and the code, is byte-unchanged.

The comment-stripped token stream is unchanged. A file already split (line 3 already closes its comment) is left as it
is, so a second run changes nothing; a file whose line 3 does not open that notice is refused (exit 1).
"""
import sys

HEAD = '(* Modified by Theorem Labs, 2026-10: new file, written by '


def split(text):
    lines = text.split('\n')
    l3 = lines[2]
    if not l3.startswith(HEAD):
        return None, 'REFUSED: line 3 does not open the notice'
    if l3.rstrip().endswith('*)'):
        return None, 'unchanged: line 3 already closes its comment (split already)'
    at = l3.find(': ', len(HEAD))
    if at >= 0:
        new = [l3[:at] + ' *)', '(* ' + l3[at + 2:]]
        how = 'notice = line 3 up to the attribution; the rest of line 3 opens the second comment'
    else:
        new = [l3 + ' *)', '(*']
        how = 'notice = line 3 (its attribution runs on into line 4); the second comment opens before line 4'
    return '\n'.join(lines[:2] + new + lines[3:]), how


def main():
    bad = 0
    for p in sys.argv[1:]:
        text = open(p).read()
        out, how = split(text)
        name = p.split('/lib/')[-1]
        if out is None:
            print('notice_split: %s: %s' % (name, how))
            bad += how.startswith('REFUSED')
            continue
        open(p, 'w').write(out)
        print('notice_split: %s: %s' % (name, how))
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
