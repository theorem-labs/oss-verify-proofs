#!/usr/bin/env python3
"""Write a run's summary.out in the record's form: host paths as $IMG / $BIN / $DONOR / $OURS / $PLANT, and the
two fixed lines of the tool's output restated as in ../gate/ (the note line naming the tool's documentation file
reads "see the tool's documentation file"; the attribution of the file-pairing note reads "(the tool author's
note)"). Counts are not touched.
Usage: norm_summary.py WORKDIR BIN SUMMARY.out OUT.txt"""
import re
import sys

w, binp, src, dst = sys.argv[1:5]
t = open(src, encoding='utf-8').read()
for a, b in ((f'{w}/tree/donor', '$DONOR'), (f'{w}/tree/ours', '$OURS'), (f'{w}/plant', '$PLANT'),
             (f'{w}/img', '$IMG'), (binp, '$BIN')):
    t = t.replace(a, b)
# the documentation file's name at the end of the donor-vs-donor control line
t = re.sub(r'(?m)^(  control donor-vs-donor: .*; )see \S+\.md$', r"\1see the tool's documentation file", t)
# the attribution in parentheses at the end of the file-pairing note line
t = re.sub(r'(?m)^(  note file pairing: .*) \([^()]*\)$', r"\1 (the tool author's note)", t)
open(dst, 'w').write(t)
