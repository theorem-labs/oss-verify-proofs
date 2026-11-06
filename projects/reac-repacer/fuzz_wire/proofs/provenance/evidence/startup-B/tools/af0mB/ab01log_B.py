"""ab01log_B.py YB01.v OUT.log -- the start-up tools' runs/zg/ab01log.py test harness: writes a released YB01's hand-off
states in the collector log's HSDUMPHOLES / HSDUMP form, so af0m's donor CONTROL can run on cgif's released B states
(no both-arms cgif B pass-2 log exists). hsform is the start-up set of record's frozen a6de3be38c53, read from $FT. The
states are the file's own; nothing is computed."""
import os, sys
sys.path.insert(0, os.environ['FT'])
sys.dont_write_bytecode = True
import hsform  # noqa: E402
src, out = sys.argv[1], sys.argv[2]
st = hsform.donor_states(src, 'HS_tfib')
hs = sorted(st)
terms = ['Some (%s[%s]%s)' % (p, '; '.join(kn), s) for p, kn, s in (st[h] for h in hs)]
with open(out, 'w') as f:
    f.write('HSDUMPHOLES = 0\n     = [%s]\n     : list nat\n' % '; '.join('%d%%nat' % h for h in hs))
    f.write('HSDUMP = 0\n     = [%s]\n     : list (option acs)\n' % '; '.join(terms))
print('ab01log_B: %d states from %s -> %s' % (len(hs), os.path.basename(src), os.path.basename(out)))
