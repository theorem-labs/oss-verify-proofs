"""ab01log_B.py YB01.v OUT.log -- the runs/zg/ab01log.py test harness (as the T0.4 ab01log_frozen.py
aea7ad98af54): writes a released YB01's hand-off states in the collector log's HSDUMPHOLES / HSDUMP form, so af0m's
donor CONTROL can run on cgif's released B states (no both-arms cgif B pass-2 log is on this disk). hsform is the
8cd71d3a4bb set's frozen a93ebaea058f (tools/frozen-set). The states are the file's own; nothing is computed."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'frozen-set'))
sys.dont_write_bytecode = True
import hsform  # noqa: E402
src, out = sys.argv[1], sys.argv[2]
st = hsform.donor_states(src, 'HS_tfib')
hs = sorted(st)
terms = ['Some (%s[%s]%s)' % (p, '; '.join(kn), s) for p, kn, s in (st[h] for h in hs)]
with open(out, 'w') as f:
    f.write('HSDUMPHOLES = 0\n     = [%s]\n     : list nat\n' % '; '.join('%d%%nat' % h for h in hs))
    f.write('HSDUMP = 0\n     = [%s]\n     : list (option acs)\n' % '; '.join(terms))
print('ab01log_B: %d states from %s -> %s' % (len(hs), src, out))
