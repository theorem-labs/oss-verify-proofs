import sys, json, os
sys.path.insert(0, os.environ.get('REVCHECK_DIR') or sys.exit('set REVCHECK_DIR to the directory holding revcheck.py (NOTES.md, Commands)'))
import revcheck as rc
ROOT = os.environ.get('PIPELINE_ROOT') or sys.exit('set PIPELINE_ROOT to the pipeline libreac root (it holds bin/ and unstripped/)')
P={'asan':ROOT+'/unstripped/fuzz_boxreg/fuzz_boxreg.asan',
   'ubsan':ROOT+'/unstripped/fuzz_boxreg/fuzz_boxreg.asan-ubsan'}
out={}
for k,p in P.items():
    e=rc.Elf(p)
    out[k]={'syms':[list(s) for s in e.syms],
            'secs':[[n,int(s['addr']),int(s['size']),int(s['type'])] if isinstance(s,dict) else None for n,s in []],
            'phoff':int(e.phoff),'phes':int(e.phes),'phn':int(e.phn)}
    # sections
    try:
        out[k]['sections']=[[s[0], int(s[1]), int(s[2])] for s in []]
    except Exception: pass
    out[k]['raw_secs']=repr(e.secs)[:4000]
    out[k]['raw_loads']=repr(e.loads)[:4000]
    out[k]['raw_tls']=repr(e.tls)[:2000]
json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'syms.json'), 'w'))
print('ok', {k:len(v['syms']) for k,v in out.items()})
print(out['asan']['raw_secs'][:1500])
print('LOADS', out['asan']['raw_loads'][:800])
