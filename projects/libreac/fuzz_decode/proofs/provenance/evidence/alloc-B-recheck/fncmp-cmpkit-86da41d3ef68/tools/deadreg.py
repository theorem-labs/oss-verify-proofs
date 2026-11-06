#!/usr/bin/env python3
"""deadreg.py -- class (e) DEAD-AT-CALL of the lui settlement: does a CALLEE read register r (holding a lui-derived value
the caller left in it, outside the callee's parameters) on ANY path, before writing it? The callee is analysed to its
return, every path covered (capstone decode; the control-flow graph of objscan.Fn: blocks split at every branch / jump
target; a `jr` dispatch goes to the measured jump-table cases, else to every block of the function):
  - an instruction that READS r (a source operand, a memory / jump base, a store's data) while r still holds the value
    -> READ (the value is used: not dead);
  - an instruction that WRITES r -> that path is done (dead from there on);
  - a call (jal / jalr ra) to g: g is analysed the same way (recursively, depth <= 6, memoised); READ in g -> READ;
    if g hands r back unchanged on some path (RETURNS-LIVE) the caller's path continues after the call with r live,
    else the path is done; an INDIRECT call (or a `jr` through a function pointer) with r live: when r is a temporary
    t0-t6, or an argument register at or beyond the arity of the pointer's type (contracts.REAL_ARITY for a REAL(x)
    cell, contracts.CALLBACK_ARITY for a callback site), the callee cannot read it under the psABI and the call clobbers
    it (the path is done); else -> UNKNOWN; a call to a function that does not return (NORETURN) ends the path after
    g's own analysis;
  - a return (or a tail call whose callee hands r back) with r still holding the value -> RETURNS-LIVE.
Result: ('READ', where) | ('UNKNOWN', why) | ('DEAD', returns_live: bool)."""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import objscan

MEMOP = re.compile(r'(-?(?:0x[0-9a-f]+|\d+))?\((\w+)\)\s*$')
NORETURN = {'_ZN11__sanitizer11CheckFailedEPKciS1_yy', '_ZN11__sanitizer3DieEv', '__stack_chk_fail', 'abort', '_Exit',
            '_exit', '_ZN11__sanitizer14internal__exitEi', '_ZN11__sanitizer23ReportMmapFailureAndDieEmPKcS1_ib'}
STORES = ('sb', 'sh', 'sw', 'sd', 'fsw', 'fsd')
REG = re.compile(r'^(zero|ra|sp|gp|tp|s\d+|a\d|t\d|fp)$')
# RISC-V Linux (asm-generic unistd.h) syscall numbers and argument counts of the syscalls in these images; an ecall
# reads a7 and a0..a(n-1) of ITS syscall (the kernel preserves every other register and writes a0)
SYSCALL_ARGS = {17: ('getcwd', 2), 24: ('dup3', 3), 29: ('ioctl', 3), 56: ('openat', 4), 57: ('close', 1),
                59: ('pipe2', 2), 61: ('getdents64', 3), 62: ('lseek', 3), 63: ('read', 3), 64: ('write', 3),
                78: ('readlinkat', 4), 79: ('newfstatat', 4), 80: ('fstat', 2), 93: ('exit', 1), 94: ('exit_group', 1),
                98: ('futex', 6), 101: ('nanosleep', 2), 113: ('clock_gettime', 2), 123: ('sched_getaffinity', 3),
                124: ('sched_yield', 0), 129: ('kill', 2), 131: ('tgkill', 3), 132: ('sigaltstack', 2),
                134: ('rt_sigaction', 4), 135: ('rt_sigprocmask', 4), 160: ('uname', 1), 167: ('prctl', 5),
                172: ('getpid', 0), 174: ('getuid', 0), 178: ('gettid', 0), 179: ('sysinfo', 1), 214: ('brk', 1),
                215: ('munmap', 2), 216: ('mremap', 5), 220: ('clone', 5), 221: ('execve', 3), 222: ('mmap', 6),
                226: ('mprotect', 3), 233: ('madvise', 3), 260: ('wait4', 4), 261: ('prlimit64', 4), 278: ('getrandom', 3)}


def syscall_number(ins, k):
    """the syscall number in a7 at the ecall ins[k]: the last write of a7 before it in straight-line code (li / addi a7,
    zero, N); None when another write, a branch target crossing or a call comes first"""
    for j in range(k - 1, max(-1, k - 40), -1):
        o, mn, op, n = ins[j]
        if op and op.split(',')[0].strip() == 'a7' and not mn.startswith('b') and mn not in STORES:
            m = re.match(r'a7, (?:zero, )?(-?(?:0x[0-9a-f]+|\d+))$', op)
            return int(m.group(1), 0) if mn in ('li', 'addi') and m else None
        if mn in ('jal', 'jalr', 'ret', 'j', 'jr') or mn.startswith('b'):
            return None
    return None


def syscall_reads(ins, k):
    n = syscall_number(ins, k)
    if n is None or n not in SYSCALL_ARGS:
        return {'a%d' % i for i in range(8)}
    return {'a7'} | {'a%d' % i for i in range(SYSCALL_ARGS[n][1])}


def regs_read(mn, op):
    """the integer registers an instruction reads (sources, bases, store data)"""
    if mn == 'ecall':
        return {'a%d' % i for i in range(8)}          # without the syscall number: every argument register (see syscall_reads)
    if not op:
        return set()
    ops = [x.strip() for x in op.split(',')]
    m = MEMOP.search(op)
    bm = mn.split('.')[0]
    if bm in STORES:
        return {ops[0]} | ({m.group(2)} if m else set())
    if bm == 'sc' or bm.startswith('amo'):
        return set(x for x in ops[1:-1] if REG.match(x)) | ({m.group(2)} if m else set())
    if m:                                             # loads, lr, jalr with offset(base)
        return {m.group(2)}
    if mn in ('j', 'jal') or mn.startswith('fence') or mn in ('lui', 'auipc', 'li'):
        return set()
    if mn in ('jr', 'jalr'):
        return {ops[-1]}
    if mn.startswith('b'):
        return {x for x in ops if REG.match(x)}
    return {x for x in ops[1:] if REG.match(x)}


def writes(mn, op):
    if not op:
        return None
    bm = mn.split('.')[0]
    if bm in STORES or mn.startswith('b') or mn in ('j', 'jr', 'ret', 'ecall', 'ebreak') or mn.startswith('fence'):
        return None
    if mn in ('jal', 'jalr'):
        ops = [x.strip() for x in op.split(',')]
        return 'ra' if (len(ops) == 1 or ops[0] == 'ra' or '(' in op) else (ops[0] if ops[0] != 'zero' else None)
    w = op.split(',')[0].strip()
    return w if REG.match(w) else None


def indirect_unread(img, a, ins, k, r):
    """(True, why) when the callee of the indirect call at instruction index k of the function at a cannot read r: a
    temporary t0-t6 (psABI), or an argument register at or beyond the arity of the function pointer's type (a REAL(x)
    cell, contracts.REAL_ARITY; a callback site, contracts.CALLBACK_ARITY)"""
    import contracts
    if re.match(r'^t[0-6]$', r):
        return True, 'a temporary register: ' + contracts.PSABI
    if not re.match(r'^a[0-7]$', r):
        return False, ''
    fn, off = img.name_at(a), ins[k][0]
    ar = contracts.CALLBACK_ARITY.get((fn, off))
    if ar is None:
        op = ins[k][2]
        m = MEMOP.search(op) if op else None
        base = m.group(2) if m else (op.split(',')[-1].strip() if op else None)
        cell = None
        for j in range(k - 1, max(-1, k - 8), -1):
            o2, m2, p2, n2 = ins[j]
            ops2 = [x.strip() for x in p2.split(',')] if p2 else []
            if not ops2 or ops2[0] != base:
                continue
            mm = MEMOP.search(p2)
            if m2 == 'ld' and mm:
                for i2 in range(j - 1, max(-1, j - 8), -1):
                    o3, m3, p3, n3 = ins[i2]
                    ops3 = [x.strip() for x in p3.split(',')] if p3 else []
                    if m3 == 'auipc' and ops3 and ops3[0] == mm.group(2):
                        cell = a + o3 + (int(ops3[1], 0) << 12) + int(mm.group(1) or '0', 0)
                        break
            break
        if cell is not None:
            nm = re.match(r'^_ZN14__interception\d+real_(\w+)E', img.home(cell))
            if nm and nm.group(1) in contracts.REAL_ARITY:
                ar = contracts.REAL_ARITY[nm.group(1)]
    if ar is not None and int(r[1]) >= ar[0]:
        return True, '%s is beyond the %d argument(s) of the function pointer: %s; %s' % (r, ar[0], ar[1], contracts.PSABI)
    return False, ''


class Dead:
    def __init__(self, img):
        self.img = img
        self.memo = {}

    def fn_of(self, a):
        z = [x for x in self.img.funcs if x[0] == a]
        return z[0][1] if z else None

    def analyse(self, a, r, depth=6, stack=(), ignore_reads=False):
        """ignore_reads=True: only whether r may come back unchanged (for a parameter the callee reads)"""
        key = (a, r, ignore_reads)
        if key in self.memo:
            return self.memo[key]
        if depth < 0 or a in stack:
            return ('UNKNOWN', 'depth / recursion at %s' % self.img.name_at(a)[:60])
        z = self.fn_of(a)
        if z is None:
            return ('UNKNOWN', 'no function at %#x' % a)
        f = objscan.Fn(self.img, a, z)
        ins = f.ins
        seen, work = set(), [f.lead[0]]
        returns_live, res = False, None
        while work and res is None:
            s = work.pop()
            if s in seen:
                continue
            seen.add(s)
            k, live = s, True
            while k <= f.end[s] and live and res is None:
                o, mn, op, n = ins[k]
                reads = syscall_reads(ins, k) if mn == 'ecall' else regs_read(mn, op)
                if r in reads and not ignore_reads:
                    res = ('READ', '%s +%#x %s %s' % (self.img.name_at(a)[:70], o, mn, op)); break
                if mn == 'ecall' and r == 'a0':
                    live = False; break                # the kernel writes the result to a0
                kd, tg, inside = f.kind[k]
                if kd == 'ijmp' and tg is not None and tg in self.img.starts and not inside:
                    kd = 'tail'
                if kd == 'ijmp' and not self.img.cases.get(a) and (tg is None or tg not in self.img.starts):
                    kd = 'tail'                        # a `jr` through a function pointer (no switch table here)
                if kd in ('call', 'tail'):
                    if tg is None or tg not in self.img.starts:
                        ok, why = indirect_unread(self.img, a, ins, k, r)
                        if ok:
                            live = False; break         # the indirect callee cannot read r; the call clobbers it
                        res = ('UNKNOWN', 'indirect call at %s +%#x with %s live' % (self.img.name_at(a)[:60], o, r)); break
                    sub = self.analyse(tg, r, depth - 1, stack + (a,), ignore_reads)
                    if sub[0] != 'DEAD':
                        res = (sub[0], '%s +%#x -> %s' % (self.img.name_at(a)[:50], o, sub[1])); break
                    if self.img.name_at(tg) in NORETURN or not sub[1]:
                        live = False; break             # g does not return, or writes r on every path
                    if kd == 'tail':
                        returns_live = True; live = False; break
                    k += 1; continue
                if kd == 'ret':
                    returns_live = True; live = False; break
                if writes(mn, op) == r:
                    live = False; break
                k += 1
            if res is None and live:
                if f.succ[s]:
                    work.extend(f.succ[s])
                else:
                    res = ('UNKNOWN', 'a path leaves %s at +%#x with %s live' % (self.img.name_at(a)[:60], ins[f.end[s]][0], r))
        if res is None:
            res = ('DEAD', returns_live)
        self.memo[key] = res
        return res
