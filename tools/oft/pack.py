"""How `oft plan` deals units into check jobs, from the measured proof-check times in proof-times.tsv.

A check job runs its units one after the other, and a unit with proofs takes from minutes to hours (no cache: a pull
request saves none), while a unit without proofs takes seconds.  Dealt in name order, the heavy units piled up in a
few jobs and those jobs hit the 6-hour limit.  So the units with proofs go first, longest first, each to the job with
the least time so far (ties to the lowest index), and then the rest each to the job with the fewest units.  The result
depends only on the units, the set with proofs, the job count and the table, so it is deterministic.

A job also carries `cpus`, the CPUs its check may use: the fewest the table gives any of its units, where a unit that
passed at the runner's full width counts for no limit.  Those are the CPUs measured to be safe on a 16-core 64 GB
runner (leptonica/paintcmap_fuzzer ran out of memory at 16, and openssl/hashtable swapped); 0 means every CPU the
runner has, so a larger runner is never held to 16.  ci/check-units.sh gives the checker container that many CPUs.
Since every unit of a limited job then runs on fewer CPUs, a proved unit the table limits gets a job with no other
proved unit, while there are jobs enough for the rest."""
import math
import os
import statistics

TABLE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "proof-times.tsv")


def load(path=TABLE):
    """{unit: (minutes, peak_gib, cpus)} from the table; lines starting with '#' and the header are skipped.  A unit
    listed twice, or a value that is not a positive finite number, is an error."""
    out = {}
    with open(path, encoding="utf-8") as f:
        for n, line in enumerate(f, 1):
            if not line.strip() or line.startswith("#") or line.startswith("unit\t"):
                continue
            unit, minutes, peak, cpus = line.rstrip("\n").split("\t")
            if unit in out or not int(minutes) > 0 or not 0 < float(peak) < math.inf or not int(cpus) > 0:
                raise ValueError("%s:%d: a unit listed twice, or a value that is not a positive finite number"
                                 % (path, n))
            out[unit] = (int(minutes), float(peak), int(cpus))
    return out


def full_width(table):
    """The most CPUs the table gives any unit: the runner's own width, which a job asking for it needs no limit for."""
    return max((row[2] for row in table.values()), default=0)


def shards(units, n, proved, table):
    """units dealt into n lists (n >= 1, at most len(units) when units is not empty), each sorted.  First each unit in
    `proved` that the table gives fewer CPUs than its most, slowest first, alone in its own job, when that leaves a
    job for the other proved units; then the other units in `proved` longest first, each to the job with the least
    time so far among the jobs not given to one of those; then the rest each to the job with the fewest units, so no
    job is empty.  An unlisted proved unit counts as the table's median (1 minute for an empty table)."""
    default = statistics.median(row[0] for row in table.values()) if table else 1
    minutes = lambda u: table[u][0] if u in table else default
    full = full_width(table)
    limited = sorted((u for u in units if u in proved and u in table and table[u][2] < full),
                     key=lambda u: (-minutes(u), u))
    if len(limited) >= n:
        limited = []
    out = [[] for _ in range(n)]
    load_ = [0] * n
    for i, u in enumerate(limited):
        out[i].append(u)
        load_[i] = math.inf
    for u in sorted((u for u in units if u in proved and u not in limited), key=lambda u: (-minutes(u), u)):
        i = min(range(n), key=lambda j: (load_[j], j))
        out[i].append(u)
        load_[i] += minutes(u)
    for u in sorted(u for u in units if u not in proved):
        out[min(range(n), key=lambda j: (len(out[j]), j))].append(u)
    return [sorted(s) for s in out]


def job_cpus(units, table):
    """The CPUs a job may use, for the units whose proofs it checks (the plan passes only those: a unit checked for
    its statements, counterexamples or findings alone never needs fewer): the fewest the table gives any of them, or 0
    (every CPU) when it lists none of them or gives each of them the most it gives any unit, the runner's full width."""
    full = full_width(table)
    fewest = min([table[u][2] for u in units if u in table], default=0)
    return 0 if fewest >= full else fewest
