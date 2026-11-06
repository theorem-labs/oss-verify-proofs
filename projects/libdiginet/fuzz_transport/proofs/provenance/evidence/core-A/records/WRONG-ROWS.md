# The WRONG rows of the hypothesis-value audit on the run of record, each read by hand

proves no function (kind: measurement). The audit (checks/hypvalues.sh WORK LIB OUT, records/RESULT.txt) derives every
relocated numeral by its DONOR role: symbol + offset, section bound, bytes, jump table. Where this core states a value
that is not the donor's quantity moved to this image, its rules say WRONG. On the run of record (WORK = work-rec5) they say
WRONG at 1 listed row (a hypothesis position) and at 34 rows outside hypothesis positions (unlisted-derived.tsv,
information only); the 3 listed CZONE rows are KNOWN (the audit's own rule, checks/hypderive.py KNOWN). Each of the 35 is a
value set on purpose with its own measurement, or a reading the image contradicts. None is a defect.

## The listed WRONG row: A/AD1o.v:87, 0x5f3200

- The row (records/differs.tsv): `A/AD1o.v:87 lemma-premise bss_shadow_facts donor 0xa14a0 written 0x5f3200 WRONG
  SYMBOL`, derivation `donor 0xa14a0 = __do_init.__object+0x10 (size 0x40, .bss); target __do_init.__object at 0xa9350
  (size 0x40) + 0x10 = 0xa9360`.
- The line (stage-out A/AD1o.v:87): `Lemma bss_shadow_facts : forall ly S W mem md p n, AR tfibsegs B ly S W mem md ->
  0x5f3200 <= p -> p + n <= 0x616000 -> 0 < n -> range_addressable ... SHADOW_OFF p n /\ shadow_hull_vis ... p n.`
  0x5f3200 is the lower bound of the lemma's premise on p.
- What the donor states: the donor's lemma reads the one zero-shadow range [0xa1460, 0x5fa000) (fuzz_grant's .bss after
  asan_globals, to its image top), and its premise bound 0xa14a0 lies 0x40 above that range's start. The rule reads 0xa14a0
  by its symbol role (__do_init.__object + 0x10) and gives that object's twin + 0x10 = 0xa9360.
- What this core states: bss-zero-range.patch makes the lemma read the piece [0x5f31e0, 0x616000) of LIB/A/AF0m.v:3105
  Tfib_zero_shadow (`bss_zero_shadow`, A/AD1o.v:80-86), because this image's list holds no range over the whole .bss (the
  18 instrumented harness globals cut it into pieces; METHOD.md, "Values this unit states otherwise than the donor", item
  2). The proof (A/AD1o.v:89-101) needs the premise bound at or above the piece's start: it takes `0x5f3200 / 8 <= p / 8`
  (L1, :93) to put every shadow byte of [p, p + n) at or above shadow_of_addr 0x5f31e0, the piece's first shadow byte
  (:98-100).
- The uses: the lemma's only uses are A/AD1o.v:214-215, at p = STDOUT_BUFA = 0x614200 and n = STDOUT_BSZ = 1024 (both
  Definitions of the core). They need 0x5f3200 <= 0x614200 and 0x614200 + 1024 = 0x614600 <= 0x616000; each holds.
- Verdict: RIGHT. Any bound b with 0x5f31e0 <= b <= 0x614200 makes both the proof and its two uses hold, and 0x5f3200 =
  0x5f31e0 + 0x20 is one. The rule's right value 0xa9360 is a tool limit here: it lies below the piece's start
  0x5f31e0, so with it the proof's step at :98-100 does not hold (a p in [0xa9360, 0x5f31e0) has shadow bytes outside the
  piece). The whole-unit build checks the proof and both uses (`lia`).

## The 34 rows outside hypothesis positions

| rows | where | what the rules say | why the written value is right |
|---|---|---|---|
| 16 | A/AD1o.v:81, 84, 91, 93, 95, 98, 99, 100 (0x5f31e0, 0x5f3200, 779840, 779836, 6238688, 17860) | the donor's 0xa1460 / 0xa14a0 are the end of asan_globals and `__do_init.__object + 0x10`, in this image 0xa9340 / 0xa9360 | the zero-shadow piece [0x5f31e0, 0x616000) that A/AD1o.v reads (above): its start 0x5f31e0 (= 6238688), the premise bound 0x5f3200, start / 8 = 779836, 0x5f3200 / 8 = 779840, (end - start) / 8 = 17860. Without the piece the build fails at A/AD1o.v:85 (METHOD.md item 2; records/decval-open-rows.tsv) |
| 3 | A/AD25.v:529, 532, 539 (0x5df0b8) | the donor's 0x5fa000 is fuzz_grant's image top, in this image 0x616000 | A/AD25.v reads the piece [0xa9340, 0x5df0b8), which holds the read window [0x5cf050, 0x5df050); without it the build fails at A/AD25.v:533 |
| 1 | A/AD1o.v:95 (797695) | 783359 read as an address | (0x616000 - 1) / 8 = 797695, the donor's (0x5fa000 - 1) / 8 for this image (gate (a) reason N-AD1o-TOP) |
| 6 | CZONE: A/AFhn.v:420, AFix.v:290, AFjb.v:289, AFju.v:587, AFkm.v:1306, AFkz.v:899 (the 3 listed ones are KNOWN) | `unshadow(0x80050000)` is theDepot + 0x1395e8, whose shadow here is 0x80050fd8 | the donor's 0x80050000 is a page-aligned BOUND, not the shadow of an object. This unit's bound is kLowShadowBeg 0x7fff7000 (Reusable/YG0f.v:22) + IMG_TOP 0x616000 / 8 = 0x800b9c00, the least shadow start of the secondary map that map_facts SM1 (A/AFjm.v:305) allows; the build's goal at A/AFju.v:663 needs it (its log: removed from the shipped tree on 2026-11-04; internal record, in git history); it is above the highest constant shadow end 0x800b663c (records/czone.txt) |
| 2 | A/AFem.v:129, 207 TOT_range (127008) | the donor's 127070 read as a byte of a .rodata string | a count: TOT := length (ly_tr0 ly) + 1 + depot_frames S (A/AFem.v:99), lo_tr0 <= 31 (Reusable/YG0f.v:326), depot_frames <= 31 * length d (A/AFem.v:39-40), DEPOT_MAX = 4096 (Reusable/YG01.v:142): 31 + 1 + 31 * 4096 = 127008 |
| 1 | A/AB1w.v:11 tfib_rodata_hi (0x22b4c) | the words around the donor's 0x22c0c read as a jump table, giving 0x22b0c | the cell is a section edge: the pin's section header gives .rodata [0x102e0, 0x22b4c); port_core 83f5203d2a2f's item 97 writes it; the donor's value is 0x40 short of fuzz_grant's own .rodata end (records/secbounds.txt: 22 of 22 equal) |
| 1 | A/AB1w.v:441 tfib_E_diginet_msg_next (0x8cfc0) | the donor's 0x81f24 is fuzz_grant's `asan.module_ctor`, here 0x86250 | the cell is the END of this unit's own function: the twin's symbol table gives diginet_msg_next at 0x8c9f8, size 1480, end 0x8cfc0 |
| 4 | A/AFem.v:413 (408118), A/AFfu.v:410 and A/AFg1.v:298 (88960), A/AFjr.v:628 (86664) | bytes of .rodata strings or `internal_alloc_placeholder` offsets | each is an operand of an `exists` / `replace` inside a proof (`exists (408118 + bkt)`, `exists (88960 + pa / 2 ^ 32)` for 711680 = 8 * 88960, `replace (693144 + 168 + 8 * LGv) with ((86664 + LGv) * 8)`), so the whole-unit build checks it: a wrong value does not type-check |

## The audit's other rows

Listed 40573 numerals, 1541 differ from the donor (DIFFERS 1531, NEW 10); derived OK 1537, KNOWN 3, OPEN 0. Among the OK
rows: COUNT 3 (A/AD2f.v:59 and :154 IMG_E / IMG_B 54 = length IMG_REGIONS, A/AD2e.v:64 PM_tailL 56 = length IMG_REGIONS
+ 2), each against LIB/A/AD2j.v:219, T3r's cut file at the pin (54 regions); GPATCH 8 (the numerals 0, 2 and 64 on the
lines the G patches add: `ajournal_gx ... G 0 []` at A/ACfn.v:56 and A/AD1w.v:100, `0 <= a < 2 ^ 64` at A/AD1r.v:229 and
:301); NEW 2 decided by hand (A/AF0l.v class 5 of pc_stack_malloc). CONTENT 373 memory facts, WRONG 0. Controls of the
audit run: the four planted rows were caught (P1 a narrowed atom range listed as differing, P2 and P4 WRONG with the right
value, P3 a kept image bound KEPT-IMAGE); `control: PASS` (records/control.txt).
