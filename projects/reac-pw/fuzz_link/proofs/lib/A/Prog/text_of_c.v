(* text_of (fuzz_link.c:126-136) on image A (fuzz_link.asan 0x87dc0, 832 bytes; listing
   (internal path) (internal record, sha256 1c4fdcbb52aa)): a text from the table `texts`, or
   a heap copy of the input's own bytes cut at their first NUL. a0 = in (the input cursor: the data pointer at +0, the
   count of bytes left at +8), a1 = own (where the copy to free is stored). The plain contract is lib/Prog/text_of_c.v
   (an SR-shape contract over the plain allocator interface); this file states the same result in link_amem.v's
   `aleaf_alloc_rd` form (link-a/form/FORM.md (internal record, sha256 13aeff774164) sections 1, 2, 3, 4.3; the read set of
   link_amem.v's section "THE READ SET"). p = aarg regs 0, o = aarg regs 1; (c0, c1) = the cursor's two words at the call.

   The image-A code, in order:
     +0x00..+0x1c  push a 64-byte frame; save ra, s0..s5                (no realignment)
     +0x20..+0x28  s4 := the shadow base, loaded through the .got cell 0xa19d0 (LA_GOT_SHADOW, which holds
                   LA_SHADOW_CELL = 0xaa438, which holds the base)
     +0x2c..+0x40  a2 := p; a0 := p + 8; check of p + 8 (8-byte load)
     +0x44  s0 := o (s0 keeps o to the end: no frame record);  +0x48  ld a1 := count;  +0x4c  beqz -> +0x12c
     count <> 0: +0x50..+0x60 check, count := c1 - 1 (sd 8(a2));  +0x68..+0x78 check, ld c0, cursor := c0 + 1;
       +0x7c..+0x88 check of c0 (1-byte load);  +0x8c..+0x98 check of o (8-byte store; s5 := its shadow address);
       +0x9c  lb a1 := the selector byte (sign-extended);  +0xa0  sd zero, 0(o);  +0xa4  bgez a1 -> +0x144
     selector bit 7 set (fuzz_u16 then fuzz_take): +0xa8..+0xb4 check, ld count, beqz -> +0x1a0 (u16 := 0);
       +0xb8..+0xec  count -= 1, cursor += 1, lbu lo := byte at c0 + 1 (checked);  +0xf0  beqz -> +0x1a4 (hi := 0);
       +0xf4..+0x124  count -= 1, cursor += 1, lbu hi := byte at c0 + 2 (checked);
       +0x1a8..+0x1dc  v := hi * 256 + lo; want := v mod 320 (multiply by 0xcccd, shift 24, times 320, subtract);
       +0x1d0  ld rem := count;  +0x1e0..+0x1e4  n := min(want, rem) (bltu);
       +0x1e8..+0x208  checks; q := cursor (ld s2); cursor := q + n; count := rem - n;
       +0x20c  n = 0 -> +0x298 (k := 0);  else +0x210..+0x21c wrapper_memchr(q, 0, n) (0x43060); +0x220..+0x224
       k := index of the first NUL, or n;
       +0x228..+0x22c  wrapper_malloc(k + 1) (0x540cc, return address 0x87ff0);  +0x230 beqz -> +0x2b4 (abort path);
       +0x238..+0x248  k <> 0: checked_memcpy(b, q, k) (0x52d78);  +0x24c..+0x260  check, sb zero, 0(b + k);
       +0x264..+0x26c  check of o, sd b, 0(o);  +0x270  a0 := b
     table arm (+0x12c for count = 0: check of o, sd zero, 0(o), selector 0; +0x144 for bit 7 clear):
       +0x144..+0x184  i := (selector & 0xff) mod 11; a0 := texts + 8 i (auipc/addi: LA_TEXTS = 0xa17c0);
       +0x188..+0x194  check of texts[i] (8-byte load);  +0x198  ld s3 := texts[i];  j +0x270
     +0x270..+0x294  a0 := s3; restore, pop, ret.
   The listing's earlier `.got` notes at 0x87f90 / 0x87fb0 / 0x87fb8 are gone: a2 there is the cursor
   (`ld a1, 8(a2)`, `ld s2, 0(a2)`, `sd a3, 0(a2)`).

   THE INSTRUMENTED CHECKS. 19 check sites, 19 error-path calls (link-a/facts/asan-facts.tsv
   (internal record, sha256 05ab19b7928f) counts 9: the shadow ADDRESSES the code forms, p + 8, p, c0, o, c0 + 1,
   c0 + 2, o again at +0x12c, texts + 8 i, b + k). An 8-byte check (`lbu`, `bnez` to the error path) passes only on
   shadow byte 0, which `range_addressable` of the 8 bytes gives at any alignment (YG0v.v check_passes_whole: the
   granule's last byte is among the 8); a 1-byte check passes on s = 0 or (x & 7) < s (YG0v.v check_passes_lb). Stores
   that follow a load check of the same word are not checked again (+0x78, +0xdc, +0x1f8).
     p + 8, 8-byte: +0x3c (load, errpath_load8 +0x2e8), +0x50 (store, errpath_store8 +0x2f0), +0xa8 (load, +0x30c),
       +0xb8 (store, +0x328), +0xf4 (store, +0x334), +0x1a8 (load, +0x310), +0x1fc (store, +0x31c);
     p, 8-byte: +0x68 (load, +0x2f8), +0xc8 (load, +0x330), +0x104 (store, +0x33c), +0x1e8 (load, +0x318):
       all from `range_addressable (ard m) SHADOW_OFF p 16`;
     o, 8-byte store: +0x94 (+0x300), +0x134 (+0x308), +0x264 (+0x324): `range_addressable ... o 8`;
     c0, c0 + 1, c0 + 2, 1-byte load: +0x84 (errpath_load1 +0x2b0), +0xe4 (+0x2d4), +0x11c (+0x2e4): reached only
       when that byte is among the c1 bytes left: `range_addressable ... c0 c1`;
     texts + 8 i, 8-byte load: +0x190 (errpath_load8 +0x2ec): the address depends on the selector, so it is a real
       check: `range_addressable ... LA_TEXTS (8 * TEXTS_N)`;
     b + k, 1-byte store: +0x258 (errpath_store1 +0x2c4): the fresh block of malloc(k + 1); its shadow is AR's block
       shadow after malloc (AR_shadow_law, YG0d.v), no premise.

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x1c (inside [sp - K, sp)); memchr (boxreg
     origin/ossv/recipes lib/A/Rt/MemchrDef.v `amemchr_realizes`; its port onto link is the libc slice's) and
     checked_memcpy (YG0d.v:325-343 `aintrin_realizes OCpy`) take ecall_pre at sp' = sp - 64, which the walk derives
     from the journal; memchr's `rom_view W mem` is a fact of the image and the journal (arodata_okP, with the
     instance's runtime statics and errno in writable segments), not a premise here; malloc takes the journal-level
     malloc rule at sp' (see THE MALLOC TRACE); +0x294 ret.
   - K = 64 + ASTACK = 16448: the 64-byte frame, then the deepest callee window, malloc's [sp' - ASTACK, sp')
     (Reusable/YC5d.v:60: sp0 - STK <= sp' - ASTACK; YG0d.v acall_pre); memchr's and checked_memcpy's ESTACK windows lie
     inside it. No realignment. link-a/form/FORM.md (internal record, sha256 13aeff774164) section 5's row (16448)
     holds. The plain K (48 + ALLOC_STACK) does not carry over.
   - the cursor: `au64_at m p c0`, `au64_at m (p + 8) c1` with their ranges (the loads +0x48, +0x70, +0xb0, +0xd0,
     +0x1d0, +0x1f0; the plain `rw_cells [C8 c0; C8 c1]`); `abuf m p 16` (the stores +0x60, +0x78, +0xc4, +0xdc,
     +0x100, +0x110, +0x1f8, +0x208); its range_addressable (the checks above) and `amem_range p 16` (each check's
     shadow entry needs the checked byte to be an application byte, outside the shadow band: the walk kit's
     shent_ok / app_apart; `ajw` does not give it, since awr_byte's own-frame clause also admits the shadow bytes
     of the owner's side frames; text_of's walk, 2026-10-30); `apart_frame regs K p 16` (the frame
     stores do not touch it; it is outside the callees' windows, so their kept clauses keep it, and the Post can
     state its value after malloc); `p mod 8 = 0` (THE MALLOC TRACE: the word the unwinder reads below o is then a
     whole cursor word or a word text_of does not write).
   - *own: `abuf m o 8` (the stores +0xa0, +0x140, +0x26c; the plain `exists w, rw_cells [C8 w]`); its
     range_addressable and `amem_range o 8` (the check +0x264 of the store +0x26c; the same reason as the
     cursor's); `shadow_hull_vis o 8` (the check +0x264 runs AFTER the malloc at +0x22c, whose kept clause does not
     keep a real-stack byte's shadow; the walk carries o's range_addressable across the call with the walk kit's
     shadow transport (LinkWalkShadow.v shadow_transport / sbyte_transport), which needs the shadow word visible at
     the call; text_of's walk, 2026-10-30. The cursor needs none: its checks +0x34, +0x50, +0x5c, +0x8c,
     +0x12c, +0x1a8, +0x1e8, +0x1fc all run before +0x22c, and after it only o and the fresh block are checked);
     `apart_frame regs K (o - 16) 24` (the slot and the 16 bytes under it are outside
     [sp - K, sp): the frame stores do not touch them, the callees' kept clauses keep the slot, and THE MALLOC TRACE
     needs the two words under it unchanged by the frame stores, e.g. o = sp would put the saved s0 / ra at
     o - 16 / o - 8); `apart o 8 p 16` (the stores to the two do not overlap, so the Post can state both). *own need
     not be zero (plain lesson): +0xa0 / +0x140 store 0 before any read; the code never reads *own.
   - the input [c0, c0 + c1): `abytes m c0 inp`, `length inp = c1` (the loads +0x9c, +0xec, +0x124, memchr, and
     checked_memcpy read only bytes among the c1 left: adv <= c1 at every step); `range_addressable ... c0 c1` (the
     three 1-byte checks; memchr's and checked_memcpy's range checks of [q, q + n) and [q, q + k), sub-ranges);
     and, when c1 > 0: `shadow_hull_vis ... c0 c1` (memchr's and checked_memcpy's `0 < n -> shadow_hull_vis` of
     the sub-range: the hull of a sub-range lies in this hull), `amem_range c0 c1` (their amem_range of the
     sub-range, and `x + n <= 2 ^ 63`; memchr's `0 < x` holds as x = c0 + 1..3 with 0 <= c0),
     `apart_frame regs K c0 c1` (their `src_ok`: outside their ESTACK windows; the frame stores do not touch the
     input), `apart c0 c1 p 16` and `apart c0 c1 o 8` (the cursor and *own stores before memchr and checked_memcpy
     do not change the input; the plain premise), `c0 + c1 <= o` (THE MALLOC TRACE).
   - the unwinder's words under o: the 16 bytes [o - 16, o) readable, and the 8-byte word at o - 16 at most o
     (THE MALLOC TRACE).
   - the table: `range_addressable ... LA_TEXTS (8 * TEXTS_N)` (+0x190); `apart p 16 LA_TEXTS 88`,
     `apart o 8 LA_TEXTS 88` (+0x198 reads the table after the stores +0x60, +0x78, +0xa0; the plain premises);
     each entry i < 11 a pointer q (with its range: au64_at fixes it only modulo 2 ^ 64, link-a/plan/CONTRACTS.md
     (internal record, sha256 5cd783c633c3) 6a class 2), 0 < q, to a C string s of fewer than 320 bytes, its bytes and
     NUL `text_of_ro` (read-only image the journal never changes: in_roP, not a runtime static, not errno: exactly the
     bytes arodata_okP fixes at every journal state), apart from the cursor and *own (so the stores leave it): the plain
     `G_img_c B [(A_TEXTS, 88)]` with `segs = rsegs` and `ro_agree`, re-stated over the A views because segs is a
     parameter here (the instance
     discharges it from the image: see the witness).
   - `text_of_traces`: THE MALLOC TRACE below.
   - the room (aleaf_alloc_rd): malloc's request is k + 1 <= n + 1 <= 320 (want = v mod 320 <= 319, n <= want):
     LIVE = 320 gives its `blocks_bytes Sc + (k + 1) <= LIVE_MAX` and `0 <= k + 1 < MALLOC_MAX`; MO = mo_malloc MT
     320 gives its meter `mo_ok MT Sc (mo_malloc MT (k + 1))` (ameter_laws mo_malloc_mono, mo_ok_le); EV = 1 and
     apre's `st_nev S + k + 1 <= EV_MAX` give its `st_nev Sc < EV_MAX`. With these malloc does not answer 0, so
     +0x230 falls through: THE ABORT PATH IS UNREACHABLE (the plain `room_slots b 320` did this on the plain
     allocator). memchr is no allocator event, and no allocator event precedes malloc, so the state at the malloc
     call has Sc's depot, meter and blocks.
   SIDE = [] (no frame_alloc).

   THE MALLOC TRACE (0x87fec). text_of keeps o in s0 (+0x44 `mv s0, a1`) and builds no frame record, so malloc's frame
   record links to o (link-a/design/ACEJ-WILD.md (internal record, sha256 6ee1df95f779) section 1): at the wrapper's
   entry ra = 0x87ff0, s0 = o, and the journal-level rule asks `chain_pre lyc rd regsT ch` (YG0d.v:219-224) and the
   trace `call_trace0 pc0 regsT ch` = `unwind_of_chain pc0 ((sp', 0x87ff0, o) :: ch)` (YCbq.v:314, YG00.v:375),
   pc0 = pc_malloc_ra0 (as_code B) (0x5436c on image A). The chain from o reads [o - 8] (pushed iff >= 4096: at
   0x82e24 / 0x837d8 the other result slot s1 + 0x128, at 0x82e34 the count slot) and [o - 16] (the count slot
   s1 + 0x120, or the cursor's data pointer): the third trace element is input-dependent, so the trace is WILD: [0x5436c;
   0x87ff0] or [0x5436c; 0x87ff0; w] (link-a/design/ACEJ-WILD.md (internal record, sha256 6ee1df95f779) sections 2-3).
   - `text_of_traces`: [pc_malloc_ra0 (as_code B); 0x87ff0] is a wild prefix of the universe, `In ... (u_wild
     (as_universe B))`. Every trace from this call starts with it (0x87ff0 <> pc0) and has at most kUnwindMax words
     (the firstn of unwind_of_chain), so it is `inU (as_universe B)` by `wild_shape`, whatever the unwinder reads
     (YG01.v:142-144); with `LedPre Sc` (wild part + 1 <= u_wmax) the room disjunct of `admits` holds
     (YG01.v:152-155). On image A this is lib/A/ACejUniv.v `Tfib_univ_wild` (u_wild = [[0x5436c; 0x87ff0]]).
     Unlike text_buf's `text_buf_traces`, the premise is not stated over CTX: the trace does not run through the
     entry chain (CTX lists `raZ regs :: spine ch` at text_of's entry; the wrapper's record links to o, not to the
     caller's s0), so no context fixes its tail, and a premise over CTX (`TEXT_OF_MALLOC_RA :: tl c`) would describe
     a trace the walk never meets. CTX stays a section Variable because aleaf_alloc_rd takes it.
   - the chain exists: o mod 8 <> 0 or o outside (sp', top - 16) ends it at once (bad_next); otherwise fpchain reads
     [o - 8] (readable by the premise) and, when it is >= 4096, [o - 16] (readable), whose value at the malloc call
     is (p mod 8 = 0, so word-granular; [o - 16, o) is outside the frame and every callee window, so only the cursor
     stores can change it) a cursor word c0 + adv or c1 - adv (adv <= c1), or the word at o - 16 at the call: each
     <= o by `c0 + c1 <= o` and the word premise, so bad_next ends the chain after one record. No word above o is
     read.
   - LedPre / LedPost (ruling: +1 per call; link-a/form/FORM.md (internal record, sha256 13aeff774164) section 1;
     lib/A/LinkWildRoom.v is the caller's sum): room for one more wild trace; after the call at most one more.
   OPEN (walk-side rule): the journal-level malloc rule on this branch, Reusable/YC5d.v:56-74 `amalloc04_rule`,
   asks `In (call_trace0 (pc_malloc_ra0 code) regsT ch) (as_universe B)`, whose coercion is u_fix: it does
   not apply to [0x5436c; 0x87ff0; w] for w >= 4096. The walk needs a wild twin of it whose trace premise is
   `admits (as_universe B) (call_trace0 ...) Sc` (or inU plus the room), as YG0d.v:265 `amalloc_realizes` already asks of the
   runtime, proved from amalloc_realizes as Reusable/YCbp.v proves `amalloc04_rule_triv`, and lifted onto `ajournal_gx` like
   the other runtime calls (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 10 item 9). Not written here.

   - `apart (as_errno B) 4 p 16` (the same class as the kernel-call walk's finding against model_read / model_write): the
     cursor's two words are stored at +0x1f8 / +0x208, BEFORE the malloc at +0x22c, and the Post states them after
     it; the malloc rule's kept clause (acall_kept through `ascratch`, YG0d.v:216-217) excepts
     [as_errno B, as_errno B + 4), and the Pre locates the slot nowhere, so without this the statement allows the
     cursor to BE errno bytes. True at the three call sites: the slot is in LLVMFuzzerTestOneInput's REAL frame,
     errno is an image byte. NOT asked of *own: its final value is the store +0x26c, AFTER the malloc (copy arm),
     or +0xa0 / +0x140 with no callee after it (table arms), so no call has to keep it (comparer, 2026-10-30).

   The write set: the cursor [p, p + 16) and the *own slot [o, o + 8). At the callers they are slots of
   LLVMFuzzerTestOneInput's REAL frame (0x82e1c `addi a0, s1, 0x118`, 0x82e20 / 0x837d4 `addi a1, s1, 0x130`,
   0x82e30 `addi a1, s1, 0x128`; s1 = the realigned sp, 0x82814 / 0x82818), inside its journal window
   [sp0 - STK, sp0): `ajw` holds of them by awr_byte's window clause (XO = 0). The fresh block's bytes (checked_memcpy
   and +0x260 write them) are NOT in Wr: Wr is evaluated at the call, where the block does not exist, and it need not
   be: `akept` has no clause over a block not in Sc, and the walk's stores into it are admitted by `in_tmp_block`
   (YCbq.v:341: a block allocated since the journal's start) once malloc has returned. The plain write set's
   (own, own + 320) is this block. checked_memcpy and memchr write nothing else outside their windows.
   The read set (`aleaf_alloc_rd`): the input bytes [c0, c0 + c1), read through the cursor (the c1 bytes left; the
   code reads at most adv of them). checked_memcpy reads them AFTER malloc: without `akb` an input in free heap could
   be the fresh block. At the callers the input is the input block (LLVMFuzzerTestOneInput's data, `In (d, N)
   (ablocks B ly S)` at the journal's start, pcap PcapEntry.v:45; live at the call): akb's block clause. The cursor
   and *own are in Wr, not Rd; texts is a global, not read through an argument; the words under o are read by the
   unwinder before malloc allocates and decide only the trace.

   PostA (the plain Post over the A views): for the cursor values c0, c1 at the call, an answer s <> 0 that is a C
   string t of fewer than 320 bytes at m', *own's new value own (with its range), the cursor advanced by
   0 <= adv <= c1 and still writable; own = 0 (the table arm): the block list is the call's up to order and the
   answer with its NUL is `text_of_ro` (it does not move: AMEND-slot item 8); own <> 0 (the copy arm): own = s,
   4096 <= own, and the block list is the call's with (own, k) appended, 1 <= k <= 320, |t| + 1 <= k (the string and
   its NUL fit in the fresh block; malloc rule's `ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)]`). It does not
   say which arm the selector chose (the plain weakest form).

   What does NOT carry over from the plain text:
   - `segs = rsegs`, `ro_agree segs mem` (Pre) and `ro_agree segs mem'` (Post): apre's `arodata_okP`; at the return
     the journal gives it (YC20.v arodata_ok_journalP).
   - `call_pre_k` / `call_post_k`, the plain `@YK11.mkst fx` start state: the journal premise and apost (under the
     same fx, `cfg_at segs pc regs memc mdc`).
   - `alloc_ceiling <= a0`, `alloc_ceiling <= a1` (call_post_k artefacts): replaced by the journal. The plain's two
     reasons: a cursor in a live block made call_post_k's block clause false (akept excepts Wr in every clause); a
     cursor or *own in a free slot could be handed out by malloc (apre's `ajw` puts every Wr byte in the window, a
     live FP or temporary block, an own side frame, or G: live memory malloc does not hand out, and malloc's kept
     clause keeps it).
   - `st_init_done A = true` (a call_post_k artefact: plain malloc's auxv side condition): no image-A counterpart.
     The A malloc contract (YG0d.v amalloc_realizes, YC5d.v amalloc04_rule) has no lazy-init premise; AR is the
     allocator's invariant at every journal state.
   - `res_ok_slots A b`, `room_slots b 320` (Pre), `res_ok_slots A' ...` (Post): replaced by aleaf_alloc_rd's
     `blocks_bytes Sc + 320 <= LIVE_MAX`, `mo_ok MT Sc (mo_malloc MT 320)`, apre's event room, and the Post's
     `mo_le MT Sc S2 MO`, LedPost and the block lists.
   - `c1 <> 0 -> exists q k, In (q, k) (user_blocks A) /\ ...` (the input in a live block): replaced by the read
     set's `akb`.
   - `a0 <> 0`, `a1 <> 0`: no instruction tests them; the views, the write set's `ajw` and the shadow facts locate
     the slots.
   - `G_img_c B [(A_TEXTS, 88)]`: replaced by the table premise (see above).
   - `fresh_block B own k` and the plain `blocks L' A' = b1 ++ (own, k) :: b2 /\ blocks L A = b1 ++ b2`:
     `4096 <= own /\ bl2 = bl ++ [(own, k)]`; the rest of fresh_block (below alloc_ceiling, no image byte) is AR's
     block placement at the return state. `L' = L /\ A' = A` (own = 0): `Permutation bl2 bl` with mo_le and LedPost.
   - `A_RO_LO <= s /\ s + |t| + 1 <= A_RO_END` (the plain image's first PT_LOAD): replaced by `exists i, 0 <= i <
     TEXTS_N /\ au64_at m (LA_TEXTS + 8 * i) s` (the answer IS the texts entry +0x198 `ld s3, 0(a0)` loaded) and
     `text_of_ro s (|t| + 1)` (the string and its NUL are read-only image bytes no journal state changes: what a
     caller needs to apply arodata_okP across later calls). The plain AMEND-slot item 13 (`s + |t| + 8 <=
     A_RO_END`, strlen's slack in the read-only segment) does NOT carry over as `text_of_ro` to |t| + 8: on image A
     the bytes after a literal's NUL are its global redzone, which is in `as_owned_static` (the slot comparer,
     by computation over AF0m.v Tfib_owned_static: .str.1 at 0x20fc0, bytes 0x20fc1..0x20fc7; "reac-pw:served" at
     0x21100, byte 0x2110f), so that premise was false at the slot's calls 0x82e24 / 0x82e34 / 0x837d8. A wrapper's
     tail visibility over the rest of the NUL's granule needs only presence, which the image's mapping gives
     (arodata_okP / AR; a ROM byte reads through seg_rom); no value of those bytes is needed. The range alone is too
     weak on image A (comparer, 2026-10-30): .rodata also
     holds the poisoned redzones of the instrumented string literals (e.g. "reac-pw:served\0" at 0x21100, zeros to
     0x2111f, ASan global descriptor at 0xa6520: beg 0x21100, size 0xf, size_with_redzone 0x20), so s = 0x21110
     with t = [] met the range; then op_write's model_write (0x83858, `range_addressable` of the alias) and
     op_decide's reac_served_decide (0x82e44, the alias[0] check at 0x89530) could not meet their premises. Naming
     the entry lets the caller take the string's shadow and slack from the image (each entry's object and redzone).
   - the plain AMEND-slot items 11 and 12: the allocating arm keeps every old user
     block and gives `st_init_done A' = true`: here `bl2 = bl ++ [(own, k)]` keeps every block of the call, and the
     allocator's state is the journal's AR (no `st_init_done` on image A); the footprint is the block's real size
     `k`: here the fresh block is in no write set (akept keeps no byte of it), and PostA names its size k.
   Nothing of the plain text is false of image A.
   Released proofs (rule 24): none of text_of (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038): no hit on the
   four refs; the index's hits are the delivered package name collisions and the unit owner's unreleased plain / UBSan twins).

   SATISFIABILITY WITNESS (op_decide, LLVMFuzzerTestOneInput 0x82e24, the first text_of call of the first op).
   The run: target_run calls LLVMFuzzerTestOneInput (ra 0x820c8) with data d = the input block (target_run's
   malloc at 0x8205c; typed in as d = 0x602000000010, a 16-aligned block) and size N; the first input byte is 0x04
   (op 4 = op_decide, fuzz_link.c:783), read at +0x5a0..+0x5bc (cursor (d + 1, N - 1)).
   Registers at 0x87dc0: ra = 0x82e28; sp = s1 = LLVMFuzzerTestOneInput's realigned sp; with its entry sp
   sp0 = 0x7ffffffef000: s1 = 0x7ffffffeee60 (sp0 - 0x1a0, already 32-aligned), so sp mod 16 = 0;
   a0 = p = s1 + 0x118 = 0x7ffffffeef78 (p mod 8 = 0); a1 = o = s1 + 0x130 = 0x7ffffffeef90; s0 = sp0 (0x82810
   `addi s0, sp, 0x1a0`); gp = as_gp B, tp = as_tp B. K window [sp - 16448, sp) = [0x7ffffffeae20, 0x7ffffffeee60):
   p, o, [o - 16, o) lie above sp, inside LLVMFuzzerTestOneInput's frame and its window (STK >= 416 + 16 + 16448).
   Bit 7 clear: N = 3, input bytes 04 05 00. At the call [p] = d + 1, [p + 8] = 2 (c0 = d + 1, c1 = 2); [o] = any
   word (stack residue; typed in 0); [o - 8] = [s1 + 0x128] = residue (0); [o - 16] = [p + 8] = 2 <= o.
     Result: selector 0x05, texts[5] = 0x21180 "reac-pw:served2" (15 bytes); cursor (d + 2, 1) (adv = 1); *own = 0;
     bl2 = bl.
   Bit 7 set: N = 7, input bytes 04 80 03 00 61 62 63. At the call c0 = d + 1, c1 = 6, the rest as above.
     Result: selector 0x80; lo = 0x03, hi = 0x00, v = 3, want = 3, rem = 3, n = 3, q = d + 4; memchr finds no NUL
     (k = 3); malloc(4) gives b (typed in 0x602000000030); t = "abc"; cursor (d + 7, 0) (adv = 6); *own = b = s;
     bl2 = bl ++ [(b, 4)]. Malloc's trace: [o - 8] = 0 < 4096, so ch = [] and the trace is [0x5436c; 0x87ff0]
     (fixed and the wild prefix); with a residue w >= 4096 it is [0x5436c; 0x87ff0; w], and [o - 16] = 0 <= o ends
     the chain.
   Shadow: p, p + 8, o are register spill slots of LLVMFuzzerTestOneInput's real frame, whose shadow is 0 (AR's
   zshadow_ok of the stack range, YG0n.v:188-191); the input block's one granule has shadow byte N (3 or 7), so
   [d + 1, d + N) is addressable (x mod 8 < N), and its shadow hull is visible (AR_shadow_law); the 88 bytes of
   texts are 11 whole granules of an instrumented global (st_size 128: 40 bytes of redzone after it), shadow 0
   [INFERENCE: the instance's as_zero_shadow lists the object ranges of the globals; the redzone is the runtime's
   const cells].
   Separation and ranges: d.. lies in the heap below alloc_ceiling, p, o on the real stack above it: the input apart
   from p, o and the K window, c0 + c1 = d + N <= o; amem_range (d + 1) (N - 1) (app memory); 0 <= c0, c1 < 2 ^ 64.
   The table: read from the pin (sha256 059dae63e07c, PT_LOAD data, pyelftools, 2026-10-30): the 11 words at
   LA_TEXTS = 0xa17c0 (.data.rel.ro [0xa1380, 0xa1970), inside PT_GNU_RELRO [0xa1340, 0xa3000)) are 0x20fc0 "",
   0x21100 "reac-pw:served", 0x21120 "reac-pw:minted", 0x21140 "host-alias", 0x21160 "reac-pw:", 0x21180
   "reac-pw:served2", 0x211a0 "reac-pw", 0x211c0 "vlan", 0x211e0 "veth", 0x21200 "vlanx", 0x21220 "vla" (lengths 0,
   14, 14, 10, 8, 15, 7, 4, 4, 5, 3, all < 320; each NUL-terminated), all in .rodata [0x102e0, 0x22fac) of the
   read-only PT_LOAD [0x10000, 0x3026c) (flags R): in_roP; not a runtime static or errno (those are in the
   writable segments; an obligation of the instance's as_owned_static / as_errno); apart from p and o (stack).
   Journal: LLVMFuzzerTestOneInput's (link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f) section 1: G = LA_G,
   XO = 0, OUT = [], own = [(4, p4)]); ajw of [p, p + 16) and [o, o + 8) by the window clause; akb of [d + 1, d + N) by
   the block clause (the input block is a block of Sc and none of its bytes is in Wr); st_nev S + k + 1 <= EV_MAX
   (k = the two callocs so far); blocks_bytes Sc = N + 8856 + 516 (input, model, marks blocks), far below
   LIVE_MAX - 320; MT the slot's meter with room for mo_malloc MT 320; LedPre: the depot has no wild trace yet in this
   target call's first op (at most 96 per call, LinkWildRoom.v; u_wmax Tfib_univ = 4064), 0 + 1 <= 4064; CTX = the
   contexts ACej.v lists for LLVMFuzzerTestOneInput's callees ([0x82e28] and [0x82e28; 0x820c8]: s0 = sp0,
   [sp0 - 8] = 0x820c8, the chain ends at target_run, ACejTfib.v); text_of_traces by ACejUniv.v Tfib_univ_wild with
   pc_malloc_ra0 = 0x5436c. The closed lemma of the register and memory part of `text_of_apre` is `hb_text_of_apre_sat`
   of lib/A/Prog/help_witness.v; three conjuncts are its hypotheses, because they are facts of the instance and not
   of memory: `text_of_traces`, the table's `text_of_ro` (string and NUL), and
   `HERR : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd` (the errno separations above; it is api_env's first
   conjunct, Reusable/YCbq.v:807, and `tl_errno` of A/ACeg.v:49 discharges it at the instance, where
   as_errno B = TFIB_ERRNO = 0x631b6c = TFIB_TP - 164).
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG00 YG01 YG0f YG0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0d YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition TEXT_OF_A : Z := 0x87dc0.
Lemma TEXT_OF_A_is_entry : TEXT_OF_A = LA_text_of. Proof. reflexivity. Qed.

(* the return address of the malloc call (+0x22c jal wrapper_malloc) *)
Definition TEXT_OF_MALLOC_RA : Z := 0x87ff0.
Lemma TEXT_OF_MALLOC_RA_off : TEXT_OF_MALLOC_RA = TEXT_OF_A + 0x230. Proof. reflexivity. Qed.

(* the stack bound on image A: the 64-byte frame and malloc's window *)
Definition TEXT_OF_AFRAME : Z := 64.
Definition TEXT_OF_AK : Z := TEXT_OF_AFRAME + ASTACK.
Lemma TEXT_OF_AK_val : TEXT_OF_AK = 16448. Proof. reflexivity. Qed.

(* the largest request: k + 1 with k <= n <= v mod 320 <= 319 *)
Definition TEXT_OF_LIVE : Z := 320.

(* the write set: the cursor's two words and the *own slot (the fresh block is no block of the call's state) *)
Definition text_of_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(aarg regs 0, aarg regs 0 + 16); (aarg regs 1, aarg regs 1 + 8)].

(* the read set: the c1 input bytes left at the cursor's data pointer c0 (both words bounded as in the Pre, so they
   are the words the code's `ld` reads) *)
Definition text_of_ard (segs : list Segment) (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  exists c0 c1, au64_at segs m (aarg regs 0) c0 /\ au64_at segs m (aarg regs 0 + 8) c1
    /\ 0 <= c0 < 2 ^ 64 /\ 0 <= c1 < 2 ^ 64 /\ rd_ivl c0 (c0 + c1) a.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable CTX : list (list Z).

(* n bytes at q that no journal state changes: read-only image (in_roP) outside the runtime's statics and errno,
   exactly the bytes arodata_okP (YC20.v:46) fixes *)
Definition text_of_ro (q n : Z) : Prop :=
  forall j, 0 <= j < n ->
    in_roP segs rlo rhi (q + j) /\ ~ Exists (in_zr (q + j)) (as_owned_static B)
    /\ ~ (as_errno B <= q + j < as_errno B + 4).

(* the malloc trace at 0x87fec starts with a wild prefix of the universe: [pc0; 0x87ff0] and any tail are inU *)
Definition text_of_traces : Prop :=
  In [pc_malloc_ra0 (as_code B); TEXT_OF_MALLOC_RA] (u_wild (as_universe B)).

Definition text_of_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists c0 c1 inp,
    (* the cursor *)
    au64_at segs m (aarg regs 0) c0 /\ au64_at segs m (aarg regs 0 + 8) c1
    /\ 0 <= c0 < 2 ^ 64 /\ 0 <= c1 < 2 ^ 64
    /\ abuf segs m (aarg regs 0) 16 /\ aarg regs 0 mod 8 = 0
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 0) 16 /\ amem_range (aarg regs 0) 16
    /\ apart_frame regs TEXT_OF_AK (aarg regs 0) 16
    (* *own *)
    /\ abuf segs m (aarg regs 1) 8
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 1) 8 /\ amem_range (aarg regs 1) 8
    /\ shadow_hull_vis (ard segs m) (aarg regs 1) 8
    /\ apart_frame regs TEXT_OF_AK (aarg regs 1 - 16) 24
    /\ apart (aarg regs 1) 8 (aarg regs 0) 16
    (* errno: the malloc rule's kept clause excepts [as_errno B, as_errno B + 4) (ascratch, YG0d.v:216-217), so the
       cursor, which the Post gives back across the malloc at +0x22c, must not be errno bytes *)
    /\ apart (as_errno B) 4 (aarg regs 0) 16
    (* the input bytes left *)
    /\ abytes segs m c0 inp /\ Z.of_nat (length inp) = c1
    /\ range_addressable (ard segs m) SHADOW_OFF c0 c1
    /\ (0 < c1 ->
          shadow_hull_vis (ard segs m) c0 c1 /\ amem_range c0 c1
          /\ apart_frame regs TEXT_OF_AK c0 c1
          /\ apart c0 c1 (aarg regs 0) 16 /\ apart c0 c1 (aarg regs 1) 8
          /\ c0 + c1 <= aarg regs 1)
    (* the words malloc's unwinder reads under *own *)
    /\ (forall i, 0 <= i < 16 -> ard segs m (aarg regs 1 - 16 + i) <> None)
    /\ (forall w, au64_at segs m (aarg regs 1 - 16) w -> 0 <= w < 2 ^ 64 -> w <= aarg regs 1)
    (* the table and its strings *)
    /\ range_addressable (ard segs m) SHADOW_OFF LA_TEXTS (8 * TEXTS_N)
    /\ apart (aarg regs 0) 16 LA_TEXTS (8 * TEXTS_N) /\ apart (aarg regs 1) 8 LA_TEXTS (8 * TEXTS_N)
    /\ (forall i, 0 <= i < TEXTS_N -> exists q s,
          au64_at segs m (LA_TEXTS + 8 * i) q /\ 0 < q < 2 ^ 64
          /\ acstr_at segs m q s /\ Z.of_nat (length s) < 320
          /\ text_of_ro q (Z.of_nat (length s) + 1)
          /\ apart (aarg regs 0) 16 q (Z.of_nat (length s) + 1)
          /\ apart (aarg regs 1) 8 q (Z.of_nat (length s) + 1))
    (* the malloc trace *)
    /\ text_of_traces.

(* room for the one wild trace the malloc may add (+1 per call); after the call at most one more *)
Definition text_of_ledpre (Sc : astate) : Prop :=
  (length (wild_part (as_universe B) (st_depot Sc)) + 1 <= u_wmax (as_universe B))%nat.
Definition text_of_ledpost (Sc S2 : astate) : Prop :=
  (length (wild_part (as_universe B) (st_depot S2)) <= length (wild_part (as_universe B) (st_depot Sc)) + 1)%nat.

Definition text_of_apostA (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) (bl bl2 : list (Z * Z)) : Prop :=
  forall c0 c1, au64_at segs m (aarg regs 0) c0 -> au64_at segs m (aarg regs 0 + 8) c1 ->
    0 <= c0 < 2 ^ 64 -> 0 <= c1 < 2 ^ 64 ->
    exists own s t,
      getr regs' 10 = w64 s /\ s <> 0
      /\ acstr_at segs m' s t /\ Z.of_nat (length t) < 320
      /\ au64_at segs m' (aarg regs 1) own /\ 0 <= own < 2 ^ 64
      /\ (exists adv, 0 <= adv <= c1
            /\ au64_at segs m' (aarg regs 0) (c0 + adv) /\ au64_at segs m' (aarg regs 0 + 8) (c1 - adv)
            /\ abuf segs m' (aarg regs 0) 16)
      /\ (own = 0 -> Permutation bl2 bl
            /\ (exists i, 0 <= i < TEXTS_N /\ au64_at segs m (LA_TEXTS + 8 * i) s)
            /\ text_of_ro s (Z.of_nat (length t) + 1))
      /\ (own <> 0 -> own = s /\ 4096 <= own
            /\ exists k, 1 <= k <= TEXT_OF_LIVE /\ Z.of_nat (length t) + 1 <= k /\ bl2 = bl ++ [(own, k)]).

Definition text_of_acontract : Prop :=
  aleaf_alloc_rd SK segs rlo rhi B MT TEXT_OF_A TEXT_OF_AK 1 TEXT_OF_LIVE (mo_malloc MT TEXT_OF_LIVE) [] CTX
    text_of_ledpre text_of_ledpost text_of_apre (text_of_ard segs) text_of_awr text_of_apostA.

End c.
