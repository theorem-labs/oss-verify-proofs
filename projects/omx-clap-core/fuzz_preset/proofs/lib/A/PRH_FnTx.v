(* This file carries the kit's text of the re-hiding move for the four tx texts
   (`PRIMED-SHAPES.md (sha256 9e4880d18317; internal record)` sec. 2.12-2.15 and sec. 5.1): each concludes SRr' segs RZ_cf with its post
   fpostWbmR .. (wle' segs RZ_cf), and prhtx_refused_at is world-free.
   The unit owner's ruling C2 (2026-10-31 04:19Z) struck the scratch notice that stood here, by a
   comment-only edit that keeps the header at 5 lines, so every line after it keeps its number. *)
(* fuzz_preset, program part (the kit's tx texts): the ASan contract TEXTS of the harness's text renderer, tx_put,
   tx_string, tx_line and tx_value (the merged #102 fuzz_preset.c :379-475; the base @0b89c6c1bd :353-441), in cgif's
   per-function form (cgif_file
   lib/YC21.v:33-66; the fm port's FMH_Fn.v:101-180), as PRH_FnAlloc.v: fpre (YCbqG's afn_pre_x + the read-only view), the
   argument registers, the realloc trace in the image's universe, the allocator room on the entry state,
   the alloc.c ledger (PRH_Base.v prh_ledger), and SRr' segs RZ_cf to the return address through the kit's budgeted
   CALLER-WINDOW post fpostWbmR at wle' segs RZ_cf (no abort arm: on the fixed harness a refused grow sets failed
   and returns). Every conclusion is `srealizes` through SRr' segs RZ_cf. IMAGE-PARAMETRIC (pa_segs, pa_sigma AS_<fn>,
   PrhImg) and ALLOCATOR-PARAMETRIC (ARx); no image constant and no numeral address is named here. Statements only.
   The functional content is preset's released plain contracts lib/Prog/tx_put_c.v, tx_string_c.v, tx_line_c.v and
   tx_value_c.v (with lib/Prog/TxRet.v tx_start / tx_ret), restated; no plain lemma is cited. The pure models are
   reused by Require (never Import): TxModel.tx_cap1 / tx_capf / plen / strp / tv_calls, WriterSpec.wstr,
   WriterValue.wind / wvpieces, PjTree.jv / depth; the tree and string predicates are the kit's lib/A/PRH_Reader.v
   (pj_nodeR / pj_cstrR / pj_footR, the plain PjStruct.v predicates restated over the kit's readers), over
   mrestrict (w_H W) mem with prh_lin Lam as lblk. No plain lib/Prog memory-predicate file is Required.
   The rebuilt images' bodies were re-read (neutral listings of all four functions on f0d2e8d4 and on 3b5e1a09, and
   round_trip_text on both). The B BODIES ARE NOT A'S (UBSan adds traps, each an `unimp`), but one TEXT serves both
   images, because the premises exclude every B trap (the walks are per image; a generic half can be shared):
   - tx_put (B 2 unimp): t misaligned (t mod 8 = 0); t->b + t->n NULL or wrapping, before the copy and before the NUL
     store (b <> 0 and b + cap <= alloc_ceiling from prhtx_inv when cap0 > 0; cap0 = 0 forces a grow, and a grow
     that returns has a live block);
   - tx_string (B 1 unimp): s NULL, and s++ wrapping at s = -1 (4096 <= s, (s + k + 7) / 8 * 8 <= alloc_ceiling:
     prhtx_bvis);
   - tx_value (B 1 unimp): v NULL or misaligned (pj_hdrR's p mod 8 = 0; v in a harness block, a read-only global or a
     fake frame, each at or above 4096 by ARx's block / frame laws or kept_at's margin); depth + 1 signed overflow
     (d + depth tv <= 2 ^ 31 - 1, depth tv >= 1 for an array or object); kids / keys NULL, misaligned or wrapping and
     the 56 * i index overflow (prhtx_bvis on D's blocks, n <= cap);
   - tx_line: no trap (A and B bodies equal, 28 lines).
   STRUCT TEXT LAYOUT (#102, re-worded 2026-10-29 from the B' walker's T4 measurement): b at t + 0, n at t + 8, cap at
   t + 16 and the NEW `int failed` at t + 24; sizeof 32, of which the bodies touch 28 bytes (prhtx_rec, prhtx_fp,
   prhtx_place). ONLY tx_put's BODY reads those offsets. tx_string (t in s4), tx_line (t in s1) and tx_value (t in s0) never load or store
   through t on either image (neutral listings f0d2e8d4 / 3b5e1a09: no access through that register); they only pass
   it as a0 to their calls. So the three callers' bodies need no re-walk for the record; every tx TEXT is re-pinned to
   the new layout.
   THE TEXT BUFFER. struct text (merged :379-384, fields b, n, cap, failed) is prhtx_rec. tx_put grows it by a DIRECT
   call of the realloc wrapper through noted (A 0x84dac, B 0x85298 on the fixed pins), not fuzz_realloc, so the buffer
   is a RAW allocator block (b, cap) of ablocks B ly S: no head, not in Lam, not in Hp (prhtx_inv, the plain tx_inv,
   tx_put_c.v:31-35, with the shadow facts the inline checks and __asan_memcpy read). Lam, Hp and the five statics are
   unchanged by every text here, and each post states the ledger again (the statics are PST: a journal neither writes
   nor keeps them unless a text says so).
   WHERE t LIES (measured; the H2/H5 walk found the earlier fake-frame-only text false). The only creator of a struct text is
   round_trip_text (rendered, merged :477-492, inlined), and its record is on its REAL stack. ON THE FIXED PINS
   (the kit owner's census): t = s1 + 0x18 with s1 the `andi sp, sp, -32` sp, 32 bytes zeroed by __asan_memset (A
   0x84aa0), failed read at s1 + 0x30 (A 0x84af0); the fake-frame spill moved from s1 + 8 to s1 + 0x10. (On the old
   pins t was s1 + 16.) So the record lies in the CALLER WINDOW [sp, sp + dw) of every tx_* entry (a nested call adds
   the frames between). Hence every text states its post in the kit's caller-window form fpostWbmR at dw (fwin's
   premises), with the record's 28 bytes (t, t + 28) IN FP (prhtx_fp), and the old buffer's block in FP;
   prhtx_place is the real-stack case only, `spZ regs + 16 <= t /\ t + 28 <= spZ regs + dw`: the call site that fixes
   the shape is round_trip_text's rendered(), the only maker of a
   struct text in either image (check_round_trip only calls round_trip_text), so no caller passes a fake-frame record
   and that case was dropped (the walk-kit lead's ruling, on the S10 walk's request: it cost every tx walk a second proof path).
   With plain fpost the journal keeps the record's bytes and the text is false.
   THE REALLOC TRACE. tx_put sets s0 := a0 = t before the call (A 0x84940, B 0x84e68). With t on the real stack above
   tx_put's sp, chain_pre's bad_next is false and the unwinder walks the frame chain FROM t: it reads the caller's
   words at t - 8, t - 16 and on up the stack (round_trip_text's s1 + 8 holds its fake-frame pointer), so the trace is
   cf_pc_realloc_ra0 :: pi_ret_tx_realloc :: the chain's return addresses, NOT constant. The two short traces
   (frame0_ok false: the empty chain) are the closure's (prh_univ_closure: [prh_pc0 RT_realloc] and the pc0-filtered
   site trace prh_trace (prh_pc0 RT_realloc) pi_ret_tx_realloc []); prhtx_trace states the rest sp-free: for a real-stack t, the trace of
   every chain fpchain reads from t through any reader that agrees with the entry view on [t - 16, ly_top ly) outside
   the record (fpchain reads only that region: fps increase from t, below; the fixed tx_put writes no record byte
   before the call, so the exclusion is now conservative
   ly_top - 16), and every byte of that region present (the S10 walk's tx_put part: chain_pre needs a chain fpchain can READ, so
   each word it loads must be there; ARx and fwin give presence only below sp + dw). The region lies above every tx_*
   sp (spZ regs + 16 <= t) and outside every FP but the record (whose bytes prhtx_rec shows present), so a caller
   re-derives prhtx_trace at each nested tx_put from its own (the journals keep the region; the admission at the
   nested call's state is the room COUNT's, below). unwind_of_chain reads only
   the tuples' return addresses, so the first tuple's sp and s0 positions are immaterial.
   allocator traces: prh_univ_closure (PRH_Base.v) in all four texts (parameter CTX0); dropped prhtx_trace's two
   short-trace conjuncts (implied by the closure's entry and literal-site clauses); kept prhtx_trace's real-stack
   clause (C-TXTRACE: tx_put's s0 = t points INTO the real stack, a shape the closure does not model, PRH_Base.v
   prh_reach's note), now the state-free `inU (as_universe B)` form (prhtx_trace's note, :203-209); no other
   allocator site is reached (tx_string's frame_alloc_0 takes no trace).
   room: room_live_cf (PRH_Base.v, owned by the allocator-model owner), room_cf at none; margins removed. (The kit owner's ruling (B): room
   is an INVARIANT re-derived from the state at each call.) All four take room_live_cf S on entry and give
   room_live_cf S' in every post. NO primary room_cf, not even at
   tx_put's raw realloc (the kit owner's ruling (i), on the Tx part's measured composition defect: tx_string / tx_line /
   tx_value could not supply it at their 2nd..kth tx_put state). room_cf's only consumer is a8's
   malloc_cf_success_of_room (YGcfPath.v:544, it excludes the NULL); the realloc rule takes none. The class-full NULL
   is excluded ONCE, globally, by the driver (the driver-contract owner's LLVMFuzzerTestOneInput slot: P8's preset_room -> room_at ->
   no_null_preset); in these texts a refusal lands in the REFUSED outcome (prhtx_out). The live room is
   RELATIVE to the buffer, `blocks_bytes S - cap0 + LIVE_tx <= LIVE_MAX` in all four texts (the S10 walk's tx_value part: the
   absolute `blocks_bytes S + LIVE_tx` does not survive a callee that grew the buffer); every post gives
   blocks_bytes S' - cap1 <= blocks_bytes S - cap0, so it composes, and it gives tx_put's realloc its lmax (it grows
   only when cap0 < len0 + n + 1 <= 2 ^ 28, so blocks_bytes S + 2 * (len0 + n + 1) <= LIVE_MAX - 2 ^ 30 + 3 * 2 ^ 28).
   The request bound `2 * need < cf_malloc_max` is the realloc P form's nmax.
   THE REFUSED OUTCOME REPLACES THE ABORT ARM (#102). On the base harness a NULL from tx_put's realloc reached
   abort() and every text ended `fpostW .. \/ fabortW F_tx_put ..`. The fixed tx_put (merged :386-406) sets failed
   and g_own_ran_out (noted) and RETURNS, returns at once when failed is already set, and writes cap only after a
   successful realloc. So no text here has an abort disjunct: each post is ONE fpostWbmR whose body names the outcome
   (prhtx_out: DONE, FAILED AT ENTRY, REFUSED), with g_own_ran_out's value (the ledger's own field; a PST cell, so
   stated, not kept by the journal) and, on REFUSED, prhtx_refused_at (world-free, below). g_ran_out is NOT set (the
   raw wrapper does not touch alloc.c's statics): the ledger's other cells are unchanged on every outcome. The
   callers' bodies are instruction-equal to the base's (the internal file INSN-COMPARE-a3b65bd4.md:40); only their texts change, with
   tx_put's.
   THE REFUSED ARM IS DEAD AT A CONSUMER WINDOW (#102, the K1-batch walk-kit lead's order 2026-10-29, the mechanism of the kit owner's
   ~19:3xZ ruling for the entry-keyed check texts): each text takes `f0 = 0 -> PRH_Base.prh_cons_from rp_sm rp_x
   rp_os rp_i (length (prhtx_evs ..))` at entry and states `f0 = 0 -> f1 = 0` (DEAD-TXPUT / -TXSTRING / -TXLINE /
   -TXVALUE) in its post. The REFUSED arm stays stated (its prhtx_refused_at carries no granted path, so a caller
   cannot refute it from the post; the walk refutes it at tx_put's raw realloc, PRH_Refute.prh_refute_tx_put).
   R1 (a preserved caller buffer lies in a live block, or in a frame disjoint from every byte the callee writes):
   tx_put's source is ALWAYS prhtx_kept (a live harness block, a read-only registered global, or a fake frame of S
   disjoint from the record): changed 1 (ttx_put_specX). The tree of tx_value and the string of tx_string already met
   it. R2 (AddrHashMap meta region): no interceptor reached here reads it (__asan_memcpy, the strlen wrapper,
   frame_alloc_0): changed 0.
   RUNTIME SHAPES the walks will need (none new): __asan_memcpy (b + n, s, n) with s as prhtx_kept; the strlen wrapper
   on a number's text (cstr_ok: the string from pj_cstrR, its ceiling `p + len + 1` from prhtx_bvis's granule bound,
   its range from the blocks law as PRH_Base.v's cstr_ok note says; the length bound from the need bound);
   frame_alloc_0 (tx_string's 64-byte frame, class 0) under `count_cid 0 (frames S) < fs_frames 0`
   (astack_malloc_realizes' premise, YG0d.v:300); the record's real-stack shadow (the head of zero_shadow_ranges,
   YG0n.v:188-189, alx_zshadow_byte).
   IMAGE FACTS of the walks (asyms facts of each image; no kit name gives these addresses and no numeral address is
   allowed here, so they are not premises of the texts; the image instance states them):
   - TX-HEX: tx_string's static `hex` table (A 0x212c0): its 16 DIGITS, the only bytes tx_string indexes (hex[c >> 4],
     hex[c & 15], :382-383), satisfy kept_at's read-only case AT LENGTH 16 (in_zs B at 16, the 64-byte image margins,
     read-only, not runtime-owned, not errno). NEVER at 17: the NUL's granule has shadow 01 and lies in no
     as_zero_shadow range (the kit owner's measurement, the walk-kit lead's ruling).
   - TX-LIT: every literal source tx_string, tx_line and tx_value pass to tx_put (the quote, the backslash, the newline,
     the two spaces, the brackets and braces, the comma, the colon, the space, null / false / true: .rodata .str.N
     formed by auipc) satisfies src_rd and kept_img (PRH_Base.v route (a): read-only image bytes whose granules are
     zero-shadow or carry a const-shadow cell) at the LENGTH PASSED (n, without the NUL), so it meets tx_put's
     `src_rd W mem s src` and `prhtx_kept Lam ly S s n` through kept_at's kept_img case. NOT through kept_at's in_zs
     case: each is a short registered global whose (last) granule has a PARTIAL, constant non-zero shadow (2 for the
     two-byte quote, 5 for null), outside every as_zero_shadow range - the D2 class the kit owner named for
     "modifiedAt" and the stamp; before the kit folded kept_img into kept_at, prhtx_kept was unsatisfiable at every
     literal call site.
   THE MODEL-RUN POSITION (the kit owner's ruling, 2026-10-29): every text below that makes allocator calls in its
   subtree takes P8's premises at a position of the model run, PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i
   rp_H0 rp_hist S (lib/Spec/PresetRoomPos.v, the one home; the driver-contract owner's PresetCfnA.v re-exports it), and every post
   gives it back at an ADVANCED position: tx_put's at Datatypes.S rp_i after an unfailed grow, else at rp_i; its callers'
   at (rp_i + j)%nat. The advance is LOAD-BEARING (the round-trip stack walker's call_entry_succ pattern): without it a callee
   could claim an earlier position and consecutive calls would not compose. Do not drop it. The live-set bounds
   at each inner allocator call follow from it by the driver-contract owner's counts_of_room_pos_rl / counts_of_room_pos_ok.
   (Binder names are rp_* because several texts already bind x and i.)
   *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require TxModel WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun PresetReqAt.
(* the re-hiding move's conclusion SRr' and relation wle' (YA0nH), preset's zone
   (YGcfRehidePost.RZ_cf), and exh_mem_cf for the world-free refusal (YG00cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YG00cf.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the live room (heads: none, the buffer is a raw block), relative to the buffer's own bytes: every request is
   at most 2 * need <= 2 ^ 29 (tx_put_c.v:72 and :88, TxRet.v:30, need <= 2 ^ 28), and the old buffer (at most
   2 ^ 28 when it grows) is live while its successor is requested ---- *)
Definition LIVE_tx : Z := 2 ^ 30.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the realloc call's trace for a real-stack record (C-TXTRACE; the short traces are prh_univ_closure's): the
   trace of every frame chain the unwinder can read from s0 = t, through any reader that agrees with the entry view
   on [t - 16, ly_top ly) outside the record's 28 bytes, and that region present (so such a chain exists).
   IN THE STATE-FREE FORM `inU (as_universe B) ..` (YG01.v:145; why: the note below), NOT arealloc_realizes_cf's
   premise `admits (as_universe B) .. S` (YGcfRealloc.v:98). The old `In _ (as_universe B)` meant, through the
   coercion u_fix, the FIXED list, which holds at this site only the 2-word trace (ACej.v:253) and the slack
   continuations of prh_univ_closure's clause 5 over the callers' contexts (ACej.v:254-268), while the run's trace
   goes on with the fake-frame chain's words: so all four tx texts were VACUOUS on both images. This gap PREDATES the
   P'' batch (it is C-TXTRACE); the universes now carry the site's wild prefix (A' [0x53c74; 0x84db0] ACej.v:273, B'
   [0x53d60; 0x8529c] YCej.v:414), so the trace is inU, and admits adds the ROOM: a caller supplies it from the wild
   prefix plus the room COUNT (|wild_part| < u_wmax, or the trace already in the depot), so the four tx texts' rows
   stay CONDITIONAL ON THE COUNT THREAD (owned by the S1 owner, not proved). *)
(* STATE-FREE (the slice walker's measurement, 2026-10-30; it OVERTURNS the kit owner's 00:20Z pre-ruling that a guard on the
   call happening would do). THE OLD `admits (as_universe B) .. S` was STATE-KEYED to a state whose admission NO
   CALLEE POST PRESERVES, so a guard leaves the same hole on a FITTING put: a concrete countermodel, stated only here
   (no lemma in this tree proves it), REFUTES the old premise (d = 1, len0 = cap0 = 0; put 1 grows with k1 = 1, put 2
   fits, K = 1; U = MkUniv [] [[7]] 1, tr = [7;1], depot S0 = [], S1 = [[7;2]], WS1 = [[7;2]]: every caller fact holds
   and `admits (as_universe B) tr S1` is still FALSE - tr is not in the depot, not fixed, and |wild_part| = 1 is not
   < u_wmax = 1). CORROBORATION FROM THE OTHER SIDE: compiling Tx102Glue on 62dc819e58ff needed exactly one added
   fact in tx_state_fold, `forall tr, admits (as_universe B) tr S -> admits (as_universe B) tr S'`, which no callee
   post gives. WHY `inU` AND NOT A GUARD OR A POST CONJUNCT: admission now comes from the callee's OWN GUARDED ROOM
   premise (a growing put has k = 1 and a fresh slot, so YCbqGwild.wild_room_admits gives admits at its realloc; a
   fitting put makes no realloc and needs none; applied at TxPut102A_Grow.v:1452 and TxPut102B_GROW.v:1040); inU is
   STATE-FREE, so the existing memory-only trace keep carries it across calls; and unlike the old
   `In _ (as_universe B)` it is NOT VACUOUS, because it includes the wild prefix. Adding prhtx_trace ly' S' W' mem' t
   to every tx post would instead need tx_put's walk to show that a GROW STORES tr, which no realloc post exposes. *)
Definition prhtx_trace (ly : alayout) (W : world segs) (mem : word -> option byte) (t : Z) : Prop :=
  (YM05.alloc_ceiling <= t ->
   (forall a, t - 16 <= a < ly_top ly -> aview segs (w_H W) mem a <> None) /\
   forall (rd : reader) (ch : list (Z * Z * Z)),
     (forall a, t - 16 <= a < ly_top ly -> ~ (t <= a < t + 28) -> rd a = aview segs (w_H W) mem a) ->
     fpchain (rdword rd) t (ly_top ly) ch ->
     inU (as_universe B) (unwind_of_chain cf_pc_realloc_ra0 ((t, pi_ret_tx_realloc, t) :: ch))).

(* struct text at t (merged fuzz_preset.c:379-384): b, n, cap (8 bytes each, t, t + 8, t + 16) and, new in #102,
   `int failed` at t + 24 (4 bytes, read by `lw` after a 4-byte shadow check, written `sw 1`; A 0x84d50 / 0x84e88,
   B 0x8523c / 0x853b0). sizeof 32: t + 28 .. t + 32 is padding no body touches. failed is 0 or 1: rendered()
   starts it at 0 (new:480) and tx_put only ever stores 1. *)
Definition prhtx_rec (W : world segs) (mem : word -> option byte) (t b len cap f : Z) : Prop :=
  0 <= b < 2 ^ 64 /\ 0 <= len < 2 ^ 64 /\ 0 <= cap < 2 ^ 64 /\ (f = 0 \/ f = 1) /\
  val_mem segs (rdW W mem) t 8 b /\ val_mem segs (rdW W mem) (t + 8) 8 len /\
  val_mem segs (rdW W mem) (t + 16) 8 cap /\ val_mem segs (rdW W mem) (t + 24) 4 f.

(* where the record lies: 8-aligned (B's UBSan alignment trap); in the caller window [sp + 16, sp + dw) of the entry
   sp (round_trip_text's real stack, the only place a struct text is made); its 28 accessed bytes writable and
   addressable (tx_put's inline checks of t, t + 8, t + 16 and the 4-byte t + 24) *)
Definition prhtx_place (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte)
  (dw t : Z) : Prop :=
  t mod 8 = 0 /\ spZ regs + 16 <= t /\ t + 28 <= spZ regs + dw /\
  (forall a, t <= a < t + 28 -> writable_at segs (rdW W mem) a) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF t 28.

(* the buffer and its text (tx_put_c.v:31-35 tx_inv): empty, or a live raw block of cap bytes holding txt and a NUL,
   writable and addressable, whose base is no harness block's (tx_string_c.v:33, tx_value_c.v:41) *)
Definition prhtx_inv (Lam : list (Z * Z)) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
  (b len cap : Z) (txt : list Z) : Prop :=
  Z.of_nat (length txt) = len /\
  ((cap = 0 /\ b = 0 /\ len = 0) \/
   (0 < cap /\ len < cap /\ In (b, cap) (ablocks B ly S) /\ bytes_at W mem b (txt ++ [0]) /\
    (* SRC-CEIL: the buffer's own bytes are below the ceiling (the kit owner's rule, 2026-10-29: a `+ 8`
       stays only where it covers an access, and the dead-arm sweep found none here - tx_put only writes the buffer, the
       memcpy destination [b + len0, b + len0 + n) and the NUL store, both inside [b, b + cap), and a later strcmp
       reads [b, b + len]). The old `b + cap + 8` was true of the block by F21b / alx_blocks_ceil8, which this clause
       no longer needs. *)
    4096 <= b /\ b + cap <= YM05.alloc_ceiling /\ amem_range b cap /\
    (forall a, b <= a < b + cap -> writable_at segs (rdW W mem) a) /\
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF b cap /\ shadow_hull_vis (aview segs (w_H W) mem) b cap /\
    (forall a k, In (a, k) Lam -> a - cf_head <> b))).

(* bytes a later runtime read finds again, with their shadow facts and values, after an allocator or program call:
   kept_at (a live harness block; a registered read-only global by in_zs; or an image string by route (a), kept_img,
   its granules' const-shadow cells kept by AR_laws_x's alx_const_cells, journal d15706bda36) or inside one fake frame
   of S (the journal keeps a frame's bytes and shadow outside FP) *)
Definition prhtx_kept (Lam : list (Z * Z)) (ly : alayout) (S : astate) (p n : Z) : Prop :=
  kept_at B Lam p n \/
  (exists cid pos, In (cid, pos) (frames S) /\ forall a, p <= a < p + n -> in_zr a (frame_rng ly (cid, pos))).

(* where a tree NODE lies (tx_value's v): inside a live harness block or one fake frame of S, never an image byte, so
   it is disjoint from tx_value's read-only jump table by ARx's client-image law (the S10 walk's tx_value part: a node is a harness
   block or a frame, never a .rodata global; writable_at alone does not exclude an image address) *)
Definition prhtx_home (Lam : list (Z * Z)) (ly : alayout) (S : astate) (p n : Z) : Prop :=
  (exists b m, In (b, m) Lam /\ b <= p /\ p + n <= b + m) \/
  (exists cid pos, In (cid, pos) (frames S) /\ forall a, p <= a < p + n -> in_zr a (frame_rng ly (cid, pos))).

(* a block of a tree's footprint (a string, a kids or keys array): what the inline checked loads, the strlen wrapper
   (cstr_ok) and __asan_memcpy (src_rd) read of it *)
(* THE CEILING IS A GRANULE, NOT A BLOCK (the kit owner's ruling, 2026-10-29, on a sub-walk of the rtt102 walk, goal
   TX-BVIS): this said `x + k + 8 <= YM05.alloc_ceiling` and `amem_range x (k + 8)`, ONE GRANULE MORE than the
   image supplies. ARx's alx_blocks bound (in_app) admits p + req_size n = alloc_ceiling and the high-app band is
   not vacuous, so a block MAY end at the ceiling and the old form was FALSE of it. The producer, ck_tree_ok's
   prhWriter_tree_vis = tree_vis_cf (YGcfTreeVis.v:42-48), gives (a + k + 7) / 8 * 8 <= alloc_ceiling, and now
   discharges this conjunct for conjunct with no bridge. This is not a weakening to make a proof go through: the
   statement it replaces is one the binary falsifies. *)
Definition prhtx_bvis (W : world segs) (mem : word -> option byte) (x k : Z) : Prop :=
  4096 <= x /\ x mod 8 = 0 /\ 0 <= k /\ (x + k + 7) / 8 * 8 <= YM05.alloc_ceiling /\
  amem_range x ((k + 7) / 8 * 8) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x k /\
  (0 < k -> shadow_hull_vis (aview segs (w_H W) mem) x k) /\
  (forall a, x <= a < x + (k + 7) / 8 * 8 -> aview segs (w_H W) mem a <> None).

(* the blocks after a run of tx_put calls (tx_put_c.v:87-90, TxRet.v:38-39): unchanged, or the old buffer (none when
   cap0 = 0) replaced by the new one *)
Definition prhtx_grow (ly : alayout) (S : astate) (ly' : alayout) (S' : astate) (b0 cap0 b1 cap1 : Z) : Prop :=
  (b1 = b0 /\ cap1 = cap0 /\ ablocks B ly' S' = ablocks B ly S) \/
  (cap0 < cap1 /\ exists bl1 bl2,
     (cap0 = 0 /\ ablocks B ly S = bl1 ++ bl2 \/ 0 < cap0 /\ ablocks B ly S = bl1 ++ (b0, cap0) :: bl2) /\
     Permutation (ablocks B ly' S') ((b1, cap1) :: bl1 ++ bl2)).

(* the footprint of a run of tx_put calls on the record at t with buffer (b0, cap0) (tx_put_c.v:37-38 tx_writes): the
   record's 28 accessed bytes and the old buffer's block. g_own_ran_out, which a refused grow sets, is a PST cell
   (prh_pst), not FP: the posts state its value (the ledger's own field). *)
Definition prhtx_fp (t b0 cap0 : Z) : list (Z * Z) :=
  (t, t + 28) :: (if cap0 =? 0 then [] else ablocks_fp [(b0, cap0)]).

(* what a run of tx_put calls leaves on return (TxRet.v:32-44 tx_relx): the record holds the buffer b1, length len1,
   capacity cap1 and failed f1, the buffer holds txt1, the record still lies where it lay (the entry regs: sp is
   back), Hp unchanged, the blocks as prhtx_grow, and the live bytes grow by at most the buffer's growth *)
Definition prhtx_post (Lam : list (Z * Z)) (regs : bvmap 5 word) (dw : Z) (ly : alayout) (S : astate) (Hp : list Z)
  (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte)
  (t b0 cap0 b1 len1 cap1 f1 : Z) (txt1 : list Z) : Prop :=
  prhtx_rec W' mem' t b1 len1 cap1 f1 /\ prhtx_inv Lam ly' S' W' mem' b1 len1 cap1 txt1 /\
  prhtx_place ly' S' W' regs mem' dw t /\ Hp' = Hp /\ prhtx_grow ly S ly' S' b0 cap0 b1 cap1 /\
  blocks_bytes S' <= blocks_bytes S + cap1 - cap0.

(* THE REFUSAL (#102): a realloc of the wrapper was REFUSED, with the allocator state S1 right after the refused call.
   It is the evidence of a REFUSED arm, which RETURNS NORMALLY: the harness no longer aborts there (new:394-399).
   WORLD-FREE (`PRIMED-SHAPES.md (sha256 9e4880d18317; internal record)` sec. 5.1): the four conjuncts of the allocator-model owner's refusal
   leaf malloc_cf_null_post (YG0dcf.v) that a refusal changes, with NO world. Under the re-hiding move the refused arm's
   leaf is the PRIMED one, whose post re-hides a dead set, so the old world-bound witness (malloc_cf_null_post at a
   fixed W: wle W Wc and an unexcepted view frame) needs that set empty; this form does not read the set at all. It
   is WEAKER than the old one (malloc_cf_null_post gives each conjunct), and the allocator-model owner's realloc_cf_refused_state
   gives it from the primed row (lib/Reusable/YGcfRealloc.v:136). *)
Definition prhtx_refused_at (S1 : astate) : Prop :=
  exists S0 rq, blocks S1 = blocks S0 /\ st_chunks S1 = st_chunks S0 /\
    from_primary rq = true /\ YG00cf.exh_mem_cf S1 (chunk_class rq) = true.

(* THE THREE OUTCOMES of a run of tx_put calls that would append `add` (the B' walker's arm draft, the internal file REWALK-102-PLAN.md T4,
   for tx_put; the same three for its callers, whose bodies did not change):
   - DONE: failed was 0 and stays 0; all of add appended; capacity capf; g_own_ran_out kept.
   - FAILED AT ENTRY: failed was 1, so every tx_put returns at once (A0, new:390-391): nothing appended, the buffer
     and capacity unchanged, g_own_ran_out kept.
   - REFUSED: failed was 0 and one realloc was refused: failed = 1, g_own_ran_out = 1 (noted, new:85-88), a PREFIX
     pre of add appended (the pieces before the refused call; every later call is A0), and prhtx_refused_at at some
     allocator state.
   pre is what was appended in each case. *)
Definition prhtx_out (f0 f1 own own' b0 cap0 b1 cap1 capf : Z) (add pre : list Z) : Prop :=
  (f0 = 0 /\ f1 = 0 /\ own' = own /\ pre = add /\ cap1 = capf) \/
  (f0 <> 0 /\ f1 = f0 /\ own' = own /\ pre = [] /\ b1 = b0 /\ cap1 = cap0) \/
  (f0 = 0 /\ f1 = 1 /\ own' = 1 /\ (exists rest, add = pre ++ rest) /\ exists S1, prhtx_refused_at S1).

(* ---- THE RUN EVENTS THE tx FAMILY MAKES (the kit owner's ruling on the B' walker's GROW-OK measurement, 2026-10-29).
   A growing tx_put reallocates the buffer to 2 * need through the RAW wrapper, which the run records as
   HMal (2 * need) when the buffer was empty (realloc (NULL, ..), PresetReqAt.v:88) and as HRe cap (2 * need)
   otherwise. A text that MAKES run events states the events it makes as an ENTRY PREMISE guarded by f0 = 0
   (TX-RUNAT-F0; before THE ADVANCE IS UNCONDITIONAL, a position-conjunct HYPOTHESIS): tx_put's is the run's event at
   rp_i when it grows (the image-A tx_put walk's wording, verbatim), its callers' that the run's next events are those of their
   puts. The conclusion is the position advanced by exactly those events (the history existential: the kit names blocks by
   address, the steps by allocator pointer), NOT `exists rp_i' rp_hist', rp_i <= rp_i' /\ ..`, which is false at the
   end of a run (the recursive-reader author's witness: rp_i = length hruns with |d| = 3). ---- *)
Definition prhtx_ev (cap need : Z) : PresetReqAt.hev :=
  if cap =? 0 then PresetReqAt.HMal (2 * need) else PresetReqAt.HRe cap (2 * need).
(* the run events of tx_put calls of sizes ks from length len and capacity cap: one per grow *)
Fixpoint prhtx_evs (len cap : Z) (ks : list Z) : list PresetReqAt.hev :=
  match ks with
  | [] => []
  | k :: r => (if len + k + 1 <=? cap then [] else [prhtx_ev cap (len + k + 1)]) ++
              prhtx_evs (len + k) (TxModel.tx_cap1 len cap k) r
  end.
(* prhtx_evs over an APPEND (the S10 walk's s10_prhtx_evs_app, taken into the kit verbatim: one home). A caller that
   splits its piece list splits its event list by this, then its position by PRH_Base.prh_run_at_app_iff. *)
Lemma prhtx_evs_app : forall (ks kc : list Z) (len cap : Z),
  prhtx_evs len cap (ks ++ kc) =
  prhtx_evs len cap ks ++ prhtx_evs (len + TxModel.zsum ks) (TxModel.tx_capf len cap ks) kc.
Proof.
  induction ks as [|a ks IH]; intros kc len cap; cbn [app prhtx_evs TxModel.zsum TxModel.tx_capf].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH, app_assoc.
    replace (len + a + TxModel.zsum ks) with (len + (a + TxModel.zsum ks)) by lia. reflexivity.
Qed.
(* THE GROW COUNT of one buffer (the internal file WILD-COUNT.md section 3.2, the tx k's: one realloc, so at most one wild trace, per
   grow; the internal file TRACE-CARRIER.md section 9.1). The doubling is the model's, not a premise: a grow happens only when
   need = len + k + 1 > cap and sets cap := 2 * need, so it at least doubles cap + 2; the last grow's need is at most
   len + zsum ks + 1 for pieces >= 0. The pieces must be >= 0 (every caller's ks is a TxModel.plen, so they are):
   with negative pieces the count has no bound at a fixed total (ks = [1; -1; 4; -4; 10; -10; ..], total 0, one
   grow per pair). From an empty buffer with total + 1 <= 2 ^ 28 (the texts' need bound at len0 = 0) the count
   is at most 28, and 28 is met: ks = [0; 2; 4; ..; 2 ^ 27] (total 2 ^ 28 - 2, needs 2 ^ j - 1, j = 1 .. 28). *)
Lemma prhtx_evs_double : forall (ks : list Z) (len cap : Z),
  Forall (fun k => 0 <= k) ks -> 0 <= cap ->
  2 ^ Z.of_nat (length (prhtx_evs len cap ks)) * (cap + 2) <= Z.max (cap + 2) (2 * (len + TxModel.zsum ks) + 4).
Proof.
  induction ks as [|k r IH]; intros len cap Hks Hc.
  - cbn [prhtx_evs length TxModel.zsum Z.of_nat]. rewrite Z.pow_0_r. lia.
  - apply Forall_cons_iff in Hks as [Hk Hr].
    assert (Hz : 0 <= TxModel.zsum r)
      by (clear - Hr; induction Hr as [|x l Hx _ IHl]; cbn [TxModel.zsum] in *; lia).
    cbn [prhtx_evs TxModel.zsum]. unfold TxModel.tx_cap1.
    destruct (len + k + 1 <=? cap) eqn:E; cbn [app length].
    + specialize (IH (len + k) cap Hr Hc).
      replace (len + (k + TxModel.zsum r)) with (len + k + TxModel.zsum r) by lia. exact IH.
    + apply Z.leb_gt in E.
      specialize (IH (len + k) (2 * (len + k + 1)) Hr ltac:(lia)).
      rewrite Z.max_r in IH by lia.
      revert IH. generalize (length (prhtx_evs (len + k) (2 * (len + k + 1)) r)) as g. intros g IH.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      assert (Hg : 0 < 2 ^ Z.of_nat g) by (apply Z.pow_pos_nonneg; lia).
      assert (Hm : 2 ^ Z.of_nat g * (2 * cap + 4) <= 2 ^ Z.of_nat g * (2 * (len + k + 1) + 2))
        by (apply Z.mul_le_mono_nonneg_l; lia).
      lia.
Qed.
Lemma prhtx_evs_le_28 : forall ks : list Z,
  Forall (fun k => 0 <= k) ks -> TxModel.zsum ks + 1 <= 2 ^ 28 -> (length (prhtx_evs 0 0 ks) <= 28)%nat.
Proof.
  intros ks Hks Hsum.
  pose proof (prhtx_evs_double ks 0 0 Hks ltac:(lia)) as Hd.
  assert (Hz : 0 <= TxModel.zsum ks)
    by (clear - Hks; induction Hks as [|x l Hx _ IHl]; cbn [TxModel.zsum] in *; lia).
  rewrite Z.max_r in Hd by lia.
  destruct (Nat.le_gt_cases (length (prhtx_evs 0 0 ks)) 28) as [Hle | Hgt]; [exact Hle | exfalso].
  assert (Hp : 2 ^ 29 <= 2 ^ Z.of_nat (length (prhtx_evs 0 0 ks))) by (apply Z.pow_le_mono_r; lia).
  assert (E28 : 2 ^ 28 = 268435456) by reflexivity.
  assert (E29 : 2 ^ 29 = 536870912) by reflexivity.
  lia.
Qed.
(* the k of a tx text that starts from an empty buffer, in the internal file WILD-COUNT.md's form *)
Lemma prhtx_evs_le_30 : forall ks : list Z,
  Forall (fun k => 0 <= k) ks -> TxModel.zsum ks + 1 <= 2 ^ 28 -> (length (prhtx_evs 0 0 ks) <= 30)%nat.
Proof. intros ks Hks Hsum. pose proof (prhtx_evs_le_28 ks Hks Hsum) as H28. lia. Qed.

(* tx_put (merged fuzz_preset.c:386-406; plain tx_put_c.v:55-90 is the base's). If failed is set, return at once.
   If n + 1 more bytes do not fit, b := noted (realloc (b, 2 * (len0 + n + 1))) through the realloc wrapper; on NULL,
   failed := 1 (and noted's g_own_ran_out := 1) and RETURN - b, n and cap unchanged; else t->b := b and only THEN
   t->cap := 2 * (len0 + n + 1) (the base wrote cap BEFORE the call). Then __asan_memcpy (b + len0, s, n),
   n := len0 + n, b[n] := 0. The source is prhtx_kept (R1) and overlaps neither the record nor the old buffer
   (tx_put_c.v:68-71; __asan_memcpy reports an overlap). Write set: the record's 28 bytes (in the caller window), the
   old buffer (written or freed), g_own_ran_out (PST); the new buffer is fresh. The four arms (A0 FAILED, A1 FIT,
   A2 GROW-OK, A3 GROW-NULL) are the B' walker's (the internal file REWALK-102-PLAN.md T4); the REFUSED outcome here is A3 alone, so it is
   stated exactly: nothing appended, the buffer unchanged, errno 12 (the wrapper), prhtx_refused_at S'. *)
Definition ttx_put_specX (CTX0 : list (list Z)) : Prop :=
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk),
  forall ly S Hp W regs mem md ch (dw t s n b0 len0 cap0 f0 own : Z) (txt src : list Z) Lam peak cnt fail ran most,
  fpre B ARx STK_tx_put ly S Hp W regs mem md ch -> prh_univ_closure B CTX0 ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* THE RUN HAS AT MOST 4 CALLS: A17's prefix bound needs it for the grow's hull at the position
     (lib/A/PresetDrvHeadroomA.v and lib/AU/PresetDrvHeadroomB.v: drv_cf_headroom_at_call_A / _B at HRe, drv_cf_headroom_at_malloc_A / _B at HMal) *)
  (length rp_os <= 4)%nat ->
  (* THE WILD BUDGET (the room count of P'', the S1 owner's internal file WILD-COUNT.md; PRH_Base's BUDGETED TWINS): this subtree
     stores a wild trace only at the GROW's raw realloc (prhtx_trace's site), one per grow, so k is the EXACT
     number of grows - the length of this call's own event list, which composes by prhtx_evs_app. Constant bound
     PRH_Base.prh_wk F_tx_put = 1.
     GUARDED BY f0 = 0, as the run premise below is (TX-RUNAT-F0; PRH_Base.wbudget_if carries the witness): a call
     entered failed returns at once (:390-391), makes no grow and stores nothing, and its UNCHANGED cap is what
     makes an unguarded premise unprovable at the next put. *)
  (f0 = 0 -> YCbqGwild.wild_room (as_universe B) [] (length (prhtx_evs len0 cap0 [n])) (st_depot S)) ->
  (* THE CALL'S ALLOCATIONS ARE CONSUMER ALLOCATIONS OF THE RUN (the ENTRY-KEYED texts' named entry premise,
     the kit owner's ruling 2026-10-29, extended to the tx family), over this call's own events (prhtx_evs: the
     grow's raw realloc when it grows, else none), GUARDED by f0 = 0 as the event premise below is (TX-RUNAT-F0).
     The raw realloc is no harness allocation (no chosen failure), so its only NULL is a REAL refusal, which this
     excludes at the realloc (PRH_Refute.prh_refute_tx_put: P8, a NULL of malloc_cf is primary-only, the engine's
     granted paths); the post states DEAD-TXPUT. Supplied by the caller from its own window
     (PRH_Base.prh_cons_from_sub). *)
  (f0 = 0 -> PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhtx_evs len0 cap0 [n]))) ->
  getr regs 10 = w64 t -> getr regs 11 = w64 s -> getr regs 12 = w64 n ->
  fwin ly W regs mem dw -> prhtx_place ly S W regs mem dw t -> prhtx_trace ly W mem t ->
  prhtx_rec W mem t b0 len0 cap0 f0 -> prhtx_inv Lam ly S W mem b0 len0 cap0 txt ->
  src_rd W mem s src -> Z.of_nat (length src) = n -> prhtx_kept Lam ly S s n ->
  (forall a, s <= a < s + n -> ~ (t <= a < t + 28) /\ ~ (b0 <= a < b0 + cap0)) ->
  len0 + n + 1 <= 2 ^ 28 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (* the GROW event, the image-A tx_put walk's wording verbatim, as an entry PREMISE (the kit owner's ruling; see the post), GUARDED by
     f0 = 0: a call entered failed returns at once (:390-391) and makes no event (TX-RUNAT-F0, a sub-walk of the rtt102 walk:
     after a refused put the run's next event is not this call's, so an unguarded premise is false there) *)
  (f0 = 0 -> cap0 < len0 + n + 1 -> nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i =
     Some (if cap0 =? 0 then PresetReqAt.HMal (2 * (len0 + n + 1)) else PresetReqAt.HRe cap0 (2 * (len0 + n + 1)))) ->
  blocks_bytes S - cap0 + LIVE_tx <= LIVE_MAX -> 2 * (len0 + n + 1) < cf_malloc_max ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.12): the grow's raw realloc frees the old
     buffer, so the run ends at wle' segs RZ_cf: SRr' and the post's journal at wle' *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_tx_put) regs mem md)
    (fpostWbmR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) (wbudget_if f0 [] (length (prhtx_evs len0 cap0 [n])))
      STK_tx_put dw (prhtx_fp t b0 cap0) regs ly S Hp W mem md
      (fun ly' S' Hp' W' regs' mem' md' =>
       exists b1 cap1 f1 own' (pre : list Z),
       prhtx_post Lam regs dw ly S Hp ly' S' Hp' W' mem' t b0 cap0 b1 (len0 + Z.of_nat (length pre)) cap1 f1
         (txt ++ pre) /\
       ((f0 = 0 /\ f1 = 0 /\ own' = own /\ pre = src /\ cap1 = TxModel.tx_cap1 len0 cap0 n) \/
        (f0 <> 0 /\ f1 = f0 /\ own' = own /\ pre = [] /\ b1 = b0 /\ cap1 = cap0) \/
        (f0 = 0 /\ cap0 < len0 + n + 1 /\ f1 = 1 /\ own' = 1 /\ pre = [] /\ b1 = b0 /\ cap1 = cap0 /\
         prhtx_refused_at S' /\ rd32 (aview segs (w_H W') mem') (as_errno B) 12)) /\
       (* DEAD-TXPUT (the REFUSED arm DEAD under prh_cons_from, above; three supports: PRH_Base's ENTRY-KEYED
          note): entered with failed = 0 it returns with
          failed = 0; the third arm follows a REAL refusal of the raw realloc and this path has no chosen failure *)
       (f0 = 0 -> f1 = 0) /\
       bytes_at W' mem' s src /\
       room_live_cf S' /\
       (f0 = 0 -> f1 = 0 -> cap0 < len0 + n + 1 ->
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (Datatypes.S rp_i) rp_H0 hist' S') /\
       (~ (f0 = 0 /\ f1 = 0 /\ cap0 < len0 + n + 1) -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S') /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own')).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== ttx_put_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. txpP_Q IS the text's post (txpP_Q_check fails to build if
   the two ever differ); txpP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition txpP_A1 (n len0 cap0 f0 own : Z) (src : list Z) (cap1 f1 own' : Z) (pre : list Z) : Prop :=
  f0 = 0 /\ f1 = 0 /\ own' = own /\ pre = src /\ cap1 = TxModel.tx_cap1 len0 cap0 n.

Definition txpP_A2 (b0 cap0 f0 own b1 cap1 f1 own' : Z) (pre : list Z) : Prop :=
  f0 <> 0 /\ f1 = f0 /\ own' = own /\ pre = [] /\ b1 = b0 /\ cap1 = cap0.

Definition txpP_A3 (n b0 len0 cap0 f0 : Z) (S' : astate) (W' : world segs) (mem' : word -> option byte) (b1 cap1 f1
    own' : Z) (pre : list Z) : Prop :=
  f0 = 0 /\ cap0 < len0 + n + 1 /\ f1 = 1 /\ own' = 1 /\ pre = [] /\ b1 = b0 /\ cap1 = cap0 /\ prhtx_refused_at S' /\
      rd32 (aview segs (w_H W') mem') (as_errno B) 12.

Definition txpP_Q (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i
    : nat) (rp_H0 : list Z) (rp_hist : list chunk) (ly : alayout) (S : astate) (Hp : list Z) (regs : bvmap 5 word) (dw
    t s n b0 len0 cap0 f0 own : Z) (txt src : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most : Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  exists b1 cap1 f1 own' (pre : list Z), prhtx_post Lam regs dw ly S Hp ly' S' Hp' W' mem' t b0 cap0 b1 (len0 +
      Z.of_nat (length pre)) cap1 f1 (txt ++ pre) /\ (txpP_A1 n len0 cap0 f0 own src cap1 f1 own' pre \/ txpP_A2 b0
      cap0 f0 own b1 cap1 f1 own' pre \/ txpP_A3 n b0 len0 cap0 f0 S' W' mem' b1 cap1 f1 own' pre) /\ (f0 = 0 -> f1 =
      0) /\ bytes_at W' mem' s src /\ room_live_cf S' /\ (f0 = 0 -> f1 = 0 -> cap0 < len0 + n + 1 -> exists hist',
      PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (Datatypes.S rp_i) rp_H0 hist' S') /\ (~ (f0 = 0 /\ f1 = 0 /\ cap0
      < len0 + n + 1) -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S') /\ prh_ledger B ly' S'
      Hp' W' mem' Lam peak cnt fail ran most own'.

Lemma txpP_Q_check : forall (CTX0 : list (list Z)), ttx_put_specX CTX0 -> ttx_put_specX CTX0.
Proof.
  intros CTX0 H. unfold ttx_put_specX in *.
  intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch dw t s n b0 len0 cap0 f0 own txt src Lam peak cnt
      fail ran most HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20 HP21
      HP22 HP23.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (txpP_Q rp_sm rp_x rp_os rp_i
      rp_H0 rp_hist ly S Hp regs dw t s n b0 len0 cap0 f0 own txt src Lam peak cnt fail ran most) end.
  exact (H rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch dw t s n b0 len0 cap0 f0 own txt src Lam peak
      cnt fail ran most HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20
      HP21 HP22 HP23).
Qed.

Record txpP_R (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i :
    nat) (rp_H0 : list Z) (rp_hist : list chunk) (ly : alayout) (S : astate) (Hp : list Z) (regs : bvmap 5 word) (dw t
    s n b0 len0 cap0 f0 own : Z) (txt src : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most : Z) (ly' : alayout)
    (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (b1 cap1 f1 own'
    : Z) (pre : list Z) : Prop := {
  txpP_post : prhtx_post Lam regs dw ly S Hp ly' S' Hp' W' mem' t b0 cap0 b1 (len0 + Z.of_nat (length pre)) cap1 f1
      (txt ++ pre);
  txpP_arm : (txpP_A1 n len0 cap0 f0 own src cap1 f1 own' pre \/ txpP_A2 b0 cap0 f0 own b1 cap1 f1 own' pre \/ txpP_A3
      n b0 len0 cap0 f0 S' W' mem' b1 cap1 f1 own' pre);
  txpP_f1 : (f0 = 0 -> f1 = 0);
  txpP_bytes : bytes_at W' mem' s src;
  txpP_room : room_live_cf S';
  txpP_pos_grow : (f0 = 0 -> f1 = 0 -> cap0 < len0 + n + 1 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x
      rp_os (Datatypes.S rp_i) rp_H0 hist' S');
  txpP_pos_keep : (~ (f0 = 0 /\ f1 = 0 /\ cap0 < len0 + n + 1) -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i
      rp_H0 rp_hist S');
  txpP_ledger : prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own' }.

Lemma txpP_R_of : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option
    nat)) (rp_i : nat) (rp_H0 : list Z) (rp_hist : list chunk) (ly : alayout) (S : astate) (Hp : list Z) (regs : bvmap
    5 word) (dw t s n b0 len0 cap0 f0 own : Z) (txt src : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most : Z)
    (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte)
    (md' : Model),
  txpP_Q rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp regs dw t s n b0 len0 cap0 f0 own txt src Lam peak cnt fail ran
      most ly' S' Hp' W' regs' mem' md' ->
  exists b1 cap1 f1 own' pre, txpP_R rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp regs dw t s n b0 len0 cap0 f0 own txt
      src Lam peak cnt fail ran most ly' S' Hp' W' regs' mem' b1 cap1 f1 own' pre.
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp regs dw t s n b0 len0 cap0 f0 own txt src Lam peak cnt fail ran
      most ly' S' Hp' W' regs' mem' md' H. destruct H as (b1 & cap1 & f1 & own' & pre & H0 & H1 & H2 & H3 & H4 & H5 &
      H6 & H7).
  exists b1, cap1, f1, own', pre.
  exact {| txpP_post := H0; txpP_arm := H1; txpP_f1 := H2; txpP_bytes := H3; txpP_room := H4; txpP_pos_grow := H5;
      txpP_pos_keep := H6; txpP_ledger := H7 |}.
Qed.

Lemma txpP_Q_of_R : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option
    nat)) (rp_i : nat) (rp_H0 : list Z) (rp_hist : list chunk) (ly : alayout) (S : astate) (Hp : list Z) (regs : bvmap
    5 word) (dw t s n b0 len0 cap0 f0 own : Z) (txt src : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most : Z)
    (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte)
    (md' : Model) (b1 cap1 f1 own' : Z) (pre : list Z),
  txpP_R rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp regs dw t s n b0 len0 cap0 f0 own txt src Lam peak cnt fail ran
      most ly' S' Hp' W' regs' mem' b1 cap1 f1 own' pre ->
  txpP_Q rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp regs dw t s n b0 len0 cap0 f0 own txt src Lam peak cnt fail ran
      most ly' S' Hp' W' regs' mem' md'.
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp regs dw t s n b0 len0 cap0 f0 own txt src Lam peak cnt fail ran
      most ly' S' Hp' W' regs' mem' md' b1 cap1 f1 own' pre HR.
  exists b1, cap1, f1, own', pre.
  exact (conj (txpP_post HR) (conj (txpP_arm HR) (conj (txpP_f1 HR) (conj (txpP_bytes HR) (conj (txpP_room HR) (conj
      (txpP_pos_grow HR) (conj (txpP_pos_keep HR) (txpP_ledger HR)))))))).
Qed.

Record txpP_R1 (n len0 cap0 f0 own : Z) (src : list Z) (cap1 f1 own' : Z) (pre : list Z) : Prop := {
  txpP1_f0 : f0 = 0;
  txpP1_f1 : f1 = 0;
  txpP1_own : own' = own;
  txpP1_pre : pre = src;
  txpP1_cap1 : cap1 = TxModel.tx_cap1 len0 cap0 n }.

Lemma txpP_R1_of : forall (n len0 cap0 f0 own : Z) (src : list Z) (cap1 f1 own' : Z) (pre : list Z),
  txpP_A1 n len0 cap0 f0 own src cap1 f1 own' pre ->
  txpP_R1 n len0 cap0 f0 own src cap1 f1 own' pre.
Proof.
  intros n len0 cap0 f0 own src cap1 f1 own' pre H. destruct H as (H0 & H1 & H2 & H3 & H4).
  exact {| txpP1_f0 := H0; txpP1_f1 := H1; txpP1_own := H2; txpP1_pre := H3; txpP1_cap1 := H4 |}.
Qed.

Lemma txpP_A1_of_R : forall (n len0 cap0 f0 own : Z) (src : list Z) (cap1 f1 own' : Z) (pre : list Z),
  txpP_R1 n len0 cap0 f0 own src cap1 f1 own' pre ->
  txpP_A1 n len0 cap0 f0 own src cap1 f1 own' pre.
Proof.
  intros n len0 cap0 f0 own src cap1 f1 own' pre HR.
  exact (conj (txpP1_f0 HR) (conj (txpP1_f1 HR) (conj (txpP1_own HR) (conj (txpP1_pre HR) (txpP1_cap1 HR))))).
Qed.

Record txpP_R2 (b0 cap0 f0 own b1 cap1 f1 own' : Z) (pre : list Z) : Prop := {
  txpP2_f0 : f0 <> 0;
  txpP2_f1 : f1 = f0;
  txpP2_own : own' = own;
  txpP2_pre : pre = [];
  txpP2_b1 : b1 = b0;
  txpP2_cap1 : cap1 = cap0 }.

Lemma txpP_R2_of : forall (b0 cap0 f0 own b1 cap1 f1 own' : Z) (pre : list Z),
  txpP_A2 b0 cap0 f0 own b1 cap1 f1 own' pre ->
  txpP_R2 b0 cap0 f0 own b1 cap1 f1 own' pre.
Proof.
  intros b0 cap0 f0 own b1 cap1 f1 own' pre H. destruct H as (H0 & H1 & H2 & H3 & H4 & H5).
  exact {| txpP2_f0 := H0; txpP2_f1 := H1; txpP2_own := H2; txpP2_pre := H3; txpP2_b1 := H4; txpP2_cap1 := H5 |}.
Qed.

Lemma txpP_A2_of_R : forall (b0 cap0 f0 own b1 cap1 f1 own' : Z) (pre : list Z),
  txpP_R2 b0 cap0 f0 own b1 cap1 f1 own' pre ->
  txpP_A2 b0 cap0 f0 own b1 cap1 f1 own' pre.
Proof.
  intros b0 cap0 f0 own b1 cap1 f1 own' pre HR.
  exact (conj (txpP2_f0 HR) (conj (txpP2_f1 HR) (conj (txpP2_own HR) (conj (txpP2_pre HR) (conj (txpP2_b1 HR)
      (txpP2_cap1 HR)))))).
Qed.

Record txpP_R3 (n b0 len0 cap0 f0 : Z) (S' : astate) (W' : world segs) (mem' : word -> option byte) (b1 cap1 f1 own' :
    Z) (pre : list Z) : Prop := {
  txpP3_f0 : f0 = 0;
  txpP3_need : cap0 < len0 + n + 1;
  txpP3_f1 : f1 = 1;
  txpP3_own : own' = 1;
  txpP3_pre : pre = [];
  txpP3_b1 : b1 = b0;
  txpP3_cap1 : cap1 = cap0;
  txpP3_refused : prhtx_refused_at S';
  txpP3_errno : rd32 (aview segs (w_H W') mem') (as_errno B) 12 }.

Lemma txpP_R3_of : forall (n b0 len0 cap0 f0 : Z) (S' : astate) (W' : world segs) (mem' : word -> option byte) (b1 cap1
    f1 own' : Z) (pre : list Z),
  txpP_A3 n b0 len0 cap0 f0 S' W' mem' b1 cap1 f1 own' pre ->
  txpP_R3 n b0 len0 cap0 f0 S' W' mem' b1 cap1 f1 own' pre.
Proof.
  intros n b0 len0 cap0 f0 S' W' mem' b1 cap1 f1 own' pre H. destruct H as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  exact {| txpP3_f0 := H0; txpP3_need := H1; txpP3_f1 := H2; txpP3_own := H3; txpP3_pre := H4; txpP3_b1 := H5;
      txpP3_cap1 := H6; txpP3_refused := H7; txpP3_errno := H8 |}.
Qed.

Lemma txpP_A3_of_R : forall (n b0 len0 cap0 f0 : Z) (S' : astate) (W' : world segs) (mem' : word -> option byte) (b1
    cap1 f1 own' : Z) (pre : list Z),
  txpP_R3 n b0 len0 cap0 f0 S' W' mem' b1 cap1 f1 own' pre ->
  txpP_A3 n b0 len0 cap0 f0 S' W' mem' b1 cap1 f1 own' pre.
Proof.
  intros n b0 len0 cap0 f0 S' W' mem' b1 cap1 f1 own' pre HR.
  exact (conj (txpP3_f0 HR) (conj (txpP3_need HR) (conj (txpP3_f1 HR) (conj (txpP3_own HR) (conj (txpP3_pre HR) (conj
      (txpP3_b1 HR) (conj (txpP3_cap1 HR) (conj (txpP3_refused HR) (txpP3_errno HR))))))))).
Qed.

Local Unset Implicit Arguments.

(* tx_string (merged :408-430, body instruction-equal to the base's :374-396): takes a 64-byte fake frame
   (frame_alloc_0, class 0; the frames-count premise makes it succeed, so esc[] lies in it) and releases it at the
   return; tx_put of the opening quote, then per byte of the string the pieces of TxModel.strp (a backslash and the
   byte for a quote or a backslash, the byte for c >= 0x20, esc[] of 2 or 6 bytes for c < 0x20), then the closing
   quote. The text it would append is WriterSpec.wstr bs (tx_string_c.v:27), the calls' sizes
   TxModel.plen (TxModel.strp bs); the three outcomes are prhtx_out's. The string is a harness string (pj_cstrR over
   prh_lin Lam, tx_string_c.v:32) and is kept. *)
Definition ttx_string_specX (CTX0 : list (list Z)) : Prop :=
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk),
  forall ly S Hp W regs mem md ch (dw t s k b0 len0 cap0 f0 own : Z) (bs txt : list Z) Lam peak cnt fail ran most,
  let add := WriterSpec.wstr bs in
  let ks := TxModel.plen (TxModel.strp bs) in
  fpre B ARx STK_tx_string ly S Hp W regs mem md ch -> prh_univ_closure B CTX0 ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* THE RUN HAS AT MOST 4 CALLS: its tx_put calls take it (ttx_put_specX) *)
  (length rp_os <= 4)%nat ->
  (* THE WILD BUDGET (as tx_put's): one wild trace per GROW of its puts, k the EXACT number of grows of this call's
     own event list, which composes by prhtx_evs_app. Constant bound PRH_Base.prh_wk F_tx_string = 30. *)
  (f0 = 0 -> YCbqGwild.wild_room (as_universe B) [] (length (prhtx_evs len0 cap0 ks)) (st_depot S)) ->
  (* THE CALL'S ALLOCATIONS ARE CONSUMER ALLOCATIONS OF THE RUN (the ENTRY-KEYED texts' named entry premise,
     the kit owner's ruling 2026-10-29, extended to the tx family), over this call's own events, GUARDED by
     f0 = 0 as its event premise is (TX-RUNAT-F0); every grow of its puts is then a consumer event, so the post
     states DEAD-TXSTRING. Supplied by the caller from its own window (PRH_Base.prh_cons_from_sub). *)
  (f0 = 0 -> PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhtx_evs len0 cap0 ks))) ->
  getr regs 10 = w64 t -> getr regs 11 = w64 s ->
  fwin ly W regs mem dw -> prhtx_place ly S W regs mem dw t -> prhtx_trace ly W mem t ->
  prhtx_rec W mem t b0 len0 cap0 f0 -> prhtx_inv Lam ly S W mem b0 len0 cap0 txt ->
  PRH_Reader.pj_cstrR segs (rdW W mem) (prh_lin Lam) s k bs -> prhtx_bvis W mem s k ->
  len0 + Z.of_nat (length add) + 1 <= 2 ^ 28 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (* the run's next events are those of this call's puts, when it is entered with failed = 0 (TX-RUNAT-F0: entered
     failed it makes no event; see tx_put); see the post's note *)
  (f0 = 0 -> prh_run_at rp_sm rp_x rp_os rp_i (prhtx_evs len0 cap0 ks)) ->
  blocks_bytes S - cap0 + LIVE_tx <= LIVE_MAX -> 2 * (len0 + Z.of_nat (length add) + 1) < cf_malloc_max ->
  count_cid 0 (frames S) < fs_frames 0 ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.13): its puts cross the grow's realloc *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_tx_string) regs mem md)
    (fpostWbmR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) (wbudget_if f0 [] (length (prhtx_evs len0 cap0 ks)))
      STK_tx_string dw (prhtx_fp t b0 cap0) regs ly S Hp W mem md
      (fun ly' S' Hp' W' regs' mem' md' =>
       exists b1 cap1 f1 own' (pre : list Z),
       prhtx_post Lam regs dw ly S Hp ly' S' Hp' W' mem' t b0 cap0 b1 (len0 + Z.of_nat (length pre)) cap1 f1
         (txt ++ pre) /\
       prhtx_out f0 f1 own own' b0 cap0 b1 cap1 (TxModel.tx_capf len0 cap0 ks) add pre /\
       (* DEAD-TXSTRING (prhtx_out's REFUSED arm DEAD under prh_cons_from; three supports: PRH_Base's ENTRY-KEYED
          note): entered with failed = 0 it
          returns with failed = 0 (a REAL refusal of a put's raw realloc is the only way to failed = 1) *)
       (f0 = 0 -> f1 = 0) /\
       PRH_Reader.pj_cstrR segs (rdW W' mem') (prh_lin Lam) s k bs /\ prhtx_bvis W' mem' s k /\
       room_live_cf S' /\
       (* THE ADVANCE IS UNCONDITIONAL (the kit owner's ruling, 2026-10-29, on the image-B tx walk's counterexample:
          tx_line with d = 1, len0 = 0, cap0 = 0 makes put("\n") then put("  "); if the run's event at rp_i is
          not HMal 4, put 1's post gave NO position, so put 2's unconditional iface_room_pos premise was
          unavailable and a two-call text could not be proved by composing its callee's text. The run_at
          hypothesis is now an entry PREMISE of this text, so every position through a walk is unconditional
          and each post's advance exact. ANTI-VACUITY: the premise's supplier is this text's caller -
          check_round_trip supplies round_trip_text's, LLVMFuzzerTestOneInput supplies the top; a supply
          lemma that cannot be proved is a finding about the model, not a licence to keep the premise. *)
       exists j hist', (j <= length (prhtx_evs len0 cap0 ks))%nat /\
          PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 hist' S' /\
          (f0 = 0 -> f1 = 0 -> j = length (prhtx_evs len0 cap0 ks)) /\ (f0 <> 0 -> j = 0%nat) /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own')).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== ttx_string_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. txsP_Q IS the text's post (txsP_Q_check fails to build if
   the two ever differ); txsP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition txsP_Q (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i
    : nat) (rp_H0 : list Z) (ly : alayout) (S : astate) (Hp : list Z) (regs : bvmap 5 word) (dw t s k b0 len0 cap0 f0
    own : Z) (bs txt : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most : Z) (add ks : list Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  exists b1 cap1 f1 own' (pre : list Z), prhtx_post Lam regs dw ly S Hp ly' S' Hp' W' mem' t b0 cap0 b1 (len0 +
      Z.of_nat (length pre)) cap1 f1 (txt ++ pre) /\ prhtx_out f0 f1 own own' b0 cap0 b1 cap1 (TxModel.tx_capf len0
      cap0 ks) add pre /\ (f0 = 0 -> f1 = 0) /\ PRH_Reader.pj_cstrR segs (rdW W' mem') (prh_lin Lam) s k bs /\
      prhtx_bvis W' mem' s k /\ room_live_cf S' /\ exists j hist', (j <= length (prhtx_evs len0 cap0 ks))%nat /\
      PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 hist' S' /\ (f0 = 0 -> f1 = 0 -> j = length
      (prhtx_evs len0 cap0 ks)) /\ (f0 <> 0 -> j = 0%nat) /\ prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most
      own'.

Lemma txsP_Q_check : forall (CTX0 : list (list Z)), ttx_string_specX CTX0 -> ttx_string_specX CTX0.
Proof.
  intros CTX0 H. unfold ttx_string_specX in *.
  cbv zeta in H |- *.
  intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch dw t s k b0 len0 cap0 f0 own bs txt Lam peak cnt
      fail ran most HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20
      HP21.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (txsP_Q rp_sm rp_x rp_os rp_i
      rp_H0 ly S Hp regs dw t s k b0 len0 cap0 f0 own bs txt Lam peak cnt fail ran most (WriterSpec.wstr bs)
      (TxModel.plen (TxModel.strp bs))) end.
  exact (H rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch dw t s k b0 len0 cap0 f0 own bs txt Lam peak
      cnt fail ran most HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19 HP20
      HP21).
Qed.

Record txsP_R (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i :
    nat) (rp_H0 : list Z) (ly : alayout) (S : astate) (Hp : list Z) (regs : bvmap 5 word) (dw t s k b0 len0 cap0 f0 own
    : Z) (bs txt : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most : Z) (add ks : list Z) (ly' : alayout) (S' :
    astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (b1 cap1 f1 own' : Z)
    (pre : list Z) (j : nat) (hist' : list chunk) : Prop := {
  txsP_post : prhtx_post Lam regs dw ly S Hp ly' S' Hp' W' mem' t b0 cap0 b1 (len0 + Z.of_nat (length pre)) cap1 f1
      (txt ++ pre);
  txsP_out : prhtx_out f0 f1 own own' b0 cap0 b1 cap1 (TxModel.tx_capf len0 cap0 ks) add pre;
  txsP_f1 : (f0 = 0 -> f1 = 0);
  txsP_cstr : PRH_Reader.pj_cstrR segs (rdW W' mem') (prh_lin Lam) s k bs;
  txsP_bvis : prhtx_bvis W' mem' s k;
  txsP_room : room_live_cf S';
  txsP_j_le : (j <= length (prhtx_evs len0 cap0 ks))%nat;
  txsP_pos : PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 hist' S';
  txsP_j_all : (f0 = 0 -> f1 = 0 -> j = length (prhtx_evs len0 cap0 ks));
  txsP_j_zero : (f0 <> 0 -> j = 0%nat);
  txsP_ledger : prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own' }.

Lemma txsP_R_of : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option
    nat)) (rp_i : nat) (rp_H0 : list Z) (ly : alayout) (S : astate) (Hp : list Z) (regs : bvmap 5 word) (dw t s k b0
    len0 cap0 f0 own : Z) (bs txt : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most : Z) (add ks : list Z) (ly' :
    alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' :
    Model),
  txsP_Q rp_sm rp_x rp_os rp_i rp_H0 ly S Hp regs dw t s k b0 len0 cap0 f0 own bs txt Lam peak cnt fail ran most add ks
      ly' S' Hp' W' regs' mem' md' ->
  exists b1 cap1 f1 own' pre j hist', txsP_R rp_sm rp_x rp_os rp_i rp_H0 ly S Hp regs dw t s k b0 len0 cap0 f0 own bs
      txt Lam peak cnt fail ran most add ks ly' S' Hp' W' regs' mem' b1 cap1 f1 own' pre j hist'.
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 ly S Hp regs dw t s k b0 len0 cap0 f0 own bs txt Lam peak cnt fail ran most add ks
      ly' S' Hp' W' regs' mem' md' H. destruct H as (b1 & cap1 & f1 & own' & pre & H0 & H1 & H2 & H3 & H4 & H5 & j &
      hist' & H6 & H7 & H8 & H9 & H10).
  exists b1, cap1, f1, own', pre, j, hist'.
  exact {| txsP_post := H0; txsP_out := H1; txsP_f1 := H2; txsP_cstr := H3; txsP_bvis := H4; txsP_room := H5; txsP_j_le
      := H6; txsP_pos := H7; txsP_j_all := H8; txsP_j_zero := H9; txsP_ledger := H10 |}.
Qed.

Lemma txsP_Q_of_R : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option
    nat)) (rp_i : nat) (rp_H0 : list Z) (ly : alayout) (S : astate) (Hp : list Z) (regs : bvmap 5 word) (dw t s k b0
    len0 cap0 f0 own : Z) (bs txt : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most : Z) (add ks : list Z) (ly' :
    alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' :
    Model) (b1 cap1 f1 own' : Z) (pre : list Z) (j : nat) (hist' : list chunk),
  txsP_R rp_sm rp_x rp_os rp_i rp_H0 ly S Hp regs dw t s k b0 len0 cap0 f0 own bs txt Lam peak cnt fail ran most add ks
      ly' S' Hp' W' regs' mem' b1 cap1 f1 own' pre j hist' ->
  txsP_Q rp_sm rp_x rp_os rp_i rp_H0 ly S Hp regs dw t s k b0 len0 cap0 f0 own bs txt Lam peak cnt fail ran most add ks
      ly' S' Hp' W' regs' mem' md'.
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 ly S Hp regs dw t s k b0 len0 cap0 f0 own bs txt Lam peak cnt fail ran most add ks
      ly' S' Hp' W' regs' mem' md' b1 cap1 f1 own' pre j hist' HR.
  exists b1, cap1, f1, own', pre.
  refine (conj (txsP_post HR) (conj (txsP_out HR) (conj (txsP_f1 HR) (conj (txsP_cstr HR) (conj (txsP_bvis HR) (conj
      (txsP_room HR) _)))))).
  exists j, hist'.
  exact (conj (txsP_j_le HR) (conj (txsP_pos HR) (conj (txsP_j_all HR) (conj (txsP_j_zero HR) (txsP_ledger HR))))).
Qed.

Local Unset Implicit Arguments.

(* tx_line (merged :432-439, body instruction-equal to the base's :398-405): tx_put of a newline, then d times two
   spaces (d an int, 0 <= d). The text it would append is concat (WriterValue.wind true d), the calls' sizes
   TxModel.plen (WriterValue.wind true d); the three outcomes are prhtx_out's. No frame, no block other than the
   buffer. *)
Definition ttx_line_specX (CTX0 : list (list Z)) : Prop :=
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk),
  forall ly S Hp W regs mem md ch (dw t d b0 len0 cap0 f0 own : Z) (txt : list Z) Lam peak cnt fail ran most,
  let add := concat (WriterValue.wind true d) in
  let ks := TxModel.plen (WriterValue.wind true d) in
  fpre B ARx STK_tx_line ly S Hp W regs mem md ch -> prh_univ_closure B CTX0 ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* THE RUN HAS AT MOST 4 CALLS: its tx_put calls take it (ttx_put_specX) *)
  (length rp_os <= 4)%nat ->
  (* THE WILD BUDGET (as tx_put's): one wild trace per GROW of its puts, k the EXACT number of grows of this call's
     own event list, which composes by prhtx_evs_app. A CONSTANT WOULD NOT DO HERE: this call makes d + 1 put calls
     (d up to 2 ^ 31 - 1) and at most 30 grows. Constant bound PRH_Base.prh_wk F_tx_line = 30. *)
  (f0 = 0 -> YCbqGwild.wild_room (as_universe B) [] (length (prhtx_evs len0 cap0 ks)) (st_depot S)) ->
  (* THE CALL'S ALLOCATIONS ARE CONSUMER ALLOCATIONS OF THE RUN (the ENTRY-KEYED texts' named entry premise,
     the kit owner's ruling 2026-10-29, extended to the tx family), over this call's own events, GUARDED by
     f0 = 0 as its event premise is (TX-RUNAT-F0); every grow of its puts is then a consumer event, so the post
     states DEAD-TXLINE. Supplied by the caller from its own window (PRH_Base.prh_cons_from_sub). *)
  (f0 = 0 -> PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhtx_evs len0 cap0 ks))) ->
  getr regs 10 = w64 t -> getr regs 11 = w64 d -> 0 <= d <= 2 ^ 31 - 1 ->
  fwin ly W regs mem dw -> prhtx_place ly S W regs mem dw t -> prhtx_trace ly W mem t ->
  prhtx_rec W mem t b0 len0 cap0 f0 -> prhtx_inv Lam ly S W mem b0 len0 cap0 txt ->
  len0 + 1 + 2 * d + 1 <= 2 ^ 28 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (* the run's next events are those of this call's puts, when it is entered with failed = 0 (TX-RUNAT-F0: entered
     failed it makes no event; see tx_put); see the post's note *)
  (f0 = 0 -> prh_run_at rp_sm rp_x rp_os rp_i (prhtx_evs len0 cap0 ks)) ->
  blocks_bytes S - cap0 + LIVE_tx <= LIVE_MAX -> 2 * (len0 + 1 + 2 * d + 1) < cf_malloc_max ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.14): its puts cross the grow's realloc *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_tx_line) regs mem md)
    (fpostWbmR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) (wbudget_if f0 [] (length (prhtx_evs len0 cap0 ks)))
      STK_tx_line dw (prhtx_fp t b0 cap0) regs ly S Hp W mem md
      (fun ly' S' Hp' W' regs' mem' md' =>
       exists b1 cap1 f1 own' (pre : list Z),
       prhtx_post Lam regs dw ly S Hp ly' S' Hp' W' mem' t b0 cap0 b1 (len0 + Z.of_nat (length pre)) cap1 f1
         (txt ++ pre) /\
       prhtx_out f0 f1 own own' b0 cap0 b1 cap1 (TxModel.tx_capf len0 cap0 ks) add pre /\
       (* DEAD-TXLINE (prhtx_out's REFUSED arm DEAD under prh_cons_from; three supports: PRH_Base's ENTRY-KEYED
          note): entered with failed = 0 it
          returns with failed = 0 (a REAL refusal of a put's raw realloc is the only way to failed = 1) *)
       (f0 = 0 -> f1 = 0) /\
       room_live_cf S' /\
       (* THE ADVANCE IS UNCONDITIONAL (the kit owner's ruling, 2026-10-29, on the image-B tx walk's counterexample:
          tx_line with d = 1, len0 = 0, cap0 = 0 makes put("\n") then put("  "); if the run's event at rp_i is
          not HMal 4, put 1's post gave NO position, so put 2's unconditional iface_room_pos premise was
          unavailable and a two-call text could not be proved by composing its callee's text. The run_at
          hypothesis is now an entry PREMISE of this text, so every position through a walk is unconditional
          and each post's advance exact. ANTI-VACUITY: the premise's supplier is this text's caller -
          check_round_trip supplies round_trip_text's, LLVMFuzzerTestOneInput supplies the top; a supply
          lemma that cannot be proved is a finding about the model, not a licence to keep the premise. *)
       exists j hist', (j <= length (prhtx_evs len0 cap0 ks))%nat /\
          PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 hist' S' /\
          (f0 = 0 -> f1 = 0 -> j = length (prhtx_evs len0 cap0 ks)) /\ (f0 <> 0 -> j = 0%nat) /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own')).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== ttx_line_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. txlP_Q IS the text's post (txlP_Q_check fails to build if
   the two ever differ); txlP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition txlP_Q (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i
    : nat) (rp_H0 : list Z) (ly : alayout) (S : astate) (Hp : list Z) (regs : bvmap 5 word) (dw t b0 len0 cap0 f0 own :
    Z) (txt : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most : Z) (add ks : list Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  exists b1 cap1 f1 own' (pre : list Z), prhtx_post Lam regs dw ly S Hp ly' S' Hp' W' mem' t b0 cap0 b1 (len0 +
      Z.of_nat (length pre)) cap1 f1 (txt ++ pre) /\ prhtx_out f0 f1 own own' b0 cap0 b1 cap1 (TxModel.tx_capf len0
      cap0 ks) add pre /\ (f0 = 0 -> f1 = 0) /\ room_live_cf S' /\ exists j hist', (j <= length (prhtx_evs len0 cap0
      ks))%nat /\ PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 hist' S' /\ (f0 = 0 -> f1 = 0 -> j
      = length (prhtx_evs len0 cap0 ks)) /\ (f0 <> 0 -> j = 0%nat) /\ prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail
      ran most own'.

Lemma txlP_Q_check : forall (CTX0 : list (list Z)), ttx_line_specX CTX0 -> ttx_line_specX CTX0.
Proof.
  intros CTX0 H. unfold ttx_line_specX in *.
  cbv zeta in H |- *.
  intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch dw t d b0 len0 cap0 f0 own txt Lam peak cnt fail
      ran most HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (txlP_Q rp_sm rp_x rp_os rp_i
      rp_H0 ly S Hp regs dw t b0 len0 cap0 f0 own txt Lam peak cnt fail ran most (concat (WriterValue.wind true d))
      (TxModel.plen (WriterValue.wind true d))) end.
  exact (H rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch dw t d b0 len0 cap0 f0 own txt Lam peak cnt
      fail ran most HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19).
Qed.

Record txlP_R (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i :
    nat) (rp_H0 : list Z) (ly : alayout) (S : astate) (Hp : list Z) (regs : bvmap 5 word) (dw t b0 len0 cap0 f0 own :
    Z) (txt : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most : Z) (add ks : list Z) (ly' : alayout) (S' : astate)
    (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (b1 cap1 f1 own' : Z) (pre :
    list Z) (j : nat) (hist' : list chunk) : Prop := {
  txlP_post : prhtx_post Lam regs dw ly S Hp ly' S' Hp' W' mem' t b0 cap0 b1 (len0 + Z.of_nat (length pre)) cap1 f1
      (txt ++ pre);
  txlP_out : prhtx_out f0 f1 own own' b0 cap0 b1 cap1 (TxModel.tx_capf len0 cap0 ks) add pre;
  txlP_f1 : (f0 = 0 -> f1 = 0);
  txlP_room : room_live_cf S';
  txlP_j_le : (j <= length (prhtx_evs len0 cap0 ks))%nat;
  txlP_pos : PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 hist' S';
  txlP_j_all : (f0 = 0 -> f1 = 0 -> j = length (prhtx_evs len0 cap0 ks));
  txlP_j_zero : (f0 <> 0 -> j = 0%nat);
  txlP_ledger : prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own' }.

Lemma txlP_R_of : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option
    nat)) (rp_i : nat) (rp_H0 : list Z) (ly : alayout) (S : astate) (Hp : list Z) (regs : bvmap 5 word) (dw t b0 len0
    cap0 f0 own : Z) (txt : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most : Z) (add ks : list Z) (ly' : alayout)
    (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  txlP_Q rp_sm rp_x rp_os rp_i rp_H0 ly S Hp regs dw t b0 len0 cap0 f0 own txt Lam peak cnt fail ran most add ks ly' S'
      Hp' W' regs' mem' md' ->
  exists b1 cap1 f1 own' pre j hist', txlP_R rp_sm rp_x rp_os rp_i rp_H0 ly S Hp regs dw t b0 len0 cap0 f0 own txt Lam
      peak cnt fail ran most add ks ly' S' Hp' W' regs' mem' b1 cap1 f1 own' pre j hist'.
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 ly S Hp regs dw t b0 len0 cap0 f0 own txt Lam peak cnt fail ran most add ks ly' S'
      Hp' W' regs' mem' md' H. destruct H as (b1 & cap1 & f1 & own' & pre & H0 & H1 & H2 & H3 & j & hist' & H4 & H5 &
      H6 & H7 & H8).
  exists b1, cap1, f1, own', pre, j, hist'.
  exact {| txlP_post := H0; txlP_out := H1; txlP_f1 := H2; txlP_room := H3; txlP_j_le := H4; txlP_pos := H5; txlP_j_all
      := H6; txlP_j_zero := H7; txlP_ledger := H8 |}.
Qed.

Lemma txlP_Q_of_R : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option
    nat)) (rp_i : nat) (rp_H0 : list Z) (ly : alayout) (S : astate) (Hp : list Z) (regs : bvmap 5 word) (dw t b0 len0
    cap0 f0 own : Z) (txt : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most : Z) (add ks : list Z) (ly' : alayout)
    (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
    (b1 cap1 f1 own' : Z) (pre : list Z) (j : nat) (hist' : list chunk),
  txlP_R rp_sm rp_x rp_os rp_i rp_H0 ly S Hp regs dw t b0 len0 cap0 f0 own txt Lam peak cnt fail ran most add ks ly' S'
      Hp' W' regs' mem' b1 cap1 f1 own' pre j hist' ->
  txlP_Q rp_sm rp_x rp_os rp_i rp_H0 ly S Hp regs dw t b0 len0 cap0 f0 own txt Lam peak cnt fail ran most add ks ly' S'
      Hp' W' regs' mem' md'.
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 ly S Hp regs dw t b0 len0 cap0 f0 own txt Lam peak cnt fail ran most add ks ly' S'
      Hp' W' regs' mem' md' b1 cap1 f1 own' pre j hist' HR.
  exists b1, cap1, f1, own', pre.
  refine (conj (txlP_post HR) (conj (txlP_out HR) (conj (txlP_f1 HR) (conj (txlP_room HR) _)))).
  exists j, hist'.
  exact (conj (txlP_j_le HR) (conj (txlP_pos HR) (conj (txlP_j_all HR) (conj (txlP_j_zero HR) (txlP_ledger HR))))).
Qed.

Local Unset Implicit Arguments.

(* tx_value (merged :441-475, body instruction-equal to the base's :407-441), recursive: n bounds the nested
   tx_value calls still to come (PjTree.depth tv <= n; plain TV_K, tx_value_c.v:18). By v->type: the literal null /
   false / true (tx_put); a number's text (the strlen wrapper, then a TAIL CALL of tx_put with tx_value's frame
   popped); a string (TAIL CALL of tx_string); an array / object: the opening bracket or brace, per item a comma,
   tx_line (depth + 1) if pretty, the key (tx_string), the colon and a space if pretty, the item (tx_value, depth + 1),
   then tx_line (depth) if pretty and non-empty, the closing bracket or brace. The text it would append is
   concat (WriterValue.wvpieces tv p d), the calls' sizes TxModel.tv_calls tv p d (tx_value_c.v:31-33); the three
   outcomes are prhtx_out's. The tree is the reader's (pj_nodeR over prh_lin Lam, its footprint D in Lam,
   tx_value_c.v:37-38); its node lies in a harness block or a fake frame (prhtx_home; never an image byte; the plain
   stack case :39 is the non-ASan build) apart from the record (:40); the tree, its footprint bytes and their shadow
   facts are kept. *)
Definition ttx_value_specX (CTX0 : list (list Z)) (n : nat) : Prop :=
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk),
  forall ly S Hp W regs mem md ch (dw t v pretty d b0 len0 cap0 f0 own : Z) (tv : PjTree.jv) (D : list (Z * Z))
    (txt : list Z) Lam peak cnt fail ran most,
  let p := negb (pretty =? 0) in
  let add := concat (WriterValue.wvpieces tv p d) in
  let ks := TxModel.tv_calls tv p d in
  fpre B ARx (STK_tx_value n) ly S Hp W regs mem md ch -> prh_univ_closure B CTX0 ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* THE RUN HAS AT MOST 4 CALLS: its tx_put / tx_string calls take it (ttx_put_specX) *)
  (length rp_os <= 4)%nat ->
  (* THE WILD BUDGET (as tx_put's): one wild trace per GROW of its puts, k the EXACT number of grows of this call's
     own event list. The two TAIL calls (a number's tx_put, a string's tx_string) need no weakening: at those arms
     the callee's event list IS this one (TxModel.tv_calls of a number / a string is that one call's list), so the
     two budgets are the same term. Constant bound PRH_Base.prh_wk F_tx_value = 30. *)
  (f0 = 0 -> YCbqGwild.wild_room (as_universe B) [] (length (prhtx_evs len0 cap0 ks)) (st_depot S)) ->
  (* THE CALL'S ALLOCATIONS ARE CONSUMER ALLOCATIONS OF THE RUN (the ENTRY-KEYED texts' named entry premise,
     the kit owner's ruling 2026-10-29, extended to the tx family), over this call's own events, GUARDED by
     f0 = 0 as its event premise is (TX-RUNAT-F0); every grow of its puts is then a consumer event, so the post
     states DEAD-TXVALUE. Supplied by the caller from its own window (PRH_Base.prh_cons_from_sub). *)
  (f0 = 0 -> PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhtx_evs len0 cap0 ks))) ->
  (PjTree.depth tv <= n)%nat ->
  getr regs 10 = w64 t -> getr regs 11 = w64 v -> getr regs 12 = w64 pretty -> getr regs 13 = w64 d ->
  - 2 ^ 31 <= pretty < 2 ^ 31 -> 0 <= d -> d + Z.of_nat (PjTree.depth tv) <= 2 ^ 31 - 1 ->
  fwin ly W regs mem dw -> prhtx_place ly S W regs mem dw t -> prhtx_trace ly W mem t ->
  prhtx_rec W mem t b0 len0 cap0 f0 -> prhtx_inv Lam ly S W mem b0 len0 cap0 txt ->
  PRH_Reader.pj_nodeR segs (rdW W mem) (prh_lin Lam) v tv D -> (forall b, In b D -> In b Lam) ->
  prhtx_home Lam ly S v 56 -> range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 56 ->
  Forall (fun b => prhtx_bvis W mem (fst b) (snd b)) D ->
  (v + 56 <= t \/ t + 28 <= v) ->
  len0 + Z.of_nat (length add) + 1 <= 2 ^ 28 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (* the run's next events are those of this call's puts, when it is entered with failed = 0 (TX-RUNAT-F0: entered
     failed it makes no event; see tx_put); see the post's note *)
  (f0 = 0 -> prh_run_at rp_sm rp_x rp_os rp_i (prhtx_evs len0 cap0 ks)) ->
  blocks_bytes S - cap0 + LIVE_tx <= LIVE_MAX -> 2 * (len0 + Z.of_nat (length add) + 1) < cf_malloc_max ->
  count_cid 0 (frames S) < fs_frames 0 ->
  (* the re-hiding move (PRIMED-SHAPES.md (sha256 9e4880d18317; internal record) sec. 2.15): its puts, strings and lines cross the
     grow's realloc *)
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_tx_value) regs mem md)
    (fpostWbmR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) (wbudget_if f0 [] (length (prhtx_evs len0 cap0 ks)))
      (STK_tx_value n) dw (prhtx_fp t b0 cap0) regs ly S Hp W mem md
      (fun ly' S' Hp' W' regs' mem' md' =>
       exists b1 cap1 f1 own' (pre : list Z),
       prhtx_post Lam regs dw ly S Hp ly' S' Hp' W' mem' t b0 cap0 b1 (len0 + Z.of_nat (length pre)) cap1 f1
         (txt ++ pre) /\
       prhtx_out f0 f1 own own' b0 cap0 b1 cap1 (TxModel.tx_capf len0 cap0 ks) add pre /\
       (* DEAD-TXVALUE (prhtx_out's REFUSED arm DEAD under prh_cons_from; three supports: PRH_Base's ENTRY-KEYED
          note): entered with failed = 0 it
          returns with failed = 0 (a REAL refusal of a put's raw realloc is the only way to failed = 1) *)
       (f0 = 0 -> f1 = 0) /\
       PRH_Reader.pj_nodeR segs (rdW W' mem') (prh_lin Lam) v tv D /\
       (forall x, PRH_Reader.pj_footR v D x -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) /\
       range_addressable (aview segs (w_H W') mem') SHADOW_OFF v 56 /\
       Forall (fun b => prhtx_bvis W' mem' (fst b) (snd b)) D /\
       room_live_cf S' /\
       (* THE ADVANCE IS UNCONDITIONAL (the kit owner's ruling, 2026-10-29, on the image-B tx walk's counterexample:
          tx_line with d = 1, len0 = 0, cap0 = 0 makes put("\n") then put("  "); if the run's event at rp_i is
          not HMal 4, put 1's post gave NO position, so put 2's unconditional iface_room_pos premise was
          unavailable and a two-call text could not be proved by composing its callee's text. The run_at
          hypothesis is now an entry PREMISE of this text, so every position through a walk is unconditional
          and each post's advance exact. ANTI-VACUITY: the premise's supplier is this text's caller -
          check_round_trip supplies round_trip_text's, LLVMFuzzerTestOneInput supplies the top; a supply
          lemma that cannot be proved is a finding about the model, not a licence to keep the premise. *)
       exists j hist', (j <= length (prhtx_evs len0 cap0 ks))%nat /\
          PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 hist' S' /\
          (f0 = 0 -> f1 = 0 -> j = length (prhtx_evs len0 cap0 ks)) /\ (f0 <> 0 -> j = 0%nat) /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own')).

Local Set Implicit Arguments.
(* the layer below: parameters a later argument determines are IMPLICIT, so a consumer writes
   <p>_R_of H, (field HR) and <field>_<name> HR .. without counting holes *)

(* ==== ttx_value_specX's POST, NAMED (read the text's post through NAMED projections; destruct once,
   cite the lemma). ADDITIVE: the text above is unchanged. txvP_Q IS the text's post (txvP_Q_check fails to build if
   the two ever differ); txvP_R and the arm records name every conjunct; the _of lemmas read them, the _of_R lemmas
   build the post from them. A consumer that reads and builds the post through these is not broken by the NEXT
   appended conjunct. ==== *)

Definition txvP_Q (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i
    : nat) (rp_H0 : list Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word) (mem :
    word -> option byte) (dw t v b0 len0 cap0 f0 own : Z) (tv : PjTree.jv) (D : list (Z * Z)) (txt : list Z) (Lam :
    list (Z * Z)) (peak cnt fail ran most : Z) (add ks : list Z) :
    alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  exists b1 cap1 f1 own' (pre : list Z), prhtx_post Lam regs dw ly S Hp ly' S' Hp' W' mem' t b0 cap0 b1 (len0 +
      Z.of_nat (length pre)) cap1 f1 (txt ++ pre) /\ prhtx_out f0 f1 own own' b0 cap0 b1 cap1 (TxModel.tx_capf len0
      cap0 ks) add pre /\ (f0 = 0 -> f1 = 0) /\ PRH_Reader.pj_nodeR segs (rdW W' mem') (prh_lin Lam) v tv D /\ (forall
      x, PRH_Reader.pj_footR v D x -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) /\ range_addressable
      (aview segs (w_H W') mem') SHADOW_OFF v 56 /\ Forall (fun b => prhtx_bvis W' mem' (fst b) (snd b)) D /\
      room_live_cf S' /\ exists j hist', (j <= length (prhtx_evs len0 cap0 ks))%nat /\ PresetRoomPos.iface_room_pos
      rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 hist' S' /\ (f0 = 0 -> f1 = 0 -> j = length (prhtx_evs len0 cap0 ks)) /\
      (f0 <> 0 -> j = 0%nat) /\ prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own'.

Lemma txvP_Q_check : forall (CTX0 : list (list Z)) (n : nat), ttx_value_specX CTX0 n -> ttx_value_specX CTX0 n.
Proof.
  intros CTX0 n H. unfold ttx_value_specX in *.
  cbv zeta in H |- *.
  intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch dw t v pretty d b0 len0 cap0 f0 own tv D txt Lam
      peak cnt fail ran most HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18 HP19
      HP20 HP21 HP22 HP23 HP24 HP25 HP26 HP27 HP28 HP29 HP30 HP31.
  lazymatch goal with |- context [SRr' _ _ _ _ (?FPOST ?QPOST)] => change QPOST with (txvP_Q rp_sm rp_x rp_os rp_i
      rp_H0 ly S Hp W regs mem dw t v b0 len0 cap0 f0 own tv D txt Lam peak cnt fail ran most (concat
      (WriterValue.wvpieces tv (negb (pretty =? 0)) d)) (TxModel.tv_calls tv (negb (pretty =? 0)) d)) end.
  exact (H rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch dw t v pretty d b0 len0 cap0 f0 own tv D txt
      Lam peak cnt fail ran most HP0 HP1 HP2 HP3 HP4 HP5 HP6 HP7 HP8 HP9 HP10 HP11 HP12 HP13 HP14 HP15 HP16 HP17 HP18
      HP19 HP20 HP21 HP22 HP23 HP24 HP25 HP26 HP27 HP28 HP29 HP30 HP31).
Qed.

Record txvP_R (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i :
    nat) (rp_H0 : list Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word) (mem : word
    -> option byte) (dw t v b0 len0 cap0 f0 own : Z) (tv : PjTree.jv) (D : list (Z * Z)) (txt : list Z) (Lam : list (Z
    * Z)) (peak cnt fail ran most : Z) (add ks : list Z) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (b1 cap1 f1 own' : Z) (pre : list Z) (j : nat) (hist' : list
    chunk) : Prop := {
  txvP_post : prhtx_post Lam regs dw ly S Hp ly' S' Hp' W' mem' t b0 cap0 b1 (len0 + Z.of_nat (length pre)) cap1 f1
      (txt ++ pre);
  txvP_out : prhtx_out f0 f1 own own' b0 cap0 b1 cap1 (TxModel.tx_capf len0 cap0 ks) add pre;
  txvP_f1 : (f0 = 0 -> f1 = 0);
  txvP_node : PRH_Reader.pj_nodeR segs (rdW W' mem') (prh_lin Lam) v tv D;
  txvP_keep : (forall x, PRH_Reader.pj_footR v D x -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x);
  txvP_addressable : range_addressable (aview segs (w_H W') mem') SHADOW_OFF v 56;
  txvP_tree_bvis : Forall (fun b => prhtx_bvis W' mem' (fst b) (snd b)) D;
  txvP_room : room_live_cf S';
  txvP_j_le : (j <= length (prhtx_evs len0 cap0 ks))%nat;
  txvP_pos : PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 hist' S';
  txvP_j_all : (f0 = 0 -> f1 = 0 -> j = length (prhtx_evs len0 cap0 ks));
  txvP_j_zero : (f0 <> 0 -> j = 0%nat);
  txvP_ledger : prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own' }.

Lemma txvP_R_of : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option
    nat)) (rp_i : nat) (rp_H0 : list Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5
    word) (mem : word -> option byte) (dw t v b0 len0 cap0 f0 own : Z) (tv : PjTree.jv) (D : list (Z * Z)) (txt : list
    Z) (Lam : list (Z * Z)) (peak cnt fail ran most : Z) (add ks : list Z) (ly' : alayout) (S' : astate) (Hp' : list Z)
    (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  txvP_Q rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem dw t v b0 len0 cap0 f0 own tv D txt Lam peak cnt fail ran most
      add ks ly' S' Hp' W' regs' mem' md' ->
  exists b1 cap1 f1 own' pre j hist', txvP_R rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem dw t v b0 len0 cap0 f0 own
      tv D txt Lam peak cnt fail ran most add ks ly' S' Hp' W' regs' mem' b1 cap1 f1 own' pre j hist'.
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem dw t v b0 len0 cap0 f0 own tv D txt Lam peak cnt fail ran most
      add ks ly' S' Hp' W' regs' mem' md' H. destruct H as (b1 & cap1 & f1 & own' & pre & H0 & H1 & H2 & H3 & H4 & H5 &
      H6 & H7 & j & hist' & H8 & H9 & H10 & H11 & H12).
  exists b1, cap1, f1, own', pre, j, hist'.
  exact {| txvP_post := H0; txvP_out := H1; txvP_f1 := H2; txvP_node := H3; txvP_keep := H4; txvP_addressable := H5;
      txvP_tree_bvis := H6; txvP_room := H7; txvP_j_le := H8; txvP_pos := H9; txvP_j_all := H10; txvP_j_zero := H11;
      txvP_ledger := H12 |}.
Qed.

Lemma txvP_Q_of_R : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option
    nat)) (rp_i : nat) (rp_H0 : list Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5
    word) (mem : word -> option byte) (dw t v b0 len0 cap0 f0 own : Z) (tv : PjTree.jv) (D : list (Z * Z)) (txt : list
    Z) (Lam : list (Z * Z)) (peak cnt fail ran most : Z) (add ks : list Z) (ly' : alayout) (S' : astate) (Hp' : list Z)
    (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (b1 cap1 f1 own' : Z) (pre :
    list Z) (j : nat) (hist' : list chunk),
  txvP_R rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem dw t v b0 len0 cap0 f0 own tv D txt Lam peak cnt fail ran most
      add ks ly' S' Hp' W' regs' mem' b1 cap1 f1 own' pre j hist' ->
  txvP_Q rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem dw t v b0 len0 cap0 f0 own tv D txt Lam peak cnt fail ran most
      add ks ly' S' Hp' W' regs' mem' md'.
Proof.
  intros rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem dw t v b0 len0 cap0 f0 own tv D txt Lam peak cnt fail ran most
      add ks ly' S' Hp' W' regs' mem' md' b1 cap1 f1 own' pre j hist' HR.
  exists b1, cap1, f1, own', pre.
  refine (conj (txvP_post HR) (conj (txvP_out HR) (conj (txvP_f1 HR) (conj (txvP_node HR) (conj (txvP_keep HR) (conj
      (txvP_addressable HR) (conj (txvP_tree_bvis HR) (conj (txvP_room HR) _)))))))).
  exists j, hist'.
  exact (conj (txvP_j_le HR) (conj (txvP_pos HR) (conj (txvP_j_all HR) (conj (txvP_j_zero HR) (txvP_ledger HR))))).
Qed.

Local Unset Implicit Arguments.

End c.
