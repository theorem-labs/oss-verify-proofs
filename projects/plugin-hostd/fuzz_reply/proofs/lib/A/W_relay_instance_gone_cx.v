(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the SEGMENT INTERFACE of the ASan walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan 0x82c2c .. 0x830dc, 300 instructions), in the form of lane W7's lib/A/W_drain_cx.v and this lane's
   lib/A/W_relay_remove_cx.v (segments joined at cut points, cgif lib/A/AC8b.v and ACfj.v).
   Nothing is proved here: the file fixes the Section hypotheses, the entry context, the cut predicates over
   concrete machine states and the statement of every segment, so that the segments are proved in parallel.

   relay_instance_gone (id) is relay.c:441-449 with gestures_end_instance (relay.c:149-168) inlined: under g_lock,
   for each entry i of the table in order: drain it when open; snprintf the prefix "param_gesture <id> " into the
   48-byte buffer at F + 32 of the class-1 fake frame F; then, over its held keys at index n while n < nheld: a key
   with the prefix is ended (gesture_end), freed, and the last key moved into its place (n stays); any other key is
   passed (n + 1).  Then g_lock is released.  Its contract is W_contract.v Section s6: rig_spec B MT MMAX RG
   (BASE + AF_fr_relay_instance_gone), post rig_post; the model is rig_rel / geik_loop (W_contract.v) and the budget
   rig_tr (the plain model's relay_instance_gone_tr).

   CUT POINTS
     RGO i       0x82d98  the outer loop's head at entry i (entries 0 .. i-1 done: GOUT i);
     RGI i n r   0x82e50  the inner (held keys) loop's head at index n of entry i, r + 1 = nheld - n (GIN);
     RGE i       0x82f44  entry i done (GOUT (S i)), before the step;
     RGU         0x82fa4  the unlock tail, every entry done (GOUT |es|).
   SEGMENTS
     PRO    0x82c2c -> RGO 0 | RGU                         prologue, __asan_stack_malloc_1, the lock, g_nsrc <= 0
     TOP    RGO i -> RGI i 0 r | RGE i                     eof check, drain (when open), unpoison F+32..F+80,
                                                           snprintf (prefix), strlen (prefix), the nheld test
     KEY    RGI i n (S r) -> RGI i (S n) r | RGI i n r     one key: strncmp; pass, or gesture_end + free + move
            RGI i n r -> RGE i
     KEYS   the inner loop by induction on r               composition of KEY
     STEP   RGE i -> RGO (S i) | RGU                       repoison F+32..F+80, i += 1, the outer test (no call)
     OUTER  the outer loop by induction on |es| - i        composition of TOP, KEYS, STEP
     TAIL   RGU -> rig_post                                unlock, the frame's release, the epilogue
   Every segment concludes `SRr SEGS W1 c1 (gPOST cx)` and takes its continuations in the same form.

   THE BUDGET.  As W_drain_cx.v's dbud: `spent` is what the walk has charged the meter, `tl` the requests still to
   come, as the plain model's trace restarted from the current g_nout / g_capout (address names (fun _ => a0), base
   0, g_out a0: the trace's cost reads sizes only, W_contract.v tr_cost).  At RGO i and RGE i it is grest (the run
   over entries i ..); inside entry i it is the rest of entry i's key run (gkrest) followed by grest (S i).

   COMPOSITION NOTE (snprintf).  ASNPRINTF (W_sites.v asnprintf_realizes, a Theorem Labs lane's RtFormat statement at our
   addresses, SRr form) is discharged ONCE at the top: lib/A/RT_pf_vf.v snprintf_chain_ok (commit 9067b7156f9; the
   evt-level chain, RT_pf_stmt.v snprintf_icpt_stmt), then a Theorem Labs lane's evt -> SRr bridge (commit
   efa2842e125).  No walk file imports the CJ / Bz tree.  The chain's stack requirement at __wrap_snprintf is
   K = 8208 bytes (glue 2608 + GXA's 48 + VF_DEPTH 5552), inside asnprintf_realizes' 3 * ESTACK window, and it
   needs GXA's frm0 (rounding mode 0) on fcsr: TOP's walk carries the stack window (ecall_pre_stk (3 * ESTACK))
   at 0x82e04, and the bridge owner takes frm0 from the start-up FP state (fcsr = 0, lib/Reusable/YK11.v:16) or the
   previous call's post.

   STATEMENT GAPS (facts the machine has that the first text lacked; each found at a prover's unprovable goal, each
   fixed by stating the fact and discharging it at PB_fr / fr_globals by vm_compute, never by weakening):
   - GLIVE own = [] (RigTail, aj_flag_store_pi / aj_stack_malloc_pres_at): the fake frame read as an ENTRY frame; now
     own = [(1, fpos)] (6322e1c462a).
   - HH44 / HH45 (RigPro, the slots 72(sp) / 40(sp) and s6): the abstract PI leaves VAL (A_HI 44 / 45) -
     VAL (A_OBJ 7 / 8) open (W_rebase.v:7-15) (d700f304923).
   - key slack (W_rep.v bounded it only from below; W8's ruling-(A) W_rep.v removes it) (ead5de7cc24).
   - HRGP / HRGI (RigTail, rig_post's aout_at / arelay_at after the unlock): counter-case rg_send_max = rg_lock + 4
     with mx = 16; four cells not placed in the image could sit in F, its shadow or the stack (eab4b19b11c).
   - HROMO and HRGI's not-owned-static half (RigPro, rom_view and aout_at across __asan_stack_malloc_1, which keeps
     only bytes that are not aowned) (cd96cd63ec8).
   - WHY ASNPRINTF'S STACK PREMISE IS DISCHARGED AT 0x82e04 (asked by a Theorem Labs lane for the snprintf chain's guarded
     route, K = 8208): sp there is gsp1 = entry sp - 224 (gregs_base), and GBASE's afn_pre gives RIG_STK_x = 17200
     bytes below the entry sp (W_rig_pro.v rgp_entry, by reflexivity), so 16976 bytes lie below the call;
     ASNPRINTF itself asks ecall_pre_stk (3 * ESTACK) = 12288 >= 8208.
   - rig_outer_stmt took rig_keys_stmt (itself `rig_key_stmt -> ...`) without rig_key_stmt, so OUTER could not feed
     KEYS and TOP's RGI continuation was undischargeable (a Theorem Labs lane's RigStep, proving OUTER); OUTER now takes
     rig_key_stmt too (ruling: a Theorem Labs lane, fix (1)).  rr_all_stmt checked: SCANS is fed by SCAN, every premise used.
   - a Theorem Labs lane's relay_remove findings, checked here: Q2 ROOM applied under the sum form (gesture_end's ge_roomb with
     a send that does not grow g_out: rig_spec and GBASE took cap < MMAX and blocks_bytes + tr_alloc + 4 * max cap
     tr_max <= LIVE_MAX, 1744b876fbd).  C3 (475b8a2b569, the peak form) REMOVED both: ge_room is stated over
     gesture_end's own trace, so rig_spec and GBASE take blocks_bytes + tr_peak tr <= LIVE_MAX (tr_max tr < MMAX and
     the meter unchanged), and gbud's room over the remaining trace tl is blocks_bytes S1 + tr_peak tl <= LIVE_MAX
     (was + tr_alloc tl).  Q3: HEND5 (W4's text) for ge_spec's END5 literal.  Q6: rig_lift_DR / rig_lift_SL in this file.
     Q1 does NOT apply: relay_instance_gone frees only the keys it ends (live blocks, RFree (|key| + 1) in every
     keys_end_run step); it has no free (NULL) site, so rig_tr is unchanged.

   - HEND5L (k3's RigKey end arm, GE / GSE's garr8 (VAL A_lit_end5) (bzs END5)): HEND5 gave the literal's zero shadow
     and placement but not its BYTES; a walk that compares against or passes a literal needs all three (bytes, shadow,
     placement), and this is the unit's fifth gap of that class tonight.
   - HEND5 and glit_at's azs conjunct REMOVED (a Theorem Labs lane, six measurements): a zero-shadow premise over a string
     literal is FALSE for ASan globals (the literal's last granule is partial: " end\0" at 0x20f00 has shadow byte 5),
     so HEND5 (W4's text) and azs over "%s %d " / "param_gesture" could not be discharged.  ge_spec / gse_spec need
     only the bytes (HEND5L + rom_view); the literal predicate (now glit_at_x) carries W3's ashp (range_addressable over exactly [a, a + n) and
     the shadow hull).  Delete-and-rebuild check: no Qed piece used HEND5 or the azs conjunct.
   CONSUMER NOTE (W8's ARM_gone, LLVMFuzzerTestOneInput's call of relay_instance_gone): since C3 (475b8a2b569) rig_spec's
   room premise at the call is `blocks_bytes S + tr_peak tr <= LIVE_MAX` (was `+ tr_alloc tr`), with tr = rig_tr c mx
   |O| cap ID es hs; the two premises 1744b876fbd added (`cap < MMAX`, `blocks_bytes S + tr_alloc tr + 4 * Z.max cap
   (tr_max tr) <= LIVE_MAX`) are GONE.  (The canary-presence premise 6a1bcf9f403 added is GONE again:
   the canary's bytes are image bytes, HCANR, so nothing about them is carried.)

   SNPRINTF'S GUARD AND LITERALS (k3's RigTop, a Theorem Labs lane's request): ASNPRINTF asks aguard_ok W mem FR_GOT_GUARD
   FR_GUARD at 0x82e04.  Its first half (the GOT word holds the canary's address) is HGOTG, an AR fact discharged at
   the top by lib/A/AE22.v got_canary_of_AR (TfibSyms B: the word is the const cell z8 0x9e658 0x5f94b0 of
   Tfib_const_abs; am_const, NOT rom_view: the word is writable).  Its second half (the canary is readable) holds in
   every state because the canary's bytes are image bytes (HCANR: seg_rom [0x5f94b0, +8) = Some 0, aview falls back to
   seg_rom); nothing is carried from the entry (a Theorem Labs lane's ruling, superseding 6a1bcf9f403's carried presence).  The two literals snprintf and strlen read, the
   format "%s %d " (.str.8, A_OBJ 20) and "param_gesture" (.str.5, A_OBJ 21), are HLIT20 / HLIT21 in W7's dlit_at
   form (W_drain_cx.v:220; W7's HLIT5 is the same fact for A_OBJ 21).

   ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record); the RIG_x round): converted IN PLACE to any
   allocator relation ARx with its laws and the room record RP (W_journal_x.v Record roomp).  Section c takes
   PST / ARx / hl / LAWS (AR_laws_x), HP0 (a Theorem Labs lane's ruling: no hidden head in any ARx state), the frame twins'
   hypotheses of W_frame_x.v in place of ML / SMP (IMGC, BLKN, OWNLOW, WFx, WFL, SFREE, SMALLOC) with ASMP / ASF / FFL
   in their _x forms, the runtime entries and callees in their _x room forms (W_sites_x.v, W_contract_x.v,
   W_journal_x.v Section hc), ALLOC_TAIL and HGOTG over ARx, the literals' shadow by W_contract_x.ashp_x, and two facts
   on the program statics PST that the journal's image clause exempts (PSTR, PSTG; both hold at PST = []), as the
   template lib/A/W_relay_finish_h.v (commit 3d17f490d56) does.  The entry record gcx gains the entry's head set gxHp
   and room budget gxkr; GBASE is rig_spec_x's premises exactly (W_contract_x.v :975), gPOST rig_post_x; GLIVE's
   journal is ajournal_gx_x from gxHp to the cut's head set Hp1 (existential, beside fpos); gbud takes the cut's
   layout and carries, beside the meter, the room the requests still owed need on top of gxkr
   (rp_RM RP S1 (Z.to_nat (tr_cost MT_rk tl) + gxkr cx)) and the live counts plus rig_pk's shape over those requests
   (cnt_ok_pk RP (fun P => Z.to_nat (tr_peakP P tl) + 3) (ablocks B ly1 S1)); at the entry (tl = gtr cx) both are
   GBASE's, by conversion.  rig_all_stmt concludes rig_spec_x.
   THE STACK BUDGET (W8's DRAIN_STK_x ruling, commit b9052387bcb, W_contract_x.v): rig_spec_x's pre and post journal
   take RIG_STK_x = RIG_STK + 128 and dr_spec_x's DRAIN_STK_x = DRAIN_STK + 128 (the strndup interceptor's inner malloc
   below the drain's frame), so GBASE's afn_pre_x and GLIVE's journal are at RIG_STK_x, the drain call at
   DRAIN_STK_x (RIG_STK_x = RIG_FRAME + DRAIN_STK_x still holds), and the segments' stack arithmetic uses both.  The
   bridge rig_spec_x_AR0 is false at RIG_STK_x and was deleted with that ruling, so the family proves only the generic
   pb_relay_instance_gone_x (a Theorem Labs lane's ruling, option 1): the AR theorem and its re-derivation are deleted. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c relay_instance_gone_b_c drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_journal W_sites W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_sites_x W_contract_x W_frame_x.
(* the count names (tr_peakP): lib/A/ReplyCnt.v, the one definition; Required, not Imported, and named qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
(* route R: a Theorem Labs lane's rig_post_xR / rig_spec_xR, a Theorem Labs lane's dr_spec_xR / ge_spec_xR, SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR W_contract_xR_relay.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ---- The walk's program counters (listing slot = (addr - 0x822ec) / 4; AF_fr_relay_instance_gone = 0x940). ---- *)
Definition A_rig_entry : Z := AF_fr_relay_instance_gone.            (* 0x82c2c, the entry *)
Definition A_rig_entryP : Z := BASE + A_rig_entry.
Definition A_rig_outer : Z := AF_fr_relay_instance_gone + 0x16c.    (* 0x82d98, the outer loop's head *)
Definition A_rig_inner : Z := AF_fr_relay_instance_gone + 0x224.    (* 0x82e50, the inner loop's head *)
Definition A_rig_step : Z := AF_fr_relay_instance_gone + 0x318.     (* 0x82f44, entry i done *)
Definition A_rig_unlock : Z := AF_fr_relay_instance_gone + 0x378.   (* 0x82fa4, the unlock tail *)

(* The callee-saved registers in their frame slots 120(sp) (s11) .. 216(sp) (ra), sp = the entry sp - 224. *)
Definition RIG_SAVED : list (bv 5) :=
[27%bv; 26%bv; 25%bv; 24%bv; 23%bv; 22%bv; 21%bv; 20%bv; 19%bv; 18%bv; 9%bv; 8%bv; 1%bv].

(* The register images of g_nsrc and g_src: the auipc at 0x82d58 (kept at 72(sp); g_nsrc = it - 1464) and s6, the
   auipc at 0x82d74 (kept at 40(sp); g_src = s6 - 1460). *)
Definition RIG_HI_NSRC : Z := 1464.
Definition RIG_HI_SRC : Z := 1460.

Section c.
Variable B : asyms.
(* the program statics of the generic journal (YCbqG.ajournal_x's image clause exempts them) *)
Variable PST : list (Z * Z).
(* the allocator relation, its third argument the head set Hp *)
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (K0_SITES' CTX_AFREE) *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts').  Each is either the AR
   walk's (AR-free, verbatim), its _x twin, or an instance fact that the instance supplies where RIG_x is plugged
   (top_x); the AR re-derivation was deleted (W_relay_instance_gone.v's header says why). ---- *)
(* the instance's laws, over ARx *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* no hidden head in any ARx state (a Theorem Labs lane's HP0 ruling; W_journal_x.v range_addressable_of_block_hp0_x) *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MLAW : ameter_laws MT.
(* the frame twins' hypotheses (W_frame_x.v), in place of ML / SMP: the image cover IMGC (frm_off_imgP_x); a live
   block's size is non-negative (W_kit_x.v's BLKN); the owned-low law OWNLOW, the model invariant WFx with its law WFL,
   and the two facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis SFREE : forall s cid pos, WFx s -> In (cid, pos) (frames s) ->
exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
(* the fake frame's laws over ARx: __asan_stack_malloc_1 (class 1), the release's flag store and frame free *)
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 1.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
(* the meter does not charge the fake frame's seat or its release, both a set_fs of the state (W8's ruling, KF-COUNT
   #4: the old text over an ablocks equation is false at the count meter) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
Hypothesis HGRIG : gx_ok SEGS B (G_RIG B RG).
(* the register images of g_nsrc / g_src: the auipc's of 0x82d58 (kept at 72(sp), listing A_HI 44) and 0x82d74
   (s6, A_HI 45).  The abstract placement does not fix them against the objects (W_rebase.v:7-15); PB_fr discharges
   both by vm_compute, as W_send_line_cx.v's HH17 .. HH24. *)
Hypothesis HH44 : VAL (A_HI 44) = rg_nsrc RG + RIG_HI_NSRC.
Hypothesis HH45 : VAL (A_HI 45) = rg_src RG + RIG_HI_SRC.
(* the relay's and the output's global cells are pairwise apart, and errno with them; the four that neither rg_place
   nor gx_ok places are image bytes (so apart from the frames, the fake frame's shadow and the stack).  The pinned
   placement decides both by vm_compute at fr_globals, as W7's W_drain_cx.v HRGD / HGSB. *)
Hypothesis HRGP : zpairwise_disjoint
[(rg_lock RG, rg_lock RG + 12); (rg_s RG, rg_s RG + 4 * ASRC); (rg_src RG, rg_src RG + 8);
 (rg_nsrc RG, rg_nsrc RG + 4); (rg_capsrc RG, rg_capsrc RG + 4); (rg_send_max RG, rg_send_max RG + 8);
 (rg_nout RG, rg_nout RG + 8); (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_dead RG, rg_send_dead RG + 1); (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_wake RG + 4, rg_wake RG + 8);
 (as_errno B, as_errno B + 4)].
Hypothesis HRGI : forall a,
(rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* no read-only image byte is owned by the runtime (W_gesture_end.v's HROMO form): rom_view survives the stack
   allocator's calls (W_journal_x.v ajournal_gx_rom_view_x) *)
Hypothesis HROMO : rom_out SEGS B (G_RIG B RG).
(* the allocator instance's granule-tail fact (W7's ALLOC_TAIL over ARx, as W_drain_cx_x.v states it; there a theorem
   of the laws, alloc_tail_x): a held key is represented over its |text| + 1 bytes (ruling (A)); a word read of a
   key to the end of its last granule is visible *)
Hypothesis ALLOC_TAIL : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
(* the runtime entries relay_instance_gone calls, at their SIGMA pcs, over ARx (W_sites_x.v / W_contract_x.v /
   W_journal_x.v Section hc; the free rule at the room record RP).  snprintf: a Theorem Labs lane's statement at fuzz_reply's
   addresses (W_sites.v asnprintf_realizes, its twin W_sites_x.v asnprintf_realizes_x), which the snprintf chain
   (commit 9067b7156f9, lib/A/RT_pf_vf.v snprintf_chain_ok, through a Theorem Labs lane's evt -> SRr bridge) discharges. *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis ASNPRINTF : asnprintf_realizes_x B ARx (SIGMA WS_snprintf) FR_GOT_GUARD FR_GUARD.
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
(* the program functions relay_instance_gone calls (W7's drain, W4's gesture_end), by their published _x room specs *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GE : ge_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gesture_end).
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* snprintf's stack-protector cells (see the header): the GOT word, a fact of every ARx state (at ARi0: the AR fact
   of lib/A/AE22.v got_canary_of_AR); the canary, image bytes *)
Hypothesis HGOTG : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  rdword (aview SEGS (w_H W) mem) FR_GOT_GUARD = Some FR_GUARD.
(* the canary's bytes are image bytes (seg_rom SEGS at FR_GUARD .. + 8 is Some 0), so aview reads them in EVERY state
   through mbyte's seg_rom fallback: aguard_ok's second half needs nothing carried (a Theorem Labs lane's ruling; a Theorem Labs lane's
   pin measurement).  PB_fr decides it by vm_compute. *)
Hypothesis HCANR : forall a, FR_GUARD <= a < FR_GUARD + 8 -> seg_rom SEGS (Z_to_bv 64 a) <> None.
(* the two literals of the snprintf call, in W7's dlit_at form (W_drain_cx.v:220): the bytes in .rodata, read-only,
   zero shadow, and the shadow hull visible in every ARx state *)
Definition RIG_FMT : list Z := [37; 115; 32; 37; 100; 32].   (* "%s %d " *)
(* ashp is RomOutPlace's lib/A/W_shadow_pin.v (commit 209a71e66fe), the unit's one definition: range_addressable over
   exactly [a, a + n) and the shadow hull, in every allocator state; glit_at_x states it over ARx (W_contract_x.v
   ashp_x).  (The AR text glit_at served only the AR re-derivation, deleted with it.) *)
Definition glit_at_x (i : nat) (l : list Z) : Prop :=
(forall k, (k < length l)%nat ->
   seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ i) + Z.of_nat k)) = option_map (Z_to_bv 8) (nth_error l k)) /\
(forall x, VAL (A_OBJ i) <= x < VAL (A_OBJ i) + Z.of_nat (length l) -> YG0d.in_rom SEGS x) /\
ashp_x ARx (VAL (A_OBJ i)) (Z.of_nat (length l)) /\
(* the bytes after the literal's NUL to the end of its 8-byte granule are image bytes (snprintf's atail_vis and its
   "%s" argument read to the granule's end; found by BRigTop at 0x82eb8; PB_fr decides it by vm_compute) *)
(forall x, VAL (A_OBJ i) + Z.of_nat (length l) <= x <
   VAL (A_OBJ i) + Z.of_nat (length l) - 1 - (VAL (A_OBJ i) + Z.of_nat (length l) - 1) mod 8 + 8 ->
   seg_rom SEGS (Z_to_bv 64 x) <> None).
Hypothesis HLIT20 : glit_at_x 20 (RIG_FMT ++ [0]).
Hypothesis HLIT21 : glit_at_x 21 (RelayModel.K_GESTURE ++ [0]).
(* the two literals lie in .rodata below the GOT word FR_GOT_GUARD = 0x9e658, |"%s %d "| + 1 = 7 and
   |"param_gesture"| + 1 + 8 = 22 bytes: the location premises M1 / M3 of the narrowed asnprintf_realizes_x
   (W_sites_x.v), which this abstract placement does not fix.  PB_fr decides it by vm_compute: SnpNarrowSites.v
   HLITGOT_PB_fr, whose statement is this text at PI := PB_fr (commit 2f48fc47493's hypothesis, carried here). *)
Hypothesis HLITGOT : VAL (A_OBJ 20) + 7 <= FR_GOT_GUARD /\ VAL (A_OBJ 21) + 22 <= FR_GOT_GUARD.
(* " end\0" (.str.4, A_lit_end5 = A_OBJ 31) in the same form, for gesture_end's / gestures_end's garr8 premise and its
   ashp (instance: W_shadow_pin_fr.v ashp_end5_5_fr): bytes, in_rom, ashp, the granule's tail; HEND5L above gives the
   bytes alone *)
Hypothesis HLIT31 : glit_at_x 31 ([32; 101; 110; 100] ++ [0]).
(* The program statics PST hold no byte this walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x, the literals and " end\0"), and no byte of the
   relay's and the output's global cells (G_RIG, and the cells of HRGP that G_RIG does not name: g_src, g_nsrc,
   g_capsrc, g_send_max, g_client, g_send_dead).  At PST := [] both hold trivially (the template's PSTR / PSTC /
   PSTO, lib/A/W_relay_finish_h.v). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a,
(inG (G_RIG B RG) a \/ rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
 rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
~ Exists (in_zr a) PST.

(* ---- The callees' journals, lifted to relay_instance_gone's globals: drain's at G_DR and gesture_end's at G_SL are
   journals at G_RIG (W_journal_x.v ajournal_gx_G_mono_x), for every call-making segment. ---- *)
Lemma rig_G_DR_RIG : forall a, inG (G_DR B RG) a -> inG (G_RIG B RG) a.
Proof. intros a Ha. unfold G_RIG, inG in *. apply Exists_cons_tl. exact Ha. Qed.
Lemma rig_G_SL_RIG : forall a, inG (G_SL B RG) a -> inG (G_RIG B RG) a.
Proof. intros a Ha. apply rig_G_DR_RIG. unfold G_DR, inG in *. apply Exists_cons_tl. exact Ha. Qed.
Lemma rig_lift_DR : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_DR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_x; [exact rig_G_DR_RIG | eassumption]. Qed.
Lemma rig_lift_SL : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_SL B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_x; [exact rig_G_SL_RIG | eassumption]. Qed.

(* ---- The entry context: rig_spec_x's binders, with the entry's head set gxHp and its room budget gxkr. ---- *)
Record gcx : Type := mkGcx {
  gxregs : bvmap 5 word;
  gxly : alayout; gxS : astate; gxHp : list Z; gxW : world SEGS; gxmem : word -> option byte; gxmd : Model;
  gxch : list (Z * Z * Z);
  gxG0 : Z; gxID : Z; gxes : list rentry; gxhs : list (hsrc * nat);
  gxc : ctl; gxO : list byte; gxmx : Z; gxcap : Z; gxout : Z;
  gxrest : list (Z * Z); gxkr : nat }.

Definition gsp0 (cx : gcx) : Z := spZ (gxregs cx).
Definition gsp1 (cx : gcx) : Z := gsp0 cx - RIG_FRAME.
Definition gpre (cx : gcx) : list Z := relay_instance_gone_b_c.instance_prefix (gxID cx).
Definition gps (cx : gcx) : list (rentry * (hsrc * nat)) := combine (gxes cx) (gxhs cx).
Definition gnth (cx : gcx) (i : nat) : rentry := nth i (gxes cx) relay_remove_b_c.no_entry.
Definition ghj (cx : gcx) (i : nat) : hsrc * nat := nth i (gxhs cx) relay_instance_gone_b_c.no_hj.
Definition gslot (cx : gcx) (i : nat) : Z := rg_s RG + ASRC * Z.of_nat (snd (ghj cx i)).
Definition gSA (cx : gcx) (i : nat) : Z := gxG0 cx + AENT * Z.of_nat i.
Definition gFP (cx : gcx) : list (Z * Z) := rig_fp (gxG0 cx) (gxes cx) (gxhs cx) (gxcap cx) (gxout cx).
Definition gtr (cx : gcx) :=
rig_tr (gxc cx) (gxmx cx) (Z.of_nat (length (gxO cx))) (gxcap cx) (gxID cx) (gxes cx) (gxhs cx).
Definition ga0 : RelayRunT.addr YO0i.sptr := drain_b_c.da_out drain_b_c.dadr0.
(* the requests of the entries i .. from g_nout = no, g_capout = cap (rig_tr's run over the suffix) *)
Definition grest (cx : gcx) (i : nat) (no cap : Z) :=
relay_instance_gone_b_c.relay_instance_gone_tr (sl_live (gxc cx) 1) (gxmx cx) no cap (gpre cx)
  (skipn i (gxes cx)) (skipn i (gxhs cx)) (fun _ => ga0) 0 ga0.
(* the requests of ending the keys Er (gesture_end, free each), from g_nout = no, g_capout = cap *)
Definition gkrest (cx : gcx) (no cap : Z) (Er : list (Z * list byte * list byte)) :=
fst (keys_end_run (sl_live (gxc cx) 1) (gxmx cx) no cap
       (map (fun k => (Z.of_nat (length (key_text k)), ga0)) Er) 0 ga0).
Definition gPOST (cx : gcx) : world SEGS -> config -> Prop :=
rig_post_x B PST ARx MT RP RG (gxregs cx) (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx)
  (gxG0 cx) (gxID cx) (gxes cx) (gxhs cx) (gxc cx) (gxO cx) (gxmx cx) (gxcap cx) (gxout cx) (gxkr cx).

(* GBASE: exactly rig_spec_x's premises at the entry (W_contract_x.v :975), with the Permutation's `rest` taken from
   the context, the room record's two premises at the entry's budget gxkr last. *)
Definition GBASE (cx : gcx) : Prop :=
afn_pre_x SEGS B ARx RIG_STK_x (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxregs cx) (gxmem cx) (gxmd cx) (gxch cx) /\
gsp0 cx mod 32 = 0 /\ count_cid 1 (frames (gxS cx)) < fs_frames 1 /\ rg_place B RG /\
getr (gxregs cx) 10 = w64 (gxID cx) /\ - 2 ^ 31 <= gxID cx < 2 ^ 31 /\
alock_at RG (gxW cx) (gxmem cx) false /\
arelay_at B RG (gxly cx) (gxS cx) (gxW cx) (gxmem cx) (gxG0 cx) (gxes cx) /\
aout_at B RG (gxly cx) (gxS cx) (gxW cx) (gxmem cx) (gxc cx) (gxO cx) (gxmx cx) (Z.of_nat (length (gxO cx)))
  (gxcap cx) (gxout cx) /\
rom_view SEGS (gxW cx) (gxmem cx) /\
length (gxhs cx) = length (gxes cx) /\
Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG (gxly cx) (gxS cx) (gxW cx) (gxmem cx) (fst p) (fst (snd p)) (snd (snd p)))
  (gps cx) /\
NoDup (rig_slots (gps cx)) /\
Permutation (ablocks B (gxly cx) (gxS cx))
  ((gxG0 cx, ATABLE) :: concat (map aentry_blks (gxes cx)) ++ rig_srcs (gps cx) ++ aout_blks (gxcap cx) (gxout cx) ++
   gxrest cx) /\
tr_max (gtr cx) < MMAX /\ blocks_bytes (gxS cx) + tr_peak (gtr cx) <= LIVE_MAX /\
mo_ok MT (gxS cx) (tr_cost MT (gtr cx)) /\
rp_RM RP (gxS cx) (Z.to_nat (tr_cost MT_rk (gtr cx)) + gxkr cx) /\
cnt_ok_pk RP (rig_pk (gtr cx)) (ablocks B (gxly cx) (gxS cx)).

(* GCTX: rig_spec's caller-context premise at the entry (W_contract.v), read by KEY's free at 0x82eb4 (ra 0x82eb8):
   0x82eb8, then this entry's return and chain (s0 = the entry sp is a frame pointer) *)
Definition GCTX (cx : gcx) : Prop :=
spZ (gxregs cx) + 16 < ly_top (gxly cx) /\ In (A_rig_entryP + 652 :: raZ (gxregs cx) :: spine (gxch cx)) CTX_AFREE.

(* ---- The frame. ----
   After the prologue: sp = the entry sp - 224 (the entry sp is 32-aligned), the thirteen callee-saved registers in
   their slots, the class-1 fake frame F at position fpos of the allocator's frame stack (the walk's OWN frame:
   GLIVE's journal carries own = [(1, fpos)]) with its flag cell FL in F's last word (F + 120: read by the release at
   0x8300c), and the frame slots: 16(sp) and 24(sp) = F (the release's tests), 80(sp) = a0 at the entry (the id, as
   the register holds it). *)
Definition g_saved (cx : gcx) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
forall i, (i < 13)%nat ->
val_mem SEGS (arm W1 m1) (gsp1 cx + 120 + 8 * Z.of_nat i) 8 (bv_unsigned (getr (gxregs cx) (nth i RIG_SAVED 0%bv))).
Definition g_frame (cx : gcx) (fpos F FL : Z) (ly1 : alayout) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
frame_addr ly1 1 fpos = F /\ flag_addr ly1 1 fpos = FL /\
val_mem SEGS (arm W1 m1) (F + 120) 8 FL /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 16) 8 F /\ val_mem SEGS (arm W1 m1) (gsp1 cx + 24) 8 F /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 80) 8 (bv_unsigned (getr (gxregs cx) 10)) /\
g_saved cx W1 m1.
(* the loop's frame slots (0x82d5c, 0x82d84-0x82d94): 40(sp) = g_src's register image, 48(sp) = F's shadow,
   56(sp) = "param_gesture" (.str.5, A_OBJ 21), 64(sp) = the format (.str.8, A_OBJ 20), 72(sp) = g_nsrc's image *)
Definition g_lslots (cx : gcx) (F : Z) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
val_mem SEGS (arm W1 m1) (gsp1 cx + 40) 8 (rg_src RG + RIG_HI_SRC) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 48) 8 (shadow_addr F) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 56) 8 (VAL (A_OBJ 21)) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 64) 8 (VAL (A_OBJ 20)) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 72) 8 (rg_nsrc RG + RIG_HI_NSRC).

(* The registers every cut after the prologue holds: sp, gp, tp, s0 = the entry sp, s1 = sp, s2 = the shadow
   offset (ld from the GOT at 0x82c88). *)
Definition gregs_base (cx : gcx) (regs1 : bvmap 5 word) : Prop :=
spZ regs1 = gsp1 cx /\
getr regs1 3 = getr (gxregs cx) 3 /\ getr regs1 4 = getr (gxregs cx) 4 /\
getr regs1 8 = w64 (gsp0 cx) /\ getr regs1 9 = w64 (gsp1 cx) /\
getr regs1 18 = w64 SHADOW_OFF.

(* ---- What holds while the lock is held: the journal from the entry (at G_RIG, RIG_STK_x, rig_fp; from the entry's head
   set gxHp to the cut's Hp1) owning the fake frame (1, fpos), the .rodata view, the presence of image bytes, the
   frame and g_lock held. ---- *)
Definition GLIVE (cx : gcx) (F FL : Z) (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte)
(md1 : Model) (k1 : Z) : Prop :=
exists fpos Hp1,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 /\
rom_view SEGS W1 m1 /\ apres_kept B (gxW cx) (gxmem cx) W1 m1 /\
g_frame cx fpos F FL ly1 W1 m1 /\
alock_at RG W1 m1 true.

(* The meter: `spent` charged so far, tl still to come (W_drain_cx.v dbud); and the room round's two facts over tl
   (W_drain_cx_x.v dbud_x's form): the room at the cut's allocator state for MT_rk's count of the requests still owed
   on top of the entry's budget gxkr, and the live counts at the cut plus rig_pk's shape over those requests (their
   own peak count tr_peakP plus 3, the largest premise constant of an inner callee: gesture_end's ge_pk; drain's
   dr_pk is its trace's peak plus 2, W_contract_x.v :309-312). *)
Definition gbud (cx : gcx) (ly1 : alayout) (S1 : astate) (spent : Z) (tl : list (RelayRunT.rev YO0i.sptr)) : Prop :=
mo_le MT (gxS cx) S1 spent /\ 0 <= spent /\
spent + tr_cost MT tl <= tr_cost MT (gtr cx) /\
blocks_bytes S1 + tr_peak tl <= LIVE_MAX /\
tr_max tl < MMAX /\
rp_RM RP S1 (Z.to_nat (tr_cost MT_rk tl) + gxkr cx) /\
cnt_ok_pk RP (fun P => (Z.to_nat (ReplyCnt.tr_peakP P tl) + 3)%nat) (ablocks B ly1 S1).

(* The harness sources of the entries done, as rig_post states them. *)
Definition gdone_srcs (ps : list (rentry * (hsrc * nat))) (qd : list (rentry * hsrc)) : list (Z * Z) :=
concat (map (fun p => if re_eof (fst (fst p)) =? 0 then asrc_blks (snd (snd p)) else []) (combine ps qd)).

(* GOUT i: entries 0 .. i-1 done (qd: each with its harness source after), the stream at (c2, O2, cap2, out2);
   entries i .. as at the entry, with drain's source facts at the current state. *)
Definition GOUT (cx : gcx) (i : nat) (qd : list (rentry * hsrc)) (c2 : ctl) (O2 : list byte) (cap2 out2 : Z)
(spent : Z) (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
(i <= length (gxes cx))%nat /\ length qd = i /\
rig_rel (gpre cx) (gxmx cx) (gxc cx) (gxO cx) (gxcap cx) (firstn i (gps cx)) qd c2 O2 cap2 /\
arelay_at B RG ly1 S1 W1 m1 (gxG0 cx) (map fst qd ++ skipn i (gxes cx)) /\
aout_at B RG ly1 S1 W1 m1 c2 O2 (gxmx cx) (Z.of_nat (length O2)) cap2 out2 /\
(forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
   asrc_at B ly1 S1 W1 m1 (gslot cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) /\
Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly1 S1 W1 m1 (fst p) (fst (snd p)) (snd (snd p)))
  (skipn i (gps cx)) /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
   (forall j, In j (rig_slots (firstn i (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
   abyte_kept (gxW cx) (gxmem cx) W1 m1 a) /\
Permutation (ablocks B ly1 S1)
  ((gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ skipn i (gxes cx))) ++
   gdone_srcs (firstn i (gps cx)) qd ++ rig_srcs (skipn i (gps cx)) ++ aout_blks cap2 out2 ++ gxrest cx) /\
gbud cx ly1 S1 spent (grest cx i (Z.of_nat (length O2)) cap2).

(* What drain leaves of entry e (at stream (cB, OB, capB)) and its source h: e1, h1, the stream (c1, O1, cap1); the
   let-bindings of W_contract.v rig_rel, named. *)
Definition gdrained (cx : gcx) (cB : ctl) (OB : list byte) (capB : Z) (e : rentry) (h : hsrc)
(e1 : rentry) (h1 : hsrc) (ev : Z) (LB : list byte) (c1 : ctl) (O1 : list byte) (cap1 : Z) : Prop :=
let open := re_eof e =? 0 in
let no := Z.of_nat (length OB) in
let live := open && dr_live cB h in
c1 = (if open then dr_ctl cB h ev else cB) /\
O1 = (if live then OB ++ LB else OB) /\
cap1 = (if live then drain_b_c.ds_ocap (dr_fin cB (gxmx cx) no capB e h) else capB) /\
(if open then dr_rel cB (gxmx cx) no capB e h e1 h1 LB else e1 = e /\ h1 = h).

(* GIN: inside entry i (i < |es|).  Entries 0 .. i-1 done (qd, stream (cB, OB, capB): GOUT i's rig_rel); entry i
   drained (gdrained: e1, h1, the stream (c1, O1, cap1)); of its held keys, Ed ended so far, ks held now (the table's
   entry i is entry_keys e1 ks), the stream after Ed at (c2, O2, cap2, out2); geik's run from index n over ks (fuel f)
   ends what is left.  |ks| = n + S r: every KEY step lowers r by one (a pass raises n, an end shortens ks), which is
   the inner loop's measure.  The prefix and its zero shadow are in the fake frame. *)
Definition GIN (cx : gcx) (i n r : nat) (F : Z) (qd : list (rentry * hsrc)) (cB : ctl) (OB : list byte) (capB : Z)
(e1 : rentry) (h1 : hsrc) (ev : Z) (LB : list byte) (c1 : ctl) (O1 : list byte) (cap1 : Z)
(ks Ed : list (Z * list byte * list byte)) (f : nat) (c2 : ctl) (O2 : list byte) (cap2 out2 : Z)
(spent : Z) (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
let e := gnth cx i in
let h := fst (ghj cx i) in
let open := re_eof e =? 0 in
let Er := fst (geik_loop f (gpre cx) n ks) in
(i < length (gxes cx))%nat /\ length qd = i /\
rig_rel (gpre cx) (gxmx cx) (gxc cx) (gxO cx) (gxcap cx) (firstn i (gps cx)) qd cB OB capB /\
gdrained cx cB OB capB e h e1 h1 ev LB c1 O1 cap1 /\
sl_sends (gxmx cx) c1 O1 cap1 (ge_bytes Ed) = (c2, O2, cap2) /\
length ks = (n + S r)%nat /\ (length ks - n <= f)%nat /\
geik (gpre cx) (re_keys e1) = (Ed ++ Er, snd (geik_loop f (gpre cx) n ks)) /\
arelay_at B RG ly1 S1 W1 m1 (gxG0 cx) (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx)) /\
aout_at B RG ly1 S1 W1 m1 c2 O2 (gxmx cx) (Z.of_nat (length O2)) cap2 out2 /\
(forall i', (i' < i)%nat -> re_eof (gnth cx i') = 0 ->
   asrc_at B ly1 S1 W1 m1 (gslot cx i') (snd (nth i' qd (relay_remove_b_c.no_entry, fst relay_instance_gone_b_c.no_hj)))) /\
(open = true -> asrc_at B ly1 S1 W1 m1 (gslot cx i) h1) /\
Forall (fun p => re_eof (fst p) = 0 -> dr_src_ok B RG ly1 S1 W1 m1 (fst p) (fst (snd p)) (snd (snd p)))
  (skipn (S i) (gps cx)) /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
   (forall j, In j (rig_slots (firstn (S i) (gps cx))) -> ~ (rg_s RG + ASRC * Z.of_nat j <= a < rg_s RG + ASRC * Z.of_nat j + ASRC)) ->
   abyte_kept (gxW cx) (gxmem cx) W1 m1 a) /\
Permutation (ablocks B ly1 S1)
  ((gxG0 cx, ATABLE) :: concat (map aentry_blks (map fst qd ++ entry_keys e1 ks :: skipn (S i) (gxes cx))) ++
   gdone_srcs (firstn i (gps cx)) qd ++ (if open then asrc_blks h1 else []) ++ rig_srcs (skipn (S i) (gps cx)) ++
   aout_blks cap2 out2 ++ gxrest cx) /\
garr8 SEGS (arm W1 m1) (F + 32) (gpre cx ++ [0]) /\
garr8 SEGS (arm W1 m1) (shadow_addr F + 4) [0; 0; 0; 0; 0; 0] /\
(let '(_, O3, cap3) := sl_sends (gxmx cx) c2 O2 cap2 (ge_bytes Er) in
 gbud cx ly1 S1 spent (gkrest cx (Z.of_nat (length O2)) cap2 Er ++ grest cx (S i) (Z.of_nat (length O3)) cap3)).

(* ---- The cut predicates. ---- *)

(* RGO i (0x82d98): the outer loop's head at entry i < |es|.  s4 = F + 32 (the prefix buffer), s5 = F's shadow,
   s6 = g_src's register image, a4 = i. *)
Definition RGO (cx : gcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd c2 O2 cap2 out2 spent,
c1 = cfg_at SEGS (BASE + A_rig_outer) regs1 m1 md1 /\
gregs_base cx regs1 /\
getr regs1 20 = w64 (F + 32) /\ getr regs1 21 = w64 (shadow_addr F) /\
getr regs1 22 = w64 (rg_src RG + RIG_HI_SRC) /\ getr regs1 14 = w64 (Z.of_nat i) /\
(i < length (gxes cx))%nat /\
GLIVE cx F FL ly1 S1 W1 m1 md1 k1 /\ g_lslots cx F W1 m1 /\
GOUT cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1.

(* RGI i n r (0x82e50): the inner loop's head at index n of entry i (SA = g_src + 56 i), nheld = n + S r.  s3 = 8 n,
   s4 = F + 32, s5 = n, s7 = &s->nheld (SA + 48) and s6 its shadow address, s8 = |prefix| (strlen's result),
   s9 = &s->held (SA + 40) and s11 its shadow address; 32(sp) = ((SA + 48) & 7) + 3 (0x82e48), 88(sp) = i
   (0x82dc0). *)
Definition RGI (cx : gcx) (i n r : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd cB OB capB e1 h1 ev LB c2' O1 cap1 ks Ed f c2 O2 cap2 out2 spent,
c1 = cfg_at SEGS (BASE + A_rig_inner) regs1 m1 md1 /\
gregs_base cx regs1 /\
getr regs1 19 = w64 (8 * Z.of_nat n) /\ getr regs1 20 = w64 (F + 32) /\ getr regs1 21 = w64 (Z.of_nat n) /\
getr regs1 23 = w64 (gSA cx i + 48) /\ getr regs1 22 = w64 (SHADOW_OFF + (gSA cx i + 48) / 8) /\
getr regs1 24 = w64 (Z.of_nat (length (gpre cx))) /\
getr regs1 25 = w64 (gSA cx i + 40) /\ getr regs1 27 = w64 (SHADOW_OFF + (gSA cx i + 40) / 8) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 32) 8 ((gSA cx i + 48) mod 8 + 3) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 88) 8 (Z.of_nat i) /\
GLIVE cx F FL ly1 S1 W1 m1 md1 k1 /\ g_lslots cx F W1 m1 /\
GIN cx i n r F qd cB OB capB e1 h1 ev LB c2' O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1.

(* RGE i (0x82f44): entry i done (GOUT (S i)).  s4 = F + 32; 88(sp) = i. *)
Definition RGE (cx : gcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd c2 O2 cap2 out2 spent,
c1 = cfg_at SEGS (BASE + A_rig_step) regs1 m1 md1 /\
gregs_base cx regs1 /\ getr regs1 20 = w64 (F + 32) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 88) 8 (Z.of_nat i) /\
(i < length (gxes cx))%nat /\
GLIVE cx F FL ly1 S1 W1 m1 md1 k1 /\ g_lslots cx F W1 m1 /\
GOUT cx (S i) qd c2 O2 cap2 out2 spent ly1 S1 W1 m1.

(* RGU (0x82fa4): every entry done (GOUT |es|; the empty table included).  s5 = F's shadow. *)
Definition RGU (cx : gcx) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd c2 O2 cap2 out2 spent,
c1 = cfg_at SEGS (BASE + A_rig_unlock) regs1 m1 md1 /\
gregs_base cx regs1 /\ getr regs1 21 = w64 (shadow_addr F) /\
GLIVE cx F FL ly1 S1 W1 m1 md1 k1 /\
GOUT cx (length (gxes cx)) qd c2 O2 cap2 out2 spent ly1 S1 W1 m1.

(* ---- The segment statements. ---- *)

(* PRO: the prologue 0x82c2c .. 0x82d48 (thirteen saves, the id at 80(sp), the uar test, __asan_stack_malloc_1 (128)
   0x82c98, the frame header and its shadow poison), pthread_mutex_lock (g_lock) 0x82d54, g_nsrc <= 0 0x82d64
   (-> RGU) and the loop's setup 0x82d68-0x82d94 (-> RGO 0). *)
Definition rig_pro_stmt : Prop :=
forall cx,
GBASE cx ->
(forall W2 c2, RGO cx 0 W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
(forall W2 c2, RGU cx W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
SRr SEGS (gxW cx) (cfg_at SEGS A_rig_entryP (gxregs cx) (gxmem cx) (gxmd cx)) (gPOST cx).

(* TOP: RGO i 0x82d98 -> the shadow check of s->eof (0x82dac-0x82dbc; 0x82f80-0x82f8c, report 0x830d4 NOT taken),
   88(sp) = i, drain (s) when s->eof = 0 (0x82dcc), F's shadow bytes 4 .. 9 = 0 (the 48-byte buffer at F + 32,
   0x82dd4-0x82dec), snprintf (F + 32, 48, "%s %d ", "param_gesture", id) (0x82e04), strlen (F + 32) (0x82e0c),
   the shadow check of s->nheld (0x82e10-0x82e24; 0x82f90-0x82f98, report 0x82fa0 NOT taken) and the nheld test
   0x82e2c: nheld > 0 -> the inner loop's setup 0x82e30-0x82e48 -> RGI i 0 r (nheld = S r); nheld <= 0 -> RGE i. *)
Definition rig_top_stmt : Prop :=
forall cx i W1 c1,
GBASE cx -> RGO cx i W1 c1 ->
(forall r W2 c2, RGI cx i 0 r W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
(forall W2 c2, RGE cx i W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
SRr SEGS W1 c1 (gPOST cx).

(* KEY: RGI i n r 0x82e50 -> the shadow checks of s->held and held[n] (0x82e50-0x82e6c; reports 0x8309c / 0x830a0
   NOT taken), key = held[n], strncmp (key, prefix, |prefix|) (0x82e80):
   - nonzero (the key lacks the prefix, 0x82f20-0x82f34): nheld reread (its shadow check, 0x82f38-0x82f3c, report
     0x830cc NOT taken), n + 1 < nheld (r = S r') -> RGI i (S n) r', else (r = 0) -> RGE i;
   - zero: gesture_end (key) (0x82e8c), the shadow checks again (0x82e90-0x82eac), free (key) (0x82eb4), nheld -= 1
     (0x82ed4), held[n] = held[nheld] (0x82f08, its checks 0x82ee0-0x82f00; reports 0x830a4-0x830c0 NOT taken):
     n < nheld (r = S r') -> RGI i n r' (the last key moved into slot n), else (r = 0) -> RGE i. *)
Definition rig_key_stmt : Prop :=
forall cx i n r W1 c1,
GBASE cx -> GCTX cx -> RGI cx i n r W1 c1 ->
(forall r' W2 c2, r = S r' -> RGI cx i (S n) r' W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
(forall r' W2 c2, r = S r' -> RGI cx i n r' W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
(forall W2 c2, RGE cx i W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
SRr SEGS W1 c1 (gPOST cx).

(* KEYS: the inner loop, by induction on r. *)
Definition rig_keys_stmt : Prop :=
rig_key_stmt ->
forall cx i n r W1 c1,
GBASE cx -> GCTX cx -> RGI cx i n r W1 c1 ->
(forall W2 c2, RGE cx i W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
SRr SEGS W1 c1 (gPOST cx).

(* STEP: RGE i 0x82f44 -> F's shadow bytes 4 .. 9 = 0xf8 again (0x82f48-0x82f60), g_nsrc reread, i + 1 < g_nsrc
   -> RGO (S i), else -> RGU.  No call. *)
Definition rig_step_stmt : Prop :=
forall cx i W1 c1,
GBASE cx -> RGE cx i W1 c1 ->
(forall W2 c2, RGO cx (S i) W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
(forall W2 c2, RGU cx W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
SRr SEGS W1 c1 (gPOST cx).

(* OUTER: the outer loop, by induction on |es| - i (KEY is passed to KEYS). *)
Definition rig_outer_stmt : Prop :=
rig_top_stmt -> rig_key_stmt -> rig_keys_stmt -> rig_step_stmt ->
forall cx i W1 c1,
GBASE cx -> GCTX cx -> RGO cx i W1 c1 ->
(forall W2 c2, RGU cx W2 c2 -> SRr SEGS W2 c2 (gPOST cx)) ->
SRr SEGS W1 c1 (gPOST cx).

(* TAIL: RGU 0x82fa4 -> pthread_mutex_unlock (g_lock) (0x82fac), the frame's release 0x82fb0-0x83054 (retired
   magic, shadow 0xf5, *flag = 0) and the epilogue -> rig_post. *)
Definition rig_tail_stmt : Prop :=
forall cx W1 c1,
GBASE cx -> RGU cx W1 c1 ->
SRr SEGS W1 c1 (gPOST cx).

(* The walk: the segments give relay_instance_gone's generic contract. *)
Definition rig_all_stmt : Prop :=
rig_pro_stmt -> rig_top_stmt -> rig_key_stmt -> rig_step_stmt -> rig_keys_stmt -> rig_outer_stmt -> rig_tail_stmt ->
rig_spec_x B PST ARx MT RP MMAX RG CTX_AFREE A_rig_entryP.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): this Section's texts at a world relation R.  Each <name>_xR below is <name>
   with the journal ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, rig_post_x / rig_spec_x -> a Theorem Labs lane's
   rig_post_xR / rig_spec_xR (W_contract_xR_relay.v, R right after ARx), and every carrier or statement it names -> its
   R twin; every other token is the strict text's.  At R := wle each is its strict twin by conversion.  The Section's
   hypotheses add, for the segment walks that copy them: the R laws, the free rule at R (afree_cf_rule_c_xR, with its
   call-boundary fact RO read off ARx) and the two callees' R specs (W_contract_xR.v dr_spec_xR / ge_spec_xR).
   GBASE, GCTX, GOUT, GIN, gbud, g_frame, g_lslots, gregs_base name no journal and no step relation and are shared. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Hypothesis DRAIN_R : dr_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GE_R : ge_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gesture_end).
(* W_relay_instance_gone_cx.v:322 rig_lift_DR at R *)
Lemma rig_lift_DR_xR : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_DR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_xR; [exact rig_G_DR_RIG | eassumption]. Qed.
(* W_relay_instance_gone_cx.v:326 rig_lift_SL at R *)
Lemma rig_lift_SL_xR : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_SL B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_xR; [exact rig_G_SL_RIG | eassumption]. Qed.
(* W_relay_instance_gone_cx.v:360 gPOST at R *)
Definition gPOST_xR (cx : gcx) : world SEGS -> config -> Prop :=
rig_post_xR B PST ARx R MT RP RG (gxregs cx) (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx)
  (gxG0 cx) (gxID cx) (gxes cx) (gxhs cx) (gxc cx) (gxO cx) (gxmx cx) (gxcap cx) (gxout cx) (gxkr cx).
(* W_relay_instance_gone_cx.v:427 GLIVE at R *)
Definition GLIVE_xR (cx : gcx) (F FL : Z) (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte)
(md1 : Model) (k1 : Z) : Prop :=
exists fpos Hp1,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 /\
rom_view SEGS W1 m1 /\ apres_kept B (gxW cx) (gxmem cx) W1 m1 /\
g_frame cx fpos F FL ly1 W1 m1 /\
alock_at RG W1 m1 true.
(* W_relay_instance_gone_cx.v:527 RGO at R *)
Definition RGO_xR (cx : gcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd c2 O2 cap2 out2 spent,
c1 = cfg_at SEGS (BASE + A_rig_outer) regs1 m1 md1 /\
gregs_base cx regs1 /\
getr regs1 20 = w64 (F + 32) /\ getr regs1 21 = w64 (shadow_addr F) /\
getr regs1 22 = w64 (rg_src RG + RIG_HI_SRC) /\ getr regs1 14 = w64 (Z.of_nat i) /\
(i < length (gxes cx))%nat /\
GLIVE_xR cx F FL ly1 S1 W1 m1 md1 k1 /\ g_lslots cx F W1 m1 /\
GOUT cx i qd c2 O2 cap2 out2 spent ly1 S1 W1 m1.
(* W_relay_instance_gone_cx.v:541 RGI at R *)
Definition RGI_xR (cx : gcx) (i n r : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd cB OB capB e1 h1 ev LB c2' O1 cap1 ks Ed f c2 O2 cap2 out2 spent,
c1 = cfg_at SEGS (BASE + A_rig_inner) regs1 m1 md1 /\
gregs_base cx regs1 /\
getr regs1 19 = w64 (8 * Z.of_nat n) /\ getr regs1 20 = w64 (F + 32) /\ getr regs1 21 = w64 (Z.of_nat n) /\
getr regs1 23 = w64 (gSA cx i + 48) /\ getr regs1 22 = w64 (SHADOW_OFF + (gSA cx i + 48) / 8) /\
getr regs1 24 = w64 (Z.of_nat (length (gpre cx))) /\
getr regs1 25 = w64 (gSA cx i + 40) /\ getr regs1 27 = w64 (SHADOW_OFF + (gSA cx i + 40) / 8) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 32) 8 ((gSA cx i + 48) mod 8 + 3) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 88) 8 (Z.of_nat i) /\
GLIVE_xR cx F FL ly1 S1 W1 m1 md1 k1 /\ g_lslots cx F W1 m1 /\
GIN cx i n r F qd cB OB capB e1 h1 ev LB c2' O1 cap1 ks Ed f c2 O2 cap2 out2 spent ly1 S1 W1 m1.
(* W_relay_instance_gone_cx.v:555 RGE at R *)
Definition RGE_xR (cx : gcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd c2 O2 cap2 out2 spent,
c1 = cfg_at SEGS (BASE + A_rig_step) regs1 m1 md1 /\
gregs_base cx regs1 /\ getr regs1 20 = w64 (F + 32) /\
val_mem SEGS (arm W1 m1) (gsp1 cx + 88) 8 (Z.of_nat i) /\
(i < length (gxes cx))%nat /\
GLIVE_xR cx F FL ly1 S1 W1 m1 md1 k1 /\ g_lslots cx F W1 m1 /\
GOUT cx (S i) qd c2 O2 cap2 out2 spent ly1 S1 W1 m1.
(* W_relay_instance_gone_cx.v:565 RGU at R *)
Definition RGU_xR (cx : gcx) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 F FL qd c2 O2 cap2 out2 spent,
c1 = cfg_at SEGS (BASE + A_rig_unlock) regs1 m1 md1 /\
gregs_base cx regs1 /\ getr regs1 21 = w64 (shadow_addr F) /\
GLIVE_xR cx F FL ly1 S1 W1 m1 md1 k1 /\
GOUT cx (length (gxes cx)) qd c2 O2 cap2 out2 spent ly1 S1 W1 m1.
(* W_relay_instance_gone_cx.v:577 rig_pro_stmt at R *)
Definition rig_pro_stmt_xR : Prop :=
forall cx,
GBASE cx ->
(forall W2 c2, RGO_xR cx 0 W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
(forall W2 c2, RGU_xR cx W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
SRrG SEGS R (gxW cx) (cfg_at SEGS A_rig_entryP (gxregs cx) (gxmem cx) (gxmd cx)) (gPOST_xR cx).
(* W_relay_instance_gone_cx.v:589 rig_top_stmt at R *)
Definition rig_top_stmt_xR : Prop :=
forall cx i W1 c1,
GBASE cx -> RGO_xR cx i W1 c1 ->
(forall r W2 c2, RGI_xR cx i 0 r W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
(forall W2 c2, RGE_xR cx i W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
SRrG SEGS R W1 c1 (gPOST_xR cx).
(* W_relay_instance_gone_cx.v:603 rig_key_stmt at R *)
Definition rig_key_stmt_xR : Prop :=
forall cx i n r W1 c1,
GBASE cx -> GCTX cx -> RGI_xR cx i n r W1 c1 ->
(forall r' W2 c2, r = S r' -> RGI_xR cx i (S n) r' W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
(forall r' W2 c2, r = S r' -> RGI_xR cx i n r' W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
(forall W2 c2, RGE_xR cx i W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
SRrG SEGS R W1 c1 (gPOST_xR cx).
(* W_relay_instance_gone_cx.v:612 rig_keys_stmt at R *)
Definition rig_keys_stmt_xR : Prop :=
rig_key_stmt_xR ->
forall cx i n r W1 c1,
GBASE cx -> GCTX cx -> RGI_xR cx i n r W1 c1 ->
(forall W2 c2, RGE_xR cx i W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
SRrG SEGS R W1 c1 (gPOST_xR cx).
(* W_relay_instance_gone_cx.v:621 rig_step_stmt at R *)
Definition rig_step_stmt_xR : Prop :=
forall cx i W1 c1,
GBASE cx -> RGE_xR cx i W1 c1 ->
(forall W2 c2, RGO_xR cx (S i) W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
(forall W2 c2, RGU_xR cx W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
SRrG SEGS R W1 c1 (gPOST_xR cx).
(* W_relay_instance_gone_cx.v:629 rig_outer_stmt at R *)
Definition rig_outer_stmt_xR : Prop :=
rig_top_stmt_xR -> rig_key_stmt_xR -> rig_keys_stmt_xR -> rig_step_stmt_xR ->
forall cx i W1 c1,
GBASE cx -> GCTX cx -> RGO_xR cx i W1 c1 ->
(forall W2 c2, RGU_xR cx W2 c2 -> SRrG SEGS R W2 c2 (gPOST_xR cx)) ->
SRrG SEGS R W1 c1 (gPOST_xR cx).
(* W_relay_instance_gone_cx.v:638 rig_tail_stmt at R *)
Definition rig_tail_stmt_xR : Prop :=
forall cx W1 c1,
GBASE cx -> RGU_xR cx W1 c1 ->
SRrG SEGS R W1 c1 (gPOST_xR cx).
(* W_relay_instance_gone_cx.v:644 rig_all_stmt at R *)
Definition rig_all_stmt_xR : Prop :=
rig_pro_stmt_xR -> rig_top_stmt_xR -> rig_key_stmt_xR -> rig_step_stmt_xR -> rig_keys_stmt_xR -> rig_outer_stmt_xR -> rig_tail_stmt_xR ->
rig_spec_xR B PST ARx R MT RP MMAX RG CTX_AFREE A_rig_entryP.
End wR.
(* at R := wle the R texts are the strict ones (conversion) *)
Lemma gPOST_wle : gPOST = gPOST_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma GLIVE_wle : GLIVE = GLIVE_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma RGO_wle : RGO = RGO_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma RGI_wle : RGI = RGI_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma RGE_wle : RGE = RGE_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma RGU_wle : RGU = RGU_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rig_pro_stmt_wle : rig_pro_stmt = rig_pro_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rig_top_stmt_wle : rig_top_stmt = rig_top_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rig_key_stmt_wle : rig_key_stmt = rig_key_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rig_keys_stmt_wle : rig_keys_stmt = rig_keys_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rig_step_stmt_wle : rig_step_stmt = rig_step_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rig_outer_stmt_wle : rig_outer_stmt = rig_outer_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rig_tail_stmt_wle : rig_tail_stmt = rig_tail_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rig_all_stmt_wle : rig_all_stmt = rig_all_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
End c.
End b.
End a.
