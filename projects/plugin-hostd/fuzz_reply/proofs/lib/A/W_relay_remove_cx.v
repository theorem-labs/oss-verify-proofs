(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the SEGMENT INTERFACE of the ASan walk of fuzz_reply's relay_remove
   (fuzz_reply.asan 0x83de4 .. 0x840b0, 179 instructions), in the form of lane W7's lib/A/W_drain_cx.v (itself the
   form of the cgif walks proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v and ACfj.v: segments joined at cut points).
   Nothing is proved here: the file fixes the Section hypotheses, the entry context, the cut predicates over
   concrete machine states and the statement of every segment, so that the segments are proved in parallel.

   relay_remove (fd) is relay.c:453-468: for fd >= 0, under g_lock, the entry of fd, if any, is drained when open,
   its held keys are ended (gestures_end), its buffer freed and the last entry moved into its slot; then g_lock is
   released and, g_wake[1] being -1, nothing is written to the wake pipe.  Its contract is W_contract.v Section s6:
   rr_spec B MT MMAX RG (BASE + AF_fr_relay_remove), post rr_post.  The fake frame is class 0 (64 bytes).

   CUT POINTS
     RRL k   0x83f14  the scan loop's head at index k (s8 = 56 k), the lock held, nothing changed yet;
     RRM i   0x83f48  the scan found fd at index i (a0 = g_src + 56 i), nothing changed yet;
     RRU oi  0x83fc4  the unlock tail: oi = None, no entry has fd and nothing changed; oi = Some i, entry i was
                      drained (when open), its keys ended, its buffer freed and the last entry moved into slot i.
   and the two ends: the entry 0x83de4 (rr_pro_stmt, which also walks the whole fd < 0 arm and the empty-table
   test 0x83ef0 -> RRU None) and the return (rr_tail_stmt, from RRU through the unlock, the wake test 0x83fe8, the
   fake frame's release 0x84000 and the epilogue).

   SEGMENTS
     PRO    0x83de4 -> RRL 0 | RRU None | rr_post (fd < 0)      prologue, __asan_stack_malloc_0, the lock
     SCAN   RRL k -> RRL (S k) | RRM k | RRU None              one step of the scan loop: NO CALLS, NO STORES
     SCANS  the scan loop by induction on |es| - k              composition of SCAN
     MATCH  RRM i -> RRU (Some i)                               drain, gestures_end, free, __asan_memcpy
     TAIL   RRU oi -> rr_post                                   unlock, the wake test, the frame release, ret
   Every segment concludes `SRr SEGS W1 c1 (RPOST cx)` and takes its continuations in the same form, so the
   composition (rr_all_stmt) is plain application.

   The scan reads only g_src's table: the shadow byte of each entry's fd field (an ASan check whose report call
   0x83f44 must be proved not taken) and the fd field itself.  It writes nothing, so every cut predicate's memory
   part (RHELD) is the SAME at RRL k, RRL (S k), RRM k and RRU None.

   STATEMENT GAPS (facts the machine has that the first text lacked; each found at a prover's unprovable goal, each
   fixed by stating the fact and discharging it at PB_fr / fr_globals by vm_compute, never by weakening):
   - RLIVE own = [] (RigTail, the flag store / stack_malloc post): the fake frame read as an ENTRY frame; now
     own = [(0, fpos)] (6322e1c462a).
   - HH59 / HH60 (RrPro, rregs_held / RRL's s7 / s9): the abstract PI leaves VAL (A_HI 59 / 60) - VAL (A_OBJ 7 / 8)
     open (W_rebase.v:7-15) (d700f304923).
   - key slack (RrPro / RrTail, arelay_at after the frame stores): W_rep.v bounded a key's slack only from below, so a
     slack byte could sit on F or its shadow; W8's ruling-(A) W_rep.v removes slack (ead5de7cc24).
   - HRGP (RrTail / RigTail, aout_at after the lock / unlock): counter-case rg_send_max = rg_lock + 4 with mx = 16;
     HRGI (RrTail): g_capsrc = F + 32 would make the final g_capsrc 0; HV4 (RrTail, the wake load 0x83fe0);
     rregs_base s10 / s11 (RrTail, aregs_preserved: relay_remove never saves them) (eab4b19b11c).
   - HROMO and HRGI's not-owned-static half (RigPro, rom_view and aout_at across __asan_stack_malloc_*, which keeps
     only bytes that are not aowned) (cd96cd63ec8).
   - the MATCH prep (PREP.md (sha256 02e2eed258c7; internal record) (d)), rulings:
     Q1 METER: rr_tr omitted free (NULL) (the held array of an entry with no held keys; s->buf of an entry with
       cap 0) while gse_cost [] = mo_free and afree_null_cf_rule charge mo_free; W_contract.v rr_tr now counts both
       frees always (AFREEN added here for the buf free).
     Q9: rr_tr's drain prefix IS dr_spec's dr_tr (drain's own liveness), one description of the trace.
     Q2 ROOM: a send that does not grow g_out leaves sl_cap = cap, which tr_max / tr_alloc do not bound; rr_spec
       (and RBASE) took cap < MMAX and blocks_bytes + tr_alloc + 4 * max cap tr_max <= LIVE_MAX (1744b876fbd).  C3
       (475b8a2b569) removed both: the callees' room premises (dr_spec, ge_room, gse_room) are stated over their
       traces' peak (W_contract.v tr_peak), so rr_spec asks only tr_max tr < MMAX and blocks_bytes S + tr_peak tr <=
       LIVE_MAX, and RBASE, RHELD and W_rr_match_cx.v rmbud carry the peak form (the kit is W_tr_peak.v).
     Q3: gse_spec's END5 literal: HEND5, W4's text.  Q4: covered by HRGP (lock, nsrc, src, capsrc, g_s, the
       G_SL cells, errno).  Q6: the callees' journal lifts rr_lift_DR / rr_lift_SL are in this file.

   - HEND5L (k3's RigKey end arm, GE / GSE's garr8 (VAL A_lit_end5) (bzs END5)): HEND5 gave the literal's zero shadow
     and placement but not its BYTES; a walk that compares against or passes a literal needs all three (bytes, shadow,
     placement), and this is the unit's fifth gap of that class tonight.
   - HEND5 and glit_at's azs conjunct REMOVED (a Theorem Labs lane, six measurements): a zero-shadow premise over a string
     literal is FALSE for ASan globals (the literal's last granule is partial: " end\0" at 0x20f00 has shadow byte 5),
     so HEND5 (W4's text) and azs over "%s %d " / "param_gesture" could not be discharged.  ge_spec / gse_spec need
     only the bytes (HEND5L + rom_view); glit_at now carries W3's ashp (range_addressable over exactly [a, a + n) and
     the shadow hull).  Delete-and-rebuild check: no Qed piece used HEND5 or the azs conjunct.
   CONSUMER NOTE (W8's ARM_remove, LLVMFuzzerTestOneInput's call of relay_remove): since C3 (475b8a2b569) rr_spec's
   room premises at the call are `tr_max tr < MMAX` and `blocks_bytes S + tr_peak tr <= LIVE_MAX`, with
   tr = rr_tr c mx |O| cap FD es h, which counts both frees of the matched entry always; the two premises
   `cap < MMAX` and `blocks_bytes S + tr_alloc tr + 4 * Z.max cap (tr_max tr) <= LIVE_MAX` of 1744b876fbd are gone. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record)) in the room form
   (a Theorem Labs lane, lane RR_x): the segment interface over ANY allocator relation ARx with its laws.  Section c takes the
   generic relation (PST / ARx / hl / LAWS / HP0), the frame twins' hypotheses of W_frame_x.v (IMGC, BLKN, OWNLOW,
   WFx / WFL, SFREE, SMALLOC; the template is commit 3d17f490d56, lib/A/W_relay_finish_h.v Section c), the PST facts
   PSTR / PSTG (the program statics hold no ROM byte and none of HRGP's cells: what the journal's image clause carries)
   and every callee in its _x room form (dr_spec_x, gse_spec_x, afree_cf_rule_c_x / afree_null_cf_rule_c_x,
   alock_realizes_x / aunlock_realizes_x, aintrin_realizes_x / amemcpy_same_realizes_x).  The entry record rcx gains
   the ghost set rxHp (after rxS) and the room budget rxkr; RBASE is rr_spec_x's premises EXACTLY (afn_pre_x at
   RR_STK_x since W8's DRAIN_STK_x ruling, commit b9052387bcb; then the AR premises, then the room record:
   rp_RM RP S (Z.to_nat (tr_cost MT_rk tr) + kr) and cnt_ok_pk RP (rr_pk tr)), the post rPOST is rr_post_x.  The cut predicates' journal is ajournal_gx_x with the head set after each state, and they
   carry the room budget as they carry the meter: RHELD (RRL / RRM / RRU None) the whole budget
   rp_RM RP S1 (Z.to_nat (tr_cost MT_rk (rtr cx)) + kr) and the entry's count fact cnt_ok_pk RP (rr_pk (rtr cx)) at
   the current blocks; RDONE (RRU (Some i)) what is left after the last free, rp_RM RP S1 kr. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_journal W_sites W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_relay.
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

(* ---- The walk's program counters (listing slot = (addr - 0x822ec) / 4; AF_fr_relay_remove = 0x1af8). ---- *)
Definition A_rr_entry : Z := AF_fr_relay_remove.            (* 0x83de4, the entry *)
Definition A_rr_entryP : Z := BASE + A_rr_entry.
Definition A_rr_scan : Z := AF_fr_relay_remove + 0x130.     (* 0x83f14, the scan loop's head *)
Definition A_rr_match : Z := AF_fr_relay_remove + 0x164.    (* 0x83f48, fd found *)
Definition A_rr_unlock : Z := AF_fr_relay_remove + 0x1e0.   (* 0x83fc4, the unlock tail *)

(* The callee-saved registers in their frame slots 8(sp) (s9) .. 88(sp) (ra), sp = the entry sp - 96. *)
Definition RR_SAVED : list (bv 5) :=
[25%bv; 24%bv; 23%bv; 22%bv; 21%bv; 20%bv; 19%bv; 18%bv; 9%bv; 8%bv; 1%bv].

(* The register images of g_nsrc and g_src: s7 = auipc at 0x83ee8 (g_nsrc = s7 - 1864) and s9 = auipc at 0x83ef8
   (g_src = s9 - 1848). *)
Definition RR_HI_NSRC : Z := 1864.
Definition RR_HI_SRC : Z := 1848.

(* the relay's and the output's global cells and errno (HRGP's list): the cells the walk carries across its calls *)
Definition rr_gcells (B : asyms) (RG : rep_globals) : list (Z * Z) :=
[(rg_lock RG, rg_lock RG + 12); (rg_s RG, rg_s RG + 4 * ASRC); (rg_src RG, rg_src RG + 8);
 (rg_nsrc RG, rg_nsrc RG + 4); (rg_capsrc RG, rg_capsrc RG + 4); (rg_send_max RG, rg_send_max RG + 8);
 (rg_nout RG, rg_nout RG + 8); (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_dead RG, rg_send_dead RG + 1); (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_wake RG + 4, rg_wake RG + 8);
 (as_errno B, as_errno B + 4)].

(* ---- THE GENERIC WALK (route (b), step 3): relay_remove over any allocator relation ARx with its laws, stated as
   W_contract_x.rr_spec_x.  Beyond the AR walk's Section: PST / ARx / hl / LAWS (the generic relation), HP0 (no hidden
   head in any ARx state, a Theorem Labs lane's ruling), the frame twins' hypotheses (IMGC, BLKN, OWNLOW, WFx / WFL, SFREE,
   SMALLOC: W_frame_x.v, in place of the AR Section's ML / SMP), the room record RP, and the PST facts PSTR / PSTG.
   Every one is an instance fact that the instance supplies where RR_x is plugged (top_x); the AR re-derivation was
   deleted (W_relay_remove.v's header says why). ---- *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (W_journal_x.v Record roomp): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (one table for free and free(NULL): K0_SITES' CTX_AFREE) *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts'). ---- *)
(* the generic relation's laws and its empty head set (CONVERSION.md (sha256 1015972e02a9; internal record) 1.) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the frame twins' hypotheses (W_frame_x.v): the image cover IMGC (frm_off_imgP_x, blk_off_imgP_x), a live block's
   size non-negative (BLKN, W_kit_x.v), the owned-low law OWNLOW, the model invariant WFx with its law WFL and the two
   facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC) *)
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
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 0.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
Hypothesis HG : gx_ok SEGS B (G_RR B RG).
(* the register images of g_nsrc / g_src: the auipc's of 0x83ee8 (s7, listing A_HI 59) and 0x83ef8 (s9, A_HI 60).
   The abstract placement does not fix them against the objects (W_rebase.v:7-15); PB_fr discharges both by
   vm_compute, as W_send_line_cx.v's HH17 .. HH24. *)
Hypothesis HH59 : VAL (A_HI 59) = rg_nsrc RG + RR_HI_NSRC.
Hypothesis HH60 : VAL (A_HI 60) = rg_src RG + RR_HI_SRC.
(* g_wake[1], read at 0x83fe0 by PLdHi (A_OBJ 4) (W5's HV4, verbatim) *)
Hypothesis HV4 : VAL (A_OBJ 4) = rg_wake RG + 4.
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
   allocator's calls (W_journal.v ajournal_gx_rom_view) *)
Hypothesis HROMO : rom_out SEGS B (G_RR B RG).
Hypothesis MLAW : ameter_laws MT.
(* the live-state meter does not see the fake frame: its seat and its release are set_fs steps (W8's ruling, the
   lead's KF-COUNT #4: the ablocks form is false at the count meter) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* the runtime entries relay_remove calls, at their SIGMA pcs (W_sites.v / the donor's YG0d.v / W_journal.v) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMCPYS : amemcpy_same_realizes_x B ARx (SIGMA WS_asan_memcpy).
(* the program functions relay_remove calls (W7's drain, W4's gestures_end), by their published _x specs *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* free (s->buf) at 0x83f94 with s->buf = NULL (an entry with cap 0) *)
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* The program statics PST hold no byte the walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x) and no byte of the relay's / output's cells or
   errno (rr_gcells, HRGP's list).  At PST := [] both hold trivially (W_relay_finish_h.v's PSTR / PSTC form). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, Exists (fun r => fst r <= a < snd r) (rr_gcells B RG) -> ~ Exists (in_zr a) PST.

(* ---- The callees' journals, lifted to relay_remove's globals (a Theorem Labs lane's Q6): drain's at G_DR and gestures_end's
   at G_SL are journals at G_RR (W_journal.v ajournal_gx_G_mono), for every call-making segment. ---- *)
Lemma rr_G_DR_RR : forall a, inG (G_DR B RG) a -> inG (G_RR B RG) a.
Proof. intros a Ha. unfold G_RR, inG in *. apply Exists_cons_tl. apply Exists_cons_tl. exact Ha. Qed.
Lemma rr_G_SL_RR : forall a, inG (G_SL B RG) a -> inG (G_RR B RG) a.
Proof. intros a Ha. apply rr_G_DR_RR. unfold G_DR, inG in *. apply Exists_cons_tl. exact Ha. Qed.
Lemma rr_lift_DR : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_DR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_x; [exact rr_G_DR_RR | eassumption]. Qed.
Lemma rr_lift_SL : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_SL B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_x; [exact rr_G_SL_RR | eassumption]. Qed.
(* the room round: a count fact moves along a Permutation of the blocks *)
Lemma rr_cnt_perm : forall pk l l', Permutation l l' -> cnt_ok_pk RP pk l -> cnt_ok_pk RP pk l'.
Proof.
intros pk l l' HP HC. apply (cnt_ok_pk_mono RP pk pk l l'); [|exact HC].
intros P. rewrite (ReplyCnt.acnt_perm P _ _ HP). lia.
Qed.

(* ---- The entry context. ----
   One record for everything rr_spec_x quantifies over at the entry (the ghost set rxHp after rxS, the room budget
   rxkr last), so that every segment statement takes one argument and the cut predicates read the entry off it. *)
Record rcx : Type := mkRcx {
  rxregs : bvmap 5 word;
  rxly : alayout; rxS : astate; rxHp : list Z; rxW : world SEGS; rxmem : word -> option byte; rxmd : Model;
  rxch : list (Z * Z * Z);
  rxG0 : Z; rxFD : Z; rxes : list rentry; rxj : nat; rxh : hsrc;
  rxc : ctl; rxO : list byte; rxmx : Z; rxcap : Z; rxout : Z;
  rxrest : list (Z * Z); rxkr : nat }.

Definition rsp0 (cx : rcx) : Z := spZ (rxregs cx).
Definition rN (cx : rcx) : Z := Z.of_nat (length (rxes cx)).
Definition rFP (cx : rcx) : list (Z * Z) := rr_fp (rxG0 cx) (rxFD cx) (rxes cx) (rxh cx) (rxcap cx) (rxout cx).
Definition rtr (cx : rcx) := rr_tr (rxc cx) (rxmx cx) (Z.of_nat (length (rxO cx))) (rxcap cx) (rxFD cx) (rxes cx) (rxh cx).
Definition rnth (cx : rcx) (i : nat) : rentry := nth i (rxes cx) relay_remove_b_c.no_entry.
Definition rPOST (cx : rcx) : world SEGS -> config -> Prop :=
rr_post_x B PST ARx MT RP RG (rxregs cx) (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx)
  (rxG0 cx) (rxFD cx) (rxes cx) (rxj cx) (rxh cx) (rxc cx) (rxO cx) (rxmx cx) (rxcap cx) (rxout cx) (rxkr cx).

(* RBASE: exactly rr_spec_x's premises at the entry, with the Permutation's `rest` taken from the context, the room
   record (rp_RM at the trace's counting-meter cost plus kr, the count premise at rr_pk) last. *)
Definition RBASE (cx : rcx) : Prop :=
afn_pre_x SEGS B ARx RR_STK_x (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxregs cx) (rxmem cx) (rxmd cx) (rxch cx) /\
rsp0 cx mod 32 = 0 /\ count_cid 0 (frames (rxS cx)) < fs_frames 0 /\ rg_place B RG /\
getr (rxregs cx) 10 = w64 (rxFD cx) /\ - 2 ^ 31 <= rxFD cx < 2 ^ 31 /\
alock_at RG (rxW cx) (rxmem cx) false /\ awake_at RG (rxW cx) (rxmem cx) /\
arelay_at B RG (rxly cx) (rxS cx) (rxW cx) (rxmem cx) (rxG0 cx) (rxes cx) /\
aout_at B RG (rxly cx) (rxS cx) (rxW cx) (rxmem cx) (rxc cx) (rxO cx) (rxmx cx) (Z.of_nat (length (rxO cx)))
  (rxcap cx) (rxout cx) /\
rom_view SEGS (rxW cx) (rxmem cx) /\
(forall i, (i < length (rxes cx))%nat -> re_fd (rnth cx i) = rxFD cx -> re_eof (rnth cx i) = 0 ->
   dr_src_ok B RG (rxly cx) (rxS cx) (rxW cx) (rxmem cx) (rnth cx i) (rxh cx) (rxj cx)) /\
Permutation (ablocks B (rxly cx) (rxS cx))
  ((rxG0 cx, ATABLE) :: concat (map aentry_blks (rxes cx)) ++
   (if rr_drains (rxFD cx) (rxes cx) then asrc_blks (rxh cx) else []) ++ aout_blks (rxcap cx) (rxout cx) ++ rxrest cx) /\
tr_max (rtr cx) < MMAX /\ blocks_bytes (rxS cx) + tr_peak (rtr cx) <= LIVE_MAX /\
mo_ok MT (rxS cx) (tr_cost MT (rtr cx)) /\
rp_RM RP (rxS cx) (Z.to_nat (tr_cost MT_rk (rtr cx)) + rxkr cx) /\
cnt_ok_pk RP (rr_pk (rtr cx)) (ablocks B (rxly cx) (rxS cx)).

(* RCTX: rr_spec's caller-context premise at the entry (W_contract.v), read by MATCH's free at 0x83f94 (ra 0x83f98):
   the free's trace is 0x83f98, then this entry's return and chain (s0 = the entry sp is a frame pointer) *)
Definition RCTX (cx : rcx) : Prop :=
spZ (rxregs cx) + 16 < ly_top (rxly cx) /\ In (A_rr_entryP + 436 :: raZ (rxregs cx) :: spine (rxch cx)) CTX_AFREE.

(* ---- The frame. ----
   After the prologue: sp = the entry sp - 96 (the entry sp is 32-aligned, so `andi sp, sp, -32` keeps it),
   the eleven callee-saved registers in their slots, and the class-0 fake frame F at position fpos of the
   allocator's frame stack (the walk's OWN frame: RLIVE's journal carries own = [(0, fpos)]), its flag cell FL stored
   in F's last word (F + 56: read by the release at 0x84034). *)
Definition rr_saved (cx : rcx) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
forall i, (i < 11)%nat ->
val_mem SEGS (arm W1 m1) (rsp0 cx - RR_FRAME + 8 + 8 * Z.of_nat i) 8 (bv_unsigned (getr (rxregs cx) (nth i RR_SAVED 0%bv))).
Definition rr_frame (cx : rcx) (fpos F FL : Z) (ly1 : alayout) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
frame_addr ly1 0 fpos = F /\ flag_addr ly1 0 fpos = FL /\
val_mem SEGS (arm W1 m1) (F + 56) 8 FL /\
rr_saved cx W1 m1.

(* The registers every cut after the prologue holds: sp, gp, tp, s0 = the entry sp, s1 = sp, s2 = s4 = F (the
   fake frame __asan_stack_malloc_0 returned), s5 = F's shadow, s6 = the shadow offset (ld from the GOT). *)
Definition rregs_base (cx : rcx) (regs1 : bvmap 5 word) (F : Z) : Prop :=
spZ regs1 = rsp0 cx - RR_FRAME /\
getr regs1 3 = getr (rxregs cx) 3 /\ getr regs1 4 = getr (rxregs cx) 4 /\
getr regs1 8 = w64 (rsp0 cx) /\ getr regs1 9 = w64 (rsp0 cx - RR_FRAME) /\
getr regs1 18 = w64 F /\ getr regs1 20 = w64 F /\
getr regs1 21 = w64 (shadow_addr F) /\ getr regs1 22 = w64 SHADOW_OFF /\
(* s10, s11: callee-saved, never saved by relay_remove, so kept in their registers *)
getr regs1 26 = getr (rxregs cx) 26 /\ getr regs1 27 = getr (rxregs cx) 27.
(* ... and, after the lock: s3 = fd, s7 = g_nsrc's register image *)
Definition rregs_held (cx : rcx) (regs1 : bvmap 5 word) (F : Z) : Prop :=
rregs_base cx regs1 F /\
getr regs1 19 = w64 (rxFD cx) /\ getr regs1 23 = w64 (rg_nsrc RG + RR_HI_NSRC).

(* ---- What holds while the lock is held. ----
   RLIVE: the journal from the entry (at relay_remove's globals G_RR, the stack RR_STK_x and the footprint rr_fp;
   ajournal_gx_x, the head set Hp1 after S1) owning the fake frame (0, fpos), the .rodata view, the presence of image
   bytes, the frame, g_lock held and g_wake[1] = -1. *)
Definition RLIVE (cx : rcx) (F FL : Z) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS)
(m1 : word -> option byte) (md1 : Model) (k1 : Z) : Prop :=
exists fpos,
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 /\
rom_view SEGS W1 m1 /\ apres_kept B (rxW cx) (rxmem cx) W1 m1 /\
rr_frame cx fpos F FL ly1 W1 m1 /\
alock_at RG W1 m1 true /\ awake_at RG W1 m1.

(* RHELD: the lock taken and nothing else changed: the relay's table, the output, the live blocks and g_s as at
   the entry; drain's source facts for the entry of fd; the meter has charged nothing, the live bytes fit; the room
   round: the whole budget (the trace's counting-meter cost plus kr) and the entry's count fact at the current
   blocks. *)
Definition RHELD (cx : rcx) (F FL : Z) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS)
(m1 : word -> option byte) (md1 : Model) (k1 : Z) : Prop :=
RLIVE cx F FL ly1 S1 Hp1 W1 m1 md1 k1 /\
arelay_at B RG ly1 S1 W1 m1 (rxG0 cx) (rxes cx) /\
aout_at B RG ly1 S1 W1 m1 (rxc cx) (rxO cx) (rxmx cx) (Z.of_nat (length (rxO cx))) (rxcap cx) (rxout cx) /\
Permutation (ablocks B ly1 S1)
  ((rxG0 cx, ATABLE) :: concat (map aentry_blks (rxes cx)) ++
   (if rr_drains (rxFD cx) (rxes cx) then asrc_blks (rxh cx) else []) ++ aout_blks (rxcap cx) (rxout cx) ++ rxrest cx) /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept (rxW cx) (rxmem cx) W1 m1 a) /\
(forall i, (i < length (rxes cx))%nat -> re_fd (rnth cx i) = rxFD cx -> re_eof (rnth cx i) = 0 ->
   dr_src_ok B RG ly1 S1 W1 m1 (rnth cx i) (rxh cx) (rxj cx)) /\
mo_le MT (rxS cx) S1 0 /\ blocks_bytes S1 + tr_peak (rtr cx) <= LIVE_MAX /\
rp_RM RP S1 (Z.to_nat (tr_cost MT_rk (rtr cx)) + rxkr cx) /\
cnt_ok_pk RP (rr_pk (rtr cx)) (ablocks B ly1 S1).

(* RDONE: entry i (the one with fd) handled: rr_post's found clause and g_s clause at the current state, the full
   cost of the request trace charged; the room round: what rr_post_x passes on, kr. *)
Definition RDONE (cx : rcx) (i : nat) (F FL : Z) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS)
(m1 : word -> option byte) (md1 : Model) (k1 : Z) : Prop :=
RLIVE cx F FL ly1 S1 Hp1 W1 m1 md1 k1 /\
(i < length (rxes cx))%nat /\ re_fd (rnth cx i) = rxFD cx /\
mo_le MT (rxS cx) S1 (tr_cost MT (rtr cx)) /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
   (rr_drains (rxFD cx) (rxes cx) = true ->
    ~ (rg_s RG + ASRC * Z.of_nat (rxj cx) <= a < rg_s RG + ASRC * Z.of_nat (rxj cx) + ASRC)) ->
   abyte_kept (rxW cx) (rxmem cx) W1 m1 a) /\
rr_found B RG (rxly cx) (rxS cx) (rxW cx) (rxmem cx) ly1 S1 W1 m1
  (rxG0 cx) (rxes cx) i (rxj cx) (rxh cx) (rxc cx) (rxO cx) (rxmx cx) (rxcap cx) (rxout cx) /\
rp_RM RP S1 (rxkr cx).

(* ---- The cut predicates. ---- *)

(* RRL k (0x83f14): the scan loop's head at entry k < |es| of the table g_src = G0, none of entries 0 .. k-1 has
   fd.  a1 = G0, a2 = 56 |es| (the loop's bound, 0x83f00-0x83f08), a3 = the shadow address of entry k's fd field
   as the loop computes it (s6 + (G0 >> 3), plus 7 per entry), s8 = 56 k, s9 = g_src's register image. *)
Definition RRL (cx : rcx) (k : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 F FL,
c1 = cfg_at SEGS (BASE + A_rr_scan) regs1 m1 md1 /\
rregs_held cx regs1 F /\
getr regs1 25 = w64 (rg_src RG + RR_HI_SRC) /\
getr regs1 11 = w64 (rxG0 cx) /\ getr regs1 12 = w64 (AENT * rN cx) /\
getr regs1 13 = w64 (SHADOW_OFF + rxG0 cx / 8 + 7 * Z.of_nat k) /\
getr regs1 24 = w64 (AENT * Z.of_nat k) /\
0 <= rxFD cx /\ (k < length (rxes cx))%nat /\
(forall i, (i < k)%nat -> re_fd (rnth cx i) <> rxFD cx) /\
RHELD cx F FL ly1 S1 Hp1 W1 m1 md1 k1.

(* RRM i (0x83f48): entry i has fd (the first that has it; arelay_at's NoDup makes it the only one).
   a0 = G0 + 56 i, s8 = 56 i, s9 = g_src's register image. *)
Definition RRM (cx : rcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 F FL,
c1 = cfg_at SEGS (BASE + A_rr_match) regs1 m1 md1 /\
rregs_held cx regs1 F /\
getr regs1 25 = w64 (rg_src RG + RR_HI_SRC) /\
getr regs1 10 = w64 (rxG0 cx + AENT * Z.of_nat i) /\ getr regs1 24 = w64 (AENT * Z.of_nat i) /\
0 <= rxFD cx /\ (i < length (rxes cx))%nat /\ re_fd (rnth cx i) = rxFD cx /\
RHELD cx F FL ly1 S1 Hp1 W1 m1 md1 k1.

(* RRU oi (0x83fc4): the unlock tail.  None: no entry has fd (the scan's exit, or the empty table) and nothing
   changed; Some i: entry i handled (RDONE).  Only the base registers are live here (s3, s7 .. s9 are dead). *)
Definition RRU (cx : rcx) (oi : option nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 F FL,
c1 = cfg_at SEGS (BASE + A_rr_unlock) regs1 m1 md1 /\
rregs_base cx regs1 F /\ 0 <= rxFD cx /\
match oi with
| None => RHELD cx F FL ly1 S1 Hp1 W1 m1 md1 k1 /\ (forall e, In e (rxes cx) -> re_fd e <> rxFD cx)
| Some i => RDONE cx i F FL ly1 S1 Hp1 W1 m1 md1 k1
end.

(* ---- The segment statements. ---- *)

(* PRO: the prologue 0x83de4 .. 0x83ed4 (eleven saves, the uar test, __asan_stack_malloc_0 (64) 0x83e48, the frame
   header and its shadow poison), the fd < 0 test 0x83ed8 (fd < 0: the frame's release 0x84000 and the return, all
   in this segment), pthread_mutex_lock (g_lock) 0x83ee4, g_nsrc <= 0 0x83ef0 (-> RRU None) and the scan's setup
   0x83ef4-0x83f10 (-> RRL 0). *)
Definition rr_pro_stmt : Prop :=
forall cx,
RBASE cx ->
(forall W2 c2, RRL cx 0 W2 c2 -> SRr SEGS W2 c2 (rPOST cx)) ->
(forall W2 c2, RRU cx None W2 c2 -> SRr SEGS W2 c2 (rPOST cx)) ->
SRr SEGS (rxW cx) (cfg_at SEGS A_rr_entryP (rxregs cx) (rxmem cx) (rxmd cx)) (rPOST cx).

(* SCAN: one step of the scan loop 0x83f14-0x83f34 at entry k: the shadow check of entry k's fd field
   (0x83f14 lb, 0x83f1c bnez, 0x83f38-0x83f40: the report call 0x83f44 is NOT taken), the fd load 0x83f20, the
   match test 0x83f24 (-> RRM k), and the step 0x83f28-0x83f34 (s8 += 56, a3 += 7; the last entry -> RRU None,
   else -> RRL (S k)).  No call, no store: memory, journal and world are unchanged. *)
Definition rr_scan_stmt : Prop :=
forall cx k W1 c1,
RBASE cx -> RRL cx k W1 c1 ->
(forall W2 c2, RRL cx (S k) W2 c2 -> SRr SEGS W2 c2 (rPOST cx)) ->
(forall W2 c2, RRM cx k W2 c2 -> SRr SEGS W2 c2 (rPOST cx)) ->
(forall W2 c2, RRU cx None W2 c2 -> SRr SEGS W2 c2 (rPOST cx)) ->
SRr SEGS W1 c1 (rPOST cx).

(* SCANS: the scan loop, by induction on |es| - k. *)
Definition rr_scans_stmt : Prop :=
rr_scan_stmt ->
forall cx k W1 c1,
RBASE cx -> RRL cx k W1 c1 ->
(forall i W2 c2, RRM cx i W2 c2 -> SRr SEGS W2 c2 (rPOST cx)) ->
(forall W2 c2, RRU cx None W2 c2 -> SRr SEGS W2 c2 (rPOST cx)) ->
SRr SEGS W1 c1 (rPOST cx).

(* MATCH: RRM i 0x83f48 -> the shadow check of the eof field (0x83f4c-0x83f58, 0x84098-0x840a8 not taken), drain
   when open (0x83f64), gestures_end (0x83f70), the shadow check of the buf field (0x83f80-0x83f8c, 0x840ac not
   taken), free (s->buf) (0x83f94), g_nsrc -= 1 (0x83fa8) and g_src[i] = g_src[g_nsrc] by __asan_memcpy (0x83fc0;
   onto itself when i is the last entry) -> RRU (Some i). *)
Definition rr_match_stmt : Prop :=
forall cx i W1 c1,
RBASE cx -> RCTX cx -> RRM cx i W1 c1 ->
(forall W2 c2, RRU cx (Some i) W2 c2 -> SRr SEGS W2 c2 (rPOST cx)) ->
SRr SEGS W1 c1 (rPOST cx).

(* TAIL: RRU oi 0x83fc4 -> pthread_mutex_unlock (g_lock) (0x83fd0), the wake byte (0x83fd8-0x83fdc), the wake
   test 0x83fe8 (g_wake[1] = -1: the write 0x83ff4 is NOT taken), the frame's release 0x84000-0x8405c (retired
   magic, shadow 0xf5, *flag = 0) and the epilogue -> rr_post. *)
Definition rr_tail_stmt : Prop :=
forall cx oi W1 c1,
RBASE cx -> RRU cx oi W1 c1 ->
SRr SEGS W1 c1 (rPOST cx).

(* The walk: the segments give relay_remove's generic contract (SCAN is passed to SCANS). *)
Definition rr_all_stmt : Prop :=
rr_pro_stmt -> rr_scan_stmt -> rr_scans_stmt -> rr_match_stmt -> rr_tail_stmt ->
rr_spec_x B PST ARx MT RP MMAX RG CTX_AFREE A_rr_entryP.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the segment interface at a world relation R, over the same generic ARx.  The
   record rcx, RBASE, RCTX and the frame / register predicates carry no journal and no step relation, so they are
   shared.  The journal predicates and the statements take ajournal_gx_x -> ajournal_gx_xR R and SRr SEGS ->
   YA0nH.SRrG SEGS R; the post is W_contract_xR_relay.rr_post_xR (a Theorem Labs lane's) and the walk's conclusion is
   W_contract_xR_relay.rr_spec_xR.  Names: X -> X_xR.  At R := wle each is the strict text above (X_wle below,
   by conversion). ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* :249 rr_lift_DR / :253 rr_lift_SL at R *)
Lemma rr_lift_DR_xR : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_DR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_xR; [exact rr_G_DR_RR | eassumption]. Qed.
Lemma rr_lift_SL_xR : forall XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_SL B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Proof. intros. eapply ajournal_gx_G_mono_xR; [exact rr_G_SL_RR | eassumption]. Qed.
(* :280 rPOST *)
Definition rPOST_xR (cx : rcx) : world SEGS -> config -> Prop :=
rr_post_xR B PST ARx R MT RP RG (rxregs cx) (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx)
  (rxG0 cx) (rxFD cx) (rxes cx) (rxj cx) (rxh cx) (rxc cx) (rxO cx) (rxmx cx) (rxcap cx) (rxout cx) (rxkr cx).
(* :342 RLIVE *)
Definition RLIVE_xR (cx : rcx) (F FL : Z) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS)
(m1 : word -> option byte) (md1 : Model) (k1 : Z) : Prop :=
exists fpos,
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 /\
rom_view SEGS W1 m1 /\ apres_kept B (rxW cx) (rxmem cx) W1 m1 /\
rr_frame cx fpos F FL ly1 W1 m1 /\
alock_at RG W1 m1 true /\ awake_at RG W1 m1.
(* :355 RHELD *)
Definition RHELD_xR (cx : rcx) (F FL : Z) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS)
(m1 : word -> option byte) (md1 : Model) (k1 : Z) : Prop :=
RLIVE_xR cx F FL ly1 S1 Hp1 W1 m1 md1 k1 /\
arelay_at B RG ly1 S1 W1 m1 (rxG0 cx) (rxes cx) /\
aout_at B RG ly1 S1 W1 m1 (rxc cx) (rxO cx) (rxmx cx) (Z.of_nat (length (rxO cx))) (rxcap cx) (rxout cx) /\
Permutation (ablocks B ly1 S1)
  ((rxG0 cx, ATABLE) :: concat (map aentry_blks (rxes cx)) ++
   (if rr_drains (rxFD cx) (rxes cx) then asrc_blks (rxh cx) else []) ++ aout_blks (rxcap cx) (rxout cx) ++ rxrest cx) /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept (rxW cx) (rxmem cx) W1 m1 a) /\
(forall i, (i < length (rxes cx))%nat -> re_fd (rnth cx i) = rxFD cx -> re_eof (rnth cx i) = 0 ->
   dr_src_ok B RG ly1 S1 W1 m1 (rnth cx i) (rxh cx) (rxj cx)) /\
mo_le MT (rxS cx) S1 0 /\ blocks_bytes S1 + tr_peak (rtr cx) <= LIVE_MAX /\
rp_RM RP S1 (Z.to_nat (tr_cost MT_rk (rtr cx)) + rxkr cx) /\
cnt_ok_pk RP (rr_pk (rtr cx)) (ablocks B ly1 S1).
(* :372 RDONE *)
Definition RDONE_xR (cx : rcx) (i : nat) (F FL : Z) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS)
(m1 : word -> option byte) (md1 : Model) (k1 : Z) : Prop :=
RLIVE_xR cx F FL ly1 S1 Hp1 W1 m1 md1 k1 /\
(i < length (rxes cx))%nat /\ re_fd (rnth cx i) = rxFD cx /\
mo_le MT (rxS cx) S1 (tr_cost MT (rtr cx)) /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
   (rr_drains (rxFD cx) (rxes cx) = true ->
    ~ (rg_s RG + ASRC * Z.of_nat (rxj cx) <= a < rg_s RG + ASRC * Z.of_nat (rxj cx) + ASRC)) ->
   abyte_kept (rxW cx) (rxmem cx) W1 m1 a) /\
rr_found B RG (rxly cx) (rxS cx) (rxW cx) (rxmem cx) ly1 S1 W1 m1
  (rxG0 cx) (rxes cx) i (rxj cx) (rxh cx) (rxc cx) (rxO cx) (rxmx cx) (rxcap cx) (rxout cx) /\
rp_RM RP S1 (rxkr cx).
(* :390 RRL *)
Definition RRL_xR (cx : rcx) (k : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 F FL,
c1 = cfg_at SEGS (BASE + A_rr_scan) regs1 m1 md1 /\
rregs_held cx regs1 F /\
getr regs1 25 = w64 (rg_src RG + RR_HI_SRC) /\
getr regs1 11 = w64 (rxG0 cx) /\ getr regs1 12 = w64 (AENT * rN cx) /\
getr regs1 13 = w64 (SHADOW_OFF + rxG0 cx / 8 + 7 * Z.of_nat k) /\
getr regs1 24 = w64 (AENT * Z.of_nat k) /\
0 <= rxFD cx /\ (k < length (rxes cx))%nat /\
(forall i, (i < k)%nat -> re_fd (rnth cx i) <> rxFD cx) /\
RHELD_xR cx F FL ly1 S1 Hp1 W1 m1 md1 k1.
(* :404 RRM *)
Definition RRM_xR (cx : rcx) (i : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 F FL,
c1 = cfg_at SEGS (BASE + A_rr_match) regs1 m1 md1 /\
rregs_held cx regs1 F /\
getr regs1 25 = w64 (rg_src RG + RR_HI_SRC) /\
getr regs1 10 = w64 (rxG0 cx + AENT * Z.of_nat i) /\ getr regs1 24 = w64 (AENT * Z.of_nat i) /\
0 <= rxFD cx /\ (i < length (rxes cx))%nat /\ re_fd (rnth cx i) = rxFD cx /\
RHELD_xR cx F FL ly1 S1 Hp1 W1 m1 md1 k1.
(* :415 RRU *)
Definition RRU_xR (cx : rcx) (oi : option nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 F FL,
c1 = cfg_at SEGS (BASE + A_rr_unlock) regs1 m1 md1 /\
rregs_base cx regs1 F /\ 0 <= rxFD cx /\
match oi with
| None => RHELD_xR cx F FL ly1 S1 Hp1 W1 m1 md1 k1 /\ (forall e, In e (rxes cx) -> re_fd e <> rxFD cx)
| Some i => RDONE_xR cx i F FL ly1 S1 Hp1 W1 m1 md1 k1
end.
(* :430 rr_pro_stmt *)
Definition rr_pro_stmt_xR : Prop :=
forall cx,
RBASE cx ->
(forall W2 c2, RRL_xR cx 0 W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (rPOST_xR cx)) ->
(forall W2 c2, RRU_xR cx None W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (rPOST_xR cx)) ->
YA0nH.SRrG SEGS R (rxW cx) (cfg_at SEGS A_rr_entryP (rxregs cx) (rxmem cx) (rxmd cx)) (rPOST_xR cx).
(* :441 rr_scan_stmt *)
Definition rr_scan_stmt_xR : Prop :=
forall cx k W1 c1,
RBASE cx -> RRL_xR cx k W1 c1 ->
(forall W2 c2, RRL_xR cx (S k) W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (rPOST_xR cx)) ->
(forall W2 c2, RRM_xR cx k W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (rPOST_xR cx)) ->
(forall W2 c2, RRU_xR cx None W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (rPOST_xR cx)) ->
YA0nH.SRrG SEGS R W1 c1 (rPOST_xR cx).
(* :450 rr_scans_stmt *)
Definition rr_scans_stmt_xR : Prop :=
rr_scan_stmt_xR ->
forall cx k W1 c1,
RBASE cx -> RRL_xR cx k W1 c1 ->
(forall i W2 c2, RRM_xR cx i W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (rPOST_xR cx)) ->
(forall W2 c2, RRU_xR cx None W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (rPOST_xR cx)) ->
YA0nH.SRrG SEGS R W1 c1 (rPOST_xR cx).
(* :462 rr_match_stmt *)
Definition rr_match_stmt_xR : Prop :=
forall cx i W1 c1,
RBASE cx -> RCTX cx -> RRM_xR cx i W1 c1 ->
(forall W2 c2, RRU_xR cx (Some i) W2 c2 -> YA0nH.SRrG SEGS R W2 c2 (rPOST_xR cx)) ->
YA0nH.SRrG SEGS R W1 c1 (rPOST_xR cx).
(* :471 rr_tail_stmt *)
Definition rr_tail_stmt_xR : Prop :=
forall cx oi W1 c1,
RBASE cx -> RRU_xR cx oi W1 c1 ->
YA0nH.SRrG SEGS R W1 c1 (rPOST_xR cx).
(* :477 rr_all_stmt *)
Definition rr_all_stmt_xR : Prop :=
rr_pro_stmt_xR -> rr_scan_stmt_xR -> rr_scans_stmt_xR -> rr_match_stmt_xR -> rr_tail_stmt_xR ->
rr_spec_xR B PST ARx R MT RP MMAX RG CTX_AFREE A_rr_entryP.
End wR.
(* the strict texts are the R texts at R := wle (by conversion) *)
Lemma rPOST_wle : rPOST = rPOST_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma RLIVE_wle : RLIVE = RLIVE_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma RHELD_wle : RHELD = RHELD_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma RDONE_wle : RDONE = RDONE_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma RRL_wle : RRL = RRL_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma RRM_wle : RRM = RRM_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma RRU_wle : RRU = RRU_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rr_pro_stmt_wle : rr_pro_stmt = rr_pro_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rr_scan_stmt_wle : rr_scan_stmt = rr_scan_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rr_scans_stmt_wle : rr_scans_stmt = rr_scans_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rr_match_stmt_wle : rr_match_stmt = rr_match_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rr_tail_stmt_wle : rr_tail_stmt = rr_tail_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma rr_all_stmt_wle : rr_all_stmt = rr_all_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
End c.
End b.
End a.
