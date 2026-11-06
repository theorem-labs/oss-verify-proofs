(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASSEMBLY of the ASan walk of fuzz_reply's relay_remove (fuzz_reply.asan
   0x83de4): pb_relay_remove_x : rr_spec_x (first written as the AR pb_relay_remove : rr_spec, deleted: see the next
   note), from the segment statements of lib/A/W_relay_remove_cx.v composed by W_rr_all.v rr_all.  Applied: W_rr_pro.v rr_pro, W_rr_scan.v rr_scan / rr_scans (a Theorem Labs lane), W_rr_match.v rr_match
   (a Theorem Labs lane's MATCH, commit a5a15c9620a), W_rr_tail.v rr_tail.  No segment is open.  The Section block
   is regenerated from the cx file whenever the cx file changes. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record)) in the room form
   (a Theorem Labs lane, lane RR_x): this file proves pb_relay_remove_x : rr_spec_x over ANY allocator relation ARx with its
   laws (Section c, the cx file's generic block), at W8's stack constants (commit b9052387bcb, lib/A/W_contract_x.v:
   rr_spec_x at RR_STK_x = RR_STK + 128, the drain at DRAIN_STK_x = DRAIN_STK + 128, room for the strndup
   interceptor's inner malloc below the drain's frame).  The AR theorem pb_relay_remove : rr_spec and its
   re-derivation Section cAR are DELETED (a Theorem Labs lane's ruling 10:34Z, option 1): the x -> AR bridge rr_spec_x_AR0 is
   false at RR_STK_x and was removed with it, and nothing on the window applied pb_relay_remove (the AR arms keep
   rr_spec as a hypothesis; top_x takes rr_spec_x). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_relay_remove_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rr_all.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_rr_pro W_rr_scan W_rr_match W_rr_tail.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_rr_m_ge W_rr_m_free W_rr_m_cpy W_rr_m_drain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_relay.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rr_match_cx.
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

(* THE GENERIC WALK: the segments over ARx give rr_spec_x. *)
Theorem pb_relay_remove_x : rr_spec_x B PST ARx MT RP MMAX RG CTX_AFREE A_rr_entryP.
Proof.
apply (rr_all B PST ARx MT RP MMAX RG CTX_AFREE).
- eapply W_rr_pro.rr_pro; eassumption.
- eapply W_rr_scan.rr_scan; eassumption.
- eapply W_rr_scan.rr_scans; eassumption.
- eapply W_rr_match.rr_match; eassumption.
- eapply W_rr_tail.rr_tail; eassumption.
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): THE WALK AT A WORLD RELATION R.  The segments' R statements give
   W_contract_xR_relay.rr_spec_xR (a Theorem Labs lane's) by W_rr_all.rr_all_xR; MATCH is W_rr_match.rr_match_xR over the hops.
   The pieces (G8-SPLIT.md sha256 c3dda82fe6c5; internal record): PRO / SCAN / SCANS and hop GE are a Theorem Labs lane's rr_pro_xR / rr_scan_xR / rr_scans_xR /
   rr_m_ge_xR (c1089c75e734; GE's own premises GSE_R / R_IMG); TAIL and hops DRAIN / FREE are a Theorem Labs lane's rr_tail_xR
   (950778133741), rr_m_drain_xR (d6c7b54f4237; its premise DRAIN_R) and rr_m_free_xR (03c312b6b482; the crew's free
   rules at R, AFREE_R / AFREEN_R .. RO, RO_ARx); hop CPY is a Theorem Labs lane's rr_m_cpy_xR (1d015fa2530c).  The
   R premises below are the pieces' own, verbatim.  At R := wle, rr_spec_xR is rr_spec_x
   (W_contract_xR_relay.rr_spec_x_wle). ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* W_rr_m_ge.rr_m_ge_xR's own premises (a Theorem Labs lane's file), verbatim *)
(* gestures_end at R (W_contract_xR.v gse_spec_xR); hop_ge_stmt_xR is over the strict GSE, so this file alone takes it *)
Hypothesis GSE_R : gse_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* the R law of the image (a Theorem Labs lane 00:40Z, exact text): R adds no hidden byte inside the image *)
Hypothesis R_IMG : forall (W W' : world SEGS) (a : word), R W W' -> in_img SEGS (bv_unsigned a) -> w_H W' a = true -> w_H W a = true.
(* the free rules at R (crew lines, token-equal to W_gestures_end.v:296-299): what W_rr_m_free.rr_m_free_xR takes *)
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* drain at R (W_contract_xR.v dr_spec_xR): W_rr_m_drain.rr_m_drain_xR's own premise, verbatim *)
Hypothesis DRAIN_R : dr_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_drain).
(* :144 pb_relay_remove_x *)
Theorem pb_relay_remove_xR : rr_spec_xR B PST ARx R MT RP MMAX RG CTX_AFREE A_rr_entryP.
Proof.
apply (rr_all_xR B PST ARx MT RP MMAX RG CTX_AFREE R).
- eapply W_rr_pro.rr_pro_xR; eassumption.
- eapply W_rr_scan.rr_scan_xR; eassumption.
- eapply W_rr_scan.rr_scans_xR; eassumption.
- apply (W_rr_match.rr_match_xR B PST ARx MT RP MMAX RG CTX_AFREE R).
  + eapply W_rr_m_drain.rr_m_drain_xR; eassumption.
  + eapply W_rr_m_ge.rr_m_ge_xR; eassumption.
  + eapply W_rr_m_free.rr_m_free_xR; first [exact RO_ARx | eassumption].
  + eapply W_rr_m_cpy.rr_m_cpy_xR; eassumption.
- eapply W_rr_tail.rr_tail_xR; eassumption.
Qed.
End wR.
End c.
End b.
End a.
