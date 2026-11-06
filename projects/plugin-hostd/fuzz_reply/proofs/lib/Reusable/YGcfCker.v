(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfCker.v, sha256 4c828894f2dd327e9fe80e0d7b577cb211de8003c8b59228c959ed91d78146e1 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
*)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: hull_room_cf and its two instance lemmas; Cker_le_kit_cf over hull_room_cf; room_wA_parts_R over the hull form. *)
(* Theorem Labs, 2026-10-30: the kit's canonical allowance fits the room's allowance form (Main 05:0xZ, option
   (beta) in the kit's form): Cker A0 ly S kk <= abudget_kit_cf S. Cker and Cker_le are a Theorem Labs lane's cgif port of the kit's
   lazy residue (YGcfLazyResid.v); abudget_kit_cf is a Theorem Labs lane's (YGcfRoomCf.v). From Cker_le: the primary and
   pointer-array reservations are the same closed terms on both sides (PRIM_SPACE_cf, PTR_SPACE_cf); the live
   secondaries' bytes are sec_live_bytes on both sides; the live hulls and the residue 2 * page_size * kk are covered
   by the unit's hull term cf_hull (YGcfNames.v) under the NAMED premise hull_room_cf S kk (`sec_live_hulls S +
   2 * page_size * kk <= cf_hull S`), which each unit discharges from its instance equation by one lemma:
   hull_room_of_preset (cf_hull = sec_hulls_cf, YGcfAbudget.preset_hull_live_k) or hull_room_of_reply (cf_hull =
   reply_hull_cf, YGcfAbudget.reply_hull_live_k), both for kk <= D (YGcfCount.dead_secs_cf), the recycled
   secondaries; and the at-main allowance A0 fits A_BASE_CF. Both premises are NAMED and discharged per unit (reply's
   admission nsec_cf S <= cf_kmax bounds kf = D + qsec_cf S by YGcfCount.kf_le_nsec_cf). Section 2:
   the ARcf facts the report walk's errbuf grant reads (a Theorem Labs lane's F4 premises: the room half of
   errb_grant_forced, H_glazy, H_aledger). No function is proved here (rule 24). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YA0n YG00 YG0f YG0n YG01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YGcfAbudget YGcfLazyResid
YGcfRoomCf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfCount.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG03cf.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* The unit's at-main allowance fits the budget's base (the A0 of Cker / base_cf, YGcfLazyResid.v:146-148). *)
Definition A0_fits_cf (A0 : list (Z * Z)) : Prop := A_bytes A0 <= A_BASE_CF.

(* The hull room the residue needs: the live hulls and two pages per recycled secondary (kk of them) fit the unit's
   hull term. *)
Definition hull_room_cf (S : astate) (kk : Z) : Prop := sec_live_hulls S + 2 * page_size * kk <= cf_hull S.

Lemma hull_room_of_preset : forall U S kk, (forall X, cf_hull X = sec_hulls_cf X) -> Wf_cf U S ->
0 <= kk <= dead_secs_cf S -> hull_room_cf S kk.
Proof. intros U S kk E W HK. unfold hull_room_cf. rewrite E. exact (preset_hull_live_k U S kk W HK). Qed.

Lemma hull_room_of_reply : forall S kk, (forall X, cf_hull X = reply_hull_cf X) ->
0 <= kk <= dead_secs_cf S -> hull_room_cf S kk.
Proof. intros S kk E HK. unfold hull_room_cf. rewrite E. exact (reply_hull_live_k S kk HK). Qed.

Lemma Cker_le_kit_cf : forall A0 ly S kk,
A0_fits_cf A0 -> hull_room_cf S kk ->
Cker A0 ly S kk <= abudget_kit_cf S.
Proof.
intros A0 ly S kk HA HK. unfold hull_room_cf in HK.
pose proof (Cker_le A0 ly S kk) as C.
pose proof (errb_cap_cf_nonneg S) as E.
unfold A0_fits_cf in HA. unfold abudget_kit_cf, abudget_cf. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. What the report walk's errbuf grant reads from ARcf (F4, a working branch 1ad9ddb5882).          *)
(* H_aledger: the restated alc_eager_x. *)
Lemma ARcf_eager_x_cf : forall segs B ly S Hp W mem md, ARcf segs B ly S Hp W mem md ->
eager_used md <= E_BASE + eager_cf ly S md.
Proof. intros segs B ly S Hp W mem md (_ & L & _). exact (alc_eager_x _ _ _ _ L). Qed.

(* H_glazy: every noaccess or lazy address is mapped (alc_lazy_in_maps). *)
Lemma ARcf_lazy_in_maps_cf : forall segs B ly S Hp W mem md, ARcf segs B ly S Hp W mem md ->
forall x, YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x = true ->
YK0g.covered (vm_maps (m_vmmaps md)) x = true.
Proof. intros segs B ly S Hp W mem md (_ & L & _). exact (alc_lazy_in_maps _ _ _ _ L). Qed.

(* The room half of errb_grant_forced (ifs_room_w at ROOMW := n): the raw allowance plus any grant of at most
   CF_HEAD fits, from the held ledger conjunct, abudget_cf <= abudget_kit_cf (abudget_le_kit_cf) and the room of
   record (room_canon_cf, YGcfRoomCf.v). The parts form reads only what every cf relation carries (Wf_cf, the
   ledger record, the raw ledger conjunct), so the drain relation's ARcfR (CfF2b) uses it as ARcf does. *)
Lemma room_wA_parts_cf : forall segs U ly S md (W : world segs) n, Wf_cf U S -> ALedger_cf segs ly S md ->
A_bytes (w_A W) <= abudget_cf S -> room_rec_cf ly S md -> n <= CF_HEAD ->
eager_used md + A_bytes (w_A W) + n <= vm_limit (m_vmmaps md).
Proof.
intros segs U ly S md W n WF L HA R Hn.
pose proof (abudget_le_kit_cf U S WF) as K.
assert (C : A_bytes (w_A W) <= abudget_kit_cf S) by lia.
exact (room_canon_cf segs ly S md (A_bytes (w_A W)) n L C R Hn).
Qed.

(* The same at a drain cut, where the state has WfR_cf (no Compl0) in place of Wf_cf: abudget_cf <= abudget_kit_cf
   from WfR_cf alone (YGcfRoomCf.abudget_le_kit_R); the room of record is the cut's (YGcfRoomCf.room_rec_cf_of_cut). *)
Lemma room_wA_parts_R : forall segs U ly S md (W : world segs) n, YG03cf.WfR_cf U 0 0 0 S -> ALedger_cf segs ly S md ->
A_bytes (w_A W) <= abudget_cf S -> room_rec_cf ly S md -> n <= CF_HEAD ->
eager_used md + A_bytes (w_A W) + n <= vm_limit (m_vmmaps md).
Proof.
intros segs U ly S md W n WF L HA R Hn.
pose proof (abudget_le_kit_R U S WF) as K.
assert (C : A_bytes (w_A W) <= abudget_kit_cf S) by lia.
exact (room_canon_cf segs ly S md (A_bytes (w_A W)) n L C R Hn).
Qed.

Lemma room_wA_cf : forall segs B ly S Hp W mem md n, ARcf segs B ly S Hp W mem md -> room_rec_cf ly S md ->
n <= CF_HEAD -> eager_used md + A_bytes (w_A W) + n <= vm_limit (m_vmmaps md).
Proof.
intros segs B ly S Hp W mem md n (M & L & (HA & _) & _) R Hn.
exact (room_wA_parts_cf segs (as_universe B) ly S md W n (amc_wf _ _ _ _ _ M) L HA R Hn).
Qed.

End U.
