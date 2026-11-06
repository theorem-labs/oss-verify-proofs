(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Lemma nth_repeat_inS {A} (a d : A) (m j : nat) : (j < m)%nat -> nth j (repeat a m) d = a.
Proof. revert j. induction m as [|m IH]; intros [|j] Hj; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); try lia; [reflexivity | apply IH; lia]. Qed.

(* [comment removed for export] *)
Definition psm (M : word -> option byte) (sp ra s0 s1 s2 s3 s4 s5 addr size value : word) : word -> option byte :=
  wbytes (ps_frame M sp ra s0 s1 s2 s3 s4 s5) (Z_to_bv 64 (shad addr)) (repeat (cbyte value) (Z.to_nat (shlen size))).

Section PSM.
  Variables (M : word -> option byte) (sp ra s0 s1 s2 s3 s4 s5 addr size value : word).
  Hypothesis Hsp : 64 <= U sp.
  Hypothesis Hsh : shad addr + shlen size < 2 ^ 64.

  Lemma shad_shlen_nonneg : 0 <= shad addr /\ 0 <= shlen size.
  Proof using value M. pose proof (u64_range addr). pose proof (u64_range size). (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end). split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia | lia] | apply Z.div_pos; lia]. Qed.

  Lemma ps_frame_out : forall x : word, (U x < U sp - 56 \/ U sp <= U x) -> ps_frame M sp ra s0 s1 s2 s3 s4 s5 x = M x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold ps_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; [reflexivity | ..]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.
  Lemma ps_frame_grows : mem_grows M (ps_frame M sp ra s0 s1 s2 s3 s4 s5).
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold ps_frame in G in change_no_check G' end). do 7 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  Lemma psm_out : forall x : word, (U x < U sp - 56 \/ U sp <= U x) -> (U x < shad addr \/ shad addr + shlen size <= U x) ->
    psm M sp ra s0 s1 s2 s3 s4 s5 addr size value x = M x.
  Proof using Hsh Hsp.
    intros x Hf Hs. pose proof shad_shlen_nonneg as [A1 A2]. (lazymatch goal with |- ?G => let G' := eval unfold psm in G in change_no_check G' end).
    rewrite wbytes_outside; [apply ps_frame_out; exact Hf | |]; rewrite repeat_length, Z2Nat.id by lia; first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ].
  Qed.
  Lemma psm_in : forall x : word, shad addr <= U x < shad addr + shlen size ->
    psm M sp ra s0 s1 s2 s3 s4 s5 addr size value x = Some (cbyte value).
  Proof using Hsh.
    intros x Hx. pose proof shad_shlen_nonneg as [A1 A2]. (lazymatch goal with |- ?G => let G' := eval unfold psm in G in change_no_check G' end).
    rewrite wbytes_inside; [| rewrite repeat_length, Z2Nat.id by lia; first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite repeat_length, Z2Nat.id by lia; first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]].
    rewrite nth_repeat_inS; [reflexivity|]. rewrite u_Z2bv by lia. lia.
  Qed.
  Lemma psm_grows : mem_grows M (psm M sp ra s0 s1 s2 s3 s4 s5 addr size value).
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold psm in G in change_no_check G' end). eapply mem_grows_trans; [apply ps_frame_grows | apply wbytes_grows]. Qed.
End PSM.

(* [comment removed for export] *)
Lemma wb_out : forall (M : word -> option byte) (a x : word) bs, U a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (U x < U a \/ U a + Z.of_nat (length bs) <= U x) -> wbytes M a bs x = M x.
Proof. intros M a x bs H1 H2. apply wbytes_outside; assumption. Qed.


(* [comment removed for export] *)
Lemma psm_facts : forall (Mx : word -> option byte) (sp ra s0 s1 s2 s3 s4 s5 : word) (a sz v : Z),
  64 <= U sp -> 0 <= a -> 0 <= sz -> a + sz <= 2 ^ 47 ->
  let Mn := psm Mx sp ra s0 s1 s2 s3 s4 s5 (Z_to_bv 64 a) (Z_to_bv 64 sz) (Z_to_bv 64 v) in
  (forall x : word, (U x < U sp - 56 \/ U sp <= U x) -> (U x < 0x7fff8000 + a / 8 \/ 0x7fff8000 + a / 8 + sz / 8 <= U x) -> Mn x = Mx x)
  /\ (forall x : word, 0x7fff8000 + a / 8 <= U x < 0x7fff8000 + a / 8 + sz / 8 -> Mn x = Some (cbyte (Z_to_bv 64 v)))
  /\ mem_grows Mx Mn.
Proof.
  intros Mx sp ra s0 s1 s2 s3 s4 s5 a sz v Hsp Ha Hsz Hle Mn.
  assert (E1 : shad (Z_to_bv 64 a) = 0x7fff8000 + a / 8) by ((lazymatch goal with |- ?G => let G' := eval unfold shad in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]).
  assert (E2 : shlen (Z_to_bv 64 sz) = sz / 8) by ((lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
  assert (Hsh : shad (Z_to_bv 64 a) + shlen (Z_to_bv 64 sz) < 2 ^ 64) by (rewrite E1, E2; Z.div_mod_to_equations; lia).
  split; [| split].
  - intros x Hf Hs. (lazymatch goal with |- ?G => let G' := eval unfold Mn in G in change_no_check G' end). apply psm_out; [exact Hsp | exact Hsh | exact Hf | rewrite E1, E2; exact Hs].
  - intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Mn in G in change_no_check G' end). apply psm_in; [exact Hsh | rewrite E1, E2; exact Hx].
  - (lazymatch goal with |- ?G => let G' := eval unfold Mn in G in change_no_check G' end). apply psm_grows.
Qed.
