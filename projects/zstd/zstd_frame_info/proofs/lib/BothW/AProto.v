(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Export AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. unfold shad. Local Ltac2 Set LiaHints.tbl := fun () => "0030=29782367974.431240251061.4749188513.4  000001004005SS1HS".
rewrite !Z.shiftr_div_pow2 by lia. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shad_aligned : forall a k, 0 <= k -> shad (a + 8 * k) = shad a + k.
Proof. intros a k Hk. unfold shad. Local Ltac2 Set LiaHints.tbl := fun () => "0030=29784460291.446668240017.461028788393.4000001002003SSS".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.add_comm with (n := a).
  rewrite Z.mul_comm, Z.div_add_l by lia. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fp_bw (R : footprint) : Prop :=
  forall b (j : nat), 0 <= b -> b + Z.of_nat j <= 2^64 ->
    (forall k, (k < j)%nat -> R (b + Z.of_nat k) 1%nat) -> R b j.

#[using="Type"] Lemma fp_ok_bw : forall lz AL, fp_bw (fp_ok lz AL).
Proof.
  intros lz AL b j Hb Hj H k Hk _.
  specialize (H k Hk 0%nat ltac:(lia) ltac:(lia)). rewrite Z.add_0_r in H. exact H.
Qed.

#[using="Type"] Lemma rng_merge : forall R lo n1 n2, fp_bw R -> 0 <= n1 -> 0 <= n2 ->
  rng R lo n1 -> rng R (lo + n1) n2 -> rng R lo (n1 + n2).
Proof.
  intros R lo n1 n2 BW N1 N2 (A1 & A2 & A) (B1 & B2 & B). split; [exact A1|]. Local Ltac2 Set LiaHints.tbl := fun () => "0070>2139048694.21 25990568416.2131924317731.2142364080399.1461883802902.1863246427132.187560260986.21 00000600<00C00G00N00U00\S2Hk1LS2Hk1GS2Hb2HkS2B2S2A12HbS2B22HjS2Hj2Hk".
split; [lia|].
  intros b j Hb Hj. apply BW; [lia | lia |]. intros k Hk.
  destruct (Z_lt_le_dec (b + Z.of_nat k) (lo + n1)) as [L|G].
  - apply A; lia.
  - apply B; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition MAP_NORESERVE : Z := 16384.

Definition fstepS (n : node) (rsp : resp) (R R' : footprint) : Prop :=
  fstepA n rsp R R' /\
  match n with
  | NMmap addr len prot flags =>
      (Z.land flags MAP_NORESERVE = 0 ->
       prot = PROT_READ + PROT_WRITE ->
       bv_unsigned (eff_ret rsp) mod page_size = 0 ->
       rng R' (shad (bv_unsigned (eff_ret rsp))) (shlen (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))))
      /\ fp_bw R'
  | NMunmap _ _ => fp_le R R'       (* [comment removed for export] *)
  | _ => True
  end.

#[using="Type"] Lemma fstepS_fstepA : forall n rsp R R', fstepS n rsp R R' -> fstepA n rsp R R'.
Proof. intros n rsp R R' [H _]; exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fstepS_le : forall n rsp R R', fstepS n rsp R R' -> fp_le R R'.
Proof.
  intros n rsp R R' [HA HS]. destruct n; cbn in HA, HS;
    first [ exact HS | exact (proj1 HA) | exact HA | (rewrite HA; intros b j H; exact H) ].
Qed.

#[using="Type"] Lemma fstepS_id : forall n rsp R,
  match n with NMmap _ _ _ _ | NMunmap _ _ | NBrk _ | NMprotect _ _ _ => False | _ => True end ->
  fstepS n rsp R R.
Proof. intros n rsp R H. split; [apply fstepA_id; exact H|]. destruct n; try exact I; destruct H. Qed.

#[using="Type"] Lemma fstepS_rng : forall n rsp R R' lo len,
  match n with NMunmap _ _ => False | _ => True end ->
  fstepS n rsp R R' -> rng R lo len -> rng R' lo len.
Proof. intros n rsp R R' lo len Hn [HF _] HR. eapply fstepA_rng; eauto. Qed.

#[using="Type"] Lemma fstepS_mmap_grant : forall addr len flags rsp R R',
  fstepS (NMmap addr len (PROT_READ + PROT_WRITE) flags) rsp R R' ->
  Z.land flags MAP_NORESERVE = 0 ->
  bv_unsigned (eff_ret rsp) mod page_size = 0 ->
  rng R' (bv_unsigned (eff_ret rsp)) (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))
  /\ rng R' (shad (bv_unsigned (eff_ret rsp))) (shlen (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))).
Proof.
  intros addr len flags rsp R R' [HF [HS _]] NR Hal. split.
  - eapply fstepA_mmap_grant; eauto.
  - apply HS; [exact NR | reflexivity | exact Hal].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fstepS_mmap_bw : forall addr len prot flags rsp R R',
  fstepS (NMmap addr len prot flags) rsp R R' -> fp_bw R'.
Proof. intros addr len prot flags rsp R R' [_ [_ HB]]. exact HB. Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation implS segs RNG t Q ms := (@implF node segs (at_nodeA segs) fstepS _ RNG t Q ms).

(* [comment removed for export] *)
Ltac fstepS_transport HF :=
  lazymatch type of HF with
  | fstepS ?n ?rsp ?RNG ?RNG' =>
      let HA := fresh "HFA" in
      destruct HF as [HA HF]; cbn [fstepS] in HF;
      first [ (* [comment removed for export] *)
              lazymatch eval hnf in (fstepA n rsp RNG RNG') with RNG' = RNG => idtac end;
              let E := fresh in assert (E : RNG' = RNG) by exact HA; subst RNG'; clear HA; try clear HF
            | fstep_transport HA; try match type of HF with True => clear HF end ]
  end.
Tactic Notation "fstepS_intro" ident(rsp) ident(RNG') ident(a) ident(HF) ident(Hdec) :=
  intros rsp RNG' a HF Hdec; fstepS_transport HF.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma implS_ret : forall RNG {R} (r : R) (Q : R -> footprint -> machine_state -> Prop) ms,
  evtF bsegs RNG (Q r RNG) ms -> implS bsegs RNG (aembed ATOP (SRet r)) (epostF Q) ms.
Proof. intros RNG R r Q ms H. rewrite aembed_ret. apply implF_ret_ok. exact H. Qed.
End CANSEC2.
