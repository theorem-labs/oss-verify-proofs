(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec FPSteps AxSymExec3 FrmInv.
Import ListNotations. Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module FPB.

Definition rm_ok (rm : bv 3) : bool := (Z.leb (bv_unsigned rm) 4 || Z.eqb (bv_unsigned rm) 7)%bool.
Definition is_ffmt (t : fcvt_ty) : bool := match t with FC_S | FC_D => true | _ => false end.

Definition fp_hv (i : instr) : option (list nat) :=
  match i with
  | Fari _ _ _ _ _ rm => if rm_ok rm then Some [] else None
  | Fcvt dst _ _ _ rm => if (is_ffmt dst && rm_ok rm)%bool then Some [] else None
  | Fsgnj _ _ _ _ _ => Some []
  | Fmv FMV_F_X _ _ _ => Some []
  | Fmv FMV_X_F _ rd _ => Some [ridx rd]
  | Csr CSR_RS rd rs1 csr => if (bv_eqb rs1 0 && bv_eqb csr 2)%bool then Some [ridx rd] else None
  | CsrI CSR_RS rd _ csr => if (bv_eqb rd 0 && bv_eqb csr 1)%bool then Some [] else None
  | _ => None
  end.

Section WithSegs.
Variable segs : list Segment.
Abbreviation mk fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)).

Definition inl_step (pc len : Z) (hv : list nat) : Prop :=
  forall (fx : FPState) R M, FrmInv.fp_ok fx ->
    exists (fx' : FPState) R',
      msteps segs (mk fx R pc M) (mk fx' R' (pc + len) M) /\
      (forall r : reg, ~ In (ridx r) hv -> getr R' r = getr R r).

Hypothesis SAFE : FrmInv.text_safe segs.

Lemma inl_step_seq : forall pc l1 l2 hv1 hv2,
  inl_step pc l1 hv1 -> inl_step (pc + l1) l2 hv2 -> inl_step pc (l1 + l2) (hv1 ++ hv2).
Proof.
  intros pc l1 l2 hv1 hv2 H1 H2 fx R M Hfx.
  destruct (H1 fx R M Hfx) as (fx1 & R1 & Hm1 & Hr1).
  pose proof (FrmInv.msteps_fp_ok segs SAFE _ _ _ _ _ _ _ _ _ _ Hm1 Hfx) as Hfx1.
  destruct (H2 fx1 R1 M Hfx1) as (fx2 & R2 & Hm2 & Hr2).
  exists fx2, R2. split.
  - replace (pc + (l1 + l2)) with (pc + l1 + l2) by lia. eapply msteps_trans; eassumption.
  - intros r Hr. rewrite Hr2 by (intros X; apply Hr; apply in_or_app; right; exact X).
    apply Hr1. intros X; apply Hr; apply in_or_app; left; exact X.
Qed.

Lemma inl_step_weaken : forall pc len hv hv', inl_step pc len hv -> incl hv hv' -> inl_step pc len hv'.
Proof.
  intros pc len hv hv' H Hi fx R M Hfx. destruct (H fx R M Hfx) as (fx' & R' & Hm & Hr).
  exists fx', R'. split; [exact Hm|]. intros r Hn. apply Hr. intros X. apply Hn. apply Hi. exact X.
Qed.

Lemma pc4 : forall pc, 0 <= pc < 2 ^ 64 -> v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 (pc + 4).
Proof.
  intros pc Hpc. unfold v_addi. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by exact Hpc. reflexivity.
Qed.

Lemma bv_eqb_true : forall n (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. apply bv_eq. unfold bv_eqb in H. apply Z.eqb_eq in H. exact H. Qed.

Lemma rm_ok_prop : forall rm, rm_ok rm = true -> (bv_unsigned rm <= 4 \/ bv_unsigned rm = 7).
Proof. intros rm H. unfold rm_ok in H. apply orb_prop in H as [H|H]; [left; apply Z.leb_le | right; apply Z.eqb_eq]; exact H. Qed.

Lemma getr_if_upd : forall (R : bvmap 5 word) (rd : reg) v (r : reg),
  ~ In (ridx r) [ridx rd] -> getr (if bv_eqb rd 0 then R else regupd R rd v) r = getr R r.
Proof.
  intros R rd v r Hn. destruct (bv_eqb rd 0); [reflexivity|].
  apply getr_other. intros ->. apply Hn. left. reflexivity.
Qed.

Theorem inl_step_1 : forall pc w i hv,
  0 <= pc < 2 ^ 64 ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
  fp_hv i = Some hv -> inl_step pc 4 hv.
Proof.
  intros pc w i hv Hpc Hf He Hd Hc fx R M Hfx. unfold FrmInv.fp_ok in Hfx.
  assert (ONE : forall (fx' : FPState) R',
            RiscvSemantics.step segs (mk fx R pc M) = MachineOk (@mkst fx' R' (v_addi (Z_to_bv 64 pc) 4) M (seg_rom segs)) ->
            (forall r : reg, ~ In (ridx r) hv -> getr R' r = getr R r) ->
            exists (fx' : FPState) R', msteps segs (mk fx R pc M) (mk fx' R' (pc + 4) M) /\ (forall r : reg, ~ In (ridx r) hv -> getr R' r = getr R r)).
  { intros fx' R' Hs Hr. exists fx', R'. split; [|exact Hr]. rewrite <- pc4 by exact Hpc. apply msteps_one; [reflexivity | exact Hs]. }
  destruct i; cbn [fp_hv] in Hc; try discriminate.
  -
    destruct op; try discriminate. destruct (bv_eqb rs1 0 && bv_eqb csr 2)%bool eqn:Eb; [|discriminate]. injection Hc as <-.
    apply andb_prop in Eb as [E1 E2]. apply bv_eqb_true in E1, E2. subst rs1 csr.
    refine (ONE _ _ (fp_step_frrm fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w rd Hf He Hd Hfx) _); intros r Hn; apply getr_if_upd; exact Hn.
  -
    destruct op; try discriminate. destruct (bv_eqb rd 0 && bv_eqb csr 1)%bool eqn:Eb; [|discriminate]. injection Hc as <-.
    apply andb_prop in Eb as [E1 E2]. apply bv_eqb_true in E1, E2. subst rd csr.
    destruct (fp_step_csrsi_fflags fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w uimm Hf He Hd Hfx) as (cs' & _ & Hs).
    refine (ONE _ _ Hs _); intros; reflexivity.
  -
    destruct (rm_ok rm) eqn:Erm; [|discriminate]. injection Hc as <-.
    destruct (fp_step_fari fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w op fmt rd rs1 rs2 rm Hf He Hd Hfx (rm_ok_prop _ Erm)) as (fr' & cs' & _ & Hs).
    refine (ONE _ _ Hs _); intros; reflexivity.
  -
    injection Hc as <-. destruct (fp_step_fsgnj fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w op fmt rd rs1 rs2 Hf He Hd) as (fr' & Hs).
    refine (ONE _ _ Hs _); intros; reflexivity.
  -
    destruct (is_ffmt dst && rm_ok rm)%bool eqn:Eb; [|discriminate]. injection Hc as <-. apply andb_prop in Eb as [Ed Erm].
    assert (Hdst : dst = FC_S \/ dst = FC_D) by (destruct dst; try discriminate; auto).
    destruct (fp_step_fcvt_to_f fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w dst src rd rs1 rm Hf He Hd Hdst Hfx (rm_ok_prop _ Erm)) as (fr' & cs' & _ & Hs).
    refine (ONE _ _ Hs _); intros; reflexivity.
  -
    destruct dir, fmt; try discriminate; injection Hc as <-.
    + refine (ONE _ _ (fp_step_fmv_x_w fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w rd rs1 Hf He Hd) _); intros r Hn; apply getr_if_upd; exact Hn.
    + refine (ONE _ _ (fp_step_fmv_x_d fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w rd rs1 Hf He Hd) _); intros r Hn; apply getr_if_upd; exact Hn.
    + refine (ONE _ _ (fp_step_fmv_w_x fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w rd rs1 Hf He Hd) _); intros; reflexivity.
    + refine (ONE _ _ (fp_step_fmv_d_x fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w rd rs1 Hf He Hd) _); intros; reflexivity.
Qed.

Definition site_chk (pc : Z) : option (list nat) :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | Some w => if is_ecall w then None else
              match decode_any w with
              | Some (i, sz) => if Z.eqb sz 4 then fp_hv i else None
              | None => None
              end
  | None => None
  end.
Theorem inl_step_chk : forall pc hv, 0 <= pc < 2 ^ 64 -> site_chk pc = Some hv -> inl_step pc 4 hv.
Proof.
  intros pc hv Hpc H. unfold site_chk in H.
  destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:He; [discriminate|].
  destruct (decode_any w) as [[i sz]|] eqn:Hd; [|discriminate].
  destruct (Z.eqb_spec sz 4) as [->|]; [|discriminate].
  exact (inl_step_1 pc w i hv Hpc Hf He Hd H).
Qed.

Definition inl_step_a0 (pc len z : Z) : Prop :=
  forall (fx : FPState) R M, FrmInv.fp_ok fx ->
    exists (fx' : FPState), msteps segs (mk fx R pc M) (mk fx' (regupd R 10%bv (Z_to_bv 64 z)) (pc + len) M).
Definition site_frrm_a0_chk (pc : Z) : bool :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | Some w => if is_ecall w then false else
              match decode_any w with
              | Some (Csr CSR_RS rd rs1 csr, sz) => (Z.eqb sz 4 && bv_eqb rd 10 && bv_eqb rs1 0 && bv_eqb csr 2)%bool
              | _ => false
              end
  | None => false
  end.
Theorem inl_step_frrm_a0 : forall pc, 0 <= pc < 2 ^ 64 -> site_frrm_a0_chk pc = true -> inl_step_a0 pc 4 0.
Proof.
  intros pc Hpc H fx R M Hfx. unfold site_frrm_a0_chk in H.
  destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:He; [discriminate|].
  destruct (decode_any w) as [[i sz]|] eqn:Hd; [|discriminate].
  destruct i; try discriminate. destruct op; try discriminate.
  apply andb_prop in H as [H E3]. apply andb_prop in H as [H E2]. apply andb_prop in H as [E0 E1].
  apply Z.eqb_eq in E0. apply bv_eqb_true in E1, E2, E3. subst sz rd rs1 csr.
  exists fx. rewrite <- pc4 by exact Hpc. apply msteps_one; [reflexivity|].
  exact (fp_step_frrm fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w 10%bv Hf He Hd Hfx).
Qed.

End WithSegs.
End FPB.
