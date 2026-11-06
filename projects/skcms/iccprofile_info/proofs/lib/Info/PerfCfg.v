(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec SymExec2 SymDrive.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations. Import SX2.

(* [comment removed for export] *)
Definition cfgx0 : expr :=
  EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EExt true 0 1 (EVar 7))) (ELit 49))
       (EExt false 0 1 (EVar 6)).
Definition cfgF0 (v6 v7 : word) : word :=
  edenot (Env (fun n => match n with 6%nat => v6 | 7%nat => v7 | _ => Z_to_bv 64 0 end) (blobs_ev []))
         cfgx0.
Definition zseq0 (n : nat) : list Z := map Z.of_nat (seq 0 n).
(* [comment removed for export] *)
Definition cfgG (v7 : word) : word :=
  Sem.alu64 ALU_SRL (Sem.mul_div M_MUL (Z_to_bv 64 144115188075855872) (ext_val true 0 1 v7)) (Z_to_bv 64 49).
Definition cfgH (v6 : word) : word := ext_val false 0 1 v6.
Lemma cfgF0_split : forall v6 v7, cfgF0 v6 v7 = bv_or (cfgG v7) (cfgH v6).
Proof. intros v6 v7. reflexivity. Qed.
Lemma cfgG_tab :
  forallb (fun b1 => Z.eqb (bv_unsigned (cfgG (Z_to_bv 64 b1))) ((256 * b1) mod 32768)) (zseq0 256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cfgH_tab :
  forallb (fun b0 => Z.eqb (bv_unsigned (cfgH (Z_to_bv 64 b0))) b0) (zseq0 256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cfg_lor_tab :
  forallb (fun b1 => forallb (fun b0 =>
     Z.eqb (Z.lor ((256 * b1) mod 32768) b0) ((b0 + 256 * b1) mod 32768)) (zseq0 256)) (zseq0 256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cfgF0_tab :
  forallb (fun b1 => forallb (fun b0 =>
     Z.eqb (bv_unsigned (cfgF0 (Z_to_bv 64 b0) (Z_to_bv 64 b1))) ((b0 + 256 * b1) mod 32768))
     (zseq0 256)) (zseq0 256) = true.
Proof.
  apply forallb_forall. intros b1 H1. apply forallb_forall. intros b0 H0. apply Z.eqb_eq.
  rewrite cfgF0_split, bv_or_unsigned.
  pose proof (proj1 (forallb_forall _ _) cfgG_tab b1 H1) as HG. cbv beta in HG. apply Z.eqb_eq in HG.
  pose proof (proj1 (forallb_forall _ _) cfgH_tab b0 H0) as HH. cbv beta in HH. apply Z.eqb_eq in HH.
  rewrite HG, HH.
  pose proof (proj1 (forallb_forall _ _) cfg_lor_tab b1 H1) as HL. cbv beta in HL.
  pose proof (proj1 (forallb_forall _ _) HL b0 H0) as HL2. cbv beta in HL2. apply Z.eqb_eq in HL2. exact HL2.
Qed.
