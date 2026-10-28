(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Section WithFP1.
Context {fx : DFP}.

Definition at_ (base : word) (d : Z) : word := Z_to_bv 64 (bv_unsigned base + d).

Lemma at_0 : forall base, at_ base 0 = base.
Proof.
  intros base. unfold at_. rewrite Z.add_0_r. apply bv_eq.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small, bv_unsigned_in_range.
Qed.

Lemma at_addi : forall base d e, v_addi (at_ base d) e = at_ base (d + e).
Proof.
  intros base d e. unfold at_, v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma at_at : forall base d e, at_ (at_ base d) e = at_ base (d + e).
Proof. exact at_addi. Qed.

Lemma at_self : forall a : word, Z_to_bv 64 (bv_unsigned a + 0) = a.
Proof. intros a. exact (at_0 a). Qed.

Definition assn := bvmap 5 word -> (word -> option byte) -> (word -> option byte) -> Prop.

Definition regset := reg -> Prop.
Definition memset := word -> Prop.

Definition regs_agree (C : regset) (regs regs' : bvmap 5 word) : Prop :=
  forall r, ~ C r -> getr regs' r = getr regs r.

Definition mem_agree (W : memset) (m m' : word -> option byte) : Prop :=
  forall x, ~ W x -> m' x = m x.

Lemma regs_agree_refl : forall C regs, regs_agree C regs regs.
Proof. intros C regs r _. reflexivity. Qed.

Lemma regs_agree_trans : forall C regs1 regs2 regs3,
  regs_agree C regs1 regs2 -> regs_agree C regs2 regs3 -> regs_agree C regs1 regs3.
Proof. intros C r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.

Lemma regs_agree_mono : forall (C C' : regset) regs regs',
  (forall r, C r -> C' r) -> regs_agree C regs regs' -> regs_agree C' regs regs'.
Proof. intros C C' regs regs' Hsub H r Hr. apply H. intro; apply Hr, Hsub; assumption. Qed.

Lemma regs_agree_upd : forall (C : regset) regs regs' r v,
  C r -> regs_agree C regs regs' -> regs_agree C regs (regupd regs' r v).
Proof.
  intros C regs regs' r v Hin H s Hs.
  rewrite getr_other by (intro Heq; subst; contradiction).
  apply H, Hs.
Qed.

Definition triple (segs : list Segment)
                  (C : regset) (W : memset)
                  (P : assn) (a b : word) (Q : assn) : Prop :=
  forall regs mem rom, P regs mem rom ->
    exists regs' mem',
      msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
      /\ Q regs' mem' rom
      /\ regs_agree C regs regs'
      /\ mem_agree W mem mem'.

Definition frameable (C : regset) (W : memset) (R : assn) : Prop :=
  forall regs mem rom regs' mem',
    regs_agree C regs regs' -> mem_agree W mem mem' ->
    R regs mem rom -> R regs' mem' rom.

Definition ret_ok (k : word) : Prop := v_jalr k 0 = k.

Lemma land_m2_even : forall z : Z, (z mod 2 = 0)%Z -> Z.land z (-2) = z.
Proof.
  intros z Hz.
  assert (Hl : Z.land z 1 = 0%Z).
  { replace 1%Z with (Z.ones 1) by reflexivity. rewrite Z.land_ones by lia. exact Hz. }
  replace (-2)%Z with (Z.lnot 1) by reflexivity.
  rewrite <- Z.ldiff_land.
  rewrite <- (Z.lor_ldiff_and z 1) at 2.
  rewrite Hl, Z.lor_0_r. reflexivity.
Qed.

Lemma ret_ok_even : forall k, (bv_unsigned k mod 2 = 0)%Z -> ret_ok k.
Proof.
  intros k Hk. unfold ret_ok, v_jalr, jalr_tgtZ.
  rewrite Z.add_0_r, land_m2_even by exact Hk.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

Definition proc (segs : list Segment) (C : regset) (W : memset)
                (P : assn) (entry : word) (Q : assn) : Prop :=
  forall k : word, ret_ok k ->
    triple segs C W (fun regs mem rom => P regs mem rom /\ getr regs 1 = k) entry k Q.

Definition ra_indep (P : assn) : Prop :=
  forall regs v mem rom, P regs mem rom -> P (regupd regs 1 v) mem rom.

End WithFP1.

