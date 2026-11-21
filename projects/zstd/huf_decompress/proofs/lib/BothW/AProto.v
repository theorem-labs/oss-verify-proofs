(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (10 recorded proofs replaced by written proofs (shad_mono, shad_aligned, fp_ok_bw and 7 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Export AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AProto () := "C47Corelib4Init5Logic8eq_ind_rI59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed:aembed_retC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z=add_le_mono_lK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z;div_le_monoC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z9div_add_lC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z8add_commK46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Peano2ltK47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib4LibA5ExecF5fp_okC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula05C4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofC59OSSVerify5KrLib4LibA8AcctCore7page_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic6eq_indc59OSSVerify5KrLib5BothW6AProto5fp_bwC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic3and01C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW6AProto6fstepSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA6fstepAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5fp_leC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00c59OSSVerify5KrLib5BothW6AProto=MAP_NORESERVEC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9PROT_READC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi:PROT_WRITEC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeK59OSSVerify5KrLib3Lib5Nodes4node01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node08C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node09C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1K59OSSVerify5KrLib3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0=C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA9fstepA_idC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4LibA6NodesA:fstepA_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesAAfstepA_mmap_grantC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6aembedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA<implF_ret_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl3aev00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. unfold shad. rewrite !Z.shiftr_div_pow2 by lia. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. Qed.
Lemma shad_aligned : forall a k, 0 <= k -> shad (a + 8 * k) = shad a + k.
Proof. intros a k Hk. unfold shad. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.add_comm with (n := a).
  rewrite Z.mul_comm, Z.div_add_l by lia. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fp_bw (R : footprint) : Prop :=
  forall b (j : nat), 0 <= b -> b + Z.of_nat j <= 2^64 ->
    (forall k, (k < j)%nat -> R (b + Z.of_nat k) 1%nat) -> R b j.

Lemma fp_ok_bw : forall lz AL, fp_bw (fp_ok lz AL).
Proof.
  intros lz AL b j Hb Hj H k Hk _.
  specialize (H k Hk 0%nat ltac:(lia) ltac:(lia)). rewrite Z.add_0_r in H. exact H.
Qed.

Lemma rng_merge : forall R lo n1 n2, fp_bw R -> 0 <= n1 -> 0 <= n2 ->
  rng R lo n1 -> rng R (lo + n1) n2 -> rng R lo (n1 + n2).
Proof.
  intros R lo n1 n2 BW N1 N2 (A1 & A2 & A) (B1 & B2 & B). split; [exact A1|]. split; [lia|].
  intros b j Hb Hj. apply BW; [lia | lia |]. intros k Hk.
  destruct (Z_lt_le_dec (b + Z.of_nat k) (lo + n1)) as [L|G].
  - apply A; lia.
  - apply B; lia.
Qed.

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

Lemma fstepS_fstepA : forall n rsp R R', fstepS n rsp R R' -> fstepA n rsp R R'.
Proof. intros n rsp R R' [H _]; exact H. Qed.

(* [comment removed for export] *)
Lemma fstepS_le : forall n rsp R R', fstepS n rsp R R' -> fp_le R R'.
Proof.
  intros n rsp R R' [HA HS]. destruct n; cbn in HA, HS;
    first [ exact HS | exact (proj1 HA) | exact HA | (rewrite HA; intros b j H; exact H) ].
Qed.

Lemma fstepS_id : forall n rsp R,
  match n with NMmap _ _ _ _ | NMunmap _ _ | NBrk _ | NMprotect _ _ _ => False | _ => True end ->
  fstepS n rsp R R.
Proof. intros n rsp R H. split; [apply fstepA_id; exact H|]. destruct n; try exact I; destruct H. Qed.

Lemma fstepS_rng : forall n rsp R R' lo len,
  match n with NMunmap _ _ => False | _ => True end ->
  fstepS n rsp R R' -> rng R lo len -> rng R' lo len.
Proof. intros n rsp R R' lo len Hn [HF _] HR. eapply fstepA_rng; eauto. Qed.

Lemma fstepS_mmap_grant : forall addr len flags rsp R R',
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
Lemma fstepS_mmap_bw : forall addr len prot flags rsp R R',
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
Lemma implS_ret : forall RNG {R} (r : R) (Q : R -> footprint -> machine_state -> Prop) ms,
  evtF bsegs RNG (Q r RNG) ms -> implS bsegs RNG (aembed ATOP (SRet r)) (epostF Q) ms.
Proof. intros RNG R r Q ms H. rewrite aembed_ret. apply implF_ret_ok. exact H. Qed.
End CANSEC2.
