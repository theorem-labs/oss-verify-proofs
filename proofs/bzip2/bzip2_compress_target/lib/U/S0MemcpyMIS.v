(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib U.S0MemcpyBase.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec U.S0_code_256f4_26728 U.S0_code_26728_26f04  .
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require WalkHide.
Import WalkHide.OptIn.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Module S7MemcpyAL.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StepTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Hoare OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WalkTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0MemcpyBase.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import ListNotations.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section AL.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  #[local] Notation SB := (sb_ bs).
  #[local] Notation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma b1_run : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    (0 <= k)%Z -> (k + 1 = n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x30aa4 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k Hret H1 H11 H13 Hk Hkn.
    eexists. split.
    - mlbu F_2692c D_2692c k.                      (* [comment removed for export] *)
      msb F_26930 D_26930 k ltac:(apply sb_val_plain).   (* [comment removed for export] *)
      replace (k + 1)%Z with n by lia.
      stepret F_26934 D_26934 ret ltac:(exact H1).
      apply mst_refl.
    - solve_keeps.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t2_run : forall regs (ret : word) k m,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z ->
    (Z.land m 2 = 0 \/ Z.land m 2 = 2)%Z -> (Z.land m 1 = 0 \/ Z.land m 1 = 1)%Z ->
    (0 <= k)%Z -> (n - k = Z.land m 2 + Z.land m 1)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x30a6c : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_268f4 D_268f4.                          (* [comment removed for export] *)
        stepb_ft F_268f8 D_268f8 ltac:(cond).           (* [comment removed for export] *)
        stepn F_268fc D_268fc.                          (* [comment removed for export] *)
        stepb_ft F_26900 D_26900 ltac:(cond).           (* [comment removed for export] *)
        stepret F_26904 D_26904 ret ltac:(exact H1).
        mk_eq. apply mst_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x30aa4 : word) (MK k) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
      + eexists. split.
        * stepn F_268f4 D_268f4.
          stepb_ft F_268f8 D_268f8 ltac:(cond).
          stepn F_268fc D_268fc.
          stepb_tk F_26900 D_26900 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
      + cbv beta. (intros r1; cps_intros (R1 & R11 & R13 & K1)).
        cps_destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_268f4 D_268f4.
        stepb_tk F_268f8 D_268f8 ltac:(cond).           (* [comment removed for export] *)
        mlbu F_26908 D_26908 k.                         (* [comment removed for export] *)
        mlbu F_2690c D_2690c (k + 1)%Z.                 (* [comment removed for export] *)
        stepn F_26910 D_26910.                          (* [comment removed for export] *)
        stepn F_26914 D_26914.                          (* [comment removed for export] *)
        msb F_26918 D_26918 k ltac:(apply sb_val_plain).          (* [comment removed for export] *)
        msb F_2691c D_2691c (k + 1)%Z ltac:(apply sb_val_plain).  (* [comment removed for export] *)
        stepn F_26920 D_26920.                          (* [comment removed for export] *)
        stepn F_26924 D_26924.                          (* [comment removed for export] *)
        stepb_tk F_26928 D_26928 ltac:(cond).           (* [comment removed for export] *)
        stepret F_26904 D_26904 ret ltac:(exact H1).
        mk_eq. apply mst_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x30aa4 : word) (MK (k + 2)) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
      + eexists. split.
        * stepn F_268f4 D_268f4.
          stepb_tk F_268f8 D_268f8 ltac:(cond).
          mlbu F_26908 D_26908 k.
          mlbu F_2690c D_2690c (k + 1)%Z.
          stepn F_26910 D_26910.
          stepn F_26914 D_26914.
          msb F_26918 D_26918 k ltac:(apply sb_val_plain).
          msb F_2691c D_2691c (k + 1)%Z ltac:(apply sb_val_plain).
          stepn F_26920 D_26920.
          stepn F_26924 D_26924.
          stepb_ft F_26928 D_26928 ltac:(cond).         (* [comment removed for export] *)
          mk_eq. apply mst_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; rwH; rewrite ?at_addi; reflexivity
                                 | gres; rwH; rewrite ?at_addi; reflexivity | solve_keeps].
      + cbv beta. (intros r1; cps_intros (R1 & R11 & R13 & K1)).
        cps_destruct (b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al4_run : forall regs (ret : word) k m,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x30828 : word) (MK k) rom)
                   (mkst regs' (0x30a6c : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 4) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
    - eexists. split.
      + stepn F_266b0 D_266b0.                          (* [comment removed for export] *)
        stepb_tk F_266b4 D_266b4 ltac:(cond).           (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_266b0 D_266b0.
        stepb_ft F_266b4 D_266b4 ltac:(cond).           (* [comment removed for export] *)
        mlw F_266b8 D_266b8 k.                          (* [comment removed for export] *)
        stepn F_266bc D_266bc.                          (* [comment removed for export] *)
        msw F_266c0 D_266c0 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).   (* [comment removed for export] *)
        stepn F_266c4 D_266c4.                          (* [comment removed for export] *)
        stepn F_266c8 D_266c8.                          (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al8_run : forall regs (ret : word) k m e8,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (m < 8 /\ e8 = 0 \/ 8 <= m /\ e8 = 8 /\ k + 8 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x30808 : word) (MK k) rom)
                   (mkst regs' (0x30828 : word) (MK (k + e8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + e8)
      /\ getr regs' 13 = at_ dst (k + e8) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
    - eexists. split.
      + stepn F_26690 D_26690.                          (* [comment removed for export] *)
        stepb_tk F_26694 D_26694 ltac:(cond).           (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_26690 D_26690.
        stepb_ft F_26694 D_26694 ltac:(cond).
        mlw F_26698 D_26698 k.                          (* [comment removed for export] *)
        mlw F_2669c D_2669c (k + 4)%Z.                  (* [comment removed for export] *)
        msw F_266a0 D_266a0 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).         (* [comment removed for export] *)
        msw F_266a4 D_266a4 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        stepn F_266a8 D_266a8.                          (* [comment removed for export] *)
        stepn F_266ac D_266ac.                          (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_loop : forall (q : nat) regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = Z_to_bv 64 15 ->
    (0 <= k)%Z -> (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x307d8 : word) (MK k) rom)
                   (mkst regs' (0x30808 : word) (MK (k + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 13 = at_ dst (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
    - (* [comment removed for export] *)
      eexists. split.
      + mlw F_26660 D_26660 k.                          (* [comment removed for export] *)
        mlw F_26664 D_26664 (k + 4)%Z.                  (* [comment removed for export] *)
        mlw F_26668 D_26668 (k + 8)%Z.                  (* [comment removed for export] *)
        mlw F_2666c D_2666c (k + 12)%Z.                 (* [comment removed for export] *)
        stepn F_26670 D_26670.                          (* [comment removed for export] *)
        stepn F_26674 D_26674.                          (* [comment removed for export] *)
        msw F_26678 D_26678 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).          (* [comment removed for export] *)
        msw F_2667c D_2667c (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        msw F_26680 D_26680 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        msw F_26684 D_26684 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        stepn F_26688 D_26688.                          (* [comment removed for export] *)
        stepb_ft F_2668c D_2668c ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
        * unfold v_addi. unorm. f_equal. lia.
        * solve_keeps.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x307d8 : word) (MK (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * mlw F_26660 D_26660 k.
          mlw F_26664 D_26664 (k + 4)%Z.
          mlw F_26668 D_26668 (k + 8)%Z.
          mlw F_2666c D_2666c (k + 12)%Z.
          stepn F_26670 D_26670.
          stepn F_26674 D_26674.
          msw F_26678 D_26678 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_2667c D_2667c (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_26680 D_26680 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_26684 D_26684 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          stepn F_26688 D_26688.
          stepb_tk F_2668c D_2668c ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          mk_eq. apply mst_refl.
        * cbv beta. repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
          -- unfold v_addi. unorm. f_equal. lia.
          -- solve_keeps.
      + cbv beta. (intros r1; cps_intros (R1 & R11 & R13 & R12 & R14 & K1)).
        cps_destruct (IH r1 ret (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. split.
        * replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia. exact RUN.
        * replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
          decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma al16_run : forall regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x307cc : word) (MK k) rom)
                   (mkst regs' (0x30808 : word) (MK (n - (n - k) mod 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (n - k) mod 16)
      /\ getr regs' 13 = at_ dst (n - (n - k) mod 16)
      /\ getr regs' 12 = Z_to_bv 64 ((n - k) mod 16) /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 Hk.
    destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_26654 D_26654.                          (* [comment removed for export] *)
        stepb_tk F_26658 D_26658 ltac:(cond).           (* [comment removed for export] *)
        replace (n - (n - k) mod 16)%Z with k by (rewrite Z.mod_small; lia).
        apply mst_refl.
      + rewrite (Z.mod_small (n - k) 16) by lia. replace (n - (n - k))%Z with k by lia.
        repeat split; gres; rwH; try reflexivity. solve_keeps.
    - set (q := Z.to_nat ((n - k) / 16 - 1)).
      assert (Hq : (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z).
      { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
        pose proof (Z.div_mod (n - k) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)). lia. }
      assert (Hk' : (k + 16 * (Z.of_nat q + 1) = n - (n - k) mod 16)%Z).
      { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
        pose proof (Z.div_mod (n - k) 16 ltac:(lia)). lia. }
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x307d8 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
                         /\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * stepn F_26654 D_26654.                        (* [comment removed for export] *)
          stepb_ft F_26658 D_26658 ltac:(cond).         (* [comment removed for export] *)
          stepn F_2665c D_2665c.                        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps.
      + cbv beta. (intros r1; cps_intros (R1 & R11 & R13 & R12 & R14 & K1)).
        cps_destruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P).
        exists r2. rewrite <- Hk'. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
        decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

End AL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S7MemcpyAL.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StepTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Hoare OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WalkTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0MemcpyBase S7MemcpyAL.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import ListNotations.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section MIS.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  #[local] Notation SB := (sb_ bs).
  #[local] Notation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac sbp := apply sb_val_plain.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma b4_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x30a40 : word) (MK k) rom) (mkst regs' (0x30a6c : word) (MK (k + 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. eexists. split.
    - mlbu F_268c8 D_268c8 k. mlbu F_268cc D_268cc (k+1)%Z. mlbu F_268d0 D_268d0 (k+2)%Z. mlbu F_268d4 D_268d4 (k+3)%Z.
      stepn F_268d8 D_268d8.                            (* [comment removed for export] *)
      stepn F_268dc D_268dc.                            (* [comment removed for export] *)
      msb F_268e0 D_268e0 k ltac:(sbp). msb F_268e4 D_268e4 (k+1)%Z ltac:(sbp).
      msb F_268e8 D_268e8 (k+2)%Z ltac:(sbp). msb F_268ec D_268ec (k+3)%Z ltac:(sbp).
      stepn F_268f0 D_268f0.                            (* [comment removed for export] *)
      mk_eq. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma b8_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 8 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x309ec : word) (MK k) rom) (mkst regs' (0x30a38 : word) (MK (k + 8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. eexists. split.
    - mlbu F_26874 D_26874 k. mlbu F_26878 D_26878 (k+1)%Z. mlbu F_2687c D_2687c (k+2)%Z. mlbu F_26880 D_26880 (k+3)%Z.
      mlbu F_26884 D_26884 (k+4)%Z. mlbu F_26888 D_26888 (k+5)%Z. mlbu F_2688c D_2688c (k+6)%Z. mlbu F_26890 D_26890 (k+7)%Z.
      stepn F_26894 D_26894.                            (* [comment removed for export] *)
      msb F_26898 D_26898 k ltac:(sbp). msb F_2689c D_2689c (k+1)%Z ltac:(sbp).
      msb F_268a0 D_268a0 (k+2)%Z ltac:(sbp). msb F_268a4 D_268a4 (k+3)%Z ltac:(sbp).
      stepn F_268a8 D_268a8.                            (* [comment removed for export] *)
      msb F_268ac D_268ac (k+4)%Z ltac:(sbp). msb F_268b0 D_268b0 (k+5)%Z ltac:(sbp).
      msb F_268b4 D_268b4 (k+6)%Z ltac:(sbp). msb F_268b8 D_268b8 (k+7)%Z ltac:(sbp).
      stepn F_268bc D_268bc.                            (* [comment removed for export] *)
      mk_eq. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma b16_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 16 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x30958 : word) (MK k) rom) (mkst regs' (0x309e4 : word) (MK (k + 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. eexists. split.
    - mlbu F_267e0 D_267e0 k. mlbu F_267e4 D_267e4 (k+1)%Z. mlbu F_267e8 D_267e8 (k+2)%Z. mlbu F_267ec D_267ec (k+3)%Z.
      mlbu F_267f0 D_267f0 (k+4)%Z. mlbu F_267f4 D_267f4 (k+5)%Z. mlbu F_267f8 D_267f8 (k+6)%Z. mlbu F_267fc D_267fc (k+7)%Z.
      msb F_26800 D_26800 k ltac:(sbp). msb F_26804 D_26804 (k+1)%Z ltac:(sbp).
      msb F_26808 D_26808 (k+2)%Z ltac:(sbp). msb F_2680c D_2680c (k+3)%Z ltac:(sbp).
      mlbu F_26810 D_26810 (k+8)%Z. mlbu F_26814 D_26814 (k+9)%Z. mlbu F_26818 D_26818 (k+10)%Z. mlbu F_2681c D_2681c (k+11)%Z.
      msb F_26820 D_26820 (k+4)%Z ltac:(sbp). msb F_26824 D_26824 (k+5)%Z ltac:(sbp).
      msb F_26828 D_26828 (k+6)%Z ltac:(sbp). msb F_2682c D_2682c (k+7)%Z ltac:(sbp).
      mlbu F_26830 D_26830 (k+12)%Z. mlbu F_26834 D_26834 (k+13)%Z. mlbu F_26838 D_26838 (k+14)%Z. mlbu F_2683c D_2683c (k+15)%Z.
      stepn F_26840 D_26840.                            (* [comment removed for export] *)
      msb F_26844 D_26844 (k+8)%Z ltac:(sbp). msb F_26848 D_26848 (k+9)%Z ltac:(sbp).
      msb F_2684c D_2684c (k+10)%Z ltac:(sbp). msb F_26850 D_26850 (k+11)%Z ltac:(sbp).
      stepn F_26854 D_26854.                            (* [comment removed for export] *)
      msb F_26858 D_26858 (k+12)%Z ltac:(sbp). msb F_2685c D_2685c (k+13)%Z ltac:(sbp).
      msb F_26860 D_26860 (k+14)%Z ltac:(sbp). msb F_26864 D_26864 (k+15)%Z ltac:(sbp).
      stepn F_26868 D_26868.                            (* [comment removed for export] *)
      mk_eq. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma t4_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x30714 : word) (MK k) rom) (mkst regs' (0x30a6c : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_2659c D_2659c.                          (* [comment removed for export] *)
        stepb_ft F_265a0 D_265a0 ltac:(cond).           (* [comment removed for export] *)
        stepn F_265a4 D_265a4.                          (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x30a40 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_2659c D_2659c.
          stepb_tk F_265a0 D_265a0 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; cps_intros (R1 & R11 & R13 & R12 & K1)).
        cps_destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma b8_tail : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x30a38 : word) (MK k) rom) (mkst regs' (0x30a6c : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_268c0 D_268c0.                          (* [comment removed for export] *)
        stepb_tk F_268c4 D_268c4 ltac:(cond).           (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x30a40 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_268c0 D_268c0.
          stepb_ft F_268c4 D_268c4 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; cps_intros (R1 & R11 & R13 & R12 & K1)).
        cps_destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma t8_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x3070c : word) (MK k) rom)
                   (mkst regs' (0x30a6c : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x30714 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_26594 D_26594.                        (* [comment removed for export] *)
          stepb_ft F_26598 D_26598 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; cps_intros (R1 & R11 & R13 & R12 & K1)).
        cps_destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x309ec : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_26594 D_26594.
          stepb_tk F_26598 D_26598 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; cps_intros (R1 & R11 & R13 & R12 & K1)).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x30a38 : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * cps_destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2; cps_intros (S1 & S11 & S13 & S12 & K2)).
          cps_destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL8. replace (k + 8 + Z.land m 4)%Z with (k + 8 + Z.land m 4)%Z by lia.
          split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma b16_tail : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x309e4 : word) (MK k) rom)
                   (mkst regs' (0x30a6c : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x30714 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_2686c D_2686c.                        (* [comment removed for export] *)
          stepb_tk F_26870 D_26870 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; cps_intros (R1 & R11 & R13 & R12 & K1)).
        cps_destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x309ec : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_2686c D_2686c.
          stepb_ft F_26870 D_26870 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; cps_intros (R1 & R11 & R13 & R12 & K1)).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x30a38 : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * cps_destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2; cps_intros (S1 & S11 & S13 & S12 & K2)).
          cps_destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL8. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma t16_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 32)%Z -> (0 <= k)%Z ->
    (k + Z.land m 16 + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x30704 : word) (MK k) rom)
                   (mkst regs' (0x30a6c : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk Hkn.
    cps_destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x3070c : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_2658c D_2658c.                        (* [comment removed for export] *)
          stepb_ft F_26590 D_26590 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; cps_intros (R1 & R11 & R13 & R12 & K1)).
        cps_destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x30958 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_2658c D_2658c.
          stepb_tk F_26590 D_26590 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; cps_intros (R1 & R11 & R13 & R12 & K1)).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x309e4 : word) (MK (k + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * cps_destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2; cps_intros (S1 & S11 & S13 & S12 & K2)).
          cps_destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

End MIS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
