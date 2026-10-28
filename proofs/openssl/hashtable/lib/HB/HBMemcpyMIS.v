(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib HBMemcpyBase.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec HB_code_528000_529000.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import DietTac.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module HAMemcpyAL.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SeqExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StepTac OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Hoare OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StoreOk OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.WalkTac OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MmapSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefMemcpyLib HBMemcpyBase.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import ListNotations.
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
  Lemma al_entry : forall regs (mem : word -> option byte),
    getr regs 10 = dst -> getr regs 11 = src ->
    (bv_unsigned src mod 4 = 0)%Z -> (bv_unsigned dst mod 4 = 0)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x560e08 : word) mem rom) (mkst regs' (0x560f28 : word) mem rom)
      /\ getr regs' 13 = at_ dst 0 /\ getr regs' 11 = at_ src 0 /\ getr regs' 12 = getr regs 12
      /\ getr regs' 1 = getr regs 1 /\ keeps regs regs'.
  Proof.
    intros regs mem H10 H11 Hs4 Hd4.
    pose proof (u64_range src). pose proof (u64_range dst).
    eexists. split.
    - stepn F_528290 D_528290.                       (* [comment removed for export] *)
      stepb_tk F_528294 D_528294                     (* [comment removed for export] *)
        ltac:(rwH; unfold c_eq, bv_eqb; rewrite u_andi by lia; unorm; rewrite land_3 by lia; apply Z.eqb_eq; lia).
      stepn F_5283a4 D_5283a4.                       (* [comment removed for export] *)
      stepn F_5283a8 D_5283a8.                       (* [comment removed for export] *)
      stepb_ft F_5283ac D_5283ac                     (* [comment removed for export] *)
        ltac:(rwH; unfold c_eq, bv_eqb; rewrite u_andi by lia; unorm; rewrite land_3 by lia; apply Z.eqb_eq; lia).
      apply mst_refl.
    - repeat split; gres; rwH; rewrite ?at_0; try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma b1_run : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    (0 <= k)%Z -> (k + 1 = n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x561200 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k Hret H1 H11 H13 Hk Hkn.
    eexists. split.
    - mlbu F_528688 D_528688 k.                      (* [comment removed for export] *)
      msb F_52868c D_52868c k ltac:(apply sb_val_plain).   (* [comment removed for export] *)
      replace (k + 1)%Z with n by lia.
      stepret F_528690 D_528690 ret ltac:(exact H1).
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
      msteps RSEGS (mkst regs (0x5611c8 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_528650 D_528650.                          (* [comment removed for export] *)
        stepb_ft F_528654 D_528654 ltac:(cond).           (* [comment removed for export] *)
        stepn F_528658 D_528658.                          (* [comment removed for export] *)
        stepb_ft F_52865c D_52865c ltac:(cond).           (* [comment removed for export] *)
        stepret F_528660 D_528660 ret ltac:(exact H1).
        mk_eq. apply mst_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x561200 : word) (MK k) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
      + eexists. split.
        * stepn F_528650 D_528650.
          stepb_ft F_528654 D_528654 ltac:(cond).
          stepn F_528658 D_528658.
          stepb_tk F_52865c D_52865c ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
      + cbv beta. intros r1 (R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; diet_eassumption].
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_528650 D_528650.
        stepb_tk F_528654 D_528654 ltac:(cond).           (* [comment removed for export] *)
        mlbu F_528664 D_528664 k.                         (* [comment removed for export] *)
        mlbu F_528668 D_528668 (k + 1)%Z.                 (* [comment removed for export] *)
        stepn F_52866c D_52866c.                          (* [comment removed for export] *)
        stepn F_528670 D_528670.                          (* [comment removed for export] *)
        msb F_528674 D_528674 k ltac:(apply sb_val_plain).          (* [comment removed for export] *)
        msb F_528678 D_528678 (k + 1)%Z ltac:(apply sb_val_plain).  (* [comment removed for export] *)
        stepn F_52867c D_52867c.                          (* [comment removed for export] *)
        stepn F_528680 D_528680.                          (* [comment removed for export] *)
        stepb_tk F_528684 D_528684 ltac:(cond).           (* [comment removed for export] *)
        stepret F_528660 D_528660 ret ltac:(exact H1).
        mk_eq. apply mst_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x561200 : word) (MK (k + 2)) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
      + eexists. split.
        * stepn F_528650 D_528650.
          stepb_tk F_528654 D_528654 ltac:(cond).
          mlbu F_528664 D_528664 k.
          mlbu F_528668 D_528668 (k + 1)%Z.
          stepn F_52866c D_52866c.
          stepn F_528670 D_528670.
          msb F_528674 D_528674 k ltac:(apply sb_val_plain).
          msb F_528678 D_528678 (k + 1)%Z ltac:(apply sb_val_plain).
          stepn F_52867c D_52867c.
          stepn F_528680 D_528680.
          stepb_ft F_528684 D_528684 ltac:(cond).         (* [comment removed for export] *)
          mk_eq. apply mst_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; rwH; rewrite ?at_addi; reflexivity
                                 | gres; rwH; rewrite ?at_addi; reflexivity | solve_keeps].
      + cbv beta. intros r1 (R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; diet_eassumption].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al4_run : forall regs (ret : word) k m,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x560f84 : word) (MK k) rom)
                   (mkst regs' (0x5611c8 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 4) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
    - eexists. split.
      + stepn F_52840c D_52840c.                          (* [comment removed for export] *)
        stepb_tk F_528410 D_528410 ltac:(cond).           (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_52840c D_52840c.
        stepb_ft F_528410 D_528410 ltac:(cond).           (* [comment removed for export] *)
        mlw F_528414 D_528414 k.                          (* [comment removed for export] *)
        stepn F_528418 D_528418.                          (* [comment removed for export] *)
        msw F_52841c D_52841c k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).   (* [comment removed for export] *)
        stepn F_528420 D_528420.                          (* [comment removed for export] *)
        stepn F_528424 D_528424.                          (* [comment removed for export] *)
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
      msteps RSEGS (mkst regs (0x560f64 : word) (MK k) rom)
                   (mkst regs' (0x560f84 : word) (MK (k + e8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + e8)
      /\ getr regs' 13 = at_ dst (k + e8) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
    - eexists. split.
      + stepn F_5283ec D_5283ec.                          (* [comment removed for export] *)
        stepb_tk F_5283f0 D_5283f0 ltac:(cond).           (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_5283ec D_5283ec.
        stepb_ft F_5283f0 D_5283f0 ltac:(cond).
        mlw F_5283f4 D_5283f4 k.                          (* [comment removed for export] *)
        mlw F_5283f8 D_5283f8 (k + 4)%Z.                  (* [comment removed for export] *)
        msw F_5283fc D_5283fc k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).         (* [comment removed for export] *)
        msw F_528400 D_528400 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        stepn F_528404 D_528404.                          (* [comment removed for export] *)
        stepn F_528408 D_528408.                          (* [comment removed for export] *)
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
      msteps RSEGS (mkst regs (0x560f34 : word) (MK k) rom)
                   (mkst regs' (0x560f64 : word) (MK (k + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 13 = at_ dst (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
    - (* [comment removed for export] *)
      eexists. split.
      + mlw F_5283bc D_5283bc k.                          (* [comment removed for export] *)
        mlw F_5283c0 D_5283c0 (k + 4)%Z.                  (* [comment removed for export] *)
        mlw F_5283c4 D_5283c4 (k + 8)%Z.                  (* [comment removed for export] *)
        mlw F_5283c8 D_5283c8 (k + 12)%Z.                 (* [comment removed for export] *)
        stepn F_5283cc D_5283cc.                          (* [comment removed for export] *)
        stepn F_5283d0 D_5283d0.                          (* [comment removed for export] *)
        msw F_5283d4 D_5283d4 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).          (* [comment removed for export] *)
        msw F_5283d8 D_5283d8 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        msw F_5283dc D_5283dc (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        msw F_5283e0 D_5283e0 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        stepn F_5283e4 D_5283e4.                          (* [comment removed for export] *)
        stepb_ft F_5283e8 D_5283e8 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
        * unfold v_addi. unorm. f_equal. lia.
        * solve_keeps.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x560f34 : word) (MK (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * mlw F_5283bc D_5283bc k.
          mlw F_5283c0 D_5283c0 (k + 4)%Z.
          mlw F_5283c4 D_5283c4 (k + 8)%Z.
          mlw F_5283c8 D_5283c8 (k + 12)%Z.
          stepn F_5283cc D_5283cc.
          stepn F_5283d0 D_5283d0.
          msw F_5283d4 D_5283d4 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_5283d8 D_5283d8 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_5283dc D_5283dc (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_5283e0 D_5283e0 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          stepn F_5283e4 D_5283e4.
          stepb_tk F_5283e8 D_5283e8 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          mk_eq. apply mst_refl.
        * cbv beta. repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
          -- unfold v_addi. unorm. f_equal. lia.
          -- solve_keeps.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
        destruct (IH r1 ret (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. split.
        * replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia. exact RUN.
        * replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
          decompose [and] P. repeat split; try assumption. eapply keeps_trans; diet_eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma al16_run : forall regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x560f28 : word) (MK k) rom)
                   (mkst regs' (0x560f64 : word) (MK (n - (n - k) mod 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (n - k) mod 16)
      /\ getr regs' 13 = at_ dst (n - (n - k) mod 16)
      /\ getr regs' 12 = Z_to_bv 64 ((n - k) mod 16) /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 Hk.
    destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_5283b0 D_5283b0.                          (* [comment removed for export] *)
        stepb_tk F_5283b4 D_5283b4 ltac:(cond).           (* [comment removed for export] *)
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
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x560f34 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
                         /\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * stepn F_5283b0 D_5283b0.                        (* [comment removed for export] *)
          stepb_ft F_5283b4 D_5283b4 ltac:(cond).         (* [comment removed for export] *)
          stepn F_5283b8 D_5283b8.                        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
        destruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P).
        exists r2. rewrite <- Hk'. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
        decompose [and] P. repeat split; try assumption. eapply keeps_trans; diet_eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem memcpy_aligned : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    (bv_unsigned src mod 4 = 0)%Z -> (bv_unsigned dst mod 4 = 0)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x560e08 : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11 H12 Hs4 Hd4.
    pose proof (u64_range src). pose proof (u64_range dst).
    rewrite <- (memk_n _ _ _ _ _ HOK). change mem0 with (MK 0).
    set (m := (n mod 16)%Z).
    pose proof (Z.mod_pos_bound n 16 ltac:(lia)) as Hm16.
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (Hl16 : Z.land m 16 = 0%Z).
    { destruct B16 as [E|E]; [exact E|]. exfalso.
      pose proof (Z.land_nonneg m 8). pose proof (Z.land_nonneg m 4). pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). lia. }
    (* [comment removed for export] *)
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x560f28 : word) (MK 0) rom)
             (fun r => getr r 13 = at_ dst 0 /\ getr r 11 = at_ src 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ getr r 1 = ret /\ keeps regs r)).
    { destruct (al_entry regs (MK 0) H10 H11 Hs4 Hd4) as (r & R & P). exists r. split; [exact R|].
      decompose [and] P. rewrite Z.sub_0_r. repeat split; try assumption; congruence. }
    cbv beta. intros r1 (R13 & R11 & R12 & R1 & K1).
    (* [comment removed for export] *)
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x560f64 : word) (MK (n - m)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al16_run r1 ret 0 R1 R11 R13 R12 ltac:(lia)) as (r & R & P). exists r.
      subst m. rewrite Z.sub_0_r in R, P. split; [exact R|]. decompose [and] P. repeat split; try assumption.
      eapply keeps_trans; diet_eassumption. }
    cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
    (* [comment removed for export] *)
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x560f84 : word) (MK (n - m + Z.land m 8)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al8_run r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia)) as (r & R & P).
      { pose proof (Z.land_nonneg m 4). pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). lia. }
      exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; diet_eassumption. }
    cbv beta. intros r3 (T1 & T11 & T13 & T12 & K3).
    (* [comment removed for export] *)
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x5611c8 : word) (MK (n - m + Z.land m 8 + Z.land m 4)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8 + Z.land m 4) /\ getr r 13 = at_ dst (n - m + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al4_run r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia)) as (r & R & P).
      { pose proof (Z.land_nonneg m 8). lia. }
      { pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). pose proof (Z.land_nonneg m 8). lia. }
      exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; diet_eassumption. }
    cbv beta. intros r4 (U1 & U11 & U13 & U12 & K4).
    (* [comment removed for export] *)
    destruct (t2_run r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1) as (r & R & P).
    { pose proof (Z.land_nonneg m 8). pose proof (Z.land_nonneg m 4). lia. }
    { lia. }
    exists r. split; [exact R | eapply keeps_trans; diet_eassumption].
  Qed.

End AL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End HAMemcpyAL.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SeqExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StepTac OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Hoare OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StoreOk OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.WalkTac OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MmapSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefMemcpyLib HBMemcpyBase HAMemcpyAL.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import ListNotations.
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
      msteps RSEGS (mkst regs (0x56119c : word) (MK k) rom) (mkst regs' (0x5611c8 : word) (MK (k + 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. eexists. split.
    - mlbu F_528624 D_528624 k. mlbu F_528628 D_528628 (k+1)%Z. mlbu F_52862c D_52862c (k+2)%Z. mlbu F_528630 D_528630 (k+3)%Z.
      stepn F_528634 D_528634.                            (* [comment removed for export] *)
      stepn F_528638 D_528638.                            (* [comment removed for export] *)
      msb F_52863c D_52863c k ltac:(sbp). msb F_528640 D_528640 (k+1)%Z ltac:(sbp).
      msb F_528644 D_528644 (k+2)%Z ltac:(sbp). msb F_528648 D_528648 (k+3)%Z ltac:(sbp).
      stepn F_52864c D_52864c.                            (* [comment removed for export] *)
      mk_eq. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma b8_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 8 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x561148 : word) (MK k) rom) (mkst regs' (0x561194 : word) (MK (k + 8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. eexists. split.
    - mlbu F_5285d0 D_5285d0 k. mlbu F_5285d4 D_5285d4 (k+1)%Z. mlbu F_5285d8 D_5285d8 (k+2)%Z. mlbu F_5285dc D_5285dc (k+3)%Z.
      mlbu F_5285e0 D_5285e0 (k+4)%Z. mlbu F_5285e4 D_5285e4 (k+5)%Z. mlbu F_5285e8 D_5285e8 (k+6)%Z. mlbu F_5285ec D_5285ec (k+7)%Z.
      stepn F_5285f0 D_5285f0.                            (* [comment removed for export] *)
      msb F_5285f4 D_5285f4 k ltac:(sbp). msb F_5285f8 D_5285f8 (k+1)%Z ltac:(sbp).
      msb F_5285fc D_5285fc (k+2)%Z ltac:(sbp). msb F_528600 D_528600 (k+3)%Z ltac:(sbp).
      stepn F_528604 D_528604.                            (* [comment removed for export] *)
      msb F_528608 D_528608 (k+4)%Z ltac:(sbp). msb F_52860c D_52860c (k+5)%Z ltac:(sbp).
      msb F_528610 D_528610 (k+6)%Z ltac:(sbp). msb F_528614 D_528614 (k+7)%Z ltac:(sbp).
      stepn F_528618 D_528618.                            (* [comment removed for export] *)
      mk_eq. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma b16_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 16 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x5610b4 : word) (MK k) rom) (mkst regs' (0x561140 : word) (MK (k + 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. eexists. split.
    - mlbu F_52853c D_52853c k. mlbu F_528540 D_528540 (k+1)%Z. mlbu F_528544 D_528544 (k+2)%Z. mlbu F_528548 D_528548 (k+3)%Z.
      mlbu F_52854c D_52854c (k+4)%Z. mlbu F_528550 D_528550 (k+5)%Z. mlbu F_528554 D_528554 (k+6)%Z. mlbu F_528558 D_528558 (k+7)%Z.
      msb F_52855c D_52855c k ltac:(sbp). msb F_528560 D_528560 (k+1)%Z ltac:(sbp).
      msb F_528564 D_528564 (k+2)%Z ltac:(sbp). msb F_528568 D_528568 (k+3)%Z ltac:(sbp).
      mlbu F_52856c D_52856c (k+8)%Z. mlbu F_528570 D_528570 (k+9)%Z. mlbu F_528574 D_528574 (k+10)%Z. mlbu F_528578 D_528578 (k+11)%Z.
      msb F_52857c D_52857c (k+4)%Z ltac:(sbp). msb F_528580 D_528580 (k+5)%Z ltac:(sbp).
      msb F_528584 D_528584 (k+6)%Z ltac:(sbp). msb F_528588 D_528588 (k+7)%Z ltac:(sbp).
      mlbu F_52858c D_52858c (k+12)%Z. mlbu F_528590 D_528590 (k+13)%Z. mlbu F_528594 D_528594 (k+14)%Z. mlbu F_528598 D_528598 (k+15)%Z.
      stepn F_52859c D_52859c.                            (* [comment removed for export] *)
      msb F_5285a0 D_5285a0 (k+8)%Z ltac:(sbp). msb F_5285a4 D_5285a4 (k+9)%Z ltac:(sbp).
      msb F_5285a8 D_5285a8 (k+10)%Z ltac:(sbp). msb F_5285ac D_5285ac (k+11)%Z ltac:(sbp).
      stepn F_5285b0 D_5285b0.                            (* [comment removed for export] *)
      msb F_5285b4 D_5285b4 (k+12)%Z ltac:(sbp). msb F_5285b8 D_5285b8 (k+13)%Z ltac:(sbp).
      msb F_5285bc D_5285bc (k+14)%Z ltac:(sbp). msb F_5285c0 D_5285c0 (k+15)%Z ltac:(sbp).
      stepn F_5285c4 D_5285c4.                            (* [comment removed for export] *)
      mk_eq. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma t4_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x560e70 : word) (MK k) rom) (mkst regs' (0x5611c8 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_5282f8 D_5282f8.                          (* [comment removed for export] *)
        stepb_ft F_5282fc D_5282fc ltac:(cond).           (* [comment removed for export] *)
        stepn F_528300 D_528300.                          (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x56119c : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_5282f8 D_5282f8.
          stepb_tk F_5282fc D_5282fc ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; diet_eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma b8_tail : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x561194 : word) (MK k) rom) (mkst regs' (0x5611c8 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_52861c D_52861c.                          (* [comment removed for export] *)
        stepb_tk F_528620 D_528620 ltac:(cond).           (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x56119c : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_52861c D_52861c.
          stepb_ft F_528620 D_528620 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; diet_eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma t8_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x560e68 : word) (MK k) rom)
                   (mkst regs' (0x5611c8 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x560e70 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_5282f0 D_5282f0.                        (* [comment removed for export] *)
          stepb_ft F_5282f4 D_5282f4 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; diet_eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x561148 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_5282f0 D_5282f0.
          stepb_tk F_5282f4 D_5282f4 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x561194 : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; diet_eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL8. replace (k + 8 + Z.land m 4)%Z with (k + 8 + Z.land m 4)%Z by lia.
          split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; diet_eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma b16_tail : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x561140 : word) (MK k) rom)
                   (mkst regs' (0x5611c8 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x560e70 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_5285c8 D_5285c8.                        (* [comment removed for export] *)
          stepb_tk F_5285cc D_5285cc ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; diet_eassumption.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x561148 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_5285c8 D_5285c8.
          stepb_ft F_5285cc D_5285cc ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x561194 : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; diet_eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL8. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; diet_eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma t16_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 32)%Z -> (0 <= k)%Z ->
    (k + Z.land m 16 + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x560e60 : word) (MK k) rom)
                   (mkst regs' (0x5611c8 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk Hkn.
    destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x560e68 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_5282e8 D_5282e8.                        (* [comment removed for export] *)
          stepb_ft F_5282ec D_5282ec ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; diet_eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x5610b4 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_5282e8 D_5282e8.
          stepb_tk F_5282ec D_5282ec ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x561140 : word) (MK (k + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; diet_eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; diet_eassumption.
  Qed.

End MIS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
