(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep OSSVerify.Proofs.glaze.binary_reflection.lib.PuLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMemcpyAL.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.PuKeep.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac lia ::= lia_nd.
#[local] Ltac not_kept ::= not_kept_fast.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


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
  Lemma b1_run : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    (0 <= k)%Z -> (k + 1 = n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x736a8 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k Hret H1 H11 H13 Hk Hkn.
    eexists. split.
    - mlbu F_73654 D_73654 k.                      (* [comment removed for export] *)
      msb F_73658 D_73658 k ltac:(apply sb_val_plain).   (* [comment removed for export] *)
      replace (k + 1)%Z with n by lia.
      stepret F_7365c D_7365c ret ltac:(exact H1).
      pu_refl.
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
      msteps RSEGS (mkst regs (0x73670 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_7361c D_7361c.                          (* [comment removed for export] *)
        stepb_ft F_73620 D_73620 ltac:(cond).           (* [comment removed for export] *)
        stepn F_73624 D_73624.                          (* [comment removed for export] *)
        stepb_ft F_73628 D_73628 ltac:(cond).           (* [comment removed for export] *)
        stepret F_7362c D_7362c ret ltac:(exact H1).
        mk_eq. pu_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x736a8 : word) (MK k) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
      + eexists. split.
        * stepn F_7361c D_7361c.
          stepb_ft F_73620 D_73620 ltac:(cond).
          stepn F_73624 D_73624.
          stepb_tk F_73628 D_73628 ltac:(cond).         (* [comment removed for export] *)
          pu_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
      + cbv beta. intros r1 (R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_7361c D_7361c.
        stepb_tk F_73620 D_73620 ltac:(cond).           (* [comment removed for export] *)
        mlbu F_73630 D_73630 k.                         (* [comment removed for export] *)
        mlbu F_73634 D_73634 (k + 1)%Z.                 (* [comment removed for export] *)
        stepn F_73638 D_73638.                          (* [comment removed for export] *)
        stepn F_7363c D_7363c.                          (* [comment removed for export] *)
        msb F_73640 D_73640 k ltac:(apply sb_val_plain).          (* [comment removed for export] *)
        msb F_73644 D_73644 (k + 1)%Z ltac:(apply sb_val_plain).  (* [comment removed for export] *)
        stepn F_73648 D_73648.                          (* [comment removed for export] *)
        stepn F_7364c D_7364c.                          (* [comment removed for export] *)
        stepb_tk F_73650 D_73650 ltac:(cond).           (* [comment removed for export] *)
        stepret F_7362c D_7362c ret ltac:(exact H1).
        mk_eq. pu_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x736a8 : word) (MK (k + 2)) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
      + eexists. split.
        * stepn F_7361c D_7361c.
          stepb_tk F_73620 D_73620 ltac:(cond).
          mlbu F_73630 D_73630 k.
          mlbu F_73634 D_73634 (k + 1)%Z.
          stepn F_73638 D_73638.
          stepn F_7363c D_7363c.
          msb F_73640 D_73640 k ltac:(apply sb_val_plain).
          msb F_73644 D_73644 (k + 1)%Z ltac:(apply sb_val_plain).
          stepn F_73648 D_73648.
          stepn F_7364c D_7364c.
          stepb_ft F_73650 D_73650 ltac:(cond).         (* [comment removed for export] *)
          mk_eq. pu_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; rwH; rewrite ?at_addi; reflexivity
                                 | gres; rwH; rewrite ?at_addi; reflexivity | solve_keeps].
      + cbv beta. intros r1 (R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
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
      msteps RSEGS (mkst regs (0x7342c : word) (MK k) rom)
                   (mkst regs' (0x73670 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 4) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
    - eexists. split.
      + stepn F_733d8 D_733d8.                          (* [comment removed for export] *)
        stepb_tk F_733dc D_733dc ltac:(cond).           (* [comment removed for export] *)
        mk_eq. pu_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_733d8 D_733d8.
        stepb_ft F_733dc D_733dc ltac:(cond).           (* [comment removed for export] *)
        mlw F_733e0 D_733e0 k.                          (* [comment removed for export] *)
        stepn F_733e4 D_733e4.                          (* [comment removed for export] *)
        msw F_733e8 D_733e8 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).   (* [comment removed for export] *)
        stepn F_733ec D_733ec.                          (* [comment removed for export] *)
        stepn F_733f0 D_733f0.                          (* [comment removed for export] *)
        mk_eq. pu_refl.
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
      msteps RSEGS (mkst regs (0x7340c : word) (MK k) rom)
                   (mkst regs' (0x7342c : word) (MK (k + e8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + e8)
      /\ getr regs' 13 = at_ dst (k + e8) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
    - eexists. split.
      + stepn F_733b8 D_733b8.                          (* [comment removed for export] *)
        stepb_tk F_733bc D_733bc ltac:(cond).           (* [comment removed for export] *)
        mk_eq. pu_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_733b8 D_733b8.
        stepb_ft F_733bc D_733bc ltac:(cond).
        mlw F_733c0 D_733c0 k.                          (* [comment removed for export] *)
        mlw F_733c4 D_733c4 (k + 4)%Z.                  (* [comment removed for export] *)
        msw F_733c8 D_733c8 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).         (* [comment removed for export] *)
        msw F_733cc D_733cc (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        stepn F_733d0 D_733d0.                          (* [comment removed for export] *)
        stepn F_733d4 D_733d4.                          (* [comment removed for export] *)
        mk_eq. pu_refl.
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
      msteps RSEGS (mkst regs (0x733dc : word) (MK k) rom)
                   (mkst regs' (0x7340c : word) (MK (k + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 13 = at_ dst (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof using Hn0 HOK.
    induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
    - (* [comment removed for export] *)
      eexists. split.
      + mlw F_73388 D_73388 k.                          (* [comment removed for export] *)
        mlw F_7338c D_7338c (k + 4)%Z.                  (* [comment removed for export] *)
        mlw F_73390 D_73390 (k + 8)%Z.                  (* [comment removed for export] *)
        mlw F_73394 D_73394 (k + 12)%Z.                 (* [comment removed for export] *)
        stepn F_73398 D_73398.                          (* [comment removed for export] *)
        stepn F_7339c D_7339c.                          (* [comment removed for export] *)
        msw F_733a0 D_733a0 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).          (* [comment removed for export] *)
        msw F_733a4 D_733a4 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        msw F_733a8 D_733a8 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        msw F_733ac D_733ac (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        stepn F_733b0 D_733b0.                          (* [comment removed for export] *)
        stepb_ft F_733b4 D_733b4 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        mk_eq. pu_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
        * unfold v_addi. unorm. f_equal. lia.
        * solve_keeps.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x733dc : word) (MK (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * mlw F_73388 D_73388 k.
          mlw F_7338c D_7338c (k + 4)%Z.
          mlw F_73390 D_73390 (k + 8)%Z.
          mlw F_73394 D_73394 (k + 12)%Z.
          stepn F_73398 D_73398.
          stepn F_7339c D_7339c.
          msw F_733a0 D_733a0 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_733a4 D_733a4 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_733a8 D_733a8 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_733ac D_733ac (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          stepn F_733b0 D_733b0.
          stepb_tk F_733b4 D_733b4 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          mk_eq. pu_refl.
        * cbv beta. repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
          -- unfold v_addi. unorm. f_equal. lia.
          -- solve_keeps.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
        destruct (IH r1 ret (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
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
      msteps RSEGS (mkst regs (0x733d0 : word) (MK k) rom)
                   (mkst regs' (0x7340c : word) (MK (n - (n - k) mod 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (n - k) mod 16)
      /\ getr regs' 13 = at_ dst (n - (n - k) mod 16)
      /\ getr regs' 12 = Z_to_bv 64 ((n - k) mod 16) /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k H1 H11 H13 H12 Hk.
    destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_7337c D_7337c.                          (* [comment removed for export] *)
        stepb_tk F_73380 D_73380 ltac:(cond).           (* [comment removed for export] *)
        replace (n - (n - k) mod 16)%Z with k by (rewrite Z.mod_small; lia).
        pu_refl.
      + rewrite (Z.mod_small (n - k) 16) by lia. replace (n - (n - k))%Z with k by lia.
        repeat split; gres; rwH; try reflexivity. solve_keeps.
    - set (q := Z.to_nat ((n - k) / 16 - 1)).
      assert (Hq : (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z).
      { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
        pose proof (Z.div_mod (n - k) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)). lia. }
      assert (Hk' : (k + 16 * (Z.of_nat q + 1) = n - (n - k) mod 16)%Z).
      { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
        pose proof (Z.div_mod (n - k) 16 ltac:(lia)). lia. }
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x733dc : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
                         /\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * stepn F_7337c D_7337c.                        (* [comment removed for export] *)
          stepb_ft F_73380 D_73380 ltac:(cond).         (* [comment removed for export] *)
          stepn F_73384 D_73384.                        (* [comment removed for export] *)
          pu_refl.
        * cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
        destruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P).
        exists r2. rewrite <- Hk'. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
        decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
  Qed.


End AL.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbMemcpyAL.
Module UbMemcpyMIS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase UbMemcpyAL OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.PuKeep.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac not_kept ::= not_kept_fast.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


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
      msteps RSEGS (mkst regs (0x73644 : word) (MK k) rom) (mkst regs' (0x73670 : word) (MK (k + 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. eexists. split.
    - mlbu F_735f0 D_735f0 k. mlbu F_735f4 D_735f4 (k+1)%Z. mlbu F_735f8 D_735f8 (k+2)%Z. mlbu F_735fc D_735fc (k+3)%Z.
      stepn F_73600 D_73600.                            (* [comment removed for export] *)
      stepn F_73604 D_73604.                            (* [comment removed for export] *)
      msb F_73608 D_73608 k ltac:(sbp). msb F_7360c D_7360c (k+1)%Z ltac:(sbp).
      msb F_73610 D_73610 (k+2)%Z ltac:(sbp). msb F_73614 D_73614 (k+3)%Z ltac:(sbp).
      stepn F_73618 D_73618.                            (* [comment removed for export] *)
      mk_eq. pu_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma b8_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 8 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x735f0 : word) (MK k) rom) (mkst regs' (0x7363c : word) (MK (k + 8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. eexists. split.
    - mlbu F_7359c D_7359c k. mlbu F_735a0 D_735a0 (k+1)%Z. mlbu F_735a4 D_735a4 (k+2)%Z. mlbu F_735a8 D_735a8 (k+3)%Z.
      mlbu F_735ac D_735ac (k+4)%Z. mlbu F_735b0 D_735b0 (k+5)%Z. mlbu F_735b4 D_735b4 (k+6)%Z. mlbu F_735b8 D_735b8 (k+7)%Z.
      stepn F_735bc D_735bc.                            (* [comment removed for export] *)
      msb F_735c0 D_735c0 k ltac:(sbp). msb F_735c4 D_735c4 (k+1)%Z ltac:(sbp).
      msb F_735c8 D_735c8 (k+2)%Z ltac:(sbp). msb F_735cc D_735cc (k+3)%Z ltac:(sbp).
      stepn F_735d0 D_735d0.                            (* [comment removed for export] *)
      msb F_735d4 D_735d4 (k+4)%Z ltac:(sbp). msb F_735d8 D_735d8 (k+5)%Z ltac:(sbp).
      msb F_735dc D_735dc (k+6)%Z ltac:(sbp). msb F_735e0 D_735e0 (k+7)%Z ltac:(sbp).
      stepn F_735e4 D_735e4.                            (* [comment removed for export] *)
      mk_eq. pu_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma b16_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 16 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x7355c : word) (MK k) rom) (mkst regs' (0x735e8 : word) (MK (k + 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. eexists. split.
    - mlbu F_73508 D_73508 k. mlbu F_7350c D_7350c (k+1)%Z. mlbu F_73510 D_73510 (k+2)%Z. mlbu F_73514 D_73514 (k+3)%Z.
      mlbu F_73518 D_73518 (k+4)%Z. mlbu F_7351c D_7351c (k+5)%Z. mlbu F_73520 D_73520 (k+6)%Z. mlbu F_73524 D_73524 (k+7)%Z.
      msb F_73528 D_73528 k ltac:(sbp). msb F_7352c D_7352c (k+1)%Z ltac:(sbp).
      msb F_73530 D_73530 (k+2)%Z ltac:(sbp). msb F_73534 D_73534 (k+3)%Z ltac:(sbp).
      mlbu F_73538 D_73538 (k+8)%Z. mlbu F_7353c D_7353c (k+9)%Z. mlbu F_73540 D_73540 (k+10)%Z. mlbu F_73544 D_73544 (k+11)%Z.
      msb F_73548 D_73548 (k+4)%Z ltac:(sbp). msb F_7354c D_7354c (k+5)%Z ltac:(sbp).
      msb F_73550 D_73550 (k+6)%Z ltac:(sbp). msb F_73554 D_73554 (k+7)%Z ltac:(sbp).
      mlbu F_73558 D_73558 (k+12)%Z. mlbu F_7355c D_7355c (k+13)%Z. mlbu F_73560 D_73560 (k+14)%Z. mlbu F_73564 D_73564 (k+15)%Z.
      stepn F_73568 D_73568.                            (* [comment removed for export] *)
      msb F_7356c D_7356c (k+8)%Z ltac:(sbp). msb F_73570 D_73570 (k+9)%Z ltac:(sbp).
      msb F_73574 D_73574 (k+10)%Z ltac:(sbp). msb F_73578 D_73578 (k+11)%Z ltac:(sbp).
      stepn F_7357c D_7357c.                            (* [comment removed for export] *)
      msb F_73580 D_73580 (k+12)%Z ltac:(sbp). msb F_73584 D_73584 (k+13)%Z ltac:(sbp).
      msb F_73588 D_73588 (k+14)%Z ltac:(sbp). msb F_7358c D_7358c (k+15)%Z ltac:(sbp).
      stepn F_73590 D_73590.                            (* [comment removed for export] *)
      mk_eq. pu_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma t4_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x73318 : word) (MK k) rom) (mkst regs' (0x73670 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_732c4 D_732c4.                          (* [comment removed for export] *)
        stepb_ft F_732c8 D_732c8 ltac:(cond).           (* [comment removed for export] *)
        stepn F_732cc D_732cc.                          (* [comment removed for export] *)
        mk_eq. pu_refl.
      + post.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x73644 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_732c4 D_732c4.
          stepb_tk F_732c8 D_732c8 ltac:(cond).         (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma b8_tail : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x7363c : word) (MK k) rom) (mkst regs' (0x73670 : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_735e8 D_735e8.                          (* [comment removed for export] *)
        stepb_tk F_735ec D_735ec ltac:(cond).           (* [comment removed for export] *)
        mk_eq. pu_refl.
      + post.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x73644 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_735e8 D_735e8.
          stepb_ft F_735ec D_735ec ltac:(cond).         (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma t8_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x73310 : word) (MK k) rom)
                   (mkst regs' (0x73670 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x73318 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_732bc D_732bc.                        (* [comment removed for export] *)
          stepb_ft F_732c0 D_732c0 ltac:(cond).         (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x735f0 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_732bc D_732bc.
          stepb_tk F_732c0 D_732c0 ltac:(cond).         (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x7363c : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
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
      msteps RSEGS (mkst regs (0x735e8 : word) (MK k) rom)
                   (mkst regs' (0x73670 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x73318 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_73594 D_73594.                        (* [comment removed for export] *)
          stepb_tk F_73598 D_73598 ltac:(cond).         (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x735f0 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_73594 D_73594.
          stepb_ft F_73598 D_73598 ltac:(cond).         (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x7363c : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL8. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma t16_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 32)%Z -> (0 <= k)%Z ->
    (k + Z.land m 16 + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x73308 : word) (MK k) rom)
                   (mkst regs' (0x73670 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k m H1 H11 H13 H12 Hm Hk Hkn.
    destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x73310 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_732b4 D_732b4.                        (* [comment removed for export] *)
          stepb_ft F_732b8 D_732b8 ltac:(cond).         (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x7355c : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_732b4 D_732b4.
          stepb_tk F_732b8 D_732b8 ltac:(cond).         (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x735e8 : word) (MK (k + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

End MIS.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbMemcpyMIS.
Module UbMemcpyC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase UbMemcpyAL UbMemcpyMIS OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.PuKeep.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac not_kept ::= not_kept_fast.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Section C1.
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
  Ltac m24 := eapply (merge_s24 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  Lemma c1_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x73324 : word) (MK k) rom) (mkst regs' (0x734f0 : word) (MK (k + 3)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 3)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 3)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 16 /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
    - mlw F_732d0 D_732d0 k.                            (* [comment removed for export] *)
      stepn F_732d4 D_732d4.                            (* [comment removed for export] *)
      stepb_ft F_732d8 D_732d8 ltac:(cond).             (* [comment removed for export] *)
      stepn F_732dc D_732dc.                            (* [comment removed for export] *)
      stepb_tk F_732e0 D_732e0 ltac:(cond).             (* [comment removed for export] *)
      stepn F_73478 D_73478.                            (* [comment removed for export] *)
      stepn F_7347c D_7347c.                            (* [comment removed for export] *)
      stepn F_73480 D_73480.                            (* [comment removed for export] *)
      msb F_73484 D_73484 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).         (* [comment removed for export] *)
      msb F_73488 D_73488 (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
      msb F_7348c D_7348c (k + 2)%Z ltac:(eapply (sb_val_srli16 _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
      stepn F_73490 D_73490.                            (* [comment removed for export] *)
      stepn F_73494 D_73494.                            (* [comment removed for export] *)
      stepn F_73498 D_73498.                            (* [comment removed for export] *)
      mk_eq. pu_refl.
    - post. unfold v_addi. unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma c1_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 16 ->
    (ja = kk + 13)%Z -> (jw = kk - 3)%Z -> (3 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 1 <= n - kk < 16 * (Z.of_nat q + 1) + 17)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x734f0 : word) (MK kk) rom)
                   (mkst regs' (0x73550 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 13)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof using Hn0 HOK.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - eexists. split.
      + stepn F_7349c D_7349c.                          (* [comment removed for export] *)
        mlw F_734a0 D_734a0 (kk + 1)%Z.                 (* [comment removed for export] *)
        mlw F_734a4 D_734a4 (kk + 5)%Z.                 (* [comment removed for export] *)
        mlw F_734a8 D_734a8 (kk + 9)%Z.                 (* [comment removed for export] *)
        mlw F_734ac D_734ac (kk + 13)%Z.                (* [comment removed for export] *)
        stepn F_734b0 D_734b0. stepn F_734b4 D_734b4. stepn F_734b8 D_734b8.
        stepn F_734bc D_734bc. stepn F_734c0 D_734c0. stepn F_734c4 D_734c4.
        stepn F_734c8 D_734c8. stepn F_734cc D_734cc. stepn F_734d0 D_734d0.
        stepn F_734d4 D_734d4. stepn F_734d8 D_734d8.
        stepn F_734dc D_734dc.                          (* [comment removed for export] *)
        msw F_734e0 D_734e0 kk ltac:(m24).
        msw F_734e4 D_734e4 (kk + 4)%Z ltac:(m24).
        msw F_734e8 D_734e8 (kk + 8)%Z ltac:(m24).
        msw F_734ec D_734ec (kk + 12)%Z ltac:(m24).
        stepn F_734f0 D_734f0.                          (* [comment removed for export] *)
        stepn F_734f4 D_734f4.                          (* [comment removed for export] *)
        stepb_ft F_734f8 D_734f8 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        mk_eq. pu_refl.
      + post. unfold v_addi. unorm. f_equal. lia.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x734f0 : word) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 13) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 13) 4)
                         /\ getr r 15 = Z_to_bv 64 16 /\ keeps regs r)).
      + eexists. split.
        * stepn F_7349c D_7349c.
          mlw F_734a0 D_734a0 (kk + 1)%Z.
          mlw F_734a4 D_734a4 (kk + 5)%Z.
          mlw F_734a8 D_734a8 (kk + 9)%Z.
          mlw F_734ac D_734ac (kk + 13)%Z.
          stepn F_734b0 D_734b0. stepn F_734b4 D_734b4. stepn F_734b8 D_734b8.
          stepn F_734bc D_734bc. stepn F_734c0 D_734c0. stepn F_734c4 D_734c4.
          stepn F_734c8 D_734c8. stepn F_734cc D_734cc. stepn F_734d0 D_734d0.
          stepn F_734d4 D_734d4. stepn F_734d8 D_734d8.
          stepn F_734dc D_734dc.
          msw F_734e0 D_734e0 kk ltac:(m24).
          msw F_734e4 D_734e4 (kk + 4)%Z ltac:(m24).
          msw F_734e8 D_734e8 (kk + 8)%Z ltac:(m24).
          msw F_734ec D_734ec (kk + 12)%Z ltac:(m24).
          stepn F_734f0 D_734f0.
          stepn F_734f4 D_734f4.
          stepb_tk F_734f8 D_734f8 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          mk_eq. pu_refl.
        * cbv beta. post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
        destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 13)%Z (kk + 13)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma c1_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 13) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps RSEGS (mkst regs (0x73550 : word) (MK kk) rom)
                   (mkst regs' (0x73670 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x73310 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_734fc D_734fc.                        (* [comment removed for export] *)
          stepn F_73500 D_73500.                        (* [comment removed for export] *)
          stepb_tk F_73504 D_73504 ltac:(cond).         (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x7355c : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_734fc D_734fc.
          stepn F_73500 D_73500.
          stepb_ft F_73504 D_73504 ltac:(cond).         (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x735e8 : word) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma c1_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps RSEGS (mkst regs (0x73324 : word) (MK k) rom)
                   (mkst regs' (0x73670 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 1 <= n - (k + 3) < 16 * (Z.of_nat q + 1) + 17)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 3 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    destruct (c1_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
    destruct (c1_loop q r1 ret (k + 3)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
    fold kk in RUN2, Q11, Q13, Q12.
    destruct (c1_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | repeat split; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C1.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbMemcpyC1.
Module UbMemcpyC2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase UbMemcpyAL UbMemcpyMIS OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.PuKeep.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac not_kept ::= not_kept_fast.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Section C2.
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
  Ltac m16 := eapply (merge_s16 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma c2_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x73324 : word) (MK k) rom) (mkst regs' (0x73354 : word) (MK (k + 2)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 2)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 2)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 17 /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
    - mlw F_732d0 D_732d0 k.                            (* [comment removed for export] *)
      stepn F_732d4 D_732d4.                            (* [comment removed for export] *)
      stepb_ft F_732d8 D_732d8 ltac:(cond).             (* [comment removed for export] *)
      stepn F_732dc D_732dc.                            (* [comment removed for export] *)
      stepb_ft F_732e0 D_732e0 ltac:(cond).             (* [comment removed for export] *)
      stepn F_732e4 D_732e4.                            (* [comment removed for export] *)
      stepn F_732e8 D_732e8.                            (* [comment removed for export] *)
      msb F_732ec D_732ec k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).        (* [comment removed for export] *)
      msb F_732f0 D_732f0 (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
      stepn F_732f4 D_732f4.                            (* [comment removed for export] *)
      stepn F_732f8 D_732f8.                            (* [comment removed for export] *)
      stepn F_732fc D_732fc.                            (* [comment removed for export] *)
      mk_eq. pu_refl.
    - post. unfold v_addi. unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma c2_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 17 ->
    (ja = kk + 14)%Z -> (jw = kk - 2)%Z -> (2 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 2 <= n - kk < 16 * (Z.of_nat q + 1) + 18)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x73354 : word) (MK kk) rom)
                   (mkst regs' (0x733b4 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 14)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof using Hn0 HOK.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - eexists. split.
      + stepn F_73300 D_73300.                          (* [comment removed for export] *)
        mlw F_73304 D_73304 (kk + 2)%Z.                 (* [comment removed for export] *)
        mlw F_73308 D_73308 (kk + 6)%Z.                 (* [comment removed for export] *)
        mlw F_7330c D_7330c (kk + 10)%Z.                (* [comment removed for export] *)
        mlw F_73310 D_73310 (kk + 14)%Z.                (* [comment removed for export] *)
        stepn F_73314 D_73314. stepn F_73318 D_73318. stepn F_7331c D_7331c.   (* [comment removed for export] *)
        stepn F_73320 D_73320. stepn F_73324 D_73324. stepn F_73328 D_73328.   (* [comment removed for export] *)
        stepn F_7332c D_7332c. stepn F_73330 D_73330. stepn F_73334 D_73334.   (* [comment removed for export] *)
        stepn F_73338 D_73338. stepn F_7333c D_7333c.                          (* [comment removed for export] *)
        stepn F_73340 D_73340.                          (* [comment removed for export] *)
        msw F_73344 D_73344 kk ltac:(m16).              (* [comment removed for export] *)
        msw F_73348 D_73348 (kk + 4)%Z ltac:(m16).      (* [comment removed for export] *)
        msw F_7334c D_7334c (kk + 8)%Z ltac:(m16).      (* [comment removed for export] *)
        msw F_73350 D_73350 (kk + 12)%Z ltac:(m16).     (* [comment removed for export] *)
        stepn F_73354 D_73354.                          (* [comment removed for export] *)
        stepn F_73358 D_73358.                          (* [comment removed for export] *)
        stepb_ft F_7335c D_7335c ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        mk_eq. pu_refl.
      + post. unfold v_addi. unorm. f_equal. lia.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x73354 : word) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 14) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 14) 4)
                         /\ getr r 15 = Z_to_bv 64 17 /\ keeps regs r)).
      + eexists. split.
        * stepn F_73300 D_73300.
          mlw F_73304 D_73304 (kk + 2)%Z.
          mlw F_73308 D_73308 (kk + 6)%Z.
          mlw F_7330c D_7330c (kk + 10)%Z.
          mlw F_73310 D_73310 (kk + 14)%Z.
          stepn F_73314 D_73314. stepn F_73318 D_73318. stepn F_7331c D_7331c.
          stepn F_73320 D_73320. stepn F_73324 D_73324. stepn F_73328 D_73328.
          stepn F_7332c D_7332c. stepn F_73330 D_73330. stepn F_73334 D_73334.
          stepn F_73338 D_73338. stepn F_7333c D_7333c.
          stepn F_73340 D_73340.
          msw F_73344 D_73344 kk ltac:(m16).
          msw F_73348 D_73348 (kk + 4)%Z ltac:(m16).
          msw F_7334c D_7334c (kk + 8)%Z ltac:(m16).
          msw F_73350 D_73350 (kk + 12)%Z ltac:(m16).
          stepn F_73354 D_73354.
          stepn F_73358 D_73358.
          stepb_tk F_7335c D_7335c ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          mk_eq. pu_refl.
        * cbv beta. post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
        destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 14)%Z (kk + 14)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma c2_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 14) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps RSEGS (mkst regs (0x733b4 : word) (MK kk) rom)
                   (mkst regs' (0x73670 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x73310 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_73360 D_73360.                        (* [comment removed for export] *)
          stepn F_73364 D_73364.                        (* [comment removed for export] *)
          stepb_tk F_73368 D_73368 ltac:(cond).         (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x7355c : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_73360 D_73360.
          stepn F_73364 D_73364.
          stepb_ft F_73368 D_73368 ltac:(cond).         (* [comment removed for export] *)
          stepn F_7336c D_7336c.                        (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x735e8 : word) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma c2_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps RSEGS (mkst regs (0x73324 : word) (MK k) rom)
                   (mkst regs' (0x73670 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 2 <= n - (k + 2) < 16 * (Z.of_nat q + 1) + 18)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 2 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    destruct (c2_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
    destruct (c2_loop q r1 ret (k + 2)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
    fold kk in RUN2, Q11, Q13, Q12.
    destruct (c2_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | repeat split; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C2.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbMemcpyC2.
Module UbMemcpyC3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase UbMemcpyAL UbMemcpyMIS OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.PuKeep.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac not_kept ::= not_kept_fast.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Section C3.
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
  Ltac m8 := eapply (merge_s8 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  Lemma c3_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x73324 : word) (MK k) rom) (mkst regs' (0x7345c : word) (MK (k + 1)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 1)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 1)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 18 /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
    - mlw F_732d0 D_732d0 k.                            (* [comment removed for export] *)
      stepn F_732d4 D_732d4.                            (* [comment removed for export] *)
      stepb_tk F_732d8 D_732d8 ltac:(cond).             (* [comment removed for export] *)
      msb F_733f4 D_733f4 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).        (* [comment removed for export] *)
      stepn F_733f8 D_733f8.                            (* [comment removed for export] *)
      stepn F_733fc D_733fc.                            (* [comment removed for export] *)
      stepn F_73400 D_73400.                            (* [comment removed for export] *)
      stepn F_73404 D_73404.                            (* [comment removed for export] *)
      mk_eq. pu_refl.
    - post. unfold v_addi. unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma c3_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 18 ->
    (ja = kk + 15)%Z -> (jw = kk - 1)%Z -> (1 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 3 <= n - kk < 16 * (Z.of_nat q + 1) + 19)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x7345c : word) (MK kk) rom)
                   (mkst regs' (0x734bc : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 15)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof using Hn0 HOK.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - eexists. split.
      + stepn F_73408 D_73408.                          (* [comment removed for export] *)
        mlw F_7340c D_7340c (kk + 3)%Z.                 (* [comment removed for export] *)
        mlw F_73410 D_73410 (kk + 7)%Z.                 (* [comment removed for export] *)
        mlw F_73414 D_73414 (kk + 11)%Z.                (* [comment removed for export] *)
        mlw F_73418 D_73418 (kk + 15)%Z.                (* [comment removed for export] *)
        stepn F_7341c D_7341c. stepn F_73420 D_73420. stepn F_73424 D_73424.
        stepn F_73428 D_73428. stepn F_7342c D_7342c. stepn F_73430 D_73430.
        stepn F_73434 D_73434. stepn F_73438 D_73438. stepn F_7343c D_7343c.
        stepn F_73440 D_73440. stepn F_73444 D_73444.
        stepn F_73448 D_73448.                          (* [comment removed for export] *)
        msw F_7344c D_7344c kk ltac:(m8).
        msw F_73450 D_73450 (kk + 4)%Z ltac:(m8).
        msw F_73454 D_73454 (kk + 8)%Z ltac:(m8).
        msw F_73458 D_73458 (kk + 12)%Z ltac:(m8).
        stepn F_7345c D_7345c.                          (* [comment removed for export] *)
        stepn F_73460 D_73460.                          (* [comment removed for export] *)
        stepb_ft F_73464 D_73464 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        mk_eq. pu_refl.
      + post. unfold v_addi. unorm. f_equal. lia.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x7345c : word) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 15) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 15) 4)
                         /\ getr r 15 = Z_to_bv 64 18 /\ keeps regs r)).
      + eexists. split.
        * stepn F_73408 D_73408.
          mlw F_7340c D_7340c (kk + 3)%Z.
          mlw F_73410 D_73410 (kk + 7)%Z.
          mlw F_73414 D_73414 (kk + 11)%Z.
          mlw F_73418 D_73418 (kk + 15)%Z.
          stepn F_7341c D_7341c. stepn F_73420 D_73420. stepn F_73424 D_73424.
          stepn F_73428 D_73428. stepn F_7342c D_7342c. stepn F_73430 D_73430.
          stepn F_73434 D_73434. stepn F_73438 D_73438. stepn F_7343c D_7343c.
          stepn F_73440 D_73440. stepn F_73444 D_73444.
          stepn F_73448 D_73448.
          msw F_7344c D_7344c kk ltac:(m8).
          msw F_73450 D_73450 (kk + 4)%Z ltac:(m8).
          msw F_73454 D_73454 (kk + 8)%Z ltac:(m8).
          msw F_73458 D_73458 (kk + 12)%Z ltac:(m8).
          stepn F_7345c D_7345c.
          stepn F_73460 D_73460.
          stepb_tk F_73464 D_73464 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          mk_eq. pu_refl.
        * cbv beta. post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
        destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 15)%Z (kk + 15)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma c3_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 15) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps RSEGS (mkst regs (0x734bc : word) (MK kk) rom)
                   (mkst regs' (0x73670 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x73310 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_73468 D_73468.                        (* [comment removed for export] *)
          stepn F_7346c D_7346c.                        (* [comment removed for export] *)
          stepb_tk F_73470 D_73470 ltac:(cond).         (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x7355c : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_73468 D_73468.
          stepn F_7346c D_7346c.
          stepb_ft F_73470 D_73470 ltac:(cond).
          stepn F_73474 D_73474.                        (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x735e8 : word) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma c3_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps RSEGS (mkst regs (0x73324 : word) (MK k) rom)
                   (mkst regs' (0x73670 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 3 <= n - (k + 1) < 16 * (Z.of_nat q + 1) + 19)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 1 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    destruct (c3_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
    destruct (c3_loop q r1 ret (k + 1)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
    fold kk in RUN2, Q11, Q13, Q12.
    destruct (c3_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | repeat split; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C3.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbMemcpyC3.
Module UbMemcpy.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase UbMemcpyAL UbMemcpyMIS UbMemcpyC1 UbMemcpyC2 UbMemcpyC3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.PuKeep.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac lia ::= lia_nd.
#[local] Ltac not_kept ::= not_kept_fast.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Section ALL.
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
  (* [comment removed for export] *)
  Ltac conda := rwH; unfold at_; cond.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_finish : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x733d0 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k Hret H1 H11 H13 H12 Hk.
    set (m := ((n - k) mod 16)%Z).
    pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)) as Hm16.
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
    assert (Hl16 : Z.land m 16 = 0%Z) by (destruct B16 as [E|E]; [exact E|exfalso; lia]).
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x7340c : word) (MK (n - m)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al16_run _ _ _ _ _ rom HOK regs ret k H1 H11 H13 H12 Hk) as (r & R & P). exists r.
      subst m. split; [exact R|]. decompose [and] P. repeat split; try assumption. }
    cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x7342c : word) (MK (n - m + Z.land m 8)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al8_run _ _ _ _ _ rom HOK r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P).
      exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. intros r3 (T1 & T11 & T13 & T12 & K3).
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x73670 : word) (MK (n - m + Z.land m 8 + Z.land m 4)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8 + Z.land m 4) /\ getr r 13 = at_ dst (n - m + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al4_run _ _ _ _ _ rom HOK r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P).
      exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. intros r4 (U1 & U11 & U13 & U12 & K4).
    destruct (t2_run _ _ _ _ _ rom HOK r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r & R & P).
    exists r. split; [exact R | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mis_run : forall regs (ret : word) k q,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 15 = Z_to_bv 64 q -> (q = 1 \/ q = 2 \/ q = 3)%Z ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x73300 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof using Hn0 HOK.
    intros regs ret k q Hret H1 H11 H13 H12 H15 Hq Hk.
    destruct (Z.lt_ge_cases (n - k) 32) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      destruct (bits_lt32 (n - k) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
      assert (0 <= Z.land (n - k) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 4)%Z by (apply Z.land_nonneg; lia).
      assert (0 <= Z.land (n - k) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 1)%Z by (apply Z.land_nonneg; lia).
      assert (0 <= Z.land (n - k) 16)%Z by (apply Z.land_nonneg; lia).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x73308 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
      + eexists. split.
        * stepn F_732ac D_732ac.                        (* [comment removed for export] *)
          stepb_ft F_732b0 D_732b0 ltac:(cond).         (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        set (m := (n - k)%Z) in *.
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x73670 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
                           /\ getr r 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (t16_run _ _ _ _ _ rom HOK r1 ret k m R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (t2_run _ _ _ _ _ rom HOK r2 ret (k + Z.land m 16 + Z.land m 8 + Z.land m 4)%Z m Hret S1 S11 S13 S12
                      ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN & K3).
          exists r3. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x73324 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
                         /\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
      + eexists. split.
        * stepn F_732ac D_732ac.                        (* [comment removed for export] *)
          stepb_tk F_732b0 D_732b0 ltac:(cond).         (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
        assert (CASE : exists regs' m,
          msteps RSEGS (mkst r1 (0x73324 : word) (MK k) rom)
                       (mkst regs' (0x73670 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
          /\ (0 <= m < 32)%Z
          /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
          /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
          /\ getr regs' 12 = Z_to_bv 64 m /\ keeps r1 regs').
        { destruct Hq as [-> | [-> | ->]].
          - apply (c1_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
          - apply (c2_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
          - apply (c3_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia. }
        destruct CASE as (r2 & m & RUN & Hm & S1 & S11 & S13 & S12 & K2).
        destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
        assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
        destruct (t2_run _ _ _ _ _ rom HOK r2 ret (n - (Z.land m 2 + Z.land m 1))%Z m Hret S1 S11 S13 S12
                    ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN3 & K3).
        exists r3. split; [eapply msteps_trans; [exact RUN | exact RUN3] |].
        eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma j_run : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x732f8 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof using Hnwd Hn0 HOK.
    intros regs ret k Hret H1 H11 H13 H12 Hk.
    pose proof (u64_range dst).
    set (q := ((bv_unsigned dst + k) mod 4)%Z).
    pose proof (Z.mod_pos_bound (bv_unsigned dst + k) 4 ltac:(lia)) as Hq4.
    destruct (Z.eq_dec q 0) as [Hq0|Hq0].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x733d0 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
      + eexists. split.
        * stepn F_732a4 D_732a4.                        (* [comment removed for export] *)
          stepb_tk F_732a8 D_732a8 ltac:(conda).        (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (al_finish r1 ret k Hret R1 R11 R13 R12 Hk) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x73300 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
                         /\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
      + eexists. split.
        * stepn F_732a4 D_732a4.
          stepb_ft F_732a8 D_732a8 ltac:(conda).        (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post. unfold v_andi, at_. subst q. rewrite <- land_3 by lia. unorm.
          change (bv_wrap 64 3) with 3%Z. reflexivity.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
        destruct (mis_run r1 ret k q Hret R1 R11 R13 R12 R15 ltac:(lia) Hk) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma hl_loop : forall (i : nat) regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = at_ src (k + 1) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (k < n)%Z -> ((bv_unsigned src + k) mod 4 <> 0)%Z ->
    (Z.of_nat i + 1 = Z.min (n - k) (4 - (bv_unsigned src + k) mod 4))%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x732c8 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof using Hnwd Hnws Hn0 HOK.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 H14 H15 Hk Hkn Hal Hi.
    - (* [comment removed for export] *)
      pose proof (u64_range src).
      destruct (Z.eq_dec ((bv_unsigned src + (k + 1)) mod 4) 0) as [Hz|Hz].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x732f8 : word) (MK (k + 1)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
        * eexists. split.
          -- mlbu F_73274 D_73274 k.                    (* [comment removed for export] *)
             stepn F_73278 D_73278.                    (* [comment removed for export] *)
             stepn F_7327c D_7327c.                    (* [comment removed for export] *)
             stepn F_73280 D_73280.                    (* [comment removed for export] *)
             msb F_73284 D_73284 k ltac:(apply sb_val_plain).   (* [comment removed for export] *)
             stepn F_73288 D_73288.                    (* [comment removed for export] *)
             stepn F_7328c D_7328c.                    (* [comment removed for export] *)
             stepb_tk F_73290 D_73290 ltac:(conda).    (* [comment removed for export] *)
             pu_refl.
          -- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
          destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x732f8 : word) (MK (k + 1)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
        * eexists. split.
          -- mlbu F_73274 D_73274 k.
             stepn F_73278 D_73278.
             stepn F_7327c D_7327c.
             stepn F_73280 D_73280.
             msb F_73284 D_73284 k ltac:(apply sb_val_plain).
             stepn F_73288 D_73288.
             stepn F_7328c D_7328c.
             stepb_ft F_73290 D_73290 ltac:(conda).    (* [comment removed for export] *)
             stepn F_73294 D_73294.                    (* [comment removed for export] *)
             stepb_ft F_73298 D_73298 ltac:(cond).     (* [comment removed for export] *)
             stepn F_7329c D_7329c.                    (* [comment removed for export] *)
             pu_refl.
          -- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
          destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      pose proof (u64_range src).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x732c8 : word) (MK (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1))
                         /\ getr r 14 = at_ src (k + 1 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
      + eexists. split.
        * mlbu F_73274 D_73274 k.
          stepn F_73278 D_73278.
          stepn F_7327c D_7327c.
          stepn F_73280 D_73280.
          msb F_73284 D_73284 k ltac:(apply sb_val_plain).
          stepn F_73288 D_73288.
          stepn F_7328c D_7328c.
          stepb_ft F_73290 D_73290 ltac:(conda).       (* [comment removed for export] *)
          stepn F_73294 D_73294.                       (* [comment removed for export] *)
          stepb_tk F_73298 D_73298 ltac:(cond).        (* [comment removed for export] *)
          pu_refl.
        * cbv beta. post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem ref_memcpy : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0x732b0 : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.
  Proof using Hnwd Hnws Hn0 HOK.
    intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range src). pose proof (u64_range dst).
    rewrite <- (memk_n _ _ _ _ _ HOK). change mem0 with (MK 0).
    assert (H11' : getr regs 11 = at_ src 0) by (rewrite at_0; exact H11).
    assert (H12' : getr regs 12 = Z_to_bv 64 (n - 0)) by (rewrite Z.sub_0_r; exact H12).
    destruct (Z.eq_dec (bv_unsigned src mod 4) 0) as [Hs4|Hs4].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec (bv_unsigned dst mod 4) 0) as [Hd4|Hd4].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x733d0 : word) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
        * eexists. split.
          -- stepn F_7325c D_7325c.                     (* [comment removed for export] *)
             stepb_tk F_73260 D_73260 ltac:(conda).     (* [comment removed for export] *)
             stepn F_73370 D_73370.                     (* [comment removed for export] *)
             stepn F_73374 D_73374.                     (* [comment removed for export] *)
             stepb_ft F_73378 D_73378 ltac:(cond).      (* [comment removed for export] *)
             pu_refl.
          -- cbv beta. post. rewrite at_0. reflexivity.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
          destruct (al_finish r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x73300 : word) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                           /\ getr r 15 = Z_to_bv 64 (bv_unsigned dst mod 4) /\ keeps regs r)).
        * eexists. split.
          -- stepn F_7325c D_7325c.
             stepb_tk F_73260 D_73260 ltac:(conda).
             stepn F_73370 D_73370.
             stepn F_73374 D_73374.
             stepb_tk F_73378 D_73378 ltac:(cond).      (* [comment removed for export] *)
             pu_refl.
          -- cbv beta. post; try (rewrite at_0; reflexivity).
             unfold v_andi. rewrite <- land_3 by lia. change (bv_wrap 64 3) with 3%Z. reflexivity.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
          pose proof (Z.mod_pos_bound (bv_unsigned dst) 4 ltac:(lia)).
          destruct (mis_run r1 ret 0 (bv_unsigned dst mod 4) Hret R1 R11 R13 R12 R15 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hn0z|Hn0z].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x732f8 : word) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
        * eexists. split.
          -- stepn F_7325c D_7325c.                     (* [comment removed for export] *)
             stepb_ft F_73260 D_73260 ltac:(conda).     (* [comment removed for export] *)
             stepb_tk F_73264 D_73264 ltac:(cond).      (* [comment removed for export] *)
             stepn F_732a0 D_732a0.                     (* [comment removed for export] *)
             pu_refl.
          -- cbv beta. post. rewrite at_0. reflexivity.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
          destruct (j_run r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
      + set (i := Z.to_nat (Z.min n (4 - bv_unsigned src mod 4) - 1)).
        pose proof (Z.mod_pos_bound (bv_unsigned src) 4 ltac:(lia)).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x732c8 : word) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                           /\ getr r 14 = at_ src (0 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
        * eexists. split.
          -- stepn F_7325c D_7325c.                     (* [comment removed for export] *)
             stepb_ft F_73260 D_73260 ltac:(conda).     (* [comment removed for export] *)
             stepb_ft F_73264 D_73264 ltac:(cond).      (* [comment removed for export] *)
             stepn F_73268 D_73268.                     (* [comment removed for export] *)
             stepn F_7326c D_7326c.                     (* [comment removed for export] *)
             stepn F_73270 D_73270.                     (* [comment removed for export] *)
             pu_refl.
          -- cbv beta. post. rewrite at_0. reflexivity.
        * cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
          destruct (hl_loop i r1 ret 0 Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hs4)) as (r2 & RUN & K2).
          { subst i. rewrite Z.add_0_r, Z.sub_0_r. rewrite Z2Nat.id; lia. }
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

End ALL.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbMemcpy.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase UbMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep. Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.PuKeep.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac lia ::= lia_nd.
#[local] Ltac not_kept ::= not_kept_fast.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Open Scope Z_scope.
Section FPGen1.
Context {fx : FPState}.


Lemma land_7 : forall a, 0 <= a -> Z.land a 7 = a mod 8.
Proof using. intros a Ha. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma u_v_add : forall x y : word, bv_unsigned (v_add x y) = (bv_unsigned x + bv_unsigned y) mod 2 ^ 64.
Proof using. intros. unfold v_add. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma u_v_sub : forall x y : word, bv_unsigned (v_sub x y) = (bv_unsigned x - bv_unsigned y) mod 2 ^ 64.
Proof using. intros. unfold v_sub. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma u_v_slli1 : forall x : word, bv_unsigned (v_slli x 1) = (2 * bv_unsigned x) mod 2 ^ 64.
Proof using. intros. unfold v_slli. rewrite Z_to_bv_unsigned, Z.shiftl_mul_pow2 by lia. change (2^1) with 2. f_equal. unfold bv_wrap. f_equal. lia. Qed.

(* [comment removed for export] *)
Lemma mod_eq_of : forall a m q r, 0 < m -> 0 <= r < m -> a = m * q + r -> a mod m = r.
Proof using. intros a m q r Hm Hr ->. symmetry. apply Z.mod_unique with q; [left; lia | reflexivity]. Qed.

Lemma apart_test_vals : forall d s n,
  0 <= d -> 0 <= s -> 0 < n < 2 ^ 63 -> d + n < 2 ^ 64 -> s + n < 2 ^ 64 ->
  (0 - (2 * n) mod 2 ^ 64) mod 2 ^ 64 = 2 ^ 64 - 2 * n
  /\ (s - (n + d) mod 2 ^ 64) mod 2 ^ 64 = (if Z.ltb (s - d - n) 0 then 2 ^ 64 + (s - d - n) else s - d - n).
Proof using.
  intros d s n Hd Hs Hn Hdn Hsn.
  split.
  - rewrite (Z.mod_small (2 * n)) by lia. apply (mod_eq_of _ _ (-1)); lia.
  - rewrite (Z.mod_small (n + d)) by lia.
    destruct (Z.ltb (s - d - n) 0) eqn:L.
    + apply Z.ltb_lt in L. apply (mod_eq_of _ _ (-1)); lia.
    + apply Z.ltb_ge in L. apply (mod_eq_of _ _ 0); lia.
Qed.

Lemma apart_test_true : forall d s n,
  0 <= d -> 0 <= s -> 0 < n < 2 ^ 63 -> d + n < 2 ^ 64 -> s + n < 2 ^ 64 -> d <> s ->
  (d + n <= s \/ s + n <= d) ->
  (s - (n + d) mod 2 ^ 64) mod 2 ^ 64 <= (0 - (2 * n) mod 2 ^ 64) mod 2 ^ 64.
Proof using.
  intros d s n Hd Hs Hn Hdn Hsn Hne Hap.
  destruct (apart_test_vals d s n Hd Hs Hn Hdn Hsn) as [-> ->].
  destruct (Z.ltb (s - d - n) 0) eqn:L; [apply Z.ltb_lt in L|apply Z.ltb_ge in L]; lia.
Qed.

Lemma apart_test_false : forall d s n,
  0 <= d -> 0 <= s -> 0 < n < 2 ^ 63 -> d + n < 2 ^ 64 -> s + n < 2 ^ 64 -> d <> s ->
  ~ (d + n <= s \/ s + n <= d) ->
  (0 - (2 * n) mod 2 ^ 64) mod 2 ^ 64 < (s - (n + d) mod 2 ^ 64) mod 2 ^ 64.
Proof using.
  intros d s n Hd Hs Hn Hdn Hsn Hne Hap.
  destruct (apart_test_vals d s n Hd Hs Hn Hdn Hsn) as [-> ->].
  destruct (Z.ltb (s - d - n) 0) eqn:L; [apply Z.ltb_lt in L|apply Z.ltb_ge in L]; lia.
Qed.

Local Close Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section PROLOGUE.
  Variables d s ret : word.
  Variable n : Z.
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Hypothesis Hn : (0 <= n < 2 ^ 63)%Z.
  Hypothesis Hnws : (bv_unsigned s + n < 2 ^ 64)%Z.
  Hypothesis Hnwd : (bv_unsigned d + n < 2 ^ 64)%Z.
  Hypothesis Hret : ret_ok ret.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.

  (* [comment removed for export] *)
  Lemma mv_same : forall regs,
    getr regs 1 = ret -> getr regs 10 = d -> getr regs 11 = s -> d = s ->
    msteps RSEGS (mkst regs (0x736b4 : word) mem rom) (mkst regs ret mem rom).
  Proof using Hret.
    intros regs H1 H10 H11 Hds.
    stepb_tk F_73660 D_73660 ltac:(rwH; rewrite Hds; apply c_eq_refl).
    stepjr F_736ec D_736ec ret ltac:(gres; rwH; reflexivity).
    imm_norm. rewrite Hret. pu_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma mv_pro : forall regs,
    getr regs 1 = ret -> getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = Z_to_bv 64 n -> d <> s ->
    exists r, msteps RSEGS (mkst regs (0x736b4 : word) mem rom) (mkst r (0x736c8 : word) mem rom)
      /\ getr r 1 = ret /\ getr r 10 = d /\ getr r 11 = s /\ getr r 12 = Z_to_bv 64 n
      /\ bv_unsigned (getr r 14) = ((0 - (2 * n) mod 2 ^ 64) mod 2 ^ 64)%Z
      /\ bv_unsigned (getr r 13) = ((bv_unsigned s - (n + bv_unsigned d) mod 2 ^ 64) mod 2 ^ 64)%Z
      /\ keeps regs r.
  Proof using Hn.
    intros regs H1 H10 H11 H12 Hds.
    pose proof (u64_range d). pose proof (u64_range s).
    eexists. split.
    - stepb_ft F_73660 D_73660 ltac:(rwH; unfold c_eq; apply bv_eqb_neq; exact Hds).
      stepn F_73664 D_73664.
      stepn F_73668 D_73668.
      stepn F_7366c D_7366c.
      stepn F_73670 D_73670.
      pu_refl.
    - post.
      + rewrite u_v_sub, u_v_slli1. unorm. reflexivity.
      + rewrite u_v_sub, u_v_add. unorm. reflexivity.
  Qed.
End PROLOGUE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section APART.
  Variable mem0 : word -> option byte.
  Variables d s : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 d s n bs.
  Hypothesis Hn63 : (n < 2 ^ 63)%Z.

  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned s + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned d + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.
  Let Hdisj := Hdisj _ _ _ _ _ HOK.

  Lemma mv_apart_pos : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = Z_to_bv 64 n ->
    d <> s -> (0 < n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x736b4 : word) mem0 rom) (mkst regs' ret (wbytes mem0 d bs) rom)
      /\ keeps regs regs'.
  Proof using Hdisj Hnwd Hnws Hn0 Hn63 HOK.
    intros regs ret Hret H1 H10 H11 H12 Hds Hnpos.
    pose proof (u64_range d) as Rd. pose proof (u64_range s) as Rs.
    destruct (mv_pro d s ret n mem0 rom ltac:(lia) regs H1 H10 H11 H12 Hds) as (r & RUN & R1 & R10 & R11 & R12 & R14 & R13 & K).
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x736c8 : word) mem0 rom)
             (fun r => getr r 1 = ret /\ getr r 10 = d /\ getr r 11 = s /\ getr r 12 = Z_to_bv 64 n
                       /\ bv_unsigned (getr r 14) = ((0 - (2 * n) mod 2 ^ 64) mod 2 ^ 64)%Z
                       /\ bv_unsigned (getr r 13) = ((bv_unsigned s - (n + bv_unsigned d) mod 2 ^ 64) mod 2 ^ 64)%Z
                       /\ keeps regs r)).
    { exists r. repeat split; assumption. }
    cbv beta. intros r1 (S1 & S10 & S11 & S12 & S14 & S13 & K1).
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x732b0 : word) mem0 rom)
             (fun r => getr r 1 = ret /\ getr r 10 = d /\ getr r 11 = s /\ getr r 12 = Z_to_bv 64 n /\ keeps regs r)).
    { eexists. split.
      - stepb_tk F_73674 D_73674 ltac:(unfold c_ltu, bv_ltu; rewrite S14, S13; apply Z.ltb_ge;
                                       apply apart_test_true; lia).
        stepn F_736b4 D_736b4.
        pu_refl.
      - repeat split; gres; assumption. }
    cbv beta. intros r2 (T1 & T10 & T11 & T12 & K2).
    destruct (ref_memcpy mem0 d s n bs rom HOK r2 ret Hret T1 T10 T11 T12) as (r3 & RUN3 & K3).
    exists r3. split; [exact RUN3 | eapply keeps_trans; eassumption].
  Qed.
End APART.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End FPGen1.


Local Open Scope Z_scope.

(* [comment removed for export] *)
Section FPGen2.
Context {fx : FPState}.

Definition inrange (a : Z) (len : Z) (x : Z) : bool := (Z.leb a x && Z.ltb x (a + len))%bool.

Lemma inrange_true : forall a len x, inrange a len x = true <-> a <= x < a + len.
Proof using.
  intros. unfold inrange. rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma inrange_false : forall a len x, inrange a len x = false <-> ~ (a <= x < a + len).
Proof using.
  intros. rewrite <- inrange_true. destruct (inrange a len x); split; intros; congruence.
Qed.

Lemma wbytes_get : forall bs m (a x : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 ->
  wbytes m a bs x =
    if inrange (bv_unsigned a) (Z.of_nat (length bs)) (bv_unsigned x)
    then Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0))
    else m x.
Proof using.
  induction bs as [|b rest IH]; intros m a x Hnw.
  - cbn [wbytes length Z.of_nat]. destruct (inrange _ _ _) eqn:E; [|reflexivity].
    apply inrange_true in E. lia.
  - cbn [wbytes length] in *. pose proof (u64_range a). pose proof (u64_range x).
    destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Ex|Nx].
    + assert (x = a) by (apply bv_eq; exact Ex). subst x.
      match goal with |- wbytes ?m1 _ _ _ = _ =>
        assert (Hb : wbytes m1 (a + 1)%bv rest a = m1 a) end.
      { destruct rest as [|b2 rest2]; [reflexivity|]. cbn [length] in Hnw.
        apply wbytes_below; rewrite word_succ_at, at_u; cbn [length]; lia. }
      rewrite Hb, bv_eqb_refl.
      replace (inrange _ _ _) with true by (symmetry; apply inrange_true; lia).
      rewrite Z.sub_diag. reflexivity.
    + destruct rest as [|b2 rest2].
      { cbn [wbytes length Z.of_nat Z.add]. rewrite (bv_eqb_neq x a) by (intros ->; apply Nx; reflexivity).
        destruct (inrange _ _ _) eqn:E; [|reflexivity].
        exfalso. apply inrange_true in E. cbn in E. lia. }
      cbn [length] in Hnw.
      rewrite IH by (rewrite word_succ_at, at_u; cbn [length]; lia).
      rewrite word_succ_at, at_u by lia.
      rewrite (bv_eqb_neq x a) by (intros ->; apply Nx; reflexivity).
      destruct (inrange (bv_unsigned a + 1) _ _) eqn:E1; destruct (inrange (bv_unsigned a) _ _) eqn:E2.
      * apply inrange_true in E1.
        replace (Z.to_nat (bv_unsigned x - bv_unsigned a)) with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
        reflexivity.
      * exfalso. apply inrange_true in E1. apply inrange_false in E2. cbn [length] in E1, E2. lia.
      * exfalso. apply inrange_true in E2. apply inrange_false in E1. cbn [length] in E1, E2. lia.
      * reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wbytes_comm : forall m (a1 a2 : word) l1 l2,
  bv_unsigned a1 + Z.of_nat (length l1) <= 2 ^ 64 ->
  bv_unsigned a2 + Z.of_nat (length l2) <= 2 ^ 64 ->
  (bv_unsigned a1 + Z.of_nat (length l1) <= bv_unsigned a2 \/ bv_unsigned a2 + Z.of_nat (length l2) <= bv_unsigned a1) ->
  wbytes (wbytes m a1 l1) a2 l2 = wbytes (wbytes m a2 l2) a1 l1.
Proof using.
  intros m a1 a2 l1 l2 H1 H2 Hd. apply functional_extensionality. intros x.
  rewrite !wbytes_get by assumption.
  destruct (inrange (bv_unsigned a2) _ _) eqn:E2; destruct (inrange (bv_unsigned a1) _ _) eqn:E1; try reflexivity.
  exfalso. apply inrange_true in E1. apply inrange_true in E2. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_id : forall m (a : word) l,
  bv_unsigned a + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (length l) -> m (at_ a i) = Some (nth (Z.to_nat i) l (Z_to_bv 8 0))) ->
  wbytes m a l = m.
Proof using.
  intros m a l Hnw Hm. apply functional_extensionality. intros x.
  rewrite wbytes_get by assumption. pose proof (u64_range x).
  destruct (inrange _ _ _) eqn:E; [|reflexivity].
  apply inrange_true in E.
  rewrite <- (Hm (bv_unsigned x - bv_unsigned a)) by lia.
  f_equal. unfold at_. apply bv_eq. rewrite Z_to_bv_unsigned.
  replace (bv_unsigned a + (bv_unsigned x - bv_unsigned a)) with (bv_unsigned x) by lia.
  rewrite bv_wrap_small; [reflexivity|]. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_overlay : forall segs l m (a : word),
  bv_unsigned a + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (length l) -> m (at_ a i) = Some (nth (Z.to_nat i) l (Z_to_bv 8 0))) ->
  rdn segs m a (length l) = Some l.
Proof using.
  intros segs l. induction l as [|b rest IH]; intros m a Hnw Hm; [reflexivity|].
  cbn [rdn length]. pose proof (u64_range a). cbn [length] in Hnw, Hm.
  pose proof (Hm 0 ltac:(lia)) as H0. rewrite at_0 in H0. cbn [Z.to_nat nth] in H0. rewrite H0.
  destruct rest as [|b2 rest2]; [reflexivity|]. cbn [length] in *.
  rewrite (IH m (a + 1)%bv); [reflexivity| rewrite word_succ_at, at_u; lia |].
  intros i Hi. rewrite word_succ_at, at_at. rewrite (Hm (1 + i)) by lia.
  f_equal. replace (Z.to_nat (1 + i)) with (S (Z.to_nat i)) by lia. reflexivity.
Qed.

Section OVL.
  Variable mem0 : word -> option byte.
  Variables d s : word.
  Variable n : Z.
  Variable bs : list byte.
  Hypothesis Hn : 0 <= n < 2 ^ 63.
  Hypothesis Hlen : length bs = Z.to_nat n.
  Hypothesis Hsrc : forall i, 0 <= i < n -> mem0 (at_ s i) = Some (b_ bs i).
  Hypothesis Hdst : store_ok RSEGS mem0 d (Z.to_nat n) = true.
  Hypothesis Hnws : bv_unsigned s + n < 2 ^ 64.
  Hypothesis Hnwd : bv_unsigned d + n < 2 ^ 64.

  (* [comment removed for export] *)
  Definition memF (k : Z) : word -> option byte := wbytes mem0 d (firstn (Z.to_nat k) bs).
  (* [comment removed for export] *)
  Definition memB (k : Z) : word -> option byte := wbytes mem0 (at_ d k) (skipn (Z.to_nat k) bs).

  Lemma src_rdn : rdn RSEGS mem0 s (length bs) = Some bs.
  Proof using Hnws Hsrc Hlen Hn n.
    apply rdn_overlay; [rewrite Hlen; lia|]. intros i Hi. apply Hsrc. rewrite Hlen in Hi. lia.
  Qed.


  Lemma memF_n : memF n = wbytes mem0 d bs.
  Proof using Hlen. unfold memF. rewrite <- Hlen, firstn_all. reflexivity. Qed.

  Lemma memB_n : memB n = mem0.
  Proof using Hlen. unfold memB. rewrite <- Hlen, skipn_all. reflexivity. Qed.

  Lemma memB_0 : memB 0 = wbytes mem0 d bs.
  Proof using. unfold memB. rewrite at_0. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma move_id : d = s -> wbytes mem0 d bs = mem0.
  Proof using Hnwd Hdst Hsrc Hlen Hn n.
    intros ->. apply wbytes_id; [rewrite Hlen; lia|]. intros i Hi. rewrite Hlen in Hi. apply Hsrc. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rdF : forall k j m,
      bv_unsigned d < bv_unsigned s ->
      0 <= k <= j -> j + Z.of_nat m <= n ->
      rdn RSEGS (memF k) (at_ s j) m = Some (sub bs (Z.to_nat j) m).
  Proof using Hnws Hsrc Hlen Hn.
    intros k j m Hds Hk Hm. unfold memF. pose proof (u64_range s). pose proof (u64_range d).
    rewrite rdn_wbytes_out.
    - replace (at_ s j) with (at_ s (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
      apply (rdn_sub RSEGS mem0 (length bs)); [exact src_rdn | rewrite Hlen; lia].
    - right. rewrite length_firstn, Hlen, at_u; lia.
    - rewrite at_u; lia.
    - rewrite length_firstn, Hlen. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rdB : forall k j m,
      bv_unsigned s < bv_unsigned d ->
      0 <= j -> j + Z.of_nat m <= k -> k <= n ->
      rdn RSEGS (memB k) (at_ s j) m = Some (sub bs (Z.to_nat j) m).
  Proof using Hnwd Hnws Hsrc Hlen Hn.
    intros k j m Hsd Hj Hm Hk. unfold memB. pose proof (u64_range s). pose proof (u64_range d).
    rewrite rdn_wbytes_out.
    - replace (at_ s j) with (at_ s (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
      apply (rdn_sub RSEGS mem0 (length bs)); [exact src_rdn | rewrite Hlen; lia].
    - left. rewrite !at_u; lia.
    - rewrite at_u; lia.
    - rewrite length_skipn, Hlen, at_u; lia.
  Qed.

  Lemma wrF : forall k j m, 0 <= j -> j + Z.of_nat m <= n -> store_ok RSEGS (memF k) (at_ d j) m = true.
  Proof using Hnwd Hdst Hlen Hn.
    intros k j m Hj Hm. unfold memF.
    apply (store_ok_at RSEGS mem0 d (Z.to_nat n)); try assumption; lia.
  Qed.

  Lemma wrB : forall k j m, 0 <= j -> j + Z.of_nat m <= n -> 0 <= k -> store_ok RSEGS (memB k) (at_ d j) m = true.
  Proof using Hnwd Hdst Hlen Hn.
    intros k j m Hj Hm Hk. unfold memB. pose proof (u64_range d).
    destruct m as [|m']; [reflexivity|].
    apply (store_ok_mono RSEGS (S m') mem0); [apply wbytes_grows|].
    apply (store_ok_sub RSEGS mem0 d (at_ d j) (Z.to_nat n) (S m')); try assumption; rewrite ?at_u; lia.
  Qed.

  Lemma memF_extend : forall k m, 0 <= k -> k + Z.of_nat m <= n ->
      wbytes (memF k) (at_ d k) (sub bs (Z.to_nat k) m) = memF (k + Z.of_nat m).
  Proof using Hlen Hn.
    intros k m Hk Hm. unfold memF.
    replace (at_ d k) with (at_ d (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
    rewrite wbytes_extend' by (rewrite Hlen; lia). f_equal. f_equal. lia.
  Qed.

  Lemma memB_extend : forall k m, Z.of_nat m <= k <= n ->
      wbytes (memB k) (at_ d (k - Z.of_nat m)) (sub bs (Z.to_nat (k - Z.of_nat m)) m) = memB (k - Z.of_nat m).
  Proof using Hnwd Hlen Hn.
    intros k m Hk. unfold memB. pose proof (u64_range d).
    assert (Hs : skipn (Z.to_nat (k - Z.of_nat m)) bs = sub bs (Z.to_nat (k - Z.of_nat m)) m ++ skipn (Z.to_nat k) bs).
    { unfold sub. rewrite <- (firstn_skipn m (skipn (Z.to_nat (k - Z.of_nat m)) bs)) at 1.
      rewrite skipn_skipn. f_equal. f_equal. lia. }
    rewrite Hs, wbytes_app, at_at.
    assert (Hl : length (sub bs (Z.to_nat (k - Z.of_nat m)) m) = m) by (apply sub_length; rewrite Hlen; lia).
    rewrite Hl. replace (k - Z.of_nat m + Z.of_nat m) with k by lia.
    symmetry. apply wbytes_comm.
    - rewrite Hl, at_u; lia.
    - rewrite length_skipn, Hlen, at_u; lia.
    - left. rewrite Hl, !at_u; lia.
  Qed.
End OVL.

Local Close Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End FPGen2.


Local Open Scope Z_scope.

(* [comment removed for export] *)
Section FPGen3.
Context {fx : FPState}.

Definition LDv (l : list byte) : word := Z_to_bv 64 (lez l).

Lemma LDv_lez : forall l, length l = 8%nat -> lez l = bv_unsigned (LDv l).
Proof using.
  intros l Hl. unfold LDv. pose proof (lez_bound_len l 8 Hl) as Hb. change (8 * Z.of_nat 8) with 64 in Hb.
  rewrite u_Z2bv; lia.
Qed.

Lemma land_shl_disjoint8 : forall a b, 0 <= a -> 0 <= b < 2 ^ 8 -> Z.land (a * 2 ^ 8) b = 0.
Proof using.
  intros a b Ha Hb. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hl|Hh].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit b i) with false; [apply Bool.andb_false_r|].
    symmetry. apply Z.bits_above_log2; [lia|]. 
    destruct (Z.eq_dec b 0) as [->|Hb0]; [cbn; lia|].
    apply (Z.lt_le_trans _ 8); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lor_shl_disjoint8 : forall a b, 0 <= a -> 0 <= b < 2 ^ 8 -> Z.lor (a * 2 ^ 8) b = a * 2 ^ 8 + b.
Proof using.
  intros a b Ha Hb.
  rewrite <- Z.lxor_lor by (apply land_shl_disjoint8; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_shl_disjoint8; lia.
Qed.

Lemma Z_to_le_bytes_of_bytes : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof using.
  induction bs as [|b rest IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256%Z in Hb.
  pose proof (bytes_le_to_Z_nonneg rest) as Hr.
  assert (Hlor : Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z rest) 8) = bv_unsigned b + 2 ^ 8 * bytes_le_to_Z rest).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm. rewrite lor_shl_disjoint8 by lia. lia. }
  rewrite Hlor. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
    change (2 ^ 8) with 256 in *. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256 in *.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z rest) / 256) with (bytes_le_to_Z rest) by lia. exact IH.
Qed.

Lemma word_to_le_bytes_of_bytes8 : forall bs,
  length bs = 8%nat -> word_to_le_bytes 8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof using.
  intros bs Hlen. unfold word_to_le_bytes.
  pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb. change (8 * Z.of_nat 8) with 64 in Hb.
  pose proof (bytes_le_to_Z_nonneg bs).
  rewrite u_Z2bv by lia. rewrite <- Hlen. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma sd_bytes_LDv : forall l, length l = 8%nat -> word_to_le_bytes 8 (LDv l) = l.
Proof using. intros l Hl. unfold LDv. apply word_to_le_bytes_of_bytes8. exact Hl. Qed.

(* [comment removed for export] *)
Lemma v_add_at_Z : forall (a : word) o z,
  0 <= bv_unsigned a + o < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  v_add (at_ a o) (Z_to_bv 64 z) = at_ a (o + z).
Proof using.
  intros a o z Ho Hz. unfold v_add. rewrite at_u by lia. rewrite u_Z2bv by lia. unfold at_. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma v_add_at_any : forall (a : word) o (y : word),
  v_add (at_ a o) y = at_ a (o + bv_unsigned y).
Proof using.
  intros a o y. unfold v_add, at_. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma v_add_any_at : forall (a : word) o (y : word),
  v_add y (at_ a o) = at_ a (o + bv_unsigned y).
Proof using.
  intros a o y. unfold v_add, at_. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_r. f_equal. lia.
Qed.

Local Close Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FWD.
  Variable mem0 : word -> option byte.
  Variables d s : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis Hn : (0 <= n < 2 ^ 63)%Z.
  Hypothesis Hlen : length bs = Z.to_nat n.
  Hypothesis Hsrc : forall i, (0 <= i < n)%Z -> mem0 (at_ s i) = Some (b_ bs i).
  Hypothesis Hdst : store_ok RSEGS mem0 d (Z.to_nat n) = true.
  Hypothesis Hnws : (bv_unsigned s + n < 2 ^ 64)%Z.
  Hypothesis Hnwd : (bv_unsigned d + n < 2 ^ 64)%Z.
  Hypothesis Hds : (bv_unsigned d < bv_unsigned s)%Z.

  #[local] Notation MF := (memF mem0 d bs).
  Let RDF : forall k j m, (bv_unsigned d < bv_unsigned s)%Z -> (0 <= k <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
      rdn RSEGS (MF k) (at_ s j) m = Some (sub bs (Z.to_nat j) m)
    := ltac:(intros; eapply rdF; eauto).
  Let WRF : forall k j m, (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z -> store_ok RSEGS (MF k) (at_ d j) m = true
    := ltac:(intros; eapply wrF; eauto).
  Let EXTF : forall k m, (0 <= k)%Z -> (k + Z.of_nat m <= n)%Z ->
      wbytes (MF k) (at_ d k) (sub bs (Z.to_nat k) m) = MF (k + Z.of_nat m)
    := ltac:(intros; eapply memF_extend; eauto).

  (* [comment removed for export] *)
  Lemma mvF_lbu : forall regs pc w rd rs k j,
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs 0, 4%Z) ->
    getr regs rs = at_ s j ->
    (0 <= k <= j)%Z -> (j + 1 <= n)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc (MF k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (b_ bs j))) (v_addi pc 4) (MF k) rom).
  Proof using RDF Hds Hnwd Hnws Hdst Hsrc Hlen Hn.
    intros regs pc w rd rs k j Hf He Hd Hrs Hk Hj.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs. imm_norm. rewrite at_addi, Z.add_0_r.
    rewrite (RDF k j 1 Hds) by lia.
    unfold b_, sub. rewrite <- sub_nth by (rewrite Hlen; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma mvF_sb : forall regs pc w rs1 rs2 k (v : word),
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 0, 4%Z) ->
    getr regs rs1 = at_ d k -> getr regs rs2 = v -> Z_to_bv 8 (bv_unsigned v) = b_ bs k ->
    (0 <= k)%Z -> (k + 1 <= n)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc (MF k) rom) =
    MachineOk (mkst regs (v_addi pc 4) (MF (k + 1)) rom).
  Proof using EXTF WRF Hnwd Hnws Hdst Hsrc Hlen Hn s.
    intros regs pc w rs1 rs2 k v Hf He Hd Hrs1 Hrs2 Hb Hk Hk1.
    replace (k + 1)%Z with (k + Z.of_nat 1)%Z by lia.
    rewrite <- (EXTF k 1) by lia.
    replace (sub bs (Z.to_nat k) 1) with [b_ bs k] by (unfold b_; symmetry; apply sub_nth; rewrite Hlen; lia).
    eapply MmapSim.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | exact Hb |].
    - rewrite Hrs1. imm_norm. rewrite at_addi, Z.add_0_r. reflexivity.
    - apply WRF; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mvF_ld : forall regs pc w rd rs k j,
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ8 true rd rs 0, 4%Z) ->
    getr regs rs = at_ s j ->
    (0 <= k <= j)%Z -> (j + 8 <= n)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc (MF k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LDv (sub bs (Z.to_nat j) 8))) (v_addi pc 4) (MF k) rom).
  Proof using RDF Hds Hnwd Hnws Hdst Hsrc Hlen Hn.
    intros regs pc w rd rs k j Hf He Hd Hrs Hk Hj.
    eapply step_ld; [exact Hf | exact He | exact Hd | |].
    - rewrite Hrs. imm_norm. rewrite at_addi, Z.add_0_r. apply (RDF k j 8 Hds); lia.
    - apply LDv_lez. apply sub_length. rewrite Hlen. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mvF_sd : forall regs pc w rs1 rs2 k,
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ8 rs1 rs2 0, 4%Z) ->
    getr regs rs1 = at_ d k -> getr regs rs2 = LDv (sub bs (Z.to_nat k) 8) ->
    (0 <= k)%Z -> (k + 8 <= n)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc (MF k) rom) =
    MachineOk (mkst regs (v_addi pc 4) (MF (k + 8)) rom).
  Proof using EXTF WRF Hnwd Hnws Hdst Hsrc Hlen Hn s.
    intros regs pc w rs1 rs2 k Hf He Hd Hrs1 Hrs2 Hk Hk8.
    replace (k + 8)%Z with (k + Z.of_nat 8)%Z by lia.
    rewrite <- (EXTF k 8) by lia.
    rewrite <- (sd_bytes_LDv (sub bs (Z.to_nat k) 8)) by (apply sub_length; rewrite Hlen; lia).
    eapply step_sd_at; [exact Hf | exact He | exact Hd | | exact Hrs2 |].
    - rewrite Hrs1. imm_norm. rewrite at_addi, Z.add_0_r. reflexivity.
    - apply WRF; lia.
  Qed.

  (* [comment removed for export] *)
  Ltac flbu F D jj :=
    chain_step; [reflexivity
      | eapply mvF_lbu with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | lia | lia]
      | step_simpl]; vnorm.
  Ltac fld F D jj :=
    chain_step; [reflexivity
      | eapply mvF_ld with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | lia | lia]
      | step_simpl]; vnorm.
  Ltac mf_at kk := match goal with |- msteps _ (mkst _ _ (MF ?a) _) _ =>
                     first [constr_eq a kk | replace (MF a) with (MF kk) by (f_equal; lia)] end.
  Ltac fsb F D kk :=
    mf_at kk;
    chain_step; [reflexivity
      | eapply mvF_sb with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity | apply sb_byte_LBv | lia | lia]
      | step_simpl].
  Ltac fsd F D kk :=
    mf_at kk;
    chain_step; [reflexivity
      | eapply mvF_sd with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; f_equal; lia] | lia | lia]
      | step_simpl].
  Ltac cond :=
    rwH; rewrite ?at_addi; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unfold at_, v_addi; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_7 by lia; lia.
  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia); try solve_keeps.

  (* [comment removed for export] *)
  Lemma fwd_bloop : forall i regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 14 = at_ s k -> getr regs 13 = at_ d k -> getr regs 12 = at_ d n ->
    (0 <= k < n)%Z -> (n - k = Z.of_nat (S i))%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x736ec : word) (MF k) rom) (mkst regs' ret (MF n) rom)
      /\ keeps regs regs'.
  Proof using EXTF WRF RDF Hds Hnwd Hnws Hdst Hsrc Hlen Hn.
    induction i as [|i IH]; intros regs ret k Hret H1 H14 H13 H12 Hk Hi.
    - (* [comment removed for export] *)
      pose proof (u64_range s). pose proof (u64_range d).
      eexists. split.
      + flbu F_73698 D_73698 k.
        stepn F_7369c D_7369c.
        stepn F_736a0 D_736a0.
        fsb F_736a4 D_736a4 k.
        stepn F_736a8 D_736a8.
        stepb_ft F_736ac D_736ac ltac:(cond).
        stepn F_736b0 D_736b0.
        stepjr F_736ec D_736ec ret ltac:(gres; rwH; reflexivity).
        imm_norm. rewrite Hret. replace (MF (k + 1)) with (MF n) by (f_equal; lia). pu_refl.
      + solve_keeps.
    - pose proof (u64_range s). pose proof (u64_range d).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x736ec : word) (MF (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 14 = at_ s (k + 1) /\ getr r 13 = at_ d (k + 1) /\ getr r 12 = at_ d n /\ keeps regs r)).
      + eexists. split.
        * flbu F_73698 D_73698 k.
          stepn F_7369c D_7369c.
          stepn F_736a0 D_736a0.
          fsb F_736a4 D_736a4 k.
          stepn F_736a8 D_736a8.
          stepb_tk F_736ac D_736ac ltac:(cond).
          pu_refl.
        * post.
      + cbv beta. intros r1 (R1 & R14 & R13 & R12 & K1).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R14 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  Lemma fwd_bytes : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 13 = at_ d k -> getr regs 14 = at_ s k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x736e4 : word) (MF k) rom) (mkst regs' ret (MF n) rom)
      /\ keeps regs regs'.
  Proof using EXTF WRF RDF Hds Hnwd Hnws Hdst Hsrc Hlen Hn.
    intros regs ret k Hret H1 H13 H14 H12 Hk.
    pose proof (u64_range s). pose proof (u64_range d).
    destruct (Z.eq_dec k n) as [->|Hkn].
    - eexists. split; [|apply keeps_refl].
      stepb_tk F_73690 D_73690 ltac:(cond).
      stepjr F_736ec D_736ec ret ltac:(gres; rwH; reflexivity).
      imm_norm. rewrite Hret. pu_refl.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x736ec : word) (MF k) rom)
               (fun r => getr r 1 = ret /\ getr r 14 = at_ s k /\ getr r 13 = at_ d k /\ getr r 12 = at_ d n /\ keeps regs r)).
      + eexists. split.
        * stepb_ft F_73690 D_73690 ltac:(cond).
          stepn F_73694 D_73694.
          pu_refl.
        * post. rewrite v_add_at_Z by lia. f_equal. lia.
      + cbv beta. intros r1 (R1 & R14 & R13 & R12 & K1).
        destruct (fwd_bloop (Z.to_nat (n - k - 1)) r1 ret k Hret R1 R14 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  Lemma fwd_wloop : forall i regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 14 = at_ s k -> getr regs 13 = at_ d k -> getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 11 = Z_to_bv 64 7 ->
    (0 <= k)%Z -> (8 * Z.of_nat (S i) <= n - k < 8 * Z.of_nat (S i) + 8)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x73814 : word) (MF k) rom) (mkst regs' ret (MF n) rom)
      /\ keeps regs regs'.
  Proof using EXTF WRF RDF Hds Hnwd Hnws Hdst Hsrc Hlen Hn.
    induction i as [|i IH]; intros regs ret k Hret H1 H14 H13 H12 H11 Hk Hi.
    - pose proof (u64_range s). pose proof (u64_range d).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x736e4 : word) (MF (k + 8)) rom)
               (fun r => getr r 1 = ret /\ getr r 13 = at_ d (k + 8) /\ getr r 14 = at_ s (k + 8) /\ getr r 12 = Z_to_bv 64 (n - (k + 8)) /\ keeps regs r)).
      + eexists. split.
        * fld F_737c0 D_737c0 k.
          stepn F_737c4 D_737c4.
          fsd F_737c8 D_737c8 k.
          stepn F_737cc D_737cc.
          stepn F_737d0 D_737d0.
          stepb_ft F_737d4 D_737d4 ltac:(cond).
          stepn F_737d8 D_737d8.
          pu_refl.
        * post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R13 & R14 & R12 & K1).
        destruct (fwd_bytes r1 ret (k + 8) Hret R1 R13 R14 R12 ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - pose proof (u64_range s). pose proof (u64_range d).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x73814 : word) (MF (k + 8)) rom)
               (fun r => getr r 1 = ret /\ getr r 14 = at_ s (k + 8) /\ getr r 13 = at_ d (k + 8) /\ getr r 12 = Z_to_bv 64 (n - (k + 8)) /\ getr r 11 = Z_to_bv 64 7 /\ keeps regs r)).
      + eexists. split.
        * fld F_737c0 D_737c0 k.
          stepn F_737c4 D_737c4.
          fsd F_737c8 D_737c8 k.
          stepn F_737cc D_737cc.
          stepn F_737d0 D_737d0.
          stepb_tk F_737d4 D_737d4 ltac:(cond).
          pu_refl.
        * post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R14 & R13 & R12 & R11 & K1).
        destruct (IH r1 ret (k + 8)%Z Hret R1 R14 R13 R12 R11 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  Lemma fwd_words : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 13 = at_ d k -> getr regs 14 = at_ s k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x73808 : word) (MF k) rom) (mkst regs' ret (MF n) rom)
      /\ keeps regs regs'.
  Proof using EXTF WRF RDF Hds Hnwd Hnws Hdst Hsrc Hlen Hn.
    intros regs ret k Hret H1 H13 H14 H12 Hk.
    pose proof (u64_range s). pose proof (u64_range d).
    destruct (Z.lt_ge_cases (n - k) 8) as [Hlt|Hge].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x736e4 : word) (MF k) rom)
               (fun r => getr r 1 = ret /\ getr r 13 = at_ d k /\ getr r 14 = at_ s k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
      + eexists. split.
        * stepn F_737b4 D_737b4.
          stepb_tk F_737b8 D_737b8 ltac:(cond).
          pu_refl.
        * post.
      + cbv beta. intros r1 (R1 & R13 & R14 & R12 & K1).
        destruct (fwd_bytes r1 ret k Hret R1 R13 R14 R12 ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x73814 : word) (MF k) rom)
               (fun r => getr r 1 = ret /\ getr r 14 = at_ s k /\ getr r 13 = at_ d k /\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 11 = Z_to_bv 64 7 /\ keeps regs r)).
      + eexists. split.
        * stepn F_737b4 D_737b4.
          stepb_ft F_737b8 D_737b8 ltac:(cond).
          stepn F_737bc D_737bc.
          pu_refl.
        * post.
      + cbv beta. intros r1 (R1 & R14 & R13 & R12 & R11 & K1).
        destruct (fwd_wloop (Z.to_nat ((n - k) / 8 - 1)) r1 ret k Hret R1 R14 R13 R12 R11 ltac:(lia)) as (r2 & RUN & K2).
        { 
          split; nia. }
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.


  (* [comment removed for export] *)
  Lemma fwd_align : forall i regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ s k -> getr regs 16 = at_ d k -> getr regs 15 = at_ d (k + 1) -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z -> (Z.of_nat (S i) = 8 - (bv_unsigned d + k) mod 8)%Z -> ((bv_unsigned d + k) mod 8 <> 0)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x73754 : word) (MF k) rom) (mkst regs' ret (MF n) rom)
      /\ keeps regs regs'.
  Proof using EXTF WRF RDF Hds Hnwd Hnws Hdst Hsrc Hlen Hn.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H16 H15 H12 Hk Hi Hal;
      pose proof (u64_range s); pose proof (u64_range d);
      (destruct (Z.eq_dec k n) as [->|Hkn];
       [ eexists; split; [|apply keeps_refl];
         stepb_tk F_73700 D_73700 ltac:(cond);
         stepjr F_736ec D_736ec ret ltac:(gres; rwH; reflexivity);
         imm_norm; rewrite Hret; pu_refl |]).
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x73808 : word) (MF (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 13 = at_ d (k + 1) /\ getr r 14 = at_ s (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
      + eexists. split.
        * stepb_ft F_73700 D_73700 ltac:(cond).
          stepn F_73704 D_73704.
          flbu F_73708 D_73708 k.
          stepn F_7370c D_7370c.
          stepn F_73710 D_73710.
          stepn F_73714 D_73714.
          fsb F_73718 D_73718 k.
          stepn F_7371c D_7371c.
          stepn F_73720 D_73720.
          stepn F_73724 D_73724.
          stepb_ft F_73728 D_73728 ltac:(cond).
          stepn F_7372c D_7372c.
          pu_refl.
        * post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R13 & R14 & R12 & K1).
        destruct (fwd_words r1 ret (k + 1) Hret R1 R13 R14 R12 ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x73754 : word) (MF (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ s (k + 1) /\ getr r 16 = at_ d (k + 1) /\ getr r 15 = at_ d (k + 1 + 1)
                         /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
      + eexists. split.
        * stepb_ft F_73700 D_73700 ltac:(cond).
          stepn F_73704 D_73704.
          flbu F_73708 D_73708 k.
          stepn F_7370c D_7370c.
          stepn F_73710 D_73710.
          stepn F_73714 D_73714.
          fsb F_73718 D_73718 k.
          stepn F_7371c D_7371c.
          stepn F_73720 D_73720.
          stepn F_73724 D_73724.
          stepb_tk F_73728 D_73728 ltac:(cond).
          pu_refl.
        * post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R11 & R16 & R15 & R12 & K1).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R16 R15 R12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.


  (* [comment removed for export] *)
  Lemma fwd_entry : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0x736cc : word) (MF 0) rom) (mkst regs' ret (MF n) rom)
      /\ keeps regs regs'.
  Proof using EXTF WRF RDF Hds Hnwd Hnws Hdst Hsrc Hlen Hn.
    intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range s). pose proof (u64_range d).
    assert (H12' : getr regs 12 = Z_to_bv 64 (n - 0)) by (rewrite Z.sub_0_r; exact H12).
    destruct (c_eq (v_andi (v_xor s d) 7) (Z_to_bv 64 0)) eqn:EQ.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec (bv_unsigned d mod 8) 0) as [Hal|Hal].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x73808 : word) (MF 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 13 = at_ d 0 /\ getr r 14 = at_ s 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
        * eexists. split.
          -- stepn F_73678 D_73678.
             stepn F_7367c D_7367c.
             stepb_ft F_73680 D_73680 ltac:(cond).
             stepb_tk F_73684 D_73684 ltac:(rwH; exact EQ).
             stepn F_736f0 D_736f0.
             stepb_tk F_736f4 D_736f4 ltac:(cond).
             stepn F_737ac D_737ac.
             stepn F_737b0 D_737b0.
             pu_refl.
          -- post; rewrite ?at_0; reflexivity.
        * cbv beta. intros r1 (R1 & R13 & R14 & R12 & K1).
          destruct (fwd_words r1 ret 0 Hret R1 R13 R14 R12 ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x73754 : word) (MF 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ s 0 /\ getr r 16 = at_ d 0 /\ getr r 15 = at_ d (0 + 1) /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
        * eexists. split.
          -- stepn F_73678 D_73678.
             stepn F_7367c D_7367c.
             stepb_ft F_73680 D_73680 ltac:(cond).
             stepb_tk F_73684 D_73684 ltac:(rwH; exact EQ).
             stepn F_736f0 D_736f0.
             stepb_ft F_736f4 D_736f4 ltac:(cond).
             stepn F_736f8 D_736f8.
             stepn F_736fc D_736fc.
             pu_refl.
          -- post; rewrite ?at_0; try reflexivity.
        * cbv beta. intros r1 (R1 & R11 & R16 & R15 & R12 & K1).
          destruct (fwd_align (Z.to_nat (7 - bv_unsigned d mod 8)) r1 ret 0 Hret R1 R11 R16 R15 R12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x736e4 : word) (MF 0) rom)
               (fun r => getr r 1 = ret /\ getr r 13 = at_ d 0 /\ getr r 14 = at_ s 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
      + eexists. split.
        * stepn F_73678 D_73678.
          stepn F_7367c D_7367c.
          stepb_ft F_73680 D_73680 ltac:(cond).
          stepb_ft F_73684 D_73684 ltac:(rwH; exact EQ).
          stepn F_73688 D_73688.
          stepn F_7368c D_7368c.
          pu_refl.
        * post; rewrite ?at_0; reflexivity.
      + cbv beta. intros r1 (R1 & R13 & R14 & R12 & K1).
        destruct (fwd_bytes r1 ret 0 Hret R1 R13 R14 R12 ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.
End FWD.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End FPGen3.


Local Open Scope Z_scope.
(* [comment removed for export] *)
Section FPGen4.
Context {fx : FPState}.

Lemma u_neg_count : forall k, 0 < k < 2 ^ 64 -> bv_unsigned (v_sub (Z_to_bv 64 0) (Z_to_bv 64 k)) = 2 ^ 64 - k.
Proof using. intros k Hk. rewrite u_v_sub. rewrite !u_Z2bv by lia. apply (mod_eq_of _ _ (-1)); lia. Qed.

Lemma neg_count_eq : forall k, 0 < k < 2 ^ 64 -> v_sub (Z_to_bv 64 0) (Z_to_bv 64 k) = Z_to_bv 64 (2 ^ 64 - k).
Proof using. intros k Hk. apply bv_eq. rewrite u_neg_count by lia. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma neg_neg_count : forall k, 0 < k < 2 ^ 64 -> v_sub (Z_to_bv 64 0) (Z_to_bv 64 (2 ^ 64 - k)) = Z_to_bv 64 k.
Proof using. intros k Hk. apply bv_eq. rewrite u_v_sub. rewrite !u_Z2bv by lia. apply (mod_eq_of _ _ (-1)); lia. Qed.

Lemma inc_count_wrap : forall k, 0 < k <= 2 ^ 64 ->
  v_addi (Z_to_bv 64 (2 ^ 64 - k)) 1 = Z_to_bv 64 ((2 ^ 64 - (k - 1)) mod 2 ^ 64).
Proof using.
  intros k Hk. unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small (2 ^ 64 - k)) by lia.
  rewrite Z.mod_mod by lia. f_equal. lia.
Qed.
Local Close Scope Z_scope.

Section BWD.
  Variable mem0 : word -> option byte.
  Variables d s : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis Hn : (0 <= n < 2 ^ 63)%Z.
  Hypothesis Hlen : length bs = Z.to_nat n.
  Hypothesis Hsrc : forall i, (0 <= i < n)%Z -> mem0 (at_ s i) = Some (b_ bs i).
  Hypothesis Hdst : store_ok RSEGS mem0 d (Z.to_nat n) = true.
  Hypothesis Hnws : (bv_unsigned s + n < 2 ^ 64)%Z.
  Hypothesis Hnwd : (bv_unsigned d + n < 2 ^ 64)%Z.
  Hypothesis Hsd : (bv_unsigned s < bv_unsigned d)%Z.

  #[local] Notation MB := (memB mem0 d bs).
  Let RDB : forall k j m, (bv_unsigned s < bv_unsigned d)%Z -> (0 <= j)%Z -> (j + Z.of_nat m <= k)%Z -> (k <= n)%Z ->
      rdn RSEGS (MB k) (at_ s j) m = Some (sub bs (Z.to_nat j) m)
    := ltac:(intros; eapply rdB; eauto).
  Let WRB : forall k j m, (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z -> (0 <= k)%Z -> store_ok RSEGS (MB k) (at_ d j) m = true
    := ltac:(intros; eapply wrB; eauto).
  Let EXTB : forall k m, (Z.of_nat m <= k <= n)%Z ->
      wbytes (MB k) (at_ d (k - Z.of_nat m)) (sub bs (Z.to_nat (k - Z.of_nat m)) m) = MB (k - Z.of_nat m)
    := ltac:(intros; eapply memB_extend; eauto).

  (* [comment removed for export] *)
  Lemma mvB_lbu : forall regs pc w rd rs k j,
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs 0, 4%Z) ->
    getr regs rs = at_ s j ->
    (0 <= j)%Z -> (j + 1 <= k)%Z -> (k <= n)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc (MB k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (b_ bs j))) (v_addi pc 4) (MB k) rom).
  Proof using RDB Hsd Hnwd Hnws Hdst Hsrc Hlen Hn.
    intros regs pc w rd rs k j Hf He Hd Hrs Hj Hjk Hk.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs. imm_norm. rewrite at_addi, Z.add_0_r.
    rewrite (RDB k j 1 Hsd) by lia.
    unfold b_, sub. rewrite <- sub_nth by (rewrite Hlen; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma mvB_sb : forall regs pc w rs1 rs2 k (v : word),
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 0, 4%Z) ->
    getr regs rs1 = at_ d (k - 1) -> getr regs rs2 = v -> Z_to_bv 8 (bv_unsigned v) = b_ bs (k - 1) ->
    (1 <= k <= n)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc (MB k) rom) =
    MachineOk (mkst regs (v_addi pc 4) (MB (k - 1)) rom).
  Proof using EXTB WRB Hnwd Hnws Hdst Hsrc Hlen Hn s.
    intros regs pc w rs1 rs2 k v Hf He Hd Hrs1 Hrs2 Hb Hk.
    replace (k - 1)%Z with (k - Z.of_nat 1)%Z by lia.
    rewrite <- (EXTB k 1) by lia.
    replace (sub bs (Z.to_nat (k - Z.of_nat 1)) 1) with [b_ bs (k - 1)]
      by (unfold b_; replace (k - Z.of_nat 1)%Z with (k - 1)%Z by lia; symmetry; apply sub_nth; rewrite Hlen; lia).
    eapply MmapSim.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | exact Hb |].
    - rewrite Hrs1. imm_norm. rewrite at_addi, Z.add_0_r. first [reflexivity | f_equal; lia].
    - apply WRB; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mvB_ld : forall regs pc w rd rs k j,
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ8 true rd rs 0, 4%Z) ->
    getr regs rs = at_ s j ->
    (0 <= j)%Z -> (j + 8 <= k)%Z -> (k <= n)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc (MB k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LDv (sub bs (Z.to_nat j) 8))) (v_addi pc 4) (MB k) rom).
  Proof using RDB Hsd Hnwd Hnws Hdst Hsrc Hlen Hn.
    intros regs pc w rd rs k j Hf He Hd Hrs Hj Hjk Hk.
    eapply step_ld; [exact Hf | exact He | exact Hd | |].
    - rewrite Hrs. imm_norm. rewrite at_addi, Z.add_0_r. apply (RDB k j 8 Hsd); lia.
    - apply LDv_lez. apply sub_length. rewrite Hlen. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mvB_sd : forall regs pc w rs1 rs2 k,
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ8 rs1 rs2 0, 4%Z) ->
    getr regs rs1 = at_ d (k - 8) -> getr regs rs2 = LDv (sub bs (Z.to_nat (k - 8)) 8) ->
    (8 <= k <= n)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc (MB k) rom) =
    MachineOk (mkst regs (v_addi pc 4) (MB (k - 8)) rom).
  Proof using EXTB WRB Hnwd Hnws Hdst Hsrc Hlen Hn s.
    intros regs pc w rs1 rs2 k Hf He Hd Hrs1 Hrs2 Hk.
    replace (k - 8)%Z with (k - Z.of_nat 8)%Z by lia.
    rewrite <- (EXTB k 8) by lia.
    rewrite <- (sd_bytes_LDv (sub bs (Z.to_nat (k - Z.of_nat 8)) 8)) by (apply sub_length; rewrite Hlen; lia).
    eapply step_sd_at; [exact Hf | exact He | exact Hd | | |].
    - rewrite Hrs1. imm_norm. rewrite at_addi, Z.add_0_r. first [reflexivity | f_equal; lia].
    - rewrite Hrs2. first [reflexivity | f_equal; f_equal; f_equal; lia].
    - apply WRB; lia.
  Qed.

  Ltac blbu F D jj :=
    chain_step; [reflexivity
      | eapply mvB_lbu with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi, ?v_add_at_any, ?v_add_any_at; unorm; first [reflexivity | f_equal; lia] | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac bld F D jj :=
    chain_step; [reflexivity
      | eapply mvB_ld with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi, ?v_add_at_any, ?v_add_any_at; unorm; first [reflexivity | f_equal; lia] | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mb_at kk := match goal with |- msteps _ (mkst _ _ (MB ?a) _) _ =>
                     first [constr_eq a kk | replace (MB a) with (MB kk) by (f_equal; lia)] end.
  Ltac bsb F D kk :=
    mb_at kk;
    chain_step; [reflexivity
      | eapply mvB_sb with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi, ?v_add_at_any, ?v_add_any_at; unorm; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity | apply sb_byte_LBv | lia]
      | step_simpl].
  Ltac bsd F D kk :=
    mb_at kk;
    chain_step; [reflexivity
      | eapply mvB_sd with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi, ?v_add_at_any, ?v_add_any_at; unorm; first [reflexivity | f_equal; lia]
        | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; f_equal; f_equal; lia] | lia]
      | step_simpl].
  Ltac cond :=
    rwH; rewrite ?at_addi; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unfold at_, v_addi; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_7 by lia; lia.
  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia); try solve_keeps.


  (* [comment removed for export] *)
  Lemma bwd_bloop : forall i regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ s (k - 1) -> getr regs 13 = at_ d (k - 1) -> getr regs 12 = Z_to_bv 64 (2 ^ 64 - k) ->
    (1 <= k <= n)%Z -> (k = Z.of_nat (S i))%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x73728 : word) (MB k) rom) (mkst regs' ret (MB 0) rom)
      /\ keeps regs regs'.
  Proof using EXTB WRB RDB Hsd Hnwd Hnws Hdst Hsrc Hlen Hn.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hi.
    - (* [comment removed for export] *)
      pose proof (u64_range s). pose proof (u64_range d).
      eexists. split.
      + blbu F_736d4 D_736d4 (k - 1)%Z.
        stepn F_736d8 D_736d8.
        bsb F_736dc D_736dc k.
        stepn F_736e0 D_736e0.
        stepn F_736e4 D_736e4.
        stepb_ft F_736e8 D_736e8 ltac:(rwH; rewrite inc_count_wrap by lia; cond).
        stepjr F_736ec D_736ec ret ltac:(gres; rwH; reflexivity).
        imm_norm. rewrite Hret. replace (MB (k - 1)) with (MB 0) by (f_equal; lia). pu_refl.
      + solve_keeps.
    - pose proof (u64_range s). pose proof (u64_range d).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x73728 : word) (MB (k - 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ s (k - 1 - 1) /\ getr r 13 = at_ d (k - 1 - 1)
                         /\ getr r 12 = Z_to_bv 64 (2 ^ 64 - (k - 1)) /\ keeps regs r)).
      + eexists. split.
        * blbu F_736d4 D_736d4 (k - 1)%Z.
          stepn F_736d8 D_736d8.
          bsb F_736dc D_736dc k.
          stepn F_736e0 D_736e0.
          stepn F_736e4 D_736e4.
          stepb_tk F_736e8 D_736e8 ltac:(rwH; rewrite inc_count_wrap by lia; cond).
          pu_refl.
        * post. rewrite inc_count_wrap by lia. f_equal. rewrite Z.mod_small; lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (IH r1 ret (k - 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  Lemma bwd_bytes : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = d -> getr regs 11 = s -> getr regs 13 = Z_to_bv 64 k ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x73714 : word) (MB k) rom) (mkst regs' ret (MB 0) rom)
      /\ keeps regs regs'.
  Proof using EXTB WRB RDB Hsd Hnwd Hnws Hdst Hsrc Hlen Hn.
    intros regs ret k Hret H1 H10 H11 H13 Hk.
    pose proof (u64_range s). pose proof (u64_range d).
    destruct (Z.eq_dec k 0) as [->|Hk0].
    - eexists. split; [|apply keeps_refl].
      stepb_tk F_736c0 D_736c0 ltac:(cond).
      stepjr F_736ec D_736ec ret ltac:(gres; rwH; reflexivity).
      imm_norm. rewrite Hret. pu_refl.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x73728 : word) (MB k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ s (k - 1) /\ getr r 13 = at_ d (k - 1)
                         /\ getr r 12 = Z_to_bv 64 (2 ^ 64 - k) /\ keeps regs r)).
      + eexists. split.
        * stepb_ft F_736c0 D_736c0 ltac:(cond).
          stepn F_736c4 D_736c4.
          stepn F_736c8 D_736c8.
          stepn F_736cc D_736cc.
          stepn F_736d0 D_736d0.
          pu_refl.
        * post.
          -- rewrite <- (at_0 s) at 1. unfold v_addi. unorm. rewrite v_add_at_Z by lia. first [reflexivity | f_equal; lia].
          -- rewrite <- (at_0 d) at 1. unfold v_addi. unorm. rewrite v_add_at_Z by lia. first [reflexivity | f_equal; lia].
          -- apply neg_count_eq. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (bwd_bloop (Z.to_nat (k - 1)) r1 ret k Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  Lemma bwd_wloop : forall i regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = d -> getr regs 11 = s ->
    getr regs 12 = Z_to_bv 64 k -> getr regs 14 = at_ s (-8) -> getr regs 15 = at_ d (-8) -> getr regs 16 = Z_to_bv 64 7 ->
    (k <= n)%Z -> (8 * Z.of_nat (S i) <= k < 8 * Z.of_nat (S i) + 8)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x737e0 : word) (MB k) rom) (mkst regs' ret (MB 0) rom)
      /\ keeps regs regs'.
  Proof using EXTB WRB RDB Hsd Hnwd Hnws Hdst Hsrc Hlen Hn.
    induction i as [|i IH]; intros regs ret k Hret H1 H10 H11 H12 H14 H15 H16 Hk Hi.
    - pose proof (u64_range s). pose proof (u64_range d).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x73714 : word) (MB (k - 8)) rom)
               (fun r => getr r 1 = ret /\ getr r 10 = d /\ getr r 11 = s /\ getr r 13 = Z_to_bv 64 (k - 8) /\ keeps regs r)).
      + eexists. split.
        * stepn F_7378c D_7378c.
          bld F_73790 D_73790 (k - 8)%Z.
          stepn F_73794 D_73794.
          stepn F_73798 D_73798.
          bsd F_7379c D_7379c k.
          stepn F_737a0 D_737a0.
          stepb_ft F_737a4 D_737a4 ltac:(cond).
          stepn F_737a8 D_737a8.
          pu_refl.
        * post. unfold v_addi. unorm. first [reflexivity | f_equal; lia].
      + cbv beta. intros r1 (R1 & R10 & R11 & R13 & K1).
        destruct (bwd_bytes r1 ret (k - 8) Hret R1 R10 R11 R13 ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - pose proof (u64_range s). pose proof (u64_range d).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x737e0 : word) (MB (k - 8)) rom)
               (fun r => getr r 1 = ret /\ getr r 10 = d /\ getr r 11 = s /\ getr r 12 = Z_to_bv 64 (k - 8)
                         /\ getr r 14 = at_ s (-8) /\ getr r 15 = at_ d (-8) /\ getr r 16 = Z_to_bv 64 7 /\ keeps regs r)).
      + eexists. split.
        * stepn F_7378c D_7378c.
          bld F_73790 D_73790 (k - 8)%Z.
          stepn F_73794 D_73794.
          stepn F_73798 D_73798.
          bsd F_7379c D_7379c k.
          stepn F_737a0 D_737a0.
          stepb_tk F_737a4 D_737a4 ltac:(cond).
          pu_refl.
        * post. unfold v_addi. unorm. first [reflexivity | f_equal; lia].
      + cbv beta. intros r1 (R1 & R10 & R11 & R12 & R14 & R15 & R16 & K1).
        destruct (IH r1 ret (k - 8)%Z Hret R1 R10 R11 R12 R14 R15 R16 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  Lemma bwd_words : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = Z_to_bv 64 k ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x737cc : word) (MB k) rom) (mkst regs' ret (MB 0) rom)
      /\ keeps regs regs'.
  Proof using EXTB WRB RDB Hsd Hnwd Hnws Hdst Hsrc Hlen Hn.
    intros regs ret k Hret H1 H10 H11 H12 Hk.
    pose proof (u64_range s). pose proof (u64_range d).
    destruct (Z.lt_ge_cases k 8) as [Hlt|Hge].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x73714 : word) (MB k) rom)
               (fun r => getr r 1 = ret /\ getr r 10 = d /\ getr r 11 = s /\ getr r 13 = Z_to_bv 64 k /\ keeps regs r)).
      + eexists. split.
        * stepn F_73778 D_73778.
          stepb_tk F_7377c D_7377c ltac:(cond).
          stepn F_736bc D_736bc.
          pu_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R11 & R13 & K1).
        destruct (bwd_bytes r1 ret k Hret R1 R10 R11 R13 ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x737e0 : word) (MB k) rom)
               (fun r => getr r 1 = ret /\ getr r 10 = d /\ getr r 11 = s /\ getr r 12 = Z_to_bv 64 k
                         /\ getr r 14 = at_ s (-8) /\ getr r 15 = at_ d (-8) /\ getr r 16 = Z_to_bv 64 7 /\ keeps regs r)).
      + eexists. split.
        * stepn F_73778 D_73778.
          stepb_ft F_7377c D_7377c ltac:(cond).
          stepn F_73780 D_73780.
          stepn F_73784 D_73784.
          stepn F_73788 D_73788.
          pu_refl.
        * post; unfold v_addi, at_; first [reflexivity | f_equal; lia].
      + cbv beta. intros r1 (R1 & R10 & R11 & R12 & R14 & R15 & R16 & K1).
        destruct (bwd_wloop (Z.to_nat (k / 8 - 1)) r1 ret k Hret R1 R10 R11 R12 R14 R15 R16 ltac:(lia)) as (r2 & RUN & K2).
        { split; nia. }
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  Lemma bwd_align : forall i regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = d -> getr regs 11 = s ->
    getr regs 14 = at_ s (k - 1) -> getr regs 12 = at_ d (k - 1) -> getr regs 15 = at_ d (k - 1) ->
    getr regs 13 = Z_to_bv 64 (2 ^ 64 - k) ->
    (1 <= k <= n)%Z -> (Z.of_nat (S i) = (bv_unsigned d + k) mod 8)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x737a4 : word) (MB k) rom) (mkst regs' ret (MB 0) rom)
      /\ keeps regs regs'.
  Proof using EXTB WRB RDB Hsd Hnwd Hnws Hdst Hsrc Hlen Hn.
    induction i as [|i IH]; intros regs ret k Hret H1 H10 H11 H14 H12 H15 H13 Hk Hi;
      pose proof (u64_range s); pose proof (u64_range d).
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x737cc : word) (MB (k - 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 10 = d /\ getr r 11 = s /\ getr r 12 = Z_to_bv 64 (k - 1) /\ keeps regs r)).
      + eexists. split.
        * stepb_ft F_73750 D_73750 ltac:(cond).
          blbu F_73754 D_73754 (k - 1)%Z.
          bsb F_73758 D_73758 k.
          stepn F_7375c D_7375c.
          stepn F_73760 D_73760.
          stepn F_73764 D_73764.
          stepn F_73768 D_73768.
          stepn F_7376c D_7376c.
          stepb_ft F_73770 D_73770 ltac:(cond).
          stepn F_73774 D_73774.
          pu_refl.
        * post. rewrite inc_count_wrap by lia.
          destruct (Z.eq_dec k 1) as [->|Hk1].
          -- rewrite Z.sub_diag. change ((2 ^ 64 - 0) mod 2 ^ 64)%Z with 0%Z. unfold v_sub. unorm. reflexivity.
          -- rewrite Z.mod_small by lia. apply neg_neg_count. lia.
      + cbv beta. intros r1 (R1 & R10 & R11 & R12 & K1).
        destruct (bwd_words r1 ret (k - 1) Hret R1 R10 R11 R12 ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec k 1) as [->|Hk1].
      + (* [comment removed for export] *)
        eexists. split.
        * stepb_ft F_73750 D_73750 ltac:(cond).
          blbu F_73754 D_73754 0%Z.
          bsb F_73758 D_73758 1%Z.
          stepn F_7375c D_7375c.
          stepn F_73760 D_73760.
          stepn F_73764 D_73764.
          stepn F_73768 D_73768.
          stepn F_7376c D_7376c.
          stepb_tk F_73770 D_73770 ltac:(cond).
          stepb_tk F_73750 D_73750 ltac:(rwH; rewrite inc_count_wrap by lia; cond).
          stepjr F_736ec D_736ec ret ltac:(gres; rwH; reflexivity).
          imm_norm. rewrite Hret. replace (MB (1 - 1)) with (MB 0) by (f_equal; lia). pu_refl.
        * solve_keeps.
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x737a4 : word) (MB (k - 1)) rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = d /\ getr r 11 = s
                           /\ getr r 14 = at_ s (k - 1 - 1) /\ getr r 12 = at_ d (k - 1 - 1) /\ getr r 15 = at_ d (k - 1 - 1)
                           /\ getr r 13 = Z_to_bv 64 (2 ^ 64 - (k - 1)) /\ keeps regs r)).
        * eexists. split.
          -- stepb_ft F_73750 D_73750 ltac:(cond).
             blbu F_73754 D_73754 (k - 1)%Z.
             bsb F_73758 D_73758 k.
             stepn F_7375c D_7375c.
             stepn F_73760 D_73760.
             stepn F_73764 D_73764.
             stepn F_73768 D_73768.
             stepn F_7376c D_7376c.
             stepb_tk F_73770 D_73770 ltac:(cond).
             pu_refl.
          -- post. rewrite inc_count_wrap by lia. f_equal. rewrite Z.mod_small; lia.
        * cbv beta. intros r1 (R1 & R10 & R11 & R14 & R12 & R15 & R13 & K1).
          destruct (IH r1 ret (k - 1)%Z Hret R1 R10 R11 R14 R12 R15 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  Lemma bwd_entry : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0x736cc : word) (MB n) rom) (mkst regs' ret (MB 0) rom)
      /\ keeps regs regs'.
  Proof using EXTB WRB RDB Hsd Hnwd Hnws Hdst Hsrc Hlen Hn.
    intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range s). pose proof (u64_range d).
    destruct (c_eq (v_andi (v_xor s d) 7) (Z_to_bv 64 0)) eqn:EQ.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec ((bv_unsigned d + n) mod 8) 0) as [Hal|Hal].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x737cc : word) (MB n) rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = d /\ getr r 11 = s /\ getr r 12 = Z_to_bv 64 n /\ keeps regs r)).
        * eexists. split.
          -- stepn F_73678 D_73678.
             stepn F_7367c D_7367c.
             stepb_tk F_73680 D_73680 ltac:(cond).
             stepb_tk F_736b8 D_736b8 ltac:(rwH; exact EQ).
             stepn F_73730 D_73730.
             stepn F_73734 D_73734.
             stepb_tk F_73738 D_73738 ltac:(rwH; rewrite <- (at_0 d), v_add_at_Z by lia; cond).
             pu_refl.
          -- post.
        * cbv beta. intros r1 (R1 & R10 & R11 & R12 & K1).
          destruct (bwd_words r1 ret n Hret R1 R10 R11 R12 ltac:(lia)) as (r2 & RUN & K2).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
      + destruct (Z.eq_dec n 0) as [Hn0|Hn0].
        * (* [comment removed for export] *)
          eexists. split.
          -- stepn F_73678 D_73678.
             stepn F_7367c D_7367c.
             stepb_tk F_73680 D_73680 ltac:(cond).
             stepb_tk F_736b8 D_736b8 ltac:(rwH; exact EQ).
             stepn F_73730 D_73730.
             stepn F_73734 D_73734.
             stepb_ft F_73738 D_73738 ltac:(rwH; rewrite <- (at_0 d), v_add_at_Z by lia; cond).
             stepn F_7373c D_7373c.
             stepn F_73740 D_73740.
             stepn F_73744 D_73744.
             stepn F_73748 D_73748.
             stepn F_7374c D_7374c.
             stepb_tk F_73750 D_73750 ltac:(rwH; subst n; unfold v_sub; cond).
             stepjr F_736ec D_736ec ret ltac:(gres; rwH; reflexivity).
             imm_norm. rewrite Hret. subst n. pu_refl.
          -- solve_keeps.
        * eapply (runs_trans RSEGS _ (fun r => mkst r (0x737a4 : word) (MB n) rom)
                   (fun r => getr r 1 = ret /\ getr r 10 = d /\ getr r 11 = s
                             /\ getr r 14 = at_ s (n - 1) /\ getr r 12 = at_ d (n - 1) /\ getr r 15 = at_ d (n - 1)
                             /\ getr r 13 = Z_to_bv 64 (2 ^ 64 - n) /\ keeps regs r)).
          -- eexists. split.
             ++ stepn F_73678 D_73678.
                stepn F_7367c D_7367c.
                stepb_tk F_73680 D_73680 ltac:(cond).
                stepb_tk F_736b8 D_736b8 ltac:(rwH; exact EQ).
                stepn F_73730 D_73730.
                stepn F_73734 D_73734.
                stepb_ft F_73738 D_73738 ltac:(rwH; rewrite <- (at_0 d), v_add_at_Z by lia; cond).
                stepn F_7373c D_7373c.
                stepn F_73740 D_73740.
                stepn F_73744 D_73744.
                stepn F_73748 D_73748.
                stepn F_7374c D_7374c.
                pu_refl.
             ++ post.
                ** rewrite <- (at_0 s) at 1. unfold v_addi. unorm. rewrite v_add_at_Z by lia. first [reflexivity | f_equal; lia].
                ** rewrite <- (at_0 d) at 1. unfold v_addi. unorm. rewrite v_add_at_Z by lia. first [reflexivity | f_equal; lia].
                ** rewrite <- (at_0 d) at 1. unfold v_addi. unorm. rewrite v_add_at_Z by lia. first [reflexivity | f_equal; lia].
                ** apply neg_count_eq. lia.
          -- cbv beta. intros r1 (R1 & R10 & R11 & R14 & R12 & R15 & R13 & K1).
             destruct (bwd_align (Z.to_nat ((bv_unsigned d + n) mod 8 - 1)) r1 ret n Hret R1 R10 R11 R14 R12 R15 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
             exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x73714 : word) (MB n) rom)
               (fun r => getr r 1 = ret /\ getr r 10 = d /\ getr r 11 = s /\ getr r 13 = Z_to_bv 64 n /\ keeps regs r)).
      + eexists. split.
        * stepn F_73678 D_73678.
          stepn F_7367c D_7367c.
          stepb_tk F_73680 D_73680 ltac:(cond).
          stepb_ft F_736b8 D_736b8 ltac:(rwH; exact EQ).
          stepn F_736bc D_736bc.
          pu_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R11 & R13 & K1).
        destruct (bwd_bytes r1 ret n Hret R1 R10 R11 R13 ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.
End BWD.
End FPGen4.


