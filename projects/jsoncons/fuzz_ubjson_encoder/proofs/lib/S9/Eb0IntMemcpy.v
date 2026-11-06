(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import muslA.Eb0MemcpyBaseS9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r71154_71230.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.

Section ALL.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  Ltac cond :=
    rwH; rewrite ?at_addi; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.

  Lemma loop_run : forall (q : nat) regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = at_ dst n ->
    (0 <= k)%Z -> (k + Z.of_nat q + 1 = n)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x8c59c : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hq;
      pose proof (u64_range src); pose proof (u64_range dst).
    - eexists. split.
      + mlbu F_8c54c D_8c54c k.
        msb F_8c550 D_8c550 k ltac:(apply sb_val_plain).
        stepn F_8c554 D_8c554.
        stepn F_8c558 D_8c558.
        stepb_ft F_8c55c D_8c55c ltac:(cond).
        stepret F_8c560 D_8c560 ret ltac:(rwH; reflexivity).
        replace (MK (k + 1)) with (MK n) by (f_equal; lia).
        apply mst_refl.
      + post.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x8c59c : word) (MK (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = at_ dst n /\ keeps regs r)).
      + eexists. split.
        * mlbu F_8c54c D_8c54c k.
          msb F_8c550 D_8c550 k ltac:(apply sb_val_plain).
          stepn F_8c554 D_8c554.
          stepn F_8c558 D_8c558.
          stepb_tk F_8c55c D_8c55c ltac:(cond).
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  Theorem int_memcpy_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0x8c590 : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11 H12. pose proof (u64_range src); pose proof (u64_range dst).
    rewrite <- (memk_n mem0 dst src n bs HOK).
    replace (mkst regs (0x8c590 : word) mem0 rom) with (mkst regs (0x8c590 : word) (MK 0) rom) by reflexivity.
    destruct (Z.eq_dec n 0) as [Hz|Hz].
    - eexists. split.
      + stepb_tk F_8c540 D_8c540 ltac:(cond).
        stepret F_8c560 D_8c560 ret ltac:(rwH; reflexivity).
        replace (MK 0) with (MK n) by (f_equal; lia).
        apply mst_refl.
      + post.
    - assert (Hq : exists q : nat, (Z.of_nat q + 1 = n)%Z) by (exists (Z.to_nat (n - 1)); rewrite Z2Nat.id; lia).
      destruct Hq as (q & Hq).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x8c59c : word) (MK 0) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = at_ dst n /\ keeps regs r)).
      + eexists. split.
        * stepb_ft F_8c540 D_8c540 ltac:(cond).
          stepn F_8c544 D_8c544.
          stepn F_8c548 D_8c548.
          apply mst_refl.
        * cbv beta. post.
          -- rewrite at_0. reflexivity.
          -- rewrite at_0. reflexivity.
          -- unfold v_add, at_. f_equal. unorm. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (loop_run q r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.
End ALL.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
