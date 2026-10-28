(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0RegionPoisoned_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r71324_71340_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub; imm_norm; unorm; first [reflexivity | f_equal; lia].

Lemma rdn_byte_at : forall (M : word -> option byte) a n bs j,
  rdn ASEGS M (Z_to_bv 64 a) n = Some bs -> (j < n)%nat -> (0 <= a)%Z -> (a + Z.of_nat j < 2 ^ 64)%Z ->
  rdn ASEGS M (Z_to_bv 64 (a + Z.of_nat j)) 1%nat = Some [nth j bs (Z_to_bv 8 0)].
Proof.
  intros M a n bs j H Hj Ha Hn.
  pose proof (rdn_nth ASEGS M n (Z_to_bv 64 a) bs j H Hj) as R.
  replace (Z_to_bv 64 a + nat_to_word j) with (Z_to_bv 64 (a + Z.of_nat j)) in R; [exact R|].
  apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
Qed.

Section ISL.
  Variable M rom : word -> option byte.
  Variable p : Z.
  Variable bs : list byte.
  Hypothesis Hp : (0 <= p)%Z /\ (p + Z.of_nat (length bs) + 1 < 2 ^ 63)%Z.
  Hypothesis HS : rdn ASEGS M (Z_to_bv 64 p) (length bs + 1) = Some (bs ++ [Z_to_bv 8 0]).
  Hypothesis HNZ : forall j, (j < length bs)%nat -> bv_unsigned (nth j bs (Z_to_bv 8 0)) <> 0%Z.

  #[local] Notation n := (Z.of_nat (length bs)).

  Lemma byte_j : forall j, (j <= length bs)%nat ->
    rdn ASEGS M (Z_to_bv 64 (p + Z.of_nat j)) 1%nat = Some [nth j (bs ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)].
  Proof. intros j Hj. apply (rdn_byte_at M p (length bs + 1)); [exact HS | lia | lia | lia]. Qed.

  (* [comment removed for export] *)
  Lemma isl_loop : forall (q : nat) regs (ret : word) (j : nat),
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 (Z.of_nat j) ->
    (j + q = length bs)%nat ->
    exists regs',
      msteps ASEGS (mkst regs (0x8b5b8 : word) M rom) (mkst regs' ret M rom)
      /\ getr regs' 10 = Z_to_bv 64 n /\ keeps_cs regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret j Hret H1 H10 H11 Hq.
    - (* [comment removed for export] *)
      assert (B : rdn ASEGS M (Z_to_bv 64 (p + Z.of_nat j)) 1%nat = Some [Z_to_bv 8 0]).
      { rewrite (byte_j j) by lia. rewrite app_nth2 by lia. replace (j - length bs)%nat with 0%nat by lia. reflexivity. }
      eexists. split.
      + stepiv F_8b1a0 D_8b1a0 (Z_to_bv 64 (p + Z.of_nat j)) ltac:(wval).                   (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_lbu; [exact F_8b1a4 | reflexivity | exact D_8b1a4 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact B] | step_simpl; vnorm].
        stepiv F_8b1a8 D_8b1a8 (Z_to_bv 64 (Z.of_nat j + 1)) ltac:(wval).                    (* [comment removed for export] *)
        stepb_ft F_8b1ac D_8b1ac ltac:(cond).                                               (* [comment removed for export] *)
        stepiv F_8b1b0 D_8b1b0 (Z_to_bv 64 n) ltac:(wval).                                   (* [comment removed for export] *)
        stepret F_8b1b4 D_8b1b4 ret ltac:(rwH; reflexivity).
        apply mst_refl.
      + split; [gres; reflexivity | solve_keeps_cs].
    - assert (B : rdn ASEGS M (Z_to_bv 64 (p + Z.of_nat j)) 1%nat = Some [nth j bs (Z_to_bv 8 0)]).
      { rewrite (byte_j j) by lia. rewrite app_nth1 by lia. reflexivity. }
      pose proof (HNZ j ltac:(lia)) as NZ. pose proof (u8_range (nth j bs (Z_to_bv 8 0))) as R8.
      eapply (runs_trans ASEGS _ (fun r => mkst r (0x8b5b8 : word) M rom)
               (fun r => getr r 1 = ret /\ getr r 10 = Z_to_bv 64 p /\ getr r 11 = Z_to_bv 64 (Z.of_nat (Datatypes.S j)) /\ keeps_cs regs r)).
      + eexists. split.
        * stepiv F_8b1a0 D_8b1a0 (Z_to_bv 64 (p + Z.of_nat j)) ltac:(wval).
          chain_step; [reflexivity | eapply step_lbu; [exact F_8b1a4 | reflexivity | exact D_8b1a4 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact B] | step_simpl; vnorm].
          stepiv F_8b1a8 D_8b1a8 (Z_to_bv 64 (Z.of_nat j + 1)) ltac:(wval).
          stepb_tk F_8b1ac D_8b1ac ltac:(cond).                                             (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. repeat split; gres; rwH; try reflexivity; try (f_equal; lia). solve_keeps_cs.
      + cbv beta. intros r1 (R1 & R10 & R11 & K1).
        destruct (IH r1 ret (Datatypes.S j) Hret R1 R10 R11 ltac:(lia)) as (r2 & RUN & V & K2).
        exists r2. split; [exact RUN | split; [exact V | eapply keeps_cs_trans; eassumption]].
  Qed.

  Theorem internal_strlen_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 p ->
    exists regs',
      msteps ASEGS (mkst regs (0x8b5b4 : word) M rom) (mkst regs' ret M rom)
      /\ getr regs' 10 = Z_to_bv 64 n /\ keeps_cs regs regs'.
  Proof.
    intros regs ret Hret H1 H10.
    eapply (runs_trans ASEGS _ (fun r => mkst r (0x8b5b8 : word) M rom)
             (fun r => getr r 1 = ret /\ getr r 10 = Z_to_bv 64 p /\ getr r 11 = Z_to_bv 64 (Z.of_nat 0) /\ keeps_cs regs r)).
    - eexists. split.
      + stepn F_8b19c D_8b19c. apply mst_refl.
      + cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps_cs.
    - cbv beta. intros r1 (R1 & R10 & R11 & K1).
      destruct (isl_loop (length bs) r1 ret 0%nat Hret R1 R10 R11 ltac:(lia)) as (r2 & RUN & V & K2).
      exists r2. split; [exact RUN | split; [exact V | eapply keeps_cs_trans; eassumption]].
  Qed.
End ISL.
End FPX_1.
