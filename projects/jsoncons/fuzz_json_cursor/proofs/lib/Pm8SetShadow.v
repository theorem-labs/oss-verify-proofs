(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit MemsetLib As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8SumsMemset_code Pm8SumsMemset.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8SetShadowTab.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section FPX_1. Context {fx : PropExec.FPState}.

Definition setsh_globs (M : word -> option byte) : Prop :=
  rdn ASEGS M (0x153158 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x155160)) /\
  rdn ASEGS M (0x155160 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x145308)).

Lemma ms_agree_keeps_cs : forall regs regs', ms_agree regs regs' -> keeps_cs regs regs'.
Proof.
  intros regs regs' H r Hr. apply H. unfold callee_saved in Hr. unfold ms_clob. cbn [In] in *.
  intros Hc. decompose [or] Hr; subst; decompose [or] Hc; try discriminate; auto.
Qed.

Section SETSH.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variable ra : word.
  Variables sa n : Z.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hsa : (0 <= sa)%Z /\ (sa + n < 2 ^ 64)%Z.
  Hypothesis Hdst : store_ok ASEGS mem0 (Z_to_bv 64 sa) (Z.to_nat n) = true.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HG : setsh_globs mem0.

  #[local] Ltac rwH :=
    repeat match goal with
           | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
           end.
  #[local] Ltac mvval := gres; rwH; rewrite ?v_addi_0; reflexivity.

  Theorem setsh_00_run : forall regs,
    getr regs 10 = Z_to_bv 64 sa -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x829e4 : word) mem0 rom) (mkst regs' ra (wbytes mem0 (Z_to_bv 64 sa) (repeat (Z_to_bv 8 0) (Z.to_nat n))) rom)
      /\ keeps_cs regs regs'.
  Proof.
    intros regs H10 H11 H1. destruct HG as (G1 & G2).
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x829e4 : word) mem0 rom) (mkst r1 (0x145308 : word) mem0 rom)
              /\ getr r1 10 = Z_to_bv 64 sa /\ getr r1 11 = Z_to_bv 64 0 /\ getr r1 12 = Z_to_bv 64 n /\ getr r1 1 = ra /\ keeps_cs regs r1).
    { eexists. split.
      - stepiv Fx_82994 Dx_82994 (Z_to_bv 64 n) ltac:(mvval).
      stepn Fx_82998 Dx_82998.
      mld Fx_8299c Dx_8299c (0x153158 : word) G1.
      mld Fx_829a0 Dx_829a0 (0x155160 : word) G2.
      stepn Fx_829a4 Dx_829a4.
      stepjr Fx_829a8 Dx_829a8 (Z_to_bv 64 0x145308) ltac:(gres; reflexivity).
        vnorm. apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_cs. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & K1).
    replace (0x145308 : word) with (Z_to_bv 64 ms_base) in RUN1 by (apply bv_eq; vm_compute; reflexivity).
    pose proof (memset_summary mem0 (Z_to_bv 64 sa) (Z_to_bv 64 0) ra n rom Hn ltac:(rewrite u_Z2bv by lia; lia) Hdst Hret r1 Q10 Q11 Q12 Q1) as (r2 & RUN2 & _ & AG).
    replace (cbyte (Z_to_bv 64 0)) with (Z_to_bv 8 0 : byte) in RUN2 by (apply bv_eq; vm_compute; reflexivity).
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | eapply keeps_cs_trans; [exact K1 | exact (ms_agree_keeps_cs _ _ AG)]].
  Qed.

  Theorem setsh_f5_run : forall regs,
    getr regs 10 = Z_to_bv 64 sa -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x82aec : word) mem0 rom) (mkst regs' ra (wbytes mem0 (Z_to_bv 64 sa) (repeat (Z_to_bv 8 245) (Z.to_nat n))) rom)
      /\ keeps_cs regs regs'.
  Proof.
    intros regs H10 H11 H1. destruct HG as (G1 & G2).
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x82aec : word) mem0 rom) (mkst r1 (0x145308 : word) mem0 rom)
              /\ getr r1 10 = Z_to_bv 64 sa /\ getr r1 11 = Z_to_bv 64 245 /\ getr r1 12 = Z_to_bv 64 n /\ getr r1 1 = ra /\ keeps_cs regs r1).
    { eexists. split.
      - stepn Fx_82a9c Dx_82a9c.
      mld Fx_82aa0 Dx_82aa0 (0x153158 : word) G1.
      mld Fx_82aa4 Dx_82aa4 (0x155160 : word) G2.
      stepiv Fx_82aa8 Dx_82aa8 (Z_to_bv 64 n) ltac:(mvval).
      stepn Fx_82aac Dx_82aac.
      stepjr Fx_82ab0 Dx_82ab0 (Z_to_bv 64 0x145308) ltac:(gres; reflexivity).
        vnorm. apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_cs. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & K1).
    replace (0x145308 : word) with (Z_to_bv 64 ms_base) in RUN1 by (apply bv_eq; vm_compute; reflexivity).
    pose proof (memset_summary mem0 (Z_to_bv 64 sa) (Z_to_bv 64 245) ra n rom Hn ltac:(rewrite u_Z2bv by lia; lia) Hdst Hret r1 Q10 Q11 Q12 Q1) as (r2 & RUN2 & _ & AG).
    replace (cbyte (Z_to_bv 64 245)) with (Z_to_bv 8 245 : byte) in RUN2 by (apply bv_eq; vm_compute; reflexivity).
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | eapply keeps_cs_trans; [exact K1 | exact (ms_agree_keeps_cs _ _ AG)]].
  Qed.

  Theorem setsh_f8_run : forall regs,
    getr regs 10 = Z_to_bv 64 sa -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x82b04 : word) mem0 rom) (mkst regs' ra (wbytes mem0 (Z_to_bv 64 sa) (repeat (Z_to_bv 8 248) (Z.to_nat n))) rom)
      /\ keeps_cs regs regs'.
  Proof.
    intros regs H10 H11 H1. destruct HG as (G1 & G2).
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x82b04 : word) mem0 rom) (mkst r1 (0x145308 : word) mem0 rom)
              /\ getr r1 10 = Z_to_bv 64 sa /\ getr r1 11 = Z_to_bv 64 248 /\ getr r1 12 = Z_to_bv 64 n /\ getr r1 1 = ra /\ keeps_cs regs r1).
    { eexists. split.
      - stepn Fx_82ab4 Dx_82ab4.
      mld Fx_82ab8 Dx_82ab8 (0x153158 : word) G1.
      mld Fx_82abc Dx_82abc (0x155160 : word) G2.
      stepiv Fx_82ac0 Dx_82ac0 (Z_to_bv 64 n) ltac:(mvval).
      stepn Fx_82ac4 Dx_82ac4.
      stepjr Fx_82ac8 Dx_82ac8 (Z_to_bv 64 0x145308) ltac:(gres; reflexivity).
        vnorm. apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_cs. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & K1).
    replace (0x145308 : word) with (Z_to_bv 64 ms_base) in RUN1 by (apply bv_eq; vm_compute; reflexivity).
    pose proof (memset_summary mem0 (Z_to_bv 64 sa) (Z_to_bv 64 248) ra n rom Hn ltac:(rewrite u_Z2bv by lia; lia) Hdst Hret r1 Q10 Q11 Q12 Q1) as (r2 & RUN2 & _ & AG).
    replace (cbyte (Z_to_bv 64 248)) with (Z_to_bv 8 248 : byte) in RUN2 by (apply bv_eq; vm_compute; reflexivity).
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | eapply keeps_cs_trans; [exact K1 | exact (ms_agree_keeps_cs _ _ AG)]].
  Qed.

End SETSH.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
