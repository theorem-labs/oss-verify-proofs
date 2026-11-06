(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit MemsetLib As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4SumsMemset_code Pm4SumsMemset.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4SetShadowTab.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition setsh_globs (M : word -> option byte) : Prop :=
  rdn ASEGS M (0x160c38 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x162c50)) /\
  rdn ASEGS M (0x162c50 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x152ea4)).

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

  (* [comment removed for export] *)
  Theorem setsh_00_run : forall regs,
    getr regs 10 = Z_to_bv 64 sa -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x83db0 : word) mem0 rom) (mkst regs' ra (wbytes mem0 (Z_to_bv 64 sa) (repeat (Z_to_bv 8 0) (Z.to_nat n))) rom)
      /\ keeps_cs regs regs'.
  Proof.
    intros regs H10 H11 H1. destruct HG as (G1 & G2).
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x83db0 : word) mem0 rom) (mkst r1 (0x152ea4 : word) mem0 rom)
              /\ getr r1 10 = Z_to_bv 64 sa /\ getr r1 11 = Z_to_bv 64 0 /\ getr r1 12 = Z_to_bv 64 n /\ getr r1 1 = ra /\ keeps_cs regs r1).
    { eexists. split.
      - stepiv Fx_83d60 Dx_83d60 (Z_to_bv 64 n) ltac:(mvval).                                  (* [comment removed for export] *)
      stepn Fx_83d64 Dx_83d64.                                                               (* [comment removed for export] *)
      mld Fx_83d68 Dx_83d68 (0x160c38 : word) G1.                                            (* [comment removed for export] *)
      mld Fx_83d6c Dx_83d6c (0x162c50 : word) G2.                                            (* [comment removed for export] *)
      stepn Fx_83d70 Dx_83d70.                                                               (* [comment removed for export] *)
      stepjr Fx_83d74 Dx_83d74 (Z_to_bv 64 0x152ea4) ltac:(gres; reflexivity).              (* [comment removed for export] *)
        vnorm. apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_cs. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & K1).
    replace (0x152ea4 : word) with (Z_to_bv 64 ms_base) in RUN1 by (apply bv_eq; vm_compute; reflexivity).
    pose proof (memset_summary mem0 (Z_to_bv 64 sa) (Z_to_bv 64 0) ra n rom Hn ltac:(rewrite u_Z2bv by lia; lia) Hdst Hret r1 Q10 Q11 Q12 Q1) as (r2 & RUN2 & _ & AG).
    replace (cbyte (Z_to_bv 64 0)) with (Z_to_bv 8 0 : byte) in RUN2 by (apply bv_eq; vm_compute; reflexivity).
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | eapply keeps_cs_trans; [exact K1 | exact (ms_agree_keeps_cs _ _ AG)]].
  Qed.

  (* [comment removed for export] *)
  Theorem setsh_f5_run : forall regs,
    getr regs 10 = Z_to_bv 64 sa -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x83eb8 : word) mem0 rom) (mkst regs' ra (wbytes mem0 (Z_to_bv 64 sa) (repeat (Z_to_bv 8 245) (Z.to_nat n))) rom)
      /\ keeps_cs regs regs'.
  Proof.
    intros regs H10 H11 H1. destruct HG as (G1 & G2).
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x83eb8 : word) mem0 rom) (mkst r1 (0x152ea4 : word) mem0 rom)
              /\ getr r1 10 = Z_to_bv 64 sa /\ getr r1 11 = Z_to_bv 64 245 /\ getr r1 12 = Z_to_bv 64 n /\ getr r1 1 = ra /\ keeps_cs regs r1).
    { eexists. split.
      - stepn Fx_83e68 Dx_83e68.                                                               (* [comment removed for export] *)
      mld Fx_83e6c Dx_83e6c (0x160c38 : word) G1.                                            (* [comment removed for export] *)
      mld Fx_83e70 Dx_83e70 (0x162c50 : word) G2.                                            (* [comment removed for export] *)
      stepiv Fx_83e74 Dx_83e74 (Z_to_bv 64 n) ltac:(mvval).                                  (* [comment removed for export] *)
      stepn Fx_83e78 Dx_83e78.                                                               (* [comment removed for export] *)
      stepjr Fx_83e7c Dx_83e7c (Z_to_bv 64 0x152ea4) ltac:(gres; reflexivity).              (* [comment removed for export] *)
        vnorm. apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_cs. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & K1).
    replace (0x152ea4 : word) with (Z_to_bv 64 ms_base) in RUN1 by (apply bv_eq; vm_compute; reflexivity).
    pose proof (memset_summary mem0 (Z_to_bv 64 sa) (Z_to_bv 64 245) ra n rom Hn ltac:(rewrite u_Z2bv by lia; lia) Hdst Hret r1 Q10 Q11 Q12 Q1) as (r2 & RUN2 & _ & AG).
    replace (cbyte (Z_to_bv 64 245)) with (Z_to_bv 8 245 : byte) in RUN2 by (apply bv_eq; vm_compute; reflexivity).
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | eapply keeps_cs_trans; [exact K1 | exact (ms_agree_keeps_cs _ _ AG)]].
  Qed.

  (* [comment removed for export] *)
  Theorem setsh_f8_run : forall regs,
    getr regs 10 = Z_to_bv 64 sa -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x83ed0 : word) mem0 rom) (mkst regs' ra (wbytes mem0 (Z_to_bv 64 sa) (repeat (Z_to_bv 8 248) (Z.to_nat n))) rom)
      /\ keeps_cs regs regs'.
  Proof.
    intros regs H10 H11 H1. destruct HG as (G1 & G2).
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x83ed0 : word) mem0 rom) (mkst r1 (0x152ea4 : word) mem0 rom)
              /\ getr r1 10 = Z_to_bv 64 sa /\ getr r1 11 = Z_to_bv 64 248 /\ getr r1 12 = Z_to_bv 64 n /\ getr r1 1 = ra /\ keeps_cs regs r1).
    { eexists. split.
      - stepn Fx_83e80 Dx_83e80.                                                               (* [comment removed for export] *)
      mld Fx_83e84 Dx_83e84 (0x160c38 : word) G1.                                            (* [comment removed for export] *)
      mld Fx_83e88 Dx_83e88 (0x162c50 : word) G2.                                            (* [comment removed for export] *)
      stepiv Fx_83e8c Dx_83e8c (Z_to_bv 64 n) ltac:(mvval).                                  (* [comment removed for export] *)
      stepn Fx_83e90 Dx_83e90.                                                               (* [comment removed for export] *)
      stepjr Fx_83e94 Dx_83e94 (Z_to_bv 64 0x152ea4) ltac:(gres; reflexivity).              (* [comment removed for export] *)
        vnorm. apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_cs. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & K1).
    replace (0x152ea4 : word) with (Z_to_bv 64 ms_base) in RUN1 by (apply bv_eq; vm_compute; reflexivity).
    pose proof (memset_summary mem0 (Z_to_bv 64 sa) (Z_to_bv 64 248) ra n rom Hn ltac:(rewrite u_Z2bv by lia; lia) Hdst Hret r1 Q10 Q11 Q12 Q1) as (r2 & RUN2 & _ & AG).
    replace (cbyte (Z_to_bv 64 248)) with (Z_to_bv 8 248 : byte) in RUN2 by (apply bv_eq; vm_compute; reflexivity).
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | eapply keeps_cs_trans; [exact K1 | exact (ms_agree_keeps_cs _ _ AG)]].
  Qed.

End SETSH.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
