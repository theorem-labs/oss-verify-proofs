(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit MemsetLib As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5SumsMemset_code Pm5SumsMemset.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5SetShadowTab.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition setsh_globs (M : word -> option byte) : Prop :=
  rdn ASEGS M (0x164538 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x166550)) /\
  rdn ASEGS M (0x166550 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1568bc)).

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
      msteps ASEGS (mkst regs (0x84680 : word) mem0 rom) (mkst regs' ra (wbytes mem0 (Z_to_bv 64 sa) (repeat (Z_to_bv 8 0) (Z.to_nat n))) rom)
      /\ keeps_cs regs regs'.
  Proof.
    intros regs H10 H11 H1. destruct HG as (G1 & G2).
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x84680 : word) mem0 rom) (mkst r1 (0x1568bc : word) mem0 rom)
              /\ getr r1 10 = Z_to_bv 64 sa /\ getr r1 11 = Z_to_bv 64 0 /\ getr r1 12 = Z_to_bv 64 n /\ getr r1 1 = ra /\ keeps_cs regs r1).
    { eexists. split.
      - stepiv Fx_84638 Dx_84638 (Z_to_bv 64 n) ltac:(mvval).                                  (* [comment removed for export] *)
      stepn Fx_8463c Dx_8463c.                                                               (* [comment removed for export] *)
      mld Fx_84640 Dx_84640 (0x164538 : word) G1.                                            (* [comment removed for export] *)
      mld Fx_84644 Dx_84644 (0x166550 : word) G2.                                            (* [comment removed for export] *)
      stepn Fx_84648 Dx_84648.                                                               (* [comment removed for export] *)
      stepjr Fx_8464c Dx_8464c (Z_to_bv 64 0x1568bc) ltac:(gres; reflexivity).              (* [comment removed for export] *)
        vnorm. apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_cs. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & K1).
    replace (0x1568bc : word) with (Z_to_bv 64 ms_base) in RUN1 by (apply bv_eq; vm_compute; reflexivity).
    pose proof (memset_summary mem0 (Z_to_bv 64 sa) (Z_to_bv 64 0) ra n rom Hn ltac:(rewrite u_Z2bv by lia; lia) Hdst Hret r1 Q10 Q11 Q12 Q1) as (r2 & RUN2 & _ & AG).
    replace (cbyte (Z_to_bv 64 0)) with (Z_to_bv 8 0 : byte) in RUN2 by (apply bv_eq; vm_compute; reflexivity).
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | eapply keeps_cs_trans; [exact K1 | exact (ms_agree_keeps_cs _ _ AG)]].
  Qed.

  (* [comment removed for export] *)
  Theorem setsh_f5_run : forall regs,
    getr regs 10 = Z_to_bv 64 sa -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x84788 : word) mem0 rom) (mkst regs' ra (wbytes mem0 (Z_to_bv 64 sa) (repeat (Z_to_bv 8 245) (Z.to_nat n))) rom)
      /\ keeps_cs regs regs'.
  Proof.
    intros regs H10 H11 H1. destruct HG as (G1 & G2).
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x84788 : word) mem0 rom) (mkst r1 (0x1568bc : word) mem0 rom)
              /\ getr r1 10 = Z_to_bv 64 sa /\ getr r1 11 = Z_to_bv 64 245 /\ getr r1 12 = Z_to_bv 64 n /\ getr r1 1 = ra /\ keeps_cs regs r1).
    { eexists. split.
      - stepn Fx_84740 Dx_84740.                                                               (* [comment removed for export] *)
      mld Fx_84744 Dx_84744 (0x164538 : word) G1.                                            (* [comment removed for export] *)
      mld Fx_84748 Dx_84748 (0x166550 : word) G2.                                            (* [comment removed for export] *)
      stepiv Fx_8474c Dx_8474c (Z_to_bv 64 n) ltac:(mvval).                                  (* [comment removed for export] *)
      stepn Fx_84750 Dx_84750.                                                               (* [comment removed for export] *)
      stepjr Fx_84754 Dx_84754 (Z_to_bv 64 0x1568bc) ltac:(gres; reflexivity).              (* [comment removed for export] *)
        vnorm. apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_cs. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & K1).
    replace (0x1568bc : word) with (Z_to_bv 64 ms_base) in RUN1 by (apply bv_eq; vm_compute; reflexivity).
    pose proof (memset_summary mem0 (Z_to_bv 64 sa) (Z_to_bv 64 245) ra n rom Hn ltac:(rewrite u_Z2bv by lia; lia) Hdst Hret r1 Q10 Q11 Q12 Q1) as (r2 & RUN2 & _ & AG).
    replace (cbyte (Z_to_bv 64 245)) with (Z_to_bv 8 245 : byte) in RUN2 by (apply bv_eq; vm_compute; reflexivity).
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | eapply keeps_cs_trans; [exact K1 | exact (ms_agree_keeps_cs _ _ AG)]].
  Qed.

  (* [comment removed for export] *)
  Theorem setsh_f8_run : forall regs,
    getr regs 10 = Z_to_bv 64 sa -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x847a0 : word) mem0 rom) (mkst regs' ra (wbytes mem0 (Z_to_bv 64 sa) (repeat (Z_to_bv 8 248) (Z.to_nat n))) rom)
      /\ keeps_cs regs regs'.
  Proof.
    intros regs H10 H11 H1. destruct HG as (G1 & G2).
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x847a0 : word) mem0 rom) (mkst r1 (0x1568bc : word) mem0 rom)
              /\ getr r1 10 = Z_to_bv 64 sa /\ getr r1 11 = Z_to_bv 64 248 /\ getr r1 12 = Z_to_bv 64 n /\ getr r1 1 = ra /\ keeps_cs regs r1).
    { eexists. split.
      - stepn Fx_84758 Dx_84758.                                                               (* [comment removed for export] *)
      mld Fx_8475c Dx_8475c (0x164538 : word) G1.                                            (* [comment removed for export] *)
      mld Fx_84760 Dx_84760 (0x166550 : word) G2.                                            (* [comment removed for export] *)
      stepiv Fx_84764 Dx_84764 (Z_to_bv 64 n) ltac:(mvval).                                  (* [comment removed for export] *)
      stepn Fx_84768 Dx_84768.                                                               (* [comment removed for export] *)
      stepjr Fx_8476c Dx_8476c (Z_to_bv 64 0x1568bc) ltac:(gres; reflexivity).              (* [comment removed for export] *)
        vnorm. apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_cs. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & K1).
    replace (0x1568bc : word) with (Z_to_bv 64 ms_base) in RUN1 by (apply bv_eq; vm_compute; reflexivity).
    pose proof (memset_summary mem0 (Z_to_bv 64 sa) (Z_to_bv 64 248) ra n rom Hn ltac:(rewrite u_Z2bv by lia; lia) Hdst Hret r1 Q10 Q11 Q12 Q1) as (r2 & RUN2 & _ & AG).
    replace (cbyte (Z_to_bv 64 248)) with (Z_to_bv 8 248 : byte) in RUN2 by (apply bv_eq; vm_compute; reflexivity).
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] | eapply keeps_cs_trans; [exact K1 | exact (ms_agree_keeps_cs _ _ AG)]].
  Qed.

End SETSH.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
