(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_arm_dbl_defs Od_arm_dbl_int Od_arm_dbl_exp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section ArmDbl.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Lemma dbl_head2 : forall (Q : machine_state -> Prop) st,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st ->
    dbl_E_k E Q st -> dbl_F_k E Q st -> dbl_A_k E Q st.
  Proof using OK.
    intros Q st HLAST HH HE HF. unfold dbl_A_k.
    intros neg q0 q v128 j0 j8 j16 j56 j64 j72 j80 j136 xt0 xt1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt4 xt5 xF xfc m1 NGR Hq0 Hq FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB).
    dbl_open_inv INV. od_env OK.
    pose proof (od_B_range E BOK q) as R0.
    set (c := B bs q) in *.
    zstep. zstep. zstep. zstep. zstep. lstep. lstep. zstep.
    if_cases K; zify_cond K.
    -
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      forget_C8 FR128.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_eq; [| eapply (HE neg q0 q); [exact NGR | exact Hq0 | exact Hq | exact FRM | unfold DBL_K0, DBL_K8; dbl_close_inv]] end.
      od_st_eq.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_eq; [| eapply (HF neg q0 q); [exact NGR | exact Hq0 | exact Hq | unfold c in K; lia | exact FRM | unfold DBL_K0, DBL_K8; dbl_close_inv]] end.
      od_st_eq.
  Qed.

  Theorem od_arm_dbl : dbl_frac_stmt E -> dbl_cf_stmt E -> arm_stmt E 0x277e0.
  Proof using OK.
    intros HFRAC HCF. unfold arm_stmt.
    intros Q st xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1 HLAST HH FRM INV HK.
    pose proof (HCF Q st HLAST HH HK) as HT.
    pose proof (dbl_exp E OK Q st HLAST HH HK HT) as HE.
    pose proof (HFRAC Q st HLAST HH HK HE) as HF.
    pose proof (dbl_head2 Q st HLAST HH HE HF) as HA.
    exact (od_dbl_int E OK Q st xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1 HLAST HH FRM INV HK HA).
  Qed.
End ArmDbl.
