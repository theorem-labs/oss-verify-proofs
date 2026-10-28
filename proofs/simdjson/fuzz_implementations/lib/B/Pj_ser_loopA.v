(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA
     Pj_ser_headA Pj_ser_dispA Pj_ser_endsA Pj_ser_openA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Loop.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis GROW : grow_cpsA RT PMc.
Hypothesis PSTR : str_stmtA RT PMc.
Hypothesis PI64 : i64_stmtA RT PMc.
Hypothesis PU64 : u64_stmtA RT PMc.
Hypothesis PDBL : dbl_stmtA RT PMc.
Hypothesis PTRUE : true_stmtA RT PMc.
Hypothesis PFALSE : false_stmtA RT PMc.
Hypothesis PNULL : null_stmtA RT PMc.
Hypothesis PKEY : key_stmtA RT PMc.

Theorem loop_closedA : forall (E : pjenvA) (D : nat) (I : serI) (K : config -> Prop),
  pjenvA_ok E -> sctxA E D I -> exit_KA RT PMc E I K -> rec_okA RT PMc D -> forall fu, head_stmtA RT PMc E I K D fu.
Proof using AF RC FDO MST GROW PSTR PI64 PU64 PDBL PTRUE PFALSE PNULL PKEY.
  intros E D I K OK CX KX REC fu. induction fu as [|fu IH].
  - unfold head_stmtA. intros d0 ks i i2 c c2 after isobj Σ st m F fc w x xs3 xt5 xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
      HF0 HD HL KR HIT HR HAF HI HC HSM FRM ACC CR.
    exfalso. pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & _). pose proof (item_okA_lt E _ _ _ _ _ _ HIT) as LT. cbn in HF0. lia.
  - pose proof (aval_proofA RT AF RC PMc FDO MST GROW E D I K fu OK CX KX IH) as AV.
    pose proof (fun k => open_proofA RT AF RC PMc FDO MST GROW E D I K fu OK CX KX IH AV REC k) as OPEN.
    pose proof (disp_proofA RT AF PMc MST E D I K fu OK CX AV (OPEN false) (OPEN true) PSTR PI64 PU64 PDBL PTRUE PFALSE PNULL) as DISP.
    exact (head_proofA RT AF RC PMc FDO MST GROW E D I K fu OK CX DISP PKEY).
Qed.

End Loop.
