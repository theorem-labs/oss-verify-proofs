(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MemcpyLib SymDriveH4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_main_entry U_stdio_call U_mainleaf_openfail_defs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_main_entryN.
Import ListNotations. Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mainleaf_usage_defs () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sidecond"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.s_pc"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sym_state"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.scripts"; "u_rA"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SCBr"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.Riscv.Instr.BC_NE"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "Corelib.Init.Datatypes.nil"; "u_rB"; "u_rC"; "u_rD"; "Corelib.Init.Datatypes.false"; "LinuxProcessSemantics.Riscv.Instr.BC_LT"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAluw"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "LX"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SCReadBase"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "u_rE"; "LinuxProcessSemantics.Riscv.Instr.BC_GEU"; "LinuxProcessSemantics.Riscv.Instr.BC_GE"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EExt"; "u_rF"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EMd"; "LinuxProcessSemantics.Riscv.Instr.M_MUL"; "u_rG"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.stdio_res"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.stdio_call"; "u_srG"; "u_knG"; "Corelib.Init.Datatypes.Some"; "u_scG"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_ret"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_f"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_fd"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_wb"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_wp"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_l"; "u_rH"; "u_rF3"; "u_srF3"; "u_knF3"; "u_scF3"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_s"; "u_rG3"; "u_srG3"; "u_knG3"; "u_scG3"; "u_rH3"; "u_rE4"; "u_srE4"; "u_knE4"; "u_scE4"; "u_rF4"; "u_rG4"; "u_srG4"; "u_knG4"; "u_scG4"; "u_rH4"].

#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition u_ssA0 : sym_state := SS 0x1d24c sr_mainN [] kn_mainN 38.
Definition u_scrA : scripts := SCR [true] [] [].       (* [comment removed for export] *)
Definition u_rA := Eval vm_compute in run u_scrA u_ssA0.
Definition u_srA : list expr := Eval vm_compute in s_regs (fst (fst u_rA)).
Definition u_knA : list kentry := Eval vm_compute in kn_after u_rA kn_mainN.
(* [comment removed for export] *)
Definition u_logM1 : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 9071406455288693)].
Definition u_knB0 : list kentry := Eval vm_compute in fst (fst (carry u_logM1 u_knA [])).
Definition u_srB0 : list expr := Eval vm_compute in sr_after_call_j u_srA KEPT_MC 38.

(* [comment removed for export] *)
Definition u_ssB0 : sym_state := SS 0x41d64 u_srB0 [] u_knB0 70.
Definition u_rB := Eval vm_compute in run scr0 u_ssB0.
Definition u_srB : list expr := Eval vm_compute in s_regs (fst (fst u_rB)).
Definition u_knB : list kentry := Eval vm_compute in kn_after u_rB u_knB0.
Definition u_srC0 : list expr := Eval vm_compute in sr_after_call_j u_srB KEPT_MC 70.

(* [comment removed for export] *)
Definition u_ssC0 : sym_state := SS 0x41d64 u_srC0 [] u_knB 102.
Definition u_rC := Eval vm_compute in run scr0 u_ssC0.
Definition u_srC : list expr := Eval vm_compute in s_regs (fst (fst u_rC)).
Definition u_knC : list kentry := Eval vm_compute in kn_after u_rC u_knB.
Definition LX : expr := EVar 112.
Definition u_knD0 : list kentry := KRange LX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI u_knC.
Definition u_srD0 : list expr := Eval vm_compute in sr_after_call_j u_srC KEPT_CS 102.

(* [comment removed for export] *)
Definition u_ssD0 : sym_state := SS 0x42748 u_srD0 [] u_knD0 134.
Definition u_scrD : scripts := SCR [false] [ELit 0] [].
Definition u_rD := Eval vm_compute in run u_scrD u_ssD0.
Definition u_srD : list expr := Eval vm_compute in s_regs (fst (fst u_rD)).
Definition u_knD : list kentry := Eval vm_compute in kn_after u_rD u_knD0.
Definition u_srE0 : list expr := Eval vm_compute in sr_after_call_j u_srD KEPT_MC 134.

(* [comment removed for export] *)
Definition u_ssE0 : sym_state := SS 0x41d64 u_srE0 [] u_knD 166.
Definition u_scrE : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition u_rE := Eval vm_compute in run u_scrE u_ssE0.
Definition u_srE : list expr := Eval vm_compute in s_regs (fst (fst u_rE)).
Definition u_knE : list kentry := Eval vm_compute in kn_after u_rE u_knD.
Definition u_knF0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knE.
Definition u_srF0 : list expr := Eval vm_compute in sr_after_call_j u_srE KEPT_MC 166.

(* [comment removed for export] *)
Definition u_ssF0 : sym_state := SS 0x41d64 u_srF0 [] u_knF0 198.
Definition u_scrF : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition u_rF := Eval vm_compute in run u_scrF u_ssF0.
Definition u_srF : list expr := Eval vm_compute in s_regs (fst (fst u_rF)).
Definition u_knF : list kentry := Eval vm_compute in kn_after u_rF u_knF0.
Definition u_knG0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knF.
Definition u_srG0 : list expr := Eval vm_compute in sr_after_call_j u_srF KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG0 : sym_state := SS 0x41d64 u_srG0 [] u_knG0 230.
Definition u_rG := Eval vm_compute in run scr0 u_ssG0.
Definition u_srG : list expr := Eval vm_compute in s_regs (fst (fst u_rG)).
Definition u_knG : list kentry := Eval vm_compute in kn_after u_rG u_knG0.
Definition u_scG : stdio_res := Eval vm_compute in sc_of 230 u_srG u_knG.
Definition u_srH0 : list expr := Eval vm_compute in sc_sr u_scG.
Definition u_knH0 : list kentry := Eval vm_compute in sc_kn u_scG.
(* [comment removed for export] *)
Definition u_ssH0 : sym_state := SS 0x420a8 u_srH0 [] u_knH0 262.
Definition u_rH := Eval vm_compute in run scr0 u_ssH0.
Definition u_srH : list expr := Eval vm_compute in s_regs (fst (fst u_rH)).
Definition u_knH : list kentry := Eval vm_compute in kn_after u_rH u_knH0.

(* [comment removed for export] *)
Definition u_scrF3 : scripts := SCR [false] [] [].   (* [comment removed for export] *)
Definition u_rF3 := Eval vm_compute in run u_scrF3 u_ssF0.
Definition u_srF3 : list expr := Eval vm_compute in s_regs (fst (fst u_rF3)).
Definition u_knF3 : list kentry := Eval vm_compute in kn_after u_rF3 u_knF0.
Definition u_scF3 : stdio_res := Eval vm_compute in sc_of 198 u_srF3 u_knF3.
Definition u_srG30 : list expr := Eval vm_compute in sc_sr u_scF3.
Definition u_knG30 : list kentry := Eval vm_compute in sc_kn u_scF3.
(* [comment removed for export] *)
Definition u_ssG30 : sym_state := SS (sc_ret u_scF3) u_srG30 [] u_knG30 230.
Definition u_rG3 := Eval vm_compute in run scr0 u_ssG30.
Definition u_srG3 : list expr := Eval vm_compute in s_regs (fst (fst u_rG3)).
Definition u_knG3 : list kentry := Eval vm_compute in kn_after u_rG3 u_knG30.
Definition u_scG3 : stdio_res := Eval vm_compute in sc_of 230 u_srG3 u_knG3.
Definition u_srH30 : list expr := Eval vm_compute in sc_sr u_scG3.
Definition u_knH30 : list kentry := Eval vm_compute in sc_kn u_scG3.
(* [comment removed for export] *)
Definition u_ssH30 : sym_state := SS 0x420a8 u_srH30 [] u_knH30 262.
Definition u_rH3 := Eval vm_compute in run scr0 u_ssH30.
Definition u_srH3 : list expr := Eval vm_compute in s_regs (fst (fst u_rH3)).
Definition u_knH3 : list kentry := Eval vm_compute in kn_after u_rH3 u_knH30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition u_scrE4 : scripts := SCR [true; false] [] [].  (* [comment removed for export] *)
Definition u_rE4 := Eval vm_compute in run u_scrE4 u_ssE0.
Definition u_srE4 : list expr := Eval vm_compute in s_regs (fst (fst u_rE4)).
Definition u_knE4 : list kentry := Eval vm_compute in kn_after u_rE4 u_knD.
Definition u_scE4 : stdio_res := Eval vm_compute in sc_of 166 u_srE4 u_knE4.
Definition u_srF40 : list expr := Eval vm_compute in sc_sr u_scE4.
Definition u_knF40 : list kentry := Eval vm_compute in sc_kn u_scE4.
(* [comment removed for export] *)
Definition u_ssF40 : sym_state := SS (sc_ret u_scE4) u_srF40 [] u_knF40 198.
Definition u_rF4 := Eval vm_compute in run scr0 u_ssF40.
Definition u_srF4 : list expr := Eval vm_compute in s_regs (fst (fst u_rF4)).
Definition u_knF4 : list kentry := Eval vm_compute in kn_after u_rF4 u_knF40.
(* [comment removed for export] *)
Definition u_logSUF : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 2907475163367712)].
Definition u_knG40 : list kentry := Eval vm_compute in fst (fst (carry u_logSUF u_knF4 [])).
Definition u_srG40 : list expr := Eval vm_compute in sr_after_call_j u_srF4 KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG40 : sym_state := SS 0x41d64 u_srG40 [] u_knG40 230.
Definition u_rG4 := Eval vm_compute in run scr0 u_ssG40.
Definition u_srG4 : list expr := Eval vm_compute in s_regs (fst (fst u_rG4)).
Definition u_knG4 : list kentry := Eval vm_compute in kn_after u_rG4 u_knG40.
Definition u_scG4 : stdio_res := Eval vm_compute in sc_of 230 u_srG4 u_knG4.
Definition u_srH40 : list expr := Eval vm_compute in sc_sr u_scG4.
Definition u_knH40 : list kentry := Eval vm_compute in sc_kn u_scG4.
(* [comment removed for export] *)
Definition u_ssH40 : sym_state := SS 0x420a8 u_srH40 [] u_knH40 262.
Definition u_rH4 := Eval vm_compute in run scr0 u_ssH40.
Definition u_srH4 : list expr := Eval vm_compute in s_regs (fst (fst u_rH4)).
Definition u_knH4 : list kentry := Eval vm_compute in kn_after u_rH4 u_knH40.

Lemma u_itinerary : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_usage_defs ()) "(0.(1.(2.$3.(4.$5.))(6.$3.(4.$5.)(7.(8.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$;.)))(<.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$;.)))(6.$3.(4.$5.)+46:40.(=.$5.(>.$?.$10.(11.#10.)(12.+2.))(13.$5.))))(0.(1.(2.$3.(4.$5.))(6.$3.(4.$5.)(7.(8.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$14.)))(<.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$14.)))(6.$3.(4.$5.)+46:40.(13.$5.)))(0.(1.(2.$3.(4.$5.))(6.$3.(4.$5.)(7.(8.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$15.)))(<.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$15.)))(6.$3.(4.$5.)+46?3<.(13.$5.)))(0.(1.(2.$3.(4.$5.))(6.$3.(4.$5.)(7.(8.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$16.)))(<.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$16.)))(6.$3.(4.$5.)+46:40.(=.$5.(>.$17.$18.(19.$1:.$1;.(12.=))$1;.)(=.$5.(1<.(1=.(1>.$1:.(11.#1.)$1;.)=)#1.$17.(12.=))(13.$5.)))))(0.(1.(2.$3.(4.$5.))(6.$3.(4.$5.)(7.(8.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$1?.)))(<.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$1?.)))(6.$3.(4.$5.)+46:40.(=.$5.(>.$?.$20.(12.+49.)$1;.)(=.$5.(>.$?.$21.(22.$?.#0.#4.$1;.)(19.$1:.(19.$1:.$1;.(12.=))(12.=)))(13.$5.)))))(0.(1.(2.$3.(4.$5.))(6.$3.(4.$5.)(7.(8.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$23.)))(<.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$23.)))(6.$3.(4.$5.)+46:40.(=.$5.(>.$?.$20.(1>.$1:.(24.$25.(12.-1.)$1;.)(12.+49.))(12.+7.))(13.$5.))))(0.(1.(2.$3.(4.$5.))(6.$3.(4.$5.)(7.(8.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$26.)))(<.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$26.)))(6.$3.(4.$5.)+41:34.(13.$5.)))(0.(1.(27.$28.)(29.#>6.$2:.$2;.)(2<.$28.$2=.))(0.(1.(2.(2.$3.$3.)$3.)(6.(2.$3.$3.)$3.(6.$3.$3.(2>.$2=.)(2?.$2=.))(30.$2=.))(6.(2.$3.$3.)$3.(6.$3.$3.+420:8.+4<=30.)+2.))(0.(1.(2.(2.$31.$31.)$31.)(6.(2.$31.$31.)$31.(6.$31.$31.(32.$2=.)(33.$2=.))(34.$2=.))(6.(2.$31.$31.)$31.(6.$31.$31.(1>.$1:.(11.#0.)(12.-230.))(1>.$1:.(1>.$1:.(11.#0.)$1;.)(12.-222.)))(12.=)))(0.(1.(2.$3.(4.$5.))(6.$3.(4.$5.)(7.(8.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$35.)))(<.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$35.)))(6.$3.(4.$5.)+3?74<.(13.$5.)))(0.(1.(2.$3.(4.$5.))(6.$3.(4.$5.)(7.(8.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$36.)))(<.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$36.)))(6.$3.(4.$5.)+41:34.(=.$5.(>.$17.$20.(1>.$1:.(24.$25.(12.-1.)$1;.)(12.+49.))(12.+7.))(13.$5.))))(0.(1.(27.$28.)(29.#<6.$37.$38.)(2<.$28.$39.))(0.(1.(2.(2.$3.$3.)$3.)(6.(2.$3.$3.)$3.(6.$3.$3.(2>.$39.)(2?.$39.))(30.$39.))(6.(2.$3.$3.)$3.(6.$3.$3.+42278.+4<=30.)+2.))(0.(1.(2.(2.(2.$31.$31.)$31.)$31.)(6.(2.(2.$31.$31.)$31.)$31.(6.(2.$31.$31.)$31.(6.$31.$31.(32.$39.)(33.$39.))(3:.$39.))(34.$39.))(6.(2.(2.$31.$31.)$31.)$31.(6.(2.$31.$31.)$31.(6.$31.$31.(1>.$1:.(11.#0.)(12.-230.))(1>.$1:.(1>.$1:.(11.#0.)$1;.)(12.-229.)))(12.+104:2.))(12.+7.)))(0.(1.(2.$3.(4.$5.))(6.$3.(4.$5.)(7.(8.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$3;.)))(<.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$3;.)))(6.$3.(4.$5.)+41:34.(13.$5.)))(0.(1.(27.$28.)(29.#>6.$3<.$3=.)(2<.$28.$3>.))(0.(1.(2.(2.$3.$3.)$3.)(6.(2.$3.$3.)$3.(6.$3.$3.(2>.$3>.)(2?.$3>.))(30.$3>.))(6.(2.$3.$3.)$3.(6.$3.$3.+420:8.+4<=30.)+2.))(0.(1.(2.(2.$31.$31.)$31.)(6.(2.$31.$31.)$31.(6.$31.$31.(32.$3>.)(33.$3>.))(34.$3>.))(6.(2.$31.$31.)$31.(6.$31.$31.(1>.$1:.(11.#0.)(12.-230.))(1>.$1:.(11.#0.)(12.-230.)))(12.=)))(0.(1.(2.$3.(4.$5.))(6.$3.(4.$5.)(7.(8.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$3?.)))(<.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$3?.)))(6.$3.(4.$5.)+3?74<.(13.$5.)))(0.(1.(2.$3.(4.$5.))(6.$3.(4.$5.)(7.(8.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$40.)))(<.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$40.)))(6.$3.(4.$5.)+41:34.(=.$5.(>.$17.$20.(12.+49.)$1;.)(=.$5.(>.$?.$21.(22.$?.#0.#4.$1;.)(19.$1:.(19.$1:.$1;.(12.=))(12.=)))(13.$5.)))))(0.(1.(27.$28.)(29.#:6.$41.$42.)(2<.$28.$43.))(0.(1.(2.(2.$3.$3.)$3.)(6.(2.$3.$3.)$3.(6.$3.$3.(2>.$43.)(2?.$43.))(30.$43.))(6.(2.$3.$3.)$3.(6.$3.$3.+42<98.+4<=30.)+2.))(0.(1.(2.(2.(2.$31.$31.)$31.)$31.)(6.(2.(2.$31.$31.)$31.)$31.(6.(2.$31.$31.)$31.(6.$31.$31.(32.$43.)(33.$43.))(3:.$43.))(34.$43.))(6.(2.(2.$31.$31.)$31.)$31.(6.(2.$31.$31.)$31.(6.$31.$31.(1>.$1:.(11.#0.)(12.-230.))(1>.$1:.(11.#0.)(12.-229.)))(11.#1.))$1;.))(0.(1.(2.$3.(4.$5.))(6.$3.(4.$5.)(7.(8.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$44.)))(<.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$44.)))(6.$3.(4.$5.)+46:40.(13.$5.)))(0.(1.(2.$3.(4.$5.))(6.$3.(4.$5.)(7.(8.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$45.)))(<.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$45.)))(6.$3.(4.$5.)+41:34.(13.$5.)))(0.(1.(27.$28.)(29.#>6.$46.$47.)(2<.$28.$48.))(0.(1.(2.(2.$3.$3.)$3.)(6.(2.$3.$3.)$3.(6.$3.$3.(2>.$48.)(2?.$48.))(30.$48.))(6.(2.$3.$3.)$3.(6.$3.$3.+420:8.+4<=30.)+2.))(0.(1.(2.(2.$31.$31.)$31.)(6.(2.$31.$31.)$31.(6.$31.$31.(32.$48.)(33.$48.))(34.$48.))(6.(2.$31.$31.)$31.(6.$31.$31.(1>.$1:.(11.#0.)(12.-230.))(1>.$1:.(11.#0.)(12.-229.)))(12.=)))(1.(2.$3.(4.$5.))(6.$3.(4.$5.)(7.(8.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$49.)))(<.$9.(4.$5.)(8.(2.$9.(4.$5.))$:.$49.)))(6.$3.(4.$5.)+3?74<.(13.$5.))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
Proof. vm_compute. repeat split; reflexivity. Qed.
