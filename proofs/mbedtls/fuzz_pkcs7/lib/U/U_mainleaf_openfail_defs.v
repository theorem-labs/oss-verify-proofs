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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_main_entry U_stdio_call.
Import ListNotations. Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mainleaf_openfail_defs () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.kentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KRange"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "knA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SE"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sidecond"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.s_pc"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sym_state"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.scripts"; "rG3"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SCBr"; "Corelib.Init.Datatypes.false"; "LinuxProcessSemantics.Riscv.Instr.BC_GEU"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EMd"; "LinuxProcessSemantics.Riscv.Instr.M_MUL"; "PX"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.stdio_res"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.stdio_call"; "srG3"; "knG3"; "Corelib.Init.Datatypes.Some"; "scG3"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_ret"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_f"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_fd"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_wb"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_wp"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_s"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_l"; "rH3"; "srH3"; "knH3"; "scH3"; "rI3"; "rF4"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.Riscv.Instr.BC_GE"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EExt"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAluw"; "srF4"; "knF4"; "scF4"; "rG4"; "rH4"; "srH4"; "knH4"; "scH4"; "rI4"; "rA"; "rB"; "LinuxProcessSemantics.Riscv.Instr.BC_LTU"; "rC"; "rD"; "rE"; "LinuxProcessSemantics.Riscv.Instr.BC_LT"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SCReadBase"; "rF"; "rG"; "rH"; "srH"; "knH"; "scOF"; "rI"].

#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition STOPS : list Z := [0x46a40; 0x46e44; 0x46f3c; 0x46944; 0x12a64; 0x12bf0; 0x4117c; 0x3f74c; 0x41a34]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
(* [comment removed for export] *)
Definition sc_of (nv : nat) (sr : list expr) (kn : list kentry) : stdio_res :=
  match stdio_call nv sr kn with
  | Some r => r
  | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] []
  end.
(* [comment removed for export] *)
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition IHI : Z := 0x7e000.
(* [comment removed for export] *)
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x1d24c sr_main [] kn_main 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_main.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (EVar 38).
Definition knB0 : list kentry := ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_defs ()) "(0.$1.(2.(3.#2.)+7???80000000.+800000400000.)(0.$1.(2.(3.#26.)(4.(5.+2.+40.)+???.)(4.(5.+2.+40.)+1.))$6.))")
(* [comment removed for export] *).
Definition ssB0 : sym_state := SS 0x4729c srB0 [] knB0 39.
Definition scrB : scripts := SCR [false] [] [].
Definition rB := Eval vm_compute in run scrB ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knB0.
(* [comment removed for export] *)
Definition logM1 : list sentry := ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_defs ()) "(0.$7.(8.(9.(3.#0.)-220.)#1.(:.+20.))(0.$7.(8.(9.(3.#0.)-228.)#8.(:.+6>65706?20746?6>.))(0.$7.(8.(9.(3.#0.)-230.)#8.(:.+6>6163203:696<63.))(;.$7.))))")
(* [comment removed for export] *).
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0x41d64 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0x41d64 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
(* [comment removed for export] *)
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x42748 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0x41d64 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x41d64 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0x41d64 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scOF : stdio_res := Eval vm_compute in sc_of 231 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS 0x420a8 srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrG3 : scripts := SCR [false] [] [].   (* [comment removed for export] *)
Definition rG3 := Eval vm_compute in run scrG3 ssG0.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_after rG3 knG0.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 199 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.
(* [comment removed for export] *)
Definition ssH30 : sym_state := SS (sc_ret scG3) srH30 [] knH30 231.
Definition rH3 := Eval vm_compute in run scr0 ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_after rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 231 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.
(* [comment removed for export] *)
Definition ssI30 : sym_state := SS 0x420a8 srI30 [] knI30 263.
Definition rI3 := Eval vm_compute in run scr0 ssI30.
Definition srI3 : list expr := Eval vm_compute in s_regs (fst (fst rI3)).
Definition knI3 : list kentry := Eval vm_compute in kn_after rI3 knI30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrF4 : scripts := SCR [true; false] [] [].  (* [comment removed for export] *)
Definition rF4 := Eval vm_compute in run scrF4 ssF0.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_after rF4 knE.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 167 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in sc_kn scF4.
(* [comment removed for export] *)
Definition ssG40 : sym_state := SS (sc_ret scF4) srG40 [] knG40 199.
Definition rG4 := Eval vm_compute in run scr0 ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_after rG4 knG40.
(* [comment removed for export] *)
Definition logNL : list sentry := [SE (SA (EVar 0) (-560)) 1 (ELit 10)].
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 199.
(* [comment removed for export] *)
Definition ssH40 : sym_state := SS 0x41d64 srH40 [] knH40 231.
Definition rH4 := Eval vm_compute in run scr0 ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_after rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 231 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : sym_state := SS 0x420a8 srI40 [] knI40 263.
Definition rI4 := Eval vm_compute in run scr0 ssI40.
Definition srI4 : list expr := Eval vm_compute in s_regs (fst (fst rI4)).
Definition knI4 : list kentry := Eval vm_compute in kn_after rI4 knI40.

Lemma itinerary_63_64 : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_defs ()) "(<.(=.(>.$?.(10.$11.))(12.$?.(10.$11.)(13.(14.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$17.)))(18.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$17.)))(12.$?.(10.$11.)+41:34.(0.$11.(19.$1:.$1;.(1<.$1=.(1>.$1?.(:.-1.)$20.)(:.+3?.))(:.+1.))(;.$11.))))(<.(=.(21.$22.)(23.#<7.$24.$25.)(26.$22.$27.))(<.(=.(>.(>.$?.$?.)$?.)(12.(>.$?.$?.)$?.(12.$?.$?.(28.$27.)(29.$27.))(2:.$27.))(12.(>.$?.$?.)$?.(12.$?.$?.+42278.+4<=30.)+2.))(<.(=.(>.(>.(>.$2;.$2;.)$2;.)$2;.)(12.(>.(>.$2;.$2;.)$2;.)$2;.(12.(>.$2;.$2;.)$2;.(12.$2;.$2;.(2<.$27.)(2=.$27.))(2>.$27.))(2?.$27.))(12.(>.(>.$2;.$2;.)$2;.)$2;.(12.(>.$2;.$2;.)$2;.(12.$2;.$2;.(1<.$1=.(3.#0.)(:.-230.))(1<.$1=.(1<.$1=.(3.#0.)$20.)(:.-21?.)))(:.+1084<.))(:.+1.)))(<.(=.(>.$?.(10.$11.))(12.$?.(10.$11.)(13.(14.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$30.)))(18.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$30.)))(12.$?.(10.$11.)+41:34.(;.$11.)))(<.(=.(21.$22.)(23.#>7.$31.$32.)(26.$22.$33.))(<.(=.(>.(>.$?.$?.)$?.)(12.(>.$?.$?.)$?.(12.$?.$?.(28.$33.)(29.$33.))(2:.$33.))(12.(>.$?.$?.)$?.(12.$?.$?.+420:8.+4<=30.)+2.))(<.(=.(>.(>.$2;.$2;.)$2;.)(12.(>.$2;.$2;.)$2;.(12.$2;.$2;.(2<.$33.)(2=.$33.))(2?.$33.))(12.(>.$2;.$2;.)$2;.(12.$2;.$2;.(1<.$1=.(3.#0.)(:.-230.))(1<.$1=.(3.#0.)(:.-230.)))(:.=)))(<.(=.(>.$?.(10.$11.))(12.$?.(10.$11.)(13.(14.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$34.)))(18.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$34.)))(12.$?.(10.$11.)+3?74<.(;.$11.)))(<.(=.(>.$?.(10.$11.))(12.$?.(10.$11.)(13.(14.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$35.)))(18.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$35.)))(12.$?.(10.$11.)+41:34.(0.$11.(19.$1:.$1;.(:.+3?.)$20.)(0.$11.(19.$36.$37.(38.$36.#0.#4.$20.)(39.$1=.(39.$1=.$20.(:.=))(:.=)))(;.$11.)))))(<.(=.(21.$22.)(23.#:7.$3:.$3;.)(26.$22.$3<.))(<.(=.(>.(>.$?.$?.)$?.)(12.(>.$?.$?.)$?.(12.$?.$?.(28.$3<.)(29.$3<.))(2:.$3<.))(12.(>.$?.$?.)$?.(12.$?.$?.+42<98.+4<=30.)+2.))(<.(=.(>.(>.(>.$2;.$2;.)$2;.)$2;.)(12.(>.(>.$2;.$2;.)$2;.)$2;.(12.(>.$2;.$2;.)$2;.(12.$2;.$2;.(2<.$3<.)(2=.$3<.))(2>.$3<.))(2?.$3<.))(12.(>.(>.$2;.$2;.)$2;.)$2;.(12.(>.$2;.$2;.)$2;.(12.$2;.$2;.(1<.$1=.(3.#0.)(:.-230.))(1<.$1=.(3.#0.)(:.-21?.)))(3.#2.))$20.))(<.(=.(>.$?.(10.$11.))(12.$?.(10.$11.)(13.(14.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$3=.)))(18.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$3=.)))(12.$?.(10.$11.)+46:40.(;.$11.)))(<.(=.(>.$?.(10.$11.))(12.$?.(10.$11.)(13.(14.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$3>.)))(18.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$3>.)))(12.$?.(10.$11.)+41:34.(;.$11.)))(<.(=.(21.$22.)(23.#>7.$3?.$40.)(26.$22.$41.))(<.(=.(>.(>.$?.$?.)$?.)(12.(>.$?.$?.)$?.(12.$?.$?.(28.$41.)(29.$41.))(2:.$41.))(12.(>.$?.$?.)$?.(12.$?.$?.+420:8.+4<=30.)+2.))(<.(=.(>.(>.$2;.$2;.)$2;.)(12.(>.$2;.$2;.)$2;.(12.$2;.$2;.(2<.$41.)(2=.$41.))(2?.$41.))(12.(>.$2;.$2;.)$2;.(12.$2;.$2;.(1<.$1=.(3.#0.)(:.-230.))(1<.$1=.(3.#0.)(:.-22?.)))(:.=)))(=.(>.$?.(10.$11.))(12.$?.(10.$11.)(13.(14.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$42.)))(18.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$42.)))(12.$?.(10.$11.)+3?74<.(;.$11.)))))))))))))))))))))")
(* [comment removed for export] *).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma itinerary_le62 : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_defs ()) "(<.(=.(>.$?.(10.$11.))(12.$?.(10.$11.)(13.(14.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$43.)))(18.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$43.)))(12.$?.(10.$11.)+47298.(;.$11.)))(<.(=.(>.$?.(10.$11.))(12.$?.(10.$11.)(13.(14.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$44.)))(18.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$44.)))(12.$?.(10.$11.)+46:40.(0.$11.(19.$1:.$45.(39.$1=.(3.#26.)(:.=))(:.+?????????????001.))(;.$11.))))(<.(=.(>.$?.(10.$11.))(12.$?.(10.$11.)(13.(14.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$46.)))(18.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$46.)))(12.$?.(10.$11.)+46:40.(;.$11.)))(<.(=.(>.$?.(10.$11.))(12.$?.(10.$11.)(13.(14.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$47.)))(18.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$47.)))(12.$?.(10.$11.)+46?3<.(;.$11.)))(<.(=.(>.$?.(10.$11.))(12.$?.(10.$11.)(13.(14.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$48.)))(18.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$48.)))(12.$?.(10.$11.)+46:40.(0.$11.(19.$1:.$49.(39.$1=.$20.(:.=))$20.)(0.$11.(4:.(9.(1<.$1=.(3.#2.)$20.)=)#1.$1:.(:.=))(;.$11.)))))(<.(=.(>.$?.(10.$11.))(12.$?.(10.$11.)(13.(14.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$4;.)))(18.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$4;.)))(12.$?.(10.$11.)+46:40.(0.$11.(19.$36.$1;.(:.+3?.)$20.)(0.$11.(19.$36.$37.(38.$36.#0.#4.$20.)(39.$1=.(39.$1=.$20.(:.=))(:.=)))(;.$11.)))))(<.(=.(>.$?.(10.$11.))(12.$?.(10.$11.)(13.(14.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$4<.)))(18.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$4<.)))(12.$?.(10.$11.)+46:40.(0.$11.(19.$36.$1;.(1<.$1=.(1>.$1?.(:.-1.)$20.)(:.+3?.))(:.+1.))(;.$11.))))(<.(=.(>.$?.(10.$11.))(12.$?.(10.$11.)(13.(14.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$4=.)))(18.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$4=.)))(12.$?.(10.$11.)+41:34.(;.$11.)))(<.(=.(21.$22.)(23.#>7.$4>.$4?.)(26.$22.$50.))(<.(=.(>.(>.$?.$?.)$?.)(12.(>.$?.$?.)$?.(12.$?.$?.(28.$50.)(29.$50.))(2:.$50.))(12.(>.$?.$?.)$?.(12.$?.$?.+420:8.+4<=30.)+2.))(<.(=.(>.(>.$2;.$2;.)$2;.)(12.(>.$2;.$2;.)$2;.(12.$2;.$2;.(2<.$50.)(2=.$50.))(2?.$50.))(12.(>.$2;.$2;.)$2;.(12.$2;.$2;.(1<.$1=.(3.#0.)(:.-230.))(1<.$1=.(1<.$1=.(3.#0.)$20.)(:.-21>.)))(:.=)))(=.(>.$?.(10.$11.))(12.$?.(10.$11.)(13.(14.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$51.)))(18.$15.(10.$11.)(14.(>.$15.(10.$11.))$16.$51.)))(12.$?.(10.$11.)+3?74<.(;.$11.))))))))))))))")
(* [comment removed for export] *).
Proof. vm_compute. repeat split; reflexivity. Qed.
