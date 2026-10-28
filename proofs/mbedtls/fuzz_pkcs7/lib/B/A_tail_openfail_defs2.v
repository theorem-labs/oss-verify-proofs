(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Specs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MemcpyLib LibKnowFrame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_stdio_call A_tail_openfail_defs.
Import ListNotations. Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_tail_openfail_defs2 () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.kentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWord"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAluw"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "LinuxProcessSemantics.Riscv.Instr.ALU_SUB"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KAlign"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KRange"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KImg"; "Corelib.Init.Datatypes.nil"].

#[local] Existing Instance PropExec.fx0.

Definition no_res : stdio_res := SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrD63 : scripts := SCR [false; false; false] [] [].   (* [comment removed for export] *)
Definition rD63 := Eval vm_compute in runOF scrD63 ssD.
Definition cD63 := Eval vm_compute in carry (s_log (fst (fst rD63))) knD [].
Definition srD63e : list expr := Eval vm_compute in s_regs (fst (fst rD63)).
Definition knD63e : list kentry := Eval vm_compute in kn_after rD63 knD.
Definition NXD63e : nat := Eval vm_compute in s_next (fst (fst rD63)).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition resD63 : stdio_res := Eval vm_compute in match stdio_call NXD63e srD63e knD63e with Some r => r | None => no_res end.
(* [comment removed for export] *)
Definition scrE63 : scripts := SCR [false] [] [].   (* [comment removed for export] *)
Definition ssE63 : sym_state := SS (sc_ret resD63) (sc_sr resD63) [] (sc_kn resD63) 237.
Definition rE63 := Eval vm_compute in runOF scrE63 ssE63.
Definition cE63 := Eval vm_compute in carry (s_log (fst (fst rE63))) (sc_kn resD63) [].
Definition srE63e : list expr := Eval vm_compute in s_regs (fst (fst rE63)).
Definition knE63e : list kentry := Eval vm_compute in kn_after rE63 (sc_kn resD63).
Definition NXE63e : nat := Eval vm_compute in s_next (fst (fst rE63)).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition resE63 : stdio_res := Eval vm_compute in match stdio_call NXE63e srE63e knE63e with Some r => r | None => no_res end.
(* [comment removed for export] *)
Definition ssF63 : sym_state := SS (sc_ret resE63) (sc_sr resE63) [] (sc_kn resE63) 269.
Definition rF63 := Eval vm_compute in runOF scrF ssF63.
Definition cF63 := Eval vm_compute in carry (s_log (fst (fst rF63))) (sc_kn resE63) [].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrC2X : scripts := SCR [true; true; false] [] [].   (* [comment removed for export] *)
Definition rC2X := Eval vm_compute in runOF scrC2X ssC2.
Definition cC2X := Eval vm_compute in carry (s_log (fst (fst rC2X))) knC1e [].
Definition srC2Xe : list expr := Eval vm_compute in s_regs (fst (fst rC2X)).
Definition knC2Xe : list kentry := Eval vm_compute in kn_after rC2X knC1e.
Definition NXC2Xe : nat := Eval vm_compute in s_next (fst (fst rC2X)).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition resC2X : stdio_res := Eval vm_compute in match stdio_call NXC2Xe srC2Xe knC2Xe with Some r => r | None => no_res end.
(* [comment removed for export] *)
Definition scrD64 : scripts := SCR [false; false] [] [].   (* [comment removed for export] *)
Definition ssD64 : sym_state := SS (sc_ret resC2X) (sc_sr resC2X) [] (sc_kn resC2X) 205.
Definition rD64 := Eval vm_compute in runOF scrD64 ssD64.
Definition cD64 := Eval vm_compute in carry (s_log (fst (fst rD64))) (sc_kn resC2X) [].
Definition srD64e : list expr := Eval vm_compute in s_regs (fst (fst rD64)).
Definition knD64e : list kentry := Eval vm_compute in kn_after rD64 (sc_kn resC2X).
Definition NXD64e : nat := Eval vm_compute in s_next (fst (fst rD64)).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition srE64 : list expr := Eval vm_compute in sr_after_call_j srD64e (map ridx KEPT_CR) 205.
Definition knE64 : list kentry := ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_defs2 ()) "(0.$1.(2.(3.(4.#0.)-438.)#8.(5.+208=;.))(0.$1.(2.(3.(4.#0.)-430.)#8.(5.+?:488.))(0.$1.(2.(3.(4.#0.)-428.)#8.(6.$7.(6.$7.(5.=)(6.$7.(4.#96.)(5.=)))(5.+11.)))(0.$1.(2.(3.(4.#0.)-420.)#8.(6.$8.(5.+7???????.)(6.$7.(6.$7.(5.=)(6.$7.(4.#96.)(5.=)))(5.+11.))))(0.$1.(2.(3.(4.#0.)-418.)#8.(5.+7???????.))(0.$1.(2.(3.(4.#0.)-410.)#8.(5.+25.))(0.$1.(2.(3.(4.#0.)-408.)#8.(5.+>74?4.))(0.$1.(2.(3.(5.=)+?:4:8.)#8.(9.$7.(4.#0.)(5.-180.)))(0.$1.(2.(3.(5.=)+?:4;0.)#8.(9.$7.(4.#0.)(5.-1=0.)))(0.$1.(2.(3.(5.=)+?:4<0.)#8.(9.$7.(4.#0.)(5.-1=0.)))(0.$1.(2.(3.(4.#0.)-3?8.)#8.(5.=))(0.$1.(2.(3.(4.#0.)-3>0.)#8.(6.$7.(5.=)(6.$7.(4.#96.)(5.=))))(0.$1.(2.(3.(4.#0.)-3?0.)#8.(4.#96.))(0.$1.(2.(3.(4.#0.)-400.)#8.(5.+10>24.))(0.$1.(2.(3.(4.#0.)-3>8.)#8.(5.=))(0.$1.(2.(3.(4.#0.)-390.)#8.(4.#13.))(0.$1.(2.(3.(4.#0.)-1>0.)#8.(9.$7.(4.#0.)(5.-28.)))(0.$1.(2.(3.(4.#0.)-1<0.)#1.(5.+20.))(0.$1.(2.(3.(4.#0.)-1<1.)#1.(5.+6>.))(0.$1.(2.(3.(4.#0.)-1<2.)#1.(5.+65.))(0.$1.(2.(3.(4.#0.)-1<3.)#1.(5.+70.))(0.$1.(2.(3.(4.#0.)-1<4.)#1.(5.+6?.))(0.$1.(2.(3.(4.#0.)-1<5.)#1.(5.+20.))(0.$1.(2.(3.(4.#0.)-1<6.)#1.(5.+74.))(0.$1.(2.(3.(4.#0.)-1<7.)#1.(5.+6?.))(0.$1.(2.(3.(4.#0.)-1<8.)#1.(5.+6>.))(0.$1.(2.(3.(4.#0.)-1<9.)#1.(5.+6>.))(0.$1.(2.(3.(4.#0.)-1<:.)#1.(5.+61.))(0.$1.(2.(3.(4.#0.)-1<;.)#1.(5.+63.))(0.$1.(2.(3.(4.#0.)-1<<.)#1.(5.+20.))(0.$1.(2.(3.(4.#0.)-1<=.)#1.(5.+3:.))(0.$1.(2.(3.(4.#0.)-1<>.)#1.(5.+69.))(0.$1.(2.(3.(4.#0.)-1<?.)#1.(5.+6<.))(0.$1.(2.(3.(4.#0.)-3=8.)#8.(5.+????????<<<<<<<=.))(0.$1.(2.(3.(4.#0.)-3=0.)#8.(5.+???????????>????.))(0.$1.(2.(3.(4.#0.)-398.)#8.(5.+<<<<<<<.))(0.$1.(2.(3.(4.#0.)-3;0.)#8.(5.+12889.))(0.$1.(2.(3.(4.#0.)-250.)#8.(4.#21.))(0.$1.(2.(3.(4.#0.)-3:0.)#8.(5.+65<:=0.))(0.$1.(2.(3.(4.#0.)-3:8.)#8.(5.=))(0.$1.(2.(3.(4.#0.)-3;8.)#8.(9.$7.(4.#0.)(5.-1>0.)))(0.$1.(2.(3.(4.#0.)-3<8.)#8.(9.$7.(4.#0.)(5.-180.)))(0.$1.(2.(3.(4.#0.)-3<0.)#8.(9.$7.(4.#0.)(5.-=8.)))(0.$1.(2.(3.(4.#0.)-248.)#8.(5.=))(0.$1.(2.(3.(4.#0.)-240.)#8.(5.=))(0.$1.(2.(3.(4.#0.)-238.)#8.(5.=))(0.$1.(2.(3.(4.#0.)-230.)#8.(5.=))(0.$1.(2.(3.(4.#0.)-228.)#8.(5.=))(0.$1.(2.(3.(4.#0.)-220.)#8.(5.=))(0.$1.(2.(3.(4.#0.)-218.)#8.(5.+5.))(0.$1.(2.(3.(4.#0.)-210.)#8.(5.+65=198.))(0.$1.(2.(3.(4.#0.)-208.)#8.(5.+1.))(0.$1.(2.(3.(4.#0.)-200.)#8.(5.+65<:=0.))(0.$1.(2.(3.(4.#0.)-1?8.)#8.(5.+208<7.))(0.$1.(2.(3.(4.#0.)-1?0.)#8.(5.+?:488.))(0.$1.(2.(3.(4.#0.)-1>8.)#8.(5.+>7304.))(0.$1.(2.(3.(5.=)+?:498.)#8.(5.=))(0.$1.(2.(3.(5.=)+?:490.)#8.(5.=))(0.$1.(2.(3.(5.=)+?:510.)#4.(5.+????????????????.))(0.$1.(2.(3.(5.=)+?:4>8.)#8.(5.+50.))(0.$1.(2.(3.(5.=)+?:4>0.)#8.(9.$7.(4.#0.)(5.-1=0.)))(0.$1.(2.(3.(5.=)+?:488.)#4.(5.+5.))(0.$1.(2.(3.(4.#0.)-<0.)#8.(5.=))(0.$1.(2.(3.(4.#0.)-<8.)#8.(5.=))(0.$1.(2.(3.(4.#0.)-=0.)#8.(5.=))(0.$1.(2.(3.(4.#0.)-=8.)#8.(5.=))(0.$1.(2.(3.(4.#0.)-;8.)#8.(5.=))(0.$1.(2.(3.(4.#0.)-1=8.)#8.(9.$7.(4.#0.)(5.-30.)))(0.$1.(2.(3.(4.#0.)-;0.)#8.(4.#21.))(0.$1.(2.(3.(4.#0.)-:8.)#8.(5.=))(0.$1.(2.(3.(4.#0.)-:0.)#8.(5.=))(0.$1.(2.(3.(4.#0.)-98.)#8.(4.#14.))(0.$1.(2.(3.(4.#0.)-90.)#8.(9.$7.(4.#0.)(5.-30.)))(0.$1.(2.(3.(4.#0.)-88.)#8.(5.+?:488.))(0.$1.(2.(3.(4.#0.)-80.)#8.(5.+208<7.))(0.$1.(2.(3.(4.#0.)-78.)#8.(5.+5;?<<.))(0.$1.(2.(3.(4.#0.)-60.)#8.(9.$7.(4.#0.)(5.-30.)))(0.$1.(2.(3.(4.#0.)-58.)#8.(9.$7.(4.#0.)(5.-30.)))(0.$1.(2.(3.(4.#0.)-68.)#8.(9.$7.(4.#0.)(5.-30.)))(0.$1.(2.(3.(4.#0.)-18.)#8.(4.#10.))(0.$1.(2.(3.(4.#0.)-20.)#8.(4.#?.))(0.$1.(2.(3.(4.#0.)-28.)#8.(4.#>.))(0.$1.(2.(3.(4.#0.)-30.)#8.(4.#13.))(0.$1.(2.(3.(4.#0.)-8.)#8.(4.#12.))(0.$1.(2.(3.(4.#0.)-10.)#8.(4.#11.))(0.$1.(2.(3.(4.#0.)-50.)#8.(4.#13.))(0.$1.(2.(3.(4.#0.)-48.)#8.(5.+2.))(0.$1.(2.(3.(4.#0.)-40.)#8.(5.+2.))(0.$1.(2.(3.(4.#0.)-38.)#8.(5.+97344.))(0.$1.(:.(4.#0.)+10.)(0.$1.(;.(4.#0.)+7???7?000000.+800000000000.)(0.$1.(;.(4.#13.)+7???7?000000.+800000000000.)(0.$1.(<.(3.(4.#0.)-1000.)+1000.)(0.$1.(=.+10000.+?1000.)(0.$1.(2.(3.(5.=)+10:6=8.)#1.(5.+1.))(0.$1.(2.(3.(5.=)+10:6=9.)#1.(5.+1.))(0.$1.(2.(3.(5.=)+?69;8.)#8.(5.+10:6=9.))(0.$1.(2.(3.(5.=)+?5>40.)#8.(5.+19;528.))(0.$1.(2.(3.(5.=)+19;57<.)#1.(5.+1.))(0.$1.(2.(3.(5.=)+?5>50.)#8.(5.+1099?8.))(0.$1.(2.(3.(5.=)+1099?8.)#8.(5.+7???8000.))(0.$1.(2.(3.(5.=)+?7;<8.)#8.(5.+>71?<.))(0.$1.(2.(3.(5.=)+?7<<8.)#8.(5.+>:9<0.))(0.$1.(2.(3.(5.=)+?7<=0.)#8.(5.+>:=<4.))(0.$1.(2.(3.(5.=)+7???<118.)#8.(5.=))(0.$1.(2.(3.(5.=)+?5>58.)#8.(5.+10:6>8.))(0.$1.(2.(3.(5.=)+?5>60.)#8.(5.+10:6?0.))(0.$1.(2.(3.(5.=)+?5>68.)#8.(5.+10:6>0.))(0.$1.(2.(3.(5.=)+10:6>8.)#8.(5.=))(0.$1.(2.(3.(5.=)+10:6?0.)#8.(5.=))(0.$1.(2.(3.(5.=)+10:6>0.)#8.(5.+7???????????.))(0.$1.(2.(3.(5.=)+?6:>0.)#8.(5.+65<:=0.))(0.$1.(2.(3.(5.=)+65<:=0.)#8.(4.#21.))(0.$1.(2.(3.(5.=)+?6:;0.)#8.(5.+?5=48.))(0.$1.(2.(3.(5.=)+?5=48.)#8.(5.+?:488.))(0.$1.(=.+?:48<.+?:490.)(0.$1.(=.+?:4:0.+?:4:8.)(0.$1.(=.+?:4;8.+?:4<0.)(0.$1.(=.+?:4<8.+?:4>0.)(0.$1.(=.+?:4?0.+?:510.)(0.$1.(=.+?:514.+?:578.)(0.$1.(<.(3.(5.=)+?:360.)+1000.)(>.$1.)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
Definition ssE64 := SS 0x0e6f40 srE64 [] knE64 237.
Definition rE64 := Eval vm_compute in runOF scrE ssE64.
Definition cE64 := Eval vm_compute in carry (s_log (fst (fst rE64))) knE64 [].
Definition srE64e : list expr := Eval vm_compute in s_regs (fst (fst rE64)).
Definition knE64e : list kentry := Eval vm_compute in kn_after rE64 knE64.
Definition NXE64e : nat := Eval vm_compute in s_next (fst (fst rE64)).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition resE64 : stdio_res := Eval vm_compute in match stdio_call NXE64e srE64e knE64e with Some r => r | None => no_res end.
(* [comment removed for export] *)
Definition ssF64 : sym_state := SS (sc_ret resE64) (sc_sr resE64) [] (sc_kn resE64) 269.
Definition rF64 := Eval vm_compute in runOF scrF ssF64.
Definition cF64 := Eval vm_compute in carry (s_log (fst (fst rF64))) (sc_kn resE64) [].

(* [comment removed for export] *)
