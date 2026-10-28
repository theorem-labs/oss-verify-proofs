(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MemcpyLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_main_entry U_stdio_call.
Import ListNotations. Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_fwrite_err_defs () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.kentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KAlign"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KRange"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KImg"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWord"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.SCR_"].

#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPS_FW : list Z := [0x1d440; 0x46a40; 0x46e44; 0x46f3c; 0x46944; 0x4117c; 0x3f74c; 0x41a34]%Z.
Definition FUEL_FW : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition runFW (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL_FW true STOPS_FW scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition sr_FW : list expr := ltac2:(CDefT.buildp (gd_tbl_P_fwrite_err_defs ()) "(0.$1.(2.=)(0.$1.(2.+1=440.)(0.$1.(3.$4.(5.#0.)(2.-80.))(0.$1.(2.+10800.)(0.$1.(2.+5=0<8.)(0.$1.(5.#7.)(0.$1.(5.#8.)(0.$1.(5.#9.)(0.$1.(5.#:.)(0.$1.(5.#;.)(0.$1.(5.#1.)(0.$1.(2.+1?.)(0.$1.(2.+1.)(0.$1.(2.+4<=30.)(0.$1.(5.#10.)(0.$1.(5.#11.)(0.$1.(5.#12.)(0.$1.(5.#13.)(0.$1.(5.#14.)(0.$1.(5.#15.)(0.$1.(5.#16.)(0.$1.(5.#17.)(0.$1.(5.#18.)(0.$1.(5.#19.)(0.$1.(5.#1:.)(0.$1.(5.#1;.)(0.$1.(5.#1<.)(0.$1.(5.#1=.)(0.$1.(5.#1>.)(0.$1.(5.#1?.)(0.$1.(5.#20.)(0.$1.(5.#21.)(6.$1.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition kn_FW : list kentry := ltac2:(CDefT.buildp (gd_tbl_P_fwrite_err_defs ()) "(0.$7.(8.(5.#0.)+10.)(0.$7.(9.(5.#0.)+7???80000000.+800000000000.)(0.$7.(:.(;.(5.#0.)-800000.)+800000.)(0.$7.(9.(5.#1.)+10000.+4;000.)(0.$7.(:.(;.(2.=)+4<000.)+32000.)(0.$7.(<.+10000.+4;<=8.)(0.$7.(=.(;.(2.=)+4;<=8.)#8.(2.+7=330.))(0.$7.(<.+4;<>0.+4<?20.)(0.$7.(=.(;.(2.=)+7=330.)#8.(5.#2.))(6.$7.))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x41d98 sr_FW [] kn_FW 34.
Definition rA := Eval vm_compute in runFW scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_FW.
Definition logA : list sentry := Eval vm_compute in s_log (fst (fst rA)).
(* [comment removed for export] *)
Definition resB : stdio_res := ltac2:(CDefT.buildp (gd_tbl_P_fwrite_err_defs ()) "(>.+4<=30.+2.+41>20.(2.+7=790.)(2.+7=790.)(2.+7=790.)(2.=)(5.#1.)(2.+1?.)(3.$4.(5.#0.)(2.-<0.))(0.$1.(5.#22.)(0.$1.(2.+41>20.)(0.$1.(3.$4.(5.#0.)(2.-<0.))(0.$1.(2.+10800.)(0.$1.(2.+5=0<8.)(0.$1.(5.#27.)(0.$1.(5.#28.)(0.$1.(5.#29.)(0.$1.(2.+1.)(0.$1.(2.+1?.)(0.$1.(2.+1?.)(0.$1.(5.#2=.)(0.$1.(5.#2>.)(0.$1.(5.#2?.)(0.$1.(5.#30.)(0.$1.(5.#31.)(0.$1.(5.#32.)(0.$1.(5.#33.)(0.$1.(2.+1?.)(0.$1.(2.+4<=30.)(0.$1.(5.#16.)(0.$1.(5.#17.)(0.$1.(5.#18.)(0.$1.(5.#19.)(0.$1.(5.#1:.)(0.$1.(5.#1;.)(0.$1.(5.#1<.)(0.$1.(5.#1=.)(0.$1.(5.#3>.)(0.$1.(5.#3?.)(0.$1.(5.#40.)(0.$1.(5.#41.)(6.$1.)))))))))))))))))))))))))))))))))(0.$7.(=.(;.(2.=)+4<=50.)#8.(2.+7=790.))(0.$7.(=.(;.(2.=)+4<=58.)#8.(2.+7=790.))(0.$7.(=.(;.(2.=)+4<=68.)#8.(2.+7=790.))(0.$7.(=.(;.(2.=)+4<=40.)#8.(2.=))(0.$7.(=.(;.(2.=)+4<=38.)#8.(2.=))(0.$7.(=.(;.(2.=)+4<=;8.)#4.(2.+????????????????.))(0.$7.(=.(;.(5.#0.)-;8.)#8.(5.#17.))(0.$7.(=.(;.(5.#0.)-;0.)#8.(5.#16.))(0.$7.(=.(;.(5.#0.)-:8.)#8.(5.#15.))(0.$7.(=.(;.(5.#0.)-:0.)#8.(5.#14.))(0.$7.(=.(;.(5.#0.)-98.)#8.(5.#;.))(0.$7.(=.(;.(5.#0.)-90.)#8.(5.#:.))(0.$7.(=.(;.(5.#0.)-88.)#8.(2.+1=440.))(0.$7.(8.(5.#0.)+10.)(0.$7.(9.(5.#0.)+7???80000000.+800000000000.)(0.$7.(:.(;.(5.#0.)-800000.)+800000.)(0.$7.(9.(5.#1.)+10000.+4;000.)(0.$7.(:.(;.(2.=)+4<000.)+32000.)(0.$7.(<.+10000.+4;<=8.)(0.$7.(=.(;.(2.=)+4;<=8.)#8.(2.+7=330.))(0.$7.(<.+4;<>0.+4<=38.)(0.$7.(<.+4<=48.+4<=50.)(0.$7.(<.+4<=60.+4<=68.)(0.$7.(<.+4<=70.+4<=;8.)(0.$7.(<.+4<=;<.+4<?20.)(0.$7.(=.(;.(2.=)+7=330.)#8.(5.#2.))(6.$7.))))))))))))))))))))))))))))")
(* [comment removed for export] *).
(* [comment removed for export] *)
Definition ssB0 : sym_state := SS (sc_ret resB) (sc_sr resB) [] (sc_kn resB) 66.
Definition rB := Eval vm_compute in runFW scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB (sc_kn resB).
Definition logB : list sentry := Eval vm_compute in s_log (fst (fst rB)).
