(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Plain.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MemcpyLib.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_main_entry P_stdio_call.
Import ListNotations. Import SX2. Import SX2S.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_fwrite_err_defs () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.BB.SymExec2.SX2.expr"; "OSSVerify.KrLib.BB.SymExec2.SX2.ELit"; "OSSVerify.KrLib.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "OSSVerify.KrLib.BB.SymExec2.SX2.EVar"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.BB.SymExec2.SX2.kentry"; "OSSVerify.KrLib.BB.SymExec2.SX2.KAlign"; "OSSVerify.KrLib.BB.SymExec2.SX2.KRange"; "OSSVerify.KrLib.BB.SymExec2.SX2.KWr"; "OSSVerify.KrLib.BB.SymExec2.SX2.SA"; "OSSVerify.KrLib.BB.SymExec2.SX2.KImg"; "OSSVerify.KrLib.BB.SymExec2.SX2.KWord"; "OSSVerify.KrLib.P.P_stdio_call.SCR_"].

#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Definition STOPS_FW : list Z := [0x1cfc0; 0x43348; 0x4374c; 0x43844; 0x4324c; 0x3da84; 0x3c054; 0x3e33c]%Z.
Definition FUEL_FW : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition runFW (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL_FW true STOPS_FW scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition sr_FW : list expr := ltac2:(CDefT.buildp (gd_tbl_P_fwrite_err_defs ()) "(0.$1.(2.=)(0.$1.(2.+1<?<0.)(0.$1.(3.$4.(5.#0.)(2.-80.))(0.$1.(2.+10800.)(0.$1.(2.+599<8.)(0.$1.(5.#7.)(0.$1.(5.#8.)(0.$1.(5.#9.)(0.$1.(5.#:.)(0.$1.(5.#;.)(0.$1.(5.#1.)(0.$1.(2.+1?.)(0.$1.(2.+1.)(0.$1.(2.+49638.)(0.$1.(5.#10.)(0.$1.(5.#11.)(0.$1.(5.#12.)(0.$1.(5.#13.)(0.$1.(5.#14.)(0.$1.(5.#15.)(0.$1.(5.#16.)(0.$1.(5.#17.)(0.$1.(5.#18.)(0.$1.(5.#19.)(0.$1.(5.#1:.)(0.$1.(5.#1;.)(0.$1.(5.#1<.)(0.$1.(5.#1=.)(0.$1.(5.#1>.)(0.$1.(5.#1?.)(0.$1.(5.#20.)(0.$1.(5.#21.)(6.$1.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition kn_FW : list kentry := ltac2:(CDefT.buildp (gd_tbl_P_fwrite_err_defs ()) "(0.$7.(8.(5.#0.)+10.)(0.$7.(9.(5.#0.)+7???80000000.+800000000000.)(0.$7.(:.(;.(5.#0.)-800000.)+800000.)(0.$7.(9.(5.#1.)+10000.+48000.)(0.$7.(:.(;.(2.=)+49000.)+32000.)(0.$7.(<.+10000.+485>0.)(0.$7.(=.(;.(2.=)+485>0.)#8.(2.+79<30.))(0.$7.(<.+485>8.+49820.)(0.$7.(=.(;.(2.=)+79<30.)#8.(5.#2.))(6.$7.))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x3e6a0 sr_FW [] kn_FW 34.
Definition rA := Eval vm_compute in runFW scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_FW.
Definition logA : list sentry := Eval vm_compute in s_log (fst (fst rA)).
(* [comment removed for export] *)
Definition resB : stdio_res := ltac2:(CDefT.buildp (gd_tbl_P_fwrite_err_defs ()) "(>.+49638.+2.+3>728.(2.+7:090.)(2.+7:090.)(2.+7:090.)(2.=)(5.#1.)(2.+1?.)(3.$4.(5.#0.)(2.-<0.))(0.$1.(5.#22.)(0.$1.(2.+3>728.)(0.$1.(3.$4.(5.#0.)(2.-<0.))(0.$1.(2.+10800.)(0.$1.(2.+599<8.)(0.$1.(5.#27.)(0.$1.(5.#28.)(0.$1.(5.#29.)(0.$1.(2.+1.)(0.$1.(2.+1?.)(0.$1.(2.+1?.)(0.$1.(5.#2=.)(0.$1.(5.#2>.)(0.$1.(5.#2?.)(0.$1.(5.#30.)(0.$1.(5.#31.)(0.$1.(5.#32.)(0.$1.(5.#33.)(0.$1.(2.+1?.)(0.$1.(2.+49638.)(0.$1.(5.#16.)(0.$1.(5.#17.)(0.$1.(5.#18.)(0.$1.(5.#19.)(0.$1.(5.#1:.)(0.$1.(5.#1;.)(0.$1.(5.#1<.)(0.$1.(5.#1=.)(0.$1.(5.#3>.)(0.$1.(5.#3?.)(0.$1.(5.#40.)(0.$1.(5.#41.)(6.$1.)))))))))))))))))))))))))))))))))(0.$7.(=.(;.(2.=)+49658.)#8.(2.+7:090.))(0.$7.(=.(;.(2.=)+49660.)#8.(2.+7:090.))(0.$7.(=.(;.(2.=)+49670.)#8.(2.+7:090.))(0.$7.(=.(;.(2.=)+49648.)#8.(2.=))(0.$7.(=.(;.(2.=)+49640.)#8.(2.=))(0.$7.(=.(;.(2.=)+496<0.)#4.(2.+????????????????.))(0.$7.(=.(;.(5.#0.)-;8.)#8.(5.#17.))(0.$7.(=.(;.(5.#0.)-;0.)#8.(5.#16.))(0.$7.(=.(;.(5.#0.)-:8.)#8.(5.#15.))(0.$7.(=.(;.(5.#0.)-:0.)#8.(5.#14.))(0.$7.(=.(;.(5.#0.)-98.)#8.(5.#;.))(0.$7.(=.(;.(5.#0.)-90.)#8.(5.#:.))(0.$7.(=.(;.(5.#0.)-88.)#8.(2.+1<?<0.))(0.$7.(8.(5.#0.)+10.)(0.$7.(9.(5.#0.)+7???80000000.+800000000000.)(0.$7.(:.(;.(5.#0.)-800000.)+800000.)(0.$7.(9.(5.#1.)+10000.+48000.)(0.$7.(:.(;.(2.=)+49000.)+32000.)(0.$7.(<.+10000.+485>0.)(0.$7.(=.(;.(2.=)+485>0.)#8.(2.+79<30.))(0.$7.(<.+485>8.+49640.)(0.$7.(<.+49650.+49658.)(0.$7.(<.+49668.+49670.)(0.$7.(<.+49678.+496<0.)(0.$7.(<.+496<4.+49820.)(0.$7.(=.(;.(2.=)+79<30.)#8.(5.#2.))(6.$7.))))))))))))))))))))))))))))")
(* [comment removed for export] *).
(* [comment removed for export] *)
Definition ssB0 : sym_state := SS (sc_ret resB) (sc_sr resB) [] (sc_kn resB) 66.
Definition rB := Eval vm_compute in runFW scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB (sc_kn resB).
Definition logB : list sentry := Eval vm_compute in s_log (fst (fst rB)).
