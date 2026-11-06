(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Specs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Plain.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb SpecConsts SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MemcpyLib.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_main_entry P_stdio_call.
Import ListNotations. Import SX2. Import SX2S.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_printf1_defs () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.BB.SymExec2.SX2.expr"; "OSSVerify.KrLib.BB.SymExec2.SX2.ELit"; "OSSVerify.KrLib.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "OSSVerify.KrLib.BB.SymExec2.SX2.EVar"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.BB.SymExec2.SX2.kentry"; "OSSVerify.KrLib.BB.SymExec2.SX2.KAlign"; "OSSVerify.KrLib.BB.SymExec2.SX2.KRange"; "OSSVerify.KrLib.BB.SymExec2.SX2.KWr"; "OSSVerify.KrLib.BB.SymExec2.SX2.SA"; "OSSVerify.KrLib.BB.SymExec2.SX2.KImg"; "OSSVerify.KrLib.BB.SymExec2.SX2.KWord"; "OSSVerify.KrLib.P.P_stdio_call.SCR_"].

#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Definition STOPS_P1 : list Z := [0x1d178; 0x3e33c]%Z.
Definition FUEL_P1 : nat := 8000.
Definition scr0 : scripts := SCR [] [] [].
Definition runP1 (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL_P1 true STOPS_P1 scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition sr_P1 : list expr := ltac2:(CDefT.buildp (gd_tbl_P_printf1_defs ()) "(0.$1.(2.=)(0.$1.(2.+1=178.)(0.$1.(3.$4.(5.#0.)(2.-=0.))(0.$1.(2.+10800.)(0.$1.(2.+599<8.)(0.$1.(5.#6.)(0.$1.(5.#7.)(0.$1.(5.#8.)(0.$1.(5.#9.)(0.$1.(5.#:.)(0.$1.(5.#;.)(0.$1.(2.=)(0.$1.(5.#=.)(0.$1.(5.#>.)(0.$1.(5.#?.)(0.$1.(5.#10.)(0.$1.(5.#11.)(0.$1.(5.#12.)(0.$1.(5.#13.)(0.$1.(5.#14.)(0.$1.(5.#15.)(0.$1.(5.#16.)(0.$1.(5.#17.)(0.$1.(5.#18.)(0.$1.(5.#19.)(0.$1.(5.#1:.)(0.$1.(5.#1;.)(0.$1.(5.#1<.)(0.$1.(5.#1=.)(0.$1.(5.#1>.)(0.$1.(5.#1?.)(0.$1.(5.#20.)(6.$1.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition kn_P1 : list kentry := ltac2:(CDefT.buildp (gd_tbl_P_printf1_defs ()) "(0.$7.(8.(5.#0.)+10.)(0.$7.(9.(5.#0.)+7???80000000.+800000000000.)(0.$7.(:.(;.(5.#0.)-800000.)+800000.)(0.$7.(:.(;.(2.=)+49000.)+32000.)(0.$7.(<.+10000.+485>0.)(0.$7.(=.(;.(2.=)+485>0.)#8.(2.+79<30.))(0.$7.(<.+485>8.+49820.)(0.$7.(=.(;.(2.=)+79<30.)#8.(5.#1.))(6.$7.)))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x1d224 sr_P1 [] kn_P1 33.
Definition rA := Eval vm_compute in runP1 scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_P1.
Definition logA : list sentry := Eval vm_compute in s_log (fst (fst rA)).
(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit (2 ^ 64 - 25)).
Definition ssB0 : sym_state := SS (s_pc (fst (fst rA)) + 4) srB0 [] knA 33.
Definition rB := Eval vm_compute in runP1 scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.
Definition logB : list sentry := Eval vm_compute in s_log (fst (fst rB)).
(* [comment removed for export] *)
Definition resC : stdio_res := ltac2:(CDefT.buildp (gd_tbl_P_printf1_defs ()) "(>.+49728.+1.+3>868.(2.+7:098.)(2.+7:099.)(2.+7:098.)(2.+400.)(2.+10422.)(2.+1.)(3.$4.(5.#0.)(2.-510.))(0.$1.(5.#21.)(0.$1.(2.+3>868.)(0.$1.(3.$4.(5.#0.)(2.-510.))(0.$1.(2.+10800.)(0.$1.(2.+599<8.)(0.$1.(5.#26.)(0.$1.(5.#27.)(0.$1.(5.#28.)(0.$1.(2.+79<30.)(0.$1.(2.+1.)(0.$1.(2.+1.)(0.$1.(5.#2<.)(0.$1.(5.#2=.)(0.$1.(5.#2>.)(0.$1.(5.#2?.)(0.$1.(5.#30.)(0.$1.(5.#31.)(0.$1.(5.#32.)(0.$1.(2.+10422.)(0.$1.(2.+1.)(0.$1.(2.=)(0.$1.(2.+10423.)(0.$1.(2.+1.)(0.$1.(2.+10422.)(0.$1.(2.+1.)(0.$1.(2.=)(0.$1.(2.+1.)(0.$1.(2.+1.)(0.$1.(5.#3=.)(0.$1.(5.#3>.)(0.$1.(5.#3?.)(0.$1.(5.#40.)(6.$1.)))))))))))))))))))))))))))))))))(0.$7.(=.(;.(2.=)+49748.)#8.(2.+7:498.))(0.$7.(=.(;.(2.=)+49750.)#8.(2.+7:098.))(0.$7.(=.(;.(2.=)+49760.)#8.(2.+7:098.))(0.$7.(=.(;.(2.=)+497;8.)#4.(2.+????????????????.))(0.$7.(=.(;.(2.=)+49770.)#8.(2.+3>33<.))(0.$7.(=.(;.(5.#0.)-508.)#8.(5.#1.))(0.$7.(=.(;.(5.#0.)-500.)#8.(2.+49728.))(0.$7.(=.(;.(5.#0.)-4?8.)#8.(2.+3>650.))(0.$7.(=.(;.(5.#0.)-4>8.)#8.(2.+10423.))(0.$7.(=.(;.(5.#0.)-4>0.)#8.(2.+49728.))(0.$7.(=.(;.(5.#0.)-4=8.)#8.(2.+1.))(0.$7.(=.(;.(5.#0.)-4=0.)#8.(2.+7??????>.))(0.$7.(=.(;.(5.#0.)-4<8.)#8.(2.+7???????.))(0.$7.(=.(;.(5.#0.)-4<0.)#8.(2.+25.))(0.$7.(=.(;.(5.#0.)-4;8.)#8.(2.+3>;80.))(0.$7.(=.(;.(2.=)+7:098.)#1.(2.+30.))(0.$7.(=.(;.(5.#0.)-400.)#1.(2.+30.))(0.$7.(=.(;.(5.#0.)-4:8.)#8.(2.=))(0.$7.(=.(;.(5.#0.)-490.)#8.(2.+1.))(0.$7.(=.(;.(5.#0.)-4:0.)#8.(2.=))(0.$7.(=.(;.(5.#0.)-4;0.)#8.(2.+102:5.))(0.$7.(=.(;.(5.#0.)-498.)#8.(2.=))(0.$7.(=.(;.(5.#0.)-440.)#8.(2.=))(0.$7.(=.(;.(5.#0.)-290.)#8.(3.$4.(5.#0.)(2.-100.)))(0.$7.(=.(;.(5.#0.)-488.)#8.(2.+????????<<<<<<<=.))(0.$7.(=.(;.(5.#0.)-480.)#8.(2.+???????????>????.))(0.$7.(=.(;.(5.#0.)-448.)#8.(2.+<<<<<<<.))(0.$7.(=.(;.(5.#0.)-460.)#8.(2.+12889.))(0.$7.(=.(;.(5.#0.)-300.)#8.(5.#1.))(0.$7.(=.(;.(5.#0.)-450.)#8.(2.+79<30.))(0.$7.(=.(;.(5.#0.)-458.)#8.(2.=))(0.$7.(=.(;.(5.#0.)-468.)#8.(3.$4.(5.#0.)(2.-290.)))(0.$7.(=.(;.(5.#0.)-478.)#8.(3.$4.(5.#0.)(2.-230.)))(0.$7.(=.(;.(5.#0.)-470.)#8.(3.$4.(5.#0.)(2.-188.)))(0.$7.(=.(;.(5.#0.)-2?8.)#8.(5.#1<.))(0.$7.(=.(;.(5.#0.)-2?0.)#8.(5.#1;.))(0.$7.(=.(;.(5.#0.)-2>8.)#8.(5.#1:.))(0.$7.(=.(;.(5.#0.)-2>0.)#8.(5.#19.))(0.$7.(=.(;.(5.#0.)-2=8.)#8.(5.#18.))(0.$7.(=.(;.(5.#0.)-2=0.)#8.(5.#17.))(0.$7.(=.(;.(5.#0.)-2<8.)#8.(2.+5.))(0.$7.(=.(;.(5.#0.)-2<0.)#8.(2.=))(0.$7.(=.(;.(5.#0.)-2;8.)#8.(2.+1.))(0.$7.(=.(;.(5.#0.)-2;0.)#8.(2.+79<30.))(0.$7.(=.(;.(5.#0.)-2:8.)#8.(2.+10420.))(0.$7.(=.(;.(5.#0.)-2:0.)#8.(2.+49728.))(0.$7.(=.(;.(5.#0.)-298.)#8.(2.+3>990.))(0.$7.(=.(;.(2.=)+49738.)#8.(2.=))(0.$7.(=.(;.(2.=)+49730.)#8.(2.=))(0.$7.(=.(;.(2.=)+497;0.)#4.(2.+????????????????.))(0.$7.(=.(;.(2.=)+49728.)#4.(2.+5.))(0.$7.(=.(;.(5.#0.)-170.)#8.(2.=))(0.$7.(=.(;.(5.#0.)-178.)#8.(2.=))(0.$7.(=.(;.(5.#0.)-180.)#8.(2.=))(0.$7.(=.(;.(5.#0.)-188.)#8.(2.=))(0.$7.(=.(;.(5.#0.)-168.)#8.(2.=))(0.$7.(=.(;.(5.#0.)-288.)#8.(3.$4.(5.#0.)(2.-108.)))(0.$7.(=.(;.(5.#0.)-160.)#8.(5.#1.))(0.$7.(=.(;.(5.#0.)-158.)#8.(5.#16.))(0.$7.(=.(;.(5.#0.)-150.)#8.(5.#15.))(0.$7.(=.(;.(5.#0.)-148.)#8.(5.#14.))(0.$7.(=.(;.(5.#0.)-140.)#8.(5.#13.))(0.$7.(=.(;.(5.#0.)-138.)#8.(5.#:.))(0.$7.(=.(;.(5.#0.)-130.)#8.(5.#9.))(0.$7.(=.(;.(5.#0.)-128.)#8.(2.+1=260.))(0.$7.(=.(;.(5.#0.)-120.)#8.(3.$4.(5.#0.)(2.-108.)))(0.$7.(=.(;.(5.#0.)-?0.)#8.(5.#?.))(0.$7.(=.(;.(5.#0.)-?8.)#8.(5.#>.))(0.$7.(=.(;.(5.#0.)-100.)#8.(5.#=.))(0.$7.(=.(;.(5.#0.)-108.)#8.(2.=))(0.$7.(=.(;.(5.#0.)-=8.)#8.(5.#12.))(0.$7.(=.(;.(5.#0.)->0.)#8.(5.#11.))(0.$7.(=.(;.(5.#0.)->8.)#8.(5.#10.))(0.$7.(=.(;.(5.#0.)-118.)#8.(2.+1=178.))(0.$7.(8.(5.#0.)+10.)(0.$7.(9.(5.#0.)+7???80000000.+800000000000.)(0.$7.(:.(;.(5.#0.)-800000.)+800000.)(0.$7.(:.(;.(2.=)+49000.)+32000.)(0.$7.(<.+10000.+485>0.)(0.$7.(=.(;.(2.=)+485>0.)#8.(2.+79<30.))(0.$7.(<.+485>8.+49728.)(0.$7.(<.+4972<.+49730.)(0.$7.(<.+49740.+49748.)(0.$7.(<.+49758.+49760.)(0.$7.(<.+49768.+49770.)(0.$7.(<.+49778.+497;0.)(0.$7.(<.+497;4.+497;8.)(0.$7.(<.+497;<.+49820.)(0.$7.(=.(;.(2.=)+79<30.)#8.(5.#1.))(6.$7.)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
(* [comment removed for export] *)
Definition ssC0 : sym_state := SS (sc_ret resC) (sc_sr resC) [] (sc_kn resC) 65.
Definition rC := Eval vm_compute in runP1 scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC (sc_kn resC).
Definition logC : list sentry := Eval vm_compute in s_log (fst (fst rC)).
