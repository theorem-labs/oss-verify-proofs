(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Specs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Asan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb SpecConsts SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MemcpyLib.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_stdio_call.
Import ListNotations. Import SX2. Import SX2S.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_printfN_defs () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.BB.SymExec2.SX2.expr"; "OSSVerify.KrLib.BB.SymExec2.SX2.ELit"; "OSSVerify.KrLib.BB.SymExec2.SX2.EVar"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.BB.SymExec2.SX2.kentry"; "OSSVerify.KrLib.BB.SymExec2.SX2.KAlign"; "OSSVerify.KrLib.BB.SymExec2.SX2.KRange"; "OSSVerify.KrLib.BB.SymExec2.SX2.KWr"; "OSSVerify.KrLib.BB.SymExec2.SX2.SA"; "OSSVerify.KrLib.BB.SymExec2.SX2.KImg"; "OSSVerify.KrLib.BB.SymExec2.SX2.KWord"; "OSSVerify.KrLib.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_AND"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRL"; "OSSVerify.KrLib.BB.SymExec2.SX2.SCR"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.true"].

#[local] Existing Instance Lib.PropExec.fx0.

Abbreviation RSEGS := Asan.M.loaded_segments.

Definition FUEL_PF : nat := 6000.
Definition runPF (stops : list Z) (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL_PF true stops scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

Definition sr_PF : list expr := ltac2:(CDefT.buildp (gd_tbl_A_printfN_defs ()) "(0.$1.(2.=)(0.$1.(2.+96?18.)(0.$1.(3.#0.)(0.$1.(2.+10800.)(0.$1.(2.+639690.)(0.$1.(3.#6.)(0.$1.(3.#7.)(0.$1.(3.#8.)(0.$1.(3.#9.)(0.$1.(3.#:.)(0.$1.(3.#;.)(0.$1.(2.=)(0.$1.(3.#=.)(0.$1.(3.#>.)(0.$1.(3.#?.)(0.$1.(3.#10.)(0.$1.(3.#11.)(0.$1.(3.#12.)(0.$1.(3.#13.)(0.$1.(3.#14.)(0.$1.(3.#15.)(0.$1.(3.#16.)(0.$1.(3.#17.)(0.$1.(3.#18.)(0.$1.(3.#19.)(0.$1.(3.#1:.)(0.$1.(3.#1;.)(0.$1.(3.#1<.)(0.$1.(3.#1=.)(0.$1.(3.#1>.)(0.$1.(3.#1?.)(0.$1.(3.#20.)(4.$1.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition kn_PN (w : Z) : list kentry := ltac2:(CDefT.buildp (gd_tbl_A_printfN_defs ()) "(0.$5.(6.(3.#0.)+10.)(0.$5.(7.(3.#0.)+7???7?000000.+800000000000.)(0.$5.(8.(9.(3.#0.)-1000.)+1000.)(0.$5.(:.+10000.+>=000.)(0.$5.(;.(9.(2.=)+1072=8.)#1.(2.+1.))(0.$5.(;.(9.(2.=)+1072=9.)#1.(2.+1.))(0.$5.(;.(9.(2.=)+?35?8.)#8.(2.+1072=9.))(0.$5.(;.(9.(2.=)+?2:80.)#8.(2.+198128.))(0.$5.(;.(9.(2.=)+19817<.)#1.(2.+1.))(0.$5.(;.(9.(2.=)+?2:90.)#8.(2.+1065?8.))(0.$5.(;.(9.(2.=)+1065?8.)#8.(2.+7???8000.))(0.$5.(;.(9.(2.=)+?4800.)#8.(2.+>6?40.))(0.$5.(;.(9.(2.=)+?4808.)#8.(2.+>3>30.))(0.$5.(;.(9.(2.=)+?4908.)#8.(2.+>75?4.))(0.$5.(;.(9.(2.=)+?4910.)#8.(2.+>79?8.))(0.$5.(;.(9.(2.=)+7???::>0.)#8.(2.=))(0.$5.(;.(9.(2.=)+800<33;0.)#8.(2.=))(0.$5.(;.(9.(<.$=.(<.$>.(<.$?.(<.$>.(3.#0.)(2.-390.))(2.+3.))(2.+7???8000.))(2.-8.))=)#8.(2.=))(0.$5.(;.(9.(2.=)+?2:98.)#8.(2.+1072>8.))(0.$5.(;.(9.(2.=)+?2::0.)#8.(2.+1072?0.))(0.$5.(;.(9.(2.=)+?2::8.)#8.(2.+1072>0.))(0.$5.(;.(9.(2.=)+1072>8.)#8.(2.=))(0.$5.(;.(9.(2.=)+1072?0.)#8.(2.=))(0.$5.(;.(9.(2.=)+1072>0.)#8.(2.+7???????????.))(0.$5.(;.(9.(2.=)+?3720.)#8.(2.+6596=0.))(0.$5.(;.(9.(2.=)+6596=0.)#8.(3.#21.))(0.$5.(;.(9.(2.=)+?71;8.)#4.(2.+5.))(0.$5.(;.(9.(2.=)+?71=8.)#8.(2.+65:1:0.))(0.$5.(;.(9.(2.=)+?71>0.)#8.(2.O1.))(0.$5.(;.(9.(2.=)+?7218.)#8.(2.+400.))(0.$5.(;.(9.(2.=)+?7244.)#4.(2.+????????.))(0.$5.(;.(9.(2.=)+?7248.)#4.(2.+????????.))(0.$5.(8.(9.(2.=)+?6?:0.)+1000.)(0.$5.(8.(9.(2.=)+659=:0.)+408.)(4.$5.)))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).                  (* [comment removed for export] *)

Definition STOPS_PN : list Z := [0x096f18]%Z.
Definition scrN : scripts := ltac2:(CDefT.buildp (gd_tbl_A_printfN_defs ()) "(10.(0.$11.$12.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$12.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$12.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$12.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$13.(0.$11.$12.(0.$11.$12.(4.$11.)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))(4.$1.)(4.$11.))")
(* [comment removed for export] *).
Definition ssN0 (w : Z) : sym_state := SS 0x096fc4 sr_PF [] (kn_PN w) 34.
Definition rN (w : Z) := runPF STOPS_PN scrN (ssN0 w).
