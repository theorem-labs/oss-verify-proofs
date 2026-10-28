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
Ltac2 gd_tbl_P_stdio_readerr_defs () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "spx"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.kentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KAlign"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KRange"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KImg"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWord"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SE"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.SCR_"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAluw"; "LinuxProcessSemantics.Riscv.Instr.ALU_SUB"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sidecond"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.s_pc"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sym_state"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.scripts"; "rB"; "Corelib.Init.Datatypes.snd"; "rC"; "rD"; "rE"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SCBr"; "Corelib.Init.Datatypes.false"; "LinuxProcessSemantics.Riscv.Instr.BC_LT"; "PX"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SCReadBase"; "rF"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.Riscv.Instr.BC_GEU"; "LinuxProcessSemantics.Riscv.Instr.BC_GE"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EExt"; "rG"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EMd"; "LinuxProcessSemantics.Riscv.Instr.M_MUL"; "rH"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.stdio_res"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.stdio_call"; "srH"; "knH"; "Corelib.Init.Datatypes.Some"; "scRE"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_ret"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_f"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_fd"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_wb"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_wp"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_call.sc_l"; "rI"].

#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPS : list Z := [0x46a40; 0x46e44; 0x46f3c; 0x46944; 0x12a64; 0x12bf0; 0x4117c; 0x3f74c; 0x41a34]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
Definition IHI : Z := 0x7e000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

(* [comment removed for export] *)
Definition srRE_base : list expr := ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr_defs ()) "(0.$1.(2.=)(0.$1.(2.=)(0.$1.(3.-80.)(0.$1.(2.+10800.)(0.$1.(2.+5=0<8.)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(4.#2.)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(0.$1.(2.=)(5.$1.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
Definition KEPT_RE : list nat := [2; 3; 4; 18]%nat.
Definition srRE0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RE 6.

(* [comment removed for export] *)
Definition knRE0 : list kentry := ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr_defs ()) "(0.$6.(7.(4.#0.)+10.)(0.$6.(8.(4.#0.)+7???80000000.+800000000000.)(0.$6.(9.(:.(4.#0.)-800000.)+800000.)(0.$6.(8.(4.#2.)+7???80000000.+800000400000.)(0.$6.(9.(:.(2.=)+4<000.)+32000.)(0.$6.(;.+10000.+4;<=8.)(0.$6.(<.(:.(2.=)+4;<=8.)#8.(2.+7=330.))(0.$6.(;.+4;<>0.+4<?20.)(0.$6.(<.(:.(2.=)+4<?68.)#1.(2.=))(0.$6.(<.(:.(2.=)+5=020.)#4.(4.#5.))(0.$6.(<.(:.(2.=)+7=328.)#4.(2.=))(0.$6.(<.(:.(2.=)+7=330.)#8.(4.#3.))(0.$6.(<.(:.(2.=)+7=353.)#1.(2.=))(0.$6.(<.(:.(2.=)+7=770.)#8.(2.=))(0.$6.(<.(:.(2.=)+7=780.)#8.(2.=))(0.$6.(8.(4.#5.)+1.+3?????.)(0.$6.(;.+7=108.+7=120.)(5.$6.))))))))))))))))))")
(* [comment removed for export] *).                          (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x1d478 srRE0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.
(* [comment removed for export] *)
Definition logM1 : list sentry := ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr_defs ()) "(0.$=.(>.(:.(4.#0.)-21>.)#1.(2.+20.))(0.$=.(>.(:.(4.#0.)-220.)#2.(2.+6>6?.))(0.$=.(>.(:.(4.#0.)-228.)#8.(2.+20726?7272652064.))(0.$=.(>.(:.(4.#0.)-230.)#8.(2.+616572203:696<63.))(5.$=.)))))")
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
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x41d64 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0x41d64 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scRE : stdio_res := ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr_defs ()) "(?.+4<=30.+2.+420:8.(10.$11.(4.#0.)(2.-230.))(10.$11.(10.$11.(4.#0.)(4.#71.))(2.-21<.))(10.$11.(4.#0.)(2.-230.))(2.+50.)(2.=)(2.=)(10.$11.(4.#0.)(2.-240.))(0.$1.(4.#>7.)(0.$1.(2.+420:8.)(0.$1.(10.$11.(4.#0.)(2.-240.))(0.$1.(2.+10800.)(0.$1.(2.+5=0<8.)(0.$1.(4.#><.)(0.$1.(4.#>=.)(0.$1.(4.#>>.)(0.$1.(2.+4<=30.)(0.$1.(12.$11.(2.+1.)(12.$11.(12.$11.(2.=)(12.$11.(4.#71.)(2.=)))(2.+13.)))(0.$1.(2.=)(0.$1.(4.#?2.)(0.$1.(4.#?3.)(0.$1.(4.#?4.)(0.$1.(4.#?5.)(0.$1.(4.#?6.)(0.$1.(4.#?7.)(0.$1.(4.#?8.)(0.$1.(2.+7=330.)(0.$1.(2.+1.)(0.$1.(2.+7=790.)(0.$1.(2.=)(0.$1.(4.#1<.)(0.$1.(4.#1=.)(0.$1.(4.#1>.)(0.$1.(4.#1?.)(0.$1.(4.#20.)(0.$1.(4.#21.)(0.$1.(4.#103.)(0.$1.(4.#104.)(0.$1.(4.#105.)(0.$1.(4.#106.)(5.$1.)))))))))))))))))))))))))))))))))(0.$6.(<.(:.(2.=)+4<=50.)#8.(10.$11.(4.#0.)(2.-1>0.)))(0.$6.(<.(:.(2.=)+4<=58.)#8.(10.$11.(4.#0.)(2.-230.)))(0.$6.(<.(:.(2.=)+4<=68.)#8.(10.$11.(4.#0.)(2.-230.)))(0.$6.(<.(:.(4.#0.)-498.)#8.(2.+10864.))(0.$6.(<.(:.(4.#0.)-490.)#8.(2.+4<=30.))(0.$6.(<.(:.(4.#0.)-488.)#8.(12.$11.(12.$11.(2.=)(12.$11.(4.#71.)(2.=)))(2.+13.)))(0.$6.(<.(:.(4.#0.)-480.)#8.(12.$13.(2.+7???????.)(12.$11.(12.$11.(2.=)(12.$11.(4.#71.)(2.=)))(2.+13.))))(0.$6.(<.(:.(4.#0.)-478.)#8.(2.+7???????.))(0.$6.(<.(:.(4.#0.)-470.)#8.(2.+25.))(0.$6.(<.(:.(4.#0.)-468.)#8.(2.+42278.))(0.$6.(<.(:.(4.#0.)-458.)#8.(2.=))(0.$6.(<.(:.(4.#0.)-440.)#8.(12.$11.(2.=)(12.$11.(4.#71.)(2.=))))(0.$6.(<.(:.(4.#0.)-450.)#8.(4.#71.))(0.$6.(<.(:.(4.#0.)-460.)#8.(2.+102:5.))(0.$6.(<.(:.(4.#0.)-448.)#8.(2.=))(0.$6.(8.(4.#71.)=+1????.)(0.$6.(<.(:.(4.#0.)-3?0.)#8.(4.#2.))(0.$6.(<.(:.(4.#0.)-240.)#8.(10.$11.(4.#0.)(2.-:8.)))(0.$6.(<.(:.(4.#0.)-21>.)#1.(2.+20.))(0.$6.(<.(:.(4.#0.)-220.)#2.(2.+6>6?.))(0.$6.(<.(:.(4.#0.)-228.)#8.(2.+20726?7272652064.))(0.$6.(<.(:.(4.#0.)-230.)#8.(2.+616572203:696<63.))(0.$6.(<.(:.(4.#0.)-438.)#8.(2.+????????<<<<<<<=.))(0.$6.(<.(:.(4.#0.)-430.)#8.(2.+???????????>????.))(0.$6.(<.(:.(4.#0.)-3?8.)#8.(2.+<<<<<<<.))(0.$6.(<.(:.(4.#0.)-410.)#8.(2.+12889.))(0.$6.(<.(:.(4.#0.)-400.)#8.(2.+7=330.))(0.$6.(<.(:.(4.#0.)-408.)#8.(2.=))(0.$6.(<.(:.(4.#0.)-418.)#8.(10.$11.(4.#0.)(2.-240.)))(0.$6.(<.(:.(4.#0.)-428.)#8.(10.$11.(4.#0.)(2.-1>0.)))(0.$6.(<.(:.(4.#0.)-420.)#8.(10.$11.(4.#0.)(2.-138.)))(0.$6.(<.(:.(2.=)+4<=40.)#8.(2.=))(0.$6.(<.(:.(2.=)+4<=38.)#8.(2.=))(0.$6.(<.(:.(2.=)+4<=;8.)#4.(2.+????????????????.))(0.$6.(<.(:.(2.=)+4<=90.)#8.(2.+50.))(0.$6.(<.(:.(2.=)+4<=88.)#8.(10.$11.(4.#0.)(2.-230.)))(0.$6.(<.(:.(2.=)+4<=30.)#4.(2.+5.))(0.$6.(<.(:.(4.#0.)-120.)#8.(2.=))(0.$6.(<.(:.(4.#0.)-128.)#8.(2.=))(0.$6.(<.(:.(4.#0.)-130.)#8.(2.=))(0.$6.(<.(:.(4.#0.)-138.)#8.(2.=))(0.$6.(<.(:.(4.#0.)-118.)#8.(2.=))(0.$6.(<.(:.(4.#0.)-238.)#8.(10.$11.(4.#0.)(2.-;0.)))(0.$6.(<.(:.(4.#0.)-110.)#8.(4.#3.))(0.$6.(<.(:.(4.#0.)-108.)#8.(4.#1;.))(0.$6.(<.(:.(4.#0.)-100.)#8.(4.#1:.))(0.$6.(<.(:.(4.#0.)-?8.)#8.(4.#19.))(0.$6.(<.(:.(4.#0.)-?0.)#8.(4.#2.))(0.$6.(<.(:.(4.#0.)->8.)#8.(4.#?.))(0.$6.(<.(:.(4.#0.)->0.)#8.(2.+7=330.))(0.$6.(<.(:.(4.#0.)-=8.)#8.(2.+41<40.))(0.$6.(<.(:.(4.#0.)-=0.)#8.(10.$11.(4.#0.)(2.-;0.)))(0.$6.(<.(:.(4.#0.)-<8.)#8.(4.#3.))(0.$6.(<.(:.(4.#0.)-98.)#8.(4.#15.))(0.$6.(<.(:.(4.#0.)-:0.)#8.(4.#14.))(0.$6.(<.(:.(4.#0.)-:8.)#8.(4.#13.))(0.$6.(<.(:.(4.#0.)-;0.)#8.(4.#2.))(0.$6.(<.(:.(4.#0.)-88.)#8.(4.#17.))(0.$6.(<.(:.(4.#0.)-90.)#8.(4.#16.))(0.$6.(<.(:.(4.#0.)-<0.)#8.(4.#>.))(0.$6.(<.(:.(4.#0.)-;8.)#8.(2.+1=4;0.))(0.$6.(7.(4.#0.)+10.)(0.$6.(8.(4.#0.)+7???80000000.+800000000000.)(0.$6.(9.(:.(4.#0.)-800000.)+800000.)(0.$6.(8.(4.#2.)+7???80000000.+800000400000.)(0.$6.(9.(:.(2.=)+4<000.)+32000.)(0.$6.(;.+10000.+4;<=8.)(0.$6.(<.(:.(2.=)+4;<=8.)#8.(2.+7=330.))(0.$6.(;.+4;<>0.+4<=30.)(0.$6.(;.+4<=34.+4<=38.)(0.$6.(;.+4<=48.+4<=50.)(0.$6.(;.+4<=60.+4<=68.)(0.$6.(;.+4<=70.+4<=88.)(0.$6.(;.+4<=98.+4<=;8.)(0.$6.(;.+4<=;<.+4<?20.)(0.$6.(<.(:.(2.=)+4<?68.)#1.(2.=))(0.$6.(<.(:.(2.=)+5=020.)#4.(4.#5.))(0.$6.(<.(:.(2.=)+7=328.)#4.(2.=))(0.$6.(<.(:.(2.=)+7=330.)#8.(4.#3.))(0.$6.(<.(:.(2.=)+7=353.)#1.(2.=))(0.$6.(<.(:.(2.=)+7=770.)#8.(2.=))(0.$6.(<.(:.(2.=)+7=780.)#8.(2.=))(0.$6.(8.(4.#5.)+1.+3?????.)(0.$6.(;.+7=108.+7=120.)(5.$6.))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
Definition srI0 : list expr := Eval vm_compute in sc_sr scRE.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scRE.

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS (sc_ret scRE) srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

Lemma itinerary_re : ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr_defs ()) "(14.(15.(16.$17.(18.$19.))(1:.$17.(18.$19.)(1;.(1<.$1=.(18.$19.)(1<.(16.$1=.(18.$19.))$1>.$1?.)))(20.$1=.(18.$19.)(1<.(16.$1=.(18.$19.))$1>.$1?.)))(1:.$17.(18.$19.)+46:40.(5.$19.)))(14.(15.(16.$17.(18.$19.))(1:.$17.(18.$19.)(1;.(1<.$1=.(18.$19.)(1<.(16.$1=.(18.$19.))$1>.$21.)))(20.$1=.(18.$19.)(1<.(16.$1=.(18.$19.))$1>.$21.)))(1:.$17.(18.$19.)+46:40.(5.$19.)))(14.(15.(16.$17.(18.$19.))(1:.$17.(18.$19.)(1;.(1<.$1=.(18.$19.)(1<.(16.$1=.(18.$19.))$1>.$22.)))(20.$1=.(18.$19.)(1<.(16.$1=.(18.$19.))$1>.$22.)))(1:.$17.(18.$19.)+46?3<.(5.$19.)))(14.(15.(16.$17.(18.$19.))(1:.$17.(18.$19.)(1;.(1<.$1=.(18.$19.)(1<.(16.$1=.(18.$19.))$1>.$23.)))(20.$1=.(18.$19.)(1<.(16.$1=.(18.$19.))$1>.$23.)))(1:.$17.(18.$19.)+46:40.(0.$19.(24.$25.$26.(12.$11.$27.(2.=))$27.)(0.$19.(28.(:.(10.$11.(4.#2.)$27.)=)#1.$25.(2.=))(5.$19.)))))(14.(15.(16.$17.(18.$19.))(1:.$17.(18.$19.)(1;.(1<.$1=.(18.$19.)(1<.(16.$1=.(18.$19.))$1>.$29.)))(20.$1=.(18.$19.)(1<.(16.$1=.(18.$19.))$1>.$29.)))(1:.$17.(18.$19.)+46:40.(0.$19.(24.$2:.$2;.(2.+3=.)$27.)(0.$19.(24.$2:.$2<.(2=.$2:.#0.#4.$27.)(12.$11.(12.$11.$27.(2.=))(2.=)))(5.$19.)))))(14.(15.(16.$17.(18.$19.))(1:.$17.(18.$19.)(1;.(1<.$1=.(18.$19.)(1<.(16.$1=.(18.$19.))$1>.$2>.)))(20.$1=.(18.$19.)(1<.(16.$1=.(18.$19.))$1>.$2>.)))(1:.$17.(18.$19.)+46:40.(0.$19.(24.$2:.$2;.(10.$11.(2?.$30.(2.-1.)$27.)(2.+3=.))(2.+1.))(5.$19.))))(14.(15.(16.$17.(18.$19.))(1:.$17.(18.$19.)(1;.(1<.$1=.(18.$19.)(1<.(16.$1=.(18.$19.))$1>.$31.)))(20.$1=.(18.$19.)(1<.(16.$1=.(18.$19.))$1>.$31.)))(1:.$17.(18.$19.)+41:34.(5.$19.)))(14.(15.(32.$33.)(34.#>7.$35.$36.)(37.$33.$38.))(14.(15.(16.(16.$17.$17.)$17.)(1:.(16.$17.$17.)$17.(1:.$17.$17.(39.$38.)(3:.$38.))(3;.$38.))(1:.(16.$17.$17.)$17.(1:.$17.$17.+420:8.+4<=30.)+2.))(14.(15.(16.(16.$1.$1.)$1.)(1:.(16.$1.$1.)$1.(1:.$1.$1.(3<.$38.)(3=.$38.))(3>.$38.))(1:.(16.$1.$1.)$1.(1:.$1.$1.(10.$11.(4.#0.)(2.-230.))(10.$11.(10.$11.(4.#0.)$27.)(2.-21<.)))(2.=)))(15.(16.$17.(18.$19.))(1:.$17.(18.$19.)(1;.(1<.$1=.(18.$19.)(1<.(16.$1=.(18.$19.))$1>.$3?.)))(20.$1=.(18.$19.)(1<.(16.$1=.(18.$19.))$1>.$3?.)))(1:.$17.(18.$19.)+3?74<.(5.$19.)))))))))))))")
(* [comment removed for export] *).
Proof. vm_compute. repeat split; reflexivity. Qed.

