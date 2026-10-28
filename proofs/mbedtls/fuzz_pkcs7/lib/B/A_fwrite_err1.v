(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame RegsExt ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX StepTac MemSplit SpecConsts AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame BBFrame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev SysNodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA Restrict RestrictLib RestrictRun NodesA SymDriveA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg ARestrict A_exit_base A_stdio_defs A_stdio_write A_stdio_call A_code_58000_59000 A_code_96000_97000 A_code_e3000_e4000 A_code_e7000_e8000            A_rip.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import SymDriveAX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_printf1_defs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxAKnD.


Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_fwrite_err1 () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.kentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KAlign"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KRange"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KImg"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWord"; "SW1"; "SW2"; "RocqVerifyHarness.AgentSubmission.B.A_stdio_call.SCR_"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sidecond"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.s_pc"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sym_state"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.scripts"; "rA"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.B.A_stdio_call.stdio_res"; "RocqVerifyHarness.AgentSubmission.B.A_stdio_call.stdio_call"; "srA"; "knA"; "Corelib.Init.Datatypes.Some"; "resB"; "RocqVerifyHarness.AgentSubmission.B.A_stdio_call.sc_f"; "RocqVerifyHarness.AgentSubmission.B.A_stdio_call.sc_fd"; "stdpp.bitvector.definitions.bv"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.env"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "Corelib.Lists.ListDef.nth"; "all_regs"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.edenot"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sentry"; "RocqVerifyHarness.AgentSubmission.LibA.Restrict.restrict"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.mem_denot"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.BB.StoreOk.mem_grows"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibA.SymDriveA.DcovZ"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.Riscv.Prelude.bv_ltu"; "Stdlib.ZArith.BinInt.Z.lxor"; "LinuxProcessSemantics.Riscv.Sem.alu64"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "fw_postA"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RET"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_emit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.W"].

#[local] Existing Instance Lib.PropExec.fx0.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition MA : Z := 0x23360%Z.
Definition MLEN : Z := 31%Z.
Definition RET : Z := 0x0972d4%Z.
Definition SW1 : Z := 0x7fffc668%Z.
Definition SW2 : Z := 0x7fffc668%Z.
Definition HLO : Z := 0x23340%Z.   (* [comment removed for export] *)

Definition FUEL_FW : nat := 3000.
Definition STOPS_FW : list Z := [0x0e66b8; RET]%Z.
Definition sr_FW : list expr := ltac2:(CDefT.buildp (gd_tbl_A_fwrite_err1 ()) "(0.$1.(2.=)(0.$1.(2.+972=4.)(0.$1.(3.#0.)(0.$1.(2.+10800.)(0.$1.(2.+63<:90.)(0.$1.(3.#6.)(0.$1.(3.#7.)(0.$1.(3.#8.)(0.$1.(3.#9.)(0.$1.(3.#:.)(0.$1.(2.+23360.)(0.$1.(2.+1?.)(0.$1.(2.+1.)(0.$1.(2.+?:488.)(0.$1.(3.#?.)(0.$1.(3.#10.)(0.$1.(3.#11.)(0.$1.(3.#12.)(0.$1.(3.#13.)(0.$1.(3.#14.)(0.$1.(3.#15.)(0.$1.(3.#16.)(0.$1.(3.#17.)(0.$1.(3.#18.)(0.$1.(3.#19.)(0.$1.(3.#1:.)(0.$1.(3.#1;.)(0.$1.(3.#1<.)(0.$1.(3.#1=.)(0.$1.(3.#1>.)(0.$1.(3.#1?.)(0.$1.(3.#20.)(4.$1.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
Definition kn_FW : list kentry := ltac2:(CDefT.buildp (gd_tbl_A_fwrite_err1 ()) "(0.$5.(6.(3.#0.)+10.)(0.$5.(7.(3.#0.)+7???7?000000.+800000000000.)(0.$5.(8.(9.(3.#0.)-1000.)+1000.)(0.$5.(:.+10000.+?1000.)(0.$5.(;.(9.(2.=)+10:6=8.)#1.(2.+1.))(0.$5.(;.(9.(2.=)+?7;:8.)#8.(2.+>6?74.))(0.$5.(;.(9.(2.=)+?5>50.)#8.(2.+1099?8.))(0.$5.(;.(9.(2.=)+1099?8.)#8.(2.+7???8000.))(0.$5.(;.(9.(2.=)+?7<<8.)#8.(2.+>:9<0.))(0.$5.(;.(9.(2.=)$<.)#8.(2.=))(0.$5.(;.(9.(2.=)$=.)#8.(2.=))(0.$5.(;.(9.(2.=)+?5>58.)#8.(2.+10:6>8.))(0.$5.(;.(9.(2.=)+?5>60.)#8.(2.+10:6?0.))(0.$5.(;.(9.(2.=)+?5>68.)#8.(2.+10:6>0.))(0.$5.(;.(9.(2.=)+10:6>8.)#8.(2.=))(0.$5.(;.(9.(2.=)+10:6?0.)#8.(2.=))(0.$5.(;.(9.(2.=)+10:6>0.)#8.(2.+7???????????.))(0.$5.(;.(9.(2.=)+?6:>0.)#8.(2.+65<:=0.))(0.$5.(;.(9.(2.=)+65<:=0.)#8.(3.#21.))(0.$5.(:.+?:488.+?:578.)(0.$5.(8.(9.(2.=)+?:360.)+1000.)(4.$5.))))))))))))))))))))))")
(* [comment removed for export] *).
Definition scr0 : scripts := SCR [] [] [].
Definition rA := Eval vm_compute in sym_exec RSEGS FUEL_FW true STOPS_FW scr0 (SS 0x58714 sr_FW [] kn_FW 34) [].
Definition srA := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA := Eval vm_compute in fst (fst (carry (s_log (fst (fst rA))) kn_FW [])).
Definition resB : stdio_res := ltac2:(CDefT.buildp (gd_tbl_A_fwrite_err1 ()) "(>.+?:488.+2.+>6??<.(2.+65=198.)(2.+65=198.)(2.+65=198.)(2.=)(2.+23360.)(2.+1?.)(?.$10.(3.#0.)(2.-890.))(0.$1.(3.#22.)(0.$1.(2.+>6??<.)(0.$1.(?.$10.(3.#0.)(2.-890.))(0.$1.(2.+10800.)(0.$1.(2.+63<:90.)(0.$1.(3.#27.)(0.$1.(3.#28.)(0.$1.(3.#29.)(0.$1.(2.+1.)(0.$1.(2.+1?.)(0.$1.(2.+1?.)(0.$1.(3.#2=.)(0.$1.(3.#2>.)(0.$1.(3.#2?.)(0.$1.(3.#30.)(0.$1.(3.#31.)(0.$1.(3.#32.)(0.$1.(3.#33.)(0.$1.(2.+1?.)(0.$1.(2.+?:488.)(0.$1.(2.+1.)(0.$1.(2.+1.)(0.$1.(3.#17.)(0.$1.(3.#18.)(0.$1.(3.#19.)(0.$1.(3.#1:.)(0.$1.(3.#1;.)(0.$1.(3.#1<.)(0.$1.(3.#3>.)(0.$1.(3.#3?.)(0.$1.(3.#40.)(0.$1.(3.#41.)(4.$1.)))))))))))))))))))))))))))))))))(0.$5.(;.(9.(2.=)+?:4:8.)#8.(2.+65=198.))(0.$5.(;.(9.(2.=)+?:4;0.)#8.(2.+65=198.))(0.$5.(;.(9.(2.=)+?:4<0.)#8.(2.+65=198.))(0.$5.(;.(9.(2.=)+?:498.)#8.(2.=))(0.$5.(;.(9.(2.=)+?:490.)#8.(2.=))(0.$5.(;.(9.(2.=)+?:510.)#4.(2.+????????????????.))(0.$5.(;.(9.(3.#0.)-888.)#8.(2.+1.))(0.$5.(;.(9.(3.#0.)-880.)#8.(2.+1.))(0.$5.(;.(9.(3.#0.)-878.)#8.(2.+?:488.))(0.$5.(;.(9.(3.#0.)-870.)#8.(2.+23360.))(0.$5.(;.(9.(3.#0.)-868.)#8.(2.+1?.))(0.$5.(;.(9.(3.#0.)-860.)#8.(3.#0.))(0.$5.(;.(9.(3.#0.)-858.)#8.(2.+5:6>0.))(0.$5.(;.(9.(3.#0.)-38.)#8.(3.#16.))(0.$5.(;.(9.(3.#0.)-30.)#8.(3.#15.))(0.$5.(;.(9.(3.#0.)-28.)#8.(3.#14.))(0.$5.(;.(9.(3.#0.)-20.)#8.(3.#13.))(0.$5.(;.(9.(3.#0.)-18.)#8.(3.#:.))(0.$5.(;.(9.(3.#0.)-10.)#8.(3.#9.))(0.$5.(;.(9.(3.#0.)-8.)#8.(2.+972=4.))(0.$5.(6.(3.#0.)+10.)(0.$5.(7.(3.#0.)+7???7?000000.+800000000000.)(0.$5.(8.(9.(3.#0.)-1000.)+1000.)(0.$5.(:.+10000.+?1000.)(0.$5.(;.(9.(2.=)+10:6=8.)#1.(2.+1.))(0.$5.(;.(9.(2.=)+?7;:8.)#8.(2.+>6?74.))(0.$5.(;.(9.(2.=)+?5>50.)#8.(2.+1099?8.))(0.$5.(;.(9.(2.=)+1099?8.)#8.(2.+7???8000.))(0.$5.(;.(9.(2.=)+?7<<8.)#8.(2.+>:9<0.))(0.$5.(;.(9.(2.=)+7???<668.)#8.(2.=))(0.$5.(;.(9.(2.=)+7???<668.)#8.(2.=))(0.$5.(;.(9.(2.=)+?5>58.)#8.(2.+10:6>8.))(0.$5.(;.(9.(2.=)+?5>60.)#8.(2.+10:6?0.))(0.$5.(;.(9.(2.=)+?5>68.)#8.(2.+10:6>0.))(0.$5.(;.(9.(2.=)+10:6>8.)#8.(2.=))(0.$5.(;.(9.(2.=)+10:6?0.)#8.(2.=))(0.$5.(;.(9.(2.=)+10:6>0.)#8.(2.+7???????????.))(0.$5.(;.(9.(2.=)+?6:>0.)#8.(2.+65<:=0.))(0.$5.(;.(9.(2.=)+65<:=0.)#8.(3.#21.))(0.$5.(:.+?:488.+?:490.)(0.$5.(:.+?:4:0.+?:4:8.)(0.$5.(:.+?:4;8.+?:4<0.)(0.$5.(:.+?:4<8.+?:510.)(0.$5.(:.+?:514.+?:578.)(0.$5.(8.(9.(2.=)+?:360.)+1000.)(4.$5.)))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
Lemma itinerary_fw : ltac2:(CDefT.buildp (gd_tbl_A_fwrite_err1 ()) "(11.(12.(13.$14.(15.$16.))(17.$14.(15.$16.)(18.(19.$1:.(15.$16.)(19.(13.$1:.(15.$16.))$1;.$1<.)))(1=.$1:.(15.$16.)(19.(13.$1:.(15.$16.))$1;.$1<.)))(17.$14.(15.$16.)+>66;8.(4.$16.)))(11.(12.(1>.$1?.)(20.#22.$21.$22.)(23.$1?.$24.))(12.(13.$14.$14.)(17.$14.$14.(25.$24.)(26.$24.))(17.$14.$14.+?:488.+2.))))")
(* [comment removed for export] *).
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Definition all_regs : list reg := ltac2:(CDefT.buildp (gd_tbl_A_fwrite_err1 ()) "(0.(27.&5.)(28.&5.=$29.)(0.(27.&5.)(28.&5.+1.$29.)(0.(27.&5.)(28.&5.+2.$29.)(0.(27.&5.)(28.&5.+3.$29.)(0.(27.&5.)(28.&5.+4.$29.)(0.(27.&5.)(28.&5.+5.$29.)(0.(27.&5.)(28.&5.+6.$29.)(0.(27.&5.)(28.&5.+7.$29.)(0.(27.&5.)(28.&5.+8.$29.)(0.(27.&5.)(28.&5.+9.$29.)(0.(27.&5.)(28.&5.+:.$29.)(0.(27.&5.)(28.&5.+;.$29.)(0.(27.&5.)(28.&5.+<.$29.)(0.(27.&5.)(28.&5.+=.$29.)(0.(27.&5.)(28.&5.+>.$29.)(0.(27.&5.)(28.&5.+?.$29.)(0.(27.&5.)(28.&5.+10.$29.)(0.(27.&5.)(28.&5.+11.$29.)(0.(27.&5.)(28.&5.+12.$29.)(0.(27.&5.)(28.&5.+13.$29.)(0.(27.&5.)(28.&5.+14.$29.)(0.(27.&5.)(28.&5.+15.$29.)(0.(27.&5.)(28.&5.+16.$29.)(0.(27.&5.)(28.&5.+17.$29.)(0.(27.&5.)(28.&5.+18.$29.)(0.(27.&5.)(28.&5.+19.$29.)(0.(27.&5.)(28.&5.+1:.$29.)(0.(27.&5.)(28.&5.+1;.$29.)(0.(27.&5.)(28.&5.+1<.$29.)(0.(27.&5.)(28.&5.+1=.$29.)(0.(27.&5.)(28.&5.+1>.$29.)(0.(27.&5.)(28.&5.+1?.$29.)(4.(27.&5.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.
Lemma regs_ok_by_index : ltac2:(CDefT.buildp (gd_tbl_A_fwrite_err1 ()) "PE,$2:.Psr,(15.$1.)PR,(2;.&5.(27.&40.))P,Pi,$2<.P,(2=.R1.#20.)(12.(27.&40.)(2>.R3.(2?.(27.&5.)R2.$30.(28.&5.=$29.)))(31.R5.(2?.$1.R2.R4.(2.=))))(32.R4.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot]. reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_all_regs in Hx by apply ridx_range.
    rewrite ridx_roundtrip in Hx. exact Hx.
Qed.

(* [comment removed for export] *)
Record fw_memA (sp0 : word) (M : word -> option byte) (can : word) : Prop := FW_MEM {
  fw_win : forall a : word, (bv_unsigned sp0 - 4096 <= bv_unsigned a < bv_unsigned sp0)%Z -> wview RSEGS M a <> None;
  fw_ro  : forall a : Z, (0x10000 <= a < 0x0f1000)%Z -> M (Z_to_bv 64 a) = None;
  fw_err : forall a : Z, (0x0fa488 <= a < 0x0fa578)%Z -> M (Z_to_bv 64 a) = None;   (* [comment removed for export] *)
  fw_inited : rdn RSEGS M (Z_to_bv 64 0x10a6d8) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 1));
  fw_rfw    : rdn RSEGS M (Z_to_bv 64 0x0f7ba8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x0e6f74));
  fw_got    : rdn RSEGS M (Z_to_bv 64 0x0f5e50) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1099f8));
  fw_sb     : rdn RSEGS M (Z_to_bv 64 0x1099f8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000));
  fw_rmc    : rdn RSEGS M (Z_to_bv 64 0x0f7cc8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x0ea9c0));
  fw_sh1    : rdn RSEGS M (Z_to_bv 64 SW1) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  fw_sh2    : rdn RSEGS M (Z_to_bv 64 SW2) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  fw_g88    : rdn RSEGS M (Z_to_bv 64 0x0f5e58) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10a6e8));
  fw_g90    : rdn RSEGS M (Z_to_bv 64 0x0f5e60) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10a6f0));
  fw_g98    : rdn RSEGS M (Z_to_bv 64 0x0f5e68) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10a6e0));
  fw_kmb    : rdn RSEGS M (Z_to_bv 64 0x10a6e8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  fw_kme    : rdn RSEGS M (Z_to_bv 64 0x10a6f0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  fw_khe    : rdn RSEGS M (Z_to_bv 64 0x10a6e0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff));
  fw_cgot   : rdn RSEGS M (Z_to_bv 64 0x0f6ae0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x65cad0));
  fw_can    : rdn RSEGS M (Z_to_bv 64 0x65cad0) 8 = Some (word_to_le_bytes 8 can)
}.

Record fw_postA (sp0 : word) (M M' : word -> option byte) : Prop := FW_POSTA {
  fwp_agree : forall x : word,
      ~ (bv_unsigned sp0 - 4096 <= bv_unsigned x < bv_unsigned sp0)%Z ->
      ~ (0x0fa488 <= bv_unsigned x < 0x0fa570)%Z -> M' x = M x;
  fwp_munch : munch [((bv_unsigned sp0 - 4096)%Z, (bv_unsigned sp0)%Z); (0x0fa488%Z, 0x0fa570%Z)] M M';
  fwp_grows : mem_grows M M';
  fwp_wmono : wmono RSEGS M M';
  fwp_clean : file_clean M' 0x0fa488 (Z_to_bv 64 0x65d198) (Z_to_bv 64 0)
}.

(* [comment removed for export] *)
Fixpoint log_out (E : env) (x : word) (log : list sentry) : Prop :=
  match log with
  | [] => True
  | SE a w _ :: rest =>
      (bv_unsigned (adenot E a) + Z.of_nat w <= 2 ^ 64)%Z
      /\ (bv_unsigned x < bv_unsigned (adenot E a) \/ bv_unsigned (adenot E a) + Z.of_nat w <= bv_unsigned x)%Z
      /\ log_out E x rest
  end.
Lemma mem_denot_out : forall E M log (x : word), log_out E x log -> mem_denot E M log x = M x.
Proof.
  intros E M log x. induction log as [|[a w v] rest IH]; intros H; [reflexivity|].
  cbn [log_out] in H. destruct H as (H1 & H2 & H3).
  cbn [mem_denot]. rewrite MemSplit.wbytes_outside.
  - apply IH. exact H3.
  - rewrite length_N_to_le_bytes. exact H1.
  - rewrite length_N_to_le_bytes. exact H2.
Qed.

Lemma mem_grows_wmono : forall M M', mem_grows M M' -> wmono RSEGS M M'.
Proof.
  intros M M' G x Hx. unfold wview in *. destruct (M x) as [b|] eqn:EE.
  - specialize (G x ltac:(congruence)). destruct (M' x); [discriminate|contradiction].
  - destruct (M' x); [discriminate|exact Hx].
Qed.

(* [comment removed for export] *)
Lemma grows_of_rst : ltac2:(CDefT.buildp (gd_tbl_A_fwrite_err1 ()) "PD,P,(27.&40.)$33.PE,$2:.PM,P,(27.&40.)(1>.(27.&8.))PM',P,(27.&40.)(1>.(27.&8.))Plog,(15.$34.)P,(12.P,(27.&40.)(1>.(27.&8.))(35.R5.R2.)(36.R4.(35.R5.R3.)R1.))P,Pa,(27.&40.)P,(12.$33.A1.R7.R1.$37.)(12.(1>.(27.&8.))A1.R5.R2.A1.R6.R2.)(38.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros D E M M' log EQ OUT x Hx. destruct (D x) eqn:Dx.
  - pose proof (mem_denot_grows E (restrict D M) log x) as G. rewrite <- EQ in G.
    rewrite !(restrict_in D _ _ Dx) in G. apply G. exact Hx.
  - rewrite (OUT x Dx). exact Hx.
Qed.

Section FW.
  (* [comment removed for export] *)
  Variable AL : asan_layout.
  Variable CS : Z -> Prop.
  Variable KI : Model -> Prop.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000%Z.
  Hypothesis K_halted : forall mo, KI mo -> m_halted mo = None.
  Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_fwrite_err1 ()) "Pmo,$39.Pacc,(15.(13.(27.&40.)$2<.))P,A1.VKI,R2.P,(3:.VAL,VCS,R2.)(3;.$39.Lmo',$39.(11.(12.(1>.$39.)(3<.R5.R4.)(23.$39.R1.))(11.A1.VKI,R1.(3=.R5.R1.))))")
(* [comment removed for export] *).
  Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_A_fwrite_err1 ()) "Pmo,$39.Pmo',$39.P,A1.VKI,R2.P,(12.$3>.(3?.R2.)(3?.R3.))P,(12.(15.(13.(27.&40.)(27.&40.)))(40.R3.)(40.R4.))P,(12.(15.(27.&40.))(41.R4.)(41.R5.))P,(12.(1>.(27.&40.))(42.R5.)(42.R6.))A1.VKI,R6.")
(* [comment removed for export] *).

  Variable sp0 : word.
  Variable model : Model.
  Hypothesis SPlo : (0x7fff7f000000 + 4096 <= bv_unsigned sp0)%Z.
  Hypothesis SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis SPal : (bv_unsigned sp0 mod 16 = 0)%Z.
  Hypothesis HKI : KI model.
  (* [comment removed for export] *)
  Hypothesis WCS : crange CS (bv_unsigned sp0 - 4096) 4096.
  Hypothesis MCS : crange CS HLO (MLEN + 128).   (* [comment removed for export] *)

  Variables (R : bvmap 5 word) (M : word -> option byte) (can : word).
  Hypothesis G1 : getr R 1 = Z_to_bv 64 RET.
  Hypothesis G2 : getr R 2 = sp0.
  Hypothesis G3 : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis G4 : getr R 4 = Z_to_bv 64 0x63ca90.
  Hypothesis G10 : getr R 10 = Z_to_bv 64 MA.
  Hypothesis G11 : getr R 11 = Z_to_bv 64 MLEN.
  Hypothesis G12 : getr R 12 = Z_to_bv 64 1.
  Hypothesis G13 : getr R 13 = Z_to_bv 64 0x0fa488.
  Hypothesis FM : fw_memA sp0 M can.
  Variable msg : list byte.
  Hypothesis Hlen : length msg = Z.to_nat MLEN.
  Hypothesis Hmsg : rdn RSEGS M (Z_to_bv 64 MA) (Z.to_nat MLEN) = Some msg.
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  (* [comment removed for export] *)
  Let D : word -> bool := Dimg [(bv_unsigned sp0 - 4096, bv_unsigned sp0)%Z; (SW1, SW1 + 8)%Z; (SW2, SW2 + 8)%Z].

  Lemma D_Dseg : forall a : word, segcov RSEGS (bv_unsigned a) = true -> D a = true.
  Proof. intros a H. unfold D. apply Dimg_Dseg. exact H. Qed.
  Lemma shadow_aok : forall c x, CS c -> (x = 0x7fff8000 + c / 8)%Z -> aok_addr AL CS x.
  Proof. intros c x Hc ->. right; left. exists c. split; [exact Hc|]. unfold shadow_of. rewrite ASB. lia. Qed.
  Lemma D_DOK : forall a, D a = true -> aok_addr AL CS (bv_unsigned a).
  Proof.
    intros a H. unfold D in H. eapply (Dimg_DOK_aok AL CS IMG); [|exact H].
    repeat (apply Forall_cons; [cbn [fst snd]|]); [ .. | apply Forall_nil].
    - intros z Hz. left. apply WCS. lia.
    - intros z Hz. apply (shadow_aok (8 * (z - 0x7fff8000))); [apply MCS; unfold HLO, MLEN, SW1, SW2 in *; lia|]. rewrite Z.mul_comm, Z.div_mul by lia. lia.
    - intros z Hz. apply (shadow_aok (8 * (z - 0x7fff8000))); [apply MCS; unfold HLO, MLEN, SW1, SW2 in *; lia|]. rewrite Z.mul_comm, Z.div_mul by lia. lia.
  Qed.
  Lemma D_D0 : D (Z_to_bv 64 0) = false.
  Proof. pose proof SPlo. unfold D. apply Dimg_D0. unfold SW1, SW2. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.

  Definition RRUN := rz_runA RSEGS D AL CS KI K_halted K_mat D_Dseg asegs_top D_DOK D_D0.

  (* [comment removed for export] *)
  Lemma D_frame : forall lo hi, (bv_unsigned sp0 - 4096 <= lo)%Z -> (hi <= bv_unsigned sp0)%Z -> DcovZ D lo hi.
  Proof. intros lo hi Hlo Hhi z Hz. unfold D. apply (Dimg_cov _ (bv_unsigned sp0 - 4096) (bv_unsigned sp0)); [left; reflexivity | lia | lia | lia]. Qed.
  Lemma D_img : forall lo hi, (0x10000 <= lo)%Z -> (hi <= 0x65f000)%Z -> DcovZ D lo hi.
  Proof. intros lo hi Hlo Hhi z Hz. unfold D. apply Dimg_img. unfold AIMG_LO, AIMG_HI. lia. Qed.
  Lemma D_sw1 : DcovZ D SW1 (SW1 + 8).
  Proof. intros z Hz. unfold D. eapply Dimg_cov; [right; left; reflexivity | unfold SW1; lia | unfold SW1; lia | lia]. Qed.
  Lemma D_sw2 : DcovZ D SW2 (SW2 + 8).
  Proof. intros z Hz. unfold D. eapply Dimg_cov; [right; right; left; reflexivity | unfold SW2; lia | unfold SW2; lia | lia]. Qed.

  Definition valsP1 : list word := [sp0] ++ junk_vals R ++ [can].
  Let E : env := Env (vals_ev valsP1) (blobs_ev []).

  Lemma valsP1_len : length valsP1 = 34%nat.
  Proof. unfold valsP1. rewrite !length_app, junk_vals_length. reflexivity. Qed.
  Lemma vP0 : vals_ev valsP1 0 = sp0. Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  Definition LITS_KND : list (Z * Z) := [(0x10000, 0x65f000)%Z].
  Lemma KND : forall kn, Forall (kentry_inD D E) (knd_residual (-4096) LITS_KND kn) -> kn_inD D E kn.
  Proof.
    apply (kn_inD_residual D E sp0 (-4096) LITS_KND).
    - exact vP0.
    - intros lo hi Hlo Hhi. apply D_frame; lia.
    - repeat (apply Forall_cons; [cbn [fst snd] |]); [apply D_img; lia | apply Forall_nil].
  Qed.
  Lemma D_frameS : ltac2:(CDefT.buildp (gd_tbl_A_fwrite_err1 ()) "Pqlo,$14.Pqhi,$14.P,(43.(44.(45.&40.Vsp0,)-1000.)R2.)P,(43.R2.(45.&40.Vsp0,))(46.VD,R4.R3.)")
(* [comment removed for export] *).
  Proof. intros qlo qhi Hlo Hhi. apply D_frame; lia. Qed.
  Lemma HLITS_KND : Forall (fun iv => DcovZ D (fst iv) (snd iv)) LITS_KND.
  Proof. unfold LITS_KND. repeat (apply Forall_cons; [cbn [fst snd] |]); [ .. | apply Forall_nil]; first [ apply D_img; lia | fail ]. Qed.
  Lemma vP33 : vals_ev valsP1 33 = can.
  Proof. unfold valsP1, vals_ev. change ([sp0] ++ junk_vals R ++ [can]) with (([sp0] ++ junk_vals R) ++ [can]).
    rewrite app_nth2; [|rewrite length_app, junk_vals_length; cbn; lia].
    rewrite length_app, junk_vals_length. reflexivity. Qed.
  Ltac evs := unfold E; cbn [ev eb]; rewrite ?vals_ev_app_l by (rewrite valsP1_len; lia); rewrite ?vP0, ?vP33.

  Lemma evP1_junk : forall i, (i < 32)%nat -> ev E (1 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E. cbn [ev]. unfold valsP1.
    change (1 + i)%nat with (length [sp0] + i)%nat.
    unfold vals_ev. cbn [app length Nat.add]. change (S i) with (length [sp0] + i)%nat. change (sp0 :: junk_vals R ++ [can]) with ([sp0] ++ (junk_vals R ++ [can])). rewrite app_nth2_plus. rewrite app_nth1 by (rewrite junk_vals_length; exact Hi).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma regs_okP1 : regs_ok E sr_FW R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_FW all_regs]; unfold MA, MLEN, RET;
      first [ (cbn [edenot]; first [ reflexivity | exact G1 | exact G3 | exact G4 | exact G10 | exact G11 | exact G12 | exact G13 | (evs; exact G2) ])
            | (lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                 change (edenot E (EVar n)) with (ev E n); rewrite (evP1_junk (n - 1)) by lia; reflexivity end) ].
  Qed.

  Lemma adenot_of_estart : forall a, flat E a 8 -> adenot E a = Z_to_bv 64 (estart E a).
  Proof. intros a Hf. rewrite <- (flat_u E a 8 Hf). symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Lemma know_okP1 : know_ok RSEGS E M kn_FW.
  Proof.
    pose proof SPlo. pose proof SPhi. pose proof SPal.
    destruct FM.
    assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
    { intros off n A B C. apply flat_abs0; lia. }
    unfold know_ok, kn_FW. unfold SW1, SW2 in *.
    repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
    all: try (split; [lia|]; split; [apply FL; lia|]; rewrite adenot_lit0; cbn [edenot]; assumption).
    all: first
      [ (* [comment removed for export] *) split; [lia|]; cbn [edenot]; evs; assumption
      | (* [comment removed for export] *) cbn [edenot]; evs; lia
      | (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot]; evs; lia|];
        intros d m Hd Hm; unfold estart; cbn [a_base a_off]; cbn [edenot]; evs;
        apply store_ok_of_all; rewrite u_small by lia; [lia|]; intros x Hx; apply fw_win0; lia
      | (* [comment removed for export] *) split; [lia|]; split; [lia|]; intros i Hi; first [apply fw_ro0; lia | apply fw_err0; lia]
      | (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|];
        intros d m Hd Hm; unfold estart; cbn [a_base a_off edenot]; rewrite (u_small 0) by lia;
        apply store_ok_data; rewrite u_small by lia; lia ].
  Qed.

  (* [comment removed for export] *)
  Ltac covtac :=
    try (unfold estart, elenZ; cbn [a_base a_off]);
    first [ exact I
          | cbn [edenot]; evs; rewrite ?(u_small 0) by lia; unfold SW1, SW2; intros z Hz;
            first [ apply (D_img z (z + 1)); lia | apply (D_frame z (z + 1)); lia | apply D_sw1; unfold SW1; lia | apply D_sw2; unfold SW2; lia ] ].


  (* [comment removed for export] *)
  Lemma rdn_of_rst : ltac2:(CDefT.buildp (gd_tbl_A_fwrite_err1 ()) "PMM,P,(27.&40.)(1>.(27.&8.))Pa,(27.&40.)Pn,$2<.Pbs,(15.(27.&8.))P,(12.(1>.(15.(27.&8.)))(47.$48.(35.VD,R4.)R3.R2.)(23.(15.(27.&8.))R1.))P,(43.(44.(45.&40.R4.)(49.R3.))(4:.+2.+40.))P,(46.VD,(45.&40.R5.)(44.(45.&40.R5.)(49.R4.)))(12.(1>.(15.(27.&8.)))(47.$48.R7.R6.R5.)(23.(15.(27.&8.))R4.))")
(* [comment removed for export] *).
  Proof. intros MM a n bs H Hnw HD. rewrite <- (rdn_restrict_in RSEGS D MM a n Hnw HD). exact H. Qed.

  (* [comment removed for export] *)
  Lemma lor40_mod16 : forall x, (0 <= x)%Z -> ((Z.lor 40 x) mod 16 <> 0)%Z.
  Proof.
    intros x Hx EQ.
    assert (T : Z.testbit (Z.lor 40 x) 3 = true) by (rewrite Z.lor_spec; reflexivity).
    apply Z.testbit_true in T; [|lia]. change (2 ^ 3)%Z with 8%Z in T.
    pose proof (Z.lor_nonneg 40 x) as NN.
    pose proof (Z.div_mod (Z.lor 40 x) 16 ltac:(lia)) as DM. rewrite EQ, Z.add_0_r in DM.
    rewrite DM in T. replace (16 * (Z.lor 40 x / 16) / 8)%Z with (2 * (Z.lor 40 x / 16))%Z in T.
    2:{ symmetry. replace (16 * (Z.lor 40 x / 16))%Z with ((2 * (Z.lor 40 x / 16)) * 8)%Z by lia. apply Z.div_mul. lia. }
    rewrite Z.mul_comm, Z_mod_mult in T. lia.
  Qed.
  Lemma memset_align_false : forall x, (0 <= x)%Z ->
    bv_eqb (Z_to_bv 64 (Z.land (Z.lor 40 x) 15)) (Z_to_bv 64 0) = false.
  Proof.
    intros x Hx. change 15%Z with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4)%Z with 16%Z.
    pose proof (Z.mod_pos_bound (Z.lor 40 x) 16 ltac:(lia)) as B. pose proof (lor40_mod16 x Hx) as NZ.
    unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. exact NZ.
  Qed.

  Lemma lor40_bound : forall x, (0 <= x < 2^64)%Z -> (0 <= Z.lor 40 x < 2^64)%Z.
  Proof.
    intros x Hx. split; [apply Z.lor_nonneg; lia|].
    apply Z.log2_lt_pow2. { assert (0 <= Z.lor 40 x)%Z by (apply Z.lor_nonneg; lia). destruct (Z.eq_dec (Z.lor 40 x) 0) as [E0|]; [|lia]. exfalso. pose proof (lor40_mod16 x ltac:(lia)) as MZ. rewrite E0 in MZ. apply MZ. reflexivity. }
    rewrite Z.log2_lor by lia. apply Z.max_lub_lt; [reflexivity|].
    destruct (Z.eq_dec x 0) as [->|NZ]; [reflexivity|]. apply Z.log2_lt_pow2; lia.
  Qed.
  Lemma memset_align_false' : ltac2:(CDefT.buildp (gd_tbl_A_fwrite_err1 ()) "Px,$14.P,(11.(43.=R1.)(4;.R1.(4:.+2.+40.)))(12.$33.(4<.&40.(4=.&40.(4>.(45.&40.(4=.&40.(4?.(45.&40.(4=.&40.+28.))(45.&40.(4=.&40.R2.)))))(45.&40.(4=.&40.+?.))))(4=.&40.=))$37.)")
(* [comment removed for export] *).
  Proof.
    intros x Hx. rewrite (unsigned_lit 40), (unsigned_lit 15), (unsigned_lit x) by lia.
    rewrite unsigned_lit by (apply lor40_bound; lia). apply memset_align_false. lia.
  Qed.
  Lemma not_ltu1_false : ltac2:(CDefT.buildp (gd_tbl_A_fwrite_err1 ()) "Px,$14.P,(11.(43.=R1.)(4;.R1.(50.(4:.+2.+40.)+1.)))(12.$33.(51.&40.(4=.&40.(52.(45.&40.(4=.&40.R2.))(45.&40.(4=.&40.-1.))))(4=.&40.+1.))$37.)")
(* [comment removed for export] *).
  Proof.
    intros x Hx. rewrite (unsigned_lit x) by lia. replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615%Z by reflexivity.
    rewrite zb_lxor_ones by lia. unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia.
  Qed.

  Lemma alu_add_zlit : ltac2:(CDefT.buildp (gd_tbl_A_fwrite_err1 ()) "Px,(27.&40.)Pk,$14.P,(11.(43.=(44.(45.&40.R2.)R1.))(4;.(44.(45.&40.R2.)R1.)(4:.+2.+40.)))(12.(27.&40.)(53.$10.R3.(4=.&40.R2.))(4=.&40.(44.(45.&40.R3.)R2.)))")
(* [comment removed for export] *).
  Proof.
    intros x k Hk. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Ltac solve_sc :=
    cbn [sc_denot branch_taken];
    first
      [ cbn [edenot]; evs; rewrite !alu_add_zlit by lia;
        first
          [ (* [comment removed for export] *) apply Bool.negb_true_iff; unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia
          | (* [comment removed for export] *) rewrite alu_and, alu_or; unfold v_and, v_or; apply memset_align_false'; lia
          | (* [comment removed for export] *) rewrite alu_xor; unfold v_xor; apply not_ltu1_false; lia ] ].

  Theorem fwrite_errA : ltac2:(CDefT.buildp (gd_tbl_A_fwrite_err1 ()) "PKK,$54.P,A1.R1.(4.$55.)P,Pt0,(27.&40.)Pt1,(27.&40.)Pt2,(27.&40.)Pa0,(27.&40.)Pa1,(27.&40.)Pa2,(27.&40.)Pa3,(27.&40.)Pa4,(27.&40.)Pa5,(27.&40.)Pa6,(27.&40.)Pa7,(27.&40.)Pt3,(27.&40.)Pt4,(27.&40.)Pt5,(27.&40.)Pt6,(27.&40.)PM',P,(27.&40.)(1>.(27.&8.))Pmo',$39.P,(56.Vsp0,VM,R2.)P,A1.VKI,R2.P,(3=.Vmodel,R3.)(57.$48.(58.(59.(5:.(4=.&40.$5;.)Vsp0,(4=.&40.+10800.)(4=.&40.+63<:90.)R14.R13.R12.(2>.VR,(28.&5.+8.$29.))(2>.VR,(28.&5.+9.$29.))R11.R10.R?.R>.R=.R<.R;.R:.(2>.VR,(28.&5.+12.$29.))(2>.VR,(28.&5.+13.$29.))(2>.VR,(28.&5.+14.$29.))(2>.VR,(28.&5.+15.$29.))(2>.VR,(28.&5.+16.$29.))(2>.VR,(28.&5.+17.$29.))(2>.VR,(28.&5.+18.$29.))(2>.VR,(28.&5.+19.$29.))(2>.VR,(28.&5.+1:.$29.))(2>.VR,(28.&5.+1;.$29.))R9.R8.R7.R6.)(5<.&5.(27.&40.))(4=.&40.$5;.)(4=.&20.=)(5=.(27.&40.))R5.(5>.$48.))R4.)R16.)(57.$48.(58.(5?.$60.VR,(4=.&40.+58714.)VM,(5>.$48.))Vmodel,)(61.(62.+2.Vmsg,)R3.))")
(* [comment removed for export] *).
  Proof.
    intros KK HKnil HC.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof regs_okP1 as HR. pose proof know_okP1 as HK.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    try clear KNDc.
    lazymatch goal with HRx : regs_ok ?EE _ _ |- _ => let EE2 := eval unfold E in EE in lazymatch EE2 with Env (vals_ev ?Vx) ?bb => pose proof (kn_inD_residual D (Env (vals_ev Vx) bb) sp0 (-4096) LITS_KND ltac:(cbn [ev]; first [ exact vP0 | rewrite ?vals_ev_app_l by (rewrite ?length_app, ?junk_vals_length, ?valsP1_len; cbn; lia); exact vP0 ]) D_frameS HLITS_KND) as KNDc end end.
    run_blockA3 RRUN KNDc FUEL_FW STOPS_FW scr0 34%nat true covtac.
    all: try solve_sc.
    rename EQM into EQMA. rename OUT into OUTA. rename R0 into RA. rename M0 into MA0. rename HKmo into HKA. rename MM into MMA.
    (* [comment removed for export] *)
    unfold W.
    change (map (WriteEv (Z_to_bv 64 2)) msg) with (map (WriteEv (Z_to_bv 64 (sc_fd resB))) ([] ++ msg)).
    assert (FdA : fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))).
    { unfold m_fds in *. destruct MMA as (E1 & _). rewrite E1. exact Hfd2. }
    eapply (stdio_call_sound_frA AL CS KI IMG K_halted K_mat K_vmonly valsP1 (blobs_ev []) srA knA RA MA0 mo resB [] msg KK HR HK);
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn resB edenot].
    + vm_compute. reflexivity.
    + lia.
    + reflexivity.
    + rewrite u_small by lia. rewrite Hlen. unfold MLEN. lia.
    + cbn. rewrite Hlen. unfold MLEN. cbn. lia.                  (* [comment removed for export] *)
    + left. evs. rewrite alu_add_zlit by lia. rewrite !u_small by lia. lia.
    + left. evs. rewrite alu_add_zlit by lia. rewrite !u_small by lia. lia.
    + rewrite !u_small by lia. lia.
    + rewrite !u_small by lia. lia.                               (* [comment removed for export] *)
    + rewrite !u_small by lia. lia.                               (* [comment removed for export] *)
    + reflexivity.
    + (* [comment removed for export] *)
      rewrite Hlen. unfold MA, MLEN in *.
      apply (rdn_of_rst MA0); [| rewrite Z2Nat.id, u_small by lia; lia | rewrite Z2Nat.id, u_small by lia; apply D_img; lia].
      rewrite EQMA. rewrite <- (RestrictRun.rdn_restrictD RSEGS D M _ _ _ Hmsg ltac:(rewrite Z2Nat.id, u_small by lia; lia) ltac:(rewrite Z2Nat.id, u_small by lia; apply D_img; lia)).
      apply rdn_agree. intros j Hj. rewrite ?Z2Nat.id in Hj by lia. cbn [Z.to_nat Z.of_nat Pos.to_nat Pos.of_succ_nat Pos.iter_op Nat.add Pos.succ] in Hj. apply mem_denot_out.
      rewrite u_small by lia. cbn [log_out]. unfold adenot, v_addi. cbn [a_base a_off edenot]. evs.
      rewrite !(u_small 0) by lia. repeat split; rewrite ?u_small by lia; lia.
    + exact FdA.
    + exact HKA.
    + intros z Hz. revert Hz. evs. rewrite alu_add_zlit by lia. rewrite !u_small by lia. intros Hz. apply WCS. lia.
    + intros z Hz. rewrite !u_small in Hz by lia. lia.
    + intros z Hz. left. rewrite !u_small in Hz by lia. apply MCS. unfold HLO, MLEN. lia.
    + exact HKnil.
    + (* [comment removed for export] *)
      intros Rm MC moC HPOST HRm HKm HKC MMC. clear HR HK. rename HRm into HR. rename HKm into HK.
      (* [comment removed for export] *)
      try clear KNDc.
      lazymatch goal with HRx : regs_ok ?EE _ _ |- _ => let EE2 := eval unfold E in EE in lazymatch EE2 with Env (vals_ev ?Vx) ?bb => pose proof (kn_inD_residual D (Env (vals_ev Vx) bb) sp0 (-4096) LITS_KND ltac:(cbn [ev]; first [ exact vP0 | rewrite ?vals_ev_app_l by (rewrite ?length_app, ?junk_vals_length, ?valsP1_len; cbn; lia); exact vP0 ]) D_frameS HLITS_KND) as KNDc end end.
      run_blockA3 RRUN KNDc FUEL_FW STOPS_FW scr0 66%nat true covtac.
      all: try solve_sc.
      lazymatch goal with |- srealizesJ _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into RC; rename Mn into MD end.
      rename EQM into EQMC. rename OUT into OUTC. rename HKmo into HKD. rename MM into MMD.
      apply (srzJ_getr_ext RSEGS
               (mkR (Z_to_bv 64 RET) sp0 (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90)
                    (getr RC (Z_to_bv 5 5)) (getr RC (Z_to_bv 5 6)) (getr RC (Z_to_bv 5 7)) (getr R 8) (getr R 9)
                    (getr RC (Z_to_bv 5 10)) (getr RC (Z_to_bv 5 11)) (getr RC (Z_to_bv 5 12)) (getr RC (Z_to_bv 5 13))
                    (getr RC (Z_to_bv 5 14)) (getr RC (Z_to_bv 5 15)) (getr RC (Z_to_bv 5 16)) (getr RC (Z_to_bv 5 17))
                    (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                    (getr R 25) (getr R 26) (getr R 27)
                    (getr RC (Z_to_bv 5 28)) (getr RC (Z_to_bv 5 29)) (getr RC (Z_to_bv 5 30)) (getr RC (Z_to_bv 5 31))) RC).
      { intros r. pose proof (ridx_range r) as Hi.
        rewrite <- (ridx_roundtrip r). set (i := ridx r) in *. clearbody i.
        destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
          [ .. | lia];
          lazymatch goal with |- _ = getr RC (Z_to_bv 5 (Z.of_nat ?k)) =>
            first
              [ (transitivity (getr RC (Z_to_bv 5 (Z.of_nat k))); [reflexivity|reflexivity])
              | rewrite (HR (Z_to_bv 5 (Z.of_nat k)));
                lazymatch goal with |- _ = edenot _ (sr_get ?L ?rr) =>
                  let e := eval vm_compute in (sr_get L rr) in change (sr_get L rr) with e end;
                cbn [edenot]; unfold RET;
                first [ reflexivity
                      | (lazymatch goal with |- _ = ev _ ?n =>
                           change (ev _ n) with (vals_ev (valsP1 ++ junk_vals Rm) n);
                           rewrite vals_ev_app_l by (rewrite valsP1_len; lia);
                           first [ change (vals_ev valsP1 n) with sp0; reflexivity
                                 | change (vals_ev valsP1 n) with (ev E n); rewrite (evP1_junk (n - 1)) by lia;
                                   etransitivity; [reflexivity|]; reflexivity ] end) ] ]
          end. }
      change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
      unfold RET. apply HC; [ | exact HKD | ].
      2:{ eapply mo_mat_trans; [exact MMA|]. eapply mo_mat_trans; [exact MMC|]. exact MMD. }
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      cbn [sc_sp sc_f sc_bufp sc_bufsz resB edenot] in Pagree, Pwend, Pwpos, Pwbase.
      unfold E in Pagree. cbn [ev] in Pagree. rewrite vP0 in Pagree. rewrite alu_add_zlit in Pagree by lia. rewrite !u_small in Pagree by lia.
      assert (AG : forall x : word,
                 ~ (bv_unsigned sp0 - 4096 <= bv_unsigned x < bv_unsigned sp0)%Z ->
                 ~ (0x0fa488 <= bv_unsigned x < 0x0fa570)%Z -> MD x = M x).
      { intros x N1 N2. pose proof (u64_range x).
        destruct (D x) eqn:Dx.
        - rewrite <- (restrict_in D MD x Dx). rewrite EQMC. rewrite mem_denot_out.
          2:{ cbn [log_out]. unfold adenot, v_addi. cbn [a_base a_off edenot]. evs.
              rewrite ?(u_small 0) by lia. repeat split; rewrite ?u_small by lia; first [lia | exact I]. }
          rewrite (restrict_in D MC x Dx). rewrite Pagree by lia.
          rewrite <- (restrict_in D MA0 x Dx). rewrite EQMA. rewrite mem_denot_out.
          2:{ cbn [log_out]. unfold adenot, v_addi. cbn [a_base a_off edenot]. evs.
              rewrite ?(u_small 0) by lia. repeat split; rewrite ?u_small by lia; first [lia | exact I]. }
          apply (restrict_in D M x Dx).
        - assert (ND : forall lo hi, DcovZ D lo hi -> ~ (lo <= bv_unsigned x < hi)%Z).
          { intros lo hi Hc Hin. specialize (Hc (bv_unsigned x) Hin). rewrite Z_to_bv_bv_unsigned in Hc. congruence. }
          rewrite (OUTC x Dx). rewrite Pagree.
          2:{ apply (ND _ _ (D_frame (bv_unsigned sp0 - 2192 - 112) (bv_unsigned sp0 - 2192) ltac:(lia) ltac:(lia))). }
          2:{ apply (ND _ _ (D_img (0x0fa488 + 32) (0x0fa488 + 48) ltac:(lia) ltac:(lia))). }
          2:{ apply (ND _ _ (D_img (0x0fa488 + 56) (0x0fa488 + 64) ltac:(lia) ltac:(lia))). }
          apply (OUTA x Dx). }
      assert (GR : mem_grows M MD).
      { eapply mem_grows_trans; [eapply (grows_of_rst D); [exact EQMA | exact OUTA]|].
        eapply mem_grows_trans; [exact Pgrows|]. eapply (grows_of_rst D); [exact EQMC | exact OUTC]. }
      split.
      * exact AG.
      * intros x Hout. cbn [outside] in Hout. destruct Hout as (O1 & O2 & _). apply AG; lia.
      * exact GR.
      * apply mem_grows_wmono. exact GR.
      * (* [comment removed for export] *)
        krd HK (0x0fa488 + 140)%Z 4%nat F140. krd HK (0x0fa488 + 40)%Z 8%nat F40. krd HK (0x0fa488 + 56)%Z 8%nat F56.
        krd HK (0x0fa488 + 8)%Z 8%nat F8. krd HK (0x0fa488 + 16)%Z 8%nat F16.
        unfold file_clean. repeat split.
        -- exact F140.
        -- rewrite F40. reflexivity.
        -- rewrite F56. reflexivity.
        -- rewrite F8. reflexivity.
        -- rewrite F16. reflexivity.
  Qed.
End FW.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

