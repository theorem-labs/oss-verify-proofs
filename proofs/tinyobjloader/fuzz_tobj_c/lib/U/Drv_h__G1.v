(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "RsCut"; "sym_run"; "RsEcall"; "instr_at"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "cons"; "option"; "nil"; "Some"; "true"; "length"; "prod"; "bool"; "false"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "sprop"; "valuation"; "reg_sv"; "ss_next"; "SAlu"; "ss_pc"; "SVar"; "sstate"; "SPBranch"; "SPUlt"; "ss_lenient"; "SPNot"; "ss_facts"; "SExt"; "eval"; "rw"; "agree_below"; "sprop_below"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "ok_frameJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states"; "FUEL"; "XEH"; "XE0"; "@Stdlib.ZArith.BinInt.Z"; "of_nat"; "add"; "le"; "lt"; "modulo"; "mul"; "div"; "lor"; "pow"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx"; "f_F"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states"; "X_tr"; "E_cl"; "E_cl0"; "X_ov"; "X_sh"; "X_sh0"; "HCUTS"; "P_cl"; "P_cl0"; "XE0f"; "CFG"; "MEMO_1"; "MEMO_3"; "MEMO_5"; "MEMO_7"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "ALU_ADD"; "Ecall"; "BC_GEU"; "ALU_SRL"; "BC_LTU"; "ALU_OR"; "ALU_SLL"; "ALU_SUB"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r"; "INVX"; "UV"; "HDR"; "KdR"; "tvK"; "fds3"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "triple1"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "FdEntry"; "with_fds"; "fd_remove"; "m_fds"; "m_fs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead"; "S_after_lit"; "hdr_val"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "config_len"; "fbyte"; "die"; "msg_cannot_open"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states.RAddr"; "fwrite_entry"; "read_ecall"; "free_entry"; "malloc_entry"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "bytes_le_to_Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h.H"; "KH"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "K_tcons"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states.HAddr"; "msg_short_addr"; "target_run_entry"; "msg_overrun_addr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open"; "std_fds"; "@Corelib.Lists.ListDef"; "firstn"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframeJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.StrAddr"; "memcpy_entry"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m"; "JD"; "P0"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require stdpp.bitvector.bitvector.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase.
Require LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Require LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.State.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require LinuxProcessSemantics.Riscv.Prelude.
Require LinuxProcessSemantics.Riscv.Instr.
Require LinuxProcessSemantics.Riscv.Decode.
Require LinuxProcessSemantics.Riscv.DecodeC.
Require LinuxProcessSemantics.Riscv.Sem.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require Stdlib.Strings.Ascii.
Require Stdlib.Strings.String.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Require LinuxProcessSemantics.LinuxProcessSem.Fs.
Require LinuxProcessSemantics.LinuxProcessSem.Specs.
Require LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Drv_h_states.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states.
Import ListNotations.

Import MAddr RAddr StrAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module HAddr.
  Definition target_run_entry : Z := 0x13754.
  Definition msg_short_addr : Z := 0x1067b.
  Definition msg_overrun_addr : Z := 0x10429.
End HAddr.
Import HAddr.

Definition HCUTS : list Z := ltac2:(tb__ "0|0|
SdSaS70SdSaS7bSdSaS73SdSaS72SdSaS81SfSaA1A3A3A3A3A3").

Local Definition MEMO_1 : ltac2:(tb__ "0|0|
SeScS4A1A1") := ltac2:(tb__ "0|0|
S7S3S30SfSaA1S31S11A5").
Local Definition MEMO_1__f : ltac2:(tb__ "0|0|
SeScS4A1A1") := ltac2:(tb__ "0|0|
S6fS3S30SfSaA1S31S11A5").
Definition E_cl : sstate := ltac:(let x := eval vm_compute in (lf0 XEH (MEMO_1__f) 0) in exact x).
Local Lemma MEMO_1_c : ltac2:(tb__ "0|1|
S0SeScS4A1M0A1S48S10G0SdS4S5S3eS8A2SfS4A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_1 MEMO_1__f. Qed.
Local Lemma MEMO_1_e : ltac2:(tb__ "0|1|
S0SeScS4A1M0A1S7S3S30SfSaA1S31S11A5S10G0SdS4S5S3eS8A2SfS4A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] XEH true) MEMO_1 (Some [mkLeaf E_cl RsEcall]) (@eq_refl _ (sym_run segs FUEL [] XEH true)) MEMO_1_c). Qed.
Lemma run_xeh : ltac2:(tb__ "0|1|
S0SeScS4A1M0A1S7S3S30SfSaA1S31S11A5S10G0SdS4S5S3eS8A2SfS4A1A3A2A3").
Proof. exact MEMO_1_e. Qed.
Lemma E_cl_shape : ltac2:(tb__ "0|0|
S1S0SaS1dS3eA1S71A3S1S0S17S1aS3eZ11A2S16Z39A1A3S1S0S17S1aS3eZaA2S16Z3A1A3S0SbS1bS3eA1P99A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma cert_cl : ltac2:(tb__ "0|0|
S0SeS4cA1S9S3S1dS3eA1A2S10S4cS4eA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some Ecall)). Qed.
Local Definition MEMO_2 := S_after_lit E_cl 0.
Definition P_cl : sstate := ltac:(let x := eval vm_compute in (MEMO_2) in exact x).
Local Lemma MEMO_2_c : MEMO_2 = P_cl. Proof. vm_cast_no_check (@eq_refl _ MEMO_2). Qed.
Local Lemma MEMO_2_e : ltac2:(tb__ "0|0|
S0S1fS66S3eZ0A2S44A3").
Proof. exact (@eq_trans _ (S_after_lit E_cl 0) MEMO_2 (P_cl) (@eq_refl _ (S_after_lit E_cl 0)) MEMO_2_c). Qed.
Lemma P_cl_eq : ltac2:(tb__ "0|0|
S0S1fS66S3eZ0A2S44A3"). Proof. exact MEMO_2_e. Qed.
Local Definition MEMO_3 : ltac2:(tb__ "0|0|
SeScS4A1A1") := ltac2:(tb__ "0|0|
S7S3S30S43S44S11A5").
Local Definition MEMO_3__f : ltac2:(tb__ "0|0|
SeScS4A1A1") := ltac2:(tb__ "0|0|
S6fS3S30S43S44S11A5").
Definition X_sh : sstate := ltac:(let x := eval vm_compute in (lf0 P_cl (MEMO_3__f) 0) in exact x).
Definition X_ov : sstate := ltac:(let x := eval vm_compute in (lf0 P_cl (MEMO_3__f) 1) in exact x).
Definition X_tr : sstate := ltac:(let x := eval vm_compute in (lf0 P_cl (MEMO_3__f) 2) in exact x).
Local Lemma MEMO_3_c : ltac2:(tb__ "0|1|
S0SeScS4A1M0A1S49S10G0SdS4S5S41S6A2SdS4S5S40S6A2SdS4S5S3dS6A2SfS4A1A3A3A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_3 MEMO_3__f. Qed.
Local Lemma MEMO_3_e : ltac2:(tb__ "0|1|
S0SeScS4A1M0A1S7S3S30S43S44S11A5S10G0SdS4S5S41S6A2SdS4S5S40S6A2SdS4S5S3dS6A2SfS4A1A3A3A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL HCUTS P_cl true) MEMO_3 (Some [mkLeaf X_sh RsCut; mkLeaf X_ov RsCut; mkLeaf X_tr RsCut]) (@eq_refl _ (sym_run segs FUEL HCUTS P_cl true)) MEMO_3_c). Qed.
Lemma run_pcl : ltac2:(tb__ "0|1|
S0SeScS4A1M0A1S7S3S30S43S44S11A5S10G0SdS4S5S41S6A2SdS4S5S40S6A2SdS4S5S3dS6A2SfS4A1A3A3A3A2A3").
Proof. exact MEMO_3_e. Qed.

Definition CFG : sv := ltac:(let x := eval vm_compute in (reg_sv X_tr 18) in exact x).
Lemma CFG_eq : ltac2:(tb__ "0|2|
S0S17S47S1cS52S1cS50S1cS53S25S11Q8M0S1cS50S1eP67A1M1S16Z8A1A3A3S16Z39A1A3S16Z31A1A3S25S15G0G1A3A3A3").
Proof. reflexivity. Qed.
Lemma X_sh_shape : ltac2:(tb__ "0|0|
S1S0SaS1dS41A1S70A3S1S0SbS1bS41A1P99A3S1S0SeS18A1S6dS18S24S41A1U0A3S10S18S20S4fS16Z5A1S1eP64A1A3A2A3S1S0S17S1aS41ZaA2S16S7aA1A3S0S17S1aS41ZbA2S16Z1fA1A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma X_ov_shape : ltac2:(tb__ "0|3|
S1S0SaS1dS40A1S70A3S1S0SbS1bS40A1P99A3S1S0SeS18A1M0S6dS18S24S40A1M1U0A3S10S18S20S51S1eP64A1M2S1cS4dS47S16Z6A1A3A3A2A3S1S0G0S6dS18G1U1A3S10S18S23S20S4fS16Z5A1G2A3A1A2A3S1S0S17S1aS40ZaA2S16S7cA1A3S0S17S1aS40ZbA2S16Z1fA1A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma X_tr_shape : ltac2:(tb__ "0|3|
S1S0SaS1dS3dA1S7bA3S1S0SbS1bS3dA1P9dA3S1S0SeS18A1M0S6dS18S24S3dA1M1U0A3S10S18S23S20S51S1eP64A1M2S1cS4dS47S16Z6A1A3A3A1A2A3S1S0G0S6dS18G1U1A3S10S18S23S20S4fS16Z5A1G2A3A1A2A3S1S0S17S1aS3dZaA2S1cS4dS1eP66A1S16Z2A1A3A3S1S0S17S1aS3dZbA2S47A3S0S17S1aS3dZdA2S1cS4dS1cS54G2S47A3S16N6A1A3A3A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Local Definition MEMO_4 : ltac2:(tb__ "0|0|
S1f") := ltac2:(tb__ "0|0|
S75SdS18S21S1eP64A1S16Z4A1A2SfS18A1A3S32A2").
Definition XE0f : sstate := ltac:(let x := eval vm_compute in (MEMO_4) in exact x).
Local Lemma MEMO_4_c : MEMO_4 = XE0f. Proof. vm_cast_no_check (@eq_refl _ MEMO_4). Qed.
Local Lemma MEMO_4_e : ltac2:(tb__ "0|0|
S0S1fS75SdS18S21S1eP64A1S16Z4A1A2SfS18A1A3S32A2S46A3").
Proof. exact (@eq_trans _ (add_facts [SPUlt (SVar 100) (SLit 4)] XE0) MEMO_4 (XE0f) (@eq_refl _ (add_facts [SPUlt (SVar 100) (SLit 4)] XE0)) MEMO_4_c). Qed.
Lemma XE0f_eq : ltac2:(tb__ "0|0|
S0S1fS75SdS18S21S1eP64A1S16Z4A1A2SfS18A1A3S32A2S46A3"). Proof. exact MEMO_4_e. Qed.
Local Definition MEMO_5 : ltac2:(tb__ "0|0|
SeScS4A1A1") := ltac2:(tb__ "0|0|
S7S3S30SfSaA1S46S11A5").
Local Definition MEMO_5__f : ltac2:(tb__ "0|0|
SeScS4A1A1") := ltac2:(tb__ "0|0|
S6fS3S30SfSaA1S46S11A5").
Definition E_cl0 : sstate := ltac:(let x := eval vm_compute in (lf0 XE0f (MEMO_5__f) 0) in exact x).
Local Lemma MEMO_5_c : ltac2:(tb__ "0|1|
S0SeScS4A1M0A1S4aS10G0SdS4S5S3fS8A2SfS4A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_5 MEMO_5__f. Qed.
Local Lemma MEMO_5_e : ltac2:(tb__ "0|1|
S0SeScS4A1M0A1S7S3S30SfSaA1S46S11A5S10G0SdS4S5S3fS8A2SfS4A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] XE0f true) MEMO_5 (Some [mkLeaf E_cl0 RsEcall]) (@eq_refl _ (sym_run segs FUEL [] XE0f true)) MEMO_5_c). Qed.
Lemma run_xe0 : ltac2:(tb__ "0|1|
S0SeScS4A1M0A1S7S3S30SfSaA1S46S11A5S10G0SdS4S5S3fS8A2SfS4A1A3A2A3").
Proof. exact MEMO_5_e. Qed.
Lemma E_cl0_shape : ltac2:(tb__ "0|0|
S1S0SaS1dS3fA1S71A3S1S0S17S1aS3fZ11A2S16Z39A1A3S1S0S17S1aS3fZaA2S16Z3A1A3S0SbS1bS3fA1P99A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma cert_cl0 : ltac2:(tb__ "0|0|
S0SeS4cA1S9S3S1dS3fA1A2S10S4cS4eA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some Ecall)). Qed.
Local Definition MEMO_6 := S_after_lit E_cl0 0.
Definition P_cl0 : sstate := ltac:(let x := eval vm_compute in (MEMO_6) in exact x).
Local Lemma MEMO_6_c : MEMO_6 = P_cl0. Proof. vm_cast_no_check (@eq_refl _ MEMO_6). Qed.
Local Lemma MEMO_6_e : ltac2:(tb__ "0|0|
S0S1fS66S3fZ0A2S45A3").
Proof. exact (@eq_trans _ (S_after_lit E_cl0 0) MEMO_6 (P_cl0) (@eq_refl _ (S_after_lit E_cl0 0)) MEMO_6_c). Qed.
Lemma P_cl0_eq : ltac2:(tb__ "0|0|
S0S1fS66S3fZ0A2S45A3"). Proof. exact MEMO_6_e. Qed.
Local Definition MEMO_7 : ltac2:(tb__ "0|0|
SeScS4A1A1") := ltac2:(tb__ "0|0|
S7S3S30S43S45S11A5").
Local Definition MEMO_7__f : ltac2:(tb__ "0|0|
SeScS4A1A1") := ltac2:(tb__ "0|0|
S6fS3S30S43S45S11A5").
Definition X_sh0 : sstate := ltac:(let x := eval vm_compute in (lf0 P_cl0 (MEMO_7__f) 0) in exact x).
Local Lemma MEMO_7_c : ltac2:(tb__ "0|1|
S0SeScS4A1M0A1S4bS10G0SdS4S5S42S6A2SfS4A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_7 MEMO_7__f. Qed.
Local Lemma MEMO_7_e : ltac2:(tb__ "0|1|
S0SeScS4A1M0A1S7S3S30S43S45S11A5S10G0SdS4S5S42S6A2SfS4A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL HCUTS P_cl0 true) MEMO_7 (Some [mkLeaf X_sh0 RsCut]) (@eq_refl _ (sym_run segs FUEL HCUTS P_cl0 true)) MEMO_7_c). Qed.
Lemma run_pcl0 : ltac2:(tb__ "0|1|
S0SeScS4A1M0A1S7S3S30S43S45S11A5S10G0SdS4S5S42S6A2SfS4A1A3A2A3").
Proof. exact MEMO_7_e. Qed.
Lemma X_sh0_shape : ltac2:(tb__ "0|0|
S1S0SaS1dS42A1S70A3S1S0SbS1bS42A1P99A3S1S0S17S1aS42ZaA2S16S7aA1A3S0S17S1aS42ZbA2S16Z1fA1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
End Drv_h_states.

Module Drv_h.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import Stdlib.Strings.Ascii Stdlib.Strings.String.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DataWin OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ctx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r.

Import ListNotations.
Import MAddr RAddr HAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Section H.
Variable cx : Fctx.
Let sp := f_sp cx. Let brk := f_brk cx. Let mb := f_mb cx. Let draw := f_draw cx. Let inp := f_inp cx.
Let Hent : valid_entry48 imgU (mkEntry sp brk mb draw) inp := f_ent cx.
Let Hinp : valid_input_either inp := f_inp_ok cx.
Let argv := in_argv inp.
Let argv1 : list byte := nth 1 argv [].
Let fs := in_fs inp.
Let Hargc : length argv = 2%nat := f_argc cx.
Let ok : world -> Prop := f_ok cx.
Let SpecT : list event -> Prop := Spec inp.
Let HokK : forall K, K_tcons SpecT K -> ok_frame segs ok K := f_okK cx.
Let HokP : forall K, K_tcons SpecT K -> ok_pframe segs ok K := f_okP cx.
Let Hmay : open_may_succeed argv1 fs := f_may cx.
Local Notation F := (f_F cx).
Let HF : fs_lookup fs argv1 = Some F := f_HF cx.
Let Hnd : argv1 <> dot_path := f_nd cx.
Local Notation L := (Z.of_nat (length (f_F cx))).

Let P0 : ltac2:(tb__ "0|0|
S19OFr;") := ltac2:(tb__ "0|0|
S83Vsp;Vdraw;Vinp;A3").
Let JD : ltac2:(tb__ "0|1|
ScS60A1S5fOF_;M0F_;S19ScS13S17S17A2A1S6cG0F_;S2eFD;Ftv;Fr0;FK;") := ltac2:(tb__ "0|0|
S82Vsp;Vdraw;Vinp;A3").
Local Notation KdR := (U.Drv_r__G1.Drv_r.KdR cx).
Local Notation fds3 := (U.Drv_r__G1.Drv_r.fds3 cx).
Local Notation HDR := (U.Drv_r__G1.Drv_r.HDR cx).
Local Notation INVX := (U.Drv_r__G1.Drv_r.INVX cx).
Local Notation UV := U.Drv_r__G1.Drv_r.UV.

Definition KH : list event -> Model -> Prop := ltac2:(tb__ "0|1|
ScS60A1M0S5fS1S0G0R2SfS60A1A3S1S0ScS13S2aQ40A1S61A2A1S64R1A1S7dA3S0S7fS65R1A1Vfs;A3A2A2Lmd;Ltr;").

Lemma cannot_open_in_spec : ltac2:(tb__ "0|0|
VSpecT;S6aVfs;S6bVargv1;A1A2A1").
Proof using Hargc Hmay. unfold SpecT, Spec. apply spec_cannot_open. exact Hargc. Qed.
Lemma KH_tcons : K_tcons SpecT KH.
Proof using . intros tr md (-> & _ & _). exists (die fs (msg_cannot_open argv1)). split; [exact cannot_open_in_spec | apply is_prefix_nil]. Qed.
Lemma KH_vmi : vm_insensitive KH.
Proof using . split; [intros tr md vm (A & B & D) | intros tr md lz mt (A & B & D)]; (split; [exact A|]; split; autorewrite with model; assumption). Qed.
Lemma fds3_remove : ltac2:(tb__ "0|1|
SaS0ScS13S2aQ40M0A1S61A2A1S63S5aVcx;R1A2S2cG0Z3A2A2S7dA3Foff;").
Proof using . intros off. reflexivity. Qed.

Lemma JD_okf : ltac2:(tb__ "0|1|
ScS60A1S5fOF_;M0F_;S19ScS13S17S17A2A1S6cG0F_;S78VSpecT;R4A2S2fS3Vok;VJD;R5R4R3R2A4A3F_;FD;Ftv;Fr0;FK;").
Proof using HokK sp.
  intros K r0 tv D HK. apply (ok_frameJ_of_tcons segs ok SpecT); [apply HokK; intros tr md H; exact H|].
  intros rho tr md (Ai & (_ & Hk & _) & _). exact (HK tr md Hk).
Qed.
Lemma JD_okp : ltac2:(tb__ "0|1|
ScS60A1S5fOF_;M0F_;S19ScS13S17S17A2A1S6cG0F_;S78VSpecT;R4A2S80S3Vok;VJD;R5R4R3R2A4A3F_;FD;Ftv;Fr0;FK;").
Proof using HokP sp.
  intros K r0 tv D HK. apply (ok_pframeJ_of_tcons segs ok SpecT); [apply HokP; intros tr md H; exact H|].
  intros rho tr md (Ai & (_ & Hk & _) & _). exact (HK tr md Hk).
Qed.

Section CloseStep.
Variable r0 : valuation.
Variable D : MA -> Model -> Prop.
Hypothesis HDfds : ltac2:(tb__ "0|0|
S6cS5fScS13S2aQ40A1S61A2A1VD;R3R2A2VD;R4S62R2R3A2A2F_;Ff;Fmd;FA;").

Lemma jclose : ltac2:(tb__ "0|0|
S1fS19SaScS13S17S17A2A1S0SeS4cA1S9S3S1dR4A1A2S10S4cS4eA2A3S0S17S1aR5Z11A2S16Z39A1A3S0S17S1aR6ZaA2S16Z3A1A3S77P1fS1bR7A1A2S0S14S79S1bR8A1R5A2S11A3S5eS3Vok;S2dS3VJD;S58Vcx;R7A2Vr0;R6VD;A4R9R8A4S2dS3VJD;S76Vr0;R6VD;A4S66R9Z0A2R8A4A4F_;F_;F_;F_;F_;Ftv;Foff;Frho;FS;").
Proof using HDfds.
  intros S rho off tv Hi H17 H10 Hnx Htv.
  apply (triple1_closeJ segs S rho Hi H17 H10 ok).
  - apply JD_okf, (U.Drv_r__G1.Drv_r.KdR_tcons cx).
  - apply JD_okp, (U.Drv_r__G1.Drv_r.KdR_tcons cx).
  - intros tr md (Ai & (_ & (_ & Hf & _) & _) & _). rewrite Hf. eexists. reflexivity.
  - intros tr md (Ai & HJ & HD). exists Ai. split.
    + apply (JGi_sys segs C_U 31 (KdR off) KH r0 P0 (ss_next S) tv Ai rho rho tr tr md _ Hnx Htv).
      * intros i _. reflexivity.
      * intros l. reflexivity.
      * reflexivity.
      * unfold close_md'. autorewrite with model. reflexivity.
      * intros (-> & Hf & Hs). split; [reflexivity|]. unfold close_md'. autorewrite with model. rewrite Hf. split; [apply fds3_remove | exact Hs].
      * exact HJ.
    + unfold close_md'. apply HDfds. exact HD.
Qed.
Lemma ejclose : ltac2:(tb__ "0|0|
S1fS19SaScS13S17S17A2A1S0SeS4cA1S9S3S1dR4A1A2S10S4cS4eA2A3S0S17S1aR5Z11A2S16Z39A1A3S0S17S1aR6ZaA2S16Z3A1A3S77P1fS1bR7A1A2S0S14S79S1bR8A1R5A2S11A3S5bS3S2dS3VJD;S58Vcx;R7A2Vr0;R6VD;A4R9R8A4S2dS3VJD;S76Vr0;R6VD;A4S66R9Z0A2R8A4A3F_;F_;F_;F_;F_;Ftv;Foff;Frho;FS;").
Proof using HDfds.
  intros S rho off tv Hi H17 H10 Hnx Htv.
  apply (etriple_closeJ segs S rho Hi H17 H10).
  - intros tr md (Ai & (_ & (_ & Hf & _) & _) & _). rewrite Hf. eexists. reflexivity.
  - intros tr md (Ai & HJ & HD). exists Ai. split.
    + apply (JGi_sys segs C_U 31 (KdR off) KH r0 P0 (ss_next S) tv Ai rho rho tr tr md _ Hnx Htv).
      * intros i _. reflexivity.
      * intros l. reflexivity.
      * reflexivity.
      * unfold close_md'. autorewrite with model. reflexivity.
      * intros (-> & Hf & Hs). split; [reflexivity|]. unfold close_md'. autorewrite with model. rewrite Hf. split; [apply fds3_remove | exact Hs].
      * exact HJ.
    + unfold close_md'. apply HDfds. exact HD.
Qed.
End CloseStep.

Lemma lor_byte_shift8 : ltac2:(tb__ "0|3|
SaSaS1S35Z0R2A2M0S36R2Z100M1A2A2G0S0SaS3aS38G1R3A2M2R4A2S34R4G2A2A3F_;F_;Fb;Fa;").
Proof using Hargc.
  intros a b Ha Hb.
  assert (D : Z.land (256 * b) a = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n 8) as [Hn8|Hn8].
    - replace (256 * b) with (b * 2 ^ 8) by lia. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite (Z.bits_above_log2 a n); [apply Bool.andb_false_r| lia |].
      assert (Z.log2 a < 8); [|lia].
      destruct (Z.eq_dec a 0) as [->|Hz]; [cbn; lia|].
      apply Z.log2_lt_pow2; lia. }
  rewrite <- (Z.lxor_lor _ _ D), <- (Z.add_nocarry_lxor _ _ D). lia.
Qed.
Lemma bytes_le_to_Z_cons : ltac2:(tb__ "0|2|
S2aQ8M0A1M1ScG1A1S0SaS74SdG1R2R1A3A1S34S2bG0R2A2S38Z100S74R1A1A2A2A3Frest;Fb;").
Proof using Hargc.
  intros b rest. cbn [bytes_le_to_Z]. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  pose proof (bytes_le_to_Z_nonneg rest). pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  rewrite Z.lor_comm, (Z.mul_comm _ 256). apply lor_byte_shift8; lia.
Qed.
Lemma bytes_le_to_Z_4 : ltac2:(tb__ "0|3|
S2aQ8M0A1M1G1G1G1ScG1A1S0SaS74S7eG1U4SdG1R5SdG1R4SdG1R3SdG1R2R1A3A3A3A3A3A1S34S2bG0R5A2S38Z100M2S34S2bG0R4A2S38G2S34S2bG0R3A2S38G2S2bG0R2A2A2A2A2A2A2A2A3Frest;Fb3;Fb2;Fb1;Fb0;").
Proof using Hargc. intros. cbn [firstn]. rewrite !bytes_le_to_Z_cons. change (bytes_le_to_Z (firstn 0 rest)) with 0. lia. Qed.

Lemma HDR_bytes_gen : ltac2:(tb__ "0|5|
ScS2aQ8A1M0A1S2aQ40M1A1S35Z4S33S12G0R2A2A1A2S0SaS37S2bG1R2A2S3bZ2Z20A2M2A2S37S2bG1S67R3A1A2G2A2A3S1S0SaS37S2bG1R3A2M3Z100M4A2S69R4U0A2A3S1S0SaS37S39G3G4A2G4A2S69R4U1A2A3S0SaS37S39G3Z10000A2G4A2S69R4U2A2A3A2A2F_;F_;Fv;FG;").
Proof using Hargc.
  intros G v HL4 H. unfold hdr_val in H.
  destruct G as [|b0 [|b1 [|b2 [|b3 rest]]]]; try (cbn in HL4; lia).
  rewrite bytes_le_to_Z_4 in H.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  change (bv_modulus 8) with 256 in *. unfold fbyte. cbn [nth].
  rewrite U_addr in H by lia. rewrite (Z.mod_small (bv_unsigned b0 + _)) in H by lia.
  set (x := bv_unsigned v) in *.
  pose proof (Z.div_mod x (2 ^ 32) ltac:(lia)) as Hx. rewrite H in Hx. set (q := x / 2 ^ 32) in Hx.
  assert (D1 : x / 256 = 2 ^ 24 * q + (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))).
  { symmetry. apply (Z.div_unique x 256 _ (bv_unsigned b0)); [left; lia | lia]. }
  assert (D2 : x / 65536 = 2 ^ 16 * q + (bv_unsigned b2 + 256 * bv_unsigned b3)).
  { symmetry. apply (Z.div_unique x 65536 _ (bv_unsigned b0 + 256 * bv_unsigned b1)); [left; lia | lia]. }
  split; [|split].
  - symmetry. apply (Z.mod_unique x 256 (2 ^ 24 * q + (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3)))); [left; lia | lia].
  - rewrite D1. symmetry. apply (Z.mod_unique _ 256 (2 ^ 16 * q + (bv_unsigned b2 + 256 * bv_unsigned b3))); [left; lia | lia].
  - rewrite D2. symmetry. apply (Z.mod_unique _ 256 (2 ^ 8 * q + bv_unsigned b3)); [left; lia | lia].
Qed.

Lemma HDR_bytes : ltac2:(tb__ "0|4|
S2aQ40M0A1S35Z4S33S12S2aQ8A1S3cVcx;A1M1A2A1A2S57Vcx;R2A2S1S0SaS37S2bG0R3A2M2Z100M3A2S69G1U0A2A3S1S0SaS37S39G2G3A2G3A2S69G1U1A2A3S0SaS37S39G2Z10000A2G3A2S69G1U2A2A3A2A2F_;F_;Fv;").
Proof using . intros v HL4 H. exact (HDR_bytes_gen F v HL4 H). Qed.

Lemma CFG_val : ltac2:(tb__ "0|1|
S19S35Z4S33S12S2aQ8A1S3cVcx;A1M0A2A1A2S57Vcx;S27R2P67A2A2S0SaS2bQ40S26R3S47A2A2S68G0A1A3F_;F_;Frho;").
Proof using .
  intros rho HL4 H. destruct (HDR_bytes (rw rho 103) HL4 H) as (B0 & B1 & B2).
  pose proof (fbyte_range F 0) as R0. pose proof (fbyte_range F 1) as R1.
  rewrite config_len_bytes, CFG_eq. cbn [eval]. rewrite or_val_A.
  rewrite U_zext_w by (cbv; discriminate). change (2 ^ Z.of_N 8) with 256. rewrite B0.
  rewrite srl_val. change (49 mod 64) with 49. rewrite Z.shiftr_div_pow2 by lia.
  rewrite sll_val. change (57 mod 64) with 57. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite U_sext_w by (cbv; try discriminate; reflexivity). change (2 ^ Z.of_N 8) with 256. change (Z.of_N 8) with 8.
  rewrite srl_val. change (8 mod 64) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite B1.
  unfold zsext. change (2 ^ (8 - 1)) with 128. unfold M64v.
  assert (E : (if fbyte F 1 <? 128 then fbyte F 1 else fbyte F 1 + 18446744073709551616 - 256) * 2 ^ 57 mod 2 ^ 64 / 2 ^ 49 = 256 * (fbyte F 1 mod 128)).
  { destruct (Z.ltb_spec (fbyte F 1) 128).
    - rewrite (Z.mod_small (fbyte F 1) 128) by lia. rewrite Z.mod_small by (change (2 ^ 64) with (128 * 2 ^ 57); nia).
      change (2 ^ 57) with (256 * 2 ^ 49). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
    - replace (fbyte F 1 mod 128) with (fbyte F 1 - 128) by (apply (Z.mod_unique _ 128 1); [left; lia | lia]).
      replace ((fbyte F 1 + 18446744073709551616 - 256) * 2 ^ 57) with ((fbyte F 1 - 128) * 2 ^ 57 + (2 ^ 57 - 1) * 2 ^ 64) by lia.
      rewrite Z_mod_plus_full. rewrite Z.mod_small by (change (2 ^ 64) with (128 * 2 ^ 57); nia).
      change (2 ^ 57) with (256 * 2 ^ 49). rewrite Z.mul_assoc, Z.div_mul by lia. lia. }
  change (2 ^ 8) with 256. rewrite E. apply lor_byte_shift8; [exact R0 | apply Z.mod_pos_bound; lia].
Qed.

Lemma CFG6_val : ltac2:(tb__ "0|2|
S19S35Z4S33S12S2aQ8A1S3cVcx;A1M0A2A1A2S57Vcx;S27R2P67A2A2S0SaS2bQ40S26R3S1cS4dS47S16Z6M1A1A3A2A2S34S68G0A1G1A2A3F_;F_;Frho;").
Proof using .
  intros rho HL4 H. rewrite CursorGlue.U_add, (CFG_val rho HL4 H), CursorGlue.U_lit.
  pose proof (config_len_range F). unfold CFG_COUNT_BIT in *. unfold M64v. rewrite (Z.mod_small 6) by lia. apply Z.mod_small. lia.
Qed.

Lemma INVX_agree : ltac2:(tb__ "0|0|
SaS19S19SbS77P68R1A2S28R2R4R3A3S55Vcx;R6R5A3S55Vcx;R7R5A3F_;F_;F_;Fn;Frho';Frho;Fcap;").
Proof using .
  intros cap rho rho' n Hn (Hw & _ & _) (A & B & C & D). unfold U.Drv_r__G1.Drv_r.INVX, U.Drv_r__G1.Drv_r.UV in *.
  rewrite <- !Hw by lia. auto.
Qed.

Lemma lenients : ltac2:(tb__ "0|0|
S1S0S14S22S31A1S15A3S1S0S14S22S44A1S15A3S1S0S14S22S46A1S15A3S0S14S22S45A1S15A3A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma nexts : ltac2:(tb__ "0|1|
S1S0SbS1bS31A1P99M0A3S1S0SbS1bS44A1G0A3S1S0SbS1bS32A1G0A3S1S0SbS1bS46A1G0A3S0SbS1bS45A1G0A3A2A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma fb_xe0 : ltac2:(tb__ "0|0|
S0S14S6eS18S29S1bS32A1A1SdS18S21S1eP64A1S16Z4A1A2SfS18A1A3A3S11A3").
Proof using . reflexivity. Qed.

Section Disp.
Variable r0 : valuation.
Variable D : MA -> Model -> Prop.
Hypothesis HDfds : ltac2:(tb__ "0|0|
S6cS5fScS13S2aQ40A1S61A2A1VD;R3R2A2VD;R4S62R2R3A2A2F_;Ff;Fmd;FA;").
Let JR (off : Z) : jpred := ltac2:(tb__ "0|0|
VJD;S58Vcx;Voff;A2Vr0;S59VD;A4").
Let JH : jpred := ltac2:(tb__ "0|0|
VJD;S76Vr0;S59VD;A4").

Section Safe.

Hypothesis TSH : ltac2:(tb__ "0|0|
S19S36S33S12S2aQ8A1S3cVcx;A1A2A1Z6A2S5cS3Vok;S2dS3VJH;S41R2A4S5dS2L_;A4F_;Frho;").
Hypothesis TSH0 : ltac2:(tb__ "0|0|
S19S36S33S12S2aQ8A1S3cVcx;A1A2A1Z4A2S5cS3Vok;S2dS3VJH;S42R2A4S5dS2L_;A4F_;Frho;").
Hypothesis TOV : ltac2:(tb__ "0|3|
S19SaS55Vcx;R1R2A3S1S35Z6M0S33S12S2aQ8A1S3cVcx;A1M1A2A1M2A2S36G2S34G0S68G1A1A2A2A2S5cS3Vok;S2dS3VJH;S40R4A4S5dS2L_;A4F_;F_;Fcap;Frho;").
Hypothesis TTR : ltac2:(tb__ "0|1|
S19SaS55Vcx;R1R2A3S35S34Z6S68S3cVcx;A1M0A1A2S33S12S2aQ8A1G0A2A1A2S5cS3Vok;S2dS3VJH;S3dR4A4S5dS2L_;A4F_;F_;Fcap;Frho;").

Theorem xeh_safe : ltac2:(tb__ "0|0|
S19SaS55Vcx;R1R2A3S5cS3Vok;S2dS3VJR;S33S12S2aQ8A1S3cVcx;A1A2A1A1S31R3A4S5dS2L_;A4F_;Fcap;Frho;").
Proof using HDfds TOV TSH TTR.
  intros rho cap HX. destruct lenients as (Ln1 & Ln2 & _). destruct nexts as (Nx1 & Nx2 & _).
  eapply (run_trJ segs ok FUEL [] XEH _ _ rho _ run_xeh Ln1); [apply JD_okf, (U.Drv_r__G1.Drv_r.KdR_tcons cx) | apply (U.Drv_r__G1.Drv_r.JD_stable cx); [rewrite Nx1; lia | rewrite Nx1; apply (U.Drv_r__G1.Drv_r.tvK_below cx); lia] |].
  intros Lf rho1 [<-|[]] Hag1. cbn [lf_state]. rewrite Nx1 in Hag1.
  destruct E_cl_shape as (Cpc & C17 & C10 & Cnx).
  eapply triple_seq.
  { apply triple1_triple. apply (jclose r0 D HDfds E_cl rho1 L U.Drv_r__G1.Drv_r.tvK cert_cl C17 C10); rewrite Cnx; [lia | apply (U.Drv_r__G1.Drv_r.tvK_below cx); lia]. }
  rewrite P_cl_eq.
  eapply (run_trJ segs ok FUEL HCUTS P_cl _ _ rho1 _ run_pcl Ln2); [apply JD_okf, KH_tcons | apply (U.Drv_r__G1.Drv_r.JD_stable cx); [rewrite Nx2; lia | rewrite Nx2; apply (U.Drv_r__G1.Drv_r.tvK_below cx); lia] |].
  rewrite Nx2. intros Lf rho2 [<-|[<-|[<-|[]]]] Hag2; cbn [lf_state].
  -
    apply triple_factsJ. intros HF0.
    pose proof (Forall_nth_error _ _ _ _ HF0 (proj1 (proj2 (proj2 X_sh_shape)))) as Hf. apply holds_bgeu in Hf.
    rewrite CursorGlue.U_lit in Hf. cbn [eval] in Hf. change (5 mod M64v) with 5 in Hf.
    pose proof (INVX_agree cap rho rho2 153 ltac:(lia) (agree_below_trans _ _ _ _ Hag1 Hag2) HX) as (I1 & _). unfold U.Drv_r__G1.Drv_r.UV in I1. rewrite I1 in Hf.
    apply TSH. lia.
  -
    apply triple_factsJ. intros HF0.
    pose proof (Forall_nth_error _ _ _ _ HF0 (proj1 (proj2 (proj2 X_ov_shape)))) as Hf. apply holds_bltu in Hf.
    pose proof (INVX_agree cap rho rho2 153 ltac:(lia) (agree_below_trans _ _ _ _ Hag1 Hag2) HX) as HX2. pose proof HX2 as (I1 & I2 & I3 & I4 & I5 & I6).
    rewrite (CFG6_val rho2 ltac:(lia) I3) in Hf. cbn [eval] in Hf. unfold U.Drv_r__G1.Drv_r.UV in I1. rewrite I1 in Hf.
    pose proof (Forall_nth_error _ _ _ _ HF0 (proj1 (proj2 (proj2 (proj2 X_ov_shape))))) as Hg. apply holds_nbgeu in Hg.
    rewrite CursorGlue.U_lit in Hg. cbn [eval] in Hg. change (5 mod M64v) with 5 in Hg. rewrite I1 in Hg.
    apply (TOV rho2 cap HX2). lia.
  -
    apply triple_factsJ. intros HF0.
    pose proof (Forall_nth_error _ _ _ _ HF0 (proj1 (proj2 (proj2 X_tr_shape)))) as Hf. apply holds_nbltu in Hf.
    pose proof (INVX_agree cap rho rho2 153 ltac:(lia) (agree_below_trans _ _ _ _ Hag1 Hag2) HX) as HX2.
    pose proof HX2 as (I1 & I2 & I3 & I4 & I5 & I6).
    rewrite (CFG6_val rho2 ltac:(lia) I3) in Hf. cbn [eval] in Hf. unfold U.Drv_r__G1.Drv_r.UV in I1. rewrite I1 in Hf.
    apply (TTR rho2 cap HX2). lia.
Qed.

Theorem xe0_safe : ltac2:(tb__ "0|1|
S19S0SaS56R1P64A2S33S12S2aQ8A1S3cVcx;A1A2A1M0A3S0SaS56R2P65A2Z10000A3S36G0Z4A2S5cS3Vok;S2dS3VJR;G0A1S32R4A4S5dS2L_;A4F_;F_;F_;Frho;").
Proof using HDfds TSH0.
  intros rho H100 H101 HL. destruct lenients as (_ & _ & Ln1 & Ln2). destruct nexts as (_ & _ & Nx0 & Nx1 & Nx2).
  apply (triple_add_facts segs ok _ rho _ XE0 XE0f _ XE0f_eq fb_xe0).
  { constructor; [|constructor]. apply holds_ult. rewrite CursorGlue.U_lit. cbn [eval]. change (4 mod M64v) with 4. unfold U.Drv_r__G1.Drv_r.UV in H100. rewrite H100. exact HL. }
  eapply (run_trJ segs ok FUEL [] XE0f _ _ rho _ run_xe0 Ln1); [apply JD_okf, (U.Drv_r__G1.Drv_r.KdR_tcons cx) | apply (U.Drv_r__G1.Drv_r.JD_stable cx); [rewrite Nx1; lia | rewrite Nx1; apply (U.Drv_r__G1.Drv_r.tvK_below cx); lia] |].
  intros Lf rho1 [<-|[]] Hag1. cbn [lf_state]. rewrite Nx1 in Hag1.
  destruct E_cl0_shape as (Cpc & C17 & C10 & Cnx).
  eapply triple_seq.
  { apply triple1_triple. apply (jclose r0 D HDfds E_cl0 rho1 L U.Drv_r__G1.Drv_r.tvK cert_cl0 C17 C10); rewrite Cnx; [lia | apply (U.Drv_r__G1.Drv_r.tvK_below cx); lia]. }
  rewrite P_cl0_eq.
  eapply (run_trJ segs ok FUEL HCUTS P_cl0 _ _ rho1 _ run_pcl0 Ln2); [apply JD_okf, KH_tcons | apply (U.Drv_r__G1.Drv_r.JD_stable cx); [rewrite Nx2; lia | rewrite Nx2; apply (U.Drv_r__G1.Drv_r.tvK_below cx); lia] |].
  rewrite Nx2. intros Lf rho2 [<-|[]] Hag2; cbn [lf_state].
  apply TSH0. exact HL.
Qed.
End Safe.

Section Ex.
Variable Q : world -> Prop.
Hypothesis ESH : ltac2:(tb__ "0|0|
S19S36S33S12S2aQ8A1S3cVcx;A1A2A1Z6A2S5bS3S2dS3VJH;S41R2A4VQ;A3F_;Frho;").
Hypothesis ESH0 : ltac2:(tb__ "0|0|
S19S36S33S12S2aQ8A1S3cVcx;A1A2A1Z4A2S5bS3S2dS3VJH;S42R2A4VQ;A3F_;Frho;").
Hypothesis EOV : ltac2:(tb__ "0|3|
S19SaS55Vcx;R1R2A3S1S35Z6M0S33S12S2aQ8A1S3cVcx;A1M1A2A1M2A2S36G2S34G0S68G1A1A2A2A2S5bS3S2dS3VJH;S40R4A4VQ;A3F_;F_;Fcap;Frho;").
Hypothesis ETR : ltac2:(tb__ "0|1|
S19SaS55Vcx;R1R2A3S35S34Z6S68S3cVcx;A1M0A1A2S33S12S2aQ8A1G0A2A1A2S5bS3S2dS3VJH;S3dR4A4VQ;A3F_;F_;Fcap;Frho;").

Theorem xeh_exists : ltac2:(tb__ "0|0|
S19SaS55Vcx;R1R2A3S5bS3S2dS3VJR;S33S12S2aQ8A1S3cVcx;A1A2A1A1S31R3A4VQ;A3F_;Fcap;Frho;").
Proof using EOV ESH ETR HDfds.
  intros rho cap HX. destruct lenients as (Ln1 & Ln2 & _). destruct nexts as (Nx1 & Nx2 & _).
  eapply (erun_trJ segs FUEL [] XEH _ _ rho _ run_xeh Ln1); [apply (U.Drv_r__G1.Drv_r.JD_stable cx); [rewrite Nx1; lia | rewrite Nx1; apply (U.Drv_r__G1.Drv_r.tvK_below cx); lia] |].
  intros Lf rho1 [<-|[]] Hag1. cbn [lf_state]. rewrite Nx1 in Hag1.
  destruct E_cl_shape as (Cpc & C17 & C10 & Cnx).
  eapply etriple_seq.
  { apply (ejclose r0 D HDfds E_cl rho1 L U.Drv_r__G1.Drv_r.tvK cert_cl C17 C10); rewrite Cnx; [lia | apply (U.Drv_r__G1.Drv_r.tvK_below cx); lia]. }
  rewrite P_cl_eq.
  eapply (erun_trJ segs FUEL HCUTS P_cl _ _ rho1 _ run_pcl Ln2); [apply (U.Drv_r__G1.Drv_r.JD_stable cx); [rewrite Nx2; lia | rewrite Nx2; apply (U.Drv_r__G1.Drv_r.tvK_below cx); lia] |].
  rewrite Nx2. intros Lf rho2 [<-|[<-|[<-|[]]]] Hag2; cbn [lf_state].
  - apply etriple_factsJ. intros HF0.
    pose proof (Forall_nth_error _ _ _ _ HF0 (proj1 (proj2 (proj2 X_sh_shape)))) as Hf. apply holds_bgeu in Hf.
    rewrite CursorGlue.U_lit in Hf. cbn [eval] in Hf. change (5 mod M64v) with 5 in Hf.
    pose proof (INVX_agree cap rho rho2 153 ltac:(lia) (agree_below_trans _ _ _ _ Hag1 Hag2) HX) as (I1 & _). unfold U.Drv_r__G1.Drv_r.UV in I1. rewrite I1 in Hf.
    apply ESH. lia.
  - apply etriple_factsJ. intros HF0.
    pose proof (Forall_nth_error _ _ _ _ HF0 (proj1 (proj2 (proj2 X_ov_shape)))) as Hf. apply holds_bltu in Hf.
    pose proof (INVX_agree cap rho rho2 153 ltac:(lia) (agree_below_trans _ _ _ _ Hag1 Hag2) HX) as HX2. pose proof HX2 as (I1 & I2 & I3 & I4 & I5 & I6).
    rewrite (CFG6_val rho2 ltac:(lia) I3) in Hf. cbn [eval] in Hf. unfold U.Drv_r__G1.Drv_r.UV in I1. rewrite I1 in Hf.
    pose proof (Forall_nth_error _ _ _ _ HF0 (proj1 (proj2 (proj2 (proj2 X_ov_shape))))) as Hg. apply holds_nbgeu in Hg.
    rewrite CursorGlue.U_lit in Hg. cbn [eval] in Hg. change (5 mod M64v) with 5 in Hg. rewrite I1 in Hg.
    apply (EOV rho2 cap HX2). lia.
  - apply etriple_factsJ. intros HF0.
    pose proof (Forall_nth_error _ _ _ _ HF0 (proj1 (proj2 (proj2 X_tr_shape)))) as Hf. apply holds_nbltu in Hf.
    pose proof (INVX_agree cap rho rho2 153 ltac:(lia) (agree_below_trans _ _ _ _ Hag1 Hag2) HX) as HX2.
    pose proof HX2 as (I1 & I2 & I3 & I4 & I5 & I6).
    rewrite (CFG6_val rho2 ltac:(lia) I3) in Hf. cbn [eval] in Hf. unfold U.Drv_r__G1.Drv_r.UV in I1. rewrite I1 in Hf.
    apply (ETR rho2 cap HX2). lia.
Qed.

Theorem xe0_exists : ltac2:(tb__ "0|1|
S19S0SaS56R1P64A2S33S12S2aQ8A1S3cVcx;A1A2A1M0A3S0SaS56R2P65A2Z10000A3S36G0Z4A2S5bS3S2dS3VJR;G0A1S32R4A4VQ;A3F_;F_;F_;Frho;").
Proof using ESH0 HDfds.
  intros rho H100 H101 HL. destruct lenients as (_ & _ & Ln1 & Ln2). destruct nexts as (_ & _ & Nx0 & Nx1 & Nx2).
  apply (etriple_add_facts segs _ rho _ XE0 XE0f _ XE0f_eq fb_xe0).
  { constructor; [|constructor]. apply holds_ult. rewrite CursorGlue.U_lit. cbn [eval]. change (4 mod M64v) with 4. unfold U.Drv_r__G1.Drv_r.UV in H100. rewrite H100. exact HL. }
  eapply (erun_trJ segs FUEL [] XE0f _ _ rho _ run_xe0 Ln1); [apply (U.Drv_r__G1.Drv_r.JD_stable cx); [rewrite Nx1; lia | rewrite Nx1; apply (U.Drv_r__G1.Drv_r.tvK_below cx); lia] |].
  intros Lf rho1 [<-|[]] Hag1. cbn [lf_state]. rewrite Nx1 in Hag1.
  destruct E_cl0_shape as (Cpc & C17 & C10 & Cnx).
  eapply etriple_seq.
  { apply (ejclose r0 D HDfds E_cl0 rho1 L U.Drv_r__G1.Drv_r.tvK cert_cl0 C17 C10); rewrite Cnx; [lia | apply (U.Drv_r__G1.Drv_r.tvK_below cx); lia]. }
  rewrite P_cl0_eq.
  eapply (erun_trJ segs FUEL HCUTS P_cl0 _ _ rho1 _ run_pcl0 Ln2); [apply (U.Drv_r__G1.Drv_r.JD_stable cx); [rewrite Nx2; lia | rewrite Nx2; apply (U.Drv_r__G1.Drv_r.tvK_below cx); lia] |].
  rewrite Nx2. intros Lf rho2 [<-|[]] Hag2; cbn [lf_state].
  apply ESH0. exact HL.
Qed.
End Ex.
End Disp.

End H.
End Drv_h.
