(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "false"; "list"; "bool"; "pair"; "Some"; "option"; "prod"; "true"; "nat"; "None"; "length"; "orb"; "andb"; "app"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "mkCell"; "sv"; "sprop"; "SAlu"; "SVar"; "SPUle"; "sobj"; "valuation"; "mkObj"; "SExt"; "DUnknown"; "sstate"; "SPAlign"; "eval"; "DList"; "SPBranch"; "SPNot"; "mkSS"; "ss_objs"; "SPUlt"; "agree_below"; "reg_sv"; "ss_pc"; "DImage"; "DZero"; "FcsrFrm0"; "SLBytes"; "ss_lenient"; "ss_next"; "ss_facts"; "sv_eqb"; "obj_range"; "rw"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "holds"; "obj_holds"; "ranges_disjoint"; "rm"; "rom_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "False"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_OR"; "ALU_SRL"; "BC_EQ"; "BC_NE"; "ALU_SUB"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "leb"; "mul"; "pow"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "ok_frame"; "SPJ"; "LQ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "FdChannel"; "m_fds"; "m_fs"; "cstr_result"; "errno_ret"; "CstrOk"; "CstrTooLong"; "FdDir"; "FdFile"; "fd_insert"; "fd_lookup"; "read_cstr"; "with_fds"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "sym_run"; "lf_state"; "mkLeaf"; "add_fact"; "RsCut"; "RsEcall"; "RsFuel"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open"; "Kx"; "cstr_of"; "std_fds"; "md_open_of"; "open_entry"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "etriple"; "assn"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states"; "E_open"; "S_M"; "S_arg0"; "S_arg"; "S_operr"; "S_opok"; "S_M1x"; "S_M1"; "FUEL"; "F_err"; "O_dataM"; "S_argwL"; "drop_last"; "xs_M1"; "E_co"; "F_arg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open.Open"; "J25"; "md_open"; "JM"; "Jop"; "Jvars"; "frame_data"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open.Open.Ranges"; "sh3"; "shape_rng"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysOpen"; "S_after_open"; "openat_post"; "AT_FDCWD_word"; "O_RD_LARGEFILE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates"; "S_main"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "open_may_succeed"; "die"; "msg_cannot_open"; "@Stdlib.Lists.List"; "In"; "forallb"; "removelast"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "path_eqb"; "Fs"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "ms_read_byte"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "K_tcons"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states.OAddr"; "malloc_entry"; "open_ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init"; "dataU_hi"; "dataU_lo"; "imgU"; "pcU"; "phU"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei"; "dotdot_path";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "obj_rng"; "state_diff"; "win"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframe"; "rho_set_rw"; "smatch_pending"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1"; "arg1_cstr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "apply_xforms"; "xform"; "XSelect"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "mkEntry"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open"; "openat_errnos"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi"; "dot_path"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "subst_state"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "img_len"; "rand_off"; "str_off"; "tab"; "valid_entry48"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "Jinit"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.StrAddr"; "strnlen_entry"; "@Stdlib.Arith.PeanoNat.Nat"; "ltb"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysOpen.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Require LinuxProcessSemantics.LinuxProcessSem.Fs.
Require LinuxProcessSemantics.LinuxProcessSem.Specs.
Require LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall.
Require LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.
Require LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Drv_open_states.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysOpen.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates.

Import ListNotations.

Import StrAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module OAddr.
  Definition open_ecall : Z := 0x27bf8.
  Definition malloc_entry : Z := 0x2056c.
End OAddr.
Import OAddr.

Definition FUEL : nat := (8 * 1000)%nat.
Definition lf0 (S : sstate) (r : option (list leaf)) (i : nat) : sstate := ltac2:(tb__ "0|1|
S7S3S66A1M0A1S1dLr;Vr;G0S68Sb7S66Vi;R1S69VS;S6dA2A4A1Lls;VS;X7x2").

Definition F_arg : list sprop := ltac2:(tb__ "0|1|
S0S14S17S10Z7fff80000000A1S16P19A1M0A2S0S14S17G0S10Z800000400000A1A2S1S14A1A3A3").
Definition S_arg0 : sstate := ltac2:(tb__ "0|1|
SbeS0S8S3eS13A2M0S5S3eS13P2S10Z2A1A4S1G0A1A3S96S2eS96A1A3").
Definition S_argw : sstate := ltac2:(tb__ "0|0|
S23S28S7cA1S35S7cA1S34S7cA1S33S7cA1S36S7cA1SfS18S24S7cA1S0S18SadS16P1A1Z10U8S16P19A1A4S1S18A1A3A3S2fS7cA1P1aS2dS7cA1A9").
Definition S_argwL : sstate := ltac:(let x := eval vm_compute in S_argw in exact x).
Lemma S_argw_eq : S_argw = S_argwL. Proof. vm_cast_no_check (@eq_refl _ S_argwL). Qed.
Definition S_arg : sstate := ltac:(let x := eval vm_compute in (add_facts F_arg S_argw) in exact x).
Lemma S_arg_eq : ltac2:(tb__ "0|0|
S3fS1dSbdS89S85A2S7dA3"). Proof. vm_cast_no_check (@eq_refl _ S_arg). Qed.
Lemma S_arg0_next : ss_next S_arg0 = 25%positive. Proof. reflexivity. Qed.
Lemma swf_S_arg0 : swf S_arg0 = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma swf_S_argw : swf S_argw = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma S_argwL_objs : ltac2:(tb__ "0|0|
S3fS3S18A1S24S85A1S24S7dA1A3"). Proof. reflexivity. Qed.

Definition E_open : sstate := ltac:(let x := eval vm_compute in (lf0 S_arg (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.sym_run_fast segs FUEL [] S_arg true) 0) in exact x).
Lemma run_arg : ltac2:(tb__ "0|1|
S3fS7S3S66A1M0A1S67S3cS82S1S3dA1S7dS9A5S6G0S0S66S69S7aS6cA2S1S66A1A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some [mkLeaf E_open RsEcall])). Qed.
Lemma E_open_pc : ltac2:(tb__ "0|0|
S3fS3dS28S7aA1Sa4A3"). Proof. reflexivity. Qed.
Lemma E_open_regs : ltac2:(tb__ "0|0|
S40S3fS13S27S7aZ11A2S10Z38A1A3S40S3fS13S27S7aZaA2S10S94A1A3S40S3fS13S27S7aZcA2S10S95A1A3S3fS13S27S7aZbA2S16P19A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma E_open_next : ss_next E_open = 26%positive. Proof. reflexivity. Qed.

Definition F_err : sprop := SPUlt (SLit 0xFFFFFFFFFFFFF000) (SVar 26).
Local Definition MEMO_1 : ltac2:(tb__ "0|0|
S1d") := ltac2:(tb__ "0|0|
S6aS92S7aA1S83A2").
Definition S_operr : sstate := ltac:(let x := eval vm_compute in (MEMO_1) in exact x).
Local Lemma MEMO_1_c : MEMO_1 = S_operr. Proof. vm_cast_no_check (@eq_refl _ MEMO_1). Qed.
Local Lemma MEMO_1_e : ltac2:(tb__ "0|0|
S3fS1dS6aS92S7aA1S83A2S7eA3").
Proof. exact (@eq_trans _ (add_fact (S_after_open E_open) F_err) MEMO_1 (S_operr) (@eq_refl _ (add_fact (S_after_open E_open) F_err)) MEMO_1_c). Qed.
Lemma S_operr_eq : ltac2:(tb__ "0|0|
S3fS1dS6aS92S7aA1S83A2S7eA3"). Proof. exact MEMO_1_e. Qed.

Definition E_co : sstate := ltac:(let x := eval vm_compute in (lf0 S_operr (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.sym_run_fast segs FUEL [strnlen_entry] S_operr true) 0) in exact x).
Lemma run_operr : ltac2:(tb__ "0|1|
S3fS7S3S66A1M0A1S67S3cS82S0S3dSc5S1S3dA1A3S7eS9A5S6G0S0S66S69S88S6bA2S1S66A1A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some [mkLeaf E_co RsCut])). Qed.

Definition S_opok : sstate := ltac:(let x := eval vm_compute in (
  let T := S_after_open E_open in
  mkSS (ss_pc T) (list_set (ss_regs T) 10 (SLit 3)) (ss_fregs T) (ss_fcsr T) (ss_resv T) (ss_objs T) (ss_facts T) (ss_next T) (ss_lenient T)) in exact x).
Lemma diff_opok : ltac2:(tb__ "0|4|
S3fS7S8S3S8S13S13A2M0A1M1S3S14A1M2A2M3A1SacS92S7aA1S7fA2S6G3S5G1G2S0G0S5S13S13S16P1aA1S10Z3A1A4S1G0A1A3S1S14A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SVar 26, SLit 3)], @nil sprop))). Qed.
Lemma swf_S_opok : swf S_opok = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Definition S_M1 : sstate := ltac:(let x := eval vm_compute in (lf0 S_opok (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.sym_run_fast segs FUEL [malloc_entry] S_opok true) 0) in exact x).
Lemma run_opok : ltac2:(tb__ "0|1|
S3fS7S3S66A1M0A1S67S3cS82S0S3dSa3S1S3dA1A3S7fS9A5S6G0S0S66S69S81S6bA2S1S66A1A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some [mkLeaf S_M1 RsCut])). Qed.
Lemma S_M1_pc : ltac2:(tb__ "0|0|
S3fS3dS28S81A1Sa3A3"). Proof. reflexivity. Qed.

Definition xs_M1 : list xform := ltac2:(tb__ "0|0|
S0Sb3Sb4S0SaU0S0SaU1S0SaU2S0SaU3S0SaU4S0SaU5S0SaU7S0SaU6S1SaA1A3A3A3A3A3A3A3A3A1S1Sb3A1A3").
Local Definition MEMO_2 := apply_xforms S_M1 xs_M1.
Local Definition MEMO_2__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast S_M1 xs_M1.
Definition S_M1x : sstate := ltac:(let x := eval vm_compute in (match MEMO_2__f with Some X => X | None => S_M1 end) in exact x).
Local Lemma MEMO_2_c : MEMO_2 = Some S_M1x. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_2 MEMO_2__f. Qed.
Local Lemma MEMO_2_e : ltac2:(tb__ "0|0|
S3fS7S1dA1Sb2S81S87A2S6S1dS80A2A3").
Proof. exact (@eq_trans _ (apply_xforms S_M1 xs_M1) MEMO_2 (Some S_M1x) (@eq_refl _ (apply_xforms S_M1 xs_M1)) MEMO_2_c). Qed.
Lemma xs_M1_ok : ltac2:(tb__ "0|0|
S3fS7S1dA1Sb2S81S87A2S6S1dS80A2A3"). Proof. exact MEMO_2_e. Qed.

Definition O_dataM : sobj := ltac:(let x := eval vm_compute in (nth 7 (ss_objs S_M1x) dummy_obj) in exact x).
Definition drop_last (S : sstate) : sstate := ltac2:(tb__ "0|0|
S23S28VS;A1S35VS;A1S34VS;A1S33VS;A1S36VS;A1S9cS18S24VS;A1A2S2fVS;A1S2eVS;A1S2dVS;A1A9").

Local Definition MEMO_3 := drop_last S_M1x.
Definition S_M : sstate := ltac:(let x := eval vm_compute in (MEMO_3) in exact x).
Local Lemma MEMO_3_c : MEMO_3 = S_M. Proof. vm_cast_no_check (@eq_refl _ MEMO_3). Qed.
Local Lemma MEMO_3_e : ltac2:(tb__ "0|0|
S3fS1dS86S80A1S7bA3").
Proof. exact (@eq_trans _ (drop_last S_M1x) MEMO_3 (S_M) (@eq_refl _ (drop_last S_M1x)) MEMO_3_c). Qed.
Lemma S_M_eq : ltac2:(tb__ "0|0|
S3fS1dS86S80A1S7bA3"). Proof. exact MEMO_3_e. Qed.
Lemma S_M1x_objs : ltac2:(tb__ "0|0|
S3fS3S18A1S24S80A1SfS18S24S7bA1S0S18S84S1S18A1A3A3A3"). Proof. reflexivity. Qed.
Lemma swf_S_M : swf S_M = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma S_M_pc : ltac2:(tb__ "0|0|
S3fS3dS28S7bA1Sa3A3"). Proof. reflexivity. Qed.
Lemma S_M_next : ss_next S_M = 27%positive. Proof. reflexivity. Qed.
End Drv_open_states.

Module Drv_open.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysOpen.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states.

Import ListNotations.
Import OAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition Kx (t : list event) (m : Model) (tr : list event) (md : Model) : Prop := ltac2:(tb__ "0|0|
S40S3fS3S56A1Vtr;Vt;A3S3fS57Vmd;Vm;A3A2").

Section Generic.
Variable ok : world -> Prop.

Lemma LQ_elim : ltac2:(tb__ "0|0|
S3S56A1S57OF_;F_;S3eS19S3S66A1S76S66S19S9aS66R2R4A3S26R7R6R2A3S74S3cVok;S52S3cR9S68R4A1R3A4R5A4F_;F_;Frho';FL;S74S3cVok;S55S3cR6R5R4R3A5R2A4F_;FQ;Fleaves;Frho;Fn;FK;").
Proof using .
  intros K n rho leaves Q H. unfold LQ, LQJ.
  apply triple_ex; intros L. apply triple_ex; intros rho'.
  apply triple_pure; intros Hin. apply triple_pure; intros Hag.
  eapply triple_conseq; [| intros w Hw; exact Hw | exact (H L rho' Hin Hag)].
  intros w [Hsm Hk]. split; assumption.
Qed.

Lemma run_tr : ltac2:(tb__ "0|1|
SaS3S3dA1S1dS3S66A1M0S3S56A1S57OF_;F_;S19S76S3fS7G0A1S67S3cR7R6R5S9A5S6G0R4A2A3S3fS4S2dR6A1S2A3S53S3cVok;R5A3S66S19S9aS66R2R9A3S26S2eRbA1R8R2A3S74S3cVok;S52S3cRaS68R4A1R3A4R8A4F_;F_;Frho';FL;S74S3cVok;S52S3cR7R9R6A4R5A4F_;F_;F_;F_;FQ;Frho;FK;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves K rho Q Hrun Hstrict Hok H.
  eapply triple_seq; [apply triple1_triple; eapply sym_run_sound; [exact Hrun | exact Hok | rewrite Hstrict; discriminate]|].
  apply LQ_elim. exact H.
Qed.

Lemma erun_tr : ltac2:(tb__ "0|1|
SaS3S3dA1S1dS3S66A1M0S3S56A1S57OF_;F_;S19S73OF_;S3fS7G0A1S67S3cR7R6R5S9A5S6G0R4A2A3S3fS4S2dR6A1S2A3S66S19S9aS66R2R8A3S26S2eRaA1R7R2A3S75S3cS52S3cR9S68R4A1R3A4R7A3F_;F_;Frho';FL;S75S3cS52S3cR6R8R5A4R4A3F_;F_;F_;FQ;Frho;FK;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves K rho Q Hrun Hstrict H w Hsp.
  destruct (sym_run_complete segs fuel cuts S leaves K rho w Hstrict Hrun Hsp) as (L & rho' & w' & Hin & Hst & Hag & Hsp').
  destruct (H L rho' Hin Hag w' Hsp') as (w'' & Hst' & HQ).
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.

Lemma triple_from : ltac2:(tb__ "0|1|
S76S19S76F_;S76S73R4R1A1M0S41S19S19R5R1R3A2Lrho';A2F_;Fw;S19S74S3cVok;G0R3A4Frho';S74S3cVok;R5R3A4F_;F_;FQ;FP';FP;").
Proof using .
  intros P P' Q HP H. eapply triple_conseq; [exact HP | intros w Hw; exact Hw |]. apply triple_ex. exact H.
Qed.

Lemma triple_or : ltac2:(tb__ "0|0|
S76S76S76S74S3cVok;R3R1A4S74S3cVok;R3R2A4S74S3cVok;S73S42R6R1A1R5R1A1A2Lw;R3A4F_;F_;FQ;FP2;FP1;").
Proof using .
  intros P1 P2 Q H1 H2.
  apply (@triple_conseq segs ok (fun w => exists b : bool, (if b then P1 w else P2 w)) _ Q Q);
    [intros w [Hw|Hw]; [exists true | exists false]; exact Hw | intros w Hw; exact Hw |].
  apply triple_ex. intros [|]; assumption.
Qed.

Lemma etriple_from : ltac2:(tb__ "0|2|
S73OF_;M0S19G0F_;G0S73R4R1A1M1S41S19S19R5R1R3A2Lrho';A2F_;Fw;S19S75S3cG1R3A3Frho';S75S3cR5R3A3F_;F_;FQ;FP';FP;").
Proof using . intros P P' Q HP H w Hw. destruct (HP w Hw) as [rho' Hp']. exact (H rho' w Hp'). Qed.
End Generic.

Lemma SP_fact : ltac2:(tb__ "0|0|
S3S56A1S57OF_;F_;S1dS19S73S14S52S3cR5R4R3R2A5S9aS14R2S2fR5A1A3S37R5R3A2F_;F_;Fp;Fw;Frho;FS;FK;").
Proof. intros K S rho w p Hsp Hin. exact (proj1 (Forall_forall _ _) (SP_facts_hold segs K rho S w Hsp) p Hin). Qed.

Lemma U_lit64 : ltac2:(tb__ "0|0|
S19S3dS40S4cZ0R1A2S4dR1S51Z2Z40A2A2A2S3fS3dS77Q40S1fR3S10R2A1A2A2R2A3F_;Fz;Frho;").
Proof. intros rho z Hz. cbn. apply Z_to_bv_small. rewrite mod64. exact Hz. Qed.

Definition std_fds : list (word * FdEntry) := ltac2:(tb__ "0|6|
S0S8S78Q40M0A1M1S58A2M2S5G1S58S79G0Z0A2M3S59G3A1A4S0G2S5G1S58S79G0Z1A2M4S59G4A1A4S0G2S5G1S58S79G0Z2A2M5S59G5A1A4S1G2A1A3A3A3").

Definition open_entry (p : list byte) : FdEntry := ltac2:(tb__ "0|0|
S4S58L_;S9dVp;SbcA2S60S61Vp;S79Q40Z0A2A2X4x2").

Definition md_open_of (md : Model) (p : list byte) : Model := ltac2:(tb__ "0|0|
S65S62S5aVmd;A1S79Q40Z3A2S72Vp;A1A3Vmd;A2").

Definition cstr_of (p : list byte) : cstr_result := ltac2:(tb__ "0|0|
S4S5cL_;Sc6ScS78Q8A1Vp;A2U1000A2S5eVp;A1S5fX4x2").

Lemma alloc_fd_std : alloc_fd std_fds = Z_to_bv 64 3.
Proof. vm_compute. reflexivity. Qed.
Lemma lookup3_std : ltac2:(tb__ "0|0|
S3fS7S58A1S63S70S79Q40Z3A2A2SbS58A1A3").
Proof. vm_compute. reflexivity. Qed.
Lemma openat_errnos_small : ltac2:(tb__ "0|0|
S3dS9aS3dR1SbbA3S40S4dZ0R2A2S4dR2Z1000A2A2F_;Fe;").
Proof. intros e H. unfold openat_errnos in H. cbn in H. unfold ENOMEM, EACCES, EMFILE, ENFILE in H. lia. Qed.

Section OpenOutcome.
Variable md : Model.
Hypothesis Hfds : ltac2:(tb__ "0|0|
S3fS3S8S78Q40A1S58A2A1S5aVmd;A1S70A3").
Variable p : list byte.

Hypothesis Hndd : ltac2:(tb__ "0|0|
S3fS4S9dVp;SaaA2S2A3").

Lemma open_outcome_gen : ltac2:(tb__ "0|2|
S78Q40M0A1M1S57S93Vmd;S6fVp;A1R2R1A4S42S41S3dS3dS40S40S4dZ0R1A2S4dR1Z1000A2A2S40S3fG1R4S5dR1A1A3S3fS57R3Vmd;A3A2A2Le;A2S40S97Vp;S5bVmd;A1A2S40S3fG1R3S79G0Z3A2A3S3fS57R2S71Vmd;Vp;A2A3A2A2A2F_;Fmd';Fr;").
Proof using Hfds Hndd.
  intros r md' H. unfold cstr_of in H. unfold open_may_succeed. rewrite PATH_MAX_eq.
  destruct (Nat.ltb_spec (length p) 4096) as [Hlen|Hlen]; unfold openat_post in H.
  2:{ left. exists ENAMETOOLONG. unfold ENAMETOOLONG in *. destruct H as [-> ->]. repeat split; lia. }
  destruct p as [|b q].
  - left. exists ENOENT. unfold ENOENT in *. destruct H as [-> ->]. repeat split; lia.
  - rewrite Hfds, alloc_fd_std, lookup3_std, (path_is_dirref_not_dotdot _ Hndd) in H.
    destruct (path_eqb (b :: q) dot_path) eqn:Hd.
    + destruct H as [(e & Hin & -> & ->)|(_ & -> & ->)].
      * left. exists e. pose proof (openat_errnos_small e Hin). auto.
      * right. split; [|split; [reflexivity|]].
        -- apply path_eqb_eq in Hd. split; [lia|]. split; [discriminate|]. left. exact Hd.
        -- unfold md_open_of, openat_dir_model, open_entry. rewrite Hd, Hfds, alloc_fd_std. reflexivity.
    + destruct (fs_lookup (m_fs md) (b :: q)) as [F|] eqn:HF.
      * destruct H as [(e & Hin & -> & ->)|(_ & -> & ->)].
        -- left. exists e. pose proof (openat_errnos_small e Hin). auto.
        -- right. split; [|split; [reflexivity|]].
           ++ split; [lia|]. split; [discriminate|]. right. rewrite ?HF. discriminate.
           ++ unfold md_open_of, openat_file_model, open_entry. rewrite Hd, Hfds, alloc_fd_std. reflexivity.
      * left. exists ENOENT. unfold ENOENT in *. destruct H as [-> ->]. repeat split; lia.
Qed.

Lemma open_outcome_err_gen : ltac2:(tb__ "0|0|
S41S3dS3dS40S40S4dZ0R1A2S4dR1Z1000A2A2S93Vmd;S6fVp;A1S5dR1A1Vmd;A4A2Le;A2").
Proof using Hndd.
  unfold cstr_of. destruct (Nat.ltb_spec (length p) 4096) as [Hlen|Hlen]; unfold openat_post.
  2:{ exists ENAMETOOLONG. unfold ENAMETOOLONG. repeat split; lia. }
  destruct p as [|b q].
  - exists ENOENT. unfold ENOENT. repeat split; lia.
  - rewrite (path_is_dirref_not_dotdot _ Hndd). destruct (path_eqb (b :: q) dot_path) eqn:Hd.
    + exists ENOMEM. split; [unfold ENOMEM; lia|]. left. exists ENOMEM. split; [left; reflexivity | auto].
    + destruct (fs_lookup (m_fs md) (b :: q)) as [F|] eqn:HF.
      * exists ENOMEM. split; [unfold ENOMEM; lia|]. left. exists ENOMEM. split; [left; reflexivity | auto].
      * exists ENOENT. unfold ENOENT. repeat split; lia.
Qed.

Lemma open_outcome_ok_gen : ltac2:(tb__ "0|0|
S97Vp;S5bVmd;A1A2S93Vmd;S6fVp;A1S79Q40Z3A2S71Vmd;Vp;A2A4F_;").
Proof using Hfds Hndd.
  intros (Hlen & Hne & Hor). rewrite PATH_MAX_eq in Hlen. unfold cstr_of.
  destruct (Nat.ltb_spec (length p) 4096) as [_|Hlen']; [|lia].
  unfold openat_post. destruct p as [|b q]; [exfalso; exact (Hne eq_refl)|].
  rewrite Hfds, alloc_fd_std, lookup3_std, (path_is_dirref_not_dotdot _ Hndd).
  destruct (path_eqb (b :: q) dot_path) eqn:Hd.
  - right. split; [reflexivity|]. split; [reflexivity|].
    unfold md_open_of, openat_dir_model, open_entry. rewrite Hd, Hfds, alloc_fd_std. reflexivity.
  - destruct Hor as [Hdot|HF]; [rewrite Hdot, path_eqb_refl in Hd; discriminate|].
    destruct (fs_lookup (m_fs md) (b :: q)) as [F|] eqn:HF'; [|exfalso; exact (HF eq_refl)].
    right. split; [reflexivity|]. split; [reflexivity|].
    unfold md_open_of, openat_file_model, open_entry. rewrite Hd, Hfds, alloc_fd_std. reflexivity.
Qed.
End OpenOutcome.

Section Open.
Variable sp brk mb : word.
Variable draw : EntryDraw.
Variable lim : Z.
Variable inp : ProcInput.
Hypothesis Hent : ltac2:(tb__ "0|0|
Sc3Sa7SbaVsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Let argv := in_argv inp.
Let envp := in_envp inp.
Let argv0 : list byte := nth 0 argv [].
Let argv1 : list byte := nth 1 argv [].
Let fs := in_fs inp.
Hypothesis Hargc : length argv = 2%nat.

Variable md0 : Model.
Hypothesis Hfds0 : ltac2:(tb__ "0|0|
S3fS3S8S78Q40A1S58A2A1S5aVmd0;A1S70A3").
Hypothesis Hfs : ltac2:(tb__ "0|0|
S3fS9eS5bVmd0;A1Vfs;A3").
Variable ok : world -> Prop.
Let SpecT : list event -> Prop := Spec inp.
Hypothesis HokK : ltac2:(tb__ "0|0|
S3S56A1S57OF_;F_;Sa2VSpecT;R1A2S53S3cVok;R2A3F_;FK;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S3S56A1S57OF_;F_;Sa2VSpecT;R1A2SaeS3cVok;R2A3F_;FK;").

Lemma Hsp : valid_sp sp. Proof using Hent. exact (proj1 Hent). Qed.
Lemma Hargc2 : (2 <= length argv)%nat. Proof using Hargc. unfold argv in *. lia. Qed.

Lemma Hnsl1 : path_has_slash argv1 = false. Proof using Hargc Hinp. exact (proj1 (valid_input_arg1_plain inp Hinp Hargc2)). Qed.
Lemma Hndd1 : ltac2:(tb__ "0|0|
S3fS4S9dVargv1;SaaA2S2A3"). Proof using Hargc Hinp. exact (proj2 (valid_input_arg1_plain inp Hinp Hargc2)). Qed.
Lemma arg1_cstr_no_slash : cstr_no_slash (arg1_cstr inp).
Proof using Hargc Hinp. unfold arg1_cstr. fold argv argv1. destruct (length argv1 <? 4096)%nat; [exact Hnsl1 | exact I]. Qed.
Let JI : ltac2:(tb__ "0|0|
S19OFrho;") := ltac2:(tb__ "0|0|
Sc4S3cSa8Sa9Vsp;Vdraw;Vinp;A6").
Let STR : ltac2:(tb__ "0|0|
S3d") := ltac2:(tb__ "0|0|
S4eSc1Vargv;Venvp;A2A1").
Let RND : ltac2:(tb__ "0|0|
S3d") := ltac2:(tb__ "0|0|
S4eSc0Vargv;Venvp;A2A1").
Let LEN : ltac2:(tb__ "0|0|
S3d") := ltac2:(tb__ "0|0|
S4eSbfVargv;Venvp;A2A1").
Let ENVC := Z.of_nat (length envp).

Let A1 : Z := A1 sp inp.

Lemma A1_eq : ltac2:(tb__ "0|0|
S3fS3dVA1;S4bS4bS4bS77Q40Vsp;A2VSTR;A2S4eScS78Q8A1Vargv0;A2A1A2Z1A2A3").
Proof using argv envp. reflexivity. Qed.

Lemma NU : ltac2:(tb__ "0|7|
S40S40S4cZ7fff80000000S77Q40Vsp;A2M0A2S4cG0Z800000000000A2A2S40S3fS3dVSTR;S4bS4bZb8S50Z8M1Z2M2A2A2S50G1VENVC;A2A2A3S40S40S4cZ0VENVC;A2S4cVENVC;Z100A2A2S40S4cS4bS4bS4bS4eScS78Q8A1M3Vargv0;A2A1Z1M4A2S4eScG3Vargv1;A2A1M5A2G4A2S4eSc2Vargv;A1A1M6A2S40S4cS4bVSTR;G6A2VRND;A2S40S3fS3dVLEN;S4bVRND;Z10A2A3S40S4dVLEN;S51G2Z16A2A2S4cG5Z1ffffA2A2A2A2A2A2A2A2").
Proof using A1 Hargc Hent Hinp envp.
  pose proof (NUMS1 sp inp Hsp Hinp Hargc2) as N1. pose proof (InitStrs.NUMS sp inp Hsp Hinp) as N2.
  assert (E : Z.of_nat (length (in_argv inp)) = 2) by (unfold argv in Hargc; rewrite Hargc; reflexivity).
  unfold STR, RND, LEN, ENVC in *. unfold argv0, argv1 in *. unfold argv, envp in *. rewrite E in N1. lia.
Qed.

Lemma co_in_spec : ltac2:(tb__ "0|0|
VSpecT;S98Vfs;S99Vargv1;A1A2A1").
Proof using Hargc. unfold SpecT, Spec. apply spec_cannot_open. exact Hargc. Qed.
Lemma Ktc0 : ltac2:(tb__ "0|0|
S57Sa2VSpecT;S6eS1S56A1R1A2A2Fm;").
Proof using Hargc argv1 fs. intros m tr md [-> _]. exists (die fs (msg_cannot_open argv1)). split; [exact co_in_spec| exact I]. Qed.
Lemma okf0 : ltac2:(tb__ "0|0|
S57S53S3cVok;S6eS1S56A1R1A2A3Fm;"). Proof using Hargc HokK argv1 fs. intros m. apply HokK, Ktc0. Qed.
Lemma okp0 : ltac2:(tb__ "0|0|
S57SaeS3cVok;S6eS1S56A1R1A2A3Fm;"). Proof using Hargc HokP argv1 fs. intros m. apply HokP, Ktc0. Qed.

Definition J25 (rho : valuation) : Prop := ltac2:(tb__ "0|1|
S40VJI;Vrho;A1S3fS78Q40M0A1S32Vrho;P19A2S79G0VA1;A2A3A2").

Lemma J25_agree : ltac2:(tb__ "0|1|
S3eS19S19S26R3R2R1A3Sb5P1aR4A2S8aR4A1M0G0F_;F_;F_;Frho';Frho;Fn;").
Proof using Hargc.
  intros n rho rho' (Hw & Hl & Hm) Hn [HJ H25]. split.
  - destruct HJ; constructor; try (rewrite <- Hw by lia; assumption); try (rewrite <- Hl; assumption).
    intros a. rewrite <- Hm. auto.
  - rewrite <- Hw by lia. exact H25.
Qed.

Section Ranges.
Variable rho : valuation.
Hypothesis HJ : J25 rho.
Let HJI : JI rho := proj1 HJ.

Lemma R_v1 : ltac2:(tb__ "0|1|
S3fS3dS77Q40M0S1fVrho;S16P1A1A2A2S77G0Vsp;A2A3"). Proof using HJI. exact (J_v1 segs pcU phU sp draw inp rho HJI). Qed.
Lemma R_v3 : ltac2:(tb__ "0|0|
S3fS3dS77Q40S1fVrho;S16P3A1A2A2VENVC;A3"). Proof using HJI Hent Hinp envp. exact (J_v3 segs pcU phU sp draw inp Hsp Hinp rho HJI). Qed.
Lemma R_v4 : ltac2:(tb__ "0|1|
S3fS3dS77Q40M0S1fVrho;S16P4A1A2A2S4bS77G0Vsp;A2VSTR;A2A3"). Proof using HJI Hent Hinp argv envp. exact (J_v4 segs pcU phU sp draw inp Hsp Hinp rho HJI). Qed.
Lemma R_v5 : ltac2:(tb__ "0|0|
S3fS3dS77Q40S1fVrho;S16P5A1A2A2S4eScS78Q8A1Vargv0;A2A1A3"). Proof using HJI Hent Hinp argv. exact (J_v5 segs pcU phU sp draw inp Hsp Hinp rho HJI). Qed.
Lemma R_v6 : ltac2:(tb__ "0|1|
S3fS3dS77Q40M0S1fVrho;S16P6A1A2A2S4bS77G0Vsp;A2VRND;A2A3"). Proof using HJI Hent Hinp argv envp. exact (J_v6 segs pcU phU sp draw inp Hsp Hinp rho HJI). Qed.
Lemma R_v25 : ltac2:(tb__ "0|0|
S3fS3dS77Q40S1fVrho;S16P19A1A2A2VA1;A3").
Proof using ENVC HJ Hargc Hent Hinp LEN RND STR argv0 argv1. cbn [eval]. rewrite (proj2 HJ). pose proof NU. rewrite A1_eq. apply Z_to_bv_small. rewrite mod64. lia. Qed.
Let ADD := J_add inp rho.
Let LIT := J_lit rho.
Let SOFF := J_soff_small inp rho.
Let SOFFL := J_soff_lit rho.
Lemma R_sll3 : ltac2:(tb__ "0|0|
S3fS3dS77Q40S1fVrho;S15S45S16P3A1S10Z3A1A3A2A2S50Z8VENVC;A2A3").
Proof using HJI Hargc Hent Hinp LEN RND STR argv0 argv1. pose proof NU. apply (J_sll3 inp rho 3 ENVC R_v3). lia. Qed.

Definition sh3 (sh : sv * sv * sv) (a b c : sv) : bool := ltac2:(tb__ "0|1|
S8S8S13S13A2M0S13A2S4Lsh;Vsh;G0S13G0S4Lp;R2S13S13SeSeS30R2Va;A2S30R1Vb;A2A2S30R3Vc;A2A2Ly;Lx;X8x1Lz;Lp;X8x1").
Lemma sh3_sound : ltac2:(tb__ "0|2|
S8S8S13S13A2M0S13A2M1S13S13S13S3fS4S90R4R3R2R1A4S9A3S3fG1R5S5G0S13S5S13S13R4R3A4R2A4A3F_;Fc;Fb;Fa;Fsh;").
Proof using .
  intros [[x y] z] a b c H. unfold sh3 in H. apply andb_prop in H as [H Hz]. apply andb_prop in H as [Hx Hy].
  rewrite (sv_eqb_sound _ _ Hx), (sv_eqb_sound _ _ Hy), (sv_eqb_sound _ _ Hz). reflexivity.
Qed.

Definition shape_rng (sh : sv * sv * sv) : option (Z * Z) := ltac2:(tb__ "0|16|
S77Q40Vsp;A2S3dS4S7S8S3dS3dA2M0A1L_;M1S90Vsh;S16P1A1M2S10N100000M3A1S10Z0M4A1M5A4S6G0S5S3dS3dS4bR1G3A2S4bR1G4A2M6A4A2G1S90Vsh;G2G5S10Z10M7A1M8A4S6G0S5S3dS3dG6S4bR1G7A2M9A4A2G1S90Vsh;S15S44G2S10Z20MaA1A3G5S15S44S15S45S16P3A1S10Z3A1A3MbS10Z8McA1A3A4S6G0S5S3dS3dS4bS4bR1GaA2MdG4A2S4bGdS4bS50GcVENVC;A2MeGcA2A2A4A2G1S90Vsh;S15S44S15S44S15S44G2G8A3GbA3S10Z18MfA1M10A3G5S10Za0M11A1A4S6G0S5S3dS3dS4bS4bS4bG9GeA2GfA2M12G4A2S4bG12G11A2A4A2G1S90Vsh;S16P4A1G5S15S44S16P5A1S10Z1M13A1A3A4S6G0S5S3dS3dS4bS4bR1VSTR;A2M14G4A2S4bG14S4bS4eScS78Q8A1Vargv0;A2A1G13A2A2A4A2G1S90Vsh;S16P6A1G5G8A4S6G0S5S3dS3dS4bS4bR1VRND;A2M15G4A2S4bG15G7A2A4A2G1S90Vsh;G5S10Sa6A1S10Sa5A1A4S6G0S5S3dS3dS4bG4Sa6A2S4bG4Sa5A2A4A2G1S90Vsh;G2G8G10A4S6G0S5S3dS3dG9S4bR1GfA2A4A2SbG0A1X4x2X4x2X4x2X4x2X4x2X4x2X4x2X4x2Tb;").

Lemma shape_range : ltac2:(tb__ "0|1|
S18S8S3dS3dA2M0S3fS7G0A1S91SabR2A1A1S6G0R1A2A3S3fG0S31Vrho;R3A2R2A3F_;Fr;Fo;").
Proof using HJI Hargc Hent Hinp.
  pose proof NU as N. assert (D : 0 <= dataU_lo <= dataU_hi /\ dataU_hi < 2 ^ 40) by (unfold dataU_lo, dataU_hi; lia).
  intros [base lo hi cells d] r H. unfold shape_rng, obj_rng in H. cbn [ob_base ob_lo ob_hi] in H.
  repeat match type of H with
  | (if sh3 ?sh ?a ?b ?c then _ else _) = _ =>
      destruct (sh3 sh a b c) eqn:?E; [apply sh3_sound in E; injection E as -> -> ->; injection H as <-|clear E]
  | None = Some _ => discriminate
  end; apply (range_of_rng rho); cbn [ob_base ob_lo ob_hi];
  first [ exact R_v1 | exact R_v4 | exact R_v6 | apply SOFFL; lia | apply LIT; lia | idtac ].
  - apply (ADD _ _ _ _ R_v1); [apply LIT; lia | lia | lia | lia].
  - apply SOFF; [|lia]. apply (ADD _ _ _ _ R_sll3); [apply LIT; lia | lia | lia | lia].
  - apply (ADD _ _ (bv_unsigned sp + 16 + 8 * ENVC) 24); [| apply LIT; lia | lia | lia | lia].
    apply (ADD _ _ (bv_unsigned sp + 16) (8 * ENVC)); [| exact R_sll3 | lia | lia | lia].
    apply (ADD _ _ _ _ R_v1); [apply LIT; lia | lia | lia | lia].
  - apply SOFF; [|lia]. apply (ADD _ _ _ _ R_v5); [apply LIT; lia | lia | lia | lia].
Qed.

Lemma shapes_disjoint : ltac2:(tb__ "0|1|
S3S18A1S3dS3dS3fS4S9bS18S18S7S8S3dS3dA2M0A1S4Lx;S91SabR1A1A1G0G0S4Lp;R1S3dS3dSdSdSdS4fR1R2A2S4fR5R6A2A2S4fR1R6A2A2S4fR5R2A2A2Lb;La;X8x1Lp;S2X7x2Lo;R3A3S9A3Sb6S18S18S39S31Vrho;R1A2S5S3dS3dR4R3A4A2Lo;R4A3F_;Fhi;Flo;Fobjs;").
Proof using HJI Hargc Hent Hinp.
  intros objs lo hi H. apply Forall_forall. intros o Hin.
  pose proof (proj1 (forallb_forall _ _) H o Hin) as Ho. cbn beta in Ho.
  destruct (shape_rng (obj_rng o)) as [[a b]|] eqn:E; [|discriminate].
  rewrite (shape_range o (a, b) E). unfold ranges_disjoint. cbn [fst snd]. lia.
Qed.
End Ranges.

Ltac solve_disj HJ :=
  apply Forall_forall; intros o Hin;
  repeat (destruct Hin as [<-|Hin];
          [erewrite (shape_range _ HJ) by reflexivity; unfold ranges_disjoint, dataU_lo, dataU_hi; cbn [fst snd];
           fold argv envp; fold argv0 argv1; lia|]);
  destruct Hin.

Lemma JI_set25 : ltac2:(tb__ "0|0|
S19S78Q40A1VJI;R2A1VJI;SafR3P19R2A3A1F_;Fv;Frho;").
Proof using A1 ENVC Hargc LEN RND STR. intros rho v HJ. exact (Jinit_set_rw segs pcU phU sp draw inp rho 25 v HJ ltac:(lia)). Qed.

Lemma arg_intro : ltac2:(tb__ "0|1|
S19S73VJI;R2A1S52S3cS6eS1S56A1Vmd0;A2M0S96R3R2A5SafR4P19S79Q40VA1;A2A3S19S40S8aR1A1S52S3cG0S7dR1R4A5A2Trho';F_;F_;Fw;Frho;").
Proof using Hargc Hent Hinp.
  intros rho w HJ [Hsm Hk] rho'. pose proof NU as N.
  assert (HJ' : J25 rho') by (split; [apply JI_set25; exact HJ | apply rho_set_rw_at]).
  split; [exact HJ'|]. split; [|exact Hk].

  assert (Hsm0 : smatch segs rho S_arg0 w).
  { unfold S_arg0. apply smatch_subst_intro; [exact swf_S_arg0|].
    eapply smatch_agree; [|exact Hsm]. split; [|split; intros; reflexivity].
    intros i _. cbn [rho_sub rw wsub_get]. destruct (Pos.eqb_spec i 2) as [->|Hne]; cbn [eval]; [|reflexivity].
    rewrite (ji_argc _ _ _ _ _ _ _ HJ). unfold argv in Hargc. rewrite Hargc. reflexivity. }

  assert (Hsm1 : smatch segs rho' S_arg0 w).
  { eapply smatch_agree; [|exact Hsm0]. rewrite S_arg0_next. apply agree_below_set_rw. lia. }

  assert (Hsm2 : smatch segs rho' S_argw w).
  { unfold S_argw. pose proof (R_v1 rho' HJ') as B1.
    apply (smatch_carve_win segs rho' S_arg0 w (SVar 1) 16 8 (SVar 25) 26); try (rewrite ?B1; lia).
    - exact Hsm1.
    - exact swf_S_argw.
    - rewrite B1. replace (ss_objs S_arg0) with (removelast (ss_objs S_arg)) by reflexivity.
      cbn [removelast ss_objs S_arg]. solve_disj HJ'.
    - rewrite B1. unfold win_bytes_in_frame. cbn [eval]. rewrite (proj2 HJ').
      exact (arg1_ptr_frame segs pcU phU sp draw inp Hsp Hinp Hargc2 rho' (proj1 HJ')). }
  rewrite S_argw_eq in Hsm2. rewrite <- S_arg_eq. apply smatch_add_facts; [exact Hsm2 | | reflexivity].
  pose proof (R_v25 rho' HJ') as V25. rewrite A1_eq in V25.
  unfold F_arg. repeat constructor; cbn [holds]; unfold bv_leu; rewrite ?V25, ?(U_lit64 rho') by lia; lia.
Qed.

Lemma E_open_cstr : ltac2:(tb__ "0|1|
S19S3S56A1M0S9fS57S8aR4A1Sb0S3cR5S7aS5G0Sb8R4Sb9R3R2A2A4A4S3fS5cS64Sa1R4A1S1fR6S27S7aZbA2A2A2Sb1Vinp;A1A3F_;F_;Fmd;Fms;Ftr;Frho1;").
Proof using Hargc Hent Hinp.
  intros rho1 tr ms md HJ1 Hsmp.
  replace (eval rho1 (reg_sv E_open 11)) with (Z_to_bv 64 A1).
  2:{ change (reg_sv E_open 11) with (SVar 25). cbn [eval]. symmetry. exact (proj2 HJ1). }
  apply (arg1_read_cstr_mm segs pcU phU sp draw inp Hsp Hinp Hargc2 rho1 (proj1 HJ1) (ss_objs E_open) ms
           (smatch_pending_mem segs _ _ _ _ _ Hsmp)).
  pose proof NU as N. fold A1. rewrite A1_eq. solve_disj HJ1.
Qed.

Definition Jop : jpred := ltac2:(tb__ "0|1|
S19S3S56A1M0S57S40S3fG0R2S1S56A1A3S93Vmd0;Sb1Vinp;A1S32R3P1aA2R1A4A2Lmd;Ltr;Lrho;").

Lemma L_open : ltac2:(tb__ "0|1|
S19S8aR1A1M0S74S3cVok;S52S3cS6eS1S56A1Vmd0;A2S7dR2A4S73S41S19S19S40G0S54S3cS8dS92S7aA1R1R2A5A2Lrho';A2Lw;A4F_;Frho;").
Proof using Hargc Hent Hinp HokK HokP.
  intros rho HJ.
  eapply (run_tr ok _ _ _ _ _ _ _ run_arg eq_refl (okf0 md0)).
  intros L rho1 [<-|[]] Hag. cbn [lf_state].
  assert (HJ1 : J25 rho1) by (eapply J25_agree; [exact Hag | cbn; lia | exact HJ]).
  apply triple1_triple.
  eapply triple1_conseq; [intros w Hw; exact Hw | |
    eapply (triple1_openatJ segs ok (liftK (Kx [] md0)) Jop E_open rho1);
      [ apply ok_frame_liftK; apply okf0
      | eapply ok_pframeJ_of_tcons; [apply HokP; intros tr0 md_ H0; exact H0 | intros r tr md Hk; exact (Ktc0 md0 tr md Hk)]
      | reflexivity | reflexivity | reflexivity | reflexivity | | ]].
  - intros w (rho' & Hag' & Hsp'). exists rho'. split; [|exact Hsp'].
    eapply J25_agree; [exact Hag' | cbn; lia | exact HJ1].
  -
    intros tr ms md Hsmp _. rewrite (E_open_cstr rho1 _ ms _ HJ1 Hsmp). exact arg1_cstr_no_slash.
  - intros tr ms md r md' Hsmp [-> ->] Hpost. split; [reflexivity|].
    rewrite E_open_next, rho_set_rw_at. rewrite (E_open_cstr rho1 _ ms _ HJ1 Hsmp) in Hpost. exact Hpost.
Qed.

Definition md_open : list byte -> Model := md_open_of md0.

Lemma after_open_cases : ltac2:(tb__ "0|1|
S19S73S54S3cS8dS92S7aA1R2R1A5S42S52S3cS6eS1S56A1M0Vmd0;A2S7eR3R2A5S40S97Vargv1;Vfs;A2S52S3cS6eG0S8bVargv1;A1A2S7fR3R2A5A2A2F_;Fw;Frho;").
Proof using A1 Hargc Hfds0 Hfs Hinp JI.
  rewrite <- Hfs. intros rho [tr [ms md]] [Hsm [Htr Hpost]]. cbn [w_tr w_cfg cfg_model fst snd] in Htr, Hpost. subst tr.
  change (arg1_cstr inp) with (cstr_of argv1) in Hpost.
  destruct (open_outcome_gen md0 Hfds0 argv1 Hndd1 _ _ Hpost) as [(e & He & Hr & ->)|(Hok & Hr & ->)].
  - left. split; [|split; reflexivity]. rewrite <- S_operr_eq. apply smatch_add_fact; [exact Hsm | reflexivity |].
    cbn [holds eval F_err]. unfold bv_ltu. change (eval rho (SVar 26)) with (rw rho 26). rewrite Hr.
    replace (bv_unsigned (Z_to_bv 64 18446744073709547520)) with 18446744073709547520 by (symmetry; apply Z_to_bv_small; rewrite mod64; lia).
    unfold errno_ret. rewrite Z_to_bv_unsigned. change (bv_wrap 64 (- e)) with ((- e) mod 2 ^ 64).
    rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
  - right. split; [exact Hok|]. split; [|split; reflexivity].
    eapply (smatch_restate segs rho (S_after_open E_open) S_opok); [exact Hsm | exact swf_S_opok | exact diff_opok | | constructor].
    constructor; [|constructor]. cbn [fst snd eval]. change (eval rho (SVar 26)) with (rw rho 26). rewrite Hr. reflexivity.
Qed.

Definition frame_data (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S41S9fS9fS40S78Q40M0A1S40S4cSa6S77G0R1A2M1A2S4dG1Sa5A2A2S3fS7S78Q8A1A1S3aVrho;R2A2Sa0R3R2A2A3F_;Fa;S40S38S3cVrho;R1S84A4S3bS3cR1A2A2A2LmsD;A2").

Record Jvars (rho : valuation) : Prop := mkJvars {
  jv_sp    : rw rho 1 = sp;
  jv_argc  : rw rho 2 = Z_to_bv 64 (Z.of_nat (length argv));
  jv_envc  : rw rho 3 = Z_to_bv 64 (Z.of_nat (length envp));
  jv_argv0 : rw rho 4 = Z_to_bv 64 (bv_unsigned sp + Z.of_nat (str_off argv envp));
  jv_len0  : rw rho 5 = Z_to_bv 64 (Z.of_nat (length argv0));
  jv_rand  : rw rho 6 = Z_to_bv 64 (bv_unsigned sp + Z.of_nat (rand_off argv envp));
  jv_rnd0  : rw rho 9 = rnd0 draw;
  jv_rnd1  : rw rho 10 = rnd1 draw;
  jv_arg1  : rw rho 25 = Z_to_bv 64 A1;
  jv_env   : rl rho 1 = env_bytes sp argv envp;
  jv_str0  : rl rho 2 = argv0 ++ [Z_to_bv 8 0];
  jv_mem   : forall a, ~ (dataU_lo <= bv_unsigned a < dataU_hi) -> rm rho a = ms_mem (ms0 segs pcU phU sp draw inp) a
}.

Definition JM (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S40S8eVrho;A1S8fVrho;A1A2").

Lemma JM_agree : ltac2:(tb__ "0|1|
S3eS19S19S26R3R2R1A3Sb5P1aR4A2S8cR4A1M0G0F_;F_;F_;Frho';Frho;Fn;").
Proof using Hargc.
  intros n rho rho' (Hw & Hl & Hm) Hn [HV (msD & HD1 & HD2 & HD3)]. split.
  - destruct HV; constructor; try (rewrite <- Hw by lia; assumption); try (rewrite <- Hl; assumption).
    intros a Ha. rewrite <- Hm. auto.
  - exists msD. split; [intros a Ha; rewrite <- Hm; auto|].
    assert (Hag : agree_below 26 rho rho') by (split; [intros i Hi; apply Hw; exact (Pos.lt_le_trans _ _ _ Hi Hn)| split; assumption]).
    split; [|exact HD3]. apply (obj_holds_agree segs 26 rho rho' msD O_dataM Hag); [reflexivity | exact HD2].
Qed.

Lemma L_ok : ltac2:(tb__ "0|1|
S19S8aR1A1S74S3cVok;S52S3cS6eS1S56A1S8bVargv1;A1A2M0S7fR2A4S73S41S19S19S40S8cR1A1S52S3cG0S7bR1R2A5A2Lrho';A2Lw;A4F_;Frho;").
Proof using Hargc Hent Hinp HokK.
  intros rho HJ.
  eapply (run_tr ok _ _ _ _ _ _ _ run_opok eq_refl (okf0 _)).
  intros L rho1 [<-|[]] Hag. cbn [lf_state].
  assert (HJ1 : J25 rho1) by (eapply J25_agree; [exact Hag | cbn; lia | exact HJ]).

  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros [tr [ms md]] [Hsm Hk].
  pose proof (smatch_xforms segs xs_M1 rho1 S_M1 S_M1x _ xs_M1_ok Hsm) as Hsm1.
  destruct (smatch_release_obj segs rho1 S_M1x (tr, mkCfg ms md) (ss_objs S_M) O_dataM (ss_next S_M) Hsm1 S_M1x_objs
              ltac:(rewrite <- S_M_eq; exact swf_S_M)) as (m' & Hsm' & Hout & Hin & Hoh & Hrom).
  cbn [w_cfg cfg_ms] in Hin, Hoh.
  exists (set_rm rho1 m'). split.
  - split.
    + pose proof HJ1 as [HJI H25]. destruct HJI; constructor; cbn [set_rm rw rl rm]; try assumption.
      intros a Ha. rewrite Hout; [auto|]. unfold in_rng.
      erewrite (shape_range rho1 HJ1 O_dataM) by reflexivity. cbn [fst snd]. unfold dataU_lo, dataU_hi in *. lia.
    + exists ms. split.
      * intros a Ha. cbn [set_rm rm]. apply Hin. unfold in_rng.
        erewrite (shape_range rho1 HJ1 O_dataM) by reflexivity. cbn [fst snd]. unfold dataU_lo, dataU_hi in *. lia.
      * split; [|exact Hrom]. apply (obj_holds_set_rm_ext segs rho1 m' ms ms O_dataM); [intros; reflexivity | intros; reflexivity | exact Hoh].
  - split; [|exact Hk]. rewrite <- S_M_eq. exact Hsm'.
Qed.

Theorem open_reach_safe : ltac2:(tb__ "0|3|
S19S8aR1A1S74S3cVok;S52S3cS6eS1S56A1M0Vmd0;A2M1S7eR2A4S73S43L_;M2A4F_;Frho;S97Vargv1;Vfs;A2S19S8cR1A1S74S3cVok;S52S3cS6eG0S8bVargv1;A1A2S7bR2A4G2A4F_;Frho;F_;S19VJI;R1A1S74S3cVok;S52S3cG1S96R2A4G2A4F_;Frho;F_;F_;").
Proof using Hargc Hent Hfds0 Hfs Hinp HokK HokP.
  intros Hco Hok rho HJ.
  apply (triple_from ok _ (fun rho' w => J25 rho' /\ SP segs (Kx [] md0) S_arg rho' w)).
  { intros w Hw. exists (rho_set_rw rho 25 (Z_to_bv 64 A1)). exact (arg_intro rho w HJ Hw). }
  intros rho1. apply triple_pure. intros HJ1.
  eapply triple_seq; [exact (L_open rho1 HJ1)|].
  apply triple_ex. intros rho2. apply triple_pure. intros HJ2.
  eapply triple_conseq; [intros w Hw; exact (after_open_cases rho2 w Hw) | intros w Hw; exact Hw |].
  apply triple_or.
  - exact (Hco rho2 HJ2).
  - apply triple_pure. intros Hmay.
    eapply triple_seq; [exact (L_ok rho2 HJ2)|].
    apply triple_ex. intros rho3. apply triple_pure. intros HJ3. exact (Hok Hmay rho3 HJ3).
Qed.

Lemma eL_open_err : ltac2:(tb__ "0|2|
S19S8aR1A1M0S75S3cS52S3cS6eS1S56A1Vmd0;A2M1S7dR2A4S73S41S19S19S40G0S52S3cG1S7eR1R2A5A2Lrho';A2Lw;A3F_;Frho;").
Proof using Hargc Hent Hinp.
  intros rho HJ.
  eapply (erun_tr _ _ _ _ _ _ _ run_arg eq_refl).
  intros L rho1 [<-|[]] Hag. cbn [lf_state].
  assert (HJ1 : J25 rho1) by (eapply J25_agree; [exact Hag | cbn; lia | exact HJ]).
  destruct (open_outcome_err_gen md0 argv1 Hndd1) as (e & He & Hpost).
  eapply etriple_conseq; [intros w Hw; exact Hw | |
    eapply (etriple_openatJ segs (liftK (Kx [] md0)) (fun r tr md => tr = [] /\ md = md0 /\ rw r 26 = errno_ret e) E_open rho1);
      [ reflexivity | reflexivity | reflexivity | reflexivity | ]].
  - intros w (rho' & Hag' & [Hsm (Htr & Hmd & Hr)]). exists rho'.
    split; [eapply J25_agree; [exact Hag' | cbn; lia | exact HJ1]|].
    split; [| split; [exact Htr | exact Hmd]].
    rewrite <- S_operr_eq. apply smatch_add_fact; [exact Hsm | reflexivity |].
    cbn [holds eval F_err]. unfold bv_ltu. change (eval rho' (SVar 26)) with (rw rho' 26). rewrite Hr.
    replace (bv_unsigned (Z_to_bv 64 18446744073709547520)) with 18446744073709547520 by (symmetry; apply Z_to_bv_small; rewrite mod64; lia).
    unfold errno_ret. rewrite Z_to_bv_unsigned. change (bv_wrap 64 (- e)) with ((- e) mod 2 ^ 64).
    rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
  - intros tr ms md Hsmp [-> ->]. rewrite (E_open_cstr rho1 _ ms _ HJ1 Hsmp).
    split; [exact arg1_cstr_no_slash|]. exists (errno_ret e), md0.
    rewrite E_open_next, rho_set_rw_at. split; [exact Hpost|repeat split; reflexivity].
Qed.

Lemma eL_open_ok : ltac2:(tb__ "0|2|
S97Vargv1;Vfs;A2S19S8aR1A1M0S75S3cS52S3cS6eS1S56A1M1Vmd0;A2S7dR2A4S73S41S19S19S40G0S52S3cS6eG1S8bVargv1;A1A2S7fR1R2A5A2Lrho';A2Lw;A3F_;Frho;F_;").
Proof using Hargc Hent Hfds0 Hfs Hinp.
  intros Hmay rho HJ.
  eapply (erun_tr _ _ _ _ _ _ _ run_arg eq_refl).
  intros L rho1 [<-|[]] Hag. cbn [lf_state].
  assert (HJ1 : J25 rho1) by (eapply J25_agree; [exact Hag | cbn; lia | exact HJ]).
  pose proof (open_outcome_ok_gen md0 Hfds0 argv1 Hndd1 ltac:(rewrite Hfs; exact Hmay)) as Hpost.
  eapply etriple_conseq; [intros w Hw; exact Hw | |
    eapply (etriple_openatJ segs (liftK (Kx [] md0)) (fun r tr md => tr = [] /\ md = md_open argv1 /\ rw r 26 = Z_to_bv 64 3) E_open rho1);
      [ reflexivity | reflexivity | reflexivity | reflexivity | ]].
  - intros w (rho' & Hag' & [Hsm (Htr & Hmd & Hr)]). exists rho'.
    split; [eapply J25_agree; [exact Hag' | cbn; lia | exact HJ1]|].
    split; [| split; [exact Htr | exact Hmd]].
    eapply (smatch_restate segs rho' (S_after_open E_open) S_opok); [exact Hsm | exact swf_S_opok | exact diff_opok | | constructor].
    constructor; [|constructor]. cbn [fst snd eval]. change (eval rho' (SVar 26)) with (rw rho' 26). rewrite Hr. reflexivity.
  - intros tr ms md Hsmp [-> ->]. rewrite (E_open_cstr rho1 _ ms _ HJ1 Hsmp).
    split; [exact arg1_cstr_no_slash|]. exists (Z_to_bv 64 3), (md_open argv1).
    rewrite E_open_next, rho_set_rw_at. split; [exact Hpost|repeat split; reflexivity].
Qed.

Lemma eL_ok : ltac2:(tb__ "0|1|
S19S8aR1A1S75S3cS52S3cS6eS1S56A1S8bVargv1;A1A2M0S7fR2A4S73S41S19S19S40S8cR1A1S52S3cG0S7bR1R2A5A2Lrho';A2Lw;A3F_;Frho;").
Proof using Hargc Hent Hinp.
  intros rho HJ.
  eapply (erun_tr _ _ _ _ _ _ _ run_opok eq_refl).
  intros L rho1 [<-|[]] Hag. cbn [lf_state].
  assert (HJ1 : J25 rho1) by (eapply J25_agree; [exact Hag | cbn; lia | exact HJ]).
  intros [tr [ms md]] [Hsm Hk]. eexists. split; [apply wsteps_refl|].
  pose proof (smatch_xforms segs xs_M1 rho1 S_M1 S_M1x _ xs_M1_ok Hsm) as Hsm1.
  destruct (smatch_release_obj segs rho1 S_M1x (tr, mkCfg ms md) (ss_objs S_M) O_dataM (ss_next S_M) Hsm1 S_M1x_objs
              ltac:(rewrite <- S_M_eq; exact swf_S_M)) as (m' & Hsm' & Hout & Hin & Hoh & Hrom).
  cbn [w_cfg cfg_ms] in Hin, Hoh.
  exists (set_rm rho1 m'). split.
  - split.
    + pose proof HJ1 as [HJI H25]. destruct HJI; constructor; cbn [set_rm rw rl rm]; try assumption.
      intros a Ha. rewrite Hout; [auto|]. unfold in_rng.
      erewrite (shape_range rho1 HJ1 O_dataM) by reflexivity. cbn [fst snd]. unfold dataU_lo, dataU_hi in *. lia.
    + exists ms. split.
      * intros a Ha. cbn [set_rm rm]. apply Hin. unfold in_rng.
        erewrite (shape_range rho1 HJ1 O_dataM) by reflexivity. cbn [fst snd]. unfold dataU_lo, dataU_hi in *. lia.
      * split; [|exact Hrom]. apply (obj_holds_set_rm_ext segs rho1 m' ms ms O_dataM); [intros; reflexivity | intros; reflexivity | exact Hoh].
  - split; [|exact Hk]. rewrite <- S_M_eq. exact Hsm'.
Qed.

Theorem copen_reach_exists : ltac2:(tb__ "0|1|
S73OF_;S19S8aR1A1S75S3cS52S3cS6eS1S56A1Vmd0;A2M0S7eR2A4R3A3F_;Frho;S19VJI;R1A1S75S3cS52S3cG0S96R2A4R4A3F_;Frho;F_;FQ;").
Proof using Hargc Hent Hinp.
  intros Q Hco rho HJ.
  apply (etriple_from _ (fun rho' w => J25 rho' /\ SP segs (Kx [] md0) S_arg rho' w)).
  { intros w Hw. exists (rho_set_rw rho 25 (Z_to_bv 64 A1)). exact (arg_intro rho w HJ Hw). }
  intros rho1. apply etriple_pure. intros HJ1.
  eapply etriple_seq; [exact (eL_open_err rho1 HJ1)|].
  apply etriple_ex. intros rho2. apply etriple_pure. intros HJ2. exact (Hco rho2 HJ2).
Qed.

Theorem open_reach_exists : ltac2:(tb__ "0|1|
S97Vargv1;Vfs;A2S73OF_;S19S8cR1A1S75S3cS52S3cS6eS1S56A1M0S8bVargv1;A1A2S7bR2A4R3A3F_;Frho;S19VJI;R1A1S75S3cS52S3cS6eG0Vmd0;A2S96R2A4R4A3F_;Frho;F_;FQ;F_;").
Proof using Hargc Hent Hfds0 Hfs Hinp.
  intros Hmay Q Hok rho HJ.
  apply (etriple_from _ (fun rho' w => J25 rho' /\ SP segs (Kx [] md0) S_arg rho' w)).
  { intros w Hw. exists (rho_set_rw rho 25 (Z_to_bv 64 A1)). exact (arg_intro rho w HJ Hw). }
  intros rho1. apply etriple_pure. intros HJ1.
  eapply etriple_seq; [exact (eL_open_ok Hmay rho1 HJ1)|].
  apply etriple_ex. intros rho2. apply etriple_pure. intros HJ2.
  eapply etriple_seq; [exact (eL_ok rho2 HJ2)|].
  apply etriple_ex. intros rho3. apply etriple_pure. intros HJ3. exact (Hok rho3 HJ3).
Qed.
End Open.
End Drv_open.
