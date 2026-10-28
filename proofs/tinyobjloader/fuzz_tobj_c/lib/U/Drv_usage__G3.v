(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "False"; "not"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "valuation"; "reg_sv"; "cell"; "SAlu"; "sobj"; "mkCell"; "SVar"; "sprop"; "sstate"; "ss_objs"; "ob_cells"; "ss_next"; "SPUle"; "ss_facts"; "ss_pc"; "eval"; "agree_below"; "rw"; "holds"; "obj_wf"; "rd_bytes"; "DList"; "mkObj"; "ob_dflt"; "rl"; "dflt_writable"; "is_arr"; "ob_hi"; "ob_lo"; "swf"; "obj_holds"; "ss_lenient"; "SPBranch"; "sprop_below"; "sv_eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "length"; "false"; "nat"; "Some"; "cons"; "option"; "pair"; "nil"; "prod"; "app"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_add"; "@Corelib.Init.Peano"; "le"; "lt"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "read_bytes_map"; "FdChannel"; "fd_lookup"; "in_fs"; "m_fds"; "m_fs"; "read_u64"; "WriteEv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "ok_frame"; "LQ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G3.Drv_usage"; "Kx"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G3.Drv_usage.Usage"; "TR"; "Good"; "MSG"; "ob0"; "M1"; "ob1"; "GoodM"; "GoodW"; "M2"; "Q_at"; "QD1"; "QDm"; "QM_at"; "BL_input"; "BL_usage"; "L0'"; "L0_of"; "L0g"; "L0m"; "OB_ibuf2"; "QD2"; "QDg"; "QW_at"; "R_of"; "sub_id7"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "cell_eqb"; "entails"; "@Stdlib.Lists.List"; "existsb"; "In"; "nth_error"; "forallb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "BLit"; "beval"; "cells_bytes"; "bexp_eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "instr"; "Ecall"; "ALU_SUB"; "BC_LTU"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "opp"; "lt"; "sub"; "pow"; "to_nat"; "mul"; "modulo"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "etriple"; "w_tr"; "assn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "instr_at"; "sym_run"; "lf_state"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_mid_states"; "E_Mg"; "CB2m"; "CB1m"; "E_Zm"; "check_core_m"; "RO_INPUT"; "BLm"; "Dm"; "E_exitm"; "GLm"; "xs_ibuf2"; "check_range_m"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_small_states"; "Tn"; "E_Wg"; "CBg"; "FUELn"; "check_core"; "Dg"; "E_exitg"; "sub_ok_n"; "BLn"; "BNZ3"; "GLg"; "check_range"; "xs_ibuf"; "@Corelib.Init.Nat"; "add"; "sub"; "@Corelib.Lists.ListDef"; "skipn"; "map"; "firstn"; "nth"; "seq"; "Forall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_states"; "E_A1"; "E_A2"; "CB1"; "CB2"; "CB3"; "E_exit"; "S_use"; "D1"; "D2"; "E_sn"; "R_sn"; "T_imp"; "T_sn1"; "T_sn74"; "X_ovf"; "s_sn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "obj_rng"; "list_eqb"; "S_after_write"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "STK_FREE"; "Jinit"; "@Stdlib.Strings.Ascii"; "Ascii"; "@Stdlib.Strings.String"; "String"; "EmptyString";
"@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_read_byte"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "wr"; "ex"; "msg_usage"; "Spec"; "str"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "mkEntry"; "is_prefix"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "smatch_pending"; "ok_pframe"; "state_has_rl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates"; "S_main"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs"; "strs_tail"; "O_strs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "K_tcons"; "ok_halted"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "rho_absorb"; "wsub_get"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "add_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "apply_xforms"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init"; "pcU"; "phU"; "imgU"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "tab"; "valid_entry48"; "img_len"; "pad_len"; "str_off"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memchr"; "FirstNul"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require Stdlib.Strings.Ascii.
Require Stdlib.Strings.String.
Require stdpp.bitvector.bitvector.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase.
Require LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Require LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Require LinuxProcessSemantics.LinuxProcessSem.Fs.
Require LinuxProcessSemantics.LinuxProcessSem.State.
Require LinuxProcessSemantics.LinuxProcessSem.Specs.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Require LinuxProcessSemantics.Riscv.Prelude.
Require LinuxProcessSemantics.Riscv.Instr.
Require LinuxProcessSemantics.Riscv.Decode.
Require LinuxProcessSemantics.Riscv.DecodeC.
Require LinuxProcessSemantics.Riscv.Sem.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memchr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_strnlen.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Drv_usage.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import Stdlib.Strings.Ascii Stdlib.Strings.String.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memchr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_strnlen OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_small_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_mid_states.

Import ListNotations.
Import StrAddr. Import UAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.

Local Ltac lia := slia.
Local Ltac nia := snia.

Definition Kx (t : list event) (m : Model) (tr : list event) (md : Model) : Prop := ltac2:(tb__ "0|0|
S1S0S2dS40A1Vtr;Vt;A3S0S41Vmd;Vm;A3A2").

Section Generic.
Variable ok : world -> Prop.

Lemma LQ_elim : ltac2:(tb__ "0|0|
S2dS40A1S41OF_;F_;S3fS7S2dS87A1S86S87S7S6bS87R2R4A3S17R7R6R2A3S83S2aVok;S4bS2aR9S8aR4A1R3A4R5A4F_;F_;Frho';FL;S83S2aVok;S4dS2aR6R5R4R3A5R2A4F_;FQ;Fleaves;Frho;Fn;FK;").
Proof using .
  intros K n rho leaves Q H. unfold LQ, LQJ.
  apply triple_ex; intros L. apply triple_ex; intros rho'.
  apply triple_pure; intros Hin. apply triple_pure; intros Hag.
  eapply triple_conseq; [| intros w Hw; exact Hw | exact (H L rho' Hin Hag)].
  intros w [Hsm Hk]. split; assumption.
Qed.

Lemma run_tr : ltac2:(tb__ "0|1|
S30S2dS3eA1SfS2dS87A1M0S2dS40A1S41OF_;F_;S7S86S0S33G0A1S89S2aR7R6R5S2bA5S31G0R4A2A3S0S2cS26R6A1S2fA3S4cS2aVok;R5A3S87S7S6bS87R2R9A3S17S12RbA1R8R2A3S83S2aVok;S4bS2aRaS8aR4A1R3A4R8A4F_;F_;Frho';FL;S83S2aVok;S4bS2aR7R9R6A4R5A4F_;F_;F_;F_;FQ;Frho;FK;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves K rho Q Hrun Hstrict Hok H.
  eapply triple_seq; [apply triple1_triple; eapply sym_run_sound; [exact Hrun | exact Hok | rewrite Hstrict; discriminate]|].
  apply LQ_elim. exact H.
Qed.

Lemma eLQ_elim : ltac2:(tb__ "0|0|
S2dS40A1S41OF_;F_;S3fS7S2dS87A1S82OF_;S87S7S6bS87R2R4A3S17R7R6R2A3S84S2aS4bS2aR9S8aR4A1R3A4R5A3F_;F_;Frho';FL;S84S2aS4dS2aR6R5R4R3A5R2A3F_;FQ;Fleaves;Frho;Fn;FK;").
Proof using .
  intros K n rho leaves Q H. unfold LQ, LQJ.
  apply etriple_ex; intros L. apply etriple_ex; intros rho'.
  intros w (Hin & Hag & Hsm & Hk). apply (H L rho' Hin Hag). split; assumption.
Qed.

Lemma erun_tr : ltac2:(tb__ "0|1|
S30S2dS3eA1SfS2dS87A1M0S2dS40A1S41OF_;F_;S7S82OF_;S0S33G0A1S89S2aR7R6R5S2bA5S31G0R4A2A3S0S2cS26R6A1S2fA3S87S7S6bS87R2R8A3S17S12RaA1R7R2A3S84S2aS4bS2aR9S8aR4A1R3A4R7A3F_;F_;Frho';FL;S84S2aS4bS2aR6R8R5A4R4A3F_;F_;F_;FQ;Frho;FK;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves K rho Q Hrun Hstrict H w Hsp.
  destruct (sym_run_complete segs fuel cuts S leaves K rho w Hstrict Hrun Hsp) as (L & rho' & w' & Hin & Hst & Hag & Hsp').
  destruct (H L rho' Hin Hag w' Hsp') as (w'' & Hst' & HQ).
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.
End Generic.

Lemma ok_frame_mono : ltac2:(tb__ "0|2|
S82OF_;S2dS40A1M0S41OF_;F_;M1G1G0S41R3R2R1A2R5R3R2A2F_;Fmd;Ftr;S4cS2aR4R3A3S4cS2aR5R3A3F_;F_;FK';FK;Fok;").
Proof. intros ok K K' HK H tr ms md ms' Hk. apply H. apply HK. exact Hk. Qed.
Lemma ok_pframe_mono : ltac2:(tb__ "0|2|
S82OF_;S2dS40A1M0S41OF_;F_;M1G1G0S41R3R2R1A2R5R3R2A2F_;Fmd;Ftr;Sd0S2aR4R3A3Sd0S2aR5R3A3F_;F_;FK';FK;Fok;").
Proof. intros ok K K' HK H tr ms md x8 Hk. apply H. apply HK. exact Hk. Qed.

Lemma SP_entails : ltac2:(tb__ "0|0|
S2dS40A1S41OF_;F_;SfSfSd8S7S82S0S2cS69R5R4R3A3S2bA3S4bS2aR7R6R3R2A5S4bS2aR8R6Sd7R4R5A2R3A5F_;F_;Fw;Frho;Fs;FT;FL;FK;").
Proof. intros K L T s rho w He [Hsm Hk]. split; [eapply entails_sound; eauto | exact Hk]. Qed.

Lemma SP_fact : ltac2:(tb__ "0|0|
S2dS40A1S41OF_;F_;SfS7S82SeS4bS2aR5R4R3R2A5S6bSeR2S14R5A1A3S19R5R3A2F_;F_;Fp;Fw;Frho;FS;FK;").
Proof. intros K S rho w p Hsp Hin. exact (proj1 (Forall_forall _ _) (SP_facts_hold segs K rho S w Hsp) p Hin). Qed.

Lemma U_lit64 : ltac2:(tb__ "0|0|
S7S3eS1S79Z0R1A2S7cR1S7eZ2Z40A2A2A2S0S3eS39Q40S16R3S6R2A1A2A2R2A3F_;Fz;Frho;").
Proof. intros. cbn [eval]. apply Z_to_bv_small. rewrite mod64. assumption. Qed.
Lemma U_addc : ltac2:(tb__ "0|3|
S7S5S3eS3eS0S3eS39Q40M0S16R4R3A2A2R1A3S1S79Z0S78R2R3A2M1A2S7cG1S7eZ2Z40A2M2A2A2S1S7cS7bG2A1R4A2S7cR4G2A2A2S0S3eS39G0S16R7SaS73R6S6R5A1A3A2A2S78R4R5A2A3F_;F_;F_;Fx;Fc;Fe;Frho;").
Proof.
  intros rho e c x Hx Hb Hc. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned, Hx.
  unfold bv_wrap. rewrite mod64. rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.
Lemma U_add2 : ltac2:(tb__ "0|2|
S7S5S5S3eS3eS0S3eS39Q40M0S16R5R4A2A2R2A3S0S3eS39G0S16R6R4A2A2R2A3S1S79Z0S78R4R3A2M1A2S7cG1S7eZ2Z40A2A2A2S0S3eS39G0S16R8SaS73R7R6A3A2A2S78R5R4A2A3F_;F_;F_;Fy;Fx;Fb;Fa;Frho;").
Proof.
  intros rho a b x y Hx Hy Hb. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Hx, Hy.
  unfold bv_wrap. rewrite mod64. apply Z.mod_small. pose proof (urange (eval rho a)). pose proof (urange (eval rho b)). lia.
Qed.
Lemma U_sub2 : ltac2:(tb__ "0|1|
S7S5S5S3eS3eS0S3eS39Q40M0S16R5R4A2A2R2A3S0S3eS39G0S16R6R4A2A2R2A3S79Z0S7dR4R3A2A2S0S3eS39G0S16R8SaS76R7R6A3A2A2S7dR5R4A2A3F_;F_;F_;Fy;Fx;Fb;Fa;Frho;").
Proof.
  intros rho a b x y Hx Hy Hb. cbn [eval]. unfold alu64, alu. rewrite bv_sub_unsigned, Hx, Hy.
  unfold bv_wrap. rewrite mod64. apply Z.mod_small. pose proof (urange (eval rho a)). pose proof (urange (eval rho b)). lia.
Qed.
Lemma bvw_add : ltac2:(tb__ "0|1|
S38Q40M0A1S3eS0S3eS39G0S3bG0R2S3aG0R1A2A3A2S81S78S39G0R2A2R1A2S7eZ2Z40A2A2A3Fz;Fa;").
Proof. intros a z. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. rewrite mod64. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

Lemma rd_bytes_skip : ltac2:(tb__ "0|4|
Sc4S30S38Q40M0A1S30S2dS38Q8A1M1A1M2S0S33G2A1M3S1bR5R3Sa4R4R2A2A3S31G2R1A2A3S0G3S1bR6S3bG0R4S3aG0S7aR5A1A2A3R3A3S31G2Sa6G1R5R2A3A2A3F_;Fbs;Fn;Fa;Fc;Fms;").
Proof.
  intros ms c. induction c as [|c IH]; intros a n bs H.
  - cbn [Nat.add] in H. cbn [skipn]. replace (a + Z_to_bv 64 (Z.of_nat 0))%bv with a; [exact H|].
    apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. cbn [Z.of_nat]. unfold bv_wrap. rewrite mod64.
    rewrite Z.mod_0_l, Z.add_0_r by lia. symmetry. apply Z.mod_small. pose proof (urange a). lia.
  - cbn [rd_bytes Nat.add] in H. destruct (rd ms a) as [b|]; [|discriminate].
    destruct (rd_bytes ms (a + 1)%bv (c + n)) as [r|] eqn:E; [|discriminate]. inversion H; subst. cbn [skipn].
    rewrite <- (IH (a + 1)%bv n r E). f_equal. apply bv_eq. rewrite !bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_unsigned (1%bv : bv 64)) with 1. rewrite Nat2Z.inj_succ, two64.
    rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l, Zplus_mod_idemp_r. f_equal. lia.
Qed.

Lemma read_bytes_map_of_rd : ltac2:(tb__ "0|4|
Sc4S38Q40M0A1M1G1S30S2dS38Q8A1A1M2S0S3eS39G0R3A2S7aR2A1A3S0S33G2A1M3S1bR6R5R3A3S31G2R2A2A3S0G3S43Sc5R7A1R6R5A3S31G2R3A2A3F_;F_;Fbs;Fn;Flen;Fa;Fms;").
Proof.
  intros ms a len n bs Hlen H. rewrite read_bytes_map_eq; unfold word_to_nat. rewrite rd_bytes_read_aux, Hlen, Nat2Z.id. exact H.
Qed.

Section Usage.
Variable sp brk mb : word.
Variable draw : EntryDraw.
Variable lim : Z.
Variable inp : ProcInput.
Hypothesis Hent : ltac2:(tb__ "0|0|
Se5Se1ScdVsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Let argv := in_argv inp.
Let envp := in_envp inp.
Let argv0 : list byte := nth 0 argv [].
Let fs := in_fs inp.
Hypothesis Hargc : length argv <> 2%nat.

Variable md0 : Model.
Hypothesis Hfd2 : ltac2:(tb__ "0|1|
S0S33S42A1S45S47Vmd0;A1S3aQ40Z2A2M0A2S31S42S44G0A1A2A3").
Hypothesis Hfs : ltac2:(tb__ "0|0|
S0Se3S48Vmd0;A1Vfs;A3").
Variable ok : world -> Prop.
Let SpecT : list event -> Prop := Spec inp.
Hypothesis HokK : ltac2:(tb__ "0|0|
S2dS40A1S41OF_;F_;Sd5VSpecT;R1A2S4cS2aVok;R2A3F_;FK;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S2dS40A1S41OF_;F_;Sd5VSpecT;R1A2Sd0S2aVok;R2A3F_;FK;").
Hypothesis Hokh : ok_halted ok SpecT.

Lemma Hsp : valid_sp sp. Proof using Hent. exact (proj1 Hent). Qed.
Let JI : ltac2:(tb__ "0|0|
S7OFrho;") := ltac2:(tb__ "0|0|
Sc0S2aSdfSe0Vsp;Vdraw;Vinp;A6").
Let STR : ltac2:(tb__ "0|0|
S3e") := ltac2:(tb__ "0|0|
S7aSe8Vargv;Venvp;A2A1").
Let LEN : ltac2:(tb__ "0|0|
S3e") := ltac2:(tb__ "0|0|
S7aSe6Vargv;Venvp;A2A1").
Let N0 := Z.of_nat (length argv0).

Definition M1 : list byte := str "usage: " ++ argv0.
Definition M2 : list byte := line " INPUT".
Definition MSG : list byte := M1 ++ M2.
Definition TR (n : nat) : list event := wr 2 (firstn n MSG).

Lemma M1_len : ltac2:(tb__ "0|1|
S0S30S2eS38Q8A1M0S53A2Sa4U7S2eG0Vargv0;A2A2A3").
Proof using . unfold M1. rewrite length_app. reflexivity. Qed.
Lemma M2_len : length M2 = 7%nat.
Proof using . reflexivity. Qed.
Lemma MSG_len : ltac2:(tb__ "0|1|
S0S30S2eS38Q8A1M0S51A2Sa4UeS2eG0Vargv0;A2A2A3").
Proof using Hargc. unfold MSG. rewrite length_app, M1_len, M2_len. lia. Qed.
Lemma MSG_usage : ltac2:(tb__ "0|0|
S0S2dS38Q8A1A1S51Sc8Vargv0;A1A3").
Proof using . unfold MSG, M1, M2, msg_usage. rewrite <- app_assoc. reflexivity. Qed.

Lemma final_in_spec : ltac2:(tb__ "0|1|
VSpecT;S37S40Sc6Z2M0S51A2S32S40Sc7Vfs;G0A2S35S40A1A3A3A1").
Proof using Hargc.
  unfold SpecT, Spec, spec_traces.
  destruct (Nat.eqb_spec (length (in_argv inp)) 2) as [E|NE]; [exfalso; exact (Hargc E)|]. cbn [negb].
  left. rewrite MSG_usage. replace (hd [] (in_argv inp)) with argv0 by (unfold argv0, argv; destruct (in_argv inp); reflexivity).
  reflexivity.
Qed.

Lemma wr_firstn_prefix : ltac2:(tb__ "0|1|
S30SceS40S4fR1A1S37S40Sc6Z2M0S51A2S32S40Sc7Vfs;G0A2S35S40A1A3A3A3Fn;").
Proof using .
  intros n. unfold TR, wr.
  replace (map (WriteEv (Z_to_bv 64 2)) MSG ++ [ex fs 2])
    with (map (WriteEv (Z_to_bv 64 2)) (firstn n MSG) ++ (map (WriteEv (Z_to_bv 64 2)) (skipn n MSG) ++ [ex fs 2]))
    by (rewrite app_assoc, <- map_app, firstn_skipn; reflexivity).
  apply is_prefix_app.
Qed.

Lemma Ktc : ltac2:(tb__ "0|0|
S30Sd5VSpecT;S4eS4fR1A1Vmd0;A2A2Fn;").
Proof using Hargc. intros n tr md [-> ->]. exists (wr 2 MSG ++ [ex fs 2]). split; [apply final_in_spec | apply wr_firstn_prefix]. Qed.
Lemma okf : ltac2:(tb__ "0|0|
S30S4cS2aVok;S4eS4fR1A1Vmd0;A2A3Fn;"). Proof using Hargc HokK. intros n. apply HokK, Ktc. Qed.
Lemma okp : ltac2:(tb__ "0|0|
S30Sd0S2aVok;S4eS4fR1A1Vmd0;A2A3Fn;"). Proof using Hargc HokP. intros n. apply HokP, Ktc. Qed.
Lemma TR0 : TR 0 = []. Proof using . reflexivity. Qed.
Lemma TR_all : ltac2:(tb__ "0|0|
S30S3cS2eS38Q8A1S51A2R1A2S0S2dS40A1S4fR2A1Sc6Z2S51A2A3F_;Fn;").
Proof using Hargc. intros n Hn. unfold TR. rewrite firstn_all2 by lia. reflexivity. Qed.
Lemma firstn_add_skipn : forall {A} (l : list A) n k, firstn n l ++ firstn k (skipn n l) = firstn (n + k) l.
Proof using .
  intros A l n. revert l. induction n as [|n IH]; intros l k; [reflexivity|].
  destruct l as [|x l]; cbn; [rewrite firstn_nil; reflexivity|]. f_equal. apply IH.
Qed.
Lemma TR_app : ltac2:(tb__ "0|1|
S30S30S0S2dS40A1S37S40S4fR2A1Sa7S38Q8A1M0S40S4aS3aQ40Z2A2A1Sa8G0R1Sa6G0R2S51A3A3A4A3S4fSa4R2R1A2A1A3Fk;Fn;").
Proof using . intros n k. unfold TR, wr. rewrite <- map_app, firstn_add_skipn. reflexivity. Qed.

Lemma NU : ltac2:(tb__ "0|a|
S1S1S79Z7fff80000000S39Q40Vsp;A2M0A2S79G0Z800000000000M1A2A2S1S0S3eVSTR;S78S78Zb8S80Z8M2S7aS2eS2dS38Q8A1A1M3Vargv;A2A1M4A2A2S80G2S7aS2eG3Venvp;A2A1M5A2A2A3S1S79S78VN0;Z1M6A2S7aSe4Vargv;A1A1M7A2S1S79VN0;Z1ffffA2S1S0S3eVLEN;S78S78S78S78VSTR;G7A2S7aSe4Venvp;A1A1M8A2S7aSe7Vargv;Venvp;A2A1M9A2Z10A2A3S1S79G7Z200000A2S1S79G8Z20000A2S1S7cG9G2A2S1S1S79G6G4A2S79G4Z400A2A2S1S79G5Z100A2S79S78G0VLEN;A2G1A2A2A2A2A2A2A2A2A2A2A2").
Proof using Hargc Hent Hinp argv0.
  pose proof (NUMS sp inp Hsp Hinp) as X. pose proof (LEN_fit sp inp Hinp (proj2 (proj2 (proj2 Hent)))) as F.
  rewrite sp_hi_val in F. unfold STR, LEN, N0, argv0, argv, envp in *. lia.
Qed.

Definition Good (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S1VJI;Vrho;A1S1S0S2dS38Q8A1A1S1fVrho;P3A2Sd3Vdraw;Vinp;A2A3S0S3eS39Q40S18Vrho;P19A2A2S7dVLEN;VSTR;A2A3A2A2").

Lemma Good_agree : ltac2:(tb__ "0|1|
S3fS7S7S17R3R2R1A3Se2P1aR4A2S50R4A1M0G0F_;F_;F_;Frho';Frho;Fn;").
Proof using Hargc.
  intros n rho rho' (Hw & Hl & Hm) Hn (HJ & H3 & H25). split; [|split].
  - destruct HJ; constructor; rewrite <- ?Hw by lia; auto. + rewrite <- Hl; auto. + rewrite <- Hl; auto. + intros a. rewrite <- Hm. auto.
  - rewrite <- Hl. exact H3.
  - rewrite <- Hw by lia. exact H25.
Qed.

Definition sub_id7 (s : wsub) : bool := ltac2:(tb__ "0|0|
S6dS3fS3fS29SdaVs;R1A2SdR1A1A2Li;S32S3fP1S32S3fP2S32S3fP3S32S3fP4S32S3fP5S32S3fP6S32S3fP7S32S3fP8S32S3fP9S32S3fPaS32S3fP19S35S3fA1A3A3A3A3A3A3A3A3A3A3A3A3").

Lemma Good_sub : ltac2:(tb__ "0|0|
Sd8S7S0S2cS67R2A1S2bA3S50R2A1S50Sd7R3R4A2A1F_;F_;Frho;Fs;").
Proof using .
  intros s rho Hs (HJ & H3 & H25). unfold sub_id7 in Hs. cbn [forallb] in Hs.
  apply andb_prop in Hs as [E1 Hs]. apply andb_prop in Hs as [E2 Hs]. apply andb_prop in Hs as [E3 Hs].
  apply andb_prop in Hs as [E4 Hs]. apply andb_prop in Hs as [E5 Hs]. apply andb_prop in Hs as [E6 Hs].
  apply andb_prop in Hs as [E8 Hs]. apply andb_prop in Hs as [E9 Hs]. apply andb_prop in Hs as [E10 Hs]. apply andb_prop in Hs as [E11 Hs].
  apply andb_prop in Hs as [E7 _].
  apply sv_eqb_sound in E1. apply sv_eqb_sound in E2. apply sv_eqb_sound in E3.
  apply sv_eqb_sound in E4. apply sv_eqb_sound in E5. apply sv_eqb_sound in E6. apply sv_eqb_sound in E7.
  apply sv_eqb_sound in E8. apply sv_eqb_sound in E9. apply sv_eqb_sound in E10. apply sv_eqb_sound in E11.
  split; [|split; [exact H3 | cbn [rho_sub rw]; rewrite E7; cbn [eval]; exact H25]].
  destruct HJ; constructor; cbn [rho_sub rw rl rm]; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E8, ?E9, ?E10, ?E11; cbn [eval]; auto.
Qed.

Lemma G_v1 : ltac2:(tb__ "0|1|
S7S50R1A1S0S3eS39Q40M0S18R2P1A2A2S39G0Vsp;A2A3F_;Frho;").
Proof using . intros rho [[H _ _ _ _ _ _ _ _] _]. rewrite H. reflexivity. Qed.
Lemma G_v25 : ltac2:(tb__ "0|0|
S7S50R1A1S0S3eS39Q40S18R2P19A2A2S7dVLEN;VSTR;A2A3F_;Frho;").
Proof using . intros rho (_ & _ & H). exact H. Qed.
Lemma G_v4 : ltac2:(tb__ "0|1|
S7S50R1A1S0S3eS39Q40M0S18R2P4A2A2S78S39G0Vsp;A2VSTR;A2A3F_;Frho;").
Proof using Hargc Hent Hinp. intros rho [HJ _]. pose proof NU. rewrite (ji_argv0 _ _ _ _ _ _ _ HJ). apply Z_to_bv_small. rewrite mod64. unfold STR, argv, envp in *. lia. Qed.
Lemma G_v5 : ltac2:(tb__ "0|0|
S7S50R1A1S0S3eS39Q40S18R2P5A2A2VN0;A3F_;Frho;").
Proof using Hargc Hent Hinp. intros rho [HJ _]. pose proof NU. rewrite (ji_len0 _ _ _ _ _ _ _ HJ). apply Z_to_bv_small. rewrite mod64. unfold N0, argv0, argv in *. lia. Qed.
Lemma G_rl3 : ltac2:(tb__ "0|0|
S7S50R1A1S0S2dS38Q8A1A1S1fR2P3A2Sd3Vdraw;Vinp;A2A3F_;Frho;").
Proof using . intros rho (_ & H & _). exact H. Qed.

Lemma tail_firstn : ltac2:(tb__ "0|1|
S0S2dS38Q8A1M0A1Sa8G0S2eG0Vargv0;A2Sd3Vdraw;Vinp;A2A3Vargv0;A3").
Proof using Hargc Hent Hinp.
  pose proof NU as X. unfold strs_tail. unfold N0, argv0, argv in *.
  destruct (in_argv inp) as [|a r] eqn:Ea; [cbn in X; lia|]. cbn [nth].
  rewrite flatten_strings_cons, <- !app_assoc. rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.
Lemma tail_nul : ltac2:(tb__ "0|3|
S0S38Q8M0A1M1Sa9G1S2eG1Vargv0;A2Sd3Vdraw;Vinp;A2S3aG0Z0A2M2A4G2A3").
Proof using Hargc Hent Hinp.
  unfold argv0, argv. rewrite (tail_nth_str0 sp draw inp Hsp Hinp (length (nth 0 (in_argv inp) []))) by lia.
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma argv0_nonul : ltac2:(tb__ "0|3|
S30S3dR1S2eS38Q8M0A1M1Vargv0;A2A2S4S0G1Sa9G1R2Vargv0;S3aG0Z0A2M2A4G2A3A1F_;Fj;").
Proof using Hargc Hinp envp.
  intros j Hj E. pose proof (proj1 Hinp) as (_ & _ & _ & Hnn & _). unfold argv0, argv in *.
  destruct (in_argv inp) as [|a r]; [cbn in Hj; lia|]. cbn [nth] in *.
  apply Forall_cons_iff in Hnn as [Ha _]. apply Ha. rewrite <- E. apply nth_In. exact Hj.
Qed.
Lemma tail_len : ltac2:(tb__ "0|0|
S0S3eS7aS2eS38Q8A1Sd3Vdraw;Vinp;A2A2A1S7dVLEN;VSTR;A2A3").
Proof using . exact (length_tail draw inp). Qed.

Lemma use_intro : ltac2:(tb__ "0|1|
S7S82VJI;R2A1S4bS2aS4eS4fU0A1Vmd0;A2M0Sd2R3R2A5S2S7S7S1S50R1A1S4bS2aG0Sb2R1R4A5A2Lrho';A2F_;F_;Fw;Frho;").
Proof using Hargc Hent Hinp.
  intros rho [tr [ms md]] HJ [Hsm Hk].
  pose proof NU as NU'. pose proof (LEN_bound inp Hinp) as HLEN.
  destruct (recarve_strs segs pcU phU dataU_lo dataU_hi dataU_ok ltac:(unfold dataU_hi; lia)
              ltac:(change segs with segsU; rewrite segs_topU; lia) sp draw inp Hsp Hinp
              rho S_main tr ms md (obj_main 0) (obj_main 1) (obj_main 2) (obj_main 3) (obj_main 6) 25 3
              Hsm HJ eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
              ltac:(discriminate) ltac:(discriminate) ltac:(cbv; discriminate) ltac:(cbv; discriminate) eq_refl)
    as (Hsm' & HJ' & Hrl3 & Hrw25 & _).
  set (rho' := rho_set_rw _ _ _) in *.
  assert (V25 : bv_unsigned (rw rho' 25) = LEN - STR) by (rewrite Hrw25; apply Z_to_bv_small; rewrite mod64; lia).
  assert (G' : Good rho') by (split; [exact HJ'|split; [exact Hrl3|exact V25]]).
  exists rho'. split; [exact G'|].
  split; [|exact Hk]. rewrite <- S_use_eq. apply smatch_add_facts; [exact Hsm' | | reflexivity].
  pose proof (G_v5 rho' G') as V5.
  assert (V2 : bv_unsigned (rw rho' 2) = Z.of_nat (length argv)).
  { rewrite (ji_argc _ _ _ _ _ _ _ HJ'). apply Z_to_bv_small. rewrite mod64. unfold argv in *. lia. }
  assert (V17 : bv_unsigned (eval rho' (SAlu ALU_ADD (SVar 5) (SLit 17))) = N0 + 17) by (apply (U_addc rho' (SVar 5) 17 N0); [exact V5 | lia | lia]).
  pose proof (U_lit64 rho' 2 ltac:(lia)) as L2.
  pose proof (U_lit64 rho' 4194304 ltac:(lia)) as L4M.
  pose proof (G_v4 rho' G') as V4. pose proof (U_lit64 rho' 140737488355311 ltac:(lia)) as L47.
  unfold F_use. repeat constructor; cbn [holds]; unfold bv_ltu, bv_eqb, branch_taken, bv_eqb;
    change (eval rho' (SVar 5)) with (rw rho' 5); change (eval rho' (SVar 25)) with (rw rho' 25); change (eval rho' (SVar 2)) with (rw rho' 2);
    change (eval rho' (SVar 4)) with (rw rho' 4);
    rewrite ?V17, ?L2, ?L4M, ?V5, ?V25, ?V2, ?V4, ?L47.
  - destruct (Z.eqb_spec (Z.of_nat (length argv)) 2); [exfalso; unfold argv in *; lia | discriminate].
  - lia.
  - lia.
  -   lia.
Qed.

Lemma hd_fact : ltac2:(tb__ "0|1|
S7SfSeS2dSeA1M0S82S2dS40A1S41OF_;F_;S0G0S14R5A1S32SeR4R3A3A3S4bS2aR2R6R7R3A5S19R8R6A2F_;F_;FK;Fw;FF;Ff;FS;Frho;").
Proof using . intros rho S f F w K E Hsp. eapply SP_fact; [exact Hsp|]. rewrite E. left. reflexivity. Qed.

Lemma SP_add1 : ltac2:(tb__ "0|0|
S2dS40A1S41OF_;F_;SfS7S82SeS4bS2aR5R4R3R2A5S19R4R2A2S0S2cS28S12R6A1R3A2S2bA3S4bS2aR8SdcS32SeR4S35SeA1A3R7A2R6R5A5F_;F_;F_;Ff;Fw;Frho;FS;FK;").
Proof using .
  intros K S rho w f [Hsm Hk] Hf Hb. split; [|exact Hk]. apply smatch_add_facts; [exact Hsm | constructor; [exact Hf|constructor] | cbn; rewrite Hb; reflexivity].
Qed.

Definition Q_at (S : sstate) (n : nat) : assn := ltac2:(tb__ "0|0|
S82S2S7S7S1S50R1A1S4bS2aS4eS4fVn;A1Vmd0;A2VS;R1R2A5A2Lrho;A2Lw;").

Lemma FirstNul_call : ltac2:(tb__ "0|0|
S7Sc4S50R2A1Se9Sd7Sd9R3Sb6R2A3SbbA2A1F_;Fms;Frho;").
Proof using Hargc Hent Hinp.
  intros rho ms HG. unfold FirstNul. rewrite rl_call, rw_call, s_sn_16. cbn [eval].
  rewrite (G_rl3 rho HG), (G_v5 rho HG). unfold nthb. unfold N0. rewrite Nat2Z.id. split.
  - rewrite tail_nul. reflexivity.
  - intros i Hi. rewrite <- (firstn_skipn (length argv0) (strs_tail draw inp)), tail_firstn.
    rewrite app_nth1 by lia. intros E. apply (argv0_nonul (Z.to_nat i) ltac:(lia)).
    apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma ovf_contra : ltac2:(tb__ "0|0|
S7S82S50R2A1S4bS2aS4eS4fU0A1Vmd0;A2SbaR3R2A5S3F_;F_;Fw;Frho;").
Proof using Hargc Hent Hinp.
  intros rho w HG Hsp.
  assert (Hf : holds rho (BNZ (SVar 5))).
  { eapply SP_fact; [exact Hsp|]. cbn. tauto. }
  apply holds_BNZ in Hf. apply Hf. rewrite (G_rl3 rho HG). change (eval rho (SVar 5)) with (rw rho 5).
  rewrite (G_v5 rho HG). unfold nthb, N0. rewrite Nat2Z.id, tail_nul. reflexivity.
Qed.

Lemma L_sn1 : ltac2:(tb__ "0|1|
S7S50R1A1S83S2aVok;S4bS2aS4eS4fU0M0A1Vmd0;A2Sb9R2A4S58SacG0A2A4F_;Frho;").
Proof using Hargc Hent Hinp HokK.
  intros rho2 HG2.
  eapply run_tr; [exact run2 | reflexivity | apply okf |].
  intros L rho3 [<-|[<-|[]]] Hag3; cbn [lf_state].
  +
    pose proof (Good_agree _ _ _ Hag3 ltac:(cbn; lia) HG2) as HG3.
    intros n Hg w Hw. exfalso. exact (ovf_contra rho3 w HG3 Hw).
  + eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. exists rho3. split; [exact (Good_agree _ _ _ Hag3 ltac:(cbn; lia) HG2) | exact Hw].
Qed.

Lemma L_post : ltac2:(tb__ "0|1|
S3cU4aS2eS38Q8A1Vargv0;A2A2S7S50R1A1SabSeS19R2A1S14Sb5A1A3S83S2aVok;S4bS2aS4eS4fU0M0A1Vmd0;A2Sb7R3A4S58SacG0A2A4F_;F_;Frho;F_;").
Proof using Hargc Hent Hinp HokK.
  intros Hlen74 rho2 HG2 HF2.
  apply (post_path segs ok (Kx (TR 0) md0) T_imp T_sn (ss_facts E_sn) xs_post rho2 _ fb_sn2 xs_post_ok HF2).

  apply triple_facts. intros HFT.
  eapply triple_conseq with (P := SP segs (Kx (TR 0) md0) T_sn74 rho2); [| intros w Hw; exact Hw | apply L_sn1; exact HG2].
  intros w Hsp. apply SP_add1; [| | reflexivity].
  - eapply (SP_restate segs _ rho2 T_sn T_sn1 w); [exact swf_T_sn1 | exact diff_sn | | constructor | exact Hsp].
    constructor; [|constructor]. cbn [fst snd]. exact (proj1 (Forall_forall _ _) HFT _ fact_T_sn).
  - cbn [holds]. rewrite U_lit64 by lia. change (eval rho2 (SVar 5)) with (rw rho2 5). rewrite (G_v5 rho2 HG2). unfold N0. lia.
Qed.

Lemma L_call : ltac2:(tb__ "0|1|
S3cU4aS2eS38Q8A1Vargv0;A2A2S7S50R1A1S83S2aVok;S4bS2aS4eS4fU0M0A1Vmd0;A2Sb2R2A4S58SacG0A2A4F_;Frho;F_;").
Proof using Hargc Hent Hinp HokK.
  intros Hlen74 rho HG.
  eapply run_tr; [exact run_use | reflexivity | apply okf |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  pose proof (Good_agree _ _ _ Hag1 ltac:(cbn; lia) HG) as HG1.
  apply (call_path segs FirstNul ok (Kx (TR 0) md0) (Kx (TR 0) md0) E_sn E_snX Pre_strnlen xs_pre s_sn R_sn Posts_strnlen _ rho1
           xs_pre_ok efr_sn chk_sn fb_sn).
  - intros rho2 HF. apply strnlen_sum; [apply okf | exact HF].
  - intros ms _. apply FirstNul_call. exact HG1.
  - intros L rho2 [<-|[]] Hag2 HF2. cbn [lf_state]. replace (ss_next Pre_strnlen) with NF by reflexivity. rewrite T_imp_eq.
    apply (L_post Hlen74); [|exact HF2]. exact (Good_agree _ _ _ Hag2 ltac:(cbn; lia) HG1).
Qed.

Definition Q_wr (S : sstate) (e : sv) (n len : nat) (rho : valuation) : assn := ltac2:(tb__ "0|2|
S82S2S7S7S2S30S30S1S50R2A1S1S17S12VS;A1M0Vrho;R2A3S1S0S38Q40M1A1S18R2G0A2S3aG1S7aR1A1A2A3S1S1S3cU1R1A2S3cR1Vlen;A2A2S4bS2aS4eS4fSa4Vn;R1A2A1Vmd0;A2SbeVS;Ve;A2R2R3A5A2A2A2A2Lk;A2Lrho';A2Lw;").

Lemma writev_site2 : forall S e n bs1 bs2 rho,
  Good rho -> (26 <= ss_next S)%positive ->
  instr_at segs (ss_pc S) = Some Ecall ->
  reg_sv S 17 = SLit 66 -> reg_sv S 10 = SLit 2 -> reg_sv S 12 = SLit 2 ->
  sv_below (ss_next S) e = true ->
  bs1 ++ bs2 = firstn (length (bs1 ++ bs2)) (skipn n MSG) ->
  (1 <= Z.of_nat (length (bs1 ++ bs2)) <= MAX_RW_COUNT)%Z ->
  (forall tr ms md, smatch_pending segs rho S (tr, mkCfg ms md) ->
     exists b1 l1 b2 l2,
       read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11)) = Some b1
       /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11) + 8)%bv = Some l1
       /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11) + 16)%bv = Some b2
       /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv S 11) + 16) + 8)%bv = Some l2
       /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1
       /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some bs2
       /\ bv_unsigned (eval rho e) = Z.of_nat (length (bs1 ++ bs2))
       /\ (bv_unsigned (eval rho (reg_sv S 11)) + 32 <= TASK_SIZE)%Z
       /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
       /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z) ->
  triple segs ok (SP segs (Kx (TR n) md0) S rho) (Q_wr S e n (length (bs1 ++ bs2)) rho).
Proof using Hargc Hfd2 HokK HokP.
  intros S e n bs1 bs2 rho HG Hn Hi H17 H10 H12 He Hbs Hlen Hrd.
  set (J' := fun (r : valuation) (tr : list event) (md : Model) =>
               exists k, rw r (ss_next S) = Z_to_bv 64 (Z.of_nat k) /\ (1 <= k <= length (bs1 ++ bs2))%nat
                         /\ tr = TR (n + k) /\ md = md0).
  apply triple1_triple.
  eapply triple1_conseq; [intros w Hw; exact Hw | |
    eapply (triple1_writev2J segs ok (liftK (Kx (TR n) md0)) J' S rho 2 bs1 bs2 e);
      [apply ok_frame_liftK; apply okf | eapply ok_pframeJ_of_tcons; [apply HokP; intros tr0 md0_ H0; exact H0 | intros r tr md Hk; exact (Ktc n tr md Hk)]
      | exact Hi | exact H17 | exact H10 | exact H12 | lia | exact Hlen | exact He | | ]].
  - intros w (rho' & Hag & Hsm & (k & Hk & Hkb & Htr & Hmd)). exists rho', k.
    split; [exact (Good_agree _ _ _ Hag Hn HG)|]. split; [exact Hag|]. split; [exact Hk|]. split; [exact Hkb|].
    split; [exact Hsm|]. split; [exact Htr | exact Hmd].
  - intros rho' tr md k Hag Hk [-> ->] Hkb. split; [exact Hfd2|]. exists k. split; [exact Hk|]. split; [exact Hkb|].
    split; [|reflexivity]. rewrite Hbs, firstn_firstn, Nat.min_l by lia. apply TR_app.
  - intros tr ms md Hsp _. exact (Hrd tr ms md Hsp).
Qed.

Lemma writev_site1 : forall S e n bs1 rho,
  Good rho -> (26 <= ss_next S)%positive ->
  instr_at segs (ss_pc S) = Some Ecall ->
  reg_sv S 17 = SLit 66 -> reg_sv S 10 = SLit 2 -> reg_sv S 12 = SLit 1 ->
  sv_below (ss_next S) e = true ->
  bs1 = firstn (length bs1) (skipn n MSG) ->
  (1 <= Z.of_nat (length bs1) <= MAX_RW_COUNT)%Z ->
  (forall tr ms md, smatch_pending segs rho S (tr, mkCfg ms md) ->
     exists b1 l1,
       read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11)) = Some b1
       /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11) + 8)%bv = Some l1
       /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1
       /\ bv_unsigned (eval rho e) = Z.of_nat (length bs1)
       /\ (bv_unsigned (eval rho (reg_sv S 11)) + 16 <= TASK_SIZE)%Z
       /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z) ->
  triple segs ok (SP segs (Kx (TR n) md0) S rho) (Q_wr S e n (length bs1) rho).
Proof using Hargc Hfd2 HokK HokP.
  intros S e n bs1 rho HG Hn Hi H17 H10 H12 He Hbs Hlen Hrd.
  set (J' := fun (r : valuation) (tr : list event) (md : Model) =>
               exists k, rw r (ss_next S) = Z_to_bv 64 (Z.of_nat k) /\ (1 <= k <= length bs1)%nat
                         /\ tr = TR (n + k) /\ md = md0).
  apply triple1_triple.
  eapply triple1_conseq; [intros w Hw; exact Hw | |
    eapply (triple1_writev1J segs ok (liftK (Kx (TR n) md0)) J' S rho 2 bs1 e);
      [apply ok_frame_liftK; apply okf | eapply ok_pframeJ_of_tcons; [apply HokP; intros tr0 md0_ H0; exact H0 | intros r tr md Hk; exact (Ktc n tr md Hk)]
      | exact Hi | exact H17 | exact H10 | exact H12 | lia | exact Hlen | exact He | | ]].
  - intros w (rho' & Hag & Hsm & (k & Hk & Hkb & Htr & Hmd)). exists rho', k.
    split; [exact (Good_agree _ _ _ Hag Hn HG)|]. split; [exact Hag|]. split; [exact Hk|]. split; [exact Hkb|].
    split; [exact Hsm|]. split; [exact Htr | exact Hmd].
  - intros rho' tr md k Hag Hk [-> ->] Hkb. split; [exact Hfd2|]. exists k. split; [exact Hk|]. split; [exact Hkb|].
    split; [|reflexivity]. rewrite Hbs, firstn_firstn, Nat.min_l by lia. apply TR_app.
  - intros tr ms md Hsp _. exact (Hrd tr ms md Hsp).
Qed.

Lemma In_cellb : ltac2:(tb__ "0|0|
S9S2dS9A1S0S2cS6aS9S68R2A1R1A3S2bA3S6bS9R3R2A3F_;Fcells;Fc;").
Proof using .
  intros c cells H. apply existsb_exists in H as (c' & Hin & E). apply cell_eqb_sound in E. subst c'. exact Hin.
Qed.

Lemma u8 : bv_unsigned (8%bv : bv 64) = 8. Proof using . reflexivity. Qed.
Lemma u16 : bv_unsigned (16%bv : bv 64) = 16. Proof using . reflexivity. Qed.
Lemma U_bvadd : ltac2:(tb__ "0|4|
S38Q40M0A1M1G1S3eS3eS0S3eS39G0R4A2R2A3M2G2S1S79Z0S78R4R3A2M3A2S7cG3S7eZ2Z40A2A2A2S0S3eS39G0S3bG0R7R6A3A2S78R5R4A2A3F_;F_;F_;Fy;Fx;Fb;Fa;").
Proof using Hargc LEN N0 STR. intros a b x y <- <- H. rewrite bv_add_unsigned. unfold bv_wrap. rewrite mod64. apply Z.mod_small. lia. Qed.

Lemma and7_tail (A B C D E F G T : Prop) : ltac2:(tb__ "0|0|
VT;S1VA;S1VB;S1VC;S1VD;S1VE;S1VF;VG;A2A2A2A2A2A2S1VA;S1VB;S1VC;S1VD;S1VE;S1VF;S1VG;VT;A2A2A2A2A2A2A2F_;F_;").
Proof using . tauto. Qed.
Lemma and4_tail (A B C D T : Prop) : ltac2:(tb__ "0|0|
VT;S1VA;S1VB;S1VC;VD;A2A2A2S1VA;S1VB;S1VC;S1VD;VT;A2A2A2A2F_;F_;").
Proof using . tauto. Qed.
Ltac Uatom := first
  [ eassumption
  | match goal with |- bv_unsigned (eval ?r (SVar ?k)) = _ => change (eval r (SVar k)) with (rw r k); first [eassumption | reflexivity] end
  | apply U_lit64; lia
  | reflexivity ].
Ltac Uexp := first
  [ eassumption
  | match goal with |- bv_unsigned (eval ?r (SVar ?k)) = _ => change (eval r (SVar k)) with (rw r k); first [eassumption | reflexivity] end
  | apply U_lit64; lia
  | eapply U_addc; [Uexp | lia | lia]
  | eapply U_add2; [Uexp | Uexp | lia]
  | eapply U_sub2; [Uexp | Uexp | lia]
  | reflexivity ].
Ltac tsz1 := unfold TASK_SIZE;
  match goal with
  | |- bv_unsigned ?a + bv_unsigned ?b <= _ =>
      let Ha := fresh "Ua" in let Hb := fresh "Ub" in
      eassert (Ha : bv_unsigned a = _) by Uexp; eassert (Hb : bv_unsigned b = _) by Uexp; rewrite Ha, Hb; lia
  | |- bv_unsigned ?a + _ <= _ => let Ha := fresh "Ua" in eassert (Ha : bv_unsigned a = _) by Uexp; rewrite Ha; lia
  end.
Ltac tsz := repeat split; tsz1.

Definition ob0 (S : sstate) : sobj := nth 0 (ss_objs S) dummy_obj.
Definition ob1 (S : sstate) : sobj := nth 1 (ss_objs S) dummy_obj.

Lemma objs_hold01 : ltac2:(tb__ "0|1|
S7SfS2dS40A1M0Sc4S41ScfS2aR5R4S34G0ScbR3SccR2R1A2A4A4S3cU2S2eSbS10R5A1A2A2S1S25S2aR7R4S52R6A1A4S25S2aR7R4S54R6A1A4A2F_;F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using Hargc JI LEN N0 STR.
  intros rho S tr ms md Hsp Hlen. destruct (smatch_pending_mem segs _ _ _ _ _ Hsp) as (Hall & _ & _).
  unfold ob0, ob1. destruct (ss_objs S) as [|o0 [|o1 r]]; cbn in Hlen; try lia.
  apply Forall_cons_iff in Hall as [H0 Hall]. apply Forall_cons_iff in Hall as [H1 _]. cbn. auto.
Qed.

Lemma strs_read : ltac2:(tb__ "0|6|
S7SfS2dS40A1M0Sc4S41S3eS30S38Q40M1A1M2G2S50R9A1ScfS2aRaR9S34G0ScbR8SccR7R6A2A4A4S3cU2S2eSbS10RaA1A2A2S0SbS54RbA1Sd4P19P3A2A3S79Z0R8A2S79S78R9S7aR8A1A2S78VN0;Z1A2A2S0S3eS39G1R8A2M3S78S78S39G1Vsp;A2VSTR;A2RaA2A3S0S3eG3S7aRaA1A3S0S33S2dS38Q8A1M4A1M5A1S43Sc5ReA1RaR9A3S31G5Sa8G4RbSa6G4S7fRcA1Sd3Vdraw;Vinp;A2A3A3A2A3F_;F_;F_;F_;F_;F_;F_;F_;Flen;Fa;Fn;Foff;Fmd;Fms;Ftr;FS;Frho;").
Proof using Hargc Hent Hinp.
  intros rho S tr ms md off n a len HG Hsp Hlen Hob Hoff Hn Ha Hl. pose proof NU.
  destruct (objs_hold01 rho S tr ms md Hsp Hlen) as [_ H1]. rewrite Hob in H1.
  rewrite <- (G_rl3 rho HG).
  rewrite (list_obj_read_bytes_map segs rho ms (O_strs 25 3) 3 n off a len H1 eq_refl eq_refl).
  - unfold obj_lo_of. cbn [ob_lo O_strs]. rewrite soff_lit_small by lia. rewrite Z.sub_0_r. reflexivity.
  - unfold obj_lo_of. cbn [ob_lo O_strs]. rewrite soff_lit_small by lia. lia.
  - unfold obj_hi_of. cbn [ob_hi O_strs]. rewrite soff_snorm. unfold U. change (eval rho (SVar 25)) with (rw rho 25).
    rewrite (G_v25 rho HG). rewrite snorm_id; [lia|]. unfold smin, smax. lia.
  - cbn [ob_base O_strs]. change (eval rho (SVar 4)) with (rw rho 4). rewrite (G_v4 rho HG). lia.
  - exact Hl.
Qed.

Lemma strs_window : ltac2:(tb__ "0|1|
S30S30S3cSa4R2R1A2S2eS38Q8A1M0Vargv0;A2A2S0S2dG0A1Sa8G0R2Sa6G0R3Sd3Vdraw;Vinp;A2A3A3Sa8G0R2Sa6G0R3Vargv0;A3A3A3F_;Fn;Fd;").
Proof using Hargc Hent Hinp.
  intros d n H. rewrite <- tail_firstn. rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia.
Qed.

Lemma ibuf_read : ltac2:(tb__ "0|8|
S7SfS2dS40A1M0Sc4S41S2dS6eA1M1S50R6A1ScfS2aR7R6S34G0ScbR5SccR4R3A2A4A4S3cU2S2eSbS10R7A1A2A2S0S2cS1aS12R8A1S52R8A1A2S2bA3S0S36S36S5S5A2M2S5A2SbcS52R9A1A1S34G2S5S34S5S5SdP1A1S6S7bSbfA1A1A4S6Z0M3A1A4A3S0S33G1A1S71S11S52RaA1A1S6N230A1G3U7M4A4S31G1R6A2A3S0S33S2dS38Q8A1M5A1M6A1S1bR9S3aQ40M7S7dS39G7Vsp;A2Z230A2A2G4A3S31G6Sa7S6eG5S70RcA1R7A4A2A3F_;F_;F_;F_;F_;F_;Fbl;Fmd;Fms;Ftr;FS;Frho;").
Proof using Hargc Hent Hinp.
  intros rho S tr ms md bl HG Hsp Hlen Hwf Hrng Hcb. pose proof NU.
  destruct (objs_hold01 rho S tr ms md Hsp Hlen) as [H0 _].
  unfold obj_rng in Hrng. injection Hrng as Hb Hlo Hhi.
  pose proof (cells_bytes_sound segs rho ms (ob0 S) (ss_next S) (SLit (-560)) 0 7 bl H0 Hwf) as X.
  unfold obj_lo_of, obj_hi_of in X. rewrite Hb, Hlo, Hhi in X. rewrite !soff_lit_small in X by (unfold STK_FREE; lia).
  change (eval rho (SVar 1)) with (rw rho 1) in X. rewrite (G_v1 rho HG) in X.
  replace (bv_unsigned sp + -560 + 0) with (bv_unsigned sp - 560) in X by lia.
  apply X; [unfold STK_FREE; lia | exact Hcb].
Qed.

Lemma iov_field : ltac2:(tb__ "0|5|
S7SfS2dS40A1M0Sc4S41S3eS5S38Q40M1A1M2S50R8A1ScfS2aR9R8S34G0ScbR7SccR6R5A2A4A4S3cU2S2eSbS10R9A1A2A2S0S36S36S5S5A2M3S5A2SbcS52RaA1A1S34G3S5S34S5S5SdP1A1S6S7bSbfA1A1A4S6Z0M4A1A4A3S0S2cS6aS9S68ScS6R7A1Z8R6A3A1S11S52RbA1A1A3S2bA3S1S79S7bS7eZ2Z14A2A1R8A2S7cR8G4A2A2S0S3eS39G1R7A2S78S39G1Vsp;A2R9A2A3S0S33G2A1S49Sc5RcA1R8A2S31G2S16RfR9A2A2A3F_;F_;F_;F_;F_;F_;F_;Fa;Fv;Foff;Fmd;Fms;Ftr;FS;Frho;").
Proof using Hargc Hent Hinp.
  intros rho S tr ms md off v a HG Hsp Hlen Hrng Hc Hoff Ha. pose proof NU.
  destruct (objs_hold01 rho S tr ms md Hsp Hlen) as [H0 _].
  unfold obj_rng in Hrng. injection Hrng as Hb Hlo Hhi.
  apply (cell_read_u64 segs rho ms (ob0 S) (SLit off) v a H0 (In_cellb _ _ Hc)).
  rewrite Hb. change (eval rho (SVar 1)) with (rw rho 1). rewrite (G_v1 rho HG), soff_lit_small by lia. lia.
Qed.

Definition BL_usage : list bexp := ltac2:(tb__ "0|0|
S32S6eS6fZ75A1S32S6eS6fZ73A1S32S6eS6fZ61A1S32S6eS6fZ67A1S32S6eS6fZ65A1S32S6eS6fZ3aA1S32S6eS6fZ20A1S35S6eA1A3A3A3A3A3A3A3").
Definition BL_input : list bexp := ltac2:(tb__ "0|0|
S32S6eS6fZ20A1S32S6eS6fZ49A1S32S6eS6fZ4eA1S32S6eS6fZ50A1S32S6eS6fZ55A1S32S6eS6fZ54A1S32S6eS6fZaA1S35S6eA1A3A3A3A3A3A3A3").
Lemma BL_usage_eval : ltac2:(tb__ "0|1|
S7S0S2dS38Q8A1M0A1Sa7S6eG0S70R1A1S5dA4ScaSc2Sc1S2bS2fS2bS2fS2bS2bS2bS2fA8Sc2Sc1S2bS2bS2fS2fS2bS2bS2bS2fA8Sc2Sc1S2bS2fS2fS2fS2fS2bS2bS2fA8Sc2Sc1S2bS2bS2bS2fS2fS2bS2bS2fA8Sc2Sc1S2bS2fS2bS2fS2fS2bS2bS2fA8Sc2Sc1S2fS2bS2fS2bS2bS2bS2fS2fA8Sc2Sc1S2fS2fS2fS2fS2fS2bS2fS2fA8Sc3A2A2A2A2A2A2A2A1A3Frho;"). Proof using . reflexivity. Qed.
Lemma BL_input_eval : ltac2:(tb__ "0|1|
S7S0S2dS38Q8A1M0A1Sa7S6eG0S70R1A1S5cA4S57A3Frho;"). Proof using . reflexivity. Qed.

Lemma cert_E_A1 : ltac2:(tb__ "0|d|
S1S0S2cS1aS12SacA1M0S52SacA1M1A2S2bA3S1S0S36S36S5S5A2M2S5A2SbcG1A1S34G2S5S34S5S5SdP1A1M3S6S7bSbfA1A1A4S6Z0M4A1A4A3S1S0SbS54SacA1Sd4P19P3A2A3S1S3cU2S2eSbS10SacA1A2A2S1S0S33S2dS6eA1M5A1S71S11G1A1M6S6N230A1M7G4U7A4S31G5S5dA2A3S1S0S2cS6aS9S68ScS6N4c8A1M8Z8M9SaS73G3G7A3A3A1G6A3S2bA3S1S0S2cS6aS9S68ScS6N4c0A1G9S6Z7A1MaA3A1G6A3S2bA3S1S0S2cS6aS9S68ScS6N4b8A1G9SdP4A1A3A1G6A3S2bA3S1S0S2cS6aS9S68ScS6N4b0A1G9SdP5A1MbA3A1G6A3S2bA3S1S0S5S8SacZbA2SaS73G3G8A3A3S1S0S5S8SacZ16A2SaS73GbGaA3A3S1S0S33S74A1S88S2aS15SacA1A2S31S74S75A2A3S1S0S5S8SacZ11A2S6Z42A1A3S1S0S5S8SacZaA2S6Z2A1McA3S1S0S5S8SacZcA2GcA3S0S3fG0P43A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using Hargc LEN N0 STR. vm_compute. repeat split; (reflexivity || lia). Qed.

Lemma bytes_E_A1 : forall rho tr ms md, Good rho -> smatch_pending segs rho E_A1 (tr, mkCfg ms md) ->
  exists b1 l1 b2 l2,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv E_A1 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv E_A1 11) + 8)%bv = Some l1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv E_A1 11) + 16)%bv = Some b2
    /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv E_A1 11) + 16) + 8)%bv = Some l2
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some (str "usage: ")
    /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some argv0
    /\ bv_unsigned (eval rho (reg_sv E_A1 22)) = Z.of_nat (length (str "usage: " ++ argv0))
    /\ (bv_unsigned (eval rho (reg_sv E_A1 11)) + 32 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
    /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros rho tr ms md HG Hsp. pose proof NU as NU'.
  destruct cert_E_A1 as (Hwf & Hrng & Hob1 & Hlen & Hcb & C1 & C2 & C3 & C4 & R11 & R22 & _).
  rewrite R11, R22.
  pose proof (G_v1 rho HG) as V1. pose proof (G_v4 rho HG) as V4. pose proof (G_v5 rho HG) as V5.
  assert (A0 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-1224)))) = bv_unsigned sp - 1224).
  { erewrite U_addc; [reflexivity | exact V1 | lia | lia]. }
  exists (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-560)))), (eval rho (SLit 7)), (eval rho (SVar 4)), (eval rho (SVar 5)).
  apply and7_tail; [tsz|].
  assert (A8 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-1224))) + 8)%bv = bv_unsigned sp - 1216).
  { rewrite (U_bvadd _ _ _ _ A0 u8) by lia. lia. }
  assert (A16 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-1224))) + 16)%bv = bv_unsigned sp - 1208).
  { rewrite (U_bvadd _ _ _ _ A0 u16) by lia. lia. }
  assert (A24 : bv_unsigned ((eval rho (SAlu ALU_ADD (SVar 1) (SLit (-1224))) + 16) + 8)%bv = bv_unsigned sp - 1200).
  { rewrite (U_bvadd _ _ _ _ A16 u8) by lia. lia. }
  split; [eapply (iov_field rho E_A1 tr ms md (-1224)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field rho E_A1 tr ms md (-1216)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | lia]|].
  split; [eapply (iov_field rho E_A1 tr ms md (-1208)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C3 | lia | lia]|].
  split; [eapply (iov_field rho E_A1 tr ms md (-1200)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C4 | lia | lia]|].
  split.
  { rewrite <- (BL_usage_eval rho). apply (read_bytes_map_of_rd ms _ _ 7); [change (Z.of_nat 7) with 7; apply U_lit64; lia|].
    replace (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-560)))) with (Z_to_bv 64 (bv_unsigned sp - 560)).
    - eapply ibuf_read; eauto.
    - apply bv_eq. rewrite Z_to_bv_small by (rewrite mod64; lia). symmetry. apply (U_addc rho (SVar 1) (-560) (bv_unsigned sp)); [exact V1 | lia | lia]. }
  split.
  { replace argv0 with (firstn (length argv0) (skipn (Z.to_nat 0) (strs_tail draw inp)))
      by (cbn [Z.to_nat skipn]; apply tail_firstn).
    apply (strs_read rho E_A1 tr ms md 0 (length argv0)); [exact HG | exact Hsp | exact Hlen | exact Hob1 | lia | unfold N0; lia | | exact V5].
    change (eval rho (SVar 4)) with (rw rho 4). rewrite V4. lia. }
  erewrite U_addc; [| exact V5 | unfold N0; lia | lia]. rewrite length_app. unfold N0. cbn [length str]. lia.
Qed.

Lemma SPp_fact : ltac2:(tb__ "0|1|
S7SfS2dS40A1M0Sc4S41SeScfS2aR6R5S34G0ScbR4SccR3R2A2A4A4S6bSeR2S14R6A1A3S19R8R3A2F_;F_;Fp;Fmd;Fms;Ftr;FS;Frho;").
Proof using . intros rho S tr ms md p Hsp Hin. exact (proj1 (Forall_forall _ _) (smatch_pending_facts segs _ _ _ _ _ Hsp) p Hin). Qed.

Lemma cert_CB2 : ltac2:(tb__ "0|c|
S1S0S2cS1aS12SafA1M0S52SafA1M1A2S2bA3S1S0S36S36S5S5A2M2S5A2SbcG1A1S34G2S5S34S5S5SdP1A1M3S6S7bSbfA1A1A4S6Z0M4A1A4A3S1S0SbS54SafA1Sd4P19P3A2A3S1S3cU2S2eSbS10SafA1A2A2S1S0S33S2dS6eA1M5A1S71S11G1A1M6S6N230A1G4U7A4S31G5S5dA2A3S1S0S2cS6aS9S68ScS6N4c8A1M7Z8M8SaS76SaS73G3S6N229A1A3SdP43A1M9A3A3A1G6A3S2bA3S1S0S2cS6aS9S68ScS6N4c0A1G8G9A3A1G6A3S2bA3S1S0S2cS6aS9S68ScS6N4b8A1G8SdP4A1A3A1G6A3S2bA3S1S0S2cS6aS9S68ScS6N4b0A1G8SdP5A1MaA3A1G6A3S2bA3S1S0S5S8SafZbA2SaS73G3G7A3A3S1S0S5S8SafZ16A2SaS73GaG9A3A3S1S0S33S74A1S88S2aS15SafA1A2S31S74S75A2A3S1S0S5S8SafZ11A2S6Z42A1A3S1S0S5S8SafZaA2S6Z2A1MbA3S1S0S5S8SafZcA2GbA3S1S0S3fG0P47A3S6bSeS13G9S6Z6A1A2S14SafA1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using Hargc LEN N0 STR. vm_compute. repeat split; (reflexivity || lia || (cbn; tauto)). Qed.

Lemma bytes_CB2 : forall rho tr ms md, Good rho -> smatch_pending segs rho CB2 (tr, mkCfg ms md) ->
  let L0 := Z.to_nat (bv_unsigned (rw rho 67)) in
  exists b1 l1 b2 l2,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv CB2 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv CB2 11) + 8)%bv = Some l1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv CB2 11) + 16)%bv = Some b2
    /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv CB2 11) + 16) + 8)%bv = Some l2
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some (skipn (7 - L0) (str "usage: "))
    /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some argv0
    /\ bv_unsigned (eval rho (reg_sv CB2 22)) = Z.of_nat (length (skipn (7 - L0) (str "usage: ") ++ argv0))
    /\ (bv_unsigned (eval rho (reg_sv CB2 11)) + 32 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
    /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros rho tr ms md HG Hsp. pose proof NU as NU'.
  destruct cert_CB2 as (Hwf & Hrng & Hob1 & Hlen & Hcb & C1 & C2 & C3 & C4 & R11 & R22 & _ & _ & _ & _ & _ & HinF).
  pose proof (SPp_fact _ _ _ _ _ _ Hsp HinF) as HL0. cbn [holds] in HL0. rewrite U_lit64 in HL0 by lia.
  change (eval rho (SVar 67)) with (rw rho 67) in HL0. pose proof (urange (rw rho 67)) as R67.
  intros L0. rewrite R11, R22.
  pose proof (G_v1 rho HG) as V1. pose proof (G_v4 rho HG) as V4. pose proof (G_v5 rho HG) as V5.
  assert (A0 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-1224)))) = bv_unsigned sp - 1224).
  { erewrite U_addc; [reflexivity | exact V1 | lia | lia]. }
  assert (A16 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-1224))) + 16)%bv = bv_unsigned sp - 1208).
  { rewrite (U_bvadd _ _ _ _ A0 u16) by lia. lia. }
  exists (eval rho (SAlu ALU_SUB (SAlu ALU_ADD (SVar 1) (SLit (-553))) (SVar 67))), (eval rho (SVar 67)), (eval rho (SVar 4)), (eval rho (SVar 5)).
  apply and7_tail; [tsz|].
  split; [eapply (iov_field rho CB2 tr ms md (-1224)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field rho CB2 tr ms md (-1216)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split; [eapply (iov_field rho CB2 tr ms md (-1208)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C3 | lia | lia]|].
  split; [eapply (iov_field rho CB2 tr ms md (-1200)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C4 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
  split.
  { rewrite <- (BL_usage_eval rho). apply (read_bytes_map_of_rd ms _ _ L0); [subst L0; change (eval rho (SVar 67)) with (rw rho 67); lia|].
    replace (eval rho (SAlu ALU_SUB (SAlu ALU_ADD (SVar 1) (SLit (-553))) (SVar 67)))
      with (Z_to_bv 64 (bv_unsigned sp - 560) + Z_to_bv 64 (Z.of_nat (7 - L0)))%bv.
    - apply rd_bytes_skip. replace (7 - L0 + L0)%nat with 7%nat by lia. eapply ibuf_read; eauto.
    - apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite mod64, <- Z.add_mod, Z.mod_small by lia.
      symmetry. erewrite (U_sub2 rho _ _ (bv_unsigned sp - 553) (bv_unsigned (rw rho 67))); [lia | | reflexivity | lia].
      apply (U_addc rho (SVar 1) (-553) (bv_unsigned sp)); [exact V1 | lia | lia]. }
  split.
  { replace argv0 with (firstn (length argv0) (skipn (Z.to_nat 0) (strs_tail draw inp)))
      by (cbn [Z.to_nat skipn]; apply tail_firstn).
    apply (strs_read rho CB2 tr ms md 0 (length argv0)); [exact HG | exact Hsp | exact Hlen | exact Hob1 | lia | unfold N0; lia | | exact V5].
    change (eval rho (SVar 4)) with (rw rho 4). rewrite V4. lia. }
  erewrite (U_add2 rho _ _ N0 (bv_unsigned (rw rho 67))); [| exact V5 | reflexivity | unfold N0; lia].
  rewrite length_app, length_skipn. unfold N0. cbn [length str]. lia.
Qed.

Lemma cert_CB1 : ltac2:(tb__ "0|a|
S1S0S36S36S5S5A2M0S5A2SbcS52SaeA1M1A1S34G0S5S34S5S5SdP1A1M2S6S7bSbfA1A1A4S6Z0A1A4A3S1S0SbS54SaeA1Sd4P19P3A2A3S1S3cU2S2eSbS10SaeA1A2A2S1S0S2cS6aS9S68ScS6N4b8A1M3Z8M4SaS76SaS73SdP4A1SdP5A1M5A3SdP44A1M6A3A3A1S11G1A1M7A3S2bA3S1S0S2cS6aS9S68ScS6N4b0A1G4G6A3A1G7A3S2bA3S1S0S5S8SaeZbA2SaS73G2G3A3A3S1S0S5S8SaeZ16A2G6A3S1S0S33S74A1S88S2aS15SaeA1A2S31S74S75A2A3S1S0S5S8SaeZ11A2S6Z42A1A3S1S0S5S8SaeZaA2S6Z2A1A3S1S0S5S8SaeZcA2S6Z1A1M8A3S1S0S3fS12SaeA1P48A3S1S6bSeS13G8G6A2S14SaeA1M9A3S6bSeS27S77G6G5A3G9A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using Hargc LEN N0 STR. vm_compute. repeat split; (reflexivity || lia || (cbn; tauto)). Qed.

Lemma bytes_CB1 : forall rho tr ms md, Good rho -> smatch_pending segs rho CB1 (tr, mkCfg ms md) ->
  let R := Z.to_nat (bv_unsigned (rw rho 68)) in
  (1 <= R < length argv0)%nat /\
  exists b1 l1,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv CB1 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv CB1 11) + 8)%bv = Some l1
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some (skipn (length argv0 - R) argv0)
    /\ bv_unsigned (eval rho (reg_sv CB1 22)) = Z.of_nat (length (skipn (length argv0 - R) argv0))
    /\ (bv_unsigned (eval rho (reg_sv CB1 11)) + 16 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros rho tr ms md HG Hsp. pose proof NU as NU'.
  destruct cert_CB1 as (Hrng & Hob1 & Hlen & C1 & C2 & R11 & R22 & _ & _ & _ & _ & _ & HinF1 & HinF2).
  pose proof (G_v1 rho HG) as V1. pose proof (G_v4 rho HG) as V4. pose proof (G_v5 rho HG) as V5.
  pose proof (SPp_fact _ _ _ _ _ _ Hsp HinF1) as HR1. cbn [holds] in HR1. rewrite U_lit64 in HR1 by lia.
  pose proof (SPp_fact _ _ _ _ _ _ Hsp HinF2) as HR2. cbn [holds branch_taken] in HR2. unfold bv_ltu in HR2. apply Z.ltb_lt in HR2.
  change (eval rho (SVar 68)) with (rw rho 68) in HR1, HR2. change (eval rho (SVar 5)) with (rw rho 5) in HR2. rewrite V5 in HR2.
  pose proof (urange (rw rho 68)) as R68.
  intros R. split; [subst R; unfold N0 in HR2; lia|]. rewrite R11, R22.
  assert (A0 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-1208)))) = bv_unsigned sp - 1208).
  { erewrite U_addc; [reflexivity | exact V1 | lia | lia]. }
  exists (eval rho (SAlu ALU_SUB (SAlu ALU_ADD (SVar 4) (SVar 5)) (SVar 68))), (eval rho (SVar 68)).
  apply and4_tail; [tsz|].
  split; [eapply (iov_field rho CB1 tr ms md (-1208)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field rho CB1 tr ms md (-1200)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split.
  { replace (skipn (length argv0 - R) argv0) with (firstn R (skipn (Z.to_nat (N0 - Z.of_nat R)) (strs_tail draw inp))).
    2:{ rewrite strs_window by (unfold N0; lia). rewrite firstn_all2 by (rewrite length_skipn; unfold N0; lia). f_equal. unfold N0. lia. }
    apply (strs_read rho CB1 tr ms md (N0 - Z.of_nat R) R); [exact HG | exact Hsp | exact Hlen | exact Hob1 | lia | lia | | subst R; change (eval rho (SVar 68)) with (rw rho 68); lia].
    erewrite (U_sub2 rho _ _ (bv_unsigned sp + STR + N0) (bv_unsigned (rw rho 68))); [subst R; lia | | reflexivity | lia].
    apply (U_add2 rho (SVar 4) (SVar 5)); [exact V4 | exact V5 | lia]. }
  change (eval rho (SVar 68)) with (rw rho 68). rewrite length_skipn. subst R. lia.
Qed.

Lemma cert_E_A2 : ltac2:(tb__ "0|d|
S1S0S2cS1aS12SadA1M0S52SadA1M1A2S2bA3S1S0S36S36S5S5A2M2S5A2SbcG1A1S34G2S5S34S5S5SdP1A1M3S6S7bSbfA1A1A4S6Z0M4A1M5A4A3S1S3cU2S2eSbS10SadA1A2A2S1S0S33S2dS6eA1M6A1S71S11G1A1M7S6N230A1M8G4U7A4S31G6S5cA2A3S1S0S2cS6aS9S68ScS6N2a8A1M9Z8MaSaS73G3G8A3A3A1G7A3S2bA3S1S0S2cS6aS9S68ScS6N2a0A1GaS6Z7A1MbA3A1G7A3S2bA3S1S0S2cS6aS9S68ScS6N298A1GaG5A3A1G7A3S2bA3S1S0S2cS6aS9S68ScS6N290A1GaG5A3A1G7A3S2bA3S1S0S5S8SadZbA2SaS73G3G9A3A3S1S0S5S8SadZ16A2GbA3S1S0S33S74A1S88S2aS15SadA1A2S31S74S75A2A3S1S0S5S8SadZ11A2S6Z42A1A3S1S0S5S8SadZaA2S6Z2A1McA3S1S0S5S8SadZcA2GcA3S0S3fG0P5aA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using Hargc LEN N0 STR. vm_compute. repeat split; (reflexivity || lia). Qed.

Lemma bytes_E_A2 : forall rho tr ms md, Good rho -> smatch_pending segs rho E_A2 (tr, mkCfg ms md) ->
  exists b1 l1 b2 l2,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv E_A2 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv E_A2 11) + 8)%bv = Some l1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv E_A2 11) + 16)%bv = Some b2
    /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv E_A2 11) + 16) + 8)%bv = Some l2
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some M2
    /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some []
    /\ bv_unsigned (eval rho (reg_sv E_A2 22)) = Z.of_nat (length (M2 ++ []))
    /\ (bv_unsigned (eval rho (reg_sv E_A2 11)) + 32 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
    /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros rho tr ms md HG Hsp. pose proof NU as NU'.
  destruct cert_E_A2 as (Hwf & Hrng & Hlen & Hcb & C1 & C2 & C3 & C4 & R11 & R22 & _).
  rewrite R11, R22. pose proof (G_v1 rho HG) as V1.
  assert (A0 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-680)))) = bv_unsigned sp - 680).
  { erewrite U_addc; [reflexivity | exact V1 | lia | lia]. }
  assert (A16 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-680))) + 16)%bv = bv_unsigned sp - 664).
  { rewrite (U_bvadd _ _ _ _ A0 u16) by lia. lia. }
  exists (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-560)))), (eval rho (SLit 7)), (eval rho (SLit 0)), (eval rho (SLit 0)).
  apply and7_tail; [tsz|].
  split; [eapply (iov_field rho E_A2 tr ms md (-680)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field rho E_A2 tr ms md (-672)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split; [eapply (iov_field rho E_A2 tr ms md (-664)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C3 | lia | lia]|].
  split; [eapply (iov_field rho E_A2 tr ms md (-656)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C4 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
  split.
  { rewrite <- (BL_input_eval rho). apply (read_bytes_map_of_rd ms _ _ 7); [change (Z.of_nat 7) with 7; apply U_lit64; lia|].
    replace (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-560)))) with (Z_to_bv 64 (bv_unsigned sp - 560)).
    - eapply ibuf_read; eauto.
    - apply bv_eq. rewrite Z_to_bv_small by (rewrite mod64; lia). symmetry. apply (U_addc rho (SVar 1) (-560) (bv_unsigned sp)); [exact V1 | lia | lia]. }
  split; [reflexivity|].
  rewrite U_lit64 by lia. reflexivity.
Qed.

Lemma cert_CB3 : ltac2:(tb__ "0|d|
S1S0S2cS1aS12Sb0A1M0S52Sb0A1M1A2S2bA3S1S0S36S36S5S5A2M2S5A2SbcG1A1S34G2S5S34S5S5SdP1A1M3S6S7bSbfA1A1A4S6Z0M4A1M5A4A3S1S3cU2S2eSbS10Sb0A1A2A2S1S0S33S2dS6eA1M6A1S71S11G1A1M7S6N230A1G4U7A4S31G6S5cA2A3S1S0S2cS6aS9S68ScS6N2a8A1M8Z8M9SaS76SaS73G3S6N229A1A3SdP5aA1MaA3A3A1G7A3S2bA3S1S0S2cS6aS9S68ScS6N2a0A1G9GaA3A1G7A3S2bA3S1S0S2cS6aS9S68ScS6N298A1G9G5A3A1G7A3S2bA3S1S0S2cS6aS9S68ScS6N290A1G9G5A3A1G7A3S2bA3S1S0S5S8Sb0ZbA2SaS73G3G8A3A3S1S0S5S8Sb0Z16A2GaA3S1S0S33S74A1S88S2aS15Sb0A1A2S31S74S75A2A3S1S0S5S8Sb0Z11A2S6Z42A1A3S1S0S5S8Sb0ZaA2S6Z2A1MbA3S1S0S5S8Sb0ZcA2GbA3S1S0S3fG0P5dA3S1S6bSeS13S6Z1A1GaA2S14Sb0A1McA3S6bSeS13GaS6Z6A1A2GcA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using Hargc LEN N0 STR. vm_compute. repeat split; (reflexivity || lia || (cbn; tauto)). Qed.

Lemma bytes_CB3 : forall rho tr ms md, Good rho -> smatch_pending segs rho CB3 (tr, mkCfg ms md) ->
  let L0 := Z.to_nat (bv_unsigned (rw rho 90)) in
  (1 <= L0 <= 6)%nat /\
  exists b1 l1 b2 l2,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv CB3 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv CB3 11) + 8)%bv = Some l1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv CB3 11) + 16)%bv = Some b2
    /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv CB3 11) + 16) + 8)%bv = Some l2
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some (skipn (7 - L0) M2)
    /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some []
    /\ bv_unsigned (eval rho (reg_sv CB3 22)) = Z.of_nat (length (skipn (7 - L0) M2 ++ []))
    /\ (bv_unsigned (eval rho (reg_sv CB3 11)) + 32 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
    /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros rho tr ms md HG Hsp. pose proof NU as NU'.
  destruct cert_CB3 as (Hwf & Hrng & Hlen & Hcb & C1 & C2 & C3 & C4 & R11 & R22 & _ & _ & _ & _ & _ & HinF1 & HinF2).
  pose proof (SPp_fact _ _ _ _ _ _ Hsp HinF1) as HL1. cbn [holds] in HL1. rewrite U_lit64 in HL1 by lia.
  pose proof (SPp_fact _ _ _ _ _ _ Hsp HinF2) as HL2. cbn [holds] in HL2. rewrite U_lit64 in HL2 by lia.
  change (eval rho (SVar 90)) with (rw rho 90) in HL1, HL2.
  intros L0. split; [subst L0; lia|]. rewrite R11, R22. pose proof (G_v1 rho HG) as V1.
  assert (A0 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-680)))) = bv_unsigned sp - 680).
  { erewrite U_addc; [reflexivity | exact V1 | lia | lia]. }
  assert (A16 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-680))) + 16)%bv = bv_unsigned sp - 664).
  { rewrite (U_bvadd _ _ _ _ A0 u16) by lia. lia. }
  exists (eval rho (SAlu ALU_SUB (SAlu ALU_ADD (SVar 1) (SLit (-553))) (SVar 90))), (eval rho (SVar 90)), (eval rho (SLit 0)), (eval rho (SLit 0)).
  apply and7_tail; [tsz|].
  split; [eapply (iov_field rho CB3 tr ms md (-680)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field rho CB3 tr ms md (-672)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split; [eapply (iov_field rho CB3 tr ms md (-664)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C3 | lia | lia]|].
  split; [eapply (iov_field rho CB3 tr ms md (-656)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C4 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
  split.
  { rewrite <- (BL_input_eval rho). apply (read_bytes_map_of_rd ms _ _ L0); [subst L0; change (eval rho (SVar 90)) with (rw rho 90); lia|].
    replace (eval rho (SAlu ALU_SUB (SAlu ALU_ADD (SVar 1) (SLit (-553))) (SVar 90)))
      with (Z_to_bv 64 (bv_unsigned sp - 560) + Z_to_bv 64 (Z.of_nat (7 - L0)))%bv.
    - apply rd_bytes_skip. replace (7 - L0 + L0)%nat with 7%nat by lia. eapply ibuf_read; eauto.
    - apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite mod64, <- Z.add_mod, Z.mod_small by lia.
      symmetry. erewrite (U_sub2 rho _ _ (bv_unsigned sp - 553) (bv_unsigned (rw rho 90))); [lia | | reflexivity | lia].
      apply (U_addc rho (SVar 1) (-553) (bv_unsigned sp)); [exact V1 | lia | lia]. }
  split; [reflexivity|].
  change (eval rho (SVar 90)) with (rw rho 90). rewrite app_nil_r, length_skipn, M2_len. lia.
Qed.

Lemma MSG_skip7 : ltac2:(tb__ "0|1|
S30S3cR1U7A2S0S2dS38Q8A1M0A1Sa6G0R2S51A3S37G0Sa6G0R2ScaSc2Sc1S2bS2fS2bS2fS2bS2bS2bS2fA8Sc2Sc1S2bS2bS2fS2fS2bS2bS2bS2fA8Sc2Sc1S2bS2fS2fS2fS2fS2bS2bS2fA8Sc2Sc1S2bS2bS2bS2fS2fS2bS2bS2fA8Sc2Sc1S2bS2fS2bS2fS2fS2bS2bS2fA8Sc2Sc1S2fS2bS2fS2bS2bS2bS2fS2fA8Sc2Sc1S2fS2fS2fS2fS2fS2bS2fS2fA8Sc3A2A2A2A2A2A2A2A1A3S37G0Vargv0;S57A3A3A3F_;Fc;").
Proof using Hargc.
  intros c Hc. unfold MSG, M1. rewrite <- app_assoc.
  destruct c as [|[|[|[|[|[|[|[|c]]]]]]]]; try reflexivity. lia.
Qed.
Lemma MSG_skipA : ltac2:(tb__ "0|1|
S30S3cR1S2eS38Q8A1M0Vargv0;A2A2S0S2dG0A1Sa6G0Sa4U7R2A2S51A3S37G0Sa6G0R2Vargv0;A3S57A3A3F_;Fd;").
Proof using Hargc.
  intros d Hd. unfold MSG, M1. rewrite <- app_assoc. cbn [skipn Nat.add app str].
  rewrite skipn_app. replace (d - length argv0)%nat with 0%nat by lia. reflexivity.
Qed.

Definition L0_of (rho : valuation) : nat := Z.to_nat (bv_unsigned (rw rho 67)).
Definition R_of (rho : valuation) : nat := Z.to_nat (bv_unsigned (rw rho 68)).
Definition QD1 : assn := Q_at D1 (length M1).

Lemma loop1 : ltac2:(tb__ "0|4|
S3cU4aS2eS38Q8A1Vargv0;A2M0A2S30S1S7S50R1A1M1S3cS5fR2A1U6A2S3cSa4S5fR3A1G0A2R4A2S83S2aVok;S4bS2aS4eS4fSa5U7M2S5fR4A1A2A1Vmd0;A2SafR4A4S59A4F_;F_;F_;Frho;S7G1S1S3cU1S66R2A1M3A2S3dG3G0A2A2S3cS66R3A1R4A2S83S2aVok;S4bS2aS4eS4fSa5Sa4G2G0A2S66R4A1A2A1Vmd0;A2SaeR4A4S59A4F_;F_;F_;Frho;A2Fm;F_;").
Proof using Hargc Hent Hfd2 Hinp HokK HokP.
  intros Hlen74. induction m as [|m IH].
  { split; intros rho HG H1 H2; exfalso; lia. }
  destruct IH as [IH2 IH1]. pose proof NU as NU'.
  destruct cert_CB2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R22b & Hib & H17b & H10b & H12b & Hnxb & HinFb).
  destruct cert_CB1 as (_ & _ & _ & _ & _ & _ & R22c & Hic & H17c & H10c & H12c & Hnxc & HinFc1 & HinFc2).
  split.
  -
    intros rho HG HL0 Hm.
    assert (HU67 : 0 <= bv_unsigned (rw rho 67) <= 6) by (pose proof (urange (rw rho 67)); unfold L0_of in HL0; lia).
    eapply triple_seq.
    { apply (writev_site2 CB2 (reg_sv CB2 22) (7 - L0_of rho) (skipn (7 - L0_of rho) (str "usage: ")) argv0 rho HG);
        [rewrite Hnxb; lia | exact Hib | exact H17b | exact H10b | exact H12b | rewrite R22b, Hnxb; reflexivity | | |].
      + rewrite MSG_skip7 by lia. rewrite app_assoc, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
      + rewrite length_app, length_skipn. cbn [length str]. unfold MAX_RW_COUNT. lia.
      + intros tr ms md Hsp. exact (bytes_CB2 rho tr ms md HG Hsp). }
    apply triple_ex; intros rho1. apply triple_ex; intros k.
    apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
    rewrite Hnxb in Hk, Hag1. rewrite length_app, length_skipn in Hkb. cbn [length str] in Hkb.
    assert (E67 : rw rho1 67 = rw rho 67) by (symmetry; apply (proj1 Hag1); lia).
    assert (U71 : bv_unsigned (rw rho1 71) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
    pose proof (G_v5 rho1 HG1) as V5.

    eapply triple_conseq with (P := SP segs (Kx (TR (7 - L0_of rho + k)) md0) PB2 rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. apply SP_add1; [exact Hw | | reflexivity]. cbn [holds]. change (eval rho1 (SVar 71)) with (rw rho1 71). rewrite U71, U_lit64 by lia. lia. }
    destruct (Nat.le_gt_cases k (L0_of rho)) as [Hle|Hgt].
    +
      eapply triple_conseq with (P := SP segs (Kx (TR (7 - L0_of rho + k)) md0) PB2a rho1); [| intros w Hw; exact Hw |].
      { intros w Hw. apply SP_add1; [exact Hw | | reflexivity]. cbn [holds]. change (eval rho1 (SVar 71)) with (rw rho1 71).
        change (eval rho1 (SVar 67)) with (rw rho1 67). rewrite U71, E67. unfold L0_of in Hle. lia. }
      eapply run_tr; [exact run_PB2a | reflexivity | apply okf |].
      intros L rho2 [<-|[]] Hag2. cbn [lf_state].
      assert (EL : L0_of (rho_sub rho2 s_PB2a_CB2) = (L0_of rho - k)%nat).
      { unfold L0_of. cbn [rho_sub rw]. rewrite sv_PB2a_67.
        erewrite U_sub2; [| reflexivity | reflexivity |]; change (eval rho2 (SVar 67)) with (rw rho2 67); change (eval rho2 (SVar 71)) with (rw rho2 71);
          rewrite <- (proj1 Hag2 67%positive ltac:(cbn; lia)), <- (proj1 Hag2 71%positive ltac:(cbn; lia)), E67, U71; unfold L0_of in Hle; lia. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH2 (rho_sub rho2 s_PB2a_CB2))].
      * intros w Hw. eapply SP_entails in Hw; [|exact ent_PB2a_CB2].
        replace (7 - L0_of (rho_sub rho2 s_PB2a_CB2))%nat with (7 - L0_of rho + k)%nat by lia. exact Hw.
      * apply Good_sub; [reflexivity|]. eapply Good_agree; [exact Hag2 | cbn; lia | exact HG1].
      * lia.
      * lia.
    +
      eapply triple_conseq with (P := SP segs (Kx (TR (7 - L0_of rho + k)) md0) PB2b rho1); [| intros w Hw; exact Hw |].
      { intros w Hw. apply SP_add1; [exact Hw | | reflexivity]. cbn [holds]. change (eval rho1 (SVar 71)) with (rw rho1 71).
        erewrite U_addc; [| reflexivity | |]; change (eval rho1 (SVar 67)) with (rw rho1 67); rewrite ?U71, ?E67; unfold L0_of in Hgt; pose proof (urange (rw rho 67)); lia. }
      eapply run_tr; [exact run_PB2b | reflexivity | apply okf |].
      intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
      *
        eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
        intros w Hw. pose proof (hd_fact rho2 L_PB2b_0 _ _ w _ eq_refl Hw) as Hf.
        cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
        erewrite (U_add2 rho2 (SVar 5) (SVar 67)) in Hf; [| reflexivity | reflexivity |];
          change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 67)) with (rw rho2 67) in *; change (eval rho2 (SVar 71)) with (rw rho2 71) in *.
        2:{ rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)), <- (proj1 Hag2 67%positive ltac:(cbn; lia)), V5, E67. lia. }
        rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)), <- (proj1 Hag2 67%positive ltac:(cbn; lia)), <- (proj1 Hag2 71%positive ltac:(cbn; lia)), V5, E67, U71 in Hf.
        exists (rho_sub rho2 s_PB2b_D1). split.
        { apply Good_sub; [reflexivity|]. eapply Good_agree; [exact Hag2 | cbn; lia | exact HG1]. }
        eapply SP_entails in Hw; [|exact ent_PB2b_D1].
        replace (length M1) with (7 - L0_of rho + k)%nat; [exact Hw|]. rewrite M1_len. unfold L0_of in *. unfold N0 in Hf. lia.
      *
        apply triple_facts. intros HF. apply Forall_cons_iff in HF as [Hf _].
        cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Z.eqb_eq in Hf.
        erewrite (U_add2 rho2 (SVar 5) (SVar 67)) in Hf; [| reflexivity | reflexivity |];
          change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 67)) with (rw rho2 67) in *; change (eval rho2 (SVar 71)) with (rw rho2 71) in *.
        2:{ rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)), <- (proj1 Hag2 67%positive ltac:(cbn; lia)), V5, E67. lia. }
        rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)), <- (proj1 Hag2 67%positive ltac:(cbn; lia)), <- (proj1 Hag2 71%positive ltac:(cbn; lia)), V5, E67, U71 in Hf.
        assert (ER : R_of (rho_sub rho2 s_PB2b_CB1) = (length argv0 + L0_of rho - k)%nat).
        { unfold R_of, L0_of. cbn [rho_sub rw]. rewrite sv_PB2b_68.
          unfold L0_of in Hgt, Hkb.
          erewrite (U_sub2 rho2 (SVar 5) _ N0 (Z.of_nat k - bv_unsigned (rw rho 67))); [unfold N0; lia | | | unfold N0 in *; lia].
          - change (eval rho2 (SVar 5)) with (rw rho2 5). rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)). exact V5.
          - erewrite U_sub2; [reflexivity | | | lia]; change (eval rho2 (SVar 71)) with (rw rho2 71); change (eval rho2 (SVar 67)) with (rw rho2 67);
              rewrite <- ?(proj1 Hag2 71%positive ltac:(cbn; lia)), <- ?(proj1 Hag2 67%positive ltac:(cbn; lia)), ?U71, ?E67; reflexivity. }
        eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH1 (rho_sub rho2 s_PB2b_CB1))].
        -- intros w Hw. eapply SP_entails in Hw; [|exact ent_PB2b_CB1].
           replace (7 + length argv0 - R_of (rho_sub rho2 s_PB2b_CB1))%nat with (7 - L0_of rho + k)%nat by (unfold L0_of, N0 in *; lia). exact Hw.
        -- apply Good_sub; [reflexivity|]. eapply Good_agree; [exact Hag2 | cbn; lia | exact HG1].
        -- unfold L0_of, N0 in *. lia.
        -- unfold L0_of, N0 in *. lia.
  -
    intros rho HG HR Hm.
    eapply triple_seq.
    { apply (writev_site1 CB1 (reg_sv CB1 22) (7 + length argv0 - R_of rho) (skipn (length argv0 - R_of rho) argv0) rho HG);
        [rewrite Hnxc; lia | exact Hic | exact H17c | exact H10c | exact H12c | rewrite R22c, Hnxc; reflexivity | | |].
      + replace (7 + length argv0 - R_of rho)%nat with (7 + (length argv0 - R_of rho))%nat by lia.
        rewrite MSG_skipA by lia. rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
      + rewrite length_skipn. unfold MAX_RW_COUNT. lia.
      + intros tr ms md Hsp. exact (proj2 (bytes_CB1 rho tr ms md HG Hsp)). }
    apply triple_ex; intros rho1. apply triple_ex; intros k.
    apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
    rewrite Hnxc in Hk, Hag1. rewrite length_skipn in Hkb.
    assert (E68 : rw rho1 68 = rw rho 68) by (symmetry; apply (proj1 Hag1); lia).
    assert (U72 : bv_unsigned (rw rho1 72) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
    assert (HU68 : bv_unsigned (rw rho 68) = Z.of_nat (R_of rho)) by (unfold R_of; pose proof (urange (rw rho 68)); lia).
    pose proof (G_v5 rho1 HG1) as V5.

    eapply triple_conseq with (P := SP segs (Kx (TR (7 + length argv0 - R_of rho + k)) md0) PB1 rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. apply SP_add1; [exact Hw | | reflexivity]. cbn [holds]. change (eval rho1 (SVar 72)) with (rw rho1 72). rewrite U72, U_lit64 by lia. lia. }
    eapply run_tr; [exact run_PB1 | reflexivity | apply okf |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
    +
      eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
      intros w Hw. pose proof (hd_fact rho2 L_PB1_0 _ _ w _ eq_refl Hw) as Hf.
      cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
      change (eval rho2 (SVar 72)) with (rw rho2 72) in Hf. change (eval rho2 (SVar 68)) with (rw rho2 68) in Hf.
      rewrite <- (proj1 Hag2 72%positive ltac:(cbn; lia)), <- (proj1 Hag2 68%positive ltac:(cbn; lia)), U72, E68, HU68 in Hf.
      exists (rho_sub rho2 s_PB1_D1). split.
      { apply Good_sub; [reflexivity|]. eapply Good_agree; [exact Hag2 | cbn; lia | exact HG1]. }
      eapply SP_entails in Hw; [|exact ent_PB1_D1].
      replace (length M1) with (7 + length argv0 - R_of rho + k)%nat; [exact Hw|]. rewrite M1_len. lia.
    +
      apply triple_facts. intros HF. apply Forall_cons_iff in HF as [Hf _].
      cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Z.eqb_eq in Hf.
      change (eval rho2 (SVar 72)) with (rw rho2 72) in Hf. change (eval rho2 (SVar 68)) with (rw rho2 68) in Hf.
      rewrite <- (proj1 Hag2 72%positive ltac:(cbn; lia)), <- (proj1 Hag2 68%positive ltac:(cbn; lia)), U72, E68, HU68 in Hf.
      assert (ER : R_of (rho_sub rho2 s_PB1_CB1) = (R_of rho - k)%nat).
      { unfold R_of at 1. cbn [rho_sub rw]. rewrite sv_PB1_68.
        erewrite U_sub2; [| reflexivity | reflexivity |]; change (eval rho2 (SVar 68)) with (rw rho2 68); change (eval rho2 (SVar 72)) with (rw rho2 72);
          rewrite <- (proj1 Hag2 68%positive ltac:(cbn; lia)), <- (proj1 Hag2 72%positive ltac:(cbn; lia)), E68, U72, HU68; lia. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH1 (rho_sub rho2 s_PB1_CB1))].
      * intros w Hw. eapply SP_entails in Hw; [|exact ent_PB1_CB1].
        replace (7 + length argv0 - R_of (rho_sub rho2 s_PB1_CB1))%nat with (7 + length argv0 - R_of rho + k)%nat by lia. exact Hw.
      * apply Good_sub; [reflexivity|]. eapply Good_agree; [exact Hag2 | cbn; lia | exact HG1].
      * lia.
      * lia.
Qed.

Lemma L_sess1 : ltac2:(tb__ "0|0|
S3cU4aS2eS38Q8A1Vargv0;A2A2S7S50R1A1S83S2aVok;S4bS2aS4eS4fU0A1Vmd0;A2SacR2A4S59A4F_;Frho;F_;").
Proof using Hargc Hent Hfd2 Hinp HokK HokP.
  intros Hlen74 rho HG. pose proof NU as NU'.
  destruct cert_E_A1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R22 & Hi & H17 & H10 & H12 & Hnx).
  eapply triple_seq.
  { apply (writev_site2 E_A1 (reg_sv E_A1 22) 0 (str "usage: ") argv0 rho HG);
      [rewrite Hnx; lia | exact Hi | exact H17 | exact H10 | exact H12 | rewrite R22, Hnx; reflexivity | | |].
    + change (skipn 0 MSG) with (M1 ++ M2). unfold M1. rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
    + rewrite length_app. cbn [length str]. unfold MAX_RW_COUNT. lia.
    + intros tr ms md Hsp. exact (bytes_E_A1 rho tr ms md HG Hsp). }
  apply triple_ex; intros rho1. apply triple_ex; intros k.
  apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
  rewrite Hnx in Hk, Hag1. rewrite length_app in Hkb. cbn [length str] in Hkb.
  assert (U67 : bv_unsigned (rw rho1 67) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
  pose proof (G_v5 rho1 HG1) as V5.
  change (S_after_write E_A1 (reg_sv E_A1 22)) with PA1. cbn [Nat.add].
  destruct (Nat.le_gt_cases k 7) as [Hle|Hgt].
  -
    eapply triple_conseq with (P := SP segs (Kx (TR k) md0) PA1a rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. apply SP_add1; [exact Hw | | reflexivity]. cbn [holds]. change (eval rho1 (SVar 67)) with (rw rho1 67). rewrite U67, U_lit64 by lia. lia. }
    eapply run_tr; [exact run_PA1a | reflexivity | apply okf |].
    intros L rho2 [<-|[]] Hag2. cbn [lf_state].
    assert (EL : L0_of (rho_sub rho2 s_PA1a_CB2) = (7 - k)%nat).
    { unfold L0_of. cbn [rho_sub rw]. rewrite sv_PA1a_67.
      erewrite U_sub2; [| apply U_lit64; lia | reflexivity |]; change (eval rho2 (SVar 67)) with (rw rho2 67);
        rewrite <- (proj1 Hag2 67%positive ltac:(cbn; lia)), U67; lia. }
    eapply triple_conseq; [| intros w Hw; exact Hw | apply (proj1 (loop1 Hlen74 (7 - k + length argv0)) (rho_sub rho2 s_PA1a_CB2))].
    + intros w Hw. eapply SP_entails in Hw; [|exact ent_PA1a_CB2].
      replace (7 - L0_of (rho_sub rho2 s_PA1a_CB2))%nat with k by lia. exact Hw.
    + apply Good_sub; [reflexivity|]. eapply Good_agree; [exact Hag2 | cbn; lia | exact HG1].
    + lia.
    + lia.
  -
    eapply triple_conseq with (P := SP segs (Kx (TR k) md0) PA1b rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. apply SP_add1; [exact Hw | | reflexivity]. cbn [holds]. change (eval rho1 (SVar 67)) with (rw rho1 67). rewrite U67, U_lit64 by lia. lia. }
    eapply run_tr; [exact run_PA1b | reflexivity | apply okf |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
    +
      apply triple_facts. intros HF. apply Forall_cons_iff in HF as [Hf _].
      cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Bool.negb_true_iff in Hf. apply Z.eqb_neq in Hf.
      erewrite (U_addc rho2 (SVar 5) 7) in Hf; [| reflexivity | |];
        change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 67)) with (rw rho2 67) in *.
      2,3: rewrite <- ?(proj1 Hag2 5%positive ltac:(cbn; lia)), ?V5; unfold N0; lia.
      rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)), <- (proj1 Hag2 67%positive ltac:(cbn; lia)), V5, U67 in Hf.
      assert (ER : R_of (rho_sub rho2 s_PA1b_CB1) = (length argv0 + 7 - k)%nat).
      { unfold R_of. cbn [rho_sub rw]. rewrite sv_PA1b_68.
        erewrite (U_sub2 rho2 (SVar 5) _ N0 (Z.of_nat k - 7)); [unfold N0; lia | | | unfold N0 in *; lia].
        - change (eval rho2 (SVar 5)) with (rw rho2 5). rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)). exact V5.
        - erewrite U_addc; [reflexivity | | lia | lia]. change (eval rho2 (SVar 67)) with (rw rho2 67).
          rewrite <- (proj1 Hag2 67%positive ltac:(cbn; lia)). exact U67. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (proj2 (loop1 Hlen74 (length argv0 + 7 - k)) (rho_sub rho2 s_PA1b_CB1))].
      * intros w Hw. eapply SP_entails in Hw; [|exact ent_PA1b_CB1].
        replace (7 + length argv0 - R_of (rho_sub rho2 s_PA1b_CB1))%nat with k by lia. exact Hw.
      * apply Good_sub; [reflexivity|]. eapply Good_agree; [exact Hag2 | cbn; lia | exact HG1].
      * unfold N0 in Hf. lia.
      * lia.
    +
      eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
      intros w Hw. pose proof (hd_fact rho2 L_PA1b_1 _ _ w _ eq_refl Hw) as Hf.
      cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Bool.negb_true_iff, Z.eqb_neq in Hf.
      erewrite (U_addc rho2 (SVar 5) 7) in Hf; [| reflexivity | |];
        change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 67)) with (rw rho2 67) in *.
      2,3: rewrite <- ?(proj1 Hag2 5%positive ltac:(cbn; lia)), ?V5; unfold N0; lia.
      rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)), <- (proj1 Hag2 67%positive ltac:(cbn; lia)), V5, U67 in Hf.
      exists (rho_sub rho2 s_PA1b_D1). split.
      { apply Good_sub; [reflexivity|]. eapply Good_agree; [exact Hag2 | cbn; lia | exact HG1]. }
      eapply SP_entails in Hw; [|exact ent_PA1b_D1].
      replace (length M1) with k; [exact Hw|]. rewrite M1_len. unfold N0 in Hf. lia.
Qed.

Definition QD2 : assn := Q_at D2 (length MSG).
Definition L0' (rho : valuation) : nat := Z.to_nat (bv_unsigned (rw rho 90)).

Lemma L_D1 : ltac2:(tb__ "0|1|
S7S50R1A1S83S2aVok;S4bS2aS4eS4fS2eS38Q8A1S53A2M0A1Vmd0;A2Sb3R2A4S58SadG0A2A4F_;Frho;").
Proof using Hargc HokK.
  intros rho HG. eapply run_tr; [exact run_D1 | reflexivity | apply okf |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hw. exists rho1. split; [exact (Good_agree _ _ _ Hag1 ltac:(cbn; lia) HG) | exact Hw].
Qed.

Lemma MSG_skipB : ltac2:(tb__ "0|1|
S30S3cR1U7A2S0S2dS38Q8A1M0A1Sa6G0Sa4S2eG0S53A2R2A2S51A3Sa6G0R2S57A3A3F_;Fc;").
Proof using Hargc. intros c Hc. unfold MSG. rewrite skipn_app, skipn_all2 by lia. replace (length M1 + c - length M1)%nat with c by lia. reflexivity. Qed.

Lemma loop2 : ltac2:(tb__ "0|1|
S30S7S50R1A1S1S3cU1S5eR2A1M0A2S3cG0U6A2A2S3cS5eR3A1R4A2S83S2aVok;S4bS2aS4eS4fSa5Sa4S2eS38Q8A1S53A2U7A2S5eR4A1A2A1Vmd0;A2Sb0R4A4S63A4F_;F_;F_;Frho;Fm;").
Proof using Hargc Hent Hfd2 Hinp HokK HokP.
  induction m as [|m IH]; intros rho HG HL Hm; [exfalso; lia|]. pose proof NU as NU'.
  destruct cert_CB3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R22 & Hi & H17 & H10 & H12 & Hnx & _).
  assert (HU90 : bv_unsigned (rw rho 90) = Z.of_nat (L0' rho)) by (unfold L0'; pose proof (urange (rw rho 90)); lia).
  eapply triple_seq.
  { apply (writev_site2 CB3 (reg_sv CB3 22) (length M1 + 7 - L0' rho) (skipn (7 - L0' rho) M2) [] rho HG);
      [rewrite Hnx; lia | exact Hi | exact H17 | exact H10 | exact H12 | rewrite R22, Hnx; reflexivity | | |].
    + rewrite app_nil_r. replace (length M1 + 7 - L0' rho)%nat with (length M1 + (7 - L0' rho))%nat by lia.
      rewrite MSG_skipB by lia. rewrite firstn_all. reflexivity.
    + rewrite app_nil_r, length_skipn, M2_len. unfold MAX_RW_COUNT. lia.
    + intros tr ms md Hsp. exact (proj2 (bytes_CB3 rho tr ms md HG Hsp)). }
  apply triple_ex; intros rho1. apply triple_ex; intros k.
  apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
  rewrite Hnx in Hk, Hag1. rewrite app_nil_r, length_skipn, M2_len in Hkb.
  assert (E90 : rw rho1 90 = rw rho 90) by (symmetry; apply (proj1 Hag1); lia).
  assert (U93 : bv_unsigned (rw rho1 93) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
  change (S_after_write CB3 (reg_sv CB3 22)) with PB3.
  eapply run_tr; [exact run_PB3 | reflexivity | apply okf |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
  -
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. pose proof (hd_fact rho2 L_PB3_0 _ _ w _ eq_refl Hw) as Hf.
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
    change (eval rho2 (SVar 93)) with (rw rho2 93) in Hf. change (eval rho2 (SVar 90)) with (rw rho2 90) in Hf.
    rewrite <- (proj1 Hag2 93%positive ltac:(cbn; lia)), <- (proj1 Hag2 90%positive ltac:(cbn; lia)), U93, E90, HU90 in Hf.
    exists (rho_sub rho2 s_PB3_D2). split.
    { apply Good_sub; [reflexivity|]. eapply Good_agree; [exact Hag2 | cbn; lia | exact HG1]. }
    eapply SP_entails in Hw; [|exact ent_PB3_D2].
    replace (length MSG) with (length M1 + 7 - L0' rho + k)%nat; [exact Hw|]. rewrite MSG_len, M1_len. lia.
  -
    apply triple_facts. intros HF. apply Forall_cons_iff in HF as [Hf _].
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Z.eqb_eq in Hf.
    change (eval rho2 (SVar 93)) with (rw rho2 93) in Hf. change (eval rho2 (SVar 90)) with (rw rho2 90) in Hf.
    rewrite <- (proj1 Hag2 93%positive ltac:(cbn; lia)), <- (proj1 Hag2 90%positive ltac:(cbn; lia)), U93, E90, HU90 in Hf.
    assert (EL : L0' (rho_sub rho2 s_PB3_CB3) = (L0' rho - k)%nat).
    { unfold L0' at 1. cbn [rho_sub rw]. rewrite sv_PB3_90.
      erewrite U_sub2; [| reflexivity | reflexivity |]; change (eval rho2 (SVar 90)) with (rw rho2 90); change (eval rho2 (SVar 93)) with (rw rho2 93);
        rewrite <- (proj1 Hag2 90%positive ltac:(cbn; lia)), <- (proj1 Hag2 93%positive ltac:(cbn; lia)), E90, U93, HU90; lia. }
    eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH (rho_sub rho2 s_PB3_CB3))].
    + intros w Hw. eapply SP_entails in Hw; [|exact ent_PB3_CB3].
      replace (length M1 + 7 - L0' (rho_sub rho2 s_PB3_CB3))%nat with (length M1 + 7 - L0' rho + k)%nat by lia. exact Hw.
    + apply Good_sub; [reflexivity|]. eapply Good_agree; [exact Hag2 | cbn; lia | exact HG1].
    + lia.
    + lia.
Qed.

Lemma L_sess2 : ltac2:(tb__ "0|0|
S7S50R1A1S83S2aVok;S4bS2aS4eS4fS2eS38Q8A1S53A2A1Vmd0;A2SadR2A4S63A4F_;Frho;").
Proof using Hargc Hent Hfd2 Hinp HokK HokP.
  intros rho HG. pose proof NU as NU'.
  destruct cert_E_A2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R22 & Hi & H17 & H10 & H12 & Hnx).
  eapply triple_seq.
  { apply (writev_site2 E_A2 (reg_sv E_A2 22) (length M1) M2 [] rho HG);
      [rewrite Hnx; lia | exact Hi | exact H17 | exact H10 | exact H12 | rewrite R22, Hnx; reflexivity | | |].
    + rewrite app_nil_r. unfold MSG. rewrite skipn_app, skipn_all, Nat.sub_diag. cbn [skipn app]. rewrite firstn_all. reflexivity.
    + rewrite app_nil_r, M2_len. unfold MAX_RW_COUNT. lia.
    + intros tr ms md Hsp. exact (bytes_E_A2 rho tr ms md HG Hsp). }
  apply triple_ex; intros rho1. apply triple_ex; intros k.
  apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
  rewrite Hnx in Hk, Hag1. rewrite app_nil_r, M2_len in Hkb.
  assert (U90 : bv_unsigned (rw rho1 90) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
  change (S_after_write E_A2 (reg_sv E_A2 22)) with PA2.
  eapply run_tr; [exact run_PA2 | reflexivity | apply okf |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
  -
    apply triple_facts. intros HF. apply Forall_cons_iff in HF as [Hf _].
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Bool.negb_true_iff in Hf. apply Z.eqb_neq in Hf.
    change (eval rho2 (SVar 90)) with (rw rho2 90) in Hf. rewrite U_lit64 in Hf by lia.
    rewrite <- (proj1 Hag2 90%positive ltac:(cbn; lia)), U90 in Hf.
    assert (EL : L0' (rho_sub rho2 s_PA2_CB3) = (7 - k)%nat).
    { unfold L0'. cbn [rho_sub rw]. rewrite sv_PA2_90.
      erewrite U_sub2; [| apply U_lit64; lia | reflexivity |]; change (eval rho2 (SVar 90)) with (rw rho2 90);
        rewrite <- (proj1 Hag2 90%positive ltac:(cbn; lia)), U90; lia. }
    eapply triple_conseq; [| intros w Hw; exact Hw | apply (loop2 (7 - k) (rho_sub rho2 s_PA2_CB3))].
    + intros w Hw. eapply SP_entails in Hw; [|exact ent_PA2_CB3].
      replace (length M1 + 7 - L0' (rho_sub rho2 s_PA2_CB3))%nat with (length M1 + k)%nat by lia. exact Hw.
    + apply Good_sub; [reflexivity|]. eapply Good_agree; [exact Hag2 | cbn; lia | exact HG1].
    + lia.
    + lia.
  -
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. pose proof (hd_fact rho2 L_PA2_1 _ _ w _ eq_refl Hw) as Hf.
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Bool.negb_true_iff, Z.eqb_neq in Hf.
    change (eval rho2 (SVar 90)) with (rw rho2 90) in Hf. rewrite U_lit64 in Hf by lia.
    rewrite <- (proj1 Hag2 90%positive ltac:(cbn; lia)), U90 in Hf.
    exists (rho_sub rho2 s_PA2_D2). split.
    { apply Good_sub; [reflexivity|]. eapply Good_agree; [exact Hag2 | cbn; lia | exact HG1]. }
    eapply SP_entails in Hw; [|exact ent_PA2_D2].
    replace (length MSG) with (length M1 + k)%nat; [exact Hw|]. rewrite MSG_len, M1_len. lia.
Qed.

Lemma cert_exit : ltac2:(tb__ "0|0|
S1S0S33S74A1S88S2aS15Sb1A1A2S31S74S75A2A3S1S0S5S8Sb1Z11A2S6Z5eA1A3S0S5S8Sb1ZaA2S6Z2A1A3A2A2").
Proof using . vm_compute. repeat split; reflexivity. Qed.

Lemma L_exit : ltac2:(tb__ "0|0|
S7S50R1A1S83S2aVok;S4bS2aS4eS4fS2eS38Q8A1S51A2A1Vmd0;A2Sb4R2A4S82S3L_;A4F_;Frho;").
Proof using Hargc Hfs HokK HokP Hokh.
  intros rho HG. eapply run_tr; [exact run_D2 | reflexivity | apply okf |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  destruct cert_exit as (Hi & H17 & H10).
  apply (triple_exit_eval segs ok SpecT (Kx (TR (length MSG)) md0) E_exit rho1 2);
    [apply okf | apply okp | exact Hokh | exact Hi | left; exact H17 | rewrite H10; rewrite U_lit64 by lia; reflexivity |].
  intros tr md [-> ->]. rewrite TR_all by lia. rewrite Hfs. exact final_in_spec.
Qed.

Theorem usage74_safe : ltac2:(tb__ "0|0|
S3cU4aS2eS38Q8A1Vargv0;A2A2S7VJI;R1A1S83S2aVok;S4bS2aS4eS35S40A1Vmd0;A2Sd2R2A4S82S3L_;A4F_;Frho;F_;").
Proof using Hargc Hent Hfd2 Hfs Hinp HokK HokP Hokh LEN N0 STR.
  intros Hlen74 rho HJ.
  eapply triple_conseq with (P := fun w => exists rho', Good rho' /\ SP segs (Kx (TR 0) md0) S_use rho' w); [| intros w Hw; exact Hw |].
  { intros w Hw. apply (use_intro rho w HJ). exact Hw. }
  apply triple_ex; intros rho1. apply triple_pure; intros HG1.
  eapply triple_seq; [apply (L_call Hlen74); exact HG1|].
  apply triple_ex; intros rho2. apply triple_pure; intros HG2.
  eapply triple_seq; [apply (L_sess1 Hlen74); exact HG2|].
  apply triple_ex; intros rho3. apply triple_pure; intros HG3.
  eapply triple_seq; [apply L_D1; exact HG3|].
  apply triple_ex; intros rho4. apply triple_pure; intros HG4.
  eapply triple_seq; [apply L_sess2; exact HG4|].
  apply triple_ex; intros rho5. apply triple_pure; intros HG5.
  apply L_exit. exact HG5.
Qed.

Definition EQ_wr (S : sstate) (e : sv) (n len : nat) (rho : valuation) : world -> Prop := ltac2:(tb__ "0|2|
S82S2S7S7S1S50R1A1S1S17S12VS;A1M0Vrho;R1A3S1S0S38Q40M1A1S18R1G0A2S3aG1S7aVlen;A1A2A3S4bS2aS4eS4fSa4Vn;Vlen;A2A1Vmd0;A2SbeVS;Ve;A2R1R2A5A2A2A2Lrho';A2Lw;").

Lemma ewritev_site2 : forall S e n bs1 bs2 rho,
  Good rho -> (26 <= ss_next S)%positive ->
  instr_at segs (ss_pc S) = Some Ecall ->
  reg_sv S 17 = SLit 66 -> reg_sv S 10 = SLit 2 -> reg_sv S 12 = SLit 2 ->
  sv_below (ss_next S) e = true ->
  bs1 ++ bs2 = firstn (length (bs1 ++ bs2)) (skipn n MSG) ->
  (1 <= Z.of_nat (length (bs1 ++ bs2)) <= MAX_RW_COUNT)%Z ->
  (forall tr ms md, smatch_pending segs rho S (tr, mkCfg ms md) ->
     exists b1 l1 b2 l2,
       read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11)) = Some b1
       /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11) + 8)%bv = Some l1
       /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv S 11) + 16)%bv = Some b2
       /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv S 11) + 16) + 8)%bv = Some l2
       /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some bs1
       /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some bs2
       /\ bv_unsigned (eval rho e) = Z.of_nat (length (bs1 ++ bs2))
       /\ (bv_unsigned (eval rho (reg_sv S 11)) + 32 <= TASK_SIZE)%Z
       /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
       /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z) ->
  etriple segs (SP segs (Kx (TR n) md0) S rho) (EQ_wr S e n (length (bs1 ++ bs2)) rho).
Proof using Hargc Hfd2.
  intros S e n bs1 bs2 rho HG Hn Hi H17 H10 H12 He Hbs Hlen Hrd.
  set (J' := fun (r : valuation) (tr : list event) (md : Model) =>
               exists k, rw r (ss_next S) = Z_to_bv 64 (Z.of_nat k) /\ (1 <= k <= length (bs1 ++ bs2))%nat
                         /\ tr = TR (n + k) /\ md = md0).
  eapply etriple_conseq; [intros w Hw; exact Hw | |
    eapply (etriple_writev2J segs (liftK (Kx (TR n) md0)) J' S rho 2 bs1 bs2 e);
      [exact Hi | exact H17 | exact H10 | exact H12 | lia | exact Hlen | exact He | | ]].
  - intros w (rho' & Hag & Hlen' & Hsm & (k & Hk & Hkb & Htr & Hmd)). exists rho'.
    split; [exact (Good_agree _ _ _ Hag Hn HG)|]. split; [exact Hag|]. split; [exact Hlen'|].
    assert (Ek : k = length (bs1 ++ bs2)).
    { rewrite Hlen' in Hk. apply (f_equal bv_unsigned) in Hk. rewrite !Z_to_bv_small in Hk by (rewrite mod64; unfold MAX_RW_COUNT in Hlen; lia). lia. }
    subst k. split; [exact Hsm|]. split; [exact Htr | exact Hmd].
  - intros rho' tr md k Hag Hk [-> ->] Hkb. split; [exact Hfd2|]. exists k. split; [exact Hk|]. split; [exact Hkb|].
    split; [|reflexivity]. rewrite Hbs, firstn_firstn, Nat.min_l by lia. apply TR_app.
  - intros tr ms md Hsp _. exact (Hrd tr ms md Hsp).
Qed.

Lemma eL_call : ltac2:(tb__ "0|1|
S3cU4aS2eS38Q8A1Vargv0;A2A2S7S50R1A1S84S2aS4bS2aS4eS4fU0M0A1Vmd0;A2Sb2R2A4S58SacG0A2A3F_;Frho;F_;").
Proof using Hargc Hent Hinp.
  intros Hlen74 rho HG.
  eapply erun_tr; [exact run_use | reflexivity |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  pose proof (Good_agree _ _ _ Hag1 ltac:(cbn; lia) HG) as HG1.
  apply (ecall_path segs FirstNul (Kx (TR 0) md0) (Kx (TR 0) md0) E_sn E_snX Pre_strnlen xs_pre s_sn R_sn Posts_strnlen _ rho1
           xs_pre_ok efr_sn chk_sn fb_sn).
  - intros rho2 HF. apply strnlen_sum_ex. exact HF.
  - intros ms _. apply FirstNul_call. exact HG1.
  - intros L rho2 [<-|[]] Hag2 HF2. cbn [lf_state]. replace (ss_next Pre_strnlen) with NF by reflexivity. rewrite T_imp_eq.
    pose proof (Good_agree _ _ _ Hag2 ltac:(cbn; lia) HG1) as HG2.
    apply (epost_path segs (Kx (TR 0) md0) T_imp T_sn (ss_facts E_sn) xs_post rho2 _ fb_sn2 xs_post_ok HF2).
    apply etriple_facts. intros HFT.
    eapply etriple_conseq with (P := SP segs (Kx (TR 0) md0) T_sn74 rho2); [| intros w Hw; exact Hw |].
    { intros w Hsp. apply SP_add1; [| | reflexivity].
      - eapply (SP_restate segs _ rho2 T_sn T_sn1 w); [exact swf_T_sn1 | exact diff_sn | | constructor | exact Hsp].
        constructor; [|constructor]. cbn [fst snd]. exact (proj1 (Forall_forall _ _) HFT _ fact_T_sn).
      - cbn [holds]. rewrite U_lit64 by lia. change (eval rho2 (SVar 5)) with (rw rho2 5). rewrite (G_v5 rho2 HG2). unfold N0. lia. }
    eapply erun_tr; [exact run2 | reflexivity |].
    intros L rho3 [<-|[<-|[]]] Hag3; cbn [lf_state].
    + intros w Hw. exfalso. exact (ovf_contra rho3 w (Good_agree _ _ _ Hag3 ltac:(cbn; lia) HG2) Hw).
    + intros w Hw. exists w. split; [apply wsteps_refl|]. exists rho3. split; [exact (Good_agree _ _ _ Hag3 ltac:(cbn; lia) HG2) | exact Hw].
Qed.

Lemma eL_sess1 : ltac2:(tb__ "0|0|
S3cU4aS2eS38Q8A1Vargv0;A2A2S7S50R1A1S84S2aS4bS2aS4eS4fU0A1Vmd0;A2SacR2A4S59A3F_;Frho;F_;").
Proof using Hargc Hent Hfd2 Hinp.
  intros Hlen74 rho HG. pose proof NU as NU'.
  destruct cert_E_A1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R22 & Hi & H17 & H10 & H12 & Hnx).
  eapply etriple_seq.
  { apply (ewritev_site2 E_A1 (reg_sv E_A1 22) 0 (str "usage: ") argv0 rho HG);
      [rewrite Hnx; lia | exact Hi | exact H17 | exact H10 | exact H12 | rewrite R22, Hnx; reflexivity | | |].
    + change (skipn 0 MSG) with (M1 ++ M2). unfold M1. rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
    + rewrite length_app. cbn [length str]. unfold MAX_RW_COUNT. lia.
    + intros tr ms md Hsp. exact (bytes_E_A1 rho tr ms md HG Hsp). }
  apply etriple_ex; intros rho1.
  apply etriple_pure; intros HG1. apply etriple_pure; intros Hag1. apply etriple_pure; intros Hk.
  rewrite Hnx in Hk, Hag1. rewrite length_app in Hk |- *. cbn [length str] in Hk |- *.
  assert (U67 : bv_unsigned (rw rho1 67) = 7 + N0) by (rewrite Hk; rewrite Z_to_bv_small by (rewrite mod64; lia); unfold N0; lia).
  pose proof (G_v5 rho1 HG1) as V5.
  change (S_after_write E_A1 (reg_sv E_A1 22)) with PA1. cbn [Nat.add].
  eapply etriple_conseq with (P := SP segs (Kx (TR (7 + length argv0)) md0) PA1b rho1); [| intros w Hw; exact Hw |].
  { intros w Hw. apply SP_add1; [exact Hw | | reflexivity]. cbn [holds]. change (eval rho1 (SVar 67)) with (rw rho1 67). rewrite U67, U_lit64 by lia. unfold N0. lia. }
  eapply erun_tr; [exact run_PA1b | reflexivity |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
  -
    apply etriple_facts. intros HF. apply Forall_cons_iff in HF as [Hf _]. exfalso.
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Bool.negb_true_iff in Hf. apply Z.eqb_neq in Hf. apply Hf.
    erewrite (U_addc rho2 (SVar 5) 7); [| reflexivity | |];
      change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 67)) with (rw rho2 67) in *.
    2,3: rewrite <- ?(proj1 Hag2 5%positive ltac:(cbn; lia)), ?V5; unfold N0; lia.
    rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)), <- (proj1 Hag2 67%positive ltac:(cbn; lia)), V5, U67. lia.
  - intros w Hw. exists w. split; [apply wsteps_refl|]. exists (rho_sub rho2 s_PA1b_D1). split.
    { apply Good_sub; [reflexivity|]. eapply Good_agree; [exact Hag2 | cbn; lia | exact HG1]. }
    eapply SP_entails in Hw; [|exact ent_PA1b_D1]. rewrite M1_len. exact Hw.
Qed.

Lemma eL_D1 : ltac2:(tb__ "0|1|
S7S50R1A1S84S2aS4bS2aS4eS4fS2eS38Q8A1S53A2M0A1Vmd0;A2Sb3R2A4S58SadG0A2A3F_;Frho;").
Proof using Hargc.
  intros rho HG. eapply erun_tr; [exact run_D1 | reflexivity |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state]. intros w Hw. exists w. split; [apply wsteps_refl|].
  exists rho1. split; [exact (Good_agree _ _ _ Hag1 ltac:(cbn; lia) HG) | exact Hw].
Qed.

Lemma eL_sess2 : ltac2:(tb__ "0|0|
S7S50R1A1S84S2aS4bS2aS4eS4fS2eS38Q8A1S53A2A1Vmd0;A2SadR2A4S63A3F_;Frho;").
Proof using Hargc Hent Hfd2 Hinp.
  intros rho HG. pose proof NU as NU'.
  destruct cert_E_A2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R22 & Hi & H17 & H10 & H12 & Hnx).
  eapply etriple_seq.
  { apply (ewritev_site2 E_A2 (reg_sv E_A2 22) (length M1) M2 [] rho HG);
      [rewrite Hnx; lia | exact Hi | exact H17 | exact H10 | exact H12 | rewrite R22, Hnx; reflexivity | | |].
    + rewrite app_nil_r. unfold MSG. rewrite skipn_app, skipn_all, Nat.sub_diag. cbn [skipn app]. rewrite firstn_all. reflexivity.
    + rewrite app_nil_r, M2_len. unfold MAX_RW_COUNT. lia.
    + intros tr ms md Hsp. exact (bytes_E_A2 rho tr ms md HG Hsp). }
  apply etriple_ex; intros rho1.
  apply etriple_pure; intros HG1. apply etriple_pure; intros Hag1. apply etriple_pure; intros Hk.
  rewrite Hnx in Hk, Hag1. rewrite app_nil_r, M2_len in Hk |- *.
  assert (U90 : bv_unsigned (rw rho1 90) = 7) by (rewrite Hk; reflexivity).
  change (S_after_write E_A2 (reg_sv E_A2 22)) with PA2.
  eapply erun_tr; [exact run_PA2 | reflexivity |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
  - apply etriple_facts. intros HF. apply Forall_cons_iff in HF as [Hf _]. exfalso.
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Bool.negb_true_iff in Hf. apply Z.eqb_neq in Hf. apply Hf.
    change (eval rho2 (SVar 90)) with (rw rho2 90). rewrite U_lit64 by lia.
    rewrite <- (proj1 Hag2 90%positive ltac:(cbn; lia)). exact U90.
  - intros w Hw. exists w. split; [apply wsteps_refl|]. exists (rho_sub rho2 s_PA2_D2). split.
    { apply Good_sub; [reflexivity|]. eapply Good_agree; [exact Hag2 | cbn; lia | exact HG1]. }
    eapply SP_entails in Hw; [|exact ent_PA2_D2]. rewrite MSG_len. rewrite M1_len in Hw. replace (14 + length argv0)%nat with (7 + length argv0 + 7)%nat by lia. exact Hw.
Qed.

Lemma eL_exit : ltac2:(tb__ "0|1|
S7S50R1A1S84S2aS4bS2aS4eS4fS2eS38Q8A1S51A2A1Vmd0;A2Sb4R2A4S82S0S2dS40A1S85R1A1S37S40Sc6Z2M0S51A2S32S40Sc7Vfs;G0A2S35S40A1A3A3A3Lw;A3F_;Frho;").
Proof using Hargc Hfs.
  intros rho HG. eapply erun_tr; [exact run_D2 | reflexivity |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  destruct cert_exit as (Hi & H17 & H10).
  eapply etriple_conseq; [intros w Hw; exact Hw | |
    apply (etriple_exit_eval segs (Kx (TR (length MSG)) md0) E_exit rho1 2 Hi (or_introl H17))].
  - intros w (tr & md & [-> ->] & ->). rewrite TR_all by lia. rewrite Hfs. reflexivity.
  - rewrite H10. rewrite U_lit64 by lia. reflexivity.
Qed.

Theorem usage74_exists : ltac2:(tb__ "0|2|
S3cU4aS2eS38Q8A1Vargv0;A2A2S7VJI;R1A1S84S2aS4bS2aS4eS35S40A1M0Vmd0;A2Sd2R2A4S82S0S2dS40A1S85R1A1S37S40Sc6Z2M1Sc8Vargv0;A1A2S32S40Sc7Vfs;G1A2G0A3A3A3Lw;A3F_;Frho;F_;").
Proof using Hargc Hent Hfd2 Hfs Hinp LEN N0 STR.
  intros Hlen74 rho HJ. rewrite <- MSG_usage.
  eapply etriple_conseq with (P := fun w => exists rho', Good rho' /\ SP segs (Kx (TR 0) md0) S_use rho' w); [| intros w Hw; exact Hw |].
  { intros w Hw. apply (use_intro rho w HJ). exact Hw. }
  apply etriple_ex; intros rho1. apply etriple_pure; intros HG1.
  eapply etriple_seq; [apply (eL_call Hlen74); exact HG1|].
  apply etriple_ex; intros rho2. apply etriple_pure; intros HG2.
  eapply etriple_seq; [apply (eL_sess1 Hlen74); exact HG2|].
  apply etriple_ex; intros rho3. apply etriple_pure; intros HG3.
  eapply etriple_seq; [apply eL_D1; exact HG3|].
  apply etriple_ex; intros rho4. apply etriple_pure; intros HG4.
  eapply etriple_seq; [apply eL_sess2; exact HG4|].
  apply etriple_ex; intros rho5. apply etriple_pure; intros HG5.
  apply eL_exit. exact HG5.
Qed.

Definition GoodW (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S1S50Vrho;A1S0S2dS38Q8A1A1S1fVrho;P4A2S51A3A2").
Definition QW_at (S : sstate) (n : nat) : assn := ltac2:(tb__ "0|0|
S82S2S7S7S1S56R1A1S4bS2aS4eS4fVn;A1Vmd0;A2VS;R1R2A5A2Lrho;A2Lw;").

Lemma GoodW_agree : ltac2:(tb__ "0|1|
S3fS7S7S17R3R2R1A3Se2P1aR4A2S56R4A1M0G0F_;F_;F_;Frho';Frho;Fn;").
Proof using Hargc. intros n rho rho' Hag Hn [HG H4]. split; [exact (Good_agree _ _ _ Hag Hn HG)|]. rewrite <- (proj1 (proj2 Hag)). exact H4. Qed.
Lemma GoodW_sub : ltac2:(tb__ "0|0|
Sd8S7S0S2cS67R2A1S2bA3S56R2A1S56Sd7R3R4A2A1F_;F_;Frho;Fs;").
Proof using . intros s rho Hs [HG H4]. split; [exact (Good_sub s rho Hs HG) | cbn [rho_sub rl]; exact H4]. Qed.

Lemma Tn_intro : ltac2:(tb__ "0|1|
S3eS7S82S50R2A1S0S3eVN0;R4A3S0S2cS24S97R5A1A1S2bA3S4bS2aS4eS4fU0A1Vmd0;A2M0Sb8R5R4A5S4bS2aG0S97R7A1R6R5A5F_;F_;F_;F_;Fw;Frho;Fn;").
Proof using Hargc Hent Hinp.
  intros n rho w HG Hn Hwf [Hsm Hk]. split; [|exact Hk]. unfold Tn. apply smatch_subst_intro; [exact Hwf|].
  eapply smatch_agree; [|exact Hsm]. split; [|split; intros; reflexivity].
  intros i _. cbn [rho_sub rw wsub_get]. destruct (Pos.eqb_spec i 5) as [->|Hne]; cbn [eval]; [|reflexivity].
  apply bv_eq. rewrite (G_v5 rho HG), Z_to_bv_small; [lia|]. rewrite mod64. pose proof NU. lia.
Qed.

Lemma bexp_eqb_beval : ltac2:(tb__ "0|0|
S7S6eS6eS0S2cS72R2R1A2S2bA3S0S38Q8A1S70R4R3A2S70R4R2A2A3F_;Fb;Fa;Frho;").
Proof using .
  intros rho [x|l i] [y|l' i'] H; cbn in H |- *; try discriminate.
  - apply Z.eqb_eq in H. apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_modulus 8) with 256. unfold bv_wrap. change (bv_modulus 8) with 256. exact H.
  - apply andb_prop in H as [H1 H2]. apply Pos.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
Lemma list_bexp_eqb_beval : ltac2:(tb__ "0|3|
S7S2dS6eA1M0G0S0S2cSbdS6eS72R2R1A4S2bA3S0S2dS38Q8A1M1A1Sa7S6eG1S70R4A1M2R3A4Sa7S6eG1G2R2A4A3F_;Fl2;Fl1;Frho;").
Proof using .
  intros rho l1. induction l1 as [|a l1 IH]; intros [|b l2] H; cbn in H |- *; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (bexp_eqb_beval rho _ _ H1), (IH _ H2). reflexivity.
Qed.
Lemma map_nth_seq_k : ltac2:(tb__ "0|2|
S2dS38Q8A1M0A1M1S30S30G0S3cSa4R2R3A2S2eG0R4A2A2S0G1Sa7S30G0S30Sa9G0R1R6R3A4Lj;SaaR3R4A2A4Sa8G0R4Sa6G0R3R5A3A3A3F_;Fd;Fk;Fn;Fl;").
Proof using Hargc LEN N0 STR.
  intros l n. induction n as [|n IH]; intros k d Hn; [cbn; rewrite firstn_O; reflexivity|].
  cbn [seq map]. rewrite (IH (S k) d) by lia.
  rewrite <- (nth_skipn_cons l k d) by lia. reflexivity.
Qed.
Lemma map_nth_seq : ltac2:(tb__ "0|2|
S2dS38Q8A1M0A1M1S30G0S3cR2S2eG0R3A2A2S0G1Sa7S30G0S30Sa9G0R1R5R3A4Lj;SaaU0R3A2A4Sa8G0R3R4A3A3F_;Fd;Fn;Fl;").
Proof using Hargc LEN N0 STR. intros l n d Hn. rewrite (map_nth_seq_k l n 0 d) by lia. reflexivity. Qed.
Lemma BLn_eval : ltac2:(tb__ "0|1|
S7S50R1A1S0S2dS38Q8A1M0A1Sa7S6eG0S70R2A1S9fVN0;A1A4S51A3F_;Frho;").
Proof using Hargc Hent Hinp.
  intros rho HG. unfold BLn, MSG, M1, M2. rewrite !map_app, map_map. cbn [beval].
  rewrite (G_rl3 rho HG). unfold N0. rewrite !Nat2Z.id.
  replace (map (fun x : nat => nth (Z.to_nat (Z.of_nat x)) (strs_tail draw inp) (Z_to_bv 8 0)) (seq 0 (length argv0)))
    with (map (fun j : nat => nth j (strs_tail draw inp) (Z_to_bv 8 0)) (seq 0 (length argv0)))
    by (apply map_ext; intros j; rewrite Nat2Z.id; reflexivity).
  rewrite (map_nth_seq (strs_tail draw inp) (length argv0) (Z_to_bv 8 0)) by (pose proof tail_len; pose proof NU; lia).
  rewrite tail_firstn. rewrite <- app_assoc. reflexivity.
Qed.

Lemma check_core_sound : ltac2:(tb__ "0|a|
S3eS33S2dS87A1M0A1M1S0S2cS9bR2R1A2S2bA3S2S87S87S2S87S87S2SfSfS2SbSbS2S2dS6eA1M2G2S1S0S2cS24S97R8A1A1S2bA3S1S0G1R7S31G0S32S87R5S32S87R4S35S87A1A3A3A2A3S1S6bSeSa0S6R8A1M3A1S14S8aR5A1A1A3S1S0S33SfA1SdeS8aR4A1Sa3R8A1A2S31SfR3A2A3S1S0S33SbA1S6cSbS10R3A1U1M4A3S31SbR2A2A3S1S0S5S23R2A1S6N230A1M5A3S1S0S5S22R2A1S6S7dR8Z222A2A1A3S1S0S2cS20S1eR2A1M6A1S2bA3S1S0S2cS21G6A1S2fA3S1S0S33G2A1S71S11R2A1G5Z0S7fS78ZeR8A2A1A4S31G2R1A2A3S1S0S2cSbdS6eS72R1S9fR8A1A4S2bA3S1S0S2cSd1P4M7R3A2S2fA3S1S0S2cS69SddR3G4G7A3M8S98S32S36S3fS5A2S34S3fS5P5G3A4SdbSa1G8S98A3A3M9A3S2bA3S0S2cS9eG9R8A2S2bA3A2A2A2A2A2A2A2A2A2A2A2A2A2Lbl;A2Lo;A2Lwx;A2Lb;A2La;A2F_;Fr;Fn;").
Proof using .
  intros n r H. unfold check_core in H. cbv zeta in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct r as [[|a [|b [|? ?]]]|]; try discriminate.
  cbn [lf0 nth lf_state] in H3, H4.
  destruct (apply_xforms (lf_state b) (xs_ibuf n)) as [wx|] eqn:Ex; [|discriminate].
  apply andb_prop in H4 as [H4 H7]. apply andb_prop in H4 as [H4 H6].
  destruct (nth_error (ss_objs wx) 1) as [o|] eqn:Eo; [|discriminate].
  apply andb_prop in H4 as [H4 Hcb]. apply andb_prop in H4 as [H4 Harr]. apply andb_prop in H4 as [H4 Hwr]. apply andb_prop in H4 as [Hlo Hhi].
  destruct (cells_bytes (ob_cells o) (SLit (-560)) 0 (Z.to_nat (14 + n))) as [bl|] eqn:Ecb; [|discriminate].
  apply andb_prop in H7 as [He Hs].
  apply existsb_exists in H3 as (p & Hp & Ep). apply sprop_eqb_sound in Ep. subst p.
  exists a, b, wx, o, bl. repeat split; auto.
  - apply sv_eqb_sound in Hlo. exact Hlo.
  - apply sv_eqb_sound in Hhi. exact Hhi.
  - destruct (is_arr (ob_dflt o)); [discriminate|reflexivity].
  - destruct (state_has_rl 4 wx); [discriminate|reflexivity].
Qed.

Lemma L_small_pre : ltac2:(tb__ "0|1|
S3eS0S2cS9bR1S89S2aS9aS35S3eA1S97R1A1S2bA5A2S2bA3S0S3eVN0;R2A3S7S50R1A1S83S2aVok;S4bS2aS4eS4fU0M0A1Vmd0;A2S97R5A1R2A4S65S98G0A2A4F_;Frho;F_;F_;Fn;").
Proof using Hargc Hent Hinp HokK.
  intros n Hchk Hn rho HG. pose proof NU as NU'.
  destruct (check_core_sound n _ Hchk) as (a & b & wx & o & bl & Hwf & Hr & HinX & Hx & Ho & Hlo & Hhi & Hwr & Harr & Hcb & Hbl & Hrl & He & Hs).
  eapply run_tr; [exact Hr | reflexivity | apply okf |].
  intros L rho1 [<-|[<-|[]]] Hag1.
  -
    intros m Hg w Hw. exfalso.
    pose proof (SP_fact _ _ _ _ _ Hw HinX) as Hf. unfold BNZ3 in Hf. apply (proj1 (holds_BNZ rho1 (SLit n))) in Hf.
    apply Hf. rewrite <- (proj1 (proj2 Hag1)), (G_rl3 rho HG). rewrite U_lit64 by lia.
    unfold nthb. subst n. unfold N0. rewrite Nat2Z.id, tail_nul. reflexivity.
  - pose proof (Good_agree _ _ _ Hag1 ltac:(unfold Tn; cbn; lia) HG) as HG1.
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w [Hsm Hk].
    pose proof (smatch_xforms segs _ _ _ _ w Hx Hsm) as Hsm2.
    pose proof (smatch_obj_to_list segs rho1 wx w 1 4 o (-560) (n - 546) bl Hsm2 Ho Hlo Hhi ltac:(lia) ltac:(lia) Hwr Harr) as Hsm3.
    replace (n - 546 - -560) with (14 + n) in Hsm3 by lia. specialize (Hsm3 Hcb Hrl).
    set (rho2 := rho_set_rl rho1 4 (map (beval rho1) bl)) in Hsm3.
    set (sW := (5%positive, SLit n) :: infer_sub GLg (obj_to_list wx 1 4) E_Wg) in He, Hs.
    exists (rho_sub rho2 sW). split.
    + assert (HG2 : Good rho2).
      { destruct HG1 as (HJ & H3 & H25). subst rho2. split; [|split; [cbn; exact H3 | cbn; exact H25]].
        destruct HJ; constructor; cbn [rho_set_rl rw rl rm]; auto. }
      unfold sub_ok_n in Hs. apply andb_prop in Hs as [Hs6 Hs5]. apply sv_eqb_sound in Hs5.
      cbn [forallb] in Hs6.
      apply andb_prop in Hs6 as [E1 Hs6]. apply andb_prop in Hs6 as [E2 Hs6]. apply andb_prop in Hs6 as [E3 Hs6].
      apply andb_prop in Hs6 as [E4 Hs6]. apply andb_prop in Hs6 as [E6 Hs6]. apply andb_prop in Hs6 as [E25 Hs6].
      apply andb_prop in Hs6 as [E7 Hs6]. apply andb_prop in Hs6 as [E8 Hs6]. apply andb_prop in Hs6 as [E9 Hs6]. apply andb_prop in Hs6 as [E10 _].
      apply sv_eqb_sound in E7. apply sv_eqb_sound in E8. apply sv_eqb_sound in E9. apply sv_eqb_sound in E10.
      apply sv_eqb_sound in E1. apply sv_eqb_sound in E2. apply sv_eqb_sound in E3.
      apply sv_eqb_sound in E4. apply sv_eqb_sound in E6. apply sv_eqb_sound in E25.
      split.
      * destruct HG2 as (HJ & H3 & H25). split; [|split; [cbn; exact H3 | cbn [rho_sub rw]; rewrite E25; cbn [eval]; exact H25]].
        destruct HJ; constructor; cbn [rho_sub rw rl rm]; rewrite ?E1, ?E2, ?E3, ?E4, ?E6, ?E7, ?E8, ?E9, ?E10, ?Hs5; cbn [eval]; auto.
        rewrite <- Hn. reflexivity.
      * cbn [rho_sub rl]. subst rho2. cbn [rho_set_rl rl]. rewrite Pos.eqb_refl.
        rewrite (list_bexp_eqb_beval rho1 _ _ Hbl). subst n. apply BLn_eval. exact HG1.
    + split; [|exact Hk]. eapply entails_sound; [exact He | exact Hsm3].
Qed.

Lemma cert_E_Wg : ltac2:(tb__ "0|c|
S1S0S36S36S5S5A2M0S5A2SbcS52S98A1M1A1S34G0S5S34S5S5SdP1A1M2S6S7bSbfA1A1A4S6N230A1M3A4A3S1S0SbS54S98A1S1dG2G3SaS73SdP5A1M4S6ZfffffffffffffddeA1A3S35S9A1S1cP4A1A5A3S1S3cU2S2eSbS10S98A1A2A2S1S0S2cS6aS9S68ScS6N2a8A1M5Z8M6SaS73G2G3A3A3A1S11G1A1M7A3S2bA3S1S0S2cS6aS9S68ScS6N2a0A1G6SaS73G4S6ZeA1A3M8A3A1G7A3S2bA3S1S0S2cS6aS9S68ScS6N298A1G6S6Z0A1M9A3A1G7A3S2bA3S1S0S2cS6aS9S68ScS6N290A1G6G9A3A1G7A3S2bA3S1S0S5S8S98ZbA2SaS73G2G5A3A3S1S0S5S8S98Z16A2G8A3S1S0S33S74A1S88S2aS15S98A1A2S31S74S75A2A3S1S0S5S8S98Z11A2S6Z42A1MaA3S1S0S5S8S98ZaA2S6Z2A1MbA3S1S0S5S8S98ZcA2GbA3S1S0S3fS12S98A1P6aA3S6bSeS13G4GaA2S14S98A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using Hargc LEN N0 STR. vm_compute. repeat split; (reflexivity || lia || (cbn; tauto)). Qed.

Lemma cert_CBg : ltac2:(tb__ "0|d|
S1S0S36S36S5S5A2M0S5A2SbcS52S99A1M1A1S34G0S5S34S5S5SdP1A1M2S6S7bSbfA1A1A4S6N230A1M3A4A3S1S0SbS54S99A1S1dG2G3SaS73SdP5A1M4S6ZfffffffffffffddeA1A3S35S9A1S1cP4A1A5A3S1S3cU2S2eSbS10S99A1A2A2S1S0S2cS6aS9S68ScS6N2a8A1M5Z8M6SaS76SaS73SaS73G2S6N222A1A3G4A3SdP6aA1M7A3A3A1S11G1A1M8A3S2bA3S1S0S2cS6aS9S68ScS6N2a0A1G6G7A3A1G8A3S2bA3S1S0S2cS6aS9S68ScS6N298A1G6S6Z0A1M9A3A1G8A3S2bA3S1S0S2cS6aS9S68ScS6N290A1G6G9A3A1G8A3S2bA3S1S0S5S8S99ZbA2SaS73G2G5A3A3S1S0S5S8S99Z16A2G7A3S1S0S33S74A1S88S2aS15S99A1A2S31S74S75A2A3S1S0S5S8S99Z11A2S6Z42A1MaA3S1S0S5S8S99ZaA2S6Z2A1MbA3S1S0S5S8S99ZcA2GbA3S1S0S3fS12S99A1P6dA3S1S6bSeS13S6Z1A1G7A2S14S99A1McA3S1S6bSeS13G7SaS73G4S6ZdA1A3A2GcA3S6bSeS13G4GaA2GcA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using Hargc LEN N0 STR. vm_compute. repeat split; (reflexivity || lia || (cbn; tauto)). Qed.

Lemma iov_field_lo : ltac2:(tb__ "0|5|
S7SfS2dS40A1M0Sc4S41S3eS5S38Q40M1A1M2S50R8A1ScfS2aR9R8S34G0ScbR7SccR6R5A2A4A4S3cU2S2eSbS10R9A1A2A2S0S36S36S5S5A2M3S5A2SbcS52RaA1A1S34G3S5S34S5S5SdP1A1S6S7bSbfA1A1A4S6N230M4A1A4A3S0S2cS6aS9S68ScS6R7A1Z8R6A3A1S11S52RbA1A1A3S2bA3S1S79S7bS7eZ2Z14A2A1R8A2S7cR8G4A2A2S0S3eS39G1R7A2S78S39G1Vsp;A2R9A2A3S0S33G2A1S49Sc5RcA1R8A2S31G2S16RfR9A2A2A3F_;F_;F_;F_;F_;F_;F_;Fa;Fv;Foff;Fmd;Fms;Ftr;FS;Frho;").
Proof using Hargc Hent Hinp.
  intros rho S tr ms md off v a HG Hsp Hlen Hrng Hc Hoff Ha. pose proof NU.
  destruct (objs_hold01 rho S tr ms md Hsp Hlen) as [H0 _].
  unfold obj_rng in Hrng. injection Hrng as Hb Hlo Hhi.
  apply (cell_read_u64 segs rho ms (ob0 S) (SLit off) v a H0 (In_cellb _ _ Hc)).
  rewrite Hb. change (eval rho (SVar 1)) with (rw rho 1). rewrite (G_v1 rho HG), soff_lit_small by lia. lia.
Qed.

Lemma ibufL_read : ltac2:(tb__ "0|6|
S7SfS2dS40A1M0Sc4S41S3eS30S38Q40M1A1M2G2S56R9A1ScfS2aRaR9S34G0ScbR8SccR7R6A2A4A4S3cU2S2eSbS10RaA1A2A2S0SbS54RbA1S1dSdP1A1S6N230A1SaS73SdP5A1S6ZfffffffffffffddeA1A3S35S9A1S1cP4A1A5A3S3cS2eS38Q8A1M3Vargv0;A2U42A2S79Z0R9A2S79S78RaS7aR9A1A2S78ZeVN0;A2A2S0S3eS39G1R9A2M4S78S7dS39G1Vsp;A2Z230A2RbA2A3S0S3eG4S7aRbA1A3S0S33S2dG3A1M5A1S43Sc5RfA1RbRaA3S31G5Sa8G3RcSa6G3S7fRdA1S51A3A3A2A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Flen;Fa;Fn;Foff;Fmd;Fms;Ftr;FS;Frho;").
Proof using Hargc Hent Hinp.
  intros rho S tr ms md off n a len [HG H4] Hsp Hlen Hob Hsmall Hoff Hn Ha Hl. pose proof NU.
  destruct (objs_hold01 rho S tr ms md Hsp Hlen) as [_ H1]. rewrite Hob in H1.
  rewrite <- H4.
  pose proof (G_v1 rho HG) as V1. pose proof (G_v5 rho HG) as V5.
  assert (Ehi : soff rho (SAlu ALU_ADD (SVar 5) (SLit 18446744073709551070)) = N0 - 546).
  { rewrite soff_snorm. unfold U. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    change (eval rho (SVar 5)) with (rw rho 5). rewrite V5. unfold bv_wrap. rewrite mod64.
    change (18446744073709551070 mod 2 ^ 64) with 18446744073709551070.
    unfold snorm. rewrite pow63, pow64. rewrite !(Z.mod_small (N0 + 18446744073709551070)) by (unfold N0 in *; lia).
    destruct (Z.ltb_spec (N0 + 18446744073709551070) 9223372036854775808); unfold N0 in *; lia. }
  rewrite (list_obj_read_bytes_map segs rho ms _ 4 n (off - 560) a len H1 eq_refl eq_refl).
  - unfold obj_lo_of. cbn [ob_lo]. rewrite soff_lit_small by lia. f_equal. f_equal. f_equal. lia.
  - unfold obj_lo_of. cbn [ob_lo]. rewrite soff_lit_small by lia. lia.
  - unfold obj_hi_of. cbn [ob_hi]. rewrite Ehi. lia.
  - cbn [ob_base]. change (eval rho (SVar 1)) with (rw rho 1). rewrite V1. lia.
  - exact Hl.
Qed.

Lemma bytes_E_Wg : forall rho tr ms md, GoodW rho -> (length argv0 <= 66)%nat -> smatch_pending segs rho E_Wg (tr, mkCfg ms md) ->
  exists b1 l1 b2 l2,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv E_Wg 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv E_Wg 11) + 8)%bv = Some l1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv E_Wg 11) + 16)%bv = Some b2
    /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv E_Wg 11) + 16) + 8)%bv = Some l2
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some MSG
    /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some []
    /\ bv_unsigned (eval rho (reg_sv E_Wg 22)) = Z.of_nat (length (MSG ++ []))
    /\ (bv_unsigned (eval rho (reg_sv E_Wg 11)) + 32 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
    /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros rho tr ms md HGW Hsmall Hsp. pose proof (proj1 HGW) as HG. pose proof NU as NU'.
  destruct cert_E_Wg as (Hrng & Hob1 & Hlen & C1 & C2 & C3 & C4 & R11 & R22 & _).
  rewrite R11, R22. pose proof (G_v1 rho HG) as V1. pose proof (G_v5 rho HG) as V5.
  assert (A0 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-680)))) = bv_unsigned sp - 680).
  { erewrite U_addc; [reflexivity | exact V1 | lia | lia]. }
  assert (A16 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-680))) + 16)%bv = bv_unsigned sp - 664).
  { rewrite (U_bvadd _ _ _ _ A0 u16) by lia. lia. }
  exists (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-560)))), (eval rho (SAlu ALU_ADD (SVar 5) (SLit 14))), (eval rho (SLit 0)), (eval rho (SLit 0)).
  apply and7_tail; [tsz|].
  split; [eapply (iov_field_lo rho E_Wg tr ms md (-680)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field_lo rho E_Wg tr ms md (-672)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split; [eapply (iov_field_lo rho E_Wg tr ms md (-664)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C3 | lia | lia]|].
  split; [eapply (iov_field_lo rho E_Wg tr ms md (-656)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C4 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
  split.
  { rewrite <- (firstn_all MSG), <- (skipn_O MSG). change 0%nat with (Z.to_nat 0).
    apply (ibufL_read rho E_Wg tr ms md 0 (length MSG)); [exact HGW | exact Hsp | exact Hlen | exact Hob1 | exact Hsmall | lia | rewrite MSG_len; unfold N0; lia | |].
    - erewrite U_addc; [| exact V1 | lia | lia]. lia.
    - erewrite U_addc; [| exact V5 | unfold N0; lia | lia]. rewrite MSG_len. unfold N0. lia. }
  split; [reflexivity|].
  erewrite U_addc; [| exact V5 | unfold N0; lia | lia]. rewrite app_nil_r, MSG_len. unfold N0. lia.
Qed.

Lemma bytes_CBg : forall rho tr ms md, GoodW rho -> (length argv0 <= 66)%nat -> smatch_pending segs rho CBg (tr, mkCfg ms md) ->
  let L0 := Z.to_nat (bv_unsigned (rw rho 106)) in
  (1 <= L0 <= 13 + length argv0)%nat /\
  exists b1 l1 b2 l2,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv CBg 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv CBg 11) + 8)%bv = Some l1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv CBg 11) + 16)%bv = Some b2
    /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv CBg 11) + 16) + 8)%bv = Some l2
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some (skipn (length MSG - L0) MSG)
    /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some []
    /\ bv_unsigned (eval rho (reg_sv CBg 22)) = Z.of_nat (length (skipn (length MSG - L0) MSG ++ []))
    /\ (bv_unsigned (eval rho (reg_sv CBg 11)) + 32 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
    /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros rho tr ms md HGW Hsmall Hsp. pose proof (proj1 HGW) as HG. pose proof NU as NU'.
  destruct cert_CBg as (Hrng & Hob1 & Hlen & C1 & C2 & C3 & C4 & R11 & R22 & _ & _ & _ & _ & _ & HinF1 & HinF2 & _).
  pose proof (G_v1 rho HG) as V1. pose proof (G_v5 rho HG) as V5.
  pose proof (SPp_fact _ _ _ _ _ _ Hsp HinF1) as HL1. cbn [holds] in HL1. rewrite U_lit64 in HL1 by lia.
  pose proof (SPp_fact _ _ _ _ _ _ Hsp HinF2) as HL2. cbn [holds] in HL2.
  erewrite (U_addc rho (SVar 5) 13) in HL2; [| exact V5 | unfold N0; lia | lia].
  change (eval rho (SVar 106)) with (rw rho 106) in HL1, HL2.
  intros L0. split; [subst L0; unfold N0 in HL2; lia|]. rewrite R11, R22.
  assert (A0 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-680)))) = bv_unsigned sp - 680).
  { erewrite U_addc; [reflexivity | exact V1 | lia | lia]. }
  assert (A16 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-680))) + 16)%bv = bv_unsigned sp - 664).
  { rewrite (U_bvadd _ _ _ _ A0 u16) by lia. lia. }
  exists (eval rho (SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_ADD (SVar 1) (SLit (-546))) (SVar 5)) (SVar 106))), (eval rho (SVar 106)), (eval rho (SLit 0)), (eval rho (SLit 0)).
  apply and7_tail; [tsz|].
  split; [eapply (iov_field_lo rho CBg tr ms md (-680)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field_lo rho CBg tr ms md (-672)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split; [eapply (iov_field_lo rho CBg tr ms md (-664)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C3 | lia | lia]|].
  split; [eapply (iov_field_lo rho CBg tr ms md (-656)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C4 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
  split.
  { replace (skipn (length MSG - L0) MSG) with (firstn L0 (skipn (Z.to_nat (Z.of_nat (length MSG - L0))) MSG)).
    2:{ rewrite Nat2Z.id. rewrite firstn_all2; [reflexivity|]. rewrite length_skipn. lia. }
    apply (ibufL_read rho CBg tr ms md (Z.of_nat (length MSG - L0)) L0); [exact HGW | exact Hsp | exact Hlen | exact Hob1 | exact Hsmall | lia | rewrite MSG_len; unfold N0; lia | | subst L0; change (eval rho (SVar 106)) with (rw rho 106); lia].
    erewrite (U_sub2 rho _ _ (bv_unsigned sp - 546 + N0) (bv_unsigned (rw rho 106))); [rewrite MSG_len; subst L0; unfold N0 in *; lia | | reflexivity | unfold N0 in *; lia].
    erewrite (U_add2 rho _ _ (bv_unsigned sp - 546) N0); [lia | | exact V5 | unfold N0 in *; lia].
    apply (U_addc rho (SVar 1) (-546) (bv_unsigned sp)); [exact V1 | lia | lia]. }
  split; [reflexivity|].
  change (eval rho (SVar 106)) with (rw rho 106). rewrite app_nil_r, length_skipn, MSG_len. subst L0. unfold N0 in *. lia.
Qed.

Definition L0g (rho : valuation) : nat := Z.to_nat (bv_unsigned (rw rho 106)).
Definition QDg : assn := ltac2:(tb__ "0|0|
S65S9cS2eS38Q8A1S51A2A2").

Lemma loopg : ltac2:(tb__ "0|3|
S3cS2eS38Q8A1M0Vargv0;A2M1U42A2S30S7S56R1A1S1S3cU1S60R2A1M2A2S3cG2Sa4UdG1A2A2A2S3cS60R3A1R4A2S83S2aVok;S4bS2aS4eS4fSa5S2eG0S51A2S60R4A1A2A1Vmd0;A2S99R4A4S64A4F_;F_;F_;Frho;Fm;F_;").
Proof using Hargc Hent Hfd2 Hinp HokK HokP.
  intros Hsmall. induction m as [|m IH]; intros rho HGW HL Hm; [exfalso; lia|]. pose proof NU as NU'. pose proof (proj1 HGW) as HG.
  destruct cert_CBg as (_ & _ & _ & _ & _ & _ & _ & _ & R22 & Hi & H17 & H10 & H12 & Hnx & _).
  assert (HU : bv_unsigned (rw rho 106) = Z.of_nat (L0g rho)) by (unfold L0g; pose proof (urange (rw rho 106)); lia).
  pose proof MSG_len as ML.
  eapply triple_seq.
  { apply (writev_site2 CBg (reg_sv CBg 22) (length MSG - L0g rho) (skipn (length MSG - L0g rho) MSG) [] rho HG);
      [rewrite Hnx; lia | exact Hi | exact H17 | exact H10 | exact H12 | rewrite R22, Hnx; reflexivity | | |].
    + rewrite app_nil_r, firstn_all. reflexivity.
    + rewrite app_nil_r, length_skipn. unfold MAX_RW_COUNT. lia.
    + intros tr ms md Hsp. exact (proj2 (bytes_CBg rho tr ms md HGW Hsmall Hsp)). }
  apply triple_ex; intros rho1. apply triple_ex; intros k.
  apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
  rewrite Hnx in Hk, Hag1. rewrite app_nil_r, length_skipn in Hkb.
  assert (HGW1 : GoodW rho1) by (split; [exact HG1 | rewrite <- (proj1 (proj2 Hag1)); exact (proj2 HGW)]).
  assert (E106 : rw rho1 106 = rw rho 106) by (symmetry; apply (proj1 Hag1); lia).
  assert (U109 : bv_unsigned (rw rho1 109) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
  change (S_after_write CBg (reg_sv CBg 22)) with PBg.
  eapply run_tr; [exact run_PBg | reflexivity | apply okf |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
  -
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. pose proof (hd_fact rho2 L_PBg_0 _ _ w _ eq_refl Hw) as Hf.
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
    change (eval rho2 (SVar 109)) with (rw rho2 109) in Hf. change (eval rho2 (SVar 106)) with (rw rho2 106) in Hf.
    rewrite <- (proj1 Hag2 109%positive ltac:(cbn; lia)), <- (proj1 Hag2 106%positive ltac:(cbn; lia)), U109, E106, HU in Hf.
    exists (rho_sub rho2 s_PBg_Dg). split.
    { apply GoodW_sub; [reflexivity|]. eapply GoodW_agree; [exact Hag2 | cbn; lia | exact HGW1]. }
    eapply SP_entails in Hw; [|exact ent_PBg_Dg].
    replace (length MSG) with (length MSG - L0g rho + k)%nat at 1; [exact Hw|]. lia.
  -
    apply triple_facts. intros HF. apply Forall_cons_iff in HF as [Hf _].
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Z.eqb_eq in Hf.
    change (eval rho2 (SVar 109)) with (rw rho2 109) in Hf. change (eval rho2 (SVar 106)) with (rw rho2 106) in Hf.
    rewrite <- (proj1 Hag2 109%positive ltac:(cbn; lia)), <- (proj1 Hag2 106%positive ltac:(cbn; lia)), U109, E106, HU in Hf.
    assert (EL : L0g (rho_sub rho2 s_PBg_CBg) = (L0g rho - k)%nat).
    { unfold L0g at 1. cbn [rho_sub rw]. rewrite sv_PBg_106.
      erewrite U_sub2; [| reflexivity | reflexivity |]; change (eval rho2 (SVar 106)) with (rw rho2 106); change (eval rho2 (SVar 109)) with (rw rho2 109);
        rewrite <- (proj1 Hag2 106%positive ltac:(cbn; lia)), <- (proj1 Hag2 109%positive ltac:(cbn; lia)), E106, U109, HU; lia. }
    eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH (rho_sub rho2 s_PBg_CBg))].
    + intros w Hw. eapply SP_entails in Hw; [|exact ent_PBg_CBg].
      replace (length MSG - L0g (rho_sub rho2 s_PBg_CBg))%nat with (length MSG - L0g rho + k)%nat by lia. exact Hw.
    + apply GoodW_sub; [reflexivity|]. eapply GoodW_agree; [exact Hag2 | cbn; lia | exact HGW1].
    + lia.
    + lia.
Qed.

Lemma L_Wg : ltac2:(tb__ "0|0|
S3cS2eS38Q8A1Vargv0;A2U42A2S7S56R1A1S83S2aVok;S4bS2aS4eS4fU0A1Vmd0;A2S98R2A4S64A4F_;Frho;F_;").
Proof using Hargc Hent Hfd2 Hinp HokK HokP.
  intros Hsmall rho HGW. pose proof NU as NU'. pose proof (proj1 HGW) as HG. pose proof MSG_len as ML.
  destruct cert_E_Wg as (_ & _ & _ & _ & _ & _ & _ & _ & R22 & Hi & H17 & H10 & H12 & Hnx & _).
  eapply triple_seq.
  { apply (writev_site2 E_Wg (reg_sv E_Wg 22) 0 MSG [] rho HG);
      [rewrite Hnx; lia | exact Hi | exact H17 | exact H10 | exact H12 | rewrite R22, Hnx; reflexivity | | |].
    + rewrite app_nil_r. cbn [skipn]. rewrite firstn_all. reflexivity.
    + rewrite app_nil_r. unfold MAX_RW_COUNT. lia.
    + intros tr ms md Hsp. exact (bytes_E_Wg rho tr ms md HGW Hsmall Hsp). }
  apply triple_ex; intros rho1. apply triple_ex; intros k.
  apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
  rewrite Hnx in Hk, Hag1. rewrite app_nil_r in Hkb.
  assert (HGW1 : GoodW rho1) by (split; [exact HG1 | rewrite <- (proj1 (proj2 Hag1)); exact (proj2 HGW)]).
  assert (U106 : bv_unsigned (rw rho1 106) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
  pose proof (G_v5 rho1 HG1) as V5.
  change (S_after_write E_Wg (reg_sv E_Wg 22)) with PAg. cbn [Nat.add].
  eapply run_tr; [exact run_PAg | reflexivity | apply okf |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
  -
    apply triple_facts. intros HF. apply Forall_cons_iff in HF as [Hf _].
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Bool.negb_true_iff in Hf. apply Z.eqb_neq in Hf.
    erewrite (U_addc rho2 (SVar 5) 14) in Hf; [| reflexivity | |];
      change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 106)) with (rw rho2 106) in *.
    2,3: rewrite <- ?(proj1 Hag2 5%positive ltac:(cbn; lia)), ?V5; unfold N0; lia.
    rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)), <- (proj1 Hag2 106%positive ltac:(cbn; lia)), V5, U106 in Hf.
    assert (EL : L0g (rho_sub rho2 s_PAg_CBg) = (length MSG - k)%nat).
    { unfold L0g. cbn [rho_sub rw]. rewrite sv_PAg_106.
      erewrite (U_sub2 rho2 _ _ (N0 + 14) (Z.of_nat k)); [unfold N0; lia | | | unfold N0 in *; lia].
      - erewrite U_addc; [reflexivity | | unfold N0; lia | lia]. change (eval rho2 (SVar 5)) with (rw rho2 5). rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)). exact V5.
      - change (eval rho2 (SVar 106)) with (rw rho2 106). rewrite <- (proj1 Hag2 106%positive ltac:(cbn; lia)). exact U106. }
    eapply triple_conseq; [| intros w Hw; exact Hw | apply (loopg Hsmall (length MSG - k) (rho_sub rho2 s_PAg_CBg))].
    + intros w Hw. eapply SP_entails in Hw; [|exact ent_PAg_CBg].
      replace (length MSG - L0g (rho_sub rho2 s_PAg_CBg))%nat with k by lia. exact Hw.
    + apply GoodW_sub; [reflexivity|]. eapply GoodW_agree; [exact Hag2 | cbn; lia | exact HGW1].
    + unfold N0 in Hf. lia.
    + lia.
  -
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. pose proof (hd_fact rho2 L_PAg_1 _ _ w _ eq_refl Hw) as Hf.
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Bool.negb_true_iff, Z.eqb_neq in Hf.
    erewrite (U_addc rho2 (SVar 5) 14) in Hf; [| reflexivity | |];
      change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 106)) with (rw rho2 106) in *.
    2,3: rewrite <- ?(proj1 Hag2 5%positive ltac:(cbn; lia)), ?V5; unfold N0; lia.
    rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)), <- (proj1 Hag2 106%positive ltac:(cbn; lia)), V5, U106 in Hf.
    exists (rho_sub rho2 s_PAg_Dg). split.
    { apply GoodW_sub; [reflexivity|]. eapply GoodW_agree; [exact Hag2 | cbn; lia | exact HGW1]. }
    eapply SP_entails in Hw; [|exact ent_PAg_Dg].
    replace (length MSG) with k; [exact Hw|]. unfold N0 in Hf. lia.
Qed.

Lemma cert_exitg : ltac2:(tb__ "0|0|
S1S0S33S74A1S88S2aS15S9dA1A2S31S74S75A2A3S1S0S5S8S9dZ11A2S6Z5eA1A3S0S5S8S9dZaA2S6Z2A1A3A2A2").
Proof using . vm_compute. repeat split; reflexivity. Qed.

Lemma L_exitg : ltac2:(tb__ "0|0|
S7S56R1A1S83S2aVok;S4bS2aS4eS4fS2eS38Q8A1S51A2A1Vmd0;A2S9cR2A4S82S3L_;A4F_;Frho;").
Proof using Hargc Hfs HokK HokP Hokh.
  intros rho HG. eapply run_tr; [exact run_Dg | reflexivity | apply okf |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  destruct cert_exitg as (Hi & H17 & H10).
  apply (triple_exit_eval segs ok SpecT (Kx (TR (length MSG)) md0) E_exitg rho1 2);
    [apply okf | apply okp | exact Hokh | exact Hi | left; exact H17 | rewrite H10; rewrite U_lit64 by lia; reflexivity |].
  intros tr md [-> ->]. rewrite TR_all by lia. rewrite Hfs. exact final_in_spec.
Qed.

Theorem usage_small_safe : ltac2:(tb__ "0|0|
S3cS2eS38Q8A1Vargv0;A2U42A2S0S2cS9bVN0;S89S2aS9aS35S3eA1S97VN0;A1S2bA5A2S2bA3S7VJI;R1A1S83S2aVok;S4bS2aS4eS35S40A1Vmd0;A2Sd2R2A4S82S3L_;A4F_;Frho;F_;F_;").
Proof using Hargc Hent Hfd2 Hfs Hinp HokK HokP Hokh LEN STR.
  intros Hsmall Hchk rho HJ.
  destruct (check_core_sound N0 _ Hchk) as (a & b & wx & o & bl & Hwf & _).
  eapply triple_conseq with (P := fun w => exists rho', Good rho' /\ SP segs (Kx (TR 0) md0) S_use rho' w); [| intros w Hw; exact Hw |].
  { intros w Hw. apply (use_intro rho w HJ). exact Hw. }
  apply triple_ex; intros rho1. apply triple_pure; intros HG1.
  eapply triple_seq.
  { eapply run_tr; [exact run_use | reflexivity | apply okf |].
    intros L rho2 [<-|[]] Hag2. cbn [lf_state].
    pose proof (Good_agree _ _ _ Hag2 ltac:(cbn; lia) HG1) as HG2.
    apply (call_path segs FirstNul ok (Kx (TR 0) md0) (Kx (TR 0) md0) E_sn E_snX Pre_strnlen xs_pre s_sn R_sn Posts_strnlen _ rho2
             xs_pre_ok efr_sn chk_sn fb_sn).
    - intros rho3 HF. apply strnlen_sum; [apply okf | exact HF].
    - intros ms _. apply FirstNul_call. exact HG2.
    - intros L rho3 [<-|[]] Hag3 HF3. cbn [lf_state]. replace (ss_next Pre_strnlen) with NF by reflexivity. rewrite T_imp_eq.
      pose proof (Good_agree _ _ _ Hag3 ltac:(cbn; lia) HG2) as HG3.
      apply (post_path segs ok (Kx (TR 0) md0) T_imp T_sn (ss_facts E_sn) xs_post rho3 _ fb_sn2 xs_post_ok HF3).
      apply triple_facts. intros HFT.
      eapply triple_conseq with (P := SP segs (Kx (TR 0) md0) (Tn N0) rho3); [| intros w Hw; exact Hw | apply (L_small_pre N0 Hchk eq_refl); exact HG3].
      intros w Hsp. apply (Tn_intro N0 rho3 w HG3 eq_refl Hwf).
      eapply (SP_restate segs _ rho3 T_sn T_sn1 w); [exact swf_T_sn1 | exact diff_sn | | constructor | exact Hsp].
      constructor; [|constructor]. cbn [fst snd]. exact (proj1 (Forall_forall _ _) HFT _ fact_T_sn). }
  apply triple_ex; intros rho4. apply triple_pure; intros HG4.
  eapply triple_seq; [apply (L_Wg Hsmall); exact HG4|].
  apply triple_ex; intros rho5. apply triple_pure; intros HG5.
  apply L_exitg. exact HG5.
Qed.

Lemma eL_small_pre : ltac2:(tb__ "0|1|
S3eS0S2cS9bR1S89S2aS9aS35S3eA1S97R1A1S2bA5A2S2bA3S0S3eVN0;R2A3S7S50R1A1S84S2aS4bS2aS4eS4fU0M0A1Vmd0;A2S97R5A1R2A4S65S98G0A2A3F_;Frho;F_;F_;Fn;").
Proof using Hargc Hent Hinp.
  intros n Hchk Hn rho HG. pose proof NU as NU'.
  destruct (check_core_sound n _ Hchk) as (a & b & wx & o & bl & Hwf & Hr & HinX & Hx & Ho & Hlo & Hhi & Hwr & Harr & Hcb & Hbl & Hrl & He & Hs).
  eapply erun_tr; [exact Hr | reflexivity |].
  intros L rho1 [<-|[<-|[]]] Hag1.
  - intros w Hw. exfalso.
    pose proof (SP_fact _ _ _ _ _ Hw HinX) as Hf. unfold BNZ3 in Hf. apply (proj1 (holds_BNZ rho1 (SLit n))) in Hf.
    apply Hf. rewrite <- (proj1 (proj2 Hag1)), (G_rl3 rho HG). rewrite U_lit64 by lia.
    unfold nthb. subst n. unfold N0. rewrite Nat2Z.id, tail_nul. reflexivity.
  - intros w Hw. exists w. split; [apply wsteps_refl|].
    revert w Hw.
    pose proof (Good_agree _ _ _ Hag1 ltac:(unfold Tn; cbn; lia) HG) as HG1.
    intros w [Hsm Hk].
    pose proof (smatch_xforms segs _ _ _ _ w Hx Hsm) as Hsm2.
    pose proof (smatch_obj_to_list segs rho1 wx w 1 4 o (-560) (n - 546) bl Hsm2 Ho Hlo Hhi ltac:(lia) ltac:(lia) Hwr Harr) as Hsm3.
    replace (n - 546 - -560) with (14 + n) in Hsm3 by lia. specialize (Hsm3 Hcb Hrl).
    set (rho2 := rho_set_rl rho1 4 (map (beval rho1) bl)) in Hsm3.
    set (sW := (5%positive, SLit n) :: infer_sub GLg (obj_to_list wx 1 4) E_Wg) in He, Hs.
    exists (rho_sub rho2 sW). split.
    + assert (HG2 : Good rho2).
      { destruct HG1 as (HJ & H3 & H25). subst rho2. split; [|split; [cbn; exact H3 | cbn; exact H25]].
        destruct HJ; constructor; cbn [rho_set_rl rw rl rm]; auto. }
      unfold sub_ok_n in Hs. apply andb_prop in Hs as [Hs6 Hs5]. apply sv_eqb_sound in Hs5.
      cbn [forallb] in Hs6.
      apply andb_prop in Hs6 as [E1 Hs6]. apply andb_prop in Hs6 as [E2 Hs6]. apply andb_prop in Hs6 as [E3 Hs6].
      apply andb_prop in Hs6 as [E4 Hs6]. apply andb_prop in Hs6 as [E6 Hs6]. apply andb_prop in Hs6 as [E25 Hs6].
      apply andb_prop in Hs6 as [E7 Hs6]. apply andb_prop in Hs6 as [E8 Hs6]. apply andb_prop in Hs6 as [E9 Hs6]. apply andb_prop in Hs6 as [E10 _].
      apply sv_eqb_sound in E7. apply sv_eqb_sound in E8. apply sv_eqb_sound in E9. apply sv_eqb_sound in E10.
      apply sv_eqb_sound in E1. apply sv_eqb_sound in E2. apply sv_eqb_sound in E3.
      apply sv_eqb_sound in E4. apply sv_eqb_sound in E6. apply sv_eqb_sound in E25.
      split.
      * destruct HG2 as (HJ & H3 & H25). split; [|split; [cbn; exact H3 | cbn [rho_sub rw]; rewrite E25; cbn [eval]; exact H25]].
        destruct HJ; constructor; cbn [rho_sub rw rl rm]; rewrite ?E1, ?E2, ?E3, ?E4, ?E6, ?E7, ?E8, ?E9, ?E10, ?Hs5; cbn [eval]; auto.
        rewrite <- Hn. reflexivity.
      * cbn [rho_sub rl]. subst rho2. cbn [rho_set_rl rl]. rewrite Pos.eqb_refl.
        rewrite (list_bexp_eqb_beval rho1 _ _ Hbl). subst n. apply BLn_eval. exact HG1.
    + split; [|exact Hk]. eapply entails_sound; [exact He | exact Hsm3].
Qed.

Lemma eL_Wg : ltac2:(tb__ "0|0|
S3cS2eS38Q8A1Vargv0;A2U42A2S7S56R1A1S84S2aS4bS2aS4eS4fU0A1Vmd0;A2S98R2A4S64A3F_;Frho;F_;").
Proof using Hargc Hent Hfd2 Hinp.
  intros Hsmall rho HGW. pose proof NU as NU'. pose proof (proj1 HGW) as HG. pose proof MSG_len as ML.
  destruct cert_E_Wg as (_ & _ & _ & _ & _ & _ & _ & _ & R22 & Hi & H17 & H10 & H12 & Hnx & _).
  eapply etriple_seq.
  { apply (ewritev_site2 E_Wg (reg_sv E_Wg 22) 0 MSG [] rho HG);
      [rewrite Hnx; lia | exact Hi | exact H17 | exact H10 | exact H12 | rewrite R22, Hnx; reflexivity | | |].
    + rewrite app_nil_r. cbn [skipn]. rewrite firstn_all. reflexivity.
    + rewrite app_nil_r. unfold MAX_RW_COUNT. lia.
    + intros tr ms md Hsp. exact (bytes_E_Wg rho tr ms md HGW Hsmall Hsp). }
  apply etriple_ex; intros rho1.
  apply etriple_pure; intros HG1. apply etriple_pure; intros Hag1. apply etriple_pure; intros Hk.
  rewrite Hnx in Hk, Hag1. rewrite app_nil_r in Hk |- *.
  assert (HGW1 : GoodW rho1) by (split; [exact HG1 | rewrite <- (proj1 (proj2 Hag1)); exact (proj2 HGW)]).
  assert (U106 : bv_unsigned (rw rho1 106) = Z.of_nat (length MSG)) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
  pose proof (G_v5 rho1 HG1) as V5.
  change (S_after_write E_Wg (reg_sv E_Wg 22)) with PAg. cbn [Nat.add].
  eapply erun_tr; [exact run_PAg | reflexivity |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
  - apply etriple_facts. intros HF. apply Forall_cons_iff in HF as [Hf _]. exfalso.
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Bool.negb_true_iff in Hf. apply Z.eqb_neq in Hf. apply Hf.
    erewrite (U_addc rho2 (SVar 5) 14); [| reflexivity | |];
      change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 106)) with (rw rho2 106) in *.
    2,3: rewrite <- ?(proj1 Hag2 5%positive ltac:(cbn; lia)), ?V5; unfold N0; lia.
    rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)), <- (proj1 Hag2 106%positive ltac:(cbn; lia)), V5, U106. rewrite ML. unfold N0. lia.
  - intros w Hw. exists w. split; [apply wsteps_refl|]. exists (rho_sub rho2 s_PAg_Dg). split.
    { apply GoodW_sub; [reflexivity|]. eapply GoodW_agree; [exact Hag2 | cbn; lia | exact HGW1]. }
    eapply SP_entails in Hw; [|exact ent_PAg_Dg]. exact Hw.
Qed.

Lemma eL_exitg : ltac2:(tb__ "0|1|
S7S56R1A1S84S2aS4bS2aS4eS4fS2eS38Q8A1S51A2A1Vmd0;A2S9cR2A4S82S0S2dS40A1S85R1A1S37S40Sc6Z2M0S51A2S32S40Sc7Vfs;G0A2S35S40A1A3A3A3Lw;A3F_;Frho;").
Proof using Hargc Hfs.
  intros rho HG. eapply erun_tr; [exact run_Dg | reflexivity |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  destruct cert_exitg as (Hi & H17 & H10).
  eapply etriple_conseq; [intros w Hw; exact Hw | |
    apply (etriple_exit_eval segs (Kx (TR (length MSG)) md0) E_exitg rho1 2 Hi (or_introl H17))].
  - intros w (tr & md & [-> ->] & ->). rewrite TR_all by lia. rewrite Hfs. reflexivity.
  - rewrite H10. rewrite U_lit64 by lia. reflexivity.
Qed.

Theorem usage_small_exists : ltac2:(tb__ "0|2|
S3cS2eS38Q8A1Vargv0;A2U42A2S0S2cS9bVN0;S89S2aS9aS35S3eA1S97VN0;A1S2bA5A2S2bA3S7VJI;R1A1S84S2aS4bS2aS4eS35S40A1M0Vmd0;A2Sd2R2A4S82S0S2dS40A1S85R1A1S37S40Sc6Z2M1Sc8Vargv0;A1A2S32S40Sc7Vfs;G1A2G0A3A3A3Lw;A3F_;Frho;F_;F_;").
Proof using Hargc Hent Hfd2 Hfs Hinp LEN STR.
  intros Hsmall Hchk rho HJ. rewrite <- MSG_usage.
  destruct (check_core_sound N0 _ Hchk) as (a & b & wx & o & bl & Hwf & _).
  eapply etriple_conseq with (P := fun w => exists rho', Good rho' /\ SP segs (Kx (TR 0) md0) S_use rho' w); [| intros w Hw; exact Hw |].
  { intros w Hw. apply (use_intro rho w HJ). exact Hw. }
  apply etriple_ex; intros rho1. apply etriple_pure; intros HG1.
  eapply etriple_seq.
  { eapply erun_tr; [exact run_use | reflexivity |].
    intros L rho2 [<-|[]] Hag2. cbn [lf_state].
    pose proof (Good_agree _ _ _ Hag2 ltac:(cbn; lia) HG1) as HG2.
    apply (ecall_path segs FirstNul (Kx (TR 0) md0) (Kx (TR 0) md0) E_sn E_snX Pre_strnlen xs_pre s_sn R_sn Posts_strnlen _ rho2
             xs_pre_ok efr_sn chk_sn fb_sn).
    - intros rho3 HF. apply strnlen_sum_ex. exact HF.
    - intros ms _. apply FirstNul_call. exact HG2.
    - intros L rho3 [<-|[]] Hag3 HF3. cbn [lf_state]. replace (ss_next Pre_strnlen) with NF by reflexivity. rewrite T_imp_eq.
      pose proof (Good_agree _ _ _ Hag3 ltac:(cbn; lia) HG2) as HG3.
      apply (epost_path segs (Kx (TR 0) md0) T_imp T_sn (ss_facts E_sn) xs_post rho3 _ fb_sn2 xs_post_ok HF3).
      apply etriple_facts. intros HFT.
      eapply etriple_conseq with (P := SP segs (Kx (TR 0) md0) (Tn N0) rho3); [| intros w Hw; exact Hw | apply (eL_small_pre N0 Hchk eq_refl); exact HG3].
      intros w Hsp. apply (Tn_intro N0 rho3 w HG3 eq_refl Hwf).
      eapply (SP_restate segs _ rho3 T_sn T_sn1 w); [exact swf_T_sn1 | exact diff_sn | | constructor | exact Hsp].
      constructor; [|constructor]. cbn [fst snd]. exact (proj1 (Forall_forall _ _) HFT _ fact_T_sn). }
  apply etriple_ex; intros rho4. apply etriple_pure; intros HG4.
  eapply etriple_seq; [apply (eL_Wg Hsmall); exact HG4|].
  apply etriple_ex; intros rho5. apply etriple_pure; intros HG5.
  apply eL_exitg. exact HG5.
Qed.

Definition GoodM (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S1S50Vrho;A1S0S2dS38Q8A1A1S1fVrho;P4A2S53A3A2").
Definition QM_at (S : sstate) (n : nat) : assn := ltac2:(tb__ "0|0|
S82S2S7S7S1S55R1A1S4bS2aS4eS4fVn;A1Vmd0;A2VS;R1R2A5A2Lrho;A2Lw;").
Lemma GoodM_agree : ltac2:(tb__ "0|1|
S3fS7S7S17R3R2R1A3Se2P1aR4A2S55R4A1M0G0F_;F_;F_;Frho';Frho;Fn;").
Proof using Hargc. intros n rho rho' Hag Hn [HG H4]. split; [exact (Good_agree _ _ _ Hag Hn HG)|]. rewrite <- (proj1 (proj2 Hag)). exact H4. Qed.
Lemma GoodM_sub : ltac2:(tb__ "0|0|
Sd8S7S0S2cS67R2A1S2bA3S55R2A1S55Sd7R3R4A2A1F_;F_;Frho;Fs;").
Proof using . intros s rho Hs [HG H4]. split; [exact (Good_sub s rho Hs HG) | cbn [rho_sub rl]; exact H4]. Qed.

Lemma BLm_eval : ltac2:(tb__ "0|1|
S7S50R1A1S0S2dS38Q8A1M0A1Sa7S6eG0S70R2A1S91VN0;A1A4S53A3F_;Frho;").
Proof using Hargc Hent Hinp.
  intros rho HG. unfold BLm, M1. rewrite !map_app, map_map. cbn [beval].
  rewrite (G_rl3 rho HG). unfold N0. rewrite !Nat2Z.id.
  replace (map (fun x : nat => nth (Z.to_nat (Z.of_nat x)) (strs_tail draw inp) (Z_to_bv 8 0)) (seq 0 (length argv0)))
    with (map (fun j : nat => nth j (strs_tail draw inp) (Z_to_bv 8 0)) (seq 0 (length argv0)))
    by (apply map_ext; intros j; rewrite Nat2Z.id; reflexivity).
  rewrite (map_nth_seq (strs_tail draw inp) (length argv0) (Z_to_bv 8 0)) by (pose proof tail_len; pose proof NU; lia).
  rewrite tail_firstn. reflexivity.
Qed.

Lemma check_core_m_sound : ltac2:(tb__ "0|a|
S3eS33S2dS87A1M0A1M1S0S2cS8fR2R1A2S2bA3S2S87S87S2S87S87S2SfSfS2SbSbS2S2dS6eA1M2G2S1S0S2cS24S97R8A1A1S2bA3S1S0G1R7S31G0S32S87R5S32S87R4S35S87A1A3A3A2A3S1S6bSeSa0S6R8A1M3A1S14S8aR5A1A1A3S1S0S33SfA1SdeS8aR4A1S95R8A1A2S31SfR3A2A3S1S0S33SbA1S6cSbS10R3A1U1M4A3S31SbR2A2A3S1S0S5S23R2A1S6N230A1M5A3S1S0S5S22R2A1S6S7dR8Z229A2A1A3S1S0S2cS20S1eR2A1M6A1S2bA3S1S0S2cS21G6A1S2fA3S1S0S33G2A1S71S11R2A1G5Z0S7fS78Z7R8A2A1A4S31G2R1A2A3S1S0S2cSbdS6eS72R1S91R8A1A4S2bA3S1S0S2cSd1P4M7R3A2S2fA3S1S0S2cS69SddR3G4G7A3M8S8bS32S36S3fS5A2S34S3fS5P5G3A4SdbS94G8S8bA3A3M9A3S2bA3S0S2cS9eG9R8A2S2bA3A2A2A2A2A2A2A2A2A2A2A2A2A2Lbl;A2Lo;A2Lwx;A2Lb;A2La;A2F_;Fr;Fn;").
Proof using .
  intros n r H. unfold check_core_m in H. cbv zeta in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct r as [[|a [|b [|? ?]]]|]; try discriminate.
  cbn [lf0 nth lf_state] in H3, H4.
  destruct (apply_xforms (lf_state b) (xs_ibuf2 n)) as [wx|] eqn:Ex; [|discriminate].
  apply andb_prop in H4 as [H4 H7]. apply andb_prop in H4 as [H4 H6].
  destruct (nth_error (ss_objs wx) 1) as [o|] eqn:Eo; [|discriminate].
  apply andb_prop in H4 as [H4 Hcb]. apply andb_prop in H4 as [H4 Harr]. apply andb_prop in H4 as [H4 Hwr]. apply andb_prop in H4 as [Hlo Hhi].
  destruct (cells_bytes (ob_cells o) (SLit (-560)) 0 (Z.to_nat (7 + n))) as [bl|] eqn:Ecb; [|discriminate].
  apply andb_prop in H7 as [He Hs].
  apply existsb_exists in H3 as (p & Hp & Ep). apply sprop_eqb_sound in Ep. subst p.
  exists a, b, wx, o, bl. repeat split; auto.
  - apply sv_eqb_sound in Hlo. exact Hlo.
  - apply sv_eqb_sound in Hhi. exact Hhi.
  - destruct (is_arr (ob_dflt o)); [discriminate|reflexivity].
  - destruct (state_has_rl 4 wx); [discriminate|reflexivity].
Qed.

Lemma mid_leaf_out : ltac2:(tb__ "0|8|
S3eS7S87SfSbS2dS6eA1M0S82S50R6A1S0S3eVN0;R8A3S0S33SfA1SdeS8aR7A1S95R9A1A2S31SfR6A2A3S0S33SbA1S6cSbS10R7A1U1M1A3S31SbR6A2A3S0S5S23R7A1S6N230A1M2A3S0S5S22R8A1S6S7dRcZ229A2A1A3S0S2cS20S1eR9A1A1S2bA3S0S2cS21S1eRaA1A1S2fA3S0S33G0A1S71S11RbA1G2Z0S7fS78Z7RfA2A1A4S31G0RaA2A3S0S2cSbdS6eS72RbS91R10A1A4S2bA3S0S2cSd1P4M3ReA2S2fA3S0S2cS69SddRfG1G3A3M4S8bS32S36S3fS5A2M5S34S3fS5P5M6S6R12A1A4SdbS94G4S8bA3A3A3S2bA3S0S2cS9eS32G5S34S3fS5G6S6R13A1A4SdbS94SddR10G1G3A3S8bA3A3R13A2S2bA3S4bS2aS4eS4fU0M7A1Vmd0;A2S8aR12A1R13ReA5S5bS8bG7RfA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Fbl;Fo;Fwx;Fb;Frho1;Fn;").
Proof using Hargc Hent Hinp.
  intros n rho1 b wx o bl w HG1 Hn Hx Ho Hlo Hhi Hwr Harr Hcb Hbl Hrl He Hs [Hsm Hk]. pose proof NU as NU'.
  pose proof (smatch_xforms segs _ _ _ _ w Hx Hsm) as Hsm2.
  pose proof (smatch_obj_to_list segs rho1 wx w 1 4 o (-560) (n - 553) bl Hsm2 Ho Hlo Hhi ltac:(lia) ltac:(unfold N0 in Hn; lia) Hwr Harr) as Hsm3.
  replace (n - 553 - -560) with (7 + n) in Hsm3 by lia. specialize (Hsm3 Hcb Hrl).
  set (rho2 := rho_set_rl rho1 4 (map (beval rho1) bl)) in Hsm3.
  set (sW := (5%positive, SLit n) :: infer_sub GLm (obj_to_list wx 1 4) E_Mg) in He, Hs.
  exists (rho_sub rho2 sW). split.
  + assert (HG2 : Good rho2).
    { destruct HG1 as (HJ & H3 & H25). subst rho2. split; [|split; [cbn; exact H3 | cbn; exact H25]].
      destruct HJ; constructor; cbn [rho_set_rl rw rl rm]; auto. }
    unfold sub_ok_n in Hs. apply andb_prop in Hs as [Hs6 Hs5]. apply sv_eqb_sound in Hs5.
    cbn [forallb] in Hs6.
    apply andb_prop in Hs6 as [E1 Hs6]. apply andb_prop in Hs6 as [E2 Hs6]. apply andb_prop in Hs6 as [E3 Hs6].
    apply andb_prop in Hs6 as [E4 Hs6]. apply andb_prop in Hs6 as [E6 Hs6]. apply andb_prop in Hs6 as [E25 Hs6].
      apply andb_prop in Hs6 as [E7 Hs6]. apply andb_prop in Hs6 as [E8 Hs6]. apply andb_prop in Hs6 as [E9 Hs6]. apply andb_prop in Hs6 as [E10 _].
      apply sv_eqb_sound in E7. apply sv_eqb_sound in E8. apply sv_eqb_sound in E9. apply sv_eqb_sound in E10.
    apply sv_eqb_sound in E1. apply sv_eqb_sound in E2. apply sv_eqb_sound in E3.
    apply sv_eqb_sound in E4. apply sv_eqb_sound in E6. apply sv_eqb_sound in E25.
    split.
    * destruct HG2 as (HJ & H3 & H25). split; [|split; [cbn; exact H3 | cbn [rho_sub rw]; rewrite E25; cbn [eval]; exact H25]].
      destruct HJ; constructor; cbn [rho_sub rw rl rm]; rewrite ?E1, ?E2, ?E3, ?E4, ?E6, ?E7, ?E8, ?E9, ?E10, ?Hs5; cbn [eval]; auto.
      rewrite <- Hn. reflexivity.
    * cbn [rho_sub rl]. subst rho2. cbn [rho_set_rl rl]. rewrite Pos.eqb_refl.
      rewrite (list_bexp_eqb_beval rho1 _ _ Hbl). subst n. apply BLm_eval. exact HG1.
  + split; [|exact Hk]. eapply entails_sound; [exact He | exact Hsm3].
Qed.

Lemma L_mid_pre : ltac2:(tb__ "0|1|
S3eS0S2cS8fR1S89S2aS9aS35S3eA1S97R1A1S2bA5A2S2bA3S0S3eVN0;R2A3S7S50R1A1S83S2aVok;S4bS2aS4eS4fU0M0A1Vmd0;A2S97R5A1R2A4S5bS8bG0A2A4F_;Frho;F_;F_;Fn;").
Proof using Hargc Hent Hinp HokK.
  intros n Hchk Hn rho HG. pose proof NU as NU'.
  destruct (check_core_m_sound n _ Hchk) as (a & b & wx & o & bl & Hwf & Hr & HinX & Hx & Ho & Hlo & Hhi & Hwr & Harr & Hcb & Hbl & Hrl & He & Hs).
  eapply run_tr; [exact Hr | reflexivity | apply okf |].
  intros L rho1 [<-|[<-|[]]] Hag1.
  - intros m Hg w Hw. exfalso.
    pose proof (SP_fact _ _ _ _ _ Hw HinX) as Hf. unfold BNZ3 in Hf. apply (proj1 (holds_BNZ rho1 (SLit n))) in Hf.
    apply Hf. rewrite <- (proj1 (proj2 Hag1)), (G_rl3 rho HG). rewrite U_lit64 by lia.
    unfold nthb. subst n. unfold N0. rewrite Nat2Z.id, tail_nul. reflexivity.
  - pose proof (Good_agree _ _ _ Hag1 ltac:(unfold Tn; cbn; lia) HG) as HG1.
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. exact (mid_leaf_out n rho1 b wx o bl w HG1 Hn Hx Ho Hlo Hhi Hwr Harr Hcb Hbl Hrl He Hs Hw).
Qed.

Lemma eL_mid_pre : ltac2:(tb__ "0|1|
S3eS0S2cS8fR1S89S2aS9aS35S3eA1S97R1A1S2bA5A2S2bA3S0S3eVN0;R2A3S7S50R1A1S84S2aS4bS2aS4eS4fU0M0A1Vmd0;A2S97R5A1R2A4S5bS8bG0A2A3F_;Frho;F_;F_;Fn;").
Proof using Hargc Hent Hinp.
  intros n Hchk Hn rho HG. pose proof NU as NU'.
  destruct (check_core_m_sound n _ Hchk) as (a & b & wx & o & bl & Hwf & Hr & HinX & Hx & Ho & Hlo & Hhi & Hwr & Harr & Hcb & Hbl & Hrl & He & Hs).
  eapply erun_tr; [exact Hr | reflexivity |].
  intros L rho1 [<-|[<-|[]]] Hag1.
  - intros w Hw. exfalso.
    pose proof (SP_fact _ _ _ _ _ Hw HinX) as Hf. unfold BNZ3 in Hf. apply (proj1 (holds_BNZ rho1 (SLit n))) in Hf.
    apply Hf. rewrite <- (proj1 (proj2 Hag1)), (G_rl3 rho HG). rewrite U_lit64 by lia.
    unfold nthb. subst n. unfold N0. rewrite Nat2Z.id, tail_nul. reflexivity.
  - pose proof (Good_agree _ _ _ Hag1 ltac:(unfold Tn; cbn; lia) HG) as HG1.
    intros w Hw. exists w. split; [apply wsteps_refl|].
    exact (mid_leaf_out n rho1 b wx o bl w HG1 Hn Hx Ho Hlo Hhi Hwr Harr Hcb Hbl Hrl He Hs Hw).
Qed.

Definition OB_ibuf2 : sobj := ltac2:(tb__ "0|0|
S1dSdP1A1S6N230A1SaS73SdP5A1S6Zfffffffffffffdd7A1A3S35S9A1S1cP4A1A5").

Lemma cert_E_Mg : ltac2:(tb__ "0|b|
S1S0S36S36S5S5A2M0S5A2SbcS52S8bA1M1A1S34G0S5S34S5S5SdP1A1M2S6S7bSbfA1A1A4S6N230A1M3A4A3S1S0SbS54S8bA1S62A3S1S3cU2S2eSbS10S8bA1A2A2S1S0S2cS6aS9S68ScS6N4c8A1M4Z8M5SaS73G2G3A3A3A1S11G1A1M6A3S2bA3S1S0S2cS6aS9S68ScS6N4c0A1G5SaS73SdP5A1M7S6Z7A1M8A3A3A1G6A3S2bA3S1S0S2cS6aS9S68ScS6N4b8A1G5S6S90A1A3A1G6A3S2bA3S1S0S2cS6aS9S68ScS6N4b0A1G5G8A3A1G6A3S2bA3S1S0S5S8S8bZbA2SaS73G2G4A3A3S1S0S5S8S8bZ16A2SaS73G7S6ZeA1A3A3S1S0S33S74A1S88S2aS15S8bA1A2S31S74S75A2A3S1S0S5S8S8bZ11A2S6Z42A1A3S1S0S5S8S8bZaA2S6Z2A1M9A3S1S0S5S8S8bZcA2G9A3S1S0S3fS12S8bA1P6aA3S1S6bSeS13S6Z43A1G7A2S14S8bA1MaA3S6bSeS13G7S6Z49A1A2GaA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using Hargc LEN N0 STR. vm_compute. repeat split; (reflexivity || lia || (cbn; tauto)). Qed.

Lemma cert_CB2m : ltac2:(tb__ "0|b|
S1S0S36S36S5S5A2M0S5A2SbcS52S8cA1M1A1S34G0S5S34S5S5SdP1A1M2S6S7bSbfA1A1A4S6N230A1A4A3S1S0SbS54S8cA1S62A3S1S3cU2S2eSbS10S8cA1A2A2S1S0S2cS6aS9S68ScS6N4c8A1M3Z8M4SaS76SaS73SaS73G2S6N229A1A3SdP5A1M5A3SdP6aA1M6A3A3A1S11G1A1M7A3S2bA3S1S0S2cS6aS9S68ScS6N4c0A1G4G6A3A1G7A3S2bA3S1S0S2cS6aS9S68ScS6N4b8A1G4S6S90A1A3A1G7A3S2bA3S1S0S2cS6aS9S68ScS6N4b0A1G4S6Z7A1M8A3A1G7A3S2bA3S1S0S5S8S8cZbA2SaS73G2G3A3A3S1S0S5S8S8cZ16A2SaS73G6G8A3A3S1S0S33S74A1S88S2aS15S8cA1A2S31S74S75A2A3S1S0S5S8S8cZ11A2S6Z42A1A3S1S0S5S8S8cZaA2S6Z2A1M9A3S1S0S5S8S8cZcA2G9A3S1S0S3fS12S8cA1P6dA3S1S6bSeS13G6SaS73G5S6Z6A1A3A2S14S8cA1MaA3S1S6bSeS13S6Z43A1G5A2GaA3S6bSeS13G5S6Z49A1A2GaA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using Hargc LEN N0 STR. vm_compute. repeat split; (reflexivity || lia || (cbn; tauto)). Qed.

Lemma cert_CB1m : ltac2:(tb__ "0|9|
S1S0S36S36S5S5A2M0S5A2SbcS52S8dA1M1A1S34G0S5S34S5S5SdP1A1M2S6S7bSbfA1A1A4S6N230A1A4A3S1S3cU2S2eSbS10S8dA1A2A2S1S0S2cS6aS9S68ScS6N4b8A1M3Z8M4SaS76S6S78S90Z7A2A1SdP6aA1M5A3A3A1S11G1A1M6A3S2bA3S1S0S2cS6aS9S68ScS6N4b0A1G4G5A3A1G6A3S2bA3S1S0S5S8S8dZbA2SaS73G2G3A3A3S1S0S5S8S8dZ16A2G5A3S1S0S33S74A1S88S2aS15S8dA1A2S31S74S75A2A3S1S0S5S8S8dZ11A2S6Z42A1A3S1S0S5S8S8dZaA2S6Z2A1A3S1S0S5S8S8dZcA2S6Z1A1M7A3S1S0S3fS12S8dA1P6eA3S1S6bSeS13G7G5A2S14S8dA1M8A3S6bSeS13G5S6Z6A1A2G8A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using Hargc LEN N0 STR. vm_compute. repeat split; (reflexivity || lia || (cbn; tauto)). Qed.

Lemma RO_INPUT_range : ltac2:(tb__ "0|0|
S1S7cZ0S90A2S7cS78S90Z7A2S7eZ2Z20A2A2A2").
Proof using Hargc LEN N0 STR. unfold RO_INPUT. lia. Qed.

Lemma ro_input : ltac2:(tb__ "0|2|
S7SfS2dS40A1M0Sc4S41ScfS2aR5R4S34G0ScbR3SccR2R1A2A4A4S0S33S2dS38Q8A1A1M1A1S1bR3S3aQ40S90A2U7A3S31G1S57A2A3F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using Hargc JI LEN N0 STR.
  intros rho S tr ms md Hsp. unfold RO_INPUT, M2.
  apply (ro_read segs ms); [ exact (smatch_pending_rom segs _ _ _ _ _ Hsp) | exact (smatch_pending_ro_clear segs _ _ _ _ _ Hsp)
    | lia | lia | lia | vm_compute; reflexivity | vm_compute; reflexivity ].
Qed.

Lemma ibuf2_read : ltac2:(tb__ "0|7|
S7SfS2dS40A1M0Sc4S41S3eS30S38Q40M1A1M2G2S55R9A1ScfS2aRaR9S34G0ScbR8SccR7R6A2A4A4S3cU2S2eSbS10RaA1A2A2S0SbS54RbA1S62A3S1S3cU43S2eS38Q8A1M3Vargv0;A2M4A2S3cG4U49A2A2S79Z0R9A2S79S78RaS7aR9A1A2S78Z7VN0;A2A2S0S3eS39G1R9A2M5S78S7dS39G1Vsp;A2Z230A2RbA2A3S0S3eG5S7aRbA1A3S0S33S2dG3A1M6A1S43Sc5RfA1RbRaA3S31G6Sa8G3RcSa6G3S7fRdA1S53A3A3A2A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Flen;Fa;Fn;Foff;Fmd;Fms;Ftr;FS;Frho;").
Proof using Hargc Hent Hinp.
  intros rho S tr ms md off n a len [HG H4] Hsp Hlen Hob Hmid Hoff Hn Ha Hl. pose proof NU.
  destruct (objs_hold01 rho S tr ms md Hsp Hlen) as [_ H1]. rewrite Hob in H1.
  rewrite <- H4.
  pose proof (G_v1 rho HG) as V1. pose proof (G_v5 rho HG) as V5.
  assert (Ehi : soff rho (SAlu ALU_ADD (SVar 5) (SLit 18446744073709551063)) = N0 - 553).
  { rewrite soff_snorm. unfold U. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    change (eval rho (SVar 5)) with (rw rho 5). rewrite V5. unfold bv_wrap. rewrite mod64.
    change (18446744073709551063 mod 2 ^ 64) with 18446744073709551063.
    unfold snorm. rewrite pow63, pow64. rewrite !(Z.mod_small (N0 + 18446744073709551063)) by (unfold N0 in *; lia).
    destruct (Z.ltb_spec (N0 + 18446744073709551063) 9223372036854775808); unfold N0 in *; lia. }
  rewrite (list_obj_read_bytes_map segs rho ms _ 4 n (off - 560) a len H1 eq_refl eq_refl).
  - unfold obj_lo_of. cbn [ob_lo OB_ibuf2]. rewrite soff_lit_small by lia. f_equal. f_equal. f_equal. lia.
  - unfold obj_lo_of. cbn [ob_lo OB_ibuf2]. rewrite soff_lit_small by lia. lia.
  - unfold obj_hi_of. cbn [ob_hi OB_ibuf2]. rewrite Ehi. lia.
  - cbn [ob_base OB_ibuf2]. change (eval rho (SVar 1)) with (rw rho 1). rewrite V1. lia.
  - exact Hl.
Qed.

Lemma MSG_skipM1 : ltac2:(tb__ "0|1|
S30S3cR1S2eS38Q8A1M0S53A2A2S0S2dG0A1Sa6G0R2S51A3S37G0Sa6G0R2S53A3S57A3A3F_;Fd;").
Proof using Hargc. intros d Hd. unfold MSG. rewrite skipn_app. replace (d - length M1)%nat with 0%nat by lia. reflexivity. Qed.

Lemma bytes_E_Mg : forall rho tr ms md, GoodM rho -> (67 <= length argv0 <= 73)%nat -> smatch_pending segs rho E_Mg (tr, mkCfg ms md) ->
  exists b1 l1 b2 l2,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv E_Mg 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv E_Mg 11) + 8)%bv = Some l1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv E_Mg 11) + 16)%bv = Some b2
    /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv E_Mg 11) + 16) + 8)%bv = Some l2
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some M1
    /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some M2
    /\ bv_unsigned (eval rho (reg_sv E_Mg 22)) = Z.of_nat (length (M1 ++ M2))
    /\ (bv_unsigned (eval rho (reg_sv E_Mg 11)) + 32 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
    /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros rho tr ms md HGM Hmid Hsp. pose proof (proj1 HGM) as HG. pose proof NU as NU'. pose proof RO_INPUT_range.
  destruct cert_E_Mg as (Hrng & Hob1 & Hlen & C1 & C2 & C3 & C4 & R11 & R22 & _).
  rewrite R11, R22. pose proof (G_v1 rho HG) as V1. pose proof (G_v5 rho HG) as V5.
  assert (A0 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-1224)))) = bv_unsigned sp - 1224).
  { erewrite U_addc; [reflexivity | exact V1 | lia | lia]. }
  assert (A16 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-1224))) + 16)%bv = bv_unsigned sp - 1208).
  { rewrite (U_bvadd _ _ _ _ A0 u16) by lia. lia. }
  exists (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-560)))), (eval rho (SAlu ALU_ADD (SVar 5) (SLit 7))), (eval rho (SLit RO_INPUT)), (eval rho (SLit 7)).
  apply and7_tail; [tsz|].
  split; [eapply (iov_field_lo rho E_Mg tr ms md (-1224)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field_lo rho E_Mg tr ms md (-1216)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split; [eapply (iov_field_lo rho E_Mg tr ms md (-1208)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C3 | lia | lia]|].
  split; [eapply (iov_field_lo rho E_Mg tr ms md (-1200)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C4 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
  split.
  { rewrite <- (firstn_all M1), <- (skipn_O M1). change 0%nat with (Z.to_nat 0).
    apply (ibuf2_read rho E_Mg tr ms md 0 (length M1)); [exact HGM | exact Hsp | exact Hlen | exact Hob1 | exact Hmid | lia | rewrite M1_len; unfold N0; lia | |].
    - erewrite U_addc; [| exact V1 | lia | lia]. lia.
    - erewrite U_addc; [| exact V5 | unfold N0; lia | lia]. rewrite M1_len. unfold N0. lia. }
  split.
  { apply (read_bytes_map_of_rd ms _ _ 7); [change (Z.of_nat 7) with 7; apply U_lit64; lia|].
    cbn [eval]. eapply ro_input. exact Hsp. }
  erewrite U_addc; [| exact V5 | unfold N0; lia | lia]. rewrite length_app, M1_len, M2_len. unfold N0. lia.
Qed.

Lemma bytes_CB2m : forall rho tr ms md, GoodM rho -> (67 <= length argv0 <= 73)%nat -> smatch_pending segs rho CB2m (tr, mkCfg ms md) ->
  let L0 := Z.to_nat (bv_unsigned (rw rho 106)) in
  (L0 <= 6 + length argv0)%nat /\
  exists b1 l1 b2 l2,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv CB2m 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv CB2m 11) + 8)%bv = Some l1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv CB2m 11) + 16)%bv = Some b2
    /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv CB2m 11) + 16) + 8)%bv = Some l2
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some (skipn (length M1 - L0) M1)
    /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some M2
    /\ bv_unsigned (eval rho (reg_sv CB2m 22)) = Z.of_nat (length (skipn (length M1 - L0) M1 ++ M2))
    /\ (bv_unsigned (eval rho (reg_sv CB2m 11)) + 32 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
    /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros rho tr ms md HGM Hmid Hsp. pose proof (proj1 HGM) as HG. pose proof NU as NU'. pose proof RO_INPUT_range.
  destruct cert_CB2m as (Hrng & Hob1 & Hlen & C1 & C2 & C3 & C4 & R11 & R22 & _ & _ & _ & _ & _ & HinF & _).
  pose proof (G_v1 rho HG) as V1. pose proof (G_v5 rho HG) as V5.
  pose proof (SPp_fact _ _ _ _ _ _ Hsp HinF) as HL. cbn [holds] in HL.
  erewrite (U_addc rho (SVar 5) 6) in HL; [| exact V5 | unfold N0; lia | lia].
  change (eval rho (SVar 106)) with (rw rho 106) in HL. pose proof (urange (rw rho 106)) as R106.
  intros L0. split; [subst L0; unfold N0 in HL; lia|]. rewrite R11, R22. pose proof M1_len as ML.
  assert (A0 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-1224)))) = bv_unsigned sp - 1224).
  { erewrite U_addc; [reflexivity | exact V1 | lia | lia]. }
  assert (A16 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-1224))) + 16)%bv = bv_unsigned sp - 1208).
  { rewrite (U_bvadd _ _ _ _ A0 u16) by lia. lia. }
  exists (eval rho (SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_ADD (SVar 1) (SLit (-553))) (SVar 5)) (SVar 106))), (eval rho (SVar 106)), (eval rho (SLit RO_INPUT)), (eval rho (SLit 7)).
  apply and7_tail; [tsz|].
  split; [eapply (iov_field_lo rho CB2m tr ms md (-1224)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field_lo rho CB2m tr ms md (-1216)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split; [eapply (iov_field_lo rho CB2m tr ms md (-1208)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C3 | lia | lia]|].
  split; [eapply (iov_field_lo rho CB2m tr ms md (-1200)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C4 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
  split.
  { replace (skipn (length M1 - L0) M1) with (firstn L0 (skipn (Z.to_nat (Z.of_nat (length M1 - L0))) M1)).
    2:{ rewrite Nat2Z.id. rewrite firstn_all2; [reflexivity|]. rewrite length_skipn. lia. }
    apply (ibuf2_read rho CB2m tr ms md (Z.of_nat (length M1 - L0)) L0); [exact HGM | exact Hsp | exact Hlen | exact Hob1 | exact Hmid | lia | rewrite ML; unfold N0; lia | | subst L0; change (eval rho (SVar 106)) with (rw rho 106); lia].
    erewrite (U_sub2 rho _ _ (bv_unsigned sp - 553 + N0) (bv_unsigned (rw rho 106))); [rewrite ML; subst L0; unfold N0 in *; lia | | reflexivity | unfold N0 in *; lia].
    erewrite (U_add2 rho _ _ (bv_unsigned sp - 553) N0); [lia | | exact V5 | unfold N0 in *; lia].
    apply (U_addc rho (SVar 1) (-553) (bv_unsigned sp)); [exact V1 | lia | lia]. }
  split.
  { apply (read_bytes_map_of_rd ms _ _ 7); [change (Z.of_nat 7) with 7; apply U_lit64; lia|].
    cbn [eval]. eapply ro_input. exact Hsp. }
  erewrite U_addc; [| reflexivity | change (eval rho (SVar 106)) with (rw rho 106); lia | lia].
  change (eval rho (SVar 106)) with (rw rho 106). rewrite length_app, length_skipn, M2_len. subst L0. lia.
Qed.

Lemma bytes_CB1m : forall rho tr ms md, GoodM rho -> smatch_pending segs rho CB1m (tr, mkCfg ms md) ->
  let R := Z.to_nat (bv_unsigned (rw rho 106)) in
  (1 <= R <= 6)%nat /\
  exists b1 l1,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv CB1m 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv CB1m 11) + 8)%bv = Some l1
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some (skipn (7 - R) M2)
    /\ bv_unsigned (eval rho (reg_sv CB1m 22)) = Z.of_nat (length (skipn (7 - R) M2))
    /\ (bv_unsigned (eval rho (reg_sv CB1m 11)) + 16 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros rho tr ms md HGM Hsp. pose proof (proj1 HGM) as HG. pose proof NU as NU'. pose proof RO_INPUT_range.
  destruct cert_CB1m as (Hrng & Hlen & C1 & C2 & R11 & R22 & _ & _ & _ & _ & _ & HinF1 & HinF2).
  pose proof (G_v1 rho HG) as V1.
  pose proof (SPp_fact _ _ _ _ _ _ Hsp HinF1) as HL1. cbn [holds] in HL1. rewrite U_lit64 in HL1 by lia.
  pose proof (SPp_fact _ _ _ _ _ _ Hsp HinF2) as HL2. cbn [holds] in HL2. rewrite U_lit64 in HL2 by lia.
  change (eval rho (SVar 106)) with (rw rho 106) in HL1, HL2.
  intros R. split; [subst R; lia|]. rewrite R11, R22.
  assert (A0 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-1208)))) = bv_unsigned sp - 1208).
  { erewrite U_addc; [reflexivity | exact V1 | lia | lia]. }
  exists (eval rho (SAlu ALU_SUB (SLit (RO_INPUT + 7)) (SVar 106))), (eval rho (SVar 106)).
  apply and4_tail; [tsz|].
  split; [eapply (iov_field_lo rho CB1m tr ms md (-1208)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field_lo rho CB1m tr ms md (-1200)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split.
  { apply (read_bytes_map_of_rd ms _ _ R); [subst R; change (eval rho (SVar 106)) with (rw rho 106); lia|].
    replace (eval rho (SAlu ALU_SUB (SLit (RO_INPUT + 7)) (SVar 106))) with (Z_to_bv 64 RO_INPUT + Z_to_bv 64 (Z.of_nat (7 - R)))%bv.
    - apply rd_bytes_skip. replace (7 - R + R)%nat with 7%nat by lia. eapply ro_input. exact Hsp.
    - apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite mod64, <- Z.add_mod, !Z.mod_small by lia.
      symmetry. erewrite (U_sub2 rho _ _ (RO_INPUT + 7) (bv_unsigned (rw rho 106))); [lia | apply U_lit64; lia | reflexivity | lia]. }
  change (eval rho (SVar 106)) with (rw rho 106). rewrite length_skipn, M2_len. subst R. lia.
Qed.

Definition L0m (rho : valuation) : nat := Z.to_nat (bv_unsigned (rw rho 106)).
Definition QDm : assn := ltac2:(tb__ "0|0|
S5bS92S2eS38Q8A1S51A2A2").

Lemma loopm : ltac2:(tb__ "0|7|
S1S3cU43S2eS38Q8A1M0Vargv0;A2M1A2S3cG1U49A2A2S30S1S7S55R1A1M2S3cS61R2A1M3Sa4U6M4G1A2A2S3cSa4S61R3A1M5U7A2R4A2S83S2aVok;S4bS2aS4eS4fSa5S2eG0S53A2S61R4A1M6A2A1Vmd0;A2S8cR4A4S5aA4F_;F_;F_;Frho;S7G2S1S3cU1G3A2S3cG3G4A2A2S3cG5R4A2S83S2aVok;S4bS2aS4eS4fSa5S2eG0S51A2G6A2A1Vmd0;A2S8dR4A4S5aA4F_;F_;F_;Frho;A2Fm;F_;").
Proof using Hargc Hent Hfd2 Hinp HokK HokP.
  intros Hmid. induction m as [|m IH].
  { split; intros rho HG H1 H2; exfalso; lia. }
  destruct IH as [IH2 IH1]. pose proof NU as NU'. pose proof M1_len as ML. pose proof MSG_len as MSL.
  destruct cert_CB2m as (_ & _ & _ & _ & _ & _ & _ & _ & R22b & Hib & H17b & H10b & H12b & Hnxb & _).
  destruct cert_CB1m as (_ & _ & _ & _ & _ & R22c & Hic & H17c & H10c & H12c & Hnxc & _).
  split.
  -
    intros rho HGM HL0 Hm. pose proof (proj1 HGM) as HG.
    assert (HU : bv_unsigned (rw rho 106) = Z.of_nat (L0m rho)) by (unfold L0m; pose proof (urange (rw rho 106)); lia).
    eapply triple_seq.
    { apply (writev_site2 CB2m (reg_sv CB2m 22) (length M1 - L0m rho) (skipn (length M1 - L0m rho) M1) M2 rho HG);
        [rewrite Hnxb; lia | exact Hib | exact H17b | exact H10b | exact H12b | rewrite R22b, Hnxb; reflexivity | | |].
      + rewrite MSG_skipM1 by lia. rewrite firstn_all. reflexivity.
      + rewrite length_app, length_skipn, M2_len. unfold MAX_RW_COUNT. lia.
      + intros tr ms md Hsp. exact (proj2 (bytes_CB2m rho tr ms md HGM Hmid Hsp)). }
    apply triple_ex; intros rho1. apply triple_ex; intros k.
    apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
    rewrite Hnxb in Hk, Hag1. rewrite length_app, length_skipn, M2_len in Hkb.
    assert (HGM1 : GoodM rho1) by (split; [exact HG1 | rewrite <- (proj1 (proj2 Hag1)); exact (proj2 HGM)]).
    assert (E106 : rw rho1 106 = rw rho 106) by (symmetry; apply (proj1 Hag1); lia).
    assert (U109 : bv_unsigned (rw rho1 109) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
    eapply triple_conseq with (P := SP segs (Kx (TR (length M1 - L0m rho + k)) md0) PB2m rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. apply SP_add1; [exact Hw | | reflexivity]. cbn [holds]. change (eval rho1 (SVar 109)) with (rw rho1 109). rewrite U109, U_lit64 by lia. lia. }
    destruct (Nat.le_gt_cases k (L0m rho)) as [Hle|Hgt].
    + eapply triple_conseq with (P := SP segs (Kx (TR (length M1 - L0m rho + k)) md0) PB2ma rho1); [| intros w Hw; exact Hw |].
      { intros w Hw. apply SP_add1; [exact Hw | | reflexivity]. cbn [holds]. change (eval rho1 (SVar 109)) with (rw rho1 109).
        change (eval rho1 (SVar 106)) with (rw rho1 106). rewrite U109, E106, HU. lia. }
      eapply run_tr; [exact run_PB2ma | reflexivity | apply okf |].
      intros L rho2 [<-|[]] Hag2. cbn [lf_state].
      assert (EL : L0m (rho_sub rho2 s_PB2ma_CB2m) = (L0m rho - k)%nat).
      { unfold L0m at 1. cbn [rho_sub rw]. rewrite sv_PB2ma.
        erewrite U_sub2; [| reflexivity | reflexivity |]; change (eval rho2 (SVar 106)) with (rw rho2 106); change (eval rho2 (SVar 109)) with (rw rho2 109);
          rewrite <- (proj1 Hag2 106%positive ltac:(cbn; lia)), <- (proj1 Hag2 109%positive ltac:(cbn; lia)), E106, U109, HU; lia. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH2 (rho_sub rho2 s_PB2ma_CB2m))].
      * intros w Hw. eapply SP_entails in Hw; [|exact ent_PB2ma_CB2m].
        replace (length M1 - L0m (rho_sub rho2 s_PB2ma_CB2m))%nat with (length M1 - L0m rho + k)%nat by lia. exact Hw.
      * apply GoodM_sub; [reflexivity|]. eapply GoodM_agree; [exact Hag2 | cbn; lia | exact HGM1].
      * lia.
      * lia.
    + eapply triple_conseq with (P := SP segs (Kx (TR (length M1 - L0m rho + k)) md0) PB2mb rho1); [| intros w Hw; exact Hw |].
      { intros w Hw. apply SP_add1; [exact Hw | | reflexivity]. cbn [holds]. change (eval rho1 (SVar 109)) with (rw rho1 109).
        erewrite U_addc; [| reflexivity | |]; change (eval rho1 (SVar 106)) with (rw rho1 106); rewrite ?U109, ?E106, ?HU; lia. }
      eapply run_tr; [exact run_PB2mb | reflexivity | apply okf |].
      intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
      *
        eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
        intros w Hw. pose proof (hd_fact rho2 L_PB2mb_0 _ _ w _ eq_refl Hw) as Hf.
        cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
        erewrite (U_addc rho2 (SVar 106) 7) in Hf; [| reflexivity | |];
          change (eval rho2 (SVar 106)) with (rw rho2 106) in *; change (eval rho2 (SVar 109)) with (rw rho2 109) in *.
        2,3: rewrite <- ?(proj1 Hag2 106%positive ltac:(cbn; lia)), ?E106, ?HU; lia.
        rewrite <- (proj1 Hag2 106%positive ltac:(cbn; lia)), <- (proj1 Hag2 109%positive ltac:(cbn; lia)), E106, U109, HU in Hf.
        exists (rho_sub rho2 s_PB2mb_Dm). split.
        { apply GoodM_sub; [reflexivity|]. eapply GoodM_agree; [exact Hag2 | cbn; lia | exact HGM1]. }
        eapply SP_entails in Hw; [|exact ent_PB2mb_Dm].
        replace (length MSG) with (length M1 - L0m rho + k)%nat; [exact Hw|]. lia.
      *
        apply triple_facts. intros HF. apply Forall_cons_iff in HF as [Hf _].
        cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Z.eqb_eq in Hf.
        erewrite (U_addc rho2 (SVar 106) 7) in Hf; [| reflexivity | |];
          change (eval rho2 (SVar 106)) with (rw rho2 106) in *; change (eval rho2 (SVar 109)) with (rw rho2 109) in *.
        2,3: rewrite <- ?(proj1 Hag2 106%positive ltac:(cbn; lia)), ?E106, ?HU; lia.
        rewrite <- (proj1 Hag2 106%positive ltac:(cbn; lia)), <- (proj1 Hag2 109%positive ltac:(cbn; lia)), E106, U109, HU in Hf.
        assert (ER : L0m (rho_sub rho2 s_PB2mb_CB1m) = (L0m rho + 7 - k)%nat).
        { unfold L0m at 1. cbn [rho_sub rw]. rewrite sv_PB2mb.
          erewrite (U_sub2 rho2 (SLit 7) _ 7 (Z.of_nat k - Z.of_nat (L0m rho))); [lia | apply U_lit64; lia | | lia].
          erewrite U_sub2; [reflexivity | | | lia]; change (eval rho2 (SVar 109)) with (rw rho2 109); change (eval rho2 (SVar 106)) with (rw rho2 106);
            rewrite <- ?(proj1 Hag2 109%positive ltac:(cbn; lia)), <- ?(proj1 Hag2 106%positive ltac:(cbn; lia)), ?U109, ?E106, ?HU; reflexivity. }
        eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH1 (rho_sub rho2 s_PB2mb_CB1m))].
        -- intros w Hw. eapply SP_entails in Hw; [|exact ent_PB2mb_CB1m].
           replace (length MSG - L0m (rho_sub rho2 s_PB2mb_CB1m))%nat with (length M1 - L0m rho + k)%nat by lia. exact Hw.
        -- apply GoodM_sub; [reflexivity|]. eapply GoodM_agree; [exact Hag2 | cbn; lia | exact HGM1].
        -- lia.
        -- lia.
  -
    intros rho HGM HR Hm. pose proof (proj1 HGM) as HG.
    assert (HU : bv_unsigned (rw rho 106) = Z.of_nat (L0m rho)) by (unfold L0m; pose proof (urange (rw rho 106)); lia).
    eapply triple_seq.
    { apply (writev_site1 CB1m (reg_sv CB1m 22) (length MSG - L0m rho) (skipn (7 - L0m rho) M2) rho HG);
        [rewrite Hnxc; lia | exact Hic | exact H17c | exact H10c | exact H12c | rewrite R22c, Hnxc; reflexivity | | |].
      + rewrite MSL. replace (14 + length argv0 - L0m rho)%nat with (length M1 + (7 - L0m rho))%nat by lia.
        rewrite MSG_skipB by lia. rewrite firstn_all. reflexivity.
      + rewrite length_skipn, M2_len. unfold MAX_RW_COUNT. lia.
      + intros tr ms md Hsp. exact (proj2 (bytes_CB1m rho tr ms md HGM Hsp)). }
    apply triple_ex; intros rho1. apply triple_ex; intros k.
    apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
    rewrite Hnxc in Hk, Hag1. rewrite length_skipn, M2_len in Hkb.
    assert (HGM1 : GoodM rho1) by (split; [exact HG1 | rewrite <- (proj1 (proj2 Hag1)); exact (proj2 HGM)]).
    assert (E106 : rw rho1 106 = rw rho 106) by (symmetry; apply (proj1 Hag1); lia).
    assert (U110 : bv_unsigned (rw rho1 110) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
    change (S_after_write CB1m (reg_sv CB1m 22)) with PB1m.
    eapply run_tr; [exact run_PB1m | reflexivity | apply okf |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
    +
      eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
      intros w Hw. pose proof (hd_fact rho2 L_PB1m_0 _ _ w _ eq_refl Hw) as Hf.
      cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
      change (eval rho2 (SVar 110)) with (rw rho2 110) in Hf. change (eval rho2 (SVar 106)) with (rw rho2 106) in Hf.
      rewrite <- (proj1 Hag2 110%positive ltac:(cbn; lia)), <- (proj1 Hag2 106%positive ltac:(cbn; lia)), U110, E106, HU in Hf.
      exists (rho_sub rho2 s_PB1m_Dm). split.
      { apply GoodM_sub; [reflexivity|]. eapply GoodM_agree; [exact Hag2 | cbn; lia | exact HGM1]. }
      eapply SP_entails in Hw; [|exact ent_PB1m_Dm].
      replace (length MSG) with (length MSG - L0m rho + k)%nat at 1; [exact Hw|]. lia.
    +
      apply triple_facts. intros HF. apply Forall_cons_iff in HF as [Hf _].
      cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Z.eqb_eq in Hf.
      change (eval rho2 (SVar 110)) with (rw rho2 110) in Hf. change (eval rho2 (SVar 106)) with (rw rho2 106) in Hf.
      rewrite <- (proj1 Hag2 110%positive ltac:(cbn; lia)), <- (proj1 Hag2 106%positive ltac:(cbn; lia)), U110, E106, HU in Hf.
      assert (ER : L0m (rho_sub rho2 s_PB1m_CB1m) = (L0m rho - k)%nat).
      { unfold L0m at 1. cbn [rho_sub rw]. rewrite sv_PB1m.
        erewrite U_sub2; [| reflexivity | reflexivity |]; change (eval rho2 (SVar 106)) with (rw rho2 106); change (eval rho2 (SVar 110)) with (rw rho2 110);
          rewrite <- (proj1 Hag2 106%positive ltac:(cbn; lia)), <- (proj1 Hag2 110%positive ltac:(cbn; lia)), E106, U110, HU; lia. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH1 (rho_sub rho2 s_PB1m_CB1m))].
      * intros w Hw. eapply SP_entails in Hw; [|exact ent_PB1m_CB1m].
        replace (length MSG - L0m (rho_sub rho2 s_PB1m_CB1m))%nat with (length MSG - L0m rho + k)%nat by lia. exact Hw.
      * apply GoodM_sub; [reflexivity|]. eapply GoodM_agree; [exact Hag2 | cbn; lia | exact HGM1].
      * lia.
      * lia.
Qed.

Lemma L_Mg : ltac2:(tb__ "0|1|
S1S3cU43S2eS38Q8A1Vargv0;A2M0A2S3cG0U49A2A2S7S55R1A1S83S2aVok;S4bS2aS4eS4fU0A1Vmd0;A2S8bR2A4S5aA4F_;Frho;F_;").
Proof using Hargc Hent Hfd2 Hinp HokK HokP.
  intros Hmid rho HGM. pose proof NU as NU'. pose proof (proj1 HGM) as HG. pose proof M1_len as ML. pose proof MSG_len as MSL.
  destruct cert_E_Mg as (_ & _ & _ & _ & _ & _ & _ & _ & R22 & Hi & H17 & H10 & H12 & Hnx & _).
  eapply triple_seq.
  { apply (writev_site2 E_Mg (reg_sv E_Mg 22) 0 M1 M2 rho HG);
      [rewrite Hnx; lia | exact Hi | exact H17 | exact H10 | exact H12 | rewrite R22, Hnx; reflexivity | | |].
    + cbn [skipn]. unfold MSG. rewrite firstn_all. reflexivity.
    + rewrite length_app, ML, M2_len. unfold MAX_RW_COUNT. lia.
    + intros tr ms md Hsp. exact (bytes_E_Mg rho tr ms md HGM Hmid Hsp). }
  apply triple_ex; intros rho1. apply triple_ex; intros k.
  apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
  rewrite Hnx in Hk, Hag1. rewrite length_app, ML, M2_len in Hkb.
  assert (HGM1 : GoodM rho1) by (split; [exact HG1 | rewrite <- (proj1 (proj2 Hag1)); exact (proj2 HGM)]).
  assert (U106 : bv_unsigned (rw rho1 106) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
  pose proof (G_v5 rho1 HG1) as V5.
  change (S_after_write E_Mg (reg_sv E_Mg 22)) with PAm. cbn [Nat.add].
  destruct (Nat.le_gt_cases k (7 + length argv0)) as [Hle|Hgt].
  -
    eapply triple_conseq with (P := SP segs (Kx (TR k) md0) PAma rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. apply SP_add1; [exact Hw | | reflexivity]. cbn [holds]. change (eval rho1 (SVar 106)) with (rw rho1 106).
      erewrite U_addc; [| exact V5 | unfold N0; lia | lia]. rewrite U106. unfold N0. lia. }
    eapply run_tr; [exact run_PAma | reflexivity | apply okf |].
    intros L rho2 [<-|[]] Hag2. cbn [lf_state].
    assert (EL : L0m (rho_sub rho2 s_PAma_CB2m) = (7 + length argv0 - k)%nat).
    { unfold L0m. cbn [rho_sub rw]. rewrite sv_PAma.
      erewrite (U_sub2 rho2 _ _ (N0 + 7) (Z.of_nat k)); [unfold N0; lia | | | unfold N0; lia].
      - erewrite U_addc; [reflexivity | | unfold N0; lia | lia]. change (eval rho2 (SVar 5)) with (rw rho2 5). rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)). exact V5.
      - change (eval rho2 (SVar 106)) with (rw rho2 106). rewrite <- (proj1 Hag2 106%positive ltac:(cbn; lia)). exact U106. }
    eapply triple_conseq; [| intros w Hw; exact Hw | apply (proj1 (loopm Hmid (14 + length argv0 - k)) (rho_sub rho2 s_PAma_CB2m))].
    + intros w Hw. eapply SP_entails in Hw; [|exact ent_PAma_CB2m].
      replace (length M1 - L0m (rho_sub rho2 s_PAma_CB2m))%nat with k by lia. exact Hw.
    + apply GoodM_sub; [reflexivity|]. eapply GoodM_agree; [exact Hag2 | cbn; lia | exact HGM1].
    + lia.
    + lia.
  -
    eapply triple_conseq with (P := SP segs (Kx (TR k) md0) PAmb rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. apply SP_add1; [exact Hw | | reflexivity]. cbn [holds]. change (eval rho1 (SVar 106)) with (rw rho1 106).
      erewrite U_addc; [| exact V5 | unfold N0; lia | lia]. rewrite U106. unfold N0. lia. }
    eapply run_tr; [exact run_PAmb | reflexivity | apply okf |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
    +
      apply triple_facts. intros HF. apply Forall_cons_iff in HF as [Hf _].
      cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Bool.negb_true_iff in Hf. apply Z.eqb_neq in Hf.
      erewrite (U_addc rho2 (SVar 5) 14) in Hf; [| reflexivity | |];
        change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 106)) with (rw rho2 106) in *.
      2,3: rewrite <- ?(proj1 Hag2 5%positive ltac:(cbn; lia)), ?V5; unfold N0; lia.
      rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)), <- (proj1 Hag2 106%positive ltac:(cbn; lia)), V5, U106 in Hf.
      assert (ER : L0m (rho_sub rho2 s_PAmb_CB1m) = (14 + length argv0 - k)%nat).
      { unfold L0m. cbn [rho_sub rw]. rewrite sv_PAmb.
        erewrite (U_sub2 rho2 (SLit 7) _ 7 (Z.of_nat k - (N0 + 7))); [unfold N0; lia | apply U_lit64; lia | | unfold N0 in *; lia].
        erewrite (U_sub2 rho2 _ _ (Z.of_nat k) (N0 + 7)); [lia | | | unfold N0; lia].
        - change (eval rho2 (SVar 106)) with (rw rho2 106). rewrite <- (proj1 Hag2 106%positive ltac:(cbn; lia)). exact U106.
        - erewrite U_addc; [reflexivity | | unfold N0; lia | lia]. change (eval rho2 (SVar 5)) with (rw rho2 5). rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)). exact V5. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (proj2 (loopm Hmid (14 + length argv0 - k)) (rho_sub rho2 s_PAmb_CB1m))].
      * intros w Hw. eapply SP_entails in Hw; [|exact ent_PAmb_CB1m].
        replace (length MSG - L0m (rho_sub rho2 s_PAmb_CB1m))%nat with k by lia. exact Hw.
      * apply GoodM_sub; [reflexivity|]. eapply GoodM_agree; [exact Hag2 | cbn; lia | exact HGM1].
      * unfold N0 in Hf. lia.
      * lia.
    +
      eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
      intros w Hw. pose proof (hd_fact rho2 L_PAmb_1 _ _ w _ eq_refl Hw) as Hf.
      cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Bool.negb_true_iff, Z.eqb_neq in Hf.
      erewrite (U_addc rho2 (SVar 5) 14) in Hf; [| reflexivity | |];
        change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 106)) with (rw rho2 106) in *.
      2,3: rewrite <- ?(proj1 Hag2 5%positive ltac:(cbn; lia)), ?V5; unfold N0; lia.
      rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)), <- (proj1 Hag2 106%positive ltac:(cbn; lia)), V5, U106 in Hf.
      exists (rho_sub rho2 s_PAmb_Dm). split.
      { apply GoodM_sub; [reflexivity|]. eapply GoodM_agree; [exact Hag2 | cbn; lia | exact HGM1]. }
      eapply SP_entails in Hw; [|exact ent_PAmb_Dm].
      replace (length MSG) with k; [exact Hw|]. unfold N0 in Hf. lia.
Qed.

Lemma cert_zm : ltac2:(tb__ "0|c|
S1S0S36S36S5S5A2M0S5A2SbcS52S8eA1M1A1S34G0S5S34S5S5SdP1A1M2S6S7bSbfA1A1A4S6N230A1A4A3S1S3cU2S2eSbS10S8eA1A2A2S1S0S2cS6aS9S68ScS6N298A1M3Z8M4S6Z0A1M5A3A1S11G1A1M6A3S2bA3S1S0S2cS6aS9S68ScS6N290A1G4G5A3A1G6A3S2bA3S1S0S5S8S8eZbA2SaS73G2G3A3A3S1S0S33S74A1M7S88S2aS15S8eA1A2S31S74S75A2M8A3S1S0S5S8S8eZ11M9A2S6Z42A1A3S1S0S5S8S8eZaMaA2S6Z2A1MbA3S1S0S5S8S8eZcA2S6Z1A1A3S1S0G7S88S2aS15S93A1A2G8A3S1S0S5S8S93G9A2S6Z5eA1A3S0S5S8S93GaA2GbA3A2A2A2A2A2A2A2A2A2A2A2").
Proof using Hargc LEN N0 STR. vm_compute. repeat split; (reflexivity || lia). Qed.

Lemma L_Dm : ltac2:(tb__ "0|0|
S7S55R1A1S83S2aVok;S4bS2aS4eS4fS2eS38Q8A1S51A2A1Vmd0;A2S92R2A4S82S3L_;A4F_;Frho;").
Proof using Hargc Hent Hfd2 Hfs Hinp HokK HokP Hokh.
  intros rho HGM. pose proof NU as NU'.
  destruct cert_zm as (Hrng & Hlen & C1 & C2 & R11 & Hi & H17 & H10 & H12 & Hix & H17x & H10x).
  eapply run_tr; [exact run_Dm | reflexivity | apply okf |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  pose proof (GoodM_agree _ _ _ Hag1 ltac:(cbn; lia) HGM) as HGM1. pose proof (proj1 HGM1) as HG1. pose proof (G_v1 rho1 HG1) as V1.
  eapply triple_seq.
  { apply triple1_triple.
    apply (triple1_writev01J segs ok (liftK (Kx (TR (length MSG)) md0)) E_Zm rho1 2);
      [apply ok_frame_liftK; apply okf | eapply ok_pframeJ_of_tcons; [apply HokP; intros tr0 md0_ H0; exact H0 | intros r tr md Hk; exact (Ktc _ tr md Hk)]
      | exact Hi | exact H17 | exact H10 | exact H12 | lia | intros r tr md [_ ->]; exact Hfd2 |].
    intros tr ms md Hsp _. rewrite R11.
    assert (A0 : bv_unsigned (eval rho1 (SAlu ALU_ADD (SVar 1) (SLit (-664)))) = bv_unsigned sp - 664).
    { erewrite U_addc; [reflexivity | exact V1 | lia | lia]. }
    exists (eval rho1 (SLit 0)). split.
    - eapply (iov_field_lo rho1 E_Zm tr ms md (-664)); [exact HG1 | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia].
    - split; [|split; [rewrite A0; unfold TASK_SIZE; lia | rewrite U_lit64 by lia; unfold TASK_SIZE; lia]].
      change (Z_to_bv 64 0) with (eval rho1 (SLit 0)).
      eapply (iov_field_lo rho1 E_Zm tr ms md (-656)); [exact HG1 | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]. }
  change (SPJ segs (liftK (Kx (TR (length MSG)) md0)) (S_after E_Zm (SLit 0) (ss_objs E_Zm) (ss_next E_Zm)) rho1) with (SP segs (Kx (TR (length MSG)) md0) PZm rho1).
  eapply run_tr; [exact run_PZm | reflexivity | apply okf |].
  intros L rho2 [<-|[]] Hag2. cbn [lf_state].
  apply (triple_exit_eval segs ok SpecT (Kx (TR (length MSG)) md0) E_exitm rho2 2);
    [apply okf | apply okp | exact Hokh | exact Hix | left; exact H17x | rewrite H10x; rewrite U_lit64 by lia; reflexivity |].
  intros tr md [-> ->]. rewrite TR_all by lia. rewrite Hfs. exact final_in_spec.
Qed.

Theorem usage_mid_safe : ltac2:(tb__ "0|1|
S1S3cU43S2eS38Q8A1Vargv0;A2M0A2S3cG0U49A2A2S0S2cS8fVN0;S89S2aS9aS35S3eA1S97VN0;A1S2bA5A2S2bA3S7VJI;R1A1S83S2aVok;S4bS2aS4eS35S40A1Vmd0;A2Sd2R2A4S82S3L_;A4F_;Frho;F_;F_;").
Proof using Hargc Hent Hfd2 Hfs Hinp HokK HokP Hokh LEN STR.
  intros Hmid Hchk rho HJ.
  destruct (check_core_m_sound N0 _ Hchk) as (a & b & wx & o & bl & Hwf & _).
  eapply triple_conseq with (P := fun w => exists rho', Good rho' /\ SP segs (Kx (TR 0) md0) S_use rho' w); [| intros w Hw; exact Hw |].
  { intros w Hw. apply (use_intro rho w HJ). exact Hw. }
  apply triple_ex; intros rho1. apply triple_pure; intros HG1.
  eapply triple_seq.
  { eapply run_tr; [exact run_use | reflexivity | apply okf |].
    intros L rho2 [<-|[]] Hag2. cbn [lf_state].
    pose proof (Good_agree _ _ _ Hag2 ltac:(cbn; lia) HG1) as HG2.
    apply (call_path segs FirstNul ok (Kx (TR 0) md0) (Kx (TR 0) md0) E_sn E_snX Pre_strnlen xs_pre s_sn R_sn Posts_strnlen _ rho2
             xs_pre_ok efr_sn chk_sn fb_sn).
    - intros rho3 HF. apply strnlen_sum; [apply okf | exact HF].
    - intros ms _. apply FirstNul_call. exact HG2.
    - intros L rho3 [<-|[]] Hag3 HF3. cbn [lf_state]. replace (ss_next Pre_strnlen) with NF by reflexivity. rewrite T_imp_eq.
      pose proof (Good_agree _ _ _ Hag3 ltac:(cbn; lia) HG2) as HG3.
      apply (post_path segs ok (Kx (TR 0) md0) T_imp T_sn (ss_facts E_sn) xs_post rho3 _ fb_sn2 xs_post_ok HF3).
      apply triple_facts. intros HFT.
      eapply triple_conseq with (P := SP segs (Kx (TR 0) md0) (Tn N0) rho3); [| intros w Hw; exact Hw | apply (L_mid_pre N0 Hchk eq_refl); exact HG3].
      intros w Hsp. apply (Tn_intro N0 rho3 w HG3 eq_refl Hwf).
      eapply (SP_restate segs _ rho3 T_sn T_sn1 w); [exact swf_T_sn1 | exact diff_sn | | constructor | exact Hsp].
      constructor; [|constructor]. cbn [fst snd]. exact (proj1 (Forall_forall _ _) HFT _ fact_T_sn). }
  apply triple_ex; intros rho4. apply triple_pure; intros HG4.
  eapply triple_seq; [apply (L_Mg Hmid); exact HG4|].
  apply triple_ex; intros rho5. apply triple_pure; intros HG5.
  apply L_Dm. exact HG5.
Qed.

Lemma eL_Mg : ltac2:(tb__ "0|1|
S1S3cU43S2eS38Q8A1Vargv0;A2M0A2S3cG0U49A2A2S7S55R1A1S84S2aS4bS2aS4eS4fU0A1Vmd0;A2S8bR2A4S5aA3F_;Frho;F_;").
Proof using Hargc Hent Hfd2 Hinp.
  intros Hmid rho HGM. pose proof NU as NU'. pose proof (proj1 HGM) as HG. pose proof M1_len as ML. pose proof MSG_len as MSL.
  destruct cert_E_Mg as (_ & _ & _ & _ & _ & _ & _ & _ & R22 & Hi & H17 & H10 & H12 & Hnx & _).
  eapply etriple_seq.
  { apply (ewritev_site2 E_Mg (reg_sv E_Mg 22) 0 M1 M2 rho HG);
      [rewrite Hnx; lia | exact Hi | exact H17 | exact H10 | exact H12 | rewrite R22, Hnx; reflexivity | | |].
    + cbn [skipn]. unfold MSG. rewrite firstn_all. reflexivity.
    + rewrite length_app, ML, M2_len. unfold MAX_RW_COUNT. lia.
    + intros tr ms md Hsp. exact (bytes_E_Mg rho tr ms md HGM Hmid Hsp). }
  apply etriple_ex; intros rho1.
  apply etriple_pure; intros HG1. apply etriple_pure; intros Hag1. apply etriple_pure; intros Hk.
  rewrite Hnx in Hk, Hag1. rewrite length_app, ML, M2_len in Hk |- *.
  assert (HGM1 : GoodM rho1) by (split; [exact HG1 | rewrite <- (proj1 (proj2 Hag1)); exact (proj2 HGM)]).
  assert (U106 : bv_unsigned (rw rho1 106) = 14 + N0) by (rewrite Hk; rewrite Z_to_bv_small by (rewrite mod64; lia); unfold N0; lia).
  pose proof (G_v5 rho1 HG1) as V5.
  change (S_after_write E_Mg (reg_sv E_Mg 22)) with PAm. cbn [Nat.add].
  eapply etriple_conseq with (P := SP segs (Kx (TR (7 + length argv0 + 7)) md0) PAmb rho1); [| intros w Hw; exact Hw |].
  { intros w Hw. apply SP_add1; [exact Hw | | reflexivity]. cbn [holds]. change (eval rho1 (SVar 106)) with (rw rho1 106).
    erewrite U_addc; [| exact V5 | unfold N0; lia | lia]. rewrite U106. lia. }
  eapply erun_tr; [exact run_PAmb | reflexivity |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
  - apply etriple_facts. intros HF. apply Forall_cons_iff in HF as [Hf _]. exfalso.
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Bool.negb_true_iff in Hf. apply Z.eqb_neq in Hf. apply Hf.
    erewrite (U_addc rho2 (SVar 5) 14); [| reflexivity | |];
      change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 106)) with (rw rho2 106) in *.
    2,3: rewrite <- ?(proj1 Hag2 5%positive ltac:(cbn; lia)), ?V5; unfold N0; lia.
    rewrite <- (proj1 Hag2 5%positive ltac:(cbn; lia)), <- (proj1 Hag2 106%positive ltac:(cbn; lia)), V5, U106. lia.
  - intros w Hw. exists w. split; [apply wsteps_refl|]. exists (rho_sub rho2 s_PAmb_Dm). split.
    { apply GoodM_sub; [reflexivity|]. eapply GoodM_agree; [exact Hag2 | cbn; lia | exact HGM1]. }
    eapply SP_entails in Hw; [|exact ent_PAmb_Dm]. rewrite MSL. replace (14 + length argv0)%nat with (7 + length argv0 + 7)%nat by lia. exact Hw.
Qed.

Lemma eL_Dm : ltac2:(tb__ "0|1|
S7S55R1A1S84S2aS4bS2aS4eS4fS2eS38Q8A1S51A2A1Vmd0;A2S92R2A4S82S0S2dS40A1S85R1A1S37S40Sc6Z2M0S51A2S32S40Sc7Vfs;G0A2S35S40A1A3A3A3Lw;A3F_;Frho;").
Proof using Hargc Hent Hfd2 Hfs Hinp.
  intros rho HGM. pose proof NU as NU'.
  destruct cert_zm as (Hrng & Hlen & C1 & C2 & R11 & Hi & H17 & H10 & H12 & Hix & H17x & H10x).
  eapply erun_tr; [exact run_Dm | reflexivity |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  pose proof (GoodM_agree _ _ _ Hag1 ltac:(cbn; lia) HGM) as HGM1. pose proof (proj1 HGM1) as HG1. pose proof (G_v1 rho1 HG1) as V1.
  eapply etriple_seq.
  { apply (etriple_writev01J segs (liftK (Kx (TR (length MSG)) md0)) E_Zm rho1 2);
      [exact Hi | exact H17 | exact H10 | exact H12 | lia | intros r tr md [_ ->]; exact Hfd2 |].
    intros tr ms md Hsp _. rewrite R11.
    assert (A0 : bv_unsigned (eval rho1 (SAlu ALU_ADD (SVar 1) (SLit (-664)))) = bv_unsigned sp - 664).
    { erewrite U_addc; [reflexivity | exact V1 | lia | lia]. }
    exists (eval rho1 (SLit 0)). split.
    - eapply (iov_field_lo rho1 E_Zm tr ms md (-664)); [exact HG1 | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia].
    - split; [|split; [rewrite A0; unfold TASK_SIZE; lia | rewrite U_lit64 by lia; unfold TASK_SIZE; lia]].
      change (Z_to_bv 64 0) with (eval rho1 (SLit 0)).
      eapply (iov_field_lo rho1 E_Zm tr ms md (-656)); [exact HG1 | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]. }
  change (SPJ segs (liftK (Kx (TR (length MSG)) md0)) (S_after E_Zm (SLit 0) (ss_objs E_Zm) (ss_next E_Zm)) rho1) with (SP segs (Kx (TR (length MSG)) md0) PZm rho1).
  eapply erun_tr; [exact run_PZm | reflexivity |].
  intros L rho2 [<-|[]] Hag2. cbn [lf_state].
  eapply etriple_conseq; [intros w Hw; exact Hw | |
    apply (etriple_exit_eval segs (Kx (TR (length MSG)) md0) E_exitm rho2 2 Hix (or_introl H17x))].
  - intros w (tr & md & [-> ->] & ->). rewrite TR_all by lia. rewrite Hfs. reflexivity.
  - rewrite H10x. rewrite U_lit64 by lia. reflexivity.
Qed.

Theorem usage_mid_exists : ltac2:(tb__ "0|3|
S1S3cU43S2eS38Q8A1Vargv0;A2M0A2S3cG0U49A2A2S0S2cS8fVN0;S89S2aS9aS35S3eA1S97VN0;A1S2bA5A2S2bA3S7VJI;R1A1S84S2aS4bS2aS4eS35S40A1M1Vmd0;A2Sd2R2A4S82S0S2dS40A1S85R1A1S37S40Sc6Z2M2Sc8Vargv0;A1A2S32S40Sc7Vfs;G2A2G1A3A3A3Lw;A3F_;Frho;F_;F_;").
Proof using Hargc Hent Hfd2 Hfs Hinp LEN STR.
  intros Hmid Hchk rho HJ. rewrite <- MSG_usage.
  destruct (check_core_m_sound N0 _ Hchk) as (a & b & wx & o & bl & Hwf & _).
  eapply etriple_conseq with (P := fun w => exists rho', Good rho' /\ SP segs (Kx (TR 0) md0) S_use rho' w); [| intros w Hw; exact Hw |].
  { intros w Hw. apply (use_intro rho w HJ). exact Hw. }
  apply etriple_ex; intros rho1. apply etriple_pure; intros HG1.
  eapply etriple_seq.
  { eapply erun_tr; [exact run_use | reflexivity |].
    intros L rho2 [<-|[]] Hag2. cbn [lf_state].
    pose proof (Good_agree _ _ _ Hag2 ltac:(cbn; lia) HG1) as HG2.
    apply (ecall_path segs FirstNul (Kx (TR 0) md0) (Kx (TR 0) md0) E_sn E_snX Pre_strnlen xs_pre s_sn R_sn Posts_strnlen _ rho2
             xs_pre_ok efr_sn chk_sn fb_sn).
    - intros rho3 HF. apply strnlen_sum_ex. exact HF.
    - intros ms _. apply FirstNul_call. exact HG2.
    - intros L rho3 [<-|[]] Hag3 HF3. cbn [lf_state]. replace (ss_next Pre_strnlen) with NF by reflexivity. rewrite T_imp_eq.
      pose proof (Good_agree _ _ _ Hag3 ltac:(cbn; lia) HG2) as HG3.
      apply (epost_path segs (Kx (TR 0) md0) T_imp T_sn (ss_facts E_sn) xs_post rho3 _ fb_sn2 xs_post_ok HF3).
      apply etriple_facts. intros HFT.
      eapply etriple_conseq with (P := SP segs (Kx (TR 0) md0) (Tn N0) rho3); [| intros w Hw; exact Hw | apply (eL_mid_pre N0 Hchk eq_refl); exact HG3].
      intros w Hsp. apply (Tn_intro N0 rho3 w HG3 eq_refl Hwf).
      eapply (SP_restate segs _ rho3 T_sn T_sn1 w); [exact swf_T_sn1 | exact diff_sn | | constructor | exact Hsp].
      constructor; [|constructor]. cbn [fst snd]. exact (proj1 (Forall_forall _ _) HFT _ fact_T_sn). }
  apply etriple_ex; intros rho4. apply etriple_pure; intros HG4.
  eapply etriple_seq; [apply (eL_Mg Hmid); exact HG4|].
  apply etriple_ex; intros rho5. apply etriple_pure; intros HG5.
  apply eL_Dm. exact HG5.
Qed.

End Usage.
End Drv_usage.

Module Drv_usage_all.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_small_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_mid_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_small_chk1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G2.Drv_usage_small_chk2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G1.Drv_usage_small_chk3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G2.Drv_usage_small_chk4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G2.Drv_usage_mid_chk OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_usage__G3.Drv_usage.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma check_range_sound : ltac2:(tb__ "0|1|
S30S30S30S0S2cSa2R3R2A2S2bA3S1S3cR4R2A2S3dR2Sa4R4R3A2A2A2S0S2cS9bS7aR3A1M0S89S2aS9aS35S3eA1S97G0A1S2bA5A2S2bA3F_;F_;Fk;Flen;Fa;").
Proof.
  intros a len k H Hk. unfold check_range in H.
  exact (proj1 (forallb_forall _ _) H k ltac:(apply in_seq; lia)).
Qed.

Lemma check_small : ltac2:(tb__ "0|1|
S30S3cR1U42A2S0S2cS9bS7aR2A1M0S89S2aS9aS35S3eA1S97G0A1S2bA5A2S2bA3F_;Fk;").
Proof.
  intros k Hk.
  destruct (Nat.lt_ge_cases k 17); [eapply (check_range_sound 0 17); [exact check_range_1 | lia]|].
  destruct (Nat.lt_ge_cases k 34); [eapply (check_range_sound 17 17); [exact check_range_2 | lia]|].
  destruct (Nat.lt_ge_cases k 51); [eapply (check_range_sound 34 17); [exact check_range_3 | lia]|].
  eapply (check_range_sound 51 16); [exact check_range_4 | lia].
Qed.

Lemma check_range_m_sound : ltac2:(tb__ "0|1|
S30S30S30S0S2cS96R3R2A2S2bA3S1S3cR4R2A2S3dR2Sa4R4R3A2A2A2S0S2cS8fS7aR3A1M0S89S2aS9aS35S3eA1S97G0A1S2bA5A2S2bA3F_;F_;Fk;Flen;Fa;").
Proof.
  intros a len k H Hk. unfold check_range_m in H.
  exact (proj1 (forallb_forall _ _) H k ltac:(apply in_seq; lia)).
Qed.

Lemma check_mid : ltac2:(tb__ "0|1|
S30S1S3cU43R1A2S3cR1U49A2A2S0S2cS8fS7aR2A1M0S89S2aS9aS35S3eA1S97G0A1S2bA5A2S2bA3F_;Fk;").
Proof. intros k Hk. apply (check_range_m_sound 67 7 k check_range_mid). lia. Qed.

Section All.
Variable sp brk mb : word.
Variable draw : EntryDraw.
Variable lim : Z.
Variable inp : ProcInput.
Hypothesis Hent : ltac2:(tb__ "0|0|
Se5Se1ScdVsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Let argv := in_argv inp.
Let argv0 : list byte := nth 0 argv [].
Hypothesis Hargc : length argv <> 2%nat.
Variable md0 : Model.
Hypothesis Hfd2 : ltac2:(tb__ "0|1|
S0S33S42A1S45S47Vmd0;A1S3aQ40Z2A2M0A2S31S42S44G0A1A2A3").
Hypothesis Hfs : ltac2:(tb__ "0|0|
S0Se3S48Vmd0;A1S46Vinp;A1A3").
Variable ok : world -> Prop.
Hypothesis HokK : ltac2:(tb__ "0|0|
S2dS40A1S41OF_;F_;Sd5Sc9Vinp;A1R1A2S4cS2aVok;R2A3F_;FK;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S2dS40A1S41OF_;F_;Sd5Sc9Vinp;A1R1A2Sd0S2aVok;R2A3F_;FK;").
Hypothesis Hokh : ltac2:(tb__ "0|0|
Sd6Vok;Sc9Vinp;A1A2").

Theorem usage_safe : ltac2:(tb__ "0|0|
S7Sc0S2aSdfSe0Vsp;Vdraw;Vinp;R1A7S83S2aVok;S4bS2aS4eS35S40A1Vmd0;A2Sd2R2A4S82S3L_;A4F_;Frho;").
Proof using Hargc Hent Hfd2 Hfs Hinp HokK HokP Hokh.
  intros rho HJ. destruct (Nat.le_gt_cases (length argv0) 66) as [Hs|Hgt]; [|destruct (Nat.le_gt_cases (length argv0) 73) as [Hm|Hb]].
  - exact (usage_small_safe sp brk mb draw inp Hent Hinp Hargc md0 Hfd2 Hfs ok HokK HokP Hokh Hs (check_small (length argv0) Hs) rho HJ).
  - assert (Hm2 : (67 <= length argv0 <= 73)%nat) by lia.
    exact (usage_mid_safe sp brk mb draw inp Hent Hinp Hargc md0 Hfd2 Hfs ok HokK HokP Hokh Hm2 (check_mid (length argv0) Hm2) rho HJ).
  - assert (Hb2 : (74 <= length argv0)%nat) by lia.
    exact (usage74_safe sp brk mb draw inp Hent Hinp Hargc md0 Hfd2 Hfs ok HokK HokP Hokh Hb2 rho HJ).
Qed.

Theorem usage_exists : ltac2:(tb__ "0|2|
S7Sc0S2aSdfSe0Vsp;Vdraw;Vinp;R1A7S84S2aS4bS2aS4eS35S40A1M0Vmd0;A2Sd2R2A4S82S0S2dS40A1S85R1A1S37S40Sc6Z2M1Sc8Vargv0;A1A2S32S40Sc7S46Vinp;A1G1A2G0A3A3A3Lw;A3F_;Frho;").
Proof using Hargc Hent Hfd2 Hfs Hinp.
  intros rho HJ. destruct (Nat.le_gt_cases (length argv0) 66) as [Hs|Hgt]; [|destruct (Nat.le_gt_cases (length argv0) 73) as [Hm|Hb]].
  - exact (usage_small_exists sp brk mb draw inp Hent Hinp Hargc md0 Hfd2 Hfs Hs (check_small (length argv0) Hs) rho HJ).
  - assert (Hm2 : (67 <= length argv0 <= 73)%nat) by lia.
    exact (usage_mid_exists sp brk mb draw inp Hent Hinp Hargc md0 Hfd2 Hfs Hm2 (check_mid (length argv0) Hm2) rho HJ).
  - assert (Hb2 : (74 <= length argv0)%nat) by lia.
    exact (usage74_exists sp brk mb draw inp Hent Hinp Hargc md0 Hfd2 Hfs Hb2 rho HJ).
Qed.
End All.
End Drv_usage_all.
