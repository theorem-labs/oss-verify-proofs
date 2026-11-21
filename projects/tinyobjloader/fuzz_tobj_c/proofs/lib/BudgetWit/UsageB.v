(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made from P/Drv_usage__G3.v: its safety half (usage_safe and the lemmas it uses) with the syscall-frame obligation restricted to a non-allocation call number (BudgetWit.NoAlloc.ok_pframe_na), at the three writev sites and the three exit sites through BudgetWit.SysNA. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the initial-valuation invariant Jinit taking the launch's mmap base; the usage path per CONFIG_RSEQ over the new entry-stack layout, as P/Drv_usage__G3.v takes it: the main entry and its states taken per value of the flag, the strings object carved by recarve_strs at its new arity, the layout's numbers from Lib/InitState.v; the first writev reached by every leaf of the run past the first, each passing the per-leaf check, argv[0] being no longer aligned; lemmas whose section variables do not reach sp and draw clear STR and LEN, which now depend on them, before lia; the per-flag certificate statements written as plain text, their bare explicit arguments parenthesised; the launch model's channel reader, LPS 08b1429, as a premise of the writev sites, as SysNA's writev lemmas take it; a per-flag leaf's first fact read off both values of the flag; the leaf's substitution keeping variable 13, which Jinit now fixes). *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "False"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "valuation"; "reg_sv"; "cell"; "SAlu"; "sobj"; "mkCell"; "SVar"; "sprop"; "sstate"; "ss_objs"; "ob_cells"; "ss_next"; "SPUle"; "ss_facts"; "ss_pc"; "eval"; "agree_below"; "rw"; "holds"; "obj_wf"; "rd_bytes"; "DList"; "mkObj"; "ob_dflt"; "rl"; "dflt_writable"; "is_arr"; "ob_hi"; "ob_lo"; "swf"; "obj_holds"; "ss_lenient"; "SPBranch"; "sprop_below"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "length"; "false"; "nat"; "Some"; "cons"; "option"; "pair"; "nil"; "prod"; "app"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_add"; "@Corelib.Init.Peano"; "le"; "lt"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "read_bytes_map"; "FdChannel"; "fd_lookup"; "in_fs"; "m_fds"; "m_fs"; "read_u64"; "WriteEv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "ok_frame"; "LQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.BudgetWit.UsageB.Drv_usage"; "Kx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.BudgetWit.UsageB.Drv_usage.Usage"; "TR"; "Good"; "MSG"; "ob0"; "M1"; "ob1"; "GoodM"; "GoodW"; "M2"; "Q_at"; "QD1"; "QDm"; "QM_at"; "BL_input"; "BL_usage"; "L0'"; "L0_of"; "L0g"; "L0m"; "OB_ibuf2"; "QD2"; "QDg"; "QW_at"; "R_of"; "sub_id7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "cell_eqb"; "entails"; "@Stdlib.Lists.List"; "existsb"; "In"; "nth_error"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "BLit"; "beval"; "cells_bytes"; "bexp_eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "instr"; "Ecall"; "ALU_SUB"; "BC_LTU"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "opp"; "lt"; "sub"; "pow"; "to_nat"; "mul"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "etriple"; "w_tr"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "instr_at"; "sym_run"; "lf_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G1.Drv_usage_mid_states"; "E_Mg"; "CB2m"; "CB1m"; "E_Zm"; "check_core_m"; "RO_INPUT"; "BLm"; "Dm"; "E_exitm"; "GLm"; "xs_ibuf2"; "check_range_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G1.Drv_usage_small_states"; "Tn"; "E_Wg"; "CBg"; "FUELn"; "check_core"; "Dg"; "E_exitg"; "sub_ok_n"; "BLn"; "BNZ3"; "GLg"; "check_range"; "xs_ibuf"; "@Corelib.Init.Nat"; "add"; "sub"; "@Corelib.Lists.ListDef"; "skipn"; "map"; "firstn"; "nth"; "seq"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G1.Drv_usage_states"; "E_A1"; "E_A2"; "CB1"; "CB2"; "CB3"; "E_exit"; "S_use"; "D1"; "D2"; "E_sn"; "R_sn"; "T_imp"; "T_sn1"; "T_sn74"; "X_ovf"; "s_sn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "obj_rng"; "list_eqb"; "S_after_write"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "STK_FREE"; "Jinit"; "@Stdlib.Strings.Ascii"; "Ascii"; "@Stdlib.Strings.String"; "String"; "EmptyString";
"@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_read_byte"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "wr"; "ex"; "msg_usage"; "Spec"; "str"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "mkEntry"; "is_prefix"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "smatch_pending"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.BudgetWit.NoAlloc"; "ok_pframe_na"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.StartStates"; "S_main"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs"; "strs_tail"; "O_strs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "K_tcons"; "ok_halted"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "rho_absorb"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "apply_xforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Init"; "pcP"; "phP"; "imgP"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "tab"; "valid_entry48"; "img_len"; "pad_len"; "str_off"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Str_memchr"; "FirstNul"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Init.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Str_memchr.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Str_strnlen.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.StartStates.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.BudgetWit.NoAlloc.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.BudgetWit.SysNA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Drv_usage.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import Stdlib.Strings.Ascii Stdlib.Strings.String.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Str_memchr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Str_strnlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.StartStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G1.Drv_usage_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G1.Drv_usage_small_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G1.Drv_usage_mid_states.

Import ListNotations.
Import StrAddr. Import UAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.

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

(* LPS 727298f3: the main entry per CONFIG_RSEQ ([S_main r]): its objects as recarve_strs reads them, by
   computation for each value of the flag. *)
Lemma S_main_objs : forall r, ss_objs (S_main r)
  = [obj_main r 0; obj_main r 1; obj_main r 2; obj_main r 3; O_str0; O_rand; obj_main r 6].
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma S_main_rngs : forall r,
  obj_rng (obj_main r 0) = ((SVar 1, SLit (- STK_FREE)), SLit 0)
  /\ obj_rng (obj_main r 1) = ((SVar 1, SLit 0), SLit 16)
  /\ obj_rng (obj_main r 2) = ((env_base, SLit 0), SAlu ALU_ADD (sll3 3) (SLit 8))
  /\ obj_rng (obj_main r 3) = ((aux_base, SLit 0), SLit (Z.of_nat (auxv_size r)))
  /\ obj_rng (obj_main r 6) = ((SLit 0, SLit dataP_lo), SLit dataP_hi).
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Lemma S_main_rl3 : forall r, state_has_rl 3 (S_main r) = false.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma S_main_next : forall r, (ss_next (S_main r) <= 25)%positive.
Proof. intros [|]; vm_compute; discriminate. Qed.
Lemma swf_S_main_rc : forall r, swf (S_main_rc r) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

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
(* LPS 08b1429: a nonempty writev needs the channel's reader ([writev_spec]'s SIGPIPE arm);
   [md0] is the launch model, whose reader [Run.valid_input_either] pins true. *)
Hypothesis Hrdr0 : m_channel_reader md0 = true.
Variable ok : world -> Prop.
Let SpecT : list event -> Prop := Spec inp.
Hypothesis HokK : ltac2:(tb__ "0|0|
S2dS40A1S41OF_;F_;Sd5VSpecT;R1A2S4cS2aVok;R2A3F_;FK;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S2dS40A1S41OF_;F_;Sd5VSpecT;R1A2Sd0S2aVok;R2A3F_;FK;").
Hypothesis Hokh : ok_halted ok SpecT.

Lemma Hsp : valid_sp sp. Proof using Hent. exact (proj1 Hent). Qed.
Lemma Hlaunch : entry_launch_ok_va Sv48 (mkEntry sp brk mb draw) inp.
Proof using Hent. exact (proj2 (proj2 (proj2 (proj2 Hent)))). Qed.
Let JI : ltac2:(tb__ "0|0|
S7OFrho;") := ltac2:(tb__ "0|0|
Sc0S2aSdfSe0Vsp;Vmb;Vdraw;Vinp;A7").
Let STR : Z := Z.of_nat (str_off inp sp draw).
Let LEN : Z := Z.of_nat (img_len inp sp draw).
Let N0 := Z.of_nat (length argv0).
(* The run's CONFIG_RSEQ: the main entry and every state of the path are taken at it. *)
Let rq : bool := kb_rseq (in_kernel inp).

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
Proof using Hargc. clear STR LEN. unfold MSG. rewrite length_app, M1_len, M2_len. lia. Qed.
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
Proof using Hargc. clear STR LEN. intros n Hn. unfold TR. rewrite firstn_all2 by lia. reflexivity. Qed.
Lemma firstn_add_skipn : forall {A} (l : list A) n k, firstn n l ++ firstn k (skipn n l) = firstn (n + k) l.
Proof using .
  intros A l n. revert l. induction n as [|n IH]; intros l k; [reflexivity|].
  destruct l as [|x l]; cbn; [rewrite firstn_nil; reflexivity|]. f_equal. apply IH.
Qed.
Lemma TR_app : ltac2:(tb__ "0|1|
S30S30S0S2dS40A1S37S40S4fR2A1Sa7S38Q8A1M0S40S4aS3aQ40Z2A2A1Sa8G0R1Sa6G0R2S51A3A3A4A3S4fSa4R2R1A2A1A3Fk;Fn;").
Proof using . intros n k. unfold TR, wr. rewrite <- map_app, firstn_add_skipn. reflexivity. Qed.

(* LPS 727298f3: the numbers the usage path reads, over the new entry-stack layout (Lib/InitState.v's
   [nums], [execfn_nums], [LEN_fit] and [LEN_bound]): the strings start at [STR], above the random
   bytes; argv's and envp's strings and AT_EXECFN's name lie in [STR, LEN), 9 bytes before its end. *)
Lemma NU :
  (140735340871680 <= bv_unsigned sp <= 140737488355328)
  /\ 16 <= STR
  /\ N0 + 1 <= Z.of_nat (tab argv)
  /\ N0 <= 131071
  /\ STR + Z.of_nat (tab argv) + Z.of_nat (tab envp) + 9 <= LEN
  /\ LEN <= 4194304 - 16
  /\ Z.of_nat (tab argv) <= 2097152
  /\ Z.of_nat (tab envp) <= 131072
  /\ (1 <= Z.of_nat (length argv) <= 1024)
  /\ Z.of_nat (length envp) <= 256
  /\ bv_unsigned sp + LEN <= 140737488355328
  /\ bv_unsigned sp mod 16 = 0.
Proof using Hargc Hent Hinp argv0.
  pose proof (nums pcP phP sp brk mb draw inp Hsp Hinp Hlaunch) as N2.
  pose proof (execfn_nums pcP phP sp brk mb draw inp Hsp Hinp Hlaunch) as (_ & EX).
  pose proof (LEN_fit pcP phP sp brk mb draw inp Hlaunch) as LF.
  pose proof (LEN_bound pcP phP sp brk mb draw inp Hinp Hlaunch) as LB.
  cbv zeta in N2, EX, LF, LB. rewrite sp_hi_val in LF.
  unfold STR, LEN, N0, argv0, argv, envp in *. lia.
Qed.

Definition Good (rho : valuation) : Prop :=
  JI rho /\ rl rho 3 = strs_tail inp /\ bv_unsigned (rw rho 25) = LEN - STR.

Lemma Good_agree : ltac2:(tb__ "0|1|
S3fS7S7S17R3R2R1A3Se2P1aR4A2S50R4A1M0G0F_;F_;F_;Frho';Frho;Fn;").
Proof using Hargc.
  intros n rho rho' (Hw & Hl & Hm) Hn (HJ & H3 & H25). split; [|split].
  - destruct HJ; constructor; rewrite <- ?Hw by lia; auto. + rewrite <- Hl; auto. + rewrite <- Hl; auto. + intros a. rewrite <- Hm. auto.
  - rewrite <- Hl. exact H3.
  - rewrite <- Hw by lia. exact H25.
Qed.

(* LPS 727298f3: [Jinit] also fixes variable 13 (AT_EXECFN's address), so a substitution keeps it. *)
Definition sub_id7 (s : wsub) : bool :=
  forallb (fun i => sv_eqb (wsub_get s i) (SVar i)) [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 25; 13]%positive.

Lemma Good_sub : ltac2:(tb__ "0|0|
Sd8S7S0S2cS67R2A1S2bA3S50R2A1S50Sd7R3R4A2A1F_;F_;Frho;Fs;").
Proof using .
  intros s rho Hs (HJ & H3 & H25). unfold sub_id7 in Hs. cbn [forallb] in Hs.
  apply andb_prop in Hs as [E1 Hs]. apply andb_prop in Hs as [E2 Hs]. apply andb_prop in Hs as [E3 Hs].
  apply andb_prop in Hs as [E4 Hs]. apply andb_prop in Hs as [E5 Hs]. apply andb_prop in Hs as [E6 Hs].
  apply andb_prop in Hs as [E8 Hs]. apply andb_prop in Hs as [E9 Hs]. apply andb_prop in Hs as [E10 Hs]. apply andb_prop in Hs as [E11 Hs].
  apply andb_prop in Hs as [E7 Hs]. apply andb_prop in Hs as [E13 _].
  apply sv_eqb_sound in E1. apply sv_eqb_sound in E2. apply sv_eqb_sound in E3.
  apply sv_eqb_sound in E4. apply sv_eqb_sound in E5. apply sv_eqb_sound in E6. apply sv_eqb_sound in E7.
  apply sv_eqb_sound in E8. apply sv_eqb_sound in E9. apply sv_eqb_sound in E10. apply sv_eqb_sound in E11.
  apply sv_eqb_sound in E13.
  split; [|split; [exact H3 | cbn [rho_sub rw]; rewrite E7; cbn [eval]; exact H25]].
  destruct HJ; constructor; cbn [rho_sub rw rl rm]; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E8, ?E9, ?E10, ?E11, ?E13; cbn [eval]; auto.
Qed.

Lemma G_v1 : ltac2:(tb__ "0|1|
S7S50R1A1S0S3eS39Q40M0S18R2P1A2A2S39G0Vsp;A2A3F_;Frho;").
Proof using . intros rho [[H _ _ _ _ _ _ _ _] _]. rewrite H. reflexivity. Qed.
Lemma G_v25 : ltac2:(tb__ "0|0|
S7S50R1A1S0S3eS39Q40S18R2P19A2A2S7dVLEN;VSTR;A2A3F_;Frho;").
Proof using . intros rho (_ & _ & H). exact H. Qed.
Lemma G_v4 : ltac2:(tb__ "0|1|
S7S50R1A1S0S3eS39Q40M0S18R2P4A2A2S78S39G0Vsp;A2VSTR;A2A3F_;Frho;").
Proof using Hargc Hent Hinp. intros rho [HJ _]. pose proof NU. rewrite (ji_argv0 _ _ _ _ _ _ _ _ HJ). apply Z_to_bv_small. rewrite mod64. unfold STR, argv, envp in *. lia. Qed.
Lemma G_v5 : ltac2:(tb__ "0|0|
S7S50R1A1S0S3eS39Q40S18R2P5A2A2VN0;A3F_;Frho;").
Proof using Hargc Hent Hinp. intros rho [HJ _]. pose proof NU. rewrite (ji_len0 _ _ _ _ _ _ _ _ HJ). apply Z_to_bv_small. rewrite mod64. unfold N0, argv0, argv in *. lia. Qed.
Lemma G_rl3 : forall rho, Good rho -> rl rho 3 = strs_tail inp.
Proof using . intros rho (_ & H & _). exact H. Qed.

Lemma tail_firstn : firstn (length argv0) (strs_tail inp) = argv0.
Proof using Hargc Hent Hinp.
  pose proof NU as X. unfold strs_tail. unfold N0, argv0, argv in *.
  destruct (in_argv inp) as [|a r] eqn:Ea; [cbn in X; lia|]. cbn [nth].
  rewrite flatten_strings_cons, <- !app_assoc. rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.
Lemma tail_nul : nth (length argv0) (strs_tail inp) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof using Hargc Hent Hinp.
  unfold argv0, argv.
  rewrite (tail_nth_str0 pcP phP sp brk mb draw inp Hsp Hinp Hlaunch (length (nth 0 (in_argv inp) []))) by lia.
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma argv0_nonul : ltac2:(tb__ "0|3|
S30S3dR1S2eS38Q8M0A1M1Vargv0;A2A2S4S0G1Sa9G1R2Vargv0;S3aG0Z0A2M2A4G2A3A1F_;Fj;").
Proof using Hargc Hinp envp. clear STR LEN.
  intros j Hj E. pose proof (proj1 Hinp) as (_ & _ & _ & Hnn & _). unfold argv0, argv in *.
  destruct (in_argv inp) as [|a r]; [cbn in Hj; lia|]. cbn [nth] in *.
  apply Forall_cons_iff in Hnn as [Ha _]. apply Ha. rewrite <- E. apply nth_In. exact Hj.
Qed.
Lemma tail_len : Z.of_nat (length (strs_tail inp)) = LEN - STR.
Proof using Hent Hinp. exact (length_tail pcP phP sp brk mb draw inp Hsp Hinp Hlaunch). Qed.

(* The main entry at the run's CONFIG_RSEQ [rq]: its argv[0] and random-bytes objects become the strings
   object (Lib/InitStrs.v [recarve_strs]); the auxv object stays. *)
Lemma use_intro : forall rho w, JI rho -> SP segs (Kx (TR 0) md0) (S_main rq) rho w ->
  exists rho', Good rho' /\ SP segs (Kx (TR 0) md0) (S_use rq) rho' w.
Proof using Hargc Hent Hinp.
  intros rho [tr [ms md]] HJ [Hsm Hk].
  pose proof NU as NU'.
  destruct (S_main_rngs rq) as (R0 & R1 & R2 & R3 & R6).
  destruct (recarve_strs segs pcP phP dataP_lo dataP_hi dataP_ok ltac:(unfold dataP_hi; lia)
              ltac:(change segs with segsP; rewrite segs_topP; lia) sp brk mb draw inp Hsp Hinp Hlaunch
              rho (S_main rq) tr ms md (obj_main rq 0) (obj_main rq 1) (obj_main rq 2) (obj_main rq 3) (obj_main rq 6) 25 3
              Hsm HJ (S_main_objs rq) R0 R1 R2 R3 R6 (S_main_rl3 rq)
              ltac:(discriminate) ltac:(discriminate) (S_main_next rq) ltac:(cbv; discriminate) (swf_S_main_rc rq))
    as (Hsm' & HJ' & Hrl3 & Hrw25 & _).
  set (rho' := rho_set_rw _ _ _) in *.
  assert (V25 : bv_unsigned (rw rho' 25) = LEN - STR) by (rewrite Hrw25; apply Z_to_bv_small; rewrite mod64; lia).
  assert (G' : Good rho') by (split; [exact HJ'|split; [exact Hrl3|exact V25]]).
  exists rho'. split; [exact G'|].
  split; [|exact Hk]. rewrite <- (S_use_eq rq). apply smatch_add_facts; [exact Hsm' | | reflexivity].
  pose proof (G_v5 rho' G') as V5.
  assert (V2 : bv_unsigned (rw rho' 2) = Z.of_nat (length argv)).
  { rewrite (ji_argc _ _ _ _ _ _ _ _ HJ'). apply Z_to_bv_small. rewrite mod64. unfold argv in *. lia. }
  assert (V10 : bv_unsigned (eval rho' (SAlu ALU_ADD (SVar 5) (SLit 10))) = N0 + 10) by (apply (U_addc rho' (SVar 5) 10 N0); [exact V5 | lia | lia]).
  pose proof (U_lit64 rho' 2 ltac:(lia)) as L2.
  pose proof (U_lit64 rho' 4194304 ltac:(lia)) as L4M.
  pose proof (G_v4 rho' G') as V4. pose proof (U_lit64 rho' 140737488355318 ltac:(lia)) as L47.
  unfold F_use. repeat constructor; cbn [holds]; unfold bv_ltu, bv_eqb, branch_taken, bv_eqb;
    change (eval rho' (SVar 5)) with (rw rho' 5); change (eval rho' (SVar 25)) with (rw rho' 25); change (eval rho' (SVar 2)) with (rw rho' 2);
    change (eval rho' (SVar 4)) with (rw rho' 4);
    rewrite ?V10, ?L2, ?L4M, ?V5, ?V25, ?V2, ?V4, ?L47.
  - destruct (Z.eqb_spec (Z.of_nat (length argv)) 2); [exfalso; unfold argv in *; lia | discriminate].
  - lia.
  - lia.
  -   lia.
Qed.

Lemma hd_fact : ltac2:(tb__ "0|1|
S7SfSeS2dSeA1M0S82S2dS40A1S41OF_;F_;S0G0S14R5A1S32SeR4R3A3A3S4bS2aR2R6R7R3A5S19R8R6A2F_;F_;FK;Fw;FF;Ff;FS;Frho;").
Proof using . intros rho S f F w K E Hsp. eapply SP_fact; [exact Hsp|]. rewrite E. left. reflexivity. Qed.

(* LPS 727298f3: a leaf of the usage path is per CONFIG_RSEQ ([X r] is [if r then X_1 else X_0]), so its
   facts do not reduce while [r] is abstract; its first fact is read off both values of the flag. *)
Lemma hd_fact_r : forall (rho : valuation) (S : bool -> sstate) (r : bool) (w : world)
  (K : list event -> Model -> Prop), SP segs K (S r) rho w ->
  forall (f : sprop) (F0 F1 : list sprop), ss_facts (S false) = f :: F0 -> ss_facts (S true) = f :: F1 -> holds rho f.
Proof using . intros rho S [|] w K Hsp f F0 F1 E0 E1; [exact (hd_fact rho _ f F1 w K E1 Hsp) | exact (hd_fact rho _ f F0 w K E0 Hsp)]. Qed.

Lemma Forall_hd_r : forall (P : sprop -> Prop) (S : bool -> sstate) (r : bool), Forall P (ss_facts (S r)) ->
  forall (f : sprop) (F0 F1 : list sprop), ss_facts (S false) = f :: F0 -> ss_facts (S true) = f :: F1 -> P f.
Proof using . intros P S [|] HF f F0 F1 E0 E1; [rewrite E1 in HF | rewrite E0 in HF]; apply Forall_cons_iff in HF as [Hf _]; exact Hf. Qed.

Lemma SP_add1 : ltac2:(tb__ "0|0|
S2dS40A1S41OF_;F_;SfS7S82SeS4bS2aR5R4R3R2A5S19R4R2A2S0S2cS28S12R6A1R3A2S2bA3S4bS2aR8SdcS32SeR4S35SeA1A3R7A2R6R5A5F_;F_;F_;Ff;Fw;Frho;FS;FK;").
Proof using .
  intros K S rho w f [Hsm Hk] Hf Hb. split; [|exact Hk]. apply smatch_add_facts; [exact Hsm | constructor; [exact Hf|constructor] | cbn; rewrite Hb; reflexivity].
Qed.

Definition Q_at (S : sstate) (n : nat) : assn := ltac2:(tb__ "0|0|
S82S2S7S7S1S50R1A1S4bS2aS4eS4fVn;A1Vmd0;A2VS;R1R2A5A2Lrho;A2Lw;").

Lemma FirstNul_call : forall r rho ms, Good rho -> FirstNul (rho_sub (rho_absorb rho (R_sn r) ms) (s_sn r)).
Proof using Hargc Hent Hinp.
  intros r rho ms HG. unfold FirstNul. rewrite rl_call, rw_call, (s_sn_16 r). cbn [eval].
  rewrite (G_rl3 rho HG), (G_v5 rho HG). unfold nthb. unfold N0. rewrite Nat2Z.id. split.
  - rewrite tail_nul. reflexivity.
  - intros i Hi. rewrite <- (firstn_skipn (length argv0) (strs_tail inp)), tail_firstn.
    rewrite app_nth1 by lia. intros E. apply (argv0_nonul (Z.to_nat i) ltac:(lia)).
    apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma ovf_contra : forall r rho w, Good rho -> SP segs (Kx (TR 0) md0) (X_ovf r) rho w -> False.
Proof using Hargc Hent Hinp.
  intros r rho w HG Hsp.
  assert (Hf : holds rho (BNZ (SVar 5))).
  { eapply SP_fact; [exact Hsp|]. destruct r; cbn; tauto. }
  apply holds_BNZ in Hf. apply Hf. rewrite (G_rl3 rho HG). change (eval rho (SVar 5)) with (rw rho 5).
  rewrite (G_v5 rho HG). unfold nthb, N0. rewrite Nat2Z.id, tail_nul. reflexivity.
Qed.

Lemma L_sn1 : forall r rho, Good rho -> triple segs ok (SP segs (Kx (TR 0) md0) (T_sn74 r) rho) (Q_at (E_A1 r) 0).
Proof using Hargc Hent Hinp HokK.
  intros r rho2 HG2.
  eapply run_tr; [exact (run2 r) | destruct r; reflexivity | apply okf |].
  intros L rho3 [<-|[<-|[]]] Hag3; cbn [lf_state].
  +
    pose proof (Good_agree _ _ _ Hag3 ltac:(destruct r; cbn; lia) HG2) as HG3.
    intros n Hg w Hw. exfalso. exact (ovf_contra r rho3 w HG3 Hw).
  + eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. exists rho3. split; [exact (Good_agree _ _ _ Hag3 ltac:(destruct r; cbn; lia) HG2) | exact Hw].
Qed.

Lemma L_post : (74 <= length argv0)%nat -> forall r rho, Good rho -> Forall (holds rho) (ss_facts (E_sn r)) ->
  triple segs ok (SP segs (Kx (TR 0) md0) (T_imp r) rho) (Q_at (E_A1 r) 0).
Proof using Hargc Hent Hinp HokK.
  intros Hlen74 r rho2 HG2 HF2.
  apply (post_path segs ok (Kx (TR 0) md0) (T_imp r) (T_sn r) (ss_facts (E_sn r)) xs_post rho2 _ (fb_sn2 r) (xs_post_ok r) HF2).

  apply triple_facts. intros HFT.
  eapply triple_conseq with (P := SP segs (Kx (TR 0) md0) (T_sn74 r) rho2); [| intros w Hw; exact Hw | apply (L_sn1 r); exact HG2].
  intros w Hsp. apply SP_add1; [| | destruct r; reflexivity].
  - eapply (SP_restate segs _ rho2 (T_sn r) (T_sn1 r) w); [exact (swf_T_sn1 r) | exact (diff_sn r) | | constructor | exact Hsp].
    constructor; [|constructor]. cbn [fst snd]. exact (proj1 (Forall_forall _ _) HFT _ (fact_T_sn r)).
  - cbn [holds]. rewrite U_lit64 by lia. change (eval rho2 (SVar 5)) with (rw rho2 5). rewrite (G_v5 rho2 HG2). unfold N0. lia.
Qed.

Lemma L_call : (74 <= length argv0)%nat -> forall r rho, Good rho ->
  triple segs ok (SP segs (Kx (TR 0) md0) (S_use r) rho) (Q_at (E_A1 r) 0).
Proof using Hargc Hent Hinp HokK.
  intros Hlen74 r rho HG.
  eapply run_tr; [exact (run_use r) | destruct r; reflexivity | apply okf |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  pose proof (Good_agree _ _ _ Hag1 ltac:(destruct r; cbn; lia) HG) as HG1.
  apply (call_path segs FirstNul ok (Kx (TR 0) md0) (Kx (TR 0) md0) (E_sn r) (E_snX r) Pre_strnlen xs_pre (s_sn r) (R_sn r) Posts_strnlen _ rho1
           (xs_pre_ok r) (efr_sn r) (chk_sn r) (fb_sn r)).
  - intros rho2 HF. apply strnlen_sum; [apply okf | exact HF].
  - intros ms _. apply (FirstNul_call r). exact HG1.
  - intros L rho2 [<-|[]] Hag2 HF2. cbn [lf_state]. replace (ss_next Pre_strnlen) with NF by reflexivity. rewrite (T_imp_eq r).
    apply (L_post Hlen74 r); [|exact HF2]. exact (Good_agree _ _ _ Hag2 ltac:(destruct r; cbn; lia) HG1).
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
Proof using Hargc Hfd2 Hrdr0 HokK HokP.
  intros S e n bs1 bs2 rho HG Hn Hi H17 H10 H12 He Hbs Hlen Hrd.
  set (J' := fun (r : valuation) (tr : list event) (md : Model) =>
               exists k, rw r (ss_next S) = Z_to_bv 64 (Z.of_nat k) /\ (1 <= k <= length (bs1 ++ bs2))%nat
                         /\ tr = TR (n + k) /\ md = md0).
  apply triple1_triple.
  eapply triple1_conseq; [intros w Hw; exact Hw | |
    eapply (SysNA.triple1_writev2J_na segs ok (liftK (Kx (TR n) md0)) J' S rho 2 bs1 bs2 e);
      [apply ok_frame_liftK; apply okf | eapply NoAlloc.ok_pframeJ_na_of_tcons; [apply HokP; intros tr0 md0_ H0; exact H0 | intros r tr md Hk; exact (Ktc n tr md Hk)]
      | exact Hi | exact H17 | exact H10 | exact H12 | lia | exact Hlen | exact He | | | ]].
  - intros w (rho' & Hag & Hsm & (k & Hk & Hkb & Htr & Hmd)). exists rho', k.
    split; [exact (Good_agree _ _ _ Hag Hn HG)|]. split; [exact Hag|]. split; [exact Hk|]. split; [exact Hkb|].
    split; [exact Hsm|]. split; [exact Htr | exact Hmd].
  - intros rho' tr md k Hag Hk [-> ->] Hkb. split; [exact Hfd2|]. exists k. split; [exact Hk|]. split; [exact Hkb|].
    split; [|reflexivity]. rewrite Hbs, firstn_firstn, Nat.min_l by lia. apply TR_app.
  - intros tr ms md Hsp _. exact (Hrd tr ms md Hsp).
  - intros tr ms md _ [_ ->]. exact Hrdr0.
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
Proof using Hargc Hfd2 Hrdr0 HokK HokP.
  intros S e n bs1 rho HG Hn Hi H17 H10 H12 He Hbs Hlen Hrd.
  set (J' := fun (r : valuation) (tr : list event) (md : Model) =>
               exists k, rw r (ss_next S) = Z_to_bv 64 (Z.of_nat k) /\ (1 <= k <= length bs1)%nat
                         /\ tr = TR (n + k) /\ md = md0).
  apply triple1_triple.
  eapply triple1_conseq; [intros w Hw; exact Hw | |
    eapply (SysNA.triple1_writev1J_na segs ok (liftK (Kx (TR n) md0)) J' S rho 2 bs1 e);
      [apply ok_frame_liftK; apply okf | eapply NoAlloc.ok_pframeJ_na_of_tcons; [apply HokP; intros tr0 md0_ H0; exact H0 | intros r tr md Hk; exact (Ktc n tr md Hk)]
      | exact Hi | exact H17 | exact H10 | exact H12 | lia | exact Hlen | exact He | | | ]].
  - intros w (rho' & Hag & Hsm & (k & Hk & Hkb & Htr & Hmd)). exists rho', k.
    split; [exact (Good_agree _ _ _ Hag Hn HG)|]. split; [exact Hag|]. split; [exact Hk|]. split; [exact Hkb|].
    split; [exact Hsm|]. split; [exact Htr | exact Hmd].
  - intros rho' tr md k Hag Hk [-> ->] Hkb. split; [exact Hfd2|]. exists k. split; [exact Hk|]. split; [exact Hkb|].
    split; [|reflexivity]. rewrite Hbs, firstn_firstn, Nat.min_l by lia. apply TR_app.
  - intros tr ms md Hsp _. exact (Hrd tr ms md Hsp).
  - intros tr ms md _ [_ ->]. exact Hrdr0.
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

Lemma strs_read : forall rho S tr ms md (off : Z) (n : nat) (a len : word),
  Good rho -> smatch_pending segs rho S (tr, mkCfg ms md) -> (2 <= length (ss_objs S))%nat ->
  ob1 S = O_strs 25 3 -> 0 <= off -> off + Z.of_nat n <= N0 + 1 ->
  bv_unsigned a = bv_unsigned sp + STR + off -> bv_unsigned len = Z.of_nat n ->
  read_bytes_map (ms_read_byte ms) a len = Some (firstn n (skipn (Z.to_nat off) (strs_tail inp))).
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

Lemma strs_window : forall d n, (d + n <= length argv0)%nat ->
  firstn n (skipn d (strs_tail inp)) = firstn n (skipn d argv0).
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

Lemma cert_E_A1 : forall r : bool, (@and (@eq (@bool) (@obj_wf (@ss_next (E_A1 r)) (@ob0 (E_A1 r))) (@true)) (@and (@eq (@prod (@prod (@sv) (@sv)) (@sv)) (@obj_rng (@ob0 (E_A1 r))) (@pair (@prod (@sv) (@sv)) (@sv) (@pair (@sv) (@sv) (@SVar 1%positive) (@SLit (@Z.opp (@STK_FREE)))) (@SLit 0%Z))) (@and (@eq (@sobj) (@ob1 (E_A1 r)) (@O_strs 25%positive 3%positive)) (@and (@Peano.le 2%nat (@length (@sobj) (@ss_objs (E_A1 r)))) (@and (@eq (@option (@list (@bexp))) (@cells_bytes (@ob_cells (@ob0 (E_A1 r))) (@SLit (-560)%Z) 0%Z 7%nat) (@Some (@list (@bexp)) (@BL_usage))) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-1224)%Z) 8%Z (@SAlu (@ALU_ADD) (@SVar 1%positive) (@SLit (-560)%Z)))) (@ob_cells (@ob0 (E_A1 r)))) (@true)) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-1216)%Z) 8%Z (@SLit 7%Z))) (@ob_cells (@ob0 (E_A1 r)))) (@true)) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-1208)%Z) 8%Z (@SVar 4%positive))) (@ob_cells (@ob0 (E_A1 r)))) (@true)) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-1200)%Z) 8%Z (@SVar 5%positive))) (@ob_cells (@ob0 (E_A1 r)))) (@true)) (@and (@eq (@sv) (@reg_sv (E_A1 r) 11%Z) (@SAlu (@ALU_ADD) (@SVar 1%positive) (@SLit (-1224)%Z))) (@and (@eq (@sv) (@reg_sv (E_A1 r) 22%Z) (@SAlu (@ALU_ADD) (@SVar 5%positive) (@SLit 7%Z))) (@and (@eq (@option (@instr)) (@instr_at (@segs) (@ss_pc (E_A1 r))) (@Some (@instr) (@Ecall))) (@and (@eq (@sv) (@reg_sv (E_A1 r) 17%Z) (@SLit 66%Z)) (@and (@eq (@sv) (@reg_sv (E_A1 r) 10%Z) (@SLit 2%Z)) (@and (@eq (@sv) (@reg_sv (E_A1 r) 12%Z) (@SLit 2%Z)) (@eq (@positive) (@ss_next (E_A1 r)) 67%positive)))))))))))))))).
Proof using Hargc LEN N0 STR. intros [|]; vm_compute; repeat split; (reflexivity || lia). Qed.

Lemma bytes_E_A1 : forall r rho tr ms md, Good rho -> smatch_pending segs rho (E_A1 r) (tr, mkCfg ms md) ->
  exists b1 l1 b2 l2,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv (E_A1 r) 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (E_A1 r) 11) + 8)%bv = Some l1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (E_A1 r) 11) + 16)%bv = Some b2
    /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv (E_A1 r) 11) + 16) + 8)%bv = Some l2
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some (str "usage: ")
    /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some argv0
    /\ bv_unsigned (eval rho (reg_sv (E_A1 r) 22)) = Z.of_nat (length (str "usage: " ++ argv0))
    /\ (bv_unsigned (eval rho (reg_sv (E_A1 r) 11)) + 32 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
    /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros r rho tr ms md HG Hsp. pose proof NU as NU'.
  destruct (cert_E_A1 r) as (Hwf & Hrng & Hob1 & Hlen & Hcb & C1 & C2 & C3 & C4 & R11 & R22 & _).
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
  split; [eapply (iov_field rho (E_A1 r) tr ms md (-1224)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field rho (E_A1 r) tr ms md (-1216)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | lia]|].
  split; [eapply (iov_field rho (E_A1 r) tr ms md (-1208)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C3 | lia | lia]|].
  split; [eapply (iov_field rho (E_A1 r) tr ms md (-1200)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C4 | lia | lia]|].
  split.
  { rewrite <- (BL_usage_eval rho). apply (read_bytes_map_of_rd ms _ _ 7); [change (Z.of_nat 7) with 7; apply U_lit64; lia|].
    replace (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-560)))) with (Z_to_bv 64 (bv_unsigned sp - 560)).
    - eapply ibuf_read; eauto.
    - apply bv_eq. rewrite Z_to_bv_small by (rewrite mod64; lia). symmetry. apply (U_addc rho (SVar 1) (-560) (bv_unsigned sp)); [exact V1 | lia | lia]. }
  split.
  { replace argv0 with (firstn (length argv0) (skipn (Z.to_nat 0) (strs_tail inp)))
      by (cbn [Z.to_nat skipn]; apply tail_firstn).
    apply (strs_read rho (E_A1 r) tr ms md 0 (length argv0)); [exact HG | exact Hsp | exact Hlen | exact Hob1 | lia | unfold N0; lia | | exact V5].
    change (eval rho (SVar 4)) with (rw rho 4). rewrite V4. lia. }
  erewrite U_addc; [| exact V5 | unfold N0; lia | lia]. rewrite length_app. unfold N0. cbn [length str]. lia.
Qed.

Lemma SPp_fact : ltac2:(tb__ "0|1|
S7SfS2dS40A1M0Sc4S41SeScfS2aR6R5S34G0ScbR4SccR3R2A2A4A4S6bSeR2S14R6A1A3S19R8R3A2F_;F_;Fp;Fmd;Fms;Ftr;FS;Frho;").
Proof using . intros rho S tr ms md p Hsp Hin. exact (proj1 (Forall_forall _ _) (smatch_pending_facts segs _ _ _ _ _ Hsp) p Hin). Qed.

Lemma cert_CB2 : forall r : bool, (@and (@eq (@bool) (@obj_wf (@ss_next (CB2 r)) (@ob0 (CB2 r))) (@true)) (@and (@eq (@prod (@prod (@sv) (@sv)) (@sv)) (@obj_rng (@ob0 (CB2 r))) (@pair (@prod (@sv) (@sv)) (@sv) (@pair (@sv) (@sv) (@SVar 1%positive) (@SLit (@Z.opp (@STK_FREE)))) (@SLit 0%Z))) (@and (@eq (@sobj) (@ob1 (CB2 r)) (@O_strs 25%positive 3%positive)) (@and (@Peano.le 2%nat (@length (@sobj) (@ss_objs (CB2 r)))) (@and (@eq (@option (@list (@bexp))) (@cells_bytes (@ob_cells (@ob0 (CB2 r))) (@SLit (-560)%Z) 0%Z 7%nat) (@Some (@list (@bexp)) (@BL_usage))) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-1224)%Z) 8%Z (@SAlu (@ALU_SUB) (@SAlu (@ALU_ADD) (@SVar 1%positive) (@SLit (-553)%Z)) (@SVar 67%positive)))) (@ob_cells (@ob0 (CB2 r)))) (@true)) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-1216)%Z) 8%Z (@SVar 67%positive))) (@ob_cells (@ob0 (CB2 r)))) (@true)) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-1208)%Z) 8%Z (@SVar 4%positive))) (@ob_cells (@ob0 (CB2 r)))) (@true)) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-1200)%Z) 8%Z (@SVar 5%positive))) (@ob_cells (@ob0 (CB2 r)))) (@true)) (@and (@eq (@sv) (@reg_sv (CB2 r) 11%Z) (@SAlu (@ALU_ADD) (@SVar 1%positive) (@SLit (-1224)%Z))) (@and (@eq (@sv) (@reg_sv (CB2 r) 22%Z) (@SAlu (@ALU_ADD) (@SVar 5%positive) (@SVar 67%positive))) (@and (@eq (@option (@instr)) (@instr_at (@segs) (@ss_pc (CB2 r))) (@Some (@instr) (@Ecall))) (@and (@eq (@sv) (@reg_sv (CB2 r) 17%Z) (@SLit 66%Z)) (@and (@eq (@sv) (@reg_sv (CB2 r) 10%Z) (@SLit 2%Z)) (@and (@eq (@sv) (@reg_sv (CB2 r) 12%Z) (@SLit 2%Z)) (@and (@eq (@positive) (@ss_next (CB2 r)) 71%positive) (@In (@sprop) (@SPUle (@SVar 67%positive) (@SLit 6%Z)) (@ss_facts (CB2 r))))))))))))))))))).
Proof using Hargc LEN N0 STR. intros [|]; vm_compute; repeat split; (reflexivity || lia || (cbn; tauto)). Qed.

Lemma bytes_CB2 : forall r rho tr ms md, Good rho -> smatch_pending segs rho (CB2 r) (tr, mkCfg ms md) ->
  let L0 := Z.to_nat (bv_unsigned (rw rho 67)) in
  exists b1 l1 b2 l2,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv (CB2 r) 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (CB2 r) 11) + 8)%bv = Some l1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (CB2 r) 11) + 16)%bv = Some b2
    /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv (CB2 r) 11) + 16) + 8)%bv = Some l2
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some (skipn (7 - L0) (str "usage: "))
    /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some argv0
    /\ bv_unsigned (eval rho (reg_sv (CB2 r) 22)) = Z.of_nat (length (skipn (7 - L0) (str "usage: ") ++ argv0))
    /\ (bv_unsigned (eval rho (reg_sv (CB2 r) 11)) + 32 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
    /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros r rho tr ms md HG Hsp. pose proof NU as NU'.
  destruct (cert_CB2 r) as (Hwf & Hrng & Hob1 & Hlen & Hcb & C1 & C2 & C3 & C4 & R11 & R22 & _ & _ & _ & _ & _ & HinF).
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
  split; [eapply (iov_field rho (CB2 r) tr ms md (-1224)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field rho (CB2 r) tr ms md (-1216)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split; [eapply (iov_field rho (CB2 r) tr ms md (-1208)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C3 | lia | lia]|].
  split; [eapply (iov_field rho (CB2 r) tr ms md (-1200)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C4 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
  split.
  { rewrite <- (BL_usage_eval rho). apply (read_bytes_map_of_rd ms _ _ L0); [subst L0; change (eval rho (SVar 67)) with (rw rho 67); lia|].
    replace (eval rho (SAlu ALU_SUB (SAlu ALU_ADD (SVar 1) (SLit (-553))) (SVar 67)))
      with (Z_to_bv 64 (bv_unsigned sp - 560) + Z_to_bv 64 (Z.of_nat (7 - L0)))%bv.
    - apply rd_bytes_skip. replace (7 - L0 + L0)%nat with 7%nat by lia. eapply ibuf_read; eauto.
    - apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite mod64, <- Z.add_mod, Z.mod_small by lia.
      symmetry. erewrite (U_sub2 rho _ _ (bv_unsigned sp - 553) (bv_unsigned (rw rho 67))); [lia | | reflexivity | lia].
      apply (U_addc rho (SVar 1) (-553) (bv_unsigned sp)); [exact V1 | lia | lia]. }
  split.
  { replace argv0 with (firstn (length argv0) (skipn (Z.to_nat 0) (strs_tail inp)))
      by (cbn [Z.to_nat skipn]; apply tail_firstn).
    apply (strs_read rho (CB2 r) tr ms md 0 (length argv0)); [exact HG | exact Hsp | exact Hlen | exact Hob1 | lia | unfold N0; lia | | exact V5].
    change (eval rho (SVar 4)) with (rw rho 4). rewrite V4. lia. }
  erewrite (U_add2 rho _ _ N0 (bv_unsigned (rw rho 67))); [| exact V5 | reflexivity | unfold N0; lia].
  rewrite length_app, length_skipn. unfold N0. cbn [length str]. lia.
Qed.

Lemma cert_CB1 : forall r : bool, (@and (@eq (@prod (@prod (@sv) (@sv)) (@sv)) (@obj_rng (@ob0 (CB1 r))) (@pair (@prod (@sv) (@sv)) (@sv) (@pair (@sv) (@sv) (@SVar 1%positive) (@SLit (@Z.opp (@STK_FREE)))) (@SLit 0%Z))) (@and (@eq (@sobj) (@ob1 (CB1 r)) (@O_strs 25%positive 3%positive)) (@and (@Peano.le 2%nat (@length (@sobj) (@ss_objs (CB1 r)))) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-1208)%Z) 8%Z (@SAlu (@ALU_SUB) (@SAlu (@ALU_ADD) (@SVar 4%positive) (@SVar 5%positive)) (@SVar 68%positive)))) (@ob_cells (@ob0 (CB1 r)))) (@true)) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-1200)%Z) 8%Z (@SVar 68%positive))) (@ob_cells (@ob0 (CB1 r)))) (@true)) (@and (@eq (@sv) (@reg_sv (CB1 r) 11%Z) (@SAlu (@ALU_ADD) (@SVar 1%positive) (@SLit (-1208)%Z))) (@and (@eq (@sv) (@reg_sv (CB1 r) 22%Z) (@SVar 68%positive)) (@and (@eq (@option (@instr)) (@instr_at (@segs) (@ss_pc (CB1 r))) (@Some (@instr) (@Ecall))) (@and (@eq (@sv) (@reg_sv (CB1 r) 17%Z) (@SLit 66%Z)) (@and (@eq (@sv) (@reg_sv (CB1 r) 10%Z) (@SLit 2%Z)) (@and (@eq (@sv) (@reg_sv (CB1 r) 12%Z) (@SLit 1%Z)) (@and (@eq (@positive) (@ss_next (CB1 r)) 72%positive) (@and (@In (@sprop) (@SPUle (@SLit 1%Z) (@SVar 68%positive)) (@ss_facts (CB1 r))) (@In (@sprop) (@SPBranch (@BC_LTU) (@SVar 68%positive) (@SVar 5%positive)) (@ss_facts (CB1 r)))))))))))))))).
Proof using Hargc LEN N0 STR. intros [|]; vm_compute; repeat split; (reflexivity || lia || (cbn; tauto)). Qed.

Lemma bytes_CB1 : forall r rho tr ms md, Good rho -> smatch_pending segs rho (CB1 r) (tr, mkCfg ms md) ->
  let R := Z.to_nat (bv_unsigned (rw rho 68)) in
  (1 <= R < length argv0)%nat /\
  exists b1 l1,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv (CB1 r) 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (CB1 r) 11) + 8)%bv = Some l1
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some (skipn (length argv0 - R) argv0)
    /\ bv_unsigned (eval rho (reg_sv (CB1 r) 22)) = Z.of_nat (length (skipn (length argv0 - R) argv0))
    /\ (bv_unsigned (eval rho (reg_sv (CB1 r) 11)) + 16 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros r rho tr ms md HG Hsp. pose proof NU as NU'.
  destruct (cert_CB1 r) as (Hrng & Hob1 & Hlen & C1 & C2 & R11 & R22 & _ & _ & _ & _ & _ & HinF1 & HinF2).
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
  split; [eapply (iov_field rho (CB1 r) tr ms md (-1208)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field rho (CB1 r) tr ms md (-1200)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split.
  { replace (skipn (length argv0 - R) argv0) with (firstn R (skipn (Z.to_nat (N0 - Z.of_nat R)) (strs_tail inp))).
    2:{ rewrite strs_window by (unfold N0; lia). rewrite firstn_all2 by (rewrite length_skipn; unfold N0; lia). f_equal. unfold N0. lia. }
    apply (strs_read rho (CB1 r) tr ms md (N0 - Z.of_nat R) R); [exact HG | exact Hsp | exact Hlen | exact Hob1 | lia | lia | | subst R; change (eval rho (SVar 68)) with (rw rho 68); lia].
    erewrite (U_sub2 rho _ _ (bv_unsigned sp + STR + N0) (bv_unsigned (rw rho 68))); [subst R; lia | | reflexivity | lia].
    apply (U_add2 rho (SVar 4) (SVar 5)); [exact V4 | exact V5 | lia]. }
  change (eval rho (SVar 68)) with (rw rho 68). rewrite length_skipn. subst R. lia.
Qed.

Lemma cert_E_A2 : forall r : bool, (@and (@eq (@bool) (@obj_wf (@ss_next (E_A2 r)) (@ob0 (E_A2 r))) (@true)) (@and (@eq (@prod (@prod (@sv) (@sv)) (@sv)) (@obj_rng (@ob0 (E_A2 r))) (@pair (@prod (@sv) (@sv)) (@sv) (@pair (@sv) (@sv) (@SVar 1%positive) (@SLit (@Z.opp (@STK_FREE)))) (@SLit 0%Z))) (@and (@Peano.le 2%nat (@length (@sobj) (@ss_objs (E_A2 r)))) (@and (@eq (@option (@list (@bexp))) (@cells_bytes (@ob_cells (@ob0 (E_A2 r))) (@SLit (-560)%Z) 0%Z 7%nat) (@Some (@list (@bexp)) (@BL_input))) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-680)%Z) 8%Z (@SAlu (@ALU_ADD) (@SVar 1%positive) (@SLit (-560)%Z)))) (@ob_cells (@ob0 (E_A2 r)))) (@true)) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-672)%Z) 8%Z (@SLit 7%Z))) (@ob_cells (@ob0 (E_A2 r)))) (@true)) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-664)%Z) 8%Z (@SLit 0%Z))) (@ob_cells (@ob0 (E_A2 r)))) (@true)) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-656)%Z) 8%Z (@SLit 0%Z))) (@ob_cells (@ob0 (E_A2 r)))) (@true)) (@and (@eq (@sv) (@reg_sv (E_A2 r) 11%Z) (@SAlu (@ALU_ADD) (@SVar 1%positive) (@SLit (-680)%Z))) (@and (@eq (@sv) (@reg_sv (E_A2 r) 22%Z) (@SLit 7%Z)) (@and (@eq (@option (@instr)) (@instr_at (@segs) (@ss_pc (E_A2 r))) (@Some (@instr) (@Ecall))) (@and (@eq (@sv) (@reg_sv (E_A2 r) 17%Z) (@SLit 66%Z)) (@and (@eq (@sv) (@reg_sv (E_A2 r) 10%Z) (@SLit 2%Z)) (@and (@eq (@sv) (@reg_sv (E_A2 r) 12%Z) (@SLit 2%Z)) (@eq (@positive) (@ss_next (E_A2 r)) 90%positive))))))))))))))).
Proof using Hargc LEN N0 STR. intros [|]; vm_compute; repeat split; (reflexivity || lia). Qed.

Lemma bytes_E_A2 : forall r rho tr ms md, Good rho -> smatch_pending segs rho (E_A2 r) (tr, mkCfg ms md) ->
  exists b1 l1 b2 l2,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv (E_A2 r) 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (E_A2 r) 11) + 8)%bv = Some l1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (E_A2 r) 11) + 16)%bv = Some b2
    /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv (E_A2 r) 11) + 16) + 8)%bv = Some l2
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some M2
    /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some []
    /\ bv_unsigned (eval rho (reg_sv (E_A2 r) 22)) = Z.of_nat (length (M2 ++ []))
    /\ (bv_unsigned (eval rho (reg_sv (E_A2 r) 11)) + 32 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
    /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros r rho tr ms md HG Hsp. pose proof NU as NU'.
  destruct (cert_E_A2 r) as (Hwf & Hrng & Hlen & Hcb & C1 & C2 & C3 & C4 & R11 & R22 & _).
  rewrite R11, R22. pose proof (G_v1 rho HG) as V1.
  assert (A0 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-680)))) = bv_unsigned sp - 680).
  { erewrite U_addc; [reflexivity | exact V1 | lia | lia]. }
  assert (A16 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-680))) + 16)%bv = bv_unsigned sp - 664).
  { rewrite (U_bvadd _ _ _ _ A0 u16) by lia. lia. }
  exists (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-560)))), (eval rho (SLit 7)), (eval rho (SLit 0)), (eval rho (SLit 0)).
  apply and7_tail; [tsz|].
  split; [eapply (iov_field rho (E_A2 r) tr ms md (-680)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field rho (E_A2 r) tr ms md (-672)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split; [eapply (iov_field rho (E_A2 r) tr ms md (-664)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C3 | lia | lia]|].
  split; [eapply (iov_field rho (E_A2 r) tr ms md (-656)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C4 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
  split.
  { rewrite <- (BL_input_eval rho). apply (read_bytes_map_of_rd ms _ _ 7); [change (Z.of_nat 7) with 7; apply U_lit64; lia|].
    replace (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-560)))) with (Z_to_bv 64 (bv_unsigned sp - 560)).
    - eapply ibuf_read; eauto.
    - apply bv_eq. rewrite Z_to_bv_small by (rewrite mod64; lia). symmetry. apply (U_addc rho (SVar 1) (-560) (bv_unsigned sp)); [exact V1 | lia | lia]. }
  split; [reflexivity|].
  rewrite U_lit64 by lia. reflexivity.
Qed.

Lemma cert_CB3 : forall r : bool, (@and (@eq (@bool) (@obj_wf (@ss_next (CB3 r)) (@ob0 (CB3 r))) (@true)) (@and (@eq (@prod (@prod (@sv) (@sv)) (@sv)) (@obj_rng (@ob0 (CB3 r))) (@pair (@prod (@sv) (@sv)) (@sv) (@pair (@sv) (@sv) (@SVar 1%positive) (@SLit (@Z.opp (@STK_FREE)))) (@SLit 0%Z))) (@and (@Peano.le 2%nat (@length (@sobj) (@ss_objs (CB3 r)))) (@and (@eq (@option (@list (@bexp))) (@cells_bytes (@ob_cells (@ob0 (CB3 r))) (@SLit (-560)%Z) 0%Z 7%nat) (@Some (@list (@bexp)) (@BL_input))) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-680)%Z) 8%Z (@SAlu (@ALU_SUB) (@SAlu (@ALU_ADD) (@SVar 1%positive) (@SLit (-553)%Z)) (@SVar 90%positive)))) (@ob_cells (@ob0 (CB3 r)))) (@true)) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-672)%Z) 8%Z (@SVar 90%positive))) (@ob_cells (@ob0 (CB3 r)))) (@true)) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-664)%Z) 8%Z (@SLit 0%Z))) (@ob_cells (@ob0 (CB3 r)))) (@true)) (@and (@eq (@bool) (@existsb (@cell) (@cell_eqb (@mkCell (@SLit (-656)%Z) 8%Z (@SLit 0%Z))) (@ob_cells (@ob0 (CB3 r)))) (@true)) (@and (@eq (@sv) (@reg_sv (CB3 r) 11%Z) (@SAlu (@ALU_ADD) (@SVar 1%positive) (@SLit (-680)%Z))) (@and (@eq (@sv) (@reg_sv (CB3 r) 22%Z) (@SVar 90%positive)) (@and (@eq (@option (@instr)) (@instr_at (@segs) (@ss_pc (CB3 r))) (@Some (@instr) (@Ecall))) (@and (@eq (@sv) (@reg_sv (CB3 r) 17%Z) (@SLit 66%Z)) (@and (@eq (@sv) (@reg_sv (CB3 r) 10%Z) (@SLit 2%Z)) (@and (@eq (@sv) (@reg_sv (CB3 r) 12%Z) (@SLit 2%Z)) (@and (@eq (@positive) (@ss_next (CB3 r)) 93%positive) (@and (@In (@sprop) (@SPUle (@SLit 1%Z) (@SVar 90%positive)) (@ss_facts (CB3 r))) (@In (@sprop) (@SPUle (@SVar 90%positive) (@SLit 6%Z)) (@ss_facts (CB3 r))))))))))))))))))).
Proof using Hargc LEN N0 STR. intros [|]; vm_compute; repeat split; (reflexivity || lia || (cbn; tauto)). Qed.

Lemma bytes_CB3 : forall r rho tr ms md, Good rho -> smatch_pending segs rho (CB3 r) (tr, mkCfg ms md) ->
  let L0 := Z.to_nat (bv_unsigned (rw rho 90)) in
  (1 <= L0 <= 6)%nat /\
  exists b1 l1 b2 l2,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv (CB3 r) 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (CB3 r) 11) + 8)%bv = Some l1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (CB3 r) 11) + 16)%bv = Some b2
    /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv (CB3 r) 11) + 16) + 8)%bv = Some l2
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some (skipn (7 - L0) M2)
    /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some []
    /\ bv_unsigned (eval rho (reg_sv (CB3 r) 22)) = Z.of_nat (length (skipn (7 - L0) M2 ++ []))
    /\ (bv_unsigned (eval rho (reg_sv (CB3 r) 11)) + 32 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
    /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros r rho tr ms md HG Hsp. pose proof NU as NU'.
  destruct (cert_CB3 r) as (Hwf & Hrng & Hlen & Hcb & C1 & C2 & C3 & C4 & R11 & R22 & _ & _ & _ & _ & _ & HinF1 & HinF2).
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
  split; [eapply (iov_field rho (CB3 r) tr ms md (-680)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field rho (CB3 r) tr ms md (-672)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split; [eapply (iov_field rho (CB3 r) tr ms md (-664)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C3 | lia | lia]|].
  split; [eapply (iov_field rho (CB3 r) tr ms md (-656)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C4 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
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
Proof using Hargc. clear STR LEN.
  intros c Hc. unfold MSG, M1. rewrite <- app_assoc.
  destruct c as [|[|[|[|[|[|[|[|c]]]]]]]]; try reflexivity. lia.
Qed.
Lemma MSG_skipA : ltac2:(tb__ "0|1|
S30S3cR1S2eS38Q8A1M0Vargv0;A2A2S0S2dG0A1Sa6G0Sa4U7R2A2S51A3S37G0Sa6G0R2Vargv0;A3S57A3A3F_;Fd;").
Proof using Hargc. clear STR LEN.
  intros d Hd. unfold MSG, M1. rewrite <- app_assoc. cbn [skipn Nat.add app str].
  rewrite skipn_app. replace (d - length argv0)%nat with 0%nat by lia. reflexivity.
Qed.

Definition L0_of (rho : valuation) : nat := Z.to_nat (bv_unsigned (rw rho 67)).
Definition R_of (rho : valuation) : nat := Z.to_nat (bv_unsigned (rw rho 68)).
Definition QD1 (r : bool) : assn := Q_at (D1 r) (length M1).

Lemma loop1 : forall r : bool, ((74%nat <= (length argv0))%nat -> (forall (m : nat), ((forall (rho : valuation), ((Good rho) -> (((L0_of rho) <= 6%nat)%nat -> (((Nat.add (L0_of rho) (length argv0)) <= m)%nat -> (triple segs ok (SP segs (Kx (TR (Nat.sub 7%nat (L0_of rho))) md0) (CB2 r) rho) (QD1 r)))))) /\ (forall (rho : valuation), ((Good rho) -> (((1%nat <= (R_of rho))%nat /\ ((R_of rho) < (length argv0))%nat) -> (((R_of rho) <= m)%nat -> (triple segs ok (SP segs (Kx (TR (Nat.sub (Nat.add 7%nat (length argv0)) (R_of rho))) md0) (CB1 r) rho) (QD1 r))))))))).
Proof using Hargc Hent Hfd2 Hrdr0 Hinp HokK HokP.
  intros r Hlen74. induction m as [|m IH].
  { split; intros rho HG H1 H2; exfalso; lia. }
  destruct IH as [IH2 IH1]. pose proof NU as NU'.
  destruct (cert_CB2 r) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R22b & Hib & H17b & H10b & H12b & Hnxb & HinFb).
  destruct (cert_CB1 r) as (_ & _ & _ & _ & _ & _ & R22c & Hic & H17c & H10c & H12c & Hnxc & HinFc1 & HinFc2).
  split.
  -
    intros rho HG HL0 Hm.
    assert (HU67 : 0 <= bv_unsigned (rw rho 67) <= 6) by (pose proof (urange (rw rho 67)); unfold L0_of in HL0; lia).
    eapply triple_seq.
    { apply (writev_site2 (CB2 r) (reg_sv (CB2 r) 22) (7 - L0_of rho) (skipn (7 - L0_of rho) (str "usage: ")) argv0 rho HG);
        [rewrite Hnxb; lia | exact Hib | exact H17b | exact H10b | exact H12b | rewrite R22b, Hnxb; reflexivity | | |].
      + rewrite MSG_skip7 by lia. rewrite app_assoc, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
      + rewrite length_app, length_skipn. cbn [length str]. unfold MAX_RW_COUNT. lia.
      + intros tr ms md Hsp. exact (bytes_CB2 r rho tr ms md HG Hsp). }
    apply triple_ex; intros rho1. apply triple_ex; intros k.
    apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
    rewrite Hnxb in Hk, Hag1. rewrite length_app, length_skipn in Hkb. cbn [length str] in Hkb.
    assert (E67 : rw rho1 67 = rw rho 67) by (symmetry; apply (proj1 Hag1); lia).
    assert (U71 : bv_unsigned (rw rho1 71) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
    pose proof (G_v5 rho1 HG1) as V5.

    eapply triple_conseq with (P := SP segs (Kx (TR (7 - L0_of rho + k)) md0) (PB2 r) rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. apply SP_add1; [exact Hw | | destruct r; reflexivity]. cbn [holds]. change (eval rho1 (SVar 71)) with (rw rho1 71). rewrite U71, U_lit64 by lia. lia. }
    destruct (Nat.le_gt_cases k (L0_of rho)) as [Hle|Hgt].
    +
      eapply triple_conseq with (P := SP segs (Kx (TR (7 - L0_of rho + k)) md0) (PB2a r) rho1); [| intros w Hw; exact Hw |].
      { intros w Hw. apply SP_add1; [exact Hw | | destruct r; reflexivity]. cbn [holds]. change (eval rho1 (SVar 71)) with (rw rho1 71).
        change (eval rho1 (SVar 67)) with (rw rho1 67). rewrite U71, E67. unfold L0_of in Hle. lia. }
      eapply run_tr; [exact (run_PB2a r) | destruct r; reflexivity | apply okf |].
      intros L rho2 [<-|[]] Hag2. cbn [lf_state].
      assert (EL : L0_of (rho_sub rho2 s_PB2a_CB2) = (L0_of rho - k)%nat).
      { unfold L0_of. cbn [rho_sub rw]. rewrite sv_PB2a_67.
        erewrite U_sub2; [| reflexivity | reflexivity |]; change (eval rho2 (SVar 67)) with (rw rho2 67); change (eval rho2 (SVar 71)) with (rw rho2 71);
          rewrite <- (proj1 Hag2 67%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 71%positive ltac:(destruct r; cbn; lia)), E67, U71; unfold L0_of in Hle; lia. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH2 (rho_sub rho2 s_PB2a_CB2))].
      * intros w Hw. eapply SP_entails in Hw; [|exact (ent_PB2a_CB2 r)].
        replace (7 - L0_of (rho_sub rho2 s_PB2a_CB2))%nat with (7 - L0_of rho + k)%nat by lia. exact Hw.
      * apply Good_sub; [destruct r; reflexivity|]. eapply Good_agree; [exact Hag2 | destruct r; cbn; lia | exact HG1].
      * lia.
      * lia.
    +
      eapply triple_conseq with (P := SP segs (Kx (TR (7 - L0_of rho + k)) md0) (PB2b r) rho1); [| intros w Hw; exact Hw |].
      { intros w Hw. apply SP_add1; [exact Hw | | destruct r; reflexivity]. cbn [holds]. change (eval rho1 (SVar 71)) with (rw rho1 71).
        erewrite U_addc; [| reflexivity | |]; change (eval rho1 (SVar 67)) with (rw rho1 67); rewrite ?U71, ?E67; unfold L0_of in Hgt; pose proof (urange (rw rho 67)); lia. }
      eapply run_tr; [exact (run_PB2b r) | destruct r; reflexivity | apply okf |].
      intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
      *
        eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
        intros w Hw. pose proof (hd_fact_r rho2 L_PB2b_0 r w _ Hw _ _ _ eq_refl eq_refl) as Hf.
        cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
        erewrite (U_add2 rho2 (SVar 5) (SVar 67)) in Hf; [| reflexivity | reflexivity |];
          change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 67)) with (rw rho2 67) in *; change (eval rho2 (SVar 71)) with (rw rho2 71) in *.
        2:{ rewrite <- (proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 67%positive ltac:(destruct r; cbn; lia)), V5, E67. lia. }
        rewrite <- (proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 67%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 71%positive ltac:(destruct r; cbn; lia)), V5, E67, U71 in Hf.
        exists (rho_sub rho2 (s_PB2b_D1 r)). split.
        { apply Good_sub; [destruct r; reflexivity|]. eapply Good_agree; [exact Hag2 | destruct r; cbn; lia | exact HG1]. }
        eapply SP_entails in Hw; [|exact (ent_PB2b_D1 r)].
        replace (length M1) with (7 - L0_of rho + k)%nat; [exact Hw|]. rewrite M1_len. unfold L0_of in *. unfold N0 in Hf. lia.
      *
        apply triple_facts. intros HF. pose proof (Forall_hd_r _ _ r HF _ _ _ eq_refl eq_refl) as Hf.
        cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Z.eqb_eq in Hf.
        erewrite (U_add2 rho2 (SVar 5) (SVar 67)) in Hf; [| reflexivity | reflexivity |];
          change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 67)) with (rw rho2 67) in *; change (eval rho2 (SVar 71)) with (rw rho2 71) in *.
        2:{ rewrite <- (proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 67%positive ltac:(destruct r; cbn; lia)), V5, E67. lia. }
        rewrite <- (proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 67%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 71%positive ltac:(destruct r; cbn; lia)), V5, E67, U71 in Hf.
        assert (ER : R_of (rho_sub rho2 s_PB2b_CB1) = (length argv0 + L0_of rho - k)%nat).
        { unfold R_of, L0_of. cbn [rho_sub rw]. rewrite sv_PB2b_68.
          unfold L0_of in Hgt, Hkb.
          erewrite (U_sub2 rho2 (SVar 5) _ N0 (Z.of_nat k - bv_unsigned (rw rho 67))); [unfold N0; lia | | | unfold N0 in *; lia].
          - change (eval rho2 (SVar 5)) with (rw rho2 5). rewrite <- (proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)). exact V5.
          - erewrite U_sub2; [reflexivity | | | lia]; change (eval rho2 (SVar 71)) with (rw rho2 71); change (eval rho2 (SVar 67)) with (rw rho2 67);
              rewrite <- ?(proj1 Hag2 71%positive ltac:(destruct r; cbn; lia)), <- ?(proj1 Hag2 67%positive ltac:(destruct r; cbn; lia)), ?U71, ?E67; reflexivity. }
        eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH1 (rho_sub rho2 s_PB2b_CB1))].
        -- intros w Hw. eapply SP_entails in Hw; [|exact (ent_PB2b_CB1 r)].
           replace (7 + length argv0 - R_of (rho_sub rho2 s_PB2b_CB1))%nat with (7 - L0_of rho + k)%nat by (unfold L0_of, N0 in *; lia). exact Hw.
        -- apply Good_sub; [destruct r; reflexivity|]. eapply Good_agree; [exact Hag2 | destruct r; cbn; lia | exact HG1].
        -- unfold L0_of, N0 in *. lia.
        -- unfold L0_of, N0 in *. lia.
  -
    intros rho HG HR Hm.
    eapply triple_seq.
    { apply (writev_site1 (CB1 r) (reg_sv (CB1 r) 22) (7 + length argv0 - R_of rho) (skipn (length argv0 - R_of rho) argv0) rho HG);
        [rewrite Hnxc; lia | exact Hic | exact H17c | exact H10c | exact H12c | rewrite R22c, Hnxc; reflexivity | | |].
      + replace (7 + length argv0 - R_of rho)%nat with (7 + (length argv0 - R_of rho))%nat by lia.
        rewrite MSG_skipA by lia. rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
      + rewrite length_skipn. unfold MAX_RW_COUNT. lia.
      + intros tr ms md Hsp. exact (proj2 (bytes_CB1 r rho tr ms md HG Hsp)). }
    apply triple_ex; intros rho1. apply triple_ex; intros k.
    apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
    rewrite Hnxc in Hk, Hag1. rewrite length_skipn in Hkb.
    assert (E68 : rw rho1 68 = rw rho 68) by (symmetry; apply (proj1 Hag1); lia).
    assert (U72 : bv_unsigned (rw rho1 72) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
    assert (HU68 : bv_unsigned (rw rho 68) = Z.of_nat (R_of rho)) by (unfold R_of; pose proof (urange (rw rho 68)); lia).
    pose proof (G_v5 rho1 HG1) as V5.

    eapply triple_conseq with (P := SP segs (Kx (TR (7 + length argv0 - R_of rho + k)) md0) (PB1 r) rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. apply SP_add1; [exact Hw | | destruct r; reflexivity]. cbn [holds]. change (eval rho1 (SVar 72)) with (rw rho1 72). rewrite U72, U_lit64 by lia. lia. }
    eapply run_tr; [exact (run_PB1 r) | destruct r; reflexivity | apply okf |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
    +
      eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
      intros w Hw. pose proof (hd_fact_r rho2 L_PB1_0 r w _ Hw _ _ _ eq_refl eq_refl) as Hf.
      cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
      change (eval rho2 (SVar 72)) with (rw rho2 72) in Hf. change (eval rho2 (SVar 68)) with (rw rho2 68) in Hf.
      rewrite <- (proj1 Hag2 72%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 68%positive ltac:(destruct r; cbn; lia)), U72, E68, HU68 in Hf.
      exists (rho_sub rho2 (s_PB1_D1 r)). split.
      { apply Good_sub; [destruct r; reflexivity|]. eapply Good_agree; [exact Hag2 | destruct r; cbn; lia | exact HG1]. }
      eapply SP_entails in Hw; [|exact (ent_PB1_D1 r)].
      replace (length M1) with (7 + length argv0 - R_of rho + k)%nat; [exact Hw|]. rewrite M1_len. lia.
    +
      apply triple_facts. intros HF. pose proof (Forall_hd_r _ _ r HF _ _ _ eq_refl eq_refl) as Hf.
      cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Z.eqb_eq in Hf.
      change (eval rho2 (SVar 72)) with (rw rho2 72) in Hf. change (eval rho2 (SVar 68)) with (rw rho2 68) in Hf.
      rewrite <- (proj1 Hag2 72%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 68%positive ltac:(destruct r; cbn; lia)), U72, E68, HU68 in Hf.
      assert (ER : R_of (rho_sub rho2 s_PB1_CB1) = (R_of rho - k)%nat).
      { unfold R_of at 1. cbn [rho_sub rw]. rewrite sv_PB1_68.
        erewrite U_sub2; [| reflexivity | reflexivity |]; change (eval rho2 (SVar 68)) with (rw rho2 68); change (eval rho2 (SVar 72)) with (rw rho2 72);
          rewrite <- (proj1 Hag2 68%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 72%positive ltac:(destruct r; cbn; lia)), E68, U72, HU68; lia. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH1 (rho_sub rho2 s_PB1_CB1))].
      * intros w Hw. eapply SP_entails in Hw; [|exact (ent_PB1_CB1 r)].
        replace (7 + length argv0 - R_of (rho_sub rho2 s_PB1_CB1))%nat with (7 + length argv0 - R_of rho + k)%nat by lia. exact Hw.
      * apply Good_sub; [destruct r; reflexivity|]. eapply Good_agree; [exact Hag2 | destruct r; cbn; lia | exact HG1].
      * lia.
      * lia.
Qed.

Lemma L_sess1 : forall r : bool, ((74%nat <= (length argv0))%nat -> (forall (rho : valuation), ((Good rho) -> (triple segs ok (SP segs (Kx (TR 0%nat) md0) (E_A1 r) rho) (QD1 r))))).
Proof using Hargc Hent Hfd2 Hrdr0 Hinp HokK HokP.
  intros r Hlen74 rho HG. pose proof NU as NU'.
  destruct (cert_E_A1 r) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R22 & Hi & H17 & H10 & H12 & Hnx).
  eapply triple_seq.
  { apply (writev_site2 (E_A1 r) (reg_sv (E_A1 r) 22) 0 (str "usage: ") argv0 rho HG);
      [rewrite Hnx; lia | exact Hi | exact H17 | exact H10 | exact H12 | rewrite R22, Hnx; reflexivity | | |].
    + change (skipn 0 MSG) with (M1 ++ M2). unfold M1. rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
    + rewrite length_app. cbn [length str]. unfold MAX_RW_COUNT. lia.
    + intros tr ms md Hsp. exact (bytes_E_A1 r rho tr ms md HG Hsp). }
  apply triple_ex; intros rho1. apply triple_ex; intros k.
  apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
  rewrite Hnx in Hk, Hag1. rewrite length_app in Hkb. cbn [length str] in Hkb.
  assert (U67 : bv_unsigned (rw rho1 67) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
  pose proof (G_v5 rho1 HG1) as V5.
  change (S_after_write (E_A1 r) (reg_sv (E_A1 r) 22)) with (PA1 r). cbn [Nat.add].
  destruct (Nat.le_gt_cases k 7) as [Hle|Hgt].
  -
    eapply triple_conseq with (P := SP segs (Kx (TR k) md0) (PA1a r) rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. apply SP_add1; [exact Hw | | destruct r; reflexivity]. cbn [holds]. change (eval rho1 (SVar 67)) with (rw rho1 67). rewrite U67, U_lit64 by lia. lia. }
    eapply run_tr; [exact (run_PA1a r) | destruct r; reflexivity | apply okf |].
    intros L rho2 [<-|[]] Hag2. cbn [lf_state].
    assert (EL : L0_of (rho_sub rho2 s_PA1a_CB2) = (7 - k)%nat).
    { unfold L0_of. cbn [rho_sub rw]. rewrite sv_PA1a_67.
      erewrite U_sub2; [| apply U_lit64; lia | reflexivity |]; change (eval rho2 (SVar 67)) with (rw rho2 67);
        rewrite <- (proj1 Hag2 67%positive ltac:(destruct r; cbn; lia)), U67; lia. }
    eapply triple_conseq; [| intros w Hw; exact Hw | apply (proj1 (loop1 r Hlen74 (7 - k + length argv0)) (rho_sub rho2 s_PA1a_CB2))].
    + intros w Hw. eapply SP_entails in Hw; [|exact (ent_PA1a_CB2 r)].
      replace (7 - L0_of (rho_sub rho2 s_PA1a_CB2))%nat with k by lia. exact Hw.
    + apply Good_sub; [destruct r; reflexivity|]. eapply Good_agree; [exact Hag2 | destruct r; cbn; lia | exact HG1].
    + lia.
    + lia.
  -
    eapply triple_conseq with (P := SP segs (Kx (TR k) md0) (PA1b r) rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. apply SP_add1; [exact Hw | | destruct r; reflexivity]. cbn [holds]. change (eval rho1 (SVar 67)) with (rw rho1 67). rewrite U67, U_lit64 by lia. lia. }
    eapply run_tr; [exact (run_PA1b r) | destruct r; reflexivity | apply okf |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
    +
      apply triple_facts. intros HF. pose proof (Forall_hd_r _ _ r HF _ _ _ eq_refl eq_refl) as Hf.
      cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Bool.negb_true_iff in Hf. apply Z.eqb_neq in Hf.
      erewrite (U_addc rho2 (SVar 5) 7) in Hf; [| reflexivity | |];
        change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 67)) with (rw rho2 67) in *.
      2,3: rewrite <- ?(proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)), ?V5; unfold N0; lia.
      rewrite <- (proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 67%positive ltac:(destruct r; cbn; lia)), V5, U67 in Hf.
      assert (ER : R_of (rho_sub rho2 s_PA1b_CB1) = (length argv0 + 7 - k)%nat).
      { unfold R_of. cbn [rho_sub rw]. rewrite sv_PA1b_68.
        erewrite (U_sub2 rho2 (SVar 5) _ N0 (Z.of_nat k - 7)); [unfold N0; lia | | | unfold N0 in *; lia].
        - change (eval rho2 (SVar 5)) with (rw rho2 5). rewrite <- (proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)). exact V5.
        - erewrite U_addc; [reflexivity | | lia | lia]. change (eval rho2 (SVar 67)) with (rw rho2 67).
          rewrite <- (proj1 Hag2 67%positive ltac:(destruct r; cbn; lia)). exact U67. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (proj2 (loop1 r Hlen74 (length argv0 + 7 - k)) (rho_sub rho2 s_PA1b_CB1))].
      * intros w Hw. eapply SP_entails in Hw; [|exact (ent_PA1b_CB1 r)].
        replace (7 + length argv0 - R_of (rho_sub rho2 s_PA1b_CB1))%nat with k by lia. exact Hw.
      * apply Good_sub; [destruct r; reflexivity|]. eapply Good_agree; [exact Hag2 | destruct r; cbn; lia | exact HG1].
      * unfold N0 in Hf. lia.
      * lia.
    +
      eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
      intros w Hw. pose proof (hd_fact_r rho2 L_PA1b_1 r w _ Hw _ _ _ eq_refl eq_refl) as Hf.
      cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Bool.negb_true_iff, Z.eqb_neq in Hf.
      erewrite (U_addc rho2 (SVar 5) 7) in Hf; [| reflexivity | |];
        change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 67)) with (rw rho2 67) in *.
      2,3: rewrite <- ?(proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)), ?V5; unfold N0; lia.
      rewrite <- (proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 67%positive ltac:(destruct r; cbn; lia)), V5, U67 in Hf.
      exists (rho_sub rho2 (s_PA1b_D1 r)). split.
      { apply Good_sub; [destruct r; reflexivity|]. eapply Good_agree; [exact Hag2 | destruct r; cbn; lia | exact HG1]. }
      eapply SP_entails in Hw; [|exact (ent_PA1b_D1 r)].
      replace (length M1) with k; [exact Hw|]. rewrite M1_len. unfold N0 in Hf. lia.
Qed.

Definition QD2 (r : bool) : assn := Q_at (D2 r) (length MSG).
Definition L0' (rho : valuation) : nat := Z.to_nat (bv_unsigned (rw rho 90)).

Lemma L_D1 : forall r : bool, (forall (rho : valuation), ((Good rho) -> (triple segs ok (SP segs (Kx (TR (length M1)) md0) (D1 r) rho) (Q_at (E_A2 r) (length M1))))).
Proof using Hargc HokK.
  intros r rho HG. eapply run_tr; [exact (run_D1 r) | destruct r; reflexivity | apply okf |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hw. exists rho1. split; [exact (Good_agree _ _ _ Hag1 ltac:(destruct r; cbn; lia) HG) | exact Hw].
Qed.

Lemma MSG_skipB : ltac2:(tb__ "0|1|
S30S3cR1U7A2S0S2dS38Q8A1M0A1Sa6G0Sa4S2eG0S53A2R2A2S51A3Sa6G0R2S57A3A3F_;Fc;").
Proof using Hargc. clear STR LEN. intros c Hc. unfold MSG. rewrite skipn_app, skipn_all2 by lia. replace (length M1 + c - length M1)%nat with c by lia. reflexivity. Qed.

Lemma loop2 : forall r : bool, (forall (m : nat), (forall (rho : valuation), ((Good rho) -> (((1%nat <= (L0' rho))%nat /\ ((L0' rho) <= 6%nat)%nat) -> (((L0' rho) <= m)%nat -> (triple segs ok (SP segs (Kx (TR (Nat.sub (Nat.add (length M1) 7%nat) (L0' rho))) md0) (CB3 r) rho) (QD2 r))))))).
Proof using Hargc Hent Hfd2 Hrdr0 Hinp HokK HokP.
  intros r. induction m as [|m IH]; intros rho HG HL Hm; [exfalso; lia|]. pose proof NU as NU'.
  destruct (cert_CB3 r) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R22 & Hi & H17 & H10 & H12 & Hnx & _).
  assert (HU90 : bv_unsigned (rw rho 90) = Z.of_nat (L0' rho)) by (unfold L0'; pose proof (urange (rw rho 90)); lia).
  eapply triple_seq.
  { apply (writev_site2 (CB3 r) (reg_sv (CB3 r) 22) (length M1 + 7 - L0' rho) (skipn (7 - L0' rho) M2) [] rho HG);
      [rewrite Hnx; lia | exact Hi | exact H17 | exact H10 | exact H12 | rewrite R22, Hnx; reflexivity | | |].
    + rewrite app_nil_r. replace (length M1 + 7 - L0' rho)%nat with (length M1 + (7 - L0' rho))%nat by lia.
      rewrite MSG_skipB by lia. rewrite firstn_all. reflexivity.
    + rewrite app_nil_r, length_skipn, M2_len. unfold MAX_RW_COUNT. lia.
    + intros tr ms md Hsp. exact (proj2 (bytes_CB3 r rho tr ms md HG Hsp)). }
  apply triple_ex; intros rho1. apply triple_ex; intros k.
  apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
  rewrite Hnx in Hk, Hag1. rewrite app_nil_r, length_skipn, M2_len in Hkb.
  assert (E90 : rw rho1 90 = rw rho 90) by (symmetry; apply (proj1 Hag1); lia).
  assert (U93 : bv_unsigned (rw rho1 93) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
  change (S_after_write (CB3 r) (reg_sv (CB3 r) 22)) with (PB3 r).
  eapply run_tr; [exact (run_PB3 r) | destruct r; reflexivity | apply okf |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
  -
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. pose proof (hd_fact_r rho2 L_PB3_0 r w _ Hw _ _ _ eq_refl eq_refl) as Hf.
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
    change (eval rho2 (SVar 93)) with (rw rho2 93) in Hf. change (eval rho2 (SVar 90)) with (rw rho2 90) in Hf.
    rewrite <- (proj1 Hag2 93%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 90%positive ltac:(destruct r; cbn; lia)), U93, E90, HU90 in Hf.
    exists (rho_sub rho2 (s_PB3_D2 r)). split.
    { apply Good_sub; [destruct r; reflexivity|]. eapply Good_agree; [exact Hag2 | destruct r; cbn; lia | exact HG1]. }
    eapply SP_entails in Hw; [|exact (ent_PB3_D2 r)].
    replace (length MSG) with (length M1 + 7 - L0' rho + k)%nat; [exact Hw|]. rewrite MSG_len, M1_len. lia.
  -
    apply triple_facts. intros HF. pose proof (Forall_hd_r _ _ r HF _ _ _ eq_refl eq_refl) as Hf.
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Z.eqb_eq in Hf.
    change (eval rho2 (SVar 93)) with (rw rho2 93) in Hf. change (eval rho2 (SVar 90)) with (rw rho2 90) in Hf.
    rewrite <- (proj1 Hag2 93%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 90%positive ltac:(destruct r; cbn; lia)), U93, E90, HU90 in Hf.
    assert (EL : L0' (rho_sub rho2 s_PB3_CB3) = (L0' rho - k)%nat).
    { unfold L0' at 1. cbn [rho_sub rw]. rewrite sv_PB3_90.
      erewrite U_sub2; [| reflexivity | reflexivity |]; change (eval rho2 (SVar 90)) with (rw rho2 90); change (eval rho2 (SVar 93)) with (rw rho2 93);
        rewrite <- (proj1 Hag2 90%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 93%positive ltac:(destruct r; cbn; lia)), E90, U93, HU90; lia. }
    eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH (rho_sub rho2 s_PB3_CB3))].
    + intros w Hw. eapply SP_entails in Hw; [|exact (ent_PB3_CB3 r)].
      replace (length M1 + 7 - L0' (rho_sub rho2 s_PB3_CB3))%nat with (length M1 + 7 - L0' rho + k)%nat by lia. exact Hw.
    + apply Good_sub; [destruct r; reflexivity|]. eapply Good_agree; [exact Hag2 | destruct r; cbn; lia | exact HG1].
    + lia.
    + lia.
Qed.

Lemma L_sess2 : forall r : bool, (forall (rho : valuation), ((Good rho) -> (triple segs ok (SP segs (Kx (TR (length M1)) md0) (E_A2 r) rho) (QD2 r)))).
Proof using Hargc Hent Hfd2 Hrdr0 Hinp HokK HokP.
  intros r rho HG. pose proof NU as NU'.
  destruct (cert_E_A2 r) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R22 & Hi & H17 & H10 & H12 & Hnx).
  eapply triple_seq.
  { apply (writev_site2 (E_A2 r) (reg_sv (E_A2 r) 22) (length M1) M2 [] rho HG);
      [rewrite Hnx; lia | exact Hi | exact H17 | exact H10 | exact H12 | rewrite R22, Hnx; reflexivity | | |].
    + rewrite app_nil_r. unfold MSG. rewrite skipn_app, skipn_all, Nat.sub_diag. cbn [skipn app]. rewrite firstn_all. reflexivity.
    + rewrite app_nil_r, M2_len. unfold MAX_RW_COUNT. lia.
    + intros tr ms md Hsp. exact (bytes_E_A2 r rho tr ms md HG Hsp). }
  apply triple_ex; intros rho1. apply triple_ex; intros k.
  apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
  rewrite Hnx in Hk, Hag1. rewrite app_nil_r, M2_len in Hkb.
  assert (U90 : bv_unsigned (rw rho1 90) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
  change (S_after_write (E_A2 r) (reg_sv (E_A2 r) 22)) with (PA2 r).
  eapply run_tr; [exact (run_PA2 r) | destruct r; reflexivity | apply okf |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
  -
    apply triple_facts. intros HF. pose proof (Forall_hd_r _ _ r HF _ _ _ eq_refl eq_refl) as Hf.
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Bool.negb_true_iff in Hf. apply Z.eqb_neq in Hf.
    change (eval rho2 (SVar 90)) with (rw rho2 90) in Hf. rewrite U_lit64 in Hf by lia.
    rewrite <- (proj1 Hag2 90%positive ltac:(destruct r; cbn; lia)), U90 in Hf.
    assert (EL : L0' (rho_sub rho2 s_PA2_CB3) = (7 - k)%nat).
    { unfold L0'. cbn [rho_sub rw]. rewrite sv_PA2_90.
      erewrite U_sub2; [| apply U_lit64; lia | reflexivity |]; change (eval rho2 (SVar 90)) with (rw rho2 90);
        rewrite <- (proj1 Hag2 90%positive ltac:(destruct r; cbn; lia)), U90; lia. }
    eapply triple_conseq; [| intros w Hw; exact Hw | apply (loop2 r (7 - k) (rho_sub rho2 s_PA2_CB3))].
    + intros w Hw. eapply SP_entails in Hw; [|exact (ent_PA2_CB3 r)].
      replace (length M1 + 7 - L0' (rho_sub rho2 s_PA2_CB3))%nat with (length M1 + k)%nat by lia. exact Hw.
    + apply Good_sub; [destruct r; reflexivity|]. eapply Good_agree; [exact Hag2 | destruct r; cbn; lia | exact HG1].
    + lia.
    + lia.
  -
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. pose proof (hd_fact_r rho2 L_PA2_1 r w _ Hw _ _ _ eq_refl eq_refl) as Hf.
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Bool.negb_true_iff, Z.eqb_neq in Hf.
    change (eval rho2 (SVar 90)) with (rw rho2 90) in Hf. rewrite U_lit64 in Hf by lia.
    rewrite <- (proj1 Hag2 90%positive ltac:(destruct r; cbn; lia)), U90 in Hf.
    exists (rho_sub rho2 (s_PA2_D2 r)). split.
    { apply Good_sub; [destruct r; reflexivity|]. eapply Good_agree; [exact Hag2 | destruct r; cbn; lia | exact HG1]. }
    eapply SP_entails in Hw; [|exact (ent_PA2_D2 r)].
    replace (length MSG) with (length M1 + k)%nat; [exact Hw|]. rewrite MSG_len, M1_len. lia.
Qed.

Lemma cert_exit : forall r : bool, (((instr_at segs (ss_pc (E_exit r))) = (Some Ecall)) /\ (((reg_sv (E_exit r) 17%Z) = (SLit 94%Z)) /\ ((reg_sv (E_exit r) 10%Z) = (SLit 2%Z)))).
Proof using . intros [|]; vm_compute; repeat split; reflexivity. Qed.

Lemma L_exit : forall r : bool, (forall (rho : valuation), ((Good rho) -> (triple segs ok (SP segs (Kx (TR (length MSG)) md0) (D2 r) rho) (fun (x : world) => False)))).
Proof using Hargc Hfs HokK HokP Hokh.
  intros r rho HG. eapply run_tr; [exact (run_D2 r) | destruct r; reflexivity | apply okf |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  destruct (cert_exit r) as (Hi & H17 & H10).
  apply (SysNA.triple_exit_eval_na segs ok SpecT (Kx (TR (length MSG)) md0) (E_exit r) rho1 2);
    [apply okf | apply okp | exact Hokh | exact Hi | left; exact H17 | rewrite H10; rewrite U_lit64 by lia; reflexivity |].
  intros tr md [-> ->]. rewrite TR_all by lia. rewrite Hfs. exact final_in_spec.
Qed.

Theorem usage74_safe : ((74%nat <= (length argv0))%nat -> (forall (rho : valuation), ((JI rho) -> (triple segs ok (SP segs (Kx [] md0) (S_main rq) rho) (fun (x : world) => False))))).
Proof using Hargc Hent Hfd2 Hrdr0 Hfs Hinp HokK HokP Hokh LEN N0 STR.
  intros Hlen74 rho HJ.
  eapply triple_conseq with (P := fun w => exists rho', Good rho' /\ SP segs (Kx (TR 0) md0) (S_use rq) rho' w); [| intros w Hw; exact Hw |].
  { intros w Hw. apply (use_intro rho w HJ). exact Hw. }
  apply triple_ex; intros rho1. apply triple_pure; intros HG1.
  eapply triple_seq; [apply (L_call Hlen74 rq); exact HG1|].
  apply triple_ex; intros rho2. apply triple_pure; intros HG2.
  eapply triple_seq; [apply (L_sess1 rq Hlen74); exact HG2|].
  apply triple_ex; intros rho3. apply triple_pure; intros HG3.
  eapply triple_seq; [apply (L_D1 rq); exact HG3|].
  apply triple_ex; intros rho4. apply triple_pure; intros HG4.
  eapply triple_seq; [apply (L_sess2 rq); exact HG4|].
  apply triple_ex; intros rho5. apply triple_pure; intros HG5.
  apply (L_exit rq). exact HG5.
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

Lemma Tn_intro : forall r : bool, (forall (n : Z), (forall (rho : valuation), (forall (w : world), ((Good rho) -> ((N0 = n) -> (((swf (Tn r n)) = true) -> ((SP segs (Kx (TR 0%nat) md0) (T_sn1 r) rho w) -> (SP segs (Kx (TR 0%nat) md0) (Tn r n) rho w)))))))).
Proof using Hargc Hent Hinp.
  intros r n rho w HG Hn Hwf [Hsm Hk]. split; [|exact Hk]. unfold Tn. apply smatch_subst_intro; [exact Hwf|].
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
  replace (map (fun x : nat => nth (Z.to_nat (Z.of_nat x)) (strs_tail inp) (Z_to_bv 8 0)) (seq 0 (length argv0)))
    with (map (fun j : nat => nth j (strs_tail inp) (Z_to_bv 8 0)) (seq 0 (length argv0)))
    by (apply map_ext; intros j; rewrite Nat2Z.id; reflexivity).
  rewrite (map_nth_seq (strs_tail inp) (length argv0) (Z_to_bv 8 0)) by (pose proof tail_len; pose proof NU; lia).
  rewrite tail_firstn. rewrite <- app_assoc. reflexivity.
Qed.

(* LPS 727298f3: the per-leaf check [check_wleaf] (P/Drv_usage__G1) gives each leaf's buffer, bytes and
   entailment of [E_Wg r]; [check_core] gives the run's leaves as [a :: ws], [a] the leaf that
   contradicts the length, and [check_wleaf] for every leaf of [ws]. *)
Lemma check_wleaf_sound : forall (r : bool) (n : Z) (w : sstate), check_wleaf r n w = true ->
  exists (wx : sstate) (o : sobj) (bl : list bexp),
    apply_xforms w (xs_ibuf n) = Some wx /\ nth_error (ss_objs wx) 1%nat = Some o /\
    ob_lo o = SLit (-560) /\ ob_hi o = SLit (n - 546) /\
    dflt_writable (ob_dflt o) = true /\ is_arr (ob_dflt o) = false /\
    cells_bytes (ob_cells o) (SLit (-560)) 0 (Z.to_nat (14 + n)) = Some bl /\
    list_eqb bexp_eqb bl (BLn n) = true /\ state_has_rl 4%positive wx = false /\
    entails (obj_to_list wx 1%nat 4%positive) (E_Wg r)
      ((5%positive, SLit n) :: infer_sub GLg (obj_to_list wx 1%nat 4%positive) (E_Wg r)) = true /\
    sub_ok_n ((5%positive, SLit n) :: infer_sub GLg (obj_to_list wx 1%nat 4%positive) (E_Wg r)) n = true.
Proof using .
  intros r n w H. unfold check_wleaf in H. cbv zeta in H.
  destruct (apply_xforms w (xs_ibuf n)) as [wx|] eqn:Ex; [|discriminate].
  apply andb_prop in H as [H4 H7]. apply andb_prop in H4 as [H4 H6].
  destruct (nth_error (ss_objs wx) 1) as [o|] eqn:Eo; [|discriminate].
  apply andb_prop in H4 as [H4 Hcb]. apply andb_prop in H4 as [H4 Harr]. apply andb_prop in H4 as [H4 Hwr]. apply andb_prop in H4 as [Hlo Hhi].
  destruct (cells_bytes (ob_cells o) (SLit (-560)) 0 (Z.to_nat (14 + n))) as [bl|] eqn:Ecb; [|discriminate].
  apply andb_prop in H7 as [He Hs].
  exists wx, o, bl. repeat split; auto.
  - apply sv_eqb_sound in Hlo. exact Hlo.
  - apply sv_eqb_sound in Hhi. exact Hhi.
  - destruct (is_arr (ob_dflt o)); [discriminate|reflexivity].
  - destruct (state_has_rl 4 wx); [discriminate|reflexivity].
Qed.

Lemma check_core_sound : forall (r : bool) (n : Z) (r1 : option (list leaf)), check_core r n r1 = true ->
  exists (a : leaf) (ws : list leaf),
    swf (Tn r n) = true /\ r1 = Some (a :: ws) /\ In (BNZ3 (SLit n)) (ss_facts (lf_state a)) /\
    Forall (fun b : leaf =>
      exists (wx : sstate) (o : sobj) (bl : list bexp),
        apply_xforms (lf_state b) (xs_ibuf n) = Some wx /\ nth_error (ss_objs wx) 1%nat = Some o /\
        ob_lo o = SLit (-560) /\ ob_hi o = SLit (n - 546) /\
        dflt_writable (ob_dflt o) = true /\ is_arr (ob_dflt o) = false /\
        cells_bytes (ob_cells o) (SLit (-560)) 0 (Z.to_nat (14 + n)) = Some bl /\
        list_eqb bexp_eqb bl (BLn n) = true /\ state_has_rl 4%positive wx = false /\
        entails (obj_to_list wx 1%nat 4%positive) (E_Wg r)
          ((5%positive, SLit n) :: infer_sub GLg (obj_to_list wx 1%nat 4%positive) (E_Wg r)) = true /\
        sub_ok_n ((5%positive, SLit n) :: infer_sub GLg (obj_to_list wx 1%nat 4%positive) (E_Wg r)) n = true) ws.
Proof using .
  intros r n r1 H. unfold check_core in H.
  apply andb_prop in H as [H1 H2].
  destruct r1 as [[|a [|b ws]]|]; cbv beta iota zeta in H2; try discriminate.
  apply andb_prop in H2 as [H3 H4].
  apply existsb_exists in H3 as (p & Hp & Ep). apply sprop_eqb_sound in Ep. subst p.
  exists a, (b :: ws). split; [exact H1|]. split; [reflexivity|]. split; [exact Hp|].
  apply Forall_forall. intros l Hl. apply check_wleaf_sound.
  exact (proj1 (forallb_forall _ _) H4 l Hl).
Qed.

Lemma L_small_pre : forall r : bool, (forall (n : Z), (((check_core r n (sym_run segs FUELn [] (Tn r n) true)) = true) -> ((N0 = n) -> (forall (rho : valuation), ((Good rho) -> (triple segs ok (SP segs (Kx (TR 0%nat) md0) (Tn r n) rho) (QW_at (E_Wg r) 0%nat))))))).
Proof using Hargc Hent Hinp HokK.
  intros r n Hchk Hn rho HG. pose proof NU as NU'.
  destruct (check_core_sound r n _ Hchk) as (a & ws & Hwf & Hr & HinX & Hws).
  eapply run_tr; [exact Hr | destruct r; reflexivity | apply okf |].
  intros L rho1 [<-|HL] Hag1.
  -
    intros m Hg w Hw. exfalso.
    pose proof (SP_fact _ _ _ _ _ Hw HinX) as Hf. unfold BNZ3 in Hf. apply (proj1 (holds_BNZ rho1 (SLit n))) in Hf.
    apply Hf. rewrite <- (proj1 (proj2 Hag1)), (G_rl3 rho HG). rewrite U_lit64 by lia.
    unfold nthb. subst n. unfold N0. rewrite Nat2Z.id, tail_nul. reflexivity.
  - destruct (proj1 (Forall_forall _ _) Hws L HL) as (wx & o & bl & Hx & Ho & Hlo & Hhi & Hwr & Harr & Hcb & Hbl & Hrl & He & Hs).
    pose proof (Good_agree _ _ _ Hag1 ltac:(unfold Tn; destruct r; cbn; lia) HG) as HG1.
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w [Hsm Hk].
    pose proof (smatch_xforms segs _ _ _ _ w Hx Hsm) as Hsm2.
    pose proof (smatch_obj_to_list segs rho1 wx w 1 4 o (-560) (n - 546) bl Hsm2 Ho Hlo Hhi ltac:(lia) ltac:(lia) Hwr Harr) as Hsm3.
    replace (n - 546 - -560) with (14 + n) in Hsm3 by lia. specialize (Hsm3 Hcb Hrl).
    set (rho2 := rho_set_rl rho1 4 (map (beval rho1) bl)) in Hsm3.
    set (sW := (5%positive, SLit n) :: infer_sub GLg (obj_to_list wx 1 4) (E_Wg r)) in He, Hs.
    exists (rho_sub rho2 sW). split.
    + assert (HG2 : Good rho2).
      { destruct HG1 as (HJ & H3 & H25). subst rho2. split; [|split; [cbn; exact H3 | cbn; exact H25]].
        destruct HJ; constructor; cbn [rho_set_rl rw rl rm]; auto. }
      unfold sub_ok_n in Hs. apply andb_prop in Hs as [Hs6 Hs5]. apply sv_eqb_sound in Hs5.
      cbn [forallb] in Hs6.
      apply andb_prop in Hs6 as [E1 Hs6]. apply andb_prop in Hs6 as [E2 Hs6]. apply andb_prop in Hs6 as [E3 Hs6].
      apply andb_prop in Hs6 as [E4 Hs6]. apply andb_prop in Hs6 as [E6 Hs6]. apply andb_prop in Hs6 as [E25 Hs6].
      apply andb_prop in Hs6 as [E7 Hs6]. apply andb_prop in Hs6 as [E8 Hs6]. apply andb_prop in Hs6 as [E9 Hs6]. apply andb_prop in Hs6 as [E10 Hs6].
      apply andb_prop in Hs6 as [E13 _].
      apply sv_eqb_sound in E7. apply sv_eqb_sound in E8. apply sv_eqb_sound in E9. apply sv_eqb_sound in E10. apply sv_eqb_sound in E13.
      apply sv_eqb_sound in E1. apply sv_eqb_sound in E2. apply sv_eqb_sound in E3.
      apply sv_eqb_sound in E4. apply sv_eqb_sound in E6. apply sv_eqb_sound in E25.
      split.
      * destruct HG2 as (HJ & H3 & H25). split; [|split; [cbn; exact H3 | cbn [rho_sub rw]; rewrite E25; cbn [eval]; exact H25]].
        destruct HJ; constructor; cbn [rho_sub rw rl rm]; rewrite ?E1, ?E2, ?E3, ?E4, ?E6, ?E7, ?E8, ?E9, ?E10, ?E13, ?Hs5; cbn [eval]; auto.
        rewrite <- Hn. reflexivity.
      * cbn [rho_sub rl]. subst rho2. cbn [rho_set_rl rl]. rewrite Pos.eqb_refl.
        rewrite (list_bexp_eqb_beval rho1 _ _ Hbl). subst n. apply BLn_eval. exact HG1.
    + split; [|exact Hk]. eapply entails_sound; [exact He | exact Hsm3].
Qed.

Lemma cert_E_Wg : forall r : bool, (((obj_rng (ob0 (E_Wg r))) = (pair (pair (SVar 1%positive) (SLit (Z.opp STK_FREE))) (SLit (-560)%Z))) /\ (((ob1 (E_Wg r)) = (mkObj (SVar 1%positive) (SLit (-560)%Z) (SAlu ALU_ADD (SVar 5%positive) (SLit 18446744073709551070%Z)) [] (DList 4%positive))) /\ ((2%nat <= (length (ss_objs (E_Wg r))))%nat /\ (((existsb (cell_eqb (mkCell (SLit (-680)%Z) 8%Z (SAlu ALU_ADD (SVar 1%positive) (SLit (-560)%Z)))) (ob_cells (ob0 (E_Wg r)))) = true) /\ (((existsb (cell_eqb (mkCell (SLit (-672)%Z) 8%Z (SAlu ALU_ADD (SVar 5%positive) (SLit 14%Z)))) (ob_cells (ob0 (E_Wg r)))) = true) /\ (((existsb (cell_eqb (mkCell (SLit (-664)%Z) 8%Z (SLit 0%Z))) (ob_cells (ob0 (E_Wg r)))) = true) /\ (((existsb (cell_eqb (mkCell (SLit (-656)%Z) 8%Z (SLit 0%Z))) (ob_cells (ob0 (E_Wg r)))) = true) /\ (((reg_sv (E_Wg r) 11%Z) = (SAlu ALU_ADD (SVar 1%positive) (SLit (-680)%Z))) /\ (((reg_sv (E_Wg r) 22%Z) = (SAlu ALU_ADD (SVar 5%positive) (SLit 14%Z))) /\ (((instr_at segs (ss_pc (E_Wg r))) = (Some Ecall)) /\ (((reg_sv (E_Wg r) 17%Z) = (SLit 66%Z)) /\ (((reg_sv (E_Wg r) 10%Z) = (SLit 2%Z)) /\ (((reg_sv (E_Wg r) 12%Z) = (SLit 2%Z)) /\ (((ss_next (E_Wg r)) = 106%positive) /\ (In (SPUle (SVar 5%positive) (SLit 66%Z)) (ss_facts (E_Wg r))))))))))))))))).
Proof using Hargc LEN N0 STR. intros [|]; vm_compute; repeat split; (reflexivity || lia || (cbn; tauto)). Qed.

Lemma cert_CBg : forall r : bool, (((obj_rng (ob0 (CBg r))) = (pair (pair (SVar 1%positive) (SLit (Z.opp STK_FREE))) (SLit (-560)%Z))) /\ (((ob1 (CBg r)) = (mkObj (SVar 1%positive) (SLit (-560)%Z) (SAlu ALU_ADD (SVar 5%positive) (SLit 18446744073709551070%Z)) [] (DList 4%positive))) /\ ((2%nat <= (length (ss_objs (CBg r))))%nat /\ (((existsb (cell_eqb (mkCell (SLit (-680)%Z) 8%Z (SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_ADD (SVar 1%positive) (SLit (-546)%Z)) (SVar 5%positive)) (SVar 106%positive)))) (ob_cells (ob0 (CBg r)))) = true) /\ (((existsb (cell_eqb (mkCell (SLit (-672)%Z) 8%Z (SVar 106%positive))) (ob_cells (ob0 (CBg r)))) = true) /\ (((existsb (cell_eqb (mkCell (SLit (-664)%Z) 8%Z (SLit 0%Z))) (ob_cells (ob0 (CBg r)))) = true) /\ (((existsb (cell_eqb (mkCell (SLit (-656)%Z) 8%Z (SLit 0%Z))) (ob_cells (ob0 (CBg r)))) = true) /\ (((reg_sv (CBg r) 11%Z) = (SAlu ALU_ADD (SVar 1%positive) (SLit (-680)%Z))) /\ (((reg_sv (CBg r) 22%Z) = (SVar 106%positive)) /\ (((instr_at segs (ss_pc (CBg r))) = (Some Ecall)) /\ (((reg_sv (CBg r) 17%Z) = (SLit 66%Z)) /\ (((reg_sv (CBg r) 10%Z) = (SLit 2%Z)) /\ (((reg_sv (CBg r) 12%Z) = (SLit 2%Z)) /\ (((ss_next (CBg r)) = 109%positive) /\ ((In (SPUle (SLit 1%Z) (SVar 106%positive)) (ss_facts (CBg r))) /\ ((In (SPUle (SVar 106%positive) (SAlu ALU_ADD (SVar 5%positive) (SLit 13%Z))) (ss_facts (CBg r))) /\ (In (SPUle (SVar 5%positive) (SLit 66%Z)) (ss_facts (CBg r))))))))))))))))))).
Proof using Hargc LEN N0 STR. intros [|]; vm_compute; repeat split; (reflexivity || lia || (cbn; tauto)). Qed.

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

Lemma bytes_E_Wg : forall r rho tr ms md, GoodW rho -> (length argv0 <= 66)%nat -> smatch_pending segs rho (E_Wg r) (tr, mkCfg ms md) ->
  exists b1 l1 b2 l2,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv (E_Wg r) 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (E_Wg r) 11) + 8)%bv = Some l1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (E_Wg r) 11) + 16)%bv = Some b2
    /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv (E_Wg r) 11) + 16) + 8)%bv = Some l2
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some MSG
    /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some []
    /\ bv_unsigned (eval rho (reg_sv (E_Wg r) 22)) = Z.of_nat (length (MSG ++ []))
    /\ (bv_unsigned (eval rho (reg_sv (E_Wg r) 11)) + 32 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
    /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros r rho tr ms md HGW Hsmall Hsp. pose proof (proj1 HGW) as HG. pose proof NU as NU'.
  destruct (cert_E_Wg r) as (Hrng & Hob1 & Hlen & C1 & C2 & C3 & C4 & R11 & R22 & _).
  rewrite R11, R22. pose proof (G_v1 rho HG) as V1. pose proof (G_v5 rho HG) as V5.
  assert (A0 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-680)))) = bv_unsigned sp - 680).
  { erewrite U_addc; [reflexivity | exact V1 | lia | lia]. }
  assert (A16 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-680))) + 16)%bv = bv_unsigned sp - 664).
  { rewrite (U_bvadd _ _ _ _ A0 u16) by lia. lia. }
  exists (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-560)))), (eval rho (SAlu ALU_ADD (SVar 5) (SLit 14))), (eval rho (SLit 0)), (eval rho (SLit 0)).
  apply and7_tail; [tsz|].
  split; [eapply (iov_field_lo rho (E_Wg r) tr ms md (-680)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field_lo rho (E_Wg r) tr ms md (-672)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split; [eapply (iov_field_lo rho (E_Wg r) tr ms md (-664)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C3 | lia | lia]|].
  split; [eapply (iov_field_lo rho (E_Wg r) tr ms md (-656)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C4 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
  split.
  { rewrite <- (firstn_all MSG), <- (skipn_O MSG). change 0%nat with (Z.to_nat 0).
    apply (ibufL_read rho (E_Wg r) tr ms md 0 (length MSG)); [exact HGW | exact Hsp | exact Hlen | exact Hob1 | exact Hsmall | lia | rewrite MSG_len; unfold N0; lia | |].
    - erewrite U_addc; [| exact V1 | lia | lia]. lia.
    - erewrite U_addc; [| exact V5 | unfold N0; lia | lia]. rewrite MSG_len. unfold N0. lia. }
  split; [reflexivity|].
  erewrite U_addc; [| exact V5 | unfold N0; lia | lia]. rewrite app_nil_r, MSG_len. unfold N0. lia.
Qed.

Lemma bytes_CBg : forall r rho tr ms md, GoodW rho -> (length argv0 <= 66)%nat -> smatch_pending segs rho (CBg r) (tr, mkCfg ms md) ->
  let L0 := Z.to_nat (bv_unsigned (rw rho 106)) in
  (1 <= L0 <= 13 + length argv0)%nat /\
  exists b1 l1 b2 l2,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv (CBg r) 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (CBg r) 11) + 8)%bv = Some l1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (CBg r) 11) + 16)%bv = Some b2
    /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv (CBg r) 11) + 16) + 8)%bv = Some l2
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some (skipn (length MSG - L0) MSG)
    /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some []
    /\ bv_unsigned (eval rho (reg_sv (CBg r) 22)) = Z.of_nat (length (skipn (length MSG - L0) MSG ++ []))
    /\ (bv_unsigned (eval rho (reg_sv (CBg r) 11)) + 32 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
    /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros r rho tr ms md HGW Hsmall Hsp. pose proof (proj1 HGW) as HG. pose proof NU as NU'.
  destruct (cert_CBg r) as (Hrng & Hob1 & Hlen & C1 & C2 & C3 & C4 & R11 & R22 & _ & _ & _ & _ & _ & HinF1 & HinF2 & _).
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
  split; [eapply (iov_field_lo rho (CBg r) tr ms md (-680)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field_lo rho (CBg r) tr ms md (-672)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split; [eapply (iov_field_lo rho (CBg r) tr ms md (-664)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C3 | lia | lia]|].
  split; [eapply (iov_field_lo rho (CBg r) tr ms md (-656)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C4 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
  split.
  { replace (skipn (length MSG - L0) MSG) with (firstn L0 (skipn (Z.to_nat (Z.of_nat (length MSG - L0))) MSG)).
    2:{ rewrite Nat2Z.id. rewrite firstn_all2; [reflexivity|]. rewrite length_skipn. lia. }
    apply (ibufL_read rho (CBg r) tr ms md (Z.of_nat (length MSG - L0)) L0); [exact HGW | exact Hsp | exact Hlen | exact Hob1 | exact Hsmall | lia | rewrite MSG_len; unfold N0; lia | | subst L0; change (eval rho (SVar 106)) with (rw rho 106); lia].
    erewrite (U_sub2 rho _ _ (bv_unsigned sp - 546 + N0) (bv_unsigned (rw rho 106))); [rewrite MSG_len; subst L0; unfold N0 in *; lia | | reflexivity | unfold N0 in *; lia].
    erewrite (U_add2 rho _ _ (bv_unsigned sp - 546) N0); [lia | | exact V5 | unfold N0 in *; lia].
    apply (U_addc rho (SVar 1) (-546) (bv_unsigned sp)); [exact V1 | lia | lia]. }
  split; [reflexivity|].
  change (eval rho (SVar 106)) with (rw rho 106). rewrite app_nil_r, length_skipn, MSG_len. subst L0. unfold N0 in *. lia.
Qed.

Definition L0g (rho : valuation) : nat := Z.to_nat (bv_unsigned (rw rho 106)).
Definition QDg (r : bool) : assn := QW_at (Dg r) (length MSG).

Lemma loopg : forall r : bool, (((length argv0) <= 66%nat)%nat -> (forall (m : nat), (forall (rho : valuation), ((GoodW rho) -> (((1%nat <= (L0g rho))%nat /\ ((L0g rho) <= (Nat.add 13%nat (length argv0)))%nat) -> (((L0g rho) <= m)%nat -> (triple segs ok (SP segs (Kx (TR (Nat.sub (length MSG) (L0g rho))) md0) (CBg r) rho) (QDg r)))))))).
Proof using Hargc Hent Hfd2 Hrdr0 Hinp HokK HokP.
  intros r Hsmall. induction m as [|m IH]; intros rho HGW HL Hm; [exfalso; lia|]. pose proof NU as NU'. pose proof (proj1 HGW) as HG.
  destruct (cert_CBg r) as (_ & _ & _ & _ & _ & _ & _ & _ & R22 & Hi & H17 & H10 & H12 & Hnx & _).
  assert (HU : bv_unsigned (rw rho 106) = Z.of_nat (L0g rho)) by (unfold L0g; pose proof (urange (rw rho 106)); lia).
  pose proof MSG_len as ML.
  eapply triple_seq.
  { apply (writev_site2 (CBg r) (reg_sv (CBg r) 22) (length MSG - L0g rho) (skipn (length MSG - L0g rho) MSG) [] rho HG);
      [rewrite Hnx; lia | exact Hi | exact H17 | exact H10 | exact H12 | rewrite R22, Hnx; reflexivity | | |].
    + rewrite app_nil_r, firstn_all. reflexivity.
    + rewrite app_nil_r, length_skipn. unfold MAX_RW_COUNT. lia.
    + intros tr ms md Hsp. exact (proj2 (bytes_CBg r rho tr ms md HGW Hsmall Hsp)). }
  apply triple_ex; intros rho1. apply triple_ex; intros k.
  apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
  rewrite Hnx in Hk, Hag1. rewrite app_nil_r, length_skipn in Hkb.
  assert (HGW1 : GoodW rho1) by (split; [exact HG1 | rewrite <- (proj1 (proj2 Hag1)); exact (proj2 HGW)]).
  assert (E106 : rw rho1 106 = rw rho 106) by (symmetry; apply (proj1 Hag1); lia).
  assert (U109 : bv_unsigned (rw rho1 109) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
  change (S_after_write (CBg r) (reg_sv (CBg r) 22)) with (PBg r).
  eapply run_tr; [exact (run_PBg r) | destruct r; reflexivity | apply okf |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
  -
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. pose proof (hd_fact_r rho2 L_PBg_0 r w _ Hw _ _ _ eq_refl eq_refl) as Hf.
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
    change (eval rho2 (SVar 109)) with (rw rho2 109) in Hf. change (eval rho2 (SVar 106)) with (rw rho2 106) in Hf.
    rewrite <- (proj1 Hag2 109%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)), U109, E106, HU in Hf.
    exists (rho_sub rho2 (s_PBg_Dg r)). split.
    { apply GoodW_sub; [destruct r; reflexivity|]. eapply GoodW_agree; [exact Hag2 | destruct r; cbn; lia | exact HGW1]. }
    eapply SP_entails in Hw; [|exact (ent_PBg_Dg r)].
    replace (length MSG) with (length MSG - L0g rho + k)%nat at 1; [exact Hw|]. lia.
  -
    apply triple_facts. intros HF. pose proof (Forall_hd_r _ _ r HF _ _ _ eq_refl eq_refl) as Hf.
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Z.eqb_eq in Hf.
    change (eval rho2 (SVar 109)) with (rw rho2 109) in Hf. change (eval rho2 (SVar 106)) with (rw rho2 106) in Hf.
    rewrite <- (proj1 Hag2 109%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)), U109, E106, HU in Hf.
    assert (EL : L0g (rho_sub rho2 (s_PBg_CBg r)) = (L0g rho - k)%nat).
    { unfold L0g at 1. cbn [rho_sub rw]. rewrite (sv_PBg_106 r).
      erewrite U_sub2; [| reflexivity | reflexivity |]; change (eval rho2 (SVar 106)) with (rw rho2 106); change (eval rho2 (SVar 109)) with (rw rho2 109);
        rewrite <- (proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 109%positive ltac:(destruct r; cbn; lia)), E106, U109, HU; lia. }
    eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH (rho_sub rho2 (s_PBg_CBg r)))].
    + intros w Hw. eapply SP_entails in Hw; [|exact (ent_PBg_CBg r)].
      replace (length MSG - L0g (rho_sub rho2 (s_PBg_CBg r)))%nat with (length MSG - L0g rho + k)%nat by lia. exact Hw.
    + apply GoodW_sub; [destruct r; reflexivity|]. eapply GoodW_agree; [exact Hag2 | destruct r; cbn; lia | exact HGW1].
    + lia.
    + lia.
Qed.

Lemma L_Wg : forall r : bool, (((length argv0) <= 66%nat)%nat -> (forall (rho : valuation), ((GoodW rho) -> (triple segs ok (SP segs (Kx (TR 0%nat) md0) (E_Wg r) rho) (QDg r))))).
Proof using Hargc Hent Hfd2 Hrdr0 Hinp HokK HokP.
  intros r Hsmall rho HGW. pose proof NU as NU'. pose proof (proj1 HGW) as HG. pose proof MSG_len as ML.
  destruct (cert_E_Wg r) as (_ & _ & _ & _ & _ & _ & _ & _ & R22 & Hi & H17 & H10 & H12 & Hnx & _).
  eapply triple_seq.
  { apply (writev_site2 (E_Wg r) (reg_sv (E_Wg r) 22) 0 MSG [] rho HG);
      [rewrite Hnx; lia | exact Hi | exact H17 | exact H10 | exact H12 | rewrite R22, Hnx; reflexivity | | |].
    + rewrite app_nil_r. cbn [skipn]. rewrite firstn_all. reflexivity.
    + rewrite app_nil_r. unfold MAX_RW_COUNT. lia.
    + intros tr ms md Hsp. exact (bytes_E_Wg r rho tr ms md HGW Hsmall Hsp). }
  apply triple_ex; intros rho1. apply triple_ex; intros k.
  apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
  rewrite Hnx in Hk, Hag1. rewrite app_nil_r in Hkb.
  assert (HGW1 : GoodW rho1) by (split; [exact HG1 | rewrite <- (proj1 (proj2 Hag1)); exact (proj2 HGW)]).
  assert (U106 : bv_unsigned (rw rho1 106) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
  pose proof (G_v5 rho1 HG1) as V5.
  change (S_after_write (E_Wg r) (reg_sv (E_Wg r) 22)) with (PAg r). cbn [Nat.add].
  eapply run_tr; [exact (run_PAg r) | destruct r; reflexivity | apply okf |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
  -
    apply triple_facts. intros HF. pose proof (Forall_hd_r _ _ r HF _ _ _ eq_refl eq_refl) as Hf.
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Bool.negb_true_iff in Hf. apply Z.eqb_neq in Hf.
    erewrite (U_addc rho2 (SVar 5) 14) in Hf; [| reflexivity | |];
      change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 106)) with (rw rho2 106) in *.
    2,3: rewrite <- ?(proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)), ?V5; unfold N0; lia.
    rewrite <- (proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)), V5, U106 in Hf.
    assert (EL : L0g (rho_sub rho2 (s_PAg_CBg r)) = (length MSG - k)%nat).
    { unfold L0g. cbn [rho_sub rw]. rewrite (sv_PAg_106 r).
      erewrite (U_sub2 rho2 _ _ (N0 + 14) (Z.of_nat k)); [unfold N0; lia | | | unfold N0 in *; lia].
      - erewrite U_addc; [reflexivity | | unfold N0; lia | lia]. change (eval rho2 (SVar 5)) with (rw rho2 5). rewrite <- (proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)). exact V5.
      - change (eval rho2 (SVar 106)) with (rw rho2 106). rewrite <- (proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)). exact U106. }
    eapply triple_conseq; [| intros w Hw; exact Hw | apply (loopg r Hsmall (length MSG - k) (rho_sub rho2 (s_PAg_CBg r)))].
    + intros w Hw. eapply SP_entails in Hw; [|exact (ent_PAg_CBg r)].
      replace (length MSG - L0g (rho_sub rho2 (s_PAg_CBg r)))%nat with k by lia. exact Hw.
    + apply GoodW_sub; [destruct r; reflexivity|]. eapply GoodW_agree; [exact Hag2 | destruct r; cbn; lia | exact HGW1].
    + unfold N0 in Hf. lia.
    + lia.
  -
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. pose proof (hd_fact_r rho2 L_PAg_1 r w _ Hw _ _ _ eq_refl eq_refl) as Hf.
    cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Bool.negb_true_iff, Z.eqb_neq in Hf.
    erewrite (U_addc rho2 (SVar 5) 14) in Hf; [| reflexivity | |];
      change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 106)) with (rw rho2 106) in *.
    2,3: rewrite <- ?(proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)), ?V5; unfold N0; lia.
    rewrite <- (proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)), V5, U106 in Hf.
    exists (rho_sub rho2 (s_PAg_Dg r)). split.
    { apply GoodW_sub; [destruct r; reflexivity|]. eapply GoodW_agree; [exact Hag2 | destruct r; cbn; lia | exact HGW1]. }
    eapply SP_entails in Hw; [|exact (ent_PAg_Dg r)].
    replace (length MSG) with k; [exact Hw|]. unfold N0 in Hf. lia.
Qed.

Lemma cert_exitg : forall r : bool, (((instr_at segs (ss_pc (E_exitg r))) = (Some Ecall)) /\ (((reg_sv (E_exitg r) 17%Z) = (SLit 94%Z)) /\ ((reg_sv (E_exitg r) 10%Z) = (SLit 2%Z)))).
Proof using . intros [|]; vm_compute; repeat split; reflexivity. Qed.

Lemma L_exitg : forall r : bool, (forall (rho : valuation), ((GoodW rho) -> (triple segs ok (SP segs (Kx (TR (length MSG)) md0) (Dg r) rho) (fun (x : world) => False)))).
Proof using Hargc Hfs HokK HokP Hokh.
  intros r rho HG. eapply run_tr; [exact (run_Dg r) | destruct r; reflexivity | apply okf |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  destruct (cert_exitg r) as (Hi & H17 & H10).
  apply (SysNA.triple_exit_eval_na segs ok SpecT (Kx (TR (length MSG)) md0) (E_exitg r) rho1 2);
    [apply okf | apply okp | exact Hokh | exact Hi | left; exact H17 | rewrite H10; rewrite U_lit64 by lia; reflexivity |].
  intros tr md [-> ->]. rewrite TR_all by lia. rewrite Hfs. exact final_in_spec.
Qed.

Theorem usage_small_safe : (((length argv0) <= 66%nat)%nat -> (((check_core rq N0 (sym_run segs FUELn [] (Tn rq N0) true)) = true) -> (forall (rho : valuation), ((JI rho) -> (triple segs ok (SP segs (Kx [] md0) (S_main rq) rho) (fun (x : world) => False)))))).
Proof using Hargc Hent Hfd2 Hrdr0 Hfs Hinp HokK HokP Hokh LEN STR.
  intros Hsmall Hchk rho HJ.
  destruct (check_core_sound rq N0 _ Hchk) as (a & ws & Hwf & _).
  eapply triple_conseq with (P := fun w => exists rho', Good rho' /\ SP segs (Kx (TR 0) md0) (S_use rq) rho' w); [| intros w Hw; exact Hw |].
  { intros w Hw. apply (use_intro rho w HJ). exact Hw. }
  apply triple_ex; intros rho1. apply triple_pure; intros HG1.
  eapply triple_seq.
  { eapply run_tr; [exact (run_use rq) | unfold rq; destruct (kb_rseq (in_kernel inp)); reflexivity | apply okf |].
    intros L rho2 [<-|[]] Hag2. cbn [lf_state].
    pose proof (Good_agree _ _ _ Hag2 ltac:(unfold rq; destruct (kb_rseq (in_kernel inp)); cbn; lia) HG1) as HG2.
    apply (call_path segs FirstNul ok (Kx (TR 0) md0) (Kx (TR 0) md0) (E_sn rq) (E_snX rq) Pre_strnlen xs_pre (s_sn rq) (R_sn rq) Posts_strnlen _ rho2
             (xs_pre_ok rq) (efr_sn rq) (chk_sn rq) (fb_sn rq)).
    - intros rho3 HF. apply strnlen_sum; [apply okf | exact HF].
    - intros ms _. apply (FirstNul_call rq). exact HG2.
    - intros L rho3 [<-|[]] Hag3 HF3. cbn [lf_state]. replace (ss_next Pre_strnlen) with NF by reflexivity. rewrite (T_imp_eq rq).
      pose proof (Good_agree _ _ _ Hag3 ltac:(unfold rq; destruct (kb_rseq (in_kernel inp)); cbn; lia) HG2) as HG3.
      apply (post_path segs ok (Kx (TR 0) md0) (T_imp rq) (T_sn rq) (ss_facts (E_sn rq)) xs_post rho3 _ (fb_sn2 rq) (xs_post_ok rq) HF3).
      apply triple_facts. intros HFT.
      eapply triple_conseq with (P := SP segs (Kx (TR 0) md0) (Tn rq N0) rho3); [| intros w Hw; exact Hw | apply (L_small_pre rq N0 Hchk eq_refl); exact HG3].
      intros w Hsp. apply (Tn_intro rq N0 rho3 w HG3 eq_refl Hwf).
      eapply (SP_restate segs _ rho3 (T_sn rq) (T_sn1 rq) w); [exact (swf_T_sn1 rq) | exact (diff_sn rq) | | constructor | exact Hsp].
      constructor; [|constructor]. cbn [fst snd]. exact (proj1 (Forall_forall _ _) HFT _ (fact_T_sn rq)). }
  apply triple_ex; intros rho4. apply triple_pure; intros HG4.
  eapply triple_seq; [apply (L_Wg rq Hsmall); exact HG4|].
  apply triple_ex; intros rho5. apply triple_pure; intros HG5.
  apply (L_exitg rq). exact HG5.
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
  replace (map (fun x : nat => nth (Z.to_nat (Z.of_nat x)) (strs_tail inp) (Z_to_bv 8 0)) (seq 0 (length argv0)))
    with (map (fun j : nat => nth j (strs_tail inp) (Z_to_bv 8 0)) (seq 0 (length argv0)))
    by (apply map_ext; intros j; rewrite Nat2Z.id; reflexivity).
  rewrite (map_nth_seq (strs_tail inp) (length argv0) (Z_to_bv 8 0)) by (pose proof tail_len; pose proof NU; lia).
  rewrite tail_firstn. reflexivity.
Qed.

(* As [check_wleaf_sound] and [check_core_sound], for the middle range. *)
Lemma check_wleaf_m_sound : forall (r : bool) (n : Z) (w : sstate), check_wleaf_m r n w = true ->
  exists (wx : sstate) (o : sobj) (bl : list bexp),
    apply_xforms w (xs_ibuf2 n) = Some wx /\ nth_error (ss_objs wx) 1%nat = Some o /\
    ob_lo o = SLit (-560) /\ ob_hi o = SLit (n - 553) /\
    dflt_writable (ob_dflt o) = true /\ is_arr (ob_dflt o) = false /\
    cells_bytes (ob_cells o) (SLit (-560)) 0 (Z.to_nat (7 + n)) = Some bl /\
    list_eqb bexp_eqb bl (BLm n) = true /\ state_has_rl 4%positive wx = false /\
    entails (obj_to_list wx 1%nat 4%positive) (E_Mg r)
      ((5%positive, SLit n) :: infer_sub GLm (obj_to_list wx 1%nat 4%positive) (E_Mg r)) = true /\
    sub_ok_n ((5%positive, SLit n) :: infer_sub GLm (obj_to_list wx 1%nat 4%positive) (E_Mg r)) n = true.
Proof using .
  intros r n w H. unfold check_wleaf_m in H. cbv zeta in H.
  destruct (apply_xforms w (xs_ibuf2 n)) as [wx|] eqn:Ex; [|discriminate].
  apply andb_prop in H as [H4 H7]. apply andb_prop in H4 as [H4 H6].
  destruct (nth_error (ss_objs wx) 1) as [o|] eqn:Eo; [|discriminate].
  apply andb_prop in H4 as [H4 Hcb]. apply andb_prop in H4 as [H4 Harr]. apply andb_prop in H4 as [H4 Hwr]. apply andb_prop in H4 as [Hlo Hhi].
  destruct (cells_bytes (ob_cells o) (SLit (-560)) 0 (Z.to_nat (7 + n))) as [bl|] eqn:Ecb; [|discriminate].
  apply andb_prop in H7 as [He Hs].
  exists wx, o, bl. repeat split; auto.
  - apply sv_eqb_sound in Hlo. exact Hlo.
  - apply sv_eqb_sound in Hhi. exact Hhi.
  - destruct (is_arr (ob_dflt o)); [discriminate|reflexivity].
  - destruct (state_has_rl 4 wx); [discriminate|reflexivity].
Qed.

Lemma check_core_m_sound : forall (r : bool) (n : Z) (r1 : option (list leaf)), check_core_m r n r1 = true ->
  exists (a : leaf) (ws : list leaf),
    swf (Tn r n) = true /\ r1 = Some (a :: ws) /\ In (BNZ3 (SLit n)) (ss_facts (lf_state a)) /\
    Forall (fun b : leaf =>
      exists (wx : sstate) (o : sobj) (bl : list bexp),
        apply_xforms (lf_state b) (xs_ibuf2 n) = Some wx /\ nth_error (ss_objs wx) 1%nat = Some o /\
        ob_lo o = SLit (-560) /\ ob_hi o = SLit (n - 553) /\
        dflt_writable (ob_dflt o) = true /\ is_arr (ob_dflt o) = false /\
        cells_bytes (ob_cells o) (SLit (-560)) 0 (Z.to_nat (7 + n)) = Some bl /\
        list_eqb bexp_eqb bl (BLm n) = true /\ state_has_rl 4%positive wx = false /\
        entails (obj_to_list wx 1%nat 4%positive) (E_Mg r)
          ((5%positive, SLit n) :: infer_sub GLm (obj_to_list wx 1%nat 4%positive) (E_Mg r)) = true /\
        sub_ok_n ((5%positive, SLit n) :: infer_sub GLm (obj_to_list wx 1%nat 4%positive) (E_Mg r)) n = true) ws.
Proof using .
  intros r n r1 H. unfold check_core_m in H.
  apply andb_prop in H as [H1 H2].
  destruct r1 as [[|a [|b ws]]|]; cbv beta iota zeta in H2; try discriminate.
  apply andb_prop in H2 as [H3 H4].
  apply existsb_exists in H3 as (p & Hp & Ep). apply sprop_eqb_sound in Ep. subst p.
  exists a, (b :: ws). split; [exact H1|]. split; [reflexivity|]. split; [exact Hp|].
  apply Forall_forall. intros l Hl. apply check_wleaf_m_sound.
  exact (proj1 (forallb_forall _ _) H4 l Hl).
Qed.

Lemma mid_leaf_out : forall r : bool, (forall (n : Z), (forall (rho1 : valuation), (forall (b : leaf), (forall (wx : sstate), (forall (o : sobj), (forall (bl : (list bexp)), (forall (w : world), ((Good rho1) -> ((N0 = n) -> (((apply_xforms (lf_state b) (xs_ibuf2 n)) = (Some wx)) -> (((nth_error (ss_objs wx) 1%nat) = (Some o)) -> (((ob_lo o) = (SLit (-560)%Z)) -> (((ob_hi o) = (SLit (Z.sub n 553%Z))) -> (((dflt_writable (ob_dflt o)) = true) -> (((is_arr (ob_dflt o)) = false) -> (((cells_bytes (ob_cells o) (SLit (-560)%Z) 0%Z (Z.to_nat (Z.add 7%Z n))) = (Some bl)) -> (((list_eqb bexp_eqb bl (BLm n)) = true) -> (((state_has_rl 4%positive wx) = false) -> (((entails (obj_to_list wx 1%nat 4%positive) (E_Mg r) (cons (pair 5%positive (SLit n)) (infer_sub GLm (obj_to_list wx 1%nat 4%positive) (E_Mg r)))) = true) -> (((sub_ok_n (cons (pair 5%positive (SLit n)) (infer_sub GLm (obj_to_list wx 1%nat 4%positive) (E_Mg r))) n) = true) -> ((SP segs (Kx (TR 0%nat) md0) (lf_state b) rho1 w) -> (QM_at (E_Mg r) 0%nat w)))))))))))))))))))))).
Proof using Hargc Hent Hinp.
  intros r n rho1 b wx o bl w HG1 Hn Hx Ho Hlo Hhi Hwr Harr Hcb Hbl Hrl He Hs [Hsm Hk]. pose proof NU as NU'.
  pose proof (smatch_xforms segs _ _ _ _ w Hx Hsm) as Hsm2.
  pose proof (smatch_obj_to_list segs rho1 wx w 1 4 o (-560) (n - 553) bl Hsm2 Ho Hlo Hhi ltac:(lia) ltac:(unfold N0 in Hn; lia) Hwr Harr) as Hsm3.
  replace (n - 553 - -560) with (7 + n) in Hsm3 by lia. specialize (Hsm3 Hcb Hrl).
  set (rho2 := rho_set_rl rho1 4 (map (beval rho1) bl)) in Hsm3.
  set (sW := (5%positive, SLit n) :: infer_sub GLm (obj_to_list wx 1 4) (E_Mg r)) in He, Hs.
  exists (rho_sub rho2 sW). split.
  + assert (HG2 : Good rho2).
    { destruct HG1 as (HJ & H3 & H25). subst rho2. split; [|split; [cbn; exact H3 | cbn; exact H25]].
      destruct HJ; constructor; cbn [rho_set_rl rw rl rm]; auto. }
    unfold sub_ok_n in Hs. apply andb_prop in Hs as [Hs6 Hs5]. apply sv_eqb_sound in Hs5.
    cbn [forallb] in Hs6.
    apply andb_prop in Hs6 as [E1 Hs6]. apply andb_prop in Hs6 as [E2 Hs6]. apply andb_prop in Hs6 as [E3 Hs6].
    apply andb_prop in Hs6 as [E4 Hs6]. apply andb_prop in Hs6 as [E6 Hs6]. apply andb_prop in Hs6 as [E25 Hs6].
      apply andb_prop in Hs6 as [E7 Hs6]. apply andb_prop in Hs6 as [E8 Hs6]. apply andb_prop in Hs6 as [E9 Hs6]. apply andb_prop in Hs6 as [E10 Hs6].
      apply andb_prop in Hs6 as [E13 _].
      apply sv_eqb_sound in E7. apply sv_eqb_sound in E8. apply sv_eqb_sound in E9. apply sv_eqb_sound in E10. apply sv_eqb_sound in E13.
    apply sv_eqb_sound in E1. apply sv_eqb_sound in E2. apply sv_eqb_sound in E3.
    apply sv_eqb_sound in E4. apply sv_eqb_sound in E6. apply sv_eqb_sound in E25.
    split.
    * destruct HG2 as (HJ & H3 & H25). split; [|split; [cbn; exact H3 | cbn [rho_sub rw]; rewrite E25; cbn [eval]; exact H25]].
      destruct HJ; constructor; cbn [rho_sub rw rl rm]; rewrite ?E1, ?E2, ?E3, ?E4, ?E6, ?E7, ?E8, ?E9, ?E10, ?E13, ?Hs5; cbn [eval]; auto.
      rewrite <- Hn. reflexivity.
    * cbn [rho_sub rl]. subst rho2. cbn [rho_set_rl rl]. rewrite Pos.eqb_refl.
      rewrite (list_bexp_eqb_beval rho1 _ _ Hbl). subst n. apply BLm_eval. exact HG1.
  + split; [|exact Hk]. eapply entails_sound; [exact He | exact Hsm3].
Qed.

Lemma L_mid_pre : forall r : bool, (forall (n : Z), (((check_core_m r n (sym_run segs FUELn [] (Tn r n) true)) = true) -> ((N0 = n) -> (forall (rho : valuation), ((Good rho) -> (triple segs ok (SP segs (Kx (TR 0%nat) md0) (Tn r n) rho) (QM_at (E_Mg r) 0%nat))))))).
Proof using Hargc Hent Hinp HokK.
  intros r n Hchk Hn rho HG. pose proof NU as NU'.
  destruct (check_core_m_sound r n _ Hchk) as (a & ws & Hwf & Hr & HinX & Hws).
  eapply run_tr; [exact Hr | destruct r; reflexivity | apply okf |].
  intros L rho1 [<-|HL] Hag1.
  - intros m Hg w Hw. exfalso.
    pose proof (SP_fact _ _ _ _ _ Hw HinX) as Hf. unfold BNZ3 in Hf. apply (proj1 (holds_BNZ rho1 (SLit n))) in Hf.
    apply Hf. rewrite <- (proj1 (proj2 Hag1)), (G_rl3 rho HG). rewrite U_lit64 by lia.
    unfold nthb. subst n. unfold N0. rewrite Nat2Z.id, tail_nul. reflexivity.
  - destruct (proj1 (Forall_forall _ _) Hws L HL) as (wx & o & bl & Hx & Ho & Hlo & Hhi & Hwr & Harr & Hcb & Hbl & Hrl & He & Hs).
    pose proof (Good_agree _ _ _ Hag1 ltac:(unfold Tn; destruct r; cbn; lia) HG) as HG1.
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. exact (mid_leaf_out r n rho1 L wx o bl w HG1 Hn Hx Ho Hlo Hhi Hwr Harr Hcb Hbl Hrl He Hs Hw).
Qed.


Definition OB_ibuf2 : sobj := ltac2:(tb__ "0|0|
S1dSdP1A1S6N230A1SaS73SdP5A1S6Zfffffffffffffdd7A1A3S35S9A1S1cP4A1A5").

Lemma cert_E_Mg : forall r : bool, (((obj_rng (ob0 (E_Mg r))) = (pair (pair (SVar 1%positive) (SLit (Z.opp STK_FREE))) (SLit (-560)%Z))) /\ (((ob1 (E_Mg r)) = OB_ibuf2) /\ ((2%nat <= (length (ss_objs (E_Mg r))))%nat /\ (((existsb (cell_eqb (mkCell (SLit (-1224)%Z) 8%Z (SAlu ALU_ADD (SVar 1%positive) (SLit (-560)%Z)))) (ob_cells (ob0 (E_Mg r)))) = true) /\ (((existsb (cell_eqb (mkCell (SLit (-1216)%Z) 8%Z (SAlu ALU_ADD (SVar 5%positive) (SLit 7%Z)))) (ob_cells (ob0 (E_Mg r)))) = true) /\ (((existsb (cell_eqb (mkCell (SLit (-1208)%Z) 8%Z (SLit RO_INPUT))) (ob_cells (ob0 (E_Mg r)))) = true) /\ (((existsb (cell_eqb (mkCell (SLit (-1200)%Z) 8%Z (SLit 7%Z))) (ob_cells (ob0 (E_Mg r)))) = true) /\ (((reg_sv (E_Mg r) 11%Z) = (SAlu ALU_ADD (SVar 1%positive) (SLit (-1224)%Z))) /\ (((reg_sv (E_Mg r) 22%Z) = (SAlu ALU_ADD (SVar 5%positive) (SLit 14%Z))) /\ (((instr_at segs (ss_pc (E_Mg r))) = (Some Ecall)) /\ (((reg_sv (E_Mg r) 17%Z) = (SLit 66%Z)) /\ (((reg_sv (E_Mg r) 10%Z) = (SLit 2%Z)) /\ (((reg_sv (E_Mg r) 12%Z) = (SLit 2%Z)) /\ (((ss_next (E_Mg r)) = 106%positive) /\ ((In (SPUle (SLit 67%Z) (SVar 5%positive)) (ss_facts (E_Mg r))) /\ (In (SPUle (SVar 5%positive) (SLit 73%Z)) (ss_facts (E_Mg r)))))))))))))))))).
Proof using Hargc LEN N0 STR. intros [|]; vm_compute; repeat split; (reflexivity || lia || (cbn; tauto)). Qed.

Lemma cert_CB2m : forall r : bool, (((obj_rng (ob0 (CB2m r))) = (pair (pair (SVar 1%positive) (SLit (Z.opp STK_FREE))) (SLit (-560)%Z))) /\ (((ob1 (CB2m r)) = OB_ibuf2) /\ ((2%nat <= (length (ss_objs (CB2m r))))%nat /\ (((existsb (cell_eqb (mkCell (SLit (-1224)%Z) 8%Z (SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_ADD (SVar 1%positive) (SLit (-553)%Z)) (SVar 5%positive)) (SVar 106%positive)))) (ob_cells (ob0 (CB2m r)))) = true) /\ (((existsb (cell_eqb (mkCell (SLit (-1216)%Z) 8%Z (SVar 106%positive))) (ob_cells (ob0 (CB2m r)))) = true) /\ (((existsb (cell_eqb (mkCell (SLit (-1208)%Z) 8%Z (SLit RO_INPUT))) (ob_cells (ob0 (CB2m r)))) = true) /\ (((existsb (cell_eqb (mkCell (SLit (-1200)%Z) 8%Z (SLit 7%Z))) (ob_cells (ob0 (CB2m r)))) = true) /\ (((reg_sv (CB2m r) 11%Z) = (SAlu ALU_ADD (SVar 1%positive) (SLit (-1224)%Z))) /\ (((reg_sv (CB2m r) 22%Z) = (SAlu ALU_ADD (SVar 106%positive) (SLit 7%Z))) /\ (((instr_at segs (ss_pc (CB2m r))) = (Some Ecall)) /\ (((reg_sv (CB2m r) 17%Z) = (SLit 66%Z)) /\ (((reg_sv (CB2m r) 10%Z) = (SLit 2%Z)) /\ (((reg_sv (CB2m r) 12%Z) = (SLit 2%Z)) /\ (((ss_next (CB2m r)) = 109%positive) /\ ((In (SPUle (SVar 106%positive) (SAlu ALU_ADD (SVar 5%positive) (SLit 6%Z))) (ss_facts (CB2m r))) /\ ((In (SPUle (SLit 67%Z) (SVar 5%positive)) (ss_facts (CB2m r))) /\ (In (SPUle (SVar 5%positive) (SLit 73%Z)) (ss_facts (CB2m r))))))))))))))))))).
Proof using Hargc LEN N0 STR. intros [|]; vm_compute; repeat split; (reflexivity || lia || (cbn; tauto)). Qed.

Lemma cert_CB1m : forall r : bool, (((obj_rng (ob0 (CB1m r))) = (pair (pair (SVar 1%positive) (SLit (Z.opp STK_FREE))) (SLit (-560)%Z))) /\ ((2%nat <= (length (ss_objs (CB1m r))))%nat /\ (((existsb (cell_eqb (mkCell (SLit (-1208)%Z) 8%Z (SAlu ALU_SUB (SLit (Z.add RO_INPUT 7%Z)) (SVar 106%positive)))) (ob_cells (ob0 (CB1m r)))) = true) /\ (((existsb (cell_eqb (mkCell (SLit (-1200)%Z) 8%Z (SVar 106%positive))) (ob_cells (ob0 (CB1m r)))) = true) /\ (((reg_sv (CB1m r) 11%Z) = (SAlu ALU_ADD (SVar 1%positive) (SLit (-1208)%Z))) /\ (((reg_sv (CB1m r) 22%Z) = (SVar 106%positive)) /\ (((instr_at segs (ss_pc (CB1m r))) = (Some Ecall)) /\ (((reg_sv (CB1m r) 17%Z) = (SLit 66%Z)) /\ (((reg_sv (CB1m r) 10%Z) = (SLit 2%Z)) /\ (((reg_sv (CB1m r) 12%Z) = (SLit 1%Z)) /\ (((ss_next (CB1m r)) = 110%positive) /\ ((In (SPUle (SLit 1%Z) (SVar 106%positive)) (ss_facts (CB1m r))) /\ (In (SPUle (SVar 106%positive) (SLit 6%Z)) (ss_facts (CB1m r))))))))))))))).
Proof using Hargc LEN N0 STR. intros [|]; vm_compute; repeat split; (reflexivity || lia || (cbn; tauto)). Qed.

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
Proof using Hargc. clear STR LEN. intros d Hd. unfold MSG. rewrite skipn_app. replace (d - length M1)%nat with 0%nat by lia. reflexivity. Qed.

Lemma bytes_E_Mg : forall r rho tr ms md, GoodM rho -> (67 <= length argv0 <= 73)%nat -> smatch_pending segs rho (E_Mg r) (tr, mkCfg ms md) ->
  exists b1 l1 b2 l2,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv (E_Mg r) 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (E_Mg r) 11) + 8)%bv = Some l1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (E_Mg r) 11) + 16)%bv = Some b2
    /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv (E_Mg r) 11) + 16) + 8)%bv = Some l2
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some M1
    /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some M2
    /\ bv_unsigned (eval rho (reg_sv (E_Mg r) 22)) = Z.of_nat (length (M1 ++ M2))
    /\ (bv_unsigned (eval rho (reg_sv (E_Mg r) 11)) + 32 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
    /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros r rho tr ms md HGM Hmid Hsp. pose proof (proj1 HGM) as HG. pose proof NU as NU'. pose proof RO_INPUT_range.
  destruct (cert_E_Mg r) as (Hrng & Hob1 & Hlen & C1 & C2 & C3 & C4 & R11 & R22 & _).
  rewrite R11, R22. pose proof (G_v1 rho HG) as V1. pose proof (G_v5 rho HG) as V5.
  assert (A0 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-1224)))) = bv_unsigned sp - 1224).
  { erewrite U_addc; [reflexivity | exact V1 | lia | lia]. }
  assert (A16 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-1224))) + 16)%bv = bv_unsigned sp - 1208).
  { rewrite (U_bvadd _ _ _ _ A0 u16) by lia. lia. }
  exists (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-560)))), (eval rho (SAlu ALU_ADD (SVar 5) (SLit 7))), (eval rho (SLit RO_INPUT)), (eval rho (SLit 7)).
  apply and7_tail; [tsz|].
  split; [eapply (iov_field_lo rho (E_Mg r) tr ms md (-1224)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field_lo rho (E_Mg r) tr ms md (-1216)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split; [eapply (iov_field_lo rho (E_Mg r) tr ms md (-1208)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C3 | lia | lia]|].
  split; [eapply (iov_field_lo rho (E_Mg r) tr ms md (-1200)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C4 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
  split.
  { rewrite <- (firstn_all M1), <- (skipn_O M1). change 0%nat with (Z.to_nat 0).
    apply (ibuf2_read rho (E_Mg r) tr ms md 0 (length M1)); [exact HGM | exact Hsp | exact Hlen | exact Hob1 | exact Hmid | lia | rewrite M1_len; unfold N0; lia | |].
    - erewrite U_addc; [| exact V1 | lia | lia]. lia.
    - erewrite U_addc; [| exact V5 | unfold N0; lia | lia]. rewrite M1_len. unfold N0. lia. }
  split.
  { apply (read_bytes_map_of_rd ms _ _ 7); [change (Z.of_nat 7) with 7; apply U_lit64; lia|].
    cbn [eval]. eapply ro_input. exact Hsp. }
  erewrite U_addc; [| exact V5 | unfold N0; lia | lia]. rewrite length_app, M1_len, M2_len. unfold N0. lia.
Qed.

Lemma bytes_CB2m : forall r rho tr ms md, GoodM rho -> (67 <= length argv0 <= 73)%nat -> smatch_pending segs rho (CB2m r) (tr, mkCfg ms md) ->
  let L0 := Z.to_nat (bv_unsigned (rw rho 106)) in
  (L0 <= 6 + length argv0)%nat /\
  exists b1 l1 b2 l2,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv (CB2m r) 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (CB2m r) 11) + 8)%bv = Some l1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (CB2m r) 11) + 16)%bv = Some b2
    /\ read_u64 (ms_read_byte ms) ((eval rho (reg_sv (CB2m r) 11) + 16) + 8)%bv = Some l2
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some (skipn (length M1 - L0) M1)
    /\ read_bytes_map (ms_read_byte ms) b2 l2 = Some M2
    /\ bv_unsigned (eval rho (reg_sv (CB2m r) 22)) = Z.of_nat (length (skipn (length M1 - L0) M1 ++ M2))
    /\ (bv_unsigned (eval rho (reg_sv (CB2m r) 11)) + 32 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z
    /\ (bv_unsigned b2 + bv_unsigned l2 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros r rho tr ms md HGM Hmid Hsp. pose proof (proj1 HGM) as HG. pose proof NU as NU'. pose proof RO_INPUT_range.
  destruct (cert_CB2m r) as (Hrng & Hob1 & Hlen & C1 & C2 & C3 & C4 & R11 & R22 & _ & _ & _ & _ & _ & HinF & _).
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
  split; [eapply (iov_field_lo rho (CB2m r) tr ms md (-1224)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field_lo rho (CB2m r) tr ms md (-1216)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split; [eapply (iov_field_lo rho (CB2m r) tr ms md (-1208)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C3 | lia | lia]|].
  split; [eapply (iov_field_lo rho (CB2m r) tr ms md (-1200)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C4 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
  split.
  { replace (skipn (length M1 - L0) M1) with (firstn L0 (skipn (Z.to_nat (Z.of_nat (length M1 - L0))) M1)).
    2:{ rewrite Nat2Z.id. rewrite firstn_all2; [reflexivity|]. rewrite length_skipn. lia. }
    apply (ibuf2_read rho (CB2m r) tr ms md (Z.of_nat (length M1 - L0)) L0); [exact HGM | exact Hsp | exact Hlen | exact Hob1 | exact Hmid | lia | rewrite ML; unfold N0; lia | | subst L0; change (eval rho (SVar 106)) with (rw rho 106); lia].
    erewrite (U_sub2 rho _ _ (bv_unsigned sp - 553 + N0) (bv_unsigned (rw rho 106))); [rewrite ML; subst L0; unfold N0 in *; lia | | reflexivity | unfold N0 in *; lia].
    erewrite (U_add2 rho _ _ (bv_unsigned sp - 553) N0); [lia | | exact V5 | unfold N0 in *; lia].
    apply (U_addc rho (SVar 1) (-553) (bv_unsigned sp)); [exact V1 | lia | lia]. }
  split.
  { apply (read_bytes_map_of_rd ms _ _ 7); [change (Z.of_nat 7) with 7; apply U_lit64; lia|].
    cbn [eval]. eapply ro_input. exact Hsp. }
  erewrite U_addc; [| reflexivity | change (eval rho (SVar 106)) with (rw rho 106); lia | lia].
  change (eval rho (SVar 106)) with (rw rho 106). rewrite length_app, length_skipn, M2_len. subst L0. lia.
Qed.

Lemma bytes_CB1m : forall r rho tr ms md, GoodM rho -> smatch_pending segs rho (CB1m r) (tr, mkCfg ms md) ->
  let R := Z.to_nat (bv_unsigned (rw rho 106)) in
  (1 <= R <= 6)%nat /\
  exists b1 l1,
    read_u64 (ms_read_byte ms) (eval rho (reg_sv (CB1m r) 11)) = Some b1
    /\ read_u64 (ms_read_byte ms) (eval rho (reg_sv (CB1m r) 11) + 8)%bv = Some l1
    /\ read_bytes_map (ms_read_byte ms) b1 l1 = Some (skipn (7 - R) M2)
    /\ bv_unsigned (eval rho (reg_sv (CB1m r) 22)) = Z.of_nat (length (skipn (7 - R) M2))
    /\ (bv_unsigned (eval rho (reg_sv (CB1m r) 11)) + 16 <= TASK_SIZE)%Z
    /\ (bv_unsigned b1 + bv_unsigned l1 <= TASK_SIZE)%Z.
Proof using Hargc Hent Hinp.
  intros r rho tr ms md HGM Hsp. pose proof (proj1 HGM) as HG. pose proof NU as NU'. pose proof RO_INPUT_range.
  destruct (cert_CB1m r) as (Hrng & Hlen & C1 & C2 & R11 & R22 & _ & _ & _ & _ & _ & HinF1 & HinF2).
  pose proof (G_v1 rho HG) as V1.
  pose proof (SPp_fact _ _ _ _ _ _ Hsp HinF1) as HL1. cbn [holds] in HL1. rewrite U_lit64 in HL1 by lia.
  pose proof (SPp_fact _ _ _ _ _ _ Hsp HinF2) as HL2. cbn [holds] in HL2. rewrite U_lit64 in HL2 by lia.
  change (eval rho (SVar 106)) with (rw rho 106) in HL1, HL2.
  intros R. split; [subst R; lia|]. rewrite R11, R22.
  assert (A0 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SLit (-1208)))) = bv_unsigned sp - 1208).
  { erewrite U_addc; [reflexivity | exact V1 | lia | lia]. }
  exists (eval rho (SAlu ALU_SUB (SLit (RO_INPUT + 7)) (SVar 106))), (eval rho (SVar 106)).
  apply and4_tail; [tsz|].
  split; [eapply (iov_field_lo rho (CB1m r) tr ms md (-1208)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia]|].
  split; [eapply (iov_field_lo rho (CB1m r) tr ms md (-1200)); [exact HG | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
  split.
  { apply (read_bytes_map_of_rd ms _ _ R); [subst R; change (eval rho (SVar 106)) with (rw rho 106); lia|].
    replace (eval rho (SAlu ALU_SUB (SLit (RO_INPUT + 7)) (SVar 106))) with (Z_to_bv 64 RO_INPUT + Z_to_bv 64 (Z.of_nat (7 - R)))%bv.
    - apply rd_bytes_skip. replace (7 - R + R)%nat with 7%nat by lia. eapply ro_input. exact Hsp.
    - apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite mod64, <- Z.add_mod, !Z.mod_small by lia.
      symmetry. erewrite (U_sub2 rho _ _ (RO_INPUT + 7) (bv_unsigned (rw rho 106))); [lia | apply U_lit64; lia | reflexivity | lia]. }
  change (eval rho (SVar 106)) with (rw rho 106). rewrite length_skipn, M2_len. subst R. lia.
Qed.

Definition L0m (rho : valuation) : nat := Z.to_nat (bv_unsigned (rw rho 106)).
Definition QDm (r : bool) : assn := QM_at (Dm r) (length MSG).

Lemma loopm : forall r : bool, (((67%nat <= (length argv0))%nat /\ ((length argv0) <= 73%nat)%nat) -> (forall (m : nat), ((forall (rho : valuation), ((GoodM rho) -> (((L0m rho) <= (Nat.add 6%nat (length argv0)))%nat -> (((Nat.add (L0m rho) 7%nat) <= m)%nat -> (triple segs ok (SP segs (Kx (TR (Nat.sub (length M1) (L0m rho))) md0) (CB2m r) rho) (QDm r)))))) /\ (forall (rho : valuation), ((GoodM rho) -> (((1%nat <= (L0m rho))%nat /\ ((L0m rho) <= 6%nat)%nat) -> (((L0m rho) <= m)%nat -> (triple segs ok (SP segs (Kx (TR (Nat.sub (length MSG) (L0m rho))) md0) (CB1m r) rho) (QDm r))))))))).
Proof using Hargc Hent Hfd2 Hrdr0 Hinp HokK HokP.
  intros r Hmid. induction m as [|m IH].
  { split; intros rho HG H1 H2; exfalso; lia. }
  destruct IH as [IH2 IH1]. pose proof NU as NU'. pose proof M1_len as ML. pose proof MSG_len as MSL.
  destruct (cert_CB2m r) as (_ & _ & _ & _ & _ & _ & _ & _ & R22b & Hib & H17b & H10b & H12b & Hnxb & _).
  destruct (cert_CB1m r) as (_ & _ & _ & _ & _ & R22c & Hic & H17c & H10c & H12c & Hnxc & _).
  split.
  -
    intros rho HGM HL0 Hm. pose proof (proj1 HGM) as HG.
    assert (HU : bv_unsigned (rw rho 106) = Z.of_nat (L0m rho)) by (unfold L0m; pose proof (urange (rw rho 106)); lia).
    eapply triple_seq.
    { apply (writev_site2 (CB2m r) (reg_sv (CB2m r) 22) (length M1 - L0m rho) (skipn (length M1 - L0m rho) M1) M2 rho HG);
        [rewrite Hnxb; lia | exact Hib | exact H17b | exact H10b | exact H12b | rewrite R22b, Hnxb; reflexivity | | |].
      + rewrite MSG_skipM1 by lia. rewrite firstn_all. reflexivity.
      + rewrite length_app, length_skipn, M2_len. unfold MAX_RW_COUNT. lia.
      + intros tr ms md Hsp. exact (proj2 (bytes_CB2m r rho tr ms md HGM Hmid Hsp)). }
    apply triple_ex; intros rho1. apply triple_ex; intros k.
    apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
    rewrite Hnxb in Hk, Hag1. rewrite length_app, length_skipn, M2_len in Hkb.
    assert (HGM1 : GoodM rho1) by (split; [exact HG1 | rewrite <- (proj1 (proj2 Hag1)); exact (proj2 HGM)]).
    assert (E106 : rw rho1 106 = rw rho 106) by (symmetry; apply (proj1 Hag1); lia).
    assert (U109 : bv_unsigned (rw rho1 109) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
    eapply triple_conseq with (P := SP segs (Kx (TR (length M1 - L0m rho + k)) md0) (PB2m r) rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. apply SP_add1; [exact Hw | | destruct r; reflexivity]. cbn [holds]. change (eval rho1 (SVar 109)) with (rw rho1 109). rewrite U109, U_lit64 by lia. lia. }
    destruct (Nat.le_gt_cases k (L0m rho)) as [Hle|Hgt].
    + eapply triple_conseq with (P := SP segs (Kx (TR (length M1 - L0m rho + k)) md0) (PB2ma r) rho1); [| intros w Hw; exact Hw |].
      { intros w Hw. apply SP_add1; [exact Hw | | destruct r; reflexivity]. cbn [holds]. change (eval rho1 (SVar 109)) with (rw rho1 109).
        change (eval rho1 (SVar 106)) with (rw rho1 106). rewrite U109, E106, HU. lia. }
      eapply run_tr; [exact (run_PB2ma r) | destruct r; reflexivity | apply okf |].
      intros L rho2 [<-|[]] Hag2. cbn [lf_state].
      assert (EL : L0m (rho_sub rho2 (s_PB2ma_CB2m r)) = (L0m rho - k)%nat).
      { unfold L0m at 1. cbn [rho_sub rw]. rewrite (sv_PB2ma r).
        erewrite U_sub2; [| reflexivity | reflexivity |]; change (eval rho2 (SVar 106)) with (rw rho2 106); change (eval rho2 (SVar 109)) with (rw rho2 109);
          rewrite <- (proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 109%positive ltac:(destruct r; cbn; lia)), E106, U109, HU; lia. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH2 (rho_sub rho2 (s_PB2ma_CB2m r)))].
      * intros w Hw. eapply SP_entails in Hw; [|exact (ent_PB2ma_CB2m r)].
        replace (length M1 - L0m (rho_sub rho2 (s_PB2ma_CB2m r)))%nat with (length M1 - L0m rho + k)%nat by lia. exact Hw.
      * apply GoodM_sub; [destruct r; reflexivity|]. eapply GoodM_agree; [exact Hag2 | destruct r; cbn; lia | exact HGM1].
      * lia.
      * lia.
    + eapply triple_conseq with (P := SP segs (Kx (TR (length M1 - L0m rho + k)) md0) (PB2mb r) rho1); [| intros w Hw; exact Hw |].
      { intros w Hw. apply SP_add1; [exact Hw | | destruct r; reflexivity]. cbn [holds]. change (eval rho1 (SVar 109)) with (rw rho1 109).
        erewrite U_addc; [| reflexivity | |]; change (eval rho1 (SVar 106)) with (rw rho1 106); rewrite ?U109, ?E106, ?HU; lia. }
      eapply run_tr; [exact (run_PB2mb r) | destruct r; reflexivity | apply okf |].
      intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
      *
        eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
        intros w Hw. pose proof (hd_fact_r rho2 L_PB2mb_0 r w _ Hw _ _ _ eq_refl eq_refl) as Hf.
        cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
        erewrite (U_addc rho2 (SVar 106) 7) in Hf; [| reflexivity | |];
          change (eval rho2 (SVar 106)) with (rw rho2 106) in *; change (eval rho2 (SVar 109)) with (rw rho2 109) in *.
        2,3: rewrite <- ?(proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)), ?E106, ?HU; lia.
        rewrite <- (proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 109%positive ltac:(destruct r; cbn; lia)), E106, U109, HU in Hf.
        exists (rho_sub rho2 (s_PB2mb_Dm r)). split.
        { apply GoodM_sub; [destruct r; reflexivity|]. eapply GoodM_agree; [exact Hag2 | destruct r; cbn; lia | exact HGM1]. }
        eapply SP_entails in Hw; [|exact (ent_PB2mb_Dm r)].
        replace (length MSG) with (length M1 - L0m rho + k)%nat; [exact Hw|]. lia.
      *
        apply triple_facts. intros HF. pose proof (Forall_hd_r _ _ r HF _ _ _ eq_refl eq_refl) as Hf.
        cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Z.eqb_eq in Hf.
        erewrite (U_addc rho2 (SVar 106) 7) in Hf; [| reflexivity | |];
          change (eval rho2 (SVar 106)) with (rw rho2 106) in *; change (eval rho2 (SVar 109)) with (rw rho2 109) in *.
        2,3: rewrite <- ?(proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)), ?E106, ?HU; lia.
        rewrite <- (proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 109%positive ltac:(destruct r; cbn; lia)), E106, U109, HU in Hf.
        assert (ER : L0m (rho_sub rho2 (s_PB2mb_CB1m r)) = (L0m rho + 7 - k)%nat).
        { unfold L0m at 1. cbn [rho_sub rw]. rewrite (sv_PB2mb r).
          erewrite (U_sub2 rho2 (SLit 7) _ 7 (Z.of_nat k - Z.of_nat (L0m rho))); [lia | apply U_lit64; lia | | lia].
          erewrite U_sub2; [reflexivity | | | lia]; change (eval rho2 (SVar 109)) with (rw rho2 109); change (eval rho2 (SVar 106)) with (rw rho2 106);
            rewrite <- ?(proj1 Hag2 109%positive ltac:(destruct r; cbn; lia)), <- ?(proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)), ?U109, ?E106, ?HU; reflexivity. }
        eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH1 (rho_sub rho2 (s_PB2mb_CB1m r)))].
        -- intros w Hw. eapply SP_entails in Hw; [|exact (ent_PB2mb_CB1m r)].
           replace (length MSG - L0m (rho_sub rho2 (s_PB2mb_CB1m r)))%nat with (length M1 - L0m rho + k)%nat by lia. exact Hw.
        -- apply GoodM_sub; [destruct r; reflexivity|]. eapply GoodM_agree; [exact Hag2 | destruct r; cbn; lia | exact HGM1].
        -- lia.
        -- lia.
  -
    intros rho HGM HR Hm. pose proof (proj1 HGM) as HG.
    assert (HU : bv_unsigned (rw rho 106) = Z.of_nat (L0m rho)) by (unfold L0m; pose proof (urange (rw rho 106)); lia).
    eapply triple_seq.
    { apply (writev_site1 (CB1m r) (reg_sv (CB1m r) 22) (length MSG - L0m rho) (skipn (7 - L0m rho) M2) rho HG);
        [rewrite Hnxc; lia | exact Hic | exact H17c | exact H10c | exact H12c | rewrite R22c, Hnxc; reflexivity | | |].
      + rewrite MSL. replace (14 + length argv0 - L0m rho)%nat with (length M1 + (7 - L0m rho))%nat by lia.
        rewrite MSG_skipB by lia. rewrite firstn_all. reflexivity.
      + rewrite length_skipn, M2_len. unfold MAX_RW_COUNT. lia.
      + intros tr ms md Hsp. exact (proj2 (bytes_CB1m r rho tr ms md HGM Hsp)). }
    apply triple_ex; intros rho1. apply triple_ex; intros k.
    apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
    rewrite Hnxc in Hk, Hag1. rewrite length_skipn, M2_len in Hkb.
    assert (HGM1 : GoodM rho1) by (split; [exact HG1 | rewrite <- (proj1 (proj2 Hag1)); exact (proj2 HGM)]).
    assert (E106 : rw rho1 106 = rw rho 106) by (symmetry; apply (proj1 Hag1); lia).
    assert (U110 : bv_unsigned (rw rho1 110) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
    change (S_after_write (CB1m r) (reg_sv (CB1m r) 22)) with (PB1m r).
    eapply run_tr; [exact (run_PB1m r) | destruct r; reflexivity | apply okf |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
    +
      eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
      intros w Hw. pose proof (hd_fact_r rho2 L_PB1m_0 r w _ Hw _ _ _ eq_refl eq_refl) as Hf.
      cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
      change (eval rho2 (SVar 110)) with (rw rho2 110) in Hf. change (eval rho2 (SVar 106)) with (rw rho2 106) in Hf.
      rewrite <- (proj1 Hag2 110%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)), U110, E106, HU in Hf.
      exists (rho_sub rho2 (s_PB1m_Dm r)). split.
      { apply GoodM_sub; [destruct r; reflexivity|]. eapply GoodM_agree; [exact Hag2 | destruct r; cbn; lia | exact HGM1]. }
      eapply SP_entails in Hw; [|exact (ent_PB1m_Dm r)].
      replace (length MSG) with (length MSG - L0m rho + k)%nat at 1; [exact Hw|]. lia.
    +
      apply triple_facts. intros HF. pose proof (Forall_hd_r _ _ r HF _ _ _ eq_refl eq_refl) as Hf.
      cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Z.eqb_eq in Hf.
      change (eval rho2 (SVar 110)) with (rw rho2 110) in Hf. change (eval rho2 (SVar 106)) with (rw rho2 106) in Hf.
      rewrite <- (proj1 Hag2 110%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)), U110, E106, HU in Hf.
      assert (ER : L0m (rho_sub rho2 (s_PB1m_CB1m r)) = (L0m rho - k)%nat).
      { unfold L0m at 1. cbn [rho_sub rw]. rewrite (sv_PB1m r).
        erewrite U_sub2; [| reflexivity | reflexivity |]; change (eval rho2 (SVar 106)) with (rw rho2 106); change (eval rho2 (SVar 110)) with (rw rho2 110);
          rewrite <- (proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 110%positive ltac:(destruct r; cbn; lia)), E106, U110, HU; lia. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH1 (rho_sub rho2 (s_PB1m_CB1m r)))].
      * intros w Hw. eapply SP_entails in Hw; [|exact (ent_PB1m_CB1m r)].
        replace (length MSG - L0m (rho_sub rho2 (s_PB1m_CB1m r)))%nat with (length MSG - L0m rho + k)%nat by lia. exact Hw.
      * apply GoodM_sub; [destruct r; reflexivity|]. eapply GoodM_agree; [exact Hag2 | destruct r; cbn; lia | exact HGM1].
      * lia.
      * lia.
Qed.

Lemma L_Mg : forall r : bool, (((67%nat <= (length argv0))%nat /\ ((length argv0) <= 73%nat)%nat) -> (forall (rho : valuation), ((GoodM rho) -> (triple segs ok (SP segs (Kx (TR 0%nat) md0) (E_Mg r) rho) (QDm r))))).
Proof using Hargc Hent Hfd2 Hrdr0 Hinp HokK HokP.
  intros r Hmid rho HGM. pose proof NU as NU'. pose proof (proj1 HGM) as HG. pose proof M1_len as ML. pose proof MSG_len as MSL.
  destruct (cert_E_Mg r) as (_ & _ & _ & _ & _ & _ & _ & _ & R22 & Hi & H17 & H10 & H12 & Hnx & _).
  eapply triple_seq.
  { apply (writev_site2 (E_Mg r) (reg_sv (E_Mg r) 22) 0 M1 M2 rho HG);
      [rewrite Hnx; lia | exact Hi | exact H17 | exact H10 | exact H12 | rewrite R22, Hnx; reflexivity | | |].
    + cbn [skipn]. unfold MSG. rewrite firstn_all. reflexivity.
    + rewrite length_app, ML, M2_len. unfold MAX_RW_COUNT. lia.
    + intros tr ms md Hsp. exact (bytes_E_Mg r rho tr ms md HGM Hmid Hsp). }
  apply triple_ex; intros rho1. apply triple_ex; intros k.
  apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
  rewrite Hnx in Hk, Hag1. rewrite length_app, ML, M2_len in Hkb.
  assert (HGM1 : GoodM rho1) by (split; [exact HG1 | rewrite <- (proj1 (proj2 Hag1)); exact (proj2 HGM)]).
  assert (U106 : bv_unsigned (rw rho1 106) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite mod64; lia).
  pose proof (G_v5 rho1 HG1) as V5.
  change (S_after_write (E_Mg r) (reg_sv (E_Mg r) 22)) with (PAm r). cbn [Nat.add].
  destruct (Nat.le_gt_cases k (7 + length argv0)) as [Hle|Hgt].
  -
    eapply triple_conseq with (P := SP segs (Kx (TR k) md0) (PAma r) rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. apply SP_add1; [exact Hw | | destruct r; reflexivity]. cbn [holds]. change (eval rho1 (SVar 106)) with (rw rho1 106).
      erewrite U_addc; [| exact V5 | unfold N0; lia | lia]. rewrite U106. unfold N0. lia. }
    eapply run_tr; [exact (run_PAma r) | destruct r; reflexivity | apply okf |].
    intros L rho2 [<-|[]] Hag2. cbn [lf_state].
    assert (EL : L0m (rho_sub rho2 (s_PAma_CB2m r)) = (7 + length argv0 - k)%nat).
    { unfold L0m. cbn [rho_sub rw]. rewrite (sv_PAma r).
      erewrite (U_sub2 rho2 _ _ (N0 + 7) (Z.of_nat k)); [unfold N0; lia | | | unfold N0; lia].
      - erewrite U_addc; [reflexivity | | unfold N0; lia | lia]. change (eval rho2 (SVar 5)) with (rw rho2 5). rewrite <- (proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)). exact V5.
      - change (eval rho2 (SVar 106)) with (rw rho2 106). rewrite <- (proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)). exact U106. }
    eapply triple_conseq; [| intros w Hw; exact Hw | apply (proj1 (loopm r Hmid (14 + length argv0 - k)) (rho_sub rho2 (s_PAma_CB2m r)))].
    + intros w Hw. eapply SP_entails in Hw; [|exact (ent_PAma_CB2m r)].
      replace (length M1 - L0m (rho_sub rho2 (s_PAma_CB2m r)))%nat with k by lia. exact Hw.
    + apply GoodM_sub; [destruct r; reflexivity|]. eapply GoodM_agree; [exact Hag2 | destruct r; cbn; lia | exact HGM1].
    + lia.
    + lia.
  -
    eapply triple_conseq with (P := SP segs (Kx (TR k) md0) (PAmb r) rho1); [| intros w Hw; exact Hw |].
    { intros w Hw. apply SP_add1; [exact Hw | | destruct r; reflexivity]. cbn [holds]. change (eval rho1 (SVar 106)) with (rw rho1 106).
      erewrite U_addc; [| exact V5 | unfold N0; lia | lia]. rewrite U106. unfold N0. lia. }
    eapply run_tr; [exact (run_PAmb r) | destruct r; reflexivity | apply okf |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state].
    +
      apply triple_facts. intros HF. pose proof (Forall_hd_r _ _ r HF _ _ _ eq_refl eq_refl) as Hf.
      cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. apply Bool.negb_true_iff in Hf. apply Z.eqb_neq in Hf.
      erewrite (U_addc rho2 (SVar 5) 14) in Hf; [| reflexivity | |];
        change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 106)) with (rw rho2 106) in *.
      2,3: rewrite <- ?(proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)), ?V5; unfold N0; lia.
      rewrite <- (proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)), V5, U106 in Hf.
      assert (ER : L0m (rho_sub rho2 (s_PAmb_CB1m r)) = (14 + length argv0 - k)%nat).
      { unfold L0m. cbn [rho_sub rw]. rewrite (sv_PAmb r).
        erewrite (U_sub2 rho2 (SLit 7) _ 7 (Z.of_nat k - (N0 + 7))); [unfold N0; lia | apply U_lit64; lia | | unfold N0 in *; lia].
        erewrite (U_sub2 rho2 _ _ (Z.of_nat k) (N0 + 7)); [lia | | | unfold N0; lia].
        - change (eval rho2 (SVar 106)) with (rw rho2 106). rewrite <- (proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)). exact U106.
        - erewrite U_addc; [reflexivity | | unfold N0; lia | lia]. change (eval rho2 (SVar 5)) with (rw rho2 5). rewrite <- (proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)). exact V5. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (proj2 (loopm r Hmid (14 + length argv0 - k)) (rho_sub rho2 (s_PAmb_CB1m r)))].
      * intros w Hw. eapply SP_entails in Hw; [|exact (ent_PAmb_CB1m r)].
        replace (length MSG - L0m (rho_sub rho2 (s_PAmb_CB1m r)))%nat with k by lia. exact Hw.
      * apply GoodM_sub; [destruct r; reflexivity|]. eapply GoodM_agree; [exact Hag2 | destruct r; cbn; lia | exact HGM1].
      * unfold N0 in Hf. lia.
      * lia.
    +
      eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
      intros w Hw. pose proof (hd_fact_r rho2 L_PAmb_1 r w _ Hw _ _ _ eq_refl eq_refl) as Hf.
      cbn [holds branch_taken] in Hf. unfold bv_eqb in Hf. rewrite Bool.negb_true_iff, Z.eqb_neq in Hf.
      erewrite (U_addc rho2 (SVar 5) 14) in Hf; [| reflexivity | |];
        change (eval rho2 (SVar 5)) with (rw rho2 5) in *; change (eval rho2 (SVar 106)) with (rw rho2 106) in *.
      2,3: rewrite <- ?(proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)), ?V5; unfold N0; lia.
      rewrite <- (proj1 Hag2 5%positive ltac:(destruct r; cbn; lia)), <- (proj1 Hag2 106%positive ltac:(destruct r; cbn; lia)), V5, U106 in Hf.
      exists (rho_sub rho2 (s_PAmb_Dm r)). split.
      { apply GoodM_sub; [destruct r; reflexivity|]. eapply GoodM_agree; [exact Hag2 | destruct r; cbn; lia | exact HGM1]. }
      eapply SP_entails in Hw; [|exact (ent_PAmb_Dm r)].
      replace (length MSG) with k; [exact Hw|]. unfold N0 in Hf. lia.
Qed.

Lemma cert_zm : forall r : bool, (((obj_rng (ob0 (E_Zm r))) = (pair (pair (SVar 1%positive) (SLit (Z.opp STK_FREE))) (SLit (-560)%Z))) /\ ((2%nat <= (length (ss_objs (E_Zm r))))%nat /\ (((existsb (cell_eqb (mkCell (SLit (-664)%Z) 8%Z (SLit 0%Z))) (ob_cells (ob0 (E_Zm r)))) = true) /\ (((existsb (cell_eqb (mkCell (SLit (-656)%Z) 8%Z (SLit 0%Z))) (ob_cells (ob0 (E_Zm r)))) = true) /\ (((reg_sv (E_Zm r) 11%Z) = (SAlu ALU_ADD (SVar 1%positive) (SLit (-664)%Z))) /\ (((instr_at segs (ss_pc (E_Zm r))) = (Some Ecall)) /\ (((reg_sv (E_Zm r) 17%Z) = (SLit 66%Z)) /\ (((reg_sv (E_Zm r) 10%Z) = (SLit 2%Z)) /\ (((reg_sv (E_Zm r) 12%Z) = (SLit 1%Z)) /\ (((instr_at segs (ss_pc (E_exitm r))) = (Some Ecall)) /\ (((reg_sv (E_exitm r) 17%Z) = (SLit 94%Z)) /\ ((reg_sv (E_exitm r) 10%Z) = (SLit 2%Z))))))))))))).
Proof using Hargc LEN N0 STR. intros [|]; vm_compute; repeat split; (reflexivity || lia). Qed.

Lemma L_Dm : forall r : bool, (forall (rho : valuation), ((GoodM rho) -> (triple segs ok (SP segs (Kx (TR (length MSG)) md0) (Dm r) rho) (fun (x : world) => False)))).
Proof using Hargc Hent Hfd2 Hfs Hinp HokK HokP Hokh.
  intros r rho HGM. pose proof NU as NU'.
  destruct (cert_zm r) as (Hrng & Hlen & C1 & C2 & R11 & Hi & H17 & H10 & H12 & Hix & H17x & H10x).
  eapply run_tr; [exact (run_Dm r) | destruct r; reflexivity | apply okf |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  pose proof (GoodM_agree _ _ _ Hag1 ltac:(destruct r; cbn; lia) HGM) as HGM1. pose proof (proj1 HGM1) as HG1. pose proof (G_v1 rho1 HG1) as V1.
  eapply triple_seq.
  { apply triple1_triple.
    apply (SysNA.triple1_writev01J_na segs ok (liftK (Kx (TR (length MSG)) md0)) (E_Zm r) rho1 2);
      [apply ok_frame_liftK; apply okf | eapply NoAlloc.ok_pframeJ_na_of_tcons; [apply HokP; intros tr0 md0_ H0; exact H0 | intros r0 tr md Hk; exact (Ktc _ tr md Hk)]
      | exact Hi | exact H17 | exact H10 | exact H12 | lia | intros r0 tr md [_ ->]; exact Hfd2 |].
    intros tr ms md Hsp _. rewrite R11.
    assert (A0 : bv_unsigned (eval rho1 (SAlu ALU_ADD (SVar 1) (SLit (-664)))) = bv_unsigned sp - 664).
    { erewrite U_addc; [reflexivity | exact V1 | lia | lia]. }
    exists (eval rho1 (SLit 0)). split.
    - eapply (iov_field_lo rho1 (E_Zm r) tr ms md (-664)); [exact HG1 | exact Hsp | exact Hlen | exact Hrng | exact C1 | lia | lia].
    - split; [|split; [rewrite A0; unfold TASK_SIZE; lia | rewrite U_lit64 by lia; unfold TASK_SIZE; lia]].
      change (Z_to_bv 64 0) with (eval rho1 (SLit 0)).
      eapply (iov_field_lo rho1 (E_Zm r) tr ms md (-656)); [exact HG1 | exact Hsp | exact Hlen | exact Hrng | exact C2 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]. }
  change (SPJ segs (liftK (Kx (TR (length MSG)) md0)) (S_after (E_Zm r) (SLit 0) (ss_objs (E_Zm r)) (ss_next (E_Zm r))) rho1) with (SP segs (Kx (TR (length MSG)) md0) (PZm r) rho1).
  eapply run_tr; [exact (run_PZm r) | destruct r; reflexivity | apply okf |].
  intros L rho2 [<-|[]] Hag2. cbn [lf_state].
  apply (SysNA.triple_exit_eval_na segs ok SpecT (Kx (TR (length MSG)) md0) (E_exitm r) rho2 2);
    [apply okf | apply okp | exact Hokh | exact Hix | left; exact H17x | rewrite H10x; rewrite U_lit64 by lia; reflexivity |].
  intros tr md [-> ->]. rewrite TR_all by lia. rewrite Hfs. exact final_in_spec.
Qed.

Theorem usage_mid_safe : (((67%nat <= (length argv0))%nat /\ ((length argv0) <= 73%nat)%nat) -> (((check_core_m rq N0 (sym_run segs FUELn [] (Tn rq N0) true)) = true) -> (forall (rho : valuation), ((JI rho) -> (triple segs ok (SP segs (Kx [] md0) (S_main rq) rho) (fun (x : world) => False)))))).
Proof using Hargc Hent Hfd2 Hrdr0 Hfs Hinp HokK HokP Hokh LEN STR.
  intros Hmid Hchk rho HJ.
  destruct (check_core_m_sound rq N0 _ Hchk) as (a & ws & Hwf & _).
  eapply triple_conseq with (P := fun w => exists rho', Good rho' /\ SP segs (Kx (TR 0) md0) (S_use rq) rho' w); [| intros w Hw; exact Hw |].
  { intros w Hw. apply (use_intro rho w HJ). exact Hw. }
  apply triple_ex; intros rho1. apply triple_pure; intros HG1.
  eapply triple_seq.
  { eapply run_tr; [exact (run_use rq) | unfold rq; destruct (kb_rseq (in_kernel inp)); reflexivity | apply okf |].
    intros L rho2 [<-|[]] Hag2. cbn [lf_state].
    pose proof (Good_agree _ _ _ Hag2 ltac:(unfold rq; destruct (kb_rseq (in_kernel inp)); cbn; lia) HG1) as HG2.
    apply (call_path segs FirstNul ok (Kx (TR 0) md0) (Kx (TR 0) md0) (E_sn rq) (E_snX rq) Pre_strnlen xs_pre (s_sn rq) (R_sn rq) Posts_strnlen _ rho2
             (xs_pre_ok rq) (efr_sn rq) (chk_sn rq) (fb_sn rq)).
    - intros rho3 HF. apply strnlen_sum; [apply okf | exact HF].
    - intros ms _. apply (FirstNul_call rq). exact HG2.
    - intros L rho3 [<-|[]] Hag3 HF3. cbn [lf_state]. replace (ss_next Pre_strnlen) with NF by reflexivity. rewrite (T_imp_eq rq).
      pose proof (Good_agree _ _ _ Hag3 ltac:(unfold rq; destruct (kb_rseq (in_kernel inp)); cbn; lia) HG2) as HG3.
      apply (post_path segs ok (Kx (TR 0) md0) (T_imp rq) (T_sn rq) (ss_facts (E_sn rq)) xs_post rho3 _ (fb_sn2 rq) (xs_post_ok rq) HF3).
      apply triple_facts. intros HFT.
      eapply triple_conseq with (P := SP segs (Kx (TR 0) md0) (Tn rq N0) rho3); [| intros w Hw; exact Hw | apply (L_mid_pre rq N0 Hchk eq_refl); exact HG3].
      intros w Hsp. apply (Tn_intro rq N0 rho3 w HG3 eq_refl Hwf).
      eapply (SP_restate segs _ rho3 (T_sn rq) (T_sn1 rq) w); [exact (swf_T_sn1 rq) | exact (diff_sn rq) | | constructor | exact Hsp].
      constructor; [|constructor]. cbn [fst snd]. exact (proj1 (Forall_forall _ _) HFT _ (fact_T_sn rq)). }
  apply triple_ex; intros rho4. apply triple_pure; intros HG4.
  eapply triple_seq; [apply (L_Mg rq Hmid); exact HG4|].
  apply triple_ex; intros rho5. apply triple_pure; intros HG5.
  apply (L_Dm rq). exact HG5.
Qed.


End Usage.
End Drv_usage.

Module Drv_usage_all.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.StartStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G1.Drv_usage_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G1.Drv_usage_small_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G1.Drv_usage_mid_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G1.Drv_usage_small_chk1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G2.Drv_usage_small_chk2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G1.Drv_usage_small_chk3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G2.Drv_usage_small_chk4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_usage__G2.Drv_usage_mid_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.BudgetWit.UsageB.Drv_usage.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma check_range_sound : forall r : bool, (forall (a : nat), (forall (len : nat), (forall (k : nat), (((check_range r a len) = true) -> (((a <= k)%nat /\ (k < (Nat.add a len))%nat) -> ((check_core r (Z.of_nat k) (sym_run segs FUELn [] (Tn r (Z.of_nat k)) true)) = true)))))).
Proof.
  intros r a len k H Hk. unfold check_range in H.
  exact (proj1 (forallb_forall _ _) H k ltac:(apply in_seq; lia)).
Qed.

Lemma check_small : forall r : bool, (forall (k : nat), ((k <= 66%nat)%nat -> ((check_core r (Z.of_nat k) (sym_run segs FUELn [] (Tn r (Z.of_nat k)) true)) = true))).
Proof.
  intros r k Hk.
  destruct (Nat.lt_ge_cases k 17); [eapply (check_range_sound r 0 17); [exact (check_range_1 r) | lia]|].
  destruct (Nat.lt_ge_cases k 34); [eapply (check_range_sound r 17 17); [exact (check_range_2 r) | lia]|].
  destruct (Nat.lt_ge_cases k 51); [eapply (check_range_sound r 34 17); [exact (check_range_3 r) | lia]|].
  eapply (check_range_sound r 51 16); [exact (check_range_4 r) | lia].
Qed.

Lemma check_range_m_sound : forall r : bool, (forall (a : nat), (forall (len : nat), (forall (k : nat), (((check_range_m r a len) = true) -> (((a <= k)%nat /\ (k < (Nat.add a len))%nat) -> ((check_core_m r (Z.of_nat k) (sym_run segs FUELn [] (Tn r (Z.of_nat k)) true)) = true)))))).
Proof.
  intros r a len k H Hk. unfold check_range_m in H.
  exact (proj1 (forallb_forall _ _) H k ltac:(apply in_seq; lia)).
Qed.

Lemma check_mid : forall r : bool, (forall (k : nat), (((67%nat <= k)%nat /\ (k <= 73%nat)%nat) -> ((check_core_m r (Z.of_nat k) (sym_run segs FUELn [] (Tn r (Z.of_nat k)) true)) = true))).
Proof. intros r k Hk. apply (check_range_m_sound r 67 7 k (check_range_mid r)). lia. Qed.

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
Hypothesis Hrdr0 : m_channel_reader md0 = true.
Variable ok : world -> Prop.
Hypothesis HokK : ltac2:(tb__ "0|0|
S2dS40A1S41OF_;F_;Sd5Sc9Vinp;A1R1A2S4cS2aVok;R2A3F_;FK;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S2dS40A1S41OF_;F_;Sd5Sc9Vinp;A1R1A2Sd0S2aVok;R2A3F_;FK;").
Hypothesis Hokh : ltac2:(tb__ "0|0|
Sd6Vok;Sc9Vinp;A1A2").

Theorem usage_safe : (forall (rho : valuation), ((Jinit segs pcP phP sp mb draw inp rho) -> (triple segs ok (SP segs (Kx [] md0) (S_main (kb_rseq (in_kernel inp))) rho) (fun (x : world) => False)))).
Proof using Hargc Hent Hfd2 Hrdr0 Hfs Hinp HokK HokP Hokh.
  intros rho HJ. destruct (Nat.le_gt_cases (length argv0) 66) as [Hs|Hgt]; [|destruct (Nat.le_gt_cases (length argv0) 73) as [Hm|Hb]].
  - exact (usage_small_safe sp brk mb draw inp Hent Hinp Hargc md0 Hfd2 Hfs Hrdr0 ok HokK HokP Hokh Hs (check_small (kb_rseq (in_kernel inp)) (length argv0) Hs) rho HJ).
  - assert (Hm2 : (67 <= length argv0 <= 73)%nat) by lia.
    exact (usage_mid_safe sp brk mb draw inp Hent Hinp Hargc md0 Hfd2 Hfs Hrdr0 ok HokK HokP Hokh Hm2 (check_mid (kb_rseq (in_kernel inp)) (length argv0) Hm2) rho HJ).
  - assert (Hb2 : (74 <= length argv0)%nat) by lia.
    exact (usage74_safe sp brk mb draw inp Hent Hinp Hargc md0 Hfd2 Hfs Hrdr0 ok HokK HokP Hokh Hb2 rho HJ).
Qed.

End All.
End Drv_usage_all.
