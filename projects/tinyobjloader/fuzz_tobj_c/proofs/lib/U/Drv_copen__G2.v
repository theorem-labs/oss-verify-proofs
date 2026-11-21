(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch model's channel reader as a premise of the writev paths, LPS 08b1429; the initial-valuation invariant Jinit taking the launch's mmap base; the cannot-open path per CONFIG_RSEQ, its lemmas stated for the run's flag and its loop checks for both values of the flag; DrvTail1's new layout: the random bytes below the strings, the auxv's CONFIG_RSEQ-dependent size, the tail's bound N + 10; w2_window written as plain text). *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "False"; "not"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "rl"; "SVar"; "eval"; "sobj"; "sstate"; "SLit"; "SAlu"; "sprop"; "sv_eqb"; "rw"; "ss_next"; "agree_below"; "holds"; "ob_dflt"; "ss_facts"; "ss_lenient"; "soff"; "ss_objs"; "dflt_writable"; "is_arr"; "ob_cells"; "ob_hi"; "ob_lo"; "obj_range"; "obj_holds"; "ranges_disjoint"; "rd"; "rm"; "rom_ok"; "sprop_below"; "swf"; "@Corelib.Init.Datatypes"; "list"; "length"; "bool"; "Some"; "option"; "nil"; "nat"; "cons"; "app"; "true"; "prod"; "false"; "pair"; "None"; "orb"; "fst"; "snd"; "andb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "LQ"; "ok_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G2.Drv_copen.Copen"; "Good"; "TR"; "MSG"; "Q_at"; "GoodS"; "M1"; "QS_at"; "V70"; "PRloc"; "PRw"; "checks_S"; "sub_idG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open"; "Kx"; "J25"; "std_fds"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "m_fds"; "FdChannel"; "fd_lookup"; "in_hwcap"; "in_uid"; "m_fs"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "of_nat"; "pow"; "modulo"; "lt"; "sub"; "leb"; "opp"; "to_nat"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "w_tr"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "sym_run"; "RsCut"; "mkLeaf"; "@Corelib.Init.Nat"; "add"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "nth"; "Forall"; "map"; "seq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "ALU_SLL"; "mulop"; "ALU_SLTU"; "ALU_XOR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "beval"; "bexp_eqb"; "cells_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G1.Drv_copen_states"; "T_cs1"; "E_po"; "BLn"; "E_fxA"; "FUELm"; "T_D1"; "T_D2"; "T_Da"; "T_Db"; "B544"; "E_W1"; "E_W1c"; "E_W2"; "E_W2c"; "E_Wa"; "E_Wa_c"; "E_Wb"; "E_Wb_c"; "E_fx"; "R_gen"; "S_co"; "check_core"; "check_nr"; "s_nr"; "E_cs"; "T_imp"; "check_pre"; "post_loc"; "the_pre"; "BL_co"; "BNZ28"; "C0_nr"; "F_n"; "HInl"; "LENa"; "LOnl"; "R_cs"; "T64"; "Tsm"; "pre_loc"; "s_cs"; "sobj_eqb"; "xs_c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "nl"; "wr"; "ex"; "msg_cannot_open"; "die"; "@Corelib.Init.Peano"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err.WLerr"; "Kw"; "MSG"; "Posts_wl"; "chw"; "TRk"; "@Stdlib.Lists.List"; "In"; "nth_error"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub_get"; "rho_absorb"; "sv_subst"; "wsub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3";
"list_eqb"; "obj_rng"; "state_diff"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G1.Drv_copen_states.CAddr"; "ret_out"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G2.Drv_copen.Copen.GoodFacts"; "lit_of"; "oval"; "add1_of"; "add28_of"; "bval"; "shape_rng"; "AUXB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err.WLerrS"; "Pre_wl2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframe"; "state_has_rl"; "rho_set_rl"; "rho_set_rw"; "smatch_pending"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "entails_fr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "K_tcons"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states"; "S_operr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init"; "phU"; "pcU"; "imgU"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "str_off"; "img_len"; "rand_off"; "region"; "tab"; "valid_entry48"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "is_prefix"; "mkCfg"; "mkEntry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "call_check"; "import_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "Jinit"; "ms0"; "segs_top"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs"; "strs_tail"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "apply_xforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memchr"; "FirstNul"; "@Stdlib.Arith.PeanoNat.Nat"; "min"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.
Require Stdlib.NArith.NArith.
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memchr.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_strnlen.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.

Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvTail1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Drv_copen_chk4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G1.Drv_copen_states.

Lemma check_range_3 : forall r, check_range r 3 0 64 = true.
Proof. intros [|]; unfold check_range, check_nr; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.fast_forallb. Qed.
End Drv_copen_chk4.

Module Drv_copen.

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.

Local Ltac lia := slia.
Local Ltac nia := snia.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import Stdlib.Strings.Ascii Stdlib.Strings.String.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysExtra OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvTail1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.

Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memchr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_strnlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G1.Drv_copen_states.
Import ListNotations.
Import CAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Section Generic.
Variable ok : world -> Prop.

Lemma LQ_elim : ltac2:(tb__ "0|0|
S2bS52A1S53OF_;F_;S8SaS2bS6bA1S6aS6bSaSbbS6bR2R4A3S17R7R6R2A3S68S6Vok;S40S6R9S6cR4A1R3A4R5A4F_;F_;Frho';FL;S68S6Vok;S41S6R6R5R4R3A5R2A4F_;FQ;Fleaves;Frho;Fn;FK;").
Proof using .
  intros K n rho leaves Q H. unfold LQ, LQJ.
  apply triple_ex; intros L. apply triple_ex; intros rho'.
  apply triple_pure; intros Hin. apply triple_pure; intros Hag.
  eapply triple_conseq; [| intros w Hw; exact Hw | exact (H L rho' Hin Hag)].
  intros w [Hsm Hk]. split; assumption.
Qed.

Lemma run_tr : ltac2:(tb__ "0|1|
S31S2bS7A1S10S2bS6bA1M0S2bS52A1S53OF_;F_;SaS6aS0S2fG0A1S6dS6R7R6R5S34A5S2eG0R4A2A3S0S2dS1bR6A1S36A3S42S6Vok;R5A3S6bSaSbbS6bR2R9A3S17S16RbA1R8R2A3S68S6Vok;S40S6RaS6cR4A1R3A4R8A4F_;F_;Frho';FL;S68S6Vok;S40S6R7R9R6A4R5A4F_;F_;F_;F_;FQ;Frho;FK;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves K rho Q Hrun Hstrict Hok H.
  eapply triple_seq; [apply triple1_triple; eapply sym_run_sound; [exact Hrun | exact Hok | rewrite Hstrict; discriminate]|].
  apply LQ_elim. exact H.
Qed.

Lemma eLQ_elim : ltac2:(tb__ "0|0|
S2bS52A1S53OF_;F_;S8SaS2bS6bA1S66OF_;S6bSaSbbS6bR2R4A3S17R7R6R2A3S67S6S40S6R9S6cR4A1R3A4R5A3F_;F_;Frho';FL;S67S6S41S6R6R5R4R3A5R2A3F_;FQ;Fleaves;Frho;Fn;FK;").
Proof using .
  intros K n rho leaves Q H w (L & rho' & Hin & Hag & Hsm & Hk).
  exact (H L rho' Hin Hag w (conj Hsm Hk)).
Qed.

Lemma erun_tr : ltac2:(tb__ "0|1|
S31S2bS7A1S10S2bS6bA1M0S2bS52A1S53OF_;F_;SaS66OF_;S0S2fG0A1S6dS6R7R6R5S34A5S2eG0R4A2A3S0S2dS1bR6A1S36A3S6bSaSbbS6bR2R8A3S17S16RaA1R7R2A3S67S6S40S6R9S6cR4A1R3A4R7A3F_;F_;Frho';FL;S67S6S40S6R6R8R5A4R4A3F_;F_;F_;FQ;Frho;FK;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves K rho Q Hrun Hstrict H w Hsp.
  destruct (sym_run_complete segs fuel cuts S leaves K rho w Hstrict Hrun Hsp) as (L & rho' & w' & Hin & Hst & Hag & Hsp').
  destruct (H L rho' Hin Hag w' Hsp') as (w'' & Hst' & HQ).
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.

Lemma triple_from : ltac2:(tb__ "0|1|
S6aSaS6aF_;S6aS66R4R1A1M0S2SaSaR5R1R3A2Lrho;A2F_;Fw;SaS68S6Vok;G0R3A4Frho;S68S6Vok;R5R3A4F_;F_;FQ;FP';FP;").
Proof using .
  intros P P' Q HP H. eapply triple_conseq with (P := fun w => exists rho, P' rho w); [exact HP | intros w Hw; exact Hw |].
  apply triple_ex. exact H.
Qed.
Lemma etriple_from : ltac2:(tb__ "0|2|
S66OF_;M0SaG0F_;G0S66R4R1A1M1S2SaSaR5R1R3A2Lrho;A2F_;Fw;SaS67S6G1R3A3Frho;S67S6R5R3A3F_;F_;FQ;FP';FP;").
Proof using . intros P P' Q HP H w Hw. destruct (HP w Hw) as [rho Hr]. exact (H rho w Hr). Qed.
End Generic.

Lemma SP_fact : ltac2:(tb__ "0|0|
S2bS52A1S53OF_;F_;S10SaS66S13S40S6R5R4R3R2A5SbbS13R2S1aR5A1A3S18R5R3A2F_;F_;Fp;Fw;Frho;FS;FK;").
Proof. intros K S rho w p Hsp Hin. exact (proj1 (Forall_forall _ _) (SP_facts_hold segs K rho S w Hsp) p Hin). Qed.

Lemma U_lit64 : ltac2:(tb__ "0|0|
SaS7S1S5bZ0R1A2S60R1S5eZ2Z40A2A2A2S0S7S3eQ40SeR3S11R2A1A2A2R2A3F_;Fz;Frho;").
Proof. intros rho z Hz. cbn. apply Z_to_bv_small. rewrite two64. exact Hz. Qed.

Lemma soff_add_small : ltac2:(tb__ "0|1|
SaSbS7S7S0S7S3eQ40SeR4R3A2A2R1A3S1S5bZ0R2A2S60R2S5eZ2Z3eA2M0A2A2S1S5bS63G0A1R4A2S60R4G0A2A2S0S7S1cR7S12S77R6S11R5A1A3A2S5cR4R5A2A3F_;F_;F_;Fx;Fc;Fe;Frho;").
Proof.
  intros rho e c x Hx Hr Hc. unfold soff, bv_signed, bv_swrap, bv_wrap. cbn [eval]. rewrite add_val, Hx.
  change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 c) with (c mod 2 ^ 64).
  rewrite Zplus_mod_idemp_r.
  destruct (Z_lt_le_dec (x + c) 0).
  - rewrite <- (Z_mod_plus_full (x + c) 1 (2 ^ 64)). rewrite (Z.mod_small (x + c + 1 * 2 ^ 64)) by lia.
    rewrite <- (Z_mod_plus_full (x + c + 1 * 2 ^ 64 + 2 ^ 63) (-1) (2 ^ 64)). rewrite Z.mod_small by lia. lia.
  - rewrite (Z.mod_small (x + c)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma firstn_add_skipn : forall {A} (l : list A) n k, firstn n l ++ firstn k (skipn n l) = firstn (n + k) l.
Proof.
  intros A l n k. revert l. induction n as [|n IH]; intros l; [reflexivity|].
  destruct l as [|x l]; cbn; [rewrite firstn_nil; reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma Kw_Kx : ltac2:(tb__ "0|2|
S2bS52A1M0S53G0S53OF_;F_;S2bS3dQ8A1A1M1G1S31G0S53S5Sb6S4fR8R7A2R5R4R3R2R1A6S4fS33S52R8SbaR5R4R3A3A3R7R2R1A4A2Fmd;Ftr;Fk;Fbs2;Fbs1;FK';Fm;Ft;").
Proof.
  intros t m K' bs1 bs2 k tr md. unfold WLerr.Kw, Kx. split.
  - intros (tr0 & [-> ->] & ->). auto.
  - intros [-> ->]. exists t. auto.
Qed.

Section Copen.
Variable sp brk mb : word.
Variable draw : EntryDraw.
Variable lim : Z.
Variable inp : ProcInput.
Hypothesis Hent : ltac2:(tb__ "0|0|
Se5SddSeaVsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Let argv := in_argv inp.
Let envp := in_envp inp.
Let argv0 : list byte := nth 0 argv [].
Let argv1 : list byte := nth 1 argv [].
Let fs := in_fs inp.
Hypothesis Hargc : length argv = 2%nat.

Variable md0 : Model.
Hypothesis Hfds0 : ltac2:(tb__ "0|0|
S0S2bS35S3dQ40A1S54A2A1S55Vmd0;A1S51A3").
Hypothesis Hfs : ltac2:(tb__ "0|0|
S0Se6S5aVmd0;A1Vfs;A3").
Hypothesis Hrdr0 : m_channel_reader md0 = true.
Variable ok : world -> Prop.
Let SpecT : list event -> Prop := Spec inp.
Hypothesis HokK : ltac2:(tb__ "0|0|
S2bS52A1S53OF_;F_;Sd9VSpecT;R1A2S42S6Vok;R2A3F_;FK;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S2bS52A1S53OF_;F_;Sd9VSpecT;R1A2Sd2S6Vok;R2A3F_;FK;").
Hypothesis Hokh : ok_halted ok SpecT.

Lemma Hsp : valid_sp sp. Proof using Hent. exact (proj1 Hent). Qed.
Lemma Hargc2 : (2 <= length argv)%nat. Proof using Hargc. unfold argv in *. lia. Qed.
Lemma Hlaunch : entry_launch_ok_va Sv48 (mkEntry sp brk mb draw) inp.
Proof using Hent. destruct Hent as (_ & _ & _ & _ & H). exact H. Qed.
Let JI : ltac2:(tb__ "0|0|
SaOFrho;") := ltac2:(tb__ "0|0|
SedS6SdcSdbVsp;Vmb;Vdraw;Vinp;A7").
(* LPS 727298f3: the layout numbers of the new entry stack (Lib/InitState.v): the head holds argc, argv,
   envp, the auxv ([AUX] = [auxv_size] bytes: 432, or 464 with CONFIG_RSEQ), a parity gap and the random
   bytes at [rand_off]; the strings start at [str_off], above them. *)
Let STR : Z := Z.of_nat (str_off inp sp draw).
Let RND : Z := Z.of_nat (rand_off inp).
Let LEN : Z := Z.of_nat (img_len inp sp draw).
Let AUX : Z := Z.of_nat (auxv_size (kb_rseq (in_kernel inp))).
Let ENVC := Z.of_nat (length envp).
Let A1 : Z := InitArg1.A1 sp draw inp.

Let N : Z := Z.of_nat (length argv1).
Let L3 : Z := ltac2:(tb__ "0|0|
S61VLEN;S5cS5cVSTR;S5dS2cS3dQ8A1Vargv0;A2A1A2Z1A2A2").

Let tail1 : list byte := DrvTail1.tail1 inp.

Lemma A1_eq : ltac2:(tb__ "0|0|
S0S7VA1;S5cS5cS5cS3eQ40Vsp;A2VSTR;A2S5dS2cS3dQ8A1Vargv0;A2A1A2Z1A2A3").
Proof using argv envp. reflexivity. Qed.

(* The numbers the path reads, in the new layout (Lib/InitArg1.v's [NUMS1], Lib/InitState.v's [nums]
   and [LEN_fit]): the auxv ends below the random bytes, the strings start above them, and the image
   ends below the stack window's top. *)
Lemma NU :
  (140735340871680 <= bv_unsigned sp <= 140737488355328)
  /\ RND = 8 * 2 + 8 * ENVC + 24 + AUX + 8 * Z.of_nat (Nat.modulo (block_items argv envp) 2)
  /\ RND + 16 <= STR
  /\ (432 <= AUX <= 464)
  /\ (0 <= ENVC <= 256)
  /\ Z.of_nat (length argv0) + 1 + N + 1 <= Z.of_nat (tab argv)
  /\ STR + Z.of_nat (tab argv) + Z.of_nat (tab envp) + 9 <= LEN
  /\ LEN < 2 ^ 22
  /\ N <= 131071
  /\ Z.of_nat (length argv0) <= 131071
  /\ bv_unsigned sp mod 16 = 0
  /\ bv_unsigned sp + LEN <= 140737488355328.
Proof using Hargc Hent Hinp.
  pose proof (NUMS1 pcU phU sp brk mb draw inp Hsp Hinp Hlaunch Hargc2) as N1.
  pose proof (nums pcU phU sp brk mb draw inp Hsp Hinp Hlaunch) as N2.
  pose proof (LEN_fit pcU phU sp brk mb draw inp Hlaunch) as LF.
  pose proof (execfn_nums pcU phU sp brk mb draw inp Hsp Hinp Hlaunch) as (_ & EX).
  pose proof (auxv_size_le (kb_rseq (in_kernel inp))) as AL.
  pose proof (auxv_size_ge (kb_rseq (in_kernel inp))) as AG.
  assert (E : Z.of_nat (length (in_argv inp)) = 2) by (unfold argv in Hargc; rewrite Hargc; reflexivity).
  cbv zeta in N1, N2, LF, EX. rewrite sp_hi_val in LF.
  unfold STR, RND, LEN, ENVC, AUX, N in *. unfold argv0, argv1 in *. unfold argv, envp in *. lia.
Qed.

Lemma length_tail1 : ltac2:(tb__ "0|0|
S0S7S5dS2cS3dQ8A1Vtail1;A2A1VL3;A3").
Proof using Hargc Hent Hinp. exact (DrvTail1.length_tail1 pcU phU sp brk mb draw inp Hsp Hinp Hlaunch Hargc). Qed.
(* The tail after argv[0] holds argv[1], its NUL, the envp strings, AT_EXECFN's name, a NUL and a zero
   word: at least [N + 10] bytes (it was [N + 17], with the random bytes at its end). *)
Lemma L3_ge : N + 10 <= L3 /\ L3 < 2 ^ 22.
Proof using Hargc Hent Hinp. exact (DrvTail1.L3_ge pcU phU sp brk mb draw inp Hsp Hinp Hlaunch Hargc). Qed.
Lemma tail1_nth : forall j : nat,
  nth j tail1 (Z_to_bv 8 0) = nth (j + (length argv0 + 1)) (strs_tail inp) (Z_to_bv 8 0).
Proof using . exact (DrvTail1.tail1_nth inp). Qed.
Lemma region_tail1 : region inp mb phU (Z_to_bv 64 (Z.of_N pcU)) sp draw
  (str_off inp sp draw + (length argv0 + 1)) tail1.
Proof using Hargc Hent Hinp. exact (DrvTail1.region_tail1 pcU phU sp brk mb draw inp Hsp Hinp Hlaunch Hargc). Qed.
Lemma tail1_head : ltac2:(tb__ "0|3|
S31Sb1R1S2cS3dQ8M0A1M1Vargv1;A2A2S0G1S73G1R2Vtail1;S3fG0Z0A2M2A4S73G1R2S33G1Vargv1;S32G1G2S30G1A1A3A3G2A4A3F_;Fj;").
Proof using Hargc. exact (DrvTail1.tail1_head inp Hargc). Qed.
Lemma tail1_firstn : ltac2:(tb__ "0|1|
S0S2bS3dQ8A1M0A1S71G0S2cG0Vargv1;A2Vtail1;A3Vargv1;A3").
Proof using Hargc. exact (DrvTail1.tail1_firstn inp Hargc). Qed.
Lemma tail1_nul : ltac2:(tb__ "0|3|
S0S3dQ8M0A1M1S73G1S2cG1Vargv1;A2Vtail1;S3fG0Z0A2M2A4G2A3").
Proof using Hargc. exact (DrvTail1.tail1_nul inp Hargc). Qed.
Lemma argv1_nonul : ltac2:(tb__ "0|3|
S31Sb2R1S2cS3dQ8M0A1M1Vargv1;A2A2S4S0G1S73G1R2Vtail1;S3fG0Z0A2M2A4G2A3A1F_;Fj;").
Proof using Hargc Hinp. exact (DrvTail1.argv1_nonul inp Hinp Hargc). Qed.

Lemma tail1_frame : ltac2:(tb__ "0|2|
SaVJI;R1A1S31Sb2R1S2cS3dQ8M0A1M1Vtail1;A2A2S0S2fG1A1S27R4S3fQ40S5cVA1;S5dR2A1A2A2A2S2eG1S73G1R2Vtail1;S3fG0Z0A2A4A2A3F_;Fj;F_;Frho;").
Proof using Hargc Hent Hinp. exact (DrvTail1.tail1_frame segs pcU phU sp brk mb draw inp Hsp Hinp Hlaunch Hargc). Qed.
Lemma tail1_ms0 : forall j : nat, (j < length tail1)%nat ->
  ms_mem (ms0 segs pcU phU sp mb draw inp) (Z_to_bv 64 (A1 + Z.of_nat j)) = Some (nth j tail1 (Z_to_bv 8 0)).
Proof using Hargc Hent Hinp. exact (DrvTail1.tail1_ms0 segs pcU phU sp brk mb draw inp Hsp Hinp Hlaunch Hargc). Qed.

Definition M1 : list byte := str "cli: cannot open ".
Definition MSG : list byte := ltac2:(tb__ "0|1|
S33S3dQ8A1M0S48S33G0Vargv1;SacA3A3").
Definition TR (n : nat) : list event := wr 2 (firstn n MSG).

Lemma M1_len : length M1 = 17%nat. Proof using . reflexivity. Qed.
Lemma MSG_len : ltac2:(tb__ "0|1|
S0S31S2cS3dQ8A1M0S45A2S70U12S2cG0Vargv1;A2A2A3").
Proof using A1 Hargc. unfold MSG. rewrite !length_app, M1_len. cbn. lia. Qed.
Lemma MSG_eq : ltac2:(tb__ "0|0|
S0S2bS3dQ8A1A1S45SafVargv1;A1A3"). Proof using . reflexivity. Qed.

Lemma final_in_spec : ltac2:(tb__ "0|1|
VSpecT;S33S52SadZ2M0S45A2S32S52SaeVfs;G0A2S30S52A1A3A3A1").
Proof using Hargc. unfold SpecT, Spec. rewrite MSG_eq. apply spec_cannot_open. exact Hargc. Qed.

Lemma wr_firstn_prefix : ltac2:(tb__ "0|1|
S31Se8S52S44R1A1S33S52SadZ2M0S45A2S32S52SaeVfs;G0A2S30S52A1A3A3A3Fn;").
Proof using .
  intros n. unfold TR, wr.
  replace (map (WriteEv (Z_to_bv 64 2)) MSG ++ [ex fs 2])
    with (map (WriteEv (Z_to_bv 64 2)) (firstn n MSG) ++ (map (WriteEv (Z_to_bv 64 2)) (skipn n MSG) ++ [ex fs 2]))
    by (rewrite app_assoc, <- map_app, firstn_skipn; reflexivity).
  apply is_prefix_app.
Qed.

Lemma Ktc : ltac2:(tb__ "0|0|
S31S53Sd9VSpecT;S4fS44R2A1R1A2A2Fm;Fn;").
Proof using Hargc.
  intros n m tr md [-> _]. exists (wr 2 MSG ++ [ex fs 2]). split; [exact final_in_spec | apply wr_firstn_prefix].
Qed.
Lemma okf : ltac2:(tb__ "0|0|
S31S53S42S6Vok;S4fS44R2A1R1A2A3Fm;Fn;"). Proof using Hargc HokK. intros. apply HokK, Ktc. Qed.
Lemma okp : ltac2:(tb__ "0|0|
S31S53Sd2S6Vok;S4fS44R2A1R1A2A3Fm;Fn;"). Proof using Hargc HokP. intros. apply HokP, Ktc. Qed.
Lemma TR0 : TR 0 = []. Proof using . reflexivity. Qed.
Lemma TR_all : ltac2:(tb__ "0|0|
S31Sb1S2cS3dQ8A1S45A2R1A2S0S2bS52A1S44R2A1SadZ2S45A2A3F_;Fn;").
Proof using . intros n Hn. unfold TR. rewrite firstn_all2 by exact Hn. reflexivity. Qed.

Lemma fd2 : ltac2:(tb__ "0|2|
S53S0S2bS35S3dQ40M0A1S54A2A1S55R1A1S51A3S0S2fS54A1S57S55R2A1S3fG0Z2A2M1A2S2eS54S56G1A1A2A3F_;Fm;").
Proof using . intros m ->. reflexivity. Qed.

Record Good (rho : valuation) : Prop := mkGood {
  g_v1 : rw rho 1 = sp;
  g_v3 : rw rho 3 = Z_to_bv 64 ENVC;
  g_v4 : rw rho 4 = Z_to_bv 64 (bv_unsigned sp + STR);
  g_v5 : rw rho 5 = Z_to_bv 64 (Z.of_nat (length argv0));
  g_v6 : rw rho 6 = Z_to_bv 64 (bv_unsigned sp + RND);
  g_v25 : rw rho 25 = Z_to_bv 64 A1;
  g_v27 : rw rho 27 = Z_to_bv 64 L3;
  g_v28 : rw rho 28 = Z_to_bv 64 N;
  g_rl3 : rl rho 3 = tail1 }.

Lemma Good_of_JI : ltac2:(tb__ "0|2|
SaVJI;R1A1S0S3dQ40M0A1M1S15R2P19A2S3fG0VA1;A2A3S0G1S15R3P1bA2S3fG0VL3;A2A3S0G1S15R4P1cA2S3fG0VN;A2A3S0S2bS3dQ8A1A1ScR5P3A2Vtail1;A3S43R6A1F_;F_;F_;F_;F_;Frho;").
Proof using .
  intros rho HJ H25 H27 H28 H3. constructor; try assumption.
  - exact (ji_sp _ _ _ _ _ _ _ _ HJ).
  - rewrite (ji_envc _ _ _ _ _ _ _ _ HJ). reflexivity.
  - rewrite (ji_argv0 _ _ _ _ _ _ _ _ HJ). reflexivity.
  - rewrite (ji_len0 _ _ _ _ _ _ _ _ HJ). reflexivity.
  - rewrite (ji_rand _ _ _ _ _ _ _ _ HJ). reflexivity.
Qed.

Lemma Good_agree : ltac2:(tb__ "0|1|
S8SaSaS17R3R2R1A3SdeP1dR4A2S43R4A1M0G0F_;F_;F_;Frho';Frho;Fn;").
Proof using Hargc.
  intros n rho rho' (Hw & Hl & Hm) Hn HG.
  destruct HG; constructor; try (rewrite <- Hw by lia; assumption); rewrite <- Hl; assumption.
Qed.

Lemma Good_rm : ltac2:(tb__ "0|0|
SaS3dQ40A1S2fS3dQ8A1A1F_;S43R2A1S43Sc8R3R2A2A1F_;Fm;Frho;").
Proof using . intros rho m HG. destruct HG; constructor; cbn; assumption. Qed.

Definition sub_idG (s : wsub) : bool := ltac2:(tb__ "0|0|
SbdS8S8S14SbfVs;R1A2SdR1A1A2Li;S32S8P1S32S8P3S32S8P4S32S8P5S32S8P6S32S8P19S32S8P1bS32S8P1cS30S8A1A3A3A3A3A3A3A3A3A3").

Lemma Good_sub : ltac2:(tb__ "0|0|
Sc2SaS0S2dS4eR2A1S34A3S43R2A1S43SbeR3R4A2A1F_;F_;Frho;Fs;").
Proof using .
  intros s rho Hs HG. unfold sub_idG in Hs. cbn [forallb] in Hs.
  repeat (apply andb_prop in Hs; destruct Hs as [?E Hs]); clear Hs.
  repeat match goal with H : sv_eqb _ _ = true |- _ => apply sv_eqb_sound in H end.
  destruct HG; constructor; cbn [rho_sub rw rl];
    rewrite ?E, ?E0, ?E1, ?E2, ?E3, ?E4, ?E5, ?E6; cbn [eval]; assumption.
Qed.

Lemma Good_set_rl : ltac2:(tb__ "0|0|
SaS8S2bS3dQ8A1A1S43R3A1S4S0S8R3P3A3A1S43Sd4R5R4R3A3A1F_;F_;FL;Fl;Frho;").
Proof using .
  intros rho l L HG N3. destruct HG; constructor; cbn; try assumption.
  destruct (Pos.eqb_spec 3 l); [congruence | assumption].
Qed.

Lemma Good_set_rw : ltac2:(tb__ "0|0|
SaS8S3dQ40A1S43R3A1SdeP1dR3A2S43Sd5R5R4R3A3A1F_;F_;Fv;Fi;Frho;").
Proof using Hargc.
  intros rho i v HG Hi. destruct HG; constructor; cbn; try assumption;
    match goal with |- (if Pos.eqb ?a ?b then _ else _) = _ => destruct (Pos.eqb_spec a b); [lia | assumption] end.
Qed.

Section GoodFacts.
Variable rho : valuation.
Hypothesis HG : Good rho.

Lemma G_v1 : ltac2:(tb__ "0|1|
S0S7S3eQ40M0SeVrho;SdP1A1A2A2S3eG0Vsp;A2A3"). Proof using HG. cbn. rewrite (g_v1 rho HG). reflexivity. Qed.
Lemma G_v3 : ltac2:(tb__ "0|0|
S0S7S3eQ40SeVrho;SdP3A1A2A2VENVC;A3").
Proof using HG Hargc Hent Hinp JI. cbn. rewrite (g_v3 rho HG). pose proof NU. apply Z_to_bv_small. rewrite mod64. lia. Qed.
Lemma G_v4 : ltac2:(tb__ "0|1|
S0S7S3eQ40M0SeVrho;SdP4A1A2A2S5cS3eG0Vsp;A2VSTR;A2A3").
Proof using HG Hargc Hent Hinp JI. cbn. rewrite (g_v4 rho HG). pose proof NU. apply Z_to_bv_small. rewrite mod64. lia. Qed.
Lemma G_v5 : ltac2:(tb__ "0|0|
S0S7S3eQ40SeVrho;SdP5A1A2A2S5dS2cS3dQ8A1Vargv0;A2A1A3").
Proof using HG Hargc Hent Hinp JI. cbn. rewrite (g_v5 rho HG). pose proof NU. apply Z_to_bv_small. rewrite mod64. lia. Qed.
Lemma G_v6 : ltac2:(tb__ "0|1|
S0S7S3eQ40M0SeVrho;SdP6A1A2A2S5cS3eG0Vsp;A2VRND;A2A3").
Proof using HG Hargc Hent Hinp JI. cbn. rewrite (g_v6 rho HG). pose proof NU. apply Z_to_bv_small. rewrite mod64. lia. Qed.
Lemma G_v25 : ltac2:(tb__ "0|0|
S0S7S3eQ40SeVrho;SdP19A1A2A2VA1;A3").
Proof using HG Hargc Hent Hinp JI. cbn [eval]. rewrite (g_v25 rho HG). pose proof NU. rewrite A1_eq. apply Z_to_bv_small. rewrite mod64. lia. Qed.
Lemma G_v27 : ltac2:(tb__ "0|0|
S0S7S3eQ40SeVrho;SdP1bA1A2A2VL3;A3").
Proof using HG Hargc Hent Hinp JI. cbn [eval]. rewrite (g_v27 rho HG). pose proof L3_ge. pose proof NU. apply Z_to_bv_small. rewrite mod64. lia. Qed.
Lemma G_v28 : ltac2:(tb__ "0|0|
S0S7S3eQ40SeVrho;SdP1cA1A2A2VN;A3").
Proof using HG Hargc Hent Hinp JI. cbn [eval]. rewrite (g_v28 rho HG). pose proof NU. apply Z_to_bv_small. rewrite mod64. lia. Qed.
Lemma G_rl3 : ltac2:(tb__ "0|0|
S0S2bS3dQ8A1A1ScVrho;P3A2Vtail1;A3"). Proof using HG. exact (g_rl3 rho HG). Qed.
Let ADD := J_add rho.
Let LIT := J_lit rho.
Let SOFF := J_soff_small rho.
Let SOFFL := J_soff_lit rho.
Lemma G_sll3 : ltac2:(tb__ "0|0|
S0S7S3eQ40SeVrho;S12S79SdP3A1S11Z3A1A3A2A2S65Z8VENVC;A2A3").
Proof using HG Hargc Hent Hinp JI. pose proof NU. apply (J_sll3 rho 3 ENVC G_v3). lia. Qed.

Definition lit_of (e : sv) : option Z := ltac2:(tb__ "0|6|
SbS2fS7A1M0Le;Ve;S7S2dG0L_;S3cS62S63S5eZ2Z28A2M1A1R1A2S62R1G1A2A2S2eS7R1A2S38S7A1M2X2dx2Lc;S8G2Li;S78SbSbG2Lb;La;M3Lop;M4G4S7aG3Lop;M5G5S2dS9SbG2La;Lw;Lsgn;S8SbS7G2Lk;Li;Ll;Xbx8").
Definition add1_of (e : sv) : option Z := ltac2:(tb__ "0|4|
SbS2fS7A1M0Le;Ve;S7S38S7A1M1Lz;S8G1Li;S78SbSbS78G0Lop;R3S2dG0L_;S14R2SdP1A1A2ScaR1A1G1X2dx2G1G1G1G1G1G1G1G1G1X78xaLc;La;Lop;S78SbSbG1Lb;La;M2Lop;S7aG2Lop;M3G3S2dS9SbG1La;Lw;Lsgn;S8SbS7G1Lk;Li;Ll;Xbx8").
Definition AUXB : sv := ltac2:(tb__ "0|0|
S12S77S12S77S12S77SdP1A1S11Z10A1A3S12S79SdP3A1S11Z3A1A3A3S11Z18A1A3").
Definition bval (e : sv) : option Z := ltac2:(tb__ "0|3|
S3eQ40Vsp;A2S7S2dS2fS7A1M0L_;M1S14Ve;SdP1A1A2S2eS7R1A2G1S14Ve;SdP4A1A2S2eS7S5cR1VSTR;A2A2G1S14Ve;SdP6A1A2S2eS7S5cR1VRND;A2A2G1S14Ve;SdP19A1A2S2eS7VA1;A2G1S14Ve;S11Z0M2A1A2S2eS7G2A2G1S14Ve;Sd0A2S2eS7S5cS5cS5cR1Z10A2S65Z8VENVC;A2A2Z18A2A2G0G0Lx;SccVe;A1S7S2eS7S5cR2R1A2A2Lc;S38S7A1X2fx2X2dx2X2dx2X2dx2X2dx2X2dx2X2dx2Tb;").
Definition add28_of (e : sv) : option Z := ltac2:(tb__ "0|4|
SbS2fS7A1M0Le;Ve;S7S38S7A1M1Lz;S8G1Li;S78SbSbS78G0Lop;R3S2dG0L_;S14R2SdP1cA1A2ScaR1A1G1X2dx2G1G1G1G1G1G1G1G1G1X78xaLc;La;Lop;S78SbSbG1Lb;La;M2Lop;S7aG2Lop;M3G3S2dS9SbG1La;Lw;Lsgn;S8SbS7G1Lk;Li;Ll;Xbx8").
Definition oval (e : sv) : option Z := ltac2:(tb__ "0|4|
S2dS2fS7A1M0L_;M1S14Ve;SdP1bA1A2S2eS7VL3;A2G1S14Ve;SdP1cA1A2S2eS7VN;A2G1S14Ve;S12S77SdP5A1S11Z1M2A1A3A2S2eS7S5cS5dS2cS3dQ8A1Vargv0;A2A1G2A2A2G1S14Ve;S12S77S12S79SdP3A1S11Z3A1A3S11Z8M3A1A3A2S2eS7S5cS65G3VENVC;A2G3A2A2G0G0Lx;ScdVe;A1S7S2eS7S5cVN;R1A2A2Lc;ScaVe;A1X2fx2X2dx2X2dx2X2dx2X2dx2").
Definition shape_rng (sh : sv * sv * sv) : option (Z * Z) := ltac2:(tb__ "0|5|
S35S35SbSbA2M0SbA2S2fS35S7S7A2M1A1M2Lsh;Vsh;G0SbG0G2Lp;R2SbSbS2fS7A1G2Lx;M3SceR2A1S7G3ScbR2A1S7G3ScbR5A1S7S2eG1S37S7S7S5cR3R2A2S5cR3R1A2A4A2Lh;S38G1A1M4X2fx2Ll;G4X2fx2Lx;G4X2fx2Llo;Lb;X35x1Lhi;Lp;X35x1").

Lemma lit_of_sound : ltac2:(tb__ "0|1|
SbS7S0S2fS7A1ScaR2A1S2eS7R1A2A3S1S0SbR3S11R2A1A3S1S5bS63S5eZ2Z28A2M0A1R2A2S5bR2G0A2A2A2F_;Fc;Fe;").
Proof using .
  intros e c H. destruct e; cbn -[Z.pow Z.leb Z.opp] in H; try discriminate.
  destruct (_ && _) eqn:E; [|discriminate]. injection H as <-.
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. auto.
Qed.

Lemma add1_of_sound : ltac2:(tb__ "0|1|
SbS7S0S2fS7A1SccR2A1S2eS7R1A2A3S1S0SbR3S12S77SdP1A1S11R2A1A3A3S1S5bS63S5eZ2Z28A2M0A1R2A2S5bR2G0A2A2A2F_;Fc;Fe;").
Proof using .
  intros e c H. destruct e as [| |op a d| | | | |]; cbn -[lit_of sv_eqb] in H; try discriminate.
  destruct op; try discriminate. destruct (sv_eqb a (SVar 1)) eqn:E; [|discriminate].
  apply sv_eqb_sound in E. subst a. destruct (lit_of_sound d c H) as [-> Hc]. auto.
Qed.

Lemma add28_of_sound : ltac2:(tb__ "0|1|
SbS7S0S2fS7A1ScdR2A1S2eS7R1A2A3S1S0SbR3S12S77SdP1cA1S11R2A1A3A3S1S5bS63S5eZ2Z28A2M0A1R2A2S5bR2G0A2A2A2F_;Fc;Fe;").
Proof using .
  intros e c H. destruct e as [| |op a d| | | | |]; cbn -[lit_of sv_eqb] in H; try discriminate.
  destruct op; try discriminate. destruct (sv_eqb a (SVar 28)) eqn:E; [|discriminate].
  apply sv_eqb_sound in E. subst a. destruct (lit_of_sound d c H) as [-> Hc]. auto.
Qed.

Ltac sv_case H :=
  match type of H with
  | (if sv_eqb ?e ?p then _ else _) = _ =>
      let E := fresh "E" in destruct (sv_eqb e p) eqn:E; [apply sv_eqb_sound in E; subst e; injection H as <-|clear E]
  end.

Lemma bval_sound : ltac2:(tb__ "0|0|
SbS7S0S2fS7A1SceR2A1S2eS7R1A2A3S0S7S3eQ40SeVrho;R3A2A2R2A3F_;Fx;Fe;").
Proof using HG Hargc Hent Hinp.
  pose proof NU as NU'. pose proof L3_ge as HL3.
  intros e x H. unfold bval in H.
  sv_case H. { exact G_v1. }
  sv_case H. { exact G_v4. }
  sv_case H. { exact G_v6. }
  sv_case H. { exact G_v25. }
  sv_case H. { apply LIT. lia. }
  sv_case H. { unfold AUXB.
    apply (ADD _ _ (bv_unsigned sp + 16 + 8 * ENVC) 24); [| apply LIT; lia | lia | lia | lia].
    apply (ADD _ _ (bv_unsigned sp + 16) (8 * ENVC)); [| exact G_sll3 | lia | lia | lia].
    apply (ADD _ _ _ _ G_v1); [apply LIT; lia | lia | lia | lia]. }
  destruct (add1_of e) as [c|] eqn:Ea; [|discriminate]. injection H as <-.
  destruct (add1_of_sound e c Ea) as [-> Hc].
  cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned.
  pose proof G_v1 as V1. cbn [eval] in V1. rewrite V1.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.

Lemma oval_sound : ltac2:(tb__ "0|1|
SbS7S0S2fS7A1ScbR2A1S2eS7R1A2A3S1S0S7S1cVrho;R3A2R2A3S1S5bS63S5eZ2Z3eA2M0A1R2A2S60R2G0A2A2A2F_;Fx;Fe;").
Proof using HG Hargc Hent Hinp JI.
  pose proof NU as NU'. pose proof L3_ge as HL3.
  intros e x H. unfold oval in H.
  sv_case H. { split; [apply SOFF; [exact G_v27 | lia] | lia]. }
  sv_case H. { split; [apply SOFF; [exact G_v28 | lia] | lia]. }
  sv_case H. { split; [|lia]. apply SOFF; [|lia]. apply (ADD _ _ _ _ G_v5); [apply LIT; lia | lia | lia | lia]. }
  sv_case H. { split; [|lia]. apply SOFF; [|lia]. apply (ADD _ _ _ _ G_sll3); [apply LIT; lia | lia | lia | lia]. }
  destruct (add28_of e) as [c|] eqn:Ea.
  { injection H as <-. destruct (add28_of_sound e c Ea) as [-> Hc].
    split; [|lia]. apply (soff_add_small rho _ _ _ G_v28); lia. }
  destruct (lit_of_sound e x H) as [-> Hc].
  split; [|lia]. rewrite soff_lit. apply snorm_id. unfold smin, smax. lia.
Qed.

Lemma shape_range : ltac2:(tb__ "0|1|
SfS35S7S7A2M0S0S2fG0A1ScfSc6R2A1A1S2eG0R1A2A3S0G0S23Vrho;R3A2R2A3F_;Fr;Fo;").
Proof using HG Hargc Hent Hinp.
  intros [base lo hi cells d] r H. unfold shape_rng, obj_rng in H. cbn [ob_base ob_lo ob_hi] in H.
  destruct (bval base) as [x|] eqn:Eb; [|discriminate].
  destruct (oval lo) as [l|] eqn:El; [|discriminate]. destruct (oval hi) as [h|] eqn:Eh; [|discriminate].
  injection H as <-. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite (bval_sound _ _ Eb), (proj1 (oval_sound _ _ El)), (proj1 (oval_sound _ _ Eh)). reflexivity.
Qed.

Lemma shapes_disjoint : ltac2:(tb__ "0|1|
S2bSfA1S7S7S0S2dSbdSfSfS2fS35S7S7A2M0A1S2dLx;ScfSc6R1A1A1G0G0S2dLp;R1S7S7S39S39S39S62R1R2A2S62R5R6A2A2S62R1R6A2A2S62R5R2A2A2Lb;La;X35x1Lp;S36X2fx2Lo;R3A3S34A3S74SfSfS25S23Vrho;R1A2S37S7S7R4R3A4A2Lo;R4A3F_;Fhi;Flo;Fobjs;").
Proof using HG Hargc Hent Hinp.
  intros objs lo hi H. apply Forall_forall. intros o Hin.
  pose proof (proj1 (forallb_forall _ _) H o Hin) as Ho. cbn beta in Ho.
  destruct (shape_rng (obj_rng o)) as [[a b]|] eqn:E; [|discriminate].
  rewrite (shape_range o (a, b) E). unfold ranges_disjoint. cbn [fst snd]. lia.
Qed.
End GoodFacts.

Ltac solve_disj HG :=
  pose proof A1_eq; pose proof NU; pose proof L3_ge;
  apply Forall_forall; let Hin := fresh "HIn" in intros o Hin;
  repeat (destruct Hin as [<-|Hin];
          [erewrite (shape_range _ HG) by reflexivity; unfold ranges_disjoint; cbn [fst snd]; lia|]);
  destruct Hin.

(* The assertions the per-flag lemmas below share; none of them depends on the flag. *)
Definition Q_at (S : sstate) (n : nat) : assn := ltac2:(tb__ "0|0|
S66S2SaSaS1S43R1A1S40S6S4fS44Vn;A1Vmd0;A2VS;R1R2A5A2Lrho;A2Lw;").
Definition PRw (bs1 bs2 : list byte) (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
S1S0S2bS3dQ8A1M0A1M1ScVrho1;P5A2Vbs1;A3S1S0G1ScVrho1;P6A2Vbs2;A3S1S0S7S3eQ40M2S15Vrho1;PdA2A2S5dS2cG0Vbs1;A2A1A3S0S7S3eG2S15Vrho1;PfA2A2S5dS2cG0Vbs2;A2A1A3A2A2A2").
Definition GoodS (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S1S43Vrho;A1S0S2bS3dQ8A1A1ScVrho;P7A2Vargv1;A3A2").
Definition QS_at (S : sstate) (n : nat) : assn := ltac2:(tb__ "0|0|
S66S2SaSaS1S47R1A1S40S6S4fS44Vn;A1Vmd0;A2VS;R1R2A5A2Lrho;A2Lw;").
Definition V70 : Z := 4 * (A1 / 4).
Definition PRloc (n : Z) (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
S1S0S2bS3dQ8A1M0A1ScVrho1;P7A2S71G0S64Vn;A1M1ScVrho1;P3A2M2A3A3Sb1G1S2cG0G2A2A2A2").

(* LPS 727298f3: the states of the cannot-open path depend on the run's CONFIG_RSEQ flag
   (Drv_copen__G1.v); the lemmas below are stated for the run's flag [rq]. *)
Section PerR.
Variable rq : bool.
Hypothesis Hrq : kb_rseq (in_kernel inp) = rq.

(* The auxv object of the path's states is 464 bytes with CONFIG_RSEQ, 432 without (Lib/InitState.v
   [O_aux]); [NU] places it below the random bytes and the strings. *)
Lemma AUXSZ : AUX = if rq then 464 else 432.
Proof using Hrq. unfold AUX. rewrite Hrq. destruct rq; vm_compute; reflexivity. Qed.

Ltac solve_disjr HG := pose proof AUXSZ as AX; destruct rq; cbv beta iota in AX; solve_disj HG.
Ltac by_r t := destruct rq; [exact (t true) | exact (t false)].


Lemma co_intro : forall (rho : valuation) (w : world),
  J25 sp mb draw inp rho -> SP segs (Kx [] md0) (S_operr rq) rho w ->
  exists rho' : valuation, Good rho' /\ SP segs (Kx [] md0) (S_co rq) rho' w.
Proof using Hargc Hent Hinp Hrq.
  intros rho [tr [ms md]] [HJ H25] [Hsm Hk]. pose proof NU as NU'. pose proof L3_ge as HL3. pose proof length_tail1 as LT1.
  destruct (S_coR_next rq) as [NxR Nx0].

  pose proof (smatch_xforms segs xs_co rho (S_operr rq) (S_co0 rq) _ (xs_co_ok rq) Hsm) as Hsm0.
  destruct (smatch_release_obj segs rho (S_co0 rq) _ (ss_objs (S_coR rq)) (lastobj (S_co0 rq)) (ss_next (S_co0 rq)) Hsm0 (S_co0_objs rq)
              ltac:(rewrite Nx0; by_r swf_S_coR)) as (m' & Hsm1 & Hout & Hin & HoR & Hrom).
  cbn [w_cfg cfg_ms] in Hin, HoR, Hrom.
  set (rho1 := set_rm rho m') in Hsm1.
  assert (Hsm1' : smatch segs rho1 (S_coR rq) (tr, mkCfg ms md)) by (rewrite Nx0 in Hsm1; destruct rq; exact Hsm1). clear Hsm1.

  assert (RR : obj_range rho (lastobj (S_co0 rq)) = (bv_unsigned sp + RND, bv_unsigned sp + RND + 16)).
  { rewrite (last_co0 rq). unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
    rewrite (J_v6 segs pcU phU sp brk mb draw inp Hsp Hinp Hlaunch rho HJ). rewrite !soff_lit_small by lia. unfold RND. f_equal; lia. }
  (* The random bytes of the released object lie at [rand_off] of the launch image (Lib/InitStrs.v
     [region_rnd]), below the strings. *)
  assert (PR : forall a, m' a = ms_mem (ms0 segs pcU phU sp mb draw inp) a).
  { intros a. destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned sp + RND)) as [Hlt|Hge];
      [rewrite Hout; [apply (ji_mem _ _ _ _ _ _ _ _ HJ) | rewrite RR; unfold in_rng; cbn [fst snd]; lia]|].
    destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned sp + RND + 16)) as [Hlt2|Hge2];
      [|rewrite Hout; [apply (ji_mem _ _ _ _ _ _ _ _ HJ) | rewrite RR; unfold in_rng; cbn [fst snd]; lia]].
    rewrite Hin by (rewrite RR; unfold in_rng; cbn [fst snd]; lia).

    rewrite (last_co0 rq) in HoR. pose proof HoR as (_ & Hw & Hc & _ & _).
    unfold obj_lo_of, obj_hi_of in Hw, Hc. cbn [ob_base ob_lo ob_hi ob_dflt ob_cells] in Hw, Hc.
    pose proof (J_v6 segs pcU phU sp brk mb draw inp Hsp Hinp Hlaunch rho HJ) as V6. fold RND in V6.
    rewrite V6 in Hw. rewrite !soff_lit_small in Hw by lia.
    set (off := bv_unsigned a - (bv_unsigned sp + RND)).
    assert (Ea : a = Z_to_bv 64 (bv_unsigned sp + RND + off)) by (apply bv_eq; rewrite Z_to_bv_small; [lia | rewrite mod64; lia]).
    assert (RB : rd ms a = Some (nth (Z.to_nat off) (rand_bytes draw) (Z_to_bv 8 0))).
    { apply Forall_cons_iff in Hc as [C9 Hc]. apply Forall_cons_iff in Hc as [C10 _].
      destruct C9 as (_ & _ & R9). destruct C10 as (_ & _ & R10). cbn [c_off c_width c_val Z.to_nat Pos.to_nat] in R9, R10.
      rewrite !soff_lit_small in R9, R10 by lia. unfold oaddr in R9, R10. rewrite V6 in R9, R10.
      change (eval rho (SVar 9)) with (rw rho 9) in R9. change (eval rho (SVar 10)) with (rw rho 10) in R10.
      rewrite (ji_rnd0 _ _ _ _ _ _ _ _ HJ) in R9. rewrite (ji_rnd1 _ _ _ _ _ _ _ _ HJ) in R10.
      destruct (Nat.lt_ge_cases (Z.to_nat off) 8) as [Hlt8|Hge8].
      - pose proof (rd_bytes_nth ms 8 _ _ (Z.to_nat off) R9 Hlt8 ltac:(rewrite Z_to_bv_small by (rewrite mod64; lia); lia)) as X.
        rewrite Z_to_bv_small in X by (rewrite mod64; lia).
        replace (bv_unsigned sp + RND + 0 + Z.of_nat (Z.to_nat off)) with (bv_unsigned sp + RND + off) in X by lia. rewrite <- Ea in X.
        rewrite X. f_equal. pose proof (rand_bytes_nth draw 0 (Z.to_nat off) ltac:(lia) Hlt8) as RBN.
        replace (8 * 0 + Z.to_nat off)%nat with (Z.to_nat off) in RBN by lia. rewrite RBN. reflexivity.
      - pose proof (rd_bytes_nth ms 8 _ _ (Z.to_nat off - 8) R10 ltac:(lia) ltac:(rewrite Z_to_bv_small by (rewrite mod64; lia); lia)) as X.
        rewrite Z_to_bv_small in X by (rewrite mod64; lia).
        replace (bv_unsigned sp + RND + 8 + Z.of_nat (Z.to_nat off - 8)) with (bv_unsigned sp + RND + off) in X by lia. rewrite <- Ea in X.
        rewrite X. f_equal. pose proof (rand_bytes_nth draw 1 (Z.to_nat off - 8) ltac:(lia) ltac:(lia)) as RBN.
        replace (8 * 1 + (Z.to_nat off - 8))%nat with (Z.to_nat off) in RBN by lia. rewrite RBN. reflexivity. }
    rewrite Ea in RB |- *. rewrite (ms_mem_some_high segs ms _ (nth (Z.to_nat off) (rand_bytes draw) (Z_to_bv 8 0))).
    - replace (bv_unsigned sp + RND + off) with (bv_unsigned sp + (Z.of_nat (rand_off inp) + Z.of_nat (Z.to_nat off))) by (unfold RND; lia).
      rewrite (ms0_mem_region segs pcU phU sp brk mb draw inp Hsp Hinp Hlaunch _ (rand_bytes draw) (Z.to_nat off)
                 (region_rnd pcU phU sp brk mb draw inp Hlaunch)) by (rewrite length_rand_bytes; lia).
      reflexivity.
    - rewrite Z_to_bv_small by (rewrite mod64; lia). change segs with segsU. rewrite segs_topU. lia.
    - apply Hw; [lia | reflexivity].
    - exact RB. }
  assert (HJ1 : JI rho1).
  { destruct HJ; constructor; cbn [rho1 set_rm rw rl rm]; assumption. }

  set (rho2 := rho_set_rw (rho_set_rw (rho_set_rl rho1 3 tail1) 27 (Z_to_bv 64 L3)) 28 (Z_to_bv 64 N)).
  assert (Hsm2 : smatch segs rho2 (S_coR rq) (tr, mkCfg ms md)).
  { eapply smatch_agree; [| apply smatch_set_rl; [exact (norl3_S_coR rq) | exact Hsm1']].
    rewrite NxR. apply (agree_below_trans 27 _ (rho_set_rw (rho_set_rl rho1 3 tail1) 27 (Z_to_bv 64 L3))); apply agree_below_set_rw; lia. }
  assert (HJ2 : JI rho2).
  { apply Jinit_set_rw; [|lia]. apply Jinit_set_rw; [|lia]. apply Jinit_set_rl; [exact HJ1 | lia | lia]. }
  assert (HG2 : Good rho2) by (apply (Good_of_JI rho2 HJ2); [cbn; exact H25 | reflexivity | reflexivity | reflexivity]).
  exists rho2. split; [exact HG2|]. split; [|exact Hk].

  rewrite <- (S_co_eq rq). apply smatch_add_facts; [| | destruct rq; reflexivity].
  - rewrite <- (S_cow_eq rq). unfold app_objs.
    apply (smatch_carve_listobj segs rho2 (S_coR rq) _ (SVar 25) (SLit 0) (SVar 27) 0 L3 (DList 3) 3 29 Hsm2 eq_refl);
      rewrite ?(G_v25 rho2 HG2).
    + by_r swf_S_cow.
    + apply soff_lit_small. lia.
    + apply (J_soff_small rho2 _ _ (G_v27 rho2 HG2)). lia.
    + lia.
    + lia.
    + rewrite A1_eq. lia.
    + rewrite A1_eq. lia.
    + rewrite (G_rl3 rho2 HG2), LT1. lia.
    + solve_disjr HG2.
    + intros off Hoff _. cbn [rho2 rho1 rho_set_rw rho_set_rl set_rm rm].
      replace (A1 + off) with (A1 + Z.of_nat (Z.to_nat off)) by lia.
      unfold wview. set (a := Z_to_bv 64 _). change (m' a) with (rm rho2 a). subst a. rewrite (tail1_frame rho2 HJ2) by lia. discriminate.
    + intros off Hoff. cbn [rho2 rho1 rho_set_rw rho_set_rl set_rm rm rl]. rewrite Pos.eqb_refl.
      replace (A1 + off) with (A1 + Z.of_nat (Z.to_nat off)) by lia.
      unfold rd_of. set (a := Z_to_bv 64 _). change (m' a) with (rm rho2 a). subst a. rewrite (tail1_frame rho2 HJ2) by lia.
      rewrite Z.sub_0_r. reflexivity.
  - pose proof (G_v27 rho2 HG2) as V27. pose proof (G_v28 rho2 HG2) as V28. cbn [eval] in V27, V28.
    unfold F_co. repeat constructor; cbn [holds]; unfold bv_leu.
    + rewrite (J_add rho2 (SVar 28) (SLit 10) N 10); [| exact V28 | apply U_lit64; lia | lia | lia | lia].
      change (eval rho2 (SVar 27)) with (rw rho2 27). rewrite V27. lia.
    + change (eval rho2 (SVar 27)) with (rw rho2 27). rewrite V27, U_lit64 by lia. lia.
    + change (eval rho2 (SVar 28)) with (rw rho2 28). rewrite V28, U_lit64 by lia. lia.
    +
      pose proof (G_v25 rho2 HG2) as V25. pose proof A1_eq as EA1.
      rewrite (J_add rho2 (SVar 25) (SVar 28) A1 N); [| exact V25 | exact V28 | lia | lia | lia].
      rewrite U_lit64 by lia. lia.
Qed.


Lemma SP_add1 : ltac2:(tb__ "0|0|
S2bS52A1S53OF_;F_;S10SaS66S13S40S6R5R4R3R2A5S18R4R2A2S0S2dS29S16R6A1R3A2S34A3S40S6R8Sb4S32S13R4S30S13A1A3R7A2R6R5A5F_;F_;F_;Ff;Fw;Frho;FS;FK;").
Proof using .
  intros K S rho w f [Hsm Hk] Hf Hb. split; [|exact Hk]. apply smatch_add_facts; [exact Hsm | constructor; [exact Hf|constructor] | cbn; rewrite Hb; reflexivity].
Qed.
Lemma hd_fact : ltac2:(tb__ "0|1|
SaS10S13S2bS13A1M0S66S2bS52A1S53OF_;F_;S0G0S1aR5A1S32S13R4R3A3A3S40S6R2R6R7R3A5S18R8R6A2F_;F_;FK;Fw;FF;Ff;FS;Frho;").
Proof using . intros rho S f F w K E Hsp. eapply SP_fact; [exact Hsp|]. rewrite E. left. reflexivity. Qed.

Lemma FirstNul_call : forall (rho : valuation) (ms : machine_state),
  Good rho -> FirstNul (rho_sub (rho_absorb rho (R_cs rq) ms) (s_cs rq)).
Proof using Hargc Hent Hinp.
  intros rho ms HG. unfold FirstNul. rewrite rl_call, rw_call, (s_cs_16 rq).
  rewrite (G_rl3 rho HG), (G_v28 rho HG). unfold nthb, N. rewrite Nat2Z.id. split.
  - rewrite tail1_nul. reflexivity.
  - intros i Hi E. apply (argv1_nonul (Z.to_nat i) ltac:(lia)). apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma ovf_contra : ltac2:(tb__ "0|0|
SaS10S66S2bS52A1S53OF_;F_;S43R4A1SbbS13S9fS1aR4A1A3S40S6R3R5R6R4A5S3F_;F_;F_;FK;Fw;FS;Frho;").
Proof using Hargc Hent Hinp.
  intros rho S w K HG Hin Hsp.
  pose proof (SP_fact _ _ _ _ _ Hsp Hin) as Hf. unfold BNZ28 in Hf. apply (proj1 (holds_BNZ rho (SVar 28))) in Hf.
  apply Hf. rewrite (G_rl3 rho HG), (G_v28 rho HG). unfold nthb, N. rewrite Nat2Z.id, tail1_nul. reflexivity.
Qed.

Lemma L_cs_post : forall rho : valuation, Good rho -> Forall (holds rho) (ss_facts (E_cs rq)) ->
  triple segs ok (SP segs (Kx (TR 0) md0) (T_imp rq) rho) (Q_at (T_cs1 rq) 0).
Proof using .
  intros rho2 HG2 HF2.
  apply (post_path segs ok (Kx (TR 0) md0) (T_imp rq) (T_cs rq) (ss_facts (E_cs rq)) xs_post rho2 _ (fb_cs2 rq) (xs_post_ok rq) HF2).
  apply triple_facts. intros HFT.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hsp. exists rho2. split; [exact HG2|].
  eapply (SP_restate segs _ rho2 (T_cs rq) (T_cs1 rq) w); [exact (swf_T_cs1 rq) | exact (diff_cs rq) | | constructor | exact Hsp].
  constructor; [|constructor]. cbn [fst snd]. exact (proj1 (Forall_forall _ _) HFT _ (fact_T_cs rq)).
Qed.

Lemma L_call : forall rho : valuation, Good rho ->
  triple segs ok (SP segs (Kx (TR 0) md0) (S_co rq) rho) (Q_at (T_cs1 rq) 0).
Proof using Hargc Hent Hinp HokK Hrq.
  intros rho HG.
  eapply run_tr; [exact (run_co rq) | destruct rq; reflexivity | apply okf |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  pose proof (Good_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HG) as HG1.
  apply (call_path segs FirstNul ok (Kx (TR 0) md0) (Kx (TR 0) md0) (E_cs rq) (E_csX rq) Pre_strnlen xs_pre (s_cs rq) (R_cs rq) Posts_strnlen _ rho1
           (xs_pre_ok rq) (efr_cs rq) (chk_cs rq) (fb_cs rq)).
  - intros rho2 HF. apply strnlen_sum; [apply okf | exact HF].
  - intros ms _. apply FirstNul_call. exact HG1.
  - intros L rho2 [<-|[]] Hag2 HF2. cbn [lf_state]. replace (ss_next Pre_strnlen) with NF by reflexivity. rewrite (T_imp_eq rq).
    apply L_cs_post; [|exact HF2]. exact (Good_agree _ _ _ Hag2 ltac:(destruct rq; cbn; lia) HG1).
Qed.

Lemma eL_cs_post : forall rho : valuation, Good rho -> Forall (holds rho) (ss_facts (E_cs rq)) ->
  etriple segs (SP segs (Kx (TR 0) md0) (T_imp rq) rho) (Q_at (T_cs1 rq) 0).
Proof using .
  intros rho2 HG2 HF2.
  apply (epost_path segs (Kx (TR 0) md0) (T_imp rq) (T_cs rq) (ss_facts (E_cs rq)) xs_post rho2 _ (fb_cs2 rq) (xs_post_ok rq) HF2).
  apply etriple_facts. intros HFT w Hsp. exists w. split; [apply wsteps_refl|]. exists rho2. split; [exact HG2|].
  eapply (SP_restate segs _ rho2 (T_cs rq) (T_cs1 rq) w); [exact (swf_T_cs1 rq) | exact (diff_cs rq) | | constructor | exact Hsp].
  constructor; [|constructor]. cbn [fst snd]. exact (proj1 (Forall_forall _ _) HFT _ (fact_T_cs rq)).
Qed.

Lemma eL_call : forall rho : valuation, Good rho ->
  etriple segs (SP segs (Kx (TR 0) md0) (S_co rq) rho) (Q_at (T_cs1 rq) 0).
Proof using Hargc Hent Hinp Hrq.
  intros rho HG.
  eapply erun_tr; [exact (run_co rq) | destruct rq; reflexivity |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  pose proof (Good_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HG) as HG1.
  apply (ecall_path segs FirstNul (Kx (TR 0) md0) (Kx (TR 0) md0) (E_cs rq) (E_csX rq) Pre_strnlen xs_pre (s_cs rq) (R_cs rq) Posts_strnlen _ rho1
           (xs_pre_ok rq) (efr_cs rq) (chk_cs rq) (fb_cs rq)).
  - intros rho2 HF. apply strnlen_sum_ex. exact HF.
  - intros ms _. apply FirstNul_call. exact HG1.
  - intros L rho2 [<-|[]] Hag2 HF2. cbn [lf_state]. replace (ss_next Pre_strnlen) with NF by reflexivity. rewrite (T_imp_eq rq).
    apply eL_cs_post; [|exact HF2]. exact (Good_agree _ _ _ Hag2 ltac:(destruct rq; cbn; lia) HG1).
Qed.

Lemma T64_intro : forall (rho : valuation) (w : world), Good rho -> 64 <= N ->
  SP segs (Kx (TR 0) md0) (T_cs1 rq) rho w -> SP segs (Kx (TR 0) md0) (T64 rq) rho w.
Proof using Hargc Hent Hinp Hrq.
  intros rho w HG HN Hsp. unfold T64. apply SP_add1; [exact Hsp | | destruct rq; reflexivity].
  cbn [holds]. unfold bv_leu. rewrite U_lit64 by lia. rewrite (G_v28 rho HG). lia.
Qed.

Lemma L_64 : 64 <= N -> forall rho : valuation, Good rho ->
  triple segs ok (SP segs (Kx (TR 0) md0) (T_cs1 rq) rho) (Q_at (E_W1 rq) 0).
Proof using Hargc Hent Hinp HokK Hrq.
  intros HN rho HG.
  eapply triple_conseq with (P := SP segs (Kx (TR 0) md0) (T64 rq) rho); [intros w Hw; exact (T64_intro rho w HG HN Hw) | intros w Hw; exact Hw |].
  eapply run_tr; [exact (run_64 rq) | destruct rq; reflexivity | apply okf |].
  intros L rho1 [<-|[<-|[]]] Hag1; cbn [lf_state].
  - pose proof (Good_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HG) as HG1.
    intros n Hg w Hw. exfalso. exact (ovf_contra rho1 (X_ovf rq) w _ HG1 (fact_ovf rq) Hw).
  - eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. exists rho1. split; [exact (Good_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HG) | exact Hw].
Qed.

Lemma eL_64 : 64 <= N -> forall rho : valuation, Good rho ->
  etriple segs (SP segs (Kx (TR 0) md0) (T_cs1 rq) rho) (Q_at (E_W1 rq) 0).
Proof using Hargc Hent Hinp Hrq.
  intros HN rho HG.
  eapply etriple_conseq with (P := SP segs (Kx (TR 0) md0) (T64 rq) rho); [intros w Hw; exact (T64_intro rho w HG HN Hw) | intros w Hw; exact Hw |].
  eapply erun_tr; [exact (run_64 rq) | destruct rq; reflexivity |].
  intros L rho1 [<-|[<-|[]]] Hag1; cbn [lf_state]; intros w Hw.
  - exfalso. exact (ovf_contra rho1 (X_ovf rq) w _ (Good_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HG) (fact_ovf rq) Hw).
  - exists w. split; [apply wsteps_refl|]. exists rho1. split; [exact (Good_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HG) | exact Hw].
Qed.

Lemma map_beval_BL_co : ltac2:(tb__ "0|1|
SaS0S2bS3dQ8A1M0A1S75S7dG0S7eR1A1S9eA4S48A3Frho;").
Proof using . intros rho. reflexivity. Qed.

Lemma rd_high_mem : ltac2:(tb__ "0|3|
Sc3S3dQ40M0A1S3dQ8A1M1S28S6R3A2S5bSefS6A1S3eG0R3A2A2S0S2fG1A1M2S26R5R4A2S2eG1R3A2A3S0G2Sc4R6R5A2S2eG1R4A2A3F_;F_;F_;Fb;Fa;Fms;").
Proof using inp.
  intros ms a b Hrom Ha Hr. unfold rd, ms_read_byte in Hr. destruct (ms_mem ms a) as [b'|] eqn:E; [exact Hr|].
  rewrite (Hrom a) in Hr. rewrite (image_byte_none_high segs a Ha) in Hr. discriminate.
Qed.

Lemma w1_intro : forall (rho : valuation) (w : world), Good rho ->
  SP segs (Kx (TR 0) md0) (E_W1 rq) rho w ->
  exists rho' : valuation, Good rho' /\ rl rho' 5 = M1 /\ rl rho' 6 = argv1 /\ SP segs (Kx (TR 0) md0) (E_W1c rq) rho' w.
Proof using Hargc Hent Hinp Hrq.
  intros rho [tr [ms md]] HG [Hsm Hk]. pose proof NU as NU'. pose proof L3_ge as HL3. pose proof length_tail1 as LT1.

  pose proof (smatch_xforms segs xs_w1 rho (E_W1 rq) (E_W1x rq) _ (xs_w1_ok rq) Hsm) as Hsm1.
  destruct (obj3_w1 rq) as (Hn3 & Hlo3 & Hhi3 & Hwr3 & Harr3).
  pose proof (smatch_obj_to_list segs rho (E_W1x rq) _ 3 5 (obj (E_W1x rq) 3) (-560) (-543) BL_co Hsm1 Hn3 Hlo3 Hhi3
                ltac:(lia) ltac:(lia) Hwr3 Harr3 (cb_w1 rq) (norl5_w1 rq)) as Hsm2.
  rewrite (E_W1l_eq rq), map_beval_BL_co in Hsm2.
  set (rho1 := rho_set_rl rho 5 M1) in Hsm2.
  assert (HG1 : Good rho1) by (apply Good_set_rl; [exact HG | lia]).

  destruct (smatch_release_obj segs rho1 (E_W1l rq) _ (ss_objs (E_W1r rq)) O_str1 (ss_next (E_W1l rq)) Hsm2 (E_W1l_objs rq)
              ltac:(by_r swf_E_W1r))
    as (m' & Hsm3 & Hout & Hin & Ho1 & Hrom).
  cbn [w_cfg cfg_ms] in Hin, Ho1, Hrom.
  set (rho2 := set_rm rho1 m') in Hsm3.
  assert (HG2 : Good rho2) by (apply Good_rm; exact HG1).
  assert (R1 : obj_range rho1 O_str1 = (A1, A1 + L3)).
  { unfold obj_range, obj_lo_of, obj_hi_of, O_str1. cbn [ob_base ob_lo ob_hi]. rewrite (G_v25 rho1 HG1).
    rewrite soff_lit_small by lia. rewrite (J_soff_small rho1 _ _ (G_v27 rho1 HG1)) by lia. f_equal; lia. }

  set (rho3 := rho_set_rl rho2 6 argv1).
  assert (Hsm4 : smatch segs rho3 (E_W1r rq) (tr, mkCfg ms md))
    by (apply smatch_set_rl; [exact (norl6_w1 rq) | destruct rq; exact Hsm3]).
  assert (HG3 : Good rho3) by (apply Good_set_rl; [exact HG2 | lia]).
  exists rho3. split; [exact HG3|]. split; [reflexivity|]. split; [reflexivity|]. split; [|exact Hk].
  rewrite <- (E_W1c_eq rq). unfold app_objs.
  apply (smatch_carve_listobj segs rho3 (E_W1r rq) _ (SVar 25) (SLit 0) (SVar 28) 0 N (DRom 6) 6 (ss_next (E_W1r rq)) Hsm4 eq_refl);
    rewrite ?(G_v25 rho3 HG3).
  - by_r swf_E_W1c.
  - apply soff_lit_small. lia.
  - apply (J_soff_small rho3 _ _ (G_v28 rho3 HG3)). lia.
  - lia.
  - lia.
  - rewrite A1_eq. lia.
  - rewrite A1_eq. lia.
  - cbn. unfold N. lia.
  - solve_disjr HG3.
  - intros off Hoff D. discriminate D.
  - intros off Hoff. cbn [rho3 rho2 rho1 rho_set_rl set_rm rm rl]. rewrite Pos.eqb_refl.
    rewrite (released_rd segs m' ms (fun a => in_rng (obj_range rho1 O_str1) (bv_unsigned a))); [| exact Hin | exact Hrom |].
    2:{ rewrite R1. unfold in_rng. cbn [fst snd]. rewrite Z_to_bv_small by (rewrite mod64, A1_eq; lia). lia. }
    pose proof (obj_bytes_list segs rho1 ms O_str1 3 off Ho1 eq_refl eq_refl) as RB.
    unfold obj_lo_of, obj_hi_of, O_str1 in RB. cbn [ob_base ob_lo ob_hi] in RB.
    rewrite (G_v25 rho1 HG1), soff_lit_small, (J_soff_small rho1 _ _ (G_v27 rho1 HG1)) in RB by lia.
    rewrite (RB ltac:(lia)). f_equal. rewrite !Z.sub_0_r. cbn [rl rho1 rho_set_rl]. rewrite (G_rl3 rho HG).
    rewrite tail1_head by (unfold N in Hoff; lia). apply app_nth1. unfold N in Hoff. lia.
Qed.

Lemma chw_eq : WLerr.chw = Z_to_bv 64 2. Proof using . reflexivity. Qed.

Lemma Kw_TR : ltac2:(tb__ "0|3|
S31S2bS3dQ8A1M0A1M1G1S31S2bS52A1S53S0G1S33G0R5R4A3M2S71G0S2cG0G2A2S72G0R6S45A3A3A3Sb6S4fS44R7A1Vmd0;A2R6R5R4R3R2A6S4fS44S70R8Sf3R5S2cG0S33G0R7R6A3A2A2A2A1Vmd0;R4R3A4F_;F_;Fmd;Ftr;Fk;Fbs2;Fbs1;Fn0;").
Proof using .
  intros n0 bs1 bs2 k tr md Hw (tr0 & [-> ->] & ->). split; [|reflexivity].
  unfold WLerr.TRk, WLerr.MSG, TR, wr. rewrite chw_eq, <- map_app. f_equal.
  set (m := length (bs1 ++ bs2)) in *. rewrite Hw, firstn_firstn. apply firstn_add_skipn.
Qed.

Lemma Kw_okf : ltac2:(tb__ "0|3|
S31S2bS3dQ8A1M0A1M1G1S31S0G1S33G0R3R2A3M2S71G0S2cG0G2A2S72G0R4S45A3A3A3S42S6Vok;Sb6S4fS44R5A1Vmd0;A2R4R3R2A4A3F_;Fk;Fbs2;Fbs1;Fn0;").
Proof using Hargc HokK.
  intros n0 bs1 bs2 k Hw. apply HokK. intros tr md HK. exact (Ktc _ md0 tr md (Kw_TR n0 bs1 bs2 k tr md Hw HK)).
Qed.
Lemma Kw_okp : ltac2:(tb__ "0|3|
S31S2bS3dQ8A1M0A1M1G1S31S0G1S33G0R3R2A3M2S71G0S2cG0G2A2S72G0R4S45A3A3A3Sd2S6Vok;Sb6S4fS44R5A1Vmd0;A2R4R3R2A4A3F_;Fk;Fbs2;Fbs1;Fn0;").
Proof using Hargc HokP.
  intros n0 bs1 bs2 k Hw. apply HokP. intros tr md HK. exact (Ktc _ md0 tr md (Kw_TR n0 bs1 bs2 k tr md Hw HK)).
Qed.
Lemma Kx_fd2 : ltac2:(tb__ "0|1|
S2bS52A1M0G0S53S4fR3Vmd0;R2R1A4S0S2fS54A1S57S55R2A1Sb9A2S2eS54S56Sb9A1A2A3F_;Fmd;Ftr;Ft;").
Proof using Hfds0 Hrdr0. intros t tr md [_ ->]. rewrite chw_eq. apply fd2. exact Hfds0. Qed.
(* LPS 08b1429: a nonempty writev needs the channel's reader ([writev_spec]'s SIGPIPE arm). *)
Lemma Kx_rdr : forall t tr md, Kx t md0 tr md -> m_channel_reader md = true.
Proof using Hrdr0. intros t tr md [_ ->]. exact Hrdr0. Qed.


Lemma wl2_call : ltac2:(tb__ "0|4|
S31S2bS3dQ8A1M0A1M1G1SaSb1U1S2cG0R3A2A2S0G1S33G0R4R3A3M2S71G0S2cG0G2A2S72G0R5S45A3A3A3S4cR5R4R3A3S68S6Vok;S40S6S4fS44R7A1Vmd0;A2M3Sd1R4A4S41S6Sb6G3R6R5S2cG0Sb7R6R5A2A2A4S16Sd1A1R4Sb8A5A4F_;F_;F_;Frho1;Fbs2;Fbs1;Fn0;").
Proof using A1 Hargc Hent Hfds0 Hrdr0 Hinp HokK HokP JI.
  intros n0 bs1 bs2 rho1 H1 Hw (H5 & H6 & H13 & H15).
  apply (WLerr.wl2_sum ok (Kx (TR n0) md0) rho1 bs1 bs2 H5 H6 H13 H15).
  - pose proof NU. unfold WLerr.MSG. apply (f_equal (@length byte)) in Hw. rewrite length_firstn, length_skipn, MSG_len in Hw.
    unfold max_write_total. unfold N in *. lia.
  - intros k. apply Kw_okf. exact Hw.
  - intros k. apply Kw_okp. exact Hw.
  - intros tr md HK. exact (Kx_fd2 _ _ _ HK).
  - intros tr md HK. exact (Kx_rdr _ _ _ HK).
  - exact H1.
Qed.

Lemma wl2_ecall : ltac2:(tb__ "0|4|
S31S2bS3dQ8A1M0A1M1G1SaSb1U1S2cG0R3A2A2S0G1S33G0R4R3A3M2S71G0S2cG0G2A2S72G0R5S45A3A3A3S4cR5R4R3A3S67S6S40S6S4fS44R7A1Vmd0;A2M3Sd1R4A4S41S6Sb6G3R6R5S2cG0Sb7R6R5A2A2A4S16Sd1A1R4Sb8A5A3F_;F_;F_;Frho1;Fbs2;Fbs1;Fn0;").
Proof using A1 Hargc Hent Hfds0 Hrdr0 Hinp JI.
  intros n0 bs1 bs2 rho1 H1 Hw (H5 & H6 & H13 & H15).
  apply (WLerr.wl2_sum_ex (Kx (TR n0) md0) rho1 bs1 bs2 H5 H6 H13 H15).
  - pose proof NU. unfold WLerr.MSG. apply (f_equal (@length byte)) in Hw. rewrite length_firstn, length_skipn, MSG_len in Hw.
    unfold max_write_total. unfold N in *. lia.
  - intros tr md HK. exact (Kx_fd2 _ _ _ HK).
  - intros tr md HK. exact (Kx_rdr _ _ _ HK).
  - exact H1.
Qed.

Lemma firstn_exact : ltac2:(tb__ "0|2|
S2bS3dQ8A1M0A1M1G1S0G1R2S71G0S2cG0R2A2S33G0R2R1A3A3A3Fb;Fa;").
Proof using . intros a b. induction a as [|x a IH]; [reflexivity|]. cbn. f_equal. exact IH. Qed.
Lemma firstn_exact3 : ltac2:(tb__ "0|3|
S2bS3dQ8A1M0A1M1G1G1S0G1S33G0R3R2A3M2S71G0S2cG0G2A2S33G0R3S33G0R2R1A3A3A3A3Fc;Fb;Fa;").
Proof using . intros a b c. induction a as [|x a IH]; cbn; [apply firstn_exact|]. f_equal. exact IH. Qed.

Lemma w1_window : ltac2:(tb__ "0|2|
S0S2bS3dQ8A1M0A1S33G0S48Vargv1;A3M1S71G0S2cG0G1A2S72G0U0S45A3A3A3").
Proof using . unfold MSG. cbn [skipn]. apply firstn_exact3. Qed.

Lemma L_W1 : forall rho : valuation, Good rho -> rl rho 5 = M1 -> rl rho 6 = argv1 ->
  triple segs ok (SP segs (Kx (TR 0) md0) (E_W1c rq) rho) (Q_at (T_D1 rq) (17 + length argv1)).
Proof using Hargc Hent Hfds0 Hrdr0 Hinp HokK HokP Hrq.
  intros rho HG H5 H6. destruct s_w1_vals as (S12 & S13 & S14 & S15).
  apply (call_path segs (PRw M1 argv1) ok (Kx (TR 0) md0) (WLerr.Kw (Kx (TR 0) md0) M1 argv1 (length (WLerr.MSG M1 argv1)))
           (E_W1c rq) (E_W1c rq) WLerrS.Pre_wl2 [] s_w1 (R_w1 rq) WLerr.Posts_wl _ rho
           eq_refl (efr_w1 rq) (chk_w1 rq) ltac:(rewrite (facts_w1c rq); exact (fb_w1 rq))).
  - intros rho1 HPR. apply (wl2_call 0 M1 argv1 rho1 ltac:(rewrite M1_len; lia) w1_window HPR).
  - intros ms _. unfold PRw. rewrite rl_call, !rw_call, S13, S15. split; [exact H5|]. split; [exact H6|].
    split; [rewrite U_lit64 by lia; reflexivity | exact (G_v28 rho HG)].
  - intros L rho' [<-|[]] Hag HF. cbn [lf_state]. rewrite (facts_w1c rq) in HF.
    change (ss_next WLerrS.Pre_wl2) with 92%positive. rewrite (T_D1i_eq rq).
    eapply triple_conseq with (P := SP segs (Kx (TR (17 + length argv1)) md0) (T_D1i rq) rho'); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [exact Hsm|]. apply (Kw_TR 0 M1 argv1 _ _ _ w1_window) in HK.
      unfold WLerr.MSG in HK. rewrite Nat.min_id, length_app, M1_len in HK. exact HK. }
    apply (post_path segs ok _ (T_D1i rq) (T_D1 rq) (ss_facts (E_W1 rq)) xs_d1 rho' _ (fb_d1 rq) (xs_d1_ok rq) HF).
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. exists rho'. split; [exact (Good_agree _ _ _ Hag ltac:(destruct rq; cbn; lia) HG) | exact Hw].
Qed.

Lemma eL_W1 : forall rho : valuation, Good rho -> rl rho 5 = M1 -> rl rho 6 = argv1 ->
  etriple segs (SP segs (Kx (TR 0) md0) (E_W1c rq) rho) (Q_at (T_D1 rq) (17 + length argv1)).
Proof using Hargc Hent Hfds0 Hrdr0 Hinp Hrq.
  intros rho HG H5 H6. destruct s_w1_vals as (S12 & S13 & S14 & S15).
  apply (ecall_path segs (PRw M1 argv1) (Kx (TR 0) md0) (WLerr.Kw (Kx (TR 0) md0) M1 argv1 (length (WLerr.MSG M1 argv1)))
           (E_W1c rq) (E_W1c rq) WLerrS.Pre_wl2 [] s_w1 (R_w1 rq) WLerr.Posts_wl _ rho
           eq_refl (efr_w1 rq) (chk_w1 rq) ltac:(rewrite (facts_w1c rq); exact (fb_w1 rq))).
  - intros rho1 HPR. apply (wl2_ecall 0 M1 argv1 rho1 ltac:(rewrite M1_len; lia) w1_window HPR).
  - intros ms _. unfold PRw. rewrite rl_call, !rw_call, S13, S15. split; [exact H5|]. split; [exact H6|].
    split; [rewrite U_lit64 by lia; reflexivity | exact (G_v28 rho HG)].
  - intros L rho' [<-|[]] Hag HF. cbn [lf_state]. rewrite (facts_w1c rq) in HF.
    change (ss_next WLerrS.Pre_wl2) with 92%positive. rewrite (T_D1i_eq rq).
    eapply etriple_conseq with (P := SP segs (Kx (TR (17 + length argv1)) md0) (T_D1i rq) rho'); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [exact Hsm|]. apply (Kw_TR 0 M1 argv1 _ _ _ w1_window) in HK.
      unfold WLerr.MSG in HK. rewrite Nat.min_id, length_app, M1_len in HK. exact HK. }
    apply (epost_path segs _ (T_D1i rq) (T_D1 rq) (ss_facts (E_W1 rq)) xs_d1 rho' _ (fb_d1 rq) (xs_d1_ok rq) HF).
    intros w Hw. exists w. split; [apply wsteps_refl|]. exists rho'. split; [exact (Good_agree _ _ _ Hag ltac:(destruct rq; cbn; lia) HG) | exact Hw].
Qed.

Lemma L_d1 : forall rho : valuation, Good rho ->
  triple segs ok (SP segs (Kx (TR (17 + length argv1)) md0) (T_D1 rq) rho) (Q_at (E_W2 rq) (17 + length argv1)).
Proof using Hargc HokK Hrq.
  intros rho HG. eapply run_tr; [exact (run_d1 rq) | destruct rq; reflexivity | apply okf |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hw. exists rho1. split; [exact (Good_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HG) | exact Hw].
Qed.
Lemma eL_d1 : forall rho : valuation, Good rho ->
  etriple segs (SP segs (Kx (TR (17 + length argv1)) md0) (T_D1 rq) rho) (Q_at (E_W2 rq) (17 + length argv1)).
Proof using Hargc Hrq.
  intros rho HG. eapply erun_tr; [exact (run_d1 rq) | destruct rq; reflexivity |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state]. intros w Hw. exists w. split; [apply wsteps_refl|].
  exists rho1. split; [exact (Good_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HG) | exact Hw].
Qed.

Lemma w2_intro : forall (rho : valuation) (w : world), Good rho ->
  SP segs (Kx (TR (17 + length argv1)) md0) (E_W2 rq) rho w ->
  exists rho' : valuation, Good rho' /\ rl rho' 5 = nl /\ rl rho' 6 = []
    /\ SP segs (Kx (TR (17 + length argv1)) md0) (E_W2c rq) rho' w.
Proof using Hargc Hent Hinp Hrq.
  intros rho [tr [ms md]] HG [Hsm Hk]. pose proof NU as NU'. pose proof L3_ge as HL3.
  destruct (E_W2_next rq) as (Nx2 & Nxs & Nxr1).

  pose proof (smatch_xforms segs xs_w2s rho (E_W2 rq) (E_W2s rq) _ (xs_w2s_ok rq) Hsm) as Hsm1.
  destruct (smatch_release_obj segs rho (E_W2s rq) _ (ss_objs (E_W2r1 rq)) (lastobj (E_W2s rq)) (ss_next (E_W2s rq)) Hsm1 (E_W2s_objs rq)
              ltac:(rewrite Nxs, <- Nxr1; by_r swf_E_W2r1)) as (m1 & Hsm2 & _ & _ & _ & _).
  set (rho1 := set_rm rho m1) in Hsm2.
  assert (Hsm2' : smatch segs rho1 (E_W2r1 rq) (tr, mkCfg ms md)) by (rewrite Nxs, <- Nxr1 in Hsm2; destruct rq; exact Hsm2). clear Hsm2.
  assert (HG1 : Good rho1) by (apply Good_rm; exact HG).
  destruct (smatch_release_obj segs rho1 (E_W2r1 rq) _ (ss_objs (E_W2r rq)) (lastobj (E_W2r1 rq)) (ss_next (E_W2r1 rq)) Hsm2' (E_W2r1_objs rq)
              ltac:(rewrite Nxr1; by_r swf_E_W2r)) as (m2 & Hsm3 & Hout & Hin & Hob & Hrom).
  cbn [w_cfg cfg_ms] in Hin, Hob, Hrom.
  set (rho2 := set_rm rho1 m2) in Hsm3.
  assert (Hsm3' : smatch segs rho2 (E_W2r rq) (tr, mkCfg ms md)) by (rewrite Nxr1 in Hsm3; destruct rq; exact Hsm3). clear Hsm3.
  assert (HG2 : Good rho2) by (apply Good_rm; exact HG1).
  assert (B1 : bv_unsigned (eval rho1 (SAlu ALU_ADD (SVar 1) (SLit (-560)))) = bv_unsigned sp - 560).
  { pose proof (bval_sound rho1 HG1 (SAlu ALU_ADD (SVar 1) (SLit (-560))) (bv_unsigned sp + (-560)) eq_refl). lia. }
  assert (Rb : obj_range rho1 (lastobj (E_W2r1 rq)) = (bv_unsigned sp - 560, bv_unsigned sp - 560 + 17)).
  { rewrite (last_w2r1 rq). unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite B1.
    rewrite !soff_lit_small by lia. f_equal; lia. }

  destruct (norl_w2 rq) as [N5 N6].
  set (rho3 := rho_set_rl (rho_set_rl rho2 6 []) 5 nl).
  assert (Hsm4 : smatch segs rho3 (E_W2r rq) (tr, mkCfg ms md)).
  { apply smatch_set_rl; [exact N5|]. apply smatch_set_rl; [exact N6|]. exact Hsm3'. }
  assert (HG3 : Good rho3) by (apply Good_set_rl; [apply Good_set_rl; [exact HG2|lia]|lia]).
  exists rho3. split; [exact HG3|]. split; [reflexivity|]. split; [reflexivity|]. split; [|exact Hk].

  apply (smatch_xforms segs xs_w2 rho3 (E_W2c0 rq) (E_W2c rq) _ (xs_w2_ok rq)).
  rewrite <- (E_W2c0_eq rq). unfold app_objs.
  assert (B3 : bv_unsigned (eval rho3 (SAlu ALU_ADD (SVar 1) (SLit (-560)))) = bv_unsigned sp - 560).
  { pose proof (bval_sound rho3 HG3 (SAlu ALU_ADD (SVar 1) (SLit (-560))) (bv_unsigned sp + (-560)) eq_refl). lia. }
  assert (Hsm5 : smatch segs rho3 (E_W2c1 rq) (tr, mkCfg ms md)).
  { rewrite <- (E_W2c1_eq rq). unfold app_objs.
    apply (smatch_carve_listobj segs rho3 (E_W2r rq) _ (SAlu ALU_ADD (SVar 1) (SLit (-560))) (SLit 0) (SLit 1) 0 1 (DList 5) 5 (ss_next (E_W2r rq)) Hsm4 eq_refl);
      rewrite ?B3.
    - by_r swf_E_W2c1.
    - apply soff_lit_small. lia.
    - apply soff_lit_small. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - reflexivity.
    - solve_disjr HG3.
    - intros off Hoff _. cbn [rho3 rho2 rho_set_rl set_rm rm].
      rewrite (released_wview segs m2 ms (fun a => in_rng (obj_range rho1 (lastobj (E_W2r1 rq))) (bv_unsigned a))); [| exact Hin |].
      2:{ rewrite Rb. unfold in_rng. cbn [fst snd]. rewrite Z_to_bv_small by (rewrite mod64; lia). lia. }
      pose proof (obj_writable segs rho1 ms (lastobj (E_W2r1 rq)) off Hob) as W. rewrite (last_w2r1 rq) in W.
      unfold obj_lo_of, obj_hi_of in W. cbn [ob_base ob_lo ob_hi ob_dflt] in W. rewrite B1, !soff_lit_small in W by lia.
      exact (W eq_refl ltac:(lia)).
    - intros off Hoff. cbn [rho3 rho2 rho_set_rl set_rm rm rl]. rewrite Pos.eqb_refl.
      rewrite (released_rd segs m2 ms (fun a => in_rng (obj_range rho1 (lastobj (E_W2r1 rq))) (bv_unsigned a))); [| exact Hin | exact Hrom |].
      2:{ rewrite Rb. unfold in_rng. cbn [fst snd]. rewrite Z_to_bv_small by (rewrite mod64; lia). lia. }
      pose proof (obj_bytes_cells segs rho1 ms (lastobj (E_W2r1 rq)) (ss_next (E_W2r1 rq)) 0 1 [BLit 10] off Hob (wf_w2r1 rq)) as RB.
      rewrite (last_w2r1 rq) in RB. unfold obj_hi_of in RB. cbn [ob_base ob_lo ob_hi ob_cells] in RB.
      rewrite B1, !soff_lit_small in RB by lia.
      rewrite (RB eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(by_r cb_w2) ltac:(lia)).
      replace off with 0 by lia. reflexivity. }
  apply (smatch_carve_listobj segs rho3 (E_W2c1 rq) _ (SLit 0) (SLit 0) (SLit 0) 0 0 (DRom 6) 6 (ss_next (E_W2c1 rq)) Hsm5 eq_refl);
    rewrite ?U_lit64 by lia.
  - by_r swf_E_W2c0.
  - apply soff_lit_small. lia.
  - apply soff_lit_small. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - solve_disjr HG3.
  - intros off Hoff D. discriminate D.
  - intros off Hoff. lia.
Qed.

(* As main's [w2_window], written as plain text. *)
Lemma w2_window : nl ++ [] = firstn (length (nl ++ [])) (skipn (17 + length argv1)%nat MSG).
Proof using A1 Hargc.
  unfold MSG. rewrite app_nil_r. replace (17 + length argv1)%nat with (length (M1 ++ argv1)) by (rewrite length_app, M1_len; lia).
  replace (M1 ++ argv1 ++ nl) with ((M1 ++ argv1) ++ nl) by (rewrite <- app_assoc; reflexivity).
  rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma L_W2 : forall rho : valuation, Good rho -> rl rho 5 = nl -> rl rho 6 = [] ->
  triple segs ok (SP segs (Kx (TR (17 + length argv1)) md0) (E_W2c rq) rho) (Q_at (T_D2 rq) (length MSG)).
Proof using Hargc Hent Hfds0 Hrdr0 Hinp HokK HokP Hrq.
  intros rho HG H5 H6. destruct s_w2_vals as (S12 & S13 & S14 & S15).
  apply (call_path segs (PRw nl []) ok (Kx (TR (17 + length argv1)) md0)
           (WLerr.Kw (Kx (TR (17 + length argv1)) md0) nl [] (length (WLerr.MSG nl [])))
           (E_W2c rq) (E_W2c rq) WLerrS.Pre_wl2 [] s_w2 (R_w2 rq) WLerr.Posts_wl _ rho
           eq_refl (efr_w2 rq) (chk_w2 rq) ltac:(rewrite (facts_w2c rq); exact (fb_w2 rq))).
  - intros rho1 HPR. apply (wl2_call _ nl [] rho1 ltac:(cbn; lia) w2_window HPR).
  - intros ms _. unfold PRw. rewrite rl_call, !rw_call, S13, S15. split; [exact H5|]. split; [exact H6|].
    split; rewrite U_lit64 by lia; reflexivity.
  - intros L rho' [<-|[]] Hag HF. cbn [lf_state]. rewrite (facts_w2c rq) in HF.
    change (ss_next WLerrS.Pre_wl2) with 92%positive. rewrite (T_D2i_eq rq).
    eapply triple_conseq with (P := SP segs (Kx (TR (length MSG)) md0) (T_D2i rq) rho'); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [exact Hsm|]. apply (Kw_TR _ nl [] _ _ _ w2_window) in HK.
      unfold WLerr.MSG in HK. rewrite Nat.min_id in HK. cbn [length app] in HK. rewrite MSG_len.
      replace (18 + length argv1)%nat with (17 + length argv1 + 1)%nat by lia. exact HK. }
    apply (post_path segs ok _ (T_D2i rq) (T_D2 rq) (ss_facts (E_W2 rq)) xs_d2 rho' _ (fb_d2 rq) (xs_d2_ok rq) HF).
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. exists rho'. split; [exact (Good_agree _ _ _ Hag ltac:(destruct rq; cbn; lia) HG) | exact Hw].
Qed.

Lemma eL_W2 : forall rho : valuation, Good rho -> rl rho 5 = nl -> rl rho 6 = [] ->
  etriple segs (SP segs (Kx (TR (17 + length argv1)) md0) (E_W2c rq) rho) (Q_at (T_D2 rq) (length MSG)).
Proof using Hargc Hent Hfds0 Hrdr0 Hinp Hrq.
  intros rho HG H5 H6. destruct s_w2_vals as (S12 & S13 & S14 & S15).
  apply (ecall_path segs (PRw nl []) (Kx (TR (17 + length argv1)) md0)
           (WLerr.Kw (Kx (TR (17 + length argv1)) md0) nl [] (length (WLerr.MSG nl [])))
           (E_W2c rq) (E_W2c rq) WLerrS.Pre_wl2 [] s_w2 (R_w2 rq) WLerr.Posts_wl _ rho
           eq_refl (efr_w2 rq) (chk_w2 rq) ltac:(rewrite (facts_w2c rq); exact (fb_w2 rq))).
  - intros rho1 HPR. apply (wl2_ecall _ nl [] rho1 ltac:(cbn; lia) w2_window HPR).
  - intros ms _. unfold PRw. rewrite rl_call, !rw_call, S13, S15. split; [exact H5|]. split; [exact H6|].
    split; rewrite U_lit64 by lia; reflexivity.
  - intros L rho' [<-|[]] Hag HF. cbn [lf_state]. rewrite (facts_w2c rq) in HF.
    change (ss_next WLerrS.Pre_wl2) with 92%positive. rewrite (T_D2i_eq rq).
    eapply etriple_conseq with (P := SP segs (Kx (TR (length MSG)) md0) (T_D2i rq) rho'); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [exact Hsm|]. apply (Kw_TR _ nl [] _ _ _ w2_window) in HK.
      unfold WLerr.MSG in HK. rewrite Nat.min_id in HK. cbn [length app] in HK. rewrite MSG_len.
      replace (18 + length argv1)%nat with (17 + length argv1 + 1)%nat by lia. exact HK. }
    apply (epost_path segs _ (T_D2i rq) (T_D2 rq) (ss_facts (E_W2 rq)) xs_d2 rho' _ (fb_d2 rq) (xs_d2_ok rq) HF).
    intros w Hw. exists w. split; [apply wsteps_refl|]. exists rho'. split; [exact (Good_agree _ _ _ Hag ltac:(destruct rq; cbn; lia) HG) | exact Hw].
Qed.

Lemma L_exit : forall rho : valuation, Good rho ->
  triple segs ok (SP segs (Kx (TR (length MSG)) md0) (T_D2 rq) rho) (fun _ : world => False).
Proof using Hargc Hfs HokK HokP Hokh Hrq.
  intros rho HG. eapply run_tr; [exact (run_d2 rq) | destruct rq; reflexivity | apply okf |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  destruct (cert_exit rq) as (Hi & H17 & H10).
  apply (triple_exit_eval segs ok SpecT (Kx (TR (length MSG)) md0) (E_exit rq) rho1 2);
    [apply okf | apply okp | exact Hokh | exact Hi | left; exact H17 | rewrite H10; rewrite U_lit64 by lia; reflexivity |].
  intros tr md [-> ->]. rewrite TR_all by lia. rewrite Hfs. exact final_in_spec.
Qed.

Lemma eL_exit : forall rho : valuation, Good rho ->
  etriple segs (SP segs (Kx (TR (length MSG)) md0) (T_D2 rq) rho) (fun w : world => w_tr w = wr 2 MSG ++ [ex fs 2]).
Proof using Hargc Hfs Hrq.
  intros rho HG. eapply erun_tr; [exact (run_d2 rq) | destruct rq; reflexivity |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  destruct (cert_exit rq) as (Hi & H17 & H10).
  eapply etriple_conseq; [intros w Hw; exact Hw | |
    apply (etriple_exit_eval segs (Kx (TR (length MSG)) md0) (E_exit rq) rho1 2 Hi (or_introl H17))].
  - intros w (tr & md & [-> ->] & ->). rewrite TR_all by lia. rewrite Hfs. reflexivity.
  - rewrite H10. rewrite U_lit64 by lia. reflexivity.
Qed.

Theorem copen64_safe : 64 <= N -> forall rho : valuation, Good rho ->
  triple segs ok (SP segs (Kx (TR 0) md0) (T_cs1 rq) rho) (fun _ : world => False).
Proof using Hargc Hent Hfds0 Hrdr0 Hfs Hinp HokK HokP Hokh Hrq.
  intros HN rho HG.
  eapply triple_seq; [exact (L_64 HN rho HG)|].
  apply triple_ex; intros rho1. apply triple_pure; intros HG1.
  apply (triple_from ok _ (fun r w => (Good r /\ rl r 5 = M1 /\ rl r 6 = argv1) /\ SP segs (Kx (TR 0) md0) (E_W1c rq) r w)).
  { intros w Hw. destruct (w1_intro rho1 w HG1 Hw) as (r & A & B & C & D). exists r. auto. }
  intros rho2. apply triple_pure. intros (HG2 & H5 & H6).
  eapply triple_seq; [exact (L_W1 rho2 HG2 H5 H6)|].
  apply triple_ex; intros rho3. apply triple_pure; intros HG3.
  eapply triple_seq; [exact (L_d1 rho3 HG3)|].
  apply triple_ex; intros rho4. apply triple_pure; intros HG4.
  apply (triple_from ok _ (fun r w => (Good r /\ rl r 5 = nl /\ rl r 6 = []) /\ SP segs (Kx (TR (17 + length argv1)) md0) (E_W2c rq) r w)).
  { intros w Hw. destruct (w2_intro rho4 w HG4 Hw) as (r & A & B & C & D). exists r. auto. }
  intros rho5. apply triple_pure. intros (HG5 & H5' & H6').
  eapply triple_seq; [exact (L_W2 rho5 HG5 H5' H6')|].
  apply triple_ex; intros rho6. apply triple_pure; intros HG6.
  exact (L_exit rho6 HG6).
Qed.

Theorem copen64_exists : 64 <= N -> forall rho : valuation, Good rho ->
  etriple segs (SP segs (Kx (TR 0) md0) (T_cs1 rq) rho) (fun w : world => w_tr w = wr 2 MSG ++ [ex fs 2]).
Proof using Hargc Hent Hfds0 Hrdr0 Hfs Hinp Hrq.
  intros HN rho HG.
  eapply etriple_seq; [exact (eL_64 HN rho HG)|].
  apply etriple_ex; intros rho1. apply etriple_pure; intros HG1.
  apply (etriple_from _ (fun r w => (Good r /\ rl r 5 = M1 /\ rl r 6 = argv1) /\ SP segs (Kx (TR 0) md0) (E_W1c rq) r w)).
  { intros w Hw. destruct (w1_intro rho1 w HG1 Hw) as (r & A & B & C & D). exists r. auto. }
  intros rho2. apply etriple_pure. intros (HG2 & H5 & H6).
  eapply etriple_seq; [exact (eL_W1 rho2 HG2 H5 H6)|].
  apply etriple_ex; intros rho3. apply etriple_pure; intros HG3.
  eapply etriple_seq; [exact (eL_d1 rho3 HG3)|].
  apply etriple_ex; intros rho4. apply etriple_pure; intros HG4.
  apply (etriple_from _ (fun r w => (Good r /\ rl r 5 = nl /\ rl r 6 = []) /\ SP segs (Kx (TR (17 + length argv1)) md0) (E_W2c rq) r w)).
  { intros w Hw. destruct (w2_intro rho4 w HG4 Hw) as (r & A & B & C & D). exists r. auto. }
  intros rho5. apply etriple_pure. intros (HG5 & H5' & H6').
  eapply etriple_seq; [exact (eL_W2 rho5 HG5 H5' H6')|].
  apply etriple_ex; intros rho6. apply etriple_pure; intros HG6.
  exact (eL_exit rho6 HG6).
Qed.

Lemma eval_pointwise : ltac2:(tb__ "0|1|
SaSaSbS8S0S3dQ40A1M0S15R4R1A2S15R3R1A2A3Fv;S8S0S2bS3dQ8A1A1ScR5R1A2ScR4R1A2A3Fl;S0G0SeR5R3A2SeR4R3A2A3F_;F_;Fe;Frho';Frho;").
Proof using .
  intros rho rho' e Hw Hl. induction e; cbn; rewrite ?IHe1, ?IHe2, ?IHe; try reflexivity.
  - apply Hw.
  - rewrite Hl. reflexivity.
Qed.

Lemma sobj_eqb_sound : ltac2:(tb__ "0|0|
SfSfS0S2dSaaR2R1A2S34A3S0SfR3R2A3F_;Fb;Fa;").
Proof using .
  intros [b1 l1 h1 c1 d1] [b2 l2 h2 c2 d2] H. unfold sobj_eqb in H. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in H.
  repeat (apply andb_prop in H; destruct H as [H ?]).
  apply sv_eqb_sound in H. repeat match goal with X : sv_eqb _ _ = true |- _ => apply sv_eqb_sound in X end.
  match goal with X : list_eqb cell_eqb _ _ = true |- _ => apply (list_eqb_sound cell_eqb) in X; [|exact cell_eqb_sound] end.
  match goal with X : odefault_eqb _ _ = true |- _ => apply odefault_eqb_sound in X end.
  subst. reflexivity.
Qed.

Lemma GoodS_agree : ltac2:(tb__ "0|1|
S8SaSaS17R3R2R1A3SdeP1dR4A2S47R4A1M0G0F_;F_;F_;Frho';Frho;Fn;").
Proof using Hargc.
  intros n rho rho' Hag Hn [HG H7]. split; [exact (Good_agree n rho rho' Hag Hn HG)|].
  rewrite <- (proj1 (proj2 Hag)). exact H7.
Qed.

Lemma Tsm_intro : forall (rho : valuation) (w : world), Good rho -> N <= 63 ->
  SP segs (Kx (TR 0) md0) (T_cs1 rq) rho w -> SP segs (Kx (TR 0) md0) (Tsm rq) rho w.
Proof using Hargc Hent Hinp Hrq.
  intros rho w HG HN Hsp. unfold Tsm. apply SP_add1; [exact Hsp | | destruct rq; reflexivity].
  cbn [holds]. unfold bv_leu. rewrite U_lit64 by lia. rewrite (G_v28 rho HG). lia.
Qed.

Lemma L_sm : N <= 63 -> forall rho : valuation, Good rho ->
  triple segs ok (SP segs (Kx (TR 0) md0) (T_cs1 rq) rho) (Q_at (E_fx rq) 0).
Proof using Hargc Hent Hinp HokK Hrq.
  intros HN rho HG.
  eapply triple_conseq with (P := SP segs (Kx (TR 0) md0) (Tsm rq) rho); [intros w Hw; exact (Tsm_intro rho w HG HN Hw) | intros w Hw; exact Hw |].
  eapply run_tr; [exact (run_sm rq) | destruct rq; reflexivity | apply okf |].
  intros L rho1 [<-|[<-|[]]] Hag1; cbn [lf_state].
  - pose proof (Good_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HG) as HG1.
    intros n Hg w Hw. exfalso. exact (ovf_contra rho1 (X_ovfS rq) w _ HG1 (fact_ovfS rq) Hw).
  - pose proof (Good_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HG) as HG1.
    eapply run_tr; [exact (run_fx0 rq) | destruct rq; reflexivity | apply okf |].
    intros L rho2 [<-|[]] Hag2; cbn [lf_state].
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. exists rho2. split; [exact (Good_agree _ _ _ Hag2 ltac:(destruct rq; cbn; lia) HG1) | exact Hw].
Qed.

Lemma eL_sm : N <= 63 -> forall rho : valuation, Good rho ->
  etriple segs (SP segs (Kx (TR 0) md0) (T_cs1 rq) rho) (Q_at (E_fx rq) 0).
Proof using Hargc Hent Hinp Hrq.
  intros HN rho HG.
  eapply etriple_conseq with (P := SP segs (Kx (TR 0) md0) (Tsm rq) rho); [intros w Hw; exact (Tsm_intro rho w HG HN Hw) | intros w Hw; exact Hw |].
  eapply erun_tr; [exact (run_sm rq) | destruct rq; reflexivity |].
  intros L rho1 [<-|[<-|[]]] Hag1; cbn [lf_state].
  - intros w Hw. exfalso. exact (ovf_contra rho1 (X_ovfS rq) w _ (Good_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HG) (fact_ovfS rq) Hw).
  - pose proof (Good_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HG) as HG1.
    eapply erun_tr; [exact (run_fx0 rq) | destruct rq; reflexivity |].
    intros L rho2 [<-|[]] Hag2; cbn [lf_state]. intros w Hw. exists w. split; [apply wsteps_refl|].
    exists rho2. split; [exact (Good_agree _ _ _ Hag2 ltac:(destruct rq; cbn; lia) HG1) | exact Hw].
Qed.


Lemma V70_eq : ltac2:(tb__ "0|3|
S1S0S7VA1;S5cS4aS5fVA1;Z4M0A2M1A2A3S1S1S5bZ0M2G1A2S60G1G0A2A2S0S7S5fS4aG0A2G2A3A2A2").
Proof using Hargc.
  unfold V70. split; [apply Z.div_mod; lia|]. split; [apply Z.mod_pos_bound; lia|].
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma fxA_intro : forall (rho : valuation) (w : world), Good rho ->
  SP segs (Kx (TR 0) md0) (E_fx rq) rho w ->
  exists rho' : valuation, GoodS rho' /\ rw rho' 70 = Z_to_bv 64 V70 /\ SP segs (Kx (TR 0) md0) (E_fxA rq) rho' w.
Proof using Hargc Hent Hinp.
  intros rho w HG [Hsm Hk]. pose proof NU as NU'. pose proof A1_eq as EA1. pose proof V70_eq as (EV & RV & MV).
  destruct (E_fxA_next rq) as (NxA & NxX & NxW).
  pose proof (smatch_xforms segs xs_fx rho (E_fx rq) (E_fxX rq) _ (xs_fx_ok rq) Hsm) as Hsm1.
  destruct (SP_entails segs (Kx (TR 0) md0) (E_fxX rq) (E_fxW rq) [] rho w (ent_fxW rq) (conj Hsm1 Hk)) as [Hsm2 _].
  set (rho1 := rho_sub rho []) in Hsm2.
  assert (HG1 : Good rho1) by (apply Good_sub; [reflexivity | exact HG]).
  set (rho2 := rho_set_rw rho1 70 (Z_to_bv 64 V70)).
  assert (Hsm3 : smatch segs rho2 (E_fxW rq) w).
  { eapply smatch_agree; [|exact Hsm2]. rewrite NxW. apply agree_below_set_rw. lia. }
  assert (HG2 : Good rho2) by (apply Good_set_rw; [exact HG1 | lia]).
  set (rho3 := rho_set_rl rho2 7 argv1).
  exists rho3. split; [|split].
  - split; [apply Good_set_rl; [exact HG2 | lia] | reflexivity].
  - reflexivity.
  - split; [|exact Hk]. apply smatch_set_rl; [exact (norl7_fxA rq)|].
    apply (SP_restate segs (Kx (TR 0) md0) rho2 (E_fxW rq) (E_fxA rq) w _ _ (swf_E_fxA rq) (diff_fxA rq)); [constructor | | split; [exact Hsm3 | exact Hk]].
    constructor; [|constructor]. cbn [holds rho2 rho_set_rw rw]. rewrite Pos.eqb_refl.
    rewrite Z_to_bv_small by (rewrite mod64; unfold V70; lia). split; [lia | exact MV].
Qed.

Lemma bexp_eqb_beval : ltac2:(tb__ "0|0|
SaS7dS7dS0S2dS7fR2R1A2S34A3S0S3dQ8A1S7eR4R3A2S7eR4R2A2A3F_;Fb;Fa;Frho;").
Proof using .
  intros rho [x|l i] [y|l' i'] H; cbn in H |- *; try discriminate.
  - apply Z.eqb_eq in H. apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_modulus 8) with 256. unfold bv_wrap. change (bv_modulus 8) with 256. exact H.
  - apply andb_prop in H as [H1 H2]. apply Pos.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
Lemma list_bexp_eqb_beval : ltac2:(tb__ "0|3|
SaS2bS7dA1M0G0S0S2dSc5S7dS7fR2R1A4S34A3S0S2bS3dQ8A1M1A1S75S7dG1S7eR4A1M2R3A4S75S7dG1G2R2A4A3F_;Fl2;Fl1;Frho;").
Proof using .
  intros rho l1. induction l1 as [|a l1 IH]; intros [|b l2] H; cbn in H |- *; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (bexp_eqb_beval rho _ _ H1), (IH _ H2). reflexivity.
Qed.
Lemma map_nth_seq_k : ltac2:(tb__ "0|2|
S2bS3dQ8A1M0A1M1S31S31G0Sb1S70R2R3A2S2cG0R4A2A2S0G1S75S31G0S31S73G0R1R6R3A4Lj;S76R3R4A2A4S71G0R4S72G0R3R5A3A3A3F_;Fd;Fk;Fn;Fl;").
Proof using A1 ENVC Hargc L3 N RND.
  intros l n. induction n as [|n IH]; intros k d Hn; [cbn; rewrite firstn_O; reflexivity|].
  cbn [seq map]. rewrite (IH (S k) d) by lia.
  rewrite <- (SysExtra.nth_skipn_cons l k d) by lia. reflexivity.
Qed.
Lemma BLn_beval : ltac2:(tb__ "0|2|
SaS7Sb1S64R1A1S2cS3dQ8A1M0ScR2P3M1A2A2A2S0S2bG0A1S75S7dG0S7eR3A1S83R2A1A4S71G0S64R2A1ScR3G1A2A3A3F_;Fn;Frho;").
Proof using A1 ENVC Hargc JI L3 N RND.
  intros rho n Hn. unfold BLn. rewrite map_map. cbn [beval].
  replace (map (fun x : nat => nth (Z.to_nat (Z.of_nat x)) (rl rho 3) (Z_to_bv 8 0)) (seq 0 (Z.to_nat n)))
    with (map (fun j : nat => nth j (rl rho 3) (Z_to_bv 8 0)) (seq 0 (Z.to_nat n)))
    by (apply map_ext; intros j; rewrite Nat2Z.id; reflexivity).
  rewrite (map_nth_seq_k (rl rho 3) (Z.to_nat n) 0 (Z_to_bv 8 0)) by lia. reflexivity.
Qed.

Lemma check_pre_sound : forall (n r : Z) (C P : sstate), check_pre rq n r = Some (C, P) ->
  exists d : list (sv * sv),
    swf (C0_nr rq n r) = true
    /\ state_diff (E_fxA rq) (C0_nr rq n r) = Some (d, [F_n n])
    /\ Forall (fun ab : sv * sv => forall rho : valuation, eval rho (sv_subst (s_nr n r) (fst ab)) = eval rho (snd ab)) d
    /\ apply_xforms (C0_nr rq n r) (xs_c n) = Some C
    /\ P = pre_loc C /\ ss_next C = 71%positive /\ ss_lenient C = false.
Proof using .
  intros n r C P H. unfold check_pre in H. cbv zeta in H.
  destruct (state_diff (E_fxA rq) (C0_nr rq n r)) as [[d nf]|] eqn:Ed; [|discriminate].
  destruct (apply_xforms (C0_nr rq n r) (xs_c n)) as [C'|] eqn:Ex; [|discriminate].
  destruct (swf (C0_nr rq n r) && forallb (diff_in_ok n r) d && list_eqb sprop_eqb nf [F_n n] && (ss_next C' =? 71)%positive && negb (ss_lenient C')) eqn:Eb; [|discriminate].
  injection H as <- <-.
  apply andb_prop in Eb as [Eb Eln]. apply andb_prop in Eb as [Eb Enx]. apply andb_prop in Eb as [Eb Enf]. apply andb_prop in Eb as [Ewf Ein].
  assert (Eln' : ss_lenient C' = false) by (destruct (ss_lenient C'); [discriminate|reflexivity]).
  apply (list_eqb_sound sprop_eqb) in Enf; [|exact sprop_eqb_sound]. subst nf. apply Pos.eqb_eq in Enx.
  exists d. repeat split; auto.
  apply Forall_forall. intros ab Hab rho. apply sv_equiv_sound. exact (proj1 (forallb_forall _ _) Ein ab Hab).
Qed.

Lemma check_core_sound : forall (n r : Z) (res : option (list leaf)), check_core rq n r res = true ->
  exists (C P : sstate) (L : leaf) (o : sobj) (bl : list bexp) (d2 : list (sv * sv)),
    check_pre rq n r = Some (C, P)
    /\ entails_fr C P [] = Some (R_gen rq)
    /\ call_check C P [] (R_gen rq) [mkLeaf (post_loc n r C) RsCut] = true
    /\ res = Some [L]
    /\ nth_error (ss_objs (lf_state L)) 1 = Some o
    /\ ob_lo o = SLit (-543)
    /\ ob_hi o = SLit (n - 543)
    /\ dflt_writable (ob_dflt o) = true
    /\ is_arr (ob_dflt o) = false
    /\ cells_bytes (ob_cells o) (SLit (-543)) 0 (Z.to_nat n) = Some bl
    /\ list_eqb bexp_eqb bl (BLn n) = true
    /\ state_has_rl 7 (lf_state L) = false
    /\ entails (obj_to_list (lf_state L) 1 7) (post_loc n r C) (infer_sub 71 (obj_to_list (lf_state L) 1 7) (post_loc n r C)) = true
    /\ (forall i : positive, (i < 71)%positive ->
          wsub_get (infer_sub 71 (obj_to_list (lf_state L) 1 7) (post_loc n r C)) i = SVar i)
    /\ state_diff (import_post [] 71 (post_loc n r C) 71 (R_gen rq)) (E_po rq) = Some (d2, [])
    /\ Forall (fun ab : sv * sv => forall rho : valuation, eval rho (fst ab) = eval rho (sv_subst (s_nr n r) (snd ab))) d2.
Proof using A1 ENVC Hargc L3 N RND.
  intros n r res H. unfold check_core in H.
  destruct (check_pre rq n r) as [[C P]|] eqn:Ep; [|discriminate]. cbv zeta in H.
  apply andb_prop in H as [H HD]. apply andb_prop in H as [H HC]. apply andb_prop in H as [HA HB].
  destruct (entails_fr C P []) as [R|] eqn:Efr; [|discriminate].
  apply (list_eqb_sound sobj_eqb) in HA; [|exact sobj_eqb_sound]. subst R.
  destruct res as [[|L [|? ?]]|]; try discriminate.
  apply andb_prop in HC as [HC He]. apply andb_prop in HC as [HC Hrl].
  destruct (nth_error (ss_objs (lf_state L)) 1) as [o|] eqn:Eo; [|discriminate].
  apply andb_prop in HC as [HC Hcb]. apply andb_prop in HC as [HC Harr]. apply andb_prop in HC as [HC Hwr]. apply andb_prop in HC as [Hlo Hhi].
  destruct (cells_bytes (ob_cells o) (SLit (-543)) 0 (Z.to_nat n)) as [bl|] eqn:Ecb; [|discriminate].
  apply andb_prop in He as [He Hs].
  destruct (state_diff (import_post [] 71 (post_loc n r C) 71 (R_gen rq)) (E_po rq)) as [[d2 [|? ?]]|] eqn:Ed2; try discriminate.
  exists C, P, L, o, bl, d2. repeat split; auto.
  - apply sv_eqb_sound in Hlo. exact Hlo.
  - apply sv_eqb_sound in Hhi. exact Hhi.
  - destruct (is_arr (ob_dflt o)); [discriminate|reflexivity].
  - destruct (state_has_rl 7 (lf_state L)); [discriminate|reflexivity].
  - intros i Hi. apply sv_eqb_sound. apply (proj1 (forallb_forall _ _) Hs i).
    unfold ids_below71. apply in_map_iff. exists (Pos.to_nat i). split; [apply Pos2Nat.id|]. apply in_seq. lia.
  - apply Forall_forall. intros ab Hab rho. apply sv_equiv_sound. exact (proj1 (forallb_forall _ _) HD ab Hab).
Qed.


Lemma loc_sum : ltac2:(tb__ "0|9|
S7S10S10S6bSfS2bS7dA1M0S2bS52A1S53OF_;F_;S0S2fS2bS6bA1M1A1S6dS6S85S32S7Sc9S30S7A1A3R6S34A5S2eG1S32S6bR4S30S6bA1M2A3A2A3S0S2dS1bR7A1S36A3S0S8S16R8A1P47M3A3S0S2fSfA1SbcSfS1dS6cR7A1A1U1M4A3S2eSfR6A2A3S0SbS22R7A1S11N21fA1M5A3S0SbS21R8A1S11S61RcZ21fA2A1A3S1S5bZ0M6RdA2S5bRdZ3fA2A2S0S2dS1eS19RaA1A1S34A3S0S2dS1fS19RbA1A1S36A3S0S2fG0A1S80S20RcA1G5G6S64R10A1A4S2eG0RbA2A3S0S2dSc5S7dS7fRcS83R11A1A4S34A3S0S2dSd3P7M7S6cRfA1A2S36A3S0S2dSd7Sb5S6cR10A1G4G7A3M8R11Sb3G3G8R11A3A3S34A3S8SdfR1G3A2S0SbSbfSb3G3Sb5S6cR13A1G4G7A3R14A3R2A2SdR2A1A3F_;Fi;S42S6Vok;RfA3SaS4bR17R1A2S68S6Vok;S40S6R12R17R2A4S41S6R12G3R2S32S6bS6fR16S6eA2G2A3A5A4F_;Frho1;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FK;Fbl;Fo;FL;FQ;FP;Fn;").
Proof using A1 ENVC Hargc JI L3 N RND.
  intros n P Q L o bl K Hrun Hlen Hnx Ho Hlo Hhi Hn Hwr Harr Hcb Hbl Hrl He Hs Hok rho1 [H7 Hlen3].
  eapply run_tr; [exact Hrun | exact Hlen | exact Hok |]. rewrite Hnx.
  intros L' rhoL [<-|[]] HagL.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w [Hsm Hk].
  pose proof (smatch_obj_to_list segs rhoL (lf_state L) w 1 7 o (-543) (n - 543) bl Hsm Ho Hlo Hhi ltac:(lia) ltac:(lia) Hwr Harr) as Hsm2.
  replace (n - 543 - -543) with n in Hsm2 by lia. specialize (Hsm2 Hcb Hrl).
  set (rho2 := rho_set_rl rhoL 7 (map (beval rhoL) bl)) in Hsm2.
  set (s := infer_sub 71 (obj_to_list (lf_state L) 1 7) Q) in He, Hs.
  assert (E7 : map (beval rhoL) bl = rl rhoL 7).
  { rewrite (list_bexp_eqb_beval rhoL _ _ Hbl). pose proof (proj1 (proj2 HagL)) as Al.
    rewrite (BLn_beval rhoL n) by (rewrite <- (Al 3%positive); exact Hlen3).
    rewrite <- (Al 7%positive), <- (Al 3%positive). symmetry. exact H7. }
  exists (mkLeaf Q RsCut), (rho_sub rho2 s). split; [left; reflexivity|]. split; [|split; [|exact Hk]].
  - destruct HagL as (Aw & Al & Am). split; [|split].
    + intros i Hi. cbn [rho_sub rw]. rewrite (Hs i Hi). cbn [eval]. subst rho2. cbn [rho_set_rl rw]. apply Aw. exact Hi.
    + intros l. cbn [rho_sub rl]. subst rho2. cbn [rho_set_rl rl]. destruct (Pos.eqb_spec l 7) as [->|]; [|apply Al].
      rewrite E7. apply Al.
    + intros a. cbn [rho_sub rm]. subst rho2. cbn [rho_set_rl rm]. apply Am.
  - cbn [lf_state]. eapply entails_sound; [exact He | exact Hsm2].
Qed.

Lemma eloc_sum : ltac2:(tb__ "0|9|
S7S10S10S6bSfS2bS7dA1M0S2bS52A1S53OF_;F_;S0S2fS2bS6bA1M1A1S6dS6S85S32S7Sc9S30S7A1A3R6S34A5S2eG1S32S6bR4S30S6bA1M2A3A2A3S0S2dS1bR7A1S36A3S0S8S16R8A1P47M3A3S0S2fSfA1SbcSfS1dS6cR7A1A1U1M4A3S2eSfR6A2A3S0SbS22R7A1S11N21fA1M5A3S0SbS21R8A1S11S61RcZ21fA2A1A3S1S5bZ0M6RdA2S5bRdZ3fA2A2S0S2dS1eS19RaA1A1S34A3S0S2dS1fS19RbA1A1S36A3S0S2fG0A1S80S20RcA1G5G6S64R10A1A4S2eG0RbA2A3S0S2dSc5S7dS7fRcS83R11A1A4S34A3S0S2dSd3P7M7S6cRfA1A2S36A3S0S2dSd7Sb5S6cR10A1G4G7A3M8R11Sb3G3G8R11A3A3S34A3S8SdfR1G3A2S0SbSbfSb3G3Sb5S6cR13A1G4G7A3R14A3R2A2SdR2A1A3F_;Fi;SaS4bR16R1A2S67S6S40S6R11R16R2A4S41S6R11G3R2S32S6bS6fR15S6eA2G2A3A5A3F_;Frho1;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FK;Fbl;Fo;FL;FQ;FP;Fn;").
Proof using A1 ENVC Hargc JI L3 N RND.
  intros n P Q L o bl K Hrun Hlen Hnx Ho Hlo Hhi Hn Hwr Harr Hcb Hbl Hrl He Hs rho1 [H7 Hlen3].
  eapply erun_tr; [exact Hrun | exact Hlen |]. rewrite Hnx.
  intros L' rhoL [<-|[]] HagL w [Hsm Hk]. exists w. split; [apply wsteps_refl|].
  pose proof (smatch_obj_to_list segs rhoL (lf_state L) w 1 7 o (-543) (n - 543) bl Hsm Ho Hlo Hhi ltac:(lia) ltac:(lia) Hwr Harr) as Hsm2.
  replace (n - 543 - -543) with n in Hsm2 by lia. specialize (Hsm2 Hcb Hrl).
  set (rho2 := rho_set_rl rhoL 7 (map (beval rhoL) bl)) in Hsm2.
  set (s := infer_sub 71 (obj_to_list (lf_state L) 1 7) Q) in He, Hs.
  assert (E7 : map (beval rhoL) bl = rl rhoL 7).
  { rewrite (list_bexp_eqb_beval rhoL _ _ Hbl). pose proof (proj1 (proj2 HagL)) as Al.
    rewrite (BLn_beval rhoL n) by (rewrite <- (Al 3%positive); exact Hlen3).
    rewrite <- (Al 7%positive), <- (Al 3%positive). symmetry. exact H7. }
  exists (mkLeaf Q RsCut), (rho_sub rho2 s). split; [left; reflexivity|]. split; [|split; [|exact Hk]].
  - destruct HagL as (Aw & Al & Am). split; [|split].
    + intros i Hi. cbn [rho_sub rw]. rewrite (Hs i Hi). cbn [eval]. subst rho2. cbn [rho_set_rl rw]. apply Aw. exact Hi.
    + intros l. cbn [rho_sub rl]. subst rho2. cbn [rho_set_rl rl]. destruct (Pos.eqb_spec l 7) as [->|]; [|apply Al].
      rewrite E7. apply Al.
    + intros a. cbn [rho_sub rm]. subst rho2. cbn [rho_set_rl rm]. apply Am.
  - cbn [lf_state]. eapply entails_sound; [exact He | exact Hsm2].
Qed.

Lemma s_nr_id : ltac2:(tb__ "0|2|
S7S7SaS43R1A1S0S7VN;R4A3S0S7S5fVA1;Z4A2R4A3S0S3dQ40M0A1M1S15R4P46A2S3fG0S4aA2A3SbS0G1SeSbeR6S98R8R7A2A2R1A2SeR6R1A2A3Fe;F_;F_;F_;F_;Frho;Fr;Fn;").
Proof using Hargc Hent Hinp.
  intros n r rho HG Hn Hr H70 e. pose proof NU as NU'. pose proof A1_eq as EA1. pose proof V70_eq as (EV & RV & MV).
  apply eval_pointwise; [|reflexivity].
  intros v. cbn [rho_sub rw]. unfold s_nr. cbn [wsub_get].
  destruct (Pos.eqb_spec v 28) as [->|N28].
  - cbn [eval]. rewrite (g_v28 rho HG). subst n. reflexivity.
  - destruct (Pos.eqb_spec v 25) as [->|N25]; [|reflexivity].
    apply bv_eq. rewrite (J_add rho (SVar 70) (SLit r) V70 r); [| cbn [eval]; rewrite H70; apply Z_to_bv_small; rewrite mod64; unfold V70; lia
      | apply U_lit64; lia | unfold V70; lia | lia | unfold V70; lia].
    pose proof (G_v25 rho HG) as V25. cbn [eval] in V25. rewrite V25. lia.
Qed.

Lemma PRloc_intro : ltac2:(tb__ "0|0|
S7SaS2bSfA1Sc3S47R3A1S0S7VN;R5A3S4bR6SbeSc0R5R4R3A3S30S35S8SbA2A1A2A2F_;F_;Fms;FR;Frho;Fn;").
Proof using Hargc Hent Hinp.
  intros n rho R ms [HG H7] Hn. unfold PRloc. rewrite !rl_call. rewrite H7, (G_rl3 rho HG). subst n. unfold N. rewrite Nat2Z.id.
  split; [symmetry; exact tail1_firstn|]. pose proof length_tail1. pose proof L3_ge. unfold N in *. lia.
Qed.

Lemma L_nr : forall n r : Z, check_core rq n r (sym_run segs FUELm [ret_out] (the_pre rq n r) true) = true ->
  N = n -> A1 mod 4 = r -> N <= 63 -> forall rho : valuation, GoodS rho -> rw rho 70 = Z_to_bv 64 V70 ->
  triple segs ok (SP segs (Kx (TR 0) md0) (E_fxA rq) rho) (QS_at (E_po rq) 0).
Proof using Hargc Hent Hinp HokK.
  intros n r Hchk Hn Hr HN rho HGS H70. pose proof (proj1 HGS) as HG. pose proof NU as NU'. pose proof L3_ge as HL3. pose proof V70_eq as (EV & RV & MV).
  destruct (check_core_sound n r _ Hchk) as (C & P & L & o & bl & d2 & Hpre & Hefr & Hcc & Hrun & Ho & Hlo & Hhi & Hwr & Harr & Hcb & Hbl & Hrl & He & Hs & Hd2 & Hd2ok).
  destruct (check_pre_sound n r C P Hpre) as (d & Hwf0 & Hd & Hdok & Hx & HP & HnxC & HlnC).
  assert (Hrun' : sym_run segs FUELm [ret_out] P true = Some [L]).
  { unfold the_pre in Hrun. rewrite Hpre in Hrun. exact Hrun. }

  eapply triple_conseq with (P := SP segs (Kx (TR 0) md0) C rho); [| intros w Hw; exact Hw |].
  { intros w Hsp. apply (SP_xforms segs (Kx (TR 0) md0) (xs_c n) rho (C0_nr rq n r) C w Hx).
    apply (SP_restate segs (Kx (TR 0) md0) rho (E_fxA rq) (C0_nr rq n r) w _ _ Hwf0 Hd); [| | exact Hsp].
    - unfold diffs_ok. apply Forall_forall. intros ab Hab.
      rewrite <- (proj1 (Forall_forall _ _) Hdok ab Hab rho). rewrite eval_subst. symmetry. apply (s_nr_id n r rho HG Hn Hr H70).
    - constructor; [|constructor]. unfold F_n. cbn [holds]. rewrite U_lit64 by lia.
      rewrite (G_v27 rho HG). subst n. lia. }

  subst P.
  apply (call_sound_P segs (PRloc n) ok (Kx (TR 0) md0) (Kx (TR 0) md0) C (pre_loc C) [] (R_gen rq) [mkLeaf (post_loc n r C) RsCut] _ rho Hefr Hcc).
  - intros rho1 HPR.
    replace (ss_next (pre_loc C)) with 71%positive by (unfold pre_loc, set_objs; cbn [ss_next]; symmetry; exact HnxC).
    apply (loc_sum n (pre_loc C) (post_loc n r C) L o bl (Kx (TR 0) md0) Hrun'); try assumption;
      try (unfold pre_loc, set_objs; cbn [ss_lenient ss_next]; assumption); [subst n; unfold N; lia | apply okf].
  - intros ms. apply (PRloc_intro n rho (R_gen rq) ms HGS Hn).
  - intros L' rho' [<-|[]] Hag. cbn [lf_state]. unfold pre_loc, set_objs. cbn [ss_next]. rewrite HnxC.
    pose proof (GoodS_agree _ _ _ Hag ltac:(rewrite HnxC; lia) HGS) as HGS'. pose proof (proj1 HGS') as HG'.
    assert (H70' : rw rho' 70 = Z_to_bv 64 V70) by (rewrite <- (proj1 Hag 70%positive ltac:(rewrite HnxC; lia)); exact H70).
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hsp. exists rho'. split; [exact HGS'|].
    apply (SP_restate segs (Kx (TR 0) md0) rho' _ (E_po rq) w _ _ (swf_E_po rq) Hd2); [| constructor | exact Hsp].
    unfold diffs_ok. apply Forall_forall. intros ab Hab.
    rewrite (proj1 (Forall_forall _ _) Hd2ok ab Hab rho'). rewrite eval_subst. apply (s_nr_id n r rho' HG' Hn Hr H70').
Qed.

Lemma eL_nr : forall n r : Z, check_core rq n r (sym_run segs FUELm [ret_out] (the_pre rq n r) true) = true ->
  N = n -> A1 mod 4 = r -> N <= 63 -> forall rho : valuation, GoodS rho -> rw rho 70 = Z_to_bv 64 V70 ->
  etriple segs (SP segs (Kx (TR 0) md0) (E_fxA rq) rho) (QS_at (E_po rq) 0).
Proof using Hargc Hent Hinp.
  intros n r Hchk Hn Hr HN rho HGS H70. pose proof (proj1 HGS) as HG. pose proof NU as NU'. pose proof L3_ge as HL3. pose proof V70_eq as (EV & RV & MV).
  destruct (check_core_sound n r _ Hchk) as (C & P & L & o & bl & d2 & Hpre & Hefr & Hcc & Hrun & Ho & Hlo & Hhi & Hwr & Harr & Hcb & Hbl & Hrl & He & Hs & Hd2 & Hd2ok).
  destruct (check_pre_sound n r C P Hpre) as (d & Hwf0 & Hd & Hdok & Hx & HP & HnxC & HlnC).
  assert (Hrun' : sym_run segs FUELm [ret_out] P true = Some [L]).
  { unfold the_pre in Hrun. rewrite Hpre in Hrun. exact Hrun. }
  eapply etriple_conseq with (P := SP segs (Kx (TR 0) md0) C rho); [| intros w Hw; exact Hw |].
  { intros w Hsp. apply (SP_xforms segs (Kx (TR 0) md0) (xs_c n) rho (C0_nr rq n r) C w Hx).
    apply (SP_restate segs (Kx (TR 0) md0) rho (E_fxA rq) (C0_nr rq n r) w _ _ Hwf0 Hd); [| | exact Hsp].
    - unfold diffs_ok. apply Forall_forall. intros ab Hab.
      rewrite <- (proj1 (Forall_forall _ _) Hdok ab Hab rho). rewrite eval_subst. symmetry. apply (s_nr_id n r rho HG Hn Hr H70).
    - constructor; [|constructor]. unfold F_n. cbn [holds]. rewrite U_lit64 by lia.
      rewrite (G_v27 rho HG). subst n. lia. }
  subst P.
  apply (call_complete_P segs (PRloc n) (Kx (TR 0) md0) (Kx (TR 0) md0) C (pre_loc C) [] (R_gen rq) [mkLeaf (post_loc n r C) RsCut] _ rho Hefr Hcc).
  - intros rho1 HPR.
    replace (ss_next (pre_loc C)) with 71%positive by (unfold pre_loc, set_objs; cbn [ss_next]; symmetry; exact HnxC).
    apply (eloc_sum n (pre_loc C) (post_loc n r C) L o bl (Kx (TR 0) md0) Hrun'); try assumption;
      try (unfold pre_loc, set_objs; cbn [ss_lenient ss_next]; assumption); subst n; unfold N; lia.
  - intros ms. apply (PRloc_intro n rho (R_gen rq) ms HGS Hn).
  - intros L' rho' [<-|[]] Hag. cbn [lf_state]. unfold pre_loc, set_objs. cbn [ss_next]. rewrite HnxC.
    pose proof (GoodS_agree _ _ _ Hag ltac:(rewrite HnxC; lia) HGS) as HGS'. pose proof (proj1 HGS') as HG'.
    assert (H70' : rw rho' 70 = Z_to_bv 64 V70) by (rewrite <- (proj1 Hag 70%positive ltac:(rewrite HnxC; lia)); exact H70).
    intros w Hsp. exists w. split; [apply wsteps_refl|]. exists rho'. split; [exact HGS'|].
    apply (SP_restate segs (Kx (TR 0) md0) rho' _ (E_po rq) w _ _ (swf_E_po rq) Hd2); [| constructor | exact Hsp].
    unfold diffs_ok. apply Forall_forall. intros ab Hab.
    rewrite (proj1 (Forall_forall _ _) Hd2ok ab Hab rho'). rewrite eval_subst. apply (s_nr_id n r rho' HG' Hn Hr H70').
Qed.

Lemma GoodS_sub_nil : ltac2:(tb__ "0|0|
SaS47R1A1S47SbeR2S30S35S8SbA2A1A2A1F_;Frho;").
Proof using . intros rho [HG H7]. split; [apply Good_sub; [reflexivity | exact HG] | cbn; exact H7]. Qed.

Lemma L_po62 : N <= 62 -> forall rho : valuation, GoodS rho ->
  triple segs ok (SP segs (Kx (TR 0) md0) (E_po rq) rho) (QS_at (E_Wa rq) 0).
Proof using Hargc Hent Hinp HokK Hrq.
  intros HN rho HGS. pose proof (proj1 HGS) as HG.
  eapply triple_conseq with (P := SP segs (Kx (TR 0) md0) (E_po62 rq) rho); [| intros w Hw; exact Hw |].
  { intros w Hsp. unfold E_po62. apply SP_add1; [apply (SP_xforms segs _ xs_po rho (E_po rq) (E_po2 rq) w (xs_po_ok rq) Hsp) | | destruct rq; reflexivity].
    cbn [holds]. unfold bv_leu. rewrite U_lit64 by lia. rewrite (G_v28 rho HG). lia. }
  eapply run_tr; [exact (run_po62 rq) | destruct rq; reflexivity | apply okf |].
  intros L rho1 [<-|[]] Hag1; cbn [lf_state]. pose proof (GoodS_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HGS) as HGS1.
  eapply run_tr; [exact (run_fx2a rq) | destruct rq; reflexivity | apply okf |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (GoodS_agree _ _ _ Hag2 ltac:(destruct rq; cbn; lia) HGS1) as HGS2.
  - eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. exists (rho_sub rho2 []). split; [exact (GoodS_sub_nil _ HGS2) | exact (SP_entails segs _ _ _ [] rho2 w (ent_Wa1 rq) Hw)].
  - eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. exists (rho_sub rho2 []). split; [exact (GoodS_sub_nil _ HGS2) | exact (SP_entails segs _ _ _ [] rho2 w (ent_Wa2 rq) Hw)].
Qed.

Lemma eL_po62 : N <= 62 -> forall rho : valuation, GoodS rho ->
  etriple segs (SP segs (Kx (TR 0) md0) (E_po rq) rho) (QS_at (E_Wa rq) 0).
Proof using Hargc Hent Hinp Hrq.
  intros HN rho HGS. pose proof (proj1 HGS) as HG.
  eapply etriple_conseq with (P := SP segs (Kx (TR 0) md0) (E_po62 rq) rho); [| intros w Hw; exact Hw |].
  { intros w Hsp. unfold E_po62. apply SP_add1; [apply (SP_xforms segs _ xs_po rho (E_po rq) (E_po2 rq) w (xs_po_ok rq) Hsp) | | destruct rq; reflexivity].
    cbn [holds]. unfold bv_leu. rewrite U_lit64 by lia. rewrite (G_v28 rho HG). lia. }
  eapply erun_tr; [exact (run_po62 rq) | destruct rq; reflexivity |].
  intros L rho1 [<-|[]] Hag1; cbn [lf_state]. pose proof (GoodS_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HGS) as HGS1.
  eapply erun_tr; [exact (run_fx2a rq) | destruct rq; reflexivity |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [lf_state]; pose proof (GoodS_agree _ _ _ Hag2 ltac:(destruct rq; cbn; lia) HGS1) as HGS2;
    intros w Hw; exists w; (split; [apply wsteps_refl|]); exists (rho_sub rho2 []); split; [exact (GoodS_sub_nil _ HGS2) | | exact (GoodS_sub_nil _ HGS2) |].
  - exact (SP_entails segs _ _ _ [] rho2 w (ent_Wa1 rq) Hw).
  - exact (SP_entails segs _ _ _ [] rho2 w (ent_Wa2 rq) Hw).
Qed.

Lemma L_po63 : N = 63 -> forall rho : valuation, GoodS rho ->
  triple segs ok (SP segs (Kx (TR 0) md0) (E_po rq) rho) (QS_at (E_Wb rq) 0).
Proof using Hargc Hent Hinp HokK Hrq.
  intros HN rho HGS. pose proof (proj1 HGS) as HG.
  eapply triple_conseq with (P := SP segs (Kx (TR 0) md0) (E_po63 rq) rho); [| intros w Hw; exact Hw |].
  { intros w Hsp. unfold E_po63. apply SP_add1; [apply (SP_xforms segs _ xs_po rho (E_po rq) (E_po2 rq) w (xs_po_ok rq) Hsp) | | destruct rq; reflexivity].
    cbn [holds]. unfold bv_leu. rewrite U_lit64 by lia. rewrite (G_v28 rho HG). lia. }
  eapply run_tr; [exact (run_po63 rq) | destruct rq; reflexivity | apply okf |].
  intros L rho1 [<-|[]] Hag1; cbn [lf_state]. pose proof (GoodS_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HGS) as HGS1.
  eapply run_tr; [exact (run_fx2b rq) | destruct rq; reflexivity | apply okf |].
  intros L rho2 [<-|[]] Hag2; cbn [lf_state]. pose proof (GoodS_agree _ _ _ Hag2 ltac:(destruct rq; cbn; lia) HGS1) as HGS2.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hw. exists rho2. split; [exact HGS2 | exact Hw].
Qed.

Lemma eL_po63 : N = 63 -> forall rho : valuation, GoodS rho ->
  etriple segs (SP segs (Kx (TR 0) md0) (E_po rq) rho) (QS_at (E_Wb rq) 0).
Proof using Hargc Hent Hinp Hrq.
  intros HN rho HGS. pose proof (proj1 HGS) as HG.
  eapply etriple_conseq with (P := SP segs (Kx (TR 0) md0) (E_po63 rq) rho); [| intros w Hw; exact Hw |].
  { intros w Hsp. unfold E_po63. apply SP_add1; [apply (SP_xforms segs _ xs_po rho (E_po rq) (E_po2 rq) w (xs_po_ok rq) Hsp) | | destruct rq; reflexivity].
    cbn [holds]. unfold bv_leu. rewrite U_lit64 by lia. rewrite (G_v28 rho HG). lia. }
  eapply erun_tr; [exact (run_po63 rq) | destruct rq; reflexivity |].
  intros L rho1 [<-|[]] Hag1; cbn [lf_state]. pose proof (GoodS_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HGS) as HGS1.
  eapply erun_tr; [exact (run_fx2b rq) | destruct rq; reflexivity |].
  intros L rho2 [<-|[]] Hag2; cbn [lf_state]. pose proof (GoodS_agree _ _ _ Hag2 ltac:(destruct rq; cbn; lia) HGS1) as HGS2.
  intros w Hw. exists w. split; [apply wsteps_refl|]. exists rho2. split; [exact HGS2 | exact Hw].
Qed.

Lemma iovcnt_two : ltac2:(tb__ "0|1|
SaSbSbS4S0S3dQ40A1M0SeR3R2A2SeR3R1A2A3A1S0G0SeR4S12S77S12S7bS11Z0A1S12S7cR3R2A3A3S11Z1A1A3A2SeR4S11Z2A1A2A3F_;FB;FA;Frho;").
Proof using A1 ENVC Hargc JI L3 N RND.
  intros rho A B Hne. cbn [eval]. unfold alu64, alu.
  set (x := eval rho A) in *. set (y := eval rho B) in *.
  assert (Hx : bv_unsigned (bv_xor x y) <> 0).
  { rewrite bv_xor_unsigned. intros E. apply Hne. apply bv_eq. apply Z.lxor_eq. exact E. }
  unfold bv_ltu. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0.
  pose proof (bv_unsigned_in_range _ (bv_xor x y)) as R.
  destruct (Z.ltb_spec 0 (bv_unsigned (bv_xor x y))); [|lia].
  apply bv_eq. reflexivity.
Qed.

Lemma G_B544 : ltac2:(tb__ "0|1|
SaS43R1A1S0S7S3eQ40M0SeR2S8aA2A2S61S3eG0Vsp;A2Z230A2A3F_;Frho;").
Proof using Hargc Hent Hinp. intros rho HG. pose proof (bval_sound rho HG B544 (bv_unsigned sp + -560) eq_refl). lia. Qed.
Lemma G_LENa : ltac2:(tb__ "0|0|
SaS43R1A1S0S7S3eQ40SeR2Sa3A2A2S5cVN;Z12A2A3F_;Frho;").
Proof using Hargc Hent Hinp. intros rho HG. pose proof NU. unfold LENa. apply (J_add rho _ _ N 18 (G_v28 rho HG)); [apply U_lit64; lia | lia | lia | lia]. Qed.
Lemma G_LOnl : ltac2:(tb__ "0|0|
SaS43R1A1S0S7S1cR2Sa4A2S61VN;Z21fA2A3F_;Frho;").
Proof using Hargc Hent Hinp. intros rho HG. pose proof NU. unfold LOnl. apply (soff_add_small rho _ _ _ (G_v28 rho HG)); lia. Qed.
Lemma G_HInl : ltac2:(tb__ "0|0|
SaS43R1A1S0S7S1cR2Sa2A2S61VN;Z21eA2A3F_;Frho;").
Proof using Hargc Hent Hinp. intros rho HG. pose proof NU. unfold HInl. apply (soff_add_small rho _ _ _ (G_v28 rho HG)); lia. Qed.
Lemma G_IOV : ltac2:(tb__ "0|0|
SaS7S43R2A1S1S5bZ0R2A2S5bR2Z1A2A2S4S0S3dQ40A1SeR4S12S77S12S77S12S77SdP1A1S11N21fA1A3SdP1cA1A3S11R3A1A3A2SeR4S8aA2A3A1F_;F_;Fk;Frho;").
Proof using Hargc Hent Hinp.
  intros rho k HG Hk E. pose proof NU as NU'. apply (f_equal bv_unsigned) in E. rewrite (G_B544 rho HG) in E.
  erewrite (J_add rho _ _ (bv_unsigned sp - 543 + N) k) in E; [lia | | apply U_lit64; lia | lia | lia | lia].
  apply (J_add rho _ _ (bv_unsigned sp - 543) N); [| exact (G_v28 rho HG) | lia | lia | lia].
  pose proof (bval_sound rho HG (SAlu ALU_ADD (SVar 1) (SLit (-543))) (bv_unsigned sp + -543) eq_refl). lia.
Qed.

Lemma wa_intro : forall (rho : valuation) (w : world), N <= 62 -> GoodS rho ->
  SP segs (Kx (TR 0) md0) (E_Wa rq) rho w ->
  exists rho' : valuation, Good rho' /\ rl rho' 5 = MSG /\ rl rho' 6 = [] /\ SP segs (Kx (TR 0) md0) (E_Wa_c rq) rho' w.
Proof using Hargc Hent Hinp Hrq.
  intros rho [tr [ms md]] HN [HG H7] [Hsm Hk]. pose proof NU as NU'. pose proof L3_ge as HL3. pose proof A1_eq as EA1.
  destruct (E_Wa_nexts rq) as (Nxm & Nxx & Nxl1 & Nxm2).

  assert (Hsm0 : smatch segs rho (E_Wa_r rq) (tr, mkCfg ms md)).
  { refine (proj1 (SP_restate segs (Kx (TR 0) md0) rho (E_Wa rq) (E_Wa_r rq) _ _ _ (swf_E_Wa_r rq) (diff_wa rq) _ _ (conj Hsm Hk))); [|constructor].
    unfold diffs_ok. unfold IOVa. repeat constructor; cbn [fst snd]; apply iovcnt_two; apply (G_IOV rho 1 HG); lia. }

  pose proof (smatch_xforms segs xs_wa1 rho (E_Wa_r rq) (E_Wa_x rq) _ (xs_wa1_ok rq) Hsm0) as Hsm1.
  destruct (obj1_wa rq) as (Hn1 & Hlo1 & Hhi1 & Hwr1 & Harr1).
  pose proof (smatch_obj_to_list segs rho (E_Wa_x rq) _ 1 8 (obj (E_Wa_x rq) 1) (-560) (-543) BL_co Hsm1 Hn1 Hlo1 Hhi1
                ltac:(lia) ltac:(lia) Hwr1 Harr1 (cb_wa1 rq) (norl8_wa rq)) as Hsm2.
  rewrite (E_Wa_l1_eq rq), map_beval_BL_co in Hsm2.
  set (rho1 := rho_set_rl rho 8 M1) in Hsm2.
  assert (HG1 : Good rho1) by (apply Good_set_rl; [exact HG | lia]).

  destruct (obj3_wa rq) as (Hn3 & Hlo3 & Hhi3 & Hwr3 & Harr3 & Hb3).
  pose proof (smatch_obj_to_list_sym segs rho1 (E_Wa_l1 rq) _ 3 9 (obj (E_Wa_l1 rq) 3) (N - 543) (N - 542) [BLit 10] Hsm2 Hn3
                ltac:(rewrite Hlo3; exact (G_LOnl rho1 HG1)) ltac:(rewrite Hhi3; exact (G_HInl rho1 HG1))
                ltac:(lia) ltac:(lia) Hwr3 Harr3) as Hsm3.
  rewrite Hlo3 in Hsm3. replace (Z.to_nat (N - 542 - (N - 543))) with 1%nat in Hsm3 by lia.
  specialize (Hsm3 (cb_wa3 rq) (norl9_wa rq)). rewrite (E_Wa_l_eq rq) in Hsm3. cbn [map beval] in Hsm3.
  set (rho2 := rho_set_rl rho1 9 [Z_to_bv 8 10]) in Hsm3.
  assert (HG2 : Good rho2) by (apply Good_set_rl; [exact HG1 | lia]).

  set (rho3 := rho_set_rl rho2 10 (M1 ++ argv1)).
  assert (HG3 : Good rho3) by (apply Good_set_rl; [exact HG2 | lia]).
  assert (Hsm4 : smatch segs rho3 (E_Wa_m1 rq) (tr, mkCfg ms md)).
  { rewrite <- (E_Wa_m1_eq rq). destruct (m1_wa rq) as [Hm1 Hm2].
    apply (smatch_merge_lists segs rho3 (E_Wa_l rq) _ 1 10 _ _ 8 7 ltac:(apply smatch_set_rl; [exact (norl10_wa rq) | exact Hsm3]) Hm1 Hm2);
      cbn [ob_cells ob_dflt ob_base ob_lo ob_hi dlist_of dflt_writable];
      match goal with |- swf _ = true => rewrite (E_Wa_m1_eq rq); exact (swf_E_Wa_m1 rq) | _ => try (destruct rq; reflexivity) end.
    - rewrite (G_LOnl rho3 HG3), soff_lit_small by lia. lia.
    - cbn [rho3 rho2 rho1 rho_set_rl rl]. rewrite H7. reflexivity. }
  set (rho4 := rho_set_rl rho3 5 MSG).
  assert (HG4 : Good rho4) by (apply Good_set_rl; [exact HG3 | lia]).
  assert (Hsm5 : smatch segs rho4 (E_Wa_m2 rq) (tr, mkCfg ms md)).
  { rewrite <- (E_Wa_m2_eq rq). destruct (m2_wa rq) as [Hm1 Hm2].
    apply (smatch_merge_lists segs rho4 (E_Wa_m1 rq) _ 1 5 _ _ 10 9 ltac:(apply smatch_set_rl; [exact (norl5_wa rq) | exact Hsm4]) Hm1 Hm2);
      cbn [ob_cells ob_dflt ob_base ob_lo ob_hi dlist_of dflt_writable];
      match goal with |- swf _ = true => rewrite (E_Wa_m2_eq rq); exact (swf_E_Wa_m2 rq) | _ => try (destruct rq; reflexivity) end.
    rewrite (G_HInl rho4 HG4), soff_lit_small by lia. lia. }

  assert (Hsm6 : smatch segs rho4 (E_Wa_m rq) (tr, mkCfg ms md)).
  { rewrite <- (E_Wa_m_eq rq).
    apply (smatch_reframe_listobj segs rho4 (E_Wa_m2 rq) _ 1 _ 5 B544 (SLit 0) LENa Hsm5 (rf_wa rq) eq_refl eq_refl);
      cbn [ob_base ob_lo ob_hi]; match goal with |- swf _ = true => rewrite (E_Wa_m_eq rq); exact (swf_E_Wa_m rq) | _ => idtac end.
    - rewrite (G_B544 rho4 HG4), !soff_lit_small by lia. rewrite (G_v1 rho4 HG4). lia.
    - rewrite (G_B544 rho4 HG4), (G_HInl rho4 HG4). rewrite (J_soff_small rho4 _ _ (G_LENa rho4 HG4)) by lia. rewrite (G_v1 rho4 HG4). lia. }

  set (rho5 := rho_set_rl rho4 6 []).
  assert (HG5 : Good rho5) by (apply Good_set_rl; [exact HG4 | lia]).
  assert (Hsm7 : smatch segs rho5 (E_Wa_c0 rq) (tr, mkCfg ms md)).
  { rewrite <- (E_Wa_c0_eq rq). unfold app_objs.
    apply (smatch_carve_listobj segs rho5 (E_Wa_m rq) _ (SLit 0) (SLit 0) (SLit 0) 0 0 (DRom 6) 6 (ss_next (E_Wa_m rq))
             ltac:(apply smatch_set_rl; [exact (norl6_wa rq) | exact Hsm6]) eq_refl); rewrite ?U_lit64 by lia.
    - by_r swf_E_Wa_c0.
    - apply soff_lit_small. lia.
    - apply soff_lit_small. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - reflexivity.
    - solve_disjr HG5.
    - intros off Hoff D. discriminate D.
    - intros off Hoff. lia. }
  exists rho5. split; [exact HG5|]. split; [reflexivity|]. split; [reflexivity|]. split; [|exact Hk].
  exact (smatch_xforms segs xs_wa2 rho5 (E_Wa_c0 rq) (E_Wa_c rq) _ (xs_wa2_ok rq) Hsm7).
Qed.

Lemma wa_window : ltac2:(tb__ "0|2|
S0S2bS3dQ8A1M0A1S33G0S45S30G0A1A3M1S71G0S2cG0G1A2S72G0U0S45A3A3A3").
Proof using . rewrite app_nil_r. cbn [skipn]. rewrite firstn_all. reflexivity. Qed.

Lemma L_Wa : forall rho : valuation, Good rho -> rl rho 5 = MSG -> rl rho 6 = [] ->
  triple segs ok (SP segs (Kx (TR 0) md0) (E_Wa_c rq) rho) (Q_at (T_Da rq) (length MSG)).
Proof using Hargc Hent Hfds0 Hrdr0 Hinp HokK HokP Hrq.
  intros rho HG H5 H6. destruct s_wa_vals as (S12 & S13 & S14 & S15). pose proof NU as NU'. pose proof MSG_len as ML.
  apply (call_path segs (PRw MSG []) ok (Kx (TR 0) md0) (WLerr.Kw (Kx (TR 0) md0) MSG [] (length (WLerr.MSG MSG [])))
           (E_Wa_c rq) (E_Wa_c rq) WLerrS.Pre_wl2 [] s_wa (R_wa rq) WLerr.Posts_wl _ rho
           eq_refl (efr_wa rq) (chk_wa rq) ltac:(rewrite (facts_wac rq); exact (fb_wa rq))).
  - intros rho1 HPR. apply (wl2_call 0 MSG [] rho1 ltac:(rewrite ML; lia) wa_window HPR).
  - intros ms _. unfold PRw. rewrite rl_call, !rw_call, S13, S15. split; [exact H5|]. split; [exact H6|].
    split; [rewrite (G_LENa rho HG), ML; lia | rewrite U_lit64 by lia; reflexivity].
  - intros L rho' [<-|[]] Hag HF. cbn [lf_state]. rewrite (facts_wac rq) in HF.
    change (ss_next WLerrS.Pre_wl2) with 92%positive. rewrite (T_Dai_eq rq).
    eapply triple_conseq with (P := SP segs (Kx (TR (length MSG)) md0) (T_Dai rq) rho'); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [exact Hsm|]. apply (Kw_TR 0 MSG [] _ _ _ wa_window) in HK.
      unfold WLerr.MSG in HK. rewrite app_nil_r, Nat.min_id in HK. exact HK. }
    apply (post_path segs ok _ (T_Dai rq) (T_Da rq) (ss_facts (E_Wa rq)) [] rho' _ (fb_da rq) (xs_da_ok rq) HF).
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. exists rho'. split; [exact (Good_agree _ _ _ Hag ltac:(destruct rq; cbn; lia) HG) | exact Hw].
Qed.

Lemma eL_Wa : forall rho : valuation, Good rho -> rl rho 5 = MSG -> rl rho 6 = [] ->
  etriple segs (SP segs (Kx (TR 0) md0) (E_Wa_c rq) rho) (Q_at (T_Da rq) (length MSG)).
Proof using Hargc Hent Hfds0 Hrdr0 Hinp Hrq.
  intros rho HG H5 H6. destruct s_wa_vals as (S12 & S13 & S14 & S15). pose proof NU as NU'. pose proof MSG_len as ML.
  apply (ecall_path segs (PRw MSG []) (Kx (TR 0) md0) (WLerr.Kw (Kx (TR 0) md0) MSG [] (length (WLerr.MSG MSG [])))
           (E_Wa_c rq) (E_Wa_c rq) WLerrS.Pre_wl2 [] s_wa (R_wa rq) WLerr.Posts_wl _ rho
           eq_refl (efr_wa rq) (chk_wa rq) ltac:(rewrite (facts_wac rq); exact (fb_wa rq))).
  - intros rho1 HPR. apply (wl2_ecall 0 MSG [] rho1 ltac:(rewrite ML; lia) wa_window HPR).
  - intros ms _. unfold PRw. rewrite rl_call, !rw_call, S13, S15. split; [exact H5|]. split; [exact H6|].
    split; [rewrite (G_LENa rho HG), ML; lia | rewrite U_lit64 by lia; reflexivity].
  - intros L rho' [<-|[]] Hag HF. cbn [lf_state]. rewrite (facts_wac rq) in HF.
    change (ss_next WLerrS.Pre_wl2) with 92%positive. rewrite (T_Dai_eq rq).
    eapply etriple_conseq with (P := SP segs (Kx (TR (length MSG)) md0) (T_Dai rq) rho'); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [exact Hsm|]. apply (Kw_TR 0 MSG [] _ _ _ wa_window) in HK.
      unfold WLerr.MSG in HK. rewrite app_nil_r, Nat.min_id in HK. exact HK. }
    apply (epost_path segs _ (T_Dai rq) (T_Da rq) (ss_facts (E_Wa rq)) [] rho' _ (fb_da rq) (xs_da_ok rq) HF).
    intros w Hw. exists w. split; [apply wsteps_refl|]. exists rho'. split; [exact (Good_agree _ _ _ Hag ltac:(destruct rq; cbn; lia) HG) | exact Hw].
Qed.

Lemma L_exa : forall rho : valuation, Good rho ->
  triple segs ok (SP segs (Kx (TR (length MSG)) md0) (T_Da rq) rho) (fun _ : world => False).
Proof using Hargc Hfs HokK HokP Hokh Hrq.
  intros rho HG. eapply run_tr; [exact (run_da rq) | destruct rq; reflexivity | apply okf |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  destruct (cert_exa rq) as (Hi & H17 & H10).
  apply (triple_exit_eval segs ok SpecT (Kx (TR (length MSG)) md0) (E_exa rq) rho1 2);
    [apply okf | apply okp | exact Hokh | exact Hi | left; exact H17 | rewrite H10; rewrite U_lit64 by lia; reflexivity |].
  intros tr md [-> ->]. rewrite TR_all by lia. rewrite Hfs. exact final_in_spec.
Qed.

Lemma eL_exa : forall rho : valuation, Good rho ->
  etriple segs (SP segs (Kx (TR (length MSG)) md0) (T_Da rq) rho) (fun w : world => w_tr w = wr 2 MSG ++ [ex fs 2]).
Proof using Hargc Hfs Hrq.
  intros rho HG. eapply erun_tr; [exact (run_da rq) | destruct rq; reflexivity |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state].
  destruct (cert_exa rq) as (Hi & H17 & H10).
  eapply etriple_conseq; [intros w Hw; exact Hw | |
    apply (etriple_exit_eval segs (Kx (TR (length MSG)) md0) (E_exa rq) rho1 2 Hi (or_introl H17))].
  - intros w (tr & md & [-> ->] & ->). rewrite TR_all by lia. rewrite Hfs. reflexivity.
  - rewrite H10. rewrite U_lit64 by lia. reflexivity.
Qed.

Lemma G_IOV0 : ltac2:(tb__ "0|0|
SaS43R1A1S4S0S3dQ40A1SeR2S12S77S12S77SdP1A1S11N21fA1A3SdP1cA1A3A2SeR2S8aA2A3A1F_;Frho;").
Proof using Hargc Hent Hinp.
  intros rho HG E. pose proof NU as NU'. apply (f_equal bv_unsigned) in E. rewrite (G_B544 rho HG) in E.
  erewrite (J_add rho _ _ (bv_unsigned sp - 543) N) in E; [lia | | exact (G_v28 rho HG) | lia | lia | lia].
  pose proof (bval_sound rho HG (SAlu ALU_ADD (SVar 1) (SLit (-543))) (bv_unsigned sp + -543) eq_refl). lia.
Qed.

Lemma nl_eq : ltac2:(tb__ "0|2|
S0S2bS3dQ8M0A1M1A1SacS32G1S3fG0ZaA2S30G1A1A3A3"). Proof using . reflexivity. Qed.

Lemma wb_intro : forall (rho : valuation) (w : world), N = 63 -> GoodS rho ->
  SP segs (Kx (TR 0) md0) (E_Wb rq) rho w ->
  exists rho' : valuation, Good rho' /\ rl rho' 5 = M1 ++ argv1 /\ rl rho' 6 = nl
    /\ SP segs (Kx (TR 0) md0) (E_Wb_c rq) rho' w.
Proof using Hargc Hent Hinp Hrq.
  intros rho [tr [ms md]] HN [HG H7] [Hsm Hk]. pose proof NU as NU'. pose proof L3_ge as HL3. pose proof A1_eq as EA1.
  destruct (E_Wb_nexts rq) as (Nxm & Nxx & Nxm1).

  assert (Hsm0 : smatch segs rho (E_Wb_r rq) (tr, mkCfg ms md)).
  { refine (proj1 (SP_restate segs (Kx (TR 0) md0) rho (E_Wb rq) (E_Wb_r rq) _ _ _ (swf_E_Wb_r rq) (diff_wb rq) _ _ (conj Hsm Hk))); [|constructor].
    unfold diffs_ok. unfold IOVb. repeat constructor; cbn [fst snd]; apply iovcnt_two; apply (G_IOV0 rho HG). }

  pose proof (smatch_xforms segs xs_wb1 rho (E_Wb_r rq) (E_Wb_x rq) _ (xs_wb1_ok rq) Hsm0) as Hsm1.
  destruct (obj1_wb rq) as (Hn1 & Hlo1 & Hhi1 & Hwr1 & Harr1).
  pose proof (smatch_obj_to_list segs rho (E_Wb_x rq) _ 1 8 (obj (E_Wb_x rq) 1) (-560) (-543) BL_co Hsm1 Hn1 Hlo1 Hhi1
                ltac:(lia) ltac:(lia) Hwr1 Harr1 (cb_wb1 rq) (norl8_wb rq)) as Hsm2.
  rewrite (E_Wb_l_eq rq), map_beval_BL_co in Hsm2.
  set (rho1 := rho_set_rl rho 8 M1) in Hsm2.
  assert (HG1 : Good rho1) by (apply Good_set_rl; [exact HG | lia]).

  set (rho2 := rho_set_rl rho1 5 (M1 ++ argv1)).
  assert (HG2 : Good rho2) by (apply Good_set_rl; [exact HG1 | lia]).
  assert (Hsm3 : smatch segs rho2 (E_Wb_m1 rq) (tr, mkCfg ms md)).
  { rewrite <- (E_Wb_m1_eq rq). destruct (m_wb rq) as [Hm1 Hm2].
    apply (smatch_merge_lists segs rho2 (E_Wb_l rq) _ 1 5 _ _ 8 7 ltac:(apply smatch_set_rl; [exact (norl5_wb rq) | exact Hsm2]) Hm1 Hm2);
      cbn [ob_cells ob_dflt ob_base ob_lo ob_hi dlist_of dflt_writable];
      match goal with |- swf _ = true => rewrite (E_Wb_m1_eq rq); exact (swf_E_Wb_m1 rq) | _ => try (destruct rq; reflexivity) end.
    - rewrite (G_LOnl rho2 HG2), soff_lit_small by lia. lia.
    - cbn [rho2 rho1 rho_set_rl rl]. rewrite H7. reflexivity. }

  assert (Hsm4 : smatch segs rho2 (E_Wb_m rq) (tr, mkCfg ms md)).
  { rewrite <- (E_Wb_m_eq rq).
    apply (smatch_reframe_listobj segs rho2 (E_Wb_m1 rq) _ 1 _ 5 B544 (SLit 0) (SLit 80) Hsm3 (rf_wb rq) eq_refl eq_refl);
      cbn [ob_base ob_lo ob_hi]; match goal with |- swf _ = true => rewrite (E_Wb_m_eq rq); exact (swf_E_Wb_m rq) | _ => idtac end.
    - rewrite (G_B544 rho2 HG2), !soff_lit_small by lia. rewrite (G_v1 rho2 HG2). lia.
    - rewrite (G_B544 rho2 HG2), (G_LOnl rho2 HG2), soff_lit_small by lia. rewrite (G_v1 rho2 HG2). lia. }

  set (rho3 := rho_set_rl rho2 6 nl).
  assert (HG3 : Good rho3) by (apply Good_set_rl; [exact HG2 | lia]).
  destruct img_nl as [Himg Hro].
  assert (Hsm5 : smatch segs rho3 (E_Wb_c0 rq) (tr, mkCfg ms md)).
  { rewrite <- (E_Wb_c0_eq rq). unfold app_objs.
    apply (ReprGlue.smatch_carve_rom segs rho3 (E_Wb_m rq) _ nl_addr 1 6 (ss_next (E_Wb_m rq))
             ltac:(apply smatch_set_rl; [exact (norl6_wb rq) | exact Hsm4])).
    - by_r swf_E_Wb_c0.
    - unfold nl_addr. lia.
    - lia.
    - unfold nl_addr. lia.
    - reflexivity.
    - intros k Hk0. replace k with 0 by lia. rewrite Z.add_0_r. split; [exact Hro | exact Himg].
    - unfold nl_addr. solve_disjr HG3. }
  exists rho3. split; [exact HG3|]. split; [reflexivity|]. split; [reflexivity|]. split; [|exact Hk].
  exact (smatch_xforms segs xs_wb2 rho3 (E_Wb_c0 rq) (E_Wb_c rq) _ (xs_wb2_ok rq) Hsm5).
Qed.

Lemma wb_window : ltac2:(tb__ "0|2|
S0S2bS3dQ8A1M0A1S33G0S33G0S48Vargv1;A3SacA3M1S71G0S2cG0G1A2S72G0U0S45A3A3A3").
Proof using . unfold MSG. rewrite <- app_assoc. cbn [skipn]. rewrite firstn_all. reflexivity. Qed.

Lemma L_Wb : N = 63 -> forall rho : valuation, Good rho -> rl rho 5 = M1 ++ argv1 -> rl rho 6 = nl ->
  triple segs ok (SP segs (Kx (TR 0) md0) (E_Wb_c rq) rho) (Q_at (T_Db rq) (length MSG)).
Proof using Hargc Hent Hfds0 Hrdr0 Hinp HokK HokP Hrq.
  intros HN rho HG H5 H6. destruct s_wb_vals as (S12 & S13 & S14 & S15). pose proof NU as NU'. pose proof MSG_len as ML.
  apply (call_path segs (PRw (M1 ++ argv1) nl) ok (Kx (TR 0) md0) (WLerr.Kw (Kx (TR 0) md0) (M1 ++ argv1) nl (length (WLerr.MSG (M1 ++ argv1) nl)))
           (E_Wb_c rq) (E_Wb_c rq) WLerrS.Pre_wl2 [] s_wb (R_wb rq) WLerr.Posts_wl _ rho
           eq_refl (efr_wb rq) (chk_wb rq) ltac:(rewrite (facts_wbc rq); exact (fb_wb rq))).
  - intros rho1 HPR. apply (wl2_call 0 (M1 ++ argv1) nl rho1 ltac:(rewrite length_app, M1_len; lia) wb_window HPR).
  - intros ms _. unfold PRw. rewrite rl_call, !rw_call, S13, S15. split; [exact H5|]. split; [exact H6|].
    split; rewrite U_lit64 by lia; [rewrite length_app, M1_len; unfold N in HN; lia | reflexivity].
  - intros L rho' [<-|[]] Hag HF. cbn [lf_state]. rewrite (facts_wbc rq) in HF.
    change (ss_next WLerrS.Pre_wl2) with 92%positive. rewrite (T_Dbi_eq rq).
    eapply triple_conseq with (P := SP segs (Kx (TR (length MSG)) md0) (T_Dbi rq) rho'); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [exact Hsm|]. apply (Kw_TR 0 (M1 ++ argv1) nl _ _ _ wb_window) in HK.
      unfold WLerr.MSG in HK. rewrite Nat.min_id in HK. unfold MSG. rewrite <- app_assoc in HK. exact HK. }
    apply (post_path segs ok _ (T_Dbi rq) (T_Db rq) (ss_facts (E_Wb rq)) [] rho' _ (fb_db rq) (xs_db_ok rq) HF).
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. exists rho'. split; [exact (Good_agree _ _ _ Hag ltac:(destruct rq; cbn; lia) HG) | exact Hw].
Qed.

Lemma eL_Wb : N = 63 -> forall rho : valuation, Good rho -> rl rho 5 = M1 ++ argv1 -> rl rho 6 = nl ->
  etriple segs (SP segs (Kx (TR 0) md0) (E_Wb_c rq) rho) (Q_at (T_Db rq) (length MSG)).
Proof using Hargc Hent Hfds0 Hrdr0 Hinp Hrq.
  intros HN rho HG H5 H6. destruct s_wb_vals as (S12 & S13 & S14 & S15). pose proof NU as NU'. pose proof MSG_len as ML.
  apply (ecall_path segs (PRw (M1 ++ argv1) nl) (Kx (TR 0) md0) (WLerr.Kw (Kx (TR 0) md0) (M1 ++ argv1) nl (length (WLerr.MSG (M1 ++ argv1) nl)))
           (E_Wb_c rq) (E_Wb_c rq) WLerrS.Pre_wl2 [] s_wb (R_wb rq) WLerr.Posts_wl _ rho
           eq_refl (efr_wb rq) (chk_wb rq) ltac:(rewrite (facts_wbc rq); exact (fb_wb rq))).
  - intros rho1 HPR. apply (wl2_ecall 0 (M1 ++ argv1) nl rho1 ltac:(rewrite length_app, M1_len; lia) wb_window HPR).
  - intros ms _. unfold PRw. rewrite rl_call, !rw_call, S13, S15. split; [exact H5|]. split; [exact H6|].
    split; rewrite U_lit64 by lia; [rewrite length_app, M1_len; unfold N in HN; lia | reflexivity].
  - intros L rho' [<-|[]] Hag HF. cbn [lf_state]. rewrite (facts_wbc rq) in HF.
    change (ss_next WLerrS.Pre_wl2) with 92%positive. rewrite (T_Dbi_eq rq).
    eapply etriple_conseq with (P := SP segs (Kx (TR (length MSG)) md0) (T_Dbi rq) rho'); [| intros w Hw; exact Hw |].
    { intros w [Hsm HK]. split; [exact Hsm|]. apply (Kw_TR 0 (M1 ++ argv1) nl _ _ _ wb_window) in HK.
      unfold WLerr.MSG in HK. rewrite Nat.min_id in HK. unfold MSG. rewrite <- app_assoc in HK. exact HK. }
    apply (epost_path segs _ (T_Dbi rq) (T_Db rq) (ss_facts (E_Wb rq)) [] rho' _ (fb_db rq) (xs_db_ok rq) HF).
    intros w Hw. exists w. split; [apply wsteps_refl|]. exists rho'. split; [exact (Good_agree _ _ _ Hag ltac:(destruct rq; cbn; lia) HG) | exact Hw].
Qed.

Lemma pending_obj : ltac2:(tb__ "0|1|
SaS10S2bS52A1M0Sc3S53S31SfSd6S6R7R6S37G0Se7R5Se9R4R3A2A4A4S0S2fSfA1SbcSfS1dR7A1R3A3S2eSfR2A2A3S24S6R9R6R3A4F_;F_;Fo;Fi;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md i o Hsp Hn. destruct (smatch_pending_mem segs _ _ _ _ _ Hsp) as (Hall & _ & _).
  exact (Forall_nth_error _ _ _ _ Hall Hn).
Qed.

Lemma L_wz : forall rho : valuation, Good rho ->
  triple segs ok (SP segs (Kx (TR (length MSG)) md0) (T_Db rq) rho) (fun _ : world => False).
Proof using Hargc Hent Hfds0 Hrdr0 Hfs Hinp HokK HokP Hokh Hrq.
  intros rho HG. pose proof NU as NU'.
  destruct (cert_wz rq) as (Hi & H17 & H10 & H12 & R11 & Hnz & Hbz & C1 & C2).
  eapply run_tr; [exact (run_db rq) | destruct rq; reflexivity | apply okf |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state]. pose proof (Good_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HG) as HG1.
  eapply triple_seq.
  { apply triple1_triple.
    apply (triple1_writev01J segs ok (liftK (Kx (TR (length MSG)) md0)) (E_Wz rq) rho1 2);
      [apply ok_frame_liftK; apply okf
      | eapply ok_pframeJ_of_tcons; [apply HokP; intros tr0 md0_ H0; exact H0 | intros r tr' md' Hk'; exact (Ktc _ _ tr' md' Hk')]
      | exact Hi | exact H17 | exact H10 | exact H12 | lia | intros r tr' md' Hk'; exact (Kx_fd2 _ _ _ Hk') |].
    intros tr ms md Hsp _. rewrite R11.
    pose proof (pending_obj rho1 (E_Wz rq) tr ms md ozi _ Hsp Hnz) as Ho.
    assert (A0 : bv_unsigned (eval rho1 (SAlu ALU_ADD (SVar 1) (SLit (-664)))) = bv_unsigned sp - 664).
    { pose proof (bval_sound rho1 HG1 (SAlu ALU_ADD (SVar 1) (SLit (-664))) (bv_unsigned sp + -664) eq_refl). lia. }
    exists (eval rho1 (SLit 0)). split.
    - apply (cell_read_u64 segs rho1 ms (obj (E_Wz rq) ozi) (SLit (-664)) (SLit 0) _ Ho (In_cellb _ _ C1)).
      rewrite Hbz, A0, soff_lit_small by lia. rewrite (G_v1 rho1 HG1). lia.
    - split; [|split; [rewrite A0; unfold TASK_SIZE; lia | rewrite U_lit64 by lia; unfold TASK_SIZE; lia]].
      change (Z_to_bv 64 0) with (eval rho1 (SLit 0)).
      apply (cell_read_u64 segs rho1 ms (obj (E_Wz rq) ozi) (SLit (-656)) (SLit 0) _ Ho (In_cellb _ _ C2)).
      rewrite Hbz, soff_lit_small by lia. rewrite (G_v1 rho1 HG1).
      rewrite bv_add_unsigned, A0. change (bv_unsigned 8%bv) with 8. unfold bv_wrap. rewrite mod64, Z.mod_small by lia. lia. }
  change (SPJ segs (liftK (Kx (TR (length MSG)) md0)) (S_after (E_Wz rq) (SLit 0) (ss_objs (E_Wz rq)) (ss_next (E_Wz rq))) rho1)
    with (SP segs (Kx (TR (length MSG)) md0) (S_after (E_Wz rq) (SLit 0) (ss_objs (E_Wz rq)) (ss_next (E_Wz rq))) rho1).
  rewrite (PZ_eq rq).
  eapply run_tr; [exact (run_pz rq) | destruct rq; reflexivity | apply okf |].
  intros L rho2 [<-|[]] Hag2. cbn [lf_state].
  destruct (cert_exb rq) as (Hix & H17x & H10x).
  apply (triple_exit_eval segs ok SpecT (Kx (TR (length MSG)) md0) (E_exb rq) rho2 2);
    [apply okf | apply okp | exact Hokh | exact Hix | left; exact H17x | rewrite H10x; rewrite U_lit64 by lia; reflexivity |].
  intros tr md [-> ->]. rewrite TR_all by lia. rewrite Hfs. exact final_in_spec.
Qed.

Lemma eL_wz : forall rho : valuation, Good rho ->
  etriple segs (SP segs (Kx (TR (length MSG)) md0) (T_Db rq) rho) (fun w : world => w_tr w = wr 2 MSG ++ [ex fs 2]).
Proof using Hargc Hent Hfds0 Hrdr0 Hfs Hinp Hrq.
  intros rho HG. pose proof NU as NU'.
  destruct (cert_wz rq) as (Hi & H17 & H10 & H12 & R11 & Hnz & Hbz & C1 & C2).
  eapply erun_tr; [exact (run_db rq) | destruct rq; reflexivity |].
  intros L rho1 [<-|[]] Hag1. cbn [lf_state]. pose proof (Good_agree _ _ _ Hag1 ltac:(destruct rq; cbn; lia) HG) as HG1.
  eapply etriple_seq.
  { apply (etriple_writev01J segs (liftK (Kx (TR (length MSG)) md0)) (E_Wz rq) rho1 2);
      [exact Hi | exact H17 | exact H10 | exact H12 | lia | intros r tr md Hk; exact (Kx_fd2 _ _ _ Hk) |].
    intros tr ms md Hsp _. rewrite R11.
    pose proof (pending_obj rho1 (E_Wz rq) tr ms md ozi _ Hsp Hnz) as Ho.
    assert (A0 : bv_unsigned (eval rho1 (SAlu ALU_ADD (SVar 1) (SLit (-664)))) = bv_unsigned sp - 664).
    { pose proof (bval_sound rho1 HG1 (SAlu ALU_ADD (SVar 1) (SLit (-664))) (bv_unsigned sp + -664) eq_refl). lia. }
    exists (eval rho1 (SLit 0)). split.
    - apply (cell_read_u64 segs rho1 ms (obj (E_Wz rq) ozi) (SLit (-664)) (SLit 0) _ Ho (In_cellb _ _ C1)).
      rewrite Hbz, A0, soff_lit_small by lia. rewrite (G_v1 rho1 HG1). lia.
    - split; [|split; [rewrite A0; unfold TASK_SIZE; lia | rewrite U_lit64 by lia; unfold TASK_SIZE; lia]].
      change (Z_to_bv 64 0) with (eval rho1 (SLit 0)).
      apply (cell_read_u64 segs rho1 ms (obj (E_Wz rq) ozi) (SLit (-656)) (SLit 0) _ Ho (In_cellb _ _ C2)).
      rewrite Hbz, soff_lit_small by lia. rewrite (G_v1 rho1 HG1).
      rewrite bv_add_unsigned, A0. change (bv_unsigned 8%bv) with 8. unfold bv_wrap. rewrite mod64, Z.mod_small by lia. lia. }
  change (SPJ segs (liftK (Kx (TR (length MSG)) md0)) (S_after (E_Wz rq) (SLit 0) (ss_objs (E_Wz rq)) (ss_next (E_Wz rq))) rho1)
    with (SP segs (Kx (TR (length MSG)) md0) (S_after (E_Wz rq) (SLit 0) (ss_objs (E_Wz rq)) (ss_next (E_Wz rq))) rho1).
  rewrite (PZ_eq rq).
  eapply erun_tr; [exact (run_pz rq) | destruct rq; reflexivity |].
  intros L rho2 [<-|[]] Hag2. cbn [lf_state].
  destruct (cert_exb rq) as (Hix & H17x & H10x).
  eapply etriple_conseq; [intros w Hw; exact Hw | |
    apply (etriple_exit_eval segs (Kx (TR (length MSG)) md0) (E_exb rq) rho2 2 Hix (or_introl H17x))].
  - intros w (tr & md & [-> ->] & ->). rewrite TR_all by lia. rewrite Hfs. reflexivity.
  - rewrite H10x. rewrite U_lit64 by lia. reflexivity.
Qed.

Theorem copenS_safe : forall q k : nat, check_nr rq q k = true -> N = Z.of_nat k -> A1 mod 4 = Z.of_nat q -> N <= 63 ->
  forall rho : valuation, Good rho -> triple segs ok (SP segs (Kx (TR 0) md0) (T_cs1 rq) rho) (fun _ : world => False).
Proof using Hargc Hent Hfds0 Hrdr0 Hfs Hinp HokK HokP Hokh Hrq.
  intros q k Hnr Hn Hr HN rho HG.
  assert (Hchk : check_core rq (Z.of_nat k) (Z.of_nat q) (sym_run segs FUELm [ret_out] (the_pre rq (Z.of_nat k) (Z.of_nat q)) true) = true) by exact Hnr.
  eapply triple_seq; [exact (L_sm HN rho HG)|].
  apply triple_ex; intros rho1. apply triple_pure; intros HG1.
  apply (triple_from ok _ (fun r w => (GoodS r /\ rw r 70 = Z_to_bv 64 V70) /\ SP segs (Kx (TR 0) md0) (E_fxA rq) r w)).
  { intros w Hw. destruct (fxA_intro rho1 w HG1 Hw) as (r & A & B & C). exists r. auto. }
  intros rho2. apply triple_pure. intros [HGS2 H70].
  eapply triple_seq; [exact (L_nr _ _ Hchk Hn Hr HN rho2 HGS2 H70)|].
  apply triple_ex; intros rho3. apply triple_pure; intros HGS3.
  destruct (Z_le_gt_dec N 62) as [H62|H63].
  - eapply triple_seq; [exact (L_po62 H62 rho3 HGS3)|].
    apply triple_ex; intros rho4. apply triple_pure; intros HGS4.
    apply (triple_from ok _ (fun r w => (Good r /\ rl r 5 = MSG /\ rl r 6 = []) /\ SP segs (Kx (TR 0) md0) (E_Wa_c rq) r w)).
    { intros w Hw. destruct (wa_intro rho4 w H62 HGS4 Hw) as (r & A & B & C & D). exists r. auto. }
    intros rho5. apply triple_pure. intros (HG5 & H5 & H6).
    eapply triple_seq; [exact (L_Wa rho5 HG5 H5 H6)|].
    apply triple_ex; intros rho6. apply triple_pure; intros HG6.
    exact (L_exa rho6 HG6).
  - assert (H63' : N = 63) by lia.
    eapply triple_seq; [exact (L_po63 H63' rho3 HGS3)|].
    apply triple_ex; intros rho4. apply triple_pure; intros HGS4.
    apply (triple_from ok _ (fun r w => (Good r /\ rl r 5 = M1 ++ argv1 /\ rl r 6 = nl) /\ SP segs (Kx (TR 0) md0) (E_Wb_c rq) r w)).
    { intros w Hw. destruct (wb_intro rho4 w H63' HGS4 Hw) as (r & A & B & C & D). exists r. auto. }
    intros rho5. apply triple_pure. intros (HG5 & H5 & H6).
    eapply triple_seq; [exact (L_Wb H63' rho5 HG5 H5 H6)|].
    apply triple_ex; intros rho6. apply triple_pure; intros HG6.
    exact (L_wz rho6 HG6).
Qed.

Theorem copenS_exists : forall q k : nat, check_nr rq q k = true -> N = Z.of_nat k -> A1 mod 4 = Z.of_nat q -> N <= 63 ->
  forall rho : valuation, Good rho ->
  etriple segs (SP segs (Kx (TR 0) md0) (T_cs1 rq) rho) (fun w : world => w_tr w = wr 2 MSG ++ [ex fs 2]).
Proof using Hargc Hent Hfds0 Hrdr0 Hfs Hinp Hrq.
  intros q k Hnr Hn Hr HN rho HG.
  assert (Hchk : check_core rq (Z.of_nat k) (Z.of_nat q) (sym_run segs FUELm [ret_out] (the_pre rq (Z.of_nat k) (Z.of_nat q)) true) = true) by exact Hnr.
  eapply etriple_seq; [exact (eL_sm HN rho HG)|].
  apply etriple_ex; intros rho1. apply etriple_pure; intros HG1.
  apply (etriple_from _ (fun r w => (GoodS r /\ rw r 70 = Z_to_bv 64 V70) /\ SP segs (Kx (TR 0) md0) (E_fxA rq) r w)).
  { intros w Hw. destruct (fxA_intro rho1 w HG1 Hw) as (r & A & B & C). exists r. auto. }
  intros rho2. apply etriple_pure. intros [HGS2 H70].
  eapply etriple_seq; [exact (eL_nr _ _ Hchk Hn Hr HN rho2 HGS2 H70)|].
  apply etriple_ex; intros rho3. apply etriple_pure; intros HGS3.
  destruct (Z_le_gt_dec N 62) as [H62|H63].
  - eapply etriple_seq; [exact (eL_po62 H62 rho3 HGS3)|].
    apply etriple_ex; intros rho4. apply etriple_pure; intros HGS4.
    apply (etriple_from _ (fun r w => (Good r /\ rl r 5 = MSG /\ rl r 6 = []) /\ SP segs (Kx (TR 0) md0) (E_Wa_c rq) r w)).
    { intros w Hw. destruct (wa_intro rho4 w H62 HGS4 Hw) as (r & A & B & C & D). exists r. auto. }
    intros rho5. apply etriple_pure. intros (HG5 & H5 & H6).
    eapply etriple_seq; [exact (eL_Wa rho5 HG5 H5 H6)|].
    apply etriple_ex; intros rho6. apply etriple_pure; intros HG6.
    exact (eL_exa rho6 HG6).
  - assert (H63' : N = 63) by lia.
    eapply etriple_seq; [exact (eL_po63 H63' rho3 HGS3)|].
    apply etriple_ex; intros rho4. apply etriple_pure; intros HGS4.
    apply (etriple_from _ (fun r w => (Good r /\ rl r 5 = M1 ++ argv1 /\ rl r 6 = nl) /\ SP segs (Kx (TR 0) md0) (E_Wb_c rq) r w)).
    { intros w Hw. destruct (wb_intro rho4 w H63' HGS4 Hw) as (r & A & B & C & D). exists r. auto. }
    intros rho5. apply etriple_pure. intros (HG5 & H5 & H6).
    eapply etriple_seq; [exact (eL_Wb H63' rho5 HG5 H5 H6)|].
    apply etriple_ex; intros rho6. apply etriple_pure; intros HG6.
    exact (eL_wz rho6 HG6).
Qed.

(* The loop checks, for both values of the CONFIG_RSEQ flag. *)
Definition checks_S : Prop :=
  forall (b : bool) (q k : nat), (q < 4)%nat -> (k < 64)%nat -> check_nr b q k = true.

Theorem copen_safe_r : checks_S -> forall rho : valuation, J25 sp mb draw inp rho ->
  triple segs ok (SP segs (Kx [] md0) (S_operr rq) rho) (fun _ : world => False).
Proof using Hargc Hent Hfds0 Hrdr0 Hfs Hinp HokK HokP Hokh Hrq.
  intros Hchk rho HJ. pose proof NU as NU'. pose proof V70_eq as (EV & RV & MV).
  apply (triple_from ok _ (fun r w => Good r /\ SP segs (Kx (TR 0) md0) (S_co rq) r w)).
  { intros w Hw. destruct (co_intro rho w HJ Hw) as (r & A & B). exists r. rewrite TR0. auto. }
  intros rho1. apply triple_pure. intros HG1.
  eapply triple_seq; [exact (L_call rho1 HG1)|].
  apply triple_ex; intros rho2. apply triple_pure; intros HG2.
  destruct (Z_le_gt_dec 64 N) as [H64|HS].
  - exact (copen64_safe H64 rho2 HG2).
  - apply (copenS_safe (Z.to_nat (A1 mod 4)) (length argv1)); [apply Hchk; lia | reflexivity | lia | lia | exact HG2].
Qed.

Theorem copen_exists_r : checks_S -> forall rho : valuation, J25 sp mb draw inp rho ->
  etriple segs (SP segs (Kx [] md0) (S_operr rq) rho) (fun w : world => w_tr w = die fs (msg_cannot_open argv1)).
Proof using Hargc Hent Hfds0 Hrdr0 Hfs Hinp Hrq.
  intros Hchk rho HJ. pose proof NU as NU'. pose proof V70_eq as (EV & RV & MV).
  unfold die. rewrite <- MSG_eq.
  apply (etriple_from _ (fun r w => Good r /\ SP segs (Kx (TR 0) md0) (S_co rq) r w)).
  { intros w Hw. destruct (co_intro rho w HJ Hw) as (r & A & B). exists r. rewrite TR0. auto. }
  intros rho1. apply etriple_pure. intros HG1.
  eapply etriple_seq; [exact (eL_call rho1 HG1)|].
  apply etriple_ex; intros rho2. apply etriple_pure; intros HG2.
  destruct (Z_le_gt_dec 64 N) as [H64|HS].
  - exact (copen64_exists H64 rho2 HG2).
  - apply (copenS_exists (Z.to_nat (A1 mod 4)) (length argv1)); [apply Hchk; lia | reflexivity | lia | lia | exact HG2].
Qed.
End PerR.

(* The run's own flag: the cannot-open path from the open-error state of the launch's CONFIG_RSEQ. *)
Theorem copen_safe : checks_S -> forall rho : valuation, J25 sp mb draw inp rho ->
  triple segs ok (SP segs (Kx [] md0) (S_operr (kb_rseq (in_kernel inp))) rho) (fun _ : world => False).
Proof using Hargc Hent Hfds0 Hrdr0 Hfs Hinp HokK HokP Hokh.
  exact (copen_safe_r (kb_rseq (in_kernel inp)) eq_refl).
Qed.

Theorem copen_exists : checks_S -> forall rho : valuation, J25 sp mb draw inp rho ->
  etriple segs (SP segs (Kx [] md0) (S_operr (kb_rseq (in_kernel inp))) rho)
    (fun w : world => w_tr w = die fs (msg_cannot_open argv1)).
Proof using Hargc Hent Hfds0 Hrdr0 Hfs Hinp.
  exact (copen_exists_r (kb_rseq (in_kernel inp)) eq_refl).
Qed.

End Copen.
End Drv_copen.
