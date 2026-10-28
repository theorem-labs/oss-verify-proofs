(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "option"; "list"; "Some"; "nat"; "true"; "false"; "bool"; "prod"; "andb"; "None"; "app"; "fst"; "negb"; "snd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "mkCell"; "sv"; "sprop"; "SVar"; "SAlu"; "sobj"; "SPUle"; "sstate"; "mkObj"; "ss_next"; "DUnknown"; "SExt"; "DList"; "ss_facts"; "SPBranch"; "SPAlign"; "ss_objs"; "SPNot"; "DImage"; "SLBytes"; "SPUlt"; "reg_sv"; "mkSS"; "ob_cells"; "ob_hi"; "ob_lo"; "sprop_below"; "ob_dflt"; "ss_pc"; "SPEq"; "FcsrFrm0"; "DRom"; "ob_base"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "sv_eqb"; "dflt_writable"; "is_arr"; "ss_lenient"; "c_off"; "c_width"; "image_byte"; "obj_wf"; "ro_addr"; "sprop_eqb"; "swf"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_OR"; "ALU_SRL"; "BC_NE"; "ALU_SUB"; "instr"; "BC_EQ"; "BC_LTU"; "ALU_XOR"; "Ecall"; "ALU_AND"; "aluop"; "mulop"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "sym_run"; "RsEcall"; "RsCut"; "list_set"; "instr_at"; "lf_state"; "sv_equiv"; "RsFuel"; "set_objs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "XSplit"; "XMerge"; "XSelect"; "XRebase"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err.WLerrS"; "segs"; "D"; "Pre_wl2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G1.Drv_copen_states"; "FUEL"; "E_Wz"; "obj"; "app_objs"; "E_W2"; "E_fxA"; "T_cs"; "E_W1"; "E_W2r"; "E_W2r1"; "E_W1c"; "E_W2c"; "E_Wa_c"; "E_Wb"; "E_Wb_c"; "E_cs"; "s_w1"; "s_w2"; "s_wa"; "s_wb"; "E_Wa"; "E_csX"; "E_W1r"; "E_Wa_m"; "E_Wb_m"; "B544"; "E_W2c1"; "E_W2s"; "E_Wa_l1"; "E_Wa_x"; "E_Wb_x"; "S_co0"; "drop_last"; "lastobj"; "s_cs"; "E_W1x"; "E_Wa_m2"; "E_Wb_m1"; "E_fx0"; "E_fx2a"; "E_fx2b"; "LOnl"; "S_coR"; "T_D1i"; "T_D2i"; "T_imp"; "E_exa"; "E_exb"; "E_exit"; "O_emp"; "PZ"; "R_cs"; "R_w1"; "R_w2"; "R_wa"; "R_wb"; "S_co"; "T_D1"; "T_D2"; "E_W1l"; "E_Wa_l"; "E_Wa_m1"; "E_Wb_l"; "E_fx"; "T_Da"; "T_Db"; "E_W2c0"; "E_Wa1"; "E_Wa2"; "E_Wa_c0"; "E_Wb_c0"; "E_fxX"; "E_po2"; "E_po62"; "E_po63"; "LENa"; "O_str1"; "S_cow"; "T64"; "T_Dai"; "T_Dbi"; "Tsm"; "xs_d1"; "xs_d2"; "xs_post"; "BL_co"; "E_Wa_r"; "E_Wb_r"; "E_fxW"; "E_po"; "HInl"; "IOVa"; "IOVb"; "O_arg1"; "O_nl"; "O_nlr"; "R_gen"; "T_cs1"; "X_ovf"; "X_ovfS"; "nl_addr"; "F_co"; "F_n"; "check_pre"; "ozi"; "s_nr"; "xs_co"; "xs_fx"; "xs_po"; "xs_pre"; "xs_w1"; "xs_w2"; "xs_w2s"; "xs_wa1"; "xs_wa2"; "xs_wb1"; "xs_wb2"; "BLn"; "C0_nr"; "FUELm"; "MEMO_10"; "MEMO_18"; "MEMO_28"; "MEMO_29"; "MEMO_30"; "MEMO_33"; "MEMO_34"; "MEMO_35"; "MEMO_36"; "MEMO_47"; "MEMO_5"; "MEMO_56"; "MEMO_58"; "a70r"; "check_core"; "check_nr"; "diff_in_ok"; "diff_out_ok"; "ids_below71"; "po_fresh"; "po_regs"; "post_loc"; "pre_loc"; "setbase"; "sobj_eqb"; "the_pre"; "upd_cell"; "wpos_off"; "xs_c"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "infer_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get";
"sv_subst"; "wsub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "entails"; "cell_eqb"; "dummy_obj"; "odefault_eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_post"; "call_check"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G1.Drv_copen_states.CAddr"; "fwritex_entry"; "ret_out"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "existsb"; "In"; "fold_left"; "removelast"; "tl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "cells_bytes"; "BLit"; "BSrc"; "bexp_eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "list_eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue"; "merge_lists"; "reframe_obj"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.StrAddr"; "strnlen_entry"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_strnlen"; "Pre_strnlen"; "P_strnlen"; "Posts_strnlen"; "@Corelib.Lists.ListDef"; "map"; "nth"; "seq"; "firstn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "state_has_rl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast"; "apply_xforms_fast"; "@Stdlib.ZArith.BinInt.Z"; "of_nat"; "sub"; "to_nat"; "add"; "eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states"; "S_operr"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@Stdlib.PArith.BinPos.Pos"; "eqb"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memchr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_strnlen.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Drv_copen_states.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memchr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_strnlen OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err.
Import ListNotations.

Import StrAddr.
Import WLerrS.
Close Scope bv_scope.
Open Scope Z_scope.

Module CAddr.
  Definition fwritex_entry : Z := 0x225f4.
  Definition ret_out : Z := 0x2362c.
  Definition exit_ecall : Z := 0x20150.
  Definition stderr_file : Z := 0x29d90.
End CAddr.
Import CAddr.

Definition FUEL : nat := (8 * 1000)%nat.
Definition lf0 (S : sstate) (r : option (list leaf)) (i : nat) : sstate := ltac2:(tb__ "0|1|
S3S4S56A1M0A1S1aLr;Vr;G0S5dS124S56Vi;R1S57VS;S5fA2A4A1Lls;VS;X3x2").
Definition xget (S : sstate) (r : option sstate) : sstate := match r with Some X => X | None => S end.
Definition drop_last (S : sstate) : sstate := ltac2:(tb__ "0|0|
S29S2fVS;A1S36VS;A1S35VS;A1S34VS;A1S37VS;A1S112S18S23VS;A1A2S20VS;A1S1cVS;A1S3bVS;A1A9").
Definition app_objs (S : sstate) (os : list sobj) (nx : positive) : sstate := ltac2:(tb__ "0|0|
S29S2fVS;A1S36VS;A1S35VS;A1S34VS;A1S37VS;A1SdS18S23VS;A1Vos;A3S20VS;A1Vnx;S3bVS;A1A9").
Definition obj (S : sstate) (i : nat) : sobj := ltac2:(tb__ "0|0|
S124S18Vi;S23VS;A1S107A4").
Definition lastobj (S : sstate) : sobj := last (ss_objs S) dummy_obj.

Definition F_co : list sprop := ltac2:(tb__ "0|2|
S0S15S19S17S48S16P1cA1M0S11Z11A1A3S16P1bA1M1A2S0S15S19G1S11Z400000A1A2S0S15S19G0S11Z1ffffA1A2S0S15S19S17S48S16P19A1G0A3S11Z7fffffffffefA1A2S2S15A1A3A3A3A3").
Definition O_str1 : sobj := ltac2:(tb__ "0|0|
S1bS16P19A1S11Z0A1S16P1bA1S2S12A1S1fP3A1A5").

Definition xs_co : list xform := ltac2:(tb__ "0|0|
S0S61S65S0S6U0S0S6U1S0S6U2S0S6U3S0S6U4S0S6U6S0S6U7S0S6U5S2S6A1A3A3A3A3A3A3A3A3A1S2S61A1A3").
Local Definition MEMO_1 := apply_xforms S_operr xs_co.
Local Definition MEMO_1__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast S_operr xs_co.
Definition S_co0 : sstate := ltac:(let x := eval vm_compute in (xget S_operr (MEMO_1__f)) in exact x).
Local Lemma MEMO_1_c : MEMO_1 = Some S_co0. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_1 MEMO_1__f. Qed.
Local Lemma MEMO_1_e : ltac2:(tb__ "0|0|
S46S3S1aA1S62S130Sd4A2S5S1aS89A2A3").
Proof. exact (@eq_trans _ (apply_xforms S_operr xs_co) MEMO_1 (Some S_co0) (@eq_refl _ (apply_xforms S_operr xs_co)) MEMO_1_c). Qed.
Lemma xs_co_ok : ltac2:(tb__ "0|0|
S46S3S1aA1S62S130Sd4A2S5S1aS89A2A3"). Proof. exact MEMO_1_e. Qed.

Local Definition MEMO_2 := drop_last S_co0.
Definition S_coR : sstate := ltac:(let x := eval vm_compute in (MEMO_2) in exact x).
Local Lemma MEMO_2_c : MEMO_2 = S_coR. Proof. vm_cast_no_check (@eq_refl _ MEMO_2). Qed.
Local Lemma MEMO_2_e : ltac2:(tb__ "0|0|
S46S1aS8aS89A1S94A3").
Proof. exact (@eq_trans _ (drop_last S_co0) MEMO_2 (S_coR) (@eq_refl _ (drop_last S_co0)) MEMO_2_c). Qed.
Lemma S_coR_eq : ltac2:(tb__ "0|0|
S46S1aS8aS89A1S94A3"). Proof. exact MEMO_2_e. Qed.
Lemma S_co0_objs : ltac2:(tb__ "0|0|
S46S4S18A1S23S89A1SdS18S23S94A1S0S18S8bS89A1S2S18A1A3A3A3"). Proof. reflexivity. Qed.
Lemma swf_S_coR : swf S_coR = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Lemma last_co0 : ltac2:(tb__ "0|2|
S46S18S8bS89A1S1bS16P6A1S11Z0A1M0S11Z10A1S0S12S13G0Z8M1S16P9A1A3S0S12S13S11G1A1G1S16PaA1A3S2S12A1A3A3S1dA5A3"). Proof. reflexivity. Qed.
Lemma S_coR_next : ltac2:(tb__ "0|1|
S47S46S43S1cS94A1P1bM0A3S46S43S1cS89A1G0A3A2"). Proof. split; reflexivity. Qed.

Local Definition MEMO_3 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S6dS94S0S18Sb6S2S18A1A3P1dA3").
Definition S_cow : sstate := ltac:(let x := eval vm_compute in (MEMO_3) in exact x).
Local Lemma MEMO_3_c : MEMO_3 = S_cow. Proof. vm_cast_no_check (@eq_refl _ MEMO_3). Qed.
Local Lemma MEMO_3_e : ltac2:(tb__ "0|0|
S46S1aS6dS94S0S18Sb6S2S18A1A3P1dA3Sb7A3").
Proof. exact (@eq_trans _ (app_objs S_coR [O_str1] 29) MEMO_3 (S_cow) (@eq_refl _ (app_objs S_coR [O_str1] 29)) MEMO_3_c). Qed.
Lemma S_cow_eq : ltac2:(tb__ "0|0|
S46S1aS6dS94S0S18Sb6S2S18A1A3P1dA3Sb7A3"). Proof. exact MEMO_3_e. Qed.
Lemma swf_S_cow : swf S_cow = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma norl3_S_coR : state_has_rl 3 S_coR = false. Proof. vm_cast_no_check (@eq_refl _ false). Qed.
Local Definition MEMO_4 := add_facts F_co S_cow.
Definition S_co : sstate := ltac:(let x := eval vm_compute in (MEMO_4) in exact x).
Local Lemma MEMO_4_c : MEMO_4 = S_co. Proof. vm_cast_no_check (@eq_refl _ MEMO_4). Qed.
Local Lemma MEMO_4_e : ltac2:(tb__ "0|0|
S46S1aSffScfSb7A2Sa2A3").
Proof. exact (@eq_trans _ (add_facts F_co S_cow) MEMO_4 (S_co) (@eq_refl _ (add_facts F_co S_cow)) MEMO_4_c). Qed.
Lemma S_co_eq : ltac2:(tb__ "0|0|
S46S1aSffScfSb7A2Sa2A3"). Proof. exact MEMO_4_e. Qed.

Local Definition MEMO_5 : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S58S67S6aS0S44S11fS2S44A1A3Sa2S7A5").
Local Definition MEMO_5__f : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S119S67S6aS0S44S11fS2S44A1A3Sa2S7A5").
Definition E_cs : sstate := ltac:(let x := eval vm_compute in (lf0 S_co (MEMO_5__f) 0) in exact x).
Local Lemma MEMO_5_c : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1SecS5G0S0S56S57S79S5aA2S2S56A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_5 MEMO_5__f. Qed.
Local Lemma MEMO_5_e : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS0S44S11fS2S44A1A3Sa2S7A5S5G0S0S56S57S79S5aA2S2S56A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [strnlen_entry] S_co true) MEMO_5 (Some [mkLeaf E_cs RsCut]) (@eq_refl _ (sym_run segs FUEL [strnlen_entry] S_co true)) MEMO_5_c). Qed.
Lemma run_co : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS0S44S11fS2S44A1A3Sa2S7A5S5G0S0S56S57S79S5aA2S2S56A1A3A2A3").
Proof. exact MEMO_5_e. Qed.

Definition xs_pre : list xform := ltac2:(tb__ "0|1|
S0S61S63U0M0S11N460A1A2S0S61S63G0S11N480A1A2S2S61A1A3A3").
Local Definition MEMO_6 := apply_xforms E_cs xs_pre.
Local Definition MEMO_6__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_cs xs_pre.
Definition E_csX : sstate := ltac:(let x := eval vm_compute in (xget E_cs (MEMO_6__f)) in exact x).
Local Lemma MEMO_6_c : MEMO_6 = Some E_csX. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_6 MEMO_6__f. Qed.
Local Lemma MEMO_6_e : ltac2:(tb__ "0|0|
S46S3S1aA1S62S79Sd7A2S5S1aS7fA2A3").
Proof. exact (@eq_trans _ (apply_xforms E_cs xs_pre) MEMO_6 (Some E_csX) (@eq_refl _ (apply_xforms E_cs xs_pre)) MEMO_6_c). Qed.
Lemma xs_pre_ok : ltac2:(tb__ "0|0|
S46S3S1aA1S62S79Sd7A2S5S1aS7fA2A3"). Proof. exact MEMO_6_e. Qed.
Definition s_cs : wsub := ltac:(let x := eval vm_compute in ((16%positive, SVar 28) :: (17%positive, SVar 27) :: infer_sub 10 E_csX Pre_strnlen) in exact x).
Local Definition MEMO_7 : ltac2:(tb__ "0|0|
S3S4S18A1A1") := ltac2:(tb__ "0|0|
S104S7fS120S8cA3").
Definition R_cs : list sobj := ltac:(let x := eval vm_compute in (match MEMO_7 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_7_c : MEMO_7 = Some R_cs. Proof. vm_cast_no_check (@eq_refl _ MEMO_7). Qed.
Local Lemma MEMO_7_e : ltac2:(tb__ "0|1|
S46S3S4S18A1M0A1S104S7fS120S8cA3S5G0S9dA2A3").
Proof. exact (@eq_trans _ (entails_fr E_csX Pre_strnlen s_cs) MEMO_7 (Some R_cs) (@eq_refl _ (entails_fr E_csX Pre_strnlen s_cs)) MEMO_7_c). Qed.
Lemma efr_cs : ltac2:(tb__ "0|1|
S46S3S4S18A1M0A1S104S7fS120S8cA3S5G0S9dA2A3"). Proof. exact MEMO_7_e. Qed.
Lemma chk_cs : ltac2:(tb__ "0|0|
S46S9S10aS7fS120S8cS9dS122A5S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_cs : ltac2:(tb__ "0|0|
S46S9S10dS15S2dS1cS7fA1A1S20S79A1A3S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_cs_16 : ltac2:(tb__ "0|0|
S46S14S101S8cP10A2S16P1cA1A3"). Proof. reflexivity. Qed.
Local Definition MEMO_8 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S109S8cS129S121S1cS7fA1S9dA5").
Definition T_imp : sstate := ltac:(let x := eval vm_compute in (MEMO_8) in exact x).
Local Lemma MEMO_8_c : MEMO_8 = T_imp. Proof. vm_cast_no_check (@eq_refl _ MEMO_8). Qed.
Local Lemma MEMO_8_e : ltac2:(tb__ "0|0|
S46S1aS109S8cS129S121S1cS7fA1S9dA5S97A3").
Proof. exact (@eq_trans _ (import_post s_cs NF P_strnlen (ss_next E_csX) R_cs) MEMO_8 (T_imp) (@eq_refl _ (import_post s_cs NF P_strnlen (ss_next E_csX) R_cs)) MEMO_8_c). Qed.
Lemma T_imp_eq : ltac2:(tb__ "0|0|
S46S1aS109S8cS129S121S1cS7fA1S9dA5S97A3"). Proof. exact MEMO_8_e. Qed.
Definition xs_post : list xform := ltac2:(tb__ "0|3|
S0S61S66U1M0A1S0S61S65S0S6U2S0S6G0S0S6U3S0S6U4S0S6U5S0S6U6S0S6U7S0S6U8S0S6U9S0S6U0M1S2S6A1A3A3A3A3A3A3A3A3A3A3A1S0S61S64G1A1M2S0S61G2S2S61A1A3A3A3A3").
Local Definition MEMO_9 : ltac2:(tb__ "0|0|
S3S1aA1") := ltac2:(tb__ "0|0|
S62SffS20S79A1S97A2SbeA2").
Local Definition MEMO_9__f : ltac2:(tb__ "0|0|
S3S1aA1") := ltac2:(tb__ "0|0|
S12aSffS20S79A1S97A2SbeA2").
Definition T_cs : sstate := ltac:(let x := eval vm_compute in (xget E_cs (MEMO_9__f)) in exact x).
Local Lemma MEMO_9_c : MEMO_9 = Some T_cs. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_9 MEMO_9__f. Qed.
Local Lemma MEMO_9_e : ltac2:(tb__ "0|0|
S46S3S1aA1S62SffS20S79A1S97A2SbeA2S5S1aS70A2A3").
Proof. exact (@eq_trans _ (apply_xforms (add_facts (ss_facts E_cs) T_imp) xs_post) MEMO_9 (Some T_cs) (@eq_refl _ (apply_xforms (add_facts (ss_facts E_cs) T_imp) xs_post)) MEMO_9_c). Qed.
Lemma xs_post_ok : ltac2:(tb__ "0|0|
S46S3S1aA1S62SffS20S79A1S97A2SbeA2S5S1aS70A2A3"). Proof. exact MEMO_9_e. Qed.
Lemma fb_cs2 : ltac2:(tb__ "0|0|
S46S9S10dS15S2dS1cS97A1A1S20S79A1A3S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Definition T_cs1 : sstate := ltac2:(tb__ "0|0|
S29S2fS70A1S5bS14S36S70A1UaS16P1cA1A4S35S70A1S34S70A1S37S70A1S23S70A1S20S70A1S1cS70A1S3bS70A1A9").
Lemma fact_T_cs : ltac2:(tb__ "0|0|
S110S15S30S16P45A1S16P1cA1A2S20S70A1A3"). Proof. cbn. tauto. Qed.
Lemma diff_cs : ltac2:(tb__ "0|4|
S46S3SaS4SaS14S14A2M0A1M1S4S15A1M2A2M3A1S11bS70ScbA2S5G3S1G1G2S0G0S1S14S14S16P45A1S16P1cA1A4S2G0A1A3S2S15A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SVar 69, SVar 28)], @nil sprop))). Qed.
Lemma swf_T_cs1 : swf T_cs1 = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma T_cs1_next : ss_next T_cs1 = 70%positive. Proof. reflexivity. Qed.

Definition T64 : sstate := ltac2:(tb__ "0|0|
SffS0S15S19S11Z40A1S16P1cA1A2S2S15A1A3ScbA2").
Local Definition MEMO_10 : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S58S67S6aS2S44A1Sb8S7A5").
Local Definition MEMO_10__f : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S119S67S6aS2S44A1Sb8S7A5").
Definition X_ovf : sstate := ltac:(let x := eval vm_compute in (lf0 T64 (MEMO_10__f) 0) in exact x).
Definition E_W1 : sstate := ltac:(let x := eval vm_compute in (lf0 T64 (MEMO_10__f) 1) in exact x).
Local Lemma MEMO_10_c : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1Se2S5G0S0S56S57SccS59A2S0S56S57S71S59A2S2S56A1A3A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_10 MEMO_10__f. Qed.
Local Lemma MEMO_10_e : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS2S44A1Sb8S7A5S5G0S0S56S57SccS59A2S0S56S57S71S59A2S2S56A1A3A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T64 true) MEMO_10 (Some [mkLeaf X_ovf RsEcall; mkLeaf E_W1 RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T64 true)) MEMO_10_c). Qed.
Lemma run_64 : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS2S44A1Sb8S7A5S5G0S0S56S57SccS59A2S0S56S57S71S59A2S2S56A1A3A3A2A3").
Proof. exact MEMO_10_e. Qed.

Definition BNZ28 : sprop := ltac2:(tb__ "0|0|
S21S4cS1eS8Q8S26P3S16P1cA1Z1A3A3S11Z0A1A3").
Lemma fact_ovf : In BNZ28 (ss_facts X_ovf). Proof. cbn. tauto. Qed.
Lemma E_W1_next : ss_next E_W1 = 70%positive. Proof. reflexivity. Qed.

Definition xs_w1 : list xform := ltac2:(tb__ "0|2|
S0S61S63U0M0S11N21fA1A2S0S61S63G0S11N230A1A2S0S61S63G0S11N4a8A1A2S0S61S63G0S11N4c8A1A2S0S61S63U9M1S11Z29e0cA1A2S0S61S63G1S11Z29e08A1A2S2S61A1A3A3A3A3A3A3").
Local Definition MEMO_11 := apply_xforms E_W1 xs_w1.
Local Definition MEMO_11__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_W1 xs_w1.
Definition E_W1x : sstate := ltac:(let x := eval vm_compute in (xget E_W1 (MEMO_11__f)) in exact x).
Local Lemma MEMO_11_c : MEMO_11 = Some E_W1x. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_11 MEMO_11__f. Qed.
Local Lemma MEMO_11_e : ltac2:(tb__ "0|0|
S46S3S1aA1S62S71Sd8A2S5S1aS8dA2A3").
Proof. exact (@eq_trans _ (apply_xforms E_W1 xs_w1) MEMO_11 (Some E_W1x) (@eq_refl _ (apply_xforms E_W1 xs_w1)) MEMO_11_c). Qed.
Lemma xs_w1_ok : ltac2:(tb__ "0|0|
S46S3S1aA1S62S71Sd8A2S5S1aS8dA2A3"). Proof. exact MEMO_11_e. Qed.

Definition BL_co : list bexp := ltac2:(tb__ "0|4|
S123S44S114S116S0S44Z63M0S0S44Z6cS0S44Z69S0S44Z3aS0S44Z20M1S0S44G0S0S44Z61S0S44Z6eM2S0S44G2S0S44Z6fM3S0S44Z74S0S44G1S0S44G3S0S44Z70S0S44Z65S0S44G2S0S44G1S2S44A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A4").
Lemma cb_w1 : ltac2:(tb__ "0|1|
S46S3S4S114A1M0A1S115S2aS6cS8dU3A2A1S11N230A1Z0U11A4S5G0SbfA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some BL_co)). Qed.
Lemma obj3_w1 : ltac2:(tb__ "0|3|
S47S46S3S18A1S10eS18S23S8dA1U3M0A3S5S18S6cS8dG0A2M1A2A3S47S46S14S2cG1A1S11N230A1A3S47S46S14S2bG1A1S11N21fA1A3S47S46S9S39S2eG1A1M2A1S7A3S46S9S3aG2A1S8A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma norl5_w1 : state_has_rl 5 E_W1x = false. Proof. vm_cast_no_check (@eq_refl _ false). Qed.
Local Definition MEMO_12 := obj_to_list E_W1x 3 5.
Definition E_W1l : sstate := ltac:(let x := eval vm_compute in (MEMO_12) in exact x).
Local Lemma MEMO_12_c : MEMO_12 = E_W1l. Proof. vm_cast_no_check (@eq_refl _ MEMO_12). Qed.
Local Lemma MEMO_12_e : ltac2:(tb__ "0|0|
S46S1aS11aS8dU3P5A3Sa5A3").
Proof. exact (@eq_trans _ (obj_to_list E_W1x 3 5) MEMO_12 (E_W1l) (@eq_refl _ (obj_to_list E_W1x 3 5)) MEMO_12_c). Qed.
Lemma E_W1l_eq : ltac2:(tb__ "0|0|
S46S1aS11aS8dU3P5A3Sa5A3"). Proof. exact MEMO_12_e. Qed.

Local Definition MEMO_13 := drop_last E_W1l.
Definition E_W1r : sstate := ltac:(let x := eval vm_compute in (MEMO_13) in exact x).
Local Lemma MEMO_13_c : MEMO_13 = E_W1r. Proof. vm_cast_no_check (@eq_refl _ MEMO_13). Qed.
Local Lemma MEMO_13_e : ltac2:(tb__ "0|0|
S46S1aS8aSa5A1S80A3").
Proof. exact (@eq_trans _ (drop_last E_W1l) MEMO_13 (E_W1r) (@eq_refl _ (drop_last E_W1l)) MEMO_13_c). Qed.
Lemma E_W1r_eq : ltac2:(tb__ "0|0|
S46S1aS8aSa5A1S80A3"). Proof. exact MEMO_13_e. Qed.
Lemma E_W1l_objs : ltac2:(tb__ "0|0|
S46S4S18A1S23Sa5A1SdS18S23S80A1S0S18Sb6S2S18A1A3A3A3"). Proof. reflexivity. Qed.
Lemma swf_E_W1r : swf E_W1r = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma norl6_w1 : state_has_rl 6 E_W1r = false. Proof. vm_cast_no_check (@eq_refl _ false). Qed.
Definition O_arg1 : sobj := ltac2:(tb__ "0|0|
S1bS16P19A1S11Z0A1S16P1cA1S2S12A1S32P6A1A5").
Local Definition MEMO_14 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S6dS80S0S18Sc7S2S18A1A3S1cS80A1A3").
Definition E_W1c : sstate := ltac:(let x := eval vm_compute in (MEMO_14) in exact x).
Local Lemma MEMO_14_c : MEMO_14 = E_W1c. Proof. vm_cast_no_check (@eq_refl _ MEMO_14). Qed.
Local Lemma MEMO_14_e : ltac2:(tb__ "0|0|
S46S1aS6dS80S0S18Sc7S2S18A1A3S1cS80A1A3S74A3").
Proof. exact (@eq_trans _ (app_objs E_W1r [O_arg1] (ss_next E_W1r)) MEMO_14 (E_W1c) (@eq_refl _ (app_objs E_W1r [O_arg1] (ss_next E_W1r))) MEMO_14_c). Qed.
Lemma E_W1c_eq : ltac2:(tb__ "0|0|
S46S1aS6dS80S0S18Sc7S2S18A1A3S1cS80A1A3S74A3"). Proof. exact MEMO_14_e. Qed.
Lemma swf_E_W1c : swf E_W1c = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Definition s_w1 : wsub := ltac2:(tb__ "0|f|
S0SaS43S14A2M0S1S43S14PcM1S17S48S16P1A1M2S11N230A1A3M3A4S0G0S1S43S14PdM4S11Z11A1A4S0G0S1S43S14PeM5S16P19M6A1M7A4S0G0S1S43S14PfS16P1cA1M8A4M9S0G0S1S43S14G5G2A4S0G0S1S43S14G1G2A4S0G0S1S43S14G4G8A4S0G0S1S43S14P5bS11Z0A1MaA4S0G0S1S43S14P5aGaA4S0G0S1S43S14P59GaA4S0G0S1S43S14P58GaA4S0G0S1S43S14P57GaA4S0G0S1S43S14P56GaA4S0G0S1S43S14P55GaA4S0G0S1S43S14P54GaA4S0G0S1S43S14P53GaA4S0G0S1S43S14P52GaA4S0G0S1S43S14P51GaA4S0G0S1S43S14P50GaA4S0G0S1S43S14P4fGaA4S0G0S1S43S14P4eGaA4S0G0S1S43S14P4dGaA4S0G0S1S43S14P4cGaA4S0G0S1S43S14P4bGaA4S0G0S1S43S14P4aGaA4S0G0S1S43S14P49GaA4S0G0S1S43S14P48GaA4S0G0S1S43S14P47GaA4S0G0S1S43S14P46GaA4S0G0S1S43S14P45GaA4S0G0S1S43S14P44GaA4S0G0S1S43S14P43GaA4S0G0S1S43S14P42GaA4S0G0S1S43S14P41GaA4S0G0S1S43S14P40GaA4S0G0S1S43S14P3fGaA4S0G0S1S43S14P3eGaA4S0G0S1S43S14P3dGaA4S0G0S1S43S14P3cMbGaA4S0G0S1S43S14P33S16GbA1A4S0G0S1S43S14P32S16P3bA1A4S0G0S1S43S14P31S16P3aA1A4S0G0S1S43S14P30S16P39A1A4S0G0S1S43S14P2fG8A4S0G0S1S43S14P2eG8A4S0G0S1S43S14P2dMcG8A4S0G0S1S43S14P2cGaA4S0G0S1S43S14P2bG7A4S0G0S1S43S14P29S11Z5a338A1A4S0G0S1S43S14P28S11Z29d90A1A4S0G0S1S43S14P24MdS16GcA1A4S0G0S1S43S14P23S11Z1A1A4S0G0S1S43S14P22MeGaA4S0G0S1S43S14P21S17S51S17S48G2S11N21fA1A3G3A3A4S0G0G9S0G0S1S43S14P1bS16GdA1A4S0G0S1S43S14P1aS11Z22224A1A4S0G0S1S43S14G6S16GeA1A4S0G0S1S43S14P18S11Z3a0d0A1A4S0G0S1S43S14PaS17S48G2S11N4d0A1A3A4S0G0S1S43S14P15S11Z2362cA1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Local Definition MEMO_15 : ltac2:(tb__ "0|0|
S3S4S18A1A1") := ltac2:(tb__ "0|0|
S104S74S69S7aA3").
Definition R_w1 : list sobj := ltac:(let x := eval vm_compute in (match MEMO_15 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_15_c : MEMO_15 = Some R_w1. Proof. vm_cast_no_check (@eq_refl _ MEMO_15). Qed.
Local Lemma MEMO_15_e : ltac2:(tb__ "0|1|
S46S3S4S18A1M0A1S104S74S69S7aA3S5G0S9eA2A3").
Proof. exact (@eq_trans _ (entails_fr E_W1c Pre_wl2 s_w1) MEMO_15 (Some R_w1) (@eq_refl _ (entails_fr E_W1c Pre_wl2 s_w1)) MEMO_15_c). Qed.
Lemma efr_w1 : ltac2:(tb__ "0|1|
S46S3S4S18A1M0A1S104S74S69S7aA3S5G0S9eA2A3"). Proof. exact MEMO_15_e. Qed.
Lemma chk_w1 : ltac2:(tb__ "0|0|
S46S9S10aS74S69S7aS9eS0S56S57S68S5aA2S2S56A1A3A5S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_w1 : ltac2:(tb__ "0|0|
S46S9S10dS15S2dS1cS74A1A1S20S71A1A3S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma facts_w1c : ltac2:(tb__ "0|0|
S46S4S15A1S20S74A1S20S71A1A3"). Proof. reflexivity. Qed.
Lemma s_w1_vals : ltac2:(tb__ "0|0|
S47S46S14S101S7aPcA2S17S48S16P1A1S11N230A1A3A3S47S46S14S101S7aPdA2S11Z11A1A3S47S46S14S101S7aPeA2S16P19A1A3S46S14S101S7aPfA2S16P1cA1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_16 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S109S7aP5cS68S1cS74A1S9eA5").
Definition T_D1i : sstate := ltac:(let x := eval vm_compute in (MEMO_16) in exact x).
Local Lemma MEMO_16_c : MEMO_16 = T_D1i. Proof. vm_cast_no_check (@eq_refl _ MEMO_16). Qed.
Local Lemma MEMO_16_e : ltac2:(tb__ "0|0|
S46S1aS109S7aP5cS68S1cS74A1S9eA5S95A3").
Proof. exact (@eq_trans _ (import_post s_w1 92 D (ss_next E_W1c) R_w1) MEMO_16 (T_D1i) (@eq_refl _ (import_post s_w1 92 D (ss_next E_W1c) R_w1)) MEMO_16_c). Qed.
Lemma T_D1i_eq : ltac2:(tb__ "0|0|
S46S1aS109S7aP5cS68S1cS74A1S9eA5S95A3"). Proof. exact MEMO_16_e. Qed.
Definition xs_d1 : list xform := ltac2:(tb__ "0|4|
S0S61S66U0M0A1S0S61S65S0S6U4S0S6G0S0S6U5S0S6U1S0S6U6S0S6U7M1S0S6U8S0S6U9S0S6UaS0S6UbS0S6U3S0S6UcS0S6UdS0S6U2S2S6A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S61S64G0A1M2S0S61G2S0S61S64G1A1M3S0S61G3S2S61A1A3A3A3A3A3A3").
Local Definition MEMO_17 : ltac2:(tb__ "0|0|
S3S1aA1") := ltac2:(tb__ "0|0|
S62SffS20S71A1S95A2SbcA2").
Local Definition MEMO_17__f : ltac2:(tb__ "0|0|
S3S1aA1") := ltac2:(tb__ "0|0|
S12aSffS20S71A1S95A2SbcA2").
Definition T_D1 : sstate := ltac:(let x := eval vm_compute in (xget T_D1i (MEMO_17__f)) in exact x).
Local Lemma MEMO_17_c : MEMO_17 = Some T_D1. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_17 MEMO_17__f. Qed.
Local Lemma MEMO_17_e : ltac2:(tb__ "0|0|
S46S3S1aA1S62SffS20S71A1S95A2SbcA2S5S1aSa3A2A3").
Proof. exact (@eq_trans _ (apply_xforms (add_facts (ss_facts E_W1) T_D1i) xs_d1) MEMO_17 (Some T_D1) (@eq_refl _ (apply_xforms (add_facts (ss_facts E_W1) T_D1i) xs_d1)) MEMO_17_c). Qed.
Lemma xs_d1_ok : ltac2:(tb__ "0|0|
S46S3S1aA1S62SffS20S71A1S95A2SbcA2S5S1aSa3A2A3"). Proof. exact MEMO_17_e. Qed.
Lemma fb_d1 : ltac2:(tb__ "0|0|
S46S9S10dS15S2dS1cS95A1A1S20S71A1A3S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Local Definition MEMO_18 : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S58S67S6aS2S44A1Sa3S7A5").
Local Definition MEMO_18__f : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S119S67S6aS2S44A1Sa3S7A5").
Definition E_W2 : sstate := ltac:(let x := eval vm_compute in (lf0 T_D1 (MEMO_18__f) 0) in exact x).
Local Lemma MEMO_18_c : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1Se3S5G0S0S56S57S6eS59A2S2S56A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_18 MEMO_18__f. Qed.
Local Lemma MEMO_18_e : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS2S44A1Sa3S7A5S5G0S0S56S57S6eS59A2S2S56A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T_D1 true) MEMO_18 (Some [mkLeaf E_W2 RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T_D1 true)) MEMO_18_c). Qed.
Lemma run_d1 : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS2S44A1Sa3S7A5S5G0S0S56S57S6eS59A2S2S56A1A3A2A3").
Proof. exact MEMO_18_e. Qed.

Definition xs_w2s : list xform := ltac2:(tb__ "0|0|
S0S61S65S0S6U0S0S6U2S0S6U3S0S6U4S0S6U5S0S6U6S0S6U7S0S6U8S0S6U1S0S6U9S2S6A1A3A3A3A3A3A3A3A3A3A3A1S2S61A1A3").
Local Definition MEMO_19 := apply_xforms E_W2 xs_w2s.
Local Definition MEMO_19__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_W2 xs_w2s.
Definition E_W2s : sstate := ltac:(let x := eval vm_compute in (xget E_W2 (MEMO_19__f)) in exact x).
Local Lemma MEMO_19_c : MEMO_19 = Some E_W2s. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_19 MEMO_19__f. Qed.
Local Lemma MEMO_19_e : ltac2:(tb__ "0|0|
S46S3S1aA1S62S6eSdaA2S5S1aS85A2A3").
Proof. exact (@eq_trans _ (apply_xforms E_W2 xs_w2s) MEMO_19 (Some E_W2s) (@eq_refl _ (apply_xforms E_W2 xs_w2s)) MEMO_19_c). Qed.
Lemma xs_w2s_ok : ltac2:(tb__ "0|0|
S46S3S1aA1S62S6eSdaA2S5S1aS85A2A3"). Proof. exact MEMO_19_e. Qed.
Local Definition MEMO_20 := drop_last E_W2s.
Definition E_W2r1 : sstate := ltac:(let x := eval vm_compute in (MEMO_20) in exact x).
Local Lemma MEMO_20_c : MEMO_20 = E_W2r1. Proof. vm_cast_no_check (@eq_refl _ MEMO_20). Qed.
Local Lemma MEMO_20_e : ltac2:(tb__ "0|0|
S46S1aS8aS85A1S73A3").
Proof. exact (@eq_trans _ (drop_last E_W2s) MEMO_20 (E_W2r1) (@eq_refl _ (drop_last E_W2s)) MEMO_20_c). Qed.
Lemma E_W2r1_eq : ltac2:(tb__ "0|0|
S46S1aS8aS85A1S73A3"). Proof. exact MEMO_20_e. Qed.
Lemma E_W2s_objs : ltac2:(tb__ "0|0|
S46S4S18A1S23S85A1SdS18S23S73A1S0S18S8bS85A1S2S18A1A3A3A3"). Proof. reflexivity. Qed.
Lemma swf_E_W2r1 : swf E_W2r1 = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Local Definition MEMO_21 := drop_last E_W2r1.
Definition E_W2r : sstate := ltac:(let x := eval vm_compute in (MEMO_21) in exact x).
Local Lemma MEMO_21_c : MEMO_21 = E_W2r. Proof. vm_cast_no_check (@eq_refl _ MEMO_21). Qed.
Local Lemma MEMO_21_e : ltac2:(tb__ "0|0|
S46S1aS8aS73A1S72A3").
Proof. exact (@eq_trans _ (drop_last E_W2r1) MEMO_21 (E_W2r) (@eq_refl _ (drop_last E_W2r1)) MEMO_21_c). Qed.
Lemma E_W2r_eq : ltac2:(tb__ "0|0|
S46S1aS8aS73A1S72A3"). Proof. exact MEMO_21_e. Qed.
Lemma E_W2r1_objs : ltac2:(tb__ "0|0|
S46S4S18A1S23S73A1SdS18S23S72A1S0S18S8bS73A1S2S18A1A3A3A3"). Proof. reflexivity. Qed.
Lemma swf_E_W2r : swf E_W2r = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma norl_w2 : ltac2:(tb__ "0|0|
S47S46S9S128P5S72A2S8A3S46S9S128P6S72A2S8A3A2"). Proof. split; vm_cast_no_check (@eq_refl _ false). Qed.

Lemma last_w2s : ltac2:(tb__ "0|0|
S46S18S8bS85A1S1bS16P19A1S11Z0A1S16P1cA1S2S12A1S32P6A1A5A3"). Proof. reflexivity. Qed.
Lemma last_w2r1 : ltac2:(tb__ "0|1|
S46S18S8bS73A1S1bS17S48S16P1A1S11N230A1A3S11Z0A1M0S11Z11A1S0S12S13G0Z1S11ZaA1A3S2S12A1A3S1fP5A1A5A3"). Proof. reflexivity. Qed.
Lemma cb_w2 : ltac2:(tb__ "0|2|
S46S3S4S114A1M0A1S115S2aS8bS73A1A1S11Z0M1A1G1U1A4S5G0S0S114S116ZaA1S2S114A1A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some [BLit 10])). Qed.
Lemma wf_w2r1 : ltac2:(tb__ "0|0|
S46S9S3fS1cS73A1S8bS73A1A2S7A3"). Proof. reflexivity. Qed.
Lemma E_W2_next : ltac2:(tb__ "0|1|
S47S46S43S1cS6eA1S1cS72A1M0A3S47S46S43S1cS85A1G0A3S46S43S1cS73A1G0A3A2A2"). Proof. repeat split; reflexivity. Qed.
Definition O_nl : sobj := ltac2:(tb__ "0|0|
S1bS17S48S16P1A1S11N230A1A3S11Z0A1S11Z1A1S2S12A1S1fP5A1A5").
Definition O_emp : sobj := ltac2:(tb__ "0|1|
S1bS11Z0A1M0G0G0S2S12A1S32P6A1A5").
Local Definition MEMO_22 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S6dS72S0S18Sc8S2S18A1A3S1cS72A1A3").
Definition E_W2c1 : sstate := ltac:(let x := eval vm_compute in (MEMO_22) in exact x).
Local Lemma MEMO_22_c : MEMO_22 = E_W2c1. Proof. vm_cast_no_check (@eq_refl _ MEMO_22). Qed.
Local Lemma MEMO_22_e : ltac2:(tb__ "0|0|
S46S1aS6dS72S0S18Sc8S2S18A1A3S1cS72A1A3S84A3").
Proof. exact (@eq_trans _ (app_objs E_W2r [O_nl] (ss_next E_W2r)) MEMO_22 (E_W2c1) (@eq_refl _ (app_objs E_W2r [O_nl] (ss_next E_W2r))) MEMO_22_c). Qed.
Lemma E_W2c1_eq : ltac2:(tb__ "0|0|
S46S1aS6dS72S0S18Sc8S2S18A1A3S1cS72A1A3S84A3"). Proof. exact MEMO_22_e. Qed.
Lemma swf_E_W2c1 : swf E_W2c1 = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Local Definition MEMO_23 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S6dS84S0S18S9bS2S18A1A3S1cS84A1A3").
Definition E_W2c0 : sstate := ltac:(let x := eval vm_compute in (MEMO_23) in exact x).
Local Lemma MEMO_23_c : MEMO_23 = E_W2c0. Proof. vm_cast_no_check (@eq_refl _ MEMO_23). Qed.
Local Lemma MEMO_23_e : ltac2:(tb__ "0|0|
S46S1aS6dS84S0S18S9bS2S18A1A3S1cS84A1A3SacA3").
Proof. exact (@eq_trans _ (app_objs E_W2c1 [O_emp] (ss_next E_W2c1)) MEMO_23 (E_W2c0) (@eq_refl _ (app_objs E_W2c1 [O_emp] (ss_next E_W2c1))) MEMO_23_c). Qed.
Lemma E_W2c0_eq : ltac2:(tb__ "0|0|
S46S1aS6dS84S0S18S9bS2S18A1A3S1cS84A1A3SacA3"). Proof. exact MEMO_23_e. Qed.
Lemma swf_E_W2c0 : swf E_W2c0 = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Definition xs_w2 : list xform := ltac2:(tb__ "0|2|
S0S61S63U0M0S11N288A1A2S0S61S63G0S11N2a8A1A2S0S61S63U8M1S11Z29e0cA1A2S0S61S63G1S11Z29e08A1A2S2S61A1A3A3A3A3").
Local Definition MEMO_24 := apply_xforms E_W2c0 xs_w2.
Local Definition MEMO_24__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_W2c0 xs_w2.
Definition E_W2c : sstate := ltac:(let x := eval vm_compute in (xget E_W2c0 (MEMO_24__f)) in exact x).
Local Lemma MEMO_24_c : MEMO_24 = Some E_W2c. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_24 MEMO_24__f. Qed.
Local Lemma MEMO_24_e : ltac2:(tb__ "0|0|
S46S3S1aA1S62SacSd9A2S5S1aS75A2A3").
Proof. exact (@eq_trans _ (apply_xforms E_W2c0 xs_w2) MEMO_24 (Some E_W2c) (@eq_refl _ (apply_xforms E_W2c0 xs_w2)) MEMO_24_c). Qed.
Lemma xs_w2_ok : ltac2:(tb__ "0|0|
S46S3S1aA1S62SacSd9A2S5S1aS75A2A3"). Proof. exact MEMO_24_e. Qed.
Definition s_w2 : wsub := ltac2:(tb__ "0|c|
S0SaS43S14A2M0S1S43S14PcM1S17S48S16P1A1M2S11N230A1A3M3A4S0G0S1S43S14PdM4S11Z1A1A4S0G0S1S43S14PeM5S11Z0A1M6A4S0G0S1S43S14PfG6A4M7S0G0S1S43S14G5G2A4S0G0S1S43S14G4S11N288A1A4S0G0S1S43S14G1G2A4S0G0S1S43S14P5bG6A4S0G0S1S43S14P5aG6A4S0G0S1S43S14P59G6A4S0G0S1S43S14P58M8G6A4S0G0S1S43S14P57G6A4S0G0S1S43S14P56G6A4S0G0S1S43S14P55G6A4S0G0S1S43S14P54G6A4S0G0S1S43S14P53G6A4S0G0S1S43S14P52G6A4S0G0S1S43S14P51G6A4S0G0S1S43S14P50G6A4S0G0S1S43S14P4fG6A4S0G0S1S43S14P4eG6A4S0G0S1S43S14P4dG6A4S0G0S1S43S14P4cG6A4S0G0S1S43S14P4bG6A4S0G0S1S43S14P4aG6A4S0G0S1S43S14P49G6A4S0G0S1S43S14P48G6A4S0G0S1S43S14P47G6A4S0G0S1S43S14P46G6A4S0G0S1S43S14P45G6A4S0G0S1S43S14P44G6A4S0G0S1S43S14P43G6A4S0G0S1S43S14P42G6A4S0G0S1S43S14P41G6A4S0G0S1S43S14P40G6A4S0G0S1S43S14P3fG6A4S0G0S1S43S14P3eG6A4S0G0S1S43S14P3dG6A4S0G0S1S43S14P3cM9G6A4S0G0S1S43S14P33S16G9A1A4S0G0S1S43S14P32S16P3bA1A4S0G0S1S43S14P31S16P3aA1A4S0G0S1S43S14P30S16P39A1A4S0G0S1S43S14P2fG6A4S0G0S1S43S14P2eG6A4S0G0S1S43S14P2dMaG6A4S0G0S1S43S14P2cG6A4S0G0S1S43S14P2bG6A4S0G0S1S43S14P29S11Z5a338A1A4S0G0S1S43S14P28S11Z5a798A1A4S0G0S1S43S14P24MbS11Z1A1A4S0G0S1S43S14P23S11Z1A1A4S0G0S1S43S14P22G6A4S0G0S1S43S14P21S17S51S17S48G2S11N22fA1A3G3A3A4S0G0G7S0G0S1S43S14P1bS16GbA1A4S0G0S1S43S14P1aS11Z22224A1A4S0G0S1S43S14P19S11Z0A1A4S0G0S1S43S14P18S11Z3a0d0A1A4S0G0S1S43S14PaS17S48G2S11N2b0A1A3A4S0G0S1S43S14P15S11Z22a3cA1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Local Definition MEMO_25 : ltac2:(tb__ "0|0|
S3S4S18A1A1") := ltac2:(tb__ "0|0|
S104S75S69S7bA3").
Definition R_w2 : list sobj := ltac:(let x := eval vm_compute in (match MEMO_25 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_25_c : MEMO_25 = Some R_w2. Proof. vm_cast_no_check (@eq_refl _ MEMO_25). Qed.
Local Lemma MEMO_25_e : ltac2:(tb__ "0|1|
S46S3S4S18A1M0A1S104S75S69S7bA3S5G0S9fA2A3").
Proof. exact (@eq_trans _ (entails_fr E_W2c Pre_wl2 s_w2) MEMO_25 (Some R_w2) (@eq_refl _ (entails_fr E_W2c Pre_wl2 s_w2)) MEMO_25_c). Qed.
Lemma efr_w2 : ltac2:(tb__ "0|1|
S46S3S4S18A1M0A1S104S75S69S7bA3S5G0S9fA2A3"). Proof. exact MEMO_25_e. Qed.
Lemma chk_w2 : ltac2:(tb__ "0|0|
S46S9S10aS75S69S7bS9fS0S56S57S68S5aA2S2S56A1A3A5S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_w2 : ltac2:(tb__ "0|0|
S46S9S10dS15S2dS1cS75A1A1S20S6eA1A3S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma facts_w2c : ltac2:(tb__ "0|0|
S46S4S15A1S20S75A1S20S6eA1A3"). Proof. reflexivity. Qed.
Lemma s_w2_vals : ltac2:(tb__ "0|1|
S47S46S14S101S7bPcA2S17S48S16P1A1S11N230A1A3A3S47S46S14S101S7bPdA2S11Z1A1A3S47S46S14S101S7bPeA2S11Z0A1M0A3S46S14S101S7bPfA2G0A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_26 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S109S7bP5cS68S1cS75A1S9fA5").
Definition T_D2i : sstate := ltac:(let x := eval vm_compute in (MEMO_26) in exact x).
Local Lemma MEMO_26_c : MEMO_26 = T_D2i. Proof. vm_cast_no_check (@eq_refl _ MEMO_26). Qed.
Local Lemma MEMO_26_e : ltac2:(tb__ "0|0|
S46S1aS109S7bP5cS68S1cS75A1S9fA5S96A3").
Proof. exact (@eq_trans _ (import_post s_w2 92 D (ss_next E_W2c) R_w2) MEMO_26 (T_D2i) (@eq_refl _ (import_post s_w2 92 D (ss_next E_W2c) R_w2)) MEMO_26_c). Qed.
Lemma T_D2i_eq : ltac2:(tb__ "0|0|
S46S1aS109S7bP5cS68S1cS75A1S9fA5S96A3"). Proof. exact MEMO_26_e. Qed.
Definition xs_d2 : list xform := ltac2:(tb__ "0|4|
S0S61S66U0M0A1S0S61S65S0S6U4S0S6G0S0S6U5S0S6U1S0S6U6S0S6U7M1S0S6U8S0S6U9S0S6UaS0S6UbS0S6U3S0S6UcS0S6UdS0S6U2S2S6A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S61S64G0A1M2S0S61G2S0S61S64G1A1M3S0S61G3S2S61A1A3A3A3A3A3A3").
Local Definition MEMO_27 : ltac2:(tb__ "0|0|
S3S1aA1") := ltac2:(tb__ "0|0|
S62SffS20S6eA1S96A2SbdA2").
Local Definition MEMO_27__f : ltac2:(tb__ "0|0|
S3S1aA1") := ltac2:(tb__ "0|0|
S12aSffS20S6eA1S96A2SbdA2").
Definition T_D2 : sstate := ltac:(let x := eval vm_compute in (xget T_D2i (MEMO_27__f)) in exact x).
Local Lemma MEMO_27_c : MEMO_27 = Some T_D2. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_27 MEMO_27__f. Qed.
Local Lemma MEMO_27_e : ltac2:(tb__ "0|0|
S46S3S1aA1S62SffS20S6eA1S96A2SbdA2S5S1aSa4A2A3").
Proof. exact (@eq_trans _ (apply_xforms (add_facts (ss_facts E_W2) T_D2i) xs_d2) MEMO_27 (Some T_D2) (@eq_refl _ (apply_xforms (add_facts (ss_facts E_W2) T_D2i) xs_d2)) MEMO_27_c). Qed.
Lemma xs_d2_ok : ltac2:(tb__ "0|0|
S46S3S1aA1S62SffS20S6eA1S96A2SbdA2S5S1aSa4A2A3"). Proof. exact MEMO_27_e. Qed.
Lemma fb_d2 : ltac2:(tb__ "0|0|
S46S9S10dS15S2dS1cS96A1A1S20S6eA1A3S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Local Definition MEMO_28 : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S58S67S6aS2S44A1Sa4S7A5").
Local Definition MEMO_28__f : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S119S67S6aS2S44A1Sa4S7A5").
Definition E_exit : sstate := ltac:(let x := eval vm_compute in (lf0 T_D2 (MEMO_28__f) 0) in exact x).
Local Lemma MEMO_28_c : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1Se4S5G0S0S56S57S9aS59A2S2S56A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_28 MEMO_28__f. Qed.
Local Lemma MEMO_28_e : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS2S44A1Sa4S7A5S5G0S0S56S57S9aS59A2S2S56A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T_D2 true) MEMO_28 (Some [mkLeaf E_exit RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T_D2 true)) MEMO_28_c). Qed.
Lemma run_d2 : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS2S44A1Sa4S7A5S5G0S0S56S57S9aS59A2S2S56A1A3A2A3").
Proof. exact MEMO_28_e. Qed.
Lemma cert_exit : ltac2:(tb__ "0|0|
S47S46S3S4eA1S5cS67S2fS9aA1A2S5S4eS52A2A3S47S46S14S28S9aZ11A2S11Z5eA1A3S46S14S28S9aZaA2S11Z2A1A3A2A2").
Proof. repeat split; reflexivity. Qed.

Definition Tsm : sstate := ltac2:(tb__ "0|0|
SffS0S15S19S16P1cA1S11Z3fA1A2S2S15A1A3ScbA2").
Local Definition MEMO_29 : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S58S67S6aS0S44S10bS2S44A1A3SbbS7A5").
Local Definition MEMO_29__f : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S119S67S6aS0S44S10bS2S44A1A3SbbS7A5").
Definition X_ovfS : sstate := ltac:(let x := eval vm_compute in (lf0 Tsm (MEMO_29__f) 0) in exact x).
Definition E_fx0 : sstate := ltac:(let x := eval vm_compute in (lf0 Tsm (MEMO_29__f) 1) in exact x).
Local Lemma MEMO_29_c : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1Se5S5G0S0S56S57ScdS59A2S0S56S57S90S5aA2S2S56A1A3A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_29 MEMO_29__f. Qed.
Local Lemma MEMO_29_e : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS0S44S10bS2S44A1A3SbbS7A5S5G0S0S56S57ScdS59A2S0S56S57S90S5aA2S2S56A1A3A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [fwritex_entry] Tsm true) MEMO_29 (Some [mkLeaf X_ovfS RsEcall; mkLeaf E_fx0 RsCut]) (@eq_refl _ (sym_run segs FUEL [fwritex_entry] Tsm true)) MEMO_29_c). Qed.
Lemma run_sm : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS0S44S10bS2S44A1A3SbbS7A5S5G0S0S56S57ScdS59A2S0S56S57S90S5aA2S2S56A1A3A3A2A3").
Proof. exact MEMO_29_e. Qed.
Lemma fact_ovfS : In BNZ28 (ss_facts X_ovfS). Proof. cbn. tauto. Qed.

Local Definition MEMO_30 : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S58S67S6aS0S44S10bS2S44A1A3S90S7A5").
Local Definition MEMO_30__f : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S119S67S6aS0S44S10bS2S44A1A3S90S7A5").
Definition E_fx : sstate := ltac:(let x := eval vm_compute in (lf0 E_fx0 (MEMO_30__f) 0) in exact x).
Local Lemma MEMO_30_c : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1Se6S5G0S0S56S57Sa9S5aA2S2S56A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_30 MEMO_30__f. Qed.
Local Lemma MEMO_30_e : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS0S44S10bS2S44A1A3S90S7A5S5G0S0S56S57Sa9S5aA2S2S56A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [fwritex_entry] E_fx0 true) MEMO_30 (Some [mkLeaf E_fx RsCut]) (@eq_refl _ (sym_run segs FUEL [fwritex_entry] E_fx0 true)) MEMO_30_c). Qed.
Lemma run_fx0 : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS0S44S10bS2S44A1A3S90S7A5S5G0S0S56S57Sa9S5aA2S2S56A1A3A2A3").
Proof. exact MEMO_30_e. Qed.
Lemma E_fx_next : ss_next E_fx = 70%positive. Proof. reflexivity. Qed.

Definition xs_fx : list xform := ltac2:(tb__ "0|2|
S0S61S63U0M0S11N1e0A1A2S0S61S63G0S11N21fA1A2S0S61S63G0S11N460A1A2S0S61S63G0S11N4a0A1A2S0S61S63U9M1S11Z29e78A1A2S0S61S63G1S11Z29d90A1A2S2S61A1A3A3A3A3A3A3").
Local Definition MEMO_31 := apply_xforms E_fx xs_fx.
Local Definition MEMO_31__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_fx xs_fx.
Definition E_fxX : sstate := ltac:(let x := eval vm_compute in (xget E_fx (MEMO_31__f)) in exact x).
Local Lemma MEMO_31_c : MEMO_31 = Some E_fxX. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_31 MEMO_31__f. Qed.
Local Lemma MEMO_31_e : ltac2:(tb__ "0|0|
S46S3S1aA1S62Sa9Sd5A2S5S1aSb1A2A3").
Proof. exact (@eq_trans _ (apply_xforms E_fx xs_fx) MEMO_31 (Some E_fxX) (@eq_refl _ (apply_xforms E_fx xs_fx)) MEMO_31_c). Qed.
Lemma xs_fx_ok : ltac2:(tb__ "0|0|
S46S3S1aA1S62Sa9Sd5A2S5S1aSb1A2A3"). Proof. exact MEMO_31_e. Qed.

Definition nocells (o : sobj) : sobj := ltac2:(tb__ "0|0|
S1bS33Vo;A1S2cVo;A1S2bVo;A1S2S12A1S1dA5").
Definition E_fxW : sstate := ltac:(let x := eval vm_compute in
  (set_objs E_fxX (obj E_fxX 0 :: nocells (obj E_fxX 1) :: obj E_fxX 2 :: nocells (obj E_fxX 3) :: skipn 4 (ss_objs E_fxX))) in exact x).
Lemma ent_fxW : ltac2:(tb__ "0|0|
S46S9S105Sb1Sc2S2SaS43S14A2A1A3S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Definition E_fxA : sstate := ltac:(let x := eval vm_compute in
  (mkSS (ss_pc E_fxW) (ss_regs E_fxW) (ss_fregs E_fxW) (ss_fcsr E_fxW) (ss_resv E_fxW) (ss_objs E_fxW)
        (SPAlign 70 2 :: ss_facts E_fxW) 71%positive false) in exact x).
Lemma diff_fxA : ltac2:(tb__ "0|4|
S46S3SaS4SaS14S14A2M0A1M1S4S15A1M2A2M3A1S11bSc2S6fA2S5G3S1G1G2S2G0A1S0S15S22P46Z2A2S2S15A1A3A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), [SPAlign 70 2]))). Qed.
Lemma swf_E_fxA : swf E_fxA = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma norl7_fxA : state_has_rl 7 E_fxA = false. Proof. vm_cast_no_check (@eq_refl _ false). Qed.
Lemma E_fxA_next : ltac2:(tb__ "0|1|
S47S46S43S1cS6fA1P47A3S47S46S43S1cSb1A1P46M0A3S46S43S1cSc2A1G0A3A2A2"). Proof. repeat split; reflexivity. Qed.

Definition s_nr (n r : Z) : wsub := ltac2:(tb__ "0|1|
S0SaS43S14A2M0S1S43S14P1cS11Vn;A1A4S0G0S1S43S14P19S17S48S16P46A1S11Vr;A1A3A4S2G0A1A3A3").
Definition a70r (r : Z) : sv := ltac2:(tb__ "0|0|
S17S48S16P46A1S11Vr;A1A3").
Definition setbase (b : sv) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S1bVb;S2cVo;A1S2bVo;A1S2aVo;A1S2eVo;A1A5").

Definition F_n (n : Z) : sprop := ltac2:(tb__ "0|0|
S19S11S12eVn;Z11A2A1S16P1bA1A2").
Definition C0_nr (n r : Z) : sstate := ltac2:(tb__ "0|2|
S29S2fS6fA1S5bS14S5bS14S36S6fA1UaSefVr;A1M0A4UbS11Vn;A1A4S35S6fA1S34S6fA1S37S6fA1SdS18S126S18UdM1S23S6fA1A3S0S18Sf9G0S6cS6fG1A2A2S2S18A1A3A3S0S15Sd0Vn;A1S20S6fA1A3S1cS6fA1S8A9").
Definition xs_c (n : Z) : list xform := ltac2:(tb__ "0|0|
S0S61S63U3S11S12cVn;Z21fA2A1A2S2S61A1A3").

Definition pre_loc (C : sstate) : sstate := ltac2:(tb__ "0|0|
S60VC;S0S18S6cVC;U1A2S0S18S6cVC;U3A2S0S18S6cVC;U4A2S0S18S6cVC;UeA2S0S18S6cVC;UbA2S2S18A1A3A3A3A3A3A2").

Definition sobj_eqb (o o' : sobj) : bool := ltac2:(tb__ "0|0|
SbSbSbSbS38S33Vo;A1S33Vo';A1A2S38S2cVo;A1S2cVo';A1A2A2S38S2bVo;A1S2bVo';A1A2A2S11cS12S106S2aVo;A1S2aVo';A1A4A2S108S2eVo;A1S2eVo';A1A2A2").

Definition R_gen : list sobj := ltac:(let x := eval vm_compute in (map (obj E_fxA) [0;2;4;5;6;7;8;9;11;12]%nat) in exact x).
Definition FUELm : nat := 3000%nat.

Definition upd_cell (off : Z) (v : sv) (o : sobj) : sobj := ltac2:(tb__ "0|3|
S1bS33Vo;A1S2cVo;A1S2bVo;A1S123S12S12S12S14S12Lx;S3cR1A1S44S9S12L_;S12fR1Voff;A2S13S3cR2A1S3dR2A1Vv;A3R2X9x2Lo';S43R2Li;S54S14S14R4Lb;La;M0Lop;M1G1S55G0Lop;M2G2S9S45S14R4La;Lw;Lsgn;S43S14S44R4Lk;Li;Ll;X14x8Lc;S2aVo;A1A4S2eVo;A1A5").
Definition po_fresh : list (nat * positive) := ltac2:(tb__ "0|1|
S0SaS6S43A2M0S1S6S43U5P47A4S0G0S1S6S43U6P48A4S0G0S1S6S43U7P49A4S0G0S1S6S43UaP4aA4S0G0S1S6S43UbP4bA4S0G0S1S6S43UcP4cA4S0G0S1S6S43UdP4dA4S0G0S1S6S43UeP4eA4S0G0S1S6S43UfP4fA4S0G0S1S6S43U10P50A4S0G0S1S6S43U11P51A4S0G0S1S6S43U1cP52A4S0G0S1S6S43U1dP53A4S0G0S1S6S43U1eP54A4S0G0S1S6S43U1fP55A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition po_regs (regs : list sv) : list sv := ltac2:(tb__ "0|2|
S5bS14S111S4S14A1M0SaS6S43A2M1G0G1S5bS14R2SeS6S43R1A3S16S10S6S43R1A3A1A4Liv;Lrs;Sf5Vregs;A5U1S11S10cA1A4").
Definition wpos_off : Z := 171448.
Definition post_loc (n r : Z) (C : sstate) : sstate := ltac2:(tb__ "0|2|
S29S10cSf6S36VC;A1A1S35VC;A1S34VC;A1S37VC;A1S0S18S6cVC;U1A2S0S18S1bS16P1A1M0S11N21fA1S11S12cVn;Z21fA2A1M1S2S12A1S1fP7A1A5S0S18S6cVC;U4A2S0S18S6cVC;UeA2S0S18SfcSfdS17S48G0G1A3S6cVC;UbA2A3S2S18A1A3A3A3A3A3S20VC;A1P56S8A9").

Definition E_hi_lo : sv := SAlu ALU_ADD (SVar 28) (SLit (-543)).
Definition E_po : sstate := ltac:(let x := eval vm_compute in
  (mkSS ret_out (po_regs (ss_regs E_fxA)) (ss_fregs E_fxA) (ss_fcsr E_fxA) (ss_resv E_fxA)
       ([obj E_fxA 1;
         mkObj (SVar 1) (SLit (-543)) E_hi_lo [] (DList 7);
         mkObj (SVar 1) E_hi_lo (SLit (-480)) [] DUnknown;
         obj E_fxA 13;
         upd_cell wpos_off (SAlu ALU_ADD (SAlu ALU_ADD (SVar 1) (SLit (-543))) (SVar 28)) (obj E_fxA 10)] ++ R_gen)
       (ss_facts E_fxA) 86%positive false) in exact x).
Lemma swf_E_po : swf E_po = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma E_po_next : ss_next E_po = 86%positive. Proof. reflexivity. Qed.

Definition BLn (n : Z) : list bexp := ltac2:(tb__ "0|0|
S123S6S114S6S117P3S12bR1A1A2Lj;S125U0S12dVn;A1A2A4").

Definition diff_in_ok (n r : Z) (ab : sv * sv) : bool := ltac2:(tb__ "0|0|
S5eS102Sd3Vn;Vr;A2SeS14S14Vab;A3A2S10S14S14Vab;A3A2").
Definition diff_out_ok (n r : Z) (ab : sv * sv) : bool := ltac2:(tb__ "0|0|
S5eSeS14S14Vab;A3S102Sd3Vn;Vr;A2S10S14S14Vab;A3A2A2").
Definition ids_below71 : list positive := map Pos.of_nat (seq 1 70).

Definition check_pre (n r : Z) : option (sstate * sstate) := ltac2:(tb__ "0|7|
Se0Vn;Vr;A2S1aS3SaS4SaS14S14A2M0A1M1S4S15A1M2A2M3A1S3SaS1aS1aA2M4A1M5Lx;S11bS6fR1A2G3G3G5Lp;R1G1G2S3S1aA1G5Lx;S62R4SfeVn;A1A2S1aS9G5L_;SbSbSbSbS42R5A1S10dG0Sf2Vn;Vr;A2R3A3A2S11cS15S41R2S0S15Sd0Vn;A1S2S15A1A3A4A2S133S1cR1A1P47A2A2SfS3bR1A1A1A2S5G4S1S1aS1aR1Sf8R1A1A4A2ScG4A1M6X9x2LC;G6X3x2Lnf;Ld;Xax1Lp;G6X3x2TC0;").
Definition the_pre (n r : Z) : sstate := ltac2:(tb__ "0|1|
S3SaS1aS1aA2M0A1S1aLx;Sd1Vn;Vr;A2G0G0S1aLp;R1S1aS1aR1LP;Ls;Xax1Lp;S6fX3x2").
Definition check_core (n r : Z) (res : option (list leaf)) : bool := ltac2:(tb__ "0|f|
S3SaS1aS1aA2M0A1S9Lx;Sd1Vn;Vr;A2G0G0S9Lp;R1S1aS1aSf7Vn;Vr;R2A3S1aSbSbSbS3S4S18A1M1A1S9Lx;S104R3R2S2SaS43S14A2A1M2A3G1S11cS18SfaR1ScaA4LR;S8X3x2S10aR3R2G2ScaS0S56S57R1S5aA2S2S56A1A3A5A2S3S4S56A1M3A1S9Lres;Vres;G3G3S9Ll;R1S8S56G3G3S9Ll0;R1SbSbS3S18A1S9Lx;S10eS18S23S5dR2A1M4A1U1M5A3S18SbSbSbSbS38S2cR1A1S11N21fA1M6A2S38S2bR1A1S11S12cVn;Z21fA2A1A2A2S39S2eR1A1M7A1A2SfS3aG7A1A1A2S3S4S114A1M8A1S9Lx;S115S2aR1A1G6Z0S12dVn;A1A4G8S11cS114S118R1SdfVn;A1A4Lbl;S8X3x2A2Lo;S8X3x2SfS128P7M9G4A2A1A2S11aG4G5G9A3S1aS100P47MaR1R5A3S103SbS105R2R6R1A3S10dS43S43S38S101R2R1A2S16R1A1A2Li;Sf4A3A2Ts;Twl;A2S56G3S8Ll2;Ll1;X4x2Ll0;LL;X4x2Ll;S8X3x2A2S3SaS4SaS14S14A2MbA1McS4S15A1MdA2MeA1S9Lx;S11bS109G2GaR1GaScaA5Sc3A2GeGeS9Lp;R1GcGdGdS9Ll;R1S10dGbSf3Vn;Vr;A2R2A3S15GdS8Ll0;Ls;X4x2Ll;Ld;Xax1Lp;S8X3x2A2TQ;LP;LC;Xax1Lp;S8X3x2").

Definition check_nr (r n : nat) : bool := ltac2:(tb__ "0|2|
Sf0S12bVn;A1M0S12bVr;A1M1S58S67Se1S0S44S10cS2S44A1A3SfbG0G1A2S7A5A3").
Definition check_range (r a len : nat) : bool := ltac2:(tb__ "0|0|
S10dS6Sf1Vr;A1S125Va;Vlen;A2A3").

Definition xs_po : list xform := ltac2:(tb__ "0|4|
S0S61S65S0S6U5S0S6U0M0S0S6U6S0S6U1S0S6U2S0S6U7S0S6U8M1S0S6U9S0S6UaS0S6UbS0S6UcS0S6U4S0S6UdS0S6UeS0S6U3S2S6A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S61S64G0A1M2S0S61G2S0S61S64G1A1M3S0S61G3S2S61A1A3A3A3A3A3").
Local Definition MEMO_32 := apply_xforms E_po xs_po.
Local Definition MEMO_32__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_po xs_po.
Definition E_po2 : sstate := ltac:(let x := eval vm_compute in (xget E_po (MEMO_32__f)) in exact x).
Local Lemma MEMO_32_c : MEMO_32 = Some E_po2. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_32 MEMO_32__f. Qed.
Local Lemma MEMO_32_e : ltac2:(tb__ "0|0|
S46S3S1aA1S62Sc3Sd6A2S5S1aSb2A2A3").
Proof. exact (@eq_trans _ (apply_xforms E_po xs_po) MEMO_32 (Some E_po2) (@eq_refl _ (apply_xforms E_po xs_po)) MEMO_32_c). Qed.
Lemma xs_po_ok : ltac2:(tb__ "0|0|
S46S3S1aA1S62Sc3Sd6A2S5S1aSb2A2A3"). Proof. exact MEMO_32_e. Qed.

Definition E_po62 : sstate := ltac2:(tb__ "0|0|
SffS0S15S19S16P1cA1S11Z3eA1A2S2S15A1A3Sb2A2").
Definition E_po63 : sstate := ltac2:(tb__ "0|0|
SffS0S15S19S11Z3fA1S16P1cA1A2S2S15A1A3Sb2A2").
Local Definition MEMO_33 : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S58S67S6aS0S44S10bS2S44A1A3Sb3S7A5").
Local Definition MEMO_33__f : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S119S67S6aS0S44S10bS2S44A1A3Sb3S7A5").
Definition E_fx2a : sstate := ltac:(let x := eval vm_compute in (lf0 E_po62 (MEMO_33__f) 0) in exact x).
Local Lemma MEMO_33_c : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1Se7S5G0S0S56S57S91S5aA2S2S56A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_33 MEMO_33__f. Qed.
Local Lemma MEMO_33_e : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS0S44S10bS2S44A1A3Sb3S7A5S5G0S0S56S57S91S5aA2S2S56A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [fwritex_entry] E_po62 true) MEMO_33 (Some [mkLeaf E_fx2a RsCut]) (@eq_refl _ (sym_run segs FUEL [fwritex_entry] E_po62 true)) MEMO_33_c). Qed.
Lemma run_po62 : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS0S44S10bS2S44A1A3Sb3S7A5S5G0S0S56S57S91S5aA2S2S56A1A3A2A3").
Proof. exact MEMO_33_e. Qed.
Local Definition MEMO_34 : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S58S67S6aS2S44A1S91S7A5").
Local Definition MEMO_34__f : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S119S67S6aS2S44A1S91S7A5").
Definition E_Wa1 : sstate := ltac:(let x := eval vm_compute in (lf0 E_fx2a (MEMO_34__f) 0) in exact x).
Definition E_Wa2 : sstate := ltac:(let x := eval vm_compute in (lf0 E_fx2a (MEMO_34__f) 1) in exact x).
Local Lemma MEMO_34_c : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1Se8S5G0S0S56S57SadS59A2S0S56S57SaeS59A2S2S56A1A3A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_34 MEMO_34__f. Qed.
Local Lemma MEMO_34_e : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS2S44A1S91S7A5S5G0S0S56S57SadS59A2S0S56S57SaeS59A2S2S56A1A3A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] E_fx2a true) MEMO_34 (Some [mkLeaf E_Wa1 RsEcall; mkLeaf E_Wa2 RsEcall]) (@eq_refl _ (sym_run segs FUEL [] E_fx2a true)) MEMO_34_c). Qed.
Lemma run_fx2a : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS2S44A1S91S7A5S5G0S0S56S57SadS59A2S0S56S57SaeS59A2S2S56A1A3A3A2A3").
Proof. exact MEMO_34_e. Qed.

Definition dropfact (S : sstate) : sstate := ltac2:(tb__ "0|0|
S29S2fVS;A1S36VS;A1S35VS;A1S34VS;A1S37VS;A1S23VS;A1S113S15S20VS;A1A2S1cVS;A1S3bVS;A1A9").
Definition E_Wa : sstate := ltac:(let x := eval vm_compute in (dropfact E_Wa1) in exact x).
Lemma ent_Wa1 : ltac2:(tb__ "0|0|
S46S9S105SadS7eS2SaS43S14A2A1A3S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma ent_Wa2 : ltac2:(tb__ "0|0|
S46S9S105SaeS7eS2SaS43S14A2A1A3S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Local Definition MEMO_35 : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S58S67S6aS0S44S10bS2S44A1A3Sb4S7A5").
Local Definition MEMO_35__f : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S119S67S6aS0S44S10bS2S44A1A3Sb4S7A5").
Definition E_fx2b : sstate := ltac:(let x := eval vm_compute in (lf0 E_po63 (MEMO_35__f) 0) in exact x).
Local Lemma MEMO_35_c : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1Se9S5G0S0S56S57S92S5aA2S2S56A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_35 MEMO_35__f. Qed.
Local Lemma MEMO_35_e : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS0S44S10bS2S44A1A3Sb4S7A5S5G0S0S56S57S92S5aA2S2S56A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [fwritex_entry] E_po63 true) MEMO_35 (Some [mkLeaf E_fx2b RsCut]) (@eq_refl _ (sym_run segs FUEL [fwritex_entry] E_po63 true)) MEMO_35_c). Qed.
Lemma run_po63 : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS0S44S10bS2S44A1A3Sb4S7A5S5G0S0S56S57S92S5aA2S2S56A1A3A2A3").
Proof. exact MEMO_35_e. Qed.
Local Definition MEMO_36 : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S58S67S6aS2S44A1S92S7A5").
Local Definition MEMO_36__f : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S119S67S6aS2S44A1S92S7A5").
Definition E_Wb : sstate := ltac:(let x := eval vm_compute in (lf0 E_fx2b (MEMO_36__f) 0) in exact x).
Local Lemma MEMO_36_c : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1SeaS5G0S0S56S57S77S59A2S2S56A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_36 MEMO_36__f. Qed.
Local Lemma MEMO_36_e : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS2S44A1S92S7A5S5G0S0S56S57S77S59A2S2S56A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] E_fx2b true) MEMO_36 (Some [mkLeaf E_Wb RsEcall]) (@eq_refl _ (sym_run segs FUEL [] E_fx2b true)) MEMO_36_c). Qed.
Lemma run_fx2b : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS2S44A1S92S7A5S5G0S0S56S57S77S59A2S2S56A1A3A2A3").
Proof. exact MEMO_36_e. Qed.

Definition IOVa : sv := ltac:(let x := eval vm_compute in (reg_sv E_Wa 12) in exact x).
Lemma r12_wa : ltac2:(tb__ "0|0|
S47S46S14S28S7eZcA2Sc5A3S46S14S28S7eZ12A2Sc5A3A2"). Proof. split; reflexivity. Qed.
Definition E_Wa_r : sstate := ltac:(let x := eval vm_compute in
  (mkSS (ss_pc E_Wa) (list_set (list_set (ss_regs E_Wa) 12 (SLit 2)) 18 (SLit 2)) (ss_fregs E_Wa) (ss_fcsr E_Wa) (ss_resv E_Wa)
        (ss_objs E_Wa) (ss_facts E_Wa) (ss_next E_Wa) false) in exact x).
Lemma diff_wa : ltac2:(tb__ "0|5|
S46S3SaS4SaS14S14A2M0A1M1S4S15A1M2A2M3A1S11bS7eSc0A2S5G3S1G1G2S0G0S1S14S14Sc5S11Z2A1A4M4S0G0G4S2G0A1A3A3S2S15A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(IOVa, SLit 2); (IOVa, SLit 2)], @nil sprop))). Qed.
Lemma swf_E_Wa_r : swf E_Wa_r = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Definition xs_wa1 : list xform := ltac2:(tb__ "0|0|
S0S61S63U0S11N230A1A2S0S61S63U3S17S48S16P1cA1S11N21eA1A3A2S2S61A1A3A3").
Local Definition MEMO_37 := apply_xforms E_Wa_r xs_wa1.
Local Definition MEMO_37__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_Wa_r xs_wa1.
Definition E_Wa_x : sstate := ltac:(let x := eval vm_compute in (xget E_Wa_r (MEMO_37__f)) in exact x).
Local Lemma MEMO_37_c : MEMO_37 = Some E_Wa_x. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_37 MEMO_37__f. Qed.
Local Lemma MEMO_37_e : ltac2:(tb__ "0|0|
S46S3S1aA1S62Sc0SdbA2S5S1aS87A2A3").
Proof. exact (@eq_trans _ (apply_xforms E_Wa_r xs_wa1) MEMO_37 (Some E_Wa_x) (@eq_refl _ (apply_xforms E_Wa_r xs_wa1)) MEMO_37_c). Qed.
Lemma xs_wa1_ok : ltac2:(tb__ "0|0|
S46S3S1aA1S62Sc0SdbA2S5S1aS87A2A3"). Proof. exact MEMO_37_e. Qed.

Lemma obj1_wa : ltac2:(tb__ "0|3|
S47S46S3S18A1S10eS18S23S87A1U1M0A3S5S18S6cS87G0A2M1A2A3S47S46S14S2cG1A1S11N230A1A3S47S46S14S2bG1A1S11N21fA1A3S47S46S9S39S2eG1A1M2A1S7A3S46S9S3aG2A1S8A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma cb_wa1 : ltac2:(tb__ "0|1|
S46S3S4S114A1M0A1S115S2aS6cS87U1A2A1S11N230A1Z0U11A4S5G0SbfA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some BL_co)). Qed.
Lemma norl8_wa : state_has_rl 8 E_Wa_x = false. Proof. vm_cast_no_check (@eq_refl _ false). Qed.
Local Definition MEMO_38 := obj_to_list E_Wa_x 1 8.
Definition E_Wa_l1 : sstate := ltac:(let x := eval vm_compute in (MEMO_38) in exact x).
Local Lemma MEMO_38_c : MEMO_38 = E_Wa_l1. Proof. vm_cast_no_check (@eq_refl _ MEMO_38). Qed.
Local Lemma MEMO_38_e : ltac2:(tb__ "0|0|
S46S1aS11aS87U1P8A3S86A3").
Proof. exact (@eq_trans _ (obj_to_list E_Wa_x 1 8) MEMO_38 (E_Wa_l1) (@eq_refl _ (obj_to_list E_Wa_x 1 8)) MEMO_38_c). Qed.
Lemma E_Wa_l1_eq : ltac2:(tb__ "0|0|
S46S1aS11aS87U1P8A3S86A3"). Proof. exact MEMO_38_e. Qed.
Definition LOnl : sv := SAlu ALU_ADD (SVar 28) (SLit (-543)).
Definition HInl : sv := SAlu ALU_ADD (SVar 28) (SLit (-542)).
Lemma obj3_wa : ltac2:(tb__ "0|3|
S47S46S3S18A1S10eS18S23S86A1U3M0A3S5S18S6cS86G0A2M1A2A3S47S46S14S2cG1A1S93A3S47S46S14S2bG1A1Sc4A3S47S46S9S39S2eG1A1M2A1S7A3S47S46S9S3aG2A1S8A3S46S14S33G1A1S16P1A1A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma cb_wa3 : ltac2:(tb__ "0|1|
S46S3S4S114A1M0A1S115S2aS6cS86U3A2A1S93Z0U1A4S5G0S0S114S116ZaA1S2S114A1A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some [BLit 10])). Qed.
Lemma norl9_wa : state_has_rl 9 E_Wa_l1 = false. Proof. vm_cast_no_check (@eq_refl _ false). Qed.
Local Definition MEMO_39 := obj_to_list E_Wa_l1 3 9.
Definition E_Wa_l : sstate := ltac:(let x := eval vm_compute in (MEMO_39) in exact x).
Local Lemma MEMO_39_c : MEMO_39 = E_Wa_l. Proof. vm_cast_no_check (@eq_refl _ MEMO_39). Qed.
Local Lemma MEMO_39_e : ltac2:(tb__ "0|0|
S46S1aS11aS86U3P9A3Sa6A3").
Proof. exact (@eq_trans _ (obj_to_list E_Wa_l1 3 9) MEMO_39 (E_Wa_l) (@eq_refl _ (obj_to_list E_Wa_l1 3 9)) MEMO_39_c). Qed.
Lemma E_Wa_l_eq : ltac2:(tb__ "0|0|
S46S1aS11aS86U3P9A3Sa6A3"). Proof. exact MEMO_39_e. Qed.

Lemma m1_wa : ltac2:(tb__ "0|5|
S47S46S3S18A1M0S10eS18S23Sa6A1M1U1A3S5S18S1bS16P1A1M2S11N230A1S11N21fA1M3S2S12A1M4S1fP8A1A5A2A3S46G0S10eS18G1U2A3S5S18S1bG2G3S93G4S1fP7A1A5A2A3A2").
Proof. split; reflexivity. Qed.
Lemma norl10_wa : state_has_rl 10 E_Wa_l = false. Proof. vm_cast_no_check (@eq_refl _ false). Qed.
Local Definition MEMO_40 := merge_lists E_Wa_l 1 10.
Definition E_Wa_m1 : sstate := ltac:(let x := eval vm_compute in (MEMO_40) in exact x).
Local Lemma MEMO_40_c : MEMO_40 = E_Wa_m1. Proof. vm_cast_no_check (@eq_refl _ MEMO_40). Qed.
Local Lemma MEMO_40_e : ltac2:(tb__ "0|0|
S46S1aS11dSa6U1PaA3Sa7A3").
Proof. exact (@eq_trans _ (merge_lists E_Wa_l 1 10) MEMO_40 (E_Wa_m1) (@eq_refl _ (merge_lists E_Wa_l 1 10)) MEMO_40_c). Qed.
Lemma E_Wa_m1_eq : ltac2:(tb__ "0|0|
S46S1aS11dSa6U1PaA3Sa7A3"). Proof. exact MEMO_40_e. Qed.
Lemma swf_E_Wa_m1 : swf E_Wa_m1 = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma m2_wa : ltac2:(tb__ "0|4|
S47S46S3S18A1M0S10eS18S23Sa7A1M1U1A3S5S18S1bS16P1A1M2S11N230A1S93S2S12A1M3S1fPaA1A5A2A3S46G0S10eS18G1U2A3S5S18S1bG2S93Sc4G3S1fP9A1A5A2A3A2").
Proof. split; reflexivity. Qed.
Lemma norl5_wa : state_has_rl 5 E_Wa_m1 = false. Proof. vm_cast_no_check (@eq_refl _ false). Qed.
Local Definition MEMO_41 := merge_lists E_Wa_m1 1 5.
Definition E_Wa_m2 : sstate := ltac:(let x := eval vm_compute in (MEMO_41) in exact x).
Local Lemma MEMO_41_c : MEMO_41 = E_Wa_m2. Proof. vm_cast_no_check (@eq_refl _ MEMO_41). Qed.
Local Lemma MEMO_41_e : ltac2:(tb__ "0|0|
S46S1aS11dSa7U1P5A3S8eA3").
Proof. exact (@eq_trans _ (merge_lists E_Wa_m1 1 5) MEMO_41 (E_Wa_m2) (@eq_refl _ (merge_lists E_Wa_m1 1 5)) MEMO_41_c). Qed.
Lemma E_Wa_m2_eq : ltac2:(tb__ "0|0|
S46S1aS11dSa7U1P5A3S8eA3"). Proof. exact MEMO_41_e. Qed.
Lemma swf_E_Wa_m2 : swf E_Wa_m2 = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Definition B544 : sv := SAlu ALU_ADD (SVar 1) (SLit (-560)).
Definition LENa : sv := SAlu ALU_ADD (SVar 28) (SLit 18).
Lemma rf_wa : ltac2:(tb__ "0|0|
S46S3S18A1S10eS18S23S8eA1U1A3S5S18S1bS16P1A1S11N230A1Sc4S2S12A1S1fP5A1A5A2A3"). Proof. reflexivity. Qed.
Local Definition MEMO_42 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S11eS8eU1S83S11Z0A1Sb5A5").
Definition E_Wa_m : sstate := ltac:(let x := eval vm_compute in (MEMO_42) in exact x).
Local Lemma MEMO_42_c : MEMO_42 = E_Wa_m. Proof. vm_cast_no_check (@eq_refl _ MEMO_42). Qed.
Local Lemma MEMO_42_e : ltac2:(tb__ "0|0|
S46S1aS11eS8eU1S83S11Z0A1Sb5A5S81A3").
Proof. exact (@eq_trans _ (reframe_obj E_Wa_m2 1 B544 (SLit 0) LENa) MEMO_42 (E_Wa_m) (@eq_refl _ (reframe_obj E_Wa_m2 1 B544 (SLit 0) LENa)) MEMO_42_c). Qed.
Lemma E_Wa_m_eq : ltac2:(tb__ "0|0|
S46S1aS11eS8eU1S83S11Z0A1Sb5A5S81A3"). Proof. exact MEMO_42_e. Qed.
Lemma swf_E_Wa_m : swf E_Wa_m = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Lemma norl6_wa : state_has_rl 6 E_Wa_m = false. Proof. vm_cast_no_check (@eq_refl _ false). Qed.
Local Definition MEMO_43 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S6dS81S0S18S9bS2S18A1A3S1cS81A1A3").
Definition E_Wa_c0 : sstate := ltac:(let x := eval vm_compute in (MEMO_43) in exact x).
Local Lemma MEMO_43_c : MEMO_43 = E_Wa_c0. Proof. vm_cast_no_check (@eq_refl _ MEMO_43). Qed.
Local Lemma MEMO_43_e : ltac2:(tb__ "0|0|
S46S1aS6dS81S0S18S9bS2S18A1A3S1cS81A1A3SafA3").
Proof. exact (@eq_trans _ (app_objs E_Wa_m [O_emp] (ss_next E_Wa_m)) MEMO_43 (E_Wa_c0) (@eq_refl _ (app_objs E_Wa_m [O_emp] (ss_next E_Wa_m))) MEMO_43_c). Qed.
Lemma E_Wa_c0_eq : ltac2:(tb__ "0|0|
S46S1aS6dS81S0S18S9bS2S18A1A3S1cS81A1A3SafA3"). Proof. exact MEMO_43_e. Qed.
Lemma swf_E_Wa_c0 : swf E_Wa_c0 = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma E_Wa_nexts : ltac2:(tb__ "0|1|
S47S46S43S1cS81A1S1cS7eA1M0A3S47S46S43S1cS87A1G0A3S47S46S43S1cS86A1G0A3S46S43S1cS8eA1G0A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition xs_wa2 : list xform := ltac2:(tb__ "0|2|
S0S61S63U0M0S11N288A1A2S0S61S63G0S11N2a8A1A2S0S61S63UaM1S11Z29e0cA1A2S0S61S63G1S11Z29e08A1A2S2S61A1A3A3A3A3").
Local Definition MEMO_44 := apply_xforms E_Wa_c0 xs_wa2.
Local Definition MEMO_44__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_Wa_c0 xs_wa2.
Definition E_Wa_c : sstate := ltac:(let x := eval vm_compute in (xget E_Wa_c0 (MEMO_44__f)) in exact x).
Local Lemma MEMO_44_c : MEMO_44 = Some E_Wa_c. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_44 MEMO_44__f. Qed.
Local Lemma MEMO_44_e : ltac2:(tb__ "0|0|
S46S3S1aA1S62SafSdcA2S5S1aS76A2A3").
Proof. exact (@eq_trans _ (apply_xforms E_Wa_c0 xs_wa2) MEMO_44 (Some E_Wa_c) (@eq_refl _ (apply_xforms E_Wa_c0 xs_wa2)) MEMO_44_c). Qed.
Lemma xs_wa2_ok : ltac2:(tb__ "0|0|
S46S3S1aA1S62SafSdcA2S5S1aS76A2A3"). Proof. exact MEMO_44_e. Qed.
Definition s_wa : wsub := ltac2:(tb__ "0|6|
S0SaS43S14A2M0S1S43S14PcS17S48S16P1A1M1S11N230A1A3M2A4S0G0S1S43S14PdS17S48S16P1cA1M3S11Z12A1A3A4S0G0S1S43S14PeS11Z0A1M4A4S0G0S1S43S14PfG4A4M5S0G0S1S43S14PeG1A4S0G0S1S43S14PcG1A4S0G0S1S43S14PdG3A4S0G0S1S43S14P5bG4A4S0G0S1S43S14P5aG4A4S0G0S1S43S14P59G4A4S0G0S1S43S14P58G4A4S0G0S1S43S14P57G4A4S0G0S1S43S14P56G4A4S0G0S1S43S14P55G4A4S0G0S1S43S14P54G4A4S0G0S1S43S14P53G4A4S0G0S1S43S14P52G4A4S0G0S1S43S14P51G4A4S0G0S1S43S14P50G4A4S0G0S1S43S14P4fG4A4S0G0S1S43S14P4eG4A4S0G0S1S43S14P4dG4A4S0G0S1S43S14P4cG4A4S0G0S1S43S14P4bG4A4S0G0S1S43S14P4aG4A4S0G0S1S43S14P49G4A4S0G0S1S43S14P48G4A4S0G0S1S43S14P47G4A4S0G0S1S43S14P46G4A4S0G0S1S43S14P45G4A4S0G0S1S43S14P44G4A4S0G0S1S43S14P43G4A4S0G0S1S43S14P42G4A4S0G0S1S43S14P41G4A4S0G0S1S43S14P40G4A4S0G0S1S43S14P3fG4A4S0G0S1S43S14P3eG4A4S0G0S1S43S14P3dG4A4S0G0S1S43S14P3cG4A4S0G0S1S43S14P33S16P55A1A4S0G0S1S43S14P32S16P54A1A4S0G0S1S43S14P31S16P53A1A4S0G0S1S43S14P30S16P52A1A4S0G0S1S43S14P2fG4A4S0G0S1S43S14P2eG4A4S0G0S1S43S14P2dG4A4S0G0S1S43S14P2cG4A4S0G0S1S43S14P2bG4A4S0G0S1S43S14P29S11Z5a338A1A4S0G0S1S43S14P28S11Z5a798A1A4S0G0S1S43S14P24S11Z1A1A4S0G0S1S43S14P23S17S53S17S48S17S48S17S48S16P1A1S11N21fA1A3S16P1cA1A3S11Z1A1A3S11Z3A1A3A4S0G0S1S43S14P22G4A4S0G0S1S43S14P21S17S51S17S48S17S48S17S48G1S11N21fA1A3G3A3S11Z1A1A3G2A3A4S0G0G5S0G0S1S43S14P1bS16P49A1A4S0G0S1S43S14P1aS16P48A1A4S0G0S1S43S14P19S11Z0A1A4S0G0S1S43S14P18S11Z3a0d0A1A4S0G0S1S43S14PaS17S48G1S11N2b0A1A3A4S0G0S1S43S14P15S11Z22a3cA1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Local Definition MEMO_45 : ltac2:(tb__ "0|0|
S3S4S18A1A1") := ltac2:(tb__ "0|0|
S104S76S69S7cA3").
Definition R_wa : list sobj := ltac:(let x := eval vm_compute in (match MEMO_45 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_45_c : MEMO_45 = Some R_wa. Proof. vm_cast_no_check (@eq_refl _ MEMO_45). Qed.
Local Lemma MEMO_45_e : ltac2:(tb__ "0|1|
S46S3S4S18A1M0A1S104S76S69S7cA3S5G0Sa0A2A3").
Proof. exact (@eq_trans _ (entails_fr E_Wa_c Pre_wl2 s_wa) MEMO_45 (Some R_wa) (@eq_refl _ (entails_fr E_Wa_c Pre_wl2 s_wa)) MEMO_45_c). Qed.
Lemma efr_wa : ltac2:(tb__ "0|1|
S46S3S4S18A1M0A1S104S76S69S7cA3S5G0Sa0A2A3"). Proof. exact MEMO_45_e. Qed.
Lemma chk_wa : ltac2:(tb__ "0|0|
S46S9S10aS76S69S7cSa0S0S56S57S68S5aA2S2S56A1A3A5S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_wa : ltac2:(tb__ "0|0|
S46S9S10dS15S2dS1cS76A1A1S20S7eA1A3S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma facts_wac : ltac2:(tb__ "0|0|
S46S4S15A1S20S76A1S20S7eA1A3"). Proof. reflexivity. Qed.
Lemma s_wa_vals : ltac2:(tb__ "0|1|
S47S46S14S101S7cPcA2S83A3S47S46S14S101S7cPdA2Sb5A3S47S46S14S101S7cPeA2S11Z0A1M0A3S46S14S101S7cPfA2G0A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_46 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S109S7cP5cS68S1cS76A1Sa0A5").
Definition T_Dai : sstate := ltac:(let x := eval vm_compute in (MEMO_46) in exact x).
Local Lemma MEMO_46_c : MEMO_46 = T_Dai. Proof. vm_cast_no_check (@eq_refl _ MEMO_46). Qed.
Local Lemma MEMO_46_e : ltac2:(tb__ "0|0|
S46S1aS109S7cP5cS68S1cS76A1Sa0A5Sb9A3").
Proof. exact (@eq_trans _ (import_post s_wa 92 D (ss_next E_Wa_c) R_wa) MEMO_46 (T_Dai) (@eq_refl _ (import_post s_wa 92 D (ss_next E_Wa_c) R_wa)) MEMO_46_c). Qed.
Lemma T_Dai_eq : ltac2:(tb__ "0|0|
S46S1aS109S7cP5cS68S1cS76A1Sa0A5Sb9A3"). Proof. exact MEMO_46_e. Qed.
Definition T_Da : sstate := ltac:(let x := eval vm_compute in (add_facts (ss_facts E_Wa) T_Dai) in exact x).
Lemma xs_da_ok : ltac2:(tb__ "0|0|
S46S3S1aA1S62SffS20S7eA1Sb9A2S2S61A1A2S5S1aSaaA2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma fb_da : ltac2:(tb__ "0|0|
S46S9S10dS15S2dS1cSb9A1A1S20S7eA1A3S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Local Definition MEMO_47 : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S58S67S6aS2S44A1SaaS7A5").
Local Definition MEMO_47__f : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S119S67S6aS2S44A1SaaS7A5").
Definition E_exa : sstate := ltac:(let x := eval vm_compute in (lf0 T_Da (MEMO_47__f) 0) in exact x).
Local Lemma MEMO_47_c : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1SebS5G0S0S56S57S98S59A2S2S56A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_47 MEMO_47__f. Qed.
Local Lemma MEMO_47_e : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS2S44A1SaaS7A5S5G0S0S56S57S98S59A2S2S56A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T_Da true) MEMO_47 (Some [mkLeaf E_exa RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T_Da true)) MEMO_47_c). Qed.
Lemma run_da : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS2S44A1SaaS7A5S5G0S0S56S57S98S59A2S2S56A1A3A2A3").
Proof. exact MEMO_47_e. Qed.
Lemma cert_exa : ltac2:(tb__ "0|0|
S47S46S3S4eA1S5cS67S2fS98A1A2S5S4eS52A2A3S47S46S14S28S98Z11A2S11Z5eA1A3S46S14S28S98ZaA2S11Z2A1A3A2A2").
Proof. repeat split; reflexivity. Qed.

Definition IOVb : sv := ltac:(let x := eval vm_compute in (reg_sv E_Wb 12) in exact x).
Lemma r12_wb : ltac2:(tb__ "0|0|
S47S46S14S28S77ZcA2Sc6A3S46S14S28S77Z12A2Sc6A3A2"). Proof. split; reflexivity. Qed.
Definition E_Wb_r : sstate := ltac:(let x := eval vm_compute in
  (mkSS (ss_pc E_Wb) (list_set (list_set (ss_regs E_Wb) 12 (SLit 2)) 18 (SLit 2)) (ss_fregs E_Wb) (ss_fcsr E_Wb) (ss_resv E_Wb)
        (ss_objs E_Wb) (ss_facts E_Wb) (ss_next E_Wb) false) in exact x).
Lemma diff_wb : ltac2:(tb__ "0|5|
S46S3SaS4SaS14S14A2M0A1M1S4S15A1M2A2M3A1S11bS77Sc1A2S5G3S1G1G2S0G0S1S14S14Sc6S11Z2A1A4M4S0G0G4S2G0A1A3A3S2S15A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(IOVb, SLit 2); (IOVb, SLit 2)], @nil sprop))). Qed.
Lemma swf_E_Wb_r : swf E_Wb_r = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Definition xs_wb1 : list xform := [XSplit 0 (SLit (-560))].
Local Definition MEMO_48 := apply_xforms E_Wb_r xs_wb1.
Local Definition MEMO_48__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_Wb_r xs_wb1.
Definition E_Wb_x : sstate := ltac:(let x := eval vm_compute in (xget E_Wb_r (MEMO_48__f)) in exact x).
Local Lemma MEMO_48_c : MEMO_48 = Some E_Wb_x. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_48 MEMO_48__f. Qed.
Local Lemma MEMO_48_e : ltac2:(tb__ "0|0|
S46S3S1aA1S62Sc1SddA2S5S1aS88A2A3").
Proof. exact (@eq_trans _ (apply_xforms E_Wb_r xs_wb1) MEMO_48 (Some E_Wb_x) (@eq_refl _ (apply_xforms E_Wb_r xs_wb1)) MEMO_48_c). Qed.
Lemma xs_wb1_ok : ltac2:(tb__ "0|0|
S46S3S1aA1S62Sc1SddA2S5S1aS88A2A3"). Proof. exact MEMO_48_e. Qed.
Lemma obj1_wb : ltac2:(tb__ "0|3|
S47S46S3S18A1S10eS18S23S88A1U1M0A3S5S18S6cS88G0A2M1A2A3S47S46S14S2cG1A1S11N230A1A3S47S46S14S2bG1A1S11N21fA1A3S47S46S9S39S2eG1A1M2A1S7A3S46S9S3aG2A1S8A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma cb_wb1 : ltac2:(tb__ "0|1|
S46S3S4S114A1M0A1S115S2aS6cS88U1A2A1S11N230A1Z0U11A4S5G0SbfA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some BL_co)). Qed.
Lemma norl8_wb : state_has_rl 8 E_Wb_x = false. Proof. vm_cast_no_check (@eq_refl _ false). Qed.
Local Definition MEMO_49 := obj_to_list E_Wb_x 1 8.
Definition E_Wb_l : sstate := ltac:(let x := eval vm_compute in (MEMO_49) in exact x).
Local Lemma MEMO_49_c : MEMO_49 = E_Wb_l. Proof. vm_cast_no_check (@eq_refl _ MEMO_49). Qed.
Local Lemma MEMO_49_e : ltac2:(tb__ "0|0|
S46S1aS11aS88U1P8A3Sa8A3").
Proof. exact (@eq_trans _ (obj_to_list E_Wb_x 1 8) MEMO_49 (E_Wb_l) (@eq_refl _ (obj_to_list E_Wb_x 1 8)) MEMO_49_c). Qed.
Lemma E_Wb_l_eq : ltac2:(tb__ "0|0|
S46S1aS11aS88U1P8A3Sa8A3"). Proof. exact MEMO_49_e. Qed.
Lemma m_wb : ltac2:(tb__ "0|5|
S47S46S3S18A1M0S10eS18S23Sa8A1M1U1A3S5S18S1bS16P1A1M2S11N230A1S11N21fA1M3S2S12A1M4S1fP8A1A5A2A3S46G0S10eS18G1U2A3S5S18S1bG2G3S93G4S1fP7A1A5A2A3A2").
Proof. split; reflexivity. Qed.
Lemma norl5_wb : state_has_rl 5 E_Wb_l = false. Proof. vm_cast_no_check (@eq_refl _ false). Qed.
Local Definition MEMO_50 := merge_lists E_Wb_l 1 5.
Definition E_Wb_m1 : sstate := ltac:(let x := eval vm_compute in (MEMO_50) in exact x).
Local Lemma MEMO_50_c : MEMO_50 = E_Wb_m1. Proof. vm_cast_no_check (@eq_refl _ MEMO_50). Qed.
Local Lemma MEMO_50_e : ltac2:(tb__ "0|0|
S46S1aS11dSa8U1P5A3S8fA3").
Proof. exact (@eq_trans _ (merge_lists E_Wb_l 1 5) MEMO_50 (E_Wb_m1) (@eq_refl _ (merge_lists E_Wb_l 1 5)) MEMO_50_c). Qed.
Lemma E_Wb_m1_eq : ltac2:(tb__ "0|0|
S46S1aS11dSa8U1P5A3S8fA3"). Proof. exact MEMO_50_e. Qed.
Lemma swf_E_Wb_m1 : swf E_Wb_m1 = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma rf_wb : ltac2:(tb__ "0|0|
S46S3S18A1S10eS18S23S8fA1U1A3S5S18S1bS16P1A1S11N230A1S93S2S12A1S1fP5A1A5A2A3"). Proof. reflexivity. Qed.
Local Definition MEMO_51 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S11eS8fU1S83S11Z0A1S11Z50A1A5").
Definition E_Wb_m : sstate := ltac:(let x := eval vm_compute in (MEMO_51) in exact x).
Local Lemma MEMO_51_c : MEMO_51 = E_Wb_m. Proof. vm_cast_no_check (@eq_refl _ MEMO_51). Qed.
Local Lemma MEMO_51_e : ltac2:(tb__ "0|0|
S46S1aS11eS8fU1S83S11Z0A1S11Z50A1A5S82A3").
Proof. exact (@eq_trans _ (reframe_obj E_Wb_m1 1 B544 (SLit 0) (SLit 80)) MEMO_51 (E_Wb_m) (@eq_refl _ (reframe_obj E_Wb_m1 1 B544 (SLit 0) (SLit 80))) MEMO_51_c). Qed.
Lemma E_Wb_m_eq : ltac2:(tb__ "0|0|
S46S1aS11eS8fU1S83S11Z0A1S11Z50A1A5S82A3"). Proof. exact MEMO_51_e. Qed.
Lemma swf_E_Wb_m : swf E_Wb_m = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Definition nl_addr : Z := ltac:(let x := eval vm_compute in (match reg_sv E_fx2b 10 with SLit a => a | _ => 0 end) in exact x).
Definition O_nlr : sobj := ltac2:(tb__ "0|0|
S1bS11SceA1S11Z0A1S11Z1A1S2S12A1S32P6A1A5").
Lemma img_nl : ltac2:(tb__ "0|3|
S47S46S3S132Q8M0A1M1A1S3eS67S131Q40SceA2M2A2S5G1S131G0ZaA2A2A3S46S9S40S67G2A2S7A3A2").
Proof. split; [vm_cast_no_check (@eq_refl _ (Some (Z_to_bv 8 10))) | vm_cast_no_check (@eq_refl _ true)]. Qed.
Lemma norl6_wb : state_has_rl 6 E_Wb_m = false. Proof. vm_cast_no_check (@eq_refl _ false). Qed.
Local Definition MEMO_52 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S6dS82S0S18Sc9S2S18A1A3S1cS82A1A3").
Definition E_Wb_c0 : sstate := ltac:(let x := eval vm_compute in (MEMO_52) in exact x).
Local Lemma MEMO_52_c : MEMO_52 = E_Wb_c0. Proof. vm_cast_no_check (@eq_refl _ MEMO_52). Qed.
Local Lemma MEMO_52_e : ltac2:(tb__ "0|0|
S46S1aS6dS82S0S18Sc9S2S18A1A3S1cS82A1A3Sb0A3").
Proof. exact (@eq_trans _ (app_objs E_Wb_m [O_nlr] (ss_next E_Wb_m)) MEMO_52 (E_Wb_c0) (@eq_refl _ (app_objs E_Wb_m [O_nlr] (ss_next E_Wb_m))) MEMO_52_c). Qed.
Lemma E_Wb_c0_eq : ltac2:(tb__ "0|0|
S46S1aS6dS82S0S18Sc9S2S18A1A3S1cS82A1A3Sb0A3"). Proof. exact MEMO_52_e. Qed.
Lemma swf_E_Wb_c0 : swf E_Wb_c0 = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma E_Wb_nexts : ltac2:(tb__ "0|1|
S47S46S43S1cS82A1S1cS77A1M0A3S47S46S43S1cS88A1G0A3S46S43S1cS8fA1G0A3A2A2").
Proof. repeat split; reflexivity. Qed.
Definition xs_wb2 : list xform := ltac2:(tb__ "0|2|
S0S61S63U0M0S11N4a8A1A2S0S61S63G0S11N4c8A1A2S0S61S63UaM1S11Z29e0cA1A2S0S61S63G1S11Z29e08A1A2S2S61A1A3A3A3A3").
Local Definition MEMO_53 := apply_xforms E_Wb_c0 xs_wb2.
Local Definition MEMO_53__f := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast E_Wb_c0 xs_wb2.
Definition E_Wb_c : sstate := ltac:(let x := eval vm_compute in (xget E_Wb_c0 (MEMO_53__f)) in exact x).
Local Lemma MEMO_53_c : MEMO_53 = Some E_Wb_c. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_memo MEMO_53 MEMO_53__f. Qed.
Local Lemma MEMO_53_e : ltac2:(tb__ "0|0|
S46S3S1aA1S62Sb0SdeA2S5S1aS78A2A3").
Proof. exact (@eq_trans _ (apply_xforms E_Wb_c0 xs_wb2) MEMO_53 (Some E_Wb_c) (@eq_refl _ (apply_xforms E_Wb_c0 xs_wb2)) MEMO_53_c). Qed.
Lemma xs_wb2_ok : ltac2:(tb__ "0|0|
S46S3S1aA1S62Sb0SdeA2S5S1aS78A2A3"). Proof. exact MEMO_53_e. Qed.
Definition s_wb : wsub := ltac2:(tb__ "0|14|
S0SaS43S14A2M0S1S43S14PcM1S17S48S16P1A1M2S11N230A1A3M3A4S0G0S1S43S14PdM4S11Z50A1A4S0G0S1S43S14PeM5S11Z105ffA1M6A4S0G0S1S43S14PfS11Z1A1M7A4M8S0G0S1S43S14G5G2A4S0G0S1S43S14G4S11N4a8A1A4S0G0S1S43S14G1G2A4S0G0S1S43S14P5bS11Z0A1M9A4S0G0S1S43S14P5aG9A4S0G0S1S43S14P59G9A4S0G0S1S43S14P58G9A4S0G0S1S43S14P57G9A4S0G0S1S43S14P56G9A4S0G0S1S43S14P55MaG9A4S0G0S1S43S14P54MbG9A4S0G0S1S43S14P53McG9A4S0G0S1S43S14P52MdG9A4S0G0S1S43S14P51G9A4S0G0S1S43S14P50MeG9A4S0G0S1S43S14P4fMfG9A4S0G0S1S43S14P4eM10G9A4S0G0S1S43S14P4dG9A4S0G0S1S43S14P4cG9A4S0G0S1S43S14P4bG9A4S0G0S1S43S14P4aG9A4S0G0S1S43S14P49M11G9A4S0G0S1S43S14P48G9A4S0G0S1S43S14P47M12G9A4S0G0S1S43S14P46G9A4S0G0S1S43S14P45G9A4S0G0S1S43S14P44G9A4S0G0S1S43S14P43G9A4S0G0S1S43S14P42G9A4S0G0S1S43S14P41G9A4S0G0S1S43S14P40G9A4S0G0S1S43S14P3fG9A4S0G0S1S43S14P3eG9A4S0G0S1S43S14P3dG9A4S0G0S1S43S14P3cG9A4S0G0S1S43S14P33S16GaA1A4S0G0S1S43S14P32S16GbA1A4S0G0S1S43S14P31S16GcA1A4S0G0S1S43S14P30S16GdA1A4S0G0S1S43S14P2fS16P1cA1M13A4S0G0S1S43S14P2eG7A4S0G0S1S43S14P2dG13A4S0G0S1S43S14P2cG9A4S0G0S1S43S14P2bG6A4S0G0S1S43S14P29S11Z5a338A1A4S0G0S1S43S14P28S11Z29d90A1A4S0G0S1S43S14P24S16GeA1A4S0G0S1S43S14P23S16GfA1A4S0G0S1S43S14P22S16G10A1A4S0G0S1S43S14P21S17S51S17S48S17S48G2S11N21fA1A3G13A3G3A3A4S0G0G8S0G0S1S43S14P1bS16G11A1A4S0G0S1S43S14P1aS11Z22224A1A4S0G0S1S43S14P19S16G12A1A4S0G0S1S43S14P18S11Z3a0d0A1A4S0G0S1S43S14PaS17S48G2S11N4d0A1A3A4S0G0S1S43S14P15S11Z22c0cA1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Local Definition MEMO_54 : ltac2:(tb__ "0|0|
S3S4S18A1A1") := ltac2:(tb__ "0|0|
S104S78S69S7dA3").
Definition R_wb : list sobj := ltac:(let x := eval vm_compute in (match MEMO_54 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_54_c : MEMO_54 = Some R_wb. Proof. vm_cast_no_check (@eq_refl _ MEMO_54). Qed.
Local Lemma MEMO_54_e : ltac2:(tb__ "0|1|
S46S3S4S18A1M0A1S104S78S69S7dA3S5G0Sa1A2A3").
Proof. exact (@eq_trans _ (entails_fr E_Wb_c Pre_wl2 s_wb) MEMO_54 (Some R_wb) (@eq_refl _ (entails_fr E_Wb_c Pre_wl2 s_wb)) MEMO_54_c). Qed.
Lemma efr_wb : ltac2:(tb__ "0|1|
S46S3S4S18A1M0A1S104S78S69S7dA3S5G0Sa1A2A3"). Proof. exact MEMO_54_e. Qed.
Lemma chk_wb : ltac2:(tb__ "0|0|
S46S9S10aS78S69S7dSa1S0S56S57S68S5aA2S2S56A1A3A5S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_wb : ltac2:(tb__ "0|0|
S46S9S10dS15S2dS1cS78A1A1S20S77A1A3S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma facts_wbc : ltac2:(tb__ "0|0|
S46S4S15A1S20S78A1S20S77A1A3"). Proof. reflexivity. Qed.
Lemma s_wb_vals : ltac2:(tb__ "0|0|
S47S46S14S101S7dPcA2S83A3S47S46S14S101S7dPdA2S11Z50A1A3S47S46S14S101S7dPeA2S11SceA1A3S46S14S101S7dPfA2S11Z1A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_55 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S109S7dP5cS68S1cS78A1Sa1A5").
Definition T_Dbi : sstate := ltac:(let x := eval vm_compute in (MEMO_55) in exact x).
Local Lemma MEMO_55_c : MEMO_55 = T_Dbi. Proof. vm_cast_no_check (@eq_refl _ MEMO_55). Qed.
Local Lemma MEMO_55_e : ltac2:(tb__ "0|0|
S46S1aS109S7dP5cS68S1cS78A1Sa1A5SbaA3").
Proof. exact (@eq_trans _ (import_post s_wb 92 D (ss_next E_Wb_c) R_wb) MEMO_55 (T_Dbi) (@eq_refl _ (import_post s_wb 92 D (ss_next E_Wb_c) R_wb)) MEMO_55_c). Qed.
Lemma T_Dbi_eq : ltac2:(tb__ "0|0|
S46S1aS109S7dP5cS68S1cS78A1Sa1A5SbaA3"). Proof. exact MEMO_55_e. Qed.
Definition T_Db : sstate := ltac:(let x := eval vm_compute in (add_facts (ss_facts E_Wb) T_Dbi) in exact x).
Lemma xs_db_ok : ltac2:(tb__ "0|0|
S46S3S1aA1S62SffS20S77A1SbaA2S2S61A1A2S5S1aSabA2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma fb_db : ltac2:(tb__ "0|0|
S46S9S10dS15S2dS1cSbaA1A1S20S77A1A3S7A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.

Local Definition MEMO_56 : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S58S67S6aS2S44A1SabS7A5").
Local Definition MEMO_56__f : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S119S67S6aS2S44A1SabS7A5").
Definition E_Wz : sstate := ltac:(let x := eval vm_compute in (lf0 T_Db (MEMO_56__f) 0) in exact x).
Local Lemma MEMO_56_c : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1SedS5G0S0S56S57S6bS59A2S2S56A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_56 MEMO_56__f. Qed.
Local Lemma MEMO_56_e : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS2S44A1SabS7A5S5G0S0S56S57S6bS59A2S2S56A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T_Db true) MEMO_56 (Some [mkLeaf E_Wz RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T_Db true)) MEMO_56_c). Qed.
Lemma run_db : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS2S44A1SabS7A5S5G0S0S56S57S6bS59A2S2S56A1A3A2A3").
Proof. exact MEMO_56_e. Qed.

Definition ozi : nat := ltac2:(tb__ "0|0|
U5").
Lemma cert_wz : ltac2:(tb__ "0|6|
S47S46S3S4eA1S5cS67S2fS6bA1A2S5S4eS52A2A3S47S46S14S28S6bZ11A2S11Z42A1A3S47S46S14S28S6bZaA2S11Z2A1A3S47S46S14S28S6bZcA2S11Z1A1A3S47S46S14S28S6bZbA2S17S48S16P1A1M0S11N298A1M1A3A3S47S46S3S18A1S10eS18S23S6bA1Sd2A3S5S18S6cS6bSd2A2M2A2A3S47S46S14S33G2A1G0A3S47S46S9S10fS12S106S13G1Z8M3S11Z0A1M4A3A1S2aG2A1M5A3S7A3S46S9S10fS12S106S13S11N290A1G3G4A3A1G5A3S7A3A2A2A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_57 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S127S6bS11Z0A1S23S6bA1S1cS6bA1A4").
Definition PZ : sstate := ltac:(let x := eval vm_compute in (MEMO_57) in exact x).
Local Lemma MEMO_57_c : MEMO_57 = PZ. Proof. vm_cast_no_check (@eq_refl _ MEMO_57). Qed.
Local Lemma MEMO_57_e : ltac2:(tb__ "0|0|
S46S1aS127S6bS11Z0A1S23S6bA1S1cS6bA1A4S9cA3").
Proof. exact (@eq_trans _ (S_after E_Wz (SLit 0) (ss_objs E_Wz) (ss_next E_Wz)) MEMO_57 (PZ) (@eq_refl _ (S_after E_Wz (SLit 0) (ss_objs E_Wz) (ss_next E_Wz))) MEMO_57_c). Qed.
Lemma PZ_eq : ltac2:(tb__ "0|0|
S46S1aS127S6bS11Z0A1S23S6bA1S1cS6bA1A4S9cA3"). Proof. exact MEMO_57_e. Qed.
Local Definition MEMO_58 : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S58S67S6aS2S44A1S9cS7A5").
Local Definition MEMO_58__f : ltac2:(tb__ "0|0|
S3S4S56A1A1") := ltac2:(tb__ "0|0|
S119S67S6aS2S44A1S9cS7A5").
Definition E_exb : sstate := ltac:(let x := eval vm_compute in (lf0 PZ (MEMO_58__f) 0) in exact x).
Local Lemma MEMO_58_c : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1SeeS5G0S0S56S57S99S59A2S2S56A1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MEMO_58 MEMO_58__f. Qed.
Local Lemma MEMO_58_e : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS2S44A1S9cS7A5S5G0S0S56S57S99S59A2S2S56A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] PZ true) MEMO_58 (Some [mkLeaf E_exb RsEcall]) (@eq_refl _ (sym_run segs FUEL [] PZ true)) MEMO_58_c). Qed.
Lemma run_pz : ltac2:(tb__ "0|1|
S46S3S4S56A1M0A1S58S67S6aS2S44A1S9cS7A5S5G0S0S56S57S99S59A2S2S56A1A3A2A3").
Proof. exact MEMO_58_e. Qed.
Lemma cert_exb : ltac2:(tb__ "0|0|
S47S46S3S4eA1S5cS67S2fS99A1A2S5S4eS52A2A3S47S46S14S28S99Z11A2S11Z5eA1A3S46S14S28S99ZaA2S11Z2A1A3A2A2").
Proof. repeat split; reflexivity. Qed.
End Drv_copen_states.

Module Drv_copen_chk2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G1.Drv_copen_states.

Lemma check_range_1 : check_range 1 0 64 = true.
Proof. unfold check_range, check_nr. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.fast_forallb. Qed.
End Drv_copen_chk2.

Module Drv_copen_chk1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G1.Drv_copen_states.

Lemma check_range_0 : check_range 0 0 64 = true.
Proof. unfold check_range, check_nr. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.fast_forallb. Qed.
End Drv_copen_chk1.

Module Drv_copen_chk3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G1.Drv_copen_states.

Lemma check_range_2 : check_range 2 0 64 = true.
Proof. unfold check_range, check_nr. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.fast_forallb. Qed.
End Drv_copen_chk3.
