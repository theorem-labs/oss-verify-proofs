(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the cannot-open path per CONFIG_RSEQ: each state of the path made in the build from the open-error state for both values of the flag, and each check of the path stated for both values). *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "option"; "list"; "Some"; "nat"; "true"; "false"; "bool"; "prod"; "andb"; "None"; "app"; "fst"; "negb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "mkCell"; "sv"; "sprop"; "SVar"; "SAlu"; "sobj"; "SPUle"; "sstate"; "mkObj"; "ss_next"; "DUnknown"; "SExt"; "DList"; "ss_facts"; "SPBranch"; "SPAlign"; "ss_objs"; "SPNot"; "DImage"; "SLBytes"; "SPUlt"; "reg_sv"; "mkSS"; "ob_cells"; "ob_hi"; "ob_lo"; "sprop_below"; "ob_dflt"; "ss_pc"; "SPEq"; "FcsrFrm0"; "DRom"; "ob_base"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "sv_eqb"; "dflt_writable"; "is_arr"; "ss_lenient"; "c_off"; "c_width"; "image_byte"; "obj_wf"; "ro_addr"; "sprop_eqb"; "swf"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_OR"; "ALU_SRL"; "BC_NE"; "ALU_SUB"; "instr"; "BC_EQ"; "BC_LTU"; "ALU_XOR"; "Ecall"; "ALU_AND"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "sym_run"; "RsEcall"; "RsCut"; "list_set"; "instr_at"; "lf_state"; "sv_equiv"; "RsFuel"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "XSplit"; "XMerge"; "XSelect"; "XRebase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Musl_wl__G1.Musl_wl_err.WLerrS"; "segs"; "D"; "Pre_wl2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_copen__G1.Drv_copen_states"; "FUEL"; "E_Wz"; "obj"; "app_objs"; "E_W2"; "E_fxA"; "T_cs"; "E_W1"; "E_W2r"; "E_W2r1"; "E_W1c"; "E_W2c"; "E_Wa_c"; "E_Wb"; "E_Wb_c"; "E_cs"; "s_w1"; "s_w2"; "s_wa"; "s_wb"; "E_Wa"; "E_csX"; "E_W1r"; "E_Wa_m"; "E_Wb_m"; "B544"; "E_W2c1"; "E_W2s"; "E_Wa_l1"; "E_Wa_x"; "E_Wb_x"; "S_co0"; "drop_last"; "lastobj"; "s_cs"; "E_W1x"; "E_Wa_m2"; "E_Wb_m1"; "E_fx0"; "E_fx2a"; "E_fx2b"; "LOnl"; "S_coR"; "T_D1i"; "T_D2i"; "T_imp"; "E_exa"; "E_exb"; "E_exit"; "O_emp"; "PZ"; "R_cs"; "R_w1"; "R_w2"; "R_wa"; "R_wb"; "S_co"; "T_D1"; "T_D2"; "E_W1l"; "E_Wa_l"; "E_Wa_m1"; "E_Wb_l"; "E_fx"; "T_Da"; "T_Db"; "E_W2c0"; "E_Wa1"; "E_Wa2"; "E_Wa_c0"; "E_Wb_c0"; "E_fxX"; "E_po2"; "E_po62"; "E_po63"; "LENa"; "O_str1"; "S_cow"; "T64"; "T_Dai"; "T_Dbi"; "Tsm"; "xs_d1"; "xs_d2"; "xs_post"; "BL_co"; "E_Wa_r"; "E_Wb_r"; "E_fxW"; "E_po"; "HInl"; "IOVa"; "IOVb"; "O_arg1"; "O_nl"; "O_nlr"; "R_gen"; "T_cs1"; "X_ovf"; "X_ovfS"; "nl_addr"; "F_co"; "F_n"; "check_pre"; "ozi"; "s_nr"; "xs_co"; "xs_fx"; "xs_po"; "xs_pre"; "xs_w1"; "xs_w2"; "xs_w2s"; "xs_wa1"; "xs_wa2"; "xs_wb1"; "xs_wb2"; "BLn"; "C0_nr"; "FUELm"; "MEMO_10"; "MEMO_18"; "MEMO_28"; "MEMO_29"; "MEMO_30"; "MEMO_33"; "MEMO_34"; "MEMO_35"; "MEMO_36"; "MEMO_47"; "MEMO_5"; "MEMO_56"; "MEMO_58"; "a70r"; "check_core"; "check_nr"; "diff_in_ok"; "diff_out_ok"; "ids_below71"; "po_fresh"; "po_regs"; "post_loc"; "pre_loc"; "setbase"; "sobj_eqb"; "the_pre"; "upd_cell"; "wpos_off"; "xs_c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get";
"sv_subst"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "entails"; "cell_eqb"; "dummy_obj"; "odefault_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_post"; "call_check"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_copen__G1.Drv_copen_states.CAddr"; "fwritex_entry"; "ret_out"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "existsb"; "In"; "fold_left"; "removelast"; "tl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "cells_bytes"; "BLit"; "BSrc"; "bexp_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "list_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue"; "merge_lists"; "reframe_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.StrAddr"; "strnlen_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Str_strnlen"; "Pre_strnlen"; "P_strnlen"; "Posts_strnlen"; "@Corelib.Lists.ListDef"; "map"; "nth"; "seq"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "state_has_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast"; "apply_xforms_fast"; "@Stdlib.ZArith.BinInt.Z"; "of_nat"; "sub"; "to_nat"; "add"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1.Drv_open_states"; "S_operr"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@Stdlib.PArith.BinPos.Pos"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
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
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Str_memchr.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Str_strnlen.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Musl_wl__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Drv_copen_states.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvGlue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Str_memchr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Str_strnlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1.Drv_open_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Musl_wl__G1.Musl_wl_err.
Import ListNotations.

Import StrAddr.
Import WLerrS.
Close Scope bv_scope.
Open Scope Z_scope.

Module CAddr.
  Definition fwritex_entry : Z := 0x21eb4.
  Definition ret_out : Z := 0x22eec.
  Definition exit_ecall : Z := 0x1fa10.
  Definition stderr_file : Z := 0x29650.
End CAddr.
Import CAddr.

(* LPS 727298f3: the open-error state [S_operr r] depends on the run's CONFIG_RSEQ flag [r], so every
   state of the cannot-open path below is made per value of [r], in the build, from [S_operr false] and
   [S_operr true] ([X_0], [X_1], [X r := if r then X_1 else X_0]); each check is stated for all [r] and
   proved after the flag is destructed. *)
Local Notation axf := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast (only parsing).
Local Notation srf := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.sym_run_fast (only parsing).
Local Ltac fast_lit_ := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit.
Local Ltac run_cast_ := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast.

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

(* The facts the strnlen call starts from: the tail holds argv[1] and at least [N + 10] bytes
   (Lib/DrvTail1.v [L3_ge]; it was [N + 17] with the random bytes at its end), so argv[1] and those ten
   bytes end below the stack window's top, [2 ^ 47]. *)
Definition F_co : list sprop :=
  [SPUle (SAlu ALU_ADD (SVar 28) (SLit 10)) (SVar 27); SPUle (SVar 27) (SLit 4194304);
   SPUle (SVar 28) (SLit 131071); SPUle (SAlu ALU_ADD (SVar 25) (SVar 28)) (SLit 140737488355318)].
Definition O_str1 : sobj := ltac2:(tb__ "0|0|
S1bS16P19A1S11Z0A1S16P1bA1S2S12A1S1fP3A1A5").

Definition xs_co : list xform := ltac2:(tb__ "0|0|
S0S61S65S0S6U0S0S6U1S0S6U2S0S6U3S0S6U4S0S6U6S0S6U7S0S6U5S2S6A1A3A3A3A3A3A3A3A3A1S2S61A1A3").
Definition S_co0_0 : sstate := Eval vm_compute in xget (S_operr false) (axf (S_operr false) xs_co).
Definition S_co0_1 : sstate := Eval vm_compute in xget (S_operr true) (axf (S_operr true) xs_co).
Definition S_co0 (r : bool) : sstate := if r then S_co0_1 else S_co0_0.
Lemma xs_co_ok : forall r, apply_xforms (S_operr r) xs_co = Some (S_co0 r).
Proof. intros [|]; fast_lit_. Qed.

Definition S_coR_0 : sstate := Eval vm_compute in drop_last (S_co0 false).
Definition S_coR_1 : sstate := Eval vm_compute in drop_last (S_co0 true).
Definition S_coR (r : bool) : sstate := if r then S_coR_1 else S_coR_0.
Lemma S_coR_eq : forall r, drop_last (S_co0 r) = S_coR r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma S_co0_objs : forall r, ss_objs (S_co0 r) = ss_objs (S_coR r) ++ [lastobj (S_co0 r)].
Proof. intros [|]; reflexivity. Qed.
Lemma swf_S_coR : forall r, swf (S_coR r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.

Lemma last_co0 : forall r,
  lastobj (S_co0 r) = mkObj (SVar 6) (SLit 0) (SLit 16) [mkCell (SLit 0) 8 (SVar 9); mkCell (SLit 8) 8 (SVar 10)] DUnknown.
Proof. intros [|]; reflexivity. Qed.
Lemma S_coR_next : forall r, ss_next (S_coR r) = 27%positive /\ ss_next (S_co0 r) = 27%positive.
Proof. intros [|]; split; reflexivity. Qed.

Definition S_cow_0 : sstate := Eval vm_compute in app_objs (S_coR false) [O_str1] 29.
Definition S_cow_1 : sstate := Eval vm_compute in app_objs (S_coR true) [O_str1] 29.
Definition S_cow (r : bool) : sstate := if r then S_cow_1 else S_cow_0.
Lemma S_cow_eq : forall r, app_objs (S_coR r) [O_str1] 29 = S_cow r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma swf_S_cow : forall r, swf (S_cow r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma norl3_S_coR : forall r, state_has_rl 3 (S_coR r) = false.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ false). Qed.
Definition S_co_0 : sstate := Eval vm_compute in add_facts F_co (S_cow false).
Definition S_co_1 : sstate := Eval vm_compute in add_facts F_co (S_cow true).
Definition S_co (r : bool) : sstate := if r then S_co_1 else S_co_0.
Lemma S_co_eq : forall r, add_facts F_co (S_cow r) = S_co r.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Definition E_cs_0 : sstate := Eval vm_compute in lf0 (S_co false) (srf segs FUEL [strnlen_entry] (S_co false) true) 0.
Definition E_cs_1 : sstate := Eval vm_compute in lf0 (S_co true) (srf segs FUEL [strnlen_entry] (S_co true) true) 0.
Definition E_cs (r : bool) : sstate := if r then E_cs_1 else E_cs_0.
Lemma run_co : forall r, sym_run segs FUEL [strnlen_entry] (S_co r) true = Some [mkLeaf (E_cs r) RsCut].
Proof. intros [|]; run_cast_. Qed.

Definition xs_pre : list xform := ltac2:(tb__ "0|1|
S0S61S63U0M0S11N460A1A2S0S61S63G0S11N480A1A2S2S61A1A3A3").
Definition E_csX_0 : sstate := Eval vm_compute in xget (E_cs false) (axf (E_cs false) xs_pre).
Definition E_csX_1 : sstate := Eval vm_compute in xget (E_cs true) (axf (E_cs true) xs_pre).
Definition E_csX (r : bool) : sstate := if r then E_csX_1 else E_csX_0.
Lemma xs_pre_ok : forall r, apply_xforms (E_cs r) xs_pre = Some (E_csX r).
Proof. intros [|]; fast_lit_. Qed.
Definition s_cs_0 : wsub := Eval vm_compute in (16%positive, SVar 28) :: (17%positive, SVar 27) :: infer_sub 10 (E_csX false) Pre_strnlen.
Definition s_cs_1 : wsub := Eval vm_compute in (16%positive, SVar 28) :: (17%positive, SVar 27) :: infer_sub 10 (E_csX true) Pre_strnlen.
Definition s_cs (r : bool) : wsub := if r then s_cs_1 else s_cs_0.
Definition R_cs_0 : list sobj := Eval vm_compute in match entails_fr (E_csX false) Pre_strnlen (s_cs false) with Some R => R | None => [] end.
Definition R_cs_1 : list sobj := Eval vm_compute in match entails_fr (E_csX true) Pre_strnlen (s_cs true) with Some R => R | None => [] end.
Definition R_cs (r : bool) : list sobj := if r then R_cs_1 else R_cs_0.
Lemma efr_cs : forall r, entails_fr (E_csX r) Pre_strnlen (s_cs r) = Some (R_cs r).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma chk_cs : forall r, call_check (E_csX r) Pre_strnlen (s_cs r) (R_cs r) Posts_strnlen = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_cs : forall r, forallb (sprop_below (ss_next (E_csX r))) (ss_facts (E_cs r)) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_cs_16 : forall r, wsub_get (s_cs r) 16 = SVar 28.
Proof. intros [|]; reflexivity. Qed.
Definition T_imp_0 : sstate := Eval vm_compute in import_post (s_cs false) NF P_strnlen (ss_next (E_csX false)) (R_cs false).
Definition T_imp_1 : sstate := Eval vm_compute in import_post (s_cs true) NF P_strnlen (ss_next (E_csX true)) (R_cs true).
Definition T_imp (r : bool) : sstate := if r then T_imp_1 else T_imp_0.
Lemma T_imp_eq : forall r, import_post (s_cs r) NF P_strnlen (ss_next (E_csX r)) (R_cs r) = T_imp r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition xs_post : list xform := ltac2:(tb__ "0|3|
S0S61S66U1M0A1S0S61S65S0S6U2S0S6G0S0S6U3S0S6U4S0S6U5S0S6U6S0S6U7S0S6U8S0S6U9S0S6U0M1S2S6A1A3A3A3A3A3A3A3A3A3A3A1S0S61S64G1A1M2S0S61G2S2S61A1A3A3A3A3").
Definition T_cs_0 : sstate := Eval vm_compute in xget (E_cs false) (axf (add_facts (ss_facts (E_cs false)) (T_imp false)) xs_post).
Definition T_cs_1 : sstate := Eval vm_compute in xget (E_cs true) (axf (add_facts (ss_facts (E_cs true)) (T_imp true)) xs_post).
Definition T_cs (r : bool) : sstate := if r then T_cs_1 else T_cs_0.
Lemma xs_post_ok : forall r, apply_xforms (add_facts (ss_facts (E_cs r)) (T_imp r)) xs_post = Some (T_cs r).
Proof. intros [|]; fast_lit_. Qed.
Lemma fb_cs2 : forall r, forallb (sprop_below (ss_next (T_imp r))) (ss_facts (E_cs r)) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.

Definition T_cs1 (r : bool) : sstate :=
  mkSS (ss_pc (T_cs r)) (list_set (ss_regs (T_cs r)) 10 (SVar 28)) (ss_fregs (T_cs r)) (ss_fcsr (T_cs r))
       (ss_resv (T_cs r)) (ss_objs (T_cs r)) (ss_facts (T_cs r)) (ss_next (T_cs r)) (ss_lenient (T_cs r)).
Lemma fact_T_cs : forall r, In (SPEq (SVar 69) (SVar 28)) (ss_facts (T_cs r)).
Proof. intros [|]; cbn; tauto. Qed.
Lemma diff_cs : forall r, state_diff (T_cs r) (T_cs1 r) = Some ([(SVar 69, SVar 28)], @nil sprop).
Proof. intros [|]; vm_cast_no_check (@eq_refl _ (Some ([(SVar 69, SVar 28)], @nil sprop))). Qed.
Lemma swf_T_cs1 : forall r, swf (T_cs1 r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma T_cs1_next : forall r, ss_next (T_cs1 r) = 70%positive.
Proof. intros [|]; reflexivity. Qed.

Definition T64 (r : bool) : sstate := add_facts [SPUle (SLit 64) (SVar 28)] (T_cs1 r).
Definition X_ovf_0 : sstate := Eval vm_compute in lf0 (T64 false) (srf segs FUEL [] (T64 false) true) 0.
Definition X_ovf_1 : sstate := Eval vm_compute in lf0 (T64 true) (srf segs FUEL [] (T64 true) true) 0.
Definition X_ovf (r : bool) : sstate := if r then X_ovf_1 else X_ovf_0.
Definition E_W1_0 : sstate := Eval vm_compute in lf0 (T64 false) (srf segs FUEL [] (T64 false) true) 1.
Definition E_W1_1 : sstate := Eval vm_compute in lf0 (T64 true) (srf segs FUEL [] (T64 true) true) 1.
Definition E_W1 (r : bool) : sstate := if r then E_W1_1 else E_W1_0.
Lemma run_64 : forall r,
  sym_run segs FUEL [] (T64 r) true = Some [mkLeaf (X_ovf r) RsEcall; mkLeaf (E_W1 r) RsEcall].
Proof. intros [|]; run_cast_. Qed.

Definition BNZ28 : sprop := ltac2:(tb__ "0|0|
S21S4cS1eS8Q8S26P3S16P1cA1Z1A3A3S11Z0A1A3").
Lemma fact_ovf : forall r, In BNZ28 (ss_facts (X_ovf r)).
Proof. intros [|]; cbn; tauto. Qed.
Lemma E_W1_next : forall r, ss_next (E_W1 r) = 70%positive.
Proof. intros [|]; reflexivity. Qed.

Definition xs_w1 : list xform := ltac2:(tb__ "0|2|
S0S61S63U0M0S11N21fA1A2S0S61S63G0S11N230A1A2S0S61S63G0S11N4a8A1A2S0S61S63G0S11N4c8A1A2S0S61S63U9M1S11Z296ccA1A2S0S61S63G1S11Z296c8A1A2S2S61A1A3A3A3A3A3A3").
Definition E_W1x_0 : sstate := Eval vm_compute in xget (E_W1 false) (axf (E_W1 false) xs_w1).
Definition E_W1x_1 : sstate := Eval vm_compute in xget (E_W1 true) (axf (E_W1 true) xs_w1).
Definition E_W1x (r : bool) : sstate := if r then E_W1x_1 else E_W1x_0.
Lemma xs_w1_ok : forall r, apply_xforms (E_W1 r) xs_w1 = Some (E_W1x r).
Proof. intros [|]; fast_lit_. Qed.

Definition BL_co : list bexp := ltac2:(tb__ "0|4|
S123S44S114S116S0S44Z63M0S0S44Z6cS0S44Z69S0S44Z3aS0S44Z20M1S0S44G0S0S44Z61S0S44Z6eM2S0S44G2S0S44Z6fM3S0S44Z74S0S44G1S0S44G3S0S44Z70S0S44Z65S0S44G2S0S44G1S2S44A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A4").
Lemma cb_w1 : forall r, cells_bytes (ob_cells (obj (E_W1x r) 3)) (SLit (-560)) 0 17 = Some BL_co.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ (Some BL_co)). Qed.
Lemma obj3_w1 : forall r,
  nth_error (ss_objs (E_W1x r)) 3 = Some (obj (E_W1x r) 3) /\ ob_lo (obj (E_W1x r) 3) = SLit (-560)
  /\ ob_hi (obj (E_W1x r) 3) = SLit (-543) /\ dflt_writable (ob_dflt (obj (E_W1x r) 3)) = true
  /\ is_arr (ob_dflt (obj (E_W1x r) 3)) = false.
Proof. intros [|]; repeat split; reflexivity. Qed.
Lemma norl5_w1 : forall r, state_has_rl 5 (E_W1x r) = false.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ false). Qed.
Definition E_W1l_0 : sstate := Eval vm_compute in obj_to_list (E_W1x false) 3 5.
Definition E_W1l_1 : sstate := Eval vm_compute in obj_to_list (E_W1x true) 3 5.
Definition E_W1l (r : bool) : sstate := if r then E_W1l_1 else E_W1l_0.
Lemma E_W1l_eq : forall r, obj_to_list (E_W1x r) 3 5 = E_W1l r.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Definition E_W1r_0 : sstate := Eval vm_compute in drop_last (E_W1l false).
Definition E_W1r_1 : sstate := Eval vm_compute in drop_last (E_W1l true).
Definition E_W1r (r : bool) : sstate := if r then E_W1r_1 else E_W1r_0.
Lemma E_W1r_eq : forall r, drop_last (E_W1l r) = E_W1r r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma E_W1l_objs : forall r, ss_objs (E_W1l r) = ss_objs (E_W1r r) ++ [O_str1].
Proof. intros [|]; reflexivity. Qed.
Lemma swf_E_W1r : forall r, swf (E_W1r r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma norl6_w1 : forall r, state_has_rl 6 (E_W1r r) = false.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ false). Qed.
Definition O_arg1 : sobj := ltac2:(tb__ "0|0|
S1bS16P19A1S11Z0A1S16P1cA1S2S12A1S32P6A1A5").
Definition E_W1c_0 : sstate := Eval vm_compute in app_objs (E_W1r false) [O_arg1] (ss_next (E_W1r false)).
Definition E_W1c_1 : sstate := Eval vm_compute in app_objs (E_W1r true) [O_arg1] (ss_next (E_W1r true)).
Definition E_W1c (r : bool) : sstate := if r then E_W1c_1 else E_W1c_0.
Lemma E_W1c_eq : forall r, app_objs (E_W1r r) [O_arg1] (ss_next (E_W1r r)) = E_W1c r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma swf_E_W1c : forall r, swf (E_W1c r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.

Definition s_w1 : wsub := ltac2:(tb__ "0|f|
S0SaS43S14A2M0S1S43S14PcM1S17S48S16P1A1M2S11N230A1A3M3A4S0G0S1S43S14PdM4S11Z11A1A4S0G0S1S43S14PeM5S16P19M6A1M7A4S0G0S1S43S14PfS16P1cA1M8A4M9S0G0S1S43S14G5G2A4S0G0S1S43S14G1G2A4S0G0S1S43S14G4G8A4S0G0S1S43S14P5bS11Z0A1MaA4S0G0S1S43S14P5aGaA4S0G0S1S43S14P59GaA4S0G0S1S43S14P58GaA4S0G0S1S43S14P57GaA4S0G0S1S43S14P56GaA4S0G0S1S43S14P55GaA4S0G0S1S43S14P54GaA4S0G0S1S43S14P53GaA4S0G0S1S43S14P52GaA4S0G0S1S43S14P51GaA4S0G0S1S43S14P50GaA4S0G0S1S43S14P4fGaA4S0G0S1S43S14P4eGaA4S0G0S1S43S14P4dGaA4S0G0S1S43S14P4cGaA4S0G0S1S43S14P4bGaA4S0G0S1S43S14P4aGaA4S0G0S1S43S14P49GaA4S0G0S1S43S14P48GaA4S0G0S1S43S14P47GaA4S0G0S1S43S14P46GaA4S0G0S1S43S14P45GaA4S0G0S1S43S14P44GaA4S0G0S1S43S14P43GaA4S0G0S1S43S14P42GaA4S0G0S1S43S14P41GaA4S0G0S1S43S14P40GaA4S0G0S1S43S14P3fGaA4S0G0S1S43S14P3eGaA4S0G0S1S43S14P3dGaA4S0G0S1S43S14P3cMbGaA4S0G0S1S43S14P33S16GbA1A4S0G0S1S43S14P32S16P3bA1A4S0G0S1S43S14P31S16P3aA1A4S0G0S1S43S14P30S16P39A1A4S0G0S1S43S14P2fG8A4S0G0S1S43S14P2eG8A4S0G0S1S43S14P2dMcG8A4S0G0S1S43S14P2cGaA4S0G0S1S43S14P2bG7A4S0G0S1S43S14P29S11Z59bf8A1A4S0G0S1S43S14P28S11Z29650A1A4S0G0S1S43S14P24MdS16GcA1A4S0G0S1S43S14P23S11Z1A1A4S0G0S1S43S14P22MeGaA4S0G0S1S43S14P21S17S51S17S48G2S11N21fA1A3G3A3A4S0G0G9S0G0S1S43S14P1bS16GdA1A4S0G0S1S43S14P1aS11Z21ae4A1A4S0G0S1S43S14G6S16GeA1A4S0G0S1S43S14P18S11Z39990A1A4S0G0S1S43S14PaS17S48G2S11N4d0A1A3A4S0G0S1S43S14P15S11Z22eecA1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition R_w1_0 : list sobj := Eval vm_compute in match entails_fr (E_W1c false) Pre_wl2 s_w1 with Some R => R | None => [] end.
Definition R_w1_1 : list sobj := Eval vm_compute in match entails_fr (E_W1c true) Pre_wl2 s_w1 with Some R => R | None => [] end.
Definition R_w1 (r : bool) : list sobj := if r then R_w1_1 else R_w1_0.
Lemma efr_w1 : forall r, entails_fr (E_W1c r) Pre_wl2 s_w1 = Some (R_w1 r).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma chk_w1 : forall r, call_check (E_W1c r) Pre_wl2 s_w1 (R_w1 r) [mkLeaf D RsCut] = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_w1 : forall r, forallb (sprop_below (ss_next (E_W1c r))) (ss_facts (E_W1 r)) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma facts_w1c : forall r, ss_facts (E_W1c r) = ss_facts (E_W1 r).
Proof. intros [|]; reflexivity. Qed.
Lemma s_w1_vals : ltac2:(tb__ "0|0|
S47S46S14S101S7aPcA2S17S48S16P1A1S11N230A1A3A3S47S46S14S101S7aPdA2S11Z11A1A3S47S46S14S101S7aPeA2S16P19A1A3S46S14S101S7aPfA2S16P1cA1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Definition T_D1i_0 : sstate := Eval vm_compute in import_post s_w1 92 D (ss_next (E_W1c false)) (R_w1 false).
Definition T_D1i_1 : sstate := Eval vm_compute in import_post s_w1 92 D (ss_next (E_W1c true)) (R_w1 true).
Definition T_D1i (r : bool) : sstate := if r then T_D1i_1 else T_D1i_0.
Lemma T_D1i_eq : forall r, import_post s_w1 92 D (ss_next (E_W1c r)) (R_w1 r) = T_D1i r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition xs_d1 : list xform := ltac2:(tb__ "0|4|
S0S61S66U0M0A1S0S61S65S0S6U4S0S6G0S0S6U5S0S6U1S0S6U6S0S6U7M1S0S6U8S0S6U9S0S6UaS0S6UbS0S6U3S0S6UcS0S6UdS0S6U2S2S6A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S61S64G0A1M2S0S61G2S0S61S64G1A1M3S0S61G3S2S61A1A3A3A3A3A3A3").
Definition T_D1_0 : sstate := Eval vm_compute in xget (T_D1i false) (axf (add_facts (ss_facts (E_W1 false)) (T_D1i false)) xs_d1).
Definition T_D1_1 : sstate := Eval vm_compute in xget (T_D1i true) (axf (add_facts (ss_facts (E_W1 true)) (T_D1i true)) xs_d1).
Definition T_D1 (r : bool) : sstate := if r then T_D1_1 else T_D1_0.
Lemma xs_d1_ok : forall r, apply_xforms (add_facts (ss_facts (E_W1 r)) (T_D1i r)) xs_d1 = Some (T_D1 r).
Proof. intros [|]; fast_lit_. Qed.
Lemma fb_d1 : forall r, forallb (sprop_below (ss_next (T_D1i r))) (ss_facts (E_W1 r)) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.

Definition E_W2_0 : sstate := Eval vm_compute in lf0 (T_D1 false) (srf segs FUEL [] (T_D1 false) true) 0.
Definition E_W2_1 : sstate := Eval vm_compute in lf0 (T_D1 true) (srf segs FUEL [] (T_D1 true) true) 0.
Definition E_W2 (r : bool) : sstate := if r then E_W2_1 else E_W2_0.
Lemma run_d1 : forall r, sym_run segs FUEL [] (T_D1 r) true = Some [mkLeaf (E_W2 r) RsEcall].
Proof. intros [|]; run_cast_. Qed.

Definition xs_w2s : list xform := ltac2:(tb__ "0|0|
S0S61S65S0S6U0S0S6U2S0S6U3S0S6U4S0S6U5S0S6U6S0S6U7S0S6U8S0S6U1S0S6U9S2S6A1A3A3A3A3A3A3A3A3A3A3A1S2S61A1A3").
Definition E_W2s_0 : sstate := Eval vm_compute in xget (E_W2 false) (axf (E_W2 false) xs_w2s).
Definition E_W2s_1 : sstate := Eval vm_compute in xget (E_W2 true) (axf (E_W2 true) xs_w2s).
Definition E_W2s (r : bool) : sstate := if r then E_W2s_1 else E_W2s_0.
Lemma xs_w2s_ok : forall r, apply_xforms (E_W2 r) xs_w2s = Some (E_W2s r).
Proof. intros [|]; fast_lit_. Qed.
Definition E_W2r1_0 : sstate := Eval vm_compute in drop_last (E_W2s false).
Definition E_W2r1_1 : sstate := Eval vm_compute in drop_last (E_W2s true).
Definition E_W2r1 (r : bool) : sstate := if r then E_W2r1_1 else E_W2r1_0.
Lemma E_W2r1_eq : forall r, drop_last (E_W2s r) = E_W2r1 r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma E_W2s_objs : forall r, ss_objs (E_W2s r) = ss_objs (E_W2r1 r) ++ [lastobj (E_W2s r)].
Proof. intros [|]; reflexivity. Qed.
Lemma swf_E_W2r1 : forall r, swf (E_W2r1 r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Definition E_W2r_0 : sstate := Eval vm_compute in drop_last (E_W2r1 false).
Definition E_W2r_1 : sstate := Eval vm_compute in drop_last (E_W2r1 true).
Definition E_W2r (r : bool) : sstate := if r then E_W2r_1 else E_W2r_0.
Lemma E_W2r_eq : forall r, drop_last (E_W2r1 r) = E_W2r r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma E_W2r1_objs : forall r, ss_objs (E_W2r1 r) = ss_objs (E_W2r r) ++ [lastobj (E_W2r1 r)].
Proof. intros [|]; reflexivity. Qed.
Lemma swf_E_W2r : forall r, swf (E_W2r r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma norl_w2 : forall r, state_has_rl 5 (E_W2r r) = false /\ state_has_rl 6 (E_W2r r) = false.
Proof. intros [|]; split; vm_cast_no_check (@eq_refl _ false). Qed.

Lemma last_w2s : forall r, lastobj (E_W2s r) = mkObj (SVar 25) (SLit 0) (SVar 28) [] (DRom 6).
Proof. intros [|]; reflexivity. Qed.
Lemma last_w2r1 : forall r,
  lastobj (E_W2r1 r) = mkObj (SAlu ALU_ADD (SVar 1) (SLit (-560))) (SLit 0) (SLit 17) [mkCell (SLit 0) 1 (SLit 10)] (DList 5).
Proof. intros [|]; reflexivity. Qed.
Lemma cb_w2 : forall r, cells_bytes (ob_cells (lastobj (E_W2r1 r))) (SLit 0) 0 1 = Some [BLit 10].
Proof. intros [|]; vm_cast_no_check (@eq_refl _ (Some [BLit 10])). Qed.
Lemma wf_w2r1 : forall r, obj_wf (ss_next (E_W2r1 r)) (lastobj (E_W2r1 r)) = true.
Proof. intros [|]; reflexivity. Qed.
Lemma E_W2_next : forall r,
  ss_next (E_W2 r) = ss_next (E_W2r r) /\ ss_next (E_W2s r) = ss_next (E_W2r r) /\ ss_next (E_W2r1 r) = ss_next (E_W2r r).
Proof. intros [|]; repeat split; reflexivity. Qed.
Definition O_nl : sobj := ltac2:(tb__ "0|0|
S1bS17S48S16P1A1S11N230A1A3S11Z0A1S11Z1A1S2S12A1S1fP5A1A5").
Definition O_emp : sobj := ltac2:(tb__ "0|1|
S1bS11Z0A1M0G0G0S2S12A1S32P6A1A5").
Definition E_W2c1_0 : sstate := Eval vm_compute in app_objs (E_W2r false) [O_nl] (ss_next (E_W2r false)).
Definition E_W2c1_1 : sstate := Eval vm_compute in app_objs (E_W2r true) [O_nl] (ss_next (E_W2r true)).
Definition E_W2c1 (r : bool) : sstate := if r then E_W2c1_1 else E_W2c1_0.
Lemma E_W2c1_eq : forall r, app_objs (E_W2r r) [O_nl] (ss_next (E_W2r r)) = E_W2c1 r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma swf_E_W2c1 : forall r, swf (E_W2c1 r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Definition E_W2c0_0 : sstate := Eval vm_compute in app_objs (E_W2c1 false) [O_emp] (ss_next (E_W2c1 false)).
Definition E_W2c0_1 : sstate := Eval vm_compute in app_objs (E_W2c1 true) [O_emp] (ss_next (E_W2c1 true)).
Definition E_W2c0 (r : bool) : sstate := if r then E_W2c0_1 else E_W2c0_0.
Lemma E_W2c0_eq : forall r, app_objs (E_W2c1 r) [O_emp] (ss_next (E_W2c1 r)) = E_W2c0 r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma swf_E_W2c0 : forall r, swf (E_W2c0 r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Definition xs_w2 : list xform := ltac2:(tb__ "0|2|
S0S61S63U0M0S11N288A1A2S0S61S63G0S11N2a8A1A2S0S61S63U8M1S11Z296ccA1A2S0S61S63G1S11Z296c8A1A2S2S61A1A3A3A3A3").
Definition E_W2c_0 : sstate := Eval vm_compute in xget (E_W2c0 false) (axf (E_W2c0 false) xs_w2).
Definition E_W2c_1 : sstate := Eval vm_compute in xget (E_W2c0 true) (axf (E_W2c0 true) xs_w2).
Definition E_W2c (r : bool) : sstate := if r then E_W2c_1 else E_W2c_0.
Lemma xs_w2_ok : forall r, apply_xforms (E_W2c0 r) xs_w2 = Some (E_W2c r).
Proof. intros [|]; fast_lit_. Qed.
Definition s_w2 : wsub := ltac2:(tb__ "0|c|
S0SaS43S14A2M0S1S43S14PcM1S17S48S16P1A1M2S11N230A1A3M3A4S0G0S1S43S14PdM4S11Z1A1A4S0G0S1S43S14PeM5S11Z0A1M6A4S0G0S1S43S14PfG6A4M7S0G0S1S43S14G5G2A4S0G0S1S43S14G4S11N288A1A4S0G0S1S43S14G1G2A4S0G0S1S43S14P5bG6A4S0G0S1S43S14P5aG6A4S0G0S1S43S14P59G6A4S0G0S1S43S14P58M8G6A4S0G0S1S43S14P57G6A4S0G0S1S43S14P56G6A4S0G0S1S43S14P55G6A4S0G0S1S43S14P54G6A4S0G0S1S43S14P53G6A4S0G0S1S43S14P52G6A4S0G0S1S43S14P51G6A4S0G0S1S43S14P50G6A4S0G0S1S43S14P4fG6A4S0G0S1S43S14P4eG6A4S0G0S1S43S14P4dG6A4S0G0S1S43S14P4cG6A4S0G0S1S43S14P4bG6A4S0G0S1S43S14P4aG6A4S0G0S1S43S14P49G6A4S0G0S1S43S14P48G6A4S0G0S1S43S14P47G6A4S0G0S1S43S14P46G6A4S0G0S1S43S14P45G6A4S0G0S1S43S14P44G6A4S0G0S1S43S14P43G6A4S0G0S1S43S14P42G6A4S0G0S1S43S14P41G6A4S0G0S1S43S14P40G6A4S0G0S1S43S14P3fG6A4S0G0S1S43S14P3eG6A4S0G0S1S43S14P3dG6A4S0G0S1S43S14P3cM9G6A4S0G0S1S43S14P33S16G9A1A4S0G0S1S43S14P32S16P3bA1A4S0G0S1S43S14P31S16P3aA1A4S0G0S1S43S14P30S16P39A1A4S0G0S1S43S14P2fG6A4S0G0S1S43S14P2eG6A4S0G0S1S43S14P2dMaG6A4S0G0S1S43S14P2cG6A4S0G0S1S43S14P2bG6A4S0G0S1S43S14P29S11Z59bf8A1A4S0G0S1S43S14P28S11Z5a058A1A4S0G0S1S43S14P24MbS16GaA1A4S0G0S1S43S14P23G6A4S0G0S1S43S14P22G6A4S0G0S1S43S14P21S17S51S17S48G2S11N22fA1A3G3A3A4S0G0G7S0G0S1S43S14P1bS16GbA1A4S0G0S1S43S14P1aS11Z21ae4A1A4S0G0S1S43S14P19S16G8A1A4S0G0S1S43S14P18S11Z39990A1A4S0G0S1S43S14PaS17S48G2S11N2b0A1A3A4S0G0S1S43S14P15S11Z222fcA1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition R_w2_0 : list sobj := Eval vm_compute in match entails_fr (E_W2c false) Pre_wl2 s_w2 with Some R => R | None => [] end.
Definition R_w2_1 : list sobj := Eval vm_compute in match entails_fr (E_W2c true) Pre_wl2 s_w2 with Some R => R | None => [] end.
Definition R_w2 (r : bool) : list sobj := if r then R_w2_1 else R_w2_0.
Lemma efr_w2 : forall r, entails_fr (E_W2c r) Pre_wl2 s_w2 = Some (R_w2 r).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma chk_w2 : forall r, call_check (E_W2c r) Pre_wl2 s_w2 (R_w2 r) [mkLeaf D RsCut] = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_w2 : forall r, forallb (sprop_below (ss_next (E_W2c r))) (ss_facts (E_W2 r)) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma facts_w2c : forall r, ss_facts (E_W2c r) = ss_facts (E_W2 r).
Proof. intros [|]; reflexivity. Qed.
Lemma s_w2_vals : ltac2:(tb__ "0|1|
S47S46S14S101S7bPcA2S17S48S16P1A1S11N230A1A3A3S47S46S14S101S7bPdA2S11Z1A1A3S47S46S14S101S7bPeA2S11Z0A1M0A3S46S14S101S7bPfA2G0A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Definition T_D2i_0 : sstate := Eval vm_compute in import_post s_w2 92 D (ss_next (E_W2c false)) (R_w2 false).
Definition T_D2i_1 : sstate := Eval vm_compute in import_post s_w2 92 D (ss_next (E_W2c true)) (R_w2 true).
Definition T_D2i (r : bool) : sstate := if r then T_D2i_1 else T_D2i_0.
Lemma T_D2i_eq : forall r, import_post s_w2 92 D (ss_next (E_W2c r)) (R_w2 r) = T_D2i r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition xs_d2 : list xform := ltac2:(tb__ "0|4|
S0S61S66U0M0A1S0S61S65S0S6U4S0S6G0S0S6U5S0S6U1S0S6U6S0S6U7M1S0S6U8S0S6U9S0S6UaS0S6UbS0S6U3S0S6UcS0S6UdS0S6U2S2S6A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S61S64G0A1M2S0S61G2S0S61S64G1A1M3S0S61G3S2S61A1A3A3A3A3A3A3").
Definition T_D2_0 : sstate := Eval vm_compute in xget (T_D2i false) (axf (add_facts (ss_facts (E_W2 false)) (T_D2i false)) xs_d2).
Definition T_D2_1 : sstate := Eval vm_compute in xget (T_D2i true) (axf (add_facts (ss_facts (E_W2 true)) (T_D2i true)) xs_d2).
Definition T_D2 (r : bool) : sstate := if r then T_D2_1 else T_D2_0.
Lemma xs_d2_ok : forall r, apply_xforms (add_facts (ss_facts (E_W2 r)) (T_D2i r)) xs_d2 = Some (T_D2 r).
Proof. intros [|]; fast_lit_. Qed.
Lemma fb_d2 : forall r, forallb (sprop_below (ss_next (T_D2i r))) (ss_facts (E_W2 r)) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.

Definition E_exit_0 : sstate := Eval vm_compute in lf0 (T_D2 false) (srf segs FUEL [] (T_D2 false) true) 0.
Definition E_exit_1 : sstate := Eval vm_compute in lf0 (T_D2 true) (srf segs FUEL [] (T_D2 true) true) 0.
Definition E_exit (r : bool) : sstate := if r then E_exit_1 else E_exit_0.
Lemma run_d2 : forall r, sym_run segs FUEL [] (T_D2 r) true = Some [mkLeaf (E_exit r) RsEcall].
Proof. intros [|]; run_cast_. Qed.
Lemma cert_exit : forall r,
  instr_at segs (ss_pc (E_exit r)) = Some Ecall /\ reg_sv (E_exit r) 17 = SLit 94 /\ reg_sv (E_exit r) 10 = SLit 2.
Proof. intros [|]; repeat split; reflexivity. Qed.

Definition Tsm (r : bool) : sstate := add_facts [SPUle (SVar 28) (SLit 63)] (T_cs1 r).
Definition X_ovfS_0 : sstate := Eval vm_compute in lf0 (Tsm false) (srf segs FUEL [fwritex_entry] (Tsm false) true) 0.
Definition X_ovfS_1 : sstate := Eval vm_compute in lf0 (Tsm true) (srf segs FUEL [fwritex_entry] (Tsm true) true) 0.
Definition X_ovfS (r : bool) : sstate := if r then X_ovfS_1 else X_ovfS_0.
Definition E_fx0_0 : sstate := Eval vm_compute in lf0 (Tsm false) (srf segs FUEL [fwritex_entry] (Tsm false) true) 1.
Definition E_fx0_1 : sstate := Eval vm_compute in lf0 (Tsm true) (srf segs FUEL [fwritex_entry] (Tsm true) true) 1.
Definition E_fx0 (r : bool) : sstate := if r then E_fx0_1 else E_fx0_0.
Lemma run_sm : forall r,
  sym_run segs FUEL [fwritex_entry] (Tsm r) true = Some [mkLeaf (X_ovfS r) RsEcall; mkLeaf (E_fx0 r) RsCut].
Proof. intros [|]; run_cast_. Qed.
Lemma fact_ovfS : forall r, In BNZ28 (ss_facts (X_ovfS r)).
Proof. intros [|]; cbn; tauto. Qed.

Definition E_fx_0 : sstate := Eval vm_compute in lf0 (E_fx0 false) (srf segs FUEL [fwritex_entry] (E_fx0 false) true) 0.
Definition E_fx_1 : sstate := Eval vm_compute in lf0 (E_fx0 true) (srf segs FUEL [fwritex_entry] (E_fx0 true) true) 0.
Definition E_fx (r : bool) : sstate := if r then E_fx_1 else E_fx_0.
Lemma run_fx0 : forall r, sym_run segs FUEL [fwritex_entry] (E_fx0 r) true = Some [mkLeaf (E_fx r) RsCut].
Proof. intros [|]; run_cast_. Qed.
Lemma E_fx_next : forall r, ss_next (E_fx r) = 70%positive.
Proof. intros [|]; reflexivity. Qed.

Definition xs_fx : list xform := ltac2:(tb__ "0|2|
S0S61S63U0M0S11N1e0A1A2S0S61S63G0S11N21fA1A2S0S61S63G0S11N460A1A2S0S61S63G0S11N4a0A1A2S0S61S63U9M1S11Z29738A1A2S0S61S63G1S11Z29650A1A2S2S61A1A3A3A3A3A3A3").
Definition E_fxX_0 : sstate := Eval vm_compute in xget (E_fx false) (axf (E_fx false) xs_fx).
Definition E_fxX_1 : sstate := Eval vm_compute in xget (E_fx true) (axf (E_fx true) xs_fx).
Definition E_fxX (r : bool) : sstate := if r then E_fxX_1 else E_fxX_0.
Lemma xs_fx_ok : forall r, apply_xforms (E_fx r) xs_fx = Some (E_fxX r).
Proof. intros [|]; fast_lit_. Qed.

Definition nocells (o : sobj) : sobj := ltac2:(tb__ "0|0|
S1bS33Vo;A1S2cVo;A1S2bVo;A1S2S12A1S1dA5").
(* The two rules that forget the cells of objects 1 and 3 and then restate the loop's base pointer
   (variable 70) with its alignment fact. *)
Definition fxW_of (X : sstate) : sstate :=
  set_objs X (obj X 0 :: nocells (obj X 1) :: obj X 2 :: nocells (obj X 3) :: skipn 4 (ss_objs X)).
Definition fxA_of (W : sstate) : sstate :=
  mkSS (ss_pc W) (ss_regs W) (ss_fregs W) (ss_fcsr W) (ss_resv W) (ss_objs W)
       (SPAlign 70 2 :: ss_facts W) 71%positive false.
Definition E_fxW_0 : sstate := Eval vm_compute in fxW_of (E_fxX false).
Definition E_fxW_1 : sstate := Eval vm_compute in fxW_of (E_fxX true).
Definition E_fxW (r : bool) : sstate := if r then E_fxW_1 else E_fxW_0.
Lemma ent_fxW : forall r, entails (E_fxX r) (E_fxW r) [] = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Definition E_fxA_0 : sstate := Eval vm_compute in fxA_of (E_fxW false).
Definition E_fxA_1 : sstate := Eval vm_compute in fxA_of (E_fxW true).
Definition E_fxA (r : bool) : sstate := if r then E_fxA_1 else E_fxA_0.
Lemma diff_fxA : forall r, state_diff (E_fxW r) (E_fxA r) = Some (@nil (sv * sv), [SPAlign 70 2]).
Proof. intros [|]; vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), [SPAlign 70 2]))). Qed.
Lemma swf_E_fxA : forall r, swf (E_fxA r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma norl7_fxA : forall r, state_has_rl 7 (E_fxA r) = false.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ false). Qed.
Lemma E_fxA_next : forall r,
  ss_next (E_fxA r) = 71%positive /\ ss_next (E_fxX r) = 70%positive /\ ss_next (E_fxW r) = 70%positive.
Proof. intros [|]; repeat split; reflexivity. Qed.

Definition s_nr (n r : Z) : wsub := ltac2:(tb__ "0|1|
S0SaS43S14A2M0S1S43S14P1cS11Vn;A1A4S0G0S1S43S14P19S17S48S16P46A1S11Vr;A1A3A4S2G0A1A3A3").
Definition a70r (r : Z) : sv := ltac2:(tb__ "0|0|
S17S48S16P46A1S11Vr;A1A3").
Definition setbase (b : sv) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S1bVb;S2cVo;A1S2bVo;A1S2aVo;A1S2eVo;A1A5").

Definition F_n (n : Z) : sprop := SPUle (SLit (n + 10)) (SVar 27).
Definition C0_nr (rq : bool) (n r : Z) : sstate :=
  mkSS (ss_pc (E_fxA rq)) (list_set (list_set (ss_regs (E_fxA rq)) 10 (a70r r)) 11 (SLit n))
    (ss_fregs (E_fxA rq)) (ss_fcsr (E_fxA rq)) (ss_resv (E_fxA rq))
    (firstn 13 (ss_objs (E_fxA rq)) ++ [setbase (a70r r) (obj (E_fxA rq) 13)])
    (F_n n :: ss_facts (E_fxA rq)) (ss_next (E_fxA rq)) false.
Definition xs_c (n : Z) : list xform := ltac2:(tb__ "0|0|
S0S61S63U3S11S12cVn;Z21fA2A1A2S2S61A1A3").

Definition pre_loc (C : sstate) : sstate := ltac2:(tb__ "0|0|
S60VC;S0S18S6cVC;U1A2S0S18S6cVC;U3A2S0S18S6cVC;U4A2S0S18S6cVC;UeA2S0S18S6cVC;UbA2S2S18A1A3A3A3A3A3A2").

Definition sobj_eqb (o o' : sobj) : bool := ltac2:(tb__ "0|0|
SbSbSbSbS38S33Vo;A1S33Vo';A1A2S38S2cVo;A1S2cVo';A1A2A2S38S2bVo;A1S2bVo';A1A2A2S11cS12S106S2aVo;A1S2aVo';A1A4A2S108S2eVo;A1S2eVo';A1A2A2").

Definition R_gen_0 : list sobj := Eval vm_compute in map (obj (E_fxA false)) [0;2;4;5;6;7;8;9;11;12]%nat.
Definition R_gen_1 : list sobj := Eval vm_compute in map (obj (E_fxA true)) [0;2;4;5;6;7;8;9;11;12]%nat.
Definition R_gen (r : bool) : list sobj := if r then R_gen_1 else R_gen_0.
Definition FUELm : nat := 3000%nat.

Definition upd_cell (off : Z) (v : sv) (o : sobj) : sobj := ltac2:(tb__ "0|3|
S1bS33Vo;A1S2cVo;A1S2bVo;A1S123S12S12S12S14S12Lx;S3cR1A1S44S9S12L_;S12fR1Voff;A2S13S3cR2A1S3dR2A1Vv;A3R2X9x2Lo';S43R2Li;S54S14S14R4Lb;La;M0Lop;M1G1S55G0Lop;M2G2S9S45S14R4La;Lw;Lsgn;S43S14S44R4Lk;Li;Ll;X14x8Lc;S2aVo;A1A4S2eVo;A1A5").
Definition po_fresh : list (nat * positive) := ltac2:(tb__ "0|1|
S0SaS6S43A2M0S1S6S43U5P47A4S0G0S1S6S43U6P48A4S0G0S1S6S43U7P49A4S0G0S1S6S43UaP4aA4S0G0S1S6S43UbP4bA4S0G0S1S6S43UcP4cA4S0G0S1S6S43UdP4dA4S0G0S1S6S43UeP4eA4S0G0S1S6S43UfP4fA4S0G0S1S6S43U10P50A4S0G0S1S6S43U11P51A4S0G0S1S6S43U1cP52A4S0G0S1S6S43U1dP53A4S0G0S1S6S43U1eP54A4S0G0S1S6S43U1fP55A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition po_regs (regs : list sv) : list sv := ltac2:(tb__ "0|2|
S5bS14S111S4S14A1M0SaS6S43A2M1G0G1S5bS14R2SeS6S43R1A3S16S10S6S43R1A3A1A4Liv;Lrs;Sf5Vregs;A5U1S11S10cA1A4").
Definition wpos_off : Z := 169592.
Definition post_loc (n r : Z) (C : sstate) : sstate := ltac2:(tb__ "0|2|
S29S10cSf6S36VC;A1A1S35VC;A1S34VC;A1S37VC;A1S0S18S6cVC;U1A2S0S18S1bS16P1A1M0S11N21fA1S11S12cVn;Z21fA2A1M1S2S12A1S1fP7A1A5S0S18S6cVC;U4A2S0S18S6cVC;UeA2S0S18SfcSfdS17S48G0G1A3S6cVC;UbA2A3S2S18A1A3A3A3A3A3S20VC;A1P56S8A9").

Definition E_hi_lo : sv := SAlu ALU_ADD (SVar 28) (SLit (-543)).
Definition mk_E_po (A : sstate) (R : list sobj) : sstate :=
  mkSS ret_out (po_regs (ss_regs A)) (ss_fregs A) (ss_fcsr A) (ss_resv A)
       ([obj A 1;
         mkObj (SVar 1) (SLit (-543)) E_hi_lo [] (DList 7);
         mkObj (SVar 1) E_hi_lo (SLit (-480)) [] DUnknown;
         obj A 13;
         upd_cell wpos_off (SAlu ALU_ADD (SAlu ALU_ADD (SVar 1) (SLit (-543))) (SVar 28)) (obj A 10)] ++ R)
       (ss_facts A) 86%positive false.
Definition E_po_0 : sstate := Eval vm_compute in mk_E_po (E_fxA false) (R_gen false).
Definition E_po_1 : sstate := Eval vm_compute in mk_E_po (E_fxA true) (R_gen true).
Definition E_po (r : bool) : sstate := if r then E_po_1 else E_po_0.
Lemma swf_E_po : forall r, swf (E_po r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma E_po_next : forall r, ss_next (E_po r) = 86%positive.
Proof. intros [|]; reflexivity. Qed.

Definition BLn (n : Z) : list bexp := ltac2:(tb__ "0|0|
S123S6S114S6S117P3S12bR1A1A2Lj;S125U0S12dVn;A1A2A4").

Definition diff_in_ok (n r : Z) (ab : sv * sv) : bool := ltac2:(tb__ "0|0|
S5eS102Sd3Vn;Vr;A2SeS14S14Vab;A3A2S10S14S14Vab;A3A2").
Definition diff_out_ok (n r : Z) (ab : sv * sv) : bool := ltac2:(tb__ "0|0|
S5eSeS14S14Vab;A3S102Sd3Vn;Vr;A2S10S14S14Vab;A3A2A2").
Definition ids_below71 : list positive := map Pos.of_nat (seq 1 70).

Definition check_pre (rq : bool) (n r : Z) : option (sstate * sstate) :=
  let C0 := C0_nr rq n r in
  match state_diff (E_fxA rq) C0 with
  | Some (d, nf) =>
      match apply_xforms C0 (xs_c n) with
      | Some C =>
          if swf C0 && forallb (diff_in_ok n r) d && list_eqb sprop_eqb nf [F_n n]
             && (ss_next C =? 71)%positive && negb (ss_lenient C)
          then Some (C, pre_loc C) else None
      | None => None
      end
  | None => None
  end.
Definition the_pre (rq : bool) (n r : Z) : sstate :=
  match check_pre rq n r with Some (_, P) => P | None => E_fxA rq end.
Definition check_core (rq : bool) (n r : Z) (res : option (list leaf)) : bool :=
  match check_pre rq n r with
  | Some (C, P) =>
      let Q := post_loc n r C in
      (match entails_fr C P [] with Some R => list_eqb sobj_eqb R (R_gen rq) | None => false end
       && call_check C P [] (R_gen rq) [mkLeaf Q RsCut]
       && match res with
          | Some [L] =>
              (match nth_error (ss_objs (lf_state L)) 1 with
               | Some o =>
                   sv_eqb (ob_lo o) (SLit (-543)) && sv_eqb (ob_hi o) (SLit (n - 543))
                   && dflt_writable (ob_dflt o) && negb (is_arr (ob_dflt o))
                   && match cells_bytes (ob_cells o) (SLit (-543)) 0 (Z.to_nat n) with
                      | Some bl => list_eqb bexp_eqb bl (BLn n)
                      | None => false
                      end
               | None => false
               end)
              && negb (state_has_rl 7 (lf_state L))
              && (let wl := obj_to_list (lf_state L) 1 7 in
                  let s := infer_sub 71 wl Q in
                  entails wl Q s && forallb (fun i => sv_eqb (wsub_get s i) (SVar i)) ids_below71)
          | _ => false
          end
       && match state_diff (import_post [] 71 Q 71 (R_gen rq)) (E_po rq) with
          | Some (d, []) => forallb (diff_out_ok n r) d
          | _ => false
          end)%bool
  | None => false
  end.

Definition check_nr (rq : bool) (r n : nat) : bool :=
  check_core rq (Z.of_nat n) (Z.of_nat r) (sym_run segs FUELm [ret_out] (the_pre rq (Z.of_nat n) (Z.of_nat r)) true).
Definition check_range (rq : bool) (r a len : nat) : bool := forallb (check_nr rq r) (seq a len).

Definition xs_po : list xform := ltac2:(tb__ "0|4|
S0S61S65S0S6U5S0S6U0M0S0S6U6S0S6U1S0S6U2S0S6U7S0S6U8M1S0S6U9S0S6UaS0S6UbS0S6UcS0S6U4S0S6UdS0S6UeS0S6U3S2S6A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S61S64G0A1M2S0S61G2S0S61S64G1A1M3S0S61G3S2S61A1A3A3A3A3A3").
Definition E_po2_0 : sstate := Eval vm_compute in xget (E_po false) (axf (E_po false) xs_po).
Definition E_po2_1 : sstate := Eval vm_compute in xget (E_po true) (axf (E_po true) xs_po).
Definition E_po2 (r : bool) : sstate := if r then E_po2_1 else E_po2_0.
Lemma xs_po_ok : forall r, apply_xforms (E_po r) xs_po = Some (E_po2 r).
Proof. intros [|]; fast_lit_. Qed.

Definition E_po62 (r : bool) : sstate := add_facts [SPUle (SVar 28) (SLit 62)] (E_po2 r).
Definition E_po63 (r : bool) : sstate := add_facts [SPUle (SLit 63) (SVar 28)] (E_po2 r).
Definition E_fx2a_0 : sstate := Eval vm_compute in lf0 (E_po62 false) (srf segs FUEL [fwritex_entry] (E_po62 false) true) 0.
Definition E_fx2a_1 : sstate := Eval vm_compute in lf0 (E_po62 true) (srf segs FUEL [fwritex_entry] (E_po62 true) true) 0.
Definition E_fx2a (r : bool) : sstate := if r then E_fx2a_1 else E_fx2a_0.
Lemma run_po62 : forall r, sym_run segs FUEL [fwritex_entry] (E_po62 r) true = Some [mkLeaf (E_fx2a r) RsCut].
Proof. intros [|]; run_cast_. Qed.
Definition E_Wa1_0 : sstate := Eval vm_compute in lf0 (E_fx2a false) (srf segs FUEL [] (E_fx2a false) true) 0.
Definition E_Wa1_1 : sstate := Eval vm_compute in lf0 (E_fx2a true) (srf segs FUEL [] (E_fx2a true) true) 0.
Definition E_Wa1 (r : bool) : sstate := if r then E_Wa1_1 else E_Wa1_0.
Definition E_Wa2_0 : sstate := Eval vm_compute in lf0 (E_fx2a false) (srf segs FUEL [] (E_fx2a false) true) 1.
Definition E_Wa2_1 : sstate := Eval vm_compute in lf0 (E_fx2a true) (srf segs FUEL [] (E_fx2a true) true) 1.
Definition E_Wa2 (r : bool) : sstate := if r then E_Wa2_1 else E_Wa2_0.
Lemma run_fx2a : forall r,
  sym_run segs FUEL [] (E_fx2a r) true = Some [mkLeaf (E_Wa1 r) RsEcall; mkLeaf (E_Wa2 r) RsEcall].
Proof. intros [|]; run_cast_. Qed.


Definition dropfact (S : sstate) : sstate := ltac2:(tb__ "0|0|
S29S2fVS;A1S36VS;A1S35VS;A1S34VS;A1S37VS;A1S23VS;A1S113S15S20VS;A1A2S1cVS;A1S3bVS;A1A9").
Definition E_Wa_0 : sstate := Eval vm_compute in dropfact (E_Wa1 false).
Definition E_Wa_1 : sstate := Eval vm_compute in dropfact (E_Wa1 true).
Definition E_Wa (r : bool) : sstate := if r then E_Wa_1 else E_Wa_0.
Lemma ent_Wa1 : forall r, entails (E_Wa1 r) (E_Wa r) [] = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma ent_Wa2 : forall r, entails (E_Wa2 r) (E_Wa r) [] = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Definition E_fx2b_0 : sstate := Eval vm_compute in lf0 (E_po63 false) (srf segs FUEL [fwritex_entry] (E_po63 false) true) 0.
Definition E_fx2b_1 : sstate := Eval vm_compute in lf0 (E_po63 true) (srf segs FUEL [fwritex_entry] (E_po63 true) true) 0.
Definition E_fx2b (r : bool) : sstate := if r then E_fx2b_1 else E_fx2b_0.
Lemma run_po63 : forall r, sym_run segs FUEL [fwritex_entry] (E_po63 r) true = Some [mkLeaf (E_fx2b r) RsCut].
Proof. intros [|]; run_cast_. Qed.
Definition E_Wb_0 : sstate := Eval vm_compute in lf0 (E_fx2b false) (srf segs FUEL [] (E_fx2b false) true) 0.
Definition E_Wb_1 : sstate := Eval vm_compute in lf0 (E_fx2b true) (srf segs FUEL [] (E_fx2b true) true) 0.
Definition E_Wb (r : bool) : sstate := if r then E_Wb_1 else E_Wb_0.
Lemma run_fx2b : forall r, sym_run segs FUEL [] (E_fx2b r) true = Some [mkLeaf (E_Wb r) RsEcall].
Proof. intros [|]; run_cast_. Qed.

(* The iovec count register: computed from the r = false run and checked equal in both runs. *)
Definition IOVa : sv := Eval vm_compute in reg_sv (E_Wa false) 12.
Lemma r12_wa : forall r, reg_sv (E_Wa r) 12 = IOVa /\ reg_sv (E_Wa r) 18 = IOVa.
Proof. intros [|]; split; reflexivity. Qed.
(* The writev call sets its iovec count to 2: the rule that restates it. *)
Definition wr2_of (E : sstate) : sstate :=
  mkSS (ss_pc E) (list_set (list_set (ss_regs E) 12 (SLit 2)) 18 (SLit 2)) (ss_fregs E) (ss_fcsr E) (ss_resv E)
       (ss_objs E) (ss_facts E) (ss_next E) false.
Definition E_Wa_r_0 : sstate := Eval vm_compute in wr2_of (E_Wa false).
Definition E_Wa_r_1 : sstate := Eval vm_compute in wr2_of (E_Wa true).
Definition E_Wa_r (r : bool) : sstate := if r then E_Wa_r_1 else E_Wa_r_0.
Lemma diff_wa : forall r, state_diff (E_Wa r) (E_Wa_r r) = Some ([(IOVa, SLit 2); (IOVa, SLit 2)], @nil sprop).
Proof. intros [|]; vm_cast_no_check (@eq_refl _ (Some ([(IOVa, SLit 2); (IOVa, SLit 2)], @nil sprop))). Qed.
Lemma swf_E_Wa_r : forall r, swf (E_Wa_r r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.

Definition xs_wa1 : list xform := ltac2:(tb__ "0|0|
S0S61S63U0S11N230A1A2S0S61S63U3S17S48S16P1cA1S11N21eA1A3A2S2S61A1A3A3").
Definition E_Wa_x_0 : sstate := Eval vm_compute in xget (E_Wa_r false) (axf (E_Wa_r false) xs_wa1).
Definition E_Wa_x_1 : sstate := Eval vm_compute in xget (E_Wa_r true) (axf (E_Wa_r true) xs_wa1).
Definition E_Wa_x (r : bool) : sstate := if r then E_Wa_x_1 else E_Wa_x_0.
Lemma xs_wa1_ok : forall r, apply_xforms (E_Wa_r r) xs_wa1 = Some (E_Wa_x r).
Proof. intros [|]; fast_lit_. Qed.

Lemma obj1_wa : forall r,
  nth_error (ss_objs (E_Wa_x r)) 1 = Some (obj (E_Wa_x r) 1) /\ ob_lo (obj (E_Wa_x r) 1) = SLit (-560)
  /\ ob_hi (obj (E_Wa_x r) 1) = SLit (-543) /\ dflt_writable (ob_dflt (obj (E_Wa_x r) 1)) = true
  /\ is_arr (ob_dflt (obj (E_Wa_x r) 1)) = false.
Proof. intros [|]; repeat split; reflexivity. Qed.
Lemma cb_wa1 : forall r, cells_bytes (ob_cells (obj (E_Wa_x r) 1)) (SLit (-560)) 0 17 = Some BL_co.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ (Some BL_co)). Qed.
Lemma norl8_wa : forall r, state_has_rl 8 (E_Wa_x r) = false.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ false). Qed.
Definition E_Wa_l1_0 : sstate := Eval vm_compute in obj_to_list (E_Wa_x false) 1 8.
Definition E_Wa_l1_1 : sstate := Eval vm_compute in obj_to_list (E_Wa_x true) 1 8.
Definition E_Wa_l1 (r : bool) : sstate := if r then E_Wa_l1_1 else E_Wa_l1_0.
Lemma E_Wa_l1_eq : forall r, obj_to_list (E_Wa_x r) 1 8 = E_Wa_l1 r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition LOnl : sv := SAlu ALU_ADD (SVar 28) (SLit (-543)).
Definition HInl : sv := SAlu ALU_ADD (SVar 28) (SLit (-542)).
Lemma obj3_wa : forall r,
  nth_error (ss_objs (E_Wa_l1 r)) 3 = Some (obj (E_Wa_l1 r) 3) /\ ob_lo (obj (E_Wa_l1 r) 3) = LOnl
  /\ ob_hi (obj (E_Wa_l1 r) 3) = HInl /\ dflt_writable (ob_dflt (obj (E_Wa_l1 r) 3)) = true
  /\ is_arr (ob_dflt (obj (E_Wa_l1 r) 3)) = false /\ ob_base (obj (E_Wa_l1 r) 3) = SVar 1.
Proof. intros [|]; repeat split; reflexivity. Qed.
Lemma cb_wa3 : forall r, cells_bytes (ob_cells (obj (E_Wa_l1 r) 3)) LOnl 0 1 = Some [BLit 10].
Proof. intros [|]; vm_cast_no_check (@eq_refl _ (Some [BLit 10])). Qed.
Lemma norl9_wa : forall r, state_has_rl 9 (E_Wa_l1 r) = false.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ false). Qed.
Definition E_Wa_l_0 : sstate := Eval vm_compute in obj_to_list (E_Wa_l1 false) 3 9.
Definition E_Wa_l_1 : sstate := Eval vm_compute in obj_to_list (E_Wa_l1 true) 3 9.
Definition E_Wa_l (r : bool) : sstate := if r then E_Wa_l_1 else E_Wa_l_0.
Lemma E_Wa_l_eq : forall r, obj_to_list (E_Wa_l1 r) 3 9 = E_Wa_l r.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Lemma m1_wa : forall r,
  nth_error (ss_objs (E_Wa_l r)) 1 = Some (mkObj (SVar 1) (SLit (-560)) (SLit (-543)) [] (DList 8))
  /\ nth_error (ss_objs (E_Wa_l r)) 2 = Some (mkObj (SVar 1) (SLit (-543)) LOnl [] (DList 7)).
Proof. intros [|]; split; reflexivity. Qed.
Lemma norl10_wa : forall r, state_has_rl 10 (E_Wa_l r) = false.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ false). Qed.
Definition E_Wa_m1_0 : sstate := Eval vm_compute in merge_lists (E_Wa_l false) 1 10.
Definition E_Wa_m1_1 : sstate := Eval vm_compute in merge_lists (E_Wa_l true) 1 10.
Definition E_Wa_m1 (r : bool) : sstate := if r then E_Wa_m1_1 else E_Wa_m1_0.
Lemma E_Wa_m1_eq : forall r, merge_lists (E_Wa_l r) 1 10 = E_Wa_m1 r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma swf_E_Wa_m1 : forall r, swf (E_Wa_m1 r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma m2_wa : forall r,
  nth_error (ss_objs (E_Wa_m1 r)) 1 = Some (mkObj (SVar 1) (SLit (-560)) LOnl [] (DList 10))
  /\ nth_error (ss_objs (E_Wa_m1 r)) 2 = Some (mkObj (SVar 1) LOnl HInl [] (DList 9)).
Proof. intros [|]; split; reflexivity. Qed.
Lemma norl5_wa : forall r, state_has_rl 5 (E_Wa_m1 r) = false.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ false). Qed.
Definition E_Wa_m2_0 : sstate := Eval vm_compute in merge_lists (E_Wa_m1 false) 1 5.
Definition E_Wa_m2_1 : sstate := Eval vm_compute in merge_lists (E_Wa_m1 true) 1 5.
Definition E_Wa_m2 (r : bool) : sstate := if r then E_Wa_m2_1 else E_Wa_m2_0.
Lemma E_Wa_m2_eq : forall r, merge_lists (E_Wa_m1 r) 1 5 = E_Wa_m2 r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma swf_E_Wa_m2 : forall r, swf (E_Wa_m2 r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.

Definition B544 : sv := SAlu ALU_ADD (SVar 1) (SLit (-560)).
Definition LENa : sv := SAlu ALU_ADD (SVar 28) (SLit 18).
Lemma rf_wa : forall r, nth_error (ss_objs (E_Wa_m2 r)) 1 = Some (mkObj (SVar 1) (SLit (-560)) HInl [] (DList 5)).
Proof. intros [|]; reflexivity. Qed.
Definition E_Wa_m_0 : sstate := Eval vm_compute in reframe_obj (E_Wa_m2 false) 1 B544 (SLit 0) LENa.
Definition E_Wa_m_1 : sstate := Eval vm_compute in reframe_obj (E_Wa_m2 true) 1 B544 (SLit 0) LENa.
Definition E_Wa_m (r : bool) : sstate := if r then E_Wa_m_1 else E_Wa_m_0.
Lemma E_Wa_m_eq : forall r, reframe_obj (E_Wa_m2 r) 1 B544 (SLit 0) LENa = E_Wa_m r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma swf_E_Wa_m : forall r, swf (E_Wa_m r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.

Lemma norl6_wa : forall r, state_has_rl 6 (E_Wa_m r) = false.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ false). Qed.
Definition E_Wa_c0_0 : sstate := Eval vm_compute in app_objs (E_Wa_m false) [O_emp] (ss_next (E_Wa_m false)).
Definition E_Wa_c0_1 : sstate := Eval vm_compute in app_objs (E_Wa_m true) [O_emp] (ss_next (E_Wa_m true)).
Definition E_Wa_c0 (r : bool) : sstate := if r then E_Wa_c0_1 else E_Wa_c0_0.
Lemma E_Wa_c0_eq : forall r, app_objs (E_Wa_m r) [O_emp] (ss_next (E_Wa_m r)) = E_Wa_c0 r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma swf_E_Wa_c0 : forall r, swf (E_Wa_c0 r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma E_Wa_nexts : forall r,
  ss_next (E_Wa_m r) = ss_next (E_Wa r) /\ ss_next (E_Wa_x r) = ss_next (E_Wa r)
  /\ ss_next (E_Wa_l1 r) = ss_next (E_Wa r) /\ ss_next (E_Wa_m2 r) = ss_next (E_Wa r).
Proof. intros [|]; repeat split; reflexivity. Qed.


Definition xs_wa2 : list xform := ltac2:(tb__ "0|2|
S0S61S63U0M0S11N288A1A2S0S61S63G0S11N2a8A1A2S0S61S63UaM1S11Z296ccA1A2S0S61S63G1S11Z296c8A1A2S2S61A1A3A3A3A3").
Definition E_Wa_c_0 : sstate := Eval vm_compute in xget (E_Wa_c0 false) (axf (E_Wa_c0 false) xs_wa2).
Definition E_Wa_c_1 : sstate := Eval vm_compute in xget (E_Wa_c0 true) (axf (E_Wa_c0 true) xs_wa2).
Definition E_Wa_c (r : bool) : sstate := if r then E_Wa_c_1 else E_Wa_c_0.
Lemma xs_wa2_ok : forall r, apply_xforms (E_Wa_c0 r) xs_wa2 = Some (E_Wa_c r).
Proof. intros [|]; fast_lit_. Qed.
Definition s_wa : wsub := ltac2:(tb__ "0|12|
S0SaS43S14A2M0S1S43S14PcM1S17S48S16P1A1M2S11N230A1A3M3A4S0G0S1S43S14PdM4S17S48S16P1cA1M5S11Z12A1A3A4S0G0S1S43S14PeM6S11Z0A1M7A4S0G0S1S43S14PfG7A4M8S0G0S1S43S14G6G2A4S0G0S1S43S14G1G2A4S0G0S1S43S14G4G5A4S0G0S1S43S14P5bG7A4S0G0S1S43S14P5aG7A4S0G0S1S43S14P59G7A4S0G0S1S43S14P58G7A4S0G0S1S43S14P57G7A4S0G0S1S43S14P56G7A4S0G0S1S43S14P55M9G7A4S0G0S1S43S14P54MaG7A4S0G0S1S43S14P53MbG7A4S0G0S1S43S14P52McG7A4S0G0S1S43S14P51G7A4S0G0S1S43S14P50MdG7A4S0G0S1S43S14P4fG7A4S0G0S1S43S14P4eG7A4S0G0S1S43S14P4dG7A4S0G0S1S43S14P4cG7A4S0G0S1S43S14P4bG7A4S0G0S1S43S14P4aG7A4S0G0S1S43S14P49MeG7A4S0G0S1S43S14P48MfG7A4S0G0S1S43S14P47M10G7A4S0G0S1S43S14P46G7A4S0G0S1S43S14P45G7A4S0G0S1S43S14P44G7A4S0G0S1S43S14P43G7A4S0G0S1S43S14P42G7A4S0G0S1S43S14P41G7A4S0G0S1S43S14P40G7A4S0G0S1S43S14P3fG7A4S0G0S1S43S14P3eG7A4S0G0S1S43S14P3dG7A4S0G0S1S43S14P3cG7A4S0G0S1S43S14P33S16G9A1A4S0G0S1S43S14P32S16GaA1A4S0G0S1S43S14P31S16GbA1A4S0G0S1S43S14P30S16GcA1A4S0G0S1S43S14P2fG7A4S0G0S1S43S14P2eG7A4S0G0S1S43S14P2dG7A4S0G0S1S43S14P2cG7A4S0G0S1S43S14P2bG7A4S0G0S1S43S14P29S11Z59bf8A1A4S0G0S1S43S14P28S11Z5a058A1A4S0G0S1S43S14P24S16GdA1A4S0G0S1S43S14P23S17S53S17S48S17S48G2S11N21fA1A3G5A3M11S11Z3A1A3A4S0G0S1S43S14P22G7A4S0G0S1S43S14P21S17S51S17S48G11S11Z1A1A3G3A3A4S0G0G8S0G0S1S43S14P1bS16GeA1A4S0G0S1S43S14P1aS16GfA1A4S0G0S1S43S14P19S16G10A1A4S0G0S1S43S14P18S11Z39990A1A4S0G0S1S43S14PaS17S48G2S11N2b0A1A3A4S0G0S1S43S14P15S11Z222fcA1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition R_wa_0 : list sobj := Eval vm_compute in match entails_fr (E_Wa_c false) Pre_wl2 s_wa with Some R => R | None => [] end.
Definition R_wa_1 : list sobj := Eval vm_compute in match entails_fr (E_Wa_c true) Pre_wl2 s_wa with Some R => R | None => [] end.
Definition R_wa (r : bool) : list sobj := if r then R_wa_1 else R_wa_0.
Lemma efr_wa : forall r, entails_fr (E_Wa_c r) Pre_wl2 s_wa = Some (R_wa r).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma chk_wa : forall r, call_check (E_Wa_c r) Pre_wl2 s_wa (R_wa r) [mkLeaf D RsCut] = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_wa : forall r, forallb (sprop_below (ss_next (E_Wa_c r))) (ss_facts (E_Wa r)) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma facts_wac : forall r, ss_facts (E_Wa_c r) = ss_facts (E_Wa r).
Proof. intros [|]; reflexivity. Qed.
Lemma s_wa_vals : ltac2:(tb__ "0|1|
S47S46S14S101S7cPcA2S83A3S47S46S14S101S7cPdA2Sb5A3S47S46S14S101S7cPeA2S11Z0A1M0A3S46S14S101S7cPfA2G0A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Definition T_Dai_0 : sstate := Eval vm_compute in import_post s_wa 92 D (ss_next (E_Wa_c false)) (R_wa false).
Definition T_Dai_1 : sstate := Eval vm_compute in import_post s_wa 92 D (ss_next (E_Wa_c true)) (R_wa true).
Definition T_Dai (r : bool) : sstate := if r then T_Dai_1 else T_Dai_0.
Lemma T_Dai_eq : forall r, import_post s_wa 92 D (ss_next (E_Wa_c r)) (R_wa r) = T_Dai r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition T_Da_0 : sstate := Eval vm_compute in add_facts (ss_facts (E_Wa false)) (T_Dai false).
Definition T_Da_1 : sstate := Eval vm_compute in add_facts (ss_facts (E_Wa true)) (T_Dai true).
Definition T_Da (r : bool) : sstate := if r then T_Da_1 else T_Da_0.
Lemma xs_da_ok : forall r, apply_xforms (add_facts (ss_facts (E_Wa r)) (T_Dai r)) [] = Some (T_Da r).
Proof. intros [|]; fast_lit_. Qed.
Lemma fb_da : forall r, forallb (sprop_below (ss_next (T_Dai r))) (ss_facts (E_Wa r)) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.

Definition E_exa_0 : sstate := Eval vm_compute in lf0 (T_Da false) (srf segs FUEL [] (T_Da false) true) 0.
Definition E_exa_1 : sstate := Eval vm_compute in lf0 (T_Da true) (srf segs FUEL [] (T_Da true) true) 0.
Definition E_exa (r : bool) : sstate := if r then E_exa_1 else E_exa_0.
Lemma run_da : forall r, sym_run segs FUEL [] (T_Da r) true = Some [mkLeaf (E_exa r) RsEcall].
Proof. intros [|]; run_cast_. Qed.
Lemma cert_exa : forall r,
  instr_at segs (ss_pc (E_exa r)) = Some Ecall /\ reg_sv (E_exa r) 17 = SLit 94 /\ reg_sv (E_exa r) 10 = SLit 2.
Proof. intros [|]; repeat split; reflexivity. Qed.

(* The iovec count register: computed from the r = false run and checked equal in both runs. *)
Definition IOVb : sv := Eval vm_compute in reg_sv (E_Wb false) 12.
Lemma r12_wb : forall r, reg_sv (E_Wb r) 12 = IOVb /\ reg_sv (E_Wb r) 18 = IOVb.
Proof. intros [|]; split; reflexivity. Qed.
Definition E_Wb_r_0 : sstate := Eval vm_compute in wr2_of (E_Wb false).
Definition E_Wb_r_1 : sstate := Eval vm_compute in wr2_of (E_Wb true).
Definition E_Wb_r (r : bool) : sstate := if r then E_Wb_r_1 else E_Wb_r_0.
Lemma diff_wb : forall r, state_diff (E_Wb r) (E_Wb_r r) = Some ([(IOVb, SLit 2); (IOVb, SLit 2)], @nil sprop).
Proof. intros [|]; vm_cast_no_check (@eq_refl _ (Some ([(IOVb, SLit 2); (IOVb, SLit 2)], @nil sprop))). Qed.
Lemma swf_E_Wb_r : forall r, swf (E_Wb_r r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.

Definition xs_wb1 : list xform := [XSplit 0 (SLit (-560))].
Definition E_Wb_x_0 : sstate := Eval vm_compute in xget (E_Wb_r false) (axf (E_Wb_r false) xs_wb1).
Definition E_Wb_x_1 : sstate := Eval vm_compute in xget (E_Wb_r true) (axf (E_Wb_r true) xs_wb1).
Definition E_Wb_x (r : bool) : sstate := if r then E_Wb_x_1 else E_Wb_x_0.
Lemma xs_wb1_ok : forall r, apply_xforms (E_Wb_r r) xs_wb1 = Some (E_Wb_x r).
Proof. intros [|]; fast_lit_. Qed.
Lemma obj1_wb : forall r,
  nth_error (ss_objs (E_Wb_x r)) 1 = Some (obj (E_Wb_x r) 1) /\ ob_lo (obj (E_Wb_x r) 1) = SLit (-560)
  /\ ob_hi (obj (E_Wb_x r) 1) = SLit (-543) /\ dflt_writable (ob_dflt (obj (E_Wb_x r) 1)) = true
  /\ is_arr (ob_dflt (obj (E_Wb_x r) 1)) = false.
Proof. intros [|]; repeat split; reflexivity. Qed.
Lemma cb_wb1 : forall r, cells_bytes (ob_cells (obj (E_Wb_x r) 1)) (SLit (-560)) 0 17 = Some BL_co.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ (Some BL_co)). Qed.
Lemma norl8_wb : forall r, state_has_rl 8 (E_Wb_x r) = false.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ false). Qed.
Definition E_Wb_l_0 : sstate := Eval vm_compute in obj_to_list (E_Wb_x false) 1 8.
Definition E_Wb_l_1 : sstate := Eval vm_compute in obj_to_list (E_Wb_x true) 1 8.
Definition E_Wb_l (r : bool) : sstate := if r then E_Wb_l_1 else E_Wb_l_0.
Lemma E_Wb_l_eq : forall r, obj_to_list (E_Wb_x r) 1 8 = E_Wb_l r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma m_wb : forall r,
  nth_error (ss_objs (E_Wb_l r)) 1 = Some (mkObj (SVar 1) (SLit (-560)) (SLit (-543)) [] (DList 8))
  /\ nth_error (ss_objs (E_Wb_l r)) 2 = Some (mkObj (SVar 1) (SLit (-543)) LOnl [] (DList 7)).
Proof. intros [|]; split; reflexivity. Qed.
Lemma norl5_wb : forall r, state_has_rl 5 (E_Wb_l r) = false.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ false). Qed.
Definition E_Wb_m1_0 : sstate := Eval vm_compute in merge_lists (E_Wb_l false) 1 5.
Definition E_Wb_m1_1 : sstate := Eval vm_compute in merge_lists (E_Wb_l true) 1 5.
Definition E_Wb_m1 (r : bool) : sstate := if r then E_Wb_m1_1 else E_Wb_m1_0.
Lemma E_Wb_m1_eq : forall r, merge_lists (E_Wb_l r) 1 5 = E_Wb_m1 r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma swf_E_Wb_m1 : forall r, swf (E_Wb_m1 r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma rf_wb : forall r, nth_error (ss_objs (E_Wb_m1 r)) 1 = Some (mkObj (SVar 1) (SLit (-560)) LOnl [] (DList 5)).
Proof. intros [|]; reflexivity. Qed.
Definition E_Wb_m_0 : sstate := Eval vm_compute in reframe_obj (E_Wb_m1 false) 1 B544 (SLit 0) (SLit 80).
Definition E_Wb_m_1 : sstate := Eval vm_compute in reframe_obj (E_Wb_m1 true) 1 B544 (SLit 0) (SLit 80).
Definition E_Wb_m (r : bool) : sstate := if r then E_Wb_m_1 else E_Wb_m_0.
Lemma E_Wb_m_eq : forall r, reframe_obj (E_Wb_m1 r) 1 B544 (SLit 0) (SLit 80) = E_Wb_m r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma swf_E_Wb_m : forall r, swf (E_Wb_m r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.

(* The address of the newline in the image: computed from the r = false run and checked equal in both runs. *)
Definition nl_addr : Z := Eval vm_compute in match reg_sv (E_fx2b false) 10 with SLit a => a | _ => 0 end.
Lemma nl_addr_r : forall r, reg_sv (E_fx2b r) 10 = SLit nl_addr.
Proof. intros [|]; reflexivity. Qed.
Definition O_nlr : sobj := ltac2:(tb__ "0|0|
S1bS11SceA1S11Z0A1S11Z1A1S2S12A1S32P6A1A5").
Lemma img_nl : ltac2:(tb__ "0|3|
S47S46S3S132Q8M0A1M1A1S3eS67S131Q40SceA2M2A2S5G1S131G0ZaA2A2A3S46S9S40S67G2A2S7A3A2").
Proof. split; [vm_cast_no_check (@eq_refl _ (Some (Z_to_bv 8 10))) | vm_cast_no_check (@eq_refl _ true)]. Qed.
Lemma norl6_wb : forall r, state_has_rl 6 (E_Wb_m r) = false.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ false). Qed.
Definition E_Wb_c0_0 : sstate := Eval vm_compute in app_objs (E_Wb_m false) [O_nlr] (ss_next (E_Wb_m false)).
Definition E_Wb_c0_1 : sstate := Eval vm_compute in app_objs (E_Wb_m true) [O_nlr] (ss_next (E_Wb_m true)).
Definition E_Wb_c0 (r : bool) : sstate := if r then E_Wb_c0_1 else E_Wb_c0_0.
Lemma E_Wb_c0_eq : forall r, app_objs (E_Wb_m r) [O_nlr] (ss_next (E_Wb_m r)) = E_Wb_c0 r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma swf_E_Wb_c0 : forall r, swf (E_Wb_c0 r) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma E_Wb_nexts : forall r,
  ss_next (E_Wb_m r) = ss_next (E_Wb r) /\ ss_next (E_Wb_x r) = ss_next (E_Wb r) /\ ss_next (E_Wb_m1 r) = ss_next (E_Wb r).
Proof. intros [|]; repeat split; reflexivity. Qed.
Definition xs_wb2 : list xform := ltac2:(tb__ "0|2|
S0S61S63U0M0S11N4a8A1A2S0S61S63G0S11N4c8A1A2S0S61S63UaM1S11Z296ccA1A2S0S61S63G1S11Z296c8A1A2S2S61A1A3A3A3A3").
Definition E_Wb_c_0 : sstate := Eval vm_compute in xget (E_Wb_c0 false) (axf (E_Wb_c0 false) xs_wb2).
Definition E_Wb_c_1 : sstate := Eval vm_compute in xget (E_Wb_c0 true) (axf (E_Wb_c0 true) xs_wb2).
Definition E_Wb_c (r : bool) : sstate := if r then E_Wb_c_1 else E_Wb_c_0.
Lemma xs_wb2_ok : forall r, apply_xforms (E_Wb_c0 r) xs_wb2 = Some (E_Wb_c r).
Proof. intros [|]; fast_lit_. Qed.
Definition s_wb : wsub := ltac2:(tb__ "0|14|
S0SaS43S14A2M0S1S43S14PcM1S17S48S16P1A1M2S11N230A1A3M3A4S0G0S1S43S14PdM4S11Z50A1A4S0G0S1S43S14PeM5S11Z105fcA1M6A4S0G0S1S43S14PfS11Z1A1M7A4M8S0G0S1S43S14G5G2A4S0G0S1S43S14G4S11N4a8A1A4S0G0S1S43S14G1G2A4S0G0S1S43S14P5bS11Z0A1M9A4S0G0S1S43S14P5aG9A4S0G0S1S43S14P59G9A4S0G0S1S43S14P58G9A4S0G0S1S43S14P57G9A4S0G0S1S43S14P56G9A4S0G0S1S43S14P55MaG9A4S0G0S1S43S14P54MbG9A4S0G0S1S43S14P53McG9A4S0G0S1S43S14P52MdG9A4S0G0S1S43S14P51G9A4S0G0S1S43S14P50MeG9A4S0G0S1S43S14P4fMfG9A4S0G0S1S43S14P4eM10G9A4S0G0S1S43S14P4dG9A4S0G0S1S43S14P4cG9A4S0G0S1S43S14P4bG9A4S0G0S1S43S14P4aG9A4S0G0S1S43S14P49M11G9A4S0G0S1S43S14P48G9A4S0G0S1S43S14P47M12G9A4S0G0S1S43S14P46G9A4S0G0S1S43S14P45G9A4S0G0S1S43S14P44G9A4S0G0S1S43S14P43G9A4S0G0S1S43S14P42G9A4S0G0S1S43S14P41G9A4S0G0S1S43S14P40G9A4S0G0S1S43S14P3fG9A4S0G0S1S43S14P3eG9A4S0G0S1S43S14P3dG9A4S0G0S1S43S14P3cG9A4S0G0S1S43S14P33S16GaA1A4S0G0S1S43S14P32S16GbA1A4S0G0S1S43S14P31S16GcA1A4S0G0S1S43S14P30S16GdA1A4S0G0S1S43S14P2fS16P1cA1M13A4S0G0S1S43S14P2eG7A4S0G0S1S43S14P2dG13A4S0G0S1S43S14P2cG9A4S0G0S1S43S14P2bG6A4S0G0S1S43S14P29S11Z59bf8A1A4S0G0S1S43S14P28S11Z29650A1A4S0G0S1S43S14P24S16GeA1A4S0G0S1S43S14P23S16GfA1A4S0G0S1S43S14P22S16G10A1A4S0G0S1S43S14P21S17S51S17S48S17S48G2S11N21fA1A3G13A3G3A3A4S0G0G8S0G0S1S43S14P1bS16G11A1A4S0G0S1S43S14P1aS11Z21ae4A1A4S0G0S1S43S14P19S16G12A1A4S0G0S1S43S14P18S11Z39990A1A4S0G0S1S43S14PaS17S48G2S11N4d0A1A3A4S0G0S1S43S14P15S11Z224ccA1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition R_wb_0 : list sobj := Eval vm_compute in match entails_fr (E_Wb_c false) Pre_wl2 s_wb with Some R => R | None => [] end.
Definition R_wb_1 : list sobj := Eval vm_compute in match entails_fr (E_Wb_c true) Pre_wl2 s_wb with Some R => R | None => [] end.
Definition R_wb (r : bool) : list sobj := if r then R_wb_1 else R_wb_0.
Lemma efr_wb : forall r, entails_fr (E_Wb_c r) Pre_wl2 s_wb = Some (R_wb r).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma chk_wb : forall r, call_check (E_Wb_c r) Pre_wl2 s_wb (R_wb r) [mkLeaf D RsCut] = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_wb : forall r, forallb (sprop_below (ss_next (E_Wb_c r))) (ss_facts (E_Wb r)) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.
Lemma facts_wbc : forall r, ss_facts (E_Wb_c r) = ss_facts (E_Wb r).
Proof. intros [|]; reflexivity. Qed.
Lemma s_wb_vals : ltac2:(tb__ "0|0|
S47S46S14S101S7dPcA2S83A3S47S46S14S101S7dPdA2S11Z50A1A3S47S46S14S101S7dPeA2S11SceA1A3S46S14S101S7dPfA2S11Z1A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Definition T_Dbi_0 : sstate := Eval vm_compute in import_post s_wb 92 D (ss_next (E_Wb_c false)) (R_wb false).
Definition T_Dbi_1 : sstate := Eval vm_compute in import_post s_wb 92 D (ss_next (E_Wb_c true)) (R_wb true).
Definition T_Dbi (r : bool) : sstate := if r then T_Dbi_1 else T_Dbi_0.
Lemma T_Dbi_eq : forall r, import_post s_wb 92 D (ss_next (E_Wb_c r)) (R_wb r) = T_Dbi r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition T_Db_0 : sstate := Eval vm_compute in add_facts (ss_facts (E_Wb false)) (T_Dbi false).
Definition T_Db_1 : sstate := Eval vm_compute in add_facts (ss_facts (E_Wb true)) (T_Dbi true).
Definition T_Db (r : bool) : sstate := if r then T_Db_1 else T_Db_0.
Lemma xs_db_ok : forall r, apply_xforms (add_facts (ss_facts (E_Wb r)) (T_Dbi r)) [] = Some (T_Db r).
Proof. intros [|]; fast_lit_. Qed.
Lemma fb_db : forall r, forallb (sprop_below (ss_next (T_Dbi r))) (ss_facts (E_Wb r)) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl _ true). Qed.

Definition E_Wz_0 : sstate := Eval vm_compute in lf0 (T_Db false) (srf segs FUEL [] (T_Db false) true) 0.
Definition E_Wz_1 : sstate := Eval vm_compute in lf0 (T_Db true) (srf segs FUEL [] (T_Db true) true) 0.
Definition E_Wz (r : bool) : sstate := if r then E_Wz_1 else E_Wz_0.
Lemma run_db : forall r, sym_run segs FUEL [] (T_Db r) true = Some [mkLeaf (E_Wz r) RsEcall].
Proof. intros [|]; run_cast_. Qed.

Definition ozi : nat := ltac2:(tb__ "0|0|
U5").
Lemma cert_wz : forall r,
  instr_at segs (ss_pc (E_Wz r)) = Some Ecall /\ reg_sv (E_Wz r) 17 = SLit 66 /\ reg_sv (E_Wz r) 10 = SLit 2
  /\ reg_sv (E_Wz r) 12 = SLit 1 /\ reg_sv (E_Wz r) 11 = SAlu ALU_ADD (SVar 1) (SLit (-664))
  /\ nth_error (ss_objs (E_Wz r)) ozi = Some (obj (E_Wz r) ozi) /\ ob_base (obj (E_Wz r) ozi) = SVar 1
  /\ existsb (cell_eqb (mkCell (SLit (-664)) 8 (SLit 0))) (ob_cells (obj (E_Wz r) ozi)) = true
  /\ existsb (cell_eqb (mkCell (SLit (-656)) 8 (SLit 0))) (ob_cells (obj (E_Wz r) ozi)) = true.
Proof. intros [|]; repeat split; reflexivity. Qed.
Definition PZ_0 : sstate := Eval vm_compute in S_after (E_Wz false) (SLit 0) (ss_objs (E_Wz false)) (ss_next (E_Wz false)).
Definition PZ_1 : sstate := Eval vm_compute in S_after (E_Wz true) (SLit 0) (ss_objs (E_Wz true)) (ss_next (E_Wz true)).
Definition PZ (r : bool) : sstate := if r then PZ_1 else PZ_0.
Lemma PZ_eq : forall r, S_after (E_Wz r) (SLit 0) (ss_objs (E_Wz r)) (ss_next (E_Wz r)) = PZ r.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition E_exb_0 : sstate := Eval vm_compute in lf0 (PZ false) (srf segs FUEL [] (PZ false) true) 0.
Definition E_exb_1 : sstate := Eval vm_compute in lf0 (PZ true) (srf segs FUEL [] (PZ true) true) 0.
Definition E_exb (r : bool) : sstate := if r then E_exb_1 else E_exb_0.
Lemma run_pz : forall r, sym_run segs FUEL [] (PZ r) true = Some [mkLeaf (E_exb r) RsEcall].
Proof. intros [|]; run_cast_. Qed.
Lemma cert_exb : forall r,
  instr_at segs (ss_pc (E_exb r)) = Some Ecall /\ reg_sv (E_exb r) 17 = SLit 94 /\ reg_sv (E_exb r) 10 = SLit 2.
Proof. intros [|]; repeat split; reflexivity. Qed.
End Drv_copen_states.

Module Drv_copen_chk2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_copen__G1.Drv_copen_states.

Lemma check_range_1 : forall r, check_range r 1 0 64 = true.
Proof. intros [|]; unfold check_range, check_nr; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.fast_forallb. Qed.
End Drv_copen_chk2.

Module Drv_copen_chk1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_copen__G1.Drv_copen_states.

Lemma check_range_0 : forall r, check_range r 0 0 64 = true.
Proof. intros [|]; unfold check_range, check_nr; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.fast_forallb. Qed.
End Drv_copen_chk1.

Module Drv_copen_chk3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_copen__G1.Drv_copen_states.

Lemma check_range_2 : forall r, check_range r 2 0 64 = true.
Proof. intros [|]; unfold check_range, check_nr; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.fast_forallb. Qed.
End Drv_copen_chk3.
