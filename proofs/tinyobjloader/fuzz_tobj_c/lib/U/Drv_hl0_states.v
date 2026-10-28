(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "option"; "true"; "Some"; "false"; "nat"; "bool"; "list"; "app"; "prod"; "None"; "fst"; "snd"; "andb"; "length"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "sv"; "mkCell"; "SVar"; "sprop"; "SPUle"; "SAlu"; "sobj"; "mkObj"; "sstate"; "DUnknown"; "SExt"; "SPBranch"; "ss_next"; "DImage"; "SPAlign"; "SPNot"; "ss_objs"; "ss_facts"; "mkSS"; "ss_lenient"; "DZero"; "FcsrFrm0"; "SLBytes"; "SPEq"; "SPUlt"; "ss_pc"; "reg_sv"; "swf"; "ss_regs"; "valuation"; "DRom"; "obj_range"; "sprop_below"; "ss_fcsr"; "ss_fregs"; "ss_resv"; "DList"; "obj_wf"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "ALU_SRL"; "BC_EQ"; "ALU_OR"; "ALU_SLL"; "BC_NE"; "instr"; "Ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "XSplit"; "XMerge"; "XRebase"; "XSelect"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "list_set"; "sym_run"; "RsCut"; "RsEcall"; "instr_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl0_states"; "E_io"; "E_w"; "S_0x"; "s_fz0"; "E_wc"; "P_0"; "E_f0x"; "T_w"; "s_F0"; "s_F2"; "T_wM"; "s_w"; "LCUTS"; "S_0"; "P_io"; "R_fz0"; "T_wDi"; "E_w3"; "P_0S"; "X_1"; "E_f0e"; "E_w2"; "O_payL"; "R_w"; "tvL"; "E_f02"; "NX0"; "N_1"; "PreFZ"; "T_wDr"; "E_f01"; "E_f0a"; "E_f0r"; "E_w1"; "S_01"; "T_wDf"; "T_wDm"; "O_b1z"; "robj_inwi"; "xs_wd"; "BL_w"; "E_f03"; "F2w"; "O_nl"; "PDfz"; "T_wDu"; "xs_f0e"; "xs_w"; "F2f"; "MEMO_13"; "MEMO_15"; "MEMO_26"; "O_pay0"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl0_states.LAddr"; "stdout_buf"; "nl_addr"; "stdout_fdo"; "ioctl_ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "In"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states"; "FUEL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FuzzOneIface"; "FZ_U"; "L_fuzz"; "fz_rets"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "reshape_obj_at"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "ltb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics"; "app_objs"; "statics_objs"; "@Corelib.Lists.ListDef"; "firstn"; "nth"; "skipn"; "map"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "BLit"; "beval"; "cells_bytes"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_afterN"; "tv_sub_eqb"; "caddr"; "call_checkT"; "img_ok"; "new_objs_tv"; "robjs_check"; "tvL_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht_states"; "F2"; "E_f0"; "C_facts"; "X_T"; "tvP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_out.WLoutS"; "D"; "Pre_wl2"; "wl_ecallA";
"@LinuxProcessSemantics.LinuxProcessSem.State"; "ENOTTY"; "errno_ret"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "state_has_rl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "import_post"; "call_check"; "wsub_dom_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht_states.TAddr"; "empty_addr"; "fz_entry_"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "robjs_missT_statics"; "robjs_missT"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states.RAddr"; "free_entry"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine"; "robj_img"; "rom_bytes_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvWins"; "robj_inw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "plain_obj"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins"; "WINS_U"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith.ZArith NArith.NArith Lists.List Bool.Bool PArith.PArith micromega.Lia.
From stdpp Require Import bitvector.bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout Contract Glue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymCall SymBytes Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue ObjXform ObjUnbase ListObj MuslWL DrvGlue DrvGlue2 TobjJV DataWin DrvStatics DrvPristine DrvLoop SysRead FuzzOneIface DrvWins.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Code Drv_wins.
Require Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_out OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht_states.
Import ListNotations.

Import MAddr RAddr StrAddr HAddr TAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module LAddr.
  Definition stdout_buf : Z := 0x5a7a0.
  Definition stdout_fdo : Z := 0x29ef8.
  Definition nl_addr : Z := 0x103c7.
  Definition ioctl_ecall : Z := 0x228d0.
End LAddr.
Import LAddr.

Definition robj_inwi (o : sobj) : bool := ltac2:(tb__ "0|0|
S8S8L_;ScfSd2Vo;A2S4ScdS8bS90Vo;A3X8x2").
Lemma robj_inwi_img : ltac2:(tb__ "0|1|
S30S19S3aS3bS8S7cR2A1S4A3S3cSa0SdS3aS3aS32R4R3A2M0A3R2A2Sa1R2SeS3aS3aG0A3A2A2Sb0S8bS90R3A3F_;F_;Fa;Fo;Frho;").
Proof.
  intros rho o a H Hr. unfold robj_inwi in H. destruct (robj_inw WINS_U o) eqn:E.
  - exact (robj_inw_sound segs C_U WINS_U rho o a WINS_U_ok E Hr).
  - exact (robj_img_sound segs C_U rho o a H Hr).
Qed.
Lemma robj_inwi_caddr : ltac2:(tb__ "0|1|
S30Sd1S3S3aA1S19S3aS3bS8S7cR2A1S4A3S3cSa0SdS3aS3aS32R6R3A2M0A3R2A2Sa1R2SeS3aS3aG0A3A2A2SaeS8bS90R6R5R3A5F_;F_;Fa;Fo;Fx;FAi;Frho;").
Proof. intros rho Ai x o a H Hr. right; left. exact (robj_inwi_img rho o a H Hr). Qed.

Definition LCUTS : list Z := ltac2:(tb__ "0|0|
S0S3aSc5S0S3aScbS2S3aA1A3A3").
Definition PreFZ : sstate := Pre_fuzz FZ_U.
Definition PDfz : list (sstate * list (sv * sv)) := PD_fuzz FZ_U.

Definition tvL : list (sv * sv) := ltac2:(tb__ "0|1|
S0SbS13S13A2M0S1S13S13S15Pf1A1S15P9eA1A4S0G0S1S13S13S15P66A1S15P65A1A4S2G0A1A3A3").
Definition O_payL : sobj := ltac2:(tb__ "0|0|
S1aS15Pf0A1S11Z0A1S15P9eA1S2S12A1S1cA5").
Definition L_facts : list sprop := ltac2:(tb__ "0|1|
SaS16S24Sb7A1SaS16Sb6S0S16S17S11Z1000A1S15Pf0A1M0A2S0S16S17G0S11Z7fffff800000A1A2S2S16A1A3A3A3A3").

Definition S0_regs : list sv := ltac2:(tb__ "0|1|
S4fS13S4fS13S4fS13S4fS13S4fS13S4fS13S4fS13S4fS13S4fS13S4fS13S2fSb4A1U9S15Pf0A1M0A4UaG0A4U12S15Pf1A1A4UbS15P9eA1A4UcS15Pf2A1A4UdS15Pf3A1A4UeS15Pf4A1A4UfS15Pf5A1A4U10S15Pf6A1A4U11S15Pf7A1A4").

Local Definition MEMO_1 : ltac2:(tb__ "0|0|
S3S1bA1") := ltac2:(tb__ "0|0|
S48Sb4S0S47S49UaS11S8cA1A2S2S47A1A3A2").
Definition F2w : sstate := ltac:(let x := eval vm_compute in (xget F2 (MEMO_1)) in exact x).
Local Lemma MEMO_1_c : MEMO_1 = Some F2w. Proof. vm_cast_no_check (@eq_refl _ MEMO_1). Qed.
Local Lemma MEMO_1_e : ltac2:(tb__ "0|0|
S3bS3S1bA1S48Sb4S0S47S49UaS11S8cA1A2S2S47A1A3A2S5S1bS80A2A3").
Proof. exact (@eq_trans _ (apply_xforms F2 [XSplit 10 (SLit stdout_buf)]) MEMO_1 (Some F2w) (@eq_refl _ (apply_xforms F2 [XSplit 10 (SLit stdout_buf)])) MEMO_1_c). Qed.
Lemma xs_F2_ok : ltac2:(tb__ "0|0|
S3bS3S1bA1S48Sb4S0S47S49UaS11S8cA1A2S2S47A1A3A2S5S1bS80A2A3"). Proof. exact MEMO_1_e. Qed.
Local Definition MEMO_2 := obj_forget F2w 11.
Definition F2f : sstate := ltac:(let x := eval vm_compute in (MEMO_2) in exact x).
Local Lemma MEMO_2_c : MEMO_2 = F2f. Proof. vm_cast_no_check (@eq_refl _ MEMO_2). Qed.
Local Lemma MEMO_2_e : obj_forget F2w 11 = F2f.
Proof. exact (@eq_trans _ (obj_forget F2w 11) MEMO_2 (F2f) (@eq_refl _ (obj_forget F2w 11)) MEMO_2_c). Qed.
Lemma F2f_eq : obj_forget F2w 11 = F2f. Proof. exact MEMO_2_e. Qed.
Definition S_0 : sstate := ltac:(let x := eval vm_compute in
  (mkSS (ss_pc F2) S0_regs (ss_fregs F2) (ss_fcsr F2) (ss_resv F2) (list_set (ss_objs F2f) 1 O_payL) L_facts 248%positive false) in exact x).
Definition s_F2 : wsub := ltac:(let x := eval vm_compute in (infer_sub 31 F2f S_0) in exact x).
Lemma ent_F2 : ltac2:(tb__ "0|0|
S3bS8S9dS86S63S5fA3S4A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma s_F2_vals : ltac2:(tb__ "0|8|
S3cS3bS13S54S5fPf0A2S15PaaA1M0A3S3cS3bS13S54S5fPf1A2G0A3S3cS3bS13S54S5fP9eM1A2S15G1A1A3S3cS3bS13S54S5fP9fM2A2S15G2A1A3S3cS3bS13S54S5fP9dM3A2S15G3A1A3S3cS3bS13S54S5fP64M4A2S15G4A1A3S3cS3bS13S54S5fP65M5A2S15G5A1A3S3cS3bS13S54S5fP66M6A2S15G6A1A3S3bS13S54S5fP67M7A2S15G7A1A3A2A2A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma s_F2_props : ltac2:(tb__ "0|0|
S3cS3bS8S55S5fP1fA2S4A3S3bS8SadS5fSb8S6eA3S4A3A2"). Proof. split; vm_cast_no_check (@eq_refl bool true). Qed.

Definition E_f0r : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc E_f0) (list_set (ss_regs E_f0) 11 (SVar 158)) (ss_fregs E_f0) (ss_fcsr E_f0) (ss_resv E_f0) (ss_objs E_f0) (ss_facts E_f0) (ss_next E_f0) false) in exact x).
Lemma diff_E_f0r : ltac2:(tb__ "0|4|
S3bS3SbS9SbS13S13A2M0A1M1S9S16A1M2A2M3A1SccSb5S76A2S5G3S1G1G2S0G0S1S13S13S11Z0A1S15P9eA1A4S2G0A1A3S2S16A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit 0, SVar 158)], @nil sprop))). Qed.
Lemma swf_E_f0r : swf E_f0r = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Local Definition MEMO_3 : ltac2:(tb__ "0|0|
S3S1bA1") := ltac2:(tb__ "0|0|
S48S76S0S47S49U0S11N50A1A2S2S47A1A3A2").
Definition E_f01 : sstate := ltac:(let x := eval vm_compute in (xget E_f0r (MEMO_3)) in exact x).
Local Lemma MEMO_3_c : MEMO_3 = Some E_f01. Proof. vm_cast_no_check (@eq_refl _ MEMO_3). Qed.
Local Lemma MEMO_3_e : ltac2:(tb__ "0|0|
S3bS3S1bA1S48S76S0S47S49U0S11N50A1A2S2S47A1A3A2S5S1bS74A2A3").
Proof. exact (@eq_trans _ (apply_xforms E_f0r [XSplit 0 (SLit (-80))]) MEMO_3 (Some E_f01) (@eq_refl _ (apply_xforms E_f0r [XSplit 0 (SLit (-80))])) MEMO_3_c). Qed.
Lemma xs_E_f01_ok : ltac2:(tb__ "0|0|
S3bS3S1bA1S48S76S0S47S49U0S11N50A1A2S2S47A1A3A2S5S1bS74A2A3"). Proof. exact MEMO_3_e. Qed.
Local Definition MEMO_4 := unbase_obj_at E_f01 0 (-80).
Definition E_f02 : sstate := ltac:(let x := eval vm_compute in (match MEMO_4 with Some s => s | None => E_f01 end) in exact x).
Local Lemma MEMO_4_c : MEMO_4 = Some E_f02. Proof. vm_cast_no_check (@eq_refl _ MEMO_4). Qed.
Local Lemma MEMO_4_e : ltac2:(tb__ "0|0|
S3bS3S1bA1S98S74U0N50A3S5S1bS6fA2A3").
Proof. exact (@eq_trans _ (unbase_obj_at E_f01 0 (-80)) MEMO_4 (Some E_f02) (@eq_refl _ (unbase_obj_at E_f01 0 (-80))) MEMO_4_c). Qed.
Lemma unb_E_f02 : ltac2:(tb__ "0|0|
S3bS3S1bA1S98S74U0N50A3S5S1bS6fA2A3"). Proof. exact MEMO_4_e. Qed.
Local Definition MEMO_5 : ltac2:(tb__ "0|0|
S3S1bA1") := ltac2:(tb__ "0|0|
S48S6fS0S47S49U9S11S8cA1A2S2S47A1A3A2").
Definition E_f03 : sstate := ltac:(let x := eval vm_compute in (xget E_f02 (MEMO_5)) in exact x).
Local Lemma MEMO_5_c : MEMO_5 = Some E_f03. Proof. vm_cast_no_check (@eq_refl _ MEMO_5). Qed.
Local Lemma MEMO_5_e : ltac2:(tb__ "0|0|
S3bS3S1bA1S48S6fS0S47S49U9S11S8cA1A2S2S47A1A3A2S5S1bS7fA2A3").
Proof. exact (@eq_trans _ (apply_xforms E_f02 [XSplit 9 (SLit stdout_buf)]) MEMO_5 (Some E_f03) (@eq_refl _ (apply_xforms E_f02 [XSplit 9 (SLit stdout_buf)])) MEMO_5_c). Qed.
Lemma xs_E_f03_ok : ltac2:(tb__ "0|0|
S3bS3S1bA1S48S6fS0S47S49U9S11S8cA1A2S2S47A1A3A2S5S1bS7fA2A3"). Proof. exact MEMO_5_e. Qed.
Local Definition MEMO_6 := obj_forget E_f03 10.
Definition E_f0x : sstate := ltac:(let x := eval vm_compute in (MEMO_6) in exact x).
Local Lemma MEMO_6_c : MEMO_6 = E_f0x. Proof. vm_cast_no_check (@eq_refl _ MEMO_6). Qed.
Local Lemma MEMO_6_e : obj_forget E_f03 10 = E_f0x.
Proof. exact (@eq_trans _ (obj_forget E_f03 10) MEMO_6 (E_f0x) (@eq_refl _ (obj_forget E_f03 10)) MEMO_6_c). Qed.
Lemma E_f0x_eq : obj_forget E_f03 10 = E_f0x. Proof. exact MEMO_6_e. Qed.
Definition O_pay0 : sobj := ltac2:(tb__ "0|0|
S1aS11Sc4A1S11Z0A1S15P9eA1S2S12A1S1cA5").

Definition E_f0a : sstate := ltac:(let x := eval vm_compute in
  (mkSS (ss_pc E_f0x) (ss_regs E_f0x) (ss_fregs E_f0x) (ss_fcsr E_f0x) (ss_resv E_f0x) (ss_objs E_f0x ++ [O_pay0]) (ss_facts E_f0x) (ss_next E_f0x) (ss_lenient E_f0x)) in exact x).
Lemma E_f0a_eq : ltac2:(tb__ "0|0|
S3bS1bS25S2cS5cA1S2fS5cA1S35S5cA1S34S5cA1S36S5cA1SaS19S23S5cA1S0S19Sd0S11Sc4A1S15P9eA1A2S2S19A1A3A3S24S5cA1S1fS5cA1S26S5cA1A9S75A3").
Proof. reflexivity. Qed.
Lemma swf_E_f0a : ltac2:(tb__ "0|0|
S3cS3bS8S2eS75A1S4A3S3cS3bS7S10S19S23S5cA1A2UbA3S3cS3bS39S1fS5cA1Pa0A3S3bS9S16A1S24S5cA1S24Sb5A1A3A2A2A2").
Proof. split; [vm_cast_no_check (@eq_refl bool true) | repeat split; reflexivity]. Qed.
Definition xs_f0e : list xform := ltac2:(tb__ "0|0|
S0S47S4cS0S7U0S0S7UbS0S7U1S0S7U2S0S7U3S0S7U4S0S7U5S0S7U6S0S7U7S0S7U8S0S7U9S0S7UaS2S7A1A3A3A3A3A3A3A3A3A3A3A3A3A1S2S47A1A3").
Local Definition MEMO_7 := apply_xforms E_f0a xs_f0e.
Definition E_f0e : sstate := ltac:(let x := eval vm_compute in (xget E_f0a (MEMO_7)) in exact x).
Local Lemma MEMO_7_c : MEMO_7 = Some E_f0e. Proof. vm_cast_no_check (@eq_refl _ MEMO_7). Qed.
Local Lemma MEMO_7_e : ltac2:(tb__ "0|0|
S3bS3S1bA1S48S75S84A2S5S1bS6aA2A3").
Proof. exact (@eq_trans _ (apply_xforms E_f0a xs_f0e) MEMO_7 (Some E_f0e) (@eq_refl _ (apply_xforms E_f0a xs_f0e)) MEMO_7_c). Qed.
Lemma xs_f0e_ok : ltac2:(tb__ "0|0|
S3bS3S1bA1S48S75S84A2S5S1bS6aA2A3"). Proof. exact MEMO_7_e. Qed.
Lemma swf_E_f0e : ltac2:(tb__ "0|0|
S3cS3bS8S2eS6aA1S4A3S3cS3bS39S1fS6aA1Pa0A3S3bS3S19A1S91S19S23S6aA1U1A3S5S19S8aA2A3A2A2"). Proof. split; [vm_cast_no_check (@eq_refl bool true) | split; reflexivity]. Qed.
Definition s_F0 : wsub := ltac:(let x := eval vm_compute in ((240%positive, SLit empty_addr) :: (241%positive, SLit 0) :: infer_sub 31 E_f0e S_0) in exact x).
Lemma ent_F0 : ltac2:(tb__ "0|0|
S3bS8S9dS6aS63S5eA3S4A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma s_F0_vals : ltac2:(tb__ "0|7|
S3cS3bS13S54S5ePf0A2S11Sc4A1A3S3cS3bS13S54S5ePf1A2S11Z0A1A3S3cS3bS13S54S5eP9eM0A2S15G0A1A3S3cS3bS13S54S5eP9fM1A2S15G1A1A3S3cS3bS13S54S5eP9dM2A2S15G2A1A3S3cS3bS13S54S5eP64M3A2S15G3A1A3S3cS3bS13S54S5eP65M4A2S15G4A1A3S3cS3bS13S54S5eP66M5A2S15G5A1A3S3bS13S54S5eP67M6A2S15G6A1A3A2A2A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma s_F0_props : ltac2:(tb__ "0|1|
S3cS3bS8S55S5eP1fA2S4A3S3bS8SadS5eS0SbS13S13A2M0S1S13S13S11Z0A1S15P9eA1A4S0G0S1S13S13S15P66A1S15P65A1A4S2G0A1A3A3S6eA3S4A3A2"). Proof. split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_0_shape : ltac2:(tb__ "0|0|
S3cS3bS3aS2cS63A1Sc5A3S3cS3bS39S1fS63A1Pf8A3S3cS3bS8S26S63A1S6A3S3bS3S19A1S91S19S23S63A1U1A3S5S19S6cA2A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Local Definition MEMO_8 : ltac2:(tb__ "0|0|
S3S1bA1") := ltac2:(tb__ "0|0|
S48S63S0S47S49U0S11N170A1A2S2S47A1A3A2").
Definition S_01 : sstate := ltac:(let x := eval vm_compute in (xget S_0 (MEMO_8)) in exact x).
Local Lemma MEMO_8_c : MEMO_8 = Some S_01. Proof. vm_cast_no_check (@eq_refl _ MEMO_8). Qed.
Local Lemma MEMO_8_e : ltac2:(tb__ "0|0|
S3bS3S1bA1S48S63S0S47S49U0S11N170A1A2S2S47A1A3A2S5S1bS78A2A3").
Proof. exact (@eq_trans _ (apply_xforms S_0 [XSplit 0 (SLit (-368))]) MEMO_8 (Some S_01) (@eq_refl _ (apply_xforms S_0 [XSplit 0 (SLit (-368))])) MEMO_8_c). Qed.
Lemma xs_S_01_ok : ltac2:(tb__ "0|0|
S3bS3S1bA1S48S63S0S47S49U0S11N170A1A2S2S47A1A3A2S5S1bS78A2A3"). Proof. exact MEMO_8_e. Qed.
Local Definition MEMO_9 := unbase_obj_at S_01 0 (-368).
Definition S_0x : sstate := ltac:(let x := eval vm_compute in (match MEMO_9 with Some s => s | None => S_01 end) in exact x).
Local Lemma MEMO_9_c : MEMO_9 = Some S_0x. Proof. vm_cast_no_check (@eq_refl _ MEMO_9). Qed.
Local Lemma MEMO_9_e : ltac2:(tb__ "0|0|
S3bS3S1bA1S98S78U0N170A3S5S1bS58A2A3").
Proof. exact (@eq_trans _ (unbase_obj_at S_01 0 (-368)) MEMO_9 (Some S_0x) (@eq_refl _ (unbase_obj_at S_01 0 (-368))) MEMO_9_c). Qed.
Lemma unb_S_0x : ltac2:(tb__ "0|0|
S3bS3S1bA1S98S78U0N170A3S5S1bS58A2A3"). Proof. exact MEMO_9_e. Qed.
Definition s_fz0 : wsub := ltac:(let x := eval vm_compute in ((15%positive, SLit (-1048000)) :: infer_sub 1 S_0x PreFZ) in exact x).
Local Definition MEMO_10 : ltac2:(tb__ "0|0|
S3S9S19A1A1") := ltac2:(tb__ "0|0|
S9cS58S72S59A3").
Definition R_fz0 : list sobj := ltac:(let x := eval vm_compute in (match MEMO_10 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_10_c : MEMO_10 = Some R_fz0. Proof. vm_cast_no_check (@eq_refl _ MEMO_10). Qed.
Local Lemma MEMO_10_e : ltac2:(tb__ "0|1|
S3bS3S9S19A1M0A1S9cS58S72S59A3S5G0S65A2A3").
Proof. exact (@eq_trans _ (entails_fr S_0x PreFZ s_fz0) MEMO_10 (Some R_fz0) (@eq_refl _ (entails_fr S_0x PreFZ s_fz0)) MEMO_10_c). Qed.
Lemma efr_fz0 : ltac2:(tb__ "0|1|
S3bS3S9S19A1M0A1S9cS58S72S59A3S5G0S65A2A3"). Proof. exact MEMO_10_e. Qed.

Lemma chk_fz0 : ltac2:(tb__ "0|4|
S3cS3bS8SafS90P1fS58S72S59S65Sa7SbS1bS9SbS13S13A2A1M0A2M1S1bSdS1bG0A2S82A4A7S4A3S3cS3bS8Sc3S59S9eA2S4A3S3cS3bS8S92G1G1SfSb3S9eS59S1fS58A1SdS1bG0R1A3M2SeS1bG0R1A3M3A5Sb1S72G2G3A3A2Ld;S82A3S4A3S3bS8Sb2S24S58A1S6eScS7A1S7cS65A5S4A3A2A2A2").
Proof. split; [vm_cast_no_check (@eq_refl bool true) | split; [vm_cast_no_check (@eq_refl bool true) | split; [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true)]]]. Qed.
Lemma s_fz0_vals : ltac2:(tb__ "0|0|
S3cS3bS13S54S59PcA2S15Pf0A1A3S3cS3bS13S54S59PdA2S15P9eA1A3S3cS3bS13S54S59PaA2S18S3eS15P1A1S11Nd0A1A3A3S3bS13S54S59PfA2S11Nffdc0A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma S_0x_call_shape : ltac2:(tb__ "0|0|
S3cS3bS3aS2cS58A1Sc5A3S3cS3bS8S26S58A1S6A3S3bS3S19A1S91S19S23S58A1U2A3S5S19S6cA2A3A2A2"). Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_11 : ltac2:(tb__ "0|0|
S1b") := ltac2:(tb__ "0|0|
SacS9eS58S59S65S96S95Sa5S3aU0S97S95A1Z0A4A2A5").
Definition P_0 : sstate := ltac:(let x := eval vm_compute in (MEMO_11) in exact x).
Local Lemma MEMO_11_c : MEMO_11 = P_0. Proof. vm_cast_no_check (@eq_refl _ MEMO_11). Qed.
Local Lemma MEMO_11_e : ltac2:(tb__ "0|0|
S3bS1bSacS9eS58S59S65S96S95Sa5S3aU0S97S95A1Z0A4A2A5S5bA3").
Proof. exact (@eq_trans _ (T_afterN NF S_0x s_fz0 R_fz0 (L_fuzz FZ_U (nth 0 (fz_rets FZ_U) 0))) MEMO_11 (P_0) (@eq_refl _ (T_afterN NF S_0x s_fz0 R_fz0 (L_fuzz FZ_U (nth 0 (fz_rets FZ_U) 0)))) MEMO_11_c). Qed.
Lemma P_0_eq : ltac2:(tb__ "0|0|
S3bS1bSacS9eS58S59S65S96S95Sa5S3aU0S97S95A1Z0A4A2A5S5bA3"). Proof. exact MEMO_11_e. Qed.

Local Definition MEMO_12 : ltac2:(tb__ "0|0|
S1b") := ltac2:(tb__ "0|1|
Sa2S5bSa3S90S1fS5bA1M0A2S9aG0A1A3").
Definition P_0S : sstate := ltac:(let x := eval vm_compute in (MEMO_12) in exact x).
Local Lemma MEMO_12_c : MEMO_12 = P_0S. Proof. vm_cast_no_check (@eq_refl _ MEMO_12). Qed.
Local Lemma MEMO_12_e : ltac2:(tb__ "0|1|
S3bS1bSa2S5bSa3S90S1fS5bA1M0A2S9aG0A1A3S68A3").
Proof. exact (@eq_trans _ (app_objs P_0 (statics_objs C_U (ss_next P_0)) (Pos.succ (ss_next P_0))) MEMO_12 (P_0S) (@eq_refl _ (app_objs P_0 (statics_objs C_U (ss_next P_0)) (Pos.succ (ss_next P_0)))) MEMO_12_c). Qed.
Lemma P_0S_eq : ltac2:(tb__ "0|1|
S3bS1bSa2S5bSa3S90S1fS5bA1M0A2S9aG0A1A3S68A3"). Proof. exact MEMO_12_e. Qed.
Lemma swf_P_0S : swf P_0S = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_P_0 : ltac2:(tb__ "0|1|
S3bS8Sc9S90S24S5bA1S6eSaS19Sa4S19U2S23S5bA1M0A3Sa6S19U3G0A3A3A4S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma P_0S_shape : ltac2:(tb__ "0|0|
S3cS3bS39S1fS68A1S9aS1fS5bA1A1A3S3cS3bS8S26S68A1S6A3S3bS3S19A1S91S19S23S5bA1U2A3S5S19S6cA2A3A2A2"). Proof. repeat split; reflexivity. Qed.
Definition NX0 : positive := ltac:(let x := eval vm_compute in (ss_next P_0) in exact x).

Local Definition MEMO_13 : ltac2:(tb__ "0|0|
S3S9S4dA1A1") := ltac2:(tb__ "0|0|
S50S8bS94S62S68S4A5").
Definition E_io : sstate := ltac:(let x := eval vm_compute in (lf0 P_0S (MEMO_13) 0) in exact x).
Local Lemma MEMO_13_c : ltac2:(tb__ "0|1|
S3bS3S9S4dA1M0A1S87S5G0S0S4dS4eS56S52A2S2S4dA1A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_13). Qed.
Local Lemma MEMO_13_e : ltac2:(tb__ "0|1|
S3bS3S9S4dA1M0A1S50S8bS94S62S68S4A5S5G0S0S4dS4eS56S52A2S2S4dA1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL LCUTS P_0S true) MEMO_13 (Some [mkLeaf E_io RsEcall]) (@eq_refl _ (sym_run segs FUEL LCUTS P_0S true)) MEMO_13_c). Qed.
Lemma run_P0 : ltac2:(tb__ "0|1|
S3bS3S9S4dA1M0A1S50S8bS94S62S68S4A5S5G0S0S4dS4eS56S52A2S2S4dA1A3A2A3").
Proof. exact MEMO_13_e. Qed.
Definition P_0b : sstate := ltac:(let x := eval vm_compute in (T_afterN NF S_0x s_fz0 R_fz0 (L_fuzz FZ_U (nth 1 (fz_rets FZ_U) 0))) in exact x).
Lemma P_0b_eq : T_afterN NF S_0x s_fz0 R_fz0 (L_fuzz FZ_U (nth 1 (fz_rets FZ_U) 0)) = P_0b.
Proof. vm_cast_no_check (@eq_refl _ P_0b). Qed.
Definition P_0bS : sstate := ltac:(let x := eval vm_compute in (app_objs P_0b (statics_objs C_U (ss_next P_0b)) (Pos.succ (ss_next P_0b))) in exact x).
Lemma P_0bS_eq : app_objs P_0b (statics_objs C_U (ss_next P_0b)) (Pos.succ (ss_next P_0b)) = P_0bS.
Proof. vm_cast_no_check (@eq_refl _ P_0bS). Qed.
Lemma swf_P_0bS : swf P_0bS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_P_0b : robjs_missT_statics C_U (ss_facts P_0b) tvL (firstn 2 (ss_objs P_0b) ++ skipn 3 (ss_objs P_0b)) = true.
Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma run_P0b : sym_run Code.segs FUEL LCUTS P_0bS true = sym_run Code.segs FUEL LCUTS P_0S true.
Proof. vm_cast_no_check (@eq_refl _ (sym_run Code.segs FUEL LCUTS P_0S true)). Qed.
Lemma posts_0 : ltac2:(tb__ "0|5|
S3aS93S3aR1S97S95A1A3S3dS1bS1bS3dS1bS1bS3cS3bS1bSacS9eS58S59S65S96S95R4A2A5R2A3S3cS3bS1bSa2R2Sa3S90S1fR2A1M0A2S9aG0A1A3R1A3S3cS3bS8S2eR1A1S4A3S3cS3bS8Sc9S90S24R2A1S6eSaS19Sa4S19U2S23R2A1M1A3M2Sa6S19U3G1A3M3A3A4S4A3S3cS3bS9S19A1G1SaS19G2S0S19S6cG3A3A3A3S3cS3bS39G0S70A3S3cS3bS39S1fR1A1S9aS70A1A3S3cS3bS8S26R1A1S6A3S3bS3S9S4dA1M4A1S50S8bS94S62R1S4A5S5G4S0S4dS4eS56S52A2S2S4dA1A3A2A3A2A2A2A2A2A2A2A2LPS;A2LP;A2F_;Fr;").
Proof.
  intros r Hr. cbn [fz_rets FZ_U] in Hr.
  destruct Hr as [<-|[<-|[]]]; [exists P_0, P_0S; split; [exact P_0_eq | split; [exact P_0S_eq | split; [exact swf_P_0S | split; [exact missT_P_0 | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | exact run_P0]]]]]]]] | exists P_0b, P_0bS; split; [exact P_0b_eq | split; [exact P_0bS_eq | split; [exact swf_P_0bS | split; [exact missT_P_0b | split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity | rewrite run_P0b; exact run_P0]]]]]]]]].
Qed.
Lemma cert_io : ltac2:(tb__ "0|1|
S3cS3bS3S45A1S53S8bS2cS56A1M0A2S5S45S46A2A3S3cS3bS3aG0S8fA3S3cS3bS13S2dS56Z11A2S11Z1dA1A3S3cS3bS13S2dS56ZaA2S11Z1A1A3S3bS13S2dS56ZbA2S11Z5413A1A3A2A2A2A2").
Proof. split; [vm_cast_no_check (@eq_refl _ (Some Ecall)) | repeat split; reflexivity]. Qed.
Local Definition MEMO_14 : ltac2:(tb__ "0|0|
S1b") := ltac2:(tb__ "0|0|
SbfS56S11Sc6Q40SbdSbcA1A2A1S23S56A1S1fS56A1A4").
Definition P_io : sstate := ltac:(let x := eval vm_compute in (MEMO_14) in exact x).
Local Lemma MEMO_14_c : MEMO_14 = P_io. Proof. vm_cast_no_check (@eq_refl _ MEMO_14). Qed.
Local Lemma MEMO_14_e : ltac2:(tb__ "0|0|
S3bS1bSbfS56S11Sc6Q40SbdSbcA1A2A1S23S56A1S1fS56A1A4S64A3").
Proof. exact (@eq_trans _ (S_after E_io (SLit (bv_unsigned (errno_ret ENOTTY))) (ss_objs E_io) (ss_next E_io)) MEMO_14 (P_io) (@eq_refl _ (S_after E_io (SLit (bv_unsigned (errno_ret ENOTTY))) (ss_objs E_io) (ss_next E_io))) MEMO_14_c). Qed.
Lemma P_io_eq : ltac2:(tb__ "0|0|
S3bS1bSbfS56S11Sc6Q40SbdSbcA1A2A1S23S56A1S1fS56A1A4S64A3"). Proof. exact MEMO_14_e. Qed.
Lemma P_io_shape : ltac2:(tb__ "0|0|
S3cS3bS39S1fS64A1S1fS56A1A3S3bS8S26S64A1S6A3A2"). Proof. split; reflexivity. Qed.
Local Definition MEMO_15 : ltac2:(tb__ "0|0|
S3S9S4dA1A1") := ltac2:(tb__ "0|0|
S50S8bS94S62S64S4A5").
Definition E_w : sstate := ltac:(let x := eval vm_compute in (lf0 P_io (MEMO_15) 0) in exact x).
Local Lemma MEMO_15_c : ltac2:(tb__ "0|1|
S3bS3S9S4dA1M0A1S88S5G0S0S4dS4eS57S52A2S2S4dA1A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_15). Qed.
Local Lemma MEMO_15_e : ltac2:(tb__ "0|1|
S3bS3S9S4dA1M0A1S50S8bS94S62S64S4A5S5G0S0S4dS4eS57S52A2S2S4dA1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL LCUTS P_io true) MEMO_15 (Some [mkLeaf E_w RsEcall]) (@eq_refl _ (sym_run segs FUEL LCUTS P_io true)) MEMO_15_c). Qed.
Lemma run_Pio : ltac2:(tb__ "0|1|
S3bS3S9S4dA1M0A1S50S8bS94S62S64S4A5S5G0S0S4dS4eS57S52A2S2S4dA1A3A2A3").
Proof. exact MEMO_15_e. Qed.
Lemma E_w_shape : ltac2:(tb__ "0|2|
S3cS3bS3aS2cS57A1SbbA3S3cS3bS39S1fS57A1S1fS56A1A3S3cS3bS13S2dS57ZdA2S11Z1M0A1A3S3cS3bS13S2dS57ZcA2S11Z2A1A3S3bS3S19A1S91S19S23S57A1UcA3S5S19S1aS11Z0A1S11S8cA1M1S11S9fS8cZ400A2A1S0S12S14G1G0S11Z30A1A3S2S12A1A3S1cA5A2A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition xs_w : list xform := ltac2:(tb__ "0|2|
S0S47S49U1M0S11N318A1A2S0S47S49G0S11N338A1A2S0S47S49U9M1S11S9fS8eZ4A2A1A2S0S47S49G1S11S8eA1A2S0S47S49U10S11S9fS8cZ1A2A1A2S2S47A1A3A3A3A3A3").
Local Definition MEMO_16 := apply_xforms E_w xs_w.
Definition E_w1 : sstate := ltac:(let x := eval vm_compute in (xget E_w (MEMO_16)) in exact x).
Local Lemma MEMO_16_c : MEMO_16 = Some E_w1. Proof. vm_cast_no_check (@eq_refl _ MEMO_16). Qed.
Local Lemma MEMO_16_e : ltac2:(tb__ "0|0|
S3bS3S1bA1S48S57S85A2S5S1bS77A2A3").
Proof. exact (@eq_trans _ (apply_xforms E_w xs_w) MEMO_16 (Some E_w1) (@eq_refl _ (apply_xforms E_w xs_w)) MEMO_16_c). Qed.
Lemma xs_w_ok : ltac2:(tb__ "0|0|
S3bS3S1bA1S48S57S85A2S5S1bS77A2A3"). Proof. exact MEMO_16_e. Qed.
Local Definition MEMO_17 := unbase_obj_at E_w1 2 (-832).
Definition E_w2 : sstate := ltac:(let x := eval vm_compute in (match MEMO_17 with Some s => s | None => E_w1 end) in exact x).
Local Lemma MEMO_17_c : MEMO_17 = Some E_w2. Proof. vm_cast_no_check (@eq_refl _ MEMO_17). Qed.
Local Lemma MEMO_17_e : ltac2:(tb__ "0|0|
S3bS3S1bA1S98S77U2N340A3S5S1bS6bA2A3").
Proof. exact (@eq_trans _ (unbase_obj_at E_w1 2 (-832)) MEMO_17 (Some E_w2) (@eq_refl _ (unbase_obj_at E_w1 2 (-832))) MEMO_17_c). Qed.
Lemma unb_w : ltac2:(tb__ "0|0|
S3bS3S1bA1S98S77U2N340A3S5S1bS6bA2A3"). Proof. exact MEMO_17_e. Qed.

Local Definition MEMO_18 := obj_to_list E_w2 16 5.
Definition E_w3 : sstate := ltac:(let x := eval vm_compute in (MEMO_18) in exact x).
Local Lemma MEMO_18_c : MEMO_18 = E_w3. Proof. vm_cast_no_check (@eq_refl _ MEMO_18). Qed.
Local Lemma MEMO_18_e : obj_to_list E_w2 16 5 = E_w3.
Proof. exact (@eq_trans _ (obj_to_list E_w2 16 5) MEMO_18 (E_w3) (@eq_refl _ (obj_to_list E_w2 16 5)) MEMO_18_c). Qed.
Lemma E_w3_eq : obj_to_list E_w2 16 5 = E_w3. Proof. exact MEMO_18_e. Qed.
Definition BL_w : list bexp := ltac2:(tb__ "0|0|
S0Sa8Sa9Z30A1S2Sa8A1A3").
Lemma obj14_w : ltac2:(tb__ "0|8|
S3cS3bS3S19A1S91S19S23S6bA1U10A3S5S19S1aS11Z0M0A1S11S8cA1M1S11S9fS8cZ1M2A2A1S0S12S14G1G2S11Z30M3A1A3S2S12A1A3M4S1cA5A2A3S3cS3bS3S9Sa8A1M5A1SabG4G1G0U1A4S5G5S7eA2A3S30S3bS9Sc8Q8M6A1M7A1Sa7Sa8G7SaaR1A1S7eA4S0G7Sc7G6G3A2S2G7A1A3A3Frho;A2A2").
Proof. split; [reflexivity | split; [vm_cast_no_check (@eq_refl _ (Some BL_w)) | intros rho; reflexivity]]. Qed.
Lemma norl_w : ltac2:(tb__ "0|0|
S3cS3bS8Sc0P5S6bA2S6A3S3bS8Sc0P6S67A2S6A3A2"). Proof. split; vm_cast_no_check (@eq_refl _ false). Qed.
Definition O_nl : sobj := ltac2:(tb__ "0|0|
S1aS11S8dA1S11Z0A1S11Z1A1S2S12A1S31P6A1A5").
Definition E_wc : sstate := ltac:(let x := eval vm_compute in (app_objs E_w3 [O_nl] (ss_next E_w3)) in exact x).
Lemma E_wc_eq : ltac2:(tb__ "0|0|
S3bS1bSa2S67S0S19S81S2S19A1A3S1fS67A1A3S5aA3"). Proof. reflexivity. Qed.
Lemma swf_E_wc : swf E_wc = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma rom_nl : ltac2:(tb__ "0|2|
S3bS8SceS8bS8dS0Sc8Q8M0A1M1Sc7G0ZaA2S2G1A1A3A3S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_nl : ltac2:(tb__ "0|1|
S3bS8ScaS90S24S57A1S6eS8dS9fS8dZ1A2SaS19Sa4S19U4S23S67A1M0A3Sa6S19U5G0A3A3A6S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma E_w_facts : ltac2:(tb__ "0|6|
S3cS3bS9S16A1M0S24S5aA1S24S57A1M1A3S3cS3bG0S24S67A1G1A3S3cS3bG0S24S6bA1G1A3S3cS3bS39S1fS5aA1S1fS57A1M2A3S3cS3bS39S1fS67A1G2A3S3cS3bS39S1fS6bA1G2A3S3cS3bS3S19A1M3S91S19S23S67A1U4M4A3S5S19S6cA2M5A3S3bG3S91S19S23S5aA1G4A3G5A3A2A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition s_w : wsub := ltac2:(tb__ "0|8|
S0SbS39S13A2M0S1S39S13PcS11Z5a7a0A1A4M1S0G0S1S39S13PdS11Z1A1M2A4M3S0G0S1S39S13PeS11Z103c7A1M4A4M5S0G0S1S39S13PfG2A4M6S0G0G5S0G0G3S0G0G1S0G0S1S39S13P5bS15P13fA1A4S0G0S1S39S13P5aS15P13eA1A4S0G0S1S39S13P59S15P13dA1A4S0G0S1S39S13P58S15P13cA1A4S0G0S1S39S13P57S15P93A1A4S0G0S1S39S13P56S15P92A1A4S0G0S1S39S13P55S15P91A1A4S0G0S1S39S13P54S15P90A1A4S0G0S1S39S13P53S15P8fA1A4S0G0S1S39S13P52S15P8eA1A4S0G0S1S39S13P51S15P8dA1A4S0G0S1S39S13P50S15P8cA1A4S0G0S1S39S13P4fS15P8bA1A4S0G0S1S39S13P4eS15P8aA1A4S0G0S1S39S13P4dS15P131A1A4S0G0S1S39S13P4cS15P130A1A4S0G0S1S39S13P4bS15P12fA1A4S0G0S1S39S13P4aS15P12eA1A4S0G0S1S39S13P49S15P12dA1A4S0G0S1S39S13P48S15P12cA1A4S0G0S1S39S13P47S15P12bA1A4S0G0S1S39S13P46S15P12aA1A4S0G0S1S39S13P45S15P81A1A4S0G0S1S39S13P44S15P80A1A4S0G0S1S39S13P43S15P127A1A4S0G0S1S39S13P42S15P126A1A4S0G0S1S39S13P41S15P125A1A4S0G0S1S39S13P40S15P124A1A4S0G0S1S39S13P3fS15P123A1A4S0G0S1S39S13P3eS15P122A1A4S0G0S1S39S13P3dS15P121A1A4S0G0S1S39S13P3cS15P120A1A4S0G0S1S39S13P33S15P117A1A4S0G0S1S39S13P32S15P116A1A4S0G0S1S39S13P31S15P115A1A4S0G0S1S39S13P30S15P114A1A4S0G0S1S39S13P2fG2A4S0G0S1S39S13P2eG2A4S0G0S1S39S13P2dS11Z0A1M7A4S0G0S1S39S13P2cG2A4S0G0S1S39S13P2bG4A4S0G0S1S39S13P29S11Z5a338A1A4S0G0S1S39S13P28G7A4S0G0S1S39S13P24S11Z29e80A1A4S0G0S1S39S13P23G2A4S0G0S1S39S13P22S11Z5413A1A4S0G0S1S39S13P21G2A4S0G0G6S0G0S1S39S13P1bS15PffA1A4S0G0S1S39S13P1aS15PfeA1A4S0G0S1S39S13P19G7A4S0G0S1S39S13P18S11Z3a0d0A1A4S0G0S1S39S13PaS18S3eS15P1A1S11N580A1A3A4S0G0S1S39S13P15S11Z228f4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Local Definition MEMO_19 : ltac2:(tb__ "0|0|
S3S9S19A1A1") := ltac2:(tb__ "0|0|
S9cS5aSbaS61A3").
Definition R_w : list sobj := ltac:(let x := eval vm_compute in (match MEMO_19 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_19_c : MEMO_19 = Some R_w. Proof. vm_cast_no_check (@eq_refl _ MEMO_19). Qed.
Local Lemma MEMO_19_e : ltac2:(tb__ "0|1|
S3bS3S9S19A1M0A1S9cS5aSbaS61A3S5G0S6dA2A3").
Proof. exact (@eq_trans _ (entails_fr E_wc WLoutS.Pre_wl2 s_w) MEMO_19 (Some R_w) (@eq_refl _ (entails_fr E_wc WLoutS.Pre_wl2 s_w)) MEMO_19_c). Qed.
Lemma efr_w : ltac2:(tb__ "0|1|
S3bS3S9S19A1M0A1S9cS5aSbaS61A3S5G0S6dA2A3"). Proof. exact MEMO_19_e. Qed.
Lemma chk_w : ltac2:(tb__ "0|0|
S3bS8Sc2S5aSbaS61S6dS0S4dS4eSb9S51A2S2S4dA1A3A5S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma fb_w : ltac2:(tb__ "0|0|
S3bS8S92S16S33S1fS5aA1A1S24S57A1A3S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma s_w_vals : ltac2:(tb__ "0|1|
S3cS3bS13S54S61PcA2S11S8cA1A3S3cS3bS13S54S61PdA2S11Z1A1M0A3S3cS3bS13S54S61PeA2S11S8dA1A3S3bS13S54S61PfA2G0A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_20 : ltac2:(tb__ "0|0|
S1b") := ltac2:(tb__ "0|0|
Sc1S61P5cSb9S1fS5aA1S6dA5").
Definition T_wDi : sstate := ltac:(let x := eval vm_compute in (MEMO_20) in exact x).
Local Lemma MEMO_20_c : MEMO_20 = T_wDi. Proof. vm_cast_no_check (@eq_refl _ MEMO_20). Qed.
Local Lemma MEMO_20_e : ltac2:(tb__ "0|0|
S3bS1bSc1S61P5cSb9S1fS5aA1S6dA5S66A3").
Proof. exact (@eq_trans _ (import_post s_w 92 WLoutS.D (ss_next E_wc) R_w) MEMO_20 (T_wDi) (@eq_refl _ (import_post s_w 92 WLoutS.D (ss_next E_wc) R_w)) MEMO_20_c). Qed.
Lemma T_wDi_eq : ltac2:(tb__ "0|0|
S3bS1bSc1S61P5cSb9S1fS5aA1S6dA5S66A3"). Proof. exact MEMO_20_e. Qed.

Definition xs_wd : list xform := ltac2:(tb__ "0|7|
S0S47S4bU0M0A1S0S47S4bU5M1A1S0S47S4bU6M2A1S0S47S4cS0S7U4S0S7G1S0S7G0S0S7G2S0S7U7M3S0S7U8S0S7U9S0S7UaS0S7UbS0S7UcS0S7U3S0S7UdS0S7UeS0S7UfS0S7U10S0S7U11S0S7U1M4S0S7U12S0S7U13S0S7U14S0S7U15S0S7U2S2S7A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S47S4aG4A1M5S0S47G5S0S47S4aG3A1M6S0S47G6S2S47A1A3A3A3A3A3A3A3A3").
Local Definition MEMO_21 : ltac2:(tb__ "0|0|
S3S1bA1") := ltac2:(tb__ "0|0|
S48SbeS24S57A1S66A2S7dA2").
Definition T_wDm : sstate := ltac:(let x := eval vm_compute in (xget T_wDi (MEMO_21)) in exact x).
Local Lemma MEMO_21_c : MEMO_21 = Some T_wDm. Proof. vm_cast_no_check (@eq_refl _ MEMO_21). Qed.
Local Lemma MEMO_21_e : ltac2:(tb__ "0|0|
S3bS3S1bA1S48SbeS24S57A1S66A2S7dA2S5S1bS7aA2A3").
Proof. exact (@eq_trans _ (apply_xforms (add_facts (ss_facts E_w) T_wDi) xs_wd) MEMO_21 (Some T_wDm) (@eq_refl _ (apply_xforms (add_facts (ss_facts E_w) T_wDi) xs_wd)) MEMO_21_c). Qed.
Lemma xs_wd_ok : ltac2:(tb__ "0|0|
S3bS3S1bA1S48SbeS24S57A1S66A2S7dA2S5S1bS7aA2A3"). Proof. exact MEMO_21_e. Qed.
Lemma fb_wd : ltac2:(tb__ "0|0|
S3bS8S92S16S33S1fS66A1A1S24S57A1A3S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Local Definition MEMO_22 := unbase_obj_at T_wDm 1 (-608).
Definition T_wDu : sstate := ltac:(let x := eval vm_compute in (match MEMO_22 with Some s => s | None => T_wDm end) in exact x).
Local Lemma MEMO_22_c : MEMO_22 = Some T_wDu. Proof. vm_cast_no_check (@eq_refl _ MEMO_22). Qed.
Local Lemma MEMO_22_e : ltac2:(tb__ "0|0|
S3bS3S1bA1S98S7aU1N260A3S5S1bS83A2A3").
Proof. exact (@eq_trans _ (unbase_obj_at T_wDm 1 (-608)) MEMO_22 (Some T_wDu) (@eq_refl _ (unbase_obj_at T_wDm 1 (-608))) MEMO_22_c). Qed.
Lemma unb_wd : ltac2:(tb__ "0|0|
S3bS3S1bA1S98S7aU1N260A3S5S1bS83A2A3"). Proof. exact MEMO_22_e. Qed.

Local Definition MEMO_23 := obj_forget T_wDu 12.
Definition T_wDf : sstate := ltac:(let x := eval vm_compute in (MEMO_23) in exact x).
Local Lemma MEMO_23_c : MEMO_23 = T_wDf. Proof. vm_cast_no_check (@eq_refl _ MEMO_23). Qed.
Local Lemma MEMO_23_e : obj_forget T_wDu 12 = T_wDf.
Proof. exact (@eq_trans _ (obj_forget T_wDu 12) MEMO_23 (T_wDf) (@eq_refl _ (obj_forget T_wDu 12)) MEMO_23_c). Qed.
Lemma T_wDf_eq : obj_forget T_wDu 12 = T_wDf. Proof. exact MEMO_23_e. Qed.

Definition O_b1z : sobj := ltac2:(tb__ "0|0|
S1aS11Z0A1S11S8cA1S11S9fS8cZ1A2A1S2S12A1S1cA5").
Local Definition MEMO_24 := reshape_obj_at T_wDf 12 O_b1z.
Definition T_wDr : sstate := ltac:(let x := eval vm_compute in (MEMO_24) in exact x).
Local Lemma MEMO_24_c : MEMO_24 = T_wDr. Proof. vm_cast_no_check (@eq_refl _ MEMO_24). Qed.
Local Lemma MEMO_24_e : ltac2:(tb__ "0|0|
S3bS1bS99S79UcS7bA3S73A3").
Proof. exact (@eq_trans _ (reshape_obj_at T_wDf 12 O_b1z) MEMO_24 (T_wDr) (@eq_refl _ (reshape_obj_at T_wDf 12 O_b1z)) MEMO_24_c). Qed.
Lemma T_wDr_eq : ltac2:(tb__ "0|1|
S3cS3bS1bS99S79UcM0S7bA3S73A3S3cS3bS3S19A1S91S19S23S79A1G0A3S5S19S1aS11S8cA1S11Z0A1S11Z1A1S2S12A1S1cA5A2A3S3bS8S38S1fS79A1S7bA2S4A3A2A2").
Proof. split; [exact MEMO_24_e | split; [reflexivity | vm_cast_no_check (@eq_refl bool true)]]. Qed.
Local Definition MEMO_25 : ltac2:(tb__ "0|0|
S3S1bA1") := ltac2:(tb__ "0|0|
S48S73S0S47S4aUcA1S2S47A1A3A2").
Definition T_wM : sstate := ltac:(let x := eval vm_compute in (xget T_wDr (MEMO_25)) in exact x).
Local Lemma MEMO_25_c : MEMO_25 = Some T_wM. Proof. vm_cast_no_check (@eq_refl _ MEMO_25). Qed.
Local Lemma MEMO_25_e : ltac2:(tb__ "0|0|
S3bS3S1bA1S48S73S0S47S4aUcA1S2S47A1A3A2S5S1bS60A2A3").
Proof. exact (@eq_trans _ (apply_xforms T_wDr [XMerge 12]) MEMO_25 (Some T_wM) (@eq_refl _ (apply_xforms T_wDr [XMerge 12])) MEMO_25_c). Qed.
Lemma xs_wm_ok : ltac2:(tb__ "0|0|
S3bS3S1bA1S48S73S0S47S4aUcA1S2S47A1A3A2S5S1bS60A2A3"). Proof. exact MEMO_25_e. Qed.

Definition T_w : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc T_wM) (ss_regs T_wM) (ss_fregs T_wM) (ss_fcsr T_wM) (ss_resv T_wM) (firstn 16 (ss_objs T_wM)) (ss_facts T_wM) (ss_next T_wM) (ss_lenient T_wM)) in exact x).
Lemma T_wM_objs : ltac2:(tb__ "0|0|
S3cS3bS9S19A1S23S60A1SaS19S23S5dA1S0S19S81S2S19A1A3A3A3S3bS8S2eS5dA1S4A3A2"). Proof. split; [reflexivity | vm_cast_no_check (@eq_refl _ true)]. Qed.
Lemma T_w_shape : ltac2:(tb__ "0|1|
S3cS3bS39S1fS5dA1S1fS66A1A3S3cS3bS8S26S5dA1S6A3S3cS3bS3S19A1S91S19S23S5dA1M0U2A3S5S19S6cA2A3S3bS9S19A1G0SaS19Sa4S19UdG0A3Sa3S90S1fS5bA1A2A3A3A2A2A2").
Proof. repeat split; reflexivity. Qed.

Lemma nexts_w : ltac2:(tb__ "0|2|
S3cS3bS39S1fS56A1S9aS70A1M0A3S3cS3bS39S1fS64A1G0A3S3cS3bS39S1fS57A1G0A3S3cS3bS39S1fS5aA1G0A3S3cS3bS8S9bS70S1fS66A1M1A2S4A3S3cS3bS39S1fS5dA1G1A3S3bS8S9bPf1S70A2S4A3A2A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma T_w_eq : ltac2:(tb__ "0|0|
S3bS1bS25S2cS60A1S2fS60A1S35S60A1S34S60A1S36S60A1S23S5dA1S24S60A1S1fS60A1S26S60A1A9S5dA3").
Proof. reflexivity. Qed.

Local Definition MEMO_26 : ltac2:(tb__ "0|0|
S3S9S4dA1A1") := ltac2:(tb__ "0|0|
S50S8bS94S62S5dS4A5").
Definition LVS_0 : list leaf := ltac:(let x := eval vm_compute in (match MEMO_26 with Some l => l | None => [] end) in exact x).
Definition N_1 : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 0 LVS_0 (mkLeaf T_w RsFuel))) in exact x).
Definition X_1 : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 1 LVS_0 (mkLeaf T_w RsFuel))) in exact x).
Local Lemma MEMO_26_c : ltac2:(tb__ "0|1|
S3bS3S9S4dA1M0A1S89S5G0S0S4dS4eS71S51A2S0S4dS4eS69S51A2S2S4dA1A3A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_26). Qed.
Local Lemma MEMO_26_e : ltac2:(tb__ "0|1|
S3bS3S9S4dA1M0A1S50S8bS94S62S5dS4A5S5G0S0S4dS4eS71S51A2S0S4dS4eS69S51A2S2S4dA1A3A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL LCUTS T_w true) MEMO_26 (Some [mkLeaf N_1 RsCut; mkLeaf X_1 RsCut]) (@eq_refl _ (sym_run segs FUEL LCUTS T_w true)) MEMO_26_c). Qed.
Lemma run_Tw : ltac2:(tb__ "0|1|
S3bS3S9S4dA1M0A1S50S8bS94S62S5dS4A5S5G0S0S4dS4eS71S51A2S0S4dS4eS69S51A2S2S4dA1A3A3A2A3").
Proof. exact MEMO_26_e. Qed.
Lemma fork_1 : ltac2:(tb__ "0|4|
S3cS3bS3S16A1M0S91S16S24S71A1U0M1A3S5S16S1eS44S18S3eS15P9fA1S11N1A1A3S11Z0A1A3M2A2A3S3cS3bG0S91S16S24S69A1G1A3S5S16S22G2A1A2A3S3cS3bS3aS2cS69A1ScbA3S3cS3bS13S2dS69ZaA2S15Pf1A1A3S3cS3bS39S1fS69A1S1fS5dA1M3A3S3bS39S1fS71A1G3A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

