(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "false"; "true"; "nat"; "option"; "Some"; "bool"; "list"; "None"; "app"; "prod"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "cell"; "mkCell"; "sv"; "SVar"; "sprop"; "SPUle"; "SAlu"; "sobj"; "mkObj"; "SPBranch"; "DUnknown"; "SExt"; "DImage"; "SPAlign"; "SPNot"; "sstate"; "ss_next"; "ss_facts"; "DZero"; "FcsrFrm0"; "SLBytes"; "SPEq"; "SPUlt"; "mkSS"; "ss_objs"; "ss_lenient"; "ss_pc"; "reg_sv"; "swf"; "obj_wf"; "sprop_eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "ALU_SRL"; "BC_EQ"; "ALU_OR"; "ALU_SLL"; "BC_NE"; "BC_LT"; "instr"; "Ecall"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "mkLeaf"; "RsCut"; "sym_run"; "set_objs"; "RsEcall"; "instr_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XRebase"; "apply_xforms"; "XMerge"; "XSelect"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hx1_states"; "C_1x"; "XB12"; "T_1Bt"; "C_1"; "T_1f"; "s_fb1"; "s_ff1"; "XA10"; "R_fb1"; "R_ff1"; "T_1BS"; "T_1fS"; "ECUTS"; "E_x1"; "XA1a"; "XA1a2"; "XA1b"; "XA1b2"; "XB1a"; "XB1b"; "XB1r"; "C_1m"; "T_1B"; "XA1a1"; "XA1a3"; "XA1a4"; "XA1b1"; "XA1b3"; "XA1b4"; "XB10"; "XB11"; "XB1a4"; "XB1b4"; "xs_xa"; "O_payB"; "s_CAa1"; "s_CAb1"; "s_CBa1"; "s_CBb1"; "xs_fo"; "MEMO_1"; "MEMO_12"; "MEMO_18"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics"; "statics_objs"; "app_objs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_hl0_states"; "X_1"; "O_payL"; "NX0"; "robj_inwi"; "tvL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht_states"; "tvK"; "PreF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states"; "FUEL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "reshape_obj_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_U"; "L_free"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "tv_sub_eqb"; "robjs_check"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states.RAddr"; "free_entry"; "@Corelib.Lists.ListDef"; "firstn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "call_checkP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvLoop"; "robjs_missT_statics"; "@Stdlib.Lists.List"; "nth_error"; "existsb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"].
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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Code Drv_wins.
Require Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_err OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Musl_wl__G1.Musl_wl_out OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_m__G1.Drv_m_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_r__G1.Drv_r_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_h__G1.Drv_h_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_ht__G1.Drv_ht_states.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Drv_hl0_states.
Import ListNotations.

Import MAddr RAddr StrAddr HAddr TAddr LAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ECUTS : list Z := [free_entry].

Lemma X_1_objs : ltac2:(tb__ "0|1|
S3aS39S9S15A1S26S75A1M0SbS15S8bS15UdG0A3S73S72S77A2A3A3S3aS39S6S15A1S8eS15G0U2A3S7S15S76A2A3S3aS39S8S27S75A1S3A3S3aS39S10S29S75ZaA2S11Pf1A1A3S39S38S28S75A1S8aA3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Definition XA10 : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc X_1) (list_set (ss_regs X_1) 10 (SLit 0)) (ss_fregs X_1) (ss_fcsr X_1) (ss_resv X_1) (ss_objs X_1) (ss_facts X_1) (ss_next X_1) false) in exact x).
Lemma diff_XA10 : ltac2:(tb__ "0|4|
S3aS39S6ScS9ScS10S10A2M0A1M1S9S12A1M2A2M3A1S90S75S4eA2S7G3S1G1G2S0G0S1S10S10S11Pf1A1SdZ0A1A4S2G0A1A3S2S12A1A4A2A3S3aS39S8S2aS4eA1S4A3S3aS39S8S27S4eA1S3A3S39S37S1eS4eA1S1eS75A1A3A2A2A2").
Proof. split; [vm_cast_no_check (@eq_refl _ (Some ([(SVar 241, SLit 0)], @nil sprop))) | split; [vm_cast_no_check (@eq_refl bool true) | split; reflexivity]]. Qed.
Local Definition MEMO_1 : ltac2:(tb__ "0|0|
S6S9S3bA1A1") := ltac2:(tb__ "0|0|
S3eS7aS7dS53S4eS4A5").
Definition LVA1 : list leaf := ltac:(let x := eval vm_compute in (match MEMO_1 with Some l => l | None => [] end) in exact x).
Definition XA1a : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 0 LVA1 (mkLeaf XA10 RsFuel))) in exact x).
Definition XA1b : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 1 LVA1 (mkLeaf XA10 RsFuel))) in exact x).
Local Lemma MEMO_1_c : ltac2:(tb__ "0|1|
S39S6S9S3bA1M0A1S6fS7G0S0S3bS3cS55S3dA2S0S3bS3cS57S3dA2S2S3bA1A3A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_1). Qed.
Local Lemma MEMO_1_e : ltac2:(tb__ "0|1|
S39S6S9S3bA1M0A1S3eS7aS7dS53S4eS4A5S7G0S0S3bS3cS55S3dA2S0S3bS3cS57S3dA2S2S3bA1A3A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL ECUTS XA10 true) MEMO_1 (Some [mkLeaf XA1a RsCut; mkLeaf XA1b RsCut]) (@eq_refl _ (sym_run segs FUEL ECUTS XA10 true)) MEMO_1_c). Qed.
Lemma run_XA10 : ltac2:(tb__ "0|1|
S39S6S9S3bA1M0A1S3eS7aS7dS53S4eS4A5S7G0S0S3bS3cS55S3dA2S0S3bS3cS57S3dA2S2S3bA1A3A3A2A3").
Proof. exact MEMO_1_e. Qed.

Definition xs_xa : list xform := ltac2:(tb__ "0|11|
S0S42S46S0S5U0M0S0S5U1M1S0S5U3M2S0S5U4M3S0S5U5M4S0S5U6M5S0S5U7M6S0S5U8M7S0S5U9M8S0S5UaM9S0S5UbMaS0S5UcMbS0S5UdMcS0S5UeMdS0S5UfMeS0S5U2MfS2S5A1M10A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S42S43G0A1S0S42S43G1A1S0S42S46S0S5G1S0S5G0S0S5GfS0S5G2S0S5G3S0S5G4S0S5G5S0S5G6S0S5G7S0S5G8S0S5G9S0S5GaS0S5GbS0S5GcS0S5GdS0S5GeG10A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S42S45G0A1S2S42A1A3A3A3A3A3").
Local Definition MEMO_2 := apply_xforms XA1a xs_xa.
Definition XA1a1 : sstate := ltac:(let x := eval vm_compute in (xget XA1a (MEMO_2)) in exact x).
Local Lemma MEMO_2_c : MEMO_2 = Some XA1a1. Proof. vm_cast_no_check (@eq_refl _ MEMO_2). Qed.
Local Lemma MEMO_2_e : ltac2:(tb__ "0|0|
S39S6S1dA1S44S55S68A2S7S1dS5eA2A3").
Proof. exact (@eq_trans _ (apply_xforms XA1a xs_xa) MEMO_2 (Some XA1a1) (@eq_refl _ (apply_xforms XA1a xs_xa)) MEMO_2_c). Qed.
Lemma xs_XA1a_ok : ltac2:(tb__ "0|0|
S39S6S1dA1S44S55S68A2S7S1dS5eA2A3"). Proof. exact MEMO_2_e. Qed.
Local Definition MEMO_3 := unbase_obj_at XA1a1 0 (-208).
Definition XA1a2 : sstate := ltac:(let x := eval vm_compute in (match MEMO_3 with Some s => s | None => XA1a1 end) in exact x).
Local Lemma MEMO_3_c : MEMO_3 = Some XA1a2. Proof. vm_cast_no_check (@eq_refl _ MEMO_3). Qed.
Local Lemma MEMO_3_e : ltac2:(tb__ "0|0|
S39S6S1dA1S80S5eU0Nd0A3S7S1dS56A2A3").
Proof. exact (@eq_trans _ (unbase_obj_at XA1a1 0 (-208)) MEMO_3 (Some XA1a2) (@eq_refl _ (unbase_obj_at XA1a1 0 (-208))) MEMO_3_c). Qed.
Lemma unb_XA1a : ltac2:(tb__ "0|0|
S39S6S1dA1S80S5eU0Nd0A3S7S1dS56A2A3"). Proof. exact MEMO_3_e. Qed.
Definition XA1a3 : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc XA1a2) (ss_regs XA1a2) (ss_fregs XA1a2) (ss_fcsr XA1a2) (ss_resv XA1a2) (firstn 14 (ss_objs XA1a2)) (ss_facts XA1a2) (ss_next XA1a2) (ss_lenient XA1a2)) in exact x).
Definition XA1a4 : sstate := ltac:(let x := eval vm_compute in (set_objs XA1a3 (firstn 11 (ss_objs XA1a3))) in exact x).
Lemma XA1a_sets : ltac2:(tb__ "0|5|
S3aS39S9S15A1M0S26S56A1SbS15S26S5fA1M1S0S15S76S2S15A1A3A3A3S3aS39S8S2aS5fA1S4A3S3aS39G0G1SbS15S26S60A1M2S73S72S77A2A3A3S3aS39S37S1eS56A1S1eS4eA1A3S3aS39S9S12A1M3S1fS60A1S1fS55A1M4A3S3aS39G3S1fS56A1G4A3S3aS39S1dS60S3fS5fG2A2A3S39S1dS5fS3fS56G1A2A3A2A2A2A2A2A2A2").
Proof. split; [reflexivity | split; [vm_cast_no_check (@eq_refl bool true) | repeat split; reflexivity]]. Qed.
Local Definition MEMO_4 := apply_xforms XA1b xs_xa.
Definition XA1b1 : sstate := ltac:(let x := eval vm_compute in (xget XA1b (MEMO_4)) in exact x).
Local Lemma MEMO_4_c : MEMO_4 = Some XA1b1. Proof. vm_cast_no_check (@eq_refl _ MEMO_4). Qed.
Local Lemma MEMO_4_e : ltac2:(tb__ "0|0|
S39S6S1dA1S44S57S68A2S7S1dS61A2A3").
Proof. exact (@eq_trans _ (apply_xforms XA1b xs_xa) MEMO_4 (Some XA1b1) (@eq_refl _ (apply_xforms XA1b xs_xa)) MEMO_4_c). Qed.
Lemma xs_XA1b_ok : ltac2:(tb__ "0|0|
S39S6S1dA1S44S57S68A2S7S1dS61A2A3"). Proof. exact MEMO_4_e. Qed.
Local Definition MEMO_5 := unbase_obj_at XA1b1 0 (-208).
Definition XA1b2 : sstate := ltac:(let x := eval vm_compute in (match MEMO_5 with Some s => s | None => XA1b1 end) in exact x).
Local Lemma MEMO_5_c : MEMO_5 = Some XA1b2. Proof. vm_cast_no_check (@eq_refl _ MEMO_5). Qed.
Local Lemma MEMO_5_e : ltac2:(tb__ "0|0|
S39S6S1dA1S80S61U0Nd0A3S7S1dS58A2A3").
Proof. exact (@eq_trans _ (unbase_obj_at XA1b1 0 (-208)) MEMO_5 (Some XA1b2) (@eq_refl _ (unbase_obj_at XA1b1 0 (-208))) MEMO_5_c). Qed.
Lemma unb_XA1b : ltac2:(tb__ "0|0|
S39S6S1dA1S80S61U0Nd0A3S7S1dS58A2A3"). Proof. exact MEMO_5_e. Qed.
Definition XA1b3 : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc XA1b2) (ss_regs XA1b2) (ss_fregs XA1b2) (ss_fcsr XA1b2) (ss_resv XA1b2) (firstn 14 (ss_objs XA1b2)) (ss_facts XA1b2) (ss_next XA1b2) (ss_lenient XA1b2)) in exact x).
Definition XA1b4 : sstate := ltac:(let x := eval vm_compute in (set_objs XA1b3 (firstn 11 (ss_objs XA1b3))) in exact x).
Lemma XA1b_sets : ltac2:(tb__ "0|5|
S3aS39S9S15A1M0S26S58A1SbS15S26S62A1M1S0S15S76S2S15A1A3A3A3S3aS39S8S2aS62A1S4A3S3aS39G0G1SbS15S26S63A1M2S73S72S77A2A3A3S3aS39S37S1eS58A1S1eS4eA1A3S3aS39S9S12A1M3S1fS63A1S1fS57A1M4A3S3aS39G3S1fS58A1G4A3S3aS39S1dS63S3fS62G2A2A3S39S1dS62S3fS58G1A2A3A2A2A2A2A2A2A2").
Proof. split; [reflexivity | split; [vm_cast_no_check (@eq_refl bool true) | repeat split; reflexivity]]. Qed.

Definition XB1r : sstate := ltac:(let x := eval vm_compute in (set_objs X_1 (firstn 13 (ss_objs X_1))) in exact x).
Lemma XB1r_eq : ltac2:(tb__ "0|0|
S39S1dS3fS75S8bS15UdS26S75A1A3A2S5bA3"). Proof. reflexivity. Qed.
Definition O_payB : sobj := ltac2:(tb__ "0|0|
S16S11Pf1A1SdZ0A1S11P9eA1S2SeA1S18A5").
Local Definition MEMO_6 := reshape_obj_at XB1r 2 O_payB.
Definition XB10 : sstate := ltac:(let x := eval vm_compute in (MEMO_6) in exact x).
Local Lemma MEMO_6_c : MEMO_6 = XB10. Proof. vm_cast_no_check (@eq_refl _ MEMO_6). Qed.
Local Lemma MEMO_6_e : ltac2:(tb__ "0|0|
S39S1dS81S5bU2S69A3S64A3").
Proof. exact (@eq_trans _ (reshape_obj_at XB1r 2 O_payB) MEMO_6 (XB10) (@eq_refl _ (reshape_obj_at XB1r 2 O_payB)) MEMO_6_c). Qed.
Lemma XB10_eq : ltac2:(tb__ "0|2|
S3aS39S1dS81S5bU2M0S69A3S64A3S3aS39S6S15A1S8eS15S26S5bA1G0A3S7S15S76A2A3S3aS39S8S2bS1eS5bA1M1S69A2S4A3S39S37G1S1eS75A1A3A2A2A2").
Proof. split; [exact MEMO_6_e | split; [reflexivity | split; [vm_cast_no_check (@eq_refl bool true) | reflexivity]]]. Qed.
Definition xs_fo : list xform := ltac2:(tb__ "0|2|
S0S42S43U0M0A1S0S42S43U1M1A1S0S42S46S0S5G1S0S5G0S0S5U2S0S5U3S0S5U4S0S5U5S0S5U6S0S5U7S0S5U8S0S5U9S0S5UaS0S5UbS0S5UcS2S5A1A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S42S45G0A1S2S42A1A3A3A3A3").
Local Definition MEMO_7 := apply_xforms XB10 xs_fo.
Definition XB11 : sstate := ltac:(let x := eval vm_compute in (xget XB10 (MEMO_7)) in exact x).
Local Lemma MEMO_7_c : MEMO_7 = Some XB11. Proof. vm_cast_no_check (@eq_refl _ MEMO_7). Qed.
Local Lemma MEMO_7_e : ltac2:(tb__ "0|0|
S39S6S1dA1S44S64S6eA2S7S1dS65A2A3").
Proof. exact (@eq_trans _ (apply_xforms XB10 xs_fo) MEMO_7 (Some XB11) (@eq_refl _ (apply_xforms XB10 xs_fo)) MEMO_7_c). Qed.
Lemma xs_fo1_ok : ltac2:(tb__ "0|0|
S39S6S1dA1S44S64S6eA2S7S1dS65A2A3"). Proof. exact MEMO_7_e. Qed.
Local Definition MEMO_8 := unbase_obj_at XB11 0 (-208).
Definition XB12 : sstate := ltac:(let x := eval vm_compute in (match MEMO_8 with Some s => s | None => XB11 end) in exact x).
Local Lemma MEMO_8_c : MEMO_8 = Some XB12. Proof. vm_cast_no_check (@eq_refl _ MEMO_8). Qed.
Local Lemma MEMO_8_e : ltac2:(tb__ "0|0|
S39S6S1dA1S80S65U0Nd0A3S7S1dS48A2A3").
Proof. exact (@eq_trans _ (unbase_obj_at XB11 0 (-208)) MEMO_8 (Some XB12) (@eq_refl _ (unbase_obj_at XB11 0 (-208))) MEMO_8_c). Qed.
Lemma unb_fo1 : ltac2:(tb__ "0|0|
S39S6S1dA1S80S65U0Nd0A3S7S1dS48A2A3"). Proof. exact MEMO_8_e. Qed.
Definition s_fb1 : wsub := ltac:(let x := eval vm_compute in
  ((10%positive, SAlu ALU_ADD (SVar 1) (SLit (-208))) :: (15%positive, SLit (-1048368)) :: (13%positive, SVar 158) :: infer_sub 1 XB12 PreF) in exact x).
Local Definition MEMO_9 : ltac2:(tb__ "0|0|
S6S9S15A1A1") := ltac2:(tb__ "0|0|
S85S48S7cS4cA3").
Definition R_fb1 : list sobj := ltac:(let x := eval vm_compute in (match MEMO_9 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_9_c : MEMO_9 = Some R_fb1. Proof. vm_cast_no_check (@eq_refl _ MEMO_9). Qed.
Local Lemma MEMO_9_e : ltac2:(tb__ "0|1|
S39S6S9S15A1M0A1S85S48S7cS4cA3S7G0S4fA2A3").
Proof. exact (@eq_trans _ (entails_fr XB12 PreF s_fb1) MEMO_9 (Some R_fb1) (@eq_refl _ (entails_fr XB12 PreF s_fb1)) MEMO_9_c). Qed.
Lemma efr_fb1 : ltac2:(tb__ "0|1|
S39S6S9S15A1M0A1S85S48S7cS4cA3S7G0S4fA2A3"). Proof. exact MEMO_9_e. Qed.
Lemma chk_fb1 : ltac2:(tb__ "0|0|
S3aS39S8S8cS48S7cS4cS4fS0S1dS83S82A1S2S1dA1A3A5S4A3S39S8S89S1fS48A1S79S7S5U0A2S78S4fA5S4A3A2").
Proof. split; [vm_cast_no_check (@eq_refl _ true) | vm_cast_no_check (@eq_refl _ true)]. Qed.
Lemma s_fb1_vals : ltac2:(tb__ "0|0|
S3aS39S10S7eS4cPcA2S11Pf1A1A3S3aS39S10S7eS4cPdA2S11P9eA1A3S3aS39S10S7eS4cPaA2S14S2dS11P1A1SdNd0A1A3A3S39S10S7eS4cPfA2SdNfff30A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma XB12_shape : ltac2:(tb__ "0|0|
S3aS39S38S28S48A1S8aA3S3aS39S37S1eS48A1S1eS75A1A3S3aS39S9S12A1S1fS48A1S1fS75A1A3S39S8S27S48A1S3A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_10 : ltac2:(tb__ "0|0|
S1d") := ltac2:(tb__ "0|0|
S87S48S4cS4fS83S82A1A4").
Definition T_1B : sstate := ltac:(let x := eval vm_compute in (MEMO_10) in exact x).
Local Lemma MEMO_10_c : MEMO_10 = T_1B. Proof. vm_cast_no_check (@eq_refl _ MEMO_10). Qed.
Local Lemma MEMO_10_e : ltac2:(tb__ "0|0|
S39S1dS87S48S4cS4fS83S82A1A4S5dA3").
Proof. exact (@eq_trans _ (T_after XB12 s_fb1 R_fb1 (L_free EC_U)) MEMO_10 (T_1B) (@eq_refl _ (T_after XB12 s_fb1 R_fb1 (L_free EC_U))) MEMO_10_c). Qed.
Lemma T_1B_eq : ltac2:(tb__ "0|0|
S39S1dS87S48S4cS4fS83S82A1A4S5dA3"). Proof. exact MEMO_10_e. Qed.

Definition T_1Bt : sstate := ltac:(let x := eval vm_compute in (mkSS (ss_pc T_1B) (ss_regs T_1B) (ss_fregs T_1B) (ss_fcsr T_1B) (ss_resv T_1B) (ss_objs T_1B) L_facts (ss_next T_1B) false) in exact x).
Lemma ent_T1Bt : ltac2:(tb__ "0|0|
S3aS39S8S86S5dS49S2ScS37S10A2A1A3S4A3S39S37S1eS49A1S1eS5dA1A3A2"). Proof. split; [vm_cast_no_check (@eq_refl bool true) | reflexivity]. Qed.
Local Definition MEMO_11 : ltac2:(tb__ "0|0|
S1d") := ltac2:(tb__ "0|1|
S74S49S73S72S1eS49A1M0A2S84G0A1A3").
Definition T_1BS : sstate := ltac:(let x := eval vm_compute in (MEMO_11) in exact x).
Local Lemma MEMO_11_c : MEMO_11 = T_1BS. Proof. vm_cast_no_check (@eq_refl _ MEMO_11). Qed.
Local Lemma MEMO_11_e : ltac2:(tb__ "0|1|
S39S1dS74S49S73S72S1eS49A1M0A2S84G0A1A3S51A3").
Proof. exact (@eq_trans _ (app_objs T_1Bt (statics_objs C_U (ss_next T_1Bt)) (Pos.succ (ss_next T_1Bt))) MEMO_11 (T_1BS) (@eq_refl _ (app_objs T_1Bt (statics_objs C_U (ss_next T_1Bt)) (Pos.succ (ss_next T_1Bt)))) MEMO_11_c). Qed.
Lemma T_1BS_eq : ltac2:(tb__ "0|1|
S39S1dS74S49S73S72S1eS49A1M0A2S84G0A1A3S51A3"). Proof. exact MEMO_11_e. Qed.
Lemma swf_T_1BS : swf T_1BS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_T1B : ltac2:(tb__ "0|0|
S39S8S8dS72S1fS49A1S7bS26S49A1A4S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma T_1BS_shape : ltac2:(tb__ "0|0|
S3aS39S37S1eS51A1S84S1eS49A1A1A3S39S8S27S51A1S3A3A2"). Proof. split; reflexivity. Qed.
Local Definition MEMO_12 : ltac2:(tb__ "0|0|
S6S9S3bA1A1") := ltac2:(tb__ "0|0|
S3eS7aS7dS53S51S4A5").
Definition LVB1 : list leaf := ltac:(let x := eval vm_compute in (match MEMO_12 with Some l => l | None => [] end) in exact x).
Definition XB1a : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 0 LVB1 (mkLeaf T_1BS RsFuel))) in exact x).
Definition XB1b : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 1 LVB1 (mkLeaf T_1BS RsFuel))) in exact x).
Local Lemma MEMO_12_c : ltac2:(tb__ "0|1|
S39S6S9S3bA1M0A1S70S7G0S0S3bS3cS59S3dA2S0S3bS3cS5aS3dA2S2S3bA1A3A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_12). Qed.
Local Lemma MEMO_12_e : ltac2:(tb__ "0|1|
S39S6S9S3bA1M0A1S3eS7aS7dS53S51S4A5S7G0S0S3bS3cS59S3dA2S0S3bS3cS5aS3dA2S2S3bA1A3A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL ECUTS T_1BS true) MEMO_12 (Some [mkLeaf XB1a RsCut; mkLeaf XB1b RsCut]) (@eq_refl _ (sym_run segs FUEL ECUTS T_1BS true)) MEMO_12_c). Qed.
Lemma run_T1B : ltac2:(tb__ "0|1|
S39S6S9S3bA1M0A1S3eS7aS7dS53S51S4A5S7G0S0S3bS3cS59S3dA2S0S3bS3cS5aS3dA2S2S3bA1A3A3A2A3").
Proof. exact MEMO_12_e. Qed.

Definition XB1a4 : sstate := ltac:(let x := eval vm_compute in (set_objs XB1a (firstn 11 (ss_objs XB1a))) in exact x).
Lemma XB1a_sets : ltac2:(tb__ "0|1|
S3aS39S9S15A1S26S59A1SbS15S26S66A1M0S73S72S1eS49A1A2A3A3S3aS39S9S12A1S1fS66A1S1fS59A1A3S39S1dS66S3fS59G0A2A3A2A2").
Proof. repeat split; reflexivity. Qed.
Definition XB1b4 : sstate := ltac:(let x := eval vm_compute in (set_objs XB1b (firstn 11 (ss_objs XB1b))) in exact x).
Lemma XB1b_sets : ltac2:(tb__ "0|1|
S3aS39S9S15A1S26S5aA1SbS15S26S67A1M0S73S72S1eS49A1A2A3A3S3aS39S9S12A1S1fS67A1S1fS5aA1A3S39S1dS67S3fS5aG0A2A3A2A2").
Proof. repeat split; reflexivity. Qed.

Local Definition rc2_rng (o : sobj) : option (Z * Z) :=
  match ob_base o, ob_lo o, ob_hi o with
  | SLit 0, SLit lo, SLit hi => Some (lo, hi)
  | _, _, _ => None
  end.
Local Definition rc2_inside (o : sobj) (c : cell) : bool :=
  match rc2_rng o, c_off c with
  | Some (lo, hi), SLit a => Z.leb lo a && Z.ltb a hi
  | _, _ => true
  end.
Local Definition rc2_regroup (S : sstate) : sstate :=
  let stray := List.concat (List.map (fun o => List.filter (fun c => negb (rc2_inside o c)) (ob_cells o))
                                     (ss_objs S)) in
  let os := List.map (fun o =>
    mkObj (ob_base o) (ob_lo o) (ob_hi o)
      (List.filter (rc2_inside o) (ob_cells o) ++
       match rc2_rng o with Some _ => List.filter (rc2_inside o) stray | None => nil end)
      (ob_dflt o)) (ss_objs S) in
  mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) os (ss_facts S) (ss_next S) (ss_lenient S).
Definition C_1_raw : sstate := ltac2:(tb__ "0|47|
S25Z2042cS0S10S11P15bA1S0S10SdZ13680A1S0S10S14S2dS11P1M0A1M1SdN80A1M2A3M3S0S10SdZ10800A1S0S10SdZ3a0d0A1S0S10S11P183A1S0S10S11P184A1S0S10S11P185A1S0S10SdZ0A1M4S0S10S11P66M5A1M6S0S10G6S0S10S11P186A1S0S10S11P187A1S0S10S11P188A1S0S10S11P189A1S0S10S11P18aA1S0S10S11P18bA1S0S10S11P18cA1S0S10S11P9dA1M7S0S10S14S2dG6S14S2dG7SdZ6A1A3M8A3M9S0S10S11P9eA1MaS0S10S19S4Q8MbS14S2fS11P67A1SdZ8McA1MdA3A3MeS0S10SdZ29fc9A1MfS0S10G4S0S10G4S0S10G4S0S10G4S0S10G4S0S10S11P18dA1S0S10S11P18eA1S0S10S11P18fA1S0S10S11P190A1S2S10A1M10A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S0S10S11P120A1S0S10S11P121A1S0S10S11P122A1S0S10S11P123A1S0S10S11P124A1S0S10S11P125A1S0S10S11P126A1S0S10S11P127A1S0S10S11P80A1S0S10S11P81A1S0S10S11P12aA1S0S10S11P12bA1S0S10S11P12cA1S0S10S11P12dA1S0S10S11P12eA1S0S10S11P12fA1S0S10S11P130A1S0S10S11P131A1S0S10S11P8aA1S0S10S11P8bA1S0S10S11P8cA1S0S10S11P8dA1S0S10S11P8eA1S0S10S11P8fA1S0S10S11P90A1S0S10S11P91A1S0S10S11P92A1S0S10S11P93A1S0S10S11P13cA1S0S10S11P13dA1S0S10S11P13eA1S0S10S11P13fA1G10A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S21SaS10A1S0S15S16S14S2dG1SdNd0A1A3SdNfff30A1G4S2SeA1M11S18A5S0S15S16G3SdN50A1M12G4S0SeSfSdN48A1M13GcG4A3S0SeSfSdN40A1M14GcGfA3S0SeSfSdN38A1M15GcGeA3S0SeSfSdN30A1M16GcGaA3S0SeSfSdN28A1M17GcG9A3S0SeSfSdN20A1M18GcG7A3S0SeSfSdN18A1M19GcG6A3S0SeSfSdN10A1M1aGcS14S2dG6SdZ2A1M1bA3A3S0SeSfSdN8A1M1cGcSdZ135f8A1A3G11A3A3A3A3A3A3A3A3A3S18A5S0S15S16G6G4S11P65M1dA1M1eG11S18A5S0S15S16G1G2G4S0SeSfSdN78A1GcG4A3S0SeSfSdN70A1GcG4A3S0SeSfSdN68A1GcG4A3S0SeSfSdN60A1GcG4A3S0SeSfSdN58A1GcS14S2dG1SdZ20A1M1fA3M20A3S0SeSfG12GcSdZ13484A1A3S0SeSfG13GcG1bA3S0SeSfG14GcS14S2dG1GdA3M21A3S0SeSfG15GcSdZ1fc3cA1A3S0SeSfG17GcG4A3S0SeSfG18GcG4A3S0SeSfG19GcG4A3S0SeSfG1aGcG4A3S0SeSfG1cGcG4A3S0SeSfG2GcG4A3S0SeSfG16GcG21A3G11A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S20A5S0S15S16G4SdZ28cb0A1SdZ28d50A1G11S1aA5S0S15S16G4SdZ28d58A1GfS0SeSfSdZ29e80A1Z4M22SdZ5A1A3S0SeSfSdZ29ea8A1GcSdZ5a7a0A1M23A3S0SeSfSdZ29eb8A1GcG23A3S0SeSfSdZ29ea0A1GcSdZ5aba0A1M24A3S0SeSfSdZ29ec8A1GcSdZ22224A1A3S0SeSfSdZ29e90A1GcG4A3S0SeSfSdZ29e88A1GcG4A3S0SeSfSdZ29f10A1G22SdZffffffffffffffffA1M25A3S0SeSfSdZ29f08A1G22G25A3S0SeSfSdZ29f80A1Z1M26SdG26A1M27A3G11A3A3A3A3A3A3A3A3A3A3S1aA5S0S15S16G4GfSdZ39fc9A1M28G11S18A5S0S15S16G4G28SdZ3a02cA1S0SeSfSdZ39fd4A1G26G4A3S0SeSfSdZ39fd0A1G26G27A3S0SeSfSdZ3a020A1GcG4A3S0SeSfSdZ3a018A1GcSdZ3a008A1M29A3S0SeSfSdZ3a010A1GcG29A3S0SeSfSdZ3a028A1G22S11P1aA1M2aA3S0SeSfG29GcG29A3S0SeSfSdZ5a100A1GcGdA3S0SeSfSdZ5a108A1GcG4A3S0SeSfSdZ5a0f8A1GcG4A3S0SeSfSdZ3a000A1GcG20A3G11A3A3A3A3A3A3A3A3A3A3A3S1aA5S0S15S16G4SdZ3a030A1M2bSdZ5a338A1S0SeSfSdZ5a118A1G22G27A3S0SeSfSdZ5a230A1GcSdZ138acA1A3S0SeSfSdZ5a130A1GcSdZ20080A1A3S0SeSfSdZ5a120A1GcSdZ5a128A1A3S0SeSfSdZ3a0c0A1GcS14S31S19S3GbS19S4Q20M2cS11P9A1M2dA3M2eA3S14S31S14S32S19S3Q10S14S2fG2eSdZ10M2fA1M30A3A3G30A3S14S32S19S3G2cS19S4G2cS14S2fG2dG1fA3A3A3G1fA3A3A3A3S0SeSfSdZ3a080A1M31GcG31A3S0SeSfSdZ3a0a0A1GcSdZ5a390A1A3S0SeSfG2bG22G1bA3S0SeSfSdZ3a0c8A1GcSdZ3a0e0A1M32A3S0SeSfG32GcG4A3G11A3A3A3A3A3A3A3A3A3A3S1aA5S0S15S16
G4SdZ5a778A1G23G11S1aA5S0S15S16G4G23G24G11S18A5S2S15A1A3A3A3A3A3A3A3A3A3A3A3S0S12S13G7SdZ7fffA1A2S0S12S13GaSdZ3fffffaA1A2S0S12S13G8S11P64A1M33A2S0S12S23G33S14S2dGaG8A3A2S0S12S13S14S2dG8GaA3G1eA2S0S12S13G33G1eA2S0S12S13SdZ10000A1G1eA2S0S12S13G1eSdZ4000000A1A2S0S12S1bG1dG2fA2S0S12S1bG5G22A2S0S12S1cS17S30G6G4A3A1S0S12S13SdZ1000A1M34G6A2S0S12S13S14S2dG6G1eA3SdZ7fffff800000A1M35A2S0S12S13S11P1eA1M36S14S2dG1SdN800000A1A3M37A2S0S12S13G37G36A2S0S12S13SdZ7fff7f800000A1M38G36A2S0S12S13G36G35A2S0S12S13G1S11P4M39A1M3aA2S0S12S13G1S11P6M3bA1M3cA2S0S12S13SdZ7fff80000000A1M3dS11P19A1M3eA2S0S12S13G3eSdZ800000400000A1A2S0S12S13G27G2aA2S0S12S24G2aSdZ400000A1A2S0S12S1cS17S33S19S3GbS22P2S11P15A1M3fG26A3A3M40G4A3A1S0S12S1cS17S30G40SdZ2fA1A3A1S0S12S13G3fS11P5A1M41A2S0S12S13G3fSdZ1ffffA1M42A2S0S12S1bG0G22A2S0S12S13G3dG1A2S0S12S13G1SdZ7fffffffff20A1A2S0S12S13G27G1bA2S0S12S13G1bSdZ400A1A2S0S12S13S11P3A1SdZ100A1A2S0S12S13G3dG3aA2S0S12S13S14S2dG3aG41A3SdZ7fffffffffefA1A2S0S12S13G41G42A2S0S12S1bG39Z3M43A2S0S12S1bG3bG43A2S0S12S13G3dG3cA2S0S12S13G3cSdZ7ffffffffff0A1A2S0S12S13G38S14S2dG1SdN100000A1A3A2S0S12S17S2eSdN300A1SdNfff80A1M44A3S0S12S17S2eG44SdN10000000000A1A3S0S12S13G27S11P9fA1M45A2S0S12S13G45SdG22A1A2S0S12S13G34S11Pf0A1M46A2S0S12S13G46G35A2S2S12A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3P191S3A9").
Definition C_1 : sstate := Eval vm_compute in rc2_regroup C_1_raw.
Definition s_CAa1 : wsub := ltac:(let x := eval vm_compute in (infer_sub 31 XA1a4 C_1) in exact x).
Definition s_CAb1 : wsub := ltac:(let x := eval vm_compute in (infer_sub 31 XA1b4 C_1) in exact x).
Definition s_CBa1 : wsub := ltac:(let x := eval vm_compute in (infer_sub 31 XB1a4 C_1) in exact x).
Definition s_CBb1 : wsub := ltac:(let x := eval vm_compute in (infer_sub 31 XB1b4 C_1) in exact x).
Lemma ent_C1 : ltac2:(tb__ "0|0|
S3aS39S8S86S60S4aS6aA3S4A3S3aS39S8S86S63S4aS6bA3S4A3S3aS39S8S86S66S4aS6cA3S4A3S39S8S86S67S4aS6dA3S4A3A2A2A2").
Proof. split; [vm_cast_no_check (@eq_refl bool true) | split; [vm_cast_no_check (@eq_refl bool true) | split; [vm_cast_no_check (@eq_refl bool true) | vm_cast_no_check (@eq_refl bool true)]]]. Qed.
Lemma ent_C1_props : ltac2:(tb__ "0|1|
S3aS39S8S7fS6aP1fM0A2S4A3S3aS39S8S7fS6bG0A2S4A3S3aS39S8S7fS6cG0A2S4A3S3aS39S8S7fS6dG0A2S4A3S3aS39S8S88S6aS7bS7bA3S4A3S3aS39S8S88S6bS7bS7bA3S4A3S3aS39S8S88S6cS7bS7bA3S4A3S39S8S88S6dS7bS7bA3S4A3A2A2A2A2A2A2A2").
Proof. repeat (split; [vm_cast_no_check (@eq_refl bool true)|]). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma C_1_shape : ltac2:(tb__ "0|0|
S3aS39S38S28S4aA1S8aA3S3aS39S8S27S4aA1S3A3S39S10S29S4aZaA2S11P66A1A3A2A2"). Proof. repeat split; reflexivity. Qed.

Local Definition MEMO_13 : ltac2:(tb__ "0|0|
S6S1dA1") := ltac2:(tb__ "0|1|
S44S4aS0S42S43U0M0A1S0S42S43U1A1S0S42S45G0A1S2S42A1A3A3A3A2").
Definition C_1m : sstate := ltac:(let x := eval vm_compute in (xget C_1 (MEMO_13)) in exact x).
Local Lemma MEMO_13_c : MEMO_13 = Some C_1m. Proof. vm_cast_no_check (@eq_refl _ MEMO_13). Qed.
Local Lemma MEMO_13_e : ltac2:(tb__ "0|1|
S39S6S1dA1S44S4aS0S42S43U0M0A1S0S42S43U1A1S0S42S45G0A1S2S42A1A3A3A3A2S7S1dS5cA2A3").
Proof. exact (@eq_trans _ (apply_xforms C_1 [XRebase 0; XRebase 1; XMerge 0]) MEMO_13 (Some C_1m) (@eq_refl _ (apply_xforms C_1 [XRebase 0; XRebase 1; XMerge 0])) MEMO_13_c). Qed.
Lemma xs_C1_ok : ltac2:(tb__ "0|1|
S39S6S1dA1S44S4aS0S42S43U0M0A1S0S42S43U1A1S0S42S45G0A1S2S42A1A3A3A3A2S7S1dS5cA2A3"). Proof. exact MEMO_13_e. Qed.
Local Definition MEMO_14 := unbase_obj_at C_1m 0 (-128).
Definition C_1x : sstate := ltac:(let x := eval vm_compute in (match MEMO_14 with Some s => s | None => C_1m end) in exact x).
Local Lemma MEMO_14_c : MEMO_14 = Some C_1x. Proof. vm_cast_no_check (@eq_refl _ MEMO_14). Qed.
Local Lemma MEMO_14_e : ltac2:(tb__ "0|0|
S39S6S1dA1S80S5cU0N80A3S7S1dS47A2A3").
Proof. exact (@eq_trans _ (unbase_obj_at C_1m 0 (-128)) MEMO_14 (Some C_1x) (@eq_refl _ (unbase_obj_at C_1m 0 (-128))) MEMO_14_c). Qed.
Lemma unb_C1 : ltac2:(tb__ "0|0|
S39S6S1dA1S80S5cU0N80A3S7S1dS47A2A3"). Proof. exact MEMO_14_e. Qed.
Definition s_ff1 : wsub := ltac:(let x := eval vm_compute in
  ((10%positive, SAlu ALU_ADD (SVar 1) (SLit (-128))) :: (15%positive, SLit (-1048448)) :: (13%positive, SVar 101) :: infer_sub 1 C_1x PreF) in exact x).
Local Definition MEMO_15 : ltac2:(tb__ "0|0|
S6S9S15A1A1") := ltac2:(tb__ "0|0|
S85S47S7cS4dA3").
Definition R_ff1 : list sobj := ltac:(let x := eval vm_compute in (match MEMO_15 with Some R => R | None => [] end) in exact x).
Local Lemma MEMO_15_c : MEMO_15 = Some R_ff1. Proof. vm_cast_no_check (@eq_refl _ MEMO_15). Qed.
Local Lemma MEMO_15_e : ltac2:(tb__ "0|1|
S39S6S9S15A1M0A1S85S47S7cS4dA3S7G0S50A2A3").
Proof. exact (@eq_trans _ (entails_fr C_1x PreF s_ff1) MEMO_15 (Some R_ff1) (@eq_refl _ (entails_fr C_1x PreF s_ff1)) MEMO_15_c). Qed.
Lemma efr_ff1 : ltac2:(tb__ "0|1|
S39S6S9S15A1M0A1S85S47S7cS4dA3S7G0S50A2A3"). Proof. exact MEMO_15_e. Qed.
Lemma chk_ff1 : ltac2:(tb__ "0|1|
S3aS39S8S8cS47S7cS4dS50S0S1dS83S82A1S2S1dA1A3A5S4A3S3aS39S8S89S1fS47A1M0S7bS7S5U0A2S78S50A5S4A3S39S8S8fS12S2cS1cS17S30S11P66A1SdZ0A1A3A1A1G0A3S4A3A2A2").
Proof. split; [vm_cast_no_check (@eq_refl _ true) | split; [vm_cast_no_check (@eq_refl _ true) | vm_cast_no_check (@eq_refl _ true)]]. Qed.
Lemma s_ff1_vals : ltac2:(tb__ "0|0|
S3aS39S10S7eS4dPcA2S11P66A1A3S3aS39S10S7eS4dPdA2S11P65A1A3S3aS39S10S7eS4dPaA2S14S2dS11P1A1SdN80A1A3A3S39S10S7eS4dPfA2SdNfff80A1A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma C_1x_shape : ltac2:(tb__ "0|0|
S3aS39S38S28S47A1S8aA3S3aS39S37S1eS47A1S1eS4aA1A3S3aS39S9S12A1S1fS47A1S1fS4aA1A3S39S8S27S47A1S3A3A2A2A2").
Proof. repeat split; reflexivity. Qed.
Local Definition MEMO_16 : ltac2:(tb__ "0|0|
S1d") := ltac2:(tb__ "0|0|
S87S47S4dS50S83S82A1A4").
Definition T_1f : sstate := ltac:(let x := eval vm_compute in (MEMO_16) in exact x).
Local Lemma MEMO_16_c : MEMO_16 = T_1f. Proof. vm_cast_no_check (@eq_refl _ MEMO_16). Qed.
Local Lemma MEMO_16_e : ltac2:(tb__ "0|0|
S39S1dS87S47S4dS50S83S82A1A4S4bA3").
Proof. exact (@eq_trans _ (T_after C_1x s_ff1 R_ff1 (L_free EC_U)) MEMO_16 (T_1f) (@eq_refl _ (T_after C_1x s_ff1 R_ff1 (L_free EC_U))) MEMO_16_c). Qed.
Lemma T_1f_eq : ltac2:(tb__ "0|0|
S39S1dS87S47S4dS50S83S82A1A4S4bA3"). Proof. exact MEMO_16_e. Qed.
Local Definition MEMO_17 : ltac2:(tb__ "0|0|
S1d") := ltac2:(tb__ "0|1|
S74S4bS73S72S1eS4bA1M0A2S84G0A1A3").
Definition T_1fS : sstate := ltac:(let x := eval vm_compute in (MEMO_17) in exact x).
Local Lemma MEMO_17_c : MEMO_17 = T_1fS. Proof. vm_cast_no_check (@eq_refl _ MEMO_17). Qed.
Local Lemma MEMO_17_e : ltac2:(tb__ "0|1|
S39S1dS74S4bS73S72S1eS4bA1M0A2S84G0A1A3S52A3").
Proof. exact (@eq_trans _ (app_objs T_1f (statics_objs C_U (ss_next T_1f)) (Pos.succ (ss_next T_1f))) MEMO_17 (T_1fS) (@eq_refl _ (app_objs T_1f (statics_objs C_U (ss_next T_1f)) (Pos.succ (ss_next T_1f)))) MEMO_17_c). Qed.
Lemma T_1fS_eq : ltac2:(tb__ "0|1|
S39S1dS74S4bS73S72S1eS4bA1M0A2S84G0A1A3S52A3"). Proof. exact MEMO_17_e. Qed.
Lemma swf_T_1fS : swf T_1fS = true. Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma missT_T1f : ltac2:(tb__ "0|0|
S39S8S8dS72S1fS4bA1S2ScS10S10A2A1S26S4bA1A4S4A3"). Proof. vm_cast_no_check (@eq_refl _ true). Qed.
Lemma T_1fS_shape : ltac2:(tb__ "0|0|
S3aS39S37S1eS52A1S84S1eS4bA1A1A3S39S8S27S52A1S3A3A2"). Proof. split; reflexivity. Qed.

Local Definition MEMO_18 : ltac2:(tb__ "0|0|
S6S9S3bA1A1") := ltac2:(tb__ "0|0|
S3eS7aS7dS2S38A1S52S4A5").
Definition LVF1 : list leaf := ltac:(let x := eval vm_compute in (match MEMO_18 with Some l => l | None => [] end) in exact x).

Definition E_x1 : sstate := ltac:(let x := eval vm_compute in (lf_state (nth 0 LVF1 (mkLeaf T_1fS RsFuel))) in exact x).
Local Lemma MEMO_18_c : ltac2:(tb__ "0|1|
S39S6S9S3bA1M0A1S71S7G0S0S3bS3cS54S40A2S2S3bA1A3A2A3"). Proof. vm_cast_no_check (@eq_refl _ MEMO_18). Qed.
Local Lemma MEMO_18_e : ltac2:(tb__ "0|1|
S39S6S9S3bA1M0A1S3eS7aS7dS2S38A1S52S4A5S7G0S0S3bS3cS54S40A2S2S3bA1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs FUEL [] T_1fS true) MEMO_18 (Some [mkLeaf E_x1 RsEcall]) (@eq_refl _ (sym_run segs FUEL [] T_1fS true)) MEMO_18_c). Qed.
Lemma run_T1f : ltac2:(tb__ "0|1|
S39S6S9S3bA1M0A1S3eS7aS7dS2S38A1S52S4A5S7G0S0S3bS3cS54S40A2S2S3bA1A3A2A3").
Proof. exact MEMO_18_e. Qed.
Lemma cert_x1 : ltac2:(tb__ "0|0|
S3aS39S6S35A1S41S7aS28S54A1A2S7S35S36A2A3S3aS39S10S29S54Z11A2SdZ5eA1A3S39S10S29S54ZaA2SdZ0A1A3A2A2").
Proof. split; [vm_cast_no_check (@eq_refl _ (Some Ecall)) | split; reflexivity]. Qed.

