(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "prod"; "nil"; "list"; "app"; "fst"; "option"; "true"; "S"; "andb"; "bool"; "negb"; "orb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sv_eqb"; "valuation"; "SVar"; "sobj"; "ss_pc"; "DUnknown"; "cell"; "mkObj"; "ob_base"; "ob_hi"; "ss_objs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "la_state"; "ax_X"; "la_reason"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ANone"; "NDA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro_eqs"; "z0"; "nd_r2"; "nd_r1"; "bd_pro"; "P_errN"; "PhisZ"; "cpsR"; "nd_rn"; "nd_rz"; "nobj"; "runR"; "vrank"; "En_sf"; "En_sf0"; "Pre_sf"; "Tn8"; "Tn_sf"; "bk_xf3"; "bk_xf4"; "bk_xf5"; "cutsR"; "cutsV"; "cv_i"; "cv_xf"; "exitsR"; "exitsV"; "vl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXSelect"; "AXSplit"; "AXRebase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "optL"; "NP"; "FUEL_lo"; "sel2last"; "vF"; "BAD"; "Pre_lo"; "find_idxb"; "idxB"; "idxC"; "optS"; "vLEN"; "z24"; "@Corelib.Lists.ListDef"; "map"; "seq"; "Forall"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "fr_lo"; "T_mb"; "vs_T"; "vsn"; "C_pro"; "C_pro2"; "C_pro3"; "E_bz0"; "E_bz_pre"; "E_f8a0"; "E_ma0"; "E_mc0"; "E_mz0"; "E_oz0"; "E_s00_0"; "E_sm0"; "T_ma_ok"; "T_mc"; "T_mz1"; "blkAR"; "pc_bz"; "pc_oz"; "vALo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "KU"; "batom"; "bitem"; "BI"; "ASv"; "@Stdlib.ZArith.BinInt.Z"; "add"; "sub"; "div"; "eqb"; "mul"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro_eqs.LI"; "nd_lo0"; "P_err"; "bd_lo0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.Lists.List"; "filter"; "@Corelib.Init.Logic"; "True"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro_eqs.LND"; "E_blr0"; "cps_proR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA"; "zero_cells_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "ejcertAF"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "CK0"; "CK_DIV"; "CV"; "CV0"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_land Lib_load_obj_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr.
Module LI. Include Lib_load_obj_iface. End LI. Module LND. Include Lib_load_obj_land. End LND.

Definition cpsR : list Z := ltac2:(tb__ "0|0|
S1S1dS70S1S1dS6fS87A3A3").
Definition runR (S : axst) : list leafA := ltac2:(tb__ "0|1|
S8S5S21A1M0A1G0Lx;S25S7eS4cS2fVS;S9A5G0R1Ll;S4S21A1X8x2").
Definition showR (S : axst) : ltac2:(tb__ "0|0|
S5S3S1dS72A2A1") := ltac2:(tb__ "0|0|
S57S21S3S1dS72A2S21S0S1dS72S16S20S22R1A1A1A1S24R1A1A4LL;S33VS;A1A4").
Definition leafR (S : axst) (pc : Z) : axst := ltac2:(tb__ "0|0|
S5aS1fU0S57S21S1fS22S83S21S21S7bS16S20S22R1A1A1A1Vpc;A2LL;S33VS;A1A3A4S4fA4").
Definition Fx (A : axst) : list sprop := ss_facts (ax_S A).
Definition nx (A : axst) : positive := ss_next (ax_S A).
Definition nobj (A : axst) : nat := length (ss_objs (ax_S A)).

Definition vT (j : nat) : axst := ltac2:(tb__ "0|0|
S2S1fLj;Vj;S5cS2S5dS5eR1A1A1Lj';X2x2").
Definition VL : list axst := Eval vm_compute in map (fun j => leafR (vT j) memset_pc) (seq 0 1).
Definition vl (j : nat) : axst := nth j VL BAD.

Definition cv_i (L : axst) (b : sv) (off : Z) : nat := ltac2:(tb__ "0|0|
S53VL;Vb;Voff;A3").
Definition cv_xf (L : axst) (b : sv) (off n : Z) : list axform := ltac2:(tb__ "0|1|
S1S44S48S3fVL;Vb;Voff;A3M0S11Voff;A1A2S1S44S48SaG0A1S11S78Voff;Vn;A2A1A2S4S44A1A3A3").
Definition cv_1 (L : axst) (b : sv) (off n : Z) : axst := ltac2:(tb__ "0|0|
S4aS45VL;S40VL;Vb;Voff;Vn;A4A2A1").

Definition bk_1 (T0 : axst) : axst := ltac2:(tb__ "0|0|
S54VT0;S88S20VT0;A1U1S56A3A2").
Definition bk_2 (T1 : axst) : axst := ltac2:(tb__ "0|0|
S4aS45VT1;S1S44S49U1A1S4S44A1A3A2A1").
Definition bk_xf3 (T2 : axst) (b : sv) (off : Z) : list axform := ltac2:(tb__ "0|0|
S1S44S47S4dVT2;S51S15S15SbS12S1aR1A1Vb;A2S12S1bR1A1S11Voff;A1A2A2Lo;S1cS20VT2;A1A1U0A4U1A3A1S4S44A1A3").
Definition bk_3 (T2 : axst) (b : sv) (off : Z) : axst := ltac2:(tb__ "0|0|
S4aS45VT2;S3aVT2;Vb;Voff;A3A2A1").
Definition bk_xf4 (T3 : axst) (b : sv) (off : Z) : list axform := ltac2:(tb__ "0|0|
S1S44S47S4dVT3;S7dS32VT3;A1U1A2S52VT3;Vb;S78Voff;Z18A2A3A3A1S4S44A1A3").
Definition bk_4 (T3 : axst) (b : sv) (off : Z) : axst := ltac2:(tb__ "0|0|
S4aS45VT3;S3bVT3;Vb;Voff;A3A2A1").
Definition bk_xf5 (T4 : axst) : list axform := ltac2:(tb__ "0|1|
S1S44S46S7dS32VT4;A1U3A2A1M0S1S44G0S4S44A1A3A3").
Definition bk_5 (T4 : axst) : axst := ltac2:(tb__ "0|0|
S4aS45VT4;S3cVT4;A1A2A1").

Definition XN (E : axst) : list (sv * sv) := ltac2:(tb__ "0|2|
S83S3S10S10A2M0G0SdSeS12S7S10S10R1A3M1S71A2S12G1S4eA2A2A1Lr;S23VE;A1A3").
Definition Tn8 : axst := Eval vm_compute in shadow_reopen_stateA T_ma_null (XN T_ma_null) g5 20 52.
Definition En_sf0 : axst := Eval vm_compute in leafR Tn8 sf5_pc.
Definition En_sfB : axst := Eval vm_compute in shadow_release_stateA En_sf0 (objs_butlast En_sf0) 110 [].
Definition zmid : sobj := ltac2:(tb__ "0|0|
S19S4eS11Z190A1S11Z1a0A1S4S18A1S17A5").
Definition En_sfC : axst := Eval vm_compute in ax_setS En_sfB (reshape_obj_at (ax_S En_sfB) 5 zmid).
Definition xf_nm : list axform := ltac2:(tb__ "0|3|
S1S44S47S1S2U6S1S2U5S1S2U7S1S2U8S1S2U9S1S2U1S1S2U0M0S1S2U2M1S1S2U3S1S2U4S1S2UaS1S2UbS1S2UcS4S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A1S1S44S46G0A1M2S1S44G2S1S44S46G1A1S4S44A1A3A3A3A3").
Definition En_sfD : axst := Eval vm_compute in optL (apply_axforms En_sfC xf_nm).
Definition En_sf : axst := Eval vm_compute in flag_carve_stateA En_sfD 120.
Definition Pre_sf : axst := Pre_stack_free AE_A 5.
Definition L_sf : axst := L_stack_free AE_A 5.
Definition s_sfn : wsub := ltac2:(tb__ "0|1|
S1S3S1eS10A2M0S0S1eS10P10S14P78A1A4S1G0S0S1eS10PfS14P13A1A4S82PaS20S35A1S20S37A1A3A3A3").
Definition Rn_sf : list sobj := Eval vm_compute in optR (entails_frA En_sf Pre_sf s_sfn).
Definition Tn_sf0 : axst := Eval vm_compute in T_afterA3 Pre_sf En_sf s_sfn Rn_sf L_sf (ax_X En_sf).
Definition Tn_sf : axst := Eval vm_compute in ax_tidy Tn_sf0.
Definition P_errN : axst := Eval vm_compute in leafR Tn_sf lo_ret.
Definition s_pe : wsub := ltac2:(tb__ "0|0|
S82S4bS20S2dA1S20S80A1A3").

Definition PhisZ : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|3|
S1S3S5S1eA1M0S13OF_;M1A2M2S0G0G1S4S1eA1S13S84L_;A4S4G2A1A3").
Definition z0 : sv := SLit 0.
Definition bd_pro : list bitem := ltac2:(tb__ "0|5|
S1S75S76Z1M0Z0M1S1S3S1dS74A2M2S0S1dS74S8dS77S55A1M3A4S4G2A1M4A3S79S8eZ40A2A4S1S75S76G1G0S1G2S0S1dS74S7aS73S8cA2G3A4G4A3S79S7cS73S8bA2S73A2A4S4S75A1A3A3").
Definition nd_r1 : ndesc := ltac2:(tb__ "0|0|
S28S4S3S10S10A2A1S5bS81S27A4").
Definition nd_rn : ndesc := ltac2:(tb__ "0|0|
S28S4S3S10S10A2A1S5bS2cS27A4").
Definition nd_r2 : ndesc := ltac2:(tb__ "0|1|
S28S1S3S10S10A2M0S6eS4G0A1A3S5bS2cS27A4").
Definition nd_rz : ndesc := ltac2:(tb__ "0|0|
S28S4S3S10S10A2A1S4S3S3S10S1dA2S10A2A1S2cS27A4").
Definition vrank (j : nat) : Z := 2900 - 10 * Z.of_nat j.
Definition cutsV : list efnode := ltac2:(tb__ "0|4|
S57S2S3S3S3S1fS26A2M0S2A2M1S3S1dS10A2M2A2S2S0G1G2S0G0S2S0S1fS26S5dS5eR1A1A1S2aA4U0M3A4S0S1dS10S34R1A1S29A4A4Lj;S58G3U1A2A4").
Definition exitsV : list efnode := ltac2:(tb__ "0|4|
S57S2S3S3S3S1fS26A2M0S2A2M1S3S1dS10A2M2A2S2S0G1G2S0G0S2S0S1fS26S43R1A1S2aA4U0M3A4S0S1dS10S78S34R1A1Z9A2S29A4A4Lj;S58G3U1A2A4").
Definition cutsR : list efnode := ltac2:(tb__ "0|5|
S6S3S3S3S1fS26A2M0S2A2M1S3S1dS10A2M2A2M3S1G3S0G1G2S0G0S2S0S1fS26S50S7fA4U0M4A4S0S1dS10Zbb8S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S5fS2bA4G4A4S0S1dS10ZbaeS29A4A4S1G3S0G1G2S0G0S2S0S1fS26S60S2bA4G4A4S0S1dS10Zba4S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S61S2bA4G4A4S0S1dS10Zb9aS29A4A4S1G3S0G1G2S0G0S2S0S1fS26S6dS2bA4G4A4S0S1dS10Zb90S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S6bS2aA4G4A4S0S1dS10Zb86S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S6cS2aA4G4A4S0S1dS10Zb7cS29A4A4S1G3S0G1G2S0G0S2S0S1fS26S63S2aA4G4A4S0S1dS10Zb72S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S5cS2aA4G4A4S0S1dS10Zb68S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S38S30A4G4A4S0S1dS10Z960S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S39S31A4G4A4S0S1dS10Z956S29A4A4S4G3A1A3A3A3A3A3A3A3A3A3A3A3S3eA3").
Definition exitsR : list efnode := ltac2:(tb__ "0|5|
S6S3S3S3S1fS26A2M0S2A2M1S3S1dS10A2M2A2M3S1G3S0G1G2S0G0S2S0S1fS26S6aS7fA4U0M4A4S0S1dS10Zbb7S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S64S2bA4G4A4S0S1dS10ZbadS29A4A4S1G3S0G1G2S0G0S2S0S1fS26S68S2bA4G4A4S0S1dS10Zba3S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S67S2bA4G4A4S0S1dS10Zb99S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S65S2bA4G4A4S0S1dS10Zb8fS29A4A4S1G3S0G1G2S0G0S2S0S1fS26S66S2aA4G4A4S0S1dS10Zb85S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S69S2aA4G4A4S0S1dS10Zb7bS29A4A4S1G3S0G1G2S0G0S2S0S1fS26S62S2aA4G4A4S0S1dS10Zb71S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S86S2aA4G4A4S0S1dS10Za09S29A4A4S1G3S0G1G2S0G0S2S0S1fS26S36S30A4G4A4S0S1dS10Z95fS29A4A4S1G3S0G1G2S0G0S2S0S1fS26S2dS31A4G4A4S0S1dS10Z955S29A4A4S4G3A1A3A3A3A3A3A3A3A3A3A3A3S42A3").

Lemma ecertR_ok : ltac2:(tb__ "0|0|
S85ScS89S7eS4bS2eS4cS2fS4bS3dS41A8S9A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma PhisZ_reads : ltac2:(tb__ "0|3|
S59S3S5S1eA1M0S13OF_;M1A2M2G2S8aS7G0G1R1A3SfG0G1R1A3A2Lp;S2eA3").
Proof. constructor; [intros rho rho' _ _ _ _; exact I | constructor]. Qed.
