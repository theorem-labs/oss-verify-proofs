(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From Stdlib Require Permutation.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f0 ec.

(* [comment removed for export] *)
Module Lib_load_obj_epiS_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "app"; "cons"; "false"; "list"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SPUle"; "sprop_eqb"; "SLit"; "SVar"; "sprop_below"; "sv"; "ss_facts"; "SAlu"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vF"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "tvL"; "extraLO"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "wsub_id_on"; "bud_le2"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_epiD_chk"; "nx"; "Fx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "BIc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs"; "V_ld"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2"; "ent_chk2"; "B_1"; "L_v0a"; "L_v0b"; "bnds"; "ndAt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR"; "V_ldR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "AHead"; "NDA"; "nd_below"; "fr_sub_eqb"; "nd_bd"; "nd_am"; "nd_fr"; "nd_tv"; "ndesc"; "am_eqb"; "am_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1"; "s_fs2"; "E_fs2"; "L_dz"; "kept_fs2"; "nd_succ"; "s_kn"; "s_nn"; "E_fs21"; "L_sk"; "L_sn"; "R_fs2"; "Xk_fs2"; "bd_fz2"; "bd_nop2"; "bd_ok2"; "bd_s0"; "hand_fs2"; "qHk2"; "qHn2"; "qHz2"; "tvL_k"; "tv_fz2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS4"; "E_fu"; "L_d6f"; "L_d7"; "L_land"; "bd_land"; "comOf"; "ekOf"; "land_chk"; "nd_d0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fg.Lib_load_obj_epiS_chk"; "Lb_v0a"; "Lb_v0b"; "cc_facts"; "f_len"; "f_nx"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "K_disp"; "bd_disp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_epiS_defs"; "nx500"; "ldef_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "tv_permb"; "@Corelib.Lists.ListDef"; "nth"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "PHIe"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1.FS"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "alA"; "bA"; "pNX"; "t_c"; "t_k"; "v_sh"; "vsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_epiD3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_epiD_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_epiS2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fe.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_epiS_defs.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.

Lemma ent_chk2_unf : ltac2:(tb__ "0|3|
S17S17S37S37S0S3S28R4R3R2R1A4S2A3S1S0S3S18R5R4S21S13S16R5A1M0S16R4A1A3M1A3S2A3S1S0S3S64G1S13A2S2A3S1S0S3S5eS13S12G0A1M2A2S2A3S1S0S3S31G2R3A2S2A3S1S0S3S77G1S36R3A1S36R2A1A3S2A3S1S0S3S32G1S35R3A1S35R2A1A3S2A3S1S0S3S1fS10G0A1S25G1S33R2A1A2S33R3A1A3S2A3S0S3S38S39G1S34R2A1A2S34R3A1A2S2A3A2A2A2A2A2A2A2F_;Fndj;Fndi;FT;FL;").
Proof.
  intros L T ndi ndj H. unfold ent_chk2 in H. cbv zeta in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H]. apply lazy_andb_prop in H as [H4 H].
  apply lazy_andb_prop in H as [H5 H]. apply lazy_andb_prop in H as [H6 H]. apply lazy_andb_prop in H as [H7 H8]. repeat split; assumption.
Qed.
Lemma land_chk_unf : ltac2:(tb__ "0|4|
S17S7S24A1SfS0S3S57R3R2R1A3S2A3S1S0S3S66R3S4S24S55R3A1M0S56R3A1M1A3A2S2A3S1S0S3S66S4S24G0S60A3S54R3A1M2A2S2A3S1S0S3S20S10S16R4A1A1ScZ0M3A1G3G1S60A5S2A3S0S3S28R4S5fS30S1aS19G2S2fR2S6A2A4S58A4S2A3A2A2A2F_;Fhd;Fbd;FL;").
Proof.
  intros L bd hd H. unfold land_chk in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H4]. repeat split; assumption.
Qed.

Lemma epiS_chk_fs : ltac2:(tb__ "0|8|
S1S0S3S6cS23S3bA1M0S3dS19S1bS44A5S2A3S1S0S3S6eG0S3dS19S6dS45A5S2A3S1S0S3S1cS9SbSaS14ScZ7fffff7ff800A1A2A1G0A3S2A3S1S0S3S62G0A1S2A3S1S0S3S61S3bA1S2A3S1S0SfS63S3aPcA2S71A3S1S0SfS63S3aP64A2S70A3S1S0S24S68S24UeS49S26Z0M1G1G1A3A4S6aZ80M2S73S75S76A1M3A1M4S74G3A1M5A3A3S1S0S3S1cS9SbSaS6bG2G5A2ScZffffffffA1M6A2A1S23S41A1M7A3S2A3S1S0S3S1cS9SbSaG4G5A2A1G7A3S2A3S1S0S3S1cS9SbSaG5G6A2A1G7A3S2A3S0S7S24A1S25S3aS33S6fA1A2S4aA3A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
Lemma epiS_chk_succ : ltac2:(tb__ "0|2|
S1S0S3S5eS13S22S43A1M0A2S2A3S1S0S3S31G0S30S1aS19S47S2fS4cS2A2A4A2S2A3S1S0S3S32S40S19S19A3S2A3S1S0S3S1eS2eS40A2S2A3S1S0S3S5eS13S22S42A1M1A2S2A3S1S0S3S31G1S30S4eS19S48S2fS4bS2A2A4A2S2A3S1S0S3S32S3fS19S19A3S2A3S1S0S3S1eS2eS3fA2S2A3S0S3S67S4fS1aA2S2A3A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition Lb_v0a : axst := Eval vm_compute in ax_add_facts bnds L_v0a.
Definition Lb_v0b : axst := Eval vm_compute in ax_add_facts bnds L_v0b.
Definition f_nx : sprop := ltac2:(tb__ "0|0|
SaS72S11S69S15ScZ1A1A3A2").
Definition f_len : sprop := SPUle vLEN (SLit 67108864).

Definition cc_facts : list sprop := ltac2:(tb__ "0|3|
S5S9SaSdP197A1SdP198A1M0A2S5S9SaG0ScZffffffffA1M1A2S5S9SaSdP1a3A1SdP1a4A1M2A2S5S9SaG2G1A2S8S9A1A3A3A3A3").
Lemma epiS_chk_v0 : ltac2:(tb__ "0|9|
S1S0S3S1dS9SeS22S2aA1A1S4S9S2cS23S2aA1M0A3M1A3S2A3S1S0S17S65S2aG1A2S59A3S1S0S3S1cS9SbS5dA1M2G0A3S2A3S1S0S3S1cS9SbS5cA1M3G0A3S2A3S1S0S3S1dS9S9S1cS9SbR1A1M4G0A3Lf;S5bA3S2A3S1S0S3S28S59S29S3eS2dU1A1M5A4S2A3S1S0S3S1eS2eS21S13S16S59A1S16S29A1M6A3A2S2A3S1S0S3S1dS9SeS22S2bA1A1S4S9S2cS23S2bA1M7A3M8A3S2A3S1S0S17S65S2bG8A2S5aA3S1S0S3S1cS9G2G7A3S2A3S1S0S3S1cS9G3G7A3S2A3S1S0S3S1dS9S9S1cS9G4G7A3Lf;S5bA3S2A3S1S0S3S28S5aS29S3eG5A4S2A3S0S3S1eS2eS21S13S16S5aA1G6A3A2S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiS_chk_fu : ltac2:(tb__ "0|0|
S1S0S3S61S50A1S2A3S0S3S1dS9SeS22S50A1A1S23S50A1A3S2A3A2").
Proof. conj_vmc. Qed.
Lemma epiS_chk_landphi : ltac2:(tb__ "0|1|
S1S0S3S1eS27S21S13S16S53A1S16S5fA1M0A3A2S2A3S1S0S3S1eS27S21S13S16S52A1G0A3A2S2A3S1S0S3S1eS27S21S13S16S51A1G0A3A2S2A3S1S0S3S1eS27S21S13S16S3cA1G0A3A2S2A3S0S3S31S22S3cA1S30S1aS19S46S2fS4dS6A2A4A2S2A3A2A2A2A2").
Proof. conj_vmc. Qed.
End Lib_load_obj_epiS_chk.

(* [comment removed for export] *)
Module Lib_load_obj_epiS_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "prod"; "nat"; "list"; "true"; "bool"; "app"; "Some"; "option"; "false"; "cons"; "fst"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "la_state"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "AHead"; "NDA"; "nd_below"; "JA"; "TPA"; "fbinA"; "ffinA"; "frinA"; "frozen"; "ok_frameKA"; "tvinA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sprop"; "ss_next"; "ss_facts"; "holds"; "sprop_eqb"; "sobj"; "sprop_below"; "agree_below"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR"; "PhisS"; "ldefR"; "V_ldR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "phiK"; "efmeasA"; "efnode"; "wsub_id_on"; "fnode"; "JAF"; "bud_le2"; "efdrop"; "enodeIAF"; "nodeIAF"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f0.Lib_load_obj_epiS_eqs"; "RB"; "zl"; "cutsS1"; "cutsS2a"; "cutsS2b"; "cutsS4"; "exitsS1"; "exitsS2a"; "exitsS2b"; "exitsS4"; "ndF"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "mul"; "pow"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2"; "ndAt"; "B_1"; "L_cf0"; "PDk_ad"; "bnds"; "ENDOWs"; "ent_chk2"; "kept_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fg.Lib_load_obj_epiS_pf.FU"; "Pre_fu"; "Posts_fu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "ldef"; "tvL"; "P0_lo"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1.FSP"; "P0_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1"; "nd_succ"; "kept_fs2"; "nd_s0"; "PDk_fs2"; "Es_fs0"; "L_dz"; "L_sk"; "L_sn"; "R_fs2"; "nd_fz2"; "nd_nop2"; "nd_ok2"; "E_fs2"; "E_fs21"; "Xk_fs2"; "bd_s0"; "nnPhi"; "passed_fs2"; "s_fs2"; "tv_fs2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "entails_frA"; "jpostA"; "call_checkA"; "import_postA"; "J_ofPA"; "call_checkPA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2.ADP"; "P0_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "BXok_d"; "bxt"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "K_disp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_epiD_chk"; "Fx"; "nx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub";
"@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1.FS"; "NP"; "Pre_fs"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2.AD"; "Pre_ad"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS4"; "nd_d0"; "E_fu0"; "L_d6f"; "L_d7"; "L_land"; "land_chk"; "nd8"; "nd9"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits"; "K_after0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "enodeA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs"; "V_ld"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fg.Lib_load_obj_epiS_chk"; "cc_facts"; "f_len"; "f_nx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS_st1"; "E0_1"; "E0_2"; "E0_3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS_st2"; "E0_4"; "E0_5"; "E0_6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_load_obj_epiS_st3"; "E0_8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf"; "frozen_stableH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "blkAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA"; "SPfamETA"; "SPfamGTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_epiD3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_epiD_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_epiS2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fe.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_load_obj_epiS_kit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_epiS_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f0.Lib_load_obj_epiS_blk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS_st1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiS_st2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_load_obj_epiS_st3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f0.Lib_load_obj_epiS_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fg.Lib_load_obj_epiS_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module DP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_load_obj_epiD_pf. End DP.
Module FU. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_finalize_unknowns. End FU.

Lemma efmeas_lit : ltac2:(tb__ "0|2|
SdS12S2S21S21S23S40S56Z0R2A2S55R2S58Z2Z40A2M0A2A2S3fS21S36S0S1S1SdS12A2M1S2A2S1S21S24A2S0G1S2S0SdS12R7R6A4R5A4S0S21S24R4S4bR3A1A4A4R2A2S59S57R4G0A2R3A2A3F_;Frho;Fm;Fr;Fk;Fnd;FT;").
Proof. intros T nd k r m rho Hm. unfold efmeasA. cbn [ef_rank ef_var fst snd]. pose proof (uval_lit rho m Hm) as E. unfold uval in E. unfold zl. rewrite E. reflexivity. Qed.
Lemma lines_in_kept_fs2 : ltac2:(tb__ "0|0|
S42S1S24S24A2S0S24S24Sa7Sc6Z10Sa8A2A4S6dA3").
Proof. vm_compute. repeat (first [left; reflexivity | right]). Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sc3S23S3S2dQ40A1A1S87OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sc2S20VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S21SaeVCST;R1A2S40S56Z0R2A2S55R2SbeA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S21SaeVXGL;R1A2S40S56Z0R2A2S55R2SbeA2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S21Sc8R1A1SaeVXGL;R2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S3S1S1S21S21A2S21A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S23OFr;") := ltac2:(tb__ "0|0|
S67VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S18VAInv;VCST;VXGL;S49VKc;Vrho0;VP0;VFB;VFF;VBX;S13Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S3aVAInv;VCST;VXGL;S49VKc;Vrho0;VP0;VFB;VFF;VBX;S13VPhi;Vnd;Ad").

Lemma nnPhi2_holds : ltac2:(tb__ "0|0|
S23S3S2dQ40A1A1S3S88A1S87S69S25S28R4A1S27SeS79A1A1A3VJAv;S16S7fS64S7bS15Sa6S4A2A4R5R4R3R2A5S28R6S7cA2F_;F_;Fmd;Ftr;Ftp;Frho;").
Proof.
  intros rho tp tr md HF (Ai & kc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HBU & _).
  cbn [nd_bd] in HBU. destruct HBU as (_ & _ & _ & _ & _ & _ & Hnn & _).
  pose proof epiS_chk_fs as (_ & _ & _ & _ & _ & _ & _ & C14 & F1c & F2c & F3c & _).
  assert (Hin : In (nth 14 bd_s0 (BIc 0 0 0)) bd_s0) by (apply (nth_error_In _ 14); OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (proj1 (Forall_forall _ _) Hnn _ Hin) as N0. rewrite C14 in N0.
  unfold PHIe in N0. cbv beta iota delta [bival lfval aval bi_f bi_c] in N0.
  pose proof (holds_mem _ _ _ HF F1c) as F1. pose proof (holds_mem _ _ _ HF F2c) as F2. pose proof (holds_mem _ _ _ HF F3c) as F3.
  rewrite h_ule in F1, F2, F3. rewrite uval_lit in F1, F3 by lia.
  pose proof (uval_range rho (t_c (v_sh vsP))) as Rc. pose proof (uval_range rho (kb 128 (t_k (v_sh vsP)))) as Rk.
  assert (Ec : uval rho (kb 128 (t_c (v_sh vsP))) = 128 * uval rho (t_c (v_sh vsP))) by (unfold kb; apply uval_mul_lit; lia).
  rewrite uval_lit in N0 by lia.
  unfold nnPhi. rewrite h_ule.
  rewrite (uval_mul_lit rho 4 (kb 128 (t_k (v_sh vsP)))) by lia.
  rewrite uval_add_small; rewrite ?uval_lit by lia; rewrite ?(uval_mul_lit rho 6 (kb 128 (t_c (v_sh vsP)))) by lia; lia.
Qed.

Lemma HIN_fs2 : ltac2:(tb__ "0|1|
S23S95Sc3S23S3S2dQ40A1A1S87S69S25S28R6A1S27SeS78A1A1A3VP0;Vrho0;A1SbcS49Vrho0;R8A3VAInv;R7R6R5R4A4S19Vrho0;R8A2SccRbSc5Sc4R9A1A1A2S1aVFB;RaA2S1bVFF;RbA2S1fVFB;RcReS6S1S24S24A2S6dS7dA3M0A4ScdRfG0A2SceR10G0A2S1cVFF;RfR11S64A4S40Sd4VCST;Vrho0;VFB;VFF;R12S6dS64S74A8S40Sd5VCST;VXGL;Vrho0;VFB;VFF;R12S6dS64S7aA9S6bScbVFB;R12S6dA3Sd3VFF;R12S64A3S93S92R12S74R11A3S7eA2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof epiS_chk_fs as (CR & CX & CvF & _ & _ & Cs12 & Cs100 & _).
  assert (HNk : tvinA FB Ai rho kept_fs2) by (apply (tvinA_sublist FB Ai rho (kept_fs2 ++ passed_fs2)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_fs2) by (exact (tvd_app_l rho kept_fs2 passed_fs2 HD)).
  assert (HZk : tvz rho kept_fs2) by (apply (tvz_sublist rho (kept_fs2 ++ passed_fs2)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - exact (DP.lo_robjsF0 AInv CST ALA HCST FB FF rho0 Ai rho _ kept_fs2 R_fs2 rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CR).
  - exact (lo_xrsF AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ kept_fs2 Xk_fs2 rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CX).
  - unfold FSP.P0_fs. rewrite !rw_call', Cs12, Cs100.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    pose proof (holds_mem _ _ _ HF CvF) as HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 544) = 544) by (apply uval_lit; lia). assert (E464 : uval rho (SLit 464) = 464) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 544) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (EalA : uval rho alA = uval rho vF + 464) by (unfold alA; rewrite <- E464; apply uval_add_small; rewrite E464; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S21S3S2dQ40A1A1S45F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S2fSdS23S3S2dQ40A1A1S45S69S25S28R3A1S27SeR4A1A1A3VTR;S2eS20R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S45S45S45S48R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S45OS45S48R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S2fS2fSdSdS94S3S2aA1M0S3S1SdS82A2M1A1S3S1S24S24A2M2A1S45S23S3S2dQ40A1A1M3G2S42G2R1R5A3S42G2R2S11RbA1A3F_;Fr;S3fS8G0A1S81RaR9R8A3S7G0R7A2A3S3fS5S86RbRaR9R8S68G1SdSbSdS82A2R7A4A5S4A3S23G3VTR;S2eS20RfRdR2R1A5S80S20S26SeRdA1A1R2R1RaA5A2Ftp1;Frho1;S3S88A1M4S95S87S30S20R9R8R10S0G4S96R3S97R2R1A2A4A5R13RaR9R4R2A4R13S93S92RbRfS8aR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;SdS82G4S95S87S23G3G4S95S87S42G1S0SdS82RaR9A4R14A3S30S20R12R11R19S0G4S96R9S97R8R7A2A4A5R1cR13R12RaR8A4SbcS26SeR1aA1A1S93S92R14R18S8aR9R13RaA3A3R19A2R8A3S30S20R9R8ReS0G4S96R7S97R6R5A2A4A5ReS93S92R16R1aS8aRbR15RcA3A3R1bA2R15RaR9R8R6A6S40Sd1R17S8aRcR16RdA3R1bR1cR1dR10R1eR19RbA9S23SbdR18S8aRdR17ReA3R1cR1dSeR1eA1SeR1fA1SeR11A1R1RcA9VTR;S2eS20S85R11S93S92R19R1dS8aReR18RfA3A3R1eA2R18RdRcA5Sd2R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S2eS20R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S23OF_;S12SdS23S3S2dQ40A1A1S45R6R3A1VTR;S2eS20VJAv;R6A1R5R4R3A5R2A2F_;VTR;S2eS20VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").

Hypothesis CHF : ltac2:(tb__ "0|1|
S3S1S21S21A2M0A1S3S1G0S21A2A1S8cS23S3S2dQ40A1A1S8bZ5R3A2VTR;S2eS20S14VAInv;VCST;VXGL;VKc;S6bR6R5A2R6R5R4S13S9aAaS99R3R2A5S80S20S98R3R2S8eVAInv;VCST;VXGL;VKc;S6bS13S6fR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CAD : ltac2:(tb__ "0|1|
S3S1S21S21A2M0A1S3S1G0S21A2A1S8cS23S3S2dQ40A1A1S8bZ3R3A2VTR;S2eS20S14VAInv;VCST;VXGL;VKc;S89VCST;R6R5A3R6R5R4S13S9cAaS9bR3R2A5S80S20SadR3R2S8eVAInv;VCST;VXGL;VKc;S89VCST;A1S13S5dR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis PURE_fu : ltac2:(tb__ "0|2|
SdS94S3S2aA1M0S23S3S2dQ40A1A1S12S45S3fS8G0A1S81R7S62R6A3S7G0R5A2A3S3fS5S83R8S62R7R6S68SfSdS10S63A4A5S4A3S3fS5SafS49S26SeR9A1A1A2S4A3S3fS5S17S26SeRaA1A1R5A2S4A3S3fS5S44S25S2bS26SeRbA1M1A1A1S27G1A1A3S4A3SfS23S42SfR2S63A3S2cS26SeRfA1A1RcR2A3VTR;S2eS20VJAv;RbA1SaaS27SeR10A1A1S84RfS62S10R4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S2eS20VJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").

Hypothesis CUTS1 : ltac2:(tb__ "0|5|
SdS12S2S1S21S24A2M0S23S3S2dQ40A1A1M1S21G1S42S1S1S1SdS12A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS12R8R7A4R6A4R5A4S4cA3S35S32R7R5A3S40S56Z0S36S0G3G0S0G2S2S0SdS12RaR9A4R8A4R7A4R6A2M4A2S55G4R4A2A2VTR;S2eS20VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis CUTS2a : ltac2:(tb__ "0|5|
SdS12S2S1S21S24A2M0S23S3S2dQ40A1A1M1S21G1S42S1S1S1SdS12A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS12R8R7A4R6A4R5A4S4dA3S35S32R7R5A3S40S56Z0S36S0G3G0S0G2S2S0SdS12RaR9A4R8A4R7A4R6A2M4A2S55G4R4A2A2VTR;S2eS20VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis CUTS2b : ltac2:(tb__ "0|5|
SdS12S2S1S21S24A2M0S23S3S2dQ40A1A1M1S21G1S42S1S1S1SdS12A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS12R8R7A4R6A4R5A4S4eA3S35S32R7R5A3S40S56Z0S36S0G3G0S0G2S2S0SdS12RaR9A4R8A4R7A4R6A2M4A2S55G4R4A2A2VTR;S2eS20VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis CUTS4 : ltac2:(tb__ "0|5|
SdS12S2S1S21S24A2M0S23S3S2dQ40A1A1M1S21G1S42S1S1S1SdS12A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS12R8R7A4R6A4R5A4S4fA3S35S32R7R5A3S40S56Z0S36S0G3G0S0G2S2S0SdS12RaR9A4R8A4R7A4R6A2M4A2S55G4R4A2A2VTR;S2eS20VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis KDISP : ltac2:(tb__ "0|1|
S23S3S2dQ40A1A1M0S21G0S65R4A1S55S57Z186S58Z2Z40A2A2R3A2VTR;S2eS20VJAv;S9dA1S8fR6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;").
Hypothesis CONT_cf : ltac2:(tb__ "0|3|
S23S3S2dQ40A1A1M0G0VTR;S2eS20VJAFv;S35S32U0M1A2S6cA2S5cR3R2A5VFAM;S36S0S1S1SdS12A2M2S2A2S1S21S24A2S0G2S2S0SdS12S5cS6cA4G1A4S0S21S24Z18aS6aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").

Ltac meas := rewrite ?DP.efmeas_z0, ?efmeas_lit by (vm_compute; split; [discriminate | reflexivity]); vm_compute; split; [discriminate | reflexivity].

Lemma X_LANDf : ltac2:(tb__ "0|1|
SdS3S8dA1S24S21S23S3S2dQ40A1A1M0G0S3fS5Sa2R7R6R5A3S4A3S3fS5S38Sb1Sa9S49SeR8A1SeS8fA1A3A2S4A3S55S57Z186S58Z2Z40A2A2R6A2S33R6A1VTR;S2eS20VJAv;S16S66S64RaS15R9S9A2A4A1RbR7R6A5VFAM;R8R5A2A2F_;F_;F_;F_;Ftp0;Ftp;Frho;Fb;Fhd;Fbd;FL;").
Proof.
  intros L bd hd b rho tp tp0 HC HP Hb HPHI.
  destruct (land_chk_unf L bd hd HC) as (P1 & P2 & PPay & HE).
  destruct (ent_chk2_unf L K_disp _ nd_d0 HE) as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  apply TR_facts. intros HF.
  apply (TR_pre (SPA segs (JAv nd_d0) K_disp (rho_sub rho (infer_sub NP (ax_S L) (ax_S K_disp))) tp)).
  { intros w Hw.
    apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L K_disp _ (NDA tvL frL (bd_land bd) (AHead hd false)) nd_d0 rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam).
    exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL frL (AHead hd false) bd (comOf bd) (ekOf bd) bd_disp (bd_land bd) _ L rho tp w P1 P2 HF PPay Hw). }
  apply KDISP; [|exact Hb].
  exact (phi_sub V_ld ldef ldef_reads _ rho HP (ldefR_ldef rho HPHI)).
Qed.
Lemma X_LANDt : ltac2:(tb__ "0|1|
SdS3S8dA1S24S21S23S3S2dQ40A1A1M0G0S3fS5Sa2R7R6R5A3S4A3S3fS5S38Sb1Sa9S49SeR8A1SeS8fA1A3A2S4A3S55S57Z186S58Z2Z40A2A2R6A2S33R6A1VTR;S2eS20VJAv;S16S66S64RaS15R9S4A2A4A1RbR7R6A5VFAM;R8R5A2A2F_;F_;F_;F_;Ftp0;Ftp;Frho;Fb;Fhd;Fbd;FL;").
Proof.
  intros L bd hd b rho tp tp0 HC HP Hb HPHI.
  apply (TR_pre (SPA segs (JAv (NDA tvL frL bd (AHead hd false))) L rho tp)); [|exact (X_LANDf L bd hd b rho tp tp0 HC HP Hb HPHI)].
  intros w Hw. apply (JA_pot_drop segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HBX). exact Hw.
Qed.

Lemma X_Es_fs0 : ltac2:(tb__ "0|3|
S23S3S2dQ40A1A1M0G0VTR;S2eS20VJAFv;S35S32U0M1A2S6eA2S70R3R2A5VFAM;S36S0S1S1SdS12A2M2S2A2S1S21S24A2S0G2S2S0SdS12S70S6eA4G1A4S0S21S24Z18eS6aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS1_checks_fs as (_ & Cxf & Cfeq & Cfb & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cptv' & Cxk & PP1 & PP2 & PWc & PPay & Cnb & Cbr & Cnp).
  pose proof epiS_chk_fs as (_ & _ & _ & CLF & C500 & _ & _ & _ & _ & _ & _ & Chand).
  set (ndv := NDA tv_fs2 frL bd_s0 (AHead pH true)).
  apply (TR_pre (SPA segs (JAv ndv) E_fs2 rho tp)).
  { intros w Hw. rewrite <- Cfeq. apply (SPA_refacts_JA segs); [| exact Cfb |].
    - apply (SPA_axforms segs (JAv ndv) xf_fs2 rho Es_fs0 E_fs21 tp w Cxf).
      unfold ndv. exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL tv_fs2 frL bd_s0 (AHead pH true) Es_fs0 rho tp w Cptv Hw).
    - intros tr md HJ HF1. apply Forall_app. split; [|exact HF1]. constructor; [|constructor].
      exact (nnPhi2_holds rho tp tr md HF1 HJ). }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD = 0 -> uval rho szL = 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ. intros E0'.
    apply (proj1 (Forall_forall _ _) HZ (xLD, szL)); [unfold tv_fs2; apply in_or_app; left; exact lines_in_kept_fs2|].
    unfold tnz. cbn [fst]. intros H. exact (H E0'). }
  intros Hnull.
  unfold ndv, tv_fs2.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX FSP.P0_fs PTrue (fun _ H => H) (fun _ _ _ H => H)
           FS.Pre_fs FS.nd0 PDk_fs2 FS.NP eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHF eq_refl
           E_fs2 s_fs2 R_fs2 Xk_fs2 rho tp kept_fs2 passed_fs2 frL bd_s0 brest_fs2 (AHead pH true) (FAM (efmeasA (Es_fs0, nd_s0, 0%nat, (398, z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand. unfold payA. exact (pay_okF_split _ _ _ _ bd_s0 (hand_fs2 ++ brest_fs2) bdrest_fs2 payX_fs2 payY_fs2 PP1 PP2 PWc PPay).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_fs2 rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _.
    assert (HPHI' : ldefR rho') by exact (ldefR_call CST FB FF rho0 E_fs2 kept_fs2 rho rho' HF CLF C500 Hag HK lines_in_kept_fs2 Hnull HPHI).
    pose proof epiS1_checks_nd as (Cndn & Cndo & Cndz & CTn & CTo & CTf & CTz & Bn & Bo & Bz & Tin & Tio & Tiz & _ & _ & _ & CABS).
    cbn [PDk_fs2 liftPD FSP.PD_fs map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[Hd|[Hd|[]]]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite CTn, Cndn.
      apply (TR_pre (SPA segs (JAv nd_nop2) T_nop2 rho' tp')).
      { intros w Hw. rewrite <- Tin. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_nop2) (xfb_fs2 T_nop20) rho' T_nop20 B_nop2 tp' w Bn Hw). }
      apply (CUTS1 T_nop2 nd_nop2 0%nat (397, z0) rho' tp'); [right; left; reflexivity | exact HPHI' | meas].
    +
      rewrite CTo, Cndo.
      apply (TR_pre (SPA segs (JAv nd_ok2) T_ok2 rho' tp')).
      { intros w Hw. rewrite <- Tio. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_ok2) (xfb_fs2 T_ok20) rho' T_ok20 B_ok2 tp' w Bo Hw). }
      apply (CUTS1 T_ok2 nd_ok2 0%nat (397, z0) rho' tp'); [right; right; left; reflexivity | exact HPHI' | meas].
    +
      rewrite CTf. apply TR_facts. intros HFf. exfalso.
      pose proof (holds_mem _ _ _ HFf CABS) as FA. cbn [holds f_absurd] in FA. apply FA. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    +
      rewrite CTz, Cndz.
      apply (TR_pre (SPA segs (JAv nd_fz2) T_fz2 rho' tp')).
      { intros w Hw. rewrite <- Tiz. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_fz2) (xfb_fs2 T_fz20) rho' T_fz20 B_fz2 tp' w Bz Hw). }
      apply (CUTS1 T_fz2 nd_fz2 0%nat (397, z0) rho' tp'); [right; right; right; left; reflexivity | exact HPHI' | meas].
Qed.

Lemma X_L_sn : ltac2:(tb__ "0|3|
S23S3S2dQ40A1A1M0G0VTR;S2eS20VJAFv;S35S32U0M1A2S76A2S73R3R2A5VFAM;S36S0S1S1SdS12A2M2S2A2S1S21S24A2S0G2S2S0SdS12S73S76A4G1A4S0S21S24Z18cS6aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS1_checks_succ as (_ & _ & _ & _ & Cen & Cidn & _ & _ & Cpn & _ & _ & Ctvn & Cbn & _ & _ & Camn).
  pose proof epiS_chk_succ as (Cnpn & Cnbn & Cfrn & Cphin & _).
  pose proof (phi_sub V_ldR ldefR ldefR_reads s_nn rho Cphin HPHI) as HPHI'.
  apply (TR_pre (SPA segs (JAv nd_succ) K_succ (rho_sub rho s_nn) tp)).
  { intros w Hw.
    apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L_sn K_succ s_nn (NDA tvL frL bd_nop2 (AHead qHn2 true)) nd_succ rho tp w
             Cen Cidn Cnpn Cnbn Ctvn Cfrn Cbn Camn).
    unfold nd_nop2 in Hw. exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_nop2 tvL frL bd_nop2 (AHead qHn2 true) L_sn rho tp w Cpn Hw). }
  apply (CUTS2a K_succ nd_succ 0%nat (395, z0) (rho_sub rho s_nn) tp); [left; reflexivity | exact HPHI' | meas].
Qed.
Lemma X_L_sk : ltac2:(tb__ "0|3|
S23S3S2dQ40A1A1M0G0VTR;S2eS20VJAFv;S35S32U0M1A2S77A2S72R3R2A5VFAM;S36S0S1S1SdS12A2M2S2A2S1S21S24A2S0G2S2S0SdS12S72S77A4G1A4S0S21S24Z18cS6aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS1_checks_succ as (_ & _ & _ & _ & _ & _ & Cek & Cidk & _ & Cpk & Ctvk & _ & _ & Cbk & Camk & _).
  pose proof epiS_chk_succ as (_ & _ & _ & _ & Cnpk & Cnbk & Cfrk & Cphik & _).
  pose proof (phi_sub V_ldR ldefR ldefR_reads s_kn rho Cphik HPHI) as HPHI'.
  apply (TR_pre (SPA segs (JAv nd_succ) K_succ (rho_sub rho s_kn) tp)).
  { intros w Hw.
    apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L_sk K_succ s_kn (NDA tvL_k frL bd_ok2 (AHead qHk2 true)) nd_succ rho tp w
             Cek Cidk Cnpk Cnbk Ctvk Cfrk Cbk Camk).
    unfold nd_ok2 in Hw. exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_ok2 tvL_k frL bd_ok2 (AHead qHk2 true) L_sk rho tp w Cpk Hw). }
  apply (CUTS2a K_succ nd_succ 0%nat (395, z0) (rho_sub rho s_kn) tp); [left; reflexivity | exact HPHI' | meas].
Qed.
Lemma X_L_dz : ltac2:(tb__ "0|3|
S23S3S2dQ40A1A1M0G0VTR;S2eS20VJAFv;S35S32U0M1A2S75A2S71R3R2A5VFAM;S36S0S1S1SdS12A2M2S2A2S1S21S24A2S0G2S2S0SdS12S71S75A4G1A4S0S21S24Z18cS6aA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS4_chk_land as (_ & _ & _ & CL). pose proof epiS_chk_landphi as (_ & _ & _ & CP & _). pose proof epiS_chk_succ as (_ & _ & _ & _ & _ & _ & _ & _ & Cpz).
  apply (TR_pre (SPA segs (JAv (NDA tvL frL bd_fz2 (AHead qHz2 false))) L_dz rho tp)).
  { intros w Hw. unfold nd_fz2 in Hw. exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_fz2 tvL frL bd_fz2 (AHead qHz2 false) L_dz rho tp w Cpz Hw). }
  apply (X_LANDf L_dz bd_fz2 qHz2 _ rho tp tp0 CL CP); [rewrite DP.efmeas_z0; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact HPHI].
Qed.

Lemma bnds_hold : ltac2:(tb__ "0|0|
S23S3S25A1S33R2A1S69S25S28R3A1R2A3S3fS5S43S25S29Sb4A1R3A3S4A3S3fS5S43S25S29Sb3A1R4A3S4A3S3fS5S44S25S25S43S25S29R1A1R6A3Lf;Sb2A3S4A3S69S25S28R7A1S5eA3F_;F_;F_;F_;F_;FF;Frho;").
Proof using .
  intros rho F HP HF C1 C2 C3.
  destruct (rate2_bounds rho (ldefR_rate rho HP) (holds_mem _ _ _ HF C1) (holds_mem _ _ _ HF C2)) as [B1 B3].
  cbn [cc_facts forallb] in C3. apply andb_prop in C3 as [D1 C3]. apply andb_prop in C3 as [D2 C3]. apply andb_prop in C3 as [D3 C3]. apply andb_prop in C3 as [D4 _].
  pose proof (holds_mem _ _ _ HF D1) as G1. pose proof (holds_mem _ _ _ HF D2) as G2. pose proof (holds_mem _ _ _ HF D3) as G3. pose proof (holds_mem _ _ _ HF D4) as G4.
  rewrite h_ule in G1, G2, G3, G4. rewrite uval_lit in G2, G4 by lia.
  unfold bnds, B32m. cbn [map].
  constructor; [exact B1|]. constructor; [rewrite h_ule, uval_lit by lia; lia|]. constructor; [exact B3|]. constructor; [rewrite h_ule, uval_lit by lia; lia|]. constructor.
Qed.
Lemma X_L_v0 : ltac2:(tb__ "0|1|
SdSdS23S3S2dQ40A1A1M0S21G0S3fS5S44S25S2bS91R6A1A1S6S25S5eS90R6A1A3A3S4A3S3fSdScaR7S6S25S5eS90R7A1A3A2R6A3S3fS5S43S25S29Sb4A1S90R8A1A3S4A3S3fS5S43S25S29Sb3A1S90R9A1A3S4A3S3fS5S44S25S25S43S25S29R1A1S90RbA1A3Lf;Sb2A3S4A3S3fS5S60RaS5bS6cS5aU1A1A4S4A3S3fS5S38S34Sa9S49SeRbA1SeS5bA1A3A2S4A3S55S59S57S4aS58Z2Z40A2A2Z37aA2R9A2VTR;S2eS20VJAFv;S35S32U0A2S6cA2ReRcRbA5VFAM;RaR9A2A2F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FLb;FL;").
Proof.
  intros L Lb rho tp b tp0 Cfb Cwf Cnx Clen Ccc HE Cphi Hb. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  destruct (ent_chk2_unf Lb B_1 nd_succ (ndAt 1) HE) as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  pose proof (phi_sub V_ldR ldefR ldefR_reads _ rho Cphi HPHI) as HPHI'.
  apply (TR_pre (SPA segs (JAv (ndAt 1)) B_1 (rho_sub rho (infer_sub NP (ax_S Lb) (ax_S B_1))) tp)).
  { intros w Hw.
    apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc Lb B_1 _ nd_succ (ndAt 1) rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam).
    rewrite <- Cwf. apply (SPA_refacts_JA segs); [exact Hw | exact Cfb |].
    intros tr md _ HF. apply Forall_app. split; [|exact HF]. exact (bnds_hold rho _ HPHI HF Cnx Clen Ccc). }
  apply (CUTS2b B_1 (ndAt 1) 0%nat (RB, zl 890) _ tp); [left; reflexivity | exact HPHI' |].
  rewrite efmeas_lit by (vm_compute; split; [discriminate | reflexivity]). split; [vm_compute; discriminate | exact Hb].
Qed.

Lemma fail_potin : ltac2:(tb__ "0|2|
SdS3S8dA1M0G0S45S23S3S2dQ40A1A1S3fS5S3bS27SeR6A1A1S6S8dR5S5fA3R4A3S4A3VTR;S2eS20VJAv;S16S66S64R6S15Sa6S4A2A4A1R7R3R2A5R4A2VTR;S2eS20VJAv;S16S6S1S24S24A2M1S61SaG1Sc9ScG1A1A3A3S64R6S15Sa6S9A2A4A1R8R4R3A5R5A2F_;F_;Ftp;Frho;FQ;Fbrest;Fbdn;FTf;").
Proof.
  intros Tf bdn brest Q rho tp Hle H. apply (TR_pre (SPA segs (JAv (NDA tvL frL bdn (AHead pH true))) Tf rho tp)); [|exact H]. intros w Hw.
  apply (SPA_JA_pot_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL frL bdn pH Tf rho tp w (BXok_d_nn 7 BX HBX)).
  exact (SPA_JA_le2 segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL frL brest (bdn ++ ENDOWs) (AHead pH false) Tf rho tp w Hle Hw).
Qed.
Ltac xblk CHK E0 E Tk0 TkB Tk Tf0 TfB Tf R d e c k bcom dupj dupn qHk rho tp HPHI :=
  pose proof CHK as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26
                     & C27 & C28 & C29 & C30 & C31 & C32 & C33 & C34 & C35 & C36 & C37 & C38 & C39 & C40);
  apply (X_BLK AInv CST XGL ALA HCST HXGL HXlits Kc HKc FB FF BX HBX rho0 TR TR_facts TR_ex TR_pre TR_pureP TR_callP CAD
           E0 E Tk0 TkB Tk Tf0 TfB Tf R d e c k bcom dupj dupn qHk _ rho tp
           ltac:(vm_compute; repeat (first [left; reflexivity | right])) ltac:(lia)
           C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 C36); [ | | exact HPHI].
Lemma X_E0_1 : ltac2:(tb__ "0|4|
S23S3S2dQ40A1A1M0G0VTR;S2eS20VJAFv;S35S32U0M1A2S5aU1A1M2A2Sb5R3R2A5VFAM;S36S0S1S1SdS12A2M3S2A2S1S21S24A2S0G3S2S0SdS12Sb5G2A4G1A4S0S21S24S4aS4bZ379A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  change (ndAt 1) with (NDA (kept_ad ++ [blkAR]) frL (bd_com (cAt 1) (kAt 1) ++ dupAt 1) (AHead pH true)).
  xblk st_chk_1 E0_1 E_1 Tk0_1 TkB_1 Tk_1 Tf0_1 TfB_1 Tf_1 R_1 (SVar 400) 4 (SMd M_MUL (SVar 401) (SLit 3)) (SVar 402) (bd_com (cAt 1) (kAt 1)) (dupAt 1) (dupAt 2) qHk_1 rho tp HPHI.
  - intros rho' tp' HP'. apply (CUTS2b Tk_1 (ndK 1 qHk_1) 0%nat (RB, zl 888) rho' tp');  [do 1 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (fail_potin Tf_1 (bdAt 2) (bd_com (cAt 1) (kAt 1) ++ dupAt 2) _ rho' tp' C40).
    apply (CUTS2b Tf_1 (ndAt 2) 0%nat (RB, zl 888) rho' tp');  [do 2 right; left; reflexivity | exact HP' | meas].
Qed.
Lemma X_E0_2 : ltac2:(tb__ "0|4|
S23S3S2dQ40A1A1M0G0VTR;S2eS20VJAFv;S35S32U0M1A2S5aU2A1M2A2Sb6R3R2A5VFAM;S36S0S1S1SdS12A2M3S2A2S1S21S24A2S0G3S2S0SdS12Sb6G2A4G1A4S0S21S24S4aS4bZ36fA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  change (ndAt 2) with (NDA (kept_ad ++ [blkAR]) frL (bd_com (cAt 2) (kAt 2) ++ dupAt 2) (AHead pH true)).
  xblk st_chk_2 E0_2 E_2 Tk0_2 TkB_2 Tk_2 Tf0_2 TfB_2 Tf_2 R_2 (SVar 403) 4 (SVar 404) (SVar 405) (bd_com (cAt 2) (kAt 2)) (dupAt 2) (dupAt 3) qHk_2 rho tp HPHI.
  - intros rho' tp' HP'. apply (CUTS2b Tk_2 (ndK 2 qHk_2) 0%nat (RB, zl 878) rho' tp');  [do 4 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (fail_potin Tf_2 (bdAt 3) (bd_com (cAt 2) (kAt 2) ++ dupAt 3) _ rho' tp' C40).
    apply (CUTS2b Tf_2 (ndAt 3) 0%nat (RB, zl 878) rho' tp');  [do 5 right; left; reflexivity | exact HP' | meas].
Qed.
Lemma X_E0_3 : ltac2:(tb__ "0|4|
S23S3S2dQ40A1A1M0G0VTR;S2eS20VJAFv;S35S32U0M1A2S5aU3A1M2A2Sb7R3R2A5VFAM;S36S0S1S1SdS12A2M3S2A2S1S21S24A2S0G3S2S0SdS12Sb7G2A4G1A4S0S21S24S4aS4bZ365A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  change (ndAt 3) with (NDA (kept_ad ++ [blkAR]) frL (bd_com (cAt 3) (kAt 3) ++ dupAt 3) (AHead pH true)).
  xblk st_chk_3 E0_3 E_3 Tk0_3 TkB_3 Tk_3 Tf0_3 TfB_3 Tf_3 R_3 (SVar 406) 4 (SVar 407) (SVar 408) (bd_com (cAt 3) (kAt 3)) (dupAt 3) (dupAt 4) qHk_3 rho tp HPHI.
  - intros rho' tp' HP'. apply (CUTS2b Tk_3 (ndK 3 qHk_3) 0%nat (RB, zl 868) rho' tp');  [do 7 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (fail_potin Tf_3 (bdAt 4) (bd_com (cAt 3) (kAt 3) ++ dupAt 4) _ rho' tp' C40).
    apply (CUTS2b Tf_3 (ndAt 4) 0%nat (RB, zl 868) rho' tp');  [do 8 right; left; reflexivity | exact HP' | meas].
Qed.
Lemma X_E0_4 : ltac2:(tb__ "0|4|
S23S3S2dQ40A1A1M0G0VTR;S2eS20VJAFv;S35S32U0M1A2S5aU4A1M2A2Sb8R3R2A5VFAM;S36S0S1S1SdS12A2M3S2A2S1S21S24A2S0G3S2S0SdS12Sb8G2A4G1A4S0S21S24S4aS4bZ35bA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  change (ndAt 4) with (NDA (kept_ad ++ [blkAR]) frL (bd_com (cAt 4) (kAt 4) ++ dupAt 4) (AHead pH true)).
  xblk st_chk_4 E0_4 E_4 Tk0_4 TkB_4 Tk_4 Tf0_4 TfB_4 Tf_4 R_4 (SVar 409) 4 (SAlu ALU_SLL (SVar 410) (SLit 1)) (SVar 411) (bd_com (cAt 4) (kAt 4)) (dupAt 4) (dupAt 5) qHk_4 rho tp HPHI.
  - intros rho' tp' HP'. apply (CUTS2b Tk_4 (ndK 4 qHk_4) 0%nat (RB, zl 858) rho' tp');  [do 10 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (fail_potin Tf_4 (bdAt 5) (bd_com (cAt 4) (kAt 4) ++ dupAt 5) _ rho' tp' C40).
    apply (CUTS2b Tf_4 (ndAt 5) 0%nat (RB, zl 858) rho' tp');  [do 11 right; left; reflexivity | exact HP' | meas].
Qed.
Lemma X_E0_5 : ltac2:(tb__ "0|4|
S23S3S2dQ40A1A1M0G0VTR;S2eS20VJAFv;S35S32U0M1A2S5aU5A1M2A2Sb9R3R2A5VFAM;S36S0S1S1SdS12A2M3S2A2S1S21S24A2S0G3S2S0SdS12Sb9G2A4G1A4S0S21S24S4aS4bZ351A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  change (ndAt 5) with (NDA (kept_ad ++ [blkAR]) frL (bd_com (cAt 5) (kAt 5) ++ dupAt 5) (AHead pH true)).
  xblk st_chk_5 E0_5 E_5 Tk0_5 TkB_5 Tk_5 Tf0_5 TfB_5 Tf_5 R_5 (SVar 412) 4 (SVar 413) (SVar 414) (bd_com (cAt 5) (kAt 5)) (dupAt 5) (dupAt 6) qHk_5 rho tp HPHI.
  - intros rho' tp' HP'. apply (CUTS2b Tk_5 (ndK 5 qHk_5) 0%nat (RB, zl 848) rho' tp');  [do 13 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (fail_potin Tf_5 (bdAt 6) (bd_com (cAt 5) (kAt 5) ++ dupAt 6) _ rho' tp' C40).
    apply (CUTS2b Tf_5 (ndAt 6) 0%nat (RB, zl 848) rho' tp');  [do 14 right; left; reflexivity | exact HP' | meas].
Qed.
Lemma X_E0_6 : ltac2:(tb__ "0|4|
S23S3S2dQ40A1A1M0G0VTR;S2eS20VJAFv;S35S32U0M1A2S5aU6A1M2A2SbaR3R2A5VFAM;S36S0S1S1SdS12A2M3S2A2S1S21S24A2S0G3S2S0SdS12SbaG2A4G1A4S0S21S24S4aS4bZ347A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  change (ndAt 6) with (NDA (kept_ad ++ [blkAR]) frL (bd_com (cAt 6) (kAt 6) ++ dupAt 6) (AHead pH true)).
  xblk st_chk_6 E0_6 E_6 Tk0_6 TkB_6 Tk_6 Tf0_6 TfB_6 Tf_6 R_6 (SVar 415) 4 (SVar 416) (SVar 417) (bd_com (cAt 6) (kAt 6)) (dupAt 6) (dupAt 7) qHk_6 rho tp HPHI.
  - intros rho' tp' HP'. apply (CUTS2b Tk_6 (ndK 6 qHk_6) 0%nat (RB, zl 838) rho' tp');  [do 16 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (CUTS2b Tf_6 (ndF 6) 0%nat (RB, zl 838) rho' tp');  [do 17 right; left; reflexivity | exact HP' | meas].
Qed.
Lemma X_E0_8 : ltac2:(tb__ "0|3|
S23S3S2dQ40A1A1M0G0VTR;S2eS20VJAFv;S35S32U0M1A2Sa3A2SbbR3R2A5VFAM;S36S0S1S1SdS12A2M2S2A2S1S21S24A2S0G2S2S0SdS12SbbSa3A4G1A4S0S21S24S4aS4bZ333A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  change (nd8) with (NDA (kept_ad ++ [blkAR]) frL (bd_com (cAt 7) (kAt 7) ++ dupAt 7) (AHead pH true)).
  xblk st_chk_8 E0_8 E_8 Tk0_8 TkB_8 Tk_8 Tf0_8 TfB_8 Tf_8 R_8 (SVar 418) 128 (SVar 419) (SVar 420) (bd_com (cAt 7) (kAt 7)) (dupAt 7) (dup8) qHk_8 rho tp HPHI.
  - intros rho' tp' HP'. apply (CUTS4 Tk_8 (ndK8) 0%nat (RB, zl 818) rho' tp'); [do 2 right; left; reflexivity | exact HP' | meas].
  - intros rho' tp' HP'. apply (fail_potin Tf_8 (bd9) (bd_com (cAt 7) (kAt 7) ++ dup8) _ rho' tp' C40).
    apply (CUTS4 Tf_8 (nd9) 0%nat (RB, zl 818) rho' tp'); [do 3 right; left; reflexivity | exact HP' | meas].
Qed.

Ltac above390 := rewrite ?DP.efmeas_z0, ?efmeas_lit by (vm_compute; split; [discriminate | reflexivity]); vm_compute; reflexivity.
Lemma X_L_d6f : ltac2:(tb__ "0|4|
S23S3S2dQ40A1A1M0G0VTR;S2eS20VJAFv;S35S32U0M1A2S54U6A1M2A2S9fR3R2A5VFAM;S36S0S1S1SdS12A2M3S2A2S1S21S24A2S0G3S2S0SdS12S9fG2A4G1A4S0S21S24S4aS4bZ345A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS4_chk_land as (_ & _ & CL & _). pose proof epiS_chk_landphi as (_ & _ & CP & _).
  apply (X_LANDf L_d6f (brestAt 6) pH _ rho tp tp0 CL CP); [above390 | exact HPHI].
Qed.
Lemma X_L_d7 : ltac2:(tb__ "0|4|
S23S3S2dQ40A1A1M0G0VTR;S2eS20VJAFv;S35S32U0M1A2S5aU7A1M2A2Sa0R3R2A5VFAM;S36S0S1S1SdS12A2M3S2A2S1S21S24A2S0G3S2S0SdS12Sa0G2A4G1A4S0S21S24S4aS4bZ33dA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS4_chk_land as (_ & CL & _). pose proof epiS_chk_landphi as (_ & CP & _).
  apply (X_LANDt L_d7 (bdAt 7) pH _ rho tp tp0 CL CP); [above390 | exact HPHI].
Qed.
Lemma X_L_land : ltac2:(tb__ "0|3|
S23S3S2dQ40A1A1M0G0VTR;S2eS20VJAFv;S35S32U0M1A2Sa4A2Sa1R3R2A5VFAM;S36S0S1S1SdS12A2M2S2A2S1S21S24A2S0G2S2S0SdS12Sa1Sa4A4G1A4S0S21S24S4aS4bZ329A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS4_chk_land as (CL & _). pose proof epiS_chk_landphi as (CP & _).
  apply (X_LANDt L_land bd9 pH _ rho tp tp0 CL CP); [above390 | exact HPHI].
Qed.
Lemma X_E_fu0 : ltac2:(tb__ "0|4|
S23S3S2dQ40A1A1M0G0VTR;S2eS20VJAFv;S35S32U0M1A2S5aU7A1M2A2S9eR3R2A5VFAM;S36S0S1S1SdS12A2M3S2A2S1S21S24A2S0G3S2S0SdS12S9eG2A4G1A4S0S21S24S4aS4bZ33dA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiS4_chk_fu as (_ & Cxf & Cent & Cchk & Cnp & Cnb & Cfb & CT0 & CxB & Ctidy & _).
  pose proof epiS_chk_fu as (C500 & _).
  apply (TR_pre (SPA segs (JAv (ndAt 7)) E_fu rho tp)).
  { intros w Hw. exact (SPA_axforms segs (JAv (ndAt 7)) (xf_fu E_fu0) rho E_fu0 E_fu tp w Cxf Hw). }
  apply (PURE_fu E_fu s_fu R_fu rho tp (ndAt 7) _ Cent Cchk Cnp Cnb Cfb).
  intros L rho' HL Hag. cbn [In FU.Posts_fu] in HL. destruct HL as [<-|[]]. cbn [la_state]. rewrite CT0.
  pose proof (ldefR_pure E_fu rho rho' C500 Hag HPHI) as HPHI'.
  apply (TR_pre (SPA segs (JAv (ndAt 7)) T_fu rho' tp)).
  { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact (SPA_axforms segs (JAv (ndAt 7)) (xfb_fu T_fu0) rho' T_fu0 B_fu tp w CxB Hw). }
  apply (CUTS4 T_fu (ndAt 7) 0%nat (RB, zl 828) rho' tp); [left; reflexivity | exact HPHI' | meas].
Qed.

Lemma exitsS1_ok : ltac2:(tb__ "0|4|
SdS12S2S1S21S24A2M0S23S3S2dQ40A1A1M1G1S42S1S1S1SdS12A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS12R7R6A4R5A4R4A4S50A3VTR;S2eS20VJAFv;S35S32R6A2R7A2R8R4R3A5VFAM;S36S0G3G0S0G2S2S0SdS12R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsS1 In] in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <- <- <-.
  - apply X_Es_fs0.
  - apply X_L_sn.
  - apply X_L_sk.
  - apply X_L_dz.
Qed.
Lemma exitsS2a_ok : ltac2:(tb__ "0|4|
SdS12S2S1S21S24A2M0S23S3S2dQ40A1A1M1G1S42S1S1S1SdS12A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS12R7R6A4R5A4R4A4S51A3VTR;S2eS20VJAFv;S35S32R6A2R7A2R8R4R3A5VFAM;S36S0G3G0S0G2S2S0SdS12R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsS2a In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <- <- <-.
  - pose proof epiS_chk_v0 as (Cfb & Cwf & Cnx & Clen & Ccc & HE & Cphi & _).
    apply (X_L_v0 L_v0a Lb_v0a rho tp _ tp0 Cfb Cwf Cnx Clen Ccc HE Cphi). rewrite DP.efmeas_z0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply CONT_cf.
  - pose proof epiS_chk_v0 as (_ & _ & _ & _ & _ & _ & _ & Cfb & Cwf & Cnx & Clen & Ccc & HE & Cphi).
    apply (X_L_v0 L_v0b Lb_v0b rho tp _ tp0 Cfb Cwf Cnx Clen Ccc HE Cphi). rewrite DP.efmeas_z0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma exitsS2b_ok : ltac2:(tb__ "0|4|
SdS12S2S1S21S24A2M0S23S3S2dQ40A1A1M1G1S42S1S1S1SdS12A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS12R7R6A4R5A4R4A4S52A3VTR;S2eS20VJAFv;S35S32R6A2R7A2R8R4R3A5VFAM;S36S0G3G0S0G2S2S0SdS12R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsS2b In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]; injection E as <- <- <- <-.
  - apply X_E0_1.
  - apply X_E0_2.
  - apply X_E0_3.
  - apply X_E0_4.
  - apply X_E0_5.
  - apply X_E0_6.
  - apply X_L_d6f.
  - apply X_L_d7.
  - apply X_E_fu0.
Qed.
Lemma exitsS4_ok : ltac2:(tb__ "0|4|
SdS12S2S1S21S24A2M0S23S3S2dQ40A1A1M1G1S42S1S1S1SdS12A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS12R7R6A4R5A4R4A4S53A3VTR;S2eS20VJAFv;S35S32R6A2R7A2R8R4R3A5VFAM;S36S0G3G0S0G2S2S0SdS12R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsS4 In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <- <- <-.
  - apply X_E0_8.
  - apply X_L_land.
Qed.
End X.

Let frozen_stable : ltac2:(tb__ "0|0|
S22S22S12S23Sb0S49R3A2S3fS5S17R4R3A2S4A3S31S20R6S1dVAInv;VCST;VXGL;S49VKc;Vrho0;VP0;VFB;VFF;VBX;S13R4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;") := ltac2:(tb__ "0|0|
Sc7VAInv;VCST;VXGL;VALA;S49VKc;VHKc;VFB;VFF;VBX;Vrho0;VP0;Ac").

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S1eS20VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
Sc0S20SbfVAInv;VCST;VXGL;A5").
Variable FAMQ : list word -> assn.
Hypothesis KDISP_T : ltac2:(tb__ "0|1|
S23S3S2dQ40A1A1M0G0S65R3A1S47S20Vok;S2eS20VJAv;S9dA1S8fR4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Hypothesis CONT_cf_T : ltac2:(tb__ "0|1|
S23S3S2dQ40A1A1M0G0S47S20Vok;S2eS20VJAFv;S35S32U0A2S6cA2S5cR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHF_T : ltac2:(tb__ "0|1|
S3S1S21S21A2M0A1S3S1G0S21A2A1S8cS23S3S2dQ40A1A1S8bZ5R3A2S47S20Vok;S2eS20S14VAInv;VCST;VXGL;VKc;S6bR6R5A2R6R5R4S13S9aAaS99R3R2A5S80S20S98R3R2S8eVAInv;VCST;VXGL;VKc;S6bS13S6fR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_fs2.
  eapply (sum_PostsC_k segs AInv CST XGL Kc FSP.P0_fs PTrue FS.Pre_fs FS.nd0 FSP.PD_fs FS.NP); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  exact (FSP.finalize_shape_sum AInv CST XGL ALA HCST HXGL HTOP Kc HKc FBc' FFc' BXc' HB' rho2 ok' Hok' AC tp2).
Qed.
Lemma CAD_T : ltac2:(tb__ "0|1|
S3S1S21S21A2M0A1S3S1G0S21A2A1S8cS23S3S2dQ40A1A1S8bZ3R3A2S47S20Vok;S2eS20S14VAInv;VCST;VXGL;VKc;S89VCST;R6R5A3R6R5R4S13S9cAaS9bR3R2A5S80S20SadR3R2S8eVAInv;VCST;VXGL;VKc;S89VCST;A1S13S5dR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_ad.
  eapply (sum_PostsC_k segs AInv CST XGL Kc (ADP.P0_ad CST) PTrue AD.Pre_ad AD.nd0 ADP.PD_ad NF); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  exact (ADP.arena_dup_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc' FFc' BXc' HB' rho2 ok' Hok' AC tp2).
Qed.
Lemma PURE_fu_T : ltac2:(tb__ "0|2|
SdS94S3S2aA1M0S23S3S2dQ40A1A1S12S45S3fS8G0A1S81R7S62R6A3S7G0R5A2A3S3fS5S83R8S62R7R6S68SfSdS10S63A4A5S4A3S3fS5SafS49S26SeR9A1A1A2S4A3S3fS5S17S26SeRaA1A1R5A2S4A3S3fS5S44S25S2bS26SeRbA1M1A1A1S27G1A1A3S4A3SfS23S42SfR2S63A3S2cS26SeRfA1A1RcR2A3S47S20Vok;S2eS20VJAv;RbA1SaaS27SeR10A1A1S84RfS62S10R4A1R10ReA5A2R3RcA5RaA4F_;F_;Frho';FL;S47S20Vok;S2eS20VJAv;R8A1RdRaR9A5R7A4F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA ok Cl FU.Pre_fu s R FU.Posts_fu rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply FU.finalize_unknowns_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
Qed.

Let famS (cuts : list efnode) (tp0 : list word) : Z -> list word -> assn := ltac2:(tb__ "0|0|
S21S3S2dQ40A1A1S48S41Sd0S20S68S39SacS3eVAInv;VCST;VXGL;S49VKc;Vrho0;VP0;VFB;VFF;VBX;S13S32AcS68S37S39S3cVcuts;A4A4R1A3VFAMQ;Vtp0;R1A2A2Lw;L_;L_;").
Lemma reenterS : ltac2:(tb__ "0|6|
S3S1S1S1SdS12A2M0S2A2M1S1S21S24A2M2A2M3A1S3S2dQ40A1A1M4SdS12S2G2S23G4S21G4S42G3S0G1G2S0G0S2S0SdS12R8R7A4R6A4R5A4RaA3S35S32R7R5A3S40S56Z0S36S0G1G2S0G0S2S0SdS12RaR9A4R8A4R7A4R6A2M5A2S55G5R4A2A2S47S20Vok;S2eS20VJAv;RaA1RbR7R6A5VfamS;RdRcR5R4A4A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Ftp0;Fcuts;").
Proof.
  intros cuts tp0 T nd k rv rho tp b tp0' Hin Hphi _.
  apply (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisS ok (map efdrop cuts) T nd k (FAMQ tp0) rho tp); [|exact Hphi].
  apply in_map_iff. exists (T, nd, k, rv). split; [reflexivity | exact Hin].
Qed.
Lemma rightS : ltac2:(tb__ "0|1|
S3S37A1S3S2dQ40A1A1M0S45S21G0S47S20Vok;R3VFAMQ;R4A1A4S47S20Vok;R4VfamS;R6R5R3R2A4A4F_;Ftp0';Fb;FP;Ftp0;Fcuts;").
Proof. intros cuts tp0 P b tp0' H. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact H]. Qed.

Lemma S4_T : ltac2:(tb__ "0|4|
SdS12S2S1S21S24A2M0S23S3S2dQ40A1A1M1G1S42S1S1S1SdS12A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS12R7R6A4R5A4R4A4S4fA3S35S32R6R4A3S47S20Vok;S2eS20VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertS4_ok 300%nat cps_c NP cutsS4 exitsS4 ok (FAMQ tp0) Hok
           ecertS4_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsS4_ok (triple segs ok) (famS cutsS4 tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CAD_T (reenterS cutsS4 tp0)
           (fun rho tp b tp0' HL _ => rightS cutsS4 tp0 _ b tp0' (KDISP_T rho tp tp0 HL)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.
Lemma S2b_T : ltac2:(tb__ "0|4|
SdS12S2S1S21S24A2M0S23S3S2dQ40A1A1M1G1S42S1S1S1SdS12A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS12R7R6A4R5A4R4A4S4eA3S35S32R6R4A3S47S20Vok;S2eS20VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertS2b_ok 300%nat cps_b NP cutsS2b exitsS2b ok (FAMQ tp0) Hok
           ecertS2b_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsS2b_ok (triple segs ok) (famS cutsS2b tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CAD_T (fun Cl s R rho tp nd Q => PURE_fu_T Cl s R rho tp nd Q) (reenterS cutsS2b tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightS cutsS2b tp0 _ b tp0' (S4_T T nd k rv rho tp tp0 Hi Hp))
           (fun rho tp b tp0' HL _ => rightS cutsS2b tp0 _ b tp0' (KDISP_T rho tp tp0 HL)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.
Lemma S2a_T : ltac2:(tb__ "0|4|
SdS12S2S1S21S24A2M0S23S3S2dQ40A1A1M1G1S42S1S1S1SdS12A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS12R7R6A4R5A4R4A4S4dA3S35S32R6R4A3S47S20Vok;S2eS20VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertS2a_ok 300%nat cps_b NP cutsS2a exitsS2a ok (FAMQ tp0) Hok
           ecertS2a_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsS2a_ok (triple segs ok) (famS cutsS2a tp0) (TRs_pre segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightS cutsS2a tp0 _ b tp0' (S2b_T T nd k rv rho tp tp0 Hi Hp))
           (fun rho tp tp0' => rightS cutsS2a tp0 _ _ tp0' (CONT_cf_T rho tp tp0)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.
Lemma S1_T : ltac2:(tb__ "0|4|
SdS12S2S1S21S24A2M0S23S3S2dQ40A1A1M1G1S42S1S1S1SdS12A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS12R7R6A4R5A4R4A4S4cA3S35S32R6R4A3S47S20Vok;S2eS20VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertS1_ok 300%nat cps_s NP cutsS1 exitsS1 ok (FAMQ tp0) Hok
           ecertS1_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsS1_ok (triple segs ok) (famS cutsS1 tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CHF_T (reenterS cutsS1 tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp _ => rightS cutsS1 tp0 _ b tp0' (S2a_T T nd k rv rho tp tp0 Hi Hp))
           (fun rho tp b tp0' HL _ => rightS cutsS1 tp0 _ b tp0' (KDISP_T rho tp tp0 HL)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.

Theorem epiS_T : ltac2:(tb__ "0|1|
S23S3S2dQ40A1A1M0G0S33R3A1S47S20Vok;S2eS20VJAv;S6eA1Sa5R4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0 HL. exact (S1_T K_after0 nd_s0 0%nat (399, z0) rho tp tp0 ltac:(left; reflexivity) HL). Qed.

Theorem epiS_B1_T : ltac2:(tb__ "0|1|
S23S3S2dQ40A1A1M0G0S33R3A1S47S20Vok;S2eS20VJAv;S5aU1A1A1S5bR4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0 HL. exact (S2b_T B_1 (ndAt 1) 0%nat (RB, zl 890) rho tp tp0 ltac:(left; reflexivity) HL). Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sc1S20SbfVAInv;VCST;VXGL;A5").
Variable FAM : ltac2:(tb__ "0|0|
S21S3S2dQ40A1A1S45F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S21S21S3S2dQ40A1A1S48S56R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis KDISP_E : ltac2:(tb__ "0|1|
S23S3S2dQ40A1A1M0G0S65R3A1S46S20S2eS20VJAv;S9dA1S8fR4R3A5VFAM;S57Z186S58Z2Z40A2A2R2A2A3F_;Ftp0;Ftp;Frho;").
Hypothesis CONT_cf_E : ltac2:(tb__ "0|3|
S23S3S2dQ40A1A1M0G0S46S20S2eS20VJAFv;S35S32U0M1A2S6cA2S5cR3R2A5VFAM;S36S0S1S1SdS12A2M2S2A2S1S21S24A2S0G2S2S0SdS12S5cS6cA4G1A4S0S21S24Z18aS6aA4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHF_E : ltac2:(tb__ "0|1|
S3S1S21S21A2M0A1S3S1G0S21A2A1S8cS23S3S2dQ40A1A1S8bZ5R3A2S46S20S2eS20S14VAInv;VCST;VXGL;VKc;S6bR6R5A2R6R5R4S13S9aAaS99R3R2A5S80S20S98R3R2S8eVAInv;VCST;VXGL;VKc;S6bS13S6fR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_fs2.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc FSP.P0_fs PTrue FS.Pre_fs FS.nd0 FSP.PD_fs FS.NP); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  exact (FSP.finalize_shape_sum_ex AInv CST XGL ALA HCST HXGL HTOP Kc HKc FBc' FFc' BXc' HB' rho2 ACX tp2).
Qed.
Lemma CAD_E : ltac2:(tb__ "0|1|
S3S1S21S21A2M0A1S3S1G0S21A2A1S8cS23S3S2dQ40A1A1S8bZ3R3A2S46S20S2eS20S14VAInv;VCST;VXGL;VKc;S89VCST;R6R5A3R6R5R4S13S9cAaS9bR3R2A5S80S20SadR3R2S8eVAInv;VCST;VXGL;VKc;S89VCST;A1S13S5dR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_ad.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc (ADP.P0_ad CST) PTrue AD.Pre_ad AD.nd0 ADP.PD_ad NF); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  exact (ADP.arena_dup_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc' FFc' BXc' HB' rho2 ACX tp2).
Qed.
Lemma PURE_fu_E : ltac2:(tb__ "0|2|
SdS94S3S2aA1M0S23S3S2dQ40A1A1S12S45S3fS8G0A1S81R7S62R6A3S7G0R5A2A3S3fS5S83R8S62R7R6S68SfSdS10S63A4A5S4A3S3fS5SafS49S26SeR9A1A1A2S4A3S3fS5S17S26SeRaA1A1R5A2S4A3S3fS5S44S25S2bS26SeRbA1M1A1A1S27G1A1A3S4A3SfS23S42SfR2S63A3S2cS26SeRfA1A1RcR2A3S46S20S2eS20VJAv;RbA1SaaS27SeR10A1A1S84RfS62S10R4A1R10ReA5A2R3RcA5RaA3F_;F_;Frho';FL;S46S20S2eS20VJAv;R8A1RdRaR9A5R7A3F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA_ex segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA Cl FU.Pre_fu s R FU.Posts_fu rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply FU.finalize_unknowns_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
Qed.

Let famE (cuts : list efnode) (tp0 : list word) : Z -> list word -> assn := ltac2:(tb__ "0|0|
S21S3S2dQ40A1A1S48S41ScfS20S68S37SabS3dVAInv;VCST;VXGL;S49VKc;Vrho0;VP0;VFB;VFF;VBX;S13S32AcVcuts;A4R3R1A4VFAM;R3Vtp0;R1A3A2Lw;L_;Lb;").
Lemma reenterE : ltac2:(tb__ "0|6|
S3S1S1S1SdS12A2M0S2A2M1S1S21S24A2M2A2M3A1S3S2dQ40A1A1M4SdS12S2G2S23G4S21G4S42G3S0G1G2S0G0S2S0SdS12R8R7A4R6A4R5A4RaA3S35S32R7R5A3S40S56Z0S36S0G1G2S0G0S2S0SdS12RaR9A4R8A4R7A4R6A2M5A2S55G5R4A2A2S46S20S2eS20VJAv;RaA1RbR7R6A5VfamE;RdRcR5R4A4A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Ftp0;Fcuts;").
Proof.
  intros cuts tp0 T nd k rv rho tp b tp0' Hin Hphi Hm.
  exact (ereenter_cutJAF_b segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisS cuts T nd k rv (FAM b tp0) b rho tp Hin Hphi Hm).
Qed.
Lemma rightE : ltac2:(tb__ "0|1|
S3S37A1S3S2dQ40A1A1M0S45S21S21G0S56R3R2A2S46S20R5VFAM;R4R6A2A3S46S20R6VfamE;R8R7R4R3A4A3F_;F_;Ftp0';Fb;Fm;FP;Ftp0;Fcuts;").
Proof. intros cuts tp0 P m b tp0' Hm H. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact (FAM_mono m b tp0 w Hm Hw) | exact H]. Qed.

Lemma S4_E : ltac2:(tb__ "0|4|
SdS12S2S1S21S24A2M0S23S3S2dQ40A1A1M1G1S42S1S1S1SdS12A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS12R7R6A4R5A4R4A4S4fA3S35S32R6R4A3S46S20S2eS20VJAv;R8A1R9R5R4A5VFAM;S36S0G3G0S0G2S2S0SdS12R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertS4_ok 300%nat cps_c NP cutsS4 exitsS4 (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertS4_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsS4_ok (etriple segs) (famE cutsS4 tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CAD_E (reenterE cutsS4 tp0)
           (fun rho tp b tp0' HL Hb => rightE cutsS4 tp0 _ _ b tp0' (Z.lt_le_incl _ _ Hb) (KDISP_E rho tp tp0 HL)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.
Lemma S2b_E : ltac2:(tb__ "0|4|
SdS12S2S1S21S24A2M0S23S3S2dQ40A1A1M1G1S42S1S1S1SdS12A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS12R7R6A4R5A4R4A4S4eA3S35S32R6R4A3S46S20S2eS20VJAv;R8A1R9R5R4A5VFAM;S36S0G3G0S0G2S2S0SdS12R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertS2b_ok 300%nat cps_b NP cutsS2b exitsS2b (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertS2b_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsS2b_ok (etriple segs) (famE cutsS2b tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CAD_E (fun Cl s R rho tp nd Q => PURE_fu_E Cl s R rho tp nd Q) (reenterE cutsS2b tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp Hm => rightE cutsS2b tp0 _ _ b tp0' (Z.lt_le_incl _ _ (proj2 Hm)) (S4_E T nd k rv rho tp tp0 Hi Hp))
           (fun rho tp b tp0' HL Hb => rightE cutsS2b tp0 _ _ b tp0' (Z.lt_le_incl _ _ Hb) (KDISP_E rho tp tp0 HL)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.
Lemma S2a_E : ltac2:(tb__ "0|4|
SdS12S2S1S21S24A2M0S23S3S2dQ40A1A1M1G1S42S1S1S1SdS12A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS12R7R6A4R5A4R4A4S4dA3S35S32R6R4A3S46S20S2eS20VJAv;R8A1R9R5R4A5VFAM;S36S0G3G0S0G2S2S0SdS12R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertS2a_ok 300%nat cps_b NP cutsS2a exitsS2a (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertS2a_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsS2a_ok (etriple segs) (famE cutsS2a tp0) (TRe_pre segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           (fun T nd k rv rho tp b tp0' Hi Hp Hm => rightE cutsS2a tp0 _ _ b tp0' (Z.lt_le_incl _ _ (proj2 Hm)) (S2b_E T nd k rv rho tp tp0 Hi Hp))
           (fun rho tp tp0' => rightE cutsS2a tp0 _ _ _ tp0' (Z.le_refl _) (CONT_cf_E rho tp tp0)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.
Lemma S1_E : ltac2:(tb__ "0|4|
SdS12S2S1S21S24A2M0S23S3S2dQ40A1A1M1G1S42S1S1S1SdS12A2M2S2A2M3G0A2S0G3G0S0G2S2S0SdS12R7R6A4R5A4R4A4S4cA3S35S32R6R4A3S46S20S2eS20VJAv;R8A1R9R5R4A5VFAM;S36S0G3G0S0G2S2S0SdS12R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertS1_ok 300%nat cps_s NP cutsS1 exitsS1 (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertS1_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsS1_ok (etriple segs) (famE cutsS1 tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CHF_E (reenterE cutsS1 tp0)
           (fun T nd k rv rho tp b tp0' Hi Hp Hm => rightE cutsS1 tp0 _ _ b tp0' (Z.lt_le_incl _ _ (proj2 Hm)) (S2a_E T nd k rv rho tp tp0 Hi Hp))
           (fun rho tp b tp0' HL Hb => rightE cutsS1 tp0 _ _ b tp0' (Z.lt_le_incl _ _ Hb) (KDISP_E rho tp tp0 HL)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.

Theorem epiS_E : ltac2:(tb__ "0|2|
S23S3S2dQ40A1A1M0G0S33R3A1S46S20S2eS20VJAv;S6eA1Sa5R4R3A5VFAM;S36S0S1S1SdS12A2M1S2A2S1S21S24A2S0G1S2S0SdS12Sa5S6eA4U0A4S0S21S24Z18fS6aA4A4R4A2R2A2A3F_;Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0 HL. exact (S1_E K_after0 nd_s0 0%nat (399, z0) rho tp tp0 ltac:(left; reflexivity) HL). Qed.
Theorem epiS_B1_E : ltac2:(tb__ "0|3|
S23S3S2dQ40A1A1M0G0S33R3A1S46S20S2eS20VJAv;S5aU1A1M1A1S5bR4R3A5VFAM;S36S0S1S1SdS12A2M2S2A2S1S21S24A2S0G2S2S0SdS12S5bG1A4U0A4S0S21S24S4aS4bZ37aA1A4A4R4A2R2A2A3F_;Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0 HL. exact (S2b_E B_1 (ndAt 1) 0%nat (RB, zl 890) rho tp tp0 ltac:(left; reflexivity) HL). Qed.
End Existence.
End Sum.
End Lib_load_obj_epiS_pf.

(* [comment removed for export] *)
Module Lib_load_obj_epiCF_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "app"; "prod"; "false"; "cons"; "nil"; "pair"; "Some"; "andb"; "list"; "option"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "sv"; "SPUle"; "SLit"; "ss_next"; "ss_facts"; "sprop_below"; "SAlu"; "SPUlt"; "SVar"; "valuation"; "sobj"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "axwf"; "ax_X"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiCF"; "s_c"; "E_c"; "brest_vr"; "R_c"; "kept_vr"; "Xk_vr"; "nd_cf"; "s_gk"; "C_cf"; "E_c1"; "L_cfZ"; "T_grown"; "T_grownS"; "T_keep"; "bd_vr"; "k_ac"; "s_ent"; "L_cfE"; "L_x"; "T_fail0"; "T_grown0"; "T_keep0"; "bd_cf"; "pcsOf"; "tv_vr"; "xfb_vr"; "B_fail"; "B_grown"; "B_keep"; "E_c0"; "K_w"; "L_xF"; "PDk_vr"; "T_fail"; "T_keepS"; "nd_grown"; "s_bk"; "slot_facts"; "vI"; "vKg"; "L_bk"; "Lf0"; "Lf1"; "Ls_c"; "Ls_f"; "Ls_w"; "Wt"; "bnd_nt"; "cnt0_src"; "d_ac"; "ent_facts"; "hand_vr"; "nd_fail"; "nv_src"; "passed_vr"; "room_vr"; "vcf"; "vr_pc"; "xf_vr"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "bd_below"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vF"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiCF.VRN"; "Pre_vr"; "P_fail"; "P_grown"; "P_keep"; "nd0"; "bdP"; "tv0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "tvL"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_am"; "nd_bd"; "nd_tv"; "ndesc"; "NDA"; "am_subst"; "AHead"; "nd_fr"; "am_eqb"; "nd_below"; "ND"; "fr_sub_eqb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fg.Lib_load_obj_epiCF_chk"; "Fx"; "ent_chkS"; "len_src"; "bd_land"; "comOf"; "ekOf"; "land_chk"; "nx"; "s_x"; "slot_src"; "nd_land"; "s_f0"; "s_f1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "sv_subst"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR"; "V_ldR"; "fact_nv"; "vNV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "xLD"; "xLK"; "alA"; "pNX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "wsub_id_on"; "bud_le2"; "V_below"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "bd_disp"; "K_disp"; "pc_disp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2"; "L_cf0"; "B_1"; "bdAt"; "ndAt"; "pc_cf"; "pc_vf0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs"; "V_ld"; "nd_d0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1"; "nd_succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_epiS2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fe.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiCF.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.

Definition Fx (A : axst) : list sprop := ss_facts (ax_S A).
Definition nx (A : axst) : positive := ss_next (ax_S A).

Definition ent_chkS (L T : axst) (s : wsub) (ndi ndj : ndesc) : bool := ltac2:(tb__ "0|2|
S2S2L_;M0S1fVL;VT;Vs;A3G0S92Vs;S65A2G0Sb7S65S8aVL;A1M1A2G0S7eG1Vndi;A2G0Sb2Vs;S77Vndi;A1S77Vndj;A1A3G0S80Vs;S7cVndi;A1S7cVndj;A1A3G0Sa4S83VL;A1S62Vs;S76Vndj;A1A2S76Vndi;A1A3S7dS7aVs;S75Vndj;A1A2S75Vndi;A1A2S6X2x2S6X2x2S6X2x2S6X2x2S6X2x2S6X2x2S6X2x2").
Lemma ent_chkS_unf : ltac2:(tb__ "0|2|
S1dS1dS95S78S78S0S2S84R5R4R3R2R1A5S3A3S1S0S2S1fR6R5R4A3S3A3S1S0S2S92R4S65A2S3A3S1S0S2Sb7S65S14S1eR6A1M0A1M1A2S3A3S1S0S2S7eG1R3A2S3A3S1S0S2Sb2R4S77R3A1S77R2A1A3S3A3S1S0S2S80R4S7cR3A1S7cR2A1A3S3A3S1S0S2Sa4S15G0A1S62R4S76R2A1A2S76R3A1A3S3A3S0S2S7dS7aR4S75R2A1A2S75R3A1A2S3A3A2A2A2A2A2A2A2F_;Fndj;Fndi;Fs;FT;FL;").
Proof.
  intros L T s ndi ndj H. unfold ent_chkS in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H]. apply lazy_andb_prop in H as [H4 H].
  apply lazy_andb_prop in H as [H5 H]. apply lazy_andb_prop in H as [H6 H]. apply lazy_andb_prop in H as [H7 H8]. repeat split; assumption.
Qed.

Lemma epiCF_checks_ent : ltac2:(tb__ "0|a|
S1S0S1dS96Sb8S4SfS55S15S1eSb8A1M0A1M1A3M2A2S34A3S1S0S2S5fSfS16S14G0A1A1G2A3S3A3S1S0S2S5eSfS10S58A1G1A3S3A3S1S0S2S5eSfS10S53A1S15S1eS34A1M3A1A3S3A3S1S0S2S1cS1eS2dA1M4A1S3A3S1S0SdS5ScS5S11S11A2M5A1M6ScSfA1M7A2M8A1Sc8G3G4A2SaG8S9G6G7S7G5S9S11S11S19P1a0A1S13Z0A1A4S8G5A1A3S8SfA1A4A2A3S1S0S82S14G4A1S14G3A1A3S1S0S1dS22S34G4A2S2dA3S1S0S2S20S2bA1S3A3S1S0S2S1fS2dS2bS33A3S3A3S1S0S2S92S33S65A2S3A3S0ScS5S81S90A2M9A1S3aS4eA1S7G9S9S81S90S5cS91A4S8G9A1A3A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiCF_checks_vr : ltac2:(tb__ "0|9|
S1S0SdS1dA1Sa2S40S5dS40A1A2SaS1dS2cA2A3S1S0S1dS96S2cS4SfS5aS15S1eS2cA1M0A1A3M1A2S24A3S1S0S2S5fSfS16S14G0A1A1G1A3S3A3S1S0SdScS1bA1M2A1Sb0S24S68S23A3SaG2S26A2A3S1S0S2SafS24S68S23S26Sc0S5S5S1dS78A2M3S1aS1aOF_;F_;M4A2M5S1dG5SeS1dS78SeG3G4R1A3A3Ld;S43A4A5S3A3S1S0S2ScaS65S23A2S3A3S1S0S2Sc9S23SbeA2S3A3S1S0S2Sb2S23S59S77Sa7S99S3S6cA3M6A1A3S3A3S1S0S2S7dS7aS23S75G6A1A2S7bS9dS3A2A2S3A3S1S0S2S5fS5Sb4G4A2M7G7Sb5S68SbeS23S14S1eS24A1A1M8SeSb4G4R1A3A5Ld;S43A3S3A3S1S0S2S98S73S3bA2S3A3S1S0S2S97S39S31A2S3A3S1S0S2Sb6S28S21S24A1A2S3A3S1S0ScS61A1S62S23S76G6A1A2S56A3S1S0S2S7eG8S29A2S3A3S1S0S2S63G8S25A2S3A3S1S0S2Sb7S65G8A2S3A3S0S2S64S31A1S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiCF_checks_vr_nd : ltac2:(tb__ "0|d|
S1S0S78S79S4S5S11S11A2M0S27Sb1SaeS23S68S6bS24A4M1S77Sa7S99S3S6cA3M2A1A2A3S72S4S61S62G1S76G2A1A2S25A3S7aG1S75G2A1A2A4S29A3S1S0S78S79S4G0S27Sb1SaeS23S68S6aS24A4M3S77Sa7S99S3S7fS6fS8S5S5S11S81A2S11A2A1M4S6dS71S70A2A3A3M5A1A2A3S72S4S61S62G3S76G5A1A2S25A3S7aG3S75G5A1A2A4S46A3S1S0S78S79S4G0S27Sb1SaeS23S68S69S24A4M6S77Sa7S99S3S7fS6eG4S8S61A1A3A3M7A1A2A3S72S4S61S62G6S76G7A1A2S25A3S7aG6S75G7A1A2A4S57A3S1S0S1dSb3S68S24S23S26S6bS28A6S38A3S1S0S1dSb3S68S24S23S26S6aS28A6S37A3S1S0S1dSb3S68S24S23S26S69S28A6S36A3S1S0SdS1dA1M8Sa2S38S3cS38A1A2SaS1dS3fA2A3S1S0G8Sa2S37S3cS37A1A2SaS1dS3eA2A3S1S0G8Sa2S36S3cS36A1A2SaS1dS3dA2A3S1S0S1dSadS3fA1S30A3S1S0S1dSadS3eA1S2eA3S1S0S1dSadS3dA1S44A3S1S0S1dS96S30S4SfS48S32A1S15S1eS30A1M9A1A3MaA2S45A3S1S0S1dS96S2eS4SfS48S4aA1S15S1eS2eA1MbA1A3McA2S2fA3S1S0S2S5fSfS16S14G9A1A1GaA3S3A3S1S0S2S5fSfS16S14GbA1A1GcA3S3A3S1S0S2S20S45A1S3A3S1S0S2S20S2fA1S3A3S1S0S2S20S44A1S3A3S1S0S2S1fS2fS41S2aA3S3A3S0S2S92S2aS65A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiCF_checks_run : ltac2:(tb__ "0|6|
S1S0ScS5S81S90A2M0A1M1S3aS50A1S7G0S9S81S90SbcS91A4S7G0S9S81S90SbdS91A4S8G0A1M2A3A3A3S1S0G1S3aS4fA1S7G0S9S81S90SacS91A4M3S7G0G3G2A3A3A3S1S0S2S1fS4bS2bS47A3S3A3S1S0S2S92S47S65A2S3A3S1S0S1dS96S35S4SfS7SfS52S8SfA1A3S15S1eS35A1M4A1A3M5A2S42A3S0S2S5fSfS16S14G4A1A1G5A3S3A3A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition len_src (F : list sprop) : bool := ltac2:(tb__ "0|0|
SbSbS5eSfS10S9bA1VF;A3S5eSfS10S12Sa1S17Sa8S67S13Z1A1A3A2A1VF;A3A2S5eSfS10S12S67S13Z4000000A1A2A1VF;A3A2").
Definition slot_src (k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|1|
SbSbSbSbS5eSfS10S12S51Vk;A2A1VF;A3S5eSfS10S12Vk;S13ZffffffffA1M0A2A1VF;A3A2S5eSfS10S12Sa9Z4Vk;A2G0A2A1VF;A3A2S5eSfS10S18S49S9cA2A1VF;A3A2S85VF;A1A2").

Definition ekOf (bd : list bitem) : list bitem := firstn 1 (skipn 1 bd).
Definition comOf (bd : list bitem) : list bitem := ltac2:(tb__ "0|0|
S4S61SbfS61U1Vbd;A3Sc1S61U2Vbd;A3A3").
Definition bd_land (bd : list bitem) : list bitem := ltac2:(tb__ "0|0|
S4S61SaaS87Vbd;A1A3").
Definition s_f0 : wsub := Eval vm_compute in infer_sub NP (ax_S Lf0) (ax_S K_disp).
Definition s_f1 : wsub := Eval vm_compute in infer_sub NP (ax_S Lf1) (ax_S K_disp).
Definition nd_land : ndesc := ltac2:(tb__ "0|0|
S79S73S72S86S25A1S7bS9dS6A2A4").
Definition land_chk (L : axst) (s : wsub) : bool := ltac2:(tb__ "0|2|
S2S2L_;M0Sa6S83VL;A1S13Z0M1A1G1S88S25A1SaaA5G0S84VL;SabVs;S8dSc6A5Sa3Sc5Vs;A2S6X2x2S6X2x2").

Lemma epiCF_chk_ent : ltac2:(tb__ "0|0|
S1S0S78Sc7S79S73S72S39S7bS9dS3A2A4A3S1S0S2S98S73S3bA2S3A3S1S0S2S97S39S31A2S3A3S1S0S2S84S2dS2bS33S29S29A5S3A3S0S2Sa3S9aS33A2S3A3A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiCF_chk_site : ltac2:(tb__ "0|5|
S1S0S2Sc2S83S24A1M0S27S72S74S26A5S3A3S1S0S2Sc4G0S27S72Sc3S28A5S3A3S1S0S2S5eSfS10S18S49S9cA2A1S83S2cA1M1A3S3A3S1S0S2S85G1A1S3A3S1S0S2S5eSfS10S12S32S13ZffffffffA1M2A2A1G0A3S3A3S1S0S2S5eSfS10S12S66S13Z7fffff7ff800A1A2A1G0A3S3A3S1S0S2S5eSfS10S12Sa9Z10S9fA2M3G2A2A1G0A3S3A3S1S0S2S5eSfS10S12S9fG2A2A1G0A3S3A3S1S0S2S5eSfS10S12S9eS13Z800000000000A1A2A1G0A3S3A3S1S0S2S5eSfS10S12S17Sa8S9eG3A3S19P1eA1M4A2A1G0A3S3A3S1S0S2S5eSfS10S12G4S13Z7fffff800000A1A2A1G0A3S3A3S1S0S2Sa5S8aS24A1S9aA2S3A3S1S0S11S93S23P11A2S32A3S1S0S11S93S23PfA2S54A3S1S0S11S93S23PcA2S17Sa8S66S13Z338A1A3A3S0S11S93S23PeA2Sa0A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma lines_in_kept_vr : ltac2:(tb__ "0|0|
S60S5S11S11A2S9S11S11S9eSa9Z10S9fA2A4S27A3").
Proof. vm_compute. repeat (first [left; reflexivity | right]). Qed.

Lemma epiCF_chk_cont : ltac2:(tb__ "0|1|
S1S0S2S8cS32S83S30A1A2S3A3S1S0S2S8cS4aS83S2eA1A2S3A3S1S0S2S84S2fS41S2aS46S29A5S3A3S1S0S2Sa3S9aS2aA2S3A3S0S11S94S2aS5bZ1A1M0A2G0A3A2A2A2A2").
Proof. conj_vmc. Qed.

Definition s_x : wsub := Eval vm_compute in infer_sub NP (ax_S L_xF) (ax_S B_1).
Lemma epiCF_chk_exit : ltac2:(tb__ "0|4|
S1S0S2S85S83S35A1M0A1S3A3S1S0S2S5eSfS10S9bA1G0A3S3A3S1S0S2S98S3bS73A2S3A3S1S0S2S97S31SbaU1M1A1M2A2S3A3S1S0S2S84S42Sb9S8bS79S73S72G2S7bS9dS3A2A4SbbG1A1A5S3A3S1S0S2Sa3S9aS8bA2S3A3S1S0S2S97S25S4S61S87S25A1M3S88S25A1A3A2S3A3S1S0S2S97S4S61G3SaaA3S86S25A1A2S3A3S1S0S2S89S4cS8eA2S3A3S0S2S89S4dS8fA2S3A3A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
End Lib_load_obj_epiCF_chk.

(* [comment removed for export] *)
Module Lib_load_obj_epiCF_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "prod"; "nil"; "app"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SPUle"; "SVar"; "SMd"; "SPUlt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efnode"; "ejcertAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiCF"; "nd_cf"; "nd_fail"; "vcf"; "C_cf"; "E_c0"; "K_w"; "L_x"; "Lf0"; "Lf1"; "T_fail"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fg.Lib_load_obj_epiCF_eqs"; "cutsCF"; "exitsCF"; "H_ecertCF_ok"; "keep_ecertCF_ok"; "@Corelib.Init.Logic"; "eq"; "@LinuxProcessSemantics.Riscv.Instr"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2"; "cps_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR"; "PhisS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA"; "hideN"; "hide_set"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_epiS2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fe.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiCF.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.

Definition cutsCF : list efnode := ltac2:(tb__ "0|6|
S1S3S3S3S8S9A2M0S2A2M1S3SaSbA2M2A2M3S0G1G2S0G0S2S0S8S9S17S14A4U0M4A4S0SaSbZ189M5S16Z3A1A4A4S1G3S0G1G2S0G0S2S0S8S9S19S14A4G4A4S0SaSbG5S16Z1A1A4A4S1G3S0G1G2S0G0S2S0S8S9S1dS15A4G4A4S0SaSbZ188ScZaA1A4A4S4G3A1A3A3A3").
Definition exitsCF : list efnode := ltac2:(tb__ "0|6|
S1S3S3S3S8S9A2M0S2A2M1S3SaSbA2M2A2M3S0G1G2S0G0S2S0S8S9S18S14A4U0M4A4S0SaSbZ189S16Z2A1A4A4S1G3S0G1G2S0G0S2S0S8S9S1aS14A4G4A4S0SaSbZ188ScZ5A1A4M5A4S1G3S0G1G2S0G0S2S0S8S9S1bS15A4G4A4G5A4S1G3S0G1G2S0G0S2S0S8S9S1cS15A4G4A4G5A4S4G3A1A3A3A3A3").

Definition keep_ecertCF_ok : list sprop := ltac2:(tb__ "0|3|
S1SdS11SfP2a8A1M0SfP191A1M1A2S1SdSeS10S25ScZ3A1G0A3SfP1a1A1M2A2S1SdSeG1ScZ10000000000A1A2S1SdSeSfP19fA1ScZ800000000000A1A2S1SdSeG2ScZffffffffA1A2S4SdA1A3A3A3A3A3").
Definition H_ecertCF_ok : list sprop := ltac2:(tb__ "0|0|
S2aS23S5S12S20S21A3A2").
Lemma ecertCF_ok : ltac2:(tb__ "0|1|
S24S6S13S26S1fS28U190S27S1fS1eS12S12S29S22A1M0S20A4S1eS12S12G0S21A4A8S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_epiCF_eqs.

(* [comment removed for export] *)
Module Lib_load_obj_epiCF_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "prod"; "list"; "nat"; "true"; "bool"; "Some"; "app"; "fst"; "option"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "TPA"; "frinA"; "tvinA"; "ANone"; "JA"; "amode"; "fbinA"; "ffinA"; "nd_am"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sprop"; "holds"; "SLit"; "sprop_eqb"; "SAlu"; "SMd"; "SPUlt"; "sobj"; "ss_facts"; "ss_next"; "SPUle"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "phiK"; "efnode"; "fnode"; "JAF"; "efdrop"; "enodeIAF"; "nodeIAF"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "mul"; "add"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR"; "PhisS"; "ldefR"; "vNV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "BXok_d"; "bxt"; "bd_wpos"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@Stdlib.Lists.List"; "In"; "existsb"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "ldef"; "P0_lo"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fg.Lib_load_obj_epiCF_pf.VRNP"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fg.Lib_load_obj_epiCF_eqs"; "cutsCF"; "exitsCF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1"; "nd_succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2"; "L_cf0"; "B_1"; "ndAt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiCF"; "vI"; "vcf"; "kept_vr"; "nd_cf"; "PDk_vr"; "E_c0"; "L_x"; "R_c"; "nd_fail"; "E_c"; "Nt"; "PD_vr"; "Wt"; "Xk_vr"; "cbI"; "cntI"; "nv_pos"; "nv_src"; "passed_vr"; "room_vr"; "s_c"; "slot_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "K_disp"; "szL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs"; "nd_d0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiCF.VRN"; "Pre_vr"; "nd0";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "tvd"; "tvz"; "FBx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fg.Lib_load_obj_epiCF_chk"; "len_src"; "land_chk"; "slot_src"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pdescA"; "robjs_okF"; "xrs_okF"; "FFx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "enodeA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA"; "SPfamETA"; "SPfamGTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "payA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_epiS2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fe.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fe.Lib_load_obj_epiCF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fg.Lib_load_obj_epiCF_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fg.Lib_load_obj_epiCF_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module VRNP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Lib_vec_reserveN_pf. End VRNP.

Lemma efmeas_z0 : ltac2:(tb__ "0|1|
ScS10S3SbS1dS2eSbS31S0S1S1ScS10A2M0S3A2S1SbS1eA2S0G0S3S0ScS10R5R4A4R3A4S0SbS1eR2S5cA4A4R1A2S3bR2S3dZ2Z40A2A2A3Frho;Fr;Fk;Fnd;FT;").
Proof. intros. unfold efmeasA. cbn [ef_rank ef_var fst snd]. unfold z0. change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)). rewrite uval_lit by lia. lia. Qed.
Lemma efmeas_lit : ltac2:(tb__ "0|2|
ScS10S3SbSbS1dS2fS39Z0R2A2S3aR2S3dZ2Z40A2M0A2A2S2eSbS31S0S1S1ScS10A2M1S3A2S1SbS1eA2S0G1S3S0ScS10R7R6A4R5A4S0SbS1eR4S21R3A1A4A4R2A2S3cS3bR4G0A2R3A2A3F_;Frho;Fc;Fr;Fk;Fnd;FT;").
Proof. intros T nd k r c rho Hc. unfold efmeasA. cbn [ef_rank ef_var fst snd]. change (bv_unsigned (eval rho (SLit c))) with (uval rho (SLit c)). rewrite uval_lit by lia. lia. Qed.
Lemma efmeas_vcf : ltac2:(tb__ "0|2|
ScS10S3SbSbS1dS2eSbS31S0S1S1ScS10A2M0S3A2S1SbS1eA2S0G0S3S0ScS10R6R5A4R4A4S0SbS1eR3S5fR2A1M1A4A4R1A2S3cS3bR3S3dZ2Z40A2A2S41R1G1A2A2A3Frho;Fc;Fr;Fk;Fnd;FT;").
Proof. reflexivity. Qed.

Lemma vcf_val : ltac2:(tb__ "0|0|
S1dSbS2fS39Z0R1A2S39R1Z3A2A2S2eSbS41R3S5fR2A1A2S3cS41R3S24S93S21Z4A1S23S92S40S5eA3A3A2R2A2A3F_;Fc;Frho;").
Proof.
  intros rho c Hc. unfold vcf.
  assert (E4 : uval rho (SLit 4) = 4) by (apply uval_lit; lia).
  assert (Ec : uval rho (SLit c) = c) by (apply uval_lit; lia).
  assert (HM : uval rho (SMd M_MUL (SLit 4) (SAlu ALU_SUB vNV vI)) <= 18446744073709551612).
  { unfold uval. rewrite U_mul. fold (uval rho (SLit 4)). rewrite E4. unfold M64v.
    change 18446744073709551616 with (4 * 4611686018427387904). rewrite Z.mul_mod_distr_l by lia.
    pose proof (Z.mod_pos_bound (bv_unsigned (eval rho (SAlu ALU_SUB vNV vI))) 4611686018427387904 ltac:(lia)). lia. }
  rewrite uval_add_small by (rewrite Ec; lia). rewrite Ec. reflexivity.
Qed.

Lemma meas_vcf_12 : ltac2:(tb__ "0|4|
S1dS1dS2eSbS41R1S24S93S21Z4A1S23S92S40S5eA3A3M0A2S41R2G0A2A3S2fS39Z0S3cS3bZ189S3dZ2M1Z40A2A2M2S41R2S5fZ1A1A2A2M3A2S3aG3S3cG2S41R3S5fG1A1A2A2A2A2F_;Frho';Frho;").
Proof.
  intros rho rho' EV. rewrite !vcf_val by lia. rewrite EV. pose proof (uval_range rho (SMd M_MUL (SLit 4) (SAlu ALU_SUB vNV vI))) as RV. lia.
Qed.

Lemma nv_pos_of_src : ltac2:(tb__ "0|0|
S1dS20R1S6fA2S20R2S6eA2F_;Frho;").
Proof.
  intros rho H. unfold nv_src in H. apply (proj1 (holds_bgeu _ _ _)) in H.
  change (bv_unsigned (eval rho (SLit 3))) with (uval rho (SLit 3)) in H. rewrite uval_lit in H by lia.
  change (bv_unsigned (eval rho (SMd M_MUL vNV (SLit 3)))) with (uval rho (SMd M_MUL vNV (SLit 3))) in H.
  unfold nv_pos. apply (proj2 (h_ult _ _ _)). rewrite uval_lit by lia. pose proof (uval_range rho vNV) as R.
  destruct (Z.eq_dec (uval rho vNV) 0) as [E|N]; [|lia].
  exfalso. rewrite uval_mul_small in H by (rewrite E; lia). rewrite E in H. lia.
Qed.

Lemma cf_vals : ltac2:(tb__ "0|4|
S1dS2S1fA1S4cS1fS20R2A1R1A3S2eS5S4bS1fS22S25S5eS40A2A1R2A3S4A3S2eS5S94R3A1S4A3S2fS3aS41R5S5eA2M0S41R5S40A2M1A2S2fS39G1Z4000001A2S2fS2eSbS41R5S6dA2S3bZ3M2G0A2M3A3S2fS2eSbS41R5S6aA2S3cG3G2A2A3S2fS2eSbS41R5S68A2S3cS3bG2G1A2Z2A2A3S2eSbS41R5S6cA2S3bZcG0A2A3A2A2A2A2A2F_;F_;F_;FF;Frho;").
Proof.
  intros rho F HF HI HL. unfold len_src in HL. apply andb_prop in HL as [HL H3]. apply andb_prop in HL as [H1 H2].
  pose proof (holds_mem _ _ _ HF HI) as FI. pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  unfold fact_nv in F1. rewrite h_ult in FI. rewrite h_ule in F1, F2, F3. rewrite uval_lit in F3 by lia.
  pose proof (uval_range rho vI) as RI. pose proof (uval_range rho vNV) as RN. pose proof (uval_range rho pNX) as RX. pose proof (uval_range rho vLEN) as RL.
  rewrite uval_add_small in F2 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F2 by lia.
  assert (Ec : uval rho cntI = 3 * uval rho vI) by (unfold cntI; apply uval_mul_lit; lia).
  assert (EW : uval rho Wt = 3 * uval rho vI + 3) by (unfold Wt; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  assert (E3N : uval rho (SMd M_MUL (SLit 3) vNV) = 3 * uval rho vNV) by (apply uval_mul_lit; lia).
  assert (EN : uval rho Nt = 3 * uval rho vNV + 2) by (unfold Nt; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  assert (Eb : uval rho cbI = 12 * uval rho vI) by (unfold cbI; rewrite uval_mul_comm; rewrite uval_mul_lit by lia; lia).
  repeat split; lia.
Qed.
Lemma room_holds : ltac2:(tb__ "0|0|
S1dS2S1fA1S4cS1fS20R2A1R1A3S2eS5S4bS1fS22S25S5eS40A2A1R2A3S4A3S2eS5S94R3A1S4A3S4cS1fS20R5A1S71A3F_;F_;F_;FF;Frho;").
Proof.
  intros rho F HF HI HL. destruct (cf_vals rho F HF HI HL) as (V1 & V2 & V3 & V4 & V5 & V6).
  assert (E4W : uval rho (SMd M_MUL (SLit 4) Wt) = 4 * uval rho Wt) by (apply uval_mul_lit; lia).
  assert (E4N : uval rho (SMd M_MUL (SLit 4) Nt) = 4 * uval rho Nt) by (apply uval_mul_lit; lia).
  unfold room_vr. constructor; [|constructor; [|constructor; [|constructor]]]; rewrite h_ule.
  - lia.
  - unfold VRN.B_EW. rewrite uval_lit by lia. lia.
  - lia.
Qed.
Lemma slot_holds : ltac2:(tb__ "0|0|
S1dS2S1fA1S1eS4cS1fS20R3A1R2A3S2eS5S96R2R3A2S4A3S4cS1fS20R5A1S73R3A1A3F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF H. unfold slot_src in H. apply andb_prop in H as [H HL]. apply andb_prop in H as [H HI]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct (cf_vals rho F HF HI HL) as (V1 & V2 & V3 & V4 & V5 & V6).
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  rewrite h_ule in F1, F2, F3. rewrite uval_lit in F2, F3 by lia. pose proof (uval_range rho k) as RK.
  assert (E4k : uval rho (kb 4 k) = 4 * uval rho k) by (unfold kb; apply uval_mul_lit; lia).
  unfold slot_facts. constructor; [|constructor; [|constructor; [|constructor]]]; rewrite h_ule.
  - rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
  - lia.
  - unfold VRN.B32. rewrite uval_lit by lia. lia.
Qed.

Lemma szL_val : ltac2:(tb__ "0|0|
S1dS2S1fA1S4cS1fS20R2A1R1A3S2eS5S4bS1fS22S29S97S21ZffffffffA1A2A1R2A3S4A3S2eSbS41R4S75A2S3bZ10S41R4S97A2A2A3F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF C. pose proof (holds_mem _ _ _ HF C) as H. rewrite h_ule, uval_lit in H by lia.
  pose proof (uval_range rho xLK) as R. unfold szL, kb. apply uval_mul_lit; lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S82S1dS2S2aQ40A1A1S5aOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sa0SfVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
SbS91VCST;R1A2S2fS39Z0R2A2S3aR2S9cA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
SbS91VXGL;R1A2S2fS39Z0R2A2S3aR2S9cA2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
SbSa1R1A1S91VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S1S1SbSbA2SbA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S1dOFr;") := ltac2:(tb__ "0|0|
S50VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S17VAInv;VCST;VXGL;S53VKc;Vrho0;VP0;VFB;VFF;VBX;S11Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S35VAInv;VCST;VXGL;S53VKc;Vrho0;VP0;VFB;VFF;VBX;S11VPhi;Vnd;Ad").

Lemma h0_ltNF : (h0 < NF)%positive. Proof. reflexivity. Qed.
Lemma HamC_vr : nd_am VRN.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_vr : ltac2:(tb__ "0|0|
S4cS98S98S2eS18S1bSaScS10R1A3A1S16A3Ld;S69A3"). Proof. repeat constructor. Qed.
Lemma P0_vr_mono : ltac2:(tb__ "0|2|
S2S1SbSbA2M0A1M1G1S2S1G0SbA2A1S1dG0S4aG0R1R5A3S4aG0R2R5A3F_;Fbn;S52R5R3R2A3S52R5R4R3A3F_;F_;Fr;FFFc;FF';FF;").
Proof. intros F F' FFc r _ H. exact H. Qed.

Lemma lo_robjsF0 : ltac2:(tb__ "0|0|
S82S1dS2S1fA1S2S1S1eS1eA2A1S2S26A1S1dS2S2aQ40A1A1S5aVAInv;R8R3R2R1A4S4cS1fS20R8A1R7A3VP0;Vrho0;A1S7bS53Vrho0;RaA3S13Vrho0;RcA2S8bRcS84S83RdA1A1A2S15VFB;ReRdRbA4S8cReRcA2S8dRfRdA2S14VFF;R11R10S4eA4S2eS5Sa2R10RfS4eS51ReA5S4A3S99VCST;Vrho0;VFB;VFF;R12R10S4eRfA8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv R rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CR.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ tv frL extraLO R rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CR).
  intros o a Ho HE Hr. exact (extraLO_pclMA CST rho0 FB FF rho tv frL o a Hav HP0 HE Hr).
Qed.
Lemma lo_xrsF0 : ltac2:(tb__ "0|1|
S82S1dS2S1fA1S2S1S1eS1eA2A1M0G0S1dS2S2aQ40A1A1S5aVAInv;R8R3R2R1A4S4cS1fS20R8A1R7A3VP0;Vrho0;A1S7bS53Vrho0;RaA3S13Vrho0;RcA2S8bRcS84S83RdA1A1A2S15VFB;ReRdRbA4S8cReRcA2S8dRfRdA2S14VFF;R11R10S4eA4S2eS5Sa4R10RfS4eSa3ReA5S4A3S9aVCST;VXGL;Vrho0;VFB;VFF;R12R10S4eRfA9F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HXlits.
  intros Ai rho facts tv X rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR CX.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ tv frL xextraLO X rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR CX).
  intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho tv frL r a Hav HP0 HE Ha).
Qed.
Lemma payA_same : ltac2:(tb__ "0|1|
S2S1fA1S2S45A1S2eS5S44R1A1S4A3SabS53Vrho0;VP0;R3S21Z0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof using .
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.

Lemma HIN_c : ltac2:(tb__ "0|1|
S1dS7aS82S1dS2S2aQ40A1A1S5aS4cS1fS20R6A1S27SdS67A1A1A3VP0;Vrho0;A1S7bS53Vrho0;R8A3VAInv;R7R6R5R4A4S13Vrho0;R8A2S8bRbS84S83R9A1A1A2S19VFB;RaA2S1aVFF;RbA2S15VFB;RcReS7S1S1eS1eA2S60S70A3M0A4S8cRfG0A2S8dR10G0A2S14VFF;RfR11S4eA4S2fS99VCST;Vrho0;VFB;VFF;R12S60S4eS65A8S2fS9aVCST;VXGL;Vrho0;VFB;VFF;R12S60S4eS6bA9S52S8eVFB;R12S60A3S9bVFF;R12S4eA3S78S77R12S65R11A3S72A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof using ALA HCST HXlits.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof epiCF_chk_site as (CR & CX & _ & _ & FkB & FvF & _ & _ & _ & _ & _ & _ & W17 & W15 & W12 & W14).
  assert (HNk : tvinA FB Ai rho kept_vr) by (apply (tvinA_sublist FB Ai rho (kept_vr ++ passed_vr)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_vr) by (exact (tvd_app_l rho kept_vr passed_vr HD)).
  assert (HZk : tvz rho kept_vr) by (apply (tvz_sublist rho (kept_vr ++ passed_vr)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - exact (lo_robjsF0 Ai rho _ kept_vr R_c rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CR).
  - exact (lo_xrsF0 Ai rho _ kept_vr Xk_vr rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CX).
  - unfold VRNP.P0_vr. rewrite !rw_call'. rewrite W17, W15, W12, W14.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    pose proof (holds_mem _ _ _ HF FvF) as HvF. rewrite h_ule, uval_lit in HvF by lia.
    pose proof (holds_mem _ _ _ HF FkB) as HkB. rewrite h_ule, uval_lit in HkB by lia.
    assert (E824 : uval rho (SAlu ALU_ADD vF (SLit 824)) = uval rho vF + 824) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; reflexivity).
    assert (EalA : uval rho alA = uval rho vF + 464) by (unfold alA; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; reflexivity).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split; [|split].
    + intros Hk. apply (tvz_in_kd rho (kept_vr ++ passed_vr) d_ac 4 k_ac HZ); [apply in_or_app; right; left; reflexivity | lia | unfold B32, Lib_vec_reserve.B32; lia | exact Hk].
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite E824. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
SbS2S2aQ40A1A1S46F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S2cScS1dS2S2aQ40A1A1S46S4cS1fS20R3A1S27SdR4A1A1A3VTR;S2bSfR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S46S46S46S49R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S46OS46S49R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S2cS2cScScS79S2S26A1M0S2S1ScS7eA2M1A1S2S1S1eS1eA2M2A1S46S1dS2S2aQ40A1A1M3G2S4aG2R1R5A3S4aG2R2SeRbA1A3F_;Fr;S2eS9G0A1S81RaR9R8A3S6G0R7A2A3S2eS5S80RbRaR9R8S4dG1ScS8ScS7eA2R7A4A5S4A3S1dG3VTR;S2bSfRfRdR2R1A5S7dSfS28SdRdA1A1R2R1RaA5A2Ftp1;Frho1;S2S5bA1M4S7aS5aS2dSfR9R8R10S0G4S85R3S86R2R1A2A4A5R13RaR9R4R2A4R13S78S77RbRfS5dR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;ScS7eG4S7aS5aS1dG3G4S7aS5aS4aG1S0ScS7eRaR9A4R14A3S2dSfR12R11R19S0G4S85R9S86R8R7A2A4A5R1cR13R12RaR8A4S7bS28SdR1aA1A1S78S77R14R18S5dR9R13RaA3A3R19A2R8A3S2dSfR9R8ReS0G4S85R7S86R6R5A2A4A5ReS78S77R16R1aS5dRbR15RcA3A3R1bA2R15RaR9R8R6A6S2fSa9R17S5dRcR16RdA3R1bR1cR1dR10R1eR19RbA9S1dS7cR18S5dRdR17ReA3R1cR1dSdR1eA1SdR1fA1SdR11A1R1RcA9VTR;S2bSfS7fR11S78S77R19R1dS5dReR18RfA3A3R1eA2R18RdRcA5SaaR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S2bSfR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S1dOF_;S10ScS1dS2S2aQ40A1A1S46R6R3A1VTR;S2bSfVJAv;R6A1R5R4R3A5R2A2F_;VTR;S2bSfVJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").

Hypothesis CVRN : ltac2:(tb__ "0|1|
S2S1SbSbA2M0A1S2S1G0SbA2A1S43S1dS2S2aQ40A1A1S42Z3R3A2VTR;S2bSfS12VAInv;VCST;VXGL;VKc;S52R6R5A2R6R5R4S11S8fS87S4S89A3AaS88R3R2A5S7dSfS8aR3R2S90VAInv;VCST;VXGL;VKc;S52S11S62R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis CUTC : ltac2:(tb__ "0|5|
ScS10S3S1SbS1eA2M0S1dS2S2aQ40A1A1M1SbG1S4aS1S1S1ScS10A2M2S3A2M3G0A2S0G3G0S0G2S3S0ScS10R8R7A4R6A4R5A4S54A3S32S3eR7R5A3S2fS39Z0S31S0G3G0S0G2S3S0ScS10RaR9A4R8A4R7A4R6A2M4A2S3aG4R4A2A2VTR;S2bSfVJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis CONT_B1 : ltac2:(tb__ "0|4|
S1dS2S2aQ40A1A1M0SbG0S3fR4A1S2fS39Z0S31S0S1S1ScS10A2M1S3A2S1SbS1eA2S0G1S3S0ScS10S58S59U1A1M2A4U0A4S0SbS1eZ187S21Z37aA1A4A4R5A2M3A2S3aG3R3A2A2VTR;S2bSfVJAv;G2A1S58R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;").
Hypothesis CONT_disp : ltac2:(tb__ "0|3|
S1dS2S2aQ40A1A1M0SbG0S4fR4A1S2fS39Z0S31S0S1S1ScS10A2M1S3A2S1SbS1eA2S0G1S3S0ScS10S74S76A4U0A4S0SbS1eZ186S5cA4A4R5A2M2A2S3aG2R3A2A2VTR;S2bSfVJAv;S76A1S74R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;").

Lemma X_E_c0 : ltac2:(tb__ "0|3|
S1dS2S2aQ40A1A1M0G0VTR;S2bSfVJAFv;S32S3eU0M1A2S61A2S63R3R2A5VFAM;S31S0S1S1ScS10A2M2S3A2S1SbS1eA2S0G2S3S0ScS10S63S61A4G1A4S0SbS1eZ189S5fZ2A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiCF_checks_vr as (Cxf & CEc & Cfb & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cpbd & Cxk & Chand & Cnb & Cbr & Cnp & Cwp).
  pose proof epiCF_chk_site as (CR & CX & FI & FL & FkB & FvF & F16 & FLK & FLD & FLDK & F30 & CVb & _).

  apply (TR_pre (SPA segs (JAv nd_cf) E_c rho tp)).
  { intros w Hw. rewrite <- CEc. apply (SPA_refacts_JA segs); [| exact Cfb |].
    - exact (SPA_axforms segs (JAv nd_cf) (xf_vr E_c0) rho E_c0 E_c1 tp w Cxf Hw).
    - intros tr md _ HF1. apply Forall_app. split; [|exact HF1]. exact (room_holds rho _ HF1 FI FL). }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD = 0 -> uval rho szL = 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv nd_cf] in HZ. intros E0.
    apply (proj1 (Forall_forall _ _) HZ (xLD, szL)); [unfold tv_vr; apply in_or_app; left; exact lines_in_kept_vr|].
    unfold tnz. cbn [fst]. intros H. exact (H E0). }
  intros Hnull.
  unfold nd_cf, tv_vr.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX VRNP.P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           VRN.Pre_vr (ndh h0 true VRN.nd0) PDk_vr NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRN eq_refl
           E_c s_c R_c Xk_vr rho tp kept_vr passed_vr frL bd_vr brest_vr (AHead pH true) (FAM (efmeasA (E_c0, nd_cf, 0%nat, (393, vcf 2)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand. exact (payA_same _ bd_vr Cwp).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho2 & tp2 & md2 & HM) HT HTK.
    exact (HIN_c rho ms Ai rho2 tp2 md2 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _.

    assert (HPHI' : ldefR rho').
    { apply (ldefR_keep rho rho'); [| | exact HPHI].
      - intros v Hv. apply (proj1 Hag). cbn [V_ldR In] in Hv. destruct Hv as [<-|[<-|[<-|[<-|[<-|[]]]]]]; reflexivity.
      - intros z Hz.
        pose proof (szL_val rho _ HF FLK) as ESZ.
        destruct (Z.eq_dec (uval rho xLD) 0) as [E0|Hnz]; [pose proof (Hnull E0); lia|].
        pose proof (holds_mem _ _ _ HF FLD) as H3. rewrite h_ule, uval_lit in H3 by lia.
        pose proof (holds_mem _ _ _ HF F16) as H1. rewrite h_ule, uval_lit in H1 by lia. fold szL in H1.
        pose proof (holds_mem _ _ _ HF FLDK) as H4. rewrite h_ule in H4. fold szL in H4.
        pose proof (holds_mem _ _ _ HF F30) as H6. rewrite h_ule, uval_lit in H6 by lia.
        rewrite (uval_add_small rho xLD szL) in H4 by lia.
        exact (keptK_lines CST FB FF rho0 rho kept_vr frL rho' HK lines_in_kept_vr Hnz ltac:(lia) ltac:(unfold B32, Lib_vec_reserve.B32; lia) z Hz). }

    assert (EV : uval rho' (SMd M_MUL (SLit 4) (SAlu ALU_SUB vNV vI)) = uval rho (SMd M_MUL (SLit 4) (SAlu ALU_SUB vNV vI))).
    { unfold uval. rewrite <- (eval_agree_vals (ss_next (ax_S E_c)) rho rho' (SMd M_MUL (SLit 4) (SAlu ALU_SUB vNV vI)) Hag eq_refl). reflexivity. }
    pose proof epiCF_checks_vr_nd as (Nk & Ng & Nf & Tk0 & Tg0 & Tf0 & Bk & Bg & Bf & Tik & Tig & Tif & Sk & Sg & Fbk & Fbg & _ & _ & _ & _ & _).
    pose proof epiCF_chk_cont as (Ssk & Ssg & Cgk & CidV & Csub).
    cbn [PDk_vr liftPD PDh PD_vr map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite Tk0, Nk.
      apply (TR_pre (SPA segs (JAv nd_cf) K_w rho' tp')).
      { intros w Hw. unfold K_w. rewrite <- Sk. apply (SPA_refacts_JA segs); [| exact Fbk |].
        - rewrite <- Tik. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_cf) (xfb_vr T_keep0) rho' T_keep0 B_keep tp' w Bk Hw).
        - intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. exact (slot_holds rho' _ k_ac HF2 Ssk). }
      apply (CUTC K_w nd_cf 0%nat (393, vcf 1) rho' tp'); [right; left; reflexivity | exact HPHI' |].
      rewrite !efmeas_vcf. exact (meas_vcf_12 rho rho' EV).
    +
      rewrite Tf0, Nf.
      apply (TR_pre (SPA segs (JAv nd_fail) T_fail rho' tp')).
      { intros w Hw. rewrite <- Tif. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_fail) (xfb_vr T_fail0) rho' T_fail0 B_fail tp' w Bf Hw). }
      apply (CUTC T_fail nd_fail 0%nat (392, SLit 10) rho' tp'); [right; right; left; reflexivity | exact HPHI' |].
      rewrite efmeas_vcf, efmeas_lit by lia. pose proof (uval_range rho (vcf 2)) as RV. lia.
    +
      rewrite Tg0, Ng.
      apply ent_chkS_unf in Cgk as (Ce & Cid & Cnp' & Cnb' & Ctv & Cfr & Cbd & Cam').
      apply (TR_pre (SPA segs (JAv nd_cf) K_w (rho_sub rho' s_gk) tp')).
      { intros w Hw.
        assert (HwS : SPA segs (JAv nd_grown) T_grownS rho' tp' w).
        { rewrite <- Sg. apply (SPA_refacts_JA segs); [| exact Fbg |].
          - rewrite <- Tig. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_grown) (xfb_vr T_grown0) rho' T_grown0 B_grown tp' w Bg Hw).
          - intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. exact (slot_holds rho' _ vKg HF2 Ssg). }
        exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc T_grownS K_w s_gk nd_grown nd_cf rho' tp' w Ce Cid Cnp' Cnb' Ctv Cfr Cbd Cam' HwS). }
      apply (CUTC K_w nd_cf 0%nat (393, vcf 1) (rho_sub rho' s_gk) tp'); [right; left; reflexivity | exact (phi_sub V_ldR ldefR ldefR_reads s_gk rho' CidV HPHI') |].
      rewrite !efmeas_vcf. unfold uval at 1. rewrite <- (eval_subst rho' s_gk (vcf 1)), Csub. fold (uval rho' (vcf 1)).
      exact (meas_vcf_12 rho rho' EV).
Qed.

Lemma X_L_x : ltac2:(tb__ "0|3|
S1dS2S2aQ40A1A1M0G0VTR;S2bSfVJAFv;S32S3eU0M1A2S61A2S64R3R2A5VFAM;S31S0S1S1ScS10A2M2S3A2S1SbS1eA2S0G2S3S0ScS10S64S61A4G1A4S0SbS1eZ188S21Z5A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiCF_checks_run as (_ & _ & _ & _ & CxF & Cfb).
  pose proof epiCF_chk_exit as (FL & _ & Cptv & Cpbd & Cx & CidV & _).
  apply ent_chkS_unf in Cx as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  apply (TR_pre (SPA segs (JAv (ndAt 1)) B_1 (rho_sub rho s_x) tp)).
  { intros w Hw.
    assert (HwF : SPA segs (JAv (NDA tvL frL (bdAt 1) (AHead pH true))) L_xF rho tp w).
    { rewrite <- CxF. apply (SPA_refacts_JA segs); [| exact Cfb |].
      - apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL frL bd_vr (bdAt 1) (AHead pH true) L_x rho tp w Cpbd).
        exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_vr tvL frL bd_vr (AHead pH true) L_x rho tp w Cptv Hw).
      - intros tr md _ HF1. apply Forall_app. split; [|exact HF1]. constructor; [|constructor].
        unfold len_src in FL. apply andb_prop in FL as [FL F3]. apply andb_prop in FL as [_ F2].
        exact (proj2 (rate2_bounds rho (ldefR_rate rho HPHI) (holds_mem _ _ _ HF1 F2) (holds_mem _ _ _ HF1 F3))). }
    exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L_xF B_1 s_x (NDA tvL frL (bdAt 1) (AHead pH true)) (ndAt 1) rho tp w
             Ce Cid Cnp Cnb Ctv Cfr Cbd Cam HwF). }
  apply (CONT_B1 (rho_sub rho s_x) tp); [exact (phi_sub V_ldR ldefR ldefR_reads s_x rho CidV HPHI) |].
  rewrite !efmeas_lit by lia. lia.
Qed.

Lemma X_Lf : ltac2:(tb__ "0|3|
ScS79S1dS2S2aQ40A1A1M0G0S2eS5S95R5R4A2S4A3VTR;S2bSfVJAFv;S32S3eU0M1A2S66A2R6R4R3A5VFAM;S31S0S1S1ScS10A2M2S3A2S1SbS1eA2S0G2S3S0ScS10R6S66A4G1A4S0SbS1eZ188S21Z5A1A4A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Fs;FL;").
Proof.
  intros L s rho tp tp0 CL. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  unfold land_chk in CL. apply lazy_andb_prop in CL as [Cpay CL]. apply lazy_andb_prop in CL as [Cx CidV].
  apply ent_chkS_unf in Cx as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  pose proof epiCF_chk_exit as (_ & _ & Cptv & _ & _ & _ & PP1 & PP2 & _).
  apply TR_facts. intros HF.
  apply (TR_pre (SPA segs (JAv nd_d0) K_disp (rho_sub rho s) tp)).
  { intros w Hw.
    apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L K_disp s nd_land nd_d0 rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam).
    unfold nd_land.
    apply (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL frL (AHead pH false) brest_vr (comOf brest_vr) (ekOf brest_vr) bd_disp (bd_land brest_vr) _ L rho tp w PP1 PP2 HF Cpay).
    apply (JA_pot_drop segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HBX).
    exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_vr tvL frL brest_vr (AHead pH true) L rho tp w Cptv Hw). }
  apply (CONT_disp (rho_sub rho s) tp); [exact (phi_sub V_ld ldef ldef_reads s rho CidV (ldefR_ldef rho HPHI)) |].
  rewrite efmeas_z0, efmeas_lit by lia. lia.
Qed.

Lemma exitsCF_ok : ltac2:(tb__ "0|4|
ScS10S3S1SbS1eA2M0S1dS2S2aQ40A1A1M1G1S4aS1S1S1ScS10A2M2S3A2M3G0A2S0G3G0S0G2S3S0ScS10R7R6A4R5A4R4A4S55A3VTR;S2bSfVJAFv;S32S3eR6A2R7A2R8R4R3A5VFAM;S31S0G3G0S0G2S3S0ScS10R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsCF In] in Hin.
  pose proof epiCF_chk_exit as (_ & _ & _ & _ & _ & _ & _ & _ & CL0 & CL1).
  destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <- <- <-.
  - apply X_E_c0.
  - apply X_L_x.
  - exact (X_Lf Lf0 s_f0 rho tp tp0 CL0).
  - exact (X_Lf Lf1 s_f1 rho tp tp0 CL1).
Qed.

Lemma X_L_cf0 : ltac2:(tb__ "0|3|
S1dS2S2aQ40A1A1M0G0VTR;S2bSfVJAFv;S32S3eU0M1A2S56A2S57R3R2A5VFAM;S31S0S1S1ScS10A2M2S3A2S1SbS1eA2S0G2S3S0ScS10S57S56A4G1A4S0SbS1eZ18aS5cA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI. change (ldefR rho) in HPHI.
  pose proof epiCF_checks_ent as (CE & Cfb & Fsrc & Fc0 & Zwf & Zsd & Znx & ZE & _).
  pose proof epiCF_chk_ent as (Nd & Cptv & Cpbd & Cx & CidV).
  apply ent_chkS_unf in Cx as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam).
  apply (TR_pre (SPA segs (JAv nd_cf) L_cfE rho tp)).
  { intros w Hw. rewrite Nd in Hw. rewrite <- CE. apply (SPA_refacts_JA segs); [| exact Cfb |].
    - unfold nd_cf. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_vr frL bd_cf bd_vr (AHead pH true) L_cf0 rho tp w Cpbd).
      exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL tv_vr frL bd_cf (AHead pH true) L_cf0 rho tp w Cptv Hw).
    - intros tr md _ HF1. apply Forall_app. split; [|exact HF1].
      constructor; [exact (ldefR_nv rho HPHI) | constructor; [exact (nv_pos_of_src rho (holds_mem _ _ _ HF1 Fsrc)) | constructor]]. }
  apply TR_facts. intros HFE.
  apply (TR_pre (SPA segs (JAv nd_cf) C_cf (rho_sub rho s_ent) tp)).
  { intros w Hw.
    apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc L_cfZ C_cf s_ent nd_cf nd_cf rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam).
    rewrite <- ZE. apply (SPA_restate segs (JAv nd_cf) rho L_cfE (ax_S L_cfZ) tp w _ _ Zwf Zsd Znx); [| constructor | exact Hw].
    constructor; [|constructor]. cbn [fst snd]. apply bv_eq. exact (proj1 (holds_nbne _ _ _) (holds_mem _ _ _ HFE Fc0)). }
  apply (CUTC C_cf nd_cf 0%nat (393, vcf 3) (rho_sub rho s_ent) tp); [left; reflexivity | exact (phi_sub V_ldR ldefR ldefR_reads s_ent rho CidV HPHI) |].
  rewrite efmeas_z0, efmeas_vcf. pose proof (uval_range (rho_sub rho s_ent) (vcf 3)) as RV. lia.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S1cSfVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S9eSfS9dVAInv;VCST;VXGL;A5").
Variable FAMQ : list word -> assn.

Hypothesis CONT_B1_T : ltac2:(tb__ "0|1|
S1dS2S2aQ40A1A1M0G0S3fR3A1S48SfVok;S2bSfVJAv;S59U1A1A1S58R4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Hypothesis CONT_disp_T : ltac2:(tb__ "0|1|
S1dS2S2aQ40A1A1M0G0S4fR3A1S48SfVok;S2bSfVJAv;S76A1S74R4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").

Lemma CVRN_T : ltac2:(tb__ "0|1|
S2S1SbSbA2M0A1S2S1G0SbA2A1S43S1dS2S2aQ40A1A1S42Z3R3A2S48SfVok;S2bSfS12VAInv;VCST;VXGL;VKc;S52R6R5A2R6R5R4S11S8fS87S4S89A3AaS88R3R2A5S7dSfS8aR3R2S90VAInv;VCST;VXGL;VKc;S52S11S62R6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof using ALA HCST HXGL HKc Hok AC.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vr.
  eapply (sum_PostsC_k segs AInv CST XGL Kc VRNP.P0_vr PTrue VRN.Pre_vr (ndh h0 true VRN.nd0) (PDh PD_vr h0 true) NF); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc VRNP.P0_vr PTrue VRN.Pre_vr VRN.nd0 PD_vr NF h0 true h0_ltNF HamC_vr HamPD_vr P0_vr_mono ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (VRNP.vec_reserveN_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.

Let famS (tp0 : list word) : Z -> list word -> assn := ltac2:(tb__ "0|0|
SbS2S2aQ40A1A1S49S30Sa8SfS4dS34Sa6S38VAInv;VCST;VXGL;S53VKc;Vrho0;VP0;VFB;VFF;VBX;S11S3eAcS4dS33S34S36S54A4A4R1A3VFAMQ;Vtp0;R1A2A2Lw;L_;L_;").
Lemma reenterS : ltac2:(tb__ "0|5|
S2S2aQ40A1A1M0ScS10S3S1SbS1eA2M1S1dG0SbG0S4aS1S1S1ScS10A2M2S3A2M3G1A2S0G3G1S0G2S3S0ScS10R8R7A4R6A4R5A4S54A3S32S3eR7R5A3S2fS39Z0S31S0G3G1S0G2S3S0ScS10RaR9A4R8A4R7A4R6A2M4A2S3aG4R4A2A2S48SfVok;S2bSfVJAv;RaA1RbR7R6A5VfamS;RcR5R4A3A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Ftp0;").
Proof.
  intros tp0 T nd k rv rho tp b tp0' Hin Hphi _.
  apply (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisS ok (map efdrop cutsCF) T nd k (FAMQ tp0) rho tp); [|exact Hphi].
  apply in_map_iff. exists (T, nd, k, rv). split; [reflexivity | exact Hin].
Qed.
Lemma rightS : ltac2:(tb__ "0|1|
S2S2aQ40A1A1M0S46SbG0S48SfVok;R3VFAMQ;R4A1A4S48SfVok;R4VfamS;R5R3R2A3A4F_;Ftp0';Fb;FP;Ftp0;").
Proof. intros tp0 P b tp0' H. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact H]. Qed.

Lemma CF_T : ltac2:(tb__ "0|4|
ScS10S3S1SbS1eA2M0S1dS2S2aQ40A1A1M1G1S4aS1S1S1ScS10A2M2S3A2M3G0A2S0G3G0S0G2S3S0ScS10R7R6A4R5A4R4A4S54A3S32S3eR6R4A3S48SfVok;S2bSfVJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertCF_ok 400%nat cps_b NP cutsCF exitsCF ok (FAMQ tp0) Hok
           ecertCF_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsCF_ok (triple segs ok) (famS tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CVRN_T (reenterS tp0)
           (fun rho tp b tp0' HL _ => rightS tp0 _ b tp0' (CONT_B1_T rho tp tp0 HL))
           (fun rho tp b tp0' HL _ => rightS tp0 _ b tp0' (CONT_disp_T rho tp tp0 HL)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.

Theorem epiCF_T : ltac2:(tb__ "0|1|
S1dS2S2aQ40A1A1M0G0S3fR3A1S48SfVok;S2bSfVJAv;S56A1S57R4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0 HL.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS 0%nat) ok nd_succ L_cf0 rho tp _ HL).
  exact (X_L_cf0 (triple segs ok) (fun _ tp0' => FAMQ tp0') (TRs_facts segs ok) (TRs_pre segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           (fun T nd k rv rho tp b tp0' Hi Hp _ => CF_T T nd k rv rho tp tp0' Hi Hp) rho tp tp0).
Qed.

Theorem epiCF_TF : ltac2:(tb__ "0|1|
S1dS2S2aQ40A1A1M0G0S48SfVok;S2bSfVJAFv;S32S3eU0A2S56A2S57R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS 0%nat) ok nd_succ L_cf0 rho tp). intros HL. exact (epiCF_T rho tp tp0 HL).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S9fSfS9dVAInv;VCST;VXGL;A5").
Variable FAM : ltac2:(tb__ "0|0|
SbS2S2aQ40A1A1S46F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
SbSbS2S2aQ40A1A1S49S39R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis CONT_B1_E : ltac2:(tb__ "0|3|
S1dS2S2aQ40A1A1M0G0S3fR3A1S47SfS2bSfVJAv;S59U1A1M1A1S58R4R3A5VFAM;S31S0S1S1ScS10A2M2S3A2S1SbS1eA2S0G2S3S0ScS10S58G1A4U0A4S0SbS1eZ187S21Z37aA1A4A4R4A2R2A2A3F_;Ftp0;Ftp;Frho;").
Hypothesis CONT_disp_E : ltac2:(tb__ "0|1|
S1dS2S2aQ40A1A1M0G0S4fR3A1S47SfS2bSfVJAv;S76A1S74R4R3A5VFAM;S3bZ186S3dZ2Z40A2A2R2A2A3F_;Ftp0;Ftp;Frho;").
Lemma disp_le : ltac2:(tb__ "0|3|
S1dSbS2fS39Z0S31S0S1S1ScS10A2M0S3A2S1SbS1eA2S0G0S3S0ScS10S74S76A4U0A4S0SbS1eZ186M1S5cA4A4R2A2M2A2S3aG2R1A2A2S39S3bG1S3dZ2Z40A2A2R2A2F_;Fb;Frho;").
Proof using . intros rho b H. rewrite efmeas_z0 in H. lia. Qed.

Lemma CVRN_E : ltac2:(tb__ "0|1|
S2S1SbSbA2M0A1S2S1G0SbA2A1S43S1dS2S2aQ40A1A1S42Z3R3A2S47SfS2bSfS12VAInv;VCST;VXGL;VKc;S52R6R5A2R6R5R4S11S8fS87S4S89A3AaS88R3R2A5S7dSfS8aR3R2S90VAInv;VCST;VXGL;VKc;S52S11S62R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof using ALA HCST HXGL HKc ACX.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vr.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc VRNP.P0_vr PTrue VRN.Pre_vr (ndh h0 true VRN.nd0) (PDh PD_vr h0 true) NF); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc VRNP.P0_vr PTrue VRN.Pre_vr VRN.nd0 PD_vr NF h0 true h0_ltNF HamC_vr HamPD_vr P0_vr_mono); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (VRNP.vec_reserveN_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.

Let famE (tp0 : list word) : Z -> list word -> assn := ltac2:(tb__ "0|0|
SbS2S2aQ40A1A1S49S30Sa7SfS4dS33Sa5S37VAInv;VCST;VXGL;S53VKc;Vrho0;VP0;VFB;VFF;VBX;S11S3eAcS54A4R3R1A4VFAM;R3Vtp0;R1A3A2Lw;L_;Lb;").
Lemma reenterE : ltac2:(tb__ "0|5|
S2S2aQ40A1A1M0ScS10S3S1SbS1eA2M1S1dG0SbG0S4aS1S1S1ScS10A2M2S3A2M3G1A2S0G3G1S0G2S3S0ScS10R8R7A4R6A4R5A4S54A3S32S3eR7R5A3S2fS39Z0S31S0G3G1S0G2S3S0ScS10RaR9A4R8A4R7A4R6A2M4A2S3aG4R4A2A2S47SfS2bSfVJAv;RaA1RbR7R6A5VfamE;RcR5R4A3A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Ftp0;").
Proof.
  intros tp0 T nd k rv rho tp b tp0' Hin Hphi Hm.
  exact (ereenter_cutJAF_b segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisS cutsCF T nd k rv (FAM b tp0) b rho tp Hin Hphi Hm).
Qed.
Lemma rightE : ltac2:(tb__ "0|1|
S2S2aQ40A1A1M0S46SbSbG0S39R3R2A2S47SfR5VFAM;R4R6A2A3S47SfR6VfamE;R7R4R3A3A3F_;F_;Ftp0';Fb;Fm;FP;Ftp0;").
Proof. intros tp0 P m b tp0' Hm H. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact (FAM_mono m b tp0 w Hm Hw) | exact H]. Qed.

Lemma CF_E : ltac2:(tb__ "0|4|
ScS10S3S1SbS1eA2M0S1dS2S2aQ40A1A1M1G1S4aS1S1S1ScS10A2M2S3A2M3G0A2S0G3G0S0G2S3S0ScS10R7R6A4R5A4R4A4S54A3S32S3eR6R4A3S47SfS2bSfVJAv;R8A1R9R5R4A5VFAM;S31S0G3G0S0G2S3S0ScS10R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisS PhisS_reads H_ecertCF_ok 400%nat cps_b NP cutsCF exitsCF (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertCF_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsCF_ok (etriple segs) (famE tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CVRN_E (reenterE tp0)
           (fun rho tp b tp0' HL Hm => rightE tp0 _ _ b tp0' (Z.lt_le_incl _ _ (proj2 Hm)) (CONT_B1_E rho tp tp0 HL))
           (fun rho tp b tp0' HL Hm => rightE tp0 _ _ b tp0' (disp_le rho b Hm) (CONT_disp_E rho tp tp0 HL)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.

Lemma cutE : ltac2:(tb__ "0|5|
ScS10S3S1SbS1eA2M0S1dS2S2aQ40A1A1M1SbG1S4aS1S1S1ScS10A2M2S3A2M3G0A2S0G3G0S0G2S3S0ScS10R8R7A4R6A4R5A4S54A3S32S3eR7R5A3S2fS39Z0S31S0G3G0S0G2S3S0ScS10RaR9A4R8A4R7A4R6A2M4A2S3aG4R4A2A2S47SfS2bSfVJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hi Hp Hm.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w (Z.lt_le_incl _ _ (proj2 Hm)) Hw) | exact (CF_E T nd k rv rho tp tp0' Hi Hp)].
Qed.

Theorem epiCF_E : ltac2:(tb__ "0|2|
S1dS2S2aQ40A1A1M0G0S3fR3A1S47SfS2bSfVJAv;S56A1S57R4R3A5VFAM;S31S0S1S1ScS10A2M1S3A2S1SbS1eA2S0G1S3S0ScS10S57S56A4U0A4S0SbS1eZ18aS5cA4A4R4A2R2A2A3F_;Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0 HL.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS 0%nat) nd_succ L_cf0 rho tp _ HL).
  exact (X_L_cf0 (etriple segs) FAM (TRe_facts segs) (TRe_pre segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           cutE rho tp tp0).
Qed.
Theorem epiCF_EF : ltac2:(tb__ "0|3|
S1dS2S2aQ40A1A1M0G0S47SfS2bSfVJAFv;S32S3eU0M1A2S56A2S57R3R2A5VFAM;S31S0S1S1ScS10A2M2S3A2S1SbS1eA2S0G2S3S0ScS10S57S56A4G1A4S0SbS1eZ18aS5cA4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisS 0%nat) nd_succ L_cf0 rho tp). intros HL. exact (epiCF_E rho tp tp0 HL).
Qed.
End Existence.
End Sum.

End Lib_load_obj_epiCF_pf.

(* [comment removed for export] *)
Module Lib_load_obj_epi_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "cons"; "prod"; "pair"; "nat"; "nil"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR"; "ldefR"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "pow"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_epiS2"; "B_1"; "ndAt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Corelib.Init.Logic"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface"; "al48_cells"; "memcpy48_contractA"; "memcpy48_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "K_disp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs"; "nd_d0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1"; "nd_s0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fg.Lib_load_obj_epi_pf.IF"; "P_err"; "P_ok"; "nd_lo_err"; "nd_lo_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits"; "K_after0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "ldef"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "JA"; "PTrue"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import BudA TobjJA TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f0.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module IF. Include Lib_load_obj_iface. End IF.
Module DP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_load_obj_epiD_pf. End DP.
Module DK. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f0.Lib_load_obj_epiS5_pf. End DK.
Module SP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fg.Lib_load_obj_epiS_pf. End SP.
Module CF. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fg.Lib_load_obj_epiCF_pf. End CF.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S38S9S2S8Q40A1A1S32OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S10S0VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S1S1cVCST;R1A2S1dS18Z0R2A2S19R2S30A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S1S1cVXGL;R1A2S1dS18Z0R2A2S19R2S30A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S1S35R1A1S1cVXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S4S4S1S1A2S1A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let P0 : ltac2:(tb__ "0|0|
S9OFr;") := ltac2:(tb__ "0|0|
S2aVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S2dVAInv;VCST;VXGL;S36VKc;Vrho0;VP0;VFB;VFF;VBX;S2eVnd;Ac").

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S2fS0VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
SeS0SdVAInv;VCST;VXGL;A5").
Hypothesis SSC : ltac2:(tb__ "0|0|
S1S31S1R1S3S1Z0S3S1Zf5S3S1Zf8S7S1A1A3A3A3A3S33S0SdVAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis MC48 : ltac2:(tb__ "0|0|
S1fS0SdVAInv;VCST;VXGL;S1eA6").
Variable FAMQ : list word -> assn.
Hypothesis XPK_T : ltac2:(tb__ "0|1|
S9S2S8Q40A1A1M0G0S12S0Vok;ScS0VJAv;S27A1S25R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XPE_T : ltac2:(tb__ "0|1|
S9S2S8Q40A1A1M0G0S12S0Vok;ScS0VJAv;S26A1S24R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Theorem epiDE_T : ltac2:(tb__ "0|1|
S9S2S8Q40A1A1M0G0S29R3A1S12S0Vok;ScS0VJAv;S22A1S21R4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Proof.
  exact (DK.epiDK_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC SSC MC48 FAMQ XPK_T XPE_T).
Qed.

Lemma epiB1_T : ltac2:(tb__ "0|1|
S9S2S8Q40A1A1M0G0S15R3A1S12S0Vok;ScS0VJAv;S1bU1A1A1S1aR4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Proof.
  exact (SP.epiS_B1_T AInv CST XGL ALA HCST HXGL HXlits Kc HKc FB FF BX HBX rho0 ok Hok AC FAMQ epiDE_T).
Qed.

Theorem epi_T : ltac2:(tb__ "0|1|
S9S2S8Q40A1A1M0G0S15R3A1S12S0Vok;ScS0VJAv;S23A1S28R4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Proof.
  exact (SP.epiS_T AInv CST XGL ALA HCST HXGL HXlits Kc HKc FB FF BX HBX rho0 ok Hok AC FAMQ epiDE_T
           (CF.epiCF_TF AInv CST XGL ALA HCST HXGL HXlits Kc HKc FB FF BX HBX rho0 ok Hok AC FAMQ epiB1_T epiDE_T)).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
SfS0SdVAInv;VCST;VXGL;A5").
Hypothesis SSCX : ltac2:(tb__ "0|0|
S1S31S1R1S3S1Z0S3S1Zf5S3S1Zf8S7S1A1A3A3A3A3S34S0SdVAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis MC48X : ltac2:(tb__ "0|0|
S20S0SdVAInv;VCST;VXGL;S1eA6").
Variable FAM : ltac2:(tb__ "0|0|
S1S2S8Q40A1A1S13F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S1S1S2S8Q40A1A1S14S18R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XPK_E : ltac2:(tb__ "0|1|
S9S2S8Q40A1A1M0G0S11S0ScS0VJAv;S27A1S25R3R2A5VFAM;S16Z158S17Z2Z40A2A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XPE_E : ltac2:(tb__ "0|1|
S9S2S8Q40A1A1M0G0S11S0ScS0VJAv;S26A1S24R3R2A5VFAM;S16Zd1S17Z2Z40A2A2R1A2A3Ftp0;Ftp;Frho;").

Theorem epiDE_E : ltac2:(tb__ "0|1|
S9S2S8Q40A1A1M0G0S29R3A1S11S0ScS0VJAv;S22A1S21R4R3A5VFAM;S16Z186S17Z2Z40A2A2R2A2A3F_;Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0 HL.
  rewrite <- (DP.efmeas_z0 K_disp nd_d0 0%nat 390 rho).
  exact (DK.epiDK_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ACX SSCX MC48X FAM FAM_mono XPK_E XPE_E rho tp tp0 HL).
Qed.

Lemma epiB1_E : ltac2:(tb__ "0|3|
S9S2S8Q40A1A1M0G0S15R3A1S11S0ScS0VJAv;S1bU1A1M1A1S1aR4R3A5VFAM;S37S5S4S4S2bS2cA2M2S6A2S4S1SaA2S5G2S6S5S2bS2cS1aG1A4U0A4S5S1SaZ187SbZ37aA1A4A4R4A2R2A2A3F_;Ftp0;Ftp;Frho;").
Proof.
  exact (SP.epiS_B1_E AInv CST XGL ALA HCST HXGL HXlits Kc HKc FB FF BX HBX rho0 ACX FAM FAM_mono epiDE_E).
Qed.

Theorem epi_E : ltac2:(tb__ "0|1|
S9S2S8Q40A1A1M0G0S15R3A1S11S0ScS0VJAv;S23A1S28R4R3A5VFAM;S16Z18fS17Z2Z40A2A2R2A2A3F_;Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0 HL.
  rewrite <- (DP.efmeas_z0 K_after0 nd_s0 0%nat 399 rho).
  exact (SP.epiS_E AInv CST XGL ALA HCST HXGL HXlits Kc HKc FB FF BX HBX rho0 ACX FAM FAM_mono epiDE_E
           (CF.epiCF_EF AInv CST XGL ALA HCST HXGL HXlits Kc HKc FB FF BX HBX rho0 ACX FAM FAM_mono epiB1_E epiDE_E) rho tp tp0 HL).
Qed.
End Existence.
End Sum.
End Lib_load_obj_epi_pf.

