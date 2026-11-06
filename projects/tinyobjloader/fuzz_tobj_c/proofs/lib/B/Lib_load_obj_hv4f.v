(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "prod"; "app"; "option"; "pair"; "fst"; "length"; "list"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SPUle"; "sprop_eqb"; "SLit"; "SAlu"; "cell"; "sobj"; "ss_facts"; "ss_next"; "sv_eqb"; "SMd"; "c_off"; "c_val"; "c_width"; "mkCell"; "mkObj"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "sprop_below"; "ss_objs"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "@Stdlib.Lists.List"; "existsb"; "find"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3f"; "lx_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4f"; "X_lokR"; "Xs_v"; "Ys_v"; "lr_chk"; "X_l1R"; "X_l3R"; "bdX_v"; "comm_v"; "X_l1S"; "X_l1b"; "X_l1r"; "X_l3S"; "X_l3b"; "X_l3r"; "X_lokS"; "X_lokb"; "X_lokr"; "av_cell_new"; "av_cell_old"; "nv1"; "rate_nv1"; "s_l1"; "s_l3"; "s_lok"; "tvj_l1"; "tvj_l3"; "tvj_lok"; "upd_cellv"; "upd_objv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pPOS"; "pLNL"; "pNX"; "X_latch"; "pE0"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "LAX"; "LAXK"; "bdX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3"; "c_av"; "objs_nl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4"; "brest_o1"; "tv_op0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4e"; "X_l1"; "X_l3"; "X_lok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4p"; "bd_p1"; "brest_o3"; "tv_p0"; "tv_p1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sv_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_release_stateA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_opt_push1 Lib_opt_push3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_hv0 Lib_load_obj_hv Lib_load_obj_hvj Lib_load_obj_hvkit Lib_load_obj_hv3 Lib_load_obj_hv3m Lib_load_obj_hv3e Lib_load_obj_loopE Lib_load_obj_hv3f Lib_load_obj_hv4 Lib_load_obj_hv4w Lib_load_obj_hv4p Lib_load_obj_hv4e.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition av_cell_old : sv := ltac2:(tb__ "0|1|
S13S2fS19S30S5aS12Z3A1M0A3G0A3").
Definition nv1 : sv := SAlu ALU_ADD c_av (SLit 1).
Definition av_cell_new : sv := SMd M_MUL nv1 (SLit 3).
Definition upd_cellv (old new : sv) (c : cell) : cell := ltac2:(tb__ "0|0|
S2S14L_;S18S1bVc;A1Vold;A2S1dS1aVc;A1S1cVc;A1Vnew;A3Vc;X2x2").
Definition upd_objv (old new : sv) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S1eS1fVo;A1S23Vo;A1S22Vo;A1S2eS14S14S4dVold;Vnew;A2S20Vo;A1A4S21Vo;A1A5").
Definition restate_cells (old new : sv) (A : axst) : axst := ltac2:(tb__ "0|1|
S2cVA;S6bS2bVA;A1M0S2eS15S15S4eVold;Vnew;A2S25G0A1A4A2A2").
Definition rate_nv1 : sprop := ltac2:(tb__ "0|0|
S10S45S13S2fS53S12Z1A1A3A2").

Definition lr_chk (L R LR : axst) : Prop := ltac2:(tb__ "0|b|
S0S1S2S26S2bVR;A1M0A1S3A3S0S1S8S6ScS6SeSeA2M1A1M2ScSfA1M3A2M4A1S69S2bVL;A1M5G0A2SdG4S9G2G3S4G1S9SeSeS44S43A4S5G1A1A3S5SfA1M6A4A2A3S0S1S55S17G0A1M7S17G5A1A3S0S1S2dS2cVL;G0A2VR;A3S0S1S2dS6cVR;S7SfS4SfS46G6A3S16G0A1M8A3M9A2VLR;A3S0S1S2S2aSfS24G7A1G9A3S3A3S0S1S2S28SfS11S10S5aS51A2A1G8A3S3A3S0S1S2S28SfS11S10S51S4fA2A1G8A3S3A3S0S1S2S28SfS11S10S13S2fS4fS50A3S59A2A1G8A3S3A3S0S1S2S28SfS11S10S59S12Z4000000A1MaA2A1G8A3S3A3S0S1S2S28SfS11S10S4fGaA2A1G8A3S3A3S1S2S28SfS11S10S50GaA2A1G8A3S3A3A2A2A2A2A2A2A2A2A2A2A2").
Definition relr (L : axst) : axst := ltac2:(tb__ "0|0|
S6eVL;S5bVL;A1P6eS5S6S54S54A2A1A4").
Definition tvj_of (s : wsub) (tv : list (sv * sv)) : list (sv * sv) := ltac2:(tb__ "0|2|
S2eS6SeSeA2M0G0G0S8G0A1G0Lx;S29G0G0S18S6aVs;SaSeSeR1A3A2SaSeSeR2A3A2Ltj;S68A3G0R1Lx;S9SeSeS12Z0A1M1G1A4X8x2Lt;Vtv;A4").

Definition X_l1S : axst := Eval vm_compute in restate_cells av_cell_old av_cell_new X_l1.
Definition X_l1R : axst := Eval vm_compute in ax_add_facts [rate_nv1] X_l1S.
Definition X_l1r : axst := Eval vm_compute in relr X_l1R.
Definition X_l1b : axst := Eval vm_compute in optL' (apply_axforms X_l1r (xf_tail X_l1r)).
Definition s_l1 : wsub := Eval vm_compute in infer_sub NP (ax_S X_l1b) (ax_S X_latchE2).
Definition tvj_l1 : list (sv * sv) := Eval vm_compute in tvj_of s_l1 tv_op0.
Lemma hv4_checks_l1 : ltac2:(tb__ "0|1|
S0S35S61S3aS36A3S31S60S5fS4aS4S27S56Z0M0A1S4S27S57G0A1S5S27A1A3A3S5cS36S3cS3bS47A9A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition X_l3S : axst := Eval vm_compute in restate_cells av_cell_old av_cell_new X_l3.
Definition X_l3R : axst := Eval vm_compute in ax_add_facts [rate_nv1] X_l3S.
Definition X_l3r : axst := Eval vm_compute in relr X_l3R.
Definition X_l3b : axst := Eval vm_compute in optL' (apply_axforms X_l3r (xf_tail X_l3r)).
Definition s_l3 : wsub := Eval vm_compute in infer_sub NP (ax_S X_l3b) (ax_S X_latchE2).
Definition tvj_l3 : list (sv * sv) := Eval vm_compute in tvj_of s_l3 tv_p0.
Lemma hv4_checks_l3 : ltac2:(tb__ "0|1|
S0S35S62S3dS37A3S31S66S65S4bS4S27S56Z0M0A1S4S27S57G0A1S5S27A1A3A3S5cS37S3fS3eS48A9A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition X_lokS : axst := Eval vm_compute in restate_cells av_cell_old av_cell_new X_lok.
Definition X_lokR : axst := Eval vm_compute in ax_add_facts [rate_nv1] X_lokS.
Definition X_lokr : axst := Eval vm_compute in relr X_lokR.
Definition X_lokb : axst := Eval vm_compute in optL' (apply_axforms X_lokr (xf_tail X_lokr)).
Definition s_lok : wsub := Eval vm_compute in infer_sub NP (ax_S X_lokb) (ax_S X_latch).
Definition tvj_lok : list (sv * sv) := Eval vm_compute in tvj_of s_lok tv_p1.
Definition bdX_v : list bitem := Eval vm_compute in bd_subst s_lok (bdX 0).
Definition comm_v : list bitem := Eval vm_compute in bd_common bd_p1 bdX_v.
Definition Xs_v : list bitem := Eval vm_compute in bd_minus bd_p1 bdX_v.
Definition Ys_v : list bitem := Eval vm_compute in bd_minus bdX_v bd_p1.
Lemma hv4_checks_lok : ltac2:(tb__ "0|2|
S0S35S63S40S32A3S0S1S2S5dS64S7S27S39S33A3A2S3A3S0S1S2S5dS7S27S39S34A3S38A2S3A3S0S1S2S6dS16S2bS32A1A1S12Z0M0A1G0S33S34A5S3A3S0S1S2S5eSbS27S33A2U8M1A2S3A3S0S1S2S5eSbS27S34A2G1A2S3A3S31S67S38S4cS58G0A1S52S32S42S41S49A9A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
