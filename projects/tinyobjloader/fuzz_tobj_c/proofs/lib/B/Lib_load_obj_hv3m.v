(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "list"; "nil"; "andb"; "app"; "false"; "negb"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_base"; "axwf"; "entailsA"; "la_state"; "ax_X"; "ax_setS"; "g8"; "has_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "ss_pc"; "SLit"; "sv"; "SPUle"; "SVar"; "sobj"; "ss_facts"; "ss_objs"; "swf"; "SPEq"; "mkSS"; "sprop_below"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_regs"; "ss_resv"; "sstate"; "sv_eqb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3m"; "C_ck"; "E_o1"; "pc_cp"; "pc_cpx"; "L_cg"; "T_mck"; "X_cpk"; "cps_m"; "Lk0"; "Lk1"; "cp_chk"; "fo500"; "s_o1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "g5"; "NP"; "vF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "runL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop.LOLAddr"; "c_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv"; "cps_v"; "X_hv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.Bool.Bool"; "Is_true"; "@Stdlib.Lists.List"; "forallb"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3"; "T_grownS"; "T_keepS"; "tv_keep"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "extra_hv"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "xs_framed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_reopen_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "@Stdlib.PArith.BinPos.Pos"; "add"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "@stdpp.list_basics.list"; "list_filter"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_hv0 Lib_load_obj_hv Lib_load_obj_hvj Lib_load_obj_hvkit Lib_load_obj_hv3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition pc_cp : Z := 0x8df48.
Definition pc_cpx : Z := 0x8dfa4.
Definition cps_m : list Z := ltac2:(tb__ "0|0|
S0SbS30S0SbS31S40A3A3").
Definition L_ck : axst := Eval vm_compute in leafL (runL 600 cps_m T_keepS) pc_cp 0.
Definition L_cg : axst := Eval vm_compute in leafL (runL 600 cps_m T_grownS) pc_cp 0.
Definition C_ck : axst := Eval vm_compute in bl_cut L_ck 13 (SLit 12) [10; 11; 16; 17]%nat [].
Definition ck_var : sv := Eval vm_compute in SAlu ALU_SUB (SLit 94) (SVar (bl_vi L_ck)).
Definition X_cpk0 : axst := Eval vm_compute in bl_junk (leafL (runL 600 cps_m C_ck) pc_cpx 0) [10; 11; 16; 17]%nat.

Definition X_cpk : axst := Eval vm_compute in bl_prune (bl_vi L_ck) (bl_forget X_cpk0 [oidx d_av (SLit 0) X_cpk0; oidx vF (SLit 32) X_cpk0]).
Definition T_mck : axst := Eval vm_compute in shadow_reopen_stateA X_cpk X_hv g5 4 18.

Definition pure_posts_ok (Pre : axst) (Ls : list axst) : bool := ltac2:(tb__ "0|1|
S44SdSdS5S5S3S1eA1M0S1Lx;S4fSeVPre;A1SeR1A1A2S2S1eG0S7Ll;Ls;X3x2S50VPre;R1A2A2S2cS10R1A1S10VPre;A1A2A2LL;VLs;A3").

Definition cp_chk (tv : list (sv * sv)) (X : list (sv * sv)) (Xc T : axst) : Prop := ltac2:(tb__ "0|2|
SaS9S1bS10VXc;A1S1aS53A1A3SaS9S1S17S0S18S22S16S3bA1S3dA2S0S18S1cS1dS3bA1S1aS56S55Z2Z3dA2Z1A2A1A2S4S18A1A3A3S1fSeVXc;A1M0A1M1A2S2A3SaS9S1S51VX;S14VXc;A1A2S2A3SaS9SdS52VXc;VX;S3bZ4Z12A5VT;A3SaS9S1S21SeVT;A1A1S2A3SaS9S1S4cG1Vtv;S4dS4bS20G0A1A5S2A3S9S1S47G1A1S2A3A2A2A2A2A2A2").
Lemma hv3_checks_lp : ltac2:(tb__ "0|5|
SaS9S3S3SbA1M0A1S2dSdG0SdS2dSfSbSfS19SeS13R1A1A1A1LL;M1S3eU258M2S35R1A3A4LT;S0SdS49S0SdS48S4SdA1A3A3A4S0G0S0SbS30S4SbA1M3A3M4S0G0G4S4G0A1A3A3A3SaS9G0S2dSfSbG1S3eG2S35S2eA3A4S0SbS30S0SbS31S0SbS30S0SbS31G3A3A3A3A3A3SaS9S1S11S2eA1S2A3SaS9S1S11S34A1S2A3S9S1S12S32S2eS42S3cSeS32A1SeS2eA1A3A3S2A3A2A2A2A2").
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma hv3_checks_mk : ltac2:(tb__ "0|0|
S38S4aS41S34S33A4"). Proof. vm_compute. repeat split; reflexivity. Qed.

Definition Lk0 : axst := Eval vm_compute in leafL (runL 600 cps_v T_mck) c_op 0.
Definition Lk1 : axst := Eval vm_compute in leafL (runL 600 cps_v T_mck) c_op 1.

Definition fo500 (F : list sprop) : list sprop := ltac2:(tb__ "0|4|
S6S18S45S18S3S18A1M0S57S18A1M1S18S43S24P1f4R1A2M2A1Lp;S18S46G2A1Lx;VF;A6S45S18G0G1S18S43S8G2A1M3A1Lp;S18S46G3A1Lx;VF;A6A3").
Definition gen_o1 (L C : axst) : axst := ltac2:(tb__ "0|0|
SeVL;A1S2bS28R1A1ScS1dR1A1S1bS15VL;S23S19R3A1S4eS1bS29R3A1UfR1A4S26R3A1S25R3A1S2aR3A1S20R3A1S0S18S1cR1S1aZ1A1A2S39S1fSeVC;A1A1A1A3S54R2P1A2S27R3A1A9A2Tpw;Tn;TS;").
Definition E_o1 : axst := Eval vm_compute in gen_o1 Lk1 T_mck.
Definition s_o1 (L : axst) : wsub := ltac2:(tb__ "0|0|
S42S3cSeVL;A1SeS2fA1A3").
Lemma hv3_checks_o1 : ltac2:(tb__ "0|3|
SaS9S1S11S2fA1S2A3SaS9S1S21SeS2fA1M0A1S2A3SaS9SbS19G0A1S3fA3SaS9S3S3SbA1M1A1S2dSdG1SdS2dSfSbSfS19SeS13R1A1A1A1LL;S3eU258S40R1A3A4LT;S0SdS33S4SdA1M2A3A4S0G1S0SbS3fS0SbS3fS4SbA1A3A3S4G1A1A3A3S9S1S44SdSdS12R1S2fS3aR1A1A3LL;S0SdS36S0SdS37G2A3A3A3S2A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
