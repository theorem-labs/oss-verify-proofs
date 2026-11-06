(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "nat"; "true"; "bool"; "cons"; "nil"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sprop"; "SPUle"; "sprop_eqb"; "ss_facts"; "eval"; "holds"; "SAlu"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "NDA"; "AHead"; "JA"; "ok_frameKA"; "@Corelib.Init.Logic"; "eq"; "and"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tblB"; "frL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.Lists.List"; "existsb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3"; "h0"; "nd_keep"; "c_av"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv_pf5.OP1P"; "P0_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv_pf5.OP3P"; "P0_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvpk"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "BXok_d"; "bxt"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_pure"; "J_pure_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "RL"; "VLA"; "ndA1"; "ndX0"; "ndXE"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "E_hv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3m"; "E_o1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "X_latch"; "pPOS"; "pLNL"; "pNX"; "pH"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface"; "white_hv"; "memcpyR_contractA"; "memcpyR_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4.OP1"; "Pre_op"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4"; "PDk_o1"; "X_1"; "T_op0r"; "T_op1r"; "tv_op0"; "tv_op1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4e"; "cutsH4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4p.OP3"; "Pre_op"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4p"; "PDk_o3"; "X_3"; "tv_p1"; "T_p0r"; "T_p1r"; "tv_p0";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4w"; "LR"; "PreR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "PhisH"; "mH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv4f"; "av_cell_new"; "av_cell_old"; "lr_chk"; "rate_nv1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_scan_double_ex OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_build_line_index_rom_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_reserve_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_opt_push1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_opt_push3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_hv0 Lib_load_obj_hv Lib_load_obj_hvj Lib_load_obj_hvkit Lib_load_obj_hvpk Lib_load_obj_hv2 Lib_load_obj_hv_pf1 Lib_load_obj_hv3 Lib_load_obj_hv3m Lib_load_obj_hv3e Lib_load_obj_loopE Lib_load_obj_hv3f Lib_load_obj_hv_pf3 Lib_load_obj_hv_pf4 Lib_load_obj_hv4 Lib_load_obj_hv4w Lib_load_obj_hv4p Lib_load_obj_hv4e Lib_load_obj_hv4f Lib_load_obj_hv_pf5 Lib_load_obj_hv1c Lib_load_obj_hv1e Lib_load_obj_hv_pf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ScanDoubleAddr DiagAppendAddr LOAddr LOLAddr HVAddr.

Ltac inl := cbn [In]; repeat (first [left; reflexivity | right]).
Lemma av_cell_eq : ltac2:(tb__ "0|0|
SaS1fS16Q40A1S10R1S77A2S10R1S76A2A3Frho;").
Proof.
  intros rho. unfold av_cell_old, av_cell_new, nv1. apply bv_eq. rewrite U_add, !U_mul, U_add, !U_lit.
  change (3 mod M64v) with 3. change (1 mod M64v) with 1.
  rewrite Zplus_mod_idemp_l. rewrite Zmult_mod_idemp_l. f_equal. lia.
Qed.
Lemma rate_nv1_holds : ltac2:(tb__ "0|1|
SaS1ScA1S1fS6S2bScSeSdS32S50A2A1R1A3S5A3S1fS6S2bScSeSdS50S4eA2A1R2A3S5A3S1fS6S2bScSeSdS12S73S4eS4fA3S5bA2A1R3A3S5A3S1fS6S2bScSeSdS5bS13Z4000000A1M0A2A1R4A3S5A3S1fS6S2bScSeSdS4eG0A2A1R5A3S5A3S1fS6S2bScSeSdS4fG0A2A1R6A3S5A3S72ScS11R8A1R7A3S11R9S79A2F_;F_;F_;F_;F_;F_;F_;FF;Frho;").
Proof.
  intros rho F M1 M2 M3 M4 M5 M6 HF.
  pose proof (holds_mem _ _ _ HF M1) as F1. pose proof (holds_mem _ _ _ HF M2) as F2. pose proof (holds_mem _ _ _ HF M3) as F3. pose proof (holds_mem _ _ _ HF M4) as F4.
  pose proof (holds_mem _ _ _ HF M5) as F5. pose proof (holds_mem _ _ _ HF M6) as F6.
  rewrite h_ule in F1, F2, F3, F4, F5, F6. rewrite uval_lit in F4, F5, F6 by lia.
  pose proof (uval_range rho pPOS) as RP. pose proof (uval_range rho pLNL) as RL. pose proof (uval_range rho c_av) as RC. pose proof (uval_range rho pNX) as RN.
  unfold rate_nv1, nv1, pE0. apply (proj2 (h_ule _ _ _)).
  rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia.
  rewrite uval_add_small by (rewrite uval_add_small, uval_lit by lia; lia). rewrite uval_add_small by lia. rewrite uval_lit by lia. lia.
Qed.
Lemma lines_in_tv_p1' : ltac2:(tb__ "0|0|
S2cS2SbSbA2S3SbSbS52S74Z10S53A2A4S69A3"). Proof. exact lines_in_tv_p1. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S55SaS1S16Q40A1A1S43OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S40S0VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S9S56VCST;R1A2S20S41Z0R2A2S42R2S71A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S9S56VXGL;R1A2S20S41Z0R2A2S42R2S71A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S9S75R1A1S56VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S1S2S2S9S9A2S9A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let P0 : ltac2:(tb__ "0|0|
SaOFr;") := ltac2:(tb__ "0|0|
S7aVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S1dVAInv;VCST;VXGL;S5aVKc;Vrho0;VP0;VFB;VFF;VBX;S19Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S2fVAInv;VCST;VXGL;S5aVKc;Vrho0;VP0;VFB;VFF;VBX;S19VPhi;Vnd;Ad").

Lemma CXR_op1 : ltac2:(tb__ "0|0|
S1fS6S35VXGL;SfS15S61A1A1S63Z4Z12S5fA6S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXR_op0 : ltac2:(tb__ "0|0|
S1fS6S35VXGL;SfS15S60A1A1S62Z4Z12S5fA6S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXR_p1 : ltac2:(tb__ "0|0|
S1fS6S35VXGL;SfS15S6bA1A1S69Z4Z12S68A6S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXR_p0 : ltac2:(tb__ "0|0|
S1fS6S35VXGL;SfS15S6aA1A1S6cZ4Z12S68A6S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S26S26S26S27R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").

Lemma site_lr : ltac2:(tb__ "0|1|
S1S2SbSbA2A1S1S38A1S14S14S14SaS1S16Q40A1A1S26S78R6R5R4A3VTR;S17S0VJAv;S1bR9S23R8S1cS51S5A2M0A4A1R5R4R3A5R2A2VTR;S17S0VJAv;S1bRaS23R9G0A4A1R8R5R4A5R3A2F_;F_;FQ;Ftp;Frho;FLR;FR;FL;Fbd;Ftv;").
Proof using TR_pre.
  intros tv bd L R LR rho tp Q (Rwf & Rsd & Rnx & RR & RLR & Rfb & M1 & M2 & M3 & M4 & M5 & M6) HK.
  apply (TR_pre (SPA segs (JAv (NDA tv frL bd (AHead pH true))) LR rho tp)); [|exact HK]. intros w Hw.
  rewrite <- RLR. apply (SPA_refacts_JA segs); [| exact Rfb |].
  - rewrite <- RR. apply (SPA_restate segs _ rho L (ax_S R) tp w _ _ Rwf Rsd Rnx); [| constructor | exact Hw].
    constructor; [|constructor]. cbn [fst snd]. apply av_cell_eq.
  - intros tr md _ HF1. apply Forall_app. split; [|exact HF1]. constructor; [|constructor]. exact (rate_nv1_holds rho _ M1 M2 M3 M4 M5 M6 HF1).
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S1eS0VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S3eS0S3bVAInv;VCST;VXGL;A5").
Hypothesis MCROM : ltac2:(tb__ "0|0|
S58S0S3bVAInv;VCST;VXGL;S57ZcA7").
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
SaS1S16Q40A1A1M0G0S25S0Vok;S17S0VJAFv;S22S48A2S4dR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|1|
SaS1S16Q40A1A1M0G0S25S0Vok;S17S0VJAFv;S22S49A2S54R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHOP1_T : ltac2:(tb__ "0|1|
S1S2S9S9A2M0A1S1S2G0S9A2A1S37SaS1S16Q40A1A1S36Z4R3A2S25S0Vok;S17S0S1aVAInv;VCST;VXGL;VKc;S33R6R5A2R6R5R4S19S39S30S5S5dA3AaS5cR3R2A5S28S0S2aR3R2S3aVAInv;VCST;VXGL;VKc;S33S19S5eR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof using ALA HCST HXGL HKc Hok AC.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_o1.
  eapply (sum_PostsC_k segs AInv CST XGL Kc OP1P.P0_op PTrue OP1.Pre_op (ndh h0 true OP1.nd0) (PDh OP1.PD_op h0 true) NF); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc OP1P.P0_op PTrue OP1.Pre_op OP1.nd0 OP1.PD_op NF h0 true h0_ltNF HamC_o1 HamPD_o1 P0_op_mono ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (OP1P.opt_push1_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.
Lemma CHOP3_T : ltac2:(tb__ "0|1|
S1S2S9S9A2M0A1S1S2G0S9A2A1S37SaS1S16Q40A1A1S36Z4R3A2S25S0Vok;S17S0S1aVAInv;VCST;VXGL;VKc;S34R6R5A2R6R5R4S19S39S30S5S66A3AaS65R3R2A5S28S0S2aR3R2S3aVAInv;VCST;VXGL;VKc;S34S19S67R6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof using ALA HCST HXGL HKc Hok AC.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_o3.
  eapply (sum_PostsC_k segs AInv CST XGL Kc OP3P.P0_op PTrue OP3.Pre_op (ndh h0 true OP3.nd0) (PDh OP3.PD_op h0 true) NF); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc OP3P.P0_op PTrue OP3.Pre_op OP3.nd0 OP3.PD_op NF h0 true h0_ltNF HamC_o3 HamPD_o3 P0_op3_mono ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (OP3P.opt_push3_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.
Lemma CMEMCPYR_T : ltac2:(tb__ "0|2|
S55SaS1S16Q40A1A1M0S25S0Vok;S17S0SaG0S1S44A1S43S20S3dVAInv;R7VKc;R4R3R2R1A7S21A2Lm;Lt;Lp;Lr;S6eR2R1A5S28S0S2aR2R1S7S2S14S29A2M1S3S14S29S6dS3cVAInv;VCST;VXGL;R3VKc;A5A4S8G1A1A3A5A4Ftp1;Frho1;FAi;").
Proof using HKc Hok MCROM.
  intros Ai rho1 tp1. eapply triple_conseq; [| intros w Hw; exact Hw |].
  2: { apply (MCROM ok Ai Kc rho1 tp1 HKc). eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K. }
  intros [tr [ms md]] [Hsm [HJ _]]. split; [exact Hsm | exact HJ].
Qed.

Lemma CUT4_T : ltac2:(tb__ "0|4|
S14S18S4S2S9SbA2M0SaS1S16Q40A1A1M1G1S2cS2S2S2S14S18A2M2S4A2M3G0A2S3G3G0S3G2S4S3S14S18R7R6A4R5A4R4A4S64A3S2eS6fR6R4A3S25S0Vok;S17S0VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0';Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX Hok AC MCROM XLATCH XLATCHE2.
  intros T nd k rv rho tp tp0' Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisH PhisH_reads 600%nat cps_v NP (map efdrop cutsH4) (map efdrop exitsH4) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisH _ _ _ _ _ ecertH4_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  set (QQ := fun w => SPfamGTA segs (map (nodeIAF AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH) (map efdrop cutsH4)) w \/ FAMQ tp0' w).
  assert (RE : forall Tc ndc rho' tp', In (Tc, ndc, 1%nat) (map efdrop cutsH4) -> tblB rho' -> triple segs ok (SPA segs (JAv ndc) Tc rho' tp') QQ).
  { intros Tc ndc rho' tp' Hi HP'. exact (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH ok (map efdrop cutsH4) Tc ndc 1%nat (FAMQ tp0') rho' tp' Hi HP'). }
  assert (WS : forall L Er Ec T0 Tb Tc, w_chk tv_op1 bd_op1 L Er Ec T0 Tb Tc -> In (Tc, nd_op1, 1%nat) (map efdrop cutsH4) -> tblB rho1 ->
               triple segs ok (SPA segs (JAv nd_op1) L rho1 tp1) QQ).
  { intros L Er Ec T0 Tb Tc Hchk Hi HP1. unfold nd_op1.
    apply (site_w AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok)
             (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok) CMEMCPYR_T tv_op1 bd_op1 L Er Ec T0 Tb Tc rho1 tp1 QQ Hchk lines_in_tv_op1 HP1).
    intros rho' tp' HP' _. exact (RE Tc nd_op1 rho' tp' Hi HP'). }
  assert (LE : forall tv bd tvj (L R LRs Lr Lb : axst) s, lr_chk L R LRs -> lx_chk tv bd tvj [LAX 0; LAXK 0] X_latchE2 LRs Lr Lb s -> In (xLD, kb 16 xLK) tv -> tblB rho1 ->
               triple segs ok (SPA segs (JAv (NDA tv frL bd (AHead pH true))) L rho1 tp1) QQ).
  { intros tv bd tvj L R LRs Lr Lb s Hlr Hlx Hlin HP1.
    apply (site_lr (triple segs ok) (TRs_pre segs ok) tv bd L R LRs rho1 tp1 QQ Hlr).
    apply (latch_rel AInv CST XGL ALA HCST HXGL LFSH Kc HKc FB FF BX HBX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok)
             tv bd tvj [LAX 0; LAXK 0] X_latchE2 LRs Lr Lb s rho1 tp1 QQ Hlx Hlin HP1).
    intros rho2 _ HP2.
    apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ok (NDA tvL frL [LAX 0; LAXK 0] (AHead pH true)) X_latchE2 (rho_sub rho2 s) tp1 _ HP2).
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCHE2 (rho_sub rho2 s) tp1 tp0')]. }
  cbn [exitsH4 In] in HinX. destruct HinX as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <- <- <-; cbn [efdrop fst snd];
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)); intros HP1.
  - exact (WS _ _ _ _ _ _ hv4_checks_w0 ltac:(cbn [map efdrop cutsH4 fst]; inl) HP1).
  - exact (WS _ _ _ _ _ _ hv4_checks_w1 ltac:(cbn [map efdrop cutsH4 fst]; inl) HP1).
  -
    apply (site_o3 AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok)
             (TRs_pureP segs ok) (call_soundPA3 segs ok) CHOP3_T rho1 tp1 QQ CXR_p1 CXR_p0 HP1).
    + intros rho' tp' HP' _. exact (RE T_p1 nd_p1 rho' tp' ltac:(cbn [map efdrop cutsH4 fst]; inl) HP').
    + intros rho' tp' HP' _. exact (RE T_p0 nd_p0 rho' tp' ltac:(cbn [map efdrop cutsH4 fst]; inl) HP').
  - destruct hv4_checks_l1 as [Hlr Hlx]. exact (LE tv_op0 brest_o1 tvj_l1 _ _ _ _ _ _ Hlr Hlx lines_in_tv_op0 HP1).
  - destruct hv4_checks_l3 as [Hlr Hlx]. exact (LE tv_p0 brest_o3 tvj_l3 _ _ _ _ _ _ Hlr Hlx lines_in_tv_p0 HP1).
  -
    destruct hv4_checks_lok as (Hlr & PP1 & PP2 & PPay & _ & _ & Hlx). unfold nd_p1.
    apply (site_lr (triple segs ok) (TRs_pre segs ok) tv_p1 bd_p1 X_lok X_lokS X_lokR rho1 tp1 QQ Hlr).
    apply (TRs_facts segs ok). intros HFo.
    apply (TRs_pre segs ok (SPA segs (JAv (NDA tv_p1 frL bdX_v (AHead pH true))) X_lokR rho1 tp1)).
    { intros w Hw. exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_p1 frL (AHead pH true) bd_p1 comm_v Xs_v Ys_v bdX_v _ X_lokR rho1 tp1 w PP1 PP2 HFo PPay Hw). }
    apply (latch_rel AInv CST XGL ALA HCST HXGL LFSH Kc HKc FB FF BX HBX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok)
             tv_p1 bdX_v tvj_lok (bdX 0) X_latch X_lokR X_lokr X_lokb s_lok rho1 tp1 QQ Hlx lines_in_tv_p1 HP1).
    intros rho2 _ HP2.
    apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ok (NDA tvL frL (bdX 0) (AHead pH true)) X_latch (rho_sub rho2 s_lok) tp1 _ HP2).
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH (rho_sub rho2 s_lok) tp1 tp0')].
Qed.

Theorem xko1_T : ltac2:(tb__ "0|1|
SaS1S16Q40A1A1M0G0S25S0Vok;S17S0VJAFv;S22S31A2S4cR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX Hok AC MCROM XLATCH XLATCHE2.
  intros rho tp tp0.
  apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB). intros HPHI.
  apply (site_o1 AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok)
           (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok) CHOP1_T rho tp _ CXR_op1 CXR_op0 HPHI).
  - intros rho' tp' HP' _. exact (CUT4_T T_op1 nd_op1 1%nat _ rho' tp' tp0 ltac:(cbn [cutsH4]; inl) HP').
  - intros rho' tp' HP' _. exact (CUT4_T T_op0 nd_op0 1%nat _ rho' tp' tp0 ltac:(cbn [cutsH4]; inl) HP').
Qed.

Theorem arm_v_T : ltac2:(tb__ "0|1|
SaS1S16Q40A1A1M0G0S25S0Vok;S17S0VJAFv;S22S47A2S4bR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX Hok AC MCROM XLATCH XLATCHE2.
  exact (arm_hv_T AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC FAMQ
           (kvr_T AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC FAMQ xko1_T XLATCHE2)).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S3fS0S3bVAInv;VCST;VXGL;A5").
Hypothesis MCROMX : ltac2:(tb__ "0|0|
S59S0S3bVAInv;VCST;VXGL;S57ZcA7").
Variable FAM : ltac2:(tb__ "0|0|
S9S1S16Q40A1A1S26F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S9S9S1S16Q40A1A1S27S41R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
SaS1S16Q40A1A1M0G0S24S0S17S0VJAFv;S22S48A2S4dR3R2A5VFAM;S2dS3S2S2S14S18A2M1S4A2S2S9SbA2S3G1S4S3S14S18S4dS48A4U1A4S3S9SbS45S46Z1S4aA2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|2|
SaS1S16Q40A1A1M0G0S24S0S17S0VJAFv;S22S49A2S54R3R2A5VFAM;S2dS3S2S2S14S18A2M1S4A2S2S9SbA2S3G1S4S3S14S18S54S49A4U1A4S3S9SbS45S46Z1S4aA2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHOP1_E : ltac2:(tb__ "0|1|
S1S2S9S9A2M0A1S1S2G0S9A2A1S37SaS1S16Q40A1A1S36Z4R3A2S24S0S17S0S1aVAInv;VCST;VXGL;VKc;S33R6R5A2R6R5R4S19S39S30S5S5dA3AaS5cR3R2A5S28S0S2aR3R2S3aVAInv;VCST;VXGL;VKc;S33S19S5eR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof using ALA HCST HXGL HKc ACX.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_o1.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc OP1P.P0_op PTrue OP1.Pre_op (ndh h0 true OP1.nd0) (PDh OP1.PD_op h0 true) NF); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc OP1P.P0_op PTrue OP1.Pre_op OP1.nd0 OP1.PD_op NF h0 true h0_ltNF HamC_o1 HamPD_o1 P0_op_mono); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (OP1P.opt_push1_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.
Lemma CHOP3_E : ltac2:(tb__ "0|1|
S1S2S9S9A2M0A1S1S2G0S9A2A1S37SaS1S16Q40A1A1S36Z4R3A2S24S0S17S0S1aVAInv;VCST;VXGL;VKc;S34R6R5A2R6R5R4S19S39S30S5S66A3AaS65R3R2A5S28S0S2aR3R2S3aVAInv;VCST;VXGL;VKc;S34S19S67R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof using ALA HCST HXGL HKc ACX.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_o3.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc OP3P.P0_op PTrue OP3.Pre_op (ndh h0 true OP3.nd0) (PDh OP3.PD_op h0 true) NF); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc OP3P.P0_op PTrue OP3.Pre_op OP3.nd0 OP3.PD_op NF h0 true h0_ltNF HamC_o3 HamPD_o3 P0_op3_mono); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (OP3P.opt_push3_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.
Lemma CMEMCPYR_E : ltac2:(tb__ "0|2|
S55SaS1S16Q40A1A1M0S24S0S17S0SaG0S1S44A1S43S20S3dVAInv;R7VKc;R4R3R2R1A7S21A2Lm;Lt;Lp;Lr;S6eR2R1A5S28S0S2aR2R1S7S2S14S29A2M1S3S14S29S6dS3cVAInv;VCST;VXGL;R3VKc;A5A4S8G1A1A3A5A3Ftp1;Frho1;FAi;").
Proof using HKc MCROMX.
  intros Ai rho1 tp1. eapply etriple_conseq; [| intros w Hw; exact Hw | exact (MCROMX Ai Kc rho1 tp1 HKc)].
  intros [tr [ms md]] [Hsm [HJ _]]. split; [exact Hsm | exact HJ].
Qed.

Lemma CUT4_E : ltac2:(tb__ "0|5|
S14S18S4S2S9SbA2M0SaS1S16Q40A1A1M1S9G1S2cS2S2S2S14S18A2M2S4A2M3G0A2S3G3G0S3G2S4S3S14S18R8R7A4R6A4R5A4S64A3S2eS6fR7R5A3S20S41Z0S2dS3G3G0S3G2S4S3S14S18RaR9A4R8A4R7A4R6A2M4A2S42G4R4A2A2S24S0S17S0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX ACX MCROMX FAM_mono XLATCH XLATCHE2.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisH PhisH_reads 600%nat cps_v NP cutsH4 exitsH4 (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertH4_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  destruct VB_460 as [I460 I467].
  set (EN := map (enodeIAF AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH) cutsH4).
  assert (WS : forall L Er Ec T0 Tb Tc, w_chk tv_op1 bd_op1 L Er Ec T0 Tb Tc -> In (Tc, nd_op1, 1%nat, mH 15 40) cutsH4 ->
               etriple segs (SPA segs (JAFv (phiK PhisH 1) nd_op1) L rho1 tp1)
                 (fun w => SPfamETA segs EN (efmeasA (L, nd_op1, 1%nat, mH 15 45) rho1) w \/ FAM (efmeasA (L, nd_op1, 1%nat, mH 15 45) rho1) tp0' w)).
  { intros L Er Ec T0 Tb Tc Hchk Hi.
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    apply (TRe_facts segs). intros HF0.
    pose proof Hchk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CL1 & CL2 & CL3).
    destruct (loopF_vals rho1 _ HF0 (conj CL1 (conj CL2 CL3))) as [HiC Hc26]. unfold nd_op1.
    apply (site_w AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs)
             (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs) CMEMCPYR_E tv_op1 bd_op1 L Er Ec T0 Tb Tc rho1 tp1 _ Hchk lines_in_tv_op1 HP1).
    intros rho' tp' HP' HVB.
    apply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH cutsH4 Tc nd_op1 1%nat (mH 15 40) _ _ rho' tp' Hi HP').
    apply (VLA_lt2 rho1 rho' 15 15 45 40 L Tc nd_op1 nd_op1 1%nat 1%nat); [exact (HVB _ I460) | exact (HVB _ I467) | exact HiC | exact Hc26 | lia | lia | lia | lia | right; lia]. }
  assert (LE : forall tv bd tvj (L R LRs Lr Lb : axst) s, lr_chk L R LRs -> lx_chk tv bd tvj [LAX 0; LAXK 0] X_latchE2 LRs Lr Lb s -> In (xLD, kb 16 xLK) tv ->
               etriple segs (SPA segs (JAFv (phiK PhisH 1) (NDA tv frL bd (AHead pH true))) L rho1 tp1)
                 (fun w => SPfamETA segs EN (efmeasA (L, NDA tv frL bd (AHead pH true), 1%nat, (RL, VLA 1 z0)) rho1) w
                           \/ FAM (efmeasA (L, NDA tv frL bd (AHead pH true), 1%nat, (RL, VLA 1 z0)) rho1) tp0' w)).
  { intros tv bd tvj L R LRs Lr Lb s Hlr Hlx Hlin.
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    pose proof Hlx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W460 & W467 & _).
    apply (site_lr (etriple segs) (TRe_pre segs) tv bd L R LRs rho1 tp1 _ Hlr).
    apply (latch_rel AInv CST XGL ALA HCST HXGL LFSH Kc HKc FB FF BX HBX rho0 (etriple segs) (TRe_facts segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs)
             tv bd tvj [LAX 0; LAXK 0] X_latchE2 LRs Lr Lb s rho1 tp1 _ Hlx Hlin HP1).
    intros rho2 HV2 HP2.
    apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB (NDA tvL frL [LAX 0; LAXK 0] (AHead pH true)) X_latchE2 (rho_sub rho2 s) tp1 _ HP2).
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    rewrite <- (efmeasA_VLA_agree X_latchE2 L ndXE (NDA tv frL bd (AHead pH true)) 1%nat 1%nat RL 1 rho1 rho2 (HV2 _ I460) (HV2 _ I467)).
    rewrite <- (efmeasA_VLA_sub X_latchE2 X_latchE2 ndXE ndXE 1%nat 1%nat RL 1 s rho2 W460 W467).
    exact (XLATCHE2 (rho_sub rho2 s) tp1 tp0'). }
  cbn [exitsH4 In] in HinX. destruct HinX as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <- <- <-.
  - exact (WS _ _ _ _ _ _ hv4_checks_w0 ltac:(cbn [cutsH4]; inl)).
  - exact (WS _ _ _ _ _ _ hv4_checks_w1 ltac:(cbn [cutsH4]; inl)).
  -
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    apply (TRe_facts segs). intros HF0.
    pose proof hv4_checks_o3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CL1 & CL2 & CL3).
    destruct (loopF_vals rho1 _ HF0 (conj CL1 (conj CL2 CL3))) as [HiC Hc26].
    assert (MM : forall rho' (Tc : axst) ndc, (forall v, In v V_B -> rw rho' v = rw rho1 v) ->
              0 <= efmeasA (Tc, ndc, 1%nat, mH 15 30) rho' < efmeasA (E_o3, nd_op1, 1%nat, mH 15 35) rho1).
    { intros rho' Tc ndc HV. apply (VLA_lt2 rho1 rho' 15 15 35 30 E_o3 Tc nd_op1 ndc 1%nat 1%nat); [exact (HV _ I460) | exact (HV _ I467) | exact HiC | exact Hc26 | lia | lia | lia | lia | right; lia]. }
    apply (site_o3 AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs)
             (TRe_pureP segs) (call_completePA3 segs) CHOP3_E rho1 tp1 _ CXR_p1 CXR_p0 HP1).
    + intros rho' tp' HP' HV. exact (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH cutsH4 T_p1 nd_p1 1%nat (mH 15 30) _ _ rho' tp' ltac:(cbn [cutsH4]; inl) HP' (MM rho' T_p1 nd_p1 HV)).
    + intros rho' tp' HP' HV. exact (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH cutsH4 T_p0 nd_p0 1%nat (mH 15 30) _ _ rho' tp' ltac:(cbn [cutsH4]; inl) HP' (MM rho' T_p0 nd_p0 HV)).
  - destruct hv4_checks_l1 as [Hlr Hlx]. exact (LE tv_op0 brest_o1 tvj_l1 _ _ _ _ _ _ Hlr Hlx lines_in_tv_op0).
  - destruct hv4_checks_l3 as [Hlr Hlx]. exact (LE tv_p0 brest_o3 tvj_l3 _ _ _ _ _ _ Hlr Hlx lines_in_tv_p0).
  -
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    destruct hv4_checks_lok as (Hlr & PP1 & PP2 & PPay & _ & _ & Hlx).
    pose proof Hlx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W460 & W467 & _). unfold nd_p1.
    apply (site_lr (etriple segs) (TRe_pre segs) tv_p1 bd_p1 X_lok X_lokS X_lokR rho1 tp1 _ Hlr).
    apply (TRe_facts segs). intros HFo.
    apply (TRe_pre segs (SPA segs (JAv (NDA tv_p1 frL bdX_v (AHead pH true))) X_lokR rho1 tp1)).
    { intros w Hw. exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_p1 frL (AHead pH true) bd_p1 comm_v Xs_v Ys_v bdX_v _ X_lokR rho1 tp1 w PP1 PP2 HFo PPay Hw). }
    apply (latch_rel AInv CST XGL ALA HCST HXGL LFSH Kc HKc FB FF BX HBX rho0 (etriple segs) (TRe_facts segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs)
             tv_p1 bdX_v tvj_lok (bdX 0) X_latch X_lokR X_lokr X_lokb s_lok rho1 tp1 _ Hlx lines_in_tv_p1 HP1).
    intros rho2 HV2 HP2.
    apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB (NDA tvL frL (bdX 0) (AHead pH true)) X_latch (rho_sub rho2 s_lok) tp1 _ HP2).
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    rewrite <- (efmeasA_VLA_agree X_latch X_lok ndX0 (NDA tv_p1 frL bd_p1 (AHead pH true)) 1%nat 1%nat RL 1 rho1 rho2 (HV2 _ I460) (HV2 _ I467)).
    rewrite <- (efmeasA_VLA_sub X_latch X_latch ndX0 ndX0 1%nat 1%nat RL 1 s_lok rho2 W460 W467).
    exact (XLATCH (rho_sub rho2 s_lok) tp1 tp0').
Qed.

Theorem xko1_E : ltac2:(tb__ "0|2|
SaS1S16Q40A1A1M0G0S24S0S17S0VJAFv;S22S31A2S4cR3R2A5VFAM;S2dS3S2S2S14S18A2M1S4A2S2S9SbA2S3G1S4S3S14S18S4cS31A4U1A4S70ZfZ3cA2A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX ACX MCROMX FAM_mono XLATCH XLATCHE2.
  intros rho tp tp0.
  apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB). intros HPHI.
  pose proof hv4_checks_rel as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL1 & CL2 & CL3).
  apply (TRe_facts segs). intros HF0. destruct (loopF_vals rho _ HF0 (conj CL1 (conj CL2 CL3))) as [HiC Hc26].
  destruct VB_460 as [I460 I467].
  assert (MM : forall rho' (Tc : axst) ndc, (forall v, In v V_B -> rw rho' v = rw rho v) ->
            0 <= efmeasA (Tc, ndc, 1%nat, mH 15 50) rho' < efmeasA (E_o1, nd_keep, 1%nat, mH 15 60) rho).
  { intros rho' Tc ndc HV. apply (VLA_lt2 rho rho' 15 15 60 50 E_o1 Tc nd_keep ndc 1%nat 1%nat); [exact (HV _ I460) | exact (HV _ I467) | exact HiC | exact Hc26 | lia | lia | lia | lia | right; lia]. }
  apply (site_o1 AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs)
           (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs) CHOP1_E rho tp _ CXR_op1 CXR_op0 HPHI).
  - intros rho' tp' HP' HV. exact (CUT4_E T_op1 nd_op1 1%nat (mH 15 50) rho' tp' _ tp0 ltac:(cbn [cutsH4]; inl) HP' (MM rho' T_op1 nd_op1 HV)).
  - intros rho' tp' HP' HV. exact (CUT4_E T_op0 nd_op0 1%nat (mH 15 50) rho' tp' _ tp0 ltac:(cbn [cutsH4]; inl) HP' (MM rho' T_op0 nd_op0 HV)).
Qed.

Theorem arm_v_E : ltac2:(tb__ "0|2|
SaS1S16Q40A1A1M0G0S24S0S17S0VJAFv;S22S47A2S4bR3R2A5VFAM;S2dS3S2S2S14S18A2M1S4A2S2S9SbA2S3G1S4S3S14S18S4bS47A4U1A4S3S9SbS45S46Z11S4aA2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX ACX MCROMX FAM_mono XLATCH XLATCHE2.
  exact (arm_hv_E AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 ACX FAM FAM_mono
           (kvr_E AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 ACX FAM FAM_mono xko1_E XLATCHE2)).
Qed.
End Existence.
End Sum.
