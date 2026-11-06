(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en f2.

(* [comment removed for export] *)
Module Lib_handle_f_iface.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "prod"; "cons"; "nil"; "pair"; "nat"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_handle_f_iface"; "P0_hf"; "PD_hf"; "Posts_hfJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "PTrue"; "ndesc"; "JA_pre"; "JLA"; "ANone"; "amode"; "nd_am"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "KcA"; "Kc_ok"; "alloc_lawsA"; "alloc_contractsA"; "alloc_contractsA_ex"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bxt"; "BXok_d"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf"; "P0_builder"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "Pre_hf"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi"; "P_fail"; "P_ok"; "nd_fail"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "ccount"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "law_flag_stmt"; "law_fshadow_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "PostsC"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3 SymSoundW.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition P0_hf (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|3|
S10S28VCST;VFB;VFF;Vr;A4S10SfS6S30Z3S38S2S2S0S0A2M0S0A2G0S7G0S0A2VFF;A4M1A2U0M2A3SfS6S30Z6G1A2G2A3A2A2").
Lemma P0_hf_b : ltac2:(tb__ "0|2|
S1S2S0S0A2M0A1M1G1S1S2G0S0A2A1SeSbR4R3R2R1A4S28R5R4R3R2A4F_;Fr;FFF;FFB;FCST;").
Proof. intros CST FB FF r [H _]. exact H. Qed.

Lemma P0_hf_mono : ltac2:(tb__ "0|2|
S1S2S0S0A2M0A1M1G1G1S1S2G0S0A2A1SeG0S1fG0R1R5A3S1fG0R2R5A3F_;Fbn;SbR6R5R3R2A4SbR7R5R4R3A4F_;F_;Fr;FFFc;FF';FF;FCST;").
Proof.
  intros CST F F' FFc r HS ((A & B & C) & E). split; [|exact E]. split; [|split; [exact B | exact C]].
  intros a Ha. destruct (A a Ha) as [H|[H|[(b & n & Hb & Hr)|(f & s & fl & Hf & Hr)]]]; [left; exact H | right; left; exact H | |].
  - right; right; left. exists b, n. split; [apply HS; exact Hb | exact Hr].
  - right; right; right. exists f, s, fl. split; [exact Hf | exact Hr].
Qed.

Definition PD_hf : list (axst * ndesc) := Posts_hf.
Lemma PD_hf_eq : ltac2:(tb__ "0|1|
SfS1S2SaS12A2M0A1ScS3G0S5SaS12S2bS2dA4S3G0S5SaS12S2cS2eA4S4G0A1A3A3A3"). Proof. reflexivity. Qed.
Lemma HamC_hf : nd_am nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_hf : ltac2:(tb__ "0|1|
S37S2SaS12A2M0G0SfS16S17S8SaS12R1A3A1S15A3Ld;ScA3"). Proof. repeat constructor. Qed.
Lemma HfrC_hf : nd_fr nd0 = []. Proof. reflexivity. Qed.

Definition Posts_hfJ (AInv : AA -> valuation -> list word -> Model -> Prop) (CST XGL : list (Z * Z)) (Kc : KcA)
    (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (BX : bxt) : list (axst * jpostA) := ltac2:(tb__ "0|0|
S3eVAInv;VCST;VXGL;VKc;SbVCST;A1S11ScVFB;VFF;VBX;Aa").
Lemma Posts_hfJ_eq : ltac2:(tb__ "0|4|
S25SeS1S26Q40A1A1S20OF_;F_;F_;F_;S1S2S0S0A2M0A1M1G1S1aG1S1S2G0S0A2A1S23SfS1S2SaS21A2M2A1SdR7R6R5R4R3R2R1A7S3G2S5SaS21S2bS14R7R6R5R4SbR6R3R2A3M3R3R2R1S11S2dAaA4S3G2S5SaS21S2cS14R7R6R5R4G3R3R2R1S11S2eAaA4S4G2A1A3A3A3FBX;FFF;FFB;FKc;FXGL;FCST;FAInv;").
Proof. reflexivity. Qed.

Definition handle_f_stmt : Prop := ltac2:(tb__ "0|5|
S25SeS1S26Q40A1A1M0S20OF_;F_;F_;F_;S1S2S0S0A2M1A1M2G2S1cS9R3R2A3S0S34R4R1A2S10S35Z0M3R2A2S36R2S33A2A2F_;Fa;M4G4S31R6A1S32R7A1S1aS1bR1A1G2S1S2G1S0A2A1S23S24Z6R1A2SeS3dOF_;S18S9R8R1A3S1dS9S19R11R10RfA5S0S1fS0R1S3S0G3S3S0Zf5S3S0Zf8S4S0A1A3A3A3A3S39S9S19R14R13R12R2A6F_;Fxx;G0S3cS9R5S2fS9S13R14R13R12RcSbR13RaR9A3RaR9R8S11S2aAaS29R6R1A5S22S9S27R6R1SdR14R13R12RcRaR9R8A7A5A4Ftp0;FSSC;FAC;FHok;Fok;Frho0;FHBX;FBX;FFF;FFB;FHKc;FKc;FLFSH;FLFLAG;FHXGL;FHCST;FALA;FXGL;FCST;FAInv;").

Definition handle_f_stmt_ex : Prop := ltac2:(tb__ "0|5|
S25SeS1S26Q40A1A1M0S20OF_;F_;F_;F_;S1S2S0S0A2M1A1M2G2S1cS9R3R2A3S0S34R4R1A2S10S35Z0M3R2A2S36R2S33A2A2F_;Fa;M4G4S31R6A1S32R7A1S1aS1bR1A1G2S1S2G1S0A2A1S23S24Z6R1A2SeS1eS9S19RfReRdA5S0S1fS0R1S3S0G3S3S0Zf5S3S0Zf8S4S0A1A3A3A3A3S3aS9S19R12R11R10R2A6F_;Fxx;G0S3bS9S2fS9S13R12R11R10RaSbR11R8R7A3R8R7R6S11S2aAaS29R4R1A5S22S9S27R4R1SdR12R11R10RaR8R7R6A7A5A3Ftp0;FSSCX;FACX;Frho0;FHBX;FBX;FFF;FFB;FHKc;FKc;FLFSH;FLFLAG;FHXGL;FHCST;FALA;FXGL;FCST;FAInv;").
End Lib_handle_f_iface.

(* [comment removed for export] *)
Module Lib_load_obj_lglue.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "batom"; "ASv"; "bd_subst"; "bitem"; "BI"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "list"; "prod"; "nil"; "pair"; "app"; "false"; "Some"; "option"; "fst"; "None"; "length"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "valuation"; "SLit"; "SVar"; "ss_facts"; "SPUle"; "SAlu"; "sv_eqb"; "holds"; "sobj"; "rm"; "sprop_below"; "ss_next"; "ob_base"; "rw"; "swf"; "ob_hi"; "ob_lo"; "obj_range"; "sprop_eqb"; "ss_objs"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "of_nat"; "opp"; "sub"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pI"; "X_bodyN"; "xLD"; "xLK"; "xLC"; "pNX"; "X_latch"; "entA"; "pLNL"; "pPOS"; "pT0"; "rate_factsLo"; "vsP"; "HNEXT"; "K_body"; "K_loop"; "O_ent"; "pE"; "pQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "vLEN"; "NP"; "vBUF"; "vCFGp"; "vF"; "vFL"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "tvL"; "s_body"; "s_loop"; "rateX600"; "X_bodyNc"; "X_latchA"; "frL"; "tblL"; "A1"; "Xl_objs"; "ent_facts600"; "extraLO"; "jL"; "rate_small"; "tblB"; "P0_lo"; "ldef"; "tblL0"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "X_dp"; "K_dpB"; "K_dpt"; "dpB_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Stdlib.Lists.List"; "forallb"; "In"; "nth_error"; "existsb"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "ndesc"; "NDA"; "am_eqb"; "am_subst"; "amode"; "JA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pclMA"; "FFx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena"; "rd64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "FBx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA"; "pinA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_le2"; "carve_ent_stateA"; "carve_site_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs"; "decodes"; "lines_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "prove_sprop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "state_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "is_shadowZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR";
"carve_stateA"; "drop_lastA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymSoundW
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.

Definition frL : list (sv * Z * sv) := ltac2:(tb__ "0|2|
SdS11S11S1dS0A2M0S1dA2M1S13G0S1dS13S1dS0S55Z5A4S56A4S12G1A1A3").

Definition tvL : list (sv * sv) := tv_k (kL vsP).
Definition jL : nat := 18%nat.

Definition P0_lo (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|4|
S2S0S2S32S7Vr;S53A2M0R1A2S34R1S33G0S7Vr;S51A2A2A2A2S7fVCST;Vr;VFB;VFF;R2A5M1F_;Fa;S2S0S2S32S7Vr;S54A2M2R1A2S34R1S33G2Z90A2A2A2G1F_;Fa;S0S2S32S39S7Vr;S20P1cA1A2M3Z10A2R1A2S34R1G3A2A2G1F_;Fa;A2A2").

Definition extraLO (o : sobj) : bool := ltac2:(tb__ "0|6|
SeSeL_;M0G0S24S2aVo;A1M1S53A2G0S24S2eVo;A1M2S1fZ0A1M3A2M4S24S2dVo;A1M5S51A2S15Xex2S15Xex2SfG0G0S24G1S54A2G0G4S24G5S1fZ90A1A2S15Xex2S15Xex2SfG0S24G1S20P1cA1A2G0S24G2S1fN10A1A2S24G5G3A2S15Xex2S15Xex2Xex2Xex2").

Definition tblL0 (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S4S10S11S0S0A2M0A1M1G1S2S8eS27Vrho;A1S7Vrho;S3dA2R1A3S2S8fR1S7Vrho;S51A2A2S2S3S0S37S1aG0R1A2A1S7Vrho;S3fA2A3G0S3S17G0A1S73G0R2S3aS7Vrho;S3bA2A1A3S16G0R1A2A3S32S7Vrho;S40A2S18S0S0R2A3A2F_;Fp;A2A2A2LT;A2").
Definition ldef (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S0S2S32S7Vrho;S3dA2M0R1A2S34R1S33G0S35Z10S7Vrho;S3eA2A2A2A2A2S6S3S17S75Q8A1M1A1S27Vrho;S76Q40R2A2A2S19G1A1A3A1F_;Fz;").
Definition tblL (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S2S6aVrho;A1S69Vrho;A1A2").
Definition V_L : list positive := ltac2:(tb__ "0|0|
SdS1P1d2SdS1PeSdS1P1d3SdS1P1ccSdS1P1eaSdS1P1d4S12S1A1A3A3A3A3A3A3").

Definition tblB (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S2S60Vrho;A1S2S3S17S0A1M0S85S27Vrho;A1M1S33S7Vrho;S3dA2S35Z10S7Vrho;S3bA2A2A2M2A2S16S0S7Vrho;S44A2A2A3S3G0S85G1S33G2Z8A2A2S16S0S7Vrho;S43A2A2A3A2A2").
Definition V_B : list positive := ltac2:(tb__ "0|0|
SdS1P1d2SdS1PeSdS1P1d3SdS1P1ccSdS1P1eaSdS1P1e0SdS1P1e1SdS1P1d4S12S1A1A3A3A3A3A3A3A3A3").

Ltac rdv HV v e := assert (uval _ e = uval _ e) by (unfold uval, e; cbn [eval]; rewrite <- (HV v%positive) by (cbn; tauto); reflexivity).
Lemma uval_rw : ltac2:(tb__ "0|0|
S1eS1eS1S1dS3S1dR1S20R2A1A3S3S75Q40A1S2bR5R3A2S2bR4R3A2A3S3S0S7R5R3A2S7R6R3A2A3F_;F_;Fe;Fv;Frho';Frho;").
Proof. intros rho rho' v e -> H. unfold uval. cbn [eval]. rewrite H. reflexivity. Qed.

Lemma tblL_reads : phi_reads V_L tblL.
Proof.
  intros rho rho' HV _ HM [(T & H1 & H2 & H3 & H4) HD]. split.
  - exists T.
    rewrite (uval_rw rho rho' 466 xLD eq_refl ltac:(apply HV; cbn; tauto)), (uval_rw rho rho' 14 vLEN eq_refl ltac:(apply HV; cbn; tauto)),
            (uval_rw rho rho' 467 xLC eq_refl ltac:(apply HV; cbn; tauto)), (uval_rw rho rho' 460 pI eq_refl ltac:(apply HV; cbn; tauto)),
            (uval_rw rho rho' 490 pNX eq_refl ltac:(apply HV; cbn; tauto)).
    split; [|split; [exact H2 | split; [exact H3 | exact H4]]]. eapply decodes_ext; [|exact H1]. intros z _. symmetry. apply HM.
  - intros z Hz. rewrite <- HM. apply HD.
    rewrite <- (uval_rw rho rho' 466 xLD eq_refl ltac:(apply HV; cbn; tauto)), <- (uval_rw rho rho' 468 xLK eq_refl ltac:(apply HV; cbn; tauto)). exact Hz.
Qed.
Lemma tblB_reads : phi_reads V_B tblB.
Proof.
  intros rho rho' HV HL HM (HT & H1 & H2). split; [|split].
  - eapply tblL_reads; [| exact HL | exact HM | exact HT]. intros v Hv. apply HV. cbn in Hv |- *. tauto.
  - rewrite (uval_rw rho rho' 466 xLD eq_refl ltac:(apply HV; cbn; tauto)), (uval_rw rho rho' 460 pI eq_refl ltac:(apply HV; cbn; tauto)),
            (uval_rw rho rho' 480 pPOS eq_refl ltac:(apply HV; cbn; tauto)).
    rewrite (rd64_ext (rm rho) (rm rho')); [exact H1|]. intros z _. symmetry. apply HM.
  - rewrite (uval_rw rho rho' 466 xLD eq_refl ltac:(apply HV; cbn; tauto)), (uval_rw rho rho' 460 pI eq_refl ltac:(apply HV; cbn; tauto)),
            (uval_rw rho rho' 481 pLNL eq_refl ltac:(apply HV; cbn; tauto)).
    rewrite (rd64_ext (rm rho) (rm rho')); [exact H2|]. intros z _. symmetry. apply HM.
Qed.

Definition ent_facts600 : list sprop := ltac2:(tb__ "0|3|
SdS1cS22S23S57S20P258A1M0S20P259A1M1A3S51A2SdS1cS22G0S1fZ4000000A1M2A2SdS1cS22G1G2A2SdS1cS22S40G0A2S12S1cA1A3A3A3A3").

Definition rateX600 : list sprop := ltac2:(tb__ "0|0|
S46S23S57S23S57S20P258A1S20P259A1A3S1fZ1A1A3S47A2").
Definition rate_small : list sprop := ltac2:(tb__ "0|2|
S14S1cSdS1cS22S40S20P258A1M0A2SdS1cS22G0S1fZ4000000A1M1A2SdS1cS22S20P259A1G1A2S12S1cA1A3A3A3S46S40S47A2A3").
Lemma rateX600_chk : ltac2:(tb__ "0|0|
S3SeS71S1cS90S66A1S5cA3SfA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma rateX600_sound : ltac2:(tb__ "0|0|
S1eS6bS1cS25R1A1S66A3S6bS1cS25R2A1S5cA3F_;Frho;").
Proof.
  intros rho HF. apply Forall_forall. intros f Hf. apply (prove_sprop_sound rho rate_small f HF).
  exact (proj1 (forallb_forall _ _) rateX600_chk f Hf).
Qed.
Definition X_bodyNc : axst := Eval vm_compute in ax_add_facts (ent_facts600 ++ rateX600) (carve_ent_stateA X_bodyN (entA pI)).
Definition s_body : wsub := ltac2:(tb__ "0|1|
SdS11S1S1dA2M0S13S1S1dP1e0S20P258A1A4SdG0S13S1S1dP1e1S20P259A1A4S12G0A1A3A3").

Definition Xl_objs : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_latch)).
Definition X_latchA : axst := Eval vm_compute in drop_lastA X_latch Xl_objs.
Definition s_loop : wsub := ltac2:(tb__ "0|2|
SdS11S1S1dA2M0S13S1S1dP1ccS23S57S3bS1fZ1A1M1A3A4SdG0S13S1S1dP1eaS23S57S4cG1A3A4S12G0A1A3A3").

Definition A1 : Z := 904.
Definition LA (c : Z) : bitem := ltac2:(tb__ "0|1|
ScZ1Z0SdS11S0S8A2M0S13S0S8S61S9S51A1A4SdG0S13S0S8S38S61A1S9S40A1A4S12G0A1A3A3Vc;A4").
Goal bud_le2 (ss_facts (ax_S X_latchA)) (bd_subst s_loop [LA A1]) [LA 0] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma lglue_checks2 : ltac2:(tb__ "0|0|
S2S3S10S26A1S31S4eS41A1A1S14S26S62SdS26S4bS3bS44S43A3S12S26A1A3A3A3S2S3S4fS95S41S62A2S5eA3S2S3SeS50S5eS4aS5bA3SfA3S2S3SeS84S5bS52A2SfA3S3SeS86S5bS59S59A3SfA3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma lglue_checks : ltac2:(tb__ "0|3|
S2S3S17S11S1dS1dA2M0A1S73G0S59S65A3S16G0S13S1dS1dS3dS77Z10M1S3eA2A4A2A3S2S3SeS2cS4eS94S3cS42S3bA1M2S1fG1A1A3A1A1SfA3S2S3SeS8bS3cS59S5fS65S64A5SfA3S2S3SeS50S5dS49S5aA3SfA3S2S3SeS84S5aS52A2SfA3S2S3SeS86S5aS59S59A3SfA3S2S3SeS71S1cS28S29S4eS8aS3cG2A2A1A1A1S14S1cS63S5cA3A3SfA3S3SeS71S1cS1cS74S1cS30R1A1S21S4eS3cA1A1A3Lf;S46S40S47A2A3SfA3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma pclMA_mono : ltac2:(tb__ "0|4|
S10S11S0S0A2M0A1M1S1eG1G1S10S11G0S0A2M2A1M3G3S0G0S72G0R1R6A3S72G0R2R6A3F_;Fx;G2S72G2R1R5A3S72G2R2R5A3F_;Fx;S7fR9R8R7R5R3A5S7fRaR9R7R5R4A5F_;F_;F_;Fa;FFF';FFF;FFB';FFB;Fr;FCST;").
Proof.
  intros CST r FB FB' FF FF' a HB HF [H|[H|[(b & n & Hb & Hr)|(f & s & fl & Hf & Hr)]]]; [left; exact H | right; left; exact H | |].
  - right; right; left. exists b, n. auto.
  - right; right; right. exists f, s, fl. auto.
Qed.

Lemma ent_addr : ltac2:(tb__ "0|7|
S1eS6bS1cS25R1A1S21S4eS3cA1A1A3S2S3S0S7R2S42S3bA1A2S33S7R2S3dA2M0S35Z10M1S7R2S3bA2M2A2A2A3S2S34G2S7R2S3fA2M3A2S2S32G3S7R2S3eA2M4A2S2S32S35G1G4A2M5ZffffffffA2S2S32G0S36Z2M6Z2fA2A2S2S3S0S7R2S77G1S3eA2A2G5A3S32S7R2S51A2S36G6Z1aA2A2A2A2A2A2A2A2F_;Fr;").
Proof.
  intros r HF.
  factz HF (SPUlt pI xLC) H1. factz HF (SPUle xLC xLK) H2. factz HF (SPUle xLK (SLit 4294967295)) H3. factz HF (SPUle (kb 16 xLK) (SLit 4294967295)) H4.
  factz HF (SPUle xLD (SLit 140737488355328)) H5. factz HF (SPUle vLEN (SLit 67108864)) H6.
  rewrite uval_lit in H3, H4, H5, H6 by lia.
  assert (EK : uval r (kb 16 xLK) = 16 * uval r xLK) by (unfold kb; apply uval_mul_lit; lia). rewrite EK in H4.
  assert (EI : uval r (SMd M_MUL (SLit 16) pI) = 16 * uval r pI) by (apply uval_mul_lit; lia).
  unfold entA. rewrite uval_add_small by (rewrite EI; lia). rewrite EI. repeat split; lia.
Qed.

Lemma ent_range : ltac2:(tb__ "0|3|
S1eS6bS1cS25R1A1S21S4eS3cA1A1A3S2S32S7R2S3dA2M0S7R2S42S3bA1A2M1A2S32S33G1Z10M2A2S33G0S7R2S77G2S3eA2A2A2A2A2F_;Fr;").
Proof.
  intros r HF. destruct (ent_addr r HF) as (E1 & H1 & H2 & H3 & H4 & EK & _). pose proof (uval_range r pI). rewrite E1, EK. lia.
Qed.

Lemma ent_addrX : ltac2:(tb__ "0|7|
S1eS6bS1cS25R1A1S21S4eS41A1A1A3S2S3S0S7R2S42S3bA1A2S33S7R2S3dA2M0S35Z10M1S7R2S3bA2M2A2A2A3S2S34G2S7R2S3fA2M3A2S2S32G3S7R2S3eA2M4A2S2S32S35G1G4A2M5ZffffffffA2S2S32G0S36Z2M6Z2fA2A2S2S3S0S7R2S77G1S3eA2A2G5A3S32S7R2S51A2S36G6Z1aA2A2A2A2A2A2A2A2F_;Fr;").
Proof.
  intros r HF.
  factz HF (SPUlt pI xLC) H1. factz HF (SPUle xLC xLK) H2. factz HF (SPUle xLK (SLit 4294967295)) H3. factz HF (SPUle (kb 16 xLK) (SLit 4294967295)) H4.
  factz HF (SPUle xLD (SLit 140737488355328)) H5. factz HF (SPUle vLEN (SLit 67108864)) H6.
  rewrite uval_lit in H3, H4, H5, H6 by lia.
  assert (EK : uval r (kb 16 xLK) = 16 * uval r xLK) by (unfold kb; apply uval_mul_lit; lia). rewrite EK in H4.
  assert (EI : uval r (SMd M_MUL (SLit 16) pI) = 16 * uval r pI) by (apply uval_mul_lit; lia).
  unfold entA. rewrite uval_add_small by (rewrite EI; lia). rewrite EI. repeat split; lia.
Qed.
Lemma ent_rangeX : ltac2:(tb__ "0|3|
S1eS6bS1cS25R1A1S21S4eS41A1A1A3S2S32S7R2S3dA2M0S7R2S2aS4bS3bS44S43A3A1A2M1A2S32S33G1Z10M2A2S33G0S7R2S77G2S3eA2A2A2A2A2F_;Fr;").
Proof.
  intros r HF. cbn [ob_base O_ent]. destruct (ent_addrX r HF) as (E1 & H1 & H2 & H3 & H4 & EK & _). pose proof (uval_range r pI). rewrite E1, EK. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S97S1eS10S75Q40A1A1S8dOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S96S58VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S8cVCST;R1A2S2S32Z0R2A2S34R2S83A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S8cVXGL;R1A2S2S32Z0R2A2S34R2S83A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S10S11S11S0S0A2S0A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable PA : AA -> Prop.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Variable rho0 : valuation.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S1eOFr;") := ltac2:(tb__ "0|0|
S68VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S7eVAInv;VCST;VXGL;S52VKc;Vrho0;VP0;VFB;VFF;VBX;VPA;Vnd;Ac").

Lemma extraLO_sound : ltac2:(tb__ "0|1|
S1eS10S26A1S10S11S1dS1dA2A1S10S11S11S1dS0A2S1dA2A1S26S0S91S52Vrho0;R6A3VP0;Vrho0;A1S72S26R4R7A3S3SeS64R5A1SfA3S2S32S18S0S0S2fRaR6A2M0A3R5A2S34R5S1bS0S0G0A3A2A2S5S7fVCST;Vrho0;S87VFB;RbR9A3S80VFF;RbR8A3R6A5S5S2S32Z0R6A2S34R6S83A2A2S93R6A1A2A2F_;F_;F_;F_;F_;Fa;Fo;Ffr;Ftv';Fobjs;Frho;").
Proof.
  intros rho objs tv' fr o a Hav (P1 & P2 & P3) _ HE Hr. left.
  assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
  { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
  apply (pclMA_mono CST rho0 FB (FBx FB rho tv') FF (FFx FF rho fr) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
  unfold extraLO in HE. apply lazy_orb_prop in HE as [HE|HE]; [|apply lazy_orb_prop in HE as [HE|HE]];
    apply lazy_andb_prop in HE as [Hb HE]; apply lazy_andb_prop in HE as [Hl Hh]; apply sv_eqb_sound in Hb; apply sv_eqb_sound in Hl; apply sv_eqb_sound in Hh;
    unfold obj_range, obj_lo_of, obj_hi_of in Hr; rewrite Hb, Hl, Hh in Hr; cbn [fst snd] in Hr.
  - apply P1. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)).
    rewrite soff_lit_small in Hr by lia. pose proof (uval_range rho vLEN) as RL.
    assert (HL : soff rho vLEN <= uval rho vLEN).
    { unfold soff, uval. rewrite bv_signed_U. destruct (Zsigned_spec (bv_unsigned (eval rho vLEN))) as [[_ X]|[_ X]]; rewrite X; lia. }
    unfold uval in *. lia.
  - apply P2. rewrite <- (AG 15%positive vCFGp eq_refl ltac:(reflexivity)). rewrite !soff_lit_small in Hr by lia. unfold uval in *. lia.
  - apply P3. rewrite <- (AG 28%positive (SVar 28) eq_refl ltac:(reflexivity)). rewrite !soff_lit_small in Hr by lia. unfold uval in *. lia.
Qed.

Lemma nd_below_mono : ltac2:(tb__ "0|0|
S1S1S79S98R3R2A2S3SeS78R4R2A2SfA3S3SeS78R4R3A2SfA3F_;F_;Fnd;Fm;Fn;").
Proof.
  intros n m [tv fr bd am] Hle H. unfold nd_below in *. cbn [nd_tv nd_fr nd_bd nd_am] in *.
  apply andb_prop in H as [H Hlen].
  apply andb_prop in H as [H Ham]. apply andb_prop in H as [H Hbd]. apply andb_prop in H as [Htv Hfr].
  apply andb_true_intro; split; [|exact Hlen].
  repeat (apply andb_true_intro; split).
  - unfold tv_below in *. apply forallb_forall. intros t Ht. pose proof (proj1 (forallb_forall _ _) Htv t Ht) as X.
    apply andb_prop in X as [X1 X2]. apply andb_true_intro. split; eapply sv_below_mono; eauto.
  - unfold fr_below in *. apply forallb_forall. intros t Ht. pose proof (proj1 (forallb_forall _ _) Hfr t Ht) as X.
    apply andb_prop in X as [X1 X2]. apply andb_true_intro. split; eapply sv_below_mono; eauto.
  - unfold bd_below in *. apply forallb_forall. intros it Hit. pose proof (proj1 (forallb_forall _ _) Hbd it Hit) as X.
    apply forallb_forall. intros ca Hca. pose proof (proj1 (forallb_forall _ _) X ca Hca) as Y. eapply sv_below_mono; eauto.
  - destruct am as [|h b|h nx c sl|h g]; cbn [am_below] in *; try reflexivity.
    + eapply sv_below_mono; eauto.
    + apply andb_prop in Ham as [Ham Hsl]. apply andb_prop in Ham as [Ham H3]. apply andb_prop in Ham as [H1 H2].
      repeat (apply andb_true_intro; split); try (eapply sv_below_mono; eauto).
      apply forallb_forall. intros ps Hps. pose proof (proj1 (forallb_forall _ _) Hsl ps Hps) as Y. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro. split; eapply sv_below_mono; eauto.
    + apply andb_prop in Ham as [H1 H2]. apply andb_true_intro. split; eapply sv_below_mono; eauto.
Qed.

Lemma X_bodyNc_eq : ltac2:(tb__ "0|1|
S3S4fS5dS82S8aS3cS42S3bA1A2M0S14S1cS14S1cS63S5cA3S21S4eG0A1A1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma body_carve : ltac2:(tb__ "0|0|
S10SbA1S7dS1eS10S75Q40A1A1S81S7aS59S5fR5R4A4S79S3SeS78S48R1A2SfA3S3SeS89S21S4eS5dA1A1SaS5aR7A2R7A3SfA3S3SeS7bS7cS5aR7A2R7A2SfA3S60R7A1S70S58VJAv;R5A1S3cR8R7R6A6S4S1eS1eS2S67R1A1S2S70S58VJAv;R7A1S49R1R9R8A6S2S3S0S7R1S3fA2S7RaS3fA2A3S3S0S7R1S3bA2S7RaS3bA2A3A2A2A2Lrho2;A2F_;F_;F_;F_;F_;Tnd;Fw;Ftp;Frho;Fam;Fbd;").
Proof.
  intros bd am rho tp w nd Hnb Hbud Ham [HT HDEF] HS. destruct w as [tr [ms md]].
  pose proof lglue_checks as (Cnth & Cwf & Csite & Cent & Cid & Ctv & Cfb).
  pose proof (smatchA_facts segs _ _ _ _ (proj1 HS)) as HF.
  destruct (ent_addr rho HF) as (EA & Hi & Hck & Hk32 & Hd47 & EK & HL26).
  destruct HT as (T & HD & HOK & HLEN & HNX).
  pose proof (uval_range rho pI) as RI. pose proof (uval_range rho xLD) as RD.
  destruct (nth_error T (Z.to_nat (uval rho pI))) as [p|] eqn:Ep.
  2: { exfalso. apply nth_error_None in Ep. lia. }
  pose proof (decodes_nth _ _ _ _ _ HD Ep) as [R0 R1]. rewrite Z2Nat.id in R0, R1 by lia. cbn [fst snd] in R0, R1.
  destruct (lines_entry_bounds T _ _ p HOK Ep) as (Q0 & Q1 & QL).
  destruct (JA_carve_ent segs HTOP AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PA HKc HNP tvL frL bd am jL xLD (kb 16 xLK) (entA pI) X_bodyN rho tp tr ms md
              Cnth eq_refl Cwf ltac:(apply (proj1 (Pos.leb_le _ _)); reflexivity) Hnb ent_range) as (rho1 & Hag & V0 & V1 & SP1).
  { apply (carve_site_chk_sound segs AInv CST ALA HCST NP rho0 P0 FB FF X_bodyN tvL frL jL extraLO rho Csite).
    intros Ai tp1 md1 _ HP0 Hav _ _ _ _ _ _ _ _ _ o a Ho HE Hr. exact (extraLO_sound rho _ _ _ o a Hav HP0 Ho HE Hr). }
  { intros z Hz. rewrite EA in Hz. apply (decodes_defined _ _ _ z HD). lia. }
  { exact HS. }
  change (ss_next (ax_S X_bodyN)) with 600%positive in V0, V1, Hag, SP1.
  rewrite EA in V0, V1. rewrite R0 in V0. rewrite R1 in V1. injection V0 as V0. injection V1 as V1.
  change (Pos.succ 600) with 601%positive in V1.
  pose proof Hag as (AGw & AGl & AGm).
  assert (AG : forall v e, e = SVar v -> (v < 600)%positive -> uval rho1 e = uval rho e).
  { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (AGw v Hv). reflexivity. }
  pose proof (uval_range rho1 (SVar 600)) as R600. pose proof (uval_range rho1 (SVar 601)) as R601.

  assert (SP2 : SPA segs (JAv nd) X_bodyNc rho1 tp (tr, mkCfg ms md)).
  { rewrite X_bodyNc_eq. apply (SPA_refacts_JA segs _ rho1 _ _ tp _ SP1).
    - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    - intros tr' md' _ HF1.
      assert (HE : Forall (holds rho1) ent_facts600).
      { unfold ent_facts600.
        constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; apply (proj2 (h_ule _ _ _)).
        + rewrite uval_add_small by lia. rewrite (AG 14%positive vLEN eq_refl ltac:(reflexivity)). lia.
        + rewrite uval_lit by lia. lia.
        + rewrite uval_lit by lia. lia.
        + rewrite (AG 490%positive pNX eq_refl ltac:(reflexivity)). rewrite <- V0. exact (HNX p eq_refl). }
      apply Forall_app. split; [|exact HF1]. apply Forall_app. split; [exact HE|].
      apply rateX600_sound. unfold rate_small. apply Forall_app. split.
      + constructor; [exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HE))))|].
        constructor; [exact (Forall_inv (Forall_inv_tail HE))|]. constructor; [exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HE)))|constructor].
      +
        apply Forall_forall. intros f Hf. apply (proj1 (Forall_forall _ _) HF1).
        pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 lglue_checks))))))) as MEM.
        pose proof (proj1 (forallb_forall _ _) MEM f Hf) as Mf. apply existsb_exists in Mf as (g & Hg & Efg). apply sprop_eqb_sound in Efg. subst g.
        revert Hg. clear. intros Hg. cbn [ax_S carve_ent_stateA]. exact Hg. }
  assert (E466 : uval (rho_sub rho1 s_body) xLD = uval rho1 xLD) by reflexivity.
  assert (E14 : uval (rho_sub rho1 s_body) vLEN = uval rho1 vLEN) by reflexivity.
  assert (E467 : uval (rho_sub rho1 s_body) xLC = uval rho1 xLC) by reflexivity.
  assert (E468 : uval (rho_sub rho1 s_body) xLK = uval rho1 xLK) by reflexivity.
  assert (E460 : uval (rho_sub rho1 s_body) pI = uval rho1 pI) by reflexivity.
  assert (E490 : uval (rho_sub rho1 s_body) pNX = uval rho1 pNX) by reflexivity.
  assert (E480 : uval (rho_sub rho1 s_body) pPOS = uval rho1 (SVar 600)) by reflexivity.
  assert (E481 : uval (rho_sub rho1 s_body) pLNL = uval rho1 (SVar 601)) by reflexivity.
  assert (EM : rm (rho_sub rho1 s_body) = rm rho1) by reflexivity.
  exists (rho_sub rho1 s_body). split; [|split; [|split; [rewrite E467; exact (AG 467%positive xLC eq_refl ltac:(reflexivity)) | rewrite E460; exact (AG 460%positive pI eq_refl ltac:(reflexivity))]]].
  -
    unfold tblB, tblL, tblL0, ldef. rewrite E466, E14, E467, E468, E460, E490, E480, E481, EM.
    rewrite (AG 466%positive xLD eq_refl ltac:(reflexivity)), (AG 14%positive vLEN eq_refl ltac:(reflexivity)), (AG 468%positive xLK eq_refl ltac:(reflexivity)),
            (AG 467%positive xLC eq_refl ltac:(reflexivity)), (AG 460%positive pI eq_refl ltac:(reflexivity)), (AG 490%positive pNX eq_refl ltac:(reflexivity)).
    split; [split|split].
    + exists T. split; [|split; [exact HOK | split; [exact HLEN | intros q Hq; rewrite Ep in Hq; exact (HNX q Hq)]]]. eapply decodes_ext; [|exact HD]. intros z _. symmetry. apply AGm.
    + intros z Hz. rewrite <- AGm. exact (HDEF z Hz).
    + rewrite (rd64_ext (rm rho) (rm rho1)) by (intros z _; symmetry; apply AGm). rewrite R0, V0. reflexivity.
    + rewrite (rd64_ext (rm rho) (rm rho1)) by (intros z _; symmetry; apply AGm). rewrite R1, V1. reflexivity.
  - apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc X_bodyNc K_body s_body nd nd rho1 tp _ Cent Cid);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | | exact Ctv | reflexivity | exact Hbud | exact Ham | exact SP2].
    apply (nd_below_mono HNEXT); [apply (proj1 (Pos.leb_le _ _)); reflexivity | exact Hnb].
Qed.

Lemma latch_absorb : ltac2:(tb__ "0|0|
S10SbA1S7dS1eS10S75Q40A1A1S81S7aS59S5fR5R4A4S79S3SeS78S48R1A2SfA3S3SeS89S21S4eS5eA1A1SaS5bR7A2R7A3SfA3S3SeS7bS7cS5bR7A2R7A2SfA3S67R7A1S70S58VJAv;R5A1S41R8R7R6A6S4S1eS1eS2S60R1A1S2S70S58VJAv;R7A1S4aR1R9R8A6S2S3S0S7R1S3fA2S7RaS3fA2A3S3S0S7R1S3bA2S7RaS23S57S3bS1fZ1A1A3A2A3A2A2A2Lrho2;A2F_;F_;F_;F_;F_;Tnd;Fw;Ftp;Frho;Fam;Fbd;").
Proof.
  intros bd am rho tp w nd Hnb Hbud Ham ([HT HDEF] & R0 & R1) HS. destruct w as [tr [ms md]].
  pose proof lglue_checks as (Cnth & _). pose proof lglue_checks2 as (Cobjs & Cdrop & Cent & Cid & Ctv).
  pose proof (smatchA_facts segs _ _ _ _ (proj1 HS)) as HF.
  destruct (ent_addrX rho HF) as (EA & Hi & Hck & Hk32 & Hd47 & EK & HL26).
  assert (EB : uval rho (ob_base (O_ent pI pPOS pLNL)) = uval rho xLD + 16 * uval rho pI) by (cbn [ob_base O_ent]; exact EA).
  destruct (JA_absorb_ent_same segs HTOP AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PA tvL frL bd am jL xLD (kb 16 xLK) X_latch Xl_objs (O_ent pI pPOS pLNL)
              pPOS pLNL rho tp tr ms md Cobjs Cnth eq_refl eq_refl eq_refl ltac:(cbn; auto) ltac:(cbn; auto) ent_rangeX
              ltac:(rewrite EB; exact R0) ltac:(rewrite EB; exact R1) HS) as [SP1 HRM].
  rewrite Cdrop in SP1. set (rho1 := rho_absorb rho [O_ent pI pPOS pLNL] (vms md tp ms)) in *.
  exists (rho_sub rho1 s_loop). split; [|split; [|split; reflexivity]].
  - assert (E466 : uval (rho_sub rho1 s_loop) xLD = uval rho xLD) by reflexivity.
    assert (E14 : uval (rho_sub rho1 s_loop) vLEN = uval rho vLEN) by reflexivity.
    assert (E467 : uval (rho_sub rho1 s_loop) xLC = uval rho xLC) by reflexivity.
    assert (E468 : uval (rho_sub rho1 s_loop) xLK = uval rho xLK) by reflexivity.
    assert (E460 : uval (rho_sub rho1 s_loop) pI = uval rho (SAlu ALU_ADD pI (SLit 1))) by reflexivity.
    assert (E490 : uval (rho_sub rho1 s_loop) pNX = uval rho (SAlu ALU_ADD pE (SLit 1))) by reflexivity.
    assert (EM : rm (rho_sub rho1 s_loop) = rm rho1) by reflexivity.
    unfold tblL, tblL0, ldef. rewrite E466, E14, E467, E468, E460, E490, EM. split; [|intros z Hz; rewrite HRM; exact (HDEF z Hz)].
    destruct HT as (T & HD & HOK & HLEN & HNX).
    pose proof (uval_range rho pI) as RI. pose proof (uval_range rho pPOS) as RP. pose proof (uval_range rho pLNL) as RL.
    destruct (nth_error T (Z.to_nat (uval rho pI))) as [p|] eqn:Ep; [|exfalso; apply nth_error_None in Ep; lia].
    pose proof (decodes_nth _ _ _ _ _ HD Ep) as [Q0 Q1]. rewrite Z2Nat.id in Q0, Q1 by lia. cbn [fst snd] in Q0, Q1.
    rewrite Q0 in R0. rewrite Q1 in R1. injection R0 as R0. injection R1 as R1.
    exists T. split; [|split; [exact HOK | split; [exact HLEN |]]]. { eapply decodes_ext; [|exact HD]. intros z _. apply HRM. }
    intros q Hq. destruct (lines_entry_bounds T _ _ p HOK Ep) as (B0 & B1 & BL).
    assert (EI1 : uval rho (SAlu ALU_ADD pI (SLit 1)) = uval rho pI + 1) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    assert (EE1 : uval rho (SAlu ALU_ADD pE (SLit 1)) = uval rho pPOS + uval rho pLNL + 1).
    { unfold pE. rewrite uval_add_small by (rewrite uval_add_small, uval_lit by lia; lia). rewrite uval_add_small by lia. rewrite uval_lit by lia. lia. }
    rewrite EE1. rewrite EI1 in Hq. replace (Z.to_nat (uval rho pI + 1)) with (S (Z.to_nat (uval rho pI))) in Hq by lia.
    pose proof (lines_next_pos T _ _ p q HOK Ep Hq). lia.
  - apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc X_latchA K_loop s_loop nd nd rho1 tp _ Cent Cid);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | | exact Ctv | reflexivity | exact Hbud | exact Ham | exact SP1].
    apply (nd_below_mono HNEXT); [apply (proj1 (Pos.leb_le _ _)); reflexivity | exact Hnb].
Qed.

Lemma dp_facts : ltac2:(tb__ "0|4|
S1eS6bS1cS25R1A1S21S4eS6cA1A1A3S2S34S7R2S45A2M0S7R2S4cA2M1A2S2S32S7R2S4dA2M2G1A2S2S32G0G2A2S2S3S0G1S33S7R2S44A2S7R2S43A2A2A3S2S32G1S7R2S51A2M3A2S32G3S36Z2Z1aA2A2A2A2A2A2A2F_;Fr;").
Proof.
  intros r HF.
  factz HF (SPUlt pT0 pE) H1. factz HF (SPUle pQ pE) H2. factz HF (SPUle pT0 pQ) H3. factz HF (SPUle pE vLEN) H4.
  factz HF (SPUle pPOS (SLit 67108864)) H5. factz HF (SPUle pLNL (SLit 67108864)) H6. factz HF (SPUle vLEN (SLit 67108864)) H7.
  rewrite uval_lit in H5, H6, H7 by lia.
  assert (EE : uval r pE = uval r pPOS + uval r pLNL) by (unfold pE; apply uval_add_small; lia). repeat split; lia.
Qed.

Lemma K_dpt_eq : ltac2:(tb__ "0|2|
S0S3S4fS6eR1A1S82S88S6cP1d8S23S57S45S1fR1A1A3M0A3M1S14S1cSdS1cS22G0S51A2S12S1cA1A3S21S4eG1A1A1A3A2A3Ft;").
Proof. intros t. reflexivity. Qed.
Lemma K_dpB_eq : ltac2:(tb__ "0|0|
S3S4fS6dS82S6cS14S1cS6fS21S4eS6cA1A1A3A2A3").
Proof. reflexivity. Qed.
Lemma dp_checks : ltac2:(tb__ "0|4|
S2S3SeS92S1SfL_;S4eS6cA1M0A2SfA3S2S3SeS71S0S0S2cS4eS88S6cP1d8S23S57S45S1fR1A1A3M1A3A1M2A1Lt;SdS0Z0SdS0Z1SdS0Z2SdS0Z3SdS0Z4SdS0Z5SdS0Z6S12S0A1A3A3A3A3A3A3A3M3A3SfA3S2S3SeS71S1cS28S29G0A1A1S6fA3SfA3S3SeS71S0S0S71S1cS28S29G2A1A1SdS1cS22G1S51A2S12S1cA1A3A3Lt;G3A3SfA3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma dp_split : ltac2:(tb__ "0|0|
S79S1eS10S75Q40A1A1S81S70S58VJAv;R4A1S6cR3R2R1A6S5S4S0S0S2S72S0R1SdS0Z0SdS0Z1SdS0Z2SdS0Z3SdS0Z4SdS0Z5SdS0Z6S12S0A1A3A3A3A3A3A3A3A3S70S58VJAv;R6A1S6eR1A1R5R4R3A6A2Lt;A2S70S58VJAv;R5A1S6dR4R3R2A6A2F_;Fw;Ftp;Frho;Fnd;").
Proof.
  intros nd rho tp w HS. pose proof (smatchA_facts segs _ _ _ _ (proj1 HS)) as HF.
  destruct (dp_facts rho HF) as (H1 & H2 & H3 & EE & H4 & H5). pose proof dp_checks as (Cva & Cwf & CfB & Cft).
  pose proof (uval_range rho pT0) as RT.
  destruct (Z_le_dec (uval rho pQ - uval rho pT0) 6) as [LE|GT].
  - left. set (t := uval rho pQ - uval rho pT0).
    assert (Ht : In t [0;1;2;3;4;5;6]) by (cbn; lia).
    exists t. split; [exact Ht|]. rewrite K_dpt_eq.
    assert (Hpin : SPA segs (JAv nd) (pinA X_dp 472 (SAlu ALU_ADD pT0 (SLit t))) rho tp w).
    { apply (SPA_pin segs _ rho tp X_dp 472 _ w); [| exact Cva | | exact HS].
      - exact (proj1 (forallb_forall _ _) Cwf t Ht).
      - apply bv_eq. change (uval rho pQ = uval rho (SAlu ALU_ADD pT0 (SLit t))).
        rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
    apply (SPA_refacts_JA segs _ rho _ _ tp w Hpin).
    + rewrite forallb_app, (proj1 (forallb_forall _ _) Cft t Ht). exact (swf_facts _ (proj1 (forallb_forall _ _) Cwf t Ht)).
    + intros tr md _ HFp. apply Forall_app. split; [|exact HFp]. constructor; [|constructor]. apply (proj2 (h_ule _ _ _)).
      rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
  - right. rewrite K_dpB_eq. apply (SPA_refacts_JA segs _ rho _ (dpB_facts ++ ss_facts (ax_S X_dp)) tp w HS); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
    intros tr md _ HFp. apply Forall_app. split; [|exact HFp]. unfold dpB_facts.
    constructor; [|constructor; [|constructor; [|constructor]]]; apply (proj2 (h_ule _ _ _));
      rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia.
Qed.
End Sum.
End Lib_load_obj_lglue.

(* [comment removed for export] *)
Module Lib_load_obj_hv0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "axst"; "la_state"; "ax_S"; "sym_runA"; "@Corelib.Init.Datatypes"; "option"; "list"; "nil"; "true"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "Pre_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_pc"; "@Stdlib.Lists.List"; "filter"; "@Stdlib.ZArith.BinInt.Z"; "eqb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.

Module HVAddr.
  Definition hv_entry : Z := 0x8d908.
  Definition hv_sd1 : Z := 0x8d934.
End HVAddr.
Import HVAddr.

Definition runL (fuel : nat) (cps : list Z) (A : axst) : list leafA := ltac2:(tb__ "0|1|
S5S6S0A1M0A1G0Lx;S4SbVfuel;Vcps;VA;S8A5G0R1Lls;S7S0A1X5x2").
Definition leafL (ls : list leafA) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
SaS1Vk;S9S0S1S2SeS0S0SfSdS3S2R1A1A1A1Vpc;A2LL;Vls;A3A4ScA4").
Definition cps_hv : list Z := hv_entry :: cps_loop.

Definition E_hv0 : axst := Eval vm_compute in leafL (runL 150 cps_hv (K_dpt 1)) hv_entry 0.
Definition sh_hv : sobj := shobj g5 4 30 [] DUnknown.
Definition K_hv0 : axst := Eval vm_compute in ax_setS E_hv0 (set_objs (ax_S E_hv0) (ss_objs (ax_S E_hv0) ++ [sh_hv])).

End Lib_load_obj_hv0.

(* [comment removed for export] *)
Module FpsC_mod.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sobj"; "SVar"; "SPEq"; "ss_objs"; "@Corelib.Init.Datatypes"; "app"; "Some"; "cons"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre"; "facts_fps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.FpsC_mod.FpsC_cert"; "T3"; "Pre"; "T5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "factsB"; "O_strS"; "factsS"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.Lists.List"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_prefix.
Import ListNotations.
Open Scope Z_scope.

Module FpsC_cert.
  Definition Pre : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.Pre.
  Definition E1 : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.E1.
  Definition E2 : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.E2.
  Definition T3 : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.T3.
  Definition E6s : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.E6s.
  Definition E6sS : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.E6sS.
  Definition T7s : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.T7s.
  Definition E4 : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.E4.
  Definition E4S : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.E4S.
  Definition T5 : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.T5.
  Definition E6b : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.E6b.
  Definition E6bS : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.E6bS.
  Definition T7b : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.T7b.
  Definition s_isl : wsub := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.s_isl.
  Definition s_sis : wsub := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.s_sis.
  Definition s_rip : wsub := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.s_rip.
  Definition s_sib : wsub := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.s_sib.
  Definition R_isl : list sobj := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.R_isl.
  Definition R_sis : list sobj := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.R_sis.
  Definition R_rip : list sobj := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.R_rip.
  Definition R_sib : list sobj := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.R_sib.
  Definition T3S : axst := ltac2:(tb__ "0|0|
SaS5S0S10S9A3SbA2").
  Definition T3B : axst := ltac2:(tb__ "0|0|
SaS5S0SeS9A3SbA2").
  Definition T5F : axst := ltac2:(tb__ "0|0|
SaS7S0S3S2P8cA1S2P10A1A2S5S0SeS9A3A3SdA2").
  Definition run1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.run1.
  Definition run2 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.run2.
  Definition efr_isl := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.efr_isl.
  Definition chk_isl := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.chk_isl.
  Definition imp_isl := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.imp_isl.
  Definition run3s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.run3s.
  Definition fsS := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.fsS.
  Definition xf6s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.xf6s.
  Definition efr_sis := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.efr_sis.
  Definition chk_sis := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.chk_sis.
  Definition imp_sis := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.imp_sis.
  Definition run3b := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.run3b.
  Definition split4 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.split4.
  Definition xs4 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.xs4.
  Definition efr_rip := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.efr_rip.
  Definition chk_rip := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.chk_rip.
  Definition imp_rip := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.imp_rip.
  Definition run5 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.run5.
  Definition fsB := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.fsB.
  Definition xf6b := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.xf6b.
  Definition efr_sib := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.efr_sib.
  Definition chk_sib := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.chk_sib.
  Definition imp_sib := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.imp_sib.
  Definition shapes := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.shapes.
  Definition Pre_facts := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.pre_facts.
  Lemma Pre_str : ltac2:(tb__ "0|0|
S11S8S1A1S13S1S4S12ScA1A1U1A3S6S1SfA2A3"). Proof. reflexivity. Qed.
  Definition lenT7 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.lenT7.
End FpsC_cert.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require FillByName.
Module FpsC_sum.
#[local] Ltac2 fbn_cfg () := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FillByName.mk reference:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_prefix.FpsSum.Jn) reference:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.FpsC_mod.FpsC_cert.Pre) @FpsC_sum [@T3S; @T3B; @T5F].
#[local] Ltac2 fbn_ty n := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FillByName.ty (fbn_cfg ()) n.
#[local] Ltac2 fbn_body n := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FillByName.body (fbn_cfg ()) n.
#[local] Ltac2 fbn_proof n := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FillByName.proof (fbn_cfg ()) n.
Definition Jn : ltac2:(fbn_ty @Jn) := ltac2:(fbn_body @Jn).
Definition tail_stmt : ltac2:(fbn_ty @tail_stmt) := ltac2:(fbn_body @tail_stmt).
Definition tail_stmt_ex : ltac2:(fbn_ty @tail_stmt_ex) := ltac2:(fbn_body @tail_stmt_ex).
Lemma fpsA_sound_S : ltac2:(fbn_ty @fpsA_sound_S). Proof. exact ltac2:(fbn_proof @fpsA_sound_S). Qed.
Lemma fpsA_sound_S_ex : ltac2:(fbn_ty @fpsA_sound_S_ex). Proof. exact ltac2:(fbn_proof @fpsA_sound_S_ex). Qed.
Lemma fpsC_sound_C : ltac2:(fbn_ty @fpsC_sound_C). Proof. exact ltac2:(fbn_proof @fpsC_sound_C). Qed.
Lemma fpsC_sound_C_ex : ltac2:(fbn_ty @fpsC_sound_C_ex). Proof. exact ltac2:(fbn_proof @fpsC_sound_C_ex). Qed.
Lemma fps_sound_S_gen : ltac2:(fbn_ty @fps_sound_S_gen). Proof. exact ltac2:(fbn_proof @fps_sound_S_gen). Qed.
Lemma fps_sound_S_gen_ex : ltac2:(fbn_ty @fps_sound_S_gen_ex). Proof. exact ltac2:(fbn_proof @fps_sound_S_gen_ex). Qed.
End FpsC_sum.
End FpsC_mod.

(* [comment removed for export] *)
Module FpsD_mod.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sobj"; "SVar"; "SPEq"; "ss_objs"; "@Corelib.Init.Datatypes"; "app"; "Some"; "cons"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre"; "facts_fps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.FpsD_mod.FpsD_cert"; "T3"; "Pre"; "T5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "factsB"; "O_strS"; "factsS"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.Lists.List"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_prefix.
Import ListNotations.
Open Scope Z_scope.

Module FpsD_cert.
  Definition Pre : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.Pre.
  Definition E1 : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.E1.
  Definition E2 : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.E2.
  Definition T3 : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.T3.
  Definition E6s : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.E6s.
  Definition E6sS : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.E6sS.
  Definition T7s : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.T7s.
  Definition E4 : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.E4.
  Definition E4S : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.E4S.
  Definition T5 : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.T5.
  Definition E6b : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.E6b.
  Definition E6bS : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.E6bS.
  Definition T7b : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.T7b.
  Definition s_isl : wsub := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.s_isl.
  Definition s_sis : wsub := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.s_sis.
  Definition s_rip : wsub := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.s_rip.
  Definition s_sib : wsub := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.s_sib.
  Definition R_isl : list sobj := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.R_isl.
  Definition R_sis : list sobj := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.R_sis.
  Definition R_rip : list sobj := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.R_rip.
  Definition R_sib : list sobj := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.R_sib.
  Definition T3S : axst := ltac2:(tb__ "0|0|
SaS5S0S10S9A3SbA2").
  Definition T3B : axst := ltac2:(tb__ "0|0|
SaS5S0SeS9A3SbA2").
  Definition T5F : axst := ltac2:(tb__ "0|0|
SaS7S0S3S2P8cA1S2P10A1A2S5S0SeS9A3A3SdA2").
  Definition run1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.run1.
  Definition run2 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.run2.
  Definition efr_isl := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.efr_isl.
  Definition chk_isl := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.chk_isl.
  Definition imp_isl := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.imp_isl.
  Definition run3s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.run3s.
  Definition fsS := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.fsS.
  Definition xf6s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.xf6s.
  Definition efr_sis := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.efr_sis.
  Definition chk_sis := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.chk_sis.
  Definition imp_sis := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.imp_sis.
  Definition run3b := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.run3b.
  Definition split4 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.split4.
  Definition xs4 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.xs4.
  Definition efr_rip := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.efr_rip.
  Definition chk_rip := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.chk_rip.
  Definition imp_rip := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.imp_rip.
  Definition run5 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.run5.
  Definition fsB := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.fsB.
  Definition xf6b := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.xf6b.
  Definition efr_sib := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.efr_sib.
  Definition chk_sib := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.chk_sib.
  Definition imp_sib := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.imp_sib.
  Definition shapes := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.shapes.
  Definition Pre_facts := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.pre_facts.
  Lemma Pre_str : ltac2:(tb__ "0|0|
S11S8S1A1S13S1S4S12ScA1A1U1A3S6S1SfA2A3"). Proof. reflexivity. Qed.
  Definition lenT7 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.lenT7.
End FpsD_cert.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require FillByName.
Module FpsD_sum.
#[local] Ltac2 fbn_cfg () := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FillByName.mk reference:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_prefix.FpsSum.Jn) reference:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.FpsD_mod.FpsD_cert.Pre) @FpsD_sum [@T3S; @T3B; @T5F].
#[local] Ltac2 fbn_ty n := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FillByName.ty (fbn_cfg ()) n.
#[local] Ltac2 fbn_body n := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FillByName.body (fbn_cfg ()) n.
#[local] Ltac2 fbn_proof n := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FillByName.proof (fbn_cfg ()) n.
Definition Jn : ltac2:(fbn_ty @Jn) := ltac2:(fbn_body @Jn).
Definition tail_stmt : ltac2:(fbn_ty @tail_stmt) := ltac2:(fbn_body @tail_stmt).
Definition tail_stmt_ex : ltac2:(fbn_ty @tail_stmt_ex) := ltac2:(fbn_body @tail_stmt_ex).
Lemma fpsA_sound_S : ltac2:(fbn_ty @fpsA_sound_S). Proof. exact ltac2:(fbn_proof @fpsA_sound_S). Qed.
Lemma fpsA_sound_S_ex : ltac2:(fbn_ty @fpsA_sound_S_ex). Proof. exact ltac2:(fbn_proof @fpsA_sound_S_ex). Qed.
End FpsD_sum.
End FpsD_mod.

(* [comment removed for export] *)
Module FpsU_mod.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sobj"; "SVar"; "SPEq"; "ss_objs"; "@Corelib.Init.Datatypes"; "app"; "Some"; "cons"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre"; "facts_fps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.FpsU_mod.FpsU_cert"; "T3"; "Pre"; "T5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "factsB"; "O_strS"; "factsS"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.Lists.List"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_prefix.
Import ListNotations.
Open Scope Z_scope.

Module FpsU_cert.
  Definition Pre : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.Pre.
  Definition E1 : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.E1.
  Definition E2 : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.E2.
  Definition T3 : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T3.
  Definition E6s : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.E6s.
  Definition E6sS : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.E6sS.
  Definition T7s : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7s.
  Definition E4 : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.E4.
  Definition E4S : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.E4S.
  Definition T5 : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T5.
  Definition E6b : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.E6b.
  Definition E6bS : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.E6bS.
  Definition T7b : axst := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b.
  Definition s_isl : wsub := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.s_isl.
  Definition s_sis : wsub := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.s_sis.
  Definition s_rip : wsub := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.s_rip.
  Definition s_sib : wsub := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.s_sib.
  Definition R_isl : list sobj := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.R_isl.
  Definition R_sis : list sobj := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.R_sis.
  Definition R_rip : list sobj := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.R_rip.
  Definition R_sib : list sobj := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.R_sib.
  Definition T3S : axst := ltac2:(tb__ "0|0|
SaS5S0S10S9A3SbA2").
  Definition T3B : axst := ltac2:(tb__ "0|0|
SaS5S0SeS9A3SbA2").
  Definition T5F : axst := ltac2:(tb__ "0|0|
SaS7S0S3S2P8cA1S2P10A1A2S5S0SeS9A3A3SdA2").
  Definition run1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.run1.
  Definition run2 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.run2.
  Definition efr_isl := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.efr_isl.
  Definition chk_isl := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.chk_isl.
  Definition imp_isl := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.imp_isl.
  Definition run3s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.run3s.
  Definition fsS := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.fsS.
  Definition xf6s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.xf6s.
  Definition efr_sis := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.efr_sis.
  Definition chk_sis := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.chk_sis.
  Definition imp_sis := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.imp_sis.
  Definition run3b := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.run3b.
  Definition split4 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.split4.
  Definition xs4 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.xs4.
  Definition efr_rip := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.efr_rip.
  Definition chk_rip := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.chk_rip.
  Definition imp_rip := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.imp_rip.
  Definition run5 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.run5.
  Definition fsB := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.fsB.
  Definition xf6b := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.xf6b.
  Definition efr_sib := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.efr_sib.
  Definition chk_sib := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.chk_sib.
  Definition imp_sib := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.imp_sib.
  Definition shapes := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.shapes.
  Definition Pre_facts := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.pre_facts.
  Lemma Pre_str : ltac2:(tb__ "0|0|
S11S8S1A1S13S1S4S12ScA1A1U1A3S6S1SfA2A3"). Proof. reflexivity. Qed.
  Definition lenT7 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.lenT7.
End FpsU_cert.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require FillByName.
Module FpsU_sum.
#[local] Ltac2 fbn_cfg () := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FillByName.mk reference:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_prefix.FpsSum.Jn) reference:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.FpsU_mod.FpsU_cert.Pre) @FpsU_sum [@T3S; @T3B; @T5F].
#[local] Ltac2 fbn_ty n := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FillByName.ty (fbn_cfg ()) n.
#[local] Ltac2 fbn_body n := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FillByName.body (fbn_cfg ()) n.
#[local] Ltac2 fbn_proof n := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FillByName.proof (fbn_cfg ()) n.
Definition Jn : ltac2:(fbn_ty @Jn) := ltac2:(fbn_body @Jn).
Definition tail_stmt : ltac2:(fbn_ty @tail_stmt) := ltac2:(fbn_body @tail_stmt).
Definition tail_stmt_ex : ltac2:(fbn_ty @tail_stmt_ex) := ltac2:(fbn_body @tail_stmt_ex).
Lemma fpsA_sound_B : ltac2:(fbn_ty @fpsA_sound_B). Proof. exact ltac2:(fbn_proof @fpsA_sound_B). Qed.
Lemma fpsA_sound_B_ex : ltac2:(fbn_ty @fpsA_sound_B_ex). Proof. exact ltac2:(fbn_proof @fpsA_sound_B_ex). Qed.
Lemma fpsA_sound_S : ltac2:(fbn_ty @fpsA_sound_S). Proof. exact ltac2:(fbn_proof @fpsA_sound_S). Qed.
Lemma fpsA_sound_S_ex : ltac2:(fbn_ty @fpsA_sound_S_ex). Proof. exact ltac2:(fbn_proof @fpsA_sound_S_ex). Qed.
Lemma fpsC_sound_C : ltac2:(fbn_ty @fpsC_sound_C). Proof. exact ltac2:(fbn_proof @fpsC_sound_C). Qed.
Lemma fpsC_sound_C_ex : ltac2:(fbn_ty @fpsC_sound_C_ex). Proof. exact ltac2:(fbn_proof @fpsC_sound_C_ex). Qed.
Lemma fps_sound_B_gen : ltac2:(fbn_ty @fps_sound_B_gen). Proof. exact ltac2:(fbn_proof @fps_sound_B_gen). Qed.
Lemma fps_sound_B_gen_ex : ltac2:(fbn_ty @fps_sound_B_gen_ex). Proof. exact ltac2:(fbn_proof @fps_sound_B_gen_ex). Qed.
End FpsU_sum.
End FpsU_mod.

