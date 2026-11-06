(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.

(* [comment removed for export] *)
Module Lib_arena_dup_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sprop"; "sv"; "SLit"; "SPUle"; "sprop_eqb"; "SAlu"; "ss_facts"; "SVar"; "ss_objs"; "sv_eqb"; "holds"; "ss_next"; "cell"; "eval"; "ob_base"; "ob_hi"; "ob_lo"; "sstate"; "DUnknown"; "ob_dflt"; "obj_range"; "odefault"; "rw"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "mul"; "lt"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "O_got"; "O_rtc"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "true"; "nil"; "prod"; "pair"; "app"; "Some"; "fst"; "option"; "false"; "snd"; "None"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "BI"; "batom"; "ASv"; "KU"; "bsumK"; "bsumV"; "bd_nn"; "bd_subst"; "bd_wpos"; "bud_le"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup"; "vSZ"; "vCAP"; "vHD"; "vLS"; "vSRC"; "s_m"; "tv0"; "vU"; "E_m"; "R_m"; "X_fit"; "X_sret2"; "bd_slow"; "nd0"; "objsR"; "P_fail"; "P_ok"; "X_ret1"; "X_ret2"; "X_sret1"; "X_sret1r"; "am_np"; "ndF"; "ndK"; "ndO"; "ndS"; "objsN"; "ohN"; "ohR"; "p_fit"; "vUg"; "O_src"; "Pre_ad"; "Pre_m"; "X_nofit1"; "X_open"; "X_ret"; "X_sret"; "base_fit"; "cutsE"; "exitsE"; "ndKc"; "rcU"; "sel_sret"; "C_K"; "C_open"; "FUEL_ad"; "O_W"; "T_mnull"; "T_mok0"; "X_K1"; "X_K2"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nofitO"; "X_nohead"; "X_ret3"; "X_sret3"; "bd_K"; "cutpcs_ad"; "fit_facts"; "iH"; "jU"; "ndL"; "ndMok"; "new_facts"; "nofit_fact"; "osR"; "otN"; "p_new"; "pad_fit"; "sel_ret"; "used_fit"; "used_new"; "vAR"; "@Stdlib.Lists.List"; "existsb"; "In"; "removelast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "potK"; "potV"; "JA_pre"; "emeasA"; "JA"; "JLA"; "NDA"; "am_eqb"; "am_subst"; "ejcertA"; "nd_below"; "nodeIA"; "ok_frameKA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ef.Lib_arena_dup_pf"; "P0_ad"; "ohF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "UStopLe"; "ulink"; "J_alloc_pre"; "L_malloc_null"; "L_malloc_ok"; "Posts_malloc"; "Pre_malloc"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "AXSplit"; "@Corelib.Lists.ListDef"; "Forall"; "map";
"@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ef.Lib_arena_dup_pf.Sum"; "Posts_ad"; "srcz"; "JL"; "srcF"; "srcP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pclMA"; "FFx"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "POT"; "drop_lastA"; "carve_stateA"; "e32"; "open_stateA"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "payA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ef.Lib_arena_dup_pf.AAP"; "basez"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ef.Lib_arena_dup_pf.Sum.X"; "openF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T0"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxCellA"; "recellv_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxCellA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Module AAP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_alloc_pf. End AAP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ADAddr RA.ReallocAddr.
Local Open Scope lazy_bool_scope.

Lemma ejcertA_ok : ltac2:(tb__ "0|0|
S0S2dSa8S29S9cS7bS89P64S74S75A7S2fA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma C_open_eq : ltac2:(tb__ "0|0|
S0S5Se2S70S4fA2S7aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mnull_eq : ltac2:(tb__ "0|0|
S0S5Se7S6eS55S52S56SbdSb9S30SbbA1SbaA3A5S7dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mok0_eq : ltac2:(tb__ "0|0|
S0S5Se7S6eS55S52S56SbeSb9S30SbbA1SbaA3A5S7eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_nofit2_eq : ltac2:(tb__ "0|0|
S0S5SddS6fS2eScS90S12S6S6fA1A1A3A2S83A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition ohF : sobj := Eval vm_compute in last (ss_objs (ax_S X_fit)) O_src.
Lemma objsF_eq : ltac2:(tb__ "0|1|
S0S2cSaA1S14S6S57A1A1M0S33SaS9bSaG0A2S2eSaSaeS30SaA1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_fit3_eq : ltac2:(tb__ "0|0|
S0S5SddSe0S57S6aS4dA3S33ScS8aS12S6S57A1A1A3A2S81A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sret1_eq : ltac2:(tb__ "0|0|
S0S36S5A1ScdS72S2eScbSccS78A1S2eScbSceSecS3aS3bS78A2U1A2SeZ18A1A2S30ScbA1A3A3A2S34S5S60A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma rcU_eq : ltac2:(tb__ "0|1|
S0S36S31S1dS18A2M0A1Sf3S6S60A1S8bS8cS4dA4S34G0S77A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sret1r_eq : ltac2:(tb__ "0|0|
S0S5S8S60S35S1dS18S77A3A2S61A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma objsN_eq : ltac2:(tb__ "0|1|
S0S2cSaA1S14S6S61A1A1S33SaS33SaS67S2eSaS68S30SaA1M0A3A3S2eSaS92G0A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sret2_eq : ltac2:(tb__ "0|0|
S0S5SdfS61S33SaS67S2eSaS68S30SaA1A3A3A2S58A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma objsN2_eq : ltac2:(tb__ "0|0|
S0S2cSaA1S14S6S58A1A1S33SaS67S2eSaS68S30SaA1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sret3_eq : ltac2:(tb__ "0|0|
S0S5SddSe0S58S93S4dA3S33ScS8fS12S6S58A1A1A3A2S87A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_ret1_eq : ltac2:(tb__ "0|0|
S0S36S5A1ScdS71S2eScbSccS95A1S30ScbA1A3A2S34S5S5eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma objsR_eq : ltac2:(tb__ "0|1|
S0S2cSaA1S14S6S5eA1A1S33SaS33SaS5bS2eSaS69S30SaA1M0A3A3S2eSaS91G0A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_ret2_eq : ltac2:(tb__ "0|0|
S0S5SdfS5eS33SaS5bS2eSaS69S30SaA1A3A3A2S5fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma objsR2_eq : ltac2:(tb__ "0|0|
S0S2cSaA1S14S6S5fA1A1S33SaS5bS2eSaS69S30SaA1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_ret3_eq : ltac2:(tb__ "0|0|
S0S5SdfS5fS5bA2S86A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition P0_ad (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S4S1S23S3cVr;S51A2M0R1A2S27R1S24G0S3cVr;S50A2A2A2A2Sd9VCST;Vr;VFB;VFF;R2A5F_;Fa;").

Definition is_src (o : sobj) : bool := ltac2:(tb__ "0|1|
S2dS2dL_;M0S15S1aVo;A1S51A2G0S15S1cVo;A1SeZ0A1A2S15S1bVo;A1S50A2S37X2dx2S37X2dx2").
Definition is_srcX (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S2dS2dL_;S15S35SdSdVr;A3S51A2S15S38SdSdVr;A3S50A2S37X2dx2").

Section Sum.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Variable AInv : ltac2:(tb__ "0|0|
Se4SbS2cS48Q40A1A1Sd2OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sc4S29VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S4SebVCST;R1A2S1S23Z0R2A2S27R2SeaA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S4SebVXGL;R1A2S1S23Z0R2A2S27R2SeaA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2cS31S31S4S4A2S4A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 3 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.

Definition JL (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
Sa4VAInv;VCST;VXGL;VKc;SadVCST;VFB;VFF;A3VFB;VFF;VBX;S9eVnd;Aa").
Definition Posts_ad : list (axst * jpostA) := ltac2:(tb__ "0|1|
S2eS31S5SafA2M0S32S5SafS5cSd6S63A1A4S2eG0S32S5SafS5dSd6S64A1A4S30G0A1A3A3").

Definition PD_ad : list (axst * ndesc) := ltac2:(tb__ "0|1|
S2eS31S5S9dA2M0S32S5S9dS5cS63A4S2eG0S32S5S9dS5dS64A4S30G0A1A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
Sa3VAInv;VCST;VXGL;S9cVKc;Vrho0;SadVCST;VFB;VFF;A3VFB;VFF;VBX;S9eVnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S31S5S9dA2SefFn;") := ltac2:(tb__ "0|0|
SaaVAInv;VCST;VXGL;S9cVKc;Vrho0;SadVCST;VFB;VFF;A3VFB;VFF;VBX;S9eAb").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Sb0S29S9cVrho0;Vtp0;Sd4A5").

Definition srcF (F : list sprop) : Prop := ltac2:(tb__ "0|1|
S1S0S2dS99ScS10SfSeZ1A1S4dA2A1VF;A3S2fA3S1S0S2dS99ScS10SfS4dS50A2A1VF;A3S2fA3S1S0S2dS99ScS10SfS50SeS25Z2Z20A2A1A2A1VF;A3S2fA3S1S0S2dS99ScS10SfSeZ1000A1S51A2A1VF;A3S2fA3S1S0S2dS99ScS10SfS11SacS51S50A3S13P1eA1M0A2A1VF;A3S2fA3S1S0S2dS99ScS10SfS51G0A2A1VF;A3S2fA3S0S2dS99ScS10SfG0SeZ7fffff800000A1A2A1VF;A3S2fA3A2A2A2A2A2A2").
Record srcz (rho : valuation) : Prop := SZ_ {
  sz_n : 1 <= uval rho vSZ <= uval rho vLS; sz_L : uval rho vLS <= 2 ^ 32;
  sz_src : 4096 <= uval rho vSRC /\ uval rho vSRC + uval rho vLS <= bv_unsigned (rw rho V_TOP);
  sz_top : bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma srcz_of : ltac2:(tb__ "0|0|
SbS2cScA1ScfScS16R2A1R1A3Sd7R2A1Sd5R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B2 & B3 & B4 & B5 & B6 & BT).
  pose proof (holds_mem _ _ _ HF BT) as HT2. zf HT2.
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  zf H1. zf H2. zf H3. zf H4. zf H5. zf H6. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  assert (E30 : uval rho (SVar 30) = bv_unsigned (rw rho V_TOP)) by reflexivity. rewrite E30 in *.
  rewrite !uval_lit in H1, H3, H4, HT2 by lia.
  rewrite uval_add_small in H5 by (pose proof (uval_range rho vSRC); pose proof (uval_range rho vLS); lia).
  constructor; lia.
Qed.
Ltac basez_tac HF := exact (AAP.basez_of _ _ HF ltac:(repeat split; vm_compute; reflexivity)).
Ltac srcz_tac HF := exact (srcz_of _ _ HF ltac:(repeat split; vm_compute; reflexivity)).

Definition srcP (rho : valuation) : Prop := ltac2:(tb__ "0|1|
S4S1S23S3cVrho;S51A2M0R1A2S27R1S24G0S3cVrho;S50A2A2A2A2Sd9VCST;Vrho0;VFB;VFF;R2A5F_;Fa;").
Lemma srcP_of : ltac2:(tb__ "0|0|
SbSadVCST;VFB;VFF;Vrho0;A4Se5S9cVrho0;R2A3Sd8R3A1F_;F_;Frho;").
Proof.
  intros rho HP [Hav _] a Ha. apply HP. unfold uval in *. cbn [eval vSRC vLS] in *.
  rewrite (Hav 13%positive) by reflexivity. rewrite (Hav 16%positive) by reflexivity. exact Ha.
Qed.
Lemma src_range : ltac2:(tb__ "0|2|
SbS4Sd5R2A1S1S23S35S4S4S20R3S6cA2M0A3R2A2S27R2S38S4S4G0A3A2A2S1S23S3cR4S51A2M1R3A2S27R3S24G1S3cR4S50A2A2A2A2F_;F_;Fa;Frho;").
Proof.
  intros rho a SZ Hr. destruct SZ as [S1 S2 S3 S4]. unfold obj_range, obj_lo_of, obj_hi_of, O_src in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. rewrite (soff_smallu rho vLS) in Hr by lia. unfold uval in *. lia.
Qed.
Lemma pclMA_x : ltac2:(tb__ "0|0|
SbS4Sd9VCST;Vrho0;VFB;VFF;R1A5Sd9VCST;Vrho0;Sf0VFB;R3S53A3SdaVFF;R3S30S31S31SdS4A2SdA2A1A3R2A5F_;Fa;Frho;").
Proof.
  intros rho a [H|[H|[(b & n & Hin & Hr)|(f & s & fl & Hin & Hr)]]]; [left; exact H | right; left; exact H | |].
  - right; right; left. exists b, n. split; [apply In_FBx; left; exact Hin | exact Hr].
  - right; right; right. exists f, s, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin | exact Hr].
Qed.

Lemma objs_ok_ad : ltac2:(tb__ "0|5|
SbS2cSaA1SedR2A1Sd5R3A1Sd8R4A1SaS9aSaR1R5A3S2S1S0SdS1aR2A1M0S13PaA1A3S1S0SdS1cR2A1M1SeN40A1A3S1S0SdS1bR2A1M2SeZ0A1M3A3S0S21S1fR2A1S1eA3M4A2A2A2S2S0SaR2S7cA3S2S1S0SdG0S98A3S1S0SdG1G3A3S1S0SdG2SeZ40A1A3G4A2A2A2S2S2S0SaR2S2aA3S0SaR2S2bA3A2S0SaR2S6cA3A2A2A2A2F_;Fo;S0S4Sf1Vrho0;A1S49Q40S22R6Sc1A2A2A3Se3VCST;Vrho0;VFB;VFF;R7S53S30S31S31SdS4A2SdA2A1R6A8F_;F_;F_;F_;F_;Fobjs;Frho;").
Proof.
  intros rho objs BZ SZ SP Hcls ET o a Ho Hr.
  destruct (Hcls o Ho) as [C|[C|[C|[C| ->]]]].
  1-4: refine (AAP.objs_ok_gen CST FB FF rho0 rho [o] BZ _ ET o a (or_introl eq_refl) Hr); intros o' [<-|[]]; auto 10.
  left. apply pclMA_x. apply SP. exact (src_range rho a SZ Hr).
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S4S2cS48Q40A1A1Sb4F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S4bS5SbS2cS48Q40A1A1Sb4ScfScS16R3A1S12S6R4A1A1A3VTR;S4aS29R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sb4Sb4Sb4Sb5R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_false : ltac2:(tb__ "0|0|
Sb4Sb4Sb5S3R3R1A1A1Fw;VTR;R3R2A2F_;FQ;FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S4bS4bS5S5Sc8S2cSaA1M0S2cS31S5SafA2M1A1S2cS31SdSdA2M2A1Sb4SbS2cS48Q40A1A1M3G2S9aG2R1R5A3S9aG2R2S7RbA1A3F_;Fr;S0S36G0A1Sb3RaR9R8A3S34G0R7A2A3S0S2dSb2RbRaR9R8Sd0G1S5S35S5SafA2R7A4A5S2fA3SbG3VTR;S4aS29RfRdR2R1A5Sb0S29S17S6RdA1A1R2R1RaA5A2Ftp1;Frho1;S2cSd3A1M4Sd1Sd2S4cS29R9R8R10S32G4SdbR3SdcR2R1A2A4A5R13RaR9R4R2A4R13Sc7Sc6RbRfSb8R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S5SafG4Sd1Sd2SbG3G4Sd1Sd2S9aG1S32S5SafRaR9A4R14A3S4cS29R12R11R19S32G4SdbR9SdcR8R7A2A4A5R1cR13R12RaR8A4Se5S17S6R1aA1A1Sc7Sc6R14R18Sb8R9R13RaA3A3R19A2R8A3S4cS29R9R8ReS32G4SdbR7SdcR6R5A2A4A5ReSc7Sc6R16R1aSb8RbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sf4R17Sb8RcR16RdA3R1bR1cR1dR10R1eR19RbA9SbSe6R18Sb8RdR17ReA3R1cR1dS6R1eA1S6R1fA1S6R11A1R1RcA9VTR;S4aS29Sb1R11Sc7Sc6R19R1dSb8ReR18RfA3A3R1eA2R18RdRcA5Sf5R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S4aS29R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CMALLOC : ltac2:(tb__ "0|1|
Se4SbS2cS48Q40A1A1VTR;S4aS29SbcVAInv;S30SbbA1M0SbaR3VKc;S13PcA1A6Sc0Sb9G0SbaA3R2R1A5Sb0S29S9cR2R1SbfSb9VAInv;VCST;VXGL;G0SbaR3VKc;A8A5A2Ftp1;Frho1;FAi;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S5S9dS31S4SdA2M0SbS2cS48Q40A1A1M1S4G1S9aS31S31S5S9dA2M2G0A2S32G2G0S32S5S9dR7R6A4R5A4S74A3S1S23Z0Sa2S32G2G0S32S5S9dR8R7A4R6A4R5A2M3A2S27G3R3A2A2VTR;S4aS29VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S5S9dSbS2cS48Q40A1A1M0S4G0S9aS31S5SafA2S32S5SafR6Sd6R5A1A4Sd4A3VTR;S4aS29VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd];
  match goal with |- context [bv_unsigned (eval ?r ?e)] => pose proof (U_range (eval r e)) end; unfold M64v in *; lia.
Tactic Notation "innth" integer(k) := do k right; left; reflexivity.

Lemma X_P_fail : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0VTR;S4aS29VJAv;S63A1S5cR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. left. reflexivity. Qed.
Lemma X_P_ok : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0VTR;S4aS29VJAv;S64A1S5dR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. right. left. reflexivity. Qed.

Lemma X_X_open : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z5bS25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S5aA1S70R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndO) C_open rho' tp w)).
  { intros w Hw.
    destruct (JA_open segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] CH vHD true X_open rho tp w) as (rho' & _ & Hw');
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | | exact Hw |].
    - intros Ai rho1 tp1 md1 HF HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET. split.
      + apply objs_ok_ad; [basez_tac HF | srcz_tac HF | exact (srcP_of rho HP0 Hav) | | exact ET].
        intros o Ho. cbn in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; auto 10.
      + intros r a Hr Ha. assert (HX : In r [(vAR, SLit 64); (vSRC, vLS)]) by exact Hr. clear Hr.
        pose proof (AAP.basez_of rho _ HF ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as [_ _ [B1 B2] _ [BT1 BT2]].
        pose proof (srcz_of rho _ HF ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as [_ _ [S1 S2] ST].
        destruct HX as [<-|[<-|[]]]; cbn [fst snd] in Ha; [rewrite uval_lit in Ha by lia; unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.vAR in *; lia | lia].
    - exists rho'. rewrite <- C_open_eq. exact Hw'. }
  apply TR_exw. intros rho'. apply (REENTER C_open ndO (90, z0)); [innth 1 | meas].
Qed.

Lemma X_X_nohead : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z51S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S5aA1S85R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [|apply (REENTER C_slow ndS (80, z0) (rho_sub rho s_nohead)); [innth 2 | meas]].
  intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_nohead C_slow s_nohead (NDA tv0 [] (CH ++ [BIc 1 0 AV0; BIc 0 1 AK0]) (AHead vHD false)) ndS);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  apply (JA_pot_out0 segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HBX); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Hw].
Qed.

Lemma and16_eq : and_hmask 18446744073709551600 = Some 16. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fit_arith : ltac2:(tb__ "0|c|
SbS23S3cR1S4fA2Z7fffff800000A2S23S3cR2S54A2S3cR2S4eA2A2S23S3cR3S4eA2S28S25Z2M0Z28A2Z21A2A2S23S3cR4S4dA2S25G0Z20M1A2A2S1S0S4S3cR5S73A2M2S24S24S3cR5S4fA2M3G1A2M4S3cR5S54A2M5A2A3S1S1S23G2S3cR5S6aA2M6A2S23G6S24G2ZfM7A2M8A2A2S1S0S4S3cR5S94A2M9S28G6G2A2A3S1S0S4S3cR5S96A2S24S24G5S3cR5S4dA2MaA2G9A2A3S1S0S4S3cR5S11SacS73SeG7A1MbA3A2G8A3S1S0S4S3cR5S11SacS6aS4dA3A2S24G6GaA2A3S1S0S4S3cR5S11SacS4fSe1S4eA1A3A2S24G3S24S3cR5S4eA2G1A2A2A3S1S0S4S3cR5S11SacS54S11SacS4dGbA3A3A2S24G5S24GaG7A2A2A3S0S4S3cR5S11SacS4fSeG1A1A3A2G4A3A2A2A2A2A2A2A2A2F_;F_;F_;F_;Frho;").
Proof.
  intros rho Hh Hu Hc Hn.
  pose proof (uval_range rho vHD) as R1. pose proof (uval_range rho vU) as R2. pose proof (uval_range rho vCAP) as R3. pose proof (uval_range rho vSZ) as R4.
  assert (EB : uval rho base_fit = uval rho vHD + 32 + uval rho vU).
  { unfold base_fit. rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
  assert (E15 : uval rho (SAlu ALU_ADD base_fit (SLit 15)) = uval rho base_fit + 15).
  { rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
  assert (EP : uval rho base_fit <= uval rho p_fit <= uval rho base_fit + 15).
  { assert (Ep : p_fit = SAlu ALU_AND (SAlu ALU_ADD base_fit (SLit 15)) (SLit 18446744073709551600)) by reflexivity. rewrite Ep.
    unfold uval at 2 3. rewrite (U_and_hmask rho _ _ 16 and16_eq). change (bv_unsigned (eval rho (SAlu ALU_ADD base_fit (SLit 15)))) with (uval rho (SAlu ALU_ADD base_fit (SLit 15))).
    rewrite E15. pose proof (Z.mod_pos_bound (uval rho base_fit + 15) 16 ltac:(lia)). lia. }
  assert (EPAD : uval rho pad_fit = uval rho p_fit - uval rho base_fit).
  { unfold pad_fit. unfold uval at 1. rewrite U_sub. change (bv_unsigned (eval rho p_fit)) with (uval rho p_fit). change (bv_unsigned (eval rho base_fit)) with (uval rho base_fit).
    unfold M64v. apply Z.mod_small. lia. }
  assert (E1 : uval rho (SAlu ALU_ADD vU vSZ) = uval rho vU + uval rho vSZ) by (rewrite uval_add_small by lia; lia).
  split; [exact EB|]. split; [exact EP|]. split; [exact EPAD|]. split; [|split; [exact E15|split; [|split; [|split]]]].
  - unfold used_fit. rewrite uval_add_small by (rewrite E1; lia). rewrite E1. lia.
  - rewrite uval_add_small by lia. reflexivity.
  - unfold e32. rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
  - rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
  - rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
Qed.

Definition openF (F : list sprop) : Prop := ltac2:(tb__ "0|1|
S1S0S2dS99ScS10SfS4fS13P1eA1M0A2A1VF;A3S2fA3S1S0S2dS99ScS10SfS54S4eA2A1VF;A3S2fA3S1S0S2dS99ScS10SfS4eSeS28S25Z2Z28A2Z21A2A1A2A1VF;A3S2fA3S1S0S2dS99ScS10SfSeZ10000A1S4eA2A1VF;A3S2fA3S1S0S2dS99ScS10SfS11SacS4fSe1S4eA1A3G0A2A1VF;A3S2fA3S1S0S2dS99ScS10SfSeZ1000A1S4fA2A1VF;A3S2fA3S0S2dS99ScS10SfG0SeZ7fffff800000A1A2A1VF;A3S2fA3A2A2A2A2A2A2").
Lemma openz : ltac2:(tb__ "0|6|
SbS2cScA1ScfScS16R2A1R1A3SeeR2A1S23S3cR4S4dA2S25Z2M0Z20M1A2A2S1S23S3cR5S4fA2M2Z7fffff800000M3A2S1S23S3cR5S54A2S3cR5S4eA2M4A2S1S23G4S28S25G0Z28A2Z21A2A2S1S23Z10000G4A2S1S23S24G2S24G4G1A2A2S3cR5S13P1eA1A2M5A2S1S23Z1000G2A2S23G5G3A2A2A2A2A2A2A2F_;F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B2 & B3 & B4 & B5 & B6 & BT) Hn.
  pose proof (holds_mem _ _ _ HF BT) as HT2. zf HT2.
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  zf H1. zf H2. zf H3. zf H4. zf H5. zf H6. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  rewrite !uval_lit in H3, H4, H6, HT2 by lia.
  destruct (fit_arith rho ltac:(lia) H2 H3 Hn) as (_ & _ & _ & _ & _ & _ & E7 & _). rewrite E7 in H5. lia.
Qed.
Ltac openz_tac HF SZ := exact (openz _ _ HF ltac:(repeat split; vm_compute; reflexivity) ltac:(destruct SZ; lia)).

Lemma X_X_nofitO : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0VTR;S4aS29VJAv;S65A1S84R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0. apply TR_facts. intros HF. apply TR_false. intros w _.
  assert (SZ : srcz rho) by srcz_tac HF.
  assert (OZ : uval rho vHD <= 140737479966720 /\ uval rho vU <= uval rho vCAP /\ uval rho vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval rho vCAP
               /\ uval rho vHD + (uval rho vCAP + 32) <= uval rho (SVar 30) /\ 4096 <= uval rho vHD /\ uval rho (SVar 30) <= 140737479966720) by openz_tac HF SZ.
  destruct OZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3 ltac:(destruct SZ; lia)) as (EB & EP & EPAD & _).
  factz HF (SPBranch BC_LTU (SAlu ALU_XOR vSZ (SLit 18446744073709551615)) pad_fit) H0.
  assert (EX : uval rho (SAlu ALU_XOR vSZ (SLit 18446744073709551615)) = 2 ^ 64 - 1 - uval rho vSZ).
  { unfold uval. rewrite (U_xor_m1 rho vSZ 18446744073709551615 ltac:(reflexivity)). reflexivity. }
  rewrite EX in H0. destruct SZ. lia.
Qed.

Lemma X_X_nofit : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z51S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S65A1S82R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  assert (SZ : srcz rho) by srcz_tac HF.
  assert (OZ : uval rho vHD <= 140737479966720 /\ uval rho vU <= uval rho vCAP /\ uval rho vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval rho vCAP
               /\ uval rho vHD + (uval rho vCAP + 32) <= uval rho (SVar 30) /\ 4096 <= uval rho vHD /\ uval rho (SVar 30) <= 140737479966720) by openz_tac HF SZ.
  destruct OZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3 ltac:(destruct SZ; lia)) as (EB & EP & EPAD & EN & _).
  factz HF (SPNot (SPBranch BC_GEU vCAP used_fit)) H0. rewrite EN in H0.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndS) C_slow rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (JA_close_np segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] bd_open vHD vNX vCAP vU X_nofit
                  (removelast (ss_objs (ax_S X_nofit))) (AA.O_hdr vHD vNX vCAP vU) rho tp tr ms md) as CL.
    specialize (CL ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(vm_compute; left; reflexivity) eq_refl Hw).
    set (rho1 := rho_absorb rho [AA.O_hdr vHD vNX vCAP vU] (vms md tp ms)) in CL.
    assert (CL2 : SPA segs (JAv (NDA tv0 [] bd_open am_np)) X_nofit2 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_nofit2_eq. change (drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit)))) with X_nofit1 in CL.
      apply (SPA_refacts_JA segs _ rho1 X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1))); [exact CL | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
      intros tr' md' _ HF1. constructor; [|exact HF1].
      apply (proj2 (holds_ule _ _ _)). rewrite U_lit. change (65537 mod M64v) with 65537.
      assert (EU : forall e, eval rho1 e = eval rho e) by (intros e; unfold rho1; apply eval_absorb).
      rewrite EU. change (bv_unsigned (eval rho (SAlu ALU_ADD vU (SAlu ALU_ADD vSZ (SLit 16))))) with (uval rho (SAlu ALU_ADD vU (SAlu ALU_ADD vSZ (SLit 16)))).
      destruct SZ as [S1 S2 S3 S4]. pose proof (uval_range rho vU).
      rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
      rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
    exists (rho_sub rho1 s_nofit).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_nofit2 C_slow s_nofit (NDA tv0 [] bd_open am_np) ndS);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact CL2]. }
  apply TR_exw. intros rho'. apply (REENTER C_slow ndS (80, z0)); [innth 2 | meas].
Qed.

Lemma X_X_fit : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z33S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S65A1S57R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  assert (SZ : srcz rho) by srcz_tac HF.
  assert (OZ : uval rho vHD <= 140737479966720 /\ uval rho vU <= uval rho vCAP /\ uval rho vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval rho vCAP
               /\ uval rho vHD + (uval rho vCAP + 32) <= uval rho (SVar 30) /\ 4096 <= uval rho vHD /\ uval rho (SVar 30) <= 140737479966720) by openz_tac HF SZ.
  destruct OZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (fit_arith rho Z1 Z2 Z3 ltac:(destruct SZ; lia)) as (EB & EP & EPAD & EN & E15 & E72 & EHC & EU15 & EH32).
  factz HF (SPBranch BC_GEU vCAP used_fit) H0. rewrite EN in H0.
  eapply TR_pre; [|apply (REENTER C_loop ndL (50, SAlu ALU_SUB vSZ vI) (rho_sub rho s_fit)); [innth 6 | meas]].
  intros w Hw.
  apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_fit3 C_loop s_fit (NDA tv0 [] bd_open (AOpen vHD vNX vCAP [(p_fit, vSZ)])) ndL);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  rewrite <- X_fit3_eq. apply (SPA_refacts_JA segs _ rho (carve_stateA X_fit p_fit vSZ) (fit_facts ++ ss_facts (ax_S X_fit))); [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HNP tv0 [] bd_open vHD vNX vCAP p_fit vSZ X_fit rho tp w);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | | | exact Hw].
    + intros r HFr. assert (SZr : srcz r) by srcz_tac HFr.
      assert (OZr : uval r vHD <= 140737479966720 /\ uval r vU <= uval r vCAP /\ uval r vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval r vCAP
                    /\ uval r vHD + (uval r vCAP + 32) <= uval r (SVar 30) /\ 4096 <= uval r vHD /\ uval r (SVar 30) <= 140737479966720) by openz_tac HFr SZr.
      destruct OZr as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6).
      destruct (fit_arith r Y1 Y2 Y3 ltac:(destruct SZr; lia)) as (EB' & EP' & EPAD' & EN' & _).
      factz HFr (SPBranch BC_GEU vCAP used_fit) H1. rewrite EN' in H1. pose proof (uval_range r vU). destruct SZr. lia.
    + intros Ai rho1 tp1 md1 HF' HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET. split.
      * intros o a Ho Hr. rewrite objsF_eq in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
        -- destruct (objs_ok_ad rho (removelast (ss_objs (ax_S X_fit))) ltac:(basez_tac HF) SZ (srcP_of rho HP0 Hav)
                      ltac:(intros o2 Ho2; revert Ho2; generalize o2; intros o3 Ho3; cbn in Ho3; destruct Ho3 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; auto 12)
                      ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
        -- right; right. unfold ohF in Hr. apply range_lit' in Hr; [|lia|lia]. unfold vHD, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.vHD. lia.
      * intros r a Hr Ha.
        pose proof (AAP.basez_of rho _ HF ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as [_ _ [B1 B2] _ [BT1 BT2]].
        assert (HX : In r [(vHD, e32 vCAP); (vAR, SLit 64); (vSRC, vLS)]) by exact Hr. clear Hr.
        destruct HX as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha.
        -- unfold e32 in Ha. rewrite uval_add_small in Ha by (rewrite uval_lit by lia; lia). rewrite uval_lit in Ha by lia.
           pose proof (uval_range rho vHD). lia.
        -- rewrite uval_lit in Ha by lia. unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.vAR in *. lia.
        -- destruct SZ as [_ _ [S1 S2] ST]. lia.
  - intros tr md _ HF2. apply Forall_app. split; [|exact HF2].
    unfold fit_facts. pose proof (uval_range rho vU). pose proof (uval_range rho vHD). destruct SZ.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; repeat change (bv_unsigned (eval ?r ?e)) with (uval r e);
      rewrite ?E15, ?E72, ?EHC, ?EU15, ?EH32, ?EN; rewrite ?uval_lit by lia; lia.
Qed.

Lemma sums_slow : ltac2:(tb__ "0|2|
SbS1S0S4S43S59R1A2S24Sa0S3cR1S6bA2M0A1S24S26Z2S3cR1S4dA2M1A2Z60A2A2A3S0S4S42S59R1A2S24S9fG0A1S24S26Z4G1A2Z40A2A2A3A2Fr;").
Proof.
  intros r. unfold bd_slow. rewrite bsumV_app, bsumK_app. destruct (POT_vals r vUg) as (-> & -> & _).
  unfold CH. cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [lfval aval bi_f bi_c]. lia.
Qed.
Lemma sums_K : ltac2:(tb__ "0|7|
SbSdS1S0S4S43S33S3dS2eS3dS3eZ1M0Z0M1S2eS31S4S3fA2M2S32S4S3fG0S40R1A1A4S30G2A1M3A3G1A4S2eS3dS3eG1G0G3S26Z2S41A2M4A4S30S3dA1A3A3SdeS4dA1A3M5R2A2S24S3cR2R1A2Sa0S3cR2S4dA2M6A1A2A3S1S0S4S42G5R2A2S24G4S9fG6A1A2A3S1S44G5R2A2S0S2dS46G5A1S2fA3A2A2A2Fk;Fr;").
Proof.
  intros r k. rewrite bsumV_app, bsumK_app. destruct (POT_vals r vSZ) as (-> & -> & NN & WP).
  cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [lfval aval bi_f bi_c]. pose proof (uval_range r k). unfold KU.
  split; [lia|]. split; [lia|]. split; [|reflexivity].
  apply bd_nn_app. split; [|exact NN]. repeat constructor; unfold bival; cbn [lfval aval bi_f bi_c]; lia.
Qed.

Lemma pay_K_arith : ltac2:(tb__ "0|5|
S4S4S4S23Z0R3A2S1S23Z1R3A2S23R3S25Z2M0Z20M1A2A2A2S23Z10001S24S24R5R4A2Z10M2A2A2S2S1S0S4R4Z10000M3A3S27S24R5G2A2M4G3A2A2S1S0S4R4G4A3S23G3G4A2A2A2S1S23S24S24R5G1A2Sa0R6A1A2S24Sa0R7A1S24S26G0R6A2Z60A2A2A2S23S24S26G0S41A2S9fR6A1A2S24S9fR7A1S24S26Z4R6A2Z40A2A2A2A2F_;F_;F_;F_;Fk;Fn;Fug;").
Proof. intros ug n k Hu Hn Hs Hk. unfold potV, potK, AV0, AK0, KU. destruct Hk as [[-> Hc]|[-> Hc]]; split; lia. Qed.

Lemma pay_K : ltac2:(tb__ "0|b|
S5SdSd7S12S6R2A1A1A1S0S2dS99ScS10SfSeZ10001A1S11SacS6bS11SacS4dSeZ10M0A1A3A3A2A1S12S6R3A1A1A3S2fA3S0S2dS99ScS10SfS6bSeS25Z2M1Z28A2A1A2A1S12S6R4A1A1A3S2fA3SbScfScS16R1A1S12S6R6A1A1M2A3Sd5R2A1S2S1S0S4S3cR3R7A2M3Z10020A3S27S24S3cR3S4dA2M4G0A2M5Z10000M6A2A2S1S0S4G3S24G4Z30A2A3S23G6G5A2A2A2F_;F_;Fr;Se8S9cVrho0;SadVCST;VFB;VFF;A3G2SeZ0M7A1G7S59S33S3dS2eS3dS3eZ1M8G7S2eS31S4S3fA2M9S32S4S3fG8S40R5A1A4S30G9A1MaA3G7A4S2eS3dS3eG7G8GaS26G1S41A2A4S30S3dA1A3A3SdeS4dA1A3A8F_;F_;F_;F_;Fk;FX;").
Proof.
  intros X k HB Hug1 Hug2 HK. destruct (sums_K rho0 k) as (_ & _ & _ & WP). split; [exact WP|]. split; [lia|]. intros r HF _ _ _. unfold pay_sem.
  assert (SZ : srcz r) by exact (srcz_of _ _ HF HB).
  destruct (sums_K r k) as (-> & -> & NN & _). destruct (sums_slow r) as [-> ->]. rewrite uval_lit by lia.
  pose proof (holds_mem _ _ _ HF Hug1) as H1. pose proof (holds_mem _ _ _ HF Hug2) as H2. zf H1. zf H2.
  repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in H1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in H2.
  rewrite !uval_lit in H1, H2 by lia. pose proof (uval_range r vUg). destruct SZ as [S1 S2 S3 S4].
  rewrite uval_add_small in H1 by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  rewrite uval_add_small in H1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H1 by lia.
  pose proof (HK r HF ltac:(split; assumption)) as HKr.
  destruct (pay_K_arith (uval r vUg) (uval r vSZ) (uval r k - 32) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [A B].
  split; [lia|]. split; [lia | exact NN].
Qed.

Lemma X_X_K : ltac2:(tb__ "0|8|
S5Sc8SdSbS2cS48Q40A1A1M0S4G0Se8S9cVrho0;SadVCST;VFB;VFF;A3S12S6R7A1A1SeZ0M1A1G1S59S33S3dS2eS3dS3eZ1M2G1S2eS31S4S3fA2M3S32S4S3fG2S40R5A1A4S30G3A1M4A3G1A4S2eS3dS3eG1G2G4S26Z2M5S41A2A4S30S3dA1A3M6A3SdeS4dA1M7A3A8S0S2dS9R8S79R7A3S2fA3S0S2dScaR8S9cA2S2fA3S0S2dSf6S9cS17S6RaA1A1A2S2fA3S0S2dSa9S17S6RbA1A1Sa5S53S30S31S31SdS4A2SdA2A1S33S3dS2eS3dS3eG2G1S2eG3S32S4S3fG2S40R9A1A4G4A3G1A4G6A3G7A3S62A4A2S2fA3S0S2dS47S12S6RcA1A1S45RbS88A2S33S3dS2eS3dS3eG2G1S2eG3S32S4S3fG2S40RaA1A4G4A3G1A4G6A3G7A3A3S2fA3S0S2dSa6Sa7RcS62A2S62A2S2fA3S0S2dSf2RdS53S53A3S2fA3S23S26Z4cS25G5Z40A2A2RaA2VTR;S4aS29VJAv;S66A1R10RdRcA5VFAM;RbRaA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fk;Fs;FX;").
Proof.
  intros X s k rho tp b tp0 HPAY He Hid Hnf Hnb Hle Ham Htv Hb.
  eapply TR_pre; [|apply (REENTER C_K ndKc (75, z0) (rho_sub rho s)); [innth 3 | meas]].
  intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X C_K s (NDA tv0 [] ([BI 1 0 [(1, ASv k)] 0; BI 0 1 [] (2 * KU)] ++ POT vSZ) am_np) ndKc);
    [exact He | exact Hid | exact Hnf | exact Hnb | exact Htv | reflexivity | exact Hle | exact Ham |].
  apply (JA_repay segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue tv0 [] bd_slow _ am_np X rho tp w HPAY Hw).
Qed.
Lemma X_X_K1 : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z4cS25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S66A1S7fR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_K X_K1 s_K1 (SLit 65568));
    [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Hb].
  apply pay_K; [repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros r HF SZ. left. factz HF (SPBranch BC_LTU (SAlu ALU_ADD vSZ (SLit 16)) (SLit 65536)) H1.
  destruct SZ. rewrite !uval_lit in * by lia. rewrite uval_add_small in H1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H1 by lia. lia.
Qed.
Lemma X_X_K2 : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z4cS25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S66A1S80R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_K X_K2 s_K2 (SAlu ALU_ADD vSZ (SLit 48)));
    [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Hb].
  apply pay_K; [repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros r HF SZ. right. factz HF (SPNot (SPBranch BC_LTU (SAlu ALU_ADD vSZ (SLit 16)) (SLit 65536))) H1.
  destruct SZ. rewrite !uval_lit in * by lia. rewrite uval_add_small in H1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H1 by lia.
  rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Lemma site_m : ltac2:(tb__ "0|1|
SbSe9VAInv;VCST;VXGL;S9cVrho0;SadVCST;VFB;VFF;A3VFB;VFF;S55S52S56R1S76S39S4A1Se4Sd1S1S1S23Z1S3cR3Sc9S52PcA2A2M0A2S27G0S25Z2Z27A2A2A2Sc5S30SbbA1SbaSc7Sc6R3S56R1A3S52A2A3A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HT HTK. cbn [nd_tv nd_fr nd_bd ndKc] in HN, HD, HZ, HFR.
  assert (SZ : srcz rho) by srcz_tac HF. pose proof (srcP_of rho HP0 Hav) as SP.
  split; [|split; [|split; [|exact I]]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None is_src R_m None r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros o a Ho Hb Hr. unfold is_src in Hb.
      apply lazy_andb_prop in Hb as [H1 Hb]. apply lazy_andb_prop in Hb as [H2 H3].
      apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
      apply (pclMA_cmaddrA CST rho0 FB FF Ai a HB HFF HT). apply SP. apply (src_range rho a SZ).
      destruct o as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi] in H1, H2, H3. subst.
      unfold obj_range, obj_lo_of, obj_hi_of, O_src in Hr |- *. cbn [ob_base ob_lo ob_hi fst snd] in Hr |- *. exact Hr.
    + exact I.
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (ss_objs (ax_S E_m)) is_srcX (ax_X E_m) None r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros r a Hr Hb Ha. unfold is_srcX in Hb. apply lazy_andb_prop in Hb as [H1 H2]. apply sv_eqb_sound in H1. apply sv_eqb_sound in H2.
      left. apply (pclMA_cmaddrA CST rho0 FB FF Ai a HB HFF HT). apply SP. destruct r as [rb rl]. cbn [fst snd] in H1, H2, Ha. subst. exact Ha.
    + exact I.
  - change (wsub_get s_m 12) with (e32 vK). factz HF (SPUle (SLit 65536) vK) H1. factz HF (SPUle vK (SLit (2 ^ 32 + 16))) H2.
    rewrite !uval_lit in H1, H2 by lia. unfold e32. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Lemma X_E_m : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z42S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S76A1S55R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (malloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E_m s_m R_m rho tp ndKc bd_m (FAM b tp0) CMALLOC).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply payA_of_bud_pay. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - intros A A_ _ _; exact I.
  - exact (site_m rho).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndKc]. fold Pre_m. rewrite T_mnull_eq. apply (REENTER T_mnull ndM (65, z0)); [innth 4 | meas].
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndKc]. fold Pre_m. rewrite T_mok0_eq.
    eapply TR_pre; [|apply (REENTER T_mok ndMok (65, z0)); [innth 5 | meas]].
    intros w Hw. unfold T_mok. apply (SPA_refacts_JA segs); [exact Hw | reflexivity |].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply JA_tv_facts; [exact ALA | | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. apply (holds_mem _ _ _ HF). OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma used_new_val : ltac2:(tb__ "0|0|
SbS0S48Q40A1S19R1S4dA2S19R1S97A2A3Fr;").
Proof.
  intros r. apply bv_eq. change (bv_unsigned (eval r vSZ) = bv_unsigned (eval r used_new)).
  unfold used_new. cbn [snd rcU c_val]. rewrite !U_add, !U_sub, !U_lit. unfold M64v.
  change (32 mod 18446744073709551616) with 32. change ((-32) mod 18446744073709551616) with (18446744073709551616 - 32).
  change (eval r vSZ) with (eval r (SVar 14)).
  pose proof (U_range (eval r (SVar 14))) as R1. pose proof (U_range (eval r (SVar pN))) as R2. unfold pN, M64v in *.
  set (n := bv_unsigned (eval r (SVar 14))) in *. set (q := bv_unsigned (eval r (SVar 122))) in *.
  rewrite <- (Zplus_mod (n - q) (q + 32)). replace (n - q + (q + 32)) with (n + 32) by lia.
  rewrite Zplus_mod_idemp_l. replace (n + 32 + (18446744073709551616 - 32)) with (n + 1 * 18446744073709551616) by lia.
  rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia.
Qed.

Lemma X_X_sret : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z33S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S8eA1S72R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndL) C_loop rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (SPA_axforms segs _ _ rho X_sret X_sret1 tp _ X_sret1_eq Hw) as H1.
    pose proof (AxCellA.SPA_recellv segs _ rho X_sret1 iH jU vSZ (fst rcU) (snd rcU) tp _ ltac:(rewrite rcU_eq; destruct rcU; reflexivity)
                  ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) (fun _ => used_new_val rho) H1) as H1r.
    rewrite X_sret1r_eq in H1r.
    pose proof (JA_push_open segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv_m [] bd_m bd_m2 0 blkN vHD vK vSZ
                  X_sret1r objsN ohN otN rho tp tr ms md objsN_eq eq_refl) as H2.
    specialize (H2 ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)
                   ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) H1r).
    rewrite X_sret2_eq in H2. cbn [remove_nth fst blkN] in H2.
    set (rho1 := rho_absorb rho [otN] (vms md tp ms)) in H2.
    assert (HF1 : Forall (holds rho1) (ss_facts (ax_S X_sret2))) by exact (smatchA_facts segs _ _ _ _ (proj1 H2)).
    assert (SZ1 : srcz rho1) by srcz_tac HF1.
    factz HF1 (SPUle (SAlu ALU_ADD (SVar pN) (e32 vK)) (SVar 30)) HE1. factz HF1 (SPUle (SVar pN) (SVar 30)) HE2.
    factz HF1 (SPUle (SLit 65536) vK) HK1. factz HF1 (SPUle vK (SLit (2 ^ 32 + 16))) HK2. factz HF1 (SPUle (SAlu ALU_ADD vSZ (SLit 16)) vK) HK3.
    factz HF1 (SPUle (SVar 30) (SLit 140737479966720)) HT30. rewrite !uval_lit in HT30, HK1, HK2 by lia.
    pose proof (uval_range rho1 (SVar pN)) as RP. pose proof (uval_range rho1 vK) as RK.
    assert (EK : uval rho1 (e32 vK) = uval rho1 vK + 32) by (unfold e32; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small in HE1 by (rewrite EK; lia). rewrite EK in HE1.
    rewrite uval_add_small in HK3 by (rewrite uval_lit by lia; destruct SZ1; lia). rewrite uval_lit in HK3 by lia.
    assert (EPn : uval rho1 p_new = uval rho1 (SVar pN) + 32) by (unfold p_new; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    assert (H3 : SPA segs (JAv (NDA tv0 [] bd_m2 (AOpen (SVar pN) vHD vK [(p_new, vSZ)]))) X_sret3 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_sret3_eq.
      apply (SPA_refacts_JA segs _ rho1 (carve_stateA X_sret2 p_new vSZ) (new_facts ++ ss_facts (ax_S X_sret2))); [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
      - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HNP tv0 [] bd_m2 (SVar pN) vHD vK p_new vSZ X_sret2 rho1 tp _);
          [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | | | exact H2].
        + intros r HFr. assert (SZr : srcz r) by srcz_tac HFr.
          factz HFr (SPUle (SAlu ALU_ADD vSZ (SLit 16)) vK) HK3'. factz HFr (SPUle vK (SLit (2 ^ 32 + 16))) HK2'. rewrite uval_lit in HK2' by lia.
          rewrite uval_add_small in HK3' by (rewrite uval_lit by lia; destruct SZr; lia). rewrite uval_lit in HK3' by lia.
          pose proof (uval_range r (SVar pN)). unfold p_new.
          rewrite uval_add_small by (rewrite uval_lit by lia; factz HFr (SPUle (SVar pN) (SVar 30)) HE; factz HFr (SPUle (SVar 30) (SLit 140737479966720)) HT30'; rewrite uval_lit in HT30' by lia; lia).
          rewrite uval_lit by lia. destruct SZr. lia.
        + intros Ai rho2 tp2 md2 HF' HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho1 Hav eq_refl) as ET. split.
          * intros o a Ho Hr. rewrite objsN2_eq in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
            -- destruct (objs_ok_ad rho1 objsN ltac:(basez_tac HF') SZ1 (srcP_of rho1 HP0 Hav)
                          ltac:(intros o2 Ho2; revert Ho2; generalize o2; intros o3 Ho3; cbn in Ho3; destruct Ho3 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; auto 12)
                          ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
            -- right; right. unfold ohN in Hr. apply range_lit' in Hr; [|lia|lia]. unfold pN. lia.
          * intros r a Hr Ha.
            assert (HX : In r [(vAR, SLit 64); (vSRC, vLS); (SVar pN, e32 vK)]) by exact Hr. clear Hr.
            pose proof (AAP.basez_of rho1 _ HF' ltac:(repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as [_ _ [B1 B2] _ [BT1 BT2]].
            destruct HX as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha.
            -- rewrite uval_lit in Ha by lia. unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.vAR in *. lia.
            -- destruct SZ1 as [_ _ [S1 S2] ST]. lia.
            -- rewrite EK in Ha. lia.
      - intros tr' md' _ HF2. apply Forall_app. split; [|exact HF2].
        unfold new_facts. destruct SZ1. change (bv_unsigned (rw rho1 V_TOP)) with (uval rho1 (SVar 30)) in *.
        assert (EPS : uval rho1 (SAlu ALU_ADD p_new vSZ) = uval rho1 p_new + uval rho1 vSZ) by (rewrite uval_add_small by lia; lia).
        assert (EHC : uval rho1 (SAlu ALU_ADD (SVar pN) (e32 vK)) = uval rho1 (SVar pN) + (uval rho1 vK + 32)) by (rewrite uval_add_small by (rewrite EK; lia); rewrite EK; lia).
        repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; repeat change (bv_unsigned (eval ?r ?e)) with (uval r e);
          rewrite ?EPS, ?EHC, ?EPn; rewrite ?uval_lit by lia; lia. }
    exists (rho_sub rho1 s_sret).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_sret3 C_loop s_sret (NDA tv0 [] bd_m2 (AOpen (SVar pN) vHD vK [(p_new, vSZ)])) ndL);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact H3]. }
  apply TR_exw. intros rho'. apply (REENTER C_loop ndL (50, SAlu ALU_SUB vSZ vI)); [innth 6 | meas].
Qed.

Lemma X_X_ret : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0VTR;S4aS29VJAv;S8dA1S71R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndK) P_ok rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (SPA_axforms segs _ _ rho X_ret X_ret1 tp _ X_ret1_eq Hw) as H1.
    pose proof (JA_unslot segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HNP tv0 [] bd_loop vH vNXl vCAPl vP vSZ
                  X_ret1 (objsR ++ [ohR]) osR rho tp tr ms md objsR_eq ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) H1) as H2.
    rewrite X_ret2_eq in H2. set (rho1 := rho_absorb rho [osR] (vms md tp ms)) in H2.
    pose proof (JA_close segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] bd_loop [] vH vNXl vCAPl vUc
                  X_ret2 objsR ohR rho1 tp tr ms md objsR2_eq ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)
                  ltac:(vm_compute; left; reflexivity) eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) H2) as H3.
    rewrite X_ret3_eq in H3. set (rho2 := rho_absorb rho1 [ohR] (vms md tp ms)) in H3.
    exists (rho_sub rho2 s_ret).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_ret3 P_ok s_ret (NDA tv0 [] [] (AHead vH true)) ndK);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact H3]. }
  apply TR_exw. intros rho'. apply X_P_ok.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S5S9dS31S4SdA2M0SbS2cS48Q40A1A1M1G1S9aS31S31S5S9dA2M2G0A2S32G2G0S32S5S9dR6R5A4R4A4S75A3VTR;S4aS29VJAv;R6A1R7R4R3A5VFAM;Sa2S32G2G0S32S5S9dR7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsE] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]; injection H as <- <- <-.
  - apply X_X_open. meas.
  - apply X_X_nohead. meas.
  - apply X_X_nofitO.
  - apply X_X_fit. meas.
  - apply X_X_nofit. meas.
  - apply X_X_K1. meas.
  - apply X_X_K2. meas.
  - apply X_E_m. meas.
  - apply X_X_sret. meas.
  - apply X_X_ret.
  - apply POST. left. reflexivity.
  - apply POST. right. left. reflexivity.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
SabS29VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
Sc2S29Sb9VAInv;VCST;VXGL;A5").

Theorem arena_dup_sum : ltac2:(tb__ "0|0|
S2cS48Q40A1A1Sb7S29Vok;S4aS29Sa1VAInv;VCST;VXGL;VKc;SadVCST;VFB;VFF;A3VFB;VFF;VBX;S9eS5aAaS6dVrho0;R1A5Sb0S29S9cVrho0;R1Sd4A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc ALA FUEL_ad cutpcs_ad 100
                (map edropA cutsE) (map edropA exitsE) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertA_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0' & Hin). cbn in E0'. injection E0' as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_false segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok))
         with (rvX := rv) (tp0 := tp0).
       - intros Ai rho1 tp1. apply (aca_malloc _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue ok (map edropA cutsE) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_ad CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_ad P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sc3S29Sb9VAInv;VCST;VXGL;A5").

Theorem arena_dup_sum_ex : ltac2:(tb__ "0|0|
S2cS48Q40A1A1Sb6S29S4aS29Sa1VAInv;VCST;VXGL;VKc;SadVCST;VFB;VFF;A3VFB;VFF;VBX;S9eS5aAaS6dVrho0;R1A5Sb0S29S9cVrho0;R1Sd4A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc ALA FUEL_ad cutpcs_ad 100 cutsE exitsE (Q tp0) ejcertA_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_false segs) (@etriple_ex segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_malloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue cutsE T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_ad CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_ad P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_arena_dup_pf.

