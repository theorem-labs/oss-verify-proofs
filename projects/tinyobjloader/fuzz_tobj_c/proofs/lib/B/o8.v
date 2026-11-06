(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_finalize_shape.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require HideA.

(* [comment removed for export] *)
Module Lib_finalize_shape_dup3_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sprop"; "sv"; "SLit"; "SPUle"; "sprop_eqb"; "SAlu"; "ss_facts"; "SVar"; "ss_objs"; "sv_eqb"; "holds"; "ss_next"; "cell"; "eval"; "ob_base"; "ob_hi"; "ob_lo"; "sstate"; "DUnknown"; "ob_dflt"; "obj_range"; "odefault"; "rw"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "mul"; "lt"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "O_got"; "O_rtc"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "true"; "nil"; "prod"; "pair"; "app"; "Some"; "fst"; "option"; "false"; "snd"; "None"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "BI"; "batom"; "ASv"; "KU"; "bsumK"; "bsumV"; "bd_nn"; "bd_subst"; "bd_wpos"; "bud_le"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup3"; "vSZ"; "vCAP"; "vHD"; "vLS"; "vSRC"; "s_m"; "tv0"; "vU"; "E_m"; "R_m"; "X_fit"; "X_sret2"; "bd_slow"; "nd0"; "objsR"; "P_fail"; "P_ok"; "X_ret1"; "X_ret2"; "X_sret1"; "X_sret1r"; "am_np"; "ndF"; "ndK"; "ndO"; "ndS"; "objsN"; "ohN"; "ohR"; "p_fit"; "vUg"; "O_src"; "Pre_ad"; "Pre_m"; "X_nofit1"; "X_open"; "X_ret"; "X_sret"; "base_fit"; "cutsE"; "exitsE"; "ndKc"; "rcU"; "sel_sret"; "C_K"; "C_open"; "FUEL_ad"; "O_W"; "T_mnull"; "T_mok0"; "X_K1"; "X_K2"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nofitO"; "X_nohead"; "X_ret3"; "X_sret3"; "bd_K"; "cutpcs_ad"; "fit_facts"; "iH"; "jU"; "ndL"; "ndMok"; "new_facts"; "nofit_fact"; "osR"; "otN"; "p_new"; "pad_fit"; "sel_ret"; "used_fit"; "used_new"; "vAR"; "@Stdlib.Lists.List"; "existsb"; "In"; "removelast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "potK"; "potV"; "JA_pre"; "emeasA"; "JA"; "JLA"; "NDA"; "am_eqb"; "am_subst"; "ejcertA"; "nd_below"; "nodeIA"; "ok_frameKA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_dup3_pf"; "P0_ad"; "ohF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "UStopLe"; "ulink"; "J_alloc_pre"; "L_malloc_null"; "L_malloc_ok"; "Posts_malloc"; "Pre_malloc"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "AXSplit"; "@Corelib.Lists.ListDef"; "Forall"; "map";
"@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_dup3_pf.Sum"; "Posts_ad"; "srcz"; "JL"; "srcF"; "srcP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pclMA"; "FFx"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "POT"; "drop_lastA"; "carve_stateA"; "e32"; "open_stateA"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "payA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_dup3_pf.AAP"; "basez"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_dup3_pf.Sum.X"; "openF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T0"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxCellA"; "recellv_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require no.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup3.
Module AAP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_arena_alloc_pf. End AAP.
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
S0S5Se2S70S4fA2S7aA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_mnull_eq : ltac2:(tb__ "0|0|
S0S5Se7S6eS55S52S56SbdSb9S30SbbA1SbaA3A5S7dA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_mok0_eq : ltac2:(tb__ "0|0|
S0S5Se7S6eS55S52S56SbeSb9S30SbbA1SbaA3A5S7eA3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_nofit2_eq : ltac2:(tb__ "0|0|
S0S5SddS6fS2eScS90S12S6S6fA1A1A3A2S83A3"). Proof. vm_compute. reflexivity. Qed.
Definition ohF : sobj := Eval vm_compute in last (ss_objs (ax_S X_fit)) O_src.
Lemma objsF_eq : ltac2:(tb__ "0|1|
S0S2cSaA1S14S6S57A1A1M0S33SaS9bSaG0A2S2eSaSaeS30SaA1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_fit3_eq : ltac2:(tb__ "0|0|
S0S5SddSe0S57S6aS4dA3S33ScS8aS12S6S57A1A1A3A2S81A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret1_eq : ltac2:(tb__ "0|0|
S0S36S5A1ScdS72S2eScbSccS78A1S2eScbSceSecS3aS3bS78A2U1A2SeZ18A1A2S30ScbA1A3A3A2S34S5S60A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma rcU_eq : ltac2:(tb__ "0|1|
S0S36S31S1dS18A2M0A1Sf3S6S60A1S8bS8cS4dA4S34G0S77A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret1r_eq : ltac2:(tb__ "0|0|
S0S5S8S60S35S1dS18S77A3A2S61A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsN_eq : ltac2:(tb__ "0|1|
S0S2cSaA1S14S6S61A1A1S33SaS33SaS67S2eSaS68S30SaA1M0A3A3S2eSaS92G0A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret2_eq : ltac2:(tb__ "0|0|
S0S5SdfS61S33SaS67S2eSaS68S30SaA1A3A3A2S58A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsN2_eq : ltac2:(tb__ "0|0|
S0S2cSaA1S14S6S58A1A1S33SaS67S2eSaS68S30SaA1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret3_eq : ltac2:(tb__ "0|0|
S0S5SddSe0S58S93S4dA3S33ScS8fS12S6S58A1A1A3A2S87A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret1_eq : ltac2:(tb__ "0|0|
S0S36S5A1ScdS71S2eScbSccS95A1S30ScbA1A3A2S34S5S5eA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsR_eq : ltac2:(tb__ "0|1|
S0S2cSaA1S14S6S5eA1A1S33SaS33SaS5bS2eSaS69S30SaA1M0A3A3S2eSaS91G0A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret2_eq : ltac2:(tb__ "0|0|
S0S5SdfS5eS33SaS5bS2eSaS69S30SaA1A3A3A2S5fA3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsR2_eq : ltac2:(tb__ "0|0|
S0S2cSaA1S14S6S5fA1A1S33SaS5bS2eSaS69S30SaA1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret3_eq : ltac2:(tb__ "0|0|
S0S5SdfS5fS5bA2S86A3"). Proof. vm_compute. reflexivity. Qed.

Definition P0_ad (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S4S1S23S3cVr;S51A2M0R1A2S27R1S24G0S3cVr;S50A2A2A2A2Sd9VCST;Vr;VFB;VFF;R2A5F_;Fa;").

Definition is_src (o : sobj) : bool := ltac2:(tb__ "0|1|
S2dS2dL_;M0S15S1aVo;A1S51A2G0S15S1cVo;A1SeZ0A1A2S15S1bVo;A1S50A2S37X2dx2S37X2dx2").
Definition is_srcX (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S2dS2dL_;S15S35SdSdVr;A3S51A2S15S38SdSdVr;A3S50A2S37X2dx2").

Section Sum.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
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
      [vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | | exact Hw |].
    - intros Ai rho1 tp1 md1 HF HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET. split.
      + apply objs_ok_ad; [basez_tac HF | srcz_tac HF | exact (srcP_of rho HP0 Hav) | | exact ET].
        intros o Ho. cbn in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; auto 10.
      + intros r a Hr Ha. assert (HX : In r [(vAR, SLit 64); (vSRC, vLS)]) by exact Hr. clear Hr.
        pose proof (AAP.basez_of rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]].
        pose proof (srcz_of rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [S1 S2] ST].
        destruct HX as [<-|[<-|[]]]; cbn [fst snd] in Ha; [rewrite uval_lit in Ha by lia; unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vAR in *; lia | lia].
    - exists rho'. rewrite <- C_open_eq. exact Hw'. }
  apply TR_exw. intros rho'. apply (REENTER C_open ndO (90, z0)); [innth 1 | meas].
Qed.

Lemma X_X_nohead : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z51S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S5aA1S85R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [|apply (REENTER C_slow ndS (80, z0) (rho_sub rho s_nohead)); [innth 2 | meas]].
  intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_nohead C_slow s_nohead (NDA tv0 [] (CH ++ [BIc 1 0 AV0; BIc 0 1 AK0]) (AHead vHD false)) ndS);
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  apply (JA_pot_out0 segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HBX); [vm_compute; reflexivity | exact Hw].
Qed.

Lemma and16_eq : and_hmask 18446744073709551600 = Some 16. Proof. vm_compute. reflexivity. Qed.
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
  assert (E1 : uval rho (SAlu ALU_ADD pad_fit vSZ) = uval rho pad_fit + uval rho vSZ) by (rewrite uval_add_small by (rewrite EPAD; lia); lia).
  split; [exact EB|]. split; [exact EP|]. split; [exact EPAD|]. split; [|split; [exact E15|split; [|split; [|split]]]].
  - unfold used_fit. rewrite uval_add_small by (rewrite E1, EPAD; lia). rewrite E1. lia.
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
    specialize (CL ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; left; reflexivity) eq_refl Hw).
    set (rho1 := rho_absorb rho [AA.O_hdr vHD vNX vCAP vU] (vms md tp ms)) in CL.
    assert (CL2 : SPA segs (JAv (NDA tv0 [] bd_open am_np)) X_nofit2 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_nofit2_eq. change (drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit)))) with X_nofit1 in CL.
      apply (SPA_refacts_JA segs _ rho1 X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1))); [exact CL | vm_compute; reflexivity |].
      intros tr' md' _ HF1. constructor; [|exact HF1].
      apply (proj2 (holds_ule _ _ _)). rewrite U_lit. change (65537 mod M64v) with 65537.
      assert (EU : forall e, eval rho1 e = eval rho e) by (intros e; unfold rho1; apply eval_absorb).
      rewrite EU. change (bv_unsigned (eval rho (SAlu ALU_ADD vU (SAlu ALU_ADD vSZ (SLit 16))))) with (uval rho (SAlu ALU_ADD vU (SAlu ALU_ADD vSZ (SLit 16)))).
      destruct SZ as [S1 S2 S3 S4]. pose proof (uval_range rho vU).
      rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
      rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
    exists (rho_sub rho1 s_nofit).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_nofit2 C_slow s_nofit (NDA tv0 [] bd_open am_np) ndS);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact CL2]. }
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
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  rewrite <- X_fit3_eq. apply (SPA_refacts_JA segs _ rho (carve_stateA X_fit p_fit vSZ) (fit_facts ++ ss_facts (ax_S X_fit))); [| vm_compute; reflexivity |].
  - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HNP tv0 [] bd_open vHD vNX vCAP p_fit vSZ X_fit rho tp w);
      [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | | | exact Hw].
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
        -- right; right. unfold ohF in Hr. apply range_lit' in Hr; [|lia|lia]. unfold vHD, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vHD. lia.
      * intros r a Hr Ha.
        pose proof (AAP.basez_of rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]].
        assert (HX : In r [(vHD, e32 vCAP); (vAR, SLit 64); (vSRC, vLS)]) by exact Hr. clear Hr.
        destruct HX as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha.
        -- unfold e32 in Ha. rewrite uval_add_small in Ha by (rewrite uval_lit by lia; lia). rewrite uval_lit in Ha by lia.
           pose proof (uval_range rho vHD). lia.
        -- rewrite uval_lit in Ha by lia. unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vAR in *. lia.
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
    [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | exact Hb].
  apply pay_K; [repeat split; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  intros r HF SZ. left. factz HF (SPBranch BC_LTU (SAlu ALU_ADD vSZ (SLit 16)) (SLit 65536)) H1.
  destruct SZ. rewrite !uval_lit in * by lia. rewrite uval_add_small in H1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H1 by lia. lia.
Qed.
Lemma X_X_K2 : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z4cS25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S66A1S80R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_K X_K2 s_K2 (SAlu ALU_ADD vSZ (SLit 48)));
    [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | exact Hb].
  apply pay_K; [repeat split; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
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
    + vm_compute. reflexivity.
    + intros o a Ho Hb Hr. unfold is_src in Hb.
      apply lazy_andb_prop in Hb as [H1 Hb]. apply lazy_andb_prop in Hb as [H2 H3].
      apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
      apply (pclMA_cmaddrA CST rho0 FB FF Ai a HB HFF HT). apply SP. apply (src_range rho a SZ).
      destruct o as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi] in H1, H2, H3. subst.
      unfold obj_range, obj_lo_of, obj_hi_of, O_src in Hr |- *. cbn [ob_base ob_lo ob_hi fst snd] in Hr |- *. exact Hr.
    + exact I.
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (ss_objs (ax_S E_m)) is_srcX (ax_X E_m) None r1 t1 m1 HM HF HN HD HZ HTK).
    + vm_compute. reflexivity.
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
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_of_bud_pay. vm_compute. reflexivity.
  - intros A A_ _ _; exact I.
  - exact (site_m rho).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndKc]. fold Pre_m. rewrite T_mnull_eq. apply (REENTER T_mnull ndM (65, z0)); [innth 4 | meas].
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndKc]. fold Pre_m. rewrite T_mok0_eq.
    eapply TR_pre; [|apply (REENTER T_mok ndMok (65, z0)); [innth 5 | meas]].
    intros w Hw. unfold T_mok. apply (SPA_refacts_JA segs); [exact Hw | reflexivity |].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply JA_tv_facts; [exact ALA | | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. apply (holds_mem _ _ _ HF). vm_compute. reflexivity.
Qed.

Lemma used_new_val : ltac2:(tb__ "0|0|
SbS0S48Q40A1S19R1S4dA2S19R1S97A2A3Fr;").
Proof.
  intros r. reflexivity.
Qed.

Lemma X_X_sret : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z33S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S8eA1S72R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndL) C_loop rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (SPA_axforms segs _ _ rho X_sret X_sret1 tp _ X_sret1_eq Hw) as H1.
    pose proof (AxCellA.SPA_recellv segs _ rho X_sret1 iH jU vSZ (fst rcU) (snd rcU) tp _ ltac:(rewrite rcU_eq; destruct rcU; reflexivity)
                  ltac:(vm_compute; reflexivity) (fun _ => used_new_val rho) H1) as H1r.
    rewrite X_sret1r_eq in H1r.
    pose proof (JA_push_open segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv_m [] bd_m bd_m2 0 blkN vHD vK vSZ
                  X_sret1r objsN ohN otN rho tp tr ms md objsN_eq eq_refl) as H2.
    specialize (H2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) H1r).
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
      apply (SPA_refacts_JA segs _ rho1 (carve_stateA X_sret2 p_new vSZ) (new_facts ++ ss_facts (ax_S X_sret2))); [| vm_compute; reflexivity |].
      - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HNP tv0 [] bd_m2 (SVar pN) vHD vK p_new vSZ X_sret2 rho1 tp _);
          [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | | | exact H2].
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
            pose proof (AAP.basez_of rho1 _ HF' ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]].
            destruct HX as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha.
            -- rewrite uval_lit in Ha by lia. unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vAR in *. lia.
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
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact H3]. }
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
                  X_ret1 (objsR ++ [ohR]) osR rho tp tr ms md objsR_eq ltac:(vm_compute; reflexivity) H1) as H2.
    rewrite X_ret2_eq in H2. set (rho1 := rho_absorb rho [osR] (vms md tp ms)) in H2.
    pose proof (JA_close segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] bd_loop [] vH vNXl vCAPl vUc
                  X_ret2 objsR ohR rho1 tp tr ms md objsR2_eq ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; left; reflexivity) eq_refl ltac:(vm_compute; reflexivity) H2) as H3.
    rewrite X_ret3_eq in H3. set (rho2 := rho_absorb rho1 [ohR] (vms md tp ms)) in H3.
    exists (rho_sub rho2 s_ret).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_ret3 P_ok s_ret (NDA tv0 [] [] (AHead vH true)) ndK);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact H3]. }
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
End Lib_finalize_shape_dup3_pf.

(* [comment removed for export] *)
Module Lib_finalize_shape_dup4_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sprop"; "sv"; "SLit"; "SPUle"; "sprop_eqb"; "SAlu"; "ss_facts"; "SVar"; "ss_objs"; "sv_eqb"; "holds"; "ss_next"; "cell"; "eval"; "ob_base"; "ob_hi"; "ob_lo"; "sstate"; "DUnknown"; "ob_dflt"; "obj_range"; "odefault"; "rw"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "mul"; "lt"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "O_got"; "O_rtc"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "true"; "nil"; "prod"; "pair"; "app"; "Some"; "fst"; "option"; "false"; "snd"; "None"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "BI"; "batom"; "ASv"; "KU"; "bsumK"; "bsumV"; "bd_nn"; "bd_subst"; "bd_wpos"; "bud_le"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup4"; "vSZ"; "vCAP"; "vHD"; "vLS"; "vSRC"; "s_m"; "tv0"; "vU"; "E_m"; "R_m"; "X_fit"; "X_sret2"; "bd_slow"; "nd0"; "objsR"; "P_fail"; "P_ok"; "X_ret1"; "X_ret2"; "X_sret1"; "X_sret1r"; "am_np"; "ndF"; "ndK"; "ndO"; "ndS"; "objsN"; "ohN"; "ohR"; "p_fit"; "vUg"; "O_src"; "Pre_ad"; "Pre_m"; "X_nofit1"; "X_open"; "X_ret"; "X_sret"; "base_fit"; "cutsE"; "exitsE"; "ndKc"; "rcU"; "sel_sret"; "C_K"; "C_open"; "FUEL_ad"; "O_W"; "T_mnull"; "T_mok0"; "X_K1"; "X_K2"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nofitO"; "X_nohead"; "X_ret3"; "X_sret3"; "bd_K"; "cutpcs_ad"; "fit_facts"; "iH"; "jU"; "ndL"; "ndMok"; "new_facts"; "nofit_fact"; "osR"; "otN"; "p_new"; "pad_fit"; "sel_ret"; "used_fit"; "used_new"; "vAR"; "@Stdlib.Lists.List"; "existsb"; "In"; "removelast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "potK"; "potV"; "JA_pre"; "emeasA"; "JA"; "JLA"; "NDA"; "am_eqb"; "am_subst"; "ejcertA"; "nd_below"; "nodeIA"; "ok_frameKA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_dup4_pf"; "P0_ad"; "ohF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "UStopLe"; "ulink"; "J_alloc_pre"; "L_malloc_null"; "L_malloc_ok"; "Posts_malloc"; "Pre_malloc"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "AXSplit"; "@Corelib.Lists.ListDef"; "Forall"; "map";
"@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_dup4_pf.Sum"; "Posts_ad"; "srcz"; "JL"; "srcF"; "srcP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pclMA"; "FFx"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "POT"; "drop_lastA"; "carve_stateA"; "e32"; "open_stateA"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "payA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_dup4_pf.AAP"; "basez"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_dup4_pf.Sum.X"; "openF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T0"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxCellA"; "recellv_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require no.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_dup4.
Module AAP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_arena_alloc_pf. End AAP.
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
S0S5Se2S70S4fA2S7aA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_mnull_eq : ltac2:(tb__ "0|0|
S0S5Se7S6eS55S52S56SbdSb9S30SbbA1SbaA3A5S7dA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_mok0_eq : ltac2:(tb__ "0|0|
S0S5Se7S6eS55S52S56SbeSb9S30SbbA1SbaA3A5S7eA3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_nofit2_eq : ltac2:(tb__ "0|0|
S0S5SddS6fS2eScS90S12S6S6fA1A1A3A2S83A3"). Proof. vm_compute. reflexivity. Qed.
Definition ohF : sobj := Eval vm_compute in last (ss_objs (ax_S X_fit)) O_src.
Lemma objsF_eq : ltac2:(tb__ "0|1|
S0S2cSaA1S14S6S57A1A1M0S33SaS9bSaG0A2S2eSaSaeS30SaA1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_fit3_eq : ltac2:(tb__ "0|0|
S0S5SddSe0S57S6aS4dA3S33ScS8aS12S6S57A1A1A3A2S81A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret1_eq : ltac2:(tb__ "0|0|
S0S36S5A1ScdS72S2eScbSccS78A1S2eScbSceSecS3aS3bS78A2U1A2SeZ18A1A2S30ScbA1A3A3A2S34S5S60A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma rcU_eq : ltac2:(tb__ "0|1|
S0S36S31S1dS18A2M0A1Sf3S6S60A1S8bS8cS4dA4S34G0S77A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret1r_eq : ltac2:(tb__ "0|0|
S0S5S8S60S35S1dS18S77A3A2S61A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsN_eq : ltac2:(tb__ "0|1|
S0S2cSaA1S14S6S61A1A1S33SaS33SaS67S2eSaS68S30SaA1M0A3A3S2eSaS92G0A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret2_eq : ltac2:(tb__ "0|0|
S0S5SdfS61S33SaS67S2eSaS68S30SaA1A3A3A2S58A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsN2_eq : ltac2:(tb__ "0|0|
S0S2cSaA1S14S6S58A1A1S33SaS67S2eSaS68S30SaA1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sret3_eq : ltac2:(tb__ "0|0|
S0S5SddSe0S58S93S4dA3S33ScS8fS12S6S58A1A1A3A2S87A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret1_eq : ltac2:(tb__ "0|0|
S0S36S5A1ScdS71S2eScbSccS95A1S30ScbA1A3A2S34S5S5eA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsR_eq : ltac2:(tb__ "0|1|
S0S2cSaA1S14S6S5eA1A1S33SaS33SaS5bS2eSaS69S30SaA1M0A3A3S2eSaS91G0A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret2_eq : ltac2:(tb__ "0|0|
S0S5SdfS5eS33SaS5bS2eSaS69S30SaA1A3A3A2S5fA3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsR2_eq : ltac2:(tb__ "0|0|
S0S2cSaA1S14S6S5fA1A1S33SaS5bS2eSaS69S30SaA1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret3_eq : ltac2:(tb__ "0|0|
S0S5SdfS5fS5bA2S86A3"). Proof. vm_compute. reflexivity. Qed.

Definition P0_ad (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S4S1S23S3cVr;S51A2M0R1A2S27R1S24G0S3cVr;S50A2A2A2A2Sd9VCST;Vr;VFB;VFF;R2A5F_;Fa;").

Definition is_src (o : sobj) : bool := ltac2:(tb__ "0|1|
S2dS2dL_;M0S15S1aVo;A1S51A2G0S15S1cVo;A1SeZ0A1A2S15S1bVo;A1S50A2S37X2dx2S37X2dx2").
Definition is_srcX (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S2dS2dL_;S15S35SdSdVr;A3S51A2S15S38SdSdVr;A3S50A2S37X2dx2").

Section Sum.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
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
      [vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | | exact Hw |].
    - intros Ai rho1 tp1 md1 HF HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET. split.
      + apply objs_ok_ad; [basez_tac HF | srcz_tac HF | exact (srcP_of rho HP0 Hav) | | exact ET].
        intros o Ho. cbn in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; auto 10.
      + intros r a Hr Ha. assert (HX : In r [(vAR, SLit 64); (vSRC, vLS)]) by exact Hr. clear Hr.
        pose proof (AAP.basez_of rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]].
        pose proof (srcz_of rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [S1 S2] ST].
        destruct HX as [<-|[<-|[]]]; cbn [fst snd] in Ha; [rewrite uval_lit in Ha by lia; unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vAR in *; lia | lia].
    - exists rho'. rewrite <- C_open_eq. exact Hw'. }
  apply TR_exw. intros rho'. apply (REENTER C_open ndO (90, z0)); [innth 1 | meas].
Qed.

Lemma X_X_nohead : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z51S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S5aA1S85R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [|apply (REENTER C_slow ndS (80, z0) (rho_sub rho s_nohead)); [innth 2 | meas]].
  intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_nohead C_slow s_nohead (NDA tv0 [] (CH ++ [BIc 1 0 AV0; BIc 0 1 AK0]) (AHead vHD false)) ndS);
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  apply (JA_pot_out0 segs AInv CST XGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HBX); [vm_compute; reflexivity | exact Hw].
Qed.

Lemma and16_eq : and_hmask 18446744073709551600 = Some 16. Proof. vm_compute. reflexivity. Qed.
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
  assert (E1 : uval rho (SAlu ALU_ADD pad_fit vSZ) = uval rho pad_fit + uval rho vSZ) by (rewrite uval_add_small by (rewrite EPAD; lia); lia).
  split; [exact EB|]. split; [exact EP|]. split; [exact EPAD|]. split; [|split; [exact E15|split; [|split; [|split]]]].
  - unfold used_fit. rewrite uval_add_small by (rewrite E1, EPAD; lia). rewrite E1. lia.
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
    specialize (CL ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; left; reflexivity) eq_refl Hw).
    set (rho1 := rho_absorb rho [AA.O_hdr vHD vNX vCAP vU] (vms md tp ms)) in CL.
    assert (CL2 : SPA segs (JAv (NDA tv0 [] bd_open am_np)) X_nofit2 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_nofit2_eq. change (drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit)))) with X_nofit1 in CL.
      apply (SPA_refacts_JA segs _ rho1 X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1))); [exact CL | vm_compute; reflexivity |].
      intros tr' md' _ HF1. constructor; [|exact HF1].
      apply (proj2 (holds_ule _ _ _)). rewrite U_lit. change (65537 mod M64v) with 65537.
      assert (EU : forall e, eval rho1 e = eval rho e) by (intros e; unfold rho1; apply eval_absorb).
      rewrite EU. change (bv_unsigned (eval rho (SAlu ALU_ADD vU (SAlu ALU_ADD vSZ (SLit 16))))) with (uval rho (SAlu ALU_ADD vU (SAlu ALU_ADD vSZ (SLit 16)))).
      destruct SZ as [S1 S2 S3 S4]. pose proof (uval_range rho vU).
      rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
      rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
    exists (rho_sub rho1 s_nofit).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_nofit2 C_slow s_nofit (NDA tv0 [] bd_open am_np) ndS);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact CL2]. }
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
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  rewrite <- X_fit3_eq. apply (SPA_refacts_JA segs _ rho (carve_stateA X_fit p_fit vSZ) (fit_facts ++ ss_facts (ax_S X_fit))); [| vm_compute; reflexivity |].
  - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HNP tv0 [] bd_open vHD vNX vCAP p_fit vSZ X_fit rho tp w);
      [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | | | exact Hw].
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
        -- right; right. unfold ohF in Hr. apply range_lit' in Hr; [|lia|lia]. unfold vHD, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vHD. lia.
      * intros r a Hr Ha.
        pose proof (AAP.basez_of rho _ HF ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]].
        assert (HX : In r [(vHD, e32 vCAP); (vAR, SLit 64); (vSRC, vLS)]) by exact Hr. clear Hr.
        destruct HX as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha.
        -- unfold e32 in Ha. rewrite uval_add_small in Ha by (rewrite uval_lit by lia; lia). rewrite uval_lit in Ha by lia.
           pose proof (uval_range rho vHD). lia.
        -- rewrite uval_lit in Ha by lia. unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vAR in *. lia.
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
    [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | exact Hb].
  apply pay_K; [repeat split; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  intros r HF SZ. left. factz HF (SPBranch BC_LTU (SAlu ALU_ADD vSZ (SLit 16)) (SLit 65536)) H1.
  destruct SZ. rewrite !uval_lit in * by lia. rewrite uval_add_small in H1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H1 by lia. lia.
Qed.
Lemma X_X_K2 : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z4cS25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S66A1S80R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_K X_K2 s_K2 (SAlu ALU_ADD vSZ (SLit 48)));
    [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | exact Hb].
  apply pay_K; [repeat split; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
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
    + vm_compute. reflexivity.
    + intros o a Ho Hb Hr. unfold is_src in Hb.
      apply lazy_andb_prop in Hb as [H1 Hb]. apply lazy_andb_prop in Hb as [H2 H3].
      apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
      apply (pclMA_cmaddrA CST rho0 FB FF Ai a HB HFF HT). apply SP. apply (src_range rho a SZ).
      destruct o as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi] in H1, H2, H3. subst.
      unfold obj_range, obj_lo_of, obj_hi_of, O_src in Hr |- *. cbn [ob_base ob_lo ob_hi fst snd] in Hr |- *. exact Hr.
    + exact I.
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (ss_objs (ax_S E_m)) is_srcX (ax_X E_m) None r1 t1 m1 HM HF HN HD HZ HTK).
    + vm_compute. reflexivity.
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
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_of_bud_pay. vm_compute. reflexivity.
  - intros A A_ _ _; exact I.
  - exact (site_m rho).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndKc]. fold Pre_m. rewrite T_mnull_eq. apply (REENTER T_mnull ndM (65, z0)); [innth 4 | meas].
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndKc]. fold Pre_m. rewrite T_mok0_eq.
    eapply TR_pre; [|apply (REENTER T_mok ndMok (65, z0)); [innth 5 | meas]].
    intros w Hw. unfold T_mok. apply (SPA_refacts_JA segs); [exact Hw | reflexivity |].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply JA_tv_facts; [exact ALA | | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. apply (holds_mem _ _ _ HF). vm_compute. reflexivity.
Qed.

Lemma used_new_val : ltac2:(tb__ "0|0|
SbS0S48Q40A1S19R1S4dA2S19R1S97A2A3Fr;").
Proof.
  intros r. reflexivity.
Qed.

Lemma X_X_sret : ltac2:(tb__ "0|1|
SbS2cS48Q40A1A1M0S4G0S23S26Z33S25Z2Z40A2A2R2A2VTR;S4aS29VJAv;S8eA1S72R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndL) C_loop rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (SPA_axforms segs _ _ rho X_sret X_sret1 tp _ X_sret1_eq Hw) as H1.
    pose proof (AxCellA.SPA_recellv segs _ rho X_sret1 iH jU vSZ (fst rcU) (snd rcU) tp _ ltac:(rewrite rcU_eq; destruct rcU; reflexivity)
                  ltac:(vm_compute; reflexivity) (fun _ => used_new_val rho) H1) as H1r.
    rewrite X_sret1r_eq in H1r.
    pose proof (JA_push_open segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv_m [] bd_m bd_m2 0 blkN vHD vK vSZ
                  X_sret1r objsN ohN otN rho tp tr ms md objsN_eq eq_refl) as H2.
    specialize (H2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) H1r).
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
      apply (SPA_refacts_JA segs _ rho1 (carve_stateA X_sret2 p_new vSZ) (new_facts ++ ss_facts (ax_S X_sret2))); [| vm_compute; reflexivity |].
      - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HNP tv0 [] bd_m2 (SVar pN) vHD vK p_new vSZ X_sret2 rho1 tp _);
          [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | | | exact H2].
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
            pose proof (AAP.basez_of rho1 _ HF' ltac:(repeat split; vm_compute; reflexivity)) as [_ _ [B1 B2] _ [BT1 BT2]].
            destruct HX as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha.
            -- rewrite uval_lit in Ha by lia. unfold vAR, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.vAR in *. lia.
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
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact H3]. }
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
                  X_ret1 (objsR ++ [ohR]) osR rho tp tr ms md objsR_eq ltac:(vm_compute; reflexivity) H1) as H2.
    rewrite X_ret2_eq in H2. set (rho1 := rho_absorb rho [osR] (vms md tp ms)) in H2.
    pose proof (JA_close segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc HBX HNP tv0 [] bd_loop [] vH vNXl vCAPl vUc
                  X_ret2 objsR ohR rho1 tp tr ms md objsR2_eq ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; left; reflexivity) eq_refl ltac:(vm_compute; reflexivity) H2) as H3.
    rewrite X_ret3_eq in H3. set (rho2 := rho_absorb rho1 [ohR] (vms md tp ms)) in H3.
    exists (rho_sub rho2 s_ret).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ad CST FB FF) FB FF BX PTrue HKc X_ret3 P_ok s_ret (NDA tv0 [] [] (AHead vH true)) ndK);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact H3]. }
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
End Lib_finalize_shape_dup4_pf.

(* [comment removed for export] *)
Module Lib_vec_push_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "pair"; "true"; "nil"; "cons"; "Some"; "fst"; "option"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "SPUle"; "sprop_eqb"; "sv"; "SLit"; "holds"; "rw"; "SVar"; "ss_facts"; "ss_next"; "SAlu"; "sobj"; "@Stdlib.Lists.List"; "existsb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "emeasA"; "JA"; "JLA"; "ND"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_vec_push_pf"; "P0_vp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "BXok_d"; "bd_wpos"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "mul"; "pow"; "sub"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_push"; "ndp0"; "Pre_vp"; "R_v"; "E_vr"; "E_vr0"; "PD_vr"; "P_push_fail"; "P_push_grown"; "P_push_keep"; "Xk_v"; "cutsP"; "exitsP"; "ndpG"; "s_v"; "slot_facts"; "vAp"; "vC1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_vec_push_pf.Sum"; "JLp"; "Posts_vp"; "basePF"; "basePz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "vK"; "vDt"; "B32"; "spm"; "vE"; "Pre_vr"; "kbytes"; "nd0"; "tv0"; "two47"; "vC"; "vDn"; "vKn"; "vV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_reserve_pf"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "PostsC"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "payA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_push.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_reserve_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_push OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_push_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRAddr RA.ReallocAddr.
Import VPAddr.

Definition P0_vp (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
SeS10SfS11S25Q40M0S19Vr;P11A2A2Z0M1A3A1S10SfS11S25G0S19Vr;PfA2A2G1A3A1F_;SeS70VFF;S25G0S19Vr;PcA2A2Z20A3S70VFF;S25G0S19Vr;PdA2A2Z30A3A2A2").

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S85S13S4S24Q40A1A1S4bOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S11S7aVCST;R1A2SeS40Z0R2A2S41R2S76A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S11S7aVXGL;R1A2SeS40Z0R2A2S41R2S76A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S4S5S5S11S11A2S11A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 4 BX.
Variable rho0 : valuation.

Definition JLp (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S30VAInv;VCST;VXGL;VKc;S35VFB;VFF;A2VFB;VFF;VBX;S2cVnd;Aa").
Definition Posts_vp : list (axst * jpostA) := ltac2:(tb__ "0|1|
SaS5S1S26A2M0S7S1S26S55S5eS4dA1A4SaG0S7S1S26S53S5eS31S6aS9S5S5S16S11A2S16A2A1S9S37A1A3A1A4SaG0S7S1S26S54S5eS59S6dS6eA2A1A4S9G0A1A3A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S2fVAInv;VCST;VXGL;S34VKc;Vrho0;S35VFB;VFF;A2VFB;VFF;VBX;S2cVnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S5S1S2bA2S7cFn;") := ltac2:(tb__ "0|0|
S32VAInv;VCST;VXGL;S34VKc;Vrho0;S35VFB;VFF;A2VFB;VFF;VBX;S2cAb").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
S27S0S34Vrho0;Vtp0;S5fA5").

Definition basePF (F : list sprop) : Prop := ltac2:(tb__ "0|4|
SeSfS6S1fS12S15S14S1aP1eA1M0S65Z30A1A2A1VF;A3S8A3SeSfS6S1fS12S15S14G0S1aPaA1M1A2A1VF;A3S8A3SeSfS6S1fS12S15S14G1S17S6bA1A2A1VF;A3S8A3SeSfS6S1fS12S15S14S17Z1A1S66A2A1VF;A3S8A3SeSfS6S1fS12S15S14S66S17Z1000A1A2A1VF;A3S8A3SeSfS6S1fS12S15S14S6cS62A2A1VF;A3S8A3SeSfS6S1fS12S15S14S62S17S64A1M2A2A1VF;A3S8A3SeSfS6S1fS12S15S14S1dS7bS63S68S62A1M3A3G0A2A1VF;A3S8A3SeSfS6S1fS12S15S14S63G0A2A1VF;A3S8A3SeSfS6S1fS12S15S14G3G2A2A1VF;A3S8A3SeSfS6S1fS12S15S14S17Z7fff7f800000A1G0A2A1VF;A3S8A3SfS6S1fS12S15S14G0S17Z7fffff800000A1A2A1VF;A3S8A3A2A2A2A2A2A2A2A2A2A2A2").
Record basePz (rho : valuation) : Prop := BPZ {
  pz_sp : bv_unsigned (rw rho V_TOP) + 48 <= uval rho (SVar 10) <= 2 ^ 47;
  pz_e : 1 <= uval rho vE <= 4096;
  pz_ck : uval rho vC <= uval rho vK <= B32;
  pz_ec : uval rho (kbytes vC) = uval rho vE * uval rho vC;
  pz_ek : uval rho (kbytes vK) = uval rho vE * uval rho vK;
  pz_dk : uval rho vDt + uval rho (kbytes vK) <= bv_unsigned (rw rho V_TOP);

  pz_top : 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma uval_spm : ltac2:(tb__ "0|1|
S13S11SeS40Z0R1A2S40R1S36R2S1aPaA1M0A2A2A2SfS11S36R3S65R2A1A2S44S36R3G0A2R2A2A3F_;Fk;Frho;").
Proof.
  intros rho k Hk. unfold spm, RA.spm, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + - k) with (x - k) by lia. apply Z.mod_small. lia.
Qed.
Lemma basePz_of : ltac2:(tb__ "0|0|
S13S4S12A1S45S12S18R2A1R1A3S60R2A1S61R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & BT1 & BT2).
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  pose proof (holds_mem _ _ _ HF B7) as H7. pose proof (holds_mem _ _ _ HF B8) as H8. pose proof (holds_mem _ _ _ HF B9) as H9. pose proof (holds_mem _ _ _ HF B10) as H10.
  pose proof (holds_mem _ _ _ HF BT1) as HT1. pose proof (holds_mem _ _ _ HF BT2) as HT2.
  zf H1. zf H2. zf H3. zf H4. zf H5. zf H6. zf H7. zf H8. zf H9. zf H10. zf HT1. zf HT2. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  assert (E30 : uval rho (SVar 30) = bv_unsigned (rw rho V_TOP)) by reflexivity. rewrite E30 in *.
  unfold two47, RA.two47, B32 in *.
  rewrite !uval_lit in H3, H4, H5, H7, H10, HT1, HT2 by lia.
  rewrite uval_spm in H1 by lia. pose proof (uval_range rho vC). pose proof (uval_range rho vDt).
  assert (EC : uval rho (kbytes vC) = uval rho vE * uval rho vC) by (unfold kbytes; apply uval_mul_small; nia).
  assert (EK : uval rho (kbytes vK) = uval rho vE * uval rho vK) by (unfold kbytes; apply uval_mul_small; nia).
  rewrite uval_add_small in H8 by lia.
  constructor; unfold B32; lia.
Qed.

Lemma P0p_now : ltac2:(tb__ "0|1|
S13S74S34Vrho0;R1A3S35VFB;VFF;Vrho0;A3SeS10SfS11S36R3S62A2Z0M0A3A1S10SfS11S36R4S63A2G0A3A1F_;SeS70VFF;S36R3S6fA2Z20A3S70VFF;S36R3S5cA2Z30A3A2A2F_;F_;Frho;").
Proof.
  intros rho Hav (A & B & C). unfold uval, vK, vDt, vV, vAp. cbn [eval].
  rewrite <- (proj1 Hav 17%positive eq_refl), <- (proj1 Hav 15%positive eq_refl), <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 13%positive eq_refl).
  auto.
Qed.

Lemma HIN_v : ltac2:(tb__ "0|2|
S13S4aS45S12S18R2A1S1bS2S50A1A1A3S35VFB;VFF;Vrho0;A3S74S34Vrho0;R4A3SeS82VCST;Vrho0;VFB;VFF;R5S9S5S16S16A2A1M0S9S5S5S16S11A2S16A2A1M1S4fA8SeS83VCST;VXGL;Vrho0;VFB;VFF;R5G0G1S56A9S73S7dVFB;R5G0A3S80VFF;R5G1A3S48S47R5S4fR4A3S5aA2A3A2A2F_;F_;F_;Fms;Frho;").
Proof.
  intros rho ms HF HP0 Hav. destruct (P0p_now rho Hav HP0) as (HKD & HV & HA).
  assert (BZ : basePz rho) by (eapply basePz_of; [exact HF | repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]). destruct BZ.
  pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET.
  split; [|split].
  - intros o a Ho Hr. cbn in Ho. destruct Ho as [<-|[]]. left. apply range_lit' in Hr; [|lia|lia]. lia.
  - intros r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in Ha; rewrite uval_lit in Ha by lia; left.
    + eapply (infrFF_pclMA CST rho0 FF); [exact HV | lia].
    + eapply (infrFF_pclMA CST rho0 FF); [exact HA | lia].
  - unfold P0_vr. rewrite !rw_call'.
    change (wsub_get s_v 17) with vK. change (wsub_get s_v 15) with vDt. change (wsub_get s_v 12) with vV. change (wsub_get s_v 14) with vAp.
    split; [exact HKD|]. split.
    + destruct HV as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin|]. unfold uval in H1, H2. lia.
    + destruct HA as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin|]. unfold uval in H1, H2. lia.
Qed.

Lemma slot_holds : ltac2:(tb__ "0|0|
S13S4S12A1S16S45S12S18R3A1R2A3S60R3A1SfS6S1fS12S15S14S5dR3A2A1R4A3S8A3SfS6S1fS12S15S14R4S17S64A1A2A1R5A3S8A3S45S12S18R7A1S5bR5A1A3F_;F_;F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF HB H1 H2. pose proof (basePz_of rho _ HF HB) as [Bsp Be Bck EC EK Bdk Btop].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. zf F1. zf F2.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. unfold B32 in *. rewrite uval_lit in F2 by lia.
  pose proof (uval_range rho vC) as RC.
  unfold vC1 in F1. rewrite uval_add_small in F1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F1 by lia.
  assert (EKk : uval rho (kbytes k) = uval rho vE * uval rho k) by (unfold kbytes; apply uval_mul_small; nia).
  assert (ECk : uval rho vE * uval rho vC + uval rho vE <= uval rho vE * uval rho k).
  { replace (uval rho vE * uval rho vC + uval rho vE) with (uval rho vE * (uval rho vC + 1)) by lia. apply Z.mul_le_mono_nonneg_l; lia. }
  unfold slot_facts. repeat constructor; apply (proj2 (holds_ule _ _ _)); repeat change (bv_unsigned (eval ?r ?e)) with (uval r e).
  - rewrite EC, EKk. nia.
  - rewrite uval_add_small by (rewrite EC; nia). rewrite EC, EKk. nia.
Qed.

Lemma payA_same : ltac2:(tb__ "0|1|
S13OF_;S4S12A1S4S37A1SfS6S39R1A1S8A3S84S34Vrho0;R4R3S17Z0M0A1G0R2R2A8F_;Fbd;Ffacts;FP0f;").
Proof.
  intros P0f facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S11S4S24Q40A1A1S3bF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S22S1S13S4S24Q40A1A1S3bS45S12S18R3A1S1bS2R4A1A1A3VTR;S21S0R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S3bS3bS3bS3eR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S22S22S1S1S49S4S1eA1M0S4S5S1S26A2M1A1S4S5S16S16A2M2A1S3bS13S4S24Q40A1A1M3G2S20G2R1R5A3S20G2R2S3RbA1A3F_;Fr;SfSdG0A1S2aRaR9R8A3SbG0R7A2A3SfS6S29RbRaR9R8S46G1S1ScS1S26A2R7A4A5S8A3S13G3VTR;S21S0RfRdR2R1A5S27S0S1cS2RdA1A1R2R1RaA5A2Ftp1;Frho1;S4S4cA1M4S4aS4bS23S0R9R8R10S7G4S71R3S72R2R1A2A4A5R13RaR9R4R2A4R13S48S47RbRfS3fR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S1S26G4S4aS4bS13G3G4S4aS4bS20G1S7S1S26RaR9A4R14A3S23S0R12R11R19S7G4S71R9S72R8R7A2A4A5R1cR13R12RaR8A4S74S1cS2R1aA1A1S48S47R14R18S3fR9R13RaA3A3R19A2R8A3S23S0R9R8ReS7G4S71R7S72R6R5A2A4A5ReS48S47R16R1aS3fRbR15RcA3A3R1bA2R15RaR9R8R6A6SeS7eR17S3fRcR16RdA3R1bR1cR1dR10R1eR19RbA9S13S75R18S3fRdR17ReA3R1cR1dS2R1eA1S2R1fA1S2R11A1R1RcA9VTR;S21S0S28R11S48S47R19R1dS3fReR18RfA3A3R1eA2R18RdRcA5S7fR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S21S0R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CVRES : ltac2:(tb__ "0|1|
S4S5S11S11A2M0A1S4S5G0S11A2A1S3aS13S4S24Q40A1A1S38Z3R3A2VTR;S21S0S2dVAInv;VCST;VXGL;VKc;S73R6R5A2R6R5R4S2cS69AaS67R3R2A5S27S0S34R3R2S81VAInv;VCST;VXGL;VKc;S73S2cS52R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S1S2bS5S11S16A2M0S13S4S24Q40A1A1M1S11G1S20S5S5S1S2bA2M2G0A2S7G2G0S7S1S2bR7R6A4R5A4S57A3SeS40Z0S2eS7G2G0S7S1S2bR8R7A4R6A4R5A2M3A2S41G3R3A2A2VTR;S21S0VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S1S2bS13S4S24Q40A1A1M0S11G0S20S5S1S26A2S7S1S26R6S5eR5A1A4S5fA3VTR;S21S0VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.
Tactic Notation "innth" integer(n) := cbn [In cutsP exitsP Posts_vp PD_vr]; do n right; left; reflexivity.

Lemma X_E_vr : ltac2:(tb__ "0|1|
S13S4S24Q40A1A1M0S11G0S40S42Z5aS43Z2Z40A2A2R2A2VTR;S21S0VJAv;S4dA1S51R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre with (P := SPA segs (JAv ndp0) E_vr rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vcall rho E_vr0 E_vr tp w E_vr_eq Hw). }
  apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_vp FB FF) FB FF BX PTrue HKc HBX P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H) Pre_vr nd0 PD_vr NF
           eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRES eq_refl
           E_vr s_v R_v Xk_v rho tp [] tv0 [] (bdP vC1 vK) [] ANone (FAM b tp0)).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply payA_of_bud_pay. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR HM HT HTK. exact (HIN_v rho ms HF' HP0 Hav).
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vr In] in Hd. destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am nd0 ndN ndG ND am_subst app].
    +   rewrite T_keep0_eq, imp_keep_tv, imp_keep_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER T_keepF ndp0 (80, z0)); [innth 1 | meas]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_keep0 T_keep tp' w T_keep_eq Hw) as Hw1.
      rewrite <- T_keepF_eq. apply (SPA_refacts_JA segs); [exact Hw1 | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
      intros tr md HJ HF2. apply Forall_app. split; [|exact HF2]. apply Forall_app. split.
      * apply (slot_holds rho' _ vK HF2); [repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
      *
        assert (TNZ : tnz rho' (vDt, kbytes vK)).
        { destruct HJ as (Ai & kc & Hav' & _ & _ & _ & _ & _ & _ & _ & _ & HP0' & _). destruct HP0' as [HKD _]. destruct Hav' as [Hrw _].
          factz HF2 (SPUle vC1 vK) F1. factz HF2 (SPUle vC vK) F0. factz HF2 (SPUle vK (SLit B32)) F2.
          unfold B32 in F2. rewrite uval_lit in F2 by lia. unfold vC1 in F1. pose proof (uval_range rho' vC) as RC.
          rewrite uval_add_small in F1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F1 by lia.
          unfold tnz. cbn [fst]. change (eval rho' vDt) with (rw rho' 15%positive).
          change (uval rho' vK) with (bv_unsigned (rw rho' 17%positive)) in F1.
          rewrite <- (Hrw 15%positive) by reflexivity. apply HKD. rewrite (Hrw 17%positive) by reflexivity. lia. }
        pose proof (JA_tv_facts segs AInv CST XGL NF Kc rho0 (P0_vp FB FF) FB FF BX PTrue ALA _ _ _ _ _ (vDt, kbytes vK) eq_refl HJ (or_introl eq_refl) TNZ) as TF.
        constructor; [|constructor]. apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA, hse_fact. cbn [fst snd]. do 5 right. left. reflexivity.
    +   rewrite T_fail0_eq, imp_fail_tv. change (bd_subst _ []) with (@nil bitem). cbn [app].
      eapply TR_pre; [|apply (REENTER T_fail (ND tv0 [] []) (80, z0)); [innth 2 | meas]].
      intros w Hw. exact (SPA_axforms segs _ xf_vback rho' T_fail0 T_fail tp' w T_fail_eq Hw).
    +   rewrite T_grown0_eq, imp_grown_tv, imp_grown_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER T_grownF (ndpG vDg vKg) (80, z0)); [innth 3 | meas]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_grown0 T_grown tp' w T_grown_eq Hw) as Hw1.
      rewrite <- T_grownF_eq. apply (SPA_refacts_JA segs); [exact Hw1 | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2].
      apply (slot_holds rho' _ vKg HF2); [repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S1S2bS5S11S16A2M0S13S4S24Q40A1A1M1G1S20S5S5S1S2bA2M2G0A2S7G2G0S7S1S2bR6R5A4R4A4S58A3VTR;S21S0VJAv;R6A1R7R4R3A5VFAM;S2eS7G2G0S7S1S2bR7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsP] in Hin.
  destruct Hin as [H|[H|[H|[H|[]]]]]; injection H as <- <- <-.
  - apply X_E_vr. meas.
  - apply POST. innth 0.
  - apply POST. innth 1.
  - apply POST. innth 2.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S33S0VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S78S0S77VAInv;VCST;VXGL;A5").

Theorem vec_push_sum : ltac2:(tb__ "0|0|
S4S24Q40A1A1S3dS0Vok;S21S0S2dVAInv;VCST;VXGL;VKc;S35VFB;VFF;A2VFB;VFF;VBX;S2cS4dAaS4eVrho0;R1A5S27S0S34Vrho0;R1S5fA5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_vp FB FF) FB FF BX PTrue HKc ALA FUEL_vp cutpcs_vp 100
                (map edropA cutsP) (map edropA exitsP) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertP_ok))
         with (ndT := ndp0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsP)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (vec_reserve_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_vp FB FF) FB FF BX PTrue ok (map edropA cutsP) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_vp FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_vp P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S79S0S77VAInv;VCST;VXGL;A5").

Theorem vec_push_sum_ex : ltac2:(tb__ "0|0|
S4S24Q40A1A1S3cS0S21S0S2dVAInv;VCST;VXGL;VKc;S35VFB;VFF;A2VFB;VFF;VBX;S2cS4dAaS4eVrho0;R1A5S27S0S34Vrho0;R1S5fA5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_vp FB FF) FB FF BX PTrue HKc ALA FUEL_vp cutpcs_vp 100 cutsP exitsP (Q tp0) ejcertP_ok)
         with (ndT := ndp0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_vp FB FF) FB FF BX PTrue) cutsP) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (vec_reserve_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_vp FB FF) FB FF BX PTrue cutsP T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_vp FB FF) FB FF BX PTrue rho0 tp0 nd Posts_vp P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_vec_push_pf.

(* [comment removed for export] *)
Module Lib_finalize_shape_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "sprop"; "ss_objs"; "SVar"; "@Corelib.Init.Datatypes"; "Some"; "option"; "cons"; "list"; "nil"; "prod"; "pair"; "true"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "AHead"; "am_subst"; "amode"; "nd_bd"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape"; "vAR"; "vHq"; "Pre_vf"; "Xk_vf"; "E_vf5"; "E_vf6"; "E_vf7"; "Xk_fin"; "s_vf5"; "s_vf6"; "s_vf7"; "vDg"; "xf_back_fin"; "sh_d"; "CHf"; "E_vp"; "ghZ"; "vLC"; "vLI"; "vPI"; "xf_back_vf"; "xf_back_vfk"; "E_ad1"; "E_ad2"; "E_ad3"; "E_ad4"; "E_mg1"; "E_mk1"; "Pre_vp"; "T_mg0"; "T_mk0"; "vHa"; "xf_call"; "E_nm"; "R_vf5"; "R_vf6"; "R_vf7"; "R_vp"; "dst_obj"; "go_facts"; "mid_obj"; "s_ad1"; "s_ad2"; "s_ad3"; "s_ad4"; "E_mg"; "E_mk"; "Pre_ad1"; "Pre_ad2"; "Pre_ad3"; "Pre_ad4"; "Pre_nm"; "Xk_vp"; "s_nm"; "vFV"; "vHv"; "vKg"; "vMI"; "vMM"; "vSG"; "xf_back_vp"; "xf_vfcall"; "E_mc"; "L_mc"; "Pre_mc"; "R_ad1"; "R_ad2"; "R_ad3"; "R_ad4"; "R_nm"; "T1_fail0"; "T1_ok0"; "T2_fail0"; "T2_ok0"; "T3_fail0"; "T3_ok0"; "T4_fail0"; "T4_ok0"; "T5_z"; "T5_z2"; "T6_z"; "T6_z2"; "T7_z"; "T7_z2"; "T_mc1"; "T_pf0"; "T_pg"; "T_pg0"; "T_pk"; "T_pk0"; "Tn_fail0"; "Tn_ok0"; "Xk_nm"; "Xof"; "bd_push"; "fmid_obj"; "lc_c"; "li_c"; "pi_c"; "s_m"; "sh_c"; "sh_k"; "src_obj"; "vSH"; "xf_back_nm"; "xf_mback"; "xf_mcall"; "E_ad1_0"; "E_ad2_0"; "E_ad3_0"; "E_ad4_0"; "E_mg0"; "E_mk0"; "E_nm_0"; "E_vf5_0"; "E_vf6_0"; "E_vf7_0"; "E_vp0"; "R_mg"; "R_mk"; "T1_fail"; "T1_ok"; "T2_fail"; "T2_ok"; "T3_fail"; "T3_ok"; "T4_fail"; "T4_ok"; "T5_f"; "T5_ok"; "T5_z2G"; "T5_zG"; "T6_f"; "T6_ok"; "T6_z2G"; "T6_zG"; "T7_f"; "T7_ok"; "T7_z2G"; "T7_zG"; "T_mg"; "T_mk"; "T_pf"; "T_pgF"; "T_pkF"; "Tn_fail"; "Tn_ok"; "hse_fact"; "kb"; "s_vp"; "top_factG"; "top_factK"; "vHD"; "xf_vpcall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.VF"; "tv_vf"; "P_fail"; "P_ok"; "P_zero"; "P_zero2"; "am_vf"; "vHDn"; "vHDv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_eqs"; "isub_vf"; "s_vpH"; "hVP"; "isub_vp"; "isub_ad1"; "isub_ad2"; "isub_ad3"; "isub_ad4"; "isub_nm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bd_subst"; "bitem"; "@Stdlib.Lists.List"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_eqs.VFZ"; "CHz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.AD1"; "P_fail"; "P_ok"; "tv0"; "am_np"; "am_ok";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.AD2"; "P_fail"; "P_ok"; "tv0"; "am_np"; "am_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.AD3"; "P_fail"; "P_ok"; "tv0"; "am_np"; "am_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.AD4"; "P_fail"; "P_ok"; "tv0"; "am_np"; "am_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.NM"; "P_fail"; "P_ok"; "tv0"; "am_np"; "am_okc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.VP"; "P_push_fail"; "P_push_grown"; "P_push_keep"; "ndp0"; "ndpG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "vDn"; "vKn"; "kbytes"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require no.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve Lib_vec_push Lib_vec_finalize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_finalize_shape.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module VFZ. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o2.Lib_vec_finalizeZ. End VFZ.
Import RA.ReallocAddr AA.AAAddr VP.VPAddr VF.VFAddr FSAddr.

Lemma E_nm_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S8dS3cZ40A1A2SbS2S3dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Tn_ok0_eq : ltac2:(tb__ "0|0|
S0S2S1bS4fS3dS51S61Se5S78A6S77A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Tn_fail0_eq : ltac2:(tb__ "0|0|
S0S2S1bS4fS3dS51S61Se4S78A6S76A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Tn_ok_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S77S84A2SbS2SaeA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Tn_fail_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S76S84A2SbS2SadA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition isub_nm (L : axst) : wsub := ltac2:(tb__ "0|0|
ScbS51S4fVL;S3dA4").
Lemma imp_nm_ok : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSc6Se5A1M1Se6A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S0S17S16G1Se8A2S15S3bS12A2A3A2"). Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_nm_fail : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSc6Se4A1M1Se6A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S0S17S16G1Se7A2S15Sb4S13A2A3A2"). Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma E_ad1_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14Sc7S43S55A1S87A2S3cZ40A1A2SbS2S32A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T1_ok0_eq : ltac2:(tb__ "0|0|
S0S2S1bS4bS32S45S5dSd1S23S55A1A6S63A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T1_fail0_eq : ltac2:(tb__ "0|0|
S0S2S1bS4bS32S45S5dSd0S23S55A1A6S62A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T1_ok_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S63S28U1A1A2SbS2S95A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T1_fail_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S62S28U1A1A2SbS2S94A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition isub_ad1 (E : axst) (s : wsub) (L : axst) : wsub := ltac2:(tb__ "0|0|
ScbVs;S4bVL;VE;A4").
Lemma imp_ad1_ok : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSc2S32S45Sd1A3M1Sd2A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S0S17S16G1Sd4A2S15S3bS12A2A3A2"). Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_ad1_fail : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSc2S32S45Sd0A3M1Sd2A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S0S17S16G1Sd3A2S15S1dS13A2A3A2"). Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_ad2_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14Sc7S43S52A1S88A2S3cZ40A1A2SbS2S33A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T2_ok0_eq : ltac2:(tb__ "0|0|
S0S2S1bS4cS33S46S5eSd6S23S52A1A6S65A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T2_fail0_eq : ltac2:(tb__ "0|0|
S0S2S1bS4cS33S46S5eSd5S23S52A1A6S64A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T2_ok_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S65S28U2A1A2SbS2S97A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T2_fail_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S64S28U2A1A2SbS2S96A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition isub_ad2 (E : axst) (s : wsub) (L : axst) : wsub := ltac2:(tb__ "0|0|
ScbVs;S4cVL;VE;A4").
Lemma imp_ad2_ok : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSc3S33S46Sd6A3M1Sd7A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S0S17S16G1Sd9A2S15S3bS12A2A3A2"). Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_ad2_fail : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSc3S33S46Sd5A3M1Sd7A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S0S17S16G1Sd8A2S15S1dS13A2A3A2"). Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_ad3_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14Sc7S43S56A1S89A2S3cZ40A1A2SbS2S34A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T3_ok0_eq : ltac2:(tb__ "0|0|
S0S2S1bS4dS34S47S5fSdbS23S56A1A6S67A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T3_fail0_eq : ltac2:(tb__ "0|0|
S0S2S1bS4dS34S47S5fSdaS23S56A1A6S66A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T3_ok_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S67S28U3A1A2SbS2S99A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T3_fail_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S66S28U3A1A2SbS2S98A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition isub_ad3 (E : axst) (s : wsub) (L : axst) : wsub := ltac2:(tb__ "0|0|
ScbVs;S4dVL;VE;A4").
Lemma imp_ad3_ok : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSc4S34S47SdbA3M1SdcA2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S0S17S16G1SdeA2S15S3bS12A2A3A2"). Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_ad3_fail : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSc4S34S47SdaA3M1SdcA2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S0S17S16G1SddA2S15S1dS13A2A3A2"). Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_ad4_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14Sc7S43S57A1S8aA2S3cZ40A1A2SbS2S35A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T4_ok0_eq : ltac2:(tb__ "0|0|
S0S2S1bS4eS35S48S60Se0S23S57A1A6S69A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T4_fail0_eq : ltac2:(tb__ "0|0|
S0S2S1bS4eS35S48S60SdfS23S57A1A6S68A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T4_ok_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S69S28U4A1A2SbS2S9bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T4_fail_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S68S28U4A1A2SbS2S9aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition isub_ad4 (E : axst) (s : wsub) (L : axst) : wsub := ltac2:(tb__ "0|0|
ScbVs;S4eVL;VE;A4").
Lemma imp_ad4_ok : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSc5S35S48Se0A3M1Se1A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S0S17S16G1Se3A2S15S3bS12A2A3A2"). Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_ad4_fail : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSc5S35S48SdfA3M1Se1A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S0S17S16G1Se2A2S15S1dS13A2A3A2"). Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition isub_vf (E : axst) (s : wsub) (L : axst) : wsub := ltac2:(tb__ "0|0|
ScbVs;S1eVL;VE;A4").
Lemma E_vf5_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S8eS59UcZ270A2A2SbS2S20A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T5_z_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S1bS1eS20S24S3eSb9S1fS2eA1A6S30UcU5A2A2SbS2S6aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T5_z2_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S1bS1eS20S24S3eSbaS1fS2eA1A6S30UcU5A2A2SbS2S6bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T5_f_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S1bS1eS20S24S3eSb7S1fS2eA1A6S31UcU5A2A2SbS2S9cA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T5_ok_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S1bS1eS20S24S3eSb8S1fS2eA1A6S31UcU5A2A2SbS2S9dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf5_z : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSbeS20S24Sb9A3M1Sb6A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S1S0S17S16G1SbbA2S15S1dS12A2A3S0SeSc9A1Sc8G1ScdA2S2aS2eS7dA2A3A2A2"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf5_z2 : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSbeS20S24SbaA3M1Sb6A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S1S0S17S16G1SbbA2S15S1dS12A2A3S0SeSc9A1Sc8G1ScdA2S2aS2eS7dA2A3A2A2"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf5_f : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSbeS20S24Sb7A3M1Sb6A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S0S17S16G1S15SbdS13A2A2S15S1dS13A2A3A2"). Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf5_ok : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSbeS20S24Sb8A3M1Sb6A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S0S17S16G1S15SbcS12A2A2S15S53S12A2A3A2"). Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T5_zG_eq : ltac2:(tb__ "0|0|
S0S2Sc7SdS8S2cSfS8A1A3S6aA2S9fA3"). Proof. reflexivity. Qed.
Lemma T5_z2G_eq : ltac2:(tb__ "0|0|
S0S2Sc7SdS8S2cSfS8A1A3S6bA2S9eA3"). Proof. reflexivity. Qed.
Lemma E_vf6_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S8fS59UdZ290A2A2SbS2S21A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T6_z_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S1bS1eS21S25S3fSb9S1fS2dA1A6S30UdU6A2A2SbS2S6cA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T6_z2_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S1bS1eS21S25S3fSbaS1fS2dA1A6S30UdU6A2A2SbS2S6dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T6_f_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S1bS1eS21S25S3fSb7S1fS2dA1A6S31UdU6A2A2SbS2Sa0A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T6_ok_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S1bS1eS21S25S3fSb8S1fS2dA1A6S31UdU6A2A2SbS2Sa1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf6_z : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSbeS21S25Sb9A3M1Sb6A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S1S0S17S16G1SbbA2S15S1dS12A2A3S0SeSc9A1Sc8G1ScdA2S2aS2dS7cA2A3A2A2"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf6_z2 : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSbeS21S25SbaA3M1Sb6A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S1S0S17S16G1SbbA2S15S1dS12A2A3S0SeSc9A1Sc8G1ScdA2S2aS2dS7cA2A3A2A2"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf6_f : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSbeS21S25Sb7A3M1Sb6A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S0S17S16G1S15SbdS13A2A2S15S1dS13A2A3A2"). Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf6_ok : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSbeS21S25Sb8A3M1Sb6A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S0S17S16G1S15SbcS12A2A2S15S53S12A2A3A2"). Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T6_zG_eq : ltac2:(tb__ "0|0|
S0S2Sc7SdS8S2cSfS8A1A3S6cA2Sa3A3"). Proof. reflexivity. Qed.
Lemma T6_z2G_eq : ltac2:(tb__ "0|0|
S0S2Sc7SdS8S2cSfS8A1A3S6dA2Sa2A3"). Proof. reflexivity. Qed.
Lemma E_vf7_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S90S59UeZ2b0A2A2SbS2S22A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T7_z_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S1bS1eS22S26S40Sb9S1fS2fA1A6S30UeU7A2A2SbS2S6eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T7_z2_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S1bS1eS22S26S40SbaS1fS2fA1A6S30UeU7A2A2SbS2S6fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T7_f_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S1bS1eS22S26S40Sb7S1fS2fA1A6S31UeU7A2A2SbS2Sa4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T7_ok_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S1bS1eS22S26S40Sb8S1fS2fA1A6S31UeU7A2A2SbS2Sa5A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf7_z : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSbeS22S26Sb9A3M1Sb6A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S1S0S17S16G1SbbA2S15S1dS12A2A3S0SeSc9A1Sc8G1ScdA2S2aS2fS7eA2A3A2A2"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf7_z2 : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSbeS22S26SbaA3M1Sb6A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S1S0S17S16G1SbbA2S15S1dS12A2A3S0SeSc9A1Sc8G1ScdA2S2aS2fS7eA2A3A2A2"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf7_f : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSbeS22S26Sb7A3M1Sb6A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S0S17S16G1S15SbdS13A2A2S15S1dS13A2A3A2"). Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf7_ok : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSbeS22S26Sb8A3M1Sb6A2SdG0S11S5S5S1cS7Z40A1A4SfG0A1A3A3S0S17S16G1S15SbcS12A2A2S15S53S12A2A3A2"). Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T7_zG_eq : ltac2:(tb__ "0|0|
S0S2Sc7SdS8S2cSfS8A1A3S6eA2Sa7A3"). Proof. reflexivity. Qed.
Lemma T7_z2G_eq : ltac2:(tb__ "0|0|
S0S2Sc7SdS8S2cSfS8A1A3S6fA2Sa6A3"). Proof. reflexivity. Qed.

Definition hVP : positive := 98%positive.
Definition s_vpH : wsub := ltac2:(tb__ "0|0|
SdS10ScfS5A2S11ScfS5Sc0S1dA4Sb1A3").
Lemma E_vp_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S91Sb5A2SbS2S2bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R_vp_eqH : ltac2:(tb__ "0|1|
S0ScSeS6A1M0A1SccS2bS38SbfA3SbG0S41A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pk0_eqH : ltac2:(tb__ "0|0|
S0S2S1bS38S2bSbfS41SebS50A6S75A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pf0_eqH : ltac2:(tb__ "0|0|
S0S2S1bS38S2bSbfS41Se9S50A6S71A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pg0_eqH : ltac2:(tb__ "0|0|
S0S2S1bS38S2bSbfS41SeaS50A6S73A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pk_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S75S58A2SbS2S74A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pf_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S71S58A2SbS2SaaA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pg_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S73S58A2SbS2S72A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pkF_eq : ltac2:(tb__ "0|0|
S0S2Sc7SdS8SafSdS8Sb3SfS8A1A3A3S74A2SacA3"). Proof. reflexivity. Qed.
Lemma T_pgF_eq : ltac2:(tb__ "0|0|
S0S2Sc7SdS8Sb2SfS8A1A3S72A2SabA3"). Proof. reflexivity. Qed.
Definition isub_vp (L : axst) : wsub := ltac2:(tb__ "0|0|
ScbSbfS38VL;S2bA4").
Lemma imp_vp_keep : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSc1SebA1M1S19SecA1A2SdG0S79S83A1SfG0A1A3A3S1S0SeSc9A1Sc8G1S18SecA1A2S7aS80S81A2A3S0S17S16G1S15SaSc0A1S12A2A2S15S1dS12A2A3A2A2").
Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vp_fail : ltac2:(tb__ "0|2|
S1S0SeS10S5S5A2M0A1S1aSc1Se9A1M1Sf1A2SdG0S79S83A1SfG0A1A3A3S0S17S16G1S15SaSc0A1S12A2A2S15S1dS12A2A3A2").
Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vp_grown : ltac2:(tb__ "0|3|
S1S0SeS10S5S5A2M0A1S1aSc1SeaA1M1SdG0S11S5S5SeeSf0SefA1A4SfG0A1M2A3A2SdG0S11S5S5S27Sb0Z80S54A2A4G2A3A3S1S0SeSc9A1Sc8G1S18SedSeeSefA2A1A2S7aS80S54A2A3S0S17S16G1S15SaSc0A1S12A2A2S15S1dS12A2A3A2A2").
Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma E_mk1_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S8cS86A2SbS2S37A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_mk_eq : ltac2:(tb__ "0|0|
S0S2S5aS37S29A2S4aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nth31_mk1 : ltac2:(tb__ "0|0|
S0ScS6A1ScaS6S9S3S37A1A1U1fA3SbS6S44S29A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nth1_mk2 : ltac2:(tb__ "0|0|
S0ScS6A1ScaS6S9S3S4S37SceS3S37A1U1fS42S29A1A3A2A1A1U1A3SbS6S7bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mk0_eq : ltac2:(tb__ "0|0|
S0S2Sf2S5cS4aS7fS4aS29S81A3S93S5bA5S3aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nth1_Tmk0 : ltac2:(tb__ "0|0|
S0ScS6A1ScaS6S9S3S3aA1A1U1A3SbS6S42S29A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nth2_Tmk1 : ltac2:(tb__ "0|0|
S0ScS6A1ScaS6S9S3S4S3aSceS3S3aA1U1S44S29A1A3A2A1A1U2A3SbS6S82A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mk_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S70S3aS29A2S85A2SbS2Sa9A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_mg1_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S8bS86A2SbS2S36A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_mg_eq : ltac2:(tb__ "0|0|
S0S2S5aS36S27A2S49A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nth31_mg1 : ltac2:(tb__ "0|0|
S0ScS6A1ScaS6S9S3S36A1A1U1fA3SbS6S44S27A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nth1_mg2 : ltac2:(tb__ "0|0|
S0ScS6A1ScaS6S9S3S4S36SceS3S36A1U1fS42S27A1A3A2A1A1U1A3SbS6S7bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mg0_eq : ltac2:(tb__ "0|0|
S0S2Sf2S5cS49S7fS49S27S54A3S92S5bA5S39A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nth1_Tmg0 : ltac2:(tb__ "0|0|
S0ScS6A1ScaS6S9S3S39A1A1U1A3SbS6S42S27A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nth2_Tmg1 : ltac2:(tb__ "0|0|
S0ScS6A1ScaS6S9S3S4S39SceS3S39A1U1S44S27A1A3A2A1A1U2A3SbS6S82A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mg_eq : ltac2:(tb__ "0|0|
S0ScS2A1S14S70S39S27A2S85A2SbS2Sa8A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_finalize_shape_eqs.

(* [comment removed for export] *)
Module Lib_finalize_shape_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SPUle"; "SVar"; "SLit"; "SAlu"; "SMd"; "@Corelib.Init.Datatypes"; "cons"; "app"; "bool"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "edescA"; "ejcertA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape"; "NP"; "cutsE"; "exitsE"; "FUEL_fs"; "cutsC"; "@Corelib.Init.Logic"; "eq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_chk"; "H_ejcert_fs_ok"; "keep_ejcert_fs_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA"; "hideE"; "hide_setE"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require no.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve Lib_vec_push Lib_vec_finalize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_finalize_shape.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import RA.ReallocAddr FSAddr.

Definition keep_ejcert_fs_ok : list sprop := ltac2:(tb__ "0|d|
S6S0S1S2PcA1S3Z800000000000A1M0A2S6S0S1S2P66A1S2P1eA1M1A2S6S0S1S2P6aA1S3Z1A1A2S6S0S1S2P72A1S2P73A1M2A2S6S0S1G2S3ZffffffffA1M3A2S6S0S1S2P75A1S2P76A1M4A2S6S0S1G4G3A2S6S0S1S2P78A1S2P79A1M5A2S6S0S1G5G3A2S6S0S1S2P7bA1S2P7cA1M6A2S6S0S1G6G3A2S6S0S1S2P7eA1S2P7fA1M7A2S6S0S1G7G3A2S6S0S1S2P81A1S2P82A1M8A2S6S0S1G8G3A2S6S0S1S2P84A1S2P85A1M9A2S6S0S1G9G3A2S6S0S1S4S14S2P6eA1MaS5S15S3Z80A1S2P70A1MbA3McA3G1A2S6S0S1GaG0A2S6S0S1GbG3A2S6S0S1GcG3A2S9S0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition H_ejcert_fs_ok : list sprop := ltac2:(tb__ "0|0|
S1aS18S7SbSfS10A3A2").
Lemma ejcert_fs_ok : ltac2:(tb__ "0|1|
S13S8ScS16SeS11S12SeSdSbSbS19S17A1M0SfA4SdSbSbG0S10A4A7SaA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_finalize_shape_chk.

(* [comment removed for export] *)
Module Lib_finalize_shape_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "prod"; "pair"; "app"; "S"; "Some"; "cons"; "nil"; "option"; "false"; "andb"; "nat"; "fst"; "None"; "snd"; "orb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "valuation"; "ss_facts"; "sprop_eqb"; "SPUle"; "SLit"; "ss_next"; "sobj"; "ss_objs"; "SAlu"; "holds"; "sv_eqb"; "SPBranch"; "SPNot"; "SVar"; "obj_range"; "obj_wf"; "soff"; "sprop_below"; "ob_base"; "ob_hi"; "ob_lo"; "rw"; "cell"; "mkObj"; "odefault"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "entailsA"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "pow"; "lt"; "leb"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "AHead"; "am_subst"; "NDA"; "amode"; "JA_pre"; "nd_below"; "am_eqb"; "tvinA"; "nd_bd"; "nd_tv"; "emeasA"; "TPA"; "ffinA"; "frinA"; "ANone"; "JA"; "JLA"; "fbinA"; "nd_am"; "nd_fr"; "nodeIA"; "ok_frameKA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.Lists.List"; "existsb"; "In"; "nth_error"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "uval"; "bd_subst"; "BXok_d"; "bxt"; "bd_below"; "bd_wpos"; "AMin"; "aval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape"; "NP"; "vd_c"; "vdesc"; "vd_k"; "CHfrom"; "cs0"; "vB"; "Xk_fin"; "vHq"; "cutsE"; "kb"; "z0"; "CHf"; "sh_c"; "tv0"; "two47"; "B32"; "ndTz"; "s_gh"; "go_facts"; "sh_k"; "Pre_vf"; "fins"; "vHa"; "vd_el"; "xf_back_fin"; "Pre_ad1"; "Pre_ad2"; "Pre_ad3"; "Pre_ad4"; "Xk_vf"; "vAR"; "bd_push"; "ndTf"; "ndTok"; "vd_d"; "L_mc"; "PD_vp"; "Pre_mc"; "Xof"; "nd_fail_f"; "s_m"; "xf_call"; "PD_vf"; "Pre_vp"; "dst_obj"; "mid_obj"; "ndE"; "vAL"; "vd_off"; "P_fail"; "P_failz"; "P_nop"; "P_ok"; "Pre_fs"; "bofs"; "finK"; "finV"; "fmid_obj"; "nd0"; "ndPf"; "nd_nop"; "nd_ok"; "slotx"; "src_obj"; "vHv"; "vLC"; "vLI"; "vPI"; "xf_back_vf"; "xf_back_vfk"; "E_ad1_0"; "E_ad2_0"; "E_ad3_0"; "E_ad4_0"; "E_mc"; "E_mg0"; "E_mk0"; "E_nm_0"; "E_vf5_0"; "E_vf6_0"; "E_vf7_0"; "E_vp0"; "FL_50"; "FL_51"; "FL_60"; "FL_61"; "FL_70"; "FL_71"; "FL_E0"; "FL_E1"; "FL_p0"; "FL_p1"; "Pre_nm"; "T_mc1"; "eC"; "exitsE"; "ghZ"; "nd1"; "nd2"; "nd3"; "nd4"; "nd5"; "nd6"; "nd7"; "nd8"; "ndPg"; "ndPk"; "qHD"; "spm"; "vSH"; "xf_mback"; "xf_mcall"; "xf_vfcall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_pf.Sum"; "keptF"; "JLf"; "Posts_fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkPA"; "entails_frA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_pf"; "P0_fs"; "fr_obj"; "fr_xr"; "lit_in"; "boff"; "img_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb";
"tvz"; "tvd"; "T_ok"; "FBx"; "tnz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "PostsC"; "pd_okA"; "pdescA"; "xrs_inclb"; "FFx"; "pclMA"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "rho_absorb"; "rho_sub"; "wsub_id_below"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "BC_EQ"; "mulop"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_pf.VPP"; "P0_vp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "xrs_checkL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "wsub_dom_below"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_eqs"; "hVP"; "isub_vf"; "isub_ad1"; "isub_ad2"; "isub_ad3"; "isub_ad4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "payA"; "T_afterA"; "cmaddrA"; "robjs_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.VF"; "tv_vf"; "am_vf"; "P_fail"; "P_ok"; "P_zero"; "P_zero2"; "vHDn"; "vHDv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_pay2"; "bud_le2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.AD1"; "tv0"; "P_fail"; "P_ok"; "CH"; "ahd"; "am_np"; "am_ok"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.AD2"; "tv0"; "P_fail"; "P_ok"; "CH"; "ahd"; "am_np"; "am_ok"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.AD3"; "tv0"; "P_fail"; "P_ok"; "CH"; "ahd"; "am_np"; "am_ok"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.AD4"; "tv0"; "P_fail"; "P_ok"; "CH"; "ahd"; "am_np"; "am_ok"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.VP"; "ndp0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_pf.ADP1"; "PD_ad"; "P0_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_pf.ADP2"; "PD_ad"; "P0_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_pf.ADP3"; "PD_ad"; "P0_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_pf.ADP4"; "PD_ad"; "P0_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_pf.Sum.X"; "slotF"; "spF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_pf.VFZ"; "CHz"; "nd0z";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH"; "PDh"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_pf.NMP"; "P0_aa"; "PD_aa"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_pf.VFP"; "P0_vf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_pure"; "J_memcpy_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape.NM"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require no.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve Lib_vec_push Lib_vec_finalize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require no.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_finalize_shape.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_finalize_shape OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module VFZ. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o2.Lib_vec_finalizeZ. End VFZ.
Import RA.ReallocAddr AA.AAAddr VP.VPAddr VF.VFAddr FSAddr.
Module ADP1. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_finalize_shape_dup1_pf. End ADP1. Module ADP2. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_finalize_shape_dup2_pf. End ADP2. Module ADP3. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_dup3_pf. End ADP3. Module ADP4. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_finalize_shape_dup4_pf. End ADP4.
Module NMP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_finalize_shape_name_pf. End NMP.
Module VPP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o8.Lib_vec_push_pf. End VPP.
Module VFP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Lib_vec_finalize_pf. End VFP.

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd];
  repeat match goal with |- context [bv_unsigned (eval ?r z0)] => change (bv_unsigned (eval r z0)) with (uval r (SLit 0)); rewrite (uval_lit r 0) by lia end; lia.
Lemma emeas_z0 : ltac2:(tb__ "0|0|
S33S40S15S1aS0S15S4cS7S6S33S40A2S6S15S18A2S7S33S40R4R3A4S7S15S18R2S75A4A4R1A2S3bR2S3cZ2Z40A2A2A3Frho;Fr;Fnd;FT;").
Proof. intros T nd r rho. unfold emeasA. cbn [eda_rank eda_var fst snd]. change (bv_unsigned (eval rho z0)) with (uval rho (SLit 0)). rewrite uval_lit by lia. lia. Qed.

Lemma edesc_eq3 : ltac2:(tb__ "0|2|
S33S33S40S40S6S15S18A2M0G0S0S6S6S33S40A2M1G0A2S7G1G0S7S33S40R6R4A4R2A4S7G1G0S7S33S40R5R3A4R1A4A3S1S0S33R7R6A3S1S0S40R5R4A3S0G0R3R2A3A2A2F_;Fc';Fc;Fb';Fb;Fa';Fa;").
Proof. intros a a' b b' c c' H. injection H as E1 E2 E3. subst. auto. Qed.
Lemma edesc_eq2 : ltac2:(tb__ "0|0|
S33S33S40S40S0S6S33S40A2S7S33S40R4R2A4S7S33S40R3R1A4A3S1S0S33R5R4A3S0S40R3R2A3A2F_;Fb';Fb;Fa';Fa;").
Proof. intros a a' b b' H. injection H as E1 E2. subst. auto. Qed.

Definition P0_fs (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S1S131VFF;S59Q40M0S2fVr;PcA2A2Z518A3S131VFF;S59G0S2fVr;P64A2A2Z30A3A2").

Definition lit_in (lo hi : sv) (n : Z) : bool := ltac2:(tb__ "0|6|
S18S4Llo;Vlo;S15S18S4Lhi;Vhi;S15SfSfS3eZ0R2A2S3eR2R1A2A2S3eR1Vn;A2A2Lh;S16SeLi;M0S104S18S18SeLb;La;M1Lop;M2G2S106G1Lop;M3G3S4S17S18SeLa;Lw;Lsgn;M4S16S18S15SeLk;Li;M5Ll0;X18x8Ll;G0G2G2G3G3G4S16G5Ll;X18x8").
Definition fr_obj (o : sobj) : bool := ltac2:(tb__ "0|3|
S14SfS24S2cVo;A1M0S70A2Se9S2eVo;A1M1S2dVo;A1M2Z518A3A2SfS24G0S9aA2Se9G1G2Z30A3A2A2").

Definition boff (e : sv) : option Z := ltac2:(tb__ "0|b|
S4SdS15A1M0L_;M1S24Ve;S70A2SaS15Z0A2S18G0Le;Ve;S15S12S15A1M2Lz;S16G2Li;M3S104S18S18S104G0Lop;R3S18G0Lb;R1S15G1S24R3S70A2SaS15R1A2G2X4x2Lk;G3S104S18S18G2Lb0;La;M4Lop0;M5G5S106G4Lop0;M6G6S4S17S18G2La;Lw;Lsgn;M7S16S18S15G2Lk;Li;Ll;M8X18x8G2G2G2G2G2G2G2G2G2X104xaLb;Le1;Lop;S104S18S18G2Lb;La;M9Lop;S106G9Lop;MaGaG7G8X18x8X4x2").
Definition fr_xr (r : sv * sv) : bool := ltac2:(tb__ "0|6|
S18S4Lx;S13S18S18Vr;A3S15SdS15A1S4Lx;SeaS11S18S18Vr;A3M0A1S15SfSfS3eZ0M1R1A2M2S3eG1R2A2A2S3eS3aR1R2A2Z518A2A2Lk;SfSfS24G0S9aA2G2A2S3eR1Z30A2A2Xdx2Ln;S16SeLi;S104S18S18SeLb;La;M3Lop;M4G4S106G3Lop;M5G5S4S17S18SeLa;Lw;Lsgn;S16S18S15SeLk;Li;Ll;X18x8").
Lemma boff_sound : ltac2:(tb__ "0|0|
S1aS18S15S0SdS15A1SeaR2A1SaS15R1A2A3S1S39Z0R2A2S39R2Z518A2A2S39S5fR5S70A2S79A2S0S15S5fR6R5A2S3aS5fR6S70A2R4A2A3F_;F_;F_;Fk;Fe;Frho;").
Proof.
  intros rho e k H Hk Hb. unfold two47, RA.two47 in Hb. unfold boff in H.
  destruct (sv_eqb e vB) eqn:E0.
  - apply sv_eqb_sound in E0. subst e. injection H as <-. lia.
  - destruct e as [| |op e1 e2| | | | |]; try discriminate. destruct op; try discriminate. destruct e2 as [|z| | | | | |]; try discriminate.
    destruct (sv_eqb e1 vB) eqn:E1; [|discriminate]. apply sv_eqb_sound in E1. subst e1. injection H as <-.
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity.
Qed.

Definition img_obj (o : sobj) : bool := ltac2:(tb__ "0|8|
SfS24S2cVo;A1S1eZ0M0A1A2S18S4Lx;M1S2eVo;A1S15G1S2dVo;A1S15SfSfS3eG0R2A2S3eR2R1A2A2S3eR1S132A2A2Lh;S16SeLi;M2S104S18S18SeLb;La;M3Lop;M4G4S106G3Lop;M5G5S4S17S18SeLa;Lw;Lsgn;M6S16S18S15SeLk;Li;M7Ll0;X18x8Ll;G2G4G4G5G5G6S16G7Ll;X18x8A2").

Lemma lit_in_sound : ltac2:(tb__ "0|2|
S1aS18S18S18S15S15S5S30A1S32S3dR4S3cZ2Z3eA2A2S0S4Se9R7R6R5A3S3A3S1S39S11S15S15S28RaS31R9R8R7R4R3A5A2M0A3R5A2S3dR5S13S15S15G0A3A2A2S1S39S5fRbRaA2M1R6A2S3dR6S3aG1R7A2A2A2F_;F_;F_;Fdflt;Fcells;Fa;Fn;Fhi;Flo;Fbase;Frho;").
Proof.
  intros rho base lo hi n a cells dflt Hn H Hr. unfold lit_in in H.
  destruct lo as [l| | | | | | |]; try discriminate. destruct hi as [h| | | | | | |]; try discriminate.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite (soff_lit_small rho l), (soff_lit_small rho h) in Hr by lia. unfold uval. lia.
Qed.
Lemma img_obj_sound : ltac2:(tb__ "0|1|
S1aS20S15S0S4SebR2A1S3A3S1S39S11S15S15S28R4R3A2M0A3R2A2S3dR2S13S15S15G0A3A2A2S1S39Z0R3A2S3dR3S132A2A2F_;F_;Fa;Fo;Frho;").
Proof.
  intros rho [base lo hi cells dflt] a H Hr. unfold img_obj in H. cbn [ob_base ob_lo ob_hi] in H. apply andb_prop in H as [Hb H].
  apply sv_eqb_sound in Hb. subst base.
  destruct lo as [l| | | | | | |]; try discriminate. destruct hi as [h| | | | | | |]; try discriminate.
  apply andb_prop in H as [H H2]. apply andb_prop in H as [H1 H3]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr. unfold IMG_HI in *.
  rewrite (soff_lit_small rho l), (soff_lit_small rho h) in Hr by lia. rewrite U_lit in Hr. change (0 mod M64v) with 0 in Hr. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S110S1aS5S58Q40A1A1S107OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S16eS38VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S15S16fVCST;R1A2S1S39Z0R2A2S3dR2S132A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S15S16fVXGL;R1A2S1S39Z0R2A2S3dR2S132A2A2F_;Fa;").
Hypothesis HTOP : InitState.segs_top segs <= IMG_HI.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S5S6S6S15S15A2S15A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 5 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.

Definition JLf (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S52VAInv;VCST;VXGL;VKc;Se6VFB;VFF;A2VFB;VFF;VBX;S41Vnd;Aa").
Definition Posts_fs : list (axst * jpostA) := ltac2:(tb__ "0|2|
SbS6S33Se1A2M0S7S33Se1S9eSdfSa7A1A4SbG0S7S33Se1S9fSdfSa8A1A4SbG0S7S33Se1S9cSdfS92A1M1A4SbG0S7S33Se1S9dG1A4ScG0A1A3A3A3A3").
Definition PD_fs : list (axst * ndesc) := ltac2:(tb__ "0|1|
SbS6S33S40A2M0S7S33S40S9eSa7A4SbG0S7S33S40S9fSa8A4SbG0S7S33S40S9cS92A4SbG0S7S33S40S9dS92A4ScG0A1A3A3A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S51VAInv;VCST;VXGL;S6aVKc;Vrho0;Se6VFB;VFF;A2VFB;VFF;VBX;S41Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S6S33S40A2S11eFn;") := ltac2:(tb__ "0|0|
S56VAInv;VCST;VXGL;S6aVKc;Vrho0;Se6VFB;VFF;A2VFB;VFF;VBX;S41Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Se2S38S6aVrho0;Vtp0;Se0A5").

Lemma P0_now : ltac2:(tb__ "0|0|
S1aS10dS6aVrho0;R1A3Se6VFB;VFF;Vrho0;A3S1S131VFF;S5fR3S70A2Z518A3S131VFF;S5fR3S9aA2Z30A3A2F_;F_;Frho;").
Proof.
  intros rho Hav [H1 H2]. unfold uval, vB, vAL. cbn [eval].
  rewrite <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 100%positive eq_refl). split; [exact H1 | exact H2].
Qed.

Lemma fr_obj_pclMA : ltac2:(tb__ "0|1|
S1aS20S15S5S6S15S15A2A1S10dS6aVrho0;R4A3Se6VFB;VFF;Vrho0;A3S0S4Se7R5A1S3A3S1S39S11S15S15S28R7R6A2M0A3R5A2S3dR5S13S15S15G0A3A2A2Sf9VCST;Vrho0;R5Sf8VFF;R8ScS6S6S18S15A2S18A2A1A3R6A5F_;F_;F_;F_;FFBc;Fa;Fo;Frho;").
Proof.
  intros rho [base lo hi cells dflt] a FBc Hav HP0 H Hr. destruct (P0_now rho Hav HP0) as [PB PA].
  unfold fr_obj in H. cbn [ob_base ob_lo ob_hi] in H. apply orb_prop in H as [H|H]; apply andb_prop in H as [Hb Hl]; apply sv_eqb_sound in Hb; subst base.
  - eapply (infrFF_pclMA CST _ FF); [exact PB | exact (lit_in_sound rho vB lo hi 1304 a cells dflt ltac:(lia) Hl Hr)].
  - eapply (infrFF_pclMA CST _ FF); [exact PA | exact (lit_in_sound rho vAL lo hi 48 a cells dflt ltac:(lia) Hl Hr)].
Qed.
Lemma fr_obj_cmaddrA : ltac2:(tb__ "0|1|
S110S1aSdS15A1S20S15S10dS6aVrho0;R4A3Se6VFB;VFF;Vrho0;A3S4eVFF;R7A2S0S4Se7R5A1S3A3S1S39S11S15S15S28R8R6A2M0A3R5A2S3dR5S13S15S15G0A3A2A2S123VCST;RaR8R6A4F_;F_;F_;F_;F_;Fa;Fo;Fxo;Frho;FAi;").
Proof.
  intros Ai rho xo [base lo hi cells dflt] a Hav HP0 HFF H Hr. destruct (P0_now rho Hav HP0) as [PB PA].
  unfold fr_obj in H. cbn [ob_base ob_lo ob_hi] in H. apply orb_prop in H as [H|H]; apply andb_prop in H as [Hb Hl]; apply sv_eqb_sound in Hb; subst base.
  - eapply (infrFF_cmaddrA CST FF); [exact HFF | exact PB | exact (lit_in_sound rho vB lo hi 1304 a cells dflt ltac:(lia) Hl Hr)].
  - eapply (infrFF_cmaddrA CST FF); [exact HFF | exact PA | exact (lit_in_sound rho vAL lo hi 48 a cells dflt ltac:(lia) Hl Hr)].
Qed.
Lemma fr_xr_pclMA : ltac2:(tb__ "0|1|
S1aS6S18S18A2S15S5S6S15S15A2A1S10dS6aVrho0;R4A3Se6VFB;VFF;Vrho0;A3S39S5fR6S70A2S79A2S0S4Se8R6A1S3A3S1S39S5fR8S11S18S18R7A3A2M0R6A2S3dR6S3aG0S5fR8S13S18S18R7A3A2A2A2A2Sf9VCST;Vrho0;R6Sf8VFF;R9ScS6S6S18S15A2S18A2A1A3R7A5F_;F_;F_;F_;F_;FFBc;Fa;Fr;Frho;").
Proof.
  intros rho [rb rn] a FBc Hav HP0 Hb H Ha. destruct (P0_now rho Hav HP0) as [PB PA].
  unfold fr_xr in H. cbn [fst snd] in H, Ha. destruct rn as [|n| | | | | |]; try discriminate.
  destruct (boff rb) as [k|] eqn:EB.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    rewrite uval_lit in Ha by lia. rewrite (boff_sound rho rb k EB ltac:(lia) Hb) in Ha. eapply (infrFF_pclMA CST _ FF); [exact PB | lia].
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply sv_eqb_sound in H1. subst rb.
    apply Z.leb_le in H2. apply Z.leb_le in H3. rewrite uval_lit in Ha by lia. eapply (infrFF_pclMA CST _ FF); [exact PA | lia].
Qed.

Lemma d_live : ltac2:(tb__ "0|0|
S40S1aS5S58Q40A1A1S5S108A1S107S18S15S18S18VJAv;R9R8R7R6R5A5S5bS6S18S18A2S7S18S18R5S74R4R2A2A4S4bRaA1A3S1S39Z1R5A2S39R5Z80A2A2S39S5fRbR4A2S7aA2S39S5fRcR6A2S5fRcR5A2A2S2S0S15S5fRdR7A2Z0A3A1Sf2ReS7S18S18RaS74R9R7A2A4A2F_;F_;F_;F_;F_;F_;Fk;Fc;Fe;Fd;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof.
  intros nd rho tp tr md d e c k HJ Hin He Hk Hck Hc Hd.
  pose proof (JA_null_size0 AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue nd rho tp tr md (d, kb e k) HJ Hin Hd) as Z0.
  cbn [snd] in Z0. change (bv_unsigned (eval rho (kb e k))) with (uval rho (kb e k)) in Z0.
  unfold kb, B32, Lib_vec_reserve.B32 in *. pose proof (uval_range rho k). pose proof (uval_range rho c). rewrite uval_mul_lit in Z0 by nia. assert (uval rho k = 0) by nia. lia.
Qed.

Lemma JA_tv_swap : ltac2:(tb__ "0|2|
S5S6S18S18A2M0A1G0G0S5S6S6S18S15A2S18A2A1S5S5eA1S45S1aS5S58Q40A1A1S5S108A1S107VJAv;S44S8G0RaSbG0R9SbG0R8ScG0A1M1A3A3A3R7R6R5A4R4R3R2R1A5VJAv;S44S8G0RbSbG0R9SbG0RaG1A3A3A3R8R7R6A4R5R4R3R2A5F_;Fmd;Ftr;Ftp;Frho;Fam;Fbd;Ffr;Fy;Fx;Fl;").
Proof.
  intros l x y fr bd am rho tp tr md (Ai & kc & HJ). exists Ai, kc.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU |- *.
  assert (PERM : forall t, In t (l ++ [y; x]) <-> In t (l ++ [x; y])).
  { intros t. rewrite !in_app_iff. cbn. tauto. }
  assert (HCNT : cntS rho (l ++ [x; y]) <= cntS rho (l ++ [y; x])) by (rewrite !cntS_app, !cntS_cons; lia).
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [|split; [exact HFR|split; [exact HK0|split; [exact HP0|split; [|split; [exact HBU|exact (JA_tail_le _ _ _ rho rho _ _ HCNT HPA)]]]]]].
  - split; [|split].
    + unfold tvinA in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HN). apply PERM. exact Ht.
    + cbn [nd_tv]. pose proof (tvd_app_l rho _ _ HD) as D1. pose proof (tvd_app_r rho _ _ HD) as D2. pose proof (tvd_app_cross rho l [x; y]) as D3.
      apply tvd_app; [exact D1 | |].
      * cbn in D2 |- *. destruct D2 as [Dxy _]. split; [|split; [intros t' [] | exact I]].
        intros t' [<-|[]] Hy Hx E0. apply (Dxy y ltac:(left; reflexivity) Hx Hy). symmetry. exact E0.
      * intros t t' Ht Ht' Hnz Hnz'. apply (D3 t t' HD Ht); [cbn in Ht' |- *; tauto | exact Hnz | exact Hnz'].
    + unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply PERM. exact Ht.
  - unfold XA in *. eapply (proj1 (XAz_transport FB FB _ Ai Ai (rm rho) (rm rho) (tvals rho (l ++ [x; y])) (tvals rho (l ++ [y; x])) kc HXA _ _ _ _)).
    Unshelve.
    + intros b n Hin Hnf Hut. split; [exact Hin|]. split; [exact Hnf|]. intros v Hv. apply Hut. unfold tvals in *. apply in_map_iff in Hv as (t & <- & Ht). apply in_map. apply PERM. exact Ht.
    + intros; reflexivity.
    + intros; split; [reflexivity | auto].
    +
      intros bn H1 _ H3 H4. split; [exact H1|]. split; [exact H3|]. intros v Hv. apply H4. unfold tvals in *. apply in_map_iff in Hv as (t & <- & Ht). apply in_map. apply PERM. exact Ht.
Qed.
Lemma SPA_tv_swap : ltac2:(tb__ "0|2|
S5S6S18S18A2M0A1G0G0S5S6S6S18S15A2S18A2A1S5S5eA1S45S33S1aS5S58Q40A1A1S11cS67S38VJAv;S44S8G0RaSbG0R9SbG0R8ScG0A1M1A3A3A3R7R6R5A4A1R4R3R2R1A6S67S38VJAv;S44S8G0RbSbG0R9SbG0RaG1A3A3A3R8R7R6A4A1R5R4R3R2A6F_;Fw;Ftp;Frho;FA;Fam;Fbd;Ffr;Fy;Fx;Fl;").
Proof. intros l x y fr bd am A rho tp [tr [ms md]] [Hsm HJ]. split; [exact Hsm|]. apply JA_tv_swap. exact HJ. Qed.

Lemma eC_val : ltac2:(tb__ "0|1|
S1aS6cS18S1S39Z1S82R2A1M0A2S39G0Z80A2A2S39S5fR4R2A2S7aA2S0S15S5fR5Sc9R4R3A2A2S3bS82R4A1S5fR5R3A2A2A3F_;F_;Fc;Fv;Frho;").
Proof.
  intros rho v c He Hc. unfold eC, B32, Lib_vec_reserve.B32 in *. pose proof (uval_range rho c).
  apply uval_mul_lit; nia.
Qed.

Lemma amin1_rng : ltac2:(tb__ "0|3|
S1aS18S1S39Z0M0S66R2S65R1Z1M1G0G1A4A2M2A2S39G2G1A2A2Fe;Fr;").
Proof. intros r e. cbn [aval]. lia. Qed.
Lemma pay_fin : ltac2:(tb__ "0|3|
S10S6cS5S19A1S5S5eA1S0SdS6cA1S5cS6cS80R4A3SaS6cR3A2A3S0S4S64R2A1S3A3S0S4S5aS19S1cS1dS6bR5A1S6dR5A1A2A1R4A3S3A3S0S4S5aS19S1cS1dS6dR6A1S1eS7aA1A2A1R5A3S3A3S121S6aVrho0;Se6VFB;VFF;A2R6S1eZ0M0A1G0S8S5eSbS5eSa3R8A1SbS5eSa2R8A1ScS5eA1M1A3A3R5A3S8S5eS76R7S6bR7A1A2S8S5eSbS5eSa3S9R8A1M2A1SbS5eSa2G2A1G1A3A3R5A3A3A8F_;F_;F_;F_;Frest;Ffacts;Fv;Fj;").
Proof.
  intros j v facts rest Hj HW H1 H2.
  split; [unfold bd_wpos in *; rewrite !forallb_app, HW; unfold CHf; destruct (vd_mesh v); reflexivity|]. split; [lia|].
  intros r HF _ _ HNN. unfold pay_sem. rewrite uval_lit by lia.
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. zf F1. zf F2.
  repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in F1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in F2.
  unfold B32, Lib_vec_reserve.B32 in F2. rewrite uval_lit in F2 by lia.
  apply bd_nn_app in HNN as [HN1 HNR].
  pose proof (uval_range r mi_c) as R1. pose proof (uval_range r fv_c) as R2. pose proof (uval_range r mm_c) as R3. pose proof (uval_range r sg_c) as R4.
  pose proof (uval_range r li_c) as R5. pose proof (uval_range r lc_c) as R6. pose proof (uval_range r pi_c) as R7.
  pose proof (amin1_rng r mi_c) as M1. pose proof (amin1_rng r fv_c) as M2. pose proof (amin1_rng r mm_c) as M3. pose proof (amin1_rng r sg_c) as M4.
  destruct j as [|[|[|[|[|[|[|j]]]]]]].
  8: { cbn in Hj. destruct j; discriminate. }
  all: cbn in Hj; injection Hj as <-; cbn [vd_c vd_k vd_el vMI vFV vMM vSG vLI vLC vPI] in F1, F2;
    (lazymatch goal with |- context [CHf ?w _] =>
       pose proof (eC_val r w (vd_c w) ltac:(cbn; lia) ltac:(unfold B32, Lib_vec_reserve.B32; cbn [vd_c vd_k vMI vFV vMM vSG vLI vLC vPI]; lia)) as EV end;
     cbn [vd_el vd_c vMI vFV vMM vSG vLI vLC vPI] in EV);
    rewrite !bsumV_app, !bsumK_app; unfold finV, finK, CHf, AMin1; cbn -[uval aval Z.mul Z.add Z.sub Z.of_nat]; unfold bival; cbn -[uval aval Z.mul Z.add Z.sub];
    repeat match goal with |- context [aval ?rr (ASv ?e)] => change (aval rr (ASv e)) with (uval rr e) end; rewrite EV;
    (split; [lia|]); (split; [lia|]);
    unfold bd_nn in *; repeat (apply Forall_cons; [unfold bival; cbn -[uval aval Z.mul Z.add Z.sub];
                                                   repeat match goal with |- context [aval ?rr (ASv ?e)] => change (aval rr (ASv e)) with (uval rr e) end; rewrite ?EV; lia|]); exact HNR.
Qed.

Definition keptF : list (sv * sv) := ltac2:(tb__ "0|1|
S8S6S18S18A2M0S102S6cG0S91S80A4SbG0S91Sd8A1ScG0A1A3A3").
Definition keptP : list (sv * sv) := ltac2:(tb__ "0|1|
S8S6S18S18A2M0S102S6cG0S91S80A4SbG0S7S18S18S89S1eZ40A1A4ScG0A1A3A3").

Lemma tvx_app_l : ltac2:(tb__ "0|2|
S110S1aS5S6S18S18A2M0A1M1G1S49VFB;R4R3S8G0R2R1A3A4SefR4S8G0R3R2A3A2SeeR5S8G0R4R3A3A2S1S49VFB;R7R6R5A4S1SefR6R5A2SeeR6R5A2A2A2F_;F_;F_;Fl2;Fl1;Frho;FAi;").
Proof.
  intros Ai rho l1 l2 HN HD HZ. unfold tvinA, tvz in *. apply Forall_app in HN as [HN _]. apply Forall_app in HZ as [HZ _].
  split; [exact HN|]. split; [exact (tvd_app_l rho l1 l2 HD) | exact HZ].
Qed.

Lemma b47_of : ltac2:(tb__ "0|0|
S1aS5S19A1S101S19S23R2A1R1A3S0S4S5aS19S1cS1dS70S1eS79A1A2A1R2A3S3A3S39S5fR4S70A2S79A2F_;F_;FF;Frho;").
Proof. intros rho F HF H. pose proof (holds_mem _ _ _ HF H) as X. zf X. unfold two47, RA.two47 in *. rewrite uval_lit in X by lia. exact X. Qed.

Lemma site_client : ltac2:(tb__ "0|4|
S33S5S20A1S5S6S18S18A2A1M0G0S1aS110S1aS5S58Q40A1A1S107VAInv;R4R3R2R1A4S101S19S23R6A1S1bS34RaA1A1A3Se6VFB;VFF;Vrho0;A3S10dS6aVrho0;R8A3S4dVrho0;R8A2Sf0RaS112S111R9A1A1A2S49VFB;RaRbRcA4SefRcRdA2SeeRdReA2S4fVFF;RdReScS6S6S18S15A2S18A2A1M1A4S0S4S5aS19S1cS1dS70S1eS79A1A2A1S1bS34R13A1A1A3S3A3S0S4S10cS1bS34R14A1A1R11G1S12S10A1M2Se7R13A6S3A3S0S4S10bVXGL;S1bS34R15A1M3A1R12G1G2S21G3A1Se8R13A8S3A3S1SfaVCST;Vrho0;VFB;VFF;R12R13G1R15A8SfbVCST;VXGL;Vrho0;VFB;VFF;R12R13G1R14A9A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Frho;Fkept;FXk;FR;FE;").
Proof.
  intros E R Xk kept rho Ai rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR H47 HR HX. pose proof (b47_of rho _ HF H47) as Hb. split.
  - intros o a Ho Hr.
    exact (robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ kept [] None fr_obj R rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK) HN HD HZ HFR HR
             (fun o' a' Ho' HE Hr' => fr_obj_pclMA rho o' a' _ Hav HP0 HE Hr') o a Ho Hr).
  - intros r a Hr Ha.
    exact (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho _ kept [] None (ss_objs (ax_S E)) fr_xr Xk rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK) HN HD HZ HFR HX
             (fun r' a' Hr' HE Ha' => or_introl (fr_xr_pclMA rho r' a' _ Hav HP0 Hb HE Ha')) r a Hr Ha).
Qed.

Lemma site_rt : ltac2:(tb__ "0|4|
S33S5S20A1S5S6S18S18A2A1S1aS110S1aS5S58Q40A1A1S107VAInv;R4R3R2R1A4S101S19S23R6A1S1bS34R9A1A1A3Se6VFB;VFF;Vrho0;A3S10dS6aVrho0;R8A3S4dVrho0;R8A2Sf0RaS112S111R9A1A1A2S53VFB;RaA2S4eVFF;RbA2S49VFB;RcRdReA4SefReRfA2SeeRfR10A2S4fVFF;RfR10ScS6S6S18S15A2S18A2A1M0A4S0S4S5aS19S1cS1dS70S1eS79A1A2A1S1bS34R14A1A1A3S3A3S0S4S10cS1bS34R15A1A1R13G0S12S10A1M1Se7R14A6S3A3S0S4S10bVXGL;S1bS34R16A1M2A1R14G0G1S21G2A1Se8S35R16A1A8S3A3S1S124VCST;R13S12S15A1M3R14R16A5S125VCST;VXGL;R13G3R14S35R17A1A6A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Frho;Ftv;FR;FE;").
Proof.
  intros E R tv rho Ai rho1 tp1 md1 HM HF HP0 Hav HT HTK HBf HFF HN HD HZ HFR H47 HR HX. pose proof (b47_of rho _ HF H47) as Hb. split.
  - exact (robjsP_okA segs AInv CST ALA rho0 FB FF Ai rho _ tv [] None fr_obj R rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR HR
             (fun o' a' Ho' HE Hr' => fr_obj_pclMA rho o' a' _ Hav HP0 HE Hr')).
  - exact (proj1 (xrs_checkL_okA segs AInv CST XGL ALA HCST HXGL rho0 FB FF Ai rho _ tv [] None (ss_objs (ax_S E)) fr_xr (ax_X E) rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR HX
             (fun r' a' Hr' HE Ha' => or_introl (fr_xr_pclMA rho r' a' _ Hav HP0 Hb HE Ha')))).
Qed.

Lemma block_pclMA : ltac2:(tb__ "0|2|
S110S1aS5S6S18S18A2M0A1G0S15S49VFB;R5R4R3A4SeeR5R4A2S5bG0R4R5A3S1S39S5fR7S11S18S18R5A3A2M1R4A2S3dR4S3aG1S5fR7S13S18S18R5A3A2A2A2A2S1aSf9VCST;R1Sf1VFB;R9R8A3Sf8VFF;R9ScS6S6S18S15A2S18A2A1A3R6A5Fr0;F_;F_;F_;F_;Fa;Ft;Fkept;Frho;FAi;").
Proof.
  intros Ai rho kept t a HN HZ Hin Ha r0.
  destruct (Z.eq_dec (uval rho (fst t)) 0) as [Hz|Hnz].
  - exfalso. pose proof (proj1 (Forall_forall _ _) HZ t Hin) as X. cbv beta in X. unfold tnz, tvv in X. cbn [snd] in X.
    specialize (X ltac:(intros Y; apply Y; exact Hz)). unfold uval in Ha. lia.
  - right; right; left. exists (fst (tvv rho t)), (snd (tvv rho t)). split.
    + apply In_FBx. right. exists t. split; [exact Hin|]. split; [exact Hnz | symmetry; apply surjective_pairing].
    + unfold tvv. cbn [fst snd]. unfold uval in Ha. exact Ha.
Qed.

Lemma go_holds : ltac2:(tb__ "0|1|
S40S1aS5S58Q40A1A1S5S108A1S107S6cS5S19A1VJAv;R7R6R5R4R3A5S5bS6S18S18A2S91R3A1S4bR8A1A3S1S39Z1S82R4A1M0A2S39G0Z80A2A2S101S19S23R9A1R4A3S0S4S5aS19S1cS26S25S105S6bR6A1S1eZ0A1A3A1A1R5A3S3A3S0S4S5aS19S1cS1dS6bR7A1S6dR7A1A2A1R6A3S3A3S0S4S5aS19S1cS1dS6dR8A1S1eS7aA1A2A1R7A3S3A3S101S19S23RdA1S7dR9A1A3F_;F_;F_;F_;F_;F_;F_;FF;Fv;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof.
  intros nd rho tp tr md v F HJ Hin He HF H0 H1 H2.
  pose proof (holds_mem _ _ _ HF H0) as F0. pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. zf F0. zf F1. zf F2.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in F1. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in F2.
  rewrite uval_lit in F0 by lia. unfold B32, Lib_vec_reserve.B32 in F2. rewrite uval_lit in F2 by lia.
  assert (TNZ : tnz rho (Xof v)) by (apply (d_live nd rho tp tr md (vd_d v) (vd_el v) (vd_c v) (vd_k v) HJ Hin He); unfold B32, Lib_vec_reserve.B32; lia).
  pose proof (JA_tv_facts segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue ALA _ _ _ _ _ (Xof v) eq_refl HJ Hin TNZ) as TF.
  unfold go_facts. constructor; [|constructor; [|constructor]].
  - apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA. cbn [fst snd Xof]. do 3 right. left. reflexivity.
  -
    apply (proj2 (h_ule _ _ _)). rewrite uval_lit by lia. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in F0.
    pose proof (uval_range rho (vd_c v)). unfold uval in *. lia.
Qed.

Lemma payA_same : ltac2:(tb__ "0|1|
S5S19A1S5S5eA1S0S4S64R1A1S3A3S121S6aVrho0;Se6VFB;VFF;A2R3S1eZ0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof.
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S15S5S58Q40A1A1S119F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S68S33S1aS5S58Q40A1A1S119S101S19S23R3A1S1bS34R4A1A1A3VTR;S67S38R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S119S119S119S11cR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S68S68S33S33SfdS5S20A1M0S5S6S33Se1A2M1A1S5S6S18S18A2M2A1S119S1aS5S58Q40A1A1M3G2S5bG2R1R5A3S5bG2R2S35RbA1A3F_;Fr;S0SdG0A1Se4RaR9R8A3SaG0R7A2A3S0S4Se3RbRaR9R8S102G1S33S11S33Se1A2R7A4A5S3A3S1aG3VTR;S67S38RfRdR2R1A5Se2S38S1fS34RdA1A1R2R1RaA5A2Ftp1;Frho1;S5S108A1M4S133S107S69S38R9R8R10S7G4S134R3S135R2R1A2A4A5R13RaR9R4R2A4R13SffSfeRbRfS11fR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S33Se1G4S133S107S1aG3G4S133S107S5bG1S7S33Se1RaR9A4R14A3S69S38R12R11R19S7G4S134R9S135R8R7A2A4A5R1cR13R12RaR8A4S10dS1fS34R1aA1A1SffSfeR14R18S11fR9R13RaA3A3R19A2R8A3S69S38R9R8ReS7G4S134R7S135R6R5A2A4A5ReSffSfeR16R1aS11fRbR15RcA3A3R1bA2R15RaR9R8R6A6S1S171R17S11fRcR16RdA3R1bR1cR1dR10R1eR19RbA9S1aS10fR18S11fRdR17ReA3R1cR1dS34R1eA1S34R1fA1S34R11A1R1RcA9VTR;S67S38Se5R11SffSfeR19R1dS11fReR18RfA3A3R1eA2R18RdRcA5S172R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S67S38R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CAD1 : ltac2:(tb__ "0|1|
S5S6S15S15A2M0A1S5S6G0S15A2A1S62S1aS5S58Q40A1A1S61Z3R3A2VTR;S67S38S46VAInv;VCST;VXGL;VKc;S158VCST;R6R5A3R6R5R4S41S13dAaS84R3R2A5Se2S38SdcR3R2Sf4VAInv;VCST;VXGL;VKc;S158VCST;A1S41S157R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CAD2 : ltac2:(tb__ "0|1|
S5S6S15S15A2M0A1S5S6G0S15A2A1S62S1aS5S58Q40A1A1S61Z3R3A2VTR;S67S38S46VAInv;VCST;VXGL;VKc;S15aVCST;R6R5A3R6R5R4S41S145AaS85R3R2A5Se2S38SdcR3R2Sf4VAInv;VCST;VXGL;VKc;S15aVCST;A1S41S159R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CAD3 : ltac2:(tb__ "0|1|
S5S6S15S15A2M0A1S5S6G0S15A2A1S62S1aS5S58Q40A1A1S61Z3R3A2VTR;S67S38S46VAInv;VCST;VXGL;VKc;S15cVCST;R6R5A3R6R5R4S41S14dAaS86R3R2A5Se2S38SdcR3R2Sf4VAInv;VCST;VXGL;VKc;S15cVCST;A1S41S15bR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CAD4 : ltac2:(tb__ "0|1|
S5S6S15S15A2M0A1S5S6G0S15A2A1S62S1aS5S58Q40A1A1S61Z3R3A2VTR;S67S38S46VAInv;VCST;VXGL;VKc;S15eVCST;R6R5A3R6R5R4S41S155AaS87R3R2A5Se2S38SdcR3R2Sf4VAInv;VCST;VXGL;VKc;S15eVCST;A1S41S15dR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CNM : ltac2:(tb__ "0|1|
S5S6S15S15A2M0A1S5S6G0S15A2A1S62S1aS5S58Q40A1A1S61Z3R3A2VTR;S67S38S46VAInv;VCST;VXGL;VKc;S165R6R5A2R6R5R4S41S170AaSc7R3R2A5Se2S38SdcR3R2Sf4VAInv;VCST;VXGL;VKc;S165S41S166R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CVF : ltac2:(tb__ "0|1|
S5S6S15S15A2M0A1S5S6G0S15A2A1S62S1aS5S58Q40A1A1S61Z4R3A2VTR;S67S38S46VAInv;VCST;VXGL;VKc;S167VCST;R6R5A3R6R5R4S41S162AaS7fR3R2A5Se2S38SdcR3R2Sf4VAInv;VCST;VXGL;VKc;S167VCST;A1S41S95R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis CVP : ltac2:(tb__ "0|1|
S5S6S15S15A2M0A1S5S6G0S15A2A1S62S1aS5S58Q40A1A1S61Z4R3A2VTR;S67S38S46VAInv;VCST;VXGL;VKc;S10aR6R5A2R6R5R4S41S164S113S3S156A3AaS96R3R2A5Se2S38SdcR3R2Sf4VAInv;VCST;VXGL;VKc;S10aS41S163S8fS113S3A3R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis CMEMCPY : ltac2:(tb__ "0|2|
S110S1aS5S58Q40A1A1VTR;S67S38S16bVAInv;R3VKc;A3S90R2R1A5Se2S38SdcR2R1SbS6S33Se1A2M0S7S33Se1S8eS16aVAInv;VCST;VXGL;R3VKc;A5A4M1SbG0G1ScG0A1A3A3A5A2Ftp1;Frho1;FAi;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S33S40S6S15S18A2M0S1aS5S58Q40A1A1M1S15G1S5bS6S6S33S40A2M2G0A2S7G2G0S7S33S40R7R6A4R5A4S73A3S1S39Z0S4cS7G2G0S7S33S40R8R7A4R6A4R5A2M3A2S3dG3R3A2A2VTR;S67S38VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S33S40S1aS5S58Q40A1A1M0S15G0S5bS6S33Se1A2S7S33Se1R6SdfR5A1A4Se0A3VTR;S67S38VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac vmr := first [ lazymatch goal with |- @eq ?T ?t ?v => tryif first [ has_evar t | has_evar v ] then fail else vm_cast_no_check (@eq_refl T v) end
                  | vm_compute; reflexivity ].
Tactic Notation "innth" integer(n) := do n right; left; reflexivity.

Lemma X_FIN1 : ltac2:(tb__ "0|16|
S10S6cS33S33S33S33S33S33SfdS5S20A1M0S15S1aS5S58Q40A1A1M1S15G1S0SdS6cA1S5cS6cS80RfA3SaS6cReA2A3S0S4S5dS19S2bS1fS34ReA1M2A1A1S8S19S7dRfA1S1bG2A1A3A3S3A3S0S4S5aS19S1cS26S25S105S6bR10A1S1eZ0M3A1M4A3A1A1S1bS34RfA1A1A3S3A3S0S4S5aS19S1cS1dS6bR11A1S6dR11A1A2A1S1bS34R10A1A1A3S3A3S0S4S5aS19S1cS1dS6dR12A1S1eS7aA1M5A2A1S1bS34R11A1A1A3S3A3S0SdS33A1M6SddS11dS7dR13A1R12A2S94Z40M7A1A2SaS33R11A2A3S0S4S5aS19S1cS1dS6bR14A1S6dR14A1A2A1S1bS34R12A1A1A3S3A3S0S4S5aS19S1cS1dS6dR15A1G5A2A1S1bS34R13A1A1A3S3A3S0S4S5aS19S1cS1dS70S1eS79A1A2A1S1bS34R14A1A1A3S3A3S0S4Sf7S71R17A1S35R15A1A2S3A3S0SdG0A1Se4R16S84R11A3SaG0R10A2A3S0S4Se3R17S84R12R11S102S6S33S40A2M8S33S11S33S40A2S157A4A5S3A3S0S4S120S6aR13A2S3A3S0S4S10eR14SdcA2S3A3S0S4S109S6aS1fS34R1aA1A1A2S3A3S0S4S47S1fS34R1bA1A1S44S8S6S18S18A2M9SdeSbG9S7S18S18S89S1eG7A1A4ScG9A1A3MaA3ScS6S6S18S15A2S18A2A1MbS8S5eS76R1dS6bR1dA1A2S8S5eS6eS9R1eA1S6fA2S8aS77S7eA2McA3A3S42S72S3A2MdA4A2S3A3S0S4S63S1fS34R1cA1A1S8S5eS6eS9R1fA1S6fA2GcA3A2S3A3S0S4SedR18GaS136A3S3A3S0S4S48S43R19S13aA2GdA2S3A3S0S4S12fS1bS34R1fA1A1G4G3S8S5eS76R21S6bR21A1A2S8S5eS6eS9R22A1S6fA2GcA3MeA3S8S5eS60R1aS139A2GeA3A5S3A3S0S4S5dSf6Sf5S84SdcR1bS1fS34R20A1A1A4S157A3S3A3S0S4S10cS1bS34R21A1A1SdeGbS12S10A1MfSe7R1bA6S3A3S0S4S10bVXGL;S1bS34R22A1M10A1SdeGbGfS21G10A1Se8S71R24A1A8S3A3S0S18SfcR1ePdA2S8dR25A1A3S0S18SfcR1fP10A2S74S82R26A1S6dR26A1A2A3S0S33Sf3S84R25R20R1fS138S71R27A1A6R24A3S0G6SddR25S83S9R29A1A1A2SaS33R24A2A3S1S0S5G9A1M11SecS115R27R22S138A3M12S136A2GaA3S0S45S43G12S13cA2S42S81S3A2A3A2S0S33Sf3S84R28R23R22S137S71R2aA1A6R25A3S0G6SddR26S83S9R2cA1A1A2SaS33R25A2A3S1S0G11SecS115R2aR25S137A3M13S136A2GaA3S0S45S43G13S13bA2S42S72SeA2A3A2S5bS6G8S6S15S18A2M14A2M15S7G8G14S7S33S40R29S8cS9R2eA1S81A2A4S7S15S18R24S75A4A4S73A3S5bG15S7G8G14S7S33S40R28S8bS9R2fA1S72A2A4S7S15S18R25S75A4A4S73A3S39G3R26A2S39S3bS3aR27Z1A2S3cZ2G7A2A2R24A2VTR;S67S38VJAv;S44S78GbS8S5eS6eR32S6fA2GcA3GdA4A1R30R27R26A5VFAM;R25R24A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FrkT;FR;Fs;FTf;FTf0;FTok;FTok0;FE;FE0;Fv;Fj;").
Proof.
  intros j v E0 E Tok0 Tok Tf0 Tf s R rkT rho tp b tp0 Hj Hgb Hc0 Hck0 HkB0 HE Hck HkB H47 HXk He Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham Hpay Hpd HR HX Hs13 Hs16
         HTok0 HTok Himp_ok HTf0 HTf Himp_f HinOk HinF Hrk Hb.
  assert (Hv : In v fins) by (eapply nth_error_In; exact Hj).
  assert (He128 : 1 <= vd_el v <= 128) by (cbn in Hv; destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn; lia).
  assert (HinX : In (Xof v) tv0) by (unfold tv0; apply in_or_app; left; apply in_map; exact Hv).

  eapply TR_pre with (P := SPA segs (JAv (NDA tv0 [] (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) (AHead vHq true))) E rho tp).
  { intros w Hw.
    assert (Hw1 : SPA segs (JAv (NDA tv0 [] (CHfrom j cs0 ++ bd_push sh_c sh_k) (AHead vHq true))) (ax_add_facts (go_facts v) E0) rho tp w).
    { apply (SPA_refacts_JA segs); [exact Hw | exact Hgb |].
      intros tr md HJ HF. apply Forall_app. split; [|exact HF]. exact (go_holds _ rho tp tr md v _ HJ HinX He128 HF Hc0 Hck0 HkB0). }
    pose proof (SPA_axforms segs _ (xf_call 64) rho _ E tp w HE Hw1) as Hw2.
    apply (JA_repay segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue tv0 [] (CHfrom j cs0 ++ bd_push sh_c sh_k)
             (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) (AHead vHq true) E rho tp w); [|exact Hw2].
    exact (pay_fin j v (ss_facts (ax_S E)) (bd_push sh_c sh_k) Hj eq_refl Hck HkB). }

  unfold tv0. change (map Xof fins ++ [Xof vSH; (vAR, SLit 64)]) with (keptF ++ [(vAR, SLit 64)]).
  change (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) with (CHf v (vd_c v) ++ CHfrom (S j) cs0 ++ bd_push sh_c sh_k).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc HBX (ADP1.P0_ad CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_ad1 AD1.nd0 ADP1.PD_ad NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CAD1 eq_refl
           E s R (Xk_fin v) rho tp keptF [(vAR, SLit 64)] [] _ (CHfrom (S j) cs0 ++ bd_push sh_c sh_k) (AHead vHq true) (FAM b tp0)
           HXk He Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham).
  - apply (payA_of_bud_pay2 NP rho0 (P0_fs FB FF)). exact Hpay.
  - exact Hpd.
  - intros Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    destruct (tvx_app_l Ai rho keptF _ HN HD HZ) as (HN1 & HD1 & HZ1).
    destruct (site_client E R (Xk_fin v) keptF rho Ai rho1 tp1 md1 HM HF HP0 Hav HT HTK HN1 HD1 HZ1 HFR H47 HR HX) as [A B].
    split; [exact A|]. split; [exact B|].
    unfold ADP1.P0_ad. intros a Ha. unfold uval, AD1.vSRC, AD1.vLS in Ha. cbn [eval] in Ha. rewrite !rw_call', Hs13, Hs16 in Ha.
    apply (block_pclMA Ai rho keptF (Xof v) a HN1 HZ1); [apply in_or_app; left; apply in_map; exact Hv | exact Ha].
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [ADP1.PD_ad In] in Hd.
    destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am AD1.ndF AD1.ndK AD1.nd0]; fold (isub_ad1 E s AD1.P_fail); fold (isub_ad1 E s AD1.P_ok).
    +   rewrite HTf0, (proj1 Himp_f), (proj2 Himp_f). change (bd_subst _ [] ++ ?r) with r.
      eapply TR_pre; [|apply (REENTER Tf (ndTf (S j) vHq) (rkT, z0) rho'); [exact HinF | rewrite emeas_z0; lia]].
      intros w Hw. exact (SPA_axforms segs _ _ rho' Tf0 Tf tp' w HTf Hw).
    +   rewrite HTok0, (proj1 Himp_ok), (proj2 Himp_ok). change (bd_subst _ [] ++ ?r) with r.
      eapply TR_pre; [|apply (REENTER Tok (ndTok (S j) vHa) (rkT, z0) rho'); [exact HinOk | rewrite emeas_z0; lia]].
      intros w Hw. exact (SPA_axforms segs _ _ rho' Tok0 Tok tp' w HTok Hw).
Qed.
Lemma X_FIN2 : ltac2:(tb__ "0|16|
S10S6cS33S33S33S33S33S33SfdS5S20A1M0S15S1aS5S58Q40A1A1M1S15G1S0SdS6cA1S5cS6cS80RfA3SaS6cReA2A3S0S4S5dS19S2bS1fS34ReA1M2A1A1S8S19S7dRfA1S1bG2A1A3A3S3A3S0S4S5aS19S1cS26S25S105S6bR10A1S1eZ0M3A1M4A3A1A1S1bS34RfA1A1A3S3A3S0S4S5aS19S1cS1dS6bR11A1S6dR11A1A2A1S1bS34R10A1A1A3S3A3S0S4S5aS19S1cS1dS6dR12A1S1eS7aA1M5A2A1S1bS34R11A1A1A3S3A3S0SdS33A1M6SddS11dS7dR13A1R12A2S94Z40M7A1A2SaS33R11A2A3S0S4S5aS19S1cS1dS6bR14A1S6dR14A1A2A1S1bS34R12A1A1A3S3A3S0S4S5aS19S1cS1dS6dR15A1G5A2A1S1bS34R13A1A1A3S3A3S0S4S5aS19S1cS1dS70S1eS79A1A2A1S1bS34R14A1A1A3S3A3S0S4Sf7S71R17A1S35R15A1A2S3A3S0SdG0A1Se4R16S85R11A3SaG0R10A2A3S0S4Se3R17S85R12R11S102S6S33S40A2M8S33S11S33S40A2S159A4A5S3A3S0S4S120S6aR13A2S3A3S0S4S10eR14SdcA2S3A3S0S4S109S6aS1fS34R1aA1A1A2S3A3S0S4S47S1fS34R1bA1A1S44S8S6S18S18A2M9SdeSbG9S7S18S18S89S1eG7A1A4ScG9A1A3MaA3ScS6S6S18S15A2S18A2A1MbS8S5eS76R1dS6bR1dA1A2S8S5eS6eS9R1eA1S6fA2S8aS77S7eA2McA3A3S42S72S3A2MdA4A2S3A3S0S4S63S1fS34R1cA1A1S8S5eS6eS9R1fA1S6fA2GcA3A2S3A3S0S4SedR18GaS13eA3S3A3S0S4S48S43R19S142A2GdA2S3A3S0S4S12fS1bS34R1fA1A1G4G3S8S5eS76R21S6bR21A1A2S8S5eS6eS9R22A1S6fA2GcA3MeA3S8S5eS60R1aS141A2GeA3A5S3A3S0S4S5dSf6Sf5S85SdcR1bS1fS34R20A1A1A4S159A3S3A3S0S4S10cS1bS34R21A1A1SdeGbS12S10A1MfSe7R1bA6S3A3S0S4S10bVXGL;S1bS34R22A1M10A1SdeGbGfS21G10A1Se8S71R24A1A8S3A3S0S18SfcR1ePdA2S8dR25A1A3S0S18SfcR1fP10A2S74S82R26A1S6dR26A1A2A3S0S33Sf3S85R25R20R1fS140S71R27A1A6R24A3S0G6SddR25S83S9R29A1A1A2SaS33R24A2A3S1S0S5G9A1M11SecS116R27R22S140A3M12S13eA2GaA3S0S45S43G12S144A2S42S81S3A2A3A2S0S33Sf3S85R28R23R22S13fS71R2aA1A6R25A3S0G6SddR26S83S9R2cA1A1A2SaS33R25A2A3S1S0G11SecS116R2aR25S13fA3M13S13eA2GaA3S0S45S43G13S143A2S42S72SeA2A3A2S5bS6G8S6S15S18A2M14A2M15S7G8G14S7S33S40R29S8cS9R2eA1S81A2A4S7S15S18R24S75A4A4S73A3S5bG15S7G8G14S7S33S40R28S8bS9R2fA1S72A2A4S7S15S18R25S75A4A4S73A3S39G3R26A2S39S3bS3aR27Z1A2S3cZ2G7A2A2R24A2VTR;S67S38VJAv;S44S78GbS8S5eS6eR32S6fA2GcA3GdA4A1R30R27R26A5VFAM;R25R24A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FrkT;FR;Fs;FTf;FTf0;FTok;FTok0;FE;FE0;Fv;Fj;").
Proof.
  intros j v E0 E Tok0 Tok Tf0 Tf s R rkT rho tp b tp0 Hj Hgb Hc0 Hck0 HkB0 HE Hck HkB H47 HXk He Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham Hpay Hpd HR HX Hs13 Hs16
         HTok0 HTok Himp_ok HTf0 HTf Himp_f HinOk HinF Hrk Hb.
  assert (Hv : In v fins) by (eapply nth_error_In; exact Hj).
  assert (He128 : 1 <= vd_el v <= 128) by (cbn in Hv; destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn; lia).
  assert (HinX : In (Xof v) tv0) by (unfold tv0; apply in_or_app; left; apply in_map; exact Hv).

  eapply TR_pre with (P := SPA segs (JAv (NDA tv0 [] (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) (AHead vHq true))) E rho tp).
  { intros w Hw.
    assert (Hw1 : SPA segs (JAv (NDA tv0 [] (CHfrom j cs0 ++ bd_push sh_c sh_k) (AHead vHq true))) (ax_add_facts (go_facts v) E0) rho tp w).
    { apply (SPA_refacts_JA segs); [exact Hw | exact Hgb |].
      intros tr md HJ HF. apply Forall_app. split; [|exact HF]. exact (go_holds _ rho tp tr md v _ HJ HinX He128 HF Hc0 Hck0 HkB0). }
    pose proof (SPA_axforms segs _ (xf_call 64) rho _ E tp w HE Hw1) as Hw2.
    apply (JA_repay segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue tv0 [] (CHfrom j cs0 ++ bd_push sh_c sh_k)
             (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) (AHead vHq true) E rho tp w); [|exact Hw2].
    exact (pay_fin j v (ss_facts (ax_S E)) (bd_push sh_c sh_k) Hj eq_refl Hck HkB). }

  unfold tv0. change (map Xof fins ++ [Xof vSH; (vAR, SLit 64)]) with (keptF ++ [(vAR, SLit 64)]).
  change (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) with (CHf v (vd_c v) ++ CHfrom (S j) cs0 ++ bd_push sh_c sh_k).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc HBX (ADP2.P0_ad CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_ad2 AD2.nd0 ADP2.PD_ad NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CAD2 eq_refl
           E s R (Xk_fin v) rho tp keptF [(vAR, SLit 64)] [] _ (CHfrom (S j) cs0 ++ bd_push sh_c sh_k) (AHead vHq true) (FAM b tp0)
           HXk He Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham).
  - apply (payA_of_bud_pay2 NP rho0 (P0_fs FB FF)). exact Hpay.
  - exact Hpd.
  - intros Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    destruct (tvx_app_l Ai rho keptF _ HN HD HZ) as (HN1 & HD1 & HZ1).
    destruct (site_client E R (Xk_fin v) keptF rho Ai rho1 tp1 md1 HM HF HP0 Hav HT HTK HN1 HD1 HZ1 HFR H47 HR HX) as [A B].
    split; [exact A|]. split; [exact B|].
    unfold ADP2.P0_ad. intros a Ha. unfold uval, AD2.vSRC, AD2.vLS in Ha. cbn [eval] in Ha. rewrite !rw_call', Hs13, Hs16 in Ha.
    apply (block_pclMA Ai rho keptF (Xof v) a HN1 HZ1); [apply in_or_app; left; apply in_map; exact Hv | exact Ha].
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [ADP2.PD_ad In] in Hd.
    destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am AD2.ndF AD2.ndK AD2.nd0]; fold (isub_ad2 E s AD2.P_fail); fold (isub_ad2 E s AD2.P_ok).
    +   rewrite HTf0, (proj1 Himp_f), (proj2 Himp_f). change (bd_subst _ [] ++ ?r) with r.
      eapply TR_pre; [|apply (REENTER Tf (ndTf (S j) vHq) (rkT, z0) rho'); [exact HinF | rewrite emeas_z0; lia]].
      intros w Hw. exact (SPA_axforms segs _ _ rho' Tf0 Tf tp' w HTf Hw).
    +   rewrite HTok0, (proj1 Himp_ok), (proj2 Himp_ok). change (bd_subst _ [] ++ ?r) with r.
      eapply TR_pre; [|apply (REENTER Tok (ndTok (S j) vHa) (rkT, z0) rho'); [exact HinOk | rewrite emeas_z0; lia]].
      intros w Hw. exact (SPA_axforms segs _ _ rho' Tok0 Tok tp' w HTok Hw).
Qed.
Lemma X_FIN3 : ltac2:(tb__ "0|16|
S10S6cS33S33S33S33S33S33SfdS5S20A1M0S15S1aS5S58Q40A1A1M1S15G1S0SdS6cA1S5cS6cS80RfA3SaS6cReA2A3S0S4S5dS19S2bS1fS34ReA1M2A1A1S8S19S7dRfA1S1bG2A1A3A3S3A3S0S4S5aS19S1cS26S25S105S6bR10A1S1eZ0M3A1M4A3A1A1S1bS34RfA1A1A3S3A3S0S4S5aS19S1cS1dS6bR11A1S6dR11A1A2A1S1bS34R10A1A1A3S3A3S0S4S5aS19S1cS1dS6dR12A1S1eS7aA1M5A2A1S1bS34R11A1A1A3S3A3S0SdS33A1M6SddS11dS7dR13A1R12A2S94Z40M7A1A2SaS33R11A2A3S0S4S5aS19S1cS1dS6bR14A1S6dR14A1A2A1S1bS34R12A1A1A3S3A3S0S4S5aS19S1cS1dS6dR15A1G5A2A1S1bS34R13A1A1A3S3A3S0S4S5aS19S1cS1dS70S1eS79A1A2A1S1bS34R14A1A1A3S3A3S0S4Sf7S71R17A1S35R15A1A2S3A3S0SdG0A1Se4R16S86R11A3SaG0R10A2A3S0S4Se3R17S86R12R11S102S6S33S40A2M8S33S11S33S40A2S15bA4A5S3A3S0S4S120S6aR13A2S3A3S0S4S10eR14SdcA2S3A3S0S4S109S6aS1fS34R1aA1A1A2S3A3S0S4S47S1fS34R1bA1A1S44S8S6S18S18A2M9SdeSbG9S7S18S18S89S1eG7A1A4ScG9A1A3MaA3ScS6S6S18S15A2S18A2A1MbS8S5eS76R1dS6bR1dA1A2S8S5eS6eS9R1eA1S6fA2S8aS77S7eA2McA3A3S42S72S3A2MdA4A2S3A3S0S4S63S1fS34R1cA1A1S8S5eS6eS9R1fA1S6fA2GcA3A2S3A3S0S4SedR18GaS146A3S3A3S0S4S48S43R19S14aA2GdA2S3A3S0S4S12fS1bS34R1fA1A1G4G3S8S5eS76R21S6bR21A1A2S8S5eS6eS9R22A1S6fA2GcA3MeA3S8S5eS60R1aS149A2GeA3A5S3A3S0S4S5dSf6Sf5S86SdcR1bS1fS34R20A1A1A4S15bA3S3A3S0S4S10cS1bS34R21A1A1SdeGbS12S10A1MfSe7R1bA6S3A3S0S4S10bVXGL;S1bS34R22A1M10A1SdeGbGfS21G10A1Se8S71R24A1A8S3A3S0S18SfcR1ePdA2S8dR25A1A3S0S18SfcR1fP10A2S74S82R26A1S6dR26A1A2A3S0S33Sf3S86R25R20R1fS148S71R27A1A6R24A3S0G6SddR25S83S9R29A1A1A2SaS33R24A2A3S1S0S5G9A1M11SecS117R27R22S148A3M12S146A2GaA3S0S45S43G12S14cA2S42S81S3A2A3A2S0S33Sf3S86R28R23R22S147S71R2aA1A6R25A3S0G6SddR26S83S9R2cA1A1A2SaS33R25A2A3S1S0G11SecS117R2aR25S147A3M13S146A2GaA3S0S45S43G13S14bA2S42S72SeA2A3A2S5bS6G8S6S15S18A2M14A2M15S7G8G14S7S33S40R29S8cS9R2eA1S81A2A4S7S15S18R24S75A4A4S73A3S5bG15S7G8G14S7S33S40R28S8bS9R2fA1S72A2A4S7S15S18R25S75A4A4S73A3S39G3R26A2S39S3bS3aR27Z1A2S3cZ2G7A2A2R24A2VTR;S67S38VJAv;S44S78GbS8S5eS6eR32S6fA2GcA3GdA4A1R30R27R26A5VFAM;R25R24A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FrkT;FR;Fs;FTf;FTf0;FTok;FTok0;FE;FE0;Fv;Fj;").
Proof.
  intros j v E0 E Tok0 Tok Tf0 Tf s R rkT rho tp b tp0 Hj Hgb Hc0 Hck0 HkB0 HE Hck HkB H47 HXk He Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham Hpay Hpd HR HX Hs13 Hs16
         HTok0 HTok Himp_ok HTf0 HTf Himp_f HinOk HinF Hrk Hb.
  assert (Hv : In v fins) by (eapply nth_error_In; exact Hj).
  assert (He128 : 1 <= vd_el v <= 128) by (cbn in Hv; destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn; lia).
  assert (HinX : In (Xof v) tv0) by (unfold tv0; apply in_or_app; left; apply in_map; exact Hv).

  eapply TR_pre with (P := SPA segs (JAv (NDA tv0 [] (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) (AHead vHq true))) E rho tp).
  { intros w Hw.
    assert (Hw1 : SPA segs (JAv (NDA tv0 [] (CHfrom j cs0 ++ bd_push sh_c sh_k) (AHead vHq true))) (ax_add_facts (go_facts v) E0) rho tp w).
    { apply (SPA_refacts_JA segs); [exact Hw | exact Hgb |].
      intros tr md HJ HF. apply Forall_app. split; [|exact HF]. exact (go_holds _ rho tp tr md v _ HJ HinX He128 HF Hc0 Hck0 HkB0). }
    pose proof (SPA_axforms segs _ (xf_call 64) rho _ E tp w HE Hw1) as Hw2.
    apply (JA_repay segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue tv0 [] (CHfrom j cs0 ++ bd_push sh_c sh_k)
             (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) (AHead vHq true) E rho tp w); [|exact Hw2].
    exact (pay_fin j v (ss_facts (ax_S E)) (bd_push sh_c sh_k) Hj eq_refl Hck HkB). }

  unfold tv0. change (map Xof fins ++ [Xof vSH; (vAR, SLit 64)]) with (keptF ++ [(vAR, SLit 64)]).
  change (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) with (CHf v (vd_c v) ++ CHfrom (S j) cs0 ++ bd_push sh_c sh_k).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc HBX (ADP3.P0_ad CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_ad3 AD3.nd0 ADP3.PD_ad NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CAD3 eq_refl
           E s R (Xk_fin v) rho tp keptF [(vAR, SLit 64)] [] _ (CHfrom (S j) cs0 ++ bd_push sh_c sh_k) (AHead vHq true) (FAM b tp0)
           HXk He Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham).
  - apply (payA_of_bud_pay2 NP rho0 (P0_fs FB FF)). exact Hpay.
  - exact Hpd.
  - intros Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    destruct (tvx_app_l Ai rho keptF _ HN HD HZ) as (HN1 & HD1 & HZ1).
    destruct (site_client E R (Xk_fin v) keptF rho Ai rho1 tp1 md1 HM HF HP0 Hav HT HTK HN1 HD1 HZ1 HFR H47 HR HX) as [A B].
    split; [exact A|]. split; [exact B|].
    unfold ADP3.P0_ad. intros a Ha. unfold uval, AD3.vSRC, AD3.vLS in Ha. cbn [eval] in Ha. rewrite !rw_call', Hs13, Hs16 in Ha.
    apply (block_pclMA Ai rho keptF (Xof v) a HN1 HZ1); [apply in_or_app; left; apply in_map; exact Hv | exact Ha].
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [ADP3.PD_ad In] in Hd.
    destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am AD3.ndF AD3.ndK AD3.nd0]; fold (isub_ad3 E s AD3.P_fail); fold (isub_ad3 E s AD3.P_ok).
    +   rewrite HTf0, (proj1 Himp_f), (proj2 Himp_f). change (bd_subst _ [] ++ ?r) with r.
      eapply TR_pre; [|apply (REENTER Tf (ndTf (S j) vHq) (rkT, z0) rho'); [exact HinF | rewrite emeas_z0; lia]].
      intros w Hw. exact (SPA_axforms segs _ _ rho' Tf0 Tf tp' w HTf Hw).
    +   rewrite HTok0, (proj1 Himp_ok), (proj2 Himp_ok). change (bd_subst _ [] ++ ?r) with r.
      eapply TR_pre; [|apply (REENTER Tok (ndTok (S j) vHa) (rkT, z0) rho'); [exact HinOk | rewrite emeas_z0; lia]].
      intros w Hw. exact (SPA_axforms segs _ _ rho' Tok0 Tok tp' w HTok Hw).
Qed.
Lemma X_FIN4 : ltac2:(tb__ "0|16|
S10S6cS33S33S33S33S33S33SfdS5S20A1M0S15S1aS5S58Q40A1A1M1S15G1S0SdS6cA1S5cS6cS80RfA3SaS6cReA2A3S0S4S5dS19S2bS1fS34ReA1M2A1A1S8S19S7dRfA1S1bG2A1A3A3S3A3S0S4S5aS19S1cS26S25S105S6bR10A1S1eZ0M3A1M4A3A1A1S1bS34RfA1A1A3S3A3S0S4S5aS19S1cS1dS6bR11A1S6dR11A1A2A1S1bS34R10A1A1A3S3A3S0S4S5aS19S1cS1dS6dR12A1S1eS7aA1M5A2A1S1bS34R11A1A1A3S3A3S0SdS33A1M6SddS11dS7dR13A1R12A2S94Z40M7A1A2SaS33R11A2A3S0S4S5aS19S1cS1dS6bR14A1S6dR14A1A2A1S1bS34R12A1A1A3S3A3S0S4S5aS19S1cS1dS6dR15A1G5A2A1S1bS34R13A1A1A3S3A3S0S4S5aS19S1cS1dS70S1eS79A1A2A1S1bS34R14A1A1A3S3A3S0S4Sf7S71R17A1S35R15A1A2S3A3S0SdG0A1Se4R16S87R11A3SaG0R10A2A3S0S4Se3R17S87R12R11S102S6S33S40A2M8S33S11S33S40A2S15dA4A5S3A3S0S4S120S6aR13A2S3A3S0S4S10eR14SdcA2S3A3S0S4S109S6aS1fS34R1aA1A1A2S3A3S0S4S47S1fS34R1bA1A1S44S8S6S18S18A2M9SdeSbG9S7S18S18S89S1eG7A1A4ScG9A1A3MaA3ScS6S6S18S15A2S18A2A1MbS8S5eS76R1dS6bR1dA1A2S8S5eS6eS9R1eA1S6fA2S8aS77S7eA2McA3A3S42S72S3A2MdA4A2S3A3S0S4S63S1fS34R1cA1A1S8S5eS6eS9R1fA1S6fA2GcA3A2S3A3S0S4SedR18GaS14eA3S3A3S0S4S48S43R19S152A2GdA2S3A3S0S4S12fS1bS34R1fA1A1G4G3S8S5eS76R21S6bR21A1A2S8S5eS6eS9R22A1S6fA2GcA3MeA3S8S5eS60R1aS151A2GeA3A5S3A3S0S4S5dSf6Sf5S87SdcR1bS1fS34R20A1A1A4S15dA3S3A3S0S4S10cS1bS34R21A1A1SdeGbS12S10A1MfSe7R1bA6S3A3S0S4S10bVXGL;S1bS34R22A1M10A1SdeGbGfS21G10A1Se8S71R24A1A8S3A3S0S18SfcR1ePdA2S8dR25A1A3S0S18SfcR1fP10A2S74S82R26A1S6dR26A1A2A3S0S33Sf3S87R25R20R1fS150S71R27A1A6R24A3S0G6SddR25S83S9R29A1A1A2SaS33R24A2A3S1S0S5G9A1M11SecS118R27R22S150A3M12S14eA2GaA3S0S45S43G12S154A2S42S81S3A2A3A2S0S33Sf3S87R28R23R22S14fS71R2aA1A6R25A3S0G6SddR26S83S9R2cA1A1A2SaS33R25A2A3S1S0G11SecS118R2aR25S14fA3M13S14eA2GaA3S0S45S43G13S153A2S42S72SeA2A3A2S5bS6G8S6S15S18A2M14A2M15S7G8G14S7S33S40R29S8cS9R2eA1S81A2A4S7S15S18R24S75A4A4S73A3S5bG15S7G8G14S7S33S40R28S8bS9R2fA1S72A2A4S7S15S18R25S75A4A4S73A3S39G3R26A2S39S3bS3aR27Z1A2S3cZ2G7A2A2R24A2VTR;S67S38VJAv;S44S78GbS8S5eS6eR32S6fA2GcA3GdA4A1R30R27R26A5VFAM;R25R24A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FrkT;FR;Fs;FTf;FTf0;FTok;FTok0;FE;FE0;Fv;Fj;").
Proof.
  intros j v E0 E Tok0 Tok Tf0 Tf s R rkT rho tp b tp0 Hj Hgb Hc0 Hck0 HkB0 HE Hck HkB H47 HXk He Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham Hpay Hpd HR HX Hs13 Hs16
         HTok0 HTok Himp_ok HTf0 HTf Himp_f HinOk HinF Hrk Hb.
  assert (Hv : In v fins) by (eapply nth_error_In; exact Hj).
  assert (He128 : 1 <= vd_el v <= 128) by (cbn in Hv; destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn; lia).
  assert (HinX : In (Xof v) tv0) by (unfold tv0; apply in_or_app; left; apply in_map; exact Hv).

  eapply TR_pre with (P := SPA segs (JAv (NDA tv0 [] (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) (AHead vHq true))) E rho tp).
  { intros w Hw.
    assert (Hw1 : SPA segs (JAv (NDA tv0 [] (CHfrom j cs0 ++ bd_push sh_c sh_k) (AHead vHq true))) (ax_add_facts (go_facts v) E0) rho tp w).
    { apply (SPA_refacts_JA segs); [exact Hw | exact Hgb |].
      intros tr md HJ HF. apply Forall_app. split; [|exact HF]. exact (go_holds _ rho tp tr md v _ HJ HinX He128 HF Hc0 Hck0 HkB0). }
    pose proof (SPA_axforms segs _ (xf_call 64) rho _ E tp w HE Hw1) as Hw2.
    apply (JA_repay segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue tv0 [] (CHfrom j cs0 ++ bd_push sh_c sh_k)
             (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) (AHead vHq true) E rho tp w); [|exact Hw2].
    exact (pay_fin j v (ss_facts (ax_S E)) (bd_push sh_c sh_k) Hj eq_refl Hck HkB). }

  unfold tv0. change (map Xof fins ++ [Xof vSH; (vAR, SLit 64)]) with (keptF ++ [(vAR, SLit 64)]).
  change (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) with (CHf v (vd_c v) ++ CHfrom (S j) cs0 ++ bd_push sh_c sh_k).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc HBX (ADP4.P0_ad CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_ad4 AD4.nd0 ADP4.PD_ad NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CAD4 eq_refl
           E s R (Xk_fin v) rho tp keptF [(vAR, SLit 64)] [] _ (CHfrom (S j) cs0 ++ bd_push sh_c sh_k) (AHead vHq true) (FAM b tp0)
           HXk He Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham).
  - apply (payA_of_bud_pay2 NP rho0 (P0_fs FB FF)). exact Hpay.
  - exact Hpd.
  - intros Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    destruct (tvx_app_l Ai rho keptF _ HN HD HZ) as (HN1 & HD1 & HZ1).
    destruct (site_client E R (Xk_fin v) keptF rho Ai rho1 tp1 md1 HM HF HP0 Hav HT HTK HN1 HD1 HZ1 HFR H47 HR HX) as [A B].
    split; [exact A|]. split; [exact B|].
    unfold ADP4.P0_ad. intros a Ha. unfold uval, AD4.vSRC, AD4.vLS in Ha. cbn [eval] in Ha. rewrite !rw_call', Hs13, Hs16 in Ha.
    apply (block_pclMA Ai rho keptF (Xof v) a HN1 HZ1); [apply in_or_app; left; apply in_map; exact Hv | exact Ha].
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [ADP4.PD_ad In] in Hd.
    destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am AD4.ndF AD4.ndK AD4.nd0]; fold (isub_ad4 E s AD4.P_fail); fold (isub_ad4 E s AD4.P_ok).
    +   rewrite HTf0, (proj1 Himp_f), (proj2 Himp_f). change (bd_subst _ [] ++ ?r) with r.
      eapply TR_pre; [|apply (REENTER Tf (ndTf (S j) vHq) (rkT, z0) rho'); [exact HinF | rewrite emeas_z0; lia]].
      intros w Hw. exact (SPA_axforms segs _ _ rho' Tf0 Tf tp' w HTf Hw).
    +   rewrite HTok0, (proj1 Himp_ok), (proj2 Himp_ok). change (bd_subst _ [] ++ ?r) with r.
      eapply TR_pre; [|apply (REENTER Tok (ndTok (S j) vHa) (rkT, z0) rho'); [exact HinOk | rewrite emeas_z0; lia]].
      intros w Hw. exact (SPA_axforms segs _ _ rho' Tok0 Tok tp' w HTok Hw).
Qed.
Lemma X_E_ad1 : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0S39S3bZ92S3cZ2Z40A2A2R2A2VTR;S67S38VJAv;SccA1Sb1R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd1.
  apply (X_FIN1 0 vMI E_ad1_0 E_ad1 T1_ok0 T1_ok T1_fail0 T1_fail s_ad1 R_ad1 145 rho tp b tp0 eq_refl);
    [vmr|vmr|vmr|vmr| exact E_ad1_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact T1_ok0_eq | exact T1_ok_eq | exact imp_ad1_ok | exact T1_fail0_eq | exact T1_fail_eq | exact imp_ad1_fail | innth 5 | innth 6 | lia | lia].
Qed.
Lemma X_E_ad2 : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0S39S3bZ88S3cZ2Z40A2A2R2A2VTR;S67S38VJAv;ScdA1Sb2R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd2.
  apply (X_FIN2 1 vFV E_ad2_0 E_ad2 T2_ok0 T2_ok T2_fail0 T2_fail s_ad2 R_ad2 135 rho tp b tp0 eq_refl);
    [vmr|vmr|vmr|vmr| exact E_ad2_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact T2_ok0_eq | exact T2_ok_eq | exact imp_ad2_ok | exact T2_fail0_eq | exact T2_fail_eq | exact imp_ad2_fail | innth 8 | innth 9 | lia | lia].
Qed.
Lemma X_E_ad3 : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0S39S3bZ7eS3cZ2Z40A2A2R2A2VTR;S67S38VJAv;SceA1Sb3R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd3.
  apply (X_FIN3 2 vMM E_ad3_0 E_ad3 T3_ok0 T3_ok T3_fail0 T3_fail s_ad3 R_ad3 125 rho tp b tp0 eq_refl);
    [vmr|vmr|vmr|vmr| exact E_ad3_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact T3_ok0_eq | exact T3_ok_eq | exact imp_ad3_ok | exact T3_fail0_eq | exact T3_fail_eq | exact imp_ad3_fail | innth 11 | innth 12 | lia | lia].
Qed.
Lemma X_E_ad4 : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0S39S3bZ74S3cZ2Z40A2A2R2A2VTR;S67S38VJAv;ScfA1Sb4R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd4.
  apply (X_FIN4 3 vSG E_ad4_0 E_ad4 T4_ok0 T4_ok T4_fail0 T4_fail s_ad4 R_ad4 115 rho tp b tp0 eq_refl);
    [vmr|vmr|vmr|vmr| exact E_ad4_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact T4_ok0_eq | exact T4_ok_eq | exact imp_ad4_ok | exact T4_fail0_eq | exact T4_fail_eq | exact imp_ad4_fail | innth 14 | innth 15 | lia | lia].
Qed.

Lemma bofs_val : ltac2:(tb__ "0|0|
S1aS15S39S5fR2S70A2S79A2S1S39Z0R2A2S39R2Z518A2A2S0S15S5fR4Sa1R3A1A2S3aS5fR4S70A2R3A2A3F_;F_;Fk;Frho;").
Proof.
  intros rho k Hb Hk. unfold bofs, two47, RA.two47 in *. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Lemma X_VF : ltac2:(tb__ "0|1a|
S10S6cS10S33S33S33S33S33S33S33S33SfdS5S20A1M0S15S1aS5S58Q40A1A1M1S15G1S0SdS6cA1S5cS6cS80R12A3SaS6cR11A2A3S0SdS33A1M2SddR10SdbR11S9bR12A1A2A2SaS33RfA2A3S0S4S5aS19S1cS1dS6bR13A1S6dR13A1A2A1S1bS34R10A1A1A3S3A3S0S4S5aS19S1cS1dS6dR14A1S1eS7aA1A2A1S1bS34R11A1A1A3S3A3S0S4S5aS19S1cS1dS70S1eS79A1A2A1S1bS34R12A1A1A3S3A3S0S4Sf7S88R16A1S35R13A1A2S3A3S0SdG0A1Se4R14S7fRdA3SaG0RcA2A3S0S4Se3R15S7fReRdS102S6S33S40A2M3S33S11S33S40A2S95A4A5S3A3S0S4S120S6aRfA2S3A3S0S4S10eR10SdcA2S3A3S0S4S109S6aS1fS34R18A1A1A2S3A3S0S4S47S1fS34R19A1A1S44S8S6S18S18A2M4SdeSbG4S7S18S18S89S1eZ40M5A1A4ScG4A1A3M6A3ScS6S6S18S15A2S18A2A1M7S8S5eS76R1cS6bR1cA1A2S8S5eS6eS9R1dA1S6fA2S8aS77S7eA2M8A3A3S42S72S3A2M9A4A2S3A3S0S4S63S1fS34R1aA1A1S8S5eS6eS9R1eA1S6fA2G8A3A2S3A3S0S4SedR14G6S126A3S3A3S0S4S48S43R15S127A2G9A2S3A3S0S4S12fS1bS34R1dA1A1S1eZ0MaA1GaS8S5eS76R20S6bR20A1A2S8S5eS6eS9R21A1S6fA2G8A3MbA3S8S5eS60R16S161A2GbA3A5S3A3S0S4S5dSf6Sf5S7fSdcR17S1fS34R1eA1A1A4S95A3S3A3S0S4S10cS1bS34R1fA1A1SdeG7S12S10A1McSe7R17A6S3A3S0S4S10bVXGL;S1bS34R20A1MdA1SdeG7GcS21GdA1Se8S88R23A1A8S3A3S0S18SfcR1aPcA2Sa1S9bR24A1A1A3S0S18SfcR1bPfA2S8dR25A1A3S0S18SfcR1cP11A2S74S82R26A1S6dR26A1A2A3S1S39GaS9bR27A1MeA2S39S3aGeZ20A2Z518A2A2S0G2SddSf3S7fR25R1eR1dS12aS88R28A1A6SafR27S9R29A1A2A2SaS33R24A2A3S1S0S5G4A1MfSecS114R26R1fS12aA3M10S126A2G6A3S1S0S45S43G10S127A2G9A3S0S5S5eA1M11S60G10S161A2S76R29S6bR29A1A2A3A2A2S0S33S11dSbS19ScbScS19A1A3M12R26A2R25A3S0S4S36R27R26S7cR27A1A3S3A3S0S4S100S7cR28A1S6aA2S3A3S0S4S109S6aS1fS34R29A1A1A2S3A3S0S4S47S1fS34R2aA1A1S7bS9R2fA1R2eA2A2S3A3S0S4SedS7cR2bA1S78S78A3S3A3S0S4S130S1bS34R2cA1A1S60S7cR2cA1S4aS7bS9R31A1R30A2A1M13A2G13A3S3A3S0S4S48S43S7cR2dA1G9A2G9A2S3A3S0G2SddSf3S7fR2fR28R27S12bS88R32A1A6SafR31S9R33A1A2A2SaS33R2cA2A3S1S0GfSecS114R30R29S12bA3M14S126A2G6A3S1S0S45S43G14S127A2G9A3S0G11S60G14S161A2S76R33S6bR33A1A2A3A2A2S0S33S11dG12R2eA2R2dA3S0S4S36R2fR2eS7cR2fA1A3S3A3S0S4S100S7cR30A1S6aA2S3A3S0S4S109S6aS1fS34R31A1A1A2S3A3S0S4S47S1fS34R32A1A1S7bS9R39A1R38A2A2S3A3S0S4SedS7cR33A1S78S78A3S3A3S0S4S130S1bS34R34A1A1S60S7cR34A1S4aS7bS9R3bA1R3aA2A1M15A2G15A3S3A3S0S4S48S43S7cR35A1G9A2G9A2S3A3S0G2SddSf3S7fR39R32R31S128S88R3cA1A6Sb0R3bS9R3dA1A2A2SaS33R34A2A3S1S0GfSecS114R3aR33S128A3M16S126A2G6A3S0S45S43G16S42S12dSeA2A2S42S72SeA2A3A2S0G2SddSf3S7fR3bR34R33S129S88R3eA1A6Sb0R3dS9R3fA1A2A2SaS33R35A2A3S1S0GfSecS114R3cR35S129A3M17S126A2G6A3S0S45S43G17S42S12cS3A2A2S42SabS3A2A3A2S5bS6G3S6S15S18A2M18A2M19S7G3G18S7S33S40R3bS7bS9R41A1R40A2A4S7S15S18R34S75A4A4S73A3S5bG19S7G3G18S7S33S40R3aS7bS9R42A1R41A2A4S7S15S18R35S75A4A4S73A3S5bG19S7G3G18S7S33S40R3aS8bS9R43A1S72A2A4S7S15S18R36S75A4A4S73A3S5bG19S7G3G18S7S33S40R3aS8cS9R44A1SabA2A4S7S15S18R37S75A4A4S73A3S39GaR38A2S39S3bS3aR39Z1A2S3cZ2G5A2A2R36A2VTR;S67S38VJAv;S44S78G7S8S5eS6eR47S6fA2G8A3G9A4A1R44R39R38A5VFAM;R37R36A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FrkT;FR;Fs;FTok;FTf;FTz2G;FTz2;FTzG;FTz;FE;FE0;Fpidx;Fv;Fj;").
Proof.
  intros j v pidx E0 E Tz TzG Tz2 Tz2G Tf Tok s R rkT rho tp b tp0 Hj HE Hck HkB Hb47 HXk He Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham Hpay Hpd HR HX Hs12 Hs15 Hs17 Hoff
         HTz Himp_z HTzG Hze Hzid Hznp Hznb Hztv Hzbd Hzam HTy Himp_y HTyG Hye Hyid Hynp Hynb Hytv Hybd Hyam HTf Himp_f HTok Himp_ok HinZ HinY HinF HinOk Hrk Hb.
  assert (Hv : In v fins) by (eapply nth_error_In; exact Hj).

  eapply TR_pre with (P := SPA segs (JAv (NDA tv0 [] (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) (AHead vHq true))) E rho tp).
  { intros w Hw. pose proof (SPA_axforms segs _ _ rho _ E tp w HE Hw) as Hw2.
    apply (JA_repay segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue tv0 [] (CHfrom j cs0 ++ bd_push sh_c sh_k)
             (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) (AHead vHq true) E rho tp w); [|exact Hw2].
    exact (pay_fin j v (ss_facts (ax_S E)) (bd_push sh_c sh_k) Hj eq_refl Hck HkB). }

  unfold tv0. change (map Xof fins ++ [Xof vSH; (vAR, SLit 64)]) with (keptF ++ [(vAR, SLit 64)]).
  change (CHf v (vd_c v) ++ [finV (S j); finK (S j)] ++ bd_push sh_c sh_k) with (CHf v (vd_c v) ++ CHfrom (S j) cs0 ++ bd_push sh_c sh_k).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc HBX (VFP.P0_vf CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_vf VFZ.nd0z PD_vf NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVF eq_refl
           E s R (Xk_vf v) rho tp keptF [(vAR, SLit 64)] [] _ (CHfrom (S j) cs0 ++ bd_push sh_c sh_k) (AHead vHq true) (FAM b tp0)
           HXk He Hchk Hta Hdom Hnp Hnb Hbb Htvs Ham).
  - apply (payA_of_bud_pay2 NP rho0 (P0_fs FB FF)). exact Hpay.
  - exact Hpd.
  - intros Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    destruct (tvx_app_l Ai rho keptF _ HN HD HZ) as (HN1 & HD1 & HZ1).
    destruct (site_client E R (Xk_vf v) keptF rho Ai rho1 tp1 md1 HM HF HP0 Hav HT HTK HN1 HD1 HZ1 HFR Hb47 HR HX) as [A B].
    split; [exact A|]. split; [exact B|].
    destruct (P0_now rho Hav HP0) as [PB PA].
    pose proof (holds_mem _ _ _ HF Hb47) as F47. zf F47. unfold two47, RA.two47 in F47. rewrite uval_lit in F47 by lia.
    unfold VFP.P0_vf. unfold uval, VF.vV, VF.vD, VF.vL. cbn [eval]. rewrite !rw_call', Hs12, Hs15, Hs17.
    change (bv_unsigned (eval rho (bofs (vd_off v)))) with (uval rho (bofs (vd_off v))). rewrite (bofs_val rho (vd_off v)) by (unfold two47, RA.two47; lia).
    split.
    + intros a Ha. eapply (infrFF_pclMA CST _ FF); [exact PB | lia].
    + change (bv_unsigned (eval rho (vd_d v))) with (uval rho (fst (Xof v))). change (bv_unsigned (eval rho (kb (vd_el v) (vd_k v)))) with (uval rho (snd (Xof v))).
      assert (HinK : In (Xof v) keptF) by (apply in_or_app; left; apply in_map; exact Hv).
      destruct (Z.eq_dec (uval rho (fst (Xof v))) 0) as [Hz|Hnz].
      * left. pose proof (proj1 (Forall_forall _ _) HZ1 (Xof v) HinK) as X. cbv beta in X. unfold tnz, tvv in X. cbn [snd] in X.
        unfold uval in *. apply X. intros Y. exact (Y Hz).
      * right; left. exists (fst (tvv rho (Xof v))), (snd (tvv rho (Xof v))). split; [|unfold tvv; cbn [fst snd]; unfold uval; lia].
        apply In_FBx. right. exists (Xof v). split; [exact HinK|]. split; [exact Hnz | symmetry; apply surjective_pairing].
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vf In] in Hd.
    destruct Hd as [Hd|[Hd|[Hd|[Hd|[]]]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am VFZ.nd0z VF.nd_fail VF.nd_ok VF.nd0];
      fold (isub_vf E s VF.P_zero); fold (isub_vf E s VF.P_fail); fold (isub_vf E s VF.P_ok); fold (isub_vf E s VF.P_zero2).
    +
      destruct Himp_z as (Hi1 & Hi2 & Hi3). rewrite Hi1, Hi2, Hi3.
      eapply TR_pre; [|apply (REENTER TzG (ndTz (S j) v) (rkT, z0) (rho_sub rho' (s_gh Tz))); [exact HinZ | rewrite emeas_z0; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ _ rho' _ Tz tp' w HTz Hw) as Hw1. subst TzG.
      apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc Tz (ax_add_facts [ghZ] Tz) (s_gh Tz) (ndTz (S j) v) (ndTz (S j) v));
        [exact Hze | exact Hzid | exact Hznp | exact Hznb | exact Hztv | reflexivity | exact Hzbd | exact Hzam |].
      unfold ndTz, tv0. exact Hw1.
    +   rewrite (proj1 Himp_f), (proj2 Himp_f). change (bd_subst _ [] ++ ?r) with r.
      eapply TR_pre; [|apply (REENTER Tf (ndTf (S j) vHq) (rkT, z0) rho'); [exact HinF | rewrite emeas_z0; lia]].
      intros w Hw. exact (SPA_axforms segs _ _ rho' _ Tf tp' w HTf Hw).
    +   rewrite (proj1 Himp_ok), (proj2 Himp_ok). change (bd_subst _ [] ++ ?r) with r.
      eapply TR_pre; [|apply (REENTER Tok (ndTok (S j) vHv) (rkT, z0) rho'); [exact HinOk | rewrite emeas_z0; lia]].
      intros w Hw. exact (SPA_axforms segs _ _ rho' _ Tok tp' w HTok Hw).
    +
      destruct Himp_y as (Hi1 & Hi2 & Hi3). rewrite Hi1, Hi2, Hi3.
      eapply TR_pre; [|apply (REENTER Tz2G (ndTz (S j) v) (rkT, z0) (rho_sub rho' (s_gh Tz2))); [exact HinY | rewrite emeas_z0; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ _ rho' _ Tz2 tp' w HTy Hw) as Hw1. subst Tz2G.
      apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc Tz2 (ax_add_facts [ghZ] Tz2) (s_gh Tz2) (ndTz (S j) v) (ndTz (S j) v));
        [exact Hye | exact Hyid | exact Hynp | exact Hynb | exact Hytv | reflexivity | exact Hybd | exact Hyam |].
      unfold ndTz, tv0. exact Hw1.
Qed.
Lemma X_E_vf5 : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0S39S3bZ6aS3cZ2Z40A2A2R2A2VTR;S67S38VJAv;Sd0A1Sb9R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd5.
  apply (X_VF 4 vLI 12 E_vf5_0 E_vf5 T5_z T5_zG T5_z2 T5_z2G T5_f T5_ok s_vf5 R_vf5 105 rho tp b tp0 eq_refl E_vf5_eq);
    [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| cbn; lia
    | exact T5_z_eq | exact imp_vf5_z | exact T5_zG_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact T5_z2_eq | exact imp_vf5_z2 | exact T5_z2G_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact T5_f_eq | exact imp_vf5_f | exact T5_ok_eq | exact imp_vf5_ok | innth 17 | innth 20 | innth 19 | innth 18 | lia | lia].
Qed.
Lemma X_E_vf6 : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0S39S3bZ60S3cZ2Z40A2A2R2A2VTR;S67S38VJAv;Sd1A1SbaR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd6.
  apply (X_VF 5 vLC 13 E_vf6_0 E_vf6 T6_z T6_zG T6_z2 T6_z2G T6_f T6_ok s_vf6 R_vf6 95 rho tp b tp0 eq_refl E_vf6_eq);
    [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| cbn; lia
    | exact T6_z_eq | exact imp_vf6_z | exact T6_zG_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact T6_z2_eq | exact imp_vf6_z2 | exact T6_z2G_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact T6_f_eq | exact imp_vf6_f | exact T6_ok_eq | exact imp_vf6_ok | innth 22 | innth 25 | innth 24 | innth 23 | lia | lia].
Qed.
Lemma X_E_vf7 : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0S39S3bZ56S3cZ2Z40A2A2R2A2VTR;S67S38VJAv;Sd2A1SbbR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd7.
  apply (X_VF 6 vPI 14 E_vf7_0 E_vf7 T7_z T7_zG T7_z2 T7_z2G T7_f T7_ok s_vf7 R_vf7 85 rho tp b tp0 eq_refl E_vf7_eq);
    [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| cbn; lia
    | exact T7_z_eq | exact imp_vf7_z | exact T7_zG_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact T7_z2_eq | exact imp_vf7_z2 | exact T7_z2G_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact T7_f_eq | exact imp_vf7_f | exact T7_ok_eq | exact imp_vf7_ok | innth 27 | innth 30 | innth 29 | innth 28 | lia | lia].
Qed.

Lemma kb_val : ltac2:(tb__ "0|0|
S1aS15S18S1S39Z1R2A2S39R2Z80A2A2S39S5fR4R2A2S7aA2S0S15S5fR5S74R4R3A2A2S3bR4S5fR5R3A2A2A3F_;F_;Fk;Fe;Frho;").
Proof. intros rho e k He Hk. unfold kb, B32, Lib_vec_reserve.B32 in *. pose proof (uval_range rho k). apply uval_mul_lit; nia. Qed.

Lemma X_E_vp : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0S39S3bZ4cS3cZ2Z40A2A2R2A2VTR;S67S38VJAv;Sd3A1SbcR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd8, tv0.
  eapply TR_pre with (P := SPA segs (JAv (NDA (keptP ++ [Xof vSH]) [] (bd_push sh_c sh_k) (AHead vHq true))) E_vp rho tp).
  { intros w Hw. apply (SPA_axforms segs _ _ rho _ E_vp tp w E_vp_eq).
    unfold keptP. rewrite <- app_assoc. cbn [app]. apply (SPA_tv_swap (map Xof fins) (Xof vSH) (vAR, SLit 64)). exact Hw. }
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc HBX VPP.P0_vp PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_vp (ndh hVP true VP.ndp0) (PDh PD_vp hVP true) NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVP eq_refl
           E_vp s_vpH R_vp Xk_vp rho tp keptP [Xof vSH] [] _ [] (AHead vHq true) (FAM b tp0)).
  - vmr.
  - exact R_vp_eqH.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - apply (payA_of_bud_pay2 NP rho0 (P0_fs FB FF)). vmr.
  - vmr.
  - intros Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    destruct (tvx_app_l Ai rho keptP _ HN HD HZ) as (HN1 & HD1 & HZ1).
    destruct (site_client E_vp R_vp Xk_vp keptP rho Ai rho1 tp1 md1 HM HF HP0 Hav HT HTK HN1 HD1 HZ1 HFR ltac:(vmr) ltac:(vmr) ltac:(vmr)) as [A B].
    split; [exact A|]. split; [exact B|].
    destruct (P0_now rho Hav HP0) as [PB PA].
    factz HF (SPUle vB (SLit two47)) F47. unfold two47, RA.two47 in F47. rewrite uval_lit in F47 by lia.
    factz HF (SPUle sh_k (SLit B32)) FK. unfold B32, Lib_vec_reserve.B32 in FK. rewrite uval_lit in FK by lia.
    unfold VPP.P0_vp. rewrite !rw_call'. change (wsub_get s_vpH 17) with sh_k. change (wsub_get s_vpH 15) with sh_d.
    change (wsub_get s_vpH 12) with (bofs 448). change (wsub_get s_vpH 13) with vAL.
    change (bv_unsigned (eval rho (bofs 448))) with (uval rho (bofs 448)). rewrite (bofs_val rho 448) by (unfold two47, RA.two47; lia).
    split; [|split].
    + intros HK HD0. pose proof (proj1 (Forall_forall _ _) HZ (Xof vSH) ltac:(apply in_or_app; right; left; reflexivity)) as X. cbv beta in X.
      unfold tnz, tvv in X. cbn [fst snd Xof vSH vd_d vd_k vd_el] in X. specialize (X ltac:(intros Y; exact (Y HD0))).
      change (bv_unsigned (eval rho (kb 128 sh_k))) with (uval rho (kb 128 sh_k)) in X. rewrite kb_val in X by (unfold B32, Lib_vec_reserve.B32; lia).
      unfold uval in X. lia.
    + destruct PB as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin | lia].
    + destruct PA as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin | unfold uval in H1, H2; lia].
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PDh PD_vp map In] in Hd.
    destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am ndh VP.ndp0 VP.ndpG ND]; fold (isub_vp VP.P_push_keep); fold (isub_vp VP.P_push_fail); fold (isub_vp VP.P_push_grown).
    +   destruct imp_vp_keep as (Hi1 & Hi2 & Hi3). cbn [nd_tv nd_bd VP.ndp0 ND] in Hi1, Hi2. rewrite T_pk0_eqH, Hi1, Hi2, Hi3, app_nil_r.
      eapply TR_pre; [|apply (REENTER T_pkF ndPk (75, z0) rho'); [innth 32 | rewrite emeas_z0; lia]].
      intros w Hw. unfold keptP in Hw. rewrite <- app_assoc in Hw. cbn [app] in Hw. apply (SPA_tv_swap (map Xof fins) (vAR, SLit 64) (Xof vSH)) in Hw.
      pose proof (SPA_axforms segs _ _ rho' _ T_pk tp' w T_pk_eq Hw) as Hw1.
      rewrite <- T_pkF_eq. apply (SPA_refacts_JA segs); [exact Hw1 | vmr |].
      intros tr md HJ HF2.
      assert (TNZ : tnz rho' (Xof vSH)).
      { factz HF2 (SPUle (SAlu ALU_ADD sh_c (SLit 1)) sh_k) F1. factz HF2 (SPUle sh_k (SLit B32)) F2. unfold B32, Lib_vec_reserve.B32 in F2. rewrite uval_lit in F2 by lia.
        factz HF2 (SPUle sh_c sh_k) F0.
        pose proof (uval_range rho' sh_c). rewrite uval_add_small in F1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F1 by lia.
        intros Hz. pose proof (JA_null_size0 AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue _ rho' tp' tr md (Xof vSH) HJ ltac:(apply in_or_app; right; left; reflexivity) Hz) as Z0.
        cbn [snd Xof vSH vd_el vd_k] in Z0. change (bv_unsigned (eval rho' (kb 128 sh_k))) with (uval rho' (kb 128 sh_k)) in Z0. rewrite kb_val in Z0 by (unfold B32, Lib_vec_reserve.B32; lia). lia. }
      pose proof (JA_tv_facts segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue ALA _ _ _ _ _ (Xof vSH) eq_refl HJ ltac:(apply in_or_app; right; left; reflexivity) TNZ) as TF.
      constructor; [|constructor; [|exact HF2]].
      * apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA, hse_fact. cbn [fst snd Xof vSH vd_d]. do 5 right. left. reflexivity.
      *
        apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA, top_factK. cbn [fst snd Xof vSH vd_d vd_k vd_el]. do 2 right. left. reflexivity.
    +   destruct imp_vp_fail as [Hi1 Hi2]. rewrite T_pf0_eqH, Hi1, Hi2. change (bd_subst _ [] ++ []) with (@nil bitem).
      eapply TR_pre; [|apply (REENTER T_pf ndPf (75, z0) rho'); [innth 33 | rewrite emeas_z0; lia]].
      intros w Hw. unfold keptP in Hw. rewrite <- app_assoc in Hw. cbn [app] in Hw. apply (SPA_tv_swap (map Xof fins) (vAR, SLit 64) (Xof vSH)) in Hw.
      exact (SPA_axforms segs _ _ rho' _ T_pf tp' w T_pf_eq Hw).
    +   destruct imp_vp_grown as (Hi1 & Hi2 & Hi3). cbn [nd_tv nd_bd VP.ndpG ND] in Hi1, Hi2. rewrite T_pg0_eqH, Hi1, Hi2, Hi3, app_nil_r.
      eapply TR_pre; [|apply (REENTER T_pgF ndPg (75, z0) rho'); [innth 34 | rewrite emeas_z0; lia]].
      intros w Hw. unfold keptP in Hw. rewrite <- app_assoc in Hw. cbn [app] in Hw. apply (SPA_tv_swap (map Xof fins) (vAR, SLit 64) (vDg, kb 128 vKg)) in Hw.
      pose proof (SPA_axforms segs _ _ rho' _ T_pg tp' w T_pg_eq Hw) as Hw1.

      rewrite <- T_pgF_eq. apply (SPA_refacts_JA segs); [exact Hw1 | vmr |].
      intros tr md HJ HF2. constructor; [|exact HF2].
      assert (TNZ : tnz rho' (vDg, kb 128 vKg)).
      { factz HF2 (SPNot (SPBranch BC_EQ vDg (SLit 0))) F0. rewrite uval_lit in F0 by lia. unfold tnz. cbn [fst]. unfold uval in F0. exact F0. }
      pose proof (JA_tv_facts segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue ALA _ _ _ _ _ (vDg, kb 128 vKg) eq_refl HJ ltac:(apply in_or_app; right; left; reflexivity) TNZ) as TF.
      apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA, top_factG. cbn [fst snd]. do 2 right. left. reflexivity.
Qed.

Lemma slot_rng : ltac2:(tb__ "0|d|
S1aS5S19A1S18S18S101S19S23R4A1R3A3S0S4S5aS19S1cS1dR3S27P1eA1M0A2A1R4A3S3A3S0S4S5aS19S1cS1dS22S103R4S74Z80M1R3A2A3G0A2A1R5A3S3A3S0S4S5aS19S1cS1dS22S103S77S1eZ1A1A3R4A2A1R6A3S3A3S0S4S5aS19S1cS1dR5S1eS7aA1M2A2A1R7A3S3A3S0S4S5aS19S1cS1dS77S7eA2A1R8A3S3A3S0S4S5aS19S1cS1dS7eG2A2A1R9A3S3A3S0S4S5aS19S1cS1dG0S1eZ7fffff800000M3A1A2A1RaA3S3A3S1S0S15S5fRcS74G1S77A2M4A2S3bG1S5fRcS77A2A2M5A3S1S0S15S2aRcS22S103G4S1eZ38M6A1M7A3A2S3aG5G6A2A3S1S0S15S2aRcS22S103G4S1eZ48M8A1A3A2S3aG5G8A2A3S1S0S15S5fRcSa9RaA1M9A2S3aS5fRcRaA2MaG5A2MbA3S1S0S15S5fRcS22S103G9G7A3A2S3aGbG6A2A3S1S39S3aG5G1A2S3bG1S5fRcR9A2A2McA2S1S0S15S5fRcS74G1R9A2A2GcA3S39S3aGaGcA2G3A2A2A2A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;Fk;Fd;FF;Fr;").
Proof.
  intros r F d k HF H1 H2 H3 H4 H5 H6 H7.
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  pose proof (holds_mem _ _ _ HF H4) as F4. pose proof (holds_mem _ _ _ HF H5) as F5. pose proof (holds_mem _ _ _ HF H6) as F6.
  pose proof (holds_mem _ _ _ HF H7) as F7.
  zf F1. zf F2. zf F3. zf F4. zf F5. zf F6. zf F7. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in *.
  unfold B32, Lib_vec_reserve.B32 in *. rewrite uval_lit in F4 by lia. rewrite uval_lit in F6 by lia. rewrite uval_lit in F7 by lia.
  pose proof (uval_range r sh_c) as RC. pose proof (uval_range r d) as Rd. pose proof (uval_range r k) as Rk.
  rewrite uval_add_small in F3 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F3 by lia.
  assert (EK : uval r (kb 128 k) = 128 * uval r k) by (apply kb_val; unfold B32, Lib_vec_reserve.B32; lia).
  assert (EC : uval r (kb 128 sh_c) = 128 * uval r sh_c) by (apply kb_val; unfold B32, Lib_vec_reserve.B32; lia).
  rewrite uval_add_small in F2 by (rewrite EK; lia). rewrite EK in F2.
  assert (A56 : uval r (SAlu ALU_ADD (kb 128 sh_c) (SLit 56)) = 128 * uval r sh_c + 56) by (rewrite uval_add_small by (rewrite EC, uval_lit by lia; lia); rewrite EC, uval_lit by lia; lia).
  assert (A72 : uval r (SAlu ALU_ADD (kb 128 sh_c) (SLit 72)) = 128 * uval r sh_c + 72) by (rewrite uval_add_small by (rewrite EC, uval_lit by lia; lia); rewrite EC, uval_lit by lia; lia).
  assert (AS : uval r (slotx d) = uval r d + 128 * uval r sh_c) by (unfold slotx; rewrite uval_add_small by (rewrite EC; lia); rewrite EC; lia).
  split; [exact EC|]. split; [rewrite soff_smallu by (rewrite A56; lia); exact A56|]. split; [rewrite soff_smallu by (rewrite A72; lia); exact A72|].
  split; [exact AS|]. split; [rewrite uval_add_small by (rewrite AS, uval_lit by lia; lia); rewrite AS, uval_lit by lia; lia|]. lia.
Qed.
Definition slotF (F : list sprop) (d k : sv) : bool := ltac2:(tb__ "0|2|
SfSfSfSfSfSfS5aS19S1cS1dVd;S27P1eA1M0A2A1VF;A3S5aS19S1cS1dS22S103Vd;S74Z80Vk;A2A3G0A2A1VF;A3A2S5aS19S1cS1dS22S103S77S1eZ1A1A3Vk;A2A1VF;A3A2S5aS19S1cS1dVk;S1eS7aA1M1A2A1VF;A3A2S5aS19S1cS1dS77S7eA2A1VF;A3A2S5aS19S1cS1dS7eG1A2A1VF;A3A2S5aS19S1cS1dG0S1eZ7fffff800000A1A2A1VF;A3A2").
Lemma slot_rngF : ltac2:(tb__ "0|a|
S1aS5S19A1S18S18S101S19S23R4A1R3A3S0S4S15fR4R3R2A3S3A3S1S0S15S5fR6S74Z80M0S77A2M1A2S3bG0S5fR6S77A2A2M2A3S1S0S15S2aR6S22S103G1S1eZ38M3A1M4A3A2S3aG2G3A2A3S1S0S15S2aR6S22S103G1S1eZ48M5A1A3A2S3aG2G5A2A3S1S0S15S5fR6Sa9R4A1M6A2S3aS5fR6R4A2M7G2A2M8A3S1S0S15S5fR6S22S103G6G4A3A2S3aG8G3A2A3S1S39S3aG2G0A2S3bG0S5fR6R3A2A2M9A2S1S0S15S5fR6S74G0R3A2A2G9A3S39S3aG7G9A2Z7fffff800000A2A2A2A2A2A2A2A2F_;F_;Fk;Fd;FF;Fr;").
Proof.
  intros r F d k HF H. unfold slotF in H. repeat (apply andb_prop in H as [H ?]).
  eapply slot_rng; eassumption.
Qed.

Definition spF (F : list sprop) : bool := ltac2:(tb__ "0|0|
S5aS19S1cS1dS1eZ7fff7f800000A1S27PaA1A2A1VF;A3").
Lemma sp232 : ltac2:(tb__ "0|1|
S1aS5S19A1S101S19S23R2A1R1A3S0S4S160R2A1S3A3S0S15S5fR4Sd7Ze8M0A1A2S3fS5fR4S27PaA1A2G0A2A3F_;F_;FF;Fr;").
Proof.
  intros r F HF H. pose proof (holds_mem _ _ _ HF H) as F1. zf F1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in *. rewrite uval_lit in F1 by lia.
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_arena_alloc_pf.uval_spm r 232). lia.
Qed.

Lemma X_MC : ltac2:(tb__ "0|c|
S33S33S33S33S33S5S20A1M0S18S18S40S1aS5S58Q40A1A1M1S15G1S0SdS33A1M2SddRdSdaA2SaS33RcA2A3S0S33Sb5RdR8A2RcA3S0SdS20A1M3S5cS20S21S34ReA1A1U1fM4A3SaS20S98R9A1A2A3S0G3S5cS20S21S34S37RfS168S34RfA1G4S97RaA1A3A2A1A1U1M5A3SaS20Sa4A2A3S0S4S29S1fS34R10A1A1S97RbA1A2S3A3S0S4S29S1fS34R11A1A1SaaA2S3A3S0S4S15fS1bS34R12A1A1RdRcA3S3A3S0S4S160S1bS34R13A1A1A1S3A3S0SdG0A1Se4R13S90S93R13RfReA3A3SaG0R10A2A3S0S4Se3R14S90S93R14R10RfA3R11SbS33S8eSbS33S8eScS33A1A3A3A5S3A3S0S4S120S6aS93R15R11R10A3A2S3A3S0S4S109S6aS1fS34R16A1A1A2S3A3S0S4S47S1fS34R17A1A1R11A2S3A3S0S4S63S1fS34R18A1A1S4aR12A1A2S3A3S0S4S64S4aR13A1A1S3A3S0S5S6S6S18S15A2S18A2M6A1S55R14A1ScG6A1M7A3S0S4S5aS19S1cS1dS70S1eS79A1A2A1S1bS34R1bA1A1A3S3A3S0S4S10cS1bS34R1cA1A1S4bR16A1G7S12S10A1M8Se7R19A6S3A3S0S4S10bVXGL;S1bS34R1dA1M9A1S4bR17A1G7G8S21G9A1Se8S35R1dA1A8S3A3S0S33S122S90R1eS93R1eR1aR19A3R1bS8eA5R1dA3S0G3S5cS20S21S34R1eA1A1G5A3SaS20S97R1bA1A2A3S0G3S5cS20S21S34S37R1fS168S34R1fA1G5S98R1cA1A3A2A1A1U2A3SaS20SaaA2A3S0S4S29S1fS34R20A1A1S98R1dA1A2S3A3S0S4S29S1fS34R21A1A1Sa4A2S3A3S0S4S15fS1bS34R22A1A1R1fR1eA3S3A3S0S4S160S1bS34R23A1A1A1S3A3S0G2SddSc8R24R21A2Sd9A2SaS33R23A2A3S5bS6S6S33S40A2MaS6S15S18A2MbA2S7GaGbS7S33S40R24R20A4S7S15S18Z41S75A4A4S73A3S39S3bZ42S3cZ2Z40A2A2R1eA2VTR;S67S38VJAv;R22A1R2aR21R20A5VFAM;R1fR1eA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fnd;Fk;Fd;FR;FTm;FTm0;FE;FE1;FE0;").
Proof.
  intros E0 E1 E Tm0 Tm R d k nd rho tp b tp0 HE1 HE Hn31 Hn1 Hwf Hwfs HSF HSP He Hchk Hta Hnp Hnb Hbb Hwp Hfr H47 HR HX HTm0 Hm1 Hm2 Hwf2 Hwf2s HSF2 HSP2 HTm HinM Hb.
  eapply TR_pre with (P := SPA segs (JAv nd) E rho tp).
  { intros w Hw. pose proof (SPA_axforms segs _ xf_mcall rho E0 E1 tp w HE1 Hw) as Hw1. rewrite <- HE. unfold E_mc. cbv zeta.
    assert (Hw2 : SPA segs (JAv nd) (ax_setS E1 (reshape_obj_at (ax_S E1) 31 (dst_obj d))) rho tp w).
    { apply (SPA_reshape segs _ rho E1 31 _ _ tp w Hn31); [reflexivity | reflexivity | reflexivity | exact Hwf | | exact Hw1].
      intros HF. destruct (slot_rngF rho _ d k HF HSF) as (EC & A56 & A72 & AS & AS56 & Hck & EK & Hd).
      pose proof (uval_range rho sh_c) as RC. pose proof (uval_range rho d) as Rd. pose proof (uval_range rho k) as Rk.
      assert (A128 : uval rho (SAlu ALU_ADD (kb 128 sh_c) (SLit 128)) = 128 * uval rho sh_c + 128) by (rewrite uval_add_small by (rewrite EC, uval_lit by lia; lia); rewrite EC, uval_lit by lia; lia).
      unfold dst_obj, mid_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
      rewrite (soff_smallu rho (kb 128 sh_c)) by (rewrite EC; lia). rewrite (soff_smallu rho (SAlu ALU_ADD (kb 128 sh_c) (SLit 128))) by (rewrite A128; lia). rewrite EC, A128.
      change (bv_unsigned (eval rho (slotx d))) with (uval rho (slotx d)). rewrite AS. unfold uval. lia. }
    apply (SPA_reshape segs _ rho _ 1 _ _ tp w Hn1); [reflexivity | reflexivity | reflexivity | exact Hwfs | | exact Hw2].
    intros HF. pose proof (sp232 rho _ HF HSP) as E232.
    unfold src_obj, fmid_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
    change (bv_unsigned (eval rho (spm 232))) with (uval rho (spm 232)). rewrite E232. unfold uval. lia. }
  destruct nd as [tvN frN bdN amN]. cbn [nd_tv nd_fr nd_bd nd_am] in *. subst frN.
  apply (purec_callT_ag_xp segs AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memcpy Pre_mc [L_mc; L_mc] E (s_m E d k) R rho tp (NDA tvN [] bdN amN) bdN (FAM b tp0)).
  - intros Ai rho1 tp1. cbn [map]. exact (CMEMCPY Ai rho1 tp1).
  - reflexivity.
  - reflexivity.
  - exact He.
  - exact Hchk.
  - exact Hta.
  - exact Hnp.
  - exact Hnb.
  - exact Hbb.
  - cbn [nd_bd]. apply payA_same. exact Hwp.
  - vmr.
  - intros Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
    destruct (site_rt E R tvN rho Ai rho1 tp1 md1 HM HF HP0 Hav HT HTK HBf HFF HN HD HZ HFR H47 HR HX) as [A B].
    split; [exact A|]. split; [exact B | exact I].
  - intros Ai tr ms md Hsm HM HX'. exact (XP_memcpy_site segs AInv CST XGL ALA HCST HXGL Ai E memcpy_pc (s_m E d k) R rho tp tr ms md Hsm HM HX' He).
  - intros L rho' tp' HL Hag. assert (EL : L = L_mc) by (destruct HL as [<-|[<-|[]]]; reflexivity). subst L. cbn [nd_tv nd_fr nd_am]. rewrite HTm0.
    eapply TR_pre; [|apply (REENTER Tm (NDA tvN [] bdN amN) (65, z0) rho'); [exact HinM | rewrite emeas_z0; lia]].
    intros w Hw.
    assert (Hw1 : SPA segs (JAv (NDA tvN [] bdN amN)) (ax_setS Tm0 (reshape_obj_at (ax_S Tm0) 1 (mid_obj d))) rho' tp' w).
    { apply (SPA_reshape segs _ rho' Tm0 1 _ _ tp' w Hm1); [reflexivity | reflexivity | reflexivity | exact Hwf2 | | exact Hw].
      intros HF. destruct (slot_rngF rho' _ d k HF HSF2) as (EC & A56 & A72 & AS & AS56 & Hck & EK & Hd).
      pose proof (uval_range rho' sh_c) as RC. pose proof (uval_range rho' d) as Rd. pose proof (uval_range rho' k) as Rk.
      assert (A128 : uval rho' (SAlu ALU_ADD (kb 128 sh_c) (SLit 128)) = 128 * uval rho' sh_c + 128) by (rewrite uval_add_small by (rewrite EC, uval_lit by lia; lia); rewrite EC, uval_lit by lia; lia).
      unfold dst_obj, mid_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
      rewrite (soff_smallu rho' (kb 128 sh_c)) by (rewrite EC; lia). rewrite (soff_smallu rho' (SAlu ALU_ADD (kb 128 sh_c) (SLit 128))) by (rewrite A128; lia). rewrite EC, A128.
      change (bv_unsigned (eval rho' (slotx d))) with (uval rho' (slotx d)). rewrite AS. unfold uval. lia. }
    assert (Hw2 : SPA segs (JAv (NDA tvN [] bdN amN)) (T_mc1 Tm0 d) rho' tp' w).
    { unfold T_mc1. cbv zeta. apply (SPA_reshape segs _ rho' _ 2 _ _ tp' w Hm2); [reflexivity | reflexivity | reflexivity | exact Hwf2s | | exact Hw1].
      intros HF. pose proof (sp232 rho' _ HF HSP2) as E232.
      unfold src_obj, fmid_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
      change (bv_unsigned (eval rho' (spm 232))) with (uval rho' (spm 232)). rewrite E232. unfold uval. lia. }
    exact (SPA_axforms segs _ xf_mback rho' _ Tm tp' w HTm Hw2).
Qed.
Lemma X_E_mk : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0S39S3bZ42S3cZ2Z40A2A2R2A2VTR;S67S38VJAv;Sd5A1Sb7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_MC E_mk0 E_mk1 E_mk T_mk0 T_mk R_mk sh_d sh_k ndPk rho tp b tp0 E_mk1_eq E_mk_eq nth31_mk1 nth1_mk2);
    [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|reflexivity|reflexivity|vmr|vmr|vmr| exact T_mk0_eq | exact nth1_Tmk0 | exact nth2_Tmk1 |vmr|vmr|vmr|vmr| exact T_mk_eq | innth 35 | exact Hb].
Qed.
Lemma X_E_mg : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0S39S3bZ42S3cZ2Z40A2A2R2A2VTR;S67S38VJAv;Sd4A1Sb6R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_MC E_mg0 E_mg1 E_mg T_mg0 T_mg R_mg vDg vKg ndPg rho tp b tp0 E_mg1_eq E_mg_eq nth31_mg1 nth1_mg2);
    [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|reflexivity|reflexivity|vmr|vmr|vmr| exact T_mg0_eq | exact nth1_Tmg0 | exact nth2_Tmg1 |vmr|vmr|vmr|vmr| exact T_mg_eq | innth 36 | exact Hb].
Qed.

Lemma X_FL : ltac2:(tb__ "0|6|
S33S33S5S5eA1S18S1aS5S58Q40A1A1M0S15G0S5bS6S33Se1A2S7S33Se1R7SdfS92A1A4Se0A3S0S4S36R9R8S12eS6aS34R9A1M1S34R8A1A3A3S3A3S0S4S100S12eS6aS34RaA1G1A3S6aA2S3A3S0S4S109S6aS1fS34RbA1A1A2S3A3S0S4S47S1fS34RcA1M2A1S44S78ScS6S6S18S15A2S18A2A1M3RaS42R9SeA2A4A2S3A3S0S4SedS12eS6aS34RdA1M4G2A3S78S78A3S3A3S0S4S130S1bS34ReA1M5A1S60S12eS6aG5G4A3ScS5eA1A2RcA3S3A3S0S4S48S43S12eS6aS34RfA1G5A3S42Sd6SeA2A2S42RcSeA2A2S3A3VTR;S67S38VJAv;S44S78G3ReS42RdS3A2A4A1R10RcRbA5VFAM;RaR9A2A2F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fhq;Fbd;FP;FFL;").
Proof.
  intros FL P bd hq rho tp b tp0 HinP He Hid Hnp Hnb Htv Hbd Ham.
  eapply TR_pre; [|apply (POST P nd_fail_f (rho_sub rho (infer_sub NP (ax_S FL) (ax_S P))) tp b tp0 HinP)].
  intros w Hw. unfold nd_fail_f.
  apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc FL P _ (NDA tv0 [] bd (AHead hq false)) (NDA tv0 [] [] (AHead qHD false)));
    [exact He | exact Hid | exact Hnp | exact Hnb | exact Htv | reflexivity | exact Hbd | exact Ham |].
  apply (JA_pot_drop segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HBX). exact Hw.
Qed.
Tactic Notation "xfl" constr(P) integer(k) := intros; apply (X_FL _ P); [do k right; left; reflexivity |vmr|vmr|vmr|vmr|vmr|vmr|vmr].
Lemma X_FL_E0 : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0VTR;S67S38VJAv;S99A1Sc3R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndE, nd0. xfl P_failz 3. Qed.
Lemma X_FL_E1 : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0VTR;S67S38VJAv;S99A1Sc4R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndE, nd0. xfl P_fail 2. Qed.
Lemma X_FL_50 : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0VTR;S67S38VJAv;S7bU5SadA2A1SbdR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndTz. xfl P_fail 2. Qed.
Lemma X_FL_51 : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0VTR;S67S38VJAv;S7bU5SadA2A1SbeR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndTz. xfl P_failz 3. Qed.
Lemma X_FL_60 : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0VTR;S67S38VJAv;S7bU6SacA2A1SbfR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndTz. xfl P_fail 2. Qed.
Lemma X_FL_61 : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0VTR;S67S38VJAv;S7bU6SacA2A1Sc0R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndTz. xfl P_failz 3. Qed.
Lemma X_FL_70 : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0VTR;S67S38VJAv;S7bU7SaeA2A1Sc1R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndTz. xfl P_fail 2. Qed.
Lemma X_FL_71 : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0VTR;S67S38VJAv;S7bU7SaeA2A1Sc2R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndTz. xfl P_failz 3. Qed.
Lemma X_FL_p0 : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0VTR;S67S38VJAv;Sa6A1Sc5R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndPf. xfl P_fail 2. Qed.
Lemma X_FL_p1 : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0VTR;S67S38VJAv;Sa6A1Sc6R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;"). Proof. unfold ndPf. xfl P_failz 3. Qed.

Lemma X_E_nm : ltac2:(tb__ "0|1|
S1aS5S58Q40A1A1M0S15G0S39S3bZb5S3cZ2Z40A2A2R2A2VTR;S67S38VJAv;S99A1Sb8R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndE, nd0.
  eapply TR_pre with (P := SPA segs (JAv (NDA tv0 [] bd0 (AHead vHD true))) E_nm rho tp).
  { intros w Hw. exact (SPA_axforms segs _ (xf_call 64) rho _ E_nm tp w E_nm_eq Hw). }
  unfold tv0. change (map Xof fins ++ [Xof vSH; (vAR, SLit 64)]) with (keptF ++ [(vAR, SLit 64)]).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc HBX NMP.P0_aa PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_nm NM.nd0 NMP.PD_aa NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CNM eq_refl
           E_nm s_nm R_nm Xk_nm rho tp keptF [(vAR, SLit 64)] [] _ (CHfrom 0 cs0 ++ bd_push sh_c sh_k) (AHead vHD true) (FAM b tp0));
    [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| | | | ].
  - apply (payA_of_bud_pay2 NP rho0 (P0_fs FB FF)). vmr.
  - vmr.
  - intros Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    destruct (tvx_app_l Ai rho keptF _ HN HD HZ) as (HN1 & HD1 & HZ1).
    destruct (site_client E_nm R_nm Xk_nm keptF rho Ai rho1 tp1 md1 HM HF HP0 Hav HT HTK HN1 HD1 HZ1 HFR ltac:(vmr) ltac:(vmr) ltac:(vmr)) as [A B].
    split; [exact A|]. split; [exact B|]. exact I.
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [NMP.PD_aa In] in Hd.
    destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am NM.ndF NM.ndKc NM.nd0]; fold (isub_nm NM.P_fail); fold (isub_nm NM.P_ok).
    +   rewrite Tn_fail0_eq, (proj1 imp_nm_fail), (proj2 imp_nm_fail). change (bd_subst _ [] ++ ?r) with r.
      eapply TR_pre; [|apply (REENTER Tn_fail (ndTf 0 vHD) (180, z0) rho'); [innth 3 | rewrite emeas_z0; lia]].
      intros w Hw. exact (SPA_axforms segs _ _ rho' Tn_fail0 Tn_fail tp' w Tn_fail_eq Hw).
    +   rewrite Tn_ok0_eq, (proj1 imp_nm_ok), (proj2 imp_nm_ok). change (bd_subst _ [] ++ ?r) with r.
      eapply TR_pre; [|apply (REENTER Tn_ok (ndTok 0 vHa) (180, z0) rho'); [innth 2 | rewrite emeas_z0; lia]].
      intros w Hw. exact (SPA_axforms segs _ _ rho' Tn_ok0 Tn_ok tp' w Tn_ok_eq Hw).
Qed.

Ltac measT := rewrite emeas_z0; lia.
Lemma exits_okT : ltac2:(tb__ "0|3|
S33S40S6S15S18A2M0S1aS5S58Q40A1A1M1G1S5bS6S6S33S40A2M2G0A2S7G2G0S7S33S40R6R5A4R4A4ScaA3VTR;S67S38VJAv;R6A1R7R4R3A5VFAM;S4cS7G2G0S7S33S40R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. unfold exitsE, fails_t in Hin. cbn [In app] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]]]]]]]]]]]];
    destruct (edesc_eq3 _ _ _ _ _ _ H) as (<- & <- & <-).
  - apply X_E_nm. measT.
  - apply X_E_ad1. measT.
  - apply X_E_ad2. measT.
  - apply X_E_ad3. measT.
  - apply X_E_ad4. measT.
  - apply X_E_vf5. measT.
  - apply X_E_vf6. measT.
  - apply X_E_vf7. measT.
  - apply X_E_vp. measT.
  - apply X_E_mk. measT.
  - apply X_E_mg. measT.
  - apply X_FL_E0.
  - apply X_FL_E1.
  - apply X_FL_50.
  - apply X_FL_51.
  - apply X_FL_60.
  - apply X_FL_61.
  - apply X_FL_70.
  - apply X_FL_71.
  - apply X_FL_p0.
  - apply X_FL_p1.
  - apply POST. innth 0.
  - apply POST. innth 1.
  - apply POST. innth 2.
  - apply POST. innth 3.
Qed.
End X.

Lemma hVP_lt : (hVP < NF)%positive. Proof. reflexivity. Qed.
Lemma ndp0_none : nd_am VP.ndp0 = ANone. Proof. reflexivity. Qed.
Lemma PD_vp_none : ltac2:(tb__ "0|1|
S101S6S33S40A2M0G0S0S45S54S13S33S40R1A3A1S50A3Ld;S8fA3"). Proof. repeat constructor. Qed.
Lemma P0_vp_mono : ltac2:(tb__ "0|2|
S5S6S15S15A2M0A1M1G1S5S6G0S15A2A1S1aG0S5bG0R1R5A3S5bG0R2R5A3F_;Fbn;S10aR5R3R2A3S10aR5R4R3A3F_;F_;Fr;FFFc;FF';FF;").
Proof. intros F F' FFc r _ H. exact H. Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S57S38VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S16cS38S169VAInv;VCST;VXGL;A5").

Let TRs_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, triple segs ok (P a) Q) -> triple segs ok (fun w => exists a, P a w) Q
  := @triple_ex segs ok.
Lemma CVP_s : ltac2:(tb__ "0|1|
S5S6S15S15A2M0A1S5S6G0S15A2A1S62S1aS5S58Q40A1A1S61Z4R3A2S11bS38Vok;S67S38S46VAInv;VCST;VXGL;VKc;S10aR6R5A2R6R5R4S41S164S113S3S156A3AaS96R3R2A5Se2S38SdcR3R2Sf4VAInv;VCST;VXGL;VKc;S10aS41S163S8fS113S3A3R6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc VPP.P0_vp PTrue Pre_vp VP.ndp0 PD_vp NF hVP true hVP_lt ndp0_none PD_vp_none P0_vp_mono ok).
  intros FBc FFc BXc rho1 tp1 HB0. apply (VPP.vec_push_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
Qed.

Theorem finalize_shape_sum : ltac2:(tb__ "0|0|
S5S58Q40A1A1S11bS38Vok;S67S38S46VAInv;VCST;VXGL;VKc;Se6VFB;VFF;A2VFB;VFF;VBX;S41Sa5AaSa0Vrho0;R1A5Se2S38S6aVrho0;R1Se0A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA_h segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc ALA H_ejcert_fs_ok FUEL_fs cutsC NP cutsE exitsE ok (Q tp0) Hok ejcert_fs_ok)
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (ADP1.arena_dup_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (ADP2.arena_dup_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (ADP3.arena_dup_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (ADP4.arena_dup_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (NMP.arena_alloc_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (VFZ.vec_finalizeZ_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - exact CVP_s.
       - intros Ai rho1 tp1. apply (aca_asan_memcpy _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue ok (map edropA cutsE) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NP Kc (P0_fs FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_fs P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S16dS38S169VAInv;VCST;VXGL;A5").

Let TRe_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, etriple segs (P a) Q) -> etriple segs (fun w => exists a, P a w) Q
  := @etriple_ex segs.
Lemma CVP_e : ltac2:(tb__ "0|1|
S5S6S15S15A2M0A1S5S6G0S15A2A1S62S1aS5S58Q40A1A1S61Z4R3A2S11aS38S67S38S46VAInv;VCST;VXGL;VKc;S10aR6R5A2R6R5R4S41S164S113S3S156A3AaS96R3R2A5Se2S38SdcR3R2Sf4VAInv;VCST;VXGL;VKc;S10aS41S163S8fS113S3A3R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc VPP.P0_vp PTrue Pre_vp VP.ndp0 PD_vp NF hVP true hVP_lt ndp0_none PD_vp_none P0_vp_mono).
  intros FBc FFc BXc rho1 tp1 HB0. apply (VPP.vec_push_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
Qed.

Theorem finalize_shape_sum_ex : ltac2:(tb__ "0|0|
S5S58Q40A1A1S11aS38S67S38S46VAInv;VCST;VXGL;VKc;Se6VFB;VFF;A2VFB;VFF;VBX;S41Sa5AaSa0Vrho0;R1A5Se2S38S6aVrho0;R1Se0A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA_h segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue HKc ALA H_ejcert_fs_ok FUEL_fs cutsC NP cutsE exitsE (Q tp0) ejcert_fs_ok)
         with (ndT := nd0) (rv := (200, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (ADP1.arena_dup_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (ADP2.arena_dup_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (ADP3.arena_dup_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (ADP4.arena_dup_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (NMP.arena_alloc_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (VFZ.vec_finalizeZ_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - exact CVP_e.
       - intros Ai rho1 tp1. apply (acx_asan_memcpy _ _ _ _ _ ACX). exact HKc.
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NP Kc rho0 (P0_fs FB FF) FB FF BX PTrue cutsE T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NP Kc (P0_fs FB FF) FB FF BX PTrue rho0 tp0 nd Posts_fs P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_finalize_shape_pf.

