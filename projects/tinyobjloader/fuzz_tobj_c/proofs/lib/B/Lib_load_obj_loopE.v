(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "pair"; "list"; "prod"; "nil"; "nat"; "app"; "false"; "andb"; "negb"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "leafA"; "ax_setS"; "axwf"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "s_E"; "X_latchE2"; "K_loopE2"; "X_bodyE2"; "ndE0"; "K_afterE2"; "X_latchE2A"; "X_errxE2"; "XlE_objs"; "upd_cell_at"; "PhisE"; "avt_cnt_cell"; "cnt_vars"; "cutsE2"; "exitsE2"; "jAVT"; "jTS"; "keepsE"; "relax_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_facts"; "sv"; "sobj"; "SLit"; "cell"; "sv_eqb"; "sprop"; "SAlu"; "holds"; "mkObj"; "ob_base"; "rw"; "ss_next"; "ss_objs"; "ss_pc"; "c_off"; "c_width"; "mkCell"; "mkSS"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "sstate"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "HNEXT"; "pI"; "X_latchE"; "cps_loop"; "xLC"; "xLK"; "K_loopE"; "O_ent"; "pLNL"; "pPOS"; "xLD"; "bA"; "entA"; "pH"; "t_c"; "v_avt"; "vsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "nd_below"; "am_eqb"; "am_subst"; "AHead"; "JA"; "amode"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tvL"; "s_loop"; "frL"; "tblB"; "tblL"; "LA"; "V_B"; "V_L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_le2"; "ejcertAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exits"; "K_afterE"; "X_bodyE"; "X_errxE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndLE"; "z0"; "LAX"; "LAXK"; "RL"; "VLA"; "ndXE"; "LAK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "runL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "leaf_matchesA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "eqb"; "leb"; "lt"; "@Corelib.Init.Nat"; "add"; "mul"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop.LOLAddr"; "pc_after"; "pc_body"; "pc_errx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sprop_vars_all";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "drop_lastA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Stdlib.Lists.List"; "existsb"; "filter"; "forallb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition jAVT : sv := SVar 532.
Definition jTS : sv := SVar 533.
Definition avt_cnt_cell : sv := ltac2:(tb__ "0|0|
S36S98S5bS5cS5dA1A1S32Z1A1A3").

Definition upd_cell_at (off : Z) (v : sv) (c : cell) : cell := ltac2:(tb__ "0|1|
S1S33L_;S34S3eVc;A1M0S32Voff;A1A2S40G0S3fVc;A1Vv;A3Vc;X1x2").
Definition relax_obj (o : sobj) : sobj := ltac2:(tb__ "0|8|
S1S31L_;M0S1S1L_;M1S34S39Vo;A1M2S58A2M3S34S45Vo;A1M4S32Zd8A1A2S9X1x2S38G2G4S44Vo;A1M5S5fS33S33S21Ze0S27A2S42Vo;A1M6A4S43Vo;A1M7A5G0G1G3S34G4S32Z330A1A2S9X1x2S38G2G4G5S5fS33S33S21Z338S28A2G6A4G7A5Vo;X1x2X1x2").

Definition cnt_vars : list positive := ltac2:(tb__ "0|0|
S8S17S5fS7S17S7S90S94U191S95U3R1A2A2A1Li;S61U0U12A2A4S5fS7S17S90S61U244UbA2A4A3").
Definition keepsE (f : sprop) : bool := ltac2:(tb__ "0|0|
S9dS17SbSa2S17S91R1A1S24A3A1Lw;Vf;A2").
Definition relaxE (A : axst) : axst := ltac2:(tb__ "0|0|
S10VA;A1S4bS13VA;S41S3dR1A1S49R1A1S47R1A1S46R1A1S4aR1A1S5fS31S31S2aS3cR1A1A4Sa3S35S29S2fR1A1A3S3bR1A1S48R1A1A9A2TS;").

Definition s_E : wsub := ltac2:(tb__ "0|1|
S0S5S17S30A2M0S3S17S30P214S23A4S0G0S3S17S30P215S32Z0A1A4S6G0A1A3A3").

Definition X_latchE2 : axst := Eval vm_compute in relaxE X_latchE.
Definition K_loopE2 : axst := Eval vm_compute in relaxE K_loopE.
Definition X_bodyE2 : axst := Eval vm_compute in relaxE X_bodyE.
Definition K_afterE2 : axst := Eval vm_compute in relaxE K_afterE.
Definition X_errxE2 : axst := Eval vm_compute in relaxE X_errxE.

Definition XlE_objs : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_latchE2)).
Definition X_latchE2A : axst := Eval vm_compute in drop_lastA X_latchE2 XlE_objs.

Lemma loopE_checks : ltac2:(tb__ "0|a|
ScSdS1Sa4SfSfSaS4cS10R1A1M0A1S14R1A1A2LA;S0SfS19S0SfS1aS0SfS1bS0SfS1dS0SfS1fS6SfA1M1A3M2A3A3A3A3A3S2A3ScSdS4S16A1S5fS12S16S12S3dS10S15R1A1M3A1A1M4LL;S8cU96M5S50S1aA3M6A4S0S16S99S0S16S9aS6S16A1A3A3A3ScSdS4S1A1S5fS12S1S12S8dS68G3S0SfS1bS0SfS1dG1A3A3A3LL;G6A4S0S1S2S0S1S2S6S1A1A3A3A3ScSdS4S5S16S1A2M7A1S5fS12G7S12S3S16S1G4S8dS68G3G2A3A4LL;S8cG5S50S1bA3A4S0G7S3S16S1S9bS2A4S6G7A1A3A3ScSdS1S11S4fS19S18A3S2A3ScSdS1S11S53S1aS18A3S2A3ScSdS1S11S7eS1bS18A3S2A3ScSdS1S11S7dS1dS18A3S2A3ScSdS1S11S7fS1fS18A3S2A3ScSdS1S82S18S68A2S2A3ScSdS1S9eS18S73S73A3S2A3ScSdS4S31A1S3cS10S19A1A1S8S31S20S0S31S54S4eS56S55A3S6S31A1A3A3A3ScSdSfS9fS19S20A2S1eA3ScSdS1S11S1eS1aS74A3S2A3ScSdS1S7bS2fS10S1eA1A1S2dS74S6S2cA1M8A2S0S2cS85Z0M9A1S0S2cS86G9A1G8A3A3A3S2A3SdS4S17A1S5fSfS17SfS3bG0A1LA;S0SfS4fS0SfS53S0SfS7eS0SfS7dS0SfS7fS0SfS19S0SfS1eG1A3A3A3A3A3A3A3A4S0S17S4dS0S17S4dS0S17S4dS0S17S4dS0S17S4dS0S17S4dS0S17S4dS6S17A1A3A3A3A3A3A3A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition ndE0 : ndesc := ndL [].
Definition PhisE : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|3|
S0S5S4S17A1M0S2eOFrho;M1A2M2S3G0G1S7aS77A4S0G2S3G0G1S79S76A4S6G2A1A3A3").
Definition cutsE2 : list efnode := ltac2:(tb__ "0|5|
S0S5S5S5SfS6aA2M0S7A2M1S5S16S30A2M2A2M3S3G1G2S3G0S7S3SfS6aS1aS1cA4U0M4A4S3S16S30S87S88Z1aS84A2A4A4S0G3S3G1G2S3G0S7S3SfS6aS1bS1cA4G4A4S3S16S30S87S88Z19S84A2A4A4S6G3A1A3A3").
Definition exitsE2 : list efnode := ltac2:(tb__ "0|6|
S0S5S5S5SfS6aA2M0S7A2M1S5S16S30A2M2A2M3S3G1G2S3G0S7S3SfS6aS1dS1cA4U0M4A4S3S16S30Z190S84A4M5A4S0G3S3G1G2S3G0S7S3SfS6aS1fS1cA4G4A4G5A4S6G3A1A3A3").
Lemma ecertE2_ok : ltac2:(tb__ "0|0|
SdS1S7cS5eS68S22U96S50S68S25S26A8S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma ent_addrE : ltac2:(tb__ "0|7|
S2eS60S35S37R1A1S2fS10S19A1A1A3ScSdS16S2bR2S59S4eA1A2S64S2bR2S57A2M0S66Z10M1S2bR2S4eA2M2A2A2A3ScS65G2S2bR2S51A2M3A2ScS63G3S2bR2S52A2M4A2ScS63S66G1G4A2M5ZffffffffA2ScS63G0S67Z2M6Z2fA2A2ScSdS16S2bR2S8bG1S52A2A2G5A3S63S2bR2S69A2S67G6Z1aA2A2A2A2A2A2A2A2F_;Fr;").
Proof.
  intros r HF.
  factz HF (SPUlt pI xLC) H1. factz HF (SPUle xLC xLK) H2. factz HF (SPUle xLK (SLit 4294967295)) H3. factz HF (SPUle (kb 16 xLK) (SLit 4294967295)) H4.
  factz HF (SPUle xLD (SLit 140737488355328)) H5. factz HF (SPUle vLEN (SLit 67108864)) H6.
  rewrite uval_lit in H3, H4, H5, H6 by lia.
  assert (EK : uval r (kb 16 xLK) = 16 * uval r xLK) by (unfold kb; apply uval_mul_lit; lia). rewrite EK in H4.
  assert (EI : uval r (SMd M_MUL (SLit 16) pI) = 16 * uval r pI) by (apply uval_mul_lit; lia).
  unfold entA. rewrite uval_add_small by (rewrite EI; lia). rewrite EI. repeat split; lia.
Qed.
Lemma ent_rangeE : ltac2:(tb__ "0|3|
S2eS60S35S37R1A1S2fS10S19A1A1A3ScS63S2bR2S57A2M0S2bR2S39S54S4eS56S55A3A1A2M1A2S63S64G1Z10M2A2S64G0S2bR2S8bG2S52A2A2A2A2A2F_;Fr;").
Proof.
  intros r HF. cbn [ob_base O_ent]. destruct (ent_addrE r HF) as (E1 & H1 & H2 & H3 & H4 & EK & _). pose proof (uval_range r pI). rewrite E1, EK. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sa1S2eS4S72Q40A1A1S96OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sa0S5eVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S16S8fVCST;R1A2ScS63Z0R2A2S65R2S8eA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S16S8fVXGL;R1A2ScS63Z0R2A2S65R2S8eA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S4S5S5S16S16A2S16A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable PA : AA -> Prop.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Variable rho0 : valuation.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S2eOFr;") := ltac2:(tb__ "0|0|
S9cVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S70VAInv;VCST;VXGL;S68VKc;Vrho0;VP0;VFB;VFF;VBX;VPA;Vnd;Ac").

Lemma loopE_checks2 : ltac2:(tb__ "0|6|
ScSdS1S7bS2fS10S4fA1A1S2dS18S0S2cS85Z0M0A1S0S2cS86G0A1S6S2cA1M1A3A3M2A2G2A3S2A3ScSdS1S7bS2fS10S7eA1A1S2dS18G1A2M3S0S2cS78G0A1S0S2cS8aG0A1G1A3A3M4A3S2A3ScSdS1S7bS2fS10S7dA1A1G3G4A3S2A3ScSdS1S6dS6eS18S6fS5aS2A2M5A2G5A2S2A3ScSdS1S6cS4dS89A2S2A3ScSdS1S6cS4dS83A2S2A3SdS1S92S68S4dA2S2A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma relax_latchE : ltac2:(tb__ "0|1|
S2eS4S72Q40A1A1S80S62S5eVJAv;S89A1M0S4fR3R2R1A6S62S5eG0S19S81R4S18A2R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w HS. pose proof loopE_checks as (_ & _ & _ & _ & C1 & _ & _ & _ & _ & Cid & Ctv & _). pose proof loopE_checks2 as (B1 & _ & _ & Bam & BnX & _ & Bnp).
  exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc X_latchE X_latchE2 s_E ndXE ndXE rho tp w C1 Cid Bnp BnX Ctv eq_refl B1 Bam HS).
Qed.

Lemma relax_bodyE : ltac2:(tb__ "0|0|
S2eS4S72Q40A1A1S80S62S5eVJAv;S83A1S7eR3R2R1A6S62S5eVJAv;S1cA1S1bS81R4S18A2R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w HS. pose proof loopE_checks as (_ & _ & _ & _ & _ & _ & C3 & _ & _ & Cid & Ctv & _). pose proof loopE_checks2 as (_ & B2 & _ & Bam & _ & BnL & Bnp).
  exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc X_bodyE X_bodyE2 s_E ndLE ndE0 rho tp w C3 Cid Bnp BnL Ctv eq_refl B2 Bam HS).
Qed.
Lemma relax_afterE : ltac2:(tb__ "0|0|
S2eS4S72Q40A1A1S80S62S5eVJAv;S83A1S7dR3R2R1A6S62S5eVJAv;S1cA1S1dS81R4S18A2R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w HS. pose proof loopE_checks as (_ & _ & _ & _ & _ & _ & _ & C4 & _ & Cid & Ctv & _). pose proof loopE_checks2 as (_ & _ & B3 & Bam & _ & BnL & Bnp).
  exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc K_afterE K_afterE2 s_E ndLE ndE0 rho tp w C4 Cid Bnp BnL Ctv eq_refl B3 Bam HS).
Qed.

Lemma s_E_low : ltac2:(tb__ "0|0|
S2eS17S93R1P214A2SdS72Q40A1S3aS81R3S18A2R2A2S3aR3R2A2A3F_;Fv;Frho;").
Proof.
  intros rho v Hv. cbn [rho_sub rw]. unfold s_E. cbn [wsub_get].
  destruct (Pos.eqb_spec v 532) as [->|_]; [lia|]. destruct (Pos.eqb_spec v 533) as [->|_]; [lia|]. reflexivity.
Qed.

Lemma latch_absorbE2 : ltac2:(tb__ "0|1|
S4S2cA1M0G0S71S2eS4S72Q40A1A1S80SdS1S6cS4dS6bS73S75R6R4A4A2S2A3SdS1S7bS2fS10S1eA1A1S2dS74R6A2R7A3S2A3SdS1S6dS6eS74R6A2R6A2S2A3S76R6A1S62S5eVJAv;S6bS73S75RaR8A4A1S19R7R6R5A6SeS2eS2eScS77R1A1ScS62S5eVJAv;S6bS73S75RbRaA4A1S1aR1R8R7A6ScSdS16S2bR1S51A2S2bR9S51A2A3SdS16S2bR1S4eA2S2bR9S36S97S4eS32Z1A1A3A2A3A2A2A2Lrho2;A2F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fam;Fbdj;Fbdi;").
Proof.
  intros bdi bdj am rho tp w Hnb Hbud Ham ([HT HDEF] & R0 & R1) HS. destruct w as [tr [ms md]].
  pose proof lglue_checks as (Cnth & _). pose proof loopE_checks as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Cobjs & Cdrop & Cent & _ & _).
  pose proof lglue_checks2 as (_ & _ & _ & Cid & Ctv).
  pose proof (smatchA_facts segs _ _ _ _ (proj1 HS)) as HF.
  destruct (ent_addrE rho HF) as (EA & Hi & Hck & Hk32 & Hd47 & EK & HL26).
  assert (EB : uval rho (ob_base (O_ent pI pPOS pLNL)) = uval rho xLD + 16 * uval rho pI) by (cbn [ob_base O_ent]; exact EA).
  destruct (JA_absorb_ent_same segs HTOP AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PA tvL frL bdi am jL xLD (kb 16 xLK) X_latchE2 XlE_objs (O_ent pI pPOS pLNL)
              pPOS pLNL rho tp tr ms md Cobjs Cnth eq_refl eq_refl eq_refl ltac:(cbn; auto) ltac:(cbn; auto) ent_rangeE
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
  - apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc X_latchE2A K_loopE2 s_loop (NDA tvL frL bdi am) (NDA tvL frL bdj am) rho1 tp _ Cent Cid);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | | exact Ctv | reflexivity | exact Hbud | exact Ham | exact SP1].
    apply (nd_below_mono HNEXT); [apply (proj1 (Pos.leb_le _ _)); reflexivity | exact Hnb].
Qed.
End Sum.
