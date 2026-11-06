(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "sub"; "leb"; "pow"; "eqb"; "modulo"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SVar"; "sprop"; "SLit"; "ss_facts"; "valuation"; "ss_objs"; "SPEq"; "SPUle"; "holds"; "cell"; "dflt_writable"; "obj_range"; "odefault"; "ss_next"; "swf"; "DUnknown"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "bool"; "cons"; "true"; "nil"; "nat"; "option"; "andb"; "Some"; "app"; "fst"; "snd"; "false"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_base"; "axst"; "g8"; "has_facts"; "ax_X"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "NDA"; "amode"; "TPA"; "fbinA"; "ffinA"; "frinA"; "tvinA"; "ndesc"; "JA"; "JAi"; "nd_below"; "@Stdlib.Lists.List"; "In"; "nth_error"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "IMG_HI"; "fs_frame_size"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "pclMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "tvd"; "tvz"; "FBx"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shobj"; "xlocal"; "shadow_release_stateA"; "shadow_reopen_stateA"; "wclear"; "expected_sh"; "granules"; "shbyte"; "zrange"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_shx"; "gcs"; "shadow_reopen_cells_stateA"; "local_okP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "lit_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary SymCall ExampleMemcpy Glue3 SymBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV TobjArena.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition local_okP (cells : list cell) (d : odefault) (k1 k2 : Z) (ol : Z * Z) : bool := ltac2:(tb__ "0|2|
S2cS0S0A2S2eLol;Vol;S0S0S34S34S34S34S34S7Z0M0R2A2S9SaR2Z8M1A2G0A2A2S7Z1R1A2A2S7Vk1;S5R2G1A2A2A2S7S5S3S3R2R1A2Z7A2G1A2Vk2;A2A2S4fS0S0S33S0A1S2eLx;S72Vcells;Vd;S3S56R1A2A3S0S3aS9R1S70R4R3R2A3A2S9R1G0A2A2Lb;S39X33x2Lq;S71R2R1A2A3A2Llen;Loff;X2cx1").

Definition gcs (off len bL : Z) : list (Z * nat * sv) := ltac2:(tb__ "0|6|
S36S2cS2cS0S32A2M0ScA2M1S64S0G1S0S2dG0ScS2dS0S32S3S56R1A2U1M2A4S10Z0A1A4Lq;S73S5Voff;Z8M3A2M4SbS6S5S3Voff;Vlen;A2G3A2M5G4A2A1A2A4S2fG1S2dG0ScS2dS0S32S3S56G5A2G2A4S10VbL;A1A4S31G1A1A3A3").
Definition shadow_reopen_cells_stateA (A : axst) (X' : list (sv * sv)) (g : positive) (k1 k2 : Z) (cs : list (Z * nat * sv)) : axst := ltac2:(tb__ "0|0|
S3bVA;A1S25S41S1eS22R1A1S23R1A1S20R1A1S1fR1A1S24R1A1S36SdS13R1A1S2fSdS6bVg;Vk1;Vk2;S7cVcs;A1S1dA5S31SdA1A3A3S11R1A1S1bR1A1S21R1A1A9VX';S3cVA;A1A3TS;").

Section WithSegs.
Variable segs : list Segment.
Hypothesis HTOP : InitState.segs_top segs <= IMG_HI.
Variable AInv : ltac2:(tb__ "0|0|
S5aS12S2bS5dQ40A1A1S52OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S7dVsegs;VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S62VCST;R1A2S26S2Z0R2A2S4R2S57A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S62VXGL;R1A2S26S2Z0R2A2S4R2S57A2A2F_;Fa;").
Hypothesis LFSH : law_fshadow_stmt AInv.

Section Sum.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2bS2cS2cS0S0A2S0A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.
Context {dF : Z}.
Hypothesis HBX : BXok_d dF BX.
Hypothesis HNP : NP_okA NP.

Let JAi : ltac2:(tb__ "0|0|
S49S5aS0S51Fkc;FAi;Fnd;") := ltac2:(tb__ "0|0|
S4bVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JA : ltac2:(tb__ "0|0|
S49S51Fnd;") := ltac2:(tb__ "0|0|
S4aVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").

Lemma JA_shadow_release0 : ltac2:(tb__ "0|6|
S2bS2cScScA2A1S2bS2cS2cScS0A2M0ScA2M1A1S2bS55A1S43S32S1S0S1S1S0S0S2bS17A1S1aS3dS2bSdA1M2S12S2bS5dQ40A1A1S2bS53A1M3S74S52S58ReA1S0S6bRdRcRbRaR9A5SdS27S33G1A1S4eG1R15R12A3S35G1S2dG0ScS2dScS0SeR11A1R10A4SeRfA1A4A2A3S26S2Z0M4R11A2S2R11Z6A2A2S27G2S13S3bRbA1A1S36SdRaS2fSdR3S31SdA1M5A3A3A3S2G4R10A2S26S2R11R10A2S2R10S5R6Z8A2A2A2S27S2eS18RfA1S30A3S27S2eS3fS2fSfS14S3eR14A1SeR17A1A2S2fSfS15SeR14A1S10S6S8Z2Z3dA2Z1A2A1A2S31SfA1A3A3S11S3bRfA1A1A2S30A3S50Vsegs;VJA;S42R1dR1cR1bR1aA4A1R10ReRdS2dG3S5eRcS5fRbRaA2A4A6S50Vsegs;VJA;S42R1eR1dR1cR1bA4A1S6dR11R10R19S31S2cS0S0A2A1A4S79RfS2fSdR9G5A3S7aRbReRcA3A3ReS2dG3S5eRdS5fRcRbA2A4A6F_;F_;F_;F_;F_;F_;F_;F_;Tsh;Tsz;Fmd;Fms;Ftr;Ftp;Frho;Fobjs;FA;Fd;Fcells;Fk2;Fk1;Fg;FpF;Fc;FpR;Fi;Fam;Fbd;Ffr;Ftv;").
Proof using ALA HCST HXGL HBX HKc HTOP LFSH HNP.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd am i pR c pF g k1 k2 cells d A objs rho tp tr ms md sz sh Hnth Hc6 Ho Hk1 Hk2 Hdw Hfe2 [Hsm (Ai & kc & HJ)].
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  set (fe := (SVar pR, c, SVar pF)) in Hnth. pose proof (nth_error_In _ _ Hnth) as Hfe.
  destruct (own_frame_facts segs AInv CST ALA HCST rho0 FF Ai rho tp md fr fe HM HT HFR Hfe) as (E1 & E2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  cbn [frv fst snd fe] in E1, E2, F1, F2, F3, F4, F5, F6, F7, F8, F9. fold sz in E1, E2, F2, F3, F5.
  set (p := uval rho (SVar pR)) in *.
  unfold aceil in F5, F7. pose proof (fs_frame_size_bounds' c Hc6) as Hszb. fold sz in Hszb.
  assert (P8 : p mod 8 = 0) by (clear -F1; pose proof (Z.div_mod p 64 ltac:(lia)); pose proof (Z.div_mod p 8 ltac:(lia)); nia).
  assert (S8 : sz mod 8 = 0) by (clear -F2 Hszb; pose proof (Z.div_mod sz 64 ltac:(lia)); pose proof (Z.div_mod sz 8 ltac:(lia)); nia).
  assert (SP8 : Sh p mod 8 = 0).
  { unfold Sh, SHADOW_OFF. clear -F1 F4. pose proof (Z.div_mod p 64 ltac:(lia)). pose proof (Z.div_mod (p / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.mod_pos_bound p 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p / 8) 8 ltac:(lia)).
    rewrite Z.add_mod by lia. replace (2147450880 mod 8) with 0 by reflexivity. rewrite Z.add_0_r, Z.mod_mod by lia. nia. }
  assert (SS8 : (sz / 8) mod 8 = 0).
  { clear -F2 Hszb. pose proof (Z.div_mod sz 64 ltac:(lia)). pose proof (Z.div_mod (sz / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod sz 8 ltac:(lia)). pose proof (Z.mod_pos_bound sz 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sz / 8) 8 ltac:(lia)). nia. }
  assert (Hp0 : 0 <= p /\ p + sz <= 2 ^ 47) by (unfold HIGH_SHADOW_END in F4; lia).

  pose proof (has_facts_sound rho _ _ HF Hfe2) as HG. apply Forall_cons_iff in HG as [HG1 HG2]. apply Forall_cons_iff in HG2 as [HG2 _].
  cbn [holds] in HG1, HG2. cbn [eval] in HG2. rewrite (u64_lit (2 ^ 61 - 1)) in HG2 by lia.
  assert (Ug : bv_unsigned (rw rho g) = p / 8).
  { apply (f_equal bv_unsigned) in HG1. unfold g8 in HG1. rewrite U_sll_lit in HG1. cbn [eval] in HG1. change (2 ^ (3 mod 64)) with 8 in HG1.
    pose proof (bv_urange (rw rho g)) as Rg. rewrite <- M64v_eq, Z.mod_small in HG1 by lia. change (bv_unsigned (rw rho pR)) with p in HG1. rewrite <- HG1. rewrite Z.div_mul by lia. reflexivity. }
  pose proof Hsm as (HsmS & HMI & HwfA & Hsh & Hhz).
  pose proof HsmS as (Hswf & _ & _ & _ & Hrom & _ & _ & _ & _ & _ & (Hall & Hpd & Hfr) & _).
  cbn [virt fst snd cfg_ms cfg_model] in Hall, Hrom.
  assert (Hrng : obj_range rho sh = (Sh p + k1, Sh p + k2)).
  { unfold obj_range, obj_lo_of, obj_hi_of, sh, shobj. cbn [ob_base ob_lo ob_hi eval]. rewrite Ug. unfold Sh, SHADOW_OFF in *. rewrite !soff_lit_small by lia. f_equal; lia. }
  set (rho' := rho_absorb rho [sh] (vms md tp ms)).
  assert (OUT : forall a, ~ (Sh p + k1 <= bv_unsigned a < Sh p + k2) -> rm rho' a = rm rho a).
  { intros a Ha. unfold rho'. apply GlueM.rm_absorb_out. intros (o2 & [<-|[]] & Hr). rewrite Hrng in Hr. exact (Ha Hr). }
  assert (INa : forall a, Sh p + k1 <= bv_unsigned a < Sh p + k2 -> rm rho' a = ms_mem (vms md tp ms) a).
  { intros a Ha. unfold rho'. apply GlueM.rm_absorb_in. exists sh. split; [left; reflexivity|]. rewrite Hrng. exact Ha. }
  destruct (released_bytesA segs HTOP rho A objs [sh] sh tp tr ms md Ho ltac:(left; reflexivity) Hsm Hdw
              ltac:(rewrite Hrng; cbn [fst]; unfold Sh, SHADOW_OFF, IMG_HI in *; lia) ltac:(rewrite Hrng; cbn [snd]; unfold Sh, SHADOW_OFF in *; lia)) as [BY _].
  rewrite Hrng in BY. cbn [fst snd] in BY. fold rho' in BY.

  assert (SP1 : SPA segs (JAi (NDA tv fr bd am) Ai kc) (ax_setS A (set_objs (ax_S A) objs)) rho' tp (tr, mkCfg ms md)).
  { apply (SPA_unobj segs (JAi (NDA tv fr bd am) Ai kc) rho A objs [sh] tp tr ms md Ho (conj Hsm HJ)).
    intros HJ'. apply (JAi_shadow_write segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0f FB FF BX PA HKc HBX (NDA tv fr bd am) Ai kc rho rho' tp tr md i fe (Sh p + k1) (Sh p + k2) HJ' Hnth);
      cbn [nd_fr frv fst snd fe]; fold (uval rho (SVar pR)); fold p; fold sz; try lia; try (intros; reflexivity).
    - exact OUT.
    - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply BY. exact Ha. }

  assert (EQA : shadow_release_stateA A objs pR [] = ax_setS A (set_objs (ax_S A) objs)) by reflexivity.
  rewrite EQA. destruct SP1 as [Hsm5 HJ5]. split; [exact Hsm5|]. exists Ai, kc. exact HJ5.
Qed.

Lemma JA_shadow_releaseP : ltac2:(tb__ "0|8|
S2bS2cScScA2A1S2bS2cS2cScS0A2M0ScA2M1A1S2bS55A1S43S32S1S0S1S1S0S0S2bS17A1S1aS3dS2bSdA1M2S2bS2cS0S0A2M3A1S12S2bS5dQ40A1A1M4S2bS53A1M5S74S52S58RfA1S0S6bReRdRcRbRaA5SdS27S33G1A1S4eG1R16R13A3S35G1S2dG0ScS2dScS0SeR12A1R11A4SeR10A1A4A2A3S26S2Z0R12A2M6S2R12Z6A2A2S27ScS3cRcA1S10S56A1A3S27G2S13S3bRdA1A1S36SdRcS2fSdR4S31SdA1M7A3A3A3G6S26S2R13R12A2S2R12S5R7Z8A2A2A2S27S2eS18R11A1S30A3S27S2eS3fS2fSfS14S3eR16A1SeR19A1A2S2fSfS15SeR16A1S10S6S8Z2Z3dA2Z1A2A1A2S31SfA1A3A3S11S3bR11A1A1A2S30A3S27S2eS4fG3S77R14R13R16R15A4R10A3S30A3S27S2eS4cS1bS3bR13A1A1S42R20R1fR1eR1dA4A2S30A3S5aS12G4S52S63SfS16R15A1S11S3bR18A1A1A3VP0f;Vrho0;A1S65VNP;Vrho0;R17A3VAInv;R7R6R5R4A4S44Vrho0;R8A2S66R1aS5cS5bR9A1A1A2S45VFB;RaA2S46VFF;RbA2S48VFB;RcR1dR2dA4S67R1eR2eA2S68R1fR2fA2S47VFF;RfR20R2fA4S7bVCST;Vrho0;VFB;VFF;R21R31R30R23A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;S50Vsegs;VJA;S42R22R21R20R1fA4A1R15R12R11S2dG5S5eR10S5fRfReA2A4A6S50Vsegs;VJA;S42R23R22R21R20A4A1S6dR16R15R1eR14A4S79R13S2fSdRdG7A3S7aRfR12R10A3A3R12S2dG5S5eR11S5fR10RfA2A4A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tsh;Tsz;Fmd;Fms;Ftr;Ftp;Frho;FL;Fobjs;FA;Fd;Fcells;Fk2;Fk1;Fg;FpF;Fc;FpR;Fi;Fam;Fbd;Ffr;Ftv;").
Proof using ALA HCST HXGL HBX HKc HTOP LFSH HNP.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd am i pR c pF g k1 k2 cells d A objs L rho tp tr ms md sz sh Hnth Hc6 Hbase Ho Hk1 Hk2 Hdw Hfe2 HL Hnb HSITE [Hsm (Ai & kc & HJ)].
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  pose proof (HSITE Ai rho tp md HF HP0 Hav HM HT (T_ok_of_TPA NP rho0 HNP rho Ai Hav HT) HB HFF HN HD HZ HFR) as HROK.
  set (fe := (SVar pR, c, SVar pF)) in Hnth. pose proof (nth_error_In _ _ Hnth) as Hfe.
  destruct (own_frame_facts segs AInv CST ALA HCST rho0 FF Ai rho tp md fr fe HM HT HFR Hfe) as (E1 & E2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  cbn [frv fst snd fe] in E1, E2, F1, F2, F3, F4, F5, F6, F7, F8, F9. fold sz in E1, E2, F2, F3, F5.
  set (p := uval rho (SVar pR)) in *.
  unfold aceil in F5, F7. pose proof (fs_frame_size_bounds' c Hc6) as Hszb. fold sz in Hszb.
  assert (P8 : p mod 8 = 0) by (clear -F1; pose proof (Z.div_mod p 64 ltac:(lia)); pose proof (Z.div_mod p 8 ltac:(lia)); nia).
  assert (S8 : sz mod 8 = 0) by (clear -F2 Hszb; pose proof (Z.div_mod sz 64 ltac:(lia)); pose proof (Z.div_mod sz 8 ltac:(lia)); nia).
  assert (SP8 : Sh p mod 8 = 0).
  { unfold Sh, SHADOW_OFF. clear -F1 F4. pose proof (Z.div_mod p 64 ltac:(lia)). pose proof (Z.div_mod (p / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.mod_pos_bound p 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p / 8) 8 ltac:(lia)).
    rewrite Z.add_mod by lia. replace (2147450880 mod 8) with 0 by reflexivity. rewrite Z.add_0_r, Z.mod_mod by lia. nia. }
  assert (SS8 : (sz / 8) mod 8 = 0).
  { clear -F2 Hszb. pose proof (Z.div_mod sz 64 ltac:(lia)). pose proof (Z.div_mod (sz / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod sz 8 ltac:(lia)). pose proof (Z.mod_pos_bound sz 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sz / 8) 8 ltac:(lia)). nia. }
  assert (Hp0 : 0 <= p /\ p + sz <= 2 ^ 47) by (unfold HIGH_SHADOW_END in F4; lia).

  pose proof (has_facts_sound rho _ _ HF Hfe2) as HG. apply Forall_cons_iff in HG as [HG1 HG2]. apply Forall_cons_iff in HG2 as [HG2 _].
  cbn [holds] in HG1, HG2. cbn [eval] in HG2. rewrite (u64_lit (2 ^ 61 - 1)) in HG2 by lia.
  assert (Ug : bv_unsigned (rw rho g) = p / 8).
  { apply (f_equal bv_unsigned) in HG1. unfold g8 in HG1. rewrite U_sll_lit in HG1. cbn [eval] in HG1. change (2 ^ (3 mod 64)) with 8 in HG1.
    pose proof (bv_urange (rw rho g)) as Rg. rewrite <- M64v_eq, Z.mod_small in HG1 by lia. change (bv_unsigned (rw rho pR)) with p in HG1. rewrite <- HG1. rewrite Z.div_mul by lia. reflexivity. }
  pose proof Hsm as (HsmS & HMI & HwfA & Hsh & Hhz).
  pose proof HsmS as (Hswf & _ & _ & _ & Hrom & _ & _ & _ & _ & _ & (Hall & Hpd & Hfr) & _).
  cbn [virt fst snd cfg_ms cfg_model] in Hall, Hrom.
  assert (Hrng : obj_range rho sh = (Sh p + k1, Sh p + k2)).
  { unfold obj_range, obj_lo_of, obj_hi_of, sh, shobj. cbn [ob_base ob_lo ob_hi eval]. rewrite Ug. unfold Sh, SHADOW_OFF in *. rewrite !soff_lit_small by lia. f_equal; lia. }
  set (rho' := rho_absorb rho [sh] (vms md tp ms)).
  assert (OUT : forall a, ~ (Sh p + k1 <= bv_unsigned a < Sh p + k2) -> rm rho' a = rm rho a).
  { intros a Ha. unfold rho'. apply GlueM.rm_absorb_out. intros (o2 & [<-|[]] & Hr). rewrite Hrng in Hr. exact (Ha Hr). }
  assert (INa : forall a, Sh p + k1 <= bv_unsigned a < Sh p + k2 -> rm rho' a = ms_mem (vms md tp ms) a).
  { intros a Ha. unfold rho'. apply GlueM.rm_absorb_in. exists sh. split; [left; reflexivity|]. rewrite Hrng. exact Ha. }
  destruct (released_bytesA segs HTOP rho A objs [sh] sh tp tr ms md Ho ltac:(left; reflexivity) Hsm Hdw
              ltac:(rewrite Hrng; cbn [fst]; unfold Sh, SHADOW_OFF, IMG_HI in *; lia) ltac:(rewrite Hrng; cbn [snd]; unfold Sh, SHADOW_OFF in *; lia)) as [BY _].
  rewrite Hrng in BY. cbn [fst snd] in BY. fold rho' in BY.

  assert (SP1 : SPA segs (JAi (NDA tv fr bd am) Ai kc) (ax_setS A (set_objs (ax_S A) objs)) rho' tp (tr, mkCfg ms md)).
  { apply (SPA_unobj segs (JAi (NDA tv fr bd am) Ai kc) rho A objs [sh] tp tr ms md Ho (conj Hsm HJ)).
    intros HJ'. apply (JAi_shadow_write segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0f FB FF BX PA HKc HBX (NDA tv fr bd am) Ai kc rho rho' tp tr md i fe (Sh p + k1) (Sh p + k2) HJ' Hnth);
      cbn [nd_fr frv fst snd fe]; fold (uval rho (SVar pR)); fold p; fold sz; try lia; try (intros; reflexivity).
    - exact OUT.
    - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply BY. exact Ha. }

  assert (EVr : forall e, eval rho' e = eval rho e) by (intros e; unfold rho'; apply eval_absorb).
  assert (HNx : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
  pose proof (fbinA_FBx FB Ai rho tv [] HB HNx) as FBX. pose proof (ffinA_FFx FF Ai rho fr HFF HFR) as FFX.
  assert (NOSH : forall o a, In o objs -> fst (obj_range rho o) <= a < snd (obj_range rho o) -> ~ is_shadowZ a).
  { intros o a Hoin Hr Hs. destruct (HROK o a Hoin Hr) as [Hc|Hi].
    - exact (cmaddrA_not_shadow segs AInv CST ALA HCST Ai None a rho tp md HM (pclMA_cmaddrA CST rho0 _ _ Ai a FBX FFX HT Hc) Hs).
    - unfold is_shadowZ, SHADOW_OFF, IMG_HI in *. lia. }
  pose proof (swf_objs _ Hswf) as HOWF. rewrite Ho, forallb_app in HOWF. apply andb_prop in HOWF as [HOWF _].
  assert (OUTS : forall z, is_shadowZ z -> 0 <= z < 2 ^ 64 -> outside_all rho' objs (Z_to_bv 64 z)).
  { intros z Hz Hz64. unfold outside_all. apply Forall_forall. intros o Hoin. cbn beta.
    rewrite (obj_range_agree_vals (ss_next (ax_S A)) rho rho' o ltac:(split; intros; reflexivity) (proj1 (forallb_forall _ _) HOWF o Hoin)).
    rewrite u64_lit by lia. intros Hr. exact (NOSH o z Hoin Hr Hz). }
  assert (FSH : forall z, Sh p <= z < Sh p + sz / 8 -> rm rho' (Z_to_bv 64 z) <> None).
  { intros z Hz. destruct (Z_le_dec (Sh p + k1) z), (Z_lt_dec z (Sh p + k2)); try (apply BY; lia);
      rewrite OUT by (rewrite u64_lit by (unfold Sh, SHADOW_OFF in *; lia); lia);
      apply (LFSH Ai rho tp md p sz z HM E1); rewrite Sh_val in *; unfold Sh; pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.div_mod sz 8 ltac:(lia)); nia. }
  destruct (nd_below_split _ _ Hnb) as (Hbt & Hbf & Hbb & Hba). cbn [nd_tv nd_fr nd_bd nd_am] in Hbf.
  pose proof (proj1 (forallb_forall _ _) Hbf fe Hfe) as Hfeb. cbn [fe fst snd sv_below] in Hfeb. apply andb_prop in Hfeb as [HpRn _]. apply Pos.ltb_lt in HpRn.
  assert (UpR : bv_unsigned (rw rho pR) = p) by reflexivity.
  assert (PUB : forall L', forallb (local_okP cells d k1 k2) L' = true -> forall X0,
            SPA segs (JAi (NDA tv fr bd am) Ai kc) (mkAX (set_objs (ax_S A) objs) X0 (ax_base A)) rho' tp (tr, mkCfg ms md) ->
            SPA segs (JAi (NDA tv fr bd am) Ai kc) (mkAX (set_objs (ax_S A) objs) (map (xlocal pR) L' ++ X0) (ax_base A)) rho' tp (tr, mkCfg ms md)).
  { induction L' as [|[off len] L' IH]; intros HL' X0 SP; [exact SP|].
    cbn [forallb] in HL'. apply andb_prop in HL' as [Hl HL']. specialize (IH HL' X0 SP). cbn [map app].
    apply (SPA_x_publish segs _ rho' (mkAX (set_objs (ax_S A) objs) (map (xlocal pR) L' ++ X0) (ax_base A)) (xlocal pR (off, len)) tp _); [| | exact IH].
    - unfold xr_below, xlocal. cbn [fst snd ax_S set_objs ss_next sv_below]. rewrite !andb_true_r. apply Pos.ltb_lt. exact HpRn.
    - unfold local_okP in Hl. apply andb_prop in Hl as [Hl HQ]. apply andb_prop in Hl as [Hl Hl5]. apply andb_prop in Hl as [Hl Hl4].
      apply andb_prop in Hl as [Hl Hl3]. apply andb_prop in Hl as [Hl1 Hl2].
      apply Z.leb_le in Hl1. apply Z.eqb_eq in Hl2. apply Z.leb_le in Hl3. apply Z.leb_le in Hl4. apply Z.leb_le in Hl5.
      assert (Hlen : off + len <= sz).
      { pose proof (Z.div_mod (off + len + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (off + len + 7) 8 ltac:(lia)). pose proof (Z.div_mod sz 8 ltac:(lia)). nia. }
      cbn [ax_base ax_S set_objs ss_objs]. rewrite Hbase. cbn [eval]. rewrite lit_unsigned. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF.
      unfold xr_ok, xlocal. cbn [fst snd]. rewrite !EVr. rewrite U_add. cbn [eval]. rewrite UpR, !u64_lit by lia. rewrite <- M64v_eq, (Z.mod_small (p + off) (2 ^ 64)) by lia.
      split; [rewrite Z.add_mod, P8, Hl2 by lia; reflexivity|]. split; [lia|].
      intros a Ha. set (q := (a - p) / 8).
      pose proof (Z.div_mod (a - p) 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound (a - p) 8 ltac:(lia)) as Mq. pose proof (Z.div_mod p 8 ltac:(lia)) as Dp.
      assert (Ha8 : a / 8 = p / 8 + q) by (subst q; rewrite P8 in Dp; clear - Dq Mq Dp; nia).
      assert (Hq : off / 8 <= q < (off + len + 7) / 8).
      { subst q. split; [apply Z.div_le_mono; clear - Ha; lia|]. apply Z.div_lt_upper_bound; [clear - Ha; lia|]. pose proof (Z.mul_div_le (off + len + 7) 8 ltac:(lia)) as MDL.
        pose proof (Z.div_mod (off + len + 7) 8 ltac:(lia)) as DL8. pose proof (Z.mod_pos_bound (off + len + 7) 8 ltac:(lia)) as ML8. first [clear - Ha MDL DL8 ML8; lia | nia]. }
      assert (HSa : is_shadowZ (Sh a)) by (apply Sh_is_shadow; lia).
      assert (Hza : Sh p <= Sh a < Sh p + sz / 8) by (apply (proj2 (Sh_range_iff p sz a P8 S8)); lia).
      pose proof HSa as SS. unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS.
      split; [unfold Sh, SHADOW_OFF in Hza, SS |- *; lia|].
      split; [rewrite shadow_addr_Sh; apply OUTS; [exact HSa | lia]|].
      split.
      + intros j Hj. pose proof (word_byte_of_shadow (Sh a) j HSa Hj) as WS.
        destruct (word_byte_range (Sh a) j ltac:(lia) Hj) as (W1 & W2 & W3).
        replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia).
        split; [rewrite <- (Z_to_bv_bv_unsigned 64 (word_byte (Sh a) j)), W2; apply OUTS; [rewrite <- W2; exact WS | lia]|].
        rewrite <- (Z_to_bv_bv_unsigned 64 (word_byte (Sh a) j)), W2. apply FSH.
        pose proof (word_in_aligned_range (Sh a) (Sh p) (sz / 8) j SP8 SS8 Hj) as WW.

        pose proof (Z.div_mod (Sh a) 8 ltac:(lia)) as DA8. pose proof (Z.mod_pos_bound (Sh a) 8 ltac:(lia)) as MA8.
        pose proof (Z.div_mod (Sh p) 8 ltac:(lia)) as DP8. pose proof (Z.div_mod (sz / 8) 8 ltac:(lia)) as DS8.
        first [ clear - DA8 MA8 DP8 DS8 WW W1 W2 W3 Hza Hj SP8 SS8; lia | clear - DA8 MA8 DP8 DS8 WW W1 W2 W3 Hza Hj SP8 SS8; nia | nia ].
      +
        pose proof (proj1 (forallb_forall _ _) HQ q (In_granules off len q Hl1 Hl3 Hq)) as HQq. cbn beta in HQq.
        destruct (shbyte cells d (SHADOW_OFF + q)) as [b|] eqn:Hsb; [|discriminate].
        assert (HQb : b = expected_sh off len q \/ b = 0) by (apply orb_prop in HQq as [HQq|HQq]; apply Z.eqb_eq in HQq; auto). clear HQq.
        rewrite Ho in Hall. apply Forall_app in Hall as [_ Hshh]. apply Forall_inv in Hshh.
        pose proof (shbyte_sound segs HTOP rho (vms md tp ms) sh (SHADOW_OFF + q) b Hrom Hshh Hsb) as SB.
        unfold obj_lo_of, obj_hi_of, sh, shobj in SB. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt eval] in SB. rewrite Ug in SB.
        unfold SHADOW_OFF in SB. rewrite !soff_lit_small in SB by lia.
        specialize (SB ltac:(lia) ltac:(unfold IMG_HI, Sh, SHADOW_OFF in *; lia)).
        replace (p / 8 + (2147450880 + q)) with (Sh a) in SB by (unfold Sh, SHADOW_OFF; lia).
        assert (HSq : Sh a = Sh p + q) by (unfold Sh; lia).
        exists (Z_to_bv 8 b). split; [rewrite shadow_addr_Sh, INa by (rewrite u64_lit by lia; lia); exact SB|].
        rewrite Z_to_bv_unsigned. unfold expected_sh in HQb.
        assert (Hb8 : 0 <= (off + len) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
        destruct HQb as [HQq|HQq]; [|subst b; left; reflexivity].
        destruct (q <? (off + len) / 8) eqn:Eq; [apply Z.ltb_lt in Eq | apply Z.ltb_ge in Eq]; subst b.
        * left. reflexivity.
        * right. rewrite bv_wrap_small by (change (bv_modulus 8) with 256; lia).
          assert (Eqq : q = (off + len) / 8).
          { subst q. apply Z.le_antisymm; [|exact Eq]. apply Z.div_le_mono; [lia|]. lia. }
          split.
          -- replace (p + off + len) with ((off + len) + p) by lia. rewrite (Z.add_mod (off + len) p 8), P8, Z.add_0_r, Z.mod_mod by lia. reflexivity.
          -- rewrite Ha8, Eqq. rewrite P8, Z.add_0_r in Dp. rewrite Dp at 2. rewrite <- Z.add_assoc, Z.mul_comm, Z.div_add_l by lia. reflexivity. }
  specialize (PUB L HL (ax_X A)).
  assert (EQA : mkAX (set_objs (ax_S A) objs) (ax_X A) (ax_base A) = ax_setS A (set_objs (ax_S A) objs)) by reflexivity.
  rewrite EQA in PUB. specialize (PUB SP1). destruct PUB as [Hsm5 HJ5].
  split; [exact Hsm5|]. exists Ai, kc. exact HJ5.
Qed.

Lemma JA_shadow_reopenS : ltac2:(tb__ "0|b|
S2bS2cScScA2M0A1M1S2bS2cS2cScS0A2M2ScA2M3A1S2bS55A1S43S32S1S0S1S1S0S0S3dG1S12S2bS5dQ40A1A1M4S78S58RaA1S0S27S33G3A1S4eG3R10RdA3S35G3S2dG2ScS2dScS0SeRcA1RbA4SeRaA1A4A2A3S26S2Z0M5RcA2S2RcZ6A2A2S27ScS3cR8A1S10S56A1A3S2G5RbA2S26S2RcRbA2S2RbS5R5Z8A2A2A2S27S2eS3fS2fSfS14S3eReA1SeR11A1A2S2fSfS15SeReA1S10S6S8Z2Z3dA2Z1M6A2A1A2S31SfA1A3A3S11S3bRbA1A1A2S30A3G0S4dG0R1RcA3S4dG0R2S40ReA1A3F_;Fr;S27S2eS1cS3bS6eRdRcR10RfReA5A1A1S30A3S5aS12G4S52S63SfS16R10A1S11S3bR12A1A1A3VP0f;Vrho0;A1S65VNP;Vrho0;R12A3VAInv;R7R6R5R4A4S44Vrho0;R8A2S66R15S5cS5bR9A1A1A2S45VFB;RaA2S46VFF;RbA2S48VFB;RcR18R25A4S67R19R26A2S68R1aR27A2S47VFF;RfR1bR27A4S26SdS0S4dSdR2S13S3bR20A1A1A3S26S2S37S0S0S19R1fR3A2M7A3R2A2S4R2S38S0S0G7A3A2A2S28S28S61VCST;Vrho0;S69VFB;R20R2dA3M8S60VFF;R20R2cA3R3A5S26S2G5R3A2S4R3S57A2A2A2S2aS26S2S3S59S54R20SeR28A1A2A1M9R24A2R3A2S4R3S3G9R23A2A2A2A1A2F_;F_;Fa;Fo;G0S0S4dG0R2R1fA3S26S2S54R1fS37ScScR3A3A2MaR2A2S4R2S3GaS54R1fS38ScScR3A3A2A2A2A2S28S28S61VCST;Vrho0;G8S60VFF;R20S6aG3R29R2cA3A3R3A5S62VXGL;R3A2A2S29S0S0S29S0S0S26S27G0R6S6cR2aS2dS0S0R2R1A4A2A3S26S2G5R2A2S26S2G6R1A2S26S2S3R2R1A2R1fA2S27S2eS6fR26R25R2R1A4S30A3A2A2A2A2Llen;A2Loff;A2A2F_;F_;Fy;Fr;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;S50Vsegs;VJA;S42R1aR19R18R17A4A1RfRdRcRbA6S50Vsegs;VJA;S42R1bR1aR19R18A4A1S6eR10RfR13R12R11A5ReRdRcA6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tsz;Fw;Ftp;Frho;FX';FA;Fk2;Fk1;Fg;FpF;Fc;FpR;Fi;Fam;Fbd;Ffr;Ftv;").
Proof using ALA HCST HXGL HBX HKc HTOP LFSH HNP.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd am i pR c pF g k1 k2 A X' rho tp w sz Hnth Hc6 Hbase Hk1 Hk2 Hfe2 HX' Hwf HSITE [Hsm (Ai & kc & HJ)].
  destruct w as [tr [ms md]].
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  destruct (HSITE Ai rho tp md HF HP0 Hav HM HT (T_ok_of_TPA NP rho0 HNP rho Ai Hav HT) HB HFF HN HD HZ HFR) as [HROK HXW].
  set (fe := (SVar pR, c, SVar pF)) in Hnth. pose proof (nth_error_In _ _ Hnth) as Hfe.
  destruct (own_frame_facts segs AInv CST ALA HCST rho0 FF Ai rho tp md fr fe HM HT HFR Hfe) as (E1 & E2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  cbn [frv fst snd fe] in E1, E2, F1, F2, F3, F4, F5, F6, F7, F8, F9. fold sz in E1, E2, F2, F3, F5.
  set (p := uval rho (SVar pR)) in *.
  unfold aceil in F5, F7. pose proof (fs_frame_size_bounds' c Hc6) as Hszb. fold sz in Hszb.
  assert (P8 : p mod 8 = 0) by (clear -F1; pose proof (Z.div_mod p 64 ltac:(lia)); pose proof (Z.div_mod p 8 ltac:(lia)); nia).
  assert (S8 : sz mod 8 = 0) by (clear -F2 Hszb; pose proof (Z.div_mod sz 64 ltac:(lia)); pose proof (Z.div_mod sz 8 ltac:(lia)); nia).
  assert (SP8 : Sh p mod 8 = 0).
  { unfold Sh, SHADOW_OFF. clear -F1 F4. pose proof (Z.div_mod p 64 ltac:(lia)). pose proof (Z.div_mod (p / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.mod_pos_bound p 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p / 8) 8 ltac:(lia)).
    rewrite Z.add_mod by lia. replace (2147450880 mod 8) with 0 by reflexivity. rewrite Z.add_0_r, Z.mod_mod by lia. nia. }
  assert (SS8 : (sz / 8) mod 8 = 0).
  { clear -F2 Hszb. pose proof (Z.div_mod sz 64 ltac:(lia)). pose proof (Z.div_mod (sz / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod sz 8 ltac:(lia)). pose proof (Z.mod_pos_bound sz 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sz / 8) 8 ltac:(lia)). nia. }
  assert (Hp0 : 0 <= p /\ p + sz <= 2 ^ 47) by (unfold HIGH_SHADOW_END in F4; lia).
  pose proof (has_facts_sound rho _ _ HF Hfe2) as HG. apply Forall_cons_iff in HG as [HG1 HG2]. apply Forall_cons_iff in HG2 as [HG2 _].
  cbn [holds] in HG1, HG2. cbn [eval] in HG2. rewrite (u64_lit (2 ^ 61 - 1)) in HG2 by lia.
  assert (Ug : bv_unsigned (rw rho g) = p / 8).
  { apply (f_equal bv_unsigned) in HG1. unfold g8 in HG1. rewrite U_sll_lit in HG1. cbn [eval] in HG1. change (2 ^ (3 mod 64)) with 8 in HG1.
    pose proof (bv_urange (rw rho g)) as Rg. rewrite <- M64v_eq, Z.mod_small in HG1 by lia.
    change (bv_unsigned (rw rho pR)) with p in HG1. rewrite <- HG1. rewrite Z.div_mul by lia. reflexivity. }
  assert (HNx : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
  pose proof (fbinA_FBx FB Ai rho tv [] HB HNx) as FBX. pose proof (ffinA_FFx FF Ai rho fr HFF HFR) as FFX.
  assert (SHAD : forall z, Sh p + k1 <= z < Sh p + k2 -> is_shadowZ z).
  { intros z Hz. pose proof (Sh_is_shadow p ltac:(lia)) as S1. pose proof (Sh_is_shadow (p + sz - 1) ltac:(lia)) as S2. rewrite Sh_last in S2 by lia.
    unfold is_shadowZ in *. lia. }
  assert (NOSH : forall o a, In o (ss_objs (ax_S A)) -> fst (obj_range rho o) <= a < snd (obj_range rho o) -> ~ (Sh p + k1 <= a < Sh p + k2)).
  { intros o a Hoin Hr Hs. destruct (HROK o a Hoin Hr) as [[Hc|Hi]|Hn]; [| | exact (Hn Hs)].
    - exact (cmaddrA_not_shadow segs AInv CST ALA HCST Ai None a rho tp md HM (pclMA_cmaddrA CST rho0 _ _ Ai a FBX FFX HT Hc) (SHAD a Hs)).
    - pose proof (SHAD a Hs) as S0. unfold is_shadowZ, SHADOW_OFF, IMG_HI in *. lia. }

  pose proof (SPA_x_sub segs _ rho A X' tp _ HX' (conj Hsm HJ)) as SP1.
  set (A1 := ax_setX A X') in SP1.

  pose proof (SPA_carve_obj segs (JAi (NDA tv fr bd am) Ai kc) rho A1 tp (tr, mkCfg ms md) (SVar g) (SHADOW_OFF + k1) (SHADOW_OFF + k2) [] (ss_next (ax_S A)) SP1) as SP2.
  cbn [eval] in SP2. rewrite Ug in SP2.
  assert (Hwf1 : swf (mkSS (ss_pc (ax_S A1)) (ss_regs (ax_S A1)) (ss_fregs (ax_S A1)) (ss_fcsr (ax_S A1)) (ss_resv (ax_S A1))
                          (ss_objs (ax_S A1) ++ [carved (SVar g) (SHADOW_OFF + k1) (SHADOW_OFF + k2) []]) (ss_facts (ax_S A1)) (ss_next (ax_S A)) (ss_lenient (ax_S A1))) = true).
  { subst A1. cbn [ax_S ax_setX]. unfold shadow_reopen_stateA in Hwf. cbn [ax_S] in Hwf. exact Hwf. }
  specialize (SP2 Hwf1 ltac:(subst A1; cbn [ax_S ax_setX]; lia) ltac:(unfold SHADOW_OFF; lia) ltac:(lia) ltac:(unfold SHADOW_OFF; lia) ltac:(lia)
                  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia) ltac:(constructor)).
  assert (DISJ : Forall (fun o' => ranges_disjoint (obj_range rho o') (p / 8 + (SHADOW_OFF + k1), p / 8 + (SHADOW_OFF + k2))) (ss_objs (ax_S A1))).
  { subst A1. cbn [ax_S ax_setX]. apply Forall_forall. intros o Ho'.
    destruct (obj_range rho o) as [lo hi] eqn:Eo. apply ranges_disjoint_by_points. intros a Ha1 Ha2.
    apply (NOSH o a Ho'); [rewrite Eo; exact Ha1|]. unfold Sh. lia. }
  specialize (SP2 DISJ).
  assert (VIEW : forall off, SHADOW_OFF + k1 <= off < SHADOW_OFF + k2 ->
             wok_of segs (rm rho) (Z_to_bv 64 (p / 8 + off)) = true /\ exists x, rd_of segs (rm rho) (Z_to_bv 64 (p / 8 + off)) = Some x).
  { intros off Hoff.
    assert (Hz : Sh p <= p / 8 + off < Sh (p + sz)).
    { unfold Sh in *. pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.div_mod sz 8 ltac:(lia)). rewrite P8 in *. rewrite S8 in *.
      replace (p + sz) with ((p / 8 + sz / 8) * 8) by lia. rewrite Z.div_mul by lia. lia. }
    pose proof (LFSH Ai rho tp md p sz (p / 8 + off) HM E1 Hz) as D.
    unfold wok_of, rd_of. destruct (rm rho (Z_to_bv 64 (p / 8 + off))) as [x|]; [split; [reflexivity | exists x; reflexivity] | exfalso; exact (D eq_refl)]. }
  specialize (SP2 VIEW ltac:(constructor)).
  assert (XCL : xwords_clear rho A1 (p / 8 + (SHADOW_OFF + k1)) (p / 8 + (SHADOW_OFF + k2))).
  { intros rr y j Hr Hy Hj Hin. subst A1. cbn [ax_X ax_base ax_setX] in Hr, Hin. rewrite Hbase in Hin. cbn [eval] in Hin.
    rewrite lit_unsigned in Hin. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF in Hin.
    destruct (HXW rr y Hr Hy) as [Hout|(off & len & -> & Ho0 & Hl1 & Hol & Hwc)].
    -
      pose proof (word_in_aligned_range (SHADOW_OFF + y / 8) (Sh p) (sz / 8) j SP8 SS8 Hj ltac:(unfold Sh in *; lia)) as W.
      replace (SHADOW_OFF + y / 8) with (Sh y) in W by (unfold Sh; lia). apply (proj1 (Sh_range_iff p sz y P8 S8)) in W.
      exact (own_frame_sep segs AInv CST XGL ALA HCST HXGL rho0 FB FF Ai rho tp md tv fr i fe y HM HT HB HFF HN HFR Hnth Hout W).
    -
      unfold xlocal in Hy. cbn [fst snd] in Hy. unfold uval in Hy. rewrite U_add in Hy. cbn [eval] in Hy. change (bv_unsigned (rw rho pR)) with p in Hy.
      rewrite !u64_lit in Hy by lia. rewrite <- M64v_eq, (Z.mod_small (p + off) (2 ^ 64)) in Hy by lia.
      set (q := (y - p) / 8).
      pose proof (Z.div_mod (y - p) 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound (y - p) 8 ltac:(lia)) as Mq. pose proof (Z.div_mod p 8 ltac:(lia)) as Dp.
      assert (Hy8 : y / 8 = p / 8 + q) by (subst q; rewrite P8 in Dp; clear - Dq Mq Dp; nia).
      assert (Hq : off / 8 <= q < (off + len + 7) / 8).
      { subst q. split; [apply Z.div_le_mono; clear - Hy; lia|]. apply Z.div_lt_upper_bound; [clear - Hy; lia|].
        pose proof (Z.div_mod (off + len + 7) 8 ltac:(lia)) as DL8. pose proof (Z.mod_pos_bound (off + len + 7) 8 ltac:(lia)) as ML8. first [clear - Hy DL8 ML8; lia | nia]. }
      pose proof (proj1 (forallb_forall _ _) Hwc q (In_granules off len q Ho0 Hl1 Hq)) as WQ. cbn beta in WQ.
      apply orb_prop in WQ. rewrite Hy8 in Hin. unfold Sh in Hin.

      pose proof (Z.div_mod q 8 ltac:(lia)) as Dq8. pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as Mq8.
      assert (WB : (SHADOW_OFF + (p / 8 + q)) / 8 * 8 = SHADOW_OFF + p / 8 + q / 8 * 8).
      { unfold Sh in SP8. pose proof (Z.div_mod (p / 8 + SHADOW_OFF) 8 ltac:(lia)) as DS. rewrite SP8 in DS.
        replace (SHADOW_OFF + (p / 8 + q)) with ((( p / 8 + SHADOW_OFF) / 8 + q / 8) * 8 + q mod 8) by (clear - DS Dq8 Mq8; lia).
        rewrite Z.div_add_l by (clear - Mq8; lia). rewrite (Z.div_small (q mod 8) 8) by (clear - Mq8; lia). clear - DS Dq8 Mq8; lia. }
      rewrite WB in Hin. destruct WQ as [WQ|WQ]; [apply Z.leb_le in WQ | apply Z.leb_le in WQ]; first [ clear - Hin WQ Hj Hq Dq8 Mq8; lia | lia ]. }
  specialize (SP2 XCL).
  assert (EQS : ax_setS A1 (mkSS (ss_pc (ax_S A1)) (ss_regs (ax_S A1)) (ss_fregs (ax_S A1)) (ss_fcsr (ax_S A1)) (ss_resv (ax_S A1))
                          (ss_objs (ax_S A1) ++ [carved (SVar g) (SHADOW_OFF + k1) (SHADOW_OFF + k2) []]) (ss_facts (ax_S A1)) (ss_next (ax_S A)) (ss_lenient (ax_S A1)))
                = shadow_reopen_stateA A X' g k1 k2).
  { subst A1. destruct A as [S X b]. destruct S. reflexivity. }
  rewrite EQS in SP2. destruct SP2 as [Hsm5 HJ5]. split; [exact Hsm5|]. exists Ai, kc. exact HJ5.
Qed.

Lemma JA_shadow_reopen_cells : ltac2:(tb__ "0|d|
S2bS2cScScA2M0A1M1S2bS2cS2cScS0A2M2ScA2M3A1S2bS55A1S43S32S1S0S1S1S0S0S0S0S3dG1S12S2bS5dQ40A1A1M4S78S58RcA1S0SaS3R8R7A2Z8M5A2S0S27S33G3A1S4eG3R13R10A3S35G3S2dG2ScS2dScS0SeRfA1ReA4SeRdA1A4A2A3S26S2Z0M6RfA2S2RfZ6A2A2S27ScS3cR9A1S10S56A1A3S2G6ReA2S26S2RfReA2S2ReS5R6G5A2A2A2S27S2eS3fS2fSfS14S3eR11A1SeR14A1A2S2fSfS15SeR11A1S10S6S8Z2Z3dA2Z1M7A2A1A2S31SfA1A3A3S11S3bRcA1A1A2S30A3G0S4dG0R1RdA3S4dG0R2S40RfA1A3F_;Fr;S4dG0S6cR16S2dS0S0R10RfA4A2S40ReA1A3S2G6R11A2S27S0SaR12G5A2G6A3S2G7R12A2S2G7RcA2S2S3R15R14A2ReA2S2R18S5R16G5A2A2S4S5S3R17R16A2G5A2R18A2S0S28S27S0R1G6A3M8S27S0R1R11A3A2S27S2eS1cS3bS76R18R17R1dR1cR1bS75R1aR19R2A3A6A1A1S30A3F_;FbL;S5aS12G4S52S63SfS16R19A1S11S3bR1bA1A1A3VP0f;Vrho0;A1S65VNP;Vrho0;R1bA3VAInv;R7R6R5R4A4S44Vrho0;R8A2S66R1eS5cS5bR9A1A1A2S45VFB;RaA2S46VFF;RbA2S48VFB;RcR21R30A4S67R22R31A2S68R23R32A2S47VFF;RfR24R32A4S26SdS0S4dSdR2S13S3bR29A1A1A3S26S2S37S0S0S19R28R3A2M9A3R2A2S4R2S38S0S0G9A3A2A2S28S28S61VCST;Vrho0;S69VFB;R29R38A3MaS60VFF;R29R37A3R3A5S26S2G6R3A2S4R3S57A2A2A2S2aS26S2S3S59S54R29SeR33A1A2A1MbR2fA2R3A2S4R3S3GbR2eA2A2A2A1A2F_;F_;Fa;Fo;G0S0S4dG0R2R28A3S26S2S54R28S37ScScR3A3A2McR2A2S4R2S3GcS54R28S38ScScR3A3A2A2A2A2S28S28S61VCST;Vrho0;GaS60VFF;R29S6aG3R34R37A3A3R3A5S62VXGL;R3A2A2S29S0S0S29S0S0S26S27G0R6S6cR35S2dS0S0R2R1A4A2A3S26S2G6R2A2S26S2G7R1A2S26S2S3R2R1A2R28A2S27S2eS6fR31R30R2R1A4S30A3A2A2A2A2Llen';A2Loff';A2A2F_;F_;Fy;Fr;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;S50Vsegs;VJA;S42R25R24R23R22A4A1R18R16R15R14A6S29S0S0S26S28G8S27S0R1R14A3A2S50Vsegs;VJA;S42R27R26R25R24A4A1S76R1aR19R1fR1eR1dS75R1cR1bR1A3A6R18R17R16A6A2LbL;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Tm;Tsz;Fw;Ftp;Frho;FX';FA;Flen;Foff;Fk2;Fk1;Fg;FpF;Fc;FpR;Fi;Fam;Fbd;Ffr;Ftv;").
Proof using ALA HCST HXGL HBX HKc HTOP LFSH HNP.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd am i pR c pF g k1 k2 off len A X' rho tp w sz m Hnth Hc6 Hbase Hk1 Hk2 Hfe2 HX' HinL Ho0 Ho8 Hl1 Hm1 Hols Hkq1 Hkq2 Hwf HSITE [Hsm (Ai & kc & HJ)].
  destruct w as [tr [ms md]].
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  destruct (HSITE Ai rho tp md HF HP0 Hav HM HT (T_ok_of_TPA NP rho0 HNP rho Ai Hav HT) HB HFF HN HD HZ HFR) as [HROK HXW].
  set (fe := (SVar pR, c, SVar pF)) in Hnth. pose proof (nth_error_In _ _ Hnth) as Hfe.
  destruct (own_frame_facts segs AInv CST ALA HCST rho0 FF Ai rho tp md fr fe HM HT HFR Hfe) as (E1 & E2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  cbn [frv fst snd fe] in E1, E2, F1, F2, F3, F4, F5, F6, F7, F8, F9. fold sz in E1, E2, F2, F3, F5.
  set (p := uval rho (SVar pR)) in *.
  unfold aceil in F5, F7. pose proof (fs_frame_size_bounds' c Hc6) as Hszb. fold sz in Hszb.
  assert (P8 : p mod 8 = 0) by (clear -F1; pose proof (Z.div_mod p 64 ltac:(lia)); pose proof (Z.div_mod p 8 ltac:(lia)); nia).
  assert (S8 : sz mod 8 = 0) by (clear -F2 Hszb; pose proof (Z.div_mod sz 64 ltac:(lia)); pose proof (Z.div_mod sz 8 ltac:(lia)); nia).
  assert (SP8 : Sh p mod 8 = 0).
  { unfold Sh, SHADOW_OFF. clear -F1 F4. pose proof (Z.div_mod p 64 ltac:(lia)). pose proof (Z.div_mod (p / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.mod_pos_bound p 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p / 8) 8 ltac:(lia)).
    rewrite Z.add_mod by lia. replace (2147450880 mod 8) with 0 by reflexivity. rewrite Z.add_0_r, Z.mod_mod by lia. nia. }
  assert (SS8 : (sz / 8) mod 8 = 0).
  { clear -F2 Hszb. pose proof (Z.div_mod sz 64 ltac:(lia)). pose proof (Z.div_mod (sz / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod sz 8 ltac:(lia)). pose proof (Z.mod_pos_bound sz 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sz / 8) 8 ltac:(lia)). nia. }
  assert (Hp0 : 0 <= p /\ p + sz <= 2 ^ 47) by (unfold HIGH_SHADOW_END in F4; lia).
  pose proof (has_facts_sound rho _ _ HF Hfe2) as HG. apply Forall_cons_iff in HG as [HG1 HG2]. apply Forall_cons_iff in HG2 as [HG2 _].
  cbn [holds] in HG1, HG2. cbn [eval] in HG2. rewrite (u64_lit (2 ^ 61 - 1)) in HG2 by lia.
  assert (Ug : bv_unsigned (rw rho g) = p / 8).
  { apply (f_equal bv_unsigned) in HG1. unfold g8 in HG1. rewrite U_sll_lit in HG1. cbn [eval] in HG1. change (2 ^ (3 mod 64)) with 8 in HG1.
    pose proof (bv_urange (rw rho g)) as Rg. rewrite <- M64v_eq, Z.mod_small in HG1 by lia.
    change (bv_unsigned (rw rho pR)) with p in HG1. rewrite <- HG1. rewrite Z.div_mul by lia. reflexivity. }
  assert (HNx : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
  pose proof (fbinA_FBx FB Ai rho tv [] HB HNx) as FBX. pose proof (ffinA_FFx FF Ai rho fr HFF HFR) as FFX.
  assert (SHAD : forall z, Sh p + k1 <= z < Sh p + k2 -> is_shadowZ z).
  { intros z Hz. pose proof (Sh_is_shadow p ltac:(lia)) as S1. pose proof (Sh_is_shadow (p + sz - 1) ltac:(lia)) as S2. rewrite Sh_last in S2 by lia.
    unfold is_shadowZ in *. lia. }
  assert (NOSH : forall o a, In o (ss_objs (ax_S A)) -> fst (obj_range rho o) <= a < snd (obj_range rho o) -> ~ (Sh p + k1 <= a < Sh p + k2)).
  { intros o a Hoin Hr Hs. destruct (HROK o a Hoin Hr) as [[Hc|Hi]|Hn]; [| | exact (Hn Hs)].
    - exact (cmaddrA_not_shadow segs AInv CST ALA HCST Ai None a rho tp md HM (pclMA_cmaddrA CST rho0 _ _ Ai a FBX FFX HT Hc) (SHAD a Hs)).
    - pose proof (SHAD a Hs) as S0. unfold is_shadowZ, SHADOW_OFF, IMG_HI in *. lia. }
  assert (XCL : xwords_clear rho (ax_setX A X') (p / 8 + (SHADOW_OFF + k1)) (p / 8 + (SHADOW_OFF + k2))).
  { clear HinL Ho0 Ho8 Hl1 Hm1 Hols Hkq1 Hkq2 Hwf. clear m. intros rr y j Hr Hy Hj Hin. cbn [ax_X ax_base ax_setX] in Hr, Hin. rewrite Hbase in Hin. cbn [eval] in Hin.
    rewrite lit_unsigned in Hin. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF in Hin.
    destruct (HXW rr y Hr Hy) as [Hout|(off1 & len1 & -> & Ho01 & Hl11 & Hol & Hwc)].
    -
      pose proof (word_in_aligned_range (SHADOW_OFF + y / 8) (Sh p) (sz / 8) j SP8 SS8 Hj ltac:(unfold Sh in *; lia)) as W.
      replace (SHADOW_OFF + y / 8) with (Sh y) in W by (unfold Sh; lia). apply (proj1 (Sh_range_iff p sz y P8 S8)) in W.
      exact (own_frame_sep segs AInv CST XGL ALA HCST HXGL rho0 FB FF Ai rho tp md tv fr i fe y HM HT HB HFF HN HFR Hnth Hout W).
    -
      unfold xlocal in Hy. cbn [fst snd] in Hy. unfold uval in Hy. rewrite U_add in Hy. cbn [eval] in Hy. change (bv_unsigned (rw rho pR)) with p in Hy.
      rewrite !u64_lit in Hy by lia. rewrite <- M64v_eq, (Z.mod_small (p + off1) (2 ^ 64)) in Hy by lia.
      set (q := (y - p) / 8).
      pose proof (Z.div_mod (y - p) 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound (y - p) 8 ltac:(lia)) as Mq. pose proof (Z.div_mod p 8 ltac:(lia)) as Dp.
      assert (Hy8 : y / 8 = p / 8 + q) by (subst q; rewrite P8 in Dp; clear - Dq Mq Dp; nia).
      assert (Hq : off1 / 8 <= q < (off1 + len1 + 7) / 8).
      { subst q. split; [apply Z.div_le_mono; clear - Hy; lia|]. apply Z.div_lt_upper_bound; [clear - Hy; lia|].
        pose proof (Z.div_mod (off1 + len1 + 7) 8 ltac:(lia)) as DL8. pose proof (Z.mod_pos_bound (off1 + len1 + 7) 8 ltac:(lia)) as ML8. first [clear - Hy DL8 ML8; lia | nia]. }
      pose proof (proj1 (forallb_forall _ _) Hwc q (In_granules off1 len1 q Ho01 Hl11 Hq)) as WQ. cbn beta in WQ.
      apply orb_prop in WQ. rewrite Hy8 in Hin. unfold Sh in Hin.

      pose proof (Z.div_mod q 8 ltac:(lia)) as Dq8. pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as Mq8.
      assert (WB : (SHADOW_OFF + (p / 8 + q)) / 8 * 8 = SHADOW_OFF + p / 8 + q / 8 * 8).
      { unfold Sh in SP8. pose proof (Z.div_mod (p / 8 + SHADOW_OFF) 8 ltac:(lia)) as DS. rewrite SP8 in DS.
        replace (SHADOW_OFF + (p / 8 + q)) with ((( p / 8 + SHADOW_OFF) / 8 + q / 8) * 8 + q mod 8) by (clear - DS Dq8 Mq8; lia).
        rewrite Z.div_add_l by (clear - Mq8; lia). rewrite (Z.div_small (q mod 8) 8) by (clear - Mq8; lia). clear - DS Dq8 Mq8; lia. }
      rewrite WB in Hin. destruct WQ as [WQ|WQ]; [apply Z.leb_le in WQ | apply Z.leb_le in WQ]; first [ clear - Hin WQ Hj Hq Dq8 Mq8; lia | lia ]. }

  pose proof Hsm as (_ & _ & _ & Hsh & _). unfold shadow_ok in Hsh. rewrite Hbase in Hsh. cbn [eval] in Hsh. rewrite lit_unsigned in Hsh. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF in Hsh.
  pose proof (proj1 (Forall_forall _ _) Hsh _ HinL) as HXR. unfold xr_ok, xlocal in HXR. cbn [fst snd] in HXR. rewrite U_add in HXR. cbn [eval] in HXR.
  change (bv_unsigned (rw rho pR)) with p in HXR. rewrite !u64_lit in HXR by lia. rewrite <- M64v_eq, (Z.mod_small (p + off) (2 ^ 64)) in HXR by lia.
  destruct HXR as (_ & _ & HXall).
  assert (Dol : off + len = 8 * ((off + len) / 8) + m) by (subst m; apply Z.div_mod; lia).
  assert (Hm8 : 0 <= m < 8) by (subst m; apply Z.mod_pos_bound; lia).
  assert (Doff : off = 8 * (off / 8)) by (pose proof (Z.div_mod off 8 ltac:(lia)); lia).
  assert (GR : forall q, off / 8 <= q <= (off + len) / 8 -> exists v, rm rho (Z_to_bv 64 (SHADOW_OFF + p / 8 + q)) = Some v
              /\ (bv_unsigned v = 0 \/ (bv_unsigned v = m /\ q = (off + len) / 8))).
  { intros q Hq. destruct (HXall (p + 8 * q) ltac:(lia)) as (_ & _ & _ & v & Hv & Hd).
    assert (E8 : (p + 8 * q) / 8 = p / 8 + q).
    { pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. rewrite P8, Z.add_0_r in Dp. rewrite Dp at 1. rewrite <- Z.mul_add_distr_l, Z.mul_comm, Z.div_mul by lia. reflexivity. }
    unfold shadow_addr in Hv. rewrite E8 in Hv. exists v. split; [replace (SHADOW_OFF + p / 8 + q) with (SHADOW_OFF + (p / 8 + q)) by lia; exact Hv|].
    destruct Hd as [Hd|[Hd1 Hd2]]; [left; exact Hd | right]. rewrite E8 in Hd2.
    assert (EM : (p + off + len) mod 8 = m) by (subst m; replace (p + off + len) with ((off + len) + p) by lia; rewrite Z.add_mod, P8, Z.add_0_r, Z.mod_mod by lia; reflexivity).
    assert (ED : (p + off + len) / 8 = p / 8 + (off + len) / 8).
    { pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. rewrite P8, Z.add_0_r in Dp. replace (p + off + len) with (8 * (p / 8 + (off + len) / 8) + m) by lia.
      rewrite Z.mul_comm, Z.div_add_l, (Z.div_small m 8) by lia. lia. }
    rewrite EM in Hd1. rewrite ED in Hd2. split; [exact Hd1 | lia]. }
  destruct (GR ((off + len) / 8) ltac:(pose proof (Z.div_le_mono off (off + len) 8 ltac:(lia) ltac:(lia)); lia)) as (vL & HvL & HdL).
  set (bL := bv_unsigned vL).
  assert (HbL : bL = 0 \/ bL = m) by (destruct HdL as [HdL|[HdL _]]; [left | right]; exact HdL).
  exists bL. split; [exact HbL|]. specialize (Hwf bL HbL).

  pose proof (SPA_x_sub segs _ rho A X' tp _ HX' (conj Hsm HJ)) as SP1.
  set (A1 := ax_setX A X') in SP1.

  pose proof (SPA_carve_obj segs (JAi (NDA tv fr bd am) Ai kc) rho A1 tp (tr, mkCfg ms md) (SVar g) (SHADOW_OFF + k1) (SHADOW_OFF + k2) (gcs off len bL) (ss_next (ax_S A)) SP1) as SP2.
  cbn [eval] in SP2. rewrite Ug in SP2.
  assert (Hwf1 : swf (mkSS (ss_pc (ax_S A1)) (ss_regs (ax_S A1)) (ss_fregs (ax_S A1)) (ss_fcsr (ax_S A1)) (ss_resv (ax_S A1))
                          (ss_objs (ax_S A1) ++ [carved (SVar g) (SHADOW_OFF + k1) (SHADOW_OFF + k2) (gcs off len bL)]) (ss_facts (ax_S A1)) (ss_next (ax_S A)) (ss_lenient (ax_S A1))) = true).
  { subst A1. cbn [ax_S ax_setX]. unfold shadow_reopen_cells_stateA in Hwf. cbn [ax_S] in Hwf. exact Hwf. }
  assert (HCI : cells_inside (SHADOW_OFF + k1) (SHADOW_OFF + k2) (gcs off len bL)).
  { unfold cells_inside, gcs. apply Forall_app. split.
    - apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as (q & <- & Hq). apply In_zrange in Hq.
      rewrite Z2Nat.id in Hq by (pose proof (Z.div_le_mono off (off + len) 8 ltac:(lia) ltac:(lia)); lia). lia.
    - constructor; [|constructor]. lia. }
  specialize (SP2 Hwf1 ltac:(subst A1; cbn [ax_S ax_setX]; lia) ltac:(unfold SHADOW_OFF; lia) ltac:(lia) ltac:(unfold SHADOW_OFF; lia) ltac:(lia)
                  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia) HCI).
  assert (DISJ : Forall (fun o' => ranges_disjoint (obj_range rho o') (p / 8 + (SHADOW_OFF + k1), p / 8 + (SHADOW_OFF + k2))) (ss_objs (ax_S A1))).
  { subst A1. cbn [ax_S ax_setX]. apply Forall_forall. intros o Ho'.
    destruct (obj_range rho o) as [lo hi] eqn:Eo. apply ranges_disjoint_by_points. intros a Ha1 Ha2.
    apply (NOSH o a Ho'); [rewrite Eo; exact Ha1|]. unfold Sh. lia. }
  specialize (SP2 DISJ).
  assert (VIEW : forall off0, SHADOW_OFF + k1 <= off0 < SHADOW_OFF + k2 ->
             wok_of segs (rm rho) (Z_to_bv 64 (p / 8 + off0)) = true /\ exists x, rd_of segs (rm rho) (Z_to_bv 64 (p / 8 + off0)) = Some x).
  { intros off0 Hoff.
    assert (Hz : Sh p <= p / 8 + off0 < Sh (p + sz)).
    { unfold Sh in *. pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.div_mod sz 8 ltac:(lia)). rewrite P8 in *. rewrite S8 in *.
      replace (p + sz) with ((p / 8 + sz / 8) * 8) by lia. rewrite Z.div_mul by lia. lia. }
    pose proof (LFSH Ai rho tp md p sz (p / 8 + off0) HM E1 Hz) as D.
    unfold wok_of, rd_of. destruct (rm rho (Z_to_bv 64 (p / 8 + off0))) as [x|]; [split; [reflexivity | exists x; reflexivity] | exfalso; exact (D eq_refl)]. }
  assert (HCV : cells_in_view rho (rd_of segs (rm rho)) (p / 8) (gcs off len bL)).
  { assert (ONE : forall q v bq, rm rho (Z_to_bv 64 (SHADOW_OFF + p / 8 + q)) = Some v -> bv_unsigned v = bq -> 0 <= bq < 8 ->
              forall j, (j < 1)%nat -> rd_of segs (rm rho) (Z_to_bv 64 (p / 8 + (SHADOW_OFF + q) + Z.of_nat j)) = Some (nth j (enc_bytes 1 (eval rho (SLit bq))) (Z_to_bv 8 0))).
    { intros q v bq Hv Hbq Hb8 j Hj. assert (j = 0%nat) by lia. subst j. change (Z.of_nat 0) with 0.
      replace (p / 8 + (SHADOW_OFF + q) + 0) with (SHADOW_OFF + p / 8 + q) by lia. unfold rd_of. rewrite Hv. f_equal.
      unfold enc_bytes. cbn [eval Z_to_le_bytes nth]. rewrite lit_unsigned, Z.mod_small by lia. rewrite <- Hbq. symmetry. apply Z_to_bv_bv_unsigned. }
    unfold cells_in_view, gcs. apply Forall_app. split.
    - apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as (q & <- & Hq). apply In_zrange in Hq.
      rewrite Z2Nat.id in Hq by (pose proof (Z.div_le_mono off (off + len) 8 ltac:(lia) ltac:(lia)); lia).
      destruct (GR q ltac:(lia)) as (v & Hv & Hd). destruct Hd as [Hd|[_ Hd]]; [|lia].
      exact (ONE q v 0 Hv Hd ltac:(lia)).
    - constructor; [|constructor]. refine (ONE _ vL bL HvL eq_refl _). destruct HbL as [->| ->]; lia. }
  specialize (SP2 VIEW HCV).
  specialize (SP2 XCL).
  assert (EQS : ax_setS A1 (mkSS (ss_pc (ax_S A1)) (ss_regs (ax_S A1)) (ss_fregs (ax_S A1)) (ss_fcsr (ax_S A1)) (ss_resv (ax_S A1))
                          (ss_objs (ax_S A1) ++ [carved (SVar g) (SHADOW_OFF + k1) (SHADOW_OFF + k2) (gcs off len bL)]) (ss_facts (ax_S A1)) (ss_next (ax_S A)) (ss_lenient (ax_S A1)))
                = shadow_reopen_cells_stateA A X' g k1 k2 (gcs off len bL)).
  { subst A1. destruct A as [S X b]. destruct S. reflexivity. }
  rewrite EQS in SP2. destruct SP2 as [Hsm5 HJ5]. split; [exact Hsm5|]. exists Ai, kc. exact HJ5.
Qed.

End Sum.
End WithSegs.
