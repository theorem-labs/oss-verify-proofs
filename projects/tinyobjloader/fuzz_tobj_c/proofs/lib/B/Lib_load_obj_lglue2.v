(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bd_subst"; "bitem"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "pair"; "nat"; "prod"; "list"; "bool"; "true"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLC"; "pI"; "HNEXT"; "K_loop"; "X_latch"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "add"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "JA"; "am_eqb"; "am_subst"; "amode"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "VLA"; "RL"; "z0"; "Mline"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "bud_le2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "tvL"; "s_loop"; "X_latchA"; "tblB"; "tblL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma VLA_val_le : ltac2:(tb__ "0|2|
S18S3S19SaS12Z0R2A2S13R2Z40A2A2S12S0R4SeA2S0R4SdA2A2S12S0R5SdA2S14Z2M0Z1aA2A2S13S0R6R4A2S14G0Z1bA2M1A2SbS3S0R7S24R6R5A2A2S15S15S16S27S17S0R7SdA2S0R7SeA2A2A2S16G1R6A2A2S0R7R5A2A2A3F_;F_;F_;F_;Finner;Fph;Frho;").
Proof.
  intros rho ph inner Hph Hi Hc Hin. pose proof (uval_range rho pI) as RI. pose proof (uval_range rho inner) as RN.
  assert (E1 : uval rho (SAlu ALU_SUB xLC pI) = uval rho xLC - uval rho pI) by (apply uval_sub_le; lia).
  assert (E2 : uval rho (SMd M_MUL (SLit Mline) (SAlu ALU_SUB xLC pI)) = Mline * (uval rho xLC - uval rho pI)).
  { rewrite uval_mul_lit by (unfold Mline; rewrite ?E1; lia). rewrite E1. reflexivity. }
  unfold VLA. rewrite uval_add_small by (rewrite uval_add_small by (rewrite E2, uval_lit by (unfold Mline; lia); unfold Mline; lia); rewrite E2, uval_lit by (unfold Mline; lia); unfold Mline; lia).
  rewrite uval_add_small by (rewrite E2, uval_lit by (unfold Mline; lia); unfold Mline; lia).
  rewrite E2, uval_lit by (unfold Mline; lia). reflexivity.
Qed.

Lemma meas_latch : ltac2:(tb__ "0|6|
S18S18S3S3S1bS1bS1dS1dS5S5SbS3S0R9SeA2S15S0RaSeA2Z1A2A3SbS3S0RaSdA2S0RbSdA2A3S13S0RcSeA2S0RcSdA2A2S12S0RdSdA2S14Z2Z1aA2A2SaS12Z0M0RbA2S13RbZ40M1A2A2SaS12G0RdA2S13RdG1A2A2SaS12G0S28S4S6S6S1bS1dA2M2S5A2M3S6S3S19A2M4S4G2S5S4S1bS1dRbR9A4R7A4S4S3S19S25S24RdS26A2A4A4RfA2M5A2S13G5S28S4G3G4S4G2S5S4S1bS1dRcRaA4R8A4S4S3S19S25S24ReS26A2A4A4R10A2A2A2F_;F_;F_;F_;F_;F_;Fk';Fk;Fnd';Fnd;FX';FX;Fph';Fph;Frho';Frho;").
Proof.
  intros rho rho' ph ph' X X' nd nd' k k' EI EC Hi Hc Hph' Hph.
  rewrite !efmeasA_VLA. rewrite (VLA_val_le rho' ph' z0) by (unfold z0; rewrite ?uval_lit; lia). rewrite (VLA_val_le rho ph z0) by (unfold z0; rewrite ?uval_lit; lia).
  unfold z0. rewrite !uval_lit by lia. rewrite EI, EC. pose proof (uval_range rho pI). unfold Mline, RL.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 37) with 137438953472. change (2 ^ 27) with 134217728 in *. change (2 ^ 26) with 67108864 in *. lia.
Qed.

Lemma meas_same : ltac2:(tb__ "0|5|
S18S18S3S3S1bS1bS1dS1dS5S5SbS3S0R9SeA2S0RaSeA2A3SbS3S0RaSdA2S0RbSdA2A3S13S0RcSeA2S0RcSdA2A2S12S0RdSdA2S14Z2Z1aA2A2SaS12Z0M0RbA2S13RbRcA2A2S13RdZ40A2SaS12G0S28S4S6S6S1bS1dA2M1S5A2M2S6S3S19A2M3S4G1S5S4S1bS1dRbR9A4R7A4S4S3S19S25S24RdS26A2A4A4RfA2M4A2S13G4S28S4G2G3S4G1S5S4S1bS1dRcRaA4R8A4S4S3S19S25S24ReS26A2A4A4R10A2A2A2F_;F_;F_;F_;F_;F_;Fk';Fk;Fnd';Fnd;FX';FX;Fph';Fph;Frho';Frho;").
Proof.
  intros rho rho' ph ph' X X' nd nd' k k' EI EC Hi Hc Hph' Hph.
  rewrite !efmeasA_VLA. rewrite (VLA_val_le rho' ph' z0) by (unfold z0; rewrite ?uval_lit; lia). rewrite (VLA_val_le rho ph z0) by (unfold z0; rewrite ?uval_lit; lia).
  unfold z0. rewrite !uval_lit by lia. rewrite EI, EC. pose proof (uval_range rho pI). unfold Mline, RL.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 37) with 137438953472. change (2 ^ 27) with 134217728 in *. change (2 ^ 26) with 67108864 in *. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S3aS18S7S34Q40A1A1S35OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S39S2aVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S3S33VCST;R1A2SaS12Z0R2A2S13R2S32A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S3S33VXGL;R1A2SaS12Z0R2A2S13R2S32A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S7S6S6S3S3A2S3A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Variable rho0 : valuation.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S18OFr;") := ltac2:(tb__ "0|0|
S37VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S1fVAInv;VCST;VXGL;S36VKc;Vrho0;VP0;VFB;VFF;VBX;VPA;Vnd;Ac").

Lemma latch_absorb2 : ltac2:(tb__ "0|3|
S7S2A1M0G0S22S18S7S34Q40A1A1S38SbS8S23SfS1eS2cS2bR6R4A4A2S9A3SbS8S29S1aS1cS2eA1A1S1S2dR6A2R7A3S9A3SbS8S20S21S2dR6A2R6A2S9A3S2fR6A1S31S2aVJAv;S1eS2cS2bRaR8A4A1S11R7R6R5A6ScS18S18SaS30R1A1SaS31S2aVJAv;S1eS2cS2bRbRaA4A1S10R1R8R7A6SaSbS3S0R1SdA2S0R9SdA2M1A3SaSbS3S0R1SeA2S15S0R9SeA2M2Z1A2A3SaS13G2G1A2S12G1S14Z2Z1aA2A2A2A2A2A2A2Lrho2;A2F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fam;Fbdj;Fbdi;").
Proof.
  intros bdi bdj am rho tp w Hnb Hbud Ham ([HT HDEF] & R0 & R1) HS. destruct w as [tr [ms md]].
  pose proof lglue_checks as (Cnth & _). pose proof lglue_checks2 as (Cobjs & Cdrop & Cent & Cid & Ctv).
  pose proof (smatchA_facts segs _ _ _ _ (proj1 HS)) as HF.
  destruct (ent_addrX rho HF) as (EA & Hi & Hck & Hk32 & Hd47 & EK & HL26).
  assert (HcL : uval rho xLC <= uval rho vLEN).
  { factz HF (SPUle xLC vLEN) X. exact X. }
  assert (EB : uval rho (ob_base (O_ent pI pPOS pLNL)) = uval rho xLD + 16 * uval rho pI) by (cbn [ob_base O_ent]; exact EA).
  destruct (JA_absorb_ent_same segs HTOP AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PA tvL frL bdi am jL xLD (kb 16 xLK) X_latch Xl_objs (O_ent pI pPOS pLNL)
              pPOS pLNL rho tp tr ms md Cobjs Cnth eq_refl eq_refl eq_refl ltac:(cbn; auto) ltac:(cbn; auto) ent_rangeX
              ltac:(rewrite EB; exact R0) ltac:(rewrite EB; exact R1) HS) as [SP1 HRM].
  rewrite Cdrop in SP1. set (rho1 := rho_absorb rho [O_ent pI pPOS pLNL] (vms md tp ms)) in *.
  pose proof (uval_range rho pI) as RI0.
  assert (EI1 : uval rho (SAlu ALU_ADD pI (SLit 1)) = uval rho pI + 1) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  exists (rho_sub rho1 s_loop). split; [|split; [|split; [reflexivity | split; [|split; [exact Hi | lia]]]]].
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
    assert (EE1 : uval rho (SAlu ALU_ADD pE (SLit 1)) = uval rho pPOS + uval rho pLNL + 1).
    { unfold pE. rewrite uval_add_small by (rewrite uval_add_small, uval_lit by lia; lia). rewrite uval_add_small by lia. rewrite uval_lit by lia. lia. }
    rewrite EE1. rewrite EI1 in Hq. replace (Z.to_nat (uval rho pI + 1)) with (S (Z.to_nat (uval rho pI))) in Hq by lia.
    pose proof (lines_next_pos T _ _ p q HOK Ep Hq). lia.
  - apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc X_latchA K_loop s_loop (NDA tvL frL bdi am) (NDA tvL frL bdj am) rho1 tp _ Cent Cid);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | | exact Ctv | reflexivity | exact Hbud | exact Ham | exact SP1].
    apply (nd_below_mono HNEXT); [apply (proj1 (Pos.leb_le _ _)); reflexivity | exact Hnb].
  - change (uval (rho_sub rho1 s_loop) pI) with (uval rho (SAlu ALU_ADD pI (SLit 1))). exact EI1.
Qed.
End Sum.
