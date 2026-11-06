(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_023.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er Lib_fuzz_one ej.

(* [comment removed for export] *)
Module Lib_load_obj_lglue2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bd_subst"; "bitem"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "pair"; "nat"; "prod"; "list"; "bool"; "true"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "xLC"; "pI"; "HNEXT"; "K_loop"; "X_latch"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "add"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "NDA"; "JA"; "am_eqb"; "am_subst"; "amode"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "VLA"; "RL"; "z0"; "Mline"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "bud_le2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "tvL"; "s_loop"; "P0_lo"; "X_latchA"; "tblB"; "tblL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2.
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
S3aS18S7S35Q40A1A1S36OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S39S2aVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S3S34VCST;R1A2SaS12Z0R2A2S13R2S33A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S3S34VXGL;R1A2SaS12Z0R2A2S13R2S33A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S7S6S6S3S3A2S3A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Variable rho0 : valuation.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S18OFr;") := ltac2:(tb__ "0|0|
S2eVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S1fVAInv;VCST;VXGL;S37VKc;Vrho0;VP0;VFB;VFF;VBX;VPA;Vnd;Ac").

Lemma latch_absorb2 : ltac2:(tb__ "0|3|
S7S2A1M0G0S22S18S7S35Q40A1A1S38SbS8S23SfS1eS2cS2bR6R4A4A2S9A3SbS8S29S1aS1cS2fA1A1S1S2dR6A2R7A3S9A3SbS8S20S21S2dR6A2R6A2S9A3S30R6A1S32S2aVJAv;S1eS2cS2bRaR8A4A1S11R7R6R5A6ScS18S18SaS31R1A1SaS32S2aVJAv;S1eS2cS2bRbRaA4A1S10R1R8R7A6SaSbS3S0R1SdA2S0R9SdA2M1A3SaSbS3S0R1SeA2S15S0R9SeA2M2Z1A2A3SaS13G2G1A2S12G1S14Z2Z1aA2A2A2A2A2A2A2Lrho2;A2F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fam;Fbdj;Fbdi;").
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
End Lib_load_obj_lglue2.

(* [comment removed for export] *)
Module Lib_load_obj_hvkit.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "nat"; "pair"; "prod"; "bool"; "list"; "true"; "cons"; "nil"; "option"; "snd"; "andb"; "app"; "fst"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "rw"; "sprop"; "sv_eqb"; "SLit"; "holds"; "ob_base"; "ob_lo"; "obj_range"; "ss_objs"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "pow"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "TPA"; "frinA"; "tvinA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "VLAi"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "RL"; "VLA"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "seq"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "xLC"; "pI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "robj_ent"; "robjs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "V_B"; "V_L"; "extraLO"; "tblB"; "tblL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T0"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "pclMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "robj_image"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Lists.List"; "In"; "combine"; "existsb"; "filter"; "find"; "forallb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import LOAddr LOLAddr.

Definition VLAi (ph a : Z) : sv := ltac2:(tb__ "0|0|
S2cVph;S17Va;A1A2").
Lemma VLAi_z0 : ltac2:(tb__ "0|0|
S0S21S12S2cR1S2dA2S29R1Z0A2A3Fph;"). Proof. reflexivity. Qed.

Lemma VLA_lt2 : ltac2:(tb__ "0|a|
S13S13S0S0S0S0S23S23S25S25S2S2S21S2fQ40A1M0S14RbP1ccM1A2S14RcG1A2A3S21G0S14RcP1d3M2A2S14RdG2A2A3S1dS2eReS34A2S2eReS33A2A2S1eS2eRfS33A2S1fZ2M3Z1aA2A2S20S1eZ0M4RbA2S1dRbS1fG3Z1bA2M5A2A2S20S1eG4RdA2S1dRdG5A2A2S1eG4RfA2S1dR11Z40A2S22S1dR11R12A2S20S21S0R11R12A3S1dRfR10A2A2A2S20S1eG4S35S3S4S4S23S25A2M6S2A2M7S4S0S12A2M8S3G6S2S3S23S25ReRcA4RaA4S3S0S12S2bS29R12R10A2A4A4R14A2M9A2S1dG9S35S3G7G8S3G6S2S3S23S25RfRdA4RbA4S3S0S12S2bS29R13R11A2A4A4R15A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fk';Fk;Fnd';Fnd;FX';FX;Fa';Fa;Fph';Fph;Frho';Frho;").
Proof.
  intros rho rho' ph ph' a a' X X' nd nd' k k' E460 E467 Hi Hc Ha' Ha Hph' Hph Hlt.
  assert (EI : uval rho' pI = uval rho pI) by (unfold uval, pI; cbn [eval]; rewrite E460; reflexivity).
  assert (EC : uval rho' xLC = uval rho xLC) by (unfold uval, xLC; cbn [eval]; rewrite E467; reflexivity).
  unfold VLAi. rewrite !efmeasA_VLA.
  rewrite (VLA_val rho' ph' (SLit a')); [| lia | rewrite EI, EC; exact Hi | rewrite EC; exact Hc | rewrite uval_lit by lia; lia].
  rewrite (VLA_val rho ph (SLit a)); [| lia | exact Hi | exact Hc | rewrite uval_lit by lia; lia].
  rewrite !uval_lit by lia. rewrite EI, EC. pose proof (uval_range rho pI). unfold Mline, RL.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 37) with 137438953472. change (2 ^ 27) with 134217728 in *. change (2 ^ 26) with 67108864 in *. lia.
Qed.

Definition oidx (b lo : sv) (T : axst) : nat := ltac2:(tb__ "0|3|
SaS4S2S11A2M0A1S2Lx;S51G0G0ScS16S19SbS2S11R1A3M1A1Vb;A2S16S1aG1A1Vlo;A2A2Lp;S4eS2S11S30U0SfS11S1cS24VT;A1A1M2A2A2G2A4A3G0G0S2Lp;R1S2S11R2Ls;Li;X4x1Lp;U3e7Xax2").
Definition spA : sv := SVar 10.
Definition s1A : sv := SAlu ALU_ADD spA (SLit (-512)).

Definition sel_front (sel : list nat) (n : nat) : axform := ltac2:(tb__ "0|0|
S44SdS2Vsel;S50S2S2S10S4fS2S4cR1A1Vsel;A3A1Li;S30U0Vn;A2A3A3A1").

Definition robjs_chkR (facts : list sprop) (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (extra : sobj -> bool) (R : list sobj) : bool := ltac2:(tb__ "0|0|
S52S11S11S5S5L_;S48R1A1S7S39Vfacts;Vtv;Vfr;Vextra;S8S11R1S9S11A1A3A5X5x2Lo;VR;A3").

Section SiteR.
Variable AInv : ltac2:(tb__ "0|0|
S36S13S6S2fQ40A1A1S32OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S4aS37VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S4bVCST;R1A2S20S1eZ0R2A2S1dR2S49A2A2F_;Fa;").
Variable rho0 : valuation.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S6S4S4S0S0A2S0A2A1").

Lemma robjs_chkR_sound : ltac2:(tb__ "0|1|
S36S13S6S15A1S6S4S12S12A2A1S6S4S4S12S0A2S12A2A1S11S5F_;S6S11A1S13S6S2fQ40A1A1S32VAInv;RaR3R2R1A4S31S15S18RaA1R9A3S26Vrho0;RcA2S41RcS40Vrho0;A1A2S28VFB;ReRdRbA4S42ReRcA2S43RfRdA2S27VFF;R11R10RdA4S21S5S2aR10RfReRdRcA5S7A3S11S0S4dS11R2RfA3S21S5R11R3A1S7A3S20S1eSeS0S0S1bR16R4A2M0A3R3A2S1dR3SbS0S0G0A3A2A2S46VCST;Vrho0;S3fVFB;R17R15A3S45VFF;R17R14A3R4A5F_;F_;F_;Fa;Fo;S47VCST;Vrho0;VFB;VFF;R13R11R10ReA8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fextra;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv fr extra R rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR Hchk Hextra o a Ho Hr.
  unfold robjs_chkR in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk o Ho) as Hc. cbv beta in Hc.
  apply lazy_orb_prop in Hc as [Hc|Hc].
  - right. unfold TobjJAS.robj_image in Hc. destruct (ob_base o) as [b0| | | | | | |] eqn:Eb; try discriminate. destruct b0; try discriminate.
    destruct (ob_lo o) as [lo| | | | | | |] eqn:El; try discriminate. destruct (ob_hi o) as [hi| | | | | | |] eqn:Eh; try discriminate.
    apply lazy_andb_prop in Hc as [H1 Hc]. apply lazy_andb_prop in Hc as [H2 H3]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Eb, El, Eh in Hr. cbn [eval fst snd] in Hr. unfold IMG_HI in *.
    rewrite (u64_lit 0), !soff_lit_small in Hr by lia. lia.
  - left. apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho facts tv fr extra [o] rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR Hc) with (o := o); [| left; reflexivity | exact Hr].
    intros o' a' [<-|[]] HE Hr'. exact (Hextra o a' Ho HE Hr').
Qed.
End SiteR.

Definition PhisH : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|3|
S8S4S6S1A1M0S13OFrho;M1A2M2S3G0G1S3bS3eA4S8G2S3G0G1S3aS3dA4S9G2A1A3A3").
Definition mH (ph a : Z) : Z * sv := ltac2:(tb__ "0|0|
S3S0S12S2bS29Vph;Va;A2A4").
Definition extra_hv (o : sobj) : bool := ltac2:(tb__ "0|0|
S5S5L_;S3cVo;A1S7S38Vo;A1X5x2").
End Lib_load_obj_hvkit.

(* [comment removed for export] *)
Module Lib_fuzz_one_ad.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nat"; "pair"; "nil"; "prod"; "Some"; "list"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sprop"; "SPBranch"; "sprop_eqb"; "swf"; "SPNot"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "entailsA"; "ax_base"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXSelect"; "AXRebase"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_fuzz_one_ad"; "Pre_fr"; "E_fd"; "C_L"; "E_fa"; "K_fa"; "s_fa"; "s_fd"; "L_fr"; "X_A1"; "T_fa"; "R_fa"; "R_fd"; "X_A2"; "X_B"; "X_B2"; "X_fa0"; "X_fa1"; "vNx"; "E_fa1"; "E_fd0"; "E_fd1"; "L_L1"; "L_L3"; "T_fa0"; "T_fd"; "T_fd0"; "X_A"; "nB"; "s_L1"; "s_L3"; "s_fa0"; "s_fa1"; "s_free"; "szB"; "vCap"; "vG"; "vNd"; "xf_fd"; "xfb_fd"; "E_fa0"; "Ls_fd"; "Ls_ok"; "fd_after0"; "gA"; "hnz"; "xf_fa"; "xfb_fa"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_one"; "showL"; "runF"; "Fx"; "optL"; "ax_tidy"; "dropX"; "pH"; "free_pc"; "nx"; "pAR"; "pc_L"; "pc_fa"; "pc_sx"; "T_err"; "body_shape"; "glob_shape"; "nobj"; "optR"; "pc_adA"; "pc_adB"; "shapes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.Lists.List"; "existsb"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD"; "pop_stateA"; "lenN_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_fuzz_one_glue"; "WIN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "@Stdlib.ZArith.BinInt.Z"; "opp"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_fuzz_iface2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_fuzz_one.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_fuzz_one_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_one.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import FZAddr.

Definition L_sxE : axst := Eval vm_compute in leafF (runF T_err) pc_sx 0.

Definition Ls_ok : list leafA := Eval vm_compute in runF T_suc.
Definition X_fa0 : axst := Eval vm_compute in leafF Ls_ok pc_fa 0.
Definition X_A : axst := Eval vm_compute in leafF Ls_ok pc_adA 0.
Definition hnz : sprop := ltac2:(tb__ "0|0|
S14S11S6cS5bSeZ0A1A3A1").
Definition X_A1 : axst := Eval vm_compute in lenN_stateA X_A.
Definition gA : sv := Eval vm_compute in SVar (nx X_A).
Definition X_A2 : axst := Eval vm_compute in pop_stateA X_A1 pH gA.
Definition L_L1 : axst := Eval vm_compute in leafF (runF X_A2) pc_L 0.

Definition Pre_fr : axst := Pre_free AE_A (Wcan 1) UStopLe.
Definition L_fr : axst := L_free AE_A (Wcan 1) UStopLe.
Definition s_free (E : axst) (sz : sv) : wsub := ltac2:(tb__ "0|1|
S2S8S1cSdA2M0S6S1cSdS7aSeS7bS79A1A1A4S2G0S6S1cSdPdVsz;A4S6aPaS17VE;A1S17S26A1A3A3A3").
Definition szB (cap : sv) : sv := SAlu ALU_ADD cap (SLit 32).

Definition xf_fd (A : axst) : list axform := ltac2:(tb__ "0|1|
S2S20S24S73S65VA;A1M0U1A2A1S2S20S22S73G0U2A2A1S2S20S25U3SeN10A1A2S7S20A1A3A3A3").
Definition fd_site (E0 : axst) (hd : sv) : axst := ltac2:(tb__ "0|0|
S5aVhd;S58S21VE0;S4bVE0;A1A2A1A2").
Definition fd_after0 (E : axst) (sz : sv) : axst := ltac2:(tb__ "0|1|
S71S26VE;S46VE;Vsz;A2M0S66S6fVE;S26G0A3A1S2dA5").
Definition xfb_fd : list axform := ltac2:(tb__ "0|1|
S2S20S23S2S5U0S2S5U4S2S5U5S2S5U6S2S5U1S2S5U7S2S5U8S2S5U9S2S5UaS2S5UbS2S5UcS2S5U2S2S5U3M0S7S5A1A3A3A3A3A3A3A3A3A3A3A3A3A3A1S2S20S22G0A1S7S20A1A3A3").
Definition fd_after (E : axst) (sz : sv) : axst := ltac2:(tb__ "0|0|
S59S58S21S50VE;Vsz;A2S4cA2A1A1").

Definition Eb_fd : axst := Eval vm_compute in fd_site (leafF (runF L_L1) free_pc 0) pH.
Definition Tb_fd : axst := Eval vm_compute in fd_after Eb_fd (szB (SVar 287)).
Definition Xb_B : axst := Eval vm_compute in leafF (runF Tb_fd) pc_adB 0.
Definition Xb_B2 : axst := Eval vm_compute in pop_stateA Xb_B (SVar 286) (SVar 289).
Definition L_L2 : axst := Eval vm_compute in leafF (runF Xb_B2) pc_L 0.

Definition vNd : sv := SVar 286.  Definition vNx : sv := SVar 331.  Definition vCap : sv := SVar 332.  Definition vG : sv := SVar 334.  Definition vGp : sv := SVar 289.
Definition C_L : axst := Eval vm_compute in dropV [285]%positive (junkRN [1; 23]%nat L_L2).
Definition s_L1 : wsub := ltac2:(tb__ "0|2|
S2S8S1cSdA2M0S6S1cSdP14eSfP121M1A1A4S2G0S6S1cSdG1SfP11dA1A4S2G0S6S1cSdP14fSfP122A1A4S6aS1fS17S3bA1S17S28A1A3A3A3A3").

Definition E_fd0 : axst := Eval vm_compute in leafF (runF C_L) free_pc 0.
Definition E_fd1 : axst := Eval vm_compute in optL (apply_axforms E_fd0 (xf_fd E_fd0)).
Definition E_fd : axst := Eval vm_compute in dropX vNd E_fd1.
Definition s_fd : wsub := ltac2:(tb__ "0|0|
S46S27S47S48A1A2").
Definition R_fd : list sobj := Eval vm_compute in optR (entails_frA E_fd Pre_fr s_fd).
Definition T_fd0 : axst := Eval vm_compute in T_afterA Pre_fr E_fd s_fd R_fd L_fr.
Definition T_fd : axst := Eval vm_compute in ax_tidy (optL (apply_axforms T_fd0 xfb_fd)).
Definition Ls_fd : list leafA := Eval vm_compute in runF T_fd.
Definition X_fa1 : axst := Eval vm_compute in leafF Ls_fd pc_fa 0.
Definition X_B : axst := Eval vm_compute in leafF Ls_fd pc_adB 0.
Definition nB : positive := Eval vm_compute in nx X_B.
Definition X_B2 : axst := Eval vm_compute in pop_stateA X_B vNx vG.
Definition L_L3 : axst := Eval vm_compute in leafF (runF X_B2) pc_L 0.
Definition s_L3 : wsub := ltac2:(tb__ "0|1|
S2S8S1cSdA2M0S6S1cSdP14eSfS77S41P3A2A1A4S2G0S6S1cSdP121S49A4S2G0S6S1cSdP14fSfS77S41P4A2A1A4S6aS1fS17S3cA1S17S28A1A3A3A3A3").

Lemma fz_checks_loop1 : ltac2:(tb__ "0|4|
S1S0SaS8S1bS1dA2M0A1M1S55S56S62A1A1S2G0S6S1bS1dS61S1eA4S7G0A1M2A3A3S1S0G1S55S4fA1S2G0S6S1bS1dS60S1eA4S2G0S6S1bS1dS67S1eA4G2A3A3A3S1S0S3S6bS10S12S52A1M3S57S40A1A3S4A3S1S0S16S75S40A1S2eA3S1S0S3S13S17S2eA1A1S4A3S1S0S16S74S2eS5bS51A3S32A3S1S0S3S13S17S32A1A1S4A3S1S0SdS1aS2eA1SeS76A1A3S1S0S3S6bS10G3S57S2eA1A3S4A3S1S0G1S55S56S32A1A1S2G0S6S1bS1dS5fS1eA4G2A3A3S1S0S3S18S28A1S4A3S1S0S3S19S3bS28S42A3S4A3S0S3S6eS42S1fA2S4A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma fz_checks_fd : ltac2:(tb__ "0|7|
S1S0SaS8S1bS1dA2M0A1M1S55S56S28A1A1S2G0S6S1bS1dS5cS1eA4S7G0A1M2A3A3S1S0SbS16A1M3S21S39S4bS39A1A2S9S16S3aA2A3S1S0S16S5aS4aS3aA2S27A3S1S0S3S18S27A1S4A3S1S0SbSaS15A1M4A1S6fS27S26S2cA3S9G4S31A2A3S1S0S3S70S27S26S2cS31S2S16S2dS7S16A1A3A5S4A3S1S0S3S72S1fS2cA2S4A3S1S0S3S78S1fS5dS27A1A2S4A3S1S0SdS6dS2cPcA2S4aA3S1S0SdS6dS2cPdA2S47S48A1A3S1S0S16S71S26S27S2cS31S2dA5S3fA3S1S0G3S21S3fS4cA2M5S9S16S58G5A1M6A2A3S1S0S16S59G6A1S3eA3S1S0S3S18S3eA1S4A3S1S0G1S55S4eA1S2G0S6S1bS1dS60S1eA4S2G0S6S1bS1dS68S1eA4G2A3A3A3S1S0S3S6bS10S12S14S11S6cS37SeZ0A1A3A1A1S57S33A1A3S4A3S1S0S16S74S33S37S49A3S34A3S1S0S3S13S17S34A1A1S4A3S1S0SdS1aS33A1SeS76A1A3S1S0G1S55S56S34A1A1S2G0S6S1bS1dS5fS1eA4G2A3A3S1S0S3S19S3cS28S43A3S4A3S0S3S6eS43S1fA2S4A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition K_fa : axst := Eval vm_compute in
  upd_obj_at (dropV [266; 285; 286; 287; 288; 289; 290; 331; 332; 333; 334; 335]%positive (junkRN [1; 18; 20; 22; 23; 27]%nat X_fa1)) 1 (drop_cells_obj [56]).
Definition s_fa0 : wsub := ltac2:(tb__ "0|0|
S6aS1fS17S35A1S17S2aA1A3").
Definition s_fa1 : wsub := ltac2:(tb__ "0|0|
S6aS1fS17S36A1S17S2aA1A3").
Definition E_fa0 : axst := Eval vm_compute in leafF (runF K_fa) free_pc 0.
Definition xf_fa : list axform := [AXSplit 3 (SLit (-16))].
Definition E_fa1 : axst := Eval vm_compute in optL (apply_axforms E_fa0 xf_fa).
Definition E_fa : axst := Eval vm_compute in dropX pAR E_fa1.
Definition s_fa : wsub := s_free E_fa (SLit 64).
Definition R_fa : list sobj := Eval vm_compute in optR (entails_frA E_fa Pre_fr s_fa).
Definition T_fa0 : axst := Eval vm_compute in T_afterA Pre_fr E_fa s_fa R_fa L_fr.
Definition xfb_fa : list axform := ltac2:(tb__ "0|1|
S2S20S23S2S5U0S2S5U4S2S5U5S2S5U6S2S5U1S2S5U7S2S5U8S2S5U9S2S5UaS2S5UbS2S5U2S2S5U3M0S7S5A1A3A3A3A3A3A3A3A3A3A3A3A3A1S2S20S22G0A1S7S20A1A3A3").
Definition T_fa : axst := Eval vm_compute in ax_tidy (optL (apply_axforms T_fa0 xfb_fa)).
Definition L_sxK : axst := Eval vm_compute in leafF (runF T_fa) pc_sx 0.

Lemma fz_checks_fa : ltac2:(tb__ "0|9|
S1S0S3S18S2aA1S4A3S1S0S3S19S35S2aS44A3S4A3S1S0S3S19S36S2aS45A3S4A3S1S0S3S6eS44S1fA2S4A3S1S0S3S6eS45S1fA2S4A3S1S0S3S6bS10S12S11S6cS5bSeZ0A1M0A3A1S57S35A1A3S4A3S1S0S3S6bS10S12S11S6cS37G0A3A1S57S36A1A3S4A3S1S0SaS8S1bS1dA2M1A1M2S55S56S2aA1A1S2G1S6S1bS1dS5cS1eA4S7G1A1M3A3A3S1S0SbS16A1M4S21S4dS53A2S9S16S38A2A3S1S0S16S5aS5eS38A2S29A3S1S0S3S18S29A1S4A3S1S0SbSaS15A1M5A1S6fS29S26S2bA3S9G5S30A2A3S1S0S3S70S29S26S2bS30S2S16S2dS7S16A1A3A5S4A3S1S0S3S72S1fS2bA2S4A3S1S0S3S78S1fS5dS29A1A2S4A3S1S0SdS6dS2bPcA2S5eA3S1S0SdS6dS2bPdA2SeZ40A1A3S1S0S16S71S26S29S2bS30S2dA5S3dA3S1S0G4S21S3dS54A2M6S9S16S58G6A1M7A2A3S1S0S16S59G7A1S2fA3S1S0S3S18S2fA1S4A3S1S0SaS8S8SdSdA2SdA2M8A1S69S2fA1ScG8S63S64A3A3S0G2S55S56S2fA1A1S2G1S6S1bS1dS61S1eA4G3A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
End Lib_fuzz_one_ad.

(* [comment removed for export] *)
Module Lib_load_obj_exitsR.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "holds"; "SPUle"; "rw"; "SLit"; "SVar"; "rm"; "ss_facts"; "SAlu"; "sprop_below"; "sprop_eqb"; "ss_next"; "swf"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "prod"; "list"; "pair"; "fst"; "option"; "snd"; "@Corelib.Init.Logic"; "eq"; "and"; "True"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_exitsR"; "ldefR"; "rate2"; "K_after0R"; "V_ldR"; "fact_nv"; "PhisS"; "fact_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "ldef"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "vLEN"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits"; "K_after0"; "X_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pNX"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "leaf_matchesA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "phi_reads"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition vNV : sv := SVar 401.
Definition fact_nv : sprop := SPUle vNV pNX.
Definition fact_nt : sprop := SPUle (SVar 410) pNX.
Definition rate2 : list sprop := ltac2:(tb__ "0|0|
S10S3S22S10S3S24S12S3A1A3A3").
Definition K_after0R : axst := ax_add_facts rate2 K_after0.

Definition ldefR (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S1bS25Vrho;A1S1dS3S4Vrho;A1S1fA3A2").
Definition V_ldR : list positive := ltac2:(tb__ "0|0|
S10S0P1d2S10S0P1d4S10S0P191S10S0P19aS10S0P1eaS12S0A1A3A3A3A3A3").
Definition PhisS : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|4|
S10S14S15S0A1M0S2OFrho;M1A2S16G0G1S21S1eA4S10S14G0S2OF_;M2A2M3S16G0G2S12S0A1S2S1cL_;A4S12G3A1A3A3").

Lemma ldefR_ldef : ltac2:(tb__ "0|0|
S2S1eR1A1S25R2A1F_;Frho;"). Proof. intros rho [H _]. exact H. Qed.
Lemma ldefR_rate : ltac2:(tb__ "0|0|
S2S1eR1A1S1dS3S4R2A1S1fA3F_;Frho;"). Proof. intros rho [_ H]. exact H. Qed.
Lemma ldefR_nv : ltac2:(tb__ "0|0|
S2S1eR1A1S4R2S22A2F_;Frho;"). Proof. intros rho [_ H]. exact (Forall_inv H). Qed.
Lemma ldefR_intro : ltac2:(tb__ "0|0|
S2S25R1A1S1dS3S4R2A1S1fA3S1eR3A1F_;F_;Frho;"). Proof. intros rho H1 H2. split; assumption. Qed.

Lemma rate2_keep : ltac2:(tb__ "0|1|
S2S2S0S30S0R1S21A3S1aS29Q40A1S6R4R2A2S6R3R2A2A3F_;Fv;S1dS3S4R3A1S1fA3M0G0F_;F_;Frho';Frho;").
Proof.
  intros rho rho' HV H.
  assert (E1 : rw rho 401 = rw rho' 401) by (apply HV; cbn; tauto). assert (E3 : rw rho 410 = rw rho' 410) by (apply HV; cbn; tauto).
  assert (E5 : rw rho 490 = rw rho' 490) by (apply HV; cbn; tauto).
  unfold rate2, fact_nv, fact_nt, vNV, pNX in *.
  inversion H as [|? ? A1 H1]; subst. inversion H1 as [|? ? A3 _]; subst.
  rewrite h_ule in A1, A3. unfold uval in A1, A3. cbn [eval] in A1, A3.
  repeat constructor; rewrite h_ule; unfold uval; cbn [eval]; rewrite <- ?E1, <- ?E3, <- ?E5; assumption.
Qed.
Lemma ldefR_reads : phi_reads V_ldR ldefR.
Proof.
  intros rho rho' HV _ HM [HD HN]. split; [|exact (rate2_keep rho rho' HV HN)].
  intros z Hz. rewrite <- HM. apply HD.
  rewrite <- (uval_rw rho rho' 466 xLD eq_refl ltac:(apply HV; cbn; tauto)), <- (uval_rw rho rho' 468 xLK eq_refl ltac:(apply HV; cbn; tauto)). exact Hz.
Qed.
Lemma PhisS_reads : ltac2:(tb__ "0|3|
S1dS14S15S0A1M0S2OF_;M1A2M2G2S39S17G0G1R1A3S19G0G1R1A3A2Lp;S23A3").
Proof. constructor; [exact ldefR_reads | constructor; [intros rho rho' _ _ _ _; exact I | constructor]]. Qed.

Lemma ldefR_keep : ltac2:(tb__ "0|4|
S2S2S0S30S0R1S21A3S1aS29Q40M0A1S6R4R2A2S6R3R2A2A3F_;Fv;S1S1bS3bS2fR4S35A2M1R1A2S3cR1S3aG1S3dZ10S2fR4S36A2A2A2A2A2S1aS18S29Q8A1A1S9R4S2aG0R2A2M2A2S9R5G2A2A3F_;Fz;S1eR4A1M3G3F_;F_;F_;Frho';Frho;").
Proof.
  intros rho rho' HV HM [HD HN]. split; [|exact (rate2_keep rho rho' HV HN)].
  intros z Hz.
  rewrite (uval_rw rho rho' 466 xLD eq_refl ltac:(apply HV; cbn; tauto)), (uval_rw rho rho' 468 xLK eq_refl ltac:(apply HV; cbn; tauto)) in Hz.
  rewrite (HM z Hz). exact (HD z Hz).
Qed.

Lemma rate2_bounds : ltac2:(tb__ "0|1|
S2S1dS3S4R1A1S1fA3S4R2S5S34SbS33S2bS7Z1A1A3A2A2S4R3S5S2bS7Z4000000A1A2A2S1bS4R4S5S8P191A1S7ZffffffffA1M0A2A2S4R4S5S8P19aA1G0A2A2A2F_;F_;F_;Frho;").
Proof.
  intros rho H HN HL. unfold rate2, fact_nv, fact_nt, vNV in H.
  inversion H as [|? ? A1 H1]; subst. inversion H1 as [|? ? A3 _]; subst.
  rewrite h_ule in A1, A3, HN, HL. rewrite uval_lit in HL by lia.
  pose proof (uval_range rho pNX) as RN. pose proof (uval_range rho vLEN) as RL.
  assert (E1 : uval rho (SAlu ALU_ADD vLEN (SLit 1)) = uval rho vLEN + 1) by (rewrite uval_add_small; rewrite uval_lit by lia; lia).
  split; rewrite h_ule, uval_lit by lia; lia.
Qed.

Lemma exitsR_checks : ltac2:(tb__ "0|2|
S1bS1aS11S37S2cS2eS10S26S20S12S26A1A3A3S13A3S1bS1aS11S28S20A1S13A3S1bS1aS11SfS27S20A1M0A1S13A3S1bS1aS26S38S20SaS27S2dA1A1M1A2S2dA3S1bS1aS11S31S3ScSeG0A1A1G1A3S13A3S1aS11S31S3S3S32S3SdR1A1SaG0A1A3Lf;S1fA3S13A3A2A2A2A2A2").
Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_load_obj_exitsR.

(* [comment removed for export] *)
Module Lib_load_obj_loopE.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "pair"; "list"; "prod"; "nil"; "nat"; "app"; "false"; "andb"; "negb"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "leafA"; "ax_setS"; "axwf"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "s_E"; "X_latchE2"; "K_loopE2"; "X_bodyE2"; "ndE0"; "K_afterE2"; "X_latchE2A"; "X_errxE2"; "XlE_objs"; "upd_cell_at"; "PhisE"; "avt_cnt_cell"; "cnt_vars"; "cutsE2"; "exitsE2"; "jAVT"; "jTS"; "keepsE"; "relax_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_facts"; "sv"; "sobj"; "SLit"; "cell"; "sv_eqb"; "sprop"; "SAlu"; "holds"; "mkObj"; "ob_base"; "rw"; "ss_next"; "ss_objs"; "ss_pc"; "c_off"; "c_width"; "mkCell"; "mkSS"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "sstate"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "HNEXT"; "pI"; "X_latchE"; "cps_loop"; "xLC"; "xLK"; "K_loopE"; "O_ent"; "pLNL"; "pPOS"; "xLD"; "bA"; "entA"; "pH"; "t_c"; "v_avt"; "vsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "NDA"; "nd_below"; "am_eqb"; "am_subst"; "AHead"; "JA"; "amode"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "tvL"; "s_loop"; "frL"; "tblB"; "tblL"; "LA"; "P0_lo"; "V_B"; "V_L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_le2"; "ejcertAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits"; "K_afterE"; "X_bodyE"; "X_errxE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndLE"; "z0"; "LAX"; "LAXK"; "RL"; "VLA"; "ndXE"; "LAK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "runL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "leaf_matchesA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "eqb"; "leb"; "lt"; "@Corelib.Init.Nat"; "add"; "mul"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop.LOLAddr"; "pc_after"; "pc_body"; "pc_errx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sprop_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "drop_lastA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Stdlib.Lists.List"; "existsb"; "filter"; "forallb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition jAVT : sv := SVar 532.
Definition jTS : sv := SVar 533.
Definition avt_cnt_cell : sv := ltac2:(tb__ "0|0|
S36S99S5bS5cS5dA1A1S32Z1A1A3").

Definition upd_cell_at (off : Z) (v : sv) (c : cell) : cell := ltac2:(tb__ "0|1|
S1S33L_;S34S3eVc;A1M0S32Voff;A1A2S40G0S3fVc;A1Vv;A3Vc;X1x2").
Definition relax_obj (o : sobj) : sobj := ltac2:(tb__ "0|8|
S1S31L_;M0S1S1L_;M1S34S39Vo;A1M2S58A2M3S34S45Vo;A1M4S32Zd8A1A2S9X1x2S38G2G4S44Vo;A1M5S5fS33S33S21Ze0S27A2S42Vo;A1M6A4S43Vo;A1M7A5G0G1G3S34G4S32Z330A1A2S9X1x2S38G2G4G5S5fS33S33S21Z338S28A2G6A4G7A5Vo;X1x2X1x2").

Definition cnt_vars : list positive := ltac2:(tb__ "0|0|
S8S17S5fS7S17S7S91S95U191S96U3R1A2A2A1Li;S61U0U12A2A4S5fS7S17S91S61U244UbA2A4A3").
Definition keepsE (f : sprop) : bool := ltac2:(tb__ "0|0|
S9dS17SbSa2S17S92R1A1S24A3A1Lw;Vf;A2").
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
ScSdS1Sa4SfSfSaS4cS10R1A1M0A1S14R1A1A2LA;S0SfS19S0SfS1aS0SfS1bS0SfS1dS0SfS1fS6SfA1M1A3M2A3A3A3A3A3S2A3ScSdS4S16A1S5fS12S16S12S3dS10S15R1A1M3A1A1M4LL;S8dU96M5S50S1aA3M6A4S0S16S9bS0S16S9aS6S16A1A3A3A3ScSdS4S1A1S5fS12S1S12S8eS68G3S0SfS1bS0SfS1dG1A3A3A3LL;G6A4S0S1S2S0S1S2S6S1A1A3A3A3ScSdS4S5S16S1A2M7A1S5fS12G7S12S3S16S1G4S8eS68G3G2A3A4LL;S8dG5S50S1bA3A4S0G7S3S16S1S9cS2A4S6G7A1A3A3ScSdS1S11S4fS19S18A3S2A3ScSdS1S11S53S1aS18A3S2A3ScSdS1S11S7fS1bS18A3S2A3ScSdS1S11S7eS1dS18A3S2A3ScSdS1S11S80S1fS18A3S2A3ScSdS1S83S18S68A2S2A3ScSdS1S9eS18S73S73A3S2A3ScSdS4S31A1S3cS10S19A1A1S8S31S20S0S31S54S4eS56S55A3S6S31A1A3A3A3ScSdSfS9fS19S20A2S1eA3ScSdS1S11S1eS1aS74A3S2A3ScSdS1S7cS2fS10S1eA1A1S2dS74S6S2cA1M8A2S0S2cS86Z0M9A1S0S2cS87G9A1G8A3A3A3S2A3SdS4S17A1S5fSfS17SfS3bG0A1LA;S0SfS4fS0SfS53S0SfS7fS0SfS7eS0SfS80S0SfS19S0SfS1eG1A3A3A3A3A3A3A3A4S0S17S4dS0S17S4dS0S17S4dS0S17S4dS0S17S4dS0S17S4dS0S17S4dS6S17A1A3A3A3A3A3A3A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition ndE0 : ndesc := ndL [].
Definition PhisE : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|3|
S0S5S4S17A1M0S2eOFrho;M1A2M2S3G0G1S7bS77A4S0G2S3G0G1S7aS76A4S6G2A1A3A3").
Definition cutsE2 : list efnode := ltac2:(tb__ "0|5|
S0S5S5S5SfS6aA2M0S7A2M1S5S16S30A2M2A2M3S3G1G2S3G0S7S3SfS6aS1aS1cA4U0M4A4S3S16S30S88S89Z1aS85A2A4A4S0G3S3G1G2S3G0S7S3SfS6aS1bS1cA4G4A4S3S16S30S88S89Z19S85A2A4A4S6G3A1A3A3").
Definition exitsE2 : list efnode := ltac2:(tb__ "0|6|
S0S5S5S5SfS6aA2M0S7A2M1S5S16S30A2M2A2M3S3G1G2S3G0S7S3SfS6aS1dS1cA4U0M4A4S3S16S30Z190S85A4M5A4S0G3S3G1G2S3G0S7S3SfS6aS1fS1cA4G4A4G5A4S6G3A1A3A3").
Lemma ecertE2_ok : ltac2:(tb__ "0|0|
SdS1S7dS5eS68S22U96S50S68S25S26A8S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma ent_addrE : ltac2:(tb__ "0|7|
S2eS60S35S37R1A1S2fS10S19A1A1A3ScSdS16S2bR2S59S4eA1A2S64S2bR2S57A2M0S66Z10M1S2bR2S4eA2M2A2A2A3ScS65G2S2bR2S51A2M3A2ScS63G3S2bR2S52A2M4A2ScS63S66G1G4A2M5ZffffffffA2ScS63G0S67Z2M6Z2fA2A2ScSdS16S2bR2S8cG1S52A2A2G5A3S63S2bR2S69A2S67G6Z1aA2A2A2A2A2A2A2A2F_;Fr;").
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
S2eS60S35S37R1A1S2fS10S19A1A1A3ScS63S2bR2S57A2M0S2bR2S39S54S4eS56S55A3A1A2M1A2S63S64G1Z10M2A2S64G0S2bR2S8cG2S52A2A2A2A2A2F_;Fr;").
Proof.
  intros r HF. cbn [ob_base O_ent]. destruct (ent_addrE r HF) as (E1 & H1 & H2 & H3 & H4 & EK & _). pose proof (uval_range r pI). rewrite E1, EK. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sa1S2eS4S72Q40A1A1S97OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sa0S5eVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S16S90VCST;R1A2ScS63Z0R2A2S65R2S8fA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S16S90VXGL;R1A2ScS63Z0R2A2S65R2S8fA2A2F_;Fa;").
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
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S2eOFr;") := ltac2:(tb__ "0|0|
S79VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S70VAInv;VCST;VXGL;S68VKc;Vrho0;VP0;VFB;VFF;VBX;VPA;Vnd;Ac").

Lemma loopE_checks2 : ltac2:(tb__ "0|6|
ScSdS1S7cS2fS10S4fA1A1S2dS18S0S2cS86Z0M0A1S0S2cS87G0A1S6S2cA1M1A3A3M2A2G2A3S2A3ScSdS1S7cS2fS10S7fA1A1S2dS18G1A2M3S0S2cS78G0A1S0S2cS8bG0A1G1A3A3M4A3S2A3ScSdS1S7cS2fS10S7eA1A1G3G4A3S2A3ScSdS1S6dS6eS18S6fS5aS2A2M5A2G5A2S2A3ScSdS1S6cS4dS8aA2S2A3ScSdS1S6cS4dS84A2S2A3SdS1S93S68S4dA2S2A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma relax_latchE : ltac2:(tb__ "0|1|
S2eS4S72Q40A1A1S81S62S5eVJAv;S8aA1M0S4fR3R2R1A6S62S5eG0S19S82R4S18A2R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w HS. pose proof loopE_checks as (_ & _ & _ & _ & C1 & _ & _ & _ & _ & Cid & Ctv & _). pose proof loopE_checks2 as (B1 & _ & _ & Bam & BnX & _ & Bnp).
  exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc X_latchE X_latchE2 s_E ndXE ndXE rho tp w C1 Cid Bnp BnX Ctv eq_refl B1 Bam HS).
Qed.

Lemma relax_bodyE : ltac2:(tb__ "0|0|
S2eS4S72Q40A1A1S81S62S5eVJAv;S84A1S7fR3R2R1A6S62S5eVJAv;S1cA1S1bS82R4S18A2R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w HS. pose proof loopE_checks as (_ & _ & _ & _ & _ & _ & C3 & _ & _ & Cid & Ctv & _). pose proof loopE_checks2 as (_ & B2 & _ & Bam & _ & BnL & Bnp).
  exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc X_bodyE X_bodyE2 s_E ndLE ndE0 rho tp w C3 Cid Bnp BnL Ctv eq_refl B2 Bam HS).
Qed.
Lemma relax_afterE : ltac2:(tb__ "0|0|
S2eS4S72Q40A1A1S81S62S5eVJAv;S84A1S7eR3R2R1A6S62S5eVJAv;S1cA1S1dS82R4S18A2R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w HS. pose proof loopE_checks as (_ & _ & _ & _ & _ & _ & _ & C4 & _ & Cid & Ctv & _). pose proof loopE_checks2 as (_ & _ & B3 & Bam & _ & BnL & Bnp).
  exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc K_afterE K_afterE2 s_E ndLE ndE0 rho tp w C4 Cid Bnp BnL Ctv eq_refl B3 Bam HS).
Qed.

Lemma s_E_low : ltac2:(tb__ "0|0|
S2eS17S94R1P214A2SdS72Q40A1S3aS82R3S18A2R2A2S3aR3R2A2A3F_;Fv;Frho;").
Proof.
  intros rho v Hv. cbn [rho_sub rw]. unfold s_E. cbn [wsub_get].
  destruct (Pos.eqb_spec v 532) as [->|_]; [lia|]. destruct (Pos.eqb_spec v 533) as [->|_]; [lia|]. reflexivity.
Qed.

Lemma latch_absorbE2 : ltac2:(tb__ "0|1|
S4S2cA1M0G0S71S2eS4S72Q40A1A1S81SdS1S6cS4dS6bS73S75R6R4A4A2S2A3SdS1S7cS2fS10S1eA1A1S2dS74R6A2R7A3S2A3SdS1S6dS6eS74R6A2R6A2S2A3S76R6A1S62S5eVJAv;S6bS73S75RaR8A4A1S19R7R6R5A6SeS2eS2eScS77R1A1ScS62S5eVJAv;S6bS73S75RbRaA4A1S1aR1R8R7A6ScSdS16S2bR1S51A2S2bR9S51A2A3SdS16S2bR1S4eA2S2bR9S36S98S4eS32Z1A1A3A2A3A2A2A2Lrho2;A2F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fam;Fbdj;Fbdi;").
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
End Lib_load_obj_loopE.

(* [comment removed for export] *)
Module Lib_load_obj_avn.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "prod"; "nat"; "nil"; "true"; "length"; "list"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SAlu"; "SMd"; "SPUle"; "sobj"; "ss_objs"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "apply_axforms"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "AHead"; "NDA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "X_latch"; "X_latchE"; "cps_loop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "A1"; "LA"; "V_B"; "V_L"; "tblB"; "tblL"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "h0"; "tv_vn"; "E_vn"; "T_vn_f"; "T_vn_ok"; "bd_vn_ok"; "bdrest_vn"; "brest_vn"; "c_avn"; "d_avn"; "k_avn"; "ndXE_vn"; "ndX_vn"; "nd_vn_f"; "nd_vn_ok"; "tv_vn_f"; "tv_vn_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "RL"; "VLA"; "z0"; "AK1"; "LAK"; "LAX"; "LAXK"; "bdX"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Lib_handle_vn_pf"; "PD_hvn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn.HVN"; "Pre_hvn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "optL"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop.LOLAddr"; "pc_join"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "B_EW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "PDh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "liftPD"; "@Stdlib.Lists.List"; "filter"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "sub"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_vn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_vn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Lib_handle_vn_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.
Module HVN. Include Lib_handle_vn. End HVN.

Definition c_avn : sv := t_c (v_avn vsP).  Definition d_avn : sv := t_d (v_avn vsP).  Definition k_avn : sv := t_k (v_avn vsP).

Definition room_vn : sprop := ltac2:(tb__ "0|0|
SdScS2bSaZ4A1SbS2aS34SaZ3A1A3A3SaS4eA1A2").

Definition xf_vn : list axform := ltac2:(tb__ "0|2|
S0S11S15U7M0SaN80M1A1A2S0S11S12G0G1A2S4S11A1A3A3").
Definition E_vn : axst := Eval vm_compute in ax_add_facts [room_vn] (optL (apply_axforms E_hvn xf_vn)).

Definition h0 : positive := 99%positive.
Definition s_vn : wsub := ltac2:(tb__ "0|1|
S0S2S18S9A2M0S1S18S9S2cS1eA4S0G0S1S18S9P13SbS2aS4bSaZ80A1A3A4S4fPaS1aS2eA1S1aS49A1A3A3A3").
Definition R_vn : list sobj := Eval vm_compute in optR (entails_frA E_vn HVN.Pre_hvn s_vn).

Definition PDk_vn : list pdescK := ltac2:(tb__ "0|0|
S51S50S48S2cS5A3A1").

Definition passed_vn : list (sv * sv) := ltac2:(tb__ "0|1|
S0S2S9S9A2M0S1S9S9S35S47Z4S36A2A4S4G0A1A3").
Definition kept_vn : list (sv * sv) := Eval vm_compute in (firstn 2 tvL ++ skipn 3 tvL).
Definition tv_vn : list (sv * sv) := kept_vn ++ passed_vn.

Definition bdrest_vn : list bitem := Eval vm_compute in (firstn 4 bd_rest ++ skipn 6 bd_rest).
Definition brest_vn : list bitem := ltac2:(tb__ "0|0|
S0S22S25S54S24Z48A2A1S0S22S41S40A1S32A3A3").
Definition hand_vn : list bitem := Eval vm_compute in bd_subst s_vn (HVN.bd_hvn vNC vNK).

Definition bd_vn : list bitem := Eval vm_compute in (firstn 2 (skipn 4 bd_rest) ++ LA A1 :: LAK AK1 :: bdrest_vn).

Definition Xk_vn : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) d_avn)) (ax_X E_vn).

Goal entails_frA E_vn HVN.Pre_hvn s_vn = Some R_vn /\ call_checkPA E_vn HVN.Pre_hvn s_vn R_vn (map (fun d => fst (fst d)) PDk_vn) = true
  /\ call_checkTA NP s_vn = true /\ wsub_dom_below s_vn NF = true
  /\ TobjJV.tv_sub_eqb s_vn passed_vn (nd_tv (ndh h0 true HVN.nd0)) = true
  /\ am_eqb (am_subst s_vn (nd_am (ndh h0 true HVN.nd0))) (AHead pH true) = true
  /\ forallb (fun d => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pd_okA HVN.Pre_hvn NF s_vn (ss_next (ax_S E_vn)) (fst d)) PDk_vn = true
  /\ tv_permb tvL tv_vn = true /\ bd_permb (bdA A1) bd_vn = true
  /\ xrs_inclb Xk_vn (ax_X E_vn) = true
  /\ bd_subst s_vn (nd_bd (ndh h0 true HVN.nd0)) = hand_vn
  /\ bud_pay2 (ss_facts (ax_S E_vn)) (SLit 0) 0 bd_vn (hand_vn ++ brest_vn) = true
  /\ nd_below (ss_next (ax_S E_vn)) (NDA tv_vn frL bd_vn (AHead pH true)) = true /\ bd_below (ss_next (ax_S E_vn)) brest_vn = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_vn_ok0 : axst := Eval vm_compute in T_afterA3 HVN.Pre_hvn E_vn s_vn R_vn HVN.P_ok Xk_vn.
Definition T_vn_f0 : axst := Eval vm_compute in T_afterA3 HVN.Pre_hvn E_vn s_vn R_vn HVN.P_fail Xk_vn.

Definition isub_ok : wsub := Eval vm_compute in import_subA s_vn HVN.Pre_hvn HVN.P_ok E_vn.
Definition isub_f : wsub := Eval vm_compute in import_subA s_vn HVN.Pre_hvn HVN.P_fail E_vn.
Definition tv_vn_ok : list (sv * sv) := Eval vm_compute in (kept_vn ++ import_tv isub_ok (nd_tv HVN.nd_ok)).
Definition bd_vn_ok : list bitem := Eval vm_compute in (bd_subst isub_ok (nd_bd HVN.nd_ok) ++ brest_vn).
Definition tv_vn_f : list (sv * sv) := Eval vm_compute in (kept_vn ++ import_tv isub_f (nd_tv HVN.nd_fail)).
Definition nd_vn_ok : ndesc := ltac2:(tb__ "0|0|
S1dS3cS23S31S1cS1eS5A2A4").
Definition nd_vn_f : ndesc := ltac2:(tb__ "0|0|
S1dS3bS23S33S1cS1eS5A2A4").
Goal am_subst isub_ok (nd_am (ndh h0 true HVN.nd_ok)) = AHead pH true /\ am_subst isub_f (nd_am (ndh h0 true HVN.nd_fail)) = AHead pH true
  /\ bd_subst isub_f (nd_bd HVN.nd_fail) = [] /\ tv_vn_f = tv_vn.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition vn_back (T : axst) : axst := ltac2:(tb__ "0|2|
S4dS4aS16VT;S0S11S12U0M0Z80A2S0S11S14S0S3G0S0S3U3S0S3U1S0S3U2S46U4M1S45S6SeSfS1aVT;A1A1A2G1A2A2A3A3A3A3A1S0S11S13G0A1S4S11A1A3A3A3A2A1A1").
Definition T_vn_ok : axst := Eval vm_compute in vn_back T_vn_ok0.
Definition T_vn_f : axst := Eval vm_compute in vn_back T_vn_f0.

Definition cps_arm : list Z := ltac2:(tb__ "0|0|
S52S17S17S8S53R1S4cA2A1Lp;S21A3").

Definition PhisV : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|3|
S0S2S7S18A1M0S10OFrho;M1A2M2S1G0G1S27S29A4S0G2S1G0G1S26S28A4S4G2A1A3A3").

Definition ndX_vn : ndesc := ltac2:(tb__ "0|0|
S1dS2dS23S44Z0A1S1cS1eS5A2A4").
Definition ndXE_vn : ndesc := ltac2:(tb__ "0|1|
S1dS2dS23S0S22S42Z0M0A1S0S22S43G0A1S4S22A1A3A3S1cS1eS5A2A4").
Definition cutsV : list efnode := ltac2:(tb__ "0|6|
S0S2S2S2S19S1bA2M0S3A2M1S2S17S9A2M2A2M3S1G1G2S1G0S3S1S19S1bS30S3aA4U1M4A4S1S17S9S3dS3eZaS3fA2A4M5A4S0G3S1G1G2S1G0S3S1S19S1bS2fS39A4G4A4G5A4S4G3A1A3A3").
Definition exitsV : list efnode := ltac2:(tb__ "0|6|
S0S2S2S2S19S1bA2M0S3A2M1S2S17S9A2M2A2M3S1G1G2S1G0S3S1S19S1bS1fS38A4U1M4A4S1S17S9S3dS3eZ1S3fA2A4M5A4S0G3S1G1G2S1G0S3S1S19S1bS20S37A4G4A4G5A4S4G3A1A3A3").

End Lib_load_obj_avn.

