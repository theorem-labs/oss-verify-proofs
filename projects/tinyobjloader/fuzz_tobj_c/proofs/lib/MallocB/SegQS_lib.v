(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "valuation"; "rm"; "sprop"; "ss_objs"; "eval"; "holds"; "rw"; "ss_facts"; "swf"; "agree_below"; "rl"; "soff"; "sprop_below"; "ss_next"; "DUnknown"; "cell"; "mkObj"; "@Corelib.Init.Datatypes"; "prod"; "andb"; "list"; "nat"; "pair"; "app"; "bool"; "true"; "length"; "nil"; "cons"; "option"; "false"; "Some"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "of_nat"; "opp"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "in_zone"; "zdisjb"; "zcheck"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue"; "dspec"; "dobj"; "TJ"; "addO"; "with_objs"; "addF"; "keepN"; "dropN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "axst"; "@Stdlib.Lists.List"; "forallb"; "In"; "Forall2"; "combine"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "bview"; "cell_ok"; "mkACell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib"; "s_C"; "s_Cd"; "s_F"; "s_N"; "s_bs"; "s_M"; "s_T"; "s_ZDn"; "s_ZDo"; "s_k"; "uobj"; "ro_cond"; "s_Ca"; "s_CaU"; "s_Cu"; "strans"; "s_Cc"; "s_CcU"; "s_ok"; "s_okU"; "unk_ok"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel"; "FRM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "QW"; "QRD"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "sv_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue"; "notin_vars"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip"; "carve_okq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM"; "entsM"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "cells_inside"; "rd_of"; "wok_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib.ROD"; "ro_cond"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ROD.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation).

Definition ro_cond (rho : valuation) (d : dspec) : Prop := ltac2:(tb__ "0|d|
S18S18S18S18S5S26A2M0S26A2M1S1aS18S18S26S1bA2M2S5A2M3A1M4A2M5S26A2OLd;Vd;G5S26G5OLp;R2G1G4G1OLp0;R2G0S26G0OLp1;R2S5S26S0S1S49Q40M6A1M7SbVrho;R2A2M8S4aG6R7A2A3S0S0S2aZ0M9R7A2S2bR7S2cZ2Z3eA2MaA2A2S0S2aS2eGaA1R1A2S0S2aR1R3A2S0S2aR3GaA2S0S2aG9S29R7R1A2A2S0S7cR1R3R5A3S0S26S0S2aS29R8R2A2R1A2S2bR1S29R8R4A2A2A2MbS0S6dVA0;R2A2S3S0S2aS80R2A2S2bR2S7fA2A2A1A2F_;Fz;S26GbS2S26S26S2S1bS1bS2S5S5S2S26S26S0S44G3S1cG2S5S1cS26S1bR4R3A4R2A4RbA3S0S0S2aS29RdR4A2McR6A2S2bR6S29GcS2dR3A1A2A2A2S0S1G7G8S4aG6R1A2A3S4eS4cS28S8Vrho;A1A2S4fGcR3R1A3A2A2A2A2Lval;A2Le;A2Lk;A2Loff;A2F_;Fz;A2A2A2A2A2A2A2A2Llo;Lb;X18x1Lhi;Lp1;X18x1Lcs;Lp0;X18x1La;Lp;X18x1").

Lemma ro_dissolve : ltac2:(tb__ "0|3|
S42S1aS6A1M0S1aS36A1S73S7S1aS49Q40A1M1A1S1aS70A1M2S6eS6fS26S6cR7R1A2S6cVA0;R2A2F_;Fz;S1G0SaS3eRaA1A1S1dS6R9S34S36S6S37R8A4A3A3S67S28S38RbR7R6S1cG2S65R5S66R4R3A2A4A6S35S36S81R8A1RaA3VK;RaR9R8R7R5A5S6bVA0;Vrho0;RaA3S71RbS34S36S6S37RdA4S72R7RaR8A3A3S7S0S67S28S38S41R10S7bS3eR10A1RfA2A2R1RbS1cG2S65RaS66R9R8A2A4A6S0VK;RdR1RbRaR8A5S0S6bVA0;Vrho0;R1A3S0S27S1G1SdR2R1A2SdRdR1A2A3Fi;S0S27S1S1aS49Q8A1A1S11R2R1A2S11RdR1A2A3Fl;S1S4dS4cS28S8R1A1A2S4cS28S8RcA1A2A3A2A2A2A2A2Trho3;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;FA1;Fds;FBASE;FC;").
Proof.
  intros C BASE ds A1 rho tp tr ms md HQW HOBJ HS HD HK HF rho3.
  pose proof (proj1 (proj1 HS)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)).
  assert (INZ : forall z, dzone ds z -> v3 z = v z /\ v3 z <> None /\ QRD A0 z /\ ~ (SHADOW_BAND_LO <= z < SHADOW_BAND_HI)).
  { intros z Hz. apply List.Exists_exists in Hz as (d & Hd & Hz). pose proof (proj1 (Forall_forall _ _) HD d Hd) as X. destruct d as [[[[b lo] hi] cs] a].
    destruct X as (Eb & A1' & L1 & L2 & L3 & L4 & CI & HQ & HC).
    destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) BASE (map dobj ds) b lo hi cs Hsm HOBJ (in_map dobj ds _ Hd) ltac:(lia) ltac:(lia) ltac:(lia) CI
                ltac:(rewrite Eb, u64_lit by lia; lia) ltac:(rewrite Eb, u64_lit by lia; lia)) as [AVc PRc].
    fold rho3 in AVc, PRc. rewrite Eb, u64_lit in AVc, PRc by lia.
    destruct (HC z Hz) as (off & k & e & val & Hin & Hzc & Ee & Cv).
    pose proof (av_cell (view segsA (rm rho3)) a off k e val rho (fun j Hj => AVc off k e j Hin Hj) Ee) as C3.
    split; [exact (cell_ok_same v v3 _ Cv C3 z ltac:(cbn [c_addr c_w]; lia))|]. split; [|exact (HQ z Hz)].
    destruct (PRc z Hz) as [x Hx]. unfold v3. rewrite Hx. discriminate. }
  assert (INRG : forall x, in_ranges rho (map dobj ds) x -> dzone ds (bv_unsigned x)).
  { intros x (o & Ho & Hz). apply in_map_iff in Ho as (d & <- & Hd). pose proof (proj1 (Forall_forall _ _) HD d Hd) as X. apply List.Exists_exists. exists d. split; [exact Hd|].
    destruct d as [[[[b lo] hi] cs] a]. destruct X as (Eb & A1' & L1 & L2 & L3 & _). rewrite (dobj_range rho b lo hi cs a Eb A1' L1 L2 L3) in Hz. cbn [fst snd] in Hz. exact Hz. }
  destruct (absorb_out rho (map dobj ds) (vms md tp ms) (dzone ds) INRG) as [FR FRrm]. fold rho3 in FR, FRrm.
  assert (EV : v3 = v).
  { apply functional_extensionality. intros z. destruct (dzone_dec ds z) as [Hz|Nz]; [exact (proj1 (INZ z Hz)) | exact (FR z Nz)]. }
  destruct (K_FRM_absorb2 K HL A0 rho0 A1 HQW rho rho3 tp tr md (dzone ds) (dzone_dec ds) ltac:(intros i; reflexivity) ltac:(intros l; reflexivity)) as [HK3 HF3]; try assumption.
  { intros z Hz. destruct (INZ z Hz) as (E1 & _ & Q1 & B1). split; [exact B1|]. right. split; [exact Q1 | exact E1]. }
  { intros z Hz. exact (proj1 (proj2 (INZ z Hz))). }
  pose proof (SPA_unobj segsA TJ rho C BASE (map dobj ds) tp tr ms md HOBJ HS (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU.
  split; [exact HU|]. split; [exact HK3|]. split; [exact HF3|]. split; [intros i; reflexivity|]. split; [intros l; reflexivity | exact EV].
Qed.
End ROD.

Record strans : Type := mkST { s_C : axst; s_k : nat; s_N : list carve_spec; s_bs : list positive; s_F : list sprop; s_T : axst; s_M : vmap;
                               s_ZDo : list zdesc; s_ZDn : list zdesc }.
Definition s_Cd (t : strans) : axst := ltac2:(tb__ "0|0|
S3dS50Vt;A1S59Vt;A1A2").
Definition s_Ca (t : strans) : axst := ltac2:(tb__ "0|0|
S39S51Vt;A1S34S47S6S48S53Vt;A1A4A2").
Definition s_Cc (t : strans) : axst := ltac2:(tb__ "0|0|
S3bS5cVt;A1S52Vt;A1A2").
Definition s_ok (t : strans) : bool := ltac2:(tb__ "0|8|
S19S19S19S19S19S19S19S19S1aS18S5S5A2M0A1M1S1eLx;S3fS50Vt;A1A1S1fG0G1S24Ll;Lp;X1ax2S74S76S54Vt;A1M2A1M3S3eS51Vt;A1M4A1M5A2A2S75G3S40G4A1A2A2S43S27S27S7aS6aR1A2Lv;G2A3A2SfS3aG5S34S47S6S48S53Vt;A1A4A2A1A2S43S9S13S14S3eS5cVt;A1A1M6A1A1S1dS9SeG6A1S52Vt;A1A3A3A2S79S60Vt;A1S56Vt;A1S55Vt;A1A3A2S33S57Vt;A1M7A1A2S43S30S30S43S30S32R1A1S58Vt;A1A3Ld;G7A3A2").

Section SStep.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation).
Variables (zb zlo zhi : nat -> Z) (ZU : list nat).
Hypothesis Hsep : ltac2:(tb__ "0|3|
S1bS1bS44S1bR2VZU;A3M0G0S3S1S1bR4R3A3A1S4S2aS29Vzb;R5A1M1Vzhi;R5A1A2S29Vzb;R4A1M2Vzlo;R4A1A2A2S2aS29G2Vzhi;R4A1A2S29G1Vzlo;R5A1A2A2A2F_;F_;F_;Fz';Fz;").

Lemma s_step : ltac2:(tb__ "0|9|
S5fS68S1aS36A1S1aS49Q40A1M0A1M1S73S7G1S1aS70A1M2S6eS6fS1S1eS62RaA1S1fA3S69S28S6aRaA3S26S6cR9R1A2S6cVA0;R2A2F_;Fz;S1S1aS6A1SaS3eS50RdA1M3A1A1S1dS6S3cG3S59RdA1A2S34S36S6S37RbA4A3A3S1S1bS20G0RbA2S20S27S54ReA1A2A3S67S28S38S50RfA1RaR9S1cG2S65R8S66R7R6A2A4A6VK;RcRbRaR9R7A5S6bVA0;Vrho0;RcA3S35S36S5bVA0;RdA2R10A3S71ReS34S36S6S37R11A4S72RaRdRbA3A3S7S77R1S46S27G0S54R14A1R11A4A2S7VK;R11R2RfReRcA5S6bVA0;Vrho0;R3A3S1S4dS4cS28S8R4A1M4A2S4cS28S8R12A1A2A3M5S0R17R5R12R11RfA4S0S35S47S78R4A1S53R18A1M6A3S0S45S6S30S31R4Vzb;Vzlo;Vzhi;VZU;A5M7S34S47S6S48G6A4S57R18A1A5S0S45S6S30G7SaS3eS51R18A1A1M8A1S58R18A1A5S35S9ScR4A1SeG8A1A3S35S9ScR5A1S52R19A1A3F_;A2A2A2A2F_;F_;F_;S2S7S7S0S67S28R16S56R17A1R1R11S1cG2S65R10S66RfReA2A4A6S0S27S5S44S18S27S5A2S1cS27S5R2R1A4S55R19A1A3S1G0SdR4R3A2SbR6R2A2A3F_;Fe;Fv;S0S1G0S23S49Q8A1A1F_;S8R1A1G4A3S0S10S6aR3R1A3G5A2A2A2A2Lrho5;A2F_;Trho4;Trho3;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;FA1;Fvals;FdsD;FJ';Ft;").
Proof.
  intros t J' dsD vals A1 rho tp tr ms md HOK HST HQW HOBJ HLEN HS HK HF HDC rho3 rho4 HCONT.
  unfold s_ok in HOK. repeat (apply andb_prop in HOK as [HOK ?]).
  match goal with H : forallb (fun d => forallb _ _) _ = true |- _ => rename H into OKZX end.
  match goal with H : zcheck _ = true |- _ => rename H into OKZC end.
  match goal with H : entsM _ _ _ = true |- _ => rename H into OKENT end.
  match goal with H : forallb (sprop_below _) _ = true |- _ => rename H into OKBEL end.
  match goal with H : swf _ = true |- _ => rename H into OKSWF end.
  match goal with H : forallb _ (s_bs t) = true |- _ => rename H into OKBS end.
  match goal with H : sv_vars_all _ _ = true |- _ => rename H into OKV2 end.
  match goal with H : state_vars_all _ _ = true |- _ => rename H into OKV1 end.
  assert (HX : ax_X (s_C t) = []) by (destruct (ax_X (s_C t)); [reflexivity | discriminate HOK]).
  destruct (ro_dissolve K HL A0 rho0 (s_C t) (keepN (s_C t) (s_k t)) dsD A1 rho tp tr ms md HQW HOBJ HS HDC HK HF) as (HU & HK3 & HF3 & RW3 & RL3 & EV).
  fold rho3 in HU, HK3, HF3, RW3, RL3, EV.
  destruct (HCONT HK3 HF3 EV) as (HJ' & CC & ZN & ZO & HFN).
  assert (H1 : SPA segsA J' (s_Cd t) rho3 tp (tr, mkCfg ms md)) by (split; [exact (proj1 HU) | exact HJ']).
  assert (MF : map fst (combine (s_bs t) vals) = s_bs t).
  { clear - HLEN. revert vals HLEN. induction (s_bs t) as [|b r IH]; intros vals HLEN; destruct vals as [|x vs]; cbn in *; try reflexivity; try discriminate. f_equal. apply IH. lia. }
  assert (H2 : SPA segsA J' (s_Cd t) rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_bindV segsA _ NPRE (s_Cd t) rho3 tp _ _ HX HST); [| rewrite MF; exact OKV1 | rewrite MF; exact OKV2 | exact H1].
    intros v Hv. rewrite MF in Hv. pose proof (proj1 (forallb_forall _ _) OKBS v Hv) as X. apply Pos.leb_le. exact X. }
  pose proof (SPA_facts_hold segsA _ rho4 (s_Cd t) tp _ H2) as HFa.
  assert (H3 : SPA segsA J' (s_Ca t) rho4 tp (tr, mkCfg ms md)).
  { pose proof (SPA_carve_list segsA J' rho4 (s_Cd t) tp _ (s_N t) (ss_next (ax_S (s_Cd t))) H2) as Y. cbn zeta in Y. apply Y; clear Y.
    - exact OKSWF.
    - apply Pos.le_refl.
    - apply carve_okq_list; [exact HX | exact CC].
    - exact (zones_cross rho4 zb zlo zhi ZU Hsep _ _ _ _ ZN ZO OKZX).
    - exact (zones_pd rho4 zb zlo zhi ZU Hsep _ _ ZN OKZC). }
  assert (H4 : SPA segsA J' (s_Cc t) rho4 tp (tr, mkCfg ms md)).
  { unfold s_Cc, addF. apply SPA_refacts; [exact H3 | exact OKBEL |]. intros HF4. apply Forall_app. split; [exact HF4 | apply HFN; exact HFa]. }
  destruct (entM_SPA J' _ (s_T t) (s_M t) rho4 tp _ OKENT HST H4) as (H5 & AG5 & V5 & RM5).
  eexists. split; [exact H5|]. split; [exact V5|]. split; [|split; [exact AG5 | exact EV]]. rewrite RM5. unfold rho4. apply rm_rho_sets.
Qed.
End SStep.

Definition uobj (u : sv * sv * sv) : sobj := ltac2:(tb__ "0|1|
S18S18S5S5A2M0S5A2S6Lu;Vu;G0S5G0S6Lp;R2S5S5S17R2R1R3S21S16A1S15A5Lulo;Lub;X18x1Luhi;Lp;X18x1").
Definition s_Cu (t : strans) (u : sv * sv * sv) : axst := ltac2:(tb__ "0|0|
S39S51Vt;A1S22S6S5aVu;A1S21S6A1A3A2").
Definition s_CaU (t : strans) (u : sv * sv * sv) : axst := ltac2:(tb__ "0|0|
S39S5eVt;Vu;A2S34S47S6S48S53Vt;A1A4A2").
Definition s_CcU (t : strans) (u : sv * sv * sv) : axst := ltac2:(tb__ "0|0|
S3bS5dVt;Vu;A2S52Vt;A1A2").
Definition s_okU (t : strans) (u : sv * sv * sv) (zdu : zdesc) : bool := ltac2:(tb__ "0|9|
S19S19S19S19S19S19S19S19S19S19S1aS18S5S5A2M0A1M1S1eLx;S3fS50Vt;A1A1S1fG0G1S24Ll;Lp;X1ax2S74S76S54Vt;A1M2A1M3S3eS51Vt;A1M4A1M5A2A2S75G3S40G4A1A2A2S43S27S27S7aS6aR1A2Lv;G2A3A2SfS3aG5S22S6S5aVu;A1S21S6A1A3A2A1A2SfS3aS3eS5eVt;Vu;A2A1S34S47S6S48S53Vt;A1A4A2A1A2S43S9S13S14S3eS5dVt;Vu;A2A1M6A1A1S1dS9SeG6A1S52Vt;A1A3A3A2S79S61Vt;Vu;A2S56Vt;A1S55Vt;A1A3A2S33S57Vt;A1M7A1A2S43S30S30S43S30S32R1A1S1dS30S58Vt;A1M8S22S30Vzdu;S21S30A1A3A3A3Ld;G7A3A2S43S30S32Vzdu;A1G8A3A2").
Definition unk_ok (rho : valuation) (u : sv * sv * sv) : Prop := ltac2:(tb__ "0|5|
S18S18S5S5A2M0S5A2OLu;Vu;G0S5G0OLp;R2S5S5S4bQ40M1SbVrho;R2A2A2S26S12Vrho;R2A2S26S12Vrho;R5A2S26S0S2aR2R1A2S0S2bS2fR1R2A2S2cZ2M2Z3fA2A2S0S2aZ0S29R3R2A2A2S0S2aS29R3R1A2S2cG2Z40A2A2S26S0S2aS29R4R3A2R1A2S2bR1S29R4R2A2A2A2S0S1S1eS7eS28S8Vrho;A1M3S4aG1R2A2A3S1fA3S2S49Q8A1M4G4S1S23G4A1S7dS28G3S4aG1R3A2A3S25G4R1A2A3Ly;A2A2F_;Fx;A2A2A2A2Thi;Tlo;Tb;Lulo;Lub;X18x1Luhi;Lp;X18x1").

Section SStepU.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation).
Variables (zb zlo zhi : nat -> Z) (ZU : list nat).
Hypothesis Hsep : ltac2:(tb__ "0|3|
S1bS1bS44S1bR2VZU;A3M0G0S3S1S1bR4R3A3A1S4S2aS29Vzb;R5A1M1Vzhi;R5A1A2S29Vzb;R4A1M2Vzlo;R4A1A2A2S2aS29G2Vzhi;R4A1A2S29G1Vzlo;R5A1A2A2A2F_;F_;F_;Fz';Fz;").

Lemma s_stepU : ltac2:(tb__ "0|9|
S5fS18S18S5S5A2S5A2S30S68S1aS36A1S1aS49Q40A1M0A1M1S73S7G1S1aS70A1M2S6eS6fS1S1eS63RcRbRaA3S1fA3S69S28S6aRaA3S26S6cR9R1A2S6cVA0;R2A2F_;Fz;S1S1aS6A1SaS3eS50RfA1M3A1A1S1dS6S3cG3S59RfA1A2S34S36S6S37RbA4A3A3S1S1bS20G0RbA2S20S27S54R10A1A2A3S67S28S38S50R11A1RaR9S1cG2S65R8S66R7R6A2A4A6VK;RcRbRaR9R7A5S6bVA0;Vrho0;RcA3S35S36S5bVA0;RdA2R10A3S71ReS34S36S6S37R11A4S72RaRdRbA3A3S7S77R1S46S27G0S54R16A1R11A4A2S7VK;R11R2RfReRcA5S6bVA0;Vrho0;R3A3S1S4dS4cS28S8R4A1M4A2S4cS28S8R12A1A2A3M5S0R17R5R12R11RfA4S0S64R4R19A2S0S35S47S78R4A1S53R1aA1M6A3S0S31R4Vzb;Vzlo;Vzhi;VZU;S5aR19A1R18A7S0S45S6S30S31R4Vzb;Vzlo;Vzhi;VZU;A5M7S34S47S6S48G6A4S57R1aA1A5S0S45S6S30G7SaS3eS51R1aA1A1M8A1S58R1aA1A5S35S9ScR4A1SeG8A1A3S35S9ScR5A1S52R1bA1A3F_;A2A2A2A2A2A2F_;F_;F_;S2S7S7S0S67S28R16S56R19A1R1R11S1cG2S65R10S66RfReA2A4A6S0S27S5S44S18S27S5A2S1cS27S5R2R1A4S55R1bA1A3S1G0SdR4R3A2SbR6R2A2A3F_;Fe;Fv;S0S1G0S23S49Q8A1A1F_;S8R1A1G4A3S0S10S6aR3R1A3G5A2A2A2A2Lrho5;A2F_;Trho4;Trho3;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;FA1;Fvals;FdsD;FJ';Fzdu;Fu;Ft;").
Proof.
  intros t u zdu J' dsD vals A1 rho tp tr ms md HOK HST HQW HOBJ HLEN HS HK HF HDC rho3 rho4 HCONT.
  unfold s_okU in HOK. repeat (apply andb_prop in HOK as [HOK ?]).
  match goal with H : forallb (zdisjb zdu) _ = true |- _ => rename H into OKZU end.
  match goal with H : forallb (fun d => forallb _ _) _ = true |- _ => rename H into OKZX end.
  match goal with H : zcheck _ = true |- _ => rename H into OKZC end.
  match goal with H : entsM _ _ _ = true |- _ => rename H into OKENT end.
  match goal with H : forallb (sprop_below _) _ = true |- _ => rename H into OKBEL end.
  match goal with H : swf (with_objs _ [uobj u]) = true |- _ => rename H into OKSWF1 end.
  match goal with H : swf (with_objs _ (map carve_obj _)) = true |- _ => rename H into OKSWF2 end.
  match goal with H : forallb _ (s_bs t) = true |- _ => rename H into OKBS end.
  match goal with H : sv_vars_all _ _ = true |- _ => rename H into OKV2 end.
  match goal with H : state_vars_all _ _ = true |- _ => rename H into OKV1 end.
  assert (HX : ax_X (s_C t) = []) by (destruct (ax_X (s_C t)); [reflexivity | discriminate HOK]).
  destruct (ro_dissolve K HL A0 rho0 (s_C t) (keepN (s_C t) (s_k t)) dsD A1 rho tp tr ms md HQW HOBJ HS HDC HK HF) as (HU & HK3 & HF3 & RW3 & RL3 & EV).
  fold rho3 in HU, HK3, HF3, RW3, RL3, EV.
  destruct (HCONT HK3 HF3 EV) as (HJ' & UOK & CC & ZUo & ZN & ZO & HFN).
  assert (H1 : SPA segsA J' (s_Cd t) rho3 tp (tr, mkCfg ms md)) by (split; [exact (proj1 HU) | exact HJ']).
  assert (MF : map fst (combine (s_bs t) vals) = s_bs t).
  { clear - HLEN. revert vals HLEN. induction (s_bs t) as [|b r IH]; intros vals HLEN; destruct vals as [|x vs]; cbn in *; try reflexivity; try discriminate. f_equal. apply IH. lia. }
  assert (H2 : SPA segsA J' (s_Cd t) rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_bindV segsA _ NPRE (s_Cd t) rho3 tp _ _ HX HST); [| rewrite MF; exact OKV1 | rewrite MF; exact OKV2 | exact H1].
    intros v Hv. rewrite MF in Hv. pose proof (proj1 (forallb_forall _ _) OKBS v Hv) as X. apply Pos.leb_le. exact X. }
  pose proof (SPA_facts_hold segsA _ rho4 (s_Cd t) tp _ H2) as HFa.
  destruct u as [[ub ulo] uhi]. cbn [uobj unk_ok] in *. destruct UOK as (U1 & U2 & U3 & U4 & U5).
  assert (H2u : SPA segsA J' (s_Cu t (ub, ulo, uhi)) rho4 tp (tr, mkCfg ms md)).
  { pose proof (SPA_carve_unk segsA J' rho4 (s_Cd t) tp (tr, mkCfg ms md) ub ulo uhi (ss_next (ax_S (s_Cd t))) H2) as Y. cbn zeta in Y. apply Y; clear Y.
    - exact OKSWF1.
    - apply Pos.le_refl.
    - exact U1.
    - exact U2.
    - exact U3.
    - exact U4.
    - pose proof (zones_cross rho4 zb zlo zhi ZU Hsep [mkObj ub ulo uhi [] DUnknown] [zdu] _ _ (Forall2_cons _ _ ZUo (Forall2_nil _)) ZO ltac:(cbn [forallb]; rewrite OKZU; reflexivity)) as ZC.
      apply Forall_cons_iff in ZC as [ZC _]. exact ZC.
    - exact U5.
    - assert (HXd : ax_X (s_Cd t) = []) by exact HX. intros rr y j Hin. rewrite HXd in Hin. destruct Hin. }
  assert (H3 : SPA segsA J' (s_CaU t (ub, ulo, uhi)) rho4 tp (tr, mkCfg ms md)).
  { pose proof (SPA_carve_list segsA J' rho4 (s_Cu t (ub, ulo, uhi)) tp _ (s_N t) (ss_next (ax_S (s_Cu t (ub, ulo, uhi)))) H2u) as Y. cbn zeta in Y. apply Y; clear Y.
    - exact OKSWF2.
    - apply Pos.le_refl.
    - apply carve_okq_list; [exact HX | exact CC].
    - apply (zones_cross rho4 zb zlo zhi ZU Hsep _ _ (ss_objs (ax_S (s_Cd t)) ++ [mkObj ub ulo uhi [] DUnknown]) (s_ZDo t ++ [zdu]) ZN); [|exact OKZX]. apply Forall2_app; [exact ZO | exact (Forall2_cons _ _ ZUo (Forall2_nil _))].
    - exact (zones_pd rho4 zb zlo zhi ZU Hsep _ _ ZN OKZC). }
  assert (H4 : SPA segsA J' (s_CcU t (ub, ulo, uhi)) rho4 tp (tr, mkCfg ms md)).
  { unfold s_CcU, addF. apply SPA_refacts; [exact H3 | exact OKBEL |]. intros HF4. apply Forall_app. split; [exact HF4 | apply HFN; exact HFa]. }
  destruct (entM_SPA J' _ (s_T t) (s_M t) rho4 tp _ OKENT HST H4) as (H5 & AG5 & V5 & RM5).
  eexists. split; [exact H5|]. split; [exact V5|]. split; [|split; [exact AG5 | exact EV]]. rewrite RM5. unfold rho4. apply rm_rho_sets.
Qed.
End SStepU.
