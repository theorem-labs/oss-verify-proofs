(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanSBase AsanSLibc AsanSMat AsanSMiz AsanSRipA AsanSRipC AsanWMemcpy AsanWMemcpyF1 AsanWMcStep AsanWMat AsanWMcM3 AsanWAmc1 AsanWAmc2 AsanWAmc3 AsanWAmc4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

(* [comment removed for export] *)
Section Amc.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variables b gI aI gK aK gMB aMB gME aME gHE aHE gR e : Z.
Variables rb mz : Z.   (* [comment removed for export] *)
Hypothesis HA : AmcCode segs b gI gK gR.
Hypothesis HRC : RipCode segs rb mz gK gMB gME gHE.
Hypothesis HJ1 : jal_ok segs b 0x3ac 1 rb = true.
Hypothesis HJ2 : jal_ok segs b 0x4a8 1 rb = true.
Hypothesis Hrb : (0x10000 <= rb /\ rb + 0x20000 < 2 ^ 47 /\ rb mod 4 = 0)%Z.
Hypothesis HMC : MCFCode segs e.
Hypothesis Hb : (0x10000 <= b /\ b + 0x30000 < 2 ^ 47 /\ b mod 4 = 0)%Z.
Hypothesis He : (0 <= e /\ e + 0x1000 < 2 ^ 47 /\ e mod 4 = 0)%Z.
Hypothesis Hgb : (0 <= gK < 2 ^ 40 /\ 0 <= gMB < 2 ^ 40 /\ 0 <= gME < 2 ^ 40 /\ 0 <= gHE < 2 ^ 40 /\
                  0 <= aK < 2 ^ 40 /\ 0 <= aMB < 2 ^ 40 /\ 0 <= aME < 2 ^ 40 /\ 0 <= aHE < 2 ^ 40 /\
                  0 <= gI < 2 ^ 40 /\ 0 <= aI < 2 ^ 40 /\ 0 <= gR < 2 ^ 40)%Z.

Variable model0 : Model.
Variable T : TSet.
Variable ms0 : machine_state.
Variables (sp dst src n : Z) (bs : list byte) (vI : byte).
Hypothesis Hh0 : m_halted model0 = None.
Hypothesis Hsp : (0x10007fff8000 + 2232 <= sp <= 2 ^ 47)%Z.
Hypothesis Hspok : store_ok segs (ms_mem ms0) (Z_to_bv 64 (sp - 2232)) 2232 = true.
Hypothesis Hspnl : no_lazy model0 (sp - 2232) sp.
Hypothesis Hn : (0 <= n <= 2 ^ 40)%Z.
Hypothesis Hd0 : (0 <= dst)%Z.
Hypothesis Hs0 : (0 <= src)%Z.
Hypothesis Hdn : (dst + n <= 2 ^ 47)%Z.
Hypothesis Hsn : (src + n <= 2 ^ 47)%Z.
Hypothesis Hbig : (65 <= n)%Z ->
  (src + n + 8 <= 2 ^ 47 /\ (0x10007fff8000 <= src \/ src + n + 8 <= 0x7fff8000))%Z /\
  (dst + n + 8 <= 2 ^ 47 /\ (0x10007fff8000 <= dst \/ dst + n + 8 <= 0x7fff8000))%Z.
Hypothesis Hdisj : (src + n <= dst \/ dst + n <= src)%Z.
Hypothesis Hdfr : (dst + n <= sp - 2232 \/ sp <= dst)%Z.
Hypothesis Hsfr : (src + n <= sp - 2232 \/ sp <= src)%Z.
Hypothesis Hbs : rdn segs (ms_mem ms0) (Z_to_bv 64 src) (Z.to_nat n) = Some bs.
Hypothesis Hsok : store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Z.to_nat n) = true.
(* [comment removed for export] *)
Hypothesis HgI : cell8 segs (ms_mem ms0) gI aI.
Hypothesis HvI : bat segs (ms_mem ms0) (Z_to_bv 64 aI) = Some vI.
Hypothesis HvI0 : bv_unsigned vI <> 0%Z.
Hypothesis HgR : cell8 segs (ms_mem ms0) gR e.
Hypothesis Hg0 : globals segs gK gMB gME gHE aK aMB aME aHE (ms_mem ms0).
Hypothesis HgN : globals_nl gK gMB gME gHE aK aMB aME aHE model0.
Hypothesis HnlI : no_lazy model0 gI (gI + 8).
Hypothesis HnlaI : no_lazy model0 aI (aI + 1).
Hypothesis HnlR : no_lazy model0 gR (gR + 8).
(* [comment removed for export] *)
Hypothesis Hshs : (1 <= n)%Z -> forall q, (0x7fff8000 + src / 8 - 7 <= q <= 0x7fff8000 + (src + n - 1) / 8 + 7)%Z ->
  (0x7fff8000 <= q < 0x10007fff8000)%Z -> bat segs (ms_mem ms0) (Z_to_bv 64 q) = Some (Z_to_bv 8 0).
Hypothesis Hshd : (1 <= n)%Z -> forall q, (0x7fff8000 + dst / 8 - 7 <= q <= 0x7fff8000 + (dst + n - 1) / 8 + 7)%Z ->
  (0x7fff8000 <= q < 0x10007fff8000)%Z -> bat segs (ms_mem ms0) (Z_to_bv 64 q) = Some (Z_to_bv 8 0).
Hypothesis Hbud : (vm_backing_used model0 + 4096 * amc_pages n <= vm_limit (m_vmmaps model0))%Z.
Hypothesis Hra : (bv_unsigned (rg ms0 1) mod 2 = 0)%Z.
Hypothesis H2 : rg ms0 2 = Z_to_bv 64 sp.
Hypothesis H10 : rg ms0 10 = Z_to_bv 64 dst.
(* [comment removed for export] *)
Local Abbreviation AMEM := (AsanWAmc3.AMEM ms0 sp dst n bs).
Hypothesis HK : forall ms' model', MCRc MCF_CLOB ms0 ms' -> AMEM (ms_mem ms') -> ms_pc_val ms' = rg ms0 1 ->
  mat_of model0 model' (amc_pages n) -> realizes_cfg segs cfg (mkCfg ms' model') T.

Set Default Proof Using "All".

Local Abbreviation SB := (AsanWAmc3.SB sp).
Local Abbreviation Mf := (AsanWAmc3.Mf ms0 sp).
Local Abbreviation MEMI := (AsanWAmc3.MEMI ms0 sp).
Local Abbreviation BI := (AsanWAmc3.BI ms0 sp).
Local Abbreviation grows_w := (AsanWAmc3.grows_w segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation SB_out := (AsanWAmc3.SB_out segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation Mf_out := (AsanWAmc3.Mf_out segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation Mf_grows := (AsanWAmc3.Mf_grows segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation MEMI_Mf := (AsanWAmc3.MEMI_Mf segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation MEMI_out := (AsanWAmc3.MEMI_out segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation MEMI_grows := (AsanWAmc3.MEMI_grows segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation rdn_MEMI := (AsanWAmc3.rdn_MEMI segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation cell8_MEMI := (AsanWAmc3.cell8_MEMI segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation bat_MEMI := (AsanWAmc3.bat_MEMI segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation globals_MEMI := (AsanWAmc3.globals_MEMI segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation rdn_SB_same := (AsanWAmc3.rdn_SB_same segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation rdn_SB_other := (AsanWAmc3.rdn_SB_other segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation rdn_slot := (AsanWAmc3.rdn_slot segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation Mf_rd1 := (AsanWAmc3.Mf_rd1 segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation Mf_rd8 := (AsanWAmc3.Mf_rd8 segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation Mf_rd9 := (AsanWAmc3.Mf_rd9 segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation Mf_rd18 := (AsanWAmc3.Mf_rd18 segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation Mf_rd19 := (AsanWAmc3.Mf_rd19 segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation Mf_rd20 := (AsanWAmc3.Mf_rd20 segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation Mf_rd21 := (AsanWAmc3.Mf_rd21 segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation Mf_rd22 := (AsanWAmc3.Mf_rd22 segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation Mf_rd23 := (AsanWAmc3.Mf_rd23 segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation Mf_rd24 := (AsanWAmc3.Mf_rd24 segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation ld_st8 := (AsanWAmc3.ld_st8 segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation nl_mat := (AsanWAmc3.nl_mat segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation acc_fr := (AsanWAmc3.acc_fr segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation acc_cell := (AsanWAmc3.acc_cell segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation halted_mat := (AsanWAmc3.halted_mat segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation pages_nonneg := (AsanWAmc3.pages_nonneg segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation MCR_restore := (AsanWAmc3.MCR_restore segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation s_epi := (AsanWAmc3.s_epi segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation MCF_in_BCL := (AsanWAmc3.MCF_in_BCL segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation s_mc := (AsanWAmc3.s_mc segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation HCLOB_in_BCL := (AsanWAmc4.HCLOB_in_BCL segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation call_rip := (AsanWAmc4.call_rip segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation shw_dst := (AsanWAmc4.shw_dst segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation d_rip := (AsanWAmc4.d_rip segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation s_dst := (AsanWAmc4.s_dst segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
(* [comment removed for export] *)

Local Abbreviation FA x := (x segs b gI gK gR HA).

Local Ltac bnorm Hb :=
  rewrite ?branch_eq_z, ?branch_ne_z, ?branch_ltu_z, ?branch_geu_z in Hb by lz;
  rewrite ?negb_true_iff, ?negb_false_iff in Hb; rewrite ?Z.eqb_eq, ?Z.eqb_neq, ?Z.ltb_lt, ?Z.ltb_ge in Hb.
Local Ltac bi_chain HS HM := split; [bcl_chain HS | rewrite ?mem_setx; exact HM].

(* [comment removed for export] *)
Lemma shw_src : forall m x, MEMI m -> (1 <= n)%Z -> (src <= x <= src + n - 1)%Z ->
  rdn segs m (Z_to_bv 64 (8 * ((0x7fff8000 + x / 8) / 8))) 8 = Some (repeat (Z_to_bv 8 0) 8).
Proof.
  intros m x HM Hn1 Hx. pose proof (shw_range x ltac:(lz)) as (A1 & A2 & A3 & A4 & A5).
  pose proof (sh_range src x ltac:(lz) ltac:(lz) ltac:(lz)) as (B1 & B2 & B3).
  pose proof (sh_range x (src + n - 1) ltac:(lz) ltac:(lz) ltac:(lz)) as (C1 & C2 & C3).
  apply rdn_zeros; [lz | change (Z.of_nat 8) with 8%Z; lz |].
  intros q Hq. change (Z.of_nat 8) with 8%Z in Hq. apply (bat_MEMI _ q _ HM); [lz|]. apply Hshs; lz.
Qed.

(* [comment removed for export] *)
Lemma s_rip : forall S m, BI S -> mat_of model0 m 0 -> (65 <= n)%Z -> ms_pc_val S = pcw b 0x398 ->
  rg S 2 = Z_to_bv 64 (sp - 2160) -> rg S 10 = Z_to_bv 64 dst -> rg S 11 = Z_to_bv 64 src -> rg S 12 = Z_to_bv 64 n ->
  rg S 20 = Z_to_bv 64 (dst + n) -> rg S 22 = Z_to_bv 64 (n + -65) ->
  realizes_cfg segs cfg (mkCfg S m) T.
Proof.
  intros S m HBI Hmat Hn65 Hpc HS2 HS10 HS11 HS12 HS20 HS22. pose proof HBI as [HS HM].
  pose proof (mcr_svc _ _ _ HS) as Hsvc. pose proof (halted_mat m _ Hmat) as Hh.
  assert (Erp : rp n = (n + 2)%Z) by (unfold rp; replace (n <=? 64)%Z with false by (symmetry; apply Z.leb_gt; lz); reflexivity).
  wr wacc_OpImm (FA FA_398) DA_00050b93 valX.
  wr wacc_OpImm (FA FA_39c) DA_00058513 valX.
  wr wacc_OpImm (FA FA_3a0) DA_00058c13 valX.
  wr wacc_OpImm (FA FA_3a4) DA_00060593 valX.
  wr wacc_OpImm (FA FA_3a8) DA_00060493 valX.
  destruct (jal_ok_sound _ _ _ _ _ HJ1) as (wj & ij & HFj & HEj & HDj & HTj).
  eapply xs_jal; [ exact Hh | reflexivity | rewrite pc_setx; exact HFj | exact HEj | exact HDj | pcX | pcX | resvX | memX | ].
  match goal with |- realizes_cfg _ _ (mkCfg ?S' _) _ => remember S' as Sc eqn:ESc end.
  assert (HSc : BI Sc) by (subst Sc; bi_chain HS HM).
  assert (Hc2 : rg Sc 2 = Z_to_bv 64 (sp - 2160)) by (subst Sc; regX).
  assert (Hc9 : rg Sc 9 = Z_to_bv 64 n) by (subst Sc; regX).
  assert (Hc10 : rg Sc 10 = Z_to_bv 64 src) by (subst Sc; regX).
  assert (Hc11 : rg Sc 11 = Z_to_bv 64 n) by (subst Sc; regX).
  assert (Hc20 : rg Sc 20 = Z_to_bv 64 (dst + n)) by (subst Sc; regX).
  assert (Hc22 : rg Sc 22 = Z_to_bv 64 (n + -65)) by (subst Sc; regX).
  assert (Hc23 : rg Sc 23 = Z_to_bv 64 dst) by (subst Sc; regX).
  assert (Hc24 : rg Sc 24 = Z_to_bv 64 src) by (subst Sc; regX).
  assert (Hc1 : rg Sc 1 = pcw b 0x3b0) by (subst Sc; regX).
  assert (Hcpc : ms_pc_val Sc = pcw rb 0) by (subst Sc; rewrite pc_setx; unfold pcw; f_equal; lz).
  clear ESc.
  apply (call_rip Sc m 0 src 0x3b0 HSc Hmat ltac:(lz) ltac:(lz) Hcpc Hc2 Hc10 Hc11 Hc1 ltac:(lz) eq_refl Hn65 (or_introl eq_refl)).
  intros S' m' HBI' HR Hpc' H10' Hmat'. pose proof HBI' as [HS' HM'].
  pose proof (mcr_svc _ _ _ HS') as Hsvc'. pose proof (halted_mat m' _ Hmat') as Hh'.
  assert (Hr2 : rg S' 2 = Z_to_bv 64 (sp - 2160)) by (rewrite HR by notin; exact Hc2).
  assert (Hr9 : rg S' 9 = Z_to_bv 64 n) by (rewrite HR by notin; exact Hc9).
  assert (Hr20 : rg S' 20 = Z_to_bv 64 (dst + n)) by (rewrite HR by notin; exact Hc20).
  assert (Hr22 : rg S' 22 = Z_to_bv 64 (n + -65)) by (rewrite HR by notin; exact Hc22).
  assert (Hr23 : rg S' 23 = Z_to_bv 64 dst) by (rewrite HR by notin; exact Hc23).
  assert (Hr24 : rg S' 24 = Z_to_bv 64 src) by (rewrite HR by notin; exact Hc24).
  clear HR.
  wr wacc_OpImm (FA FA_3b0) DA_000c0593 valX.
  wr wacc_OpImm (FA FA_3b4) DA_00048613 valX.
  wr wacc_OpImm (FA FA_3b8) DA_00050913 ltac:(rgn; rwregsX; reflexivity).
  wr wacc_OpImm (FA FA_3bc) DA_000b8513 valX.
  wb2 (FA FA_3c0) DA_ce0906e3; [intros _ | intros Hbr; exfalso; revert Hbr; rgn; vm_compute; discriminate].
  apply s_dst; [ bi_chain HS' HM' | rewrite Erp; exact Hmat' | reflexivity | regX | regX | regX | regX | regX | regX ].
Qed.

Lemma s_src : forall S m, BI S -> mat_of model0 m 0 -> ms_pc_val S = pcw b 0x60 ->
  rg S 2 = Z_to_bv 64 (sp - 2160) -> rg S 10 = Z_to_bv 64 dst -> rg S 11 = Z_to_bv 64 src -> rg S 12 = Z_to_bv 64 n ->
  rg S 19 = Z_to_bv 64 (src + n) -> rg S 20 = Z_to_bv 64 (dst + n) ->
  realizes_cfg segs cfg (mkCfg S m) T.
Proof.
  intros S m HBI Hmat Hpc HS2 HS10 HS11 HS12 HS19 HS20. pose proof HBI as [HS HM].
  pose proof (mcr_svc _ _ _ HS) as Hsvc. pose proof (halted_mat m _ Hmat) as Hh.
  pose proof pages_nonneg as [Hp1 Hp2].
  wr wacc_OpImm (FA FA_60) DA_fff5c693 ltac:(rgn; rwregsX; rewrite not_z by lz; reflexivity).
  wb2 (FA FA_64) DA_26c6e863; [intros Hbr; bnorm Hbr; exfalso; lz | intros _].
  wr wacc_OpImm (FA FA_68) DA_fbf60b13 valX.
  wr wacc_OpImm (FA FA_6c) DA_fbf00693 valX.
  wb2 (FA FA_70) DA_2f66f663; intros Hbr;
    change (Z_to_bv 64 (-65)) with m65 in Hbr; change (Z_to_bv 64 (n + -65)) with (s6w n) in Hbr;
    rewrite size_taken in Hbr by lz.
  - (* [comment removed for export] *)
    wb2 (FA FA_35c) DA_02061e63; intros Hb2; unfold w0 in Hb2; bnorm Hb2.
    + (* [comment removed for export] *)
      assert (Hn65 : (65 <= n)%Z) by (destruct (n =? 0)%Z eqn:E0; [apply Z.eqb_eq in E0; lz | apply Z.leb_le; exact Hbr]).
      apply s_rip; [ bi_chain HS HM | exact Hmat | exact Hn65 | reflexivity | regX | regX | regX | regX | regX | regX ].
    + (* [comment removed for export] *)
      wj (FA FA_360) DA_d4dff06f.
      apply s_dst; [ bi_chain HS HM | apply (mat_of_mono model0 m 0); [exact Hmat | lz] | reflexivity | regX | regX | regX | regX | regX | regX ].
  - (* [comment removed for export] *)
    assert (Hn1 : (1 <= n <= 64)%Z) by (destruct (n =? 0)%Z eqn:E0; [discriminate | apply Z.eqb_neq in E0; apply Z.leb_gt in Hbr; lz]).
    assert (Erp : rp n = 2%Z) by (unfold rp; replace (n <=? 64)%Z with true by (symmetry; apply Z.leb_le; lz); reflexivity).
    destruct (globals_MEMI _ HM) as ((lgK & HlgK & HvgK) & (laK & HlaK & HvaK) & _).
    destruct HgN as (NgK & NaK & _).
    eapply xs_got; [ exact (amc_pK1 _ _ _ _ _ HA) | reflexivity | lz | lz | exact Hh | reflexivity | reflexivity
                   | rewrite ?mem_setx; exists lgK; split; [exact HlgK | exact HvgK] | eapply nl_mat; [exact Hmat | exact NgK] | ].
    intros X r0 m1 -> ->. rewrite ?resv_setx, ?mem_setx.
    wl (FA FA_7c) DA_0006b703 ltac:(cbn [msz_n]; exact HlaK)
       ltac:(cbn [msz_n]; eapply acc_cell; [exact Hmat | lz | cbn; lz | exact NaK]).
    rewrite HvaK.
    wr wacc_OpImm (FA FA_80) DA_fff98993 valX.
    wr wacc_ShiftImm (FA FA_84) DA_0035d693 ltac:(rgn; rwregsX; rewrite srl3_z by lz; reflexivity).
    wr wacc_ShiftImm (FA FA_88) DA_0039d793 ltac:(rgn; rwregsX; rewrite srl3_z by lz; reflexivity).
    wr wacc_Op (FA FA_8c) DA_00d706b3 valX.
    wr wacc_Op (FA FA_90) DA_00f70733 valX.
    wr wacc_OpImm (FA FA_94) DA_ff86f793 ltac:(rgn; rwregsX; rewrite and_m8 by (pose proof (sh_range src src ltac:(lz) ltac:(lz) ltac:(lz)); lz); reflexivity).
    wr wacc_OpImm (FA FA_98) DA_ff877813
       ltac:(rgn; rwregsX; rewrite and_m8 by (pose proof (sh_range (src + n + -1) (src + n + -1) ltac:(lz) ltac:(lz) ltac:(lz)); lz); reflexivity).
    eapply (xs_ld_mat segs cfg model0 m 0);
      [ exact Hh0 | exact Hmat | svcX | ftacX (FA FA_9c) | ecX | exact DA_0007b783 | regX | addrX | memX
      | cbn [msz_n]; apply (shw_src _ src HM); lz | apply shw_pg; lz | unfold amc_pages in Hbud; rewrite Erp in *; lz | pcX | resvX | ].
    intros m2 Hmat2.
    eapply (xs_ld_mat segs cfg model0 m2 (0 + 1));
      [ exact Hh0 | exact Hmat2 | svcX | ftacX (FA FA_a0) | ecX | exact DA_00083803 | regX | addrX | memX
      | cbn [msz_n]; apply (shw_src _ (src + n + -1)%Z HM); lz | apply shw_pg; lz | unfold amc_pages in Hbud; rewrite Erp in *; lz | pcX | resvX | ].
    intros m3 Hmat3. pose proof (halted_mat m3 _ Hmat3) as Hh3.
    wr wacc_Op (FA FA_a4) DA_00f867b3 ltac:(rgn; rewrite !load_zero8; apply or_zero).
    wb2 (FA FA_a8) DA_2a079e63; [intros Hb3; vm_compute in Hb3; discriminate | intros _].
    apply s_dst; [ bi_chain HS HM | rewrite Erp; exact Hmat3 | reflexivity | regX | regX | regX | regX | regX | regX ].
Qed.

End Amc.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
