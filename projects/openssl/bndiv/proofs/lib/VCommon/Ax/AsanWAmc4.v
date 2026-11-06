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
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanSBase AsanSLibc AsanSMat AsanSMiz AsanSRipA AsanSRipC AsanWMemcpy AsanWMemcpyF1 AsanWMcStep AsanWMat AsanWMcM3 AsanWAmc1 AsanWAmc2 AsanWAmc3.
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
(* [comment removed for export] *)

Local Abbreviation FA x := (x segs b gI gK gR HA).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma HCLOB_in_BCL : forall r, In r HCLOB -> In r BCL.
Proof.
  intros r Hr. cbn [In HCLOB] in Hr.
  repeat (destruct Hr as [Hr|Hr]; [subst r; cbn [In BCL]; solve [repeat first [left; reflexivity | right]] |]). contradiction.
Qed.

Lemma call_rip : forall S m k beg ro,
  BI S -> mat_of model0 m k -> (0 <= k)%Z -> (k + (n + 2) <= 2 * rp n)%Z ->
  ms_pc_val S = pcw rb 0 -> rg S 2 = Z_to_bv 64 (sp - 2160) -> rg S 10 = Z_to_bv 64 beg -> rg S 11 = Z_to_bv 64 n ->
  rg S 1 = pcw b ro -> (0 <= ro < 0x1000)%Z -> (ro mod 4 = 0)%Z -> (65 <= n)%Z -> (beg = src \/ beg = dst) ->
  (forall S' m', BI S' -> (forall r, ~ In r HCLOB -> rg S' r = rg S r) -> ms_pc_val S' = pcw b ro -> rg S' 10 = w0 ->
     mat_of model0 m' (k + (n + 2)) -> realizes_cfg segs cfg (mkCfg S' m') T) ->
  realizes_cfg segs cfg (mkCfg S m) T.
Proof.
  intros S m k beg ro [HS HM] Hmat Hk Hkb Hpc HS2 HS10 HS11 HS1 Hro Hro4 Hn65 Hbeg HC.
  pose proof (mcr_svc _ _ _ HS) as Hsvc. pose proof (halted_mat m _ Hmat) as Hh.
  pose proof pages_nonneg as [Hp1 Hp2].
  destruct (Hbig Hn65) as [[Hs8 Hsreg] [Hd8 Hdreg]].
  assert (Hb0 : (0 <= beg)%Z) by (destruct Hbeg; subst beg; lz).
  assert (Hb8 : (beg + n + 8 <= 2 ^ 47)%Z) by (destruct Hbeg; subst beg; lz).
  assert (Hbreg : (0x10007fff8000 <= beg \/ beg + n + 8 <= 0x7fff8000)%Z) by (destruct Hbeg; subst beg; assumption).
  assert (Hbsh : forall q, (0x7fff8000 + beg / 8 - 7 <= q <= 0x7fff8000 + (beg + n - 1) / 8 + 7)%Z ->
            (0x7fff8000 <= q < 0x10007fff8000)%Z -> bat segs (ms_mem ms0) (Z_to_bv 64 q) = Some (Z_to_bv 8 0))
    by (destruct Hbeg; subst beg; [apply Hshs | apply Hshd]; lz).
  pose proof (sh_range beg (beg + n - 1) Hb0 ltac:(lz) ltac:(lz)) as (Hq1 & Hq2 & Hq3).
  assert (Eu2 : bv_unsigned (rg S 2) = (sp - 2160)%Z) by (rewrite HS2; apply bvu_z; lz).
  assert (Eub : bv_unsigned (Z_to_bv 64 beg) = beg) by (apply bvu_z; lz).
  refine (rip_sum segs cfg rb mz gK gMB gME gHE aK aMB aME aHE
            (rc_W _ _ _ _ _ _ _ HRC) (rc_Wh _ _ _ _ _ _ _ HRC) (rc_Wz _ _ _ _ _ _ _ HRC) (rc_Jz _ _ _ _ _ _ _ HRC)
            (rc_h0 _ _ _ _ _ _ _ HRC) (rc_h20 _ _ _ _ _ _ _ HRC)
            (rc_h28 _ _ _ _ _ _ _ HRC) (rc_h44 _ _ _ _ _ _ _ HRC) (rc_2c _ _ _ _ _ _ _ HRC) (rc_4c _ _ _ _ _ _ _ HRC) (rc_54 _ _ _ _ _ _ _ HRC)
            (rc_70 _ _ _ _ _ _ _ HRC) (rc_94 _ _ _ _ _ _ _ HRC) (rc_9c _ _ _ _ _ _ _ HRC) (rc_b8 _ _ _ _ _ _ _ HRC)
            ltac:(lz) Hrb S m T (Z_to_bv 64 beg) n Hsvc _ Hh HS10 HS11 ltac:(lz)
            _ _ _ _ _ _ _ _ _ _ _ _ _).
  - exact Hpc.
  - rewrite Eub. lz.
  - rewrite Eub. exact Hbreg.
  - exact (globals_MEMI _ HM).
  - destruct HgN as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). repeat split; eapply nl_mat; eassumption.
  - rewrite Eub. intros q Hq. apply (bat_MEMI _ q _ HM); [lz|]. apply Hbsh; lz.
  - pose proof Hmat as [_ Hu]. rewrite (mat_of_vmmaps model0 m _ Hmat). unfold amc_pages in Hbud. lz.
  - rewrite Eu2. lz.
  - rewrite Eu2. replace (sp - 2160 - 72)%Z with (sp - 2232)%Z by lz.
    apply (store_ok_mono segs 72 (ms_mem ms0)); [exact (MEMI_grows _ HM)|].
    apply (store_ok_sub segs (ms_mem ms0) (Z_to_bv 64 (sp - 2232)) _ 2232 72); rewrite ?bvu_z by lz; [lz | exact Hspok | lz | lz].
  - rewrite Eu2. eapply nl_mat; [exact Hmat|]. apply (no_lazy_sub model0 _ _ _ _ Hspnl); lz.
  - rewrite Eu2, Eub. right. lz.
  - rewrite Eu2. intros a Ha. cbn [In] in Ha. left.
    destruct Ha as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; lz.
  - rewrite HS1. apply pcw_even; lz.
  - intros S' m' HP Hpc' H10' Hmat'. rewrite Eu2 in HP.
    destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    apply (HC S' m').
    + split.
      * apply (MCR_trans BCL HCLOB ms0 S S' HS); [|exact HCLOB_in_BCL]. constructor; assumption.
      * destruct HM as [HM1 HM2]. split; [|exact (mem_grows_trans _ _ _ HM2 P8)].
        intros x Hx. rewrite P7 by lz. apply HM1. exact Hx.
    + exact P6.
    + rewrite Hpc'. exact HS1.
    + exact H10'.
    + exact (mat_of_trans _ _ _ _ _ Hmat Hmat').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac bnorm Hb :=
  rewrite ?branch_eq_z, ?branch_ne_z, ?branch_ltu_z, ?branch_geu_z in Hb by lz;
  rewrite ?negb_true_iff, ?negb_false_iff in Hb; rewrite ?Z.eqb_eq, ?Z.eqb_neq, ?Z.ltb_lt, ?Z.ltb_ge in Hb.

(* [comment removed for export] *)
Lemma shw_dst : forall m x, MEMI m -> (1 <= n)%Z -> (dst <= x <= dst + n - 1)%Z ->
  rdn segs m (Z_to_bv 64 (8 * ((0x7fff8000 + x / 8) / 8))) 8 = Some (repeat (Z_to_bv 8 0) 8).
Proof.
  intros m x HM Hn1 Hx. pose proof (shw_range x ltac:(lz)) as (A1 & A2 & A3 & A4 & A5).
  pose proof (sh_range dst x ltac:(lz) ltac:(lz) ltac:(lz)) as (B1 & B2 & B3).
  pose proof (sh_range x (dst + n - 1) ltac:(lz) ltac:(lz) ltac:(lz)) as (C1 & C2 & C3).
  apply rdn_zeros; [lz | change (Z.of_nat 8) with 8%Z; lz |].
  intros q Hq. change (Z.of_nat 8) with 8%Z in Hq. apply (bat_MEMI _ q _ HM); [lz|]. apply Hshd; lz.
Qed.

Local Ltac bi_chain HS HM := split; [bcl_chain HS | rewrite ?mem_setx; exact HM].

(* [comment removed for export] *)
Lemma d_rip : forall S m, BI S -> mat_of model0 m (rp n) -> (65 <= n)%Z -> ms_pc_val S = pcw b 0x498 ->
  rg S 2 = Z_to_bv 64 (sp - 2160) -> rg S 10 = Z_to_bv 64 dst -> rg S 11 = Z_to_bv 64 src -> rg S 12 = Z_to_bv 64 n ->
  realizes_cfg segs cfg (mkCfg S m) T.
Proof.
  intros S m HBI Hmat Hn65 Hpc HS2 HS10 HS11 HS12. pose proof HBI as [HS HM].
  pose proof (mcr_svc _ _ _ HS) as Hsvc. pose proof (halted_mat m _ Hmat) as Hh.
  assert (Erp : rp n = (n + 2)%Z) by (unfold rp; replace (n <=? 64)%Z with false by (symmetry; apply Z.leb_gt; lz); reflexivity).
  wr wacc_OpImm (FA FA_498) DA_00050493 valX.
  wr wacc_OpImm (FA FA_49c) DA_00058b13 valX.
  wr wacc_OpImm (FA FA_4a0) DA_00060593 valX.
  wr wacc_OpImm (FA FA_4a4) DA_00060913 valX.
  destruct (jal_ok_sound _ _ _ _ _ HJ2) as (wj & ij & HFj & HEj & HDj & HTj).
  eapply xs_jal; [ exact Hh | reflexivity | rewrite pc_setx; exact HFj | exact HEj | exact HDj | pcX | pcX | resvX | memX | ].
  match goal with |- realizes_cfg _ _ (mkCfg ?S' _) _ => remember S' as Sc eqn:ESc end.
  assert (HSc : BI Sc) by (subst Sc; bi_chain HS HM).
  assert (Hc2 : rg Sc 2 = Z_to_bv 64 (sp - 2160)) by (subst Sc; regX).
  assert (Hc9 : rg Sc 9 = Z_to_bv 64 dst) by (subst Sc; regX).
  assert (Hc10 : rg Sc 10 = Z_to_bv 64 dst) by (subst Sc; regX).
  assert (Hc11 : rg Sc 11 = Z_to_bv 64 n) by (subst Sc; regX).
  assert (Hc18 : rg Sc 18 = Z_to_bv 64 n) by (subst Sc; regX).
  assert (Hc22 : rg Sc 22 = Z_to_bv 64 src) by (subst Sc; regX).
  assert (Hc1 : rg Sc 1 = pcw b 0x4ac) by (subst Sc; regX).
  assert (Hcpc : ms_pc_val Sc = pcw rb 0) by (subst Sc; rewrite pc_setx; unfold pcw; f_equal; lz).
  clear ESc.
  apply (call_rip Sc m (rp n) dst 0x4ac HSc Hmat ltac:(lz) ltac:(lz) Hcpc Hc2 Hc10 Hc11 Hc1 ltac:(lz) eq_refl Hn65 (or_intror eq_refl)).
  intros S' m' HBI' HR Hpc' H10' Hmat'. pose proof HBI' as [HS' HM'].
  pose proof (mcr_svc _ _ _ HS') as Hsvc'. pose proof (halted_mat m' _ Hmat') as Hh'.
  assert (Hr2 : rg S' 2 = Z_to_bv 64 (sp - 2160)) by (rewrite HR by notin; exact Hc2).
  assert (Hr9 : rg S' 9 = Z_to_bv 64 dst) by (rewrite HR by notin; exact Hc9).
  assert (Hr18 : rg S' 18 = Z_to_bv 64 n) by (rewrite HR by notin; exact Hc18).
  assert (Hr22 : rg S' 22 = Z_to_bv 64 src) by (rewrite HR by notin; exact Hc22).
  clear HR.
  wr wacc_OpImm (FA FA_4ac) DA_000b0593 valX.
  wr wacc_OpImm (FA FA_4b0) DA_00090613 valX.
  wr wacc_OpImm (FA FA_4b4) DA_00050993 ltac:(rgn; rwregsX; reflexivity).
  wr wacc_OpImm (FA FA_4b8) DA_00048513 valX.
  wb2 (FA FA_4bc) DA_c2098ce3; [intros _ | intros Hbr; exfalso; revert Hbr; rgn; vm_compute; discriminate].
  apply s_mc; [ bi_chain HS' HM' | rewrite Erp in *; replace (2 * (n + 2))%Z with (n + 2 + (n + 2))%Z by lz; exact Hmat'
              | reflexivity | regX | regX | regX | regX ].
Qed.

Lemma s_dst : forall S m, BI S -> mat_of model0 m (rp n) -> ms_pc_val S = pcw b 0xac ->
  rg S 2 = Z_to_bv 64 (sp - 2160) -> rg S 10 = Z_to_bv 64 dst -> rg S 11 = Z_to_bv 64 src -> rg S 12 = Z_to_bv 64 n ->
  rg S 20 = Z_to_bv 64 (dst + n) -> rg S 22 = Z_to_bv 64 (n + -65) ->
  realizes_cfg segs cfg (mkCfg S m) T.
Proof.
  intros S m HBI Hmat Hpc HS2 HS10 HS11 HS12 HS20 HS22. pose proof HBI as [HS HM].
  pose proof (mcr_svc _ _ _ HS) as Hsvc. pose proof (halted_mat m _ Hmat) as Hh.
  pose proof pages_nonneg as [Hp1 Hp2].
  wr wacc_OpImm (FA FA_ac) DA_fff54693 ltac:(rgn; rwregsX; rewrite not_z by lz; reflexivity).
  wb2 (FA FA_b0) DA_0cc6ee63; [intros Hbr; bnorm Hbr; exfalso; lz | intros _].
  wr wacc_OpImm (FA FA_b4) DA_fbf00693 valX.
  wb2 (FA FA_b8) DA_1566fc63; intros Hbr;
    change (Z_to_bv 64 (-65)) with m65 in Hbr; change (Z_to_bv 64 (n + -65)) with (s6w n) in Hbr;
    rewrite size_taken in Hbr by lz.
  - (* [comment removed for export] *)
    wb2 (FA FA_210) DA_28061463; intros Hb2; unfold w0 in Hb2; bnorm Hb2.
    + (* [comment removed for export] *)
      assert (Hn65 : (65 <= n)%Z) by (destruct (n =? 0)%Z eqn:E0; [apply Z.eqb_eq in E0; lz | apply Z.leb_le; exact Hbr]).
      apply d_rip; [ bi_chain HS HM | exact Hmat | exact Hn65 | reflexivity | regX | regX | regX | regX ].
    + (* [comment removed for export] *)
      wj (FA FA_214) DA_ee1ff06f.
      apply s_mc; [ bi_chain HS HM | apply (mat_of_mono model0 m (rp n)); [exact Hmat | lz] | reflexivity | regX | regX | regX | regX ].
  - (* [comment removed for export] *)
    assert (Hn1 : (1 <= n <= 64)%Z) by (destruct (n =? 0)%Z eqn:E0; [discriminate | apply Z.eqb_neq in E0; apply Z.leb_gt in Hbr; lz]).
    assert (Erp : rp n = 2%Z) by (unfold rp; replace (n <=? 64)%Z with true by (symmetry; apply Z.leb_le; lz); reflexivity).
    destruct (globals_MEMI _ HM) as ((lgK & HlgK & HvgK) & (laK & HlaK & HvaK) & _).
    destruct HgN as (NgK & NaK & _).
    eapply xs_got; [ exact (amc_pK2 _ _ _ _ _ HA) | reflexivity | lz | lz | exact Hh | reflexivity | reflexivity
                   | rewrite ?mem_setx; exists lgK; split; [exact HlgK | exact HvgK] | eapply nl_mat; [exact Hmat | exact NgK] | ].
    intros X r0 m1 -> ->. rewrite ?resv_setx, ?mem_setx.
    wl (FA FA_c4) DA_0006b703 ltac:(cbn [msz_n]; exact HlaK)
       ltac:(cbn [msz_n]; eapply acc_cell; [exact Hmat | lz | cbn; lz | exact NaK]).
    rewrite HvaK.
    wr wacc_OpImm (FA FA_c8) DA_fffa0a13 valX.
    wr wacc_ShiftImm (FA FA_cc) DA_00355693 ltac:(rgn; rwregsX; rewrite srl3_z by lz; reflexivity).
    wr wacc_ShiftImm (FA FA_d0) DA_003a5793 ltac:(rgn; rwregsX; rewrite srl3_z by lz; reflexivity).
    wr wacc_Op (FA FA_d4) DA_00d706b3 valX.
    wr wacc_Op (FA FA_d8) DA_00f70733 valX.
    wr wacc_OpImm (FA FA_dc) DA_ff86f793 ltac:(rgn; rwregsX; rewrite and_m8 by (pose proof (sh_range dst dst ltac:(lz) ltac:(lz) ltac:(lz)); lz); reflexivity).
    wr wacc_OpImm (FA FA_e0) DA_ff877813
       ltac:(rgn; rwregsX; rewrite and_m8 by (pose proof (sh_range (dst + n + -1) (dst + n + -1) ltac:(lz) ltac:(lz) ltac:(lz)); lz); reflexivity).
    eapply (xs_ld_mat segs cfg model0 m (rp n));
      [ exact Hh0 | exact Hmat | svcX | ftacX (FA FA_e4) | ecX | exact DA_0007b783 | regX | addrX | memX
      | cbn [msz_n]; apply (shw_dst _ dst HM); lz | apply shw_pg; lz | unfold amc_pages in Hbud; rewrite Erp in *; lz | pcX | resvX | ].
    intros m2 Hmat2.
    eapply (xs_ld_mat segs cfg model0 m2 (rp n + 1));
      [ exact Hh0 | exact Hmat2 | svcX | ftacX (FA FA_e8) | ecX | exact DA_00083803 | regX | addrX | memX
      | cbn [msz_n]; apply (shw_dst _ (dst + n + -1)%Z HM); lz | apply shw_pg; lz | unfold amc_pages in Hbud; rewrite Erp in *; lz | pcX | resvX | ].
    intros m3 Hmat3. pose proof (halted_mat m3 _ Hmat3) as Hh3.
    wr wacc_Op (FA FA_ec) DA_00f867b3 ltac:(rgn; rewrite !load_zero8; apply or_zero).
    wb2 (FA FA_f0) DA_36079a63; [intros Hb3; vm_compute in Hb3; discriminate | intros _].
    apply s_mc; [ bi_chain HS HM | replace (2 * rp n)%Z with (rp n + 1 + 1)%Z by (rewrite Erp; reflexivity); exact Hmat3
                | reflexivity | regX | regX | regX | regX ].
Qed.


End Amc.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
