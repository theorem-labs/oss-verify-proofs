(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanSBase AsanSLibc AsanSMat AsanSMiz AsanSRipA AsanSRipC AsanWMemcpy AsanWMemcpyF1 AsanWMcStep AsanWMat AsanWMcM3 AsanWAmc1 AsanWAmc2 AsanWAmc3 AsanWAmc4 AsanWAmc5.
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
Local Abbreviation shw_src := (AsanWAmc5.shw_src segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation s_rip := (AsanWAmc5.s_rip segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
Local Abbreviation s_src := (AsanWAmc5.s_src segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK).
(* [comment removed for export] *)

Local Abbreviation FA x := (x segs b gI gK gR HA).

Local Ltac bnorm Hb :=
  rewrite ?branch_eq_z, ?branch_ne_z, ?branch_ltu_z, ?branch_geu_z in Hb by lz;
  rewrite ?negb_true_iff, ?negb_false_iff in Hb; rewrite ?Z.eqb_eq, ?Z.eqb_neq, ?Z.ltb_lt, ?Z.ltb_ge in Hb.
Local Ltac bi_chain HS HM := split; [bcl_chain HS | rewrite ?mem_setx; exact HM].

(* [comment removed for export] *)
Lemma st_slot : forall m (a : Z), mem_grows (ms_mem ms0) m -> (sp - 2232 <= a)%Z -> (a + 8 <= sp)%Z ->
  store_ok segs m (Z_to_bv 64 a) 8 = true.
Proof.
  intros m a Hg Ha1 Ha2. apply (store_ok_mono segs 8 (ms_mem ms0)); [exact Hg|].
  apply (store_ok_sub segs (ms_mem ms0) (Z_to_bv 64 (sp - 2232)) _ 2232 8); rewrite ?bvu_z by lz; [lz | exact Hspok | lz | lz].
Qed.

Lemma s_pro : ms_svc_pending ms0 = None -> ms_pc_val ms0 = pcw b 0 ->
  rg ms0 11 = Z_to_bv 64 src -> rg ms0 12 = Z_to_bv 64 n -> realizes_cfg segs cfg (mkCfg ms0 model0) T.
Proof.
  intros Hsvc0 Hpc0 H11 H12. pose proof Hh0 as Hh. pose proof (mat_of_refl model0) as Hmat0.
  Local Ltac sdslot F D Hmat0 :=
    ws F D regX ltac:(cbn [msz_n]; apply st_slot; [repeat apply grows_w; apply mem_grows_refl | lz | lz])
       ltac:(cbn [msz_n]; eapply acc_fr; [exact Hmat0 | lz | change (Z.of_nat 8) with 8%Z; lz]).
  wr wacc_OpImm (FA FA_0) DA_81010113 valX.
  sdslot (FA FA_4) DA_7e113423 Hmat0. sdslot (FA FA_8) DA_7e813023 Hmat0. sdslot (FA FA_c) DA_7c913c23 Hmat0.
  sdslot (FA FA_10) DA_7d213823 Hmat0. sdslot (FA FA_14) DA_7d313423 Hmat0. sdslot (FA FA_18) DA_7d413023 Hmat0.
  sdslot (FA FA_1c) DA_7b513c23 Hmat0. sdslot (FA FA_20) DA_7b613823 Hmat0. sdslot (FA FA_24) DA_7b713423 Hmat0.
  sdslot (FA FA_28) DA_7b813023 Hmat0.
  match goal with |- realizes_cfg _ _ (mkCfg ?S' _) _ => remember S' as S1 eqn:E1 end.
  assert (HS1 : MCRc BCL ms0 S1) by (subst S1; bcl_chain (MCR_refl BCL ms0 Hsvc0)).
  assert (Hm1 : ms_mem S1 = Mf).
  { subst S1. rewrite mem_setx. unfold AsanWAmc3.Mf, AsanWAmc3.SB.
    replace (sp + -2032 + 2024)%Z with (sp + -8)%Z by lz. replace (sp + -2032 + 2016)%Z with (sp + -16)%Z by lz.
    replace (sp + -2032 + 2008)%Z with (sp + -24)%Z by lz. replace (sp + -2032 + 2000)%Z with (sp + -32)%Z by lz.
    replace (sp + -2032 + 1992)%Z with (sp + -40)%Z by lz. replace (sp + -2032 + 1984)%Z with (sp + -48)%Z by lz.
    replace (sp + -2032 + 1976)%Z with (sp + -56)%Z by lz. replace (sp + -2032 + 1968)%Z with (sp + -64)%Z by lz.
    replace (sp + -2032 + 1960)%Z with (sp + -72)%Z by lz. replace (sp + -2032 + 1952)%Z with (sp + -80)%Z by lz.
    reflexivity. }
  assert (H1_2 : rg S1 2 = Z_to_bv 64 (sp + -2032)) by (subst S1; regX).
  assert (H1_10 : rg S1 10 = Z_to_bv 64 dst) by (subst S1; regX).
  assert (H1_11 : rg S1 11 = Z_to_bv 64 src) by (subst S1; regX).
  assert (H1_12 : rg S1 12 = Z_to_bv 64 n) by (subst S1; regX).
  assert (H1pc : ms_pc_val S1 = pcw b 0x2c) by (subst S1; reflexivity).
  assert (H1svc : ms_svc_pending S1 = None) by (subst S1; reflexivity).
  clear E1.
  assert (HM1 : MEMI (ms_mem S1)) by (rewrite Hm1; exact MEMI_Mf).
  wr wacc_OpImm (FA FA_2c) DA_7f010413 valX.
  wr wacc_OpImm (FA FA_30) DA_f8010113 valX.
  eapply xs_got; [ exact (amc_pI _ _ _ _ _ HA) | reflexivity | lz | lz | exact Hh | reflexivity | reflexivity
                 | rewrite ?mem_setx; apply cell8_MEMI; [exact HM1 | lz | exact HgI] | exact HnlI | ].
  intros X r0 m1 -> ->. rewrite ?resv_setx, ?mem_setx.
  wl (FA FA_3c) DA_0006c683 ltac:(cbn [msz_n]; apply rdn_1; apply (bat_MEMI _ aI vI HM1); [lz | exact HvI])
     ltac:(cbn [msz_n]; eapply acc_cell; [exact Hmat0 | lz | cbn; lz | exact HnlaI]).
  wb2 (FA FA_40) DA_0e068a63; [intros Hbr; exfalso; revert Hbr; rgn; rewrite lbu_nz by exact HvI0; discriminate | intros _].
  wr wacc_OpImm (FA FA_44) DA_80040a93 valX.
  wr wacc_OpImm (FA FA_48) DA_f98a8a93 valX.
  wr wacc_Op (FA FA_4c) DA_00c589b3 valX.
  wr wacc_Op (FA FA_50) DA_00c50a33 valX.
  Local Ltac to_src HS1 HM1 Hmat0 :=
    apply s_src; [ bi_chain HS1 HM1 | exact Hmat0 | reflexivity | rgn; rwregsX; apply f_equal; lz | regX | regX | regX | regX | regX ].
  wb2 (FA FA_54) DA_00b50663; intros Hb1; [to_src HS1 HM1 Hmat0|].
  wb2 (FA FA_58) DA_0145f463; intros Hb2; [to_src HS1 HM1 Hmat0|].
  wb2 (FA FA_5c) DA_1b356e63; intros Hb3; [|to_src HS1 HM1 Hmat0].
  exfalso. bnorm Hb2. bnorm Hb3. lia.
Qed.

End Amc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem amc_sum : forall (segs : list Segment) (cfg : SpuriousCfg) (b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz : Z),
  AmcCode segs b gI gK gR -> RipCode segs rb mz gK gMB gME gHE ->
  jal_ok segs b 0x3ac 1 rb = true -> jal_ok segs b 0x4a8 1 rb = true ->
  (0x10000 <= rb /\ rb + 0x20000 < 2 ^ 47 /\ rb mod 4 = 0)%Z -> MCFCode segs e ->
  (0x10000 <= b /\ b + 0x30000 < 2 ^ 47 /\ b mod 4 = 0)%Z -> (0 <= e /\ e + 0x1000 < 2 ^ 47 /\ e mod 4 = 0)%Z ->
  (0 <= gK < 2 ^ 40 /\ 0 <= gMB < 2 ^ 40 /\ 0 <= gME < 2 ^ 40 /\ 0 <= gHE < 2 ^ 40 /\
   0 <= aK < 2 ^ 40 /\ 0 <= aMB < 2 ^ 40 /\ 0 <= aME < 2 ^ 40 /\ 0 <= aHE < 2 ^ 40 /\
   0 <= gI < 2 ^ 40 /\ 0 <= aI < 2 ^ 40 /\ 0 <= gR < 2 ^ 40)%Z ->
  forall (ms : machine_state) (model : Model) (T : TSet) (sp dst src n : Z) (bs : list byte) (vI : byte),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw b 0 -> m_halted model = None ->
  rg ms 2 = Z_to_bv 64 sp -> rg ms 10 = Z_to_bv 64 dst -> rg ms 11 = Z_to_bv 64 src -> rg ms 12 = Z_to_bv 64 n ->
  (0x10007fff8000 + 2232 <= sp <= 2 ^ 47)%Z ->
  store_ok segs (ms_mem ms) (Z_to_bv 64 (sp - 2232)) 2232 = true -> no_lazy model (sp - 2232) sp ->
  (0 <= n <= 2 ^ 40)%Z -> (0 <= dst)%Z -> (0 <= src)%Z -> (dst + n <= 2 ^ 47)%Z -> (src + n <= 2 ^ 47)%Z ->
  ((65 <= n)%Z ->
     (src + n + 8 <= 2 ^ 47 /\ (0x10007fff8000 <= src \/ src + n + 8 <= 0x7fff8000))%Z /\
     (dst + n + 8 <= 2 ^ 47 /\ (0x10007fff8000 <= dst \/ dst + n + 8 <= 0x7fff8000))%Z) ->
  (src + n <= dst \/ dst + n <= src)%Z -> (dst + n <= sp - 2232 \/ sp <= dst)%Z -> (src + n <= sp - 2232 \/ sp <= src)%Z ->
  rdn segs (ms_mem ms) (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
  store_ok segs (ms_mem ms) (Z_to_bv 64 dst) (Z.to_nat n) = true ->
  cell8 segs (ms_mem ms) gI aI -> bat segs (ms_mem ms) (Z_to_bv 64 aI) = Some vI -> bv_unsigned vI <> 0%Z ->
  cell8 segs (ms_mem ms) gR e ->
  globals segs gK gMB gME gHE aK aMB aME aHE (ms_mem ms) -> globals_nl gK gMB gME gHE aK aMB aME aHE model ->
  no_lazy model gI (gI + 8) -> no_lazy model aI (aI + 1) -> no_lazy model gR (gR + 8) ->
  ((1 <= n)%Z -> forall q, (0x7fff8000 + src / 8 - 7 <= q <= 0x7fff8000 + (src + n - 1) / 8 + 7)%Z ->
     (0x7fff8000 <= q < 0x10007fff8000)%Z -> bat segs (ms_mem ms) (Z_to_bv 64 q) = Some (Z_to_bv 8 0)) ->
  ((1 <= n)%Z -> forall q, (0x7fff8000 + dst / 8 - 7 <= q <= 0x7fff8000 + (dst + n - 1) / 8 + 7)%Z ->
     (0x7fff8000 <= q < 0x10007fff8000)%Z -> bat segs (ms_mem ms) (Z_to_bv 64 q) = Some (Z_to_bv 8 0)) ->
  (vm_backing_used model + 4096 * amc_pages n <= vm_limit (m_vmmaps model))%Z ->
  (bv_unsigned (rg ms 1) mod 2 = 0)%Z ->
  (forall ms' model', MCRc MCF_CLOB ms ms' -> AMEM ms sp dst n bs (ms_mem ms') -> ms_pc_val ms' = rg ms 1 ->
     mat_of model model' (amc_pages n) -> realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb ms0 model0 T sp dst src n bs vI
         Hsvc0 Hpc0 Hh0 H2 H10 H11 H12 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN
         HnlI HnlaI HnlR Hshs Hshd Hbud Hra HK.
  exact (s_pro segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HA HRC HJ1 HJ2 Hrb HMC Hb He Hgb model0 T ms0 sp dst src n bs vI Hh0 Hsp Hspok Hspnl Hn Hd0 Hs0 Hdn Hsn Hbig Hdisj Hdfr Hsfr Hbs Hsok HgI HvI HvI0 HgR Hg0 HgN HnlI HnlaI HnlR Hshs Hshd Hbud Hra H2 H10 HK Hsvc0 Hpc0 H11 H12).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
