(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.

(* [comment removed for export] *)
Module TobjJAH.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "prod"; "snd"; "fst"; "pair"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bxt"; "BXok_d"; "BUD"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "JA_pre"; "ndesc"; "keptFA"; "pclFA"; "pclSA"; "AHead"; "ANone"; "NDA"; "amode"; "nd_am"; "nd_bd"; "nd_fr"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "PostsC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH.WithSegs"; "ndh"; "PDh"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena"; "HDR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM SymSoundR SymFrame SymEntail SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV TobjArena.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Model Iface RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S2dS7S1SeQ40A1A1S2aOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S2cVsegs;VAInv;VCST;A3").
Variable Kc : KcA.
Variable P0c : ltac2:(tb__ "0|1|
S1S2S0S0A2M0A1S1S2G0S0A2A1S7OF_;F_;F_;").
Variable PAc : AA -> Prop.
Variable PreC : axst.
Variable ndC : ndesc.
Variable PD : list pdescA.
Variable NPc : positive.
Variable h0 : positive.
Variable pot : bool.
Hypothesis Hh0 : (h0 < NPc)%positive.
Hypothesis HamC : nd_am ndC = ANone.
Hypothesis HamPD : ltac2:(tb__ "0|1|
S28S2S10S17A2M0G0S26S1eS1fS3S10S17R1A3A1S1cA3Ld;VPD;A3").
Hypothesis P0mono : ltac2:(tb__ "0|2|
S1S2S0S0A2M0A1M1G1S1S2G0S0A2A1S7G0SdG0R1R5A3SdG0R2R5A3F_;Fbn;VP0c;R5R3R2A3VP0c;R5R4R3A3F_;F_;Fr;FFFc;FF';FF;").

Definition ndh (nd : ndesc) : ndesc := ltac2:(tb__ "0|0|
S1dS22Vnd;A1S21Vnd;A1S20Vnd;A1S1bS8Vh0;A1Vpot;A2A4").
Definition PDh : list pdescA := ltac2:(tb__ "0|1|
S29S2S10S17A2M0G0G0S5S10S17S4S10S17R1A3S24S3S10S17R1A3A1A4Ld;VPD;A4").

Definition nblk (bc : Z * Z) : Z * Z := ltac2:(tb__ "0|0|
S5S0S0S4S0S0Vbc;A3S2eS2bS3S0S0Vbc;A3A2A4").

Lemma BUD_bx_ext : ltac2:(tb__ "0|1|
S1S15A1S2S0S0A2M0G0S0S0S0S7S26S0S4S0S0R6A3S4S0S0R5A3A3S26S0S3S0S0R7A3S3S0S0R6A3A3S14R9R8R6R5R4R3A6S14RaR8R7R6R5R4A6F_;F_;F_;Frho;FKf;FKm;FV;FB2;FB1;Fb;").
Proof using . clear. intros b B1 B2 V Km Kf rho E1 E2 H. unfold BUD in *. rewrite <- E1, <- E2. exact H. Qed.

Lemma pclFA_mono : ltac2:(tb__ "0|2|
S7S1S2S0S0A2M0A1M1G1S1S2G0S0A2A1S0G0SdG0R1R5A3SdG0R2R5A3F_;Fbn;S19VCST;R6R5R3R2A5S19VCST;R7R5R4R3A5F_;F_;Fa;FFFc;FF';FF;Fr;").
Proof using .
  clear. intros r F F' FFc a Hs [H|[H|[(b & n & Hin & Hr)|H]]]; [left; exact H | right; left; exact H | | right; right; right; exact H].
  right; right; left. exists b, n. split; [apply Hs; exact Hin | exact Hr].
Qed.
Lemma pclSA_mono : ltac2:(tb__ "0|2|
S7S1S2S0S0A2M0A1M1G1S1S2G0S0A2A1S0G0SdG0R1R5A3SdG0R2R5A3F_;Fbn;S1aVCST;VXGL;R6R5R3R2A6S1aVCST;VXGL;R7R5R4R3A6F_;F_;Fa;FFFc;FF';FF;Fr;").
Proof using .
  clear. intros r F F' FFc a Hs (x & Hx & [H|H] & E); exists x; (split; [exact Hx|]); (split; [|exact E]); [left; apply (pclFA_mono r F F'); assumption | right; exact H].
Qed.
Lemma keptFA_mono : ltac2:(tb__ "0|3|
S7S1S2S0S0A2M0A1M1G1S1S2G0S0A2A1SeQ40A1S6SeQ8A1A1F_;M2G2G0SdG0R1R6A3SdG0R2R6A3F_;Fbn;S18VCST;VXGL;R7R5R4R3R2A7S18VCST;VXGL;R8R7R5R4R3A7F_;F_;Fm1;Fm0;FFFc;FF';FF;Fr;").
Proof using .
  clear. intros r F F' FFc m0 m1 Hs [K1 K2]. split.
  - intros a Ha [Hp|[Hp Hd]]; apply (K1 a Ha); [left; apply (pclFA_mono r F F'); assumption | right; split; [apply (pclSA_mono r F F'); assumption | exact Hd]].
  - intros a j Ha Hp Hj Hd. apply (K2 a j Ha); [apply (pclSA_mono r F F'); assumption | exact Hj | exact Hd].
Qed.

Section T.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S9S9S9SaR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_post : ltac2:(tb__ "0|0|
S9S9S9SaR3R1A1R3R2A1F_;Fw;VTR;R4R3A2VTR;R5R3A2F_;F_;FQ';FQ;FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OS9S9R3VTR;R3R2A2F_;VTR;SaS27R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX;").
Context {d : Z}.
Hypothesis SUMT : ltac2:(tb__ "0|1|
S1S2S0S0A2M0A1S1S2G0S0A2A1S12S7S1SeQ40A1A1S13Vd;R3A2VTR;SfVsegs;S16VAInv;VCST;VXGL;VKc;VP0c;R6R5A2R6R5R4VPAc;VndC;AaVPreC;R3R2A5S11Vsegs;VNPc;R3R2S23VAInv;VCST;VXGL;VKc;VP0c;VPAc;VPD;R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Theorem JA_frame_sumT : ltac2:(tb__ "0|1|
S1S2S0S0A2M0A1S1S2G0S0A2A1S12S7S1SeQ40A1A1S13Vd;R3A2VTR;SfVsegs;S16VAInv;VCST;VXGL;VKc;VP0c;R6R5A2R6R5R4VPAc;S24VndC;A1AaVPreC;R3R2A5S11Vsegs;VNPc;R3R2S23VAInv;VCST;VXGL;VKc;VP0c;VPAc;S25R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof using ALA HamC HamPD Hh0 P0mono SUMT TR_exw TR_post TR_pre TR_pureh.
  intros FBc FFc BXc rho1 tp1 HBX.
  set (h := uval rho1 (SVar h0)).
  set (P := apot (AHead (SVar h0) pot) rho1).

  apply (TR_pre (fun w => exists Ai ns,
            (chainZ FBc Ai (rm rho1) (tvals rho1 (nd_tv ndC)) h ns /\ P0c FBc FFc rho1 /\ (exists tp md, AInv Ai rho1 tp md))
            /\ SPA segs (JA_pre AInv CST XGL Kc (P0c (FBc ++ map nblk ns) FFc) (FBc ++ map nblk ns) FFc
                            (mkBX (bxa (bx2 BXc) P (KU * Z.of_nat (length ns))) (bxS BXc) (bxN BXc)) PAc ndC) PreC rho1 tp1 w)).
  { intros [tr [ms md]] [Hsm HJ].
    destruct HJ as (Hk & Ai & kc & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    cbn [nd_tv nd_fr nd_bd nd_am ndh] in HN, HD, HZ, HFR, HXA, HBU.
    unfold XA in HXA. cbn [am_eval] in HXA. destruct HXA as [HXA HCEN]. cbn -[chainZ KU] in HXA. destruct HXA as (ns & HC & Hkc). fold h in HC.
    exists Ai, ns. split.
    - split; [exact HC|]. split; [exact HP0|]. exists tp1, md. exact HM.
    - split; [exact Hsm|]. split; [exact Hk|]. exists Ai, 0.
      assert (NODE : forall bc, In bc ns -> In (nblk bc) (aa_live Ai) /\ ~ In (nblk bc) FBc /\ untrackedZ (tvals rho1 (nd_tv ndC)) (nblk bc)).
      { intros bc Hbc. destruct HC as [_ [HF _]]. destruct (proj1 (Forall_forall _ _) HF bc Hbc) as (N1 & N2 & N3 & _). unfold nblk. auto. }
      split; [exact HM|]. split; [exact HT|]. split.
      { intros bn Hbn. apply in_app_or in Hbn as [Hbn|Hbn]; [exact (HB bn Hbn)|]. apply in_map_iff in Hbn as (bc & <- & Hbc). exact (proj1 (NODE bc Hbc)). }
      split; [exact HFF|]. split.
      { split; [|split; [exact HD | exact HZ]]. unfold tvinA in HN |- *. apply Forall_forall. intros t Ht Hnz.
        destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [exact X1|].
        intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (X2 Hin)|]. apply in_map_iff in Hin as (bc & Heq & Hbc).
        apply (proj2 (proj2 (NODE bc Hbc)) (tvv rho1 t)); [unfold tvals; apply in_map; exact Ht | exact Hnz | symmetry; exact Heq]. }
      split; [exact HFR|]. split; [apply keptFA_refl|]. split; [apply (P0mono FBc); [intros bn Hbn; apply in_or_app; left; exact Hbn | exact HP0]|].
      split.
      { rewrite HamC. unfold XA. cbn [am_eval]. split; [reflexivity|].

        intros bn L1 L2 L3 L4. cbn [amblkZ]. apply L3. apply in_or_app. right.
        assert (L3' : ~ In bn FBc) by (intros Hf; apply L3; apply in_or_app; left; exact Hf).
        pose proof (HCEN bn L1 L2 L3' L4) as HAM. cbn [amblkZ] in HAM. fold h in HAM. destruct HAM as (ns' & HC' & Hin').
        rewrite (achain_det _ _ _ _ (proj1 HC) HC') in Hin'. exact Hin'. }
      split; [|exact (conj HPA (conj HCKi HCNi))].
      rewrite HamC. unfold apot. cbn [am_eval apotz]. rewrite <- Hkc. fold P in HBU.
      apply (BUD_bx_ext _ (bxa (bx2 BXc) P kc)); [cbn; lia | cbn; lia | exact HBU]. }
  apply TR_exw. intros Ai. apply TR_exw. intros ns. apply TR_pureh. intros (HC & HP0 & (tp0 & md0 & HM0)).
  set (FBn := FBc ++ map nblk ns). set (kc := KU * Z.of_nat (length ns)). set (BXn := mkBX (bxa (bx2 BXc) P kc) (bxS BXc) (bxN BXc)).
  assert (Hkc0 : 0 <= kc) by (unfold kc, KU; lia).
  assert (HBXn : BXok_d d BXn).
  { pose proof (apot_range (AHead (SVar h0) pot) rho1) as [R1 R2]. fold P in R1, R2. pose proof (BXok_d_pair _ BXc HBX) as [HX1 HX2].
    apply (BXok_d_mono0 d BXc); [exact HBX | reflexivity | unfold BXn, bxV, bxa; cbn [bx2 fst snd]; lia | unfold BXn, bxK, bxa; cbn [bx2 fst snd]; lia | reflexivity]. }
  apply (TR_post _ (LQPA segs NPc rho1 tp1 (PostsC AInv CST XGL Kc P0c PAc PD FBn FFc BXn))); [|apply SUMT; exact HBXn].
  intros [tr [ms md]] (L & JL & rhoL & tpL & HinL & Hag & HsmL & HJL).
  unfold PostsC in HinL. apply in_map_iff in HinL as ([Ld ndL] & Heq & Hd). cbn [fst snd] in Heq. injection Heq as HL HJLe. subst L JL.
  exists Ld, (JLA AInv CST XGL Kc (P0c FBc FFc) FBc FFc BXc PAc (ndh ndL)), rhoL, tpL.
  split; [unfold PostsC, PDh; rewrite map_map; apply in_map_iff; exists (Ld, ndL); split; [reflexivity | exact Hd]|].
  split; [exact Hag|]. split; [exact HsmL|].
  pose proof (proj1 (Forall_forall _ _) HamPD _ Hd) as HamL. cbn [snd] in HamL.
  cbn [w_tr w_cfg cfg_model] in HJL |- *.
  destruct HJL as (Hk & A' & kc' & HM' & HT' & HB' & HFF' & (HN' & HD' & HZ') & HFR' & HK' & HP0' & HXA' & HBU' & HPA').
  cbn [nd_tv nd_fr nd_bd nd_am ndh] in HN', HD', HZ', HFR', HXA', HBU' |- *. rewrite HamL in HXA', HBU'.
  unfold XA in HXA'. cbn [am_eval] in HXA'. destruct HXA' as [HXA' HCEN']. cbn [XAz0] in HXA'. cbn [amblkZ] in HCEN'. subst kc'.
  assert (SUB : forall bn, In bn FBc -> In bn FBn) by (intros bn Hbn; unfold FBn; apply in_or_app; left; exact Hbn).
  assert (INn : forall bc, In bc ns -> In (nblk bc) FBn) by (intros bc Hbc; unfold FBn; apply in_or_app; right; apply in_map; exact Hbc).

  destruct HC as [HA [HF HND]].
  assert (GEO : forall b c, In (b, c) ns -> 4096 <= b /\ b + (HDR + c) + 2048 <= 2 ^ 47 /\ 0 <= c).
  { intros b c Hin. destruct (proj1 (Forall_forall _ _) HF _ Hin) as (N1 & _ & _ & N4 & _). cbn [fst snd] in N1, N4.
    destruct (law_blocks _ _ _ ALA Ai rho1 tp0 md0 HM0) as (_ & HBl & _). destruct (HBl b (HDR + c) N1) as (_ & _ & G3 & G4 & _).
    pose proof (topG_range (aa_geom Ai)). lia. }

  destruct HK' as [K1 K2].
  assert (KEPT : forall z, node_addr ns z -> rm rhoL (Z_to_bv 64 z) = rm rho1 (Z_to_bv 64 z)).
  { intros z (b & c & Hin & Hz). destruct (GEO b c Hin) as (G1 & G2 & G3). unfold HDR in *.
    apply K1; [lia|]. left. right; right; left. exists b, (HDR + c). split; [apply INn in Hin; exact Hin | unfold HDR; lia]. }
  assert (KEPTS : forall b c a, In (b, c) ns -> b <= a < b + (HDR + c) ->
            (rm rho1 (shadow_addr SHADOW_OFF a) <> None -> rm rhoL (shadow_addr SHADOW_OFF a) = rm rho1 (shadow_addr SHADOW_OFF a))
            /\ forall j, 0 <= j < 8 -> rm rho1 (word_byte (SHADOW_OFF + a / 8) j) <> None -> rm rhoL (word_byte (SHADOW_OFF + a / 8) j) <> None).
  { intros b c a Hin Ha. destruct (GEO b c Hin) as (G1 & G2 & G3). unfold HDR in *.
    assert (HSa : pclSA CST XGL rho1 FBn FFc (Sh a)).
    { exists a. split; [lia|]. split; [|reflexivity]. left. right; right; left. exists b, (HDR + c). split; [apply INn in Hin; exact Hin | unfold HDR; lia]. }
    assert (HSr : 0 <= Sh a < 2 ^ 64) by (unfold Sh, SHADOW_OFF; split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia | lia] | apply (Z.le_lt_trans _ (a + SHADOW_OFF)); [unfold SHADOW_OFF; apply Z.add_le_mono_r; apply Z.div_le_upper_bound; lia | unfold SHADOW_OFF; lia]]).
    split.
    - unfold shadow_addr. replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia). intros Hdf. apply K1; [exact HSr | right; exact (conj HSa Hdf)].
    - intros j Hj Hdef. replace (SHADOW_OFF + a / 8) with (Sh a) in Hdef |- * by (unfold Sh; lia). apply (K2 (Sh a) j HSr HSa Hj Hdef). }
  split; [exact Hk|]. exists A', kc.
  split; [exact HM'|]. split; [exact HT'|]. split; [intros bn Hbn; apply HB'; apply SUB; exact Hbn|]. split; [exact HFF'|]. split.
  { split; [|split; [exact HD' | exact HZ']]. unfold tvinA in HN' |- *. apply Forall_forall. intros t Ht Hnz.
    destruct (proj1 (Forall_forall _ _) HN' t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [exact X1|]. intros Hin. exact (X2 (SUB _ Hin)). }
  split; [exact HFR'|]. split; [apply (keptFA_mono _ FBc FBn); [exact SUB | split; [exact K1 | exact K2]]|]. split; [exact HP0|].
  assert (Eh : uval rhoL (SVar h0) = h).
  { unfold h, uval. cbn [eval]. rewrite <- (proj1 Hag h0 Hh0). reflexivity. }
  split.
  -
    assert (HA' : achain (rm rhoL) h ns).
    { apply (achain_frame (rm rho1)); [exact HA | |].
      * intros z Hz. apply KEPT. exact (hdr_node_addr _ _ _ _ HA Hz).
      * intros z Hz Hdef. rewrite (KEPT z Hz). exact Hdef. }
    unfold XA. cbn [nd_am nd_tv ndh am_eval]. rewrite Eh. split.
    2: {
         intros bn L1 L2 L3 L4. cbn [amblkZ].
         destruct (in_dec ZZ_eq_dec bn (map nblk ns)) as [Hc|Hc]; [exists ns; split; [exact HA' | exact Hc]|].
         exfalso. apply (HCEN' bn L1 L2); [|exact L4]. unfold FBn. intros Hf. apply in_app_or in Hf as [Hf|Hf]; [exact (L3 Hf) | exact (Hc Hf)]. }
    cbn -[chainZ KU]. exists ns. split; [|reflexivity]. split; [|split; [|exact HND]].
    + exact HA'.
    + apply Forall_forall. intros [b c] Hbc. destruct (proj1 (Forall_forall _ _) HF _ Hbc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6). cbn [fst snd] in *.
      split; [apply HB'; apply (INn (b, c)); exact Hbc|]. split; [exact Y2|]. split.
      { intros v Hv Hvz Heq. unfold tvals in Hv. apply in_map_iff in Hv as (t & <- & Ht).
        destruct (proj1 (Forall_forall _ _) HN' t Ht ltac:(exact Hvz)) as (_ & _ & X2). apply X2. rewrite Heq. apply (INn (b, c)). exact Hbc. }
      split; [exact Y4|]. split; [exact Y5|].
      apply (xmemA_frame (rm rho1)); [exact Y6 | |].
      * intros a Ha. exact (proj1 (KEPTS b c a Hbc Ha)).
      * intros a j Ha Hj Hdef. exact (proj2 (KEPTS b c a Hbc Ha) j Hj Hdef).
  - split; [|exact HPA'].

    cbn [nd_am nd_bd ndh].
    assert (EP : apot (AHead (SVar h0) pot) rhoL = P).
    { unfold P, apot. cbn [am_eval apotz]. rewrite Eh. fold h. destruct pot; [|reflexivity].
      unfold areq. destruct (Z.eqb_spec h 0) as [E0|NE]; [reflexivity|].
      destruct (achain_cons _ _ _ HA NE) as (c & r & Ens).
      assert (Hin : In (h, c) ns) by (rewrite Ens; left; reflexivity).
      rewrite (rd64_ext (rm rho1) (rm rhoL)); [reflexivity|]. intros z Hz. apply KEPT. exists h, c. split; [exact Hin|].
      destruct (GEO h c Hin) as (_ & _ & G3). unfold HDR. lia. }
    rewrite EP. unfold apot in HBU'. cbn [am_eval apotz] in HBU'.
    apply (BUD_bx_ext _ (bxa (bx2 BXn) (0, 0) 0)); [unfold BXn, bxa; cbn; lia | unfold BXn, bxa; cbn; lia | exact HBU'].
Qed.
End T.

Theorem JA_frame_sum {d : Z} : ltac2:(tb__ "0|6|
SaOF_;S1S2S0S0A2M0A1M1S1S2G0S0A2A1M2S12S7S1SeQ40A1A1M3S13Vd;R3A2M4ScVsegs;R7SfVsegs;S16VAInv;VCST;VXGL;VKc;VP0c;R6R5A2M5R6R5R4VPAc;VndC;AaVPreC;R3R2A5S11Vsegs;VNPc;R3R2S23VAInv;VCST;VXGL;VKc;VP0c;VPAc;VPD;R6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;G1G2S12S7G3G4ScVsegs;R8SfVsegs;S16VAInv;VCST;VXGL;VKc;G5R6R5R4VPAc;S24VndC;A1AaVPreC;R3R2A5S11Vsegs;VNPc;R3R2S23VAInv;VCST;VXGL;VKc;VP0c;VPAc;S25R6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;F_;Fok;").
Proof using ALA HamC HamPD Hh0 P0mono.
  intros ok SUM. apply (JA_frame_sumT (triple segs ok)).
  - intros P P' Q HP H. eapply triple_conseq; [exact HP | intros w Hw; exact Hw | exact H].
  - intros P Q Q' HQ H. eapply triple_conseq; [intros w Hw; exact Hw | exact HQ | exact H].
  - intros A P Q H. apply triple_ex. exact H.
  - intros X P Q H. apply triple_pure. exact H.
  - exact SUM.
Qed.
Theorem JA_frame_sum_ex {d : Z} : ltac2:(tb__ "0|6|
S1S2S0S0A2M0A1M1S1S2G0S0A2A1M2S12S7S1SeQ40A1A1M3S13Vd;R3A2M4SbVsegs;SfVsegs;S16VAInv;VCST;VXGL;VKc;VP0c;R6R5A2M5R6R5R4VPAc;VndC;AaVPreC;R3R2A5S11Vsegs;VNPc;R3R2S23VAInv;VCST;VXGL;VKc;VP0c;VPAc;VPD;R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;G1G2S12S7G3G4SbVsegs;SfVsegs;S16VAInv;VCST;VXGL;VKc;G5R6R5R4VPAc;S24VndC;A1AaVPreC;R3R2A5S11Vsegs;VNPc;R3R2S23VAInv;VCST;VXGL;VKc;VP0c;VPAc;S25R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;F_;").
Proof using ALA HamC HamPD Hh0 P0mono.
  intros SUM. apply (JA_frame_sumT (etriple segs)).
  - intros P P' Q HP H. eapply etriple_conseq; [exact HP | intros w Hw; exact Hw | exact H].
  - intros P Q Q' HQ H. eapply etriple_conseq; [intros w Hw; exact Hw | exact HQ | exact H].
  - intros A P Q H. apply etriple_ex. exact H.
  - intros X P Q H w [HX HP]. exact (H HX w HP).
  - exact SUM.
Qed.
End WithSegs.
End TobjJAH.

(* [comment removed for export] *)
Module ObjZeroA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sstate"; "cell"; "valuation"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "odefault"; "SLit"; "obj_holds"; "smatch"; "swf"; "DZero"; "c_off"; "c_val"; "c_width"; "mkObj"; "ob_cells"; "ss_objs"; "tfact"; "@Corelib.Init.Datatypes"; "list"; "bool"; "option"; "Some"; "andb"; "false"; "prod"; "true"; "None"; "nat"; "S"; "app"; "cons"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA"; "small63"; "zero_cells_obj"; "zero_cells_at"; "zero_cell_ok"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "ltb"; "add"; "opp"; "pow"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "firstn"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "xrs_inclb"; "@Stdlib.Lists.List"; "forallb"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymObj SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition small63 (z : Z) : bool := ltac2:(tb__ "0|1|
S1aS2eS31S32Z2Z3fA2M0A1Vz;A2S2fVz;G0A2A2").
Definition zero_cell_ok (lo hi : Z) (c : cell) : bool := ltac2:(tb__ "0|9|
S0S17Lx;M0SfVc;A1S25G0S10Vc;A1S25S25S17Lz;R1S1aS1aS1aS2eVlo;R2A2S2eS30R2S11Vc;A1M1A2Vhi;A2A2S2fZ0G1A2A2S2aR2A1A2S26S1bLp;M2G2X25x3Lz;S26S1bLi;M3S33S0S0S1bLb;La;M4Lop;M5G5S34G4Lop;M6G6S17S27S0S1bLa;Lw;Lsgn;M7S26S0S25S1bLk;Li;Ll;M8X0x8Loff;G3G5G5G6G6G7G8X0x8").

Definition zero_cells_obj (o : sobj) (cs : list cell) : option sobj := ltac2:(tb__ "0|b|
S0S18S1A1M0Lx;M1S8Vo;A1S25G1S7Vo;A1S25S9G0Lx;S6Vo;A1S1eS1A1M2S16S3A1M3G0Lx;S13Vo;A1S17G0L_;S1aS1aS43S3S2dR2R1A2Vcs;A3S2aR2A1A2S2aR1A1A2S19S1S12S5Vo;A1SaR2A1SaR1A1Vcs;SeA5A2G2X17x2S3G3G2Ll;Lc;X16x2G2S26G2Ll;M4G4S25S0S16S1cS25S25A2A1S16S15A1G2Ltmpl;Lflds;Lcnt;Lesz;X9x6Lhi;S26G2Li;M5S33S0S0G2Lb;La;M6Lop;M7G7S34G6Lop;M8G8S17S27S0G2La;Lw;Lsgn;M9S26S0S25G2Lk;Li;Ll;MaX0x8Llo;G5G7G7G8G8G9GaX0x8").

Definition zero_cells_at (S : sstate) (i : nat) (cs : list cell) : option sstate := ltac2:(tb__ "0|3|
S18S1A1S18S2A1Lx;M0S44S1S14VS;A1M1Vi;A3S1G0S2bR1Vcs;A2S1S19S2S40VS;S21S1S3bS1Vi;G1A3S22S1R1S3cS1S20Vi;A1G1A3A3A3A2A2Lo';S1eS2A1M2X18x2Lo;G2X18x2").

Section WithSegs.
Variable segs : list Segment.

Lemma zero_cells_obj_holds : ltac2:(tb__ "0|0|
S4S3dS1S16S3A1S1S23S18S1A1S2bR3R2A2S19S1R1A2A3SbVsegs;R6R5R4A4SbVsegs;R7R6R3A4F_;F_;Fo';Fcs;Fo;Fms;Frho;").
Proof using .
  intros rho ms o cs o' Hz Hoh.
  unfold zero_cells_obj in Hz.
  destruct (ob_lo o) as [lo| | | | | | |] eqn:Elo; try discriminate.
  destruct (ob_hi o) as [hi| | | | | | |] eqn:Ehi; try discriminate.
  destruct (ob_dflt o) eqn:Ed; try discriminate.
  destruct (ob_cells o) as [|c0 r0] eqn:Ec; try discriminate.
  destruct (forallb (zero_cell_ok lo hi) cs && small63 lo && small63 hi) eqn:Hall0; [|discriminate]. injection Hz as <-.
  apply andb_prop in Hall0 as [Hall0 Shi]. apply andb_prop in Hall0 as [Hall Slo].
  unfold small63 in Slo, Shi. apply andb_prop in Slo as [Slo1 Slo2]. apply andb_prop in Shi as [Shi1 Shi2].
  apply Z.leb_le in Slo1. apply Z.ltb_lt in Slo2. apply Z.leb_le in Shi1. apply Z.ltb_lt in Shi2.
  pose proof Hoh as (Hrg & Hwr & Hcells & Hd & Hinv).
  assert (Elo' : obj_lo_of rho o = lo) by (unfold obj_lo_of; rewrite Elo; apply soff_lit_small; lia).
  assert (Ehi' : obj_hi_of rho o = hi) by (unfold obj_hi_of; rewrite Ehi; apply soff_lit_small; lia).
  assert (Elo2 : soff rho (SLit lo) = lo) by (apply soff_lit_small; lia).
  assert (Ehi2 : soff rho (SLit hi) = hi) by (apply soff_lit_small; lia).
  unfold obj_holds. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. unfold obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite Elo2, Ehi2.
  rewrite Elo', Ehi' in Hrg, Hwr, Hd. rewrite Ed in Hwr, Hd. rewrite Ec in Hd.
  split; [exact Hrg|]. split; [exact Hwr|]. split; [|split; [|exact I]].
  - apply Forall_forall. intros c Hin.
    pose proof (proj1 (forallb_forall _ _) Hall c Hin) as Hc. unfold zero_cell_ok in Hc.
    destruct (c_off c) as [off| | | | | | |] eqn:Eoff; try discriminate.
    destruct (c_val c) as [v| | | | | | |] eqn:Ev; try discriminate. destruct v; try discriminate.
    apply andb_prop in Hc as [Hc Hs]. apply andb_prop in Hc as [Hc Hk]. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in Hk.
    unfold small63 in Hs. apply andb_prop in Hs as [Hs1 Hs2]. apply Z.leb_le in Hs1. apply Z.ltb_lt in Hs2.
    assert (Eoff2 : soff rho (SLit off) = off) by (apply soff_lit_small; lia).
    unfold cell_holds. rewrite Eoff, Ev, Eoff2. split; [lia|]. split; [lia|].
    rewrite (obj_read_zero segs rho ms o off (c_width c) Hoh Ed ltac:(rewrite Elo'; lia) ltac:(rewrite Ehi'; lia) Hk).
    + reflexivity.
    + unfold uncovered. intros off' _. rewrite Ec. intros HX. inversion HX.
  - intros off Hoff _. apply Hd; [exact Hoff|]. intros HX. inversion HX.
Qed.

Lemma zero_cells_obj_shape : ltac2:(tb__ "0|0|
S1S16S3A1S1S23S18S1A1S2bR3R2A2S19S1R1A2A3S24S23S0S5R2A1S5R4A1A3S24S23S0S8R2A1S8R4A1A3S24S23S0S7R2A1S7R4A1A3S23S9S6R2A1S6R4A1A3A2A2A2F_;Fo';Fcs;Fo;").
Proof using .
  intros o cs o' Hz. unfold zero_cells_obj in Hz.
  destruct (ob_lo o); try discriminate. destruct (ob_hi o); try discriminate.
  destruct (ob_dflt o); try discriminate. destruct (ob_cells o); try discriminate.
  destruct (forallb _ cs && _ && _); [|discriminate]. injection Hz as <-. cbn. repeat split; reflexivity.
Qed.

Theorem smatch_zero_cells : ltac2:(tb__ "0|0|
S4S2S1fS16S3A1S2S1cS16S3fA1S3eA2S23S18S2A1S2cR5R4R3A3S19S2R2A2A3S23S17SdR3A1S1dA3ScVsegs;R8R7R3A4ScVsegs;R9R5R4A4F_;F_;F_;Fw;FS';Fcs;Fi;FS;Frho;").
Proof using .
  intros rho S i cs S' [tr [ms md]] Hz HwfS' Hsm.
  unfold zero_cells_at in Hz.
  destruct (nth_error (ss_objs S) i) as [o|] eqn:Hn; [|discriminate].
  destruct (zero_cells_obj o cs) as [o'|] eqn:Ho'; [|discriminate]. injection Hz as <-.
  pose proof (zero_cells_obj_shape o cs o' Ho') as (Eb & Elo & Ehi & Ed).
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (nth_error_split3 _ _ _ Hn) as EQ.
  assert (Hoh : obj_holds segs rho ms o).
  { destruct Hmem as (Hall & _ & _). rewrite EQ in Hall. apply Forall_app in Hall as [_ Hall]. inversion Hall; auto. }
  assert (Hrange : obj_range rho o' = obj_range rho o).
  { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, Elo, Ehi. reflexivity. }
  pose proof (zero_cells_obj_holds rho ms o cs o' Ho' Hoh) as Hoh'.
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split; [exact HwfS'|].
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  rewrite EQ in Hmem.
  change (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S)) with (firstn i (ss_objs S) ++ [o'] ++ skipn (Datatypes.S i) (ss_objs S)).
  apply mem_match_replace with (o := o).
  - exact Hmem.
  - constructor; [exact Hoh'|]. constructor.
  - destruct Hmem as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
    rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *. rewrite Hrange. exact Hpd.
  - intros x. split.
    + intros Hx. exists o'. split; [cbn; auto|]. rewrite Hrange. exact Hx.
    + intros (o'' & Hin'' & Hx). destruct Hin'' as [<-|[]]. rewrite Hrange in Hx. exact Hx.
Qed.

Lemma SPA_zero_cells : ltac2:(tb__ "0|0|
S29S4S36S1fS16S3A1S2S16S3aQ40A1A1S35S23S18S2A1S2cS37R6A1R5R4A3S19S2R3A2A3S23S17SdR4A1S1dA3S28Vsegs;RaR8R9R4R3A6S28Vsegs;RbS39R9R6A2RaR5R4A6F_;F_;F_;Fw;Ftp;FS';Fcs;Fi;FA;Frho;FJ;").
Proof using .
  intros J rho A i cs S' tp [tr [ms md]] Hz HwfS' [(Hsm & HMI & Hwf' & Hsh & Hhz) Hk]. split; [|exact Hk].
  pose proof (smatch_zero_cells rho (ax_S A) i cs S' _ Hz HwfS' Hsm) as Hsm'.
  unfold zero_cells_at in Hz.
  destruct (nth_error (ss_objs (ax_S A)) i) as [o|] eqn:Hn; [|discriminate].
  destruct (zero_cells_obj o cs) as [o'|] eqn:Ho'; [|discriminate]. injection Hz as E'.
  pose proof (zero_cells_obj_shape o cs o' Ho') as (Eb & Elo & Ehi & Ed).
  assert (Hin_o : In o (ss_objs (ax_S A))) by (eapply nth_error_In; exact Hn).
  split; [exact Hsm'|]. split; [exact HMI|].
  assert (EN : ss_next S' = ss_next (ax_S A)) by (rewrite <- E'; reflexivity).
  split; [unfold axwf in Hwf' |- *; cbn [ax_S ax_X ax_base ax_setS] in Hwf' |- *; rewrite EN; exact Hwf'|].
  split; [|exact Hhz].
  apply shadow_ok_reobjs; [exact Hsh|]. apply xshadow_outside_cover; [exact Hsh|].
  rewrite <- E'. cbn [set_objs ss_objs]. intros o2 x Ho2 Hx. apply in_app_or in Ho2 as [Ho2|[<-|Ho2]].
  - exists o2. split; [eapply In_firstn_In; exact Ho2 | exact Hx].
  - exists o. split; [exact Hin_o|]. unfold obj_range, obj_lo_of, obj_hi_of in Hx |- *. rewrite Eb, Elo, Ehi in Hx. exact Hx.
  - exists o2. split; [eapply In_skipn_In; exact Ho2 | exact Hx].
Qed.

End WithSegs.

Section XIncl.
Variable segs : list Segment.
Lemma SPA_x_incl : ltac2:(tb__ "0|0|
S29S4S36S16S1cS0S0A2A1S16S3aQ40A1A1S35S23S17S42R3S38R4A1A2S1dA3S28Vsegs;R7R5R6R3R2A6S28Vsegs;R8S41R6R5A2R7R4R3A6F_;F_;Fw;Ftp;FX';FA;Frho;FJ;").
Proof using .
  intros J rho A X' tp [tr [ms md]] Hincl [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.xrs_inclb_sound X' (ax_X A) Hincl) as HIn.
  split; [exact Hsm|]. split; [exact HMI|].
  split.
  { unfold axwf in Hwf |- *. cbn [ax_S ax_X ax_base ax_setX] in Hwf |- *. apply andb_prop in Hwf as [HX Hb]. rewrite Hb.
    rewrite andb_true_r. apply forallb_forall. intros r Hr. exact (proj1 (forallb_forall _ _) HX r (HIn r Hr)). }
  split; [|exact Hhz].
  unfold shadow_ok in Hsh |- *. cbn [ax_X ax_setX ax_S ax_base]. apply Forall_forall. intros r Hr.
  exact (proj1 (Forall_forall _ _) Hsh r (HIn r Hr)).
Qed.
End XIncl.
End ObjZeroA.

(* [comment removed for export] *)
Module CertGlueA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "SMd"; "SLit"; "holds"; "sprop"; "eval"; "DUnknown"; "SAlu"; "SPUle"; "SPUlt"; "cell"; "mkObj"; "obj_range"; "soff"; "sprop_eqb"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "add"; "pow"; "mul"; "opp"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "iff"; "not"; "@Corelib.Init.Datatypes"; "prod"; "list"; "pair"; "bool"; "fst"; "nil"; "option"; "snd"; "true"; "@LinuxProcessSemantics.Riscv.Instr"; "M_MUL"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ffinA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "pclMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "cmaddrA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Stdlib.Lists.List"; "In"; "existsb"; "@stdpp.bitvector.definitions"; "bv"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma uval_lit : ltac2:(tb__ "0|0|
S3S0S18S13Z0R1A2S12R1S15Z2Z40A2A2A2S19S0S1R3S5R2A1A2R2A3F_;Fc;Frho;").
Proof. intros rho c Hc. unfold uval. rewrite U_lit. unfold M64v. apply Z.mod_small. lia. Qed.
Lemma uval_mul_small : ltac2:(tb__ "0|0|
S3S2S2S12S16S1R3R2A2S1R3R1A2A2S15Z2Z40A2A2S19S0S1R4S4S26R3R2A3A2S16S1R4R3A2S1R4R2A2A2A3F_;Fb;Fa;Frho;").
Proof.
  intros rho a b H. unfold uval in *. rewrite U_mul. unfold M64v. apply Z.mod_small.
  pose proof (U_range (eval rho a)). pose proof (U_range (eval rho b)). unfold M64v in *. nia.
Qed.
Lemma uval_mul_lit : ltac2:(tb__ "0|1|
S3S0S2S18S13Z0R2A2S12R2S15Z2Z40A2M0A2A2S12S16R3S1R4R2A2A2G0A2S19S0S1R5S4S26S5R4A1R3A3A2S16R4S1R5R3A2A2A3F_;F_;Fb;Fc;Frho;").
Proof.
  intros rho c b Hc H. pose proof (uval_range rho b).
  rewrite uval_mul_small; rewrite uval_lit by lia; [reflexivity | exact H].
Qed.
Lemma uval_mul_comm : ltac2:(tb__ "0|0|
S3S2S2S19S0S1R3S4S26R2R1A3A2S1R3S4S26R1R2A3A2A3Fb;Fa;Frho;").
Proof. intros. unfold uval. rewrite !U_mul. f_equal. lia. Qed.
Lemma eval_mul_comm : ltac2:(tb__ "0|0|
S3S2S2S19S35Q40A1S8R3S4S26R2R1A3A2S8R3S4S26R1R2A3A2A3Fb;Fa;Frho;").
Proof. intros. apply bv_eq. pose proof (uval_mul_comm rho a b). unfold uval in H. lia. Qed.
Lemma uval_add_small : ltac2:(tb__ "0|0|
S3S2S2S12S14S1R3R2A2S1R3R1A2A2S15Z2Z40A2A2S19S0S1R4SaS27R3R2A3A2S14S1R4R3A2S1R4R2A2A2A3F_;Fb;Fa;Frho;").
Proof.
  intros rho a b H. unfold uval in *. rewrite U_add. unfold M64v. apply Z.mod_small.
  pose proof (U_range (eval rho a)). pose proof (U_range (eval rho b)). unfold M64v in *. lia.
Qed.

Lemma h_ule : ltac2:(tb__ "0|0|
S3S2S2S1bS6R3SbR2R1A2A2S13S1R3R2A2S1R3R1A2A2A2Fb;Fa;Frho;").
Proof. intros. cbn [holds]. unfold uval. tauto. Qed.
Lemma h_ult : ltac2:(tb__ "0|0|
S3S2S2S1bS6R3ScR2R1A2A2S12S1R3R2A2S1R3R1A2A2A2Fb;Fa;Frho;").
Proof. intros. cbn [holds]. unfold uval. tauto. Qed.
Lemma holds_mem : ltac2:(tb__ "0|0|
S3S1eS7A1S7S2dS7S6R3A1R2A3S19S20S34S7S11R2A1R3A3S25A3S6R5R3A2F_;F_;Ff;Ffacts;Frho;").
Proof.
  intros rho facts f HF H. apply existsb_exists in H as (g & Hg & E). apply sprop_eqb_sound in E. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hg).
Qed.

Tactic Notation "fact" constr(HF) constr(f) ident(H) := assert (H : holds _ f) by (apply (holds_mem _ _ f HF); vm_compute; reflexivity).

Ltac zf H := first
  [ apply (proj1 (holds_ule _ _ _)) in H | apply (proj1 (holds_ult _ _ _)) in H
  | apply (proj1 (holds_bltu _ _ _)) in H | apply (proj1 (holds_nbltu _ _ _)) in H
  | apply (proj1 (holds_bgeu _ _ _)) in H | apply (proj1 (holds_nbgeu _ _ _)) in H
  | apply (proj1 (holds_beq _ _ _)) in H | apply (proj1 (holds_nbeq _ _ _)) in H
  | apply (proj1 (holds_bne _ _ _)) in H | apply (proj1 (holds_nbne _ _ _)) in H ];
  change (bv_unsigned (eval ?r ?e)) with (uval r e) in H.
Tactic Notation "factz" constr(HF) constr(f) ident(H) := fact HF f H; zf H; repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in H.

Lemma aceil_val : aceil = 140735332483072. Proof. reflexivity. Qed.

Lemma range_lit' : ltac2:(tb__ "0|4|
S3S2S0S0S1eSdA1S0S18S13S17S15Z2Z3fA2M0A1R4A2S12R4G0A2A2M1G1S18S13S21S0S0SfR8SeR7S5R6A1S5R5A1R4S9A5A2M2A3R3A2S12R3S24S0S0G2A3A2A2S18S13S14S1R9R8A2M3R7A2R4A2S12R4S14G3R6A2A2A2F_;F_;F_;Fa;Fcells;Fhi;Flo;Fb;Frho;").
Proof.
  intros rho b lo hi cells a H1 H2 Hr. unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite (soff_lit_small rho lo H1), (soff_lit_small rho hi H2) in Hr. unfold uval. lia.
Qed.
Lemma soff_smallu : ltac2:(tb__ "0|0|
S3S2S12S1R2R1A2S15Z2Z3fA2A2S19S0S10R3R2A2S1R3R2A2A3F_;Fe;Frho;").
Proof.
  intros rho e H. rewrite soff_snorm. unfold U, uval in *. pose proof (urange (eval rho e)). apply snorm_small. lia.
Qed.

Definition infrFF (FF : list (Z * Z * Z)) (x n : Z) : Prop := ltac2:(tb__ "0|1|
S1aS0S0S1aS0S0S1aS0S0S18S33S1dS1dS0S0A2M0S0A2S1fG0S0S1fS0S0R3R2A4R1A4VFF;A3S18S13R3Vx;A2S13S14Vx;Vn;A2S14R3R2A2A2A2A2Lfl;A2Ls;A2Lf;A2").
Lemma infrFF_cmaddrA : ltac2:(tb__ "0|1|
S1eS1dS0S0A2M0A1S1eS1dG0S0A2A1S32S0S0S23S0A1S0S2eR6R5A2S2cR7R5R4A3S18S13R6R3A2S12R3S14R6R5A2A2A2S31RaR8R5R4A4F_;F_;F_;Fa;Fxo;Fn;Fx;FAi;FFF;FCST;").
Proof.
  intros CST FF Ai x n xo a HFF (f & s & fl & Hin & H1 & H2) Ha. right; right; right. exists f, s. split; [exact (proj1 (HFF _ _ _ Hin)) | lia].
Qed.
Lemma infrFF_pclMA : ltac2:(tb__ "0|2|
S1eS1dS0S0A2M0A1M1S3S1eS1dG0S0A2A1G1S3S0S0S0S2cR6R3R2A3S18S13R4R2A2S12R2S14R4R3A2A2A2S30RaR9R7S2fR8R6S22S1dS1dS2S0A2S2A2A1A3R3A5F_;F_;Fa;Fn;Fx;Frho;FFBc;FFF;Frho0;FCST;").
Proof.
  intros CST rho0 FF FBc rho x n a (f & sz & fl & Hin & H1 & H2) Ha. right; right; right. exists f, sz, fl.
  split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin | lia].
Qed.

Section WithSegs.
Variable segs : list Segment.
Lemma TRs_false : ltac2:(tb__ "0|0|
S28OF_;S29S29S28S1cR3R1A1A1Fw;S2bVsegs;R4R3R2A4F_;FQ;FP;Fok;").
Proof using . clear. intros ok P Q H n _ w Hw. destruct (H w Hw). Qed.
Lemma TRe_false : ltac2:(tb__ "0|0|
S29S28OF_;S28S1cR3R1A1A1Fw;S2aVsegs;R3R2A3F_;FQ;FP;").
Proof using . clear. intros P Q H w Hw. destruct (H w Hw). Qed.
End WithSegs.
End CertGlueA.

