(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "enodeA"; "ena_state"; "edgeA"; "ena_meas"; "ena_pred"; "jnodeA"; "cfg_edgesA"; "edge_okA"; "eedge_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "SPA"; "stableA"; "ok_frameA"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "Some"; "app"; "nat"; "option"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "agree_below"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@Corelib.Init.Logic"; "ex"; "and"; "or"; "eq"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA.G"; "SPfamETA"; "SPfamGTA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith Zwf Wellfounded.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CompleteA CFGA.
Import ListNotations.
Open Scope Z_scope.

Section G.
Variable segs : list Segment.

Definition SPfamGTA (nodes : list jnodeA) : assn := ltac2:(tb__ "0|1|
S1bS1fS0S0S1fSbSbS1fS17S17S1fSfS23Q40A1A1M0G0S20S1aS11S0SbA2S10S0SbR4R3A4Vnodes;A3ScVsegs;R3R4R2R1R5A6A2Ltp;A2Lrho;A2LJ;A2LT;A2Lw;").

Theorem cfg_sound_genTA : ltac2:(tb__ "0|8|
S14SfS26A1S27SfS7A1M0G0SfS4A1M1S1bOF_;S1eS0SbS1aS11S0SbA2M2S10S0SbR2R1A4M3R7A3SeVsegs;R5R2A3F_;FJ;FT;S0SbS1aG2G3R8A3SdVsegs;S18S1R3A1A1R2A3F_;FJ;FT;S22S15G1A1S8Vsegs;RaR9R8S24G2S0S16S0SbA2M4R7A4S24G2S0G4R6A4A6S12G1R5A2A3S25S4S9S13S7R8R7A3A1R6A3S0SbS17SfS23Q40A1A1M5S1aG2S10S0SbR4R3A4M6RcA3S1dVsegs;RbScVsegs;R4R5R3R2A5M7S1bS21S29RfR1A2RbR1A1A2Lw;A4F_;Ftp;Frho;FJE;FE;S0SbS17G5S1aG2G6ReA3S1dVsegs;RcG7RbA4F_;Ftp;Frho;FJ;FT;F_;F_;F_;F_;F_;FQ;Fok;Fes;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits es ok Q Hok Hst Hes Hedges Hexits T J rho tp HinT.
  assert (Hloop : triple segs ok (SPfamGTA cuts) Q).
  { apply triple_loop.
    unfold SPfamGTA at 1. apply triple1_ex; intros T'. apply triple1_ex; intros J'. apply triple1_ex; intros rho'. apply triple1_ex; intros tp'.
    apply triple1_pure; intros HinT'.
    destruct (In_nth_error _ _ HinT') as [k Hk].
    assert (HkT : nth_error (map fst cuts) k = Some T') by (rewrite nth_error_map, Hk; reflexivity).
    unfold cfg_edgesA in Hes.
    destruct (cuts_edgesA_spec segs fuel cutpcs g (map fst cuts) 0 (map fst cuts ++ map fst exits) es Hes k T' HkT)
      as (Hle & Hlen & Hwf & leaves & Hrun & HL).
    eapply triple1_seq_l.
    { eapply (sym_run_soundA segs fuel cutpcs T' leaves ok J' rho' tp' Hrun); [exact (Hok T' J' HinT') | exact Hlen | exact (Hst T' J' HinT')]. }
    intros m Hgm w Hw. destruct Hw as (L & rho'' & HinL & Hag & Hsm & Hkk).
    destruct (HL L HinL) as [Hr|(j & s & X & HinE & HnX & Hid & Hent)].
    { exfalso. eapply (leaf_refuted_sound rho''); [exact Hr|]. eapply smatchA_facts; exact Hsm. }
    rewrite Nat.add_0_l in HinE.
    pose proof (proj1 (Forall_forall _ _) Hedges _ HinE) as EOK. unfold edge_okA in EOK. cbn [ea_src ea_tgt ea_leaf ea_sub] in EOK.
    rewrite <- map_app in HnX. rewrite nth_error_map in HnX. unfold jnodeA in *.
    destruct (nth_error (cuts ++ exits) j) as [[Xs JX]|] eqn:HnXG; cbn in HnX; [|discriminate].
    injection HnX as ->.
    destruct w as [tr [ms md]]. cbn [w_tr w_cfg fst snd cfg_model] in Hkk.
    assert (HJX : JX (rho_sub rho'' s) tp' tr md).
    { eapply (EOK (T', J') (X, JX)); [| reflexivity | apply agree_below_refl | exact Hkk |].
      - rewrite nth_error_app1; [exact Hk|]. apply nth_error_Some. congruence.
      - eapply smatchA_facts; exact Hsm. }
    assert (HSPX : SPA segs JX X (rho_sub rho'' s) tp' (tr, mkCfg ms md)).
    { split; [eapply smatchA_entails; eauto | exact HJX]. }
    destruct (Nat.lt_ge_cases j (length cuts)) as [Hj|Hj].
    - apply Hgm. left. exists X, JX, (rho_sub rho'' s), tp'. split; [|exact HSPX].
      rewrite nth_error_app1 in HnXG by exact Hj. eapply nth_error_In; eauto.
    - rewrite nth_error_app2 in HnXG by exact Hj.
      exact (Hexits X JX (rho_sub rho'' s) tp' (nth_error_In _ _ HnXG) m Hgm _ HSPX). }
  eapply triple_conseq; [| intros w Hw; exact Hw | exact Hloop].
  intros w Hw. exists T, J, rho, tp. auto.
Qed.

Lemma reenter_cutGTA : ltac2:(tb__ "0|0|
S1bOF_;SfS7A1S0SbS1eS17SfS23Q40A1A1S1aS11S0SbA2S10S0SbR5R4A4R6A3S1dVsegs;R8ScVsegs;R5R6R3R2A5S1bS21S29R8R1A2R5R1A1A2Lw;A4F_;Ftp;Frho;FQ;FJ;FT;Fcuts;Fok;").
Proof using .
  intros ok cuts T J Q rho tp Hin.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hw. left. exists T, J, rho, tp. split; [exact Hin | exact Hw].
Qed.

Definition SPfamETA (nodes : list enodeA) (bound : Z) : world -> Prop := ltac2:(tb__ "0|2|
S1bS1fS2S2S1fS17S17S1fSfS23Q40A1A1M0G0S20S1aS2R3Vnodes;A3S20ScVsegs;S6R3A1S3R3A1R2R1R4A6S20S2aZ0S5R3R2A2M1A2S2bG1Vbound;A2A2A2A2Ltp;A2Lrho;A2Ln;A2Lw;").

Theorem cfg_complete_genTA : ltac2:(tb__ "0|6|
S14SfS26A1S27SfS2A1M0G0SfS4A1M1S1bOF_;S2S1aS2R1R5A3SdVsegs;S18S1S3R2A1A1A1S6R2A1A3F_;Fn;S2S17S17S1aS2R3R8A3S19S18S1S3R4A1M2A1A1R3R2A3S22S26S5R5R3A2S5R5R4A2M3A3F_;F_;Frho';Frho;Fn;S22S15G1A1S8Vsegs;R9R8R7S24S2S0S3R6A4S24S2S0S3R5A4A6S12G1R4A2A3S25S4SaS13S2R7R6A3A1R5A3S2S17SfS23Q40A1A1M4S1aS2R3RaA3S1cVsegs;ScVsegs;S6R4A1G2R3R2A5M5S1bS21S28RdG3R1A3RaR1A1A2Lw;A3F_;Ftp;Frho;FE;S2S17G4S1aS2R3RcA3S1cVsegs;G5RaA3F_;Ftp;Frho;Fn;F_;F_;F_;F_;F_;FQ;Fes;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof using .
  intros fuel cutpcs g cuts exits es Q Hst Hms Hes Hedges Hexits n rho tp Hin.
  set (I := fun (a : Z) (w : world) =>
              exists n rho tp, In n (cuts ++ exits) /\ SPA segs (ena_pred n) (ena_state n) rho tp w /\ ena_meas n rho = a /\ 0 <= a).
  assert (ROUND : forall n0 rho0 tp0 w, In n0 cuts -> SPA segs (ena_pred n0) (ena_state n0) rho0 tp0 w ->
            exists w' nj rhoj, wsteps segs w w' /\ In nj (cuts ++ exits)
              /\ SPA segs (ena_pred nj) (ena_state nj) rhoj tp0 w'
              /\ 0 <= ena_meas nj rhoj < ena_meas n0 rho0).
  { intros n0 rho0 tp0 w Hcut Hsp0.
    destruct (In_nth_error _ _ Hcut) as [k Hk].
    assert (HkT : nth_error (map ena_state cuts) k = Some (ena_state n0)) by (rewrite nth_error_map, Hk; reflexivity).
    unfold cfg_edgesA in Hes.
    destruct (cuts_edgesA_spec segs fuel cutpcs g (map ena_state cuts) 0 (map ena_state cuts ++ map ena_state exits) es Hes k _ HkT)
      as (Hle & Hlen & Hwf & leaves & Hrun & HL).
    destruct (sym_run_etripleA segs fuel cutpcs (ena_state n0) leaves (ena_pred n0) rho0 tp0 Hlen (Hst n0 Hcut) Hrun w Hsp0) as (w' & Hsteps & HLQ).
    destruct HLQ as (L & rho'' & HinL & Hag & Hsm & Hkk).
    destruct (HL L HinL) as [Hr|(j & s & X & HinE & HnX & Hid & Hent)].
    { exfalso. eapply (leaf_refuted_sound rho''); [exact Hr|]. eapply smatchA_facts; exact Hsm. }
    rewrite Nat.add_0_l in HinE.
    pose proof (proj1 (Forall_forall _ _) Hedges _ HinE) as EOK. unfold eedge_okA in EOK. cbn [ea_src ea_tgt ea_leaf ea_sub] in EOK.
    rewrite <- map_app in HnX. rewrite nth_error_map in HnX. unfold enodeA in *.
    destruct (nth_error (cuts ++ exits) j) as [nj|] eqn:HnXG; cbn in HnX; [|discriminate]. injection HnX as HX.
    destruct w' as [tr [ms md]]. cbn [w_tr w_cfg fst snd cfg_model] in Hkk.
    assert (FACTS : Forall (holds rho'') (ss_facts (ax_S (la_state L)))) by (eapply smatchA_facts; exact Hsm).
    destruct (EOK n0 nj ltac:(rewrite nth_error_app1; [exact Hk| apply nth_error_Some; congruence]) eq_refl rho'' rho'' tp0 tr md
                (agree_below_refl _ _) Hkk FACTS) as [HGj HMj].
    rewrite (Hms n0 rho0 rho'' Hcut Hag) in HMj.
    exists (tr, mkCfg ms md), nj, (rho_sub rho'' s). split; [exact Hsteps|]. split; [eapply nth_error_In; exact HnXG|].
    split; [|exact HMj]. split; [rewrite HX; eapply smatchA_entails; eauto | exact HGj]. }
  assert (BODY : forall a, etriple segs (I a) (fun w => (exists a', (Zwf 0 a' a) /\ I a' w) \/ Q w)).
  { intros a w (n0 & rho0 & tp0 & Hin0 & Hsp0 & Hm0 & Ha0).
    apply in_app_or in Hin0 as [Hcut|Hexit].
    - destruct (ROUND n0 rho0 tp0 w Hcut Hsp0) as (w' & nj & rhoj & Hsteps & Hinj & Hspj & Hmj).
      exists w'. split; [exact Hsteps|]. left. exists (ena_meas nj rhoj). split; [unfold Zwf; lia|].
      exists nj, rhoj, tp0. split; [exact Hinj|]. split; [exact Hspj|]. split; [reflexivity|lia].
    - destruct (Hexits n0 rho0 tp0 Hexit w Hsp0) as (w' & Hsteps & [Hfam|Hq]).
      + destruct Hfam as (n1 & rho1 & tp1 & Hin1 & Hsp1 & Hm1).
        exists w'. split; [exact Hsteps|]. left. exists (ena_meas n1 rho1). split; [unfold Zwf; lia|].
        exists n1, rho1, tp1. split; [apply in_or_app; left; exact Hin1|].
        split; [exact Hsp1|]. split; [reflexivity|lia].
      + exists w'. split; [exact Hsteps|]. right. exact Hq. }
  pose proof (@etriple_loop segs Z (Zwf 0) (Zwf_well_founded 0) I Q BODY) as LOOP.
  intros w Hw.
  destruct (Z_lt_le_dec (ena_meas n rho) 0) as [Hneg|Hnn].
  - exfalso. destruct (ROUND n rho tp w Hin Hw) as (w' & nj & rhoj & _ & _ & _ & Hmj). lia.
  - apply (LOOP (ena_meas n rho)). exists n, rho, tp. split; [apply in_or_app; left; exact Hin|].
    split; [exact Hw|]. split; [reflexivity|lia].
Qed.

Lemma ereenter_cutETA : ltac2:(tb__ "0|1|
SfS2A1S2S1bOF_;S26S17SfS23Q40A1A1S1aS2R5R6A3S20S2aZ0S5R6R3A2M0A2S2bG0R4A2A2S1cVsegs;ScVsegs;S6R7A1S3R7A1R4R3A5S1bS21S28R9R6R1A3R7R1A1A2Lw;A3F_;F_;Ftp;Frho;Fbound;FQ;Fn;Fcuts;").
Proof using .
  intros cuts n Q bound rho tp Hin Hm w Hw. exists w. split; [apply wsteps_refl|]. left.
  exists n, rho, tp. auto.
Qed.
End G.
