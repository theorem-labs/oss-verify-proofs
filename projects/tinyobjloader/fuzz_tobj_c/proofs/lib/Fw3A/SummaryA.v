(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_X"; "ax_base"; "la_state"; "axwf"; "word_byte"; "xr_subst"; "mkAX"; "xr_covered"; "xr_eqb"; "xrs_covered_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sobj"; "ss_next"; "sv"; "sstate"; "eval"; "obj_range"; "ss_objs"; "agree_below"; "sv_eqb"; "outside_all"; "rm"; "smatch"; "ss_facts"; "sv_below"; "obj_holds"; "obj_wf"; "pairwise_disjoint"; "@Corelib.Init.Datatypes"; "list"; "pair"; "bool"; "option"; "andb"; "prod"; "Some"; "true"; "fst"; "snd"; "None"; "orb"; "app"; "negb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "mat_equiv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "smatchA"; "SPA"; "jpredA"; "LQA"; "stableA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "sv_subst"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "w_cfg"; "w_tr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA.SA"; "entails_frA"; "import_postA"; "LQPA"; "J_ofPA"; "call_checkA"; "call_checkPA"; "import_okPA"; "post_vars"; "import_subA"; "post_okXA"; "entails_frA_ref"; "xs_framed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "sv_vars_all"; "call_link"; "call_linkP"; "import_sub"; "call_checkP"; "import_okP"; "import_post"; "new_objs"; "post_ok"; "wsub_below"; "wsub_bound"; "wsub_dom_below"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "div"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@Stdlib.PArith.BinPos.Pos"; "ltb"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.EntailFast"; "entails_fr_f"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymSoundF SymSoundR SymFrame SymEntail SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.EntailFast.
Import ListNotations.
Open Scope Z_scope.

Definition jpostA : Type := ltac2:(tb__ "0|1|
SdS1fS43Q40A1A1M0SdG0S1fS2eA1S2dOF_;F_;F_;F_;F_;F_;").

Section SA.
Variable segs : list Segment.

Definition LQPA (n : positive) (rho0 : valuation) (tp0 : list word) (Posts : list (axst * jpostA)) : assn := ltac2:(tb__ "0|1|
S4bS31S0S0S31S36S36S31SdSdS31S1fS43Q40A1A1M0G0S30S37S24S0S36A2S20S0S36R4R3A4VPosts;A3S30S5dVn;Vrho0;R2A3S30S3bVsegs;R2R1R4R5A5R3Vrho0;Vtp0;R2R1S50R5A1S42S4fR5A1A1A6A2A2A2Ltp';A2Lrho';A2LJL;A2LL;A2Lw;").

Lemma LQA_LQPA : forall (J : jpredA) n rho0 tp0 (leaves : list leafA) w,
  LQA segs J n rho0 tp0 leaves w ->
  LQPA n rho0 tp0 (map (fun L => (la_state L, (fun _ _ r p t m => J r p t m) : jpostA)) leaves) w.
Proof using .
  intros J n rho0 tp0 leaves w (L & rho' & Hin & Hag & Hsm & Hk).
  exists (la_state L), (fun _ _ r p t m => J r p t m), rho', tp0. split; [|split; [apply agree_below_vals; exact Hag | split; assumption]].
  apply in_map_iff. exists L. auto.
Qed.

Lemma LQPA_intro : ltac2:(tb__ "0|2|
S4aSdS1fS43Q40A1A1M0S1fS24S0S36A2M1A1S0S36SdG0S4bS3dS37G1S20S0S36R6R5A4R7A3S3cVsegs;R2R7R5R4R3A6S5dRcRbR6A3R4R7R6S50R5A1S42S4fR5A1A1A4R9RdRcR8R7S50R6A1S42S4fR6A1A1A6F_;S53ReRdRcRbR6A5F_;F_;F_;F_;FJ;Fw;Ftp;Frho;FJL;FL;FPosts;Ftp0;Frho0;Fn;").
Proof using .
  intros n rho0 tp0 Posts L JL rho tp w J Hin [Hsm Hk] Hag HJ. exists L, JL, rho, tp. auto.
Qed.

Lemma triple_LQA_LQPA : forall ok (P : assn) (J : jpredA) n rho0 tp0 leaves,
  triple segs ok P (LQA segs J n rho0 tp0 leaves) ->
  triple segs ok P (LQPA n rho0 tp0 (map (fun L => (la_state L, (fun _ _ r p t m => J r p t m) : jpostA)) leaves)).
Proof using .
  intros ok P J n rho0 tp0 leaves HT. eapply triple_conseq; [intros w Hw; exact Hw | | exact HT].
  intros w Hw. apply LQA_LQPA. exact Hw.
Qed.

Lemma etriple_LQA_LQPA : forall (P : world -> Prop) (J : jpredA) n rho0 tp0 leaves,
  etriple segs P (LQA segs J n rho0 tp0 leaves) ->
  etriple segs P (LQPA n rho0 tp0 (map (fun L => (la_state L, (fun _ _ r p t m => J r p t m) : jpostA)) leaves)).
Proof using .
  intros P J n rho0 tp0 leaves HT. eapply etriple_conseq; [intros w Hw; exact Hw | | exact HT].
  intros w Hw. apply LQA_LQPA. exact Hw.
Qed.

Lemma exit_postPA : ltac2:(tb__ "0|2|
S4bOF_;S3dS4aSdS1fS43Q40A1A1M0S1fS24S0S36A2M1A1S0S36S4eS37G1S20S0S36R3R2A4R4A3SdG0S1fS2eA1S2dRdR4R3R2R1A4S30S5dRdRcR5A3R8RcRbR5R4R3R2A6A2F_;Fmd;Ftr;Ftp;Frho;SdG0S4dVsegs;RdS3cVsegs;RcR7R2R1A5S4bS33R6R1A1S53RcRbRaR9R1A5A2Lw;A4Ftp;Frho;F_;F_;FX;FJL;FE;FPosts;Ftp0;Frho0;Fn;FJE;Fok;").
Proof using .
  intros ok JE n rho0 tp0 Posts E JL X Hin HJ rho tp.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w [Hsm Hk]. right. destruct (HJ _ _ _ _ Hk) as [Hag HJL]. exists E, JL, rho, tp. auto.
Qed.

Lemma eexit_postPA : ltac2:(tb__ "0|2|
S3dS4aSdS1fS43Q40A1A1M0S1fS24S0S36A2M1A1S0S36S4bOF_;S37G1S20S0S36R3R2A4R4A3SdG0S1fS2eA1S2dRdR4R3R2R1A4S30S5dRdRcR5A3R8RcRbR5R4R3R2A6A2F_;Fmd;Ftr;Ftp;Frho;SdG0S4cVsegs;S3cVsegs;RcR7R2R1A5S4bS33R6R1A1S53RcRbRaR9R1A5A2Lw;A3Ftp;Frho;F_;F_;FX;FJL;FE;FPosts;Ftp0;Frho0;Fn;FJE;").
Proof using .
  intros JE n rho0 tp0 Posts E JL X Hin HJ rho tp w [Hsm Hk].
  exists w. split; [apply wsteps_refl|]. right. destruct (HJ _ _ _ _ Hk) as [Hag HJL]. exists E, JL, rho, tp. auto.
Qed.

Definition entails_frA_ref (C Pre : axst) (s : wsub) : option (list sobj) := ltac2:(tb__ "0|5|
S22S1fSeA1M0A1M1G1Lx;S70S1VC;A1M2S1VPre;A1Vs;A3G0S21G1L_;S23S23S38S24S10S10A2M3G3SaS1aG2A1S3VC;A1S8Vs;R1A2A3Lr;S3VPre;A1A3S16S48Vs;S4VPre;A1A2S4VC;A1A2A2S6VPre;A1A2S25G0R1A2S29G0A1M4X21x2LR;G4X22x2").

Definition entails_frA (C Pre : axst) (s : wsub) : option (list sobj) := ltac2:(tb__ "0|5|
S22S1fSeA1M0A1M1G1Lx;S73S1VC;A1M2S1VPre;A1Vs;A3G0S21G1L_;M3ScS1aG2A1S3VC;A1Vs;S3VPre;A1A4G3S16S48Vs;S4VPre;A1A2S4VC;A1A2G3S6VPre;A1S25G0R1A2S29G0A1M4X21x2G4X21x2G4X21x2LR;G4X22x2").
Lemma entails_frA_ref_eq : ltac2:(tb__ "0|0|
S0S0S47S2fS22S1fSeA1A1S51R3R2R1A3S5bR3R2R1A3A3Fs;FPre;FC;").
Proof using .
  intros C Pre s. unfold entails_frA, entails_frA_ref. rewrite EntailFast.entails_fr_f_eq, xrs_covered_f_eq.
  destruct (entails_fr (ax_S C) (ax_S Pre) s) as [R|]; [|reflexivity].
  destruct (forallb (fun r => xr_covered (ss_facts (ax_S C)) (ax_X C) (xr_subst s r)) (ax_X Pre)); [|reflexivity]. cbn [andb].
  destruct (sv_eqb (sv_subst s (ax_base Pre)) (ax_base C)); [|reflexivity]. cbn [andb]. destruct (axwf Pre); reflexivity.
Qed.

Lemma entails_fr_ranges_ex : ltac2:(tb__ "0|2|
S11S11S47S1fSeA1M0SdS1fS2eA1M1S3aS2dS2fS22G0A1S70R8R7R6A3S25G0R5A2A3S19Vsegs;R5R9S20G1S40R4S41R3R2A2A4A4SeS37SeR1S14RaA1A3S31SeSeS30S37SeR1S14RdA1A3S2fS24S49S49A2S13S46S45R9RaR7A3RbA2R3A2S13R9R1A2A3A2LoL;A2F_;FoT;F_;F_;Fmd;Fms;Ftr;Frho;FR;Fs;FT;FL;").
Proof using .
  intros L T s R rho tr ms md He Hsm.
  rewrite entails_fr_eq in He. unfold entails_fr_ref in He.
  destruct (witnesses (ss_facts L) (ss_objs L) (map (obj_subst s) (ss_objs T))) as [ns|] eqn:Hw; [|discriminate].
  destruct (nodupN ns && forallb (fun i => Nat.ltb i (length (ss_objs L))) ns
            && entails (set_objs L (select (ss_objs L) ns)) T s)%bool eqn:Hc; [|discriminate].
  injection He as <-.
  apply andb_prop in Hc as [Hc Hent]. apply andb_prop in Hc as [Hnd Hlt].
  assert (Hlt' : forall i, In i ns -> (i < length (ss_objs L))%nat).
  { intros i Hi. apply Nat.ltb_lt. exact (proj1 (forallb_forall _ _) Hlt i Hi). }
  set (idxs := ns ++ complement ns (length (ss_objs L))).
  assert (Hperm : smatch segs rho (set_objs L (select (ss_objs L) idxs)) (tr, mkCfg ms md)).
  { apply smatch_select; [exact Hsm | apply nodupN_app_complement; exact Hnd | |].
    - intros i Hi. apply in_app_or in Hi as [Hi|Hi]; [apply Hlt'; exact Hi|]. apply complement_spec in Hi. lia.
    - intros i Hi. subst idxs. apply in_or_app. destruct (memN i ns) eqn:E.
      + left. apply memN_In. exact E.
      + right. apply complement_spec. split; [exact Hi|]. intros Hin. apply (proj2 (memN_In i ns)) in Hin. congruence. }
  assert (Hsplit : ss_objs (set_objs L (select (ss_objs L) idxs))
                   = select (ss_objs L) ns ++ select (ss_objs L) (complement ns (length (ss_objs L)))).
  { cbn. unfold select, idxs. apply map_app. }
  pose proof (smatch_frame_in segs rho _ _ _ tr ms md Hsplit Hperm) as Hin.
  intros oT HoT.
  destruct (entails_ranges segs _ T s _ tr ms md Hent Hin oT HoT) as (oL & HoL & ->).
  cbn [set_objs ss_objs] in HoL. rewrite obj_range_absorb.
  exists oL. split; [|reflexivity]. eapply select_In; [exact HoL|]. intros i Hi. apply Hlt'. exact Hi.
Qed.

Lemma entails_fr_outside : ltac2:(tb__ "0|3|
S11S11S47S1fSeA1M0SdS1fS2eA1M1S3aS2dS43Q40A1S2fS22G0A1S70R9R8R7A3S25G0R6A2A3S19Vsegs;R6RaS20G1S40R5S41R4R3A2A4A4S17R7S14RbA1M2R3A3S17S46S45R8R9R6A3RaA2G2R4A3F_;F_;F_;Fa;Fmd;Fms;Ftr;Frho;FR;Fs;FT;FL;").
Proof using .
  intros L T s R rho tr ms md a He Hsm Hout. apply Forall_forall. intros oT HoT.
  destruct (entails_fr_ranges_ex L T s R rho tr ms md He Hsm oT HoT) as (oL & HoL & E).
  cbn zeta. rewrite E. exact (proj1 (Forall_forall _ _) Hout oL HoL).
Qed.

Theorem entails_frA_sound : ltac2:(tb__ "0|3|
S0S0S47S1fSeA1M0SdS1fS43Q40A1A1S1fS2eA1M1S3aS2dS2fS22G0A1S51R9R8R7A3S25G0R6A2A3S3bVsegs;R6R5RaS20G1S40R4S41R3R2A2A4A5S30S3bVsegs;S46S45R7R8S34R3R6R4A3M2A3R9A2R6RaS20G1S40R5S41R4R3A2A4A5S30S6bSeS1cVsegs;R7G2A3R8A3S30S1eR7R8A2S30S2fS21S38SeS1dSfS1RbA1A1A1R8A3S26A3SeS37SeR1R9A3S37SeR2S14S1RdA1A1A3F_;Fo;A2A2A2A2F_;F_;Fmd;Fms;Ftr;Ftp;Frho;FR;Fs;FPre;FC;").
Proof using .
  intros C Pre s R rho tp tr ms md He (Hsm & HMI & Hwf & Hsh & Hhz). rewrite entails_frA_ref_eq in He. unfold entails_frA_ref in He.
  destruct (entails_fr (ax_S C) (ax_S Pre) s) as [R0|] eqn:Hfr; [|discriminate].
  match type of He with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection He as ->.
  apply andb_prop in Hc as [Hc HwfP]. apply andb_prop in Hc as [HX Hb]. apply sv_eqb_sound in Hb.
  unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
  destruct (entails_fr_sound segs (ax_S C) (ax_S Pre) s R rho tr (vms md tp ms) (vmd md) Hfr Hsm) as (HsmP & HR & Hpd & HwfR & HinR).
  split; [|split; [exact HR | split; [exact Hpd | split; [exact HwfR | exact HinR]]]].
  split; [unfold virt; cbn [fst snd cfg_ms cfg_model w_tr w_cfg]; exact HsmP|].
  split; [exact HMI|]. split; [exact HwfP|]. split; [|exact Hhz].

  unfold shadow_ok in Hsh |- *. pose proof (smatch_facts segs _ _ _ Hsm) as Hf.
  rewrite <- eval_subst, eval_absorb, Hb.
  apply Forall_forall. intros r Hr.
  pose proof (proj1 (forallb_forall _ _) HX r Hr) as Hx.
  pose proof (xr_covered_sound rho (ss_facts (ax_S C)) (ss_objs (ax_S C)) (bv_unsigned (eval rho (ax_base C))) (ax_X C) (xr_subst s r) Hf Hx Hsh) as Hok.
  destruct r as [b l]. unfold xr_ok in Hok |- *. unfold xr_subst in Hok. cbn [fst snd] in Hok |- *.
  rewrite <- !eval_subst, !eval_absorb.
  destruct Hok as (H8 & Hnw & Hok). split; [exact H8|]. split; [exact Hnw|].
  intros a Ha. destruct (Hok a Ha) as (Hoff & Hout & Hwd & v & Hv & Henc).
  split; [exact Hoff|]. split; [|split].
  - eapply entails_fr_outside; eauto.
  - intros j Hj. destruct (Hwd j Hj) as [Hoj Hrj]. split; [eapply entails_fr_outside; eauto|].
    unfold rho_sub, rho_absorb. cbn [rm]. destruct (in_ranges_dec rho R _) as [Hin|]; [|exact Hrj].
    exfalso. destruct Hin as (o & HoR & Hrng). exact (proj1 (Forall_forall _ _) Hoj o (HinR o HoR) Hrng).
  - exists v. split; [|exact Henc]. unfold rho_sub, rho_absorb. cbn [rm].
    destruct (in_ranges_dec rho R _) as [Hin|]; [|exact Hv].
    exfalso. destruct Hin as (o & HoR & Hrng). exact (proj1 (Forall_forall _ _) Hout o (HinR o HoR) Hrng).
Qed.

Definition import_subA (s : wsub) (Pre L C : axst) : wsub := ltac2:(tb__ "0|0|
S61Vs;SfS1VPre;A1A1S1VL;A1SfS1VC;A1A1A4").

Definition import_postA (s : wsub) (Pre L C : axst) (R : list sobj) : axst := ltac2:(tb__ "0|1|
S9S64Vs;SfS1VPre;A1A1S1VL;A1SfS1VC;A1A1VR;A5S2bS24S10S10A2M0S3VC;A1S6aG0G0S8S59Vs;VPre;VL;VC;A4A1S3VL;A1A4A3S4VC;A1A3").

Definition post_vars (s : wsub) (nf nc : positive) : positive -> bool := ltac2:(tb__ "0|0|
S4aS2aS2aS2cS71R1Vnf;A2A1S68Vs;R1A2A2S71R1Vnc;A2A2Lv;").

Definition post_okXA (Pre C : axst) (s : wsub) (R : list sobj) (L : axst) : bool := ltac2:(tb__ "0|2|
S58Vs;SfS1VPre;A1A1SfS1VC;A1A1A3S4aS21F_;S23S23S23S23S38S24S10S10A2M0G0S23S5eR2S27S10S10R1A3A2S5eR2S28S10S10R1A3A2A2Lr;S3VL;A1A3S5eR1S4VL;A1M1A2A2S16S48S59Vs;VPre;VL;VC;A4G1A2S4VC;A1A2A2S6VL;A1A2S6S52Vs;VPre;VL;VC;VR;A5A1A2Tf;").

Definition call_checkPA (C Pre : axst) (s : wsub) (R : list sobj) (Posts : list axst) : bool := ltac2:(tb__ "0|0|
S23S62S1VC;A1S1VPre;A1Vs;VR;S6aS0S11S1VPosts;A4A5S38S0S5aVPre;VC;Vs;VR;A4VPosts;A3A2").

Definition import_okPA (rho : valuation) (ms : machine_state) (R : list sobj) (s : wsub)
           (Pre L C : axst) (rhoL : valuation) : Prop := ltac2:(tb__ "0|f|
S30S63Vrho;Vms;VR;Vs;S1VPre;A1M0S1VL;A1M1VrhoL;A7S30S24S10S10A2M2S49S49SeS37G2R4S3VL;A1A3S30S6cS44Q40M3S12VrhoL;S27S10S10R5A3A2A2M4R4A2S6dR4S6eG4S44G3S12VrhoL;S28S10S10R5A3A2A2A2A2A2S30S6cZ0M5R4A2S6dR4Z8M6A2A2S37SeR4VR;A3S32S30S6cS27S49S49S13Vrho;R5A2M7A3S44G3S7S6eS44G3S12VrhoL;S4VL;A1A2A2S6fR7G6A2M8A2R6A2A2M9A2S6dG9S28S49S49G7A3A2A2A1F_;F_;F_;F_;FoR;Fj;Fa;Fr;G2S49S49S37G2R3S3VC;A1A3S30S6cS44G3S12Vrho;S27S10S10R4A3A2A2MaR3A2S6dR3S6eGaS44G3S12Vrho;S28S10S10R4A3A2A2A2A2A2S30S6cG5R3A2S6dR3G6A2A2S30S2fS22S43Q8A1A1S18VrhoL;S7S6eS44G3S12Vrho;S4VC;A1A2A2MbS6fR5G6A2A2R4A2McA2S18Vrho;GcA2A3SeS37SeR1S65G0G1A2A3S32S30S6cS27S49S49S13VrhoL;R2A2MdA3S44G3S7S6eGbG8A2R6A2A2MeA2S6dGeS28S49S49GdA3A2A2A1F_;Fo';A2F_;F_;F_;Fj;Fa;Fr;A2A2").

Definition J_ofPA (JL : jpostA) (rho1 : valuation) (tp1 : list word) (rhoL : valuation) (tpL : list word) : jpredA := ltac2:(tb__ "0|0|
SdS1fS43Q40A1A1S1fS2eA1S2dVJL;Vrho1;Vtp1;VrhoL;VtpL;R2R1A6Lm;Lt;L_;L_;").

Lemma stableA_ofPA : ltac2:(tb__ "0|2|
S4aSdS1fS43Q40A1A1M0SdG0S1fS2eA1M1S2dOFx4;Fx3;Fx2;Fx1;Fx0;Fx;SdG0SdG0G0G1S2dS2dS35Vsegs;R4R2R1A4RaR9R8R7R6R4R3A6RbRaR9R8R7R5R3A6F_;F_;Fm';Fm;Ft;Ftp;S3fVsegs;R7S54R6R5R4R3R2A5A3F_;FtpL;FrhoL;Ftp1;Frho1;FJL;Fn;").
Proof using . intros n JL rho1 tp1 rhoL tpL H r r' tp t m m' _ Hme HJ. unfold J_ofPA in *. exact (H tp t m m' Hme HJ). Qed.

Lemma call_linkP_eval : ltac2:(tb__ "0|1|
SdS3aS1fSeA1S47S11S11S11SdSdS10S60RaR9R8R7R6R5R4R3R2A9S2fS21S5eS58R8SfR7A1SfR6A1M0A3R2A2S26A3S2fS21S1bG0R3A2S26A3S2fS43Q40A1S12R6S48S61RaSfR9A1R7SfR8A1A4R4A2A2S12R5R4A2A3F_;F_;F_;Fe;FrhoL;Frho';FL;FC;FPre;Fs;FR;Fms;Frho;").
Proof using .
  intros rho ms R s Pre C L rho' rhoL e (A1 & A2 & A3 & A4) Hv Hb.
  rewrite eval_subst. symmetry.
  apply (eval_agree_vars (fun v => post_vars s (ss_next Pre) (ss_next C) v && (v <? ss_next L)%positive)).
  - intros v H. apply andb_prop in H as [H1 H2]. apply Pos.ltb_lt in H2. cbn [rho_sub rw].
    apply A4; [exact H1 | lia].
  - intros l. cbn [rho_sub rl]. destruct A3 as [_ AL]. rewrite <- AL. cbn [rho_sub rho_absorb rl].
    destruct A1 as [_ AL1]. apply AL1.
  - apply sv_vars_all_and; assumption.
Qed.

Lemma import_post_linkPA : ltac2:(tb__ "0|4|
S0S0S47S1fSeA1M0S1fS0A1SdS1fS43Q40A1A1M1S1fS2eA1M2S3aS2dG2S3aS2dS0SdG1S2fS22G0A1S51R10RfReA3S25G0RdA2A3S2fS21S56R11R10RfReRdA5S26A3S3bVsegs;RdRcR12S20G2S40RbS41RaR9A2A4M3A5S37S0R6RfA3S5dSfS1R13A1A1S46S45RfR11S34RbReRcA3A3R12A2R6A3S3bVsegs;R7R6R8G3A5S57R11S34RdR10ReA3R13R14R15R9R16R8A8S31SdSdS30S60R13S34RfR12R10A3R15R16S1R17A1S1R18A1S1RbA1R1RaA9S3bVsegs;R1R9S52R16R17RbR18R15A5S20G2S40ReS41RdRcA2A4A5A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;FtpL;FrhoL;FL;Fmd';Fms';Ftr';Fmd;Fms;Ftr;Ftp;Frho;FPosts;FR;Fs;FPre;FC;").
Proof using .
  intros C Pre s R Posts rho tp tr ms md tr' ms' md' L rhoL tpL He Hchk HsmA HinL HagL HsmAL (Hok & Hshc & Hkeep).
  pose proof HsmA as (Hsm & HMI & Hwf & Hsh & Hhz). pose proof HsmAL as (HsmL & HMIL & HwfL & HshL & HhzL).
  unfold call_checkPA in Hchk. apply andb_prop in Hchk as [Hchk HXA].
  pose proof (proj1 (forallb_forall _ _) HXA L HinL) as HXL. unfold post_okXA in HXL.
  apply andb_prop in HXL as [HXL HwfI]. apply andb_prop in HXL as [HXL HwfL']. apply andb_prop in HXL as [HXL Hbq]. apply andb_prop in HXL as [HXv Hbv].
  assert (Hfr : entails_fr (ax_S C) (ax_S Pre) s = Some R).
  { rewrite entails_frA_ref_eq in He. unfold entails_frA_ref in He. destruct (entails_fr (ax_S C) (ax_S Pre) s) as [R0|]; [|discriminate].
    match type of He with (if ?c then _ else _) = _ => destruct c; [|discriminate] end. congruence. }
  unfold virt in Hsm, HsmL. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm, HsmL.
  destruct (import_post_linkP segs (ax_S C) (ax_S Pre) s R (map ax_S Posts) rho tr (vms md tp ms) (vmd md) tr' (vms md' tpL ms') (vmd md') (ax_S L) rhoL
              Hfr Hchk Hsm ltac:(apply in_map_iff; exists L; auto) HagL HsmL Hok) as (rho' & HLK & HSP).
  exists rho'. split; [exact HLK|].
  split; [unfold virt; cbn [fst snd cfg_ms cfg_model w_tr w_cfg]; exact HSP|].
  split; [exact HMIL|]. split; [exact HwfI|]. split; [|exact HhzL].

  pose proof HLK as (A1 & A2 & A3 & A4).
  unfold shadow_ok in HshL |- *. unfold import_postA, import_subA. cbn [ax_X ax_base ax_S].
  unfold axwf in HwfL'. apply andb_prop in HwfL' as [HXb Hbb].
  apply sv_eqb_sound in Hbq.

  pose proof Hwf as HwfC. unfold axwf in HwfC. apply andb_prop in HwfC as [HXC HbC].
  assert (EbC : eval rho' (ax_base C) = eval rho (ax_base C)).
  { symmetry. exact (eval_agree_vals (ss_next (ax_S C)) rho rho' _ A1 HbC). }
  assert (EbL : eval rho' (ax_base C) = eval rhoL (ax_base L)).
  { rewrite <- Hbq. apply (call_linkP_eval rho (vms md tp ms) R s (ax_S Pre) (ax_S C) (ax_S L) rho' rhoL (ax_base L) HLK Hbv Hbb). }

  unfold call_checkP in Hchk. apply andb_prop in Hchk as [Hchk Hposts].
  pose proof (proj1 (forallb_forall _ _) Hposts (ax_S L) ltac:(apply in_map_iff; exists L; auto)) as HP.
  unfold post_okP in HP. apply andb_prop in HP as [HP _]. apply andb_prop in HP as [HP HswfL]. apply andb_prop in HP as [_ Hpv].
  assert (E1 : forall oL, In oL (ss_objs (ax_S L)) ->
            obj_range (rho_sub rho' (import_sub s (ss_next (ax_S Pre)) (ax_S L) (ss_next (ax_S C)))) oL = obj_range rhoL oL).
  { intros oL HoL.
    pose proof (state_vars_all_and _ _ Hpv HswfL) as VARS. unfold state_vars_all in VARS.
    apply andb_prop in VARS as [VARS _]. apply andb_prop in VARS as [_ VOB].
    apply (obj_range_agree_vars (fun v => post_vars s (ss_next (ax_S Pre)) (ss_next (ax_S C)) v && (v <? ss_next (ax_S L))%positive)).
    - intros v0 H. apply andb_prop in H as [H1 H2]. apply Pos.ltb_lt in H2. cbn [rho_sub rw]. apply A4; [exact H1 | lia].
    - intros l0. cbn [rho_sub rl]. destruct A3 as [_ AL]. rewrite <- AL. cbn [rho_sub rho_absorb rl]. destruct A1 as [_ AL1]. exact (AL1 l0).
    - exact (proj1 (forallb_forall _ _) VOB oL HoL). }
  destruct (entails_frA_sound C Pre s R rho tp tr ms md He HsmA) as (HsmPre & _ & _ & HwfR & HinR).
  assert (ER : forall oR, In oR R -> obj_range rho' oR = obj_range rho oR).
  { intros oR HoR. exact (obj_range_agree_vals (ss_next (ax_S C)) rho rho' oR A1 (proj1 (forallb_forall _ _) HwfR oR HoR)). }
  apply Forall_app. split.
  -
    apply Forall_forall. intros [b l] Hr. pose proof (proj1 (Forall_forall _ _) Hsh _ Hr) as Hx.
    pose proof (proj1 (forallb_forall _ _) HXC _ Hr) as Hbl. unfold xr_below in Hbl. cbn [fst snd] in Hbl. apply andb_prop in Hbl as [Hb1 Hl1].
    unfold xr_ok in Hx |- *. cbn [fst snd] in Hx |- *.
    rewrite <- (eval_agree_vals (ss_next (ax_S C)) rho rho' b A1 Hb1).
    rewrite <- (eval_agree_vals (ss_next (ax_S C)) rho rho' l A1 Hl1).
    rewrite EbC.
    destruct Hx as (H8 & Hnw & Hx). split; [exact H8|]. split; [exact Hnw|].
    intros a Ha. destruct (Hx a Ha) as (Hoff & Hout & Hwd & v & Hv & Henc).
    assert (OUT : forall x, outside_all rho (ss_objs (ax_S C)) x ->
              (forall o', In o' (new_objs (ax_S Pre) (ax_S L)) -> ~ (fst (obj_range rhoL o') <= bv_unsigned x < snd (obj_range rhoL o'))) ->
              outside_all rho' (ss_objs (import_post s (ss_next (ax_S Pre)) (ax_S L) (ss_next (ax_S C)) R)) x).
    { intros x HoutX HnewX. unfold import_post. cbn [ss_objs set_objs subst_state]. apply outside_all_app_iff. split.
      * apply Forall_forall. intros o' Ho'. apply in_map_iff in Ho' as (oL & <- & HoL). cbn zeta.
        rewrite obj_range_subst, (E1 oL HoL).
        destruct (new_objs_spec (ax_S Pre) (ax_S L) oL HoL) as [FR|NEW]; [|exact (HnewX oL NEW)].
        apply existsb_exists in FR as (oP & HinP & SF). rewrite (same_frame_range rhoL oL oP SF).
        assert (E2 : obj_range rhoL oP = obj_range (rho_sub (rho_absorb rho R (vms md tp ms)) s) oP).
        { apply (obj_range_agree_vals (ss_next (ax_S Pre))); [exact HagL|].
          pose proof (smatchA_swf segs _ _ _ _ HsmPre) as W. exact (proj1 (forallb_forall _ _) (swf_objs _ W) oP HinP). }
        rewrite E2. destruct (entails_fr_ranges_ex (ax_S C) (ax_S Pre) s R rho tr (vms md tp ms) (vmd md) Hfr Hsm oP HinP) as (oC & HoC & ->).
        exact (proj1 (Forall_forall _ _) HoutX oC HoC).
      * apply Forall_forall. intros oR HoR. cbn zeta. rewrite (ER oR HoR). exact (proj1 (Forall_forall _ _) HoutX oR (HinR oR HoR)). }
    assert (Hj0 : 0 <= (bv_unsigned (eval rho (ax_base C)) + a / 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (Eba : shadow_addr (bv_unsigned (eval rho (ax_base C))) a
                  = word_byte (bv_unsigned (eval rho (ax_base C)) + a / 8) ((bv_unsigned (eval rho (ax_base C)) + a / 8) mod 8)).
    { unfold shadow_addr. rewrite word_byte_self; [reflexivity | lia]. }
    split; [exact Hoff|]. split; [|split].
    + destruct (Hkeep (b, l) a _ Hr Ha Hj0) as [_ Hnewo]. rewrite Eba. apply OUT; [rewrite <- Eba; exact Hout | exact Hnewo].
    + intros j Hj. destruct (Hwd j Hj) as [Hoj Hrj]. destruct (Hkeep (b, l) a j Hr Ha Hj) as [Hrm Hnewo].
      split; [apply OUT; [exact Hoj | exact Hnewo] | rewrite A2, Hrm; exact Hrj].
    + exists v. split; [|exact Henc]. destruct (Hkeep (b, l) a _ Hr Ha Hj0) as [Hrm _]. rewrite A2, Eba, Hrm, <- Eba. exact Hv.
  -
    apply Forall_forall. intros r' Hr'. apply in_map_iff in Hr' as ([b l] & <- & Hr).
    pose proof (proj1 (Forall_forall _ _) HshL _ Hr) as Hx.
    pose proof (proj1 (forallb_forall _ _) HXv _ Hr) as Hv. cbn [fst snd] in Hv. apply andb_prop in Hv as [Hvb Hvl].
    pose proof (proj1 (forallb_forall _ _) HXb _ Hr) as Hbl. unfold xr_below in Hbl. cbn [fst snd] in Hbl. apply andb_prop in Hbl as [Hbb' Hlb].
    unfold xr_ok in Hx |- *. unfold xr_subst. cbn [fst snd] in Hx |- *.
    rewrite (call_linkP_eval rho (vms md tp ms) R s (ax_S Pre) (ax_S C) (ax_S L) rho' rhoL b HLK Hvb Hbb').
    rewrite (call_linkP_eval rho (vms md tp ms) R s (ax_S Pre) (ax_S C) (ax_S L) rho' rhoL l HLK Hvl Hlb).
    rewrite EbL.
    destruct Hx as (H8 & Hnw & Hx). split; [exact H8|]. split; [exact Hnw|].
    intros a Ha. destruct (Hx a Ha) as (Hoff & Hout & Hwd & v & Hv & Henc).
    assert (OUT : forall x, outside_all rhoL (ss_objs (ax_S L)) x ->
              (forall oR, In oR R -> ~ (fst (obj_range rho oR) <= bv_unsigned x < snd (obj_range rho oR))) ->
              outside_all rho' (ss_objs (import_post s (ss_next (ax_S Pre)) (ax_S L) (ss_next (ax_S C)) R)) x).
    { intros x HoutX HRX. unfold import_post. cbn [ss_objs set_objs subst_state].
      apply outside_all_app_iff. split.
      * apply Forall_forall. intros o' Ho'. apply in_map_iff in Ho' as (oL & <- & HoL). cbn zeta.
        rewrite obj_range_subst, (E1 oL HoL). exact (proj1 (Forall_forall _ _) HoutX oL HoL).
      * apply Forall_forall. intros oR HoR. cbn zeta. rewrite (ER oR HoR). exact (HRX oR HoR). }
    assert (Hj0 : 0 <= (bv_unsigned (eval rhoL (ax_base L)) + a / 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (Eba : shadow_addr (bv_unsigned (eval rhoL (ax_base L))) a
                  = word_byte (bv_unsigned (eval rhoL (ax_base L)) + a / 8) ((bv_unsigned (eval rhoL (ax_base L)) + a / 8) mod 8)).
    { unfold shadow_addr. rewrite word_byte_self; [reflexivity | lia]. }
    split; [exact Hoff|]. split; [|split].
    + rewrite Eba. apply OUT; [rewrite <- Eba; exact Hout | intros oR HoR; exact (Hshc (b, l) a _ oR Hr Ha Hj0 HoR)].
    + intros j Hj. destruct (Hwd j Hj) as [Hoj Hrj].
      split; [apply OUT; [exact Hoj | intros oR HoR; exact (Hshc (b, l) a j oR Hr Ha Hj HoR)] | rewrite A2; exact Hrj].
    + exists v. split; [|exact Henc]. rewrite A2. exact Hv.
Qed.

Theorem call_soundPA : ltac2:(tb__ "0|4|
S4bOF_;S3dS3dS0S0S47S1fSeA1M0S1fS24S0S36A2M1A1S4eSdS1fS43Q40A1A1M2S2fS22G0A1S51R8R7R6A3S25G0R5A2A3S2fS21S56R9R8R7R6S6aG1S0S27S0S36A2R5A4A5S26A3SdG2S4dVsegs;RfS3cVsegs;RdRbR2R1A5S53SfS1RbA1A1R2R1R8A4A4Ftp1;Frho1;S1fS2eA1M3S3aS2dS3bVsegs;R8R7ReS20G3S40R3S41R2R1A2A4A5R11R9R8R4R2A4R11S46S45RaRdS34R3R9R4A3A3ReA2R9R5R3A4F_;F_;Fmd;Fms;Ftr;S0S36G3S3aS2dSdG2G3S3aS2dS37G1S20S0S36RaR9A4R12A3S3bVsegs;R11R10R17S20G3S40R9S41R8R7A2A4A5R1aR12R11RaR8A4S5dSfS1R18A1A1S46S45R13R16S34R9R12RaA3A3R17A2R8A3S3bVsegs;R9R8ReS20G3S40R7S41R6R5A2A4A5ReS46S45R15R18S34RbR14RcA3A3R19A2R14RaR9R8R6A6S30S57R16S34RcR15RdA3R19R1aR1bR10R1cRbA8SdS60R17S34RdR16ReA3R1aR1bS1R1cA1S1R1dA1S1R11A1R1RcA9S4dVsegs;R21S3cVsegs;S54R11S46S45R18R1bS34ReR17RfA3A3R1cA2R17RdRcA5S52R1cR1dR12R1eR1bA5R2RcA5R19A4F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;S4dVsegs;R10S3cVsegs;RfRdR7R6A5R8A4F_;F_;F_;F_;F_;Ftp;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJp;FJ;Fok;").
Proof using .
  intros ok J Jp C Pre s R Posts Q rho tp He Hchk Hsum Hin Hout.
  intros n HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound C Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp n); [|split; [exact HsmPre|exact (Hin tr ms md Hsm Hk)]].
  intros w' (L & JL & rhoL & tpL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (Hout L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm Hk HagL HsmL Hk') as [Hok Hcont].
  destruct (import_post_linkPA C Pre s R (map fst Posts) rho tp tr ms md tr' ms' md' L rhoL tpL He Hchk Hsm
              ltac:(apply in_map_iff; exists (L, JL); auto) HagL HsmL Hok) as (rho' & HLK & HSP).
  apply (Hcont rho' HLK n HgQ). split; [exact HSP|]. exact Hk'.
Qed.

Theorem call_completePA : ltac2:(tb__ "0|4|
S3dS3dS0S0S47S1fSeA1M0S1fS24S0S36A2M1A1S4bOF_;SdS1fS43Q40A1A1M2S2fS22G0A1S51R8R7R6A3S25G0R5A2A3S2fS21S56R9R8R7R6S6aG1S0S27S0S36A2R5A4A5S26A3SdG2S4cVsegs;S3cVsegs;RdRbR2R1A5S53SfS1RbA1A1R2R1R8A4A3Ftp1;Frho1;S1fS2eA1M3S3aS2dS3bVsegs;R8R7ReS20G3S40R3S41R2R1A2A4A5R11R9R8R4R2A4R11S46S45RaRdS34R3R9R4A3A3ReA2R9R5R3A4F_;F_;Fmd;Fms;Ftr;S0S36G3S3aS2dSdG2G3S3aS2dS37G1S20S0S36RaR9A4R12A3S3bVsegs;R11R10R17S20G3S40R9S41R8R7A2A4A5R1aR12R11RaR8A4S5dSfS1R18A1A1S46S45R13R16S34R9R12RaA3A3R17A2R8A3S3bVsegs;R9R8ReS20G3S40R7S41R6R5A2A4A5ReS46S45R15R18S34RbR14RcA3A3R19A2R14RaR9R8R6A6S30S57R16S34RcR15RdA3R19R1aR1bR10R1cRbA8SdS60R17S34RdR16ReA3R1aR1bS1R1cA1S1R1dA1S1R11A1R1RcA9S4cVsegs;S3cVsegs;S54R11S46S45R18R1bS34ReR17RfA3A3R1cA2R17RdRcA5S52R1cR1dR12R1eR1bA5R2RcA5R19A3F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;S4cVsegs;S3cVsegs;RfRdR7R6A5R8A3F_;F_;F_;F_;F_;Ftp;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Proof using .
  intros J Jp C Pre s R Posts Q rho tp He Hchk Hsum Hin Hout.
  intros w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound C Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  destruct (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp _ (conj HsmPre (Hin tr ms md Hsm Hk))) as (w' & Hsteps & HLQ).
  destruct HLQ as (L & JL & rhoL & tpL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (Hout L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm Hk HagL HsmL Hk') as [Hok Hcont].
  destruct (import_post_linkPA C Pre s R (map fst Posts) rho tp tr ms md tr' ms' md' L rhoL tpL He Hchk Hsm
              ltac:(apply in_map_iff; exists (L, JL); auto) HagL HsmL Hok) as (rho' & HLK & HSP).
  destruct (Hcont rho' HLK _ (conj HSP Hk')) as (w'' & Hsteps' & HQ).
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.

Definition xs_framed (Pre L : axst) : bool := ltac2:(tb__ "0|1|
S38S24S10S10A2M0G0S39G0SbR1A1S3VPre;A1A3Lr;S3VL;A1A3").

Definition call_checkA (C Pre : axst) (s : wsub) (R : list sobj) (Posts : list axst) : bool := ltac2:(tb__ "0|2|
S23S23S23S23S23S67Vs;SfS1VC;A1A1M0A2S69Vs;SfS1VPre;A1M1A1A2A2S72PaG0A2A2S38S0S0S66G1Vs;G0VR;S1R1A1A5LL;VPosts;A3A2S38S0S5aVPre;VC;Vs;VR;A4VPosts;A3A2S38S0S5cVPre;A1VPosts;A3A2").

Lemma call_link_eval : ltac2:(tb__ "0|1|
SdS3aS1fSeA1S47S11S11S11SdSdS10S5fRaR9R8R7R6R5R4R3R2A9S2fS21S5eS58R8SfR7A1SfR6A1M0A3R2A2S26A3S2fS21S1bG0R3A2S26A3S2fS43Q40A1S12R6S48S61RaSfR9A1R7SfR8A1A4R4A2A2S12R5R4A2A3F_;F_;F_;Fe;FrhoL;Frho';FL;FC;FPre;Fs;FR;Fms;Frho;").
Proof using .
  intros rho ms R s Pre C L rho' rhoL e (A1 & A2 & A3) Hv Hb.
  rewrite eval_subst. symmetry.
  apply (eval_agree_vars (fun v => post_vars s (ss_next Pre) (ss_next C) v && (v <? ss_next L)%positive)).
  - intros v H. apply andb_prop in H as [H1 H2]. apply Pos.ltb_lt in H2. cbn [rho_sub rw].
    apply A3; [exact H1 | lia].
  - intros l. cbn [rho_sub rl]. destruct A2 as (_ & AL & _). rewrite <- AL. cbn [rho_sub rho_absorb rl].
    destruct A1 as (_ & AL1 & _). apply AL1.
  - apply sv_vars_all_and; assumption.
Qed.

Lemma import_post_linkA : ltac2:(tb__ "0|4|
S0S0S47S1fSeA1M0S1fS0A1SdS1fS43Q40A1A1M1S1fS2eA1M2S3aS2dG2S3aS2dS0SdG1S2fS22G0A1S51R10RfReA3S25G0RdA2A3S2fS21S55R11R10RfReRdA5S26A3S3bVsegs;RdRcR12S20G2S40RbS41RaR9A2A4M3A5S37S0R6RfA3S15SfS1R13A1A1S46S45RfR11S34RbReRcA3A3R12A2R6A3S3bVsegs;R7R6R8G3A5S31SdSdS30S5fR12S34ReR11RfA3R14R15S1R16A1S1R17A1S1RaA1R1R9A9S3bVsegs;R1R8S52R15R16RaR17R14A5S20G2S40RdS41RcRbA2A4A5A2Lrho';A2F_;F_;F_;F_;F_;F_;FtpL;FrhoL;FL;Fmd';Fms';Ftr';Fmd;Fms;Ftr;Ftp;Frho;FPosts;FR;Fs;FPre;FC;").
Proof using .
  intros C Pre s R Posts rho tp tr ms md tr' ms' md' L rhoL tpL He Hchk HsmA HinL HagL HsmAL.
  pose proof HsmA as (Hsm & HMI & Hwf & Hsh & Hhz). pose proof HsmAL as (HsmL & HMIL & HwfL & HshL & HhzL).
  unfold call_checkA in Hchk.
  apply andb_prop in Hchk as [Hchk Hxf]. apply andb_prop in Hchk as [Hchk HXA]. apply andb_prop in Hchk as [Hchk Hposts].
  pose proof (proj1 (forallb_forall _ _) HXA L HinL) as HXL. unfold post_okXA in HXL.
  apply andb_prop in HXL as [HXL HwfI]. apply andb_prop in HXL as [HXL HwfL']. apply andb_prop in HXL as [HXL Hbq]. apply andb_prop in HXL as [HXv Hbv].
  pose proof (proj1 (forallb_forall _ _) Hxf L HinL) as HxfL. unfold xs_framed in HxfL.
  pose proof (proj1 (forallb_forall _ _) Hposts L HinL) as HPL.
  assert (Hfr : entails_fr (ax_S C) (ax_S Pre) s = Some R).
  { rewrite entails_frA_ref_eq in He. unfold entails_frA_ref in He. destruct (entails_fr (ax_S C) (ax_S Pre) s) as [R0|]; [|discriminate].
    match type of He with (if ?c then _ else _) = _ => destruct c; [|discriminate] end. congruence. }
  assert (HXcov : forallb (fun r => xr_covered (ss_facts (ax_S C)) (ax_X C) (xr_subst s r)) (ax_X Pre) = true).
  { rewrite entails_frA_ref_eq in He. unfold entails_frA_ref in He. rewrite Hfr in He.
    match type of He with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. exact Hc. }
  assert (Hchk1 : call_check (ax_S C) (ax_S Pre) s R [mkLeaf (ax_S L) RsCut] = true).
  { unfold call_check. rewrite Hchk. cbn [forallb lf_state]. rewrite HPL. reflexivity. }
  unfold virt in Hsm, HsmL. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm, HsmL.
  destruct (import_post_link segs (ax_S C) (ax_S Pre) s R [mkLeaf (ax_S L) RsCut] rho tr (vms md tp ms) (vmd md) tr' (vms md' tpL ms') (vmd md') (mkLeaf (ax_S L) RsCut) rhoL
              Hfr Hchk1 Hsm ltac:(left; reflexivity) HagL HsmL) as (rho' & HLK & HSP).
  cbn [lf_state] in HLK, HSP.
  exists rho'. split; [exact HLK|].
  split; [unfold virt; cbn [fst snd cfg_ms cfg_model w_tr w_cfg]; exact HSP|].
  split; [exact HMIL|]. split; [exact HwfI|]. split; [|exact HhzL].

  pose proof HLK as (A1 & A2 & A3).
  unfold shadow_ok in HshL |- *. unfold import_postA, import_subA. cbn [ax_X ax_base ax_S].
  unfold axwf in HwfL'. apply andb_prop in HwfL' as [HXb Hbb].
  apply sv_eqb_sound in Hbq.
  pose proof Hwf as HwfC. unfold axwf in HwfC. apply andb_prop in HwfC as [HXC HbC].
  assert (EbC : eval rho' (ax_base C) = eval rho (ax_base C)).
  { symmetry. exact (eval_agree (ss_next (ax_S C)) rho rho' _ A1 HbC). }
  assert (EbL : eval rho' (ax_base C) = eval rhoL (ax_base L)).
  { rewrite <- Hbq. apply (call_link_eval rho (vms md tp ms) R s (ax_S Pre) (ax_S C) (ax_S L) rho' rhoL (ax_base L) HLK Hbv Hbb). }

  unfold post_ok in HPL. apply andb_prop in HPL as [HPL _]. apply andb_prop in HPL as [HPL HswfL].
  apply andb_prop in HPL as [HPL Hpv]. apply andb_prop in HPL as [_ Hframes].
  assert (E1 : forall oL, In oL (ss_objs (ax_S L)) ->
            obj_range (rho_sub rho' (import_sub s (ss_next (ax_S Pre)) (ax_S L) (ss_next (ax_S C)))) oL = obj_range rhoL oL).
  { intros oL HoL.
    pose proof (state_vars_all_and _ _ Hpv HswfL) as VARS. unfold state_vars_all in VARS.
    apply andb_prop in VARS as [VARS _]. apply andb_prop in VARS as [_ VOB].
    apply (obj_range_agree_vars (fun v => post_vars s (ss_next (ax_S Pre)) (ss_next (ax_S C)) v && (v <? ss_next (ax_S L))%positive)).
    - intros v0 H. apply andb_prop in H as [H1 H2]. apply Pos.ltb_lt in H2. cbn [rho_sub rw]. apply A3; [exact H1 | lia].
    - intros l0. cbn [rho_sub rl]. destruct A2 as (_ & AL & _). rewrite <- AL. cbn [rho_sub rho_absorb rl]. destruct A1 as (_ & AL1 & _). exact (AL1 l0).
    - exact (proj1 (forallb_forall _ _) VOB oL HoL). }
  destruct (entails_frA_sound C Pre s R rho tp tr ms md He HsmA) as (HsmPre & _ & _ & HwfR & HinR).
  assert (ER : forall oR, In oR R -> obj_range rho' oR = obj_range rho oR).
  { intros oR HoR. exact (obj_range_agree (ss_next (ax_S C)) rho rho' oR A1 (proj1 (forallb_forall _ _) HwfR oR HoR)). }

  assert (IMP : forall o', In o' (ss_objs (import_post s (ss_next (ax_S Pre)) (ax_S L) (ss_next (ax_S C)) R)) ->
                exists oC, In oC (ss_objs (ax_S C)) /\ obj_range rho' o' = obj_range rho oC).
  { intros o' Ho'. unfold import_post in Ho'. cbn [ss_objs set_objs subst_state] in Ho'. apply in_app_or in Ho' as [Ho'|Ho'].
    - apply in_map_iff in Ho' as (oL & <- & HoL). rewrite obj_range_subst, (E1 oL HoL).
      pose proof (proj1 (forallb_forall _ _) Hframes oL HoL) as FR. apply existsb_exists in FR as (oP & HinP & SF).
      rewrite (same_frame_range rhoL oL oP SF).
      assert (E2 : obj_range rhoL oP = obj_range (rho_sub (rho_absorb rho R (vms md tp ms)) s) oP).
      { apply (obj_range_agree (ss_next (ax_S Pre))); [exact HagL|].
        pose proof (smatchA_swf segs _ _ _ _ HsmPre) as W. exact (proj1 (forallb_forall _ _) (swf_objs _ W) oP HinP). }
      rewrite E2. destruct (entails_fr_ranges_ex (ax_S C) (ax_S Pre) s R rho tr (vms md tp ms) (vmd md) Hfr Hsm oP HinP) as (oC & HoC & ->).
      exists oC. split; [exact HoC | reflexivity].
    - exists o'. split; [exact (HinR o' Ho') | exact (ER o' Ho')]. }
  assert (OUT : forall x, outside_all rho (ss_objs (ax_S C)) x ->
            outside_all rho' (ss_objs (import_post s (ss_next (ax_S Pre)) (ax_S L) (ss_next (ax_S C)) R)) x).
  { intros x Hout. apply Forall_forall. intros o' Ho'. cbn zeta. destruct (IMP o' Ho') as (oC & HoC & ->).
    exact (proj1 (Forall_forall _ _) Hout oC HoC). }
  pose proof A1 as (_ & _ & Arm).

  assert (KEEP : forall b l, In (b, l) (ax_X C) ->
            xr_ok rho' (ss_objs (import_post s (ss_next (ax_S Pre)) (ax_S L) (ss_next (ax_S C)) R)) (bv_unsigned (eval rho' (ax_base C))) (b, l)).
  { intros b l Hr. pose proof (proj1 (Forall_forall _ _) Hsh _ Hr) as Hx.
    pose proof (proj1 (forallb_forall _ _) HXC _ Hr) as Hbl. unfold xr_below in Hbl. cbn [fst snd] in Hbl. apply andb_prop in Hbl as [Hb1 Hl1].
    unfold xr_ok in Hx |- *. cbn [fst snd] in Hx |- *.
    rewrite <- (eval_agree (ss_next (ax_S C)) rho rho' b A1 Hb1).
    rewrite <- (eval_agree (ss_next (ax_S C)) rho rho' l A1 Hl1).
    rewrite EbC.
    destruct Hx as (H8 & Hnw & Hx). split; [exact H8|]. split; [exact Hnw|].
    intros a Ha. destruct (Hx a Ha) as (Hoff & Hout & Hwd & v & Hv & Henc).
    split; [exact Hoff|]. split; [exact (OUT _ Hout)|]. split.
    - intros j Hj. destruct (Hwd j Hj) as [Hoj Hrj]. split; [exact (OUT _ Hoj) | rewrite <- Arm; exact Hrj].
    - exists v. rewrite <- Arm. split; [exact Hv | exact Henc]. }
  apply Forall_app. split.
  - apply Forall_forall. intros [b l] Hr. exact (KEEP b l Hr).
  -
    apply Forall_forall. intros r' Hr'. apply in_map_iff in Hr' as ([b l] & <- & Hr).
    pose proof (proj1 (forallb_forall _ _) HxfL _ Hr) as FRx. apply existsb_exists in FRx as (rP & HrP & Exr).
    apply xr_eqb_sound in Exr. subst rP.
    pose proof (proj1 (forallb_forall _ _) HXv _ Hr) as Hvv. cbn [fst snd] in Hvv. apply andb_prop in Hvv as [Hvb Hvl].
    pose proof (proj1 (forallb_forall _ _) HXb _ Hr) as Hbl. unfold xr_below in Hbl. cbn [fst snd] in Hbl. apply andb_prop in Hbl as [Hbb' Hlb].

    pose proof (proj1 (forallb_forall _ _) HXcov _ HrP) as Hcov.
    pose proof (smatch_facts segs _ _ _ Hsm) as HfC.
    pose proof (xr_covered_sound rho (ss_facts (ax_S C)) (ss_objs (ax_S C)) (bv_unsigned (eval rho (ax_base C))) (ax_X C) (xr_subst s (b, l)) HfC Hcov Hsh) as HokC.

    assert (HwfPre : axwf Pre = true).
    { rewrite entails_frA_ref_eq in He. unfold entails_frA_ref in He. rewrite Hfr in He.
      match type of He with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
      apply andb_prop in Hc as [_ Hc]. exact Hc. }
    unfold axwf in HwfPre. apply andb_prop in HwfPre as [HXP _].
    pose proof (proj1 (forallb_forall _ _) HXP _ HrP) as HbP. unfold xr_below in HbP. cbn [fst snd] in HbP. apply andb_prop in HbP as [HbP1 HbP2].
    assert (Eb : eval rho' (sv_subst (import_sub s (ss_next (ax_S Pre)) (ax_S L) (ss_next (ax_S C))) b) = eval rho (sv_subst s b)).
    { rewrite (call_link_eval rho (vms md tp ms) R s (ax_S Pre) (ax_S C) (ax_S L) rho' rhoL b HLK Hvb Hbb').
      rewrite <- (eval_agree (ss_next (ax_S Pre)) _ rhoL b HagL HbP1). rewrite <- eval_subst. apply eval_absorb. }
    assert (El : eval rho' (sv_subst (import_sub s (ss_next (ax_S Pre)) (ax_S L) (ss_next (ax_S C))) l) = eval rho (sv_subst s l)).
    { rewrite (call_link_eval rho (vms md tp ms) R s (ax_S Pre) (ax_S C) (ax_S L) rho' rhoL l HLK Hvl Hlb).
      rewrite <- (eval_agree (ss_next (ax_S Pre)) _ rhoL l HagL HbP2). rewrite <- eval_subst. apply eval_absorb. }
    unfold xr_ok in HokC |- *. unfold xr_subst in HokC |- *. cbn [fst snd] in HokC |- *.
    rewrite Eb, El, EbC.
    destruct HokC as (H8 & Hnw & HokC). split; [exact H8|]. split; [exact Hnw|].
    intros a Ha. destruct (HokC a Ha) as (Hoff & Hout & Hwd & v & Hv & Henc).
    split; [exact Hoff|]. split; [exact (OUT _ Hout)|]. split.
    + intros j Hj. destruct (Hwd j Hj) as [Hoj Hrj]. split; [exact (OUT _ Hoj) | rewrite <- Arm; exact Hrj].
    + exists v. rewrite <- Arm. split; [exact Hv | exact Henc].
Qed.

Theorem call_soundA : ltac2:(tb__ "0|3|
S4bOF_;S3dS3dS3dS3dS0S0S47S1fSeA1M0S1fS2A1S4eSdS1fS43Q40A1A1M1S2fS22G0A1S51R8R7R6A3S25G0R5A2A3S2fS21S55R9R8R7R6S6aS2S0S5R5A4A5S26A3SdG1S4dVsegs;R11S3cVsegs;RfRbR2R1A5S3eVsegs;ReSfS1RbA1A1R2R1R8A6A4Ftp1;Frho1;S1fS2eA1M2S3aS2dS3bVsegs;R8R7ReS20G2S40R3S41R2R1A2A4A5R13R9R8R4R2A4R13S46S45RaRdS34R3R9R4A3A3ReA2R9R5R3A4F_;F_;Fmd;Fms;Ftr;S2SdSdG1G2S3aS2dG2S2dS37S2R9R11A3S3bVsegs;R10RfR16S20G2S40R6S41R5R4A2A4A5R1bR11R10R7R5A4S5fR12S34R6R11R7A3R15R16S1R17A1S1R18A1S1S5RcA1A1RbRaA9R1bRbRaR6R5A4R1bRdRbR7R6A4F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FtpL;FrhoL;Frho';FL;S2SdG1S37S2R3RcA3S15SfS1R11A1A1RbR3A3S4dVsegs;R17S3cVsegs;R13S52R10R11S5R5A1R12RfA5R4R3A5RdA4F_;F_;FtpL;Frho';FL;S4dVsegs;R13S3cVsegs;R12ReR8R7A5R9A4F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJc;FJp';FJp;FJ;Fok;").
Proof using .
  intros ok J Jp Jp' Jc C Pre s R Posts Q rho tp He Hchk Hsum Hin Hout Hcont.
  intros n HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound C Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp n); [|split; [exact HsmPre|exact (Hin tr ms md Hsm Hk)]].
  intros w' (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (import_post_linkA C Pre s R (map la_state Posts) rho tp tr ms md tr' ms' md' (la_state L) rhoL tp He Hchk Hsm
              ltac:(apply in_map_iff; exists L; auto) HagL HsmL) as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  apply (Hcont L rho' tp HinL HAG n HgQ). split; [exact HSP|].
  exact (Hout L rho' rhoL tp tr ms md tr' md' HinL Hsm Hk HLK Hk').
Qed.

Theorem call_completeA : ltac2:(tb__ "0|3|
S3dS3dS3dS3dS0S0S47S1fSeA1M0S1fS2A1S4bOF_;SdS1fS43Q40A1A1M1S2fS22G0A1S51R8R7R6A3S25G0R5A2A3S2fS21S55R9R8R7R6S6aS2S0S5R5A4A5S26A3SdG1S4cVsegs;S3cVsegs;RfRbR2R1A5S3eVsegs;ReSfS1RbA1A1R2R1R8A6A3Ftp1;Frho1;S1fS2eA1M2S3aS2dS3bVsegs;R8R7ReS20G2S40R3S41R2R1A2A4A5R13R9R8R4R2A4R13S46S45RaRdS34R3R9R4A3A3ReA2R9R5R3A4F_;F_;Fmd;Fms;Ftr;S2SdSdG1G2S3aS2dG2S2dS37S2R9R11A3S3bVsegs;R10RfR16S20G2S40R6S41R5R4A2A4A5R1bR11R10R7R5A4S5fR12S34R6R11R7A3R15R16S1R17A1S1R18A1S1S5RcA1A1RbRaA9R1bRbRaR6R5A4R1bRdRbR7R6A4F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FtpL;FrhoL;Frho';FL;S2SdG1S37S2R3RcA3S15SfS1R11A1A1RbR3A3S4cVsegs;S3cVsegs;R13S52R10R11S5R5A1R12RfA5R4R3A5RdA3F_;F_;FtpL;Frho';FL;S4cVsegs;S3cVsegs;R12ReR8R7A5R9A3F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJc;FJp';FJp;FJ;").
Proof using .
  intros J Jp Jp' Jc C Pre s R Posts Q rho tp He Hchk Hsum Hin Hout Hcont.
  intros w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound C Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  destruct (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp _ (conj HsmPre (Hin tr ms md Hsm Hk))) as (w' & Hsteps & HLQ).
  destruct HLQ as (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (import_post_linkA C Pre s R (map la_state Posts) rho tp tr ms md tr' ms' md' (la_state L) rhoL tp He Hchk Hsm
              ltac:(apply in_map_iff; exists L; auto) HagL HsmL) as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  destruct (Hcont L rho' tp HinL HAG _ (conj HSP (Hout L rho' rhoL tp tr ms md tr' md' HinL Hsm Hk HLK Hk'))) as (w'' & Hsteps' & HQ).
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.

End SA.
