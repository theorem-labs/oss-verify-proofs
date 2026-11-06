(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "pair"; "cons"; "nil"; "prod"; "Some"; "false"; "nat"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "agree_below"; "sprop"; "holds"; "ss_next"; "sobj"; "outside_all"; "ss_facts"; "ss_lenient"; "sstate"; "smatch"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "axst"; "ax_S"; "la_state"; "xr_ok"; "entailsA"; "sym_runA"; "prov"; "pv_ok"; "xr_covered"; "xr_eqb"; "xr_sub"; "xr_sub_pv"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "eq"; "False"; "and"; "ex"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "etriple"; "assn"; "triple1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "LQA"; "stableA"; "ok_frameA"; "smatchA"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "wsub_id_below"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymSoundR SymFrame SymEntail.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.EntailFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section E.
Variable segs : list Segment.

Lemma xr_eqb_sound : ltac2:(tb__ "0|1|
S6ScScA2M0G0S26S1S22R2R1A2S2A3S26G0R3R2A3F_;Fb;Fa;").
Proof.
  intros [a1 a2] [b1 b2] H. unfold xr_eqb in H. cbn in H. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. subst. reflexivity.
Qed.

Lemma entails_outside : ltac2:(tb__ "0|2|
S15S15S3bSbS0S40A1M0S42S41S25Q40A1S26S1S43R8R7R6A3S2A3S16Vsegs;R6R9S3G0S3eR5S3fR4R3A2A4A4S12R7S17RaA1M1R3A3S12S3aR8R9A2G1R4A3F_;F_;F_;Fa;Fmd;Fms;Ftr;Frho;Fs;FT;FL;").
Proof using .
  intros L T s rho tr ms md a He Hsm Hout. apply Forall_forall. intros oT HoT.
  destruct (entails_ranges segs L T s rho tr ms md He Hsm oT HoT) as (oL & HoL & E).
  cbn zeta. rewrite E. exact (proj1 (Forall_forall _ _) Hout oL HoL).
Qed.

Lemma xr_ok_sub_pv : ltac2:(tb__ "0|1|
SbS1fS0S11A1S38ScScScScS20R8R7A2S26S1S24R8S3ScScR3R2A4S3ScScR5R4A4M0A3S2A3S1cRaR8R7S3ScScR6R5A4A4S1cRbR9R8G0A4F_;F_;F_;Fl';Fb';Fl;Fb;Foff;Fobjs;Fpv;Frho;").
Proof using .
  intros rho pv objs off b l b' l' Hpv H Hok. pose proof Hpv as (Hf & _ & _). set (facts := pv_facts pv) in *.
  unfold xr_sub_pv in H. cbn [fst snd] in H. fold facts in H.
  apply lazy_andb_prop in H as [Hal H]. apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [Hnw H].
  apply lazy_andb_prop in H as [H2 Hend].
  pose proof (puleq_sound rho _ _ _ _ Hpv H1) as A1. pose proof (puleq_sound rho _ _ _ _ Hpv H2) as A2.
  pose proof (puleq_sound rho _ _ _ _ Hpv Hnw) as A3.
  apply Z.leb_le in Hal. destruct (align_sv_sound rho facts b' Hf) as [_ Hdiv].
  unfold xr_ok in Hok |- *. cbn [fst snd] in Hok |- *.
  destruct Hok as (HB8 & HBL & Hall).
  unfold U in A1, A2, A3. cbn [eval] in A1, A2, A3. rewrite !add_val in A2. rewrite add_val in A3.
  pose proof (urange (eval rho b)) as Rb. pose proof (urange (eval rho l)) as Rl.
  pose proof (urange (eval rho b')) as Rb'. pose proof (urange (eval rho l')) as Rl'.
  set (B := bv_unsigned (eval rho b)) in *. set (L := bv_unsigned (eval rho l)) in *.
  set (B' := bv_unsigned (eval rho b')) in *. set (L' := bv_unsigned (eval rho l')) in *.
  assert (HB'8 : B' mod 8 = 0).
  { apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hdiv]. exists (2 ^ (align_sv facts b' - 3)).
    change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }

  assert (Hnw' : B' + L' < 2 ^ 64 \/ L' = 0).
  { destruct (Z.eq_dec L' 0) as [|Hne]; [right; lia | left].
    destruct (Z_lt_le_dec (B' + L') (2 ^ 64)) as [Hlt|Hge]; [exact Hlt|]. exfalso.
    rewrite <- (Z.mod_add _ (-1)) in A3 by lia. rewrite Z.mod_small in A3; lia. }
  assert (HE' : L' = 0 \/ (B' + L' < 2 ^ 64 /\ B' + L' <= B + L)).
  { destruct Hnw' as [Hlt | Hz]; [right | left; exact Hz]. split; [exact Hlt|].
    rewrite (Z.mod_small (B' + L')) in A2 by lia.
    destruct (Z.eq_dec (B + L) (2 ^ 64)) as [E|E]; [lia|]. rewrite Z.mod_small in A2; lia. }
  split; [exact HB'8|]. split; [lia|].
  intros a Ha. destruct HE' as [Hz | [Hlt Hle]]; [lia|].
  destruct (Hall a ltac:(lia)) as (Hoff & Hout & Hwd & v & Hv & Henc).
  split; [exact Hoff|]. split; [exact Hout|]. split; [exact Hwd|]. exists v. split; [exact Hv|].
  destruct Henc as [H0 | [Hv8 Hq]]; [left; exact H0|].
  destruct (Z.eq_dec (bv_unsigned v) 0) as [Z0|Z0]; [left; exact Z0|]. right.
  pose proof (Z.div_mod (B + L) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (B + L) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ma.
  apply lazy_orb_prop in Hend as [Hl8 | Heq].
  -
    exfalso. apply Z.leb_le in Hl8. destruct (align_sv_sound rho facts l' Hf) as [_ HdivL].
    assert (HL'8 : L' mod 8 = 0).
    { apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact HdivL]. exists (2 ^ (align_sv facts l' - 3)).
      change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    pose proof (Z.div_mod (B' + L') 8 ltac:(lia)) as D2.
    assert (HS8 : (B' + L') mod 8 = 0) by (rewrite Z.add_mod, HB'8, HL'8 by lia; reflexivity).

    rewrite Hq in Da. rewrite HS8 in D2. lia.
  - pose proof (puleq_sound rho _ _ _ _ Hpv Heq) as A4. unfold U in A4. cbn [eval] in A4. rewrite !add_val in A4.
    fold B L B' L' in A4. rewrite (Z.mod_small (B' + L')) in A4 by lia.
    destruct (Z.eq_dec (B + L) (2 ^ 64)) as [E|E].
    + exfalso. rewrite E, Z.mod_same in A4 by lia. lia.
    + rewrite Z.mod_small in A4 by lia. assert (EE : B' + L' = B + L) by lia. rewrite EE. split; assumption.
Qed.

Lemma xr_ok_sub : ltac2:(tb__ "0|1|
SbS0SeA1S0S11A1S38ScScScScS39SeSfR8A1R7A3S26S1S23R8S3ScScR3R2A4S3ScScR5R4A4M0A3S2A3S1cRaR8R7S3ScScR6R5A4A4S1cRbR9R8G0A4F_;F_;F_;Fl';Fb';Fl;Fb;Foff;Fobjs;Ffacts;Frho;").
Proof using .
  intros rho facts objs off b l b' l' Hf H Hok. unfold xr_sub in H.
  eapply xr_ok_sub_pv; [exact (mk_prov_ok rho facts Hf) | exact H | exact Hok].
Qed.

Lemma xr_covered_sound : ltac2:(tb__ "0|1|
SbS0SeA1S0S11A1S38S0S6ScScA2M0A1G0S39SeSfR6A1R5A3S26S1S21R6R3R2A3S2A3S39G0S1cR8R6R5A3R4A3S1cR9R7R6R4A4F_;F_;F_;Fr';FX;Foff;Fobjs;Ffacts;Frho;").
Proof using .
  intros rho facts objs off X [b' l'] Hf H HX. unfold xr_covered in H. apply lazy_orb_prop in H as [H|H].
  - apply existsb_exists in H as (r & Hr & Heq). apply xr_eqb_sound in Heq. subst r.
    exact (proj1 (Forall_forall _ _) HX _ Hr).
  - apply existsb_exists in H as ([b l] & Hr & Hsub).
    eapply xr_ok_sub_pv; [exact (mk_prov_ok rho facts Hf) | exact Hsub | exact (proj1 (Forall_forall _ _) HX _ Hr)].
Qed.

Lemma smatchA_entails : ltac2:(tb__ "0|0|
S19S19S3bSbS0S25Q40A1A1S6S0S40A1S3eA2S26S1S1dR6R5R4A3S2A3S36Vsegs;R4R3R7R2A5S36Vsegs;S3aR5R6A2R4R7R3A5F_;F_;Fw;Ftp;Frho;Fs;FT;FL;").
Proof using .
  intros L T s rho tp [tr [ms md]] He (Hsm & HMI & Hwf & Hsh & Hhz). rewrite entailsA_ref_eq in He. unfold entailsA_ref in He.
  apply andb_prop in He as [He HwfT]. apply andb_prop in He as [He Hb]. apply andb_prop in He as [He HX].
  split; [eapply entails_sound; eauto|]. split; [exact HMI|]. split; [exact HwfT|]. split; [|exact Hhz].
  unfold shadow_ok in Hsh |- *. apply sv_eqb_sound in Hb. rewrite <- eval_subst, Hb.
  pose proof (smatch_facts segs _ _ _ Hsm) as Hf.

  apply Forall_forall. intros r Hr.
  pose proof (proj1 (forallb_forall _ _) HX r Hr) as Hx.
  pose proof (xr_covered_sound rho (ss_facts (ax_S L)) (ss_objs (ax_S L)) (bv_unsigned (eval rho (ax_base L))) (ax_X L) (xr_subst s r) Hf Hx Hsh) as Hok.
  destruct r as [b l]. unfold xr_ok in Hok |- *. unfold xr_subst in Hok. cbn [fst snd] in Hok |- *. rewrite <- !eval_subst.
  destruct Hok as (H8 & Hnw & Hok). split; [exact H8|]. split; [exact Hnw|].
  intros a Ha. destruct (Hok a Ha) as (Hoff & Hout & Hwd & v & Hv & Henc).
  unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
  split; [exact Hoff|]. split; [|split].
  - eapply entails_outside; eauto.
  - intros j Hj. destruct (Hwd j Hj) as [Hoj Hrj]. split; [eapply entails_outside; eauto | cbn; exact Hrj].
  - exists v. split; [|exact Henc]. cbn. exact Hv.
Qed.

Lemma SPA_entails : ltac2:(tb__ "0|0|
S32S37S19S19S3bSbS0S25Q40A1A1S2cS26S1S1dR6R5R4A3S2A3S26S1S3cR5R8A2S2A3S34Vsegs;R9RaA3S31Vsegs;RbR9R6R5R4A6S31Vsegs;RcR9S3aR7R8A2R6R5A6F_;F_;F_;F_;Fw;Ftp;Frho;Fs;FT;FL;Fg;FJ;").
Proof using .
  intros J g L T s rho tp w He Hid Hst [Hsm Hk]. split.
  - eapply smatchA_entails; eauto.
  - eapply Hst; [apply rho_sub_agree; exact Hid | apply mat_equiv_refl | exact Hk].
Qed.

Lemma LQA_nil : ltac2:(tb__ "0|0|
S32S37SbS0S25Q40A1A1S2cS2aS33Vsegs;R5R4R3R2S5S18A1R1A7A1Fw;Ftp;Frho;Fn;FJ;").
Proof using . intros J n rho tp w (L & rho' & Hin & _). exact Hin. Qed.

Lemma LQA_cons_inv : ltac2:(tb__ "0|0|
S32S37SbS0S25Q40A1A1S18S0S18A1S2cS33Vsegs;R7R6R5R4S4S18R3R2A3R1A7S2bS29SbSbS28SdR8R7R1A3S31Vsegs;R9S1bR5A1R1R6R3A6A2Lrho';A2S33Vsegs;R8R7R6R5R3R2A7A2F_;Fw;Frest;FL;Ftp;Frho;Fn;FJ;").
Proof using .
  intros J n rho tp L rest w (L' & rho' & [<-|Hin] & Hag & Hsm & Hk).
  - left. exists rho'. split; [exact Hag|]. split; assumption.
  - right. exists L', rho'. auto.
Qed.

Lemma LQA_intro : ltac2:(tb__ "0|0|
S32S37SbS0S25Q40A1A1S18S0S18A1SbS2cS3dS18R4R3A3SdR8R7R3A3S31Vsegs;RaS1bR6A1R4R7R3A6S33Vsegs;RbRaR9R8R6R4A7F_;F_;F_;Fw;Frho';Fleaves;FL;Ftp;Frho;Fn;FJ;").
Proof using . intros J n rho tp L leaves rho' w Hin Hag [Hsm Hk]. exists L, rho'. auto. Qed.

Lemma triple_leavesA_nil : ltac2:(tb__ "0|0|
S2cOF_;S32S37SbS0S25Q40A1A1S2fS2dVsegs;R6S33Vsegs;R5R4R3R2S5S18A1A6R1A4FQ;Ftp;Frho;Fn;FJ;Fok;").
Proof using . intros ok J n rho tp Q m Hg w Hw. exfalso. exact (LQA_nil J n rho tp w Hw). Qed.

Lemma triple_leavesA_cons : ltac2:(tb__ "0|0|
S2cOF_;S32S37SbS0S25Q40A1A1S18S0S18A1S2fSbSdR7R6R1A3S2dVsegs;RaS31Vsegs;R9S1bR5A1R2R6A5R3A4F_;Frho';S2dVsegs;R9S33Vsegs;R8R7R6R5R3A6R2A4S2dVsegs;RaS33Vsegs;R9R8R7R6S4S18R5R4A3A6R3A4F_;F_;FQ;Frest;FL;Ftp;Frho;Fn;FJ;Fok;").
Proof using .
  intros ok J n rho tp L rest Q H1 H2 m Hg w Hw.
  destruct (LQA_cons_inv J n rho tp L rest w Hw) as [(rho' & Hag & Hsp)|Hrest].
  - exact (H1 rho' Hag m Hg w Hsp).
  - exact (H2 m Hg w Hrest).
Qed.

Lemma etriple_leavesA_nil : ltac2:(tb__ "0|0|
S32S37SbS0S25Q40A1A1S2cOF_;S2eVsegs;S33Vsegs;R5R4R3R2S5S18A1A6R1A3FQ;Ftp;Frho;Fn;FJ;").
Proof using . intros J n rho tp Q w Hw. exfalso. exact (LQA_nil J n rho tp w Hw). Qed.

Lemma etriple_leavesA_cons : ltac2:(tb__ "0|0|
S32S37SbS0S25Q40A1A1S18S0S18A1S2cOF_;SbSdR7R6R1A3S2eVsegs;S31Vsegs;R9S1bR5A1R2R6A5R3A3F_;Frho';S2eVsegs;S33Vsegs;R8R7R6R5R3A6R2A3S2eVsegs;S33Vsegs;R9R8R7R6S4S18R5R4A3A6R3A3F_;F_;FQ;Frest;FL;Ftp;Frho;Fn;FJ;").
Proof using .
  intros J n rho tp L rest Q H1 H2 w Hw.
  destruct (LQA_cons_inv J n rho tp L rest w Hw) as [(rho' & Hag & Hsp)|Hrest].
  - exact (H1 rho' Hag w Hsp).
  - exact (H2 w Hrest).
Qed.

Lemma triple_leafA_absurd : ltac2:(tb__ "0|0|
S2cOF_;S32S19SbS0S25Q40A1A1S2fS39SeSfR3A1S13S1aR4A1A1A3S27F_;S2dVsegs;R7S31Vsegs;R6R5R4R3A5R2A4F_;FQ;Ftp;Frho;FA;FJ;Fok;").
Proof using .
  intros ok J A rho tp Q H m Hg w [Hsm _]. exfalso. apply H. eapply smatchA_facts; exact Hsm.
Qed.

Lemma etriple_leafA_absurd : ltac2:(tb__ "0|0|
S32S19SbS0S25Q40A1A1S2cOF_;S39SeSfR3A1S13S1aR4A1A1A3S27F_;S2eVsegs;S31Vsegs;R6R5R4R3A5R2A3F_;FQ;Ftp;Frho;FA;FJ;").
Proof using .
  intros J A rho tp Q H w [Hsm _]. exfalso. apply H. eapply smatchA_facts; exact Hsm.
Qed.

Lemma triple_entailsA : ltac2:(tb__ "0|0|
S2cOF_;S32S37S19S19S3bSbS0S25Q40A1A1S2fS26S1S1dR6R5R4A3S2A3S26S1S3cR5R8A2S2A3S34Vsegs;R9RaA3S2dVsegs;RcS31Vsegs;RbR8S3aR6R7A2R5A5R4A4S2dVsegs;RdS31Vsegs;RcRaR7R6A5R5A4F_;F_;F_;F_;FQ;Ftp;Frho;Fs;FT;FL;Fg;FJ;Fok;").
Proof using .
  intros ok J g L T s rho tp Q He Hid Hst HT. eapply triple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. eapply SPA_entails; eauto.
Qed.

Lemma etriple_entailsA : ltac2:(tb__ "0|0|
S32S37S19S19S3bSbS0S25Q40A1A1S2cOF_;S26S1S1dR6R5R4A3S2A3S26S1S3cR5R8A2S2A3S34Vsegs;R9RaA3S2eVsegs;S31Vsegs;RbR8S3aR6R7A2R5A5R4A3S2eVsegs;S31Vsegs;RcRaR7R6A5R5A3F_;F_;F_;F_;FQ;Ftp;Frho;Fs;FT;FL;Fg;FJ;").
Proof using .
  intros J g L T s rho tp Q He Hid Hst HT. eapply etriple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. eapply SPA_entails; eauto.
Qed.

Lemma triple_LQA_of_leaves : ltac2:(tb__ "0|0|
S2cOF_;S32S37SbS0S25Q40A1A1S0S18A1S2fS18SbS3dS18R2R4A3SdR8R7R2A3S2dVsegs;RbS31Vsegs;RaS1bR4A1R3R7A5R5A4F_;F_;Frho';FL;S2dVsegs;R8S33Vsegs;R7R6R5R4R3A6R2A4F_;FQ;Fleaves;Ftp;Frho;Fn;FJ;Fok;").
Proof using .
  intros ok J n rho tp leaves Q H m Hg w (L & rho' & Hin & Hag & Hsm & Hk).
  exact (H L rho' Hin Hag m Hg w (conj Hsm Hk)).
Qed.

Lemma etriple_LQA_of_leaves : ltac2:(tb__ "0|0|
S32S37SbS0S25Q40A1A1S0S18A1S2cOF_;S18SbS3dS18R2R4A3SdR8R7R2A3S2eVsegs;S31Vsegs;RaS1bR4A1R3R7A5R5A3F_;F_;Frho';FL;S2eVsegs;S33Vsegs;R7R6R5R4R3A6R2A3F_;FQ;Fleaves;Ftp;Frho;Fn;FJ;").
Proof using .
  intros J n rho tp leaves Q H w (L & rho' & Hin & Hag & Hsm & Hk).
  exact (H L rho' Hin Hag w (conj Hsm Hk)).
Qed.

Theorem sym_run_soundA : ltac2:(tb__ "0|1|
S9S0S38A1S19S0S18A1M0S2cOF_;S32SbS0S25Q40A1A1S26SaG0A1S1eVsegs;R8R7R6S2A5S7G0R5A2A3S35Vsegs;R5R4A3S26S1S14S1aR8A1A1S8A3S34Vsegs;S10S1aR9A1A1R6A3S30Vsegs;R8S31Vsegs;R7RaR6R5A5S33Vsegs;R7S10S1aRaA1A1R6R5R9A6A4F_;F_;F_;F_;Ftp;Frho;FJ;Fok;Fleaves;FA;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts A leaves ok J rho tp Hrun Hok Hlen Hst.
  exact (sym_run_sound_genA0 segs ok J Hok fuel cuts A true leaves rho tp Hlen Hst Hrun).
Qed.

Theorem sym_run_sound_genA : ltac2:(tb__ "0|3|
S9S0S38A1S2cOF_;S32S35Vsegs;R2R1A3S19S1S0S18A1M0SbS0S25Q40A1A1S26S1S14S1aR5A1A1S8A3S34Vsegs;S10S1aR6A1A1R8A3S26SaG0A1S1eVsegs;RcRbR7R6A5S7G0R5A2A3S1OLfirst;R7S30Vsegs;RbS31Vsegs;RaR8R5R4A5M1S33Vsegs;RaS10S1aR8A1A1R5R4R6A6M2A4S2dVsegs;RbG1G2A4X1x2F_;F_;F_;Ftp;Frho;Fleaves;Ffirst;FA;F_;FJ;Fok;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts ok J Hok A first leaves rho tp Hlen Hst Hrun.
  exact (sym_run_sound_genA0 segs ok J Hok fuel cuts A first leaves rho tp Hlen Hst Hrun).
Qed.

End E.
