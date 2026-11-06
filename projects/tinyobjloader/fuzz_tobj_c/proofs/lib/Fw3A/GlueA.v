(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "pair"; "true"; "prod"; "Some"; "fst"; "option"; "snd"; "app"; "length"; "nat"; "nil"; "andb"; "false"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sobj"; "sv"; "sprop"; "ss_objs"; "sstate"; "holds"; "ss_next"; "eval"; "ss_facts"; "SLit"; "obj_range"; "DZero"; "cell"; "mem_match"; "mkObj"; "outside_all"; "ranges_disjoint"; "sprop_below"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "shadow_ok"; "ax_X"; "ax_base"; "mkAX"; "word_byte"; "xr_below"; "xr_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "etriple"; "assn"; "w_cfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "page_size"; "Model"; "event"; "page_base"; "m_vm_lazy"; "page_in_ranges"; "m_vmmaps"; "vm_noaccess"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "ge"; "of_nat"; "div"; "pow"; "@Corelib.Lists.ListDef"; "Forall"; "@Stdlib.Lists.List"; "In"; "forallb"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_ms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA.G"; "xshadow_outside"; "ax_setX"; "in_page"; "ax_with_facts"; "zero_page_obj"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "MI"; "headroom"; "hid"; "paid"; "unpaid"; "virt"; "vms"; "@LinuxProcessSemantics.Riscv.Prelude"; "bv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "diffs_ok"; "same_but_objs"; "state_diff"; "with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymSoundF SymSoundR SymFrame SymEntail SymCFG SymCall Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section G.
Variable segs : list Segment.

Lemma SPA_facts_hold : ltac2:(tb__ "0|0|
S12S1aS31S0S13Q40A1A1S3aS11Vsegs;R5R3R4R2R1A6S4fS1dS20R5A1S23S30R4A1A1A3F_;Fw;Ftp;FA;Frho;FJ;").
Proof using . intros J rho A tp w [Hsm _]. eapply smatchA_facts; eauto. Qed.

Lemma triple_factsA : ltac2:(tb__ "0|1|
S3aOF_;S12S31S1aS0S13Q40A1A1S3dS4fS1dS20R3A1S23S30R4A1A1A3S3bVsegs;R7S11Vsegs;R6R5R4R3A5R2A4M0F_;G0F_;FQ;Ftp;Frho;FA;FJ;Fok;").
Proof using .
  intros ok J A rho tp Q H n Hg w Hw. apply H; [|exact Hg|exact Hw]. eapply SPA_facts_hold. exact Hw.
Qed.

Lemma etriple_factsA : ltac2:(tb__ "0|1|
S12S31S1aS0S13Q40A1A1S3aOF_;S4fS1dS20R3A1S23S30R4A1A1A3S3cVsegs;S11Vsegs;R6R5R4R3A5R2A3M0F_;G0F_;FQ;Ftp;Frho;FA;FJ;").
Proof using .
  intros J A rho tp Q H w Hw. apply H; [|exact Hw]. eapply SPA_facts_hold. exact Hw.
Qed.

Lemma triple_SPA_pure : ltac2:(tb__ "0|2|
S3aOF_;S12S31S1aS0S13Q40A1A1M0S3dS0S41A1M1S40R7R5R4R2R1A4S3bVsegs;R9S11Vsegs;S1aG0G1S40S17RcR4R3R2R1A4S17S16G1R2R7A3S16S40R1R6A3A2A2Lm;Lt;Lp;Lr;R7R6R5A5R4A4F_;Fmd;Ftr;S3bVsegs;R7S11Vsegs;R6R5R4R3A5R2A4F_;FQ;Ftp;Frho;FA;FJ;Fok;").
Proof using .
  intros ok J A rho tp Q H n Hg w [Hsm Hk]. destruct w as [tr [ms md]].
  apply (H tr md Hk n Hg). split; [exact Hsm|]. cbn. auto.
Qed.

Lemma triple_SPA_ex : forall (ok : world -> Prop) (T : Type) (J : T -> jpredA) A rho tp (Q : assn),
  (forall x, triple segs ok (SPA segs (J x) A rho tp) Q) ->
  triple segs ok (SPA segs (fun r p t m => exists x, J x r p t m) A rho tp) Q.
Proof using .
  intros ok T J A rho tp Q H n Hg w [Hsm [x Hx]]. exact (H x n Hg w (conj Hsm Hx)).
Qed.

Lemma triple_SPA_pure_and : ltac2:(tb__ "0|1|
S3aOF_;OS12S31S1aS0S13Q40A1A1M0S3dR6S3bVsegs;R8S11Vsegs;R6R5R4R3A5R2A4F_;S3bVsegs;R8S11Vsegs;S1aG0S0S41A1S40S17RbRaR4R3R2R1A4A2Lm;Lt;Lp;Lr;R5R4R3A5R2A4F_;FQ;Ftp;Frho;FA;FJ;FX;Fok;").
Proof using .
  intros ok X J A rho tp Q H n Hg w [Hsm [HX HJ]]. exact (H HX n Hg w (conj Hsm HJ)).
Qed.

Lemma etriple_SPA_ex : forall (T : Type) (J : T -> jpredA) A rho tp (Q : world -> Prop),
  (forall x, etriple segs (SPA segs (J x) A rho tp) Q) ->
  etriple segs (SPA segs (fun r p t m => exists x, J x r p t m) A rho tp) Q.
Proof using .
  intros T J A rho tp Q H w [Hsm [x Hx]]. exact (H x w (conj Hsm Hx)).
Qed.

Lemma etriple_SPA_pure_and : ltac2:(tb__ "0|1|
OS12S31S1aS0S13Q40A1A1M0S3aOF_;R6S3cVsegs;S11Vsegs;R6R5R4R3A5R2A3F_;S3cVsegs;S11Vsegs;S1aG0S0S41A1S40S17RbRaR4R3R2R1A4A2Lm;Lt;Lp;Lr;R5R4R3A5R2A3F_;FQ;Ftp;Frho;FA;FJ;FX;").
Proof using .
  intros X J A rho tp Q H w [Hsm [HX HJ]]. exact (H HX w (conj Hsm HJ)).
Qed.

Lemma triple_SPA_conseq_J : ltac2:(tb__ "0|0|
S3aOF_;S12S12S31S1aS0S13Q40A1A1S3dS0S41A1S40R8R5R4R2R1A4R8R6R5R3R2A4F_;Fm;Ft;S3bVsegs;R8S11Vsegs;R6R5R4R3A5R2A4S3bVsegs;R9S11Vsegs;R8R6R5R4A5R3A4F_;F_;FQ;Ftp;Frho;FA;FJ';FJ;Fok;").
Proof using .
  intros ok J J' A rho tp Q HJ H n Hg w [Hsm Hk]. exact (H n Hg w (conj Hsm (HJ _ _ Hk))).
Qed.

Lemma etriple_SPA_conseq_J : ltac2:(tb__ "0|0|
S12S12S31S1aS0S13Q40A1A1S3aOF_;S0S41A1S40R8R5R4R2R1A4R8R6R5R3R2A4F_;Fm;Ft;S3cVsegs;S11Vsegs;R6R5R4R3A5R2A3S3cVsegs;S11Vsegs;R8R6R5R4A5R3A3F_;F_;FQ;Ftp;Frho;FA;FJ';FJ;").
Proof using .
  intros J J' A rho tp Q HJ H w [Hsm Hk]. exact (H w (conj Hsm (HJ _ _ Hk))).
Qed.

Definition ax_with_facts (A : axst) (f : list sprop) : axst := ltac2:(tb__ "0|0|
S32VA;S67S30VA;A1Vf;A2A2").

Lemma SPA_refacts : ltac2:(tb__ "0|0|
S12S1aS31S0S1dA1S0S13Q40A1A1S3aS11Vsegs;R6R4R5R2R1A6S16S1S51S1dS2cS21S30R5A1A1A1R4A3S4A3S4fS1dS20R7A1S23S30R6A1A1A3S4fS1dS20R8A1R6A3F_;S11Vsegs;R9S58R7R6A2R8R5R4A6F_;F_;F_;Fw;Ftp;Ff;FA;Frho;FJ;").
Proof using .
  intros J rho A f tp w [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] Hb Hf. split; [|exact Hk].
  split; [|split; [exact HMI | split; [exact Hwf | split; [exact Hsh | exact Hhz]]]].
  apply smatch_refacts; [exact Hsm | exact Hb |]. apply Hf. eapply smatch_facts_hold; eauto.
Qed.

Lemma SPA_restate : ltac2:(tb__ "0|3|
S12S1aS31S1fS0S13Q40A1A1S3aS0S5S1cS1cA2A1M0S0S1dA1M1S16S1S2dR5A1S4A3S16S8S5G0G1A2M2A1S66S30R7A1R6A2S6G2S3G0G1R3R2A4A2A3S16S2fS21R7A1S21S30R8A1A1A3S64RaR5A2S4fS1dS20RbA1R5A3S11Vsegs;RdRbRcR9R8A6S11Vsegs;ReS32RcRbA2RdRaR9A6F_;F_;F_;F_;F_;F_;Fnf;Fd;Fw;Ftp;FS';FA;Frho;FJ;").
Proof using .
  intros J rho A S' tp w d nf Hwf Hsd Hnx Hok Hnf [(Hsm & HMI & Hwfx & Hsh & Hhz) Hk]. split; [|exact Hk].
  split; [eapply smatch_restate; eauto|]. split; [exact HMI|]. split; [unfold axwf; cbn; rewrite Hnx; exact Hwfx|].
  split; [|exact Hhz].

  unfold state_diff in Hsd.
  destruct (ss_pc (ax_S A) =? ss_pc S'); [|discriminate].
  destruct (sfcsr_diff _ _) as [d0|]; [|discriminate]. destruct (osv_diff _ _) as [d0'|]; [|discriminate].
  destruct (svs_diff (ss_regs (ax_S A)) (ss_regs S')) as [d1|]; [|discriminate].
  destruct (svs_diff (ss_fregs (ax_S A)) (ss_fregs S')) as [d2|]; [|discriminate].
  destruct (objs_diff (ss_objs (ax_S A)) (ss_objs S')) as [d3|] eqn:Hod; [|discriminate].
  injection Hsd as E1 E2. subst d.
  assert (Hok3 : diffs_ok rho d3).
  { unfold diffs_ok in Hok |- *. rewrite !Forall_app in Hok. tauto. }
  pose proof (objs_diff_spec segs rho _ _ _ Hod Hok3) as HF.
  assert (HF1 : Forall2 (fun o o' => obj_range rho o' = obj_range rho o) (ss_objs (ax_S A)) (ss_objs S')).
  { clear -HF. induction HF; constructor; [exact (proj1 H) | assumption]. }
  apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_S ax_setS]. intros x _ Hout _.

  clear -HF1 Hout. revert Hout. induction HF1 as [|o o' t t' Ho Ht IH]; intros Hout; [constructor|].
  inversion Hout; subst. constructor; [|apply IH; assumption]. cbn zeta in *. rewrite Ho. assumption.
Qed.

Definition xshadow_outside (rho : valuation) (A : axst) (objs : list sobj) : Prop := ltac2:(tb__ "0|3|
S4fS5S1cS1cA2M0G0S14Q40M1S22Vrho;S7S1cS1cR1A3A2A2S2eS14G1S22Vrho;S9S1cS1cR2A3A2A2S2eS2eS2eS17S47R4R2A2S49R2S48R4R3A2A2A2S17S47Z0R2A2S49R2Z8M2A2A2S2aVrho;Vobjs;S37S48S14G1S22Vrho;S35VA;A1A2A2S4dR4G2A2A2R3A2A3F_;F_;Fj;Fa;TL;TB;Lr;S34VA;A1A3").

Lemma shadow_ok_outside : ltac2:(tb__ "0|0|
S1aS31S33R2R1A2S55R3R2S1eS30R2A1A1A3F_;FA;Frho;").
Proof using .
  intros rho A H. unfold shadow_ok, xshadow_outside in *. apply Forall_forall. intros [b l] Hr a j Ha Hj.
  pose proof (proj1 (Forall_forall _ _) H _ Hr) as X. unfold xr_ok in X. cbn [fst snd] in X, Ha.
  destruct X as (_ & _ & X). destruct (X a Ha) as (_ & _ & Hwd & _). exact (proj1 (Hwd j Hj)).
Qed.

Lemma shadow_ok_reobjs : ltac2:(tb__ "0|0|
S1aS31S1fS33R3R2A2S55R4R3S1eR2A1A3S33R5S32R4R3A2A2F_;F_;FS';FA;Frho;").
Proof using .
  intros rho A S' H Hout. unfold shadow_ok, xshadow_outside in *. cbn.
  apply Forall_forall. intros [b l] Hr.
  pose proof (proj1 (Forall_forall _ _) H _ Hr) as X. pose proof (proj1 (Forall_forall _ _) Hout _ Hr) as Y.
  unfold xr_ok in X |- *. cbn [fst snd] in X, Y |- *.
  destruct X as (H8 & Hnw & X). split; [exact H8|]. split; [exact Hnw|].
  intros a Ha. destruct (X a Ha) as (Ho & _ & Hwd & Hv). split; [exact Ho|]. split; [|split; [|exact Hv]].
  - unfold shadow_addr. rewrite <- (word_byte_self _ (proj1 Ho)). apply Y; [exact Ha|]. apply Z.mod_pos_bound. lia.
  - intros j Hj. split; [exact (Y a j Ha Hj) | exact (proj2 (Hwd j Hj))].
Qed.

Lemma SPA_reobj : ltac2:(tb__ "0|0|
S12S1aS31S1fS0S13Q40A1A1S3aS16S1S65S30R4A1R3A2S4A3S16S2fS21R4A1S21S30R5A1A1A3S11Vsegs;R8R6R7R4R3A6S28Vsegs;R8S1eR6A1S54S3eS61R5R4A2A1A1A4S55R9R8S1eR7A1A3S11Vsegs;RbS32R9R8A2RaR7R6A6F_;F_;F_;F_;F_;Fw;Ftp;FT;FA;Frho;FJ;").
Proof using .
  intros J rho A T tp [tr [ms md]] He Hnx [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] Hmm Hout. split; [|exact Hk].
  split; [eapply smatch_reobj; eauto|]. split; [exact HMI|]. split; [unfold axwf; cbn; rewrite Hnx; exact Hwf|].
  split; [apply shadow_ok_reobjs; assumption | exact Hhz].
Qed.

Definition ax_setX (A : axst) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
S36S30VA;A1VX;S35VA;A1A3").

Lemma SPA_x_sub : ltac2:(tb__ "0|1|
S12S1aS31S0S5S1cS1cA2M0A1S0S13Q40A1A1S3aG0S50G0R1R4A3S50G0R2S34R6A1A3F_;Fr;S11Vsegs;R7R5R6R3R2A6S11Vsegs;R8S56R6R5A2R7R4R3A6F_;F_;Fw;Ftp;FX';FA;Frho;FJ;").
Proof using .
  intros J rho A X' tp w Hsub [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  split; [exact Hsm|]. split; [exact HMI|]. split.
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. rewrite Hb, andb_true_r.
    apply forallb_forall. intros r Hr. exact (proj1 (forallb_forall _ _) HX r (Hsub r Hr)).
  - split; [|exact Hhz]. unfold shadow_ok in Hsh |- *. cbn. apply Forall_forall. intros r Hr.
    exact (proj1 (Forall_forall _ _) Hsh r (Hsub r Hr)).
Qed.

Lemma SPA_x_publish : ltac2:(tb__ "0|2|
S12S1aS31S5S1cS1cA2M0S0S13Q40M1A1A1S3aS16S1S38S21S30R4A1A1R3A2S4A3S39R6S1eS30R5A1A1S14G1S22R6S35R5A1A2A2R4A4S11Vsegs;R8R6R7R4R3A6S11Vsegs;R9S56R7S2G0R6S34R7A1A3A2R8R5R4A6F_;F_;F_;Fw;Ftp;Fr;FA;Frho;FJ;").
Proof using .
  intros J rho A r tp w Hb Hr [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  split; [exact Hsm|]. split; [exact HMI|]. split.
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hbb]. rewrite Hb, HX, Hbb. reflexivity.
  - split; [|exact Hhz]. unfold shadow_ok in Hsh |- *. cbn. constructor; [exact Hr | exact Hsh].
Qed.

Lemma SPA_unobj : ltac2:(tb__ "0|2|
S12S1aS31S0S1bA1M0G0S0S13Q40A1A1S0S41A1M1S5aS40S16G0S1eS30R7A1A1SaS1bR6R5A3A3S11Vsegs;RaR8R9R5S3G1S52R4S53R3R2A2A4A6S68RaR7S62R3R6R4A3A3S1aRcRbR7R6R4A4RdR2R8R7R5A4F_;S11Vsegs;RdS32RbS5bS30RbA1RaA2A2R2R8S3G1S52R7S53R6R5A2A4A6F_;Trho';F_;F_;Fmd;Fms;Ftr;Ftp;FR;Fobjs;FA;Frho;FJ;").
Proof using .
  intros J rho A objs R tp tr ms md Ho [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] rho' HJ. split; [|exact (HJ Hk)].
  split; [|split; [exact HMI | split; [unfold axwf; cbn; exact Hwf | split; [|exact Hhz]]]].
  - unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg]. unfold rho'. eapply smatch_frame_in; eauto.
  -
    eapply (shadow_ok_transport rho rho' A); [reflexivity | unfold rho'; apply eval_absorb
      | intros; unfold rho'; rewrite !eval_absorb; split; reflexivity | | exact Hsh].
    cbn [ax_S ax_setS ss_objs set_objs]. rewrite Ho. intros x _ Hout _. apply outside_all_app_iff in Hout as [Hout1 Hout2].
    split; [unfold rho'; apply outside_all_absorb; exact Hout1|].
    unfold rho', rho_absorb. cbn [rm].
    destruct (in_ranges_dec rho R _) as [Hin|Hnin]; [|reflexivity].
    exfalso. destruct Hin as (o & HoR & Hrng). exact (proj1 (Forall_forall _ _) Hout2 o HoR Hrng).
Qed.

Lemma unpaid_cons_le : ltac2:(tb__ "0|1|
S40S13Q40A1M0S0G0A1S47S4cSbG0S60R3S2G0R2R1A3A2A2A1S48S4cSbG0S60R3R1A2A2A1Z1A2A2Ftp;Fp;Fmd;").
Proof.
  intros md p tp. unfold unpaid. cbn. destruct (page_in_ranges p (m_vm_lazy md) && negb (page_mem p (m_vm_materialized md))); cbn; lia.
Qed.

Lemma paid_cons_le : ltac2:(tb__ "0|1|
S40S13Q40A1M0S0G0A1S47S5fR3S2G0R2R1A3A2S48S5fR3R1A2S3fA2A2Ftp;Fp;Fmd;").
Proof.
  intros md p tp. unfold paid. pose proof (unpaid_cons_le md p tp). pose proof page_size_pos. nia.
Qed.

Lemma MI_prepay : ltac2:(tb__ "0|2|
S40S0S13Q40M0A1M1A1G1S5cVsegs;R3R2A3S18S50G1R2R3A3A1S16S2eS4aS14G0R3A2S3fA2Z0A3S16S1S44R4S43R6A1A2S4A3S4bS5dR7R6A2S3fA2S5cVsegs;R8S2G1R6R7A3A3F_;F_;F_;F_;F_;Fp;Ftp;Fmd;").
Proof.
  intros md tp p (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlm & Htm) Hnin Hal Hlz Hroom.
  split; [exact HW|]. split; [constructor; assumption|]. split; [exact Hmat|].
  split; [intros q Hq; right; exact (Hsub q Hq)|]. split; [|split; [exact Hlc | split; [exact Hivs | split; [exact Hlm|]]]].
  - pose proof (paid_cons_le md p tp). unfold headroom in Hroom. lia.
  - intros q [<-|Hq]; [|exact (Htm q Hq)]. split; [exact Hal|].
    unfold page_in_ranges in Hlz. apply existsb_exists in Hlz as ([lo sz] & Hin & Hb). cbn [fst snd] in Hb.
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof page_size_pos. pose proof (urange p).
    destruct (Hlm lo sz Hin ltac:(lia)) as (b & s & Hbs & B1 & B2). exists b, s. split; [exact Hbs|]. lia.
Qed.

Lemma hid_cons : ltac2:(tb__ "0|2|
S40S13Q40M0A1M1S0G1A1G1S16S1S5eR4S2G1R3R2A3R1A3SeS5eR4R2R1A3S10S63G0S42R1A1R3A3A1A2A3Fa;Ftp;Fp;Fmd;").
Proof.
  intros md p tp a. unfold hid. cbn [page_mem existsb].
  destruct (page_in_ranges (page_base a) (m_vm_lazy md)); [|reflexivity]. cbn.
  destruct (bv_eqb (page_base a) p); cbn; [rewrite andb_false_r | rewrite andb_true_r]; reflexivity.
Qed.

Lemma page_base_of_page : ltac2:(tb__ "0|3|
S13Q40M0A1M1S2eS16S2eS4aS14G0R2A2S3fA2Z0M2A3S17S47G2R2A2S49R2S3fA2A2S16G1S42S15G0S48S14G0R4A2R3A2A2A1R4A3F_;F_;Fj;Fp;").
Proof.
  intros p j Hp Hj. unfold page_base, page_base_of. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  pose proof (urange p) as R. pose proof page_size_pos.
  assert (E : (bv_unsigned p + j) mod 2 ^ 64 = bv_unsigned p + j \/ bv_unsigned p + j >= 2 ^ 64) by
    (destruct (Z_lt_le_dec (bv_unsigned p + j) (2 ^ 64)); [left; apply Z.mod_small; lia | right; lia]).
  assert (Hdiv : (bv_unsigned p + j) / page_size = bv_unsigned p / page_size).
  { pose proof (Z.div_mod (bv_unsigned p) page_size ltac:(lia)) as D. rewrite Hp in D.
    rewrite D at 1. rewrite Z.add_0_r. replace (page_size * (bv_unsigned p / page_size) + j) with (j + (bv_unsigned p / page_size) * page_size) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  destruct E as [E|E].
  - rewrite E, Hdiv. pose proof (Z.div_mod (bv_unsigned p) page_size ltac:(lia)) as D. rewrite Hp in D.
    rewrite Z.mod_small; [lia|]. split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia] | lia].
  -
    exfalso. assert (bv_unsigned p <= 2 ^ 64 - page_size); [|lia].
    pose proof (Z.div_mod (bv_unsigned p) page_size ltac:(lia)) as D. rewrite Hp in D.
    assert (Hq : bv_unsigned p / page_size <= 2 ^ 64 / page_size - 1).
    { assert (bv_unsigned p / page_size < 2 ^ 64 / page_size); [|lia].
      apply Z.div_lt_upper_bound; [lia|]. change (page_size * (2 ^ 64 / page_size)) with (2 ^ 64). lia. }
    change (2 ^ 64 / page_size) with (2 ^ 52) in Hq. change (2 ^ 64) with (page_size * 2 ^ 52). nia.
Qed.

Definition in_page (p a : word) : Prop := ltac2:(tb__ "0|3|
S17S47S14Q40M0Vp;A2M1S14G0Va;A2M2A2S49G2S48G1S3fA2A2A2").

Lemma page_aligned_end : ltac2:(tb__ "0|1|
S13Q40M0A1S16S2eS4aS14G0R1A2S3fA2Z0A3S47S48S14G0R2A2S3fA2S4eZ2Z40A2A2F_;Fp;").
Proof.
  intros p Hal. pose proof (urange p) as Rp. pose proof page_size_pos as Pps.
  pose proof (Z.div_mod (bv_unsigned p) page_size ltac:(lia)) as D. rewrite Hal in D.
  assert (Hq : bv_unsigned p / page_size < 2 ^ 64 / page_size).
  { apply Z.div_lt_upper_bound; [lia|]. change (page_size * (2 ^ 64 / page_size)) with (2 ^ 64). lia. }
  change (2 ^ 64 / page_size) with (2 ^ 52) in Hq. change (2 ^ 64) with (page_size * 2 ^ 52). nia.
Qed.

Lemma page_base_in_page : ltac2:(tb__ "0|2|
S13Q40M0A1M1G1S16S2eS4aS14G0R2A2S3fA2Z0A3S57R3R2A2S16G1S42R3A1R4A3F_;F_;Fa;Fp;").
Proof.
  intros p a Hal [H1 H2].
  rewrite <- (Z_to_bv_bv_unsigned 64 a).
  replace (bv_unsigned a) with (bv_unsigned p + (bv_unsigned a - bv_unsigned p)) by lia.
  apply page_base_of_page; [exact Hal | lia].
Qed.

Lemma in_page_of_base : ltac2:(tb__ "0|1|
S13Q40A1M0G0S16G0S42R1A1R2A3S57R3R2A2F_;Fa;Fp;").
Proof. intros p a H. unfold in_page. rewrite <- H. apply page_base_range. Qed.

Definition zero_page_obj (p : word) : sobj := ltac2:(tb__ "0|0|
S29S24S14Q40Vp;A2A1S24Z0A1S24S3fA1SdS27A1S26A5").

Lemma SPA_prepay_zero : ltac2:(tb__ "0|7|
S12S1aS31S13Q40M0A1M1S0G1A1S0S41A1M2S5aS40S11Vsegs;R8R6R7R4S3G2S52R3S53R2R1A2A4A6S16S2eS4aS14G0R6A2S3fA2Z0M3A3S16S1S44R7S43R3A1A2S4A3S18S50G1R8R7A3A1S2eS17S47G3R1A2S49R1S3fA2A2S16S1S6bS46S45R7A1A1S48S14G0RbA2R2A2A2SfA3F_;Fj;S4bS5dR6R9A2S3fA2S4fS1bS1bS2bS25ReR1A2S3S2eS2eS14G0RcA2M4S48G4S3fA2A4A2Lo;S1eS30RcA1A1A3RfReRbRaR8A4R10RfS2G1RdRcA3M5RbR9A4F_;S11Vsegs;R10S32ReS5bS30ReA1M6SaS1bS1eG6A1S2S1bS59RdA1SdS1bA1A3A3A2A2RfG5S3G2S52RbS53RaR9A2A4A6F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Fp;FA;Frho;FJ;").
Proof using .
  intros J rho A p tp tr ms md [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] Hal Hlz Hnin Hacc Hroom Hdisj HJ.
  pose proof (urange p) as Rp. pose proof page_size_pos as Pps.
  pose proof (page_aligned_end p Hal) as Hp64. assert (Pv : page_size = 4096) by reflexivity.

  assert (Hhid : forall a, in_page p a -> hid md tp a = true).
  { intros a Ha. unfold hid. rewrite (page_base_in_page p a Hal Ha), Hlz. cbn.
    destruct (page_mem p tp) eqn:E; [|reflexivity]. apply page_mem_In in E. exfalso. exact (Hnin E). }
  assert (Hvis : forall a, in_page p a -> hid md (p :: tp) a = false).
  { intros a Ha. rewrite hid_cons, (page_base_in_page p a Hal Ha). unfold bv_eqb. rewrite Z.eqb_refl. cbn. apply andb_false_r. }
  assert (Hsame : forall a, hid md (p :: tp) a = true -> hid md tp a = true).
  { intros a Ha. rewrite hid_cons in Ha. apply andb_prop in Ha as [Ha _]. exact Ha. }
  assert (Hother : forall a, ~ in_page p a -> hid md (p :: tp) a = hid md tp a).
  { intros a Hn. rewrite hid_cons. destruct (hid md tp a) eqn:E; [|reflexivity]. cbn.
    destruct (bv_eqb (page_base a) p) eqn:E2; [|reflexivity]. exfalso. apply Hn. apply in_page_of_base. apply bv_eqb_eq. exact E2. }
  assert (MEMold : forall a, ~ in_page p a -> ms_mem (vms md (p :: tp) ms) a = ms_mem (vms md tp ms) a).
  { intros a Ha. rewrite !vms_mem, (Hother a Ha). reflexivity. }
  assert (MEMnew : forall a, in_page p a -> ms_mem (vms md (p :: tp) ms) a = Some (Z_to_bv 8 0)).
  { intros a Ha. rewrite vms_mem, (Hvis a Ha). destruct (Hhz a (Hhid a Ha)) as [E|[_ Hc]]; [exact E|].
    exfalso. pose proof (Hacc (bv_unsigned a - bv_unsigned p) ltac:(unfold in_page in Ha; lia)) as X.
    replace (bv_unsigned p + (bv_unsigned a - bv_unsigned p)) with (bv_unsigned a) in X by lia.
    cbn [cfg_model snd] in Hc. rewrite X in Hc. discriminate. }
  assert (MEMnewj : forall j, 0 <= j < page_size -> ms_mem (vms md (p :: tp) ms) (Z_to_bv 64 (bv_unsigned p + j)) = Some (Z_to_bv 8 0)).
  { intros j Hj. apply MEMnew. unfold in_page. rewrite u64_lit by lia. lia. }
  unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & (Hall & Hpd & Hfr) & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in Hswf, Hpc, Hpend, Hhalt, Hrom, Hroc, Hregs, Hfregs, Hfcsr, Hresv, Hall, Hpd, Hfr, Hfacts.

  assert (SHout : forall sa v, rm rho sa = Some v -> outside_all rho (ss_objs (ax_S A)) sa -> ~ in_page p sa).
  { intros sa v Hv Hout Hin. pose proof (Hfr sa Hout) as E. rewrite vms_mem, (Hhid sa Hin) in E. congruence. }

  assert (Hzr : obj_range rho (zero_page_obj p) = (bv_unsigned p, bv_unsigned p + page_size)).
  { unfold obj_range, obj_lo_of, obj_hi_of, zero_page_obj. cbn [ob_base ob_lo ob_hi eval].
    rewrite u64_lit by lia. rewrite !soff_lit_small by (unfold page_size; lia). f_equal. lia. }
  split; [|exact (HJ Hk)]. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in HMI, Hhz |- *.
  unfold smatchA. cbn [ax_S ax_setS fst snd cfg_ms cfg_model w_tr w_cfg].
  split; [|split; [apply MI_prepay; assumption | split; [unfold axwf in Hwf |- *; cbn [ax_S ax_X ax_base ax_setS ss_next set_objs] in Hwf |- *; exact Hwf | split]]].
  -
    unfold virt, smatch. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ss_pc ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts set_objs].
    split.
    {   unfold swf in Hswf |- *. cbn [ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts set_objs].
      rewrite forallb_app. cbn [forallb].
      replace (obj_wf (ss_next (ax_S A)) (zero_page_obj p)) with true by reflexivity.
      rewrite andb_true_r. exact Hswf. }
    split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
    split; [intros a; rewrite vms_rom; pose proof (Hrom a) as X; rewrite vms_rom in X; exact X|].
    split.
    {   intros a Hro. destruct (hid md tp a) eqn:E.
      - exfalso. pose proof (hid_off_segments segs md tp (MI_lazy_clear segs md tp HMI) a E) as X.
        unfold ro_addr in Hro. rewrite X in Hro. discriminate.
      - rewrite vms_mem. destruct (hid md (p :: tp) a) eqn:E2; [reflexivity|].
        pose proof (Hroc a Hro) as X. rewrite vms_mem, E in X. exact X. }
    split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
    split; [|exact Hfacts].
    split; [|split].
    +   cbn [ss_objs set_objs]. apply Forall_app. split.
      * apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Hall o Ho) as Hoh.
        pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as Hd.
        eapply (obj_holds_mem_ext segs rho (vms md tp ms)); [intros a; rewrite !vms_rom; reflexivity| |exact Hoh].
        intros off Hoff. apply MEMold. intros Hin. unfold in_page in Hin.
        pose proof (proj1 Hoh) as HB. unfold obj_range, ranges_disjoint in Hd. cbn [fst snd] in Hd.
        rewrite u64_lit in Hin by (unfold obj_lo_of, obj_hi_of in *; lia). unfold obj_lo_of, obj_hi_of in *. lia.
      * constructor; [|constructor]. unfold obj_holds. unfold obj_lo_of, obj_hi_of, zero_page_obj.
        cbn [ob_base ob_lo ob_hi ob_cells ob_dflt eval dflt_writable].
        rewrite u64_lit by lia. rewrite !soff_lit_small by (unfold page_size; lia).
        split; [lia|]. split.
        { intros off Hoff _. unfold wview. rewrite (MEMnewj off Hoff). discriminate. }
        split; [constructor|]. split; [|exact I].
        intros off Hoff _. unfold dflt_holds, rd, ms_read_byte. rewrite (MEMnewj off Hoff). reflexivity.
    +   cbn [ss_objs set_objs]. apply pairwise_disjoint_app1; [exact Hpd|].
      apply Forall_forall. intros o Ho. rewrite Hzr. exact (proj1 (Forall_forall _ _) Hdisj o Ho).
    +   cbn [ss_objs set_objs]. intros a Hout. apply outside_all_app_iff in Hout as [Hout1 Hout2].
      assert (Hn : ~ in_page p a).
      { intros Hin. inversion Hout2 as [|x l Hx _]; subst. cbn zeta in Hx. rewrite Hzr in Hx. cbn [fst snd] in Hx.
        apply Hx. exact Hin. }
      rewrite (MEMold a Hn). exact (Hfr a Hout1).
  -
    apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs set_objs]. intros x _ Hout Hdef.
    apply outside_all_app_iff. split; [exact Hout|].
    constructor; [|constructor]. cbn zeta. rewrite Hzr. cbn [fst snd].
    intros Hin. destruct (rm rho x) as [v|] eqn:Hv; [|exact (Hdef eq_refl)]. exact (SHout _ v Hv Hout Hin).
  -
    intros a Ha. exact (Hhz a (Hsame a Ha)).
Qed.

Lemma xshadow_outside_cover : ltac2:(tb__ "0|2|
S1aS31S0S1bA1S33R3R2A2S1bS2eS50S1bR2R4A3S17S47S7S2eS2eS25R7R3A2M0A3R2A2S49R2S9S2eS2eG0A3A2A2S19S1bS1bS17S50S1bR1S1eS30R8A1A1A3S17S47S7S2eS2eS25R9R1A2M1A3R4A2S49R4S9S2eS2eG1A3A2A2A2Lo;A2F_;F_;Fx;Fo';S55R5R4R3A3F_;F_;Fobjs';FA;Frho;").
Proof using .
  intros rho A objs' Hsh Hcov. pose proof (shadow_ok_outside rho A Hsh) as Hout.
  unfold xshadow_outside in Hout |- *. apply Forall_forall. intros [b l] Hr a j Ha Hj.
  pose proof (proj1 (Forall_forall _ _) Hout _ Hr a j Ha Hj) as X. cbn [fst snd] in X.
  apply Forall_forall. intros o' Ho'. cbn zeta. intros Hin.
  destruct (Hcov o' _ Ho' Hin) as (o & Ho & Hx). exact (proj1 (Forall_forall _ _) X o Ho Hx).
Qed.

Lemma In_firstn_In : forall {T} (l : list T) i x, In x (firstn i l) -> In x l.
Proof. intros T l i x H. rewrite <- (firstn_skipn i l). apply in_or_app. left. exact H. Qed.
Lemma In_skipn_In : forall {T} (l : list T) i x, In x (skipn i l) -> In x l.
Proof. intros T l i x H. rewrite <- (firstn_skipn i l). apply in_or_app. right. exact H. Qed.

Lemma SPA_split : ltac2:(tb__ "0|0|
S12S1aS31ScS1cS1fS0S13Q40A1A1S3aS16S8S1fA1S6aS30R6A1R5R4A3S6S1fR3A2A3S11Vsegs;R9R7R8R3R2A6S11Vsegs;RaS32R8R5A2R9R4R3A6F_;F_;Fw;Ftp;FS';Fmid;Fi;FA;Frho;FJ;").
Proof using .
  intros J rho A i mid S' tp [tr [ms md]] Hsp [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  pose proof (smatch_split segs rho (ax_S A) i mid S' _ Hsp Hsm) as Hsm'.
  unfold split_obj_at in Hsp.
  destruct (nth_error (ss_objs (ax_S A)) i) as [o|] eqn:Hn; [|discriminate].
  destruct (sv_below (ss_next (ax_S A)) mid && in_bounds (ss_facts (ax_S A)) (ob_lo o) (ob_hi o) mid 0)%bool; [|discriminate].
  destruct (obj_split o mid) as [[o1 o2]|] eqn:Ho; [|discriminate]. injection Hsp as <-.
  assert (Hin_o : In o (ss_objs (ax_S A))) by (eapply nth_error_In; exact Hn).

  unfold obj_split in Ho. destruct (ob_dflt o); try discriminate;
    destruct (part_cells (ob_cells o) mid) as [[lc rc]|]; try discriminate; injection Ho as <- <-.
  all: split; [exact Hsm'|]; split; [exact HMI|]; split; [unfold axwf in Hwf |- *; cbn; exact Hwf|]; split; [|exact Hhz].
  all: apply shadow_ok_reobjs; [exact Hsh|]; apply xshadow_outside_cover; [exact Hsh|].
  all: unfold virt in Hsm'; cbn [fst snd cfg_ms cfg_model w_tr w_cfg set_objs ss_objs] in Hsm';
       destruct Hsm' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall' & _ & _) & _); cbn [fst snd cfg_ms set_objs ss_objs] in Hall';
       apply Forall_app in Hall' as [_ Hall']; inversion Hall' as [|x1 l1 Ho1 Hall2]; subst; inversion Hall2 as [|x2 l2 Ho2 _]; subst;
       destruct Ho1 as ((_ & _ & L1 & _) & _); destruct Ho2 as ((_ & _ & L2 & _) & _);
       unfold obj_lo_of, obj_hi_of in L1, L2; cbn [ob_lo ob_hi ob_base] in L1, L2.
  all: intros o' x Ho' Hx; apply in_app_or in Ho' as [Ho'|[<-|[<-|Ho']]];
       [ exists o'; split; [eapply In_firstn_In; exact Ho' | exact Hx]
       | exists o; split; [exact Hin_o|]; unfold obj_range, obj_lo_of, obj_hi_of in Hx |- *; cbn [ob_base ob_lo ob_hi fst snd] in Hx |- *; lia
       | exists o; split; [exact Hin_o|]; unfold obj_range, obj_lo_of, obj_hi_of in Hx |- *; cbn [ob_base ob_lo ob_hi fst snd] in Hx |- *; lia
       | exists o'; split; [eapply In_skipn_In; exact Ho' | exact Hx] ].
Qed.

Lemma SPA_merge : ltac2:(tb__ "0|0|
S12S1aS31ScS1fS0S13Q40A1A1S3aS16S8S1fA1S69S30R5A1R4A2S6S1fR3A2A3S11Vsegs;R8R6R7R3R2A6S11Vsegs;R9S32R7R5A2R8R4R3A6F_;F_;Fw;Ftp;FS';Fi;FA;Frho;FJ;").
Proof using .
  intros J rho A i S' tp [tr [ms md]] Hmg [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  pose proof (smatch_merge segs rho (ax_S A) i S' _ Hmg Hsm) as Hsm'.
  unfold merge_objs_at in Hmg.
  destruct (nth_error (ss_objs (ax_S A)) i) as [o1|] eqn:Hn1; [|discriminate].
  destruct (nth_error (ss_objs (ax_S A)) (Datatypes.S i)) as [o2|] eqn:Hn2; [|discriminate].
  destruct (sitv (ss_facts (ax_S A)) (ob_lo o1)) as [[l1 h1]|]; [|discriminate].
  destruct (sitv (ss_facts (ax_S A)) (ob_hi o2)) as [[l2 h2]|]; [|discriminate].
  destruct (h2 - l1 <? 2 ^ 63); [|discriminate].
  destruct (obj_merge o1 o2) as [o|] eqn:Ho; [|discriminate]. injection Hmg as <-.
  assert (Hin1 : In o1 (ss_objs (ax_S A))) by (eapply nth_error_In; exact Hn1).
  assert (Hin2 : In o2 (ss_objs (ax_S A))) by (eapply nth_error_In; exact Hn2).
  unfold obj_merge in Ho.
  destruct (sv_eqb (ob_base o1) (ob_base o2) && match same_atoms (ob_hi o1) (ob_lo o2) with Some 0 => true | _ => false end)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hb Hsa]. apply sv_eqb_sound in Hb.
  destruct (same_atoms (ob_hi o1) (ob_lo o2)) as [d|] eqn:Hsd; [|discriminate]. destruct d; try discriminate.
  pose proof (same_atoms_eq rho _ _ Hsd) as Ehl.
  destruct (dflt_merge (ob_dflt o1) (ob_dflt o2)) as [d|]; [|discriminate]. injection Ho as <-.

  unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
  pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall.
  destruct (proj1 (Forall_forall _ _) Hall o1 Hin1) as ((_ & _ & L1 & _) & _).
  destruct (proj1 (Forall_forall _ _) Hall o2 Hin2) as ((_ & _ & L2 & _) & _).
  unfold obj_lo_of, obj_hi_of in L1, L2.
  assert (E12 : soff rho (ob_hi o1) = soff rho (ob_lo o2)) by (unfold soff; rewrite Ehl; reflexivity).
  split; [unfold virt; cbn [fst snd cfg_ms cfg_model w_tr w_cfg]; exact Hsm'|]. split; [exact HMI|].
  split; [unfold axwf in Hwf |- *; cbn; exact Hwf|]. split; [|exact Hhz].
  apply shadow_ok_reobjs; [exact Hsh|]. apply xshadow_outside_cover; [exact Hsh|].
  cbn [set_objs ss_objs]. intros o' x Ho' Hx. apply in_app_or in Ho' as [Ho'|[<-|Ho']].
  - exists o'. split; [eapply In_firstn_In; exact Ho' | exact Hx].
  - unfold obj_range, obj_lo_of, obj_hi_of in Hx. cbn [ob_base ob_lo ob_hi fst snd] in Hx.
    destruct (Z_lt_ge_dec x (bv_unsigned (eval rho (ob_base o1)) + soff rho (ob_hi o1))).
    + exists o1. split; [exact Hin1|]. unfold obj_range, obj_lo_of, obj_hi_of. cbn [fst snd]. lia.
    + exists o2. split; [exact Hin2|]. unfold obj_range, obj_lo_of, obj_hi_of. cbn [fst snd]. rewrite <- Hb. lia.
  - exists o'. split; [eapply In_skipn_In; exact Ho' | exact Hx].
Qed.

End G.
