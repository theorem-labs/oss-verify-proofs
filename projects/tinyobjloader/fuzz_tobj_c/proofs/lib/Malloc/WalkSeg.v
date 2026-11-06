(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "rw"; "sstate"; "holds"; "eval"; "rl"; "rm"; "ss_facts"; "swf"; "ss_lenient"; "ss_next"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "prod"; "fst"; "option"; "negb"; "pair"; "Some"; "false"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "below200"; "in_vars"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg"; "setp"; "set_par"; "keys_distinct"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "assn"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "sym_run"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sprop_vars_all"; "state_vars_all"; "sv_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "psupported"; "zholds"; "zeval"; "zsupported"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "diffs_ok"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg.Seg"; "POST"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundM SymSoundR SymFrame SymSummary SymCall SymEntail Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import WalkLink ZEval WalkArith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Fixpoint set_par (rhoA rhoB : valuation) (l : list (positive * sv)) : valuation :=
  match l with
  | [] => rhoB
  | (j, e) :: t => set_par rhoA (rho_set_rw rhoB j (eval rhoA e)) t
  end.
Definition setp (rhoB : valuation) (l : list (positive * sv)) : valuation := set_par rhoB rhoB l.

Fixpoint keys_distinct (l : list positive) : bool :=
  match l with [] => true | j :: t => negb (in_vars t j) && keys_distinct t end.

Lemma set_par_rl : ltac2:(tb__ "0|0|
S7S14S16S0S6A2A1S7S2S0S14S21Q8A1A1F_;SdS25R3R1R2A3A1SdR1A1A3FrhoB;Fl;FrhoA;").
Proof. intros rhoA l. induction l as [|[j e] t IH]; intros rhoB; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma set_par_rm : ltac2:(tb__ "0|0|
S7S14S16S0S6A2A1S7S2S21Q40A1S18S21Q8A1A1F_;SeS25R3R1R2A3A1SeR1A1A3FrhoB;Fl;FrhoA;").
Proof. intros rhoA l. induction l as [|[j e] t IH]; intros rhoB; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma set_par_other : ltac2:(tb__ "0|1|
S7S14S16S0S6A2M0A1S7S0S2S13S20S28G0S0S17S0S6A2R3A4R1A2S1cA3S2S21Q40A1S9S25R5R3R4A3R2A2S9R3R2A2A3F_;Fu;FrhoB;Fl;FrhoA;").
Proof.
  intros rhoA l. induction l as [|[j e] t IH]; intros rhoB u Hu; [reflexivity|].
  cbn in Hu. apply Bool.orb_false_iff in Hu as [H1 H2]. cbn. rewrite IH by exact H2. cbn [rw rho_set_rw]. rewrite H1. reflexivity.
Qed.
Lemma set_par_get : ltac2:(tb__ "0|1|
S7S14S16S0S6A2M0A1S7S0S6S2S13S26S28G0S0S17S0S6A2R4A4A1S15A3S2dG0S1aS0S6R3R2A4R5A3S2S21Q40A1S9S25R7R5R6A3R4A2ScR7R3A2A3F_;F_;Fe;Fj;FrhoB;Fl;FrhoA;").
Proof.
  intros rhoA l. induction l as [|[j' e'] t IH]; intros rhoB j e Hd Hin; [destruct Hin|].
  cbn in Hd. apply andb_prop in Hd as [Hn Hd]. cbn. destruct Hin as [E|Hin].
  - injection E as E1 E2. subst j' e'.
    rewrite set_par_other. { cbn [rw rho_set_rw]. rewrite Pos.eqb_refl. reflexivity. }
    destruct (in_vars (map fst t) j); [discriminate|reflexivity].
  - apply IH; assumption.
Qed.
Lemma setp_get : ltac2:(tb__ "0|1|
S7S14S16S0S6A2M0A1S0S6S2S13S26S28G0S0S17S0S6A2R3A4A1S15A3S2dG0S1aS0S6R3R2A4R4A3S2S21Q40A1S9S24R6R5A2R4A2ScR6R3A2A3F_;F_;Fe;Fj;Fl;FrhoB;").
Proof. intros. unfold setp. apply set_par_get; assumption. Qed.
Lemma setp_other : ltac2:(tb__ "0|1|
S7S14S16S0S6A2M0A1S0S2S13S20S28G0S0S17S0S6A2R2A4R1A2S1cA3S2S21Q40A1S9S24R4R3A2R2A2S9R4R2A2A3F_;Fu;Fl;FrhoB;").
Proof. intros. unfold setp. apply set_par_other; assumption. Qed.
Lemma setp_rl : ltac2:(tb__ "0|0|
S7S14S16S0S6A2A1S2S0S14S21Q8A1A1F_;SdS24R2R1A2A1SdR2A1A3Fl;FrhoB;"). Proof. intros. apply set_par_rl. Qed.
Lemma setp_rm : ltac2:(tb__ "0|0|
S7S14S16S0S6A2A1S2S21Q40A1S18S21Q8A1A1F_;SeS24R2R1A2A1SeR2A1A3Fl;FrhoB;"). Proof. intros. apply set_par_rm. Qed.

Fixpoint scratch_of (d : list (sv * sv)) : list (positive * sv) :=
  match d with
  | [] => []
  | (e, SVar j) :: t => if (200 <=? j)%positive then (j, e) :: scratch_of t else scratch_of t
  | _ :: t => scratch_of t
  end.

Section Seg.
Variable segs : list Segment.
Variable cuts : list Z.
Variable nxa : positive.
Hypothesis Hnxa : (200 <= nxa)%positive.
Variable ok : world -> Prop.
Variable K : ltac2:(tb__ "0|0|
S14S3dA1S3cOF_;F_;").
Hypothesis HK : ok_frame segs ok K.
Variable rhoW : valuation.
Let zr := zr_of rhoW.
Let zl := zl_of rhoW.

Lemma EV : ltac2:(tb__ "0|1|
S7S6S1eVrhoW;R2A2S2S13S34S1fR2A2S15A3S2S13S38R3A1S15A3S2S21Q40M0A1ScR5R4A2S22G0S37Vzr;Vzl;R4A3A2A3F_;F_;F_;Fe;Frho';").
Proof using .
  intros rho' e Hag Hv Hs. rewrite (eval_agrees rhoW rho' e Hag Hv).
  unfold zr, zl. rewrite <- (eval_zeval rhoW e Hs). symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma EVu : ltac2:(tb__ "0|0|
S7S6S1eVrhoW;R2A2S2S13S34S1fR2A2S15A3S2S13S38R3A1S15A3S2S1S23Q40ScR5R4A2A2S37Vzr;Vzl;R4A3A3F_;F_;F_;Fe;Frho';").
Proof using . intros rho' e Hag Hv Hs. rewrite (EV rho' e Hag Hv Hs). apply u64. apply zeval_range. exact Hs. Qed.

Lemma HOLDS : ltac2:(tb__ "0|0|
S7S8S1eVrhoW;R2A2S2S13S32S1fR2A2S15A3S2S13S35R3A1S15A3S5SbR5R4A2S36Vzr;Vzl;R4A3A2F_;F_;F_;Fp;Frho';").
Proof using .
  intros rho' p (Hw & Hl & _) Hv Hs.
  rewrite (holds_agree_vars below200 rho' rhoW p Hw Hl Hv).
  rewrite (holds_zholds rhoW p Hs). apply zholds_ext; intros; reflexivity.
Qed.

Lemma rw_agrees : ltac2:(tb__ "0|0|
S7S0S1eVrhoW;R2A2S2S13S1fR2A1S15A3S2S21Q40A1S9R4R3A2S9VrhoW;R3A2A3F_;F_;Fj;Frho';").
Proof using . intros rho' j (Hw & _) Hj. rewrite (Hw j Hj). reflexivity. Qed.

Lemma seg_run : ltac2:(tb__ "0|1|
S1dSaS14S2fA1M0S2cS7S2S13S11R4A1S1cA3S2S0S12R5A1Vnxa;A3S2S18G0A1S31Vsegs;R7Vcuts;R6S15A5S1bG0R5A2A3S1eVrhoW;R4A2S2fS7S2aS2dS2fR3RaA3S1eVrhoW;R3A2S27Vsegs;VK;S30R5A1R4R3A5RcR4A1F_;F_;F_;Fw;Frho'';FLf;S2bVsegs;Vok;S27Vsegs;VK;R9R6A4R7A4F_;F_;F_;F_;F_;Frho';FQ;Fleaves;FS;Ffuel;").
Proof using HK Hnxa.
  intros fuel S leaves Q rho' Hl Hn Hrun Hag HQ.
  eapply triple_conseq; [intros w Hw; exact Hw | | apply triple1_triple; exact (sym_run_sound_strict segs fuel cuts S leaves ok K rho' Hl Hrun HK)].
  intros w (Lf & rho'' & Hin & Hab & Hsm & HKw). apply (HQ Lf rho'' w Hin).
  - eapply agrees_below; [exact Hag | exact Hab | rewrite Hn; exact Hnxa].
  - split; [exact Hsm | exact HKw].
Qed.

Definition POST (C : sstate) : assn := ltac2:(tb__ "0|0|
S2aS4S7S7S3S1eVrhoW;R1A2S27Vsegs;VK;VC;R1R2A5A2Lrho'';A2Lw;").

Lemma from_POST : ltac2:(tb__ "0|0|
SaS2cS7S1eVrhoW;R1A2S2bVsegs;Vok;S27Vsegs;VK;R4R2A4R3A4F_;Frho';S2bVsegs;Vok;S3bR3A1R2A4F_;FQ;FC;").
Proof using . intros C Q H. unfold POST. apply triple_ex. intros rho'. apply triple_pure. apply H. Qed.

Lemma leaf_fact : ltac2:(tb__ "0|0|
S7SaS2aS8S1eVrhoW;R4A2S27Vsegs;VK;R4R5R3A5S2dS8R3SfR5A1A3S2S13S32S1fR4A2S15A3S2S13S35R5A1S15A3S36Vzr;Vzl;R6A3F_;F_;F_;F_;F_;Fp;Fw;FLf;Frho';").
Proof using .
  intros rho' Lf w p Hag HSP Hin Hv Hs. apply (proj1 (HOLDS rho' p Hag Hv Hs)).
  exact (proj1 (Forall_forall _ _) (SP_facts_hold segs K rho' Lf w HSP) p Hin).
Qed.

Lemma ZF_holds : ltac2:(tb__ "0|0|
S7S14S8A1S1eVrhoW;R2A2S2S13S2eS8S32S1fA1R2A3S15A3S2S13S2eS8S35R3A3S15A3S29S8S36Vzr;Vzl;A2R4A3S29S8SbR6A1R5A3F_;F_;F_;F_;Fl;Frho';").
Proof using .
  intros rho' l Hag Hv Hs HZ. apply Forall_forall. intros p Hp.
  apply (proj2 (HOLDS rho' p Hag (proj1 (forallb_forall _ _) Hv p Hp) (proj1 (forallb_forall _ _) Hs p Hp))).
  exact (proj1 (Forall_forall _ _) HZ p Hp).
Qed.

Lemma agrees_setp : ltac2:(tb__ "0|1|
S7S14S16S0S6A2M0A1S1eVrhoW;R2A2S2S13S2eS0S0S19S1fR1A1A1Lj;S28G0S0S17S0S6A2R2A4A3S15A3S1eVrhoW;S24R4R3A2A2F_;F_;Fl;FrhoB;").
Proof using .
  intros rhoB l (Hw & Hl & Hm) Hb. split; [|split; [intros l0; rewrite setp_rl; apply Hl | rewrite setp_rm; exact Hm]].
  intros u Hu. rewrite setp_other; [apply Hw; exact Hu|].
  rewrite forallb_forall in Hb. destruct (in_vars (map fst l) u) eqn:E; [|reflexivity].
  unfold in_vars in E. apply existsb_exists in E as (u' & Hu' & E). apply Pos.eqb_eq in E. subst u'.
  specialize (Hb u Hu'). rewrite Hu in Hb. discriminate.
Qed.

Lemma relinkp : ltac2:(tb__ "0|4|
S7SaSaS2aS14S16S0S6A2M0A1S14S16S6S6A2A1M1S14S8A1M2S2S13S33S0S19S20S28G0S0S17S0S6A2R4A4R1A2A1Lu;R6A2S15A3S2S13S10R6A1S15A3S2S18S16G1G2A2M3A1S3aR8R7A2S1bG3S1aG1G2R4R3A4A2A3S39S24RaR6A2R5A2S29S8SbS24RbR7A2A1R5A3S27Vsegs;VK;RbRcR9A5S27Vsegs;VK;RbS24RdR9A2RaA5F_;F_;F_;F_;F_;F_;Fnf;Fd;Fl;Fw;FS';FS;FrhoB;").
Proof using .
  intros rhoB S S' w l d nf Hvars Hwf Hsd Hd Hnf HSP.
  eapply SP_restate; [exact Hwf | exact Hsd | exact Hd | exact Hnf |].
  destruct HSP as [Hsm HK']. split; [|exact HK'].
  apply (smatch_agree_vars segs (fun u => negb (in_vars (map fst l) u)) rhoB); try assumption.
  - intros u Hu. symmetry. apply setp_other. destruct (in_vars (map fst l) u); [discriminate|reflexivity].
  - intros l0. rewrite setp_rl. reflexivity.
  - rewrite setp_rm. reflexivity.
Qed.

Lemma linkp : ltac2:(tb__ "0|6|
SaSaS14S16S0S6A2M0A1S14S16S6S6A2A1M1S14S8A1M2S7S2aS2S13S33S0S19S20S28G0S0S17S0S6A2R6A4M3R1A2A1Lu;R7A2S15A3S2S13S2eS0S0S19S1fR1A1A1Lj;G3A3S15A3S2S13S10R8A1S15A3S2S18S16G1G2A2M4A1S3aRaR9A2S1bG4S1aG1G2R7R6A4A2A3S1eVrhoW;R6A2S1eVrhoW;S24R7RaA2A2S29S8SbR8A1SfRdA1A3S3S39S24R9RcA2M5RbA2S29S8SbG5A1RaA3A2F_;F_;S27Vsegs;VK;RdR8R7A5S3bRdR8A2F_;F_;F_;F_;F_;F_;F_;Fw;FrhoB';Fnf;Fd;Fsets;FC;FLf;").
Proof using .
  intros Lf C sets d nf rhoB' w Hvars Hb Hwf Hsd Hag Hsem HSP.
  pose proof (agrees_setp rhoB' sets Hag Hb) as Hag'.
  destruct (Hsem Hag' (SP_facts_hold segs K rhoB' Lf w HSP)) as [Hd Hnf].
  exists (setp rhoB' sets). split; [exact Hag'|].
  exact (relinkp rhoB' Lf C w sets d nf Hvars Hwf Hsd Hd Hnf HSP).
Qed.

End Seg.
