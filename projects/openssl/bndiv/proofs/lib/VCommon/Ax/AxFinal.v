(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List String Ascii.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Cli Require Import CliVerdict CliSpecG.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxMem AxZZ AxState AxSys AxJoin AxJoinSound AxEntryRel.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxModelRel AsanWShape.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Export AxFinalK.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pieces_eqb (a b : list piece) : bool := list_eqb piece_eqb a b.

Lemma pieces_eqb_eq (a b : list piece) : pieces_eqb a b = true -> a = b.
Proof. apply (list_eqb_eq _ piece_eqb_eq). Qed.

Lemma pieces_val_app (ρ : valuation) (l1 l2 : list piece) (o : list byte) :
  pieces_val ρ (l1 ++ l2) o -> exists o1 o2, o = o1 ++ o2 /\ pieces_val ρ l1 o1 /\ pieces_val ρ l2 o2.
Proof.
  revert o. induction l1 as [|p l1 IH]; intros o H; cbn [app] in H.
  - exists [], o. split; [reflexivity | split; [reflexivity | exact H]].
  - destruct p as [b|k]; cbn [pieces_val] in H.
    + destruct H as (y & o' & -> & Hy & H'). destruct (IH o' H') as (o1 & o2 & -> & H1 & H2).
      exists (y :: o1), o2. split; [reflexivity|]. split; [|exact H2]. cbn [pieces_val]. exists y, o1. repeat split; assumption.
    + destruct H as (o' & -> & H'). destruct (IH o' H') as (o1 & o2 & -> & H1 & H2).
      exists (dec_str k ρ ++ o1), o2. split; [rewrite app_assoc; reflexivity|]. split; [|exact H2]. cbn [pieces_val]. exists o1. split; [reflexivity | exact H1].
Qed.

Lemma pieces_val_app_intro (ρ : valuation) (l1 l2 : list piece) (o1 o2 : list byte) :
  pieces_val ρ l1 o1 -> pieces_val ρ l2 o2 -> pieces_val ρ (l1 ++ l2) (o1 ++ o2).
Proof.
  revert o1. induction l1 as [|p l1 IH]; intros o1 H1 H2; cbn [app pieces_val] in *.
  - subst o1. exact H2.
  - destruct p as [b|k].
    + destruct H1 as (y & o' & -> & Hy & H'). exists y, (o' ++ o2). split; [reflexivity|]. split; [exact Hy | exact (IH o' H' H2)].
    + destruct H1 as (o' & -> & H'). exists (o' ++ o2). split; [rewrite app_assoc; reflexivity | exact (IH o' H' H2)].
Qed.

(* [comment removed for export] *)
Definition lit_bytes (bs : list byte) : list piece := map (fun b => PB (BL (of_Z (bv_unsigned b)))) bs.
Definition lit_pieces (s : string) : list piece := lit_bytes (s2b s).

Lemma pieces_val_lit_bytes (ρ : valuation) (bs o : list byte) : pieces_val ρ (lit_bytes bs) o -> o = bs.
Proof.
  revert o. induction bs as [|b bs IH]; intros o H; cbn [lit_bytes map pieces_val] in H; [exact H|].
  destruct H as (y & o' & -> & Hy & H'). fold (lit_bytes bs) in H'. rewrite (IH o' H'). f_equal.
  cbn [xb_z] in Hy. apply bv_eq. rewrite Hy. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  rewrite of_Z_spec. apply Z.mod_small. change wB with (2 ^ 63). lia.
Qed.

Lemma pieces_val_lit (ρ : valuation) (a : string) (o : list byte) : pieces_val ρ (lit_pieces a) o -> o = s2b a.
Proof. apply pieces_val_lit_bytes. Qed.

Lemma pieces_val_lit_intro (ρ : valuation) (bs : list byte) : pieces_val ρ (lit_bytes bs) bs.
Proof.
  induction bs as [|b bs IH]; cbn [lit_bytes map pieces_val]; [reflexivity|]. exists b, bs. split; [reflexivity|]. split; [|exact IH].
  cbn [xb_z]. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  rewrite of_Z_spec. symmetry. apply Z.mod_small. change wB with (2 ^ 63). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition nl_str : string := String (ascii_of_nat 10) EmptyString.

Definition pat_usage : list piece := lit_pieces "usage: " ++ [PS 0] ++ lit_pieces (" INPUT" ++ nl_str).

Lemma pat_usage_val (ρ : valuation) (o : list byte) : pieces_val ρ pat_usage o -> o = msg_usage (dec_str 0 ρ).
Proof.
  intros H. destruct (pieces_val_app ρ _ _ o H) as [o1 [o2 [-> [H1 H2]]]]. rewrite (pieces_val_lit ρ _ o1 H1).
  cbn [app pieces_val] in H2. destruct H2 as [o3 [-> H3]]. rewrite (pieces_val_lit ρ _ o3 H3). reflexivity.
Qed.

Definition KT_usage (fs0 : Fs.Fs) (ρ : valuation) (o : list byte) : TSet := KDer (t_die (msg_usage (dec_str 0 ρ)) fs0) o.

Lemma KT_usage_agree (fs0 : Fs.Fs) (ρ ρ' : valuation) (o : list byte) :
  (forall x, entry_var x = true -> ρ' x = ρ x) -> KT_usage fs0 ρ' o = KT_usage fs0 ρ o.
Proof. intros H. unfold KT_usage. rewrite (dec_str_agree_entry ρ ρ' 0 H). reflexivity. Qed.

Lemma KT_usage_emit (fs0 : Fs.Fs) (ρ : valuation) (o bs : list byte) :
  KT_usage fs0 ρ (o ++ bs) [] -> t_eq (KT_usage fs0 ρ o) (t_emit (W 2 bs) (KT_usage fs0 ρ (o ++ bs))).
Proof. apply KDer_emit. Qed.

Lemma KT_usage_end (fs0 : Fs.Fs) (ρ : valuation) (o : list byte) :
  pieces_val ρ pat_usage o -> t_eq (KT_usage fs0 ρ o) (t_exit (Z_to_bv 64 2) fs0).
Proof.
  intros H. rewrite (pat_usage_val ρ o H). unfold KT_usage.
  eapply t_eq_trans; [apply (KDer_KD _ [] _ fs0); rewrite app_nil_r; reflexivity | apply KD_end].
Qed.

Lemma KT_usage_start (fs0 : Fs.Fs) (ρ : valuation) : t_eq (KT_usage fs0 ρ []) (t_die (msg_usage (dec_str 0 ρ)) fs0).
Proof. apply KDer_nil. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pin0 (s : store) (k : Z) : bool :=
  match lrange s (lvar (lenvar k) 1) with Some (lo, hi) => (lo =? 0) &&& (hi =? 0) | None => false end.

Fixpoint drop_empty (s : store) (pat : list piece) : list piece :=
  match pat with
  | [] => []
  | PS k :: r => if pin0 s k then drop_empty s r else PS k :: drop_empty s r
  | p :: r => p :: drop_empty s r
  end.

Lemma drop_empty_val (ρ : valuation) (s : store) : sat ρ s -> forall (pat : list piece) (o : list byte),
  pieces_val ρ (drop_empty s pat) o -> pieces_val ρ pat o.
Proof.
  intros Hs. induction pat as [|[x|k] r IH]; intros o H; cbn [drop_empty] in H; [exact H| |].
  - cbn [pieces_val] in *. destruct H as (y & o1 & -> & Hy & Hr). exists y, o1. split; [reflexivity|]. split; [exact Hy | exact (IH o1 Hr)].
  - destruct (pin0 s k) eqn:Ep.
    + cbn [pieces_val]. exists o. split; [|exact (IH o H)]. unfold pin0 in Ep.
      destruct (lrange s (lvar (lenvar k) 1)) as [[lo hi]|] eqn:El; [|discriminate]. apply land_true in Ep as [E1 E2].
      apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst lo hi.
      pose proof (lrange_sound ρ s _ Hs _ El) as X. cbn [fst snd] in X. unfold leval, lvar in X. cbn [fst snd teval] in X.
      assert (E0 : ρ (lenvar k) = 0) by lia. unfold dec_str. destruct ((0 <=? k) && (k <? 1048576)); [|reflexivity].
      rewrite E0. reflexivity.
    + cbn [pieces_val] in *. destruct H as (o1 & -> & Hr). exists o1. split; [reflexivity | exact (IH o1 Hr)].
Qed.

(* [comment removed for export] *)
Definition pieces_match (s : store) (out pat : list piece) : bool := pieces_eqb out pat ||| pieces_eqb out (drop_empty s pat).

Lemma pieces_match_val (ρ : valuation) (s : store) (out pat : list piece) (o : list byte) :
  sat ρ s -> pieces_match s out pat = true -> pieces_val ρ out o -> pieces_val ρ pat o.
Proof.
  intros Hs H Hv. unfold pieces_match in H. apply lor_true in H as [H|H]; apply pieces_eqb_eq in H; subst out; [exact Hv|].
  exact (drop_empty_val ρ s Hs pat o Hv).
Qed.

(* [comment removed for export] *)
Definition final_ok (segs : list Segment) (pat : list piece) (A : AST) : bool :=
  match xlit (aget (a_regs A) 17%uint63), xlit (aget (a_regs A) 10%uint63) with
  | Some x, Some y =>
      (x =? 94) && (y =? 2) && pieces_match (a_facts A) (am_out (a_model A)) pat &&
      match fetch_word segs (wbv (a_pc A)) with Some w => is_ecall w | None => false end
  | _, _ => false
  end.

Section FinalGen.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.

Notation RR ρ := (R segs amodel (MR segs fs0 ρ) LIM ρ).

Theorem final_sound_gen (pat : list piece) (A : AST) :
  final_ok segs pat A = true ->
  (forall ρ ms model o, RR ρ A (mkCfg ms model) -> pieces_val ρ pat o -> t_eq (KT ρ o) (t_exit (Z_to_bv 64 2) fs0)) ->
  Sound segs cfg LIM (MR segs fs0) KT A.
Proof.
  intros H Hend ρ [ms model] HR o Hout. unfold final_ok in H.
  destruct (xlit (aget (a_regs A) 17%uint63)) as [x|] eqn:E17; [|discriminate].
  destruct (xlit (aget (a_regs A) 10%uint63)) as [y|] eqn:E10; [|discriminate].
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H Hp]. apply andb_prop in H as [Hx Hy].
  apply Z.eqb_eq in Hx. apply Z.eqb_eq in Hy. subst x y.
  destruct (fetch_word segs (wbv (a_pc A))) as [w|] eqn:Ef; [|discriminate].
  pose proof HR as [Hpc _ Hsvc Hregs _ _ _ Hmod Hh _ Hsat _ _ _ _]. cbn [cfg_ms cfg_model] in *.
  assert (H17 : rg ms 17%bv = Z_to_bv 64 94).
  { apply bv_eq. exact (reg_lit ρ _ ms (Z_to_bv 5 17) 17%uint63 94 Hregs eq_refl E17). }
  assert (H10 : rg ms 10%bv = Z_to_bv 64 2).
  { apply bv_eq. exact (reg_lit ρ _ ms (Z_to_bv 5 10) 10%uint63 2 Hregs eq_refl E10). }
  rewrite <- Hpc in Ef.
  pose proof (rzc_exit_raw_lit segs cfg ms model w 2 Hsvc Ef Hf Hh (or_introl H17) H10 ltac:(lia)) as Hz.
  rewrite (mr_fs segs fs0 ρ _ _ Hmod) in Hz.
  apply (rzc_conseq segs cfg _ _ _ Hz). apply t_eq_sym. apply (Hend ρ ms model o HR).
  exact (pieces_match_val ρ (a_facts A) _ pat o Hsat Hp Hout).
Qed.

End FinalGen.

Theorem final_usage_sound (segs : list Segment) (cfg : SpuriousCfg) (LIM : Z) (fs0 : Fs.Fs) (A : AST) :
  final_ok segs pat_usage A = true -> Sound segs cfg LIM (MR segs fs0) (KT_usage fs0) A.
Proof.
  intros H. apply (final_sound_gen segs cfg LIM fs0 (KT_usage fs0) pat_usage A H).
  intros ρ ms model o _ Hp. exact (KT_usage_end fs0 ρ o Hp).
Qed.
