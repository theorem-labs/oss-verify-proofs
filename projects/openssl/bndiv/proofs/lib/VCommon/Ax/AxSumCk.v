(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec FastWord ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Cli Require Import CliSpecG.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxMem AxMemC AxZZ AxState AxStep AxSys AxJoinSound AxSum AxTabs.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxModelRel AxSumLibc AxSumStr AxSumMem AxSumAmc AxSumRip2 AxSumBig AxSumD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition code_ck (T : img_tabs) (segs : list Segment) (p : Z * Z) : bool :=
  if fst p =? 4 then rip_ck T segs (snd p)
  else if fst p =? 6 then mc_code_ok segs (snd p)
  else if fst p =? 9 then amc_ck T segs (snd p)
  else false.

(* [comment removed for export] *)
Definition cks_ok (T : img_tabs) (segs : list Segment) : bool := forallb (code_ck T segs) (t_cks T).

Definition ck_has (T : img_tabs) (k b : Z) : bool := existsb (fun p => (fst p =? k) && (snd p =? b)) (t_cks T).

Lemma ck_has_ok (T : img_tabs) (segs : list Segment) (k b : Z) : cks_ok T segs = true -> ck_has T k b = true -> code_ck T segs (k, b) = true.
Proof.
  intros Hok Hh. unfold cks_ok in Hok. rewrite forallb_forall in Hok. unfold ck_has in Hh. apply existsb_exists in Hh as [[k' b'] [Hin Hp]].
  cbn [fst snd] in Hp. apply andb_prop in Hp as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. exact (Hok _ Hin).
Qed.

Definition sum_rip_ck (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  if ck_has T 4 (wZ (a_pc A)) then sum_rip_g ck_true6 T segs LIM A else sum_rip T segs LIM A.
Definition sum_rip2_ck (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  if ck_has T 4 (wZ (a_pc A)) then sum_rip2_g ck_true6 T segs LIM A else sum_rip2 T segs LIM A.
Definition sum_rip_big_ck (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  if ck_has T 4 (wZ (a_pc A)) then sum_rip_big_g ck_true6 T segs LIM A else sum_rip_big T segs LIM A.
Definition sum_memcpy_ck (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  if ck_has T 6 (wZ (a_pc A)) then sum_memcpy_g ck_true1 segs LIM A else sum_memcpy segs LIM A.
Definition sum_memcpy_big_ck (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  if ck_has T 6 (wZ (a_pc A)) then sum_memcpy_big_g ck_true1 segs LIM A else sum_memcpy_big segs LIM A.
Definition sum_amc_ck (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  if ck_has T 9 (wZ (a_pc A)) then sum_amc_g ck_true5 ck_true6 ck_true1 T segs LIM A else sum_amc T segs LIM A.

Local Notation "a 'orelse' b" := (match a with Some l => Some l | None => b end) (at level 60, right associativity, only parsing).

Definition asum_ck0 (T : img_tabs) (segs : list Segment) (LIM : Z) (k : Z) (A : AST) : option (list AST) :=
  if k =? 4 then sum_rip_ck T segs LIM A orelse sum_rip2_ck T segs LIM A orelse sum_rip_big_ck T segs LIM A
  else if k =? 6 then sum_memcpy_ck T segs LIM A orelse sum_memcpy_big_ck T segs LIM A
  else if k =? 9 then sum_amc_ck T segs LIM A
  else asum T segs LIM k A.

(* [comment removed for export] *)
Fixpoint ts_pinned (s : store) (ts : terms) : bool :=
  match ts with
  | [] => false
  | t :: r => match pin_of s (fst t) with Some _ => true | None => ts_pinned s r end
  end.

Fixpoint regs_pinned_l (s : store) (m : aregs) (l : list int) : bool :=
  match l with
  | [] => false
  | r :: l' => if (match aget m r with XS ts _ => ts_pinned s ts | _ => false end) then true else regs_pinned_l s m l'
  end.

Definition ALL_REGS : list int :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%uint63.

Definition regs_pinned (s : store) (m : aregs) : bool := regs_pinned_l s m ALL_REGS.

(* [comment removed for export] *)
Definition canon_state (A : AST) : AST :=
  AS (a_pc A) (renorm_regs (a_facts A) (a_regs A)) (a_resv A) (a_mem A) (a_facts A) (a_model A) (a_budget A) (a_steps A).

Definition asum_ck (T : img_tabs) (segs : list Segment) (LIM : Z) (k : Z) (A : AST) : option (list AST) :=
  match asum_ck0 T segs LIM k A with
  | Some l => Some l
  | None => if regs_pinned (a_facts A) (a_regs A) then asum_ck0 T segs LIM k (canon_state A) else None
  end.

Section Ck.
Variable T : img_tabs.
Hypothesis HT : tabs_ok T = true.
Variable segs : list Segment.
Hypothesis Hck : cks_ok T segs = true.

Lemma sum_rip_ck_eq (LIM : Z) (A : AST) (l : list AST) : sum_rip_ck T segs LIM A = Some l -> sum_rip T segs LIM A = Some l.
Proof.
  unfold sum_rip_ck. destruct (ck_has T 4 (wZ (a_pc A))) eqn:E; [|trivial].
  exact (sum_rip_g_ck T segs LIM A l (ck_has_ok T segs 4 _ Hck E)).
Qed.

Lemma sum_rip2_ck_eq (LIM : Z) (A : AST) (l : list AST) : sum_rip2_ck T segs LIM A = Some l -> sum_rip2 T segs LIM A = Some l.
Proof.
  unfold sum_rip2_ck. destruct (ck_has T 4 (wZ (a_pc A))) eqn:E; [|trivial].
  exact (sum_rip2_g_ck T segs LIM A l (ck_has_ok T segs 4 _ Hck E)).
Qed.

Lemma sum_rip_big_ck_eq (LIM : Z) (A : AST) (l : list AST) : sum_rip_big_ck T segs LIM A = Some l -> sum_rip_big T segs LIM A = Some l.
Proof.
  unfold sum_rip_big_ck. destruct (ck_has T 4 (wZ (a_pc A))) eqn:E; [|trivial].
  exact (sum_rip_big_g_ck T segs LIM A l (ck_has_ok T segs 4 _ Hck E)).
Qed.

Lemma sum_memcpy_ck_eq (LIM : Z) (A : AST) (l : list AST) : sum_memcpy_ck T segs LIM A = Some l -> sum_memcpy segs LIM A = Some l.
Proof.
  unfold sum_memcpy_ck. destruct (ck_has T 6 (wZ (a_pc A))) eqn:E; [|trivial].
  exact (sum_memcpy_g_ck segs LIM A l (ck_has_ok T segs 6 _ Hck E)).
Qed.

Lemma sum_memcpy_big_ck_eq (LIM : Z) (A : AST) (l : list AST) : sum_memcpy_big_ck T segs LIM A = Some l -> sum_memcpy_big segs LIM A = Some l.
Proof.
  unfold sum_memcpy_big_ck. destruct (ck_has T 6 (wZ (a_pc A))) eqn:E; [|trivial].
  exact (sum_memcpy_big_g_ck segs LIM A l (ck_has_ok T segs 6 _ Hck E)).
Qed.

Lemma sum_amc_ck_eq (LIM : Z) (A : AST) (l : list AST) : sum_amc_ck T segs LIM A = Some l -> sum_amc T segs LIM A = Some l.
Proof.
  unfold sum_amc_ck. destruct (ck_has T 9 (wZ (a_pc A))) eqn:E; [|trivial].
  exact (sum_amc_g_ck T segs LIM A l (ck_has_ok T segs 9 _ Hck E)).
Qed.

Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.
Hypothesis KT_emit : forall ρ o bs, KT ρ (o ++ bs) [] -> t_eq (KT ρ o) (t_emit (W 2 bs) (KT ρ (o ++ bs))).

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Theorem asum_ck0_sound (k : Z) (A : AST) (l : list AST) : asum_ck0 T segs LIM k A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  unfold asum_ck0.
  destruct (k =? 4).
  { destruct (sum_rip_ck T segs LIM A) as [l0|] eqn:E1;
      [intros H; injection H as <-; exact (sum_rip_sound T HT segs cfg LIM fs0 KT Hlow A l0 (sum_rip_ck_eq LIM A l0 E1))|].
    destruct (sum_rip2_ck T segs LIM A) as [l0|] eqn:E2;
      [intros H; injection H as <-; exact (sum_rip2_sound T HT segs cfg LIM fs0 KT Hlow A l0 (sum_rip2_ck_eq LIM A l0 E2))|].
    intros H. exact (sum_rip_big_sound T HT segs cfg LIM fs0 KT Hlow A l (sum_rip_big_ck_eq LIM A l H)). }
  destruct (k =? 6).
  { destruct (sum_memcpy_ck T segs LIM A) as [l0|] eqn:E1;
      [intros H; injection H as <-; exact (sum_memcpy_sound segs cfg LIM fs0 KT Hlow A l0 (sum_memcpy_ck_eq LIM A l0 E1))|].
    intros H. exact (sum_memcpy_big_sound segs cfg LIM fs0 KT Hlow A l (sum_memcpy_big_ck_eq LIM A l H)). }
  destruct (k =? 9); [intros H; exact (sum_amc_sound T HT segs cfg LIM fs0 KT Hlow A l (sum_amc_ck_eq LIM A l H))|].
  exact (asum_sound T HT segs cfg LIM fs0 KT Hlow KT_emit k A l).
Qed.

(* [comment removed for export] *)
Lemma R_canon_state (ρ : valuation) (A : AST) (c : config) :
  R segs amodel (MR segs fs0 ρ) LIM ρ A c -> R segs amodel (MR segs fs0 ρ) LIM ρ (canon_state A) c.
Proof.
  intros [Hpc Hal Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hna].
  constructor; cbn [canon_state a_pc a_regs a_resv a_mem a_facts a_model a_budget]; try assumption.
  apply RRegs_renorm; assumption.
Qed.

Theorem asum_ck_sound (k : Z) (A : AST) (l : list AST) : asum_ck T segs LIM k A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  unfold asum_ck. destruct (asum_ck0 T segs LIM k A) as [l0|] eqn:E0.
  - intros H. injection H as <-. exact (asum_ck0_sound k A l0 E0).
  - destruct (regs_pinned (a_facts A) (a_regs A)); [|discriminate]. intros H HS ρ c HR o Ho.
    exact (asum_ck0_sound k (canon_state A) l H HS ρ c (R_canon_state ρ A c HR) o Ho).
Qed.

End Ck.
