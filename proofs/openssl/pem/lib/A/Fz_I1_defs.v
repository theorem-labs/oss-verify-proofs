(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem I_ut Fz_kit Fz_chk Fz_I1_img Fz_I1_hash.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bp (A : Z) : bptr := ((0%N, A), 0).
Lemma bp_inj : forall A A', bp A = bp A' -> A = A'.
Proof. intros A A' H. unfold bp in H. injection H as H1. exact H1. Qed.

(* [comment removed for export] *)
Definition ownL (L : list (Z * Z)) : own_t := fun p A n _ => In (A, n) L /\ p = bp A.

Definition lapart (L : list (Z * Z)) : Prop :=
  forall A1 n1 A2 n2, In (A1, n1) L -> In (A2, n2) L -> (A1, n1) <> (A2, n2) -> A1 + n1 <= A2 \/ A2 + n2 <= A1.

Lemma ownL_apart : forall L, lapart L -> own_apart (ownL L).
Proof.
  intros L HL p1 A1 n1 nm1 p2 A2 n2 nm2 [I1 ->] [I2 ->] NE.
  apply (HL A1 n1 A2 n2 I1 I2). intros E. apply NE. injection E as -> ->. reflexivity.
Qed.

Lemma lapart_perm : forall L L', Permutation L L' -> lapart L -> lapart L'.
Proof. intros L L' HP H A1 n1 A2 n2 I1 I2 NE. apply (H A1 n1 A2 n2); [| | exact NE]; eapply Permutation_in; [apply Permutation_sym; exact HP| eassumption| apply Permutation_sym; exact HP| eassumption]. Qed.

Lemma lapart_sub : forall L L', incl L' L -> lapart L -> lapart L'.
Proof. intros L L' HI H A1 n1 A2 n2 I1 I2 NE. exact (H A1 n1 A2 n2 (HI _ I1) (HI _ I2) NE). Qed.

(* [comment removed for export] *)
Definition LH_CEIL : Z := USTACK_TOP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DVerr (GOBJ : Z -> Z -> Prop) (d : Z) : Prop :=
  d mod 8 = 0 /\ IMG_UT_LO <= d /\ d + 16 <= IMG_UT_HI /\ exists b s, GOBJ b s /\ b <= d /\ d + 16 <= b + s.

(* [comment removed for export] *)
Definition ERR_FNS_A : lh_fns := mkFns e_err_cmp e_err_hash e_err_hash_thunk e_err_comp_thunk.

(* [comment removed for export] *)
Definition lh_repE (GOBJ : Z -> Z -> Prop) (m : mem) (L : list (Z * Z)) (lh B : Z) (g : lh_geo) (bks : list (list (bptr * Z))) : Prop :=
  lh_rep asegs LH_CEIL (DVerr GOBJ) m (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks
  /\ Permutation L ((lh, 104) :: (B, 8 * g_na g) :: map (fun x => (snd x, 24)) (concat bks))
  /\ Forall (fun x => fst x mod 16 = 0) L.          (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FromART.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.

(* [comment removed for export] *)
Lemma live_apart : forall Σ m x y, ART RT Σ m -> In x (rt_live RT Σ) -> In y (rt_live RT Σ) -> x <> y -> fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof using AF.
  intros Σ m [p1 n1] [p2 n2] HA I1 I2 NE. cbn [fst snd].
  destruct (in_split _ _ I1) as (l1 & l2 & EL).
  assert (I2' : In (p2, n2) (l1 ++ l2)).
  { rewrite EL in I2. apply in_app_or in I2. apply in_or_app. destruct I2 as [X|[X|X]]; [left; exact X| exfalso; exact (NE X)| right; exact X]. }
  exact (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 l2 HA EL I2').
Qed.

(* [comment removed for export] *)
Lemma live_lapart : forall Σ m L, ART RT Σ m -> incl L (rt_live RT Σ) -> lapart L.
Proof using AF. intros Σ m L HA HI A1 n1 A2 n2 I1 I2 NE. exact (live_apart Σ m (A1, n1) (A2, n2) HA (HI _ I1) (HI _ I2) NE). Qed.

(* [comment removed for export] *)
Lemma live_sel_facts : forall Σ m L p n lo, ART RT Σ m -> incl L (rt_live RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= lo -> In (p, n) L ->
  acc asegs m p n /\ wr_at asegs m p n /\ 0 < p /\ p + n <= lo.
Proof using AF.
  intros Σ m L p n lo HA HI HLO Hin. pose proof (HI _ Hin) as HinL.
  destruct (af_acc_live RT AF Σ m p n HA HinL) as [W A]. pose proof (af_live_range RT AF Σ m p n HA HinL) as (P0 & P1 & _).
  split; [exact A|]. split; [exact W|]. split; [exact P0| lia].
Qed.

(* [comment removed for export] *)
Lemma dverr_cells : forall Σ m d, ART RT Σ m -> DVerr GOBJ d ->
  (exists e : word, ro_cells asegs m d [C8 e]) /\ acc asegs m d 8 /\ acc asegs m d 16.
Proof using AF AFP.
  intros Σ m d HA (AL & LO & HI & b & s & G & B1 & B2).
  destruct (af_client_consts RT AF Σ m HA) as (_ & _ & _ & _ & UT).
  split; [exact (ut_ro_C8_any m d UT LO ltac:(lia))|].
  split; apply (afp_acc_global RT GOBJ AFP Σ m b s); try exact HA; try exact G; lia.
Qed.

End FromART.
