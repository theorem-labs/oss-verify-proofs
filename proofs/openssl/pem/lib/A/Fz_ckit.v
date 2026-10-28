(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_libiface_pem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record cli_rt (RT : rt_sig) (GOBJ : Z -> Z -> Prop) : Prop := mkCliRT {
  cr_af : art_facts RT;                  (* [comment removed for export] *)
  cr_afp : art_facts_pem RT GOBJ;        (* [comment removed for export] *)
  cr_rc : rt_contracts RT;               (* [comment removed for export] *)
  cr_rcp : rt_contracts_pem RT           (* [comment removed for export] *)
}.
Arguments cr_af {RT GOBJ} _. Arguments cr_afp {RT GOBJ} _. Arguments cr_rc {RT GOBJ} _. Arguments cr_rcp {RT GOBJ} _.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cg_has_weaken : forall cg s c s' c', cg_has cg s c -> inclP s' s = true -> inclP c' c = true -> cg_has cg s' c'.
Proof. intros cg s c s' c' H H1 H2. exact (cg_has_sub cg s c s' c' H (inclP_sound _ _ H1) (inclP_sound _ _ H2)). Qed.

(* [comment removed for export] *)
Definition cg_sub (s c S C : list (Z * Z)) : Prop := incl s S /\ incl c C.
Lemma cg_has_of_sub : forall cg s c S C, cg_has cg S C -> cg_sub s c S C -> cg_has cg s c.
Proof. intros cg s c S C H [H1 H2]. exact (cg_has_sub cg S C s c H H1 H2). Qed.
Lemma cg_sub_lit : forall s c S C, inclP s S = true -> inclP c C = true -> cg_sub s c S C.
Proof. intros s c S C H1 H2. split; apply inclP_sound; assumption. Qed.
Lemma cg_sub_trans : forall s c s' c' S C, cg_sub s c s' c' -> cg_sub s' c' S C -> cg_sub s c S C.
Proof. intros s c s' c' S C [A1 A2] [B1 B2]. split; eapply incl_tran; eassumption. Qed.
Lemma cg_sub_app : forall s1 c1 s2 c2 S C, cg_sub s1 c1 S C -> cg_sub s2 c2 S C -> cg_sub (s1 ++ s2) (c1 ++ c2) S C.
Proof. intros s1 c1 s2 c2 S C [A1 A2] [B1 B2]. split; apply incl_app; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record rep_pkg : Type := mkRP {
  rp_rep : list (Z * Z) -> mem -> Prop;
  rp_cells : list (Z * Z);
  rp_sub : forall x, in_ranges rp_cells x -> in_ranges LIB_D x;
  rp_local : forall CL (m m' : mem), rp_rep CL m ->
               (forall a : word, in_ranges rp_cells (bv_unsigned a) \/ in_live CL (bv_unsigned a) -> m' a = m a) -> rp_rep CL m';
  rp_pos : forall CL m p n, rp_rep CL m -> In (p, n) CL -> 0 < n
}.

(* [comment removed for export] *)
Lemma rp_lib_local : forall P : rep_pkg, lib_local_d (rp_rep P).
Proof.
  intros P CL m m' H AG. apply (rp_local P CL m m' H). intros a [Ha|Ha]; apply AG; [left; exact (rp_sub P _ Ha) | right; exact Ha].
Qed.

Lemma in_live_app : forall l1 l2 a, in_live (l1 ++ l2) a <-> in_live l1 a \/ in_live l2 a.
Proof.
  intros l1 l2 a. unfold in_live. split.
  - intros (p & n & Hin & Ha). apply in_app_or in Hin as [Hin|Hin]; [left|right]; exists p, n; split; assumption.
  - intros [(p & n & Hin & Ha)|(p & n & Hin & Ha)]; exists p, n; split; [apply in_or_app; left; exact Hin| exact Ha| apply in_or_app; right; exact Hin| exact Ha].
Qed.
Lemma in_live_perm : forall l l' a, Permutation l l' -> in_live l a -> in_live l' a.
Proof. intros l l' a HP (p & n & Hin & Ha). exists p, n. split; [exact (Permutation_in _ HP Hin)| exact Ha]. Qed.
Lemma in_ranges_app : forall l1 l2 x, in_ranges (l1 ++ l2) x <-> in_ranges l1 x \/ in_ranges l2 x.
Proof.
  intros l1 l2 x. unfold in_ranges. split.
  - intros (lo & hi & Hin & Hx). apply in_app_or in Hin as [Hin|Hin]; [left|right]; exists lo, hi; split; assumption.
  - intros [(lo & hi & Hin & Hx)|(lo & hi & Hin & Hx)]; exists lo, hi; split; [apply in_or_app; left; exact Hin| exact Hx| apply in_or_app; right; exact Hin| exact Hx].
Qed.

(* [comment removed for export] *)
Definition rp_join_rep (P Q : rep_pkg) (CL : list (Z * Z)) (m : mem) : Prop :=
  exists CL1 CL2, Permutation CL (CL1 ++ CL2) /\ rp_rep P CL1 m /\ rp_rep Q CL2 m.

Lemma rp_join_sub : forall P Q x, in_ranges (rp_cells P ++ rp_cells Q) x -> in_ranges LIB_D x.
Proof. intros P Q x H. apply in_ranges_app in H as [H|H]; [exact (rp_sub P _ H)| exact (rp_sub Q _ H)]. Qed.

Lemma rp_join_local : forall P Q CL (m m' : mem), rp_join_rep P Q CL m ->
  (forall a : word, in_ranges (rp_cells P ++ rp_cells Q) (bv_unsigned a) \/ in_live CL (bv_unsigned a) -> m' a = m a) -> rp_join_rep P Q CL m'.
Proof.
  intros P Q CL m m' (CL1 & CL2 & HP & H1 & H2) AG. exists CL1, CL2. split; [exact HP|]. split.
  - apply (rp_local P CL1 m m' H1). intros a [Ha|Ha]; apply AG.
    + left. apply in_ranges_app. left. exact Ha.
    + right. apply (in_live_perm _ _ _ (Permutation_sym HP)). apply in_live_app. left. exact Ha.
  - apply (rp_local Q CL2 m m' H2). intros a [Ha|Ha]; apply AG.
    + left. apply in_ranges_app. right. exact Ha.
    + right. apply (in_live_perm _ _ _ (Permutation_sym HP)). apply in_live_app. right. exact Ha.
Qed.

Lemma rp_join_pos : forall P Q CL m p n, rp_join_rep P Q CL m -> In (p, n) CL -> 0 < n.
Proof.
  intros P Q CL m p n (CL1 & CL2 & HP & H1 & H2) Hin.
  apply (Permutation_in _ HP) in Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (rp_pos P CL1 m p n H1 Hin)| exact (rp_pos Q CL2 m p n H2 Hin)].
Qed.

Definition rp_join (P Q : rep_pkg) : rep_pkg :=
  mkRP (rp_join_rep P Q) (rp_cells P ++ rp_cells Q) (rp_join_sub P Q) (rp_join_local P Q) (rp_join_pos P Q).

(* [comment removed for export] *)
Lemma rp_join_perm : forall P Q CL CL' m, Permutation CL CL' -> rp_join_rep P Q CL m -> rp_join_rep P Q CL' m.
Proof. intros P Q CL CL' m HP (CL1 & CL2 & H & H1 & H2). exists CL1, CL2. split; [| split; assumption]. exact (Permutation_trans (Permutation_sym HP) H). Qed.

(* [comment removed for export] *)
Lemma rp_lib0_local : forall P : rep_pkg, lib0_local_d (fun m => rp_rep P [] m).
Proof.
  intros P m m' H AG. apply (rp_local P [] m m' H). intros a [Ha|(p & n & Hin & _)]; [apply AG; exact (rp_sub P _ Ha)| destruct Hin].
Qed.
