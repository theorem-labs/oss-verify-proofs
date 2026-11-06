(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LazyModel NodesA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanOps AsanHoare AsanFakeStack AsanPS AsanBudget2 AsanSucc AsanSucc2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_alloc_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sall_arun : forall {R} (Q : astate * aout R -> Prop) fuel (t : stree aev aans (astate * aout R)) orc s o evs orc',
  sall Q t -> arun fuel t orc = Some (s, o, evs, orc') -> Q (s, o).
Proof.
  intros R Q fuel. induction fuel as [|fuel IH]; intros t orc s o evs orc' HS HR.
  - destruct t as [[s1 o1]|e k]; cbn in HR; [injection HR as -> -> <- ->; exact HS|]. destruct orc; discriminate.
  - destruct t as [[s1 o1]|e k]; cbn in HR; [injection HR as -> -> <- ->; exact HS|].
    destruct orc as [|a rest]; [discriminate|]. cbn in HS.
    destruct (arun fuel (k a) rest) as [p|] eqn:HR2; [| discriminate].
    destruct p as [[[s2 o2] evs2] orc2].
    injection HR as E1 E2 E3 E4. subst. exact (IH (k a) rest _ _ _ _ (HS a) HR2).
Qed.
Lemma hoareW_arun : forall {R} (P : astate -> Prop) (m : AM R) (Q : astate -> R -> Prop) s0 fuel orc s' r evs orc',
  hoareW P m Q -> P s0 -> arun fuel (m s0) orc = Some (s', ONorm r, evs, orc') -> Q s' r.
Proof.
  intros R P m Q s0 fuel orc s' r evs orc' HW HP HR.
  exact (sall_arun (leaf_okW Q) fuel (m s0) orc s' (ONorm r) evs orc' (HW s0 HP) HR).
Qed.
Lemma hoare_arun : forall {R} (P : astate -> Prop) (m : AM R) (Q : astate -> R -> Prop) s0 fuel orc s' r evs orc',
  hoare P m Q -> P s0 -> arun fuel (m s0) orc = Some (s', ONorm r, evs, orc') -> Q s' r.
Proof.
  intros R P m Q s0 fuel orc s' r evs orc' HW HP HR.
  exact (sall_arun (leaf_ok Q) fuel (m s0) orc s' (ONorm r) evs orc' (HW s0 HP) HR).
Qed.

(* [comment removed for export] *)
Definition agrantb (a : aans) : bool := match a with AnsOk _ => true | AnsErr _ => false end.

Lemma gall_arun : forall {R} (G : R -> Prop) fuel (t : stree aev aans (astate * aout R)) orc s o evs orc',
  gall G t -> Forall (fun a => agrantb a = true) orc -> arun fuel t orc = Some (s, o, evs, orc') ->
  match o with ONorm r => G r | OSpin => False | OUndef _ => True end.
Proof.
  intros R G fuel. induction fuel as [|fuel IH]; intros t orc s o evs orc' HS HO HR.
  - destruct t as [[s1 o1]|e k]; cbn in HR; [injection HR as -> -> <- ->; exact HS|]. destruct orc; discriminate.
  - destruct t as [[s1 o1]|e k]; cbn in HR; [injection HR as -> -> <- ->; exact HS|].
    destruct orc as [|a rest]; [discriminate|]. cbn in HS. inversion HO as [|a' l Ha HO']; subst.
    destruct (arun fuel (k a) rest) as [p|] eqn:HR2; [| discriminate].
    destruct p as [[[s2 o2] evs2] orc2].
    injection HR as E1 E2 E3 E4. subst. apply (IH (k a) rest _ _ _ _ (HS a ltac:(destruct a; [exact I| discriminate Ha])) HO' HR2).
Qed.

Lemma gallS_arun : forall {R} (G : astate -> R -> Prop) fuel (t : stree aev aans (astate * aout R)) orc s o evs orc',
  gallS G t -> Forall (fun a => agrantb a = true) orc -> arun fuel t orc = Some (s, o, evs, orc') ->
  match o with ONorm r => G s r | OSpin => False | OUndef _ => True end.
Proof.
  intros R G fuel. induction fuel as [|fuel IH]; intros t orc s o evs orc' HS HO HR.
  - destruct t as [[s1 o1]|e k]; cbn in HR; [injection HR as -> -> <- ->; exact HS|]. destruct orc; discriminate.
  - destruct t as [[s1 o1]|e k]; cbn in HR; [injection HR as -> -> <- ->; exact HS|].
    destruct orc as [|a rest]; [discriminate|]. cbn in HS. inversion HO as [|a' l Ha HO']; subst.
    destruct (arun fuel (k a) rest) as [p|] eqn:HR2; [| discriminate].
    destruct p as [[[s2 o2] evs2] orc2].
    injection HR as E1 E2 E3 E4. subst. apply (IH (k a) rest _ _ _ _ (HS a ltac:(destruct a; [exact I| discriminate Ha])) HO' HR2).
Qed.

(* [comment removed for export] *)
Lemma gok_arun_norm : forall {R} (m : AM R) (G : R -> Prop) s0 fuel orc s' r evs orc',
  gok m G -> Forall (fun a => agrantb a = true) orc -> arun fuel (m s0) orc = Some (s', ONorm r, evs, orc') -> G r.
Proof. intros R m G s0 fuel orc s' r evs orc' HG HO HR. exact (gall_arun G fuel (m s0) orc s' (ONorm r) evs orc' (HG s0) HO HR). Qed.
Lemma gok_arun_nospin : forall {R} (m : AM R) (G : R -> Prop) s0 fuel orc s' evs orc',
  gok m G -> Forall (fun a => agrantb a = true) orc -> arun fuel (m s0) orc = Some (s', OSpin, evs, orc') -> False.
Proof. intros R m G s0 fuel orc s' evs orc' HG HO HR. exact (gall_arun G fuel (m s0) orc s' OSpin evs orc' (HG s0) HO HR). Qed.
Lemma ghoare_arun_norm : forall {R} (P : astate -> Prop) (m : AM R) (G : astate -> R -> Prop) s0 fuel orc s' r evs orc',
  ghoare P m G -> P s0 -> Forall (fun a => agrantb a = true) orc -> arun fuel (m s0) orc = Some (s', ONorm r, evs, orc') -> G s' r.
Proof. intros R P m G s0 fuel orc s' r evs orc' HG HP HO HR. exact (gallS_arun G fuel (m s0) orc s' (ONorm r) evs orc' (HG s0 HP) HO HR). Qed.
Lemma ghoare_arun_nospin : forall {R} (P : astate -> Prop) (m : AM R) (G : astate -> R -> Prop) s0 fuel orc s' evs orc',
  ghoare P m G -> P s0 -> Forall (fun a => agrantb a = true) orc -> arun fuel (m s0) orc = Some (s', OSpin, evs, orc') -> False.
Proof. intros R P m G s0 fuel orc s' evs orc' HG HP HO HR. exact (gallS_arun G fuel (m s0) orc s' OSpin evs orc' (HG s0 HP) HO HR). Qed.

Lemma amalloc_arun_some : forall E key n s0 fuel orc s' r evs orc',
  Forall (fun a => agrantb a = true) orc -> arun fuel (amalloc E key n s0) orc = Some (s', ONorm r, evs, orc') -> exists p, r = Some p.
Proof. intros E key n s0 fuel orc s' r evs orc' HO HR. exact (gok_arun_norm _ _ s0 fuel orc s' r evs orc' (gok_amalloc E key n) HO HR). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint hsum (H : list aevent) : Z :=
  match H with [] => 0 | EvMalloc n _ :: t => n + hsum t | _ :: t => hsum t end.
Fixpoint nfree (H : list aevent) : Z :=
  match H with [] => 0 | EvFree _ :: t => 1 + nfree t | _ :: t => nfree t end.
Definition xsum (X : list (Z * Z)) : Z := fold_right (fun b acc => snd b + acc) 0 X.
Definition cyZ (H : list aevent) : Z := Z.of_nat (count_yfuzz H).
Lemma xsum_perm : forall X Y, Permutation X Y -> xsum X = xsum Y.
Proof. intros X Y P. unfold xsum. induction P; cbn; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Rel.
Variable E0 : aenv.
Definition aps_frame_alloc (s s' : aps) : Prop :=
  aps_env s' = aps_env s /\ aps_fsbase s' = aps_fsbase s /\ aps_fs s' = aps_fs s /\ aps_so s' = aps_so s /\ aps_initialized s' = aps_initialized s.
Definition amalloc_rel (n : Z) (s : aps) (mo : Model) (r : option Z) (s' : aps) (mo' : Model) : Prop :=
  (exists key fuel orc evs orc', arun fuel (amalloc E0 key n (aps_alloc s)) orc = Some (aps_alloc s', ONorm r, evs, orc'))
  /\ aps_credit s - acharge n <= aps_credit s' /\ aps_frame_alloc s s'.
Definition afree_rel (p : Z) (s : aps) (mo : Model) (s' : aps) (mo' : Model) : Prop :=
  (exists key fuel orc evs orc', arun fuel (afree E0 key p (aps_alloc s)) orc = Some (aps_alloc s', ONorm tt, evs, orc'))
  /\ aps_credit s - 1 <= aps_credit s' /\ aps_frame_alloc s s'.
Definition arealloc_rel (p n : Z) (s : aps) (mo : Model) (r : option Z) (s' : aps) (mo' : Model) : Prop :=
  (exists key fuel orc evs orc', arun fuel (arealloc E0 key p n (aps_alloc s)) orc = Some (aps_alloc s', ONorm r, evs, orc'))
  /\ aps_credit s - acharge n - 1 <= aps_credit s' /\ aps_frame_alloc s s'.
(* [comment removed for export] *)
Definition ayfuzz_rel (s : aps) (mo : Model) (s' : aps) (mo' : Model) : Prop :=
  aps_credit s - ycost (2^26) <= aps_credit s' /\ aps_env s' = aps_env s /\ aps_fsbase s' = aps_fsbase s.
Definition aalloc_same (s s' : aps) : Prop :=
  aps_alloc s' = aps_alloc s /\ aps_credit s' = aps_credit s /\ aps_env s' = aps_env s /\ aps_fsbase s' = aps_fsbase s /\ aps_fs s' = aps_fs s.
Lemma aalloc_same_refl : aalloc_same_refl_stmt aps aalloc_same.
Proof. intros s. repeat split; reflexivity. Qed.
End Rel.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Cm_max : Z := 18500.
Definition Ymax : Z := ycost (2^26).
Definition yleft (H : list aevent) : Z := Z.max 0 (4 - cyZ H).

Definition AHEAD (k : nat) (X : list (Z * Z)) (H : list aevent) (s : aps) (mo : Model) : Prop :=
  (Cm_max + 1) * Z.of_nat k + yleft H * Ymax + 2 <= aps_credit s.   (* [comment removed for export] *)

Lemma acharge_le_Cm : forall n, 0 <= n <= 2^26 -> acharge n <= Cm_max.
Proof.
  intros n Hn. unfold acharge, Cm_max, kCmPrim. pose proof (map_size_le n ltac:(lia)) as ML. pose proof (map_size_pos n) as MP.
  change kPageSize with 4096 in MP.
  destruct (from_primary n); [lia|]. destruct (map_size n <? kBigMapSize); Z.div_mod_to_equations; lia.
Qed.
Lemma Ymax_val : Ymax = 10794304.
Proof. reflexivity. Qed.
Lemma ycost_le_Ymax : forall L, 0 <= L <= 2^26 -> ycost L <= Ymax.
Proof. intros L HL. rewrite Ymax_val. unfold ycost. Z.div_mod_to_equations. lia. Qed.
Lemma ycost_nonneg : forall L, 0 <= L -> 0 <= ycost L.
Proof. intros L HL. unfold ycost. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma ahead_credit_malloc : ahead_credit_malloc_stmt aps aps_credit acharge AHEAD.
Proof.
  intros s mo k X H n CR Hn. unfold AHEAD in CR. pose proof (acharge_le_Cm n Hn) as AC. unfold yleft, Cm_max in *. rewrite Ymax_val in CR.
  rewrite Nat2Z.inj_succ in CR.
  assert (P1 : 0 <= Z.max 0 (4 - cyZ H) * 10794304) by (pose proof (Z.le_max_l 0 (4 - cyZ H)); nia).
  assert (P2 : 18500 + 1 <= (18500 + 1) * Z.succ (Z.of_nat k)) by nia.
  lia.
Qed.
Lemma ahead_credit_free : ahead_credit_free_stmt aps aps_credit AHEAD.
Proof.
  intros s mo k X H A CR. unfold AHEAD in CR. unfold yleft, Cm_max in *. rewrite Ymax_val in CR.
  rewrite Nat2Z.inj_succ in CR.
  assert (P1 : 0 <= Z.max 0 (4 - cyZ H) * 10794304) by (pose proof (Z.le_max_l 0 (4 - cyZ H)); nia).
  assert (P2 : 18500 + 1 <= (18500 + 1) * Z.succ (Z.of_nat k)) by nia.
  assert (AC : afree_cost A <= 1) by (unfold afree_cost; destruct (Z.eqb A 0); lia).
  lia.
Qed.
Lemma ahead_reserve : ahead_reserve_stmt aps aps_credit AHEAD.
Proof.
  intros s mo k X H CR. unfold AHEAD in CR. unfold yleft, Cm_max in *. rewrite Ymax_val in CR.
  assert (P1 : 0 <= Z.max 0 (4 - cyZ H) * 10794304) by (pose proof (Z.le_max_l 0 (4 - cyZ H)); nia).
  lia.
Qed.
Lemma ahead_credit_yfuzz : ahead_credit_yfuzz_stmt aps aps_credit AHEAD.
Proof.
  intros s mo k X H L CR Hc HL. unfold AHEAD in CR. pose proof (ycost_le_Ymax L ltac:(lia)) as YC. pose proof (ycost_nonneg (2^26) ltac:(lia)) as Y0.
  unfold yleft, cyZ, Ymax in *.
  assert (1 <= Z.max 0 (4 - Z.of_nat (count_yfuzz H))) by lia.
  assert (0 <= (Cm_max + 1) * Z.of_nat k) by (unfold Cm_max; lia). nia.
Qed.

(* [comment removed for export] *)
Lemma ahead_perm : ahead_perm_stmt aps AHEAD.
Proof. intros s mo k X Y H A _. exact A. Qed.
Lemma ahead_weaken : ahead_weaken_stmt aps AHEAD.
Proof.
  intros s mo k X H CR. unfold AHEAD in *. rewrite Nat2Z.inj_succ in CR. unfold Cm_max, yleft in *. rewrite Ymax_val in *.
  pose proof (Z.le_max_l 0 (4 - cyZ H)). nia.
Qed.
Lemma ahead_magree : ahead_magree_stmt aps AHEAD.
Proof. intros s mo mo' k X H A _. exact A. Qed.
Lemma ahead_vmsame : ahead_vmsame_stmt aps AHEAD.
Proof. intros s mo mo' k X H A _. exact A. Qed.
Lemma ahead_aps : ahead_aps_stmt aps aalloc_same AHEAD.
Proof. intros s s' mo k X H CR (E1 & E2 & _). unfold AHEAD in *. rewrite E2; exact CR. Qed.

(* [comment removed for export] *)
Lemma AHEAD_init : forall E fsb mo, AHEAD 40%nat [] [] (aps_init E fsb) mo.
Proof.
  intros E fsb mo. unfold AHEAD. cbn [aps_credit aps_init]. unfold kInitialCredit, yleft, cyZ, Cm_max. cbn [count_yfuzz List.filter length Z.of_nat]. rewrite Ymax_val.
  cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Steps.
Variable E0 : aenv.

Lemma ahead_malloc : ahead_malloc_stmt aps (amalloc_rel E0) AHEAD.
Proof.
  intros s mo n k X H A s' mo' CR Hn (_ & CRD & _). unfold AHEAD in *.
  pose proof (acharge_le_Cm n ltac:(lia)). rewrite Nat2Z.inj_succ in CR.
  assert (YL : yleft (EvMalloc n (Some A) :: H) = yleft H) by reflexivity. rewrite YL.
  unfold yleft in *. rewrite Ymax_val in *. pose proof (Z.le_max_l 0 (4 - cyZ H)). unfold Cm_max in *. nia.
Qed.

Lemma ahead_free : ahead_free_stmt aps (afree_rel E0) AHEAD.
Proof.
  intros s mo A n k X H s' mo' CR (_ & CRD & _). unfold AHEAD in *.
  rewrite Nat2Z.inj_succ in CR. assert (YL : yleft (EvFree A :: H) = yleft H) by reflexivity. rewrite YL.
  unfold yleft in *. rewrite Ymax_val in *. pose proof (Z.le_max_l 0 (4 - cyZ H)). unfold Cm_max in *. nia.
Qed.

Lemma ahead_free0 : ahead_free0_stmt aps (afree_rel E0) AHEAD.
Proof. intros s mo k X H s' mo' A R. exact (ahead_free s mo 0 0 k X H s' mo' A R). Qed.

Lemma ahead_yfuzz : ahead_yfuzz_stmt aps ayfuzz_rel AHEAD.
Proof.
  intros s mo k X H s' mo' CR Hc (CRD & _ & _). unfold AHEAD in *.
  rewrite Nat2Z.inj_succ in CR.
  assert (YL : yleft (EvYfuzz :: H) = yleft H - 1).
  { unfold yleft, cyZ. cbn [count_yfuzz List.filter length]. fold (count_yfuzz H). rewrite Nat2Z.inj_succ. lia. }
  rewrite YL. unfold yleft, cyZ, Ymax, Cm_max in *. pose proof (ycost_nonneg (2^26) ltac:(lia)). nia.
Qed.
End Steps.
End RC__1.
