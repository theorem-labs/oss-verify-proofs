(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module CXFI.
Import AX2. Import APC.

Definition smemo : Type := list (expr * expr).
(* [comment removed for export] *)
Definition sm_get (m : smemo) (x : expr) : option expr :=
  match m with
  | [] => None
  | (k, v) :: _ => if expr_eqb x k then Some v else None
  end.
Section Pass.
Variables (J : nat) (e : expr).
Definition sm_ok (m : smemo) : Prop := forall k v, In (k, v) m -> v = esubst J e k.
Lemma sm_get_ok : forall m x v, sm_ok m -> sm_get m x = Some v -> v = esubst J e x.
Proof.
  intros [|[k w] r] x v H G; cbn in G; [discriminate|].
  destruct (expr_eqb x k) eqn:E; [|discriminate].
  injection G as <-. apply AX2B.p_expr_eqb_eq in E. subst k. apply H. left. reflexivity.
Qed.
(* [comment removed for export] *)
Definition bsubM (x : expr) (m : smemo) : expr * smemo :=
  match x with
  | ELit _ => (x, m)
  | EVar n => ((if Nat.eqb n J then e else x), m)
  | _ => match sm_get m x with
         | Some v => (v, m)
         | None => let v := esubst J e x in (v, [(x, v)])
         end
  end.
Lemma bsubM_spec : forall x m, sm_ok m -> fst (bsubM x m) = esubst J e x /\ sm_ok (snd (bsubM x m)).
Proof.
  intros x m H. unfold bsubM.
  assert (G : fst (match sm_get m x with Some v => (v, m) | None => let v := esubst J e x in (v, [(x, v)]) end) = esubst J e x
              /\ sm_ok (snd (match sm_get m x with Some v => (v, m) | None => let v := esubst J e x in (v, [(x, v)]) end))).
  { destruct (sm_get m x) as [v|] eqn:E; cbn [fst snd].
    - split; [exact (sm_get_ok m x v H E) | exact H].
    - split; [reflexivity|]. intros k w [IN|[]]. injection IN as <- <-. reflexivity. }
  destruct x; try exact G; cbn [fst snd esubst]; split; try reflexivity; exact H.
Qed.
Definition asubM (a : saddr) (m : smemo) : saddr * smemo := let '(b, m') := bsubM (a_base a) m in (SA b (a_off a), m').
Lemma asubM_spec : forall a m, sm_ok m -> fst (asubM a m) = asubst J e a /\ sm_ok (snd (asubM a m)).
Proof.
  intros a m H. unfold asubM, asubst. destruct (bsubM_spec (a_base a) m H) as [E1 E2].
  destruct (bsubM (a_base a) m) as [b m']. cbn [fst snd] in *. subst b. split; [reflexivity|exact E2].
Qed.
Definition ksubM (K : kentry) (m : smemo) : kentry * smemo :=
  match K with
  | KWord a w v => let '(a', m') := asubM a m in (KWord a' w (esubst J e v), m')
  | KZero a n => let '(a', m') := asubM a m in (KZero a' (esubst J e n), m')
  | KBlob a n k => let '(a', m') := asubM a m in (KBlob a' (esubst J e n) k, m')
  | KImg lo hi => (K, m)
  | KAlign x mm => (KAlign (esubst J e x) mm, m)
  | KRange x lo hi => (KRange (esubst J e x) lo hi, m)
  | KWr a n => let '(a', m') := asubM a m in (KWr a' (esubst J e n), m')
  | KDisj a1 n1 a2 n2 => let '(a1', m1) := asubM a1 m in let '(a2', m2) := asubM a2 m1 in (KDisj a1' (esubst J e n1) a2' (esubst J e n2), m2)
  | KFill a n c => let '(a', m') := asubM a m in (KFill a' (esubst J e n) c, m')
  | KUnk a n => let '(a', m') := asubM a m in (KUnk a' (esubst J e n), m')
  end.
Lemma ksubM_spec : forall K m, sm_ok m -> fst (ksubM K m) = ksubst J e K /\ sm_ok (snd (ksubM K m)).
Proof.
  intros K m H. destruct K as [a w v|a n|a n k|lo hi|x mm|x lo hi|a n|a1 n1 a2 n2|a n c|a n]; cbn [ksubM ksubst];
    try (split; [reflexivity|exact H]);
    try (destruct (asubM_spec a m H) as [E1 E2]; destruct (asubM a m) as [a' m']; cbn [fst snd] in *; subst a'; split; [reflexivity|exact E2]).
  destruct (asubM_spec a1 m H) as [E1 E2]. destruct (asubM a1 m) as [a1' m1]. cbn [fst snd] in *. subst a1'.
  destruct (asubM_spec a2 m1 E2) as [E3 E4]. destruct (asubM a2 m1) as [a2' m2]. cbn [fst snd] in *. subst a2'. split; [reflexivity|exact E4].
Qed.
Fixpoint knsubM (k : list kentry) (m : smemo) : list kentry :=
  match k with
  | [] => []
  | K :: r => let '(K', m') := ksubM K m in K' :: knsubM r m'
  end.
Lemma knsubM_eq : forall k m, sm_ok m -> knsubM k m = map (ksubst J e) k.
Proof.
  induction k as [|K r IH]; intros m H; [reflexivity|]. cbn [knsubM map].
  destruct (ksubM_spec K m H) as [E1 E2]. destruct (ksubM K m) as [K' m']. cbn [fst snd] in *. subst K'. rewrite (IH m' E2). reflexivity.
Qed.
End Pass.


(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint rebuild (x : expr) : expr :=
  match x with
  | ELit _ => x
  | EVar _ => x
  | EAlu op a b => mkAlu op (rebuild a) (rebuild b)
  | EAluw op a b => mkAluw op (rebuild a) (rebuild b)
  | EMd op a b => mkMd op (rebuild a) (rebuild b)
  | EMdw op a b => mkMdw op (rebuild a) (rebuild b)
  | EExt sx lo n a => EExt sx lo n (rebuild a)
  | EBlob _ _ _ _ => x
  end.
Lemma esubst_absent : forall J e x, mentions_var J x = false -> esubst J e x = rebuild x.
Proof.
  intros J e x. induction x as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|s k i n]; cbn [mentions_var esubst rebuild]; intros H;
    try reflexivity;
    try (destruct (mentions_var J a) eqn:Ea; [discriminate|]; rewrite (IHa eq_refl), (IHb H); reflexivity).
  - rewrite Nat.eqb_sym. rewrite H. reflexivity.
  - rewrite (IHa H). reflexivity.
Qed.
(* [comment removed for export] *)
Fixpoint esubst_seq (s : list (nat * expr)) (x : expr) : expr :=
  match s with
  | [] => x
  | (J, e) :: r => esubst J e (esubst_seq r x)
  end.
Definition stable (s : list (nat * expr)) (x : expr) : bool :=
  if forallb (fun p => negb (mentions_var (fst p) x)) s then expr_eqb (rebuild x) x else false.
Lemma stable_seq : forall s x, stable s x = true -> esubst_seq s x = x.
Proof.
  intros s x H. unfold stable in H. destruct (forallb (fun p => negb (mentions_var (fst p) x)) s) eqn:F; [|discriminate].
  apply AX2B.p_expr_eqb_eq in H. induction s as [|[J e] r IH]; [reflexivity|]. cbn [esubst_seq].
  cbn [forallb fst] in F. apply andb_prop in F as [F1 F2]. rewrite (IH F2). rewrite esubst_absent by (destruct (mentions_var J x); [discriminate|reflexivity]). exact H.
Qed.
Definition ksubst_seq (s : list (nat * expr)) (K : kentry) : kentry := fold_right (fun p K => ksubst (fst p) (snd p) K) K s.
Definition astable (s : list (nat * expr)) (a : saddr) : bool := stable s (a_base a).
Definition kstable (s : list (nat * expr)) (K : kentry) : bool :=
  match K with
  | KWord a _ v => if astable s a then stable s v else false
  | KZero a n | KWr a n | KUnk a n | KBlob a n _ | KFill a n _ => if astable s a then stable s n else false
  | KImg _ _ => true
  | KAlign x _ | KRange x _ _ => stable s x
  | KDisj a1 n1 a2 n2 => if astable s a1 then if stable s n1 then if astable s a2 then stable s n2 else false else false else false
  end.
Lemma ksubst_seq_cons : forall J e r K, ksubst_seq ((J, e) :: r) K = ksubst J e (ksubst_seq r K).
Proof. reflexivity. Qed.
Lemma kstable_seq : forall s K, kstable s K = true -> ksubst_seq s K = K.
Proof.
  intros s K H. induction s as [|[J e] r IH]; [reflexivity|]. rewrite ksubst_seq_cons.
  assert (Hr : kstable r K = true).
  { clear IH. unfold kstable, astable, stable in *. cbn [forallb fst] in H.
    destruct K as [a w v|a n|a n k|lo hi|x mm|x lo hi|a n|a1 n1 a2 n2|a n c|a n]; try reflexivity;
      repeat match type of H with
             | (if (if ?c && ?d then _ else _) then _ else _) = true => destruct c; cbn [andb negb] in H; [|discriminate]
             | (if ?c && ?d then _ else _) = true => destruct c; cbn [andb negb] in H; [|discriminate]
             | (if ?c then _ else _) = true => destruct c eqn:?; [|discriminate]
             end; try exact H; try reflexivity. }
  rewrite (IH Hr).
  assert (ST : forall x, stable ((J, e) :: r) x = true -> esubst J e x = x).
  { intros x Hx. pose proof (stable_seq ((J, e) :: r) x Hx) as E1. cbn [esubst_seq] in E1.
    assert (Hx' : stable r x = true).
    { unfold stable in *. cbn [forallb fst] in Hx. destruct (negb (mentions_var J x)); cbn [andb] in Hx; [|discriminate]. exact Hx. }
    rewrite (stable_seq r x Hx') in E1. exact E1. }
  unfold kstable, astable in H.
  destruct K as [a w v|a n|a n k|lo hi|x mm|x lo hi|a n|a1 n1 a2 n2|a n c|a n]; cbn [ksubst]; unfold asubst; try reflexivity;
    repeat match type of H with (if ?c then _ else _) = true => destruct c eqn:?; [|discriminate] end;
    repeat match goal with
           | Hs : stable ((J, e) :: r) ?y = true |- _ => rewrite (ST y Hs); clear Hs
           end; try (rewrite (ST _ H)); try (destruct a; reflexivity); try (destruct a1, a2; reflexivity); reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint mk_dom (s : list (nat * expr)) : ptree unit :=
  match s with [] => PTLeaf | (J, _) :: r => pt_set (vkey J) tt (mk_dom r) end.
Lemma mk_dom_in : forall s J e, In (J, e) s -> pt_get (mk_dom s) (vkey J) = Some tt.
Proof.
  induction s as [|[J' e'] r IH]; intros J e IN; [contradiction|]. cbn [mk_dom].
  destruct IN as [E|IN]; [injection E as -> _; apply pt_gss|].
  destruct (Pos.eq_dec (vkey J) (vkey J')) as [E|NE]; [rewrite E; apply pt_gss | rewrite pt_gso by exact NE; exact (IH J e IN)].
Qed.
Fixpoint vars_free (dom : ptree unit) (x : expr) : bool :=
  match x with
  | ELit _ => true
  | EVar n => match pt_get dom (vkey n) with None => true | Some _ => false end
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if vars_free dom a then vars_free dom b else false
  | EExt _ _ _ a => vars_free dom a
  | EBlob _ _ _ _ => true
  end.
Lemma vars_free_absent : forall s x, vars_free (mk_dom s) x = true -> forallb (fun p => negb (mentions_var (fst p) x)) s = true.
Proof.
  intros s x H. apply forallb_forall. intros [J e] IN. cbn [fst]. pose proof (mk_dom_in s J e IN) as D.
  induction x as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sg k i n]; cbn [vars_free mentions_var] in *;
    try reflexivity;
    try (destruct (vars_free (mk_dom s) a); [|discriminate]; specialize (IHa eq_refl); specialize (IHb H);
         destruct (mentions_var J a); [discriminate|exact IHb]).
  - destruct (Nat.eqb_spec J n) as [->|NE]; [rewrite D in H; discriminate | reflexivity].
  - exact (IHa H).
Qed.
Definition stableD (dom : ptree unit) (x : expr) : bool := if vars_free dom x then expr_eqb (rebuild x) x else false.
Lemma stableD_stable : forall s x, stableD (mk_dom s) x = true -> stable s x = true.
Proof. intros s x H. unfold stableD in H. unfold stable. destruct (vars_free (mk_dom s) x) eqn:V; [|discriminate]. rewrite (vars_free_absent s x V). exact H. Qed.
Definition bcache : Type := option (expr * bool).
Definition bflag (dom : ptree unit) (b : expr) (c : bcache) : bool * bcache :=
  match c with
  | Some (b0, f) => if expr_eqb b b0 then (f, c) else let f' := stableD dom b in (f', Some (b, f'))
  | None => let f' := stableD dom b in (f', Some (b, f'))
  end.
Definition bc_ok (dom : ptree unit) (c : bcache) : Prop := forall b0 f, c = Some (b0, f) -> f = stableD dom b0.
Lemma bflag_spec : forall dom b c, bc_ok dom c -> fst (bflag dom b c) = stableD dom b /\ bc_ok dom (snd (bflag dom b c)).
Proof.
  intros dom b c H. unfold bflag. destruct c as [[b0 f]|].
  - destruct (expr_eqb b b0) eqn:E; cbn [fst snd].
    + apply AX2B.p_expr_eqb_eq in E. subst b0. split; [exact (H b f eq_refl) | exact H].
    + split; [reflexivity|]. intros b1 f1 E1. injection E1 as <- <-. reflexivity.
  - cbn [fst snd]. split; [reflexivity|]. intros b1 f1 E1. injection E1 as <- <-. reflexivity.
Qed.
Definition kstableC (dom : ptree unit) (K : kentry) (c : bcache) : bool * bcache :=
  match K with
  | KWord a _ v => let '(f, c') := bflag dom (a_base a) c in ((if f then stableD dom v else false), c')
  | KZero a n | KWr a n | KUnk a n | KBlob a n _ | KFill a n _ => let '(f, c') := bflag dom (a_base a) c in ((if f then stableD dom n else false), c')
  | KImg _ _ => (true, c)
  | KAlign x _ | KRange x _ _ => (stableD dom x, c)
  | KDisj a1 n1 a2 n2 =>
      let '(f1, c1) := bflag dom (a_base a1) c in let '(f2, c2) := bflag dom (a_base a2) c1 in
      ((if f1 then if stableD dom n1 then if f2 then stableD dom n2 else false else false else false), c2)
  end.
Lemma kstableC_spec : forall s K c, bc_ok (mk_dom s) c ->
  (fst (kstableC (mk_dom s) K c) = true -> kstable s K = true) /\ bc_ok (mk_dom s) (snd (kstableC (mk_dom s) K c)).
Proof.
  intros s K c H. set (dom := mk_dom s) in *.
  assert (B : forall a c0, bc_ok dom c0 -> (fst (bflag dom (a_base a) c0) = true -> astable s a = true) /\ bc_ok dom (snd (bflag dom (a_base a) c0))).
  { intros a c0 H0. destruct (bflag_spec dom (a_base a) c0 H0) as [E1 E2]. split; [|exact E2]. rewrite E1. apply stableD_stable. }
  destruct K as [a w v|a n|a n k|lo hi|x mm|x lo hi|a n|a1 n1 a2 n2|a n cc|a n]; cbn [kstableC kstable];
    try (split; [intros _; reflexivity | exact H]);
    try (split; [apply stableD_stable | exact H]);
    try (destruct (B a c H) as [E1 E2]; destruct (bflag dom (a_base a) c) as [f c']; cbn [fst snd] in *; split; [|exact E2];
         destruct f; [|discriminate]; rewrite (E1 eq_refl); apply stableD_stable).
  destruct (B a1 c H) as [E1 E2]. destruct (bflag dom (a_base a1) c) as [f1 c1]. cbn [fst snd] in *.
  destruct (B a2 c1 E2) as [E3 E4]. destruct (bflag dom (a_base a2) c1) as [f2 c2]. cbn [fst snd] in *. split; [|exact E4].
  destruct f1; [|discriminate]. rewrite (E1 eq_refl). destruct (stableD dom n1) eqn:S1; [|discriminate]. rewrite (stableD_stable s n1 S1).
  destruct f2; [|discriminate]. rewrite (E3 eq_refl). apply stableD_stable.
Qed.
Fixpoint kn_skip (s : list (nat * expr)) (dom : ptree unit) (k : list kentry) (c : bcache) : list kentry :=
  match k with
  | [] => []
  | K :: r => let '(ok, c') := kstableC dom K c in (if ok then K else ksubst_seq s K) :: kn_skip s dom r c'
  end.
Lemma kn_skip_eq : forall s k c, bc_ok (mk_dom s) c -> kn_skip s (mk_dom s) k c = map (ksubst_seq s) k.
Proof.
  intros s k. induction k as [|K r IH]; intros c H; [reflexivity|]. cbn [kn_skip map].
  destruct (kstableC_spec s K c H) as [E1 E2]. destruct (kstableC (mk_dom s) K c) as [ok c']. cbn [fst snd] in *.
  rewrite (IH c' E2). f_equal. destruct ok; [|reflexivity]. symmetry. apply kstable_seq. apply E1. reflexivity.
Qed.
Definition inst_m (inv : acs) (J : nat) (e : expr) : acs :=
  ACS (mk_ss (pc inv) (map (esubst J e) (s_regs (a_ss inv))) (knsubM J e (kn inv) []) (nxt inv))
      (map (msubst J e) (a_maps inv)) (a_totsz inv) (a_ylo inv) (a_eager inv)
      (map (psubst J e) (a_vis inv)) (map (psubst J e) (a_ghost inv)) (a_abytes inv)
      (esubst J e (a_brk inv)) (fsubst J e (a_fd inv)) (a_tidset inv).
Lemma inst_m_eq : forall inv J e, inst_m inv J e = inst inv J e.
Proof. intros. unfold inst_m, inst. rewrite knsubM_eq by (intros k v []). reflexivity. Qed.
Fixpoint inst_list_m (ch : acs) (s : list (nat * expr)) : acs :=
  match s with
  | [] => ch
  | (J, e) :: r => inst_m (inst_list_m ch r) J e
  end.
Lemma inst_list_m_eq : forall ch s, inst_list_m ch s = inst_list ch s.
Proof. intros ch s. induction s as [|[J e] r IH]; [reflexivity|]. cbn [inst_list_m inst_list]. rewrite IH. apply inst_m_eq. Qed.

(* [comment removed for export] *)
Lemma inst_set_kn : forall X k J e, inst (set_kn X k) J e = set_kn (inst X J e) (map (ksubst J e) k).
Proof. intros. reflexivity. Qed.
Lemma inst_list_split : forall ch p r,
  inst_list ch (p :: r) = set_kn (inst_list (set_kn ch []) (p :: r)) (map (ksubst_seq (p :: r)) (kn ch)).
Proof.
  intros ch p r. revert p. induction r as [|q r IH]; intros [J e].
  - cbn [inst_list ksubst_seq fold_right fst snd]. reflexivity.
  - change (inst_list ch ((J, e) :: q :: r)) with (inst (inst_list ch (q :: r)) J e). rewrite (IH q), inst_set_kn.
    change (inst_list (set_kn ch []) ((J, e) :: q :: r)) with (inst (inst_list (set_kn ch []) (q :: r)) J e).
    rewrite map_map. reflexivity.
Qed.
Definition inst_list_s (ch : acs) (s : list (nat * expr)) : acs :=
  match s with
  | [] => ch
  | _ => set_kn (inst_list_m (set_kn ch []) s) (kn_skip s (mk_dom s) (kn ch) None)
  end.
Lemma inst_list_s_eq : forall ch s, inst_list_s ch s = inst_list ch s.
Proof.
  intros ch [|p r]; [reflexivity|]. unfold inst_list_s. rewrite inst_list_m_eq, kn_skip_eq by (intros b0 f E; discriminate).
  symmetry. apply inst_list_split.
Qed.

End CXFI.
