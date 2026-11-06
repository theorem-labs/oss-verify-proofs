(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S.

Definition is_kdisj_for (b1 : expr) (K : kentry) : bool :=
  match K with KDisj c1 _ c2 _ => (expr_eqb b1 (a_base c1) || expr_eqb b1 (a_base c2))%bool | _ => false end.

Lemma kdisj_filter : forall kn b1 k1 n1 b2 k2 n2,
  kdisj_apart (List.filter (is_kdisj_for b1) kn) b1 k1 n1 b2 k2 n2 = kdisj_apart kn b1 k1 n1 b2 k2 n2.
Proof.
  induction kn as [|K kn IH]; intros b1 k1 n1 b2 k2 n2; [reflexivity|].
  cbn [List.filter]. destruct K; cbn [is_kdisj_for]; try (cbn [kdisj_apart]; apply IH).
  destruct (expr_eqb b1 (a_base a1) || expr_eqb b1 (a_base a2))%bool eqn:E.
  - cbn [kdisj_apart]. rewrite IH. reflexivity.
  - apply orb_false_elim in E. destruct E as [E1 E2].
    cbn [kdisj_apart]. unfold sub_itv at 1 3. rewrite E1, E2. cbn [andb orb]. apply IH.
Qed.

(* [comment removed for export] *)
Fixpoint assoc_e (b : expr) (l : list (expr * option (Z * Z))) : option (option (Z * Z)) :=
  match l with [] => None | (b', r) :: t => if expr_eqb b b' then Some r else assoc_e b t end.
Definition kbase (K : kentry) : option expr :=
  match K with
  | KZero (SA kb _) _ => Some kb | KWord (SA kb _) _ _ => Some kb | KBlob (SA kb _) _ _ => Some kb | KImg _ _ => Some (ELit 0)
  | _ => None
  end.
Fixpoint mk_brs (allkn kn : list kentry) (acc : list (expr * option (Z * Z))) : list (expr * option (Z * Z)) :=
  match kn with
  | [] => acc
  | K :: t => match kbase K with
              | Some b => match assoc_e b acc with
                          | Some _ => mk_brs allkn t acc
                          | None => mk_brs allkn t ((b, base_range allkn b) :: acc)
                          end
              | None => mk_brs allkn t acc
              end
  end.
Definition brs_ok (allkn : list kentry) (brs : list (expr * option (Z * Z))) : Prop :=
  forall b r, assoc_e b brs = Some r -> r = base_range allkn b.
Lemma brs_ok_nil allkn : brs_ok allkn [].
Proof. intros b r H. discriminate H. Qed.
Lemma brs_ok_cons allkn b brs : brs_ok allkn brs -> brs_ok allkn ((b, base_range allkn b) :: brs).
Proof.
  intros H b' r E. cbn [assoc_e] in E. destruct (expr_eqb b' b) eqn:Eb.
  - injection E as <-. rewrite (expr_eqb_eq _ _ Eb). reflexivity.
  - exact (H b' r E).
Qed.
Lemma mk_brs_ok allkn : forall kn acc, brs_ok allkn acc -> brs_ok allkn (mk_brs allkn kn acc).
Proof.
  induction kn as [|K t IH]; intros acc H; [exact H|].
  cbn [mk_brs]. destruct (kbase K) as [b|]; [|apply IH; exact H].
  destruct (assoc_e b acc); [apply IH; exact H|apply IH, brs_ok_cons, H].
Qed.

Definition ranges_apartC (r1 : option (Z * Z)) (kd : list kentry) (brs : list (expr * option (Z * Z))) (kn : list kentry)
           (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  (match r1, (match assoc_e b2 brs with Some r => r | None => base_range kn b2 end) with
   | Some (lo1, hi1), Some (lo2, hi2) =>
       (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
   | _, _ => false
   end) || kdisj_apart kd b1 k1 n1 b2 k2 n2.

Lemma ranges_apartC_eq kn brs b1 k1 n1 b2 k2 n2 : brs_ok kn brs ->
  ranges_apartC (base_range kn b1) (List.filter (is_kdisj_for b1) kn) brs kn b1 k1 n1 b2 k2 n2
  = ranges_apart kn b1 k1 n1 b2 k2 n2.
Proof.
  intros H. unfold ranges_apartC, ranges_apart. rewrite kdisj_filter.
  destruct (assoc_e b2 brs) as [r|] eqn:E; [rewrite (H _ _ E)|]; reflexivity.
Qed.

Definition prune1C (r1 : option (Z * Z)) (kd : list kentry) (brs : list (expr * option (Z * Z)))
           (allkn : list kentry) (wa : saddr) (w : nat) (K : kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := match kl with
                 | ELit l => ranges_apartC r1 kd brs allkn (a_base wa) k (Z.of_nat w) (a_base ka) (a_off ka) (l mod two64)%Z
                 | _ => false
                 end in
    if apart then ([K], [], hints) else
    match hints with
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)
    | false :: hs => ([], [], hs)
    | [] => ([], [], [])
    end in
  match K with
  | KAlign _ _ => ([K], [], hints)
  | KRange _ _ _ => ([K], [], hints)
  | KWr _ _ => ([K], [], hints)
  | KDisj _ _ _ _ => ([K], [], hints)
  | KImg lo hi =>
      match a_base wa with
      | ELit 0 =>
          let r1' := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
          let lo2 := Z.max lo (k + Z.of_nat w) in
          let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
          (r1' ++ r2, [], hints)
      | _ => if Z.ltb (hi - lo) two64 then diffbase (SA (ELit 0) lo) (ELit (hi - lo))
             else ([], [], hints)
      end
  | KZero (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then
        match len with
        | ELit l0 =>
            let l := (l0 mod two64)%Z in
            let hi1 := Z.min k (kk + l) in
            let r1' := if Z.ltb kk hi1 then [KZero (SA kb kk) (ELit (hi1 - kk))] else [] in
            let lo2 := Z.max kk (k + Z.of_nat w) in
            let r2 := if Z.ltb lo2 (kk + l) then [KZero (SA kb lo2) (ELit (kk + l - lo2))] else [] in
            (r1' ++ r2, [], hints)
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
        end
      else diffbase (SA kb kk) len
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then
        (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
         then ([K], [], hints) else ([], [], hints))
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then
        match len with
        | ELit l0 =>
            let l := (l0 mod two64)%Z in
            (if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool
             then ([K], [], hints) else ([], [], hints))
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
        end
      else diffbase (SA kb kk) len
  end.

Lemma prune1C_eq allkn brs wa w K hints : brs_ok allkn brs ->
  prune1C (base_range allkn (a_base wa)) (List.filter (is_kdisj_for (a_base wa)) allkn) brs allkn wa w K hints
  = prune1 allkn wa w K hints.
Proof.
  intros H. unfold prune1C, prune1. change two64 with (2 ^ 64).
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[kb kk] n|a1 n1 a2 n2]; try reflexivity.
  - (* [comment removed for export] *) destruct (expr_eqb kb (a_base wa)); [reflexivity|]. unfold elen. rewrite (ranges_apartC_eq _ _ _ _ _ _ _ _ H). reflexivity.
  - (* [comment removed for export] *) destruct (expr_eqb kb (a_base wa)); [reflexivity|]. destruct len; try reflexivity. rewrite (ranges_apartC_eq _ _ _ _ _ _ _ _ H). reflexivity.
  - (* [comment removed for export] *) destruct (expr_eqb kb (a_base wa)); [reflexivity|]. destruct len; try reflexivity. rewrite (ranges_apartC_eq _ _ _ _ _ _ _ _ H). reflexivity.
  - (* [comment removed for export] *) destruct (a_base wa) as [z| | | | | | |] eqn:Eb; try (destruct (Z.ltb (hi - lo) (2 ^ 64)); [|reflexivity]; rewrite <- ?Eb; rewrite (ranges_apartC_eq _ _ _ _ _ _ _ _ H); reflexivity).
Qed.

Fixpoint pruneC (r1 : option (Z * Z)) (kd : list kentry) (brs : list (expr * option (Z * Z)))
         (allkn : list kentry) (wa : saddr) (w : nat) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(kept, scs1, hs1) := prune1C r1 kd brs allkn wa w K hints in
      let '(r, scs2, hs2) := pruneC r1 kd brs allkn wa w rest hs1 in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.

Lemma pruneC_eq allkn brs wa w : brs_ok allkn brs -> forall kn hints,
  pruneC (base_range allkn (a_base wa)) (List.filter (is_kdisj_for (a_base wa)) allkn) brs allkn wa w kn hints
  = prune allkn wa w kn hints.
Proof.
  intros H. induction kn as [|K rest IH]; intros hints; [reflexivity|].
  cbn [pruneC prune]. rewrite (prune1C_eq _ _ _ _ _ _ H).
  destruct (prune1 allkn wa w K hints) as [[kept scs1] hs1]. rewrite IH. reflexivity.
Qed.

Fixpoint carryC (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let '(kn1, scs1, hs1) := carryC older kn hints in
      let '(kn2, scs2, hs2) := pruneC (base_range kn1 (a_base a)) (List.filter (is_kdisj_for (a_base a)) kn1)
                                       (mk_brs kn1 kn1 []) kn1 a w kn1 hs1 in
      (KWord a w v :: kn2, scs1 ++ scs2, hs2)
  end.

Theorem carryC_eq : forall log kn hints, carryC log kn hints = carry log kn hints.
Proof.
  induction log as [|[a w v] older IH]; intros kn hints; [reflexivity|].
  cbn [carryC carry]. rewrite IH. destruct (carry older kn hints) as [[kn1 scs1] hs1].
  rewrite (pruneC_eq kn1 _ a w (mk_brs_ok kn1 kn1 [] (brs_ok_nil kn1))). reflexivity.
Qed.
