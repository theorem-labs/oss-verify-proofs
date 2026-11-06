(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutOpsF.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CX.

Definition rel_range (kn : list kentry) (c : Z) (ts : list (Z * expr)) : option (Z * Z) :=
  match sum_facts kn kn with
  | [] => None
  | fs => match sum_subst fs ts 0 0 false with
          | (ts', (lo0, hi0), true) =>
              match lin_range (erange kn) c ts' with Some (lo, hi) => Some (lo + lo0, hi + hi0) | None => None end
          | _ => None
          end
  end.
Lemma rel_range_sound : forall segs E M kn c ts lo hi,
  know_ok segs E M kn -> rel_range kn c ts = Some (lo, hi) -> lo <= c + tden E ts <= hi.
Proof.
  intros segs E M kn c ts lo hi Hkn H. unfold rel_range in H.
  pose proof (sum_facts_sound segs E M kn kn Hkn Hkn) as Hfs.
  destruct (sum_facts kn kn) as [|f fs] eqn:Hsf; [discriminate|].
  destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] hit] eqn:Hss.
  destruct hit; [|discriminate].
  pose proof (sum_subst_sound E _ _ _ _ _ _ _ _ _ Hfs Hss) as [A B].
  destruct (lin_range (erange kn) c ts') as [[l h]|] eqn:Hlr; [|discriminate]. injection H as <- <-.
  pose proof (lin_range_sound E (erange kn) (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha) _ _ _ _ Hlr) as Hb.
  lia.
Qed.

(* [comment removed for export] *)
Fixpoint part_quot (fts ts : list (Z * expr)) (acc : option Z) : option Z :=
  match fts with
  | [] => acc
  | (k, a) :: r =>
      if Z.eqb k 0 then None else
      let q := Z.quot (coef_of a ts) k in
      if Z.eqb q 0 then None else
      match acc with
      | None => part_quot r ts (Some q)
      | Some q0 => if (Z.ltb 0 q0 && Z.ltb 0 q)%bool then part_quot r ts (Some (Z.min q0 q))
                   else if (Z.ltb q0 0 && Z.ltb q 0)%bool then part_quot r ts (Some (Z.max q0 q)) else None
      end
  end.
Fixpoint sum_subst2 (fs : list sfact) (ts : list (Z * expr)) (lo hi : Z) (hit : bool) : list (Z * expr) * (Z * Z) * bool :=
  match fs with
  | [] => (ts, (lo, hi), hit)
  | (fts, (flo, fhi)) :: r =>
      match part_quot fts ts None with
      | Some q =>
          let ts' := sub_fact q fts ts in
          if Z.leb 0 q then sum_subst2 r ts' (lo + q * flo) (hi + q * fhi) true
          else sum_subst2 r ts' (lo + q * fhi) (hi + q * flo) true
      | None => sum_subst2 r ts lo hi hit
      end
  end.
Lemma sum_subst2_sound : forall E fs ts lo hi hit ts' lo' hi' hit',
  Forall (sfact_ok E) fs -> sum_subst2 fs ts lo hi hit = (ts', (lo', hi'), hit') ->
  tden E ts' + lo' <= tden E ts + lo /\ tden E ts + hi <= tden E ts' + hi'.
Proof.
  intros E fs. induction fs as [|[fts [flo fhi]] r IH]; intros ts lo hi hit ts' lo' hi' hit' Hfs H; cbn [sum_subst2] in H.
  - injection H as <- <- <- <-. lia.
  - apply Forall_cons_iff in Hfs as [Hf Hr]. unfold sfact_ok in Hf. cbn [fst snd] in Hf.
    destruct (part_quot fts ts None) as [q|]; [|exact (IH _ _ _ _ _ _ _ _ Hr H)].
    pose proof (sub_fact_sound E q fts ts) as Hs.
    destruct (Z.leb 0 q) eqn:Hq.
    + apply Z.leb_le in Hq. pose proof (IH _ _ _ _ _ _ _ _ Hr H) as [A B]. rewrite Hs in A, B. nia.
    + apply Z.leb_gt in Hq. pose proof (IH _ _ _ _ _ _ _ _ Hr H) as [A B]. rewrite Hs in A, B. nia.
Qed.
Definition rel_range2 (kn : list kentry) (c : Z) (ts : list (Z * expr)) : option (Z * Z) :=
  match sum_facts kn kn with
  | [] => None
  | fs => match sum_subst2 fs ts 0 0 false with
          | (ts', (lo0, hi0), true) =>
              match lin_range (erange kn) c ts' with Some (lo, hi) => Some (lo + lo0, hi + hi0) | None => None end
          | _ => None
          end
  end.
Lemma rel_range2_sound : forall segs E M kn c ts lo hi,
  know_ok segs E M kn -> rel_range2 kn c ts = Some (lo, hi) -> lo <= c + tden E ts <= hi.
Proof.
  intros segs E M kn c ts lo hi Hkn H. unfold rel_range2 in H.
  pose proof (sum_facts_sound segs E M kn kn Hkn Hkn) as Hfs.
  destruct (sum_facts kn kn) as [|f fs] eqn:Hsf; [discriminate|].
  destruct (sum_subst2 (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] hit] eqn:Hss.
  destruct hit; [|discriminate].
  pose proof (sum_subst2_sound E _ _ _ _ _ _ _ _ _ Hfs Hss) as [A B].
  destruct (lin_range (erange kn) c ts') as [[l h]|] eqn:Hlr; [|discriminate]. injection H as <- <-.
  pose proof (lin_range_sound E (erange kn) (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha) _ _ _ _ Hlr) as Hb.
  lia.
Qed.

(* [comment removed for export] *)
Definition meet (x y : option (Z * Z)) : option (Z * Z) :=
  match x, y with
  | Some (a, b), Some (a', b') => Some (Z.max a a', Z.min b b')
  | Some r, None | None, Some r => Some r
  | None, None => None
  end.
Lemma meet_sound : forall x y v, (forall a b, x = Some (a, b) -> a <= v <= b) -> (forall a b, y = Some (a, b) -> a <= v <= b) ->
  forall a b, meet x y = Some (a, b) -> a <= v <= b.
Proof.
  intros x y v Hx Hy a b H. destruct x as [[a1 b1]|]; destruct y as [[a2 b2]|]; cbn [meet] in H; try discriminate; injection H as <- <-;
    try (specialize (Hx _ _ eq_refl)); try (specialize (Hy _ _ eq_refl)); lia.
Qed.
(* [comment removed for export] *)
Definition one_fact (kn : list kentry) (c : Z) (ts : list (Z * expr)) (f : sfact) (q : Z) : option (Z * Z) :=
  let '(fts, (flo, fhi)) := f in
  match lin_range (erange kn) c (sub_fact q fts ts) with
  | Some (lo, hi) => Some (if Z.leb 0 q then (lo + q * flo, hi + q * fhi) else (lo + q * fhi, hi + q * flo))
  | None => None
  end.
Lemma one_fact_sound : forall segs E M kn c ts f q lo hi, know_ok segs E M kn -> sfact_ok E f ->
  one_fact kn c ts f q = Some (lo, hi) -> lo <= c + tden E ts <= hi.
Proof.
  intros segs E M kn c ts [fts [flo fhi]] q lo hi Hkn Hf H. unfold one_fact in H. unfold sfact_ok in Hf. cbn [fst snd] in Hf.
  destruct (lin_range (erange kn) c (sub_fact q fts ts)) as [[l h]|] eqn:Hlr; [|discriminate].
  pose proof (lin_range_sound E (erange kn) (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha) _ _ _ _ Hlr) as Hb.
  rewrite (sub_fact_sound E q fts ts) in Hb.
  destruct (Z.leb 0 q) eqn:Hq; [apply Z.leb_le in Hq | apply Z.leb_gt in Hq]; injection H as <- <-; nia.
Qed.
(* [comment removed for export] *)
Definition fact_qs (fts ts : list (Z * expr)) : list Z :=
  flat_map (fun t : Z * expr => let kt := coef_of (snd t) ts in
                                if (Z.eqb kt 0 || Z.eqb (fst t) 0)%bool then [] else if Z.eqb (kt mod fst t) 0 then [kt / fst t] else []) fts.
Fixpoint meet_all (l : list (option (Z * Z))) : option (Z * Z) := match l with [] => None | x :: r => meet x (meet_all r) end.
Lemma meet_all_sound : forall l v, (forall x a b, In x l -> x = Some (a, b) -> a <= v <= b) -> forall a b, meet_all l = Some (a, b) -> a <= v <= b.
Proof.
  induction l as [|x r IH]; intros v H a b Hm; [discriminate|]. cbn [meet_all] in Hm. revert Hm. apply meet_sound.
  - intros a0 b0 Hx. exact (H x a0 b0 (or_introl eq_refl) Hx).
  - apply IH. intros y a0 b0 Hy. exact (H y a0 b0 (or_intror Hy)).
Qed.
Definition each_range (fs : list sfact) (kn : list kentry) (c : Z) (ts : list (Z * expr)) : option (Z * Z) :=
  meet_all (flat_map (fun f : sfact => map (one_fact kn c ts f) (fact_qs (fst f) ts)) fs).
Lemma each_range_sound : forall segs E M kn, know_ok segs E M kn -> forall fs c ts lo hi, Forall (sfact_ok E) fs ->
  each_range fs kn c ts = Some (lo, hi) -> lo <= c + tden E ts <= hi.
Proof.
  intros segs E M kn Hkn fs c ts lo hi Hfs. unfold each_range. apply meet_all_sound.
  intros x a b Hx Hxe. apply in_flat_map in Hx as (f & Hf & Hx). apply in_map_iff in Hx as (q & <- & _).
  exact (one_fact_sound segs E M kn c ts f q a b Hkn (proj1 (Forall_forall _ _) Hfs f Hf) Hxe).
Qed.

(* [comment removed for export] *)
Definition form_range (kn : list kentry) (c : Z) (ts : list (Z * expr)) : option (Z * Z) :=
  let one (c0 : Z) (t0 : list (Z * expr)) := meet (lin_range (erange kn) c0 t0) (meet (rel_range kn c0 t0) (meet (rel_range2 kn c0 t0) (each_range (sum_facts kn kn) kn c0 t0))) in
  if has_srl ts then let '(c2, ts2) := srl_expand kn ts in meet (one c ts) (one (c + c2) ts2) else one c ts.
Lemma form_range_sound : forall segs E M kn c ts lo hi,
  know_ok segs E M kn -> form_range kn c ts = Some (lo, hi) -> lo <= c + tden E ts <= hi.
Proof.
  intros segs E M kn c ts lo hi Hkn H. unfold form_range in H.
  assert (ONE : forall c0 t0 a b, meet (lin_range (erange kn) c0 t0) (meet (rel_range kn c0 t0) (meet (rel_range2 kn c0 t0) (each_range (sum_facts kn kn) kn c0 t0))) = Some (a, b) ->
                a <= c0 + tden E t0 <= b).
  { intros c0 t0. apply meet_sound.
    - intros a b Ha. exact (lin_range_sound E (erange kn) (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha) _ _ _ _ Ha).
    - apply meet_sound; [intros a b Ha; exact (rel_range_sound segs E M kn c0 t0 _ _ Hkn Ha)|].
      apply meet_sound; intros a b Ha; [exact (rel_range2_sound segs E M kn c0 t0 _ _ Hkn Ha)|].
      exact (each_range_sound segs E M kn Hkn _ c0 t0 a b (sum_facts_sound segs E M kn kn Hkn Hkn) Ha). }
  destruct (has_srl ts); [|exact (ONE _ _ _ _ H)].
  destruct (srl_expand kn ts) as [c2 ts2] eqn:Hx. pose proof (srl_expand_sound segs E M kn ts c2 ts2 Hkn Hx) as Hs.
  revert H. apply meet_sound; intros a b Ha; [exact (ONE _ _ _ _ Ha) | pose proof (ONE _ _ _ _ Ha); lia].
Qed.

Definition brange2 (kn : list kentry) (e : expr) : option (Z * Z) :=
  match form_range kn (fst (lin_of e)) (snd (lin_of e)) with
  | Some (lo, hi) => if (Z.leb 0 lo && Z.ltb hi two64)%bool then Some (lo, hi)
                     else if (Z.leb (- two64) lo && Z.ltb hi 0)%bool then Some (lo + two64, hi + two64)   (* [comment removed for export] *)
                     else None
  | None => None
  end.
Lemma brange2_sound : forall segs E M kn e lo hi,
  know_ok segs E M kn -> brange2 kn e = Some (lo, hi) -> lo <= bv_unsigned (edenot E e) <= hi.
Proof.
  intros segs E M kn e lo hi Hkn H. unfold brange2 in H.
  destruct (form_range kn (fst (lin_of e)) (snd (lin_of e))) as [[a b]|] eqn:Hf; [|discriminate].
  pose proof (form_range_sound segs E M kn _ _ a b Hkn Hf) as HL.
  pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
  pose proof (u64_range (edenot E e)) as Hu.
  destruct (Z.leb 0 a && Z.ltb b two64)%bool eqn:Hc.
  - injection H as <- <-.
    apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2. nia.
  - destruct (Z.leb (- two64) a && Z.ltb b 0)%bool eqn:Hc2; [|discriminate]. injection H as <- <-.
    apply andb_prop in Hc2 as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in *. nia.
Qed.

(* [comment removed for export] *)
Definition all_even (ts : list (Z * expr)) : bool := forallb (fun t : Z * expr => Z.even (fst t)) ts.
Definition bit0_lin (e : expr) : option bool := if all_even (snd (lin_of e)) then Some (Z.odd (fst (lin_of e))) else None.
Fixpoint bit0 (e : expr) : option bool :=
  match e with
  | EExt false O (S _) a => bit0 a
  | _ => bit0_lin e
  end.
Lemma tden_even : forall E ts, all_even ts = true -> (tden E ts) mod 2 = 0.
Proof.
  intros E ts. induction ts as [|[k a] r IH]; intros H; cbn [tden]; [reflexivity|].
  cbn [all_even forallb fst] in H. apply andb_prop in H as [Hk Hr]. specialize (IH Hr).
  apply Z.even_spec in Hk. destruct Hk as [q ->].
  rewrite Z.add_mod by lia. rewrite IH. rewrite <- Z.mul_assoc, Z.mul_comm, Z_mod_mult. reflexivity.
Qed.
Lemma bit0_lin_sound : forall E e b, all_even (snd (lin_of e)) = true -> Z.odd (fst (lin_of e)) = b ->
  bv_unsigned (edenot E e) mod 2 = if b then 1 else 0.
Proof.
  intros E e b He Hb. pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
  pose proof (tden_even E _ He) as Ht.
  assert (Hu : bv_unsigned (edenot E e) = fst (lin_of e) + tden E (snd (lin_of e)) - q * 2 ^ 64) by lia.
  rewrite Hu. replace (q * 2 ^ 64) with (2 * (q * 2 ^ 63)) by (change (2 ^ 64) with (2 * 2 ^ 63); ring).
  rewrite Zminus_mod, Z.mul_comm, Z_mod_mult, Z.sub_0_r, Z.mod_mod by lia.
  rewrite Z.add_mod by lia. rewrite Ht, Z.add_0_r, Z.mod_mod by lia.
  rewrite <- Hb. rewrite Zmod_odd. reflexivity.
Qed.
Lemma bit0_sound : forall E e b, bit0 e = Some b -> bv_unsigned (edenot E e) mod 2 = if b then 1 else 0.
Proof.
  intros E e. 
  assert (LIN : forall e0 b, bit0_lin e0 = Some b -> bv_unsigned (edenot E e0) mod 2 = if b then 1 else 0).
  { intros e0 b H. unfold bit0_lin in H. destruct (all_even (snd (lin_of e0))) eqn:Hev; [|discriminate]. injection H as H.
    exact (bit0_lin_sound E e0 b Hev H). }
  induction e as [z|n|op a IHa b0 IHb|op a IHa b0 IHb|op a IHa b0 IHb|op a IHa b0 IHb|sx lo n a IHa|sx k i n]; intros b H;
    try (exact (LIN _ b H)).
  cbn [bit0] in H. destruct sx; [exact (LIN _ b H)|]. destruct lo as [|lo]; [|exact (LIN _ b H)]. destruct n as [|n]; [exact (LIN _ b H)|].
  specialize (IHa b H). cbn [edenot]. destruct (u_ext_zx 0 (S n) (edenot E a)) as (Hx & _ & _). rewrite Hx.
  change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  rewrite <- IHa. apply Z.mod_mod_divide.
  exists (2 ^ (8 * Z.of_nat (S n) - 1)).
  replace (8 * Z.of_nat (S n)) with (Z.succ (8 * Z.of_nat (S n) - 1)) at 1 by lia.
  rewrite Z.pow_succ_r by lia. ring.
Qed.

(* [comment removed for export] *)
Definition range3 (kn : list kentry) (e : expr) : option (Z * Z) :=
  match e with
  | EAlu ALU_AND x (ELit 1) => match bit0 x with Some b => Some (if b then (1, 1) else (0, 0)) | None => brange2 kn e end
  | _ => brange2 kn e
  end.
Lemma range3_sound : forall segs E M kn e lo hi,
  know_ok segs E M kn -> range3 kn e = Some (lo, hi) -> lo <= bv_unsigned (edenot E e) <= hi.
Proof.
  intros segs E M kn e lo hi Hkn H.
  assert (D : brange2 kn e = Some (lo, hi) -> lo <= bv_unsigned (edenot E e) <= hi) by (apply brange2_sound with (M := M) (segs := segs); exact Hkn).
  destruct e as [z|n|op a b|op a b|op a b|op a b|sx l n a|sx k i n]; try exact (D H).
  destruct op; try exact (D H). destruct b as [z| | | | | | |]; try exact (D H).
  cbn [range3] in H. destruct (Z.eq_dec z 1) as [->|Hz]; [|destruct z as [|[p|p|]|]; try exact (D H); exfalso; apply Hz; reflexivity].
  destruct (bit0 a) as [bb|] eqn:Hb; [|exact (D H)].
  pose proof (bit0_sound E a bb Hb) as Hp. cbn [edenot]. rewrite u_and64.
  replace (bv_unsigned (Z_to_bv 64 1)) with (Z.ones 1) by reflexivity. rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  destruct bb; injection H as <- <-; lia.
Qed.

Definition range2_ok (kn : list kentry) (e : expr) (lo hi : Z) : bool :=
  match range3 kn e with Some (l, h) => (Z.leb lo l && Z.leb h hi)%bool | None => false end.
Definition fact2_ok (kn : list kentry) (K : kentry) : bool :=
  (APC.fact_ok kn K || match K with KRange e lo hi => range2_ok kn e lo hi | _ => false end)%bool.

Lemma fact2_ok_sound : forall segs E M kn K, know_ok segs E M kn -> fact2_ok kn K = true -> kentry_ok segs E M K.
Proof.
  intros segs E M kn K Hkn H. unfold fact2_ok in H. apply orb_prop in H as [H|H].
  - exact (APS.fact_ok_sound segs E M kn K Hkn H).
  - destruct K as [| | | | |e lo hi| | | |]; try discriminate. unfold range2_ok in H.
    destruct (range3 kn e) as [[l h]|] eqn:Hb; [|discriminate]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. pose proof (range3_sound segs E M kn e l h Hkn Hb). cbn [kentry_ok]. lia.
Qed.

(* [comment removed for export] *)
Definition nowrap_form (kn : list kentry) (e : expr) : bool :=
  match form_range kn (fst (lin_of e)) (snd (lin_of e)) with Some (a, b) => (Z.leb 0 a && Z.ltb b two64)%bool | None => false end.
Lemma nowrap_form_sound : forall segs E M kn e, know_ok segs E M kn -> nowrap_form kn e = true -> bv_unsigned (edenot E e) = lden E (lin_of e).
Proof.
  intros segs E M kn e Hkn H. unfold nowrap_form in H.
  destruct (form_range kn (fst (lin_of e)) (snd (lin_of e))) as [[a b]|] eqn:Hf; [|discriminate].
  pose proof (form_range_sound segs E M kn _ _ a b Hkn Hf) as HL. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
  pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in *. pose proof (u64_range (edenot E e)) as Hu. nia.
Qed.
Definition ladd_e (ts2 ts1 : list (Z * expr)) : list (Z * expr) := fold_right (fun t acc => lins_e (fst t) (snd t) acc) ts2 ts1.
Lemma ladd_e_sound : forall E ts2 ts1, tden E (ladd_e ts2 ts1) = tden E ts2 + tden E ts1.
Proof.
  intros E ts2 ts1. unfold ladd_e. induction ts1 as [|[k a] rest IH]; cbn [fold_right tden]; [lia|].
  rewrite lins_e_sound. cbn [fst snd]. rewrite IH. lia.
Qed.
Definition form_ge0 (kn : list kentry) (c : Z) (ts : list (Z * expr)) : bool :=
  match form_range kn c ts with Some (lo, _) => Z.leb 0 lo | None => false end.
Definition xinside2 (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  let l1 := lin_of b1 in let l2 := lin_of b2 in let m1 := lin_of n1 in let m2 := lin_of n2 in
  (nowrap_form kn b1 && nowrap_form kn b2 && nowrap_form kn n1 && nowrap_form kn n2
   && form_ge0 kn (fst l1 + k1 - (fst l2 + k2)) (lsub_e (snd l1) (snd l2))
   && form_ge0 kn (fst l2 + k2 + fst m2 - (fst l1 + k1 + fst m1)) (lsub_e (ladd_e (snd l2) (snd m2)) (ladd_e (snd l1) (snd m1))))%bool.

Lemma form_ge0_sound : forall segs E M kn c ts, know_ok segs E M kn -> form_ge0 kn c ts = true -> 0 <= c + tden E ts.
Proof.
  intros segs E M kn c ts Hkn H. unfold form_ge0 in H. destruct (form_range kn c ts) as [[lo hi]|] eqn:Hf; [|discriminate].
  apply Z.leb_le in H. pose proof (form_range_sound segs E M kn c ts lo hi Hkn Hf). lia.
Qed.
Lemma xinside2_sound : forall segs E M kn b1 k1 n1 b2 k2 n2,
  know_ok segs E M kn -> xinside2 kn b1 k1 n1 b2 k2 n2 = true ->
  estart E (SA b2 k2) <= estart E (SA b1 k1) /\ estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2) + elenZ E n2.
Proof.
  intros segs E M kn b1 k1 n1 b2 k2 n2 Hkn H. unfold xinside2 in H. repeat (apply andb_prop in H as [H ?X]).
  pose proof (nowrap_form_sound segs E M kn b1 Hkn H) as U1. pose proof (nowrap_form_sound segs E M kn b2 Hkn X3) as U2.
  pose proof (nowrap_form_sound segs E M kn n1 Hkn X2) as U3. pose proof (nowrap_form_sound segs E M kn n2 Hkn X1) as U4.
  pose proof (form_ge0_sound segs E M kn _ _ Hkn X0) as G1. pose proof (form_ge0_sound segs E M kn _ _ Hkn X) as G2.
  rewrite lsub_e_sound in G1. rewrite lsub_e_sound, !ladd_e_sound in G2.
  unfold estart, elenZ. cbn [a_base a_off]. rewrite U1, U2, U3, U4. unfold lden. lia.
Qed.

(* [comment removed for export] *)
Fixpoint comb (F : list sfact) (cert : list (nat * Z)) (ts : list (Z * expr)) (lo hi : Z) : list (Z * expr) * (Z * Z) :=
  match cert with
  | [] => (ts, (lo, hi))
  | (i, q) :: r =>
      match nth_error F i with
      | Some (fts, (flo, fhi)) =>
          if Z.leb 0 q then comb F r (sub_fact (- q) fts ts) (lo + q * flo) (hi + q * fhi)
          else comb F r (sub_fact (- q) fts ts) (lo + q * fhi) (hi + q * flo)
      | None => comb F r ts lo hi
      end
  end.
Definition contra_chk (kn : list kentry) (cert : list (nat * Z)) : bool :=
  let '(ts, (lo, hi)) := comb (sum_facts kn kn) cert [] 0 0 in
  match lin_range (erange kn) 0 ts with
  | Some (a, b) => (Z.ltb b lo || Z.ltb hi a)%bool
  | None => false
  end.
Lemma comb_sound : forall E F, Forall (sfact_ok E) F -> forall cert ts lo hi ts' lo' hi',
  lo <= tden E ts <= hi -> comb F cert ts lo hi = (ts', (lo', hi')) -> lo' <= tden E ts' <= hi'.
Proof.
  intros E F HF. induction cert as [|[i q] r IH]; intros ts lo hi ts' lo' hi' Hb H; cbn [comb] in H.
  - injection H as <- <- <-. exact Hb.
  - destruct (nth_error F i) as [[fts [flo fhi]]|] eqn:Hn; [|exact (IH _ _ _ _ _ _ Hb H)].
    pose proof (proj1 (Forall_forall _ _) HF _ (nth_error_In _ _ Hn)) as Hf. unfold sfact_ok in Hf. cbn [fst snd] in Hf.
    pose proof (sub_fact_sound E (- q) fts ts) as Hs.
    destruct (Z.leb 0 q) eqn:Hq; [apply Z.leb_le in Hq | apply Z.leb_gt in Hq]; (eapply IH; [|exact H]); rewrite Hs; nia.
Qed.
Lemma contra_sound : forall segs E M kn cert, know_ok segs E M kn -> contra_chk kn cert = true -> False.
Proof.
  intros segs E M kn cert Hkn H. unfold contra_chk in H.
  destruct (comb (sum_facts kn kn) cert [] 0 0) as [ts [lo hi]] eqn:Hc.
  pose proof (comb_sound E _ (sum_facts_sound segs E M kn kn Hkn Hkn) cert [] 0 0 ts lo hi ltac:(cbn [tden]; lia) Hc) as Hb.
  destruct (lin_range (erange kn) 0 ts) as [[a b]|] eqn:Hlr; [|discriminate].
  pose proof (lin_range_sound E (erange kn) (fun x l h Hx => erange_sound segs E M kn x l h Hkn Hx) _ _ _ _ Hlr) as Hr.
  apply orb_prop in H as [H|H]; apply Z.ltb_lt in H; lia.
Qed.
(* [comment removed for export] *)
Definition cert_range (kn : list kentry) (e : expr) (cert : list (nat * Z)) : option (Z * Z) :=
  let l := lin_of e in
  match form_range kn (fst l) (snd l) with
  | Some (a0, b0) =>
      if (Z.leb 0 a0 && Z.ltb b0 two64)%bool then        (* [comment removed for export] *)
        let '(tsS, (LO, HI)) := comb (sum_facts kn kn) cert [] 0 0 in
        match lin_range (erange kn) (fst l) (lsub_e (snd l) tsS) with
        | Some (a, b) => Some (Z.max a0 (a + LO), Z.min b0 (b + HI))
        | None => None
        end
      else None
  | None => None
  end.
Lemma cert_range_sound : forall segs E M kn e cert A B, know_ok segs E M kn -> cert_range kn e cert = Some (A, B) ->
  A <= bv_unsigned (edenot E e) <= B.
Proof.
  intros segs E M kn e cert A B Hkn H. unfold cert_range in H.
  destruct (form_range kn (fst (lin_of e)) (snd (lin_of e))) as [[a0 b0]|] eqn:Hf; [|discriminate].
  pose proof (form_range_sound segs E M kn _ _ a0 b0 Hkn Hf) as HL.
  destruct (Z.leb 0 a0 && Z.ltb b0 two64)%bool eqn:Hw; [|discriminate].
  apply andb_prop in Hw as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
  destruct (comb (sum_facts kn kn) cert [] 0 0) as [tsS [LO HI]] eqn:Hc.
  pose proof (comb_sound E _ (sum_facts_sound segs E M kn kn Hkn Hkn) cert [] 0 0 tsS LO HI ltac:(cbn [tden]; lia) Hc) as Hb.
  destruct (lin_range (erange kn) (fst (lin_of e)) (lsub_e (snd (lin_of e)) tsS)) as [[a b]|] eqn:Hlr; [|discriminate].
  pose proof (lin_range_sound E (erange kn) (fun x l h Hx => erange_sound segs E M kn x l h Hkn Hx) _ _ _ _ Hlr) as Hr.
  rewrite lsub_e_sound in Hr. injection H as <- <-.
  pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq. pose proof (u64_range (edenot E e)) as Hu.
  assert (q = 0) by nia. subst q. lia.
Qed.
Definition factc_ok (kn : list kentry) (K : kentry) (cert : list (nat * Z)) : bool :=
  match K with
  | KRange e lo hi => match cert_range kn e cert with Some (A, B) => (Z.leb lo A && Z.leb B hi)%bool | None => false end
  | _ => false
  end.
Lemma factc_ok_sound : forall segs E M kn K cert, know_ok segs E M kn -> factc_ok kn K cert = true -> kentry_ok segs E M K.
Proof.
  intros segs E M kn K cert Hkn H. destruct K as [| | | | |e lo hi| | | |]; try discriminate. cbn [factc_ok] in H.
  destruct (cert_range kn e cert) as [[A B]|] eqn:Hc; [|discriminate]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2.
  pose proof (cert_range_sound segs E M kn e cert A B Hkn Hc). cbn [kentry_ok]. lia.
Qed.
(* [comment removed for export] *)
Definition contra_state (ss : sym_state) : sym_state :=
  SSR (s_pc ss) (s_regs ss) (s_log ss) (KRange (ELit 0) 1 0 :: KRange (EVar (s_next ss)) 0 1 :: s_know ss) (S (s_next ss)) (s_resv ss).

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive xop : Type := OFact (K : kentry) | OLtu (a b : expr) (strict : bool) | OForget (r : nat) | OContra (cert : list (nat * Z)) | OFactC (K : kentry) (cert : list (nat * Z)).
Definition has_k (kn : list kentry) (X : kentry) : bool := existsb (APC.kentry_eqb X) kn.
Definition ltu_fact (kn : list kentry) (a b : expr) (strict : bool) : option kentry :=
  if (if strict then has_k kn (KRange (EAlu ALU_SLTU a b) 1 1) else has_k kn (KRange (EAlu ALU_SLTU b a) 0 0)) then
    match range3 kn a, range3 kn b with
    | Some (la, _), Some (_, hb) => Some (KRange (APC.esub b a) (if strict then 1 else 0) (hb - la))
    | _, _ => None
    end
  else None.
Lemma has_k_In : forall kn X, has_k kn X = true -> In X kn.
Proof. intros kn X H. unfold has_k in H. apply existsb_exists in H as (Y & HY & Heq). apply APS.kentry_eqb_eq in Heq. subst Y. exact HY. Qed.
Lemma ltu_fact_sound : forall segs E M kn a b strict K,
  know_ok segs E M kn -> ltu_fact kn a b strict = Some K -> kentry_ok segs E M K.
Proof.
  intros segs E M kn a b strict K Hkn H. unfold ltu_fact in H.
  destruct (if strict then has_k kn (KRange (EAlu ALU_SLTU a b) 1 1) else has_k kn (KRange (EAlu ALU_SLTU b a) 0 0)) eqn:Hh; [|discriminate].
  destruct (range3 kn a) as [[la ha]|] eqn:Ra; [|discriminate]. destruct (range3 kn b) as [[lb hb]|] eqn:Rb; [|discriminate].
  injection H as <-.
  pose proof (range3_sound segs E M kn a la ha Hkn Ra) as Ba. pose proof (range3_sound segs E M kn b lb hb Hkn Rb) as Bb.
  pose proof (u64_range (edenot E a)) as Ua. pose proof (u64_range (edenot E b)) as Ub.
  cbn [kentry_ok]. unfold APC.esub. rewrite mkAlu_denot, u_sub64.
  assert (Hlt : if strict then bv_unsigned (edenot E a) < bv_unsigned (edenot E b) else bv_unsigned (edenot E a) <= bv_unsigned (edenot E b)).
  { destruct strict; apply has_k_In in Hh; pose proof (proj1 (Forall_forall _ _) Hkn _ Hh) as HK; cbn [kentry_ok edenot] in HK;
      rewrite u_sltu64 in HK.
    - destruct (Z.ltb_spec (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b))); lia.
    - destruct (Z.ltb_spec (bv_unsigned (edenot E b)) (bv_unsigned (edenot E a))); lia. }
  rewrite Z.mod_small by (destruct strict; lia). destruct strict; lia.
Qed.
Inductive xop2 : Type := OCase (e : expr) (mid : Z).

Definition xop_apply (op : xop) (ss : sym_state) : option sym_state :=
  match op with
  | OFact K => if (fact2_ok (s_know ss) K && APC.kentry_vars_lt (s_next ss) K)%bool
               then Some (SGP.set_kn ss (K :: s_know ss)) else None
  | OLtu a b strict =>
      match ltu_fact (s_know ss) a b strict with
      | Some K => if APC.kentry_vars_lt (s_next ss) K then Some (SGP.set_kn ss (K :: s_know ss)) else None
      | None => None
      end
  | OForget r => CXF.forget r ss
  | OContra cert => if contra_chk (s_know ss) cert then Some (contra_state ss) else None
  | OFactC K cert => if (factc_ok (s_know ss) K cert && APC.kentry_vars_lt (s_next ss) K)%bool then Some (SGP.set_kn ss (K :: s_know ss)) else None
  end.
Definition xop2_apply (op : xop2) (ss : sym_state) : option (sym_state * sym_state) :=
  match op with
  | OCase e mid =>
      if negb (APC.expr_vars_lt (s_next ss) e) then None else
      match range3 (s_know ss) e with
      | Some (lo, hi) =>
          if (Z.leb lo mid && Z.ltb mid hi)%bool
          then Some (SGP.set_kn ss (KRange e lo mid :: s_know ss), SGP.set_kn ss (KRange e (mid + 1) hi :: s_know ss))
          else None
      | None => None
      end
  end.
Definition xstep (T : list xop) (F : list SGP.region) (id : nat) (ss : sym_state) : option sym_state :=
  match nth_error T id with Some op => xop_apply op ss | None => None end.
Definition xstep2 (T : list xop2) (F : list SGP.region) (id : nat) (ss : sym_state) : option (sym_state * sym_state) :=
  match nth_error T id with Some op => xop2_apply op ss | None => None end.

Theorem xstep_ok : forall segs nx0 BR T F M0, SGP.XSTEP_ok segs nx0 BR (xstep T) F M0.
Proof.
  intros segs nx0 BR T F M0 Fv BRv fx id ss ss' E R Mc H HI. unfold xstep in H.
  destruct (nth_error T id) as [[K|a b strict|r|cert|K cert]|]; [| | | | |discriminate]; cbn [xop_apply] in H.
  - destruct (fact2_ok (s_know ss) K && APC.kentry_vars_lt (s_next ss) K)%bool eqn:Hc; [|discriminate]. injection H as <-.
    apply andb_prop in Hc as [Hf _].
    exists fx, E, R, Mc. split; [split; reflexivity|]. split; [|cbn [SGP.set_kn s_pc]; apply mst_refl].
    apply SGP.set_kn_INV2; [exact HI|]. constructor; [|exact (SGP.i_know _ _ _ _ _ _ _ _ _ HI)].
    exact (fact2_ok_sound segs E Mc (s_know ss) K (SGP.i_know _ _ _ _ _ _ _ _ _ HI) Hf).
  - destruct (ltu_fact (s_know ss) a b strict) as [K|] eqn:Hf; [|discriminate].
    destruct (APC.kentry_vars_lt (s_next ss) K); [|discriminate]. injection H as <-.
    exists fx, E, R, Mc. split; [split; reflexivity|]. split; [|cbn [SGP.set_kn s_pc]; apply mst_refl].
    apply SGP.set_kn_INV2; [exact HI|]. constructor; [|exact (SGP.i_know _ _ _ _ _ _ _ _ _ HI)].
    exact (ltu_fact_sound segs E Mc (s_know ss) a b strict K (SGP.i_know _ _ _ _ _ _ _ _ _ HI) Hf).
  - destruct (CXF.forget_sound segs nx0 BR F M0 r ss ss' E R Mc Fv BRv H HI) as (E' & Hag & HI' & Hpc).
    exists fx, E', R, Mc. split; [exact Hag|]. split; [exact HI' | rewrite Hpc; apply mst_refl].
  - destruct (contra_chk (s_know ss) cert) eqn:Hc; [|discriminate]. exfalso.
    exact (contra_sound segs E Mc (s_know ss) cert (SGP.i_know _ _ _ _ _ _ _ _ _ HI) Hc).
  - destruct (factc_ok (s_know ss) K cert && APC.kentry_vars_lt (s_next ss) K)%bool eqn:Hc; [|discriminate]. injection H as <-.
    apply andb_prop in Hc as [Hf _].
    exists fx, E, R, Mc. split; [split; reflexivity|]. split; [|cbn [SGP.set_kn s_pc]; apply mst_refl].
    apply SGP.set_kn_INV2; [exact HI|]. constructor; [|exact (SGP.i_know _ _ _ _ _ _ _ _ _ HI)].
    exact (factc_ok_sound segs E Mc (s_know ss) K cert (SGP.i_know _ _ _ _ _ _ _ _ _ HI) Hf).
Qed.

Theorem xstep2_ok : forall segs nx0 BR T F M0, SGP.XSTEP2_ok segs nx0 BR (xstep2 T) F M0.
Proof.
  intros segs nx0 BR T F M0 _ _ fx id ss ssa ssb E R Mc H HI. unfold xstep2 in H.
  destruct (nth_error T id) as [[e mid]|]; [|discriminate]. cbn [xop2_apply] in H.
  destruct (negb (APC.expr_vars_lt (s_next ss) e)); [discriminate|].
  destruct (range3 (s_know ss) e) as [[lo hi]|] eqn:Hb; [|discriminate].
  destruct (Z.leb lo mid && Z.ltb mid hi)%bool; [|discriminate]. injection H as <- <-.
  pose proof (range3_sound segs E Mc (s_know ss) e lo hi (SGP.i_know _ _ _ _ _ _ _ _ _ HI) Hb) as Hr.
  destruct (Z_le_gt_dec (bv_unsigned (edenot E e)) mid) as [Hle|Hgt].
  - exists fx, E, R, Mc, (SGP.set_kn ss (KRange e lo mid :: s_know ss)). split; [left; reflexivity|].
    split; [split; reflexivity|]. split; [|cbn [SGP.set_kn s_pc]; apply mst_refl].
    apply SGP.set_kn_INV2; [exact HI|]. constructor; [cbn [kentry_ok]; lia | exact (SGP.i_know _ _ _ _ _ _ _ _ _ HI)].
  - exists fx, E, R, Mc, (SGP.set_kn ss (KRange e (mid + 1) hi :: s_know ss)). split; [right; reflexivity|].
    split; [split; reflexivity|]. split; [|cbn [SGP.set_kn s_pc]; apply mst_refl].
    apply SGP.set_kn_INV2; [exact HI|]. constructor; [cbn [kentry_ok]; lia | exact (SGP.i_know _ _ _ _ _ _ _ _ _ HI)].
Qed.

End CX.
