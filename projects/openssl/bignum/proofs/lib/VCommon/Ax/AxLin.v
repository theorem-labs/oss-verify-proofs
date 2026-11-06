(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Definition terms := list (int * Z).
Definition lin : Type := (Z * terms)%type.
Definition valuation := int -> Z.

Fixpoint teval (ρ : valuation) (ts : terms) : Z :=
  match ts with
  | [] => 0
  | (x, a) :: r => a * ρ x + teval ρ r
  end.

Definition leval (ρ : valuation) (f : lin) : Z := fst f + teval ρ (snd f).

Definition lconst (c : Z) : lin := (c, []).
Definition lvar (x : int) (k : Z) : lin := (0, [(x, k)]).

Fixpoint tadd (a : terms) : terms -> terms :=
  match a with
  | [] => fun b => b
  | (x, p) :: ra =>
      fix tadd_b (b : terms) : terms :=
        match b with
        | [] => a
        | (y, q) :: rb =>
            if (x <? y)%uint63 then (x, p) :: tadd ra b
            else if (y <? x)%uint63 then (y, q) :: tadd_b rb
            else let s := p + q in if s =? 0 then tadd ra rb else (x, s) :: tadd ra rb
        end
  end.

Definition tscale (k : Z) (ts : terms) : terms := map (fun p => (fst p, k * snd p)) ts.

Definition ladd (f g : lin) : lin := (fst f + fst g, tadd (snd f) (snd g)).
Definition lscale (k : Z) (f : lin) : lin :=
  if k =? 0 then (0, []) else (k * fst f, tscale k (snd f)).
Definition laddc (f : lin) (c : Z) : lin := (fst f + c, snd f).
Definition lsub (f g : lin) : lin := ladd f (lscale (-1) g).

Lemma teval_tadd (ρ : valuation) : forall a b, teval ρ (tadd a b) = teval ρ a + teval ρ b.
Proof.
  induction a as [|[x p] ra IH]; intros b; [reflexivity|].
  induction b as [|[y q] rb IHb]; cbn [tadd teval] in *.
  - lia.
  - destruct (ltbP x y) as [Hxy|Hxy].
    + cbn [teval]. rewrite IH. cbn [teval]. lia.
    + destruct (ltbP y x) as [Hyx|Hyx].
      * cbn [teval]. rewrite IHb. cbn [teval]. lia.
      * assert (to_Z x = to_Z y) as E by lia. apply to_Z_inj in E. subst y.
        destruct (Z.eqb_spec (p + q) 0) as [E|E].
        -- rewrite IH. nia.
        -- cbn [teval]. rewrite IH. lia.
Qed.

Lemma teval_tscale (ρ : valuation) (k : Z) : forall ts, teval ρ (tscale k ts) = k * teval ρ ts.
Proof. induction ts as [|[x a] r IH]; cbn [tscale map teval fst snd] in *; [lia|]. unfold tscale in IH. rewrite IH. ring. Qed.

Lemma leval_ladd (ρ : valuation) (f g : lin) : leval ρ (ladd f g) = leval ρ f + leval ρ g.
Proof. unfold leval, ladd. cbn [fst snd]. rewrite teval_tadd. ring. Qed.

Lemma leval_lscale (ρ : valuation) (k : Z) (f : lin) : leval ρ (lscale k f) = k * leval ρ f.
Proof.
  unfold leval, lscale. destruct (Z.eqb_spec k 0) as [->|Hk]; cbn [fst snd teval]; [ring|].
  rewrite teval_tscale. ring.
Qed.

Lemma leval_laddc (ρ : valuation) (f : lin) (c : Z) : leval ρ (laddc f c) = leval ρ f + c.
Proof. unfold leval, laddc. cbn [fst snd]. ring. Qed.

Lemma leval_lsub (ρ : valuation) (f g : lin) : leval ρ (lsub f g) = leval ρ f - leval ρ g.
Proof. unfold lsub. rewrite leval_ladd, leval_lscale. ring. Qed.

Lemma leval_lvar (ρ : valuation) (x : int) (k : Z) : leval ρ (lvar x k) = k * ρ x.
Proof. unfold leval, lvar. cbn [fst snd teval]. ring. Qed.

Fixpoint teqb (a b : terms) : bool :=
  match a, b with
  | [], [] => true
  | (x, p) :: ra, (y, q) :: rb => if (x =? y)%uint63 then (if (p =? q) then teqb ra rb else false) else false
  | _, _ => false
  end.

Lemma teqb_eq (a b : terms) : teqb a b = true -> a = b.
Proof.
  revert b; induction a as [|[x p] ra IH]; intros [|[y q] rb] H; cbn [teqb] in H; try discriminate; [reflexivity|].
  destruct (x =? y)%uint63 eqn:H1; [|discriminate]. destruct (p =? q) eqn:H3; [|discriminate]. rename H into H2.
  apply eqb_spec in H1. apply Z.eqb_eq in H3. subst. f_equal. apply IH. exact H2.
Qed.

Definition tmult (k : Z) (g f : terms) : bool := teqb g (tscale k f).

Lemma tmult_sound (ρ : valuation) (k : Z) (g f : terms) : tmult k g f = true -> teval ρ g = k * teval ρ f.
Proof. unfold tmult. intros H. apply teqb_eq in H. subst g. apply teval_tscale. Qed.

Fixpoint tsame_vars (g f : terms) : bool :=
  match g, f with
  | [], [] => true
  | (x, _) :: rg, (y, _) :: rf => if (x =? y)%uint63 then tsame_vars rg rf else false
  | _, _ => false
  end.

Definition tratio (g f : terms) : option Z :=
  if tsame_vars g f then
  match g, f with
  | (_, p) :: _, (_, q) :: _ => if (q =? 0) then None else if (p mod q =? 0) then
                                  (let k := p / q in if tmult k g f then Some k else None) else None
  | _, _ => None
  end else None.

Lemma tsame_vars_tscale (k : Z) : forall g f, teqb g (tscale k f) = true -> tsame_vars g f = true.
Proof.
  induction g as [|[x p] rg IH]; intros [|[y q] rf] H; cbn [teqb tscale map fst snd tsame_vars] in *; try discriminate; [reflexivity|].
  destruct (x =? y)%uint63 eqn:H1; [|discriminate]. destruct (p =? k * q); [|discriminate]. apply IH. exact H.
Qed.

Lemma tratio_pre (g f : terms) : tratio g f =
  match g, f with
  | (_, p) :: _, (_, q) :: _ => if (q =? 0) then None else if (p mod q =? 0) then
                                  (let k := p / q in if tmult k g f then Some k else None) else None
  | _, _ => None
  end.
Proof.
  unfold tratio. destruct (tsame_vars g f) eqn:E; [reflexivity|]. cbv zeta.
  destruct g as [|[x p] rg]; [reflexivity|]. destruct f as [|[y q] rf]; [reflexivity|].
  destruct (q =? 0); [reflexivity|]. destruct (p mod q =? 0); [|reflexivity].
  destruct (tmult (p / q) ((x, p) :: rg) ((y, q) :: rf)) eqn:Et; [|reflexivity].
  unfold tmult in Et. apply tsame_vars_tscale in Et. rewrite Et in E. discriminate.
Qed.

Lemma tratio_sound (ρ : valuation) (g f : terms) (k : Z) : tratio g f = Some k -> teval ρ g = k * teval ρ f.
Proof.
  rewrite tratio_pre. cbv zeta.
  destruct g as [|[x p] rg]; [discriminate|]. destruct f as [|[y q] rf]; [discriminate|].
  destruct (q =? 0); [discriminate|]. destruct (p mod q =? 0); [|discriminate].
  destruct (tmult (p / q) ((x, p) :: rg) ((y, q) :: rf)) eqn:E; [|discriminate].
  intros H. injection H as <-. apply tmult_sound. exact E.
Qed.

Record fact : Type := Fact { fc_f : lin; fc_lo : Z; fc_hi : Z; fc_hole : bool }.

Definition fact_sat (ρ : valuation) (x : fact) : Prop :=
  if fc_hole x then leval ρ (fc_f x) <= fc_lo x \/ fc_hi x <= leval ρ (fc_f x)
  else fc_lo x <= leval ρ (fc_f x) <= fc_hi x.

Definition bdepth : nat := 16.

Record store : Type := ST { st_box : itrie (Z * Z); st_facts : list fact }.

Definition st_empty : store := ST IEmpty [].

Definition box_ok (ρ : valuation) (b : itrie (Z * Z)) : Prop :=
  forall (x : int) (i : Z * Z), to_Z x < 2 ^ 16 -> iget bdepth b x = Some i -> fst i <= ρ x <= snd i.

Definition sat (ρ : valuation) (s : store) : Prop := box_ok ρ (st_box s) /\ Forall (fact_sat ρ) (st_facts s).

Definition ivl : Type := (Z * Z)%type.

Fixpoint pdiv2 (p : positive) (x : Z) : option Z :=
  match p with
  | xH => Some x
  | xO p' => pdiv2 p' (Z.div2 x)
  | xI _ => None
  end.

Definition zdiv (x k : Z) : Z :=
  match k with
  | Zpos p => match pdiv2 p x with Some r => r | None => x / k end
  | _ => x / k
  end.

Lemma pdiv2_sound : forall p x r, pdiv2 p x = Some r -> r = x / Zpos p.
Proof.
  induction p as [p IH|p IH|]; intros x r H; cbn [pdiv2] in H; [discriminate| |].
  - apply IH in H. subst r. rewrite Z.div2_div. rewrite Z.div_div by lia. f_equal.
  - injection H as <-. rewrite Z.div_1_r. reflexivity.
Qed.

Lemma zdiv_eq (x k : Z) : zdiv x k = x / k.
Proof.
  unfold zdiv. destruct k as [|p|p]; try reflexivity.
  destruct (pdiv2 p x) as [r|] eqn:E; [exact (pdiv2_sound p x r E)|reflexivity].
Qed.

Definition imeet (a b : option ivl) : option ivl :=
  match a, b with
  | None, x => x
  | x, None => x
  | Some (l1, h1), Some (l2, h2) => Some (Z.max l1 l2, Z.min h1 h2)
  end.

Fixpoint fbound (l : list fact) (x : int) : option ivl :=
  match l with
  | [] => None
  | Fact (c, [(y, a)]) lo hi false :: r => if (y =? x)%uint63 then if c =? 0 then if a =? 1 then Some (lo, hi) else fbound r x else fbound r x else fbound r x
  | _ :: r => fbound r x
  end.

Lemma fbound_sound (ρ : valuation) (l : list fact) (x : int) : Forall (fact_sat ρ) l -> forall i, fbound l x = Some i -> fst i <= ρ x <= snd i.
Proof.
  induction l as [|fc r IH]; intros Hs i H; [discriminate|]. inversion Hs as [|? ? Hf Hr]; subst.
  destruct fc as [[c ts] lo hi ho]. cbn [fbound] in H.
  destruct ts as [|[y a] [|t2 r2]]; try (exact (IH Hr i H)). destruct ho; try (exact (IH Hr i H)).
  destruct (eqbP y x) as [E|E]; [|exact (IH Hr i H)]. destruct (Z.eqb_spec c 0) as [Ec|Ec]; [|exact (IH Hr i H)].
  destruct (Z.eqb_spec a 1) as [Ea|Ea]; [|exact (IH Hr i H)]. injection H as <-. apply to_Z_inj in E. subst.
  unfold fact_sat, leval in Hf. cbn [fc_hole fc_f fc_lo fc_hi fst snd teval] in *. lia.
Qed.

Definition vbound (s : store) (x : int) : option ivl :=
  if (x <? 65536)%uint63 then iget bdepth (st_box s) x else fbound (st_facts s) x.

Definition iscale (a : Z) (i : ivl) : ivl :=
  if 0 <=? a then (a * fst i, a * snd i) else (a * snd i, a * fst i).

Fixpoint tbox (s : store) (ts : terms) : option ivl :=
  match ts with
  | [] => Some (0, 0)
  | (x, a) :: r =>
      match vbound s x, tbox s r with
      | Some i, Some j => let k := iscale a i in Some (fst k + fst j, snd k + snd j)
      | _, _ => None
      end
  end.

Fixpoint trel (s : list fact) (c : Z) (ts : terms) : option ivl :=
  match s with
  | [] => None
  | Fact f lo hi false :: r =>
      let rest := trel r c ts in
      match tratio ts (snd f) with
      | Some k =>
          let i := iscale k (lo - fst f, hi - fst f) in imeet (Some (c + fst i, c + snd i)) rest
      | None =>
          match tratio (snd f) ts with
          | Some k => if 0 <? k then imeet (Some (c + - (zdiv (- (lo - fst f)) k), c + zdiv (hi - fst f) k)) rest else rest
          | None => rest
          end
      end
  | _ :: r => trel r c ts
  end.

Fixpoint hrefine (s : list fact) (ts : terms) (c : Z) (i : ivl) : ivl :=
  match s with
  | [] => i
  | Fact (cf, tf) hl hh true :: r =>
      let i' := if teqb ts tf then
                  let d := c - cf in
                  let lo := if hl <? fst i - d then Z.max (fst i) (hh + d) else fst i in
                  let hi := if snd i - d <? hh then Z.min (snd i) (hl + d) else snd i in
                  (lo, hi)
                else i in
      hrefine r ts c i'
  | _ :: r => hrefine r ts c i
  end.

Definition lrange (s : store) (g : lin) : option ivl :=
  match snd g with
  | [] => Some (fst g, fst g)
  | ts => match imeet (match tbox s ts with Some i => Some (fst g + fst i, fst g + snd i) | None => None end)
                      (trel (st_facts s) (fst g) ts) with
          | Some i => Some (hrefine (st_facts s) ts (fst g) i)
          | None => None
          end
  end.

Lemma imeet_sound (z : Z) (a b : option ivl) :
  (forall i, a = Some i -> fst i <= z <= snd i) -> (forall i, b = Some i -> fst i <= z <= snd i) ->
  forall i, imeet a b = Some i -> fst i <= z <= snd i.
Proof.
  intros Ha Hb i H. destruct a as [[l1 h1]|], b as [[l2 h2]|]; cbn [imeet] in H.
  - injection H as <-. specialize (Ha _ eq_refl). specialize (Hb _ eq_refl). cbn in *. lia.
  - apply Ha. exact H.
  - apply Hb. exact H.
  - discriminate.
Qed.

Lemma vbound_sound (ρ : valuation) (s : store) (x : int) :
  sat ρ s -> forall i, vbound s x = Some i -> fst i <= ρ x <= snd i.
Proof.
  intros [Hb Hfs] i H. unfold vbound in H. destruct (ltbP x 65536) as [Hx|Hx]; [|exact (fbound_sound ρ _ x Hfs i H)].
  apply (Hb x i); [change (to_Z 65536%uint63) with (2 ^ 16) in Hx; exact Hx | exact H].
Qed.

Lemma iscale_sound (a z : Z) (i : ivl) : fst i <= z <= snd i -> fst (iscale a i) <= a * z <= snd (iscale a i).
Proof. intros H. unfold iscale. destruct (Z.leb_spec 0 a); cbn [fst snd]; nia. Qed.

Lemma tbox_sound (ρ : valuation) (s : store) (ts : terms) :
  sat ρ s -> forall i, tbox s ts = Some i -> fst i <= teval ρ ts <= snd i.
Proof.
  intros Hs. induction ts as [|[x a] r IH]; intros i H; cbn [tbox teval] in *.
  - injection H as <-. cbn. lia.
  - destruct (vbound s x) as [j|] eqn:Ev; [|discriminate]. destruct (tbox s r) as [k|] eqn:Et; [|discriminate].
    injection H as <-. pose proof (vbound_sound ρ s x Hs j Ev) as Hj. pose proof (iscale_sound a (ρ x) j Hj).
    specialize (IH k eq_refl). cbn [fst snd]. lia.
Qed.

Lemma trel_sound (ρ : valuation) (s : list fact) (c : Z) (ts : terms) :
  Forall (fact_sat ρ) s -> forall i, trel s c ts = Some i -> fst i <= c + teval ρ ts <= snd i.
Proof.
  induction s as [|[f lo hi hl] r IH]; intros Hs i H; [discriminate|].
  inversion Hs as [|? ? Hf Hr]; subst. unfold fact_sat in Hf. cbn [fc_f fc_lo fc_hi fc_hole] in Hf.
  destruct hl; [apply IH; assumption|].
  cbn [trel] in H. destruct (tratio ts (snd f)) as [k|] eqn:Er.
  - revert H. apply imeet_sound; [| intros j Hj; apply IH; assumption].
    intros j Hj. injection Hj as <-. rewrite (tratio_sound ρ _ _ k Er).
    assert (Hi : fst (lo - fst f, hi - fst f) <= teval ρ (snd f) <= snd (lo - fst f, hi - fst f)).
    { unfold leval in Hf. cbn [fst snd]. lia. }
    pose proof (iscale_sound k _ _ Hi). cbn [fst snd] in *. lia.
  - destruct (tratio (snd f) ts) as [k|] eqn:Er2; [|apply IH; assumption].
    destruct (0 <? k) eqn:Ek; [|apply IH; assumption]. apply Z.ltb_lt in Ek.
    revert H. apply imeet_sound; [| intros j Hj; apply IH; assumption].
    intros j Hj. injection Hj as <-. cbn [fst snd]. rewrite !zdiv_eq.
    pose proof (tratio_sound ρ _ _ k Er2) as Et. unfold leval in Hf. rewrite Et in Hf.
    split.
    + assert (X : - teval ρ ts <= (- (lo - fst f)) / k) by (apply Z.div_le_lower_bound; lia). lia.
    + assert (X : teval ρ ts <= (hi - fst f) / k) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma hrefine_sound (ρ : valuation) (s : list fact) (ts : terms) (c : Z) :
  Forall (fact_sat ρ) s -> forall i, fst i <= c + teval ρ ts <= snd i -> fst (hrefine s ts c i) <= c + teval ρ ts <= snd (hrefine s ts c i).
Proof.
  induction s as [|[[cf tf] hl hh ho] r IH]; intros Hs i Hi; [exact Hi|].
  inversion Hs as [|? ? Hf Hr]; subst. unfold fact_sat, leval in Hf. cbn [fc_f fc_lo fc_hi fc_hole fst snd] in Hf.
  destruct ho; cbn [hrefine]; [|apply IH; assumption].
  apply IH; [exact Hr|]. destruct (teqb ts tf) eqn:Et; [|exact Hi].
  apply teqb_eq in Et. subst tf. destruct i as [lo hi]. cbn [fst snd] in *.
  destruct (Z.ltb_spec hl (lo - (c - cf))) as [H1|H1]; destruct (Z.ltb_spec (hi - (c - cf)) hh) as [H2|H2]; cbn [fst snd]; lia.
Qed.

Lemma lrange_sound (ρ : valuation) (s : store) (g : lin) :
  sat ρ s -> forall i, lrange s g = Some i -> fst i <= leval ρ g <= snd i.
Proof.
  intros Hs i H. unfold lrange, leval in *. destruct g as [c ts]. cbn [fst snd] in *.
  destruct ts as [|t r].
  - injection H as <-. cbn. lia.
  - destruct (imeet (match tbox s (t :: r) with Some i => Some (c + fst i, c + snd i) | None => None end)
                    (trel (st_facts s) c (t :: r))) as [j|] eqn:Ej; [|discriminate].
    injection H as <-. apply hrefine_sound; [exact (proj2 Hs)|]. revert Ej. apply imeet_sound.
    + intros k Hk. destruct (tbox s (t :: r)) as [k0|] eqn:Et; [|discriminate]. injection Hk as <-.
      pose proof (tbox_sound ρ s _ Hs k0 Et). cbn [fst snd]. lia.
    + intros k Hk. exact (trel_sound ρ (st_facts s) c (t :: r) (proj2 Hs) k Hk).
Qed.

Definition fdivc (a k : Z) : Z := - (zdiv (- a) k).

Definition mk_fact (f : lin) (lo hi : Z) : fact :=
  match snd f with
  | [(x, k)] => if 0 <? k then Fact (0, [(x, 1)]) (fdivc (lo - fst f) k) (zdiv (hi - fst f) k) false
                else if k <? 0 then Fact (0, [(x, 1)]) (fdivc (fst f - hi) (- k)) (zdiv (fst f - lo) (- k)) false
                else Fact f lo hi false
  | _ => Fact f lo hi false
  end.

Lemma fdivc_le (a k z : Z) : 0 < k -> a <= k * z -> fdivc a k <= z.
Proof.
  intros Hk H. unfold fdivc. rewrite zdiv_eq.
  assert (- z <= (- a) / k) as H2 by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma zdiv_le_of (b k z : Z) : 0 < k -> k * z <= b -> z <= zdiv b k.
Proof. intros Hk H. rewrite zdiv_eq. apply Z.div_le_lower_bound; lia. Qed.

Lemma mk_fact_sound (ρ : valuation) (f : lin) (lo hi : Z) :
  lo <= leval ρ f <= hi -> fact_sat ρ (mk_fact f lo hi).
Proof.
  intros H. unfold mk_fact. destruct f as [c ts]. cbn [fst snd] in *.
  destruct ts as [|[x k] [|t r]]; try exact H.
  unfold leval in H. cbn [fst snd teval] in H.
  destruct (Z.ltb_spec 0 k) as [Hk|Hk].
  - unfold fact_sat, leval; cbn [fc_f fc_lo fc_hi fc_hole fst snd teval]. split.
    + apply fdivc_le; [exact Hk|]. lia.
    + apply zdiv_le_of; [exact Hk|]. lia.
  - destruct (Z.ltb_spec k 0) as [Hk'|Hk'].
    + unfold fact_sat, leval; cbn [fc_f fc_lo fc_hi fc_hole fst snd teval]. split.
      * apply fdivc_le; [lia|]. lia.
      * apply zdiv_le_of; [lia|]. lia.
    + exact H.
Qed.

Definition box_add (b : itrie (Z * Z)) (x : int) (lo hi : Z) : itrie (Z * Z) :=
  match iget bdepth b x with
  | Some (l0, h0) => iset bdepth b x (Z.max lo l0, Z.min hi h0)
  | None => iset bdepth b x (lo, hi)
  end.

Definition unit_of (fc : fact) : option int :=
  match snd (fc_f fc) with
  | [p] => if (fst (fc_f fc) =? 0) && (snd p =? 1) && ((fst p) <? 65536)%uint63 && negb (fc_hole fc) then Some (fst p) else None
  | _ => None
  end.

Lemma unit_of_spec (fc : fact) (x : int) :
  unit_of fc = Some x -> fc_f fc = (0, [(x, 1)]) /\ fc_hole fc = false /\ to_Z x < 2 ^ 16.
Proof.
  unfold unit_of. destruct fc as [[c ts] l h ho]. cbn [fc_f fc_hole fst snd].
  destruct ts as [|[y k] [|t r]]; try discriminate. cbn [fst snd].
  destruct (Z.eqb_spec c 0) as [E1|E1]; cbn [andb]; [|discriminate].
  destruct (Z.eqb_spec k 1) as [E2|E2]; cbn [andb]; [|discriminate].
  destruct (ltbP y 65536) as [Hy|Hy]; cbn [andb]; [|discriminate].
  destruct ho; cbn [negb]; [discriminate|]. intros H. injection H as <-.
  subst. split; [reflexivity|]. split; [reflexivity|].
  change (to_Z 65536%uint63) with (2 ^ 16) in Hy. exact Hy.
Qed.

Definition sadd (s : store) (f : lin) (lo hi : Z) : store :=
  let fc := mk_fact f lo hi in
  match unit_of fc with
  | Some x => ST (box_add (st_box s) x (fc_lo fc) (fc_hi fc)) (st_facts s)
  | None => ST (st_box s) (fc :: st_facts s)
  end.

Lemma box_ok_add (ρ : valuation) (b : itrie (Z * Z)) (x : int) (lo hi : Z) :
  box_ok ρ b -> to_Z x < 2 ^ 16 -> lo <= ρ x <= hi -> box_ok ρ (box_add b x lo hi).
Proof.
  intros Hb Hx Hr y i Hy H. unfold box_add in H.
  assert (Hsame : forall v, iget bdepth (iset bdepth b x v) y = if (to_Z x =? to_Z y) then Some v else iget bdepth b y).
  { intros v. rewrite iget_iset. change (2 ^ Z.of_nat bdepth) with (2 ^ 16).
    pose proof (to_Z_bounded x). pose proof (to_Z_bounded y).
    rewrite !Z.mod_small by lia. reflexivity. }
  destruct (iget bdepth b x) as [[l0 h0]|] eqn:Eg; rewrite Hsame in H;
    destruct (Z.eqb_spec (to_Z x) (to_Z y)) as [E|E].
  - apply to_Z_inj in E. subst y. injection H as <-. pose proof (Hb x (l0, h0) Hx Eg). cbn [fst snd] in *. lia.
  - exact (Hb y i Hy H).
  - apply to_Z_inj in E. subst y. injection H as <-. cbn [fst snd]. lia.
  - exact (Hb y i Hy H).
Qed.

Lemma sat_sadd (ρ : valuation) (s : store) (f : lin) (lo hi : Z) :
  sat ρ s -> lo <= leval ρ f <= hi -> sat ρ (sadd s f lo hi).
Proof.
  intros [Hb Hf] Hr. pose proof (mk_fact_sound ρ f lo hi Hr) as Hm. unfold sadd.
  destruct (unit_of (mk_fact f lo hi)) as [x|] eqn:Eu.
  - destruct (unit_of_spec _ x Eu) as [E1 [E2 Hx]].
    split; [|exact Hf]. apply box_ok_add; [exact Hb | exact Hx|].
    unfold fact_sat in Hm. rewrite E1, E2 in Hm. unfold leval in Hm. cbn [fst snd teval] in Hm. lia.
  - split; [exact Hb | constructor; [exact Hm | exact Hf]].
Qed.

Definition shole (s : store) (f : lin) (lo hi : Z) : store := ST (st_box s) (Fact f lo hi true :: st_facts s).

Lemma sat_shole (ρ : valuation) (s : store) (f : lin) (lo hi : Z) :
  sat ρ s -> (leval ρ f <= lo \/ hi <= leval ρ f) -> sat ρ (shole s f lo hi).
Proof. intros [Hb Hs] Hf. split; [exact Hb | constructor; [exact Hf | exact Hs]]. Qed.

Lemma sat_empty (ρ : valuation) : sat ρ st_empty.
Proof. split; [intros x i _ H; cbn in H; discriminate | constructor]. Qed.

Fixpoint tvars_in (p : int -> bool) (ts : terms) : bool :=
  match ts with [] => true | (x, _) :: r => if p x then tvars_in p r else false end.
