(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Definition two64r : Z := 18446744073709551616.

(* [comment removed for export] *)
Fixpoint coef (ts : terms) (x : int) : Z :=
  match ts with
  | [] => 0
  | (y, a) :: r => if (y =? x)%uint63 then a else coef r x
  end.

(* [comment removed for export] *)
Fixpoint tmaxv (ts : terms) (acc : int) : int :=
  match ts with
  | [] => acc
  | (y, _) :: r => tmaxv r (if (y <? 65536)%uint63 &&& (acc <? y)%uint63 then y else acc)
  end.

(* [comment removed for export] *)
Fixpoint pivot2 (top : int) (tf ts : terms) : option (int * Z) :=
  match tf with
  | [] => None
  | (x, a) :: r => if negb (x =? top)%uint63 &&& negb (coef ts x =? 0) then Some (x, a) else pivot2 top r ts
  end.

Definition rgcd (ts : terms) : Z := fold_right (fun p g => Z.gcd (snd p) g) 0 ts.
Definition tdivide (g : Z) (ts : terms) : terms := map (fun p => (fst p, snd p / g)) ts.

Lemma rgcd_nonneg (ts : terms) : 0 <= rgcd ts.
Proof. destruct ts as [|p r]; cbn [rgcd fold_right]; [lia | apply Z.gcd_nonneg]. Qed.

Lemma teval_tdivide (ρ : valuation) (g : Z) : 0 < g -> forall ts, (forall p, In p ts -> (g | snd p)) ->
  teval ρ ts = g * teval ρ (tdivide g ts).
Proof.
  intros Hg. induction ts as [|[x a] r IH]; intros Hd; cbn [tdivide map teval fst snd]; [lia|].
  fold (tdivide g r). rewrite (IH (fun p Hp => Hd p (or_intror Hp))).
  destruct (Hd (x, a) (or_introl eq_refl)) as [q Hq]. cbn [snd] in Hq. subst a. rewrite Z.div_mul by lia. ring.
Qed.

Lemma rgcd_divides (ts : terms) : forall p, In p ts -> (rgcd ts | snd p).
Proof.
  induction ts as [|[x a] r IH]; intros p Hp; [destruct Hp|]. cbn [rgcd fold_right snd]. fold (rgcd r).
  destruct Hp as [<-|Hp]; [apply Z.gcd_divide_l|]. eapply Z.divide_trans; [apply Z.gcd_divide_r | exact (IH p Hp)].
Qed.

(* [comment removed for export] *)
Definition searcher : Type := Z -> terms -> Z -> Z -> bool * Z.

Definition searcher_ok (ρ : valuation) (sub : searcher) : Prop :=
  forall c ts G fuel fuel', sub c ts G fuel = (true, fuel') -> G <= c + teval ρ ts.

Section Pass.
Variable sub : searcher.

(* [comment removed for export] *)
Fixpoint rpass (only_top : bool) (top : int) (c : Z) (ts : terms) (G : Z) (fs : list fact) (fuel : Z) {struct fs} : bool * Z :=
  match fs with
  | [] => (false, fuel)
  | Fact (cf, tf) lo hi false :: r =>
      if fuel <=? 0 then (false, fuel) else
      let at_top := coef tf top in
      match (if only_top then (if at_top =? 0 then None else Some (top, at_top))
             else (if at_top =? 0 then pivot2 top tf ts else None)) with
      | None => rpass only_top top c ts G r fuel
      | Some (x, a) =>
          let b := coef ts x in
          let A := Z.abs a in
          let B := if 0 <? a then b else - b in
          if (if 0 <? B then lo <=? - two64r else two64r <=? hi) ||| (A =? 0) then rpass only_top top c ts G r fuel else
          let Blo := if 0 <? B then B * lo else B * hi in
          let '(ok, fuel') := sub (A * c - B * cf) (tadd (tscale A ts) (tscale (- B) tf)) (A * G - (A - 1) - Blo) (fuel - 1) in
          if ok then (true, fuel') else rpass only_top top c ts G r fuel'
      end
  | _ :: r => rpass only_top top c ts G r fuel
  end.

Lemma rpass_sound (ρ : valuation) (only_top : bool) (top : int) (c : Z) (ts : terms) (G : Z) :
  searcher_ok ρ sub -> forall fs fuel fuel', Forall (fact_sat ρ) fs -> rpass only_top top c ts G fs fuel = (true, fuel') -> G <= c + teval ρ ts.
Proof.
  intros Hsub. induction fs as [|[[cf tf] lo hi ho] r IH]; intros fuel fuel' Hfs H; [discriminate|].
  inversion Hfs as [|? ? Hf Hr]; subst. cbn [rpass] in H. destruct ho; [exact (IH _ _ Hr H)|].
  destruct (fuel <=? 0); [discriminate|].
  destruct (if only_top then (if coef tf top =? 0 then None else Some (top, coef tf top))
            else (if coef tf top =? 0 then pivot2 top tf ts else None)) as [[x a]|]; [|exact (IH _ _ Hr H)].
  cbv zeta in H.
  set (b := coef ts x) in *. set (A := Z.abs a) in *. set (B := if 0 <? a then b else - b) in *.
  destruct ((if 0 <? B then lo <=? - two64r else two64r <=? hi) ||| (A =? 0)) eqn:Einf; [exact (IH _ _ Hr H)|].
  apply lor_false in Einf as [_ EA]. apply Z.eqb_neq in EA.
  assert (HA : 0 < A) by (unfold A in *; lia).
  set (Blo := if 0 <? B then B * lo else B * hi) in *.
  destruct (sub (A * c - B * cf) (tadd (tscale A ts) (tscale (- B) tf)) (A * G - (A - 1) - Blo) (fuel - 1)) as [ok fuel1] eqn:Es.
  destruct ok; [|exact (IH _ _ Hr H)].
  pose proof (Hsub _ _ _ _ _ Es) as Hres. rewrite teval_tadd, !teval_tscale in Hres.
  unfold fact_sat, leval in Hf. cbn [fc_f fc_lo fc_hi fc_hole fst snd] in Hf.
  assert (HB : Blo <= B * (cf + teval ρ tf)).
  { unfold Blo. destruct (Z.ltb_spec 0 B); nia. }
  set (F := c + teval ρ ts) in *. set (P := cf + teval ρ tf) in *.
  assert (HF : A * G - (A - 1) <= A * F) by (unfold F, P in *; nia).
  nia.
Qed.

End Pass.

Definition RFUEL : Z := 400.

(* [comment removed for export] *)
Definition tnil (ts : terms) : bool := match ts with [] => true | _ => false end.

Fixpoint rsearch (d : nat) (s : store) {struct d} : searcher :=
  fun c ts G fuel =>
  if tnil ts then (G <=? c, fuel) else
  let g := rgcd ts in
  let ts' := if g <=? 1 then ts else tdivide g ts in
  let c' := if g <=? 1 then c else 0 in
  let G' := if g <=? 1 then G else - ((c - G) / g) in
  if (match tbox s ts' with Some (lo, _) => G' <=? c' + lo | None => false end) then (true, fuel) else
  match d with
  | O => (false, fuel)
  | S d' =>
      let top := tmaxv ts' 0%uint63 in
      let '(ok, fuel1) := rpass (rsearch d' s) true top c' ts' G' (st_facts s) fuel in
      if ok then (true, fuel1) else rpass (rsearch d' s) false top c' ts' G' (st_facts s) fuel1
  end.

Lemma rsearch_sound (ρ : valuation) (s : store) : sat ρ s -> forall d, searcher_ok ρ (rsearch d s).
Proof.
  intros Hs.
  assert (Hnorm : forall c ts G c' ts' G',
         c' = (if rgcd ts <=? 1 then c else 0) -> ts' = (if rgcd ts <=? 1 then ts else tdivide (rgcd ts) ts) ->
         G' = (if rgcd ts <=? 1 then G else - ((c - G) / rgcd ts)) ->
         G' <= c' + teval ρ ts' -> G <= c + teval ρ ts).
  { intros c ts G c' ts' G' -> -> ->. destruct (Z.leb_spec (rgcd ts) 1) as [Hg|Hg]; [tauto|].
    intros Hle. rewrite (teval_tdivide ρ (rgcd ts) ltac:(lia) ts (rgcd_divides ts)).
    pose proof (Z.mul_div_le (c - G) (rgcd ts) ltac:(lia)). nia. }
  induction d as [|d IH]; intros c ts G fuel fuel' H.
  all: unfold rsearch in H; fold rsearch in H; cbv zeta in H.
  all: destruct (tnil ts) eqn:En;
    [ destruct ts; [|discriminate En]; injection H as H _; apply Z.leb_le in H; cbn [teval]; lia | ].
  all: set (g := rgcd ts) in *; set (ts' := if g <=? 1 then ts else tdivide g ts) in *;
       set (c' := if g <=? 1 then c else 0) in *; set (G' := if g <=? 1 then G else - ((c - G) / g)) in *.
  all: apply (Hnorm c ts G c' ts' G' eq_refl eq_refl eq_refl).
  all: destruct (match tbox s ts' with Some (lo, _) => G' <=? c' + lo | None => false end) eqn:Eb;
    [ destruct (tbox s ts') as [[lo hi]|] eqn:Et; [|discriminate]; apply Z.leb_le in Eb;
      pose proof (tbox_sound ρ s ts' Hs _ Et) as Hb; cbn [fst snd] in Hb; lia | ].
  - discriminate.
  - destruct (rpass (rsearch d s) true (tmaxv ts' 0%uint63) c' ts' G' (st_facts s) fuel) as [ok fuel1] eqn:E1.
    destruct ok.
    + exact (rpass_sound (rsearch d s) ρ true _ c' ts' G' IH _ _ _ (proj2 Hs) E1).
    + exact (rpass_sound (rsearch d s) ρ false _ c' ts' G' IH _ _ _ (proj2 Hs) H).
Qed.

(* [comment removed for export] *)
Fixpoint rdeepen (n : nat) (d0 : nat) (s : store) (f : lin) (c : Z) : bool :=
  match n with
  | O => false
  | S n' => if fst (rsearch d0 s (fst f) (snd f) c RFUEL) then true else rdeepen n' (S d0) s f c
  end.

Lemma rdeepen_sound (ρ : valuation) (s : store) (f : lin) (c : Z) : sat ρ s ->
  forall n d0, rdeepen n d0 s f c = true -> c <= leval ρ f.
Proof.
  intros Hs. induction n as [|n IH]; intros d0 H; [discriminate|]. cbn [rdeepen] in H.
  destruct (rsearch d0 s (fst f) (snd f) c RFUEL) as [ok fl] eqn:E. cbn [fst] in H. destruct ok.
  - exact (rsearch_sound ρ s Hs d0 _ _ _ _ _ E).
  - exact (IH _ H).
Qed.

(* [comment removed for export] *)
Definition rprove (d : nat) (s : store) (f : lin) (c : Z) : bool :=
  match lrange s f with
  | Some (lo, _) => if c <=? lo then true else rdeepen (S d) 1 s f c
  | None => rdeepen (S d) 1 s f c
  end.

Lemma rprove_sound (ρ : valuation) (s : store) (d : nat) (f : lin) (c : Z) : sat ρ s -> rprove d s f c = true -> c <= leval ρ f.
Proof.
  intros Hs H. unfold rprove in H.
  destruct (lrange s f) as [[lo hi]|] eqn:El; [|exact (rdeepen_sound ρ s f c Hs _ _ H)].
  destruct (Z.leb_spec c lo) as [Hc|Hc]; [|exact (rdeepen_sound ρ s f c Hs _ _ H)].
  pose proof (lrange_sound ρ s f Hs _ El) as X. cbn [fst snd] in X. lia.
Qed.

(* [comment removed for export] *)
Definition rprove_le (d : nat) (s : store) (f : lin) (c : Z) : bool := rprove d s (lscale (-1) f) (- c).

Lemma rprove_le_sound (ρ : valuation) (s : store) (d : nat) (f : lin) (c : Z) : sat ρ s -> rprove_le d s f c = true -> leval ρ f <= c.
Proof. intros Hs H. pose proof (rprove_sound ρ s d _ _ Hs H) as X. rewrite leval_lscale in X. lia. Qed.

(* [comment removed for export] *)
Definition rbetween (d : nat) (s : store) (f : lin) (lo hi : Z) : bool :=
  match lrange s f with
  | Some (l, h) => ((lo <=? l) ||| rprove d s f lo) &&& ((h <=? hi) ||| rprove_le d s f hi)
  | None => rprove d s f lo &&& rprove_le d s f hi
  end.

Lemma rbetween_sound (ρ : valuation) (s : store) (d : nat) (f : lin) (lo hi : Z) : sat ρ s -> rbetween d s f lo hi = true -> lo <= leval ρ f <= hi.
Proof.
  intros Hs H. unfold rbetween in H.
  destruct (lrange s f) as [[l h]|] eqn:El.
  - pose proof (lrange_sound ρ s f Hs _ El) as X. cbn [fst snd] in X.
    apply land_true in H as [H1 H2]. split.
    + apply lor_true in H1 as [H1|H1]; [apply Z.leb_le in H1; lia | exact (rprove_sound ρ s d f lo Hs H1)].
    + apply lor_true in H2 as [H2|H2]; [apply Z.leb_le in H2; lia | exact (rprove_le_sound ρ s d f hi Hs H2)].
  - apply land_true in H as [H1 H2]. split; [exact (rprove_sound ρ s d f lo Hs H1) | exact (rprove_le_sound ρ s d f hi Hs H2)].
Qed.
