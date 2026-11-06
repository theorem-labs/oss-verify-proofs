(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec SeqExec StoreOk MemSplit SymExec3Sound.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import SymExec3Sound.SX2S.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Fixpoint ins_sorted (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | y :: t => if x <? y then x :: l else if x =? y then l else y :: ins_sorted x t
  end.

Definition covered (rs : list run) : list Z :=
  flat_map (fun r : run => map (fun i => fst r + Z.of_nat i) (seq 0 (length (snd r)))) rs.

Definition addrs_sorted (rs : list run) : list Z := fold_right ins_sorted [] (covered rs).

Fixpoint group_runs (rs : list run) (xs : list Z) (cur_a : Z) (cur : list Z) (next : Z) : list run :=
  match xs with
  | [] => match cur with [] => [] | _ => [(cur_a, rev cur)] end
  | x :: t =>
      let b := match lookup_byte rs x with Some b => b | None => 0 end in
      match cur with
      | [] => group_runs rs t x [b] (x + 1)
      | _ => if x =? next then group_runs rs t cur_a (b :: cur) (x + 1)
             else (cur_a, rev cur) :: group_runs rs t x [b] (x + 1)
      end
  end.

Definition norm_runs (rs : list run) : list run := group_runs rs (addrs_sorted rs) 0 [] 0.

Definition ozeqb (a b : option Z) : bool :=
  match a, b with
  | Some x, Some y => x =? y
  | None, None => true
  | _, _ => false
  end.

Definition runs_equiv (r1 r2 : list run) : bool :=
  forallb (fun x => ozeqb (lookup_byte r1 x) (lookup_byte r2 x)) (covered r1 ++ covered r2).

Definition annot (rs : list run) : list (Z * Z * list Z) :=
  map (fun r : run => (fst r, fst r + Z.of_nat (length (snd r)), snd r)) rs.
Fixpoint lookupL (rs : list (Z * Z * list Z)) (x : Z) : option Z :=
  match rs with
  | [] => None
  | (a, e, bs) :: rest => if (Z.leb a x && Z.ltb x e)%bool then Some (nth (Z.to_nat (x - a)) bs 0%Z) else lookupL rest x
  end.
Lemma lookupL_annot : forall rs x, lookupL (annot rs) x = lookup_byte rs x.
Proof. induction rs as [|[a bs] rest IH]; intros x; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Definition runs_equivF (r1 r2 : list run) : bool :=
  let a1 := annot r1 in let a2 := annot r2 in
  forallb (fun x => ozeqb (lookupL a1 x) (lookupL a2 x)) (covered r1 ++ covered r2).
Lemma runs_equivF_eq : forall r1 r2, runs_equivF r1 r2 = runs_equiv r1 r2.
Proof.
  intros r1 r2. unfold runs_equivF, runs_equiv. cbv zeta.
  induction (covered r1 ++ covered r2) as [|x l IH]; cbn [forallb]; [reflexivity|].
  rewrite !lookupL_annot, IH. reflexivity.
Qed.

Lemma ozeqb_eq : forall a b, ozeqb a b = true -> a = b.
Proof.
  intros [x|] [y|] H; cbn in H; try discriminate; [|reflexivity].
  apply Z.eqb_eq in H. congruence.
Qed.

Lemma in_covered : forall rs x a bs,
  In (a, bs) rs -> a <= x < a + Z.of_nat (length bs) -> In x (covered rs).
Proof.
  intros rs x a bs Hin Hx. unfold covered. apply in_flat_map. exists (a, bs). split; [exact Hin|].
  cbn [fst snd]. apply in_map_iff. exists (Z.to_nat (x - a)). split; [lia|].
  apply in_seq. lia.
Qed.

Lemma lookup_byte_none : forall rs x, ~ In x (covered rs) -> lookup_byte rs x = None.
Proof.
  induction rs as [|[a bs] rest IH]; intros x Hn; cbn [lookup_byte]; [reflexivity|].
  destruct (Z.leb a x && Z.ltb x (a + Z.of_nat (length bs)))%bool eqn:Hin.
  - exfalso. apply Hn. apply andb_prop in Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    apply (in_covered _ x a bs); [left; reflexivity | lia].
  - apply IH. intros Hc. apply Hn. unfold covered in *. cbn [flat_map]. apply in_app_iff. right. exact Hc.
Qed.

Lemma runs_equiv_lookup : forall r1 r2 x, runs_equiv r1 r2 = true -> lookup_byte r1 x = lookup_byte r2 x.
Proof.
  intros r1 r2 x H. unfold runs_equiv in H.
  destruct (in_dec Z.eq_dec x (covered r1 ++ covered r2)) as [Hin|Hout].
  - apply ozeqb_eq. exact (proj1 (forallb_forall _ _) H x Hin).
  - rewrite !lookup_byte_none; [reflexivity| |]; intros Hc; apply Hout; apply in_app_iff; [right|left]; exact Hc.
Qed.

Theorem runs_equiv_sound : forall r1 r2 D (a : word),
  runs_ok r1 = true -> runs_ok r2 = true -> runs_equiv r1 r2 = true ->
  apply_runs r1 D a = apply_runs r2 D a.
Proof.
  intros r1 r2 D a H1 H2 He. pose proof (u64_range a) as Ha.
  rewrite <- (Z_to_bv_bv_unsigned 64 a).
  rewrite !apply_runs_at by (assumption || lia).
  rewrite (runs_equiv_lookup r1 r2) by exact He. reflexivity.
Qed.

Definition runs_clear (rs : list run) (lo : Z) (n : nat) : bool :=
  forallb (fun r : run => (lo + Z.of_nat n <=? fst r) || (fst r + Z.of_nat (length (snd r)) <=? lo)) rs.

Lemma runs_clear_lookup : forall rs lo n x,
  runs_clear rs lo n = true -> lo <= x < lo + Z.of_nat n -> lookup_byte rs x = None.
Proof.
  induction rs as [|[a bs] rest IH]; intros lo n x H Hx; cbn [lookup_byte runs_clear forallb fst snd] in *; [reflexivity|].
  apply andb_prop in H as [H Hr]. apply orb_true_iff in H. destruct H as [H|H]; apply Z.leb_le in H.
  - replace (Z.leb a x && Z.ltb x (a + Z.of_nat (length bs)))%bool with false
      by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    eapply IH; eassumption.
  - replace (Z.leb a x && Z.ltb x (a + Z.of_nat (length bs)))%bool with false
      by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
    eapply IH; eassumption.
Qed.

Lemma apply_runs_clear_at : forall rs D lo n (x : Z),
  runs_ok rs = true -> runs_clear rs lo n = true -> 0 <= x < 2 ^ 64 -> lo <= x < lo + Z.of_nat n ->
  apply_runs rs D (Z_to_bv 64 x) = D (Z_to_bv 64 x).
Proof.
  intros rs D lo n x Hok Hc Hx Hr. rewrite apply_runs_at by assumption.
  rewrite (runs_clear_lookup rs lo n x Hc Hr). reflexivity.
Qed.

Lemma rdn_apply_runs_clear : forall segs rs D lo n,
  runs_ok rs = true -> runs_clear rs lo n = true -> 0 <= lo < 2 ^ 64 -> lo + Z.of_nat n <= 2 ^ 64 ->
  rdn segs (apply_runs rs D) (Z_to_bv 64 lo) n = rdn segs D (Z_to_bv 64 lo) n.
Proof.
  intros segs rs D lo n Hok Hc Hlo Hhi. apply rdn_ext; [rewrite u_small by lia; lia|]. intros x Hx.
  rewrite u_small in Hx by lia. pose proof (u64_range x).
  rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (apply_runs_clear_at rs D lo n); try assumption; lia.
Qed.

Definition pins (rs : list run) (M : word -> option byte) : Prop :=
  forall y b, 0 <= y < 2 ^ 64 -> lookup_byte rs y = Some b -> M (Z_to_bv 64 y) = Some (Z_to_bv 8 b).

Definition in_runs (rs : list run) (a : Z) : Prop := lookup_byte rs a <> None.

Lemma in_runs_covered : forall rs a, in_runs rs a ->
  exists r, In r rs /\ fst r <= a < fst r + Z.of_nat (length (snd r)).
Proof.
  intros rs a H. unfold in_runs in H.
  destruct (in_dec Z.eq_dec a (covered rs)) as [Hin|Hout].
  - unfold covered in Hin. apply in_flat_map in Hin as ([ra bs] & Hr & Hm). cbn [fst snd] in Hm.
    apply in_map_iff in Hm as (i & Hi1 & Hi). apply in_seq in Hi.
    exists (ra, bs). split; [exact Hr|]. cbn [fst snd]. lia.
  - exfalso. apply H. apply lookup_byte_none. exact Hout.
Qed.

Lemma apply_runs_pins : forall rs D, runs_ok rs = true -> pins rs (apply_runs rs D).
Proof.
  intros rs D Hok y b Hy Hl. rewrite apply_runs_at by assumption. rewrite Hl. reflexivity.
Qed.

Lemma rdn_of_pins : forall segs rs M n (x : Z) zs,
  pins rs M -> 0 <= x -> x + Z.of_nat n <= 2 ^ 64 ->
  lookup_runs rs x n = Some zs ->
  rdn segs M (Z_to_bv 64 x) n = Some (map (Z_to_bv 8) zs).
Proof.
  intros segs rs M n. induction n as [|k IH]; intros x zs HP Hx Hn HL; cbn [lookup_runs] in HL.
  - injection HL as <-. reflexivity.
  - destruct (lookup_byte rs x) as [b|] eqn:Hb; [|discriminate].
    destruct (lookup_runs rs (x + 1) k) as [r|] eqn:Hr; [|discriminate].
    injection HL as <-. cbn [map].
    change (S k) with (1 + k)%nat. apply (rdn_app segs _ 1 k _ [Z_to_bv 8 b] (map (Z_to_bv 8) r)).
    + cbn [rdn]. rewrite (HP x b) by (lia || exact Hb). reflexivity.
    + rewrite w_add_nat, u_small by lia. cbn [Z.of_nat]. apply IH; try assumption; lia.
Qed.

Lemma pins_same : forall rs M M',
  pins rs M -> (forall a : word, in_runs rs (bv_unsigned a) -> M' a = M a) -> pins rs M'.
Proof.
  intros rs M M' HP HS y b Hy Hl. rewrite HS; [apply HP; assumption|].
  unfold in_runs. rewrite u_small by lia. rewrite Hl. discriminate.
Qed.

Definition runs_sub (r1 r2 : list run) : bool :=
  forallb (fun x => ozeqb (lookup_byte r1 x) (lookup_byte r2 x)) (covered r1).

Lemma runs_sub_lookup : forall r1 r2 x b, runs_sub r1 r2 = true ->
  lookup_byte r1 x = Some b -> lookup_byte r2 x = Some b.
Proof.
  intros r1 r2 x b H Hl. unfold runs_sub in H.
  destruct (in_dec Z.eq_dec x (covered r1)) as [Hin|Hout].
  - rewrite <- Hl. symmetry. apply ozeqb_eq. exact (proj1 (forallb_forall _ _) H x Hin).
  - rewrite (lookup_byte_none r1 x Hout) in Hl. discriminate.
Qed.

Lemma pins_sub : forall r1 r2 M, runs_sub r1 r2 = true -> pins r2 M -> pins r1 M.
Proof.
  intros r1 r2 M Hs HP y b Hy Hl. apply HP; [exact Hy|]. eapply runs_sub_lookup; eassumption.
Qed.

Definition drop_run (a : Z) (rs : list run) : list run := filter (fun r : run => negb (fst r =? a)) rs.
