(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From Stdlib Require PrimInt63 Uint63.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import PropExec AxSyioe AxSyclu Asanz3l.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Booteo9.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Booteo9.Bootf6d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Bootx2q Boot1pr.

Module Bootnws.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Import ListNotations. Import AX2.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Module KBF.

(* [comment removed for export] *)
Fixpoint eqbL (x y : expr) : bool :=
  match x, y with
  | ELit a, ELit b => Z.eqb a b
  | EVar a, EVar b => Nat.eqb a b
  | EAlu o a b, EAlu o' a' b' => if aluop_eqb o o' then (if eqbL a a' then eqbL b b' else false) else false
  | EAluw o a b, EAluw o' a' b' => if aluop_eqb o o' then (if eqbL a a' then eqbL b b' else false) else false
  | EMd o a b, EMd o' a' b' => if mulop_eqb o o' then (if eqbL a a' then eqbL b b' else false) else false
  | EMdw o a b, EMdw o' a' b' => if mulop_eqb o o' then (if eqbL a a' then eqbL b b' else false) else false
  | EExt s l n a, EExt s' l' n' a' =>
      if Bool.eqb s s' then (if Nat.eqb l l' then (if Nat.eqb n n' then eqbL a a' else false) else false) else false
  | EBlob s k i n, EBlob s' k' i' n' =>
      if Bool.eqb s s' then (if Nat.eqb k k' then (if Z.eqb i i' then Nat.eqb n n' else false) else false) else false
  | _, _ => false
  end.
Lemma eqbL_eq : forall x y, eqbL x y = expr_eqb x y.
Proof.
  induction x as [a|a|o a IHa b IHb|o a IHa b IHb|o a IHa b IHb|o a IHa b IHb|sx l n a IHa|sx k i n];
    intros [a'|a'|o' a' b'|o' a' b'|o' a' b'|o' a' b'|sx' l' n' a'|sx' k' i' n']; try reflexivity; cbn [eqbL expr_eqb];
    rewrite ?IHa, ?IHb.
  - destruct (aluop_eqb o o'); [destruct (expr_eqb a a'); reflexivity|reflexivity].
  - destruct (aluop_eqb o o'); [destruct (expr_eqb a a'); reflexivity|reflexivity].
  - destruct (mulop_eqb o o'); [destruct (expr_eqb a a'); reflexivity|reflexivity].
  - destruct (mulop_eqb o o'); [destruct (expr_eqb a a'); reflexivity|reflexivity].
  - destruct (Bool.eqb sx sx'); [destruct (Nat.eqb l l'); [destruct (Nat.eqb n n'); reflexivity|reflexivity]|reflexivity].
  - destruct (Bool.eqb sx sx'); [destruct (Nat.eqb k k'); [destruct (Z.eqb i i'); reflexivity|reflexivity]|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma two64_eq : two64 = 2 ^ 64. Proof. reflexivity. Qed.
Lemma two64_pos : 0 < two64. Proof. reflexivity. Qed.
Definition ones64 : Z := Z.ones 64.
Lemma ones64_eq : ones64 = two64 - 1. Proof. reflexivity. Qed.

Lemma land_le_l : forall a k, 0 <= a -> Z.land a k <= a.
Proof.
  intros a k Ha.
  assert (H : Z.ldiff (Z.land a k) a = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit a n), (Z.testbit k n); reflexivity. }
  pose proof (Z.sub_nocarry_ldiff a (Z.land a k) H) as E.
  assert (0 <= Z.ldiff a (Z.land a k)) by (apply Z.ldiff_nonneg; left; exact Ha). lia.
Qed.
Lemma land_nonneg_l : forall a k, 0 <= a -> 0 <= Z.land a k.
Proof. intros. apply Z.land_nonneg. left. assumption. Qed.
Lemma lor_lt_two64 : forall a b, 0 <= a < two64 -> 0 <= b < two64 -> 0 <= Z.lor a b < two64.
Proof.
  intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [E|E]; [rewrite E; reflexivity|].
  assert (0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
  rewrite two64_eq. apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor by lia.
  assert (La : Z.log2 a < 64). { destruct (Z.eq_dec a 0) as [->|]; [reflexivity|apply Z.log2_lt_pow2; [lia|rewrite <- two64_eq; lia]]. }
  assert (Lb : Z.log2 b < 64). { destruct (Z.eq_dec b 0) as [->|]; [reflexivity|apply Z.log2_lt_pow2; [lia|rewrite <- two64_eq; lia]]. }
  lia.
Qed.
Lemma lxor_lt_two64 : forall a b, 0 <= a < two64 -> 0 <= b < two64 -> 0 <= Z.lxor a b < two64.
Proof.
  intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [E|E]; [rewrite E; reflexivity|].
  assert (0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  rewrite two64_eq. apply Z.log2_lt_pow2; [lia|]. pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)).
  assert (La : Z.log2 a < 64). { destruct (Z.eq_dec a 0) as [->|]; [reflexivity|apply Z.log2_lt_pow2; [lia|rewrite <- two64_eq; lia]]. }
  assert (Lb : Z.log2 b < 64). { destruct (Z.eq_dec b 0) as [->|]; [reflexivity|apply Z.log2_lt_pow2; [lia|rewrite <- two64_eq; lia]]. }
  lia.
Qed.
(* [comment removed for export] *)
Lemma le_ones_sub : forall x m, 0 <= x < two64 -> 0 <= m < two64 -> Z.land x m = 0 -> x <= ones64 - m.
Proof.
  intros x m Hx Hm H. pose proof (Z.add_lor_land x m) as E. rewrite H in E.
  pose proof (lor_lt_two64 x m Hx Hm). rewrite ones64_eq. lia.
Qed.
Lemma ge_known1 : forall x k, 0 <= x -> Z.land x k = k -> k <= x.
Proof. intros x k Hx H. rewrite <- H. apply land_le_l. exact Hx. Qed.

(* [comment removed for export] *)
Record av : Type := AV { alo : Z; ahi : Z; ak0 : Z; ak1 : Z }.
Definition gam (A : av) (x : Z) : Prop :=
  0 <= x < two64 /\ alo A <= x <= ahi A /\ Z.land x (ak0 A) = 0 /\ Z.land x (ak1 A) = ak1 A.

Ltac tb H n := let Hb := fresh "Hb" in
  pose proof (f_equal (fun t => Z.testbit t n) H) as Hb; cbn beta in Hb;
  rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.lxor_spec, ?Z.bits_0 in Hb.
Ltac bcases := repeat match goal with
  | H : context [Z.testbit ?a ?m] |- _ => destruct (Z.testbit a m)
  | |- context [Z.testbit ?a ?m] => destruct (Z.testbit a m)
  end; try discriminate; try reflexivity.

Lemma land_ones64_id : forall x, 0 <= x < two64 -> Z.land x ones64 = x.
Proof. intros x Hx. unfold ones64. rewrite Z.land_ones by lia. apply Z.mod_small. rewrite <- two64_eq. exact Hx. Qed.
(* [comment removed for export] *)
Lemma land_compl : forall x, 0 <= x < two64 -> Z.land x (Z.lxor x ones64) = 0.
Proof.
  intros x Hx. pose proof (land_ones64_id x Hx) as E. apply Z.bits_inj'. intros n Hn. tb E n.
  rewrite Z.land_spec, Z.lxor_spec, Z.bits_0. bcases.
Qed.

(* [comment removed for export] *)
Lemma hi_bits_eq : forall lo hi x, 0 <= lo -> lo <= x <= hi -> Z.lxor lo hi <> 0 ->
  let j := Z.succ (Z.log2 (Z.lxor lo hi)) in 0 < j /\ Z.shiftr x j = Z.shiftr lo j.
Proof.
  intros lo hi x Hlo Hx Hd j.
  assert (Hd0 : 0 <= Z.lxor lo hi) by (apply Z.lxor_nonneg; lia).
  assert (Hj : 0 < j) by (unfold j; pose proof (Z.log2_nonneg (Z.lxor lo hi)); lia).
  split; [exact Hj|].
  assert (E0 : Z.shiftr (Z.lxor lo hi) j = 0) by (apply Z.shiftr_eq_0; [exact Hd0|unfold j; lia]).
  rewrite Z.shiftr_lxor in E0. apply Z.lxor_eq in E0.
  rewrite !Z.shiftr_div_pow2 in * by lia.
  assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.div_le_mono lo x (2 ^ j) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono x hi (2 ^ j) ltac:(lia) ltac:(lia)). lia.
Qed.

Definition reduce (lo hi k0 k1 : Z) : option av :=
  let lo1 := Z.max (Z.max lo 0) k1 in
  let hi1 := Z.min hi (ones64 - Z.land k0 ones64) in
  if Z.ltb hi1 lo1 then None else
  let d := Z.lxor lo1 hi1 in
  if Z.eqb d 0 then Some (AV lo1 lo1 (Z.lxor lo1 ones64) lo1)
  else let j := Z.succ (Z.log2 d) in
       Some (AV lo1 hi1 (Z.lor k0 (Z.shiftl (Z.shiftr (Z.lxor lo1 ones64) j) j)) (Z.lor k1 (Z.shiftl (Z.shiftr lo1 j) j))).

Lemma reduce_sound : forall lo hi k0 k1 x A,
  0 <= x < two64 -> lo <= x <= hi -> Z.land x k0 = 0 -> Z.land x k1 = k1 ->
  reduce lo hi k0 k1 = Some A -> gam A x.
Proof.
  intros lo hi k0 k1 x A Hx Hi H0 H1. unfold reduce.
  set (lo1 := Z.max (Z.max lo 0) k1). set (hi1 := Z.min hi (ones64 - Z.land k0 ones64)).
  assert (L1 : lo1 <= x). { pose proof (ge_known1 x k1 ltac:(lia) H1). unfold lo1. lia. }
  assert (L2 : x <= hi1).
  { assert (Hm : 0 <= Z.land k0 ones64 < two64).
    { unfold ones64. rewrite Z.land_ones by lia. rewrite two64_eq. apply Z.mod_pos_bound. reflexivity. }
    pose proof (le_ones_sub x (Z.land k0 ones64) Hx Hm) as Q.
    rewrite Z.land_assoc, H0, Z.land_0_l in Q. specialize (Q eq_refl). unfold hi1. lia. }
  assert (L0 : 0 <= lo1) by (unfold lo1; lia).
  destruct (Z.ltb hi1 lo1); [discriminate|].
  destruct (Z.eqb (Z.lxor lo1 hi1) 0) eqn:Ed.
  - apply Z.eqb_eq, Z.lxor_eq in Ed. intros Q. injection Q as <-. unfold gam. cbn [alo ahi ak0 ak1].
    assert (x = lo1) by lia. subst x. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; [apply land_compl; exact Hx|apply Z.land_diag].
  - apply Z.eqb_neq in Ed. intros Q. injection Q as <-. unfold gam. cbn [alo ahi ak0 ak1].
    destruct (hi_bits_eq lo1 hi1 x L0 (conj L1 L2) Ed) as [Hj Es]. set (j := Z.succ (Z.log2 (Z.lxor lo1 hi1))) in *.
    assert (Hb : forall n, j <= n -> Z.testbit lo1 n = Z.testbit x n).
    { intros n Hn. replace n with ((n - j) + j) by lia. rewrite <- !Z.shiftr_spec by lia. rewrite Es. reflexivity. }
    pose proof (land_ones64_id x Hx) as Eo.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
    + rewrite Z.land_lor_distr_r, H0, Z.lor_0_l. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.lt_ge_cases n j) as [Hl|Hg].
      * rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
      * rewrite Z.shiftl_spec by lia. rewrite Z.shiftr_spec by lia. replace (n - j + j) with n by lia.
        rewrite Z.lxor_spec, (Hb n Hg). tb Eo n. bcases.
    + rewrite Z.land_lor_distr_r, H1. f_equal. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
      destruct (Z.lt_ge_cases n j) as [Hl|Hg].
      * rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
      * rewrite Z.shiftl_spec by lia. rewrite Z.shiftr_spec by lia. replace (n - j + j) with n by lia.
        rewrite (Hb n Hg). apply andb_diag.
Qed.

Definition cst (c : Z) : av := AV c c (Z.lxor c ones64) c.
Lemma cst_gam : forall c, 0 <= c < two64 -> gam (cst c) c.
Proof. intros c Hc. unfold gam, cst. cbn [alo ahi ak0 ak1]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; [apply land_compl; exact Hc|apply Z.land_diag]. Qed.

(* [comment removed for export] *)
Fixpoint lowcnt (fuel : nat) (m : Z) : Z :=
  match fuel with
  | O => 0
  | S f => if Z.odd m then Z.succ (lowcnt f (Z.div2 m)) else 0
  end.
Lemma lowcnt_spec : forall f m, 0 <= lowcnt f m <= Z.of_nat f /\ Z.land m (Z.ones (lowcnt f m)) = Z.ones (lowcnt f m).
Proof.
  induction f as [|f IH]; intros m; cbn [lowcnt].
  - split; [lia|]. change (Z.ones 0) with 0. apply Z.land_0_r.
  - destruct (Z.odd m) eqn:Eo.
    + destruct (IH (Z.div2 m)) as [[H1 H2] H3]. split; [lia|].
      set (j := lowcnt f (Z.div2 m)) in *.
      apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
      destruct (Z.eq_dec n 0) as [->|Hn0].
      * rewrite Z.bit0_odd, Eo. reflexivity.
      * tb H3 (n - 1). rewrite Z.div2_spec, Z.shiftr_spec in Hb by lia. replace (n - 1 + 1) with n in Hb by lia.
        destruct (Z.lt_ge_cases n (Z.succ j)) as [Hl|Hg].
        -- rewrite (Z.ones_spec_low (Z.succ j) n) by lia. rewrite (Z.ones_spec_low j (n - 1)) in Hb by lia. exact Hb.
        -- rewrite Z.ones_spec_high by lia. apply andb_false_r.
    + split; [lia|]. change (Z.ones 0) with 0. apply Z.land_0_r.
Qed.
(* [comment removed for export] *)
Lemma known_low : forall x k0 k1 M, Z.land x k0 = 0 -> Z.land x k1 = k1 -> Z.land (Z.lor k0 k1) M = M ->
  Z.land x M = Z.land k1 M.
Proof.
  intros x k0 k1 M H0 H1 HM. apply Z.bits_inj'. intros n Hn. tb H0 n. tb H1 n. tb HM n.
  rewrite !Z.land_spec. bcases.
Qed.
Lemma land_sub_mask : forall m a b, Z.land m a = a -> Z.land (Z.land m b) a = Z.land b a.
Proof. intros m a b H. apply Z.bits_inj'. intros n Hn. tb H n. rewrite !Z.land_spec. bcases. Qed.
(* [comment removed for export] *)
Lemma lowbits_gam : forall w M, Z.land w (Z.land w M) = Z.land w M /\ Z.land w (Z.lxor M (Z.land w M)) = 0.
Proof.
  intros w M. split; apply Z.bits_inj'; intros n Hn; rewrite ?Z.land_spec, ?Z.lxor_spec, ?Z.land_spec, ?Z.bits_0; bcases.
Qed.

Definition kmask (A : av) : Z := Z.lor (ak0 A) (ak1 A).
Definition lowj (A B : av) : Z := lowcnt 64 (Z.land (kmask A) (kmask B)).
Lemma lowj_spec : forall A B x y, gam A x -> gam B y ->
  let j := lowj A B in 0 <= j <= 64 /\ x mod 2 ^ j = ak1 A mod 2 ^ j /\ y mod 2 ^ j = ak1 B mod 2 ^ j.
Proof.
  intros A B x y (_ & _ & A0 & A1) (_ & _ & B0 & B1) j.
  destruct (lowcnt_spec 64 (Z.land (kmask A) (kmask B))) as [Hj HM]. fold (lowj A B) in Hj, HM. fold j in Hj, HM.
  split; [exact Hj|]. rewrite <- !Z.land_ones by lia.
  unfold kmask in HM.
  split; (eapply known_low; [eassumption|eassumption|]);
    (apply Z.bits_inj'; intros n Hn; tb HM n; rewrite !Z.land_spec, ?Z.lor_spec; rewrite ?Z.lor_spec in Hb; bcases).
Qed.

(* [comment removed for export] *)
Definition lowk1 (j c : Z) : Z := Z.land c (Z.ones j).
Definition lowk0 (j c : Z) : Z := Z.lxor (Z.ones j) (lowk1 j c).
Lemma lowk_gam : forall j c w, 0 <= j -> w mod 2 ^ j = c mod 2 ^ j ->
  Z.land w (lowk0 j c) = 0 /\ Z.land w (lowk1 j c) = lowk1 j c.
Proof.
  intros j c w Hj E. unfold lowk0, lowk1. rewrite <- !Z.land_ones in E by lia. rewrite <- E.
  destruct (lowbits_gam w (Z.ones j)) as [Q1 Q2]. split; assumption.
Qed.
Lemma mod_mod_pow : forall a j, 0 <= j <= 64 -> (a mod two64) mod 2 ^ j = a mod 2 ^ j.
Proof.
  intros a j Hj. symmetry. apply Znumtheory.Zmod_div_mod.
  - apply Z.pow_pos_nonneg; lia.
  - exact two64_pos.
  - exists (2 ^ (64 - j)). rewrite two64_eq, <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma land64_mod : forall z, land64 z = z mod two64.
Proof.
  intros z. unfold land64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:E.
  - apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. symmetry. apply Z.mod_small. lia.
  - unfold ones64z. rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma wrap64_mod : forall z, wrap64 z = z mod two64.
Proof.
  intros z. unfold wrap64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. symmetry. apply Z.mod_small. lia.
Qed.
Lemma mod64_range : forall z, 0 <= z mod two64 < two64.
Proof. intros z. apply Z.mod_pos_bound. exact two64_pos. Qed.
Lemma wrap64_id : forall z, 0 <= z < two64 -> wrap64 z = z.
Proof. intros z Hz. rewrite wrap64_mod. apply Z.mod_small. exact Hz. Qed.
Lemma zadd_mod : forall x y, 0 <= x < two64 -> 0 <= y < two64 -> zfast ALU_ADD x y = (x + y) mod two64.
Proof.
  intros x y Hx Hy. cbn [zfast]. destruct (Z.ltb (x + y) two64) eqn:E.
  - apply Z.ltb_lt in E. symmetry. apply Z.mod_small. lia.
  - apply Z.ltb_ge in E. apply Z.mod_unique with (q := 1); lia.
Qed.
Lemma zsub_mod : forall x y, 0 <= x < two64 -> 0 <= y < two64 -> zfast ALU_SUB x y = (x - y) mod two64.
Proof.
  intros x y Hx Hy. cbn [zfast]. destruct (Z.leb 0 (x - y)) eqn:E.
  - apply Z.leb_le in E. symmetry. apply Z.mod_small. lia.
  - apply Z.leb_gt in E. apply Z.mod_unique with (q := -1); lia.
Qed.

(* [comment removed for export] *)
Lemma mod_iv_small : forall t lo hi, lo <= t <= hi -> 0 <= t < two64 -> lo <= t mod two64 <= hi.
Proof. intros t lo hi H H0. rewrite Z.mod_small by exact H0. exact H. Qed.
Lemma mod_iv_wrap : forall t lo hi, lo <= t <= hi -> two64 <= lo -> t < 2 * two64 -> lo - two64 <= t mod two64 <= hi - two64.
Proof.
  intros t lo hi H H0 H1. assert (E : t mod two64 = t - two64) by (symmetry; apply Z.mod_unique with (q := 1); lia).
  rewrite E. lia.
Qed.
Lemma mod_iv_neg : forall t lo hi, lo <= t <= hi -> hi < 0 -> - two64 <= t -> lo + two64 <= t mod two64 <= hi + two64.
Proof.
  intros t lo hi H H0 H1. assert (E : t mod two64 = t + two64) by (symmetry; apply Z.mod_unique with (q := -1); lia).
  rewrite E. lia.
Qed.
Lemma mod_iv_full : forall t, 0 <= t mod two64 <= ones64.
Proof. intros t. pose proof (mod64_range t). rewrite ones64_eq. lia. Qed.

(* [comment removed for export] *)
Definition a_add (A B : av) : option av :=
  let lo := alo A + alo B in let hi := ahi A + ahi B in
  let j := lowj A B in let c := ak1 A + ak1 B in
  if Z.ltb hi two64 then reduce lo hi (lowk0 j c) (lowk1 j c)
  else if Z.leb two64 lo then reduce (lo - two64) (hi - two64) (lowk0 j c) (lowk1 j c)
  else reduce 0 ones64 (lowk0 j c) (lowk1 j c).
Lemma a_add_sound : forall A B C x y, gam A x -> gam B y -> a_add A B = Some C -> gam C (zfast ALU_ADD x y).
Proof.
  intros A B C x y GA GB. destruct (lowj_spec A B x y GA GB) as (Hj & Ex & Ey).
  destruct GA as (Hx & Ix & _ & _). destruct GB as (Hy & Iy & _ & _).
  rewrite (zadd_mod x y Hx Hy).
  assert (Hm : ((x + y) mod two64) mod 2 ^ lowj A B = (ak1 A + ak1 B) mod 2 ^ lowj A B).
  { rewrite mod_mod_pow by exact Hj. rewrite Zplus_mod, Ex, Ey, <- Zplus_mod. reflexivity. }
  destruct (lowk_gam _ _ _ (proj1 Hj) Hm) as [K0 K1]. clear Hm Ex Ey Hj.
  pose proof (mod64_range (x + y)) as Hw.
  unfold a_add. destruct (Z.ltb (ahi A + ahi B) two64) eqn:E1.
  - apply Z.ltb_lt in E1. apply reduce_sound; try assumption. clear K0 K1 Hw. apply mod_iv_small; lia.
  - apply Z.ltb_ge in E1. destruct (Z.leb two64 (alo A + alo B)) eqn:E2.
    + apply Z.leb_le in E2. apply reduce_sound; try assumption. clear K0 K1 Hw. apply mod_iv_wrap; lia.
    + apply reduce_sound; try assumption. apply mod_iv_full.
Qed.
Definition a_sub (A B : av) : option av :=
  let lo := alo A - ahi B in let hi := ahi A - alo B in
  let j := lowj A B in let c := ak1 A - ak1 B in
  if Z.leb 0 lo then reduce lo hi (lowk0 j c) (lowk1 j c)
  else if Z.ltb hi 0 then reduce (lo + two64) (hi + two64) (lowk0 j c) (lowk1 j c)
  else reduce 0 ones64 (lowk0 j c) (lowk1 j c).
Lemma a_sub_sound : forall A B C x y, gam A x -> gam B y -> a_sub A B = Some C -> gam C (zfast ALU_SUB x y).
Proof.
  intros A B C x y GA GB. destruct (lowj_spec A B x y GA GB) as (Hj & Ex & Ey).
  destruct GA as (Hx & Ix & _ & _). destruct GB as (Hy & Iy & _ & _).
  rewrite (zsub_mod x y Hx Hy).
  assert (Hm : ((x - y) mod two64) mod 2 ^ lowj A B = (ak1 A - ak1 B) mod 2 ^ lowj A B).
  { rewrite mod_mod_pow by exact Hj. rewrite Zminus_mod, Ex, Ey, <- Zminus_mod. reflexivity. }
  destruct (lowk_gam _ _ _ (proj1 Hj) Hm) as [K0 K1]. clear Hm Ex Ey Hj.
  pose proof (mod64_range (x - y)) as Hw.
  unfold a_sub. destruct (Z.leb 0 (alo A - ahi B)) eqn:E1.
  - apply Z.leb_le in E1. apply reduce_sound; try assumption. clear K0 K1 Hw. apply mod_iv_small; lia.
  - apply Z.leb_gt in E1. destruct (Z.ltb (ahi A - alo B) 0) eqn:E2.
    + apply Z.ltb_lt in E2. apply reduce_sound; try assumption. clear K0 K1 Hw. apply mod_iv_neg; lia.
    + apply reduce_sound; try assumption. apply mod_iv_full.
Qed.

(* [comment removed for export] *)
Definition tz (A : av) : Z := lowcnt 64 (ak0 A).
Lemma tz_spec : forall A x, gam A x -> 0 <= tz A <= 64 /\ (2 ^ tz A | x).
Proof.
  intros A x (_ & _ & A0 & _). destruct (lowcnt_spec 64 (ak0 A)) as [Ht HM]. fold (tz A) in Ht, HM.
  split; [exact Ht|]. apply Z.mod_divide; [apply Z.pow_nonzero; lia|].
  rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros n Hn. tb A0 n. tb HM n. rewrite Z.land_spec, Z.bits_0. bcases.
Qed.
Lemma mul_iv : forall x y la ha lb hb, 0 <= x -> 0 <= y -> la <= x <= ha -> lb <= y <= hb ->
  Z.max 0 la * Z.max 0 lb <= x * y <= ha * hb.
Proof. intros. split; apply Z.mul_le_mono_nonneg; lia. Qed.
Lemma pow_split_divide : forall a b t x' y', 0 <= a -> 0 <= b -> 0 <= t <= a + b ->
  (2 ^ t | (x' * 2 ^ a) * (y' * 2 ^ b)).
Proof.
  intros a b t x' y' Ha Hb Ht. exists (2 ^ (a + b - t) * (x' * y')).
  replace (2 ^ (a + b - t) * (x' * y') * 2 ^ t) with ((2 ^ (a + b - t) * 2 ^ t) * (x' * y')) by ring.
  rewrite <- Z.pow_add_r by lia. replace (a + b - t + t) with (a + b) by lia.
  rewrite Z.pow_add_r by lia. ring.
Qed.
Definition a_mul (A B : av) : option av :=
  let hi := ahi A * ahi B in
  let j := lowj A B in let c := ak1 A * ak1 B in
  let t := Z.min 64 (tz A + tz B) in
  let k0 := Z.lor (lowk0 j c) (Z.ones t) in
  if Z.ltb hi two64 then reduce (Z.max 0 (alo A) * Z.max 0 (alo B)) hi k0 (lowk1 j c) else reduce 0 ones64 k0 (lowk1 j c).
Lemma a_mul_sound : forall A B C x y, gam A x -> gam B y -> a_mul A B = Some C -> gam C (zfastm M_MUL x y).
Proof.
  intros A B C x y GA GB. destruct (lowj_spec A B x y GA GB) as (Hj & Ex & Ey).
  destruct (tz_spec A x GA) as [HtA [x' Dx]]. destruct (tz_spec B y GB) as [HtB [y' Dy]].
  destruct GA as (Hx & Ix & _ & _). destruct GB as (Hy & Iy & _ & _).
  cbn [zfastm]. rewrite land64_mod.
  assert (Hm : ((x * y) mod two64) mod 2 ^ lowj A B = (ak1 A * ak1 B) mod 2 ^ lowj A B).
  { rewrite mod_mod_pow by exact Hj. rewrite Zmult_mod, Ex, Ey, <- Zmult_mod. reflexivity. }
  destruct (lowk_gam _ _ _ (proj1 Hj) Hm) as [K0 K1]. clear Hm Ex Ey Hj.
  set (t := Z.min 64 (tz A + tz B)).
  assert (Ht : 0 <= t <= 64) by (unfold t; lia).
  assert (Kt : Z.land ((x * y) mod two64) (Z.ones t) = 0).
  { rewrite Z.land_ones by lia. rewrite mod_mod_pow by exact Ht.
    apply Z.mod_divide; [apply Z.pow_nonzero; lia|]. rewrite Dx, Dy. apply pow_split_divide; unfold t; lia. }
  assert (K0' : Z.land ((x * y) mod two64) (Z.lor (lowk0 (lowj A B) (ak1 A * ak1 B)) (Z.ones t)) = 0).
  { rewrite Z.land_lor_distr_r, K0, Kt. reflexivity. }
  pose proof (mod64_range (x * y)) as Hw.
  pose proof (mul_iv x y _ _ _ _ (proj1 Hx) (proj1 Hy) Ix Iy) as Hi.
  unfold a_mul. fold t. destruct (Z.ltb (ahi A * ahi B) two64) eqn:E1.
  - apply Z.ltb_lt in E1. apply reduce_sound; try assumption. clear K0 K1 Kt K0' Hw Dx Dy.
    apply mod_iv_small; [exact Hi|]. split; [apply Z.mul_nonneg_nonneg; lia|lia].
  - apply reduce_sound; try assumption. apply mod_iv_full.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mod_block : forall a x b p, 0 < p -> a <= x <= b -> a / p = b / p -> a mod p <= x mod p <= b mod p.
Proof.
  intros a x b p Hp Hx E.
  assert (Ex : x / p = a / p).
  { pose proof (Z.div_le_mono a x p Hp (proj1 Hx)). pose proof (Z.div_le_mono x b p Hp (proj2 Hx)). lia. }
  rewrite !Z.mod_eq by lia. rewrite Ex, <- E. set (t := p * (a / p)). lia.
Qed.
Definition pt (A : av) : option Z := if Z.eqb (alo A) (ahi A) then Some (alo A) else None.
Lemma pt_gam : forall A x c, gam A x -> pt A = Some c -> x = c.
Proof.
  intros A x c (_ & Ix & _ & _) H. unfold pt in H. destruct (Z.eqb (alo A) (ahi A)) eqn:E; [|discriminate].
  injection H as <-. apply Z.eqb_eq in E. lia.
Qed.
Definition lowmask_k (m : Z) : option Z := let k := Z.log2 (m + 1) in if Z.eqb m (Z.ones k) then Some k else None.
(* [comment removed for export] *)
Definition mask_iv (A : av) (m : Z) : option (Z * Z) :=
  match lowmask_k m with
  | Some k => if (if Z.leb 0 (alo A) then Z.eqb (Z.shiftr (alo A) k) (Z.shiftr (ahi A) k) else false)
              then Some (Z.land (alo A) m, Z.land (ahi A) m) else None
  | None => None
  end.
Lemma mask_iv_sound : forall A m x l h, gam A x -> mask_iv A m = Some (l, h) -> l <= Z.land x m <= h.
Proof.
  intros A m x l h (Hx & Ix & _ & _) H. unfold mask_iv, lowmask_k in H.
  destruct (Z.eqb m (Z.ones (Z.log2 (m + 1)))) eqn:Em; [|discriminate]. apply Z.eqb_eq in Em.
  set (k := Z.log2 (m + 1)) in *. assert (Hk : 0 <= k) by apply Z.log2_nonneg.
  destruct (Z.leb 0 (alo A)) eqn:E0; [|discriminate]. destruct (Z.eqb (Z.shiftr (alo A) k) (Z.shiftr (ahi A) k)) eqn:E1; [|discriminate].
  injection H as <- <-. apply Z.eqb_eq in E1. rewrite !Z.shiftr_div_pow2 in E1 by exact Hk.
  rewrite Em, !Z.land_ones by exact Hk. apply mod_block; [apply Z.pow_pos_nonneg; lia|exact Ix|exact E1].
Qed.
Definition and_iv (A B : av) : Z * Z :=
  match (match pt B with Some m => mask_iv A m | None => None end) with
  | Some r => r
  | None => match (match pt A with Some m => mask_iv B m | None => None end) with
            | Some r => r
            | None => (0, Z.min (ahi A) (ahi B))
            end
  end.
Definition a_and (A B : av) : option av :=
  let r := and_iv A B in reduce (fst r) (snd r) (Z.lor (ak0 A) (ak0 B)) (Z.land (ak1 A) (ak1 B)).
Lemma a_and_sound : forall A B C x y, gam A x -> gam B y -> a_and A B = Some C -> gam C (zfast ALU_AND x y).
Proof.
  intros A B C x y GA GB. cbn [zfast]. unfold a_and.
  assert (Hi : fst (and_iv A B) <= Z.land x y <= snd (and_iv A B)).
  { unfold and_iv.
    destruct (match pt B with Some m => mask_iv A m | None => None end) as [[l h]|] eqn:E1.
    - destruct (pt B) as [m|] eqn:EB; [|discriminate]. rewrite (pt_gam B y m GB EB). exact (mask_iv_sound A m x l h GA E1).
    - destruct (match pt A with Some m => mask_iv B m | None => None end) as [[l h]|] eqn:E2.
      + destruct (pt A) as [m|] eqn:EA; [|discriminate]. rewrite (pt_gam A x m GA EA), Z.land_comm.
        exact (mask_iv_sound B m y l h GB E2).
      + cbn [fst snd]. destruct GA as (Hx & Ix & _ & _). destruct GB as (Hy & Iy & _ & _).
        pose proof (land_le_l x y (proj1 Hx)). pose proof (land_le_l y x (proj1 Hy)) as H2. rewrite Z.land_comm in H2.
        pose proof (land_nonneg_l x y (proj1 Hx)). lia. }
  destruct GA as (Hx & Ix & A0 & A1). destruct GB as (Hy & Iy & B0 & B1).
  pose proof (land_le_l x y (proj1 Hx)). pose proof (land_nonneg_l x y (proj1 Hx)).
  apply reduce_sound; try lia; try exact Hi.
  - apply Z.bits_inj'. intros n Hn. tb A0 n. tb B0 n. rewrite !Z.land_spec, Z.lor_spec, Z.bits_0. bcases.
  - apply Z.bits_inj'. intros n Hn. tb A1 n. tb B1 n. rewrite !Z.land_spec. bcases.
Qed.
Lemma lor_ge_l : forall x y, 0 <= x -> 0 <= y -> x <= Z.lor x y /\ y <= Z.lor x y.
Proof.
  intros x y Hx Hy. pose proof (Z.add_lor_land x y). pose proof (land_le_l x y Hx). pose proof (land_le_l y x Hy) as H2.
  rewrite Z.land_comm in H2. lia.
Qed.
Definition a_or (A B : av) : option av :=
  reduce (Z.max (alo A) (alo B)) ones64 (Z.land (ak0 A) (ak0 B)) (Z.lor (ak1 A) (ak1 B)).
Lemma a_or_sound : forall A B C x y, gam A x -> gam B y -> a_or A B = Some C -> gam C (zfast ALU_OR x y).
Proof.
  intros A B C x y (Hx & Ix & A0 & A1) (Hy & Iy & B0 & B1). cbn [zfast]. unfold a_or.
  pose proof (lor_lt_two64 x y Hx Hy). pose proof (lor_ge_l x y (proj1 Hx) (proj1 Hy)).
  apply reduce_sound; try (rewrite ?ones64_eq; lia).
  - apply Z.bits_inj'. intros n Hn. tb A0 n. tb B0 n. rewrite !Z.land_spec, Z.lor_spec, Z.bits_0. bcases.
  - apply Z.bits_inj'. intros n Hn. tb A1 n. tb B1 n. rewrite Z.land_spec, !Z.lor_spec. bcases.
Qed.
Definition a_xor (A B : av) : option av :=
  reduce 0 ones64 (Z.lor (Z.land (ak0 A) (ak0 B)) (Z.land (ak1 A) (ak1 B)))
                  (Z.lor (Z.land (ak1 A) (ak0 B)) (Z.land (ak0 A) (ak1 B))).
Lemma a_xor_sound : forall A B C x y, gam A x -> gam B y -> a_xor A B = Some C -> gam C (zfast ALU_XOR x y).
Proof.
  intros A B C x y (Hx & Ix & A0 & A1) (Hy & Iy & B0 & B1). cbn [zfast]. unfold a_xor.
  pose proof (lxor_lt_two64 x y Hx Hy).
  apply reduce_sound; try (rewrite ?ones64_eq; lia).
  - apply Z.bits_inj'. intros n Hn. tb A0 n. tb B0 n. tb A1 n. tb B1 n.
    rewrite !Z.land_spec, !Z.lor_spec, !Z.land_spec, Z.lxor_spec, Z.bits_0. bcases.
  - apply Z.bits_inj'. intros n Hn. tb A0 n. tb B0 n. tb A1 n. tb B1 n.
    rewrite !Z.land_spec, !Z.lor_spec, !Z.land_spec, Z.lxor_spec. bcases.
Qed.

(* [comment removed for export] *)
Lemma known_point : forall B y, gam B y -> Z.eqb (alo B) (ahi B) = true -> y = alo B.
Proof. intros B y (_ & Iy & _ & _) E. apply Z.eqb_eq in E. lia. Qed.
Lemma shamt_nonneg : forall y, 0 <= Z.land y 63.
Proof. intros y. apply Z.land_nonneg. right. lia. Qed.
Definition a_srl (A B : av) : option av :=
  if Z.eqb (alo B) (ahi B) then
    let sh := Z.land (alo B) 63 in
    reduce (Z.shiftr (alo A) sh) (Z.shiftr (ahi A) sh) (Z.shiftr (ak0 A) sh) (Z.shiftr (ak1 A) sh)
  else None.
Lemma shiftr_mono : forall a b n, 0 <= n -> a <= b -> Z.shiftr a n <= Z.shiftr b n.
Proof. intros a b n Hn H. rewrite !Z.shiftr_div_pow2 by exact Hn. apply Z.div_le_mono; [apply Z.pow_pos_nonneg; lia|exact H]. Qed.
Lemma shiftr_range : forall x n, 0 <= n -> 0 <= x < two64 -> 0 <= Z.shiftr x n < two64.
Proof.
  intros x n Hn Hx. split; [apply Z.shiftr_nonneg; lia|].
  pose proof (shiftr_mono 0 x n Hn (proj1 Hx)). rewrite Z.shiftr_div_pow2 by exact Hn.
  assert (0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
  assert (x / 2 ^ n <= x) by (apply Z.div_le_upper_bound; [lia|nia]). lia.
Qed.
Lemma a_srl_sound : forall A B C x y, gam A x -> gam B y -> a_srl A B = Some C -> gam C (zfast ALU_SRL x y).
Proof.
  intros A B C x y GA GB. unfold a_srl. destruct (Z.eqb (alo B) (ahi B)) eqn:E; [|discriminate].
  rewrite <- (known_point B y GB E). destruct GA as (Hx & Ix & A0 & A1). cbn [zfast].
  pose proof (shamt_nonneg y) as Hs. set (sh := Z.land y 63) in *.
  apply reduce_sound.
  - apply shiftr_range; assumption.
  - split; apply shiftr_mono; lia.
  - rewrite <- Z.shiftr_land, A0. apply Z.shiftr_0_l.
  - rewrite <- Z.shiftr_land, A1. reflexivity.
Qed.
Definition a_sll (A B : av) : option av :=
  if Z.eqb (alo B) (ahi B) then
    let sh := Z.land (alo B) 63 in
    let k0 := Z.lor (Z.land (Z.shiftl (ak0 A) sh) ones64) (Z.ones sh) in
    let k1 := Z.land (Z.shiftl (ak1 A) sh) ones64 in
    let hi := Z.shiftl (ahi A) sh in
    if Z.ltb hi two64 then reduce (Z.shiftl (alo A) sh) hi k0 k1 else reduce 0 ones64 k0 k1
  else None.
Lemma shiftl_mono : forall a b n, 0 <= n -> a <= b -> Z.shiftl a n <= Z.shiftl b n.
Proof. intros a b n Hn H. rewrite !Z.shiftl_mul_pow2 by exact Hn. apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; lia|exact H]. Qed.
Lemma a_sll_sound : forall A B C x y, gam A x -> gam B y -> a_sll A B = Some C -> gam C (zfast ALU_SLL x y).
Proof.
  intros A B C x y GA GB. unfold a_sll. destruct (Z.eqb (alo B) (ahi B)) eqn:E; [|discriminate].
  rewrite <- (known_point B y GB E). destruct GA as (Hx & Ix & A0 & A1). cbn [zfast].
  pose proof (shamt_nonneg y) as Hs. set (sh := Z.land y 63) in *. rewrite land64_mod.
  assert (Ew : Z.shiftl x sh mod two64 = Z.land (Z.shiftl x sh) ones64) by (unfold ones64; rewrite Z.land_ones by lia; reflexivity).
  assert (K0 : Z.land (Z.shiftl x sh mod two64) (Z.lor (Z.land (Z.shiftl (ak0 A) sh) ones64) (Z.ones sh)) = 0).
  { rewrite Ew. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.lor_spec, Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n sh) as [Hl|Hg].
    - rewrite (Z.shiftl_spec_low x) by lia. reflexivity.
    - rewrite !Z.shiftl_spec by lia. rewrite Z.ones_spec_high by lia. tb A0 (n - sh). bcases. }
  assert (K1 : Z.land (Z.shiftl x sh mod two64) (Z.land (Z.shiftl (ak1 A) sh) ones64) = Z.land (Z.shiftl (ak1 A) sh) ones64).
  { rewrite Ew. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
    destruct (Z.lt_ge_cases n sh) as [Hl|Hg].
    - rewrite !Z.shiftl_spec_low by lia. reflexivity.
    - rewrite !Z.shiftl_spec by lia. tb A1 (n - sh). bcases. }
  pose proof (mod64_range (Z.shiftl x sh)) as Hw.
  destruct (Z.ltb (Z.shiftl (ahi A) sh) two64) eqn:E1.
  - apply Z.ltb_lt in E1. apply reduce_sound; try assumption. clear K0 K1 Ew Hw.
    pose proof (shiftl_mono (alo A) x sh Hs (proj1 Ix)). pose proof (shiftl_mono x (ahi A) sh Hs (proj2 Ix)).
    assert (0 <= Z.shiftl x sh) by (apply Z.shiftl_nonneg; lia).
    apply mod_iv_small; lia.
  - apply reduce_sound; try assumption. apply mod_iv_full.
Qed.
Definition a_sltu (A B : av) : option av :=
  if Z.ltb (ahi A) (alo B) then Some (cst 1)
  else if Z.leb (ahi B) (alo A) then Some (cst 0)
  else reduce 0 1 (ones64 - 1) 0.
Lemma a_sltu_sound : forall A B C x y, gam A x -> gam B y -> a_sltu A B = Some C -> gam C (zfast ALU_SLTU x y).
Proof.
  intros A B C x y (Hx & Ix & _ & _) (Hy & Iy & _ & _). cbn [zfast]. unfold a_sltu.
  assert (R0 : 0 <= 0 < two64) by (rewrite two64_eq; lia). assert (R1 : 0 <= 1 < two64) by (rewrite two64_eq; lia).
  destruct (Z.ltb (ahi A) (alo B)) eqn:E1.
  - apply Z.ltb_lt in E1. intros Q. injection Q as <-. assert (E : Z.ltb x y = true) by (apply Z.ltb_lt; lia).
    rewrite E. apply cst_gam. exact R1.
  - destruct (Z.leb (ahi B) (alo A)) eqn:E2.
    + apply Z.leb_le in E2. intros Q. injection Q as <-. assert (E : Z.ltb x y = false) by (apply Z.ltb_ge; lia).
      rewrite E. apply cst_gam. exact R0.
    + destruct (Z.ltb x y); (apply reduce_sound; [assumption|lia|reflexivity|reflexivity]).
Qed.

(* [comment removed for export] *)
Definition aop (op : aluop) (A B : av) : option av :=
  match op with
  | ALU_ADD => a_add A B | ALU_SUB => a_sub A B | ALU_AND => a_and A B | ALU_OR => a_or A B
  | ALU_XOR => a_xor A B | ALU_SRL => a_srl A B | ALU_SLL => a_sll A B | ALU_SLTU => a_sltu A B
  | _ => None
  end.
Lemma aop_sound : forall op A B C x y, gam A x -> gam B y -> aop op A B = Some C -> gam C (zfast op x y).
Proof.
  intros op A B C x y GA GB H. destruct op; cbn [aop] in H; try discriminate;
    eauto using a_add_sound, a_sub_sound, a_and_sound, a_or_sound, a_xor_sound, a_srl_sound, a_sll_sound, a_sltu_sound.
Qed.
(* [comment removed for export] *)
Definition in64b (w : Z) : bool := if Z.leb 0 w then Z.ltb w two64 else false.
Lemma in64b_ok : forall w, in64b w = true -> 0 <= w < two64.
Proof. intros w H. unfold in64b in H. destruct (Z.leb 0 w) eqn:E; [|discriminate]. apply Z.leb_le in E. apply Z.ltb_lt in H. lia. Qed.
Definition fold2 (f : Z -> Z -> Z) (A B : av) : option av :=
  match pt A with
  | Some x => match pt B with
              | Some y => let w := f x y in if in64b w then Some (cst w) else None
              | None => None
              end
  | None => None
  end.
Lemma fold2_sound : forall f A B C x y, gam A x -> gam B y -> fold2 f A B = Some C -> gam C (f x y).
Proof.
  intros f A B C x y GA GB H. unfold fold2 in H.
  destruct (pt A) as [x0|] eqn:EA; [|discriminate]. destruct (pt B) as [y0|] eqn:EB; [|discriminate].
  rewrite (pt_gam A x x0 GA EA), (pt_gam B y y0 GB EB).
  destruct (in64b (f x0 y0)) eqn:Ew; [|discriminate]. injection H as <-. apply cst_gam. apply in64b_ok. exact Ew.
Qed.
Definition fold1 (f : Z -> Z) (A : av) : option av :=
  match pt A with
  | Some x => let w := f x in if in64b w then Some (cst w) else None
  | None => None
  end.
Lemma fold1_sound : forall f A C x, gam A x -> fold1 f A = Some C -> gam C (f x).
Proof.
  intros f A C x GA H. unfold fold1 in H. destruct (pt A) as [x0|] eqn:EA; [|discriminate].
  rewrite (pt_gam A x x0 GA EA). destruct (in64b (f x0)) eqn:Ew; [|discriminate]. injection H as <-.
  apply cst_gam. apply in64b_ok. exact Ew.
Qed.
Definition c_alu (op : aluop) (A B : av) : option av :=
  match fold2 (zfast op) A B with Some C => Some C | None => aop op A B end.
Lemma c_alu_sound : forall op A B C x y, gam A x -> gam B y -> c_alu op A B = Some C -> gam C (zfast op x y).
Proof.
  intros op A B C x y GA GB H. unfold c_alu in H. destruct (fold2 (zfast op) A B) as [C0|] eqn:E.
  - injection H as <-. eapply fold2_sound; eassumption.
  - eapply aop_sound; eassumption.
Qed.
Definition c_md (op : mulop) (A B : av) : option av :=
  match fold2 (zfastm op) A B with
  | Some C => Some C
  | None => match op with M_MUL => a_mul A B | _ => None end
  end.
Lemma c_md_sound : forall op A B C x y, gam A x -> gam B y -> c_md op A B = Some C -> gam C (zfastm op x y).
Proof.
  intros op A B C x y GA GB H. unfold c_md in H. destruct (fold2 (zfastm op) A B) as [C0|] eqn:E.
  - injection H as <-. eapply fold2_sound; eassumption.
  - destruct op; try discriminate. eapply a_mul_sound; eassumption.
Qed.
Fixpoint kbv (s : expr) (P : av) (e : expr) {struct e} : option av :=
  if eqbL e s then Some P else
  match e with
  | ELit w => Some (cst (wrap64 w))
  | EVar _ => None
  | EAlu op a b =>
      match kbv s P a with
      | Some A => match kbv s P b with Some B => c_alu op A B | None => None end
      | None => None
      end
  | EAluw op a b =>
      match kbv s P a with
      | Some A => match kbv s P b with Some B => fold2 (zfastw op) A B | None => None end
      | None => None
      end
  | EMd op a b =>
      match kbv s P a with
      | Some A => match kbv s P b with Some B => c_md op A B | None => None end
      | None => None
      end
  | EMdw op a b =>
      match kbv s P a with
      | Some A => match kbv s P b with Some B => fold2 (zmdw op) A B | None => None end
      | None => None
      end
  | EExt sx l n a =>
      match kbv s P a with
      | Some A => fold1 (zext_fast sx l n) A
      | None => None
      end
  | EBlob _ _ _ _ => None
  end.

Section Sound.
Variables (s : expr) (P : av) (lo hi : Z).
Hypothesis P_ok : forall z, lo <= z <= hi -> gam P z.
Lemma kbv_sound : forall e A, kbv s P e = Some A -> forall z, lo <= z <= hi -> exists w, evalS s z e = Some w /\ gam A w.
Proof.
  induction e as [w|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx l n a IHa|sx k i n];
    intros A HA z Hz; cbn [kbv] in HA; cbn [evalS]; rewrite eqbL_eq in HA;
    match goal with |- context [expr_eqb ?e0 s] => destruct (expr_eqb e0 s) end;
    try (injection HA as <-; exists z; split; [reflexivity|apply P_ok; exact Hz]); try discriminate.
  - injection HA as <-. eexists. split; [reflexivity|]. apply cst_gam. rewrite wrap64_mod. apply mod64_range.
  - destruct (kbv s P a) as [A1|] eqn:Ka; [|discriminate]. destruct (kbv s P b) as [B1|] eqn:Kb; [|discriminate].
    destruct (IHa A1 eq_refl z Hz) as (x & Ea & Ga). destruct (IHb B1 eq_refl z Hz) as (y & Eb & Gb).
    rewrite Ea, Eb. eexists. split; [reflexivity|]. eapply c_alu_sound; eassumption.
  - destruct (kbv s P a) as [A1|] eqn:Ka; [|discriminate]. destruct (kbv s P b) as [B1|] eqn:Kb; [|discriminate].
    destruct (IHa A1 eq_refl z Hz) as (x & Ea & Ga). destruct (IHb B1 eq_refl z Hz) as (y & Eb & Gb).
    rewrite Ea, Eb. eexists. split; [reflexivity|]. eapply fold2_sound; eassumption.
  - destruct (kbv s P a) as [A1|] eqn:Ka; [|discriminate]. destruct (kbv s P b) as [B1|] eqn:Kb; [|discriminate].
    destruct (IHa A1 eq_refl z Hz) as (x & Ea & Ga). destruct (IHb B1 eq_refl z Hz) as (y & Eb & Gb).
    rewrite Ea, Eb. eexists. split; [reflexivity|]. eapply c_md_sound; eassumption.
  - destruct (kbv s P a) as [A1|] eqn:Ka; [|discriminate]. destruct (kbv s P b) as [B1|] eqn:Kb; [|discriminate].
    destruct (IHa A1 eq_refl z Hz) as (x & Ea & Ga). destruct (IHb B1 eq_refl z Hz) as (y & Eb & Gb).
    rewrite Ea, Eb. eexists. split; [reflexivity|]. eapply fold2_sound; eassumption.
  - destruct (kbv s P a) as [A1|] eqn:Ka; [|discriminate].
    destruct (IHa A1 eq_refl z Hz) as (x & Ea & Ga).
    rewrite Ea. eexists. split; [reflexivity|]. eapply fold1_sound; eassumption.
Qed.
End Sound.

(* [comment removed for export] *)
Definition kb_mid (s : expr) (lo hi : Z) (e : expr) : option Z :=
  match reduce lo hi 0 0 with
  | Some P => match kbv s P e with
              | Some A => if Z.eqb (alo A) (ahi A) then Some (alo A) else None
              | None => None
              end
  | None => None
  end.
Lemma kb_mid_sound : forall s lo hi e v, kb_mid s lo hi e = Some v -> 0 <= lo -> hi < two64 ->
  forall z, lo <= z <= hi -> evalS s z e = Some v.
Proof.
  intros s lo hi e v H Hlo Hhi z Hz. unfold kb_mid in H.
  destruct (reduce lo hi 0 0) as [P|] eqn:EP; [|discriminate].
  destruct (kbv s P e) as [A|] eqn:EA; [|discriminate].
  destruct (Z.eqb (alo A) (ahi A)) eqn:Eq; [|discriminate]. injection H as <-. apply Z.eqb_eq in Eq.
  assert (P_ok : forall z0, lo <= z0 <= hi -> gam P z0).
  { intros z0 Hz0. eapply reduce_sound; [split; lia|exact Hz0|apply Z.land_0_r|apply Z.land_0_r|exact EP]. }
  destruct (kbv_sound s P lo hi P_ok e A EA z Hz) as (w & Ew & _ & Iw & _). rewrite Ew. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma sweep_all : forall s e v cnt l, (forall z, l <= z < l + Z.of_nat cnt -> evalS s (wrap64 z) e = Some v) ->
  all_eval_toS s e v l cnt = true.
Proof.
  intros s e v. induction cnt as [|c IH]; intros l H; [reflexivity|]. cbn [all_eval_toS].
  rewrite (H l) by lia. rewrite Z.eqb_refl. apply IH. intros z Hz. apply H. lia.
Qed.
(* [comment removed for export] *)
Lemma kb_peel_sound : forall s lo hi e v, 0 <= lo -> lo <= hi -> hi < 2 ^ 64 ->
  evalS s (wrap64 lo) e = Some v -> probeS s e v hi = true -> kb_mid s (lo + 1) (hi - 1) e = Some v ->
  all_eval_toS s e v lo (Z.to_nat (hi - lo + 1)) = true.
Proof.
  intros s lo hi e v Hlo Hle Hhi El Ph Hm. rewrite <- two64_eq in Hhi. apply sweep_all. intros z Hz.
  rewrite Z2Nat.id in Hz by lia.
  destruct (Z.eq_dec z lo) as [->|Nl]; [exact El|].
  destruct (Z.eq_dec z hi) as [->|Nh].
  - unfold probeS in Ph. destruct (evalS s (wrap64 hi) e) as [w|]; [|discriminate]. apply Z.eqb_eq in Ph. subst w. reflexivity.
  - rewrite wrap64_id by lia. apply (kb_mid_sound s (lo + 1) (hi - 1) e v Hm); lia.
Qed.
(* [comment removed for export] *)
Definition cand : Type := (expr * Z)%type.
Definition cand_of (e : expr) (r : option av) : option cand :=
  match r with
  | Some A => if Z.ltb 0 (alo A) then
                (if Z.eqb (Z.log2 (alo A)) (Z.log2 (ahi A)) then None else Some (e, 2 ^ Z.log2 (ahi A)))
              else None
  | None => None
  end.
Definition arith_op (op : aluop) : bool :=
  match op with ALU_ADD | ALU_SUB | ALU_SRL | ALU_SLL => true | _ => false end.
Definition first_cand (a b c : option cand) : option cand :=
  match a with Some x => Some x | None => match b with Some x => Some x | None => c end end.
(* [comment removed for export] *)
Definition kbc2 (ra : option av * option cand) (rbf : unit -> option av * option cand)
                (comb : av -> av -> option av) (mkc : option av -> option cand) : option av * option cand :=
  match fst ra with
  | Some A => let rb := rbf tt in
              match fst rb with
              | Some B => let r := comb A B in (r, first_cand (snd ra) (snd rb) (mkc r))
              | None => (None, first_cand (snd ra) (snd rb) None)
              end
  | None => (None, snd ra)
  end.
Lemma kbc2_fst : forall ra rbf comb mkc,
  fst (kbc2 ra rbf comb mkc) = match fst ra with
                               | Some A => match fst (rbf tt) with Some B => comb A B | None => None end
                               | None => None
                               end.
Proof. intros ra rbf comb mkc. unfold kbc2. destruct (fst ra); [|reflexivity]. destruct (fst (rbf tt)); reflexivity. Qed.
Fixpoint kbc (s : expr) (P : av) (e : expr) {struct e} : option av * option cand :=
  if eqbL e s then (Some P, cand_of e (Some P)) else
  match e with
  | ELit w => (Some (cst (wrap64 w)), None)
  | EVar _ => (None, None)
  | EAlu op a b => kbc2 (kbc s P a) (fun _ => kbc s P b) (c_alu op) (fun r => if arith_op op then cand_of e r else None)
  | EAluw op a b => kbc2 (kbc s P a) (fun _ => kbc s P b) (fold2 (zfastw op)) (fun _ => None)
  | EMd op a b => kbc2 (kbc s P a) (fun _ => kbc s P b) (c_md op) (fun r => match op with M_MUL => cand_of e r | _ => None end)
  | EMdw op a b => kbc2 (kbc s P a) (fun _ => kbc s P b) (fold2 (zmdw op)) (fun _ => None)
  | EExt sx l n a => let ra := kbc s P a in
                     (match fst ra with Some A => fold1 (zext_fast sx l n) A | None => None end, snd ra)
  | EBlob _ _ _ _ => (None, None)
  end.
Lemma kbc_fst : forall s P e, fst (kbc s P e) = kbv s P e.
Proof.
  intros s P. induction e as [w|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx l n a IHa|sx k i n];
    cbn [kbc kbv]; match goal with |- context [eqbL ?e0 s] => destruct (eqbL e0 s) end; try reflexivity;
    try (rewrite kbc2_fst, IHa, IHb; reflexivity).
  cbn [fst]. rewrite IHa. reflexivity.
Qed.
(* [comment removed for export] *)
Definition kb_try (s : expr) (lo hi : Z) (e : expr) : option Z * option cand :=
  match reduce lo hi 0 0 with
  | Some P => let r := kbc s P e in
              (match fst r with
               | Some A => if Z.eqb (alo A) (ahi A) then Some (alo A) else None
               | None => None
               end, snd r)
  | None => (None, None)
  end.
Lemma kb_try_mid : forall s lo hi e, fst (kb_try s lo hi e) = kb_mid s lo hi e.
Proof.
  intros s lo hi e. unfold kb_try, kb_mid. destruct (reduce lo hi 0 0) as [P|]; [|reflexivity].
  cbn [fst]. rewrite kbc_fst. reflexivity.
Qed.
(* [comment removed for export] *)
Fixpoint bsearch (fuel : nat) (s g : expr) (T a b : Z) : Z :=
  match fuel with
  | O => b
  | S f => if Z.leb (b - a) 1 then b
           else let m := Z.div2 (a + b) in
                match evalS s m g with
                | Some w => if Z.leb T w then bsearch f s g T a m else bsearch f s g T m b
                | None => b
                end
  end.
Definition split_at (s : expr) (lo hi : Z) (c : cand) : option Z :=
  let '(g, T) := c in
  match evalS s lo g with
  | Some wl => match evalS s hi g with
               | Some wh => if (if Z.ltb wl T then Z.leb T wh else false) then Some (bsearch 64 s g T lo hi) else None
               | None => None
               end
  | None => None
  end.
Fixpoint kb_split (fuel : nat) (s : expr) (lo hi : Z) (e : expr) {struct fuel} : option Z :=
  let r := kb_try s lo hi e in
  match fst r with
  | Some v => Some v
  | None =>
      match fuel with
      | O => None
      | S f =>
          match snd r with
          | Some c =>
              match split_at s lo hi c with
              | Some z =>
                  if (if Z.ltb lo z then Z.leb z hi else false) then
                    match kb_split f s lo (z - 1) e with
                    | Some v1 => match kb_split f s z hi e with
                                 | Some v2 => if Z.eqb v1 v2 then Some v1 else None
                                 | None => None
                                 end
                    | None => None
                    end
                  else None
              | None => None
              end
          | None => None
          end
      end
  end.
Lemma kb_split_sound : forall fuel s e lo hi v, kb_split fuel s lo hi e = Some v -> 0 <= lo -> hi < two64 ->
  forall z, lo <= z <= hi -> evalS s z e = Some v.
Proof.
  induction fuel as [|f IH]; intros s e lo hi v H Hlo Hhi z Hz; cbn [kb_split] in H;
    rewrite kb_try_mid in H; destruct (kb_mid s lo hi e) as [v0|] eqn:E0;
    try (injection H as <-; apply (kb_mid_sound s lo hi e v0 E0 Hlo Hhi z Hz)); try discriminate.
  destruct (snd (kb_try s lo hi e)) as [c|]; [|discriminate].
  destruct (split_at s lo hi c) as [z0|]; [|discriminate].
  destruct (Z.ltb lo z0) eqn:E1; [|discriminate]. destruct (Z.leb z0 hi) eqn:E2; [|discriminate].
  apply Z.ltb_lt in E1. apply Z.leb_le in E2.
  destruct (kb_split f s lo (z0 - 1) e) as [v1|] eqn:K1; [|discriminate].
  destruct (kb_split f s z0 hi e) as [v2|] eqn:K2; [|discriminate].
  destruct (Z.eqb v1 v2) eqn:E3; [|discriminate]. injection H as <-. apply Z.eqb_eq in E3. subst v2.
  destruct (Z.lt_ge_cases z z0) as [Hl|Hg].
  - apply (IH s e lo (z0 - 1) v1 K1); lia.
  - apply (IH s e z0 hi v1 K2); lia.
Qed.

(* [comment removed for export] *)
Definition kb_const (s : expr) (lo hi : Z) (e : expr) : option Z := kb_split 3 s lo hi e.
Theorem kb_const_sound : forall s lo hi e v, kb_const s lo hi e = Some v -> 0 <= lo -> lo <= hi -> hi < 2 ^ 64 ->
  all_eval_toS s e v lo (Z.to_nat (hi - lo + 1)) = true.
Proof.
  intros s lo hi e v H Hlo Hle Hhi. rewrite <- two64_eq in Hhi. apply sweep_all. intros z Hz.
  rewrite Z2Nat.id in Hz by lia. rewrite wrap64_id by lia.
  apply (kb_split_sound 3 s e lo hi v H Hlo Hhi). lia.
Qed.

End KBF.
End Bootnws.

Module Boott1m.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From Stdlib Require PrimInt63 Uint63.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import PropExec AxSyioe AxSyclu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Boot1pr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Boot1pr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bootha0.Bootnws.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
(* [comment removed for export] *)
Module BXI.
Import PrimInt63.
Definition B61 : int := 2305843009213693952%uint63.
Definition B62 : int := 4611686018427387904%uint63.
Definition i0 : int := 0%uint63.
End BXI.
Module BASF.
Import AX2. Import AX2B.
Local Open Scope Z_scope.
Local Close Scope Z_scope.
(* [comment removed for export] *)
Fixpoint neqb4 (a b : nat) {struct a} : bool :=
  match a, b with
  | S (S (S (S a'))), S (S (S (S b'))) => neqb4 a' b'
  | _, _ => Nat.eqb a b
  end.
Lemma neqb4_eq : forall a b, neqb4 a b = Nat.eqb a b.
Proof.
  intros a. induction a as [a IH] using lt_wf_ind. intros b.
  destruct a as [|[|[|[|a']]]]; try reflexivity.
  destruct b as [|[|[|[|b']]]]; try reflexivity.
  cbn [neqb4 Nat.eqb]. apply IH. lia.
Qed.
Fixpoint expr_eqbF (x y : expr) : bool :=
  match x, y with
  | ELit a, ELit b => Z.eqb a b
  | EVar a, EVar b => neqb4 a b
  | EAlu o a b, EAlu o' a' b' => if aluop_eqb o o' then if expr_eqbF a a' then expr_eqbF b b' else false else false
  | EAluw o a b, EAluw o' a' b' => if aluop_eqb o o' then if expr_eqbF a a' then expr_eqbF b b' else false else false
  | EMd o a b, EMd o' a' b' => if mulop_eqb o o' then if expr_eqbF a a' then expr_eqbF b b' else false else false
  | EMdw o a b, EMdw o' a' b' => if mulop_eqb o o' then if expr_eqbF a a' then expr_eqbF b b' else false else false
  | EExt s l n a, EExt s' l' n' a' =>
      if Bool.eqb s s' then if neqb4 l l' then if neqb4 n n' then expr_eqbF a a' else false else false else false
  | EBlob s k i n, EBlob s' k' i' n' =>
      if Bool.eqb s s' then if neqb4 k k' then if Z.eqb i i' then neqb4 n n' else false else false else false
  | _, _ => false
  end.
Lemma expr_eqbF_eq : forall x y, expr_eqbF x y = expr_eqb x y.
Proof.
  induction x; destruct y; cbn [expr_eqbF expr_eqb]; rewrite ?neqb4_eq, ?IHx, ?IHx1, ?IHx2; try reflexivity;
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.
Lemma expr_eqbF_fe : expr_eqbF = expr_eqb.
Proof. apply functional_extensionality; intros x. apply functional_extensionality; intros y. apply expr_eqbF_eq. Qed.
Lemma expr_eqbF_refl : forall x, expr_eqbF x x = true.
Proof. intros x. rewrite expr_eqbF_eq. apply kx_expr_eqb_refl. Qed.
Lemma expr_eqbF_true : forall x y, expr_eqbF x y = true -> x = y.
Proof. intros x y H. rewrite expr_eqbF_eq in H. apply p_expr_eqb_eq. exact H. Qed.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Fixpoint find_rangeF (kn : list kentry) (e : expr) : option (Z * Z) :=
  match kn with
  | [] => None
  | KRange e' lo hi :: rest =>
      if expr_eqbF e e' then Some (lo, hi) else
      match e with
      | ELit _ => find_rangeF rest e
      | _ =>
        let '(v, c) := lit_strip e in
        let '(v', c') := lit_strip e' in
        if expr_eqbF v v' then
          let d := (c - c')%Z in
          if (if Z.leb 0 lo then if Z.leb lo hi then if Z.ltb hi two64 then if Z.leb 0 (lo + d) then Z.ltb (hi + d) two64 else false else false else false else false)
          then Some ((lo + d)%Z, (hi + d)%Z) else find_rangeF rest e
        else find_rangeF rest e
      end
  | _ :: rest => find_rangeF rest e
  end.
Lemma find_rangeF_eq : forall kn e, find_rangeF kn e = find_range kn e.
Proof.
  induction kn as [|K rest IH]; intros e; [reflexivity|]. cbn [find_rangeF find_range]. rewrite !IH.
  destruct K as [a w v|a l|a l k|lo hi|e' m|e' lo hi|a n|c1 m1 c2 m2|a l c|a l]; try reflexivity.
  rewrite expr_eqbF_eq. destruct (expr_eqb e e'); [reflexivity|].
  destruct e; try reflexivity;
    (match goal with |- context [lit_strip ?x] => destruct (lit_strip x) as [v0 c0] end;
     destruct (lit_strip e') as [v' c']; rewrite expr_eqbF_eq; destruct (expr_eqb v0 v'); [|reflexivity];
     change (2 ^ 64) with two64;
     destruct (Z.leb 0 lo); destruct (Z.leb lo hi); destruct (Z.ltb hi two64); destruct (Z.leb 0 (lo + (c0 - c'))); reflexivity).
Qed.
Definition find_rangeIF (ri : rindex) (e : expr) : option (Z * Z) := find_rangeF (ri_bucket ri (vkey_of e)) e.
Lemma find_rangeIF_eq : forall ri e, find_rangeIF ri e = find_rangeI ri e.
Proof. intros. unfold find_rangeIF, find_rangeI. apply find_rangeF_eq. Qed.
Lemma find_rangeIF_fe : find_rangeIF = find_rangeI.
Proof. repeat (apply functional_extensionality; intros ?). apply find_rangeIF_eq. Qed.
(* [comment removed for export] *)
Fixpoint erange_fBF (fuel : nat) (bc : bctx) (e : expr) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
  let erange := erange_fBF fuel' in
  match find_rangeIF (bc_ri bc) e with
  | Some r => Some (clampi r)
  | None =>
  match (let l := lin_of e in
         if lin_trivial l then None
         else match lin_range (erange bc) (fst l) (snd l) with
              | Some (lo, hi) =>
                  (* [comment removed for export] *)
                  let q := zdiv64 lo in   (* [comment removed for export] *)
                  if Z.eqb q (zdiv64 hi) then Some ((lo - q * two64)%Z, (hi - q * two64)%Z) else None
              | None => None
              end) with
  | Some r => Some r
  | None =>
  match e with
  | ELit z => let v := zmod64 z in Some (v, v)   (* [comment removed for export] *)
  | EVar _ => None
  | EAlu op a b =>
      match op with
      | ALU_ADD =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb (ah + bh) two64 then Some ((al + bl)%Z, (ah + bh)%Z)
              else if Z.leb two64 (al + bl) then Some ((al + bl - two64)%Z, (ah + bh - two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.leb bh al then Some ((al - bh)%Z, (ah - bl)%Z)
              else if Z.ltb ah bl then Some ((al - bh + two64)%Z, (ah - bl + two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_AND =>
          (* [comment removed for export] *)
          (* [comment removed for export] *)
          let ra := erange bc a in
          match (match b, ra with
                 | ELit m, Some (al, ah) =>
                     let m' := (m mod two64)%Z in
                     let j := Z.log2 (m' + 1) in
                     if (if (if Z.eqb (m' + 1) (2 ^ j) then Z.leb (al / 2 ^ j) (ah / 2 ^ j) else false) then Z.eqb (al / 2 ^ j) (ah / 2 ^ j) else false)
                     then Some ((al mod 2 ^ j)%Z, (ah mod 2 ^ j)%Z)
                     else let jh := Z.log2 (two64 - m') in
                          if (if Z.eqb (two64 - m') (2 ^ jh) then Z.ltb jh 64 else false)
                          then Some ((al - al mod 2 ^ jh)%Z, (ah - ah mod 2 ^ jh)%Z)
                          else None
                 | _, _ => None
                 end) with
          | Some r => Some r
          | None =>
          match ra, erange bc b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, Z.min ah bh)
          | Some (_, ah), None => Some (0%Z, ah)
          | None, Some (_, bh) => Some (0%Z, bh)
          | None, None => None
          end
          end
      | ALU_OR =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) => Some (Z.max al bl, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_XOR =>
          match erange bc a, erange bc b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_SRL =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s => Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z)
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb ah (2 ^ 63) then Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb (ah * 2 ^ s) two64 then Some ((al * 2 ^ s)%Z, (ah * 2 ^ s)%Z) else None
          | _, _ => None
          end
      | ALU_SLTU =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb ah bl then Some (1%Z, 1%Z)
              else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      | ALU_SLT =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool then
                (if Z.ltb ah bl then Some (1%Z, 1%Z)
                 else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z))
              else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      end
  | EAluw op a b =>
      match op with
      | ALU_ADD =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              let bl' := if Z.eqb bl bh then zsigned64 bl else bl in
              let bh' := if Z.eqb bl bh then zsigned64 bh else bh in
              if (Z.leb 0 (al + bl') && Z.ltb (ah + bh') (2 ^ 31))%bool
              then Some ((al + bl')%Z, (ah + bh')%Z) else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb bh al && Z.ltb (ah - bl) (2 ^ 31))%bool
              then Some ((al - bh)%Z, (ah - bl)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb (ah * 2 ^ s') (2 ^ 31) then Some ((al * 2 ^ s')%Z, (ah * 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRL =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if (Z.ltb ah (2 ^ 32) && (Z.ltb 0 s' || Z.ltb ah (2 ^ 31)))%bool
              then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb ah (2 ^ 31) then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMd op a b =>
      match op with
      | M_MUL =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl && Z.ltb (ah * bh) two64)%bool
              then Some ((al * bl)%Z, (ah * bh)%Z) else None
          | _, _ => None
          end
      | M_MULHU =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl)%bool
              then Some ((al * bl / two64)%Z, (ah * bh / two64)%Z) else None
          | _, _ => None
          end
      | M_DIVU =>
          match erange bc a, b with
          | Some (al, ah), ELit d =>
              let d' := (d mod two64)%Z in
              if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
          | _, _ => None
          end
      | M_REMU =>
          match erange bc a, b with
          | Some (al, ah), ELit d =>
              let d' := (d mod two64)%Z in
              if Z.ltb 0 d' then Some (0%Z, Z.min ah (d' - 1)) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMdw _ _ _ => None
  | EExt sx lo n a =>
      let w := (2 ^ (8 * Z.of_nat n))%Z in
      if sx then
        match lo, erange bc a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah (w / 2))%bool then Some (al, ah)
            else if (Nat.leb 1 n && Nat.leb n 8 && Z.leb (w / 2) al && Z.ltb ah w)%bool
                 then Some ((two64 - w + al)%Z, (two64 - w + ah)%Z) else None
        | _, _ => None
        end
      else
        match lo, erange bc a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah w)%bool then Some (al, ah) else Some (0%Z, Z.min (w - 1) (two64 - 1))
        | _, _ => Some (0%Z, Z.min (w - 1) (two64 - 1))
        end
  | EBlob sx k i n =>
      (* [comment removed for export] *)
      if sx then Some (0%Z, two64m1) else Some (0%Z, Z.min (2 ^ (8 * Z.of_nat n) - 1) (two64 - 1))%Z
  end
  end
  end
  end.
Lemma erange_fBF_fe : forall fuel, erange_fBF fuel = erange_fB fuel.
Proof.
  induction fuel as [|f IH]; apply functional_extensionality; intros bc; apply functional_extensionality; intros e; [reflexivity|].
  cbn [erange_fBF erange_fB]. rewrite IH, find_rangeIF_eq. reflexivity.
Qed.
Definition erange0BF (bc : bctx) (e : expr) : option (Z * Z) := erange_fBF erange_fuel bc e.
Definition erangeBF (bc : bctx) (e : expr) : option (Z * Z) :=
  let r := erange0BF bc e in
  let '(e', s) := deand e in
  if Z.eqb s 0 then r else
  match erange0BF bc (unlin (lin_of e')) with
  | Some (lo', hi') =>
      if Z.leb s lo' then
        match r with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some ((lo' - s)%Z, hi')
        end
      else r
  | None => r
  end.
Lemma erangeBF_fe : erangeBF = erangeB.
Proof.
  apply functional_extensionality; intros bc; apply functional_extensionality; intros e.
  unfold erangeBF, erangeB, erange0BF, erange0B. rewrite erange_fBF_fe. reflexivity.
Qed.

(* [comment removed for export] *)
Definition zb (z : Z) : option PrimInt63.int :=
  match z with
  | Z0 => Some BXI.B61
  | Zpos p => match IMGF.p2i p 60 BXI.i0 BXI.i0 with Some v => Some (PrimInt63.add BXI.B61 v) | None => None end
  | Zneg p => match IMGF.p2i p 60 BXI.i0 BXI.i0 with Some v => Some (PrimInt63.sub BXI.B61 v) | None => None end
  end.
Lemma wB63 : Uint63.wB = 2 ^ 63. Proof. reflexivity. Qed.
Lemma zb_spec : forall z a, zb z = Some a -> Uint63.to_Z a = z + 2 ^ 61 /\ - 2 ^ 60 < z < 2 ^ 60.
Proof.
  intros z a H. assert (EB : Uint63.to_Z BXI.B61 = 2 ^ 61) by reflexivity.
  destruct z as [|p|p]; cbn [zb] in H.
  - injection H as <-. rewrite EB. split; lia.
  - destruct (IMGF.p2i p 60 BXI.i0 BXI.i0) as [v|] eqn:E; [|discriminate]. injection H as <-.
    apply IMGF.p2i_spec in E; [|change (Uint63.to_Z BXI.i0) with 0; lia|change (Uint63.to_Z BXI.i0) with 0; change (2 ^ 0) with 1; lia].
    change (Uint63.to_Z BXI.i0) with 0 in E. change (Z.of_nat 60) with 60 in E. change (2 ^ 0) with 1 in E. destruct E as [E1 E2].
    rewrite Uint63.add_spec, EB, E1, wB63. rewrite Z.mod_small by lia. split; lia.
  - destruct (IMGF.p2i p 60 BXI.i0 BXI.i0) as [v|] eqn:E; [|discriminate]. injection H as <-.
    apply IMGF.p2i_spec in E; [|change (Uint63.to_Z BXI.i0) with 0; lia|change (Uint63.to_Z BXI.i0) with 0; change (2 ^ 0) with 1; lia].
    change (Uint63.to_Z BXI.i0) with 0 in E. change (Z.of_nat 60) with 60 in E. change (2 ^ 0) with 1 in E. destruct E as [E1 E2].
    rewrite Uint63.sub_spec, EB, E1, wB63. rewrite Z.mod_small by lia. split; lia.
Qed.
(* [comment removed for export] *)
Definition rng63 (r : option (Z * Z)) : option (PrimInt63.int * PrimInt63.int) :=
  match r with
  | Some (lo, hi) => match zb lo, zb hi with Some x, Some y => Some (x, y) | _, _ => None end
  | None => None
  end.

(* [comment removed for export] *)
Definition ins (T : list (Z * expr)) : list (Z * expr) := fold_right (fun t acc => lins (fst t) (snd t) acc) [] T.
Definition nonnil {A : Type} (l : list A) : bool := match l with [] => false | _ => true end.
(* [comment removed for export] *)
Definition wide (r : option (Z * Z)) : bool := match r with Some (lo, hi) => negb (Z.leb (hi - lo) conc_limit) | None => true end.
(* [comment removed for export] *)
Definition pfail (bc : bctx) (e s : expr) : bool :=
  if closedb s then true else if evalS_def s e then wide (erangeB bc s) else true.

Record binfo : Type := BI {
  bi_b : expr;                  (* [comment removed for export] *)
  bi_er : option (Z * Z);       (* [comment removed for export] *)
  bi_nf : bool;                 (* [comment removed for export] *)
  bi_c0 : Z;                    (* [comment removed for export] *)
  bi_triv : bool;               (* [comment removed for export] *)
  bi_A : option (Z * Z);        (* [comment removed for export] *)
  bi_W : bool;                  (* [comment removed for export] *)
  bi_e63 : option (PrimInt63.int * PrimInt63.int);  (* [comment removed for export] *)
  bi_fa : option (PrimInt63.int * PrimInt63.int * bool)   (* [comment removed for export] *)
}.
Definition fuel63 : nat := Nat.pred erange_fuel.
Definition nf_test (B : expr) (T1 T2 : list (Z * expr)) : bool :=
  if nonnil T1 then if nonnil T2 then if expr_eqb (lterms T1) B then if expr_eqb (lterms T2) B then
    if closedb B then false else Z.eqb (snd (deand B)) 0 else false else false else false else false.
(* [comment removed for export] *)
Definition pfailm (bc : bctx) (B : expr) (er : option (Z * Z)) (s : expr) : bool :=
  if closedb s then true else if evalS_def s B then wide (if expr_eqb s B then er else erangeBF bc s) else true.
(* [comment removed for export] *)
Definition fa_of (A : option (Z * Z)) : option (PrimInt63.int * PrimInt63.int * bool) :=
  match A with
  | Some (lo0, hi0) =>
      if Z.ltb lo0 hi0 then
        match zb lo0, zb hi0 with
        | Some l, Some h => Some (l, h, wide (Some (lo0, hi0)))
        | _, _ => None
        end
      else None
  | None => None
  end.
Definition mk_binfo (bc : bctx) (B : expr) : binfo :=
  let L := lin_of B in
  let T1 := ins (snd L) in
  let T2 := ins T1 in
  let er := erangeBF bc B in
  if nf_test B T1 T2 then
    let A := lin_range (erange_fBF fuel63 bc) 0 T1 in
    BI B er true (fst L) (match T1 with [(k, _)] => Z.eqb k 1 | _ => false end)
       A (forallb (pfailm bc B er) (subexprs B)) (rng63 er) (fa_of A)
  else BI B er false 0 false None false (rng63 er) None.

Lemma bi_er_eq : forall bc B, bi_er (mk_binfo bc B) = erangeB bc B.
Proof. intros. unfold mk_binfo. rewrite ?erangeBF_fe, ?erange_fBF_fe. cbv zeta. destruct (nf_test _ _ _); reflexivity. Qed.
Lemma bi_b_eq : forall bc B, bi_b (mk_binfo bc B) = B.
Proof. intros. unfold mk_binfo. rewrite ?erangeBF_fe, ?erange_fBF_fe. cbv zeta. destruct (nf_test _ _ _); reflexivity. Qed.

(* [comment removed for export] *)
Definition erange_add (bc : bctx) (bi : binfo) (cc : Z) : option (Z * Z) :=
  match find_rangeIF (bc_ri bc) (EAlu ALU_ADD (bi_b bi) (ELit cc)) with
  | Some r => Some (clampi r)
  | None =>
    let c := snorm (bi_c0 bi + snorm cc) in
    match (if (if Z.eqb c 0 then bi_triv bi else false) then None
           else match bi_A bi with
                | Some (lo0, hi0) =>
                    let lo := lo0 + c in let hi := hi0 + c in let q := zdiv64 lo in
                    if Z.eqb q (zdiv64 hi) then Some (lo - q * two64, hi - q * two64) else None
                | None => None
                end) with
    | Some r => Some r
    | None =>
        match erange_fBF fuel63 bc (bi_b bi), erange_fBF fuel63 bc (ELit cc) with
        | Some (al, ah), Some (bl, bh) =>
            if Z.ltb (ah + bh) two64 then Some (al + bl, ah + bh)
            else if Z.leb two64 (al + bl) then Some (al + bl - two64, ah + bh - two64)
            else None
        | _, _ => None
        end
    end
  end.

(* [comment removed for export] *)
Definition bsum (B : expr) (cc : Z) : expr := if Z.eqb cc 0 then B else EAlu ALU_ADD B (ELit cc).
(* [comment removed for export] *)
Definition addc (bi : binfo) (hask : bool) (k imm : Z) : Z :=
  if hask then snorm (snorm (bi_c0 bi + snorm k) + snorm imm) else snorm (bi_c0 bi + snorm imm).
(* [comment removed for export] *)
Definition bsum_range (bc : bctx) (bi : binfo) (cc : Z) : option (Z * Z) :=
  if Z.eqb cc 0 then bi_er bi else erange_add bc bi cc.
(* [comment removed for export] *)
Definition bsum_noconc (bi : binfo) (cc : Z) (r : option (Z * Z)) : bool :=
  if bi_W bi then (if Z.eqb cc 0 then true else wide r) else false.

(* [comment removed for export] *)
Definition bcache : Type := list binfo.
Fixpoint bfind (c : bcache) (B : expr) : option binfo :=
  match c with
  | [] => None
  | bi :: r => if expr_eqbF B (bi_b bi) then Some bi else bfind r B
  end.
Definition bget (bc : bctx) (c : bcache) (B : expr) : binfo * bcache :=
  match bfind c B with
  | Some bi => (bi, c)
  | None => let bi := mk_binfo bc B in (bi, bi :: c)
  end.
Definition BCOK (bc : bctx) (c : bcache) : Prop := forall bi, In bi c -> bi = mk_binfo bc (bi_b bi).
Lemma BCOK_nil : forall bc, BCOK bc []. Proof. intros bc bi []. Qed.
Lemma bfind_spec : forall bc c B bi, BCOK bc c -> bfind c B = Some bi -> bi = mk_binfo bc B.
Proof.
  intros bc c B bi. induction c as [|b r IH]; intros H F; [discriminate|]. cbn [bfind] in F.
  rewrite expr_eqbF_eq in F. destruct (expr_eqb B (bi_b b)) eqn:E.
  - injection F as <-. apply p_expr_eqb_eq in E. subst B. apply H. left. reflexivity.
  - apply IH; [|exact F]. intros x Hx. apply H. right. exact Hx.
Qed.
Lemma bget_spec : forall bc c B, BCOK bc c -> fst (bget bc c B) = mk_binfo bc B /\ BCOK bc (snd (bget bc c B)).
Proof.
  intros bc c B H. unfold bget. destruct (bfind c B) as [bi|] eqn:F; cbn [fst snd].
  - split; [apply (bfind_spec bc c B bi H F)|exact H].
  - split; [reflexivity|]. intros x [<-|Hx]; [rewrite bi_b_eq; reflexivity|apply H; exact Hx].
Qed.

(* [comment removed for export] *)
Lemma ladd_lit : forall L c, ladd L (c, []) = (snorm (fst L + c), ins (snd L)).
Proof. reflexivity. Qed.
Lemma lin_range_shift0 : forall rng c ts,
  lin_range rng c ts = match lin_range rng 0 ts with Some (lo, hi) => Some (lo + c, hi + c) | None => None end.
Proof.
  intros rng c ts. induction ts as [|[k a] rest IH]; [reflexivity|]. cbn [lin_range]. rewrite IH.
  destruct (rng a) as [[al ah]|]; [|reflexivity]. destruct (lin_range rng 0 rest) as [[lo hi]|]; [|reflexivity].
  destruct (Z.leb 0 k); f_equal; f_equal; ring.
Qed.
Lemma erange_fB_add : forall f bc a b, erange_fB (S f) bc (EAlu ALU_ADD a b) =
  match find_rangeI (bc_ri bc) (EAlu ALU_ADD a b) with
  | Some r => Some (clampi r)
  | None =>
    match (let l := lin_of (EAlu ALU_ADD a b) in
           if lin_trivial l then None
           else match lin_range (erange_fB f bc) (fst l) (snd l) with
                | Some (lo, hi) => let q := zdiv64 lo in if Z.eqb q (zdiv64 hi) then Some ((lo - q * two64)%Z, (hi - q * two64)%Z) else None
                | None => None
                end) with
    | Some r => Some r
    | None =>
        match erange_fB f bc a, erange_fB f bc b with
        | Some (al, ah), Some (bl, bh) =>
            if Z.ltb (ah + bh) two64 then Some ((al + bl)%Z, (ah + bh)%Z)
            else if Z.leb two64 (al + bl) then Some ((al + bl - two64)%Z, (ah + bh - two64)%Z)
            else None
        | _, _ => None
        end
    end
  end.
Proof. reflexivity. Qed.
Lemma lin_trivial_eq : forall c T, lin_trivial (c, T) = if Z.eqb c 0 then (match T with [(k, _)] => Z.eqb k 1 | _ => false end) else false.
Proof. intros c T. unfold lin_trivial. destruct T as [|[k a] [|t r]]; destruct (Z.eqb c 0); reflexivity. Qed.
Lemma pfailm_eq : forall bc B s, pfailm bc B (erangeB bc B) s = pfail bc B s.
Proof.
  intros bc B s. unfold pfailm, pfail. rewrite ?erangeBF_fe. destruct (closedb s); [reflexivity|]. destruct (evalS_def s B); [|reflexivity].
  destruct (expr_eqb s B) eqn:E; [|reflexivity]. apply p_expr_eqb_eq in E. subst s. reflexivity.
Qed.
Lemma mk_binfo_nf : forall bc B, bi_nf (mk_binfo bc B) = true ->
  nf_test B (ins (snd (lin_of B))) (ins (ins (snd (lin_of B)))) = true /\
  mk_binfo bc B = BI B (erangeB bc B) true (fst (lin_of B)) (match ins (snd (lin_of B)) with [(k, _)] => Z.eqb k 1 | _ => false end)
                     (lin_range (erange_fB fuel63 bc) 0 (ins (snd (lin_of B)))) (forallb (pfail bc B) (subexprs B)) (rng63 (erangeB bc B))
                     (fa_of (lin_range (erange_fB fuel63 bc) 0 (ins (snd (lin_of B))))).
Proof.
  intros bc B H. unfold mk_binfo in *. rewrite ?erangeBF_fe, ?erange_fBF_fe in *. cbv zeta in *.
  destruct (nf_test B (ins (snd (lin_of B))) (ins (ins (snd (lin_of B))))); [|discriminate].
  split; [reflexivity|]. f_equal. apply forallb_ext_in || idtac.
  clear H. induction (subexprs B) as [|s r IH]; [reflexivity|]. cbn [forallb]. rewrite pfailm_eq, IH. reflexivity.
Qed.
Lemma nf_spec : forall bc B, bi_nf (mk_binfo bc B) = true ->
  nonnil (ins (snd (lin_of B))) = true /\ nonnil (ins (ins (snd (lin_of B)))) = true /\
  lterms (ins (snd (lin_of B))) = B /\ lterms (ins (ins (snd (lin_of B)))) = B /\ closedb B = false /\ snd (deand B) = 0.
Proof.
  intros bc B H. destruct (mk_binfo_nf bc B H) as [H1 _]. unfold nf_test in H1.
  destruct (nonnil (ins (snd (lin_of B)))); [|discriminate]. destruct (nonnil (ins (ins (snd (lin_of B))))); [|discriminate].
  destruct (expr_eqb (lterms (ins (snd (lin_of B)))) B) eqn:E1; [|discriminate].
  destruct (expr_eqb (lterms (ins (ins (snd (lin_of B))))) B) eqn:E2; [|discriminate].
  destruct (closedb B); [discriminate|]. apply Z.eqb_eq in H1. apply p_expr_eqb_eq in E1, E2. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
Qed.
Lemma unlin_nonnil : forall c T, nonnil T = true -> unlin (c, T) = bsum (lterms T) c.
Proof. intros c T H. unfold unlin, bsum. cbn [fst snd]. destruct T; [discriminate|reflexivity]. Qed.
Lemma mkAlu_add_A : forall bc B k imm, bi_nf (mk_binfo bc B) = true ->
  mkAlu ALU_ADD (EAlu ALU_ADD B (ELit k)) (ELit imm) = bsum B (addc (mk_binfo bc B) true k imm).
Proof.
  intros bc B k imm H. destruct (nf_spec bc B H) as (N1 & N2 & L1 & L2 & _ & _).
  destruct (mk_binfo_nf bc B H) as [_ EQ]. rewrite EQ. unfold addc. cbn [bi_c0].
  unfold mkAlu. cbn [is_lit].
  change (lin_of (EAlu ALU_ADD B (ELit k))) with (ladd (lin_of B) (snorm k, [])).
  change (lin_of (ELit imm)) with (snorm imm, @nil (Z * expr)).
  rewrite !ladd_lit. cbn [fst snd]. rewrite unlin_nonnil by exact N2. rewrite L2. reflexivity.
Qed.
Lemma mkAlu_add_B : forall bc B imm, bi_nf (mk_binfo bc B) = true -> is_lit B = None ->
  mkAlu ALU_ADD B (ELit imm) = bsum B (addc (mk_binfo bc B) false 0 imm).
Proof.
  intros bc B imm H HL. destruct (nf_spec bc B H) as (N1 & N2 & L1 & L2 & _ & _).
  destruct (mk_binfo_nf bc B H) as [_ EQ]. rewrite EQ. unfold addc. cbn [bi_c0].
  unfold mkAlu. rewrite HL.
  change (lin_of (ELit imm)) with (snorm imm, @nil (Z * expr)).
  rewrite ladd_lit. cbn [fst snd]. rewrite unlin_nonnil by exact N1. rewrite L1. reflexivity.
Qed.
Lemma erange_add_eq : forall bc B cc, bi_nf (mk_binfo bc B) = true ->
  erange_add bc (mk_binfo bc B) cc = erangeB bc (EAlu ALU_ADD B (ELit cc)).
Proof.
  intros bc B cc H. destruct (nf_spec bc B H) as (_ & _ & _ & _ & _ & DZ).
  unfold erangeB. cbn [deand]. destruct (deand B) as [a' s1] eqn:ED. cbn [snd] in DZ. subst s1.
  change (Z.eqb (0 + 0) 0) with true. cbv iota.
  unfold erange0B. change erange_fuel with (S fuel63). rewrite erange_fB_add.
  destruct (mk_binfo_nf bc B H) as [_ EQ]. rewrite EQ. unfold erange_add. cbn [bi_b bi_c0 bi_triv bi_A]. rewrite find_rangeIF_eq, ?erange_fBF_fe.
  destruct (find_rangeI (bc_ri bc) (EAlu ALU_ADD B (ELit cc))) as [r|]; [reflexivity|].
  change (lin_of (EAlu ALU_ADD B (ELit cc))) with (ladd (lin_of B) (snorm cc, [])).
  rewrite ladd_lit. cbv zeta. cbn [fst snd]. rewrite lin_trivial_eq.
  rewrite (lin_range_shift0 (erange_fB fuel63 bc) (snorm (fst (lin_of B) + snorm cc)) (ins (snd (lin_of B)))).
  destruct (lin_range (erange_fB fuel63 bc) 0 (ins (snd (lin_of B)))) as [[lo0 hi0]|]; reflexivity.
Qed.
Lemma bsum_range_eq : forall bc B cc, bi_nf (mk_binfo bc B) = true ->
  bsum_range bc (mk_binfo bc B) cc = erangeB bc (bsum B cc).
Proof.
  intros bc B cc H. unfold bsum_range, bsum. destruct (Z.eqb cc 0); [apply bi_er_eq|]. apply erange_add_eq. exact H.
Qed.
(* [comment removed for export] *)
Lemma nubE_acc_in : forall l acc s, In s (nubE_acc l acc) -> In s l.
Proof.
  induction l as [|x r IH]; intros acc s H; [exact H|]. cbn [nubE_acc] in H.
  destruct (memE x acc); [right; apply (IH _ _ H)|]. destruct H as [<-|H]; [left; reflexivity|right; apply (IH _ _ H)].
Qed.
Lemma conc_fail : forall bc e l, (forall s, In s l -> pfail bc e s = true) -> conc_tryB bc e l = None.
Proof.
  intros bc e l. induction l as [|s r IH]; intros H; [reflexivity|]. cbn [conc_tryB].
  assert (Hr : conc_tryB bc e r = None) by (apply IH; intros x Hx; apply H; right; exact Hx).
  pose proof (H s (or_introl eq_refl)) as P. unfold pfail in P.
  destruct (closedb s); [exact Hr|]. destruct (evalS_def s e); cbn [negb]; [|exact Hr].
  unfold wide in P. destruct (erangeB bc s) as [[lo hi]|]; [|exact Hr].
  destruct (Z.leb (hi - lo) conc_limit); [discriminate|exact Hr].
Qed.
Lemma evalS_def_lit : forall s z, evalS_def s (ELit z) = true.
Proof. intros. cbn [evalS_def]. destruct (expr_eqb (ELit z) s); reflexivity. Qed.
Lemma conc_none : forall bc B cc, bi_nf (mk_binfo bc B) = true ->
  bsum_noconc (mk_binfo bc B) cc (erangeB bc (bsum B cc)) = true -> concretizeB bc (bsum B cc) = None.
Proof.
  intros bc B cc H HN. destruct (nf_spec bc B H) as (_ & _ & _ & _ & CL & _).
  destruct (mk_binfo_nf bc B H) as [_ EQ]. rewrite EQ in HN. unfold bsum_noconc in HN. cbn [bi_W] in HN.
  destruct (forallb (pfail bc B) (subexprs B)) eqn:W; [|discriminate].
  rewrite forallb_forall in W. unfold bsum in *. unfold concretizeB.
  destruct (Z.eqb cc 0).
  - rewrite CL. apply conc_fail. intros s Hs. apply W. apply (nubE_acc_in _ _ _ Hs).
  - cbn [closedb]. rewrite CL. cbn [andb]. apply conc_fail. intros s Hs. apply nubE_acc_in in Hs.
    cbn [subexprs] in Hs. apply in_app_or in Hs. destruct Hs as [Hs|Hs].
    + unfold pfail. destruct (closedb s) eqn:Cs; [reflexivity|]. cbn [evalS_def].
      destruct (expr_eqb (EAlu ALU_ADD B (ELit cc)) s) eqn:E.
      * apply p_expr_eqb_eq in E. subst s. exact HN.
      * pose proof (W s Hs) as P. unfold pfail in P. rewrite Cs in P.
        destruct (evalS_def s B); [destruct (expr_eqb (ELit cc) s); exact P|reflexivity].
    + apply in_app_or in Hs. destruct Hs as [Hs|Hs].
      * destruct Hs as [<-|[]]. reflexivity.
      * destruct Hs as [<-|[]]. unfold pfail. cbn [closedb]. rewrite CL. cbn [andb].
        destruct (evalS_def (EAlu ALU_ADD B (ELit cc)) (EAlu ALU_ADD B (ELit cc))); [exact HN|reflexivity].
Qed.
(* [comment removed for export] *)
Local Notation "'φ' x" := (Uint63.to_Z x) (at level 0).
Definition I61 : PrimInt63.int := Uint63.of_Z (2 ^ 61).
Definition I63m : PrimInt63.int := Uint63.of_Z 63.
Definition I1 : PrimInt63.int := Uint63.of_Z 1.
Definition I0 : PrimInt63.int := Uint63.of_Z 0.
(* [comment removed for export] *)
Inductive pex : Type :=
| PHole
| PLit (i : PrimInt63.int)
| PAlu (op : aluop) (a b : pex)
| PMul (a b : pex)
| PBad.
Fixpoint pcompile (s e : expr) : pex :=
  if expr_eqb e s then PHole else
  match e with
  | ELit w => match IMGF.z61 (wrap64 w) with Some i => PLit i | None => PBad end
  | EAlu op a b =>
      match op with
      | ALU_ADD | ALU_SUB | ALU_AND | ALU_OR | ALU_XOR | ALU_SRL | ALU_SLL | ALU_SLTU => PAlu op (pcompile s a) (pcompile s b)
      | _ => PBad
      end
  | EMd M_MUL a b => PMul (pcompile s a) (pcompile s b)
  | _ => PBad
  end.
(* [comment removed for export] *)
Definition chk61 (t : PrimInt63.int) : option PrimInt63.int := if PrimInt63.ltb t I61 then Some t else None.
Fixpoint evalP (p : pex) (z : PrimInt63.int) : option PrimInt63.int :=
  match p with
  | PHole => Some z
  | PLit i => Some i
  | PAlu op a b =>
      match evalP a z with
      | Some x =>
          match evalP b z with
          | Some y =>
              match op with
              | ALU_ADD => chk61 (PrimInt63.add x y)
              | ALU_SUB => if PrimInt63.leb y x then Some (PrimInt63.sub x y) else None
              | ALU_AND => chk61 (PrimInt63.land x y)
              | ALU_OR => chk61 (PrimInt63.lor x y)
              | ALU_XOR => chk61 (PrimInt63.lxor x y)
              | ALU_SRL => chk61 (PrimInt63.lsr x (PrimInt63.land y I63m))
              | ALU_SLL => let p := PrimInt63.land y I63m in
                           if PrimInt63.ltb x (PrimInt63.lsr I61 p) then Some (PrimInt63.lsl x p) else None
              | ALU_SLTU => Some (if PrimInt63.ltb x y then I1 else I0)
              | _ => None
              end
          | None => None
          end
      | None => None
      end
  | PMul a b =>
      match evalP a z with
      | Some x =>
          match evalP b z with
          | Some y => let '(hi, lo) := PrimInt63.mulc x y in
                      if PrimInt63.eqb hi I0 then chk61 lo else None
          | None => None
          end
      | None => None
      end
  | PBad => None
  end.
Lemma phi_I61 : φ I61 = 2 ^ 61. Proof. reflexivity. Qed.
Lemma phi_I63m : φ I63m = 63. Proof. reflexivity. Qed.
Lemma phi_I1 : φ I1 = 1. Proof. reflexivity. Qed.
Lemma phi_I0 : φ I0 = 0. Proof. reflexivity. Qed.
Lemma chk61_spec : forall t r, chk61 t = Some r -> r = t /\ φ t < 2 ^ 61.
Proof.
  intros t r H. unfold chk61 in H. rewrite IMGF.ltb_b, phi_I61 in H.
  destruct (Z.ltb_spec (φ t) (2 ^ 61)); [injection H as <-; split; [reflexivity|assumption]|discriminate].
Qed.
Lemma land63_bound : forall a, 0 <= Z.land a 63 <= 63.
Proof.
  intros a. change 63 with (Z.ones 6) at 1 2. rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound a (2 ^ 6) ltac:(lia)) as H. change (2 ^ 6) with 64 in H. lia.
Qed.
Lemma evalP_alu : forall op x y r, φ x < 2 ^ 61 -> φ y < 2 ^ 61 ->
  (match op with
   | ALU_ADD => chk61 (PrimInt63.add x y)
   | ALU_SUB => if PrimInt63.leb y x then Some (PrimInt63.sub x y) else None
   | ALU_AND => chk61 (PrimInt63.land x y)
   | ALU_OR => chk61 (PrimInt63.lor x y)
   | ALU_XOR => chk61 (PrimInt63.lxor x y)
   | ALU_SRL => chk61 (PrimInt63.lsr x (PrimInt63.land y I63m))
   | ALU_SLL => let p := PrimInt63.land y I63m in
                if PrimInt63.ltb x (PrimInt63.lsr I61 p) then Some (PrimInt63.lsl x p) else None
   | ALU_SLTU => Some (if PrimInt63.ltb x y then I1 else I0)
   | _ => None
   end) = Some r ->
  zfast op (φ x) (φ y) = φ r /\ φ r < 2 ^ 61.
Proof.
  intros op x y r Hx Hy H.
  pose proof (Uint63.to_Z_bounded x) as Bx. pose proof (Uint63.to_Z_bounded y) as By. rewrite wB63 in Bx, By.
  assert (T64 : two64 = 2 ^ 64) by reflexivity.
  destruct op; try discriminate.
  - (* [comment removed for export] *) apply chk61_spec in H. destruct H as [-> H]. rewrite Uint63.add_spec, wB63, Z.mod_small in * by lia.
    cbn [zfast]. cbv zeta. rewrite T64. destruct (Z.ltb_spec (φ x + φ y) (2 ^ 64)); [split; [reflexivity|assumption]|lia].
  - (* [comment removed for export] *) rewrite IMGF.leb_b in H. destruct (Z.leb_spec (φ y) (φ x)) as [L|L]; [|discriminate]. injection H as <-.
    rewrite Uint63.sub_spec, wB63, Z.mod_small by lia. cbn [zfast]. cbv zeta.
    destruct (Z.leb_spec 0 (φ x - φ y)); [split; [reflexivity|lia]|lia].
  - (* [comment removed for export] *) cbv zeta in H. rewrite IMGF.ltb_b in H.
    assert (EP : φ (PrimInt63.land y I63m) = Z.land (φ y) 63) by (rewrite Uint63.land_spec', phi_I63m; reflexivity).
    pose proof (land63_bound (φ y)) as BP.
    rewrite Uint63.lsr_spec, phi_I61, EP in H.
    destruct (Z.ltb_spec (φ x) (2 ^ 61 / 2 ^ Z.land (φ y) 63)) as [L|L]; [|discriminate]. injection H as <-.
    set (p := Z.land (φ y) 63) in *.
    assert (PP : 0 < 2 ^ p) by (apply Z.pow_pos_nonneg; lia).
    assert (M : φ x * 2 ^ p < 2 ^ 61).
    { pose proof (Z.mul_div_le (2 ^ 61) (2 ^ p) PP). nia. }
    rewrite Uint63.lsl_spec, EP, wB63. fold p. rewrite Z.mod_small by nia.
    cbn [zfast]. fold p. rewrite Z.shiftl_mul_pow2 by lia. unfold land64. rewrite T64.
    destruct (Z.leb_spec 0 (φ x * 2 ^ p)); [|nia]. destruct (Z.ltb_spec (φ x * 2 ^ p) (2 ^ 64)); [|lia]. cbn [andb].
    split; [reflexivity|exact M].
  - (* [comment removed for export] *) injection H as <-. cbn [zfast]. rewrite IMGF.ltb_b. destruct (Z.ltb (φ x) (φ y)); [rewrite phi_I1|rewrite phi_I0]; split; try reflexivity; lia.
  - (* [comment removed for export] *) apply chk61_spec in H. destruct H as [-> H]. rewrite Uint63.lxor_spec' in *. cbn [zfast]. split; [reflexivity|assumption].
  - (* [comment removed for export] *) apply chk61_spec in H. destruct H as [-> H].
    assert (EP : φ (PrimInt63.land y I63m) = Z.land (φ y) 63) by (rewrite Uint63.land_spec', phi_I63m; reflexivity).
    rewrite Uint63.lsr_spec, EP in *. cbn [zfast]. rewrite Z.shiftr_div_pow2 by (apply Z.land_nonneg; lia). split; [reflexivity|assumption].
  - (* [comment removed for export] *) apply chk61_spec in H. destruct H as [-> H]. rewrite Uint63.lor_spec' in *. cbn [zfast]. split; [reflexivity|assumption].
  - (* [comment removed for export] *) apply chk61_spec in H. destruct H as [-> H]. rewrite Uint63.land_spec' in *. cbn [zfast]. split; [reflexivity|assumption].
Qed.
Lemma evalP_mul : forall x y r, φ x < 2 ^ 61 -> φ y < 2 ^ 61 ->
  (let '(hi, lo) := PrimInt63.mulc x y in if PrimInt63.eqb hi I0 then chk61 lo else None) = Some r ->
  zfastm M_MUL (φ x) (φ y) = φ r /\ φ r < 2 ^ 61.
Proof.
  intros x y r Hx Hy H. pose proof (Uint63.mulc_spec x y) as MS.
  destruct (PrimInt63.mulc x y) as [hi lo]. cbn [fst snd] in MS.
  destruct (PrimInt63.eqb hi I0) eqn:E; [|discriminate]. apply Uint63.eqb_correct in E. subst hi. rewrite phi_I0 in MS.
  apply chk61_spec in H. destruct H as [-> H].
  pose proof (Uint63.to_Z_bounded lo) as Bl.
  cbn [zfastm]. unfold land64. assert (T64 : two64 = 2 ^ 64) by reflexivity. rewrite T64, MS. change (0 * Uint63.wB) with 0. rewrite Z.add_0_l.
  destruct (Z.leb_spec 0 (φ lo)); [|lia]. destruct (Z.ltb_spec (φ lo) (2 ^ 64)); [|lia]. split; [reflexivity|exact H].
Qed.
Lemma evalP_sound : forall s e z r, φ z < 2 ^ 61 -> evalP (pcompile s e) z = Some r ->
  evalS s (φ z) e = Some (φ r) /\ φ r < 2 ^ 61.
Proof.
  intros s e z. induction e; intros r Hz H; cbn [pcompile evalS] in *;
    match type of H with context [expr_eqb ?x s] => destruct (expr_eqb x s) eqn:E end;
    try (cbn [evalP] in H; injection H as <-; split; [reflexivity|exact Hz]).
  - (* [comment removed for export] *) destruct (IMGF.z61 (wrap64 z0)) as [i|] eqn:EZ; [|discriminate]. cbn [evalP] in H. injection H as <-.
    destruct (IMGF.z61_spec _ _ EZ) as [E1 E2]. rewrite E1. split; [reflexivity|lia].
  - discriminate.
  - (* [comment removed for export] *) destruct op; try discriminate; cbn [evalP] in H;
      (destruct (evalP (pcompile s e1) z) as [x|] eqn:EA; [|discriminate]; destruct (evalP (pcompile s e2) z) as [y|] eqn:EB; [|discriminate];
       destruct (IHe1 x Hz eq_refl) as [A1 A2]; destruct (IHe2 y Hz eq_refl) as [B1 B2]; rewrite A1, B1;
       match goal with |- context [zfast ?o _ _] => destruct (evalP_alu o x y r A2 B2 H) as [C1 C2] end; rewrite C1; split; [reflexivity|exact C2]).
  - discriminate.
  - (* [comment removed for export] *) destruct op; try discriminate. cbn [evalP] in H.
    destruct (evalP (pcompile s e1) z) as [x|] eqn:EA; [|discriminate]. destruct (evalP (pcompile s e2) z) as [y|] eqn:EB; [|discriminate].
    destruct (IHe1 x Hz eq_refl) as [A1 A2]. destruct (IHe2 y Hz eq_refl) as [B1 B2]. rewrite A1, B1.
    destruct (evalP_mul x y r A2 B2 H) as [C1 C2]. rewrite C1. split; [reflexivity|exact C2].
  - discriminate.
  - discriminate.
  - discriminate.
Qed.
Fixpoint all_eval_toSF (s e : expr) (p : pex) (v : Z) (vi : PrimInt63.int) (lo : Z) (loi : PrimInt63.int) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c =>
      match evalP p loi with
      | Some r => if PrimInt63.eqb r vi then all_eval_toSF s e p v vi (lo + 1) (PrimInt63.add loi I1) c else false
      | None => match evalS s (wrap64 lo) e with
                | Some w => if Z.eqb w v then all_eval_toSF s e p v vi (lo + 1) (PrimInt63.add loi I1) c else false
                | None => false
                end
      end
  end.
Lemma eqb_b : forall x y, PrimInt63.eqb x y = Z.eqb (φ x) (φ y).
Proof.
  intros x y. destruct (Z.eqb_spec (φ x) (φ y)) as [H|H].
  - apply Uint63.to_Z_inj in H. subst. apply Uint63.eqb_refl.
  - destruct (PrimInt63.eqb x y) eqn:E; [|reflexivity]. apply Uint63.eqb_correct in E. subst. contradiction.
Qed.
Lemma all_eval_toSF_eq : forall s e v vi cnt lo loi, φ vi = v -> φ loi = lo -> lo + Z.of_nat cnt <= 2 ^ 61 ->
  all_eval_toSF s e (pcompile s e) v vi lo loi cnt = all_eval_toS s e v lo cnt.
Proof.
  intros s e v vi cnt. induction cnt as [|c IH]; intros lo loi Hv Hl Hb; [reflexivity|]. cbn [all_eval_toSF all_eval_toS].
  pose proof (Uint63.to_Z_bounded loi) as Bl. rewrite Nat2Z.inj_succ in Hb.
  assert (EW : wrap64 lo = lo).
  { unfold wrap64. assert (T64 : two64 = 2 ^ 64) by reflexivity. rewrite T64. destruct (Z.leb_spec 0 lo); [|lia]. destruct (Z.ltb_spec lo (2 ^ 64)); [reflexivity|lia]. }
  assert (EN : φ (PrimInt63.add loi I1) = lo + 1) by (rewrite Uint63.add_spec, phi_I1, wB63, Hl, Z.mod_small by lia; reflexivity).
  destruct (evalP (pcompile s e) loi) as [r|] eqn:EP.
  - apply evalP_sound in EP; [|lia]. destruct EP as [EP _]. rewrite EW, <- Hl, EP, eqb_b, Hv.
    destruct (Z.eqb (φ r) v); [|reflexivity]. rewrite Hl. apply IH; [exact Hv|exact EN|lia].
  - destruct (evalS s (wrap64 lo) e) as [w|]; [|reflexivity]. destruct (Z.eqb w v); [|reflexivity]. apply IH; [exact Hv|exact EN|lia].
Qed.
(* [comment removed for export] *)
Inductive dex : Type :=
| DHole | DLit (w : Z) | DRef (i : nat)
| DAlu (op : aluop) (a b : dex) | DAluw (op : aluop) (a b : dex)
| DMd (op : mulop) (a b : dex) | DMdw (op : mulop) (a b : dex)
| DExt (sx : bool) (lo n : nat) (a : dex)
| DLet (a body : dex) (e0 : expr)
| DEval (e0 : expr).
Fixpoint evalD (s : expr) (env : list Z) (d : dex) (z : Z) : option Z :=
  match d with
  | DHole => Some z
  | DLit w => Some w
  | DRef i => nth_error env i
  | DAlu op a b => match evalD s env a z with
                   | Some x => match evalD s env b z with Some y => Some (zfast op x y) | None => None end
                   | None => None
                   end
  | DAluw op a b => match evalD s env a z with
                    | Some x => match evalD s env b z with Some y => Some (zfastw op x y) | None => None end
                    | None => None
                    end
  | DMd op a b => match evalD s env a z with
                  | Some x => match evalD s env b z with Some y => Some (zfastm op x y) | None => None end
                  | None => None
                  end
  | DMdw op a b => match evalD s env a z with
                   | Some x => match evalD s env b z with Some y => Some (zmdw op x y) | None => None end
                   | None => None
                   end
  | DExt sx lo n a => match evalD s env a z with Some x => Some (zext_fast sx lo n x) | None => None end
  | DLet a body e0 => match evalD s env a z with
                      | Some va => evalD s (va :: env) body z
                      | None => evalS s z e0
                      end
  | DEval e0 => evalS s z e0
  end.
(* [comment removed for export] *)
Fixpoint chain_base (e : expr) : expr :=
  match e with
  | EAlu _ a (ELit _) => chain_base a
  | EAlu _ (ELit _) b => chain_base b
  | EAluw _ a (ELit _) => chain_base a
  | EAluw _ (ELit _) b => chain_base b
  | EMd _ a (ELit _) => chain_base a
  | EMd _ (ELit _) b => chain_base b
  | EMdw _ a (ELit _) => chain_base a
  | EMdw _ (ELit _) b => chain_base b
  | EExt _ _ _ a => chain_base a
  | _ => e
  end.
(* [comment removed for export] *)
Definition shareable (e : expr) : bool :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b =>
      match a with ELit _ => false | _ => match b with ELit _ => false | _ => true end end
  | _ => false
  end.
Fixpoint sfind (stk : list expr) (e : expr) (i : nat) : option nat :=
  match stk with
  | [] => None
  | a :: r => if expr_eqbF e a then Some i else sfind r e (S i)
  end.
Fixpoint dcomp (fuel : nat) (s : expr) (stk : list expr) (e : expr) : dex :=
  match fuel with
  | O => DEval e
  | S f =>
      if expr_eqbF e s then DHole else
      match sfind stk e O with
      | Some i => DRef i
      | None =>
          let bin (mk : dex -> dex -> dex) (a b : expr) : dex :=
            let A := chain_base a in
            if (if shareable A then expr_eqbF A (chain_base b) else false)
            then DLet (dcomp f s stk A) (mk (dcomp f s (A :: stk) a) (dcomp f s (A :: stk) b)) e
            else mk (dcomp f s stk a) (dcomp f s stk b) in
          match e with
          | ELit w => DLit (wrap64 w)
          | EVar _ => DEval e
          | EAlu op a b => bin (DAlu op) a b
          | EAluw op a b => bin (DAluw op) a b
          | EMd op a b => bin (DMd op) a b
          | EMdw op a b => bin (DMdw op) a b
          | EExt sx lo n a => DExt sx lo n (dcomp f s stk a)
          | EBlob _ _ _ _ => DEval e
          end
      end
  end.
Lemma evalS_unfold : forall s z e, evalS s z e =
  if expr_eqb e s then Some z else
  match e with
  | ELit w => Some (wrap64 w)
  | EVar _ => None
  | EAlu op a b => match evalS s z a with Some x => match evalS s z b with Some y => Some (zfast op x y) | None => None end | None => None end
  | EAluw op a b => match evalS s z a with Some x => match evalS s z b with Some y => Some (zfastw op x y) | None => None end | None => None end
  | EMd op a b => match evalS s z a with Some x => match evalS s z b with Some y => Some (zfastm op x y) | None => None end | None => None end
  | EMdw op a b => match evalS s z a with Some x => match evalS s z b with Some y => Some (zmdw op x y) | None => None end | None => None end
  | EExt sx lo n a => match evalS s z a with Some x => Some (zext_fast sx lo n x) | None => None end
  | EBlob _ _ _ _ => None
  end.
Proof. intros s z e. destruct e; reflexivity. Qed.
Definition stk_ok (s : expr) (z : Z) (stk : list expr) (env : list Z) : Prop := Forall2 (fun a v => evalS s z a = Some v) stk env.
Lemma sfind_spec : forall s z stk env e k i, stk_ok s z stk env -> sfind stk e k = Some i ->
  exists v, nth_error env (i - k) = Some v /\ evalS s z e = Some v /\ (k <= i)%nat.
Proof.
  intros s z stk env e k i H. revert k i. induction H as [|a v stk' env' Hav H IH]; intros k i F; [discriminate|].
  cbn [sfind] in F. destruct (expr_eqbF e a) eqn:E.
  - injection F as <-. apply expr_eqbF_true in E. subst a. exists v. rewrite Nat.sub_diag. split; [reflexivity|]. split; [exact Hav|lia].
  - destruct (IH _ _ F) as (v' & N & EV & LE). exists v'. split; [|split; [exact EV|lia]].
    replace (i - k)%nat with (S (i - S k)) by lia. exact N.
Qed.
Lemma dcomp_ok : forall fuel s stk e env z, stk_ok s z stk env -> evalD s env (dcomp fuel s stk e) z = evalS s z e.
Proof.
  induction fuel as [|f IH]; intros s stk e env z H; [reflexivity|].
  cbn [dcomp]. rewrite (evalS_unfold s z e), expr_eqbF_eq.
  destruct (expr_eqb e s) eqn:EP; [reflexivity|].
  destruct (sfind stk e O) as [i|] eqn:SF.
  { destruct (sfind_spec s z stk env e O i H SF) as (v & N & EV & _). rewrite Nat.sub_0_r in N. cbn [evalD]. rewrite N.
    rewrite (evalS_unfold s z e), EP in EV. symmetry. exact EV. }
  assert (BIN : forall (mk : dex -> dex -> dex) (g : Z -> Z -> Z) a b,
            (forall env' da db, evalD s env' (mk da db) z = match evalD s env' da z with Some x => match evalD s env' db z with Some y => Some (g x y) | None => None end | None => None end) ->
            evalS s z e = match evalS s z a with Some x => match evalS s z b with Some y => Some (g x y) | None => None end | None => None end ->
            evalD s env (let A := chain_base a in
                         if (if shareable A then expr_eqbF A (chain_base b) else false)
                         then DLet (dcomp f s stk A) (mk (dcomp f s (A :: stk) a) (dcomp f s (A :: stk) b)) e
                         else mk (dcomp f s stk a) (dcomp f s stk b)) z
            = match evalS s z a with Some x => match evalS s z b with Some y => Some (g x y) | None => None end | None => None end).
  { intros mk g a b Hmk He. cbv zeta.
    destruct (if shareable (chain_base a) then expr_eqbF (chain_base a) (chain_base b) else false).
    - cbn [evalD]. rewrite (IH s stk (chain_base a) env z H).
      destruct (evalS s z (chain_base a)) as [va|] eqn:EA; [|exact He].
      assert (H' : stk_ok s z (chain_base a :: stk) (va :: env)) by (constructor; [exact EA|exact H]).
      rewrite Hmk, (IH s _ a _ z H'), (IH s _ b _ z H'). reflexivity.
    - rewrite Hmk, (IH s stk a env z H), (IH s stk b env z H). reflexivity. }
  destruct e as [w|n|op a b|op a b|op a b|op a b|sx lo n a|sx k i n]; try reflexivity;
    try (cbn [evalD]; rewrite (evalS_unfold s z _), EP; reflexivity).
  - apply (BIN (DAlu op) (zfast op)); [reflexivity|]. rewrite (evalS_unfold s z (EAlu op a b)), EP. reflexivity.
  - apply (BIN (DAluw op) (zfastw op)); [reflexivity|]. rewrite (evalS_unfold s z (EAluw op a b)), EP. reflexivity.
  - apply (BIN (DMd op) (zfastm op)); [reflexivity|]. rewrite (evalS_unfold s z (EMd op a b)), EP. reflexivity.
  - apply (BIN (DMdw op) (zmdw op)); [reflexivity|]. rewrite (evalS_unfold s z (EMdw op a b)), EP. reflexivity.
  - cbn [evalD]. rewrite (IH s stk a env z H). reflexivity.
Qed.
Definition DFUEL : nat := 160.
Definition dcomp0 (s e : expr) : dex := dcomp DFUEL s [] e.
Lemma dcomp0_ok : forall s e z, evalD s [] (dcomp0 s e) z = evalS s z e.
Proof. intros. unfold dcomp0. apply dcomp_ok. constructor. Qed.
(* [comment removed for export] *)
Fixpoint all_eval_toSD (s : expr) (d : dex) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match evalD s [] d (wrap64 lo) with
           | Some w => if Z.eqb w v then all_eval_toSD s d v (lo + 1) c else false
           | None => false
           end
  end.
Lemma all_eval_toSD_eq : forall s e v cnt lo, all_eval_toSD s (dcomp0 s e) v lo cnt = all_eval_toS s e v lo cnt.
Proof.
  intros s e v cnt. induction cnt as [|c IH]; intros lo; [reflexivity|]. cbn [all_eval_toSD all_eval_toS].
  rewrite dcomp0_ok. destruct (evalS s (wrap64 lo) e) as [w|]; [|reflexivity]. destruct (Z.eqb w v); [apply IH|reflexivity].
Qed.
Fixpoint all_eval_toSG (s e : expr) (p : pex) (d : dex) (v : Z) (vi : PrimInt63.int) (lo : Z) (loi : PrimInt63.int) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c =>
      match evalP p loi with
      | Some r => if PrimInt63.eqb r vi then all_eval_toSG s e p d v vi (lo + 1) (PrimInt63.add loi I1) c else false
      | None => all_eval_toSD s d v lo (S c)      (* [comment removed for export] *)
      end
  end.
Lemma all_eval_toSG_eq : forall s e v vi cnt lo loi, φ vi = v -> φ loi = lo -> lo + Z.of_nat cnt <= 2 ^ 61 ->
  all_eval_toSG s e (pcompile s e) (dcomp0 s e) v vi lo loi cnt = all_eval_toS s e v lo cnt.
Proof.
  intros s e v vi cnt. induction cnt as [|c IH]; intros lo loi Hv Hl Hb; [reflexivity|]. cbn [all_eval_toSG].
  pose proof (Uint63.to_Z_bounded loi) as Bl.
  destruct (evalP (pcompile s e) loi) as [r|] eqn:EP; [|apply all_eval_toSD_eq].
  cbn [all_eval_toS]. rewrite Nat2Z.inj_succ in Hb.
  assert (EW : wrap64 lo = lo).
  { unfold wrap64. assert (T64 : two64 = 2 ^ 64) by reflexivity. rewrite T64. destruct (Z.leb_spec 0 lo); [|lia]. destruct (Z.ltb_spec lo (2 ^ 64)); [reflexivity|lia]. }
  assert (EN : φ (PrimInt63.add loi I1) = lo + 1) by (rewrite Uint63.add_spec, phi_I1, wB63, Hl, Z.mod_small by lia; reflexivity).
  apply evalP_sound in EP; [|lia]. destruct EP as [EP _]. rewrite EW, <- Hl, EP, eqb_b, Hv.
  destruct (Z.eqb (φ r) v); [|reflexivity]. rewrite Hl. apply IH; [exact Hv|exact EN|lia].
Qed.
(* [comment removed for export] *)
Definition sweepGd (s e : expr) (d : dex) (v lo : Z) (cnt : nat) : bool :=
  match IMGF.z61 v, IMGF.z61 lo, IMGF.z61 (lo + Z.of_nat cnt) with
  | Some vi, Some loi, Some _ => all_eval_toSG s e (pcompile s e) d v vi lo loi cnt
  | _, _, _ => all_eval_toSD s d v lo cnt
  end.
Lemma sweepGd_eq : forall s e v lo cnt, sweepGd s e (dcomp0 s e) v lo cnt = all_eval_toS s e v lo cnt.
Proof.
  intros s e v lo cnt. unfold sweepGd.
  destruct (IMGF.z61 v) as [vi|] eqn:E1; [|apply all_eval_toSD_eq]. destruct (IMGF.z61 lo) as [loi|] eqn:E2; [|apply all_eval_toSD_eq].
  destruct (IMGF.z61 (lo + Z.of_nat cnt)) as [x|] eqn:E3; [|apply all_eval_toSD_eq].
  destruct (IMGF.z61_spec _ _ E1) as [A1 _]. destruct (IMGF.z61_spec _ _ E2) as [A2 _]. destruct (IMGF.z61_spec _ _ E3) as [_ A3].
  apply all_eval_toSG_eq; [exact A1|exact A2|lia].
Qed.
Definition probeD (s : expr) (d : dex) (v z : Z) : bool :=
  match evalD s [] d (wrap64 z) with Some w => Z.eqb w v | None => false end.
Lemma probeD_eq : forall s e v z, probeD s (dcomp0 s e) v z = probeS s e v z.
Proof. intros. unfold probeD, probeS. rewrite dcomp0_ok. reflexivity. Qed.
(* [comment removed for export] *)
Definition sweepF (s e : expr) (v lo : Z) (cnt : nat) : bool := sweepGd s e (dcomp0 s e) v lo cnt.
Lemma sweepF_eq : forall s e v lo cnt, sweepF s e v lo cnt = all_eval_toS s e v lo cnt.
Proof. intros. unfold sweepF. apply sweepGd_eq. Qed.
Lemma sweepF_fe : sweepF = all_eval_toS.
Proof. repeat (apply functional_extensionality; intros ?). apply sweepF_eq. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint nvl (e : expr) : Z :=
  match e with
  | ELit _ => 0
  | EVar _ | EBlob _ _ _ _ => 1
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => nvl a + nvl b
  | EExt _ _ _ a => nvl a
  end.
(* [comment removed for export] *)
Fixpoint subxN (e : expr) : list (expr * Z) * Z :=
  match e with
  | ELit _ => ([(e, 0)], 0)
  | EVar _ | EBlob _ _ _ _ => ([(e, 1)], 1)
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b =>
      let '(la, na) := subxN a in let '(lb, nb) := subxN b in (la ++ lb ++ [(e, na + nb)], na + nb)
  | EExt _ _ _ a => let '(la, na) := subxN a in (la ++ [(e, na)], na)
  end.
(* [comment removed for export] *)
Fixpoint bump (x : expr) (nx : Z) (a : list (expr * Z * Z)) : list (expr * Z * Z) :=
  match a with
  | [] => [(x, nx, 1)]
  | (y, ny, c) :: r => if expr_eqb x y then (y, ny, c + 1) :: r else (y, ny, c) :: bump x nx r
  end.
Definition counts (l : list (expr * Z)) : list (expr * Z * Z) := fold_left (fun a p => bump (fst p) (snd p) a) l [].
(* [comment removed for export] *)
Fixpoint bumpF (x : expr) (nx : Z) (a : list (expr * Z * Z)) : list (expr * Z * Z) :=
  match a with
  | [] => [(x, nx, 1)]
  | (y, ny, c) :: r => if expr_eqbF x y then (y, ny, c + 1) :: r else (y, ny, c) :: bumpF x nx r
  end.
Definition countsF (l : list (expr * Z)) : list (expr * Z * Z) := fold_left (fun a p => bumpF (fst p) (snd p) a) l [].
Fixpoint evalS_defF (s e : expr) : bool :=
  if expr_eqbF e s then true else
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if evalS_defF s a then evalS_defF s b else false
  | EExt _ _ _ a => evalS_defF s a
  | EBlob _ _ _ _ => false
  end.
Fixpoint conc_tryBF (bc : bctx) (e : expr) (nve : Z) (cands : list (expr * Z * Z)) : option Z :=
  match cands with
  | [] => None
  | (s, nvs, c) :: rest =>
      if closedb s then conc_tryBF bc e nve rest else
      if negb (Z.eqb (c * nvs) nve) then conc_tryBF bc e nve rest else
      if negb (evalS_def s e) then conc_tryBF bc e nve rest else
      match erangeB bc s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalS s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
                  if sweepF s e v lo (Z.to_nat (hi - lo + 1)) then Some v
                  else conc_tryBF bc e nve rest
                else conc_tryBF bc e nve rest
            | None => conc_tryBF bc e nve rest
            end
          else conc_tryBF bc e nve rest
      | None => conc_tryBF bc e nve rest
      end
  end.
Definition concretizeBF (bc : bctx) (e : expr) : option Z :=
  if closedb e then eval_closed e else let '(l, n) := subxN e in conc_tryBF bc e n (counts l).
Definition foldKBF (bc : bctx) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match erangeB bc e with
         | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                            else match concretizeBF bc e with Some v => ELit v | None => e end
         | None => match concretizeBF bc e with Some v => ELit v | None => e end
         end
  end.

(* [comment removed for export] *)
Lemma subxN_spec : forall e, subxN e = (map (fun t => (t, nvl t)) (subexprs e), nvl e).
Proof.
  induction e; cbn [subxN subexprs nvl map]; try reflexivity;
    rewrite ?IHe1, ?IHe2, ?IHe; rewrite ?map_app; reflexivity.
Qed.
(* [comment removed for export] *)
Fixpoint cntE (s : expr) (l : list expr) : Z :=
  match l with [] => 0 | t :: r => (if expr_eqb t s then 1 else 0) + cntE s r end.
Lemma cntE_app : forall s l1 l2, cntE s (l1 ++ l2) = cntE s l1 + cntE s l2.
Proof. intros s l1 l2. induction l1 as [|t r IH]; [reflexivity|]. cbn [app cntE]. rewrite IH. ring. Qed.
Fixpoint esz (e : expr) : nat :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => S (esz a + esz b)
  | EExt _ _ _ a => S (esz a)
  | _ => 1%nat
  end.
Lemma subexprs_sz : forall e t, In t (subexprs e) -> (esz t <= esz e)%nat.
Proof.
  induction e; intros t H; cbn [subexprs] in H; cbn [esz];
    try (destruct H as [<-|[]]; cbn [esz]; lia);
    try (apply in_app_or in H; destruct H as [H|H]; [apply IHe1 in H; lia|];
         apply in_app_or in H; destruct H as [H|H]; [apply IHe2 in H; lia|]; destruct H as [<-|[]]; cbn [esz]; lia).
  apply in_app_or in H; destruct H as [H|H]; [apply IHe in H; lia|]. destruct H as [<-|[]]; cbn [esz]; lia.
Qed.
Lemma cntE_small : forall s l, (forall t, In t l -> (esz t < esz s)%nat) -> cntE s l = 0.
Proof.
  intros s l H. induction l as [|t r IH]; [reflexivity|]. cbn [cntE].
  destruct (expr_eqb t s) eqn:E.
  - apply p_expr_eqb_eq in E. subst t. specialize (H s (or_introl eq_refl)). lia.
  - rewrite IH; [reflexivity|]. intros x Hx. apply H. right. exact Hx.
Qed.
Lemma cntE_self : forall s, cntE s (subexprs s) = 1.
Proof.
  intros s. destruct s; cbn [subexprs cntE]; rewrite ?kx_expr_eqb_refl; try reflexivity;
    rewrite ?cntE_app; cbn [cntE]; rewrite ?kx_expr_eqb_refl;
    rewrite !cntE_small; try reflexivity; intros t Ht; apply subexprs_sz in Ht; cbn [esz]; lia.
Qed.
(* [comment removed for export] *)
Lemma evalS_def_count : forall s e, evalS_def s e = true -> nvl e = cntE s (subexprs e) * nvl s.
Proof.
  intros s e. induction e; cbn [evalS_def]; intros H;
    match type of H with (if expr_eqb ?x ?y then _ else _) = true => destruct (expr_eqb x y) eqn:E end;
    try (apply p_expr_eqb_eq in E; subst s; rewrite cntE_self; ring);
    try discriminate.
  - cbn [subexprs cntE nvl]. rewrite E. ring.
  - destruct (evalS_def s e1) eqn:E1; [|discriminate]. cbn [subexprs nvl]. rewrite !cntE_app. cbn [cntE]. rewrite E, (IHe1 eq_refl), (IHe2 H). ring.
  - destruct (evalS_def s e1) eqn:E1; [|discriminate]. cbn [subexprs nvl]. rewrite !cntE_app. cbn [cntE]. rewrite E, (IHe1 eq_refl), (IHe2 H). ring.
  - destruct (evalS_def s e1) eqn:E1; [|discriminate]. cbn [subexprs nvl]. rewrite !cntE_app. cbn [cntE]. rewrite E, (IHe1 eq_refl), (IHe2 H). ring.
  - destruct (evalS_def s e1) eqn:E1; [|discriminate]. cbn [subexprs nvl]. rewrite !cntE_app. cbn [cntE]. rewrite E, (IHe1 eq_refl), (IHe2 H). ring.
  - cbn [subexprs nvl]. rewrite cntE_app. cbn [cntE]. rewrite E, (IHe H). ring.
Qed.
(* [comment removed for export] *)
Definition keys (a : list (expr * Z * Z)) : list expr := map (fun q => fst (fst q)) a.
Lemma eqb_iff : forall x y, expr_eqb x y = true <-> x = y.
Proof. intros x y. split; [apply p_expr_eqb_eq|intros ->; apply kx_expr_eqb_refl]. Qed.
Lemma memE_in : forall x l, memE x l = true <-> In x l.
Proof.
  intros x l. induction l as [|y r IH]; cbn [memE In]; [split; [discriminate|intros []]|].
  destruct (expr_eqb x y) eqn:E.
  - apply eqb_iff in E. subst. split; [left; reflexivity|reflexivity].
  - rewrite IH. split; [right; assumption|]. intros [->|H]; [rewrite kx_expr_eqb_refl in E; discriminate|exact H].
Qed.
Lemma bump_keys : forall x nx a, keys (bump x nx a) = if memE x (keys a) then keys a else keys a ++ [x].
Proof.
  intros x nx a. induction a as [|[[y ny] c] r IH]; [reflexivity|]. cbn [bump keys map fst memE].
  destruct (expr_eqb x y); [reflexivity|]. cbn [keys map fst]. fold (keys (bump x nx r)). fold (keys r). rewrite IH.
  destruct (memE x (keys r)); reflexivity.
Qed.
Lemma keys_fold : forall (L : list (expr * Z)) a acc, (forall x, memE x acc = memE x (keys a)) ->
  keys (fold_left (fun a p => bump (fst p) (snd p) a) L a) = keys a ++ nubE_acc (map fst L) acc.
Proof.
  induction L as [|[x nx] r IH]; intros a acc H; cbn [fold_left map fst snd nubE_acc]; [rewrite app_nil_r; reflexivity|].
  pose proof (bump_keys x nx a) as BK. rewrite (H x). destruct (memE x (keys a)) eqn:M.
  - rewrite (IH (bump x nx a) acc); [rewrite BK; reflexivity|]. intros y. rewrite BK. apply H.
  - rewrite (IH (bump x nx a) (x :: acc)); [rewrite BK, <- app_assoc; reflexivity|].
    intros y. rewrite BK. cbn [memE].
    destruct (memE y (keys a ++ [x])) eqn:M2.
    + apply memE_in in M2. apply in_app_or in M2. destruct M2 as [M2|[<-|[]]].
      * apply memE_in in M2. rewrite H, M2. destruct (expr_eqb y x); reflexivity.
      * rewrite kx_expr_eqb_refl. reflexivity.
    + destruct (expr_eqb y x) eqn:E.
      * apply eqb_iff in E. subst y. assert (C : memE x (keys a ++ [x]) = true) by (apply memE_in, in_or_app; right; left; reflexivity).
        rewrite C in M2. discriminate.
      * rewrite H. destruct (memE y (keys a)) eqn:M3; [|reflexivity].
        assert (C : memE y (keys a ++ [x]) = true) by (apply memE_in, in_or_app; left; apply memE_in; exact M3).
        rewrite C in M2. discriminate.
Qed.
Lemma keys_counts : forall L, keys (counts L) = nubE (map fst L).
Proof. intros L. unfold counts, nubE. rewrite (keys_fold L [] []); [reflexivity|]. intros x. reflexivity. Qed.
(* [comment removed for export] *)
Definition CINV (a : list (expr * Z * Z)) (done : list expr) : Prop :=
  List.NoDup (keys a) /\ (forall t, In t done -> In t (keys a)) /\
  (forall y ny c, In (y, ny, c) a -> ny = nvl y /\ c = cntE y done).
Lemma cntE_notin : forall s l, ~ In s l -> cntE s l = 0.
Proof.
  intros s l H. induction l as [|t r IH]; [reflexivity|]. cbn [cntE]. destruct (expr_eqb t s) eqn:E.
  - apply eqb_iff in E. subst t. exfalso. apply H. left. reflexivity.
  - rewrite IH; [reflexivity|]. intros C. apply H. right. exact C.
Qed.
Lemma cntE_snoc : forall s l x, cntE s (l ++ [x]) = cntE s l + (if expr_eqb x s then 1 else 0).
Proof. intros. rewrite cntE_app. cbn [cntE]. ring. Qed.
Lemma bump_inv : forall x a done, CINV a done -> CINV (bump x (nvl x) a) (done ++ [x]).
Proof.
  intros x a done (ND & CO & EN). unfold CINV. rewrite bump_keys.
  destruct (memE x (keys a)) eqn:M.
  - split; [exact ND|]. split.
    + intros t Ht. apply in_app_or in Ht. destruct Ht as [Ht|[<-|[]]]; [apply CO; exact Ht|apply memE_in; exact M].
    + clear CO. revert ND EN M. induction a as [|[[y0 ny0] c0] r IH]; intros ND EN M; [discriminate|].
      cbn [bump]. cbn [keys map fst memE] in M, ND. fold (keys r) in M, ND. inversion ND as [|? ? NI ND']; subst.
      destruct (expr_eqb x y0) eqn:E.
      * apply eqb_iff in E. subst y0. intros y ny c [H|H].
        -- injection H as <- <- <-. destruct (EN x ny0 c0 (or_introl eq_refl)) as [A B]. split; [exact A|].
           rewrite cntE_snoc, kx_expr_eqb_refl, B. reflexivity.
        -- destruct (EN y ny c (or_intror H)) as [A B]. split; [exact A|]. rewrite cntE_snoc, B.
           destruct (expr_eqb x y) eqn:E2; [|ring]. apply eqb_iff in E2. subst y. exfalso. apply NI.
           change (In x (keys r)). unfold keys. apply in_map_iff. exists (x, ny, c). split; [reflexivity|exact H].
      * intros y ny c [H|H].
        -- injection H as <- <- <-. destruct (EN y0 ny0 c0 (or_introl eq_refl)) as [A B]. split; [exact A|].
           rewrite cntE_snoc, B, E. ring.
        -- apply (IH ND'); [|exact M|exact H]. intros y1 ny1 c1 H1. apply EN. right. exact H1.
  - assert (NX : ~ In x (keys a)) by (intros C; apply memE_in in C; rewrite C in M; discriminate).
    split; [|split].
    + clear EN CO M. induction (keys a) as [|k r IH]; cbn [app].
      * constructor; [intros []|constructor].
      * inversion ND as [|? ? NI ND']; subst. constructor.
        -- intros C. apply in_app_or in C. destruct C as [C|[C|[]]]; [exact (NI C)|]. subst k. apply NX. left. reflexivity.
        -- apply IH; [exact ND'|]. intros C. apply NX. right. exact C.
    + intros t Ht. apply in_app_or in Ht. apply in_or_app. destruct Ht as [Ht|[<-|[]]]; [left; apply CO; exact Ht|right; left; reflexivity].
    + assert (XD : ~ In x done) by (intros C; apply NX, CO, C).
      clear ND CO M. revert EN NX. induction a as [|[[y0 ny0] c0] r IH]; intros EN NX y ny c H.
      * destruct H as [H|[]]. injection H as <- <- <-. split; [reflexivity|]. rewrite cntE_snoc, kx_expr_eqb_refl, (cntE_notin _ _ XD). reflexivity.
      * cbn [bump] in H. cbn [keys map fst] in NX. fold (keys r) in NX.
        destruct (expr_eqb x y0) eqn:E; [apply eqb_iff in E; subst y0; exfalso; apply NX; left; reflexivity|].
        destruct H as [H|H].
        -- injection H as <- <- <-. destruct (EN y0 ny0 c0 (or_introl eq_refl)) as [A B]. split; [exact A|]. rewrite cntE_snoc, B, E. ring.
        -- apply IH; [|intros C; apply NX; right; exact C|exact H]. intros y1 ny1 c1 H1. apply EN. right. exact H1.
Qed.
Lemma counts_inv : forall (l : list expr) a done, CINV a done ->
  CINV (fold_left (fun a p => bump (fst p) (snd p) a) (map (fun t => (t, nvl t)) l) a) (done ++ l).
Proof.
  induction l as [|x r IH]; intros a done H; cbn [map fold_left fst snd]; [rewrite app_nil_r; exact H|].
  replace (done ++ x :: r) with ((done ++ [x]) ++ r) by (rewrite <- app_assoc; reflexivity).
  apply IH. apply bump_inv. exact H.
Qed.
Lemma conc_tryBF_eq : forall bc e cands,
  (forall s nvs c, In (s, nvs, c) cands -> nvs = nvl s /\ c = cntE s (subexprs e)) ->
  conc_tryBF bc e (nvl e) cands = conc_tryB bc e (keys cands).
Proof.
  intros bc e cands. induction cands as [|[[s nvs] c] rest IH]; intros H; [reflexivity|].
  cbn [conc_tryBF conc_tryB keys map fst]. fold (keys rest). rewrite sweepF_fe.
  assert (IH' : conc_tryBF bc e (nvl e) rest = conc_tryB bc e (keys rest)) by (apply IH; intros; apply H; right; assumption).
  rewrite IH'. destruct (closedb s); [reflexivity|].
  destruct (Z.eqb (c * nvs) (nvl e)) eqn:EQ; cbn [negb]; [reflexivity|].
  destruct (evalS_def s e) eqn:ED; cbn [negb]; [|reflexivity].
  exfalso. destruct (H s nvs c (or_introl eq_refl)) as [-> ->]. apply evalS_def_count in ED. rewrite ED, Z.eqb_refl in EQ. discriminate.
Qed.
Lemma concretizeBF_eq : forall bc e, concretizeBF bc e = concretizeB bc e.
Proof.
  intros bc e. unfold concretizeBF, concretizeB. destruct (closedb e); [reflexivity|]. rewrite subxN_spec.
  rewrite conc_tryBF_eq.
  - rewrite keys_counts, map_map. cbn [fst]. rewrite map_id. reflexivity.
  - assert (CI : CINV (counts (map (fun t => (t, nvl t)) (subexprs e))) ([] ++ subexprs e)).
    { unfold counts. apply counts_inv. split; [constructor|]. split; [intros t []|intros y ny c []]. }
    destruct CI as (_ & _ & EN). exact EN.
Qed.
Lemma foldKBF_eq : forall bc e, foldKBF bc e = foldKB bc e.
Proof. intros bc e. unfold foldKBF, foldKB. rewrite concretizeBF_eq. reflexivity. Qed.
(* [comment removed for export] *)
Definition to_saddrKBF (bc : bctx) (e : expr) (imm : Z) : saddr :=
  match split_lit e with
  | (ELit _, _) => to_saddr e imm
  | _ => match concretizeBF bc (mkAlu ALU_ADD e (ELit imm)) with
         | Some v => SA (ELit 0) v
         | None => to_saddr e imm
         end
  end.
Lemma to_saddrKBF_eq : forall bc e imm, to_saddrKBF bc e imm = to_saddrKB bc e imm.
Proof. intros. unfold to_saddrKBF, to_saddrKB. rewrite concretizeBF_eq. reflexivity. Qed.

(* [comment removed for export] *)
Definition kb_gate (s e : expr) (lo hi v : Z) : bool :=
  if Z.leb 64 (hi - lo) then if Z.leb 0 lo then if Z.ltb hi two64 then
    match KBF.kb_const s lo hi e with Some v' => Z.eqb v' v | None => false end
  else false else false else false.
Lemma kb_gate_sound : forall s e lo hi v, kb_gate s e lo hi v = true ->
  all_eval_toS s e v lo (Z.to_nat (hi - lo + 1)) = true.
Proof.
  intros s e lo hi v G. unfold kb_gate in G.
  destruct (Z.leb_spec 64 (hi - lo)) as [H1|]; [|discriminate]. destruct (Z.leb_spec 0 lo) as [H2|]; [|discriminate].
  destruct (Z.ltb_spec hi two64) as [H3|]; [|discriminate].
  destruct (KBF.kb_const s lo hi e) as [v'|] eqn:KM; [|discriminate]. apply Z.eqb_eq in G. subst v'.
  apply (KBF.kb_const_sound s lo hi e v KM); [exact H2|lia|exact H3].
Qed.

Lemma bumpF_eq : forall x nx a, bumpF x nx a = bump x nx a.
Proof. intros x nx a. induction a as [|[[y ny] c] r IH]; [reflexivity|]. cbn [bumpF bump]. rewrite expr_eqbF_eq, IH. reflexivity. Qed.
Lemma countsF_eq : forall l, countsF l = counts l.
Proof.
  intros l. unfold countsF, counts. generalize (@nil (expr * Z * Z)). induction l as [|p r IH]; intros a; [reflexivity|].
  cbn [fold_left]. rewrite bumpF_eq. apply IH.
Qed.
Lemma evalS_defF_eq : forall s e, evalS_defF s e = evalS_def s e.
Proof.
  intros s e. induction e; cbn [evalS_defF evalS_def]; rewrite expr_eqbF_eq; try reflexivity;
    rewrite ?IHe1, ?IHe2, ?IHe; reflexivity.
Qed.
Lemma nvl_nonneg : forall e, 0 <= nvl e.
Proof. induction e; cbn [nvl]; lia. Qed.
Lemma closedb_nvl : forall s, closedb s = Z.eqb (nvl s) 0.
Proof.
  induction s; cbn [closedb nvl]; try reflexivity; try exact IHs;
    rewrite IHs1, IHs2; pose proof (nvl_nonneg s1); pose proof (nvl_nonneg s2);
    destruct (Z.eqb_spec (nvl s1) 0), (Z.eqb_spec (nvl s2) 0), (Z.eqb_spec (nvl s1 + nvl s2) 0); cbn [andb]; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Fixpoint conc_tryBG (bc : bctx) (e : expr) (nve : Z) (cands : list (expr * Z * Z)) : option Z :=
  match cands with
  | [] => None
  | (s, nvs, c) :: rest =>
      if Z.eqb nvs 0 then conc_tryBG bc e nve rest else      (* [comment removed for export] *)
      if negb (Z.eqb (c * nvs) nve) then conc_tryBG bc e nve rest else
      if negb (evalS_defF s e) then conc_tryBG bc e nve rest else
      match erangeBF bc s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            let d := dcomp0 s e in
            match evalD s [] d (wrap64 lo) with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeD s d v hi then probeD s d v (lo + (hi - lo) / 2)%Z else false) then
                  if (if kb_gate s e lo hi v then true else sweepGd s e d v lo (Z.to_nat (hi - lo + 1))) then Some v
                  else conc_tryBG bc e nve rest
                else conc_tryBG bc e nve rest
            | None => conc_tryBG bc e nve rest
            end
          else conc_tryBG bc e nve rest
      | None => conc_tryBG bc e nve rest
      end
  end.
Definition concretizeBG (bc : bctx) (e : expr) : option Z :=
  if closedb e then eval_closed e else let '(l, n) := subxN e in conc_tryBG bc e n (countsF l).
Definition foldKBG (bc : bctx) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match erangeBF bc e with
         | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                            else match concretizeBG bc e with Some v => ELit v | None => e end
         | None => match concretizeBG bc e with Some v => ELit v | None => e end
         end
  end.
Lemma conc_tryBG_eq : forall bc e cands,
  (forall s nvs c, In (s, nvs, c) cands -> nvs = nvl s /\ c = cntE s (subexprs e)) ->
  conc_tryBG bc e (nvl e) cands = conc_tryB bc e (keys cands).
Proof.
  intros bc e cands. induction cands as [|[[s nvs] c] rest IH]; intros H; [reflexivity|].
  cbn [conc_tryBG conc_tryB keys map fst]. fold (keys rest). rewrite erangeBF_fe, evalS_defF_eq.
  assert (IH' : conc_tryBG bc e (nvl e) rest = conc_tryB bc e (keys rest)) by (apply IH; intros; apply H; right; assumption).
  rewrite IH'. destruct (H s nvs c (or_introl eq_refl)) as [Hn _]. rewrite (closedb_nvl s), <- Hn. destruct (Z.eqb nvs 0); [reflexivity|].
  destruct (Z.eqb (c * nvs) (nvl e)) eqn:EQ; cbn [negb].
  - destruct (evalS_def s e); cbn [negb]; [|reflexivity].
    destruct (erangeB bc s) as [[lo hi]|]; [|reflexivity]. destruct (Z.leb (hi - lo) conc_limit); [|reflexivity].
    cbv zeta. rewrite dcomp0_ok. destruct (evalS s (wrap64 lo) e) as [v|] eqn:EV; [|reflexivity].
    rewrite !probeD_eq, sweepGd_eq.
    destruct (if Z.ltb hi lo then true else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2) else false) eqn:PR; [|reflexivity].
    destruct (kb_gate s e lo hi v) eqn:KG; [|reflexivity].
    rewrite (kb_gate_sound s e lo hi v KG). reflexivity.
  - destruct (evalS_def s e) eqn:ED; cbn [negb]; [|reflexivity].
    exfalso. destruct (H s nvs c (or_introl eq_refl)) as [-> ->]. apply evalS_def_count in ED. rewrite ED, Z.eqb_refl in EQ. discriminate.
Qed.
Lemma concretizeBG_eq : forall bc e, concretizeBG bc e = concretizeB bc e.
Proof.
  intros bc e. unfold concretizeBG, concretizeB. destruct (closedb e); [reflexivity|]. rewrite subxN_spec. cbv beta iota. rewrite countsF_eq.
  rewrite conc_tryBG_eq.
  - rewrite keys_counts, map_map. cbn [fst]. rewrite map_id. reflexivity.
  - assert (CI : CINV (counts (map (fun t => (t, nvl t)) (subexprs e))) ([] ++ subexprs e)).
    { unfold counts. apply counts_inv. split; [constructor|]. split; [intros t []|intros y ny c []]. }
    destruct CI as (_ & _ & EN). exact EN.
Qed.
Lemma foldKBG_eq : forall bc e, foldKBG bc e = foldKB bc e.
Proof. intros bc e. unfold foldKBG, foldKB. rewrite concretizeBG_eq, erangeBF_fe. reflexivity. Qed.
(* [comment removed for export] *)
Definition to_saddrKBG (bc : bctx) (e : expr) (imm : Z) : saddr :=
  match split_lit e with
  | (ELit _, _) => to_saddr e imm
  | _ => match concretizeBG bc (mkAlu ALU_ADD e (ELit imm)) with
         | Some v => SA (ELit 0) v
         | None => to_saddr e imm
         end
  end.
Lemma to_saddrKBG_eq : forall bc e imm, to_saddrKBG bc e imm = to_saddrKB bc e imm.
Proof. intros. unfold to_saddrKBG, to_saddrKB. rewrite concretizeBG_eq. reflexivity. Qed.

(* [comment removed for export] *)
Definition bigE (e : expr) : bool := negb (esize_le e 48).
Definition rmemo : Type := list (expr * option (Z * Z)).
Definition RMOK (bc : bctx) (m : rmemo) : Prop := forall e r, In (e, r) m -> r = erangeB bc e.
Lemma RMOK_nil : forall bc, RMOK bc []. Proof. intros bc e r []. Qed.
Fixpoint rm_get (m : rmemo) (e : expr) : option (option (Z * Z)) :=
  match m with
  | [] => None
  | (a, r) :: t => if expr_eqbF e a then Some r else rm_get t e
  end.
Lemma rm_get_ok : forall bc m e r, RMOK bc m -> rm_get m e = Some r -> r = erangeB bc e.
Proof.
  intros bc m e r. induction m as [|[a ra] t IH]; intros H G; [discriminate|]. cbn [rm_get] in G.
  destruct (expr_eqbF e a) eqn:E.
  - injection G as <-. apply expr_eqbF_true in E. subst a. apply H. left. reflexivity.
  - apply IH; [|exact G]. intros x rx Hx. apply H. right. exact Hx.
Qed.
Definition rangeM (bc : bctx) (m : rmemo) (e : expr) : option (Z * Z) * rmemo :=
  if bigE e then
    match rm_get m e with
    | Some r => (r, m)
    | None => let r := erangeBF bc e in (r, (e, r) :: m)
    end
  else (erangeBF bc e, m).
Lemma rangeM_ok : forall bc m e, RMOK bc m -> fst (rangeM bc m e) = erangeB bc e /\ RMOK bc (snd (rangeM bc m e)).
Proof.
  intros bc m e H. unfold rangeM. rewrite erangeBF_fe. destruct (bigE e); [|split; [reflexivity|exact H]].
  destruct (rm_get m e) as [r|] eqn:G; cbn [fst snd].
  - split; [apply (rm_get_ok bc m e r H G)|exact H].
  - split; [reflexivity|]. intros x rx [E|Hx]; [injection E as <- <-; reflexivity|apply H; exact Hx].
Qed.
Fixpoint conc_tryBM (bc : bctx) (e : expr) (nve : Z) (cands : list (expr * Z * Z)) (m : rmemo) : option Z * rmemo :=
  match cands with
  | [] => (None, m)
  | (s, nvs, c) :: rest =>
      if Z.eqb nvs 0 then conc_tryBM bc e nve rest m else
      if negb (Z.eqb (c * nvs) nve) then conc_tryBM bc e nve rest m else
      if negb (evalS_defF s e) then conc_tryBM bc e nve rest m else
      let '(r, m1) := rangeM bc m s in
      match r with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            let d := dcomp0 s e in
            match evalD s [] d (wrap64 lo) with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeD s d v hi then probeD s d v (lo + (hi - lo) / 2)%Z else false) then
                  if (if kb_gate s e lo hi v then true else sweepGd s e d v lo (Z.to_nat (hi - lo + 1))) then (Some v, m1)
                  else conc_tryBM bc e nve rest m1
                else conc_tryBM bc e nve rest m1
            | None => conc_tryBM bc e nve rest m1
            end
          else conc_tryBM bc e nve rest m1
      | None => conc_tryBM bc e nve rest m1
      end
  end.
Lemma conc_tryBM_ok : forall bc e nve cands m, RMOK bc m ->
  fst (conc_tryBM bc e nve cands m) = conc_tryBG bc e nve cands /\ RMOK bc (snd (conc_tryBM bc e nve cands m)).
Proof.
  intros bc e nve cands. induction cands as [|[[s nvs] c] rest IH]; intros m H; [split; [reflexivity|exact H]|].
  cbn [conc_tryBM conc_tryBG]. destruct (Z.eqb nvs 0); [apply IH; exact H|].
  destruct (negb (Z.eqb (c * nvs) nve)); [apply IH; exact H|].
  destruct (negb (evalS_defF s e)); [apply IH; exact H|].
  destruct (rangeM_ok bc m s H) as [Hr Hm1]. destruct (rangeM bc m s) as [r m1]. cbn [fst snd] in Hr, Hm1.
  rewrite erangeBF_fe, <- Hr. destruct r as [[lo hi]|]; [|apply IH; exact Hm1].
  destruct (Z.leb (hi - lo) conc_limit); [|apply IH; exact Hm1]. cbv zeta.
  destruct (evalD s [] (dcomp0 s e) (wrap64 lo)) as [v|]; [|apply IH; exact Hm1].
  destruct (if Z.ltb hi lo then true else if probeD s (dcomp0 s e) v hi then probeD s (dcomp0 s e) v (lo + (hi - lo) / 2) else false); [|apply IH; exact Hm1].
  destruct (if kb_gate s e lo hi v then true else sweepGd s e (dcomp0 s e) v lo (Z.to_nat (hi - lo + 1))); [split; [reflexivity|exact Hm1]|apply IH; exact Hm1].
Qed.
Definition concretizeBM (bc : bctx) (e : expr) (m : rmemo) : option Z * rmemo :=
  if closedb e then (eval_closed e, m) else let '(l, n) := subxN e in conc_tryBM bc e n (countsF l) m.
Lemma concretizeBM_ok : forall bc e m, RMOK bc m ->
  fst (concretizeBM bc e m) = concretizeBG bc e /\ RMOK bc (snd (concretizeBM bc e m)).
Proof.
  intros bc e m H. unfold concretizeBM, concretizeBG. destruct (closedb e); [split; [reflexivity|exact H]|].
  destruct (subxN e) as [l n]. apply conc_tryBM_ok. exact H.
Qed.
Definition foldKBM (bc : bctx) (m : rmemo) (e : expr) : expr * rmemo :=
  match e with
  | ELit _ => (e, m)
  | _ => let '(r, m1) := rangeM bc m e in
         let tail := fun (_ : unit) => let '(c, m2) := concretizeBM bc e m1 in (match c with Some v => ELit v | None => e end, m2) in
         match r with
         | Some (lo, hi) => if Z.eqb lo hi then (ELit lo, m1) else tail tt
         | None => tail tt
         end
  end.
Lemma foldKBM_ok : forall bc m e, RMOK bc m -> fst (foldKBM bc m e) = foldKBG bc e /\ RMOK bc (snd (foldKBM bc m e)).
Proof.
  intros bc m e H.
  assert (G : forall e', fst (let '(r, m1) := rangeM bc m e' in
                           let tail := fun (_ : unit) => let '(c, m2) := concretizeBM bc e' m1 in (match c with Some v => ELit v | None => e' end, m2) in
                           match r with Some (lo, hi) => if Z.eqb lo hi then (ELit lo, m1) else tail tt | None => tail tt end)
                    = match erangeBF bc e' with
                      | Some (lo, hi) => if Z.eqb lo hi then ELit lo else match concretizeBG bc e' with Some v => ELit v | None => e' end
                      | None => match concretizeBG bc e' with Some v => ELit v | None => e' end
                      end
                    /\ RMOK bc (snd (let '(r, m1) := rangeM bc m e' in
                           let tail := fun (_ : unit) => let '(c, m2) := concretizeBM bc e' m1 in (match c with Some v => ELit v | None => e' end, m2) in
                           match r with Some (lo, hi) => if Z.eqb lo hi then (ELit lo, m1) else tail tt | None => tail tt end))).
  { intros e'. destruct (rangeM_ok bc m e' H) as [Hr Hm1]. destruct (rangeM bc m e') as [r m1]. cbn [fst snd] in Hr, Hm1.
    rewrite erangeBF_fe, <- Hr. cbv zeta.
    destruct (concretizeBM_ok bc e' m1 Hm1) as [Hc Hm2]. destruct (concretizeBM bc e' m1) as [c m2]. cbn [fst snd] in Hc, Hm2. subst c.
    destruct r as [[lo hi]|]; [destruct (Z.eqb lo hi)|]; cbn [fst snd]; split; try reflexivity; assumption. }
  destruct e; try apply G. split; [reflexivity|exact H].
Qed.

(* [comment removed for export] *)
Definition hask (e : expr) : bool := match e with EAlu ALU_ADD _ (ELit _) => true | _ => false end.
Lemma split_lit_shape : forall e B k, split_lit e = (B, k) -> is_lit B = None ->
  (hask e = true /\ e = EAlu ALU_ADD B (ELit k)) \/ (hask e = false /\ e = B /\ k = 0).
Proof.
  intros e B k H HL. unfold split_lit in H.
  destruct e as [z|n|op a b|op a b|op a b|op a b|sx lo n a|sx kk i n];
    try (injection H as <- <-; right; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity).
  - injection H as <- <-. discriminate.
  - destruct op; try (injection H as <- <-; right; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity).
    destruct b; try (injection H as <- <-; right; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity).
    injection H as <- <-. left. split; reflexivity.
Qed.
Lemma to_saddrKB_nolit : forall bc e imm B k, split_lit e = (B, k) -> is_lit B = None ->
  to_saddrKB bc e imm = match concretizeB bc (mkAlu ALU_ADD e (ELit imm)) with Some v => SA (ELit 0) v | None => to_saddr e imm end.
Proof. intros bc e imm B k H HL. unfold to_saddrKB. rewrite H. destruct B; try reflexivity; discriminate. Qed.
(* [comment removed for export] *)
Lemma mkAlu_add_base : forall bc e imm B k, split_lit e = (B, k) -> is_lit B = None -> bi_nf (mk_binfo bc B) = true ->
  mkAlu ALU_ADD e (ELit imm) = bsum B (addc (mk_binfo bc B) (hask e) k imm).
Proof.
  intros bc e imm B k H HL NF. destruct (split_lit_shape e B k H HL) as [[HK ->]|[HK [-> ->]]]; rewrite HK.
  - apply mkAlu_add_A. exact NF.
  - apply mkAlu_add_B; assumption.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rfast (bc : bctx) (bi : binfo) (cc : Z) : option bool :=
  match bi_fa bi with
  | Some (lo63, hi63, w) =>
      if Z.eqb cc 0 then None else
      match find_rangeIF (bc_ri bc) (EAlu ALU_ADD (bi_b bi) (ELit cc)) with
      | Some _ => None
      | None =>
          let c := snorm (bi_c0 bi + snorm cc) in
          if (if Z.eqb c 0 then bi_triv bi else false) then None else
          match zb c with
          | Some c63 => if PrimInt63.leb BXI.B62 (PrimInt63.add lo63 c63) then Some w else None
          | None => None
          end
      end
  | None => None
  end.
Lemma bi_fa_eq : forall bc B, bi_fa (mk_binfo bc B) = fa_of (bi_A (mk_binfo bc B)).
Proof. intros. unfold mk_binfo. rewrite ?erangeBF_fe, ?erange_fBF_fe. cbv zeta. destruct (nf_test _ _ _); reflexivity. Qed.
Lemma rfast_spec : forall bc B cc w, rfast bc (mk_binfo bc B) cc = Some w ->
  exists lo hi, bsum_range bc (mk_binfo bc B) cc = Some (lo, hi) /\ Z.eqb lo hi = false
                /\ bsum_noconc (mk_binfo bc B) cc (Some (lo, hi)) = (if bi_W (mk_binfo bc B) then w else false).
Proof.
  intros bc B cc w H. unfold rfast in H. rewrite bi_fa_eq in H. unfold fa_of in H.
  destruct (bi_A (mk_binfo bc B)) as [[lo0 hi0]|] eqn:EA; [|discriminate].
  destruct (Z.ltb_spec lo0 hi0) as [LT|]; [|discriminate].
  destruct (zb lo0) as [l63|] eqn:E1; [|discriminate]. destruct (zb hi0) as [h63|] eqn:E2; [|discriminate].
  destruct (Z.eqb cc 0) eqn:EC; [discriminate|].
  destruct (find_rangeIF (bc_ri bc) (EAlu ALU_ADD (bi_b (mk_binfo bc B)) (ELit cc))) eqn:EF; [discriminate|]. cbv zeta in H.
  destruct (if Z.eqb (snorm (bi_c0 (mk_binfo bc B) + snorm cc)) 0 then bi_triv (mk_binfo bc B) else false) eqn:ET; [discriminate|].
  destruct (zb (snorm (bi_c0 (mk_binfo bc B) + snorm cc))) as [c63|] eqn:E3; [|discriminate].
  destruct (PrimInt63.leb BXI.B62 (PrimInt63.add l63 c63)) eqn:EL; [|discriminate]. injection H as <-.
  set (c := snorm (bi_c0 (mk_binfo bc B) + snorm cc)) in *.
  destruct (zb_spec _ _ E1) as [A1 B1]. destruct (zb_spec _ _ E2) as [A2 B2]. destruct (zb_spec _ _ E3) as [A3 B3].
  rewrite IMGF.leb_b, Uint63.add_spec, A1, A3, wB63 in EL. change (Uint63.to_Z BXI.B62) with (2 ^ 62) in EL.
  rewrite Z.mod_small in EL by lia. apply Z.leb_le in EL.
  assert (Q1 : zdiv64 (lo0 + c) = 0).
  { unfold zdiv64. destruct (Z.leb_spec 0 (lo0 + c)); [|lia]. destruct (Z.ltb_spec (lo0 + c) two64z); [reflexivity|]. unfold two64z in *. lia. }
  assert (Q2 : zdiv64 (hi0 + c) = 0).
  { unfold zdiv64. destruct (Z.leb_spec 0 (hi0 + c)); [|lia]. destruct (Z.ltb_spec (hi0 + c) two64z); [reflexivity|]. unfold two64z in *. lia. }
  exists (lo0 + c), (hi0 + c). split; [|split].
  - unfold bsum_range. rewrite EC. unfold erange_add. rewrite EF. fold c. rewrite ET, EA. cbv zeta. rewrite Q1, Q2. cbn [Z.eqb].
    f_equal. f_equal; ring.
  - apply Z.eqb_neq. lia.
  - unfold bsum_noconc. rewrite EC. destruct (bi_W (mk_binfo bc B)); [|reflexivity].
    unfold wide. replace (hi0 + c - (lo0 + c)) with (hi0 - lo0) by ring. reflexivity.
Qed.

Definition to_saddr_nl0 (bc : bctx) (c : bcache) (e : expr) (imm : Z) (B : expr) (k : Z) : saddr * bcache :=
  let '(bi, c') := bget bc c B in
  if bi_nf bi then
    let cc := addc bi (hask e) k imm in
    if bsum_noconc bi cc (bsum_range bc bi cc) then (to_saddr e imm, c') else (to_saddrKBG bc e imm, c')
  else (to_saddrKBG bc e imm, c').
Definition to_saddr_nl (bc : bctx) (c : bcache) (e : expr) (imm : Z) (B : expr) (k : Z) : saddr * bcache :=
  let '(bi, c') := bget bc c B in
  if bi_nf bi then
    let cc := addc bi (hask e) k imm in
    if (match rfast bc bi cc with Some w => if bi_W bi then w else false | None => bsum_noconc bi cc (bsum_range bc bi cc) end)
    then (to_saddr e imm, c') else (to_saddrKBG bc e imm, c')
  else (to_saddrKBG bc e imm, c').
Definition to_saddrKB_c (bc : bctx) (c : bcache) (e : expr) (imm : Z) : saddr * bcache :=
  let '(B, k) := split_lit e in
  match B with
  | ELit _ => (to_saddr e imm, c)
  | _ => to_saddr_nl bc c e imm B k
  end.
Lemma to_saddr_nl0_spec : forall bc c e imm B k, BCOK bc c -> split_lit e = (B, k) -> is_lit B = None ->
  fst (to_saddr_nl0 bc c e imm B k) = to_saddrKB bc e imm /\ BCOK bc (snd (to_saddr_nl0 bc c e imm B k)).
Proof.
  intros bc c e imm B k HC ES HL. unfold to_saddr_nl0. rewrite to_saddrKBG_eq. destruct (bget_spec bc c B HC) as [G1 G2].
  destruct (bget bc c B) as [bi c']. cbn [fst snd] in G1, G2. subst bi.
  destruct (bi_nf (mk_binfo bc B)) eqn:NF; [|split; [reflexivity|exact G2]]. cbv zeta.
  destruct (bsum_noconc _ _ _) eqn:NC; [|split; [reflexivity|exact G2]].
  split; [|exact G2]. cbn [fst]. rewrite (to_saddrKB_nolit bc e imm B k ES HL), (mkAlu_add_base bc e imm B k ES HL NF).
  rewrite bsum_range_eq in NC by exact NF. rewrite (conc_none bc B _ NF NC). reflexivity.
Qed.
Lemma to_saddr_nl_eq0 : forall bc c e imm B k, BCOK bc c -> to_saddr_nl bc c e imm B k = to_saddr_nl0 bc c e imm B k.
Proof.
  intros bc c e imm B k HC. unfold to_saddr_nl, to_saddr_nl0. destruct (bget_spec bc c B HC) as [G1 G2].
  destruct (bget bc c B) as [bi c']. cbn [fst snd] in G1, G2. subst bi.
  destruct (bi_nf (mk_binfo bc B)); [|reflexivity]. cbv zeta.
  destruct (rfast bc (mk_binfo bc B) (addc (mk_binfo bc B) (hask e) k imm)) as [w|] eqn:RF; [|reflexivity].
  destruct (rfast_spec bc B _ w RF) as (lo & hi & R1 & R2 & R3). rewrite R1, R3. reflexivity.
Qed.
Lemma to_saddr_nl_spec : forall bc c e imm B k, BCOK bc c -> split_lit e = (B, k) -> is_lit B = None ->
  fst (to_saddr_nl bc c e imm B k) = to_saddrKB bc e imm /\ BCOK bc (snd (to_saddr_nl bc c e imm B k)).
Proof. intros bc c e imm B k HC ES HL. rewrite (to_saddr_nl_eq0 bc c e imm B k HC). apply to_saddr_nl0_spec; assumption. Qed.

Lemma to_saddrKB_c_spec : forall bc c e imm, BCOK bc c ->
  fst (to_saddrKB_c bc c e imm) = to_saddrKB bc e imm /\ BCOK bc (snd (to_saddrKB_c bc c e imm)).
Proof.
  intros bc c e imm HC. unfold to_saddrKB_c. destruct (split_lit e) as [B k] eqn:ES.
  destruct B; try (apply to_saddr_nl_spec; [exact HC|exact ES|reflexivity]).
  split; [|exact HC]. cbn [fst]. unfold to_saddrKB. rewrite ES. reflexivity.
Qed.
(* [comment removed for export] *)
Definition add_nl0 (bc : bctx) (c : bcache) (a : expr) (imm : Z) (B : expr) (k : Z) : expr * bcache :=
  let '(bi, c') := bget bc c B in
  if bi_nf bi then
    let cc := addc bi (hask a) k imm in
    let r := bsum_range bc bi cc in
    match r with
    | Some (lo, hi) =>
        if Z.eqb lo hi then (ELit lo, c')
        else if bsum_noconc bi cc r then (bsum B cc, c') else (foldKBG bc (mkAlu ALU_ADD a (ELit imm)), c')
    | None => if bsum_noconc bi cc r then (bsum B cc, c') else (foldKBG bc (mkAlu ALU_ADD a (ELit imm)), c')
    end
  else (foldKBG bc (mkAlu ALU_ADD a (ELit imm)), c').
Definition add_nl (bc : bctx) (c : bcache) (a : expr) (imm : Z) (B : expr) (k : Z) : expr * bcache :=
  let '(bi, c') := bget bc c B in
  if bi_nf bi then
    let cc := addc bi (hask a) k imm in
    match rfast bc bi cc with
    | Some w => if (if bi_W bi then w else false) then (bsum B cc, c') else (foldKBG bc (mkAlu ALU_ADD a (ELit imm)), c')
    | None =>
        let r := bsum_range bc bi cc in
        match r with
        | Some (lo, hi) =>
            if Z.eqb lo hi then (ELit lo, c')
            else if bsum_noconc bi cc r then (bsum B cc, c') else (foldKBG bc (mkAlu ALU_ADD a (ELit imm)), c')
        | None => if bsum_noconc bi cc r then (bsum B cc, c') else (foldKBG bc (mkAlu ALU_ADD a (ELit imm)), c')
        end
    end
  else (foldKBG bc (mkAlu ALU_ADD a (ELit imm)), c').
(* [comment removed for export] *)
Definition mkAluL (op : aluop) (a b : expr) : expr :=
  match a, b with
  | ELit x, ELit y => ELit (zfast op (zmod64 x) (zmod64 y))
  | _, _ => mkAlu op a b
  end.
Lemma wrap64_zmod64 : forall z, wrap64 z = zmod64 z.
Proof.
  intros z. rewrite zmod64_eq. unfold wrap64. destruct (Z.leb_spec 0 z); cbn [andb]; [|reflexivity].
  destruct (Z.ltb_spec z two64); [|reflexivity]. symmetry. apply Z.mod_small. unfold two64 in *. lia.
Qed.
Lemma mkAluL_eq : forall op a b, mkAluL op a b = mkAlu op a b.
Proof.
  intros op a b. unfold mkAluL. destruct a; try reflexivity. destruct b; try reflexivity.
  unfold mkAlu. cbn [is_lit]. unfold zalu_l. rewrite !wrap64_zmod64. reflexivity.
Qed.
Definition mkAluKB_add_c (bc : bctx) (c : bcache) (a : expr) (imm : Z) : expr * bcache :=
  let '(B, k) := split_lit a in
  match B with
  | ELit _ => (foldKBG bc (mkAluL ALU_ADD a (ELit imm)), c)
  | _ => add_nl bc c a imm B k
  end.
Lemma foldKB_bsum : forall bc B cc, closedb B = false ->
  foldKB bc (bsum B cc) =
  match erangeB bc (bsum B cc) with
  | Some (lo, hi) => if Z.eqb lo hi then ELit lo else match concretizeB bc (bsum B cc) with Some v => ELit v | None => bsum B cc end
  | None => match concretizeB bc (bsum B cc) with Some v => ELit v | None => bsum B cc end
  end.
Proof. intros bc B cc H. unfold bsum. destruct (Z.eqb cc 0); [|reflexivity]. destruct B; try reflexivity. discriminate. Qed.
Lemma add_nl0_spec : forall bc c a imm B k, BCOK bc c -> split_lit a = (B, k) -> is_lit B = None ->
  fst (add_nl0 bc c a imm B k) = mkAluKB bc ALU_ADD a (ELit imm) /\ BCOK bc (snd (add_nl0 bc c a imm B k)).
Proof.
  intros bc c a imm B k HC ES HL. unfold add_nl0.
  replace (foldKBG bc (mkAlu ALU_ADD a (ELit imm))) with (mkAluKB bc ALU_ADD a (ELit imm)) by (rewrite foldKBG_eq; reflexivity).
  destruct (bget_spec bc c B HC) as [G1 G2].
  destruct (bget bc c B) as [bi c']. cbn [fst snd] in G1, G2. subst bi.
  destruct (bi_nf (mk_binfo bc B)) eqn:NF; [|split; [reflexivity|exact G2]]. cbv zeta.
  destruct (nf_spec bc B NF) as (_ & _ & _ & _ & CL & _).
  assert (EQ : mkAluKB bc ALU_ADD a (ELit imm) = foldKB bc (bsum B (addc (mk_binfo bc B) (hask a) k imm))).
  { unfold mkAluKB. change (mkAluK0B bc ALU_ADD a (ELit imm)) with (mkAlu ALU_ADD a (ELit imm)).
    rewrite (mkAlu_add_base bc a imm B k ES HL NF). reflexivity. }
  rewrite EQ, (foldKB_bsum bc B _ CL). rewrite <- (bsum_range_eq bc B _ NF).
  set (cc := addc (mk_binfo bc B) (hask a) k imm). set (r := bsum_range bc (mk_binfo bc B) cc).
  assert (NCE : bsum_noconc (mk_binfo bc B) cc r = true -> concretizeB bc (bsum B cc) = None).
  { intros NC. apply (conc_none bc B cc NF). rewrite <- (bsum_range_eq bc B cc NF). exact NC. }
  destruct r as [[lo hi]|].
  - destruct (Z.eqb lo hi); [split; [reflexivity|exact G2]|].
    destruct (bsum_noconc (mk_binfo bc B) cc (Some (lo, hi))) eqn:NC; [|split; [reflexivity|exact G2]].
    rewrite (NCE eq_refl). split; [reflexivity|exact G2].
  - destruct (bsum_noconc (mk_binfo bc B) cc None) eqn:NC; [|split; [reflexivity|exact G2]].
    rewrite (NCE eq_refl). split; [reflexivity|exact G2].
Qed.
Lemma add_nl_eq0 : forall bc c a imm B k, BCOK bc c -> add_nl bc c a imm B k = add_nl0 bc c a imm B k.
Proof.
  intros bc c a imm B k HC. unfold add_nl, add_nl0. destruct (bget_spec bc c B HC) as [G1 G2].
  destruct (bget bc c B) as [bi c']. cbn [fst snd] in G1, G2. subst bi.
  destruct (bi_nf (mk_binfo bc B)); [|reflexivity]. cbv zeta.
  destruct (rfast bc (mk_binfo bc B) (addc (mk_binfo bc B) (hask a) k imm)) as [w|] eqn:RF; [|reflexivity].
  destruct (rfast_spec bc B _ w RF) as (lo & hi & R1 & R2 & R3). rewrite R1, R2, R3. reflexivity.
Qed.
Lemma add_nl_spec : forall bc c a imm B k, BCOK bc c -> split_lit a = (B, k) -> is_lit B = None ->
  fst (add_nl bc c a imm B k) = mkAluKB bc ALU_ADD a (ELit imm) /\ BCOK bc (snd (add_nl bc c a imm B k)).
Proof. intros bc c a imm B k HC ES HL. rewrite (add_nl_eq0 bc c a imm B k HC). apply add_nl0_spec; assumption. Qed.

Lemma mkAluKB_add_c_spec : forall bc c a imm, BCOK bc c ->
  fst (mkAluKB_add_c bc c a imm) = mkAluKB bc ALU_ADD a (ELit imm) /\ BCOK bc (snd (mkAluKB_add_c bc c a imm)).
Proof.
  intros bc c a imm HC. unfold mkAluKB_add_c. destruct (split_lit a) as [B k] eqn:ES.
  destruct B; try (apply add_nl_spec; [exact HC|exact ES|reflexivity]).
  split; [cbn [fst]; rewrite ?foldKBG_eq, mkAluL_eq; reflexivity|exact HC].
Qed.
(* [comment removed for export] *)
Definition br_nl (bc : bctx) (c : bcache) (B : expr) : option (Z * Z) * bcache :=
  let '(bi, c') := bget bc c B in (bi_er bi, c').
Definition base_range_c (bc : bctx) (c : bcache) (B : expr) : option (Z * Z) * bcache :=
  match B with
  | ELit _ => (base_rangeB bc B, c)
  | _ => br_nl bc c B
  end.
Lemma br_nl_spec : forall bc c B, BCOK bc c -> is_lit B = None ->
  fst (br_nl bc c B) = base_rangeB bc B /\ BCOK bc (snd (br_nl bc c B)).
Proof.
  intros bc c B HC HL. unfold br_nl. destruct (bget_spec bc c B HC) as [G1 G2].
  destruct (bget bc c B) as [bi c']. cbn [fst snd] in *. subst bi. split; [|exact G2].
  rewrite bi_er_eq. destruct B; try reflexivity. discriminate.
Qed.
(* [comment removed for export] *)
Definition base_range63_c (bc : bctx) (c : bcache) (B : expr) : option (Z * Z) * option (PrimInt63.int * PrimInt63.int) * bcache :=
  match B with
  | ELit _ => (base_rangeB bc B, None, c)
  | _ => let '(bi, c') := bget bc c B in (bi_er bi, bi_e63 bi, c')
  end.
Lemma bi_e63_eq : forall bc B, bi_e63 (mk_binfo bc B) = rng63 (erangeB bc B).
Proof. intros. unfold mk_binfo. rewrite ?erangeBF_fe, ?erange_fBF_fe. cbv zeta. destruct (nf_test _ _ _); reflexivity. Qed.
Lemma base_range63_c_spec : forall bc c B, BCOK bc c ->
  fst (fst (base_range63_c bc c B)) = base_rangeB bc B
  /\ (snd (fst (base_range63_c bc c B)) = None \/ snd (fst (base_range63_c bc c B)) = rng63 (base_rangeB bc B))
  /\ BCOK bc (snd (base_range63_c bc c B)).
Proof.
  intros bc c B HC. unfold base_range63_c.
  assert (G : forall B', is_lit B' = None ->
            fst (fst (let '(bi, c') := bget bc c B' in (bi_er bi, bi_e63 bi, c'))) = base_rangeB bc B'
            /\ (snd (fst (let '(bi, c') := bget bc c B' in (bi_er bi, bi_e63 bi, c'))) = None
                \/ snd (fst (let '(bi, c') := bget bc c B' in (bi_er bi, bi_e63 bi, c'))) = rng63 (base_rangeB bc B'))
            /\ BCOK bc (snd (let '(bi, c') := bget bc c B' in (bi_er bi, bi_e63 bi, c')))).
  { intros B' HL. destruct (bget_spec bc c B' HC) as [G1 G2]. destruct (bget bc c B') as [bi c']. cbn [fst snd] in *. subst bi.
    rewrite bi_er_eq, bi_e63_eq. assert (E : base_rangeB bc B' = erangeB bc B') by (destruct B'; try reflexivity; discriminate).
    rewrite E. split; [reflexivity|]. split; [right; reflexivity|exact G2]. }
  destruct B; try (apply G; reflexivity).
  cbn [fst snd]. split; [reflexivity|]. split; [left; reflexivity|exact HC].
Qed.
Lemma base_range_c_spec : forall bc c B, BCOK bc c ->
  fst (base_range_c bc c B) = base_rangeB bc B /\ BCOK bc (snd (base_range_c bc c B)).
Proof.
  intros bc c B HC. unfold base_range_c.
  destruct B; try (apply br_nl_spec; [exact HC|reflexivity]).
  split; [reflexivity|exact HC].
Qed.
(* [comment removed for export] *)
Definition fold_nl0 (bc : bctx) (c : bcache) (e : expr) (B : expr) (k : Z) : expr * bcache :=
  let '(bi, c') := bget bc c B in
  if bi_nf bi then
    if (if hask e then Z.eqb k 0 else false) then (foldKBG bc e, c')
    else
      let cc := if hask e then k else 0 in
      let r := bsum_range bc bi cc in
      match r with
      | Some (lo, hi) =>
          if Z.eqb lo hi then (ELit lo, c')
          else if bsum_noconc bi cc r then (e, c') else (foldKBG bc e, c')
      | None => if bsum_noconc bi cc r then (e, c') else (foldKBG bc e, c')
      end
  else (foldKBG bc e, c').
Definition fold_nl (bc : bctx) (c : bcache) (e : expr) (B : expr) (k : Z) : expr * bcache :=
  let '(bi, c') := bget bc c B in
  if bi_nf bi then
    if (if hask e then Z.eqb k 0 else false) then (foldKBG bc e, c')
    else
      let cc := if hask e then k else 0 in
      match rfast bc bi cc with
      | Some w => if (if bi_W bi then w else false) then (e, c') else (foldKBG bc e, c')
      | None =>
          let r := bsum_range bc bi cc in
          match r with
          | Some (lo, hi) =>
              if Z.eqb lo hi then (ELit lo, c')
              else if bsum_noconc bi cc r then (e, c') else (foldKBG bc e, c')
          | None => if bsum_noconc bi cc r then (e, c') else (foldKBG bc e, c')
          end
      end
  else (foldKBG bc e, c').
Definition foldKB_c (bc : bctx) (c : bcache) (e : expr) : expr * bcache :=
  match e with
  | ELit _ => (e, c)
  | _ => let '(B, k) := split_lit e in
         match B with
         | ELit _ => (foldKBG bc e, c)
         | _ => fold_nl bc c e B k
         end
  end.
Lemma fold_nl0_spec : forall bc c e B k, BCOK bc c -> split_lit e = (B, k) -> is_lit B = None ->
  fst (fold_nl0 bc c e B k) = foldKB bc e /\ BCOK bc (snd (fold_nl0 bc c e B k)).
Proof.
  intros bc c e B k HC ES HL. unfold fold_nl0. rewrite foldKBG_eq. destruct (bget_spec bc c B HC) as [G1 G2].
  destruct (bget bc c B) as [bi c']. cbn [fst snd] in G1, G2. subst bi.
  destruct (bi_nf (mk_binfo bc B)) eqn:NF; [|split; [reflexivity|exact G2]].
  destruct (nf_spec bc B NF) as (_ & _ & _ & _ & CL & _).
  destruct (if hask e then Z.eqb k 0 else false) eqn:HZ; [split; [reflexivity|exact G2]|]. cbv zeta.
  set (cc := if hask e then k else 0).
  assert (EB : e = bsum B cc).
  { unfold cc, bsum. destruct (split_lit_shape e B k ES HL) as [[HK ->]|[HK [-> ->]]]; rewrite HK in *.
    - rewrite HZ. reflexivity.
    - reflexivity. }
  assert (FE : foldKB bc e = match erangeB bc e with
                            | Some (lo, hi) => if Z.eqb lo hi then ELit lo else match concretizeB bc e with Some v => ELit v | None => e end
                            | None => match concretizeB bc e with Some v => ELit v | None => e end
                            end) by (rewrite EB; apply (foldKB_bsum bc B cc CL)).
  assert (RE : bsum_range bc (mk_binfo bc B) cc = erangeB bc e) by (rewrite EB; apply (bsum_range_eq bc B cc NF)).
  assert (NCE : bsum_noconc (mk_binfo bc B) cc (erangeB bc e) = true -> concretizeB bc e = None).
  { intros NC. rewrite EB in *. apply (conc_none bc B cc NF). exact NC. }
  rewrite FE, RE. clear FE RE EB.
  destruct (erangeB bc e) as [[lo hi]|].
  - destruct (Z.eqb lo hi); [split; [reflexivity|exact G2]|].
    destruct (bsum_noconc (mk_binfo bc B) cc (Some (lo, hi))) eqn:NC; [|split; [reflexivity|exact G2]].
    rewrite (NCE eq_refl). split; [reflexivity|exact G2].
  - destruct (bsum_noconc (mk_binfo bc B) cc None) eqn:NC; [|split; [reflexivity|exact G2]].
    rewrite (NCE eq_refl). split; [reflexivity|exact G2].
Qed.
Lemma fold_nl_eq0 : forall bc c e B k, BCOK bc c -> fold_nl bc c e B k = fold_nl0 bc c e B k.
Proof.
  intros bc c e B k HC. unfold fold_nl, fold_nl0. destruct (bget_spec bc c B HC) as [G1 G2].
  destruct (bget bc c B) as [bi c']. cbn [fst snd] in G1, G2. subst bi.
  destruct (bi_nf (mk_binfo bc B)); [|reflexivity].
  destruct (if hask e then Z.eqb k 0 else false); [reflexivity|]. cbv zeta.
  destruct (rfast bc (mk_binfo bc B) (if hask e then k else 0)) as [w|] eqn:RF; [|reflexivity].
  destruct (rfast_spec bc B _ w RF) as (lo & hi & R1 & R2 & R3). rewrite R1, R2, R3. reflexivity.
Qed.
Lemma fold_nl_spec : forall bc c e B k, BCOK bc c -> split_lit e = (B, k) -> is_lit B = None ->
  fst (fold_nl bc c e B k) = foldKB bc e /\ BCOK bc (snd (fold_nl bc c e B k)).
Proof. intros bc c e B k HC ES HL. rewrite (fold_nl_eq0 bc c e B k HC). apply fold_nl0_spec; assumption. Qed.

Lemma foldKB_c_spec : forall bc c e, BCOK bc c -> fst (foldKB_c bc c e) = foldKB bc e /\ BCOK bc (snd (foldKB_c bc c e)).
Proof.
  intros bc c e HC. unfold foldKB_c.
  destruct e; try (split; [reflexivity|exact HC]);
    (destruct (split_lit _) as [B k0] eqn:ES; destruct B; try (apply fold_nl_spec; [exact HC|exact ES|reflexivity]); split; [cbn [fst]; rewrite ?foldKBG_eq; reflexivity|exact HC]).
Qed.
(* [comment removed for export] *)
Definition erange_h (bc : bctx) (c : bcache) (e : expr) : option (Z * Z) :=
  match e with
  | ELit _ => erangeBF bc e
  | _ => let '(B, k) := split_lit e in
         match B with
         | ELit _ => erangeBF bc e
         | _ => match bfind c B with
                | Some bi =>
                    if bi_nf bi then
                      if (if hask e then Z.eqb k 0 else false) then erangeBF bc e
                      else bsum_range bc bi (if hask e then k else 0)
                    else erangeBF bc e
                | None => erangeBF bc e
                end
         end
  end.
Lemma erange_h_eq : forall bc c e, BCOK bc c -> erange_h bc c e = erangeB bc e.
Proof.
  intros bc c e HC. unfold erange_h. rewrite erangeBF_fe.
  destruct e; try reflexivity;
    (destruct (split_lit _) as [B k0] eqn:ES; destruct B; try reflexivity;
     match goal with |- context [bfind c ?b] => destruct (bfind c b) as [bi|] eqn:F; [|reflexivity];
       pose proof (bfind_spec bc c b bi HC F) as EB0; subst bi;
       destruct (bi_nf (mk_binfo bc b)) eqn:NF; [|reflexivity];
       match goal with |- context [if hask ?e0 then Z.eqb k0 0 else false] =>
         destruct (if hask e0 then Z.eqb k0 0 else false) eqn:HZ; [reflexivity|];
         assert (EB : e0 = bsum b (if hask e0 then k0 else 0));
         [ unfold bsum; destruct (split_lit_shape e0 b k0 ES eq_refl) as [[HK EE]|[HK [EE1 EE2]]]; rewrite HK in *;
           [ rewrite HZ; exact EE | rewrite EE2 in *; cbn [Z.eqb]; exact EE1 ]
         | rewrite EB at 2; apply (bsum_range_eq bc b _ NF) ]
       end
     end).
Qed.
End BASF.
End Boott1m.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Booteo9.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bootx2q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Boot1pr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bootha0.Boott1m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Booteo9.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.


(* [comment removed for export] *)
Module EXI.
Import PrimInt63.
Definition B61 : int := 2305843009213693952%uint63.
Definition i0 : int := 0%uint63.
End EXI.

Module EXF.
Import AX2. Import AX2B. Import CARF. Import BFXP.

(* [comment removed for export] *)
Definition rel_litF (rb : expr) (rk : Z) (rn : Z) (kb : expr) (kk : Z) (kn : Z) : rangerel :=
  if BASF.expr_eqbF rb kb then
    if (if Z.leb kk rk then Z.leb (rk + rn) (kk + kn) else false) then RInside (rk - kk)
    else if (if Z.leb (rk + rn) kk then true else Z.leb (kk + kn) rk) then RDisjoint
    else RPartial
  else RUnknown.

(* [comment removed for export] *)
Local Open Scope Z_scope.
(* [comment removed for export] *)
Fixpoint ctz_fuelF (fuel : nat) (z : Z) : Z :=
  match fuel with
  | O => 0%Z
  | S f => if Z.odd z then 0%Z else (1 + ctz_fuelF f (Z.div2 z))%Z
  end.
Definition ctz64F (z : Z) : Z := ctz_fuelF 64 z.
Fixpoint ealign0F (kn : list kentry) (e : expr) {struct e} : Z :=
  match find_align kn e with
  | Some m => if Z.ltb 0 m then ctz64F m else 0%Z
  | None =>
  match e with
  | ELit z => ctz64F (zmod64 z)
  | EAlu ALU_ADD a b => Z.min (ealign0F kn a) (ealign0F kn b)
  | EAlu ALU_SUB a b => Z.min (ealign0F kn a) (ealign0F kn b)
  | EAlu ALU_AND a b => Z.max (ealign0F kn a) (ealign0F kn b)
  | EAlu ALU_OR a b => Z.min (ealign0F kn a) (ealign0F kn b)
  | EAlu ALU_SLL a b =>
      match lit_shamt b with
      | Some s => Z.min (ealign0F kn a + s)%Z 64
      | None => 0%Z
      end
  | EMd M_MUL a b => Z.min (ealign0F kn a + ealign0F kn b)%Z 64
  | _ => 0%Z
  end
  end.


Definition ealignBF (bc : bctx) (e : expr) : Z := Z.max (ealign0F (bc_ffk bc) e) (pageup_align e).

(* [comment removed for export] *)
Definition modp2 (x j : Z) : Z := if Z.leb 0 j then Z.land x (Z.ones j) else (x mod 2 ^ j)%Z.
(* [comment removed for export] *)
Definition p2 (j : Z) : Z := if Z.leb 0 j then Z.shiftl 1 j else (2 ^ j)%Z.
Fixpoint lowbitsBF (bc : bctx) (e : expr) (j : Z) {struct e} : option Z :=
  let dflt := fun _ : unit => if Z.leb j (ealignBF bc e) then Some 0%Z else lin_lowbits_knB bc e j in
  match e with
  | ELit z => Some (modp2 (zmod64 z) j)
  | EAlu ALU_AND a (ELit c) =>
      if Z.eqb (modp2 (zmod64 c) j) 0 then Some 0%Z else
      match lowbitsBF bc a j with Some v => Some (Z.land v (modp2 (zmod64 c) j)) | None => dflt tt end
  | EAlu ALU_OR a (ELit c) =>
      match lowbitsBF bc a j with Some v => Some (Z.lor v (modp2 (zmod64 c) j)) | None => dflt tt end
  | EAlu ALU_XOR a (ELit c) =>
      match lowbitsBF bc a j with Some v => Some (Z.lxor v (modp2 (zmod64 c) j)) | None => dflt tt end
  | EAlu ALU_ADD a b =>
      match lowbitsBF bc a j, lowbitsBF bc b j with Some x, Some y => Some (modp2 (x + y) j) | _, _ => dflt tt end
  | EAlu ALU_SUB a b =>
      match lowbitsBF bc a j, lowbitsBF bc b j with Some x, Some y => Some (modp2 (x - y) j) | _, _ => dflt tt end
  | EMd M_MUL (ELit c) a =>
      if Z.eqb (modp2 (zmod64 c) j) 0 then Some 0%Z else
      match lowbitsBF bc a j with Some v => Some (modp2 (c * v) j) | None => dflt tt end
  | _ => dflt tt
  end.

(* [comment removed for export] *)
Definition lin_nowrapBF (bc : bctx) (e : expr) : bool :=
  let l := lin_of e in
  match lin_range (BASF.erangeBF bc) (fst l) (snd l) with
  | Some (lo, hi) => if Z.leb 0 lo then Z.ltb hi two64 else false
  | None => false
  end.
Definition lin_nowrap_lBF (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  match lin_range (BASF.erangeBF bc) c ts with
  | Some (lo, hi) => if Z.leb 0 lo then Z.ltb hi two64 else false
  | None => false
  end.
Definition mkSrlBF (bc : bctx) (a : expr) (s : Z) : expr :=
  let l := lin_of a in
  if lin_trivial l then mkAlu ALU_SRL a (ELit s) else
  let m := (2 ^ s)%Z in
  let nw := lin_nowrapBF bc a in
  if (if coeffs_div m (snd l) then nw else false)
  then unlin ((fst l / m)%Z, ldiv_terms m (snd l))
  else
    match (if nw then lsplit_divc m (snd l) else ([], [])) with
    | ((_ :: _) as dts, (_ :: _) as rts) =>
        match (if lin_nowrap_lBF bc (fst l) rts then BASF.erangeBF bc (unlin (fst l, rts)) else None) with
        | Some (lo, hi) =>
            if Z.eqb (lo / m) (hi / m) then unlin ((lo / m)%Z, ldiv_terms m dts)
            else mkAlu ALU_SRL a (ELit s)
        | None => mkAlu ALU_SRL a (ELit s)
        end
    | _ => mkAlu ALU_SRL a (ELit s)
    end.

Definition narrow_maskBF (bc : bctx) (a : expr) (k' : Z) : option Z :=
  let i := ctz64F k' in
  let pi := p2 i in
  let m := (k' + pi)%Z in
  let j := Z.log2 m in
  let pj := p2 j in
  if (if Z.ltb 0 k' then if Z.eqb m pj then Z.ltb j 64 else false else false) then
    match xhiB bc a with
    | Some h => if Z.ltb h pj then Some (two64 - pi)%Z else None
    | None => None
    end
  else None.

Definition mkAnd0BF (bc : bctx) (a b : expr) : expr :=
  match b with
  | ELit k =>
      let k' := zmod64 k in
      let j := Z.log2 (two64 - k') in
      if (if Z.eqb (two64 - k') (p2 j) then Z.ltb j 64 else false) then
        (* [comment removed for export] *)
        (if Z.leb j (ealignBF bc a) then a
         else let l := lin_of a in
              if (negb (lin_trivial l) && coeffs_divkB bc (2 ^ j) (snd l))%bool
              then unlin ((fst l - (fst l) mod 2 ^ j)%Z, snd l)
              else (* [comment removed for export] *)
                match (if lin_trivial l then ([], snd l) else lsplit_divB bc (2 ^ j) (snd l)) with
                | ((_ :: _) as dts, (_ :: _) as rts) => and_high_splitB bc b j (fst l) dts rts
                | _ => (* [comment removed for export] *)
                       mkMd M_MUL (ELit (2 ^ j)%Z) (mkSrlBF bc a j)
                end)
      else
        let j2 := Z.log2 (k' + 1) in
        if (if Z.eqb (k' + 1) (p2 j2) then Z.ltb j2 64 else false) then
          (* [comment removed for export] *)
          (if Z.leb j2 (ealignBF bc a) then ELit 0
           else match lowbitsBF bc a j2 with        (* [comment removed for export] *)
           | Some v => ELit v
           | None =>
           if lin_trivial (lin_of a) then mkAlu ALU_AND a b
           else match lin_lowbits_knB bc a j2 with
                | Some v => ELit v
                | None => (* [comment removed for export] *)
                    match lsplit_divB bc (2 ^ j2) (snd (lin_of a)) with
                    | (_ :: _, (_ :: _) as rts) => and_low_splitB bc b j2 (fst (lin_of a)) rts
                    | _ => mkAlu ALU_AND a b
                    end
                end
           end)
        else (* [comment removed for export] *)
          let j3 := (Z.log2 k' + 1)%Z in
          if (Z.ltb 0 k' && Z.leb j3 64 && negb (lin_trivial (lin_of a)))%bool then
            match lin_lowbits_knB bc a j3 with
            | Some v => ELit (Z.land v k')
            | None => mkAlu ALU_AND a b
            end
          else mkAlu ALU_AND a b
  | _ => mkAlu ALU_AND a b
  end.

Definition mkAndBF (bc : bctx) (a b : expr) : expr :=
  match b with
  | ELit k =>
      match narrow_maskBF bc a (zmod64 k) with
      | Some m => mkAnd0BF bc a (ELit m)
      | None => mkAnd0BF bc a b
      end
  | _ => mkAnd0BF bc a b
  end.

Definition mkAndKBF (bc : bctx) (a b : expr) : expr :=
  match a, b with
  | EAlu ALU_AND x (ELit m1), ELit k => mkAndBF bc x (ELit (Z.land (zmod64 m1) (zmod64 k))%Z)
  | EMd M_MUL (ELit m) (EAlu ALU_SRL x (ELit i)), ELit k =>
      (* [comment removed for export] *)
      let i' := ((i mod two64) mod 64)%Z in
      if Z.eqb (m mod two64) (2 ^ i') then mkAndBF bc x (ELit (Z.land (two64 - 2 ^ i') (k mod two64))%Z)
      else mkAndBF bc a b
  | _, _ => mkAndBF bc a b
  end.

Definition or_disjointBF (bc : bctx) (a b : expr) : bool :=
  match BASF.erangeBF bc b with
  | Some (lo, hi) => if Z.leb 0 lo then Z.ltb hi (2 ^ (ealignBF bc a)) else false
  | None => false
  end.
Definition mkOrBF (bc : bctx) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zalu ALU_OR x y)
  | _, _ =>
      if or_disjointBF bc a b then mkAlu ALU_ADD a b
      else if or_disjointBF bc b a then mkAlu ALU_ADD a b
      else match b with
           | ELit c => mkAlu ALU_ADD (mkAndKBF bc a (ELit (Z.lnot (c mod two64)))) (ELit c)
           | _ => match a with
                  | ELit c => mkAlu ALU_ADD (mkAndKBF bc b (ELit (Z.lnot (c mod two64)))) (ELit c)
                  | _ => EAlu ALU_OR a b
                  end
           end
  end.

Definition mkAluK0BF (bc : bctx) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_SLTU => mkSltB bc BC_LTU ALU_SLTU a b
  | ALU_SLT => mkSltB bc BC_LT ALU_SLT a b
  | ALU_AND => match a, b with
               | ELit _, ELit _ => mkAndBF bc a b
               | ELit _, _ => mkAndKBF bc b a      (* [comment removed for export] *)
               | _, _ => mkAndKBF bc a b
               end
  | ALU_OR => if BASF.expr_eqbF a b then a else mkOrBF bc a b
  | ALU_XOR => if BASF.expr_eqbF a b then ELit 0 else match is_lit a, b with
               | None, ELit k => if Z.eqb (zmod64 k) (two64 - 1) then mkAlu ALU_SUB (ELit (two64 - 1)) a
                                else mkAlu op a b
               | _, _ => BASF.mkAluL op a b
               end
  | ALU_SRL => match is_lit a, shamt_of b 6 with
               | None, Some s => mkSrlBF bc a s
               | _, _ => mkAlu op a b
               end
  | _ => BASF.mkAluL op a b
  end.

Definition mkAluKBF (bc : bctx) (op : aluop) (a b : expr) : expr :=
  BASF.foldKBG bc (mkAluK0BF bc op a b).

Definition mkMdKBF (bc : bctx) (op : mulop) (a b : expr) : expr :=
  match is_lit a, op, b with
  | None, M_REMU, ELit m =>
      match pow2_log m with
      | Some k => mkAluKBF bc ALU_AND a (ELit (2 ^ k - 1))
      | None => mkMd op a b
      end
  | None, M_DIVU, ELit m =>
      match pow2_log m with
      | Some k => mkAluKBF bc ALU_SRL a (ELit k)
      | None => mkMd op a b
      end
  | _, _, _ => mkMd op a b
  end.

Definition amo_newvalBF (bc : bctx) (wd : awidth) (aop : option aluop) (old src : expr) : expr :=
  match aop with
  | None => src
  | Some o => match wd with AW => mkAluwKB bc o old src | AD => mkAluKBF bc o old src end
  end.

Local Close Scope Z_scope.

(* [comment removed for export] *)
Definition ranges_apartBF (bc : bctx) (kd : list kentry) (br1 : option (Z * Z)) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match br1, base_rangeB bc b2 with
      | Some (lo1, hi1), Some (lo2, hi2) => if Z.leb (hi1 + k1 + n1) (lo2 + k2) then true else Z.leb (hi2 + k2 + n2) (lo1 + k1)
      | _, _ => false
      end)%Z then true
  else if kdisj_apartB bc kd b1 k1 n1 b2 k2 n2 then true
  else lin_apartB bc b1 k1 n1 b2 k2 n2.
Fixpoint log_lookupBF (bc : bctx) (kd : list kentry) (obr : option (option (Z * Z))) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_litF rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupBF bc kd obr rest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let br1 := match obr with Some r => r | None => base_rangeB bc rb end in
          if ranges_apartBF bc kd br1 rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupBF bc kd (Some br1) rest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupBF bc kd (Some br1) rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ranges_apartBF2 (bc : bctx) (kd : list kentry) (sp : sprep) (br1 : option (Z * Z)) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match br1, sp_rng sp with
      | Some (lo1, hi1), Some (lo2, hi2) => if Z.leb (hi1 + k1 + n1) (lo2 + k2) then true else Z.leb (hi2 + k2 + n2) (lo1 + k1)
      | _, _ => false
      end)%Z then true
  else if (if Z.eqb (zlit64 n2) n2 then in_sidesB bc (sp_D sp) b1 k1 n1 else kdisj_apartB bc kd b1 k1 n1 b2 k2 n2) then true
  else lin_apartB bc b1 k1 n1 b2 k2 n2.
Fixpoint log_lookupBF2 (bc : bctx) (kd : list kentry) (obr : option (option (Z * Z))) (log : list sentry) (lis : list sprep) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log, lis with
  | [], _ => LMiss acc hints
  | SE (SA kb kk) w v :: rest, li :: lrest =>
      match rel_litF rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupBF2 bc kd obr rest lrest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let br1 := match obr with Some r => r | None => base_rangeB bc rb end in
          if ranges_apartBF2 bc kd li br1 rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupBF2 bc kd (Some br1) rest lrest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupBF2 bc kd (Some br1) rest lrest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  | _ :: _, [] => log_lookupBF bc kd obr log rb rk n sx hints acc       (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zb (z : Z) : option PrimInt63.int := BASF.zb z.      (* [comment removed for export] *)
(* [comment removed for export] *)
Record sann : Type := SAN { sa_zw : Z; sa_rng : option (PrimInt63.int * PrimInt63.int) }.
Definition sann_sp (sp : sprep) (e : sentry) : sann :=
  let zw := Z.of_nat (e_width e) in
  SAN zw (match sp_rng sp with
          | Some (lo2, hi2) =>
              match zb (lo2 + a_off (e_addr e))%Z, zb (hi2 + a_off (e_addr e) + zw)%Z with
              | Some x, Some y => Some (x, y)
              | _, _ => None
              end
          | None => None
          end).
Definition rann (br1 : option (Z * Z)) (rk n : Z) : option (PrimInt63.int * PrimInt63.int) :=
  match br1 with
  | Some (lo1, hi1) =>
      match zb (lo1 + rk)%Z, zb (hi1 + rk + n)%Z with
      | Some x, Some y => Some (x, y)
      | _, _ => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition rann63 (e63 : option (PrimInt63.int * PrimInt63.int)) (br1 : option (Z * Z)) (rk n : Z) : option (PrimInt63.int * PrimInt63.int) :=
  match e63 with
  | Some (lo63, hi63) =>
      match zb rk, IMGF.z61 n with
      | Some k63, Some n63 =>
          Some (PrimInt63.sub (PrimInt63.add lo63 k63) EXI.B61, PrimInt63.add (PrimInt63.sub (PrimInt63.add hi63 k63) EXI.B61) n63)
      | _, _ => rann br1 rk n
      end
  | None => rann br1 rk n
  end.
Definition i63apart (ra sa : option (PrimInt63.int * PrimInt63.int)) : bool :=
  match ra, sa with
  | Some (rlo, rhi), Some (slo, shi) => if PrimInt63.leb rhi slo then true else PrimInt63.leb shi rlo
  | _, _ => false
  end.
Fixpoint log_lookupBF3 (bc : bctx) (kd : list kentry) (br1 : option (Z * Z)) (ra : option (PrimInt63.int * PrimInt63.int))
         (log : list sentry) (lis : list sprep) (lia : list sann)
         (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match log, lis, lia with
  | [], _, _ => LMiss acc hints
  | SE (SA kb kk) w v :: rest, li :: lrest, sa :: arest =>
      match rel_litF rb rk zn kb kk (sa_zw sa) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupBF3 bc kd br1 ra rest lrest arest rb rk n zn sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          if (if i63apart ra (sa_rng sa) then true else ranges_apartBF2 bc kd li br1 rb rk zn kb kk (sa_zw sa))
          then log_lookupBF3 bc kd br1 ra rest lrest arest rb rk n zn sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupBF3 bc kd br1 ra rest lrest arest rb rk n zn sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  | _, _, _ => log_lookupBF2 bc kd (Some br1) log lis rb rk n sx hints acc       (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ivof (k w : Z) : option (PrimInt63.int * PrimInt63.int) :=
  match zb k, IMGF.z61 w with
  | Some s, Some w63 => Some (s, PrimInt63.add s w63)
  | _, _ => None
  end.
Record lent : Type := LE { le_k : Z; le_zw : Z; le_w : nat; le_v : expr; le_iv : option (PrimInt63.int * PrimInt63.int) }.
(* [comment removed for export] *)
Definition ibucket (idx : ptree (list lent)) (k : Z) : list lent := match pt_get idx (kx_gkey k) with Some l => l | None => [] end.
Definition idx_add (idx : ptree (list lent)) (en : lent) : ptree (list lent) :=
  pt_set (kx_gkey (le_k en)) (en :: ibucket idx (le_k en)) idx.
Record lgroup : Type := LG { lg_b : expr; lg_hull : option (PrimInt63.int * PrimInt63.int); lg_es : list lent;
                             lg_cnt : Z; lg_wmax : Z; lg_idx : ptree (list lent) }.
Definition hull_join (h r : option (PrimInt63.int * PrimInt63.int)) : option (PrimInt63.int * PrimInt63.int) :=
  match h, r with
  | Some (a, b), Some (c, d) => Some (if PrimInt63.ltb c a then c else a, if PrimInt63.ltb b d then d else b)
  | _, _ => None
  end.
Fixpoint gl_add (gl : list lgroup) (kb : expr) (en : lent) (rng : option (PrimInt63.int * PrimInt63.int)) : list lgroup :=
  match gl with
  | [] => [LG kb rng [en] 1 (le_zw en) (idx_add PTLeaf en)]
  | g :: r => if BASF.expr_eqbF kb (lg_b g)
              then LG (lg_b g) (hull_join (lg_hull g) rng) (en :: lg_es g) (lg_cnt g + 1)%Z (Z.max (lg_wmax g) (le_zw en)) (idx_add (lg_idx g) en) :: r
              else g :: gl_add r kb en rng
  end.
Definition gl_adde (gl : list lgroup) (e : sentry) (sa : sann) : list lgroup :=
  gl_add gl (a_base (e_addr e)) (LE (a_off (e_addr e)) (sa_zw sa) (e_width e) (e_val e) (ivof (a_off (e_addr e)) (sa_zw sa))) (sa_rng sa).
Fixpoint GLof (f : sentry -> sprep) (log : list sentry) : list lgroup :=
  match log with
  | [] => []
  | e :: rest => gl_adde (GLof f rest) e (sann_sp (f e) e)
  end.
Fixpoint gl_others_apart (gl : list lgroup) (rb : expr) (ra : option (PrimInt63.int * PrimInt63.int)) : bool :=
  match gl with
  | [] => true
  | g :: r => if BASF.expr_eqbF rb (lg_b g) then gl_others_apart r rb ra
              else if i63apart ra (lg_hull g) then gl_others_apart r rb ra else false
  end.
Fixpoint gl_find (gl : list lgroup) (rb : expr) : list lent :=
  match gl with
  | [] => []
  | g :: r => if BASF.expr_eqbF rb (lg_b g) then lg_es g else gl_find r rb
  end.
Fixpoint le_scan (es : list lent) (rk zn : Z) (n : nat) (sx : bool) (hints : list bool) : option lres :=
  match es with
  | [] => Some (LMiss [] hints)
  | LE kk zw w v _ :: r =>
      if (if Z.leb kk rk then Z.leb (rk + zn) (kk + zw) else false)%Z then Some (LHit (mkExt sx (Z.to_nat (rk - kk)) n v) [] hints)
      else if (if Z.leb (rk + zn) kk then true else Z.leb (kk + zw) rk)%Z then le_scan r rk zn n sx hints
      else None
  end.
Fixpoint le_scanI (es : list lent) (qi : option (PrimInt63.int * PrimInt63.int)) (rk zn : Z) (n : nat) (sx : bool) (hints : list bool) : option lres :=
  match es with
  | [] => Some (LMiss [] hints)
  | LE kk zw w v iv :: r =>
      match iv, qi with
      | Some (s, e), Some (q, qe) =>
          if (if PrimInt63.leb s q then PrimInt63.leb qe e else false) then Some (LHit (mkExt sx (Z.to_nat (rk - kk)) n v) [] hints)
          else if (if PrimInt63.leb qe s then true else PrimInt63.leb e q) then le_scanI r qi rk zn n sx hints
          else None
      | _, _ =>
          if (if Z.leb kk rk then Z.leb (rk + zn) (kk + zw) else false)%Z then Some (LHit (mkExt sx (Z.to_nat (rk - kk)) n v) [] hints)
          else if (if Z.leb (rk + zn) kk then true else Z.leb (kk + zw) rk)%Z then le_scanI r qi rk zn n sx hints
          else None
      end
  end.
Fixpoint gl_findg (gl : list lgroup) (rb : expr) : option lgroup :=
  match gl with
  | [] => None
  | g :: r => if BASF.expr_eqbF rb (lg_b g) then Some g else gl_findg r rb
  end.
Definition le_disj (e : lent) (rk zn : Z) : bool := (if Z.leb (rk + zn) (le_k e) then true else Z.leb (le_k e + le_zw e) rk)%Z.
Fixpoint bucket_clear (l : list lent) (rk zn : Z) : bool :=
  match l with [] => true | e :: r => if le_disj e rk zn then bucket_clear r rk zn else false end.
Fixpoint win_clear (idx : ptree (list lent)) (k : Z) (cnt : nat) (rk zn : Z) : bool :=
  match cnt with
  | O => true
  | S c => if bucket_clear (ibucket idx k) rk zn then win_clear idx (k + 1)%Z c rk zn else false
  end.
Definition grp_miss (g : lgroup) (rk zn : Z) : bool :=
  (if Z.ltb 24 (lg_cnt g) then if Z.ltb 0 zn then if Z.ltb 0 (lg_wmax g) then if Z.ltb (lg_wmax g) 65 then
     win_clear (lg_idx g) (rk - lg_wmax g + 1) (Z.to_nat (lg_wmax g + zn - 1)) rk zn
   else false else false else false else false)%Z.
Definition grp_scan (gl : list lgroup) (rb : expr) (rk zn : Z) (n : nat) (sx : bool) (hints : list bool) : option lres :=
  match gl_findg gl rb with
  | Some g => if grp_miss g rk zn then Some (LMiss [] hints) else le_scanI (lg_es g) (ivof rk zn) rk zn n sx hints
  | None => Some (LMiss [] hints)
  end.
Definition log_lookupG (bc : bctx) (kd : list kentry) (br1 : option (Z * Z)) (ra : option (PrimInt63.int * PrimInt63.int))
           (gl : list lgroup) (log : list sentry) (lis : list sprep) (lia : list sann)
           (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool) (hints : list bool) : lres :=
  match (if gl_others_apart gl rb ra then grp_scan gl rb rk zn n sx hints else None) with
  | Some r => r
  | None => log_lookupBF3 bc kd br1 ra log lis lia rb rk n zn sx hints []
  end.

(* [comment removed for export] *)
Fixpoint wr_numB (bc : bctx) (kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (if BASF.expr_eqbF (a_base a) kb then Z.leb kk (a_off a) else false) then
        match xloB bc len with
        | Some l => if Z.leb (a_off a + Z.of_nat n) (kk + l) then true else wr_numB bc rest a n
        | None => wr_numB bc rest a n
        end
      else wr_numB bc rest a n
  | _ :: rest => wr_numB bc rest a n
  end.
Definition storeok_scBF (bc : bctx) (ex : bext) (a : saddr) (n : nat) : list sidecond :=
  if (if wr_numB bc (be_kw ex) a n then true else wr_coveredB bc (be_kw ex) a n) then [] else [SCStoreOk a n].

(* [comment removed for export] *)
Fixpoint know_lookupA0F (bc : bctx) (st : option (list IMGF.sgi)) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (zn : Z) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupA0F bc st in
  match kn with
  | [] => LMiss acc hints
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w v =>
          if BASF.expr_eqbF rb kb then
            (if (if Z.leb kk rk then Z.leb (rk + zn) (kk + Z.of_nat w) else false) then LHit (mkExt sx (Z.to_nat (rk - kk)) n v) acc hints
             else know_lookup segs rest rb rk n zn sx hints acc)
          else know_lookup segs rest rb rk n zn sx hints acc
      | KZero (SA kb kk) len =>
          match len with
          | ELit l0 =>
              if BASF.expr_eqbF rb kb then
                (if (if Z.leb kk rk then Z.leb (rk + zn) (kk + zmod64 l0) else false) then LHit (ELit 0) acc hints
                 else know_lookup segs rest rb rk n zn sx hints acc)
              else
                  (* [comment removed for export] *)
                  if xinsideB bc rb rk (ELit zn) kb kk len then LHit (ELit 0) acc hints else
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n zn sx hs acc
                  | [] => know_lookup segs rest rb rk n zn sx [] acc
                  end
          | _ =>
              if xinsideB bc rb rk (ELit zn) kb kk len then LHit (ELit 0) acc hints else
              match hints with
              | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n zn sx hs acc
              | [] => know_lookup segs rest rb rk n zn sx [] acc
              end
          end
      | KFill (SA kb kk) len c =>
          (* [comment removed for export] *)
          match len with
          | ELit l0 =>
              if BASF.expr_eqbF rb kb then
                (if (if Z.leb kk rk then Z.leb (rk + zn) (kk + zmod64 l0) else false) then LHit (fill_lit sx n c) acc hints
                 else know_lookup segs rest rb rk n zn sx hints acc)
              else
                  if xinsideB bc rb rk (ELit zn) kb kk len then LHit (fill_lit sx n c) acc hints else
                  match hints with
                  | true :: hs => LHit (fill_lit sx n c) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n zn sx hs acc
                  | [] => know_lookup segs rest rb rk n zn sx [] acc
                  end
          | _ =>
              if xinsideB bc rb rk (ELit zn) kb kk len then LHit (fill_lit sx n c) acc hints else
              match hints with
              | true :: hs => LHit (fill_lit sx n c) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n zn sx hs acc
              | [] => know_lookup segs rest rb rk n zn sx [] acc
              end
          end
      | KUnk _ _ => know_lookup segs rest rb rk n zn sx hints acc   (* [comment removed for export] *)
      | KBlob (SA kb kk) len k =>
          if BASF.expr_eqbF rb kb then
            (* [comment removed for export] *)
            if Z.leb kk rk then
              match len with
              | ELit l0 =>
                  if Z.leb (rk + zn) (kk + (zmod64 l0))
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + (zmod64 l0)) rk then know_lookup segs rest rb rk n zn sx hints acc
                  else LStuck
              | _ =>
                  (* [comment removed for export] *)
                  if match erangeB bc len with   (* [comment removed for export] *)
                     | Some (lo, _) => Z.leb (rk + zn) (kk + lo)
                     | None => false
                     end
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else
                  match hints with
                  | true :: hs => LHit (EBlob sx k (rk - kk) n)
                                    (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n zn sx hs acc
                  | [] => know_lookup segs rest rb rk n zn sx [] acc
                  end
              end
            else know_lookup segs rest rb rk n zn sx hints acc
          else know_lookup segs rest rb rk n zn sx hints acc
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (if Z.leb lo rk then Z.leb (rk + zn) hi else false) then
                match IMGF.img_bytesFF st segs rk n with
                | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                | None => LStuck
                end
              else know_lookup segs rest rb rk n zn sx hints acc
          | _ => know_lookup segs rest rb rk n zn sx hints acc
          end
      | KAlign _ _ => know_lookup segs rest rb rk n zn sx hints acc
      | KRange _ _ _ => know_lookup segs rest rb rk n zn sx hints acc
      | KWr _ _ => know_lookup segs rest rb rk n zn sx hints acc
      | KDisj _ _ _ _ => know_lookup segs rest rb rk n zn sx hints acc
      end
  end.



(* [comment removed for export] *)
Definition annw (K : kentry) : option (PrimInt63.int * PrimInt63.int) :=
  match K with
  | KWord (SA _ kk) w _ =>
      match zb kk, IMGF.z61 (Z.of_nat w) with
      | Some s, Some w63 => Some (s, PrimInt63.add s w63)
      | _, _ => None
      end
  | _ => None
  end.
Definition qann (rk zn : Z) : option (PrimInt63.int * PrimInt63.int) :=
  match zb rk, IMGF.z61 zn with Some a, Some b => Some (a, b) | _, _ => None end.
(* [comment removed for export] *)
Definition keepL (K : kentry) : bool :=
  match K with
  | KZero (SA kb _) _ | KFill (SA kb _) _ _ => novars kb
  | _ => true
  end.
Record xctx : Type := XC { xc_st : option (list IMGF.sgi); xc_fw : list (option (PrimInt63.int * PrimInt63.int) * kentry);
                           xc_w0 : list (positive * kentry) }.
Definition mk_xc (segs : list Segment) (kx : kix) : xctx :=
  XC (IMGF.mk_stab segs) (List.map (fun K => (annw K, K)) (kx_wf kx)) (List.filter (fun t => keepL (snd t)) (kx_w0 kx)).

(* [comment removed for export] *)
Definition xinside_numBr (bc : bctx) (br1 : option (Z * Z)) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xloB bc b2, xhiB bc b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match br1, xhiB bc n1, xloB bc n2 with
        | Some (lo1, hi1), Some h1, Some l2 => (Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2))%bool%Z
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
Definition xinsideBr (bc : bctx) (br1 : option (Z * Z)) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if shares_var b1 b2 then xinside0B bc b1 k1 n1 b2 k2 n2
  else if novars b2 then xinside_numBr bc br1 k1 n1 b2 k2 n2 else false.
(* [comment removed for export] *)
Local Open Scope Z_scope.
Definition kstepF (bc : bctx) (st : option (list IMGF.sgi)) (segs : list Segment) (br : option (Z * Z)) (K : kentry) (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool)
           (acc : list sidecond) (k : unit -> lres) : lres :=
  match K with
  | KWord (SA kb kk) w v =>
      if BASF.expr_eqbF rb kb then
        (if (if Z.leb kk rk then Z.leb (rk + zn) (kk + Z.of_nat w) else false) then LHit (mkExt sx (Z.to_nat (rk - kk)) n v) acc []
         else k tt)
      else k tt
  | KZero (SA kb kk) len =>
      match len with
      | ELit l0 =>
          if BASF.expr_eqbF rb kb then
            (if (if Z.leb kk rk then Z.leb (rk + zn) (kk + zmod64 l0) else false) then LHit (ELit 0) acc [] else k tt)
          else if xinsideBr bc br rb rk (ELit zn) kb kk len then LHit (ELit 0) acc [] else k tt
      | _ => if xinsideBr bc br rb rk (ELit zn) kb kk len then LHit (ELit 0) acc [] else k tt
      end
  | KFill (SA kb kk) len c =>
      match len with
      | ELit l0 =>
          if BASF.expr_eqbF rb kb then
            (if (if Z.leb kk rk then Z.leb (rk + zn) (kk + zmod64 l0) else false) then LHit (fill_lit sx n c) acc [] else k tt)
          else if xinsideBr bc br rb rk (ELit zn) kb kk len then LHit (fill_lit sx n c) acc [] else k tt
      | _ => if xinsideBr bc br rb rk (ELit zn) kb kk len then LHit (fill_lit sx n c) acc [] else k tt
      end
  | KBlob (SA kb kk) len bk =>
      if BASF.expr_eqbF rb kb then
        if Z.leb kk rk then
          match len with
          | ELit l0 =>
              if Z.leb (rk + zn) (kk + (zmod64 l0)) then LHit (EBlob sx bk (rk - kk) n) acc []
              else if Z.leb (kk + (zmod64 l0)) rk then k tt
              else LStuck
          | _ =>
              if match erangeB bc len with
                 | Some (lo, _) => Z.leb (rk + zn) (kk + lo)
                 | None => false
                 end
              then LHit (EBlob sx bk (rk - kk) n) acc []
              else k tt
          end
        else k tt
      else k tt
  | KImg lo hi =>
      match rb with
      | ELit 0 =>
          if (if Z.leb lo rk then Z.leb (rk + zn) hi else false) then
            match IMGF.img_bytesFF st segs rk n with
            | Some bs => LHit (lit_of_bytes sx n bs) acc []
            | None => LStuck
            end
          else k tt
      | _ => k tt
      end
  | _ => k tt
  end.
Local Close Scope Z_scope.
Fixpoint kwalkfF (bc : bctx) (st : option (list IMGF.sgi)) (segs : list Segment) (br : option (Z * Z)) (l : list (option (PrimInt63.int * PrimInt63.int) * kentry))
         (r : option (PrimInt63.int * PrimInt63.int)) (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool) (acc : list sidecond) : lres :=
  match l with
  | [] => LMiss acc []
  | (a, K) :: rest =>
      if (match a, r with
          | Some (s, e), Some (r63, zn63) => if PrimInt63.leb s r63 then PrimInt63.leb (PrimInt63.add r63 zn63) e else false
          | _, _ => true
          end)
      then kstepF bc st segs br K rb rk n zn sx acc (fun _ => kwalkfF bc st segs br rest r rb rk n zn sx acc)
      else kwalkfF bc st segs br rest r rb rk n zn sx acc
  end.

Local Open Scope Z_scope.
Definition know_lookupA0IF (bc : bctx) (kx : kix) (xc : xctx) (br : option (Z * Z)) (segs : list Segment) (rb : expr) (rk : Z)
           (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match hints, n with
  | [], S _ =>
      if is_lit0 rb then know_lookupA0F bc (xc_st xc) segs (kx_merge (kx_bucket (kx_gran kx) (gran rk)) (xc_w0 xc)) rb rk n (Z.of_nat n) sx [] acc
      else let zn := Z.of_nat n in kwalkfF bc (xc_st xc) segs br (xc_fw xc) (qann rk zn) rb rk n zn sx acc
  | _, _ => know_lookupA0F bc (xc_st xc) segs (kx_kn kx) rb rk n (Z.of_nat n) sx hints acc
  end.


Definition know_lookupABIF (bc : bctx) (kx : kix) (xc : xctx) (br : option (Z * Z)) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match know_lookupA0IF bc kx xc br segs rb rk n sx hints acc with
  | LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end.

Local Close Scope Z_scope.

(* [comment removed for export] *)
Definition bv_signedG {n : N} (b : bv n) : Z :=
  let u := bv_unsigned b in let h := Z.shiftl 1 (Z.of_N n - 1) in if Z.ltb u h then u else u - Z.shiftl h 1.
(* [comment removed for export] *)
Definition bv_signedF {n : N} (b : bv n) : Z :=
  if N.eqb n 12 then let u := bv_unsigned b in if Z.ltb u 2048 then u else u - 4096
  else if N.eqb n 13 then let u := bv_unsigned b in if Z.ltb u 4096 then u else u - 8192
  else if N.eqb n 21 then let u := bv_unsigned b in if Z.ltb u 1048576 then u else u - 2097152
  else if N.eqb n 20 then let u := bv_unsigned b in if Z.ltb u 524288 then u else u - 1048576
  else bv_signedG b.

(* [comment removed for export] *)
Definition flat_scBF (bc : bctx) (a : saddr) (n : nat) : list sidecond :=
  match base_rangeB bc (a_base a) with
  | Some (lo, hi) =>
      if (if Z.leb 0 (lo + a_off a) then Z.leb (hi + a_off a + Z.of_nat n) two64 else false)%Z
      then [] else [SCFlat a (elen n)]
  | None => [SCFlat a (elen n)]
  end.

(* [comment removed for export] *)
Definition zsx32F (v : Z) : Z := zmod64 (modp2 (v + 2147483648) 32 - 2147483648)%Z.
(* [comment removed for export] *)
Definition zband32BF (bc : bctx) (d : expr) : bool :=
  let l := lin_of d in
  match lin_range (BASF.erangeBF bc) (fst l) (snd l) with
  | Some (lo, hi) => if Z.ltb (- 2 ^ 31) lo then Z.ltb hi (2 ^ 31) else false
  | None => false
  end.
Definition mkAluwK0BF (bc : bctx) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_ADD | ALU_SUB =>
      let d := mkAlu op a b in
      match is_lit d with
      | Some v => ELit (zsx32F v)
      | None => match BASF.erangeBF bc d with
                | Some (lo, hi) => if sx32_stable lo hi then d else if zband32BF bc d then d else mkAluw op a b
                | None => if zband32BF bc d then d else mkAluw op a b
                end
      end
  | _ => mkAluw op a b
  end.
Definition mkAluwKBF (bc : bctx) (op : aluop) (a b : expr) : expr := BASF.foldKBG bc (mkAluwK0BF bc op a b).
(* [comment removed for export] *)
Definition conc_exprBF (bc : bctx) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match BASF.concretizeBG bc e with Some v => ELit v | None => e end
  end.
Definition enum_branchBF (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  let '(e, pos) := cond_probe c a b in
  match BASF.concretizeBG bc e with
  | Some v => let z := Z.eqb (v mod two64) 0 in Some (if pos then negb z else z)
  | None => None
  end.

(* [comment removed for export] *)
Definition p2n5 (p : positive) : nat :=
  match p with
  | 1%positive => 1 | 2%positive => 2 | 3%positive => 3 | 4%positive => 4 | 5%positive => 5 | 6%positive => 6 | 7%positive => 7
  | 8%positive => 8 | 9%positive => 9 | 10%positive => 10 | 11%positive => 11 | 12%positive => 12 | 13%positive => 13
  | 14%positive => 14 | 15%positive => 15 | 16%positive => 16 | 17%positive => 17 | 18%positive => 18 | 19%positive => 19
  | 20%positive => 20 | 21%positive => 21 | 22%positive => 22 | 23%positive => 23 | 24%positive => 24 | 25%positive => 25
  | 26%positive => 26 | 27%positive => 27 | 28%positive => 28 | 29%positive => 29 | 30%positive => 30 | 31%positive => 31
  | _ => Pos.to_nat p
  end%nat.
Definition ridxF (r : reg) : nat := match bv_unsigned r with Zpos p => p2n5 p | _ => O end.
Definition sr_getF (sr : list expr) (r : reg) : expr := if bv_eqb r 0 then ELit 0 else nth (ridxF r) sr (ELit 0).
Definition ssetF (ss : sym_state) (rd : reg) (e : expr) (npc : Z) : sym_state :=
  SSR npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) e) (s_log ss) (s_know ss) (s_next ss) (s_resv ss).

(* [comment removed for export] *)
Definition lit_branchF (c : branch_cond) (x y : Z) : bool :=
  let x' := zmod64 x in let y' := zmod64 y in
  match c with
  | BC_EQ => Z.eqb x' y'
  | BC_NE => negb (Z.eqb x' y')
  | BC_LT => Z.ltb (zsigned64 x') (zsigned64 y')
  | BC_GE => negb (Z.ltb (zsigned64 x') (zsigned64 y'))
  | BC_LTU => Z.ltb x' y'
  | BC_GEU => negb (Z.ltb x' y')
  end.
Definition decide_branchBF (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  match a, b with
  | ELit x, ELit y => Some (lit_branchF c x y)
  | _, _ =>
      (* [comment removed for export] *)
      if BASF.expr_eqbF a b then Some (cond_on_eq c)
      else match diff_branch c a b with
           | Some t => Some t
           | None =>
             match (match BASF.erangeBF bc a, BASF.erangeBF bc b with
                    | Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
                    | _, _ => None
                    end) with
             | Some t => Some t
             | None => lin_branchB bc c a b
             end
           end
  end.

(* [comment removed for export] *)
Definition decide_branchBF_h (bc : bctx) (cache : BASF.bcache) (c : branch_cond) (a b : expr) : option bool :=
  match a, b with
  | ELit x, ELit y => Some (lit_branchF c x y)
  | _, _ =>
      if BASF.expr_eqbF a b then Some (cond_on_eq c)
      else match diff_branch c a b with
           | Some t => Some t
           | None =>
             match (match BASF.erange_h bc cache a, BASF.erange_h bc cache b with
                    | Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
                    | _, _ => None
                    end) with
             | Some t => Some t
             | None => lin_branchB bc c a b
             end
           end
  end.

Definition sym_readBIF (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookupBF2 bc (be_kd ex) None (s_log ss) lis (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scBF bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupABIF bc kx xc (base_rangeB bc (a_base a)) segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scBF bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          (* [comment removed for export] *)
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scBF bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.


(* [comment removed for export] *)
Definition flat_scBFr (br : option (Z * Z)) (a : saddr) (n : nat) : list sidecond :=
  match br with
  | Some (lo, hi) =>
      if (if Z.leb 0 (lo + a_off a) then Z.leb (hi + a_off a + Z.of_nat n) two64 else false)%Z
      then [] else [SCFlat a (elen n)]
  | None => [SCFlat a (elen n)]
  end.
(* [comment removed for export] *)
Definition flat_scBFa (ra : option (PrimInt63.int * PrimInt63.int)) (br : option (Z * Z)) (a : saddr) (n : nat) : list sidecond :=
  match ra with
  | Some (x, _) => if PrimInt63.leb EXI.B61 x then [] else [SCFlat a (elen n)]
  | None => flat_scBFr br a n
  end.
Definition sym_readBIFr (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep)
           (lia : list sann) (gl : list lgroup) (c : BASF.bcache) (scr : scripts)
           (br : option (Z * Z)) (e63 : option (PrimInt63.int * PrimInt63.int)) (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) * BASF.bcache :=
  let zn := Z.of_nat n in
  let ra := rann63 e63 br (a_off a) zn in
  match log_lookupG bc (be_kd ex) br ra gl
          (s_log ss) lis lia (a_base a) (a_off a) n zn sx' (sc_hints scr) with
  | LStuck => (None, c)
  | LHit v scs hints =>
      let '(v', c') := BASF.foldKB_c bc c (extK0B bc v) in
      (Some (v', flat_scBFa ra br a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss), c')
  | LMiss scs hints =>
      match know_lookupABIF bc kx xc br segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => (None, c)
      | LHit v scs' hints' =>
          let '(v', c') := BASF.foldKB_c bc c (extK0B bc v) in
          (Some (v', flat_scBFa ra br a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss), c')
      | LMiss scs' hints' =>
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          (Some (rv, flat_scBFa ra br a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i), c)
      end
  end.


Definition sym_stepBIF (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_getF (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (ssetF ss rd (mkAluKBF bc op (g rs) (ELit (bv_signedF imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (ssetF ss rd (mkAluKBF bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (ssetF ss rd (mkAluKBF bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (ssetF ss rd (mkAluwKBF bc ALU_ADD (g rs) (ELit (bv_signedF imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (ssetF ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (ssetF ss rd (mkAluwKBF bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (ssetF ss rd (mkMdKBF bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (ssetF ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (ssetF ss rd (ELit (zmod64 (Z.shiftl (bv_signedF imm) 12))) (p + 4)) [] scr
  | Auipc rd imm => SOk (ssetF ss rd (ELit (zmod64 (Z.shiftl (bv_signedF imm) 12 + p))) (p + 4)) [] scr
  | Jal rd imm => SOk (ssetF ss rd (ELit (p + 4)) (zmod64 (p + bv_signedF imm))) [] scr
  | Jalr rd rs1 imm =>
      match conc_exprBF bc (g rs1) with
      | ELit z => SOk (ssetF ss rd (ELit (p + 4)) (zmod64 (Z.land (zmod64 z + bv_signedF imm) (-2)))) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let a := g rs1 in let b := g rs2 in
      match match decide_branchBF bc c a b with
            | Some t => Some t
            | None => match decide_branchB bc c (conc_exprBF bc a) (conc_exprBF bc b) with
                      | Some t => Some t
                      | None => enum_branchBF bc c a b
                      end
            end with
      | Some t => SOk (sjump ss (if t then zmod64 (p + bv_signedF imm) else p + 4)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' =>
              SOk (sjump ss (if t then zmod64 (p + bv_signedF imm) else p + 4)) [SCBr t c a b]
                  (SCR dirs' (sc_reads scr) (sc_hints scr))
          end
      end
  | Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      (* [comment removed for export] *)
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bv_signedF imm) in
      match sym_readBIF segs ss bc kx xc ex lis scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrKB bc (g rs1) (bv_signedF imm) in
      match resv_inval (s_resv ss) a with
      | None => SStop
      | Some r' =>
          SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
              (flat_scBF bc a n ++ storeok_scBF bc ex a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match sym_readBIF segs ss bc kx xc ex lis scr a n (amo_sx wd) with
        | None => SStop
        | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
        end
      else SStop
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) (ELit 0))
                       (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                  (flat_scBF bc a n ++ storeok_scBF bc ex a n) scr
            else SStop   (* [comment removed for export] *)
        | None => SStop
        end
      else SStop
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => SStop
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedbB bc e wd then
            let a := to_saddrKB bc e 0 in
            match resv_inval (s_resv ss) a with
            | None => SStop
            | Some r' =>
                match sym_readBIF segs ss bc kx xc ex lis scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) vold)
                             (SE a n (amo_newvalBF bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_scBF bc ex a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.



(* [comment removed for export] *)
Definition sym_stepBIF_c (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep) (lia : list sann) (gl : list lgroup)
           (c : BASF.bcache) (segs : list Segment)
           (i : instr) (ss : sym_state) (scr : scripts) : stepres * BASF.bcache :=
  let g r := sr_getF (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm =>
      match op with
      | ALU_ADD => let '(v, c1) := BASF.mkAluKB_add_c bc c (g rs) (bv_signedF imm) in (SOk (ssetF ss rd v (p + 4)) [] scr, c1)
      | _ => (* [comment removed for export] *)
             let '(v, c1) := BASF.foldKB_c bc c (mkAluK0BF bc op (g rs) (ELit (bv_signedF imm))) in (SOk (ssetF ss rd v (p + 4)) [] scr, c1)
      end
  | ShiftImm op rd rs sh =>
      let '(v, c1) := BASF.foldKB_c bc c (mkAluK0BF bc op (g rs) (ELit (bv_unsigned sh))) in (SOk (ssetF ss rd v (p + 4)) [] scr, c1)
  | Op op rd rs1 rs2 =>
      match op, g rs2 with
      | ALU_ADD, ELit z => let '(v, c1) := BASF.mkAluKB_add_c bc c (g rs1) z in (SOk (ssetF ss rd v (p + 4)) [] scr, c1)
      | _, _ => let '(v, c1) := BASF.foldKB_c bc c (mkAluK0BF bc op (g rs1) (g rs2)) in (SOk (ssetF ss rd v (p + 4)) [] scr, c1)
      end
  | Branch cnd rs1 rs2 imm =>
      let a := g rs1 in let b := g rs2 in
      (match match decide_branchBF_h bc c cnd a b with
             | Some t => Some t
             | None => match decide_branchB bc cnd (conc_exprBF bc a) (conc_exprBF bc b) with
                       | Some t => Some t
                       | None => enum_branchBF bc cnd a b
                       end
             end with
       | Some t => SOk (sjump ss (if t then zmod64 (p + bv_signedF imm) else p + 4)) [] scr
       | None =>
           match sc_dirs scr with
           | [] => SStop
           | t :: dirs' =>
               SOk (sjump ss (if t then zmod64 (p + bv_signedF imm) else p + 4)) [SCBr t cnd a b]
                   (SCR dirs' (sc_reads scr) (sc_hints scr))
           end
       end, c)
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      let sx' := match sz with SZ8 => false | _ => sx end in
      let '(a, c1) := BASF.to_saddrKB_c bc c (g rs) (bv_signedF imm) in
      let '(br, e63, c2) := BASF.base_range63_c bc c1 (a_base a) in
      let '(r, c3) := sym_readBIFr segs ss bc kx xc ex lis lia gl c2 scr br e63 a n sx' in
      (match r with
       | None => SStop
       | Some (v, scs, scr', nx') =>
           SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) v)
                    (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
       end, c3)
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let '(a, c1) := BASF.to_saddrKB_c bc c (g rs1) (bv_signedF imm) in
      match resv_inval (s_resv ss) a with
      | None => (SStop, c1)
      | Some r' =>
          let '(br, c2) := BASF.base_range_c bc c1 (a_base a) in
          (SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
               (flat_scBFr br a n ++ storeok_scBF bc ex a n) scr, c2)
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let '(a, c1) := BASF.to_saddrKB_c bc c e 0 in
        let '(br, e63, c2) := BASF.base_range63_c bc c1 (a_base a) in
        let '(r, c3) := sym_readBIFr segs ss bc kx xc ex lis lia gl c2 scr br e63 a n (amo_sx wd) in
        (match r with
         | None => SStop
         | Some (v, scs, scr', nx') =>
             SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) v)
                      (s_log ss) (s_know ss) nx' (Some a)) scs scr'
         end, c3)
      else (SStop, c)
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedbB bc e wd then
        let '(a, c1) := BASF.to_saddrKB_c bc c e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              let '(br, c2) := BASF.base_range_c bc c1 (a_base a) in
              (SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) (ELit 0))
                        (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                   (flat_scBFr br a n ++ storeok_scBF bc ex a n) scr, c2)
            else (SStop, c1)
        | None => (SStop, c1)
        end
      else (SStop, c)
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => (SStop, c)
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedbB bc e wd then
            let '(a, c1) := BASF.to_saddrKB_c bc c e 0 in
            match resv_inval (s_resv ss) a with
            | None => (SStop, c1)
            | Some r' =>
                let '(br, e63, c2) := BASF.base_range63_c bc c1 (a_base a) in
                let '(r, c3) := sym_readBIFr segs ss bc kx xc ex lis lia gl c2 scr br e63 a n (amo_sx wd) in
                (match r with
                 | None => SStop
                 | Some (vold, scs, scr', nx') =>
                     SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) vold)
                              (SE a n (amo_newvalBF bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                         (scs ++ storeok_scBF bc ex a n) scr'
                 end, c3)
            end
          else (SStop, c)
      end
  | _ => (sym_stepBIF bc kx xc ex lis segs i ss scr, c)
  end.


(* [comment removed for export] *)
Local Open Scope Z_scope.
(* [comment removed for export] *)
Record xme : Type := XME { xe_c : saddr; xe_m : expr; xe_x : xin }.
Record xmb : Type := XMB { xb_b : expr; xb_bi : binf; xb_l : list xme }.
Definition xmemo : Type := list xmb.
Fixpoint xe_find (l : list xme) (cb : expr) (co : Z) (m : expr) : option xin :=
  match l with
  | [] => None
  | e :: r => if (if Z.eqb co (a_off (xe_c e)) then if BASF.expr_eqbF cb (a_base (xe_c e)) then BASF.expr_eqbF m (xe_m e) else false else false)
              then Some (xe_x e) else xe_find r cb co m
  end.
(* [comment removed for export] *)
Definition nwlit (bc : bctx) (n : Z) : bool := if (if Z.leb 0 n then Z.ltb n two63z else false) then true else lin_nowrapRB bc (ELit n).
Definition xb_eval (bc : bctx) (b : xmb) (k n : Z) (cb : expr) (co : Z) (m : expr) : bool * option xmb :=
  match xe_find (xb_l b) cb co m with
  | Some x => (xeval x k (snorm n) (zlit64 n) (nwlit bc n), None)
  | None => let x := mk_xin bc (xb_b b) (xb_bi b) cb co m in
            (xeval x k (snorm n) (zlit64 n) (nwlit bc n), Some (XMB (xb_b b) (xb_bi b) (XME (SA cb co) m x :: xb_l b)))
  end.
Fixpoint xm_eval (bc : bctx) (xm : xmemo) (b1 : expr) (k n : Z) (cb : expr) (co : Z) (m : expr) : bool * xmemo :=
  match xm with
  | [] => let bi := mk_binf bc b1 in let x := mk_xin bc b1 bi cb co m in
          (xeval x k (snorm n) (zlit64 n) (nwlit bc n), [XMB b1 bi [XME (SA cb co) m x]])
  | b :: r => if BASF.expr_eqbF b1 (xb_b b) then
                match xb_eval bc b k n cb co m with
                | (v, Some b') => (v, b' :: r)
                | (v, None) => (v, xm)
                end
              else let '(v, r') := xm_eval bc r b1 k n cb co m in (v, b :: r')
  end.
Definition XBOK (bc : bctx) (b : xmb) : Prop :=
  xb_bi b = mk_binf bc (xb_b b) /\ forall e, In e (xb_l b) -> xe_x e = mk_xin bc (xb_b b) (mk_binf bc (xb_b b)) (a_base (xe_c e)) (a_off (xe_c e)) (xe_m e).
Definition XMOK (bc : bctx) (xm : xmemo) : Prop := forall b, In b xm -> XBOK bc b.
Lemma XMOK_nil : forall bc, XMOK bc []. Proof. intros bc b []. Qed.
Lemma nwlit_eq : forall bc n, nwlit bc n = lin_nowrapRB bc (ELit n).
Proof.
  intros bc n. unfold nwlit. destruct (Z.leb_spec 0 n); [|reflexivity]. destruct (Z.ltb_spec n two63z); [|reflexivity].
  symmetry. apply lin_nowrapRB_lit. lia.
Qed.
Lemma xe_find_spec : forall l cb co m x, xe_find l cb co m = Some x -> exists e, In e l /\ xe_x e = x /\ xe_c e = SA cb co /\ xe_m e = m.
Proof.
  induction l as [|e r IH]; intros cb co m x H; [discriminate|]. cbn [xe_find] in H.
  destruct (Z.eqb_spec co (a_off (xe_c e))) as [E1|N1].
  - destruct (BASF.expr_eqbF cb (a_base (xe_c e))) eqn:E2.
    + destruct (BASF.expr_eqbF m (xe_m e)) eqn:E3.
      * injection H as <-. apply BASF.expr_eqbF_true in E2, E3. exists e. split; [left; reflexivity|]. split; [reflexivity|].
        split; [destruct (xe_c e) as [cb' co']; cbn in *; subst; reflexivity|symmetry; exact E3].
      * destruct (IH _ _ _ _ H) as (e' & I & R). exists e'. split; [right; exact I|exact R].
    + destruct (IH _ _ _ _ H) as (e' & I & R). exists e'. split; [right; exact I|exact R].
  - destruct (IH _ _ _ _ H) as (e' & I & R). exists e'. split; [right; exact I|exact R].
Qed.
Lemma xb_eval_spec : forall bc b k n cb co m, XBOK bc b ->
  fst (xb_eval bc b k n cb co m) = xinsideB bc (xb_b b) k (ELit n) cb co m
  /\ match snd (xb_eval bc b k n cb co m) with Some b' => XBOK bc b' /\ xb_b b' = xb_b b | None => True end.
Proof.
  intros bc b k n cb co m [HB HL]. unfold xb_eval. rewrite nwlit_eq.
  destruct (xe_find (xb_l b) cb co m) as [x|] eqn:F; cbn [fst snd].
  - split; [|exact I]. destruct (xe_find_spec _ _ _ _ _ F) as (e & I1 & <- & EC & EM).
    rewrite (HL e I1), EC, EM. cbn [a_base a_off]. apply xeval_eq.
  - rewrite HB. split; [apply xeval_eq|]. split; [|reflexivity]. split; [reflexivity|]. cbn [xb_b xb_l].
    intros e [<-|I1]; [reflexivity|apply HL; exact I1].
Qed.
Lemma xm_eval_spec : forall bc xm b1 k n cb co m, XMOK bc xm ->
  fst (xm_eval bc xm b1 k n cb co m) = xinsideB bc b1 k (ELit n) cb co m /\ XMOK bc (snd (xm_eval bc xm b1 k n cb co m)).
Proof.
  intros bc xm b1 k n cb co m. induction xm as [|b r IH]; intros H.
  - cbn [xm_eval fst snd]. rewrite nwlit_eq. split; [apply xeval_eq|].
    intros b [<-|[]]. split; [reflexivity|]. cbn [xb_b xb_l]. intros e [<-|[]]. reflexivity.
  - cbn [xm_eval]. destruct (BASF.expr_eqbF b1 (xb_b b)) eqn:E.
    + apply BASF.expr_eqbF_true in E. subst b1. assert (HB : XBOK bc b) by (apply H; left; reflexivity).
      destruct (xb_eval_spec bc b k n cb co m HB) as [E1 E2]. destruct (xb_eval bc b k n cb co m) as [v [b'|]]; cbn [fst snd] in *.
      * split; [exact E1|]. intros x [<-|I]; [apply E2|apply H; right; exact I].
      * split; [exact E1|exact H].
    + assert (HR : XMOK bc r) by (intros x I; apply H; right; exact I). destruct (IH HR) as [E1 E2].
      destruct (xm_eval bc r b1 k n cb co m) as [v r']. cbn [fst snd] in *. split; [exact E1|].
      intros x [<-|I]; [apply H; left; reflexivity|apply E2; exact I].
Qed.
(* [comment removed for export] *)
Definition sub_itvM (bc : bctx) (xm : xmemo) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool * xmemo :=
  if (if (if BASF.expr_eqbF b (a_base c) then Z.leb (a_off c) k else false) then
        match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
      else false)
  then (true, xm)
  else if (if Z.leb 0 n then Z.ltb n two64 else false) then
         (if shares_var b (a_base c) then xm_eval bc xm b k n (a_base c) (a_off c) m
          else (xinsideB bc b k (ELit n) (a_base c) (a_off c) m, xm))
       else (false, xm).
Lemma sub_itvM_spec : forall bc xm b k n c m, XMOK bc xm ->
  fst (sub_itvM bc xm b k n c m) = sub_itvB bc b k n c m /\ XMOK bc (snd (sub_itvM bc xm b k n c m)).
Proof.
  intros bc xm b k n c m H. unfold sub_itvM, sub_itvB. rewrite BASF.expr_eqbF_eq.
  replace (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool with (if expr_eqb b (a_base c) then Z.leb (a_off c) k else false) by (destruct (expr_eqb b (a_base c)); reflexivity).
  replace (Z.leb 0 n && Z.ltb n two64)%bool with (if Z.leb 0 n then Z.ltb n two64 else false) by (destruct (Z.leb 0 n); reflexivity).
  destruct (if (if expr_eqb b (a_base c) then Z.leb (a_off c) k else false) then match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end else false);
    [split; [reflexivity|exact H]|].
  destruct (if Z.leb 0 n then Z.ltb n two64 else false); [|split; [reflexivity|exact H]].
  destruct (shares_var b (a_base c)); [apply xm_eval_spec; exact H|split; [reflexivity|exact H]].
Qed.
Fixpoint in_sidesM (bc : bctx) (xm : xmemo) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool * xmemo :=
  match D with
  | [] => (false, xm)
  | (c, m) :: r => let '(v, xm') := sub_itvM bc xm b2 k2 n2 c m in if v then (true, xm') else in_sidesM bc xm' r b2 k2 n2
  end.
Lemma in_sidesM_spec : forall bc D xm b2 k2 n2, XMOK bc xm ->
  fst (in_sidesM bc xm D b2 k2 n2) = in_sidesB bc D b2 k2 n2 /\ XMOK bc (snd (in_sidesM bc xm D b2 k2 n2)).
Proof.
  intros bc D. induction D as [|[c m] r IH]; intros xm b2 k2 n2 H; [split; [reflexivity|exact H]|].
  cbn [in_sidesM in_sidesB]. destruct (sub_itvM_spec bc xm b2 k2 n2 c m H) as [E1 E2].
  destruct (sub_itvM bc xm b2 k2 n2 c m) as [v xm']. cbn [fst snd] in *. subst v.
  destruct (sub_itvB bc b2 k2 n2 c m); [split; [reflexivity|exact E2]|apply IH; exact E2].
Qed.
Definition ranges_apartM (bc : bctx) (kd : list kentry) (sp : sprep) (br1 : option (Z * Z)) (xm : xmemo) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool * xmemo :=
  if (match br1, sp_rng sp with
      | Some (lo1, hi1), Some (lo2, hi2) => if Z.leb (hi1 + k1 + n1) (lo2 + k2) then true else Z.leb (hi2 + k2 + n2) (lo1 + k1)
      | _, _ => false
      end)%Z then (true, xm)
  else if Z.eqb (zlit64 n2) n2 then
         let '(v, xm') := in_sidesM bc xm (sp_D sp) b1 k1 n1 in
         if v then (true, xm') else (lin_apartB bc b1 k1 n1 b2 k2 n2, xm')
       else ((if kdisj_apartB bc kd b1 k1 n1 b2 k2 n2 then true else lin_apartB bc b1 k1 n1 b2 k2 n2), xm).
Lemma ranges_apartM_spec : forall bc kd sp br1 xm b1 k1 n1 b2 k2 n2, XMOK bc xm ->
  fst (ranges_apartM bc kd sp br1 xm b1 k1 n1 b2 k2 n2) = ranges_apartBF2 bc kd sp br1 b1 k1 n1 b2 k2 n2
  /\ XMOK bc (snd (ranges_apartM bc kd sp br1 xm b1 k1 n1 b2 k2 n2)).
Proof.
  intros bc kd sp br1 xm b1 k1 n1 b2 k2 n2 H. unfold ranges_apartM, ranges_apartBF2.
  destruct (match br1, sp_rng sp with
            | Some (lo1, hi1), Some (lo2, hi2) => if Z.leb (hi1 + k1 + n1) (lo2 + k2) then true else Z.leb (hi2 + k2 + n2) (lo1 + k1)
            | _, _ => false end)%Z; [split; [reflexivity|exact H]|].
  destruct (Z.eqb (zlit64 n2) n2); [|split; [reflexivity|exact H]].
  destruct (in_sidesM_spec bc (sp_D sp) xm b1 k1 n1 H) as [E1 E2].
  destruct (in_sidesM bc xm (sp_D sp) b1 k1 n1) as [v xm']. cbn [fst snd] in *. subst v.
  destruct (in_sidesB bc (sp_D sp) b1 k1 n1); split; try reflexivity; exact E2.
Qed.
Fixpoint log_lookupBF3M (bc : bctx) (kd : list kentry) (br1 : option (Z * Z)) (ra : option (PrimInt63.int * PrimInt63.int))
         (log : list sentry) (lis : list sprep) (lia : list sann)
         (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool) (hints : list bool) (acc : list sidecond) (xm : xmemo) : lres * xmemo :=
  match log, lis, lia with
  | [], _, _ => (LMiss acc hints, xm)
  | SE (SA kb kk) w v :: rest, li :: lrest, sa :: arest =>
      match rel_litF rb rk zn kb kk (sa_zw sa) with
      | RInside d => (LHit (mkExt sx (Z.to_nat d) n v) acc hints, xm)
      | RDisjoint => log_lookupBF3M bc kd br1 ra rest lrest arest rb rk n zn sx hints acc xm
      | RPartial => (match log_bytes_lit log rb rk n with
                     | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                     | None => LStuck
                     end, xm)
      | RUnknown =>
          let '(ap, xm') := if i63apart ra (sa_rng sa) then (true, xm) else ranges_apartM bc kd li br1 xm rb rk zn kb kk (sa_zw sa) in
          if ap then log_lookupBF3M bc kd br1 ra rest lrest arest rb rk n zn sx hints acc xm'
          else
          match hints with
          | false :: _ => (LStuck, xm')
          | _ => log_lookupBF3M bc kd br1 ra rest lrest arest rb rk n zn sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc) xm'
          end
      end
  | _, _, _ => (log_lookupBF2 bc kd (Some br1) log lis rb rk n sx hints acc, xm)
  end.
Lemma log_lookupBF3M_spec : forall bc kd br1 ra log lis lia rb rk n zn sx hints acc xm, XMOK bc xm ->
  fst (log_lookupBF3M bc kd br1 ra log lis lia rb rk n zn sx hints acc xm) = log_lookupBF3 bc kd br1 ra log lis lia rb rk n zn sx hints acc
  /\ XMOK bc (snd (log_lookupBF3M bc kd br1 ra log lis lia rb rk n zn sx hints acc xm)).
Proof.
  intros bc kd br1 ra log. induction log as [|[[kb kk] w v] rest IH]; intros lis lia rb rk n zn sx hints acc xm H; [split; [reflexivity|exact H]|].
  destruct lis as [|li lrest]; [split; [reflexivity|exact H]|]. destruct lia as [|sa arest]; [split; [reflexivity|exact H]|].
  cbn [log_lookupBF3M log_lookupBF3].
  destruct (rel_litF rb rk zn kb kk (sa_zw sa)); try (split; [reflexivity|exact H]); [apply IH; exact H|].
  destruct (i63apart ra (sa_rng sa)); [apply IH; exact H|].
  destruct (ranges_apartM_spec bc kd li br1 xm rb rk zn kb kk (sa_zw sa) H) as [E1 E2].
  destruct (ranges_apartM bc kd li br1 xm rb rk zn kb kk (sa_zw sa)) as [ap xm']. cbn [fst snd] in *. subst ap.
  destruct (ranges_apartBF2 bc kd li br1 rb rk zn kb kk (sa_zw sa)); [apply IH; exact E2|].
  destruct hints as [|[|] hs]; try (apply IH; exact E2). split; [reflexivity|exact E2].
Qed.
Definition log_lookupGM (bc : bctx) (kd : list kentry) (br1 : option (Z * Z)) (ra : option (PrimInt63.int * PrimInt63.int))
           (gl : list lgroup) (log : list sentry) (lis : list sprep) (lia : list sann)
           (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool) (hints : list bool) (xm : xmemo) : lres * xmemo :=
  match (if gl_others_apart gl rb ra then grp_scan gl rb rk zn n sx hints else None) with
  | Some r => (r, xm)
  | None => log_lookupBF3M bc kd br1 ra log lis lia rb rk n zn sx hints [] xm
  end.
Lemma log_lookupGM_spec : forall bc kd br1 ra gl log lis lia rb rk n zn sx hints xm, XMOK bc xm ->
  fst (log_lookupGM bc kd br1 ra gl log lis lia rb rk n zn sx hints xm) = log_lookupG bc kd br1 ra gl log lis lia rb rk n zn sx hints
  /\ XMOK bc (snd (log_lookupGM bc kd br1 ra gl log lis lia rb rk n zn sx hints xm)).
Proof.
  intros. unfold log_lookupGM, log_lookupG.
  destruct (if gl_others_apart gl rb ra then grp_scan gl rb rk zn n sx hints else None); [split; [reflexivity|assumption]|].
  apply log_lookupBF3M_spec. assumption.
Qed.

(* [comment removed for export] *)
Definition xinsM (bc : bctx) (br : option (Z * Z)) (xm : xmemo) (rb : expr) (rk zn : Z) (kb : expr) (kk : Z) (len : expr) : bool * xmemo :=
  if shares_var rb kb then xm_eval bc xm rb rk zn kb kk len
  else ((if novars kb then xinside_numBr bc br rk (ELit zn) kb kk len else false), xm).
Lemma xinsM_spec : forall bc br xm rb rk zn kb kk len, XMOK bc xm ->
  fst (xinsM bc br xm rb rk zn kb kk len) = xinsideBr bc br rb rk (ELit zn) kb kk len
  /\ XMOK bc (snd (xinsM bc br xm rb rk zn kb kk len)).
Proof.
  intros bc br xm rb rk zn kb kk len H. unfold xinsM, xinsideBr. destruct (shares_var rb kb) eqn:E.
  - destruct (xm_eval_spec bc xm rb rk zn kb kk len H) as [E1 E2]. split; [|exact E2]. rewrite E1. unfold xinsideB. rewrite E. reflexivity.
  - split; [reflexivity|exact H].
Qed.
(* [comment removed for export] *)
Definition kstepM (bc : bctx) (st : option (list IMGF.sgi)) (segs : list Segment) (br : option (Z * Z)) (K : kentry) (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool)
           (acc : list sidecond) (xm : xmemo) : option lres * xmemo :=
  match K with
  | KZero (SA kb kk) len =>
      if (match len with ELit _ => BASF.expr_eqbF rb kb | _ => false end) then
        (match kstepF bc st segs br K rb rk n zn sx acc (fun _ => LMiss [] []) with LMiss _ _ => None | r => Some r end, xm)
      else let '(v, xm') := xinsM bc br xm rb rk zn kb kk len in ((if v then Some (LHit (ELit 0) acc []) else None), xm')
  | KFill (SA kb kk) len c =>
      if (match len with ELit _ => BASF.expr_eqbF rb kb | _ => false end) then
        (match kstepF bc st segs br K rb rk n zn sx acc (fun _ => LMiss [] []) with LMiss _ _ => None | r => Some r end, xm)
      else let '(v, xm') := xinsM bc br xm rb rk zn kb kk len in ((if v then Some (LHit (fill_lit sx n c) acc []) else None), xm')
  | _ => (match kstepF bc st segs br K rb rk n zn sx acc (fun _ => LMiss [] []) with LMiss _ _ => None | r => Some r end, xm)
  end.
Lemma kstepF_marker : forall bc st segs br K rb rk n zn sx acc k,
  kstepF bc st segs br K rb rk n zn sx acc k
  = match kstepF bc st segs br K rb rk n zn sx acc (fun _ => LMiss [] []) with LMiss _ _ => k tt | r => r end.
Proof.
  intros. unfold kstepF.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity;
    repeat match goal with
           | |- context [match ?x with ELit _ => _ | _ => _ end] => is_var x; destruct x
           | |- context [match ?x with Z0 => _ | Zpos _ => _ | Zneg _ => _ end] => is_var x; destruct x
           | |- context [if ?c then _ else _] => lazymatch c with context [if _ then _ else _] => fail | _ => destruct c end
           | |- context [match ?c with Some _ => _ | None => _ end] => lazymatch c with context [if _ then _ else _] => fail | _ => destruct c end
           end; try reflexivity.
Qed.

Lemma kstepM_spec : forall bc st segs br0 K rb rk n zn sx acc xm k, XMOK bc xm ->
  kstepF bc st segs br0 K rb rk n zn sx acc k
  = match fst (kstepM bc st segs br0 K rb rk n zn sx acc xm) with Some r => r | None => k tt end
  /\ XMOK bc (snd (kstepM bc st segs br0 K rb rk n zn sx acc xm)).
Proof.
  intros bc st segs br0 K rb rk n zn sx acc xm k H.
  assert (G : forall K', kstepF bc st segs br0 K' rb rk n zn sx acc k
              = match fst (match kstepF bc st segs br0 K' rb rk n zn sx acc (fun _ => LMiss [] []) with LMiss _ _ => None | r => Some r end, xm) with
                | Some r => r | None => k tt end
              /\ XMOK bc (snd (match kstepF bc st segs br0 K' rb rk n zn sx acc (fun _ => LMiss [] []) with LMiss _ _ => None | r => Some r end, xm))).
  { intros K'. cbn [fst snd]. split; [|exact H]. rewrite (kstepF_marker bc st segs br0 K' rb rk n zn sx acc k).
    destruct (kstepF bc st segs br0 K' rb rk n zn sx acc (fun _ => LMiss [] [])); reflexivity. }
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try apply G.
  - unfold kstepM. destruct (match len with ELit _ => BASF.expr_eqbF rb kb | _ => false end) eqn:EL; [apply G|].
    destruct (xinsM_spec bc br0 xm rb rk zn kb kk len H) as [E1 E2].
    destruct (xinsM bc br0 xm rb rk zn kb kk len) as [v xm']. cbn [fst snd] in *. split; [|exact E2].
    unfold kstepF. destruct len; rewrite ?EL, <- ?E1; destruct v; reflexivity.
  - unfold kstepM. destruct (match len with ELit _ => BASF.expr_eqbF rb kb | _ => false end) eqn:EL; [apply G|].
    destruct (xinsM_spec bc br0 xm rb rk zn kb kk len H) as [E1 E2].
    destruct (xinsM bc br0 xm rb rk zn kb kk len) as [v xm']. cbn [fst snd] in *. split; [|exact E2].
    unfold kstepF. destruct len; rewrite ?EL, <- ?E1; destruct v; reflexivity.
Qed.
Fixpoint kwalkM (bc : bctx) (st : option (list IMGF.sgi)) (segs : list Segment) (br : option (Z * Z)) (l : list (option (PrimInt63.int * PrimInt63.int) * kentry))
         (r : option (PrimInt63.int * PrimInt63.int)) (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool) (acc : list sidecond) (xm : xmemo) : lres * xmemo :=
  match l with
  | [] => (LMiss acc [], xm)
  | (a, K) :: rest =>
      if (match a, r with
          | Some (s, e), Some (r63, zn63) => if PrimInt63.leb s r63 then PrimInt63.leb (PrimInt63.add r63 zn63) e else false
          | _, _ => true
          end)
      then let '(o, xm') := kstepM bc st segs br K rb rk n zn sx acc xm in
           match o with
           | Some res => (res, xm')
           | None => kwalkM bc st segs br rest r rb rk n zn sx acc xm'
           end
      else kwalkM bc st segs br rest r rb rk n zn sx acc xm
  end.
Lemma kwalkM_spec : forall bc st segs br0 l r rb rk n zn sx acc xm, XMOK bc xm ->
  fst (kwalkM bc st segs br0 l r rb rk n zn sx acc xm) = kwalkfF bc st segs br0 l r rb rk n zn sx acc
  /\ XMOK bc (snd (kwalkM bc st segs br0 l r rb rk n zn sx acc xm)).
Proof.
  intros bc st segs br0 l r rb rk n zn sx acc. induction l as [|[a K] rest IH]; intros xm H; [split; [reflexivity|exact H]|].
  cbn [kwalkM kwalkfF].
  destruct (match a, r with
            | Some (s, e), Some (r63, zn63) => if PrimInt63.leb s r63 then PrimInt63.leb (PrimInt63.add r63 zn63) e else false
            | _, _ => true end); [|apply IH; exact H].
  destruct (kstepM_spec bc st segs br0 K rb rk n zn sx acc xm (fun _ => kwalkfF bc st segs br0 rest r rb rk n zn sx acc) H) as [E1 E2].
  rewrite E1. destruct (kstepM bc st segs br0 K rb rk n zn sx acc xm) as [[res|] xm']; cbn [fst snd] in *.
  - split; [reflexivity|exact E2].
  - apply IH. exact E2.
Qed.

Definition know_lookupA0IM (bc : bctx) (kx : kix) (xc : xctx) (br : option (Z * Z)) (segs : list Segment) (rb : expr) (rk : Z)
           (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) (xm : xmemo) : lres * xmemo :=
  match hints, n with
  | [], S _ =>
      if is_lit0 rb then (know_lookupA0IF bc kx xc br segs rb rk n sx hints acc, xm)
      else let zn := Z.of_nat n in kwalkM bc (xc_st xc) segs br (xc_fw xc) (qann rk zn) rb rk n zn sx acc xm
  | _, _ => (know_lookupA0IF bc kx xc br segs rb rk n sx hints acc, xm)
  end.
Lemma know_lookupA0IM_spec : forall bc kx xc br segs rb rk n sx hints acc xm, XMOK bc xm ->
  fst (know_lookupA0IM bc kx xc br segs rb rk n sx hints acc xm) = know_lookupA0IF bc kx xc br segs rb rk n sx hints acc
  /\ XMOK bc (snd (know_lookupA0IM bc kx xc br segs rb rk n sx hints acc xm)).
Proof.
  intros bc kx xc br segs rb rk n sx hints acc xm H. unfold know_lookupA0IM.
  destruct hints as [|h hs]; [|split; [reflexivity|exact H]]. destruct n as [|n']; [split; [reflexivity|exact H]|].
  destruct (is_lit0 rb) eqn:L; [split; [reflexivity|exact H]|]. cbv zeta.
  destruct (kwalkM_spec bc (xc_st xc) segs br (xc_fw xc) (qann rk (Z.of_nat (S n'))) rb rk (S n') (Z.of_nat (S n')) sx acc xm H) as [E1 E2].
  split; [|exact E2]. rewrite E1. unfold know_lookupA0IF. rewrite L. reflexivity.
Qed.
Definition know_lookupABIM (bc : bctx) (kx : kix) (xc : xctx) (br : option (Z * Z)) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) (xm : xmemo) : lres * xmemo :=
  let '(r0, xm') := know_lookupA0IM bc kx xc br segs rb rk n sx hints acc xm in
  (match r0 with
   | LMiss acc' hints' =>
       match know_bytes_lit segs kn rb rk n with
       | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
       | None => LMiss acc' hints'
       end
   | r => r
   end, xm').
Lemma know_lookupABIM_spec : forall bc kx xc br segs kn rb rk n sx hints acc xm, XMOK bc xm ->
  fst (know_lookupABIM bc kx xc br segs kn rb rk n sx hints acc xm) = know_lookupABIF bc kx xc br segs kn rb rk n sx hints acc
  /\ XMOK bc (snd (know_lookupABIM bc kx xc br segs kn rb rk n sx hints acc xm)).
Proof.
  intros bc kx xc br segs kn rb rk n sx hints acc xm H. unfold know_lookupABIM, know_lookupABIF.
  destruct (know_lookupA0IM_spec bc kx xc br segs rb rk n sx hints acc xm H) as [E1 E2].
  destruct (know_lookupA0IM bc kx xc br segs rb rk n sx hints acc xm) as [r0 xm']. cbn [fst snd] in *. subst r0. split; [|exact E2].
  destruct (know_lookupA0IF bc kx xc br segs rb rk n sx hints acc); reflexivity.
Qed.
(* [comment removed for export] *)
Definition sym_readBIFx (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep)
           (lia : list sann) (gl : list lgroup) (c : BASF.bcache) (xm : xmemo) (scr : scripts)
           (br : option (Z * Z)) (e63 : option (PrimInt63.int * PrimInt63.int)) (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) * BASF.bcache * xmemo :=
  let zn := Z.of_nat n in
  let ra := rann63 e63 br (a_off a) zn in
  let '(lr, xm0) := log_lookupGM bc (be_kd ex) br ra gl (s_log ss) lis lia (a_base a) (a_off a) n zn sx' (sc_hints scr) xm in
  match lr with
  | LStuck => (None, c, xm0)
  | LHit v scs hints =>
      let '(v', c') := BASF.foldKB_c bc c (extK0B bc v) in
      (Some (v', flat_scBFa ra br a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss), c', xm0)
  | LMiss scs hints =>
      let '(kr, xm') := know_lookupABIM bc kx xc br segs (s_know ss) (a_base a) (a_off a) n sx' hints scs xm0 in
      match kr with
      | LStuck => (None, c, xm')
      | LHit v scs' hints' =>
          let '(v', c') := BASF.foldKB_c bc c (extK0B bc v) in
          (Some (v', flat_scBFa ra br a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss), c', xm')
      | LMiss scs' hints' =>
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          (Some (rv, flat_scBFa ra br a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i), c, xm')
      end
  end.
Lemma sym_readBIFx_spec : forall segs ss bc kx xc ex lis lia gl c xm scr br e63 a n sx', XMOK bc xm ->
  fst (sym_readBIFx segs ss bc kx xc ex lis lia gl c xm scr br e63 a n sx') = sym_readBIFr segs ss bc kx xc ex lis lia gl c scr br e63 a n sx'
  /\ XMOK bc (snd (sym_readBIFx segs ss bc kx xc ex lis lia gl c xm scr br e63 a n sx')).
Proof.
  intros segs ss bc kx xc ex lis lia gl c xm scr br e63 a n sx' H. unfold sym_readBIFx, sym_readBIFr. cbv zeta.
  destruct (log_lookupGM_spec bc (be_kd ex) br (rann63 e63 br (a_off a) (Z.of_nat n)) gl (s_log ss) lis lia (a_base a) (a_off a) n (Z.of_nat n) sx' (sc_hints scr) xm H) as [L1 L2].
  destruct (log_lookupGM bc (be_kd ex) br (rann63 e63 br (a_off a) (Z.of_nat n)) gl (s_log ss) lis lia (a_base a) (a_off a) n (Z.of_nat n) sx' (sc_hints scr) xm) as [lr xm0].
  cbn [fst snd] in L1, L2. subst lr.
  destruct (log_lookupG bc (be_kd ex) br (rann63 e63 br (a_off a) (Z.of_nat n)) gl (s_log ss) lis lia (a_base a) (a_off a) n (Z.of_nat n) sx' (sc_hints scr)) as [v scs hints|scs hints|].
  - destruct (BASF.foldKB_c bc c (extK0B bc v)) as [v' c']. split; [reflexivity|exact L2].
  - destruct (know_lookupABIM_spec bc kx xc br segs (s_know ss) (a_base a) (a_off a) n sx' hints scs xm0 L2) as [E1 E2].
    destruct (know_lookupABIM bc kx xc br segs (s_know ss) (a_base a) (a_off a) n sx' hints scs xm0) as [kr xm']. cbn [fst snd] in *. subst kr.
    destruct (know_lookupABIF bc kx xc br segs (s_know ss) (a_base a) (a_off a) n sx' hints scs) as [v scs' hints'|scs' hints'|].
    + destruct (BASF.foldKB_c bc c (extK0B bc v)) as [v' c']. split; [reflexivity|exact E2].
    + split; [reflexivity|exact E2].
    + split; [reflexivity|exact E2].
  - split; [reflexivity|exact L2].
Qed.
(* [comment removed for export] *)
Definition sym_stepBIF_cx (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep) (lia : list sann) (gl : list lgroup)
           (c : BASF.bcache) (xm : xmemo) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres * BASF.bcache * xmemo :=
  match i with
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      let sx' := match sz with SZ8 => false | _ => sx end in
      let '(a, c1) := BASF.to_saddrKB_c bc c (sr_getF (s_regs ss) rs) (bv_signedF imm) in
      let '(br, e63, c2) := BASF.base_range63_c bc c1 (a_base a) in
      let '(r, c3, xm') := sym_readBIFx segs ss bc kx xc ex lis lia gl c2 xm scr br e63 a n sx' in
      (match r with
       | None => SStop
       | Some (v, scs, scr', nx') =>
           SOk (SSR (s_pc ss + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) v)
                    (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
       end, c3, xm')
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := sr_getF (s_regs ss) rs in
      if amo_alignedbB bc e wd then
        let '(a, c1) := BASF.to_saddrKB_c bc c e 0 in
        let '(br, e63, c2) := BASF.base_range63_c bc c1 (a_base a) in
        let '(r, c3, xm') := sym_readBIFx segs ss bc kx xc ex lis lia gl c2 xm scr br e63 a n (amo_sx wd) in
        (match r with
         | None => SStop
         | Some (v, scs, scr', nx') =>
             SOk (SSR (s_pc ss + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) v)
                      (s_log ss) (s_know ss) nx' (Some a)) scs scr'
         end, c3, xm')
      else (SStop, c, xm)
  | _ => (sym_stepBIF_c bc kx xc ex lis lia gl c segs i ss scr, xm)
  end.
Lemma sym_stepBIF_cx_spec : forall bc kx xc ex lis lia gl c xm segs i ss scr, XMOK bc xm ->
  fst (sym_stepBIF_cx bc kx xc ex lis lia gl c xm segs i ss scr) = sym_stepBIF_c bc kx xc ex lis lia gl c segs i ss scr
  /\ XMOK bc (snd (sym_stepBIF_cx bc kx xc ex lis lia gl c xm segs i ss scr)).
Proof.
  intros bc kx xc ex lis lia gl c xm segs i ss scr H. destruct i; try (split; [reflexivity|exact H]);
  cbn [sym_stepBIF_cx sym_stepBIF_c]; cbv zeta;
  try match goal with |- context [if amo_alignedbB ?bc ?e ?wd then _ else _] => destruct (amo_alignedbB bc e wd); [|split; [reflexivity|exact H]] end;
  match goal with |- context [BASF.to_saddrKB_c ?bc ?c ?e ?im] => destruct (BASF.to_saddrKB_c bc c e im) as [a c1] end;
  destruct (BASF.base_range63_c bc c1 (a_base a)) as [[br e63] c2];
  match goal with |- context [sym_readBIFx ?segs ?ss ?bc ?kx ?xc ?ex ?lis ?lia ?gl ?c2 ?xm ?scr ?br ?e63 ?a ?n ?sx'] =>
    destruct (sym_readBIFx_spec segs ss bc kx xc ex lis lia gl c2 xm scr br e63 a n sx' H) as [E1 E2];
    destruct (sym_readBIFx segs ss bc kx xc ex lis lia gl c2 xm scr br e63 a n sx') as [[r c3] xm'] end;
  cbn [fst snd] in *; rewrite <- E1; (split; [reflexivity|exact E2]).
Qed.
(* [comment removed for export] *)
Definition sym_stepBIF_cr (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep) (lia : list sann) (gl : list lgroup)
           (c : BASF.bcache) (xm : xmemo) (rm : BASF.rmemo) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts)
  : stepres * BASF.bcache * xmemo * BASF.rmemo :=
  let g r := sr_getF (s_regs ss) r in
  let p := s_pc ss in
  let dflt := fun (_ : unit) => (sym_stepBIF_cx bc kx xc ex lis lia gl c xm segs i ss scr, rm) in
  let big2 := fun (a b : expr) => if BASF.bigE a then true else BASF.bigE b in
  match i with
  | OpImm op rd rs imm =>
      if BASF.bigE (g rs) then
        let '(v, rm') := BASF.foldKBM bc rm (mkAluK0BF bc op (g rs) (ELit (bv_signedF imm))) in (SOk (ssetF ss rd v (p + 4)) [] scr, c, xm, rm')
      else dflt tt
  | ShiftImm op rd rs sh =>
      if BASF.bigE (g rs) then
        let '(v, rm') := BASF.foldKBM bc rm (mkAluK0BF bc op (g rs) (ELit (bv_unsigned sh))) in (SOk (ssetF ss rd v (p + 4)) [] scr, c, xm, rm')
      else dflt tt
  | Op op rd rs1 rs2 =>
      if big2 (g rs1) (g rs2) then
        let '(v, rm') := BASF.foldKBM bc rm (mkAluK0BF bc op (g rs1) (g rs2)) in (SOk (ssetF ss rd v (p + 4)) [] scr, c, xm, rm')
      else dflt tt
  | OpImm32 rd rs imm =>
      if BASF.bigE (g rs) then
        let '(v, rm') := BASF.foldKBM bc rm (mkAluwK0BF bc ALU_ADD (g rs) (ELit (bv_signedF imm))) in (SOk (ssetF ss rd v (p + 4)) [] scr, c, xm, rm')
      else dflt tt
  | Op32 op rd rs1 rs2 =>
      if big2 (g rs1) (g rs2) then
        let '(v, rm') := BASF.foldKBM bc rm (mkAluwK0BF bc op (g rs1) (g rs2)) in (SOk (ssetF ss rd v (p + 4)) [] scr, c, xm, rm')
      else dflt tt
  | _ => dflt tt
  end.


Local Close Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Fixpoint existsbL {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with [] => false | a :: r => if f a then true else existsbL f r end.
Definition zf_coversBF (bc : bctx) (rb : expr) (rk : Z) (zn : Z) (kb : expr) (kk : Z) (len : expr) : bool :=
  if (match len with
      | ELit l0 => match rel_litF rb rk zn kb kk (zmod64 l0) with RInside _ => true | _ => false end
      | _ => false
      end) then true
  else xinsideB bc rb rk (ELit zn) kb kk len.
Definition kentry_overlayBF (bc : bctx) (rb : expr) (rk : Z) (zn : Z) (K : kentry) : bool :=
  match K with
  | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ => zf_coversBF bc rb rk zn kb kk len
  | _ => false
  end.
Definition kentry_readableBF (bc : bctx) (rb : expr) (rk : Z) (zn : Z) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ => match rel_litF rb rk zn kb kk (Z.of_nat w) with RInside _ => true | _ => false end
  | _ => kentry_overlayBF bc rb rk zn K
  end.
Definition kn_readableBF (bc : bctx) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  if existsbL (kentry_readableBF bc rb rk (Z.of_nat n)) kn then true else know_bytes_cov segs true kn rb rk n.
Definition kn_overlayBF (bc : bctx) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  if existsbL (kentry_overlayBF bc rb rk (Z.of_nat n)) kn then true else know_bytes_cov segs false kn rb rk n.
Definition x_dischargeableBF (bc : bctx) (ss ss' : sym_state) (rb : option (saddr * nat * bool)) (sc : sidecond) : bool :=
  let kn := s_know ss in
  match sc with
  | SCReadBase a n sx (EVar j) =>
      if (match rb with
          | Some (a', n', sx') => if saddr_eqb a' a then if Nat.eqb n' n then Bool.eqb sx' sx else false else false
          | None => false
          end)
      then if Nat.eqb j (s_next ss) then if Nat.ltb j (s_next ss') then if evars_lt (s_next ss) (a_base a) then
           if Nat.leb 1 n then if Nat.leb n 8 then kn_readableBF bc kn (a_base a) (a_off a) n else false else false else false else false else false
      else false
  | SCFlat a (ELit z) =>
      if Z.leb 1 z then if Z.leb z 8 then kn_readableBF bc kn (a_base a) (a_off a) (Z.to_nat z) else false else false
  | SCStoreOk a n => if Nat.leb 1 n then if Nat.leb n 8 then kn_overlayBF bc kn (a_base a) (a_off a) n else false else false
  | _ => false
  end.
Definition x_filterBF (bc : bctx) (ss ss' : sym_state) (scs : list sidecond) : list sidecond :=
  match scs with
  | [] => []
  | _ => let rb := find_readbase (s_next ss) scs in
         List.filter (fun sc => negb (x_dischargeableBF bc ss ss' rb sc)) scs
  end.

Definition sym_stepXBIF (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep) (lia : list sann) (gl : list lgroup)
           (c : BASF.bcache) (K : nat) (i : instr) (ss : sym_state) (scr : scripts)
  : stepres * BASF.bcache :=
  let '(r, c') := sym_stepBIF_c bc kx xc ex lis lia gl c segs i ss scr in
  (match r with
   | SOk ss' scs scr' => SOk (cap_rd K i ss') (x_filterBF bc ss ss' scs) scr'    (* [comment removed for export] *)
   | SStop => SStop
   end, c').

(* [comment removed for export] *)
Definition sym_stepXBIFx (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep) (lia : list sann) (gl : list lgroup)
           (c : BASF.bcache) (xm : xmemo) (rm : BASF.rmemo) (K : nat) (i : instr) (ss : sym_state) (scr : scripts)
  : stepres * BASF.bcache * xmemo * BASF.rmemo :=
  let '(r, c', xm', rm') := sym_stepBIF_cr bc kx xc ex lis lia gl c xm rm segs i ss scr in
  (match r with
   | SOk ss' scs scr' => SOk (cap_rd K i ss') (x_filterBF bc ss ss' scs) scr'
   | SStop => SStop
   end, c', xm', rm').

(* [comment removed for export] *)
Fixpoint mk_stt (stops : list Z) : ptree unit :=
  match stops with
  | [] => PTLeaf
  | z :: r => match z with Zpos p => pt_set p tt (mk_stt r) | _ => mk_stt r end
  end.
Definition is_stopF (stt : ptree unit) (stops : list Z) (pc : Z) : bool :=
  match pc with
  | Zpos p => match pt_get stt p with Some _ => true | None => false end
  | _ => existsb (Z.eqb pc) stops
  end.
Definition is_store_instr (i : instr) : bool :=
  match i with Store _ _ _ _ | Sc _ _ _ _ _ _ | Amo _ _ _ _ _ _ _ => true | _ => false end.
(* [comment removed for export] *)
Definition lupd (bc : bctx) (ex : bext) (i : instr) (ss' : sym_state) (lis : list sprep) (lia : list sann) (gl : list lgroup)
           (wc : wcache) : list sprep * list sann * list lgroup * wcache :=
  if is_store_instr i then
    match s_log ss' with
    | e :: _ => let '(sp, wc') := mk_sctx_c bc ex wc e in
                let sa := sann_sp sp e in
                (sp :: lis, sa :: lia, gl_adde gl e sa, wc')
    | [] => (lis, lia, gl, wc)
    end
  else (lis, lia, gl, wc).
(* [comment removed for export] *)
Fixpoint sym_execTXBIF_go (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state)
  (lis : list sprep) (lia : list sann) (gl : list lgroup) (ck : sym_state) (cklis : list sprep)
  (cklia : list sann) (ckgl : list lgroup) (wc : wcache) (c : BASF.bcache) (xm : xmemo) (rm : BASF.rmemo) (stt : ptree unit) : sym_state * list sprep :=
  match fuel with
  | O => if s_clean ss then (ss, lis) else (ck, cklis)
  | S f =>
      if (if first then false else is_stopF stt stops (s_pc ss)) then (if s_clean ss then (ss, lis) else (ck, cklis)) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then (ss, lis) else (ck, cklis)
      | Some i =>
          let '(r, c', xm', rm') := sym_stepXBIFx bc kx xc ex lis lia gl c xm rm K i ss scr_nil in
          match r with
          | SOk ss' [] _ =>
              if is_store_instr i then
                let '(lis', lia', gl', wc') := lupd bc ex i ss' lis lia gl wc in
                if s_clean ss' then sym_execTXBIF_go bc kx xc ex t K f false stops ss' lis' lia' gl' ss' lis' lia' gl' wc' c' xm' rm' stt
                else sym_execTXBIF_go bc kx xc ex t K f false stops ss' lis' lia' gl' ck cklis cklia ckgl wc' c' xm' rm' stt
              else (* [comment removed for export] *)
                if s_clean ss' then sym_execTXBIF_go bc kx xc ex t K f false stops ss' lis lia gl ss' lis lia gl wc c' xm' rm' stt
                else sym_execTXBIF_go bc kx xc ex t K f false stops ss' lis lia gl ck cklis cklia ckgl wc c' xm' rm' stt
          | _ => if s_clean ss then (ss, lis) else (ck, cklis)
          end
      end
  end.
Definition sym_execTXBIF (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state * list sprep :=
  let lis := map (mk_sctx bc ex) (s_log ss) in
  let lia := map (fun e => sann_sp (mk_sctx bc ex e) e) (s_log ss) in
  let gl := GLof (mk_sctx bc ex) (s_log ss) in
  sym_execTXBIF_go bc kx xc ex t K fuel first stops (clr ss) lis lia gl (clr ss) lis lia gl wc_empty [] [] [] (mk_stt stops).

(* [comment removed for export] *)
Definition needs_kx (i : instr) : bool :=
  match i with Load _ _ _ _ _ | Lr _ _ _ _ _ | Amo _ _ _ _ _ _ _ => true | _ => false end.
Definition kx_nil : kix := KX [] [] PTLeaf [].
Definition xc_nil : xctx := XC None [] [].
Fixpoint sym_execTXBIF_goL (bc : bctx) (kn : list kentry) (okx : option (kix * xctx)) (ex : bext) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state)
  (lis : list sprep) (lia : list sann) (gl : list lgroup) (ck : sym_state) (cklis : list sprep)
  (cklia : list sann) (ckgl : list lgroup) (wc : wcache) (c : BASF.bcache) (xm : xmemo) (rm : BASF.rmemo) (stt : ptree unit) : sym_state * list sprep :=
  match fuel with
  | O => if s_clean ss then (ss, lis) else (ck, cklis)
  | S f =>
      if (if first then false else is_stopF stt stops (s_pc ss)) then (if s_clean ss then (ss, lis) else (ck, cklis)) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then (ss, lis) else (ck, cklis)
      | Some i =>
          let '(kx, xc, okx') :=
            if needs_kx i then
              match okx with
              | Some (kx, xc) => (kx, xc, okx)
              | None => let kx := BLKF.mk_kix_f kn in let xc := mk_xc segs kx in (kx, xc, Some (kx, xc))
              end
            else (kx_nil, xc_nil, okx) in
          let '(r, c', xm', rm') := sym_stepXBIFx bc kx xc ex lis lia gl c xm rm K i ss scr_nil in
          match r with
          | SOk ss' [] _ =>
              if is_store_instr i then
                let '(lis', lia', gl', wc') := lupd bc ex i ss' lis lia gl wc in
                if s_clean ss' then sym_execTXBIF_goL bc kn okx' ex t K f false stops ss' lis' lia' gl' ss' lis' lia' gl' wc' c' xm' rm' stt
                else sym_execTXBIF_goL bc kn okx' ex t K f false stops ss' lis' lia' gl' ck cklis cklia ckgl wc' c' xm' rm' stt
              else
                if s_clean ss' then sym_execTXBIF_goL bc kn okx' ex t K f false stops ss' lis lia gl ss' lis lia gl wc c' xm' rm' stt
                else sym_execTXBIF_goL bc kn okx' ex t K f false stops ss' lis lia gl ck cklis cklia ckgl wc c' xm' rm' stt
          | _ => if s_clean ss then (ss, lis) else (ck, cklis)
          end
      end
  end.
Definition sym_execTXBIFL (bc : bctx) (kn : list kentry) (ex : bext) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state * list sprep :=
  let lis := map (mk_sctx bc ex) (s_log ss) in
  let lia := map (fun e => sann_sp (mk_sctx bc ex e) e) (s_log ss) in
  let gl := GLof (mk_sctx bc ex) (s_log ss) in
  sym_execTXBIF_goL bc kn None ex t K fuel first stops (clr ss) lis lia gl (clr ss) lis lia gl wc_empty [] [] [] (mk_stt stops).

End WithSegs.

(* [comment removed for export] *)
Import APC.
Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable nx0 : nat.
Definition run_block_f (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if BLKF.fresh_ok_f nx0 cs then
    let ss := a_ss cs in
    let bc := BLKF.mkbc_m (facts_of (s_know ss)) in
    let '(ss', scs) := sym_execTXBIFL segs bc (s_know ss) (mk_bext bc) IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    match carryKF_ctx bc (s_log ss') scs (s_know ss') [] with
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
  else None.
Definition run_block_gc_f (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  match run_block_f K fuel stops cs with Some cs' => Some (BLKF.cs_gc_b nx0 cs') | None => None end.
End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fe := repeat (apply functional_extensionality; intros ?).
(* [comment removed for export] *)
Ltac eqf := rewrite ?BASF.expr_eqbF_eq in *.
Lemma rel_litF_eq : forall rb rk rn kb kk kn, rel_litF rb rk rn kb kk kn = rel_lit rb rk rn kb kk kn.
Proof. intros. unfold rel_litF, rel_lit. rewrite BASF.expr_eqbF_eq. reflexivity. Qed.
Lemma rel_litF_fe : rel_litF = rel_lit.
Proof. repeat (apply functional_extensionality; intros ?). apply rel_litF_eq. Qed.
Lemma zmod64_fe : zmod64 = fun z => (z mod 2 ^ 64)%Z.
Proof. fe. apply zmod64_eq. Qed.
(* [comment removed for export] *)
Lemma img_fe : forall segs, IMGF.img_bytesFF (IMGF.mk_stab segs) segs = img_bytes segs.
Proof. intros. fe. apply IMGF.img_bytesFF_eq. Qed.

Ltac crush0 :=
  repeat (first [ reflexivity
                | match goal with
                  | |- context [match ?x with ELit _ => _ | _ => _ end] => is_var x; destruct x
                  | |- context [if ?c then _ else _] =>
                      lazymatch c with context [if _ then _ else _] => fail | _ => destruct c end
                  end ]).
Lemma know_lookupA0F_eq : forall bc segs kn rb rk n sx,
  know_lookupA0F bc (IMGF.mk_stab segs) segs kn rb rk n (Z.of_nat n) sx = know_lookupA0B bc segs kn rb rk n sx.
Proof.
  intros bc segs kn rb rk n sx. induction kn as [|K rest IH]; fe; [reflexivity|].
  cbn [know_lookupA0F know_lookupA0B]. rewrite IH, (img_fe segs), zmod64_fe, BASF.expr_eqbF_fe. unfold rel_lit, elen. cbv [andb orb]. cbv zeta beta.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity;
    crush0.
Qed.
(* [comment removed for export] *)
Lemma xinsideBr_eq : forall bc b1 k1 n1 b2 k2 n2, xinsideBr bc (base_rangeB bc b1) b1 k1 n1 b2 k2 n2 = xinsideB bc b1 k1 n1 b2 k2 n2.
Proof. reflexivity. Qed.
Lemma kstepF_eq : forall bc st segs K rest rb rk n zn sx acc,
  kstepF bc st segs (base_rangeB bc rb) K rb rk n zn sx acc (fun _ => know_lookupA0F bc st segs rest rb rk n zn sx [] acc)
  = know_lookupA0F bc st segs (K :: rest) rb rk n zn sx [] acc.
Proof.
  intros. cbn [know_lookupA0F]. unfold kstepF. rewrite ?xinsideBr_eq.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity;
    destruct len; reflexivity.
Qed.
Local Open Scope Z_scope.
Lemma wB63 : Uint63.wB = 2 ^ 63. Proof. reflexivity. Qed.
Lemma zb_spec : forall z a, zb z = Some a -> Uint63.to_Z a = z + 2 ^ 61 /\ - 2 ^ 60 < z < 2 ^ 60.
Proof. exact BASF.zb_spec. Qed.
(* [comment removed for export] *)
Lemma skipw : forall bc st segs K rest rb rk n zn sx acc s e r63 zn63,
  annw K = Some (s, e) -> zb rk = Some r63 -> IMGF.z61 zn = Some zn63 ->
  (if PrimInt63.leb s r63 then PrimInt63.leb (PrimInt63.add r63 zn63) e else false) = false ->
  know_lookupA0F bc st segs (K :: rest) rb rk n zn sx [] acc = know_lookupA0F bc st segs rest rb rk n zn sx [] acc.
Proof.
  intros bc st segs K rest rb rk n zn sx acc s e r63 zn63 HA Hr Hz HT.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e0 m|e0 lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; cbn [annw] in HA; try discriminate.
  destruct (zb kk) as [s0|] eqn:Es; [|discriminate]. destruct (IMGF.z61 (Z.of_nat w)) as [w63|] eqn:Ew; [|discriminate].
  injection HA as <- <-.
  destruct (zb_spec _ _ Es) as [S1 S2]. destruct (zb_spec _ _ Hr) as [R1 R2].
  destruct (IMGF.z61_spec _ _ Ew) as [W1 W2]. destruct (IMGF.z61_spec _ _ Hz) as [Z1 Z2].
  rewrite !IMGF.leb_b in HT. rewrite !Uint63.add_spec, S1, R1, W1, Z1, wB63 in HT.
  rewrite !Z.mod_small in HT by lia.
  cbn [know_lookupA0F]. destruct (BASF.expr_eqbF rb kb); [|reflexivity].
  destruct (Z.leb_spec kk rk) as [H1|H1].
  - destruct (Z.leb_spec (kk + 2 ^ 61) (rk + 2 ^ 61)) as [_|C]; [|lia].
    destruct (Z.leb_spec (rk + zn) (kk + Z.of_nat w)) as [H2|H2]; [|reflexivity].
    destruct (Z.leb_spec (rk + 2 ^ 61 + zn) (kk + 2 ^ 61 + Z.of_nat w)) as [_|C]; [discriminate|lia].
  - reflexivity.
Qed.
Local Close Scope Z_scope.
Lemma kwalkfF_eq : forall bc st segs l rb rk n zn sx acc,
  kwalkfF bc st segs (base_rangeB bc rb) (map (fun K => (annw K, K)) l) (qann rk zn) rb rk n zn sx acc = know_lookupA0F bc st segs l rb rk n zn sx [] acc.
Proof.
  intros bc st segs l rb rk n zn sx acc. induction l as [|K rest IH]; [reflexivity|].
  cbn [map kwalkfF]. rewrite IH.
  destruct (match annw K, qann rk zn with
            | Some (s, e), Some (r63, zn63) => if PrimInt63.leb s r63 then PrimInt63.leb (PrimInt63.add r63 zn63) e else false
            | _, _ => true end) eqn:HT.
  - apply kstepF_eq.
  - destruct (annw K) as [[s e]|] eqn:HA; [|discriminate]. unfold qann in HT.
    destruct (zb rk) as [r63|] eqn:Hr; [|discriminate]. destruct (IMGF.z61 zn) as [zn63|] eqn:Hz; [|discriminate].
    symmetry. apply (skipw bc st segs K rest rb rk n zn sx acc s e r63 zn63 HA Hr Hz HT).
Qed.
(* [comment removed for export] *)
Definition KXOK (kx : kix) : Prop := exists kn, kx = mk_kix kn.
Lemma mentions_var_lit : forall v z, mentions_var v (ELit z) = false. Proof. reflexivity. Qed.
Lemma shares_var_lit : forall z e, shares_var (ELit z) e = false.
Proof.
  intros z e. induction e as [| | op a IHa b IHb| op a IHa b IHb| op a IHa b IHb| op a IHa b IHb| sx lo n a IHa| sx k i n]; cbn [shares_var]; try reflexivity;
    try (rewrite IHa, IHb; reflexivity). exact IHa.
Qed.
Lemma novars_false_neq_lit : forall kb z, novars kb = false -> expr_eqb (ELit z) kb = false.
Proof. intros kb z H. destruct kb; try reflexivity. discriminate. Qed.
Lemma xinsideB_lit_novars : forall bc z k1 n1 b2 k2 n2, novars b2 = false -> xinsideB bc (ELit z) k1 n1 b2 k2 n2 = false.
Proof. intros. unfold xinsideB. rewrite shares_var_lit, H. reflexivity. Qed.
Lemma skipL : forall bc segs K rest rk n sx acc, keepL K = false ->
  know_lookupA0B bc segs (K :: rest) (ELit 0) rk n sx [] acc = know_lookupA0B bc segs rest (ELit 0) rk n sx [] acc.
Proof.
  intros bc segs K rest rk n sx acc HK. cbn [know_lookupA0B].
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; cbn [keepL] in HK; try discriminate.
  - destruct len; rewrite ?(rel_lit_other _ _ _ _ _ _ (novars_false_neq_lit kb 0 HK)), ?(xinsideB_lit_novars bc 0 rk _ kb kk _ HK); reflexivity.
  - cbv zeta. destruct len; rewrite ?(rel_lit_other _ _ _ _ _ _ (novars_false_neq_lit kb 0 HK)), ?(xinsideB_lit_novars bc 0 rk _ kb kk _ HK); reflexivity.
Qed.
Lemma walk_filter_keepL : forall bc segs (P : kentry -> bool) kn rk n sx acc,
  know_lookupA0B bc segs (List.filter (fun K => P K && keepL K) kn) (ELit 0) rk n sx [] acc
  = know_lookupA0B bc segs (List.filter P kn) (ELit 0) rk n sx [] acc.
Proof.
  intros bc segs P kn rk n sx. induction kn as [|K rest IH]; intros acc; [reflexivity|]. cbn [List.filter].
  destruct (P K); cbn [andb]; [|apply IH].
  destruct (keepL K) eqn:HK.
  - cbn [know_lookupA0B]. rewrite !IH. reflexivity.
  - rewrite (skipL bc segs K _ rk n sx acc HK). apply IH.
Qed.
Lemma filter_filter' : forall (A : Type) (f g : A -> bool) l, List.filter f (List.filter g l) = List.filter (fun x => g x && f x) l.
Proof.
  intros A f g l. induction l as [|x r IH]; [reflexivity|]. cbn [List.filter]. destruct (g x); cbn [andb List.filter]; [|exact IH].
  destruct (f x); rewrite IH; reflexivity.
Qed.
Lemma narrow_keepL : forall g K, narrow_in g K = true -> keepL K = true.
Proof.
  intros g K H. unfold narrow_in in H. destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity;
    cbn [lit0_extent keepL] in *; destruct kb as [z| | | | | | |]; try discriminate; reflexivity.
Qed.
Lemma lit_select_eq : forall bc segs kn rk n sx acc,
  know_lookupA0B bc segs (kx_merge (kx_bucket (kx_gran (mk_kix kn)) (gran rk)) (List.filter (fun t => keepL (snd t)) (kx_w0 (mk_kix kn)))) (ELit 0) rk n sx [] acc
  = know_lookupA0B bc segs (kx_select (mk_kix kn) (ELit 0) rk) (ELit 0) rk n sx [] acc.
Proof.
  intros bc segs kn rk n sx acc. rewrite kx_select_eq. cbn [is_lit0].
  unfold mk_kix. destruct (kx_build kn 1%positive) as [[w0 gr] wf] eqn:Hb. cbn [kx_gran kx_w0 kx_wf fst snd].
  destruct (kx_build_spec kn 1%positive w0 gr wf Hb) as (A & B & C).
  rewrite B, A, filter_filter'.
  rewrite (kx_merge_filters (narrow_in (gran rk)) (fun K => kx_wide0 K && keepL K) kn 1%positive).
  2:{ intros K HK. rewrite (narrow_not_wide (gran rk) K HK). reflexivity. }
  rewrite <- (walk_filter_keepL bc segs (kx_cand0 (gran rk))).
  f_equal. apply filter_ext. intros K. rewrite kx_cand0_split.
  destruct (narrow_in (gran rk) K) eqn:HN; cbn [orb andb]; [rewrite (narrow_keepL _ _ HN); reflexivity|reflexivity].
Qed.
Lemma know_lookupA0IF_eq : forall bc kx segs rb, KXOK kx -> know_lookupA0IF bc kx (mk_xc segs kx) (base_rangeB bc rb) segs rb = know_lookupA0I bc kx segs rb.
Proof.
  intros bc kx segs rb [kn0 ->]. apply functional_extensionality; intros rk.
  apply functional_extensionality; intros n. apply functional_extensionality; intros sx.
  apply functional_extensionality; intros hints. apply functional_extensionality; intros acc.
  unfold know_lookupA0IF, know_lookupA0I, mk_xc. cbn [xc_st xc_fw xc_w0].
  destruct hints as [|h hs]; [|rewrite know_lookupA0F_eq; reflexivity]. destruct n as [|n']; [rewrite know_lookupA0F_eq; reflexivity|].
  destruct (is_lit0 rb) eqn:L.
  - rewrite know_lookupA0F_eq. apply is_lit0_true in L. subst rb. apply lit_select_eq.
  - cbv zeta. rewrite kwalkfF_eq, know_lookupA0F_eq. unfold kx_select. rewrite L. reflexivity.
Qed.
Lemma know_lookupABIF_eq : forall bc kx segs kn rb, KXOK kx -> know_lookupABIF bc kx (mk_xc segs kx) (base_rangeB bc rb) segs kn rb = know_lookupABI bc kx segs kn rb.
Proof. intros bc kx segs kn rb HK. fe. unfold know_lookupABIF, know_lookupABI. rewrite (know_lookupA0IF_eq bc kx segs rb HK). reflexivity. Qed.
Lemma ctz_fuelF_eq : forall f z, ctz_fuelF f z = ctz_fuel f z.
Proof.
  intros f. induction f as [|f IH]; intros z; [reflexivity|]. cbn [ctz_fuelF ctz_fuel].
  rewrite IH, Zmod_odd, <- Z.div2_div. destruct (Z.odd z); reflexivity.
Qed.
Lemma ctz64F_fe : ctz64F = ctz64.
Proof. fe. unfold ctz64F, ctz64. apply ctz_fuelF_eq. Qed.
Lemma ealign0F_eq : forall kn e, ealign0F kn e = ealign0 kn e.
Proof.
  intros kn e. induction e; cbn [ealign0F ealign0]; rewrite ?ctz64F_fe, ?zmod64_eq2; try reflexivity; rewrite ?IHe1, ?IHe2; reflexivity.
Qed.
Lemma ealignBF_eq : ealignBF = ealignB.
Proof. fe. unfold ealignBF, ealignB. rewrite ealign0F_eq. reflexivity. Qed.
Lemma p2_eq : forall j, p2 j = (2 ^ j)%Z.
Proof. intros j. unfold p2. destruct (Z.leb_spec 0 j) as [H|H]; [apply Z.shiftl_1_l|reflexivity]. Qed.
Lemma p2_fe : p2 = fun j => (2 ^ j)%Z.
Proof. apply functional_extensionality; intros j. apply p2_eq. Qed.
Lemma narrow_maskBF_eq : narrow_maskBF = narrow_maskB.
Proof.
  fe. unfold narrow_maskBF, narrow_maskB. rewrite ctz64F_fe, p2_fe. cbv zeta beta.
  destruct (Z.ltb 0 x1); cbn [andb]; [|reflexivity].
  destruct (Z.eqb (x1 + 2 ^ ctz64 x1) (2 ^ Z.log2 (x1 + 2 ^ ctz64 x1))); reflexivity.
Qed.
Lemma modp2_eq : forall x j, modp2 x j = (x mod 2 ^ j)%Z.
Proof. intros x j. unfold modp2. destruct (Z.leb_spec 0 j) as [H|H]; [apply Z.land_ones; exact H|reflexivity]. Qed.
Lemma modp2_fe : modp2 = fun x j => (x mod 2 ^ j)%Z.
Proof. apply functional_extensionality; intros x. apply functional_extensionality; intros j. apply modp2_eq. Qed.
Lemma lowbitsBF_eq : forall bc e j, lowbitsBF bc e j = lowbitsB bc e j.
Proof.
  intros bc e j. induction e; cbn [lowbitsBF lowbitsB]; cbv zeta; rewrite ?ealignBF_eq, ?modp2_fe, ?zmod64_fe; cbv beta; try reflexivity.
  - destruct op; try reflexivity; rewrite ?IHe1, ?IHe2; try reflexivity; destruct e2; reflexivity.
  - destruct op; try reflexivity. destruct e1; try reflexivity. rewrite ?IHe2. reflexivity.
Qed.
Lemma lowbitsBF_fe : lowbitsBF = lowbitsB.
Proof. fe. apply lowbitsBF_eq. Qed.
Lemma lin_nowrapBF_eq : lin_nowrapBF = lin_nowrapB.
Proof. fe. unfold lin_nowrapBF, lin_nowrapB. rewrite BASF.erangeBF_fe. reflexivity. Qed.
Lemma lin_nowrap_lBF_eq : lin_nowrap_lBF = lin_nowrap_lB.
Proof. fe. unfold lin_nowrap_lBF, lin_nowrap_lB. rewrite BASF.erangeBF_fe. reflexivity. Qed.
Lemma mkSrlBF_eq : mkSrlBF = mkSrlB.
Proof.
  fe. unfold mkSrlBF, mkSrlB. rewrite lin_nowrapBF_eq, lin_nowrap_lBF_eq, BASF.erangeBF_fe. cbv zeta.
  destruct (lin_trivial (lin_of x0)); cbn [negb andb]; [reflexivity|].
  destruct (coeffs_div (2 ^ x1) (snd (lin_of x0))); destruct (lin_nowrapB x x0); reflexivity.
Qed.
Lemma mkAnd0BF_eq : mkAnd0BF = mkAnd0B.
Proof.
  fe. unfold mkAnd0BF, mkAnd0B. rewrite mkSrlBF_eq, ealignBF_eq, lowbitsBF_fe, p2_fe. destruct x1; try reflexivity. rewrite zmod64_eq2. cbv zeta beta.
  destruct (Z.eqb (two64 - z mod 2 ^ 64) (2 ^ Z.log2 (two64 - z mod 2 ^ 64))); cbn [andb].
  - reflexivity.
  - destruct (Z.eqb (z mod 2 ^ 64 + 1) (2 ^ Z.log2 (z mod 2 ^ 64 + 1))); reflexivity.
Qed.
Lemma mkAndBF_eq : mkAndBF = mkAndB.
Proof. fe. unfold mkAndBF, mkAndB. rewrite narrow_maskBF_eq, mkAnd0BF_eq. destruct x1; try reflexivity. rewrite zmod64_eq2. reflexivity. Qed.
Lemma mkAndKBF_eq : mkAndKBF = mkAndKB.
Proof. fe. unfold mkAndKBF, mkAndKB. rewrite mkAndBF_eq, !zmod64_fe. reflexivity. Qed.
Lemma mkAluL_fe : BASF.mkAluL = mkAlu.
Proof. fe. apply BASF.mkAluL_eq. Qed.
Lemma or_disjointBF_eq : or_disjointBF = or_disjointB.
Proof. fe. unfold or_disjointBF, or_disjointB. rewrite BASF.erangeBF_fe, ealignBF_eq. reflexivity. Qed.
Lemma mkOrBF_eq : mkOrBF = mkOrB.
Proof. fe. unfold mkOrBF, mkOrB. rewrite or_disjointBF_eq, mkAndKBF_eq. reflexivity. Qed.
Lemma mkAluK0BF_eq : mkAluK0BF = mkAluK0B.
Proof. fe. unfold mkAluK0BF, mkAluK0B. rewrite mkSrlBF_eq, mkOrBF_eq, mkAndBF_eq, mkAndKBF_eq, mkAluL_fe, zmod64_fe, BASF.expr_eqbF_fe. reflexivity. Qed.
Lemma foldKBF_fe : BASF.foldKBG = foldKB.
Proof. fe. apply BASF.foldKBG_eq. Qed.
Lemma mkAluKBF_eq : mkAluKBF = mkAluKB.
Proof. fe. unfold mkAluKBF, mkAluKB. rewrite mkAluK0BF_eq, foldKBF_fe. reflexivity. Qed.
Lemma mkMdKBF_eq : mkMdKBF = mkMdKB.
Proof. fe. unfold mkMdKBF, mkMdKB. rewrite mkAluKBF_eq. reflexivity. Qed.
Lemma amo_newvalBF_eq : amo_newvalBF = amo_newvalB.
Proof. fe. unfold amo_newvalBF, amo_newvalB. rewrite mkAluKBF_eq. reflexivity. Qed.
Lemma in_sides_disj_sides : forall bc kn b1 k1 n1 b2 k2 n2,
  in_sidesB bc (disj_sidesB bc kn b1 k1 n1) b2 k2 n2 = kdisj_apartB bc kn b1 k1 n1 b2 k2 n2.
Proof.
  intros bc kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [a w v|a l|a l k|lo hi|e m|e lo hi|a n|c1 m1 c2 m2|a l c|a l]; cbn [disj_sidesB kdisj_apartB]; try exact IH.
  destruct (sub_itvB bc b1 k1 n1 c1 m1) eqn:E1; destruct (sub_itvB bc b1 k1 n1 c2 m2) eqn:E2;
    cbn [in_sidesB]; rewrite ?IH; destruct (sub_itvB bc b2 k2 n2 c2 m2), (sub_itvB bc b2 k2 n2 c1 m1); reflexivity.
Qed.

Lemma kdisj_apartB_filter : forall bc kn, kdisj_apartB bc (List.filter is_kdisjb kn) = kdisj_apartB bc kn.
Proof.
  intros bc kn. induction kn as [|K rest IH]; [reflexivity|]. fe.
  destruct K; cbn [List.filter is_kdisjb kdisj_apartB]; rewrite IH; reflexivity.
Qed.
Lemma wr_coveredB_filter : forall bc kn, wr_coveredB bc (List.filter is_kwrb kn) = wr_coveredB bc kn.
Proof.
  intros bc kn. induction kn as [|K rest IH]; [reflexivity|]. fe.
  destruct K as [[]| | | | | |[]| | |]; cbn [List.filter is_kwrb wr_coveredB]; rewrite ?IH; reflexivity.
Qed.
Lemma ranges_apartBF_eq : forall bc b1 k1 n1 b2 k2 n2,
  ranges_apartBF bc (be_kd (mk_bext bc)) (base_rangeB bc b1) b1 k1 n1 b2 k2 n2 = ranges_apartB bc b1 k1 n1 b2 k2 n2.
Proof. intros. unfold ranges_apartBF, ranges_apartB. cbn [be_kd mk_bext]. rewrite kdisj_apartB_filter. reflexivity. Qed.
Lemma log_lookupBF_eq : forall bc log rb rk n sx hints acc obr,
  (obr = None \/ obr = Some (base_rangeB bc rb)) ->
  log_lookupBF bc (be_kd (mk_bext bc)) obr log rb rk n sx hints acc = log_lookupB bc log rb rk n sx hints acc.
Proof.
  intros bc log rb rk n sx. induction log as [|[[kb kk] w v] rest IH]; intros hints acc obr Hobr; [reflexivity|].
  cbn [log_lookupBF log_lookupB].
  assert (Hbr : match obr with Some r => r | None => base_rangeB bc rb end = base_rangeB bc rb)
    by (destruct Hobr as [->| ->]; reflexivity).
  rewrite rel_litF_eq.
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity.
  - apply IH. exact Hobr.
  - rewrite Hbr, ranges_apartBF_eq. destruct (ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w)).
    + apply IH. right. reflexivity.
    + destruct hints as [|[|] hs]; try reflexivity; apply IH; right; reflexivity.
Qed.
Lemma wr_numB_covered : forall bc kn a n, wr_numB bc kn a n = true -> wr_coveredB bc kn a n = true.
Proof.
  intros bc kn a n. induction kn as [|K rest IH]; cbn [wr_numB wr_coveredB]; [discriminate|].
  destruct K as [[]| | | | | |[kb kk] len| | |]; try exact IH.
  rewrite BASF.expr_eqbF_eq. destruct (expr_eqb (a_base a) kb); cbn [andb]; [|intros H; rewrite IH by exact H; destruct (xinsideB _ _ _ _ _ _ _); reflexivity].
  destruct (Z.leb kk (a_off a)); [|intros H; rewrite IH by exact H; destruct (xinsideB _ _ _ _ _ _ _); reflexivity].
  destruct (xloB bc len) as [l|]; [|intros H; rewrite IH by exact H; destruct (xinsideB _ _ _ _ _ _ _); reflexivity].
  destruct (Z.leb (a_off a + Z.of_nat n) (kk + l)); [reflexivity|].
  intros H. rewrite IH by exact H. destruct (xinsideB _ _ _ _ _ _ _); reflexivity.
Qed.
Lemma storeok_scBF_eq : forall bc, storeok_scBF bc (mk_bext bc) = storeok_scB bc.
Proof.
  intros. fe. unfold storeok_scBF, storeok_scB. cbn [be_kw mk_bext].
  destruct (wr_numB bc (List.filter is_kwrb (bc_fk bc)) x x0) eqn:E.
  - apply wr_numB_covered in E. rewrite wr_coveredB_filter in E. rewrite E. reflexivity.
  - rewrite wr_coveredB_filter. reflexivity.
Qed.
Lemma kdisj_apartB_sym : forall bc kn b1 k1 n1 b2 k2 n2, kdisj_apartB bc kn b1 k1 n1 b2 k2 n2 = kdisj_apartB bc kn b2 k2 n2 b1 k1 n1.
Proof.
  intros bc kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [a w v|a l|a l k|lo hi|e m|e lo hi|a n|c1 m1 c2 m2|a l c|a l]; cbn [kdisj_apartB]; try exact IH.
  rewrite IH. destruct (sub_itvB bc b1 k1 n1 c1 m1), (sub_itvB bc b2 k2 n2 c2 m2), (sub_itvB bc b1 k1 n1 c2 m2), (sub_itvB bc b2 k2 n2 c1 m1);
    reflexivity.
Qed.
Lemma ranges_apartBF2_eq : forall bc kb kk w v b1 k1 n1,
  ranges_apartBF2 bc (be_kd (mk_bext bc)) (mk_sctx bc (mk_bext bc) (SE (SA kb kk) w v)) (base_rangeB bc b1) b1 k1 n1 kb kk (Z.of_nat w)
  = ranges_apartB bc b1 k1 n1 kb kk (Z.of_nat w).
Proof.
  intros. unfold ranges_apartBF2, ranges_apartB. rewrite mk_sctx_rng, mk_sctx_D. cbn [a_base a_off].
  destruct (Z.eqb (zlit64 (Z.of_nat w)) (Z.of_nat w)) eqn:E.
  - apply Z.eqb_eq in E. rewrite E, in_sides_disj_sides, kdisj_apartB_sym. reflexivity.
  - cbn [be_kd mk_bext]. rewrite kdisj_apartB_filter. reflexivity.
Qed.
Lemma log_lookupBF2_eq : forall bc log rb rk n sx hints acc obr,
  (obr = None \/ obr = Some (base_rangeB bc rb)) ->
  log_lookupBF2 bc (be_kd (mk_bext bc)) obr log (map (mk_sctx bc (mk_bext bc)) log) rb rk n sx hints acc
  = log_lookupB bc log rb rk n sx hints acc.
Proof.
  intros bc log rb rk n sx. induction log as [|[[kb kk] w v] rest IH]; intros hints acc obr Hobr; [reflexivity|].
  cbn [map log_lookupBF2 log_lookupB].
  assert (Hbr : match obr with Some r => r | None => base_rangeB bc rb end = base_rangeB bc rb)
    by (destruct Hobr as [->| ->]; reflexivity).
  rewrite rel_litF_eq.
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity.
  - apply IH. exact Hobr.
  - rewrite Hbr, ranges_apartBF2_eq. destruct (ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w)).
    + apply IH. right. reflexivity.
    + destruct hints as [|[|] hs]; try reflexivity; apply IH; right; reflexivity.
Qed.
Lemma sym_readBIF_eq : forall segs ss bc kx, KXOK kx ->
  sym_readBIF segs ss bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) = sym_readBI segs ss bc kx.
Proof.
  intros segs ss bc kx HK. fe. unfold sym_readBIF, sym_readBI. rewrite log_lookupBF2_eq by (left; reflexivity).
  rewrite (know_lookupABIF_eq bc kx segs _ _ HK). reflexivity.
Qed.
Local Open Scope Z_scope.
Lemma bv_signedF_G : forall n (b : bv n), bv_signedF b = bv_signedG b.
Proof.
  intros n b. unfold bv_signedF.
  destruct (N.eqb_spec n 12) as [->|_]; [reflexivity|]. destruct (N.eqb_spec n 13) as [->|_]; [reflexivity|].
  destruct (N.eqb_spec n 21) as [->|_]; [reflexivity|]. destruct (N.eqb_spec n 20) as [->|_]; reflexivity.
Qed.
Lemma bv_signedF_eq : forall n (b : bv n), (0 < n)%N -> bv_signedF b = bv_signed b.
Proof.
  intros n b Hn. rewrite bv_signedF_G. unfold bv_signedG, bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  pose proof (bv_unsigned_in_range n b) as HR. unfold bv_modulus in HR.
  set (u := bv_unsigned b) in *. set (k := Z.of_N n) in *.
  assert (Hk : 1 <= k) by (unfold k; lia).
  assert (E1 : Z.shiftl 1 (k - 1) = 2 ^ (k - 1)) by (rewrite Z.shiftl_1_l; reflexivity).
  assert (E2 : 2 ^ k = 2 * 2 ^ (k - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (E3 : 2 ^ k / 2 = 2 ^ (k - 1)) by (rewrite E2, Z.mul_comm, Z.div_mul by lia; reflexivity).
  assert (E4 : Z.shiftl (2 ^ (k - 1)) 1 = 2 ^ k) by (rewrite Z.shiftl_mul_pow2 by lia; rewrite E2; lia).
  rewrite E1, E3, E4. pose proof (Z.pow_pos_nonneg 2 (k - 1) ltac:(lia) ltac:(lia)) as HP.
  destruct (Z.ltb_spec u (2 ^ (k - 1))) as [H|H].
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add (u + 2 ^ (k - 1)) (-1) (2 ^ k)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma bv_signedF_fe : forall n, (0 < n)%N -> @bv_signedF n = @bv_signed n.
Proof. intros n Hn. fe. apply bv_signedF_eq. exact Hn. Qed.
Local Close Scope Z_scope.
Local Open Scope Z_scope.
Lemma zsigned64_swrap : forall u, 0 <= u < 2 ^ 64 -> zsigned64 u = bv_swrap 64 u.
Proof.
  intros u Hu. unfold zsigned64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. unfold two63z, two64.
  change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 `div` 2) with (2 ^ 63).
  destruct (Z.leb_spec (2 ^ 63) u) as [H|H].
  - rewrite <- (Z.mod_add (u + 2 ^ 63) (-1) (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.
Lemma lit_branchF_eq : forall c x y, lit_branchF c x y = lit_branch c x y.
Proof.
  intros c x y. unfold lit_branchF, lit_branch, branch_taken, bv_eqb, bv_ltu, bv_lts, bv_signed. cbv zeta.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap at 1 2 3 4 5 6 7 8 9 10 11 12. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite !zmod64_eq.
  pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)) as Bx. pose proof (Z.mod_pos_bound y (2 ^ 64) ltac:(lia)) as By.
  rewrite !zsigned64_swrap by assumption. destruct c; reflexivity.
Qed.
Local Close Scope Z_scope.
Lemma decide_branchBF_eq : decide_branchBF = decide_branchB.
Proof.
  fe. unfold decide_branchBF, decide_branchB. rewrite BASF.erangeBF_fe, BASF.expr_eqbF_fe. destruct x1; try reflexivity. destruct x2; try reflexivity. rewrite lit_branchF_eq. reflexivity.
Qed.
Lemma decide_branchBF_h_eq : forall bc cache c a b, BASF.BCOK bc cache -> decide_branchBF_h bc cache c a b = decide_branchBF bc c a b.
Proof.
  intros bc cache c a b HC. unfold decide_branchBF_h, decide_branchBF. rewrite !(BASF.erange_h_eq bc cache _ HC), BASF.erangeBF_fe. reflexivity.
Qed.
Lemma zsx32F_eq : forall v, zsx32F v = zsx32 v.
Proof.
  intros v. unfold zsx32F, zsx32, bv_swrap, bv_wrap. rewrite zmod64_eq2, modp2_eq. reflexivity.
Qed.
Lemma zband32BF_fe : zband32BF = zband32B.
Proof. fe. unfold zband32BF, zband32B. rewrite BASF.erangeBF_fe. reflexivity. Qed.
Lemma mkAluwKBF_eq : mkAluwKBF = mkAluwKB.
Proof.
  fe. unfold mkAluwKBF, mkAluwKB, mkAluwK0BF, mkAluwK0B. rewrite foldKBF_fe, zband32BF_fe, BASF.erangeBF_fe. destruct x0; try reflexivity;
    (destruct (is_lit (mkAlu _ x1 x2)); [rewrite zsx32F_eq|]; reflexivity).
Qed.
Lemma conc_exprBF_fe : conc_exprBF = conc_exprB.
Proof. fe. unfold conc_exprBF, conc_exprB. rewrite BASF.concretizeBG_eq. reflexivity. Qed.
Lemma enum_branchBF_fe : enum_branchBF = enum_branchB.
Proof. fe. unfold enum_branchBF, enum_branchB. destruct (cond_probe x0 x1 x2). rewrite BASF.concretizeBG_eq. reflexivity. Qed.
Lemma p2n5_eq : forall p, p2n5 p = Pos.to_nat p.
Proof. intros p. do 5 (try destruct p as [p|p|]); reflexivity. Qed.
Lemma ridxF_fe : ridxF = ridx.
Proof. fe. unfold ridxF, ridx. destruct (bv_unsigned x) as [|p|p]; try reflexivity. rewrite p2n5_eq. reflexivity. Qed.
Lemma sr_getF_fe : sr_getF = sr_get.
Proof. fe. unfold sr_getF, sr_get. rewrite ridxF_fe. reflexivity. Qed.
Lemma ssetF_fe : ssetF = sset.
Proof. fe. unfold ssetF, sset. rewrite ridxF_fe. reflexivity. Qed.
Lemma sym_stepBIF_eq : forall bc kx segs i ss scr, KXOK kx ->
  sym_stepBIF bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) segs i ss scr = sym_stepBI bc kx segs i ss scr.
Proof.
  intros bc kx segs i ss scr HK. unfold sym_stepBIF, sym_stepBI. rewrite sr_getF_fe, ssetF_fe, ridxF_fe, mkAluwKBF_eq, conc_exprBF_fe, enum_branchBF_fe. rewrite !(sym_readBIF_eq segs ss bc kx HK), storeok_scBF_eq, zmod64_fe, mkAluKBF_eq, mkMdKBF_eq, amo_newvalBF_eq, decide_branchBF_eq.
  rewrite (bv_signedF_fe 12 ltac:(lia)), (bv_signedF_fe 13 ltac:(lia)), (bv_signedF_fe 20 ltac:(lia)), (bv_signedF_fe 21 ltac:(lia)).
  reflexivity.
Qed.
Local Open Scope Z_scope.
Definition RAOK (br1 : option (Z * Z)) (rk n : Z) (ra : option (PrimInt63.int * PrimInt63.int)) : Prop :=
  match ra with
  | None => True
  | Some (x, y) => match br1 with
                   | Some (lo1, hi1) => Uint63.to_Z x = lo1 + rk + 2 ^ 61 /\ Uint63.to_Z y = hi1 + rk + n + 2 ^ 61
                   | None => False
                   end
  end.
Lemma rann_ok : forall br1 rk n, RAOK br1 rk n (rann br1 rk n).
Proof.
  intros [[lo1 hi1]|] rk n; cbn [rann RAOK]; [|exact I].
  destruct (zb (lo1 + rk)) as [x|] eqn:E1; [|exact I]. destruct (zb (hi1 + rk + n)) as [y|] eqn:E2; [|exact I].
  destruct (zb_spec _ _ E1) as [A1 _]. destruct (zb_spec _ _ E2) as [A2 _]. split; assumption.
Qed.
Lemma rann63_ok : forall e63 br1 rk n, (e63 = None \/ e63 = BASF.rng63 br1) -> RAOK br1 rk n (rann63 e63 br1 rk n).
Proof.
  intros e63 br1 rk n [->| ->]; [apply rann_ok|]. unfold rann63, BASF.rng63.
  destruct br1 as [[lo1 hi1]|]; [|apply rann_ok].
  destruct (BASF.zb lo1) as [lo63|] eqn:E1; [|apply rann_ok]. destruct (BASF.zb hi1) as [hi63|] eqn:E2; [|apply rann_ok].
  destruct (zb rk) as [k63|] eqn:E3; [|apply rann_ok]. destruct (IMGF.z61 n) as [n63|] eqn:E4; [|apply rann_ok].
  destruct (BASF.zb_spec _ _ E1) as [A1 B1]. destruct (BASF.zb_spec _ _ E2) as [A2 B2]. destruct (zb_spec _ _ E3) as [A3 B3].
  destruct (IMGF.z61_spec _ _ E4) as [A4 B4].
  assert (EB : Uint63.to_Z EXI.B61 = 2 ^ 61) by reflexivity.
  cbn [RAOK]. rewrite !Uint63.sub_spec, !Uint63.add_spec, !Uint63.sub_spec, !Uint63.add_spec, EB, A1, A2, A3, A4, wB63.
  rewrite (Z.mod_small (lo1 + 2 ^ 61 + (rk + 2 ^ 61))) by lia. rewrite (Z.mod_small (hi1 + 2 ^ 61 + (rk + 2 ^ 61))) by lia.
  rewrite (Z.mod_small (lo1 + 2 ^ 61 + (rk + 2 ^ 61) - 2 ^ 61)) by lia. rewrite (Z.mod_small (hi1 + 2 ^ 61 + (rk + 2 ^ 61) - 2 ^ 61)) by lia.
  rewrite Z.mod_small by lia. split; lia.
Qed.
Lemma i63apart_sound : forall br1 rk n ra sp kb kk w v, RAOK br1 rk n ra ->
  i63apart ra (sa_rng (sann_sp sp (SE (SA kb kk) w v))) = true ->
  (match br1, sp_rng sp with
   | Some (lo1, hi1), Some (lo2, hi2) => if Z.leb (hi1 + rk + n) (lo2 + kk) then true else Z.leb (hi2 + kk + Z.of_nat w) (lo1 + rk)
   | _, _ => false
   end) = true.
Proof.
  intros br1 rk n ra sp kb kk w v HR H. unfold i63apart, sann_sp in H. cbv zeta in H. cbn [sa_rng e_addr e_width a_off] in H.
  destruct ra as [[rlo rhi]|]; [|discriminate]. cbn [RAOK] in HR.
  destruct br1 as [[lo1 hi1]|]; [|contradiction]. destruct HR as [A1 A2].
  destruct (sp_rng sp) as [[lo2 hi2]|]; [|discriminate].
  destruct (zb (lo2 + kk)) as [slo|] eqn:E3; [|discriminate]. destruct (zb (hi2 + kk + Z.of_nat w)) as [shi|] eqn:E4; [|discriminate].
  destruct (zb_spec _ _ E3) as [A3 _]. destruct (zb_spec _ _ E4) as [A4 _].
  rewrite !IMGF.leb_b, A1, A2, A3, A4 in H.
  destruct (Z.leb_spec (hi1 + rk + n) (lo2 + kk)) as [L|L]; [reflexivity|].
  destruct (Z.leb_spec (hi1 + rk + n + 2 ^ 61) (lo2 + kk + 2 ^ 61)) as [C|_]; [lia|].
  destruct (Z.leb_spec (hi2 + kk + Z.of_nat w + 2 ^ 61) (lo1 + rk + 2 ^ 61)) as [C|_]; [|discriminate].
  apply Z.leb_le. lia.
Qed.
Lemma flat_scBFa_eq : forall ra br a n, RAOK br (a_off a) (Z.of_nat n) ra -> flat_scBFa ra br a n = flat_scBFr br a n.
Proof.
  intros [[x y]|] br a n H; [|reflexivity]. cbn [RAOK] in H. destruct br as [[lo hi]|]; [|contradiction]. destruct H as [H1 H2].
  unfold flat_scBFa, flat_scBFr. rewrite IMGF.leb_b, H1. change (Uint63.to_Z EXI.B61) with (2 ^ 61).
  pose proof (Uint63.to_Z_bounded y) as By. rewrite wB63 in By.
  assert (E2 : Z.leb (hi + a_off a + Z.of_nat n) two64 = true) by (apply Z.leb_le; unfold two64; lia). rewrite E2.
  destruct (Z.leb_spec (2 ^ 61) (lo + a_off a + 2 ^ 61)); destruct (Z.leb_spec 0 (lo + a_off a)); try reflexivity; lia.
Qed.
Local Close Scope Z_scope.
Lemma log_lookupBF3_eq : forall bc kd br1 ra (f : sentry -> sprep) log rb rk n sx hints acc,
  RAOK br1 rk (Z.of_nat n) ra ->
  log_lookupBF3 bc kd br1 ra log (map f log) (map (fun e => sann_sp (f e) e) log) rb rk n (Z.of_nat n) sx hints acc
  = log_lookupBF2 bc kd (Some br1) log (map f log) rb rk n sx hints acc.
Proof.
  intros bc kd br1 ra f log rb rk n sx hints acc Hra. revert hints acc.
  induction log as [|[[kb kk] w v] rest IH]; intros hints acc; [reflexivity|].
  cbn [map log_lookupBF3 log_lookupBF2]. change (sa_zw (sann_sp (f (SE (SA kb kk) w v)) (SE (SA kb kk) w v))) with (Z.of_nat w).
  destruct (rel_litF rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity; [apply IH|].
  assert (HA : i63apart ra (sa_rng (sann_sp (f (SE (SA kb kk) w v)) (SE (SA kb kk) w v))) = true ->
               ranges_apartBF2 bc kd (f (SE (SA kb kk) w v)) br1 rb rk (Z.of_nat n) kb kk (Z.of_nat w) = true).
  { intros HT. apply (i63apart_sound _ _ _ _ _ _ _ _ _ Hra) in HT. unfold ranges_apartBF2. rewrite HT. reflexivity. }
  destruct (i63apart ra (sa_rng (sann_sp (f (SE (SA kb kk) w v)) (SE (SA kb kk) w v)))).
  - rewrite (HA eq_refl). apply IH.
  - destruct (ranges_apartBF2 bc kd (f (SE (SA kb kk) w v)) br1 rb rk (Z.of_nat n) kb kk (Z.of_nat w)); [apply IH|].
    destruct hints as [|[|] hs]; try reflexivity; apply IH.
Qed.
(* [comment removed for export] *)
Lemma i63apart_hull : forall ra h r, i63apart ra (hull_join h r) = true -> i63apart ra h = true /\ i63apart ra r = true.
Proof.
  intros [[rlo rhi]|] [[a b]|] [[c d]|] H; cbn [i63apart hull_join] in *; try discriminate.
  rewrite !IMGF.leb_b in *. rewrite !IMGF.ltb_b in H.
  destruct (Z.ltb_spec (Uint63.to_Z c) (Uint63.to_Z a)); destruct (Z.ltb_spec (Uint63.to_Z b) (Uint63.to_Z d));
    destruct (Z.leb_spec (Uint63.to_Z rhi) (Uint63.to_Z a)); destruct (Z.leb_spec (Uint63.to_Z rhi) (Uint63.to_Z c));
    destruct (Z.leb_spec (Uint63.to_Z b) (Uint63.to_Z rlo)); destruct (Z.leb_spec (Uint63.to_Z d) (Uint63.to_Z rlo));
    try (split; reflexivity); exfalso;
    repeat match type of H with
           | (if ?x then _ else _) = _ => destruct x eqn:?
           end; try discriminate;
    repeat match goal with
           | E : Z.leb _ _ = true |- _ => apply Z.leb_le in E
           | E : Z.leb _ _ = false |- _ => apply Z.leb_gt in E
           end; lia.
Qed.
Lemma gl_find_add : forall gl kb en rng rb,
  gl_find (gl_add gl kb en rng) rb = if BASF.expr_eqbF rb kb then en :: gl_find gl rb else gl_find gl rb.
Proof.
  induction gl as [|g r IH]; intros kb en rng rb; cbn [gl_add gl_find lg_b lg_es]; [destruct (BASF.expr_eqbF rb kb); reflexivity|].
  destruct (BASF.expr_eqbF kb (lg_b g)) eqn:E; cbn [gl_find lg_b lg_es].
  - apply BASF.expr_eqbF_true in E. subst kb. destruct (BASF.expr_eqbF rb (lg_b g)); reflexivity.
  - rewrite IH. destruct (BASF.expr_eqbF rb (lg_b g)) eqn:E1; [|reflexivity].
    destruct (BASF.expr_eqbF rb kb) eqn:E2; [|reflexivity].
    apply BASF.expr_eqbF_true in E1, E2. subst. rewrite BASF.expr_eqbF_refl in E. discriminate.
Qed.
Lemma gl_others_add : forall gl kb en rng rb ra,
  gl_others_apart (gl_add gl kb en rng) rb ra = true ->
  gl_others_apart gl rb ra = true /\ (BASF.expr_eqbF rb kb = false -> i63apart ra rng = true).
Proof.
  induction gl as [|g r IH]; intros kb en rng rb ra H; cbn [gl_add gl_others_apart lg_b lg_hull] in *.
  - split; [reflexivity|]. intros E. rewrite E in H. destruct (i63apart ra rng); [reflexivity|discriminate].
  - destruct (BASF.expr_eqbF kb (lg_b g)) eqn:E; cbn [gl_others_apart lg_b lg_hull] in H.
    + apply BASF.expr_eqbF_true in E. subst kb. destruct (BASF.expr_eqbF rb (lg_b g)) eqn:E1.
      * split; [exact H|]. intros C. discriminate.
      * destruct (i63apart ra (hull_join (lg_hull g) rng)) eqn:HA; [|discriminate].
        apply i63apart_hull in HA. destruct HA as [HA1 HA2]. rewrite HA1. split; [exact H|]. intros _. exact HA2.
    + destruct (BASF.expr_eqbF rb (lg_b g)) eqn:E1.
      * apply IH in H. exact H.
      * destruct (i63apart ra (lg_hull g)); [|discriminate]. apply IH in H. exact H.
Qed.
Lemma le_scan_sound : forall bc kd br1 ra (f : sentry -> sprep) log rb rk n sx hints r,
  RAOK br1 rk (Z.of_nat n) ra ->
  gl_others_apart (GLof f log) rb ra = true ->
  le_scan (gl_find (GLof f log) rb) rk (Z.of_nat n) n sx hints = Some r ->
  log_lookupBF2 bc kd (Some br1) log (map f log) rb rk n sx hints [] = r.
Proof.
  intros bc kd br1 ra f log rb rk n sx hints r Hra. induction log as [|[[kb kk] w v] rest IH]; intros GA LS.
  - cbn in LS. injection LS as <-. reflexivity.
  - cbn [GLof] in GA, LS. unfold gl_adde in GA, LS. cbn [e_addr e_width e_val a_base a_off] in GA, LS.
    apply gl_others_add in GA. destruct GA as [GA1 GA2]. rewrite gl_find_add in LS.
    change (sa_zw (sann_sp (f (SE (SA kb kk) w v)) (SE (SA kb kk) w v))) with (Z.of_nat w) in LS.
    cbn [map log_lookupBF2]. unfold rel_litF. destruct (BASF.expr_eqbF rb kb) eqn:E.
    + cbn [le_scan] in LS.
      destruct (if Z.leb kk rk then Z.leb (rk + Z.of_nat n) (kk + Z.of_nat w) else false); [injection LS as <-; reflexivity|].
      destruct (if Z.leb (rk + Z.of_nat n) kk then true else Z.leb (kk + Z.of_nat w) rk); [|discriminate].
      apply IH; assumption.
    + assert (HT : ranges_apartBF2 bc kd (f (SE (SA kb kk) w v)) br1 rb rk (Z.of_nat n) kb kk (Z.of_nat w) = true).
      { specialize (GA2 eq_refl). apply (i63apart_sound _ _ _ _ _ _ _ _ _ Hra) in GA2.
        unfold ranges_apartBF2. rewrite GA2. reflexivity. }
      rewrite HT. apply IH; assumption.
Qed.
(* [comment removed for export] *)
Definition GOK (g : lgroup) : Prop := forall e, In e (lg_es g) -> (le_zw e <= lg_wmax g)%Z /\ In e (ibucket (lg_idx g) (le_k e)) /\ le_iv e = ivof (le_k e) (le_zw e).
Lemma idx_add_in : forall idx en e, e = en \/ In e (ibucket idx (le_k e)) -> In e (ibucket (idx_add idx en) (le_k e)).
Proof.
  intros idx en e H. unfold idx_add, ibucket at 1.
  destruct (Pos.eq_dec (kx_gkey (le_k e)) (kx_gkey (le_k en))) as [EK|NK].
  - rewrite EK, pt_gss. destruct H as [->|H]; [left; reflexivity|]. right. unfold ibucket in *. rewrite <- EK. exact H.
  - rewrite pt_gso by exact NK. destruct H as [->|H]; [contradiction|exact H].
Qed.
Lemma gl_add_ok : forall gl kb en rng, le_iv en = ivof (le_k en) (le_zw en) -> (forall g, In g gl -> GOK g) -> forall g, In g (gl_add gl kb en rng) -> GOK g.
Proof.
  induction gl as [|g0 r IH]; intros kb en rng HI H g Hg; cbn [gl_add] in Hg.
  - destruct Hg as [<-|[]]. intros e He. cbn [lg_es lg_wmax lg_idx] in *. destruct He as [<-|[]].
    split; [apply Z.le_refl|]. split; [|exact HI]. apply idx_add_in. left. reflexivity.
  - destruct (BASF.expr_eqbF kb (lg_b g0)).
    + destruct Hg as [<-|Hg]; [|apply H; right; exact Hg].
      intros e He. cbn [lg_es lg_wmax lg_idx] in *. destruct He as [<-|He].
      * split; [apply Z.le_max_r|]. split; [|exact HI]. apply idx_add_in. left. reflexivity.
      * destruct (H g0 (or_introl eq_refl) e He) as [A [B C]]. split; [etransitivity; [exact A|apply Z.le_max_l]|]. split; [|exact C]. apply idx_add_in. right. exact B.
    + destruct Hg as [<-|Hg]; [apply H; left; reflexivity|]. apply (IH kb en rng HI); [|exact Hg]. intros g1 H1. apply H. right. exact H1.
Qed.
Lemma GLof_ok : forall f log g, In g (GLof f log) -> GOK g.
Proof.
  intros f log. induction log as [|e rest IH]; intros g Hg; [destruct Hg|]. cbn [GLof] in Hg. unfold gl_adde in Hg.
  refine (gl_add_ok _ _ _ _ _ IH g Hg). reflexivity.
Qed.
Lemma gl_findg_spec : forall gl rb, match gl_findg gl rb with Some g => In g gl /\ lg_es g = gl_find gl rb | None => gl_find gl rb = [] end.
Proof.
  induction gl as [|g r IH]; intros rb; cbn [gl_findg gl_find]; [reflexivity|].
  destruct (BASF.expr_eqbF rb (lg_b g)); [split; [left; reflexivity|reflexivity]|].
  specialize (IH rb). destruct (gl_findg r rb); [destruct IH as [A B]; split; [right; exact A|exact B]|exact IH].
Qed.
Lemma bucket_clear_spec : forall l rk zn, bucket_clear l rk zn = true -> forall e, In e l -> le_disj e rk zn = true.
Proof.
  induction l as [|x r IH]; intros rk zn H e He; [destruct He|]. cbn [bucket_clear] in H.
  destruct (le_disj x rk zn) eqn:D; [|discriminate]. destruct He as [<-|He]; [exact D|apply (IH _ _ H e He)].
Qed.
Local Open Scope Z_scope.
Lemma win_clear_spec : forall idx cnt k rk zn, win_clear idx k cnt rk zn = true ->
  forall j, k <= j < k + Z.of_nat cnt -> bucket_clear (ibucket idx j) rk zn = true.
Proof.
  intros idx cnt. induction cnt as [|c IH]; intros k rk zn H j Hj; [lia|]. cbn [win_clear] in H.
  destruct (bucket_clear (ibucket idx k) rk zn) eqn:B; [|discriminate].
  destruct (Z.eq_dec j k) as [->|NE]; [exact B|]. apply (IH (k + 1) rk zn H). lia.
Qed.
Lemma grp_miss_sound : forall g rk zn, GOK g -> grp_miss g rk zn = true -> 0 < zn /\ forall e, In e (lg_es g) -> le_disj e rk zn = true.
Proof.
  intros g rk zn HG H. unfold grp_miss in H.
  destruct (Z.ltb_spec 24 (lg_cnt g)); [|discriminate]. destruct (Z.ltb_spec 0 zn) as [Hz|]; [|discriminate].
  destruct (Z.ltb_spec 0 (lg_wmax g)) as [Hw|]; [|discriminate]. destruct (Z.ltb_spec (lg_wmax g) 65); [|discriminate].
  split; [exact Hz|]. intros e He. destruct (HG e He) as [A [B _]].
  destruct (Z_lt_le_dec (le_k e) (rk - lg_wmax g + 1)) as [L|L].
  - unfold le_disj. destruct (Z.leb_spec (rk + zn) (le_k e)); [reflexivity|]. apply Z.leb_le. lia.
  - destruct (Z_lt_le_dec (le_k e) (rk + zn)) as [L2|L2].
    + apply (bucket_clear_spec _ _ _ (win_clear_spec _ _ _ _ _ H (le_k e) ltac:(rewrite Z2Nat.id by lia; lia)) e B).
    + unfold le_disj. destruct (Z.leb_spec (rk + zn) (le_k e)); [reflexivity|lia].
Qed.
Lemma le_scan_alldisj : forall es rk zn n sx hints, 0 < zn -> (forall e, In e es -> le_disj e rk zn = true) ->
  le_scan es rk zn n sx hints = Some (LMiss [] hints).
Proof.
  induction es as [|[kk zw w v iv] r IH]; intros rk zn n sx hints Hz H; [reflexivity|]. cbn [le_scan].
  pose proof (H _ (or_introl eq_refl)) as D. unfold le_disj in D. cbn [le_k le_zw] in D.
  destruct (Z.leb_spec kk rk) as [A|A].
  - destruct (Z.leb_spec (rk + zn) (kk + zw)) as [B|B].
    + exfalso. destruct (Z.leb_spec (rk + zn) kk); [lia|]. apply Z.leb_le in D. lia.
    + rewrite D. apply IH; [exact Hz|]. intros e He. apply H. right. exact He.
  - rewrite D. apply IH; [exact Hz|]. intros e He. apply H. right. exact He.
Qed.
Local Close Scope Z_scope.
Local Open Scope Z_scope.
Lemma ivof_spec : forall k w s e, ivof k w = Some (s, e) ->
  Uint63.to_Z s = k + 2 ^ 61 /\ Uint63.to_Z e = k + w + 2 ^ 61 /\ - 2 ^ 60 < k < 2 ^ 60 /\ 0 <= w < 2 ^ 61.
Proof.
  intros k w s e H. unfold ivof in H. destruct (zb k) as [s0|] eqn:Es; [|discriminate]. destruct (IMGF.z61 w) as [w63|] eqn:Ew; [|discriminate].
  injection H as <- <-. destruct (zb_spec _ _ Es) as [S1 S2]. destruct (IMGF.z61_spec _ _ Ew) as [W1 W2].
  rewrite Uint63.add_spec, S1, W1, wB63, Z.mod_small by lia. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
Qed.
Lemma le_scanI_eq : forall es rk zn n sx hints, (forall e, In e es -> le_iv e = ivof (le_k e) (le_zw e)) ->
  le_scanI es (ivof rk zn) rk zn n sx hints = le_scan es rk zn n sx hints.
Proof.
  induction es as [|[kk zw w v iv] r IH]; intros rk zn n sx hints H; [reflexivity|]. cbn [le_scanI le_scan].
  assert (IH' : le_scanI r (ivof rk zn) rk zn n sx hints = le_scan r rk zn n sx hints) by (apply IH; intros e He; apply H; right; exact He).
  pose proof (H _ (or_introl eq_refl)) as HI. cbn [le_iv le_k le_zw] in HI. subst iv.
  destruct (ivof kk zw) as [[s e]|] eqn:E1; [|rewrite IH'; reflexivity].
  destruct (ivof rk zn) as [[q qe]|] eqn:E2; [|rewrite IH'; reflexivity].
  destruct (ivof_spec _ _ _ _ E1) as (A1 & A2 & A3 & A4). destruct (ivof_spec _ _ _ _ E2) as (B1 & B2 & B3 & B4).
  rewrite !IMGF.leb_b, A1, A2, B1, B2, IH'.
  replace (Z.leb (kk + 2 ^ 61) (rk + 2 ^ 61)) with (Z.leb kk rk) by (destruct (Z.leb_spec kk rk), (Z.leb_spec (kk + 2 ^ 61) (rk + 2 ^ 61)); try reflexivity; lia).
  replace (Z.leb (rk + zn + 2 ^ 61) (kk + zw + 2 ^ 61)) with (Z.leb (rk + zn) (kk + zw)) by (destruct (Z.leb_spec (rk + zn) (kk + zw)), (Z.leb_spec (rk + zn + 2 ^ 61) (kk + zw + 2 ^ 61)); try reflexivity; lia).
  replace (Z.leb (rk + zn + 2 ^ 61) (kk + 2 ^ 61)) with (Z.leb (rk + zn) kk) by (destruct (Z.leb_spec (rk + zn) kk), (Z.leb_spec (rk + zn + 2 ^ 61) (kk + 2 ^ 61)); try reflexivity; lia).
  replace (Z.leb (kk + zw + 2 ^ 61) (rk + 2 ^ 61)) with (Z.leb (kk + zw) rk) by (destruct (Z.leb_spec (kk + zw) rk), (Z.leb_spec (kk + zw + 2 ^ 61) (rk + 2 ^ 61)); try reflexivity; lia).
  reflexivity.
Qed.
Local Close Scope Z_scope.
Lemma grp_scan_eq : forall gl rb rk zn n sx hints, (forall g, In g gl -> GOK g) ->
  grp_scan gl rb rk zn n sx hints = le_scan (gl_find gl rb) rk zn n sx hints.
Proof.
  intros gl rb rk zn n sx hints HG. unfold grp_scan. pose proof (gl_findg_spec gl rb) as S.
  destruct (gl_findg gl rb) as [g|]; [|rewrite S; reflexivity]. destruct S as [Sin Ses]. rewrite <- Ses.
  destruct (grp_miss g rk zn) eqn:M; [|apply le_scanI_eq; intros e He; apply (HG g Sin e He)].
  destruct (grp_miss_sound g rk zn (HG g Sin) M) as [Hz HD]. symmetry. apply le_scan_alldisj; assumption.
Qed.
Lemma log_lookupG_eq : forall bc kd br1 ra (f : sentry -> sprep) log rb rk n sx hints,
  RAOK br1 rk (Z.of_nat n) ra ->
  log_lookupG bc kd br1 ra (GLof f log) log (map f log) (map (fun e => sann_sp (f e) e) log) rb rk n (Z.of_nat n) sx hints
  = log_lookupBF2 bc kd (Some br1) log (map f log) rb rk n sx hints [].
Proof.
  intros bc kd br1 ra f log rb rk n sx hints Hra. unfold log_lookupG. rewrite (grp_scan_eq _ _ _ _ _ _ _ (GLof_ok f log)).
  destruct (gl_others_apart (GLof f log) rb ra) eqn:GA; [|apply log_lookupBF3_eq; exact Hra].
  destruct (le_scan (gl_find (GLof f log) rb) rk (Z.of_nat n) n sx hints) as [r|] eqn:LS; [|apply log_lookupBF3_eq; exact Hra].
  symmetry. apply (le_scan_sound bc kd br1 ra f log rb rk n sx hints r Hra GA LS).
Qed.
Lemma sym_readBIFr_spec : forall segs ss bc kx c scr e63 a n sx', KXOK kx -> BASF.BCOK bc c ->
  (e63 = None \/ e63 = BASF.rng63 (base_rangeB bc (a_base a))) ->
  fst (sym_readBIFr segs ss bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss))
    (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c scr (base_rangeB bc (a_base a)) e63 a n sx')
  = sym_readBI segs ss bc kx scr a n sx'
  /\ BASF.BCOK bc (snd (sym_readBIFr segs ss bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss))
    (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c scr (base_rangeB bc (a_base a)) e63 a n sx')).
Proof.
  intros segs ss bc kx c scr e63 a n sx' HK HC HE. unfold sym_readBIFr, sym_readBI. cbv zeta.
  pose proof (rann63_ok e63 (base_rangeB bc (a_base a)) (a_off a) (Z.of_nat n) HE) as HR.
  rewrite (log_lookupG_eq _ _ _ _ _ _ _ _ _ _ _ HR).
  rewrite log_lookupBF2_eq by (right; reflexivity).
  rewrite (know_lookupABIF_eq bc kx segs _ _ HK). rewrite !(flat_scBFa_eq _ _ _ _ HR).
  destruct (log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) []) as [v scs hints|scs hints|].
  - destruct (BASF.foldKB_c_spec bc c (extK0B bc v) HC) as [E O]. destruct (BASF.foldKB_c bc c (extK0B bc v)) as [v' c'].
    cbn [fst snd] in *. subst v'. split; [reflexivity|exact O].
  - destruct (know_lookupABI bc kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs) as [v scs' hints'|scs' hints'|].
    + destruct (BASF.foldKB_c_spec bc c (extK0B bc v) HC) as [E O]. destruct (BASF.foldKB_c bc c (extK0B bc v)) as [v' c'].
      cbn [fst snd] in *. subst v'. split; [reflexivity|exact O].
    + split; [reflexivity|exact HC].
    + split; [reflexivity|exact HC].
  - split; [reflexivity|exact HC].
Qed.
Definition step_c_ok (bc : bctx) (kx : kix) (segs : list Segment) (c : BASF.bcache) (i : instr) (ss : sym_state) (scr : scripts) : Prop :=
  fst (sym_stepBIF_c bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c segs i ss scr) = sym_stepBI bc kx segs i ss scr
  /\ BASF.BCOK bc (snd (sym_stepBIF_c bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c segs i ss scr)).
Lemma step_c_default : forall bc kx segs c i ss scr, KXOK kx -> BASF.BCOK bc c ->
  sym_stepBIF_c bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c segs i ss scr
  = (sym_stepBIF bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) segs i ss scr, c) ->
  step_c_ok bc kx segs c i ss scr.
Proof. intros bc kx segs c i ss scr HK HC E. unfold step_c_ok. rewrite E. cbn [fst snd]. split; [apply sym_stepBIF_eq; exact HK|exact HC]. Qed.
Lemma step_c_opimm : forall bc kx segs c op rd rs imm ss scr, KXOK kx -> BASF.BCOK bc c -> step_c_ok bc kx segs c (OpImm op rd rs imm) ss scr.
Proof.
  intros bc kx segs c op rd rs imm ss scr HK HC.
  destruct op;
  try (unfold step_c_ok; cbn [sym_stepBIF_c]; cbv zeta; rewrite sr_getF_fe, ssetF_fe;
       match goal with |- context [BASF.foldKB_c bc c ?x] =>
         destruct (BASF.foldKB_c_spec bc c x HC) as [E1 O1]; destruct (BASF.foldKB_c bc c x) as [v c1] end;
       cbn [fst snd] in *; subst v; split; [|exact O1];
       unfold sym_stepBI, mkAluKB; rewrite mkAluK0BF_eq, (bv_signedF_eq 12 imm ltac:(lia)); reflexivity).
  unfold step_c_ok. cbn [sym_stepBIF_c]. cbv zeta. rewrite sr_getF_fe, ssetF_fe.
  destruct (BASF.mkAluKB_add_c_spec bc c (sr_get (s_regs ss) rs) (bv_signedF imm) HC) as [E1 O1].
  destruct (BASF.mkAluKB_add_c bc c (sr_get (s_regs ss) rs) (bv_signedF imm)) as [v c1]. cbn [fst snd] in *. subst v.
  split; [|exact O1]. rewrite (bv_signedF_eq 12 imm ltac:(lia)). reflexivity.
Qed.
Lemma step_c_shimm : forall bc kx segs c op rd rs sh ss scr, KXOK kx -> BASF.BCOK bc c -> step_c_ok bc kx segs c (ShiftImm op rd rs sh) ss scr.
Proof.
  intros bc kx segs c op rd rs sh ss scr HK HC.
  unfold step_c_ok. cbn [sym_stepBIF_c]. cbv zeta. rewrite sr_getF_fe, ssetF_fe.
  match goal with |- context [BASF.foldKB_c bc c ?x] =>
    destruct (BASF.foldKB_c_spec bc c x HC) as [E1 O1]; destruct (BASF.foldKB_c bc c x) as [v c1] end.
  cbn [fst snd] in *. subst v. split; [|exact O1]. unfold sym_stepBI, mkAluKB. rewrite mkAluK0BF_eq. reflexivity.
Qed.
Lemma step_c_op : forall bc kx segs c op rd rs1 rs2 ss scr, KXOK kx -> BASF.BCOK bc c -> step_c_ok bc kx segs c (Op op rd rs1 rs2) ss scr.
Proof.
  intros bc kx segs c op rd rs1 rs2 ss scr HK HC.
  assert (GEN : sym_stepBIF_c bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c segs (Op op rd rs1 rs2) ss scr
      = (let '(v, c1) := BASF.foldKB_c bc c (mkAluK0BF bc op (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2)) in (SOk (ssetF ss rd v (s_pc ss + 4)) [] scr, c1)) ->
      step_c_ok bc kx segs c (Op op rd rs1 rs2) ss scr).
  { intros EQ. unfold step_c_ok. rewrite EQ. rewrite ssetF_fe.
    match goal with |- context [BASF.foldKB_c bc c ?y] =>
      destruct (BASF.foldKB_c_spec bc c y HC) as [E1 O1]; destruct (BASF.foldKB_c bc c y) as [v c1] end.
    cbn [fst snd] in *. subst v. split; [|exact O1]. unfold sym_stepBI, mkAluKB. rewrite mkAluK0BF_eq. reflexivity. }
  destruct op; try (apply GEN; cbn [sym_stepBIF_c]; cbv zeta; rewrite sr_getF_fe; destruct (sr_get (s_regs ss) rs2); reflexivity).
  clear GEN.
  destruct (sr_get (s_regs ss) rs2) as [z| | | | | | |] eqn:E2;
  try (unfold step_c_ok; cbn [sym_stepBIF_c]; cbv zeta; rewrite sr_getF_fe, ssetF_fe, E2;
        match goal with |- context [BASF.foldKB_c bc c ?y] =>
          destruct (BASF.foldKB_c_spec bc c y HC) as [E1 O1]; destruct (BASF.foldKB_c bc c y) as [v c1] end;
        cbn [fst snd] in *; subst v; split; [|exact O1]; unfold sym_stepBI, mkAluKB; rewrite mkAluK0BF_eq, E2; reflexivity).
  unfold step_c_ok. cbn [sym_stepBIF_c]. cbv zeta. rewrite sr_getF_fe, ssetF_fe, E2.
  destruct (BASF.mkAluKB_add_c_spec bc c (sr_get (s_regs ss) rs1) z HC) as [E1 O1].
  destruct (BASF.mkAluKB_add_c bc c (sr_get (s_regs ss) rs1) z) as [v c1]. cbn [fst snd] in *. subst v.
  split; [|exact O1]. unfold sym_stepBI. rewrite E2. reflexivity.
Qed.
Lemma step_c_load : forall bc kx segs c sz sg rd rs imm ss scr, KXOK kx -> BASF.BCOK bc c -> step_c_ok bc kx segs c (Load sz sg rd rs imm) ss scr.
Proof.
  intros bc kx segs c sz sg rd rs imm ss scr HK HC. unfold step_c_ok. cbn [sym_stepBIF_c]. cbv zeta. rewrite sr_getF_fe, ridxF_fe.
  destruct (BASF.to_saddrKB_c_spec bc c (sr_get (s_regs ss) rs) (bv_signedF imm) HC) as [E1 O1].
  destruct (BASF.to_saddrKB_c bc c (sr_get (s_regs ss) rs) (bv_signedF imm)) as [a c1]. cbn [fst snd] in E1, O1. subst a.
  destruct (BASF.base_range63_c_spec bc c1 (a_base (to_saddrKB bc (sr_get (s_regs ss) rs) (bv_signedF imm))) O1) as (E2 & E2' & O2).
  destruct (BASF.base_range63_c bc c1 (a_base (to_saddrKB bc (sr_get (s_regs ss) rs) (bv_signedF imm)))) as [[br e63] c2]. cbn [fst snd] in E2, E2', O2. subst br.
  destruct (sym_readBIFr_spec segs ss bc kx c2 scr e63 (to_saddrKB bc (sr_get (s_regs ss) rs) (bv_signedF imm)) (msize_bytes sz)
              (match sz with SZ8 => false | _ => sg end) HK O2 E2') as [E3 O3].
  destruct (sym_readBIFr segs ss bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss))
              (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c2 scr
              (base_rangeB bc (a_base (to_saddrKB bc (sr_get (s_regs ss) rs) (bv_signedF imm)))) e63
              (to_saddrKB bc (sr_get (s_regs ss) rs) (bv_signedF imm)) (msize_bytes sz) (match sz with SZ8 => false | _ => sg end)) as [r c3].
  cbn [fst snd] in E3, O3. subst r.
  split; [|exact O3]. cbn [fst]. rewrite (bv_signedF_eq 12 imm ltac:(lia)). reflexivity.
Qed.
Lemma step_c_store : forall bc kx segs c sz rs1 rs2 imm ss scr, KXOK kx -> BASF.BCOK bc c -> step_c_ok bc kx segs c (Store sz rs1 rs2 imm) ss scr.
Proof.
  intros bc kx segs c sz rs1 rs2 imm ss scr HK HC. unfold step_c_ok. cbn [sym_stepBIF_c]. cbv zeta. rewrite sr_getF_fe.
  destruct (BASF.to_saddrKB_c_spec bc c (sr_get (s_regs ss) rs1) (bv_signedF imm) HC) as [E1 O1].
  destruct (BASF.to_saddrKB_c bc c (sr_get (s_regs ss) rs1) (bv_signedF imm)) as [a c1]. cbn [fst snd] in E1, O1. subst a.
  rewrite (bv_signedF_eq 12 imm ltac:(lia)) in *.
  unfold sym_stepBI. destruct (resv_inval (s_resv ss) (to_saddrKB bc (sr_get (s_regs ss) rs1) (bv_signed imm))) as [r'|]; [|split; [reflexivity|exact O1]].
  destruct (BASF.base_range_c_spec bc c1 (a_base (to_saddrKB bc (sr_get (s_regs ss) rs1) (bv_signed imm))) O1) as [E2 O2].
  destruct (BASF.base_range_c bc c1 (a_base (to_saddrKB bc (sr_get (s_regs ss) rs1) (bv_signed imm)))) as [br c2]. cbn [fst snd] in E2, O2. subst br.
  split; [|exact O2]. cbn [fst]. rewrite storeok_scBF_eq. reflexivity.
Qed.
Ltac use_addr HC c1 O1 :=
  match goal with
  | |- context [BASF.to_saddrKB_c ?bc ?c ?e ?imm] =>
      let E1 := fresh "E1" in let a := fresh "a" in
      destruct (BASF.to_saddrKB_c_spec bc c e imm HC) as [E1 O1];
      destruct (BASF.to_saddrKB_c bc c e imm) as [a c1]; cbn [fst snd] in E1, O1; subst a
  end.
Ltac use_br O1 c2 O2 :=
  match goal with
  | |- context [BASF.base_range_c ?bc ?c1 ?B] =>
      let E2 := fresh "E2" in let br := fresh "br" in
      destruct (BASF.base_range_c_spec bc c1 B O1) as [E2 O2];
      destruct (BASF.base_range_c bc c1 B) as [br c2]; cbn [fst snd] in E2, O2; subst br
  end.
Ltac use_br63 O1 c2 O2 E2' :=
  match goal with
  | |- context [BASF.base_range63_c ?bc ?c1 ?B] =>
      let E2 := fresh "E2" in let br := fresh "br" in let e63 := fresh "e63" in
      destruct (BASF.base_range63_c_spec bc c1 B O1) as (E2 & E2' & O2);
      destruct (BASF.base_range63_c bc c1 B) as [[br e63] c2]; cbn [fst snd] in E2, E2', O2; subst br
  end.
Ltac use_read HK O2 E2' c3 O3 :=
  match goal with
  | |- context [sym_readBIFr ?segs ?ss ?bc ?kx ?xc ?ex ?lis ?lia ?gl ?c2 ?scr (base_rangeB ?bc (a_base ?a)) ?e63 ?a ?n ?sx] =>
      let E3 := fresh "E3" in let r := fresh "r" in
      destruct (sym_readBIFr_spec segs ss bc kx c2 scr e63 a n sx HK O2 E2') as [E3 O3];
      destruct (sym_readBIFr segs ss bc kx xc ex lis lia gl c2 scr (base_rangeB bc (a_base a)) e63 a n sx) as [r c3]; cbn [fst snd] in E3, O3; subst r
  end.
Lemma step_c_lr : forall bc kx segs c wd aq rl rd rs ss scr, KXOK kx -> BASF.BCOK bc c -> step_c_ok bc kx segs c (Lr wd aq rl rd rs) ss scr.
Proof.
  intros bc kx segs c wd aq rl rd rs ss scr HK HC. unfold step_c_ok. cbn [sym_stepBIF_c]. cbv zeta. rewrite sr_getF_fe, ridxF_fe.
  unfold sym_stepBI. destruct (amo_alignedbB bc (sr_get (s_regs ss) rs) wd); [|split; [reflexivity|exact HC]].
  use_addr HC c1 O1. use_br63 O1 c2 O2 E2'. use_read HK O2 E2' c3 O3. split; [reflexivity|exact O3].
Qed.
Lemma step_c_sc : forall bc kx segs c wd aq rl rd rs1 rs2 ss scr, KXOK kx -> BASF.BCOK bc c -> step_c_ok bc kx segs c (Sc wd aq rl rd rs1 rs2) ss scr.
Proof.
  intros bc kx segs c wd aq rl rd rs1 rs2 ss scr HK HC. unfold step_c_ok. cbn [sym_stepBIF_c]. cbv zeta. rewrite sr_getF_fe, ridxF_fe.
  unfold sym_stepBI. destruct (amo_alignedbB bc (sr_get (s_regs ss) rs1) wd); [|split; [reflexivity|exact HC]].
  use_addr HC c1 O1. destruct (s_resv ss) as [r|]; [|split; [reflexivity|exact O1]].
  destruct (saddr_eqb r (to_saddrKB bc (sr_get (s_regs ss) rs1) 0)); [|split; [reflexivity|exact O1]].
  use_br O1 c2 O2. split; [|exact O2]. cbn [fst]. rewrite storeok_scBF_eq. reflexivity.
Qed.
Lemma step_c_amo : forall bc kx segs c op wd aq rl rd rs1 rs2 ss scr, KXOK kx -> BASF.BCOK bc c -> step_c_ok bc kx segs c (Amo op wd aq rl rd rs1 rs2) ss scr.
Proof.
  intros bc kx segs c op wd aq rl rd rs1 rs2 ss scr HK HC. unfold step_c_ok. cbn [sym_stepBIF_c]. cbv zeta. rewrite sr_getF_fe, ridxF_fe.
  unfold sym_stepBI. destruct (amo_aluop op) as [aop|]; [|split; [reflexivity|exact HC]].
  destruct (amo_alignedbB bc (sr_get (s_regs ss) rs1) wd); [|split; [reflexivity|exact HC]].
  use_addr HC c1 O1. destruct (resv_inval (s_resv ss) (to_saddrKB bc (sr_get (s_regs ss) rs1) 0)) as [r'|]; [|split; [reflexivity|exact O1]].
  use_br63 O1 c2 O2 E2'. use_read HK O2 E2' c3 O3. split; [|exact O3]. cbn [fst]. rewrite storeok_scBF_eq, amo_newvalBF_eq. reflexivity.
Qed.
Lemma step_c_branch : forall bc kx segs c cnd rs1 rs2 imm ss scr, KXOK kx -> BASF.BCOK bc c -> step_c_ok bc kx segs c (Branch cnd rs1 rs2 imm) ss scr.
Proof.
  intros bc kx segs c cnd rs1 rs2 imm ss scr HK HC. apply step_c_default; [exact HK|exact HC|].
  cbn [sym_stepBIF_c sym_stepBIF]. cbv zeta. rewrite (decide_branchBF_h_eq bc c cnd _ _ HC). reflexivity.
Qed.
Lemma sym_stepBIF_c_spec : forall bc kx segs c i ss scr, KXOK kx -> BASF.BCOK bc c -> step_c_ok bc kx segs c i ss scr.
Proof.
  intros bc kx segs c i ss scr HK HC.
  destruct i; first [apply step_c_opimm; assumption | apply step_c_shimm; assumption | apply step_c_op; assumption | apply step_c_branch; assumption | apply step_c_load; assumption | apply step_c_store; assumption
                    | apply step_c_lr; assumption | apply step_c_sc; assumption | apply step_c_amo; assumption
                    | apply step_c_default; [exact HK|exact HC|reflexivity]].
Qed.
Lemma sym_readBI_next : forall segs ss bc kx scr a n sx v scs scr' nx',
  sym_readBI segs ss bc kx scr a n sx = Some (v, scs, scr', nx') -> Nat.leb (s_next ss) nx' = true.
Proof.
  intros segs ss bc kx scr a n sx v scs scr' nx' H. unfold sym_readBI in H.
  destruct (log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx (sc_hints scr) []) as [v0 scs0 h0|scs0 h0|]; [| |discriminate].
  - injection H as _ _ _ <-. apply Nat.leb_refl.
  - destruct (know_lookupABI bc kx segs (s_know ss) (a_base a) (a_off a) n sx h0 scs0) as [v1 scs1 h1|scs1 h1|]; [| |discriminate].
    + injection H as _ _ _ <-. apply Nat.leb_refl.
    + injection H as _ _ _ <-. apply Nat.leb_le. apply Nat.le_succ_diag_r.
Qed.
Lemma step_next_mono : forall bc kx segs i ss scr ss' scs scr',
  sym_stepBI bc kx segs i ss scr = SOk ss' scs scr' -> Nat.leb (s_next ss) (s_next ss') = true.
Proof.
  intros bc kx segs i ss scr ss' scs scr' H. unfold sym_stepBI in H.
  destruct i; cbv beta iota zeta in H;
    repeat match type of H with
           | context [sym_readBI ?a ?b ?c ?d ?e ?f ?g ?h] =>
               let ER := fresh "ER" in
               destruct (sym_readBI a b c d e f g h) as [[[[? ?] ?] ?]|] eqn:ER; [apply sym_readBI_next in ER|]
           | context [match ?x with _ => _ end] => destruct x
           end; try discriminate; injection H as <- _ _; cbn [s_next sset sjump]; first [apply Nat.leb_refl | assumption].
Qed.
(* [comment removed for export] *)
Lemma existsb_ext' : forall (A : Type) (f g : A -> bool) l, (forall a, f a = g a) -> existsb f l = existsb g l.
Proof. intros A f g l H. induction l as [|a r IH]; [reflexivity|]. cbn [existsb]. rewrite H, IH. reflexivity. Qed.
Lemma existsbL_eq : forall (A : Type) (f : A -> bool) l, existsbL f l = existsb f l.
Proof. intros A f l. induction l as [|a r IH]; [reflexivity|]. cbn [existsbL existsb]. rewrite IH. reflexivity. Qed.
Lemma kentry_overlayBF_eq : forall bc rb rk n K, kentry_overlayBF bc rb rk (Z.of_nat n) K = kentry_overlayB bc rb rk n K.
Proof.
  intros bc rb rk n K. unfold kentry_overlayBF, kentry_overlayB, zf_coversBF, zf_coversB, elen. rewrite ?rel_litF_fe.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity;
    (destruct len; try reflexivity; rewrite zmod64_eq; reflexivity).
Qed.
Lemma kentry_readableBF_eq : forall bc rb rk n K, kentry_readableBF bc rb rk (Z.of_nat n) K = kentry_readableB bc rb rk n K.
Proof.
  intros bc rb rk n K. unfold kentry_readableBF, kentry_readableB. rewrite ?rel_litF_fe.
  destruct K as [[kb kk] w v|a len|a len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|a len c|a len]; try reflexivity; apply kentry_overlayBF_eq.
Qed.
Lemma kn_readableBF_eq : forall segs bc kn rb rk n, bc = mkbc (bc_fk bc) ->
  kn_readableBF segs bc kn rb rk n = kn_readable segs (bc_fk bc) kn rb rk n.
Proof.
  intros segs bc kn rb rk n HB. rewrite <- (kn_readableB_eqf segs (bc_fk bc)), <- HB.
  unfold kn_readableBF, kn_readableB. rewrite existsbL_eq.
  rewrite (existsb_ext' _ (kentry_readableBF bc rb rk (Z.of_nat n)) (kentry_readableB bc rb rk n) kn) by (intros K; apply kentry_readableBF_eq).
  reflexivity.
Qed.
Lemma kn_overlayBF_eq : forall segs bc kn rb rk n, bc = mkbc (bc_fk bc) ->
  kn_overlayBF segs bc kn rb rk n = kn_overlay segs (bc_fk bc) kn rb rk n.
Proof.
  intros segs bc kn rb rk n HB. rewrite <- (kn_overlayB_eqf segs (bc_fk bc)), <- HB.
  unfold kn_overlayBF, kn_overlayB. rewrite existsbL_eq.
  rewrite (existsb_ext' _ (kentry_overlayBF bc rb rk (Z.of_nat n)) (kentry_overlayB bc rb rk n) kn) by (intros K; apply kentry_overlayBF_eq).
  reflexivity.
Qed.
Lemma x_dischargeableBF_eq : forall segs bc ss ss' rb sc, bc = mkbc (bc_fk bc) ->
  x_dischargeableBF segs bc ss ss' rb sc = x_dischargeableB segs bc ss ss' rb sc.
Proof.
  intros segs bc ss ss' rb sc HB. unfold x_dischargeableBF, x_dischargeableB. cbv zeta.
  destruct sc as [t c a b|a n|a1 n1 a2 n2|a1 n1 a2 n2|a n|a n sx e|a b]; try reflexivity.
  - destruct n; try reflexivity. rewrite (kn_readableBF_eq segs bc _ _ _ _ HB).
    destruct (Z.leb 1 z); [|reflexivity]. destruct (Z.leb z 8); reflexivity.
  - rewrite (kn_overlayBF_eq segs bc _ _ _ _ HB). destruct (Nat.leb 1 n); [|reflexivity]. destruct (Nat.leb n 8); reflexivity.
  - destruct e; try reflexivity. rewrite (kn_readableBF_eq segs bc _ _ _ _ HB).
    destruct rb as [[[a' n'] sx']|]; [|reflexivity].
    destruct (saddr_eqb a' a); [|reflexivity]. destruct (Nat.eqb n' n); [|reflexivity]. destruct (Bool.eqb sx' sx); [|reflexivity]. cbn [andb].
    destruct (Nat.eqb n0 (s_next ss)); [|reflexivity]. destruct (Nat.ltb n0 (s_next ss')); [|reflexivity].
    destruct (evars_lt (s_next ss) (a_base a)); [|reflexivity]. destruct (Nat.leb 1 n); [|reflexivity]. destruct (Nat.leb n 8); reflexivity.
Qed.
Lemma x_filterBF_eq : forall segs bc ss ss' scs, bc = mkbc (bc_fk bc) -> x_filterBF segs bc ss ss' scs = x_filterB segs bc ss ss' scs.
Proof.
  intros segs bc ss ss' scs HB. unfold x_filterBF, x_filterB. destruct scs as [|sc rest]; [reflexivity|].
  apply filter_ext. intros x. rewrite (x_dischargeableBF_eq segs bc ss ss' _ x HB). reflexivity.
Qed.
Lemma sym_stepXBIF_spec : forall segs bc kx c K i ss scr, KXOK kx -> bc = mkbc (bc_fk bc) -> BASF.BCOK bc c ->
  fst (sym_stepXBIF segs bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c K i ss scr) = sym_stepXBI segs bc kx K i ss scr
  /\ BASF.BCOK bc (snd (sym_stepXBIF segs bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c K i ss scr)).
Proof.
  intros segs bc kx c K i ss scr HK HB HC. unfold sym_stepXBIF, sym_stepXBI.
  destruct (sym_stepBIF_c_spec bc kx segs c i ss scr HK HC) as [E O].
  destruct (sym_stepBIF_c bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c segs i ss scr) as [r c'].
  cbn [fst snd] in *. subst r. split; [|exact O].
  destruct (sym_stepBI bc kx segs i ss scr) as [ss' scs scr'|] eqn:E; [|reflexivity].
  rewrite (step_next_mono _ _ _ _ _ _ _ _ _ E), (x_filterBF_eq segs bc ss ss' scs HB). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma step_log : forall bc kx segs i ss scr ss' scs scr',
  sym_stepBI bc kx segs i ss scr = SOk ss' scs scr' ->
  if is_store_instr i then exists e, s_log ss' = e :: s_log ss else s_log ss' = s_log ss.
Proof.
  intros bc kx segs i ss scr ss' scs scr' H. unfold sym_stepBI in H.
  destruct i; cbv beta iota zeta in H; cbn [is_store_instr];
    repeat match type of H with
           | context [match ?x with _ => _ end] => destruct x
           end; try discriminate; injection H as <- _ _; cbn [s_log sset sjump]; eauto.
Qed.
Lemma is_stopF_eq : forall stops pc, is_stopF (mk_stt stops) stops pc = existsb (Z.eqb pc) stops.
Proof.
  intros stops pc. unfold is_stopF. destruct pc as [|p|p]; try reflexivity.
  induction stops as [|z r IH]; [cbn; rewrite pt_get_leaf; reflexivity|].
  cbn [mk_stt existsb]. destruct z as [|q|q]; try exact IH.
  change (Z.eqb (Zpos p) (Zpos q)) with (Pos.eqb p q). destruct (Pos.eqb_spec p q) as [->|NE].
  - rewrite pt_gss. reflexivity.
  - rewrite pt_gso by exact NE. exact IH.
Qed.
Lemma lupd_ok : forall segs bc kx K i ss scr ss' scs scr' wc,
  sym_stepXBI segs bc kx K i ss scr = SOk ss' scs scr' -> WCOK bc (mk_bext bc) wc ->
  exists wc', lupd bc (mk_bext bc) i ss' (map (mk_sctx bc (mk_bext bc)) (s_log ss)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss))
                (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) wc
              = (map (mk_sctx bc (mk_bext bc)) (s_log ss'), map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss'),
                 GLof (mk_sctx bc (mk_bext bc)) (s_log ss'), wc')
              /\ WCOK bc (mk_bext bc) wc'.
Proof.
  intros segs bc kx K i ss scr ss' scs scr' wc H HW. unfold sym_stepXBI in H.
  destruct (sym_stepBI bc kx segs i ss scr) as [ss1 scs1 scr1|] eqn:E; [|discriminate].
  destruct (Nat.leb (s_next ss) (s_next ss1)); [|discriminate]. injection H as <- _ _.
  assert (HL : s_log (cap_rd K i ss1) = s_log ss1).
  { unfold cap_rd. destruct K; [reflexivity|]. destruct (rd_of i) as [rd|]; [|reflexivity].
    destruct (bv_eqb rd 0); [reflexivity|]. destruct (esize_le (sr_get (s_regs ss1) rd) (S K)); reflexivity. }
  pose proof (step_log _ _ _ _ _ _ _ _ _ E) as HS. unfold lupd. rewrite HL.
  destruct (is_store_instr i).
  - destruct HS as [e He]. rewrite He.
    pose proof (mk_sctx_c_fst bc (mk_bext bc) wc e HW) as F1. pose proof (mk_sctx_c_ok bc (mk_bext bc) wc e HW) as F2.
    destruct (mk_sctx_c bc (mk_bext bc) wc e) as [sp wc']. cbn [fst snd] in *. subst sp. exists wc'. split; [reflexivity|exact F2].
  - rewrite HS. exists wc. split; [reflexivity|exact HW].
Qed.
(* [comment removed for export] *)
Lemma sym_stepBIF_cr_spec : forall segs bc kx c xm rm i ss scr, KXOK kx -> BASF.BCOK bc c -> XMOK bc xm -> BASF.RMOK bc rm ->
  let r := sym_stepBIF_cr bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss))
             (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c xm rm segs i ss scr in
  fst (fst (fst r)) = sym_stepBI bc kx segs i ss scr /\ BASF.BCOK bc (snd (fst (fst r))) /\ XMOK bc (snd (fst r)) /\ BASF.RMOK bc (snd r).
Proof.
  intros segs bc kx c xm rm i ss scr HK HC HX HR.
  set (lis := map (mk_sctx bc (mk_bext bc)) (s_log ss)). set (lia := map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)).
  set (gl := GLof (mk_sctx bc (mk_bext bc)) (s_log ss)).
  assert (DF : let r := (sym_stepBIF_cx bc kx (mk_xc segs kx) (mk_bext bc) lis lia gl c xm segs i ss scr, rm) in
               fst (fst (fst r)) = sym_stepBI bc kx segs i ss scr /\ BASF.BCOK bc (snd (fst (fst r))) /\ XMOK bc (snd (fst r)) /\ BASF.RMOK bc (snd r)).
  { cbv zeta. cbn [fst snd]. destruct (sym_stepBIF_cx_spec bc kx (mk_xc segs kx) (mk_bext bc) lis lia gl c xm segs i ss scr HX) as [E1 E2].
    destruct (sym_stepBIF_c_spec bc kx segs c i ss scr HK HC) as [E3 E4]. fold lis lia gl in E3, E4.
    rewrite E1. split; [exact E3|]. split; [exact E4|]. split; [exact E2|exact HR]. }
  assert (MEMO : forall rd e, sym_stepBI bc kx segs i ss scr = SOk (ssetF ss rd (BASF.foldKBG bc e) (s_pc ss + 4)) [] scr ->
            let r := (let '(v, rm') := BASF.foldKBM bc rm e in (SOk (ssetF ss rd v (s_pc ss + 4)) [] scr, c, xm, rm')) in
            fst (fst (fst r)) = sym_stepBI bc kx segs i ss scr /\ BASF.BCOK bc (snd (fst (fst r))) /\ XMOK bc (snd (fst r)) /\ BASF.RMOK bc (snd r)).
  { intros rd e HE. destruct (BASF.foldKBM_ok bc rm e HR) as [F1 F2]. destruct (BASF.foldKBM bc rm e) as [v rm']. cbn [fst snd] in *. subst v.
    split; [symmetry; exact HE|]. split; [exact HC|]. split; [exact HX|exact F2]. }
  pose proof (sym_stepBIF_eq bc kx segs i ss scr HK) as GEN. fold lis in GEN.
  unfold sym_stepBIF_cr. cbv zeta. fold lis lia gl.
  destruct i; try exact DF;
    repeat match goal with |- context [if BASF.bigE ?x then _ else _] => destruct (BASF.bigE x) end;
    first [exact DF | apply MEMO; rewrite <- GEN; reflexivity].
Qed.
Lemma sym_stepXBIFx_spec : forall segs bc kx c xm rm K i ss scr, KXOK kx -> bc = mkbc (bc_fk bc) -> BASF.BCOK bc c -> XMOK bc xm -> BASF.RMOK bc rm ->
  let r := sym_stepXBIFx segs bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss))
             (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c xm rm K i ss scr in
  fst (fst (fst r)) = sym_stepXBI segs bc kx K i ss scr /\ BASF.BCOK bc (snd (fst (fst r))) /\ XMOK bc (snd (fst r)) /\ BASF.RMOK bc (snd r).
Proof.
  intros segs bc kx c xm rm K i ss scr HK HB HC HX HR. cbv zeta. unfold sym_stepXBIFx, sym_stepXBI.
  destruct (sym_stepBIF_cr_spec segs bc kx c xm rm i ss scr HK HC HX HR) as (E & O1 & O2 & O3).
  destruct (sym_stepBIF_cr bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss))
              (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c xm rm segs i ss scr) as [[[r c'] xm'] rm'].
  cbn [fst snd] in *. subst r. split; [|split; [exact O1|split; [exact O2|exact O3]]].
  destruct (sym_stepBI bc kx segs i ss scr) as [ss' scs scr'|] eqn:E; [|reflexivity].
  rewrite (step_next_mono _ _ _ _ _ _ _ _ _ E), (x_filterBF_eq segs bc ss ss' scs HB). reflexivity.
Qed.
Lemma sym_execTXBIF_go_eq : forall segs bc kx t K fuel first stops ss ck wc c xm rm,
  KXOK kx -> bc = mkbc (bc_fk bc) -> WCOK bc (mk_bext bc) wc -> BASF.BCOK bc c -> XMOK bc xm -> BASF.RMOK bc rm ->
  sym_execTXBIF_go segs bc kx (mk_xc segs kx) (mk_bext bc) t K fuel first stops ss (map (mk_sctx bc (mk_bext bc)) (s_log ss))
    (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss))
    ck (map (mk_sctx bc (mk_bext bc)) (s_log ck)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ck))
    (GLof (mk_sctx bc (mk_bext bc)) (s_log ck)) wc c xm rm (mk_stt stops)
  = (sym_execTXBI_go segs bc kx t K fuel first stops ss ck,
     map (mk_sctx bc (mk_bext bc)) (s_log (sym_execTXBI_go segs bc kx t K fuel first stops ss ck))).
Proof.
  intros segs bc kx t K fuel. induction fuel as [|f IH]; intros first stops ss ck wc c xm rm HK HB HW HC HX HR.
  - cbn [sym_execTXBIF_go sym_execTXBI_go]. destruct (s_clean ss); reflexivity.
  - cbn [sym_execTXBIF_go sym_execTXBI_go]. rewrite is_stopF_eq.
    replace (if first then false else existsb (Z.eqb (s_pc ss)) stops) with (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool by (destruct first; reflexivity).
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [destruct (s_clean ss); reflexivity|].
    destruct (itab_lookup t (s_pc ss)) as [i|]; [|destruct (s_clean ss); reflexivity].
    destruct (sym_stepXBIFx_spec segs bc kx c xm rm K i ss scr_nil HK HB HC HX HR) as (EX & OX & OM & OR).
    destruct (sym_stepXBIFx segs bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss))
                (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c xm rm K i ss scr_nil) as [[[r c'] xm'] rm'].
    cbn [fst snd] in EX, OX, OM, OR. subst r.
    destruct (sym_stepXBI segs bc kx K i ss scr_nil) as [ss' [|sc scs] scr'|] eqn:E; try (destruct (s_clean ss); reflexivity).
    destruct (lupd_ok _ _ _ _ _ _ _ _ _ _ wc E HW) as [wc' [L1 L2]].
    destruct (is_store_instr i) eqn:IS.
    + rewrite L1. destruct (s_clean ss'); apply IH; assumption.
    + unfold lupd in L1. rewrite IS in L1. injection L1 as L1a L1b L1c L1d. rewrite L1a, L1b, L1c.
      destruct (s_clean ss'); apply IH; assumption.
Qed.
Lemma sym_execTXBIF_eq : forall segs bc kx t K fuel first stops ss, KXOK kx -> bc = mkbc (bc_fk bc) ->
  sym_execTXBIF segs bc kx (mk_xc segs kx) (mk_bext bc) t K fuel first stops ss
  = (sym_execTXBI segs bc kx t K fuel first stops ss,
     map (mk_sctx bc (mk_bext bc)) (s_log (sym_execTXBI segs bc kx t K fuel first stops ss))).
Proof.
  intros. unfold sym_execTXBIF, sym_execTXBI. cbv zeta.
  change (s_log ss) with (s_log (clr ss)). apply sym_execTXBIF_go_eq; [assumption|assumption|apply WCOK_empty|apply BASF.BCOK_nil|apply XMOK_nil|apply BASF.RMOK_nil].
Qed.

(* [comment removed for export] *)
Lemma stepx_nokx : forall segs bc kx xc kx' xc' ex lis lia gl c xm rm K i ss scr, needs_kx i = false ->
  sym_stepXBIFx segs bc kx xc ex lis lia gl c xm rm K i ss scr = sym_stepXBIFx segs bc kx' xc' ex lis lia gl c xm rm K i ss scr.
Proof.
  intros segs bc kx xc kx' xc' ex lis lia gl c xm rm K i ss scr H. unfold sym_stepXBIFx, sym_stepBIF_cr, sym_stepBIF_cx.
  destruct i; try discriminate; reflexivity.
Qed.
Lemma sym_execTXBIF_goL_eq : forall segs bc kn ex t K fuel okx first stops ss lis lia gl ck cklis cklia ckgl wc c xm rm stt,
  (okx = None \/ okx = Some (BLKF.mk_kix_f kn, mk_xc segs (BLKF.mk_kix_f kn))) ->
  sym_execTXBIF_goL segs bc kn okx ex t K fuel first stops ss lis lia gl ck cklis cklia ckgl wc c xm rm stt
  = sym_execTXBIF_go segs bc (BLKF.mk_kix_f kn) (mk_xc segs (BLKF.mk_kix_f kn)) ex t K fuel first stops ss lis lia gl ck cklis cklia ckgl wc c xm rm stt.
Proof.
  intros segs bc kn ex t K fuel. induction fuel as [|f IH]; intros okx first stops ss lis lia gl ck cklis cklia ckgl wc c xm rm stt HO; [reflexivity|].
  cbn [sym_execTXBIF_goL sym_execTXBIF_go].
  destruct (if first then false else is_stopF stt stops (s_pc ss)); [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  set (KX0 := BLKF.mk_kix_f kn) in *. set (XC0 := mk_xc segs KX0) in *.
  assert (G : exists okx', (okx' = None \/ okx' = Some (KX0, XC0)) /\
              (let '(kx, xc, okx1) := if needs_kx i then match okx with Some (kx, xc) => (kx, xc, okx) | None => (KX0, XC0, Some (KX0, XC0)) end else (kx_nil, xc_nil, okx) in
               (sym_stepXBIFx segs bc kx xc ex lis lia gl c xm rm K i ss scr_nil, okx1))
              = (sym_stepXBIFx segs bc KX0 XC0 ex lis lia gl c xm rm K i ss scr_nil, okx')).
  { destruct (needs_kx i) eqn:NK.
    - destruct HO as [->| ->]; exists (Some (KX0, XC0)); (split; [right; reflexivity|reflexivity]).
    - exists okx. split; [exact HO|]. rewrite (stepx_nokx segs bc kx_nil xc_nil KX0 XC0 ex lis lia gl c xm rm K i ss scr_nil NK). reflexivity. }
  destruct G as (okx' & HO' & GE).
  destruct (if needs_kx i then match okx with Some (kx, xc) => (kx, xc, okx) | None => (KX0, XC0, Some (KX0, XC0)) end else (kx_nil, xc_nil, okx)) as [[kx xc] okx1].
  injection GE as GE1 GE2. subst okx1. rewrite GE1.
  destruct (sym_stepXBIFx segs bc KX0 XC0 ex lis lia gl c xm rm K i ss scr_nil) as [[[r c'] xm'] rm'].
  destruct r as [ss' [|sc scs] scr'|]; try reflexivity.
  destruct (is_store_instr i).
  - destruct (lupd bc ex i ss' lis lia gl wc) as [[[lis' lia'] gl'] wc']. destruct (s_clean ss'); apply IH; exact HO'.
  - destruct (s_clean ss'); apply IH; exact HO'.
Qed.
Lemma sym_execTXBIFL_eq : forall segs bc kn ex t K fuel first stops ss,
  sym_execTXBIFL segs bc kn ex t K fuel first stops ss
  = sym_execTXBIF segs bc (BLKF.mk_kix_f kn) (mk_xc segs (BLKF.mk_kix_f kn)) ex t K fuel first stops ss.
Proof. intros. unfold sym_execTXBIFL, sym_execTXBIF. cbv zeta. apply sym_execTXBIF_goL_eq. left. reflexivity. Qed.
Lemma run_block_f_eq : forall segs IT nx0 K fuel stops cs, run_block_f segs IT nx0 K fuel stops cs = run_block segs IT nx0 K fuel stops cs.
Proof.
  intros. unfold run_block_f, run_block. rewrite sym_execTXBIFL_eq. rewrite BLKF.fresh_ok_f_eq, BLKF.mkbc_m_eq, BLKF.mk_kix_f_eq. destruct (fresh_ok nx0 cs); [|reflexivity]. cbv zeta.
  rewrite sym_execTXBIF_eq by (first [reflexivity | eexists; reflexivity]). rewrite carryKF_ctx_eq, carryKF_eq. reflexivity.
Qed.
Theorem run_block_gc_f_eq : forall segs IT nx0 K fuel stops cs,
  run_block_gc_f segs IT nx0 K fuel stops cs = run_block_gc segs IT nx0 K fuel stops cs.
Proof. intros. unfold run_block_gc_f, run_block_gc. rewrite run_block_f_eq. destruct (run_block segs IT nx0 K fuel stops cs); [rewrite BLKF.cs_gc_b_eq|]; reflexivity. Qed.

End EXF.
