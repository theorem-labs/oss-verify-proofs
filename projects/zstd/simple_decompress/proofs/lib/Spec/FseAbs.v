(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition runval (k : Z) : Z := (2^(2*(k/3)) - 1) + (k mod 3) * 2^(2*(k/3)).
Definition runw (k : Z) : Z := 2*(k/3) + 2.

(* [comment removed for export] *)
Definition cmax (r t : Z) : Z := 2*t - 1 - r.
Definition cval (c r t : Z) : Z := if t <=? c + 1 then c + 1 + cmax r t else c + 1.
Definition cwidth (c r t nb : Z) : Z := nb - (if cval c r t <? cmax r t then 1 else 0).

(* [comment removed for export] *)
Definition norm (r t nb : Z) : Z * Z :=
  if r <? t then (2^(Z.log2 r), Z.log2 r + 1) else (t, nb).

Lemma runval_range k : 0 <= k -> 0 <= runval k < 2^(runw k).
Proof.
  intros. unfold runval, runw.
  assert (0 <= k mod 3 < 3) by (apply Z.mod_pos_bound; lia).
  assert (0 <= k/3) by (apply Z.div_pos; lia).
  assert (0 < 2^(2*(k/3))) by (apply pow2_pos; lia).
  rewrite Z.pow_add_r by lia. change (2^2) with 4. nia.
Qed.

Lemma runw_pos k : 0 <= k -> 2 <= runw k <= k + 2.
Proof. intros; unfold runw. assert (0 <= k/3) by (apply Z.div_pos; lia). pose proof (Z.mul_div_le k 3 ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Lemma count_code_ok c r t nb :
  1 <= nb -> t = 2^(nb-1) -> t <= r < 2*t -> 2 <= r -> -1 <= c -> Z.abs c <= r - 1 ->
  let v := cval c r t in
  let w := cwidth c r t nb in
  0 <= cmax r t <= t - 1 /\ 0 <= v < 2^w /\ (w = nb \/ w = nb - 1) /\ 1 <= w /\
  (v = 1 <-> c = 0) /\
  forall x, 0 <= x -> x mod 2^w = v ->
    (if x mod t <? cmax r t then (x mod t, nb - 1)
     else ((if t <=? x mod 2^nb then x mod 2^nb - cmax r t else x mod 2^nb), nb))
    = (c + 1, w).
Proof.
  intros Hnb Ht Hr Hr2 Hc Habs. cbv zeta.
  assert (Ht2 : 2 <= t) by lia.
  assert (Hnb2 : 2 <= nb).
  { destruct (Z_lt_le_dec nb 2); [|lia]. assert (nb = 1) by lia. subst. simpl in Ht2. lia. }
  assert (Htnb : 2^nb = 2*t) by (subst t; rewrite <- pow2_S by lia; f_equal; lia).
  unfold cwidth, cval, cmax.
  destruct (Z.leb_spec t (c+1)).
  - (* [comment removed for export] *)
    destruct (Z.ltb_spec (c+1+(2*t-1-r)) (2*t-1-r)); [lia|].
    rewrite Z.sub_0_r. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    intros x Hx Hmod.
    replace (x mod t) with ((x mod 2^nb) mod t).
    2:{ subst t. apply mod_pow2_mod_pow2. lia. }
    rewrite Hmod. replace ((c+1+(2*t-1-r)) mod t) with (c+1+(2*t-1-r) - t).
    2:{ symmetry. replace (c+1+(2*t-1-r)) with ((c+1+(2*t-1-r)-t) + 1*t) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    destruct (Z.ltb_spec (c+1+(2*t-1-r)-t) (2*t-1-r)); [lia|].
    destruct (Z.leb_spec t (c+1+(2*t-1-r))); [|lia]. f_equal. lia.
  - destruct (Z.ltb_spec (c+1) (2*t-1-r)).
    + (* [comment removed for export] *)
      rewrite <- Ht.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      intros x Hx Hmod. rewrite Hmod.
      destruct (Z.ltb_spec (c+1) (2*t-1-r)); [|lia]. reflexivity.
    + (* [comment removed for export] *)
      rewrite Z.sub_0_r. 
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      intros x Hx Hmod.
      replace (x mod t) with ((x mod 2^nb) mod t).
      2:{ subst t. apply mod_pow2_mod_pow2. lia. }
      rewrite Hmod. rewrite (Z.mod_small (c+1) t) by lia.
      destruct (Z.ltb_spec (c+1) (2*t-1-r)); [lia|].
      destruct (Z.leb_spec t (c+1)); [lia|]. reflexivity.
Qed.

Lemma norm_spec r t nb :
  1 <= r -> 1 <= nb -> t = 2^(nb-1) -> r < 2*t ->
  let '(t', nb') := norm r t nb in
  t' = 2^(nb'-1) /\ 1 <= nb' <= nb /\ t' <= r < 2*t'.
Proof.
  intros. unfold norm. destruct (Z.ltb_spec r t).
  - pose proof (Z.log2_spec r ltac:(lia)) as [A B]. pose proof (Z.log2_nonneg r).
    rewrite Z.pow_succ_r in B by lia.
    assert (Z.log2 r < nb - 1).
    { apply Z.log2_lt_pow2; [lia|]. rewrite <- H1. lia. }
    repeat split; try lia. f_equal; lia.
  - repeat split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Valid.
  Variable nc : list Z.
  Variable maxSV tableLog : Z.
  Hypothesis V : valid_ncount nc maxSV tableLog.

  Let L := tableLog.

  Definition psum (j : Z) : Z := wsum (firstn (Z.to_nat j) nc).

  Lemma V_len : length nc = 256%nat. Proof. destruct V; tauto. Qed.
  Lemma V_msv : 0 <= maxSV <= 255. Proof. destruct V; tauto. Qed.
  Lemma V_tl : 5 <= tableLog <= 12. Proof. destruct V as (_&_&A&_). unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG in A. lia. Qed.
  Lemma V_ge i : 0 <= i <= maxSV -> -1 <= Znth i nc. Proof. destruct V as (_&_&_&A&_). apply A. Qed.
  Lemma V_last : Znth maxSV nc <> 0. Proof. destruct V as (_&_&_&_&A&_). apply A. Qed.
  Lemma V_above i : maxSV < i -> Znth i nc = 0. Proof. destruct V as (_&_&_&_&_&A&_). apply A. Qed.
  Lemma V_sum : psum (maxSV + 1) = 2^tableLog. Proof. destruct V as (_&_&_&_&_&_&A). exact A. Qed.

  Lemma weight_nonneg c : -1 <= c -> 0 <= weight c.
  Proof. unfold weight. destruct (Z.eqb_spec c (-1)); lia. Qed.

  Lemma weight_abs c : -1 <= c -> Z.abs c = weight c.
  Proof. unfold weight. destruct (Z.eqb_spec c (-1)); lia. Qed.

  Lemma weight_zero_iff c : -1 <= c -> (weight c = 0 <-> c = 0).
  Proof. unfold weight. destruct (Z.eqb_spec c (-1)); lia. Qed.

  Lemma wsum_firstn_S n l : (n < length l)%nat ->
    wsum (firstn (S n) l) = wsum (firstn n l) + weight (nth n l 0).
  Proof.
    revert l. induction n; intros [|a l] H; cbn [length] in H; try lia.
    - cbn [firstn wsum nth]. lia.
    - specialize (IHn l ltac:(lia)). cbn [firstn wsum nth] in *. rewrite IHn. lia.
  Qed.

  Lemma psum_0 : psum 0 = 0. Proof. reflexivity. Qed.

  Lemma psum_S j : 0 <= j < 256 -> psum (j + 1) = psum j + weight (Znth j nc).
  Proof.
    intros. unfold psum, Znth. replace (Z.to_nat (j+1)) with (S (Z.to_nat j)) by lia.
    apply wsum_firstn_S. rewrite V_len. lia.
  Qed.

  Lemma psum_mono i j : 0 <= i <= j -> j <= maxSV + 1 -> psum i <= psum j.
  Proof.
    intros Hij Hj. pose proof V_msv.
    replace j with (i + Z.of_nat (Z.to_nat (j - i))) by lia.
    assert (Hk : i + Z.of_nat (Z.to_nat (j - i)) <= maxSV + 1) by lia.
    revert Hk. generalize (Z.to_nat (j - i)) as k. intros k. induction k; intros.
    - replace (i + Z.of_nat 0) with i by lia. lia.
    - replace (i + Z.of_nat (S k)) with ((i + Z.of_nat k) + 1) by lia.
      rewrite psum_S by lia.
      pose proof (weight_nonneg (Znth (i + Z.of_nat k) nc) ltac:(apply V_ge; lia)).
      assert (psum i <= psum (i + Z.of_nat k)) by (apply IHk; lia). lia.
  Qed.

  Lemma psum_le j : 0 <= j <= maxSV -> psum j <= 2^tableLog - 1.
  Proof.
    intros. pose proof V_msv. pose proof V_sum as S. rewrite psum_S in S by lia.
    pose proof (psum_mono j maxSV ltac:(lia) ltac:(lia)).
    pose proof (V_ge maxSV ltac:(lia)). pose proof V_last.
    pose proof (weight_zero_iff (Znth maxSV nc) ltac:(lia)).
    pose proof (weight_nonneg (Znth maxSV nc) ltac:(lia)). lia.
  Qed.

  Lemma psum_nonneg j : 0 <= j <= maxSV + 1 -> 0 <= psum j.
  Proof. intros. pose proof (psum_mono 0 j ltac:(lia) ltac:(lia)). rewrite psum_0 in *. lia. Qed.

  Lemma nc_upper i : 0 <= i <= maxSV -> weight (Znth i nc) <= 2^tableLog - psum i /\ Znth i nc <= 2^tableLog.
  Proof.
    intros. pose proof V_msv. pose proof (psum_mono (i+1) (maxSV+1) ltac:(lia) ltac:(lia)).
    rewrite V_sum in *. rewrite psum_S in * by lia.
    pose proof (psum_nonneg i ltac:(lia)). pose proof (V_ge i ltac:(lia)).
    unfold weight in *. destruct (Z.eqb_spec (Znth i nc) (-1)); lia.
  Qed.

  (* [comment removed for export] *)
  Fixpoint next_nz (fuel : nat) (j : Z) : Z :=
    match fuel with
    | O => j
    | S f => if (j <? maxSV + 1) && (Znth j nc =? 0) then next_nz f (j + 1) else j
    end.

  Lemma next_nz_spec fuel j :
    0 <= j <= maxSV -> (maxSV - j < Z.of_nat fuel) ->
    let j' := next_nz fuel j in
    j <= j' <= maxSV /\ Znth j' nc <> 0 /\ psum j' = psum j /\
    (forall i, j <= i < j' -> Znth i nc = 0).
  Proof.
    revert j. induction fuel; intros j Hj Hf; cbv zeta; [simpl in Hf; lia|].
    cbn [next_nz]. pose proof V_last as VL. pose proof V_msv.
    destruct (Z.ltb_spec j (maxSV + 1)); [|lia].
    destruct (Z.eqb_spec (Znth j nc) 0); cbn [andb].
    - assert (j <> maxSV) by (intros ->; tauto).
      destruct (IHfuel (j+1)) as (A & B & C & D); [lia|lia|].
      split; [lia|]. split; [auto|]. split.
      + rewrite C. rewrite psum_S by lia. rewrite e. unfold weight; simpl. lia.
      + intros i Hi. destruct (Z.eq_dec i j); [subst; auto|]. apply D. lia.
    - split; [lia|]. split; [auto|]. split; [auto|]. intros; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Record astate := mkA {
    a_sym : Z; a_rem : Z; a_thr : Z; a_nb : Z; a_p0 : bool; a_N : Z; a_T : Z }.

  (* [comment removed for export] *)
  Definition askip (a : astate) : Z * Z * Z :=
    if a_p0 a then
      let j := next_nz 256 (a_sym a) in
      let k := j - a_sym a in
      (j, a_N a + runval k * 2^(a_T a), a_T a + runw k)
    else (a_sym a, a_N a, a_T a).

  Definition astep (a : astate) : astate :=
    let '(sym, N, T) := askip a in
    let c := Znth sym nc in
    let r := a_rem a in
    let t := a_thr a in
    let nb := a_nb a in
    let r' := r - Z.abs c in
    let v := cval c r t in
    let w := cwidth c r t nb in
    let '(t', nb') := norm r' t nb in
    mkA (sym + 1) r' t' nb' (v =? 1) (N + v * 2^T) (T + w).

  Definition acond (a : astate) : bool := (a_sym a <? maxSV + 1) && (1 <? a_rem a).

  Fixpoint arun (fuel : nat) (a : astate) : astate :=
    match fuel with
    | O => a
    | S f => if acond a then arun f (astep a) else a
    end.

  Definition a0 : astate :=
    mkA 0 (2^tableLog + 1) (2^tableLog) (tableLog + 1) false (tableLog - FSE_MIN_TABLELOG) 4.

  Definition afinal : astate := arun (S (Z.to_nat (maxSV + 1))) a0.

  Definition ainv (a : astate) : Prop :=
    0 <= a_sym a <= maxSV + 1 /\
    a_rem a = 2^tableLog + 1 - psum (a_sym a) /\
    a_thr a = 2^(a_nb a - 1) /\ 1 <= a_nb a <= tableLog + 1 /\
    a_thr a <= a_rem a < 2 * a_thr a /\
    0 <= a_N a < 2^(a_T a) /\ 4 <= a_T a <= 4 + 15 * a_sym a.

  Lemma ainv_a0 : ainv a0.
  Proof.
    pose proof V_tl. pose proof V_msv.
    unfold ainv, a0; cbn [a_sym a_rem a_thr a_nb a_p0 a_N a_T].
    rewrite psum_0. replace (tableLog + 1 - 1) with tableLog by lia.
    assert (0 < 2^tableLog) by (apply pow2_pos; lia).
    assert (32 <= 2^tableLog) by (change 32 with (2^5); apply Z.pow_le_mono_r; lia).
    unfold FSE_MIN_TABLELOG. change (2^4) with 16. repeat split; lia.
  Qed.

  Lemma acond_true a : ainv a -> acond a = true <-> a_sym a <= maxSV.
  Proof.
    intros (A & B & _). unfold acond. pose proof V_msv.
    destruct (Z.ltb_spec (a_sym a) (maxSV + 1)); destruct (Z.ltb_spec 1 (a_rem a)); simpl; split; auto; try lia; intros _; exfalso.
    assert (a_sym a <= maxSV) by lia. pose proof (psum_le (a_sym a) ltac:(lia)). lia.
  Qed.

  Lemma acond_false a : ainv a -> acond a = false -> a_sym a = maxSV + 1 /\ a_rem a = 1.
  Proof.
    intros I C. pose proof (acond_true a I) as AT. destruct I as (A & B & _).
    assert (E : a_sym a = maxSV + 1).
    { destruct (Z_lt_le_dec maxSV (a_sym a)); [lia|]. apply AT in l. congruence. }
    split; auto. rewrite E, V_sum in B. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma askip_spec a :
    ainv a -> a_sym a <= maxSV ->
    let '(j, N1, T1) := askip a in
    a_sym a <= j <= maxSV /\ psum j = psum (a_sym a) /\
    0 <= N1 < 2^T1 /\ a_T a <= T1 /\ N1 mod 2^(a_T a) = a_N a /\
    T1 + 13 <= 4 + 15 * (j + 1) /\
    (a_p0 a = true ->
       j = next_nz 256 (a_sym a) /\
       N1 = a_N a + runval (j - a_sym a) * 2^(a_T a) /\ T1 = a_T a + runw (j - a_sym a) /\
       Znth j nc <> 0 /\ (forall i, a_sym a <= i < j -> Znth i nc = 0)) /\
    (a_p0 a = false -> j = a_sym a /\ N1 = a_N a /\ T1 = a_T a).
  Proof.
    intros I Hs. destruct I as (A & B & C & D & E & F & G). pose proof V_msv.
    unfold askip. destruct (a_p0 a) eqn:P.
    - pose proof (next_nz_spec 256 (a_sym a) ltac:(lia) ltac:(simpl; lia)) as (J1 & J2 & J3 & J4).
      set (j := next_nz 256 (a_sym a)) in *.
      pose proof (runval_range (j - a_sym a) ltac:(lia)).
      pose proof (runw_pos (j - a_sym a) ltac:(lia)).
      pose proof (append_bound (a_N a) (runval (j - a_sym a)) (a_T a) (runw (j - a_sym a)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      repeat split; auto; try lia; try (intros; discriminate).
      apply low_bits_append; lia.
    - repeat split; auto; try lia; try (intros; discriminate).
      apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma acount_pre a j :
    ainv a -> a_sym a <= j <= maxSV -> psum j = psum (a_sym a) ->
    let c := Znth j nc in
    let r := a_rem a in
    -1 <= c /\ Z.abs c = weight c /\ Z.abs c <= r - 1 /\ 2 <= r /\
    r - Z.abs c = 2^tableLog + 1 - psum (j + 1) /\ 1 <= r - Z.abs c /\
    (j < maxSV -> 2 <= r - Z.abs c) /\ (j = maxSV <-> r - Z.abs c = 1) /\
    1 <= a_nb a /\ a_thr a = 2^(a_nb a - 1) /\ a_thr a <= r < 2 * a_thr a /\ 2 <= a_thr a /\
    c <= 2^tableLog.
  Proof.
    intros I Hj Hps. destruct I as (A & B & C & D & E & F & G). pose proof V_msv. cbv zeta.
    pose proof (V_ge j ltac:(lia)) as Cge.
    rewrite (weight_abs _ Cge).
    pose proof (psum_S j ltac:(lia)) as PS.
    pose proof (psum_le j ltac:(lia)).
    pose proof (nc_upper j ltac:(lia)) as [U1 U2].
    assert (Hlast : j = maxSV <-> psum (j+1) = 2^tableLog).
    { split. - intros ->. apply V_sum.
      - intros HH. destruct (Z.eq_dec j maxSV); auto. exfalso.
        pose proof (psum_le (j+1) ltac:(lia)). lia. }
    assert (j < maxSV -> psum (j+1) <= 2^tableLog - 1).
    { intros. apply psum_le. lia. }
    pose proof (weight_nonneg _ Cge).
    repeat split; try lia.
  Qed.

  Lemma astep_ainv a :
    ainv a -> a_sym a <= maxSV ->
    ainv (astep a) /\ a_sym a < a_sym (astep a) /\
    a_T a < a_T (astep a) /\ a_N (astep a) mod 2^(a_T a) = a_N a.
  Proof.
    intros I Hs. pose proof (askip_spec a I Hs) as SK.
    unfold astep. destruct (askip a) as [[j N1] T1].
    destruct SK as (S1 & S2 & S3 & S4 & S5 & S6 & _ & _).
    pose proof (acount_pre a j I ltac:(lia) S2) as CP. cbv zeta in CP.
    destruct CP as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
    pose proof (count_code_ok (Znth j nc) (a_rem a) (a_thr a) (a_nb a) C9 C10 C11 C4 C1 C3) as CC.
    cbv zeta in CC. destruct CC as (K1 & K2 & K3 & K4 & K5 & _).
    pose proof (norm_spec (a_rem a - Z.abs (Znth j nc)) (a_thr a) (a_nb a) C6 C9 C10 ltac:(lia)) as NS.
    destruct (norm _ _ _) as [t' nb']. destruct NS as (N1' & N2' & N3').
    destruct I as (A & B & C & D & E & F & G).
    pose proof (append_bound N1 (cval (Znth j nc) (a_rem a) (a_thr a)) T1
                  (cwidth (Znth j nc) (a_rem a) (a_thr a) (a_nb a)) ltac:(lia) ltac:(lia) S3 K2).
    unfold ainv; cbn [a_sym a_rem a_thr a_nb a_p0 a_N a_T].
    pose proof V_tl.
    repeat split; try lia.
    rewrite mod_add_mul_pow2_le by lia. exact S5.
  Qed.

  Lemma arun_ainv f a : ainv a -> ainv (arun f a).
  Proof.
    revert a; induction f; intros a I; cbn [arun]; auto.
    destruct (acond a) eqn:C; auto. apply IHf.
    apply (proj1 (astep_ainv a I (proj1 (acond_true a I) C))).
  Qed.

  Lemma arun_prefix f a : ainv a ->
    a_T a <= a_T (arun f a) /\ a_N (arun f a) mod 2^(a_T a) = a_N a /\ a_sym a <= a_sym (arun f a).
  Proof.
    revert a; induction f; intros a I; cbn [arun].
    - destruct I as (A & B & C & D & E & F & G). repeat split; try lia. apply Z.mod_small; lia.
    - destruct (acond a) eqn:Cn.
      + pose proof (astep_ainv a I (proj1 (acond_true a I) Cn)) as (I' & Q1 & Q2 & Q3).
        destruct (IHf _ I') as (P1 & P2 & P3). destruct I as (A & _ & _ & _ & _ & F & G).
        repeat split; try lia.
        rewrite <- (mod_pow2_mod_pow2 _ (a_T (astep a)) (a_T a)) by lia. rewrite P2. exact Q3.
      + destruct I as (A & B & C & D & E & F & G). repeat split; try lia. apply Z.mod_small; lia.
  Qed.

  Lemma arun_done f a : ainv a -> maxSV - a_sym a < Z.of_nat f -> acond (arun f a) = false.
  Proof.
    revert a; induction f; intros a I Hf; cbn [arun].
    - pose proof (acond_true a I) as AT. simpl in Hf.
      destruct (acond a); auto. exfalso. pose proof (proj1 AT eq_refl). lia.
    - destruct (acond a) eqn:Cn; auto.
      pose proof (astep_ainv a I (proj1 (acond_true a I) Cn)) as (I' & Q1 & _).
      apply IHf; auto. pose proof (proj1 (acond_true a I) Cn). lia.
  Qed.

  Lemma arun_stable f a : acond a = false -> arun f a = a.
  Proof. destruct f; cbn [arun]; auto. intros ->. reflexivity. Qed.

  Lemma arun_split f g a : arun (f + g) a = arun g (arun f a).
  Proof.
    revert a; induction f; intros a; cbn [arun Nat.add]; auto.
    destruct (acond a) eqn:C; auto. rewrite arun_stable; auto.
  Qed.

  Lemma afinal_spec :
    ainv afinal /\ a_sym afinal = maxSV + 1 /\ a_rem afinal = 1 /\ acond afinal = false /\
    4 <= a_T afinal <= 4 + 15 * (maxSV + 1) /\ 0 <= a_N afinal < 2^(a_T afinal).
  Proof.
    pose proof V_msv.
    assert (I : ainv afinal) by (apply arun_ainv, ainv_a0).
    assert (C : acond afinal = false).
    { unfold afinal. apply arun_done. apply ainv_a0. cbn [a0 a_sym]. lia. }
    pose proof (acond_false _ I C) as [S R].
    destruct I as (A & B & C' & D & E & F & G) eqn:EI. clear EI.
    repeat split; auto; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma arun_afinal f : (Z.to_nat (maxSV + 1) <= f)%nat -> arun f a0 = afinal.
  Proof.
    intros. pose proof V_msv.
    assert (C : acond (arun (Z.to_nat (maxSV + 1)) a0) = false).
    { apply arun_done. apply ainv_a0. cbn [a0 a_sym]. lia. }
    unfold afinal.
    replace f with (Z.to_nat (maxSV + 1) + (f - Z.to_nat (maxSV + 1)))%nat by lia.
    replace (S (Z.to_nat (maxSV + 1))) with (Z.to_nat (maxSV + 1) + 1)%nat by lia.
    rewrite !arun_split. rewrite !(arun_stable _ (arun _ a0)) by exact C. reflexivity.
  Qed.

  Lemma arun_acond_done f : (Z.to_nat (maxSV + 1) <= f)%nat -> acond (arun f a0) = false.
  Proof.
    intros. pose proof V_msv. apply arun_done. apply ainv_a0. cbn [a0 a_sym]. lia.
  Qed.

End Valid.
