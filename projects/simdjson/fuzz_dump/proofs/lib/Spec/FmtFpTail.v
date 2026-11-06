(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim SoftFloat FmtFp FmtFpPre FmtFpProps FmtFpRun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Opaque zrepeat.
Local Opaque f128_mul f128_add f128_sub f128_div f128_of_d f128_to_d f128_le f128_ge f128_of_u32 f128_of_i32.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.
Local Ltac dnia := Z.div_mod_to_equations; nia.

Definition isdig (c : Z) : Prop := 48 <= c <= 57.

Definition gch (c : Z) : Prop := (48 <= c <= 57) \/ c = 43 \/ c = 45 \/ c = 46 \/ c = 69 \/ c = 101.
Lemma gch_dig : forall c, isdig c -> gch c. Proof. intros c H. left. exact H. Qed.

Lemma zsub_length : forall l i n, 0 <= i -> 0 <= n -> i + n <= zlength l -> length (zsub l i n) = Z.to_nat n.
Proof.
  intros l i n Hi Hn H. unfold zsub. rewrite length_firstn, length_skipn. unfold zlength in H. lia.
Qed.

Lemma zsub_Forall : forall (P : Z -> Prop) l i n, 0 <= i -> 0 <= n -> i + n <= zlength l ->
  (forall k, i <= k < i + n -> P (znth l k)) -> Forall P (zsub l i n).
Proof.
  intros P l i n Hi Hn H HP. apply Forall_nth. intros j d Hj.
  rewrite (nth_indep _ d 0) by exact Hj.
  rewrite zsub_length in Hj by lia.
  unfold zsub. rewrite nth_firstn. replace (j <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_skipn. specialize (HP (i + Z.of_nat j) ltac:(lia)). unfold znth in HP.
  destruct (Z.ltb_spec (i + Z.of_nat j) 0); [lia|]. replace (Z.to_nat i + j)%nat with (Z.to_nat (i + Z.of_nat j)) by lia. exact HP.
Qed.

Lemma zlength_app : forall (l1 l2 : list Z), zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_zsub : forall l i n, 0 <= i -> 0 <= n -> i + n <= zlength l -> zlength (zsub l i n) = n.
Proof. intros. unfold zlength. rewrite zsub_length by lia. lia. Qed.

Definition DIGk (x k : Z) : Prop := (x = 0 /\ k = 0) \/ (1 <= k /\ 10^(k-1) <= x < 10^k).

Lemma DIGk_exists : forall x n, 0 <= x < 10^n -> 0 <= n -> exists k, DIGk x k /\ 0 <= k <= n.
Proof.
  intros x n Hx Hn. destruct (Z.eq_dec x 0) as [->|NZ]. { exists 0. split; [left; lia| lia]. }
  revert x Hx NZ. pattern n. apply (Wf_Z.natlike_ind); [| | lia].
  - intros x Hx NZ. change (10^0) with 1 in Hx. lia.
  - intros m Hm IH x Hx NZ. destruct (Z.lt_ge_cases x (10^m)).
    + destruct (IH x ltac:(lia) NZ) as [k [Hk Hkn]]. exists k. split; [exact Hk| lia].
    + exists (Z.succ m). split; [| lia]. right. split; [lia|]. replace (Z.succ m - 1) with m by lia. lia.
Qed.

Lemma pow10_pos : forall k, 0 <= k -> 0 < 10^k. Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.

Lemma fmt_u_loop_spec : forall k fuel y s b, DIGk y k -> 0 <= y -> (Z.to_nat k < fuel)%nat -> k <= s <= zlength b ->
  exists b', fmt_u_loop fuel (y, s, b) = Some (0, s - k, b') /\ zlength b' = zlength b /\
    (forall i, s - k <= i < s -> isdig (znth b' i)) /\ (forall i, ~ (s - k <= i < s) -> znth b' i = znth b i).
Proof.
  intros k. destruct (Z.lt_ge_cases k 0) as [Hneg|Hk0].
  { intros fuel y s b [[_ K]|[K _]]; lia. }
  generalize Hk0. pattern k. apply Wf_Z.natlike_ind; [ | | exact Hk0].
  - intros _ fuel y s b D Hy Hf Hs. destruct D as [[-> _]|[? _]]; [|lia].
    destruct fuel as [|fuel]; [lia|]. cbn [fmt_u_loop Z.eqb negb]. exists b. rewrite Z.sub_0_r.
    split; [reflexivity|]. split; [reflexivity|]. split; [intros; lia| intros; reflexivity].
  - intros m Hm IH _ fuel y s b D Hy Hf Hs. destruct D as [[-> K]|[K R]]; [lia|].
    pose proof (pow10_pos m Hm) as P0.
    assert (E1 : 10 ^ Z.succ m = 10 * 10 ^ m) by (rewrite Z.pow_succ_r; lia).
    destruct fuel as [|fuel]; [lia|]. cbn [fmt_u_loop].
    replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. unfold fmt_u_loop_body.
    destruct (IH ltac:(lia) fuel (y / 10) (s - 1) (zupd b (s - 1) (CHR_0 + y mod 10))) as [b' (E & L & D1 & D2)].
    + destruct (Z.eq_dec m 0) as [->|M0].
      * left. split; [|reflexivity]. change (10^0) with 1 in R. change (10 ^ Z.succ 0) with 10 in R. dlia.
      * right. split; [lia|].
        assert (E2 : 10 ^ m = 10 * 10 ^ (m - 1)) by (replace m with (Z.succ (m - 1)) at 1 by lia; rewrite Z.pow_succ_r; lia).
        replace (Z.succ m - 1) with m in R by lia. pose proof (pow10_pos (m - 1) ltac:(lia)). dlia.
    + dlia.
    + lia.
    + rewrite zlength_zupd. lia.
    + rewrite E. exists b'. replace (s - 1 - m) with (s - Z.succ m) by lia.
      split; [reflexivity|]. split; [rewrite L; apply zlength_zupd|]. split.
      * intros i Hi. destruct (Z.eq_dec i (s - 1)) as [->|NE].
        -- rewrite D2 by lia. rewrite znth_zupd_eq by lia. unfold isdig, CHR_0. pose proof (Z.mod_pos_bound y 10 ltac:(lia)). lia.
        -- apply D1. lia.
      * intros i Hi. rewrite D2 by lia. apply znth_zupd_neq. lia.
Qed.

Lemma fmt_u_spec : forall x b s k, 0 <= x -> DIGk x k -> k <= 20 -> k <= s <= zlength b ->
  exists b', fmt_u x b s = Some (s - k, b') /\ zlength b' = zlength b /\
    (forall i, s - k <= i < s -> isdig (znth b' i)) /\ (forall i, ~ (s - k <= i < s) -> znth b' i = znth b i).
Proof.
  intros x b s k Hx D Hk Hs. unfold fmt_u.
  destruct (fmt_u_loop_spec k FMT_U_FUEL x s b D Hx ltac:(unfold FMT_U_FUEL; lia) Hs) as [b' (E & L & D1 & D2)].
  rewrite E. exists b'. auto.
Qed.

Lemma zfill_spec : forall s buf, 0 <= s <= 11 -> s <= zlength buf ->
  exists buf', fmt_fp_zfill ZFILL_FUEL (s, buf) = Some (0, buf') /\ zlength buf' = zlength buf /\
    (forall i, 0 <= i < s -> znth buf' i = CHR_0) /\ (forall i, ~ (0 <= i < s) -> znth buf' i = znth buf i).
Proof.
  intros s buf Hs Hl. rewrite fmt_fp_zfill_eq.
  destruct (wloop_total (fun st : Z * list Z => 0 <? fst st) fmt_fp_zfill_body
             (fun st => 0 <= fst st <= s /\ zlength (snd st) = zlength buf /\
                        (forall i, fst st <= i < s -> znth (snd st) i = CHR_0) /\
                        (forall i, ~ (fst st <= i < s) -> znth (snd st) i = znth buf i))
             (fun st => fst st))
    with (fuel := ZFILL_FUEL) (s := (s, buf)) as [[s' b'] (E & (R & L & F1 & F2) & C)].
  - intros [s1 b1] (R1 & L1 & G1 & G2) C1. cbn [fst snd] in *. apply Z.ltb_lt in C1. unfold fmt_fp_zfill_body. cbn [fst snd].
    split; [| lia]. split; [lia|]. split; [now rewrite zlength_zupd|]. split.
    + intros i Hi. destruct (Z.eq_dec i (s1 - 1)) as [->|]; [apply znth_zupd_eq; lia|]. rewrite znth_zupd_neq by lia. apply G1. lia.
    + intros i Hi. rewrite znth_zupd_neq by lia. apply G2. lia.
  - cbn [fst snd]. split; [lia|]. split; [reflexivity|]. split; [intros; lia| intros; reflexivity].
  - cbn [fst]. unfold ZFILL_FUEL. change (Z.of_nat 12) with 12. lia.
  - rewrite E. cbn [fst snd] in *. apply Z.ltb_ge in C. assert (s' = 0) by lia. subst s'.
    exists b'. split; [reflexivity|]. split; [exact L|]. split; [intros i Hi; apply F1; lia| intros i Hi; apply F2; lia].
Qed.

Lemma epad_spec : forall estr eb, 8 <= estr <= 12 -> zlength eb = 12 ->
  exists eb', fmt_fp_epad EPAD_FUEL (estr, eb) = Some (Z.min estr 10, eb') /\ zlength eb' = 12 /\
    (forall i, Z.min estr 10 <= i < estr -> znth eb' i = CHR_0) /\ (forall i, ~ (Z.min estr 10 <= i < estr) -> znth eb' i = znth eb i).
Proof.
  intros estr eb He Hl. rewrite fmt_fp_epad_eq.
  destruct (wloop_total (fun st : Z * list Z => 12 - fst st <? 2) fmt_fp_epad_body
             (fun st => Z.min estr 10 <= fst st <= estr /\ zlength (snd st) = 12 /\
                        (forall i, fst st <= i < estr -> znth (snd st) i = CHR_0) /\
                        (forall i, ~ (fst st <= i < estr) -> znth (snd st) i = znth eb i))
             (fun st => fst st - Z.min estr 10))
    with (fuel := EPAD_FUEL) (s := (estr, eb)) as [[e' b'] (E & (R & L & F1 & F2) & C)].
  - intros [e1 b1] (R1 & L1 & G1 & G2) C1. cbn [fst snd] in *. apply Z.ltb_lt in C1. unfold fmt_fp_epad_body. cbn [fst snd].
    split; [| lia]. split; [lia|]. split; [now rewrite zlength_zupd|]. split.
    + intros i Hi. destruct (Z.eq_dec i (e1 - 1)) as [->|]; [apply znth_zupd_eq; lia|]. rewrite znth_zupd_neq by lia. apply G1. lia.
    + intros i Hi. rewrite znth_zupd_neq by lia. apply G2. lia.
  - cbn [fst snd]. split; [lia|]. split; [exact Hl|]. split; [intros; lia| intros; reflexivity].
  - cbn [fst]. unfold EPAD_FUEL. change (Z.of_nat 4) with 4. lia.
  - rewrite E. cbn [fst snd] in *. apply Z.ltb_ge in C. assert (e' = Z.min estr 10) by lia. subst e'.
    exists b'. split; [reflexivity|]. split; [exact L|]. split; [exact F1| exact F2].
Qed.

Lemma cnt_spec : forall v e0, 0 <= v < NB ->
  exists k, fmt_fp_cnt TEN_FUEL v (10, e0) = Some (10^k, e0 + k - 1) /\ 1 <= k <= 9 /\ v < 10^k /\ (v <> 0 -> 10^(k-1) <= v).
Proof.
  intros v e0 Hv. rewrite fmt_fp_cnt_eq.
  destruct (wloop_total (fun s : Z * Z => fst s <=? v) fmt_fp_cnt_body
             (fun s => exists k, 1 <= k <= 10 /\ fst s = 10 ^ k /\ snd s = e0 + k - 1 /\ (k = 1 \/ 10^(k-1) <= v))
             (fun s => 11 - (snd s - e0))) with (fuel := TEN_FUEL) (s := (10, e0)) as [[i e] (E & [k (Hk & Hi & He & Hlow)] & C)].
  - intros [i e] [k (Hk & Hi & He & Hlow)] C1. cbn [fst snd] in *. subst i. apply Z.leb_le in C1.
    assert (k <= 9). { destruct (Z.le_gt_cases k 9); [assumption|]. exfalso.
      assert (10 ^ 10 <= 10 ^ k) by (apply Z.pow_le_mono_r; lia). change (10^10) with 10000000000 in *. unfold NB in Hv. lia. }
    unfold fmt_fp_cnt_body. cbn [fst snd]. split; [| lia]. exists (k + 1). split; [lia|]. split; [rewrite pow10_succ by lia; lia|].
    split; [lia|]. right. replace (k + 1 - 1) with k by lia. exact C1.
  - exists 1. cbn. repeat split; lia.
  - cbn [snd]. unfold TEN_FUEL. change (Z.of_nat 12) with 12. lia.
  - rewrite E. cbn [fst snd] in *. apply Z.leb_gt in C. subst i e. exists k. split; [reflexivity|].
    assert (k <= 9). { destruct (Z.le_gt_cases k 9); [assumption|]. exfalso. destruct Hlow as [->|Hlow]; [lia|].
      assert (10 ^ 9 <= 10 ^ (k-1)) by (apply Z.pow_le_mono_r; lia). change (10^9) with 1000000000 in *. unfold NB in Hv. lia. }
    split; [lia|]. split; [exact C|]. intros NZ. destruct Hlow as [->|Hlow]; [change (10^(1-1)) with 1; lia| exact Hlow].
Qed.

Lemma powi_spec : forall j2, 0 <= j2 <= 8 -> fmt_fp_powi TEN_FUEL (10, j2 + 1) = Some (10^(9 - j2), 9).
Proof.
  intros j2 Hj. rewrite fmt_fp_powi_eq.
  destruct (wloop_total (fun s : Z * Z => snd s <? 9) fmt_fp_powi_body
             (fun s => fst s = 10 ^ (snd s - j2) /\ j2 + 1 <= snd s <= 9)
             (fun s => 9 - snd s)) with (fuel := TEN_FUEL) (s := (10, j2 + 1)) as [[i j] (E & [Hi Hj'] & C)].
  - intros [i j] [Hi Hj2] C1. cbn [fst snd] in *. apply Z.ltb_lt in C1. subst i.
    unfold fmt_fp_powi_body. cbn [fst snd]. split; [|lia]. split; [|lia].
    replace (j + 1 - j2) with ((j - j2) + 1) by lia. rewrite pow10_succ by lia. lia.
  - cbn [fst snd]. split; [|lia]. replace (j2 + 1 - j2) with 1 by lia. reflexivity.
  - cbn [snd]. unfold TEN_FUEL. change (Z.of_nat 12) with 12. lia.
  - rewrite E. cbn [fst snd] in *. apply Z.ltb_ge in C. assert (j = 9) by lia. subst j i. reflexivity.
Qed.

Lemma carry_spec : forall big d a,
  zlength big = 128 -> 0 <= a <= d -> d < 128 ->
  (forall i, i <> d -> 0 <= znth big i < NB) -> 1 <= znth big d <= NB ->
  (a = 0 -> a < d /\ znth big 0 < NB - 1) ->
  exists big' d' a', fmt_fp_carry BIG_FUEL (big, d, a) = Some (big', d', a') /\
    zlength big' = 128 /\ W9 big' /\ 0 <= a' /\ (a' = a \/ (a' = a - 1 /\ d' = a' /\ znth big' a' = 1)) /\ a' <= d' <= d /\
    1 <= znth big' d' /\
    (forall i, i < a' -> znth big' i = znth big i) /\
    (forall i, a' <= i < d' -> znth big' i = znth big i) /\
    (forall i, d' < i <= d -> znth big' i = 0) /\
    (forall i, d < i -> znth big' i = znth big i) /\
    (d' = d -> big' = big).
Proof.
  intros big d a HL Had Hd128 Hoth Hd Ha0.
  rewrite fmt_fp_carry_eq.
  destruct (wloop_total (fun s : list Z * Z * Z => let '(b0, d0, _) := s in 999999999 <? znth b0 d0) fmt_fp_carry_body
    (fun s => let '(b, d1, a1) := s in
       zlength b = 128 /\
       ((a1 = a /\ a <= d1 <= d /\ 0 <= znth b d1 <= NB /\ (d1 < d -> znth b d1 = znth big d1 + 1) /\ (d1 = d -> b = big)) \/
        (a1 = a - 1 /\ 1 <= a /\ d1 = a1 /\ znth b d1 = 1)) /\
       (forall i, i <> d1 -> 0 <= znth b i < NB) /\
       (forall i, i < a1 -> znth b i = znth big i) /\
       (forall i, a1 <= i < d1 -> znth b i = znth big i) /\
       (forall i, d1 < i <= d -> znth b i = 0) /\
       (forall i, d < i -> znth b i = znth big i))
    (fun s => let '(b, d1, a1) := s in d1 - a + 2))
    with (fuel := BIG_FUEL) (s := (big, d, a)) as [[[b' d'] a'] (E & (L' & M' & O' & B' & U' & Z' & T') & C)].
  - intros [[b d1] a1] (L1 & M1 & O1 & B1 & U1 & Z1 & T1) C1. apply Z.ltb_lt in C1.
    destruct M1 as [(-> & R1 & V1 & PL & _)|(-> & A1 & -> & V1)]; [| rewrite V1 in C1; lia].
    unfold fmt_fp_carry_body.
    assert (VD : znth b d1 = NB) by (unfold NB in *; lia).
    assert (D1p : 1 <= d1).
    { destruct (Z.eq_dec d1 0) as [D0|]; [|lia]. exfalso. assert (a = 0) by lia.
      destruct (Ha0 ltac:(lia)) as [AD B0]. rewrite D0 in *. specialize (PL ltac:(lia)). unfold NB in *. lia. }
    destruct (Z.ltb_spec (d1 - 1) a) as [LT|GE].
    +
      assert (d1 = a) by lia. subst d1.
      split; [| lia]. split; [now rewrite !zlength_zupd|].
      assert (Vn : znth (zupd (zupd b a 0) (a - 1) 0) (a - 1) = 0) by (apply znth_zupd_eq; rewrite zlength_zupd; lia).
      rewrite Vn. change (u32 (0 + 1)) with 1.
      split. { right. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. apply znth_zupd_eq. rewrite !zlength_zupd. lia. }
      split. { intros i Hi. destruct (Z.eq_dec i a) as [->|].
               - rewrite znth_zupd_neq, znth_zupd_neq, znth_zupd_eq by lia. unfold NB; lia.
               - rewrite !znth_zupd_neq by lia. apply O1. lia. }
      split. { intros i Hi. rewrite !znth_zupd_neq by lia. apply B1. lia. }
      split. { intros i Hi. lia. }
      split. { intros i Hi. destruct (Z.eq_dec i a) as [->|].
               - rewrite znth_zupd_neq, znth_zupd_neq, znth_zupd_eq by lia. reflexivity.
               - rewrite !znth_zupd_neq by lia. apply Z1. lia. }
      intros i Hi. rewrite !znth_zupd_neq by lia. apply T1. lia.
    +
      split; [| lia]. split; [now rewrite !zlength_zupd|].
      assert (Wp : 0 <= znth b (d1 - 1) < NB) by (apply O1; lia).
      rewrite (znth_zupd_neq b d1 (d1 - 1)) by lia.
      rewrite u32_id by (unfold NB in *; lia).
      split. { left. split; [reflexivity|]. split; [lia|].
               rewrite znth_zupd_eq by (rewrite zlength_zupd; lia).
               split; [lia|]. split; [| intros; lia]. intros _. rewrite U1 by lia. reflexivity. }
      split. { intros i Hi. destruct (Z.eq_dec i d1) as [->|].
               - rewrite znth_zupd_neq, znth_zupd_eq by lia. unfold NB; lia.
               - rewrite !znth_zupd_neq by lia. apply O1. lia. }
      split. { intros i Hi. rewrite !znth_zupd_neq by lia. apply B1. lia. }
      split. { intros i Hi. rewrite !znth_zupd_neq by lia. apply U1. lia. }
      split. { intros i Hi. destruct (Z.eq_dec i d1) as [->|].
               - rewrite znth_zupd_neq, znth_zupd_eq by lia. reflexivity.
               - rewrite !znth_zupd_neq by lia. apply Z1. lia. }
      intros i Hi. rewrite !znth_zupd_neq by lia. apply T1. lia.
  - split; [exact HL|]. split. { left. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [intros; lia| intros; reflexivity]. }
    split; [exact Hoth|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; lia| intros; reflexivity].
  - unfold BIG_FUEL. change (Z.of_nat 130) with 130. lia.
  - rewrite E. apply Z.ltb_ge in C. exists b', d', a'. split; [reflexivity|]. split; [exact L'|].
    assert (Vd : 0 <= znth b' d' < NB) by (destruct M' as [(_ & _ & V & _)|(_ & _ & _ & V)]; unfold NB in *; lia).
    split. { intros i. destruct (Z.eq_dec i d') as [->|]; [exact Vd| apply O'; lia]. }
    destruct M' as [(-> & R1 & V1 & PL & EQ)|(-> & A1 & -> & V1)].
    + split; [lia|]. split; [left; reflexivity|]. split; [lia|].
      split. { destruct (Z.eq_dec d' d) as [->|]. - rewrite (EQ eq_refl). lia. - rewrite PL by lia. pose proof (Hoth d' ltac:(lia)). lia. }
      split; [exact B'|]. split; [exact U'|]. split; [exact Z'|]. split; [exact T'| exact EQ].
    + split; [lia|]. split; [right; repeat split; lia|]. split; [lia|]. split; [lia|].
      split; [exact B'|]. split; [intros; lia|]. split; [exact Z'|]. split; [exact T'| intros; lia].
Qed.

Local Notation "'let?' x ':=' e 'in' k" :=
  (match e with Some x => k | None => None end)
  (at level 200, x pattern, e at level 100, k at level 200, only parsing).

Definition g_e (big : list Z) (a r z : Z) : option Z :=
  if a <? z
  then (let? (i, e) := fmt_fp_cnt TEN_FUEL (znth big a) (10, 9 * (r - a)) in Some e)
  else Some 0.
Definition g_j (t p e : Z) : Z :=
  p - (if negb (Z.lor t 32 =? CHR_f) then 1 else 0) * e
    - (if (Z.lor t 32 =? CHR_g) && negb (p =? 0) then 1 else 0).

Definition g_R (t p prefix pl : Z) (big : list Z) (a r z e j : Z) : option (list Z * Z * Z * Z) :=
    if j <? 9 * (z - r - 1) then
      let d := r + 1 + (Z.quot (j + 9 * LDBL_MAX_EXP) 9 - LDBL_MAX_EXP) in
      let j := j + 9 * LDBL_MAX_EXP in
      let j := Z.rem j 9 in
      let? (i, j) := fmt_fp_powi TEN_FUEL (10, j + 1) in
      let x := (znth big d) mod i in
      let? (big, a, d, e) :=
        if negb (x =? 0) || negb (d + 1 =? z) then
          let round := f128_div (f128_of_i32 2) K_LDBL_EPSILON in
          let round :=
            if negb (Z.land (znth big d / i) 1 =? 0)
               || ((i =? 1000000000) && (a <? d) && negb (Z.land (znth big (d - 1)) 1 =? 0))
            then f128_add round (f128_of_i32 2)
            else round in
          let small :=
            if x <? Z.quot i 2 then f128_of_d D_0_5
            else if (x =? Z.quot i 2) && (d + 1 =? z) then f128_of_d D_1_0
            else f128_of_d D_1_5 in
          let '(round, small) :=
            if negb (pl =? 0) && (znth PREFIX_STR prefix =? CHR_minus) then
              let m1 := f128_of_i32 (-1) in
              let round := f128_mul round m1 in
              let small := f128_mul small m1 in
              (round, small)
            else (round, small) in
          let big := zupd big d (znth big d - x) in
          if negb (f128_le (f128_add round small) round =? 0) then
            let big := zupd big d (u32 (znth big d + i)) in
            let? (big, d, a) := fmt_fp_carry BIG_FUEL (big, d, a) in
            let? (i, e) := fmt_fp_cnt TEN_FUEL (znth big a) (10, 9 * (r - a)) in
            Some (big, a, d, e)
          else Some (big, a, d, e)
        else Some (big, a, d, e) in
      let z := if d + 1 <? z then d + 1 else z in
      Some (big, a, z, e)
    else Some (big, a, z, e).

Definition TS (r0 : Z) (big : list Z) (a z e : Z) : Prop :=
  W9 big /\ zlength big = 128 /\ 0 <= a < z /\ z <= 127 /\ zeros_below big a /\
  (r0 = 0 \/ (r0 = 122 /\ 85 <= a <= 122)) /\
  exists k, 1 <= k <= 9 /\ 10^(k-1) <= znth big a < 10^k /\ e = 9 * (r0 - a) + k - 1.

Lemma TS_e_bound : forall r0 big a z e, TS r0 big a z e -> -1143 <= e <= 341.
Proof. intros r0 big a z e (_ & _ & AZ & Z7 & _ & R & [k (Hk & _ & ->)]). lia. Qed.

Lemma g_e_spec : forall r0 big a z, POST r0 big a z -> exists e, g_e big a r0 z = Some e /\ TS r0 big a z e.
Proof.
  intros r0 big a z (WB & LB & AZ & Z7 & NZ & ZB & R).
  unfold g_e. replace (a <? z) with true by (symmetry; apply Z.ltb_lt; lia).
  pose proof (WB a) as Wa.
  destruct (cnt_spec (znth big a) (9 * (r0 - a)) Wa) as [k (E & Hk & Hhi & Hlo)]. rewrite E.
  eexists. split; [reflexivity|]. unfold TS.
  split; [exact WB|]. split; [exact LB|]. split; [exact AZ|]. split; [exact Z7|]. split; [exact ZB|].
  split; [destruct R as [[-> _]|(-> & ? & _)]; [left; reflexivity| right; lia]|].
  exists k. split; [exact Hk|]. split; [| lia]. split; [apply Hlo; exact NZ| exact Hhi].
Qed.

Lemma pow10_le_NB : forall k, 0 <= k <= 9 -> 1 <= 10^k <= NB.
Proof.
  intros k Hk. unfold NB. change 1000000000 with (10^9). split; [pose proof (pow10_pos k); lia| apply Z.pow_le_mono_r; lia].
Qed.

Lemma NB_multiple : forall k, 0 <= k <= 9 -> NB = 10^k * 10^(9 - k).
Proof. intros. unfold NB. change 1000000000 with (10^9). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma R_spec : forall p1 prefix pl r0 big a z e,
  TS r0 big a z e -> znth big a <> 0 -> (r0 = 0 -> znth big 0 < 2^29) -> (r0 = 122 -> 86 <= a) -> 9 <= p1 <= 26 ->
  exists bigR aR zR eR, g_R CHR_g p1 prefix pl big a r0 z e (g_j CHR_g p1 e) = Some (bigR, aR, zR, eR) /\
    TS r0 bigR aR zR eR /\ znth bigR aR <> 0 /\ (aR = a \/ aR = a - 1) /\ zR <= z.
Proof.
  intros p1 prefix pl r0 big a z e HT NZ B0 A86 Hp.
  pose proof HT as (WB & LB & AZ & Z7 & ZB & R & [k (Hk & Hka & He)]).
  unfold g_j. change (Z.lor CHR_g 32 =? CHR_f) with false. change (Z.lor CHR_g 32 =? CHR_g) with true.
  replace (p1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb].
  set (j := p1 - 1 * e - 1).
  unfold g_R.
  destruct (Z.ltb_spec j (9 * (z - r0 - 1))) as [JL|JG].
  2:{ eexists _, _, _, _. split; [reflexivity|]. split; [exact HT|]. split; [exact NZ|]. split; [left; reflexivity| lia]. }
  change LDBL_MAX_EXP with 16384.
  assert (Hj : -1200 <= j <= 1200) by (subst j; lia).
  rewrite Z.quot_div_nonneg by lia. rewrite Z.rem_mod_nonneg by lia.
  set (q := (j + 9 * 16384) / 9 - 16384). set (j2 := (j + 9 * 16384) mod 9).
  assert (Hq : j = 9 * q + j2 /\ 0 <= j2 <= 8) by (subst q j2; dlia).
  assert (Hd : a + 1 <= r0 + 1 + q < z).
  { subst j. destruct Hq as [Hq _]. split; [| nia].   nia. }
  set (d := r0 + 1 + q) in *.
  rewrite (powi_spec j2) by lia.
  set (i := 10 ^ (9 - j2)).
  assert (Hi : 10 <= i <= NB /\ NB = i * 10^j2).
  { subst i. pose proof (pow10_le_NB (9 - j2) ltac:(lia)). pose proof (pow10_le_NB j2 ltac:(lia)).
    split; [| rewrite (NB_multiple (9 - j2)) by lia; f_equal; f_equal; lia].
    split; [| lia]. change 10 with (10^1). apply Z.pow_le_mono_r; lia. }
  clearbody i. destruct Hi as [Hi NBi].
  pose proof (WB d) as Wd.
  pose proof (Z.mod_pos_bound (znth big d) i ltac:(lia)) as Xr.
  pose proof (Z.div_mod (znth big d) i ltac:(lia)) as Xd.
  set (x := znth big d mod i) in *.
  destruct (negb (x =? 0) || negb (d + 1 =? z)) eqn:CX.
  2:{
      eexists _, _, _, _. split; [reflexivity|].
      replace (if d + 1 <? z then d + 1 else z) with z by (destruct (Z.ltb_spec (d + 1) z); lia).
      split; [exact HT|]. split; [exact NZ|]. split; [left; reflexivity| lia]. }
  cbv zeta.

  assert (DOWN : exists bigR aR zR eR,
    match Some (zupd big d (znth big d - x), a, d, e) with
    | Some (big0, a0, d0, e0) => Some (big0, a0, if d0 + 1 <? z then d0 + 1 else z, e0)
    | None => None end = Some (bigR, aR, zR, eR) /\
    TS r0 bigR aR zR eR /\ znth bigR aR <> 0 /\ (aR = a \/ aR = a - 1) /\ zR <= z).
  { eexists _, _, _, _. split; [reflexivity|].
    assert (ZR : a + 1 < (if d + 1 <? z then d + 1 else z) <= z) by (destruct (Z.ltb_spec (d + 1) z); lia).
    split; [| split; [rewrite znth_zupd_neq by lia; exact NZ| split; [left; reflexivity| lia]]].
    unfold TS. split; [apply W9_zupd; [exact WB| lia]|]. split; [rewrite zlength_zupd; exact LB|].
    split; [lia|]. split; [lia|]. split; [intros kk Hkk; rewrite znth_zupd_neq by lia; apply ZB; lia|].
    split; [exact R|]. exists k. rewrite znth_zupd_neq by lia. split; [exact Hk|]. split; [exact Hka| exact He]. }
  assert (UP : exists bigR aR zR eR,
    match (match fmt_fp_carry BIG_FUEL
             (zupd (zupd big d (znth big d - x)) d (u32 (znth (zupd big d (znth big d - x)) d + i)), d, a) with
           | Some (big0, d0, a0) =>
             match fmt_fp_cnt TEN_FUEL (znth big0 a0) (10, 9 * (r0 - a0)) with
             | Some (_, e0) => Some (big0, a0, d0, e0)
             | None => None
             end
           | None => None end) with
    | Some (big0, a0, d0, e0) => Some (big0, a0, if d0 + 1 <? z then d0 + 1 else z, e0)
    | None => None end = Some (bigR, aR, zR, eR) /\
    TS r0 bigR aR zR eR /\ znth bigR aR <> 0 /\ (aR = a \/ aR = a - 1) /\ zR <= z).
  { rewrite znth_zupd_eq by lia.
    assert (XI : 0 <= znth big d - x /\ znth big d - x + i <= NB).
    { split; [lia|]. assert (znth big d / i < 10 ^ j2) by nia. nia. }
    rewrite (u32_id (znth big d - x + i)) by (unfold NB in *; lia).
    set (big2 := zupd (zupd big d (znth big d - x)) d (znth big d - x + i)).
    assert (L2 : zlength big2 = 128) by (subst big2; rewrite !zlength_zupd; exact LB).
    destruct (carry_spec big2 d a L2 ltac:(lia) ltac:(lia)) as [bigC [dC [aC (EC & LC & WC & AC0 & ACa & DC & VdC & BC & UC & ZC & TC & EQC)]]].
    { intros ii Hii. subst big2. rewrite !znth_zupd_neq by lia. apply WB. }
    { subst big2. rewrite znth_zupd_eq by (rewrite zlength_zupd; lia). lia. }
    { intros A0. split; [lia|]. subst big2. rewrite !znth_zupd_neq by lia. destruct R as [R0|[_ ?]]; [| lia]. specialize (B0 R0). unfold NB. lia. }
    rewrite EC.
    assert (NZC : znth bigC aC <> 0).
    { destruct ACa as [->|(-> & -> & V1)]; [| rewrite V1; lia].
      destruct (Z.eq_dec dC a) as [->|]; [lia|]. rewrite UC by lia. subst big2. rewrite !znth_zupd_neq by lia. exact NZ. }
    pose proof (WC aC) as WaC.
    destruct (cnt_spec (znth bigC aC) (9 * (r0 - aC)) WaC) as [kC (ECn & HkC & HhiC & HloC)]. rewrite ECn.
    eexists _, _, _, _. split; [reflexivity|].
    assert (ZR : aC < (if dC + 1 <? z then dC + 1 else z) <= z) by (destruct (Z.ltb_spec (dC + 1) z); lia).
    split; [| split; [exact NZC| split; [destruct ACa as [->|(-> & _)]; [left|right]; reflexivity| lia]]].
    unfold TS. split; [exact WC|]. split; [exact LC|]. split; [lia|]. split; [lia|].
    split. { intros kk Hkk. rewrite BC by lia. subst big2. rewrite !znth_zupd_neq by lia. apply ZB. destruct ACa as [->|(-> & _)]; lia. }
    split. { destruct R as [R0|(R1 & R2)]; [left; exact R0| right]. split; [exact R1|]. specialize (A86 R1). destruct ACa as [->|(-> & _)]; lia. }
    exists kC. split; [exact HkC|]. split; [| lia]. split; [apply HloC; exact NZC| exact HhiC]. }
  destruct (negb (pl =? 0) && (znth PREFIX_STR prefix =? CHR_minus)); cbv beta iota;
  match goal with |- context [negb (f128_le ?A ?B =? 0)] => destruct (negb (f128_le A B =? 0)) end;
  first [exact DOWN | exact UP].
Qed.

Lemma zrepeat_nil : forall c n, n <= 0 -> zrepeat c n = [].
Proof. intros. Local Transparent zrepeat. unfold zrepeat. replace (Z.to_nat n) with 0%nat by lia. reflexivity. Qed.
Local Opaque zrepeat.

Lemma pad_exact : forall o c w l, w - l < 256 ->
  pad o c w l 0 = Some (o ++ zrepeat c (w - l)).
Proof.
  intros o c w l Hw. unfold pad. change (negb (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0)) with false. cbn [orb].
  destruct (Z.leb_spec w l).
  - rewrite zrepeat_nil by lia. rewrite app_nil_r. reflexivity.
  - rewrite pad_loop_eq. unfold PAD_FUEL. cbn [wloop]. cbn [fst].
    replace (256 <=? w - l) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

Lemma zlength_zrepeat' : forall c n, zlength (zrepeat c n) = Z.max 0 n.
Proof. intros. Local Transparent zrepeat. unfold zlength, zrepeat. rewrite repeat_length. lia. Qed.

Lemma Forall_zrepeat : forall (P : Z -> Prop) c n, P c -> Forall P (zrepeat c n).
Proof. intros P c n Hc. Local Transparent zrepeat. unfold zrepeat. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. exact Hc. Qed.
Local Opaque zrepeat.

Lemma isdig_0 : isdig CHR_0. Proof. unfold isdig, CHR_0. lia. Qed.

Lemma W9_DIGk : forall big i, W9 big -> exists k, DIGk (znth big i) k /\ 0 <= k <= 9.
Proof.
  intros big i WB. pose proof (WB i). apply (DIGk_exists (znth big i) 9); [| lia]. unfold NB in H. change (10^9) with 1000000000. lia.
Qed.

Lemma fint_body_spec : forall big a0 d o k, W9 big -> DIGk (znth big d) k -> 0 <= k <= 9 ->
  exists txt, fmt_fp_fint_body big a0 (d, o) = Some (d + 1, o ++ txt) /\ Forall isdig txt /\
    zlength txt = (if d =? a0 then Z.max k 1 else 9).
Proof.
  intros big a0 d o k WB D Hk. pose proof (WB d) as Hv. unfold fmt_fp_fint_body.
  destruct (fmt_u_spec (znth big d) (zrepeat 0 37) 9 k ltac:(lia) D ltac:(lia)) as [b1 (E1 & L1 & D1 & U1)].
  { rewrite zlength_zrepeat; lia. }
  rewrite E1. rewrite zlength_zrepeat in L1 by lia.
  destruct (Z.eqb_spec d a0) as [->|NE].
  - cbn [negb]. destruct (Z.eqb_spec (9 - k) 9) as [K0|K0].
    + assert (k = 0) by lia. subst k. eexists. split; [reflexivity|]. unfold out. split.
      * apply zsub_Forall; try (rewrite ?zlength_zupd; lia). intros i Hi. replace i with 8 by lia. rewrite znth_zupd_eq by lia. apply isdig_0.
      * rewrite zlength_zsub by (rewrite ?zlength_zupd; lia). reflexivity.
    + eexists. split; [reflexivity|]. unfold out. split.
      * apply zsub_Forall; try lia. intros i Hi. apply D1. lia.
      * rewrite zlength_zsub by lia. lia.
  - cbn [negb]. destruct (zfill_spec (9 - k) b1 ltac:(lia) ltac:(lia)) as [b2 (E2 & L2 & F1 & F2)]. rewrite E2.
    eexists. split; [reflexivity|]. unfold out. split.
    + apply zsub_Forall; try lia. intros i Hi. destruct (Z.lt_ge_cases i (9 - k)).
      * rewrite F1 by lia. apply isdig_0.
      * rewrite F2 by lia. apply D1. lia.
    + rewrite zlength_zsub by lia. reflexivity.
Qed.

Lemma fint_spec : forall big a0 r o k, W9 big -> 0 <= a0 <= r -> r - a0 <= 128 -> DIGk (znth big a0) k -> 0 <= k <= 9 ->
  exists txt, fmt_fp_fint BIG_FUEL big a0 r (a0, o) = Some (r + 1, o ++ txt) /\ Forall isdig txt /\
    zlength txt = Z.max k 1 + 9 * (r - a0).
Proof.
  intros big a0 r o k WB Har Hw D Hk. rewrite fmt_fp_fint_eq.
  destruct (owloop_total (fun st : Z * list Z => fst st <=? r) (fmt_fp_fint_body big a0)
    (fun st => a0 <= fst st <= r + 1 /\ exists acc, snd st = o ++ acc /\ Forall isdig acc /\
               zlength acc = (if fst st =? a0 then 0 else Z.max k 1 + 9 * (fst st - a0 - 1)))
    (fun st => r + 1 - fst st)) with (fuel := BIG_FUEL) (s := (a0, o)) as [[d' o'] (E & (R' & [acc (Eo & Facc & Lacc)]) & C)].
  - intros [d o1] (R1 & [acc (Eo1 & F1 & L1)]) C1. cbn [fst snd] in *. subst o1. apply Z.leb_le in C1.
    destruct (W9_DIGk big d WB) as [kd [Dd Hkd]].
    assert (KD : d = a0 -> kd = k).
    { intros ->. destruct D as [[A1 A2]|[A1 A2]]; destruct Dd as [[B1 B2]|[B1 B2]]; try lia.
      destruct (Z.lt_trichotomy kd k) as [LT|[EQ|GT]]; [| exact EQ |].
      - exfalso. assert (10 ^ kd <= 10 ^ (k - 1)) by (apply Z.pow_le_mono_r; lia). lia.
      - exfalso. assert (10 ^ k <= 10 ^ (kd - 1)) by (apply Z.pow_le_mono_r; lia). lia. }
    destruct (fint_body_spec big a0 d (o ++ acc) kd WB Dd Hkd) as [txt (Eb & Ft & Lt)].
    rewrite Eb. eexists. split; [reflexivity|]. cbn [fst snd]. split; [| lia]. split; [lia|].
    exists (acc ++ txt). split; [now rewrite app_assoc|]. split; [apply Forall_app; split; assumption|].
    rewrite zlength_app, L1, Lt. destruct (Z.eqb_spec d a0) as [->|NE].
    + rewrite (KD eq_refl). replace (a0 + 1 =? a0) with false by (symmetry; apply Z.eqb_neq; lia). lia.
    + replace (d + 1 =? a0) with false by (symmetry; apply Z.eqb_neq; lia). lia.
  - cbn [fst snd]. split; [lia|]. exists []. rewrite app_nil_r, Z.eqb_refl. repeat split; auto.
  - cbn [fst]. unfold BIG_FUEL. change (Z.of_nat 130) with 130. lia.
  - rewrite E. cbn [fst snd] in *. subst o'. apply Z.leb_gt in C. assert (d' = r + 1) by lia. subst d'.
    exists acc. split; [reflexivity|]. split; [exact Facc|]. rewrite Lacc.
    replace (r + 1 =? a0) with false by (symmetry; apply Z.eqb_neq; lia). lia.
Qed.

Lemma ffrac_spec : forall big z d p o, W9 big -> z - d <= 129 -> 0 <= p ->
  exists d' p' acc, fmt_fp_ffrac BIG_FUEL big z (d, p, o) = Some (d', p', o ++ acc) /\ Forall isdig acc /\
    zlength acc = p - Z.max p' 0 /\ p' <= p.
Proof.
  intros big z d p o WB Hw Hp. rewrite fmt_fp_ffrac_eq.
  destruct (owloop_total (fun st : Z * Z * list Z => let '(d0, p0, _) := st in (d0 <? z) && (0 <? p0)) (fmt_fp_ffrac_body big)
    (fun st => let '(d1, p1, o1) := st in z - d1 <= 129 /\ p1 <= p /\ exists acc, o1 = o ++ acc /\ Forall isdig acc /\ zlength acc = p - Z.max p1 0)
    (fun st => let '(d1, _, _) := st in Z.max 0 (z - d1))) with (fuel := BIG_FUEL) (s := (d, p, o)) as [[[d' p'] o'] (E & (R1 & R2 & [acc (-> & Facc & Lacc)]) & C)].
  - intros [[d1 p1] o1] (Q1 & Q2 & [acc (-> & F1 & L1)]) C1. apply andb_prop in C1. destruct C1 as [C1 C2]. apply Z.ltb_lt in C1. apply Z.ltb_lt in C2.
    unfold fmt_fp_ffrac_body.
    destruct (W9_DIGk big d1 WB) as [kd [Dd Hkd]]. pose proof (WB d1) as Wd.
    destruct (fmt_u_spec (znth big d1) (zrepeat 0 37) 9 kd ltac:(lia) Dd ltac:(lia)) as [b1 (E1 & L1' & D1 & U1)].
    { rewrite zlength_zrepeat; lia. }
    rewrite E1. rewrite zlength_zrepeat in L1' by lia.
    destruct (zfill_spec (9 - kd) b1 ltac:(lia) ltac:(lia)) as [b2 (E2 & L2 & G1 & G2)]. rewrite E2.
    eexists. split; [reflexivity|]. split; [| lia]. split; [lia|]. split; [lia|].
    exists (acc ++ zsub b2 0 (Z.min 9 p1)). unfold out. split; [now rewrite app_assoc|]. split.
    + apply Forall_app. split; [exact F1|]. apply zsub_Forall; try lia. intros i Hi.
      destruct (Z.lt_ge_cases i (9 - kd)); [rewrite G1 by lia; apply isdig_0| rewrite G2 by lia; apply D1; lia].
    + rewrite zlength_app, L1, zlength_zsub by lia. lia.
  - split; [lia|]. split; [lia|]. exists []. rewrite app_nil_r. repeat split; auto. unfold zlength. cbn [length]. lia.
  - unfold BIG_FUEL. change (Z.of_nat 130) with 130. lia.
  - rewrite E. exists d', p', acc. split; [reflexivity|]. split; [exact Facc|]. split; [exact Lacc| exact R2].
Qed.

Definition isdigdot (c : Z) : Prop := isdig c \/ c = CHR_dot.

Lemma emit_f_spec : forall o big a r0 z p k, W9 big -> 0 <= r0 -> r0 - 128 < a -> a < z -> z <= 128 -> 0 <= a -> 0 <= p <= 40 ->
  (r0 < a -> znth big r0 = 0) -> DIGk (znth big a) k -> 1 <= k <= 9 ->
  exists txt, fmt_fp_emit_f o big a r0 z p 0 = Some (o ++ txt) /\ Forall isdigdot txt /\
    zlength txt = (if a <=? r0 then k + 9 * (r0 - a) else 1) + (if p =? 0 then 0 else 1) + p.
Proof.
  intros o big a r0 z p k WB Hr0 Har Haz Hz Ha Hp Hbelow D Hk. unfold fmt_fp_emit_f.
  set (a0 := if r0 <? a then r0 else a).
  assert (A0 : (a <= r0 /\ a0 = a) \/ (r0 < a /\ a0 = r0)) by (subst a0; destruct (Z.ltb_spec r0 a); lia).
  assert (K0 : exists k0, DIGk (znth big a0) k0 /\ 0 <= k0 <= 9 /\ Z.max k0 1 = (if a <=? r0 then k else 1)).
  { destruct A0 as [[H1 ->]|[H1 ->]].
    - exists k. split; [exact D|]. replace (a <=? r0) with true by (symmetry; apply Z.leb_le; lia). lia.
    - exists 0. rewrite (Hbelow H1). split; [left; lia|]. replace (a <=? r0) with false by (symmetry; apply Z.leb_gt; lia). lia. }
  destruct K0 as [k0 (D0 & Hk0 & MK)]. clearbody a0.
  destruct (fint_spec big a0 r0 o k0 WB ltac:(lia) ltac:(lia) D0 Hk0) as [t1 (E1 & F1 & L1)]. rewrite E1.
  change (Z.land 0 ALT_FORM =? 0) with true. cbn [negb orb].
  set (o2 := if negb (p =? 0) || false then out (o ++ t1) [CHR_dot] else o ++ t1).
  assert (O2 : exists t2, o2 = o ++ t2 /\ Forall isdigdot t2 /\ zlength t2 = zlength t1 + (if p =? 0 then 0 else 1)).
  { subst o2. destruct (Z.eqb_spec p 0); cbn [negb orb].
    - exists t1. split; [reflexivity|]. split; [| lia]. eapply Forall_impl; [| exact F1]. intros c Hc; left; exact Hc.
    - exists (t1 ++ [CHR_dot]). unfold out. rewrite app_assoc. split; [reflexivity|]. split.
      + apply Forall_app. split; [eapply Forall_impl; [| exact F1]; intros c Hc; left; exact Hc|]. constructor; [right; reflexivity| constructor].
      + rewrite zlength_app. unfold zlength. cbn [length]. lia. }
  destruct O2 as [t2 (-> & F2 & L2)].
  destruct (ffrac_spec big z (r0 + 1) p (o ++ t2) WB ltac:(lia) ltac:(lia)) as [d' [p' [t3 (E3 & F3 & L3 & P3)]]].
  rewrite E3. rewrite pad_exact by lia.
  exists (t2 ++ t3 ++ zrepeat CHR_0 (p' + 9 - 9)). unfold out. split; [rewrite <- !app_assoc; reflexivity|]. split.
  - apply Forall_app. split; [exact F2|]. apply Forall_app. split; [eapply Forall_impl; [| exact F3]; intros c Hc; left; exact Hc|].
    apply Forall_zrepeat. left. apply isdig_0.
  - rewrite !zlength_app, zlength_zrepeat', L2, L1, L3, MK. destruct A0 as [[H1 ->]|[H1 ->]].
    + replace (a <=? r0) with true by (symmetry; apply Z.leb_le; lia). lia.
    + replace (a <=? r0) with false by (symmetry; apply Z.leb_gt; lia). lia.
Qed.

Lemma owloop_S : forall {A} (c : A -> bool) (b : A -> option A) n s,
  owloop c b (S n) s = (if c s then match b s with Some s' => owloop c b n s' | None => None end else Some s).
Proof. reflexivity. Qed.

Lemma eloop_rest_spec : forall fuel big a z d p o, W9 big -> a < d -> (1 <= fuel)%nat -> z - d < Z.of_nat fuel ->
  exists d' p' acc, fmt_fp_eloop fuel big a z 0 (d, p, o) = Some (d', p', o ++ acc) /\ Forall isdig acc /\
    zlength acc = Z.max p 0 - Z.max p' 0 /\ p' <= p.
Proof.
  intros fuel big a z d p o WB Had Hf1 Hf. rewrite fmt_fp_eloop_eq.
  destruct (owloop_total (fun st : Z * Z * list Z => let '(d0, p0, _) := st in (d0 <? z) && (0 <=? p0)) (fmt_fp_eloop_body big a 0)
    (fun st => let '(d1, p1, o1) := st in a < d1 /\ p1 <= p /\ exists acc, o1 = o ++ acc /\ Forall isdig acc /\ zlength acc = Z.max p 0 - Z.max p1 0)
    (fun st => let '(d1, p1, _) := st in if (d1 <? z) && (0 <=? p1) then z - d1 else 0)) with (fuel := fuel) (s := (d, p, o))
    as [[[d' p'] o'] (E & (R1 & R2 & [acc (-> & Facc & Lacc)]) & C)].
  - intros [[d1 p1] o1] (Q1 & Q2 & [acc (-> & F1 & L1)]) C1. rewrite C1.
    apply andb_prop in C1. destruct C1 as [C1 C2]. apply Z.ltb_lt in C1. apply Z.leb_le in C2.
    unfold fmt_fp_eloop_body.
    destruct (W9_DIGk big d1 WB) as [kd [Dd Hkd]]. pose proof (WB d1) as Wd.
    destruct (fmt_u_spec (znth big d1) (zrepeat 0 37) 9 kd ltac:(lia) Dd ltac:(lia)) as [b1 (E1 & L1' & D1 & U1)].
    { rewrite zlength_zrepeat; lia. }
    rewrite E1. rewrite zlength_zrepeat in L1' by lia.
    replace (negb (d1 =? a)) with true by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; lia).
    set (sb := if 9 - kd =? 9 then (9 - kd - 1, zupd b1 (9 - kd - 1) CHR_0) else (9 - kd, b1)).
    assert (SB : exists s2 b2, sb = (s2, b2) /\ 0 <= s2 <= 8 /\ zlength b2 = 37 /\ forall i, s2 <= i < 9 -> isdig (znth b2 i)).
    { subst sb. destruct (Z.eqb_spec (9 - kd) 9).
      - eexists _, _. split; [reflexivity|]. split; [lia|]. split; [rewrite zlength_zupd; lia|].
        intros i Hi. replace i with 8 by lia. replace (9 - kd - 1) with 8 by lia. rewrite znth_zupd_eq by lia. apply isdig_0.
      - eexists _, _. split; [reflexivity|]. split; [lia|]. split; [lia|]. intros i Hi. apply D1. lia. }
    destruct SB as [s2 [b2 (-> & S2 & L2 & D2)]].
    destruct (zfill_spec s2 b2 ltac:(lia) ltac:(lia)) as [b3 (E3 & L3 & G1 & G2)]. rewrite E3.
    eexists. split; [reflexivity|]. split.
    + split; [lia|]. split; [lia|]. exists (acc ++ zsub b3 0 (Z.min (9 - 0) (p1))). unfold out. split; [now rewrite app_assoc|]. split.
      * apply Forall_app. split; [exact F1|]. apply zsub_Forall; try lia. intros i Hi.
        destruct (Z.lt_ge_cases i s2); [rewrite G1 by lia; apply isdig_0| rewrite G2 by lia; apply D2; lia].
      * rewrite zlength_app, L1, zlength_zsub by lia. lia.
    + destruct ((d1 + 1 <? z) && (0 <=? p1 - (9 - 0))) eqn:CC; [|lia].
      apply andb_prop in CC. destruct CC as [CC1 CC2]. apply Z.ltb_lt in CC1. lia.
  - split; [lia|]. split; [lia|]. exists []. rewrite app_nil_r. repeat split; auto. unfold zlength. cbn [length]. lia.
  - destruct ((d <? z) && (0 <=? p)) eqn:CC; [|lia]. apply andb_prop in CC. destruct CC as [CC1 CC2]. apply Z.ltb_lt in CC1. lia.
  - rewrite E. exists d', p', acc. split; [reflexivity|]. split; [exact Facc|]. split; [exact Lacc| exact R2].
Qed.

Lemma eloop_S : forall n big a z fl d p o,
  fmt_fp_eloop (S n) big a z fl (d, p, o) =
  (if (d <? z) && (0 <=? p) then match fmt_fp_eloop_body big a fl (d, p, o) with Some st => fmt_fp_eloop n big a z fl st | None => None end
   else Some (d, p, o)).
Proof. reflexivity. Qed.

Lemma emit_e_spec : forall o big a z p ebuf0 estr k, W9 big -> 0 <= a -> a < z -> z <= 128 -> 0 <= p <= 40 ->
  DIGk (znth big a) k -> 1 <= k <= 9 -> 0 <= estr <= 12 -> zlength ebuf0 = 12 ->
  exists txt, fmt_fp_emit_e o big a z p 0 ebuf0 estr = Some (o ++ txt ++ zsub ebuf0 estr (12 - estr)) /\ Forall isdigdot txt /\
    zlength txt = 1 + (if 0 <? p then 1 else 0) + p.
Proof.
  intros o big a z p ebuf0 estr k WB Ha Haz Hz Hp D Hk He HLe. unfold fmt_fp_emit_e.
  replace (z <=? a) with false by (symmetry; apply Z.leb_gt; lia).
  change BIG_FUEL with (S 129%nat). rewrite eloop_S.
  replace ((a <? z) && (0 <=? p)) with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Z.ltb_lt; lia| apply Z.leb_le; lia]. }
  unfold fmt_fp_eloop_body at 1.
  pose proof (WB a) as Wa.
  destruct (fmt_u_spec (znth big a) (zrepeat 0 37) 9 k ltac:(lia) D ltac:(lia)) as [b1 (E1 & L1 & D1 & U1)].
  { rewrite zlength_zrepeat; lia. }
  rewrite E1. rewrite zlength_zrepeat in L1 by lia.
  replace (9 - k =? 9) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite Z.eqb_refl. cbn [negb]. change (Z.land 0 ALT_FORM =? 0) with true. cbn [negb]. rewrite Bool.orb_false_r.
  set (o1 := out o (zsub b1 (9 - k) 1)).
  set (o2 := if 0 <? p then out o1 [CHR_dot] else o1).
  set (o3 := out o2 (zsub b1 (9 - k + 1) (Z.min (9 - (9 - k + 1)) p))).
  assert (O3 : exists t3, o3 = o ++ t3 /\ Forall isdigdot t3 /\ zlength t3 = 1 + (if 0 <? p then 1 else 0) + Z.min (k - 1) p).
  { subst o3 o2 o1. unfold out.
    assert (F0 : Forall isdigdot (zsub b1 (9 - k) 1)).
    { apply zsub_Forall; try lia. intros i Hi. left. apply D1. lia. }
    assert (F2 : Forall isdigdot (zsub b1 (9 - k + 1) (Z.min (9 - (9 - k + 1)) p))).
    { apply zsub_Forall; try lia. intros i Hi. left. apply D1. lia. }
    destruct (Z.ltb_spec 0 p).
    - eexists. rewrite <- !app_assoc. split; [reflexivity|]. split.
      + apply Forall_app. split; [exact F0|]. apply Forall_app. split; [constructor; [right; reflexivity| constructor]| exact F2].
      + rewrite !zlength_app, !zlength_zsub by lia. unfold zlength. cbn [length]. lia.
    - eexists. rewrite <- !app_assoc. split; [reflexivity|]. split.
      + apply Forall_app. split; [exact F0| exact F2].
      + rewrite !zlength_app, !zlength_zsub by lia. lia. }
  destruct O3 as [t3 (EO3 & F3 & L3)]. rewrite EO3.
  destruct (eloop_rest_spec 129%nat big a z (a + 1) (p - (9 - (9 - k + 1))) (o ++ t3) WB ltac:(lia) ltac:(lia) ltac:(lia)) as [d' [p' [t4 (E4 & F4 & L4 & P4)]]].
  rewrite E4. rewrite pad_exact by lia.
  exists (t3 ++ t4 ++ zrepeat CHR_0 (p' + 18 - 18)). unfold out. split; [rewrite <- !app_assoc; reflexivity|]. split.
  - apply Forall_app. split; [exact F3|]. apply Forall_app. split; [eapply Forall_impl; [| exact F4]; intros c Hc; left; exact Hc|].
    apply Forall_zrepeat. left. apply isdig_0.
  - rewrite !zlength_app, zlength_zrepeat', L3, L4. lia.
Qed.

Definition g_H (o : list Z) (w fl t p prefix pl : Z) (big : list Z) (a r z e : Z) : option (list Z * Z) :=
  let? z := fmt_fp_strip BIG_FUEL big a z in
  let? (p, t) :=
    if Z.lor t 32 =? CHR_g then
      let p := if p =? 0 then p + 1 else p in
      let '(t, p) := if (e <? p) && (-4 <=? e) then (t - 1, p - (e + 1)) else (t - 2, p - 1) in
      if Z.land fl ALT_FORM =? 0 then
        let? j := if (a <? z) && negb (znth big (z - 1) =? 0)
                  then (let? (i, j) := fmt_fp_tz TEN_FUEL (znth big (z - 1)) (10, 0) in Some j)
                  else Some 9 in
        let p := if Z.lor t 32 =? CHR_f
                 then Z.min p (Z.max 0 (9 * (z - r - 1) - j))
                 else Z.min p (Z.max 0 (9 * (z - r - 1) + e - j)) in
        Some (p, t)
      else Some (p, t)
    else Some (p, t) in
  let palt := if negb (p =? 0) || negb (Z.land fl ALT_FORM =? 0) then 1 else 0 in
  if INT_MAX - 1 - palt <? p then Some (o, -1) else
  let l := 1 + p + palt in
  let? len := fmt_fp_len t l e in
  match len with
  | Ret v => Some (o, v)
  | Cont (l, ebuf0, estr) =>
  if INT_MAX - pl <? l then Some (o, -1) else
  let? o := pad o CHR_sp w (pl + l) fl in
  let o := out o (zsub PREFIX_STR prefix pl) in
  let? o := pad o CHR_0 w (pl + l) (Z.lxor fl ZERO_PAD) in
  let? o := if Z.lor t 32 =? CHR_f
            then fmt_fp_emit_f o big a r z p fl
            else fmt_fp_emit_e o big a z p fl ebuf0 estr in
  let? o := pad o CHR_sp w (pl + l) (Z.lxor fl LEFT_ADJ) in
  Some (o, Z.max w (pl + l))
  end.

Lemma pad_flag : forall o c w l fl, Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) <> 0 -> pad o c w l fl = Some o.
Proof.
  intros o c w l fl H. unfold pad. replace (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) with false by (symmetry; apply Z.eqb_neq; exact H).
  reflexivity.
Qed.

Lemma gch_0 : gch CHR_0. Proof. left. unfold CHR_0. lia. Qed.
Lemma gch_isdigdot : forall c, isdigdot c -> gch c.
Proof. intros c [H| ->]; [left; exact H| unfold gch, CHR_dot; lia]. Qed.

Lemma len_f_spec : forall l e, 0 <= l <= 100 -> -2000 <= e <= 2000 ->
  fmt_fp_len 102 l e = Some (Cont ((if 0 <? e then l + e else l), zrepeat 0 12, 12)).
Proof.
  intros l e Hl He. unfold fmt_fp_len. change (Z.lor 102 32 =? CHR_f) with true. cbv iota.
  replace (INT_MAX - l <? e) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia). reflexivity.
Qed.

Lemma len_e_spec : forall l e, 0 <= l <= 100 -> -9999 <= e <= 9999 ->
  exists estr eb, fmt_fp_len 101 l e = Some (Cont (l + (12 - estr), eb, estr)) /\ 4 <= 12 - estr <= 6 /\ zlength eb = 12 /\
    forall i, estr <= i < 12 -> gch (znth eb i).
Proof.
  intros l e Hl He. unfold fmt_fp_len. change (Z.lor 101 32 =? CHR_f) with false. cbv iota.
  set (ea := if e <? 0 then - e else e).
  assert (Hea : 0 <= ea < 10^4) by (subst ea; destruct (Z.ltb_spec e 0); lia).
  destruct (DIGk_exists ea 4 Hea ltac:(lia)) as [ke [Dk Hke]].
  destruct (fmt_u_spec ea (zrepeat 0 12) 12 ke ltac:(lia) Dk ltac:(lia)) as [eb1 (E1 & L1 & D1 & U1)].
  { rewrite zlength_zrepeat; lia. }
  rewrite E1. rewrite zlength_zrepeat in L1 by lia.
  destruct (epad_spec (12 - ke) eb1 ltac:(lia) L1) as [eb2 (E2 & L2 & G1 & G2)]. rewrite E2.
  replace (INT_MAX - l <? 12 - (Z.min (12 - ke) 10 - 1 - 1)) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
  eexists _, _. split; [reflexivity|]. split; [lia|]. split; [rewrite !zlength_zupd; exact L2|].
  intros i Hi.
  destruct (Z.eq_dec i (Z.min (12 - ke) 10 - 1 - 1)) as [->|N1].
  { rewrite znth_zupd_eq by (rewrite zlength_zupd, L2; lia). unfold u8. change (101 mod 2^8) with 101. unfold gch. lia. }
  rewrite znth_zupd_neq by lia.
  destruct (Z.eq_dec i (Z.min (12 - ke) 10 - 1)) as [->|N2].
  { rewrite znth_zupd_eq by (rewrite L2; lia). unfold gch, CHR_minus, CHR_plus. destruct (e <? 0); lia. }
  rewrite znth_zupd_neq by lia.
  destruct (Z.lt_ge_cases i (12 - ke)).
  - rewrite G1 by lia. apply gch_0.
  - rewrite G2 by lia. apply gch_dig. apply D1. lia.
Qed.

Theorem H_spec : forall o p1 prefix pl r0 big a z e,
  TS r0 big a z e -> znth big a <> 0 -> 1 <= p1 <= 26 -> 0 <= pl -> 0 <= prefix -> prefix + pl <= 18 ->
  Forall gch (zsub PREFIX_STR prefix pl) ->
  exists txt l', g_H o 1 0 CHR_g p1 prefix pl big a r0 z e = Some (o ++ txt, pl + l') /\
    zlength txt = pl + l' /\ Forall gch txt /\ 1 <= l' <= p1 + 7.
Proof.
  intros o p1 prefix pl r0 big a z e HT NZ Hp Hpl Hpr Hpp Fpre.
  pose proof HT as (WB & LB & AZ & Z7 & ZB & R & [k (Hk & Hka & He)]).
  assert (Hr0 : 0 <= r0 <= 122) by (destruct R as [->|[-> _]]; lia).
  unfold g_H.
  destruct (strip_spec big a z ltac:(lia) ltac:(lia) NZ) as [z' (Es & Hz' & Zs & NZs)]. rewrite Es.
  change (Z.lor CHR_g 32 =? CHR_g) with true. cbv iota.
  replace (p1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change (Z.land 0 ALT_FORM =? 0) with true.
  replace ((a <? z') && negb (znth big (z' - 1) =? 0)) with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Z.ltb_lt; lia| apply Bool.negb_true_iff, Z.eqb_neq; exact NZs]. }
  pose proof (WB (z' - 1)) as Wz.
  destruct (fmt_fp_tz_total (znth big (z' - 1)) ltac:(unfold NB in Wz; lia)) as [it [jt Et]]. rewrite Et.
  assert (PL : zlength (zsub PREFIX_STR prefix pl) = pl) by (apply zlength_zsub; [lia|lia| unfold PREFIX_STR, zlength; cbn [length]; lia]).
  destruct ((e <? p1) && (-4 <=? e)) eqn:CF.
  -
    apply andb_prop in CF. destruct CF as [CF1 CF2]. apply Z.ltb_lt in CF1. apply Z.leb_le in CF2.
    change (Z.lor (CHR_g - 1) 32 =? CHR_f) with true. cbv iota.
    set (p2 := Z.min (p1 - (e + 1)) (Z.max 0 (9 * (z' - r0 - 1) - jt))).
    assert (Hp2 : 0 <= p2 <= p1 - (e + 1)) by (subst p2; lia). clearbody p2.
    cbn [negb orb]. rewrite Bool.orb_false_r.
    set (palt := if negb (p2 =? 0) then 1 else 0).
    assert (Hpalt : palt = (if p2 =? 0 then 0 else 1) /\ 0 <= palt <= 1) by (subst palt; destruct (p2 =? 0); cbn; lia).
    destruct Hpalt as [Epalt Bpalt]. clearbody palt.
    replace (INT_MAX - 1 - palt <? p2) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
    change (CHR_g - 1) with 102. rewrite len_f_spec by lia.
    set (l2 := if 0 <? e then 1 + p2 + palt + e else 1 + p2 + palt).
    assert (Hl2 : l2 = 1 + p2 + palt + Z.max e 0 /\ 1 <= l2 <= p1 + 7) by (subst l2; destruct (Z.ltb_spec 0 e); lia).
    destruct Hl2 as [El2 Bl2]. clearbody l2.
    replace (INT_MAX - pl <? l2) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
    rewrite pad_exact by lia. rewrite zrepeat_nil by lia. rewrite app_nil_r.
    rewrite pad_flag by (cbv; discriminate).
    change (Z.lor 102 32 =? CHR_f) with true. cbv iota.
    destruct (emit_f_spec (out o (zsub PREFIX_STR prefix pl)) big a r0 z' p2 k WB) as [txt (Ef & Ff & Lf)]; try lia.
    { intros Hra. apply ZB. lia. }
    { right. split; [lia| exact Hka]. }
    rewrite Ef. rewrite pad_flag by (cbv; discriminate).
    exists (zsub PREFIX_STR prefix pl ++ txt), l2. unfold out. rewrite <- app_assoc.
    split; [f_equal; f_equal; lia|]. split.
    + rewrite zlength_app, PL, Lf, El2, Epalt.
      destruct (Z.leb_spec a r0); destruct (Z.eqb_spec p2 0); lia.
    + split; [| exact Bl2]. apply Forall_app. split; [exact Fpre|]. eapply Forall_impl; [| exact Ff]. apply gch_isdigdot.
  -
    change (Z.lor (CHR_g - 2) 32 =? CHR_f) with false. cbv iota.
    set (p2 := Z.min (p1 - 1) (Z.max 0 (9 * (z' - r0 - 1) + e - jt))).
    assert (Hp2 : 0 <= p2 <= p1 - 1) by (subst p2; lia). clearbody p2.
    cbn [negb orb]. rewrite Bool.orb_false_r.
    set (palt := if negb (p2 =? 0) then 1 else 0).
    assert (Hpalt : palt = (if p2 =? 0 then 0 else 1) /\ 0 <= palt <= 1) by (subst palt; destruct (p2 =? 0); cbn; lia).
    destruct Hpalt as [Epalt Bpalt]. clearbody palt.
    replace (INT_MAX - 1 - palt <? p2) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
    change (CHR_g - 2) with 101.
    pose proof (TS_e_bound _ _ _ _ _ HT) as EB.
    destruct (len_e_spec (1 + p2 + palt) e ltac:(lia) ltac:(lia)) as [estr [eb (El & Hest & Leb & Geb)]]. rewrite El.
    replace (INT_MAX - pl <? 1 + p2 + palt + (12 - estr)) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
    rewrite pad_exact by lia. rewrite zrepeat_nil by lia. rewrite app_nil_r.
    rewrite pad_flag by (cbv; discriminate).
    change (Z.lor 101 32 =? CHR_f) with false. cbv iota.
    destruct (emit_e_spec (out o (zsub PREFIX_STR prefix pl)) big a z' p2 eb estr k WB) as [txt (Ee & Fe & Le)]; try lia.
    { right. split; [lia| exact Hka]. }
    rewrite Ee. rewrite pad_flag by (cbv; discriminate).
    exists (zsub PREFIX_STR prefix pl ++ txt ++ zsub eb estr (12 - estr)), (1 + p2 + palt + (12 - estr)). unfold out. rewrite <- !app_assoc.
    split; [f_equal; f_equal; lia|]. split.
    + rewrite !zlength_app, PL, Le, zlength_zsub by lia. rewrite Epalt.
      destruct (Z.ltb_spec 0 p2); destruct (Z.eqb_spec p2 0); lia.
    + split; [| lia]. apply Forall_app. split; [exact Fpre|]. apply Forall_app. split; [eapply Forall_impl; [| exact Fe]; apply gch_isdigdot|].
      apply zsub_Forall; try lia. intros kk Hkk. apply Geb. lia.
Qed.
