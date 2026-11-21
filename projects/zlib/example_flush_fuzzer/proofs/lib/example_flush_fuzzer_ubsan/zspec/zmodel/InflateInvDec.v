(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms InflateGarbBase.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInv InflateInvRun InflateInvTab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma pow2_pos : forall n, 0 <= n -> 0 < 2 ^ n.
Proof. intros n Hn. apply Z.pow_pos_nonneg; lia. Qed.

Lemma mod_mod_indep : forall a op m B, 0 <= op -> 0 <= m <= B ->
  ((a mod 2 ^ B) mod 2 ^ op) mod 2 ^ m = (a mod 2 ^ op) mod 2 ^ m.
Proof.
  intros a op m B Hop Hm.
  destruct (Z_le_gt_dec m op).
  - rewrite !(mod_pow2_le _ m op) by lia. apply mod_pow2_le. lia.
  - pose proof (pow2_pos op ltac:(lia)). pose proof (Z.pow_lt_mono_r 2 op m ltac:(lia) ltac:(lia)).
    rewrite (Z.mod_small ((a mod 2 ^ B) mod 2 ^ op) (2 ^ m)) by (pose proof (Z.mod_pos_bound (a mod 2 ^ B) (2 ^ op)); lia).
    rewrite (Z.mod_small (a mod 2 ^ op) (2 ^ m)) by (pose proof (Z.mod_pos_bound a (2 ^ op)); lia).
    apply mod_pow2_le. lia.
Qed.

Lemma div_mod_pow2 : forall a r B, 0 <= r <= B -> (a mod 2 ^ B) / 2 ^ r = (a / 2 ^ r) mod 2 ^ (B - r).
Proof.
  intros a r B H.
  pose proof (pow2_pos r ltac:(lia)) as Pr. pose proof (pow2_pos (B - r) ltac:(lia)) as Pbr.
  assert (E : 2 ^ B = 2 ^ r * 2 ^ (B - r)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite E. rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm. rewrite Z.div_add by lia. rewrite (Z.div_small (a mod 2 ^ r)) by (apply Z.mod_pos_bound; lia).
  lia.
Qed.

Lemma BITSv_mod : forall h n, 0 <= h -> 0 <= n <= 32 -> BITSv h n = h mod 2 ^ n.
Proof.
  intros h n Hh Hn. unfold BITSv. rewrite zmask_ones by lia. rewrite Z.min_l by lia. rewrite Z.land_ones by lia.
  rewrite wrap32_mod. apply mod_pow2_le. lia.
Qed.
Lemma land_ones_mod : forall h n, 0 <= n -> Z.land h (Z.ones n) = h mod 2 ^ n.
Proof. intros h n Hn. apply Z.land_ones. exact Hn. Qed.
Lemma land_zmask_mod : forall h n, 0 <= n <= 32 -> Z.land h (zmask n) = h mod 2 ^ n.
Proof. intros h n Hn. rewrite zmask_ones by lia. rewrite Z.min_l by lia. apply Z.land_ones. lia. Qed.
Lemma shiftr_div : forall h b, 0 <= b -> Z.shiftr h b = h / 2 ^ b.
Proof. intros h b Hb. apply Z.shiftr_div_pow2. exact Hb. Qed.
Lemma idx2_eq : forall h b o, 0 <= h -> 0 <= b -> 0 <= o -> b + o <= 32 ->
  Z.shiftr (BITSv h (b + o)) b = (h / 2 ^ b) mod 2 ^ o.
Proof.
  intros h b o Hh Hb Ho Hbo. rewrite BITSv_mod by lia. rewrite shiftr_div by lia.
  rewrite div_mod_pow2 by lia. f_equal. f_equal. lia.
Qed.
Lemma idxf_eq : forall h b o, 0 <= b -> 0 <= o <= 32 -> Z.land (Z.shiftr h b) (zmask o) = (h / 2 ^ b) mod 2 ^ o.
Proof. intros h b o Hb Ho. rewrite land_zmask_mod by lia. rewrite shiftr_div by lia. reflexivity. Qed.


Section Stable.
  Variables (rd : Z -> Z) (root : Z).
  Hypothesis REP : rep_ok rd root.
  Hypothesis Hroot : 0 <= root.

  Lemma root_stable : forall h h' b, 0 <= b ->
    h' mod 2 ^ b = h mod 2 ^ b ->
    is_linkop (code_op (rd (h mod 2 ^ root))) = false ->
    0 <= code_bits (rd (h mod 2 ^ root)) <= b -> code_bits (rd (h mod 2 ^ root)) <= root ->
    rd (h' mod 2 ^ root) = rd (h mod 2 ^ root).
  Proof.
    intros h h' b Hb E NL Hl Hlr. destruct REP as [R _].
    pose proof (pow2_pos root Hroot).
    apply (R (h mod 2 ^ root) (h' mod 2 ^ root)); [apply Z.mod_pos_bound; lia | apply Z.mod_pos_bound; lia | exact NL |].
    rewrite !(mod_pow2_le _ (code_bits _) root) by lia.
    rewrite <- (mod_pow2_le h (code_bits (rd (h mod 2 ^ root))) b) by lia.
    rewrite <- (mod_pow2_le h' (code_bits (rd (h mod 2 ^ root))) b) by lia.
    rewrite E. reflexivity.
  Qed.

  Lemma root_same : forall h h' b, 0 <= b -> h' mod 2 ^ b = h mod 2 ^ b -> root <= b ->
    rd (h' mod 2 ^ root) = rd (h mod 2 ^ root).
  Proof.
    intros h h' b Hb E Hr. rewrite <- (mod_pow2_le h root b), <- (mod_pow2_le h' root b) by lia. rewrite E. reflexivity.
  Qed.

  Lemma sub_stable : forall h h' b, 0 <= b -> 0 <= h -> 0 <= h' ->
    h' mod 2 ^ b = h mod 2 ^ b ->
    let l := rd (h mod 2 ^ root) in
    is_linkop (code_op l) = true -> 0 <= code_op l -> root <= b ->
    let e := rd (code_val l + (h / 2 ^ root) mod 2 ^ code_op l) in
    0 <= code_bits e -> root + code_bits e <= b ->
    rd (code_val l + (h' / 2 ^ root) mod 2 ^ code_op l) = e.
  Proof.
    intros h h' b Hb Hh Hh' E l L Hop Hr e He Hbe. subst l e. destruct REP as [_ R].
    pose proof (pow2_pos root Hroot). pose proof (pow2_pos (code_op (rd (h mod 2 ^ root))) Hop).
    apply (R (h mod 2 ^ root) ltac:(apply Z.mod_pos_bound; lia) L);
      [apply Z.mod_pos_bound; lia | apply Z.mod_pos_bound; lia |].
    set (l := rd (h mod 2 ^ root)) in *. set (m := code_bits (rd (code_val l + (h / 2 ^ root) mod 2 ^ code_op l))) in *.
    transitivity (((h mod 2 ^ b) / 2 ^ root) mod 2 ^ code_op l mod 2 ^ m).
    { rewrite div_mod_pow2 by lia. symmetry. apply mod_mod_indep; lia. }
    transitivity (((h' mod 2 ^ b) / 2 ^ root) mod 2 ^ code_op l mod 2 ^ m).
    { rewrite E. reflexivity. }
    rewrite div_mod_pow2 by lia. apply mod_mod_indep; lia.
  Qed.
End Stable.


Section Exit.
  Variables (rd : Z -> Z) (root : Z).
  Hypothesis REP : rep_ok rd root.
  Hypothesis Hroot : 0 <= root <= 15.

  Lemma pulled_root : forall h1 b1, 0 <= h1 -> 8 <= b1 ->
    let e := rd (h1 mod 2 ^ root) in
    is_linkop (code_op e) = false -> 0 <= code_bits e <= root ->
    b1 - 8 < code_bits (rd ((htrunc h1 (b1 - 8)) mod 2 ^ root)) ->
    b1 - code_bits e < 8.
  Proof.
    intros h1 b1 Hh Hb e NL Be M. subst e. unfold htrunc in M.
    destruct (Z_lt_le_dec (b1 - 8) (code_bits (rd (h1 mod 2 ^ root)))); [lia|]. exfalso.
    rewrite (root_stable rd root REP ltac:(lia) h1 (h1 mod 2 ^ (b1 - 8)) (b1 - 8) ltac:(lia)) in M; try lia.
    - apply mod_pow2_le. lia.
    - exact NL.
  Qed.

  Lemma pulled_link : forall h1 b1, 0 <= h1 -> 8 <= b1 ->
    let e := rd (h1 mod 2 ^ root) in
    code_bits e = root ->
    b1 - 8 < code_bits (rd ((htrunc h1 (b1 - 8)) mod 2 ^ root)) ->
    b1 - root < 8.
  Proof.
    intros h1 b1 Hh Hb e Be M. subst e. unfold htrunc in M.
    destruct (Z_lt_le_dec (b1 - 8) root); [lia|]. exfalso.
    rewrite (mod_pow2_le h1 root (b1 - 8)) in M by lia. lia.
  Qed.

  Lemma pulled_sub : forall h2 b2, 0 <= h2 -> 8 <= b2 ->
    let l := rd (h2 mod 2 ^ root) in
    is_linkop (code_op l) = true -> 0 <= code_op l -> root <= b2 - 8 ->
    let e := rd (code_val l + (h2 / 2 ^ root) mod 2 ^ code_op l) in
    0 <= code_bits e ->
    b2 - 8 < root + code_bits (rd (code_val l + ((htrunc h2 (b2 - 8)) / 2 ^ root) mod 2 ^ code_op l)) ->
    b2 - root - code_bits e < 8.
  Proof.
    intros h2 b2 Hh Hb l L Hop Hr e He M. subst l e. unfold htrunc in M.
    destruct (Z_lt_le_dec (b2 - 8) (root + code_bits (rd (code_val (rd (h2 mod 2 ^ root)) + (h2 / 2 ^ root) mod 2 ^ code_op (rd (h2 mod 2 ^ root)))))); [lia|]. exfalso.
    pose proof (sub_stable rd root REP ltac:(lia) h2 (h2 mod 2 ^ (b2 - 8)) (b2 - 8) ltac:(lia) Hh
                  ltac:(apply Z.mod_pos_bound; apply pow2_pos; lia) ltac:(apply mod_pow2_le; lia) L Hop Hr He ltac:(lia)) as S.
    cbv zeta in S. rewrite S in M. lia.
  Qed.
End Exit.


Lemma BITSv_hpre : forall h2 h1 b1 n, hpre h2 b1 h1 -> 0 <= h1 -> 0 <= h2 -> 0 <= n <= b1 -> n <= 32 ->
  BITSv h2 n = BITSv h1 n.
Proof.
  intros h2 h1 b1 n P H1 H2 Hn Hn32. unfold hpre, htrunc in P. rewrite !BITSv_mod by lia.
  rewrite <- (mod_pow2_le h2 n b1) by lia. rewrite P. reflexivity.
Qed.

Lemma hpre_nopull : forall h1 h0 b0, hpre h1 b0 h0 -> 0 <= h1 < 2 ^ b0 -> h1 = h0.
Proof. intros h1 h0 b0 P H. unfold hpre, htrunc in P. rewrite Z.mod_small in P by exact H. exact P. Qed.

Section Cons.
  Variable s : inflate_state.

  Lemma lcons_term : forall h e, 0 <= h -> 0 <= is_lenbits s <= 32 ->
    e = code_at s (is_lencode s) (BITSv h (is_lenbits s)) -> is_linkop (code_op e) = false -> lcons s h = code_bits e.
  Proof.
    intros h e Hh Hlb E NL. unfold lcons. rewrite land_ones_mod by lia. rewrite <- BITSv_mod by lia. rewrite <- E, NL. reflexivity.
  Qed.
  Lemma lcons_link : forall h e, 0 <= h -> 0 <= is_lenbits s <= 32 ->
    e = code_at s (is_lencode s) (BITSv h (is_lenbits s)) -> is_linkop (code_op e) = true ->
    0 <= code_bits e -> 0 <= code_op e -> code_bits e + code_op e <= 32 ->
    lcons s h = code_bits e + code_bits (code_at s (is_lencode s) (code_val e + Z.shiftr (BITSv h (code_bits e + code_op e)) (code_bits e))).
  Proof.
    intros h e Hh Hlb E L Hb Hop Hbo. unfold lcons. rewrite land_ones_mod by lia. rewrite <- BITSv_mod by lia. rewrite <- E, L.
    rewrite idxf_eq by lia. rewrite idx2_eq by lia. reflexivity.
  Qed.
  Lemma lcons_ge_root : forall h, 0 <= h -> 0 <= is_lenbits s <= 32 ->
    code_bits (code_at s (is_lencode s) (BITSv h (is_lenbits s))) <= lcons s h.
  Proof.
    intros h Hh Hlb. unfold lcons. rewrite land_ones_mod by lia. rewrite <- BITSv_mod by lia.
    match goal with |- context [code_bits ?e1 + code_bits ?e2] => pose proof (code_bits_bound e2) end.
    destruct (is_linkop _); lia.
  Qed.

  Lemma dcons_term : forall h e, 0 <= h -> 0 <= is_distbits s <= 32 ->
    e = code_at s (is_distcode s) (BITSv h (is_distbits s)) -> is_linkop (code_op e) = false -> dcons s h = code_bits e.
  Proof.
    intros h e Hh Hlb E NL. unfold dcons. rewrite land_ones_mod by lia. rewrite <- BITSv_mod by lia. rewrite <- E, NL. reflexivity.
  Qed.
  Lemma dcons_link : forall h e, 0 <= h -> 0 <= is_distbits s <= 32 ->
    e = code_at s (is_distcode s) (BITSv h (is_distbits s)) -> is_linkop (code_op e) = true ->
    0 <= code_bits e -> 0 <= code_op e -> code_bits e + code_op e <= 32 ->
    dcons s h = code_bits e + code_bits (code_at s (is_distcode s) (code_val e + Z.shiftr (BITSv h (code_bits e + code_op e)) (code_bits e))).
  Proof.
    intros h e Hh Hlb E L Hb Hop Hbo. unfold dcons. rewrite land_ones_mod by lia. rewrite <- BITSv_mod by lia. rewrite <- E, L.
    rewrite idxf_eq by lia. rewrite idx2_eq by lia. reflexivity.
  Qed.
  Lemma dcons_ge_root : forall h, 0 <= h -> 0 <= is_distbits s <= 32 ->
    code_bits (code_at s (is_distcode s) (BITSv h (is_distbits s))) <= dcons s h.
  Proof.
    intros h Hh Hlb. unfold dcons. rewrite land_ones_mod by lia. rewrite <- BITSv_mod by lia.
    match goal with |- context [code_bits ?e1 + code_bits ?e2] => pose proof (code_bits_bound e2) end.
    destruct (is_linkop _); lia.
  Qed.

  Lemma ccons_eq : forall h e, 0 <= h -> 0 <= is_lenbits s <= 32 ->
    e = code_at s (is_lencode s) (BITSv h (is_lenbits s)) -> ccons s h = code_bits e + clx (code_val e).
  Proof.
    intros h e Hh Hlb E. unfold ccons. rewrite land_ones_mod by lia. rewrite <- BITSv_mod by lia. rewrite <- E. reflexivity.
  Qed.
  Lemma clx_range : forall v, 0 <= clx v <= 7.
  Proof. intros v. unfold clx. destruct (v <? 16); [lia|]. destruct (v =? 16); [lia|]. destruct (v =? 17); lia. Qed.
End Cons.

Lemma BITSv_idx : forall h n, 0 <= h -> 0 <= n <= 32 -> BITSv h n = h mod 2 ^ n.
Proof. intros. apply BITSv_mod; assumption. Qed.
Lemma idx2_div : forall h b o, 0 <= h -> 0 <= b -> 0 <= o -> b + o <= 32 ->
  Z.shiftr (BITSv h (b + o)) b = (h / 2 ^ b) mod 2 ^ o.
Proof. intros. apply idx2_eq; assumption. Qed.


Lemma htrunc_nonneg : forall h b, 0 <= b -> 0 <= htrunc h b.
Proof. intros h b Hb. unfold htrunc. apply Z.mod_pos_bound. apply pow2_pos. exact Hb. Qed.

Section ExitD.
  Variables (rd : Z -> Z) (root : Z).
  Hypothesis REP : rep_ok rd root.
  Hypothesis Hroot : 0 <= root <= 15.

  Lemma dec1_exit : forall h0 b0 h1 b1 e,
    0 <= b0 -> 0 <= h1 < 2 ^ b1 -> hpre h1 b0 h0 ->
    e = rd (BITSv h1 root) -> is_linkop (code_op e) = false -> 0 <= code_bits e <= root ->
    (b1 = b0 \/ (b0 + 8 <= b1 /\ b1 - 8 < code_bits (rd (BITSv (htrunc h1 (b1 - 8)) root)))) ->
    b1 - code_bits e < 8 \/ (b1 = b0 /\ h1 = h0).
  Proof.
    intros h0 b0 h1 b1 e Hb0 Hh1 P E NL Be D.
    destruct D as [Eb | [Ge M]].
    - right. split; [exact Eb|]. apply (hpre_nopull h1 h0 b0 P). rewrite <- Eb. exact Hh1.
    - left. rewrite BITSv_idx in E by lia. rewrite BITSv_idx in M by (try apply htrunc_nonneg; lia). subst e.
      apply (pulled_root rd root REP Hroot h1 b1); try lia; assumption.
  Qed.

  Lemma dec1_exit_link : forall h0 b0 h1 b1 e,
    0 <= b0 -> 0 <= h1 < 2 ^ b1 -> hpre h1 b0 h0 ->
    e = rd (BITSv h1 root) -> code_bits e = root ->
    (b1 = b0 \/ (b0 + 8 <= b1 /\ b1 - 8 < code_bits (rd (BITSv (htrunc h1 (b1 - 8)) root)))) ->
    b1 - root < 8 \/ (b1 = b0 /\ h1 = h0).
  Proof.
    intros h0 b0 h1 b1 e Hb0 Hh1 P E Be D.
    destruct D as [Eb | [Ge M]].
    - right. split; [exact Eb|]. apply (hpre_nopull h1 h0 b0 P). rewrite <- Eb. exact Hh1.
    - left. rewrite BITSv_idx in E by lia. rewrite BITSv_idx in M by (try apply htrunc_nonneg; lia). subst e.
      apply (pulled_link rd root Hroot h1 b1); try lia; assumption.
  Qed.

  Lemma dec2_exit : forall h1 b1 h2 b2 l e2,
    l = rd (BITSv h1 root) -> is_linkop (code_op l) = true -> 0 <= code_op l -> root + code_op l <= 32 -> code_bits l = root ->
    root <= b1 -> 0 <= h1 -> 0 <= h2 < 2 ^ b2 -> hpre h2 b1 h1 ->
    e2 = rd (code_val l + Z.shiftr (BITSv h2 (root + code_op l)) root) -> 0 <= code_bits e2 ->
    (b2 = b1 \/ (b1 + 8 <= b2 /\ b2 - 8 < root + code_bits (rd (code_val l + Z.shiftr (BITSv (htrunc h2 (b2 - 8)) (root + code_op l)) root)))) ->
    b2 - root - code_bits e2 < 8 \/ (b2 = b1 /\ h2 = h1).
  Proof.
    intros h1 b1 h2 b2 l e2 El L Hop Hro Bl Hr1 Hh1 Hh2 P E2 Be2 D.
    destruct D as [Eb | [Ge M]].
    - right. split; [exact Eb|]. apply (hpre_nopull h2 h1 b1 P). rewrite <- Eb. exact Hh2.
    - left.
      assert (El2 : l = rd (h2 mod 2 ^ root)).
      { rewrite El. rewrite <- (BITSv_hpre h2 h1 b1 root P) by lia. rewrite BITSv_idx by lia. reflexivity. }
      rewrite idx2_div in E2 by lia. rewrite idx2_div in M by (try apply htrunc_nonneg; lia).
      pose proof (pulled_sub rd root REP ltac:(lia) h2 b2 ltac:(lia) ltac:(lia)) as PS. cbv zeta in PS.
      rewrite <- El2 in PS. subst e2. apply PS; try assumption; lia.
  Qed.
End ExitD.

Lemma len_rep : forall s, sinv s -> codes_live (is_mode s) = true -> rep_ok (cat (is_codes s) (is_lencode s)) (is_lenbits s).
Proof. intros s SI L. destruct SI as (_&_&_&_&_&_&_&_&_&_&_&TR&_). exact (proj1 (TR L)). Qed.
Lemma dist_rep : forall s, sinv s -> codes_live (is_mode s) = true -> rep_ok (cat (is_codes s) (is_distcode s)) (is_distbits s).
Proof. intros s SI L. destruct SI as (_&_&_&_&_&_&_&_&_&_&_&TR&_). exact (proj2 (TR L)). Qed.
Lemma code_rep : forall s, sinv s -> is_mode s = CODELENS -> rep_ok (cat (is_codes s) (is_lencode s)) (is_lenbits s).
Proof. intros s SI L. destruct SI as (_&_&_&_&_&_&_&_&_&_&_&_&CR). exact (CR L). Qed.


Lemma lcons_rd : forall s rd h, (forall i, code_at s (is_lencode s) i = rd i) -> 0 <= is_lenbits s ->
  lcons s h = (let e := rd (h mod 2 ^ is_lenbits s) in
               if is_linkop (code_op e) then code_bits e + code_bits (rd (code_val e + (h / 2 ^ code_bits e) mod 2 ^ code_op e))
               else code_bits e).
Proof.
  intros s rd h Hrd Hlb. unfold lcons. rewrite land_ones_mod by lia. rewrite !Hrd.
  destruct (is_linkop _) eqn:L; [| reflexivity].
  rewrite zmask_ones by (pose proof (code_op_bound (rd (h mod 2 ^ is_lenbits s))); lia).
  pose proof (proj1 (is_linkop_true _) L).
  rewrite Z.min_l by lia. rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by (pose proof (code_bits_bound (rd (h mod 2 ^ is_lenbits s))); lia).
  reflexivity.
Qed.

Lemma lcons_pending : forall rd root ext, rep_ok rd root -> tab_ok LENS rd root ext = true ->
  forall s h0 b0 h', (forall i, code_at s (is_lencode s) i = rd i) -> is_lenbits s = root ->
  0 <= h0 < 2 ^ b0 -> 0 <= h' -> h' mod 2 ^ b0 = h0 -> b0 < lcons s h0 -> b0 < lcons s h'.
Proof.
  intros rd root ext REP T s h0 b0 h' Hrd Hlb Hh0 Hh' M BP.
  destruct (tab_ok_root _ _ _ _ T) as (R1 & R2 & R3).
  assert (Hb0 : 0 <= b0) by (destruct (Z_lt_le_dec b0 0); [|lia]; exfalso; rewrite Z.pow_neg_r in Hh0 by lia; lia).
  rewrite (lcons_rd s rd h0 Hrd) in BP by lia. rewrite (lcons_rd s rd h' Hrd) by lia. rewrite Hlb in *. cbv zeta in *.
  assert (M' : h0 mod 2 ^ b0 = h' mod 2 ^ b0) by (rewrite <- M; rewrite Z.mod_mod by (pose proof (pow2_pos b0 Hb0); lia); reflexivity).
  pose proof (tab_root_entry LENS _ _ _ (h' mod 2 ^ root) T ltac:(apply Z.mod_pos_bound; apply pow2_pos; lia)) as RT. cbv beta in RT.
  destruct RT as (RB & _ & _ & [[NL TM] | (OP & BR & VR & XR & SUB)]).
  -
    rewrite NL. destruct (Z_lt_le_dec b0 (code_bits (rd (h' mod 2 ^ root)))) as [|LE]; [lia|]. exfalso.
    pose proof (root_stable rd root REP ltac:(lia) h' h0 b0 Hb0 M' NL ltac:(lia) ltac:(lia)) as ST.
    rewrite ST, NL in BP. lia.
  -
    assert (LK : is_linkop (code_op (rd (h' mod 2 ^ root))) = true) by (apply is_linkop_true; lia). rewrite LK.
    match goal with |- context [code_bits (rd (h' mod 2 ^ root)) + code_bits ?e2] =>
      pose proof (code_bits_bound e2) as CB2;
      destruct (Z_lt_le_dec b0 (code_bits (rd (h' mod 2 ^ root)) + code_bits e2)) as [|LE]; [lia|] end.
    exfalso.
    pose proof (root_same rd root ltac:(lia) h' h0 b0 Hb0 M' ltac:(lia)) as RS.
    pose proof (sub_stable rd root REP ltac:(lia) h' h0 b0 Hb0 Hh' ltac:(lia) M') as SS. cbv zeta in SS.
    rewrite BR in LE, CB2.
    specialize (SS LK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    rewrite RS, LK, BR, SS in BP. lia.
Qed.


Lemma ones_index : forall h n, 0 <= n -> 0 <= Z.land h (Z.ones n) < 2 ^ n.
Proof. intros h n Hn. apply land_ones_bound. exact Hn. Qed.
Lemma zmask_index : forall h n, 0 <= n <= 15 -> 0 <= Z.land h (zmask n) < 2 ^ n.
Proof. intros h n Hn. rewrite zmask_ones by lia. rewrite Z.min_l by lia. apply land_ones_bound. lia. Qed.

Lemma lcons_pos_tab : forall s ext h, tab_ok LENS (fun i => code_at s (is_lencode s) i) (is_lenbits s) ext = true -> 0 <= h -> 1 <= lcons s h.
Proof.
  intros s ext h T Hh. unfold lcons.
  destruct (tab_ok_root _ _ _ _ T) as (R1 & _ & _).
  pose proof (tab_root_entry LENS _ _ _ _ T (ones_index h (is_lenbits s) ltac:(lia))) as RT. cbv beta in RT.
  set (e := code_at s (is_lencode s) (Z.land h (Z.ones (is_lenbits s)))) in *.
  destruct RT as (RB & _ & _ & [[NL _] | (OP & _ & _ & _ & SUB)]).
  - rewrite NL. lia.
  - replace (is_linkop (code_op e)) with true by (symmetry; apply is_linkop_true; lia).
    destruct (SUB _ (zmask_index (Z.shiftr h (code_bits e)) (code_op e) ltac:(lia))) as [_ TM2].
    pose proof (term_ok_LENS _ _ TM2) as (HB2 & _). lia.
Qed.

Lemma DEBT_small : forall s c r ext,
  tab_ok LENS (fun i => code_at s (is_lencode s) i) (is_lenbits s) ext = true ->
  0 <= ir_next r -> ir_bits r < 8 -> DEBT (mkW s c r).
Proof.
  intros s c r ext T Hn Hb h' Hh' _. cbn [w_s w_r]. pose proof (lcons_pos_tab s ext h' T Hh'). lia.
Qed.
