(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VWord2 VState VLogic VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VGamma VStepSound VStepMemSound.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_le_split bs k : (k <= length bs)%nat ->
  bytes_le_to_Z bs = bytes_le_to_Z (firstn k bs) + bytes_le_to_Z (skipn k bs) * 2 ^ (8 * Z.of_nat k)
  /\ 0 <= bytes_le_to_Z (firstn k bs) < 2 ^ (8 * Z.of_nat k).
Proof.
  intros Hk.
  pose proof (bytes_le_to_Z_bound (firstn k bs)) as B1. rewrite firstn_length_le in B1 by exact Hk.
  pose proof (bytes_le_to_Z_nonneg (firstn k bs)) as B0. pose proof (bytes_le_to_Z_nonneg (skipn k bs)) as C0.
  pose proof (pow2_pos (8 * Z.of_nat k) ltac:(lia)) as P0.
  split; [|lia].
  rewrite <- (firstn_skipn k bs) at 1. rewrite bytes_le_app. rewrite firstn_length_le by exact Hk.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm.
  rewrite (lor_disjoint _ _ (8 * Z.of_nat k)); [lia|lia|apply Z.mul_nonneg_nonneg; lia|apply Z.mod_mul; lia|lia].
Qed.

Lemma bytes_le_firstn bs k : (k <= length bs)%nat ->
  bytes_le_to_Z (firstn k bs) = bytes_le_to_Z bs mod 2 ^ (8 * Z.of_nat k).
Proof.
  intros Hk. destruct (bytes_le_split bs k Hk) as [E B]. rewrite E.
  pose proof (pow2_pos (8 * Z.of_nat k) ltac:(lia)).
  rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia.
Qed.

Lemma bytes_le_skipn bs k : (k <= length bs)%nat ->
  bytes_le_to_Z (skipn k bs) = bytes_le_to_Z bs / 2 ^ (8 * Z.of_nat k).
Proof.
  intros Hk. destruct (bytes_le_split bs k Hk) as [E B]. rewrite E.
  pose proof (pow2_pos (8 * Z.of_nat k) ltac:(lia)).
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma const_slice_eq c w sh n : 0 <= w -> 0 <= sh -> 0 <= n ->
  const_slice c w sh n = ((c mod 2 ^ (8 * w)) / 2 ^ (8 * sh)) mod 2 ^ (8 * n).
Proof.
  intros. unfold const_slice. rewrite !land_lowmask, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma const_slice_range c w sh n : 0 <= w -> 0 <= sh -> 0 <= n -> 0 <= const_slice c w sh n < 2 ^ (8 * n).
Proof.
  intros. rewrite const_slice_eq by lia. apply Z.mod_pos_bound. apply pow2_pos. lia.
Qed.

(* [comment removed for export] *)
Lemma ldval_sign_adjust sg n X : 0 < n <= 8 -> 0 <= X < 2 ^ (8 * n) ->
  ldval sg n X = zwrap 64 (sign_adjust sg n X).
Proof.
  intros Hn HX. unfold ldval, sign_adjust.
  assert (X64 : 0 <= X < 2 ^ 64).
  { split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 HX)|]. apply Z.pow_le_mono_r; lia. }
  pose proof (pow2_half (8 * n) ltac:(lia)) as Hh.
  destruct sg; cbn [andb].
  - destruct (Z.ltb_spec n 8) as [Hn8|Hn8].
    + f_equal. destruct (Z.leb_spec (2 ^ (8 * n - 1)) X).
      * rewrite (zswrap_congr (8 * n) X (X - 2 ^ (8 * n))); [|lia|exists 1; lia].
        apply zswrap_id; lia.
      * apply zswrap_id; lia.
    + assert (n = 8) by lia. subst n.
      destruct (Z.leb_spec (2 ^ (8 * 8 - 1)) X).
      * rewrite (zwrap_congr 64 (X - 2 ^ (8 * 8)) X); [|lia|exists (-1); lia].
        symmetry. apply zwrap_id. exact X64.
      * symmetry. apply zwrap_id. exact X64.
  - symmetry. apply zwrap_id. exact X64.
Qed.

(* [comment removed for export] *)
Lemma list_min_le l : forall m x, (x = m \/ In x l) -> list_min l m <= x.
Proof.
  induction l as [|y t IH]; intros m x Hx; cbn [list_min].
  - destruct Hx as [->|[]]. lia.
  - destruct Hx as [->|[->|Hx]].
    + eapply Z.le_trans; [apply (IH (Z.min m y) (Z.min m y)); auto|lia].
    + eapply Z.le_trans; [apply (IH (Z.min m x) (Z.min m x)); auto|lia].
    + apply IH. auto.
Qed.

Lemma list_max_ge l : forall m x, (x = m \/ In x l) -> x <= list_max l m.
Proof.
  induction l as [|y t IH]; intros m x Hx; cbn [list_max].
  - destruct Hx as [->|[]]. lia.
  - destruct Hx as [->|[->|Hx]].
    + eapply Z.le_trans; [|apply (IH (Z.max m y) (Z.max m y)); auto]. lia.
    + eapply Z.le_trans; [|apply (IH (Z.max m x) (Z.max m x)); auto]. lia.
    + apply IH. auto.
Qed.

Lemma all_eq_sound l v x : all_eq l v = true -> In x l -> x = v.
Proof.
  induction l as [|y t IH]; cbn [all_eq]; intros H Hx; [destruct Hx|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. destruct Hx as [<-|Hx]; auto.
Qed.

Lemma zinsert_in x y l : In x (zinsert y l) <-> x = y \/ In x l.
Proof.
  induction l as [|z t IH]; cbn [zinsert].
  - cbn. intuition congruence.
  - destruct (Z.compare_spec y z).
    + subst. cbn. intuition congruence.
    + cbn. intuition congruence.
    + cbn. rewrite IH. intuition congruence.
Qed.

Lemma zsort_dedup_in x l : In x l -> In x (zsort_dedup l).
Proof.
  unfold zsort_dedup. induction l as [|y t IH]; cbn [fold_right]; intros Hx; [destruct Hx|].
  apply (proj2 (zinsert_in x y _)). destruct Hx as [->|Hx]; auto.
Qed.

Lemma wordZ_add_nat a k : (wordZ a + nat_to_word k)%bv = wordZ (a + Z.of_nat k).
Proof.
  apply bv_eq. unfold nat_to_word, wordZ. rewrite bv_add_unsigned, bv_wrap64_zwrap, !u_Z_to_bv64.
  apply zwrap64_add.
Qed.

(* [comment removed for export] *)
Lemma lgamma_add_valset A nu s ds :
  lgamma A nu -> In (nu s) ds -> (s < vs_next A)%positive ->
  lgamma (set_valset A (pm_set s ds (vs_valset A))) nu
  /\ aext A (set_valset A (pm_set s ds (vs_valset A))) nu nu.
Proof.
  intros (HS&HC&HM&HV&(B0&B1&B2&B3&B4&(C1&C2&C3))) Hin Hs. split.
  - split; [exact HS|]. split; [exact HC|]. split; [exact HM|]. split.
    { intros s' vs Hg'. cbn [vs_valset set_valset] in Hg'. rewrite pm_get_set in Hg'.
      destruct (Pos.eqb_spec s' s); [|exact (HV _ _ Hg')]. injection Hg' as <-. subst s'. exact Hin. }
    split; [exact B0|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
    split; [exact C1|]. split; [exact C2|].
    intros s' vs Hg'. cbn [vs_valset set_valset vs_next] in Hg' |- *. rewrite pm_get_set in Hg'.
    destruct (Pos.eqb_spec s' s); [subst; exact Hs|exact (C3 _ _ Hg')].
  - apply aext_keep; [reflexivity|apply same_shape_set_valset].
Qed.

Section Sound.
  Variable SEGS : list Segment.
  Variable P : vparams.
  Variable E : venv.
  Variable mem0 : word -> option byte.
  Hypothesis PO : params_ok SEGS P.

  Notation gammaP := (gamma SEGS P E mem0).
  Notation MCP := (MC SEGS P E mem0).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma frame_bytes mem a k :
    env_ok P E -> MCP mem -> e_sp0 E - vp_frame P <= a -> a + Z.of_nat k <= e_sp0 E ->
    exists bs, rdn SEGS mem (wordZ a) k = Some bs /\ length bs = k.
  Proof.
    intros HE HM H1 H2. destruct PO as (P0&P1&_). destruct HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12).
    apply rdn_bytes; [lia|lia|]. intros j Hj.
    destruct (MC_frame_ok SEGS P E mem0 mem (a + j) HM) as [_ X]; [lia|exact X].
  Qed.

  Lemma data_bytes mem a k :
    env_ok P E -> MCP mem -> e_data E <= a -> a + Z.of_nat k <= e_data E + e_size E ->
    exists bs, rdn SEGS mem (wordZ a) k = Some bs /\ length bs = k.
  Proof.
    intros HE HM H1 H2. destruct HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12). destruct HM as (MF&MD&MP&MFM).
    apply rdn_bytes; [lia|lia|]. intros j Hj.
    replace (a + j) with (e_data E + (a - e_data E + j)) by lia. apply MD. lia.
  Qed.

  Lemma seg_bytes mem a k lo hi :
    env_ok P E -> In (lo, hi) (vp_segs P) -> lo <= a -> a + Z.of_nat k <= hi ->
    exists bs, rdn SEGS mem (wordZ a) k = Some bs /\ length bs = k.
  Proof.
    intros HE Hin H1 H2. destruct PO as (P0&P1&PS&_). destruct (PS _ _ Hin) as (S0&S1&SB).
    destruct HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12).
    apply rdn_bytes; [lia|lia|]. intros j Hj. apply rdn1_any. apply SB. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma rom_read_sound mem a k v :
    env_ok P E -> MCP mem ->
    (forall x, a <= x < a + Z.of_nat k -> exists lo hi, In (lo, hi) (vp_pristine P) /\ lo <= x < hi) ->
    rom_read (vp_rom P) a k = Some v ->
    exists bs, rdn SEGS mem (wordZ a) k = Some bs /\ bytes_le_to_Z bs = v /\ length bs = k.
  Proof.
    intros HE HM. revert a v. induction k as [|k IH]; intros a v Hpr Hr.
    - cbn in Hr. inversion Hr; subst. exists []. split; [reflexivity|]. split; reflexivity.
    - cbn [rom_read] in Hr.
      destruct (Z.ltb_spec 0 a); [|discriminate].
      destruct (pm_get (Z.to_pos a) (vp_rom P)) as [b|] eqn:Eg; [|discriminate].
      destruct (rom_read (vp_rom P) (a + 1) k) as [rest|] eqn:Er; [|discriminate]. inversion Hr; subst; clear Hr.
      destruct PO as (P0&P1&PS&PF&PW&PR&PP&PB).
      destruct (PB a b ltac:(lia) Eg) as [Hin [bb [Hrom Hbb]]].
      destruct (Hpr a ltac:(lia)) as [lo [hi [Hp Hx]]]. destruct (PP _ _ Hp) as [Plo Phi].
      destruct HM as (MF&MD&MP&MFM) eqn:EHM. clear EHM.
      pose proof (MP lo hi a Hp Hx) as Hnone.
      destruct (IH (a + 1) rest) as [bs [Hbs [Hv Hl]]]; [intros x Hx'; apply Hpr; lia|exact Er|].
      exists (bb :: bs). cbn [rdn]. rewrite Hnone, Hrom.
      destruct k as [|k'].
      + cbn in Hbs. injection Hbs as <-. cbn in Hv. subst rest. split; [reflexivity|]. split; [|reflexivity].
        cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. lia.
      + assert (Ha1 : a + 1 < 2 ^ 64).
        { destruct (Hpr (a + 1) ltac:(lia)) as [lo' [hi' [Hp' Hx']]]. destruct (PP _ _ Hp').
          destruct HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12). lia. }
        rewrite wordZ_add1 by lia. rewrite Hbs. split; [reflexivity|]. split; [|cbn; lia].
        cbn [bytes_le_to_Z]. rewrite Z.shiftl_mul_pow2 by lia.
        pose proof (bv_unsigned_in_range 8 bb) as R8. unfold bv_modulus in R8. cbn in R8.
        pose proof (bytes_le_to_Z_nonneg bs) as NB. change (2 ^ 8) with 256 in *.
        rewrite Z.lor_comm, (lor_disjoint _ _ 8); [lia|lia|apply Z.mul_nonneg_nonneg; lia|change (2 ^ 8) with 256; apply Z.mod_mul; lia|change (2 ^ 8) with 256; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma pristine_cover lo len a k :
    in_ranges (vp_pristine P) lo len = true -> lo <= a -> a + Z.of_nat k <= lo + len ->
    forall x, a <= x < a + Z.of_nat k -> exists plo phi, In (plo, phi) (vp_pristine P) /\ plo <= x < phi.
  Proof.
    intros Hr H1 H2 x Hx. destruct (in_ranges_sound _ _ _ Hr) as [plo [phi (Hin&Q1&Q2)]].
    exists plo, phi. split; [exact Hin|lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma table_values_sound A nu mem addr n sg vals lo len :
    lgamma A nu -> env_ok P E -> MCP mem -> 0 < n <= 8 ->
    in_ranges (vp_pristine P) lo len = true -> lo <= eval nu addr -> eval nu addr + n <= lo + len ->
    table_values P A addr n sg = Some vals ->
    exists bs, rdn SEGS mem (wordZ (eval nu addr)) (Z.to_nat n) = Some bs /\ length bs = Z.to_nat n /\
               In (sign_adjust sg n (bytes_le_to_Z bs)) vals.
  Proof.
    intros HL HE HM Hn Hpr H1 H2 Ht. unfold table_values in Ht.
    destruct (lin_single addr) as [[s k]|] eqn:Es; [|discriminate].
    pose proof (eval_single nu addr s k Es) as Ea.
    pose proof (lp_bounds_sound nu (vs_store A) (lg_sat _ _ HL) (lsym s)) as Hb.
    destruct (lp_bounds (vs_store A) (lsym s)) as [[sl|] [sh|]]; try discriminate.
    destruct Hb as [Hsl Hsh]; cbn [fst snd lo_le hi_ge] in Hsl, Hsh. rewrite eval_lsym in Hsl, Hsh.
    destruct (Z.ltb 4096 (sh - sl) || Z.ltb sh sl); [discriminate|].
    set (cand := match pm_get s (vs_valset A) with
                 | Some vs => List.filter (fun x => Z.leb sl x && Z.leb x sh) vs
                 | None => zrange sl (Z.to_nat (sh - sl + 1)) end) in Ht.
    assert (Hc : In (nu s) cand).
    { unfold cand. destruct (pm_get s (vs_valset A)) as [vs|] eqn:Eg.
      - apply filter_In. split; [destruct HL as (_&_&_&HV&_); exact (HV _ _ Eg)|].
        apply andb_true_intro. split; apply Z.leb_le; lia.
      - apply zrange_in. rewrite Z2Nat.id by lia. lia. }
    clearbody cand.
    set (F := fun x : Z => match rom_read (vp_rom P) (lc addr + k * x) (Z.to_nat n) with
                           | Some v => Some (sign_adjust sg n v) | None => None end) in Ht.
    destruct cand as [|c0 ct]; [destruct Hc|].
    match type of Ht with context [existsb ?g ?l] => destruct (existsb g l) eqn:Ex end; [discriminate|].
    match type of Ht with Some ?x = Some _ => assert (Evals : vals = x) by congruence end. subst vals. clear Ht.
    assert (HF : exists v, rom_read (vp_rom P) (eval nu addr) (Z.to_nat n) = Some v /\ In (Some (sign_adjust sg n v)) (map F (c0 :: ct))).
    { pose proof (in_map F _ _ Hc) as Hin. rewrite Ea.
      destruct (rom_read (vp_rom P) (lc addr + k * nu s) (Z.to_nat n)) as [v|] eqn:Er.
      - exists v. split; [reflexivity|]. replace (Some (sign_adjust sg n v)) with (F (nu s)); [exact Hin|].
        unfold F. rewrite Er. reflexivity.
      - exfalso.
        assert (X : existsb (fun o : option Z => match o with Some _ => false | None => true end) (map F (c0 :: ct)) = true).
        { apply existsb_exists. exists (F (nu s)). split; [exact Hin|]. unfold F. rewrite Er. reflexivity. }
        rewrite X in Ex. discriminate. }
    destruct HF as [v [Hr Hin]].
    destruct (rom_read_sound mem (eval nu addr) (Z.to_nat n) v HE HM) as [bs (Hbs&Hv&Hl)].
    { apply (pristine_cover lo len); auto. rewrite Z2Nat.id by lia. lia. }
    { exact Hr. }
    exists bs. split; [exact Hbs|]. split; [exact Hl|]. rewrite Hv.
    apply in_map_iff. exists (Some (sign_adjust sg n v)). split; [reflexivity|exact Hin].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma const_cover_sound (m : cellmap) nu mem (base lo n c : Z) :
    (forall o w v, In (o, (w, v)) m -> cell_holds SEGS nu mem (base + o) w v) ->
    0 < n -> const_cover m lo n = Some c ->
    exists bs, rdn SEGS mem (wordZ (base + lo)) (Z.to_nat n) = Some bs /\ length bs = Z.to_nat n
               /\ bytes_le_to_Z bs = c /\ 0 <= c < 2 ^ (8 * n).
  Proof.
    intros Hcells Hn. unfold const_cover.
    match goal with |- context [find ?f ?l] => destruct (find f l) as [[o2 [w2 [v2|]]]|] eqn:Ef end;
      [|discriminate|discriminate].
    intros X; injection X as <-.
    apply find_some in Ef as [Hin Hp]. apply cm_overlapping_in in Hin.
    apply andb_prop in Hp as [Hp Hc]. apply andb_prop in Hp as [Hp1 Hp2]. apply Z.leb_le in Hp1. apply Z.leb_le in Hp2.
    pose proof (Hcells _ _ _ Hin) as CH. cbn [cell_holds] in CH. destruct CH as [bs2 [Hbs2 Hval2]].
    pose proof (rdn_length _ _ _ _ _ Hbs2) as Hlen2.
    set (kk := Z.to_nat (lo - o2)).
    pose proof (rdn_skipn SEGS mem _ _ _ kk Hbs2 ltac:(unfold kk; lia)) as Hsk.
    rewrite wordZ_add_nat in Hsk. replace (base + o2 + Z.of_nat kk) with (base + lo) in Hsk by (unfold kk; lia).
    pose proof (rdn_firstn SEGS mem _ _ _ (Z.to_nat n) Hsk ltac:(unfold kk; lia)) as Hrd.
    exists (firstn (Z.to_nat n) (skipn kk bs2)). split; [exact Hrd|].
    split; [rewrite firstn_length_le by (rewrite length_skipn; unfold kk; lia); reflexivity|].
    split; [|apply const_slice_range; lia].
    rewrite bytes_le_firstn by (rewrite length_skipn; unfold kk; lia).
    rewrite bytes_le_skipn by (unfold kk; lia). rewrite Z2Nat.id, Hval2 by lia.
    replace (Z.of_nat kk) with (lo - o2) by (unfold kk; lia).
    rewrite (eval_is_const nu v2 Hc).
    replace (zwrap (8 * w2) (lc v2) / 2 ^ (8 * (lo - o2))) with (lc v2 mod 2 ^ (8 * w2) / 2 ^ (8 * (lo - o2))) by reflexivity.
    symmetry. apply const_slice_eq; lia.
  Qed.

  Lemma range_vals_sound (m : cellmap) nu mem (base n step : Z) sg :
    (forall o w v, In (o, (w, v)) m -> cell_holds SEGS nu mem (base + o) w v) ->
    0 < n -> 0 < step ->
    forall k o vals x,
      range_vals m o step n sg k = Some vals ->
      (exists i, 0 <= i < Z.of_nat k /\ x = o + i * step) ->
      exists bs, rdn SEGS mem (wordZ (base + x)) (Z.to_nat n) = Some bs /\ length bs = Z.to_nat n
                 /\ In (sign_adjust sg n (bytes_le_to_Z bs)) vals.
  Proof.
    intros Hcells Hn Hs. induction k as [|k IH]; intros o vals x Hr [i [Hi Hx]]; [lia|].
    cbn [range_vals] in Hr.
    destruct (const_cover m o n) as [c|] eqn:Ec; [|discriminate].
    destruct (range_vals m (o + step) step n sg k) as [rest|] eqn:Er; [|discriminate]. injection Hr as <-.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    - rewrite Z.mul_0_l, Z.add_0_r in Hx. subst x.
      destruct (const_cover_sound m nu mem base o n c Hcells Hn Ec) as [bs (Hbs&Hl&Hv&_)].
      exists bs. split; [exact Hbs|]. split; [exact Hl|]. left. rewrite Hv. reflexivity.
    - destruct (IH (o + step) rest x Er) as [bs (Hbs&Hl&Hin)].
      { exists (i - 1). split; [lia|]. rewrite Hx. lia. }
      exists bs. split; [exact Hbs|]. split; [exact Hl|]. right. exact Hin.
  Qed.

  Lemma range_step_sound A nu off lo n :
    lgamma A nu -> 0 < n ->
    0 < range_step A off lo n /\ (range_step A off lo n | eval nu off - lo).
  Proof.
    intros HL Hn. unfold range_step.
    pose proof (lin_cong_sound nu (scong (vs_store A)) off (sat_cong _ _ (lg_sat _ _ HL))) as HC.
    destruct (lin_cong (scong (vs_store A)) off) as [m0 r]. destruct HC as (D0&M0&_).
    set (m := if m0 =? 0 then TWO64 else m0).
    assert (Dm : (m | eval nu off - r) /\ 0 < m).
    { unfold m. destruct (Z.eqb_spec m0 0).
      - subst m0. apply Z.divide_0_l in D0. split; [rewrite D0; apply Z.divide_0_r|unfold TWO64; lia].
      - split; [exact D0|lia]. }
    destruct Dm as [Dm Pm]. clearbody m.
    destruct (Z.eqb (m mod n) 0 && Z.eqb ((lo - r) mod n) 0 && Z.ltb 1 n) eqn:E1.
    - apply andb_prop in E1 as [E1 _]. apply andb_prop in E1 as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
      split; [lia|]. apply Z.mod_divide in E1; [|lia]. apply Z.mod_divide in E2; [|lia].
      replace (eval nu off - lo) with ((eval nu off - r) - (lo - r)) by lia.
      apply Z.divide_sub_r; [eapply Z.divide_trans; [exact E1|exact Dm]|exact E2].
    - destruct (Z.ltb 1 m && Z.leb m n && Z.eqb ((lo - r) mod m) 0) eqn:E2.
      + apply andb_prop in E2 as [E2 E3]. apply Z.eqb_eq in E3. apply Z.mod_divide in E3; [|lia].
        split; [lia|]. replace (eval nu off - lo) with ((eval nu off - r) - (lo - r)) by lia.
        apply Z.divide_sub_r; [exact Dm|exact E3].
      + split; [lia|]. apply Z.divide_1_l.
  Qed.

  Lemma range_load_sound A nu regs mem off lo hi n sg vals :
    gammaP A nu regs mem -> 0 < n -> lo <= eval nu off <= hi ->
    range_load A off lo hi n sg = Some vals ->
    exists bs, rdn SEGS mem (wordZ (e_sp0 E + eval nu off)) (Z.to_nat n) = Some bs /\ length bs = Z.to_nat n
               /\ In (sign_adjust sg n (bytes_le_to_Z bs)) vals.
  Proof.
    intros HGm Hn Hx Hr. unfold range_load in Hr.
    pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    destruct (range_step_sound A nu off lo n HL Hn) as [Ps Ds].
    set (step := range_step A off lo n) in *. clearbody step.
    eapply (range_vals_sound (vs_slots A) nu mem (e_sp0 E) n step sg); [intros o w v Hin; exact (proj2 (HSl _ _ _ Hin))|exact Hn|exact Ps|exact Hr|].
    destruct Ds as [i Hi]. exists i.
    assert (Hi0 : 0 <= i) by nia.
    assert (His : i * step <= hi - lo) by lia.
    assert (Hik : i <= (hi - lo) / step) by (apply Z.div_le_lower_bound; lia).
    split; [rewrite Nat2Z.inj_succ, Z2Nat.id by (apply Z.div_pos; lia); lia|lia].
  Qed.

  Lemma fresh_valset_sound A nu v0 rest (rec : bool) y :
    lgamma A nu -> In y (v0 :: rest) ->
    res_word A nu (fresh_valset A v0 rest rec) (zwrap 64 y).
  Proof.
    intros HL Hin. unfold fresh_valset.
    set (mn := list_min rest v0). set (mx := list_max rest v0).
    assert (Hy : in_itv y (Some mn, Some mx)).
    { split; cbn [fst snd lo_le hi_ge].
      - apply list_min_le. destruct Hin as [<-|Hin']; auto.
      - apply list_max_ge. destruct Hin as [<-|Hin']; auto. }
    pose proof (fresh_sym_box_sound A nu (Some mn, Some mx) y HL Hy) as FS.
    destruct (fresh_sym A) as [s A1].
    destruct FS as (X1&L2&V2&S2&N2).
    set (A2 := asetbox A1 s (Some mn, Some mx)) in *.
    set (ds := zsort_dedup (v0 :: rest)).
    assert (L3 : lgamma (if rec then set_valset A2 (pm_set s ds (vs_valset A2)) else A2) (vupd nu s y)
                 /\ aext A2 (if rec then set_valset A2 (pm_set s ds (vs_valset A2)) else A2) (vupd nu s y) (vupd nu s y)
                 /\ vs_next (if rec then set_valset A2 (pm_set s ds (vs_valset A2)) else A2) = vs_next A2).
    { destruct rec.
      - destruct (lgamma_add_valset A2 (vupd nu s y) s ds L2) as [L XX]; [rewrite V2; apply zsort_dedup_in; exact Hin|exact S2|].
        split; [exact L|]. split; [exact XX|reflexivity].
      - split; [exact L2|]. split; [apply aext_refl|reflexivity]. }
    destruct L3 as (L3&X3&N3).
    exists (vupd nu s y). split; [eapply aext_trans; [exact X1|exact X3]|]. split; [exact L3|].
    split; [rewrite eval_lsym, V2; reflexivity|]. apply lin_below_lsym. rewrite N3. exact S2.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="PO"] Lemma load_val_sound A nu regs mem r addr n sg :
    gammaP A nu regs mem -> 0 < n <= 8 -> lin_below addr (vs_next A) = true ->
    classify P A addr n false = COk r ->
    exists bs, rdn SEGS mem (wordZ (zwrap 64 (eval nu addr))) (Z.to_nat n) = Some bs /\
               res_word A nu (load_val P A r addr n sg) (ldval sg n (bytes_le_to_Z bs)).
  Proof.
    intros HGm Hn Baddr Hcl.
    pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    pose proof HB as (B10&B11&B12&B13&B14&B15).
    pose proof PO as (P0&P1&PS&PF&PW&PR&PP&PB).
    pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12).
    assert (Hkn : Z.of_nat (Z.to_nat n) = n) by lia.
    (* [comment removed for export] *)
    assert (FRESH : forall bs, length bs = Z.to_nat n ->
              res_word A nu (fresh_loaded A n sg) (ldval sg n (bytes_le_to_Z bs))).
    { intros bs Hlen. apply fresh_loaded_sound; [exact HL|lia|].
      pose proof (bytes_le_to_Z_bound bs) as X. rewrite Hlen, Hkn in X. pose proof (bytes_le_to_Z_nonneg bs). lia. }
    destruct r as [off lo hi|off|lo hi].
    - (* [comment removed for export] *)
      destruct (classify_stack_sound P E A nu addr n false off lo hi HL HF ltac:(lia) Hcl) as (Eoff&Ea&Hlh&Hf1&Hf2&_).
      assert (Hid : zwrap 64 (eval nu addr) = eval nu addr) by (apply zwrap_id; lia). rewrite Hid, Ea.
      destruct (frame_bytes mem (e_sp0 E + eval nu off) (Z.to_nat n) HE HM ltac:(lia) ltac:(lia)) as [bs [Hbs Hlen]].
      cbn [load_val].
      destruct (Z.eqb_spec lo hi) as [Elh|Nlh].
      2: { (* [comment removed for export] *)
        destruct (Z.leb (hi - lo) 64) eqn:E64; [|exists bs; eauto].
        destruct (range_load A off lo hi n sg) as [[|v0 rest]|] eqn:Erl; [exists bs; eauto| |exists bs; eauto].
        destruct (range_load_sound A nu regs mem off lo hi n sg (v0 :: rest) HGm ltac:(lia) ltac:(lia) Erl) as [bs' (Hbs'&Hl'&Hin)].
        exists bs'. split; [exact Hbs'|].
        pose proof (bytes_le_to_Z_bound bs') as X. rewrite Hl', Hkn in X. pose proof (bytes_le_to_Z_nonneg bs') as X0.
        rewrite ldval_sign_adjust by (ltac2:(LK.k [@Hn; @E3; @E7; @E8; @E9; @E11; @Hkn; @Hlen; @Hl'; @E4; @E5; @X; @X0]); lia). set (y := sign_adjust sg n (bytes_le_to_Z bs')) in *.
        destruct (all_eq rest v0) eqn:Eall.
        * assert (Ey : y = v0).
          { destruct Hin as [<-|Hin]; [reflexivity|]. exact (all_eq_sound _ _ _ Eall Hin). }
          apply res_word_same; [exact HL|now rewrite eval_lconst, Ey|apply lin_below_lconst].
        * apply fresh_valset_sound; [exact HL|exact Hin]. }
      assert (Eo : eval nu off = lo) by lia. rewrite Eo in *.
      destruct (cm_get (vs_slots A) lo) as [[w [v|]]|] eqn:Ecm.
      + (* [comment removed for export] *)
        apply cm_get_in in Ecm. destruct (HSl _ _ _ Ecm) as [(R1&R2&R3) CH]. cbn [cell_holds] in CH.
        destruct CH as [bs' [Hbs' Hval]]. pose proof (B13 _ _ _ Ecm) as Bv.
        pose proof (rdn_length _ _ _ _ _ Hbs') as Hlen'.
        destruct (Z.eqb_spec w n) as [->|Nw].
        * exists bs'. split; [exact Hbs'|]. apply areinterp_sound; auto.
        * destruct (Z.ltb_spec n w).
          -- exists (firstn (Z.to_nat n) bs'). split; [eapply rdn_firstn; [exact Hbs'|lia]|].
             apply atruncate_sound; auto. rewrite bytes_le_firstn by lia. rewrite Hkn, Hval.
             change (zwrap (8 * w) (eval nu v) mod 2 ^ (8 * n)) with (zwrap (8 * n) (zwrap (8 * w) (eval nu v))).
             apply zwrap_zwrap. lia.
          -- exists bs. eauto.
      + (* [comment removed for export] *)
        destruct (const_cover (vs_slots A) lo n) as [c|] eqn:Ecc; [|exists bs; eauto].
        destruct (const_cover_sound (vs_slots A) nu mem (e_sp0 E) lo n c
                    ltac:(intros oo ww vv Hc0; exact (proj2 (HSl _ _ _ Hc0))) ltac:(lia) Ecc) as [bs' (Hbs'&Hl'&Hv'&Hc)].
        exists bs'. split; [exact Hbs'|]. rewrite Hv'. rewrite ldval_sign_adjust by lia.
        apply res_word_same; [exact HL|now rewrite eval_lconst|apply lin_below_lconst].
      + destruct (const_cover (vs_slots A) lo n) as [c|] eqn:Ecc; [|exists bs; eauto].
        destruct (const_cover_sound (vs_slots A) nu mem (e_sp0 E) lo n c
                    ltac:(intros oo ww vv Hc0; exact (proj2 (HSl _ _ _ Hc0))) ltac:(lia) Ecc) as [bs' (Hbs'&Hl'&Hv'&Hc)].
        exists bs'. split; [exact Hbs'|]. rewrite Hv'. rewrite ldval_sign_adjust by lia.
        apply res_word_same; [exact HL|now rewrite eval_lconst|apply lin_below_lconst].
    - (* [comment removed for export] *)
      destruct (classify_data_sound P E A nu addr n false off HL HF Hcl) as (_&Ea&Ho1&Ho2).
      assert (Hid : zwrap 64 (eval nu addr) = eval nu addr) by (apply zwrap_id; lia). rewrite Hid, Ea.
      destruct (data_bytes mem (e_data E + eval nu off) (Z.to_nat n) HE HM ltac:(lia) ltac:(lia)) as [bs [Hbs Hlen]].
      exists bs. split; [exact Hbs|]. cbn [load_val]. apply FRESH. exact Hlen.
    - (* [comment removed for export] *)
      destruct (classify_img_sound P A nu addr n false lo hi HL Hcl) as (Hlh&_&Hsg).
      specialize (Hsg eq_refl). destruct (in_ranges_sound _ _ _ Hsg) as [slo [shi (Hsin&Q1&Q2)]].
      destruct (PS _ _ Hsin) as (S0&S1&SB).
      assert (Hid : zwrap 64 (eval nu addr) = eval nu addr) by (apply zwrap_id; lia). rewrite Hid.
      destruct (seg_bytes mem (eval nu addr) (Z.to_nat n) slo shi HE Hsin ltac:(lia) ltac:(lia)) as [bs [Hbs Hlen]].
      cbn [load_val].
      destruct (Z.eqb_spec lo hi) as [Elh|Nlh].
      + assert (Eaddr : eval nu addr = lo) by lia. rewrite Eaddr in *.
        destruct (cm_get (vs_globs A) lo) as [[w [v|]]|] eqn:Ecm.
        * apply cm_get_in in Ecm. destruct (HG _ _ _ Ecm) as [(R1&R2&R3) CH]. cbn [cell_holds] in CH.
          destruct CH as [bs' [Hbs' Hval]]. pose proof (B14 _ _ _ Ecm) as Bv.
          destruct (Z.eqb_spec w n) as [->|Nw]; [|exists bs; eauto].
          exists bs'. split; [exact Hbs'|]. apply areinterp_sound; auto.
        * exists bs; eauto.
        * destruct (cm_overlapping (vs_globs A) lo (lo + n)); [|exists bs; eauto].
          destruct (in_ranges (vp_pristine P) lo n) eqn:Epr; [|exists bs; eauto].
          destruct (rom_read (vp_rom P) lo (Z.to_nat n)) as [v|] eqn:Er; [|exists bs; eauto].
          destruct (rom_read_sound mem lo (Z.to_nat n) v HE HM) as [bs' (Hbs'&Hv&Hl')].
          { apply (pristine_cover lo n); auto; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Hkn; @Hlen; @E4; @E5]); lia). }
          { exact Er. }
          exists bs'. split; [exact Hbs'|]. rewrite Hv.
          pose proof (bytes_le_to_Z_bound bs') as X. rewrite Hl', Hkn in X. pose proof (bytes_le_to_Z_nonneg bs') as X0.
          rewrite <- Hv. rewrite ldval_sign_adjust by (ltac2:(LK.k [@Hn; @E3; @E7; @E8; @E9; @E11; @Hkn; @Hlen; @Hl'; @E4; @E5; @X; @X0]); lia).
          apply res_word_same; [exact HL|now rewrite eval_lconst|apply lin_below_lconst].
      + destruct (in_ranges (vp_pristine P) lo (hi - lo + n)) eqn:Epr; [|exists bs; eauto].
        destruct (table_values P A addr n sg) as [[|v0 rest]|] eqn:Et; [exists bs; eauto| |exists bs; eauto].
        destruct (table_values_sound A nu mem addr n sg (v0 :: rest) lo (hi - lo + n) HL HE HM Hn Epr ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hkn; @Hlh; @Hlen]); lia)) ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hkn; @Hlh; @Hlen]); lia)) Et)
          as [bs' (Hbs'&Hl'&Hin)].
        exists bs'. split; [exact Hbs'|].
        pose proof (bytes_le_to_Z_bound bs') as X. rewrite Hl', Hkn in X. pose proof (bytes_le_to_Z_nonneg bs') as X0.
        rewrite ldval_sign_adjust by (ltac2:(LK.k [@Hn; @E3; @E7; @E8; @E9; @E11; @Hkn; @Hlen; @Hl'; @E4; @E5; @X; @X0]); lia). set (y := sign_adjust sg n (bytes_le_to_Z bs')) in *.
        destruct rest as [|v1 rest'].
        * assert (Ey : y = v0) by (destruct Hin as [<-|[]]; reflexivity).
          apply res_word_same; [exact HL|now rewrite eval_lconst, Ey|apply lin_below_lconst].
        * apply fresh_valset_sound; [exact HL|exact Hin].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma x_load_eq A sz sg rd rs1 imm :
    x_load P A sz sg rd rs1 imm =
    if (match sz with SZ8 => negb sg | _ => false end) then VR_fail "ld: unexpected unsigned form"
    else match addr_of A rs1 imm with
         | None => VR_fail "load via Top address"
         | Some addr =>
             match classify P A addr (msize_z sz) false with
             | CDead => VR_next []
             | CFail m => VR_fail m
             | COk r => let '(v, A1) := load_val P A r addr (msize_z sz) sg in one (finish A1 rd v)
             end
         end.
  Proof. destruct sz, sg; reflexivity. Qed.

  Lemma set_reg_0 A v : set_reg A 0 v = A.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma step_post_res0 A nu regs mem pc rom u (rA : absval * vstate) :
    gammaP A nu regs mem -> res_word A nu rA u ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom) ->
    vs_pc A = bv_unsigned pc ->
    step_post SEGS P E mem0 A nu [let '(v, A1) := rA in finish A1 0 v] regs mem pc rom.
  Proof.
    intros HGm HR Hstep Hpc. destruct rA as [v A1]. destruct HR as [nu1 (HX&HL1&_)].
    exists regs, (v_addi pc 4), mem, (finish A1 0 v), nu1.
    split; [exact Hstep|]. split; [left; reflexivity|].
    unfold finish. rewrite set_reg_0.
    split.
    { unfold npc_of. cbn [vs_pc set_pc]. destruct HX as (_&_&(_&_&_&_&SP&_)). rewrite SP, Hpc.
      unfold v_addi. rewrite u_Z_to_bv64. apply wrap64_zwrap. }
    split; [exact (proj1 HX)|]. split; [cbn [vs_next set_pc]; exact (proj1 (proj2 HX))|].
    split; [apply frame_mod_refl|]. eapply gamma_keep; eauto.
  Qed.

  Theorem x_load_sound A nu regs mem pc rom w sz sg (rd rs1 : reg) (imm : bv 12) succs :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load sz sg rd rs1 imm, 4) ->
    x_load P A sz sg (rz rd) (rz rs1) (bv_signed imm) = VR_next succs ->
    step_post SEGS P E mem0 A nu succs regs mem pc rom.
  Proof.
    intros HGm Hpc Hf He Hd Hx. rewrite x_load_eq in Hx.
    pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    destruct (match sz with SZ8 => negb sg | _ => false end) eqn:Eg; [discriminate|].
    assert (Hsz : sz = SZ8 -> sg = true) by (intros ->; destruct sg; [reflexivity|discriminate]).
    pose proof (msize_pos sz) as Hn. set (n := msize_z sz) in *.
    destruct (addr_of A (rz rs1) (bv_signed imm)) as [addr|] eqn:Ea; [|discriminate].
    destruct (addr_of_sound SEGS P E mem0 A nu regs mem rs1 (bv_signed imm) addr HGm Ea) as [Baddr Ua].
    destruct (classify P A addr n false) as [r| |m] eqn:Ecl; [|exfalso; exact (classify_not_dead P A nu addr n false HL Ecl)|discriminate].
    destruct (load_val_sound A nu regs mem r addr n sg HGm Hn Baddr Ecl) as [bs [Hbs HRW]].
    rewrite <- Ua, wordZ_u in Hbs.
    destruct (step_load_any SEGS mem0 regs pc mem rom w sz sg rd rs1 imm bs Hf He Hd Hsz Hbs) as [wl [Hwl Hstep]].
    destruct (load_val P A r addr n sg) as [v A1] eqn:Elv. cbn [one] in Hx. inversion Hx; subst; clear Hx.
    destruct (Z.eqb (rz rd) 0) eqn:Erd.
    - assert (Hbe : bv_eqb rd 0%bv = true) by (rewrite bv_eqb_rz; exact Erd). rewrite Hbe in Hstep.
      apply Z.eqb_eq in Erd. rewrite Erd.
      apply (step_post_res0 A nu regs mem pc rom (bv_unsigned wl) (v, A1)); auto. rewrite Hwl. exact HRW.
    - assert (Hbe : bv_eqb rd 0%bv = false) by (rewrite bv_eqb_rz; exact Erd). rewrite Hbe in Hstep.
      assert (Hrz : rz rd <> 0) by (intros X; rewrite X in Erd; discriminate).
      apply (step_post_res SEGS P E mem0 A nu regs mem pc rom rd wl (v, A1)); auto. rewrite Hwl. exact HRW.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem vstep_sound A nu regs mem pc rom w i succs :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    vstep P A i = VR_next succs ->
    step_post SEGS P E mem0 A nu succs regs mem pc rom.
  Proof.
    intros HGm Hpc Hf He Hd Hx.
    destruct (is_mem_instr i) eqn:Hm.
    - destruct i; try discriminate; cbn [vstep vstep_core] in Hx; rewrite ?bvs_eq in Hx.
      + eapply x_load_sound; eauto.
      + eapply x_store_sound; eauto.
    - eapply vstep_core_sound_nomem; eauto.
  Qed.
End Sound.
