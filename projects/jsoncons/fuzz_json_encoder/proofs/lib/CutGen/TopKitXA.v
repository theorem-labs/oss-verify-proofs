(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim StoreOk ShapeAlg SpinAlg Hoare AsanAcct HeapIface HeapIfaceA L5Defs L5Core PmHeapIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5 CutL5A.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module TKA.
Definition mem := (word -> option byte).

Lemma land1_even : forall k, Z.land (2 * k) 1 = 0.
Proof. intros k. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. rewrite Z.mul_comm. apply Z.mod_mul. discriminate. Qed.
Lemma land1_odd : forall w, Z.testbit w 0 = true -> Z.land w 1 = 1.
Proof. intros w H. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2 ^ 1) with 2. rewrite <- Z.bit0_mod. rewrite H. reflexivity. Qed.
Lemma land1_odd_low : forall w, Z.testbit w 0 = true -> Z.land (w mod 256) 1 = 1.
Proof.
  intros w H. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2 ^ 1) with 2. rewrite <- Z.bit0_mod.
  change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by lia. rewrite H. reflexivity.
Qed.
Lemma str_cap_facts : forall n, 23 <= n -> n < 2 ^ 26 ->
  PML.str_cap n = (if Z.eqb n 23 then 26 else 8 * (n / 8) + 8) /\ n < PML.str_cap n <= n + 8 /\ Z.testbit (PML.str_cap n + 1) 0 = true /\ 0 < PML.str_cap n <= 2 ^ 27.
Proof.
  intros n Hn Hn26. unfold PML.str_cap. rewrite CL5.lor7 by lia. pose proof (Z.div_mod n 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as B.
  set (q := n / 8) in *.
  assert (E23 : (8 * q + 7 =? 23) = (n =? 23)).
  { destruct (Z.eqb_spec n 23) as [E|NE]; [apply Z.eqb_eq; subst n; subst q; reflexivity|]. apply Z.eqb_neq. intros X. assert (q = 2) by lia. lia. }
  rewrite E23. destruct (Z.eqb_spec n 23) as [E|NE].
  - subst n. repeat split; try lia; try reflexivity.
  - split; [lia|]. split; [lia|]. split; [|lia]. rewrite Z.bit0_odd. replace (8 * q + 7 + 1 + 1) with (1 + 2 * (4 * q + 4)) by lia. rewrite Z.odd_add_mul_2. reflexivity.
Qed.
Lemma copy_cap_facts : forall n, 0 <= n -> n < PML.copy_cap n <= Z.max n 44 + 8 /\ PML.copy_cap n mod 8 = 0 /\ Z.testbit (PML.copy_cap n + 1) 0 = true /\
  PML.copy_cap n = 8 * (Z.max n 44 / 8) + 8.
Proof.
  intros n Hn. unfold PML.copy_cap. rewrite CL5.lor7 by lia. pose proof (Z.div_mod (Z.max n 44) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (Z.max n 44) 8 ltac:(lia)) as B.
  set (q := Z.max n 44 / 8) in *. split; [lia|]. split; [|split; [|lia]].
  - replace (8 * q + 7 + 1) with ((q + 1) * 8) by lia. apply Z_mod_mult.
  - rewrite Z.bit0_odd. replace (8 * q + 7 + 1 + 1) with (1 + 2 * (4 * q + 4)) by lia. rewrite Z.odd_add_mul_2. reflexivity.
Qed.

Section Pure.
Variable segs : list Segment.

Lemma u8_inj : forall (M : mem) a x y, L5.u8_at segs M a x -> L5.u8_at segs M a y -> 0 <= x < 256 -> 0 <= y < 256 -> x = y.
Proof.
  intros M a x y Hx Hy Rx Ry. unfold L5.u8_at in *. rewrite Hx in Hy.
  assert (E : Z_to_bv 8 x = Z_to_bv 8 y) by congruence. pose proof (f_equal bv_unsigned E) as E'.
  rewrite !Z_to_bv_unsigned in E'. unfold bv_wrap in E'. change (bv_modulus 8) with 256 in E'. rewrite !Z.mod_small in E' by lia. exact E'.
Qed.
Lemma u64_u8_low : forall (M : mem) a w, 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at segs M a w -> L5.u8_at segs M a (w mod 256).
Proof.
  intros M a w Ha Ha8 H. unfold L5.u64_at, L5.u8_at in *.
  assert (EQ : forall x n, rdn segs M x (Datatypes.S n) = match (match M x with Some b => Some b | None => seg_rom segs x end) with
                 | Some b => match rdn segs M (x + 1)%bv n with Some rest => Some (b :: rest) | None => None end | None => None end) by reflexivity.
  rewrite (EQ _ 7%nat) in H. rewrite (EQ _ 0%nat). cbn [rdn].
  destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 a) end) as [b0|] eqn:E0; [|discriminate].
  destruct (rdn segs M (Z_to_bv 64 a + 1)%bv 7) as [rest|] eqn:ER; [|discriminate].
  unfold word_to_le_bytes in H. cbn [Z_to_le_bytes] in H. injection H as H1 H2. f_equal. f_equal. rewrite H1. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. replace (2 ^ 64) with (256 * 2 ^ 56) by reflexivity. rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256), Z.mod_add by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma u64_of_defined : forall (M : mem) a, L5.defined M a 8 -> exists v, 0 <= v < 2 ^ 64 /\ L5.u64_at segs M a v.
Proof.
  intros M a Hd.
  assert (RD : forall (k : nat) b, (forall i, 0 <= i < Z.of_nat k -> M (Z_to_bv 64 (b + i)) <> None) -> exists bs, rdn segs M (Z_to_bv 64 b) k = Some bs /\ length bs = k).
  { induction k as [|k IH]; intros b H; [exists []; split; reflexivity|].
    destruct (IH (b + 1)) as (bs & Hr & Hl); [intros i Hi; replace (b + 1 + i) with (b + (1 + i)) by lia; apply H; lia|].
    pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (M (Z_to_bv 64 b)) as [x|] eqn:Hb; [|contradiction].
    exists (x :: bs). cbn [rdn]. rewrite Hb, L5C.add1_lit, Hr. split; [reflexivity | cbn [length]; lia]. }
  destruct (RD 8%nat a Hd) as (bs & Hr & Hl). exists (bytes_le_to_Z bs).
  pose proof (bytes_le_to_Z_nonneg bs) as N0. pose proof (bytes_le_to_Z_bound bs) as N1. rewrite Hl in N1. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in N1.
  split; [lia|]. unfold L5.u64_at. rewrite Hr. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Hl | lia].
Qed.
Lemma u64_copy_u8 : forall (M M' : mem) a b w k v, 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= b -> b + 8 <= 2 ^ 64 -> L5.u64_at segs M a w -> L5.u64_at segs M' b w -> 0 <= k < 8 ->
  L5.u8_at segs M (a + k) v -> L5.u8_at segs M' (b + k) v.
Proof.
  intros M M' a b w k v Ha Ha8 Hb Hb8 HA HB Hk Hv. unfold L5.u64_at in HA, HB. set (l := word_to_le_bytes 8 (Z_to_bv 64 w)) in *.
  assert (Ll : length l = 8%nat) by (unfold l, word_to_le_bytes; apply length_Z_to_le_bytes).
  pose proof (L5C.rdn_bytes_at segs M l a Ha ltac:(rewrite Ll; lia) ltac:(rewrite Ll; exact HA)) as BA.
  pose proof (L5C.rdn_bytes_at segs M' l b Hb ltac:(rewrite Ll; lia) ltac:(rewrite Ll; exact HB)) as BB.
  specialize (BA (Z.to_nat k) ltac:(rewrite length_map, Ll; lia)). specialize (BB (Z.to_nat k) ltac:(rewrite length_map, Ll; lia)). rewrite Z2Nat.id in BA, BB by lia.
  unfold L5.u8_at in *. rewrite BB, <- BA. exact Hv.
Qed.
(* [comment removed for export] *)
Lemma sso_copy : forall (M M' : mem) so d w0 w1 w2 s, 0 <= so -> so + 24 <= 2 ^ 64 -> 0 <= d -> d + 24 <= 2 ^ 64 ->
  L5.u64_at segs M so w0 -> L5.u64_at segs M (so + 8) w1 -> L5.u64_at segs M (so + 16) w2 -> L5.u64_at segs M' d w0 -> L5.u64_at segs M' (d + 8) w1 -> L5.u64_at segs M' (d + 16) w2 ->
  L5.lstr_short segs M so s -> L5.lstr_short segs M' d s.
Proof.
  intros M M' so d w0 w1 w2 s Hso Hso2 Hd Hd2 S0 S1 S2 D0 D1 D2 (Hlen & Hflag & Hbytes & Hnul).
  assert (CP : forall i v, 0 <= i < 24 -> L5.u8_at segs M (so + i) v -> L5.u8_at segs M' (d + i) v).
  { intros i v Hi Hv. destruct (Z_lt_le_dec i 8) as [I8|I8]; [exact (u64_copy_u8 M M' so d w0 i v Hso ltac:(lia) Hd ltac:(lia) S0 D0 ltac:(lia) Hv)|].
    destruct (Z_lt_le_dec i 16) as [I16|I16].
    - replace (d + i) with (d + 8 + (i - 8)) by lia. apply (u64_copy_u8 M M' (so + 8) (d + 8) w1 (i - 8) v); [lia | lia | lia | lia | exact S1 | exact D1 | lia|].
      replace (so + 8 + (i - 8)) with (so + i) by lia. exact Hv.
    - replace (d + i) with (d + 16 + (i - 16)) by lia. apply (u64_copy_u8 M M' (so + 16) (d + 16) w2 (i - 16) v); [lia | lia | lia | lia | exact S2 | exact D2 | lia|].
      replace (so + 16 + (i - 16)) with (so + i) by lia. exact Hv. }
  split; [exact Hlen|]. split; [rewrite <- (Z.add_0_r d); apply CP; [lia | rewrite Z.add_0_r; exact Hflag]|].
  split.
  - intros j Hj. replace (d + 1 + Z.of_nat j) with (d + (1 + Z.of_nat j)) by lia. apply CP; [lia|]. replace (so + (1 + Z.of_nat j)) with (so + 1 + Z.of_nat j) by lia. exact (Hbytes j Hj).
  - replace (d + 1 + Z.of_nat (length s)) with (d + (1 + Z.of_nat (length s))) by lia. apply CP; [lia|]. replace (so + (1 + Z.of_nat (length s))) with (so + 1 + Z.of_nat (length s)) by lia. exact Hnul.
Qed.
(* [comment removed for export] *)
Lemma sso_words : forall (M : mem) o s, 0 <= o -> o + 24 <= 2 ^ 64 -> L5.lstr_short segs M o s -> L5.defined M o 24 ->
  exists w0 w1 w2, 0 <= w0 < 2 ^ 64 /\ 0 <= w1 < 2 ^ 64 /\ 0 <= w2 < 2 ^ 64 /\ L5.u64_at segs M o w0 /\ L5.u64_at segs M (o + 8) w1 /\ L5.u64_at segs M (o + 16) w2 /\
    w0 mod 256 = 2 * Z.of_nat (length s).
Proof.
  intros M o s Ho Ho2 (Hlen & Hflag & _) D.
  destruct (u64_of_defined M o ltac:(eapply L5.defined_sub; [exact D | lia | lia])) as (w0 & Hw0 & C0).
  destruct (u64_of_defined M (o + 8) ltac:(eapply L5.defined_sub; [exact D | lia | lia])) as (w1 & Hw1 & C1).
  destruct (u64_of_defined M (o + 16) ltac:(eapply L5.defined_sub; [exact D | lia | lia])) as (w2 & Hw2 & C2).
  exists w0, w1, w2. repeat (split; [assumption|]).
  pose proof (u64_u8_low M o w0 Ho ltac:(lia) C0) as B. pose proof (Z.mod_pos_bound w0 256 ltac:(lia)) as Bm.
  apply (u8_inj M o _ _ B Hflag); lia.
Qed.
(* [comment removed for export] *)
Lemma bytes_of_copy : forall (M : mem) d (txt : list Z), (forall z, In z txt -> 0 <= z < 256) ->
  (forall i, 0 <= i < Z.of_nat (length txt) -> exists v, (nth_error (map (Z_to_bv 8) txt) (Z.to_nat i) = Some (Z_to_bv 8 v) /\ 0 <= v < 256) /\ byte_at M (d + i) v) ->
  L5.bytes_at segs M d txt.
Proof.
  intros M d txt Htxt H j Hj. destruct (H (Z.of_nat j) ltac:(lia)) as (v & (Hn & Hv) & Hb). rewrite Nat2Z.id in Hn.
  rewrite nth_error_map in Hn. destruct (nth_error txt j) as [z|] eqn:Hz; [|discriminate]. cbn [option_map] in Hn.
  pose proof (Htxt z (nth_error_In _ _ Hz)) as Rz. assert (E : v = z).
  { assert (Hn' : Z_to_bv 8 z = Z_to_bv 8 v) by congruence. pose proof (f_equal bv_unsigned Hn') as E'. rewrite !Z_to_bv_unsigned in E'. unfold bv_wrap in E'. change (bv_modulus 8) with 256 in E'. rewrite !Z.mod_small in E' by lia. lia. }
  subst v. rewrite (nth_error_nth _ _ _ Hz). apply CL5A.byte_at_u8. exact Hb.
Qed.
(* [comment removed for export] *)
Lemma rdn_of_bytes : forall (M : mem) (bs : list byte) a,
  (forall j, (j < length bs)%nat -> M (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) -> rdn segs M (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
  intros M bs. induction bs as [|b bs IH]; intros a H; [reflexivity|]. cbn [rdn length].
  pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn [Z.of_nat nth] in H0. rewrite Z.add_0_r in H0. rewrite H0, L5C.add1_lit, (IH (a + 1)); [reflexivity|].
  intros j Hj. replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (Datatypes.S j)) by lia. exact (H (Datatypes.S j) ltac:(cbn; lia)).
Qed.
Lemma u64_zero : forall (M : mem) a, (forall j, 0 <= j < 8 -> byte_at M (a + j) 0) -> L5.u64_at segs M a 0.
Proof.
  intros M a H. unfold L5.u64_at. change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 8).
  apply (rdn_of_bytes M (repeat (Z_to_bv 8 0) 8) a). intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. exact (H (Z.of_nat j) ltac:(lia)).
Qed.
Lemma u32_zero : forall (M : mem) a, (forall j, 0 <= j < 4 -> byte_at M (a + j) 0) -> L5.u32_at segs M a 0.
Proof.
  intros M a H. unfold L5.u32_at. change (word_to_le_bytes 4 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 4).
  apply (rdn_of_bytes M (repeat (Z_to_bv 8 0) 4) a). intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. exact (H (Z.of_nat j) ltac:(lia)).
Qed.
Lemma bytes_of_copy2 : forall (M : mem) d (txt : list Z),
  (forall i, 0 <= i < Z.of_nat (length txt) -> exists v, (nth_error (map (Z_to_bv 8) txt) (Z.to_nat i) = Some (Z_to_bv 8 v) /\ 0 <= v < 256) /\ byte_at M (d + i) v) ->
  L5.bytes_at segs M d txt.
Proof.
  intros M d txt H j Hj. destruct (H (Z.of_nat j) ltac:(lia)) as (v & (Hn & Hv) & Hb). rewrite Nat2Z.id in Hn.
  rewrite nth_error_map in Hn. destruct (nth_error txt j) as [z|] eqn:Hz; [|discriminate]. cbn [option_map] in Hn. assert (Hn' : Z_to_bv 8 z = Z_to_bv 8 v) by congruence.
  rewrite (nth_error_nth _ _ _ Hz). unfold L5.u8_at. unfold byte_at in Hb. cbn [rdn]. rewrite Hb, <- Hn'. reflexivity.
Qed.
End Pure.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Agree.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable IC : PMLA.consts.
Variables (M M' : mem) (S : Z -> Prop).
Hypothesis AG : forall a, S a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Hypothesis HS : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> 0 <= a < 2 ^ 63 /\ S a.
Hypothesis HF : forall a, PMLA.GLOC_GUARD IC <= a < PMLA.GLOC_GUARD IC + 1 \/ PMLA.GLOC_PTR IC <= a < PMLA.GLOC_PTR IC + 8 \/ PMLA.SYSCAT_GUARD IC <= a < PMLA.SYSCAT_GUARD IC + 2
             \/ PMLA.ERRCAT_GUARD IC <= a < PMLA.ERRCAT_GUARD IC + 2 \/ PMLA.ATEXIT_TAB IC <= a < PMLA.ATEXIT_TAB IC + 544 \/ a = PMLA.NEED_LOCKS IC
             \/ PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 -> PMLA.in_foot IC a.
Abbreviation segs := (hl_segs L).

Lemma OF : forall a n, 0 < n -> (forall i, a <= i < a + n -> PMLA.in_foot IC i) -> PTA.out S a n.
Proof.
  intros a n Hn Hi. destruct (HS a (or_intror (Hi a ltac:(lia)))) as ((X0 & _) & _). destruct (HS (a + n - 1) (or_intror (Hi (a + n - 1) ltac:(lia)))) as ((_ & X1) & _).
  split; [lia|]. split; [lia|]. intros i Hii. exact (proj2 (HS i (or_intror (Hi i Hii)))).
Qed.
Lemma U8 : forall a v, (forall i, a <= i < a + 1 -> PMLA.in_foot IC i) -> L5.u8_at segs M a v -> L5.u8_at segs M' a v.
Proof. intros a v Hf. apply (PTA.u8_ag segs M M' S AG). apply OF; [lia | exact Hf]. Qed.
Lemma U64 : forall a v, (forall i, a <= i < a + 8 -> PMLA.in_foot IC i) -> L5.u64_at segs M a v -> L5.u64_at segs M' a v.
Proof. intros a v Hf. apply (PTA.u64_ag segs M M' S AG). apply OF; [lia | exact Hf]. Qed.
Lemma CE : forall a (n : nat) v, (0 < n)%nat -> (forall i, a <= i < a + Z.of_nat n -> PMLA.in_foot IC i) -> cell_is segs M a n v -> cell_is segs M' a n v.
Proof. intros a n v Hn Hf. apply (PTA.cell_ag segs M M' S AG). apply OF; [lia | exact Hf]. Qed.
Lemma atexit_ok_ag : forall g, PMLA.atexit_ok segs IC M g -> PMLA.atexit_ok segs IC M' g.
Proof.
  intros g ((T1 & T2 & T3) & (Q1 & Q2)).
  assert (TAB : forall i, PMLA.ATEXIT_TAB IC <= i < PMLA.ATEXIT_TAB IC + 544 -> PMLA.in_foot IC i) by (intros i Hi; apply HF; do 4 right; left; lia).
  split.
  - split; [apply CE; [lia | intros ii Hii; apply TAB; lia | exact T1]|]. split; [apply CE; [lia | intros ii Hii; apply TAB; lia | exact T2]|].
    destruct (PMLA.HS0 IC ++ PMLA.ls_atexit IC g) as [|h0 hs] eqn:EH.
    + destruct T3 as (X & Y). split; [apply CE; [lia | intros ii Hii; apply TAB; lia | exact X]|].
      destruct Y as [Y|[Y1 Y2]]; [left; apply CE; [lia | intros ii Hii; apply TAB; lia | exact Y] | right; split; [apply CE; [lia | intros ii Hii; apply TAB; lia | exact Y1] | apply CE; [lia | intros ii Hii; apply TAB; lia | exact Y2]]].
    + destruct T3 as (X0 & X1 & X2 & X3 & X4). split; [exact X0|]. split; [apply CE; [lia | intros ii Hii; apply TAB; lia | exact X1]|]. split; [apply CE; [lia | intros ii Hii; apply TAB; lia | exact X2]|].
      split; [apply CE; [lia | intros ii Hii; apply TAB; lia | exact X3]|]. intros i f a Hn. destruct (X4 i f a Hn) as (Y1 & Y2).
      assert (Hi : Z.of_nat i < 32) by (pose proof (nth_error_Some (h0 :: hs) i) as G; rewrite Hn in G; assert ((i < length (h0 :: hs))%nat) by (apply G; discriminate); lia).
      split; [apply CE; [lia | intros ii Hii; apply TAB; lia | exact Y1] | apply CE; [lia | intros ii Hii; apply TAB; lia | exact Y2]].
  - split; [apply CE; [lia | intros i Hi; apply HF; do 5 right; left; lia | exact Q1] | apply CE; [lia | intros i Hi; apply HF; do 6 right; lia | exact Q2]].
Qed.
Lemma img_ro_ag : PMLA.img_ro IC M -> PMLA.img_ro IC M'.
Proof. apply (PTA.clear_ag M M' S AG). intros i Hi. exact (proj2 (HS i (or_introl Hi))). Qed.
Lemma gloc_done_ag : PMSA.gloc_done L IC M -> PMSA.gloc_done L IC M'.
Proof.
  intros (X & Y). unfold PMSA.u8, PMSA.u64 in *. split; [apply U8; [intros i Hi; apply HF; left; lia | exact X]|].
  apply U64; [intros i Hi; apply HF; right; left; lia | exact Y].
Qed.
Lemma errcat_guard_ag : forall b, PMLA.errcat_guard segs IC M b -> PMLA.errcat_guard segs IC M' b.
Proof. intros b (X & Y). unfold PMLA.u8 in *. split; apply U8; try assumption; intros i Hi; apply HF; do 3 right; left; lia. Qed.
Lemma statics_mid_ag : PMSA.statics_mid L IC M -> PMSA.statics_mid L IC M'.
Proof.
  intros (RO & GL & SY & EA). split; [exact (img_ro_ag RO)|]. split; [exact (gloc_done_ag GL)|]. unfold PMSA.u8 in *. split.
  - destruct SY as [(Y1 & Y2)|Y]; [left; split | right]; apply U8; try assumption; intros i Hi; apply HF; do 2 right; left; lia.
  - destruct EA as [(E1 & E2)|(E1 & E2)]; [left | right]; split; [exact (errcat_guard_ag _ E1) | exact (atexit_ok_ag _ E2) | exact (errcat_guard_ag _ E1) | exact (atexit_ok_ag _ E2)].
Qed.
Lemma ls0_ag : PMLA.ls_ok segs IC PML.LS0 M -> PMLA.ls_ok segs IC PML.LS0 M'.
Proof.
  intros (RO & AT & FP). split; [exact (img_ro_ag RO)|]. split; [exact (atexit_ok_ag _ AT)|].
  intros a Ha Ht Hn. rewrite (AG a (proj2 (HS a (or_intror Ha)))). exact (FP a Ha Ht Hn).
Qed.
Lemma ls0_or_mid_ag : (PMLA.ls_ok segs IC PML.LS0 M \/ PMSA.statics_mid L IC M) -> (PMLA.ls_ok segs IC PML.LS0 M' \/ PMSA.statics_mid L IC M').
Proof. intros [X|X]; [left; exact (ls0_ag X) | right; exact (statics_mid_ag X)]. Qed.
End Agree.

(* [comment removed for export] *)
Lemma island_mid : forall {SCFG_P : ScfgP} (L : asan_layout) IC (M : mem),
  PMSA.u8 L M (PMLA.GLOC_GUARD IC) 1 -> PMSA.u64 L M (PMLA.GLOC_PTR IC) (PMLA.CLASSIC_IMP IC) ->
  PMLA.errcat_guard (hl_segs L) IC M 0 -> PMLA.atexit_ok (hl_segs L) IC M PML.LS0 -> PMLA.img_ro IC M ->
  PMSA.u8 L M (PMLA.SYSCAT_GUARD IC) 0 -> PMSA.u8 L M (PMLA.SYSCAT_GUARD IC + 1) 0 -> PMSA.statics_mid L IC M.
Proof.
  intros SP L IC M G1 G2 EG AT RO S0 S1. split; [exact RO|]. split; [split; [exact G1 | exact G2]|]. split; [left; split; [exact S0 | exact S1]|].
  left. split; [exact EG | exact AT].
Qed.
End TKA.
