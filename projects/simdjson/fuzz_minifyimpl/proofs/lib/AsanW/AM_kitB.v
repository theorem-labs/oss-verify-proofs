(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Mem Cells Step Frame Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg ABase ARep F_annot F_annot_sg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shlen_div8 : forall x, shlen x = x / 8.
Proof. intros x. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma granules_rup8 : forall n, 0 <= n -> shlen (rup8 n) = granules n.
Proof.
  intros n Hn. unfold granules, rup8, rdn8. rewrite !shlen_div8. Z.div_mod_to_equations. lia.
Qed.

Lemma granules_div : forall n, 0 <= n -> granules n = (n + 7) / 8.
Proof. intros n Hn. unfold granules. apply shlen_div8. Qed.

Lemma granules_cases : forall n, 0 <= n ->
  (n mod 8 = 0 -> granules n = n / 8) /\ (n mod 8 <> 0 -> granules n = n / 8 + 1) /\ 0 <= n / 8.
Proof. intros n Hn. rewrite granules_div by lia. repeat split; Z.div_mod_to_equations; lia. Qed.

Lemma granules_mono : forall k n, 0 <= k <= n -> granules k <= granules n.
Proof. intros k n H. rewrite !granules_div by lia. Z.div_mod_to_equations. lia. Qed.

Lemma granules_0 : granules 0 = 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma firstn_repeat : forall {A} (a : A) k n, (k <= n)%nat -> firstn k (repeat a n) = repeat a k.
Proof.
  intros A a k. induction k as [|k IH]; intros [|n] H; cbn; try reflexivity; [lia|]. f_equal. apply IH. lia.
Qed.
Lemma skipn_repeat : forall {A} (a : A) k n, skipn k (repeat a n) = repeat a (n - k).
Proof.
  intros A a k. induction k as [|k IH]; intros [|n]; cbn; try reflexivity. apply IH.
Qed.

Lemma length_bsb : forall n, 0 <= n -> length (block_shadow_bytes n) = Z.to_nat (granules n).
Proof.
  intros n Hn. unfold block_shadow_bytes. rewrite length_app, repeat_length, shlen_div8.
  pose proof (granules_cases n Hn) as (G0 & G1 & G2).
  destruct (Z.eqb_spec (n mod 8) 0) as [E|E]; cbn [length]; [rewrite (G0 E)| rewrite (G1 E)]; lia.
Qed.

(* [comment removed for export] *)
Definition vpat (n k : Z) : list byte :=
  block_shadow_bytes k ++ repeat (Z_to_bv 8 252) (Z.to_nat (granules n - granules k)).

Lemma vpat_tight : forall n, vpat n n = block_shadow_bytes n.
Proof. intros n. unfold vpat. rewrite Z.sub_diag. cbn. apply app_nil_r. Qed.

Lemma vpat_zero : forall n, vpat n 0 = repeat (Z_to_bv 8 252) (Z.to_nat (granules n)).
Proof. intros n. unfold vpat. rewrite granules_0, Z.sub_0_r. reflexivity. Qed.

Lemma length_vpat : forall n k, 0 <= k <= n -> length (vpat n k) = Z.to_nat (granules n).
Proof.
  intros n k H. unfold vpat. rewrite length_app, repeat_length, length_bsb by lia.
  pose proof (granules_mono k n H). pose proof (granules_mono 0 k ltac:(lia)) as G0. rewrite granules_0 in G0. lia.
Qed.

(* [comment removed for export] *)
Lemma bsb_shape : forall n, 0 <= n ->
  block_shadow_bytes n = repeat (Z_to_bv 8 0) (Z.to_nat (n / 8)) ++ (if n mod 8 =? 0 then [] else [Z_to_bv 8 (n mod 8)]).
Proof. intros n Hn. unfold block_shadow_bytes. rewrite shlen_div8. reflexivity. Qed.

Lemma firstn_repeat_app : forall {A} (x : A) a b l, (a <= b)%nat -> firstn a (repeat x b ++ l) = repeat x a.
Proof.
  intros A x a b l H. rewrite firstn_app, firstn_repeat by lia. rewrite repeat_length. replace (a - b)%nat with 0%nat by lia. cbn. apply app_nil_r.
Qed.
Lemma skipn_repeat_app : forall {A} (x : A) a b l, (a <= b)%nat -> skipn a (repeat x b ++ l) = repeat x (b - a) ++ l.
Proof. intros A x a b l H. rewrite skipn_app, skipn_repeat, repeat_length. replace (a - b)%nat with 0%nat by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sg_out_tight : forall n k, 0 <= k -> k < n -> sg_out (block_shadow_bytes n) k n = vpat n k.
Proof.
  intros n k K0 KN.
  pose proof (granules_cases n ltac:(lia)) as (Gn0 & Gn1 & Gn2). pose proof (granules_cases k ltac:(lia)) as (Gk0 & Gk1 & Gk2).
  pose proof (granules_mono k n ltac:(lia)) as GM.
  assert (SM : sg_mid (block_shadow_bytes n) k n
               = firstn (Z.to_nat (granules k)) (block_shadow_bytes n) ++ repeat (Z_to_bv 8 252) (Z.to_nat (granules n - granules k))).
  { unfold sg_mid. rewrite !granules_rup8 by lia. rewrite skipn_all2 by (rewrite length_bsb; lia). rewrite app_nil_r. reflexivity. }
  unfold sg_out. rewrite SM. clear SM. unfold vpat. rewrite (bsb_shape n) by lia. rewrite (bsb_shape k) by lia.
  (* [comment removed for export] *)
  destruct (Z.eqb_spec (k mod 8) 0) as [KM|KM]; cbv beta iota.
  - (* [comment removed for export] *)
    rewrite (Gk0 KM). rewrite firstn_repeat_app by lia. rewrite app_nil_r. reflexivity.
  - rewrite (Gk1 KM).
    destruct (Z_le_gt_dec (k / 8 + 1) (n / 8)) as [LE|GT].
    + (* [comment removed for export] *)
      rewrite (firstn_repeat_app _ (Z.to_nat (k / 8 + 1))) by lia.
      rewrite firstn_repeat_app by lia. rewrite skipn_repeat_app by lia.
      replace (Z.to_nat (k / 8 + 1) - (Z.to_nat (k / 8) + 1))%nat with 0%nat by lia. cbn [repeat app]. rewrite <- ?app_assoc. cbn [app]. reflexivity.
    + (* [comment removed for export] *)
      assert (KD : k / 8 = n / 8) by (Z.div_mod_to_equations; lia).
      assert (NM : n mod 8 <> 0) by (Z.div_mod_to_equations; lia).
      rewrite (Gn1 NM) in *. replace (n mod 8 =? 0) with false by (symmetry; apply Z.eqb_neq; exact NM).
      rewrite KD. rewrite Z.sub_diag. change (Z.to_nat 0) with 0%nat. cbn [repeat]. rewrite !app_nil_r.
      rewrite (firstn_all2 (n:=Z.to_nat (n / 8 + 1))) by (rewrite length_app, repeat_length; cbn; lia).
      rewrite firstn_repeat_app by lia. rewrite skipn_all2 by (rewrite length_app, repeat_length; cbn; lia).
      rewrite app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sg_out_clear : forall n k, 0 < k -> k <= n -> sg_out (vpat n k) 0 k = repeat (Z_to_bv 8 252) (Z.to_nat (granules n)).
Proof.
  intros n k K0 KN. pose proof (granules_mono k n ltac:(lia)) as GM. pose proof (granules_mono 0 k ltac:(lia)) as G0. rewrite granules_0 in G0.
  unfold sg_out. rewrite Z.mod_0_l by lia. rewrite Z.eqb_refl. cbv beta iota.
  unfold sg_mid. rewrite !granules_rup8 by lia. rewrite granules_0, Z.sub_0_r. change (Z.to_nat 0) with 0%nat.
  unfold vpat. rewrite skipn_app. rewrite length_bsb by lia. rewrite Nat.sub_diag. rewrite skipn_all2 by (rewrite length_bsb; lia).
  rewrite firstn_O, !skipn_O. cbn [app]. rewrite <- repeat_app. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma sg_out_tight_all : forall n, 0 < n -> sg_out (block_shadow_bytes n) 0 n = repeat (Z_to_bv 8 252) (Z.to_nat (granules n)).
Proof. intros n Hn. rewrite <- vpat_tight. apply sg_out_clear; lia. Qed.

(* [comment removed for export] *)
Lemma vpat_last : forall n k, 0 < k -> n mod 8 <> 0 -> rdn8 n < k -> k <= n ->
  nth_error (vpat n k) (Z.to_nat (n / 8)) = Some (Z_to_bv 8 (k mod 8)) /\ end_byte_ok n (Z_to_bv 8 (k mod 8)).
Proof.
  intros n k K0 NM RK KN. unfold rdn8 in RK.
  assert (KD : k / 8 = n / 8 /\ k mod 8 <> 0 /\ 0 < k mod 8 <= n mod 8 /\ n mod 8 < 8 /\ 0 <= n / 8) by (Z.div_mod_to_equations; lia).
  destruct KD as (KD & KM & KB & N8 & N0).
  split.
  - unfold vpat. rewrite (bsb_shape k) by lia. replace (k mod 8 =? 0) with false by (symmetry; apply Z.eqb_neq; exact KM).
    rewrite KD, <- app_assoc. rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length, Nat.sub_diag. reflexivity.
  - unfold end_byte_ok. rewrite sval_lit by lia. lia.
Qed.

Lemma bsb_last : forall n, 0 < n -> n mod 8 <> 0 ->
  nth_error (block_shadow_bytes n) (Z.to_nat (n / 8)) = Some (Z_to_bv 8 (n mod 8)) /\ end_byte_ok n (Z_to_bv 8 (n mod 8)).
Proof. intros n Hn NM. rewrite <- vpat_tight. apply vpat_last; [lia| exact NM| unfold rdn8; Z.div_mod_to_equations; lia| lia]. Qed.

(* [comment removed for export] *)
Lemma vpat_hsb : forall n k, 0 < k -> k <= n ->
  (n mod 8 <> 0 -> rdn8 n < k -> exists sb, nth_error (vpat n k) (Z.to_nat (n / 8)) = Some sb /\ end_byte_ok n sb).
Proof. intros n k K0 KN NM RK. exists (Z_to_bv 8 (k mod 8)). apply vpat_last; assumption. Qed.

Lemma bsb_hsb : forall n, 0 < n ->
  (n mod 8 <> 0 -> rdn8 n < n -> exists sb, nth_error (block_shadow_bytes n) (Z.to_nat (n / 8)) = Some sb /\ end_byte_ok n sb).
Proof. intros n Hn. rewrite <- vpat_tight. apply vpat_hsb; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bsb_cells_join : forall m S n, 0 < n ->
  rw_cells asegs m S [CB (Z.to_nat (n / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8)))] ->
  (n mod 8 <> 0 -> rw_cells asegs m (S + n / 8) [C1 (Z_to_bv 8 (n mod 8))]) ->
  rw_cells asegs m S [CB (Z.to_nat (granules n)) (block_shadow_bytes n)].
Proof.
  intros m S n Hn BODY LAST. pose proof (granules_cases n ltac:(lia)) as (G0 & G1 & G2). rewrite (bsb_shape n) by lia.
  destruct (Z.eqb_spec (n mod 8) 0) as [E|E].
  - rewrite (G0 E), app_nil_r. exact BODY.
  - rewrite (G1 E). specialize (LAST E).
    pose proof (CB_byte_join m S (Z.to_nat (n / 8) + 1) (Z.to_nat (n / 8)) _ (Z_to_bv 8 (n mod 8)) [] BODY) as J.
    rewrite Z2Nat.id in J by lia. rewrite app_nil_r in J. replace (Z.to_nat (n / 8 + 1)) with (Z.to_nat (n / 8) + 1)%nat by lia.
    apply J; [exact LAST| | lia].
    replace (Z.to_nat (n / 8) + 1 - Z.to_nat (n / 8) - 1)%nat with 0%nat by lia.
    (* [comment removed for export] *)
    destruct LAST as [[_ (L0 & L1 & _)] _]. cbn [cells_bytes cbytes app length] in L1.
    split; [split; [cbn; split; [reflexivity| exact I]|]|].
    + cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    + cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma CB_pointwise : forall m S G bs i, rw_cells asegs m S [CB G bs] -> 0x6c7000 <= S -> (i < G)%nat ->
  m (wa (S + Z.of_nat i)) = nth_error bs i.
Proof.
  intros m S G bs i [[WF (B0 & B1 & BB)] _] HS Hi. cbn in WF. destruct WF as [WF _].
  cbn [cells_bytes cbytes app] in B1, BB. rewrite app_nil_r in B1, BB.
  rewrite <- (BB i ltac:(lia)). symmetry. apply ref_mrd_overlay. right. rewrite wa_unsigned by lia. lia.
Qed.

Lemma ablock_shadow_of_cells : forall m A n, 0 < n -> 0 <= A ->
  rw_cells asegs m (shad A) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)] -> ablock_shadow m A n.
Proof.
  intros m A n Hn HA H g Hg0 Hg.
  pose proof (granules_cases n ltac:(lia)) as (G0 & G1 & G2).
  assert (SA : 0x6c7000 <= shad A) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
  assert (GL : g < granules n) by (rewrite granules_div by lia; Z.div_mod_to_equations; lia).
  replace g with (Z.of_nat (Z.to_nat g)) at 1 by lia. rewrite (CB_pointwise m (shad A) _ _ (Z.to_nat g) H SA) by lia.
  rewrite (bsb_shape n) by lia.
  destruct (Z_lt_le_dec g (n / 8)) as [LT|GE].
  - rewrite nth_error_app1 by (rewrite repeat_length; lia). rewrite nth_error_repeat by lia.
    replace (8 * g + 8 <=? n) with true by (symmetry; apply Z.leb_le; Z.div_mod_to_equations; lia). reflexivity.
  - assert (E : g = n / 8 /\ n mod 8 <> 0) by (Z.div_mod_to_equations; lia). destruct E as [-> NM].
    rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length, Nat.sub_diag.
    replace (n mod 8 =? 0) with false by (symmetry; apply Z.eqb_neq; exact NM). cbn [nth_error].
    replace (8 * (n / 8) + 8 <=? n) with false by (symmetry; apply Z.leb_gt; Z.div_mod_to_equations; lia).
    do 2 f_equal. Z.div_mod_to_equations; lia.
Qed.

Lemma cells_of_ablock_shadow : forall m A n, 0 < n -> 0 <= A -> A + n <= 2^47 ->
  ablock_shadow m A n -> rw_cells asegs m (shad A) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)].
Proof.
  intros m A n Hn HA HE BSH.
  pose proof (granules_cases n ltac:(lia)) as (G0 & G1 & G2). pose proof (length_bsb n ltac:(lia)) as LEN.
  assert (SA : 0x6c7000 <= shad A /\ shad A + granules n <= 2^64) by (rewrite shad_div, granules_div by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
  assert (BY : forall i, (i < Z.to_nat (granules n))%nat -> m (wa (shad A + Z.of_nat i)) = nth_error (block_shadow_bytes n) i).
  { intros i Hi. rewrite (BSH (Z.of_nat i)) by (try lia; rewrite granules_div in Hi by lia; Z.div_mod_to_equations; lia).
    rewrite (bsb_shape n) by lia.
    destruct (Z_lt_le_dec (Z.of_nat i) (n / 8)) as [LT|GE].
    - rewrite nth_error_app1 by (rewrite repeat_length; lia). rewrite nth_error_repeat by lia.
      replace (8 * Z.of_nat i + 8 <=? n) with true by (symmetry; apply Z.leb_le; Z.div_mod_to_equations; lia). reflexivity.
    - assert (E : Z.of_nat i = n / 8 /\ n mod 8 <> 0) by (rewrite granules_div in Hi by lia; Z.div_mod_to_equations; lia). destruct E as [E NM].
      rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length. replace (i - Z.to_nat (n / 8))%nat with 0%nat by lia.
      replace (n mod 8 =? 0) with false by (symmetry; apply Z.eqb_neq; exact NM). cbn [nth_error].
      replace (8 * Z.of_nat i + 8 <=? n) with false by (symmetry; apply Z.leb_gt; Z.div_mod_to_equations; lia).
      do 2 f_equal. Z.div_mod_to_equations; lia. }
  split; [split|].
  - cbn. split; [exact LEN| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. split; [lia|]. split; [rewrite LEN; lia|].
    intros i Hi. rewrite LEN in Hi. unfold mrd. rewrite (BY i Hi).
    destruct (nth_error (block_shadow_bytes n) i) eqn:NE; [reflexivity|]. exfalso. apply nth_error_None in NE. lia.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia. unfold wview. rewrite (BY (Z.to_nat i)) by lia.
    destruct (nth_error (block_shadow_bytes n) (Z.to_nat i)) eqn:NE; [discriminate|]. exfalso. apply nth_error_None in NE. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma munch_unwrite : forall W m m' S hi G (bs : list byte),
  munch ((S, hi) :: W) m m' -> hi <= S + Z.of_nat G ->
  rw_cells asegs m S [CB G bs] -> rw_cells asegs m' S [CB G bs] ->
  0x6c7000 <= S -> S + Z.of_nat G <= 2^64 ->
  munch W m m'.
Proof.
  intros W m m' S hi G bs MU HI H H' HS HE x Hx. pose proof (bv_unsigned_in_range 64 x) as RX.
  destruct (Z_le_gt_dec S (bv_unsigned x)) as [L1|L1]; [destruct (Z_lt_ge_dec (bv_unsigned x) (S + Z.of_nat G)) as [L2|L2]|].
  - rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)).
    replace (bv_unsigned x) with (S + Z.of_nat (Z.to_nat (bv_unsigned x - S))) by lia.
    rewrite (CB_pointwise m S G bs _ H HS) by lia. rewrite (CB_pointwise m' S G bs _ H' HS) by lia. reflexivity.
  - apply MU. cbn [outside]. split; [lia| exact Hx].
  - apply MU. cbn [outside]. split; [lia| exact Hx].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sh3_pointwise : forall m V i, rw_cells asegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  0 <= V -> 0 <= i < 3 -> m (wa (shad V + i)) = Some (Z_to_bv 8 0).
Proof.
  intros m V i [[WF (B0 & B1 & BB)] _] HV Hi. cbn [cells_bytes cbytes app length] in B1, BB.
  assert (SA : 0x6c7000 <= shad V) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
  replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite <- (ref_mrd_overlay m) by (right; rewrite wa_unsigned by lia; lia).
  rewrite (BB (Z.to_nat i)) by lia.
  assert (C : Z.to_nat i = 0%nat \/ Z.to_nat i = 1%nat \/ Z.to_nat i = 2%nat) by lia. destruct C as [->|[->| ->]]; reflexivity.
Qed.

Lemma sh3_unpoisoned : forall m V, rw_cells asegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> 0 <= V -> V + 24 <= 2^47 -> unpoisoned m V (V + 24).
Proof.
  intros m V H V8 V0 VH. split; [lia|]. split; [lia|]. intros G _ G1 G2.
  exists (Z_to_bv 8 0). split; [| left; apply sval_zero].
  replace (ASHOFF + G) with (shad V + (G - V / 8)) by (rewrite shad_div; lia).
  apply sh3_pointwise; [exact H| lia| Z.div_mod_to_equations; lia].
Qed.

(* [comment removed for export] *)
Lemma vec3_as_CB : forall m V (a b c : word), rw_cells asegs m V [C8 a; C8 b; C8 c] -> rw_cells asegs m V [CB 24 (le8 a ++ le8 b ++ le8 c)].
Proof.
  intros m V a b c H. eapply rw_cells_recast; [exact H| | |]; cbn; repeat split; reflexivity.
Qed.
Lemma vec3_of_zeros : forall m V, rw_cells asegs m V [CB 24 (repeat (Z_to_bv 8 0) 24)] ->
  rw_cells asegs m V [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  intros m V H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity].
Qed.
End CANSEC1.
