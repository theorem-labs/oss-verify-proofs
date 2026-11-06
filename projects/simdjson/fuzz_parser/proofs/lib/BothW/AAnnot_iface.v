(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase ABytes FsKit.
(* [comment removed for export] *)
Definition rdn8 (x : Z) : Z := x - x mod 8.
Definition rup8 (x : Z) : Z := rdn8 (x + 7).
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma ARepKit_firstn_repeat : forall {A} (x : A) k n, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof. intros A x k. induction k as [|k IH]; intros [|n] H; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity. Qed.
Lemma ARepKit_skipn_repeat : forall {A} (x : A) k n, skipn k (repeat x n) = repeat x (n - k).
Proof. intros A x k. induction k as [|k IH]; intros [|n]; cbn; try reflexivity. apply IH. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wr_at_sub' : forall m a n a' n', wr_at bsegs m a n -> 0 <= a -> a <= a' -> a' + n' <= a + n -> wr_at bsegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_rw_cells : forall m A n (f : Z -> Z),
  0 <= n -> wr_at bsegs m A n ->
  (forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 (f i))) ->
  rw_cells bsegs m A [CB (Z.to_nat n) (map (fun k => Z_to_bv 8 (f (Z.of_nat k))) (seq 0 (Z.to_nat n)))].
Proof.
  intros m A n f Hn W Hb. pose proof W as (W0 & W1 & W2).
  split; [split|].
  - cbn. rewrite length_map, length_seq. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite length_map, length_seq; lia|].
    intros i Hi. rewrite length_map, length_seq in Hi. unfold mrd. rewrite (Hb (Z.of_nat i)) by lia.
    rewrite nth_error_map, nth_error_seq. replace (PeanoNat.Nat.ltb i (Z.to_nat n)) with true by (symmetry; apply PeanoNat.Nat.ltb_lt; lia). cbn [option_map]. reflexivity.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact W.
Qed.

(* [comment removed for export] *)
Lemma ablock_shadow_chunks : forall m A n,
  0 < n -> A mod 8 = 0 -> 0 <= A ->
  ablock_shadow m A n -> wr_at bsegs m (shad A) (shlen (n + 7)) ->
  rw_cells bsegs m (shad A) [CB (Z.to_nat (n / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8)))]
  /\ (n mod 8 <> 0 -> rw_cells bsegs m (shad A + n / 8) [C1 (Z_to_bv 8 (n mod 8))]).
Proof.
  intros m A n Hn AL A0 SH W.
  assert (SL : shlen (n + 7) = (n + 7) / 8) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (S0 : 0 <= shad A) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  assert (DB : 0 <= n / 8 /\ 8 * (n / 8) <= n /\ n < 8 * (n / 8) + 8 /\ n / 8 <= (n + 7) / 8 /\ (n mod 8 <> 0 -> n / 8 + 1 <= (n + 7) / 8) /\ n mod 8 = n - 8 * (n / 8))
    by (Z.div_mod_to_equations; lia).
  destruct DB as (D1 & D2 & D3 & D4 & D5 & D6).
  split.
  - pose proof (bytes_rw_cells m (shad A) (n / 8) (fun _ => 0) D1
                 ltac:(eapply wr_at_sub'; [exact W| exact S0| lia| rewrite SL; lia])) as H.
    cbn beta in H. rewrite map_const, length_seq in H. apply H.
    intros i Hi. rewrite (SH i) by lia. f_equal. f_equal.
    replace (8 * i + 8 <=? n) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - intros NE.
    pose proof (bytes_rw_cells m (shad A + n / 8) 1 (fun _ => n mod 8) ltac:(lia)
                 ltac:(eapply wr_at_sub'; [exact W| exact S0| lia| rewrite SL; lia])) as H.
    cbn [Z.to_nat seq map Pos.to_nat Z.of_nat] in H.
    eapply rw_cells_recast; [apply H| cbn; tauto| reflexivity| reflexivity].
    intros i Hi. replace (shad A + n / 8 + i) with (shad A + n / 8) by lia. rewrite (SH (n / 8)) by lia. f_equal. f_equal.
    replace (8 * (n / 8) + 8 <=? n) with false by (symmetry; apply Z.leb_gt; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma chunks_ablock_shadow : forall m A n,
  0 < n -> A mod 8 = 0 -> 0 <= A -> A + n <= 2^47 ->
  rw_cells bsegs m (shad A) [CB (Z.to_nat (n / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8)))] ->
  (n mod 8 <> 0 -> rw_cells bsegs m (shad A + n / 8) [C1 (Z_to_bv 8 (n mod 8))]) ->
  ablock_shadow m A n.
Proof.
  intros m A n Hn AL A0 AH BODY LAST g Hg0 Hg.
  assert (S0 : 0x671000 <= shad A /\ shad A + n / 8 < 2^62) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  assert (DB : 0 <= n / 8 /\ 8 * (n / 8) <= n /\ n < 8 * (n / 8) + 8 /\ n mod 8 = n - 8 * (n / 8)) by (Z.div_mod_to_equations; lia).
  destruct DB as (D1 & D2 & D3 & D6). destruct S0 as [S0 S1].
  destruct (Z.leb_spec (8 * g + 8) n) as [LE|GT].
  - (* [comment removed for export] *)
    destruct BODY as [[_ [B0 [B1 BR]]] _]. cbn [cells_bytes cbytes] in B1, BR. rewrite app_nil_r in B1, BR.
    rewrite repeat_length in B1, BR.
    specialize (BR (Z.to_nat g) ltac:(lia)). rewrite Z2Nat.id in BR by lia. rewrite <- mrd_high by lia. rewrite BR.
    rewrite nth_error_repeat by lia. reflexivity.
  - (* [comment removed for export] *)
    assert (g = n / 8) as -> by lia. assert (NE : n mod 8 <> 0) by lia.
    rewrite <- mrd_high by lia. pose proof (rw_cells_read bsegs m _ _ 0%nat (C1 (Z_to_bv 8 (n mod 8))) (LAST NE) eq_refl) as R.
    cbn [csize cbytes] in R. rewrite Z.add_0_r in R.
    (* [comment removed for export] *)
    rewrite ov_rdn in R. cbn [rdn] in R.
    destruct (mrd bsegs m (wa (shad A + n / 8))) as [b|] eqn:E; [| unfold mrd in E; rewrite E in R; discriminate].
    unfold mrd in E. rewrite E in R. injection R as ->. rewrite <- D6. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma poisoned_chunks : forall m A cap,
  0 < cap ->
  rw_cells bsegs m (shad A) [CB (Z.to_nat (shlen (rup8 cap))) (repeat (Z_to_bv 8 252) (Z.to_nat (shlen (rup8 cap))))] ->
  rw_cells bsegs m (shad A) [CB (Z.to_nat (cap / 8)) (repeat (Z_to_bv 8 252) (Z.to_nat (cap / 8)))]
  /\ (cap mod 8 <> 0 -> rw_cells bsegs m (shad A + cap / 8) [C1 (Z_to_bv 8 252)]).
Proof.
  intros m A cap CAP H.
  assert (E : shlen (rup8 cap) = cap / 8 + (if cap mod 8 =? 0 then 0 else 1)).
  { unfold shlen, rup8, rdn8. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    destruct (Z.eqb_spec (cap mod 8) 0); Z.div_mod_to_equations; lia. }
  rewrite E in H. assert (D0 : 0 <= cap / 8) by (Z.div_mod_to_equations; lia).
  destruct (Z.eqb_spec (cap mod 8) 0) as [Z0|NZ].
  - rewrite Z.add_0_r in H. split; [exact H| intros NE; exfalso; exact (NE Z0)].
  - pose proof (rw_cells_split_CB bsegs m (shad A) [] _ _ [] [Z.to_nat (cap / 8); 1%nat] H ltac:(cbn; lia)) as H2.
    cbn [app mk_CB_cells] in H2.
    rewrite ARepKit_firstn_repeat in H2 by lia. rewrite ARepKit_skipn_repeat, ARepKit_firstn_repeat in H2 by lia.
    replace (Z.to_nat (cap / 8 + 1) - Z.to_nat (cap / 8))%nat with 1%nat in H2 by lia. cbn [repeat] in H2.
    apply (proj1 (rw_cells_app bsegs m (shad A) [_] [_])) in H2. destruct H2 as [H1 H2].
    cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r, Z2Nat.id in H2 by lia.
    split; [exact H1|]. intros _. eapply rw_cells_recast; [exact H2| cbn; tauto| reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma annot_pair_munch : forall (W : list (Z * Z)) m0 m3 A n,
  0 < n -> A mod 8 = 0 -> 0 <= A -> A + n <= 2^47 ->
  ablock_shadow m0 A n -> ablock_shadow m3 A n ->
  (forall x : word, outside W (bv_unsigned x) ->
     ~ (shad A <= bv_unsigned x < shad A + shlen (rup8 n)) -> m3 x = m0 x) ->
  munch W m0 m3.
Proof.
  intros W m0 m3 A n Hn AL A0 AH S0 S3 OUT x Hx.
  pose proof (bv_unsigned_in_range 64 x) as XR.
  assert (SE : shlen (rup8 n) = (n + 7) / 8 /\ shad A = 2147450880 + A / 8).
  { unfold shlen, rup8, rdn8, shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. split; [|reflexivity].
    Z.div_mod_to_equations. lia. }
  destruct SE as [SE SA].
  destruct (Z_lt_le_dec (bv_unsigned x) (shad A)) as [LT|GE]; [apply OUT; [exact Hx| lia]|].
  destruct (Z_lt_le_dec (bv_unsigned x) (shad A + shlen (rup8 n))) as [IN|GE2]; [| apply OUT; [exact Hx| lia]].
  (* [comment removed for export] *)
  set (g := bv_unsigned x - shad A).
  assert (G : 0 <= g /\ 8 * g < n) by (subst g; rewrite SE in IN; Z.div_mod_to_equations; lia).
  rewrite <- (Z_to_bv_bv_unsigned x). replace (bv_unsigned x) with (shad A + g) by lia.
  change (Z_to_bv 64 (shad A + g)) with (wa (shad A + g)).
  rewrite (S0 g), (S3 g) by lia. reflexivity.
Qed.
End CANSEC1.
