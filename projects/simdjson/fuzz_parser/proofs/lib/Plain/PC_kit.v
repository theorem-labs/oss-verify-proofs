(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import Stdio_pure Printf_pieces.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface ROpNew ROpNew_nt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessP ProgP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RunDraw PU_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma div3_magic : forall cap, 0 <= cap < 2^32 -> Z.shiftr (cap * 2863311531) 33 = cap / 3.
Proof.
  intros cap Hc. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 33) with 8589934592.
  pose proof (Z.div_mod cap 3 ltac:(lia)) as D. pose proof (Z.mod_pos_bound cap 3 ltac:(lia)) as R.
  set (q := cap / 3) in *. set (r := cap mod 3) in *. clearbody q r.
  symmetry. apply (Z.div_unique _ _ q (q + r * 2863311531)); [left; lia| lia].
Qed.
Lemma land_m64 : forall y, 0 <= y < 2^64 -> Z.land y 18446744073709551552 = y / 64 * 64.
Proof.
  intros y Hy. change 18446744073709551552 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 6))).
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma land_m512_36 : forall y, 0 <= y < 2^36 -> Z.land y 68719476224 = y / 512 * 512.
Proof.
  intros y Hy. change 68719476224 with (Z.land (Z.ones 36) (Z.lnot (Z.ones 9))).
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma land_ones64 : forall y, 0 <= y < 2^64 -> Z.land y 18446744073709551615 = y.
Proof. intros y Hy. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.


Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition rheap_pres_x (LB : list block) (SP X n : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> ~ (X <= a < X + n) ->
    m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None).


(* [comment removed for export] *)
Lemma rheap_pres_x_trans : forall LB SP X n m1 m2 m3,
  rheap_pres_x LB SP X n m1 m2 -> rheap_pres_x LB SP X n m2 m3 -> rheap_pres_x LB SP X n m1 m3.
Proof.
  intros LB SP X n m1 m2 m3 H1 H2 a Ha Hc Hx. destruct (H1 a Ha Hc Hx) as [E1 W1]. destruct (H2 a Ha Hc Hx) as [E2 W2].
  split; [congruence| auto].
Qed.
Lemma rheap_pres_x_of_munch : forall LB SP X n W m m', munch W m m' -> wmono psegs m m' ->
  (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> ~ (X <= a < X + n) -> outside W a) -> rheap_pres_x LB SP X n m m'.
Proof.
  intros LB SP X n W m m' MU WM OUT a Ha Hc Hx. split.
  - apply MU. unfold wa. rewrite unsigned_lit by lia. apply OUT; assumption.
  - intros Hv. apply WM. exact Hv.
Qed.
Lemma rheap_pres_x_of_pres : forall LB LB' SP SP' X n m m', rheap_pres LB' SP' m m' -> SP' <= SP ->
  (forall b, In b LB -> In b LB') -> rheap_pres_x LB SP X n m m'.
Proof.
  intros LB LB' SP SP' X n m m' H HS HL a Ha Hc _. apply (rheap_pres_weaken LB' LB SP' SP m m' H HS HL a Ha Hc).
Qed.


(* [comment removed for export] *)
Lemma bytes_at_app_split : forall segs m A b1 b2, bytes_at segs m A (b1 ++ b2) ->
  bytes_at segs m A b1 /\ bytes_at segs m (A + Z.of_nat (length b1)) b2.
Proof.
  intros segs m A b1 b2 (H0 & H1 & H). rewrite length_app in H1. split.
  - split; [exact H0|]. split; [lia|]. intros i Hi. rewrite (H i ltac:(rewrite length_app; lia)). apply nth_error_app1. exact Hi.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (length b1) + Z.of_nat i) with (A + Z.of_nat (length b1 + i)) by lia.
    rewrite (H (length b1 + i)%nat ltac:(rewrite length_app; lia)). rewrite nth_error_app2 by lia. f_equal. lia.
Qed.
Lemma bytes_at_app_join : forall segs m A b1 b2, bytes_at segs m A b1 -> bytes_at segs m (A + Z.of_nat (length b1)) b2 ->
  bytes_at segs m A (b1 ++ b2).
Proof.
  intros segs m A b1 b2 (H0 & H1 & HA) (_ & H2 & HB). split; [exact H0|]. split; [rewrite length_app; lia|].
  intros i Hi. rewrite length_app in Hi. destruct (Nat.lt_ge_cases i (length b1)) as [L|G].
  - rewrite nth_error_app1 by exact L. exact (HA i L).
  - rewrite nth_error_app2 by exact G. specialize (HB (i - length b1)%nat ltac:(lia)).
    replace (A + Z.of_nat (length b1) + Z.of_nat (i - length b1)) with (A + Z.of_nat i) in HB by lia. exact HB.
Qed.
Lemma rw_cells_app_split : forall segs m A cs1 cs2, rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[Hwf Hb] (W0 & W1 & W)]. apply cells_wf_app in Hwf as [Hw1 Hw2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app_split in Hb as [Hb1 Hb2]. rewrite cells_bytes_length in Hb2 by exact Hw1.
  rewrite cells_size_app in W1, W. split.
  - split; [split; assumption|]. split; [exact W0|]. split; [lia|]. intros i Hi. apply W. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply W. lia.
Qed.
Lemma rw_cells_app_join : forall segs m A cs1 cs2, rw_cells segs m A cs1 -> rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A cs1 cs2 [[Hw1 Hb1] (W0 & W1 & WA)] [[Hw2 Hb2] (_ & W2 & WB)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app_join; [exact Hb1|]. rewrite cells_bytes_length by exact Hw1. exact Hb2.
  - rewrite cells_size_app. split; [exact W0|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))) as [L|G]; [apply WA; lia|].
    specialize (WB (i - Z.of_nat (cells_size cs1)) ltac:(lia)).
    replace (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) with (A + i) in WB by lia. exact WB.
Qed.


Lemma rw_cells_cut : forall segs m A cs k, rw_cells segs m A cs ->
  rw_cells segs m A (firstn k cs) /\ rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs))) (skipn k cs).
Proof. intros segs m A cs k H. apply rw_cells_app_split. rewrite firstn_skipn. exact H. Qed.

(* [comment removed for export] *)
Lemma new_block_disj : forall s p A n LB m b, RHEAP s ((p, A, n) :: LB) m -> In b LB ->
  A + n <= blk_addr b \/ blk_addr b + blk_size b <= A.
Proof.
  intros s p A n LB m b HP Hb. pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP) as ND. cbn [map] in ND.
  apply NoDup_cons_iff in ND as [NI _].
  assert (NE : blk_id (p, A, n) <> blk_id b) by (intros E; apply NI; rewrite E; apply in_map; exact Hb).
  exact (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ (p, A, n) b HP (or_introl eq_refl) (or_intror Hb) NE).
Qed.

(* [comment removed for export] *)
Lemma rheap_pres_x_bytes_at : forall LB SP X n m m' A bs, rheap_pres_x LB SP X n m m' -> bytes_at psegs m A bs ->
  rclient_range LB SP A (Z.of_nat (length bs)) -> (A + Z.of_nat (length bs) <= X \/ X + n <= A) -> bytes_at psegs m' A bs.
Proof.
  intros LB SP X n m m' A bs HP (H0 & H1 & HB) HR HX. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia]) ltac:(lia)) as [E _].
  rewrite E. reflexivity.
Qed.
Lemma rheap_pres_x_rw_cells : forall LB SP X n m m' A cs, rheap_pres_x LB SP X n m m' -> rw_cells psegs m A cs ->
  rclient_range LB SP A (Z.of_nat (cells_size cs)) -> (A + Z.of_nat (cells_size cs) <= X \/ X + n <= A) -> rw_cells psegs m' A cs.
Proof.
  intros LB SP X n m m' A cs HP [[Hwf HB] (W0 & W1 & W)] HR HX. split; [split; [exact Hwf|]|].
  - eapply rheap_pres_x_bytes_at; [exact HP| exact HB| rewrite cells_bytes_length by exact Hwf; exact HR| rewrite cells_bytes_length by exact Hwf; exact HX].
  - split; [exact W0|]. split; [exact W1|]. intros i Hi.
    destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia]) ltac:(lia)) as [_ WW]. apply WW. apply W. exact Hi.
Qed.

Lemma rheap_pres_x_weaken : forall LB LB' SP SP' X n Y k m m', rheap_pres_x LB' SP' X n m m' -> SP' <= SP ->
  (forall b, In b LB -> In b LB') -> (forall a, rclient_addr LB SP a -> ~ (Y <= a < Y + k) -> ~ (X <= a < X + n)) ->
  rheap_pres_x LB SP Y k m m'.
Proof.
  intros LB LB' SP SP' X n Y k m m' H HS HL HX a Ha Hc Hy. apply H; [exact Ha| | exact (HX a Hc Hy)].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right; exists b; split; [apply HL; exact Hb| exact Hr]].
Qed.

(* [comment removed for export] *)
Lemma stk_of_cells : forall m A cs, rw_cells psegs m A cs -> stk psegs m A (A + Z.of_nat (cells_size cs)).
Proof.
  intros m A cs [[Hwf (B0 & B1 & HB)] (W0 & W1 & W)]. rewrite cells_bytes_length in B1 by exact Hwf.
  split; [exact B0|]. split; [exact B1|]. intros a Ha. split; [replace (wa a) with (wa (A + (a - A))) by (f_equal; lia); apply W; lia|].
  specialize (HB (Z.to_nat (a - A)) ltac:(rewrite cells_bytes_length by exact Hwf; lia)).
  replace (A + Z.of_nat (Z.to_nat (a - A))) with a in HB by lia.
  destruct (nth_error (cells_bytes cs) (Z.to_nat (a - A))) as [b|] eqn:E; [exists b; exact HB|].
  apply nth_error_None in E. rewrite cells_bytes_length in E by exact Hwf. lia.
Qed.
Lemma rheap_pres_x_stk : forall LB SP X n m m' lo hi, rheap_pres_x LB SP X n m m' -> stk psegs m lo hi -> SP <= lo ->
  (hi <= X \/ X + n <= lo) -> stk psegs m' lo hi.
Proof.
  intros LB SP X n m m' lo hi HP (H0 & H1 & HW) HS HX. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia) ltac:(lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.
(* [comment removed for export] *)
Lemma stk_of_x_stk : forall LB SP X n m m' lo hi, rheap_pres_x LB SP X n m m' -> stk psegs m lo hi -> stk psegs m' X (X + n) ->
  SP <= lo -> lo <= X -> X + n <= hi -> stk psegs m' lo hi.
Proof.
  intros LB SP X n m m' lo hi HP (H0 & H1 & HW) (G0 & G1 & GW) HS H2 H3. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (Z_lt_le_dec i X) as [L|L]; [|destruct (Z_lt_le_dec i (X + n)) as [L2|L2]].
  - destruct (HP i ltac:(lia) ltac:(left; lia) ltac:(lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
    split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
  - apply GW. lia.
  - destruct (HP i ltac:(lia) ltac:(left; lia) ltac:(lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
    split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.
End CANSEC1.
