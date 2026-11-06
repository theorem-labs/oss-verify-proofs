(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require RMalloc_ifaceP RDriver_facts.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessM ProgP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import RunDraw PU_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma land_ones64 : forall y, 0 <= y < 2^64 -> Z.land y 18446744073709551615 = y.
Proof. intros y Hy. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
(* [comment removed for export] *)
Lemma land_m2 : forall y, 0 <= y < 2^64 -> Z.land y 18446744073709551614 = y - y mod 2.
Proof.
  intros y Hy. change 18446744073709551614 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 1))).
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2. pose proof (Z.div_mod y 2 ltac:(lia)). lia.
Qed.

Lemma land_ones_mod : forall x, Z.land x 18446744073709551615 = x mod 2^64.
Proof. intros x. change 18446744073709551615 with (Z.ones 64). apply Z.land_ones. lia. Qed.
(* [comment removed for export] *)
Lemma memmove_test_apart : forall d s n, 0 <= s -> 0 <= d -> 0 < n -> s + n < 2^63 -> d + n < 2^63 ->
  (s + n <= d \/ d + n <= s) -> ~ ((0 + - ((n + n) mod 2^64)) mod 2^64 < (s + - (n + d)) mod 2^64).
Proof.
  intros d s n Hs Hd Hn Hsn Hdn SEP LT.
  rewrite (Z.mod_small (n + n)) in LT by lia.
  replace ((0 + - (n + n)) mod 2 ^ 64) with (2^64 - (n + n)) in LT.
  2:{ replace (0 + - (n + n)) with ((2^64 - (n + n)) + (-1) * 2^64) by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
  destruct SEP as [L|R].
  - replace (s + - (n + d)) with ((2^64 + s - (n + d)) + (-1) * 2^64) in LT by lia. rewrite Z.mod_add in LT by lia.
    rewrite Z.mod_small in LT by lia. lia.
  - rewrite Z.mod_small in LT by lia. lia.
Qed.

Lemma outside_app : forall W1 W2 a, outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 a; cbn; [tauto|]. rewrite IH. tauto.
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
Lemma stk_of_cells : forall m A cs, rw_cells psegs m A cs -> stk psegs m A (A + Z.of_nat (cells_size cs)).
Proof.
  intros m A cs [[Hwf (B0 & B1 & HB)] (W0 & W1 & W)]. rewrite cells_bytes_length in B1 by exact Hwf.
  split; [exact B0|]. split; [exact B1|]. intros a Ha. split; [replace (wa a) with (wa (A + (a - A))) by (f_equal; lia); apply W; lia|].
  specialize (HB (Z.to_nat (a - A)) ltac:(rewrite cells_bytes_length by exact Hwf; lia)).
  replace (A + Z.of_nat (Z.to_nat (a - A))) with a in HB by lia.
  destruct (nth_error (cells_bytes cs) (Z.to_nat (a - A))) as [b|] eqn:E; [exists b; exact HB|].
  apply nth_error_None in E. rewrite cells_bytes_length in E by exact Hwf. lia.
Qed.
(* [comment removed for export] *)
Lemma u8arr_of_cells : forall m A cs, rw_cells psegs m A cs -> u8arr psegs m A (cells_bytes cs).
Proof.
  intros m A cs [[Hwf HB] (W0 & W1 & W)]. split; [exact HB|]. rewrite cells_bytes_length by exact Hwf.
  split; [exact W0|]. split; [exact W1|]. intros i Hi. apply W. exact Hi.
Qed.
Lemma cells_of_u8arr : forall m A bs, u8arr psegs m A bs -> rw_cells psegs m A [CB (length bs) bs].
Proof.
  intros m A bs [HB HW]. split; [split; [cbn; split; [reflexivity| exact I]|]|].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact HW.
Qed.

(* [comment removed for export] *)
Lemma nodup_ids_ne : forall (LB : list block) b1 b2, List.NoDup (map blk_id LB) -> In b1 LB -> In b2 LB -> b1 <> b2 -> blk_id b1 <> blk_id b2.
Proof.
  induction LB as [|x LB IH]; intros b1 b2 ND H1 H2 NE; [destruct H1|].
  cbn [map] in ND. apply NoDup_cons_iff in ND as [NI ND].
  destruct H1 as [->|H1], H2 as [->|H2].
  - congruence.
  - intros E. apply NI. rewrite E. apply in_map. exact H2.
  - intros E. apply NI. rewrite <- E. apply in_map. exact H1.
  - exact (IH b1 b2 ND H1 H2 NE).
Qed.
Lemma in_lb_remove : forall p LB b, In b LB -> blk_id b <> p -> In b (lb_remove p LB).
Proof.
  intros p LB b. unfold lb_remove. induction LB as [|x LB IH]; intros Hb Hne; [destruct Hb|].
  rewrite filter_cons. destruct Hb as [->|Hb].
  - destruct (decide _) as [Y|N]; [left; reflexivity|]. exfalso. apply N.
    destruct (bptr_eqb (blk_id b) p) eqn:E; [| exact I]. apply RDriver_facts.bptr_eqb_eq in E. congruence.
  - destruct (decide _); [right|]; apply IH; assumption.
Qed.
Lemma lb_remove_sub : forall p LB b, In b (lb_remove p LB) -> In b LB.
Proof.
  intros p LB b. unfold lb_remove. induction LB as [|x LB IH]; intros Hb; [exact Hb|].
  rewrite filter_cons in Hb. destruct (decide _); [destruct Hb as [->|Hb]; [left; reflexivity| right; apply IH; exact Hb]| right; apply IH; exact Hb].
Qed.

Lemma lb_remove_ne : forall p LB b, In b (lb_remove p LB) -> blk_id b <> p.
Proof.
  intros p LB b. unfold lb_remove. induction LB as [|x LB IH]; intros Hb; [destruct Hb|].
  rewrite filter_cons in Hb. destruct (decide _) as [Y|N]; [| apply IH; exact Hb].
  destruct Hb as [->|Hb]; [| apply IH; exact Hb].
  intros E. rewrite <- E in Y. rewrite RDriver_facts.bptr_eqb_refl' in Y. exact Y.
Qed.


Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition rheap_pres_x (LB : list block) (SP X n : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> ~ (X <= a < X + n) ->
    m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None).
(* [comment removed for export] *)
Definition rheap_pres_W (LB : list block) (SP : Z) (W : list (Z * Z)) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a ->
    m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None).

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
Lemma rheap_pres_x_weaken : forall LB LB' SP SP' X n Y k m m', rheap_pres_x LB' SP' X n m m' -> SP' <= SP ->
  (forall b, In b LB -> In b LB') -> (forall a, rclient_addr LB SP a -> ~ (Y <= a < Y + k) -> ~ (X <= a < X + n)) ->
  rheap_pres_x LB SP Y k m m'.
Proof.
  intros LB LB' SP SP' X n Y k m m' H HS HL HX a Ha Hc Hy. apply H; [exact Ha| | exact (HX a Hc Hy)].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right; exists b; split; [apply HL; exact Hb| exact Hr]].
Qed.
Lemma rheap_pres_W_trans : forall LB SP W m1 m2 m3,
  rheap_pres_W LB SP W m1 m2 -> rheap_pres_W LB SP W m2 m3 -> rheap_pres_W LB SP W m1 m3.
Proof.
  intros LB SP W m1 m2 m3 H1 H2 a Ha Hc Hx. destruct (H1 a Ha Hc Hx) as [E1 W1]. destruct (H2 a Ha Hc Hx) as [E2 W2].
  split; [congruence| auto].
Qed.
Lemma rheap_pres_W_of_munch : forall LB SP Wq W m m', munch Wq m m' -> wmono psegs m m' ->
  (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a -> outside Wq a) -> rheap_pres_W LB SP W m m'.
Proof.
  intros LB SP Wq W m m' MU WM OUT a Ha Hc Hx. split.
  - apply MU. unfold wa. rewrite unsigned_lit by lia. apply OUT; assumption.
  - intros Hv. apply WM. exact Hv.
Qed.
Lemma rheap_pres_W_of_pres : forall LB LB' SP SP' W m m', rheap_pres LB' SP' m m' -> SP' <= SP ->
  (forall b, In b LB -> In b LB') -> rheap_pres_W LB SP W m m'.
Proof.
  intros LB LB' SP SP' W m m' H HS HL a Ha Hc _. apply (rheap_pres_weaken LB' LB SP' SP m m' H HS HL a Ha Hc).
Qed.
Lemma rheap_pres_W_of_x : forall LB SP X n W m m', rheap_pres_x LB SP X n m m' ->
  (forall a, outside W a -> ~ (X <= a < X + n)) -> rheap_pres_W LB SP W m m'.
Proof. intros LB SP X n W m m' H HX a Ha Hc Ho. exact (H a Ha Hc (HX a Ho)). Qed.

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
Lemma rheap_pres_x_stk : forall LB SP X n m m' lo hi, rheap_pres_x LB SP X n m m' -> stk psegs m lo hi -> SP <= lo ->
  (hi <= X \/ X + n <= lo) -> stk psegs m' lo hi.
Proof.
  intros LB SP X n m m' lo hi HP (H0 & H1 & HW) HS HX. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia) ltac:(lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.
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
Lemma rheap_pres_W_bytes_at : forall LB SP W m m' A bs, rheap_pres_W LB SP W m m' -> bytes_at psegs m A bs ->
  rclient_range LB SP A (Z.of_nat (length bs)) -> disjoint_from W A (Z.of_nat (length bs)) -> bytes_at psegs m' A bs.
Proof.
  intros LB SP W m m' A bs HP (H0 & H1 & HB) HR HD. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia]) ltac:(eapply disjoint_outside; [exact HD| lia])) as [E _].
  rewrite E. reflexivity.
Qed.
Lemma rheap_pres_W_rw_cells : forall LB SP W m m' A cs, rheap_pres_W LB SP W m m' -> rw_cells psegs m A cs ->
  rclient_range LB SP A (Z.of_nat (cells_size cs)) -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells psegs m' A cs.
Proof.
  intros LB SP W m m' A cs HP [[Hwf HB] (W0 & W1 & WW)] HR HD. split; [split; [exact Hwf|]|].
  - eapply rheap_pres_W_bytes_at; [exact HP| exact HB| rewrite cells_bytes_length by exact Hwf; exact HR| rewrite cells_bytes_length by exact Hwf; exact HD].
  - split; [exact W0|]. split; [exact W1|]. intros i Hi.
    destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia]) ltac:(eapply disjoint_outside; [exact HD| lia])) as [_ WV].
    apply WV. apply WW. exact Hi.
Qed.
Lemma rheap_pres_W_stk : forall LB SP W m m' lo hi, rheap_pres_W LB SP W m m' -> stk psegs m lo hi -> SP <= lo ->
  (forall a, lo <= a < hi -> outside W a) -> stk psegs m' lo hi.
Proof.
  intros LB SP W m m' lo hi HP (H0 & H1 & HW) HS HX. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia) (HX i Hi)) as [E W']. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W', W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma rclient_range_sp : forall LB SP SP' A n, rclient_range LB SP A n -> SP' <= SP -> rclient_range LB SP' A n.
Proof. intros LB SP SP' A n [H|[H|H]] HS; [left; lia| right; left; exact H| right; right; exact H]. Qed.
Lemma rclient_range_len : forall LB SP A n n', rclient_range LB SP A n -> n' = n -> rclient_range LB SP A n'.
Proof. intros LB SP A n n' H ->. exact H. Qed.
Lemma rclient_range_mono : forall LB LB' SP A n, (forall b, In b LB -> In b LB') -> rclient_range LB SP A n -> rclient_range LB' SP A n.
Proof.
  intros LB LB' SP A n HS [H|[H|(b & Hb & Hr)]]; [left; exact H| right; left; exact H|].
  right; right. exists b. split; [apply HS; exact Hb| exact Hr].
Qed.
Lemma rclient_range_app_r : forall L1 LB SP A n, rclient_range LB SP A n -> rclient_range (L1 ++ LB) SP A n.
Proof.
  intros L1 LB SP A n [H|[H|(b & Hb & Hr)]]; [left; exact H| right; left; exact H|].
  right; right. exists b. split; [apply in_or_app; right; exact Hb| exact Hr].
Qed.
Lemma rclient_range_cons : forall b0 LB SP A n, rclient_range LB SP A n -> rclient_range (b0 :: LB) SP A n.
Proof. intros b0 LB SP A n H. apply (rclient_range_app_r [b0]). exact H. Qed.
End CANSEC1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ret_lit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; rpc) | |- _ => idtac end.
(* [comment removed for export] *)
Ltac has_var c := match c with context [?v] => is_var v end.
Ltac lit_if := lazymatch goal with |- evt _ _ (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?mm ?ro) =>
   tryif has_var c then fail 0 "lit_if: the branch condition is not closed" else
   (let v := eval vm_compute in c in
    lazymatch v with true => change (if c then x else y) with x | false => change (if c then x else y) with y end) end.
(* [comment removed for export] *)
Ltac br_dead K := if_cases K; zify_cond K; try (exfalso; lia).
(* [comment removed for export] *)
Definition hidden (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?T => change T with (hidden T) in H end.
Ltac unhide H := unfold hidden in H.
(* [comment removed for export] *)
Ltac blk_find L X := lazymatch L with
  | (?p, X, ?n) :: _ => constr:((p, X, n))
  | _ :: ?L' => blk_find L' X
  end.
Ltac rcr := lazymatch goal with |- rclient_range ?L ?SP ?A ?n =>
  first [ is_Zlit A; right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; cbn; lia
        | let X := lazymatch A with ?X + _ => X | ?X => X end in
          let b := blk_find L X in
          right; right; exists b; split; [cbn [In]; repeat (first [left; reflexivity| right]) | cbn; lia]
        | let X := lazymatch A with ?X + _ => X | ?X => X end in
          match goal with HIN : In (?p, X, ?k) ?L0 |- _ =>
            right; right; exists (p, X, k); split; [first [exact HIN | cbn [In]; repeat (first [exact HIN | left; reflexivity | right])] | cbn; lia] end
        | match goal with HCR : rclient_range ?L1 ?SP1 A ?k |- _ =>
            eapply rclient_range_len; [first [eapply rclient_range_sp; [exact HCR| cbn; lia]
                                            | eapply rclient_range_cons; eapply rclient_range_sp; [exact HCR| cbn; lia]
                                            | eapply rclient_range_cons; eapply rclient_range_cons; eapply rclient_range_sp; [exact HCR| cbn; lia]
                                            | match goal with HS : forall bq, In bq L1 -> In bq _ |- _ =>
                                                first [ eapply (rclient_range_mono _ _ _ _ _ HS)
                                                      | eapply rclient_range_cons; eapply (rclient_range_mono _ _ _ _ _ HS)
                                                      | eapply rclient_range_cons; eapply rclient_range_cons; eapply (rclient_range_mono _ _ _ _ _ HS) ];
                                                eapply rclient_range_sp; [exact HCR| cbn; lia] end] | cbn; lia] end
        | left; cbn; lia ] end.
(* [comment removed for export] *)
Definition skipped (P : Prop) : Prop := P.
Ltac skip_it H := lazymatch type of H with ?T => change (skipped T) in H end.
Ltac unskip := repeat match goal with H : skipped _ |- _ => unfold skipped in H end.
Ltac trx HPR :=
  lazymatch type of HPR with rheap_pres_x ?L ?SP ?X ?n ?mo ?mn =>
  repeat match goal with
  | H : rw_cells psegs mo ?A ?cs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : rw_cells psegs mn A cs) by (eapply rheap_pres_x_rw_cells; [exact HPR| exact H| rcr | cbn; lia]); clear H; rename H' into H
            | skip_it H ]
  | H : bytes_at psegs mo ?A ?bs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : bytes_at psegs mn A bs) by (eapply rheap_pres_x_bytes_at; [exact HPR| exact H| rcr | cbn; lia]); clear H; rename H' into H
            | skip_it H ]
  end end; unskip.
Ltac trW HPR :=
  lazymatch type of HPR with rheap_pres_W ?L ?SP ?W ?mo ?mn =>
  repeat match goal with
  | H : rw_cells psegs mo ?A ?cs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : rw_cells psegs mn A cs) by (eapply rheap_pres_W_rw_cells; [exact HPR| exact H| rcr | cbn; lia]); clear H; rename H' into H
            | skip_it H ]
  | H : bytes_at psegs mo ?A ?bs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : bytes_at psegs mn A bs) by (eapply rheap_pres_W_bytes_at; [exact HPR| exact H| rcr | cbn; lia]); clear H; rename H' into H
            | skip_it H ]
  end end; unskip.
Ltac trp HPR :=
  lazymatch type of HPR with rheap_pres ?L ?SP ?mo ?mn =>
  repeat match goal with
  | H : rw_cells psegs mo ?A ?cs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : rw_cells psegs mn A cs) by (eapply rheap_pres_rw_cells; [exact HPR| exact H| rcr]); clear H; rename H' into H
            | skip_it H ]
  | H : bytes_at psegs mo ?A ?bs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : bytes_at psegs mn A bs) by (eapply rheap_pres_bytes_at; [exact HPR| exact H| rcr]); clear H; rename H' into H
            | skip_it H ]
  end end; unskip.
Ltac trm MU WM :=
  lazymatch type of MU with munch ?W ?mo ?mn =>
  repeat match goal with
  | H : rw_cells psegs mo ?A ?cs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : rw_cells psegs mn A cs) by (eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn; lia]); clear H; rename H' into H
            | skip_it H ]
  | H : bytes_at psegs mo ?A ?bs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : bytes_at psegs mn A bs) by (eapply bytes_at_transport; [exact H| exact MU| cbn; lia]); clear H; rename H' into H
            | skip_it H ]
  end end; unskip.
(* [comment removed for export] *)
Definition parked (P : Prop) : Prop := P.
Ltac park_mem m := repeat match goal with
  | H : rw_cells psegs m _ _ |- _ => lazymatch type of H with ?T => change (parked T) in H end
  | H : bytes_at psegs m _ _ |- _ => lazymatch type of H with ?T => change (parked T) in H end end.
Ltac unpark := repeat match goal with H : parked _ |- _ => unfold parked in H end.
