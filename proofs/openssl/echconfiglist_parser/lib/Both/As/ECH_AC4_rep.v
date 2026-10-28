(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsAtomics ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AKit ECH_AStmt_C2 ECH_APF_C4 ECH_AStmt_C4.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma rw_cells_recut : forall m A cs cs',
  rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
Proof.
  intros m A cs cs' [[WF B] W] WF' E. split; [split; [exact WF'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' WF'), E, (cells_bytes_length cs WF). exact W.
Qed.

(* [comment removed for export] *)
Lemma u32arr_of_CB : forall m A ws, rw_cells asegs m A [CB (4 * length ws)%nat (u32s ws)] -> u32arr asegs m A ws.
Proof.
  intros m A ws [[WF B] W]. split.
  - cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  - cbn [cells_size csize] in W. rewrite Nat.add_0_r in W. replace (4 * Z.of_nat (length ws)) with (Z.of_nat (4 * length ws)) by lia. exact W.
Qed.
Lemma u64arr_of_CB' : forall m A ws, rw_cells asegs m A [CB (8 * length ws)%nat (u64s ws)] -> u64arr asegs m A ws.
Proof.
  intros m A ws [[WF B] W]. split.
  - cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  - cbn [cells_size csize] in W. rewrite Nat.add_0_r in W. replace (8 * Z.of_nat (length ws)) with (Z.of_nat (8 * length ws)) by lia. exact W.
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition errst_zero_cells : list cell :=
  [CB 64 (zeros 64); CB 64 (zeros 64); CB 128 (zeros 128); CB 128 (zeros 128); CB 128 (zeros 128); CB 64 (zeros 64);
   CB 128 (zeros 128); CB 64 (zeros 64); CB 128 (zeros 128); C4 (wz 0); C4 (wz 0)].

Lemma ERRST_of_zeros : forall LB m a, rw_cells asegs m a [CB 904 (zeros 904)] -> ERRST LB m a errst_zero.
Proof.
  intros LB m a H.
  assert (R : rw_cells asegs m a errst_zero_cells).
  { eapply rw_cells_recut; [exact H| |]; vm_compute; [repeat split| reflexivity]. }
  unfold errst_zero_cells in R.
  (* [comment removed for export] *)
  change (rw_cells asegs m a ([CB 64 (zeros 64)] ++ [CB 64 (zeros 64)] ++ [CB 128 (zeros 128)] ++ [CB 128 (zeros 128)] ++ [CB 128 (zeros 128)]
            ++ [CB 64 (zeros 64)] ++ [CB 128 (zeros 128)] ++ [CB 64 (zeros 64)] ++ [CB 128 (zeros 128)] ++ [C4 (wz 0); C4 (wz 0)])) in R.
  repeat (apply (proj1 (rw_cells_app _ _ _ _ _)) in R; let K := fresh "K" in destruct R as [K R]; cbn [cells_size csize Nat.add] in R).
  unfold ERRST, errst_zero, O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP. cbn [es_slots es_top es_bottom].
  repeat rewrite <- Z.add_assoc in *. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in *.
  split; [reflexivity|]. split; [lia|]. split; [lia|].
  repeat match goal with |- _ /\ _ => split end;
    try first [ apply u32arr_of_CB; assumption | apply u64arr_of_CB'; assumption | assumption ].
  repeat constructor; cbn; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma slot_nth : forall (E : errst) (i : Z) {X} (f : errslot -> X),
  length (es_slots E) = 16%nat -> 0 <= i < 16 -> nth_error (map f (es_slots E)) (Z.to_nat i) = Some (f (slot_at E i)).
Proof.
  intros E i X f L Hi. rewrite nth_error_map. unfold slot_at.
  rewrite (nth_error_nth' (es_slots E) (slot_clear 0)) by lia. reflexivity.
Qed.

Lemma slot_upd_length : forall ss i x, (i < length ss)%nat -> length (slot_upd ss i x) = length ss.
Proof. intros ss i x Hi. unfold slot_upd. rewrite length_app, length_firstn. cbn [length]. rewrite length_skipn. lia. Qed.

Lemma map_slot_upd : forall {X} (f : errslot -> X) ss i x, (i < length ss)%nat -> map f (slot_upd ss i x) = upd (map f ss) i (f x).
Proof.
  intros X f ss i x Hi. rewrite upd_firstn_skipn by (rewrite length_map; exact Hi).
  unfold slot_upd. rewrite map_app. cbn [map]. rewrite firstn_map, skipn_map. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma upd_same : forall {X} (l : list X) i x, nth_error l i = Some x -> upd l i x = l.
Proof. intros X l. induction l as [|y l IH]; intros [|i] x H; cbn in *; try discriminate; [congruence| rewrite IH by exact H; reflexivity]. Qed.

Lemma upd_zero16 : forall i, (i < 16)%nat -> upd zero16 i (wz 0) = zero16.
Proof. intros i Hi. do 16 (destruct i as [|i]; [reflexivity|]). lia. Qed.

Lemma in_firstn_in : forall {X} n (l : list X) y, In y (firstn n l) -> In y l.
Proof. intros X n. induction n as [|n IH]; intros [|z l] y H; cbn in *; try contradiction. destruct H as [->|H]; [left; reflexivity| right; apply IH; exact H]. Qed.
Lemma in_skipn_in : forall {X} n (l : list X) y, In y (skipn n l) -> In y l.
Proof. intros X n. induction n as [|n IH]; intros [|z l] y H; cbn in *; try contradiction; try exact H. right. apply IH. exact H. Qed.
Lemma own_slot_upd : forall (P : errslot -> Prop) ss i x, Forall P ss -> P x -> Forall P (slot_upd ss i x).
Proof.
  intros P ss i x FA Px. unfold slot_upd. rewrite Forall_forall in *. intros y Hy. apply in_app_or in Hy.
  destruct Hy as [Hy|[<-|Hy]]; [apply FA; eapply in_firstn_in; exact Hy| exact Px| apply FA; eapply in_skipn_in; exact Hy].
Qed.

Lemma slot_at_own : forall (P : errslot -> Prop) E i, Forall P (es_slots E) -> length (es_slots E) = 16%nat -> 0 <= i < 16 -> P (slot_at E i).
Proof. intros P E i FA L Hi. unfold slot_at. eapply (proj1 (Forall_forall _ _) FA). apply nth_In. lia. Qed.

(* [comment removed for export] *)
Lemma zero16_byte : forall m A i, u32arr asegs m A zero16 -> 0 <= i < 16 -> ov_read_bytes asegs m (wa (A + 4 * i)) 1 = Some [b8 0].
Proof.
  intros m A i [HB _] Hi.
  replace (4 * i) with (Z.of_nat (4 * Z.to_nat i)) by lia.
  rewrite (bytes_at_ov_read asegs m A (u32s zero16) (4 * Z.to_nat i) 1 HB) by (rewrite u32s_length; cbn; lia).
  assert (C : (Z.to_nat i < 16)%nat) by lia. revert C. generalize (Z.to_nat i). intros k Hk.
  do 16 (destruct k as [|k]; [reflexivity|]). lia.
Qed.

(* [comment removed for export] *)
Lemma u64arr_read_m : forall m A ws i w, u64arr asegs m A ws -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i ->
  ov_read_bytes asegs m (wa (A + i * 8)) 8 = Some (le8 w).
Proof. intros m A ws i w H N Hi. eapply u64arr_read; [exact H| exact N| exact Hi|]. f_equal. lia. Qed.
Lemma u64arr_store_ok_m : forall m A ws i, u64arr asegs m A ws -> 0 <= i < Z.of_nat (length ws) -> store_ok asegs m (wa (A + i * 8)) 8 = true.
Proof. intros m A ws i H Hi. eapply u64arr_store_ok; [exact H| exact Hi|]. f_equal. lia. Qed.
Lemma u64arr_write_m : forall m A ws i (v : word), u64arr asegs m A ws -> 0 <= i < Z.of_nat (length ws) ->
  u64arr asegs (write_to_mem m (wa (A + i * 8)) (le8 v)) A (upd ws (Z.to_nat i) v).
Proof. intros m A ws i v H Hi. replace (A + i * 8) with (A + 8 * i) by lia. apply u64arr_write; assumption. Qed.
Lemma u32arr_read_m : forall m A ws i w, u32arr asegs m A ws -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i ->
  ov_read_bytes asegs m (wa (A + i * 4)) 4 = Some (le4 w).
Proof. intros m A ws i w H N Hi. eapply u32arr_read; [exact H| exact N| exact Hi|]. f_equal. lia. Qed.
Lemma u32arr_store_ok_m : forall m A ws i, u32arr asegs m A ws -> 0 <= i < Z.of_nat (length ws) -> store_ok asegs m (wa (A + i * 4)) 4 = true.
Proof. intros m A ws i H Hi. eapply u32arr_store_ok; [exact H| exact Hi|]. f_equal. lia. Qed.
Lemma u32arr_write_m : forall m A ws i (v : word), u32arr asegs m A ws -> 0 <= i < Z.of_nat (length ws) ->
  u32arr asegs (write_to_mem m (wa (A + i * 4)) (le4 v)) A (upd ws (Z.to_nat i) v).
Proof. intros m A ws i v H Hi. replace (A + i * 4) with (A + 4 * i) by lia. apply u32arr_write; assumption. Qed.
Lemma zero16_byte_m : forall m A i, u32arr asegs m A zero16 -> 0 <= i < 16 -> ov_read_bytes asegs m (wa (A + i * 4)) 1 = Some [b8 0].
Proof. intros m A i H Hi. replace (A + i * 4) with (A + 4 * i) by lia. apply zero16_byte; assumption. Qed.

(* [comment removed for export] *)
Lemma err_pack_reg : forall lib reason, 0 < lib < 256 -> 0 < reason < 2^23 ->
  Z.lor (Z.shiftr (Z.shiftl lib 56 mod 18446744073709551616) 33) (reason mod 8388608) mod 4294967296 = ERR_PACK lib reason.
Proof.
  intros lib reason HL HR. unfold ERR_PACK.
  rewrite (Z.shiftl_mul_pow2 lib 56) by lia. rewrite (Z.mod_small (lib * 2 ^ 56)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. replace (2 ^ 56) with (2 ^ 23 * 2 ^ 33) by reflexivity. rewrite Z.mul_assoc, Z.div_mul by lia.
  rewrite (Z.mod_small reason) by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite (Z.mod_small lib) by lia.
  change 8388607 with (Z.ones 23). rewrite Z.land_ones by lia. rewrite (Z.mod_small reason) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  apply Z.mod_small. pose proof (lor_lt_pow2 (lib * 2 ^ 23) reason 31 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma err_pack_range : forall lib reason, 0 < lib < 256 -> 0 < reason < 2^23 -> 0 <= ERR_PACK lib reason < 2^31.
Proof.
  intros lib reason HL HR. unfold ERR_PACK.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite (Z.mod_small lib) by lia.
  change 8388607 with (Z.ones 23). rewrite Z.land_ones by lia. rewrite (Z.mod_small reason) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. apply lor_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ERRSTm (m : mem) (a : Z) (E : errst) : Prop :=
  length (es_slots E) = 16%nat /\ 0 <= es_top E < 16 /\ 0 <= es_bottom E < 16
  /\ u32arr asegs m a (map (fun s => wz (sl_flags s)) (es_slots E))
  /\ u32arr asegs m (a + O_ES_MARKS) zero16
  /\ u64arr asegs m (a + O_ES_BUFFER) (map (fun s => wz (sl_buffer s)) (es_slots E))
  /\ u64arr asegs m (a + O_ES_DATA) zero16
  /\ u64arr asegs m (a + O_ES_DSIZE) zero16
  /\ u32arr asegs m (a + O_ES_DFLAGS) zero16
  /\ u64arr asegs m (a + O_ES_FILE) (map (fun s => wz (sl_file s)) (es_slots E))
  /\ u32arr asegs m (a + O_ES_LINE) (map (fun s => wz (sl_line s)) (es_slots E))
  /\ u64arr asegs m (a + O_ES_FUNC) (map (fun s => wz (sl_func s)) (es_slots E))
  /\ rw_cells asegs m (a + O_ES_TOP) [C4 (wz (es_top E)); C4 (wz (es_bottom E))]
  /\ Forall (fun s => 0 <= sl_flags s < 2^32 /\ 0 <= sl_buffer s < 2^64 /\ 0 <= sl_line s < 2^32) (es_slots E).
Definition ERROWN (LB : list block) (E : errst) : Prop :=
  Forall (fun s => ofield LB (sl_file s) (sl_file_o s) /\ ofield LB (sl_func s) (sl_func_o s)) (es_slots E).

Lemma ERRST_split : forall LB m a E, ERRST LB m a E <-> ERRSTm m a E /\ ERROWN LB E.
Proof.
  intros LB m a E. unfold ERRST, ERRSTm, ERROWN. split.
  - intros (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & OWN).
    split; [repeat match goal with |- _ /\ _ => split end; try assumption; try lia|];
      (eapply Forall_impl; [| exact OWN]); cbn beta; intros s0 K; tauto.
  - intros [(SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG) OWN].
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    rewrite Forall_forall in *. intros s0 Hs. specialize (RG s0 Hs). specialize (OWN s0 Hs). tauto.
Qed.

Lemma ERRSTm_agree : forall (R : Z -> Prop) m m' a E,
  magree R m m' -> ERRSTm m a E -> (forall x, a <= x < a + ERRST_SIZE -> R x) -> ERRSTm m' a E.
Proof.
  intros R m m' a E AG H HR. unfold ERRSTm in *.
  destruct H as (L & T & B & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
  assert (L16 : forall (f : errslot -> word), length (map f (es_slots E)) = 16%nat) by (intros f; rewrite length_map; exact L).
  assert (Z16 : length zero16 = 16%nat) by reflexivity.
  unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP, ERRST_SIZE in *.
  repeat match goal with |- _ /\ _ => split end; try assumption;
    try first [ eapply u32arr_agree; [exact AG | eassumption | intros x Hx; apply HR; unfold in_range in *; rewrite ?L16, ?Z16 in Hx; lia]
          | eapply u64arr_agree; [exact AG | eassumption | intros x Hx; apply HR; unfold in_range in *; rewrite ?L16, ?Z16 in Hx; lia]
          | eapply rw_cells_agree; [exact AG | eassumption | intros x Hx; apply HR; unfold in_range in *; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; lia] ].
  all: lia.
Qed.

Lemma ERRSTm_munch : forall W m m' a E,
  ERRSTm m a E -> munch W m m' -> wmono asegs m m' -> disjoint_from W a ERRST_SIZE -> ERRSTm m' a E.
Proof.
  intros W m m' a E H MU WM DJ. eapply ERRSTm_agree with (R := fun x => a <= x < a + ERRST_SIZE); [| exact H| intros x Hx; exact Hx].
  eapply magree_of_munch; [exact MU| exact WM|]. intros x Hr. eapply disjoint_outside; [exact DJ| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma ERRSTm_xpres : forall (H : asr) LB SP X m m' a E,
  ERRSTm m a E -> xpres H LB SP X m m' -> (forall x, a <= x < a + ERRST_SIZE -> xclient H LB SP X x) -> 0 <= a -> a + ERRST_SIZE <= 2^64 ->
  ERRSTm m' a E.
Proof.
  intros H LB SP X m m' a E H0 XP HC A0 A1. eapply ERRSTm_agree with (R := fun x => a <= x < a + ERRST_SIZE); [| exact H0| intros x Hx; exact Hx].
  intros x Hx Hr. apply XP; [exact Hx| apply HC; exact Hr].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma skipn_cons_nth : forall {X} (l : list X) i d, (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof. intros X l. induction l as [|y l IH]; intros [|i] d Hi; cbn in *; try lia; [reflexivity| apply IH; lia]. Qed.

Definition blocks_slots (ss : list errslot) : list block := concat (map blocks_slot ss).
Lemma blocks_slots_split : forall ss i d, (i < length ss)%nat ->
  blocks_slots ss = blocks_slots (firstn i ss) ++ blocks_slot (nth i ss d) ++ blocks_slots (skipn (S i) ss).
Proof.
  intros ss i d Hi. unfold blocks_slots. rewrite <- (firstn_skipn i ss) at 1. rewrite (skipn_cons_nth ss i d Hi).
  rewrite map_app, concat_app. cbn [map concat]. reflexivity.
Qed.
Lemma blocks_slots_upd : forall ss i x,
  blocks_slots (slot_upd ss i x) = blocks_slots (firstn i ss) ++ blocks_slot x ++ blocks_slots (skipn (S i) ss).
Proof. intros ss i x. unfold blocks_slots, slot_upd. rewrite map_app, concat_app. cbn [map concat]. reflexivity. Qed.

(* [comment removed for export] *)
Lemma blocks_slots_clear_perm : forall ss i x d, (i < length ss)%nat ->
  Permutation (blocks_slots ss) (blocks_slot (nth i ss d) ++ blocks_slots (slot_upd ss i (slot_clear x))).
Proof.
  intros ss i x d Hi. rewrite (blocks_slots_split ss i d Hi), blocks_slots_upd. cbn [blocks_slot slot_clear sl_file sl_file_o sl_func sl_func_o blocks_of app].
  apply Permutation_app_swap_app.
Qed.
(* [comment removed for export] *)
Lemma blocks_slots_fill_perm : forall ss i x d, (i < length ss)%nat -> blocks_slot (nth i ss d) = [] ->
  Permutation (blocks_slot x ++ blocks_slots ss) (blocks_slots (slot_upd ss i x)).
Proof.
  intros ss i x d Hi HE. rewrite (blocks_slots_split ss i d Hi), blocks_slots_upd, HE. cbn [app].
  apply Permutation_app_swap_app.
Qed.
(* [comment removed for export] *)
Lemma blocks_slots_upd_same : forall ss i x d, (i < length ss)%nat -> blocks_slot x = blocks_slot (nth i ss d) ->
  blocks_slots (slot_upd ss i x) = blocks_slots ss.
Proof. intros ss i x d Hi HE. rewrite (blocks_slots_split ss i d Hi), blocks_slots_upd, HE. reflexivity. Qed.

Lemma blocks_ERRST_slots : forall E, blocks_ERRST E = blocks_slots (es_slots E).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ofield_blocks : forall ss s0, In s0 ss ->
  (forall P o, (P = sl_file s0 /\ o = sl_file_o s0) \/ (P = sl_func s0 /\ o = sl_func_o s0) -> forall LB0, ofield LB0 P o -> ofield (blocks_slots ss) P o).
Proof.
  intros ss s0 Hs P o HPo LB0 HF. destruct o as [[id n]|]; cbn in *; [| exact HF].
  destruct HF as (H1 & H2 & _). split; [exact H1|]. split; [exact H2|].
  unfold blocks_slots. apply in_concat. exists (blocks_slot s0). split; [apply in_map; exact Hs|].
  unfold blocks_slot. apply in_or_app. destruct HPo as [[-> E]|[-> E]]; [left| right]; rewrite <- E; cbn; left; reflexivity.
Qed.
Lemma ERROWN_carved : forall LB0 ss top bot, ERROWN LB0 (mkERRST ss top bot) -> ERROWN (blocks_slots ss) (mkERRST ss top bot).
Proof.
  intros LB0 ss top bot OWN. unfold ERROWN in *. cbn [es_slots] in *. rewrite Forall_forall in *. intros s0 Hs.
  destruct (OWN s0 Hs) as [O1 O2]. split.
  - eapply (ofield_blocks ss s0 Hs); [left; split; reflexivity| exact O1].
  - eapply (ofield_blocks ss s0 Hs); [right; split; reflexivity| exact O2].
Qed.
(* [comment removed for export] *)
Lemma ERROWN_upd : forall LB0 ss i x top bot top' bot',
  ERROWN LB0 (mkERRST ss top bot) ->
  (forall LBx, (forall b, In b (blocks_slot x) -> In b LBx) -> ofield LBx (sl_file x) (sl_file_o x) /\ ofield LBx (sl_func x) (sl_func_o x)) ->
  ERROWN (blocks_slots (slot_upd ss i x)) (mkERRST (slot_upd ss i x) top' bot').
Proof.
  intros LB0 ss i x top bot top' bot' OWN HX. unfold ERROWN in *. cbn [es_slots] in *. rewrite Forall_forall in *. intros s0 Hs.
  unfold slot_upd in Hs. apply in_app_or in Hs.
  assert (IN : In s0 (slot_upd ss i x)) by (unfold slot_upd; apply in_or_app; destruct Hs as [Hs|Hs]; [left; exact Hs| right; exact Hs]).
  destruct Hs as [Hs|[<-|Hs]].
  - destruct (OWN s0 (in_firstn_in _ _ _ Hs)) as [O1 O2]. split.
    + eapply (ofield_blocks _ s0 IN); [left; split; reflexivity| exact O1].
    + eapply (ofield_blocks _ s0 IN); [right; split; reflexivity| exact O2].
  - apply HX. intros b Hb. unfold blocks_slots. apply in_concat. exists (blocks_slot x). split; [apply in_map; exact IN| exact Hb].
  - destruct (OWN s0 (in_skipn_in _ _ _ Hs)) as [O1 O2]. split.
    + eapply (ofield_blocks _ s0 IN); [left; split; reflexivity| exact O1].
    + eapply (ofield_blocks _ s0 IN); [right; split; reflexivity| exact O2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition es_with_slot (E : errst) (t : Z) (x : errslot) : errst :=
  mkERRST (slot_upd (es_slots E) (Z.to_nat t) x) (es_top E) (es_bottom E).
Definition slot_wipe (s : errslot) : errslot := mkSLOT 0 0 (sl_file s) (sl_file_o s) (2^32 - 1) (sl_func s) (sl_func_o s).
Definition slot_file0 (s : errslot) : errslot := mkSLOT (sl_flags s) (sl_buffer s) 0 None (sl_line s) (sl_func s) (sl_func_o s).
Definition slot_func0 (s : errslot) : errslot := mkSLOT (sl_flags s) (sl_buffer s) (sl_file s) (sl_file_o s) (sl_line s) 0 None.

Definition slot_setfile (s : errslot) (f : Z) (fo : oblk) (line : Z) : errslot :=
  mkSLOT (sl_flags s) (sl_buffer s) f fo line (sl_func s) (sl_func_o s).
Definition slot_setfunc (s : errslot) (g : Z) (go : oblk) : errslot :=
  mkSLOT (sl_flags s) (sl_buffer s) (sl_file s) (sl_file_o s) (sl_line s) g go.

Lemma slot_upd_twice : forall ss i x y, (i < length ss)%nat -> slot_upd (slot_upd ss i x) i y = slot_upd ss i y.
Proof.
  intros ss i x y Hi. unfold slot_upd.
  assert (L : length (firstn i ss) = i) by (rewrite length_firstn; lia).
  rewrite firstn_app, L, Nat.sub_diag, firstn_O, app_nil_r. rewrite (firstn_all2 (n := i)) by lia.
  f_equal. f_equal. rewrite skipn_app, L. rewrite (skipn_all2 (firstn i ss)) by lia.
  replace (S i - i)%nat with 1%nat by lia. reflexivity.
Qed.
Lemma slot_at_upd : forall E t x, length (es_slots E) = 16%nat -> 0 <= t < 16 -> slot_at (es_with_slot E t x) t = x.
Proof.
  intros E t x L Ht. unfold slot_at, es_with_slot, slot_upd. cbn [es_slots].
  assert (LF : length (firstn (Z.to_nat t) (es_slots E)) = Z.to_nat t) by (rewrite length_firstn; lia).
  rewrite app_nth2 by lia. rewrite LF, Nat.sub_diag. reflexivity.
Qed.
Lemma es_with_slot_twice : forall E t x y, length (es_slots E) = 16%nat -> 0 <= t < 16 ->
  es_with_slot (es_with_slot E t x) t y = es_with_slot E t y.
Proof. intros E t x y L Ht. unfold es_with_slot. cbn [es_slots es_top es_bottom]. rewrite slot_upd_twice by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma u32s_upd_le4 : forall ws i (v v' : word), le4 v = le4 v' -> u32s (upd ws i v) = u32s (upd ws i v').
Proof.
  induction ws as [|w ws IH]; intros [|i] v v' E; cbn [upd u32s]; try reflexivity; [rewrite E; reflexivity| rewrite (IH i v v' E); reflexivity].
Qed.
Lemma u32arr_upd_le4 : forall m A ws i (v v' : word), le4 v = le4 v' -> u32arr asegs m A (upd ws i v) -> u32arr asegs m A (upd ws i v').
Proof. intros m A ws i v v' E [HB HW]. split; [rewrite <- (u32s_upd_le4 ws i v v' E); exact HB| rewrite upd_length in *; exact HW]. Qed.
Lemma le4_minus1 : le4 (Z_to_bv 64 (-1)) = le4 (wz (2^32 - 1)).
Proof. unfold wz. apply le4_congr. reflexivity. Qed.

(* [comment removed for export] *)
Lemma upd_keep : forall E t {X} (f : errslot -> X) x, length (es_slots E) = 16%nat -> 0 <= t < 16 -> f x = f (slot_at E t) ->
  map f (es_slots E) = upd (map f (es_slots E)) (Z.to_nat t) (f x).
Proof. intros E t X f x L Ht EQ. symmetry. apply upd_same. rewrite EQ. apply slot_nth; assumption. Qed.
Lemma ERRSTm_with_slot : forall m a E t x w1 w3 w7 w8 w9,
  length (es_slots E) = 16%nat -> 0 <= t < 16 -> 0 <= es_top E < 16 -> 0 <= es_bottom E < 16 ->
  u32arr asegs m a w1 -> w1 = upd (map (fun s => wz (sl_flags s)) (es_slots E)) (Z.to_nat t) (wz (sl_flags x)) ->
  u32arr asegs m (a + 64) zero16 ->
  u64arr asegs m (a + 128) w3 -> w3 = upd (map (fun s => wz (sl_buffer s)) (es_slots E)) (Z.to_nat t) (wz (sl_buffer x)) ->
  u64arr asegs m (a + 256) zero16 -> u64arr asegs m (a + 384) zero16 -> u32arr asegs m (a + 512) zero16 ->
  u64arr asegs m (a + 576) w7 -> w7 = upd (map (fun s => wz (sl_file s)) (es_slots E)) (Z.to_nat t) (wz (sl_file x)) ->
  u32arr asegs m (a + 704) w8 -> w8 = upd (map (fun s => wz (sl_line s)) (es_slots E)) (Z.to_nat t) (wz (sl_line x)) ->
  u64arr asegs m (a + 768) w9 -> w9 = upd (map (fun s => wz (sl_func s)) (es_slots E)) (Z.to_nat t) (wz (sl_func x)) ->
  rw_cells asegs m (a + 896) [C4 (wz (es_top E)); C4 (wz (es_bottom E))] ->
  Forall (fun s => 0 <= sl_flags s < 2^32 /\ 0 <= sl_buffer s < 2^64 /\ 0 <= sl_line s < 2^32) (es_slots E) ->
  0 <= sl_flags x < 2^32 -> 0 <= sl_buffer x < 2^64 -> 0 <= sl_line x < 2^32 ->
  ERRSTm m a (es_with_slot E t x).
Proof.
  intros m a E t x w1 w3 w7 w8 w9 L Ht TR BR F1 E1 F2 F3 E3 F4 F5 F6 F7 E7 F8 E8 F9 E9 TB RG X1 X2 X3. subst w1 w3 w7 w8 w9.
  assert (TN : (Z.to_nat t < length (es_slots E))%nat) by lia.
  unfold ERRSTm, es_with_slot. cbn [es_slots es_top es_bottom].
  unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP.
  rewrite !map_slot_upd by exact TN.
  split; [rewrite slot_upd_length by exact TN; exact L|]. split; [exact TR|]. split; [exact BR|].
  repeat match goal with |- _ /\ _ => split end; try assumption.
  apply own_slot_upd; [exact RG| repeat split; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition clr_slots (ss : list errslot) (i : nat) : list errslot := map (fun _ => slot_clear (2^32 - 1)) (firstn i ss) ++ skipn i ss.
Definition clr (E : errst) (i : Z) : errst := mkERRST (clr_slots (es_slots E) (Z.to_nat i)) (es_top E) (es_bottom E).

Lemma clr_slots_length : forall ss i, length (clr_slots ss i) = length ss.
Proof. intros ss i. unfold clr_slots. rewrite length_app, length_map. rewrite <- (firstn_skipn i ss) at 3. rewrite length_app. reflexivity. Qed.
Lemma clr_slots_0 : forall ss, clr_slots ss 0 = ss.
Proof. reflexivity. Qed.
Lemma clr_slots_nth : forall ss i d, (i < length ss)%nat -> nth i (clr_slots ss i) d = nth i ss d.
Proof.
  intros ss i d Hi. unfold clr_slots. assert (L : length (map (fun _ : errslot => slot_clear (2 ^ 32 - 1)) (firstn i ss)) = i) by (rewrite length_map, length_firstn; lia).
  rewrite app_nth2 by lia. rewrite L, Nat.sub_diag. rewrite (skipn_cons_nth ss i d Hi). reflexivity.
Qed.
Lemma firstn_S_snoc : forall {X} (l : list X) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof. intros X l. induction l as [|y l IH]; intros [|i] d Hi; cbn in *; try lia; [reflexivity| rewrite (IH i d) by lia; reflexivity]. Qed.
Lemma clr_slots_step : forall ss i, (i < length ss)%nat -> slot_upd (clr_slots ss i) i (slot_clear (2^32 - 1)) = clr_slots ss (S i).
Proof.
  intros ss i Hi. unfold slot_upd, clr_slots.
  assert (L : length (map (fun _ : errslot => slot_clear (2 ^ 32 - 1)) (firstn i ss)) = i) by (rewrite length_map, length_firstn; lia).
  rewrite firstn_app, L, Nat.sub_diag, firstn_O, app_nil_r. rewrite (firstn_all2 (n := i)) by lia.
  rewrite skipn_app, L. rewrite (skipn_all2 (map _ _)) by lia. replace (S i - i)%nat with 1%nat by lia. cbn [app].
  rewrite (skipn_cons_nth ss i (slot_clear 0) Hi). cbn [skipn].
  rewrite (firstn_S_snoc ss i (slot_clear 0) Hi). rewrite map_app. cbn [map]. rewrite <- app_assoc. reflexivity.
Qed.
Lemma clr_slots_all : forall ss, clr_slots ss (length ss) = repeat (slot_clear (2^32 - 1)) (length ss).
Proof.
  intros ss. unfold clr_slots. rewrite firstn_all, skipn_all, app_nil_r. induction ss as [|y ss IH]; [reflexivity|]. cbn [map length repeat]. rewrite IH. reflexivity.
Qed.
Lemma blocks_clr_slots : forall ss i, blocks_slots (clr_slots ss i) = blocks_slots (skipn i ss).
Proof.
  intros ss i. unfold clr_slots, blocks_slots. rewrite map_app, concat_app.
  assert (Z : forall l : list errslot, concat (map blocks_slot (map (fun _ : errslot => slot_clear (2 ^ 32 - 1)) l)) = []) by (induction l as [|y l IH]; [reflexivity| cbn; exact IH]).
  rewrite Z. reflexivity.
Qed.
Lemma slot_at_clr : forall E i, length (es_slots E) = 16%nat -> 0 <= i < 16 -> slot_at (clr E i) i = slot_at E i.
Proof. intros E i L Hi. unfold slot_at, clr. cbn [es_slots]. apply clr_slots_nth. lia. Qed.
Lemma clr_step : forall E i, length (es_slots E) = 16%nat -> 0 <= i < 16 -> es_with_slot (clr E i) i (slot_clear (2^32 - 1)) = clr E (i + 1).
Proof.
  intros E i L Hi. unfold es_with_slot, clr. cbn [es_slots es_top es_bottom]. rewrite clr_slots_step by lia.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac cases16 t :=
  let C := fresh "C" in
  assert (C : t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8 \/ t = 9 \/ t = 10 \/ t = 11
              \/ t = 12 \/ t = 13 \/ t = 14 \/ t = 15) by lia;
  repeat (destruct C as [C|C]; [subst t|]); [..| subst t].
Lemma err_next_reg : forall t, 0 <= t < 16 ->
  bv_swrap 32 (t + 1 - Z.land ((t + 1 + bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (t + 1)) 31) mod 18446744073709551616)) 28))
                               mod 18446744073709551616) 18446744073709551600) = err_next t.
Proof. intros t Ht. cases16 t; vm_compute; reflexivity. Qed.
Lemma err_next_reg8 : forall t, 0 <= t < 16 ->
  Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl
     (bv_swrap 32 (t + 1 - Z.land ((t + 1 + Z.shiftr (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (t + 1) 56))) 3 mod 18446744073709551616) 60)
                                   mod 18446744073709551616) 240) mod 18446744073709551616) 56))) 56 = err_next t.
Proof. intros t Ht. cases16 t; vm_compute; reflexivity. Qed.
Lemma err_next_range : forall t, 0 <= t < 16 -> 0 <= err_next t < 16.
Proof. intros t Ht. unfold err_next. apply Z.mod_pos_bound. lia. Qed.

End HCW.

(* [comment removed for export] *)
Ltac arr_lens SL :=
  repeat match goal with
  | H : u32arr _ _ _ ?ws |- _ =>
      lazymatch goal with _ : length ws = 16%nat |- _ => fail | _ => idtac end;
      assert (length ws = 16%nat) by (first [reflexivity | rewrite ?upd_length, length_map; exact SL])
  | H : u64arr _ _ _ ?ws |- _ =>
      lazymatch goal with _ : length ws = 16%nat |- _ => fail | _ => idtac end;
      assert (length ws = 16%nat) by (first [reflexivity | rewrite ?upd_length, length_map; exact SL])
  end.

(* [comment removed for export] *)
Ltac arr_store_sync Fw :=
  lazymatch type of Fw with context [write_to_mem ?m (wa ?E) ?bs'] =>
    lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem m ?a ?bs) ?ro) =>
      first [ change (evt segs Q (MS R F pc fc rv (write_to_mem m (wa E) bs') ro))
            | replace (write_to_mem m a bs) with (write_to_mem m (wa E) bs') by (f_equal; [unfold wa; f_equal; lia | reflexivity]) ]
    end end.

(* [comment removed for export] *)
Ltac arr_store64 F i v :=
  let SOK := fresh "SOK" in
  pose proof (u64arr_store_ok_m _ _ _ i F ltac:(lia)) as SOK;
  step;
  let Fw := fresh "Fw" in
  pose proof (u64arr_write_m _ _ _ i v F ltac:(lia)) as Fw; clear F; arr_store_sync Fw;
  store_done; rename Fw into F.
Ltac arr_store32 F i v :=
  let SOK := fresh "SOK" in
  pose proof (u32arr_store_ok_m _ _ _ i F ltac:(lia)) as SOK;
  step;
  let Fw := fresh "Fw" in
  pose proof (u32arr_write_m _ _ _ i v F ltac:(lia)) as Fw; clear F; arr_store_sync Fw;
  store_done; rename Fw into F.

(* [comment removed for export] *)
Ltac shl_norm :=
  repeat match goal with
  | |- context [Z.shiftl ?x 3] => rewrite (Z.shiftl_mul_pow2 x 3) by lia; change (2 ^ 3) with 8
  | |- context [Z.shiftl ?x 2] => rewrite (Z.shiftl_mul_pow2 x 2) by lia; change (2 ^ 2) with 4
  end.

(* [comment removed for export] *)
Ltac upd_keep_tac E t SL TR :=
  first [ apply (upd_keep E t (fun s => wz (sl_flags s))); [exact SL| exact TR| reflexivity]
        | apply (upd_keep E t (fun s => wz (sl_buffer s))); [exact SL| exact TR| reflexivity]
        | apply (upd_keep E t (fun s => wz (sl_file s))); [exact SL| exact TR| reflexivity]
        | apply (upd_keep E t (fun s => wz (sl_line s))); [exact SL| exact TR| reflexivity]
        | apply (upd_keep E t (fun s => wz (sl_func s))); [exact SL| exact TR| reflexivity] ].

From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ECH_AsKit.
Ltac has_var c := match c with context [?x] => is_var x end.
Ltac if_lit_strict := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      tryif has_var c then fail else
      let v := eval vm_compute in c in
      lazymatch v with true => idtac | false => idtac end;
      replace c with v by (vm_compute; reflexivity); cbv iota end.
Ltac ubal_any :=
  repeat match goal with
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 7] => rewrite (al8u x) by (first [assumption | lia])
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 3] => rewrite (al4u x) by (first [assumption | lia])
  | |- context [Z.land ?x 7] => rewrite (al8 x) by (first [assumption | lia])
  | |- context [Z.land ?x 3] => rewrite (al4 x) by (first [assumption | lia])
  end.
Ltac ub_A_any :=
  let KU := fresh "KU" in
  if_cases KU; zify_cond KU;
  [ clear KU
  | exfalso; revert KU; rewrite ?unsigned_lit, ?signed_lit by lia; intros KU; lia ].
Ltac ub_al := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      lazymatch c with context [Z.land _ _] => progress ubal_any; if_lit_strict end end.
Ltac ub_norm := rewrite ?sx32_wz by lia; rewrite ?zb_lxor_ones by lia; shl_norm.
Ltac ub_res := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      first [ if_lit_strict | ub_al | ub_dead | ub_A_any | (progress ub_norm; first [if_lit_strict | ub_dead | ub_A_any]) ] end.
Ltac at_ctl := lazymatch goal with |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with Some ?w => let d := eval vm_compute in (decode_any w) in
    lazymatch d with
    | Some (Jalr _ _ _, _) => idtac
    | Some (Jal ?rd ?imm, _) => let z := eval vm_compute in (Z.eqb (bv_unsigned rd) 0 && Z.ltb (Z.abs (bv_signed imm)) 4096)%bool in
        lazymatch z with true => fail | false => idtac end
    | _ => fail end end end.
Ltac bst := first [ ub_res | (tryif at_ctl then fail else st1) ].
Ltac bgo_n n := lazymatch n with O => idtac | S ?k => tryif (progress bst) then bgo_n k else idtac end.
Ltac bgo := bgo_n 80%nat.
Ltac at_pc P := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => let b := eval vm_compute in (Z.eqb pc P) in lazymatch b with true => idtac | false => fail end end.
Ltac bgo_to_n P n := lazymatch n with O => idtac | S ?k => tryif at_pc P then idtac else (tryif (progress bst) then bgo_to_n P k else idtac) end.
Ltac bgo_to P := bgo_to_n P 200%nat.
Ltac sh_align a := try (lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
  match R with context [Z.shiftr ?x 3] => tryif constr_eq x a then fail else replace x with a by lia end end).
