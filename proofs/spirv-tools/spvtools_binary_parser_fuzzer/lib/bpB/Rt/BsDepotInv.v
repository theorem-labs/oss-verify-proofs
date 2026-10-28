(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BZBridge BellsX BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Notation DEP        := 2567960 (only parsing).
Notation DEP_NUI    := 6762264 (only parsing).
Notation DEP_MAP1   := 6762280 (only parsing).
Notation SSB        := 2502408 (only parsing).
Notation SSB_DATA   := 2502424 (only parsing).
Notation SSB_STORED := 2502432 (only parsing).
Notation LIM_IDS    := 65536 (only parsing).
Notation LIM_FRAMES := 32768 (only parsing).
Notation MASK20     := 1048575 (only parsing).
Definition bucket (h : Z) : Z := Z.land h MASK20.

Lemma bucket_range : forall h, 0 <= bucket h < 2^20.
Proof.
  intros h. unfold bucket. change 1048575 with (Z.ones 20). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

Record depot : Type := mkDepot {
  d_ids : Z; d_frames : Z; d_hash : Z -> Z; d_chain : Z -> list Z; d_nb : Z; d_sb : Z }.

Fixpoint link_of (l : list Z) (id : Z) : Z :=
  match l with
  | [] => 0
  | x :: rest => if x =? id then hd 0 rest else link_of rest id
  end.

Fixpoint find_hash (hs : Z -> Z) (h : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: rest => if hs x =? h then x else find_hash hs h rest
  end.

Definition d_find (d : depot) (h : Z) : Z := find_hash (d_hash d) h (d_chain d (bucket h)).

Definition d_insert (d : depot) (h n : Z) : depot :=
  mkDepot (d_ids d + 1) (d_frames d + n + 1)
          (fun id => if id =? d_ids d + 1 then h else d_hash d id)
          (fun b => if b =? bucket h then (d_ids d + 1) :: d_chain d b else d_chain d b)
          (d_nb d) (d_sb d).

Definition d_put (d : depot) (h n : Z) : depot := if d_find d h =? 0 then d_insert d h n else d.
Definition d_putid (d : depot) (h : Z) : Z := if d_find d h =? 0 then d_ids d + 1 else d_find d h.

Definition idseq (k : Z) : list Z := map Z.of_nat (seq 1 (Z.to_nat k)).
Definition d_K (d : depot) : list Z := map (d_hash d) (idseq (d_ids d)).

Record d_wf (d : depot) : Prop := mkWf {
  wf_ids    : 1 <= d_ids d < LIM_IDS;
  wf_frames : 0 <= d_frames d <= LIM_FRAMES;
  wf_hash   : forall id, 1 <= id <= d_ids d -> 0 <= d_hash d id < 2^64;
  wf_in     : forall id, 1 <= id <= d_ids d -> In id (d_chain d (bucket (d_hash d id)));
  wf_chain  : forall b id, In id (d_chain d b) -> 1 <= id <= d_ids d /\ bucket (d_hash d id) = b;
  wf_nodup  : forall b, List.NoDup (d_chain d b);
  wf_nb     : AIMG_TOP <= d_nb d /\ d_nb d + 16 * LIM_IDS <= 2^47;
  wf_sb     : AIMG_TOP <= d_sb d /\ d_sb d + 8 * LIM_FRAMES <= 2^47;
  wf_nbsb   : d_nb d + 16 * LIM_IDS <= d_sb d \/ d_sb d + 8 * LIM_FRAMES <= d_nb d
}.

Section Cells.
Variable segs : list Segment.

Record depot_mem (d : depot) (m : word -> option byte) : Prop := mkDM {
  dm_tab   : forall b, 0 <= b < 2^20 -> rw_cells segs m (DEP + 4 * b) [C4 (wz (hd 0 (d_chain d b)))];
  dm_nui   : rw_cells segs m DEP_NUI [C4 (wz (d_ids d))];
  dm_map1  : rw_cells segs m DEP_MAP1 [C8 (wz (d_nb d))];
  dm_node  : forall id, 1 <= id <= d_ids d ->
               rw_cells segs m (d_nb d + 16 * id) [C8 (wz (d_hash d id)); C4 (wz (link_of (d_chain d (bucket (d_hash d id))) id))];
  dm_sid   : forall id, 1 <= id <= d_ids d -> exists sid, rw_cells segs m (d_nb d + 16 * id + 12) [C4 sid];
  dm_free  : forall id, d_ids d < id < LIM_IDS -> exists j1 j2 j3, rw_cells segs m (d_nb d + 16 * id) [C8 j1; C4 j2; C4 j3];
  dm_tf    : rw_cells segs m SSB [C8 (wz (d_frames d))];
  dm_data  : rw_cells segs m SSB_DATA [C8 (wz (d_sb d))];
  dm_stored: rw_cells segs m SSB_STORED [C4 (wz (d_frames d))];
  dm_space : exists junk, u8arr segs m (d_sb d + 8 * d_frames d) junk /\ Z.of_nat (length junk) = 8 * (LIM_FRAMES - d_frames d)
}.

Definition DEPOT (d : depot) (m : word -> option byte) : Prop := d_wf d /\ depot_mem d m.

Definition depot_W (d : depot) : list ivl :=
  [(DEP, DEP_MAP1 + 8); (SSB, SSB + 28); (d_nb d, d_nb d + 16 * LIM_IDS); (d_sb d, d_sb d + 8 * LIM_FRAMES)].

End Cells.

Lemma in_idseq : forall k id, In id (idseq k) <-> 1 <= id <= k.
Proof.
  intros k id. unfold idseq. rewrite in_map_iff. split.
  - intros (x & <- & Hx). apply in_seq in Hx. lia.
  - intros H. exists (Z.to_nat id). split; [lia|]. apply in_seq. lia.
Qed.

Lemma in_d_K : forall d h, In h (d_K d) <-> exists id, 1 <= id <= d_ids d /\ d_hash d id = h.
Proof.
  intros d h. unfold d_K. rewrite in_map_iff. split.
  - intros (id & E & Hin). apply in_idseq in Hin. exists id. auto.
  - intros (id & Hid & E). exists id. split; [exact E|]. apply in_idseq. exact Hid.
Qed.

Lemma find_hash_some : forall hs h l, find_hash hs h l <> 0 -> ~ In 0 l -> In (find_hash hs h l) l /\ hs (find_hash hs h l) = h.
Proof.
  induction l as [|x l IH]; intros H N0; cbn in *. { congruence. }
  destruct (Z.eqb_spec (hs x) h).
  - auto.
  - destruct (IH H) as [A B]. { tauto. } auto.
Qed.

Lemma find_hash_none : forall hs h l, find_hash hs h l = 0 -> ~ In 0 l -> forall x, In x l -> hs x <> h.
Proof.
  induction l as [|y l IH]; intros H N0 x Hx; cbn in *. { tauto. }
  destruct (Z.eqb_spec (hs y) h). { subst. exfalso. tauto. }
  destruct Hx as [<-|Hx]; [assumption|]. apply IH; tauto.
Qed.

Lemma find_hash_app_skip : forall hs h l1 l2, (forall x, In x l1 -> hs x <> h) -> find_hash hs h (l1 ++ l2) = find_hash hs h l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2 H; cbn. { reflexivity. }
  destruct (Z.eqb_spec (hs x) h). { exfalso. apply (H x); cbn; auto. }
  apply IH. intros y Hy. apply H. cbn; auto.
Qed.

Lemma chain_no0 : forall d b, d_wf d -> ~ In 0 (d_chain d b).
Proof. intros d b W H. pose proof (wf_chain d W b 0 H). lia. Qed.

Lemma d_find_K : forall d h, d_wf d -> (d_find d h <> 0 <-> In h (d_K d)).
Proof.
  intros d h W. unfold d_find. split.
  - intros H. destruct (find_hash_some _ _ _ H (chain_no0 d _ W)) as [A B].
    apply in_d_K. exists (find_hash (d_hash d) h (d_chain d (bucket h))). split; [|exact B].
    apply (wf_chain d W (bucket h)). exact A.
  - intros H E. apply in_d_K in H. destruct H as (id & Hid & Hh).
    pose proof (wf_in d W id Hid) as I. rewrite Hh in I.
    exact (find_hash_none _ _ _ E (chain_no0 d _ W) id I Hh).
Qed.

Lemma d_find_range : forall d h, d_wf d -> d_find d h <> 0 -> 1 <= d_find d h <= d_ids d /\ d_hash d (d_find d h) = h.
Proof.
  intros d h W H. unfold d_find in *. destruct (find_hash_some _ _ _ H (chain_no0 d _ W)) as [A B].
  split; [|exact B]. apply (wf_chain d W (bucket h)). exact A.
Qed.

Lemma chain_hd_range : forall d b, d_wf d -> 0 <= hd 0 (d_chain d b) <= d_ids d.
Proof.
  intros d b W. destruct (d_chain d b) as [|x l] eqn:E; cbn. { pose proof (wf_ids d W). lia. }
  assert (In x (d_chain d b)) by (rewrite E; left; reflexivity). pose proof (wf_chain d W b x H). lia.
Qed.

Lemma link_of_app : forall l1 i l2, ~ In i l1 -> link_of (l1 ++ i :: l2) i = hd 0 l2.
Proof.
  induction l1 as [|x l1 IH]; intros i l2 H; cbn. { rewrite Z.eqb_refl. reflexivity. }
  destruct (Z.eqb_spec x i). { exfalso. apply H. cbn. auto. }
  apply IH. intros I. apply H. cbn. auto.
Qed.

Lemma link_of_cons_other : forall x l i, x <> i -> link_of (x :: l) i = link_of l i.
Proof. intros. cbn. destruct (Z.eqb_spec x i); [contradiction|reflexivity]. Qed.

Lemma NoDup_app_cons : forall (l1 : list Z) x l2, List.NoDup (l1 ++ x :: l2) -> ~ In x l1 /\ List.NoDup (l1 ++ l2).
Proof.
  intros l1 x l2 H. split.
  - intros I. apply NoDup_remove_2 in H. apply H. apply in_or_app. auto.
  - apply NoDup_remove_1 in H. exact H.
Qed.

Lemma d_insert_wf : forall d h n, d_wf d -> d_find d h = 0 -> 0 <= h < 2^64 -> 0 <= n ->
  d_ids d + 1 < LIM_IDS -> d_frames d + n + 1 <= LIM_FRAMES -> d_wf (d_insert d h n).
Proof.
  intros d h n W NF Hh Hn CI CF. pose proof W as [I1 I2 I3 I4 I5 I6 I7 I8 I9].
  constructor; cbn; try assumption; try lia.
  - intros id Hid. destruct (Z.eqb_spec id (d_ids d + 1)); [lia|]. apply I3. lia.
  - intros id Hid. destruct (Z.eqb_spec id (d_ids d + 1)).
    + rewrite Z.eqb_refl. cbn. auto.
    + destruct (Z.eqb_spec (bucket (d_hash d id)) (bucket h)); [cbn; right|]; apply I4; lia.
  - intros b id Hin. destruct (Z.eqb_spec b (bucket h)).
    + destruct Hin as [<-|Hin]. { rewrite Z.eqb_refl. lia. }
      pose proof (I5 b id Hin) as [A B]. destruct (Z.eqb_spec id (d_ids d + 1)); lia.
    + pose proof (I5 b id Hin) as [A B]. destruct (Z.eqb_spec id (d_ids d + 1)); lia.
  - intros b. destruct (Z.eqb_spec b (bucket h)); [|apply I6].
    constructor; [|apply I6]. intros Hin. pose proof (I5 b _ Hin). lia.
Qed.

Lemma d_K_insert : forall d h n, 0 <= d_ids d -> d_K (d_insert d h n) = d_K d ++ [h].
Proof.
  intros d h n Hi. unfold d_K, idseq. cbn [d_ids d_hash d_insert].
  replace (Z.to_nat (d_ids d + 1)) with (Z.to_nat (d_ids d) + 1)%nat by lia.
  rewrite seq_app, !map_app. cbn [map seq]. f_equal.
  - apply map_ext_in. intros id Hin. apply in_idseq in Hin. destruct (Z.eqb_spec id (d_ids d + 1)); [lia|reflexivity].
  - replace (Z.of_nat (1 + Z.to_nat (d_ids d))) with (d_ids d + 1) by lia. rewrite Z.eqb_refl. reflexivity.
Qed.

Section MemHelpers.
Variable segs : list Segment.

Lemma u8arr_app : forall m A bs1 bs2,
  u8arr segs m A (bs1 ++ bs2) <-> u8arr segs m A bs1 /\ u8arr segs m (A + Z.of_nat (length bs1)) bs2.
Proof.
  intros m A bs1 bs2. unfold u8arr. rewrite length_app, Nat2Z.inj_add, bytes_at_app, wr_at_app by lia. tauto.
Qed.

Lemma u8arr_store_ok_n : forall m A bs (i : Z) (k : nat) a,
  u8arr segs m A bs -> 0 <= i -> i + Z.of_nat k <= Z.of_nat (length bs) -> a = wa (A + i) ->
  store_ok segs m a k = true.
Proof. intros m A bs i k a [_ Hw] Hi Hk ->. eapply wr_at_store_ok; eauto. Qed.

Lemma u8arr_write_n : forall m A bs (i : Z) (xs : list byte),
  u8arr segs m A bs -> 0 <= i -> i + Z.of_nat (length xs) <= Z.of_nat (length bs) ->
  u8arr segs (write_to_mem m (wa (A + i)) xs) A (upd_bytes bs (Z.to_nat i) xs).
Proof.
  intros m A bs i xs [Hb Hw] Hi Hl. split.
  - apply bytes_at_write_inside; [exact Hb|lia|lia].
  - rewrite upd_bytes_length by lia. apply wr_at_write. exact Hw.
Qed.

Lemma bytes_at_read1 : forall m A bs (k : Z) b a,
  bytes_at segs m A bs -> nth_error bs (Z.to_nat k) = Some b -> 0 <= k -> a = wa (A + k) ->
  ov_read_bytes segs m a 1 = Some [b].
Proof.
  intros m A bs k b a Hb Hn Hk ->. rewrite (bytes_at_read segs m A bs k 1 Hb Hk).
  2:{ pose proof (nth_error_lt _ _ _ Hn). lia. }
  f_equal. destruct (nth_error_split bs (Z.to_nat k) b Hn) as (l1 & l2 & -> & L).
  rewrite skipn_app, skipn_all2, L, Nat.sub_diag by lia. reflexivity.
Qed.

Lemma swrap32_small : forall z, (-2^31 <= z < 2^31)%Z -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma list_split3 : forall {X} (l : list X) (a b : nat), (a + b <= length l)%nat ->
  exists l1 l2 l3, l = l1 ++ l2 ++ l3 /\ length l1 = a /\ length l2 = b.
Proof.
  intros X l a b H. exists (firstn a l), (firstn b (skipn a l)), (skipn b (skipn a l)).
  split. { rewrite (firstn_skipn b (skipn a l)). symmetry. apply firstn_skipn. }
  split. { apply firstn_length_le. lia. } { apply firstn_length_le. rewrite length_skipn. lia. }
Qed.

Lemma u64arr_u8arr : forall m A ws, u64arr segs m A ws <-> u8arr segs m A (u64s ws).
Proof. intros. unfold u64arr, u8arr. rewrite u64s_length, Nat2Z.inj_mul. change (Z.of_nat 8) with 8. tauto. Qed.

Lemma Z_to_le_bytes_add : forall a b z, Z_to_le_bytes (a + b) z = Z_to_le_bytes a z ++ Z_to_le_bytes b (Z.shiftr z (8 * Z.of_nat a)).
Proof.
  induction a as [|a IH]; intros b z; cbn [Z_to_le_bytes Nat.add app].
  - rewrite Z.shiftr_0_r. reflexivity.
  - f_equal. rewrite IH. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma le8_le4_le4 : forall x, 0 <= x < 2^64 -> le8 (wz x) = le4 (wz x) ++ le4 (wz (Z.shiftr x 32)).
Proof.
  intros x Hx. unfold le8, le4, word_to_le_bytes, wz. rewrite !unsigned_lit; [|split; [apply Z.shiftr_nonneg; lia|]|lia].
  2:{ rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [lia|]. change (2^32*2^64) with (2^96). lia. }
  change 8%nat with (4 + 4)%nat at 1. rewrite Z_to_le_bytes_add. reflexivity.
Qed.

Lemma rw_cells_C8_C4C4 : forall m A pre x post, 0 <= x < 2^64 ->
  rw_cells segs m A (pre ++ C8 (wz x) :: post) <-> rw_cells segs m A (pre ++ C4 (wz x) :: C4 (wz (Z.shiftr x 32)) :: post).
Proof.
  intros m A pre x post Hx. unfold rw_cells, cells_at.
  rewrite !cells_wf_app, !cells_bytes_app, !cells_size_app. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite (le8_le4_le4 x Hx), <- app_assoc. cbn [app].
  replace (8 + cells_size post)%nat with (4 + (4 + cells_size post))%nat by lia. tauto.
Qed.

End MemHelpers.

Ltac head_of t := lazymatch t with ?h _ => head_of h | _ => t end.
Ltac post_callU segs m :=
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO;
  (let h := head_of ltac:(type of PO) in try unfold h in PO);
  rewrite ?unsigned_lit in PO by lia; rewrite ?Z.add_0_r in PO; revert ms' PO; post_call segs m.
Tactic Notation "callU" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callU segs m ]
  end.

Section DepotFrame.
Variable segs : list Segment.

Lemma depot_mem_stack : forall d m m' lo hi,
  d_wf d -> depot_mem segs d m -> munch [(lo, hi)] m m' -> wmono segs m m' ->
  DEP_MAP1 + 8 <= lo -> d_nb d + 16 * LIM_IDS <= lo -> d_sb d + 8 * LIM_FRAMES <= lo ->
  depot_mem segs d m'.
Proof.
  intros d m m' lo hi W DM MU WM L1 L2 L3.
  pose proof (wf_ids d W) as I1. pose proof (wf_frames d W) as I2. pose proof (wf_nb d W) as I3. pose proof (wf_sb d W) as I4.
  destruct DM as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10].
  constructor.
  - intros b Hb. eapply rw_cells_transport; [apply T1; exact Hb|exact MU|exact WM|]. cbn. lia.
  - eapply rw_cells_transport; [exact T2|exact MU|exact WM|]. cbn. lia.
  - eapply rw_cells_transport; [exact T3|exact MU|exact WM|]. cbn. lia.
  - intros id Hid. eapply rw_cells_transport; [apply T4; exact Hid|exact MU|exact WM|]. cbn. lia.
  - intros id Hid. destruct (T5 id Hid) as [sid H]. exists sid. eapply rw_cells_transport; [exact H|exact MU|exact WM|]. cbn. lia.
  - intros id Hid. destruct (T6 id Hid) as (j1 & j2 & j3 & H). exists j1, j2, j3. eapply rw_cells_transport; [exact H|exact MU|exact WM|]. cbn. lia.
  - eapply rw_cells_transport; [exact T7|exact MU|exact WM|]. cbn. lia.
  - eapply rw_cells_transport; [exact T8|exact MU|exact WM|]. cbn. lia.
  - eapply rw_cells_transport; [exact T9|exact MU|exact WM|]. cbn. lia.
  - destruct T10 as (junk & U & L). exists junk. split; [|exact L]. eapply u8arr_transport; [exact U|exact MU|exact WM|]. cbn. lia.
Qed.

Definition put_W (lo spv b0 nb id sb fr n : Z) : list ivl :=
  [(lo, spv); (DEP + 4 * b0, DEP + 4 * b0 + 4); (DEP_NUI, DEP_NUI + 4); (nb + 16 * id, nb + 16 * id + 16);
   (SSB, SSB + 8); (SSB_STORED, SSB_STORED + 4); (sb + 8 * fr, sb + 8 * fr + 8 * (n + 1))].

Lemma depot_insert_mem : forall d h n m m' lo spv sid junk,
  d_wf d -> depot_mem segs d m ->
  d_find d h = 0 -> 0 <= h < 2^64 -> 1 <= n -> d_ids d + 1 < LIM_IDS -> d_frames d + n + 1 <= LIM_FRAMES ->
  DEP_MAP1 + 8 <= lo -> d_nb d + 16 * LIM_IDS <= lo -> d_sb d + 8 * LIM_FRAMES <= lo ->
  munch (put_W lo spv (bucket h) (d_nb d) (d_ids d + 1) (d_sb d) (d_frames d) n) m m' -> wmono segs m m' ->
  rw_cells segs m' (DEP + 4 * bucket h) [C4 (wz (d_ids d + 1))] ->
  rw_cells segs m' DEP_NUI [C4 (wz (d_ids d + 1))] ->
  rw_cells segs m' (d_nb d + 16 * (d_ids d + 1)) [C8 (wz h); C4 (wz (hd 0 (d_chain d (bucket h)))); C4 sid] ->
  rw_cells segs m' SSB [C8 (wz (d_frames d + n + 1))] ->
  rw_cells segs m' SSB_STORED [C4 (wz (d_frames d + n + 1))] ->
  u8arr segs m' (d_sb d + 8 * d_frames d) junk -> Z.of_nat (length junk) = 8 * (LIM_FRAMES - d_frames d) ->
  depot_mem segs (d_insert d h n) m'.
Proof.
  intros d h n m m' lo spv sid junk W DM NF Hh Hn CI CF L1 L2 L3 MU WM TAB NUI ND TF STO SP LJ.
  pose proof (wf_ids d W) as I1. pose proof (wf_frames d W) as I2. pose proof (wf_nb d W) as I3. pose proof (wf_sb d W) as I4.
  pose proof (wf_nbsb d W) as I5. pose proof (bucket_range h) as BR.
  destruct DM as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10].
  unfold put_W in MU. unfold AIMG_TOP in *.
  constructor; cbn [d_insert d_ids d_frames d_hash d_chain d_nb d_sb].
  - intros b Hb. destruct (Z.eqb_spec b (bucket h)) as [->|NE]. { exact TAB. }
    eapply rw_cells_transport; [apply T1; exact Hb|exact MU|exact WM|]. cbn -[bucket]. lia.
  - exact NUI.
  - eapply rw_cells_transport; [exact T3|exact MU|exact WM|]. cbn -[bucket]. lia.
  - intros id Hid. destruct (Z.eqb_spec id (d_ids d + 1)) as [->|NE].
    + rewrite Z.eqb_refl. cbn [link_of]. rewrite Z.eqb_refl.
      apply (proj1 (rw_cells_app segs m' _ [C8 (wz h); C4 (wz (hd 0 (d_chain d (bucket h))))] [C4 sid])) in ND. apply ND.
    + assert (Hid' : 1 <= id <= d_ids d) by lia.
      assert (E : link_of (if bucket (d_hash d id) =? bucket h then d_ids d + 1 :: d_chain d (bucket (d_hash d id)) else d_chain d (bucket (d_hash d id))) id
                  = link_of (d_chain d (bucket (d_hash d id))) id).
      { destruct (Z.eqb_spec (bucket (d_hash d id)) (bucket h)); [|reflexivity]. apply link_of_cons_other. lia. }
      rewrite E. eapply rw_cells_transport; [apply T4; exact Hid'|exact MU|exact WM|]. cbn -[bucket]. lia.
  - intros id Hid. destruct (Z.eqb_spec id (d_ids d + 1)) as [->|NE].
    + exists sid. apply (proj1 (rw_cells_app segs m' _ [C8 (wz h); C4 (wz (hd 0 (d_chain d (bucket h))))] [C4 sid])) in ND.
      destruct ND as [_ ND]. cbn [cells_size csize Nat.add] in ND.
      replace (d_nb d + 16 * (d_ids d + 1) + Z.of_nat 12) with (d_nb d + 16 * (d_ids d + 1) + 12) in ND by lia. exact ND.
    + destruct (T5 id ltac:(lia)) as [sid' H]. exists sid'. eapply rw_cells_transport; [exact H|exact MU|exact WM|]. cbn -[bucket]. lia.
  - intros id Hid. destruct (T6 id ltac:(lia)) as (j1 & j2 & j3 & H). exists j1, j2, j3.
    eapply rw_cells_transport; [exact H|exact MU|exact WM|]. cbn -[bucket]. lia.
  - exact TF.
  - eapply rw_cells_transport; [exact T8|exact MU|exact WM|]. cbn -[bucket]. lia.
  - exact STO.
  - destruct (list_split3 junk (Z.to_nat (8 * (n + 1))) 0 ltac:(lia)) as (ja & jb & jc & EJ & LA & LB).
    destruct jb; [|cbn in LB; lia]. cbn [app] in EJ. subst junk.
    apply u8arr_app in SP. destruct SP as [_ SP]. rewrite length_app in LJ.
    exists jc. split.
    + replace (d_sb d + 8 * (d_frames d + n + 1)) with (d_sb d + 8 * d_frames d + Z.of_nat (length ja)) by lia. exact SP.
    + lia.
Qed.

End DepotFrame.
