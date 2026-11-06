(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK15 YN06 YK1b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI00 YI02 YI07 YP14 YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition LAY_RgbFrameConfig : layout_t := [(0, 8%N); (8, 4%N); (12, 4%N); (16, 4%N); (20, 2%N)].
Definition RGBFC_SIZE : Z := 24.
Definition RF_img := 0%nat. Definition RF_fmt := 1%nat. Definition RF_attr := 2%nat.
Definition RF_gen := 3%nat. Definition RF_delay := 4%nat.
Definition LAY_Node : layout_t :=
[(0, 8%N); (8, 8%N); (16, 8%N); (24, 8%N); (32, 8%N); (40, 4%N); (44, 4%N); (48, 1%N); (49, 1%N); (50, 1%N)].
Definition NODE_SIZE : Z := 56.
Definition ND_c0 := 0%nat. Definition ND_c1 := 1%nat. Definition ND_m0 := 2%nat. Definition ND_m1 := 3%nat.
Definition ND_m2 := 4%nat. Definition ND_imin := 5%nat. Definition ND_imax := 6%nat. Definition ND_cut := 7%nat.
Definition ND_cidx := 8%nat. Definition ND_leaf := 9%nat.
Lemma lay_inside_RgbFrameConfig : lay_inside LAY_RgbFrameConfig RGBFC_SIZE = true. Proof. reflexivity. Qed.
Lemma lay_inside_Node : lay_inside LAY_Node NODE_SIZE = true /\ lay_widths_ok LAY_Node = true. Proof. split; reflexivity. Qed.
Definition seg_dummy : Segment :=
{| seg_base := 0%N; seg_size := 0%N; seg_perms := String.EmptyString; seg_bytes := nil |}.
Definition CGIF_RGB_FRAME_ATTR_INTERLACED : Z := 1.
Definition CGIF_RGB_FRAME_ATTR_NO_DITHERING : Z := 2.
Definition FATTR_USE_LOCAL_TABLE : Z := 1. Definition FATTR_HAS_ALPHA : Z := 2.
Definition FATTR_HAS_SET_TRANS : Z := 4. Definition FATTR_INTERLACED : Z := 8.
Definition COL_MAX : Z := 255.
Definition RGB_NMAX : Z := 10000.
Definition COLHASH_STK : Z := 64.
Definition NTN_STK : Z := 160 + ALLOC_STACK.
Definition TREE_HMAX : Z := 255.
Definition FREETREE_STK : Z := 16 * (TREE_HMAX + 2) + ALLOC_STACK.
Definition GETPAL_STK : Z := 64 * (TREE_HMAX + 2) + 16.
Definition GLNI_STK : Z := 0.
Definition RGBA_FRAME_MAX : Z := 5168.
Definition RGBA_STK : Z := 24576.

Section b.
Variable segs : list Segment.
Definition arr8 (mem : word -> option byte) (base : Z) (l : list Z) : Prop :=
forall j, (j < length l)%nat -> mbyte segs mem (base + Z.of_nat j) = Some (Z_to_bv 8 (nth j l 0)) /\ 0 <= nth j l 0 < 256.
Definition arr32 (mem : word -> option byte) (base : Z) (l : list Z) : Prop :=
forall j, (j < length l)%nat -> val_mem segs mem (base + 4 * Z.of_nat j) 4 (nth j l 0) /\ 0 <= nth j l 0 < 2 ^ 32.
Lemma arr8_getz : forall mem base l i, arr8 mem base l -> 0 <= i < zlen l ->
mbyte segs mem (base + i) = Some (Z_to_bv 8 (getz l i)) /\ 0 <= getz l i < 256.
Proof.
intros mem base l i H Hi. unfold getz. rewrite <- (Z2Nat.id i) at 1 by lia.
apply H. unfold zlen in Hi. lia.
Qed.
Lemma arr32_getz : forall mem base l i, arr32 mem base l -> 0 <= i < zlen l ->
val_mem segs mem (base + 4 * i) 4 (getz l i) /\ 0 <= getz l i < 2 ^ 32.
Proof.
intros mem base l i H Hi. unfold getz. rewrite <- (Z2Nat.id i) at 1 by lia.
apply H. unfold zlen in Hi. lia.
Qed.
Lemma arr8_frame : forall mem mem' base l,
arr8 mem base l ->
(forall a, base <= a < base + zlen l -> mbyte segs mem' a = mbyte segs mem a) ->
arr8 mem' base l.
Proof.
intros mem mem' base l H Hfr j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
rewrite Hfr; [exact Hv|]. unfold zlen. lia.
Qed.
Lemma arr32_frame : forall mem mem' base l,
arr32 mem base l ->
(forall a, base <= a < base + 4 * zlen l -> mbyte segs mem' a = mbyte segs mem a) ->
arr32 mem' base l.
Proof.
intros mem mem' base l H Hfr j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. rewrite Hfr; [apply Hv; exact Hk|]. unfold zlen. lia.
Qed.



Definition col3 (mem : word -> option byte) (a : Z) (c : colour) : Prop :=
mbyte segs mem a = Some (Z_to_bv 8 (cR c)) /\ mbyte segs mem (a + 1) = Some (Z_to_bv 8 (cG c)) /\
mbyte segs mem (a + 2) = Some (Z_to_bv 8 (cB c)) /\ colour_ok c.
Lemma arr8_col3 : forall mem base l i, arr8 mem base l -> 0 <= i -> 3 * i + 3 <= zlen l ->
col3 mem (base + 3 * i) (col_at l i).
Proof.
intros mem base l i H Hi Hlen. unfold col3, col_at, cR, cG, cB, mkcol, colour_ok. cbn [fst snd].
destruct (arr8_getz mem base l (3 * i) H ltac:(lia)) as [A0 B0].
destruct (arr8_getz mem base l (3 * i + 1) H ltac:(lia)) as [A1 B1].
destruct (arr8_getz mem base l (3 * i + 2) H ltac:(lia)) as [A2 B2].
replace (base + 3 * i + 1) with (base + (3 * i + 1)) by lia.
replace (base + 3 * i + 2) with (base + (3 * i + 2)) by lia.
unfold cR, cG, cB. cbn [fst snd]. repeat split; try assumption; lia.
Qed.
Definition cht_arrays (mem : word -> option byte) (f h u p x : Z) (H : htab) : Prop :=
arr32 mem f (ht_frequ H) /\ arr8 mem h (ht_keys H) /\ arr8 mem u (ht_used H) /\
arr8 mem p (ht_pal H) /\ arr32 mem x (ht_colidx H).
Definition cht_blocks (f h u p x T : Z) : list (Z * Z) :=
[(f, 4 * T); (h, 3 * T); (u, T); (p, 3 * T); (x, 4 * T)].
End b.
Definition HT0 (T : Z) (used keys : list Z) : htab := mkHT [] keys used [] [] 0 T.
Definition probe (T : Z) (used keys : list Z) (c : colour) : option Z := find_slot (HT0 T used keys) c.
Lemma probe_of_htab : forall H c, find_slot H c = probe (ht_T H) (ht_used H) (ht_keys H) c.
Proof. intros H c. destruct H; reflexivity. Qed.
Definition col_hash_ret (r : option Z) : Z := match r with Some h => h | None => 2 ^ 64 - 1 end.
Definition pixel_at (segs : list Segment) (mem : word -> option byte) (rgb fmt : Z) (c : colour) (op : bool) : Prop :=
col3 segs mem rgb c /\
((fmt = 3 /\ op = true) \/
(fmt = 4 /\ exists a, mbyte segs mem (rgb + 3) = Some (Z_to_bv 8 a) /\ 0 <= a < 256 /\ op = (128 <=? a))).
Record tnode := mkTN {
tn_addr : Z;
tn_mean : list Z;
tn_imin : Z;
tn_imax : Z;
tn_cut : Z;
tn_cidx : Z
}.
Inductive tree : Type :=
| TNull
| TLeaf (n : tnode)
| TNode (n : tnode) (l r : tree).
Definition troot (t : tree) : Z :=
match t with TNull => 0 | TLeaf n => tn_addr n | TNode n _ _ => tn_addr n end.
Definition node_vals (c0 c1 : Z) (n : tnode) (leaf : Z) : list Z :=
[c0; c1] ++ tn_mean n ++ [tn_imin n; tn_imax n; tn_cut n; tn_cidx n; leaf].
Section e.
Variable segs : list Segment.
Fixpoint tree_at (mem : word -> option byte) (t : tree) : Prop :=
match t with
| TNull => True
| TLeaf n => tn_addr n <> 0 /\ length (tn_mean n) = 3%nat /\
exists c0 c1, obj_at segs mem (tn_addr n) LAY_Node (node_vals c0 c1 n 1)
| TNode n l r => tn_addr n <> 0 /\ length (tn_mean n) = 3%nat /\
obj_at segs mem (tn_addr n) LAY_Node (node_vals (troot l) (troot r) n 0) /\
tree_at mem l /\ tree_at mem r
end.
End e.
Fixpoint tree_blocks (t : tree) : list (Z * Z) :=
match t with
| TNull => []
| TLeaf n => [(tn_addr n, NODE_SIZE)]
| TNode n l r => (tn_addr n, NODE_SIZE) :: tree_blocks l ++ tree_blocks r
end.
Fixpoint tree_height (t : tree) : nat :=
match t with
| TNull | TLeaf _ => 0
| TNode _ l r => S (Nat.max (tree_height l) (tree_height r))
end.
Fixpoint tree_full (t : tree) : Prop :=
match t with TNull => False | TLeaf _ => True | TNode _ l r => tree_full l /\ tree_full r end.
Fixpoint tree_nodes (t : tree) : list tnode :=
match t with TNull => [] | TLeaf n => [n] | TNode n l r => n :: tree_nodes l ++ tree_nodes r end.
Fixpoint tree_leaves (t : tree) : list tnode :=
match t with TNull => [] | TLeaf n => [n] | TNode _ l r => tree_leaves l ++ tree_leaves r end.
Definition tree_forall (P : tnode -> Prop) (t : tree) : Prop := Forall P (tree_nodes t).
Lemma tree_blocks_nodes : forall t, tree_blocks t = map (fun n => (tn_addr n, NODE_SIZE)) (tree_nodes t).
Proof. induction t as [|n|n l IHl r IHr]; cbn; [reflexivity|reflexivity|]. rewrite map_app, IHl, IHr. reflexivity. Qed.
Lemma tree_forall_node : forall P n l r, tree_forall P (TNode n l r) <-> P n /\ tree_forall P l /\ tree_forall P r.
Proof.
intros P n l r. unfold tree_forall. cbn. rewrite Forall_cons_iff, Forall_app. tauto.
Qed.
Lemma tree_at_frame : forall segs mem mem' t,
tree_at segs mem t ->
(forall n a, In n (tree_nodes t) -> tn_addr n <= a < tn_addr n + NODE_SIZE -> mbyte segs mem' a = mbyte segs mem a) ->
tree_at segs mem' t.
Proof.
intros segs mem mem' t. induction t as [|n|n l IHl r IHr]; intros H Hfr; cbn [tree_at tree_nodes] in *.
- exact I.
- destruct H as (Ha & Hl & c0 & c1 & Ho). split; [exact Ha|]. split; [exact Hl|]. exists c0, c1.
eapply obj_at_transport_range; [exact Ho | apply (proj1 lay_inside_Node) |].
intros i Hi. apply (Hfr n); [left; reflexivity | unfold NODE_SIZE in *; lia].
- destruct H as (Ha & Hl & Ho & Hlt & Hrt). split; [exact Ha|]. split; [exact Hl|]. split.
+ eapply obj_at_transport_range; [exact Ho | apply (proj1 lay_inside_Node) |].
intros i Hi. apply (Hfr n); [left; reflexivity | unfold NODE_SIZE in *; lia].
+ split; [apply IHl; [exact Hlt|] | apply IHr; [exact Hrt|]]; intros n' a Hin Ha'; (apply (Hfr n'); [|exact Ha']);
right; apply in_app_iff; [left|right]; exact Hin.
Qed.
Definition mean_ok (x : Z) : Prop := exists m s, is_quot x m s /\ m <= 255 * s.
Definition tnode_wf (n : tnode) : Prop :=
0 <= tn_cut n <= 2 /\ 0 <= tn_cidx n < 256 /\ 0 <= tn_imin n <= tn_imax n /\ tn_imax n < 2 ^ 32 /\
length (tn_mean n) = 3%nat /\ Forall (fun x => 0 <= x < 2 ^ 64) (tn_mean n).
Definition tnode_means_ok (n : tnode) : Prop := Forall mean_ok (tn_mean n).
Definition node_list (pal fr : list Z) (imin imax d : Z) : list (Z * Z) :=
map (fun i => (getz fr i, getz pal (3 * i + d))) (zseq imin (imax - imin + 1)).
Lemma node_list_length : forall pal fr imin imax d, imin <= imax + 1 ->
Z.of_nat (length (node_list pal fr imin imax d)) = imax - imin + 1.
Proof. intros. unfold node_list. rewrite length_map, zseq_length. lia. Qed.
Lemma In_node_list : forall pal fr imin imax d x,
In x (node_list pal fr imin imax d) <-> exists i, imin <= i <= imax /\ x = (getz fr i, getz pal (3 * i + d)).
Proof.
intros pal fr imin imax d x. unfold node_list. rewrite in_map_iff. split.
- intros (i & <- & Hi). apply In_zseq in Hi. exists i. split; [lia | reflexivity].
- intros (i & Hi & ->). exists i. split; [reflexivity|]. apply In_zseq. lia.
Qed.
Definition dim_splits (pal : list Z) (imin imax d : Z) : Prop :=
exists i j, imin <= i <= imax /\ imin <= j <= imax /\ getz pal (3 * i + d) <> getz pal (3 * j + d).
Definition range_has_two (pal : list Z) (imin imax : Z) : Prop :=
exists i j, imin <= i <= imax /\ imin <= j <= imax /\ col_at pal i <> col_at pal j.
Lemma range_has_two_dim : forall pal imin imax,
range_has_two pal imin imax -> exists d, 0 <= d <= 2 /\ dim_splits pal imin imax d.
Proof.
intros pal imin imax (i & j & Hi & Hj & Hne). unfold col_at, mkcol in Hne.
destruct (Z.eq_dec (getz pal (3 * i)) (getz pal (3 * j))) as [E0|N0].
- destruct (Z.eq_dec (getz pal (3 * i + 1)) (getz pal (3 * j + 1))) as [E1|N1].
+ destruct (Z.eq_dec (getz pal (3 * i + 2)) (getz pal (3 * j + 2))) as [E2|N2].
* exfalso. apply Hne. rewrite E0, E1, E2. reflexivity.
* exists 2. split; [lia|]. exists i, j. auto.
+ exists 1. split; [lia|]. exists i, j. auto.
- exists 0. split; [lia|]. exists i, j. rewrite !Z.add_0_r. auto.
Qed.
