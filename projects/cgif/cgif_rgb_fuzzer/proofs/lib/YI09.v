(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0b YI00 YI02 YI07 YM01 YM02 YP14 YP16 YI08 YI0c.
From Stdlib Require Import ZArith List Bool Lia Permutation.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition ents_of (pal fdl : list Z) (cnt : Z) : list entry :=
map (fun i => (col_at pal i, getz fdl i)) (zseq 0 cnt).
Lemma elen_ents_of : forall pal fdl cnt, 0 <= cnt -> elen (ents_of pal fdl cnt) = cnt.
Proof. intros. unfold ents_of, elen. rewrite length_map, zseq_length. lia. Qed.
Lemma nth_map' : forall {A B} (f : A -> B) l n dA dB, (n < length l)%nat -> nth n (map f l) dB = f (nth n l dA).
Proof. intros A B f l n dA dB Hn. rewrite (nth_indep _ dB (f dA)) by (rewrite length_map; exact Hn). apply map_nth. Qed.
Lemma nth_zseq : forall a n k d, (k < Z.to_nat n)%nat -> nth k (zseq a n) d = a + Z.of_nat k.
Proof.
intros a n k d Hk. unfold zseq. rewrite (nth_map' _ _ _ 0%nat d) by (rewrite length_seq; exact Hk).
rewrite seq_nth by exact Hk. reflexivity.
Qed.
Lemma znth_ents_of : forall pal fdl cnt j, 0 <= j < cnt ->
znth dentry (ents_of pal fdl cnt) j = (col_at pal j, getz fdl j).
Proof.
intros pal fdl cnt j Hj. unfold znth, ents_of.
rewrite (nth_map' _ _ _ 0 dentry) by (rewrite zseq_length; lia).
rewrite nth_zseq by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma ecol_ents_of : forall pal fdl cnt j, 0 <= j < cnt -> ecol (ents_of pal fdl cnt) j = col_at pal j.
Proof. intros. unfold ecol. rewrite znth_ents_of by assumption. reflexivity. Qed.
Lemma efreq_ents_of : forall pal fdl cnt j, 0 <= j < cnt -> efreq (ents_of pal fdl cnt) j = getz fdl j.
Proof. intros. unfold efreq. rewrite znth_ents_of by assumption. reflexivity. Qed.
Lemma comp_col_at : forall pal j d, 0 <= d < 3 -> comp d (col_at pal j) = getz pal (3 * j + d).
Proof.
intros pal j d Hd. unfold comp, col_at, mkcol, cR, cG, cB. cbn [fst snd].
destruct (Z.eqb_spec d 0) as [->|]; [rewrite Z.add_0_r; reflexivity|].
destruct (Z.eqb_spec d 1) as [->|]; [reflexivity|]. replace d with 2 by lia. reflexivity.
Qed.
Lemma getz_pal_bytes_ents_of : forall pal fdl cnt x, 0 <= cnt -> 0 <= x < 3 * cnt ->
getz (pal_bytes (ents_of pal fdl cnt)) x = getz pal x.
Proof.
intros pal fdl cnt x Hc Hx.
rewrite getz_pal_bytes_at by (rewrite elen_ents_of; lia).
pose proof (Z.div_mod x 3 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 3 ltac:(lia)) as Hm.
rewrite ecol_ents_of by nia. rewrite comp_col_at by lia. f_equal. lia.
Qed.
Lemma getz_fr_vals_ents_of : forall pal fdl cnt j, 0 <= cnt -> 0 <= j < cnt ->
getz (fr_vals (ents_of pal fdl cnt)) j = getz fdl j.
Proof.
intros pal fdl cnt j Hc Hj. rewrite getz_fr_vals by (rewrite elen_ents_of; lia). apply efreq_ents_of. exact Hj.
Qed.
Lemma getz_ext : forall l l', length l = length l' -> (forall i, 0 <= i < zlen l -> getz l i = getz l' i) -> l = l'.
Proof.
intros l l' Hlen H. apply (nth_ext _ _ 0 0); [exact Hlen|]. intros n Hn.
specialize (H (Z.of_nat n) ltac:(unfold zlen; lia)). unfold getz in H. rewrite Nat2Z.id in H. exact H.
Qed.
Lemma pal_bytes_ents_of : forall pal fdl cnt, 0 <= cnt -> 3 * cnt <= zlen pal ->
pal_bytes (ents_of pal fdl cnt) = firstn (Z.to_nat (3 * cnt)) pal.
Proof.
intros pal fdl cnt Hc Hlen. apply getz_ext.
- rewrite pal_bytes_length, length_firstn. unfold ents_of. rewrite length_map, zseq_length. unfold zlen in Hlen. lia.
- intros i Hi. rewrite zlen_pal_bytes, elen_ents_of in Hi by lia.
rewrite getz_pal_bytes_ents_of by lia. unfold getz. rewrite nth_firstn.
destruct (Nat.ltb_spec (Z.to_nat i) (Z.to_nat (3 * cnt))); [reflexivity | lia].
Qed.
Lemma pal_split_ents_of : forall pal fdl cnt, 0 <= cnt -> 3 * cnt <= zlen pal ->
pal_bytes (ents_of pal fdl cnt) ++ skipn (Z.to_nat (3 * cnt)) pal = pal.
Proof. intros. rewrite pal_bytes_ents_of by assumption. apply firstn_skipn. Qed.
Lemma fr_vals_ents_of : forall pal fdl cnt, 0 <= cnt -> zlen fdl = cnt -> fr_vals (ents_of pal fdl cnt) = fdl.
Proof.
intros pal fdl cnt Hc Hlen. apply getz_ext.
- unfold fr_vals, ents_of. rewrite !length_map, zseq_length. unfold zlen in Hlen. lia.
- intros i Hi. rewrite zlen_fr_vals, elen_ents_of in Hi by lia. apply getz_fr_vals_ents_of; lia.
Qed.
Lemma ent_ok_ents_of : forall pal fdl cnt, 0 <= cnt ->
(forall x, 0 <= x < 3 * cnt -> 0 <= getz pal x < 256) ->
(forall i, 0 <= i < cnt -> 1 <= getz fdl i) ->
ent_ok (ents_of pal fdl cnt).
Proof.
intros pal fdl cnt Hc Hpal Hfr. unfold ent_ok, ents_of. apply Forall_map. apply Forall_forall.
intros i Hi. apply In_zseq in Hi. cbn [fst snd]. split; [| apply Hfr; lia].
unfold colour_ok, col_at, mkcol, cR, cG, cB. cbn [fst snd].
pose proof (Hpal (3 * i) ltac:(lia)). pose proof (Hpal (3 * i + 1) ltac:(lia)). pose proof (Hpal (3 * i + 2) ltac:(lia)). lia.
Qed.
Lemma NoDup_map_zseq : forall {B} (f : Z -> B) a n,
(forall i j, a <= i < a + n -> a <= j < a + n -> i <> j -> f i <> f j) -> NoDup (map f (zseq a n)).
Proof.
intros B f a n Hinj.
assert (G : forall m, Z.of_nat m <= n -> NoDup (map f (zseq a (Z.of_nat m)))).
{ induction m as [|m IH]; intros Hm.
- unfold zseq. cbn. constructor.
- rewrite Nat2Z.inj_succ. replace (Z.succ (Z.of_nat m)) with (Z.of_nat m + 1) by lia. rewrite zseq_succ by lia. rewrite map_app. cbn [map].
apply NoDup_app; [apply IH; lia | constructor; [intros []| constructor] |].
intros x Hx [<-|[]]. apply in_map_iff in Hx as (i & Hfi & Hi). apply In_zseq in Hi.
apply (Hinj i (a + Z.of_nat m)); [lia | lia | lia | exact Hfi]. }
destruct (Z_lt_le_dec n 0) as [Hn|Hn].
- unfold zseq. replace (Z.to_nat n) with 0%nat by lia. cbn. constructor.
- replace n with (Z.of_nat (Z.to_nat n)) at 1 by lia. apply G. lia.
Qed.
Lemma NoDup_ents_of : forall pal fdl cnt,
(forall i j, 0 <= i < cnt -> 0 <= j < cnt -> i <> j -> col_at pal i <> col_at pal j) ->
NoDup (map fst (ents_of pal fdl cnt)).
Proof.
intros pal fdl cnt Hd. unfold ents_of. rewrite map_map. cbn [fst].
apply NoDup_map_zseq. intros i j Hi Hj Hne. apply Hd; lia.
Qed.

Definition pal_agrees (palc : list Z) (E : list entry) : Prop :=
forall x, 0 <= x < 3 * elen E -> getz palc x = getz (pal_bytes E) x.
Lemma pal_agrees_app : forall E tail, pal_agrees (pal_bytes E ++ tail) E.
Proof.
intros E tail x Hx. unfold getz. rewrite app_nth1; [reflexivity|]. rewrite pal_bytes_length. unfold elen in Hx. lia.
Qed.
Lemma node_list_dseg : forall palc E lo hi d, pal_agrees palc E ->
0 <= d < 3 -> 0 <= lo -> lo <= hi + 1 -> hi < elen E ->
node_list palc (fr_vals E) lo hi d = dseg d E lo hi.
Proof.
intros palc E lo hi d Hp Hd Hlo Hle Hhi. unfold node_list. symmetry.
apply dseg_as_map; [exact Hd | exact Hlo | exact Hle | exact Hhi | exact Hp | intros; reflexivity].
Qed.
Lemma neqd_of_dim_splits : forall palc E lo hi cut, pal_agrees palc E ->
0 <= lo -> hi < elen E -> 0 <= cut < 3 ->
dim_splits palc lo hi cut -> neqd (dseg cut E lo hi).
Proof.
intros palc E lo hi cut Hp Hlo Hhi Hcut (i & j & Hi & Hj & Hne).
rewrite !Hp in Hne by nia. rewrite !getz_pal_bytes in Hne by lia.
exists (efreq E i, comp cut (ecol E i)), (efreq E j, comp cut (ecol E j)).
split; [apply In_dseg; [lia|lia|]; exists i; split; [lia|reflexivity]|].
split; [apply In_dseg; [lia|lia|]; exists j; split; [lia|reflexivity]|].
cbn [snd]. exact Hne.
Qed.
Lemma col_at_agrees : forall palc E j, pal_agrees palc E -> 0 <= j < elen E -> col_at palc j = ecol E j.
Proof.
intros palc E j Hp Hj. unfold col_at, mkcol. rewrite <- (Z.add_0_r (3 * j)) at 1.
rewrite !Hp by lia. rewrite !getz_pal_bytes by lia.
unfold comp. cbn. destruct (ecol E j) as [[r g] b]. reflexivity.
Qed.
Lemma range_has_two_of_NoDup : forall palc E lo hi, pal_agrees palc E -> NoDup (map fst E) ->
0 <= lo -> lo < hi -> hi < elen E -> range_has_two palc lo hi.
Proof.
intros palc E lo hi Hp Hnd Hlo Hlt Hhi. exists lo, hi. split; [lia|]. split; [lia|].
rewrite !(col_at_agrees palc E) by (try exact Hp; lia).
unfold ecol, znth. intros Eq.
pose proof (proj1 (NoDup_nth_error _) Hnd (Z.to_nat lo) (Z.to_nat hi)) as Hinj.
assert (Z.to_nat lo = Z.to_nat hi); [|lia]. apply Hinj; [rewrite length_map; unfold elen in *; lia|].
rewrite !nth_error_map. unfold elen in *.
rewrite (nth_error_nth' E dentry) by lia. rewrite (nth_error_nth' E dentry) by lia. cbn. f_equal. exact Eq.
Qed.
Definition ptest (palc : list Z) (cut s m x : Z) : bool := getz palc (3 * x + cut) * s <=? m.
Lemma smallb_ptest : forall palc E cut s m x, pal_agrees palc E -> 0 <= cut < 3 -> 0 <= x < elen E ->
smallb dentry (Ptest cut s m) E x = ptest palc cut s m x.
Proof.
intros palc E cut s m x Hp Hcut Hx. unfold smallb, Ptest, ptest.
rewrite Hp by nia. rewrite getz_pal_bytes by lia. reflexivity.
Qed.
Lemma pinv_start : forall E lo hi cut, ent_ok E -> 0 <= lo -> lo <= hi -> hi < elen E ->
neqd (dseg cut E lo hi) ->
let l := dseg cut E lo hi in
pinv dentry (Ptest cut (wsum l) (wdot l)) lo hi E E lo hi.
Proof.
intros E lo hi cut HE Hlo Hle Hhi Hneq l.
destruct (mean_witnesses cut E lo hi HE Hlo Hle Hhi Hneq) as [Wx Wy].
apply pinv_init; [exact Hlo | exact Hle | exact Hhi | exact Wx | exact Wy].
Qed.

Definition dtn : tnode := mkTN 0 [0; 0; 0] 0 0 0 0.
Definition tnth (tns : list tnode) (j : Z) : tnode := znth dtn tns j.
Definition oaddr (tns : list tnode) (o : option Z) : Z :=
match o with Some c => tn_addr (tnth tns c) | None => 0 end.
Lemma tnth_app_l : forall tns l j, 0 <= j < elen tns -> tnth (tns ++ l) j = tnth tns j.
Proof. intros tns l j Hj. unfold tnth, znth, elen in *. apply app_nth1. lia. Qed.
Lemma tnth_app_r : forall tns l j, elen tns <= j -> tnth (tns ++ l) j = tnth l (j - elen tns).
Proof.
intros tns l j Hj. unfold tnth, znth, elen in *. rewrite app_nth2 by lia. f_equal. lia.
Qed.
Definition tn_matches (tn : tnode) (nd : anode (A := entry)) : Prop :=
tn_imin tn = n_lo nd /\ tn_imax tn = n_hi nd /\ tn_cidx tn = n_col nd /\ tnode_wf tn /\ tn_addr tn <> 0.
Definition tn_facts (tn : tnode) (nd : anode (A := entry)) : Prop :=
(forall d, 0 <= d <= 2 ->
is_quot (nth (Z.to_nat d) (tn_mean tn) 0) (wdot (segd d (n_seg nd))) (wsum (segd d (n_seg nd)))) /\
(n_lo nd < n_hi nd -> neqd (segd (tn_cut tn) (n_seg nd))).
Section t.
Variable segs : list Segment.
Definition node_mem (mem : word -> option byte) (ns : list (anode (A := entry))) (tns : list tnode) (j : Z) : Prop :=
let nd := node ns j in let tn := tnth tns j in
if n_leaf nd then exists c0 c1, obj_at segs mem (tn_addr tn) LAY_Node (node_vals c0 c1 tn 1)
else obj_at segs mem (tn_addr tn) LAY_Node (node_vals (oaddr tns (n_k0 nd)) (oaddr tns (n_k1 nd)) tn 0).
Lemma node_mem_frame : forall mem mem' ns tns j,
node_mem mem ns tns j ->
(forall i, 0 <= i < NODE_SIZE -> mbyte segs mem' (tn_addr (tnth tns j) + i) = mbyte segs mem (tn_addr (tnth tns j) + i)) ->
node_mem mem' ns tns j.
Proof.
intros mem mem' ns tns j H Hfr. unfold node_mem in *.
destruct (n_leaf (node ns j)).
- destruct H as (c0 & c1 & H). exists c0, c1. eapply obj_at_transport_range; [exact H | apply (proj1 lay_inside_Node) | exact Hfr].
- eapply obj_at_transport_range; [exact H | apply (proj1 lay_inside_Node) | exact Hfr].
Qed.
Fixpoint build (ns : list (anode (A := entry))) (tns : list tnode) (j : Z) (h : nat) : tree :=
match h with
| O => TNull
| S h' =>
let nd := node ns j in
if n_leaf nd then TLeaf (tnth tns j)
else TNode (tnth tns j)
(match n_k0 nd with Some c => build ns tns c h' | None => TNull end)
(match n_k1 nd with Some c => build ns tns c h' | None => TNull end)
end.
Lemma build_root : forall ns tns j h, (1 <= h)%nat -> troot (build ns tns j h) = tn_addr (tnth tns j).
Proof. intros ns tns j [|h] Hh; [lia|]. cbn [build]. destruct (n_leaf (node ns j)); reflexivity. Qed.
Lemma build_height : forall ns tns j h, (tree_height (build ns tns j h) <= h)%nat.
Proof.
intros ns tns j h. revert j. induction h as [|h IH]; intros j; cbn [build tree_height]; [lia|].
destruct (n_leaf (node ns j)); cbn [tree_height]; [lia|].
apply le_n_S. apply Nat.max_lub.
- destruct (n_k0 (node ns j)) as [c|]; [apply IH | cbn; lia].
- destruct (n_k1 (node ns j)) as [c|]; [apply IH | cbn; lia].
Qed.
Lemma build_at : forall mem ns tns h j,
YP16.tree_ok ns j h ->
(forall x, 0 <= x < elen ns -> node_mem mem ns tns x /\ length (tn_mean (tnth tns x)) = 3%nat /\ tn_addr (tnth tns x) <> 0) ->
tree_at segs mem (build ns tns j h).
Proof.
intros mem ns tns h. induction h as [|h IH]; intros j HT Hn; [destruct HT|].
destruct HT as [Hj Hk]. cbn [build]. destruct (Hn j Hj) as (Hm & Hl & Ha). unfold node_mem in Hm.
destruct (n_leaf (node ns j)) eqn:El.
- cbn [tree_at]. split; [exact Ha|]. split; [exact Hl|]. exact Hm.
- destruct (Hk eq_refl) as [K0 K1]. cbn [tree_at]. split; [exact Ha|]. split; [exact Hl|]. split.
+ assert (R0 : troot (match n_k0 (node ns j) with Some c => build ns tns c h | None => TNull end) = oaddr tns (n_k0 (node ns j))).
{ destruct (n_k0 (node ns j)) as [c|]; [|reflexivity]. cbn [oaddr]. apply build_root.
exact (proj2 (tree_ok_node _ _ _ (K0 c eq_refl))). }
assert (R1 : troot (match n_k1 (node ns j) with Some c => build ns tns c h | None => TNull end) = oaddr tns (n_k1 (node ns j))).
{ destruct (n_k1 (node ns j)) as [c|]; [|reflexivity]. cbn [oaddr]. apply build_root.
exact (proj2 (tree_ok_node _ _ _ (K1 c eq_refl))). }
rewrite R0, R1. exact Hm.
+ split.
* destruct (n_k0 (node ns j)) as [c|]; [apply IH; [exact (K0 c eq_refl) | exact Hn] | exact I].
* destruct (n_k1 (node ns j)) as [c|]; [apply IH; [exact (K1 c eq_refl) | exact Hn] | exact I].
Qed.
Lemma build_full : forall ns tns h j,
YP16.tree_ok ns j h ->
(forall x, 0 <= x < elen ns -> n_leaf (node ns x) = false ->
exists c, n_k0 (node ns x) = Some c /\ n_k1 (node ns x) = Some (c + 1)) ->
tree_full (build ns tns j h).
Proof.
intros ns tns h. induction h as [|h IH]; intros j HT Hk; [destruct HT|].
destruct HT as [Hj HK]. cbn [build]. destruct (n_leaf (node ns j)) eqn:El; [exact I|].
destruct (Hk j Hj El) as (c & E0 & E1). rewrite E0, E1. destruct (HK eq_refl) as [K0 K1].
cbn [tree_full]. split; apply IH; auto.
Qed.
Lemma build_nodes : forall ns tns h j,
par_ok ns -> YP16.tree_ok ns j h ->
Permutation (tree_nodes (build ns tns j h)) (map (tnth tns) (desc ns j)).
Proof.
intros ns tns h. induction h as [|h IH]; intros j PO HT; [destruct HT|].
destruct HT as [Hj HK]. cbn [build]. destruct (n_leaf (node ns j)) eqn:El.
- rewrite (desc_leaf ns PO j Hj El). cbn. apply Permutation_refl.
- cbn [tree_nodes]. eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; exact (desc_split ns PO j Hj El)].
cbn [map]. apply perm_skip. rewrite map_app. destruct (HK eq_refl) as [K0 K1]. apply Permutation_app.
+ destruct (n_k0 (node ns j)) as [c|]; cbn [odesc tree_nodes map]; [apply IH; auto | apply Permutation_refl].
+ destruct (n_k1 (node ns j)) as [c|]; cbn [odesc tree_nodes map]; [apply IH; auto | apply Permutation_refl].
Qed.
Lemma build_forall : forall (P : tnode -> Prop) ns tns h j,
par_ok ns -> YP16.tree_ok ns j h ->
(forall x, 0 <= x < elen ns -> P (tnth tns x)) -> tree_forall P (build ns tns j h).
Proof.
intros P ns tns h j PO HT HP. unfold tree_forall.
eapply Permutation_Forall; [apply Permutation_sym; apply build_nodes; assumption|].
apply Forall_map. apply Forall_forall. intros x Hx. apply HP. exact (desc_range ns j x Hx).
Qed.
Lemma build_nodes_root : forall ns tns h,
par_ok ns -> YP16.tree_ok ns 0 h ->
Permutation (tree_nodes (build ns tns 0 h)) (map (tnth tns) (zseq 0 (elen ns))).
Proof. intros ns tns h PO HT. rewrite <- (desc_root ns PO). apply build_nodes; assumption. Qed.
Lemma build_blocks_root : forall ns tns h,
par_ok ns -> YP16.tree_ok ns 0 h ->
Permutation (tree_blocks (build ns tns 0 h)) (map (fun j => (tn_addr (tnth tns j), NODE_SIZE)) (zseq 0 (elen ns))).
Proof.
intros ns tns h PO HT. rewrite tree_blocks_nodes.
rewrite <- (map_map (tnth tns) (fun n => (tn_addr n, NODE_SIZE))). apply Permutation_map. apply build_nodes_root; assumption.
Qed.
Lemma In_nodes_build_root : forall ns tns h n,
par_ok ns -> YP16.tree_ok ns 0 h ->
In n (tree_nodes (build ns tns 0 h)) -> exists j, 0 <= j < elen ns /\ n = tnth tns j.
Proof.
intros ns tns h n PO HT Hin.
apply (Permutation_in _ (build_nodes_root ns tns h PO HT)) in Hin. apply in_map_iff in Hin as (j & <- & Hj).
apply In_zseq in Hj. exists j. split; [lia | reflexivity].
Qed.
End t.
Section u.
Variable segs : list Segment.
Lemma zlen_app_pal : forall E tail, zlen (pal_bytes E ++ tail) = 3 * elen E + zlen tail.
Proof. intros. unfold zlen. rewrite length_app, pal_bytes_length. unfold elen. lia. Qed.
Lemma getz_app_l : forall l1 l2 x, 0 <= x < zlen l1 -> getz (l1 ++ l2) x = getz l1 x.
Proof. intros l1 l2 x Hx. unfold getz, zlen in *. apply app_nth1. lia. Qed.
Lemma getz_app_r : forall l1 l2 x, zlen l1 <= x -> getz (l1 ++ l2) x = getz l2 (x - zlen l1).
Proof. intros l1 l2 x Hx. unfold getz, zlen in *. rewrite app_nth2 by lia. f_equal. lia. Qed.
Lemma arr8_of_getz : forall mem base l,
(forall x, 0 <= x < zlen l -> mbyte segs mem (base + x) = Some (Z_to_bv 8 (getz l x)) /\ 0 <= getz l x < 256) ->
arr8 segs mem base l.
Proof.
intros mem base l H j Hj. specialize (H (Z.of_nat j) ltac:(unfold zlen; lia)). unfold getz in H. rewrite Nat2Z.id in H. exact H.
Qed.
Lemma arr8_eswap : forall mem mem' p E tail i k,
arr8 segs mem p (pal_bytes E ++ tail) -> ent_ok E -> 0 <= i < elen E -> 0 <= k < elen E -> i < k ->
(forall x, 0 <= x < 3 * elen E + zlen tail -> ~ (3 * i <= x < 3 * i + 3) -> ~ (3 * k <= x < 3 * k + 3) ->
mbyte segs mem' (p + x) = mbyte segs mem (p + x)) ->
(forall d, 0 <= d < 3 -> mbyte segs mem' (p + 3 * i + d) = Some (Z_to_bv 8 (getz (pal_bytes E) (3 * k + d)))) ->
(forall d, 0 <= d < 3 -> mbyte segs mem' (p + 3 * k + d) = Some (Z_to_bv 8 (getz (pal_bytes E) (3 * i + d)))) ->
arr8 segs mem' p (pal_bytes (eswap dentry E i k) ++ tail).
Proof.
intros mem mem' p E tail i k Ha HE Hi Hk Hik Hfr Hpi Hpk.
pose proof (pal_bytes_bytes E HE) as HB. pose proof (pal_bytes_bytes _ (ent_ok_perm _ _ (eswap_perm dentry E i k ltac:(lia) ltac:(lia)) HE)) as HB'.
assert (Hlen : zlen (pal_bytes (eswap dentry E i k) ++ tail) = 3 * elen E + zlen tail) by (rewrite zlen_app_pal, elen_eswap; reflexivity).
apply arr8_of_getz. intros x Hx. rewrite Hlen in Hx.
assert (R : forall l y, Forall (fun v => 0 <= v < 256) l -> 0 <= y < zlen l -> 0 <= getz l y < 256).
{ intros l y Hl Hy. apply (proj1 (Forall_forall _ _) Hl). unfold getz. apply nth_In. unfold zlen in Hy. lia. }
pose proof (zlen_pal_bytes E) as HL. pose proof (zlen_pal_bytes (eswap dentry E i k)) as HL'. rewrite elen_eswap in HL'.
destruct (Z_lt_le_dec x (3 * elen E)) as [Hlo|Hhi].
- rewrite getz_app_l by lia. rewrite pal_bytes_eswap by lia.
destruct (Z_lt_le_dec x (3 * i)) as [H1|H1]; [| destruct (Z_lt_le_dec x (3 * i + 3)) as [H2|H2]].
+ replace ((3 * k <=? x) && (x <? 3 * k + 3)) with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
replace ((3 * i <=? x) && (x <? 3 * i + 3)) with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
rewrite Hfr by lia. destruct (Ha (Z.to_nat x) ltac:(rewrite length_app, pal_bytes_length; unfold elen in *; lia)) as [H H'].
rewrite Z2Nat.id in H by lia. unfold getz. rewrite <- (app_nth1 _ tail) by (rewrite pal_bytes_length; unfold elen in *; lia). split; [exact H | exact H'].
+ replace ((3 * k <=? x) && (x <? 3 * k + 3)) with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
replace ((3 * i <=? x) && (x <? 3 * i + 3)) with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
replace x with (3 * i + (x - 3 * i)) at 1 by lia. rewrite Z.add_assoc, Hpi by lia.
replace (3 * k + (x - 3 * i)) with (x - 3 * i + 3 * k) by lia. split; [reflexivity | apply R; [exact HB | lia]].
+ destruct (Z_lt_le_dec x (3 * k)) as [H3|H3]; [| destruct (Z_lt_le_dec x (3 * k + 3)) as [H4|H4]].
* replace ((3 * k <=? x) && (x <? 3 * k + 3)) with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
replace ((3 * i <=? x) && (x <? 3 * i + 3)) with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.ltb_ge; lia).
rewrite Hfr by lia. destruct (Ha (Z.to_nat x) ltac:(rewrite length_app, pal_bytes_length; unfold elen in *; lia)) as [H H'].
rewrite Z2Nat.id in H by lia. unfold getz. rewrite <- (app_nth1 _ tail) by (rewrite pal_bytes_length; unfold elen in *; lia). split; [exact H | exact H'].
* replace ((3 * k <=? x) && (x <? 3 * k + 3)) with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
replace x with (3 * k + (x - 3 * k)) at 1 by lia. rewrite Z.add_assoc, Hpk by lia.
replace (3 * i + (x - 3 * k)) with (x - 3 * k + 3 * i) by lia. split; [reflexivity | apply R; [exact HB | lia]].
* replace ((3 * k <=? x) && (x <? 3 * k + 3)) with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.ltb_ge; lia).
replace ((3 * i <=? x) && (x <? 3 * i + 3)) with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.ltb_ge; lia).
rewrite Hfr by lia. destruct (Ha (Z.to_nat x) ltac:(rewrite length_app, pal_bytes_length; unfold elen in *; lia)) as [H H'].
rewrite Z2Nat.id in H by lia. unfold getz. rewrite <- (app_nth1 _ tail) by (rewrite pal_bytes_length; unfold elen in *; lia). split; [exact H | exact H'].
- rewrite getz_app_r by lia. rewrite HL'. rewrite Hfr by lia.
destruct (Ha (Z.to_nat x) ltac:(rewrite length_app, pal_bytes_length; unfold elen, zlen in *; lia)) as [H H'].
rewrite Z2Nat.id in H by lia. unfold getz, zlen. rewrite <- (Z2Nat.id x) in H at 1 by lia.
rewrite app_nth2 in H, H' by (rewrite pal_bytes_length; unfold elen in *; lia). rewrite pal_bytes_length in H, H'.
replace (Z.to_nat (x - 3 * elen E)) with (Z.to_nat x - 3 * length E)%nat by (unfold elen; lia).
rewrite Z2Nat.id in H by lia. split; [exact H | exact H'].
Qed.
Lemma arr32_eswap : forall mem mem' q E i k,
arr32 segs mem q (fr_vals E) -> 0 <= i < elen E -> 0 <= k < elen E -> i < k ->
(forall x, 0 <= x < 4 * elen E -> ~ (4 * i <= x < 4 * i + 4) -> ~ (4 * k <= x < 4 * k + 4) ->
mbyte segs mem' (q + x) = mbyte segs mem (q + x)) ->
val_mem segs mem' (q + 4 * i) 4 (getz (fr_vals E) k) ->
val_mem segs mem' (q + 4 * k) 4 (getz (fr_vals E) i) ->
arr32 segs mem' q (fr_vals (eswap dentry E i k)).
Proof.
intros mem mem' q E i k Ha Hi Hk Hik Hfr Vi Vk j Hj.
unfold fr_vals in Hj. rewrite length_map, eswap_length in Hj.
pose proof (zlen_fr_vals E) as HL.
replace (nth j (fr_vals (eswap dentry E i k)) 0) with (getz (fr_vals (eswap dentry E i k)) (Z.of_nat j)) by (unfold getz; rewrite Nat2Z.id; reflexivity).
rewrite fr_vals_eswap by (unfold elen in *; lia).
destruct (Z.eqb_spec (Z.of_nat j) k) as [Ej|Nj].
- split; [rewrite Ej; exact Vk| apply (proj2 (arr32_getz segs mem q (fr_vals E) i Ha ltac:(lia)))].
- destruct (Z.eqb_spec (Z.of_nat j) i) as [Ej'|Nj'].
+ split; [rewrite Ej'; exact Vi| apply (proj2 (arr32_getz segs mem q (fr_vals E) k Ha ltac:(lia)))].
+ destruct (arr32_getz segs mem q (fr_vals E) (Z.of_nat j) Ha ltac:(unfold elen in *; lia)) as [V R]. split; [|exact R].
intros b Hb. rewrite <- (V b Hb). rewrite <- !Z.add_assoc. apply Hfr; unfold elen in *; lia.
Qed.
End u.
Section w.
Context {A : Type}.
Implicit Types (ns : list (anode (A := A))).
Lemma elen_zupd : forall ns q x, elen (zupd ns q x) = elen ns.
Proof. intros. unfold elen. rewrite zupd_length. reflexivity. Qed.
Lemma csplit_nodes : forall (st : cstate (A := A)) E' i,
let ns := c_ns st in let q := c_q st in let m := elen ns in let p := node ns q in let L := nleaves ns in
0 <= q < m ->
let ns' := c_ns (csplit st E' i) in
elen ns' = m + 2 /\
(forall j, 0 <= j < m -> j <> q -> node ns' j = node ns j) /\
node ns' q = mkN (n_lo p) (n_hi p) false (n_col p) (Some m) (Some (m + 1)) (n_par p) (n_depth p) (n_seg p) /\
node ns' m = mkN (n_lo p) (i - 1) true (n_col p) None None q (n_depth p + 1) (zsub E' (n_lo p) (i - 1)) /\
node ns' (m + 1) = mkN i (n_hi p) true L None None q (n_depth p + 1) (zsub E' i (n_hi p)) /\
c_q (csplit st E' i) = q + 1 /\ c_E (csplit st E' i) = E'.
Proof.
intros [E ns q] E' i. cbn [c_ns c_q c_E]. intros Hq. unfold csplit. cbn [c_ns c_q c_E].
set (m := elen ns). set (p := node ns q).
set (p' := mkN (n_lo p) (n_hi p) false (n_col p) (Some m) (Some (m + 1)) (n_par p) (n_depth p) (n_seg p)).
assert (Hzl : elen (zupd ns q p') = m) by apply elen_zupd.
split; [unfold elen in *; rewrite length_app, zupd_length; cbn [length]; lia|].
split. { intros j Hj Hne. rewrite node_app_l by (rewrite Hzl; lia). rewrite node_zupd by lia. destruct (Z.eqb_spec j q); [lia| reflexivity]. }
split. { rewrite node_app_l by (rewrite Hzl; lia). rewrite node_zupd by lia. rewrite Z.eqb_refl. fold m. destruct (Z.ltb_spec q m); [reflexivity| lia]. }
split. { rewrite node_app_r by (rewrite Hzl; lia). rewrite Hzl, Z.sub_diag. reflexivity. }
split. { rewrite node_app_r by (rewrite Hzl; lia). rewrite Hzl. replace (m + 1 - m) with 1 by lia. reflexivity. }
split; reflexivity.
Qed.
Lemma cfail_nodes : forall ns q i col1 ok0 ok1,
let m := elen ns in let p := node ns q in
0 <= q < m ->
let ns' := cfail_ns ns q i col1 ok0 ok1 in
let b0 := (if ok0 then 1 else 0) in
elen ns' = m + b0 + (if ok1 then 1 else 0) /\
(forall j, 0 <= j < m -> j <> q -> node ns' j = node ns j) /\
node ns' q = mkN (n_lo p) (n_hi p) false (n_col p) (if ok0 then Some m else None) (if ok1 then Some (m + b0) else None)
(n_par p) (n_depth p) (n_seg p) /\
(ok0 = true -> node ns' m = mkN (n_lo p) (i - 1) true (n_col p) None None q (n_depth p + 1) []) /\
(ok1 = true -> node ns' (m + b0) = mkN i (n_hi p) true col1 None None q (n_depth p + 1) []).
Proof.
intros ns q i col1 ok0 ok1 m p Hq ns' b0. unfold cfail_ns in ns'. cbv zeta in ns'. fold m p in ns'.
set (p' := mkN (n_lo p) (n_hi p) false (n_col p) (if ok0 then Some m else None) (if ok1 then Some (m + (if ok0 then 1 else 0)) else None)
(n_par p) (n_depth p) (n_seg p)) in ns'.
assert (Hzl : elen (zupd ns q p') = m) by apply elen_zupd.
split. { subst ns' b0. unfold elen in *. rewrite !length_app, zupd_length. destruct ok0, ok1; cbn [length]; lia. }
split. { intros j Hj Hne. subst ns'. rewrite node_app_l by (rewrite Hzl; lia). rewrite node_zupd by lia. destruct (Z.eqb_spec j q); [lia| reflexivity]. }
split. { subst ns'. rewrite node_app_l by (rewrite Hzl; lia). rewrite node_zupd by lia. rewrite Z.eqb_refl. fold m. destruct (Z.ltb_spec q m); [reflexivity| lia]. }
split. { intros ->. subst ns'. rewrite node_app_r by (rewrite Hzl; lia). rewrite Hzl, Z.sub_diag. reflexivity. }
intros ->. assert (Hb0 : 0 <= b0 <= 1) by (subst b0; destruct ok0; lia).
subst ns'. change (m + (if ok0 then 1 else 0)) with (m + b0). rewrite node_app_r by (rewrite Hzl; lia). rewrite Hzl. replace (m + b0 - m) with b0 by lia.
subst b0. destruct ok0; reflexivity.
Qed.
End w.

Lemma tnth_app_new0 : forall tns x l, tnth (tns ++ x :: l) (elen tns) = x.
Proof. intros. rewrite tnth_app_r by lia. rewrite Z.sub_diag. reflexivity. Qed.
Lemma tnth_app_new1 : forall tns x y l, tnth (tns ++ x :: y :: l) (elen tns + 1) = y.
Proof. intros. rewrite tnth_app_r by lia. replace (elen tns + 1 - elen tns) with 1 by lia. reflexivity. Qed.
Lemma elen_app2 : forall {B} (l : list B) x y, elen (l ++ [x; y]) = elen l + 2.
Proof. intros. unfold elen. rewrite length_app. cbn [length]. lia. Qed.
Lemma elen_app1 : forall {B} (l : list B) x, elen (l ++ [x]) = elen l + 1.
Proof. intros. unfold elen. rewrite length_app. cbn [length]. lia. Qed.
Lemma map_zseq_ext : forall {B} (f g : Z -> B) a n, (forall j, a <= j < a + n -> f j = g j) -> map f (zseq a n) = map g (zseq a n).
Proof.
intros B f g a n H. apply map_ext_in. intros j Hj. apply In_zseq in Hj. apply H. exact Hj.
Qed.
Lemma map_zseq_snoc : forall {B} (f : Z -> B) a n, 0 <= n -> map f (zseq a (n + 1)) = map f (zseq a n) ++ [f (a + n)].
Proof. intros. rewrite zseq_succ by assumption. rewrite map_app. reflexivity. Qed.
Lemma tn_facts_intro : forall palc E lo hi (tn : tnode) (nd : anode (A := entry)),
pal_agrees palc E -> ent_ok E -> NoDup (map fst E) -> 0 <= lo -> lo <= hi -> hi < elen E ->
n_lo nd = lo -> n_hi nd = hi -> n_seg nd = zsub E lo hi -> 0 <= tn_cut tn <= 2 ->
(forall d, 0 <= d <= 2 ->
is_quot (nth (Z.to_nat d) (tn_mean tn) 0) (wdot (node_list palc (fr_vals E) lo hi d)) (wsum (node_list palc (fr_vals E) lo hi d))) ->
(range_has_two palc lo hi -> dim_splits palc lo hi (tn_cut tn)) ->
tn_facts tn nd.
Proof.
intros palc E lo hi tn nd Hp HE Hnd Hlo Hle Hhi Elo Ehi Eseg Hcut Hq Hdim. split.
- intros d Hd. rewrite Eseg. change (segd d (zsub E lo hi)) with (dseg d E lo hi).
rewrite <- (node_list_dseg palc E lo hi d Hp ltac:(lia) Hlo ltac:(lia) Hhi). apply Hq. exact Hd.
- rewrite Elo, Ehi, Eseg. intros Hlt. change (segd (tn_cut tn) (zsub E lo hi)) with (dseg (tn_cut tn) E lo hi).
apply (neqd_of_dim_splits palc E lo hi (tn_cut tn) Hp Hlo Hhi ltac:(lia)).
apply Hdim. apply (range_has_two_of_NoDup palc E lo hi Hp Hnd Hlo Hlt Hhi).
Qed.
Lemma efreq_le_zsum : forall E j, ent_ok E -> 0 <= j < elen E -> efreq E j <= zsum (fr_vals E).
Proof.
intros E j HE Hj. pose proof (wsum_dseg_le 0 E j j HE ltac:(lia) ltac:(lia) ltac:(lia)) as [_ H].
pose proof (dseg_snoc 0 E j (j - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as X. replace (j - 1 + 1) with j in X by lia.
rewrite X, dseg_nil in H. cbn [app wsum] in H. lia.
Qed.
Lemma ent_freq31 : forall E, ent_ok E -> zsum (fr_vals E) < 2 ^ 31 -> Forall (fun e => snd e < 2 ^ 31) E.
Proof.
intros E HE Hs. apply Forall_forall. intros e He. apply In_nth with (d := dentry) in He as (n & Hn & <-).
pose proof (efreq_le_zsum E (Z.of_nat n) HE ltac:(unfold elen; lia)) as H. unfold efreq, znth in H. rewrite Nat2Z.id in H. lia.
Qed.
Lemma node_mem_ext : forall segs mem (ns ns' : list (anode (A := entry))) tns k j,
node ns' j = node ns j -> 0 <= j < elen tns ->
(n_leaf (node ns j) = false -> forall c, (n_k0 (node ns j) = Some c \/ n_k1 (node ns j) = Some c) -> 0 <= c < elen tns) ->
node_mem segs mem ns tns j -> node_mem segs mem ns' (tns ++ k) j.
Proof.
intros segs mem ns ns' tns k j Hn Hj Hk H. unfold node_mem in *. rewrite Hn. rewrite (tnth_app_l tns k j Hj).
destruct (n_leaf (node ns j)) eqn:El; [exact H|].
assert (O : forall o, (forall c, o = Some c -> 0 <= c < elen tns) -> oaddr (tns ++ k) o = oaddr tns o).
{ intros [c|] Ho; [|reflexivity]. cbn [oaddr]. rewrite tnth_app_l; [reflexivity|]. apply Ho. reflexivity. }
rewrite !O; [exact H | |]; intros c Hc; apply (Hk eq_refl c); [right | left]; exact Hc.
Qed.
