(** * BtItem6b — the symbol-side spelling: [BlcOf] and [ValidLengths] at the
      built tree.

    OWNER: an earlier development run.

    BtItem6 ended position-side: the output histogram counts window leaves by
    length.  The consumers (HuffGenCodes, LdDynV's item 6, the decode gate)
    speak SYMBOL-side: [bl_count (tree_lens t maxc)].  The census bijection —
    every live symbol parks exactly once, every dead symbol keeps its
    [bt_init] zero — converts one to the other, and the ported
    [KraftCount.LeavesAt_is_bl_count] plus a nat/Z bridge lands the Kraft
    equality in the decoder's own vocabulary. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes SendGo KraftCount Kraft15 KraftLens KraftInit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus1 BtCensus2 BtCensus3 BtCensus4 BtCensus5
  BtPass1 BtLevels BtAdjust BtPass2 BtItem6 KraftAdjust BuildTree BtSized.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** nat/Z bridges *)

Lemma filter_length_wsum : forall (f : nat -> bool) (n : nat),
  Z.of_nat (length (filter f (seq 0 n)))
  = wsum (fun s => ind (f (Z.to_nat s))) 0 n.
Proof.
  intros f n.
  induction n as [|k IH].
  - reflexivity.
  - rewrite seq_S, filter_app, length_app.
    replace (0 + k)%nat with k by lia.
    cbn [filter].
    rewrite (wsum_split_last (fun s => ind (f (Z.to_nat s))) 0 k).
    rewrite Z.add_0_l, Nat2Z.id.
    rewrite Nat2Z.inj_add, IH.
    destruct (f k) eqn:E; cbn [length ind]; lia.
Qed.

Lemma sum_over_bridge : forall (L : list nat) (blc : zarr) (M : Z)
                               (l : list nat),
  (forall j, In j l -> 1 <= Z.of_nat j <= M) ->
  (forall b, 1 <= b <= M -> blc b = Z.of_nat (bl_count L (Z.to_nat b))) ->
  Z.of_nat (list_sum
    (map (fun b => (bl_count L b * 2 ^ (Z.to_nat M - b))%nat) l))
  = zksum_over M blc l.
Proof.
  intros L blc M l Hin Hbl.
  induction l as [|a l IH].
  - rewrite zksum_over_nil. reflexivity.
  - cbn [map]. rewrite list_sum_cons, zksum_over_cons.
    rewrite Nat2Z.inj_add.
    rewrite IH by (intros j Hj; apply Hin; right; exact Hj).
    assert (Ha : 1 <= Z.of_nat a <= M) by (apply Hin; left; reflexivity).
    rewrite (Hbl (Z.of_nat a) Ha), Nat2Z.id.
    rewrite Nat2Z.inj_mul, Nat2Z.inj_pow.
    rewrite Nat2Z.inj_sub by lia.
    rewrite Z2Nat.id by lia.
    change (Z.of_nat 2) with 2.
    reflexivity.
Qed.

Lemma kraft_nat_z : forall (L : list nat) (blc : zarr) (M : Z),
  1 <= M ->
  (forall b, 1 <= b <= M -> blc b = Z.of_nat (bl_count L (Z.to_nat b))) ->
  Z.of_nat (list_sum
    (map (fun b => (bl_count L b * 2 ^ (Z.to_nat M - b))%nat)
         (seq 1 (Z.to_nat M))))
  = zksum M blc.
Proof.
  intros L blc M HM Hbl.
  unfold zksum.
  apply sum_over_bridge; [|exact Hbl].
  intros j Hj. apply in_seq in Hj.
  split; [lia|].
  destruct Hj as [_ Hj].
  rewrite <- (Z2Nat.id M) by lia. lia.
Qed.



(** ** The symbol side, under the census *)

Section SymSide.

Variables (elems maxc1 M : Z) (t1 tf : Tree) (hp3 : zarr) (hmaxf ndf : Z).
Hypothesis Hpk : BtParked elems maxc1 t1 tf hp3 hmaxf ndf.
Hypothesis HM : 1 <= M <= 15.
Variable t : Tree.
Hypothesis Hrng : forall p, hmaxf + 1 <= p < HEAP_SIZE -> hp3 p <= maxc1 ->
                  1 <= t_len t (hp3 p) <= M.
Hypothesis Hdead : forall s, 0 <= s <= maxc1 -> t_freq t1 s = 0 ->
                   t_len t s = 0.

Let NW := Z.to_nat (HEAP_SIZE - (hmaxf + 1)).
Let SW := Z.to_nat (maxc1 + 1).

Lemma sym_wsz : (S NW = Z.to_nat (HEAP_SIZE - hmaxf))%nat.
Proof.
  pose proof (pk_hmaxf_lt _ _ _ _ _ _ _ Hpk).
  unfold NW. rewrite <- Z2Nat.inj_succ by lia. f_equal. lia.
Qed.

Lemma sym_whi : hmaxf + Z.of_nat (S NW) = HEAP_SIZE.
Proof.
  pose proof (pk_hmaxf_lt _ _ _ _ _ _ _ Hpk).
  rewrite sym_wsz, Z2Nat.id by lia. lia.
Qed.

Lemma sym_pcount1 : forall s, 0 <= s <= maxc1 -> t_freq t1 s <> 0 ->
  wcount hp3 hmaxf (S NW) s = 1.
Proof.
  intros s Hs Hf.
  rewrite sym_wsz. fold (pcount hp3 hmaxf s).
  rewrite (bp_cnt _ _ _ _ _ _ _ Hpk s).
  rewrite (live_b_true t1 maxc1 s Hs Hf).
  pose proof (bp_maxc _ _ _ _ _ _ _ Hpk).
  replace ((elems <=? s) && (s <? ndf)) with false
    by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia).
  reflexivity.
Qed.

Lemma sym_pcount0 : forall s, 0 <= s <= maxc1 -> t_freq t1 s = 0 ->
  wcount hp3 hmaxf (S NW) s = 0.
Proof.
  intros s Hs Hf.
  rewrite sym_wsz. fold (pcount hp3 hmaxf s).
  rewrite (bp_cnt _ _ _ _ _ _ _ Hpk s).
  rewrite (live_b_false_dead t1 maxc1 s Hf).
  pose proof (bp_maxc _ _ _ _ _ _ _ Hpk).
  replace ((elems <=? s) && (s <? ndf)) with false
    by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia).
  reflexivity.
Qed.

Lemma sym_live_range : forall s, 0 <= s <= maxc1 -> t_freq t1 s <> 0 ->
  1 <= t_len t s <= M.
Proof.
  intros s Hs Hf.
  pose proof (sym_pcount1 s Hs Hf) as H1.
  destruct (wcount_pos_inv hp3 hmaxf (S NW) s ltac:(lia)) as [p [Hp He]].
  rewrite sym_whi in Hp.
  assert (Hpr : hmaxf + 1 <= p).
  { destruct (Z.eq_dec p hmaxf) as [->|Hne]; [|lia].
    exfalso.
    rewrite (bp_root _ _ _ _ _ _ _ Hpk) in He.
    pose proof (bp_ndf _ _ _ _ _ _ _ Hpk).
    pose proof (bp_maxc _ _ _ _ _ _ _ Hpk).
    lia. }
  rewrite <- He. apply Hrng; [lia | rewrite He; lia].
Qed.

Lemma sym_hist : forall b, 1 <= b ->
  BtPass2.hist maxc1 hp3 t b (hmaxf + 1) NW
  = wsum (fun s => ind (negb (Z.eqb (t_freq t1 s) 0)
                        && (Z.eqb (t_len t s) b))) 0 SW.
Proof.
  intros b Hb.
  pose proof (pk_hmaxf_lt _ _ _ _ _ _ _ Hpk) as Hlt.
  pose proof (bp_maxc _ _ _ _ _ _ _ Hpk) as Hmc.
  set (g := fun p => ind ((hp3 p <=? maxc1)
                          && (Z.eqb (t_len t (hp3 p)) b))).
  symmetry.
  rewrite (wsum_ext
             (fun s => ind (negb (Z.eqb (t_freq t1 s) 0)
                            && (Z.eqb (t_len t s) b)))
             (fun s => wsum (fun p => ind (Z.eqb (hp3 p) s) * g p)
                            hmaxf (S NW))
             0 SW).
  2: { intros s Hs.
       unfold SW in Hs. rewrite Z2Nat.id in Hs by lia.
       destruct (Z.eq_dec (t_freq t1 s) 0) as [Hf|Hf].
       - rewrite Hf.
         replace (Z.eqb 0 0) with true by reflexivity.
         cbn [negb andb ind].
         symmetry.
         transitivity (wsum (fun _ : Z => 0) hmaxf (S NW));
           [|apply wsum_zero].
         apply wsum_ext. intros p Hp.
         destruct (Z.eqb (hp3 p) s) eqn:Ee; [|cbn [ind]; lia].
         apply Z.eqb_eq in Ee. exfalso.
         pose proof (sym_pcount0 s ltac:(lia) Hf) as H0.
         pose proof (wcount_of_member hp3 hmaxf (S NW) s p Hp Ee). lia.
       - symmetry.
         apply (wsum_pick hp3 hmaxf (S NW) s
                  (ind (negb (Z.eqb (t_freq t1 s) 0)
                        && (Z.eqb (t_len t s) b))) g
                  (sym_pcount1 s ltac:(lia) Hf)).
         intros p Hp He. unfold g. rewrite He.
         replace (s <=? maxc1) with true
           by (symmetry; apply Z.leb_le; lia).
         replace (negb (Z.eqb (t_freq t1 s) 0)) with true
           by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact Hf).
         reflexivity. }
  rewrite (wsum_swap (fun s p => ind (Z.eqb (hp3 p) s) * g p)
             0 SW hmaxf (S NW)).
  rewrite (wsum_ext
             (fun p => wsum (fun s => ind (Z.eqb (hp3 p) s) * g p) 0 SW)
             g hmaxf (S NW)).
  2: { intros p Hp.
       rewrite sym_whi in Hp.
       rewrite (wsum_scale_r (fun s => ind (Z.eqb (hp3 p) s)) (g p) 0 SW).
       destruct (pk_member_class _ _ _ _ _ _ _ Hpk p Hp) as [[Hlv _]|Hcr].
       - rewrite (wsum_ext (fun s => ind (Z.eqb (hp3 p) s))
                    (fun s => ind (Z.eqb s (hp3 p))) 0 SW)
           by (intros s _; rewrite (Z.eqb_sym (hp3 p) s); reflexivity).
         rewrite (wsum_ind_eqb_one (hp3 p) 0 SW)
           by (unfold SW; rewrite Z2Nat.id by lia; lia).
         lia.
       - assert (Hz : wsum (fun s => ind (Z.eqb (hp3 p) s)) 0 SW = 0).
         { transitivity (wsum (fun _ : Z => 0) 0 SW); [|apply wsum_zero].
           apply wsum_ext. intros s Hs.
           unfold SW in Hs. rewrite Z2Nat.id in Hs by lia.
           replace (Z.eqb (hp3 p) s) with false
             by (symmetry; apply Z.eqb_neq; lia).
           reflexivity. }
         rewrite Hz.
         unfold g.
         replace (hp3 p <=? maxc1) with false
           by (symmetry; apply Z.leb_gt; lia).
         cbn [andb ind]. lia. }
  rewrite (wsum_split_first g hmaxf NW).
  assert (Hg0 : g hmaxf = 0).
  { unfold g.
    rewrite (bp_root _ _ _ _ _ _ _ Hpk).
    pose proof (bp_ndf _ _ _ _ _ _ _ Hpk).
    replace (ndf - 1 <=? maxc1) with false
      by (symmetry; apply Z.leb_gt; lia).
    reflexivity. }
  rewrite Hg0.
  unfold BtPass2.hist, g.
  replace (hmaxf + 1) with (hmaxf + 1) by lia.
  lia.
Qed.

Lemma sym_blcount : forall b, 1 <= b <= 15 ->
  wsum (fun s => ind (negb (Z.eqb (t_freq t1 s) 0)
                      && (Z.eqb (t_len t s) b))) 0 SW
  = Z.of_nat (bl_count (SendGo.tree_lens t maxc1) (Z.to_nat b)).
Proof.
  intros b Hb.
  pose proof (bp_maxc _ _ _ _ _ _ _ Hpk) as Hmc.
  rewrite <- (LeavesAt_is_bl_count t maxc1 (Z.to_nat b)).
  destruct (Z.to_nat b) as [|b'] eqn:Eb; [lia|].
  cbn [LeavesAt].
  rewrite filter_length_wsum.
  fold SW.
  symmetry.
  apply wsum_ext. intros s Hs.
  unfold SW in Hs. rewrite Z2Nat.id in Hs by lia.
  rewrite Z2Nat.id by lia.
  destruct (Z.eq_dec (t_freq t1 s) 0) as [Hf|Hf].
  - rewrite Hf.
    replace (Z.eqb 0 0) with true by reflexivity.
    cbn [negb andb ind].
    rewrite (Hdead s ltac:(lia) Hf).
    replace (Z.to_nat 0) with O by reflexivity.
    reflexivity.
  - pose proof (sym_live_range s ltac:(lia) Hf) as Hlr.
    replace (negb (Z.eqb (t_freq t1 s) 0)) with true
      by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact Hf).
    cbn [andb].
    destruct (Z.eq_dec (t_len t s) b) as [He|He].
    + replace (Nat.eqb (Z.to_nat (t_len t s)) (S b')) with true
        by (symmetry; apply Nat.eqb_eq; rewrite He, Eb; reflexivity).
      replace (Z.eqb (t_len t s) b) with true
        by (symmetry; apply Z.eqb_eq; exact He).
      reflexivity.
    + replace (Nat.eqb (Z.to_nat (t_len t s)) (S b')) with false
        by (symmetry; apply Nat.eqb_neq; intro Hc; apply He;
            rewrite <- Eb in Hc; apply Z2Nat.inj in Hc; lia).
      replace (Z.eqb (t_len t s) b) with false
        by (symmetry; apply Z.eqb_neq; exact He).
      reflexivity.
Qed.

Lemma sym_hist_high : forall b, M < b ->
  BtPass2.hist maxc1 hp3 t b (hmaxf + 1) NW = 0.
Proof.
  intros b Hb.
  pose proof (pk_hmaxf_lt _ _ _ _ _ _ _ Hpk) as Hlt.
  unfold BtPass2.hist.
  transitivity (wsum (fun _ : Z => 0) (hmaxf + 1) NW); [|apply wsum_zero].
  apply wsum_ext. intros p Hp.
  unfold NW in Hp. rewrite Z2Nat.id in Hp by lia.
  destruct (Z.leb (hp3 p) maxc1) eqn:El; [|reflexivity].
  apply Z.leb_le in El.
  assert (1 <= t_len t (hp3 p) <= M) by (apply Hrng; [lia | exact El]).
  replace (Z.eqb (t_len t (hp3 p)) b) with false
    by (symmetry; apply Z.eqb_neq; lia).
  rewrite andb_false_r. reflexivity.
Qed.

Theorem sym_BlcOf : forall blc,
  (forall b, 1 <= b <= M ->
   blc b = BtPass2.hist maxc1 hp3 t b (hmaxf + 1) NW) ->
  (forall b, b < 1 \/ M < b -> blc b = 0) ->
  BlcOf blc (SendGo.tree_lens t maxc1).
Proof.
  intros blc Hh Hz.
  unfold BlcOf. intros b Hb. unfold MAX_BITS in Hb.
  destruct (Z.eq_dec b 0) as [->|Hb0].
  - rewrite (Hz 0 ltac:(lia)).
    replace (Z.to_nat 0) with O by reflexivity.
    reflexivity.
  - destruct (Z_le_gt_dec b M) as [HbM|HbM].
    + rewrite (Hh b ltac:(lia)), (sym_hist b ltac:(lia)).
      apply sym_blcount. lia.
    + rewrite (Hz b ltac:(lia)).
      rewrite <- (sym_blcount b ltac:(lia)).
      rewrite <- (sym_hist b ltac:(lia)).
      rewrite (sym_hist_high b ltac:(lia)).
      reflexivity.
Qed.

Theorem sym_valid : forall blc,
  (forall b, 1 <= b <= M ->
   blc b = BtPass2.hist maxc1 hp3 t b (hmaxf + 1) NW) ->
  (forall b, b < 1 \/ M < b -> blc b = 0) ->
  zksum M blc = 2 ^ M ->
  ValidLengths (SendGo.tree_lens t maxc1) (Z.to_nat M).
Proof.
  intros blc Hh Hz Hzk.
  pose proof (sym_BlcOf blc Hh Hz) as HB.
  apply kraft_from_histogram.
  - intros len Hin.
    destruct (in_tree_lens_inv t maxc1 len Hin) as [i [Hi Hlen]].
    subst len.
    destruct (Z.eq_dec (t_freq t1 i) 0) as [Hf|Hf].
    + rewrite (Hdead i Hi Hf). lia.
    + pose proof (sym_live_range i Hi Hf). 
      assert (Z.to_nat (t_len t i) <= Z.to_nat M)%nat
        by (apply Z2Nat.inj_le; lia).
      lia.
  - assert (Hbl : forall b, 1 <= b <= M ->
            blc b = Z.of_nat (bl_count (SendGo.tree_lens t maxc1)
                                       (Z.to_nat b))).
    { intros b Hb. apply HB. unfold MAX_BITS. lia. }
    pose proof (kraft_nat_z (SendGo.tree_lens t maxc1) blc M
                  ltac:(lia) Hbl) as HKZ.
    rewrite Hzk in HKZ.
    assert (HP : Z.of_nat (2 ^ Z.to_nat M) = 2 ^ M)
      by (rewrite Nat2Z.inj_pow, Z2Nat.id by lia; reflexivity).
    lia.
Qed.

End SymSide.

Print Assumptions sym_hist.
Print Assumptions sym_blcount.
Print Assumptions sym_BlcOf.
Print Assumptions sym_valid.

(** ** Setter projections (one at a time — see BuildTree.v's 18 GB warning) *)

Lemma mc_statlen : forall v s, ts_maxcode (set_statlen v s) = ts_maxcode s.
Proof. reflexivity. Qed.
Lemma mc_optlen : forall v s, ts_maxcode (set_optlen v s) = ts_maxcode s.
Proof. reflexivity. Qed.
Lemma mc_heapmax : forall v s, ts_maxcode (set_heapmax v s) = ts_maxcode s.
Proof. reflexivity. Qed.
Lemma mc_heaplen : forall v s, ts_maxcode (set_heaplen v s) = ts_maxcode s.
Proof. reflexivity. Qed.
Lemma mc_depth : forall v s, ts_maxcode (set_depth v s) = ts_maxcode s.
Proof. reflexivity. Qed.
Lemma mc_heap : forall v s, ts_maxcode (set_heap v s) = ts_maxcode s.
Proof. reflexivity. Qed.
Lemma mc_blcount : forall v s, ts_maxcode (set_blcount v s) = ts_maxcode s.
Proof. reflexivity. Qed.
Lemma mc_settree : forall k t s, ts_maxcode (set_tree k t s) = ts_maxcode s.
Proof. reflexivity. Qed.
Lemma mc_max : forall k v s, ts_maxcode (set_max k v s) k = v.
Proof.
  intros k v s. unfold set_max, set_maxcode. cbn [ts_maxcode].
  rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma bc_statlen : forall v s, ts_blcount (set_statlen v s) = ts_blcount s.
Proof. reflexivity. Qed.
Lemma bc_optlen : forall v s, ts_blcount (set_optlen v s) = ts_blcount s.
Proof. reflexivity. Qed.
Lemma bc_heapmax : forall v s, ts_blcount (set_heapmax v s) = ts_blcount s.
Proof. reflexivity. Qed.
Lemma bc_heaplen : forall v s, ts_blcount (set_heaplen v s) = ts_blcount s.
Proof. reflexivity. Qed.
Lemma bc_depth : forall v s, ts_blcount (set_depth v s) = ts_blcount s.
Proof. reflexivity. Qed.
Lemma bc_heap : forall v s, ts_blcount (set_heap v s) = ts_blcount s.
Proof. reflexivity. Qed.
Lemma bc_max : forall k v s, ts_blcount (set_max k v s) = ts_blcount s.
Proof. reflexivity. Qed.
Lemma bc_settree : forall k t s, ts_blcount (set_tree k t s) = ts_blcount s.
Proof. reflexivity. Qed.
Lemma bc_setblc : forall v s, ts_blcount (set_blcount v s) = v.
Proof. reflexivity. Qed.

Lemma s1_maxcode : forall k maxc1 stf ol1 sl1 s,
  ts_maxcode (s1_of k maxc1 stf ol1 sl1 s) k = maxc1.
Proof.
  intros. unfold s1_of.
  rewrite mc_statlen, mc_optlen, mc_heapmax, mc_heaplen, mc_depth, mc_heap.
  apply mc_max.
Qed.

Lemma s1_blcount : forall k maxc1 stf ol1 sl1 s,
  ts_blcount (s1_of k maxc1 stf ol1 sl1 s) = ts_blcount s.
Proof.
  intros. unfold s1_of.
  rewrite bc_statlen, bc_optlen, bc_heapmax, bc_heaplen, bc_depth, bc_heap,
          bc_max, bc_settree.
  reflexivity.
Qed.

Lemma gen_bitlen_maxcode : forall k s1,
  ts_maxcode (gen_bitlen k s1) = ts_maxcode s1.
Proof.
  intros k s1. unfold gen_bitlen.
  destruct (gb_pass1 (Z.to_nat HEAP_SIZE + 1) k (ts_heap s1)
              (ts_maxcode s1 k) (sd_max_length k) (sd_extra_base k)
              (sd_extra k) (sd_stree k) (ts_heapmax s1 + 1)
              (t_setlen (ts_trees s1 k) (ts_heap s1 (ts_heapmax s1)) 0)
              (arr_zero (Z.to_nat MAX_BITS + 1) 0 (ts_blcount s1))
              (ts_optlen s1) (ts_statlen s1) 0)
    as [[[[t2 blc1] ol1] sl1] ov].
  destruct (Z.eqb ov 0).
  - rewrite mc_statlen, mc_optlen, mc_blcount, mc_settree. reflexivity.
  - destruct (gb_pass2 (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
                (ts_heap s1) (ts_maxcode s1 k) t2
                (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov)
                (sd_max_length k)
                (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov
                   (sd_max_length k))
                HEAP_SIZE ol1) as [t3 ol2].
    rewrite mc_statlen, mc_optlen, mc_blcount, mc_settree. reflexivity.
Qed.

Lemma tree_lens_gen_codes : forall t maxc blc mc,
  SendGo.tree_lens (gen_codes t maxc blc) mc = SendGo.tree_lens t mc.
Proof.
  intros. unfold SendGo.tree_lens.
  apply map_ext. intro i. rewrite gen_codes_len. reflexivity.
Qed.

(** ** [bt_force2] keeps the union array and only raises frequencies *)

Definition f2_tree (r : Tree * zarr * zarr * Z * Z * Z * Z) : Tree :=
  match r with (t, _, _, _, _, _, _) => t end.

Lemma bt_force2_dl_eq : forall fuel stree t hp dep hlen maxc ol sl,
  tr_dl (f2_tree (bt_force2 fuel stree t hp dep hlen maxc ol sl)) = tr_dl t.
Proof.
  induction fuel as [|f IH]; intros stree t hp dep hlen maxc ol sl.
  - reflexivity.
  - cbn [bt_force2].
    destruct (Z.leb 2 hlen); [reflexivity|].
    rewrite IH. reflexivity.
Qed.

Lemma bt_force2_freq0 : forall fuel stree t hp dep hlen maxc ol sl x,
  t_freq (f2_tree (bt_force2 fuel stree t hp dep hlen maxc ol sl)) x = 0 ->
  t_freq t x = 0.
Proof.
  induction fuel as [|f IH]; intros stree t hp dep hlen maxc ol sl x H.
  - exact H.
  - cbn [bt_force2] in H.
    destruct (Z.leb 2 hlen); [exact H|].
    apply IH in H.
    destruct (Z.eq_dec x (if Z.ltb maxc 2 then maxc + 1 else 0)) as [->|Hne].
    + exfalso. unfold t_freq, t_setfreq in H. cbn [tr_fc] in H.
      rewrite zset_same in H. unfold u16 in H. cbn in H. lia.
    + unfold t_freq, t_setfreq in H. cbn [tr_fc] in H.
      rewrite zset_other in H by exact Hne. exact H.
Qed.

Print Assumptions s1_maxcode.
Print Assumptions gen_bitlen_maxcode.
Print Assumptions bt_force2_freq0.

(** ** THE DELIVERABLE: item 6 and [BlcOf] at [build_tree]'s own call shape *)

Theorem build_tree_out :
  forall k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf,
  3 <= sd_elems k <= L_CODES ->
  1 <= sd_max_length k <= 15 ->
  4 * (hlen1 - 1) < 2 ^ sd_max_length k ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k) (ts_heap s)
          (ts_depth s) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen s) (ts_statlen s)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  bt_loop (Z.to_nat HEAP_SIZE)
          {| b_tree := t1;
             b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                                  (hlen1 / 2);
             b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
             b_node := sd_elems k |}
    = Some stf ->
  ts_maxcode (build_tree k s) k = maxc1
  /\ ValidLengths (SendGo.tree_lens (ts_trees (build_tree k s) k) maxc1)
       (Z.to_nat (sd_max_length k))
  /\ BlcOf (ts_blcount (build_tree k s))
       (SendGo.tree_lens (ts_trees (build_tree k s) k) maxc1)
  /\ zksum (sd_max_length k) (ts_blcount (build_tree k s))
     = 2 ^ sd_max_length k
  /\ (forall x, 0 <= x < sd_elems k -> t_freq t1 x = 0 ->
      t_len (ts_trees (build_tree k s) k) x = 0)
  /\ (forall x, maxc1 < x < sd_elems k -> t_freq t1 x = 0)
  /\ (forall x, 0 <= x < sd_elems k ->
      0 <= t_len (ts_trees (build_tree k s) k) x <= sd_max_length k).
Proof.
  intros k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
         Hel HM HK Hbl0 E0 E2 Eloop.
  destruct (build_tree_parked k s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1
              (bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2))
              stf Hel E0 E2 eq_refl Eloop)
    as [Hpk [Hout1 [Hsz [Hcen Hfr0]]]].
  set (hp3 := zset (b_heap stf) (b_hmax stf - 1) (b_heap stf 1)) in *.
  set (hmaxf := b_hmax stf - 1) in *.
  set (ndf := b_node stf) in *.
  set (M := sd_max_length k) in *.
  pose proof (bp_hmax _ _ _ _ _ _ _ Hpk) as Hhm.
  pose proof (bp_maxc _ _ _ _ _ _ _ Hpk) as Hmcb.
  assert (Hmf0 : 0 <= hmaxf)
    by (unfold HEAP_SIZE in Hhm; unfold L_CODES in Hsz; lia).
  unfold build_tree. cbv zeta.
  rewrite E0. cbv beta match.
  rewrite E2. cbv beta match.
  rewrite Eloop. cbv beta match.
  fold (s1_of k maxc1 stf ol1 sl1 s).
  set (s2 := gen_bitlen k (s1_of k maxc1 stf ol1 sl1 s)) in *.
  rewrite set_tree_same, bc_settree, mc_settree.
  assert (Gmc : ts_maxcode s2 k = maxc1)
    by (unfold s2; rewrite gen_bitlen_maxcode; apply s1_maxcode).
  rewrite Gmc.
  rewrite tree_lens_gen_codes.
  destruct (gen_bitlen_out k (s1_of k maxc1 stf ol1 sl1 s)
              (sd_elems k) maxc1 M t1 (b_tree stf) hp3 hmaxf ndf hlen1
              Hpk HM Hmf0 eq_refl
              (s1_heap k maxc1 stf ol1 sl1 s)
              (s1_heapmax k maxc1 stf ol1 sl1 s)
              (s1_trees k maxc1 stf ol1 sl1 s)
              (s1_maxcode k maxc1 stf ol1 sl1 s)
              ltac:(intros b Hb; rewrite s1_blcount; apply Hbl0; exact Hb)
              Hcen ltac:(lia) HK)
    as [G1 [G2 [G3 [G4 [G5 G6]]]]].
  fold s2 in G1, G2, G3, G4, G5, G6.
  set (t2t := ts_trees s2 k) in *.
  assert (Hdead0 : forall s', 0 <= s' < sd_elems k -> t_freq t1 s' = 0 ->
                   t_len t2t s' = 0).
  { intros s' Hs' Hf.
    assert (Hpc : pcount hp3 hmaxf s' = 0).
    { rewrite (bp_cnt _ _ _ _ _ _ _ Hpk s').
      assert (Hlb : live_b t1 maxc1 s' = false)
        by (apply live_b_false_dead; exact Hf).
      rewrite Hlb.
      replace ((sd_elems k <=? s') && (s' <? ndf)) with false
        by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia).
      reflexivity. }
    unfold t_len. rewrite (G5 s' Hpc).
    pose proof (bt_force2_dl_eq 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
                  (ts_optlen s) (ts_statlen s)) as HF2.
    rewrite E2 in HF2. cbn [f2_tree] in HF2.
    rewrite HF2.
    pose proof (bt_init_zeroes_zero_freq (Z.to_nat L_CODES + 2) 0
                  (sd_elems k) (ts_trees s k) (ts_heap s) (ts_depth s)
                  0 (-1) s') as HZ.
    rewrite E0 in HZ. cbn [bti_tree] in HZ.
    apply HZ.
    - rewrite Nat2Z.inj_add, Z2Nat.id by (unfold L_CODES; lia).
      change (Z.of_nat 2) with 2. lia.
    - lia.
    - rewrite <- (Hfr0 s').
      pose proof (bt_force2_freq0 3%nat (sd_stree k) t0 hp0 dep0 hlen0
                    maxc0 (ts_optlen s) (ts_statlen s) s') as HF0.
      rewrite E2 in HF0. cbn [f2_tree] in HF0.
      apply HF0. exact Hf. }
  assert (Hdead : forall s', 0 <= s' <= maxc1 -> t_freq t1 s' = 0 ->
                  t_len t2t s' = 0)
    by (intros s' Hs' Hf; apply Hdead0; [lia | exact Hf]).
  assert (Hh12 : forall b, 1 <= b <= M ->
          ts_blcount s2 b
          = BtPass2.hist maxc1 hp3 t2t b (hmaxf + 1)
              (Z.to_nat (HEAP_SIZE - (hmaxf + 1))))
    by (intros b Hb; apply G2; lia).
  split; [reflexivity|].
  split; [|split; [|split; [|split; [|split]]]].
  - apply (sym_valid (sd_elems k) maxc1 M t1 (b_tree stf) hp3 hmaxf ndf
             Hpk HM t2t G4 Hdead (ts_blcount s2) Hh12 G3 G1).
  - apply (sym_BlcOf (sd_elems k) maxc1 M t1 (b_tree stf) hp3 hmaxf ndf
             Hpk t2t G4 Hdead (ts_blcount s2) Hh12 G3).
  - exact G1.
  - intros x Hx Hf.
    unfold t_len. rewrite gen_codes_len.
    apply (Hdead0 x Hx Hf).
  - intros x Hx.
    pose proof (io_gapz _ _ _ _ _ Hout1 x Hx). assumption.
  - intros x Hx.
    unfold t_len. rewrite gen_codes_len.
    destruct (Z.eq_dec (t_freq t1 x) 0) as [Hf|Hf].
    + pose proof (Hdead0 x Hx Hf). unfold t_len in *. lia.
    + destruct (Z_le_gt_dec x maxc1) as [Hle|Hgt].
      * pose proof (sym_live_range (sd_elems k) maxc1 M t1 (b_tree stf) hp3
                      hmaxf ndf Hpk t2t G4 x ltac:(lia) Hf) as HR.
        unfold t_len in *. lia.
      * exfalso.
        pose proof (io_gapz _ _ _ _ _ Hout1 x ltac:(lia)). lia.
Qed.

Print Assumptions build_tree_out.
