(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees FillWinModel TreeModel BitsModel SendModel BitsModel2 CompressModel ScanModel FlushBlockModel TreesTab TrSmallModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BuildTreeModel GenBitlenModel GenCodesModel RefDeflSafeZ RefDeflSafeB1 RefDeflSafeB2 RefDeflSafeB3 RefDeflSafeB4 RefDeflSafeB5 RefDeflSafeB6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefCompressBlk1 RefSendTree3 RefSendTree4 RefFlushBlk12 RefFlushBlk13 RefDeflFastM RefDeflFast6 DeflateOverlay RefDeflSafeFB RefDeflSafeE1 RefDeflSafeE2 RefDeflSafeE3 RefDeflSafeE4 RefDeflSafeE5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_tr_cb4 Z_tr_fb8 Z_tr_fb11.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma brl_lt : forall k code res j, let len := Z.of_nat k in
  1 <= len -> 0 <= code -> 1 <= j -> j + len <= 17 -> 0 <= res < 2 ^ j -> 0 <= brl code res len < 2 ^ (j + len - 1).
Proof.
  induction k as [|k IH]; intros code res j len Hl Hc Hj Hjl Hr; [subst len; cbn in Hl; lia|].
  assert (Hv : 0 <= Z.lor (code mod 2 ^ 1) res < 2 ^ j) by (apply lor_bit_bound; [lia| exact Hr| apply (proj1 (Z.pow_gt_1 2 j ltac:(lia))); lia]).
  assert (Hp : 2 ^ j <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia).
  destruct (Z.eq_dec len 1) as [C1|C1].
  - rewrite C1. rewrite brl_last by lia. replace (j + 1 - 1) with j by lia. exact Hv.
  - rewrite brl_step by lia. subst len.
    set (v := Z.lor (code mod 2 ^ 1) res) in *.
    replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia.
    replace (j + Z.of_nat (S k) - 1) with ((j + 1) + Z.of_nat k - 1) by lia.
    apply IH; [lia| apply Z.div_pos; lia| lia| lia|].
    rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
Qed.

Lemma bi_reverse_lt : forall code len, 0 <= code -> 1 <= len <= 16 -> 0 <= bi_reverse code len < 2 ^ len.
Proof.
  intros code len Hc Hl. rewrite bi_reverse_brl by lia.
  pose proof (brl_lt (Z.to_nat len) code 0 1) as X. cbv zeta in X. rewrite Z2Nat.id in X by lia.
  replace (1 + len - 1) with len in X by lia. apply X; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma loop1_nonneg : forall f blc nc code bits, (forall i, 0 <= arr_get nc i) ->
  forall i, 0 <= arr_get (gen_codes_loop1 f blc nc code bits) i.
Proof.
  induction f as [|f IH]; intros blc nc code bits H i; cbn [gen_codes_loop1]; [apply H|].
  destruct (bits <=? MAX_BITS); [|apply H]. cbv zeta. apply IH.
  intros j. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range'| apply H].
Qed.

Lemma loop2_codes : forall f s0 t a nc mc n,
  arr_len a = tsize t -> 0 <= n -> mc < tsize t ->
  (forall i, 0 <= i <= mc -> Len s0 t i <> 0 -> 1 <= Len s0 t i <= 16) ->
  (forall i, 0 <= arr_get nc i) ->
  exists a', gen_codes_loop2 f (set_tree_fc s0 t a) t nc mc n = set_tree_fc s0 t a' /\ arr_len a' = tsize t
    /\ (forall i, (i < n \/ mc < i \/ Len s0 t i = 0) -> arr_get a' i = arr_get a i)
    /\ (forall i, n <= i <= mc -> i < n + Z.of_nat f -> Len s0 t i <> 0 -> 0 <= arr_get a' i < 2 ^ Len s0 t i).
Proof.
  induction f as [|f IH]; intros s0 t a nc mc n Ha Hn Hmc HL Hnc.
  - exists a. split; [reflexivity|]. split; [exact Ha|]. split; [intros; reflexivity| intros; lia].
  - rewrite loop2_S. destruct (Z.leb_spec n mc) as [Cn|Cn].
    2:{ exists a. split; [reflexivity|]. split; [exact Ha|]. split; [intros; reflexivity| intros; lia]. }
    cbv zeta. destruct (Z.eqb_spec (Len s0 t n) 0) as [Z0|NZ].
    + destruct (IH s0 t a nc mc (n + 1) Ha ltac:(lia) Hmc HL Hnc) as (a' & E & La & U & B).
      exists a'. split; [exact E|]. split; [exact La|]. split.
      * intros i Hi. apply U. lia.
      * intros i Hi Hf Hz. destruct (Z.eq_dec i n) as [->|Hne]; [congruence|]. apply B; lia.
    + set (v := wrap16 (bi_reverse (arr_get nc (Len s0 t n)) (Len s0 t n))).
      destruct (IH s0 t (arr_set a n v) (arr_set nc (Len s0 t n) (wrap16 (arr_get nc (Len s0 t n) + 1))) mc (n + 1)
                   ltac:(rewrite arr_len_set; exact Ha) ltac:(lia) Hmc HL
                   ltac:(intros i; rewrite arr_get_set; destruct (_ && _); [apply wrap16_range'| apply Hnc]))
        as (a' & E & La & U & B).
      exists a'. split; [exact E|]. split; [exact La|].
      assert (Hv : 0 <= v < 2 ^ Len s0 t n).
      { subst v. pose proof (HL n ltac:(lia) NZ) as R.
        pose proof (bi_reverse_lt (arr_get nc (Len s0 t n)) (Len s0 t n) (Hnc _) R) as Q.
        assert (P : 2 ^ Len s0 t n <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia). change (2 ^ 16) with 65536 in P.
        rewrite wrap16_id by lia. exact Q. }
      split.
      * intros i Hi. rewrite U by lia. apply arr_get_set_other. intros ->. lia.
      * intros i Hi Hf Hz. destruct (Z.eq_dec i n) as [->|Hne].
        -- rewrite U by lia. rewrite arr_get_set_same by (rewrite Ha; lia). exact Hv.
        -- apply B; lia.
Qed.

Lemma gen_codes_codes : forall X t mc, tree_lens X -> 0 <= mc < tsize t ->
  (forall i, 0 <= i <= mc -> Len X t i <> 0 -> 1 <= Len X t i <= 16) ->
  exists a', gen_codes X t mc = set_tree_fc X t a' /\ arr_len a' = tsize t
    /\ (forall c, (mc < c \/ Len X t c = 0) -> arr_get a' c = arr_get (tree_fc X t) c)
    /\ (forall c, 0 <= c <= mc -> Len X t c <> 0 -> 0 <= arr_get a' c < 2 ^ Len X t c).
Proof.
  intros X t mc TLX Hmc HL. unfold gen_codes.
  destruct (loop2_codes (Z.to_nat (mc + 1)) X t (tree_fc X t) (gen_codes_loop1 16 (ds_bl_count X) (arr_make (MAX_BITS + 1) 0) 0 1) mc 0
              (tree_lens_fc X t TLX) ltac:(lia) ltac:(lia) HL ltac:(apply loop1_nonneg; intros i; rewrite arr_get_make; lia))
    as (a' & E & La & U & B).
  rewrite stf_self in E. exists a'. split; [exact E|]. split; [exact La|]. split.
  - intros c Hc. apply U. lia.
  - intros c Hc Hz. apply B; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BTcodes.
Variable s : deflate_state.
Variable t : tree_id.
Hypothesis HP : bt_pre s t.

Theorem build_tree_codes : forall c, 0 <= c < sd_elems t -> 0 <= arr_get (tree_fc (build_tree s t) t) c < 2 ^ sd_max_length t.
Proof.
  intros c0 Hc0.
  pose proof (RefDeflSafeB1.elems_range t) as RE.
  pose proof (heap_phase_s s t HP) as H. cbv zeta in H.
  apply let_pair_elim in H. apply let_pair_elim in H.
  destruct H as (Fl & DL2 & HP2 & DP2 & L & FCf & DLf & HPf & DPf & E3 & E7 & HR & Z2 & LHP2 & LDP2 & LDL2 & RDP2 & RFC2 & RDL2 & LF & ND & FF & FCE & DLE).
  pose proof (hr_L _ _ _ _ _ _ _ _ _ HR) as RL. pose proof (ML_range t _ _ _ _ _ _ _ _ HR) as RML. pose proof (hr_mc _ _ _ _ _ _ _ _ _ HR) as Rmc.
  rewrite build_tree_unfold. cbv zeta. rewrite E7.
  set (p1 := build_tree_loop1 (Z.to_nat (sd_elems t)) (set_heap_max (set_heap_len s 0) HEAP_SIZE) t (sd_elems t) 0 (-1)) in *.
  set (p2 := build_tree_loop2 2 (fst p1) t (snd p1)) in *.
  set (mc := snd p2) in *.
  set (FC := tree_fc s t) in *. set (FC2 := fc_forced Fl FC) in *.
  pose proof (LBC s t HP) as LB.
  assert (ROL : 0 <= ol_forced Fl (ds_opt_len s) < 2 ^ 64).
  { unfold ol_forced. destruct Fl as [|a [|b [|c l]]]; cbn [fold_left]; [apply (bp_ol _ _ HP) | apply wrap64_range | apply wrap64_range | cbn in LF; lia]. }
  assert (RSL : 0 <= sl_forced t Fl (ds_static_len s) < 2 ^ 64).
  { unfold sl_forced. destruct (stree_has t); [| apply (bp_sl _ _ HP)].
    destruct Fl as [|a [|b [|c l]]]; cbn [fold_left]; [apply (bp_sl _ _ HP) | apply wrap64_range | apply wrap64_range | cbn in LF; lia]. }
  destruct (gen_bitlen_run t _ _ _ _ _ _ _ _ HR s (ds_bl_count s) (ol_forced Fl (ds_opt_len s)) (sl_forced t Fl (ds_static_len s)) LB ROL RSL)
    as ((DL' & BC' & OL' & SL' & EG & HD & RO & RS & LB' & RBC) & _ & _).
  change (RefDeflSafeB3.HM L) with (574 - 2 * L) in EG. rewrite EG.
  set (X := bt_upd s t FCf DL' HPf 1 (574 - 2 * L) DPf BC' OL' SL' mc).
  assert (TLX : tree_lens X) by (subst X; apply bt_tree_lens; try assumption; [apply (bp_tl _ _ HP) | apply (hr_lfc _ _ _ _ _ _ _ _ _ HR) | apply (dli_len _ _ _ _ _ HD) | apply (hr_lhp _ _ _ _ _ _ _ _ _ HR) | apply (hr_ldp _ _ _ _ _ _ _ _ _ HR)]).
  assert (LENX : forall i, Len X t i = arr_get DL' i) by (intros i; unfold Len; subst X; rewrite bt_tree_dl; reflexivity).
  assert (FCX : tree_fc X t = FCf) by (subst X; apply bt_tree_fc).
  assert (LEN : forall c, 0 <= c < sd_elems t -> (arr_get FC2 c = 0 -> arr_get DL' c = 0) /\ (arr_get FC2 c <> 0 -> 1 <= arr_get DL' c <= sd_max_length t /\ c <= mc)).
  { intros c Hc. exact (DLI_code t _ _ _ _ _ _ _ _ DL' c HR HD Hc). }
  destruct (gen_codes_codes X t mc TLX ltac:(lia)
              ltac:(intros i Hi Hz; rewrite LENX in Hz |- *; destruct (LEN i ltac:(lia)) as [A B];
                    destruct (Z.eq_dec (arr_get FC2 i) 0) as [Z0|NZ]; [exfalso; exact (Hz (A Z0))| pose proof (B NZ); lia]))
    as (a' & EC & La & U & B).
  assert (CODES : forall c, 0 <= c < sd_elems t -> 0 <= arr_get a' c < 2 ^ sd_max_length t).
  { intros c Hc. destruct (LEN c Hc) as [A Bc]. destruct (Z.eq_dec (arr_get FC2 c) 0) as [Z0|NZ].
    - rewrite U by (right; rewrite LENX; exact (A Z0)). rewrite FCX, (hr_fc _ _ _ _ _ _ _ _ _ HR c Hc). rewrite Z0.
      split; [lia| apply Z.pow_pos_nonneg; lia].
    - destruct (Bc NZ) as [R1 R2]. pose proof (B c ltac:(lia) ltac:(rewrite LENX; lia)) as Q. rewrite LENX in Q.
      assert (P : 2 ^ arr_get DL' c <= 2 ^ sd_max_length t) by (apply Z.pow_le_mono_r; lia). lia. }
  rewrite EC, stf_get. apply CODES. exact Hc0.
Qed.

End BTcodes.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma td_cnt_pos : forall L mc f n p q k mx mn,
  0 <= n <= mc -> mc + 1 - n <= Z.of_nat f -> 0 <= k -> 1 <= mn ->
  (forall j, 0 <= j <= mc -> 0 <= L j <= 15) -> 15 < L (mc + 1) ->
  0 <= q <= 15 -> (1 <= q -> q <> p) ->
  (1 <= q \/ exists i, n < i <= mc /\ 1 <= L i) ->
  exists x, 0 <= x <= 15 /\ 1 <= td_cnt L mc f n p q k mx mn x.
Proof.
  intros L mc f. induction f as [|f IH]; intros n p q k mx mn Hn Hf Hk Hmn HL HG Hq Hfresh Hw; [lia|].
  cbn [td_cnt]. replace (n <=? mc) with true by (symmetry; apply Z.leb_le; lia).
  destruct ((k + 1 <? mx) && (q =? L (n + 1))) eqn:C.
  - (* [comment removed for export] *)
    apply andb_prop in C. destruct C as [_ C]. apply Z.eqb_eq in C.
    assert (Hn1 : n + 1 <= mc) by (destruct (Z.eq_dec n mc) as [->|]; [rewrite C in Hq; lia| lia]).
    apply (IH (n + 1) p (L (n + 1)) (k + 1) mx mn); [lia| lia| lia| lia| exact HL| exact HG| rewrite <- C; exact Hq| rewrite <- C; exact Hfresh|].
    destruct Hw as [W|(i & Hi & Li)]; [left; rewrite <- C; exact W|].
    destruct (Z.eq_dec i (n + 1)) as [->|Hne]; [left; exact Li| right; exists i; lia].
  - (* [comment removed for export] *)
    destruct (tree_counts q (L (n + 1))) as [mx' mn'] eqn:TC.
    pose proof (tree_counts_range _ _ _ _ TC) as [_ Rmn'].
    destruct (Z_lt_le_dec q 1) as [Q0|Q1].
    + (* [comment removed for export] *)
      destruct Hw as [W|(i & Hi & Li)]; [lia|].
      assert (Hn1 : n + 1 <= mc) by lia.
      destruct (IH (n + 1) q (L (n + 1)) 0 mx' mn' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HL HG ltac:(apply HL; lia) ltac:(lia)
                   ltac:(destruct (Z.eq_dec i (n + 1)) as [->|Hne]; [left; exact Li| destruct (Z_lt_le_dec (L (n + 1)) 1); [right; exists i; lia| left; lia]]))
        as (x & Hx & Cx).
      exists x. split; [exact Hx|]. pose proof (trip_cnt_nonneg mn q p (k + 1) x ltac:(lia)). lia.
    + (* [comment removed for export] *)
      exists q. split; [lia|].
      pose proof (td_cnt_nonneg L mc f (n + 1) q (L (n + 1)) 0 mx' mn' q) as R0.
      assert (T : 1 <= trip_cnt mn q p (k + 1) q); [|specialize (R0 ltac:(lia)); lia].
      unfold trip_cnt. destruct (k + 1 <? mn) eqn:E1; [rewrite Z.eqb_refl; lia|].
      replace (negb (q =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
      replace (negb (q =? p)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
      rewrite Z.eqb_refl. cbn [zind]. pose proof (zind_le1 (q =? REP_3_6)). unfold zind in *. destruct (q =? REP_3_6); lia.
Qed.

Lemma TDcnt_pos : forall L mc, 0 <= mc -> (forall j, 0 <= j <= mc -> 0 <= L j <= 15) -> 15 < L (mc + 1) ->
  (exists i, 0 <= i <= mc /\ 1 <= L i) -> exists x, 0 <= x <= 15 /\ 1 <= TDcnt L mc x.
Proof.
  intros L mc Hmc HL HG (i & Hi & Li). unfold TDcnt.
  pose proof (cnts0_range (L 0)) as (Rmn & _ & _). destruct (cnts0 (L 0)) as [mx mn]. cbn [fst snd] in Rmn.
  apply (td_cnt_pos L mc (Z.to_nat (mc + 1)) 0 (-1) (L 0) 0 mx mn); try lia.
  - exact HL.
  - apply HL; lia.
  - destruct (Z.eq_dec i 0) as [->|Hne]; [left; exact Li| right; exists i; lia].
Qed.

(* [comment removed for export] *)
Lemma bl_loop_ge : forall f s m k, 3 <= k <= m -> Len s TB (arr_get bl_order_a k) <> 0 -> k <= build_bl_tree_loop f s m.
Proof.
  induction f as [|f IH]; intros s m k Hk Hz; cbn [build_bl_tree_loop]; [lia|].
  replace (3 <=? m) with true by (symmetry; apply Z.leb_le; lia).
  destruct (Z.eqb_spec (Len s TB (arr_get bl_order_a m)) 0) as [Z0|NZ]; cbn [negb]; [|lia].
  apply IH; [|exact Hz]. destruct (Z.eq_dec k m) as [->|Hne]; [congruence| lia].
Qed.

(* [comment removed for export] *)
Lemma bl_order_inv : forall x, 0 <= x <= 15 -> exists k, 3 <= k <= 18 /\ arr_get bl_order_a k = x.
Proof.
  intros x Hx.
  assert (C : x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/ x = 11 \/ x = 12 \/ x = 13 \/ x = 14 \/ x = 15) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]];
    [exists 3| exists 17| exists 15| exists 13| exists 11| exists 9| exists 7| exists 5| exists 4| exists 6| exists 8| exists 10| exists 12| exists 14| exists 16| exists 18];
    (split; [lia| vm_compute; reflexivity]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FlushU.
Variable s : deflate_state.
Hypothesis OP : overlay_pre s.

Let TP : TPF s := tree_phase s OP.

(* [comment removed for export] *)
Lemma lmax_ge_256 : 256 <= ds_l_max_code (ov_X6 s).
Proof.
  destruct (op_hist _ OP) as (HL & _ & _).
  assert (NZ : arr_get (ds_dyn_ltree_fc s) END_BLOCK <> 0).
  { rewrite (HL END_BLOCK ltac:(unfold END_BLOCK, L_CODES; lia)). rewrite Z.eqb_refl. cbn [zind].
    pose proof (zsum_nonneg (fun i => zind (sym_lcode s i =? END_BLOCK)) 0 (Z.to_nat (nsym s)) ltac:(intros; apply zind_le1)). lia. }
  pose proof (proj2 (tp_LDu _ TP END_BLOCK ltac:(unfold END_BLOCK, L_CODES; lia) NZ)) as X. unfold END_BLOCK in X. exact X.
Qed.

Lemma used_END : 1 <= Len (ov_X6 s) TL END_BLOCK <= 15.
Proof.
  destruct (op_hist _ OP) as (HL & _ & _).
  assert (NZ : arr_get (ds_dyn_ltree_fc s) END_BLOCK <> 0).
  { rewrite (HL END_BLOCK ltac:(unfold END_BLOCK, L_CODES; lia)). rewrite Z.eqb_refl. cbn [zind].
    pose proof (zsum_nonneg (fun i => zind (sym_lcode s i =? END_BLOCK)) 0 (Z.to_nat (nsym s)) ltac:(intros; apply zind_le1)). lia. }
  exact (proj1 (tp_LDu _ TP END_BLOCK ltac:(unfold END_BLOCK, L_CODES; lia) NZ)).
Qed.

(* [comment removed for export] *)
Lemma tree_fc_sol : forall x v t, tree_fc (set_opt_len x v) t = tree_fc x t.
Proof. intros x v t. destruct t; reflexivity. Qed.

Lemma scan_tree_fc_other : forall x t mc t', t' <> TB -> tree_fc (scan_tree x t mc) t' = tree_fc x t'.
Proof.
  intros x t mc t' Ht. unfold scan_tree.
  destruct (if Len x t 0 =? 0 then (138, 3) else (7, 4)) as [mxc mnc].
  rewrite <- (sbf_self (set_Len x t (mc + 1) 65535)).
  destruct (scan_loop_shape (Z.to_nat (mc + 1)) (set_Len x t (mc + 1) 65535) (ds_bl_tree_fc (set_Len x t (mc + 1) 65535)) t mc 0 (-1) (Len x t 0) 0 mxc mnc)
    as (b' & E & _ & _).
  rewrite E, sbf_tree_fc, tree_fc_set_Len by exact Ht. reflexivity.
Qed.

Lemma fc6_TL : tree_fc (ov_X6 s) TL = tree_fc (build_tree (ov_X0 s) TL) TL.
Proof.
  unfold ov_X6, tfb_X6. rewrite tree_fc_sol. unfold ov_X5.
  destruct (build_tree_facts (ov_X4 s) TB (tp_bp4 _ TP)) as (FC5 & DL5 & HP5 & DP5 & BC5 & L5 & mc5 & Fl5 & SO5 & SS5 & EX5 & _).
  rewrite EX5, bt_tree_fc_other by discriminate. unfold ov_X4. rewrite scan_tree_fc_other by discriminate.
  unfold ov_X3. rewrite scan_tree_fc_other by discriminate. unfold ov_X2.
  destruct (build_tree_facts (ov_X1 s) TD (tp_bp1 _ TP)) as (FC2 & DL2 & HP2 & DP2 & BC2 & L2 & mc2 & Fl2 & SO2 & SS2 & EX2 & _).
  rewrite EX2, bt_tree_fc_other by discriminate. reflexivity.
Qed.

Lemma fc6_TD : tree_fc (ov_X6 s) TD = tree_fc (build_tree (ov_X1 s) TD) TD.
Proof.
  unfold ov_X6, tfb_X6. rewrite tree_fc_sol. unfold ov_X5.
  destruct (build_tree_facts (ov_X4 s) TB (tp_bp4 _ TP)) as (FC5 & DL5 & HP5 & DP5 & BC5 & L5 & mc5 & Fl5 & SO5 & SS5 & EX5 & _).
  rewrite EX5, bt_tree_fc_other by discriminate. unfold ov_X4. rewrite scan_tree_fc_other by discriminate.
  unfold ov_X3. rewrite scan_tree_fc_other by discriminate. reflexivity.
Qed.

Lemma fc6_TB : tree_fc (ov_X6 s) TB = tree_fc (build_tree (ov_X4 s) TB) TB.
Proof. unfold ov_X6, tfb_X6. rewrite tree_fc_sol. reflexivity. Qed.

Lemma codes6_TL : c15 (ds_dyn_ltree_fc (ov_X6 s)) 286.
Proof.
  unfold c15. intros i Hi. rewrite <- RefDeflSafeE3.tree_fc_TL, fc6_TL.
  pose proof (build_tree_codes (ov_X0 s) TL (bt_pre_X0 s OP) i ltac:(cbn [sd_elems]; unfold L_CODES; lia)) as X.
  cbn [sd_max_length] in X. unfold MAX_BITS in X. change (2 ^ 15) with 32768 in X. exact X.
Qed.

Lemma codes6_TD : c15 (ds_dyn_dtree_fc (ov_X6 s)) 30.
Proof.
  unfold c15. intros i Hi. rewrite <- RefDeflSafeE3.tree_fc_TD, fc6_TD.
  pose proof (build_tree_codes (ov_X1 s) TD (tp_bp1 _ TP) i ltac:(cbn [sd_elems]; unfold D_CODES; lia)) as X.
  cbn [sd_max_length] in X. unfold MAX_BITS in X. change (2 ^ 15) with 32768 in X. exact X.
Qed.

Lemma codes6_TB : forall i, 0 <= i < 19 -> 0 <= arr_get (ds_bl_tree_fc (ov_X6 s)) i < 32768.
Proof.
  intros i Hi. rewrite <- RefDeflSafeE3.tree_fc_TB, fc6_TB.
  pose proof (build_tree_codes (ov_X4 s) TB (tp_bp4 _ TP) i ltac:(cbn [sd_elems]; unfold BL_CODES; lia)) as X.
  cbn [sd_max_length] in X. unfold MAX_BL_BITS in X. change (2 ^ 7) with 128 in X. lia.
Qed.

(* [comment removed for export] *)
Lemma mb_ge_3 : 3 <= ov_mb s.
Proof.
  pose proof (tp_lmax _ TP) as RL. pose proof (tp_LD _ TP) as LD. pose proof (tp_guard1 _ TP) as G1. pose proof lmax_ge_256 as E256. pose proof used_END as UE.
  unfold L_CODES in RL. unfold END_BLOCK in UE.
  destruct (TDcnt_pos (fun i => Len (ov_X6 s) TL i) (ds_l_max_code (ov_X6 s)) ltac:(lia) LD ltac:(cbv beta; rewrite G1; lia)
              ltac:(exists 256; cbv beta; lia)) as (x & Hx & Cx).
  pose proof (tp_BC _ TP x ltac:(lia)) as BCx.
  pose proof (TDcnt_nonneg (fun i => Len (ov_X6 s) TD i) (ds_d_max_code (ov_X6 s)) x) as D0.
  assert (NZ : arr_get (tree_fc (ov_X4 s) TB) x <> 0) by (rewrite (tp_fc4B _ TP), BCx; lia).
  destruct (build_tree_facts (ov_X4 s) TB (tp_bp4 _ TP)) as (FC5 & DL5 & HP5 & DP5 & BC5 & L5 & mc5 & Fl5 & SO5 & SS5 & EX5 & RL5 & Rmc5 & LF5 & ND5 & FF5 & LFC5 & LDL5 & LHP5 & LDP5 & LBC5 & TFC5 & TDL5 & TDP5 & RBC5 & Len5 & Use5 & _).
  cbn [sd_elems] in Use5. unfold BL_CODES in Use5.
  pose proof (Use5 x ltac:(lia) (or_introl NZ)) as [U1 _].
  destruct (bl_order_inv x Hx) as (k & Hk & Ek).
  unfold ov_mb, tfb_mb. apply (Z.le_trans 3 k); [lia|]. apply bl_loop_ge; [lia|].
  rewrite Ek. unfold Len, ov_X5. rewrite EX5, bt_tree_dl. lia.
Qed.

Theorem ubsan_dyn_X6 : ubsan_dyn (ov_X6 s) (ov_mb s).
Proof.
  unfold ubsan_dyn. split; [exact mb_ge_3|]. split; [exact lmax_ge_256|]. split; [exact codes6_TL|]. split; [exact codes6_TD| exact codes6_TB].
Qed.

End FlushU.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem flush_ubsan_pre : forall s, overlay_pre s -> forall buf len last, fb_ubsan s buf len last.
Proof.
  intros s OP buf len last. unfold fb_ubsan. intros Hl. cbv zeta. intros _.
  change (ubsan_dyn (ov_X6 s) (ov_mb s)). exact (ubsan_dyn_X6 s OP).
Qed.

Theorem flush_ubsan_facts : forall s last, fb_entry s last -> forall buf len, fb_ubsan s buf len last.
Proof. intros s last FE buf len. apply flush_ubsan_pre. exact (RefDeflSafeE5.OP s last FE). Qed.
