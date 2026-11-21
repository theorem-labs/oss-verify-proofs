(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac dsred :=
  cbn [set_status set_pending_buf set_pending_buf_size set_pending_out set_pending set_wrap set_gzhead
       set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size
       set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start
       set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead
       set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match
       set_nice_match set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc
       set_bl_tree_dl set_l_max_code set_d_max_code set_bl_max_code set_bl_count set_heap set_heap_len
       set_heap_max set_depth set_lit_bufsize set_sym_next set_sym_end set_opt_len set_static_len
       set_matches set_insert set_bi_buf set_bi_valid set_high_water set_self_blk set_window_blk
       set_prev_blk set_head_blk set_pending_buf_blk set_strm
       ds_status ds_pending_buf ds_pending_buf_size ds_pending_out ds_pending ds_wrap ds_gzhead
       ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size
       ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start
       ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead
       ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match
       ds_nice_match ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc
       ds_bl_tree_dl ds_l_max_code ds_d_max_code ds_bl_max_code ds_bl_count ds_heap ds_heap_len
       ds_heap_max ds_depth ds_lit_bufsize ds_sym_next ds_sym_end ds_opt_len ds_static_len
       ds_matches ds_insert ds_bi_buf ds_bi_valid ds_high_water ds_self_blk ds_window_blk
       ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm
       cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out
       cset_msg cset_data_type cset_adler
       cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg
       cs_data_type cs_adler
       fst snd].

Tactic Notation "dsred" "in" hyp(H) :=
  cbn [set_status set_pending_buf set_pending_buf_size set_pending_out set_pending set_wrap set_gzhead
       set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size
       set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start
       set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead
       set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match
       set_nice_match set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc
       set_bl_tree_dl set_l_max_code set_d_max_code set_bl_max_code set_bl_count set_heap set_heap_len
       set_heap_max set_depth set_lit_bufsize set_sym_next set_sym_end set_opt_len set_static_len
       set_matches set_insert set_bi_buf set_bi_valid set_high_water set_self_blk set_window_blk
       set_prev_blk set_head_blk set_pending_buf_blk set_strm
       ds_status ds_pending_buf ds_pending_buf_size ds_pending_out ds_pending ds_wrap ds_gzhead
       ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size
       ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start
       ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead
       ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match
       ds_nice_match ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc
       ds_bl_tree_dl ds_l_max_code ds_d_max_code ds_bl_max_code ds_bl_count ds_heap ds_heap_len
       ds_heap_max ds_depth ds_lit_bufsize ds_sym_next ds_sym_end ds_opt_len ds_static_len
       ds_matches ds_insert ds_bi_buf ds_bi_valid ds_high_water ds_self_blk ds_window_blk
       ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm
       cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out
       cset_msg cset_data_type cset_adler
       cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg
       cs_data_type cs_adler
       fst snd] in H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_mask_range : forall y m, 0 <= m -> 0 <= Z.land y m <= m.
Proof.
  intros y m Hm. split; [apply Z.land_nonneg; right; exact Hm|].
  destruct (Z.eq_dec m 0) as [->|Hm0]; [rewrite Z.land_0_r; lia|].
  (* [comment removed for export] *)
  pose proof (Z.add_nocarry_lxor (Z.land y m) (Z.ldiff m y)) as E.
  assert (D : Z.land (Z.land y m) (Z.ldiff m y) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.land_spec, Z.ldiff_spec, Z.bits_0.
    destruct (Z.testbit y n), (Z.testbit m n); reflexivity. }
  specialize (E D).
  assert (X : Z.lxor (Z.land y m) (Z.ldiff m y) = m).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.land_spec, Z.ldiff_spec.
    destruct (Z.testbit y n), (Z.testbit m n); reflexivity. }
  rewrite X in E. pose proof (Z.ldiff_nonneg m y) as Hl. lia.
Qed.

Lemma update_hash_range : forall s h c, 0 <= ds_hash_mask s -> 0 <= update_hash s h c <= ds_hash_mask s.
Proof. intros s h c Hm. unfold update_hash. apply land_mask_range. exact Hm. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record fw_wf (ws hs : Z) (s : deflate_state) : Prop := FWWF {
  wf_ws    : ds_w_size s = ws;
  wf_wsr   : 512 <= ws <= 32768;
  wf_wl    : arr_len (ds_window s) = 2 * ws;
  wf_wsz   : ds_window_size s = 2 * ws;
  wf_pl    : arr_len (ds_prev s) = ws;
  wf_wmask : ds_w_mask s = ws - 1;
  wf_hs    : ds_hash_size s = hs;
  wf_hsr   : 1 <= hs <= 65536;
  wf_hl    : arr_len (ds_head s) = hs;
  wf_hmask : ds_hash_mask s = hs - 1;
  wf_hshift : 0 <= ds_hash_shift s < 32;
  wf_ins   : 0 <= ds_insert s <= ds_strstart s;
  wf_look  : 0 <= ds_lookahead s;
  wf_sl    : ds_strstart s + ds_lookahead s <= 2 * ws;
  wf_ms    : 0 <= ds_match_start s < 2 ^ 32;
  wf_ih    : 0 <= ds_ins_h s < 2 ^ 32;
  wf_hw    : 0 <= ds_high_water s < 2 ^ 64;
  wf_ni    : 0 <= cs_next_in (ds_strm s);
  wf_ai    : 0 <= cs_avail_in (ds_strm s) < 2 ^ 32;
  wf_inlen : cs_next_in (ds_strm s) + cs_avail_in (ds_strm s) <= arr_len (cs_input (ds_strm s));
  wf_ti    : 0 <= cs_total_in (ds_strm s) < 2 ^ 64;
  wf_wrap  : 0 <= ds_wrap s <= 2;
  wf_ad1   : ds_wrap s = 1 -> 0 <= cs_adler (ds_strm s) < 2 ^ 64;   (* [comment removed for export] *)
  wf_ad2   : ds_wrap s = 2 -> 0 <= cs_adler (ds_strm s) < 2 ^ 64;
  wf_wb    : forall i, 0 <= i < 2 * ws -> 0 <= arr_get (ds_window s) i < 256;
  wf_pb    : forall i, 0 <= i < ws -> 0 <= arr_get (ds_prev s) i < 65536;
  wf_hb    : forall i, 0 <= i < hs -> 0 <= arr_get (ds_head s) i < 65536;
  wf_ib    : forall i, 0 <= i < arr_len (cs_input (ds_strm s)) -> 0 <= arr_get (cs_input (ds_strm s)) i < 256
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition shm (ws m : Z) : Z := wrap16 (if ws <=? m then m - ws else NIL).

Lemma shm_range : forall ws m, 0 <= shm ws m < 65536.
Proof. intros ws m. unfold shm. apply wrap16_range. Qed.

Lemma shm_small : forall ws m, 0 <= ws -> 0 <= m < 65536 ->
  shm ws m = (if ws <=? m then m - ws else 0).
Proof.
  intros ws m Hws Hm. unfold shm, NIL. rewrite wrap16_id; [reflexivity|].
  destruct (Z.leb_spec ws m); lia.
Qed.

Lemma slide_hash_loop_step : forall k a ws, 1 <= k ->
  slide_hash_loop (Z.to_nat k) a k ws =
  (let a' := arr_set a (k - 1) (shm ws (arr_get a (k - 1))) in
   if k - 1 =? 0 then a' else slide_hash_loop (Z.to_nat (k - 1)) a' (k - 1) ws).
Proof.
  intros k a ws Hk. replace (Z.to_nat k) with (S (Z.to_nat (k - 1))) by lia.
  cbn [slide_hash_loop]. unfold shm. destruct (k - 1 =? 0); reflexivity.
Qed.

Lemma slide_hash_loop_len : forall f a n ws, arr_len (slide_hash_loop f a n ws) = arr_len a.
Proof.
  induction f as [|f IH]; intros a n ws; [reflexivity|]. cbn [slide_hash_loop].
  destruct (negb (n - 1 =? 0)); rewrite ?IH, arr_len_set; reflexivity.
Qed.

Lemma slide_hash_loop_get : forall n a ws i (k : Z), k = Z.of_nat n -> k <= arr_len a ->
  arr_get (slide_hash_loop n a k ws) i
  = if (0 <=? i) && (i <? k) then shm ws (arr_get a i) else arr_get a i.
Proof.
  induction n as [|n IH]; intros a ws i k Hk Hlen.
  - cbn [slide_hash_loop]. subst k. change (Z.of_nat 0) with 0.
    destruct (Z.leb_spec 0 i), (Z.ltb_spec i 0); cbn [andb]; try reflexivity; lia.
  - cbn [slide_hash_loop]. fold (shm ws (arr_get a (k - 1))).
    destruct (Z.eqb_spec (k - 1) 0) as [E|NE]; cbn [negb].
    + rewrite arr_get_set. unfold arr_inb.
      destruct (Z.eqb_spec (k - 1) i), (Z.leb_spec 0 i), (Z.ltb_spec i k), (Z.leb_spec 0 (k - 1)),
        (Z.ltb_spec (k - 1) (arr_len a)); cbn [andb]; subst; try reflexivity; try lia;
      replace i with 0 by lia; reflexivity.
    + rewrite (IH _ ws i (k - 1)) by (rewrite ?arr_len_set; lia).
      rewrite arr_get_set. unfold arr_inb.
      destruct (Z.leb_spec 0 i), (Z.ltb_spec i (k - 1)), (Z.ltb_spec i k), (Z.eqb_spec (k - 1) i),
        (Z.leb_spec 0 (k - 1)), (Z.ltb_spec (k - 1) (arr_len a)); cbn [andb]; subst; try reflexivity; try lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fill_window_insert_step : forall ins s str, 1 <= ins ->
  fill_window_insert (Z.to_nat ins) s str =
    if negb (ds_insert s =? 0) then
      let h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) in
      let s1 := set_ins_h s h in
      let s2 := set_prev s1 (arr_set (ds_prev s1) (Z.land str (ds_w_mask s1)) (arr_get (ds_head s1) h)) in
      let s3 := set_head s2 (arr_set (ds_head s2) h (wrap16 str)) in
      let str' := str + 1 in
      let s4 := set_insert s3 (ds_insert s3 - 1) in
      if ds_lookahead s4 + ds_insert s4 <? MIN_MATCH then s4
      else fill_window_insert (Z.to_nat (ins - 1)) s4 str'
    else s.
Proof.
  intros ins s str Hins. replace (Z.to_nat ins) with (S (Z.to_nat (ins - 1))) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fill_window_loop_step : forall f s ws,
  fill_window_loop (S f) s ws =
  (let '(s', brk) := fill_window_body s ws in
   if brk then s'
   else if (ds_lookahead s' <? MIN_LOOKAHEAD) && negb (cs_avail_in (ds_strm s') =? 0)
        then fill_window_loop f s' ws else s').
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma crc32_upd_range : forall c buf,
  (forall b, In b buf -> 0 <= b < 256) -> 0 <= crc32_upd c buf < 2 ^ 32.
Proof.
  intros c buf Hb. unfold crc32_upd, crc32_model.
  change (2 ^ 32) with 4294967296. apply lxor_bound32; [|unfold MASK32; lia].
  apply crc_fold_range; [|exact Hb].
  apply lxor_bound32; [|unfold MASK32; lia]. pose proof (wrap32_range c). change (2 ^ 32) with 4294967296 in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma lor_shift16_add : forall b x, 0 <= x < 2 ^ 16 -> 0 <= b -> Z.lor (b * 2 ^ 16) x = b * 2 ^ 16 + x.
Proof.
  intros b x Hx Hb.
  assert (Hl : Z.land (b * 2 ^ 16) x = 0).
  { apply Z.bits_inj'; intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec n 16) as [L|L].
    - rewrite <- Z.shiftl_mul_pow2, Z.shiftl_spec_low by lia. reflexivity.
    - assert (Tx : Z.testbit x n = false).
      { apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|]. split; [lia|].
        eapply Z.lt_le_trans; [apply (proj2 Hx)|]. apply Z.pow_le_mono_r; lia. }
      rewrite Tx. apply Bool.andb_false_r. }
  rewrite <- Z.lxor_lor by exact Hl.
  symmetry. apply Z.add_nocarry_lxor. exact Hl.
Qed.

Lemma adler32_len1_range : forall a c, 0 <= c < 256 -> 0 <= adler32_len1 a c < 2 ^ 34.
Proof.
  intros a c Hc. unfold adler32_len1, adler_csub.
  pose proof (Z.mod_pos_bound a (2 ^ 16) ltac:(lia)) as H16.
  pose proof (Z.mod_pos_bound a (2 ^ 32) ltac:(lia)) as H32.
  assert (Hh : 0 <= a mod 2 ^ 32 / 2 ^ 16 < 2 ^ 16).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  set (h := a mod 2 ^ 32 / 2 ^ 16) in *. set (l := a mod 2 ^ 16) in *. clearbody h l.
  set (x := if 65520 <? l + c then l + c - 65521 else l + c).
  assert (Hx : 0 <= x < 2 ^ 16) by (subst x; destruct (Z.ltb_spec 65520 (l + c)); lia). clearbody x.
  set (b := if 65520 <? x + h then x + h - 65521 else x + h).
  assert (Hb : 0 <= b < 2 ^ 18) by (subst b; destruct (Z.ltb_spec 65520 (x + h)); lia). clearbody b.
  rewrite lor_shift16_add by lia. lia.
Qed.

Lemma adler32_upd_range : forall a buf,
  (forall b, In b buf -> 0 <= b < 256) -> 0 <= adler32_upd a buf < 2 ^ 64.
Proof.
  intros a buf Hb. unfold adler32_upd.
  destruct buf as [|c [|c' l]].
  - pose proof (adler32_model_canon a []) as ((? & ?) & _). lia.
  - pose proof (adler32_len1_range a c (Hb c (or_introl eq_refl))). lia.
  - pose proof (adler32_model_canon a (c :: c' :: l)) as ((? & ?) & _). lia.
Qed.

Lemma arr_slice_nat_In : forall (a : arr) k ofs b,
  (forall i, ofs <= i < ofs + Z.of_nat k -> 0 <= arr_get a i < 256) -> In b (arr_slice_nat a ofs k) -> 0 <= b < 256.
Proof.
  intros a k. induction k as [|k IH]; intros ofs b Hr Hin; [destruct Hin|].
  cbn [arr_slice_nat] in Hin. destruct Hin as [<-|Hin].
  - apply Hr. lia.
  - apply (IH (ofs + 1)); [intros i Hi; apply Hr; lia | exact Hin].
Qed.

Lemma arr_slice_In : forall (a : arr) ofs n b,
  (forall i, ofs <= i < ofs + n -> 0 <= arr_get a i < 256) -> In b (arr_slice a ofs n) -> 0 <= b < 256.
Proof.
  intros a ofs n b Hr Hin. unfold arr_slice in Hin.
  apply (arr_slice_nat_In a (Z.to_nat n) ofs b); [|exact Hin]. intros i Hi. apply Hr. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fw_slide (s : deflate_state) (ws more : Z) : deflate_state :=
  let s := set_window s (arr_blit (ds_window s) 0 (ds_window s) ws (wrap32 (ws - more))) in
  let s := set_match_start s (wrap32 (ds_match_start s - ws)) in
  let s := set_strstart s (ds_strstart s - ws) in
  let s := set_block_start s (ds_block_start s - ws) in
  let s := if ds_strstart s <? ds_insert s then set_insert s (ds_strstart s) else s in
  slide_hash s.

(* [comment removed for export] *)
Definition fw_insert (s : deflate_state) : deflate_state :=
  if MIN_MATCH <=? ds_lookahead s + ds_insert s then
    let str := ds_strstart s - ds_insert s in
    let s := set_ins_h s (arr_get (ds_window s) str) in
    let s := set_ins_h s (update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + 1))) in
    fill_window_insert (Z.to_nat (ds_insert s)) s str
  else s.

Definition fw_more (s : deflate_state) : Z := wrap32 (ds_window_size s - ds_lookahead s - ds_strstart s).

Lemma fill_window_body_eq : forall s ws,
  fill_window_body s ws =
  (let '(s1, more1) :=
     (if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s
      then (fw_slide s ws (fw_more s), wrap32 (fw_more s + ws)) else (s, fw_more s)) in
   if cs_avail_in (ds_strm s1) =? 0 then (s1, true)
   else let '(s2, n) := read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) more1 in
        (fw_insert (set_lookahead s2 (ds_lookahead s2 + n)), false)).
Proof. intros s ws. reflexivity. Qed.

(* [comment removed for export] *)
Definition fw_const (s s' : deflate_state) : Prop :=
  cs_input (ds_strm s') = cs_input (ds_strm s) /\ ds_wrap s' = ds_wrap s
  /\ ds_w_size s' = ds_w_size s /\ ds_hash_size s' = ds_hash_size s.

Local Ltac wf_tac HW := destruct HW; constructor; dsred; try assumption; try lia.

Lemma slide_hash_loop_wf16 : forall n a k ws i,
  k = Z.of_nat n -> k <= arr_len a -> (forall j, 0 <= j < arr_len a -> 0 <= arr_get a j < 65536) ->
  0 <= i < arr_len a -> 0 <= arr_get (slide_hash_loop n a k ws) i < 65536.
Proof.
  intros n a k ws i Hk Hka Ha Hi. rewrite (slide_hash_loop_get n a ws i k Hk Hka).
  destruct ((0 <=? i) && (i <? k)); [apply shm_range | apply Ha; exact Hi].
Qed.

Lemma fw_slide_wf : forall ws hs s more,
  fw_wf ws hs s -> ws + (ws - 262) <= ds_strstart s -> more = 2 * ws - ds_lookahead s - ds_strstart s ->
  fw_wf ws hs (fw_slide s ws more)
  /\ fw_const s (fw_slide s ws more)
  /\ ds_lookahead (fw_slide s ws more) = ds_lookahead s
  /\ ds_strstart (fw_slide s ws more) = ds_strstart s - ws.
Proof.
  intros ws hs s more HW Hsl Hmore.
  pose proof (wf_wsr _ _ _ HW) as Lws. pose proof (wf_sl _ _ _ HW) as Vsl. pose proof (wf_look _ _ _ HW) as Vlook.
  pose proof (wf_ins _ _ _ HW) as Vins. pose proof (wf_wl _ _ _ HW) as Vwl. pose proof (wf_pl _ _ _ HW) as Vpl.
  pose proof (wf_hl _ _ _ HW) as Vhl. pose proof (wf_hs _ _ _ HW) as Vhs. pose proof (wf_ws _ _ _ HW) as Vws.
  pose proof (wf_hsr _ _ _ HW) as Lhs.
  assert (Hn : wrap32 (ws - more) = ds_strstart s + ds_lookahead s - ws).
  { rewrite Hmore. rewrite wrap32_id by lia. lia. }
  unfold fw_slide, slide_hash. dsred.
  destruct (Z.ltb_spec (ds_strstart s - ws) (ds_insert s)) as [Lt|Ge]; dsred; rewrite Vws, Vhs, Hn.
  - split; [|split; [unfold fw_const; dsred; repeat split; reflexivity | split; reflexivity]].
    wf_tac HW.
    + rewrite arr_len_blit. assumption.
    + rewrite slide_hash_loop_len. assumption.
    + rewrite slide_hash_loop_len. assumption.
    + pose proof (wrap32_range (ds_match_start s - ws)). lia.
    + intros i Hi. rewrite arr_get_blit.
      destruct (Z.leb_spec 0 i), (Z.ltb_spec i (0 + Z.max 0 (ds_strstart s + ds_lookahead s - ws))), (arr_inb (ds_window s) i);
        cbn [andb]; apply wf_wb0; lia.
    + intros i Hi. apply (slide_hash_loop_wf16 (Z.to_nat ws) (ds_prev s) ws ws i); try lia. intros j Hj. apply wf_pb0. lia.
    + intros i Hi. apply (slide_hash_loop_wf16 (Z.to_nat hs) (ds_head s) hs ws i); try lia. intros j Hj. apply wf_hb0. lia.
  - split; [|split; [unfold fw_const; dsred; repeat split; reflexivity | split; reflexivity]].
    wf_tac HW.
    + rewrite arr_len_blit. assumption.
    + rewrite slide_hash_loop_len. assumption.
    + rewrite slide_hash_loop_len. assumption.
    + pose proof (wrap32_range (ds_match_start s - ws)). lia.
    + intros i Hi. rewrite arr_get_blit.
      destruct (Z.leb_spec 0 i), (Z.ltb_spec i (0 + Z.max 0 (ds_strstart s + ds_lookahead s - ws))), (arr_inb (ds_window s) i);
        cbn [andb]; apply wf_wb0; lia.
    + intros i Hi. apply (slide_hash_loop_wf16 (Z.to_nat ws) (ds_prev s) ws ws i); try lia. intros j Hj. apply wf_pb0. lia.
    + intros i Hi. apply (slide_hash_loop_wf16 (Z.to_nat hs) (ds_head s) hs ws i); try lia. intros j Hj. apply wf_hb0. lia.
Qed.

Lemma read_buf_wf : forall ws hs s off more,
  fw_wf ws hs s -> off = ds_strstart s + ds_lookahead s -> 0 <= more -> off + more <= 2 * ws ->
  let r := read_buf s (RB_window off) more in
  fw_wf ws hs (fst r) /\ fw_const s (fst r)
  /\ ds_lookahead (fst r) = ds_lookahead s /\ ds_strstart (fst r) = ds_strstart s /\ ds_insert (fst r) = ds_insert s
  /\ ds_hash_shift (fst r) = ds_hash_shift s /\ ds_hash_mask (fst r) = ds_hash_mask s /\ ds_w_mask (fst r) = ds_w_mask s
  /\ ds_ins_h (fst r) = ds_ins_h s
  /\ 0 <= snd r <= more /\ (cs_avail_in (ds_strm s) <> 0 -> 0 < more -> 0 < snd r)
  /\ cs_avail_in (ds_strm (fst r)) = cs_avail_in (ds_strm s) - snd r.
Proof.
  intros ws hs s off more HW Hoff Hmore Hom r. subst r.
  pose proof (wf_wsr _ _ _ HW) as Lws. pose proof (wf_ai _ _ _ HW) as Vai. pose proof (wf_ni _ _ _ HW) as Vni.
  pose proof (wf_inlen _ _ _ HW) as Vil. pose proof (wf_wl _ _ _ HW) as Vwl.
  unfold read_buf. cbv beta iota zeta.
  set (ai := cs_avail_in (ds_strm s)). set (len := if more <? ai then more else ai).
  assert (Hlen : 0 <= len <= ai /\ len <= more /\ (ai <> 0 -> 0 < more -> 0 < len))
    by (subst len ai; destruct (Z.ltb_spec more (cs_avail_in (ds_strm s))); lia).
  destruct (Z.eqb_spec len 0) as [L0|L0].
  { cbn [fst snd]. split; [exact HW|]. unfold fw_const. repeat split; try reflexivity; lia. }
  cbn [fst snd].
  assert (Hbytes : forall b, In b (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) len) -> 0 <= b < 256).
  { intros b Hb. eapply arr_slice_In; [|exact Hb]. intros i Hi. apply (wf_ib _ _ _ HW). subst ai. lia. }
  pose proof (wf_wrap _ _ _ HW) as Vwrap. dsred.
  destruct (Z.eqb_spec (ds_wrap s) 1) as [W1|W1]; [|destruct (Z.eqb_spec (ds_wrap s) 2) as [W2|W2]]; dsred.
  all: split; [| unfold fw_const; dsred; repeat split; try reflexivity; subst ai; lia].
  all: destruct HW; constructor; dsred; try assumption; try (subst ai; lia).
  all: try (rewrite arr_len_upd; assumption).
  all: try (pose proof (wrap64_range (cs_total_in (ds_strm s) + len)); lia).
  all: try (intros i Hi; rewrite (arr_get_upd _ _ _ _ 0);
            destruct (_ && _) eqn:E; [|apply wf_wb0; exact Hi];
            apply Hbytes; apply nth_In; apply Bool.andb_true_iff in E as [E _]; apply Bool.andb_true_iff in E as [E1 E2];
            apply Z.leb_le in E1; apply Z.ltb_lt in E2; unfold zlength in E2; lia).
  - intros _. apply adler32_upd_range. exact Hbytes.
  - intros _. pose proof (crc32_upd_range (cs_adler (ds_strm s)) _ Hbytes). lia.
Qed.

Lemma fill_window_insert_wf : forall n ws hs s str,
  ds_insert s = Z.of_nat n ->
  fw_wf ws hs s -> 0 <= str -> ds_insert s = ds_strstart s - str ->
  (ds_insert s <> 0 -> 3 <= ds_lookahead s + ds_insert s) ->
  let s' := fill_window_insert (Z.to_nat (ds_insert s)) s str in
  fw_wf ws hs s' /\ fw_const s s' /\ ds_lookahead s' = ds_lookahead s /\ ds_strstart s' = ds_strstart s
  /\ cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s).
Proof.
  induction n as [|n IH]; intros ws hs s str Hn HW Hstr Hins Hbig s'; subst s'.
  - rewrite Hn. change (Z.to_nat (Z.of_nat 0)) with 0%nat. cbn [fill_window_insert].
    split; [exact HW|]. unfold fw_const. repeat split; reflexivity.
  - rewrite (fill_window_insert_step (ds_insert s) s str) by lia.
    replace (ds_insert s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv zeta. dsred.
    pose proof (wf_wsr _ _ _ HW) as Lws. pose proof (wf_hsr _ _ _ HW) as Lhs. pose proof (wf_sl _ _ _ HW) as Vsl.
    pose proof (wf_look _ _ _ HW) as Vlook. pose proof (wf_hmask _ _ _ HW) as Vhm. pose proof (wf_wmask _ _ _ HW) as Vwm.
    pose proof (wf_wl _ _ _ HW) as Vwl. pose proof (wf_pl _ _ _ HW) as Vpl. pose proof (wf_hl _ _ _ HW) as Vhl.
    set (h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1)))).
    pose proof (update_hash_range s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) ltac:(lia)) as Hh.
    fold h in Hh.
    assert (Hy : 0 <= Z.land str (ds_w_mask s) <= ds_w_mask s) by (apply land_mask_range; lia).
    set (s4 := set_insert (set_head (set_prev (set_ins_h s h) (arr_set (ds_prev s) (Z.land str (ds_w_mask s)) (arr_get (ds_head s) h)))
                          (arr_set (ds_head s) h (wrap16 str))) (ds_insert s - 1)).
    assert (HW4 : fw_wf ws hs s4).
    { subst s4. destruct HW; constructor; dsred; try assumption; try lia.
      - rewrite arr_len_set. assumption.
      - rewrite arr_len_set. assumption.
      - intros i Hi. rewrite arr_get_set. destruct (_ && _); [apply wf_hb0; lia | apply wf_pb0; exact Hi].
      - intros i Hi. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply wf_hb0; exact Hi]. }
    change (set_insert (set_head (set_prev (set_ins_h s h) (arr_set (ds_prev s) (Z.land str (ds_w_mask s)) (arr_get (ds_head s) h)))
                          (arr_set (ds_head s) h (wrap16 str))) (ds_insert s - 1)) with s4.
    unfold MIN_MATCH. destruct (Z.ltb_spec (ds_lookahead s + (ds_insert s - 1)) 3) as [Brk|Cont].
    + split; [exact HW4|]. subst s4. unfold fw_const. dsred. repeat split; reflexivity.
    + assert (Hn4 : ds_insert s4 = Z.of_nat n) by (subst s4; dsred; lia).
      replace (Z.to_nat (ds_insert s - 1)) with (Z.to_nat (ds_insert s4)) by (rewrite Hn4; lia).
      destruct (IH ws hs s4 (str + 1) Hn4 HW4 ltac:(lia) ltac:(subst s4; dsred; lia) ltac:(subst s4; dsred; lia))
        as (HW' & HC' & HL' & HS' & HA').
      split; [exact HW'|]. revert HC' HL' HS' HA'. subst s4. unfold fw_const. dsred. tauto.
Qed.

Lemma fw_insert_wf : forall ws hs s,
  fw_wf ws hs s ->
  fw_wf ws hs (fw_insert s) /\ fw_const s (fw_insert s)
  /\ ds_lookahead (fw_insert s) = ds_lookahead s /\ ds_strstart (fw_insert s) = ds_strstart s
  /\ cs_avail_in (ds_strm (fw_insert s)) = cs_avail_in (ds_strm s).
Proof.
  intros ws hs s HW. unfold fw_insert, MIN_MATCH.
  destruct (Z.leb_spec 3 (ds_lookahead s + ds_insert s)) as [Big|Small].
  2: { split; [exact HW|]. unfold fw_const. repeat split; reflexivity. }
  cbv zeta.
  pose proof (wf_wsr _ _ _ HW) as Lws. pose proof (wf_hsr _ _ _ HW) as Lhs. pose proof (wf_sl _ _ _ HW) as Vsl.
  pose proof (wf_look _ _ _ HW) as Vlook. pose proof (wf_hmask _ _ _ HW) as Vhm. pose proof (wf_ins _ _ _ HW) as Vins.
  set (str := ds_strstart s - ds_insert s).
  set (s1 := set_ins_h s (arr_get (ds_window s) str)).
  set (s2 := set_ins_h s1 (update_hash s1 (ds_ins_h s1) (arr_get (ds_window s1) (str + 1)))).
  pose proof (wf_wb _ _ _ HW str ltac:(lia)) as Hb0.
  pose proof (update_hash_range s1 (ds_ins_h s1) (arr_get (ds_window s1) (str + 1)) ltac:(subst s1; dsred; lia)) as Hh1.
  assert (HW2 : fw_wf ws hs s2).
  { subst s2 s1. destruct HW; constructor; dsred; try assumption. revert Hh1. dsred. lia. }
  destruct (fill_window_insert_wf (Z.to_nat (ds_insert s)) ws hs s2 str ltac:(subst s2 s1; dsred; lia) HW2 ltac:(lia)
              ltac:(subst s2 s1; dsred; lia) ltac:(subst s2 s1; dsred; lia)) as (HW' & HC' & HL' & HS' & HA').
  replace (Z.to_nat (ds_insert s2)) with (Z.to_nat (ds_insert s)) in * by (subst s2 s1; dsred; reflexivity).
  split; [exact HW'|]. revert HC' HL' HS' HA'. subst s2 s1. unfold fw_const. dsred. tauto.
Qed.

(* [comment removed for export] *)
Lemma fill_window_body_wf : forall ws hs s,
  fw_wf ws hs s -> ds_lookahead s < MIN_LOOKAHEAD ->
  let '(s', brk) := fill_window_body s ws in
  fw_wf ws hs s' /\ fw_const s s'
  /\ (brk = false -> ds_lookahead s < ds_lookahead s' /\ ds_lookahead s' <= 2 * ws).
Proof.
  intros ws hs s HW Hlook. rewrite fill_window_body_eq.
  pose proof (wf_wsr _ _ _ HW) as Lws. pose proof (wf_sl _ _ _ HW) as Vsl. pose proof (wf_look _ _ _ HW) as Vlook.
  pose proof (wf_ws _ _ _ HW) as Vws. pose proof (wf_wsz _ _ _ HW) as Vwsz. pose proof (wf_ins _ _ _ HW) as Vins.
  unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *.
  assert (Hmore : fw_more s = 2 * ws - ds_lookahead s - ds_strstart s).
  { unfold fw_more. rewrite Vwsz. rewrite wrap32_id by lia. lia. }
  destruct (Z.leb_spec (ws + (ds_w_size s - (258 + 3 + 1))) (ds_strstart s)) as [Sl|Ns].
  - (* [comment removed for export] *)
    destruct (fw_slide_wf ws hs s (fw_more s) HW ltac:(lia) Hmore) as (HW1 & HC1 & HL1 & HS1).
    set (s1 := fw_slide s ws (fw_more s)) in *.
    assert (Hm1 : wrap32 (fw_more s + ws) = 3 * ws - ds_lookahead s - ds_strstart s).
    { rewrite Hmore. rewrite wrap32_id by lia. lia. }
    rewrite Hm1.
    destruct (Z.eqb_spec (cs_avail_in (ds_strm s1)) 0) as [A0|A0].
    + split; [exact HW1|]. split; [exact HC1|]. intros; discriminate.
    + destruct (read_buf_wf ws hs s1 (ds_strstart s1 + ds_lookahead s1) (3 * ws - ds_lookahead s - ds_strstart s) HW1 eq_refl
                  ltac:(lia) ltac:(lia)) as (HW2 & HC2 & HL2 & HS2 & _ & _ & _ & _ & _ & Hn & Hpos & _).
      destruct (read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) (3 * ws - ds_lookahead s - ds_strstart s)) as [s2 n].
      cbn [fst snd] in *.
      pose proof (wf_sl _ _ _ HW2) as Vsl2.
      destruct (fw_insert_wf ws hs (set_lookahead s2 (ds_lookahead s2 + n)) ltac:(destruct HW2; constructor; dsred; try assumption; lia))
        as (HW3 & HC3 & HL3 & HS3 & _).
      split; [exact HW3|].
      split; [revert HC1 HC2 HC3; unfold fw_const; dsred; intuition congruence|].
      intros _. rewrite HL3. dsred. specialize (Hpos A0 ltac:(lia)). lia.
  - destruct (Z.eqb_spec (cs_avail_in (ds_strm s)) 0) as [A0|A0].
    + split; [exact HW|]. split; [unfold fw_const; repeat split; reflexivity|]. intros; discriminate.
    + destruct (read_buf_wf ws hs s (ds_strstart s + ds_lookahead s) (fw_more s) HW eq_refl ltac:(lia) ltac:(lia))
        as (HW2 & HC2 & HL2 & HS2 & _ & _ & _ & _ & _ & Hn & Hpos & _).
      destruct (read_buf s (RB_window (ds_strstart s + ds_lookahead s)) (fw_more s)) as [s2 n].
      cbn [fst snd] in *.
      pose proof (wf_sl _ _ _ HW2) as Vsl2.
      destruct (fw_insert_wf ws hs (set_lookahead s2 (ds_lookahead s2 + n)) ltac:(destruct HW2; constructor; dsred; try assumption; lia))
        as (HW3 & HC3 & HL3 & HS3 & _).
      split; [exact HW3|].
      split; [revert HC2 HC3; unfold fw_const; dsred; intuition congruence|].
      intros _. rewrite HL3. dsred. specialize (Hpos A0 ltac:(lia)). lia.
Qed.
