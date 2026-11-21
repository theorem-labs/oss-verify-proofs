(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record st_entry (s : deflate_state) : Prop := {
  se_inv : so_inv s;
  se_pend : ds_pending s = 0;
  se_pout : ds_pending_out s = 0;
  se_bibuf : 0 <= ds_bi_buf s < 2 ^ 16;
  se_pbs : ds_pending_buf_size s = ds_lit_bufsize s * 4;
  se_ao : 0 <= cs_avail_out (ds_strm s) < 2 ^ 32 }.

(* [comment removed for export] *)
Definition TI (s : deflate_state) : Prop := st_entry s.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma arr_upd_bytes : forall (w : arr) ofs (l : list Z) (N : Z),
  (forall j, 0 <= j < N -> 0 <= arr_get w j < 256) ->
  (forall b, In b l -> 0 <= b < 256) ->
  forall j, 0 <= j < N -> 0 <= arr_get (arr_upd w ofs l) j < 256.
Proof.
  intros w ofs l N Hw Hl j Hj. rewrite (arr_get_upd l w ofs j 0).
  destruct (_ && _) eqn:E; [| apply Hw; exact Hj].
  apply Bool.andb_true_iff in E. destruct E as [E _]. apply Bool.andb_true_iff in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  apply Hl. apply nth_In. unfold zlength in E2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sb_hdr_eq' : forall s, 0 <= ds_bi_valid s <= 16 -> tsb_hP s + 4 = ds_pending s + sb_hdr s.
Proof.
  intros s H. unfold tsb_hP, sb_hdr. rewrite Z.shiftr_div_pow2 by lia.
  destruct (Z.leb_spec (ds_bi_valid s) 5); [| destruct (Z.leb_spec (ds_bi_valid s) 13)];
    (Z.to_euclidean_division_equations; lia).
Qed.

(* [comment removed for export] *)
Lemma tsb_none_facts : forall s last, 0 <= ds_bi_valid s <= 16 -> 0 <= ds_bi_buf s < 2 ^ 16 ->
  let s1 := tr_stored_block s None 0 last in
  ds_pending s1 = ds_pending s + sb_hdr s /\ ds_bi_valid s1 = 0 /\ ds_bi_buf s1 = 0
  /\ ds_pending_out s1 = ds_pending_out s /\ ds_strm s1 = ds_strm s /\ ds_window s1 = ds_window s
  /\ ds_lit_bufsize s1 = ds_lit_bufsize s /\ ds_pending_buf_size s1 = ds_pending_buf_size s
  /\ ds_w_size s1 = ds_w_size s /\ ds_strstart s1 = ds_strstart s /\ ds_block_start s1 = ds_block_start s
  /\ ds_insert s1 = ds_insert s /\ ds_matches s1 = ds_matches s /\ ds_high_water s1 = ds_high_water s
  /\ ds_window_size s1 = ds_window_size s /\ ds_wrap s1 = ds_wrap s /\ ds_hash_size s1 = ds_hash_size s.
Proof.
  intros s last Hbv Hbb s1. subst s1. rewrite (tr_stored_block_eq s None 0 last Hbv Hbb).
  pose proof (sb_hdr_eq' s Hbv) as E.
  unfold tsb_tail, upd4. cbn [negb Z.eqb]. dsred. repeat split; try reflexivity. lia.
Qed.

(* [comment removed for export] *)
Lemma sb_patch_facts : forall s len,
  let s1 := sb_patch s len in
  ds_pending s1 = ds_pending s /\ ds_bi_valid s1 = ds_bi_valid s /\ ds_bi_buf s1 = ds_bi_buf s
  /\ ds_pending_out s1 = ds_pending_out s /\ ds_strm s1 = ds_strm s /\ ds_window s1 = ds_window s
  /\ ds_lit_bufsize s1 = ds_lit_bufsize s /\ ds_pending_buf_size s1 = ds_pending_buf_size s
  /\ ds_w_size s1 = ds_w_size s /\ ds_strstart s1 = ds_strstart s /\ ds_block_start s1 = ds_block_start s
  /\ ds_insert s1 = ds_insert s /\ ds_matches s1 = ds_matches s /\ ds_high_water s1 = ds_high_water s
  /\ ds_window_size s1 = ds_window_size s /\ ds_wrap s1 = ds_wrap s /\ ds_hash_size s1 = ds_hash_size s.
Proof. intros s len s1. subst s1. unfold sb_patch. dsred. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma tr_flush_bits_0 : forall s, ds_bi_valid s = 0 -> tr_flush_bits s = s.
Proof.
  intros s H. unfold tr_flush_bits, bi_flush. rewrite H. reflexivity.
Qed.

Lemma fp_len_all : forall s, 0 <= ds_pending s <= cs_avail_out (ds_strm s) -> ds_pending s < 2 ^ 32 -> fp_len s = ds_pending s.
Proof.
  intros s H H2. unfold fp_len. rewrite wrap32_mod, Z.mod_small by lia.
  destruct (Z.ltb_spec (cs_avail_out (ds_strm s)) (ds_pending s)); lia.
Qed.

(* [comment removed for export] *)
Lemma fp_tail_facts : forall s len, len = ds_pending s ->
  let s1 := fp_tail s len in
  ds_pending s1 = 0 /\ ds_pending_out s1 = 0 /\ ds_bi_valid s1 = ds_bi_valid s /\ ds_bi_buf s1 = ds_bi_buf s
  /\ cs_avail_out (ds_strm s1) = cs_avail_out (ds_strm s) - len
  /\ cs_avail_in (ds_strm s1) = cs_avail_in (ds_strm s) /\ cs_next_in (ds_strm s1) = cs_next_in (ds_strm s)
  /\ cs_input (ds_strm s1) = cs_input (ds_strm s) /\ cs_total_in (ds_strm s1) = cs_total_in (ds_strm s)
  /\ cs_total_out (ds_strm s1) = wrap64 (cs_total_out (ds_strm s) + len) /\ cs_adler (ds_strm s1) = cs_adler (ds_strm s)
  /\ Z.of_nat (length (cs_out_rev (ds_strm s1))) = Z.of_nat (length (cs_out_rev (ds_strm s))) + Z.max 0 len
  /\ ds_window s1 = ds_window s
  /\ ds_lit_bufsize s1 = ds_lit_bufsize s /\ ds_pending_buf_size s1 = ds_pending_buf_size s
  /\ ds_w_size s1 = ds_w_size s /\ ds_strstart s1 = ds_strstart s /\ ds_block_start s1 = ds_block_start s
  /\ ds_insert s1 = ds_insert s /\ ds_matches s1 = ds_matches s /\ ds_high_water s1 = ds_high_water s
  /\ ds_window_size s1 = ds_window_size s /\ ds_wrap s1 = ds_wrap s /\ ds_hash_size s1 = ds_hash_size s.
Proof.
  intros s len Hl s1. subst s1. unfold fp_tail. rewrite <- Hl, Z.sub_diag. cbn [Z.eqb]. unfold cs_emit. dsred.
  repeat split; try reflexivity; try lia.
  rewrite List.rev_append_rev, List.length_app, List.length_rev. unfold arr_slice. rewrite arr_slice_nat_length. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lz_same (a b : deflate_state) : Prop :=
  ds_window b = ds_window a /\ ds_lit_bufsize b = ds_lit_bufsize a /\ ds_pending_buf_size b = ds_pending_buf_size a
  /\ ds_w_size b = ds_w_size a /\ ds_strstart b = ds_strstart a /\ ds_block_start b = ds_block_start a
  /\ ds_insert b = ds_insert a /\ ds_matches b = ds_matches a /\ ds_high_water b = ds_high_water a
  /\ ds_window_size b = ds_window_size a /\ ds_wrap b = ds_wrap a /\ ds_hash_size b = ds_hash_size a.

Definition in_same (a b : cstrm) : Prop :=
  cs_avail_in b = cs_avail_in a /\ cs_next_in b = cs_next_in a /\ cs_input b = cs_input a
  /\ cs_total_in b = cs_total_in a /\ cs_adler b = cs_adler a.

Lemma in_same_refl : forall a, in_same a a.
Proof. intros a. repeat split; reflexivity. Qed.

Lemma lz_same_trans : forall a b c, lz_same a b -> lz_same b c -> lz_same a c.
Proof.
  intros a b c (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
  unfold lz_same. rewrite B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12. repeat split; assumption.
Qed.

Lemma so_inv_transport : forall a b, so_inv a -> lz_same a b -> in_same (ds_strm a) (ds_strm b) ->
  0 <= cs_total_out (ds_strm b) < 2 ^ 64 -> 0 <= ds_bi_valid b <= 16 -> so_inv b.
Proof.
  intros a b HV (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) (B1 & B2 & B3 & B4 & B5) Hto Hbv.
  destruct HV. constructor; rewrite ?A1, ?A2, ?A3, ?A4, ?A5, ?A6, ?A7, ?A8, ?A9, ?A10, ?A11, ?A12, ?B1, ?B2, ?B3, ?B4, ?B5; try assumption.
Qed.

Lemma tsb_none_same : forall s last, 0 <= ds_bi_valid s <= 16 -> 0 <= ds_bi_buf s < 2 ^ 16 ->
  lz_same s (tr_stored_block s None 0 last) /\ ds_strm (tr_stored_block s None 0 last) = ds_strm s.
Proof.
  intros s last Hbv Hbb. pose proof (tsb_none_facts s last Hbv Hbb) as F. cbv zeta in F.
  destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17).
  split; [| exact F5]. unfold lz_same. repeat split; assumption.
Qed.

Lemma sb_patch_same : forall s len, lz_same s (sb_patch s len) /\ ds_strm (sb_patch s len) = ds_strm s.
Proof. intros s len. unfold lz_same, sb_patch. dsred. repeat split; reflexivity. Qed.

Lemma fp_tail_same : forall s len, lz_same s (fp_tail s len) /\ in_same (ds_strm s) (ds_strm (fp_tail s len)).
Proof. intros s len. unfold lz_same, in_same, fp_tail. destruct (_ =? 0); dsred; repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma st_emit1_eq' : forall s flush,
  st_emit1 s flush
  = (let X3 := tr_flush_bits (sb_patch (tr_stored_block s None 0 (sb_lastv s flush)) (sb_len s)) in
     if fp_len X3 =? 0 then X3 else fp_tail X3 (fp_len X3)).
Proof. intros. unfold st_emit1. rewrite flush_pending_eq. reflexivity. Qed.

Lemma emit1_facts : forall s flush, TI s -> sb_hdr s <= cs_avail_out (ds_strm s) ->
  let s4 := st_emit1 s flush in
  lz_same s s4 /\ in_same (ds_strm s) (ds_strm s4)
  /\ ds_pending s4 = 0 /\ ds_pending_out s4 = 0 /\ ds_bi_valid s4 = 0 /\ ds_bi_buf s4 = 0
  /\ cs_avail_out (ds_strm s4) = cs_avail_out (ds_strm s) - sb_hdr s
  /\ 0 <= cs_total_out (ds_strm s4) < 2 ^ 64
  /\ Z.of_nat (length (cs_out_rev (ds_strm s4))) = Z.of_nat (length (cs_out_rev (ds_strm s))) + sb_hdr s
  /\ 5 <= sb_hdr s <= 7.
Proof.
  intros s flush [HV Hp Hpo Hbb Hpbs Hao] Hh s4. subst s4. rewrite st_emit1_eq'. cbv zeta.
  pose proof (vi_bv _ HV) as Hbv. pose proof (sb_hdr_eq s Hbv) as [Eh Hhr]. rewrite <- Eh in Hhr.
  pose proof (tsb_none_facts s (sb_lastv s flush) Hbv Hbb) as F. cbv zeta in F.
  destruct F as (F1 & F2 & F3 & F4 & F5 & _).
  pose proof (tsb_none_same s (sb_lastv s flush) Hbv Hbb) as [S1 _].
  revert F1 F2 F3 F4 F5 S1. generalize (tr_stored_block s None 0 (sb_lastv s flush)). intros X1 F1 F2 F3 F4 F5 S1.
  pose proof (sb_patch_facts X1 (sb_len s)) as G. cbv zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & _).
  pose proof (sb_patch_same X1 (sb_len s)) as [S2 _].
  revert G1 G2 G3 G4 G5 S2. generalize (sb_patch X1 (sb_len s)). intros X2 G1 G2 G3 G4 G5 S2.
  rewrite (tr_flush_bits_0 X2) by (rewrite G2; exact F2).
  assert (EP : ds_pending X2 = sb_hdr s) by (rewrite G1, F1, Hp; lia).
  rewrite (fp_len_all X2) by (rewrite ?EP, ?G5, ?F5; lia).
  replace (ds_pending X2 =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite EP; lia).
  pose proof (fp_tail_facts X2 (ds_pending X2) eq_refl) as K. cbv zeta in K.
  destruct K as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & _).
  pose proof (fp_tail_same X2 (ds_pending X2)) as [S3 S3'].
  split; [exact (lz_same_trans _ _ _ (lz_same_trans _ _ _ S1 S2) S3)|].
  split; [rewrite <- F5, <- G5; exact S3'|].
  split; [exact K1|]. split; [exact K2|]. split; [rewrite K3, G2; exact F2|]. split; [rewrite K4, G3; exact F3|].
  split; [rewrite K5, G5, F5, EP; reflexivity|].
  split; [rewrite K10; apply wrap64_range|].
  split; [rewrite K12, G5, F5, EP; lia | exact Hhr].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lcopy_facts : forall s len, 0 <= len ->
  let s5 := st_lcopy s len in
  in_same (ds_strm s) (ds_strm s5)
  /\ ds_pending s5 = ds_pending s /\ ds_pending_out s5 = ds_pending_out s /\ ds_bi_valid s5 = ds_bi_valid s /\ ds_bi_buf s5 = ds_bi_buf s
  /\ cs_avail_out (ds_strm s5) = cs_avail_out (ds_strm s) - len
  /\ 0 <= cs_total_out (ds_strm s5) < 2 ^ 64
  /\ Z.of_nat (length (cs_out_rev (ds_strm s5))) = Z.of_nat (length (cs_out_rev (ds_strm s))) + len
  /\ ds_block_start s5 = ds_block_start s + len
  /\ ds_window s5 = ds_window s /\ ds_lit_bufsize s5 = ds_lit_bufsize s /\ ds_pending_buf_size s5 = ds_pending_buf_size s
  /\ ds_w_size s5 = ds_w_size s /\ ds_strstart s5 = ds_strstart s
  /\ ds_insert s5 = ds_insert s /\ ds_matches s5 = ds_matches s /\ ds_high_water s5 = ds_high_water s
  /\ ds_window_size s5 = ds_window_size s /\ ds_wrap s5 = ds_wrap s /\ ds_hash_size s5 = ds_hash_size s.
Proof.
  intros s len Hlen s5. subst s5. unfold st_lcopy, in_same, cs_emit. dsred.
  repeat split; try reflexivity; try lia; try apply wrap64_range.
  rewrite List.rev_append_rev, List.length_app, List.length_rev. unfold arr_slice. rewrite arr_slice_nat_length. lia.
Qed.

Lemma lcopy_so_inv : forall s len, so_inv s -> 0 <= len -> ds_block_start s + len <= ds_strstart s -> so_inv (st_lcopy s len).
Proof.
  intros s len HV Hlen Hbs. destruct HV. unfold st_lcopy, cs_emit. constructor; dsred; try assumption; try lia.
  apply wrap64_range.
Qed.

Lemma rdo_facts : forall s n, 0 < n <= cs_avail_in (ds_strm s) ->
  let s6 := st_rdo s n in
  lz_same s s6
  /\ ds_pending s6 = ds_pending s /\ ds_pending_out s6 = ds_pending_out s /\ ds_bi_valid s6 = ds_bi_valid s /\ ds_bi_buf s6 = ds_bi_buf s
  /\ cs_avail_out (ds_strm s6) = cs_avail_out (ds_strm s) - n
  /\ cs_avail_in (ds_strm s6) = cs_avail_in (ds_strm s) - n /\ cs_next_in (ds_strm s6) = cs_next_in (ds_strm s) + n
  /\ cs_input (ds_strm s6) = cs_input (ds_strm s)
  /\ 0 <= cs_total_in (ds_strm s6) < 2 ^ 64 /\ 0 <= cs_total_out (ds_strm s6) < 2 ^ 64
  /\ Z.of_nat (length (cs_out_rev (ds_strm s6))) = Z.of_nat (length (cs_out_rev (ds_strm s))) + n
  /\ cs_adler (ds_strm s6) = (if ds_wrap s =? 1 then adler32_upd (cs_adler (ds_strm s)) (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n)
                             else if ds_wrap s =? 2 then crc32_upd (cs_adler (ds_strm s)) (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n)
                             else cs_adler (ds_strm s)).
Proof.
  intros s n Hn s6. subst s6. rewrite (st_rdo_eq s n Hn). unfold st_rbfin, rb_mid, lz_same, cs_emit. cbv zeta.
  destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; dsred;
    (repeat split; try reflexivity; try lia; try apply wrap64_range;
     rewrite List.rev_append_rev, List.length_app, List.length_rev; unfold arr_slice; rewrite arr_slice_nat_length; lia).
Qed.

Lemma adler_range_upd : forall s n,
  so_inv s -> 0 < n <= cs_avail_in (ds_strm s) ->
  1 <= ds_wrap s ->
  0 <= (if ds_wrap s =? 1 then adler32_upd (cs_adler (ds_strm s)) (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n)
        else if ds_wrap s =? 2 then crc32_upd (cs_adler (ds_strm s)) (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n)
        else cs_adler (ds_strm s)) < 2 ^ 64.
Proof.
  intros s n HV Hn Hw. pose proof (vi_ib _ HV) as Vib. pose proof (vi_ni _ HV) as Vni. pose proof (vi_inlen _ HV) as Vinlen.
  assert (Hb : forall b, In b (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n) -> 0 <= b < 256).
  { intros b Hb. eapply arr_slice_In; [| exact Hb]. intros i Hi. apply Vib. lia. }
  destruct (Z.eqb_spec (ds_wrap s) 1); [apply adler32_upd_range; exact Hb|].
  destruct (Z.eqb_spec (ds_wrap s) 2); [pose proof (crc32_upd_range (cs_adler (ds_strm s)) _ Hb); lia|].
  apply (vi_ad _ HV). exact Hw.
Qed.

Lemma rdo_so_inv : forall s n, so_inv s -> 0 < n <= cs_avail_in (ds_strm s) -> so_inv (st_rdo s n).
Proof.
  intros s n HV Hn. pose proof (rdo_facts s n Hn) as F. cbv zeta in F.
  destruct F as (S1 & _ & _ & F3 & _ & _ & F6 & F7 & F8 & F9 & F10 & _ & F12).
  pose proof (adler_range_upd s n HV Hn) as Had. rewrite <- F12 in Had.
  destruct S1 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  pose proof HV as HV'. destruct HV.
  constructor; rewrite ?A1, ?A2, ?A3, ?A4, ?A5, ?A6, ?A7, ?A8, ?A9, ?A10, ?A11, ?A12, ?F3, ?F6, ?F7, ?F8; try assumption; try lia.
Qed.

Lemma st_rdo_0' : forall s, st_rdo s 0 = s.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sb_left_eq : forall s, so_inv s -> ds_w_size s <= 32768 -> sb_left s = ds_strstart s - ds_block_start s.
Proof.
  intros s HV Hws. pose proof (vi_str _ HV). pose proof (vi_bs _ HV).
  unfold sb_left. rewrite wrap32_mod. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma copy_facts : forall s4 left len, so_inv s4 -> 0 <= left -> left = ds_strstart s4 - ds_block_start s4 -> 0 <= len ->
  let s5 := fst (st_copy s4 left len) in
  let n2 := snd (st_copy s4 left len) in
  so_inv s5 /\ in_same (ds_strm s4) (ds_strm s5)
  /\ ds_pending s5 = ds_pending s4 /\ ds_pending_out s5 = ds_pending_out s4 /\ ds_bi_valid s5 = ds_bi_valid s4 /\ ds_bi_buf s5 = ds_bi_buf s4
  /\ cs_avail_out (ds_strm s5) = cs_avail_out (ds_strm s4) - (len - n2)
  /\ Z.of_nat (length (cs_out_rev (ds_strm s5))) = Z.of_nat (length (cs_out_rev (ds_strm s4))) + (len - n2)
  /\ 0 <= n2 <= len /\ (left = 0 -> n2 = len) /\ (left <> 0 -> n2 = len - lc_len left len /\ (n2 <> 0 -> n2 = len - left))
  /\ ds_block_start s4 <= ds_block_start s5 <= ds_strstart s5
  /\ ds_window s5 = ds_window s4 /\ ds_lit_bufsize s5 = ds_lit_bufsize s4 /\ ds_pending_buf_size s5 = ds_pending_buf_size s4
  /\ ds_w_size s5 = ds_w_size s4 /\ ds_strstart s5 = ds_strstart s4
  /\ ds_insert s5 = ds_insert s4 /\ ds_matches s5 = ds_matches s4 /\ ds_high_water s5 = ds_high_water s4
  /\ ds_window_size s5 = ds_window_size s4 /\ ds_wrap s5 = ds_wrap s4 /\ ds_hash_size s5 = ds_hash_size s4.
Proof.
  intros s4 left len HV Hl0 Hleft Hlen s5 n2. subst s5 n2. unfold st_copy.
  pose proof (vi_bs _ HV) as Vbs.
  destruct (Z.eqb_spec left 0) as [Hz|Hnz]; cbn [negb fst snd].
  - split; [exact HV|]. split; [apply in_same_refl|]. repeat split; try reflexivity; try lia.
  - assert (Hlc : 0 <= lc_len left len <= len /\ lc_len left len <= left /\ (len - lc_len left len <> 0 -> lc_len left len = left)).
    { unfold lc_len. destruct (Z.ltb_spec len left); lia. }
    pose proof (lcopy_facts s4 (lc_len left len) ltac:(lia)) as F. cbv zeta in F.
    destruct F as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19).
    split; [apply lcopy_so_inv; [exact HV | lia | lia]|].
    split; [exact F0|].
    rewrite F1, F2, F3, F4, F5, F7, F8, F13. repeat split; try reflexivity; try assumption; try lia.
Qed.

(* [comment removed for export] *)
Lemma trip_facts : forall s flush, TI s -> ds_w_size s <= 32768 -> sb_hdr s <= cs_avail_out (ds_strm s) ->
  let s' := st_trip s flush in
  TI s' /\ lz_same s (set_block_start s' (ds_block_start s))
  /\ ds_block_start s <= ds_block_start s' <= ds_strstart s'
  /\ cs_input (ds_strm s') = cs_input (ds_strm s)
  /\ cs_avail_in (ds_strm s') + cs_next_in (ds_strm s') = cs_avail_in (ds_strm s) + cs_next_in (ds_strm s)
  /\ 0 <= cs_avail_in (ds_strm s') <= cs_avail_in (ds_strm s)
  /\ 0 <= cs_avail_out (ds_strm s') <= cs_avail_out (ds_strm s) - 5
  /\ Z.of_nat (length (cs_out_rev (ds_strm s'))) + cs_avail_out (ds_strm s')
     = Z.of_nat (length (cs_out_rev (ds_strm s))) + cs_avail_out (ds_strm s)
  /\ ds_bi_valid s' = 0.
Proof.
  intros s flush HT Hws Hh s'. pose proof HT as [HV Hp Hpo Hbb Hpbs Hao].
  pose proof (vi_ai _ HV) as Vai. pose proof (vi_bs _ HV) as Vbs. pose proof (vi_str _ HV) as Vstr.
  pose proof (sb_left_eq s HV Hws) as Eleft. pose proof (sb_left_range s) as Hleft.
  pose proof (sb_len_range s ltac:(lia) Hh) as (Hlen & Hlen2 & Hlen3).
  pose proof (sb_len1_eq s ltac:(lia)) as (_ & _ & Hlen1).
  pose proof (emit1_facts s flush HT Hh) as E. cbv zeta in E.
  destruct E as (S4 & I4 & P4 & PO4 & BV4 & BB4 & AO4 & TO4 & OL4 & Hhr).
  subst s'. unfold st_trip. cbv zeta.
  revert S4 I4 P4 PO4 BV4 BB4 AO4 TO4 OL4. generalize (st_emit1 s flush). intros s4 S4 I4 P4 PO4 BV4 BB4 AO4 TO4 OL4.
  pose proof S4 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  pose proof I4 as (B1 & B2 & B3 & B4 & B5).
  assert (HV4 : so_inv s4) by (apply (so_inv_transport s s4 HV S4 I4 TO4); rewrite BV4; lia).
  pose proof (copy_facts s4 (sb_left s) (sb_len s) HV4 ltac:(lia) ltac:(rewrite A5, A6; exact Eleft) ltac:(lia)) as C. cbv zeta in C.
  revert C. generalize (snd (st_copy s4 (sb_left s) (sb_len s))) as n2. generalize (fst (st_copy s4 (sb_left s) (sb_len s))) as s5.
  intros s5 n2 (HV5 & I5 & P5 & PO5 & BV5 & BB5 & AO5 & OL5 & Hn2 & Hz & Hnz & Hbs5 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
  pose proof I5 as (D1 & D2 & D3 & D4 & D5).
  assert (Hn2ai : n2 <= cs_avail_in (ds_strm s5)).
  { rewrite D1, B1. destruct (Z.eq_dec (sb_left s) 0) as [Hl|Hl]; [rewrite (Hz Hl); lia|].
    destruct (Hnz Hl) as [E1 E2]. destruct (Z.eq_dec n2 0); [lia|]. pose proof (E2 ltac:(assumption)). lia. }
  destruct (Z.eq_dec n2 0) as [En|En].
  - rewrite En, st_rdo_0'.
    split. { constructor; [exact HV5 | rewrite P5; exact P4 | rewrite PO5; exact PO4 | rewrite BB5, BB4; lia | rewrite C3, C2, A2, A3; exact Hpbs | rewrite AO5, AO4; lia]. }
    split. { unfold lz_same. dsred. rewrite C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, A1, A2, A3, A4, A5, A7, A8, A9, A10, A11, A12. repeat split; reflexivity. }
    split; [lia|].
    split; [rewrite D3, B3; reflexivity|]. split; [rewrite D1, D2, B1, B2; reflexivity|]. split; [rewrite D1, B1; lia|].
    split; [rewrite AO5, AO4; lia|]. split; [rewrite OL5, AO5, OL4, AO4; lia | rewrite BV5; exact BV4].
  - pose proof (rdo_facts s5 n2 ltac:(lia)) as R. cbv zeta in R.
    destruct R as (S6 & P6 & PO6 & BV6 & BB6 & AO6 & AI6 & NI6 & IN6 & TI6 & TO6 & OL6 & AD6).
    pose proof (rdo_so_inv s5 n2 HV5 ltac:(lia)) as HV6.
    revert S6 P6 PO6 BV6 BB6 AO6 AI6 NI6 IN6 TI6 TO6 OL6 AD6 HV6. generalize (st_rdo s5 n2). intros s6 S6 P6 PO6 BV6 BB6 AO6 AI6 NI6 IN6 TI6 TO6 OL6 AD6 HV6.
    pose proof S6 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
    split. { constructor; [exact HV6 | rewrite P6, P5; exact P4 | rewrite PO6, PO5; exact PO4 | rewrite BB6, BB5, BB4; lia | rewrite G3, G2, C3, C2, A2, A3; exact Hpbs | rewrite AO6, AO5, AO4; lia]. }
    split. { unfold lz_same. dsred. rewrite G1, G2, G3, G4, G5, G7, G8, G9, G10, G11, G12, C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, A1, A2, A3, A4, A5, A7, A8, A9, A10, A11, A12. repeat split; reflexivity. }
    split; [lia|].
    split; [rewrite IN6, D3, B3; reflexivity|]. split; [rewrite AI6, NI6, D1, D2, B1, B2; lia|]. split; [rewrite AI6, D1, B1; lia|].
    split; [rewrite AO6, AO5, AO4; lia|]. split; [rewrite OL6, AO6, OL5, AO5, OL4, AO4; lia | rewrite BV6, BV5; exact BV4].
Qed.

Lemma so_trip_ok_TI : forall s flush mb, TI s -> ds_w_size s <= 32768 -> so_trip_ok s flush mb.
Proof.
  intros s flush mb HT Hws. pose proof HT as [HV Hp Hpo Hbb Hpbs Hao].
  pose proof (vi_ai _ HV) as Vai. pose proof (vi_bs _ HV) as Vbs. pose proof (vi_str _ HV) as Vstr. pose proof (vi_bv _ HV) as Vbv.
  pose proof (vi_pbs _ HV) as Vpbs. pose proof (vi_to _ HV) as Vto.
  split; [exact HV|]. intros Hb.
  assert (Hh : sb_hdr s <= cs_avail_out (ds_strm s)).
  { unfold sb_broke in Hb. apply Bool.orb_false_elim in Hb. destruct Hb as [Hb _]. apply Z.ltb_ge in Hb. exact Hb. }
  pose proof (sb_left_eq s HV Hws) as Eleft. pose proof (sb_left_range s) as Hleft.
  pose proof (sb_len_range s ltac:(lia) Hh) as (Hlen & Hlen2 & Hlen3).
  pose proof (sb_len1_eq s ltac:(lia)) as (_ & _ & Hlen1).
  pose proof (sb_hdr_eq s Vbv) as [Eh Hhr]. rewrite <- Eh in Hhr.
  split.
  { (* [comment removed for export] *)
    unfold so_emit_ok, so_fp_ok. cbv zeta.
    pose proof (tsb_none_facts s (sb_lastv s flush) Vbv Hbb) as F. cbv zeta in F. destruct F as (F1 & F2 & F3 & F4 & F5 & _).
    revert F1 F2 F3 F4 F5. generalize (tr_stored_block s None 0 (sb_lastv s flush)). intros X1 F1 F2 F3 F4 F5.
    pose proof (sb_patch_facts X1 (sb_len s)) as G. cbv zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & _).
    revert G1 G2 G3 G4 G5. generalize (sb_patch X1 (sb_len s)). intros X2 G1 G2 G3 G4 G5.
    rewrite (tr_flush_bits_0 X2) by (rewrite G2; exact F2).
    assert (EP : ds_pending X2 = sb_hdr s) by (rewrite G1, F1, Hp; lia).
    pose proof (fp_len_eq X2 ltac:(rewrite EP; lia) ltac:(rewrite G5, F5; lia)) as (_ & Hfl & _).
    unfold BINV. rewrite ?EP, ?G2, ?G3, ?G4, ?G5, ?F1, ?F2, ?F3, ?F4, ?F5, ?Hpo, ?Hp. repeat split; lia. }
  pose proof (emit1_facts s flush HT Hh) as E. cbv zeta in E.
  destruct E as (S4 & I4 & P4 & PO4 & BV4 & BB4 & AO4 & TO4 & OL4 & _).
  unfold so_copy_ok, so_rdo_ok, st_trip. cbv zeta.
  revert S4 I4 P4 PO4 BV4 BB4 AO4 TO4 OL4. generalize (st_emit1 s flush). intros s4 S4 I4 P4 PO4 BV4 BB4 AO4 TO4 OL4.
  pose proof S4 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  pose proof I4 as (B1 & B2 & B3 & B4 & B5).
  assert (HV4 : so_inv s4) by (apply (so_inv_transport s s4 HV S4 I4 TO4); rewrite BV4; lia).
  split.
  { intros Hl0. assert (Hlc : 0 <= lc_len (sb_left s) (sb_len s) <= sb_len s /\ lc_len (sb_left s) (sb_len s) <= sb_left s).
    { unfold lc_len. destruct (Z.ltb_spec (sb_len s) (sb_left s)); lia. }
    rewrite A6, A4, AO4. repeat split; lia. }
  pose proof (copy_facts s4 (sb_left s) (sb_len s) HV4 ltac:(lia) ltac:(rewrite A5, A6; exact Eleft) ltac:(lia)) as C. cbv zeta in C.
  revert C. generalize (snd (st_copy s4 (sb_left s) (sb_len s))) as n2. generalize (fst (st_copy s4 (sb_left s) (sb_len s))) as s5.
  intros s5 n2 (HV5 & I5 & P5 & PO5 & BV5 & BB5 & AO5 & OL5 & Hn2 & Hz & Hnz & Hbs5 & _).
  pose proof I5 as (D1 & D2 & D3 & D4 & D5).
  assert (Hn2ai : n2 <= cs_avail_in (ds_strm s5)).
  { rewrite D1, B1. destruct (Z.eq_dec (sb_left s) 0) as [Hl|Hl]; [rewrite (Hz Hl); lia|].
    destruct (Hnz Hl) as [E1 E2]. destruct (Z.eq_dec n2 0); [lia|]. pose proof (E2 ltac:(assumption)). lia. }
  split. { split; [exact HV5|]. intros En. rewrite AO5, AO4. lia. }
  destruct (Z.eq_dec n2 0) as [En|En]; [rewrite En, st_rdo_0'; exact HV5|].
  apply rdo_so_inv; [exact HV5 | lia].
Qed.

(* [comment removed for export] *)
Lemma loop_TI : forall fuel s flush mb, TI s -> ds_w_size s <= 32768 -> cs_avail_out (ds_strm s) + 1 <= Z.of_nat fuel ->
  so_loop_ok fuel s flush mb
  /\ let sL := fst (deflate_stored_loop fuel s flush mb) in
     let last := snd (deflate_stored_loop fuel s flush mb) in
     TI sL /\ lz_same s (set_block_start sL (ds_block_start s))
     /\ ds_block_start s <= ds_block_start sL <= ds_strstart sL
     /\ cs_input (ds_strm sL) = cs_input (ds_strm s)
     /\ cs_avail_in (ds_strm sL) + cs_next_in (ds_strm sL) = cs_avail_in (ds_strm s) + cs_next_in (ds_strm s)
     /\ 0 <= cs_avail_in (ds_strm sL) <= cs_avail_in (ds_strm s)
     /\ 0 <= cs_avail_out (ds_strm sL) <= cs_avail_out (ds_strm s)
     /\ Z.of_nat (length (cs_out_rev (ds_strm sL))) + cs_avail_out (ds_strm sL)
        = Z.of_nat (length (cs_out_rev (ds_strm s))) + cs_avail_out (ds_strm s)
     /\ 0 <= last <= 1 /\ (0 <= ds_bi_valid sL <= 16).
Proof.
  induction fuel as [|f IH]; intros s flush mb HT Hws Hfuel.
  { pose proof (se_ao _ HT). lia. }
  pose proof HT as [HV Hp Hpo Hbb Hpbs Hao]. pose proof (vi_ai _ HV) as Vai. pose proof (vi_bs _ HV) as Vbs. pose proof (vi_bv _ HV) as Vbv.
  assert (BASE : TI s /\ lz_same s (set_block_start s (ds_block_start s)) /\ ds_block_start s <= ds_block_start s <= ds_strstart s
                 /\ cs_input (ds_strm s) = cs_input (ds_strm s)
                 /\ cs_avail_in (ds_strm s) + cs_next_in (ds_strm s) = cs_avail_in (ds_strm s) + cs_next_in (ds_strm s)
                 /\ 0 <= cs_avail_in (ds_strm s) <= cs_avail_in (ds_strm s)
                 /\ 0 <= cs_avail_out (ds_strm s) <= cs_avail_out (ds_strm s)
                 /\ Z.of_nat (length (cs_out_rev (ds_strm s))) + cs_avail_out (ds_strm s) = Z.of_nat (length (cs_out_rev (ds_strm s))) + cs_avail_out (ds_strm s)).
  { split; [exact HT|]. split; [unfold lz_same; dsred; repeat split; reflexivity|]. repeat split; lia. }
  rewrite so_loop_ok_S, sloop_S'. cbv zeta.
  split.
  { split; [apply so_trip_ok_TI; assumption|]. intros Hb Hl.
    assert (Hh : sb_hdr s <= cs_avail_out (ds_strm s)).
    { unfold sb_broke in Hb. apply Bool.orb_false_elim in Hb. destruct Hb as [Hb _]. apply Z.ltb_ge in Hb. exact Hb. }
    pose proof (trip_facts s flush HT Hws Hh) as T. cbv zeta in T. destruct T as (HT' & S' & _ & _ & _ & _ & AO' & _).
    pose proof S' as (_ & _ & _ & W' & _). dsred in W'.
    apply (proj1 (IH _ flush mb HT' ltac:(rewrite W'; exact Hws) ltac:(lia))). }
  destruct (sb_broke s flush mb) eqn:Hb.
  { cbn [fst snd]. destruct BASE as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8). repeat (split; [assumption|]). split; lia. }
  assert (Hh : sb_hdr s <= cs_avail_out (ds_strm s)).
  { unfold sb_broke in Hb. apply Bool.orb_false_elim in Hb. destruct Hb as [Hb' _]. apply Z.ltb_ge in Hb'. exact Hb'. }
  pose proof (trip_facts s flush HT Hws Hh) as T. cbv zeta in T. destruct T as (HT' & S' & BS' & IN' & AN' & AI' & AO' & OL' & BV').
  pose proof (sb_lastv_range s flush) as Hlr.
  destruct (Z.eqb_spec (sb_lastv s flush) 0) as [Hl|Hl].
  2: { cbn [fst snd]. split; [exact HT'|]. split; [exact S'|]. repeat (split; [first [assumption | lia]|]). lia. }
  pose proof S' as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12). dsred in W4. dsred in W5.
  destruct (IH (st_trip s flush) flush mb HT' ltac:(rewrite W4; exact Hws) ltac:(lia)) as [_ R]. cbv zeta in R.
  destruct R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
  split; [exact R1|].
  split. { revert S' R2. generalize (fst (deflate_stored_loop f (st_trip s flush) flush mb)). generalize (st_trip s flush).
           intros a b Sa Sb. unfold lz_same in Sa, Sb |- *. dsred in Sa. dsred in Sb. dsred.
           destruct Sa as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
           destruct Sb as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12).
           rewrite Q1, Q2, Q3, Q4, Q5, Q7, Q8, Q9, Q10, Q11, Q12. repeat split; first [assumption | reflexivity]. }
  split; [lia|]. split; [rewrite R4; exact IN'|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. exact (conj R9 R10).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma slice_input_bytes : forall s ofs n, so_inv s -> 0 <= ofs -> ofs + n <= arr_len (cs_input (ds_strm s)) ->
  forall b, In b (arr_slice (cs_input (ds_strm s)) ofs n) -> 0 <= b < 256.
Proof. intros s ofs n HV Ho Hn b Hb. eapply arr_slice_In; [| exact Hb]. intros i Hi. apply (vi_ib _ HV). lia. Qed.

Lemma slice_window_bytes : forall s ofs n, so_inv s -> 0 <= ofs -> ofs + n <= 2 * ds_w_size s ->
  forall b, In b (arr_slice (ds_window s) ofs n) -> 0 <= b < 256.
Proof. intros s ofs n HV Ho Hn b Hb. eapply arr_slice_In; [| exact Hb]. intros i Hi. apply (vi_wb _ HV). lia. Qed.

(* [comment removed for export] *)
Definition bits_same (a b : deflate_state) : Prop :=
  ds_pending b = ds_pending a /\ ds_pending_out b = ds_pending_out a /\ ds_bi_valid b = ds_bi_valid a /\ ds_bi_buf b = ds_bi_buf a
  /\ ds_lit_bufsize b = ds_lit_bufsize a /\ ds_pending_buf_size b = ds_pending_buf_size a /\ ds_w_size b = ds_w_size a
  /\ cs_avail_out (ds_strm b) = cs_avail_out (ds_strm a) /\ cs_total_out (ds_strm b) = cs_total_out (ds_strm a)
  /\ cs_out_rev (ds_strm b) = cs_out_rev (ds_strm a) /\ cs_input (ds_strm b) = cs_input (ds_strm a).

Lemma hw_st_so_inv : forall s, so_inv s -> ds_w_size s <= 32768 ->
  so_inv (hw_st s) /\ bits_same s (hw_st s) /\ ds_strm (hw_st s) = ds_strm s
  /\ ds_strstart (hw_st s) = ds_strstart s /\ ds_block_start (hw_st s) = ds_block_start s /\ ds_window_size (hw_st s) = ds_window_size s
  /\ ds_w_size (hw_st s) = ds_w_size s.
Proof.
  intros s HV Hws. pose proof (vi_str _ HV). pose proof (vi_bs _ HV). unfold hw_st, bits_same.
  destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s)); [| split; [exact HV|]; repeat split; reflexivity].
  split; [| dsred; repeat split; reflexivity].
  destruct HV; constructor; dsred; try assumption. lia.
Qed.

(* [comment removed for export] *)
Lemma wupd_so_inv : forall s used, so_inv s -> ds_w_size s <= 32768 -> 0 <= used <= cs_next_in (ds_strm s) ->
  so_inv (st_wupd s used) /\ bits_same s (st_wupd s used) /\ ds_strm (st_wupd s used) = ds_strm s
  /\ ds_w_size (st_wupd s used) = ds_w_size s.
Proof.
  intros s used HV Hws Hu.
  pose proof (vi_str _ HV) as Vstr. pose proof (vi_bs _ HV) as Vbs. pose proof (vi_wsz _ HV) as Vwsz. pose proof (vi_ins _ HV) as Vins.
  pose proof (vi_mat _ HV) as Vmat. pose proof (vi_ni _ HV) as Vni. pose proof (vi_inlen _ HV) as Vinlen. pose proof (vi_ai _ HV) as Vai.
  unfold st_wupd, bits_same.
  destruct (Z.eqb_spec used 0) as [Hz|Hnz]; cbn [negb].
  { split; [exact HV|]. repeat split; reflexivity. }
  destruct (Z.leb_spec (ds_w_size s) used) as [Hsup|Hsup].
  - (* [comment removed for export] *)
    dsred. split; [| repeat split; reflexivity].
    pose proof (slice_input_bytes s (cs_next_in (ds_strm s) - ds_w_size s) (ds_w_size s) HV ltac:(lia) ltac:(lia)) as Hb.
    destruct HV; constructor; dsred; try assumption; try lia.
    intros j Hj. apply (arr_upd_bytes _ _ _ (2 * ds_w_size s)); [exact vi_wb | exact Hb | exact Hj].
  - cbv zeta. destruct (Z.leb_spec (ds_window_size s - ds_strstart s) used) as [Hsl|Hsl].
    + (* [comment removed for export] *)
      dsred.
      pose proof (slice_window_bytes s (ds_w_size s) (ds_strstart s - ds_w_size s) HV ltac:(lia) ltac:(lia)) as Hb1.
      pose proof (slice_input_bytes s (cs_next_in (ds_strm s) - used) used HV ltac:(lia) ltac:(lia)) as Hb2.
      destruct (Z.ltb_spec (ds_matches s) 2); dsred; destruct (Z.ltb_spec (ds_strstart s - ds_w_size s) (ds_insert s)); dsred;
        (split; [| repeat split; reflexivity]).
      all: pose proof (arr_blit_upd (ds_window s) 0 (ds_window s) (ds_w_size s) (ds_strstart s - ds_w_size s)) as EB.
      all: match goal with |- so_inv ?X =>
             lazymatch X with context [MIN ?u (wrap32 (?w - ?i))] =>
               pose proof (ins_add_eq i u w ltac:(lia) ltac:(lia) ltac:(lia)) as [_ Hia]; unfold ins_add in Hia end end.
      all: destruct HV; constructor; dsred; try assumption; try lia.
      all: intros j Hj; apply (arr_upd_bytes _ _ _ (2 * ds_w_size s)); [ | exact Hb2 | exact Hj];
           intros j' Hj'; rewrite EB; apply (arr_upd_bytes _ _ _ (2 * ds_w_size s)); [exact vi_wb | exact Hb1 | exact Hj'].
    + (* [comment removed for export] *)
      dsred. split; [| repeat split; reflexivity].
      pose proof (slice_input_bytes s (cs_next_in (ds_strm s) - used) used HV ltac:(lia) ltac:(lia)) as Hb2.
      pose proof (ins_add_eq (ds_insert s) used (ds_w_size s) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ Hia]. unfold ins_add in Hia.
      destruct HV; constructor; dsred; try assumption; try lia.
      intros j Hj. apply (arr_upd_bytes _ _ _ (2 * ds_w_size s)); [exact vi_wb | exact Hb2 | exact Hj].
Qed.

(* [comment removed for export] *)
Lemma slide3_so_inv : forall s have, so_inv s -> ds_w_size s <= 32768 -> have = 2 * ds_w_size s - ds_strstart s ->
  let s3 := fst (st_slide3 s have) in
  let have' := snd (st_slide3 s have) in
  so_inv s3 /\ bits_same s s3 /\ ds_strm s3 = ds_strm s /\ ds_w_size s3 = ds_w_size s
  /\ have' = 2 * ds_w_size s3 - ds_strstart s3 /\ 0 <= have'.
Proof.
  intros s have HV Hws Eh s3 have'. subst s3 have'.
  pose proof (vi_str _ HV) as Vstr. pose proof (vi_bs _ HV) as Vbs. pose proof (vi_ins _ HV) as Vins. pose proof (vi_mat _ HV) as Vmat.
  destruct ((have <? cs_avail_in (ds_strm s)) && (ds_w_size s <=? ds_block_start s)) eqn:Ec.
  - rewrite (st_slide3_true s have Ec). cbv zeta. cbn [fst snd].
    apply Bool.andb_true_iff in Ec. destruct Ec as [_ Ec]. apply Z.leb_le in Ec.
    pose proof (slice_window_bytes s (ds_w_size s) (ds_strstart s - ds_w_size s) HV ltac:(lia) ltac:(lia)) as Hb1.
    unfold sl_fix, bits_same. dsred.
    rewrite wrap32_mod, Z.mod_small by lia.
    destruct (Z.ltb_spec (ds_matches s) 2); dsred; destruct (Z.ltb_spec (ds_strstart s - ds_w_size s) (ds_insert s)); dsred;
      (split; [| repeat split; try reflexivity; lia]);
      (destruct HV; constructor; dsred; try assumption; try lia;
       intros j Hj; apply (arr_upd_bytes _ _ _ (2 * ds_w_size s)); [exact vi_wb | exact Hb1 | exact Hj]).
  - rewrite (st_slide3_false s have Ec). cbn [fst snd]. split; [exact HV|]. unfold bits_same. repeat split; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma rbw_mid_adler : forall s off n, so_inv s -> 0 < n <= cs_avail_in (ds_strm s) -> 1 <= ds_wrap s ->
  0 <= cs_adler (ds_strm (rbw_mid s off n)) < 2 ^ 64.
Proof.
  intros s off n HV Hn Hw. pose proof (adler_range_upd s n HV Hn Hw) as H.
  unfold rbw_mid. destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; dsred; exact H.
Qed.

Lemma fillw_so_inv : forall s n, so_inv s -> ds_w_size s <= 32768 -> 0 <= n <= cs_avail_in (ds_strm s) ->
  ds_strstart s + n <= 2 * ds_w_size s ->
  let s4 := st_fillw s n in
  so_inv s4 /\ bits_same s s4 /\ ds_w_size s4 = ds_w_size s.
Proof.
  intros s n HV Hws Hn Hroom s4. subst s4.
  destruct (Z.eq_dec n 0) as [Hz|Hnz].
  { subst n. rewrite st_fillw_0. split; [exact HV|]. unfold bits_same. repeat split; reflexivity. }
  rewrite (st_fillw_eq s s n eq_refl ltac:(lia)).
  pose proof (vi_str _ HV) as Vstr. pose proof (vi_bs _ HV) as Vbs. pose proof (vi_ins _ HV) as Vins.
  pose proof (vi_ni _ HV) as Vni. pose proof (vi_inlen _ HV) as Vinlen. pose proof (vi_wrap _ HV) as Vwr.
  pose proof (slice_input_bytes s (cs_next_in (ds_strm s)) n HV ltac:(lia) ltac:(lia)) as Hb.
  pose proof (ins_add_eq (ds_insert s) n (ds_w_size s) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ Hia].
  pose proof (rbw_mid_adler s (ds_strstart s) n HV ltac:(lia)) as Had.
  revert Had. unfold st_rbw, rbw_mid, bits_same.
  destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; dsred; intros Had;
    (split; [| repeat split; reflexivity]);
    (destruct HV; constructor; dsred; try assumption; try lia; try apply wrap64_range;
     intros j Hj; apply (arr_upd_bytes _ _ _ (2 * ds_w_size s)); [exact vi_wb | exact Hb | exact Hj]).
Qed.

(* [comment removed for export] *)
Lemma tsb_facts : forall s buf len last, 0 <= ds_bi_valid s <= 16 -> 0 <= ds_bi_buf s < 2 ^ 16 ->
  let s1 := tr_stored_block s buf len last in
  ds_pending s1 = ds_pending s + sb_hdr s + len /\ ds_bi_valid s1 = 0 /\ ds_bi_buf s1 = 0
  /\ ds_pending_out s1 = ds_pending_out s /\ ds_strm s1 = ds_strm s /\ ds_lit_bufsize s1 = ds_lit_bufsize s
  /\ ds_block_start s1 = ds_block_start s.
Proof.
  intros s buf len last Hbv Hbb s1. subst s1. rewrite (tr_stored_block_eq s buf len last Hbv Hbb).
  pose proof (sb_hdr_eq' s Hbv) as E.
  unfold tsb_tail, upd4. dsred. repeat split; try reflexivity. lia.
Qed.

(* [comment removed for export] *)
Lemma final_ok_intro : forall s flush, so_inv s -> ds_lit_bufsize s < 2 ^ 16 ->
  ds_pending s = 0 -> ds_pending_out s = 0 -> 0 <= ds_bi_buf s < 2 ^ 16 -> ds_pending_buf_size s = ds_lit_bufsize s * 4 ->
  0 <= cs_avail_out (ds_strm s) ->
  so_final_ok s flush.
Proof.
  intros s flush HV Hlbs Hp Hpo Hbb Hpbs Hao. unfold so_final_ok, so_fp_ok. cbv zeta. intros Hc.
  pose proof (vi_bv _ HV) as Vbv. pose proof (vi_pbs _ HV) as Vpbs. pose proof (vi_to _ HV) as Vto.
  pose proof (sb_hdr_eq s Vbv) as [Eh Hhr].
  destruct (t_have_eq s Vbv ltac:(lia)) as (Eth & Hth & _). rewrite <- Eh in Eth.
  assert (Hfl : 0 <= fin_len s <= t_have s).
  { unfold fin_len, MIN. pose proof (wrap32_range (ds_strstart s - ds_block_start s)). destruct (Z.ltb_spec (t_have s) (wrap32 (ds_strstart s - ds_block_start s))); lia. }
  assert (Hfl2 : sb_hdr s + fin_len s <= ds_pending_buf_size s).
  { rewrite Eth in Hfl. destruct (Z.ltb_spec (ds_pending_buf_size s - sb_hdr s) 65536); lia. }
  pose proof (tsb_facts s (Some (ds_block_start s)) (fin_len s) (fin_last s flush) Vbv Hbb) as F. cbv zeta in F.
  destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  revert F1 F2 F3 F4 F5 F6 F7. generalize (tr_stored_block s (Some (ds_block_start s)) (fin_len s) (fin_last s flush)). intros s5 F1 F2 F3 F4 F5 F6 F7.
  rewrite (tr_flush_bits_0 (set_block_start s5 (ds_block_start s5 + fin_len s))) by (dsred; exact F2).
  pose proof (fp_len_eq (set_block_start s5 (ds_block_start s5 + fin_len s)) ltac:(dsred; rewrite F1, Hp; lia) ltac:(dsred; rewrite F5; exact Hao)) as (_ & Hfle & _).
  revert Hfle. unfold BINV. dsred. intros Hfle. rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?Hp, ?Hpo in Hfle. rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?Hp, ?Hpo. rewrite Hpbs in Hfl2.
  repeat split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem stored_safe_intro : forall s flush, st_entry s -> DWF s -> stored_safe s flush.
Proof.
  intros s flush HE HWF. pose proof HE as [HV Hp Hpo Hbb Hpbs Hao].
  pose proof (wf_wsz _ HWF) as Wws. pose proof (wf_lbs _ HWF) as Wlbs.
  pose proof (vi_ni _ HV) as Vni. pose proof (vi_ai _ HV) as Vai.
  unfold stored_safe. cbv zeta. split; [exact HWF|].
  destruct (loop_TI (Z.to_nat (cs_avail_out (ds_strm s) + 1)) s flush (wrap32 (MIN (ds_pending_buf_size s - 5) (ds_w_size s))) HE ltac:(lia) ltac:(lia))
    as [HLO R]. cbv zeta in R.
  split; [exact HLO|].
  revert R. generalize (snd (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm s) + 1)) s flush (wrap32 (MIN (ds_pending_buf_size s - 5) (ds_w_size s))))) as last.
  generalize (fst (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm s) + 1)) s flush (wrap32 (MIN (ds_pending_buf_size s - 5) (ds_w_size s))))) as sL.
  intros sL last (HTL & SL & BSL & INL & ANL & AIL & AOL & OLL & Hlast & BVL).
  pose proof HTL as [HVL HpL HpoL HbbL HpbsL HaoL].
  pose proof SL as (W1 & W2 & W3 & W4 & _). dsred in W4.
  unfold so_tail_ok. cbv zeta.
  split; [lia|]. split; [exact HVL|]. split; [lia|].
  (* [comment removed for export] *)
  destruct (wupd_so_inv sL (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL)) HVL ltac:(rewrite W4; lia) ltac:(lia)) as (HV1 & B1 & ST1 & WS1).
  destruct (hw_st_so_inv (st_wupd sL (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL))) HV1 ltac:(rewrite WS1, W4; lia))
    as (HV2 & B2 & ST2 & STR2 & BS2 & WSZ2 & WS2).
  revert HV1 B1 ST1 WS1 HV2 B2 ST2 STR2 BS2 WSZ2 WS2.
  generalize (st_wupd sL (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL))). intros s1 HV1 B1 ST1 WS1.
  generalize (hw_st s1). intros s2 HV2 B2 ST2 STR2 BS2 WSZ2 WS2.
  split; [exact HV2|]. intros Hl0.
  pose proof (vi_str _ HV2) as Vstr2. pose proof (vi_bs _ HV2) as Vbs2. pose proof (vi_wsz _ HV2) as Vwsz2.
  assert (Hws2 : ds_w_size s2 <= 32768) by (rewrite WS2, WS1, W4; lia).
  assert (Ehave : wrap32 (ds_window_size s2 - ds_strstart s2) = 2 * ds_w_size s2 - ds_strstart s2).
  { rewrite Vwsz2, wrap32_mod. apply Z.mod_small. lia. }
  rewrite Ehave.
  (* [comment removed for export] *)
  destruct (slide3_so_inv s2 (2 * ds_w_size s2 - ds_strstart s2) HV2 Hws2 eq_refl) as (HV3 & B3 & ST3 & WS3 & Eh3 & Hh3).
  revert HV3 B3 ST3 WS3 Eh3 Hh3.
  generalize (snd (st_slide3 s2 (2 * ds_w_size s2 - ds_strstart s2))) as have'. generalize (fst (st_slide3 s2 (2 * ds_w_size s2 - ds_strstart s2))) as s3.
  intros s3 have' HV3 B3 ST3 WS3 Eh3 Hh3.
  split; [exact HV3|].
  pose proof (vi_ai _ HV3) as Vai3.
  assert (Hfm : 0 <= fmin have' (cs_avail_in (ds_strm s3)) <= have' /\ fmin have' (cs_avail_in (ds_strm s3)) <= cs_avail_in (ds_strm s3)).
  { unfold fmin. destruct (Z.ltb_spec (cs_avail_in (ds_strm s3)) have'); lia. }
  (* [comment removed for export] *)
  destruct (fillw_so_inv s3 (fmin have' (cs_avail_in (ds_strm s3))) HV3 ltac:(rewrite WS3; exact Hws2) ltac:(lia) ltac:(lia)) as (HV4 & B4 & WS4).
  destruct (hw_st_so_inv (st_fillw s3 (fmin have' (cs_avail_in (ds_strm s3)))) HV4 ltac:(rewrite WS4, WS3; exact Hws2))
    as (HV5 & B5 & ST5 & _).
  revert HV4 B4 WS4 HV5 B5 ST5.
  generalize (st_fillw s3 (fmin have' (cs_avail_in (ds_strm s3)))). intros s4 HV4 B4 WS4.
  generalize (hw_st s4). intros s5 HV5 B5 ST5.
  split; [exact HV5|].
  (* [comment removed for export] *)
  destruct B1 as (P1 & PO1 & BV1 & BB1 & LB1 & PBS1 & _ & AO1 & _).
  destruct B2 as (P2 & PO2 & BV2 & BB2 & LB2 & PBS2 & _ & AO2 & _).
  destruct B3 as (P3 & PO3 & BV3 & BB3 & LB3 & PBS3 & _ & AO3 & _).
  destruct B4 as (P4 & PO4 & BV4 & BB4 & LB4 & PBS4 & _ & AO4 & _).
  destruct B5 as (P5 & PO5 & BV5 & BB5 & LB5 & PBS5 & _ & AO5 & _).
  pose proof SL as (_ & LBL & PBSL & _).  dsred in LBL. dsred in PBSL.
  apply final_ok_intro; [exact HV5 | | | | | | ].
  - rewrite LB5, LB4, LB3, LB2, LB1, LBL. lia.
  - rewrite P5, P4, P3, P2, P1. exact HpL.
  - rewrite PO5, PO4, PO3, PO2, PO1. exact HpoL.
  - rewrite BB5, BB4, BB3, BB2, BB1. exact HbbL.
  - rewrite PBS5, PBS4, PBS3, PBS2, PBS1, LB5, LB4, LB3, LB2, LB1. exact HpbsL.
  - rewrite AO5, AO4, AO3, AO2, AO1. lia.
Qed.
