(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz FillWinModel FlushBlockModel DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM RefDeflFast1 RefDeflSafeFB RefDeflSafeLF BoundArith BoundTfb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition olen (s : deflate_state) : Z := Z.of_nat (length (cs_out_rev (ds_strm s))).
Definition Mc (s : deflate_state) : Z := olen s + Mloc s.

Lemma Mloc_tr_flush_bits : forall s, 0 <= ds_bi_valid s <= 16 -> Mloc (tr_flush_bits s) = Mloc s.
Proof.
  intros s H. unfold Mloc, tr_flush_bits, bi_flush, put_short, put_byte.
  destruct (Z.eqb_spec (ds_bi_valid s) 16) as [E|N]; dsred.
  - rewrite E. unfold cdiv8. change ((0 + 7) / 8) with 0. change ((16 + 7) / 8) with 2. lia.
  - destruct (Z.leb_spec 8 (ds_bi_valid s)); dsred; [| reflexivity].
    unfold cdiv8. Z.to_euclidean_division_equations. lia.
Qed.

Lemma olen_tr_flush_bits : forall s, olen (tr_flush_bits s) = olen s.
Proof.
  intros s. unfold olen. destruct (tr_flush_bits_cases s) as [E|[E|E]]; rewrite E; unfold put_byte; dsred; reflexivity.
Qed.

Lemma Mc_flush_pending : forall s, 0 <= ds_bi_valid s <= 16 -> 0 <= ds_pending (tr_flush_bits s) < 2 ^ 32 ->
  0 <= cs_avail_out (ds_strm (tr_flush_bits s)) -> Mc (flush_pending s) = Mc s.
Proof.
  intros s Hb Hp Ha. rewrite flush_pending_eq. cbv zeta.
  assert (E1 : Mc (tr_flush_bits s) = Mc s) by (unfold Mc; rewrite olen_tr_flush_bits, Mloc_tr_flush_bits by exact Hb; reflexivity).
  set (s1 := tr_flush_bits s) in *. clearbody s1.
  destruct (Z.eqb_spec (fp_len s1) 0) as [E0|N0]; [exact E1|].
  rewrite <- E1. unfold fp_len in *. rewrite (wrap32_id (ds_pending s1)) in * by lia.
  set (len := if cs_avail_out (ds_strm s1) <? ds_pending s1 then cs_avail_out (ds_strm s1) else ds_pending s1) in *.
  assert (Hlen : 0 <= len) by (subst len; destruct (_ <? _); lia).
  unfold Mc, olen, Mloc, fp_tail, cs_emit. cbv zeta.
  destruct (ds_pending s1 - len =? 0); dsred; rewrite rev_append_rev, length_app, length_rev;
    pose proof (arr_slice_length (ds_pending_buf s1) (ds_pending_out s1) len) as SL; unfold zlength in SL; lia.
Qed.

(* [comment removed for export] *)
Lemma Mc_flush_block_only : forall s last s8,
  s8 = tr_flush_block s (fb_buf s) (fb_len s) last -> fb_post s last s8 -> 0 <= cs_avail_out (ds_strm s) ->
  2048 <= ds_lit_bufsize s <= 32768 ->
  Mc (flush_block_only s last) = olen s + Mloc s8.
Proof.
  intros s last s8 E8 FP Ha Hl. rewrite flush_block_only_eq'. rewrite <- E8.
  destruct (fp_strm _ _ _ FP) as (dt & Es & _). pose proof (fp_pending _ _ _ FP) as Pp. pose proof (fp_biv _ _ _ FP) as Pb.
  set (s9 := set_block_start s8 (ds_strstart s8)).
  assert (B9 : ds_bi_valid s9 = ds_bi_valid s8) by reflexivity.
  assert (P9 : ds_pending s9 = ds_pending s8) by reflexivity.
  assert (S9 : ds_strm s9 = ds_strm s8) by reflexivity.
  rewrite Mc_flush_pending.
  - unfold Mc, olen, Mloc. rewrite S9, B9, P9, Es. unfold cset_data_type; cbn [cs_out_rev]. reflexivity.
  - rewrite B9. exact Pb.
  - destruct (tr_flush_bits_cases s9) as [E|[E|E]]; rewrite E; unfold put_byte; dsred; rewrite ?P9; lia.
  - assert (ES : ds_strm (tr_flush_bits s9) = ds_strm s9)
      by (destruct (tr_flush_bits_cases s9) as [E|[E|E]]; rewrite E; unfold put_byte; dsred; reflexivity).
    rewrite ES, S9, Es. unfold cset_data_type; cbn [cs_avail_out]. exact Ha.
Qed.
