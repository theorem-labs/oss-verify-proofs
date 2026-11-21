(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItableMem2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefUpdWin1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ZS.
Variable strm : Z.
Variable nin : Z.
Variable ain : Z.
Variable nout : Z.
Variable aout : Z.
Variable S : Z.
Variable fa : Z.
Variable ff : Z.
Hypothesis Hstrm : 0 <= strm /\ strm + 112 <= 2 ^ 63.
End ZS.

Definition ireset_s (s : inflate_state) : inflate_state :=
  iset_back (iset_sane (iset_lencode (iset_distcode (iset_next (iset_last (iset_mode (iset_dmax (iset_flags
   (iset_bits (iset_hold (iset_head (iset_havedict (iset_total (iset_wnext (iset_whave (iset_wsize s
    0) 0) 0) 0) 0) 0) 0) 0) (-1)) 32768) HEAD) 0) 0) (CDyn 0)) (CDyn 0)) 1) (-1).
(* zlib 1.4: inflateResetKeep also sets strm->data_type = 0 *)
Definition ireset_z (s : inflate_state) (z : zstrm) : zstrm :=
  let z := zs_set_data_type 0 (zs_set_msg MSG_NULL (zs_set_total_in 0 (zs_set_total_out 0 z))) in
  if negb (is_wrap s =? 0) then zs_set_adler (Z.land (is_wrap s) 1) z else z.

(* zlib 1.4: 1.3.1's inflateReset is now [inflateReset_tail], the part after the window / wbits / wrap restore *)
Lemma inflateReset_eq : forall s z, inflateStateCheck s = false ->
  inflateReset_tail ivar_ref s z = (ireset_s s, ireset_z s z, Z_OK).
Proof.
  intros s z Hc. unfold inflateReset_tail, inflateResetKeep. rewrite Hc.
  replace (inflateStateCheck (iset_wnext (iset_whave (iset_wsize s 0) 0) 0)) with false by (destruct s; exact (eq_sym Hc)).
  unfold ireset_s, ireset_z, auxp. cbn [iv_aux ivar_ref].
  destruct s; cbn. destruct (negb (is_wrap =? 0)); reflexivity.
Qed.

(** zlib 1.4's monadic inflateReset, when wbits already is the requested reqbits (always so after inflateReset2):
    no window free, wrap restored from reqwrap, then the tail. *)
Lemma inflateReset_same : forall iv St (hooks : zhooks St) s z, is_wbits s = is_reqbits s ->
  inflateReset iv hooks s z
  = if inflateStateCheck s then sret (s, z, Z_STREAM_ERROR)
    else sret (inflateReset_tail iv (iset_wrap s (is_reqwrap s)) z).
Proof.
  intros iv St hooks s z H. unfold inflateReset. destruct (inflateStateCheck s); [reflexivity|].
  rewrite H, Z.eqb_refl. reflexivity.
Qed.

Section Reset.

Local Ltac islS := first [lia | unfold isl_SIZE; lia].
Local Ltac sfr := first [ apply sub_franges_here; cbn; lia | apply sub_franges_later; sfr ].
End Reset.

Section End_.
End End_.

Section End2.
End End2.

Section Init.
End Init.

Section Init2.
End Init2.

Definition wbits_valid (w : Z) : bool := (w =? 0) || ((8 <=? w) && (w <=? 15)).

Section Init3.

Lemma land15_mod : forall w, Z.land w 15 = w mod 2 ^ 4.
Proof. intros w. change 15 with (Z.ones 4). apply Z.land_ones. lia. Qed.

Definition ir2_bad (wb : Z) : bool :=
  (wb <? -15) || (47 <? wb) || negb (wbits_valid (if wb <? 0 then - wb else Z.land wb 15)).
End Init3.
