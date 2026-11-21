(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateModel.

Module RefInflateInit1.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
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
Definition ireset_z (s : inflate_state) (z : zstrm) : zstrm :=
  let z := zs_set_data_type 0 (zs_set_msg MSG_NULL (zs_set_total_in 0 (zs_set_total_out 0 z))) in
  if negb (is_wrap s =? 0) then zs_set_adler (Z.land (is_wrap s) 1) z else z.

Lemma inflateReset_eq : forall s z, inflateStateCheck s = false ->
  inflateReset_tail ivar_ref s z = (ireset_s s, ireset_z s z, Z_OK).
Proof.
  intros s z Hc. unfold inflateReset_tail, inflateResetKeep. rewrite Hc.
  replace (inflateStateCheck (iset_wnext (iset_whave (iset_wsize s 0) 0) 0)) with false by (destruct s; exact (eq_sym Hc)).
  unfold ireset_s, ireset_z, auxp. cbn [iv_aux ivar_ref].
  destruct s; cbn. destruct (negb (is_wrap =? 0)); reflexivity.
Qed.

(** zlib 1.4's monadic inflateReset, when wbits already is the requested reqbits (always so after inflateReset2):
    no window free, wrap restored from reqwrap, then the tail. (zl14infl-r2) *)
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

Lemma wbits_valid_bit : forall w, 0 <= w <= 15 -> (65281 / 2 ^ w) mod 2 = (if wbits_valid w then 1 else 0).
Proof.
  intros w Hw.
  assert (H : w = 0 \/ w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/ w = 10 \/ w = 11 \/ w = 12 \/ w = 13 \/ w = 14 \/ w = 15) by lia.
  repeat (destruct H as [->|H]; [reflexivity|]). subst w. reflexivity.
Qed.

Section Init3.

Lemma land15_mod : forall w, Z.land w 15 = w mod 2 ^ 4.
Proof. intros w. change 15 with (Z.ones 4). apply Z.land_ones. lia. Qed.


Lemma szwrap_add_pow : forall k a, 0 < k -> szwrap k (a + 2 ^ k) = szwrap k a.
Proof.
  intros k a Hk. unfold szwrap. replace (a + 2 ^ k + 2 ^ (k - 1)) with (a + 2 ^ (k - 1) + 1 * 2 ^ k) by lia.
  rewrite Z.mod_add by (apply Z.pow_nonzero; lia). reflexivity.
Qed.
Lemma szwrap64_neg : forall a, - 2 ^ 63 <= a < 0 -> szwrap 64 (a + 2 ^ 64) = a.
Proof. intros a Ha. rewrite szwrap_add_pow by lia. apply szwrap_small; [lia|]. change (64 - 1) with 63. lia. Qed.
Lemma szwrap32_neg64 : forall a, - 2 ^ 31 < a <= 2 ^ 31 -> szwrap 32 (0 - (a + 2 ^ 64)) = - a.
Proof.
  intros a Ha. replace (0 - (a + 2 ^ 64)) with (- a + (- 2 ^ 32) * 2 ^ 32) by lia.
  unfold szwrap. replace (- a + - 2 ^ 32 * 2 ^ 32 + 2 ^ (32 - 1)) with (- a + 2 ^ (32 - 1) + (- 2 ^ 32) * 2 ^ 32) by lia.
  rewrite Z.mod_add by lia. change (32 - 1) with 31. rewrite Z.mod_small by lia. lia.
Qed.

Definition ir2_bad (wb : Z) : bool :=
  (wb <? -15) || (47 <? wb) || negb (wbits_valid (if wb <? 0 then - wb else Z.land wb 15)).
End Init3.
End RefInflateInit1.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition LFX : Z := 0x2e130.
Definition DFX : Z := 0x2e088.

Definition iwfx (st : inflate_state) : Prop :=
  - 2 ^ 31 <= is_last st < 2 ^ 31
  /\ - 2 ^ 31 <= is_havedict st < 2 ^ 31
  /\ - 2 ^ 31 <= is_flags st < 2 ^ 31
  /\ 0 <= is_dmax st < 2 ^ 32
  /\ 0 <= is_total st < 2 ^ 64
  /\ is_head st = 0
  /\ 0 <= is_bits st < 64 /\ 0 <= is_hold st < 2 ^ is_bits st
  /\ 0 <= is_length st < 2 ^ 32 /\ 0 <= is_offset st < 2 ^ 32 /\ 0 <= is_extra st < 2 ^ 32
  /\ match is_lencode st with CDyn ofs => 0 <= ofs <= 1444 | _ => True end
  /\ match is_distcode st with CDyn ofs => 0 <= ofs <= 1444 | _ => True end
  /\ 0 <= is_lenbits st < 2 ^ 32 /\ 0 <= is_distbits st < 2 ^ 32
  /\ 0 <= is_ncode st < 2 ^ 32 /\ 0 <= is_nlen st < 2 ^ 32 /\ 0 <= is_ndist st < 2 ^ 32 /\ 0 <= is_have st < 2 ^ 32
  /\ 0 <= is_next st <= 1444
  /\ arr_len (is_lens st) = 320 /\ arr_len (is_work st) = 288 /\ arr_len (is_codes st) = 1444
  /\ (forall i, 0 <= i < 320 -> 0 <= arr_get (is_lens st) i < 2 ^ 16)
  /\ (forall i, 0 <= i < 288 -> 0 <= arr_get (is_work st) i < 2 ^ 16)
  /\ (forall i, 0 <= i < 1444 -> 0 <= arr_get (is_codes st) i < 2 ^ 32)
  /\ is_sane st = 1 /\ - 2 ^ 31 <= is_back st < 2 ^ 31 /\ 0 <= is_was st < 2 ^ 32.

Definition iwf (st : inflate_state) : Prop :=
  HEAD <= is_mode st <= SYNC
  /\ 0 <= is_wrap st < 16
  /\ match is_window_blk st with
     | Some _ => 8 <= is_wbits st <= 15 /\ arr_len (is_window st) = 2 ^ is_wbits st
                 /\ (is_wsize st = 0 \/ is_wsize st = 2 ^ is_wbits st)
     | None => True
     end
  /\ 0 <= is_wsize st < 2 ^ 32 /\ 0 <= is_whave st < 2 ^ 32 /\ 0 <= is_wnext st < 2 ^ 32
  /\ (is_wsize st <> 0 -> is_wnext st <= is_wsize st /\ is_whave st <= is_wsize st)
  /\ (forall i, 0 <= i < arr_len (is_window st) -> 0 <= arr_get (is_window st) i < 256)
  /\ 8 <= is_wbits st <= 15
  /\ (is_window_blk st = None -> is_wsize st = 0)
  /\ (is_wsize st <> 0 -> is_whave st < is_wsize st -> is_wnext st = is_whave st)
  /\ 0 <= is_check st < 2 ^ 64
  /\ (is_wsize st = 0 -> is_whave st = 0 /\ is_wnext st = 0)
  /\ (is_window_blk st = None -> arr_len (is_window st) = 0)
  /\ iwfx st.

Lemma iwf_set_havedict : forall st v, - 2 ^ 31 <= v < 2 ^ 31 -> iwf st -> iwf (iset_havedict st v).
Proof.
  intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.
Lemma iwf_set_mode : forall st v, HEAD <= v <= SYNC -> iwf st -> iwf (iset_mode st v).
Proof.
  intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len HEAD SYNC] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.

Definition zcall_wf (zc : ZCall) : Prop :=
  zstrm_ok (zc_strm zc) /\ 0 <= zc_avail_out zc < 2 ^ 32 /\ zlength (zc_input zc) < 2 ^ 32 /\ bytes_ok (zc_input zc).
Inductive ireach : inflate_state -> Prop :=
| IR_init : forall zc wb ch s zr,
    ipure (inflateInit2_m ivar_ref hooks_pure zc wb) ch = Some (Some s, zr) -> ireach s
| IR_inflate : forall s zc flush ch s' zr,
    ireach s -> zcall_wf zc -> 0 <= flush < 16 ->
    ipure (inflate_m ivar_ref hooks_pure s zc flush) ch = Some (s', zr) -> ireach s'
| IR_setdict : forall s zc dict ch s' zr,
    ireach s -> zstrm_ok (zc_strm zc) -> bytes_ok dict -> 0 < zlength dict < 2 ^ 31 ->
    ipure (inflateSetDictionary_m hooks_pure s zc dict) ch = Some (s', zr) -> ireach s'.

Definition uw_pure (s : inflate_state) (src : arr) (end_ copy : Z) (ch : CH) : option inflate_state :=
  match is_window_blk s with
  | Some _ => Some (updw_core s src end_ copy)
  | None => match ch with
            | None => None
            | Some (b, g) => Some (updw_core (iset_window (iset_window_blk s (Some b)) (iarr_u8_of g 0 (shl32 1 (is_wbits s)))) src end_ copy)
            end
  end.
Lemma updatewindow_pure : forall s src end_ copy ch,
  updatewindow hooks_pure s src end_ copy ch = MRet (uw_pure s src end_ copy ch, ch).
Proof.
  intros s src end_ copy ch. rewrite updatewindow_unfold. unfold uw_pure.
  destruct (is_window_blk s) as [b|].
  - unfold sbind at 1. unfold sret at 1. cbn [mbind fst snd]. rewrite updw_body_eq. reflexivity.
  - unfold sbind. cbn [zalloc hooks_pure mbind fst snd sret].
    destruct ch as [[b g]|]; cbn [mbind fst snd]; [rewrite updw_body_eq|]; reflexivity.
Qed.

Definition iblocks (st : inflate_state) : list (blk * Z) :=
  match is_window_blk st with Some b => [(b, 2 ^ is_wbits st)] | None => [] end
  ++ [(is_self_blk st, 7176)].  (* zlib 1.4: sizeof(struct inflate_state) *)
