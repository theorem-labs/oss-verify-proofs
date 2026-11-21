(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeS.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma DX_status_wrap : forall s s',
  dx_core2 s' = dx_core2 (set_wrap (set_status s (ds_status s')) (ds_wrap s')) ->
  ds_pending s' = ds_pending s -> ds_pending_out s' = ds_pending_out s -> ds_bi_valid s' = ds_bi_valid s ->
  ds_pending_buf s' = ds_pending_buf s -> ds_lit_bufsize s' = ds_lit_bufsize s ->
  (ds_wrap s' < 0 -> ds_status s' = FINISH_STATE) ->
  (ds_status s' = FINISH_STATE -> ds_lookahead s = 0) ->
  DX s -> DX s'.
Proof.
  intros s s' E Ep Epo Ebv Epb Elbs Hw Hf X.
  set (t := set_wrap (set_status s (ds_status s')) (ds_wrap s')) in E.
  assert (Xt : DX t).
  { subst t. destruct X; constructor; unfold set_wrap, set_status, dmode, nsym in *; dsred; assumption. }
  apply (DX_core2_same t s' E).
  - intros i Hi. unfold sym_buf_get. subst t; unfold set_wrap, set_status; dsred. rewrite Epb, Elbs. reflexivity.
  - subst t; unfold set_wrap, set_status; dsred. rewrite Ep, Epo. exact (dx_pout0 _ X).
  - subst t; unfold set_wrap, set_status; dsred. rewrite Ebv. exact (dx_biv _ X).
  - exact Xt.
Qed.

Lemma DC_set_status : forall c0 s st,
  DC c0 s -> (st = 42 \/ st = 57 \/ st = 113 \/ st = 666) ->
  (ds_wrap s < 0 -> st = FINISH_STATE) -> (st = FINISH_STATE -> ds_lookahead s = 0) ->
  DC c0 (set_status s st) /\ KV (set_status s st) = KV s /\ ds_strm (set_status s st) = ds_strm s.
Proof.
  intros c0 s st [[D X] V] Hst Hw Hf. split; [| split; reflexivity].
  split; [split|].
  - destruct D; constructor; unfold set_status; dsred; try assumption.
    unfold deflateStateCheck. dsred. unfold INIT_STATE, GZIP_STATE, BUSY_STATE, FINISH_STATE.
    destruct Hst as [-> | [-> | [-> | ->]]]; reflexivity.
  - apply (DX_status_wrap s (set_status s st)); unfold set_status, set_wrap; dsred.
    all: first [exact X | exact Hw | exact Hf | reflexivity | (destruct s; reflexivity)].
  - apply (SV_strm c0 s); [reflexivity | exact V].
Qed.

Lemma DC_set_wrap_neg : forall c0 s w,
  DC c0 s -> - 2 <= w <= 2 -> ds_status s = FINISH_STATE ->
  DC c0 (set_wrap s w) /\ KV (set_wrap s w) = KV s /\ ds_strm (set_wrap s w) = ds_strm s.
Proof.
  intros c0 s w [[D X] V] Hw Hst. split; [| split; reflexivity].
  split; [split|].
  - destruct D; constructor; unfold set_wrap; dsred; try assumption.
  - pose proof (dx_fin _ X) as Hf.
    assert (Hw' : w < 0 -> ds_status s = FINISH_STATE) by (intros _; exact Hst).
    apply (DX_status_wrap s (set_wrap s w)); unfold set_status, set_wrap; dsred.
    all: first [exact X | exact Hw' | exact Hf | reflexivity | (destruct s; reflexivity)].
  - apply (SV_strm c0 s); [reflexivity | exact V].
Qed.

Lemma DC_set_adler : forall c0 s a, DC c0 s -> 0 <= a < 2 ^ 64 ->
  DC c0 (set_strm s (cset_adler (ds_strm s) a)) /\ KV (set_strm s (cset_adler (ds_strm s) a)) = KV s.
Proof.
  intros c0 s a [DDs V] Ha. split; [| reflexivity]. split; [apply DD_set_strm; exact DDs|].
  destruct V; constructor; unfold set_strm, cset_adler; dsred; cbn; assumption.
Qed.

Lemma put_byte_status : forall s b, ds_status (put_byte s b) = ds_status s. Proof. reflexivity. Qed.
Lemma put_byte_wrap : forall s b, ds_wrap (put_byte s b) = ds_wrap s. Proof. reflexivity. Qed.
Lemma put_byte_lookahead : forall s b, ds_lookahead (put_byte s b) = ds_lookahead s. Proof. reflexivity. Qed.
Lemma putShortMSB_status : forall s b, ds_status (putShortMSB s b) = ds_status s. Proof. reflexivity. Qed.
Lemma putShortMSB_wrap : forall s b, ds_wrap (putShortMSB s b) = ds_wrap s. Proof. reflexivity. Qed.
Lemma putShortMSB_lookahead : forall s b, ds_lookahead (putShortMSB s b) = ds_lookahead s. Proof. reflexivity. Qed.

Definition PW (c0 : cstrm) (s : deflate_state) (n : Z) : Prop :=
  DC c0 s /\ ds_pending_out s = 0 /\ 0 <= ds_pending s <= n.

Lemma PW_put_byte : forall c0 s n b, PW c0 s n -> n + 1 <= 128 ->
  PW c0 (put_byte s b) (n + 1) /\ KV (put_byte s b) = KV s /\ ds_strm (put_byte s b) = ds_strm s.
Proof.
  intros c0 s n b (HDC & Hpo & Hp) Hn. pose proof HDC as [[D X] V]. pose proof (dwf_sizes s D) as (_ & _ & Sl & _).
  destruct (DC_put_byte c0 s b HDC ltac:(lia) ltac:(lia)) as (HDC' & E1 & E2 & E3 & E4 & E5).
  split; [| split; [exact E3 | exact E4]]. split; [exact HDC'|]. rewrite E1, E2. lia.
Qed.

Lemma PW_putShortMSB : forall c0 s n b, PW c0 s n -> n + 2 <= 128 ->
  PW c0 (putShortMSB s b) (n + 2) /\ KV (putShortMSB s b) = KV s /\ ds_strm (putShortMSB s b) = ds_strm s.
Proof.
  intros c0 s n b H Hn. unfold putShortMSB.
  destruct (PW_put_byte c0 s n (Z.shiftr b 8) H ltac:(lia)) as (H1 & K1 & S1).
  destruct (PW_put_byte c0 _ (n + 1) (Z.land b 255) H1 ltac:(lia)) as (H2 & K2 & S2).
  replace (n + 2) with (n + 1 + 1) by lia. split; [exact H2|]. rewrite K2, S2, K1, S1. split; reflexivity.
Qed.

Lemma PW_weaken : forall c0 s n m, PW c0 s n -> n <= m -> PW c0 s m.
Proof. intros c0 s n m (A & B & C) H. split; [exact A|]. split; [exact B | lia]. Qed.

Lemma PW_set_adler : forall c0 s n a, PW c0 s n -> 0 <= a < 2 ^ 64 ->
  PW c0 (set_strm s (cset_adler (ds_strm s) a)) n /\ KV (set_strm s (cset_adler (ds_strm s) a)) = KV s.
Proof.
  intros c0 s n a (A & B & C) Ha. destruct (DC_set_adler c0 s a A Ha) as [A' K]. split; [| exact K].
  split; [exact A'|]. unfold set_strm; dsred. split; [exact B | exact C].
Qed.

Lemma PW_set_status_busy : forall c0 s n, PW c0 s n -> ds_status s <> FINISH_STATE ->
  PW c0 (set_status s BUSY_STATE) n /\ KV (set_status s BUSY_STATE) = KV s.
Proof.
  intros c0 s n (A & B & C) Hst. pose proof A as [[D X] V].
  destruct (DC_set_status c0 s BUSY_STATE A ltac:(unfold BUSY_STATE; lia)
              ltac:(intros Hw; exfalso; exact (Hst (dx_wrapneg _ X Hw))) ltac:(unfold BUSY_STATE, FINISH_STATE; intros; lia)) as (A' & K & _).
  split; [| exact K]. split; [exact A'|]. unfold set_status; dsred. split; [exact B | exact C].
Qed.

Lemma adler32_init_range : 0 <= adler32_init < 2 ^ 64. Proof. unfold adler32_init. cbn. lia. Qed.
Lemma crc32_init_range : 0 <= crc32_init < 2 ^ 64. Proof. unfold crc32_init. cbn. lia. Qed.

Lemma zhdr_facts : forall c0 s, DC c0 s -> ds_pending s = 0 -> ds_status s = INIT_STATE ->
  let h := zhdr_st s in
  PW c0 h 6 /\ KV h = KV s /\ OUTLE s h /\ ds_status h = BUSY_STATE
  /\ cs_avail_in (ds_strm h) = cs_avail_in (ds_strm s) /\ ds_lookahead h = ds_lookahead s /\ ds_wrap h = ds_wrap s.
Proof.
  intros c0 s HDC Hp Hst h. subst h. pose proof HDC as [[D X] V].
  assert (P0 : PW c0 s 0) by (split; [exact HDC|]; split; [exact (dx_pout0 _ X Hp) | lia]).
  unfold zhdr_st. cbv zeta.
  match goal with |- context [putShortMSB s ?hd] => set (hdr := hd) end.
  destruct (PW_putShortMSB c0 s 0 hdr P0 ltac:(lia)) as (P1 & K1 & S1).
  set (s1 := putShortMSB s hdr) in *.
  assert (Hst1 : ds_status s1 = INIT_STATE) by (unfold s1; rewrite putShortMSB_status; exact Hst).
  set (s2 := if negb (ds_strstart s1 =? 0) then putShortMSB (putShortMSB s1 (wrap32 (Z.shiftr (cs_adler (ds_strm s1)) 16))) (Z.land (cs_adler (ds_strm s1)) 65535) else s1).
  assert (Hl1 : ds_lookahead s1 = ds_lookahead s /\ ds_wrap s1 = ds_wrap s) by (unfold s1; rewrite putShortMSB_lookahead, putShortMSB_wrap; split; reflexivity).
  assert (H2 : PW c0 s2 6 /\ KV s2 = KV s /\ ds_strm s2 = ds_strm s /\ ds_status s2 = INIT_STATE /\ ds_lookahead s2 = ds_lookahead s /\ ds_wrap s2 = ds_wrap s).
  { subst s2. destruct (negb (ds_strstart s1 =? 0)).
    - destruct (PW_putShortMSB c0 s1 2 (wrap32 (Z.shiftr (cs_adler (ds_strm s1)) 16)) P1 ltac:(lia)) as (P2 & K2 & S2).
      destruct (PW_putShortMSB c0 _ 4 (Z.land (cs_adler (ds_strm s1)) 65535) P2 ltac:(lia)) as (P3 & K3 & S3).
      split; [exact P3|]. rewrite K3, S3, K2, S2, K1, S1. split; [reflexivity|]. split; [reflexivity|].
      rewrite !putShortMSB_status, !putShortMSB_lookahead, !putShortMSB_wrap. split; [exact Hst1 | exact Hl1].
    - split; [apply (PW_weaken c0 s1 2 6 P1); lia|]. rewrite K1, S1. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hst1 | exact Hl1]. }
  clearbody s2. destruct H2 as (P2 & K2 & S2 & Hst2 & Hl2 & Hw2).
  destruct (PW_set_adler c0 s2 6 adler32_init P2 adler32_init_range) as (P3 & K3).
  destruct (PW_set_status_busy c0 _ 6 P3 ltac:(unfold set_strm; dsred; rewrite Hst2; unfold INIT_STATE, FINISH_STATE; lia)) as (P4 & K4).
  split; [exact P4|]. split; [rewrite K4, K3, K2; reflexivity|].
  split; [unfold OUTLE, set_status, set_strm, cset_adler; dsred; cbn [cs_out_rev]; rewrite S2; exists nil; reflexivity|].
  split; [reflexivity|].
  unfold set_status, set_strm, cset_adler; dsred. cbn [cs_avail_in]. rewrite S2. split; [reflexivity|]. split; [exact Hl2 | exact Hw2].
Qed.

Lemma gzhdr_facts : forall c0 s, DC c0 s -> ds_pending s = 0 -> ds_status s = GZIP_STATE ->
  let h := gzhdr_st s in
  PW c0 h 10 /\ KV h = KV s /\ OUTLE s h /\ ds_status h = BUSY_STATE
  /\ cs_avail_in (ds_strm h) = cs_avail_in (ds_strm s) /\ ds_lookahead h = ds_lookahead s /\ ds_wrap h = ds_wrap s.
Proof.
  intros c0 s HDC Hp Hst h. subst h. pose proof HDC as [[D X] V].
  assert (P0 : PW c0 s 0) by (split; [exact HDC|]; split; [exact (dx_pout0 _ X Hp) | lia]).
  unfold gzhdr_st. cbv zeta.
  destruct (PW_set_adler c0 s 0 crc32_init P0 crc32_init_range) as (Q0 & J0).
  set (t0 := set_strm s (cset_adler (ds_strm s) crc32_init)) in *.
  set (t1 := put_byte t0 31). set (t2 := put_byte t1 139). set (t3 := put_byte t2 8). set (t4 := put_byte t3 0).
  set (t5 := put_byte t4 0). set (t6 := put_byte t5 0). set (t7 := put_byte t6 0). set (t8 := put_byte t7 0).
  match goal with |- context [put_byte t8 ?x] => set (xflv := x) end.
  set (t9 := put_byte t8 xflv). set (t10 := put_byte t9 OS_CODE).
  destruct (PW_put_byte c0 t0 0 31 Q0 ltac:(lia)) as (Q1 & J1 & S1). fold t1 in Q1, J1, S1.
  destruct (PW_put_byte c0 t1 1 139 Q1 ltac:(lia)) as (Q2 & J2 & S2). fold t2 in Q2, J2, S2.
  destruct (PW_put_byte c0 t2 2 8 Q2 ltac:(lia)) as (Q3 & J3 & S3). fold t3 in Q3, J3, S3.
  destruct (PW_put_byte c0 t3 3 0 Q3 ltac:(lia)) as (Q4 & J4 & S4). fold t4 in Q4, J4, S4.
  destruct (PW_put_byte c0 t4 4 0 Q4 ltac:(lia)) as (Q5 & J5 & S5). fold t5 in Q5, J5, S5.
  destruct (PW_put_byte c0 t5 5 0 Q5 ltac:(lia)) as (Q6 & J6 & S6). fold t6 in Q6, J6, S6.
  destruct (PW_put_byte c0 t6 6 0 Q6 ltac:(lia)) as (Q7 & J7 & S7). fold t7 in Q7, J7, S7.
  destruct (PW_put_byte c0 t7 7 0 Q7 ltac:(lia)) as (Q8 & J8 & S8). fold t8 in Q8, J8, S8.
  destruct (PW_put_byte c0 t8 8 xflv Q8 ltac:(lia)) as (Q9 & J9 & S9). fold t9 in Q9, J9, S9.
  destruct (PW_put_byte c0 t9 9 OS_CODE Q9 ltac:(lia)) as (Q10 & J10 & S10). fold t10 in Q10, J10, S10.
  assert (St10 : ds_status t10 = GZIP_STATE /\ ds_lookahead t10 = ds_lookahead s /\ ds_wrap t10 = ds_wrap s).
  { unfold t10. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap. unfold t9. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap.
    unfold t8. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap. unfold t7. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap.
    unfold t6. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap. unfold t5. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap.
    unfold t4. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap. unfold t3. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap.
    unfold t2. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap. unfold t1. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap.
    unfold t0. unfold set_strm; dsred. split; [exact Hst | split; reflexivity]. }
  destruct St10 as (St10 & Lk10 & Wr10).
  destruct (PW_set_status_busy c0 t10 10 Q10 ltac:(rewrite St10; unfold GZIP_STATE, FINISH_STATE; lia)) as (Q11 & J11).
  split; [exact Q11|].
  split; [rewrite J11, J10, J9, J8, J7, J6, J5, J4, J3, J2, J1, J0; reflexivity|].
  split; [unfold OUTLE; unfold set_status; dsred; rewrite S10, S9, S8, S7, S6, S5, S4, S3, S2, S1; unfold t0, set_strm, cset_adler; dsred; cbn [cs_out_rev]; exists nil; reflexivity|].
  split; [reflexivity|].
  unfold set_status; dsred. rewrite S10, S9, S8, S7, S6, S5, S4, S3, S2, S1. split; [unfold t0, set_strm, cset_adler; dsred; reflexivity|].
  split; [exact Lk10 | exact Wr10].
Qed.

Lemma trailer_facts : forall c0 s, DC c0 s -> ds_pending s = 0 ->
  let h := trailer_st s in
  PW c0 h 8 /\ KV h = KV s /\ OUTLE s h /\ ds_status h = ds_status s /\ ds_wrap h = ds_wrap s /\ ds_lookahead h = ds_lookahead s.
Proof.
  intros c0 s HDC Hp h. subst h. pose proof HDC as [[D X] V].
  assert (P0 : PW c0 s 0) by (split; [exact HDC|]; split; [exact (dx_pout0 _ X Hp) | lia]).
  unfold trailer_st. cbv zeta.
  destruct (ds_wrap s =? 2).
  - set (a := cs_adler (ds_strm s)). set (t := cs_total_in (ds_strm s)).
    set (t1 := put_byte s (Z.land a 255)). set (t2 := put_byte t1 (Z.land (Z.shiftr a 8) 255)).
    set (t3 := put_byte t2 (Z.land (Z.shiftr a 16) 255)). set (t4 := put_byte t3 (Z.land (Z.shiftr a 24) 255)).
    set (t5 := put_byte t4 (Z.land t 255)). set (t6 := put_byte t5 (Z.land (Z.shiftr t 8) 255)).
    set (t7 := put_byte t6 (Z.land (Z.shiftr t 16) 255)). set (t8 := put_byte t7 (Z.land (Z.shiftr t 24) 255)).
    destruct (PW_put_byte c0 s 0 (Z.land a 255) P0 ltac:(lia)) as (Q1 & J1 & S1). fold t1 in Q1, J1, S1.
    destruct (PW_put_byte c0 t1 1 (Z.land (Z.shiftr a 8) 255) Q1 ltac:(lia)) as (Q2 & J2 & S2). fold t2 in Q2, J2, S2.
    destruct (PW_put_byte c0 t2 2 (Z.land (Z.shiftr a 16) 255) Q2 ltac:(lia)) as (Q3 & J3 & S3). fold t3 in Q3, J3, S3.
    destruct (PW_put_byte c0 t3 3 (Z.land (Z.shiftr a 24) 255) Q3 ltac:(lia)) as (Q4 & J4 & S4). fold t4 in Q4, J4, S4.
    destruct (PW_put_byte c0 t4 4 (Z.land t 255) Q4 ltac:(lia)) as (Q5 & J5 & S5). fold t5 in Q5, J5, S5.
    destruct (PW_put_byte c0 t5 5 (Z.land (Z.shiftr t 8) 255) Q5 ltac:(lia)) as (Q6 & J6 & S6). fold t6 in Q6, J6, S6.
    destruct (PW_put_byte c0 t6 6 (Z.land (Z.shiftr t 16) 255) Q6 ltac:(lia)) as (Q7 & J7 & S7). fold t7 in Q7, J7, S7.
    destruct (PW_put_byte c0 t7 7 (Z.land (Z.shiftr t 24) 255) Q7 ltac:(lia)) as (Q8 & J8 & S8). fold t8 in Q8, J8, S8.
    split; [exact Q8|].
    split; [rewrite J8, J7, J6, J5, J4, J3, J2, J1; reflexivity|].
    split; [unfold OUTLE; rewrite S8, S7, S6, S5, S4, S3, S2, S1; exists nil; reflexivity|].
    unfold t8. rewrite put_byte_status, put_byte_wrap, put_byte_lookahead. unfold t7. rewrite put_byte_status, put_byte_wrap, put_byte_lookahead.
    unfold t6. rewrite put_byte_status, put_byte_wrap, put_byte_lookahead. unfold t5. rewrite put_byte_status, put_byte_wrap, put_byte_lookahead.
    unfold t4. rewrite put_byte_status, put_byte_wrap, put_byte_lookahead. unfold t3. rewrite put_byte_status, put_byte_wrap, put_byte_lookahead.
    unfold t2. rewrite put_byte_status, put_byte_wrap, put_byte_lookahead. unfold t1. rewrite put_byte_status, put_byte_wrap, put_byte_lookahead.
    repeat split; reflexivity.
  - set (a := cs_adler (ds_strm s)).
    set (t1 := putShortMSB s (wrap32 (Z.shiftr a 16))). set (t2 := putShortMSB t1 (Z.land a 65535)).
    destruct (PW_putShortMSB c0 s 0 (wrap32 (Z.shiftr a 16)) P0 ltac:(lia)) as (Q1 & J1 & S1). fold t1 in Q1, J1, S1.
    destruct (PW_putShortMSB c0 t1 2 (Z.land a 65535) Q1 ltac:(lia)) as (Q2 & J2 & S2). fold t2 in Q2, J2, S2.
    split; [apply (PW_weaken _ _ _ 8 Q2); lia|].
    split; [rewrite J2, J1; reflexivity|].
    split; [unfold OUTLE; rewrite S2, S1; exists nil; reflexivity|].
    unfold t2. rewrite putShortMSB_status, putShortMSB_wrap, putShortMSB_lookahead.
    unfold t1. rewrite putShortMSB_status, putShortMSB_wrap, putShortMSB_lookahead. repeat split; reflexivity.
Qed.

Lemma DC_upd4 : forall c0 s A P B V,
  DC c0 s -> ds_pending_out s = 0 ->
  arr_len A = arr_len (ds_pending_buf s) ->
  (forall i, 0 <= i < ds_lit_bufsize s * 4 -> 0 <= arr_get A i < 256) ->
  (forall i, ds_lit_bufsize s <= i -> arr_get A i = arr_get (ds_pending_buf s) i) ->
  0 <= P <= ds_lit_bufsize s -> 0 <= V <= 7 -> 0 <= B < 2 ^ 16 ->
  DC c0 (upd4 s A P B V) /\ KV (upd4 s A P B V) = KV s /\ ds_strm (upd4 s A P B V) = ds_strm s.
Proof.
  intros c0 s A P B V [[D X] Vs] Hpo HlenA HbA HhiA HP HV HB. pose proof (dwf_sizes s D) as (_ & _ & Sl & _).
  split; [| split; reflexivity].
  split; [split|].
  - destruct D; constructor; unfold upd4; dsred; try assumption; try lia.
  - apply (DX_core2_same s); [reflexivity | | | | exact X]; unfold upd4; dsred.
    + intros i Hi. unfold sym_buf_get; dsred. apply HhiA. lia.
    + intros _. exact Hpo.
    + lia.
  - apply (SV_strm c0 s); [reflexivity | exact Vs].
Qed.

Lemma arr_get_set_other' : forall (a : arr) i j v, i <> j -> arr_get (arr_set a i v) j = arr_get a j.
Proof. intros a i j v H. rewrite arr_get_set. destruct (Z.eqb_spec i j); [lia|]. cbn [andb]. reflexivity. Qed.

Local Ltac bytes_tac Hbb :=
  intros i Hi; rewrite !arr_get_set;
  repeat (destruct (_ && _); [apply wrap8_range|]); apply Hbb; exact Hi.

Lemma tr_align_facts : forall c0 s, DC c0 s -> ds_pending s = 0 ->
  let h := tr_align s in
  DC c0 h /\ KV h = KV s /\ ds_strm h = ds_strm s /\ 0 <= ds_pending h <= 3 /\ ds_pending_out h = 0 /\ dx_core2 h = dx_core2 s.
Proof.
  intros c0 s HDC Hp h. subst h. pose proof HDC as [[D X] V]. pose proof (dwf_sizes s D) as (_ & _ & Sl & _).
  pose proof (df_bi _ D) as [Hbv Hbb]. pose proof (dx_biv _ X) as Hbv7. pose proof (dx_pout0 _ X Hp) as Hpo.
  pose proof (df_bb _ D) as Hbytes. pose proof (df_bl _ D) as Hbl.
  pose proof (sb_nb_range s 2) as Hnb.
  assert (Hnb8 : 0 <= Z.shiftr (sb_nb s 2) 8 < 2 ^ 16).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  destruct (Z_lt_le_dec (ds_bi_valid s) 6) as [C1|C1]; [| destruct (Z.eq_dec (ds_bi_valid s) 6) as [C2|C2]].
  - rewrite (tr_align_eq1 s Hbb) by lia.
    destruct (DC_upd4 c0 s (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (sb_nb s 2))) (ds_pending s + 1) (Z.shiftr (sb_nb s 2) 8) (ds_bi_valid s + 2)
                HDC Hpo ltac:(rewrite arr_len_set; reflexivity) ltac:(bytes_tac Hbytes)
                ltac:(intros i Hi; apply arr_get_set_other'; lia) ltac:(lia) ltac:(lia) Hnb8) as (A1 & A2 & A3).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. unfold upd4; dsred. repeat split; try lia; reflexivity.
  - rewrite (tr_align_eq2 s Hbb C2).
    destruct (DC_upd4 c0 s (arr_set (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land (sb_nb s 2) 255))) (ds_pending s + 1) (wrap8 (Z.shiftr (wrap16 (sb_nb s 2)) 8)))
                (ds_pending s + 1 + 1) 0 0
                HDC Hpo ltac:(rewrite !arr_len_set; reflexivity) ltac:(bytes_tac Hbytes)
                ltac:(intros i Hi; rewrite !arr_get_set_other' by lia; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as (A1 & A2 & A3).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. unfold upd4; dsred. repeat split; try lia; reflexivity.
  - rewrite (tr_align_eq3 s Hbb) by lia.
    destruct (DC_upd4 c0 s (arr_set (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land (sb_nb s 2) 255))) (ds_pending s + 1) (wrap8 (Z.shiftr (wrap16 (sb_nb s 2)) 8)))
                (ds_pending s + 1 + 1) 0 (ds_bi_valid s - 6)
                HDC Hpo ltac:(rewrite !arr_len_set; reflexivity) ltac:(bytes_tac Hbytes)
                ltac:(intros i Hi; rewrite !arr_get_set_other' by lia; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as (A1 & A2 & A3).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. unfold upd4; dsred. repeat split; try lia; reflexivity.
Qed.

Lemma tsb0_facts : forall c0 s, DC c0 s -> ds_pending s = 0 ->
  let h := tr_stored_block s None 0 0 in
  DC c0 h /\ KV h = KV s /\ ds_strm h = ds_strm s /\ 0 <= ds_pending h <= 7 /\ ds_pending_out h = 0 /\ dx_core2 h = dx_core2 s
  /\ ds_bi_valid h = 0.
Proof.
  intros c0 s HDC Hp h. subst h. pose proof HDC as [[D X] V]. pose proof (dwf_sizes s D) as (_ & _ & Sl & _).
  pose proof (df_bi _ D) as [Hbv Hbb]. pose proof (dx_pout0 _ X Hp) as Hpo.
  pose proof (df_bb _ D) as Hbytes.
  rewrite (tr_stored_block_eq s None 0 0 Hbv Hbb). unfold tsb_tail. cbn [negb Z.eqb].
  pose proof (tsb_hP_range s) as HP.
  assert (HA : forall i, ds_pending s + 3 <= i -> arr_get (tsb_hA s 0) i = arr_get (ds_pending_buf s) i).
  { intros i Hi. unfold tsb_hA. destruct (_ <=? 5); [| destruct (_ <=? 13)]; rewrite !arr_get_set_other' by lia; reflexivity. }
  assert (HAb : forall i, 0 <= i < ds_lit_bufsize s * 4 -> 0 <= arr_get (tsb_hA s 0) i < 256).
  { unfold tsb_hA. destruct (_ <=? 5); [| destruct (_ <=? 13)]; bytes_tac Hbytes. }
  destruct (DC_upd4 c0 s (tsb_lenA (tsb_hA s 0) (tsb_hP s) 0) (tsb_hP s + 1 + 1 + 1 + 1 + 0) 0 0 HDC Hpo
              ltac:(unfold tsb_lenA; rewrite !arr_len_set; apply tsb_hA_len)
              ltac:(unfold tsb_lenA; bytes_tac HAb)
              ltac:(intros i Hi; unfold tsb_lenA; rewrite !arr_get_set_other' by lia; apply HA; lia)
              ltac:(lia) ltac:(lia) ltac:(lia)) as (A1 & A2 & A3).
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. unfold upd4; dsred. repeat split; try lia; reflexivity.
Qed.

Lemma clear_hash_eq : forall s,
  clear_hash s = set_head s (arr_fill (arr_set (ds_head s) (ds_hash_size s - 1) NIL) 0 (ds_hash_size s - 1) 0).
Proof. intros s. unfold clear_hash. dsred. reflexivity. Qed.

Lemma DC_clear_hash : forall c0 s, DC c0 s ->
  DC c0 (clear_hash s) /\ KV (clear_hash s) = KV s /\ ds_strm (clear_hash s) = ds_strm s
  /\ (forall h, 0 <= h < ds_hash_size s -> arr_get (ds_head (clear_hash s)) h = 0)
  /\ ds_pending (clear_hash s) = ds_pending s /\ ds_pending_out (clear_hash s) = ds_pending_out s
  /\ ds_lookahead (clear_hash s) = ds_lookahead s /\ ds_bi_valid (clear_hash s) = ds_bi_valid s
  /\ ds_match_available (clear_hash s) = ds_match_available s.
Proof.
  intros c0 s [[D X] V]. pose proof (dwf_sizes s D) as (_ & Sh & _). pose proof (df_hl _ D) as Hhl.
  assert (H0 : forall h, 0 <= h < ds_hash_size s -> arr_get (ds_head (clear_hash s)) h = 0).
  { intros h Hh. rewrite clear_hash_eq. dsred. rewrite arr_get_fill. unfold arr_inb. rewrite arr_len_set, Hhl.
    destruct (Z_lt_le_dec h (ds_hash_size s - 1)).
    - replace ((0 <=? h) && (h <? 0 + Z.max 0 (ds_hash_size s - 1)) && ((0 <=? h) && (h <? ds_hash_size s))) with true
        by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity.
    - replace ((0 <=? h) && (h <? 0 + Z.max 0 (ds_hash_size s - 1)) && ((0 <=? h) && (h <? ds_hash_size s))) with false
        by (symmetry; apply andb_false_iff; left; apply andb_false_iff; right; apply Z.ltb_ge; lia).
      replace h with (ds_hash_size s - 1) by lia. rewrite arr_get_set_same by (rewrite Hhl; lia). reflexivity. }
  rewrite clear_hash_eq in H0 |- *. unfold set_head in H0. cbn [ds_head] in H0. dsred.
  split; [| repeat split; reflexivity || (intros; apply H0; assumption)].
  split; [split|].
  - destruct D; constructor; dsred; try assumption.
    + rewrite arr_len_fill, arr_len_set. assumption.
    + intros i Hi. rewrite (H0 i Hi). lia.
  - destruct X; constructor; dsred; try assumption.
    intros Hm. apply CHAIN_heads0. dsred. exact H0.
  - apply (SV_strm c0 s); [reflexivity | exact V].
Qed.

Lemma DC_reset0 : forall c0 s, DC c0 s -> ds_lookahead s = 0 -> ds_match_available s = 0 ->
  (forall h, 0 <= h < ds_hash_size s -> arr_get (ds_head s) h = 0) ->
  let s' := set_insert (set_block_start (set_strstart s 0) 0) 0 in
  DC c0 s' /\ KV s' = KV s /\ ds_strm s' = ds_strm s /\ ds_pending s' = ds_pending s /\ ds_pending_out s' = ds_pending_out s
  /\ ds_lookahead s' = 0 /\ ds_bi_valid s' = ds_bi_valid s.
Proof.
  intros c0 s [[D X] V] Hl Hma0 H0 s'. subst s'.
  split; [| dsred; repeat split; try reflexivity; exact Hl].
  split; [split|].
  - destruct D; constructor; dsred; try assumption; try lia.
  - pose proof (dx_nsym _ X) as Xns. pose proof (dx_ma _ X) as Xma. pose proof (dwf_sizes s D) as (Sw & _).

    destruct X as [Xcfg Xinsh Xins Xml Xpl Xma' Xpm Xmatches Xhw Xfast Xnotslow Xslow Xst0 Xwrapneg Xfin Xsn Xnsym Xsyms Xhist Xopt
                   Xstat Xext Xtfc Xtdl Xdepth Xblc Xchain Xpout0 Xbiv];
      constructor; unfold dmode, nsym in *; dsred; try assumption;
      [ first [ solve [ clear - Sw; lia ] | lia ]
      | first [ solve [ clear - Xslow Hl Hma0; lia ] | lia ]
      | first [ solve [ clear - Xst0 Hl; lia ] | lia ]
      | first [ solve [ clear - Xns Xma; lia ] | lia ]
      | intros Hm; apply CHAIN_heads0; dsred; exact H0 ].
  - apply (SV_strm c0 s); [reflexivity | exact V].
Qed.

Lemma bdone_facts : forall c0 s flush, DC c0 s -> ds_pending s = 0 -> ds_match_available s = 0 ->
  let h := bdone_st s flush in
  DC c0 h /\ KV h = KV s /\ ds_strm h = ds_strm s /\ 0 <= ds_pending h <= 7 /\ ds_pending_out h = 0
  /\ (flush = Z_PARTIAL_FLUSH -> ds_pending (tr_align s) <= ds_lit_bufsize s * 4)
  /\ (flush <> Z_PARTIAL_FLUSH -> flush <> Z_BLOCK -> ds_pending (tr_stored_block s None 0 0) <= ds_lit_bufsize s * 4).
Proof.
  intros c0 s flush HDC Hp Hma0 h. subst h. pose proof HDC as [[D X] V]. pose proof (dwf_sizes s D) as (_ & _ & Sl & _).
  pose proof (dx_pout0 _ X Hp) as Hpo.
  destruct (tr_align_facts c0 s HDC Hp) as (A1 & A2 & A3 & A4 & A5 & A6).
  destruct (tsb0_facts c0 s HDC Hp) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  assert (R1 : flush = Z_PARTIAL_FLUSH -> ds_pending (tr_align s) <= ds_lit_bufsize s * 4) by (intros; lia).
  assert (R2 : flush <> Z_PARTIAL_FLUSH -> flush <> Z_BLOCK -> ds_pending (tr_stored_block s None 0 0) <= ds_lit_bufsize s * 4) by (intros; lia).
  unfold bdone_st.
  destruct (Z.eqb_spec flush Z_PARTIAL_FLUSH) as [Ef|Ef].
  { split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [lia|]. split; [exact A5|]. split; [exact R1 | exact R2]. }
  destruct (negb (flush =? Z_BLOCK)) eqn:Eb.
  2:{ split; [exact HDC|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact Hpo|]. split; [exact R1 | exact R2]. }
  set (t := tr_stored_block s None 0 0) in *.
  destruct (flush =? Z_FULL_FLUSH).
  2:{ split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|]. split; [exact R1 | exact R2]. }
  destruct (DC_clear_hash c0 t B1) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
  destruct (Z.eqb_spec (ds_lookahead (clear_hash t)) 0) as [El|El].
  - pose proof (KV_fields t (clear_hash t) C2) as (_ & Eh & _).
    pose proof (dx_core2_fields _ _ B6) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ema & _).
    destruct (DC_reset0 c0 (clear_hash t) C1 El ltac:(rewrite C9, Ema; exact Hma0) ltac:(rewrite Eh; exact C4)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
    split; [exact E1|]. split; [rewrite E2, C2; exact B2|]. split; [rewrite E3, C3; exact B3|].
    split; [rewrite E4, C5; exact B4|]. split; [rewrite E5, C6; exact B5|]. split; [exact R1 | exact R2].
  - split; [exact C1|]. split; [rewrite C2; exact B2|]. split; [rewrite C3; exact B3|].
    split; [rewrite C5; exact B4|]. split; [rewrite C6; exact B5|]. split; [exact R1 | exact R2].
Qed.
