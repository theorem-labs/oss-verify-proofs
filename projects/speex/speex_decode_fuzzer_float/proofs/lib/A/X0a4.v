(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1dh X1ch X1cg X1dk X1cr X1cs X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nw X1qz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X05p X09u X0ae X09j X09x X09z X0a0 X0a1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1cu.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X110 X106 X10j X10l X10m X10n.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10n.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1cu.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition body_pre (body : list Z) (bytes : list byte) : Prop :=
firstn (length body) (ubytes bytes) = body /\ (length body <= length bytes)%nat.

Lemma u32s_firstn : forall n ws, firstn (4 * n) (u32s ws) = u32s (firstn n ws).
Proof.
induction n as [|n IH]; intros ws; [cbn; reflexivity|].
destruct ws as [|w ws]; [cbn; destruct (4 * S n)%nat; reflexivity|]. cbn [u32s firstn].
rewrite firstn_app, length_le4, firstn_all2 by (rewrite length_le4; lia).
replace (4 * S n - 4)%nat with (4 * n)%nat by lia. rewrite IH. reflexivity.
Qed.
Lemma u32s_skipn : forall n ws, skipn (4 * n) (u32s ws) = u32s (skipn n ws).
Proof.
induction n as [|n IH]; intros ws; [cbn; reflexivity|].
destruct ws as [|w ws]; [cbn; destruct (4 * S n)%nat; reflexivity|]. cbn [u32s skipn].
rewrite skipn_app, length_le4, skipn_all2 by (rewrite length_le4; lia).
replace (4 * S n - 4)%nat with (4 * n)%nat by lia. rewrite IH. reflexivity.
Qed.
Lemma u64s_firstn : forall n ws, firstn (8 * n) (u64s ws) = u64s (firstn n ws).
Proof.
induction n as [|n IH]; intros ws; [cbn; reflexivity|].
destruct ws as [|w ws]; [cbn; destruct (8 * S n)%nat; reflexivity|]. cbn [u64s firstn].
rewrite firstn_app, length_le8, firstn_all2 by (rewrite length_le8; lia).
replace (8 * S n - 8)%nat with (8 * n)%nat by lia. rewrite IH. reflexivity.
Qed.
Lemma u64s_skipn : forall n ws, skipn (8 * n) (u64s ws) = u64s (skipn n ws).
Proof.
induction n as [|n IH]; intros ws; [cbn; reflexivity|].
destruct ws as [|w ws]; [cbn; destruct (8 * S n)%nat; reflexivity|]. cbn [u64s skipn].
rewrite skipn_app, length_le8, skipn_all2 by (rewrite length_le8; lia).
replace (8 * S n - 8)%nat with (8 * n)%nat by lia. rewrite IH. reflexivity.
Qed.

Lemma u32_move : forall ws k n, (k + n <= length ws)%nat ->
firstn (4 * n) (skipn (4 * k) (u32s ws)) ++ skipn (4 * n) (u32s ws) = u32s (firstn n (skipn k ws) ++ skipn n ws).
Proof. intros. rewrite u32s_skipn, u32s_firstn, u32s_skipn, u32s_app. reflexivity. Qed.
Lemma u64_move : forall ws k n, (k + n <= length ws)%nat ->
firstn (8 * n) (skipn (8 * k) (u64s ws)) ++ skipn (8 * n) (u64s ws) = u64s (firstn n (skipn k ws) ++ skipn n ws).
Proof. intros. rewrite u64s_skipn, u64s_firstn, u64s_skipn, u64s_app. reflexivity. Qed.

Lemma wpre_move : forall l ws k, wpre l ws -> (k <= length l)%nat ->
wpre (skipn k l) (firstn (length l - k) (skipn k ws) ++ skipn (length l - k) ws).
Proof.
intros l ws k [P L] Hk. unfold wpre. rewrite skipn_length, app_length, firstn_length_le, skipn_length by (rewrite skipn_length; lia).
split; [|lia]. rewrite firstn_app, firstn_firstn, Nat.min_id, firstn_length_le, Nat.sub_diag, firstn_O, app_nil_r by (rewrite skipn_length; lia).
rewrite <- skipn_map, <- P, skipn_firstn_comm. reflexivity.
Qed.

Definition ret_body (os : stream_st bptr) : stream_st bptr :=
if negb (os_body_returned os =? 0) then
set_body os (ztake (os_body_fill os - os_body_returned os) (zdrop (os_body_returned os) (os_body os)))
(os_body_storage os) (os_body_fill os - os_body_returned os) 0
else os.
Definition ret_lacing (os : stream_st bptr) : stream_st bptr :=
if negb (os_lacing_returned os =? 0) then
set_lacing os (zdrop (os_lacing_returned os) (os_lacing os)) (zdrop (os_lacing_returned os) (os_granules os)) (os_lacing_storage os)
(os_lacing_fill os - os_lacing_returned os) (os_lacing_packet os - os_lacing_returned os) 0
else os.
Lemma pagein_returned_eq : forall os : stream_st bptr, pagein_returned os = ret_lacing (ret_body os).
Proof.
intros os. unfold pagein_returned, ret_lacing, ret_body.
destruct (negb (os_body_returned os =? 0)); reflexivity.
Qed.

Lemma fields_ok_returned : forall os : stream_st bptr,
stream_fields_ok os -> stream_inv os -> os_body_returned os <= os_body_fill os ->
stream_fields_ok (pagein_returned os).
Proof.
intros os FOK sfH_; first [ sf_destruct 5%nat sfH_ as I1 I2 I3 I4 I5 | sf_fb; destruct sfH_ as (I1 & I2 & I3 & I4 & I5) ]; intros Hbr.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in *.
unfold pagein_returned.
destruct (negb (os_body_returned os =? 0)); destruct (negb (os_lacing_returned _ =? 0));
unfold stream_fields_ok, int31, set_lacing, set_body in *; destruct os; cbn in *; (clear - F7 F6 F5 F3 F2 Hbr I2 I1 FOK os_pageno os_serialno os_b_o_s os_e_o_s os_header_fill os_lacing_returned os_lacing_packet os_lacing_fill os_lacing_storage os_body_returned os_body_fill os_body_storage; lia).
Qed.

Lemma fields_ok_set_blocks : forall (os : stream_st bptr) b bs l g ls,
stream_fields_ok os -> 0 <= bs < 2^63 -> int31 ls -> stream_fields_ok (set_blocks os b bs l g ls).
Proof.
intros os b bs l g ls FOK Hbs Hls.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ].
unfold stream_fields_ok, set_blocks in *; destruct os; cbn in *. unfold int31 in *. lia.
Qed.

Lemma pageno_range : forall hs : list byte, (22 <= length hs)%nat -> 0 <= ogg_page_pageno (ubytes hs) < 2^32.
Proof.
intros hs Hl. unfold ogg_page_pageno, le32_at.
pose proof (le_val_bound (zslice 18 4 (ubytes hs)) (bytes_ok_zslice _ _ _ (ubytes_ok hs))) as B.
rewrite (X10m.zlength_zslice 18 4) in B by (rewrite ?zlength_ubytes; lia). exact B.
Qed.

Lemma Forall_ztake : forall (P : Z -> Prop) n l, Forall P l -> Forall P (ztake n l).
Proof. intros P n l H. unfold ztake. rewrite <- (firstn_skipn (Z.to_nat n) l) in H. apply Forall_app in H. tauto. Qed.
Lemma Forall_zdrop : forall (P : Z -> Prop) n l, Forall P l -> Forall P (zdrop n l).
Proof. intros P n l H. unfold zdrop. rewrite <- (firstn_skipn (Z.to_nat n) l) in H. apply Forall_app in H. tauto. Qed.

Lemma wpre_app_junk : forall l ws junk, wpre l ws -> wpre l (ws ++ junk).
Proof.
intros l ws junk [H1 H2]. split.
- rewrite firstn_app. replace (length l - length ws)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. exact H1.
- rewrite app_length. lia.
Qed.

Lemma body_pre_ztake : forall body bytes k, body_pre body bytes -> 0 <= k -> k <= zlength body -> body_pre (ztake k body) bytes.
Proof.
intros body bytes k [H1 H2] Hk Hk2. unfold body_pre, ztake. unfold zlength in Hk2.
rewrite firstn_length_le by lia. split; [| lia].
rewrite <- H1. rewrite firstn_firstn. f_equal. lia.
Qed.

Lemma lacing_vals_ok_zdrop : forall n l, lacing_vals_ok l -> lacing_vals_ok (zdrop n l).
Proof. intros. apply Forall_zdrop. assumption. Qed.
Lemma lacing_vals_ok_ztake : forall n l, lacing_vals_ok l -> lacing_vals_ok (ztake n l).
Proof. intros. apply Forall_ztake. assumption. Qed.
Lemma lacing_vals_ok_app : forall l1 l2, lacing_vals_ok l1 -> lacing_vals_ok l2 -> lacing_vals_ok (l1 ++ l2).
Proof. intros. apply Forall_app. split; assumption. Qed.

Lemma lacing_vals_ok_returned : forall os : stream_st bptr, lacing_vals_ok (os_lacing os) -> lacing_vals_ok (os_lacing (pagein_returned os)).
Proof.
intros os H. unfold pagein_returned.
destruct (negb (os_body_returned os =? 0)); destruct (negb (os_lacing_returned _ =? 0)); cbn; try apply lacing_vals_ok_zdrop; destruct os; cbn in *; exact H.
Qed.

Lemma lacing_vals_ok_unroll : forall (os : stream_st bptr) pn, lacing_vals_ok (os_lacing os) -> lacing_vals_ok (os_lacing (pagein_unroll os pn)).
Proof.
intros os pn H. unfold pagein_unroll.
destruct (negb (pn =? os_pageno os)); [| exact H].
destruct (negb (os_pageno _ =? -1)); cbn.
- apply lacing_vals_ok_app; [apply lacing_vals_ok_ztake; destruct os; exact H|]. constructor; [cbv beta; lia| constructor].
- apply lacing_vals_ok_ztake. destruct os; exact H.
Qed.

Lemma fields_ok_unroll : forall (os : stream_st bptr) pn,
stream_fields_ok os -> stream_inv os ->
0 <= os_body_fill (pagein_unroll os pn) <= os_body_fill os -> os_lacing_fill os + 1 < 2^31 ->
stream_fields_ok (pagein_unroll os pn).
Proof.
intros os pn FOK sfH_; first [ sf_destruct 5%nat sfH_ as I1 I2 I3 I4 I5 | sf_fb; destruct sfH_ as (I1 & I2 & I3 & I4 & I5) ]; intros Hbf Hlf.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in *.
revert Hbf. unfold pagein_unroll.
destruct (negb (pn =? os_pageno os)); [| intros; exact FOK].
destruct (negb (os_pageno _ =? -1)); unfold stream_fields_ok, int31, set_lacing, set_body in *; destruct os; cbn in *; intros; (clear - Hbf Hlf I2 I1 FOK os_pageno os_serialno os_b_o_s os_e_o_s os_header_fill os_lacing_returned os_lacing_packet os_lacing_fill os_lacing_storage os_lacing os_body_returned os_body_fill os_body_storage F12 F11 F10 F9 F8 F7 F6 F4 F3 F2 F1; lia).
Qed.

Lemma segments_shape : forall (os : stream_st bptr) hdr bos segptr,
bytes_ok (lacing_of hdr) -> 0 <= segptr <= zlength (lacing_of hdr) -> os_lacing_packet os <= os_lacing_fill os ->
let os' := pagein_segments os hdr bos segptr in
os_body_data os' = os_body_data os /\ os_lacing_vals os' = os_lacing_vals os /\ os_granule_vals os' = os_granule_vals os /\
os_body_storage os' = os_body_storage os /\ os_lacing_storage os' = os_lacing_storage os /\
os_body_fill os' = os_body_fill os /\ os_body os' = os_body os /\ os_body_returned os' = os_body_returned os /\
os_lacing_returned os' = os_lacing_returned os /\ os_header_fill os' = os_header_fill os /\ os_b_o_s os' = os_b_o_s os /\
os_serialno os' = os_serialno os /\ os_packetno os' = os_packetno os /\ os_pageno os' = ogg_page_pageno hdr + 1 /\
(os_e_o_s os' = 1 \/ os_e_o_s os' = os_e_o_s os) /\
os_lacing_fill os' = os_lacing_fill os + (zlength (lacing_of hdr) - segptr) /\
os_lacing_packet os <= os_lacing_packet os' <= os_lacing_fill os'.
Proof.
intros os hdr bos segptr Hb Hseg Hpf. cbv zeta. unfold pagein_segments.
destruct (seg_loop (zdrop segptr (lacing_of hdr)) (negb (bos =? 0)) (os_lacing_fill os) (os_lacing_packet os) (-1))
as [[[[lac gran] f1] p1] sv] eqn:E.
apply seg_loop_spec in E; [| apply Forall_zdrop; exact Hb| exact Hpf].
rewrite zlength_zdrop in E by lia.
first [ sf_destruct 6%nat E as E1 E2 E3 E4 E5 E6 | sf_fb; destruct E as (E1 & E2 & E3 & E4 & E5 & E6) ].
destruct (negb (ogg_page_eos hdr =? 0)); destruct (negb (sv =? -1)); destruct (0 <? f1);
unfold set_lacing, set_tail; destruct os; cbn in *; repeat split; try reflexivity; try (clear - os_e_o_s E3 f1 segptr hdr os_lacing_fill E4 p1 os_lacing_packet; lia).
Qed.

Lemma fields_ok_segments : forall (os : stream_st bptr) hdr bos segptr,
stream_fields_ok os -> bytes_ok (lacing_of hdr) -> 0 <= segptr <= zlength (lacing_of hdr) ->
os_lacing_packet os <= os_lacing_fill os -> os_lacing_fill os + zlength (lacing_of hdr) < 2^31 ->
0 <= ogg_page_pageno hdr < 2^32 ->
stream_fields_ok (pagein_segments os hdr bos segptr).
Proof.
intros os hdr bos segptr FOK Hb Hseg Hpf Hlf Hpn.
pose proof (segments_shape os hdr bos segptr Hb Hseg Hpf) as SH. cbv zeta in SH.
first [ sf_destruct 17%nat SH as E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 | sf_fb; destruct SH as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17) ].
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ].
unfold stream_fields_ok, int31 in *. rewrite E4, E5, E6, E8, E9, E10, E11, E12, E14. repeat split; try lia.
Qed.

Lemma zlength_lacing_of : forall hs : list byte, length hs = (27 + Z.to_nat (znth (ubytes hs) 26))%nat -> 0 <= znth (ubytes hs) 26 ->
zlength (lacing_of (ubytes hs)) = znth (ubytes hs) 26.
Proof.
intros hs LENH Hn. unfold lacing_of. apply X10m.zlength_zslice; [lia| lia| rewrite zlength_ubytes; lia].
Qed.

Lemma fields_ok_body : forall (os : stream_st bptr) body sk n,
stream_fields_ok os -> 0 <= os_body_fill os + n < 2^63 -> stream_fields_ok (pagein_body os body sk n).
Proof.
intros os body sk n FOK Hn. pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ].
unfold stream_fields_ok, pagein_body, set_body in *; destruct os; cbn in *. unfold int31 in *. lia.
Qed.

Lemma unroll_body : forall (os : stream_st bptr) pn,
pagein_unroll os pn = os \/ os_body (pagein_unroll os pn) = ztake (os_body_fill (pagein_unroll os pn)) (os_body os).
Proof.
intros os pn. unfold pagein_unroll.
destruct (negb (pn =? os_pageno os)); [| left; reflexivity]. right.
destruct (negb (os_pageno _ =? -1)); destruct os; cbn; reflexivity.
Qed.

End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition body_pre (body : list Z) (bytes : list byte) : Prop :=
firstn (length body) (ubytes bytes) = body /\ (length body <= length bytes)%nat.

Lemma u32s_firstn : forall n ws, firstn (4 * n) (u32s ws) = u32s (firstn n ws).
Proof.
induction n as [|n IH]; intros ws; [cbn; reflexivity|].
destruct ws as [|w ws]; [cbn; destruct (4 * S n)%nat; reflexivity|]. cbn [u32s firstn].
rewrite firstn_app, length_le4, firstn_all2 by (rewrite length_le4; lia).
replace (4 * S n - 4)%nat with (4 * n)%nat by lia. rewrite IH. reflexivity.
Qed.
Lemma u32s_skipn : forall n ws, skipn (4 * n) (u32s ws) = u32s (skipn n ws).
Proof.
induction n as [|n IH]; intros ws; [cbn; reflexivity|].
destruct ws as [|w ws]; [cbn; destruct (4 * S n)%nat; reflexivity|]. cbn [u32s skipn].
rewrite skipn_app, length_le4, skipn_all2 by (rewrite length_le4; lia).
replace (4 * S n - 4)%nat with (4 * n)%nat by lia. rewrite IH. reflexivity.
Qed.
Lemma u64s_firstn : forall n ws, firstn (8 * n) (u64s ws) = u64s (firstn n ws).
Proof.
induction n as [|n IH]; intros ws; [cbn; reflexivity|].
destruct ws as [|w ws]; [cbn; destruct (8 * S n)%nat; reflexivity|]. cbn [u64s firstn].
rewrite firstn_app, length_le8, firstn_all2 by (rewrite length_le8; lia).
replace (8 * S n - 8)%nat with (8 * n)%nat by lia. rewrite IH. reflexivity.
Qed.
Lemma u64s_skipn : forall n ws, skipn (8 * n) (u64s ws) = u64s (skipn n ws).
Proof.
induction n as [|n IH]; intros ws; [cbn; reflexivity|].
destruct ws as [|w ws]; [cbn; destruct (8 * S n)%nat; reflexivity|]. cbn [u64s skipn].
rewrite skipn_app, length_le8, skipn_all2 by (rewrite length_le8; lia).
replace (8 * S n - 8)%nat with (8 * n)%nat by lia. rewrite IH. reflexivity.
Qed.

Lemma u32_move : forall ws k n, (k + n <= length ws)%nat ->
firstn (4 * n) (skipn (4 * k) (u32s ws)) ++ skipn (4 * n) (u32s ws) = u32s (firstn n (skipn k ws) ++ skipn n ws).
Proof. intros. rewrite u32s_skipn, u32s_firstn, u32s_skipn, u32s_app. reflexivity. Qed.
Lemma u64_move : forall ws k n, (k + n <= length ws)%nat ->
firstn (8 * n) (skipn (8 * k) (u64s ws)) ++ skipn (8 * n) (u64s ws) = u64s (firstn n (skipn k ws) ++ skipn n ws).
Proof. intros. rewrite u64s_skipn, u64s_firstn, u64s_skipn, u64s_app. reflexivity. Qed.

Lemma wpre_move : forall l ws k, wpre l ws -> (k <= length l)%nat ->
wpre (skipn k l) (firstn (length l - k) (skipn k ws) ++ skipn (length l - k) ws).
Proof.
intros l ws k [P L] Hk. unfold wpre. rewrite skipn_length, app_length, firstn_length_le, skipn_length by (rewrite skipn_length; lia).
split; [|lia]. rewrite firstn_app, firstn_firstn, Nat.min_id, firstn_length_le, Nat.sub_diag, firstn_O, app_nil_r by (rewrite skipn_length; lia).
rewrite <- skipn_map, <- P, skipn_firstn_comm. reflexivity.
Qed.

Definition ret_body (os : stream_st bptr) : stream_st bptr :=
if negb (os_body_returned os =? 0) then
set_body os (ztake (os_body_fill os - os_body_returned os) (zdrop (os_body_returned os) (os_body os)))
(os_body_storage os) (os_body_fill os - os_body_returned os) 0
else os.
Definition ret_lacing (os : stream_st bptr) : stream_st bptr :=
if negb (os_lacing_returned os =? 0) then
set_lacing os (zdrop (os_lacing_returned os) (os_lacing os)) (zdrop (os_lacing_returned os) (os_granules os)) (os_lacing_storage os)
(os_lacing_fill os - os_lacing_returned os) (os_lacing_packet os - os_lacing_returned os) 0
else os.
Lemma pagein_returned_eq : forall os : stream_st bptr, pagein_returned os = ret_lacing (ret_body os).
Proof.
intros os. unfold pagein_returned, ret_lacing, ret_body.
destruct (negb (os_body_returned os =? 0)); reflexivity.
Qed.

Lemma fields_ok_returned : forall os : stream_st bptr,
stream_fields_ok os -> stream_inv os -> os_body_returned os <= os_body_fill os ->
stream_fields_ok (pagein_returned os).
Proof.
intros os FOK sfH_; first [ sf_destruct 5%nat sfH_ as I1 I2 I3 I4 I5 | sf_fb; destruct sfH_ as (I1 & I2 & I3 & I4 & I5) ]; intros Hbr.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in *.
unfold pagein_returned.
destruct (negb (os_body_returned os =? 0)); destruct (negb (os_lacing_returned _ =? 0));
unfold stream_fields_ok, int31, set_lacing, set_body in *; destruct os; cbn in *; (clear - F7 F6 F5 F3 F2 Hbr I2 I1 FOK os_pageno os_serialno os_b_o_s os_e_o_s os_header_fill os_lacing_returned os_lacing_packet os_lacing_fill os_lacing_storage os_body_returned os_body_fill os_body_storage; lia).
Qed.

Lemma fields_ok_set_blocks : forall (os : stream_st bptr) b bs l g ls,
stream_fields_ok os -> 0 <= bs < 2^63 -> int31 ls -> stream_fields_ok (set_blocks os b bs l g ls).
Proof.
intros os b bs l g ls FOK Hbs Hls.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ].
unfold stream_fields_ok, set_blocks in *; destruct os; cbn in *. unfold int31 in *. lia.
Qed.

Lemma pageno_range : forall hs : list byte, (22 <= length hs)%nat -> 0 <= ogg_page_pageno (ubytes hs) < 2^32.
Proof.
intros hs Hl. unfold ogg_page_pageno, le32_at.
pose proof (le_val_bound (zslice 18 4 (ubytes hs)) (bytes_ok_zslice _ _ _ (ubytes_ok hs))) as B.
rewrite (X0a0.zlength_zslice 18 4) in B by (rewrite ?zlength_ubytes; lia). exact B.
Qed.

Lemma Forall_ztake : forall (P : Z -> Prop) n l, Forall P l -> Forall P (ztake n l).
Proof. intros P n l H. unfold ztake. rewrite <- (firstn_skipn (Z.to_nat n) l) in H. apply Forall_app in H. tauto. Qed.
Lemma Forall_zdrop : forall (P : Z -> Prop) n l, Forall P l -> Forall P (zdrop n l).
Proof. intros P n l H. unfold zdrop. rewrite <- (firstn_skipn (Z.to_nat n) l) in H. apply Forall_app in H. tauto. Qed.

Lemma wpre_app_junk : forall l ws junk, wpre l ws -> wpre l (ws ++ junk).
Proof.
intros l ws junk [H1 H2]. split.
- rewrite firstn_app. replace (length l - length ws)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. exact H1.
- rewrite app_length. lia.
Qed.

Lemma body_pre_ztake : forall body bytes k, body_pre body bytes -> 0 <= k -> k <= zlength body -> body_pre (ztake k body) bytes.
Proof.
intros body bytes k [H1 H2] Hk Hk2. unfold body_pre, ztake. unfold zlength in Hk2.
rewrite firstn_length_le by lia. split; [| lia].
rewrite <- H1. rewrite firstn_firstn. f_equal. lia.
Qed.

Lemma lacing_vals_ok_zdrop : forall n l, lacing_vals_ok l -> lacing_vals_ok (zdrop n l).
Proof. intros. apply Forall_zdrop. assumption. Qed.
Lemma lacing_vals_ok_ztake : forall n l, lacing_vals_ok l -> lacing_vals_ok (ztake n l).
Proof. intros. apply Forall_ztake. assumption. Qed.
Lemma lacing_vals_ok_app : forall l1 l2, lacing_vals_ok l1 -> lacing_vals_ok l2 -> lacing_vals_ok (l1 ++ l2).
Proof. intros. apply Forall_app. split; assumption. Qed.

Lemma lacing_vals_ok_returned : forall os : stream_st bptr, lacing_vals_ok (os_lacing os) -> lacing_vals_ok (os_lacing (pagein_returned os)).
Proof.
intros os H. unfold pagein_returned.
destruct (negb (os_body_returned os =? 0)); destruct (negb (os_lacing_returned _ =? 0)); cbn; try apply lacing_vals_ok_zdrop; destruct os; cbn in *; exact H.
Qed.

Lemma lacing_vals_ok_unroll : forall (os : stream_st bptr) pn, lacing_vals_ok (os_lacing os) -> lacing_vals_ok (os_lacing (pagein_unroll os pn)).
Proof.
intros os pn H. unfold pagein_unroll.
destruct (negb (pn =? os_pageno os)); [| exact H].
destruct (negb (os_pageno _ =? -1)); cbn.
- apply lacing_vals_ok_app; [apply lacing_vals_ok_ztake; destruct os; exact H|]. constructor; [cbv beta; lia| constructor].
- apply lacing_vals_ok_ztake. destruct os; exact H.
Qed.

Lemma fields_ok_unroll : forall (os : stream_st bptr) pn,
stream_fields_ok os -> stream_inv os ->
0 <= os_body_fill (pagein_unroll os pn) <= os_body_fill os -> os_lacing_fill os + 1 < 2^31 ->
stream_fields_ok (pagein_unroll os pn).
Proof.
intros os pn FOK sfH_; first [ sf_destruct 5%nat sfH_ as I1 I2 I3 I4 I5 | sf_fb; destruct sfH_ as (I1 & I2 & I3 & I4 & I5) ]; intros Hbf Hlf.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in *.
revert Hbf. unfold pagein_unroll.
destruct (negb (pn =? os_pageno os)); [| intros; exact FOK].
destruct (negb (os_pageno _ =? -1)); unfold stream_fields_ok, int31, set_lacing, set_body in *; destruct os; cbn in *; intros; (clear - Hbf Hlf I2 I1 FOK os_pageno os_serialno os_b_o_s os_e_o_s os_header_fill os_lacing_returned os_lacing_packet os_lacing_fill os_lacing_storage os_lacing os_body_returned os_body_fill os_body_storage F12 F11 F10 F9 F8 F7 F6 F4 F3 F2 F1; lia).
Qed.

Lemma segments_shape : forall (os : stream_st bptr) hdr bos segptr,
bytes_ok (lacing_of hdr) -> 0 <= segptr <= zlength (lacing_of hdr) -> os_lacing_packet os <= os_lacing_fill os ->
let os' := pagein_segments os hdr bos segptr in
os_body_data os' = os_body_data os /\ os_lacing_vals os' = os_lacing_vals os /\ os_granule_vals os' = os_granule_vals os /\
os_body_storage os' = os_body_storage os /\ os_lacing_storage os' = os_lacing_storage os /\
os_body_fill os' = os_body_fill os /\ os_body os' = os_body os /\ os_body_returned os' = os_body_returned os /\
os_lacing_returned os' = os_lacing_returned os /\ os_header_fill os' = os_header_fill os /\ os_b_o_s os' = os_b_o_s os /\
os_serialno os' = os_serialno os /\ os_packetno os' = os_packetno os /\ os_pageno os' = ogg_page_pageno hdr + 1 /\
(os_e_o_s os' = 1 \/ os_e_o_s os' = os_e_o_s os) /\
os_lacing_fill os' = os_lacing_fill os + (zlength (lacing_of hdr) - segptr) /\
os_lacing_packet os <= os_lacing_packet os' <= os_lacing_fill os'.
Proof.
intros os hdr bos segptr Hb Hseg Hpf. cbv zeta. unfold pagein_segments.
destruct (seg_loop (zdrop segptr (lacing_of hdr)) (negb (bos =? 0)) (os_lacing_fill os) (os_lacing_packet os) (-1))
as [[[[lac gran] f1] p1] sv] eqn:E.
apply seg_loop_spec in E; [| apply Forall_zdrop; exact Hb| exact Hpf].
rewrite zlength_zdrop in E by lia.
first [ sf_destruct 6%nat E as E1 E2 E3 E4 E5 E6 | sf_fb; destruct E as (E1 & E2 & E3 & E4 & E5 & E6) ].
destruct (negb (ogg_page_eos hdr =? 0)); destruct (negb (sv =? -1)); destruct (0 <? f1);
unfold set_lacing, set_tail; destruct os; cbn in *; repeat split; try reflexivity; try (clear - os_e_o_s E3 f1 segptr hdr os_lacing_fill E4 p1 os_lacing_packet; lia).
Qed.

Lemma fields_ok_segments : forall (os : stream_st bptr) hdr bos segptr,
stream_fields_ok os -> bytes_ok (lacing_of hdr) -> 0 <= segptr <= zlength (lacing_of hdr) ->
os_lacing_packet os <= os_lacing_fill os -> os_lacing_fill os + zlength (lacing_of hdr) < 2^31 ->
0 <= ogg_page_pageno hdr < 2^32 ->
stream_fields_ok (pagein_segments os hdr bos segptr).
Proof.
intros os hdr bos segptr FOK Hb Hseg Hpf Hlf Hpn.
pose proof (segments_shape os hdr bos segptr Hb Hseg Hpf) as SH. cbv zeta in SH.
first [ sf_destruct 17%nat SH as E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 | sf_fb; destruct SH as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17) ].
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ].
unfold stream_fields_ok, int31 in *. rewrite E4, E5, E6, E8, E9, E10, E11, E12, E14. repeat split; try lia.
Qed.

Lemma zlength_lacing_of : forall hs : list byte, length hs = (27 + Z.to_nat (znth (ubytes hs) 26))%nat -> 0 <= znth (ubytes hs) 26 ->
zlength (lacing_of (ubytes hs)) = znth (ubytes hs) 26.
Proof.
intros hs LENH Hn. unfold lacing_of. apply X0a0.zlength_zslice; [lia| lia| rewrite zlength_ubytes; lia].
Qed.

Lemma fields_ok_body : forall (os : stream_st bptr) body sk n,
stream_fields_ok os -> 0 <= os_body_fill os + n < 2^63 -> stream_fields_ok (pagein_body os body sk n).
Proof.
intros os body sk n FOK Hn. pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ].
unfold stream_fields_ok, pagein_body, set_body in *; destruct os; cbn in *. unfold int31 in *. lia.
Qed.

Lemma unroll_body : forall (os : stream_st bptr) pn,
pagein_unroll os pn = os \/ os_body (pagein_unroll os pn) = ztake (os_body_fill (pagein_unroll os pn)) (os_body os).
Proof.
intros os pn. unfold pagein_unroll.
destruct (negb (pn =? os_pageno os)); [| left; reflexivity]. right.
destruct (negb (os_pageno _ =? -1)); destruct os; cbn; reflexivity.
Qed.

