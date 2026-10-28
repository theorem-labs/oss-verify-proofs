(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0om X0qn X0px X0qc X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fd X1fe X1m2 X1m3 X1m5 X1m6 X1ik X1ii X1ij X1iu X1it X1im X1ip X1iq X1ix X1iy X1iz X1j0 X1j1.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qv X1qx X1r3 X1r4 X1qz X1r0 X1nv X1r1.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma cmod_drop_iv : forall lo' hi W LB SP m m',
cmod ((lo', hi) :: W) LB SP m m' -> hi <= SP -> (hi <= 0x3b000 \/ 0x6e000 <= lo') ->
(forall b, In b LB -> blk_addr b + blk_size b <= lo' \/ hi <= blk_addr b) -> cmod W LB SP m m'.
Proof.
intros lo' hi W LB SP m m' H Hhi Hlo HB a Ha Hc Ho. apply H; [exact Ha| exact Hc|]. cbn. split; [| exact Ho].
destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia|].
destruct (HB b Hb); unfold in_range in Hr; lia.
Qed.

Definition memcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(D S n : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(D, D + n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' D [CB (Z.to_nat n) src]
/\ bytes_at rsegs m' S src.
Lemma memcpy_callZ : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (D S n : Z) (src junk : list byte),
bytes_at rsegs m S src -> length src = Z.to_nat n ->
rw_cells rsegs m D [CB (Z.to_nat n) junk] ->
0 <= D -> D + n < 2^64 -> 0 <= S -> S + n < 2^64 -> 0 <= n ->
(S + n <= D \/ D + n <= S) ->
mem_inv rsegs m ->
evt rsegs (memcpy_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S n src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x39c5c) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros SRC LEN DST HD HD2 HS HS2 Hn SEP MI.
assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
eapply evt_mono.
{ eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n)); rewrite ?ED, ?ES, ?EN; eauto. }
intros ms' P. unfold memcpy_post in P. rewrite !ED, !ES, !EN in P. exact P.
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

Lemma frame_merge40 : forall m a j0 (w1 w2 w3 w4 : word) rest,
rw_cells rsegs m a ([CB 8 j0; C8 w1; C8 w2; C8 w3; C8 w4] ++ rest) ->
exists j, rw_cells rsegs m a (CB 40 j :: rest).
Proof.
intros m a j0 w1 w2 w3 w4 rest H. eexists.
pose proof (rw_cells_merge rsegs m a [] [CB 8 j0; C8 w1; C8 w2; C8 w3; C8 w4] rest H) as H'.
cbn [cells_size csize Nat.add app] in H'. exact H'.
Qed.

Lemma s32_range : forall x, -2^31 <= s32 x < 2^31.
Proof. intros x. unfold s32. pose proof (Z.mod_pos_bound (x + 2^31) (2^32) ltac:(lia)). lia. Qed.

Lemma pageno_range : forall hs : list byte, (22 <= length hs)%nat -> 0 <= ogg_page_pageno (ubytes hs) < 2^32.
Proof.
intros hs Hl. unfold ogg_page_pageno, le32_at.
pose proof (le_val_bound (zslice 18 4 (ubytes hs)) (bytes_ok_zslice _ _ _ (ubytes_ok hs))) as B.
rewrite (X1iy.zlength_zslice 18 4) in B by (rewrite ?zlength_ubytes; lia). exact B.
Qed.

Lemma land64_inj_signed : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
Z.land a 18446744073709551615 = Z.land b 18446744073709551615 -> a = b.
Proof.
intros a b Ha Hb E. rewrite !land_ones64 in E.
assert (Ea : a = a mod 2^64 - (if a <? 0 then 2^64 else 0)).
{ destruct (Z.ltb_spec a 0).
- rewrite <- (Z.mod_add a 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia. }
assert (Eb : b = b mod 2^64 - (if b <? 0 then 2^64 else 0)).
{ destruct (Z.ltb_spec b 0).
- rewrite <- (Z.mod_add b 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia. }
pose proof (Z.mod_pos_bound a (2^64) ltac:(lia)). pose proof (Z.mod_pos_bound b (2^64) ltac:(lia)).
destruct (Z.ltb_spec a 0); destruct (Z.ltb_spec b 0); lia.
Qed.

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
intros hs LENH Hn. unfold lacing_of. apply X1iy.zlength_zslice; [lia| lia| rewrite zlength_ubytes; lia].
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

Lemma body_split3 : forall m Bd' L0 (f n r : nat),
rw_cells rsegs m Bd' [CB (f + n + r)%nat L0] ->
rw_cells rsegs m Bd' [CB f (firstn f L0)] /\
rw_cells rsegs m (Bd' + Z.of_nat f) [CB n (firstn n (skipn f L0))] /\
rw_cells rsegs m (Bd' + Z.of_nat f + Z.of_nat n) [CB r (firstn r (skipn n (skipn f L0)))].
Proof.
intros m Bd' L0 f n r H.
pose proof (rw_cells_split_CB rsegs m Bd' [] (f + n + r)%nat L0 [] [f; n; r] H ltac:(cbn; lia)) as X.
cbn [mk_CB_cells app] in X.
change ([CB f (firstn f L0); CB n (firstn n (skipn f L0)); CB r (firstn r (skipn n (skipn f L0)))])
with ([CB f (firstn f L0)] ++ ([CB n (firstn n (skipn f L0))] ++ [CB r (firstn r (skipn n (skipn f L0)))])) in X.
apply rw_cells_app in X. destruct X as [X1 X']. cbn [cells_size csize Nat.add] in X'.
apply rw_cells_app in X'. destruct X' as [X2 X3]. cbn [cells_size csize Nat.add] in X3.
rewrite Nat.add_0_r in X2, X3.
split; [exact X1|]. split; [exact X2|].
replace (Bd' + Z.of_nat f + Z.of_nat n) with (Bd' + Z.of_nat f + Z.of_nat (n + 0)) by lia. exact X3.
Qed.

Lemma body_merge3 : forall m Bd' (a b c : list byte) (f n r : nat),
rw_cells rsegs m Bd' [CB f a] -> rw_cells rsegs m (Bd' + Z.of_nat f) [CB n b] ->
rw_cells rsegs m (Bd' + Z.of_nat f + Z.of_nat n) [CB r c] ->
u8arr rsegs m Bd' (a ++ b ++ c) /\ length (a ++ b ++ c) = (f + n + r)%nat.
Proof.
intros m Bd' a b c f n r X1 X2 X3.
pose proof X1 as [[W1 _] _]. pose proof X2 as [[W2 _] _]. pose proof X3 as [[W3 _] _]. cbn in W1, W2, W3.
assert (X23 : rw_cells rsegs m (Bd' + Z.of_nat f) ([CB n b] ++ [CB r c])).
{ apply rw_cells_join; [exact X2|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact X3. }
assert (X : rw_cells rsegs m Bd' ([CB f a] ++ [CB n b] ++ [CB r c])).
{ apply rw_cells_join; [exact X1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact X23. }
pose proof (rw_cells_merge rsegs m Bd' [] ([CB f a] ++ [CB n b] ++ [CB r c]) [] ltac:(rewrite app_nil_r; exact X)) as Y.
cbn [cells_size csize cells_bytes cbytes Nat.add app] in Y. rewrite !app_nil_r in Y.
split.
- apply u8arr_of_rw_cells in Y. rewrite <- ?app_assoc in Y. exact Y.
- rewrite !app_length. lia.
Qed.

Section PAGEIN.
Context {RCEIL : RunCeiling}.
Variable rhdr_known : PState -> bptr -> Prop.
Hypothesis rhdr_known_indep : forall s s' p, rhdr_known s p -> rhdr_known s' p.
Hypothesis HR : ogg_realloc_stmt rhdr_known.
Hypothesis HF : rfree_stmt.

#[using="Type"] Lemma pi_epilogue : forall (lo : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) (j : list byte) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
rw_cells rsegs m (bv_unsigned sp + -144) [CB 40 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs m lo (bv_unsigned sp + -144) -> lo + 144 <= bv_unsigned sp -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x18 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs)
/\ stk rsegs m lo (bv_unsigned sp))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x30bf8) fc None m (seg_rom rsegs)).
Proof.
intros until x31. intros FR ST LOSP MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.

zstep.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
release_frame FR ST (bv_unsigned sp).
zstep. zstep.
apply evt_done. sf_eexists 14%nat. split; [reflexivity| exact ST].
Qed.

Definition stream_arrays (m : mem) (os : stream_st bptr) (Bd L Gv : Z) (bodybytes : list byte) (lws gws : list word) : Prop :=
u8arr rsegs m Bd bodybytes /\ Z.of_nat (length bodybytes) = os_body_storage os /\ body_pre (os_body os) bodybytes /\
u32arr rsegs m L lws /\ wpre (os_lacing os) lws /\ Z.of_nat (length lws) = os_lacing_storage os /\
u64arr rsegs m Gv gws /\ Z.of_nat (length gws) = os_lacing_storage os.

Definition pagein_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (pb pl pg : bptr) (A G Dsy lo B : Z) (og : page) (shdr hs bs : list byte) (m : mem)
(r : Z * stream_st bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (LB' : list block),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (fst r)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ RHEAP s' LB' m'
/\ (forall b, In b LB -> blk_id b <> pb -> blk_id b <> pl -> blk_id b <> pg -> In b LB')
/\ cmod [(A, A + 408)] (lb_remove pg (lb_remove pl (lb_remove pb LB))) (bv_unsigned sp) m m'
/\ rw_cells rsegs m' G (page_cells Dsy og) /\ bytes_at rsegs m' (Dsy + pg_hdr og) hs
/\ bytes_at rsegs m' (Dsy + pg_hdr og + pg_header_len og) bs
/\ (fst r = 0 \/ fst r = -1)
/\ ( (exists (Bd' L' Gv' : Z) (pb' pl' pg' : bptr) bodybytes' lws' gws',
os_body_data (snd r) = Some pb' /\ os_lacing_vals (snd r) = Some pl' /\ os_granule_vals (snd r) = Some pg'
/\ In (pb', Bd', os_body_storage (snd r)) LB' /\ In (pl', L', os_lacing_storage (snd r) * 4) LB'
/\ In (pg', Gv', os_lacing_storage (snd r) * 8) LB'
/\ rhdr_known s' pb' /\ rhdr_known s' pl' /\ rhdr_known s' pg'
/\ stream_blocks LB' (snd r) Bd' L' Gv' /\ stream_fields_ok (snd r)
/\ rw_cells rsegs m' A (stream_cells Bd' L' Gv' shdr (snd r))
/\ stream_arrays m' (snd r) Bd' L' Gv' bodybytes' lws' gws'
/\ Permutation LB' ((pb', Bd', os_body_storage (snd r)) :: (pl', L', os_lacing_storage (snd r) * 4)
:: (pg', Gv', os_lacing_storage (snd r) * 8)
:: lb_remove pg (lb_remove pl (lb_remove pb LB))))
\/ (snd r = stream_zero /\ rw_cells rsegs m' A (stream_cells 0 0 0 zero_hdr stream_zero)
/\ Permutation LB' (lb_remove pg (lb_remove pl (lb_remove pb LB)))) ).

Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
Variables (s : PState) (LB : list block) (os : stream_st bptr) (pb pl pg psy : bptr).
Variables (A G Dsy nsy Bd L Gv lo B : Z) (og : page) (shdr hs bs bodybytes : list byte) (lws gws : list word) (errv : word).

Hypothesis HP : RHEAP s LB m.
Hypothesis SB : stream_blocks LB os Bd L Gv.
Hypothesis Hpb : os_body_data os = Some pb.
Hypothesis Hpl : os_lacing_vals os = Some pl.
Hypothesis Hpg : os_granule_vals os = Some pg.
Hypothesis HINb : In (pb, Bd, os_body_storage os) LB.
Hypothesis HINl : In (pl, L, os_lacing_storage os * 4) LB.
Hypothesis HINg : In (pg, Gv, os_lacing_storage os * 8) LB.
Hypothesis HKb : rhdr_known s pb.
Hypothesis HKl : rhdr_known s pl.
Hypothesis HKg : rhdr_known s pg.
Hypothesis HINsy : In (psy, Dsy, nsy) LB.
Hypothesis NEb : psy <> pb.
Hypothesis NEl : psy <> pl.
Hypothesis NEg : psy <> pg.

Hypothesis OS : rw_cells rsegs m A (stream_cells Bd L Gv shdr os).
Hypothesis HL : length shdr = 284%nat.
Hypothesis ARR : stream_arrays m os Bd L Gv bodybytes lws gws.
Hypothesis FOK : stream_fields_ok os.
Hypothesis SINV : stream_inv os.
Hypothesis BINV : body_inv os.
Hypothesis LOK : lacing_vals_ok (os_lacing os).

Hypothesis OG : rw_cells rsegs m G (page_cells Dsy og).
Hypothesis HS : bytes_at rsegs m (Dsy + pg_hdr og) hs.
Hypothesis HBS : bytes_at rsegs m (Dsy + pg_hdr og + pg_header_len og) bs.
Hypothesis LENH : length hs = (27 + Z.to_nat (znth (ubytes hs) 26))%nat.
Hypothesis HLEN : Z.of_nat (length hs) = pg_header_len og.
Hypothesis BSLEN : Z.of_nat (length bs) = pg_body_len og.
Hypothesis Hsum : zsum (lacing_of (ubytes hs)) <= pg_body_len og.
Hypothesis Hpg0 : 0 <= pg_hdr og.
Hypothesis PGIN : pg_hdr og + pg_header_len og + pg_body_len og <= nsy.

Hypothesis HboundL : (os_lacing_storage os + znth (ubytes hs) 26 + 33) * 8 < MMAP_THRESHOLD.
Hypothesis HboundB : os_body_storage os + pg_body_len og + 1024 < MMAP_THRESHOLD.
Hypothesis HBIG : 1024 <= os_lacing_storage os.

Hypothesis AUX : rauxv_ok m B.
Hypothesis SPB : bv_unsigned sp <= B.
Hypothesis SPA : bv_unsigned sp <= A.
Hypothesis AB : A + 408 <= B.
Hypothesis SPG : bv_unsigned sp <= G.
Hypothesis SEP_AG : A + 408 <= G \/ G + 32 <= A.
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 176 - OGG_REALLOC_STACK.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
#[local] Set Default Proof Using "HP SB Hpb Hpl Hpg HINb HINl HINg HKb HKl HKg HINsy NEb NEl NEg OS HL ARR FOK SINV BINV LOK OG HS HBS LENH HLEN BSLEN Hsum Hpg0 PGIN HboundL HboundB HBIG AUX SPB SPA AB SPG SEP_AG ST CEIL LO ERR MI TP rhdr_known_indep HR HF".

Local Notation hdr := (ubytes hs).
Local Notation nseg := (znth (ubytes hs) 26).
Local Notation H := (Dsy + pg_hdr og).
Local Notation POST := (pagein_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB pb pl pg A G Dsy lo B og shdr hs bs m).
Local Notation kept := (lb_remove pg (lb_remove pl (lb_remove pb LB))).
Local Notation os1 := (pagein_returned os).
Local Notation W1 := [(bv_unsigned sp - 144, bv_unsigned sp); (A, A + 408); (Bd, Bd + os_body_storage os);
(L, L + 4 * os_lacing_storage os); (Gv, Gv + 8 * os_lacing_storage os)].
Local Notation FRAME mm loc := (rw_cells rsegs mm (bv_unsigned sp + -144)
(loc ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
Local Notation LOC j0 := [CB 8 j0; C8 (wz (ogg_page_granulepos hdr)); C8 (Z_to_bv 64 (znth hdr 18)); C8 (Z_to_bv 64 (znth hdr 21)); C8 (Z_to_bv 64 (znth hdr 5))].

Definition facts : Prop :=
0 < Bd /\ 0 < L /\ 0 < Gv /\ 0 < Dsy /\ 0 < A /\
Bd + os_body_storage os <= lo /\ L + os_lacing_storage os * 4 <= lo /\ Gv + os_lacing_storage os * 8 <= lo /\ Dsy + nsy <= lo /\
Bd + os_body_storage os <= 2^47 /\ L + os_lacing_storage os * 4 <= 2^47 /\ Gv + os_lacing_storage os * 8 <= 2^47 /\ Dsy + nsy <= 2^47 /\
0 <= os_body_storage os /\ 0 <= os_lacing_storage os /\ 0 <= nsy /\
lo + 8432 <= bv_unsigned sp /\ bv_unsigned sp <= A /\ A + 408 <= B /\ bv_unsigned sp < 2^64 /\
0 <= nseg < 256 /\ (22 <= length hs)%nat /\
-2^31 <= ogg_page_serialno hdr < 2^31 /\ 0 <= ogg_page_pageno hdr < 2^32 /\ 0 <= znth hdr 4 < 256 /\
os_body_returned os <= os_body_fill os /\ Z.of_nat (length (os_lacing os)) = os_lacing_fill os /\
0 <= os_lacing_returned os <= os_lacing_packet os /\ os_lacing_packet os <= os_lacing_fill os /\ 0 <= os_body_returned os /\
os_lacing_fill os <= os_lacing_storage os /\ os_body_fill os <= os_body_storage os /\
Z.of_nat (length lws) = os_lacing_storage os /\ Z.of_nat (length gws) = os_lacing_storage os /\
Z.of_nat (length bodybytes) = os_body_storage os /\
Z.of_nat (length (os_body os)) = os_body_fill os /\ (length (os_lacing os) <= length lws)%nat /\ (length (os_body os) <= length bodybytes)%nat.

Lemma facts_proof : facts.
Proof.
pose proof ARR as sfP_; first [ sf_destruct 8%nat sfP_ as BODY BLEN BPRE LAC LPRE LLEN GRA GLEN | sf_fb; destruct sfP_ as (BODY & BLEN & BPRE & LAC & LPRE & LLEN & GRA & GLEN) ].
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. pose proof LO as LO'. unfold OGG_REALLOC_STACK in LO'.
pose proof SINV as sfP_; first [ sf_destruct 5%nat sfP_ as I1 I2 I3 I4 I5 | sf_fb; destruct sfP_ as (I1 & I2 & I3 & I4 & I5) ]. pose proof BINV as sfP_; first [ sf_destruct 4%nat sfP_ as Bi1 Bi2 Bi3 Bi4 | sf_fb; destruct sfP_ as (Bi1 & Bi2 & Bi3 & Bi4) ].
pose proof (body_inv_returned_le_fill os BINV) as Hbrf.
pose proof (RHEAP_block_range_proof _ _ _ _ HP HINb) as BRb. cbn [blk_addr blk_size fst snd] in BRb.
pose proof (RHEAP_block_range_proof _ _ _ _ HP HINl) as BRl. cbn [blk_addr blk_size fst snd] in BRl.
pose proof (RHEAP_block_range_proof _ _ _ _ HP HINg) as BRg. cbn [blk_addr blk_size fst snd] in BRg.
pose proof (RHEAP_block_range_proof _ _ _ _ HP HINsy) as BRs. cbn [blk_addr blk_size fst snd] in BRs.
unfold rblock_range, alloc_ceiling in BRb, BRl, BRg, BRs.
pose proof (wpre_length _ _ LPRE) as LL. pose proof BPRE as [BP1 BP2]. unfold zlength in I3, I4, Bi1.
assert (Hnseg : 0 <= nseg < 256) by (rewrite znth_ubytes by lia; apply byte_range).
pose proof (s32_range (le32_at hdr 14)) as SERR. change (s32 (le32_at hdr 14)) with (ogg_page_serialno hdr) in SERR.
pose proof (pageno_range hs ltac:(lia)) as PNR.
pose proof (byte_range (nth (Z.to_nat 4) hs (Z_to_bv 8 0))) as H4. rewrite <- (znth_ubytes hs 4) in H4 by lia.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
unfold facts. repeat split; try (clear - BRb Bd os RCEIL BRl L BRg Gv BRs nsy Dsy SPR BP2 LL LO' CEIL' SPG SPA LENH HL gws lws bodybytes bs hs shdr lo G A sp GLEN AB B Hnseg SERR PNR H4 Hbrf I3 I1 I2 Bi2 LLEN Bi1 BLEN; lia).
Qed.

Lemma sep_BL : Bd + os_body_storage os <= L \/ L + os_lacing_storage os * 4 <= Bd.
Proof. pose proof SB as sfP_; first [ sf_destruct 6%nat sfP_ as _ _ _ D12 _ _ | sf_fb; destruct sfP_ as (_ & _ & _ & D12 & _ & _) ]. exact (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP HINb HINl ltac:(cbn; eapply D12; eassumption)). Qed.
Lemma sep_BG : Bd + os_body_storage os <= Gv \/ Gv + os_lacing_storage os * 8 <= Bd.
Proof. pose proof SB as sfP_; first [ sf_destruct 6%nat sfP_ as _ _ _ _ D13 _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & D13 & _) ]. exact (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP HINb HINg ltac:(cbn; eapply D13; eassumption)). Qed.
Lemma sep_LG : L + os_lacing_storage os * 4 <= Gv \/ Gv + os_lacing_storage os * 8 <= L.
Proof. pose proof SB as sfP_; first [ sf_destruct 6%nat sfP_ as _ _ _ _ _ D23 | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & D23) ]. exact (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP HINl HINg ltac:(cbn; eapply D23; eassumption)). Qed.
Lemma sep_SB : Dsy + nsy <= Bd \/ Bd + os_body_storage os <= Dsy.
Proof. exact (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP HINsy HINb ltac:(cbn; exact NEb)). Qed.
Lemma sep_SL : Dsy + nsy <= L \/ L + os_lacing_storage os * 4 <= Dsy.
Proof. exact (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP HINsy HINl ltac:(cbn; exact NEl)). Qed.
Lemma sep_SG : Dsy + nsy <= Gv \/ Gv + os_lacing_storage os * 8 <= Dsy.
Proof. exact (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP HINsy HINg ltac:(cbn; exact NEg)). Qed.
Lemma statics_B : Bd + os_body_storage os <= 0x10000 \/ 0x6e000 <= Bd.
Proof. pose proof (RHEAP_block_range_proof _ _ _ _ HP HINb) as BR. cbn [blk_addr blk_size fst snd] in BR. unfold rblock_range in BR. tauto. Qed.
Lemma statics_L : L + os_lacing_storage os * 4 <= 0x10000 \/ 0x6e000 <= L.
Proof. pose proof (RHEAP_block_range_proof _ _ _ _ HP HINl) as BR. cbn [blk_addr blk_size fst snd] in BR. unfold rblock_range in BR. tauto. Qed.
Lemma statics_G : Gv + os_lacing_storage os * 8 <= 0x10000 \/ 0x6e000 <= Gv.
Proof. pose proof (RHEAP_block_range_proof _ _ _ _ HP HINg) as BR. cbn [blk_addr blk_size fst snd] in BR. unfold rblock_range in BR. tauto. Qed.

Lemma kept_apart : forall b p X n, In (p, X, n) LB -> In b kept -> blk_id b <> p ->
blk_addr b + blk_size b <= X \/ X + n <= blk_addr b.
Proof.
intros b p X n HIN Hb NE. do 3 apply lb_remove_sub in Hb.
exact (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP Hb HIN NE).
Qed.
Lemma kept_ids : forall b, In b kept -> In b LB /\ blk_id b <> pb /\ blk_id b <> pl /\ blk_id b <> pg.
Proof.
intros b Hb. pose proof (lb_remove_neq _ _ _ Hb) as N1. apply lb_remove_sub in Hb.
pose proof (lb_remove_neq _ _ _ Hb) as N2. apply lb_remove_sub in Hb.
pose proof (lb_remove_neq _ _ _ Hb) as N3. apply lb_remove_sub in Hb. auto.
Qed.

Lemma cmod_phase1 : forall m', munch W1 m m' -> wmono rsegs m m' -> cmod [(A, A + 408)] kept (bv_unsigned sp) m m'.
Proof.
intros m' MU WM. pose proof facts_proof as FA. unfold facts in FA. pose proof CEIL as CE. unfold alloc_ceiling in CE.
pose proof statics_B as XB. pose proof statics_L as XL. pose proof statics_G as XG.
pose proof (cmod_of_munch W1 kept (bv_unsigned sp) m m' MU WM) as C.
apply (cmod_weaken _ [(Bd, Bd + os_body_storage os); (L, L + 4 * os_lacing_storage os); (Gv, Gv + 8 * os_lacing_storage os);
(bv_unsigned sp - 144, bv_unsigned sp); (A, A + 408)] kept kept (bv_unsigned sp) (bv_unsigned sp)) in C;
[| lia| auto| unfold sub_fp; cbn [outside]; intros; lia].
apply cmod_drop_iv in C; [| lia| lia| intros b Hb; first [ pose proof (kept_ids b Hb) as sfP_; sf_destruct 4%nat sfP_ as H0 N1 N2 N3 | sf_fb; destruct (kept_ids b Hb) as (H0 & N1 & N2 & N3) ]; exact (kept_apart b pb _ _ HINb Hb N1)].
apply cmod_drop_iv in C; [| lia| lia| intros b Hb; first [ pose proof (kept_ids b Hb) as sfP_; sf_destruct 4%nat sfP_ as H0 N1 N2 N3 | sf_fb; destruct (kept_ids b Hb) as (H0 & N1 & N2 & N3) ]; pose proof (kept_apart b pl _ _ HINl Hb N2); lia].
apply cmod_drop_iv in C; [| lia| lia| intros b Hb; first [ pose proof (kept_ids b Hb) as sfP_; sf_destruct 4%nat sfP_ as H0 N1 N2 N3 | sf_fb; destruct (kept_ids b Hb) as (H0 & N1 & N2 & N3) ]; pose proof (kept_apart b pg _ _ HINg Hb N3); lia].
apply cmod_drop_iv in C; [| lia| unfold alloc_ceiling in *; lia| intros b Hb; destruct (kept_ids b Hb) as (H0 & _);
pose proof (RHEAP_block_range_proof _ _ _ _ HP H0) as BR; unfold rblock_range, alloc_ceiling in BR; lia].
exact C.
Qed.

Lemma ERR0 : rw_cells rsegs m (316496 + -164) [C4 errv].
Proof. pose proof ERR as E. rewrite TP, unsigned_lit in E by (unfold RATP; lia). unfold RATP in E. exact E. Qed.

Lemma sb_os1 : stream_blocks LB os1 Bd L Gv.
Proof.
pose proof (pagein_returned_inv os SINV) as sfP_; first [ sf_destruct 6%nat sfP_ as _ _ Elv1 Egv1 Ebd1 _ | sf_fb; destruct sfP_ as (_ & _ & Elv1 & Egv1 & Ebd1 & _) ].
unfold stream_blocks in *. rewrite Ebd1, Elv1, Egv1. exact SB.
Qed.

Lemma HP_phase1 : forall m', munch W1 m m' -> wmono rsegs m m' -> RHEAP s LB m'.
Proof.
intros m' MU WM. pose proof facts_proof as FA. unfold facts in FA. pose proof CEIL as CE. unfold alloc_ceiling in CE.
eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|].
apply Forall_cons; [right; right; exists (pb, Bd, os_body_storage os); split; [exact HINb| cbn; lia]|].
apply Forall_cons; [right; right; exists (pl, L, os_lacing_storage os * 4); split; [exact HINl| cbn; lia]|].
apply Forall_cons; [right; right; exists (pg, Gv, os_lacing_storage os * 8); split; [exact HINg| cbn; lia]|].
apply Forall_nil.
Qed.
Lemma AUX_phase1 : forall m', munch W1 m m' -> wmono rsegs m m' -> rauxv_ok m' B.
Proof.
intros m' MU WM. pose proof facts_proof as FA. unfold facts in FA. pose proof CEIL as CE. unfold alloc_ceiling in CE.
pose proof statics_B as XB. pose proof statics_L as XL. pose proof statics_G as XG.
eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
repeat (apply Forall_cons; [cbn; unfold RAUXV_CELL; (clear - CE FA gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp RCEIL XB XL XG; lia)|]). apply Forall_nil.
Qed.
Lemma ERR_phase1 : forall m', munch W1 m m' -> wmono rsegs m m' -> rw_cells rsegs m' (316496 + -164) [C4 errv].
Proof.
intros m' MU WM. pose proof facts_proof as FA. unfold facts in FA. pose proof CEIL as CE. unfold alloc_ceiling in CE.
pose proof statics_B as XB. pose proof statics_L as XL. pose proof statics_G as XG.
eapply rw_cells_transport; [exact ERR0| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia].
Qed.
Lemma HBS_phase1 : forall m', munch W1 m m' -> bytes_at rsegs m' (H + pg_header_len og) bs.
Proof.
intros m' MU. pose proof facts_proof as FA. unfold facts in FA.
pose proof sep_SB. pose proof sep_SL. pose proof sep_SG.
eapply bytes_at_transport; [exact HBS| exact MU| cbn [disjoint_from]; (clear - H1 H0 H FA SPG PGIN Hpg0 BSLEN HLEN LENH HL gws lws bodybytes bs hs shdr og B lo Gv L Bd nsy Dsy G A os sp RCEIL; lia)].
Qed.

Lemma pi_fail1 : forall m1 (j0 : list byte) bodybytes1 lws1 gws1
(x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
munch W1 m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
rw_cells rsegs m1 A (stream_cells Bd L Gv shdr os1) ->
u8arr rsegs m1 Bd bodybytes1 -> Z.of_nat (length bodybytes1) = os_body_storage os -> body_pre (os_body os1) bodybytes1 ->
u32arr rsegs m1 L lws1 -> wpre (os_lacing os1) lws1 -> Z.of_nat (length lws1) = os_lacing_storage os ->
u64arr rsegs m1 Gv gws1 -> Z.of_nat (length gws1) = os_lacing_storage os ->
FRAME m1 (LOC j0) -> bytes_at rsegs m1 H hs -> rw_cells rsegs m1 G (page_cells Dsy og) -> stk rsegs m1 lo (bv_unsigned sp + -144) ->
evt rsegs (POST (-1, os1) s)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (-1)) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x30bf8) fc None m1 (seg_rom rsegs)).
Proof.
intros until x31. intros MU WM MI1 OS1 BODY1 BLEN1 BPRE1 LAC1 LPRE1 LLEN1 GRA1 GLEN1 FR1 HS1 OG1 ST1.
pose proof facts_proof as FA. unfold facts in FA. pose proof CEIL as CE. unfold alloc_ceiling in CE.
pose proof statics_B as XB. pose proof statics_L as XL. pose proof statics_G as XG.
pose proof (pagein_returned_inv os SINV) as sfP_; first [ sf_destruct 9%nat sfP_ as SINV1 Hret1 Elv1 Egv1 Ebd1 Els1 Ebs1 Esn1 Epn1 | sf_fb; destruct sfP_ as (SINV1 & Hret1 & Elv1 & Egv1 & Ebd1 & Els1 & Ebs1 & Esn1 & Epn1) ].
destruct (frame_merge40 _ _ _ _ _ _ _ _ FR1) as [j FRj].
eapply evt_cut.
{ eapply (pi_epilogue lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 j); [exact FRj| exact ST1| lia| exact MI1]. }
intros ms2 sfH_; first [ sf_destruct 16%nat sfH_ as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' -> ST2 | sf_fb; destruct sfH_ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & ST2) ].
apply evt_done. unfold pagein_post.
sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (m1) | exact (errv) | exact (LB) | ] | sf_fb; exists m1, errv, LB ].
split; [reflexivity|]. split; [exact MI1|]. split; [exact ST2|].
split. { rewrite TP. rewrite unsigned_lit by (unfold RATP; lia). unfold RATP. apply ERR_phase1; assumption. }
split; [apply AUX_phase1; assumption|].
split; [reflexivity|]. split; [reflexivity|].
split; [apply HP_phase1; assumption|].
split; [intros b Hb _ _ _; exact Hb|].
split; [apply cmod_phase1; assumption|].
split; [exact OG1|]. split; [exact HS1|].
split; [apply HBS_phase1; assumption|].
split; [right; reflexivity|].
left. first [ unshelve sf_eexists 9%nat; [ exact (Bd) | exact (L) | exact (Gv) | exact (pb) | exact (pl) | exact (pg) | exact (bodybytes1) | exact (lws1) | exact (gws1) | ] | sf_fb; exists Bd, L, Gv, pb, pl, pg, bodybytes1, lws1, gws1 ]. cbn [fst snd].
rewrite Ebd1, Elv1, Egv1, Ebs1, Els1.
split; [exact Hpb|]. split; [exact Hpl|]. split; [exact Hpg|].
split; [exact HINb|]. split; [exact HINl|]. split; [exact HINg|].
split; [exact HKb|]. split; [exact HKl|]. split; [exact HKg|].
split; [exact sb_os1|]. split; [apply fields_ok_returned; [exact FOK| exact SINV| lia]|].
split; [exact OS1|].
unfold stream_arrays. rewrite Ebs1, Els1.
split. { split; [exact BODY1|]. split; [exact BLEN1|]. split; [exact BPRE1|]. split; [exact LAC1|]. split; [exact LPRE1|].
split; [exact LLEN1|]. split; [exact GRA1| exact GLEN1]. }
pose proof SB as sfP_; first [ sf_destruct 6%nat sfP_ as _ _ _ D12 D13 D23 | sf_fb; destruct sfP_ as (_ & _ & _ & D12 & D13 & D23) ].
apply perm_hd3_lbr; [exact (RHEAP_blocks_nodup_proof _ _ _ HP)| exact HINb| exact HINl| exact HINg
| exact (D12 _ _ Hpb Hpl)| exact (D13 _ _ Hpb Hpg)| exact (D23 _ _ Hpl Hpg)].
Qed.

Local Notation Wc := [(bv_unsigned sp + -144 - 32, bv_unsigned sp + -144); (A, A + 408)].

Lemma cmod_callee : forall m1 m2 LBc,
cmod [(A, A + 408)] kept (bv_unsigned sp) m m1 -> cmod Wc LBc (bv_unsigned sp + -144) m1 m2 ->
(forall b, In b kept -> In b LBc) -> cmod [(A, A + 408)] kept (bv_unsigned sp) m m2.
Proof.
intros m1 m2 LBc C1 C2 K. pose proof facts_proof as FA. unfold facts in FA. pose proof CEIL as CE. unfold alloc_ceiling in CE.
eapply cmod_trans; [exact C1|].
apply (cmod_weaken _ Wc LBc kept (bv_unsigned sp + -144) (bv_unsigned sp)) in C2; [| lia| exact K| intros x Hx; exact Hx].
apply cmod_drop_iv in C2; [exact C2| lia| lia|].
intros b Hb. destruct (kept_ids b Hb) as (Hb0 & _). pose proof (RHEAP_block_range_proof _ _ _ _ HP Hb0) as BR.
unfold rblock_range, alloc_ceiling in BR. lia.
Qed.

Lemma sync_kept : In (psy, Dsy, nsy) kept.
Proof. apply lb_remove_keep; [| cbn; exact NEg]. apply lb_remove_keep; [| cbn; exact NEl]. apply lb_remove_keep; [exact HINsy| cbn; exact NEb]. Qed.

Lemma callee_keeps : forall m1 m2 LBc (j0 : list byte),
cmod Wc LBc (bv_unsigned sp + -144) m1 m2 -> (forall b, In b kept -> In b LBc) ->
(FRAME m1 (LOC j0) -> FRAME m2 (LOC j0)) /\
(bytes_at rsegs m1 H hs -> bytes_at rsegs m2 H hs) /\
(bytes_at rsegs m1 (H + pg_header_len og) bs -> bytes_at rsegs m2 (H + pg_header_len og) bs) /\
(rw_cells rsegs m1 G (page_cells Dsy og) -> rw_cells rsegs m2 G (page_cells Dsy og)).
Proof.
intros m1 m2 LBc j0 C K. pose proof facts_proof as FA. unfold facts in FA.
pose proof (K _ sync_kept) as SYK.
split. { intros X. eapply cmod_rw_cells; [exact C| exact X| apply rclient_range_stack; lia| cbn [disjoint_from cells_size csize Nat.add app]; lia]. }
split. { intros X. eapply cmod_bytes_at; [exact C| exact X| eapply (rclient_range_block _ _ psy Dsy nsy); [exact SYK| lia| lia]| cbn [disjoint_from]; lia]. }
split. { intros X. eapply cmod_bytes_at; [exact C| exact X| eapply (rclient_range_block _ _ psy Dsy nsy); [exact SYK| lia| lia]| cbn [disjoint_from]; lia]. }
intros X. eapply cmod_rw_cells; [exact C| exact X| apply rclient_range_stack; lia| unfold page_cells; cbn [disjoint_from cells_size csize Nat.add]; lia].
Qed.

Lemma pi_fail_zero : forall m2 ps2 LB2 (errv2 : word) (j0 : list byte)
(x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
mem_inv rsegs m2 -> stk rsegs m2 lo (bv_unsigned sp + -144) -> rw_cells rsegs m2 (316496 + -164) [C4 errv2] -> rauxv_ok m2 B ->
ps_fa ps2 = ps_fa s -> ps_so ps2 = ps_so s -> RHEAP ps2 LB2 m2 -> (forall b, In b kept -> In b LB2) ->
cmod [(A, A + 408)] kept (bv_unsigned sp) m m2 ->
rw_cells rsegs m2 A (stream_cells 0 0 0 zero_hdr stream_zero) -> Permutation LB2 kept ->
FRAME m2 (LOC j0) -> bytes_at rsegs m2 H hs -> bytes_at rsegs m2 (H + pg_header_len og) bs -> rw_cells rsegs m2 G (page_cells Dsy og) ->
evt rsegs (POST (-1, stream_zero) ps2)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (-1)) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x30bf8) fc None m2 (seg_rom rsegs)).
Proof.
intros until x31. intros MI2 ST2 ERR2 AUX2 FA2 SO2 HP2 KEPT2 CM2 OS2 PERM2 FR2 HS2 HBS2 OG2.
pose proof facts_proof as FA. unfold facts in FA.
destruct (frame_merge40 _ _ _ _ _ _ _ _ FR2) as [j FRj].
eapply evt_cut.
{ eapply (pi_epilogue lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 j); [exact FRj| exact ST2| lia| exact MI2]. }
intros ms3 sfH_; first [ sf_destruct 16%nat sfH_ as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' -> ST3 | sf_fb; destruct sfH_ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & ST3) ].
apply evt_done. unfold pagein_post.
sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (m2) | exact (errv2) | exact (LB2) | ] | sf_fb; exists m2, errv2, LB2 ].
split; [reflexivity|]. split; [exact MI2|]. split; [exact ST3|].
split. { rewrite TP. rewrite unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR2. }
split; [exact AUX2|]. split; [exact FA2|]. split; [exact SO2|]. split; [exact HP2|].
split. { intros b Hb N1 N2 N3. apply KEPT2. apply lb_remove_keep; [| exact N3]. apply lb_remove_keep; [| exact N2]. apply lb_remove_keep; [exact Hb| exact N1]. }
split; [exact CM2|]. split; [exact OG2|]. split; [exact HS2|]. split; [exact HBS2|].
split; [right; reflexivity|].
right. split; [reflexivity|]. split; [exact OS2| exact PERM2].
Qed.

Lemma cmod_phaseW : forall m5 m6 ps LB5 (ql qg : bptr) (L' Gv' n : Z),
RHEAP ps LB5 m5 -> (forall b, In b kept -> In b LB5) -> (forall b, In b kept -> blk_id b <> ql /\ blk_id b <> qg) ->
In (ql, L', n * 4) LB5 -> In (qg, Gv', n * 8) LB5 ->
munch [(bv_unsigned sp - 144, bv_unsigned sp); (A, A + 408); (L', L' + 4 * n); (Gv', Gv' + 8 * n)] m5 m6 -> wmono rsegs m5 m6 ->
cmod [(A, A + 408)] kept (bv_unsigned sp) m5 m6.
Proof.
intros m5 m6 ps LB5 ql qg L' Gv' n HP5 K5 FRK HINl5 HINg5 MU6 WM6.
pose proof facts_proof as FA. unfold facts in FA. pose proof CEIL as CE. unfold alloc_ceiling in CE.
pose proof (RHEAP_block_range_proof _ _ _ _ HP5 HINl5) as BRl. cbn [blk_addr blk_size fst snd] in BRl. unfold rblock_range, alloc_ceiling in BRl.
pose proof (RHEAP_block_range_proof _ _ _ _ HP5 HINg5) as BRg. cbn [blk_addr blk_size fst snd] in BRg. unfold rblock_range, alloc_ceiling in BRg.
pose proof (cmod_of_munch _ kept (bv_unsigned sp) m5 m6 MU6 WM6) as C.
apply (cmod_weaken _ [(L', L' + 4 * n); (Gv', Gv' + 8 * n); (bv_unsigned sp - 144, bv_unsigned sp); (A, A + 408)]
kept kept (bv_unsigned sp) (bv_unsigned sp)) in C; [| lia| auto| unfold sub_fp; cbn [outside]; intros; lia].
apply cmod_drop_iv in C; [| lia| lia| intros b Hb; destruct (FRK b Hb) as [N1 N2];
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP5 (K5 b Hb) HINl5 N1) as X; cbn [blk_addr blk_size fst snd] in X; lia].
apply cmod_drop_iv in C; [| lia| lia| intros b Hb; destruct (FRK b Hb) as [N1 N2];
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP5 (K5 b Hb) HINg5 N2) as X; cbn [blk_addr blk_size fst snd] in X; lia].
apply cmod_drop_iv in C; [| lia| lia| intros b Hb; pose proof (RHEAP_block_range_proof _ _ _ _ HP5 (K5 b Hb)) as BR;
unfold rblock_range, alloc_ceiling in BR; lia].
exact C.
Qed.

Lemma phaseW_keeps : forall m5 m6 ps LB5 (pb5 ql qg : bptr) (Bd5 L' Gv' n nb : Z) (errv5 : word) (bodyb : list byte),
RHEAP ps LB5 m5 -> In (pb5, Bd5, nb) LB5 -> In (ql, L', n * 4) LB5 -> In (qg, Gv', n * 8) LB5 -> In (psy, Dsy, nsy) LB5 ->
pb5 <> ql -> pb5 <> qg -> psy <> ql -> psy <> qg ->
munch [(bv_unsigned sp - 144, bv_unsigned sp); (A, A + 408); (L', L' + 4 * n); (Gv', Gv' + 8 * n)] m5 m6 -> wmono rsegs m5 m6 ->
(stk rsegs m5 lo (bv_unsigned sp + -144) -> stk rsegs m6 lo (bv_unsigned sp + -144)) /\
(rw_cells rsegs m5 G (page_cells Dsy og) -> rw_cells rsegs m6 G (page_cells Dsy og)) /\
(bytes_at rsegs m5 (H + pg_header_len og) bs -> bytes_at rsegs m6 (H + pg_header_len og) bs) /\
(rw_cells rsegs m5 (316496 + -164) [C4 errv5] -> rw_cells rsegs m6 (316496 + -164) [C4 errv5]) /\
(rauxv_ok m5 B -> rauxv_ok m6 B) /\
RHEAP ps LB5 m6 /\
(Z.of_nat (length bodyb) = nb -> u8arr rsegs m5 Bd5 bodyb -> u8arr rsegs m6 Bd5 bodyb).
Proof.
intros until bodyb. intros HP5 HINb5 HINl5 HINg5 HINsy5 NEbl NEbg NEsl NEsg MU6 WM6.
pose proof facts_proof as FA. unfold facts in FA. pose proof CEIL as CE. unfold alloc_ceiling in CE.
pose proof (RHEAP_block_range_proof _ _ _ _ HP5 HINb5) as BRb. cbn [blk_addr blk_size fst snd] in BRb. unfold rblock_range, alloc_ceiling in BRb.
pose proof (RHEAP_block_range_proof _ _ _ _ HP5 HINl5) as BRl. cbn [blk_addr blk_size fst snd] in BRl. unfold rblock_range, alloc_ceiling in BRl.
pose proof (RHEAP_block_range_proof _ _ _ _ HP5 HINg5) as BRg. cbn [blk_addr blk_size fst snd] in BRg. unfold rblock_range, alloc_ceiling in BRg.
pose proof (RHEAP_block_range_proof _ _ _ _ HP5 HINsy5) as BRs. cbn [blk_addr blk_size fst snd] in BRs. unfold rblock_range, alloc_ceiling in BRs.
first [ sf_destruct 5%nat BRb as Bb1 Bb2 Bb3 Bb4 Bb5 | sf_fb; destruct BRb as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5) ]. first [ sf_destruct 5%nat BRl as Bl1 Bl2 Bl3 Bl4 Bl5 | sf_fb; destruct BRl as (Bl1 & Bl2 & Bl3 & Bl4 & Bl5) ]. first [ sf_destruct 5%nat BRg as Bg1 Bg2 Bg3 Bg4 Bg5 | sf_fb; destruct BRg as (Bg1 & Bg2 & Bg3 & Bg4 & Bg5) ]. first [ sf_destruct 5%nat BRs as Bs1 Bs2 Bs3 Bs4 Bs5 | sf_fb; destruct BRs as (Bs1 & Bs2 & Bs3 & Bs4 & Bs5) ].
hide Bb5. hide Bl5. hide Bg5. hide Bs5.
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP5 HINb5 HINl5 ltac:(cbn; exact NEbl)) as SEP_BL5. cbn [blk_addr blk_size fst snd] in SEP_BL5. hide SEP_BL5.
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP5 HINb5 HINg5 ltac:(cbn; exact NEbg)) as SEP_BG5. cbn [blk_addr blk_size fst snd] in SEP_BG5. hide SEP_BG5.
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP5 HINsy5 HINl5 ltac:(cbn; exact NEsl)) as SEP_SL5. cbn [blk_addr blk_size fst snd] in SEP_SL5. hide SEP_SL5.
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP5 HINsy5 HINg5 ltac:(cbn; exact NEsg)) as SEP_SG5. cbn [blk_addr blk_size fst snd] in SEP_SG5. hide SEP_SG5.
split. { intros X. eapply stk_transport_disjoint; [exact X| exact MU6| exact WM6| cbn [disjoint_from]; lia]. }
split. { intros X. eapply rw_cells_transport; [exact X| exact MU6| exact WM6| unfold page_cells; cbn [disjoint_from cells_size csize Nat.add]; lia]. }
split. { intros X. unfold hideP in SEP_SL5, SEP_SG5. eapply bytes_at_transport; [exact X| exact MU6| cbn [disjoint_from]; (clear - SEP_SG5 SEP_SL5 Bs4 Bs1 Bg3 Bg1 Bl4 Bl1 Bb1 CE FA n Gv' L' Bd5 SPG PGIN Hpg0 BSLEN HLEN LENH HL gws lws bodybytes bs hs shdr og B lo Gv L Bd nsy Dsy G A os sp RCEIL; lia)]. }
split. { intros X. unfold hideP in Bl5, Bg5. eapply rw_cells_transport; [exact X| exact MU6| exact WM6| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
split. { intros X. unfold hideP in Bl5, Bg5. eapply rauxv_ok_frame; [exact X| exact MU6| exact WM6|].
repeat (apply Forall_cons; [cbn; unfold RAUXV_CELL; (clear - Bs1 CE FA gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp RCEIL Bg1 Bl5 Bl4 Bl1 n Gv' L' Bg5 Bg4; lia)|]). apply Forall_nil. }
split. { eapply RHEAP_frame_proof; [exact HP5| exact MU6| exact WM6|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|].
apply Forall_cons; [right; right; exists (ql, L', n * 4); split; [exact HINl5| cbn; lia]|].
apply Forall_cons; [right; right; exists (qg, Gv', n * 8); split; [exact HINg5| cbn; lia]|].
apply Forall_nil. }
intros LEN X. unfold hideP in SEP_BL5, SEP_BG5. eapply u8arr_transport; [exact X| exact MU6| exact WM6| cbn [disjoint_from]; lia].
Qed.

Lemma pi_finish : forall m5 ps LB5 (errv5 : word) (os4 : stream_st bptr) (pb4 ql qg : bptr) (Bd4 L' Gv' : Z)
(bodybytes4 : list byte) (lws4 gws4 : list word) (j0 : list byte) (segptr bos' : Z)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x18 x19 x20 x22 x27 x29 x30 x31 : word),
mem_inv rsegs m5 -> stk rsegs m5 lo (bv_unsigned sp + -144) -> rw_cells rsegs m5 (316496 + -164) [C4 errv5] -> rauxv_ok m5 B ->
ps_fa ps = ps_fa s -> ps_so ps = ps_so s -> RHEAP ps LB5 m5 -> (forall b, In b kept -> In b LB5) ->
(forall b, In b kept -> blk_id b <> ql /\ blk_id b <> qg) ->
cmod [(A, A + 408)] kept (bv_unsigned sp) m m5 ->
rw_cells rsegs m5 A (stream_cells Bd4 L' Gv' shdr os4) ->
u8arr rsegs m5 Bd4 bodybytes4 -> Z.of_nat (length bodybytes4) = os_body_storage os4 -> body_pre (os_body os4) bodybytes4 ->
u32arr rsegs m5 L' lws4 -> wpre (os_lacing os4) lws4 -> Z.of_nat (length lws4) = os_lacing_storage os4 ->
u64arr rsegs m5 Gv' gws4 -> Z.of_nat (length gws4) = os_lacing_storage os4 ->
FRAME m5 (LOC j0) -> bytes_at rsegs m5 H hs -> bytes_at rsegs m5 (H + pg_header_len og) bs -> rw_cells rsegs m5 G (page_cells Dsy og) ->
os_body_data os4 = Some pb4 -> os_lacing_vals os4 = Some ql -> os_granule_vals os4 = Some qg ->
In (pb4, Bd4, os_body_storage os4) LB5 -> In (ql, L', os_lacing_storage os4 * 4) LB5 -> In (qg, Gv', os_lacing_storage os4 * 8) LB5 ->
rhdr_known ps pb4 -> rhdr_known ps ql -> rhdr_known ps qg -> stream_blocks LB5 os4 Bd4 L' Gv' ->
Permutation LB5 ((pb4, Bd4, os_body_storage os4) :: (ql, L', os_lacing_storage os4 * 4) :: (qg, Gv', os_lacing_storage os4 * 8) :: kept) ->
psy <> ql -> psy <> qg ->
stream_fields_ok os4 -> stream_inv os4 -> os_lacing_returned os4 = 0 -> lacing_vals_ok (os_lacing os4) ->
os_lacing_fill os4 + nseg + 1 <= os_lacing_storage os4 -> os_lacing_storage os4 < 2^31 ->
0 <= segptr <= nseg -> (bos' = 0 \/ bos' = Z.land (znth hdr 5) 2) ->
evt rsegs (POST (0, pagein_segments os4 hdr bos' segptr) ps)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 (znth hdr 5)) x10
x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 H) x22 (Z_to_bv 64 segptr) (Z_to_bv 64 (ogg_page_pageno hdr)) (Z_to_bv 64 bos') (Z_to_bv 64 nseg) x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x30afc) fc None m5 (seg_rom rsegs)).
Proof.
intros until x31.
intros MI5 ST5 ERR5 AUX5 FA5 SO5 HP5 K5 FRK CM5 OS5 BODY5 BLEN5 BPRE5 LAC5 LPRE5 LLEN5 GRA5 GLEN5 FR5 HS5 HBS5 OG5
Hpb4 Hql Hqg HINb5 HINl5 HINg5 HKb5 HKl5 HKg5 SB5 PERM5 NEsl NEsg FOK4 SINV4 Hret4 LOK4 Hls4 INT31 Hseg Hbos.
pose proof facts_proof as FA. unfold facts in FA. pose proof CEIL as CE. unfold alloc_ceiling in CE.
pose proof SINV4 as sfP_; first [ sf_destruct 5%nat sfP_ as J1 J2 J3 J4 J5 | sf_fb; destruct sfP_ as (J1 & J2 & J3 & J4 & J5) ]. unfold zlength in J3, J4.
pose proof FOK4 as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in F4, F5, F6, F7, F8, F9, F10.
pose proof (wpre_length _ _ LPRE5) as LL5.
pose proof (K5 _ sync_kept) as HINsy5.
pose proof SB5 as sfP_; first [ sf_destruct 6%nat sfP_ as _ _ _ D12 D13 D23 | sf_fb; destruct sfP_ as (_ & _ & _ & D12 & D13 & D23) ].
assert (NEbl : pb4 <> ql) by (eapply D12; eassumption). assert (NEbg : pb4 <> qg) by (eapply D13; eassumption). assert (NElg : ql <> qg) by (eapply D23; eassumption).
pose proof (RHEAP_block_range_proof _ _ _ _ HP5 HINl5) as BRl. cbn [blk_addr blk_size fst snd] in BRl. unfold rblock_range, alloc_ceiling in BRl. first [ sf_destruct 5%nat BRl as Bl1 Bl2 Bl3 Bl4 _ | sf_fb; destruct BRl as (Bl1 & Bl2 & Bl3 & Bl4 & _) ].
pose proof (RHEAP_block_range_proof _ _ _ _ HP5 HINg5) as BRg. cbn [blk_addr blk_size fst snd] in BRg. unfold rblock_range, alloc_ceiling in BRg. first [ sf_destruct 5%nat BRg as Bg1 Bg2 Bg3 Bg4 _ | sf_fb; destruct BRg as (Bg1 & Bg2 & Bg3 & Bg4 & _) ].
pose proof (RHEAP_block_range_proof _ _ _ _ HP5 HINsy5) as BRs. cbn [blk_addr blk_size fst snd] in BRs. unfold rblock_range, alloc_ceiling in BRs. first [ sf_destruct 5%nat BRs as Bs1 Bs2 Bs3 Bs4 _ | sf_fb; destruct BRs as (Bs1 & Bs2 & Bs3 & Bs4 & _) ].
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP5 HINl5 HINg5 ltac:(cbn; exact NElg)) as SEP_LG5. cbn [blk_addr blk_size fst snd] in SEP_LG5.
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP5 HINsy5 HINl5 ltac:(cbn; exact NEsl)) as SEP_SL5. cbn [blk_addr blk_size fst snd] in SEP_SL5.
pose proof (RHEAP_blocks_disjoint_proof _ _ _ _ _ HP5 HINsy5 HINg5 ltac:(cbn; exact NEsg)) as SEP_SG5. cbn [blk_addr blk_size fst snd] in SEP_SG5.
hide SEP_LG5. hide SEP_SL5. hide SEP_SG5.
assert (Hlac : bytes_ok (lacing_of hdr)) by (apply bytes_ok_zslice; apply ubytes_ok).
pose proof (zlength_lacing_of hs LENH ltac:(lia)) as ZL.
eapply evt_cut.
{ eapply (pi_final A Bd4 L' Gv' H lo shdr hs os4 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc _ segptr bos' (ogg_page_pageno hdr)
(Z_to_bv 64 (znth hdr 18)) (Z_to_bv 64 (znth hdr 21)) j0); try eassumption; try reflexivity.
all: try (unfold zlength; (clear - FA gws4 lws4 os4 gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp RCEIL Hseg Hls4 segptr F6 J2 Bs1 Bg1 Bl1 LL5 bodybytes4 Gv' L' Hpg0 LENH HL bs shdr og Bl4 Bg4 Bs4 PGIN BSLEN HLEN CE; lia)).
1: unfold hideP in SEP_LG5; lia.
1: unfold hideP in SEP_SL5; (clear - SEP_SL5 Bs1 Bg1 Bl1 LL5 FA gws4 lws4 bodybytes4 Gv' L' os4 PGIN Hpg0 BSLEN HLEN LENH HL gws lws bodybytes bs hs shdr og B lo Gv L Bd nsy Dsy A os sp RCEIL; lia).
1: unfold hideP in SEP_SG5; (clear - SEP_SG5 Bs1 Bg1 Bl1 LL5 FA gws4 lws4 bodybytes4 Gv' L' os4 PGIN Hpg0 BSLEN HLEN LENH HL gws lws bodybytes bs hs shdr og B lo Gv L Bd nsy Dsy A os sp RCEIL; lia). }
intros ms6 FP. unfold final_post in FP.
first [ sf_destruct 29%nat FP as u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 m6 lws6 gws6 -> MU6 WM6 MI6 OS6 LAC6 LPRE6 LLEN6 GRA6 GLEN6 ST6 HS6 | sf_fb; destruct FP as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m6 & lws6 & gws6 & -> & MU6 & WM6 & MI6 & OS6 & LAC6 & LPRE6 & LLEN6 & GRA6 & GLEN6 & ST6 & HS6) ].
first [ pose proof (phaseW_keeps m5 m6 ps LB5 pb4 ql qg Bd4 L' Gv' (os_lacing_storage os4) (os_body_storage os4) errv5 bodybytes4
HP5 HINb5 HINl5 HINg5 HINsy5 NEbl NEbg NEsl NEsg MU6 WM6) as sfP_; sf_destruct 7%nat sfP_ as Tst Tog Thbs Terr Taux HP6 Tbody | sf_fb; destruct (phaseW_keeps m5 m6 ps LB5 pb4 ql qg Bd4 L' Gv' (os_lacing_storage os4) (os_body_storage os4) errv5 bodybytes4
HP5 HINb5 HINl5 HINg5 HINsy5 NEbl NEbg NEsl NEsg MU6 WM6) as (Tst & Tog & Thbs & Terr & Taux & HP6 & Tbody) ].
pose proof (segments_shape os4 hdr bos' segptr Hlac ltac:(lia) ltac:(lia)) as SH. cbv zeta in SH.
first [ sf_destruct 17%nat SH as E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 | sf_fb; destruct SH as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17) ].
apply evt_done. unfold pagein_post.
sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (m6) | exact (errv5) | exact (LB5) | ] | sf_fb; exists m6, errv5, LB5 ].
split; [reflexivity|]. split; [exact MI6|]. split; [exact ST6|].
split. { rewrite TP. rewrite unsigned_lit by (unfold RATP; lia). unfold RATP. exact (Terr ERR5). }
split; [exact (Taux AUX5)|].
split; [exact FA5|]. split; [exact SO5|].
split; [exact HP6|].
split. { intros b Hb N1 N2 N3. apply K5. apply lb_remove_keep; [| exact N3]. apply lb_remove_keep; [| exact N2]. apply lb_remove_keep; [exact Hb| exact N1]. }
split. { eapply cmod_trans; [exact CM5|]. eapply (cmod_phaseW m5 m6 ps LB5 ql qg); try eassumption. }
split; [exact (Tog OG5)|].
split; [exact HS6|].
split; [exact (Thbs HBS5)|].
split; [left; reflexivity|].
left. first [ unshelve sf_eexists 9%nat; [ exact (Bd4) | exact (L') | exact (Gv') | exact (pb4) | exact (ql) | exact (qg) | exact (bodybytes4) | exact (lws6) | exact (gws6) | ] | sf_fb; exists Bd4, L', Gv', pb4, ql, qg, bodybytes4, lws6, gws6 ]. cbn [fst snd].
rewrite E1, E2, E3, E4, E5.
split; [exact Hpb4|]. split; [exact Hql|]. split; [exact Hqg|].
split; [exact HINb5|]. split; [exact HINl5|]. split; [exact HINg5|].
split; [exact HKb5|]. split; [exact HKl5|]. split; [exact HKg5|].
split; [unfold stream_blocks in *; rewrite E1, E2, E3; exact SB5|].
split; [apply fields_ok_segments; [exact FOK4| exact Hlac| (clear - ZL FA Hseg segptr os4 gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp; lia)| (clear - J2 os4; lia)| (clear - gws6 lws6 ZL LL5 F4 FA Hls4 gws4 lws4 os4 gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp RCEIL; lia)| (clear - FA gws lws bodybytes hs B lo Gv L Bd nsy Dsy A os sp RCEIL; lia)]|].
split; [exact OS6|].
unfold stream_arrays. rewrite E4, E5, E7.
split. { split; [exact (Tbody BLEN5 BODY5)|].
split; [exact BLEN5|]. split; [exact BPRE5|]. split; [exact LAC6|]. split; [exact LPRE6|]. split; [exact LLEN6|].
split; [exact GRA6| exact GLEN6]. }
exact PERM5.
Qed.

End PAGEIN.
