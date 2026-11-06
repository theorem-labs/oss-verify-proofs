(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s
X09u X0ae X09j X09m X09p X09k.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0wl X110 X106 X109 X10c X107.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X109 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X107.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.

Lemma bytes_at_prefix_eq : forall (m : mem) a (all pre : list byte),
bytes_at bsegs m a all -> bytes_at bsegs m a pre -> (length pre <= length all)%nat -> firstn (length pre) all = pre.
Proof.
intros m a all pre (_ & _ & HA) (_ & _ & HP) Hle. apply nth_error_ext. intros i. rewrite nth_error_firstn.
destruct (Nat.ltb_spec i (length pre)) as [Hi|Hi].
- rewrite <- (HA i ltac:(lia)), <- (HP i Hi). reflexivity.
- symmetry. apply nth_error_None. exact Hi.
Qed.

Lemma fresh_block_u8arr : forall (m : mem) q n (pre : list byte),
wr_at bsegs m q n -> 0 <= n -> bytes_at bsegs m q pre -> Z.of_nat (length pre) <= n ->
exists junk, u8arr bsegs m q (pre ++ junk) /\ Z.of_nat (length (pre ++ junk)) = n.
Proof.
intros m q n pre WR N0 BP LE. destruct (wr_at_rw_CB m q n WR N0) as (all & BLK).
pose proof BLK as [[[LA _] BA] _]. cbn [cell_wf] in LA. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
pose proof (bytes_at_prefix_eq m q all pre BA BP ltac:(lia)) as E.
exists (skipn (length pre) all). split.
- rewrite <- E at 1. rewrite firstn_skipn. apply u8arr_rw_CB. rewrite LA. exact BLK.
- rewrite length_app, length_skipn, LA. lia.
Qed.

Definition sy_compact (sy : sync_st bptr) : sync_st bptr :=
if negb (sy_returned sy =? 0) then
mkSync (sy_data sy) (ztake (sy_fill sy - sy_returned sy) (zdrop (sy_returned sy) (sy_buf sy)))
(sy_storage sy) (sy_fill sy - sy_returned sy) 0 (sy_unsynced sy) (sy_headerbytes sy) (sy_bodybytes sy)
else sy.

Lemma compact_prefix : forall (buf : list Z) (bytes : list byte) (ret fill : nat),
firstn (length buf) (ubytes bytes) = buf -> (ret + fill <= length buf)%nat -> (length buf <= length bytes)%nat ->
firstn (length (firstn fill (skipn ret buf))) (ubytes (firstn fill (skipn ret bytes) ++ skipn fill bytes)) = firstn fill (skipn ret buf)
/\ (length (firstn fill (skipn ret buf)) <= length (firstn fill (skipn ret bytes) ++ skipn fill bytes))%nat.
Proof.
intros buf bytes ret fill Hpre Hrf Hlen.
assert (L1 : length (firstn fill (skipn ret buf)) = fill) by (rewrite firstn_length_le by (rewrite length_skipn; lia); reflexivity).
rewrite L1. split.
- rewrite ubytes_app, firstn_app, ubytes_firstn, ubytes_skipn, firstn_firstn, Nat.min_id.
rewrite firstn_length_le by (rewrite length_skipn, ubytes_length; lia). rewrite Nat.sub_diag, firstn_O, app_nil_r.
rewrite <- Hpre. rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia.
- rewrite length_app, firstn_length_le by (rewrite length_skipn; lia). lia.
Qed.

Definition sync_buffer_res (sy : sync_st bptr) (size : Z) : option (bptr * Z) * sync_st bptr :=
let sy1 := sy_compact sy in
if sy_storage sy1 - sy_fill sy1 <? size then
(Some (tt, sy_fill sy1),
mkSync (Some tt) (sy_buf sy1) (size + sy_fill sy1 + 4096) (sy_fill sy1) (sy_returned sy1) (sy_unsynced sy1) (sy_headerbytes sy1) (sy_bodybytes sy1))
else (match sy_data sy1 with Some p => Some (p, sy_fill sy1) | None => None end, sy1).

Lemma sync_buffer_prun : forall (sy : sync_st unit) size q r q',
prun (ogg_sync_buffer (St := pst) p_malloc p_realloc p_free sy size) q = Some (r, q') ->
0 <= sy_storage sy -> 0 <= size -> size + (sy_fill sy - sy_returned sy) + 4096 < 2^31 -> 0 <= sy_fill sy - sy_returned sy ->
r = sync_buffer_res sy size /\ q' = q.
Proof.
intros sy size q r q' H S0 Z0 NB F0. unfold ogg_sync_buffer, ogg_sync_check in H.
replace (sy_storage sy <? 0) with false in H by (symmetry; apply Z.ltb_ge; exact S0).
unfold sync_buffer_res, sy_compact, bptr in *.
destruct (negb (sy_returned sy =? 0)) eqn:ER; cbn [sy_storage sy_fill sy_data sy_buf sy_returned sy_unsynced sy_headerbytes sy_bodybytes] in H |- *.
- destruct (sy_storage sy - (sy_fill sy - sy_returned sy) <? size) eqn:EG.
+ replace (INT_MAX - 4096 - (sy_fill sy - sy_returned sy) <? size) with false in H by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
rewrite prun_bind in H.
assert (OV : p_overflows (size + (sy_fill sy - sy_returned sy) + 4096) = false) by (unfold p_overflows; apply Z.leb_gt; lia).
destruct (sy_data sy) as [[]|]; [rewrite (prun_realloc_ok tt _ _ OV) in H | rewrite (prun_malloc_ok _ _ OV) in H];
cbn beta iota in H; rewrite prun_ret in H; injection H as <- <-; split; reflexivity.
+ rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- destruct (sy_storage sy - sy_fill sy <? size) eqn:EG.
+ apply negb_false_iff, Z.eqb_eq in ER.
replace (INT_MAX - 4096 - sy_fill sy <? size) with false in H by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
rewrite prun_bind in H.
assert (OV : p_overflows (size + sy_fill sy + 4096) = false) by (unfold p_overflows; apply Z.leb_gt; lia).
destruct (sy_data sy) as [[]|]; [rewrite (prun_realloc_ok tt _ _ OV) in H | rewrite (prun_malloc_ok _ _ OV) in H];
cbn beta iota in H; rewrite prun_ret in H; injection H as <- <-; split; reflexivity.
+ rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Section OggBufferCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MAL : malloc_contract RT.
Hypothesis REA : realloc_contract RT.
Hypothesis MMOV : memmove_icontract RT e_memmove.

Definition sync_rest_live (sy : sync_st bptr) (D : Z) (live : list (Z * Z)) : list (Z * Z) :=
match sy_data sy with Some _ => live_remove D live | None => live end.

Lemma sync_rest_sub : forall sy D live e, In e (sync_rest_live sy D live) -> In e live.
Proof. intros sy D live e H. unfold sync_rest_live in H. destruct (sy_data sy); [exact (live_remove_sub _ _ _ H)| exact H]. Qed.

Lemma buf_phase1 : forall (Σ : rts RT) PMc (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A D size f lo usp : Z) (k : nat) (sy : sync_st bptr) (bytes : list byte),
fdfs_only PMc -> mat_stable PMc ->
sync_rep m A D sy bytes -> sync_inv sy -> 0 < A -> sync_live RT Σ sy D ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 32 <= f + fs_size k - 8 ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 112 <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
forall T c,
ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 usp) gp (Z_to_bv 64 0x638c98) t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_ogg_sync_buffer) fc None m (seg_rom bsegs))) c ->
(forall c1 (m1 : mem) (bytes1 j8 : list byte) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ASTA RT Σ PMc (eq (MS (mkR ra' (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x638c98) t0' t1' t2' (Z_to_bv 64 A) (Z_to_bv 64 size)
(Z_to_bv 64 (sy_storage sy)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 PC_buf_p2) fc None m1 (seg_rom bsegs))) c1 ->
ART RT Σ m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo (usp + -32) ->
rw_cells bsegs m1 (usp + -32) (buf_frame ra s0 s1 j8) ->
rw_cells bsegs m1 A (sync_cells_c D (sy_storage sy) (sy_fill (sy_compact sy)) 0 sy) ->
sync_data m1 D (sy_compact sy) bytes1 ->
rt_pres_fp (sync_rest_live sy D (rt_live RT Σ)) (rt_frames RT Σ) usp [(A, A + 32)] m m1 ->
realizes bsegs c1 T) ->
realizes bsegs c T.
Proof using AF MMOV.
intros Σ PMc ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A D size f lo usp k sy bytes
FDO MST REP INV A0 INL INF FA1 FA2 ART0 MI0 ST0 LOW LOR SPT SPA T c Hc Hk.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
destruct REP as (SY & FOK & DAT & SEP).
pose proof FOK as (Fs & Ff & Fr & Fu & Fh & Fb). unfold int31 in Fs, Ff, Fr, Fu, Fh, Fb.
destruct INV as (I1 & I2 & I3 & I4 & I5).
set (LV := sync_rest_live sy D (rt_live RT Σ)) in *.
pose proof (pres_fp_refl LV (rt_frames RT Σ) usp [(A, A + 32)] m) as PF.
assert (SPL : forall a, aclient LV (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [apply sync_rest_sub| auto| apply Z.le_refl]. }
unfold sync_cells in SY. unfold sync_data in DAT.
destruct (sy_data sy) as [p|] eqn:ED.
2:{
destruct DAT as (-> & -> & BUF0 & ST00).
assert (RZ : sy_returned sy = 0) by (rewrite BUF0 in I2; unfold zlength in I2; cbn [length] in I2; clear - I1 I2; lia).
assert (EC : sy_compact sy = sy) by (unfold sy_compact; rewrite RZ; reflexivity).
cps_norm.
cps_seg (buf_w1a A 0 size usp lo sy).
destruct POST as (m1 & j8 & a1' & -> & MU1 & WM1 & MI1 & ST1 & FR1). unfold buf_frame in FR1.
cps_seg_post.
eapply (Hk _ m1 [] j8); [exact Hc0| exact ART| exact MI1| exact ST1| exact FR1| | |].
- rewrite EC. rewrite RZ in SY. exact SY.
- rewrite EC. unfold sync_data. rewrite ED. repeat split; assumption.
- exact PF. }
destruct DAT as (D0 & ARR & LEN & PRE & LE).
specialize (INL ltac:(rewrite ED; intros X; discriminate X)).
destruct (live_below_lo RT AF Σ m D (sy_storage sy) lo ART0 INL LOW) as (_ & BD1 & _).
assert (NAD : forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (D <= a < D + sy_storage sy)).
{ intros a Ha. unfold LV, sync_rest_live in Ha. rewrite ED in Ha. exact (aclient_remove_apart RT AF Σ m D (sy_storage sy) usp a ART0 INL LOU Ha). }
destruct (Z.eq_dec (sy_returned sy) 0) as [RZ|RNZ].
-
assert (EC : sy_compact sy = sy) by (unfold sy_compact; rewrite RZ; reflexivity).
apply u8arr_rw_CB in ARR.
cps_norm.
cps_seg (buf_w1a A D size usp lo sy).
destruct POST as (m1 & j8 & a1' & -> & MU1 & WM1 & MI1 & ST1 & FR1). unfold buf_frame in FR1.
cps_seg_post.
eapply (Hk _ m1 bytes j8); [exact Hc0| exact ART| exact MI1| exact ST1| exact FR1| | |].
+ rewrite EC. rewrite RZ in SY. exact SY.
+ rewrite EC. unfold sync_data. rewrite ED. apply u8arr_rw_CB in ARR. exact (conj D0 (conj ARR (conj LEN (conj PRE LE)))).
+ exact PF.
- assert (EC : sy_compact sy = mkSync (sy_data sy) (ztake (sy_fill sy - sy_returned sy) (zdrop (sy_returned sy) (sy_buf sy)))
(sy_storage sy) (sy_fill sy - sy_returned sy) 0 (sy_unsynced sy) (sy_headerbytes sy) (sy_bodybytes sy)).
{ unfold sy_compact. replace (sy_returned sy =? 0) with false by (symmetry; apply Z.eqb_neq; exact RNZ). reflexivity. }
unfold zlength in I2.
set (nr := Z.to_nat (sy_returned sy)). set (nf := Z.to_nat (sy_fill sy - sy_returned sy)).
destruct (compact_prefix (sy_buf sy) bytes nr nf PRE ltac:(unfold nr, nf; lia) LE) as (CP1 & CP2).
destruct (Z_le_gt_dec (sy_fill sy - sy_returned sy) 0) as [FZ|FP].
+
assert (NF0 : nf = 0%nat) by (unfold nf; lia).
apply u8arr_rw_CB in ARR.
cps_norm.
cps_seg (buf_w1b A D size usp lo sy).
destruct POST as (m1 & j8 & a1' & a2' & -> & MU1 & WM1 & MI1 & ST1 & FR1 & SY1). unfold buf_frame in FR1. unfold sync_cells_c in SY1.
clear SY. cps_seg_post.
eapply (Hk _ m1 bytes j8); [exact Hc0| exact ART| exact MI1| exact ST1| exact FR1| | |].
* rewrite EC. cbn [sy_fill]. exact SY1.
* rewrite EC. unfold sync_data. cbn [sy_data sy_buf sy_storage]. rewrite ED. apply u8arr_rw_CB in ARR.
split; [exact D0|]. split; [exact ARR|]. split; [exact LEN|].
unfold ztake. fold nf. rewrite NF0. cbn [firstn length]. split; [reflexivity| lia].
* exact PF.
+
set (b1 := firstn nf bytes). set (b2 := skipn nf bytes). set (bs := firstn nf (skipn nr bytes)).
assert (Lb1 : Z.of_nat (length b1) = sy_fill sy - sy_returned sy) by (unfold b1; rewrite firstn_length_le by (unfold nf, nr in *; lia); unfold nf; lia).
assert (LEQ : length bs = length b1) by (unfold bs, b1; rewrite !firstn_length_le by (rewrite ?length_skipn; unfold nf, nr in *; lia); reflexivity).
assert (Lb2 : Z.of_nat (length b2) = sy_storage sy - (sy_fill sy - sy_returned sy)) by (unfold b2; rewrite length_skipn; unfold nf, nr in *; lia).
assert (EB : bytes = b1 ++ b2) by (symmetry; apply firstn_skipn).
pose proof (bytes_at_sub m D bytes nr nf (proj1 ARR) ltac:(unfold nf, nr in *; lia)) as SRC. fold bs in SRC.
replace (D + Z.of_nat nr) with (D + sy_returned sy) in SRC by (unfold nr; lia).
rewrite EB in ARR. apply u8arr_app in ARR. destruct ARR as (P1 & P2). apply u8arr_rw_CB in P1, P2.
assert (SEP' : D + sy_storage sy <= A \/ A + 32 <= D) by (rewrite <- LEN; exact SEP). clear SEP.
assert (Lbs : Z.of_nat (length bs) = sy_fill sy - sy_returned sy) by (rewrite LEQ; exact Lb1).
assert (FST : sy_fill sy <= sy_storage sy) by (clear - I2 LE LEN; lia).
assert (DRT : D + sy_returned sy < 2^64) by (clear - BD1 I1 Ff Fs LOR SPT I2 LE LEN; unfold RT_STACK, USTACK_TOP in *; lia).
cps_norm. cps_hide.
cps_seg (buf_w1c A D size usp lo sy).
destruct POST as (m1 & j8 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & SY1). unfold buf_frame in FR1. unfold sync_cells_c in SY1.
clear SY. cps_seg_post.

assert (SUBLV : forall e, In e LV -> In e (rt_live RT Σ)) by (intros e He; exact (sync_rest_sub _ _ _ _ He)).
assert (NAD' : forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (D <= a < D + Z.of_nat (length bs))).
{ intros a Ha. specialize (NAD a Ha). clear - NAD Lbs FST I1. lia. }
pose proof (proj2 P1) as WR1. cbn [cells_size csize Nat.add] in WR1. rewrite Nat.add_0_r, <- LEQ in WR1.
assert (AR : 0 < A < 2^64) by (clear - A0 FA2 BF1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ulc).
rewrite <- Lbs in Hc0.
cps_rt (MMOV Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 D (D + sy_returned sy) bs lo).
all: [> .. | ].
all: lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- checked_src _ _ _ _ _ _ _ => idtac
| |- checked_dst _ _ _ _ _ _ => idtac
| |- _ => try (clear - BD1 D0 I1 Ff Fs LOR SPT Lbs FST; lia)
end.
{ apply (live_checked_src RT AF Σ m1 _ lo D (sy_storage sy)); [exact ART| exact INL| lia| lia| exact BD1]. }
{ apply (live_checked_dst RT AF Σ m1 _ D (sy_storage sy)); [exact ART| exact INL| lia| lia| exact WR1]. }
intros kc2 Hc2. unfold icpt_postF in Hc2.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2).
pose proof (ogg_bytes_piece m1 m2 D bs WR1 WM2 BY2) as P1'. clear BY2.

cps_seg (buf_w1d A D size sy (sy_fill sy - sy_returned sy) (sy_returned sy)).
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & SY3). unfold sync_cells_c in SY3.
clear SY1. cps_seg_post.
eapply (Hk _ m3 (bs ++ b2) j8); [exact Hc1| exact ART| exact MI3| exact ST2| exact FR1| | |].
* rewrite EC. cbn [sy_fill]. exact SY3.
* rewrite EC. unfold sync_data. cbn [sy_data sy_buf sy_storage]. rewrite ED.
split; [exact D0|]. split.
{ apply u8arr_app. split; [apply u8arr_rw_CB; exact P1'|]. rewrite LEQ. apply u8arr_rw_CB. exact P2. }
split; [rewrite length_app; clear - Lbs Lb2; lia|].
unfold ztake, zdrop. fold nr nf. exact (conj CP1 CP2).
* exact PF.
Qed.

Lemma sync_cells_compact : forall D (sy : sync_st bptr),
sync_cells_c D (sy_storage sy) (sy_fill (sy_compact sy)) 0 sy = sync_cells D (sy_compact sy).
Proof.
intros D sy. unfold sy_compact, sync_cells_c, sync_cells. destruct (Z.eqb_spec (sy_returned sy) 0) as [E|E]; cbn [negb]; [rewrite E|]; reflexivity.
Qed.
Lemma sy_compact_facts : forall (sy : sync_st bptr), sync_inv sy -> sync_fields_ok sy ->
sy_storage (sy_compact sy) = sy_storage sy /\ sy_data (sy_compact sy) = sy_data sy /\ sy_returned (sy_compact sy) = 0
/\ sy_fill (sy_compact sy) = sy_fill sy - sy_returned sy /\ sync_fields_ok (sy_compact sy)
/\ sy_unsynced (sy_compact sy) = sy_unsynced sy /\ sy_headerbytes (sy_compact sy) = sy_headerbytes sy /\ sy_bodybytes (sy_compact sy) = sy_bodybytes sy.
Proof.
intros sy (I1 & _) FOK. pose proof FOK as (Fs & Ff & Fr & Fu & Fh & Fb). unfold sy_compact, sync_fields_ok, int31 in *.
destruct (Z.eqb_spec (sy_returned sy) 0) as [E|E]; cbn [negb sy_storage sy_data sy_returned sy_fill sy_unsynced sy_headerbytes sy_bodybytes]; repeat split; lia.
Qed.

Definition ogg_sync_buffer_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A D size f lo : Z) (k : nat) (sy : sync_st bptr) (bytes : list byte),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 size -> tp = Z_to_bv 64 0x638c98 ->
sync_rep m A D sy bytes -> sync_inv sy -> 0 < A -> sync_live RT Σ sy D ->
0 <= size -> size + (sy_fill sy - sy_returned sy) + 4096 <= 64512 -> sy_storage sy <= 64512 ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 32 <= f + fs_size k - 8 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 112 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_ogg_sync_buffer m)))
(fun c => exists (Σ' : rts RT) (D' : Z),
ASTA RT Σ' PMc (fun ms => exists m' (bytes' : list byte),
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
(Z_to_bv 64 (D' + sy_fill (sy_compact sy))) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (sync_rest_live sy D (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 32)] m m'
/\ sync_rep m' A D' (snd (sync_buffer_res sy size)) bytes') c
/\ sync_live RT Σ' (snd (sync_buffer_res sy size)) D'
/\ ((sy_storage sy - (sy_fill sy - sy_returned sy) >= size /\ D' = D /\ rt_live RT Σ' = rt_live RT Σ)
\/ (sy_storage sy - (sy_fill sy - sy_returned sy) < size
/\ rt_live RT Σ' = (D', size + (sy_fill sy - sy_returned sy) + 4096) :: sync_rest_live sy D (rt_live RT Σ)))
/\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem ogg_sync_buffer_ok : ogg_sync_buffer_cps.
Proof using AF MAL REA MMOV.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A D size f lo k sy bytes
FDO MST -> -> -> REP INV A0 INL SZ0 NB STB INF FA1 FA2 LVM CR0 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
pose proof REP as (_ & FOK & _ & SEP).
destruct (sy_compact_facts sy INV FOK) as (CS & CD & CR & CF & CFOK & CU & CH & CB).
apply (buf_phase1 Σ PMc ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A D size f lo usp k sy bytes
FDO MST REP INV A0 INL INF FA1 FA2 ART0 MI0 ST0 LOW LOR SPT SPA T c Hc).
clear Hc. intros c1 m1 bytes1 j8 ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Hc ART1 MI1 ST1 FR1 SY1 DAT1 PF.
set (sy1 := sy_compact sy) in *. set (fl := sy_fill sy1) in *. set (st := sy_storage sy) in *.
pose proof FOK as (Fs & Ff & Fr & _). unfold int31 in Fs, Ff, Fr. fold st in Fs.
pose proof INV as (I1 & I2 & _). unfold zlength in I2.
destruct (frame_below_lo RT AF Σ m1 f k lo ART1 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m1 f k ART1 INF) as (F0 & F64 & FIMG & _ & _ & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
assert (SUBLV : forall e, In e (sync_rest_live sy D (rt_live RT Σ)) -> In e (rt_live RT Σ)) by (intros e He; exact (sync_rest_sub _ _ _ _ He)).
assert (SPL : forall a, aclient (sync_rest_live sy D (rt_live RT Σ)) (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m1 usp a ART1). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUBLV| auto| apply Z.le_refl]. }
assert (AR : 0 < A < 2^64) by (clear - A0 FA2 BF1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; clear - LOR SPT BF3; unfold RT_STACK, USTACK_TOP, SH_HI in *; lia).
unfold sync_data in DAT1. rewrite CD in DAT1. unfold sync_live in INL. unfold sync_rest_live in *.
unfold sync_cells_c in SY1. unfold buf_frame in FR1.
destruct (sy_data sy) as [p|] eqn:ED.
-
destruct DAT1 as (D0 & ARR & LEN & PRE & LE). rewrite CS in LEN. fold st in LEN.
specialize (INL ltac:(intros X; discriminate X)). fold st in INL.
destruct (live_below_lo RT AF Σ m1 D st lo ART1 INL LOW) as (_ & BD1 & _).
assert (FLS : 0 <= fl <= st).
{ destruct REP as (_ & _ & DAT & _). unfold sync_data in DAT. rewrite ED in DAT. destruct DAT as (_ & _ & LEN0 & _ & LE0).
fold st in LEN0. clear - CF I1 I2 LEN0 LE0. lia. }
assert (SEP' : D + st <= A \/ A + 32 <= D) by (destruct REP as (_ & _ & DAT & SEP0); unfold sync_data in DAT; rewrite ED in DAT; destruct DAT as (_ & _ & LEN0 & _); fold st in LEN0; rewrite <- LEN0; exact SEP0).
assert (DR : 0 < D < 2^64) by (clear - D0 BD1 Fs LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
apply u8arr_rw_CB in ARR.
destruct (Z_lt_ge_dec (st - fl) size) as [GROW|FITS].
+
set (ns := size + fl + 4096) in *.
assert (NS : 1 <= ns <= 64512) by (unfold ns; clear - NB CF SZ0 FLS; lia).
assert (BY1 : bytes_at bsegs m1 D bytes1) by (destruct ARR as [[_ B] _]; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B).
cps_norm. cps_hide.
cps_seg (buf_w2b A D st fl 0 size sy).
lazymatch type of POST with ?x = _ => subst x end.
cps_rt (REA Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 D st ns lo bytes1).
all: [> lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- unwind_ch _ _ _ _ => apply unwind_ok_ch; unfold unwind_ok, RA_buf_realloc; rewrite EU, !unsigned_lit by (clear - AR; lia);
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]
| |- mcost _ <= _ => unfold mcost; replace (ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia); exact CR0
| |- _ + _ + 80 <= _ => rewrite EU; ulc
| |- _ => first [ exact BY1 | exact LEN | exact LVM | lia ]
end .. | ].
intros kc3 (Σ1 & q & Hc3 & LV1 & FRS1 & SP1 & CR1 & Q0 & Q16 & QND & QTOP & PO1).
cps_unpack Hc3 as (m3 & RS3 & (ART3 & MI3 & ST3) & PRES3 & WRQ & ACQ & BYQ).
rewrite Z.min_l, <- LEN, Nat2Z.id, firstn_all in BYQ by lia.
destruct (fresh_block_u8arr m3 q ns bytes1 WRQ ltac:(lia) BYQ ltac:(lia)) as (junk & ARQ & LQ).
apply u8arr_rw_CB in ARQ.
pose proof LQ as LQ'. rewrite length_app, Nat2Z.inj_add in LQ'.
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m3 q ns lo ART3 INL LOW) as (_ & BQ1 & _).
destruct (frame_live_apart RT AF Σ1 m3 f k q ns ART3 INF INL) as (FLQ & _).
assert (SEPQ : q + ns <= A \/ A + 32 <= q) by (clear - FLQ FA1 FA2; lia).
assert (QR : 0 < q < 2^64) by (clear - Q0 BQ1 NS LOR SPT; lia).
cps_hide.
cps_seg (buf_w3b A D q st fl 0 ns usp lo sy j8).
destruct POST as (m4 & a1'' & -> & MU4 & WM4 & MI4 & ST4 & SY4). unfold sync_cells_c in SY4.
clear FR1 SY1. cps_seg_post.
apply Hk. exists Σ1, q. split.
2:{ split.
{ unfold sync_buffer_res. fold sy1. rewrite CS. fold st fl. replace (st - fl <? size) with true by (symmetry; apply Z.ltb_lt; lia). cbn [snd].
unfold sync_live. cbn [sy_data sy_storage]. intros _. exact INL. }
split; [right; rewrite <- CF; split; [lia| exact LV1]|].
split; [exact FRS1|]. split; [exact SP1|]. split; [| exact PO1].
rewrite CR1. unfold mcost. replace (ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia). apply Z.sub_0_r. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m4, (bytes1 ++ junk).
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI4 ST4))|]. split; [exact PF|].
unfold sync_buffer_res. fold sy1. rewrite CS. fold st fl. replace (st - fl <? size) with true by (symmetry; apply Z.ltb_lt; lia). cbn [snd].
split; [unfold sync_cells; cbn [sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]; rewrite CR, CU, CH, CB; exact SY4|].
split. { destruct CFOK as (_ & G2 & G3 & G4 & G5 & G6). unfold sync_fields_ok, int31 in *. cbn [sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]. fold ns. repeat split; try tauto; lia. }
split. { unfold sync_data. cbn [sy_data sy_buf sy_storage]. fold ns. apply u8arr_rw_CB in ARQ.
split; [lia|]. split; [exact ARQ|]. split; [exact LQ|].
split; [rewrite ubytes_app, firstn_app, (proj2 (Nat.sub_0_le _ _)) by (rewrite ubytes_length; exact LE); cbn [firstn]; rewrite app_nil_r; exact PRE|].
rewrite length_app. lia. }
rewrite LQ. cps_unhide. exact SEPQ.
+
cps_norm. cps_hide.
cps_seg (buf_w2a A D st fl 0 size usp lo sy j8).
destruct POST as (m2 & a1'' & -> & MU2 & WM2 & MI2 & ST2).
clear FR1. cps_seg_post.
apply Hk. exists Σ, D. split.
2:{ split.
{ unfold sync_buffer_res. fold sy1. rewrite CS. fold st fl. replace (st - fl <? size) with false by (symmetry; apply Z.ltb_ge; lia). cbn [snd].
unfold sync_live. rewrite CS. fold st. intros _. exact INL. }
split; [left; rewrite <- CF; split; [lia| split; reflexivity]|]. repeat split; reflexivity. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m2, bytes1.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI2 ST2))|]. split; [exact PF|].
unfold sync_buffer_res. fold sy1. rewrite CS. fold st fl. replace (st - fl <? size) with false by (symmetry; apply Z.ltb_ge; lia). cbn [snd].
split; [unfold sy1; rewrite <- sync_cells_compact; exact SY1|]. split; [exact CFOK|].
split; [unfold sync_data; rewrite CD, CS; apply u8arr_rw_CB in ARR; exact (conj D0 (conj ARR (conj LEN (conj PRE LE))))|].
rewrite LEN. cps_unhide. exact SEP'.
-
destruct DAT1 as (D0 & B0 & BUF0 & ST00). rewrite CS in ST00. subst D bytes1.
assert (FL0 : fl = 0).
{ destruct REP as (_ & _ & DAT & _). unfold sync_data in DAT. rewrite ED in DAT. destruct DAT as (_ & _ & BUF00 & _).
rewrite BUF00 in I2. cbn [length] in I2. clear - CF I1 I2. lia. }
destruct (Z_lt_ge_dec (st - fl) size) as [GROW|FITS].
+
set (ns := size + fl + 4096) in *.
assert (NS : 1 <= ns <= 64512) by (unfold ns; clear - NB CF SZ0 FL0; lia).
cps_norm.
cps_seg (buf_w2c A st fl 0 size sy).
destruct POST as (a1x & ->).
cps_rt (MAL Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 ns lo).
all: [> lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- unwind_ch _ _ _ _ => apply unwind_ok_ch; unfold unwind_ok, RA_buf_malloc; rewrite EU, !unsigned_lit by (clear - AR; lia);
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]
| |- mcost _ <= _ => unfold mcost; replace (ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia); exact CR0
| |- _ => first [ exact LVM | lia ]
end .. | ].
intros kc3 (Σ1 & q & Hc3 & LV1 & FRS1 & SP1 & CR1 & Q0 & Q16 & QTOP & PO1).
cps_unpack Hc3 as (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & WRQ & ACQ).
destruct (fresh_block_u8arr m3 q ns [] WRQ ltac:(lia) ltac:(apply bytes_at_nil; clear - Q0 QTOP NS; unfold USTACK_TOP in *; lia) ltac:(cbn; lia)) as (junk & ARQ & LQ).
cbn [app] in ARQ, LQ. apply u8arr_rw_CB in ARQ.
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m3 q ns lo ART3 INL0 LOW) as (_ & BQ1 & _).
destruct (frame_live_apart RT AF Σ1 m3 f k q ns ART3 INF INL0) as (FLQ & _).
assert (SEPQ : q + ns <= A \/ A + 32 <= q) by (clear - FLQ FA1 FA2; lia).
assert (QR : 0 < q < 2^64) by (clear - Q0 BQ1 NS LOR SPT; lia).
cps_hide.
cps_seg (buf_w3c A 0 q st fl 0 ns usp lo sy j8).
destruct POST as (m4 & a1y & -> & MU4 & WM4 & MI4 & ST4 & SY4). unfold sync_cells_c in SY4.
clear FR1 SY1. cps_seg_post.
apply Hk. exists Σ1, q. split.
2:{ split.
{ unfold sync_buffer_res. fold sy1. rewrite CS. fold st fl. replace (st - fl <? size) with true by (symmetry; apply Z.ltb_lt; lia). cbn [snd].
unfold sync_live. cbn [sy_data sy_storage]. intros _. exact INL0. }
split; [right; rewrite <- CF; split; [lia| exact LV1]|].
split; [exact FRS1|]. split; [exact SP1|]. split; [| exact PO1].
rewrite CR1. unfold mcost. replace (ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia). apply Z.sub_0_r. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m4, junk.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI4 ST4))|]. split; [exact PF|].
unfold sync_buffer_res. fold sy1. rewrite CS. fold st fl. replace (st - fl <? size) with true by (symmetry; apply Z.ltb_lt; lia). cbn [snd].
split; [unfold sync_cells; cbn [sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]; rewrite CR, CU, CH, CB; exact SY4|].
split. { destruct CFOK as (_ & G2 & G3 & G4 & G5 & G6). unfold sync_fields_ok, int31 in *. cbn [sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]. fold ns. repeat split; try tauto; lia. }
split. { unfold sync_data. cbn [sy_data sy_buf sy_storage]. fold ns. apply u8arr_rw_CB in ARQ.
split; [lia|]. split; [exact ARQ|]. split; [exact LQ|]. rewrite BUF0. cbn [length firstn]. split; [reflexivity| lia]. }
rewrite LQ. cps_unhide. exact SEPQ.
+
cps_norm.
cps_seg (buf_w2a A 0 st fl 0 size usp lo sy j8).
destruct POST as (m2 & a1x & -> & MU2 & WM2 & MI2 & ST2).
clear FR1. cps_seg_post.
apply Hk. exists Σ, 0. split.
2:{ split.
{ unfold sync_buffer_res. fold sy1. rewrite CS. fold st fl. replace (st - fl <? size) with false by (symmetry; apply Z.ltb_ge; lia). cbn [snd].
unfold sync_live. rewrite CD. intros X. exfalso. apply X. reflexivity. }
split; [left; rewrite <- CF; split; [lia| split; reflexivity]|]. repeat split; reflexivity. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m2, [].
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI2 ST2))|]. split; [exact PF|].
unfold sync_buffer_res. fold sy1. rewrite CS. fold st fl. replace (st - fl <? size) with false by (symmetry; apply Z.ltb_ge; lia). cbn [snd].
split; [unfold sy1; rewrite <- sync_cells_compact; exact SY1|]. split; [exact CFOK|].
split; [unfold sync_data; rewrite CD, CS; repeat split; assumption|].
cbn [length]. clear - A0. lia.
Qed.
End OggBufferCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.

Lemma bytes_at_prefix_eq : forall (m : mem) a (all pre : list byte),
bytes_at asegs m a all -> bytes_at asegs m a pre -> (length pre <= length all)%nat -> firstn (length pre) all = pre.
Proof.
intros m a all pre (_ & _ & HA) (_ & _ & HP) Hle. apply nth_error_ext. intros i. rewrite nth_error_firstn.
destruct (Nat.ltb_spec i (length pre)) as [Hi|Hi].
- rewrite <- (HA i ltac:(lia)), <- (HP i Hi). reflexivity.
- symmetry. apply nth_error_None. exact Hi.
Qed.

Lemma fresh_block_u8arr : forall (m : mem) q n (pre : list byte),
wr_at asegs m q n -> 0 <= n -> bytes_at asegs m q pre -> Z.of_nat (length pre) <= n ->
exists junk, u8arr asegs m q (pre ++ junk) /\ Z.of_nat (length (pre ++ junk)) = n.
Proof.
intros m q n pre WR N0 BP LE. destruct (wr_at_rw_CB m q n WR N0) as (all & BLK).
pose proof BLK as [[[LA _] BA] _]. cbn [cell_wf] in LA. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
pose proof (bytes_at_prefix_eq m q all pre BA BP ltac:(lia)) as E.
exists (skipn (length pre) all). split.
- rewrite <- E at 1. rewrite firstn_skipn. apply u8arr_rw_CB. rewrite LA. exact BLK.
- rewrite length_app, length_skipn, LA. lia.
Qed.

Definition sy_compact (sy : sync_st bptr) : sync_st bptr :=
if negb (sy_returned sy =? 0) then
mkSync (sy_data sy) (ztake (sy_fill sy - sy_returned sy) (zdrop (sy_returned sy) (sy_buf sy)))
(sy_storage sy) (sy_fill sy - sy_returned sy) 0 (sy_unsynced sy) (sy_headerbytes sy) (sy_bodybytes sy)
else sy.

Lemma compact_prefix : forall (buf : list Z) (bytes : list byte) (ret fill : nat),
firstn (length buf) (ubytes bytes) = buf -> (ret + fill <= length buf)%nat -> (length buf <= length bytes)%nat ->
firstn (length (firstn fill (skipn ret buf))) (ubytes (firstn fill (skipn ret bytes) ++ skipn fill bytes)) = firstn fill (skipn ret buf)
/\ (length (firstn fill (skipn ret buf)) <= length (firstn fill (skipn ret bytes) ++ skipn fill bytes))%nat.
Proof.
intros buf bytes ret fill Hpre Hrf Hlen.
assert (L1 : length (firstn fill (skipn ret buf)) = fill) by (rewrite firstn_length_le by (rewrite length_skipn; lia); reflexivity).
rewrite L1. split.
- rewrite ubytes_app, firstn_app, ubytes_firstn, ubytes_skipn, firstn_firstn, Nat.min_id.
rewrite firstn_length_le by (rewrite length_skipn, ubytes_length; lia). rewrite Nat.sub_diag, firstn_O, app_nil_r.
rewrite <- Hpre. rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia.
- rewrite length_app, firstn_length_le by (rewrite length_skipn; lia). lia.
Qed.

Definition sync_buffer_res (sy : sync_st bptr) (size : Z) : option (bptr * Z) * sync_st bptr :=
let sy1 := sy_compact sy in
if sy_storage sy1 - sy_fill sy1 <? size then
(Some (tt, sy_fill sy1),
mkSync (Some tt) (sy_buf sy1) (size + sy_fill sy1 + 4096) (sy_fill sy1) (sy_returned sy1) (sy_unsynced sy1) (sy_headerbytes sy1) (sy_bodybytes sy1))
else (match sy_data sy1 with Some p => Some (p, sy_fill sy1) | None => None end, sy1).

Lemma sync_buffer_prun : forall (sy : sync_st unit) size q r q',
prun (ogg_sync_buffer (St := pst) p_malloc p_realloc p_free sy size) q = Some (r, q') ->
0 <= sy_storage sy -> 0 <= size -> size + (sy_fill sy - sy_returned sy) + 4096 < 2^31 -> 0 <= sy_fill sy - sy_returned sy ->
r = sync_buffer_res sy size /\ q' = q.
Proof.
intros sy size q r q' H S0 Z0 NB F0. unfold ogg_sync_buffer, ogg_sync_check in H.
replace (sy_storage sy <? 0) with false in H by (symmetry; apply Z.ltb_ge; exact S0).
unfold sync_buffer_res, sy_compact, bptr in *.
destruct (negb (sy_returned sy =? 0)) eqn:ER; cbn [sy_storage sy_fill sy_data sy_buf sy_returned sy_unsynced sy_headerbytes sy_bodybytes] in H |- *.
- destruct (sy_storage sy - (sy_fill sy - sy_returned sy) <? size) eqn:EG.
+ replace (INT_MAX - 4096 - (sy_fill sy - sy_returned sy) <? size) with false in H by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
rewrite prun_bind in H.
assert (OV : p_overflows (size + (sy_fill sy - sy_returned sy) + 4096) = false) by (unfold p_overflows; apply Z.leb_gt; lia).
destruct (sy_data sy) as [[]|]; [rewrite (prun_realloc_ok tt _ _ OV) in H | rewrite (prun_malloc_ok _ _ OV) in H];
cbn beta iota in H; rewrite prun_ret in H; injection H as <- <-; split; reflexivity.
+ rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- destruct (sy_storage sy - sy_fill sy <? size) eqn:EG.
+ apply negb_false_iff, Z.eqb_eq in ER.
replace (INT_MAX - 4096 - sy_fill sy <? size) with false in H by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
rewrite prun_bind in H.
assert (OV : p_overflows (size + sy_fill sy + 4096) = false) by (unfold p_overflows; apply Z.leb_gt; lia).
destruct (sy_data sy) as [[]|]; [rewrite (prun_realloc_ok tt _ _ OV) in H | rewrite (prun_malloc_ok _ _ OV) in H];
cbn beta iota in H; rewrite prun_ret in H; injection H as <- <-; split; reflexivity.
+ rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Section OggBufferCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MAL : malloc_contract RT.
Hypothesis REA : realloc_contract RT.
Hypothesis MMOV : memmove_icontract RT e_memmove.

Definition sync_rest_live (sy : sync_st bptr) (D : Z) (live : list (Z * Z)) : list (Z * Z) :=
match sy_data sy with Some _ => live_remove D live | None => live end.

Lemma sync_rest_sub : forall sy D live e, In e (sync_rest_live sy D live) -> In e live.
Proof. intros sy D live e H. unfold sync_rest_live in H. destruct (sy_data sy); [exact (live_remove_sub _ _ _ H)| exact H]. Qed.

Lemma buf_phase1 : forall (Σ : rts RT) PMc (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A D size f lo usp : Z) (k : nat) (sy : sync_st bptr) (bytes : list byte),
fdfs_only PMc -> mat_stable PMc ->
sync_rep m A D sy bytes -> sync_inv sy -> 0 < A -> sync_live RT Σ sy D ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 32 <= f + fs_size k - 8 ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 112 <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
forall T c,
ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 usp) gp (Z_to_bv 64 0x630458) t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_ogg_sync_buffer) fc None m (seg_rom asegs))) c ->
(forall c1 (m1 : mem) (bytes1 j8 : list byte) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ASTA RT Σ PMc (eq (MS (mkR ra' (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x630458) t0' t1' t2' (Z_to_bv 64 A) (Z_to_bv 64 size)
(Z_to_bv 64 (sy_storage sy)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 PC_buf_p2) fc None m1 (seg_rom asegs))) c1 ->
ART RT Σ m1 -> mem_inv asegs m1 -> stk asegs m1 lo (usp + -32) ->
rw_cells asegs m1 (usp + -32) (buf_frame ra s0 s1 j8) ->
rw_cells asegs m1 A (sync_cells_c D (sy_storage sy) (sy_fill (sy_compact sy)) 0 sy) ->
sync_data m1 D (sy_compact sy) bytes1 ->
rt_pres_fp (sync_rest_live sy D (rt_live RT Σ)) (rt_frames RT Σ) usp [(A, A + 32)] m m1 ->
realizes asegs c1 T) ->
realizes asegs c T.
Proof using AF MMOV.
intros Σ PMc ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A D size f lo usp k sy bytes
FDO MST REP INV A0 INL INF FA1 FA2 ART0 MI0 ST0 LOW LOR SPT SPA T c Hc Hk.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
destruct REP as (SY & FOK & DAT & SEP).
pose proof FOK as (Fs & Ff & Fr & Fu & Fh & Fb). unfold int31 in Fs, Ff, Fr, Fu, Fh, Fb.
destruct INV as (I1 & I2 & I3 & I4 & I5).
set (LV := sync_rest_live sy D (rt_live RT Σ)) in *.
pose proof (pres_fp_refl LV (rt_frames RT Σ) usp [(A, A + 32)] m) as PF.
assert (SPL : forall a, aclient LV (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [apply sync_rest_sub| auto| apply Z.le_refl]. }
unfold sync_cells in SY. unfold sync_data in DAT.
destruct (sy_data sy) as [p|] eqn:ED.
2:{
destruct DAT as (-> & -> & BUF0 & ST00).
assert (RZ : sy_returned sy = 0) by (rewrite BUF0 in I2; unfold zlength in I2; cbn [length] in I2; clear - I1 I2; lia).
assert (EC : sy_compact sy = sy) by (unfold sy_compact; rewrite RZ; reflexivity).
cps_norm.
cps_seg (buf_w1a A 0 size usp lo sy).
destruct POST as (m1 & j8 & a1' & -> & MU1 & WM1 & MI1 & ST1 & FR1). unfold buf_frame in FR1.
cps_seg_post.
eapply (Hk _ m1 [] j8); [exact Hc0| exact ART| exact MI1| exact ST1| exact FR1| | |].
- rewrite EC. rewrite RZ in SY. exact SY.
- rewrite EC. unfold sync_data. rewrite ED. repeat split; assumption.
- exact PF. }
destruct DAT as (D0 & ARR & LEN & PRE & LE).
specialize (INL ltac:(rewrite ED; intros X; discriminate X)).
destruct (live_below_lo RT AF Σ m D (sy_storage sy) lo ART0 INL LOW) as (_ & BD1 & _).
assert (NAD : forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (D <= a < D + sy_storage sy)).
{ intros a Ha. unfold LV, sync_rest_live in Ha. rewrite ED in Ha. exact (aclient_remove_apart RT AF Σ m D (sy_storage sy) usp a ART0 INL LOU Ha). }
destruct (Z.eq_dec (sy_returned sy) 0) as [RZ|RNZ].
-
assert (EC : sy_compact sy = sy) by (unfold sy_compact; rewrite RZ; reflexivity).
apply u8arr_rw_CB in ARR.
cps_norm.
cps_seg (buf_w1a A D size usp lo sy).
destruct POST as (m1 & j8 & a1' & -> & MU1 & WM1 & MI1 & ST1 & FR1). unfold buf_frame in FR1.
cps_seg_post.
eapply (Hk _ m1 bytes j8); [exact Hc0| exact ART| exact MI1| exact ST1| exact FR1| | |].
+ rewrite EC. rewrite RZ in SY. exact SY.
+ rewrite EC. unfold sync_data. rewrite ED. apply u8arr_rw_CB in ARR. exact (conj D0 (conj ARR (conj LEN (conj PRE LE)))).
+ exact PF.
- assert (EC : sy_compact sy = mkSync (sy_data sy) (ztake (sy_fill sy - sy_returned sy) (zdrop (sy_returned sy) (sy_buf sy)))
(sy_storage sy) (sy_fill sy - sy_returned sy) 0 (sy_unsynced sy) (sy_headerbytes sy) (sy_bodybytes sy)).
{ unfold sy_compact. replace (sy_returned sy =? 0) with false by (symmetry; apply Z.eqb_neq; exact RNZ). reflexivity. }
unfold zlength in I2.
set (nr := Z.to_nat (sy_returned sy)). set (nf := Z.to_nat (sy_fill sy - sy_returned sy)).
destruct (compact_prefix (sy_buf sy) bytes nr nf PRE ltac:(unfold nr, nf; lia) LE) as (CP1 & CP2).
destruct (Z_le_gt_dec (sy_fill sy - sy_returned sy) 0) as [FZ|FP].
+
assert (NF0 : nf = 0%nat) by (unfold nf; lia).
apply u8arr_rw_CB in ARR.
cps_norm.
cps_seg (buf_w1b A D size usp lo sy).
destruct POST as (m1 & j8 & a1' & a2' & -> & MU1 & WM1 & MI1 & ST1 & FR1 & SY1). unfold buf_frame in FR1. unfold sync_cells_c in SY1.
clear SY. cps_seg_post.
eapply (Hk _ m1 bytes j8); [exact Hc0| exact ART| exact MI1| exact ST1| exact FR1| | |].
* rewrite EC. cbn [sy_fill]. exact SY1.
* rewrite EC. unfold sync_data. cbn [sy_data sy_buf sy_storage]. rewrite ED. apply u8arr_rw_CB in ARR.
split; [exact D0|]. split; [exact ARR|]. split; [exact LEN|].
unfold ztake. fold nf. rewrite NF0. cbn [firstn length]. split; [reflexivity| lia].
* exact PF.
+
set (b1 := firstn nf bytes). set (b2 := skipn nf bytes). set (bs := firstn nf (skipn nr bytes)).
assert (Lb1 : Z.of_nat (length b1) = sy_fill sy - sy_returned sy) by (unfold b1; rewrite firstn_length_le by (unfold nf, nr in *; lia); unfold nf; lia).
assert (LEQ : length bs = length b1) by (unfold bs, b1; rewrite !firstn_length_le by (rewrite ?length_skipn; unfold nf, nr in *; lia); reflexivity).
assert (Lb2 : Z.of_nat (length b2) = sy_storage sy - (sy_fill sy - sy_returned sy)) by (unfold b2; rewrite length_skipn; unfold nf, nr in *; lia).
assert (EB : bytes = b1 ++ b2) by (symmetry; apply firstn_skipn).
pose proof (bytes_at_sub m D bytes nr nf (proj1 ARR) ltac:(unfold nf, nr in *; lia)) as SRC. fold bs in SRC.
replace (D + Z.of_nat nr) with (D + sy_returned sy) in SRC by (unfold nr; lia).
rewrite EB in ARR. apply u8arr_app in ARR. destruct ARR as (P1 & P2). apply u8arr_rw_CB in P1, P2.
assert (SEP' : D + sy_storage sy <= A \/ A + 32 <= D) by (rewrite <- LEN; exact SEP). clear SEP.
assert (Lbs : Z.of_nat (length bs) = sy_fill sy - sy_returned sy) by (rewrite LEQ; exact Lb1).
assert (FST : sy_fill sy <= sy_storage sy) by (clear - I2 LE LEN; lia).
assert (DRT : D + sy_returned sy < 2^64) by (clear - BD1 I1 Ff Fs LOR SPT I2 LE LEN; unfold RT_STACK, USTACK_TOP in *; lia).
cps_norm. cps_hide.
cps_seg (buf_w1c A D size usp lo sy).
destruct POST as (m1 & j8 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & SY1). unfold buf_frame in FR1. unfold sync_cells_c in SY1.
clear SY. cps_seg_post.

assert (SUBLV : forall e, In e LV -> In e (rt_live RT Σ)) by (intros e He; exact (sync_rest_sub _ _ _ _ He)).
assert (NAD' : forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (D <= a < D + Z.of_nat (length bs))).
{ intros a Ha. specialize (NAD a Ha). clear - NAD Lbs FST I1. lia. }
pose proof (proj2 P1) as WR1. cbn [cells_size csize Nat.add] in WR1. rewrite Nat.add_0_r, <- LEQ in WR1.
assert (AR : 0 < A < 2^64) by (clear - A0 FA2 BF1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ulc).
rewrite <- Lbs in Hc0.
cps_rt (MMOV Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 D (D + sy_returned sy) bs lo).
all: [> .. | ].
all: lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- checked_src _ _ _ _ _ _ _ => idtac
| |- checked_dst _ _ _ _ _ _ => idtac
| |- _ => try (clear - BD1 D0 I1 Ff Fs LOR SPT Lbs FST; lia)
end.
{ apply (live_checked_src RT AF Σ m1 _ lo D (sy_storage sy)); [exact ART| exact INL| lia| lia| exact BD1]. }
{ apply (live_checked_dst RT AF Σ m1 _ D (sy_storage sy)); [exact ART| exact INL| lia| lia| exact WR1]. }
intros kc2 Hc2. unfold icpt_postF in Hc2.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2).
pose proof (ogg_bytes_piece m1 m2 D bs WR1 WM2 BY2) as P1'. clear BY2.

cps_seg (buf_w1d A D size sy (sy_fill sy - sy_returned sy) (sy_returned sy)).
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & SY3). unfold sync_cells_c in SY3.
clear SY1. cps_seg_post.
eapply (Hk _ m3 (bs ++ b2) j8); [exact Hc1| exact ART| exact MI3| exact ST2| exact FR1| | |].
* rewrite EC. cbn [sy_fill]. exact SY3.
* rewrite EC. unfold sync_data. cbn [sy_data sy_buf sy_storage]. rewrite ED.
split; [exact D0|]. split.
{ apply u8arr_app. split; [apply u8arr_rw_CB; exact P1'|]. rewrite LEQ. apply u8arr_rw_CB. exact P2. }
split; [rewrite length_app; clear - Lbs Lb2; lia|].
unfold ztake, zdrop. fold nr nf. exact (conj CP1 CP2).
* exact PF.
Qed.

Lemma sync_cells_compact : forall D (sy : sync_st bptr),
sync_cells_c D (sy_storage sy) (sy_fill (sy_compact sy)) 0 sy = sync_cells D (sy_compact sy).
Proof.
intros D sy. unfold sy_compact, sync_cells_c, sync_cells. destruct (Z.eqb_spec (sy_returned sy) 0) as [E|E]; cbn [negb]; [rewrite E|]; reflexivity.
Qed.
Lemma sy_compact_facts : forall (sy : sync_st bptr), sync_inv sy -> sync_fields_ok sy ->
sy_storage (sy_compact sy) = sy_storage sy /\ sy_data (sy_compact sy) = sy_data sy /\ sy_returned (sy_compact sy) = 0
/\ sy_fill (sy_compact sy) = sy_fill sy - sy_returned sy /\ sync_fields_ok (sy_compact sy)
/\ sy_unsynced (sy_compact sy) = sy_unsynced sy /\ sy_headerbytes (sy_compact sy) = sy_headerbytes sy /\ sy_bodybytes (sy_compact sy) = sy_bodybytes sy.
Proof.
intros sy (I1 & _) FOK. pose proof FOK as (Fs & Ff & Fr & Fu & Fh & Fb). unfold sy_compact, sync_fields_ok, int31 in *.
destruct (Z.eqb_spec (sy_returned sy) 0) as [E|E]; cbn [negb sy_storage sy_data sy_returned sy_fill sy_unsynced sy_headerbytes sy_bodybytes]; repeat split; lia.
Qed.

Definition ogg_sync_buffer_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A D size f lo : Z) (k : nat) (sy : sync_st bptr) (bytes : list byte),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 size -> tp = Z_to_bv 64 0x630458 ->
sync_rep m A D sy bytes -> sync_inv sy -> 0 < A -> sync_live RT Σ sy D ->
0 <= size -> size + (sy_fill sy - sy_returned sy) + 4096 <= 64512 -> sy_storage sy <= 64512 ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 32 <= f + fs_size k - 8 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 112 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_ogg_sync_buffer m)))
(fun c => exists (Σ' : rts RT) (D' : Z),
ASTA RT Σ' PMc (fun ms => exists m' (bytes' : list byte),
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
(Z_to_bv 64 (D' + sy_fill (sy_compact sy))) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (sync_rest_live sy D (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 32)] m m'
/\ sync_rep m' A D' (snd (sync_buffer_res sy size)) bytes') c
/\ sync_live RT Σ' (snd (sync_buffer_res sy size)) D'
/\ ((sy_storage sy - (sy_fill sy - sy_returned sy) >= size /\ D' = D /\ rt_live RT Σ' = rt_live RT Σ)
\/ (sy_storage sy - (sy_fill sy - sy_returned sy) < size
/\ rt_live RT Σ' = (D', size + (sy_fill sy - sy_returned sy) + 4096) :: sync_rest_live sy D (rt_live RT Σ)))
/\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem ogg_sync_buffer_ok : ogg_sync_buffer_cps.
Proof using AF MAL REA MMOV.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A D size f lo k sy bytes
FDO MST -> -> -> REP INV A0 INL SZ0 NB STB INF FA1 FA2 LVM CR0 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
pose proof REP as (_ & FOK & _ & SEP).
destruct (sy_compact_facts sy INV FOK) as (CS & CD & CR & CF & CFOK & CU & CH & CB).
apply (buf_phase1 Σ PMc ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A D size f lo usp k sy bytes
FDO MST REP INV A0 INL INF FA1 FA2 ART0 MI0 ST0 LOW LOR SPT SPA T c Hc).
clear Hc. intros c1 m1 bytes1 j8 ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Hc ART1 MI1 ST1 FR1 SY1 DAT1 PF.
set (sy1 := sy_compact sy) in *. set (fl := sy_fill sy1) in *. set (st := sy_storage sy) in *.
pose proof FOK as (Fs & Ff & Fr & _). unfold int31 in Fs, Ff, Fr. fold st in Fs.
pose proof INV as (I1 & I2 & _). unfold zlength in I2.
destruct (frame_below_lo RT AF Σ m1 f k lo ART1 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m1 f k ART1 INF) as (F0 & F64 & FIMG & _ & _ & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
assert (SUBLV : forall e, In e (sync_rest_live sy D (rt_live RT Σ)) -> In e (rt_live RT Σ)) by (intros e He; exact (sync_rest_sub _ _ _ _ He)).
assert (SPL : forall a, aclient (sync_rest_live sy D (rt_live RT Σ)) (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m1 usp a ART1). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUBLV| auto| apply Z.le_refl]. }
assert (AR : 0 < A < 2^64) by (clear - A0 FA2 BF1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; clear - LOR SPT BF3; unfold RT_STACK, USTACK_TOP, SH_HI in *; lia).
unfold sync_data in DAT1. rewrite CD in DAT1. unfold sync_live in INL. unfold sync_rest_live in *.
unfold sync_cells_c in SY1. unfold buf_frame in FR1.
destruct (sy_data sy) as [p|] eqn:ED.
-
destruct DAT1 as (D0 & ARR & LEN & PRE & LE). rewrite CS in LEN. fold st in LEN.
specialize (INL ltac:(intros X; discriminate X)). fold st in INL.
destruct (live_below_lo RT AF Σ m1 D st lo ART1 INL LOW) as (_ & BD1 & _).
assert (FLS : 0 <= fl <= st).
{ destruct REP as (_ & _ & DAT & _). unfold sync_data in DAT. rewrite ED in DAT. destruct DAT as (_ & _ & LEN0 & _ & LE0).
fold st in LEN0. clear - CF I1 I2 LEN0 LE0. lia. }
assert (SEP' : D + st <= A \/ A + 32 <= D) by (destruct REP as (_ & _ & DAT & SEP0); unfold sync_data in DAT; rewrite ED in DAT; destruct DAT as (_ & _ & LEN0 & _); fold st in LEN0; rewrite <- LEN0; exact SEP0).
assert (DR : 0 < D < 2^64) by (clear - D0 BD1 Fs LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
apply u8arr_rw_CB in ARR.
destruct (Z_lt_ge_dec (st - fl) size) as [GROW|FITS].
+
set (ns := size + fl + 4096) in *.
assert (NS : 1 <= ns <= 64512) by (unfold ns; clear - NB CF SZ0 FLS; lia).
assert (BY1 : bytes_at asegs m1 D bytes1) by (destruct ARR as [[_ B] _]; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B).
cps_norm. cps_hide.
cps_seg (buf_w2b A D st fl 0 size sy).
lazymatch type of POST with ?x = _ => subst x end.
cps_rt (REA Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 D st ns lo bytes1).
all: [> lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- unwind_ch _ _ _ _ => apply unwind_ok_ch; unfold unwind_ok, RA_buf_realloc; rewrite EU, !unsigned_lit by (clear - AR; lia);
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]
| |- mcost _ <= _ => unfold mcost; replace (ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia); exact CR0
| |- _ + _ + 80 <= _ => rewrite EU; ulc
| |- _ => first [ exact BY1 | exact LEN | exact LVM | lia ]
end .. | ].
intros kc3 (Σ1 & q & Hc3 & LV1 & FRS1 & SP1 & CR1 & Q0 & Q16 & QND & QTOP & PO1).
cps_unpack Hc3 as (m3 & RS3 & (ART3 & MI3 & ST3) & PRES3 & WRQ & ACQ & BYQ).
rewrite Z.min_l, <- LEN, Nat2Z.id, firstn_all in BYQ by lia.
destruct (fresh_block_u8arr m3 q ns bytes1 WRQ ltac:(lia) BYQ ltac:(lia)) as (junk & ARQ & LQ).
apply u8arr_rw_CB in ARQ.
pose proof LQ as LQ'. rewrite length_app, Nat2Z.inj_add in LQ'.
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m3 q ns lo ART3 INL LOW) as (_ & BQ1 & _).
destruct (frame_live_apart RT AF Σ1 m3 f k q ns ART3 INF INL) as (FLQ & _).
assert (SEPQ : q + ns <= A \/ A + 32 <= q) by (clear - FLQ FA1 FA2; lia).
assert (QR : 0 < q < 2^64) by (clear - Q0 BQ1 NS LOR SPT; lia).
cps_hide.
cps_seg (buf_w3b A D q st fl 0 ns usp lo sy j8).
destruct POST as (m4 & a1'' & -> & MU4 & WM4 & MI4 & ST4 & SY4). unfold sync_cells_c in SY4.
clear FR1 SY1. cps_seg_post.
apply Hk. exists Σ1, q. split.
2:{ split.
{ unfold sync_buffer_res. fold sy1. rewrite CS. fold st fl. replace (st - fl <? size) with true by (symmetry; apply Z.ltb_lt; lia). cbn [snd].
unfold sync_live. cbn [sy_data sy_storage]. intros _. exact INL. }
split; [right; rewrite <- CF; split; [lia| exact LV1]|].
split; [exact FRS1|]. split; [exact SP1|]. split; [| exact PO1].
rewrite CR1. unfold mcost. replace (ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia). apply Z.sub_0_r. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m4, (bytes1 ++ junk).
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI4 ST4))|]. split; [exact PF|].
unfold sync_buffer_res. fold sy1. rewrite CS. fold st fl. replace (st - fl <? size) with true by (symmetry; apply Z.ltb_lt; lia). cbn [snd].
split; [unfold sync_cells; cbn [sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]; rewrite CR, CU, CH, CB; exact SY4|].
split. { destruct CFOK as (_ & G2 & G3 & G4 & G5 & G6). unfold sync_fields_ok, int31 in *. cbn [sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]. fold ns. repeat split; try tauto; lia. }
split. { unfold sync_data. cbn [sy_data sy_buf sy_storage]. fold ns. apply u8arr_rw_CB in ARQ.
split; [lia|]. split; [exact ARQ|]. split; [exact LQ|].
split; [rewrite ubytes_app, firstn_app, (proj2 (Nat.sub_0_le _ _)) by (rewrite ubytes_length; exact LE); cbn [firstn]; rewrite app_nil_r; exact PRE|].
rewrite length_app. lia. }
rewrite LQ. cps_unhide. exact SEPQ.
+
cps_norm. cps_hide.
cps_seg (buf_w2a A D st fl 0 size usp lo sy j8).
destruct POST as (m2 & a1'' & -> & MU2 & WM2 & MI2 & ST2).
clear FR1. cps_seg_post.
apply Hk. exists Σ, D. split.
2:{ split.
{ unfold sync_buffer_res. fold sy1. rewrite CS. fold st fl. replace (st - fl <? size) with false by (symmetry; apply Z.ltb_ge; lia). cbn [snd].
unfold sync_live. rewrite CS. fold st. intros _. exact INL. }
split; [left; rewrite <- CF; split; [lia| split; reflexivity]|]. repeat split; reflexivity. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m2, bytes1.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI2 ST2))|]. split; [exact PF|].
unfold sync_buffer_res. fold sy1. rewrite CS. fold st fl. replace (st - fl <? size) with false by (symmetry; apply Z.ltb_ge; lia). cbn [snd].
split; [unfold sy1; rewrite <- sync_cells_compact; exact SY1|]. split; [exact CFOK|].
split; [unfold sync_data; rewrite CD, CS; apply u8arr_rw_CB in ARR; exact (conj D0 (conj ARR (conj LEN (conj PRE LE))))|].
rewrite LEN. cps_unhide. exact SEP'.
-
destruct DAT1 as (D0 & B0 & BUF0 & ST00). rewrite CS in ST00. subst D bytes1.
assert (FL0 : fl = 0).
{ destruct REP as (_ & _ & DAT & _). unfold sync_data in DAT. rewrite ED in DAT. destruct DAT as (_ & _ & BUF00 & _).
rewrite BUF00 in I2. cbn [length] in I2. clear - CF I1 I2. lia. }
destruct (Z_lt_ge_dec (st - fl) size) as [GROW|FITS].
+
set (ns := size + fl + 4096) in *.
assert (NS : 1 <= ns <= 64512) by (unfold ns; clear - NB CF SZ0 FL0; lia).
cps_norm.
cps_seg (buf_w2c A st fl 0 size sy).
destruct POST as (a1x & ->).
cps_rt (MAL Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 ns lo).
all: [> lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- unwind_ch _ _ _ _ => apply unwind_ok_ch; unfold unwind_ok, RA_buf_malloc; rewrite EU, !unsigned_lit by (clear - AR; lia);
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]
| |- mcost _ <= _ => unfold mcost; replace (ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia); exact CR0
| |- _ => first [ exact LVM | lia ]
end .. | ].
intros kc3 (Σ1 & q & Hc3 & LV1 & FRS1 & SP1 & CR1 & Q0 & Q16 & QTOP & PO1).
cps_unpack Hc3 as (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & WRQ & ACQ).
destruct (fresh_block_u8arr m3 q ns [] WRQ ltac:(lia) ltac:(apply bytes_at_nil; clear - Q0 QTOP NS; unfold USTACK_TOP in *; lia) ltac:(cbn; lia)) as (junk & ARQ & LQ).
cbn [app] in ARQ, LQ. apply u8arr_rw_CB in ARQ.
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m3 q ns lo ART3 INL0 LOW) as (_ & BQ1 & _).
destruct (frame_live_apart RT AF Σ1 m3 f k q ns ART3 INF INL0) as (FLQ & _).
assert (SEPQ : q + ns <= A \/ A + 32 <= q) by (clear - FLQ FA1 FA2; lia).
assert (QR : 0 < q < 2^64) by (clear - Q0 BQ1 NS LOR SPT; lia).
cps_hide.
cps_seg (buf_w3c A 0 q st fl 0 ns usp lo sy j8).
destruct POST as (m4 & a1y & -> & MU4 & WM4 & MI4 & ST4 & SY4). unfold sync_cells_c in SY4.
clear FR1 SY1. cps_seg_post.
apply Hk. exists Σ1, q. split.
2:{ split.
{ unfold sync_buffer_res. fold sy1. rewrite CS. fold st fl. replace (st - fl <? size) with true by (symmetry; apply Z.ltb_lt; lia). cbn [snd].
unfold sync_live. cbn [sy_data sy_storage]. intros _. exact INL0. }
split; [right; rewrite <- CF; split; [lia| exact LV1]|].
split; [exact FRS1|]. split; [exact SP1|]. split; [| exact PO1].
rewrite CR1. unfold mcost. replace (ns <=? 64512) with true by (symmetry; apply Z.leb_le; lia). apply Z.sub_0_r. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m4, junk.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI4 ST4))|]. split; [exact PF|].
unfold sync_buffer_res. fold sy1. rewrite CS. fold st fl. replace (st - fl <? size) with true by (symmetry; apply Z.ltb_lt; lia). cbn [snd].
split; [unfold sync_cells; cbn [sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]; rewrite CR, CU, CH, CB; exact SY4|].
split. { destruct CFOK as (_ & G2 & G3 & G4 & G5 & G6). unfold sync_fields_ok, int31 in *. cbn [sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]. fold ns. repeat split; try tauto; lia. }
split. { unfold sync_data. cbn [sy_data sy_buf sy_storage]. fold ns. apply u8arr_rw_CB in ARQ.
split; [lia|]. split; [exact ARQ|]. split; [exact LQ|]. rewrite BUF0. cbn [length firstn]. split; [reflexivity| lia]. }
rewrite LQ. cps_unhide. exact SEPQ.
+
cps_norm.
cps_seg (buf_w2a A 0 st fl 0 size usp lo sy j8).
destruct POST as (m2 & a1x & -> & MU2 & WM2 & MI2 & ST2).
clear FR1. cps_seg_post.
apply Hk. exists Σ, 0. split.
2:{ split.
{ unfold sync_buffer_res. fold sy1. rewrite CS. fold st fl. replace (st - fl <? size) with false by (symmetry; apply Z.ltb_ge; lia). cbn [snd].
unfold sync_live. rewrite CD. intros X. exfalso. apply X. reflexivity. }
split; [left; rewrite <- CF; split; [lia| split; reflexivity]|]. repeat split; reflexivity. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m2, [].
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [exact (conj ART (conj MI2 ST2))|]. split; [exact PF|].
unfold sync_buffer_res. fold sy1. rewrite CS. fold st fl. replace (st - fl <? size) with false by (symmetry; apply Z.ltb_ge; lia). cbn [snd].
split; [unfold sy1; rewrite <- sync_cells_compact; exact SY1|]. split; [exact CFOK|].
split; [unfold sync_data; rewrite CD, CS; repeat split; assumption|].
cbn [length]. clear - A0. lia.
Qed.
End OggBufferCPS.
