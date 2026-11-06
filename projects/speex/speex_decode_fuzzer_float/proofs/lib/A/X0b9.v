(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05q X05s X05u X05t
X081 X05l X05m X09f X06d X069 X082 X08y X0b1 X0b0 X05a X088.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0ba X0b8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_sizes ::=
rewrite ?cells_size_sbp_hdr, ?cells_size_sbp_ptrs, ?cells_size_sbp_cfg, ?cells_size_sb_slots, ?app_length, ?cells_size_app, ?cells_size_f32, ?length_f32;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length, ?cells_size_f32, ?length_f32; cbn [length].

Lemma sbl_e12a : forall (usp lo hb S OUT A f sf MODE fsz FS sub EX : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (exs ows : list word) (xs4 xra : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) -> v_248 v = Z_to_bv 64 (sha (S + 120)) ->
rw_cells asegs m S (sbp_hdr s a) -> sbd_subframeSize s = FS -> ((FS = 40 /\ fsz = 160) \/ (FS = 80 /\ fsz = 320)) -> 0 <= sub < 4 ->
rw_cells asegs m (S + 40) (sbp_ptrs s a OUT) -> (sb_isave_ptr OUT s = 0 \/ sb_isave_ptr OUT s = OUT + 8 * fsz) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
rw_cells asegs m EX (f32 exs) -> Z.of_nat (length exs) = FS -> aobj asegs m EX (4 * FS) -> EX mod 4 = 0 -> hb <= EX ->
rw_cells asegs m OUT (f32 ows) -> length ows = 2000%nat -> acc asegs m OUT 8000 -> 0 < OUT -> OUT mod 4 = 0 -> IMG_TOP <= OUT -> OUT + 8000 <= lo -> OUT + 8000 <= APP_TOP ->
(OUT + 8000 <= SH_LO \/ SH_HI <= OUT) -> (S + 160 <= OUT \/ OUT + 8000 <= S) ->
lo <= hb -> hb <= usp + -1088 -> SH_HI <= lo -> usp < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xa0 xa1 xa2 xa3 xa4 xa5 xs3' : word) (F' : bvmap 5 word) (ows' : list word),
ms = MS (R_L usp hb S sub gp tp xra t0 t1 t2 xa0 xa1 xa2 xa3 xa4 xa5 a6 a7
xs3' xs4 (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (sha (S + 28))) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 EX)
t3 t4 t5 t6) F' (Z_to_bv 64 SBL_PC_K) fc None m1 (seg_rom asegs)
/\ munch [(OUT, OUT + 8000)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 OUT (f32 ows') /\ length ows' = 2000%nat)
(MS (R_L usp hb S sub gp tp xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (sbl_Y OUT s FS sub)) xs4 (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 EX) t3 t4 t5 t6)
F (Z_to_bv 64 SBL_PC_J) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SL V248 HD EFS HFS SUB PT HIS OBS S8 SPOS SOFF SLO EXC LEX OBEX EX4 HBEX OUTC LOUT ACO O0 O4 OIMG OLO OAPP OOFF SEPSO LO HB LOS SPH MI.
assert (FSB : 40 <= FS <= 80 /\ 160 <= fsz <= 320 /\ fsz = 4 * FS) by (clear - HFS; lia).
unfold sbl_Y. destruct HIS as [EIS | EIS].
-
rewrite EIS. cbn [Z.eqb].
eapply evt_mono; [apply (sbl_e12a0 usp lo hb S OUT A f sf MODE fsz sub EX v s a (Z_to_bv 64 0) xs4 xra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m
SL V248 PT EIS OBS S8 SPOS SOFF SLO LO HB LOS SPH MI)|].
intros ms ->. exists m, (Z_to_bv 64 0), a1, a2, a3, a4, a5, (Z_to_bv 64 0), F, ows.
split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact OUTC| exact LOUT].
-
rewrite EIS. replace (OUT + 8 * fsz =? 0) with false by (symmetry; apply Z.eqb_neq; clear - O0 FSB; lia).
assert (WIN : (Z.to_nat (2 * fsz + 2 * (FS * sub)) + Z.to_nat (2 * FS) <= length ows)%nat) by (rewrite LOUT; clear - FSB SUB; nia).
destruct (sbl_f32_win _ OUT ows _ _ OUTC WIN) as (OW1 & OW2 & OW3).
replace (OUT + 4 * Z.of_nat (Z.to_nat (2 * fsz + 2 * (FS * sub)))) with (OUT + 8 * fsz + 8 * (FS * sub)) in OW2, OW3 by (clear - FSB SUB; nia).
replace (OUT + 8 * fsz + 8 * (FS * sub) + 4 * Z.of_nat (Z.to_nat (2 * FS))) with (OUT + 8 * fsz + 8 * (FS * sub) + 8 * FS) in OW3 by (clear - FSB SUB; nia).
assert (LO1 : Z.of_nat (length (firstn (Z.to_nat (2 * fsz + 2 * (FS * sub))) ows)) = 2 * fsz + 2 * (FS * sub)) by (rewrite length_firstn, LOUT; clear - FSB SUB; nia).
assert (LO2 : Z.of_nat (length (firstn (Z.to_nat (2 * FS)) (skipn (Z.to_nat (2 * fsz + 2 * (FS * sub))) ows))) = 2 * FS)
by (rewrite length_firstn, length_skipn, LOUT; clear - FSB SUB; nia).
assert (LO3 : Z.of_nat (length (skipn (Z.to_nat (2 * fsz + 2 * (FS * sub)) + Z.to_nat (2 * FS)) ows)) = 2000 - 2 * fsz - 2 * (FS * sub) - 2 * FS)
by (rewrite length_skipn, LOUT; clear - FSB SUB; nia).
remember (firstn (Z.to_nat (2 * fsz + 2 * (FS * sub))) ows) as o1 eqn:EO1.
remember (firstn (Z.to_nat (2 * FS)) (skipn (Z.to_nat (2 * fsz + 2 * (FS * sub))) ows)) as o2 eqn:EO2.
remember (skipn (Z.to_nat (2 * fsz + 2 * (FS * sub)) + Z.to_nat (2 * FS)) ows) as o3 eqn:EO3.
clear EO1 EO2 EO3 WIN.
assert (OBY : aobj asegs m (OUT + 8 * fsz + 8 * (FS * sub)) (8 * FS)).
{ split; [clear - O0 FSB SUB; nia|]. split; [clear - OAPP FSB SUB; nia|].
apply (acc_sub asegs m OUT 8000); [exact ACO| clear - FSB SUB; nia | clear - FSB SUB; nia]. }
assert (Y4 : (OUT + 8 * fsz + 8 * (FS * sub)) mod 4 = 0)
by (replace (OUT + 8 * fsz + 8 * (FS * sub)) with (OUT + (2 * fsz + 2 * (FS * sub)) * 4) by ring; rewrite Z_mod_plus_full; exact O4).
eapply evt_mono.
+ apply (sbl_e12a1 usp lo hb S OUT A f sf MODE fsz FS sub EX (OUT + 8 * fsz + 8 * (FS * sub)) v s a exs o2 xs4 xra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m
SL V248 HD EFS ltac:(clear - HFS; lia) PT ltac:(rewrite EIS; clear - O0 FSB; lia) ltac:(rewrite EIS; clear - O0 FSB OLO LO LOS SPH HB; unfold SH_HI in *; lia)
OBS S8 SPOS SOFF SLO EXC LEX OBEX EX4 HBEX OW2 LO2 OBY Y4 ltac:(clear - OIMG O0 FSB SUB; unfold IMG_TOP in *; nia)
ltac:(clear - OLO FSB SUB; nia) ltac:(clear - OOFF FSB SUB; nia) ltac:(clear - SEPSO FSB SUB; nia) LO HB LOS SPH MI).
+ intros ms (m1 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xs3' & F' & yw' & -> & MU & WM & MI1 & YC & LY).
exists m1, xa0, xa1, xa2, xa3, xa4, xa5, xs3', F', (o1 ++ yw' ++ o3).
assert (OF : forall x, outside [(OUT, OUT + 8000)] x -> outside [(OUT + 8 * fsz + 8 * (FS * sub), OUT + 8 * fsz + 8 * (FS * sub) + 8 * FS)] x)
by (intros x Hx; cbn [outside] in Hx |- *; destruct Hx as (Hx & _); split; [clear - Hx FSB SUB; nia | exact I]).
split; [reflexivity|]. split; [exact (munch_weaken _ _ _ _ OF MU)|]. split; [exact WM|]. split; [exact MI1|].
split.
* apply sbl_f32_join_win.
-- apply (rw_cells_transport asegs _ m m1 OUT _ OW1 MU WM). cbn [disjoint_from]. rewrite cells_size_f32. clear - LO1 FSB SUB. split; [|exact I]. nia.
-- rewrite LO1. replace (OUT + 4 * (2 * fsz + 2 * (FS * sub))) with (OUT + 8 * fsz + 8 * (FS * sub)) by (clear; lia). exact YC.
-- rewrite LO1. replace (OUT + 4 * (2 * fsz + 2 * (FS * sub)) + 4 * Z.of_nat (length yw')) with (OUT + 8 * fsz + 8 * (FS * sub) + 8 * FS) by (clear - LY; lia).
apply (rw_cells_transport asegs _ m m1 _ _ OW3 MU WM). cbn [disjoint_from]. rewrite cells_size_f32. clear - LO3 FSB SUB. split; [|exact I]. nia.
* rewrite !length_app. clear - LO1 LO3 LY FSB SUB. nia.
Qed.

Lemma sbl_scb_ok : forall n hs sbits (bb : bits_st bptr), bits_ok bb -> 0 <= sbits -> bits_ok (scb_bits n hs sbits bb) /\ sb_buf_size (scb_bits n hs sbits bb) = sb_buf_size bb.
Proof.
induction n as [|n IH]; intros hs sbits bb OKb Hs; cbn [scb_bits]; [split; [exact OKb| reflexivity]|].
destruct (negb (hs =? 0)).
- destruct (ub_ok bb 1 OKb ltac:(lia)) as (OK1 & SZ1 & _). destruct (ub_ok (ub bb 1) sbits OK1 Hs) as (OK3 & SZ3 & _).
destruct (IH hs sbits _ OK3 Hs) as (OK4 & SZ4). split; [exact OK4| rewrite SZ4, SZ3, SZ1; reflexivity].
- destruct (ub_ok bb sbits OKb Hs) as (OK3 & SZ3 & _). destruct (IH hs sbits _ OK3 Hs) as (OK4 & SZ4). split; [exact OK4| rewrite SZ4, SZ3; reflexivity].
Qed.
Lemma sbl_sbsub_ok : forall (b : bits_st bptr) sm mo id, bits_ok b -> (mo = ModeWB \/ mo = ModeUWB) -> 0 <= id <= 7 -> submode_at (sbm_submodes mo) id = Some sm ->
bits_ok (sbsub_bits sm b) /\ sb_buf_size (sbsub_bits sm b) = sb_buf_size b.
Proof.
intros b sm mo id OKb HMO HID SM.
destruct (ub_ok b 4 OKb ltac:(lia)) as (OK4 & SZ4 & _).
destruct (sb_submode_cases mo id sm HMO HID SM) as [(_ & [(_ & ->)|[(_ & ->)|[(_ & ->)|(_ & ->)]]]) | (_ & _ & ->)].
- destruct (ub_ok b 5 OKb ltac:(lia)) as (OK5 & SZ5 & _). exact (conj OK5 SZ5).
- unfold sbsub_bits. cbn [wb_submode2 sm_innovation_unquant sm_double_codebook Z.eqb negb innov_bits split_cb_high_lbr scb_nb_subvect scb_have_sign scb_shape_bits].
destruct (sbl_scb_ok (Z.to_nat 4) 0 5 (ub b 4) OK4 ltac:(lia)) as (O & Z). split; [exact O| rewrite Z; exact SZ4].
- unfold sbsub_bits. cbn [wb_submode3 sm_innovation_unquant sm_double_codebook Z.eqb negb innov_bits split_cb_high scb_nb_subvect scb_have_sign scb_shape_bits].
destruct (sbl_scb_ok (Z.to_nat 5) 1 7 (ub b 4) OK4 ltac:(lia)) as (O & Z). split; [exact O| rewrite Z; exact SZ4].
- unfold sbsub_bits. cbn [wb_submode4 sm_innovation_unquant sm_double_codebook Z.eqb Pos.eqb negb innov_bits split_cb_high scb_nb_subvect scb_have_sign scb_shape_bits].
destruct (sbl_scb_ok (Z.to_nat 5) 1 7 (ub b 4) OK4 ltac:(lia)) as (O & Z).
destruct (sbl_scb_ok (Z.to_nat 5) 1 7 _ O ltac:(lia)) as (O2 & Z2). split; [exact O2| rewrite Z2, Z; exact SZ4].
- destruct (ub_ok b 5 OKb ltac:(lia)) as (OK5 & SZ5 & _). exact (conj OK5 SZ5).
Qed.
