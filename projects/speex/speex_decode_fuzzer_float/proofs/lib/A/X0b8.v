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
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0ba.

From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X12b X0z5 X0wl X0wn X0wm X0ys X0x2 X0yt X0zq X11l X11k X0w7 X0yz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X11w.
Module B_TWIN.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X0j9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X09f OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X06d.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w7 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yz.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11w.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_sizes ::=
rewrite ?cells_size_sbp_hdr, ?cells_size_sbp_ptrs, ?cells_size_sbp_cfg, ?cells_size_sb_slots, ?app_length, ?cells_size_app, ?cells_size_f32, ?length_f32;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length, ?cells_size_f32, ?length_f32; cbn [length].

Definition sblB_Y (OUT : Z) (s : sbd_state bptr) (FS sub : Z) : Z := if sb_isave_ptr OUT s =? 0 then 0 else sb_isave_ptr OUT s + 8 * (FS * sub).

Lemma sblB_f32_win : forall (m : mem) A (ws : list word) (i k : nat), rw_cells bsegs m A (f32 ws) -> (i + k <= length ws)%nat ->
rw_cells bsegs m A (f32 (firstn i ws)) /\ rw_cells bsegs m (A + 4 * Z.of_nat i) (f32 (firstn k (skipn i ws)))
/\ rw_cells bsegs m (A + 4 * Z.of_nat i + 4 * Z.of_nat k) (f32 (skipn (i + k) ws)).
Proof.
intros m A ws i k H Hk.
destruct (rw_cells_f32_split bsegs m A ws i H) as [H1 H2]. rewrite length_firstn in H2. replace (Nat.min i (length ws)) with i in H2 by lia.
destruct (rw_cells_f32_split bsegs m _ (skipn i ws) k H2) as [H3 H4]. rewrite length_firstn, length_skipn in H4. replace (Nat.min k (length ws - i)) with k in H4 by lia.
rewrite skipn_skipn in H4. replace (k + i)%nat with (i + k)%nat in H4 by lia.
split; [exact H1|]. split; [replace (A + 4 * Z.of_nat i) with (A + Z.of_nat (4 * i)) by lia; exact H3|].
replace (A + 4 * Z.of_nat i + 4 * Z.of_nat k) with (A + Z.of_nat (4 * i) + Z.of_nat (4 * k)) by lia. exact H4.
Qed.
Lemma sblB_f32_join_win : forall (m : mem) A (l1 l2 l3 : list word), rw_cells bsegs m A (f32 l1) -> rw_cells bsegs m (A + 4 * Z.of_nat (length l1)) (f32 l2) ->
rw_cells bsegs m (A + 4 * Z.of_nat (length l1) + 4 * Z.of_nat (length l2)) (f32 l3) -> rw_cells bsegs m A (f32 (l1 ++ l2 ++ l3)).
Proof.
intros m A l1 l2 l3 H1 H2 H3. rewrite !f32_app. apply rw_cells_join; [exact H1|]. rewrite cells_size_f32.
replace (A + Z.of_nat (4 * length l1)) with (A + 4 * Z.of_nat (length l1)) by lia.
apply rw_cells_join; [exact H2|]. rewrite cells_size_f32. replace (A + 4 * Z.of_nat (length l1) + Z.of_nat (4 * length l2)) with (A + 4 * Z.of_nat (length l1) + 4 * Z.of_nat (length l2)) by lia. exact H3.
Qed.

Section DB.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MEMS : memset_icontract RT e_asan_memset.

Lemma sblB_dB : forall (Σ : rts RT) PMc (usp lo hb S OUT A f sf MODE fsz FS sub fh : Z) (kh : nat) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (ows : list word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs10 t3 t4 t5 t6 : word) F fc (m : mem),
fdfs_only PMc -> mat_stable PMc -> X1cn.frm0 fc ->
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells bsegs m S (sbp_hdr s a) -> rw_cells bsegs m (S + 40) (sbp_ptrs s a OUT) -> sbd_subframeSize s = FS ->
(FS = 40 \/ FS = 80) -> (fsz = 160 \/ fsz = 320) -> 0 <= sub < 4 -> (sb_isave_ptr OUT s = 0 \/ sb_isave_ptr OUT s = OUT + 8 * fsz) ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo -> lo <= usp + -1216 ->
0 < OUT -> OUT + 8000 < 2^63 -> OUT mod 4 = 0 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
rw_cells bsegs m OUT (f32 ows) -> length ows = 2000%nat -> acc bsegs m OUT 8000 ->
In (fh, kh) (rt_frames RT Σ) -> fh <= OUT -> OUT + 8000 <= fh + fs_size kh - 8 -> OUT + 8000 <= lo ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m (Z_to_bv 64 hb) lo -> hb + 32 <= usp + -1216 -> usp + 16 <= 140737488355328 -> 0 < hb < 2^63 ->
cps bsegs (ASTA RT Σ PMc (eq (MS (R_LB usp hb gp tp (Z_to_bv 64 RA_sblB_pois1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (FS * sub)) (Z_to_bv 64 (hb + 32)) (Z_to_bv 64 hb) (Z_to_bv 64 0) (Z_to_bv 64 (4 * FS)) (Z_to_bv 64 FS) xs10 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sblB_pois1)) fc None m (seg_rom bsegs))))
(fun c => exists Σ', ASTA RT Σ' PMc (fun ms => exists (m' : mem) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 : word) (F' : bvmap 5 word) (fc' : bv 32) (ows' : list word),
ms = MS (R_LB usp hb gp tp xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (FS * sub)) (Z_to_bv 64 (hb + 32)) (Z_to_bv 64 (sblB_Y OUT s FS sub)) xs5 (Z_to_bv 64 (4 * FS)) (Z_to_bv 64 FS) xs10
xt3 xt4 xt5 xt6) F' (Z_to_bv 64 SBLB_PC_B) fc' None m' (seg_rom bsegs)
/\ X1cn.frm0 fc' /\ rt_after RT Σ' hb lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) hb [(usp + -736, usp + -160); (OUT, OUT + 8000)] m m'
/\ rw_cells bsegs m' (usp + -736) (sb_slots usp S OUT A f sf MODE fsz (sbvB_544 v (Z_to_bv 64 hb)))
/\ rw_cells bsegs m' OUT (f32 ows') /\ length ows' = 2000%nat) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).
Proof.
intros Σ PMc usp lo hb S OUT A f sf MODE fsz FS sub fh kh v s a ows gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs10 t3 t4 t5 t6 F fc m
FDO MST FRM SL HD PT EFS HFS HFSZ SUB HIS OBS S8 SPOS SOFF SLO LO O0 O1 O4 LOS SPH U32 OUTC LOUT ACO INFH FH1 FH2 OUTLO ART0 MI0 COK HBU USPT HBB.
intros T c Hc Hk.
pose proof COK as (ST0 & LOWS & LRT & HTOP & H16).
assert (HB0 : 0 <= hb < 2^64) by (clear - HBB; lia).
rewrite unsigned_lit in ST0, LRT, HTOP, H16 by exact HB0.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) hb [(usp + -736, usp + -160); (OUT, OUT + 8000)] m) as PF.
pose proof (fun a0 => aclient_split RT AF Σ m hb a0 ART0) as SPL.
cps_norm. cps_hide.
cps_seg (sblB_e2 usp lo hb S OUT A f sf MODE fsz FS sub (sb_isave_ptr OUT s)).
destruct POST as (m1 & b0 & b1 & b2 & [[EIS ->] | [EIS ->]] & MU1 & WM1 & MI1 & SL1); clear SL.
-
cps_seg_post.
apply Hk. exists Σ. split; [| repeat split; reflexivity].
eapply ASTA_conseq; [eassumption|]. intros ms <-. do 20 eexists. exists ows.
split; [unfold sblB_Y; rewrite EIS; cbn [Z.eqb]; reflexivity|].
split; [eassumption|]. split; [split; [eassumption|]; split; [eassumption|]; split; [eassumption| eassumption]|].
split; [exact PF|]. split; [exact SL1|]. split; [exact OUTC| exact LOUT].
-
cps_seg_post.
assert (EIS2 : sb_isave_ptr OUT s = OUT + 8 * fsz) by (destruct HIS; [contradiction| assumption]).
rewrite EIS2 in *.
pose proof (HFS : _ \/ _) as HFS'. pose proof (HFSZ : _ \/ _) as HFSZ'.
assert (FSB : 40 <= FS <= 80 /\ 160 <= fsz <= 320) by (clear - HFS' HFSZ'; lia).
assert (WIN : (Z.to_nat (2 * fsz + 2 * (FS * sub)) + Z.to_nat (2 * FS) <= length ows)%nat) by (rewrite LOUT; clear - HFS' HFSZ' SUB; destruct HFS' as [-> | ->]; destruct HFSZ' as [-> | ->]; lia).
destruct (sblB_f32_win _ OUT ows _ _ OUTC WIN) as (OW1 & OW2 & OW3). clear OUTC.
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
clear EO1 EO2 EO3.

assert (OBO1 : aobj bsegs m1 OUT 8000).
{ assert (OBO : aobj bsegs m OUT 8000) by (split; [lia|]; split; [clear - OUTLO LO USPT; unfold APP_TOP; lia| exact ACO]).
assert (OF1 : offsh [(usp + -736, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; clear - LO LOS USPT SPH; lia).
exact (aobj_munch bsegs _ m m1 OUT 8000 OBO MU1 (shfree_of_aobj bsegs _ m OUT 8000 OF1 OBO)). }
pose proof OW2 as [_ WRW]. rewrite cells_size_f32 in WRW. replace (Z.of_nat (4 * length o2)) with (8 * FS) in WRW by lia.
cps_rt (MEMS Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (OUT + 8 * fsz + 8 * (FS * sub)) (8 * FS) z8 lo).
{ clear - OUTLO LO USPT FSB SUB O0; nia. }
{ unfold checked_dst. rewrite unsigned_lit by (clear - HBB; lia). split; [intros _; split|split].
- apply (acc_sub bsegs m1 OUT 8000); [exact (proj2 (proj2 OBO1))| clear - O0 FSB SUB; nia | clear - FSB SUB; nia].
- right; left. exists fh, kh. split; [exact INFH|]. split; [clear - FH1 FSB SUB O0; nia| clear - FH2 FSB SUB; nia].
- intros i Hi. right; right; right; left. exists fh, kh. split; [exact INFH|]. clear - FH1 FH2 Hi FSB SUB O0. nia.
- exact WRW. }
{ cps_callok. }
intros c2 Hc2.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BYW).
assert (OWz : exists wz, length wz = Z.to_nat (2 * FS) /\ rw_cells bsegs m2 (OUT + 8 * fsz + 8 * (FS * sub)) (f32 wz)).
{ apply (rw_cells_CB_f32 bsegs m2 _ (Z.to_nat (2 * FS)) (repeat z8 (Z.to_nat (8 * FS)))).
split; [split; [split; [cbn [cell_wf]; rewrite repeat_length; clear - FSB; lia| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BYW]|].
cbn [cells_size csize Nat.add]. replace (Z.of_nat (4 * Z.to_nat (2 * FS) + 0)) with (8 * FS) by (clear - FSB; lia).
exact (wr_at_transport bsegs m1 m2 _ _ WRW WM2). }
destruct OWz as (wz & Lwz & OWZ). clear WRW BYW.
assert (OUTC2 : rw_cells bsegs m2 OUT (f32 (o1 ++ wz ++ o3))).
{ apply sblB_f32_join_win; [exact OW1| rewrite LO1; replace (OUT + 4 * (2 * fsz + 2 * (FS * sub))) with (OUT + 8 * fsz + 8 * (FS * sub)) by (clear; lia); exact OWZ|].
rewrite LO1, Lwz. replace (OUT + 4 * (2 * fsz + 2 * (FS * sub)) + 4 * Z.of_nat (Z.to_nat (2 * FS))) with (OUT + 8 * fsz + 8 * (FS * sub) + 8 * FS) by (clear - FSB; lia). exact OW3. }
assert (LOUT2 : length (o1 ++ wz ++ o3) = 2000%nat) by (rewrite !length_app; clear - LO1 LO3 Lwz FSB SUB; nia).
clear OW1 OW3 OWZ.
cps_seg (sblB_e2b usp hb).
subst ms.
apply Hk. exists Σ. split; [| repeat split; reflexivity].
eapply ASTA_conseq; [eassumption|]. intros ms <-. do 20 eexists. exists (o1 ++ wz ++ o3).
split; [unfold sblB_Y; rewrite EIS2; replace (OUT + 8 * fsz =? 0) with false by (symmetry; apply Z.eqb_neq; clear - O0 FSB; lia); reflexivity|].
split; [eassumption|]. split; [split; [eassumption|]; split; [eassumption|]; split; [cps_wmono| eassumption]|].
split; [exact PF|]. split; [exact SL1|]. split; [exact OUTC2| exact LOUT2].
Qed.
End DB.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_sizes ::=
rewrite ?cells_size_sbp_hdr, ?cells_size_sbp_ptrs, ?cells_size_sbp_cfg, ?cells_size_sb_slots, ?app_length, ?cells_size_app, ?cells_size_f32, ?length_f32;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length, ?cells_size_f32, ?length_f32; cbn [length].

Definition sbl_Y (OUT : Z) (s : sbd_state bptr) (FS sub : Z) : Z := if sb_isave_ptr OUT s =? 0 then 0 else sb_isave_ptr OUT s + 8 * (FS * sub).

Lemma sbl_f32_win : forall (m : mem) A (ws : list word) (i k : nat), rw_cells asegs m A (f32 ws) -> (i + k <= length ws)%nat ->
rw_cells asegs m A (f32 (firstn i ws)) /\ rw_cells asegs m (A + 4 * Z.of_nat i) (f32 (firstn k (skipn i ws)))
/\ rw_cells asegs m (A + 4 * Z.of_nat i + 4 * Z.of_nat k) (f32 (skipn (i + k) ws)).
Proof.
intros m A ws i k H Hk.
destruct (rw_cells_f32_split asegs m A ws i H) as [H1 H2]. rewrite length_firstn in H2. replace (Nat.min i (length ws)) with i in H2 by lia.
destruct (rw_cells_f32_split asegs m _ (skipn i ws) k H2) as [H3 H4]. rewrite length_firstn, length_skipn in H4. replace (Nat.min k (length ws - i)) with k in H4 by lia.
rewrite skipn_skipn in H4. replace (k + i)%nat with (i + k)%nat in H4 by lia.
split; [exact H1|]. split; [replace (A + 4 * Z.of_nat i) with (A + Z.of_nat (4 * i)) by lia; exact H3|].
replace (A + 4 * Z.of_nat i + 4 * Z.of_nat k) with (A + Z.of_nat (4 * i) + Z.of_nat (4 * k)) by lia. exact H4.
Qed.
Lemma sbl_f32_join_win : forall (m : mem) A (l1 l2 l3 : list word), rw_cells asegs m A (f32 l1) -> rw_cells asegs m (A + 4 * Z.of_nat (length l1)) (f32 l2) ->
rw_cells asegs m (A + 4 * Z.of_nat (length l1) + 4 * Z.of_nat (length l2)) (f32 l3) -> rw_cells asegs m A (f32 (l1 ++ l2 ++ l3)).
Proof.
intros m A l1 l2 l3 H1 H2 H3. rewrite !f32_app. apply rw_cells_join; [exact H1|]. rewrite cells_size_f32.
replace (A + Z.of_nat (4 * length l1)) with (A + 4 * Z.of_nat (length l1)) by lia.
apply rw_cells_join; [exact H2|]. rewrite cells_size_f32. replace (A + 4 * Z.of_nat (length l1) + Z.of_nat (4 * length l2)) with (A + 4 * Z.of_nat (length l1) + 4 * Z.of_nat (length l2)) by lia. exact H3.
Qed.

Section DB.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MEMS : memset_icontract RT e_asan_memset.

Lemma sbl_dB : forall (Σ : rts RT) PMc (usp lo hb S OUT A f sf MODE fsz FS sub fh : Z) (kh : nat) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (ows : list word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
fdfs_only PMc -> mat_stable PMc -> X1cn.frm0 fc ->
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells asegs m S (sbp_hdr s a) -> rw_cells asegs m (S + 40) (sbp_ptrs s a OUT) -> sbd_subframeSize s = FS ->
(FS = 40 \/ FS = 80) -> (fsz = 160 \/ fsz = 320) -> 0 <= sub < 4 -> (sb_isave_ptr OUT s = 0 \/ sb_isave_ptr OUT s = OUT + 8 * fsz) ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo -> lo <= usp + -1088 ->
0 < OUT -> OUT + 8000 < 2^63 -> OUT mod 4 = 0 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
rw_cells asegs m OUT (f32 ows) -> length ows = 2000%nat -> acc asegs m OUT 8000 ->
In (fh, kh) (rt_frames RT Σ) -> fh <= OUT -> OUT + 8000 <= fh + fs_size kh - 8 -> OUT + 8000 <= lo ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m (Z_to_bv 64 hb) lo -> hb + 32 <= usp + -1088 -> usp + 16 <= 140737488355328 -> 0 < hb < 2^63 ->
cps asegs (ASTA RT Σ PMc (eq (MS (R_L usp hb S sub gp tp (Z_to_bv 64 RA_sbl_pois1) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (FS * sub)) (Z_to_bv 64 FS) (Z_to_bv 64 hb) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 OUT) (Z_to_bv 64 (hb + 32)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbl_pois1)) fc None m (seg_rom asegs))))
(fun c => exists Σ', ASTA RT Σ' PMc (fun ms => exists (m' : mem) (xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (F' : bvmap 5 word) (fc' : bv 32) (ows' : list word),
ms = MS (R_L usp hb S sub gp tp xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 (S + 80)) xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 (sbl_Y OUT s FS sub)) (Z_to_bv 64 FS) (Z_to_bv 64 (sha (S + 120))) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (hb + 32))
xt3 xt4 xt5 xt6) F' (Z_to_bv 64 SBL_PC_B) fc' None m' (seg_rom asegs)
/\ X1cn.frm0 fc' /\ rt_after RT Σ' hb lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) hb [(usp + -608, usp + -160); (OUT, OUT + 8000)] m m'
/\ rw_cells asegs m' (usp + -608) (sb_slots usp S OUT A f sf MODE fsz (sbv_416 v (Z_to_bv 64 hb)))
/\ rw_cells asegs m' OUT (f32 ows') /\ length ows' = 2000%nat) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).
Proof.
intros Σ PMc usp lo hb S OUT A f sf MODE fsz FS sub fh kh v s a ows gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m
FDO MST FRM SL HD PT EFS HFS HFSZ SUB HIS OBS S8 SPOS SOFF SLO LO O0 O1 O4 LOS SPH U32 OUTC LOUT ACO INFH FH1 FH2 OUTLO ART0 MI0 COK HBU USPT HBB.
intros T c Hc Hk.
pose proof COK as (ST0 & LOWS & LRT & HTOP & H16).
assert (HB0 : 0 <= hb < 2^64) by (clear - HBB; lia).
rewrite unsigned_lit in ST0, LRT, HTOP, H16 by exact HB0.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) hb [(usp + -608, usp + -160); (OUT, OUT + 8000)] m) as PF.
pose proof (fun a0 => aclient_split RT AF Σ m hb a0 ART0) as SPL.
cps_norm. cps_hide.
cps_seg (sbl_e2 usp lo hb S OUT A f sf MODE fsz FS sub (sb_isave_ptr OUT s)).
destruct POST as (m1 & [[EIS ->] | [EIS ->]] & MU1 & WM1 & MI1 & SL1); clear SL.
-
cps_seg_post.
apply Hk. exists Σ. split; [| repeat split; reflexivity].
eapply ASTA_conseq; [eassumption|]. intros ms <-. do 18 eexists. exists ows.
split; [unfold sbl_Y; rewrite EIS; cbn [Z.eqb]; reflexivity|].
split; [eassumption|]. split; [split; [eassumption|]; split; [eassumption|]; split; [eassumption| eassumption]|].
split; [exact PF|]. split; [exact SL1|]. split; [exact OUTC| exact LOUT].
-
cps_seg_post.
assert (EIS2 : sb_isave_ptr OUT s = OUT + 8 * fsz) by (destruct HIS; [contradiction| assumption]).
rewrite EIS2 in *.
pose proof (HFS : _ \/ _) as HFS'. pose proof (HFSZ : _ \/ _) as HFSZ'.
assert (FSB : 40 <= FS <= 80 /\ 160 <= fsz <= 320) by (clear - HFS' HFSZ'; lia).
assert (WIN : (Z.to_nat (2 * fsz + 2 * (FS * sub)) + Z.to_nat (2 * FS) <= length ows)%nat) by (rewrite LOUT; clear - HFS' HFSZ' SUB; destruct HFS' as [-> | ->]; destruct HFSZ' as [-> | ->]; lia).
destruct (sbl_f32_win _ OUT ows _ _ OUTC WIN) as (OW1 & OW2 & OW3). clear OUTC.
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
clear EO1 EO2 EO3.

assert (OBO1 : aobj asegs m1 OUT 8000).
{ assert (OBO : aobj asegs m OUT 8000) by (split; [lia|]; split; [clear - OUTLO LO USPT; unfold APP_TOP; lia| exact ACO]).
assert (OF1 : offsh [(usp + -608, usp + -160)]) by (cbn; unfold SH_LO, SH_HI; clear - LO LOS USPT SPH; lia).
exact (aobj_munch asegs _ m m1 OUT 8000 OBO MU1 (shfree_of_aobj asegs _ m OUT 8000 OF1 OBO)). }
pose proof OW2 as [_ WRW]. rewrite cells_size_f32 in WRW. replace (Z.of_nat (4 * length o2)) with (8 * FS) in WRW by lia.
cps_rt (MEMS Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (OUT + 8 * fsz + 8 * (FS * sub)) (8 * FS) z8 lo).
{ clear - OUTLO LO USPT FSB SUB O0; nia. }
{ unfold checked_dst. rewrite unsigned_lit by (clear - HBB; lia). split; [intros _; split|split].
- apply (acc_sub asegs m1 OUT 8000); [exact (proj2 (proj2 OBO1))| clear - O0 FSB SUB; nia | clear - FSB SUB; nia].
- right; left. exists fh, kh. split; [exact INFH|]. split; [clear - FH1 FSB SUB O0; nia| clear - FH2 FSB SUB; nia].
- intros i Hi. right; right; right; left. exists fh, kh. split; [exact INFH|]. clear - FH1 FH2 Hi FSB SUB O0. nia.
- exact WRW. }
{ cps_callok. }
intros c2 Hc2.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BYW).
assert (OWz : exists wz, length wz = Z.to_nat (2 * FS) /\ rw_cells asegs m2 (OUT + 8 * fsz + 8 * (FS * sub)) (f32 wz)).
{ apply (rw_cells_CB_f32 asegs m2 _ (Z.to_nat (2 * FS)) (repeat z8 (Z.to_nat (8 * FS)))).
split; [split; [split; [cbn [cell_wf]; rewrite repeat_length; clear - FSB; lia| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BYW]|].
cbn [cells_size csize Nat.add]. replace (Z.of_nat (4 * Z.to_nat (2 * FS) + 0)) with (8 * FS) by (clear - FSB; lia).
exact (wr_at_transport asegs m1 m2 _ _ WRW WM2). }
destruct OWz as (wz & Lwz & OWZ). clear WRW BYW.
assert (OUTC2 : rw_cells asegs m2 OUT (f32 (o1 ++ wz ++ o3))).
{ apply sbl_f32_join_win; [exact OW1| rewrite LO1; replace (OUT + 4 * (2 * fsz + 2 * (FS * sub))) with (OUT + 8 * fsz + 8 * (FS * sub)) by (clear; lia); exact OWZ|].
rewrite LO1, Lwz. replace (OUT + 4 * (2 * fsz + 2 * (FS * sub)) + 4 * Z.of_nat (Z.to_nat (2 * FS))) with (OUT + 8 * fsz + 8 * (FS * sub) + 8 * FS) by (clear - FSB; lia). exact OW3. }
assert (LOUT2 : length (o1 ++ wz ++ o3) = 2000%nat) by (rewrite !length_app; clear - LO1 LO3 Lwz FSB SUB; nia).
clear OW1 OW3 OWZ.
cps_seg (sbl_e2b usp hb S OUT A f sf MODE fsz FS sub).
subst ms.
apply Hk. exists Σ. split; [| repeat split; reflexivity].
eapply ASTA_conseq; [eassumption|]. intros ms <-. do 18 eexists. exists (o1 ++ wz ++ o3).
split; [unfold sbl_Y; rewrite EIS2; replace (OUT + 8 * fsz =? 0) with false by (symmetry; apply Z.eqb_neq; clear - O0 FSB; lia); reflexivity|].
split; [eassumption|]. split; [split; [eassumption|]; split; [eassumption|]; split; [cps_wmono| eassumption]|].
split; [exact PF|]. split; [exact SL1|]. split; [exact OUTC2| exact LOUT2].
Qed.
End DB.
