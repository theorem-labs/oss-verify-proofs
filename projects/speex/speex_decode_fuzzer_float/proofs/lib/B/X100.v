(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1df X1ck X1cu X1cv.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05l X05m X09f X06d X09e X091.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X12c X14x X0r0 X0ra X0v9 X0yr X12b X0z5 X0wl X0wn X0wm
X0ys X0x2 X0yt X0zq X0zp X0zl X0zu
X0yw X0z7 X0yc X0yb X101 X102 X0zw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NbG.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
Hypothesis L2F : lsp_to_lpc_cpsF RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MSTa : mat_stable PMc.
Variable X : @nbinvA bptr.
Hypothesis NXOK : nbx_ok X.
Hypothesis TP : x_tp X = Z_to_bv 64 0x638c98.
Variables (Σ0 : rts RT) (fr0 : list (Z * nat)) (PD ND fh : Z) (kh : nat).
Hypothesis NSIG : nbsig RT Σ0 X fr0 PD ND fh kh.
Local Notation ST := (x_st X). Local Notation OUT := (x_out X). Local Notation FF := (x_ff X). Local Notation SF := (x_sf X).
Local Notation lo := (x_lo X). Local Notation usp := (x_usp X). Local Notation nout := (x_nout X).

Definition nbW_G : list (Z * Z) := [(ST + 2080, ST + 2160); (ST + 2168, ST + 2184); (FF + 240, FF + 280); (FF + 992, FF + 1032); (OUT, OUT + 4 * Z.of_nat nout)].

Definition nbG_at (mG : mem) (crG : Z) (sG : nbslots) (rest : list byte) (oq qs : list word) (sub : Z) : config -> Prop :=
fun c => exists (Σ : rts RT) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 t3 t5 t6 : word) (iq msp pg aks iqs ows : list word),
ASTA RT Σ PMc (eq (MS (R_G usp ST FF sub (x_gp X) (x_tp X) xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 t3 t5 t6) Fx
(Z_to_bv 64 (if sub <? 4 then NBG_PC else NBH_PC)) fc None m (seg_rom bsegs))) c
/\ frm0 fc
/\ rt_live RT Σ = rt_live RT Σ0 /\ rt_frames RT Σ = rt_frames RT Σ0 /\ rt_sp0 RT Σ = rt_sp0 RT Σ0 /\ rt_credit RT Σ = crG /\ rt_pois RT Σ = rt_pois RT Σ0
/\ ART RT Σ m /\ mem_inv bsegs m /\ stk bsegs m lo (usp + -576) /\ wmono bsegs mG m
/\ rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp + -576) nbW_G mG m
/\ rw_cells bsegs m (usp + -576) (slot_cells sG)
/\ rw_cells bsegs m (ST + 2040) (f32 oq) /\ rw_cells bsegs m (ST + 2080) (f32 iq) /\ length iq = 10%nat
/\ rw_cells bsegs m (ST + 2120) (f32 msp) /\ length msp = 10%nat /\ rw_cells bsegs m (ST + 2168) (f32 pg) /\ length pg = 4%nat
/\ rw_cells bsegs m (FF + 160) (f32 qs) /\ rw_cells bsegs m (FF + 240) (f32 aks) /\ length aks = 10%nat
/\ rw_cells bsegs m (FF + 992) (f32 iqs) /\ length iqs = 10%nat
/\ rw_cells bsegs m OUT (f32 ows) /\ length ows = nout
/\ rw_cells bsegs m SF (nbd_shadow SC_F rest)
/\ (sub = 4 -> s3 = Z_to_bv 64 (FF + 240) /\ s7 = Z_to_bv 64 (OUT + 160 * 3)).

Lemma nbsh_acc_F : forall (m : mem) (F0 S0 : Z) rest, rw_cells bsegs m S0 (nbd_shadow SC_F rest) -> S0 = Z.shiftr F0 3 + SHB -> F0 mod 64 = 0 -> 0 <= F0 ->
acc bsegs m (F0 + 160) 40 /\ acc bsegs m (F0 + 240) 40 /\ acc bsegs m (F0 + 992) 40.
Proof.
intros m F0 S0 rest SH ESF F64 FPOS.
split; [| split].
- pose proof (shadow_acc m F0 S0 _ (firstn 20 (nbd_shadow_bytes SC_F)) (skipn 25 (nbd_shadow_bytes SC_F) ++ rest ++ []) 5 SH) as H.
cbn in H. apply H; [reflexivity| exact ESF| exact F64| exact FPOS].
- pose proof (shadow_acc m F0 S0 _ (firstn 30 (nbd_shadow_bytes SC_F)) (skipn 35 (nbd_shadow_bytes SC_F) ++ rest ++ []) 5 SH) as H.
cbn in H. apply H; [reflexivity| exact ESF| exact F64| exact FPOS].
- pose proof (shadow_acc m F0 S0 _ (firstn 124 (nbd_shadow_bytes SC_F)) (skipn 129 (nbd_shadow_bytes SC_F) ++ rest ++ []) 5 SH) as H.
cbn in H. apply H; [reflexivity| exact ESF| exact F64| exact FPOS].
Qed.

Lemma cells_size_nbd_shadow : forall sc rest, cells_size (nbd_shadow sc rest) = 256%nat.
Proof. intros [[] [] [] [] []] rest; reflexivity. Qed.

Local Ltac simpl_sizes ::=
rewrite ?cells_size_nbd_shadow;
rewrite ?app_length, ?cells_size_app, ?cells_size_f32, ?length_f32;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length, ?cells_size_f32, ?length_f32; cbn [length].

Lemma nbG_acc_pres : forall (Σ : rts RT) (m0 m m' : mem) sp W fp kp P n,
ART RT Σ m0 -> In (fp, kp) (rt_frames RT Σ) -> fp <= P -> P + n <= fp + fs_size kp - 8 ->
rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) sp W m m' -> (forall x, SH_LO <= x < SH_HI -> outside W x) ->
acc bsegs m P n -> acc bsegs m' P n.
Proof using AF.
intros Σ m0 m m' sp W fp kp P n ART0 INF F1 F2 PRES OFF ACC i Hi. destruct (ACC i Hi) as (b & B & OK). exists b. split; [| exact OK].
pose proof (frame_facts RT AF Σ m0 fp kp ART0 INF) as (FP0 & FP64 & _ & _ & _ & _ & SA & S1 & S2 & _).
assert (FSZ : 0 <= fs_size kp) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (R : shad fp <= shad (P + i) < shad (fp + fs_size kp)).
{ unfold shad. split; [assert (fp / 8 <= (P + i) / 8) by (apply Z.div_le_mono; lia); lia|].
assert ((P + i) / 8 < (fp + fs_size kp) / 8); [| lia].
assert (E8 : (fp + fs_size kp) mod 8 = 0).
{ unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. clear - FP64. set (q := 2 ^ Z.of_nat kp). assert (fp mod 8 = 0) by (Z.div_mod_to_equations; lia).
rewrite Z.add_mod, H by lia. change 64 with (8 * 8). rewrite <- Z.mul_assoc, Z.mul_comm, Z.mod_mul by lia. reflexivity. }
clear - E8 F2 Hi. Z.div_mod_to_equations. lia. }
apply (bytes_at_agree bsegs m m' _ _ B). intros a Ha. cbn [length] in Ha.
apply PRES; [right; right; right; right; exists fp, kp; split; [exact INF| lia]|].
apply OFF. rewrite SA in R. lia.
Qed.

Lemma nbG_live_checked_dst : forall (Σ : rts RT) (m : mem) sp p k d n,
ART RT Σ m -> In (p, k) (rt_live RT Σ) -> p <= d -> d + n <= p + k -> wr_at bsegs m d n -> checked_dst RT Σ m sp d n.
Proof using AF.
intros Σ m sp p k d n ART0 INL H1 H2 WR. split; [intros _; split| split; [| exact WR]].
- apply (acc_sub bsegs m p k d n (proj2 (af_acc_live RT AF Σ m p k ART0 INL)) H1 H2).
- left. exists p, k. split; [exact INL| lia].
- intros i Hi. right; right; left. exists p, k. split; [exact INL| lia].
Qed.
Lemma nbG_frame_checked_src : forall (Σ : rts RT) (m : mem) sp lo f k s n,
In (f, k) (rt_frames RT Σ) -> f <= s -> s + n <= f + fs_size k - 8 -> acc bsegs m s n -> s + n <= lo -> checked_src RT Σ m sp lo s n.
Proof.
intros Σ m sp lo f k s n INF H1 H2 ACC H3. split; [intros _; split| left; lia].
- exact ACC.
- right; left. exists f, k. split; [exact INF| lia].
Qed.

Lemma nbG_iter : forall (mG : mem) (crG : Z) (sG : nbslots) (rest : list byte) (oq qs : list word) (sub : Z),
0 <= sub < 4 -> length oq = 10%nat -> length qs = 10%nat ->
v280 sG = Z_to_bv 64 (ST + 2040) -> v272 sG = Z_to_bv 64 (FF + 160) -> v240 sG = Z_to_bv 64 OUT -> v304 sG = Z_to_bv 64 0 ->
v344 sG = Z_to_bv 64 (FF + 244) -> v336 sG = Z_to_bv 64 (18446744073709551615 - (ST + 2168)) -> v328 sG = Z_to_bv 64 (ST + 2120) ->
v152 sG = Z_to_bv 64 (FF + 240) -> acc bsegs mG OUT (4 * Z.of_nat nout) ->
cps bsegs (nbG_at mG crG sG rest oq qs sub) (nbG_at mG crG sG rest oq qs (sub + 1)).
Proof.
intros mG crG sG rest oq qs sub SUB LOQ LQS E280 E272 E240 E304 E344 E336 E328 E152 ACO T c Hc Hk.
destruct Hc as (Σ & Fx & fc & m & xra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s7 & t3 & t5 & t6 & iq & msp & pg & aks & iqs & ows
& Hc & FRM & LV & FRS & SP0 & CR & POI & ART0 & MI0 & ST0 & WM0 & PF & SL & OQ & IQ & LIQ & MSP & LMSP & PG & LPG & QS & AK & LAK & IQS & LIQS & OW & LOW & SH & S37).
replace (if sub <? 4 then NBG_PC else NBH_PC) with NBG_PC in Hc by (destruct (Z.ltb_spec sub 4); [reflexivity| lia]).
pose proof NXOK as (U32 & SPH & LOS & LOU & F0 & F64 & ESF & FLO & FTOP & FSH & SF0 & SF1 & SFLO & S8 & SPOS & SLO & SSH & SIMG & O4 & OTOP & OLO & NOUT & OSH
& A8 & ATOP & ALO & ASH & D0 & DLO & DSZ & STE4 & STETOP & STELO & STESH & ISV & SOA & SAA & SDA & SSTA & SFA & SSFA & OAA & ODA & OSTA & OFA & OSFA
& ADA & ASTA & AFA & ASFA & DSTA & DFA & DSFA & STEFA & STESFA & FSFA).
pose proof NSIG as (NFR & NLS & NLD & PD1 & PD2 & PDS & NFH & FHO1 & FHO2 & FHA1 & FHA2 & FHS1 & FHS2 & NPOIS & NLOW & NROOM & NTOP).

assert (INL : In (ST, NBSTATE_SIZEOF) (rt_live RT Σ)) by (rewrite LV; exact NLS).
assert (INF : In (FF, NBD_FCLASS) (rt_frames RT Σ)) by (rewrite FRS, NFR; left; reflexivity).
destruct (af_acc_live RT AF Σ m ST NBSTATE_SIZEOF ART0 INL) as (_ & ACS).
pose proof (nbsh_acc_F m FF SF rest SH ESF F64 ltac:(lia)) as (ACQ & ACK & ACI).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
unfold NBSTATE_SIZEOF, NBD_FRAME, NBD_CALLEE_STACK, RT_STACK in *.
assert (OBO : aobj bsegs m (ST + 2040) 40) by (split; [lia|]; split; [unfold APP_TOP, IMG_TOP_B, USTACK_TOP in *; lia| exact (acc_sub bsegs m ST 2968 (ST + 2040) 40 ACS ltac:(lia) ltac:(lia))]).
assert (OBN : aobj bsegs m (FF + 160) 40) by (split; [lia|]; split; [unfold APP_TOP, IMG_TOP_B, USTACK_TOP in *; lia| exact ACQ]).
assert (OBQ : aobj bsegs m (FF + 992) 40) by (split; [lia|]; split; [unfold APP_TOP, IMG_TOP_B, USTACK_TOP in *; lia| exact ACI]).

cps_norm. cps_hide.
cps_seg (nbg_1 usp lo ST OUT FF sub oq qs iqs (x_gp X) (x_tp X) xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 t3 t5 t6 sG Fx fc m).
{ unfold IMG_TOP_B in OTOP. lia. }
{ clear - OLO NOUT LOU SPH. lia. }

destruct POST as (m1 & F1 & fc1 & xt0 & xt1 & xt2 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & iqs1 & FRM1 & MU1 & WM1 & MI1 & ST1 & IQS1 & LIQS1 & ->).
clear IQS LIQS FRM.
change hidp with hid in *.
assert (LOWS : rt_sp0 RT Σ - STACK_WIN <= lo) by (rewrite SP0; exact NLOW).
pose proof (fun a0 => aclient_split RT AF Σ m (usp + -576) a0 ART0) as SPL.
rewrite <- LV, <- FRS in PF.
assert (ART1 : ART RT Σ m1).
{ apply (af_frame RT AF Σ m m1 lo ART0 LOWS); [| exact WM1]. intros a Ha; apply MU1; cbn [outside]; repeat split; intros Hin; apply Ha; aclient_tac ltac:(ulc). }
unfold nbW_G in PF. cps_pf_seg m m1 MU1.
clear ART0. seg_transport m m1 MU1 WM1. try match goal with MI : mem_inv bsegs m |- _ => clear MI end.

pose proof (nbsh_acc_F m1 FF SF rest SH ESF F64 ltac:(lia)) as (ACQ1 & ACK1 & ACI1).
assert (POA : pois_above (rt_pois RT Σ) (usp + -576)) by (rewrite POI; apply (pois_above_le _ (usp - 576)); [exact NPOIS| lia]).
cps_rt (L2F Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m1 (FF + 992) (FF + 240) lo FF NBD_FCLASS iqs1 aks).
{ fs_lit; lia. }
{ fs_lit; lia. }
{ rewrite unsigned_lit by ulc; exact POA. }
{ rewrite unsigned_lit by ulc; exact ST1. }
{ rewrite unsigned_lit by ulc; unfold RT_STACK; lia. }
{ rewrite unsigned_lit by ulc; unfold USTACK_TOP in *; lia. }
{ rewrite unsigned_lit by ulc; clear - U32; Z.div_mod_to_equations; lia. }

intros c2 (Σ2 & Hc2 & LV2 & FRS2 & SP2 & CR2 & POI2).
cps_unpack_lib Hc2 as (v2 & m2 & aks2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & AK2 & LAK2 & ACI2 & ACK2).

assert (INFH : In (fh, kh) (rt_frames RT Σ)) by (rewrite FRS, NFR; right; exact NFH).
assert (ESF8 : FF / 8 + SHB = SF) by (rewrite ESF, Z.shiftr_div_pow2 by lia; reflexivity).
assert (ESF8' : (FF + 2048) / 8 + SHB = SF + 256) by (rewrite <- ESF8; clear - F64; Z.div_mod_to_equations; lia).
assert (SHD1 : shad FF = SF) by (unfold shad; exact ESF8).
assert (SHD2 : shad (FF + 2048) = SF + 256) by (unfold shad; exact ESF8').

try clear Hc0. clear AK LAK ACQ1 ACK1 ACI1 ACQ ACK ACI.
replace (FF + 240 + 40) with (FF + 280) in PRES2 by lia.
cps_tr_lib PRES2.
cps_pf_lib PRES2 SPL.

cps_sigma LV2 FRS2 SP2.
assert (NO160 : (160 <= nout)%nat) by exact NOUT.
destruct (nbe_f32_win m2 OUT ows (Z.to_nat (40 * sub)) 40 OW ltac:(lia)) as (OW1 & OW2 & OW3). clear OW.
replace (OUT + 4 * Z.of_nat (Z.to_nat (40 * sub))) with (OUT + 160 * sub) in OW2, OW3 by lia.
change (4 * Z.of_nat 40) with 160 in OW3.
remember (firstn (Z.to_nat (40 * sub)) ows) as ow1 eqn:EOW1. remember (skipn (Z.to_nat (40 * sub) + 40) ows) as ow3 eqn:EOW3.
assert (LOW1 : Z.of_nat (length ow1) = 40 * sub) by (subst ow1; rewrite length_firstn; lia).
assert (LOW3 : Z.of_nat (length ow3) = Z.of_nat nout - 40 * sub - 40) by (subst ow3; rewrite length_skipn; lia).
assert (ACO2 : acc bsegs m2 OUT (4 * Z.of_nat nout)).
{ apply (nbG_acc_pres Σ2 m2 mG m2 (usp + -576) [(ST + 2080, ST + 2160); (ST + 2168, ST + 2184); (FF + 240, FF + 280); (FF + 992, FF + 1032); (OUT, OUT + 4 * Z.of_nat nout)] fh kh OUT (4 * Z.of_nat nout) ART2 INFH FHO1); [exact FHO2| rewrite LV2, FRS2; exact PF| | exact ACO].
intros x Hx. cbn [outside]. pose proof (SSH : _ \/ _) as U1. pose proof (FSH : _ \/ _) as U2. pose proof (OSH : _ \/ _) as U3.
unfold SH_LO, SH_HI in *. repeat split; lia. }
assert (OBX2 : aobj bsegs m2 (OUT + 160 * sub) 160)
by (split; [unfold IMG_TOP_B in OTOP; lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact (acc_sub bsegs m2 OUT (4 * Z.of_nat nout) (OUT + 160 * sub) 160 ACO2 ltac:(lia) ltac:(lia))]).

assert (LXO : length (firstn 40 (skipn (Z.to_nat (40 * sub)) ows)) = 40%nat) by (rewrite length_firstn, length_skipn; lia).
cps_seg (nbg_2 usp lo ST OUT FF sub aks2 pg (firstn 40 (skipn (Z.to_nat (40 * sub)) ows)) iq msp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sG _ _ m2).
{ unfold IMG_TOP_B in OTOP. lia. }
{ unfold hidp, SH_LO, SH_HI. pose proof (OSH : _ \/ _) as U. unfold SH_LO, SH_HI in U. clear - U NOUT SUB. lia. }
{ unfold hidp. pose proof (SOA : _ \/ _) as U. unfold NBSTATE_SIZEOF. clear - U NOUT SUB. lia. }
{ unfold hidp. pose proof (OFA : _ \/ _) as U. clear - U NOUT SUB. lia. }
{ destruct (af_acc_live RT AF Σ2 m2 ST 2968 ART2 INL) as (_ & ACS2). split; [lia|]. split; [unfold NBSTATE_SIZEOF, APP_TOP, USTACK_TOP in *; lia| exact ACS2]. }
{ pose proof (af_live_small RT AF Σ2 m2 ST 2968 ART2 INL ltac:(lia)) as SM. unfold SEGTOP_A in SM. unfold IMG_TOP_B. lia. }
{ exact (af_client_consts RT AF Σ2 m2 ART2). }

destruct POST as (m3 & F3 & fc3 & yt0 & yt1 & yt2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt5 & yt6 & pg3 & xo3 & msp3 & iq3
& FRM3 & MU3 & WM3 & MI3 & ST3 & PG3 & LPG3 & XO3 & LXO3 & MSP3 & LMSP3 & IQ3 & LIQ3 & AK3 & ->).
clear PG MSP OW2 IQ AK2 FRM1 RS2.
cps_seg_post.

cps_seg (nbg_3 usp ST OUT FF sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3).
destruct POST as (a0n & [(SUB3 & ->) | (SUB3 & ->)]).

- apply Hk. exists Σ2, F3, fc3, m3. do 17 eexists. exists iq3, msp3, pg3, aks2, iqs1, (ow1 ++ xo3 ++ ow3).
split; [replace (sub + 1 <? 4) with true by (symmetry; apply Z.ltb_lt; lia); eassumption|].
split; [exact FRM3|].
split; [rewrite LV2; exact LV|]. split; [rewrite FRS2; exact FRS|]. split; [rewrite SP2; exact SP0|]. split; [rewrite CR2; exact CR|]. split; [rewrite POI2; exact POI|].
split; [eassumption|]. split; [exact MI3|]. split; [exact ST3|]. split; [cps_wmono|].
split; [rewrite <- LV, <- FRS; unfold nbW_G; exact PF|].
split; [exact SL|]. split; [exact OQ|]. split; [exact IQ3|]. split; [exact LIQ3|]. split; [exact MSP3|]. split; [exact LMSP3|].
split; [exact PG3|]. split; [exact LPG3|]. split; [exact QS|]. split; [exact AK3|]. split; [exact LAK2|]. split; [exact IQS1|]. split; [exact LIQS1|].
split; [apply nbe_f32_join_win; [exact OW1| rewrite LOW1; replace (OUT + 4 * (40 * sub)) with (OUT + 160 * sub) by lia; exact XO3| rewrite LOW1, LXO3; replace (OUT + 4 * (40 * sub) + 4 * Z.of_nat 40) with (OUT + 160 * sub + 160) by lia; exact OW3]|].
split; [rewrite !length_app; lia|]. split; [exact SH|]. intros E; lia.

- apply Hk. replace (sub + 1) with 4 by lia. exists Σ2, F3, fc3, m3. do 17 eexists. exists iq3, msp3, pg3, aks2, iqs1, (ow1 ++ xo3 ++ ow3).
split; [replace (4 <? 4) with false by reflexivity; eassumption|].
split; [exact FRM3|].
split; [rewrite LV2; exact LV|]. split; [rewrite FRS2; exact FRS|]. split; [rewrite SP2; exact SP0|]. split; [rewrite CR2; exact CR|]. split; [rewrite POI2; exact POI|].
split; [eassumption|]. split; [exact MI3|]. split; [exact ST3|]. split; [cps_wmono|].
split; [rewrite <- LV, <- FRS; unfold nbW_G; exact PF|].
split; [exact SL|]. split; [exact OQ|]. split; [exact IQ3|]. split; [exact LIQ3|]. split; [exact MSP3|]. split; [exact LMSP3|].
split; [exact PG3|]. split; [exact LPG3|]. split; [exact QS|]. split; [exact AK3|]. split; [exact LAK2|]. split; [exact IQS1|]. split; [exact LIQS1|].
split; [apply nbe_f32_join_win; [exact OW1| rewrite LOW1; replace (OUT + 4 * (40 * sub)) with (OUT + 160 * sub) by lia; exact XO3| rewrite LOW1, LXO3; replace (OUT + 4 * (40 * sub) + 4 * Z.of_nat 40) with (OUT + 160 * sub + 160) by lia; exact OW3]|].
split; [rewrite !length_app; lia|]. split; [exact SH|]. intros _; split; [reflexivity| rewrite SUB3; reflexivity].
Qed.

Lemma nbG_loop : forall (n : nat) (mG : mem) (crG : Z) (sG : nbslots) (rest : list byte) (oq qs : list word) (sub : Z),
Z.of_nat n + sub = 4 -> 0 <= sub -> length oq = 10%nat -> length qs = 10%nat ->
v280 sG = Z_to_bv 64 (ST + 2040) -> v272 sG = Z_to_bv 64 (FF + 160) -> v240 sG = Z_to_bv 64 OUT -> v304 sG = Z_to_bv 64 0 ->
v344 sG = Z_to_bv 64 (FF + 244) -> v336 sG = Z_to_bv 64 (18446744073709551615 - (ST + 2168)) -> v328 sG = Z_to_bv 64 (ST + 2120) ->
v152 sG = Z_to_bv 64 (FF + 240) -> acc bsegs mG OUT (4 * Z.of_nat nout) ->
cps bsegs (nbG_at mG crG sG rest oq qs sub) (nbG_at mG crG sG rest oq qs 4).
Proof.
induction n as [|n IH]; intros mG crG sG rest oq qs sub HN H0 LOQ LQS E280 E272 E240 E304 E344 E336 E328 E152 ACO.
- replace sub with 4 by lia. apply cps_refl.
- eapply cps_seq; [apply nbG_iter; try assumption; lia|].
apply IH; try assumption; lia.
Qed.

Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Hypothesis MC : multicomb_cps RT.
Hypothesis HP : highpass_cps RT.
Variable mE : mem.
Variables (r : smrec) (mo olp : Z).
Local Notation A := (x_A X). Local Notation STEREO := (x_stereo X).

Local Notation nbEH_sig := (X0zw.nbEH_sig RT Σ0).
Local Notation nbEH_mem := (X0zw.nbEH_mem RT X Σ0 mE).
Local Notation R_EX := (X0zw.R_EX X).
Local Notation at_EXc := (X0zw.at_EXc RT PMc X Σ0 mE r mo olp).

Lemma nbG_tabs_acc_art : forall (Σ : rts RT) (m : mem), ART RT Σ m -> nb_tabs_acc m.
Proof using AF.
intros Σ m A0.
assert (K : forall a n, In (a, n) ACC_LITS -> 0 <= a -> a + n <= APP_TOP -> aobj bsegs m a n) by (intros a n; exact (aobj_lit RT AF Σ m a n A0)).
split.
- apply K; [unfold ACC_LITS, A_nb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_nb_mode; lia | unfold A_nb_mode, APP_TOP; lia].
- unfold nb_smrecs, nb_smrec1, nb_smrec2, nb_smrec3, nb_smrec4, nb_smrec5, nb_smrec6, nb_smrec7, nb_smrec8.
repeat (apply Forall_cons; [cbv beta; cbn [smr_ptr];
unfold A_nb_submode1, A_nb_submode2, A_nb_submode3, A_nb_submode4, A_nb_submode5, A_nb_submode6, A_nb_submode7, A_nb_submode8;
apply K; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | lia | unfold APP_TOP; lia]|]). apply Forall_nil.
Qed.

Lemma nbG_acc_pres2 : forall (Σ : rts RT) (m0 m m' : mem) sp W fp kp P n,
ART RT Σ m0 -> In (fp, kp) (rt_frames RT Σ) -> fp <= P -> P + n <= fp + fs_size kp - 8 ->
rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) sp W m m' -> (forall i, 0 <= i < n -> outside W (shad (P + i))) ->
acc bsegs m P n -> acc bsegs m' P n.
Proof using AF.
intros Σ m0 m m' sp W fp kp P n ART0 INF F1 F2 PRES OFF ACC i Hi. destruct (ACC i Hi) as (b & B & OK). exists b. split; [| exact OK].
pose proof (frame_facts RT AF Σ m0 fp kp ART0 INF) as (FP0 & FP64 & _ & _ & _ & _ & SA & S1 & S2 & _).
assert (FSZ : 0 <= fs_size kp) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (R : shad fp <= shad (P + i) < shad (fp + fs_size kp)).
{ unfold shad. split; [assert (fp / 8 <= (P + i) / 8) by (apply Z.div_le_mono; lia); lia|].
assert ((P + i) / 8 < (fp + fs_size kp) / 8); [| lia].
assert (E8 : (fp + fs_size kp) mod 8 = 0).
{ unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. clear - FP64. set (q := 2 ^ Z.of_nat kp). assert (fp mod 8 = 0) by (Z.div_mod_to_equations; lia).
rewrite Z.add_mod, H by lia. change 64 with (8 * 8). rewrite <- Z.mul_assoc, Z.mul_comm, Z.mod_mul by lia. reflexivity. }
clear - E8 F2 Hi. Z.div_mod_to_equations. lia. }
apply (bytes_at_agree bsegs m m' _ _ B). intros a Ha. cbn [length] in Ha.
apply PRES; [right; right; right; right; exists fp, kp; split; [exact INF| lia]|].
replace (bv_unsigned a) with (shad (P + i)) by lia. apply OFF. exact Hi.
Qed.

Lemma nbEH_off_shadow : forall (ST0 OUT0 A0 FF0 SF0 usp0 lo0 nout0 P n i : Z),
SF0 = FF0 / 8 + SHB -> FF0 mod 64 = 0 -> 0 <= P -> P + n <= 2^47 -> (P + n <= FF0 \/ FF0 + 2048 <= P) -> 0 <= i < n ->
(ST0 + 2968 <= SH_LO \/ SH_HI <= ST0) -> (OUT0 + nout0 <= SH_LO \/ SH_HI <= OUT0) -> (A0 + 48 <= SH_LO \/ SH_HI <= A0) -> (FF0 + 2048 <= SH_LO \/ SH_HI <= FF0) ->
SH_HI <= lo0 -> lo0 <= usp0 - 576 ->
outside [(ST0, ST0 + 2968); (OUT0, OUT0 + nout0); (A0, A0 + 48); (FF0, FF0 + 2048); (SF0, SF0 + 256); (usp0 - 576, usp0)] (shad (P + i)).
Proof.
intros ST0 OUT0 A0 FF0 SF0 usp0 lo0 nout0 P n i ESF F64 P0 P1 PFA Hi SSH OSH ASH FSH LOS LOU.
assert (SW : SH_LO <= shad (P + i) < SH_HI) by (apply shad_window; unfold APP_TOP; Lia.lia).
assert (SHS : shad (P + i) < SF0 \/ SF0 + 256 <= shad (P + i)) by (unfold shad; rewrite ESF; clear - PFA Hi F64; Z.div_mod_to_equations; Lia.lia).
cbn [outside]. split; [clear - SW SSH; Lia.lia|]. split; [clear - SW OSH; Lia.lia|]. split; [clear - SW ASH; Lia.lia|]. split; [clear - SW FSH; Lia.lia|].
split; [clear - SHS; Lia.lia|]. split; [clear - SW LOS LOU; Lia.lia| exact I].
Qed.

Hypothesis NACCE : nbacc X mE.

Lemma nbEH_acc_out : forall (Σ : rts RT) (m m' : mem), ART RT Σ m -> rt_frames RT Σ = rt_frames RT Σ0 ->
rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (usp + -576)
[(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + BITS_SIZEOF); (FF, FF + 2048); (SF, SF + 256); (usp - 576, usp)] mE m' ->
nbacc X m'.
Proof using AF NXOK NSIG NACCE.
intros Σ m m' ART0 FRS PF.
pose proof NXOK as (U32 & SPH & LOS & LOU & F0 & F64 & ESF & FLO & FTOP & FSH & SF0 & SF1 & SFLO & S8 & SPOS & SLO & SSH & SIMG & O4 & OTOP & OLO & NOUT & OSH
& A8 & ATOP & ALO & ASH & D0 & DLO & DSZ & STE4 & STETOP & STELO & STESH & ISV & SOA & SAA & SDA & SSTE & SFA & SSFA & OAA & ODA & OSTE & OFA & OSFA
& ADA & ASTE & AFA & ASFA & DSTE & DFA & DSFA & STEFA & STESFA & FSFA).
pose proof NSIG as (NFR & NLS & NLD & PD1 & PD2 & PDS & NFH & FHO1 & FHO2 & FHA1 & FHA2 & FHS1 & FHS2 & NPOIS & NLOW & NROOM & NTOP).
assert (INFH : In (fh, kh) (rt_frames RT Σ)) by (rewrite FRS, NFR; right; exact NFH).
assert (ESF8 : SF = FF / 8 + SHB) by (rewrite ESF, Z.shiftr_div_pow2 by lia; reflexivity).
destruct NACCE as (ACO & ACA & ACS).
unfold hidp, BITS_SIZEOF, NBD_FRAME in *.
split; [| split].
- apply (nbG_acc_pres2 Σ m mE m' (usp + -576) _ fh kh (x_out X) (4 * Z.of_nat (x_nout X)) ART0 INFH FHO1 FHO2 PF); [| exact ACO].
intros i Hi. refine (nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat (x_nout X)) (x_out X) (4 * Z.of_nat (x_nout X)) i ESF8 F64 _ _ OFA Hi SSH OSH ASH FSH LOS LOU).
+ clear - OTOP. unfold IMG_TOP_B in OTOP. Lia.lia.
+ clear - OLO LOU NTOP. unfold USTACK_TOP in NTOP. Lia.lia.
- apply (nbG_acc_pres2 Σ m mE m' (usp + -576) _ fh kh (x_A X) 48 ART0 INFH FHA1 FHA2 PF); [| exact ACA].
intros i Hi. refine (nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat (x_nout X)) (x_A X) 48 i ESF8 F64 _ _ AFA Hi SSH OSH ASH FSH LOS LOU).
+ clear - ATOP. unfold IMG_TOP_B in ATOP. Lia.lia.
+ clear - ALO LOU NTOP. unfold USTACK_TOP in NTOP. Lia.lia.
- apply (nbG_acc_pres2 Σ m mE m' (usp + -576) _ fh kh (x_stereo X) 8 ART0 INFH FHS1 FHS2 PF); [| exact ACS].
intros i Hi. refine (nbEH_off_shadow ST OUT A FF SF usp lo (4 * Z.of_nat (x_nout X)) (x_stereo X) 8 i ESF8 F64 _ _ STEFA Hi SSH OSH ASH FSH LOS LOU).
+ clear - STETOP. unfold IMG_TOP_B in STETOP. Lia.lia.
+ clear - STELO LOU NTOP. unfold USTACK_TOP in NTOP. Lia.lia.
Qed.

Ltac nbg_base t := lazymatch t with ?x + _ => nbg_base x | _ => t end.
Ltac nbg_cls_with tac :=
lazymatch goal with |- aclient ?L ?Fr ?sp ?x =>
unfold aclient; cps_unf;
first [ left; tac
| right; right; left; match goal with H : In (?p, ?n) L |- _ => exists p, n; split; [exact H | tac] end
| right; right; right; left; match goal with H : In (?f, ?k) Fr |- _ => exists f, k; split; [exact H | fs_lit; tac] end
| right; right; right; right; match goal with H : In (?f, ?k) Fr |- _ => exists f, k; split; [exact H | fs_lit; tac] end ]
end.
Ltac nbg_cls := first [ nbg_cls_with ltac:(llia) | nbg_cls_with ltac:(cllia) ].
Ltac nbg_out1 :=
cps_unf;
first [ llia
| match goal with Hx : ?A <= ?x < _ |- ~ (?d <= ?x < _) =>
let a := nbg_base A in let b := nbg_base d in
match goal with H : hid ?P |- _ => match P with context [a] => match P with context [b] =>
let U := fresh "U" in pose proof (H : P) as U; llia end end end
end
| cllia ].
Ltac nbg_trp PRES :=
lazymatch type of PRES with
| rt_pres_ex ?live ?frames ?sp ?d ?n ?m ?m' =>
lazymatch goal with WM : wmono bsegs m m' |- _ =>
repeat match goal with
| H : rw_cells bsegs m ?A ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : rw_cells bsegs m' A cs)
by (apply (rw_cells_agree bsegs m m' A cs H); [ apply (agree_of_pres_ex live frames sp d n m m' _ PRES); intros ?x ?Hx; cps_sizes Hx; split; [nbg_cls | nbg_out1] | exact WM ]);
clear H; rename H' into H
| idtac "note: nbg_trp dropping" H; clear H ]
end end
end.
Ltac nbg_trfp PRES :=
lazymatch type of PRES with
| rt_pres_fp ?live ?frames ?sp ?W ?m ?m' =>
lazymatch goal with WM : wmono bsegs m m' |- _ =>
repeat match goal with
| H : rw_cells bsegs m ?A ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : rw_cells bsegs m' A cs)
by (apply (rw_cells_agree bsegs m m' A cs H);
[ apply (agree_of_pres_fp live frames sp W m m' _ PRES); intros ?x ?Hx; cps_sizes Hx; split; [nbg_cls | cbn [outside]; repeat split; nbg_out1]
| exact WM ]);
clear H; rename H' into H
| idtac "note: nbg_trfp dropping" H; clear H ]
end end
end.

Lemma nbFGH : forall (bp : Z) (st : nb_state bptr) (b : bits_st bptr),
NBD_EH_CREDIT <= rt_credit RT Σ0 -> (length (rt_frames RT Σ0) < FRAMES_MAX)%nat ->
cps bsegs (at_EXc bp st b)
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms' => at_X_A X 0 (nb_end st) b ms' /\ nbEH_mem Σ' (ms_mem ms')) c
/\ rt_live RT Σ' = rt_live RT Σ0 /\ rt_frames RT Σ' = rt_frames RT Σ0 /\ rt_sp0 RT Σ' = rt_sp0 RT Σ0
/\ rt_credit RT Σ0 - NBD_EH_CREDIT <= rt_credit RT Σ' <= rt_credit RT Σ0 /\ rt_pois RT Σ' = rt_pois RT Σ0).
Proof.
intros bp st b CRD FRMX T c Hc Hk.
destruct Hc as (Σ & Fx & fc & m & xra & t0 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & s2 & s3 & s4 & s7 & s9 & t3 & t4 & t5 & t6 & j & ows & sws & s & ff
& Hc & FRM & CTX & SLE & E112 & SMR & EMO & BP & (ART0 & NACC & WM0 & PF) & (LV & FRS & SP0 & CR & POI)).
destruct CTX as (MI0 & ST0 & NBP & JOK & CBOK & INV & BREP & BOK & BSZ & OW & LOW & SW & LSW & (SL & SV) & FFA & FFOK & (rest & SH) & CC & LC & JEXC & JISV).
destruct NBP as (HDR & EXB & EXP & OQ & IQ & MSP & MHP & PG & ISP & LVL & LPP & PGB & IDX & SEED & CFG & CBS & UCB & VOC & TL).
destruct FFA as (FF0 & FPI & FPG & FLPC & FQS & FAK & FIN & FE32 & FIN2 & FIQ).
destruct JOK as (LEXB & LOQ & LIQ & LMSP & LMHP & LPG & LLVL & LPGB & LPAD1 & LCBS & LUCB & LVOC & LPAD2).
destruct FFOK as (LFPG & LFLPC & LFQS & LFAK & LFIN & LFE32 & LFIN2 & LFIQ).
destruct NACC as (ACO & ACA & ACSTE).
pose proof NXOK as (U32 & SPH & LOS & LOU & F0 & F64 & ESF & FLO & FTOP & FSH & SF0 & SF1 & SFLO & S8 & SPOS & SLO & SSH & SIMG & O4 & OTOP & OLO & NOUT & OSH
& A8 & ATOP & ALO & ASH & D0 & DLO & DSZ & STE4 & STETOP & STELO & STESH & ISV & SOA & SAA & SDA & SSTE & SFA & SSFA & OAA & ODA & OSTE & OFA & OSFA
& ADA & ASTE & AFA & ASFA & DSTE & DFA & DSFA & STEFA & STESFA & FSFA).
pose proof NSIG as (NFR & NLS & NLD & PD1 & PD2 & PDS & NFH & FHO1 & FHO2 & FHA1 & FHA2 & FHS1 & FHS2 & NPOIS & NLOW & NROOM & NTOP).
change hidp with hid in *.

unfold nb_cfg_cells in CFG. unfold nb_tail_cells in TL. unfold nb_ucb_cells, cb_cells in UCB.
destruct BREP as ((rjb & Lrjb & BOBJ) & (bsb & BDAT & Hbsb) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB m (x_D X) bsb)) in BDAT.
assert (LBSB : Z.of_nat (length bsb) = x_dsz X) by (pose proof BOK as (ZL & _); change (Z.of_nat (length (sb_data b)) = sb_buf_size b) in ZL; rewrite Hbsb, length_map in ZL; rewrite DSZ, <- BSZ; exact ZL).
unfold BITS_SIZEOF in SAA, OAA, ADA, ASTE, AFA, ASFA, ASH, ALO, FHA2.
destruct INV as (CL0 & ENC1 & HP1 & FST01 & VOCR & IDXR & SIDR & DTX01 & WB01 & ENH01 & SRR & ISVK).
unfold nb_hdr_cells in HDR. chunk_uncons HDR as HD0. chunk_uncons HDR as HD8. chunk_uncons HDR as HD12. chunk_uncons HDR as HD16. chunk_uncons HDR as HD20.
rewrite CL0 in HD12. rewrite JEXC in EXP.
assert (INL : In (ST, NBSTATE_SIZEOF) (rt_live RT Σ)) by (rewrite LV; exact NLS).
assert (INF : In (FF, NBD_FCLASS) (rt_frames RT Σ)) by (rewrite FRS, NFR; left; reflexivity).
assert (INFH : In (fh, kh) (rt_frames RT Σ)) by (rewrite FRS, NFR; right; exact NFH).
assert (INPD : In (PD, ND) (rt_live RT Σ)) by (rewrite LV; exact NLD).
assert (ESF8 : FF / 8 + SHB = SF) by (rewrite ESF, Z.shiftr_div_pow2 by lia; reflexivity).
assert (ESF8' : (FF + 2048) / 8 + SHB = SF + 256) by (rewrite <- ESF8; clear - F64; Z.div_mod_to_equations; lia).
assert (SHD1 : shad FF = SF) by (unfold shad; exact ESF8).
assert (SHD2 : shad (FF + 2048) = SF + 256) by (unfold shad; exact ESF8').
assert (LOWS : rt_sp0 RT Σ - STACK_WIN <= lo) by (rewrite SP0; exact NLOW).
pose proof (fun a0 => aclient_split RT AF Σ m (usp + -576) a0 ART0) as SPL.
unfold NBD_FRAME in PF. replace (usp - 576) with (usp + -576) in PF by lia. rewrite <- LV, <- FRS in PF. unfold nbW_EH in PF.
destruct (af_acc_live RT AF Σ m ST NBSTATE_SIZEOF ART0 INL) as (_ & ACS).
unfold NBSTATE_SIZEOF, NBD_FRAME, NBD_CALLEE_STACK, RT_STACK in *.
assert (OBS : aobj bsegs m ST 2968) by (split; [lia|]; split; [unfold APP_TOP, IMG_TOP_B, USTACK_TOP in *; lia| exact ACS]).
pose proof (nbG_tabs_acc_art Σ m ART0) as NTA.
replace (ST + 8 + 4) with (ST + 12) in HD12 by lia. replace (ST + 8 + 4 + 4) with (ST + 16) in HD16 by lia.
replace (ST + 8 + 4 + 4 + 4) with (ST + 20) in HD20 by lia. replace (ST + 8 + 4 + 4 + 4 + 4) with (ST + 24) in HDR by lia.
cps_norm. cps_hide.
cps_seg (@nbf_1 bptr usp lo ST OUT A FF SF olp bp mo r st (j_pad1 j) rest (x_gp X) (x_tp X) xra t0 t2 a0 a1 a2 a3 a4 a5 s2 s3 s4 s7 s9 t3 t4 t5 t6 s Fx fc m).

{ unfold IMG_TOP_B in OTOP. lia. }
{ clear - OLO NOUT LOU SPH. lia. }

destruct POST as (m1 & F1 & fc1 & xt0 & xt1 & xt2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & FRM1 & MU1 & WM1 & MI1 & ST1 & SH1 & ARMS).
clear SH FRM.
cps_seg_post.

pose proof (nbsh_acc_F m1 FF SF rest SH1 ESF F64 ltac:(lia)) as (ACQ1 & ACK1 & ACI1).
destruct (nbe_f32_win m1 (ST + 32) (j_excbuf j) 294 160 EXB ltac:(lia)) as (EXB1 & EXB2 & EXB3). clear EXB.
remember (firstn 294 (j_excbuf j)) as eb1 eqn:EEB1. remember (firstn 160 (skipn 294 (j_excbuf j))) as eb2 eqn:EEB2.
remember (skipn (294 + 160) (j_excbuf j)) as eb3 eqn:EEB3.
assert (LEB1 : length eb1 = 294%nat) by (subst eb1; rewrite length_firstn; lia).
assert (LEB2 : length eb2 = 160%nat) by (subst eb2; rewrite length_firstn, length_skipn; lia).
assert (LEB3 : length eb3 = 46%nat) by (subst eb3; rewrite length_skipn; lia).
clear EEB1 EEB2 EEB3. change (ST + 32 + 4 * Z.of_nat 294) with (ST + 32 + 1176) in EXB2. replace (ST + 32 + 1176) with (ST + 1208) in EXB2 by lia.
change (ST + 32 + 4 * Z.of_nat 294 + 4 * Z.of_nat 160) with (ST + 32 + 1176 + 640) in EXB3. replace (ST + 32 + 1176 + 640) with (ST + 1848) in EXB3 by lia.
destruct ARMS as [-> | ->].

-
chunk_split_f32 OW at 160%nat as OWa.
remember (firstn 160 ows) as ow1 eqn:EOW1. remember (skipn 160 ows) as ow2 eqn:EOW2.
assert (LOW1 : length ow1 = 160%nat) by (subst ow1; rewrite length_firstn; lia).
assert (LOW2 : Z.of_nat (length ow2) = Z.of_nat nout - 160) by (subst ow2; rewrite length_skipn; lia).
clear EOW1 EOW2. rewrite LOW1 in OW. change (OUT + Z.of_nat (4 * 160)) with (OUT + 640) in OW.
set (bsx := cells_bytes (f32 eb2)) in *.
assert (Lbsx : length bsx = 640%nat) by (unfold bsx; rewrite cells_bytes_length by apply cells_wf_f32; rewrite cells_size_f32, LEB2; reflexivity).
pose proof (proj2 (proj1 EXB2)) as SRCX. fold bsx in SRCX.
pose proof (proj2 OWa) as WRO. rewrite cells_size_f32, LOW1 in WRO.
assert (ACO1 : acc bsegs m1 OUT 640)
by (destruct (nbEH_acc_out Σ m1 m1 ART FRS PF) as (AC1 & _ & _); exact (acc_sub bsegs m1 OUT (4 * Z.of_nat nout) OUT 640 AC1 ltac:(lia) ltac:(lia))).
cps_rt (MCP Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 OUT (ST + 1208) bsx lo).
{ rewrite Lbsx. reflexivity. }
{ unfold USTACK_TOP, IMG_TOP_B in *; lia. }
{ unfold USTACK_TOP, IMG_TOP_B in *; lia. }
{ rewrite Lbsx. change (Z.of_nat 640) with 640. split; [intros _; split| left; lia].
- destruct (af_acc_live RT AF Σ m1 ST 2968 ART INL) as (_ & ACS1). exact (acc_sub bsegs m1 ST 2968 (ST + 1208) 640 ACS1 ltac:(lia) ltac:(lia)).
- left. exists ST, 2968. split; [exact INL| lia]. }
{ rewrite Lbsx. change (Z.of_nat 640) with 640. split; [intros _; split| split; [| exact WRO]].
- exact ACO1.
- right; left. exists fh, kh. split; [exact INFH| lia].
- intros i Hi. rewrite unsigned_lit by ulc. right; right; right; left. exists fh, kh. split; [exact INFH| lia]. }
{ cps_callok. }
intros c2 Hc2. clear OWa.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2).
rewrite Lbsx in PRES2. change (Z.of_nat 640) with 640 in PRES2.
nbg_trp PRES2.

assert (OWa : rw_cells bsegs m2 OUT (f32 eb2)).
{ split; [split; [apply cells_wf_f32 | exact BY2]|]. rewrite cells_size_f32, LEB2. exact (wr_at_transport bsegs m1 m2 _ _ WRO WM2). }
clear BY2 WRO SRCX PRES2 Lbsx. clear bsx. try clear MI1 ST1.
lazymatch goal with H : X14x.ASTA _ _ _ _ c2 |- _ => rewrite (ret_pc_even RA_nbf_cpy ltac:(unfold RA_nbf_cpy; lia) eq_refl) in H end.
cps_seg (nbf_3 usp lo ST OUT A FF SF olp bp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s _ _ m2).

{ destruct (af_acc_live RT AF Σ m2 ST 2968 ART2 INL) as (_ & ACS2). split; [lia|]. split; [unfold NBSTATE_SIZEOF, APP_TOP, USTACK_TOP in *; lia| exact ACS2]. }
{ exact (af_client_consts RT AF Σ m2 ART2). }
destruct POST as (m3 & F3 & fc3 & zt0 & zt1 & zt2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zs3 & zs7 & zt3 & zt5 & zt6 & FRM3 & MU3 & WM3 & MI3 & ST3 & SL3 & ->).
clear SL. try clear FRM1.
cps_seg_post.

assert (OW3 : rw_cells bsegs m3 OUT (f32 (eb2 ++ ow2))).
{ rewrite f32_app. apply rw_cells_join; [exact OWa|]. rewrite cells_size_f32, LEB2. change (OUT + Z.of_nat (4 * 160)) with (OUT + 640).
change (OUT + Z.of_nat (160 + (160 + (160 + (160 + 0))))) with (OUT + Z.of_nat 640) in OW. exact OW. }
assert (LOW3 : length (eb2 ++ ow2) = nout) by (rewrite length_app; lia).
clear OWa OW.
pose proof SLE as (E0 & E24 & E32 & E40 & E48 & E56 & E64 & E72 & E80 & E88 & E96 & E104 & E120 & E128 & E136 & E144 & E152 & E160 & E168 & E176 & E184
& E192 & E200 & E208 & E216 & E232 & E240 & E256 & E264 & E272 & E280 & E288 & E296 & E304 & E312 & E320 & E328 & E336 & E344 & E368).
set (sG := slots_G ST FF s) in *.
assert (G280 : v280 sG = Z_to_bv 64 (ST + 2040)) by exact E280.
assert (G272 : v272 sG = Z_to_bv 64 (FF + 160)) by exact E272.
assert (G240 : v240 sG = Z_to_bv 64 OUT) by exact E240.
assert (G304 : v304 sG = Z_to_bv 64 0) by exact E304.
assert (G344 : v344 sG = Z_to_bv 64 (FF + 244)) by reflexivity.
assert (G336 : v336 sG = Z_to_bv 64 (18446744073709551615 - (ST + 2168))) by reflexivity.
assert (G328 : v328 sG = Z_to_bv 64 (ST + 2120)) by reflexivity.
assert (G152 : v152 sG = Z_to_bv 64 (FF + 240)) by exact E152.
assert (ACO3 : acc bsegs m3 OUT (4 * Z.of_nat nout)) by (destruct (nbEH_acc_out Σ m3 m3 ltac:(assumption) FRS PF) as (AC3 & _ & _); exact AC3).
apply (cps_realizes bsegs _ _ T c1 (nbG_loop 4 m3 (rt_credit RT Σ) sG rest (j_old_qlsp j) (f_qlsp ff) 0 eq_refl ltac:(lia) LOQ LFQS
G280 G272 G240 G304 G344 G336 G328 G152 ACO3)).
{ exists Σ, F3, fc3, m3. do 17 eexists. exists (j_interp_qlpc j), (j_mem_sp j), (j_pi_gain j), (f_ak ff), (f_iq ff), (eb2 ++ ow2).
split; [replace (0 <? 4) with true by reflexivity; eassumption|].
split; [exact FRM3|]. split; [exact LV|]. split; [exact FRS|]. split; [exact SP0|]. split; [reflexivity|]. split; [exact POI|].
split; [eassumption|]. split; [exact MI3|]. split; [exact ST3|]. split; [apply wmono_refl|]. split; [apply pres_fp_refl|].
split; [exact SL3|]. split; [exact OQ|]. split; [exact IQ|]. split; [exact LIQ|]. split; [exact MSP|]. split; [exact LMSP|].
split; [exact PG|]. split; [exact LPG|]. split; [exact FQS|]. split; [exact FAK|]. split; [exact LFAK|]. split; [exact FIQ|]. split; [exact LFIQ|].
split; [exact OW3|]. split; [exact LOW3|]. split; [exact SH1| intros E; discriminate E]. }
intros c4 Hg.
destruct Hg as (Σ4 & F4 & fc4 & m4 & xra4 & xt04 & xt14 & xt24 & xa04 & xa14 & xa24 & xa34 & xa44 & xa54 & xa64 & xa74 & xs34 & xs74 & xt34 & xt54 & xt64
& iq4 & msp4 & pg4 & aks4 & iqs4 & ows4
& Hc4 & FRM4 & LV4 & FRS4 & SP04 & CR4 & POI4 & ART4 & MI4 & ST4 & WM4 & PFG & SL4 & OQ4 & IQ4 & LIQ4 & MSP4 & LMSP4 & PG4 & LPG4
& QS4 & AK4 & LAK4 & IQS4 & LIQS4 & OW4 & LOW4 & SH4 & S374).
replace (4 <? 4) with false in Hc4 by reflexivity. cbv iota in Hc4.
clear OQ IQ MSP PG FQS FAK FIQ OW3 SH1 SL3.
rewrite <- LV, <- FRS in PFG. unfold nbW_G in PFG.
nbg_trfp PFG.
assert (PF4 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (usp + -576)
[(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + BITS_SIZEOF); (FF, FF + 2048); (SF, SF + 256); (usp - 576, usp)] mE m4).
{ apply (pres_fp_trans _ _ _ _ mE m3 m4 PF).
apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ) (rt_frames RT Σ) (usp + -576) _ m3 m4 PFG); [intros e He; exact He| intros e He; exact He| lia|].
intros x Hx Ho. cbn [outside] in Ho |- *. destruct Ho as (H1 & H2 & H3 & H4 & H5 & H6 & _). clear - H1 H2 H4. repeat split; Lia.lia. }
clear PF. rename PF4 into PF. try clear ART. clear MI3 ST3.

destruct (S374 eq_refl) as (-> & ->).
assert (LV4' : rt_live RT Σ4 = rt_live RT Σ) by (rewrite LV4, LV; reflexivity).
assert (FRS4' : rt_frames RT Σ4 = rt_frames RT Σ) by (rewrite FRS4, FRS; reflexivity).
assert (SP04' : rt_sp0 RT Σ4 = rt_sp0 RT Σ) by (rewrite SP04, SP0; reflexivity).
cps_sigma LV4' FRS4' SP04'.
chunk_split_f32 OW4 at 160%nat as OWh.
remember (firstn 160 ows4) as oh1 eqn:EOH1. remember (skipn 160 ows4) as oh2 eqn:EOH2.
assert (LOH1 : length oh1 = 160%nat) by (subst oh1; rewrite length_firstn; lia).
assert (LOH2 : Z.of_nat (length oh2) = Z.of_nat nout - 160) by (subst oh2; rewrite length_skipn; lia).
clear EOH1 EOH2. rewrite LOH1 in OW4. change (OUT + Z.of_nat (4 * 160)) with (OUT + 640) in OW4.
assert (ACO4 : acc bsegs m4 OUT (4 * Z.of_nat nout)) by (destruct (nbEH_acc_out Σ4 m4 m4 ART4 ltac:(rewrite FRS4'; exact FRS) ltac:(rewrite LV4', FRS4'; exact PF)) as (AC4 & _ & _); exact AC4).
destruct (af_acc_live RT AF Σ4 m4 ST 2968 ART4 INL) as (_ & ACS4).
assert (OBS4 : aobj bsegs m4 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS4]).
pose proof (af_client_consts RT AF Σ4 m4 ART4) as CC4.
cps_seg (@nbh_1a bptr usp lo ST OUT FF st (j_pad2 j) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sG _ _ m4).

destruct POST as (hyt0 & hyt1 & hyt2 & hya5 & hya6 & hya7 & hyt3 & hyt4 & hyt5 & hyt6 & ->).

assert (ACO4h : acc bsegs m4 OUT 640) by exact (acc_sub bsegs m4 OUT (4 * Z.of_nat nout) OUT 640 ACO4 ltac:(lia) ltac:(lia)).
cps_rt (HP Σ4 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 m4 OUT (ST + 2160) (hp_filt (nb_isWideband st)) lo fh ST 2968 kh oh1 (j_mem_hp j)).
{ unfold hp_filt. destruct (nb_isWideband st =? 0); [left| right]; reflexivity. }
{ rewrite FRS4; exact FRMX. }
{ rewrite CR4; rewrite ?CR; unfold NBD_EH_CREDIT in CRD; lia. }
{ rewrite unsigned_lit by ulc; exact ST4. }
{ rewrite unsigned_lit by ulc; unfold RT_STACK, HIGHPASS_STACK; lia. }
{ rewrite unsigned_lit by ulc; unfold USTACK_TOP in *; lia. }
{ rewrite unsigned_lit by ulc; clear - U32; Z.div_mod_to_equations; lia. }

intros cH5 (Σ5 & Hc5 & LV5 & FRS5 & SP5 & CR5 & POI5).
cps_unpack_lib Hc5 as (v5 & m5 & ys5 & hs5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & YS5 & LYS5 & ACY5 & HS5 & LHS5).
clear OWh MHP ACO4h.
nbg_trfp PRES5.
assert (PF5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (usp + -576)
[(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + BITS_SIZEOF); (FF, FF + 2048); (SF, SF + 256); (usp - 576, usp)] mE m5).
{ apply (pres_fp_trans _ _ _ _ mE m4 m5 PF).
apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ4) (rt_frames RT Σ4) (usp + -576) _ m4 m5 PRES5); [intros e He; rewrite LV4'; exact He| intros e He; rewrite FRS4'; exact He| lia|].
intros x Hx Ho. cbn [outside] in Ho |- *. destruct Ho as (H1 & H2 & _). split; [clear - H2 NOUT; Lia.lia| split; [clear - H1; Lia.lia| exact I]]. }
clear PF PRES5. rename PF5 into PF.
cps_sigma LV5 FRS5 SP5.
lazymatch goal with H : X14x.ASTA _ _ _ _ cH5 |- _ => rewrite (ret_pc_even NBH_PC_LV ltac:(unfold NBH_PC_LV; lia) eq_refl) in H end.

destruct (af_acc_live RT AF Σ5 m5 ST 2968 ART5 INL) as (_ & ACS5).
assert (OBS5 : aobj bsegs m5 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS5]).
cps_seg (nbh_1b usp lo ST OUT FF (j_levels j) (j_old_qlsp j) (f_qlsp ff) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sG _ _ m5).

{ pose proof (af_live_small RT AF Σ5 m5 ST 2968 ART5 INL ltac:(lia)) as SM. unfold SEGTOP_A in SM. unfold IMG_TOP_B. lia. }
{ exact (af_client_consts RT AF Σ5 m5 ART5). }
destruct POST as (m6 & F6 & fc6 & xa06 & xa16 & xa26 & xa36 & xa46 & xa56 & lv6 & oq6 & FRM6 & MU6 & WM6 & MI6 & ST6 & LVL6 & LLV6 & OQ6 & LOQ6 & ->).
clear LVL OQ4. try clear FRM4.
cps_seg_post.

replace (ST + 8 + 4) with (ST + 12) in HD12 by lia.
chunk_snoc HD8 HD12.
destruct (j_pitch_gain_buf j) as [|pb0 [|pb1 [|pb2 [|]]]] eqn:EPGB; cbn [length] in LPGB; try discriminate LPGB.
lazymatch goal with A6 : X14x.ART RT Σ5 m6 |- _ =>
destruct (af_acc_live RT AF Σ5 m6 ST 2968 A6 INL) as (_ & ACS6);
pose proof (af_client_consts RT AF Σ5 m6 A6) as CC6 end.
assert (OBS6 : aobj bsegs m6 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS6]).
assert (G112 : v112 sG = Z_to_bv 64 (Z.shiftr (ST + 2208) 3 + SHB)) by exact E112.
cps_seg (nbh_2 usp lo ST OUT FF SF bp (nb_pitch_gain_buf_idx st) (nb_first st) 0 rest (j_last_ol_gain j) (j_last_pitch j) (j_last_pitch_gain j) [pb0; pb1; pb2]
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sG _ _ m6).

{ pose proof (af_live_small RT AF Σ5 m6 ST 2968 ltac:(assumption) INL ltac:(lia)) as SM. unfold SEGTOP_A in SM. unfold IMG_TOP_B. lia. }
destruct POST as (m7 & F7 & fc7 & za07 & za17 & za37 & za47 & za57 & za67 & za77 & lol7 & lpg7 & pgb7
& FRM7 & MU7 & WM7 & MI7 & ST7 & HD8' & HD20' & LPP' & PGB' & LPGB' & IDX' & SH7 & ->).
clear HD8 HD20 LPP PGB IDX SH4 FRM6.
cps_seg_post.

lazymatch goal with A7 : X14x.ART RT Σ5 m7 |- _ => pose proof (AF_LIB Σ5 m7 A7) as LC7; pose proof (af_client_consts RT AF Σ5 m7 A7) as CC7 end.
apply Hk. exists Σ5. split; [| split; [rewrite LV5; exact LV4|]; split; [rewrite FRS5; exact FRS4|]; split; [rewrite SP5; exact SP04|];
split; [rewrite CR5, CR4; rewrite ?CR; unfold NBD_EH_CREDIT; lia| rewrite POI5; exact POI4]].
unfold ASTA. eapply AST_conseq; [eassumption | | intros mo0 Hmo; exact Hmo].
intros ms <-. split.
+ unfold at_X_A. exists F7, fc7, m7. do 24 eexists.
exists (NBJ lol7 (eb1 ++ eb2 ++ eb3) (ST + 1368) oq6 iq4 msp4 hs5 pg4 lv6 (Z_to_bv 64 bp) lpg7 pgb7 (j_seed j) (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)).
exists (ys5 ++ oh2), sws, sG, (NBF (f_pitch ff) (f_pg ff) (f_lpc ff) (f_qlsp ff) aks4 (f_innov ff) (f_exc32 ff) (f_innov2 ff) iqs4).
split; [reflexivity|]. split; [exact FRM7|].

split.
{ unfold nbctx. split; [exact MI7|]. split; [exact ST7|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain
j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split.
{ unfold nb_hdr_cells. cbn [nb_end set_nb_pitch_gain_buf_idx set_nb_count_lost set_nb_first nb_first nb_count_lost nb_sampling_rate].
change [C8 (Z_to_bv 64 A_speex_nb_mode); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (nb_sampling_rate st)); C4 lol7; C8 (Z_to_bv 64 0)]
with ([C8 (Z_to_bv 64 A_speex_nb_mode)] ++ ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ ([C4 (Z_to_bv 64 (nb_sampling_rate st))] ++ ([C4 lol7] ++ [C8 (Z_to_bv 64 0)])))).
apply rw_cells_join; [exact HD0|]. cbn [cells_size csize Nat.add]. replace (ST + Z.of_nat 8) with (ST + 8) by lia.
apply rw_cells_join; [exact HD8'|]. cbn [cells_size csize Nat.add]. replace (ST + 8 + Z.of_nat 8) with (ST + 16) by lia.
apply rw_cells_join; [exact HD16|]. cbn [cells_size csize Nat.add]. replace (ST + 16 + Z.of_nat 4) with (ST + 20) by lia.
apply rw_cells_join; [exact HD20'|]. cbn [cells_size csize Nat.add]. replace (ST + 20 + Z.of_nat 4) with (ST + 24) by lia. exact HDR. }
split; [apply nbe_f32_join_win; [exact EXB1| rewrite LEB1; replace (ST + 32 + 4 * Z.of_nat 294) with (ST + 1208) by lia; exact EXB2| rewrite LEB1, LEB2; replace (ST + 32 + 4 * Z.of_nat 294 + 4 * Z.of_nat 160) with (ST + 1848) by lia; exact EXB3]|].
split; [exact EXP|]. split; [exact OQ6|]. split; [exact IQ4|]. split; [exact MSP4|]. split; [exact HS5|]. split; [exact PG4|].
split; [exact ISP|]. split; [exact LVL6|]. split; [exact LPP'|]. split; [exact PGB'|]. split; [exact IDX'|]. split; [exact SEED|].
split; [unfold nb_cfg_cells; exact CFG|]. split; [exact CBS|]. split; [unfold nb_ucb_cells, cb_cells; exact UCB|]. split; [exact VOC|].
unfold nb_tail_cells; exact TL. }
split.
{ unfold nb_junk_ok; cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain
j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
rewrite !length_app, LEB1, LEB2, LEB3. repeat split; first [reflexivity | assumption | apply LUCB]. }
split; [exact CBOK|].
split.
{ unfold nb_inv. cbn [nb_end set_nb_pitch_gain_buf_idx set_nb_count_lost set_nb_first nb_first nb_count_lost nb_encode_submode nb_highpass_enabled
nb_voc_offset nb_pitch_gain_buf_idx nb_submodeID nb_dtx_enabled nb_isWideband nb_lpc_enh_enabled nb_sampling_rate nb_innov_save].
repeat split; try assumption; try lia.
- destruct (Z.ltb_spec 2 (nb_pitch_gain_buf_idx st + 1)); lia.
- destruct (Z.ltb_spec 2 (nb_pitch_gain_buf_idx st + 1)); lia. }
split.
{ split; [exists rjb; split; [exact Lrjb| unfold bits_cells; exact BOBJ]|].
split; [exists bsb; split; [apply (proj2 (u8arr_rw_CB m7 (x_D X) bsb)); exact BDAT| exact Hbsb]| exact BSIDE]. }
split; [exact BOK|]. split; [exact BSZ|].
split.
{ rewrite f32_app. apply rw_cells_join; [exact YS5|]. rewrite cells_size_f32, LYS5.
replace (OUT + Z.of_nat (160 + (160 + (160 + (160 + 0))))) with (OUT + Z.of_nat (4 * 160)) in OW4 by lia. exact OW4. }
split; [rewrite length_app; lia|].
split; [exact SW|]. split; [exact LSW|].
split; [split; [exact SL4| exact SV]|].
split.
{ unfold fframe_at; cbn [f_pitch f_pg f_lpc f_qlsp f_ak f_innov f_exc32 f_innov2 f_iq].
split; [exact FF0|]. split; [exact FPI|]. split; [exact FPG|]. split; [exact FLPC|]. split; [exact QS4|]. split; [exact AK4|].
split; [exact FIN|]. split; [exact FE32|]. split; [exact FIN2| exact IQS4]. }
split.
{ unfold ff_ok; cbn [f_pitch f_pg f_lpc f_qlsp f_ak f_innov f_exc32 f_innov2 f_iq].
split; [exact LFPG|]. split; [exact LFLPC|]. split; [exact LFQS|]. split; [exact LAK4|]. split; [exact LFIN|]. split; [exact LFE32|].
split; [exact LFIN2| exact LIQS4]. }
split; [exists rest; exact SH7|].
split; [exact CC7|]. split; [exact LC7|]. split; [reflexivity|].
cbn [nb_end set_nb_pitch_gain_buf_idx set_nb_count_lost set_nb_first nb_innov_save]. exact JISV. }
split; [exact E48| exact E56].
+
lazymatch goal with |- context [ms_mem (MS _ _ _ _ _ ?mm _)] => change (ms_mem (MS _ _ _ _ _ mm _)) with mm end.
assert (PF7 : rt_pres_fp (rt_live RT Σ5) (rt_frames RT Σ5) (usp + -576)
[(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + BITS_SIZEOF); (FF, FF + 2048); (SF, SF + 256); (usp - 576, usp)] mE m7)
by (rewrite LV5, FRS5, LV4, FRS4, <- LV, <- FRS; exact PF).
split; [assumption|]. split; [exact (nbEH_acc_out Σ5 m7 m7 ltac:(assumption) ltac:(rewrite FRS5; exact FRS4) PF7)|].
split; [cps_wmono|].
rewrite <- LV, <- FRS. unfold nbW_EH, NBD_FRAME, NBSTATE_SIZEOF. replace (usp - 576) with (usp + -576) by lia. exact PF.

-

chunk_split_f32 OW at 160%nat as OWa.
remember (firstn 160 ows) as ow1 eqn:EOW1. remember (skipn 160 ows) as ow2 eqn:EOW2.
assert (LOW1 : length ow1 = 160%nat) by (subst ow1; rewrite length_firstn; lia).
assert (LOW2 : Z.of_nat (length ow2) = Z.of_nat nout - 160) by (subst ow2; rewrite length_skipn; lia).
clear EOW1 EOW2. rewrite LOW1 in OW. change (OUT + Z.of_nat (4 * 160)) with (OUT + 640) in OW.
chunk_split_f32 OWa at 80%nat as OWb.
remember (firstn 80 ow1) as o1a eqn:EO1A. remember (skipn 80 ow1) as o1b eqn:EO1B.
assert (LO1A : length o1a = 80%nat) by (subst o1a; rewrite length_firstn; lia).
assert (LO1B : length o1b = 80%nat) by (subst o1b; rewrite length_skipn; lia).
clear EO1A EO1B. rewrite LO1A in OWa. change (OUT + Z.of_nat (4 * 80)) with (OUT + 320) in OWa.
assert (EXB : rw_cells bsegs m1 (ST + 32) (f32 (eb1 ++ eb2 ++ eb3))).
{ apply nbe_f32_join_win; [exact EXB1| rewrite LEB1; replace (ST + 32 + 4 * Z.of_nat 294) with (ST + 1208) by lia; exact EXB2
| rewrite LEB1, LEB2; replace (ST + 32 + 4 * Z.of_nat 294 + 4 * Z.of_nat 160) with (ST + 1848) by lia; exact EXB3]. }
assert (LEB : length (eb1 ++ eb2 ++ eb3) = 500%nat) by (rewrite !length_app, LEB1, LEB2, LEB3; reflexivity).
clear EXB1 EXB2 EXB3.
assert (POA : pois_above (rt_pois RT Σ) (usp + -576)) by (rewrite POI; apply (pois_above_le _ (usp - 576)); [exact NPOIS| lia]).
assert (ACO1 : acc bsegs m1 OUT 320)
by (destruct (nbEH_acc_out Σ m1 m1 ltac:(assumption) FRS PF) as (AC1 & _ & _); exact (acc_sub bsegs m1 OUT (4 * Z.of_nat nout) OUT 320 AC1 ltac:(lia) ltac:(lia))).
cps_rt (MC Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m1 (ST + 32) 294 OUT bp lo fh ST 2968 kh (eb1 ++ eb2 ++ eb3) o1a).

{ f_equal; lia. }
{ rewrite FRS; exact FRMX. }
{ rewrite CR; unfold NBD_EH_CREDIT in CRD; lia. }
{ rewrite unsigned_lit by ulc; exact POA. }
{ rewrite unsigned_lit by ulc; exact ST1. }
{ rewrite unsigned_lit by ulc; unfold RT_STACK, MULTICOMB_STACK; lia. }
{ rewrite unsigned_lit by ulc; unfold USTACK_TOP in *; lia. }
{ rewrite unsigned_lit by ulc; clear - U32; Z.div_mod_to_equations; lia. }
intros c2 (Σ2 & Hc2 & LV2 & FRS2 & SP2 & CR2 & POI2).
cps_unpack_lib Hc2 as (v2 & m2a & ns1 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & NS1 & LNS1 & ACN1).
try clear Hc0. clear OWb.
nbg_trfp PRES2.
try clear ART. clear MI1. try clear ST1. try clear ST0.
assert (PF2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (usp + -576)
[(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + BITS_SIZEOF); (FF, FF + 2048); (SF, SF + 256); (usp - 576, usp)] mE m2a).
{ apply (pres_fp_trans _ _ _ _ mE m1 m2a PF).
apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ) (rt_frames RT Σ) (usp + -576) _ m1 m2a PRES2); [intros e He; exact He| intros e He; exact He| lia|].
intros x Hx Ho. cbn [outside] in Ho |- *. destruct Ho as (H1 & H2 & _). split; [| exact I]. clear - H2 NOUT. Lia.lia. }
clear PF PRES2. rename PF2 into PF.

cps_seg (@nbf_2 bptr usp lo ST OUT A FF SF olp bp mo r st (j_pad1 j) (x_gp X) (x_tp X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s _ _ m2a).

{ assert (INL2 : In (ST, 2968) (rt_live RT Σ2)) by (rewrite LV2; exact INL).
destruct (af_acc_live RT AF Σ2 m2a ST 2968 ART2 INL2) as (_ & ACS2). split; [lia|]. split; [unfold NBSTATE_SIZEOF, APP_TOP, USTACK_TOP in *; lia| exact ACS2]. }
{ unfold IMG_TOP_B in OTOP. lia. }
{ clear - OLO NOUT LOU SPH. lia. }
{ exact (AF_LIB Σ2 m2a ART2). }
{ exact (nbG_tabs_acc_art Σ2 m2a ART2). }
{ exact (af_client_consts RT AF Σ2 m2a ART2). }
destruct POST as (F2 & fc2 & yt0 & yt1 & yt2 & yt3 & yt4 & yt5 & yt6 & FRM2 & ->).
change (OUT + Z.of_nat (80 + (80 + (80 + (80 + 0))))) with (OUT + 320) in OWa.
change (OUT + Z.of_nat (160 + (160 + (160 + (160 + 0))))) with (OUT + 640) in OW.
assert (INL2 : In (ST, 2968) (rt_live RT Σ2)) by (rewrite LV2; exact INL).
assert (INFH2 : In (fh, kh) (rt_frames RT Σ2)) by (rewrite FRS2; exact INFH).
assert (FRS2' : rt_frames RT Σ2 = rt_frames RT Σ0) by (rewrite FRS2; exact FRS).
assert (ACO2 : acc bsegs m2a (OUT + 320) 320).
{ assert (PFx : rt_pres_fp (rt_live RT Σ2) (rt_frames RT Σ2) (usp + -576)
[(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + BITS_SIZEOF); (FF, FF + 2048); (SF, SF + 256); (usp - 576, usp)] mE m2a)
by (rewrite LV2, FRS2; exact PF).
destruct (nbEH_acc_out Σ2 m2a m2a ART2 FRS2' PFx) as (AC2 & _ & _). exact (acc_sub bsegs m2a OUT (4 * Z.of_nat nout) (OUT + 320) 320 AC2 ltac:(lia) ltac:(lia)). }
assert (POA2 : pois_above (rt_pois RT Σ2) (usp + -576)) by (rewrite POI2; exact POA).
cps_rt (MC Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m2a (ST + 32) 374 (OUT + 320) bp lo fh ST 2968 kh (eb1 ++ eb2 ++ eb3) o1b).
{ f_equal; lia. }
{ rewrite FRS2'; exact FRMX. }
{ rewrite CR2, CR; unfold NBD_EH_CREDIT in CRD; lia. }
{ rewrite unsigned_lit by ulc; exact POA2. }
{ rewrite unsigned_lit by ulc; exact ST2. }
{ rewrite unsigned_lit by ulc; unfold RT_STACK, MULTICOMB_STACK; lia. }
{ rewrite unsigned_lit by ulc; unfold USTACK_TOP in *; lia. }
{ rewrite unsigned_lit by ulc; clear - U32; Z.div_mod_to_equations; lia. }
intros c3 (Σ3 & Hc3 & LV3 & FRS3 & SP3 & CR3 & POI3).
cps_unpack_lib Hc3 as (v3 & m2 & ns2 & RS3 & (ART3 & MI3a & WM3a & ST3a) & PRES3 & NS2 & LNS2 & ACN2).
clear OWa.
rewrite LV2, FRS2 in PRES3.
nbg_trfp PRES3.
clear ART2 MI2 ST2.
assert (PF3 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (usp + -576)
[(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + BITS_SIZEOF); (FF, FF + 2048); (SF, SF + 256); (usp - 576, usp)] mE m2).
{ apply (pres_fp_trans _ _ _ _ mE m2a m2 PF).
apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ) (rt_frames RT Σ) (usp + -576) _ m2a m2 PRES3); [intros e He; exact He| intros e He; exact He| lia|].
intros x Hx Ho. cbn [outside] in Ho |- *. destruct Ho as (H1 & H2 & _). split; [| exact I]. clear - H2 NOUT. Lia.lia. }
clear PF PRES3. rename PF3 into PF.

cps_seg (nbf_3m usp ST OUT FF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2).
subst ms.
assert (LOWS3 : rt_sp0 RT Σ3 - 8388608 <= lo) by (rewrite SP3, SP2; exact LOWS).
cps_seg (nbf_3 usp lo ST OUT A FF SF olp bp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s _ _ m2).

{ assert (INL3 : In (ST, 2968) (rt_live RT Σ3)) by (rewrite LV3, LV2; exact INL).
destruct (af_acc_live RT AF Σ3 m2 ST 2968 ART3 INL3) as (_ & ACS3). split; [lia|]. split; [unfold NBSTATE_SIZEOF, APP_TOP, USTACK_TOP in *; lia| exact ACS3]. }
{ exact (af_client_consts RT AF Σ3 m2 ART3). }
destruct POST as (m3 & F3 & fc3 & zt0 & zt1 & zt2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zs3 & zs7 & zt3 & zt5 & zt6 & FRM3 & MU3 & WM3 & MI3 & ST3 & SL3 & ->).
clear SL. try clear FRM1. try clear FRM2.
cps_seg_post.

assert (OW3 : rw_cells bsegs m3 OUT (f32 (ns1 ++ ns2 ++ ow2))).
{ apply nbe_f32_join_win; [exact NS1| rewrite LNS1; change (OUT + 4 * Z.of_nat 80) with (OUT + 320); exact NS2
| rewrite LNS1, LNS2; replace (OUT + 4 * Z.of_nat 80 + 4 * Z.of_nat 80) with (OUT + 640) by lia; exact OW]. }
assert (LOW3 : length (ns1 ++ ns2 ++ ow2) = nout) by (rewrite !length_app; lia).
clear NS1 NS2 OW.
pose proof SLE as (E0 & E24 & E32 & E40 & E48 & E56 & E64 & E72 & E80 & E88 & E96 & E104 & E120 & E128 & E136 & E144 & E152 & E160 & E168 & E176 & E184
& E192 & E200 & E208 & E216 & E232 & E240 & E256 & E264 & E272 & E280 & E288 & E296 & E304 & E312 & E320 & E328 & E336 & E344 & E368).
set (sG := slots_G ST FF s) in *.
assert (G280 : v280 sG = Z_to_bv 64 (ST + 2040)) by exact E280.
assert (G272 : v272 sG = Z_to_bv 64 (FF + 160)) by exact E272.
assert (G240 : v240 sG = Z_to_bv 64 OUT) by exact E240.
assert (G304 : v304 sG = Z_to_bv 64 0) by exact E304.
assert (G344 : v344 sG = Z_to_bv 64 (FF + 244)) by reflexivity.
assert (G336 : v336 sG = Z_to_bv 64 (18446744073709551615 - (ST + 2168))) by reflexivity.
assert (G328 : v328 sG = Z_to_bv 64 (ST + 2120)) by reflexivity.
assert (G152 : v152 sG = Z_to_bv 64 (FF + 240)) by exact E152.
assert (FRS3' : rt_frames RT Σ3 = rt_frames RT Σ0) by (rewrite FRS3, FRS2; exact FRS).
assert (ACO3 : acc bsegs m3 OUT (4 * Z.of_nat nout))
by (destruct (nbEH_acc_out Σ3 m3 m3 ltac:(assumption) FRS3' ltac:(rewrite LV3, LV2, FRS3, FRS2; exact PF)) as (AC3 & _ & _); exact AC3).
lazymatch goal with |- realizes _ ?cc _ =>
apply (cps_realizes bsegs _ _ T cc (nbG_loop 4 m3 (rt_credit RT Σ3) sG rest (j_old_qlsp j) (f_qlsp ff) 0 eq_refl ltac:(lia) LOQ LFQS
G280 G272 G240 G304 G344 G336 G328 G152 ACO3)) end.
{ exists Σ3, F3, fc3, m3. do 17 eexists. exists (j_interp_qlpc j), (j_mem_sp j), (j_pi_gain j), (f_ak ff), (f_iq ff), (ns1 ++ ns2 ++ ow2).
split; [replace (0 <? 4) with true by reflexivity; eassumption|].
split; [exact FRM3|]. split; [rewrite LV3, LV2; exact LV|]. split; [exact FRS3'|]. split; [rewrite SP3, SP2; exact SP0|]. split; [reflexivity|]. split; [rewrite POI3, POI2; exact POI|].
split; [assumption|]. split; [exact MI3|]. split; [exact ST3|]. split; [apply wmono_refl|]. split; [apply pres_fp_refl|].
split; [exact SL3|]. split; [exact OQ|]. split; [exact IQ|]. split; [exact LIQ|]. split; [exact MSP|]. split; [exact LMSP|].
split; [exact PG|]. split; [exact LPG|]. split; [exact FQS|]. split; [exact FAK|]. split; [exact LFAK|]. split; [exact FIQ|]. split; [exact LFIQ|].
split; [exact OW3|]. split; [exact LOW3|]. split; [exact SH1| intros E; discriminate E]. }
try clear c0; try clear c1; try clear c2; try clear c3; try clear c4; try clear c5.
intros c4 Hg.
destruct Hg as (Σ4 & F4 & fc4 & m4 & xra4 & xt04 & xt14 & xt24 & xa04 & xa14 & xa24 & xa34 & xa44 & xa54 & xa64 & xa74 & xs34 & xs74 & xt34 & xt54 & xt64
& iq4 & msp4 & pg4 & aks4 & iqs4 & ows4
& Hc4 & FRM4 & LV4 & FRS4 & SP04 & CR4 & POI4 & ART4 & MI4 & ST4 & WM4 & PFG & SL4 & OQ4 & IQ4 & LIQ4 & MSP4 & LMSP4 & PG4 & LPG4
& QS4 & AK4 & LAK4 & IQS4 & LIQS4 & OW4 & LOW4 & SH4 & S374).
replace (4 <? 4) with false in Hc4 by reflexivity. cbv iota in Hc4.
clear OQ IQ MSP PG FQS FAK FIQ OW3 SH1 SL3.
rewrite <- LV, <- FRS in PFG. unfold nbW_G in PFG.
nbg_trfp PFG.
rewrite CR3, CR2 in CR4.
assert (PF4 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (usp + -576)
[(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + BITS_SIZEOF); (FF, FF + 2048); (SF, SF + 256); (usp - 576, usp)] mE m4).
{ apply (pres_fp_trans _ _ _ _ mE m3 m4 PF).
apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ) (rt_frames RT Σ) (usp + -576) _ m3 m4 PFG); [intros e He; exact He| intros e He; exact He| lia|].
intros x Hx Ho. cbn [outside] in Ho |- *. destruct Ho as (H1 & H2 & H3 & H4 & H5 & H6 & _). clear - H1 H2 H4. repeat split; Lia.lia. }
clear PF. rename PF4 into PF. try clear ART. clear MI3 ST3.

destruct (S374 eq_refl) as (-> & ->).
assert (LV4' : rt_live RT Σ4 = rt_live RT Σ) by (rewrite LV4, LV; reflexivity).
assert (FRS4' : rt_frames RT Σ4 = rt_frames RT Σ) by (rewrite FRS4, FRS; reflexivity).
assert (SP04' : rt_sp0 RT Σ4 = rt_sp0 RT Σ) by (rewrite SP04, SP0; reflexivity).
cps_sigma LV4' FRS4' SP04'.
chunk_split_f32 OW4 at 160%nat as OWh.
remember (firstn 160 ows4) as oh1 eqn:EOH1. remember (skipn 160 ows4) as oh2 eqn:EOH2.
assert (LOH1 : length oh1 = 160%nat) by (subst oh1; rewrite length_firstn; lia).
assert (LOH2 : Z.of_nat (length oh2) = Z.of_nat nout - 160) by (subst oh2; rewrite length_skipn; lia).
clear EOH1 EOH2. rewrite LOH1 in OW4. change (OUT + Z.of_nat (4 * 160)) with (OUT + 640) in OW4.
assert (ACO4 : acc bsegs m4 OUT (4 * Z.of_nat nout)) by (destruct (nbEH_acc_out Σ4 m4 m4 ART4 ltac:(rewrite FRS4'; exact FRS) ltac:(rewrite LV4', FRS4'; exact PF)) as (AC4 & _ & _); exact AC4).
destruct (af_acc_live RT AF Σ4 m4 ST 2968 ART4 INL) as (_ & ACS4).
assert (OBS4 : aobj bsegs m4 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS4]).
pose proof (af_client_consts RT AF Σ4 m4 ART4) as CC4.
cps_seg (@nbh_1a bptr usp lo ST OUT FF st (j_pad2 j) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sG _ _ m4).

destruct POST as (hyt0 & hyt1 & hyt2 & hya5 & hya6 & hya7 & hyt3 & hyt4 & hyt5 & hyt6 & ->).

assert (ACO4h : acc bsegs m4 OUT 640) by exact (acc_sub bsegs m4 OUT (4 * Z.of_nat nout) OUT 640 ACO4 ltac:(lia) ltac:(lia)).
cps_rt (HP Σ4 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 m4 OUT (ST + 2160) (hp_filt (nb_isWideband st)) lo fh ST 2968 kh oh1 (j_mem_hp j)).
{ unfold hp_filt. destruct (nb_isWideband st =? 0); [left| right]; reflexivity. }
{ rewrite FRS4; exact FRMX. }
{ rewrite CR4; rewrite ?CR; unfold NBD_EH_CREDIT in CRD; lia. }
{ rewrite unsigned_lit by ulc; exact ST4. }
{ rewrite unsigned_lit by ulc; unfold RT_STACK, HIGHPASS_STACK; lia. }
{ rewrite unsigned_lit by ulc; unfold USTACK_TOP in *; lia. }
{ rewrite unsigned_lit by ulc; clear - U32; Z.div_mod_to_equations; lia. }

intros cH5 (Σ5 & Hc5 & LV5 & FRS5 & SP5 & CR5 & POI5).
cps_unpack_lib Hc5 as (v5 & m5 & ys5 & hs5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & YS5 & LYS5 & ACY5 & HS5 & LHS5).
clear OWh MHP ACO4h.
nbg_trfp PRES5.
assert (PF5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (usp + -576)
[(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + BITS_SIZEOF); (FF, FF + 2048); (SF, SF + 256); (usp - 576, usp)] mE m5).
{ apply (pres_fp_trans _ _ _ _ mE m4 m5 PF).
apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ4) (rt_frames RT Σ4) (usp + -576) _ m4 m5 PRES5); [intros e He; rewrite LV4'; exact He| intros e He; rewrite FRS4'; exact He| lia|].
intros x Hx Ho. cbn [outside] in Ho |- *. destruct Ho as (H1 & H2 & _). split; [clear - H2 NOUT; Lia.lia| split; [clear - H1; Lia.lia| exact I]]. }
clear PF PRES5. rename PF5 into PF.
cps_sigma LV5 FRS5 SP5.
lazymatch goal with H : X14x.ASTA _ _ _ _ cH5 |- _ => rewrite (ret_pc_even NBH_PC_LV ltac:(unfold NBH_PC_LV; lia) eq_refl) in H end.

destruct (af_acc_live RT AF Σ5 m5 ST 2968 ART5 INL) as (_ & ACS5).
assert (OBS5 : aobj bsegs m5 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS5]).
cps_seg (nbh_1b usp lo ST OUT FF (j_levels j) (j_old_qlsp j) (f_qlsp ff) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sG _ _ m5).

{ pose proof (af_live_small RT AF Σ5 m5 ST 2968 ART5 INL ltac:(lia)) as SM. unfold SEGTOP_A in SM. unfold IMG_TOP_B. lia. }
{ exact (af_client_consts RT AF Σ5 m5 ART5). }
destruct POST as (m6 & F6 & fc6 & xa06 & xa16 & xa26 & xa36 & xa46 & xa56 & lv6 & oq6 & FRM6 & MU6 & WM6 & MI6 & ST6 & LVL6 & LLV6 & OQ6 & LOQ6 & ->).
clear LVL OQ4. try clear FRM4.
cps_seg_post.

replace (ST + 8 + 4) with (ST + 12) in HD12 by lia.
chunk_snoc HD8 HD12.
destruct (j_pitch_gain_buf j) as [|pb0 [|pb1 [|pb2 [|]]]] eqn:EPGB; cbn [length] in LPGB; try discriminate LPGB.
lazymatch goal with A6 : X14x.ART RT Σ5 m6 |- _ =>
destruct (af_acc_live RT AF Σ5 m6 ST 2968 A6 INL) as (_ & ACS6);
pose proof (af_client_consts RT AF Σ5 m6 A6) as CC6 end.
assert (OBS6 : aobj bsegs m6 ST 2968) by (split; [lia|]; split; [unfold APP_TOP, USTACK_TOP in *; lia| exact ACS6]).
assert (G112 : v112 sG = Z_to_bv 64 (Z.shiftr (ST + 2208) 3 + SHB)) by exact E112.
cps_seg (nbh_2 usp lo ST OUT FF SF bp (nb_pitch_gain_buf_idx st) (nb_first st) 0 rest (j_last_ol_gain j) (j_last_pitch j) (j_last_pitch_gain j) [pb0; pb1; pb2]
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sG _ _ m6).

{ pose proof (af_live_small RT AF Σ5 m6 ST 2968 ltac:(assumption) INL ltac:(lia)) as SM. unfold SEGTOP_A in SM. unfold IMG_TOP_B. lia. }
destruct POST as (m7 & F7 & fc7 & za07 & za17 & za37 & za47 & za57 & za67 & za77 & lol7 & lpg7 & pgb7
& FRM7 & MU7 & WM7 & MI7 & ST7 & HD8' & HD20' & LPP' & PGB' & LPGB' & IDX' & SH7 & ->).
clear HD8 HD20 LPP PGB IDX SH4 FRM6.
cps_seg_post.

lazymatch goal with A7 : X14x.ART RT Σ5 m7 |- _ => pose proof (AF_LIB Σ5 m7 A7) as LC7; pose proof (af_client_consts RT AF Σ5 m7 A7) as CC7 end.
apply Hk. exists Σ5. split; [| split; [rewrite LV5; exact LV4|]; split; [rewrite FRS5; exact FRS4|]; split; [rewrite SP5; exact SP04|];
split; [rewrite CR5, CR4; rewrite ?CR; unfold NBD_EH_CREDIT; lia| rewrite POI5; exact POI4]].
unfold ASTA. eapply AST_conseq; [eassumption | | intros mo0 Hmo; exact Hmo].
intros ms <-. split.
+ unfold at_X_A. exists F7, fc7, m7. do 24 eexists.
exists (NBJ lol7 (eb1 ++ eb2 ++ eb3) (ST + 1368) oq6 iq4 msp4 hs5 pg4 lv6 (Z_to_bv 64 bp) lpg7 pgb7 (j_seed j) (j_pad1 j) (j_cbs j) (j_ucb j) (j_voc j) (j_pad2 j)).
exists (ys5 ++ oh2), sws, sG, (NBF (f_pitch ff) (f_pg ff) (f_lpc ff) (f_qlsp ff) aks4 (f_innov ff) (f_exc32 ff) (f_innov2 ff) iqs4).
split; [reflexivity|]. split; [exact FRM7|].

rewrite !f32_app in EXB. apply rw_cells_app in EXB as (EXB1 & EXB23). apply rw_cells_app in EXB23 as (EXB2 & EXB3).
rewrite !cells_size_f32, LEB1 in EXB2, EXB3. rewrite !cells_size_f32, LEB2 in EXB3.
replace (ST + 32 + Z.of_nat (4 * 294)) with (ST + 1208) in EXB2, EXB3 by lia.
replace (ST + 1208 + Z.of_nat (4 * 160)) with (ST + 1848) in EXB3 by lia.

split.
{ unfold nbctx. split; [exact MI7|]. split; [exact ST7|].
split.
{ unfold nb_pieces. cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain
j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
split.
{ unfold nb_hdr_cells. cbn [nb_end set_nb_pitch_gain_buf_idx set_nb_count_lost set_nb_first nb_first nb_count_lost nb_sampling_rate].
change [C8 (Z_to_bv 64 A_speex_nb_mode); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (nb_sampling_rate st)); C4 lol7; C8 (Z_to_bv 64 0)]
with ([C8 (Z_to_bv 64 A_speex_nb_mode)] ++ ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ ([C4 (Z_to_bv 64 (nb_sampling_rate st))] ++ ([C4 lol7] ++ [C8 (Z_to_bv 64 0)])))).
apply rw_cells_join; [exact HD0|]. cbn [cells_size csize Nat.add]. replace (ST + Z.of_nat 8) with (ST + 8) by lia.
apply rw_cells_join; [exact HD8'|]. cbn [cells_size csize Nat.add]. replace (ST + 8 + Z.of_nat 8) with (ST + 16) by lia.
apply rw_cells_join; [exact HD16|]. cbn [cells_size csize Nat.add]. replace (ST + 16 + Z.of_nat 4) with (ST + 20) by lia.
apply rw_cells_join; [exact HD20'|]. cbn [cells_size csize Nat.add]. replace (ST + 20 + Z.of_nat 4) with (ST + 24) by lia. exact HDR. }
split; [apply nbe_f32_join_win; [exact EXB1| rewrite LEB1; replace (ST + 32 + 4 * Z.of_nat 294) with (ST + 1208) by lia; exact EXB2| rewrite LEB1, LEB2; replace (ST + 32 + 4 * Z.of_nat 294 + 4 * Z.of_nat 160) with (ST + 1848) by lia; exact EXB3]|].
split; [exact EXP|]. split; [exact OQ6|]. split; [exact IQ4|]. split; [exact MSP4|]. split; [exact HS5|]. split; [exact PG4|].
split; [exact ISP|]. split; [exact LVL6|]. split; [exact LPP'|]. split; [exact PGB'|]. split; [exact IDX'|]. split; [exact SEED|].
split; [unfold nb_cfg_cells; exact CFG|]. split; [exact CBS|]. split; [unfold nb_ucb_cells, cb_cells; exact UCB|]. split; [exact VOC|].
unfold nb_tail_cells; exact TL. }
split.
{ unfold nb_junk_ok; cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch j_last_pitch_gain
j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2].
rewrite !length_app, LEB1, LEB2, LEB3. repeat split; first [reflexivity | assumption | apply LUCB]. }
split; [exact CBOK|].
split.
{ unfold nb_inv. cbn [nb_end set_nb_pitch_gain_buf_idx set_nb_count_lost set_nb_first nb_first nb_count_lost nb_encode_submode nb_highpass_enabled
nb_voc_offset nb_pitch_gain_buf_idx nb_submodeID nb_dtx_enabled nb_isWideband nb_lpc_enh_enabled nb_sampling_rate nb_innov_save].
repeat split; try assumption; try lia.
- destruct (Z.ltb_spec 2 (nb_pitch_gain_buf_idx st + 1)); lia.
- destruct (Z.ltb_spec 2 (nb_pitch_gain_buf_idx st + 1)); lia. }
split.
{ split; [exists rjb; split; [exact Lrjb| unfold bits_cells; exact BOBJ]|].
split; [exists bsb; split; [apply (proj2 (u8arr_rw_CB m7 (x_D X) bsb)); exact BDAT| exact Hbsb]| exact BSIDE]. }
split; [exact BOK|]. split; [exact BSZ|].
split.
{ rewrite f32_app. apply rw_cells_join; [exact YS5|]. rewrite cells_size_f32, LYS5.
replace (OUT + Z.of_nat (160 + (160 + (160 + (160 + 0))))) with (OUT + Z.of_nat (4 * 160)) in OW4 by lia. exact OW4. }
split; [rewrite length_app; lia|].
split; [exact SW|]. split; [exact LSW|].
split; [split; [exact SL4| exact SV]|].
split.
{ unfold fframe_at; cbn [f_pitch f_pg f_lpc f_qlsp f_ak f_innov f_exc32 f_innov2 f_iq].
split; [exact FF0|]. split; [exact FPI|]. split; [exact FPG|]. split; [exact FLPC|]. split; [exact QS4|]. split; [exact AK4|].
split; [exact FIN|]. split; [exact FE32|]. split; [exact FIN2| exact IQS4]. }
split.
{ unfold ff_ok; cbn [f_pitch f_pg f_lpc f_qlsp f_ak f_innov f_exc32 f_innov2 f_iq].
split; [exact LFPG|]. split; [exact LFLPC|]. split; [exact LFQS|]. split; [exact LAK4|]. split; [exact LFIN|]. split; [exact LFE32|].
split; [exact LFIN2| exact LIQS4]. }
split; [exists rest; exact SH7|].
split; [exact CC7|]. split; [exact LC7|]. split; [reflexivity|].
cbn [nb_end set_nb_pitch_gain_buf_idx set_nb_count_lost set_nb_first nb_innov_save]. exact JISV. }
split; [exact E48| exact E56].
+
lazymatch goal with |- context [ms_mem (MS _ _ _ _ _ ?mm _)] => change (ms_mem (MS _ _ _ _ _ mm _)) with mm end.
assert (PF7 : rt_pres_fp (rt_live RT Σ5) (rt_frames RT Σ5) (usp + -576)
[(ST, ST + 2968); (OUT, OUT + 4 * Z.of_nat nout); (A, A + BITS_SIZEOF); (FF, FF + 2048); (SF, SF + 256); (usp - 576, usp)] mE m7)
by (rewrite LV5, FRS5, LV4, FRS4, <- LV, <- FRS; exact PF).
split; [assumption|]. split; [exact (nbEH_acc_out Σ5 m7 m7 ltac:(assumption) ltac:(rewrite FRS5; exact FRS4) PF7)|].
split; [cps_wmono|].
rewrite <- LV, <- FRS. unfold nbW_EH, NBD_FRAME, NBSTATE_SIZEOF. replace (usp - 576) with (usp + -576) by lia. exact PF.

Qed.

End NbG.

