(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1df X1ck X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1nt X1rg X1rh X1re X1od X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X000 X04b X00c X07z X05o X05p X05s X05t
X0ae X09u X0af X09p X0ab X0a7 X09l X05l X071 X06v X06r
X06u X073 X07j X072.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12c X14x X0r0 X0ra X0qz X0v9 X0rb X0wl X0wm X110 X10c X10x X10t X108 X0xn X0xj X0xm X0xu X0ya X0xt.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X108 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xj OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ya OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xt.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Section Chunk.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis SBUF : ogg_sync_buffer_cps RT.
Hypothesis MCPY : memcpy_icontract RT e_asan_memcpy.
Hypothesis POUT : ogg_sync_pageout_cps RT.
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.

Lemma ch_h1_eq : forall h, 0 < h_bytes_remaining h -> hpure X h -> sync_fields_ok (h_oy h) ->
ch_h1 X h = set_bytes_remaining (set_ogg h (snd (sync_buffer_res (h_oy h) (ch_nbr h))) (h_os h))
(snd (ogg_sync_wrote (sync_write (snd (sync_buffer_res (h_oy h) (ch_nbr h))) (sy_fill (h_oy h) - sy_returned (h_oy h))
(ztake (ch_nbr h) (x_payload X))) (ch_nbr h)))
(h_bytes_remaining h - ch_nbr h).
Proof.
intros h BR HP FOK. pose proof HP as (_ & SI & (S0 & _) & SDN & _).
assert (NB : 0 < ch_nbr h) by (unfold ch_nbr, CHUNK; destruct (200 <? h_bytes_remaining h); lia).
destruct (sbuf_facts (h_oy h) (ch_nbr h) SI FOK NB SDN S0) as (EFST & _).
unfold ch_h1. destruct (sync_buffer_res (h_oy h) (ch_nbr h)) as [data oy1] eqn:ER. cbn [fst snd] in EFST |- *. rewrite EFST.
destruct (ogg_sync_wrote _ (ch_nbr h)) as [r0 oyw]. reflexivity.
Qed.

Theorem h_chunk_ok : h_chunk_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Proof using AF ERR_loc OUT_loc IO_img AF_DRV SBUF MCPY POUT.
intros HX h BRP T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & r2 & r7 & t3 & t4 & t5 & t6 & v40 & v48 & v56 & v88 & j224 & j232
& ogc & opc & Hc & FRM & HS & HR & OGJ & OPJ).
destruct OGJ as (g0 & g1 & g2 & g3 & ->). destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->).
pose proof HR as HR'. destruct HR' as (_ & MI & _ & _ & _ & _ & _ & SP & _ & _ & _ & _ & _ & SY & _ & _ & _ & _ & _ & _ & _ & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
unfold h_regs in Hc. unfold h_spill in SP.
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).
assert (BR4 : h_bytes_remaining h <= 4096) by (destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B & _);
pose proof (hi_pay _ _ _ HX) as (_ & SZ & _); unfold MAX_FUZZ_SIZE in SZ; lia).

refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply ch_w1; [split; [exact BRP| exact BR4] | exact SP | exact MI | exact S1R]. }
intros ms1 c1 -> Hc1. clear Hc.

set (m1 := m) in *. clearbody m1. rename HR into HR1. rename MI into MI1. clear SP SY.
pose proof HR1 as HR'. destruct HR' as (ART1 & _ & ST1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SY1 & _).
change (ch_nb (h_bytes_remaining h)) with (ch_nbr h) in Hc1.
assert (NB : 0 < ch_nbr h <= 200) by (unfold ch_nbr, CHUNK; destruct (Z.ltb_spec 200 (h_bytes_remaining h)); lia).
assert (NBB : ch_nbr h <= h_bytes_remaining h) by (unfold ch_nbr, CHUNK; destruct (Z.ltb_spec 200 (h_bytes_remaining h)); lia).
pose proof HP as (SI2 & SI & STB0 & SDN & _).
assert (PEND : 0 <= sy_fill (h_oy h) - sy_returned (h_oy h) <= 4096).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BR & _ & P1 & P2 & _). unfold h_consumed, h_pend in *.
pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ. lia. }
assert (SYL : sync_live RT Σ1 (h_oy h) (a_Dsy a)).
{ intros NS. rewrite EL. apply in_or_app. left. apply (Permutation_in _ (Permutation_sym PERM)). exact (own_in_Dsy a h NS). }
assert (INF : In (x_F X, 8%nat) (rt_frames RT Σ1)) by (rewrite EF; left; reflexivity).
assert (LVR : Z.of_nat (length (rt_live RT Σ1)) < LIVE_MAX).
{ rewrite (h_live_len RT X Σ1 a h HS).
pose proof (h_own_len RT OUT_rep ERR_rep IO_FP X Σ1 m1 a h _ _ _ HR1) as L24.
pose proof (hi_live _ _ _ HX) as (_ & LL). unfold H_LIVE in LL. lia. }
unfold HO_OY in SY1. pose proof SY1 as (_ & FOK & _).
Time cps_rt (SBUF Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (x_F X + 8480) (a_Dsy a) (ch_nbr h) (x_F X) (x_lo X) 8%nat
(h_oy h) (a_sybytes a)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ unfold bptr in *. lia. }
{ unfold bptr in *. lia. }
{ change (fs_size 8) with 16384. lia. }
{ exact (af_credit_nonneg RT AF Σ1 m1 ART1). }
{ rewrite unsigned_lit by lia. exact ST1. }
{ rewrite unsigned_lit by lia. unfold RT_STACK, H_STACK in *. lia. }
{ rewrite unsigned_lit by lia. unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by lia. clear - S32. Z.div_mod_to_equations. lia. }
intros c2 (Σ2 & D' & Hc2 & SL2 & CASE & EF2 & ES2 & EC2 & EP2). clear Hc1.
Time cps_unpack_lib Hc2 as (m2 & bytes2 & RS & RA2 & PR2 & SY2).
destruct RS as (-> & ->).
destruct (hrep_sbuf RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 Σ2 m1 m2 a h _ _ _ (ch_nbr h) D' bytes2 HS HR1
ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) NB RA2 PR2 SY2 CASE EF2 ES2 EC2 EP2) as (P2 & HS2 & HR2).
clear HR1 SY1 PR2 SY2 RA2 ART1 ST1.

destruct (sbuf_facts (h_oy h) (ch_nbr h) SI FOK ltac:(lia) SDN (proj1 STB0)) as (EFST & EFILL & ERET & EDATA & EBUF & SNOG & SGRO).
destruct (sy_compact_facts (h_oy h) SI FOK) as (_ & _ & _ & ECF & _).
rewrite ECF in Hc.
set (oy1 := snd (sync_buffer_res (h_oy h) (ch_nbr h))) in *.
unfold bptr in *.
assert (ROOM : sy_fill oy1 + ch_nbr h <= sy_storage oy1).
{ rewrite EFILL. destruct (Z_lt_ge_dec (sy_storage (h_oy h) - (sy_fill (h_oy h) - sy_returned (h_oy h))) (ch_nbr h)) as [LT|GE];
[rewrite (SGRO LT); lia| rewrite (SNOG GE); lia]. }
pose proof HR2 as HR'. destruct HR' as (ART2 & MI2 & ST2 & PF2 & _ & _ & _ & SP2 & _ & _ & _ & _ & _ & SY2 & _).

refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c2 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply ch_w2; [reflexivity | exact MI2]. }
intros ms3 c3 -> Hc3. clear Hc.

assert (SZP : 0 < x_size X) by (destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B & _); lia).
destruct (hi_pay _ _ _ HX) as (D0 & _ & _ & [(pp & pn & INP & PP1 & PP2) | EB]); [| unfold x_size in SZP; rewrite EB in SZP; cbn in SZP; lia].
pose proof (hi_live_geo _ _ _ HX pp pn INP) as (PG1 & _).
pose proof (h_payload_at OUT_rep IO_FP IO_img X HX m2 PF2) as BYP.
assert (LBS : Z.of_nat (length (firstn (Z.to_nat (ch_nbr h)) (x_bs X))) = ch_nbr h).
{ rewrite firstn_length_le; [lia|]. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B & _). unfold x_size in B. lia. }
assert (BYS : bytes_at bsegs m2 (x_d X) (firstn (Z.to_nat (ch_nbr h)) (x_bs X))).
{ rewrite <- (firstn_skipn (Z.to_nat (ch_nbr h)) (x_bs X)) in BYP. apply bytes_at_app in BYP. exact (proj1 BYP). }
pose proof HS2 as (EL2 & ND2 & PERM2 & EF2' & ESP2 & EPO2 & ECR2).
assert (INP2 : In (pp, pn) (rt_live RT Σ2)) by (rewrite EL2; apply in_or_app; right; exact INP).
assert (NSY : sy_data (h_oy (set_ogg h oy1 (h_os h))) <> None) by (cbn [set_ogg h_oy]; rewrite EDATA; discriminate).
pose proof (own_in_Dsy (a_set_sync a D' bytes2 P2) (set_ogg h oy1 (h_os h)) NSY) as INSY. cbn [a_set_sync a_Dsy set_ogg h_oy] in INSY.
assert (INSY2 : In (D', sy_storage oy1) (rt_live RT Σ2)).
{ rewrite EL2. apply in_or_app. left. exact (Permutation_in _ (Permutation_sym PERM2) INSY). }
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ2 m2 _ _ ART2 HS2) as HSP2.
destruct (proj1 HSP2 _ _ INSY) as (DP0 & DLO & _ & _ & _ & DSEP).
destruct SY2 as (_ & _ & DAT2 & _). unfold sync_data in DAT2. cbn [a_set_sync a_Dsy a_sybytes set_ogg h_oy] in DAT2. unfold bptr in DAT2. rewrite EDATA in DAT2.
destruct DAT2 as (_ & ARR2 & LEN2 & _).
assert (WRD : wr_at bsegs m2 (D' + (sy_fill (h_oy h) - sy_returned (h_oy h))) (ch_nbr h)).
{ destruct ARR2 as (_ & (W0 & W1 & W)). rewrite LEN2 in W1, W. split; [lia|]. split; [lia|]. intros i Hi.
replace (D' + (sy_fill (h_oy h) - sy_returned (h_oy h)) + i) with (D' + ((sy_fill (h_oy h) - sy_returned (h_oy h)) + i)) by lia. apply W. lia. }
Time cps_rt (MCPY Σ2 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2
(D' + (sy_fill (h_oy h) - sy_returned (h_oy h))) (x_d X) (firstn (Z.to_nat (ch_nbr h)) (x_bs X)) (x_lo X)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ rewrite LBS. reflexivity. }
{ rewrite EFILL in ROOM. unfold USTACK_TOP, RT_STACK, H_STACK in *. lia. }
{ unfold USTACK_TOP, RT_STACK, H_STACK in *. lia. }
{ rewrite LBS. apply (live_checked_src RT AF Σ2 m2 _ (x_lo X) pp pn (x_d X) (ch_nbr h) ART2 INP2 PP1); [| exact PG1].
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B & _). unfold x_size in *. lia. }
{ rewrite LBS. rewrite EFILL in ROOM. apply (live_checked_dst RT AF Σ2 m2 _ D' (sy_storage oy1) _ _ ART2 INSY2); [lia| lia| exact WRD]. }
{ rewrite LBS. rewrite EFILL in ROOM. destruct (DSEP pp pn INP) as [S|S];
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B & _); unfold x_size in *; lia. }
{ unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST2|]. split; [rewrite ESP2; pose proof (hi_lo _ _ _ HX) as (LW0 & _); exact LW0|].
split; [unfold RT_STACK, H_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|]. clear - S32. Z.div_mod_to_equations. lia. }
intros c4 Hc4. clear Hc3. rewrite LBS in Hc4.
unfold icpt_postF in Hc4.
Time cps_unpack_lib Hc4 as (m3 & RS3 & RA3 & PRX3 & BY3).
destruct RS3 as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & ->).
rewrite <- EFILL in PRX3, BY3.
assert (NBS : ch_nbr h <= x_size X)
by (destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B & _); lia).
rewrite EF2' in PRX3.
destruct (hrep_memcpy RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ2 m2 m3 (a_set_sync a D' bytes2 P2) (set_ogg h oy1 (h_os h))
_ _ _ (ch_nbr h) HS2 HR2 ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) EDATA ltac:(lia) ROOM NBS RA3
ltac:(rewrite EF2'; exact PRX3) BY3) as (HS3 & HR3).
clear HR2 PRX3 BY3 RA3 SP2 ARR2 WRD BYS BYP PF2 ST2 MI2 ART2.
pose proof HR3 as HR'. destruct HR' as (ART3 & MI3 & ST3 & PF3 & _ & _ & _ & SP3 & _ & _ & _ & _ & _ & SY3 & _).
cbn [a_set_sync a_Dsy a_sybytes set_ogg h_oy] in SY3. unfold HO_OY in SY3.
assert (SYD : D' + Z.of_nat (length (firstn (Z.to_nat (sy_fill oy1)) bytes2 ++ firstn (Z.to_nat (ch_nbr h)) (x_bs X) ++
skipn (Z.to_nat (sy_fill oy1 + ch_nbr h)) bytes2)) <= x_S1 X).
{ destruct SY3 as (_ & _ & DAT3 & _). unfold sync_data, bptr in DAT3. cbn [sync_write sy_data] in DAT3. rewrite EDATA in DAT3.
destruct DAT3 as (_ & _ & LB3 & _). cbn [sync_write sy_storage] in LB3. rewrite LB3. unfold RT_STACK, H_STACK in *. lia. }
assert (FILLB : sy_fill (sync_write oy1 (sy_fill oy1) (ztake (ch_nbr h) (x_payload X))) + ch_nbr h < 2^31).
{ cbn [sync_write sy_fill]. rewrite EFILL. lia. }

refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c4 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply ch_w3; [reflexivity | lia | lia | exact FILLB | lia | exact S1R | unfold RT_STACK, H_STACK in *; lia | left; exact SYD | exact SY3 | exact SP3 | exact MI3]. }
intros ms5 c5 (m4 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & -> & MU4 & WM4 & MI4 & SY4 & SP4) Hc5. clear Hc.
replace (x_F X + 8512) with (x_F X + 8480 + 32) in MU4 by lia.
pose proof (sbuf_inv2 (h_oy h) (ch_nbr h) SI2) as SI21. fold oy1 in SI21.
assert (BOKP : bytes_ok (ztake (ch_nbr h) (x_payload X))).
{ apply bytes_ok_ztake. unfold bytes_ok, x_payload. apply Forall_map. apply Forall_forall. intros b _.
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. }
destruct (sync_write_inv oy1 (ztake (ch_nbr h) (x_payload X)) (proj1 SI21) BOKP) as (_ & SWL & _).
rewrite zlength_ztake in SWL by (unfold x_size, zlength, x_payload in *; rewrite length_map; lia).
lazymatch type of SP4 with rw_cells _ _ _ ?sp' =>
destruct (hrep_wrote RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ2 m3 m4 _ _ _ sp' _ _ (ch_nbr h) HS3 HR3
ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; exact ROOM)
ltac:(cbn [set_ogg h_oy]; rewrite SWL; cbn [sync_write sy_fill]; lia) MU4 WM4 MI4 SY4 SP4) as (HS4 & HR4) end.
clear HR3 SY3 SY4 SP3 SP4 MU4 WM4 ART3 ST3 MI3 PF3.

lazymatch type of HS4 with hsig _ _ _ _ ?h3 => assert (EH3 : h3 = ch_h1 X h) end.
{ rewrite (ch_h1_eq h BRP HP FOK). fold oy1. unfold set_bytes_remaining. cbn [set_ogg h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule
h_skip_samples h_nframes h_eos h_channels h_rate h_extra_headers h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
rewrite EFILL. reflexivity. }
rewrite EH3 in HS4, HR4.
lazymatch type of HS4 with hsig _ _ _ ?aa _ => set (a3 := aa) in HS4, HR4 end.
set (hc := ch_h1 X h) in HS4, HR4.
pose proof HR4 as HR'. destruct HR' as (ART4 & MI4' & ST4 & _ & _ & _ & _ & SP4 & _ & _ & _ & _ & _ & SY4 & OGC4 & _ & _ & _ & _ & _ & _ & HP4).
pose proof HS4 as (EL4 & ND4 & PERM4 & EF4 & ESP4 & EPO4 & ECR4).
pose proof HP4 as (SI24 & SI4 & _).
destruct (ogg_sync_pageout (h_oy hc)) as [[[rp ogo] oy5]|] eqn:EPO; [| exfalso; exact (ogg_sync_pageout_total _ SI4 EPO)].
assert (SYL4 : sync_live RT Σ2 (h_oy hc) (a_Dsy a3)).
{ intros NS. rewrite EL4. apply in_or_app. left. apply (Permutation_in _ (Permutation_sym PERM4)). exact (own_in_Dsy a3 hc NS). }
assert (INF4 : In (x_F X, 8%nat) (rt_frames RT Σ2)) by (rewrite EF4; left; reflexivity).
unfold HO_OY, HO_OG in SY4, OGC4.
Time cps_rt (POUT Σ2 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 (x_F X + 8480) (x_F X + 8544) (a_Dsy a3) (x_F X) (x_lo X) 8%nat
(h_oy hc) (a_sybytes a3) g0 g1 g2 g3 rp ogo oy5).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ change (fs_size 8) with 16384. lia. }
{ change (fs_size 8) with 16384. lia. }
{ rewrite unsigned_lit by lia. exact ST4. }
{ rewrite unsigned_lit by lia. unfold RT_STACK, H_STACK in *. lia. }
{ rewrite unsigned_lit by lia. unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by lia. clear - S32. Z.div_mod_to_equations. lia. }
intros c6 Hc6. clear Hc5.
Time cps_unpack_lib Hc6 as (m5 & RS & RA5 & PR5 & SY5 & OG5).
destruct RS as (-> & ->).
destruct (hrep_pageout RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ2 m4 m5 a3 hc _ _ g0 g1 g2 g3 rp ogo oy5 HS4 HR4
ltac:(reflexivity) ltac:(reflexivity) EPO RA5 PR5 SY5 OG5) as (HS5 & HR5 & PGI).
clear HR4 SY4 OGC4 SY5 OG5 PR5 SP4 ART4 MI4' ST4.
pose proof HR5 as HR''. destruct HR'' as (_ & MI5 & _ & _ & _ & _ & _ & SP5 & _).
pose proof (pageout_ret _ _ _ _ EPO) as RR.

assert (BRS : h_bytes_remaining h <= x_size X)
by (destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B & _); lia).
pose proof HP as HPh. destruct HPh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SIR & _).
refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c6 (PMfd_mat_stable F0 fs0) Hc _ _).
{ unfold wz. eapply ch_w4; [reflexivity | lia | exact SIR | exact SP5 | exact MI5 | exact S1R]. }
intros ms7 c7 POST Hc7. clear Hc. cbv beta in POST.
apply Hk. unfold hc in *. rewrite <- EH3 in EPO, HS5, HR5, PGI |- *.
exists rp, ogo, oy5. split; [exact EPO|].
destruct POST as [(E1 & ->) | (NE & ->)].
- destruct ogo as [og|]; [| exfalso; exact (PGI E1)]. destruct PGI as (_ & POK & PBUD).
left. split; [exact E1|]. exists og. split; [reflexivity|].
exists Σ2, a3, Fx, fc, m5, (Z64 617820), r15, r16, r17, (Z64 rp), r19, r20, r21, r22, r23, r24, (Z64 (x_F X + 8480)), (Z64 (h_stream_init h)),
(Z64 (h_bytes_remaining h)), r25, r26, r27, r28, v48, v56, v88, j224, j232, [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
split; [unfold h_regs; cbn [set_ogg set_bytes_remaining h_stream_init h_packet_count h_channels h_eos]; exact Hc7|].
split; [exact FRM|]. split; [exact HS5|].
split; [unfold h_iter; cbn [set_ogg set_bytes_remaining h_bytes_remaining]; unfold CHUNK; lia|].
split; [exact HR5|]. split; [do 6 eexists; reflexivity| split; [exact POK| exact PBUD]].
- destruct ogo as [og|]; [exfalso; exact (NE (proj1 PGI))|].
right. split; [exact NE|].
exists Σ2, a3, Fx, fc, m5, (Z64 617820), r15, r16, r17, (Z64 rp), (Z64 1), r19, r20, r21, r22, r23, r24, (Z64 (x_F X + 8480)),
(Z64 (h_bytes_remaining h)), (Z64 (x_F X + 8544)), r25, r26, r27, r28, v48, v56, v88, j224, j232,
[CB 8 g0; CB 8 g1; CB 8 g2; CB 8 g3], [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
split; [unfold h_regs; cbn [set_ogg set_bytes_remaining h_stream_init h_packet_count h_channels h_eos]; exact Hc7|].
split; [exact FRM|]. split; [exact HS5|].
split; [unfold h_iter; cbn [set_ogg set_bytes_remaining h_bytes_remaining]; unfold CHUNK; lia|].
split; [exact HR5|]. split; [do 4 eexists; reflexivity| do 6 eexists; reflexivity].
Qed.
End Chunk.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Section Chunk.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis SBUF : ogg_sync_buffer_cps RT.
Hypothesis MCPY : memcpy_icontract RT e_asan_memcpy.
Hypothesis POUT : ogg_sync_pageout_cps RT.
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.

Lemma ch_h1_eq : forall h, 0 < h_bytes_remaining h -> hpure X h -> sync_fields_ok (h_oy h) ->
ch_h1 X h = set_bytes_remaining (set_ogg h (snd (sync_buffer_res (h_oy h) (ch_nbr h))) (h_os h))
(snd (ogg_sync_wrote (sync_write (snd (sync_buffer_res (h_oy h) (ch_nbr h))) (sy_fill (h_oy h) - sy_returned (h_oy h))
(ztake (ch_nbr h) (x_payload X))) (ch_nbr h)))
(h_bytes_remaining h - ch_nbr h).
Proof.
intros h BR HP FOK. pose proof HP as (_ & SI & (S0 & _) & SDN & _).
assert (NB : 0 < ch_nbr h) by (unfold ch_nbr, CHUNK; destruct (200 <? h_bytes_remaining h); lia).
destruct (sbuf_facts (h_oy h) (ch_nbr h) SI FOK NB SDN S0) as (EFST & _).
unfold ch_h1. destruct (sync_buffer_res (h_oy h) (ch_nbr h)) as [data oy1] eqn:ER. cbn [fst snd] in EFST |- *. rewrite EFST.
destruct (ogg_sync_wrote _ (ch_nbr h)) as [r0 oyw]. reflexivity.
Qed.

Theorem h_chunk_ok : h_chunk_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Proof using AF ERR_loc OUT_loc IO_img AF_DRV SBUF MCPY POUT.
intros HX h BRP T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a1 & a4 & a5 & a6 & a7 & r5 & r7 & t3 & t4 & t5 & t6 & v80 & v88 & v144 & v176 & j0 & j192 & j200
& ogc & opc & Hc & FRM & HS & HR & OGJ & OPJ).
destruct OGJ as (g0 & g1 & g2 & g3 & ->). destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->).
pose proof HR as HR'. destruct HR' as (_ & MI & _ & _ & _ & _ & _ & SP & _ & _ & _ & _ & _ & SY & _ & _ & _ & _ & _ & _ & _ & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
unfold h_regs in Hc. unfold h_spill in SP.
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).
assert (BR4 : h_bytes_remaining h <= 4096) by (destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B & _);
pose proof (hi_pay _ _ _ HX) as (_ & SZ & _); unfold MAX_FUZZ_SIZE in SZ; lia).

refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply ch_w1; [split; [exact BRP| exact BR4] | exact SP | exact MI | exact S1R]. }
intros ms1 c1 (m1 & -> & MU1 & WM1 & MI1 & SP1) Hc1. clear Hc.
lazymatch type of SP1 with rw_cells _ _ _ ?sp' =>
pose proof (hrep_spill RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m1 a h _ sp' _ _ HS HR
ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) MU1 WM1 MI1 SP1) as HR1 end.
clear HR SP MI MU1 WM1 SY.
pose proof HR1 as HR'. destruct HR' as (ART1 & _ & ST1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SY1 & _).
change (ch_nb (h_bytes_remaining h)) with (ch_nbr h) in Hc1.
assert (NB : 0 < ch_nbr h <= 200) by (unfold ch_nbr, CHUNK; destruct (Z.ltb_spec 200 (h_bytes_remaining h)); lia).
assert (NBB : ch_nbr h <= h_bytes_remaining h) by (unfold ch_nbr, CHUNK; destruct (Z.ltb_spec 200 (h_bytes_remaining h)); lia).
pose proof HP as (SI2 & SI & STB0 & SDN & _).
assert (PEND : 0 <= sy_fill (h_oy h) - sy_returned (h_oy h) <= 4096).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BR & _ & P1 & P2 & _). unfold h_consumed, h_pend in *.
pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ. lia. }
assert (SYL : sync_live RT Σ1 (h_oy h) (a_Dsy a)).
{ intros NS. rewrite EL. apply in_or_app. left. apply (Permutation_in _ (Permutation_sym PERM)). exact (own_in_Dsy a h NS). }
assert (INF : In (x_F X, 8%nat) (rt_frames RT Σ1)) by (rewrite EF; left; reflexivity).
assert (LVR : Z.of_nat (length (rt_live RT Σ1)) < LIVE_MAX).
{ rewrite (h_live_len RT X Σ1 a h HS).
pose proof (h_own_len RT OUT_rep ERR_rep IO_FP X Σ1 m1 a h _ _ _ HR1) as L24.
pose proof (hi_live _ _ _ HX) as (_ & LL). unfold H_LIVE in LL. lia. }
unfold HO_OY in SY1. pose proof SY1 as (_ & FOK & _).
Time cps_rt (SBUF Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (x_F X + 8480) (a_Dsy a) (ch_nbr h) (x_F X) (x_lo X) 8%nat
(h_oy h) (a_sybytes a)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ unfold bptr in *. lia. }
{ unfold bptr in *. lia. }
{ change (fs_size 8) with 16384. lia. }
{ exact (af_credit_nonneg RT AF Σ1 m1 ART1). }
{ rewrite unsigned_lit by lia. exact ST1. }
{ rewrite unsigned_lit by lia. unfold RT_STACK, H_STACK in *. lia. }
{ rewrite unsigned_lit by lia. unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by lia. clear - S32. Z.div_mod_to_equations. lia. }
intros c2 (Σ2 & D' & Hc2 & SL2 & CASE & EF2 & ES2 & EC2 & EP2). clear Hc1.
Time cps_unpack_lib Hc2 as (m2 & bytes2 & RS & RA2 & PR2 & SY2).
destruct RS as (-> & ->).
destruct (hrep_sbuf RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 Σ2 m1 m2 a h _ _ _ (ch_nbr h) D' bytes2 HS HR1
ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) NB RA2 PR2 SY2 CASE EF2 ES2 EC2 EP2) as (P2 & HS2 & HR2).
clear HR1 SY1 PR2 SY2 RA2 ART1 ST1.

destruct (sbuf_facts (h_oy h) (ch_nbr h) SI FOK ltac:(lia) SDN (proj1 STB0)) as (EFST & EFILL & ERET & EDATA & EBUF & SNOG & SGRO).
destruct (sy_compact_facts (h_oy h) SI FOK) as (_ & _ & _ & ECF & _).
rewrite ECF in Hc.
set (oy1 := snd (sync_buffer_res (h_oy h) (ch_nbr h))) in *.
unfold bptr in *.
assert (ROOM : sy_fill oy1 + ch_nbr h <= sy_storage oy1).
{ rewrite EFILL. destruct (Z_lt_ge_dec (sy_storage (h_oy h) - (sy_fill (h_oy h) - sy_returned (h_oy h))) (ch_nbr h)) as [LT|GE];
[rewrite (SGRO LT); lia| rewrite (SNOG GE); lia]. }
pose proof HR2 as HR'. destruct HR' as (ART2 & MI2 & ST2 & PF2 & _ & _ & _ & SP2 & _ & _ & _ & _ & _ & SY2 & _).

refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c2 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply ch_w2; [reflexivity | exact SP2 | exact MI2 | exact S1R]. }
intros ms3 c3 -> Hc3. clear Hc.

assert (SZP : 0 < x_size X) by (destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B & _); lia).
destruct (hi_pay _ _ _ HX) as (D0 & _ & _ & [(pp & pn & INP & PP1 & PP2) | EB]); [| unfold x_size in SZP; rewrite EB in SZP; cbn in SZP; lia].
pose proof (hi_live_geo _ _ _ HX pp pn INP) as (PG1 & _).
pose proof (h_payload_at OUT_rep IO_FP IO_img X HX m2 PF2) as BYP.
assert (LBS : Z.of_nat (length (firstn (Z.to_nat (ch_nbr h)) (x_bs X))) = ch_nbr h).
{ rewrite firstn_length_le; [lia|]. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B & _). unfold x_size in B. lia. }
assert (BYS : bytes_at asegs m2 (x_d X) (firstn (Z.to_nat (ch_nbr h)) (x_bs X))).
{ rewrite <- (firstn_skipn (Z.to_nat (ch_nbr h)) (x_bs X)) in BYP. apply bytes_at_app in BYP. exact (proj1 BYP). }
pose proof HS2 as (EL2 & ND2 & PERM2 & EF2' & ESP2 & EPO2 & ECR2).
assert (INP2 : In (pp, pn) (rt_live RT Σ2)) by (rewrite EL2; apply in_or_app; right; exact INP).
assert (NSY : sy_data (h_oy (set_ogg h oy1 (h_os h))) <> None) by (cbn [set_ogg h_oy]; rewrite EDATA; discriminate).
pose proof (own_in_Dsy (a_set_sync a D' bytes2 P2) (set_ogg h oy1 (h_os h)) NSY) as INSY. cbn [a_set_sync a_Dsy set_ogg h_oy] in INSY.
assert (INSY2 : In (D', sy_storage oy1) (rt_live RT Σ2)).
{ rewrite EL2. apply in_or_app. left. exact (Permutation_in _ (Permutation_sym PERM2) INSY). }
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ2 m2 _ _ ART2 HS2) as HSP2.
destruct (proj1 HSP2 _ _ INSY) as (DP0 & DLO & _ & _ & _ & DSEP).
destruct SY2 as (_ & _ & DAT2 & _). unfold sync_data in DAT2. cbn [a_set_sync a_Dsy a_sybytes set_ogg h_oy] in DAT2. unfold bptr in DAT2. rewrite EDATA in DAT2.
destruct DAT2 as (_ & ARR2 & LEN2 & _).
assert (WRD : wr_at asegs m2 (D' + (sy_fill (h_oy h) - sy_returned (h_oy h))) (ch_nbr h)).
{ destruct ARR2 as (_ & (W0 & W1 & W)). rewrite LEN2 in W1, W. split; [lia|]. split; [lia|]. intros i Hi.
replace (D' + (sy_fill (h_oy h) - sy_returned (h_oy h)) + i) with (D' + ((sy_fill (h_oy h) - sy_returned (h_oy h)) + i)) by lia. apply W. lia. }
Time cps_rt (MCPY Σ2 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2
(D' + (sy_fill (h_oy h) - sy_returned (h_oy h))) (x_d X) (firstn (Z.to_nat (ch_nbr h)) (x_bs X)) (x_lo X)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ rewrite LBS. reflexivity. }
{ rewrite EFILL in ROOM. unfold USTACK_TOP, RT_STACK, H_STACK in *. lia. }
{ unfold USTACK_TOP, RT_STACK, H_STACK in *. lia. }
{ rewrite LBS. apply (live_checked_src RT AF Σ2 m2 _ (x_lo X) pp pn (x_d X) (ch_nbr h) ART2 INP2 PP1); [| exact PG1].
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B & _). unfold x_size in *. lia. }
{ rewrite LBS. rewrite EFILL in ROOM. apply (live_checked_dst RT AF Σ2 m2 _ D' (sy_storage oy1) _ _ ART2 INSY2); [lia| lia| exact WRD]. }
{ rewrite LBS. rewrite EFILL in ROOM. destruct (DSEP pp pn INP) as [S|S];
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B & _); unfold x_size in *; lia. }
{ unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST2|]. split; [rewrite ESP2; pose proof (hi_lo _ _ _ HX) as (LW0 & _); exact LW0|].
split; [unfold RT_STACK, H_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|]. clear - S32. Z.div_mod_to_equations. lia. }
intros c4 Hc4. clear Hc3. rewrite LBS in Hc4.
unfold icpt_postF in Hc4.
Time cps_unpack_lib Hc4 as (m3 & RS3 & RA3 & PRX3 & BY3).
destruct RS3 as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & ->).
rewrite <- EFILL in PRX3, BY3.
assert (NBS : ch_nbr h <= x_size X)
by (destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B & _); lia).
rewrite EF2' in PRX3.
destruct (hrep_memcpy RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ2 m2 m3 (a_set_sync a D' bytes2 P2) (set_ogg h oy1 (h_os h))
_ _ _ (ch_nbr h) HS2 HR2 ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) EDATA ltac:(lia) ROOM NBS RA3
ltac:(rewrite EF2'; exact PRX3) BY3) as (HS3 & HR3).
clear HR2 PRX3 BY3 RA3 SP2 ARR2 WRD BYS BYP PF2 ST2 MI2 ART2.
pose proof HR3 as HR'. destruct HR' as (ART3 & MI3 & ST3 & PF3 & _ & _ & _ & SP3 & _ & _ & _ & _ & _ & SY3 & _).
cbn [a_set_sync a_Dsy a_sybytes set_ogg h_oy] in SY3. unfold HO_OY in SY3.
assert (SYD : D' + Z.of_nat (length (firstn (Z.to_nat (sy_fill oy1)) bytes2 ++ firstn (Z.to_nat (ch_nbr h)) (x_bs X) ++
skipn (Z.to_nat (sy_fill oy1 + ch_nbr h)) bytes2)) <= x_S1 X).
{ destruct SY3 as (_ & _ & DAT3 & _). unfold sync_data, bptr in DAT3. cbn [sync_write sy_data] in DAT3. rewrite EDATA in DAT3.
destruct DAT3 as (_ & _ & LB3 & _). cbn [sync_write sy_storage] in LB3. rewrite LB3. unfold RT_STACK, H_STACK in *. lia. }
assert (FILLB : sy_fill (sync_write oy1 (sy_fill oy1) (ztake (ch_nbr h) (x_payload X))) + ch_nbr h < 2^31).
{ cbn [sync_write sy_fill]. rewrite EFILL. lia. }

refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c4 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply ch_w3; [reflexivity | lia | exact FILLB | lia | exact S1R | unfold RT_STACK, H_STACK in *; lia | left; exact SYD | exact SY3 | exact SP3 | exact MI3]. }
intros ms5 c5 (m4 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & -> & MU4 & WM4 & MI4 & SY4 & SP4) Hc5. clear Hc.
replace (x_F X + 8512) with (x_F X + 8480 + 32) in MU4 by lia.
pose proof (sbuf_inv2 (h_oy h) (ch_nbr h) SI2) as SI21. fold oy1 in SI21.
assert (BOKP : bytes_ok (ztake (ch_nbr h) (x_payload X))).
{ apply bytes_ok_ztake. unfold bytes_ok, x_payload. apply Forall_map. apply Forall_forall. intros b _.
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. }
destruct (sync_write_inv oy1 (ztake (ch_nbr h) (x_payload X)) (proj1 SI21) BOKP) as (_ & SWL & _).
rewrite zlength_ztake in SWL by (unfold x_size, zlength, x_payload in *; rewrite length_map; lia).
lazymatch type of SP4 with rw_cells _ _ _ ?sp' =>
destruct (hrep_wrote RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ2 m3 m4 _ _ _ sp' _ _ (ch_nbr h) HS3 HR3
ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; exact ROOM)
ltac:(cbn [set_ogg h_oy]; rewrite SWL; cbn [sync_write sy_fill]; lia) MU4 WM4 MI4 SY4 SP4) as (HS4 & HR4) end.
clear HR3 SY3 SY4 SP3 SP4 MU4 WM4 ART3 ST3 MI3 PF3.

lazymatch type of HS4 with hsig _ _ _ _ ?h3 => assert (EH3 : h3 = ch_h1 X h) end.
{ rewrite (ch_h1_eq h BRP HP FOK). fold oy1. unfold set_bytes_remaining. cbn [set_ogg h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule
h_skip_samples h_nframes h_eos h_channels h_rate h_extra_headers h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
rewrite EFILL. reflexivity. }
rewrite EH3 in HS4, HR4.
lazymatch type of HS4 with hsig _ _ _ ?aa _ => set (a3 := aa) in HS4, HR4 end.
set (hc := ch_h1 X h) in HS4, HR4.
pose proof HR4 as HR'. destruct HR' as (ART4 & MI4' & ST4 & _ & _ & _ & _ & SP4 & _ & _ & _ & _ & _ & SY4 & OGC4 & _ & _ & _ & _ & _ & _ & HP4).
pose proof HS4 as (EL4 & ND4 & PERM4 & EF4 & ESP4 & EPO4 & ECR4).
pose proof HP4 as (SI24 & SI4 & _).
destruct (ogg_sync_pageout (h_oy hc)) as [[[rp ogo] oy5]|] eqn:EPO; [| exfalso; exact (ogg_sync_pageout_total _ SI4 EPO)].
assert (SYL4 : sync_live RT Σ2 (h_oy hc) (a_Dsy a3)).
{ intros NS. rewrite EL4. apply in_or_app. left. apply (Permutation_in _ (Permutation_sym PERM4)). exact (own_in_Dsy a3 hc NS). }
assert (INF4 : In (x_F X, 8%nat) (rt_frames RT Σ2)) by (rewrite EF4; left; reflexivity).
unfold HO_OY, HO_OG in SY4, OGC4.
Time cps_rt (POUT Σ2 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 (x_F X + 8480) (x_F X + 8544) (a_Dsy a3) (x_F X) (x_lo X) 8%nat
(h_oy hc) (a_sybytes a3) g0 g1 g2 g3 rp ogo oy5).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ change (fs_size 8) with 16384. lia. }
{ change (fs_size 8) with 16384. lia. }
{ rewrite unsigned_lit by lia. exact ST4. }
{ rewrite unsigned_lit by lia. unfold RT_STACK, H_STACK in *. lia. }
{ rewrite unsigned_lit by lia. unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by lia. clear - S32. Z.div_mod_to_equations. lia. }
intros c6 Hc6. clear Hc5.
Time cps_unpack_lib Hc6 as (m5 & RS & RA5 & PR5 & SY5 & OG5).
destruct RS as (-> & ->).
destruct (hrep_pageout RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ2 m4 m5 a3 hc _ _ g0 g1 g2 g3 rp ogo oy5 HS4 HR4
ltac:(reflexivity) ltac:(reflexivity) EPO RA5 PR5 SY5 OG5) as (HS5 & HR5 & PGI).
clear HR4 SY4 OGC4 SY5 OG5 PR5 SP4 ART4 MI4' ST4.
pose proof HR5 as HR''. destruct HR'' as (_ & MI5 & _ & _ & _ & _ & _ & SP5 & _).
pose proof (pageout_ret _ _ _ _ EPO) as RR.

assert (BRS : h_bytes_remaining h <= x_size X)
by (destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B & _); lia).
pose proof HP as HPh. destruct HPh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SIR & _).
refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c6 (PMfd_mat_stable F0 fs0) Hc _ _).
{ unfold wz. eapply ch_w4; [reflexivity | lia | exact SIR | exact SP5 | exact MI5 | exact S1R]. }
intros ms7 c7 POST Hc7. clear Hc. cbv beta in POST.
apply Hk. unfold hc in *. rewrite <- EH3 in EPO, HS5, HR5, PGI |- *.
exists rp, ogo, oy5. split; [exact EPO|].
destruct POST as [(E1 & ->) | (NE & ->)].
- destruct ogo as [og|]; [| exfalso; exact (PGI E1)]. destruct PGI as (_ & POK & PBUD).
left. split; [exact E1|]. exists og. split; [reflexivity|].
exists Σ2, a3, Fx, fc, m5, (Z64 617556), r15, r16, r17, (Z64 rp), r20, r21, r22, r23, r24, (Z64 (ch_nbr h)), (Z64 (h_stream_init h)), r25, r26, r27, r28,
j0, j192, j200, [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
split; [unfold h_regs; cbn [set_ogg set_bytes_remaining h_stream_init h_last_granule h_packet_count]; exact Hc7|].
split; [exact FRM|]. split; [exact HS5|].
split; [unfold h_iter; cbn [set_ogg set_bytes_remaining h_bytes_remaining]; unfold CHUNK; lia|].
split; [exact HR5|]. split; [do 6 eexists; reflexivity| split; [exact POK| exact PBUD]].
- destruct ogo as [og|]; [exfalso; exact (NE (proj1 PGI))|].
right. split; [exact NE|].
exists Σ2, a3, Fx, fc, m5, (Z64 617556), r15, r16, r17, (Z64 rp), (Z64 1), r20, r21, r22, r23, r24, (Z64 (ch_nbr h)), r25, r26, r27, r28,
j0, j192, j200, [CB 8 g0; CB 8 g1; CB 8 g2; CB 8 g3], [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
split; [unfold h_regs; cbn [set_ogg set_bytes_remaining h_stream_init h_last_granule h_packet_count]; exact Hc7|].
split; [exact FRM|]. split; [exact HS5|].
split; [unfold h_iter; cbn [set_ogg set_bytes_remaining h_bytes_remaining]; unfold CHUNK; lia|].
split; [exact HR5|]. split; [do 4 eexists; reflexivity| do 6 eexists; reflexivity].
Qed.
End Chunk.
