(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1nt X1rg X1rh X1re X1od X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1qy X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X000 X04b X00c X07z X05o X05p X05s X05t
X0ae X09j X09u X0af X09x X09p X0ab X09l X0a4 X0a5
X05l X05e X05c X05j X05i X06c X05m X09f X08y X09e X06d X069 X068 X07m
X071 X06v X06y X06u X073 X07j X072 X079 X07h
X077 X076 X07f X07e X07b X07a.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12c X14x X0r0 X0ra X0qz X0v9 X0rb X0wl X0wm X110 X106 X10j X10c X10x X108 X10q X10r X0wb X0w9 X0wg X0wf X0x5 X0zq X0x2 X0x1 X0xn X0xq X0xm X0xu X0ya X0xt X0y0 X0y8 X0y6 X0y5 X0y2 X0y1.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X108 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wg OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wf OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ya OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y8 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y6 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Section Pkt.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis IO_drv : forall y, in_ranges IO_FP y -> ~ drv_cell y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis DEC : forall d, dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode d.
Hypothesis ISAVE : forall (d d' : dec_state bptr) b q ret b' q',
prun (speex_decode (St := pst) p_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M d b 0) q = Some ((ret, d', b'), q') ->
isave_ok d -> isave_ok d'.
Hypothesis RF : speex_bits_read_from_cps RT OUT_rep ERR_rep IO_FP.
Hypothesis BCMP : bcmp_icontract RT.
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.
Hypothesis FD2 : fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Hypothesis HDR : h_hdr_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.

Lemma hpure_incr : forall (h : hstate unit), hinv_ok OUT_rep IO_FP X -> hpure X h -> pc_room X h ->
os_lacing_returned (h_os h) <= os_lacing_fill (h_os h) -> hpure X (incr_packet_count h).
Proof.
intros h HX HP (PR1 & PR2) LRF. pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ.
unfold hpure, h_consumed, h_pend in *.
cbn [incr_packet_count h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
do 14 (split; [assumption|]). split; [lia|]. do 4 (split; [assumption|]).
split; [destruct (h_st h); [lia| exfalso; exact (PR2 eq_refl)]|].
repeat split; lia.
Qed.

Lemma hrep_incr : forall (Σ1 : rts RT) (m : mem) a (h : hstate unit) spill ogc opc, hinv_ok OUT_rep IO_FP X ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc -> pc_room X h -> h_stream_init h <> 0 ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a (incr_packet_count h) spill ogc opc.
Proof.
intros Σ1 m a h spill ogc opc HX HR PRM SI.
destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & HP).
assert (LRF : os_lacing_returned (h_os h) <= os_lacing_fill (h_os h)).
{ unfold h_os_rep in A17. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0|_]; [exfalso; exact (SI E0)|].
destruct A17 as (_ & _ & _ & _ & (I1 & I2 & _) & _). lia. }
unfold hrep. cbn [incr_packet_count h_frame_size h_bits h_oy h_rate].
do 16 (split; [assumption|]).
split; [unfold h_os_rep in *; cbn [incr_packet_count h_stream_init h_os]; exact A17|].
do 3 (split; [assumption|]).
split; [unfold h_dec_rep in *; cbn [incr_packet_count h_st]; exact A21|].
exact (hpure_incr h HX HP PRM LRF).
Qed.

Lemma hsig_incr : forall (Σ1 : rts RT) a (h : hstate unit), hsig_k RT X Σ1 a h (10 * H_DEC_CREDIT) -> hsig RT X Σ1 a (incr_packet_count h).
Proof.
intros Σ1 a h (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold hsig, h_own, h_cost in *.
cbn [incr_packet_count h_st h_bits h_stream_init h_os h_oy h_packet_count]. repeat split; try assumption. lia.
Qed.

Theorem h_kt_ok : hinv_ok OUT_rep IO_FP X -> forall (h : hstate unit) (pno nbr brem0 : Z),
cps bsegs (at_KT RT OUT_rep ERR_rep IO_FP X F0 fs0 h pno nbr brem0)
(fun c => (h_eos h = 0 /\ at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 (incr_packet_count h) pno nbr brem0 c)
\/ (h_eos h = 1 /\ at_PN RT OUT_rep ERR_rep IO_FP X F0 fs0 (incr_packet_count h) nbr brem0 c)).
Proof using AF ERR_loc OUT_loc IO_img AF_DRV.
intros HX h pno nbr brem0 T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r2 & r7 & r9 & r10 & t3 & t4 & t5 & t6
& v48 & v56 & v88 & j224 & j232 & ogc & opc & Hc & FRM & HS & HIT & SI1 & EOR & PNR & SKW & HR & OGJ & OPJ & PRM).
pose proof HR as HR'. destruct HR' as (ART & MI & ST & _ & _ & _ & _ & SP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PCR & _).
unfold h_spill in SP. unfold h_regs in Hc.
refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply (kt_w (x_S1 X) (x_F X) (h_packet_count h) (h_eos h)); [exact S1R| lia| exact EOR| exact SP| exact MI]. }
intros ms1 c1 [(E0 & ->) | (E1 & ->)] Hc1.
-
apply Hk. left. split; [exact E0|].
exists Σ1, a, Fx, fc, m, ra, t0, t1, t2, (Z64 (h_packet_count h + 1)), a1, a2, a3, a4, a5, a6, a7, r2, (Z64 0), r10, t3, t4, t5, t6,
v48, v56, v88, j224, j232, ogc, opc.
split; [unfold h_regs; cbn [incr_packet_count h_packet_count h_channels]; unfold HO_OS, HO_OG; exact Hc1|].
split; [exact FRM|]. split; [exact (hsig_incr Σ1 a h HS)|]. split; [exact HIT|]. split; [exact SI1|].
split; [cbn [incr_packet_count h_eos]; exact E0|]. split; [cbn [incr_packet_count h_packet_count]; lia|].
split; [exact SKW|]. split; [cbn [incr_packet_count h_packet_count]; intros; lia|].
split; [exact (hrep_incr Σ1 m a h _ ogc opc HX HR PRM ltac:(rewrite SI1; discriminate))|]. split; [exact OGJ| exact OPJ].
-
apply Hk. right. split; [exact E1|].
exists Σ1, a, Fx, fc, m, ra, t0, t1, t2, (Z64 (h_packet_count h + 1)), a1, a2, a3, a4, a5, a6, a7, r2, (Z64 1), (Z64 pno), t3, t4, t5, t6,
v48, v56, v88, j224, j232, ogc, opc.
split; [unfold h_regs; cbn [incr_packet_count h_packet_count h_channels h_eos]; rewrite E1; unfold HO_OS, HO_OG; exact Hc1|].
split; [exact FRM|]. split; [exact (hsig_incr Σ1 a h HS)|]. split; [exact HIT|]. split; [exact SI1|].
split; [exact (hrep_incr Σ1 m a h _ ogc opc HX HR PRM ltac:(rewrite SI1; discriminate))|]. split; [exact OGJ| exact OPJ].
Qed.

Lemma dec_bounds : forall d : dec_state bptr, (dec_depth d <= 3)%nat ->
dec_stack d <= H_STACK /\ (dec_frames d <= 15)%nat /\ dec_credit d <= H_DEC_CREDIT.
Proof.
intros d Hd.
assert (SBS : (SB_OWN_STACK <=? 20000) && (0 <=? SB_OWN_STACK) = true) by reflexivity.
assert (NBS : (NBDEC_STACK <=? 20000) && (0 <=? NBDEC_STACK) = true) by reflexivity.
assert (NBC : (NBDEC_CREDIT <=? 8) && (1 <=? NBDEC_CREDIT) = true) by reflexivity.
apply andb_true_iff in SBS as (SBS1 & SBS2). apply andb_true_iff in NBS as (NBS1 & NBS2). apply andb_true_iff in NBC as (NBC1 & NBC2).
apply Z.leb_le in SBS1, SBS2, NBS1, NBS2, NBC1, NBC2.
destruct d as [st | s1 [st | s2 [st | s3 low]]]; cbn [dec_depth] in Hd;
cbn [dec_stack dec_frames dec_credit dec_depth]; unfold H_STACK, H_DEC_CREDIT, NBDEC_FRAMES; try lia.
pose proof (dec_depth_pos low). lia.
Qed.

Lemma hrep_set_eos : forall (Σ1 : rts RT) (m : mem) a (h : hstate unit) spill ogc opc e, (e = 0 \/ e = 1) ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a (set_bits_st h (h_bits h) (h_st h) e) spill ogc opc.
Proof.
intros Σ1 m a h spill ogc opc e EE HR.
destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & HP).
unfold hrep. cbn [set_bits_st h_frame_size h_bits h_oy h_rate].
do 16 (split; [assumption|]).
split; [unfold h_os_rep in *; cbn [set_bits_st h_stream_init h_os]; exact A17|].
do 3 (split; [assumption|]).
split; [unfold h_dec_rep in *; cbn [set_bits_st h_st]; exact A21|].
unfold hpure, h_consumed, h_pend in *.
cbn [set_bits_st h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18 & REST).
do 17 (split; [assumption|]). split; [exact EE| exact REST].
Qed.

Theorem h_dstep_ok : hinv_ok OUT_rep IO_FP X -> forall (n : nat) (h : hstate unit) (st : dec_state unit) (b : bits_st unit) (eosf pno nbr brem0 : Z)
(q q1 : pst) ret (st1 : dec_state unit) (b1 : bits_st unit) bs,
prun (speex_decode (St := pst) p_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M st b 0) q = Some ((ret, st1, b1), q1) ->
p_err q1 = p_err q ++ bs ->
cpsE bsegs (at_DHk RT OUT_rep ERR_rep IO_FP X F0 fs0 h st b (S n) eosf pno nbr brem0) (Spec.X1nu.evw 2 bs)
(fun c => ((((ret =? -1) || (ret =? -2)) = true \/ speex_bits_remaining b1 < 0 \/ n = 0%nat)
/\ at_KT RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_bits_st h b1 (Some st1) eosf) pno nbr brem0 c)
\/ (((ret =? -1) || (ret =? -2)) = false /\ 0 <= speex_bits_remaining b1 /\ (1 <= n)%nat
/\ at_DHk RT OUT_rep ERR_rep IO_FP X F0 fs0 h st1 b1 n eosf pno nbr brem0 c)).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE FD2.
intros HX n h st b eosf pno nbr brem0 q q1 ret st1 b1 bs RUN EB T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & t3 & t4 & t5 & t6 & v48 & v56 & v88 & j224 & j232 & ogc & opc
& Hc & FRM & NR1 & NR2 & EOR & STN & E0 & PNR & HS & HIT & SI1 & SKW & FLG & HR & OGJ & OPJ & PRM).
set (hD := set_bits_st h b (Some st) 0) in *.
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a hD _ ogc opc HR) as OPOS.
pose proof HR as HR'. destruct HR' as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC
& OSR & (stb & STB) & RATE & (wl & LOOK & LKR) & DEC0 & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
pose proof (hsep_of_k RT AF OUT_rep IO_FP X HX Σ1 m a hD _ ART HS) as HSP.
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).
assert (INF : In (x_F X, 8%nat) (rt_frames RT Σ1)) by (rewrite EF; left; reflexivity).
assert (INL : forall e, In e (h_own a hD) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
unfold h_dec_rep in DEC0. cbn [hD set_bits_st h_st] in DEC0.
destruct DEC0 as (DR & SP0 & DD & IS & NRd & NDB & AL8 & NBD & LLB).
pose proof (dec_bounds st DD) as (DSTK & DFR & DCR).

unfold h_spill in SP. unfold h_regs in Hc.
refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ _ c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply dh_w1; [exact S1R| exact SP| exact MI]. }
intros ms1 c1 <- Hc1. clear Hc.

edestruct (DEC st Σ1 F0 fs0 (Z64 0x96fe8) (Z64 (x_S1 X)) (x_gp X) (Z64 0x638c98) t0 t1 t2 (Z64 (x_usp X)) (Z64 (x_S1 X))
(Z64 (a_S a)) (Z64 (x_F X + HO_BITS)) (Z64 (x_F X + HO_OUT)) a3 a4 a5 a6 a7 (Z64 pno) (Z64 (x_sf X)) (Z64 (h_packet_count h))
(Z64 eosf) (Z64 (-8)) (Z64 0x7fffffff) (Z64 (h_channels h)) (Z64 (h_skip_samples h)) (Z64 (h_nframes h - Z.of_nat (S n)))
(Z64 (x_F X + HO_BITS)) t3 t4 t5 t6 Fx fc m (x_F X + 128) (x_F X + 9168) (a_S a) (x_F X + 8400) (a_Dc a)
(a_LBD a) b (x_lo X) (x_F X) (a_Dc a) (sb_buf_size b) 8%nat ows stb q q1 ret st1 b1 RUN) as (bs1 & EB1 & DECE).
{ reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
{ exact DR. } { exact DD. } { exact IS. } { exact NRd. } { exact NDB. } { exact AL8. }
{ intros x Hx. apply INL. exact (own_in_blk a hD ltac:(cbn [hD set_bits_st h_st]; discriminate) x Hx). }
{ exact BITS. }
{ destruct HP as (_ & _ & _ & _ & B & _). exact B. }
{ exact (INL _ (own_in_Dc a hD)). }
{ apply Z.le_refl. } { apply Z.le_refl. }
{ exact NBD. }
{ exact OUTB. } { exact LOWS. } { exact STB. }
{ exact INF. }
{ pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m PF) as (_ & _ & ACB & _). unfold in_frame_obj. change (fs_size 8) with 16384. unfold BITS_SIZEOF in *.
split; [lia|]. split; [lia|]. split; [exact ACB| clear - F64; Z.div_mod_to_equations; lia]. }
{ pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m PF) as (ACO & _). unfold in_frame_obj. change (fs_size 8) with 16384.
split; [lia|]. split; [lia|]. split; [exact ACO| clear - F64; Z.div_mod_to_equations; lia]. }
{ pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m PF) as (_ & _ & _ & _ & _ & _ & _ & ACS & _). unfold in_frame_obj. change (fs_size 8) with 16384.
split; [lia|]. split; [lia|]. split; [exact ACS| clear - F64; Z.div_mod_to_equations; lia]. }
{ unfold hidp, BITS_SIZEOF. lia. } { unfold hidp, BITS_SIZEOF. lia. } { unfold hidp. lia. }
{ exact FD2. } { exact ERR. } { exact SSP. }
{ rewrite EF. cbn [length]. unfold FRAMES_MAX. lia. }
{ pose proof (hi_cr _ _ _ HX) as CR0. unfold FUZZ_COST in CR0. pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ.
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PCR & _ & _ & _ & BR & _ & P1 & P2 & _ & _ & _ & _ & P7 & _).
unfold h_cost, H_HDR_CREDIT, H_DEC_CREDIT, h_consumed, h_pend in *. cbn [hD set_bits_st h_packet_count h_oy h_bytes_remaining] in *. lia. }
{ rewrite EPO0. apply pois_above_nil. }
{ exact ART. } { exact MI. } { exact FRM. }
{ rewrite unsigned_lit by lia. exact ST. }
{ rewrite ESP. exact LW. }
{ rewrite unsigned_lit by lia. unfold RT_STACK, H_STACK in *. lia. }
{ rewrite unsigned_lit by lia. unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by lia. exact S32. }
assert (EBS1 : bs1 = bs) by (rewrite EB in EB1; exact (eq_sym (app_inv_head _ _ _ EB1))). subst bs1.
refine (DECE T c1 Hc1 _). clear DECE Hc1.
intros c2 (Σ2 & Hc2 & RR & EDD & EDM & NR' & EOW & ECH & EBS & EL2 & EF2 & ES2 & EC2 & EP2).
Time cps_unpack_lib Hc2 as (m2 & ows' & stb' & RS & RA & PR & DR' & EXC & BITS' & BOK' & OUT' & LOW' & STB' & ACA & ACO & ACS & ERR' & OUTR').
pose proof (ISAVE st st1 b q ret b1 q1 RUN IS) as IS'.
destruct (hrep_dec RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_drv AF_DRV X HX Σ1 Σ2 m m2 a hD _ ogc opc _ st st1 b1 ows' stb' HS HR
ltac:(reflexivity) ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) ltac:(destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->); reflexivity)
eq_refl RA PR DR' BITS' BOK' OUT' LOW' STB' ERR' OUTR' EDD NR' IS' EOW EBS EL2 EF2 ES2 (proj1 EC2) EP2) as (HS2 & HR2).
clear HR ART MI ST PF ERR OUTR SSP SP LSH ENH OUTB LOWS FSZ BITS SY OGC OPC OSR STB RATE LOOK LKR HP DR.
set (hD2 := set_bits_st hD b1 (Some st1) (h_eos hD)) in *.
pose proof HR2 as HR'. destruct HR' as (ART2 & MI2 & ST2 & PF2 & ERR2 & OUTR2 & SSP2 & SP2 & LSH2 & (je2 & ENH2) & (ows2 & OUTB2 & LOWS2) & FSZ2 & BITS2 & SY2
& OGC2 & OPC2 & OSR2 & (stb2 & STB2) & RATE2 & (wl2 & LOOK2 & LKR2) & DEC2 & HP2).
refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c2 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply dh_w2a; [reflexivity| exact RR| exact MI2]. }
intros ms3 c3 [(RM & ->) | (R0 & ->)] Hc3. clear Hc.

assert (KT_HR : forall (m' : mem), hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' a hD2 (h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88 j224 j232 a h) ogc opc ->
hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' a (set_bits_st h b1 (Some st1) eosf)
(h_spill X (Z64 (h_bytes_remaining (set_bits_st h b1 (Some st1) eosf))) v48 v56 v88 j224 j232 a (set_bits_st h b1 (Some st1) eosf)) ogc opc).
{ intros m' H'. exact (hrep_set_eos Σ2 m' a hD2 _ ogc opc eosf EOR H'). }
assert (KT_HS : hsig_k RT X Σ2 a (set_bits_st h b1 (Some st1) eosf) (10 * H_DEC_CREDIT)).
{ apply (hsig_k_weaken RT X Σ2 a _ (H_DEC_CREDIT * (10 - Z.of_nat (S n)) + dec_credit st)); [unfold H_DEC_CREDIT in *; lia| exact HS2]. }
assert (KT_PR : pc_room X (set_bits_st h b1 (Some st1) eosf)).
{ destruct PRM as (PR1 & PR2). split; [exact PR1| cbn [set_bits_st h_st]; discriminate]. }
-
apply Hk. left. split; [left; destruct RM as [-> | ->]; reflexivity|].
exists Σ2, a. do 2 eexists. exists m2. do 20 eexists. exists v48, v56, v88, j224, j232, ogc, opc.
split; [unfold h_regs; exact Hc3|].
split; [exact RS|]. split; [exact KT_HS|]. split; [exact HIT|]. split; [exact SI1|]. split; [exact EOR|]. split; [cbn [set_bits_st h_packet_count]; lia|]. split; [exact SKW|].
split; [exact (KT_HR m2 HR2)|]. split; [exact OGJ|]. split; [exact OPJ| exact KT_PR].
-
subst ret.
assert (KT_HR : forall (m' : mem), hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' a hD2 (h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88 j224 j232 a h) ogc opc ->
hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' a (set_bits_st h b1 (Some st1) eosf)
(h_spill X (Z64 (h_bytes_remaining (set_bits_st h b1 (Some st1) eosf))) v48 v56 v88 j224 j232 a (set_bits_st h b1 (Some st1) eosf)) ogc opc).
{ intros m' H'. exact (hrep_set_eos Σ2 m' a hD2 _ ogc opc eosf EOR H'). }
assert (KT_HS : hsig_k RT X Σ2 a (set_bits_st h b1 (Some st1) eosf) (10 * H_DEC_CREDIT)).
{ apply (hsig_k_weaken RT X Σ2 a _ (H_DEC_CREDIT * (10 - Z.of_nat (S n)) + dec_credit st)); [unfold H_DEC_CREDIT in *; lia| exact HS2]. }
assert (KT_PR : pc_room X (set_bits_st h b1 (Some st1) eosf)).
{ destruct PRM as (PR1 & PR2). split; [exact PR1| cbn [set_bits_st h_st]; discriminate]. }
assert (BDc : a_Dc a + sb_buf_size b1 <= x_lo X).
{ destruct (hsep_of_k RT AF OUT_rep IO_FP X HX Σ2 m2 a hD2 _ ART2 HS2) as (HSP1 & _).
destruct (HSP1 _ _ (own_in_Dc a hD2)) as (_ & DL & _). cbn [hD2 hD set_bits_st h_bits] in DL. exact DL. }
refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c3 (PMfd_mat_stable F0 fs0) Hc3 _ _).
{ eapply (speex_bits_remaining_walk (x_F X + 8400) (a_Dc a) (x_S1 X) (x_lo X) b1).
- exact BITS2.
- exact BOK'.
- unfold aobj. unfold BITS_SIZEOF in *. split; [lia|]. split; [unfold APP_TOP; unfold RT_STACK, H_STACK, USTACK_TOP in *; lia| exact ACA].
- exact ST2.
- unfold RT_STACK, H_STACK in *. lia.
- exact SHLO.
- unfold USTACK_TOP in *. lia.
- unfold BITS_SIZEOF. lia.
- exact BDc.
- exact (af_client_consts RT AF Σ2 m2 ART2).
- exact MI2. }
intros ms4 c4 (v0 & v1 & v2 & v3 & v4 & v5 & m3 & -> & MU3 & WM3 & MI3 & ST3 & EV0 & BITS3) Hc4. clear Hc3. subst v0.
assert (OUT3 : rw_cells bsegs m3 (x_F X + 128) (f32 ows2)).
{ apply (rw_cells_transport bsegs _ m2 m3 _ _ OUTB2 MU3 WM3). rewrite cells_size_f32, LOWS2. cbn [disjoint_from].
split; [left; unfold HO_OUT, HO_STEREO, RT_STACK, H_STACK in *; lia| exact I]. }
assert (STB3 : rw_cells bsegs m3 (x_F X + 9168) [CB 24 stb2]).
{ apply (rw_cells_transport bsegs _ m2 m3 _ _ STB2 MU3 WM3). cbn [disjoint_from cells_size csize Nat.add].
split; [left; unfold HO_OUT, HO_STEREO, RT_STACK, H_STACK in *; lia| exact I]. }
pose proof (hrep_out_step RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ2 m2 m3 a hD2 _ ogc opc ows2 stb2 _ HS2 HR2
ltac:(reflexivity) ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) ltac:(destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->); reflexivity)
ltac:(apply (munch_weaken [(x_S1 X + -16, x_S1 X)]); [unfold sub_fp; cbn [outside]; intros x Hx; lia| exact MU3])
WM3 MI3 ST3 OUT3 LOWS2 STB3) as HR3.
clear HR2 MU3 WM3 OUT3 STB3.
assert (REMR : -2^63 <= speex_bits_remaining b1 < 2^63).
{ pose proof BITS3 as (_ & _ & SIDE3). destruct (bits_ints _ _ b1 BOK' SIDE3) as (I1 & I2 & I3 & _ & _ & _ & C1 & C2 & IP & _).
unfold speex_bits_remaining. destruct (negb (sb_overflow b1 =? 0)); [lia|]. unfold bits_pos, X05l.int31 in *. lia. }
pose proof HR3 as HR'. destruct HR' as (ART3 & _ & _ & PF3 & ERR3 & OUTR3 & SSP3 & SP3 & LSH3 & (je3 & ENH3) & (ows3 & OUTB3 & LOWS3) & FSZ3 & BITS3' & SY3
& OGC3 & OPC3 & OSR3 & (stb3 & STB3) & RATE3 & (wl3 & LOOK3 & LKR3) & DEC3 & HP3).
unfold h_spill in SP3. unfold HO_FSZ, HO_STEREO, HO_LOOK, HO_RATE, HO_ENH, HO_OY, HO_OS in SP3, FSZ3.
pose proof HP3 as (_ & _ & _ & _ & _ & _ & _ & FSR & _ & _ & CHR & _).
cbn [hD2 hD set_bits_st h_frame_size h_channels] in FSR, CHR.
assert (K_DT : forall (m' : mem) (Fx' : bvmap 5 word) (fc' : bv 32) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (c' : config),
ASTA RT Σ2 (PMfd F0 fs0) (eq (MS (mkR ra' (Z64 (x_S1 X)) (x_gp X) (Z64 0x638c98) t0' t1' t2' (Z64 (x_usp X)) (Z64 (x_S1 X))
a0' a1' a2' a3' a4' a5' a6' a7' (Z64 pno) (Z64 (x_sf X)) (Z64 (h_packet_count h)) (Z64 eosf) (Z64 (-8))
(Z64 0x7fffffff) (Z64 (h_channels h)) (Z64 (h_skip_samples h)) (Z64 (h_nframes h - Z.of_nat (S n)))
(Z64 (h_channels h)) t3' t4' t5' t6') Fx' (Z64 A_DT) fc' None m' (seg_rom bsegs))) c' ->
frm0 fc' -> 0 <= speex_bits_remaining b1 ->
hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' a hD2 (h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88 j224 j232 a h) ogc opc ->
realizes bsegs c' T).
{ intros m' Fx' fc' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' c' Hc' FRM' RP0 HR'.
pose proof HR' as (_ & MI' & _ & _ & _ & _ & _ & SP' & _ & _ & _ & FSZ' & _ & _ & _ & _ & _ & _ & _ & (wl' & LOOK' & LKR') & _ & HP').
unfold h_spill in SP'. unfold HO_FSZ, HO_LOOK in SP', FSZ', LOOK'.
pose proof HP' as (_ & _ & _ & _ & _ & _ & _ & FSR' & _ & NFR' & _ & _ & _ & (_ & SKR') & _).
cbn [hD2 hD set_bits_st h_frame_size h_nframes h_skip_samples h_st] in FSR', NFR', SKR', LKR', FSZ'.
assert (LR' : 0 <= wl' <= H_LOOK_MAX) by (apply LKR'; discriminate).
unfold H_LOOK_MAX in LR'.
refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c' (PMfd_mat_stable F0 fs0) Hc' _ _).
{ eapply (dh_w2c (x_S1 X) (x_F X) (h_nframes h - Z.of_nat (S n)) (h_nframes h) (h_frame_size h) wl' (h_skip_samples h) v88);
[exact S1R| lia| lia| exact FSR'| lia| lia| exact FLG| exact FSZ'| exact LOOK'| exact SP'| exact MI']. }
intros ms6 c6 (a0'' & a1'' & a2'' & a3'' & [(N1 & ->) | (N2 & ->)]) Hc6.
- apply Hk. left. split; [right; right; lia|].
exists Σ2, a, Fx', fc', m'. do 20 eexists. exists v48, v56, v88, j224, j232, ogc, opc.
split; [unfold h_regs; exact Hc6|].
split; [exact FRM'|]. split; [exact KT_HS|]. split; [exact HIT|]. split; [exact SI1|]. split; [exact EOR|].
split; [cbn [set_bits_st h_packet_count]; lia|]. split; [exact SKW|].
split; [exact (KT_HR m' HR')|]. split; [exact OGJ|]. split; [exact OPJ| exact KT_PR].
- apply Hk. right. split; [reflexivity|]. split; [exact RP0|]. split; [lia|].
replace (h_nframes h - Z.of_nat (S n) + 1) with (h_nframes h - Z.of_nat n) in Hc6 by lia.
exists Σ2, a, Fx', fc', m'. do 17 eexists. exists v48, v56, v88, j224, j232, ogc, opc.
split; [unfold h_regs; exact Hc6|].
split; [exact FRM'|]. split; [lia|]. split; [lia|]. split; [exact EOR|]. split; [exact STN|]. split; [exact E0|]. split; [exact PNR|].
split; [apply (hsig_k_weaken RT X Σ2 a _ (H_DEC_CREDIT * (10 - Z.of_nat (S n)) + dec_credit st)); [unfold H_DEC_CREDIT in *; lia| exact HS2]|].
split; [exact HIT|]. split; [exact SI1|]. split; [exact SKW|]. split; [exact FLG|]. split; [exact HR'|]. split; [exact OGJ|]. split; [exact OPJ| exact PRM]. }
refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c4 (PMfd_mat_stable F0 fs0) Hc4 _ _).
{ eapply (dh_w2b (x_S1 X) (x_F X) (speex_bits_remaining b1) (h_channels h) (h_frame_size h)); [reflexivity| exact S1R| exact REMR| exact CHR| exact FSR| | | exact MI3].
- cbn [hD2 hD set_bits_st h_frame_size] in FSZ3. exact FSZ3.
- exact SP3. }
intros ms5 c5 [(RN & ->) | [(RP & CN & ->) | (RP & C2 & ->)]] Hc5. clear Hc4.
+
apply Hk. left. split; [right; left; exact RN|].
exists Σ2, a. do 2 eexists. exists m3. do 20 eexists. exists v48, v56, v88, j224, j232, ogc, opc.
split; [unfold h_regs; exact Hc5|].
split; [exact RS|]. split; [exact KT_HS|]. split; [exact HIT|]. split; [exact SI1|]. split; [exact EOR|].
split; [cbn [set_bits_st h_packet_count]; lia|]. split; [exact SKW|].
split; [exact (KT_HR m3 HR3)|]. split; [exact OGJ|]. split; [exact OPJ| exact KT_PR].
+
eapply K_DT; [exact Hc5| exact RS| exact RP| exact HR3].
+
subst. destruct (rw_cells_CB_f32 bsegs m3 (x_F X + HO_STEREO) 6 stb3 STB3) as ([|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 ws6]]]]]]] & L6 & STB6);
cbn [length] in L6; try lia.
pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m3 PF3) as (ACO3 & _ & _ & _ & _ & _ & _ & ACS3 & _).
pose proof (hi_F _ _ _ HX) as (_ & _ & _ & FSH & _). change (fs_size 8) with 16384 in FSH.
unfold HO_OUT, HO_STEREO in *.
assert (FSRh : 0 <= h_frame_size h <= 640) by exact FSR.
refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c5 (PMfd_mat_stable F0 fs0) Hc5 _ _).
{ eapply (speex_decode_stereo_walk (x_F X + 128) (x_F X + 9168) (x_S1 X) (x_lo X) 2000%nat).
- unfold aobj. split; [lia|]. split; [unfold APP_TOP, RT_STACK, H_STACK, USTACK_TOP in *; lia| exact ACO3].
- unfold aobj. split; [lia|]. split; [unfold APP_TOP, RT_STACK, H_STACK, USTACK_TOP in *; lia| exact ACS3].
- clear - F64. Z.div_mod_to_equations. lia.
- clear - F64. Z.div_mod_to_equations. lia.
- try change (Z.of_nat 2000) with 2000. lia.
- try change (Z.of_nat 2000) with 2000. unfold RT_STACK, H_STACK in *. lia.
- exact SHLO.
- unfold USTACK_TOP in *. lia.
- try change (Z.of_nat 2000) with 2000. lia.
- try change (Z.of_nat 2000) with 2000. lia.
- try change (Z.of_nat 2000) with 2000. unfold RT_STACK, H_STACK in *. lia.
- try change (Z.of_nat 2000) with 2000. unfold RT_STACK, H_STACK in *. lia.
- try change (Z.of_nat 2000) with 2000. lia.
- exact OUTB3.
- exact LOWS3.
- exact STB6.
- try change (Z.of_nat 2000) with 2000. lia.
- try change (Z.of_nat 2000) with 2000. lia.
- unfold IMG_TOP_B, SEGTOP_A in *. lia.
- unfold IMG_TOP_B, SEGTOP_A in *. lia.
- exact (af_client_consts RT AF Σ2 m3 ART3).
- exact ST3.
- exact MI3.
- exact RS. }
intros ms6 c6 (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & F6 & fc6 & m4 & ws4 & sw4 & -> & MU4 & WM4 & MI4 & ST4 & FRM4
& OUT4 & LW4 & STW4 & LS4) Hc6. clear Hc5.
pose proof (rw_cells_f32_CB bsegs m4 (x_F X + 9168) sw4 STW4) as STB4. rewrite LS4 in STB4.
pose proof (hrep_out_step RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ2 m3 m4 a hD2 _ ogc opc ws4 (cells_bytes (f32 sw4)) _ HS2 HR3
ltac:(reflexivity) ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) ltac:(destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->); reflexivity)
ltac:(eapply munch_weaken; [| exact MU4]; unfold sub_fp; cbn [outside]; intros x Hx; change (Z.of_nat 2000) with 2000 in Hx |- *; lia)
WM4 MI4 ST4 OUT4 LW4 STB4) as HR4.
replace (ret_pc (Z64 0x9701c)) with (Z64 0x9701c) in Hc6 by (symmetry; apply ret_pc_even; [lia | reflexivity]).
eapply K_DT; [exact Hc6| exact FRM4| exact RP| exact HR4].
Qed.
Lemma cpsE_or : forall (P1 P2 Q : config -> Prop) e, cpsE bsegs P1 e Q -> cpsE bsegs P2 e Q -> cpsE bsegs (fun c => P1 c \/ P2 c) e Q.
Proof. intros P1 P2 Q e H1 H2 T c [Hc|Hc] Hk; [exact (H1 T c Hc Hk)| exact (H2 T c Hc Hk)]. Qed.

Theorem h_dloop_ok : hinv_ok OUT_rep IO_FP X -> forall (n : nat) (h : hstate unit) (st : dec_state unit) (b : bits_st unit) (eosf pno nbr brem0 : Z)
(q q' : pst) (st' : dec_state unit) (b' : bits_st unit) bs,
prun (hP_decode_loop n st b) q = Some ((st', b'), q') -> p_err q' = p_err q ++ bs ->
cpsE bsegs (at_DHk RT OUT_rep ERR_rep IO_FP X F0 fs0 h st b n eosf pno nbr brem0) (Spec.X1nu.evw 2 bs)
(at_KT RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_bits_st h b' (Some st') eosf) pno nbr brem0).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE FD2.
intros HX n. induction n as [|n IH]; intros h st b eosf pno nbr brem0 q q' st' b' bs RUN EB.
- intros T c Hc _. exfalso.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r8 & t3 & t4 & t5 & t6 & v48 & v56 & v88 & j224 & j232 & ogc & opc
& Hc & FRM & NR & _). lia.
- unfold hP_decode_loop in RUN.
destruct (dloop_step n st b q (st', b') q' RUN) as (ret & st1 & b1 & q1 & ED & CASES).
destruct (X0wy.dec_appends_all st b q _ q1 ED) as (bs1 & EB1).
destruct CASES as [(RC & ER & EQ) | [(RC & RN & ER & EQ) | (RC & RP & HR)]].
+ injection ER as -> ->. subst q'. rewrite EB in EB1. apply app_inv_head in EB1. subst bs1.
eapply cpsE_conseq; [apply (h_dstep_ok HX n h st b eosf pno nbr brem0 q q1 ret st1 b1 bs ED EB)| intros c Hc; exact Hc|].
intros c [(_ & H) | (RC' & _)]; [exact H| rewrite RC in RC'; discriminate RC'].
+ injection ER as -> ->. subst q'. rewrite EB in EB1. apply app_inv_head in EB1. subst bs1.
eapply cpsE_conseq; [apply (h_dstep_ok HX n h st b eosf pno nbr brem0 q q1 ret st1 b1 bs ED EB)| intros c Hc; exact Hc|].
intros c [(_ & H) | (_ & RP' & _)]; [exact H| lia].
+ destruct (dloop_appends n st1 b1 q1 _ q' HR) as (bs2 & EB2).
assert (EBS : bs = bs1 ++ bs2) by (rewrite EB2, EB1, <- app_assoc in EB; exact (eq_sym (app_inv_head _ _ _ EB))). subst bs.
rewrite Spec.X1nu.evw_app.
eapply cpsE_seq; [apply (h_dstep_ok HX n h st b eosf pno nbr brem0 q q1 ret st1 b1 bs1 ED EB1)|].
apply cpsE_or.
*
destruct n as [|n'].
-- cbn [decode_loop] in HR. rewrite prun_ret in HR. injection HR as <- <- <-.
assert (LB : length bs2 = 0%nat) by (apply (f_equal (@length Z)) in EB2; rewrite length_app in EB2; lia).
destruct bs2; [| discriminate LB]. cbn [Spec.X1nu.evw map]. apply cpsE_nil.
intros T c (CX & Hc) Hk. apply Hk. exact Hc.
-- intros T c (CX & Hc) Hk. exfalso. destruct CX as [CX|[CX|CX]]; [rewrite RC in CX; discriminate CX| lia| discriminate CX].
* intros T c (_ & _ & N1 & Hc) Hk. exact (IH h st1 b1 eosf pno nbr brem0 q1 q' st' b' bs2 HR EB2 T c Hc Hk).
Qed.

Definition at_RF (h : hstate unit) (op : packet) (pno nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (t0 t1 t2 a3 a4 a5 a6 a7 r10 t3 t4 t5 t6 : word)
(v48 v56 v88 j224 j232 gw : word) (ogc kc : list cell),
ASTA RT Σ1 (PMfd F0 fs0) (eq (MS (h_regs X h (Z64 0x96fa8) t0 t1 t2 (Z64 (x_F X + 8400)) (Z64 (a_Bd a + pk_off op)) (Z64 (pk_bytes op)) a3 a4 a5 a6 a7
(Z64 (pno + 1)) (Z64 (Z.b2z (0 <? pk_e_o_s op))) (Z64 0x7fffffff) (Z64 pno) (Z64 (pk_bytes op)) r10 t3 t4 t5 t6)
Fx (Z64 A_speex_bits_read_from_h) fc None m (seg_rom bsegs))) c
/\ X1cn.frm0 fc /\ hsig RT X Σ1 a h /\ h_iter X h nbr brem0 /\ h_stream_init h = 1 /\ h_eos h = 0 /\ 0 <= pno <= h_packet_count h /\ h_st h <> None
/\ h_skip_word v48 h
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h (h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88 j224 j232 a h) ogc (op_cells (a_Bd a) (Some op) gw kc)
/\ og_junk ogc /\ cells_size kc = 48%nat
/\ 0 <= pk_off op /\ 0 <= pk_bytes op /\ pk_off op + pk_bytes op <= os_body_fill (h_os h) /\ 0 <= pk_e_o_s op < 2^63
/\ pc_room X h.

Lemma b2z_ltb0 : forall e, 0 <= e -> Z.b2z (0 <? e) = (if e =? 0 then 0 else 1).
Proof. intros e He. destruct (Z.eqb_spec e 0) as [->|NE]; [reflexivity|]. replace (0 <? e) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

Lemma pk_window : forall (m : mem) (Bd : Z) (body : list byte) (os : stream_st unit) (op : packet),
u8arr bsegs m Bd body -> body_pre (os_body os) body -> zlength (os_body os) = os_body_fill os ->
0 <= pk_off op -> 0 <= pk_bytes op -> pk_off op + pk_bytes op <= os_body_fill os ->
u8ro bsegs m (Bd + pk_off op) (firstn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) body))
/\ map bv_unsigned (firstn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) body)) = packet_data os op
/\ Z.of_nat (length (firstn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) body))) = pk_bytes op.
Proof.
intros m Bd body os op [UB _] [BP BL] ZL P0 P1 P2. unfold zlength in ZL.
assert (ON : (Z.to_nat (pk_off op) + Z.to_nat (pk_bytes op) <= length (os_body os))%nat) by lia.
split; [| split].
- unfold u8ro. rewrite <- (firstn_skipn (Z.to_nat (pk_off op)) body) in UB. apply bytes_at_app in UB as [_ UB].
rewrite <- (firstn_skipn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) body)) in UB. apply bytes_at_app in UB as [UB _].
rewrite length_firstn in UB. replace (Bd + Z.of_nat (Nat.min (Z.to_nat (pk_off op)) (length body))) with (Bd + pk_off op) in UB by lia. exact UB.
- unfold packet_data, zslice, ztake, zdrop. rewrite <- BP. unfold ubytes.
rewrite skipn_firstn_comm, firstn_firstn. replace (Nat.min (Z.to_nat (pk_bytes op)) (length (os_body os) - Z.to_nat (pk_off op))) with (Z.to_nat (pk_bytes op)) by lia.
rewrite skipn_map, firstn_map. reflexivity.
- rewrite length_firstn, length_skipn. lia.
Qed.

Lemma hrep_op_junk : forall (Σ1 : rts RT) (m : mem) a (h : hstate unit) spill ogc Bd op gw kc,
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc (op_cells Bd (Some op) gw kc) ->
exists opc, op_junk opc /\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc.
Proof.
intros Σ1 m a h spill ogc Bd op gw kc HR.
destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22).
cbn [op_cells] in A16.
exists [CB 8 (le8 (wz (Bd + pk_off op))); CB 8 (le8 (wz (pk_bytes op))); CB 8 (le8 (wz (pk_b_o_s op))); CB 8 (le8 (wz (pk_e_o_s op)));
CB 8 (le8 gw); CB 8 (le8 (wz (pk_packetno op)))].
split; [do 6 eexists; reflexivity|].
assert (A16' : rw_cells bsegs m (x_F X + HO_OP) [CB 8 (le8 (wz (Bd + pk_off op))); CB 8 (le8 (wz (pk_bytes op))); CB 8 (le8 (wz (pk_b_o_s op)));
CB 8 (le8 (wz (pk_e_o_s op))); CB 8 (le8 gw); CB 8 (le8 (wz (pk_packetno op)))]).
{ eapply rw_cells_recast; [exact A16| cbn [cells_wf cell_wf]; repeat split; apply length_le8| reflexivity]. }
exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 (conj A10 (conj A11 (conj A12 (conj A13 (conj A14 (conj A15
(conj A16' (conj A17 (conj A18 (conj A19 (conj A20 (conj A21 A22))))))))))))))))))))).
Qed.

Theorem h_data_ok : hinv_ok OUT_rep IO_FP X -> forall (h : hstate unit) (op : packet) (pno nbr brem0 : Z) (q q1 q' : pst) (b : bits_st unit)
(d st' : dec_state unit) (b' : bits_st unit) bs,
h_st h = Some d ->
prun (speex_bits_read_from (St := pst) p_realloc p_notify p_warning (h_bits h) (packet_data (h_os h) op) (pk_bytes op)) q = Some (b, q1) ->
prun (hP_decode_loop (Z.to_nat (h_nframes h)) d b) q1 = Some ((st', b'), q') ->
p_err q' = p_err q ++ bs ->
cpsE bsegs (at_RF h op pno nbr brem0) (Spec.X1nu.evw 2 bs)
(at_KT RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_bits_st h b' (Some st') (if pk_e_o_s op =? 0 then 0 else 1)) (pno + 1) nbr brem0).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE FD2 RF.
intros HX h op pno nbr brem0 q q1 q' b d st' b' bs ESt RUN1 RUN2 EB T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & r10 & t3 & t4 & t5 & t6 & v48 & v56 & v88 & j224 & j232 & gw & ogc & kc
& Hc & FRM & HS & HIT & SI1 & E0 & PNR & STN & SKW & HR & OGJ & KCS & PK0 & PK1 & PK2 & EOR & PRM).
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a h _ ogc _ HR) as OPOS.
pose proof HR as HR'. destruct HR' as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC
& OSR & (stb & STB) & RATE & (wl & LOOK & LKR) & DEC0 & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART HS) as HSP.
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).
assert (INF : In (x_F X, 8%nat) (rt_frames RT Σ1)) by (rewrite EF; left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }

unfold h_os_rep in OSR. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0'|_]; [rewrite SI1 in E0'; discriminate E0'|].
destruct OSR as (OS & LH & (UB & LB & BP & UL & WP & LL & UG & LG) & FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS & NBL & NBG & NLG).
destruct (pk_window m (a_Bd a) (a_body a) (h_os h) op UB BP (proj1 BINV) PK0 PK1 PK2) as (U8 & EPD & LPB).
set (pb := firstn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) (a_body a))) in *.
rewrite <- EPD in RUN1.
assert (SIN : h_stream_init h <> 0) by (rewrite SI1; discriminate).
pose proof (own_in_os a h SIN) as (IBD & _ & _).
pose proof (own_ne_os a h (proj2 (proj2 HSP)) SIN (a_Bd a) (or_introl eq_refl)) as (NBD & _).
assert (LVR : Z.of_nat (length (rt_live RT Σ1)) < LIVE_MAX).
{ rewrite (h_live_len RT X Σ1 a h HS).
pose proof (h_own_len RT OUT_rep ERR_rep IO_FP X Σ1 m a h _ _ _ HR) as L24.
pose proof (hi_live _ _ _ HX) as (_ & LLV). unfold H_LIVE in LLV. lia. }
assert (BFS : pk_off op + pk_bytes op <= os_body_storage (h_os h)).
{ destruct BP as (_ & BPL). pose proof (proj1 BINV) as ZL. unfold zlength in ZL. unfold bptr in *. lia. }
assert (LEN : pk_bytes op <= 4096).
{ pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ.
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BR & _ & P1 & P2 & _ & BF & _).
unfold h_consumed, h_pend in *. lia. }
pose proof HP as (_ & _ & _ & _ & BOK & OWN & BSZ & _ & _ & NFR & _).
assert (OV : p_overflows (pk_bytes op) = false) by (unfold p_overflows; apply Z.leb_gt; lia).
destruct (read_from_prun (h_bits h) (map bv_unsigned pb) (pk_bytes op) q b q1 RUN1 OWN OV) as [PFIT PBIG].
unfold h_regs in Hc.
edestruct (RF Σ1 F0 fs0 (Z64 0x96fa8) (Z64 (x_S1 X)) (x_gp X) (Z64 0x638c98) t0 t1 t2 (Z64 (x_usp X)) (Z64 (x_S1 X))
(Z64 (x_F X + 8400)) (Z64 (a_Bd a + pk_off op)) (Z64 (pk_bytes op)) a3 a4 a5 a6 a7 (Z64 (pno + 1)) (Z64 (x_sf X))
(Z64 (h_packet_count h)) (Z64 (Z.b2z (0 <? pk_e_o_s op))) (Z64 (-8)) (Z64 0x7fffffff) (Z64 pno) (Z64 (pk_bytes op)) r10 (Z64 (h_channels h))
t3 t4 t5 t6 Fx fc m (x_F X + 8400) (a_Dc a) (a_Bd a + pk_off op) (x_F X)
(a_Bd a) (os_body_storage (h_os h)) (x_lo X) 8%nat (h_bits h) pb (pk_bytes op) q q1 b RUN1) as (bs1 & EB1 & RFE).
{ reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
{ exact BITS. } { exact BOK. } { exact OWN. }
{ exact (h_bits_shadow_at OUT_rep IO_FP IO_img X HX m PF). }
{ exact INF. } { lia. } { change (fs_size 8) with 16384. lia. }
{ exact (INL _ (own_in_Dc a h)). }
{ exact U8. } { rewrite LPB. lia. } { unfold READ_FROM_LEN_MAX. lia. }
{ exact (INL _ IBD). } { lia. } { rewrite LPB. lia. }
{ exact (not_eq_sym NBD). }
{ exact FD2. } { exact ERR. } { exact SSP. } { exact LVR. }
{ exact (af_credit_nonneg RT AF Σ1 m ART). }
{ rewrite EPO0. apply pois_above_nil. }
{ exact ART. } { exact MI. }
{ rewrite unsigned_lit by lia. exact ST. }
{ rewrite ESP. exact LW. }
{ rewrite unsigned_lit by lia. unfold RT_STACK, H_STACK in *. lia. }
{ rewrite unsigned_lit by lia. unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by lia. apply Z.mod_divide; [lia|]. apply Z.mod_divide in S32; [|lia]. destruct S32 as (k32 & E32). exists (2 * k32). lia. }

pose proof RUN2 as RUN2'. unfold hP_decode_loop in RUN2'. destruct (dloop_appends _ d b q1 _ q' RUN2') as (bs2 & EB2). clear RUN2'.
assert (EBS : bs = bs1 ++ bs2) by (rewrite EB2, EB1, <- app_assoc in EB; exact (eq_sym (app_inv_head _ _ _ EB))). subst bs.
rewrite Spec.X1nu.evw_app.
eapply rz_conseq; [| apply t_eq_sym, t_emit_app].
refine (RFE (t_emit (Spec.X1nu.evw 2 bs2) T) c Hc _). clear RFE Hc.
intros c2 (Σ2 & D' & Hc2 & INL2 & CASE & EF2 & ES2 & EC2 & EP2).
Time cps_unpack_lib Hc2 as (v & m2 & RS & RA & PR & BITS' & BOK' & SHC' & ERR' & OUTR').

assert (OWN' : sb_owner b = 1 /\ 2000 <= sb_buf_size b <= 64512
/\ (pk_bytes op <= sb_buf_size (h_bits h) -> sb_buf_size b = sb_buf_size (h_bits h))
/\ (sb_buf_size (h_bits h) < pk_bytes op -> sb_buf_size b = pk_bytes op)).
{ destruct (Z_le_gt_dec (pk_bytes op) (sb_buf_size (h_bits h))) as [C|C].
- destruct (PFIT C) as (EBB & _). rewrite EBB. cbn [sb_owner sb_buf_size]. split; [exact OWN|]. split; [lia|]. split; [intros _; reflexivity| intros; lia].
- destruct (PBIG ltac:(lia)) as (EBB & _). rewrite EBB. cbn [sb_owner sb_buf_size]. split; [exact OWN|]. split; [lia|]. split; [intros; lia| intros _; reflexivity]. }
assert (CASE' : (pk_bytes op <= sb_buf_size (h_bits h) /\ D' = a_Dc a /\ rt_live RT Σ2 = rt_live RT Σ1 /\ sb_buf_size b = sb_buf_size (h_bits h))
\/ (sb_buf_size (h_bits h) < pk_bytes op /\ rt_live RT Σ2 = (D', pk_bytes op) :: live_remove (a_Dc a) (rt_live RT Σ1)
/\ sb_buf_size b = pk_bytes op)).
{ destruct OWN' as (_ & _ & S1' & S2'). destruct CASE as [(C1 & C2 & C3) | (C1 & C2)].
- left. split; [exact C1|]. split; [exact C2|]. split; [exact C3| exact (S1' C1)].
- right. split; [exact C1|]. split; [exact C2| exact (S2' C1)]. }
destruct (hrep_rf RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_drv AF_DRV X HX Σ1 Σ2 m m2 a h _ ogc _ 0 (pk_bytes op) D' b
(hsig_k_of RT X Σ1 a h HS) HR ltac:(reflexivity) ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) ltac:(reflexivity)
RA PR BITS' BOK' (proj1 OWN') (proj1 (proj2 OWN')) ERR' OUTR' CASE' EF2 ES2 EC2 EP2) as (P' & HS2 & HR2).
destruct (hrep_op_junk Σ2 m2 _ _ _ ogc (a_Bd a) op gw kc HR2) as (opc & OPJ & HR3). clear HR2.
rewrite ESt, E0 in HS2, HR3.
clear HR ART MI ST PF ERR OUTR SSP SP LSH ENH OUTB LOWS FSZ BITS SY OGC OPC STB RATE LOOK DEC0.
pose proof HR3 as HR'. destruct HR' as (ART2 & MI2 & ST2 & PF2 & ERR2 & OUTR2 & SSP2 & SP2 & _).

pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & SKR) & _).
refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ _ c2 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply (kd_w1 (x_S1 X) (h_nframes h) (h_skip_samples h) v48); [reflexivity| exact S1R| exact NFR| exact SKR| exact SKW| unfold h_spill in SP2; exact SP2| exact MI2]. }
intros ms3 c3 (m3 & v88' & a0' & a1' & MU3 & WM3 & MI3 & FLG3 & SP3 & ->) Hc3. clear Hc.
pose proof (hrep_spill RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ2 m2 m3 _ _ _
(h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88' j224 j232 (a_set_dc a D' P') h) ogc opc (hsig_of_k RT X Σ2 _ _ HS2) HR3
ltac:(reflexivity) ltac:(reflexivity) ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) ltac:(destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->); reflexivity)
MU3 WM3 MI3 SP3) as HR4.

rewrite (b2z_ltb0 _ (proj1 EOR)) in Hc3.
assert (HDk : at_DHk RT OUT_rep ERR_rep IO_FP X F0 fs0 h d b (Z.to_nat (h_nframes h)) (if pk_e_o_s op =? 0 then 0 else 1) (pno + 1) nbr brem0 c3).
{ exists Σ2, (a_set_dc a D' P'). do 2 eexists. exists m3. do 17 eexists. exists v48, v56, v88', j224, j232, ogc, opc.
split; [unfold h_regs; rewrite Z2Nat.id by lia; replace (h_nframes h - h_nframes h) with 0 by lia; exact Hc3|].
split; [exact (RS FRM)|]. split; [lia|]. split; [lia|]. split; [destruct (pk_e_o_s op =? 0); [left| right]; reflexivity|].
split; [exact STN|]. split; [exact E0|]. split; [lia|].
split; [apply (hsig_k_weaken RT X Σ2 _ _ 0); [unfold H_DEC_CREDIT; lia| exact HS2]|].
split; [exact HIT|]. split; [exact SI1|]. split; [exact SKW|]. split; [exact FLG3|]. split; [exact HR4|]. split; [exact OGJ|]. split; [exact OPJ| exact PRM]. }
exact (h_dloop_ok HX (Z.to_nat (h_nframes h)) h d b _ (pno + 1) nbr brem0 q1 q' st' b' bs2 RUN2 EB2 T c3 HDk Hk).
Qed.

Lemma prun_cleanup_none : forall (h : hstate unit) q, h_st h = None -> prun (hP_cleanup h) q = Some (tt, q).
Proof.
intros h q E. unfold hP_cleanup, cleanup. rewrite E.
unfold speex_bits_destroy, ogg_stream_clear, ogg_sync_clear, mfree_opt.
destruct (negb (sb_owner (h_bits h) =? 0)), (negb (h_stream_init h =? 0)), (os_body_data (h_os h)), (os_lacing_vals (h_os h)),
(os_granule_vals (h_os h)), (sy_data (h_oy h)); reflexivity.
Qed.

Definition pk_sser (h : hstate unit) (os : stream_st unit) (op : packet) : Z :=
if (5 <=? pk_bytes op) && list_eqb (ztake 5 (packet_data os op)) SPEEX_STR then os_serialno os else h_speex_serialno h.

Definition pkt_cases (fuel : nat) (h1 : hstate unit) (os : stream_st unit) (op : packet) (pno : Z) (q : pst) (o : outcome unit) (q' : pst) : Prop :=
((pk_sser h1 os op = -1 \/ os_serialno os <> pk_sser h1 os op) /\ o = Cont (set_serialno h1 (pk_sser h1 os op)) /\ q' = q)
\/ (pk_sser h1 os op <> -1 /\ os_serialno os = pk_sser h1 os op /\
( (h_packet_count h1 = 0 /\ exists ph q1, prun (hP_process_header (set_serialno h1 (pk_sser h1 os op)) (packet_data os op) (pk_bytes op)) q = Some (ph, q1)
/\ match ph with None => o = Returned /\ q' = q1
| Some h3 => prun (hP_packet_loop fuel (incr_packet_count h3) pno) q1 = Some (o, q') end)
\/ (h_packet_count h1 <> 0 /\ h_packet_count h1 <= 1 + h_extra_headers h1
/\ prun (hP_packet_loop fuel (incr_packet_count (set_serialno h1 (pk_sser h1 os op))) pno) q = Some (o, q'))
\/ (h_packet_count h1 <> 0 /\ 1 + h_extra_headers h1 < h_packet_count h1 /\
exists d b q1 st' b' q2, h_st h1 = Some d
/\ prun (speex_bits_read_from (St := pst) p_realloc p_notify p_warning (h_bits h1) (packet_data os op) (pk_bytes op)) q = Some (b, q1)
/\ prun (hP_decode_loop (Z.to_nat (h_nframes h1)) d b) q1 = Some ((st', b'), q2)
/\ prun (hP_packet_loop fuel (incr_packet_count (set_bits_st (set_serialno h1 (pk_sser h1 os op)) b' (Some st')
(if pk_e_o_s op =? 0 then 0 else 1))) (pno + 1)) q2 = Some (o, q')))).

Lemma pkt_step : forall fuel (h : hstate unit) pno q o q', h_eos h = 0 -> (h_packet_count h = 0 -> h_st h = None) ->
prun (hP_packet_loop (S fuel) h pno) q = Some (o, q') ->
exists r opo os, ogg_stream_packetout (h_os h) = Some ((r, opo), os) /\
( (r <> 1 /\ o = Cont (set_ogg h (h_oy h) os) /\ q' = q)
\/ (r = 1 /\ exists op, opo = Some op /\ pkt_cases fuel (set_ogg h (h_oy h) os) os op pno q o q') ).
Proof.
intros fuel h pno q o q' E0 PC0 H.
unfold hP_packet_loop in H. cbn [packet_loop] in H. rewrite E0 in H. cbn [Z.eqb negb] in H.
destruct (ogg_stream_packetout (h_os h)) as [[[r opo] os]|] eqn:EPO; [| rewrite prun_munr in H; discriminate H].
exists r, opo, os. split; [reflexivity|].
destruct (Z.eqb_spec r 1) as [R1|RN].
2:{ left. cbn [negb] in H. rewrite prun_ret in H. injection H as <- <-. split; [exact RN| split; reflexivity]. }
right. split; [exact R1|]. cbn [negb] in H.
destruct opo as [op|]; [| rewrite prun_munr in H; discriminate H].
exists op. split; [reflexivity|]. unfold pkt_cases.
fold (pk_sser (set_ogg h (h_oy h) os) os op) in H.
destruct ((pk_sser (set_ogg h (h_oy h) os) os op =? -1) || negb (os_serialno os =? pk_sser (set_ogg h (h_oy h) os) os op)) eqn:ES.
{ left. rewrite prun_ret in H. injection H as <- <-. split; [| split; reflexivity].
apply orb_true_iff in ES. destruct ES as [ES|ES]; [left; apply Z.eqb_eq; exact ES| right; apply negb_true_iff, Z.eqb_neq in ES; exact ES]. }
right. apply orb_false_iff in ES as (ES1 & ES2). apply Z.eqb_neq in ES1. apply negb_false_iff, Z.eqb_eq in ES2.
split; [exact ES1|]. split; [exact ES2|].
cbn [set_serialno set_ogg h_packet_count h_extra_headers h_bits h_st h_nframes h_speex_serialno h_eos] in H |- *.
rewrite prun_bind in H.
destruct (Z.eqb_spec (h_packet_count h) 0) as [P0|PN].
- left. split; [exact P0|]. cbn beta iota in H. rewrite prun_bind in H.
lazymatch type of H with context [prun (process_header ?x1 ?x2 ?x3 ?x4 ?x5 ?x6) q] =>
destruct (prun (process_header x1 x2 x3 x4 x5 x6) q) as [[ph q1]|] eqn:EPH; [| discriminate H] end.
exists ph, q1. split; [exact EPH|].
destruct ph as [h3|].
+ rewrite prun_ret in H. exact H.
+ pose proof (prun_cleanup_none (set_serialno (set_ogg h (h_oy h) os) (pk_sser (set_ogg h (h_oy h) os) os op)) q1 (PC0 P0)) as EC.
unfold hP_cleanup in EC. rewrite prun_bind, EC, prun_ret, prun_ret in H. injection H as <- <-. split; reflexivity.
- right. cbn beta iota in H. destruct (Z.leb_spec (h_packet_count h) (1 + h_extra_headers h)) as [LE|GT].
+ left. split; [exact PN|]. split; [exact LE|]. rewrite prun_ret in H. exact H.
+ right. split; [exact PN|]. split; [exact GT|]. rewrite prun_bind in H.
lazymatch type of H with context [prun (speex_bits_read_from ?x1 ?x2 ?x3 ?x4 ?x5 ?x6) q] =>
destruct (prun (speex_bits_read_from x1 x2 x3 x4 x5 x6) q) as [[b q1]|] eqn:ERF; [| discriminate H] end.
destruct (h_st h) as [d|] eqn:EST; [| rewrite prun_munr in H; discriminate H].
rewrite prun_bind in H.
lazymatch type of H with context [prun (decode_loop ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8) q1] =>
destruct (prun (decode_loop x1 x2 x3 x4 x5 x6 x7 x8) q1) as [[[st' b'] q2]|] eqn:EDL; [| discriminate H] end.
rewrite prun_ret in H. cbn beta iota in H.
exists d, b, q1, st', b', q2. split; [reflexivity|]. split; [first [exact ERF| reflexivity]|]. split; [first [exact EDL| reflexivity]|].
replace (os_serialno os =? pk_sser (set_ogg h (h_oy h) os) os op) with true in H by (symmetry; apply Z.eqb_eq; exact ES2).
rewrite andb_true_r, E0 in H.
replace (if pk_e_o_s op =? 0 then 0 else 1) with (if negb (pk_e_o_s op =? 0) then 1 else 0) by (destruct (pk_e_o_s op =? 0); reflexivity).
exact H.
Qed.

Lemma gather255_eos : forall rest size eos bytes n n' eos' bytes', gather255 size rest eos bytes n = Some (n', eos', bytes') ->
0 <= eos < 1024 -> 0 <= eos' < 1024.
Proof.
induction rest as [|v rest IH]; intros size eos bytes n n' eos' bytes' H E; cbn [gather255] in H.
- destruct (size =? 255); [discriminate H| injection H as _ <- _; exact E].
- destruct (size =? 255); [| injection H as _ <- _; exact E].
apply (IH _ _ _ _ _ _ _ H). destruct (negb (Z.land v 512 =? 0)); lia.
Qed.

Lemma land512_bound : forall v, 0 <= Z.land v 512 < 1024.
Proof.
intros v.
assert (E1 : Z.land v 512 = Z.land (Z.land v (Z.ones 10)) 512) by (rewrite <- Z.land_assoc; reflexivity).
rewrite E1, Z.land_ones by lia. rewrite Z.land_comm.
pose proof (Z.mod_pos_bound v (2^10) ltac:(lia)).
exact (OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1ch.land_lt_pow2 512 (v mod 2^10) 10 ltac:(lia) ltac:(lia)).
Qed.

Lemma packetout_r_eos : forall (os os' : stream_st unit) r opo, ogg_stream_packetout os = Some ((r, opo), os') ->
(r = 0 \/ r = -1 \/ r = 1) /\ match opo with Some p => 0 <= pk_e_o_s p < 1024 | None => True end.
Proof.
intros os os' r opo H. unfold ogg_stream_packetout, packetout in H.
destruct (ogg_stream_check os); [injection H as <- <- _; split; [left; reflexivity| exact I]|].
destruct (_ <=? _); [injection H as <- <- _; split; [left; reflexivity| exact I]|].
destruct (negb _); [injection H as <- <- _; split; [right; left; reflexivity| exact I]|].
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|] eqn:EG; [| discriminate H].
injection H as <- <- _. split; [right; right; reflexivity|]. cbn [pk_e_o_s].
exact (gather255_eos _ _ _ _ _ _ _ _ EG (land512_bound _)).
Qed.
End Pkt.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Section Pkt.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis IO_drv : forall y, in_ranges IO_FP y -> ~ drv_cell y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis DEC : forall d, dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode d.
Hypothesis ISAVE : forall (d d' : dec_state bptr) b q ret b' q',
prun (speex_decode (St := pst) p_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M d b 0) q = Some ((ret, d', b'), q') ->
isave_ok d -> isave_ok d'.
Hypothesis RF : speex_bits_read_from_cps RT OUT_rep ERR_rep IO_FP.
Hypothesis BCMP : bcmp_icontract RT.
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.
Hypothesis FD2 : fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Hypothesis HDR : h_hdr_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.

Lemma hpure_incr : forall (h : hstate unit), hinv_ok OUT_rep IO_FP X -> hpure X h -> pc_room X h ->
os_lacing_returned (h_os h) <= os_lacing_fill (h_os h) -> hpure X (incr_packet_count h).
Proof.
intros h HX HP (PR1 & PR2) LRF. pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ.
unfold hpure, h_consumed, h_pend in *.
cbn [incr_packet_count h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
do 14 (split; [assumption|]). split; [lia|]. do 4 (split; [assumption|]).
split; [destruct (h_st h); [lia| exfalso; exact (PR2 eq_refl)]|].
repeat split; lia.
Qed.

Lemma hrep_incr : forall (Σ1 : rts RT) (m : mem) a (h : hstate unit) spill ogc opc, hinv_ok OUT_rep IO_FP X ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc -> pc_room X h -> h_stream_init h <> 0 ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a (incr_packet_count h) spill ogc opc.
Proof.
intros Σ1 m a h spill ogc opc HX HR PRM SI.
destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & HP).
assert (LRF : os_lacing_returned (h_os h) <= os_lacing_fill (h_os h)).
{ unfold h_os_rep in A17. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0|_]; [exfalso; exact (SI E0)|].
destruct A17 as (_ & _ & _ & _ & (I1 & I2 & _) & _). lia. }
unfold hrep. cbn [incr_packet_count h_frame_size h_bits h_oy h_rate].
do 16 (split; [assumption|]).
split; [unfold h_os_rep in *; cbn [incr_packet_count h_stream_init h_os]; exact A17|].
do 3 (split; [assumption|]).
split; [unfold h_dec_rep in *; cbn [incr_packet_count h_st]; exact A21|].
exact (hpure_incr h HX HP PRM LRF).
Qed.

Lemma hsig_incr : forall (Σ1 : rts RT) a (h : hstate unit), hsig_k RT X Σ1 a h (10 * H_DEC_CREDIT) -> hsig RT X Σ1 a (incr_packet_count h).
Proof.
intros Σ1 a h (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold hsig, h_own, h_cost in *.
cbn [incr_packet_count h_st h_bits h_stream_init h_os h_oy h_packet_count]. repeat split; try assumption. lia.
Qed.

Theorem h_kt_ok : hinv_ok OUT_rep IO_FP X -> forall (h : hstate unit) (pno nbr brem0 : Z),
cps asegs (at_KT RT OUT_rep ERR_rep IO_FP X F0 fs0 h pno nbr brem0)
(fun c => (h_eos h = 0 /\ at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 (incr_packet_count h) pno nbr brem0 c)
\/ (h_eos h = 1 /\ at_PN RT OUT_rep ERR_rep IO_FP X F0 fs0 (incr_packet_count h) nbr brem0 c)).
Proof using AF ERR_loc OUT_loc IO_img AF_DRV.
intros HX h pno nbr brem0 T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r10 & t3 & t4 & t5 & t6 & j0 & j192 & j200 & ogc & opc
& Hc & FRM & HS & HIT & SI1 & EOR & PN0 & HR & OGJ & OPJ & PRM).
pose proof HR as HR'. destruct HR' as (ART & MI & ST & _ & _ & _ & _ & SP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PCR & _).
unfold h_spill, h_eos0 in SP. cbn [set_bits_st h_granule_frame_size h_extra_headers h_eos h_nframes h_channels] in SP.
unfold HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS in Hc.
refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply (kt_w (x_S1 X) (h_packet_count h) (h_eos h)); [exact S1R| lia| exact EOR| exact SP| exact MI]. }
intros ms1 c1 (m1 & MU & WM & MI1 & [(E0 & -> & ->) | (E1 & SP1 & ->)]) Hc1.
-
apply Hk. left. split; [exact E0|].
assert (ESPL : h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 (h_eos0 h)
= h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule (incr_packet_count h))) (Z64 (h_speex_serialno (incr_packet_count h))) j0 j192 j200
(incr_packet_count h)).
{ unfold h_spill, h_eos0. cbn [set_bits_st incr_packet_count h_granule_frame_size h_extra_headers h_eos h_nframes h_channels h_last_granule h_speex_serialno].
rewrite E0. reflexivity. }
rewrite ESPL in HR.
exists Σ1, a, Fx, fc, m, ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, (Z64 (x_F X + HO_OG)), (Z64 0), t3, t4, t5, t6, j0, j192, j200, ogc, opc.
split; [unfold h_regs; cbn [incr_packet_count h_packet_count h_extra_headers]; unfold HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; exact Hc1|].
split; [exact FRM|]. split; [exact (hsig_incr Σ1 a h HS)|]. split; [exact HIT|]. split; [exact SI1|].
split; [cbn [incr_packet_count h_eos]; exact E0|]. split; [exact PN0|].
split; [exact (hrep_incr Σ1 m a h _ ogc opc HX HR PRM ltac:(rewrite SI1; discriminate))|]. split; [exact OGJ| exact OPJ].
-
apply Hk. right. split; [exact E1|].
assert (ESPL : hsp j0 (Z64 (x_F X + 64)) (Z64 (x_F X + 48)) (Z64 (x_sf X + 16)) (Z64 (x_F X)) (Z64 (x_F X)) (Z64 (x_F X + HO_LOOK)) (Z64 (x_F X + HO_RATE))
(Z64 (x_F X + HO_ENH)) (Z64 (x_d X)) (Z64 nbr) (Z64 brem0) (Z64 SHB) (Z64 (h_granule_frame_size h)) (Z64 (h_extra_headers h))
(Z64 (x_F X + HO_OY)) (Z64 1) (Z64 (h_nframes h)) (Z64 (h_last_granule h)) (Z64 (x_F X + HO_OS)) (Z64 (x_F X + HO_STEREO))
(Z64 (x_F X + HO_FSZ)) (Z64 (h_speex_serialno h)) (Z64 (h_channels h)) j192 j200 (Z64 (x_F X))
= h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule (incr_packet_count h))) (Z64 (h_speex_serialno (incr_packet_count h))) j0 j192 j200
(incr_packet_count h)).
{ unfold h_spill. cbn [incr_packet_count h_granule_frame_size h_extra_headers h_eos h_nframes h_channels h_last_granule h_speex_serialno].
rewrite E1. reflexivity. }
pose proof (hrep_incr Σ1 m a h _ ogc opc HX HR PRM ltac:(rewrite SI1; discriminate)) as HRi.
lazymatch type of SP1 with rw_cells _ _ _ ?sp' =>
pose proof (hrep_spill RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m1 a (incr_packet_count h) _ sp' ogc opc (hsig_incr Σ1 a h HS) HRi
ltac:(reflexivity) ltac:(reflexivity) ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) ltac:(destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->); reflexivity)
MU WM MI1 SP1) as HR1 end.
rewrite ESPL in HR1.
exists Σ1, a, Fx, fc, m1, ra, t0, t1, t2, (Z64 1), a1, a2, a3, a4, a5, a6, a7, (Z64 (x_F X + HO_OG)), (Z64 (1 + h_extra_headers h)), t3, t4, t5, t6,
j0, j192, j200, ogc, opc.
split; [unfold h_regs; cbn [incr_packet_count h_packet_count h_extra_headers]; unfold HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; exact Hc1|].
split; [exact FRM|]. split; [exact (hsig_incr Σ1 a h HS)|]. split; [exact HIT|]. split; [exact SI1|].
split; [exact HR1|]. split; [exact OGJ| exact OPJ].
Qed.

Lemma dec_bounds : forall d : dec_state bptr, (dec_depth d <= 3)%nat ->
dec_stack d <= H_STACK /\ (dec_frames d <= 15)%nat /\ dec_credit d <= H_DEC_CREDIT.
Proof.
intros d Hd.
assert (SBS : (SB_OWN_STACK <=? 20000) && (0 <=? SB_OWN_STACK) = true) by reflexivity.
assert (NBS : (NBDEC_STACK <=? 20000) && (0 <=? NBDEC_STACK) = true) by reflexivity.
assert (NBC : (NBDEC_CREDIT <=? 8) && (1 <=? NBDEC_CREDIT) = true) by reflexivity.
apply andb_true_iff in SBS as (SBS1 & SBS2). apply andb_true_iff in NBS as (NBS1 & NBS2). apply andb_true_iff in NBC as (NBC1 & NBC2).
apply Z.leb_le in SBS1, SBS2, NBS1, NBS2, NBC1, NBC2.
destruct d as [st | s1 [st | s2 [st | s3 low]]]; cbn [dec_depth] in Hd;
cbn [dec_stack dec_frames dec_credit dec_depth]; unfold H_STACK, H_DEC_CREDIT, NBDEC_FRAMES; try lia.
pose proof (dec_depth_pos low). lia.
Qed.

Lemma hrep_set_eos : forall (Σ1 : rts RT) (m : mem) a (h : hstate unit) spill ogc opc e, (e = 0 \/ e = 1) ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a (set_bits_st h (h_bits h) (h_st h) e) spill ogc opc.
Proof.
intros Σ1 m a h spill ogc opc e EE HR.
destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & HP).
unfold hrep. cbn [set_bits_st h_frame_size h_bits h_oy h_rate].
do 16 (split; [assumption|]).
split; [unfold h_os_rep in *; cbn [set_bits_st h_stream_init h_os]; exact A17|].
do 3 (split; [assumption|]).
split; [unfold h_dec_rep in *; cbn [set_bits_st h_st]; exact A21|].
unfold hpure, h_consumed, h_pend in *.
cbn [set_bits_st h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18 & REST).
do 17 (split; [assumption|]). split; [exact EE| exact REST].
Qed.

Theorem h_dstep_ok : hinv_ok OUT_rep IO_FP X -> forall (n : nat) (h : hstate unit) (st : dec_state unit) (b : bits_st unit) (eosf pno nbr brem0 : Z)
(q q1 : pst) ret (st1 : dec_state unit) (b1 : bits_st unit) bs,
prun (speex_decode (St := pst) p_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M st b 0) q = Some ((ret, st1, b1), q1) ->
p_err q1 = p_err q ++ bs ->
cpsE asegs (at_DHk RT OUT_rep ERR_rep IO_FP X F0 fs0 h st b (S n) eosf pno nbr brem0) (Spec.X1nu.evw 2 bs)
(fun c => ((((ret =? -1) || (ret =? -2)) = true \/ speex_bits_remaining b1 < 0 \/ n = 0%nat)
/\ at_KT RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_bits_st h b1 (Some st1) eosf) pno nbr brem0 c)
\/ (((ret =? -1) || (ret =? -2)) = false /\ 0 <= speex_bits_remaining b1 /\ (1 <= n)%nat
/\ at_DHk RT OUT_rep ERR_rep IO_FP X F0 fs0 h st1 b1 n eosf pno nbr brem0 c)).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE FD2.
intros HX n h st b eosf pno nbr brem0 q q1 ret st1 b1 bs RUN EB T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & j0 & j192 & j200 & ogc & opc
& Hc & FRM & NR & EOR & STN & E0 & PN0 & HS & HIT & SI1 & HR & OGJ & OPJ & PRM).
set (hD := set_bits_st h b (Some st) 0) in *.
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a hD _ ogc opc HR) as OPOS.
pose proof HR as HR'. destruct HR' as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC
& OSR & (stb & STB) & RATE & (wl & LOOK) & DEC0 & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
pose proof (hsep_of_k RT AF OUT_rep IO_FP X HX Σ1 m a hD _ ART HS) as HSP.
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).
assert (INF : In (x_F X, 8%nat) (rt_frames RT Σ1)) by (rewrite EF; left; reflexivity).
assert (INL : forall e, In e (h_own a hD) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
unfold h_dec_rep in DEC0. cbn [hD set_bits_st h_st] in DEC0.
destruct DEC0 as (DR & SP0 & DD & IS & NRd & NDB & AL8 & NBD & LLB).
pose proof (dec_bounds st DD) as (DSTK & DFR & DCR).

unfold HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS in Hc.
refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ _ c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply dh_w1. exact MI. }
intros ms1 c1 -> Hc1. clear Hc.

edestruct (DEC st Σ1 F0 fs0 (Z64 0x96dfc) (Z64 (x_S1 X)) (x_gp X) (Z64 0x630458) t0 t1 t2 (Z64 (x_usp X)) (Z64 (x_S1 X))
(Z64 (a_S a)) (Z64 (x_F X + 8400)) (Z64 (x_F X + 128)) a3 a4 a5 a6 a7 (Z64 (x_F X + 8608)) (Z64 (x_sf X)) (Z64 (x_F X + 128))
(Z64 (x_F X + 8544)) (Z64 (h_packet_count h)) (Z64 eosf) (Z64 (1 + h_extra_headers h)) (Z64 (a_S a)) (Z64 (Z.of_nat (S n)))
(Z64 (x_F X + 8400)) t3 t4 t5 t6 Fx fc m (x_F X + 128) (x_F X + 9168) (a_S a) (x_F X + 8400) (a_Dc a)
(a_LBD a) b (x_lo X) (x_F X) (a_Dc a) (sb_buf_size b) 8%nat ows stb q q1 ret st1 b1 RUN) as (bs1 & EB1 & DECE).
{ reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
{ exact DR. } { exact DD. } { exact IS. } { exact NRd. } { exact NDB. } { exact AL8. }
{ intros x Hx. apply INL. exact (own_in_blk a hD ltac:(cbn [hD set_bits_st h_st]; discriminate) x Hx). }
{ exact BITS. }
{ destruct HP as (_ & _ & _ & _ & B & _). exact B. }
{ exact (INL _ (own_in_Dc a hD)). }
{ apply Z.le_refl. } { apply Z.le_refl. }
{ exact NBD. }
{ exact OUTB. } { exact LOWS. } { exact STB. }
{ exact INF. }
{ pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m PF) as (_ & _ & ACB & _). unfold in_frame_obj. change (fs_size 8) with 16384. unfold BITS_SIZEOF in *.
split; [lia|]. split; [lia|]. split; [exact ACB| clear - F64; Z.div_mod_to_equations; lia]. }
{ pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m PF) as (ACO & _). unfold in_frame_obj. change (fs_size 8) with 16384.
split; [lia|]. split; [lia|]. split; [exact ACO| clear - F64; Z.div_mod_to_equations; lia]. }
{ pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m PF) as (_ & _ & _ & _ & _ & _ & _ & ACS & _). unfold in_frame_obj. change (fs_size 8) with 16384.
split; [lia|]. split; [lia|]. split; [exact ACS| clear - F64; Z.div_mod_to_equations; lia]. }
{ unfold hidp, BITS_SIZEOF. lia. } { unfold hidp, BITS_SIZEOF. lia. } { unfold hidp. lia. }
{ exact FD2. } { exact ERR. } { exact SSP. }
{ rewrite EF. cbn [length]. unfold FRAMES_MAX. lia. }
{ pose proof (hi_cr _ _ _ HX) as CR0. unfold FUZZ_COST in CR0. pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ.
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PCR & _ & _ & _ & BR & _ & P1 & P2 & _ & _ & _ & _ & P7 & _).
unfold h_cost, H_HDR_CREDIT, H_DEC_CREDIT, h_consumed, h_pend in *. cbn [hD set_bits_st h_packet_count h_oy h_bytes_remaining] in *. lia. }
{ rewrite EPO0. apply pois_above_nil. }
{ exact ART. } { exact MI. } { exact FRM. }
{ rewrite unsigned_lit by lia. exact ST. }
{ rewrite ESP. exact LW. }
{ rewrite unsigned_lit by lia. unfold RT_STACK, H_STACK in *. lia. }
{ rewrite unsigned_lit by lia. unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by lia. exact S32. }
assert (EBS1 : bs1 = bs) by (rewrite EB in EB1; exact (eq_sym (app_inv_head _ _ _ EB1))). subst bs1.
refine (DECE T c1 Hc1 _). clear DECE Hc1.
intros c2 (Σ2 & Hc2 & RR & EDD & EDM & NR' & EOW & ECH & EBS & EL2 & EF2 & ES2 & EC2 & EP2).
Time cps_unpack_lib Hc2 as (m2 & ows' & stb' & RS & RA & PR & DR' & EXC & BITS' & BOK' & OUT' & LOW' & STB' & ACA & ACO & ACS & ERR' & OUTR').
pose proof (ISAVE st st1 b q ret b1 q1 RUN IS) as IS'.
destruct (hrep_dec RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_drv AF_DRV X HX Σ1 Σ2 m m2 a hD _ ogc opc _ st st1 b1 ows' stb' HS HR
ltac:(reflexivity) ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) ltac:(destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->); reflexivity)
eq_refl RA PR DR' BITS' BOK' OUT' LOW' STB' ERR' OUTR' EDD NR' IS' EOW EBS EL2 EF2 ES2 (proj1 EC2) EP2) as (HS2 & HR2).
clear HR ART MI ST PF ERR OUTR SSP SP LSH ENH OUTB LOWS FSZ BITS SY OGC OPC OSR STB RATE LOOK HP DR.
set (hD2 := set_bits_st hD b1 (Some st1) (h_eos hD)) in *.
pose proof HR2 as HR'. destruct HR' as (ART2 & MI2 & ST2 & PF2 & ERR2 & OUTR2 & SSP2 & SP2 & LSH2 & (je2 & ENH2) & (ows2 & OUTB2 & LOWS2) & FSZ2 & BITS2 & SY2
& OGC2 & OPC2 & OSR2 & (stb2 & STB2) & RATE2 & (wl2 & LOOK2) & DEC2 & HP2).
refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c2 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply dh_w2a; [reflexivity| exact RR| exact MI2]. }
intros ms3 c3 [(RM & ->) | (R0 & ->)] Hc3. clear Hc.

assert (KT_HR : forall (m' : mem), hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' a hD2
(h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h) ogc opc ->
hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' a (set_bits_st h b1 (Some st1) eosf)
(h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule (set_bits_st h b1 (Some st1) eosf)))
(Z64 (h_speex_serialno (set_bits_st h b1 (Some st1) eosf))) j0 j192 j200 (h_eos0 (set_bits_st h b1 (Some st1) eosf))) ogc opc).
{ intros m' H'.
assert (ESPL : h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h
= h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule (set_bits_st h b1 (Some st1) eosf)))
(Z64 (h_speex_serialno (set_bits_st h b1 (Some st1) eosf))) j0 j192 j200 (h_eos0 (set_bits_st h b1 (Some st1) eosf))).
{ unfold h_spill, h_eos0. cbn [set_bits_st h_granule_frame_size h_extra_headers h_eos h_nframes h_channels h_last_granule h_speex_serialno].
rewrite E0. reflexivity. }
rewrite <- ESPL. exact (hrep_set_eos Σ2 m' a hD2 _ ogc opc eosf EOR H'). }
assert (KT_HS : hsig_k RT X Σ2 a (set_bits_st h b1 (Some st1) eosf) (10 * H_DEC_CREDIT)).
{ apply (hsig_k_weaken RT X Σ2 a _ (H_DEC_CREDIT * (10 - Z.of_nat (S n)) + dec_credit st)); [unfold H_DEC_CREDIT in *; lia| exact HS2]. }
assert (KT_PR : pc_room X (set_bits_st h b1 (Some st1) eosf)).
{ destruct PRM as (PR1 & PR2). split; [exact PR1| cbn [set_bits_st h_st]; discriminate]. }
-
apply Hk. left. split; [left; destruct RM as [-> | ->]; reflexivity|].
exists Σ2, a, r13, r14, m2, (Z64 0x96dfc), r, r0, r1, (Z64 ret), (Z64 (-3)), r3, r4, r5, r6, r7, r8, (Z64 (Z.of_nat (S n))), r9, r10, r11, r12,
j0, j192, j200, ogc, opc.
split; [cbn [set_bits_st h_packet_count h_eos h_extra_headers]; unfold HO_OP, HO_OUT, HO_OG, HO_BITS; exact Hc3|].
split; [exact RS|]. split; [exact KT_HS|]. split; [exact HIT|]. split; [exact SI1|]. split; [exact EOR|]. split; [exact PN0|].
split; [exact (KT_HR m2 HR2)|]. split; [exact OGJ|]. split; [exact OPJ| exact KT_PR].
-
subst ret.
assert (KT_HR : forall (m' : mem), hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' a hD2
(h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h) ogc opc ->
hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' a (set_bits_st h b1 (Some st1) eosf)
(h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule (set_bits_st h b1 (Some st1) eosf)))
(Z64 (h_speex_serialno (set_bits_st h b1 (Some st1) eosf))) j0 j192 j200 (h_eos0 (set_bits_st h b1 (Some st1) eosf))) ogc opc).
{ intros m' H'.
assert (ESPL : h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h
= h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule (set_bits_st h b1 (Some st1) eosf)))
(Z64 (h_speex_serialno (set_bits_st h b1 (Some st1) eosf))) j0 j192 j200 (h_eos0 (set_bits_st h b1 (Some st1) eosf))).
{ unfold h_spill, h_eos0. cbn [set_bits_st h_granule_frame_size h_extra_headers h_eos h_nframes h_channels h_last_granule h_speex_serialno].
rewrite E0. reflexivity. }
rewrite <- ESPL. exact (hrep_set_eos Σ2 m' a hD2 _ ogc opc eosf EOR H'). }
assert (KT_HS : hsig_k RT X Σ2 a (set_bits_st h b1 (Some st1) eosf) (10 * H_DEC_CREDIT)).
{ apply (hsig_k_weaken RT X Σ2 a _ (H_DEC_CREDIT * (10 - Z.of_nat (S n)) + dec_credit st)); [unfold H_DEC_CREDIT in *; lia| exact HS2]. }
assert (KT_PR : pc_room X (set_bits_st h b1 (Some st1) eosf)).
{ destruct PRM as (PR1 & PR2). split; [exact PR1| cbn [set_bits_st h_st]; discriminate]. }
assert (BDc : a_Dc a + sb_buf_size b1 <= x_lo X).
{ destruct (hsep_of_k RT AF OUT_rep IO_FP X HX Σ2 m2 a hD2 _ ART2 HS2) as (HSP1 & _).
destruct (HSP1 _ _ (own_in_Dc a hD2)) as (_ & DL & _). cbn [hD2 hD set_bits_st h_bits] in DL. exact DL. }
refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c3 (PMfd_mat_stable F0 fs0) Hc3 _ _).
{ eapply (speex_bits_remaining_walk (x_F X + 8400) (a_Dc a) (x_S1 X) (x_lo X) b1).
- exact BITS2.
- exact BOK'.
- unfold aobj. unfold BITS_SIZEOF in *. split; [lia|]. split; [unfold APP_TOP; unfold RT_STACK, H_STACK, USTACK_TOP in *; lia| exact ACA].
- exact ST2.
- unfold RT_STACK, H_STACK in *. lia.
- exact SHLO.
- unfold USTACK_TOP in *. lia.
- unfold BITS_SIZEOF. lia.
- exact BDc.
- exact (af_client_consts RT AF Σ2 m2 ART2).
- exact MI2. }
intros ms4 c4 (v0 & v1 & v2 & v3 & v4 & v5 & m3 & -> & MU3 & WM3 & MI3 & ST3 & EV0 & BITS3) Hc4. clear Hc3. subst v0.
assert (OUT3 : rw_cells asegs m3 (x_F X + 128) (f32 ows2)).
{ apply (rw_cells_transport asegs _ m2 m3 _ _ OUTB2 MU3 WM3). rewrite cells_size_f32, LOWS2. cbn [disjoint_from].
split; [left; unfold HO_OUT, HO_STEREO, RT_STACK, H_STACK in *; lia| exact I]. }
assert (STB3 : rw_cells asegs m3 (x_F X + 9168) [CB 24 stb2]).
{ apply (rw_cells_transport asegs _ m2 m3 _ _ STB2 MU3 WM3). cbn [disjoint_from cells_size csize Nat.add].
split; [left; unfold HO_OUT, HO_STEREO, RT_STACK, H_STACK in *; lia| exact I]. }
pose proof (hrep_out_step RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ2 m2 m3 a hD2 _ ogc opc ows2 stb2 _ HS2 HR2
ltac:(reflexivity) ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) ltac:(destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->); reflexivity)
ltac:(apply (munch_weaken [(x_S1 X + -16, x_S1 X)]); [unfold sub_fp; cbn [outside]; intros x Hx; tauto| exact MU3])
WM3 MI3 ST3 OUT3 LOWS2 STB3) as HR3.
clear HR2 MU3 WM3 OUT3 STB3.
assert (REMR : -2^63 <= speex_bits_remaining b1 < 2^63).
{ pose proof BITS3 as (_ & _ & SIDE3). destruct (bits_ints _ _ b1 BOK' SIDE3) as (I1 & I2 & I3 & _ & _ & _ & C1 & C2 & IP & _).
unfold speex_bits_remaining. destruct (negb (sb_overflow b1 =? 0)); [lia|]. unfold bits_pos, int31 in *. lia. }
pose proof HR3 as HR'. destruct HR' as (ART3 & _ & _ & PF3 & ERR3 & OUTR3 & SSP3 & SP3 & LSH3 & (je3 & ENH3) & (ows3 & OUTB3 & LOWS3) & FSZ3 & BITS3' & SY3
& OGC3 & OPC3 & OSR3 & (stb3 & STB3) & RATE3 & (wl3 & LOOK3) & DEC3 & HP3).
unfold h_spill in SP3. unfold HO_FSZ, HO_STEREO, HO_LOOK, HO_RATE, HO_ENH, HO_OY, HO_OS in SP3, FSZ3.
pose proof HP3 as (_ & _ & _ & _ & _ & _ & _ & FSR & _ & _ & CHR & _).
assert (K_DT : forall (m' : mem) (Fx' : bvmap 5 word) (fc' : bv 32) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (c' : config),
ASTA RT Σ2 (PMfd F0 fs0) (eq (MS (mkR ra' (Z64 (x_S1 X)) (x_gp X) (Z64 0x630458) t0' t1' t2' (Z64 (x_usp X)) (Z64 (x_S1 X))
a0' a1' a2' a3' a4' a5' a6' a7' (Z64 (x_F X + 8608)) (Z64 (x_sf X)) (Z64 (x_F X + 128)) (Z64 (x_F X + 8544))
(Z64 (h_packet_count h)) (Z64 eosf) (Z64 (1 + h_extra_headers h)) (Z64 (a_S a)) (Z64 (Z.of_nat (S n)))
(Z64 (x_F X + 8400)) t3' t4' t5' t6') Fx' (Z64 A_DT) fc' None m' (seg_rom asegs))) c' ->
frm0 fc' -> 0 <= speex_bits_remaining b1 -> hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' a hD2
(h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h) ogc opc ->
realizes asegs c' T).
{ intros m' Fx' fc' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' c' Hc' FRM' RP0 HR'.
pose proof HR' as (_ & MI' & _).
refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c' (PMfd_mat_stable F0 fs0) Hc' _ _).
{ eapply (dh_w2c (Z.of_nat (S n))); [lia| exact MI']. }
intros ms6 c6 [(N1 & ->) | (N2 & ->)] Hc6.
- apply Hk. left. split; [right; right; lia|].
exists Σ2, a, Fx', fc', m'. do 17 eexists. exists j0, j192, j200, ogc, opc.
split; [cbn [set_bits_st h_packet_count h_eos h_extra_headers]; unfold HO_OP, HO_OUT, HO_OG, HO_BITS; exact Hc6|].
split; [exact FRM'|]. split; [exact KT_HS|]. split; [exact HIT|]. split; [exact SI1|]. split; [exact EOR|]. split; [exact PN0|].
split; [exact (KT_HR m' HR')|]. split; [exact OGJ|]. split; [exact OPJ| exact KT_PR].
- apply Hk. right. split; [reflexivity|]. split; [exact RP0|]. split; [lia|].
replace (Z.of_nat (S n) - 1) with (Z.of_nat n) in Hc6 by lia.
exists Σ2, a, Fx', fc', m'. do 16 eexists. exists j0, j192, j200, ogc, opc.
split; [unfold HO_OP, HO_OUT, HO_OG, HO_BITS; exact Hc6|].
split; [exact FRM'|]. split; [lia|]. split; [exact EOR|]. split; [exact STN|]. split; [exact E0|]. split; [exact PN0|].
split; [apply (hsig_k_weaken RT X Σ2 a _ (H_DEC_CREDIT * (10 - Z.of_nat (S n)) + dec_credit st)); [unfold H_DEC_CREDIT in *; lia| exact HS2]|].
split; [exact HIT|]. split; [exact SI1|]. split; [exact HR'|]. split; [exact OGJ|]. split; [exact OPJ| exact PRM]. }
refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c4 (PMfd_mat_stable F0 fs0) Hc4 _ _).
{ eapply (dh_w2b (x_S1 X) (x_F X) (speex_bits_remaining b1) (h_channels h) (h_frame_size h)); [reflexivity| exact S1R| exact REMR| exact CHR| exact FSR| | | exact MI3].
- cbn [hD2 hD set_bits_st h_frame_size] in FSZ3. exact FSZ3.
- cbn [hD2 hD set_bits_st h_granule_frame_size h_extra_headers h_eos h_nframes h_channels] in SP3. exact SP3. }
intros ms5 c5 [(RN & ->) | [(RP & CN & ->) | (RP & C2 & ->)]] Hc5. clear Hc4.
+
apply Hk. left. split; [right; left; exact RN|].
exists Σ2, a, r13, r14, m3. do 17 eexists. exists j0, j192, j200, ogc, opc.
split; [cbn [set_bits_st h_packet_count h_eos h_extra_headers]; unfold HO_OP, HO_OUT, HO_OG, HO_BITS; exact Hc5|].
split; [exact RS|]. split; [exact KT_HS|]. split; [exact HIT|]. split; [exact SI1|]. split; [exact EOR|]. split; [exact PN0|].
split; [exact (KT_HR m3 HR3)|]. split; [exact OGJ|]. split; [exact OPJ| exact KT_PR].
+
eapply K_DT; [exact Hc5| exact RS| exact RP| exact HR3].
+
subst. destruct (rw_cells_CB_f32 asegs m3 (x_F X + HO_STEREO) 6 stb3 STB3) as ([|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 ws6]]]]]]] & L6 & STB6);
cbn [length] in L6; try lia.
pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m3 PF3) as (ACO3 & _ & _ & _ & _ & _ & _ & ACS3 & _).
pose proof (hi_F _ _ _ HX) as (_ & _ & _ & FSH & _). change (fs_size 8) with 16384 in FSH.
unfold HO_OUT, HO_STEREO in *.
assert (FSRh : 0 <= h_frame_size h <= 640) by exact FSR.
refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c5 (PMfd_mat_stable F0 fs0) Hc5 _ _).
{ eapply (speex_decode_stereo_walk (x_F X + 128) (x_F X + 9168) (x_S1 X) (x_lo X) 2000%nat).
- unfold aobj. split; [lia|]. split; [unfold APP_TOP, RT_STACK, H_STACK, USTACK_TOP in *; lia| exact ACO3].
- unfold aobj. split; [lia|]. split; [unfold APP_TOP, RT_STACK, H_STACK, USTACK_TOP in *; lia| exact ACS3].
- clear - F64. Z.div_mod_to_equations. lia.
- clear - F64. Z.div_mod_to_equations. lia.
- try change (Z.of_nat 2000) with 2000. lia.
- try change (Z.of_nat 2000) with 2000. unfold RT_STACK, H_STACK in *. lia.
- exact SHLO.
- unfold USTACK_TOP in *. lia.
- try change (Z.of_nat 2000) with 2000. lia.
- try change (Z.of_nat 2000) with 2000. lia.
- try change (Z.of_nat 2000) with 2000. unfold RT_STACK, H_STACK in *. lia.
- try change (Z.of_nat 2000) with 2000. unfold RT_STACK, H_STACK in *. lia.
- try change (Z.of_nat 2000) with 2000. lia.
- exact OUTB3.
- exact LOWS3.
- exact STB6.
- try change (Z.of_nat 2000) with 2000. lia.
- try change (Z.of_nat 2000) with 2000. lia.
- unfold IMG_TOP, SEGTOP_A in *. lia.
- unfold IMG_TOP, SEGTOP_A in *. lia.
- exact (af_client_consts RT AF Σ2 m3 ART3).
- exact ST3.
- exact MI3.
- exact RS. }
intros ms6 c6 (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & F6 & fc6 & m4 & ws4 & sw4 & -> & MU4 & WM4 & MI4 & ST4 & FRM4
& OUT4 & LW4 & STW4 & LS4) Hc6. clear Hc5.
pose proof (rw_cells_f32_CB asegs m4 (x_F X + 9168) sw4 STW4) as STB4. rewrite LS4 in STB4.
pose proof (hrep_out_step RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ2 m3 m4 a hD2 _ ogc opc ws4 (cells_bytes (f32 sw4)) _ HS2 HR3
ltac:(reflexivity) ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) ltac:(destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->); reflexivity)
ltac:(eapply munch_weaken; [| exact MU4]; unfold sub_fp; cbn [outside]; intros x Hx; change (Z.of_nat 2000) with 2000 in Hx |- *; lia)
WM4 MI4 ST4 OUT4 LW4 STB4) as HR4.
replace (ret_pc (Z64 618032)) with (Z64 618032) in Hc6 by (symmetry; apply ret_pc_even; [lia | reflexivity]).
eapply K_DT; [exact Hc6| exact FRM4| exact RP| exact HR4].
Qed.

Lemma cpsE_or : forall (P1 P2 Q : config -> Prop) e, cpsE asegs P1 e Q -> cpsE asegs P2 e Q -> cpsE asegs (fun c => P1 c \/ P2 c) e Q.
Proof. intros P1 P2 Q e H1 H2 T c [Hc|Hc] Hk; [exact (H1 T c Hc Hk)| exact (H2 T c Hc Hk)]. Qed.

Theorem h_dloop_ok : hinv_ok OUT_rep IO_FP X -> forall (n : nat) (h : hstate unit) (st : dec_state unit) (b : bits_st unit) (eosf pno nbr brem0 : Z)
(q q' : pst) (st' : dec_state unit) (b' : bits_st unit) bs,
prun (hP_decode_loop n st b) q = Some ((st', b'), q') -> p_err q' = p_err q ++ bs ->
cpsE asegs (at_DHk RT OUT_rep ERR_rep IO_FP X F0 fs0 h st b n eosf pno nbr brem0) (Spec.X1nu.evw 2 bs)
(at_KT RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_bits_st h b' (Some st') eosf) pno nbr brem0).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE FD2.
intros HX n. induction n as [|n IH]; intros h st b eosf pno nbr brem0 q q' st' b' bs RUN EB.
- intros T c Hc _. exfalso.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & j0 & j192 & j200 & ogc & opc
& Hc & FRM & NR & _). lia.
- unfold hP_decode_loop in RUN.
destruct (dloop_step n st b q (st', b') q' RUN) as (ret & st1 & b1 & q1 & ED & CASES).
destruct (X065.dec_appends_all st b q _ q1 ED) as (bs1 & EB1).
destruct CASES as [(RC & ER & EQ) | [(RC & RN & ER & EQ) | (RC & RP & HR)]].
+ injection ER as -> ->. subst q'. rewrite EB in EB1. apply app_inv_head in EB1. subst bs1.
eapply cpsE_conseq; [apply (h_dstep_ok HX n h st b eosf pno nbr brem0 q q1 ret st1 b1 bs ED EB)| intros c Hc; exact Hc|].
intros c [(_ & H) | (RC' & _)]; [exact H| rewrite RC in RC'; discriminate RC'].
+ injection ER as -> ->. subst q'. rewrite EB in EB1. apply app_inv_head in EB1. subst bs1.
eapply cpsE_conseq; [apply (h_dstep_ok HX n h st b eosf pno nbr brem0 q q1 ret st1 b1 bs ED EB)| intros c Hc; exact Hc|].
intros c [(_ & H) | (_ & RP' & _)]; [exact H| lia].
+ destruct (dloop_appends n st1 b1 q1 _ q' HR) as (bs2 & EB2).
assert (EBS : bs = bs1 ++ bs2) by (rewrite EB2, EB1, <- app_assoc in EB; exact (eq_sym (app_inv_head _ _ _ EB))). subst bs.
rewrite Spec.X1nu.evw_app.
eapply cpsE_seq; [apply (h_dstep_ok HX n h st b eosf pno nbr brem0 q q1 ret st1 b1 bs1 ED EB1)|].
apply cpsE_or.
*
destruct n as [|n'].
-- cbn [decode_loop] in HR. rewrite prun_ret in HR. injection HR as <- <- <-.
assert (LB : length bs2 = 0%nat) by (apply (f_equal (@length Z)) in EB2; rewrite length_app in EB2; lia).
destruct bs2; [| discriminate LB]. cbn [Spec.X1nu.evw map]. apply cpsE_nil.
intros T c (CX & Hc) Hk. apply Hk. exact Hc.
-- intros T c (CX & Hc) Hk. exfalso. destruct CX as [CX|[CX|CX]]; [rewrite RC in CX; discriminate CX| lia| discriminate CX].
* intros T c (_ & _ & N1 & Hc) Hk. exact (IH h st1 b1 eosf pno nbr brem0 q1 q' st' b' bs2 HR EB2 T c Hc Hk).
Qed.

Definition at_RF (h : hstate unit) (op : packet) (pno nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(j0 j192 j200 gw : word) (ogc kc : list cell),
ASTA RT Σ1 (PMfd F0 fs0) (eq (MS (mkR (Z64 0x96de4) (Z64 (x_S1 X)) (x_gp X) (Z64 0x630458) t0 t1 t2 (Z64 (x_usp X)) (Z64 (x_S1 X))
(Z64 (x_F X + 8400)) (Z64 (a_Bd a + pk_off op)) (Z64 (pk_bytes op)) a3 a4 a5 a6 a7
(Z64 (x_F X + 8608)) (Z64 (x_sf X)) (Z64 (x_F X + 128)) (Z64 (x_F X + 8544)) (Z64 (h_packet_count h))
(Z64 (Z.b2z (0 <? pk_e_o_s op))) (Z64 (1 + h_extra_headers h)) (Z64 (a_S a)) (Z64 (pk_bytes op))
(Z64 (x_F X + 8400)) t3 t4 t5 t6) Fx (Z64 A_speex_bits_read_from_h) fc None m (seg_rom asegs))) c
/\ X1cn.frm0 fc /\ hsig RT X Σ1 a h /\ h_iter X h nbr brem0 /\ h_stream_init h = 1 /\ h_eos h = 0 /\ 0 <= pno /\ h_st h <> None
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h (h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h)
ogc (op_cells (a_Bd a) (Some op) gw kc)
/\ og_junk ogc /\ cells_size kc = 48%nat
/\ 0 <= pk_off op /\ 0 <= pk_bytes op /\ pk_off op + pk_bytes op <= os_body_fill (h_os h) /\ 0 <= pk_e_o_s op < 2^63
/\ pc_room X h.

Lemma b2z_ltb0 : forall e, 0 <= e -> Z.b2z (0 <? e) = (if e =? 0 then 0 else 1).
Proof. intros e He. destruct (Z.eqb_spec e 0) as [->|NE]; [reflexivity|]. replace (0 <? e) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

Lemma pk_window : forall (m : mem) (Bd : Z) (body : list byte) (os : stream_st unit) (op : packet),
u8arr asegs m Bd body -> body_pre (os_body os) body -> zlength (os_body os) = os_body_fill os ->
0 <= pk_off op -> 0 <= pk_bytes op -> pk_off op + pk_bytes op <= os_body_fill os ->
u8ro asegs m (Bd + pk_off op) (firstn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) body))
/\ map bv_unsigned (firstn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) body)) = packet_data os op
/\ Z.of_nat (length (firstn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) body))) = pk_bytes op.
Proof.
intros m Bd body os op [UB _] [BP BL] ZL P0 P1 P2. unfold zlength in ZL.
assert (ON : (Z.to_nat (pk_off op) + Z.to_nat (pk_bytes op) <= length (os_body os))%nat) by lia.
split; [| split].
- unfold u8ro. rewrite <- (firstn_skipn (Z.to_nat (pk_off op)) body) in UB. apply bytes_at_app in UB as [_ UB].
rewrite <- (firstn_skipn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) body)) in UB. apply bytes_at_app in UB as [UB _].
rewrite length_firstn in UB. replace (Bd + Z.of_nat (Nat.min (Z.to_nat (pk_off op)) (length body))) with (Bd + pk_off op) in UB by lia. exact UB.
- unfold packet_data, zslice, ztake, zdrop. rewrite <- BP. unfold ubytes.
rewrite skipn_firstn_comm, firstn_firstn. replace (Nat.min (Z.to_nat (pk_bytes op)) (length (os_body os) - Z.to_nat (pk_off op))) with (Z.to_nat (pk_bytes op)) by lia.
rewrite skipn_map, firstn_map. reflexivity.
- rewrite length_firstn, length_skipn. lia.
Qed.

Lemma hrep_op_junk : forall (Σ1 : rts RT) (m : mem) a (h : hstate unit) spill ogc Bd op gw kc,
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc (op_cells Bd (Some op) gw kc) ->
exists opc, op_junk opc /\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc.
Proof.
intros Σ1 m a h spill ogc Bd op gw kc HR.
destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22).
cbn [op_cells] in A16.
exists [CB 8 (le8 (wz (Bd + pk_off op))); CB 8 (le8 (wz (pk_bytes op))); CB 8 (le8 (wz (pk_b_o_s op))); CB 8 (le8 (wz (pk_e_o_s op)));
CB 8 (le8 gw); CB 8 (le8 (wz (pk_packetno op)))].
split; [do 6 eexists; reflexivity|].
assert (A16' : rw_cells asegs m (x_F X + HO_OP) [CB 8 (le8 (wz (Bd + pk_off op))); CB 8 (le8 (wz (pk_bytes op))); CB 8 (le8 (wz (pk_b_o_s op)));
CB 8 (le8 (wz (pk_e_o_s op))); CB 8 (le8 gw); CB 8 (le8 (wz (pk_packetno op)))]).
{ eapply rw_cells_recast; [exact A16| cbn [cells_wf cell_wf]; repeat split; apply length_le8| reflexivity]. }
exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 (conj A10 (conj A11 (conj A12 (conj A13 (conj A14 (conj A15
(conj A16' (conj A17 (conj A18 (conj A19 (conj A20 (conj A21 A22))))))))))))))))))))).
Qed.

Theorem h_data_ok : hinv_ok OUT_rep IO_FP X -> forall (h : hstate unit) (op : packet) (pno nbr brem0 : Z) (q q1 q' : pst) (b : bits_st unit)
(d st' : dec_state unit) (b' : bits_st unit) bs,
h_st h = Some d ->
prun (speex_bits_read_from (St := pst) p_realloc p_notify p_warning (h_bits h) (packet_data (h_os h) op) (pk_bytes op)) q = Some (b, q1) ->
prun (hP_decode_loop (Z.to_nat (h_nframes h)) d b) q1 = Some ((st', b'), q') ->
p_err q' = p_err q ++ bs ->
cpsE asegs (at_RF h op pno nbr brem0) (Spec.X1nu.evw 2 bs)
(at_KT RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_bits_st h b' (Some st') (if pk_e_o_s op =? 0 then 0 else 1)) (pno + 1) nbr brem0).
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE FD2 RF.
intros HX h op pno nbr brem0 q q1 q' b d st' b' bs ESt RUN1 RUN2 EB T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & j0 & j192 & j200 & gw & ogc & kc
& Hc & FRM & HS & HIT & SI1 & E0 & PN0 & STN & HR & OGJ & KCS & PK0 & PK1 & PK2 & EOR & PRM).
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a h _ ogc _ HR) as OPOS.
pose proof HR as HR'. destruct HR' as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC
& OSR & (stb & STB) & RATE & (wl & LOOK) & DEC0 & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART HS) as HSP.
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).
assert (INF : In (x_F X, 8%nat) (rt_frames RT Σ1)) by (rewrite EF; left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }

unfold h_os_rep in OSR. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0'|_]; [rewrite SI1 in E0'; discriminate E0'|].
destruct OSR as (OS & LH & (UB & LB & BP & UL & WP & LL & UG & LG) & FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS & NBL & NBG & NLG).
destruct (pk_window m (a_Bd a) (a_body a) (h_os h) op UB BP (proj1 BINV) PK0 PK1 PK2) as (U8 & EPD & LPB).
set (pb := firstn (Z.to_nat (pk_bytes op)) (skipn (Z.to_nat (pk_off op)) (a_body a))) in *.
rewrite <- EPD in RUN1.
assert (SIN : h_stream_init h <> 0) by (rewrite SI1; discriminate).
pose proof (own_in_os a h SIN) as (IBD & _ & _).
pose proof (own_ne_os a h (proj2 (proj2 HSP)) SIN (a_Bd a) (or_introl eq_refl)) as (NBD & _).
assert (LVR : Z.of_nat (length (rt_live RT Σ1)) < LIVE_MAX).
{ rewrite (h_live_len RT X Σ1 a h HS).
pose proof (h_own_len RT OUT_rep ERR_rep IO_FP X Σ1 m a h _ _ _ HR) as L24.
pose proof (hi_live _ _ _ HX) as (_ & LLV). unfold H_LIVE in LLV. lia. }
assert (BFS : pk_off op + pk_bytes op <= os_body_storage (h_os h)).
{ destruct BP as (_ & BPL). pose proof (proj1 BINV) as ZL. unfold zlength in ZL. unfold bptr in *. lia. }
assert (LEN : pk_bytes op <= 4096).
{ pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ.
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BR & _ & P1 & P2 & _ & BF & _).
unfold h_consumed, h_pend in *. lia. }
pose proof HP as (_ & _ & _ & _ & BOK & OWN & BSZ & _ & _ & NFR & _).
assert (OV : p_overflows (pk_bytes op) = false) by (unfold p_overflows; apply Z.leb_gt; lia).
destruct (read_from_prun (h_bits h) (map bv_unsigned pb) (pk_bytes op) q b q1 RUN1 OWN OV) as [PFIT PBIG].
edestruct (RF Σ1 F0 fs0 (Z64 0x96de4) (Z64 (x_S1 X)) (x_gp X) (Z64 0x630458) t0 t1 t2 (Z64 (x_usp X)) (Z64 (x_S1 X))
(Z64 (x_F X + 8400)) (Z64 (a_Bd a + pk_off op)) (Z64 (pk_bytes op)) a3 a4 a5 a6 a7 (Z64 (x_F X + 8608)) (Z64 (x_sf X))
(Z64 (x_F X + 128)) (Z64 (x_F X + 8544)) (Z64 (h_packet_count h)) (Z64 (Z.b2z (0 <? pk_e_o_s op))) (Z64 (1 + h_extra_headers h))
(Z64 (a_S a)) (Z64 (pk_bytes op)) (Z64 (x_F X + 8400)) t3 t4 t5 t6 Fx fc m (x_F X + 8400) (a_Dc a) (a_Bd a + pk_off op) (x_F X)
(a_Bd a) (os_body_storage (h_os h)) (x_lo X) 8%nat (h_bits h) pb (pk_bytes op) q q1 b RUN1) as (bs1 & EB1 & RFE).
{ reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
{ exact BITS. } { exact BOK. } { exact OWN. }
{ exact (h_bits_shadow_at OUT_rep IO_FP IO_img X HX m PF). }
{ exact INF. } { lia. } { change (fs_size 8) with 16384. lia. }
{ exact (INL _ (own_in_Dc a h)). }
{ exact U8. } { rewrite LPB. lia. } { unfold READ_FROM_LEN_MAX. lia. }
{ exact (INL _ IBD). } { lia. } { rewrite LPB. lia. }
{ exact (not_eq_sym NBD). }
{ exact FD2. } { exact ERR. } { exact SSP. } { exact LVR. }
{ exact (af_credit_nonneg RT AF Σ1 m ART). }
{ rewrite EPO0. apply pois_above_nil. }
{ exact ART. } { exact MI. }
{ rewrite unsigned_lit by lia. exact ST. }
{ rewrite ESP. exact LW. }
{ rewrite unsigned_lit by lia. unfold RT_STACK, H_STACK in *. lia. }
{ rewrite unsigned_lit by lia. unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by lia. apply Z.mod_divide; [lia|]. apply Z.mod_divide in S32; [|lia]. destruct S32 as (k32 & E32). exists (2 * k32). lia. }

pose proof RUN2 as RUN2'. unfold hP_decode_loop in RUN2'. destruct (dloop_appends _ d b q1 _ q' RUN2') as (bs2 & EB2). clear RUN2'.
assert (EBS : bs = bs1 ++ bs2) by (rewrite EB2, EB1, <- app_assoc in EB; exact (eq_sym (app_inv_head _ _ _ EB))). subst bs.
rewrite Spec.X1nu.evw_app.
eapply rz_conseq; [| apply t_eq_sym, t_emit_app].
refine (RFE (t_emit (Spec.X1nu.evw 2 bs2) T) c Hc _). clear RFE Hc.
intros c2 (Σ2 & D' & Hc2 & INL2 & CASE & EF2 & ES2 & EC2 & EP2).
Time cps_unpack_lib Hc2 as (v & m2 & RS & RA & PR & BITS' & BOK' & SHC' & ERR' & OUTR').

assert (OWN' : sb_owner b = 1 /\ 2000 <= sb_buf_size b <= 64512
/\ (pk_bytes op <= sb_buf_size (h_bits h) -> sb_buf_size b = sb_buf_size (h_bits h))
/\ (sb_buf_size (h_bits h) < pk_bytes op -> sb_buf_size b = pk_bytes op)).
{ destruct (Z_le_gt_dec (pk_bytes op) (sb_buf_size (h_bits h))) as [C|C].
- destruct (PFIT C) as (EBB & _). rewrite EBB. cbn [sb_owner sb_buf_size]. split; [exact OWN|]. split; [lia|]. split; [intros _; reflexivity| intros; lia].
- destruct (PBIG ltac:(lia)) as (EBB & _). rewrite EBB. cbn [sb_owner sb_buf_size]. split; [exact OWN|]. split; [lia|]. split; [intros; lia| intros _; reflexivity]. }
assert (CASE' : (pk_bytes op <= sb_buf_size (h_bits h) /\ D' = a_Dc a /\ rt_live RT Σ2 = rt_live RT Σ1 /\ sb_buf_size b = sb_buf_size (h_bits h))
\/ (sb_buf_size (h_bits h) < pk_bytes op /\ rt_live RT Σ2 = (D', pk_bytes op) :: live_remove (a_Dc a) (rt_live RT Σ1)
/\ sb_buf_size b = pk_bytes op)).
{ destruct OWN' as (_ & _ & S1' & S2'). destruct CASE as [(C1 & C2 & C3) | (C1 & C2)].
- left. split; [exact C1|]. split; [exact C2|]. split; [exact C3| exact (S1' C1)].
- right. split; [exact C1|]. split; [exact C2| exact (S2' C1)]. }
destruct (hrep_rf RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_drv AF_DRV X HX Σ1 Σ2 m m2 a h _ ogc _ 0 (pk_bytes op) D' b
(hsig_k_of RT X Σ1 a h HS) HR ltac:(reflexivity) ltac:(destruct OGJ as (g0 & g1 & g2 & g3 & ->); reflexivity) ltac:(reflexivity)
RA PR BITS' BOK' (proj1 OWN') (proj1 (proj2 OWN')) ERR' OUTR' CASE' EF2 ES2 EC2 EP2) as (P' & HS2 & HR2).
destruct (hrep_op_junk Σ2 m2 _ _ _ ogc (a_Bd a) op gw kc HR2) as (opc & OPJ & HR3). clear HR2.
rewrite ESt, E0 in HS2, HR3.
clear HR ART MI ST PF ERR OUTR SSP SP LSH ENH OUTB LOWS FSZ BITS SY OGC OPC STB RATE LOOK DEC0.
pose proof HR3 as HR'. destruct HR' as (ART2 & MI2 & ST2 & PF2 & ERR2 & OUTR2 & SSP2 & SP2 & _).

refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ _ c2 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply kd_w1; [reflexivity| exact S1R| exact NFR| unfold h_spill in SP2; exact SP2| exact MI2]. }
intros ms3 c3 -> Hc3. clear Hc.

rewrite (b2z_ltb0 _ (proj1 EOR)) in Hc3.
assert (HDk : at_DHk RT OUT_rep ERR_rep IO_FP X F0 fs0 h d b (Z.to_nat (h_nframes h)) (if pk_e_o_s op =? 0 then 0 else 1) (pno + 1) nbr brem0 c3).
{ exists Σ2, (a_set_dc a D' P'), r13, r14, m2, (Z64 617956), r, r0, r1, v, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, j0, j192, j200, ogc, opc.
split; [cbn [a_set_dc a_S]; unfold HO_OP, HO_OUT, HO_OG, HO_BITS; rewrite Z2Nat.id by lia; exact Hc3|].
split; [exact (RS FRM)|]. split; [lia|]. split; [destruct (pk_e_o_s op =? 0); [left| right]; reflexivity|].
split; [exact STN|]. split; [exact E0|]. split; [lia|].
split; [apply (hsig_k_weaken RT X Σ2 _ _ 0); [unfold H_DEC_CREDIT; lia| exact HS2]|].
split; [exact HIT|]. split; [exact SI1|]. split; [exact HR3|]. split; [exact OGJ|]. split; [exact OPJ| exact PRM]. }
exact (h_dloop_ok HX (Z.to_nat (h_nframes h)) h d b _ (pno + 1) nbr brem0 q1 q' st' b' bs2 RUN2 EB2 T c3 HDk Hk).
Qed.

Lemma prun_cleanup_none : forall (h : hstate unit) q, h_st h = None -> prun (hP_cleanup h) q = Some (tt, q).
Proof.
intros h q E. unfold hP_cleanup, cleanup. rewrite E.
unfold speex_bits_destroy, ogg_stream_clear, ogg_sync_clear, mfree_opt.
destruct (negb (sb_owner (h_bits h) =? 0)), (negb (h_stream_init h =? 0)), (os_body_data (h_os h)), (os_lacing_vals (h_os h)),
(os_granule_vals (h_os h)), (sy_data (h_oy h)); reflexivity.
Qed.

Definition pk_sser (h : hstate unit) (os : stream_st unit) (op : packet) : Z :=
if (5 <=? pk_bytes op) && list_eqb (ztake 5 (packet_data os op)) SPEEX_STR then os_serialno os else h_speex_serialno h.

Definition pkt_cases (fuel : nat) (h1 : hstate unit) (os : stream_st unit) (op : packet) (pno : Z) (q : pst) (o : outcome unit) (q' : pst) : Prop :=
((pk_sser h1 os op = -1 \/ os_serialno os <> pk_sser h1 os op) /\ o = Cont (set_serialno h1 (pk_sser h1 os op)) /\ q' = q)
\/ (pk_sser h1 os op <> -1 /\ os_serialno os = pk_sser h1 os op /\
( (h_packet_count h1 = 0 /\ exists ph q1, prun (hP_process_header (set_serialno h1 (pk_sser h1 os op)) (packet_data os op) (pk_bytes op)) q = Some (ph, q1)
/\ match ph with None => o = Returned /\ q' = q1
| Some h3 => prun (hP_packet_loop fuel (incr_packet_count h3) pno) q1 = Some (o, q') end)
\/ (h_packet_count h1 <> 0 /\ h_packet_count h1 <= 1 + h_extra_headers h1
/\ prun (hP_packet_loop fuel (incr_packet_count (set_serialno h1 (pk_sser h1 os op))) pno) q = Some (o, q'))
\/ (h_packet_count h1 <> 0 /\ 1 + h_extra_headers h1 < h_packet_count h1 /\
exists d b q1 st' b' q2, h_st h1 = Some d
/\ prun (speex_bits_read_from (St := pst) p_realloc p_notify p_warning (h_bits h1) (packet_data os op) (pk_bytes op)) q = Some (b, q1)
/\ prun (hP_decode_loop (Z.to_nat (h_nframes h1)) d b) q1 = Some ((st', b'), q2)
/\ prun (hP_packet_loop fuel (incr_packet_count (set_bits_st (set_serialno h1 (pk_sser h1 os op)) b' (Some st')
(if pk_e_o_s op =? 0 then 0 else 1))) (pno + 1)) q2 = Some (o, q')))).

Lemma pkt_step : forall fuel (h : hstate unit) pno q o q', h_eos h = 0 -> (h_packet_count h = 0 -> h_st h = None) ->
prun (hP_packet_loop (S fuel) h pno) q = Some (o, q') ->
exists r opo os, ogg_stream_packetout (h_os h) = Some ((r, opo), os) /\
( (r <> 1 /\ o = Cont (set_ogg h (h_oy h) os) /\ q' = q)
\/ (r = 1 /\ exists op, opo = Some op /\ pkt_cases fuel (set_ogg h (h_oy h) os) os op pno q o q') ).
Proof.
intros fuel h pno q o q' E0 PC0 H.
unfold hP_packet_loop in H. cbn [packet_loop] in H. rewrite E0 in H. cbn [Z.eqb negb] in H.
destruct (ogg_stream_packetout (h_os h)) as [[[r opo] os]|] eqn:EPO; [| rewrite prun_munr in H; discriminate H].
exists r, opo, os. split; [reflexivity|].
destruct (Z.eqb_spec r 1) as [R1|RN].
2:{ left. cbn [negb] in H. rewrite prun_ret in H. injection H as <- <-. split; [exact RN| split; reflexivity]. }
right. split; [exact R1|]. cbn [negb] in H.
destruct opo as [op|]; [| rewrite prun_munr in H; discriminate H].
exists op. split; [reflexivity|]. unfold pkt_cases.
fold (pk_sser (set_ogg h (h_oy h) os) os op) in H.
destruct ((pk_sser (set_ogg h (h_oy h) os) os op =? -1) || negb (os_serialno os =? pk_sser (set_ogg h (h_oy h) os) os op)) eqn:ES.
{ left. rewrite prun_ret in H. injection H as <- <-. split; [| split; reflexivity].
apply orb_true_iff in ES. destruct ES as [ES|ES]; [left; apply Z.eqb_eq; exact ES| right; apply negb_true_iff, Z.eqb_neq in ES; exact ES]. }
right. apply orb_false_iff in ES as (ES1 & ES2). apply Z.eqb_neq in ES1. apply negb_false_iff, Z.eqb_eq in ES2.
split; [exact ES1|]. split; [exact ES2|].
cbn [set_serialno set_ogg h_packet_count h_extra_headers h_bits h_st h_nframes h_speex_serialno h_eos] in H |- *.
rewrite prun_bind in H.
destruct (Z.eqb_spec (h_packet_count h) 0) as [P0|PN].
- left. split; [exact P0|]. cbn beta iota in H. rewrite prun_bind in H.
lazymatch type of H with context [prun (process_header ?x1 ?x2 ?x3 ?x4 ?x5 ?x6) q] =>
destruct (prun (process_header x1 x2 x3 x4 x5 x6) q) as [[ph q1]|] eqn:EPH; [| discriminate H] end.
exists ph, q1. split; [exact EPH|].
destruct ph as [h3|].
+ rewrite prun_ret in H. exact H.
+ pose proof (prun_cleanup_none (set_serialno (set_ogg h (h_oy h) os) (pk_sser (set_ogg h (h_oy h) os) os op)) q1 (PC0 P0)) as EC.
unfold hP_cleanup in EC. rewrite prun_bind, EC, prun_ret, prun_ret in H. injection H as <- <-. split; reflexivity.
- right. cbn beta iota in H. destruct (Z.leb_spec (h_packet_count h) (1 + h_extra_headers h)) as [LE|GT].
+ left. split; [exact PN|]. split; [exact LE|]. rewrite prun_ret in H. exact H.
+ right. split; [exact PN|]. split; [exact GT|]. rewrite prun_bind in H.
lazymatch type of H with context [prun (speex_bits_read_from ?x1 ?x2 ?x3 ?x4 ?x5 ?x6) q] =>
destruct (prun (speex_bits_read_from x1 x2 x3 x4 x5 x6) q) as [[b q1]|] eqn:ERF; [| discriminate H] end.
destruct (h_st h) as [d|] eqn:EST; [| rewrite prun_munr in H; discriminate H].
rewrite prun_bind in H.
lazymatch type of H with context [prun (decode_loop ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8) q1] =>
destruct (prun (decode_loop x1 x2 x3 x4 x5 x6 x7 x8) q1) as [[[st' b'] q2]|] eqn:EDL; [| discriminate H] end.
rewrite prun_ret in H. cbn beta iota in H.
exists d, b, q1, st', b', q2. split; [reflexivity|]. split; [first [exact ERF| reflexivity]|]. split; [first [exact EDL| reflexivity]|].
replace (os_serialno os =? pk_sser (set_ogg h (h_oy h) os) os op) with true in H by (symmetry; apply Z.eqb_eq; exact ES2).
rewrite andb_true_r, E0 in H.
replace (if pk_e_o_s op =? 0 then 0 else 1) with (if negb (pk_e_o_s op =? 0) then 1 else 0) by (destruct (pk_e_o_s op =? 0); reflexivity).
exact H.
Qed.

Lemma gather255_eos : forall rest size eos bytes n n' eos' bytes', gather255 size rest eos bytes n = Some (n', eos', bytes') ->
0 <= eos < 1024 -> 0 <= eos' < 1024.
Proof.
induction rest as [|v rest IH]; intros size eos bytes n n' eos' bytes' H E; cbn [gather255] in H.
- destruct (size =? 255); [discriminate H| injection H as _ <- _; exact E].
- destruct (size =? 255); [| injection H as _ <- _; exact E].
apply (IH _ _ _ _ _ _ _ H). destruct (negb (Z.land v 512 =? 0)); lia.
Qed.

Lemma land512_bound : forall v, 0 <= Z.land v 512 < 1024.
Proof.
intros v.
assert (E1 : Z.land v 512 = Z.land (Z.land v (Z.ones 10)) 512) by (rewrite <- Z.land_assoc; reflexivity).
rewrite E1, Z.land_ones by lia. rewrite Z.land_comm.
pose proof (Z.mod_pos_bound v (2^10) ltac:(lia)).
exact (OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1ch.land_lt_pow2 512 (v mod 2^10) 10 ltac:(lia) ltac:(lia)).
Qed.

Lemma packetout_r_eos : forall (os os' : stream_st unit) r opo, ogg_stream_packetout os = Some ((r, opo), os') ->
(r = 0 \/ r = -1 \/ r = 1) /\ match opo with Some p => 0 <= pk_e_o_s p < 1024 | None => True end.
Proof.
intros os os' r opo H. unfold ogg_stream_packetout, packetout in H.
destruct (ogg_stream_check os); [injection H as <- <- _; split; [left; reflexivity| exact I]|].
destruct (_ <=? _); [injection H as <- <- _; split; [left; reflexivity| exact I]|].
destruct (negb _); [injection H as <- <- _; split; [right; left; reflexivity| exact I]|].
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|] eqn:EG; [| discriminate H].
injection H as <- <- _. split; [right; right; reflexivity|]. cbn [pk_e_o_s].
exact (gather255_eos _ _ _ _ _ _ _ _ EG (land512_bound _)).
Qed.
End Pkt.
