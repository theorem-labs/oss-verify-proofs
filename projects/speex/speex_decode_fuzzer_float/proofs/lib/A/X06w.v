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
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X000 X04b X00c X07z X05o X05p X05s X05t
X0ae X09j X09u X09x X0af X0ah X09p X05l X05e X05c X071 X06v X06y X06u X06x.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12c X14x X0r0 X0ra X0qz X0v9 X0rb X0wl X0wm X110 X106 X10j X112 X10c X0wb X0w9 X0xn X0xq X0xm X0xp.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X112 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xp.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Definition STEREO_INIT24 : list byte := map (Z_to_bv 8) [0; 0; 128; 63; 0; 0; 0; 63; 0; 0; 128; 63; 0; 0; 128; 63; 0; 0; 0; 0; 0; 0; 0; 0].
Lemma stereo_init_ro : forall m, mem_inv bsegs m -> bytes_at bsegs m 0x232a0 STEREO_INIT24.
Proof.
intros m MI.
pose proof (ro_cells_image bsegs m 0x232a0 STEREO_INIT24 MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; intros X; discriminate X)) as [_ B].
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma hsh_acc_at : forall (m : mem) (F base o n : Z) (sh : list byte),
F mod 8 = 0 -> 0 <= F -> o mod 8 = 0 -> 0 <= base -> 8 * base <= o -> 0 <= n -> bytes_at bsegs m (shad F + base) sh ->
(Z.to_nat (o / 8 - base) + length (ushadow n) <= length sh)%nat ->
firstn (length (ushadow n)) (skipn (Z.to_nat (o / 8 - base)) sh) = ushadow n -> acc bsegs m (F + o) n.
Proof.
intros m F base o n sh F8 F0 O8 B0 OB N0 B L E.
assert (BO : base <= o / 8) by (apply Z.div_le_lower_bound; lia).
apply acc_ushadow; [rewrite Zplus_mod, F8, O8; reflexivity| lia| lia|].
rewrite (shad_aligned_add F o F8 ltac:(lia)).
pose proof (bytes_at_sub m (shad F + base) sh (Z.to_nat (o / 8 - base)) (length (ushadow n)) B L) as X.
rewrite E, Z2Nat.id in X by lia.
replace (shad F + o / 8) with (shad F + base + (o / 8 - base)) by lia. exact X.
Qed.

Lemma bits_fresh_ok : bits_ok bits_fresh.
Proof. unfold bits_ok, bits_pos. vm_compute. repeat split; try discriminate; try (left; reflexivity). Qed.
Lemma hpure_init : forall X, hpure X (h_init X).
Proof.
intros X. unfold hpure, h_consumed, h_pend, h_init. cbn [h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_skip_samples h_nframes h_eos h_channels
h_rate h_extra_headers h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
pose proof (ogg_sync_init_inv2 (ptr := unit)) as I2. pose proof (ogg_sync_init_inv (ptr := unit)) as I1.
pose proof bits_fresh_ok as BO.
assert (XS : 0 <= x_size X) by (unfold x_size; lia).
assert (BS : sb_buf_size bits_fresh = 2000) by reflexivity.
assert (BW : sb_owner bits_fresh = 1) by reflexivity.
split; [exact I2|]. split; [exact I1|]. split; [cbn; lia|]. split; [split; intros _; reflexivity|]. split; [exact BO|]. split; [exact BW|].
split; [rewrite BS; lia|].
cbn. repeat split; try lia; try (left; reflexivity).
Qed.

Ltac clear_stale_asta :=
lazymatch goal with |- realizes _ ?c _ =>
repeat match goal with H : ASTA _ _ _ _ ?c' |- _ => tryif constr_eq c c' then fail else clear H end
end.

Section Entry.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis SM8 : stack_malloc_contract RT 8.
Hypothesis SSF8 : set_shadow_contract RT 0xf8.
Hypothesis SS00 : set_shadow_contract RT 0.
Hypothesis MCPY : memcpy_icontract RT e_asan_memcpy.
Hypothesis BINIT : speex_bits_init_cps RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.

Definition h_entry_pre (Σ : rts RT) (ra sp gp tp s0 a0 a1 : word) (m : mem) (d : Z) (bs : list byte) (lo : Z) : Prop :=
a0 = Z_to_bv 64 d /\ a1 = Z_to_bv 64 (Z.of_nat (length bs)) /\ tp = Z_to_bv 64 0x638c98 /\ ra = Z_to_bv 64 0x96650
/\ 0 < d < 2^64 /\ Z.of_nat (length bs) < 2^26 /\ bytes_at bsegs m d bs
/\ ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ bs = [])
/\ rt_frames RT Σ = [] /\ (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n)
/\ Z.of_nat (length (rt_live RT Σ)) + H_LIVE <= LIVE_MAX /\ FUZZ_COST <= rt_credit RT Σ
/\ (bv_unsigned s0 <= bv_unsigned sp - 16 \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0)
/\ ERR_rep m /\ io_ssp m /\ ART RT Σ m /\ mem_inv bsegs m
/\ stk bsegs m lo (bv_unsigned sp) /\ rt_sp0 RT Σ - STACK_WIN <= lo /\ lo + FUZZ_STACK <= bv_unsigned sp
/\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp <= rt_sp0 RT Σ.

Definition h_entry_X (X : hinv) (Σ : rts RT) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (d : Z) (bs : list byte) (lo : Z) : Prop :=
x_usp X = bv_unsigned sp /\ x_lo X = lo /\ x_gp X = gp /\ x_d X = d /\ x_bs X = bs /\ x_live X = rt_live RT Σ /\ x_sp0 X = rt_sp0 RT Σ
/\ x_cr0 X = rt_credit RT Σ /\ x_m0 X = m /\ x_ra X = ra /\ x_s0 X = s0 /\ x_s1 X = s1 /\ x_s2 X = s2 /\ x_s3 X = s3 /\ x_s4 X = s4 /\ x_s5 X = s5
/\ x_s6 X = s6 /\ x_s7 X = s7 /\ x_s8 X = s8 /\ x_s9 X = s9 /\ x_s10 X = s10 /\ x_s11 X = s11.

Theorem h_entry_ok : forall (Σ : rts RT) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
X1cn.frm0 fc -> h_entry_pre Σ ra sp gp tp s0 a0 a1 m d bs lo ->
cps bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fuzz m)))
(fun c => exists X, h_entry_X X Σ ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m d bs lo
/\ ((MAX_FUZZ_SIZE < Z.of_nat (length bs) /\ hep_ok X /\ at_EP RT OUT_rep ERR_rep IO_FP X F0 fs0 c)
\/ (Z.of_nat (length bs) <= MAX_FUZZ_SIZE /\ hinv_ok OUT_rep IO_FP X /\ at_CH RT OUT_rep ERR_rep IO_FP X F0 fs0 (h_init X) c))).
Proof using AF ERR_loc OUT_loc IO_img SM8 SSF8 SS00 MCPY BINIT AF_DRV.
intros Σ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo FRM HPRE.
destruct HPRE as (-> & -> & -> & -> & D0 & BSL & BY & PAY & FRM0 & LVP & LVR & CRE & S0C & ERR0 & SSP0 & ART0 & MI0 & ST0 & LOW & LOR & SPT & SPA & SP0L).
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc. unfold e_fuzz in Hc.
pose proof (PMfd_mat_stable F0 fs0) as MST. pose proof (PMfd_fdfs_only F0 fs0) as FDO.

pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [] m) as PF.

pose proof (conj BY (conj ERR0 SSP0)) as ENT0. clear BY ERR0 SSP0.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (fun E : rt_frames RT Σ = [] => af_pois_nil RT AF Σ m ART0 E) as PNIL.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.

assert (LGEO : forall p n, In (p, n) (rt_live RT Σ) -> p + n <= lo /\ (p + n <= SH_LO \/ SH_HI <= p) /\ (p + n <= 0x10000 \/ SEGTOP_A <= p)).
{ intros p n H. pose proof (af_live_range RT AF Σ m p n ART0 H) as (R0 & R1 & R2). pose proof (af_live_offshadow RT AF Σ m p n ART0 H) as OS.
split; [clear - R1 LOW; lia|]. split; [unfold SH_LO, SH_HI; lia| exact R2]. }

pose proof (PNIL FRM0) as PO0. assert (HFR0 : rt_frames RT Σ = [] /\ True) by (split; [exact FRM0| exact I]). clear FRM0 PNIL.
assert (SHLO : SH_HI <= lo).
{ pose proof (af_sp0_win RT AF Σ m ART0) as W0. unfold SH_HI, STACK_WIN in *. lia. }
cps_norm. unfold FUZZ_STACK in LOR.

Time cps_seg (hf_f0a usp lo).
destruct POST as (m1 & j1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
Time cps_seg_post.

remember (Z.land (usp + -352) 18446744073709551584) as S1 eqn:ES1.
assert (UR : 368 <= usp < 2^63) by (clear - SHLO LOR SPT; lia).
destruct (h_rechunk m1 lo usp S1 j1 _ ES1 UR SPA ltac:(clear - LOR; lia) ST1 FR1 eq_refl) as ((S32 & SR) & w0 & w8 & w16 & w24 & w32 & w40 & w48 & w56 & w64 & w72 & w80 & w88 & w96 & w104 & w112 & w120 & w128 & w136 & w144 & w152 & w160 & w168 & w176 & w184 & w192 & w200 & w208 & w216 & w224 & w232 & w240 & jg & ST & SPC & GAP & SV).
clear ST1 FR1.
pose proof (af_client_consts RT AF Σ m1 ART) as CC1. clear CC0.

Time cps_seg (hf_f0b usp S1).
{ clear - SHLO SR LOR; unfold IMG_TOP_B; lia. }
destruct POST as (m2 & -> & MU2 & WM2 & MI2 & SPC2).
clear SPC CC1.
Time cps_seg_post.

Time cps_rt_sized SM8 9280.
{ cbn. tauto. }
{ intros _. unfold HF_SIZE. split; [reflexivity|]. split; [reflexivity| change (fs_size 8) with 16384; lia]. }
{ rewrite (proj1 HFR0). cbn. unfold FRAMES_MAX. lia. }
{ clear - CRE. unfold FUZZ_COST in CRE. lia. }
{ cps_callok. }
intros cc2 (Σ1 & Ff & Hc2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP & PO1).
Time cps_unpack Hc2 as (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & WRF & WRS).
Time cps_new_frame ART3 FRS1 LV1 SP1 WRF WRS sf.

cb_cut FRB 24%nat FHDR. cb_cut FRB 8%nat FJ. clear FJ. cb_cut FRB 56%nat FENH. cb_cut FRB 40%nat FJ. clear FJ.
cb_cut FRB (4 * 2000)%nat FOUT. cb_cut FRB 256%nat FJ. clear FJ. cb_cut FRB 4%nat FFSZ. cb_cut FRB 12%nat FJ. clear FJ.
cb_cut FRB 48%nat FBITS. cb_cut FRB 32%nat FJ. clear FJ. cb_cut FRB 32%nat FOY. cb_cut FRB 32%nat FJ. clear FJ.
cb_cut FRB 32%nat FOG. cb_cut FRB 32%nat FJ. clear FJ. cb_cut FRB 48%nat FOP. cb_cut FRB 32%nat FJ. clear FJ.
cb_cut FRB 408%nat FOS. cb_cut FRB 72%nat FJ. clear FJ. cb_cut FRB 24%nat FST. cb_cut FRB 40%nat FJ. clear FJ.
cb_cut FRB 4%nat FRT. cb_cut FRB 12%nat FJ. clear FJ. cb_cut FRB 4%nat FLK. clear FRB.
cb_cut FRS 16%nat FSL. cb_cut FRS 1000%nat FSM. cb_cut FRS 144%nat FST8. clear FRS.
destruct (rw_cells_CB_f32 bsegs m3 (Ff + 128) 2000 j8 FOUT) as (ows & Lows & FOUT2). clear FOUT.
assert (FS1 : Ff + 16384 <= S1) by (clear - BF LOR SR; lia).
assert (SFS : sf + 2048 <= S1) by (clear - BF0 LOR SR; lia).

Time cps_seg (hf_f1 usp S1 Ff sf).
destruct POST as (m4 & -> & MU4 & WM4 & MI4 & SPC4 & HDR4).
clear SPC2 FHDR.
Time cps_seg_post.
clear WM1 WM2 WM3. clear_stale_asta.
cps_hide.

Time cps_seg (hf_p1 sf Ff).
destruct POST as (m5 & -> & MU5 & WM5 & MI5 & FSL5).
clear FSL.
Time cps_seg_post.
pose proof (proj2 FSM) as WFSM.
Time cps_rt (SSF8 Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (sf + 16) 1000 lo).
{ cbn. tauto. }
{ intros i Hi. exists Ff, 8%nat. split; [exact INF|]. rewrite <- SHF. change (fs_size 8) with 16384. rewrite SHF0. lia. }
{ cps_callok. }
intros cc6 (v6 & Hc6).
Time cps_unpack Hc6 as (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & BY6).
pose proof (ogg_ms_piece m5 m6 (sf + 16) 1000 (Z_to_bv 8 248) WFSM WM6 BY6) as FSM6. clear WFSM BY6.

Time cps_seg (hf_p2 sf Ff).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & FST87).
clear FST8.
Time cps_seg_post.
pose proof (proj2 FSM6) as WFSM.
Time cps_rt (SS00 Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 (sf + 16) 1000 lo).
{ cbn. tauto. }
{ intros i Hi. exists Ff, 8%nat. split; [exact INF|]. rewrite <- SHF. change (fs_size 8) with 16384. rewrite SHF0. lia. }
{ cps_callok. }
intros cc8 (v8 & Hc8).
Time cps_unpack Hc8 as (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & BY8).
pose proof (ogg_ms_piece m7 m8 (sf + 16) 1000 (Z_to_bv 8 0) WFSM WM8 BY8) as FSM8. clear WFSM BY8.
clear PRES3 PRES6 PRES8. clear_stale_asta.
lazymatch goal with H : ASTA _ _ _ _ _ |- _ => replace (Ff + 8384 + 784) with (Ff + 9168) in H by lia end.

Time cps_seg (hf_p3 usp S1 sf Ff).

destruct POST as (m9 & -> & MU9 & WM9 & MI9 & FST9 & FFSZ9 & SPC9).
clear FST87 FFSZ SPC4.
Time cps_seg_post.

pose proof (stereo_init_ro m9 MI9) as SRC.
pose proof (proj2 FST) as WST.
assert (ACST : acc bsegs m9 (Ff + 9168) 24).
{ destruct FST9 as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. rewrite SHF in B.
apply (hsh_acc_at m9 Ff 1016 9168 24 HSH_P3); [clear - F64; Z.div_mod_to_equations; lia| lia| reflexivity| lia| lia| lia| exact B| vm_compute; lia| vm_compute; reflexivity]. }
pose proof (af_acc_lits RT AF Σ1 m9 ART) as LITS.
assert (ACSRC : acc bsegs m9 0x232a0 24) by (rewrite Forall_forall in LITS; apply (LITS (0x232a0, 24)); unfold ACC_LITS; cbn [In]; left; reflexivity).
clear LITS.
Time cps_rt (MCPY Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m9 (Ff + 9168) 0x232a0 STEREO_INIT24 lo).

{ cbn [length STEREO_INIT24 map]. change (Z.of_nat 24) with 24. split; [intros _; split; [exact ACSRC| right; right; right; unfold SEGTOP_A; lia]|].
left. clear - SHLO. unfold SH_HI in SHLO. lia. }
{ cbn [length STEREO_INIT24 map]. change (Z.of_nat 24) with 24.
apply (frame_checked_dst RT Σ1 m9 (Z64 S1) Ff 8%nat (Ff + 9168) 24 INF ltac:(lia) ltac:(change (fs_size 8) with 16384; lia) ACST).
cbn [cells_size csize Nat.add] in WST. exact WST. }
{ right. cbn [length STEREO_INIT24 map]. change (Z.of_nat 24) with 24. clear - FIMG. unfold SEGTOP_A in FIMG. lia. }
{ cps_callok. }
intros cc10 Hc10. change (Z.of_nat (length STEREO_INIT24)) with 24 in Hc10.
Time cps_unpack Hc10 as (m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & BY10).
pose proof (ogg_bytes_piece m9 m10 (Ff + 9168) STEREO_INIT24 WST WM10 BY10) as FST10. cbn [length STEREO_INIT24 map] in FST10. clear WST BY10 ACST ACSRC. try clear SRC.

clear_stale_asta.
destruct (Z_lt_le_dec MAX_FUZZ_SIZE (Z.of_nat (length bs))) as [BIG | SMALL].
-
Time cps_seg (hf_p4b usp S1 sf Ff (Z.of_nat (length bs))).
{ unfold MAX_FUZZ_SIZE in BIG. clear - BIG BSL. lia. }

destruct POST as (m11 & -> & MU11 & WM11 & MI11 & FST11 & FRT11 & SPC11).
clear FST9 FRT SPC9.
Time cps_seg_post.
clear_stale_asta.

chunk_uncons HDR4 as HDR0. clear HDR4.
assert (ERR11 : ERR_rep m11).
{ destruct ENT0 as (_ & E0 & _). apply (ERR_loc m m11 E0). intros a Ha. apply PF; [| exact I].
right; left. exact (IO_img _ Ha). }
assert (OUT11 : forall so, OUT_rep so m -> OUT_rep so m11).
{ intros so Hso. apply (OUT_loc so m m11 Hso). intros a Ha. apply PF; [| exact I]. right; left. exact (IO_img _ Ha). }
apply Hk. exists (HI usp S1 lo gp Ff d bs (rt_live RT Σ) (rt_sp0 RT Σ) (rt_credit RT Σ) m m11 (Z64 0x96650) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
split; [unfold h_entry_X; cbn; repeat split; reflexivity|].
left. split; [exact BIG|]. split.
{ unfold hep_ok; cbn [x_usp x_S1 x_lo x_sp0 x_F]. change (fs_size 8) with 16384. cps_unf. unfold hid in FHI.
split; [exact SPA|]. split; [clear - LOR SHLO; lia|]. split; [clear - SPT; lia|]. split; [exact S32|]. split; [exact SR|].
split; [rewrite <- SP1; exact LOW|]. split; [clear - LOR SR; lia|]. split; [exact SHLO|]. split; [exact FPOS|]. split; [exact F64|].
split; [exact BF|]. destruct FHI as [H|H]; [left; lia| right; lia]. }

unfold at_EP. cbn [x_usp x_S1 x_lo x_gp x_F x_d x_bs x_live x_sp0 x_cr0 x_m0 x_mR x_ra x_s0 x_s1 x_s2 x_s3 x_s4 x_s5 x_s6 x_s7 x_s8 x_s9 x_s10 x_s11 x_sf].
exists Σ1, F, fc, m11. do 56 eexists.
split; [exact Hc|].
split; [exact FRM|].
split; [exact LV1|]. split; [rewrite FRS1, (proj1 HFR0); reflexivity|]. split; [exact SP1|]. split; [rewrite PO1; exact PO0|].
split; [rewrite CR1; unfold FUZZ_COST; clear; lia|].
split; [exact ART|]. split; [exact MI11|]. split; [exact ST10|].
split; [exact FST11|]. split; [exact FSM8|]. split; [exact HDR0|]. split; [exact SPC11|]. split; [exact GAP|]. split; [exact SV|].
split; [rewrite (proj1 HFR0) in PF; apply (pres_fp_weaken _ _ _ [] IO_FP m m11 PF); intros; exact I|].
split; [rewrite (proj1 HFR0) in NAF; exact NAF|].
split; [exact ERR11| exact OUT11].
-
Time cps_seg (hf_p4 usp S1 sf Ff (Z.of_nat (length bs))).
{ unfold MAX_FUZZ_SIZE in SMALL. lia. }

destruct POST as (m12 & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MU12 & WM12 & MI12 & FST12 & FRT12 & OY12 & SPC12).
clear FST9 FRT FOY SPC9.
Time cps_seg_post.
clear_stale_asta.
destruct OY12 as (OYC & OYF & OYD & OYS). unfold sync_cells in OYC.

assert (BSH : ro_cells bsegs m12 (shad (Ff + 8400)) bits_shadow).
{ destruct FST12 as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
pose proof (bytes_at_sub m12 (sf + 1016) HSH_T 34 6 B ltac:(vm_compute; lia)) as B6.
assert (E6 : firstn 6 (skipn 34 HSH_T) = repeat (Z_to_bv 8 0) 6) by (vm_compute; reflexivity).
rewrite E6 in B6. replace (sf + 1016 + Z.of_nat 34) with (sf + 1050) in B6 by (change (Z.of_nat 34) with 34; lia).
assert (ESB : shad (Ff + 8400) = sf + 1050)
by (rewrite (shad_aligned_add Ff 8400 ltac:(clear - F64; Z.div_mod_to_equations; lia) ltac:(lia)), <- SHF; change (8400 / 8) with 1050; reflexivity).
rewrite ESB. unfold bits_shadow. split; [cbn; tauto|]. cbn [cells_bytes cbytes map repeat app]. exact B6. }

Time cps_rt (BINIT Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m12 (Ff + 8400) Ff lo 8%nat j16).

{ change (fs_size 8) with 16384. lia. }
{ rewrite LV1. clear - LVR. unfold H_LIVE, LIVE_MAX in *. lia. }
{ rewrite CR1. clear - CRE. unfold FUZZ_COST in CRE. lia. }
{ rewrite unsigned_lit by (clear - SR SPT UR; lia). exact ST10. }
{ rewrite unsigned_lit by (clear - SR SPT UR; lia). clear - LOR SR. unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (clear - SR SPT UR; lia). clear - SR SPT. unfold USTACK_TOP. lia. }
{ rewrite unsigned_lit by (clear - SR SPT UR; lia). clear - S32. Z.div_mod_to_equations. lia. }
intros cc13 (Σ2 & Dc & Hc13 & LV2 & FRS2 & SP2 & CR2 & PO2).
Time cps_unpack_lib Hc13 as (v13 & m13 & RS13 & (ART13 & MI13 & WM13 & ST13) & PRES13 & BREP13 & BSH13).
clear FBITS BSH.
Time cps_tr_lib PRES13.
assert (PF13 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [] m m13).
{ apply (pres_fp_trans _ _ _ _ m m12 m13 PF). apply (pres_fp_of_pres_fp _ _ _ [] _ _ _ _ m12 m13 PRES13).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- clear - SR. lia.
- intros x Hx _. cbn [outside]. destruct (NAF x Hx) as (N1 & _). split; [| exact I]. intros Hin. apply N1. lia. }
clear PF. rename PF13 into PF.
clear_stale_asta.

cps_sigma LV2 FRS2 SP2.
destruct BREP13 as ((rjb & Lrjb & BOBJ) & (bsb & BDAT & Hbsb) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB m13 Dc bsb)) in BDAT.
assert (LBSB : length bsb = 2000%nat) by (apply (f_equal (@length Z)) in Hbsb; rewrite length_map in Hbsb; rewrite <- Hbsb; vm_compute; reflexivity).
rewrite LBSB in BDAT.
destruct (live_below_lo RT AF Σ2 m13 Dc 2000 lo ART13 INL LOW) as (DC0 & DCLO & _).
clear BSH13.

Time cps_seg (hf_p5 usp S1 sf Ff (Z.of_nat (length bs))).
destruct POST as (m14 & -> & MU14 & WM14 & MI14 & SPC14).
clear SPC12.
Time cps_seg_post.
clear_stale_asta.

apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FOG; [| reflexivity]. cbn [mk_CB_cells app] in FOG.
apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FOP; [| reflexivity]. cbn [mk_CB_cells app] in FOP.
destruct (rw_cells_CB_f32 bsegs m14 (Ff + 9248) 1 j44 FLK) as (wls & Lwls & FLK1). clear FLK.
destruct wls as [|wl [|? ?]]; try discriminate Lwls. clear Lwls.

rewrite (proj1 HFR0) in PF, NAF.
destruct ENT0 as (BY0 & ERR0 & (g & _ & SSPG)).
assert (ERR14 : ERR_rep m14).
{ apply (ERR_loc m m14 ERR0). intros a Ha. apply PF; [| exact I]. right; left. exact (IO_img _ Ha). }
assert (SSP14 : io_ssp m14).
{ exists g. split; [exact (proj1 (proj2 (AF_DRV _ _ ART)))|].
apply (ro_cells_agree bsegs m m14 _ _ SSPG). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply PF; [| exact I].
right; left. apply client_static_intro. clear - Ha. lia. }
assert (BY14 : bytes_at bsegs m14 d bs).
{ destruct PAY as [(p & n & INP & P1 & P2) | ->]; [| apply bytes_at_nil; clear - D0; lia ].
apply (bytes_at_agree bsegs m m14 d bs BY0). intros a Ha. apply PF; [| exact I].
right; right; left. exists p, n. split; [exact INP| lia]. }

apply Hk. exists (HI usp S1 lo gp Ff d bs (rt_live RT Σ) (rt_sp0 RT Σ) (rt_credit RT Σ) m m14 (Z64 0x96650) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
split; [unfold h_entry_X; cbn; repeat split; reflexivity|].
right. split; [exact SMALL|]. split.
{
unfold hid in FHI.
constructor; cbn [x_usp x_S1 x_lo x_gp x_F x_d x_bs x_live x_sp0 x_cr0 x_m0 x_mR x_ra x_s0 x_s1 x_s2 x_s3 x_s4 x_s5 x_s6 x_s7 x_s8 x_s9 x_s10 x_s11 x_sf x_size];
change (fs_size 8) with 16384; cps_unf.
- split; [exact SPA|]. split; lia.
- split; [exact ES1|]. split; [exact S32| exact SR].
- split; [rewrite <- SP1, <- SP2; exact LOW|]. split; [unfold H_STACK; lia| exact SHLO].
- split; [exact FPOS|]. split; [exact F64|]. split; [exact BF|]. split; [destruct FHI as [H|H]; [left; lia| right; lia]|]. clear - FIMG. lia.
- split; [exact D0|]. split; [exact SMALL|]. split; [exact BY14| exact PAY].
- split; [exact LVP| exact LVR].
- exact CRE.
- change (x_sf _) with sf.
assert (J : rw_cells bsegs m14 (sf + 16) ([CB 1000 (repeat (Z_to_bv 8 0) 1000)] ++ [CB 144 HSH_T])).
{ apply rw_cells_app. split; [exact FSM8|]. cbn [cells_size csize Nat.add]. match goal with |- rw_cells _ _ ?A0 _ => replace A0 with (sf + 1016) by lia end. exact FST12. }
apply h_rw_cells_to_CB in J. cbn [cells_size csize Nat.add cells_bytes cbytes app] in J. rewrite app_nil_r in J. exact J.
- exact HDR4.
- exact SV.
- exists jg. exact GAP.
- reflexivity.
- exact S0C.
- apply (pres_fp_weaken _ _ _ [] IO_FP m m14 PF). intros; exact I.
- intros so Hso. apply (OUT_loc so m m14 Hso). intros a Ha. apply PF; [| exact I]. right; left. exact (IO_img _ Ha).
- change (x_sf _) with sf. exact NAF.
- exact LGEO. }

unfold at_CH.
exists Σ2, (HA 0 [] 0 0 0 [] [] [] [] Dc 0 [] [(Dc, 2000)]), r69, r70, m14, (Z64 617660), r55, r56, r57, (Z64 (-1)), r58, r59, r60, r61, r62, r63, r64,
(Z64 (Ff + 8400)), (Z64 (Ff + 8688)), r65, r66, r67, r68, w40, w48, w56, (Z64 (Z.of_nat (length bs))), w224, w232.
do 2 eexists.
split; [unfold h_regs, x_size; cbn [h_init h_bytes_remaining h_stream_init h_packet_count h_eos h_channels a_S x_gp x_usp x_S1 x_F x_d x_bs]; exact Hc|].
split; [rewrite (proj2 RS13); exact FRM|].
split.
{ unfold hsig. cbn [a_P]. split; [rewrite LV2, LV1; reflexivity|]. split; [constructor; [intros []| constructor]|].
split; [unfold h_own; cbn [h_st h_bits h_stream_init h_os h_oy h_init a_Dc sy_data ogg_sync_init]; change (sb_buf_size bits_fresh) with 2000; cbn; apply Permutation_refl|].
split; [rewrite FRS2, FRS1, (proj1 HFR0); reflexivity|]. split; [rewrite SP2, SP1; reflexivity|]. split; [rewrite PO2, PO1; exact PO0|].
rewrite CR2, CR1. cbn [x_cr0]. unfold h_cost, H_HDR_CREDIT, H_DEC_CREDIT. cbn [h_packet_count h_init]. lia. }

split.
{ unfold hrep. cbn [x_usp x_S1 x_lo x_gp x_F x_d x_bs x_live x_sp0 x_cr0 x_m0 x_mR a_Dc a_Dsy a_sybytes].
split; [exact ART|]. split; [exact MI14|]. split; [exact ST13|]. split; [apply pres_fp_refl|].
split; [exact ERR14|]. split; [intros so Hso; exact Hso|]. split; [exact SSP14|].
split; [unfold h_spill; exact SPC14|].
split; [exact FSL5|].
split; [exists j4; exact FENH|].
split; [exists ows; split; [exact FOUT2| exact Lows]|].
split; [exact FFSZ9|].
split.
{ split; [exists rjb; split; [exact Lrjb| exact BOBJ]|]. split; [exists bsb; split; [apply (proj2 (u8arr_rw_CB m14 Dc bsb)); rewrite LBSB; exact BDAT| exact Hbsb]| exact BSIDE]. }
split.
{ split; [unfold sync_cells; exact OYC|]. split; [exact OYF|]. split; [cbn; repeat split; reflexivity| exact OYS]. }
split; [exact FOG|]. split; [exact FOP|].
split; [unfold h_os_rep; cbn [h_stream_init h_init h_os]; split; [exists j32; exact FOS| reflexivity]|].
split; [eexists; exact FST10|].
split; [exact FRT12|].
split; [exists (bv_unsigned wl); split; [rewrite Z_to_bv_bv_unsigned; exact FLK1| intros NS; exfalso; apply NS; reflexivity]|].
split; [unfold h_dec_rep; cbn [h_st h_init]; split; reflexivity|].
exact (hpure_init _). }
split; [do 4 eexists; reflexivity| do 6 eexists; reflexivity].
Qed.
End Entry.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Definition STEREO_INIT24 : list byte := map (Z_to_bv 8) [0; 0; 128; 63; 0; 0; 0; 63; 0; 0; 128; 63; 0; 0; 128; 63; 0; 0; 0; 0; 0; 0; 0; 0].
Lemma stereo_init_ro : forall m, mem_inv asegs m -> bytes_at asegs m 0x23260 STEREO_INIT24.
Proof.
intros m MI.
pose proof (ro_cells_image asegs m 0x23260 STEREO_INIT24 MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; intros X; discriminate X)) as [_ B].
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma hsh_acc_at : forall (m : mem) (F base o n : Z) (sh : list byte),
F mod 8 = 0 -> 0 <= F -> o mod 8 = 0 -> 0 <= base -> 8 * base <= o -> 0 <= n -> bytes_at asegs m (shad F + base) sh ->
(Z.to_nat (o / 8 - base) + length (ushadow n) <= length sh)%nat ->
firstn (length (ushadow n)) (skipn (Z.to_nat (o / 8 - base)) sh) = ushadow n -> acc asegs m (F + o) n.
Proof.
intros m F base o n sh F8 F0 O8 B0 OB N0 B L E.
assert (BO : base <= o / 8) by (apply Z.div_le_lower_bound; lia).
apply acc_ushadow; [rewrite Zplus_mod, F8, O8; reflexivity| lia| lia|].
rewrite (shad_aligned_add F o F8 ltac:(lia)).
pose proof (bytes_at_sub m (shad F + base) sh (Z.to_nat (o / 8 - base)) (length (ushadow n)) B L) as X.
rewrite E, Z2Nat.id in X by lia.
replace (shad F + o / 8) with (shad F + base + (o / 8 - base)) by lia. exact X.
Qed.

Lemma bits_fresh_ok : bits_ok bits_fresh.
Proof. unfold bits_ok, bits_pos. vm_compute. repeat split; try discriminate; try (left; reflexivity). Qed.
Lemma hpure_init : forall X, hpure X (h_init X).
Proof.
intros X. unfold hpure, h_consumed, h_pend, h_init. cbn [h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_skip_samples h_nframes h_eos h_channels
h_rate h_extra_headers h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
pose proof (ogg_sync_init_inv2 (ptr := unit)) as I2. pose proof (ogg_sync_init_inv (ptr := unit)) as I1.
pose proof bits_fresh_ok as BO.
assert (XS : 0 <= x_size X) by (unfold x_size; lia).
assert (BS : sb_buf_size bits_fresh = 2000) by reflexivity.
assert (BW : sb_owner bits_fresh = 1) by reflexivity.
split; [exact I2|]. split; [exact I1|]. split; [cbn; lia|]. split; [split; intros _; reflexivity|]. split; [exact BO|]. split; [exact BW|].
split; [rewrite BS; lia|].
cbn. repeat split; try lia; try (left; reflexivity).
Qed.

Ltac clear_stale_asta :=
lazymatch goal with |- realizes _ ?c _ =>
repeat match goal with H : ASTA _ _ _ _ ?c' |- _ => tryif constr_eq c c' then fail else clear H end
end.

Section Entry.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis SM8 : stack_malloc_contract RT 8.
Hypothesis SSF8 : set_shadow_contract RT 0xf8.
Hypothesis SS00 : set_shadow_contract RT 0.
Hypothesis MCPY : memcpy_icontract RT e_asan_memcpy.
Hypothesis BINIT : speex_bits_init_cps RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.

Definition h_entry_pre (Σ : rts RT) (ra sp gp tp s0 a0 a1 : word) (m : mem) (d : Z) (bs : list byte) (lo : Z) : Prop :=
a0 = Z_to_bv 64 d /\ a1 = Z_to_bv 64 (Z.of_nat (length bs)) /\ tp = Z_to_bv 64 0x630458 /\ ra = Z_to_bv 64 0x96564
/\ 0 < d < 2^64 /\ Z.of_nat (length bs) < 2^26 /\ bytes_at asegs m d bs
/\ ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ bs = [])
/\ rt_frames RT Σ = [] /\ (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n)
/\ Z.of_nat (length (rt_live RT Σ)) + H_LIVE <= LIVE_MAX /\ FUZZ_COST <= rt_credit RT Σ
/\ (bv_unsigned s0 <= bv_unsigned sp - 16 \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0)
/\ ERR_rep m /\ io_ssp m /\ ART RT Σ m /\ mem_inv asegs m
/\ stk asegs m lo (bv_unsigned sp) /\ rt_sp0 RT Σ - STACK_WIN <= lo /\ lo + FUZZ_STACK <= bv_unsigned sp
/\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp <= rt_sp0 RT Σ.

Definition h_entry_X (X : hinv) (Σ : rts RT) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (d : Z) (bs : list byte) (lo : Z) : Prop :=
x_usp X = bv_unsigned sp /\ x_lo X = lo /\ x_gp X = gp /\ x_d X = d /\ x_bs X = bs /\ x_live X = rt_live RT Σ /\ x_sp0 X = rt_sp0 RT Σ
/\ x_cr0 X = rt_credit RT Σ /\ x_m0 X = m /\ x_ra X = ra /\ x_s0 X = s0 /\ x_s1 X = s1 /\ x_s2 X = s2 /\ x_s3 X = s3 /\ x_s4 X = s4 /\ x_s5 X = s5
/\ x_s6 X = s6 /\ x_s7 X = s7 /\ x_s8 X = s8 /\ x_s9 X = s9 /\ x_s10 X = s10 /\ x_s11 X = s11.

Theorem h_entry_ok : forall (Σ : rts RT) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
X1cn.frm0 fc -> h_entry_pre Σ ra sp gp tp s0 a0 a1 m d bs lo ->
cps asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fuzz m)))
(fun c => exists X, h_entry_X X Σ ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m d bs lo
/\ ((MAX_FUZZ_SIZE < Z.of_nat (length bs) /\ hep_ok X /\ at_EP RT OUT_rep ERR_rep IO_FP X F0 fs0 c)
\/ (Z.of_nat (length bs) <= MAX_FUZZ_SIZE /\ hinv_ok OUT_rep IO_FP X /\ at_CH RT OUT_rep ERR_rep IO_FP X F0 fs0 (h_init X) c))).
Proof using AF ERR_loc OUT_loc IO_img SM8 SSF8 SS00 MCPY BINIT AF_DRV.
intros Σ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo FRM HPRE.
destruct HPRE as (-> & -> & -> & -> & D0 & BSL & BY & PAY & FRM0 & LVP & LVR & CRE & S0C & ERR0 & SSP0 & ART0 & MI0 & ST0 & LOW & LOR & SPT & SPA & SP0L).
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc. unfold e_fuzz in Hc.
pose proof (PMfd_mat_stable F0 fs0) as MST. pose proof (PMfd_fdfs_only F0 fs0) as FDO.

pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [] m) as PF.

pose proof (conj BY (conj ERR0 SSP0)) as ENT0. clear BY ERR0 SSP0.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (fun E : rt_frames RT Σ = [] => af_pois_nil RT AF Σ m ART0 E) as PNIL.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.

assert (LGEO : forall p n, In (p, n) (rt_live RT Σ) -> p + n <= lo /\ (p + n <= SH_LO \/ SH_HI <= p) /\ (p + n <= 0x10000 \/ SEGTOP_A <= p)).
{ intros p n H. pose proof (af_live_range RT AF Σ m p n ART0 H) as (R0 & R1 & R2). pose proof (af_live_offshadow RT AF Σ m p n ART0 H) as OS.
split; [clear - R1 LOW; lia|]. split; [unfold SH_LO, SH_HI; lia| exact R2]. }

pose proof (PNIL FRM0) as PO0. assert (HFR0 : rt_frames RT Σ = [] /\ True) by (split; [exact FRM0| exact I]). clear FRM0 PNIL.
assert (SHLO : SH_HI <= lo).
{ pose proof (af_sp0_win RT AF Σ m ART0) as W0. unfold SH_HI, STACK_WIN in *. lia. }
cps_norm. unfold FUZZ_STACK in LOR.

Time cps_seg (hf_f0a usp lo).
destruct POST as (m1 & j1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
Time cps_seg_post.

remember (Z.land (usp + -320) 18446744073709551584) as S1 eqn:ES1.
assert (UR : 336 <= usp < 2^63) by (clear - SHLO LOR SPT; lia).
destruct (h_rechunk m1 lo usp S1 j1 _ ES1 UR SPA ltac:(clear - LOR; lia) ST1 FR1 eq_refl) as ((S32 & SR) & w0 & w8 & w16 & w24 & w32 & w40 & w48 & w56 & w64 & w72 & w80 & w88 & w96 & w104 & w112 & w120 & w128 & w136 & w144 & w152 & w160 & w168 & w176 & w184 & w192 & w200 & w208 & jg & ST2 & SPC & GAP & SV).
clear ST1 FR1.
pose proof (af_client_consts RT AF Σ m1 ART) as CC1. clear CC0.

Time cps_seg (hf_f0b usp S1).
{ clear - SHLO SR LOR; unfold IMG_TOP; lia. }
destruct POST as (m2 & -> & MU2 & WM2 & MI2 & SPC2).
clear SPC CC1.
Time cps_seg_post.

Time cps_rt_sized SM8 9280.
{ cbn. tauto. }
{ intros _. unfold HF_SIZE. split; [reflexivity|]. split; [reflexivity| change (fs_size 8) with 16384; lia]. }
{ rewrite (proj1 HFR0). cbn. unfold FRAMES_MAX. lia. }
{ clear - CRE. unfold FUZZ_COST in CRE. lia. }
{ cps_callok. }
intros cc2 (Σ1 & Ff & Hc2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP & PO1).
Time cps_unpack Hc2 as (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & WRF & WRS).
Time cps_new_frame ART3 FRS1 LV1 SP1 WRF WRS sf.

cb_cut FRB 24%nat FHDR. cb_cut FRB 8%nat FJ. clear FJ. cb_cut FRB 56%nat FENH. cb_cut FRB 40%nat FJ. clear FJ.
cb_cut FRB (4 * 2000)%nat FOUT. cb_cut FRB 256%nat FJ. clear FJ. cb_cut FRB 4%nat FFSZ. cb_cut FRB 12%nat FJ. clear FJ.
cb_cut FRB 48%nat FBITS. cb_cut FRB 32%nat FJ. clear FJ. cb_cut FRB 32%nat FOY. cb_cut FRB 32%nat FJ. clear FJ.
cb_cut FRB 32%nat FOG. cb_cut FRB 32%nat FJ. clear FJ. cb_cut FRB 48%nat FOP. cb_cut FRB 32%nat FJ. clear FJ.
cb_cut FRB 408%nat FOS. cb_cut FRB 72%nat FJ. clear FJ. cb_cut FRB 24%nat FST. cb_cut FRB 40%nat FJ. clear FJ.
cb_cut FRB 4%nat FRT. cb_cut FRB 12%nat FJ. clear FJ. cb_cut FRB 4%nat FLK. clear FRB.
cb_cut FRS 16%nat FSL. cb_cut FRS 1000%nat FSM. cb_cut FRS 144%nat FST8. clear FRS.
destruct (rw_cells_CB_f32 asegs m3 (Ff + 128) 2000 j8 FOUT) as (ows & Lows & FOUT2). clear FOUT.
assert (FS1 : Ff + 16384 <= S1) by (clear - BF LOR SR; lia).
assert (SFS : sf + 2048 <= S1) by (clear - BF0 LOR SR; lia).

Time cps_seg (hf_f1 usp S1 Ff sf).
destruct POST as (m4 & -> & MU4 & WM4 & MI4 & SPC4 & HDR4).
clear SPC2 FHDR.
Time cps_seg_post.
clear WM1 WM2 WM3. clear_stale_asta.
cps_hide.

Time cps_seg (hf_p1 sf Ff).
destruct POST as (m5 & -> & MU5 & WM5 & MI5 & FSL5).
clear FSL.
Time cps_seg_post.
pose proof (proj2 FSM) as WFSM.
Time cps_rt (SSF8 Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (sf + 16) 1000 lo).
{ cbn. tauto. }
{ intros i Hi. exists Ff, 8%nat. split; [exact INF|]. rewrite <- SHF. change (fs_size 8) with 16384. rewrite SHF0. lia. }
{ cps_callok. }
intros cc6 (v6 & Hc6).
Time cps_unpack Hc6 as (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & BY6).
pose proof (ogg_ms_piece m5 m6 (sf + 16) 1000 (Z_to_bv 8 248) WFSM WM6 BY6) as FSM6. clear WFSM BY6.

Time cps_seg (hf_p2 sf Ff).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & FST87).
clear FST8.
Time cps_seg_post.
pose proof (proj2 FSM6) as WFSM.
Time cps_rt (SS00 Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 (sf + 16) 1000 lo).
{ cbn. tauto. }
{ intros i Hi. exists Ff, 8%nat. split; [exact INF|]. rewrite <- SHF. change (fs_size 8) with 16384. rewrite SHF0. lia. }
{ cps_callok. }
intros cc8 (v8 & Hc8).
Time cps_unpack Hc8 as (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & BY8).
pose proof (ogg_ms_piece m7 m8 (sf + 16) 1000 (Z_to_bv 8 0) WFSM WM8 BY8) as FSM8. clear WFSM BY8.
clear PRES3 PRES6 PRES8. clear_stale_asta.
lazymatch goal with H : ASTA _ _ _ _ _ |- _ => replace (Ff + 8384 + 784) with (Ff + 9168) in H by lia end.

Time cps_seg (hf_p3 usp S1 sf Ff).

destruct POST as (m9 & -> & MU9 & WM9 & MI9 & FST9 & FFSZ9 & SPC9).
clear FST87 FFSZ SPC4.
Time cps_seg_post.

pose proof (stereo_init_ro m9 MI9) as SRC.
pose proof (proj2 FST) as WST.
assert (ACST : acc asegs m9 (Ff + 9168) 24).
{ destruct FST9 as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. rewrite SHF in B.
apply (hsh_acc_at m9 Ff 1016 9168 24 HSH_P3); [clear - F64; Z.div_mod_to_equations; lia| lia| reflexivity| lia| lia| lia| exact B| vm_compute; lia| vm_compute; reflexivity]. }
pose proof (af_acc_lits RT AF Σ1 m9 ART) as LITS.
assert (ACSRC : acc asegs m9 0x23260 24) by (rewrite Forall_forall in LITS; apply (LITS (0x23260, 24)); unfold ACC_LITS; cbn [In]; left; reflexivity).
clear LITS.
Time cps_rt (MCPY Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m9 (Ff + 9168) 0x23260 STEREO_INIT24 lo).

{ cbn [length STEREO_INIT24 map]. change (Z.of_nat 24) with 24. split; [intros _; split; [exact ACSRC| right; right; right; unfold SEGTOP_A; lia]|].
left. clear - SHLO. unfold SH_HI in SHLO. lia. }
{ cbn [length STEREO_INIT24 map]. change (Z.of_nat 24) with 24.
apply (frame_checked_dst RT Σ1 m9 (Z64 S1) Ff 8%nat (Ff + 9168) 24 INF ltac:(lia) ltac:(change (fs_size 8) with 16384; lia) ACST).
cbn [cells_size csize Nat.add] in WST. exact WST. }
{ right. cbn [length STEREO_INIT24 map]. change (Z.of_nat 24) with 24. clear - FIMG. unfold SEGTOP_A in FIMG. lia. }
{ cps_callok. }
intros cc10 Hc10. change (Z.of_nat (length STEREO_INIT24)) with 24 in Hc10.
Time cps_unpack Hc10 as (m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & BY10).
pose proof (ogg_bytes_piece m9 m10 (Ff + 9168) STEREO_INIT24 WST WM10 BY10) as FST10. cbn [length STEREO_INIT24 map] in FST10. clear WST BY10 ACST ACSRC. try clear SRC.

clear_stale_asta.
destruct (Z_lt_le_dec MAX_FUZZ_SIZE (Z.of_nat (length bs))) as [BIG | SMALL].
-
Time cps_seg (hf_p4b usp S1 sf Ff (Z.of_nat (length bs))).
{ unfold MAX_FUZZ_SIZE in BIG. clear - BIG BSL. lia. }

destruct POST as (m11 & -> & MU11 & WM11 & MI11 & FST11 & FRT11).
clear FST9 FRT.
Time cps_seg_post.
clear_stale_asta.

chunk_uncons HDR4 as HDR0. clear HDR4.
assert (ERR11 : ERR_rep m11).
{ destruct ENT0 as (_ & E0 & _). apply (ERR_loc m m11 E0). intros a Ha. apply PF; [| exact I].
right; left. exact (IO_img _ Ha). }
assert (OUT11 : forall so, OUT_rep so m -> OUT_rep so m11).
{ intros so Hso. apply (OUT_loc so m m11 Hso). intros a Ha. apply PF; [| exact I]. right; left. exact (IO_img _ Ha). }
apply Hk. exists (HI usp S1 lo gp Ff d bs (rt_live RT Σ) (rt_sp0 RT Σ) (rt_credit RT Σ) m m11 (Z64 0x96564) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
split; [unfold h_entry_X; cbn; repeat split; reflexivity|].
left. split; [exact BIG|]. split.
{ unfold hep_ok; cbn [x_usp x_S1 x_lo x_sp0 x_F]. change (fs_size 8) with 16384. cps_unf. unfold hid in FHI.
split; [exact SPA|]. split; [clear - LOR SHLO; lia|]. split; [clear - SPT; lia|]. split; [exact S32|]. split; [exact SR|].
split; [rewrite <- SP1; exact LOW|]. split; [clear - LOR SR; lia|]. split; [exact SHLO|]. split; [exact FPOS|]. split; [exact F64|].
split; [exact BF|]. destruct FHI as [H|H]; [left; lia| right; lia]. }

unfold at_EP. cbn [x_usp x_S1 x_lo x_gp x_F x_d x_bs x_live x_sp0 x_cr0 x_m0 x_mR x_ra x_s0 x_s1 x_s2 x_s3 x_s4 x_s5 x_s6 x_s7 x_s8 x_s9 x_s10 x_s11 x_sf].
exists Σ1, F, fc, m11. do 52 eexists.
split; [exact Hc|].
split; [exact FRM|].
split; [exact LV1|]. split; [rewrite FRS1, (proj1 HFR0); reflexivity|]. split; [exact SP1|]. split; [rewrite PO1; exact PO0|].
split; [rewrite CR1; unfold FUZZ_COST; clear; lia|].
split; [exact ART|]. split; [exact MI11|]. split; [exact ST10|].
split; [exact FST11|]. split; [exact FSM8|]. split; [exact HDR0|]. split; [exact SPC9|]. split; [exact GAP|]. split; [exact SV|].
split; [rewrite (proj1 HFR0) in PF; apply (pres_fp_weaken _ _ _ [] IO_FP m m11 PF); intros; exact I|].
split; [rewrite (proj1 HFR0) in NAF; exact NAF|].
split; [exact ERR11| exact OUT11].
-
Time cps_seg (hf_p4 usp S1 sf Ff (Z.of_nat (length bs))).
{ unfold MAX_FUZZ_SIZE in SMALL. lia. }

destruct POST as (m12 & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MU12 & WM12 & MI12 & FST12 & FRT12 & OY12 & SPC12).
clear FST9 FRT FOY SPC9.
Time cps_seg_post.
clear_stale_asta.
destruct OY12 as (OYC & OYF & OYD & OYS). unfold sync_cells in OYC.

assert (BSH : ro_cells asegs m12 (shad (Ff + 8400)) bits_shadow).
{ destruct FST12 as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
pose proof (bytes_at_sub m12 (sf + 1016) HSH_T 34 6 B ltac:(vm_compute; lia)) as B6.
assert (E6 : firstn 6 (skipn 34 HSH_T) = repeat (Z_to_bv 8 0) 6) by (vm_compute; reflexivity).
rewrite E6 in B6. replace (sf + 1016 + Z.of_nat 34) with (sf + 1050) in B6 by (change (Z.of_nat 34) with 34; lia).
assert (ESB : shad (Ff + 8400) = sf + 1050)
by (rewrite (shad_aligned_add Ff 8400 ltac:(clear - F64; Z.div_mod_to_equations; lia) ltac:(lia)), <- SHF; change (8400 / 8) with 1050; reflexivity).
rewrite ESB. unfold bits_shadow. split; [cbn; tauto|]. cbn [cells_bytes cbytes map repeat app]. exact B6. }

Time cps_rt (BINIT Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m12 (Ff + 8400) Ff lo 8%nat j16).

{ change (fs_size 8) with 16384. lia. }
{ rewrite LV1. clear - LVR. unfold H_LIVE, LIVE_MAX in *. lia. }
{ rewrite CR1. clear - CRE. unfold FUZZ_COST in CRE. lia. }
{ rewrite unsigned_lit by (clear - SR SPT UR; lia). exact ST10. }
{ rewrite unsigned_lit by (clear - SR SPT UR; lia). clear - LOR SR. unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (clear - SR SPT UR; lia). clear - SR SPT. unfold USTACK_TOP. lia. }
{ rewrite unsigned_lit by (clear - SR SPT UR; lia). clear - S32. Z.div_mod_to_equations. lia. }
intros cc13 (Σ2 & Dc & Hc13 & LV2 & FRS2 & SP2 & CR2 & PO2).
Time cps_unpack_lib Hc13 as (v13 & m13 & RS13 & (ART13 & MI13 & WM13 & ST13) & PRES13 & BREP13 & BSH13).
clear FBITS BSH.
Time cps_tr_lib PRES13.
assert (PF13 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [] m m13).
{ apply (pres_fp_trans _ _ _ _ m m12 m13 PF). apply (pres_fp_of_pres_fp _ _ _ [] _ _ _ _ m12 m13 PRES13).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- clear - SR. lia.
- intros x Hx _. cbn [outside]. destruct (NAF x Hx) as (N1 & _). split; [| exact I]. intros Hin. apply N1. lia. }
clear PF. rename PF13 into PF.
clear_stale_asta.

cps_sigma LV2 FRS2 SP2.
destruct BREP13 as ((rjb & Lrjb & BOBJ) & (bsb & BDAT & Hbsb) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB m13 Dc bsb)) in BDAT.
assert (LBSB : length bsb = 2000%nat) by (apply (f_equal (@length Z)) in Hbsb; rewrite length_map in Hbsb; rewrite <- Hbsb; vm_compute; reflexivity).
rewrite LBSB in BDAT.
destruct (live_below_lo RT AF Σ2 m13 Dc 2000 lo ART13 INL LOW) as (DC0 & DCLO & _).
clear BSH13.

Time cps_seg (hf_p5 usp S1 sf Ff (Z.of_nat (length bs))).
destruct POST as (m14 & -> & MU14 & WM14 & MI14 & SPC14).
clear SPC12.
Time cps_seg_post.
clear_stale_asta.

apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FOG; [| reflexivity]. cbn [mk_CB_cells app] in FOG.
apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FOP; [| reflexivity]. cbn [mk_CB_cells app] in FOP.
destruct (rw_cells_CB_f32 asegs m14 (Ff + 9248) 1 j44 FLK) as (wls & Lwls & FLK1). clear FLK.
destruct wls as [|wl [|? ?]]; try discriminate Lwls. clear Lwls.

rewrite (proj1 HFR0) in PF, NAF.
destruct ENT0 as (BY0 & ERR0 & (g & _ & SSPG)).
assert (ERR14 : ERR_rep m14).
{ apply (ERR_loc m m14 ERR0). intros a Ha. apply PF; [| exact I]. right; left. exact (IO_img _ Ha). }
assert (SSP14 : io_ssp m14).
{ exists g. split; [exact (proj1 (proj2 (AF_DRV _ _ ART)))|].
apply (ro_cells_agree asegs m m14 _ _ SSPG). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply PF; [| exact I].
right; left. apply client_static_intro. clear - Ha. lia. }
assert (BY14 : bytes_at asegs m14 d bs).
{ destruct PAY as [(p & n & INP & P1 & P2) | ->]; [| apply bytes_at_nil; clear - D0; lia ].
apply (bytes_at_agree asegs m m14 d bs BY0). intros a Ha. apply PF; [| exact I].
right; right; left. exists p, n. split; [exact INP| lia]. }

apply Hk. exists (HI usp S1 lo gp Ff d bs (rt_live RT Σ) (rt_sp0 RT Σ) (rt_credit RT Σ) m m14 (Z64 0x96564) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
split; [unfold h_entry_X; cbn; repeat split; reflexivity|].
right. split; [exact SMALL|]. split.
{
unfold hid in FHI.
constructor; cbn [x_usp x_S1 x_lo x_gp x_F x_d x_bs x_live x_sp0 x_cr0 x_m0 x_mR x_ra x_s0 x_s1 x_s2 x_s3 x_s4 x_s5 x_s6 x_s7 x_s8 x_s9 x_s10 x_s11 x_sf x_size];
change (fs_size 8) with 16384; cps_unf.
- split; [exact SPA|]. split; lia.
- split; [exact ES1|]. split; [exact S32| exact SR].
- split; [rewrite <- SP1, <- SP2; exact LOW|]. split; [unfold H_STACK; lia| exact SHLO].
- split; [exact FPOS|]. split; [exact F64|]. split; [exact BF|]. split; [destruct FHI as [H|H]; [left; lia| right; lia]|]. clear - FIMG. lia.
- split; [exact D0|]. split; [exact SMALL|]. split; [exact BY14| exact PAY].
- split; [exact LVP| exact LVR].
- exact CRE.
- change (x_sf _) with sf.
assert (J : rw_cells asegs m14 (sf + 16) ([CB 1000 (repeat (Z_to_bv 8 0) 1000)] ++ [CB 144 HSH_T])).
{ apply rw_cells_app. split; [exact FSM8|]. cbn [cells_size csize Nat.add]. match goal with |- rw_cells _ _ ?A0 _ => replace A0 with (sf + 1016) by lia end. exact FST12. }
apply h_rw_cells_to_CB in J. cbn [cells_size csize Nat.add cells_bytes cbytes app] in J. rewrite app_nil_r in J. exact J.
- exact HDR4.
- exact SV.
- exists jg. exact GAP.
- reflexivity.
- exact S0C.
- apply (pres_fp_weaken _ _ _ [] IO_FP m m14 PF). intros; exact I.
- intros so Hso. apply (OUT_loc so m m14 Hso). intros a Ha. apply PF; [| exact I]. right; left. exact (IO_img _ Ha).
- change (x_sf _) with sf. exact NAF.
- exact LGEO. }

unfold at_CH.
exists Σ2, (HA 0 [] 0 0 0 [] [] [] [] Dc 0 [] [(Dc, 2000)]), r69, r70, m14, (Z64 617412), r55, r56, r57, (Z64 (-1)), r61, r62, r63, r64, (Z64 Ff), (Z64 (Ff + 64)),
r65, r66, r67, r68, w80, w88, w144, w176, w0, w192, w200.
do 2 eexists.
split; [unfold h_regs; cbn [h_init h_bytes_remaining h_last_granule h_speex_serialno h_stream_init h_packet_count a_S x_gp x_usp x_S1 x_F]; exact Hc|].
split; [rewrite (proj2 RS13); exact FRM|].
split.
{ unfold hsig. cbn [a_P]. split; [rewrite LV2, LV1; reflexivity|]. split; [constructor; [intros []| constructor]|].
split; [unfold h_own; cbn [h_st h_bits h_stream_init h_os h_oy h_init a_Dc sy_data ogg_sync_init]; change (sb_buf_size bits_fresh) with 2000; cbn; apply Permutation_refl|].
split; [rewrite FRS2, FRS1, (proj1 HFR0); reflexivity|]. split; [rewrite SP2, SP1; reflexivity|]. split; [rewrite PO2, PO1; exact PO0|].
rewrite CR2, CR1. cbn [x_cr0]. unfold h_cost, H_HDR_CREDIT, H_DEC_CREDIT. cbn [h_packet_count h_init]. lia. }

split.
{ unfold hrep. cbn [x_usp x_S1 x_lo x_gp x_F x_d x_bs x_live x_sp0 x_cr0 x_m0 x_mR a_Dc a_Dsy a_sybytes].
split; [exact ART|]. split; [exact MI14|]. split; [exact ST13|]. split; [apply pres_fp_refl|].
split; [exact ERR14|]. split; [intros so Hso; exact Hso|]. split; [exact SSP14|].
split; [unfold h_spill; exact SPC14|].
split; [exact FSL5|].
split; [exists j4; exact FENH|].
split; [exists ows; split; [exact FOUT2| exact Lows]|].
split; [exact FFSZ9|].
split.
{ split; [exists rjb; split; [exact Lrjb| exact BOBJ]|]. split; [exists bsb; split; [apply (proj2 (u8arr_rw_CB m14 Dc bsb)); rewrite LBSB; exact BDAT| exact Hbsb]| exact BSIDE]. }
split.
{ split; [unfold sync_cells; exact OYC|]. split; [exact OYF|]. split; [cbn; repeat split; reflexivity| exact OYS]. }
split; [exact FOG|]. split; [exact FOP|].
split; [unfold h_os_rep; cbn [h_stream_init h_init h_os]; split; [exists j32; exact FOS| reflexivity]|].
split; [eexists; exact FST10|].
split; [exact FRT12|].
split; [exists wl; exact FLK1|].
split; [unfold h_dec_rep; cbn [h_st h_init]; split; reflexivity|].
exact (hpure_init _). }
split; [do 4 eexists; reflexivity| do 6 eexists; reflexivity].
Qed.
End Entry.
