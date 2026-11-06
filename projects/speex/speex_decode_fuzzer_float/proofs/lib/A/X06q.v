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
X06u X073 X07j X072 X07h X06p X074.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12c X14x X0r0 X0ra X0qz X0v9 X0rb X0wl X0wm X110 X10c X10x X10t X108 X0xn X0xj X0xm X0xu X0ya X0xt X0y8 X0xh X0xv.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X108 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xj OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ya OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y8 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xh OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xv.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Lemma sbuf0_init : sync_buffer_res ogg_sync_init 0 = (None, ogg_sync_init).
Proof. reflexivity. Qed.
Lemma wrote0_init : ogg_sync_wrote (ogg_sync_init (ptr := unit)) 0 = (0, ogg_sync_init).
Proof. reflexivity. Qed.
Lemma pageout0_init : ogg_sync_pageout (ogg_sync_init (ptr := unit)) = Some ((0, None), ogg_sync_init).
Proof. vm_compute. reflexivity. Qed.

Section C0step.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Variable X : hinv.
Hypothesis HX : hinv_ok OUT_rep IO_FP X.
Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X). Local Notation sf := (x_sf X).

Lemma hrep_icpt0 : forall (Σ1 : rts RT) (m m' : mem) a (h : hstate unit) spill ogc opc d,
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 248%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
rt_after RT Σ1 S1 lo m m' -> rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) S1 d 0 m m' ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m' a h spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 m m' a h spill ogc opc d HS HR SPS OGS OPS (ART' & MI' & WM' & ST') PRX.
pose proof HS as (EL & ND & PERM & EF & _).
rewrite EF in PRX.
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (PR : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(F + 8688, F + 8688 + 408)] m m')
by (apply (pres_fp_of_ex _ _ _ d 0 _ m m' PRX); intros x Hx; exfalso; lia).
assert (PR0 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [] m m')
by (apply (pres_fp_of_ex _ _ _ d 0 _ m m' PRX); intros x Hx; exfalso; lia).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OSR & _ & _ & _ & _ & HP).
assert (OSR' : h_os_rep X m' a h).
{ apply (h_os_rep_tr _ _ _ _ m m' PR0 X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IB)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IL)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IG)); lia| apply rng_out_nil]. }
exact (hrep_os_step RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 Σ1 m m' a a h h spill ogc opc (rt_live RT Σ1) HS HR SPS OGS OPS ART' MI' ST'
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) ltac:(intros p q Hin _; exact (INL _ Hin)) PR OSR'
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HP).
Qed.

Lemma hrep_sbuf0 : forall (Σ1 Σ2 : rts RT) (m m' : mem) a (h : hstate unit) spill ogc opc D' bytes',
h_oy h = ogg_sync_init ->
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 248%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
rt_after_f RT Σ2 S1 lo m m' ->
rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) S1 [(F + 8480, F + 8480 + 32)] m m' ->
sync_rep m' (F + 8480) D' ogg_sync_init bytes' ->
rt_live RT Σ2 = rt_live RT Σ1 -> rt_frames RT Σ2 = rt_frames RT Σ1 -> rt_sp0 RT Σ2 = rt_sp0 RT Σ1 -> rt_credit RT Σ2 = rt_credit RT Σ1 ->
rt_pois RT Σ2 = rt_pois RT Σ1 ->
hsig RT X Σ2 (a_set_sync a D' bytes' (a_P a)) h /\ hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' (a_set_sync a D' bytes' (a_P a)) h spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 Σ2 m m' a h spill ogc opc D' bytes' EOY HS HR SPS OGS OPS (ART' & MI' & ST') PR SY' EL2 EF2 ES2 EC2 EP2.
destruct HR as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK & LKR) & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
rewrite EF in PR.
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (XL : forall e, In e (x_live X) -> In e (rt_live RT Σ1)) by (intros e He; rewrite EL; apply in_or_app; right; exact He).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.
assert (FRT : forall A cs, rw_cells bsegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 8480 \/ F + 8512 <= A) -> rw_cells bsegs m' A cs).
{ intros A cs C H1 H2 H3. apply (htr_rw _ _ _ _ m m' PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (ENH' : rw_cells bsegs m' (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (OUTB' : rw_cells bsegs m' (F + 128) (f32 ows)) by (apply (FRT _ _ OUTB); rewrite ?cells_size_f32, ?LOWS; lia).
assert (FSZ' : rw_cells bsegs m' (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells bsegs m' (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (OPC' : rw_cells bsegs m' (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (STB' : rw_cells bsegs m' (F + 9168) [CB 24 stb]) by (apply (FRT _ _ STB); cbn [cells_size csize Nat.add]; lia).
assert (RATE' : rw_cells bsegs m' (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells bsegs m' (F + 9248) [C4 (Z_to_bv 64 wl)]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OGC OPC STB RATE LOOK.
assert (SP' : rw_cells bsegs m' S1 spill).
{ apply (htr_rw _ _ _ _ m m' PR _ _ SP); rewrite SPS; [apply acl_stack; lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (LSH' : rw_cells bsegs m' sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m' PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (OWNTR : forall p q, In (p, q) (h_own a h) -> acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q /\ rng_out [(F + 8480, F + 8480 + 32)] p q).
{ intros p q Hin. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|]. apply rng_out_nil. }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep bsegs m' (F + 8400) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h)) as (D1 & D2).
apply (bits_rep_tr _ _ _ _ m m' PR _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (OSR' : h_os_rep X m' a h).
{ apply (h_os_rep_tr _ _ _ _ m m' PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (OWNTR _ _ IB) as (B1 & B2). destruct (OWNTR _ _ IL) as (L1 & L2). destruct (OWNTR _ _ IG) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
assert (DEC' : h_dec_rep X m' a h).
{ apply (h_dec_rep_tr _ _ _ _ m m' PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E); rewrite E in Hb; destruct Hb]).
exact (OWNTR _ _ (own_in_blk a h NS0 b Hb)). }
clear OSR DEC BITS OWNTR.
assert (FPH : fp_h X a h [(F + 8480, F + 8480 + 32)]) by (apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m' a h _ _ HSP PR XL FPH (AF_DRV _ _ ART') PF ERR OUTR SSP)
as (PF' & ERR' & OUTR' & SSP').
assert (EOWN : h_own (a_set_sync a D' bytes' (a_P a)) h = h_own a h).
{ unfold h_own. cbn [a_set_sync a_Dsy a_Dc a_Bd a_L a_G a_LBD]. rewrite EOY. reflexivity. }
split.
- unfold hsig. rewrite EOWN. cbn [a_set_sync a_P]. rewrite EL2, EF2, ES2, EP2, EC2.
split; [exact EL|]. split; [exact ND|]. split; [exact PERM|]. split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0| exact ECR].
- unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
cbn [a_set_sync a_Dc a_Dsy a_sybytes].
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [rewrite EOY; exact SY'|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [exact OSR'|]. split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; split; [exact LOOK'| first [exact LKR | (let HH := fresh in intros HH; apply LKR; congruence)]]|].
split; [exact DEC'| exact HP].
Qed.
End C0step.

Lemma ch_w1z : forall (S1 F brem : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
0 <= brem <= 4096 -> rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 (Z_to_bv 64 (F + 8480)) w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240) -> mem_inv bsegs m -> 0 <= S1 < 2^62 ->
evt bsegs (fun ms =>
ms = MS (mkR (Z_to_bv 64 0x96d20) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (F + 8480)) (Z_to_bv 64 (ch_nb brem)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (F + 8480)) s3 s4 s5 s6 (Z_to_bv 64 (ch_nb brem)) (Z_to_bv 64 brem) s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_ogg_sync_buffer_h) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 brem) s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_CH) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros BR SP MI S1R. unfold hsp in *. unfold A_CH, A_ogg_sync_buffer_h, ch_nb.
ato 0x96d08.
destruct (Z.ltb_spec 200 brem) as [LT|GE]; astep; sh_if.
- ato 0xc16b0. apply evt_done. reflexivity.
- ato 0xc16b0. try rewrite Z.add_0_r; try rewrite swrap32_small by lia. apply evt_done. reflexivity.
Qed.
Section Chunk0.
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

Theorem h_chunk0_ok : h_chunk0_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Proof using AF ERR_loc OUT_loc IO_img AF_DRV SBUF MCPY POUT.
intros HX SZ0 DLO T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & r2 & r7 & t3 & t4 & t5 & t6 & v40 & v48 & v56 & v88 & j224 & j232
& ogc & opc & Hc & FRM & HS & HR & OGJ & OPJ).
destruct OGJ as (g0 & g1 & g2 & g3 & ->). destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->).
set (h := h_init X) in *.
assert (EBR : h_bytes_remaining h = 0) by (unfold h, h_init; cbn [h_bytes_remaining]; exact SZ0).
assert (EOY : h_oy h = ogg_sync_init) by reflexivity.
assert (ENB : ch_nbr h = 0) by (unfold ch_nbr, CHUNK; rewrite EBR; reflexivity).
pose proof HR as HR'. destruct HR' as (_ & MI & _ & _ & _ & _ & _ & SP & _ & _ & _ & _ & _ & SY & _ & _ & _ & _ & _ & _ & _ & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
unfold h_regs in Hc. unfold h_spill in SP.
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).

refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply ch_w1z; [split; [rewrite EBR; lia| rewrite EBR; lia] | exact SP | exact MI | exact S1R]. }
intros ms1 c1 -> Hc1. clear Hc.

set (m1 := m) in *. clearbody m1. rename HR into HR1. rename MI into MI1. clear SP SY.
pose proof HR1 as HR'. destruct HR' as (ART1 & _ & ST1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SY1 & _).
change (ch_nb (h_bytes_remaining h)) with (ch_nbr h) in Hc1. rewrite ENB in Hc1.
assert (INF : In (x_F X, 8%nat) (rt_frames RT Σ1)) by (rewrite EF; left; reflexivity).
assert (SYL : sync_live RT Σ1 (h_oy h) (a_Dsy a)) by (rewrite EOY; intros NS; exfalso; exact (NS eq_refl)).
assert (LVR : Z.of_nat (length (rt_live RT Σ1)) < LIVE_MAX).
{ rewrite (h_live_len RT X Σ1 a h HS).
pose proof (h_own_len RT OUT_rep ERR_rep IO_FP X Σ1 m1 a h _ _ _ HR1) as L24.
pose proof (hi_live _ _ _ HX) as (_ & LL). unfold H_LIVE in LL. lia. }
unfold HO_OY in SY1. pose proof SY1 as (_ & FOK & _).
rewrite EOY in SY1, SYL.
Time cps_rt (SBUF Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (x_F X + 8480) (a_Dsy a) 0 (x_F X) (x_lo X) 8%nat
ogg_sync_init (a_sybytes a)).
{ apply PMfd_fdfs_only. } { apply PMfd_mat_stable. }
{ pose proof HP as (_ & SI & _). rewrite EOY in SI. exact SI. }
{ cbn. lia. } { cbn. lia. }
{ change (fs_size 8) with 16384. lia. }
{ exact (af_credit_nonneg RT AF Σ1 m1 ART1). }
{ rewrite unsigned_lit by lia. exact ST1. }
{ rewrite unsigned_lit by lia. unfold RT_STACK, H_STACK in *. lia. }
{ rewrite unsigned_lit by lia. unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by lia. clear - S32. Z.div_mod_to_equations. lia. }
intros c2 (Σ2 & D' & Hc2 & SL2 & CASE & EF2 & ES2 & EC2 & EP2). clear Hc1.
Time cps_unpack_lib Hc2 as (m2 & bytes2 & RS & RA2 & PR2 & SY2).
destruct RS as (-> & ->).
rewrite sbuf0_init in SY2. cbn [snd] in SY2.
assert (EL2 : rt_live RT Σ2 = rt_live RT Σ1) by (destruct CASE as [(_ & _ & E) | (LT & _)]; [exact E| exfalso; cbn in LT; lia]).
change (sync_rest_live ogg_sync_init (a_Dsy a) (rt_live RT Σ1)) with (rt_live RT Σ1) in PR2.
destruct (hrep_sbuf0 RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 Σ2 m1 m2 a h _ _ _ D' bytes2 EOY HS HR1
eq_refl eq_refl eq_refl RA2 PR2 SY2 EL2 EF2 ES2 EC2 EP2) as (HS2 & HR2).
pose proof SY2 as (_ & _ & DAT2 & _). cbn in DAT2. destruct DAT2 as (ED' & EB2 & _). subst D' bytes2.
clear HR1 SY1 PR2 SY2 RA2 ART1 ST1.
change (0 + sy_fill (sy_compact ogg_sync_init)) with 0 in Hc.
pose proof HR2 as HR'. destruct HR' as (ART2 & MI2 & ST2 & PF2 & _ & _ & _ & SP2 & _ & _ & _ & _ & _ & SY2 & _).

refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c2 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply ch_w2; [reflexivity | exact MI2]. }
intros ms3 c3 -> Hc3. clear Hc.
pose proof HS2 as (EL2' & ND2 & PERM2 & EF2' & ESP2 & EPO2 & ECR2).
pose proof (hi_pay _ _ _ HX) as (D0 & _).
Time cps_rt (MCPY Σ2 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 0 (x_d X) [] (x_lo X)).
{ apply PMfd_fdfs_only. } { apply PMfd_mat_stable. }
{ unfold USTACK_TOP, RT_STACK, H_STACK in *. lia. }
{ split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia. }
{ split; [cbn; intros C; lia| left; cbn; lia]. }
{ split; [cbn; intros C; lia|]. split; [cbn; intros i Hi; lia|]. split; [lia|]. split; [cbn; lia| intros i Hi; cbn in Hi; lia]. }
{ left. cbn. lia. }
{ unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST2|]. split; [rewrite ESP2; pose proof (hi_lo _ _ _ HX) as (LW0 & _); exact LW0|].
split; [unfold RT_STACK, H_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|]. clear - S32. Z.div_mod_to_equations. lia. }
intros c4 Hc4. clear Hc3.
unfold icpt_postF in Hc4.
Time cps_unpack_lib Hc4 as (m3 & RS3 & RA3 & PRX3 & _).
cps_ret RS3.
rewrite EF2' in PRX3.
pose proof (hrep_icpt0 RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ2 m2 m3 _ h _ _ _ 0 HS2 HR2 eq_refl eq_refl eq_refl RA3
ltac:(rewrite EF2'; exact PRX3)) as HR3.
clear HR2 PRX3 RA3 SP2 PF2 ST2 MI2 ART2.
pose proof HR3 as HR'. destruct HR' as (ART3 & MI3 & ST3 & PF3 & _ & _ & _ & SP3 & _ & _ & _ & _ & _ & SY3 & _).
cbn [a_set_sync a_Dsy a_sybytes] in SY3. unfold HO_OY in SY3. rewrite EOY in SY3.

refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c4 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply (ch_w3 (x_S1 X) (x_F X) 0 (h_bytes_remaining h) 0 ogg_sync_init []); [reflexivity | lia | lia | cbn; lia | lia | exact S1R | unfold RT_STACK, H_STACK in *; lia | left; cbn; lia | exact SY3 | exact SP3 | exact MI3]. }
intros ms5 c5 (m4 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & -> & MU4 & WM4 & MI4 & SY4 & SP4) Hc5. clear Hc.
replace (x_F X + 8512) with (x_F X + 8480 + 32) in MU4 by lia.
lazymatch type of SP4 with rw_cells _ _ _ ?sp' =>
destruct (hrep_wrote RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ2 m3 m4 _ h _ sp' _ _ 0 HS2 HR3
ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(rewrite EBR; lia) ltac:(rewrite EOY; vm_compute; discriminate)
ltac:(rewrite EOY; vm_compute; discriminate) MU4 WM4 MI4 SY4 SP4) as (HS4 & HR4) end.
clear HR3 SY3 SY4 SP3 SP4 MU4 WM4 ART3 ST3 MI3 PF3.

lazymatch type of HS4 with hsig _ _ _ _ ?h3 => assert (EH3 : h3 = ch_h1 X h) end.
{ unfold ch_h1. rewrite ENB. unfold h. cbn. rewrite SZ0. reflexivity. }
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

assert (ERP : rp = 0 /\ ogo = None).
{ assert (EOYc : h_oy hc = ogg_sync_init) by (unfold hc, ch_h1; rewrite ENB; unfold h; reflexivity).
rewrite EOYc, pageout0_init in EPO. injection EPO as <- <- _. split; reflexivity. }
destruct ERP as (-> & ->).

refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c6 (PMfd_mat_stable F0 fs0) Hc _ _).
{ unfold wz. eapply ch_w4; [reflexivity | lia | left; reflexivity | exact SP5 | exact MI5 | exact S1R]. }
intros ms7 c7 POST Hc7. clear Hc. cbv beta in POST.
apply Hk. exists 0, None, oy5. split; [exact EPO|].
destruct POST as [(E1 & _) | (NE & ->)]; [discriminate E1|].
right. split; [exact NE|].
exists Σ2, a3, Fx, fc, m5. do 19 eexists. exists v48, v56, v88, j224, j232, [CB 8 g0; CB 8 g1; CB 8 g2; CB 8 g3], [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
unfold hc in *. rewrite <- EH3 in HS5, HR5 |- *. rewrite ENB.
split; [unfold h_regs; cbn [set_ogg set_bytes_remaining h_stream_init h_packet_count h_channels h_eos]; exact Hc7|].
split; [exact FRM|]. split; [exact HS5|].
split; [unfold h_iter; cbn [set_ogg set_bytes_remaining h_bytes_remaining]; rewrite EBR; unfold CHUNK, x_size in *; lia|].
split; [exact HR5|]. split; [do 4 eexists; reflexivity| do 6 eexists; reflexivity].
Qed.
End Chunk0.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Lemma sbuf0_init : sync_buffer_res ogg_sync_init 0 = (None, ogg_sync_init).
Proof. reflexivity. Qed.
Lemma wrote0_init : ogg_sync_wrote (ogg_sync_init (ptr := unit)) 0 = (0, ogg_sync_init).
Proof. reflexivity. Qed.
Lemma pageout0_init : ogg_sync_pageout (ogg_sync_init (ptr := unit)) = Some ((0, None), ogg_sync_init).
Proof. vm_compute. reflexivity. Qed.

Section C0step.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Variable X : hinv.
Hypothesis HX : hinv_ok OUT_rep IO_FP X.
Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X). Local Notation sf := (x_sf X).

Lemma hrep_icpt0 : forall (Σ1 : rts RT) (m m' : mem) a (h : hstate unit) spill ogc opc d,
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 216%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
rt_after RT Σ1 S1 lo m m' -> rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) S1 d 0 m m' ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m' a h spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 m m' a h spill ogc opc d HS HR SPS OGS OPS (ART' & MI' & WM' & ST') PRX.
pose proof HS as (EL & ND & PERM & EF & _).
rewrite EF in PRX.
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (PR : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(F + 8688, F + 8688 + 408)] m m')
by (apply (pres_fp_of_ex _ _ _ d 0 _ m m' PRX); intros x Hx; exfalso; lia).
assert (PR0 : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [] m m')
by (apply (pres_fp_of_ex _ _ _ d 0 _ m m' PRX); intros x Hx; exfalso; lia).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OSR & _ & _ & _ & _ & HP).
assert (OSR' : h_os_rep X m' a h).
{ apply (h_os_rep_tr _ _ _ _ m m' PR0 X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IB)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IL)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IG)); lia| apply rng_out_nil]. }
exact (hrep_os_step RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 Σ1 m m' a a h h spill ogc opc (rt_live RT Σ1) HS HR SPS OGS OPS ART' MI' ST'
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) ltac:(intros p q Hin _; exact (INL _ Hin)) PR OSR'
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HP).
Qed.

Lemma hrep_sbuf0 : forall (Σ1 Σ2 : rts RT) (m m' : mem) a (h : hstate unit) spill ogc opc D' bytes',
h_oy h = ogg_sync_init ->
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 216%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
rt_after_f RT Σ2 S1 lo m m' ->
rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) S1 [(F + 8480, F + 8480 + 32)] m m' ->
sync_rep m' (F + 8480) D' ogg_sync_init bytes' ->
rt_live RT Σ2 = rt_live RT Σ1 -> rt_frames RT Σ2 = rt_frames RT Σ1 -> rt_sp0 RT Σ2 = rt_sp0 RT Σ1 -> rt_credit RT Σ2 = rt_credit RT Σ1 ->
rt_pois RT Σ2 = rt_pois RT Σ1 ->
hsig RT X Σ2 (a_set_sync a D' bytes' (a_P a)) h /\ hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' (a_set_sync a D' bytes' (a_P a)) h spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 Σ2 m m' a h spill ogc opc D' bytes' EOY HS HR SPS OGS OPS (ART' & MI' & ST') PR SY' EL2 EF2 ES2 EC2 EP2.
destruct HR as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK) & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
rewrite EF in PR.
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (XL : forall e, In e (x_live X) -> In e (rt_live RT Σ1)) by (intros e He; rewrite EL; apply in_or_app; right; exact He).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.
assert (FRT : forall A cs, rw_cells asegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 8480 \/ F + 8512 <= A) -> rw_cells asegs m' A cs).
{ intros A cs C H1 H2 H3. apply (htr_rw _ _ _ _ m m' PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (ENH' : rw_cells asegs m' (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (OUTB' : rw_cells asegs m' (F + 128) (f32 ows)) by (apply (FRT _ _ OUTB); rewrite ?cells_size_f32, ?LOWS; lia).
assert (FSZ' : rw_cells asegs m' (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells asegs m' (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (OPC' : rw_cells asegs m' (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (STB' : rw_cells asegs m' (F + 9168) [CB 24 stb]) by (apply (FRT _ _ STB); cbn [cells_size csize Nat.add]; lia).
assert (RATE' : rw_cells asegs m' (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells asegs m' (F + 9248) [C4 wl]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OGC OPC STB RATE LOOK.
assert (SP' : rw_cells asegs m' S1 spill).
{ apply (htr_rw _ _ _ _ m m' PR _ _ SP); rewrite SPS; [apply acl_stack; lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (LSH' : rw_cells asegs m' sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m' PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (OWNTR : forall p q, In (p, q) (h_own a h) -> acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q /\ rng_out [(F + 8480, F + 8480 + 32)] p q).
{ intros p q Hin. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|]. apply rng_out_nil. }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep asegs m' (F + 8400) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h)) as (D1 & D2).
apply (bits_rep_tr _ _ _ _ m m' PR _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (OSR' : h_os_rep X m' a h).
{ apply (h_os_rep_tr _ _ _ _ m m' PR X a h OSR).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- unfold HO_OS. apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (OWNTR _ _ IB) as (B1 & B2). destruct (OWNTR _ _ IL) as (L1 & L2). destruct (OWNTR _ _ IG) as (G1 & G2).
exact (conj B1 (conj B2 (conj L1 (conj L2 (conj G1 G2))))). }
assert (DEC' : h_dec_rep X m' a h).
{ apply (h_dec_rep_tr _ _ _ _ m m' PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E); rewrite E in Hb; destruct Hb]).
exact (OWNTR _ _ (own_in_blk a h NS0 b Hb)). }
clear OSR DEC BITS OWNTR.
assert (FPH : fp_h X a h [(F + 8480, F + 8480 + 32)]) by (apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m' a h _ _ HSP PR XL FPH (AF_DRV _ _ ART') PF ERR OUTR SSP)
as (PF' & ERR' & OUTR' & SSP').
assert (EOWN : h_own (a_set_sync a D' bytes' (a_P a)) h = h_own a h).
{ unfold h_own. cbn [a_set_sync a_Dsy a_Dc a_Bd a_L a_G a_LBD]. rewrite EOY. reflexivity. }
split.
- unfold hsig. rewrite EOWN. cbn [a_set_sync a_P]. rewrite EL2, EF2, ES2, EP2, EC2.
split; [exact EL|]. split; [exact ND|]. split; [exact PERM|]. split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0| exact ECR].
- unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
cbn [a_set_sync a_Dc a_Dsy a_sybytes].
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [rewrite EOY; exact SY'|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [exact OSR'|]. split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; exact LOOK'|].
split; [exact DEC'| exact HP].
Qed.
End C0step.

Lemma ch_w1z : forall (S1 F brem lastg sser : Z) (ra sp gp tp t0 t1 t2 s0 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
0 <= brem <= 4096 -> rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 (Z_to_bv 64 (F + 8480)) w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) -> mem_inv asegs m -> 0 <= S1 < 2^62 ->
evt asegs (fun ms => exists m1 : mem,
ms = MS (mkR (Z_to_bv 64 0x96c2c) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (F + 8480)) (Z_to_bv 64 (ch_nb brem)) (Z_to_bv 64 lastg) (Z_to_bv 64 sser) a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 (ch_nb brem)) s6 (Z_to_bv 64 (F + 8480)) s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_ogg_sync_buffer_h) fc None m1 (seg_rom asegs)
/\ munch [(S1, S1 + 216)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 (Z_to_bv 64 brem) w96 w104 w112 (Z_to_bv 64 (F + 8480)) w128 w136 (Z_to_bv 64 lastg) w152 w160 w168 (Z_to_bv 64 sser) w184 w192 w200 w208))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 brem) a1 (Z_to_bv 64 lastg) (Z_to_bv 64 sser) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_CH) fc None m (seg_rom asegs)).
Proof.
intros until m. intros BR SP MI S1R. unfold hsp in *. unfold A_CH, A_ogg_sync_buffer_h, ch_nb.
pose proof (munch_refl [(S1, S1 + 216)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0x96c14.
destruct (Z.ltb_spec 200 brem) as [LT|GE]; astep; sh_if.
- ato 0xb8f80. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SP].
- ato 0xb8f80. rewrite Z.add_0_r, swrap32_small by lia. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SP].
Qed.
Section Chunk0.
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

Theorem h_chunk0_ok : h_chunk0_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Proof using AF ERR_loc OUT_loc IO_img AF_DRV SBUF MCPY POUT.
intros HX SZ0 DLO T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a1 & a4 & a5 & a6 & a7 & r5 & r7 & t3 & t4 & t5 & t6 & v80 & v88 & v144 & v176 & j0 & j192 & j200
& ogc & opc & Hc & FRM & HS & HR & OGJ & OPJ).
destruct OGJ as (g0 & g1 & g2 & g3 & ->). destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->).
set (h := h_init X) in *.
assert (EBR : h_bytes_remaining h = 0) by (unfold h, h_init; cbn [h_bytes_remaining]; exact SZ0).
assert (EOY : h_oy h = ogg_sync_init) by reflexivity.
assert (ENB : ch_nbr h = 0) by (unfold ch_nbr, CHUNK; rewrite EBR; reflexivity).
pose proof HR as HR'. destruct HR' as (_ & MI & _ & _ & _ & _ & _ & SP & _ & _ & _ & _ & _ & SY & _ & _ & _ & _ & _ & _ & _ & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
unfold h_regs in Hc. unfold h_spill in SP.
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).

refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply ch_w1z; [split; [rewrite EBR; lia| rewrite EBR; lia] | exact SP | exact MI | exact S1R]. }
intros ms1 c1 (m1 & -> & MU1 & WM1 & MI1 & SP1) Hc1. clear Hc.
lazymatch type of SP1 with rw_cells _ _ _ ?sp' =>
pose proof (hrep_spill RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m1 a h _ sp' _ _ HS HR
ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) MU1 WM1 MI1 SP1) as HR1 end.
clear HR SP MI MU1 WM1 SY.
pose proof HR1 as HR'. destruct HR' as (ART1 & _ & ST1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SY1 & _).
change (ch_nb (h_bytes_remaining h)) with (ch_nbr h) in Hc1. rewrite ENB in Hc1.
assert (INF : In (x_F X, 8%nat) (rt_frames RT Σ1)) by (rewrite EF; left; reflexivity).
assert (SYL : sync_live RT Σ1 (h_oy h) (a_Dsy a)) by (rewrite EOY; intros NS; exfalso; exact (NS eq_refl)).
assert (LVR : Z.of_nat (length (rt_live RT Σ1)) < LIVE_MAX).
{ rewrite (h_live_len RT X Σ1 a h HS).
pose proof (h_own_len RT OUT_rep ERR_rep IO_FP X Σ1 m1 a h _ _ _ HR1) as L24.
pose proof (hi_live _ _ _ HX) as (_ & LL). unfold H_LIVE in LL. lia. }
unfold HO_OY in SY1. pose proof SY1 as (_ & FOK & _).
rewrite EOY in SY1, SYL.
Time cps_rt (SBUF Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (x_F X + 8480) (a_Dsy a) 0 (x_F X) (x_lo X) 8%nat
ogg_sync_init (a_sybytes a)).
{ apply PMfd_fdfs_only. } { apply PMfd_mat_stable. }
{ pose proof HP as (_ & SI & _). rewrite EOY in SI. exact SI. }
{ cbn. lia. } { cbn. lia. }
{ change (fs_size 8) with 16384. lia. }
{ exact (af_credit_nonneg RT AF Σ1 m1 ART1). }
{ rewrite unsigned_lit by lia. exact ST1. }
{ rewrite unsigned_lit by lia. unfold RT_STACK, H_STACK in *. lia. }
{ rewrite unsigned_lit by lia. unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by lia. clear - S32. Z.div_mod_to_equations. lia. }
intros c2 (Σ2 & D' & Hc2 & SL2 & CASE & EF2 & ES2 & EC2 & EP2). clear Hc1.
Time cps_unpack_lib Hc2 as (m2 & bytes2 & RS & RA2 & PR2 & SY2).
destruct RS as (-> & ->).
rewrite sbuf0_init in SY2. cbn [snd] in SY2.
assert (EL2 : rt_live RT Σ2 = rt_live RT Σ1) by (destruct CASE as [(_ & _ & E) | (LT & _)]; [exact E| exfalso; cbn in LT; lia]).
change (sync_rest_live ogg_sync_init (a_Dsy a) (rt_live RT Σ1)) with (rt_live RT Σ1) in PR2.
destruct (hrep_sbuf0 RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 Σ2 m1 m2 a h _ _ _ D' bytes2 EOY HS HR1
eq_refl eq_refl eq_refl RA2 PR2 SY2 EL2 EF2 ES2 EC2 EP2) as (HS2 & HR2).
pose proof SY2 as (_ & _ & DAT2 & _). cbn in DAT2. destruct DAT2 as (ED' & EB2 & _). subst D' bytes2.
clear HR1 SY1 PR2 SY2 RA2 ART1 ST1.
change (0 + sy_fill (sy_compact ogg_sync_init)) with 0 in Hc.
pose proof HR2 as HR'. destruct HR' as (ART2 & MI2 & ST2 & PF2 & _ & _ & _ & SP2 & _ & _ & _ & _ & _ & SY2 & _).

refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c2 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply ch_w2; [reflexivity | exact SP2 | exact MI2 | exact S1R]. }
intros ms3 c3 -> Hc3. clear Hc.
pose proof HS2 as (EL2' & ND2 & PERM2 & EF2' & ESP2 & EPO2 & ECR2).
pose proof (hi_pay _ _ _ HX) as (D0 & _).
Time cps_rt (MCPY Σ2 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 0 (x_d X) [] (x_lo X)).
{ apply PMfd_fdfs_only. } { apply PMfd_mat_stable. }
{ unfold USTACK_TOP, RT_STACK, H_STACK in *. lia. }
{ split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia. }
{ split; [cbn; intros C; lia| left; cbn; lia]. }
{ split; [cbn; intros C; lia|]. split; [cbn; intros i Hi; lia|]. split; [lia|]. split; [cbn; lia| intros i Hi; cbn in Hi; lia]. }
{ left. cbn. lia. }
{ unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST2|]. split; [rewrite ESP2; pose proof (hi_lo _ _ _ HX) as (LW0 & _); exact LW0|].
split; [unfold RT_STACK, H_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|]. clear - S32. Z.div_mod_to_equations. lia. }
intros c4 Hc4. clear Hc3.
unfold icpt_postF in Hc4.
Time cps_unpack_lib Hc4 as (m3 & RS3 & RA3 & PRX3 & _).
cps_ret RS3.
rewrite EF2' in PRX3.
pose proof (hrep_icpt0 RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ2 m2 m3 _ h _ _ _ 0 HS2 HR2 eq_refl eq_refl eq_refl RA3
ltac:(rewrite EF2'; exact PRX3)) as HR3.
clear HR2 PRX3 RA3 SP2 PF2 ST2 MI2 ART2.
pose proof HR3 as HR'. destruct HR' as (ART3 & MI3 & ST3 & PF3 & _ & _ & _ & SP3 & _ & _ & _ & _ & _ & SY3 & _).
cbn [a_set_sync a_Dsy a_sybytes] in SY3. unfold HO_OY in SY3. rewrite EOY in SY3.

refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c4 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply (ch_w3 (x_S1 X) (x_F X) 0 0 ogg_sync_init []); [reflexivity | lia | cbn; lia | lia | exact S1R | unfold RT_STACK, H_STACK in *; lia | left; cbn; lia | exact SY3 | exact SP3 | exact MI3]. }
intros ms5 c5 (m4 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & -> & MU4 & WM4 & MI4 & SY4 & SP4) Hc5. clear Hc.
replace (x_F X + 8512) with (x_F X + 8480 + 32) in MU4 by lia.
lazymatch type of SP4 with rw_cells _ _ _ ?sp' =>
destruct (hrep_wrote RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ2 m3 m4 _ h _ sp' _ _ 0 HS2 HR3
ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(rewrite EBR; lia) ltac:(rewrite EOY; vm_compute; discriminate)
ltac:(rewrite EOY; vm_compute; discriminate) MU4 WM4 MI4 SY4 SP4) as (HS4 & HR4) end.
clear HR3 SY3 SY4 SP3 SP4 MU4 WM4 ART3 ST3 MI3 PF3.

lazymatch type of HS4 with hsig _ _ _ _ ?h3 => assert (EH3 : h3 = ch_h1 X h) end.
{ unfold ch_h1. rewrite ENB. unfold h. cbn. rewrite SZ0. reflexivity. }
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

assert (ERP : rp = 0 /\ ogo = None).
{ assert (EOYc : h_oy hc = ogg_sync_init) by (unfold hc, ch_h1; rewrite ENB; unfold h; reflexivity).
rewrite EOYc, pageout0_init in EPO. injection EPO as <- <- _. split; reflexivity. }
destruct ERP as (-> & ->).

refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T c6 (PMfd_mat_stable F0 fs0) Hc _ _).
{ unfold wz. eapply ch_w4; [reflexivity | lia | left; reflexivity | exact SP5 | exact MI5 | exact S1R]. }
intros ms7 c7 POST Hc7. clear Hc. cbv beta in POST.
apply Hk. exists 0, None, oy5. split; [exact EPO|].
destruct POST as [(E1 & _) | (NE & ->)]; [discriminate E1|].
right. split; [exact NE|].
exists Σ2, a3, Fx, fc, m5, (Z64 617556), r29, r30, r31, (Z64 0), (Z64 1), r34, r35, r36, r37, r38, (Z64 0), r39, r40, r41, r42,
j0, j192, j200, [CB 8 g0; CB 8 g1; CB 8 g2; CB 8 g3], [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
unfold hc in *. rewrite <- EH3 in HS5, HR5 |- *. rewrite ENB.
split; [unfold h_regs; cbn [set_ogg set_bytes_remaining h_stream_init h_last_granule h_packet_count]; exact Hc7|].
split; [exact FRM|]. split; [exact HS5|].
split; [unfold h_iter; cbn [set_ogg set_bytes_remaining h_bytes_remaining]; rewrite EBR; unfold CHUNK, x_size in *; lia|].
split; [exact HR5|]. split; [do 4 eexists; reflexivity| do 6 eexists; reflexivity].
Qed.
End Chunk0.
