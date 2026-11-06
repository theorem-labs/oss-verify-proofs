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
X077 X076 X07f X07e X07b X07a X07c X06o X07d
X0a7 X09w X09o X06e
X06x X06w X07g X06p X078 X06s X075 X074 X06q
X081 X0aj X05w X06z X06k.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12c X14x X0r0 X0ra X0qz X0v9 X0rb X0wl X0wm X110 X106 X10j X10c X10x X108 X10q X10r X0wb X0w9 X0wg X0wf X0x5 X0zq X0x2 X0x1 X0xn X0xq X0xm X0xu X0ya X0xt X0y0 X0y8 X0y6 X0y5 X0y2 X0y1 X0y3 X0xg X0y4 X10t X10i X10b X0x6 X0xp X0xo X0y7 X0xh X0xz X0xk X0xv X0xi X0ys X0xc.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X108 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wg OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wf OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ya OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y8 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y6 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y3 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xg OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y4 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x6 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xo OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y7 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xh OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xk OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xv OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xi OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xc.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Section Top.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis IO_drv : forall y, in_ranges IO_FP y -> ~ drv_cell y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis LIB_loc : fp_local LIB_FP LIB.

Hypothesis SM8 : stack_malloc_contract RT 8.
Hypothesis SSF8 : set_shadow_contract RT 0xf8.
Hypothesis SS00 : set_shadow_contract RT 0.
Hypothesis SF8 : stack_free_contract RT 8.
Hypothesis MCPY : memcpy_icontract RT e_asan_memcpy.
Hypothesis BCMP : bcmp_icontract RT.

Hypothesis BINIT : speex_bits_init_cps RT.
Hypothesis BDES : speex_bits_destroy_cps RT.
Hypothesis RF : speex_bits_read_from_cps RT OUT_rep ERR_rep IO_FP.
Hypothesis SBUF : ogg_sync_buffer_cps RT.
Hypothesis POUT : ogg_sync_pageout_cps RT.
Hypothesis SCLR : ogg_stream_clear_cps RT.
Hypothesis YCLR : ogg_sync_clear_cps RT.
Hypothesis DESTROY : forall d, destroy_cps_at RT d.
Hypothesis DEC : forall d, dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode d.
Hypothesis ISAVE : forall (d d' : dec_state bptr) b q ret b' q',
prun (speex_decode (St := pst) p_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M d b 0) q = Some ((ret, d', b'), q') ->
isave_ok d -> isave_ok d'.

Hypothesis HDRB : forall X F0 fs0, fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> h_hdr_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Hypothesis PAGEB : forall X F0 fs0, h_clean_cps RT OUT_rep ERR_rep IO_FP X F0 fs0 -> h_page_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.

Theorem h_fuzz_one_ok : fuzz_one_cpsE RT OUT_rep ERR_rep IO_FP LIB.
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV LIB_loc SM8 SSF8 SS00 SF8 MCPY BCMP BINIT BDES RF SBUF POUT SCLR YCLR DESTROY DEC ISAVE
HDRB PAGEB.
intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo rc eb
RUN EA0 EA1 ETP ERA D0 BSL BY PAY FR0 LVP LVR CRE S0C FD2 LIB0 ERR0 SSP0 ART0 MI0 FRM ST0 LOW LOR SPT SPA SP0L.
assert (HPRE : h_entry_pre RT ERR_rep Σ ra sp gp tp s0 a0 a1 m d bs lo).
{ assert (LVH : Z.of_nat (length (rt_live RT Σ)) + H_LIVE <= LIVE_MAX) by (unfold H_LIVE; unfold FUZZ_LIVE in LVR; lia).
assert (PAY' : (exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ bs = [])
by (destruct PAY as [PAY|(PAY & _)]; [left; exact PAY| right; exact PAY]).
exact (conj EA0 (conj EA1 (conj ETP (conj ERA (conj D0 (conj BSL (conj BY (conj PAY' (conj FR0 (conj LVP (conj LVH (conj CRE (conj S0C
(conj ERR0 (conj SSP0 (conj ART0 (conj MI0 (conj ST0 (conj LOW (conj LOR (conj SPT (conj SPA SP0L)))))))))))))))))))))). }
pose proof (h_entry_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img SM8 SSF8 SS00 MCPY BINIT AF_DRV F0 fs0
Σ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo FRM HPRE) as ENT.
change (SpecA.X1rn.evw 2 eb) with (Spec.X1nu.evw 2 eb).

assert (FIN : forall X c, h_entry_X RT X Σ ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m d bs lo ->
h_final RT OUT_rep ERR_rep IO_FP X F0 fs0 Σ LIB fc c ->
exists Σ' : rts RT, ASTA RT Σ' (PMfd F0 fs0) (fun ms => exists m', ret_stR fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (LIB_FP ++ IO_FP) m m'
/\ LIB m' /\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m')) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σ').
{ intros X c HXE HF.
destruct HXE as (EUSP & ELO & EGP & ED & EBS & ELV & ESP0 & ECR & EM0 & ERA' & ES0 & ES1 & ES2 & ES3 & ES4 & ES5 & ES6 & ES7 & ES8 & ES9 & ES10 & ES11).
unfold h_final in HF.
rewrite EUSP, ELO, EGP, EM0, ERA', ES0, ES1, ES2, ES3, ES4, ES5, ES6, ES7, ES8, ES9, ES10, ES11, Z_to_bv_bv_unsigned, <- ETP in HF. exact HF. }

unfold X1r8.p_fuzz_one, LLVMFuzzerTestOneInput in RUN. cbv zeta in RUN.
assert (ZL : zlength (map bv_unsigned bs) = Z.of_nat (length bs)) by (unfold zlength; rewrite length_map; reflexivity).
rewrite ZL in RUN.
destruct (Z.ltb_spec MAX_FUZZ_SIZE (Z.of_nat (length bs))) as [BIG|SMALL].
-
rewrite prun_ret in RUN. injection RUN as <- EEB. subst eb.
rewrite evw_nil. apply cpsE_nil. eapply cps_seq; [exact ENT|].
intros T c (X & HXE & [(BIG' & HEP & HAT) | (SMALL' & _)]) Hk; [| exfalso; lia].
pose proof HXE as (_ & _ & _ & _ & _ & ELV & ESP0 & ECR & EM0 & _).
refine (h_ep_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img LIB LIB_loc SSF8 SF8 X F0 fs0 Σ fc HEP (eq_sym ELV) FR0 (eq_sym ESP0) (eq_sym ECR)
ltac:(rewrite EM0; exact LIB0) T c HAT _).
intros c' HF. apply Hk. exact (FIN X c' HXE HF).
-
rewrite prun_bind in RUN. destruct (prun (speex_bits_init p_calloc) p0) as [[ob q0]|] eqn:EBI; [| discriminate RUN].
destruct (bits_init_prun p0 ob q0 EBI) as (-> & ->). cbn beta iota in RUN.
rewrite prun_bind in RUN.
lazymatch type of RUN with
| match prun ?C p0 with _ => _ end = _ => destruct (prun C p0) as [[o q1]|] eqn:ECL; [| discriminate RUN]
end.
assert (EQ1 : p_err q1 = p_err p0 ++ eb).
{ destruct o as [h1|].
- cbn beta iota in RUN. rewrite prun_bind in RUN. pose proof (prun_cleanup h1 q1) as PC. unfold hP_cleanup in PC. rewrite PC in RUN.
cbn beta iota in RUN. rewrite prun_ret in RUN. injection RUN as _ ->. reflexivity.
- rewrite prun_ret in RUN. injection RUN as _ ->. reflexivity. }
eapply cps_cpsE; [exact ENT|].
intros T c (X & HXE & [(BIG' & _) | (SMALL' & HX & HCH)]) Hk; [exfalso; lia|].
pose proof HXE as (_ & _ & _ & _ & EBS & ELV & ESP0 & ECR & EM0 & _).
assert (ECL' : prun (hP_chunk_loop (chunk_fuel (Z.of_nat (length bs))) (x_payload X) (h_init X)) p0 = Some (o, q1)).
{ unfold hP_chunk_loop, h_init, x_payload, x_size. rewrite EBS. exact ECL. }
assert (XTF : forall c', at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c' -> realizes bsegs c' T).
{ intros c' HXT.
refine (h_xt_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img LIB LIB_loc SSF8 SF8 X F0 fs0 Σ fc HX (eq_sym ELV) FR0 (eq_sym ESP0) (eq_sym ECR)
ltac:(rewrite EM0; exact LIB0) T c' HXT _).
intros c'' HF. apply Hk. exact (FIN X c'' HXE HF). }
pose proof (h_clean_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV DESTROY BDES SCLR YCLR X F0 fs0) as CLEAN.

assert (BRI : 0 < h_bytes_remaining (h_init X) \/ (h_init X = h_init X /\ x_size X = 0 /\ x_d X <= x_lo X)).
{ destruct (Z.eq_dec (x_size X) 0) as [S0|SN]; [right| left; unfold h_init, x_size in *; cbn [h_bytes_remaining]; lia].
split; [reflexivity|]. split; [exact S0|].
pose proof HXE as (_ & ELO & _ & ED & EBS' & ELV' & _).
pose proof (hx_arith OUT_rep IO_FP X HX) as (_ & _ & _ & _ & _ & _ & _ & SHLO & _).
destruct PAY as [(p & n & INP & P1 & P2)|(_ & DS)].
- rewrite <- ELV' in INP. pose proof (hi_live_geo _ _ _ HX p n INP) as (PL & _). rewrite ED. unfold x_size in S0. rewrite EBS' in S0. lia.
- rewrite ED. unfold SH_HI, SEGTOP_A in *. lia. }
refine (h_cloop_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF BCMP X F0 fs0 FD2
(HDRB X F0 fs0 FD2)
(h_chunk_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV SBUF MCPY POUT X F0 fs0)
(h_pnext_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV POUT X F0 fs0)
(h_pexit_ok RT AF OUT_rep ERR_rep IO_FP X F0 fs0)
(PAGEB X F0 fs0 CLEAN)
(h_chunk0_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV SBUF MCPY POUT X F0 fs0) HX _ (h_init X) p0 o q1 eb BRI ECL' EQ1 T c HCH _).
intros c1 [(EO & HXT) | (h1 & EO & HCL)].
+ exact (XTF c1 HXT).
+ exact (CLEAN HX h1 T c1 HCL XTF).
Qed.
End Top.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Section Top.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis IO_drv : forall y, in_ranges IO_FP y -> ~ drv_cell y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis LIB_loc : fp_local LIB_FP LIB.

Hypothesis SM8 : stack_malloc_contract RT 8.
Hypothesis SSF8 : set_shadow_contract RT 0xf8.
Hypothesis SS00 : set_shadow_contract RT 0.
Hypothesis SF8 : stack_free_contract RT 8.
Hypothesis MCPY : memcpy_icontract RT e_asan_memcpy.
Hypothesis BCMP : bcmp_icontract RT.

Hypothesis BINIT : speex_bits_init_cps RT.
Hypothesis BDES : speex_bits_destroy_cps RT.
Hypothesis RF : speex_bits_read_from_cps RT OUT_rep ERR_rep IO_FP.
Hypothesis SBUF : ogg_sync_buffer_cps RT.
Hypothesis POUT : ogg_sync_pageout_cps RT.
Hypothesis SINIT : ogg_stream_init_cps RT.
Hypothesis PGIN : ogg_stream_pagein_cps RT.
Hypothesis SCLR : ogg_stream_clear_cps RT.
Hypothesis YCLR : ogg_sync_clear_cps RT.
Hypothesis DESTROY : forall d, destroy_cps_at RT d.
Hypothesis DEC : forall d, dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode d.
Hypothesis ISAVE : forall (d d' : dec_state bptr) b q ret b' q',
prun (speex_decode (St := pst) p_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M d b 0) q = Some ((ret, d', b'), q') ->
isave_ok d -> isave_ok d'.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Hypothesis FRE : free_contract RT.

Hypothesis P2H2 : speex_packet_to_header_cps RT OUT_rep ERR_rep IO_FP.
Hypothesis CTL : forall d, ctl_cps_at RT d.
Hypothesis INIT8 : forall mo, init_cps_at8 RT mo.

Theorem h_fuzz_one_ok : fuzz_one_cpsE RT OUT_rep ERR_rep IO_FP LIB.
Proof using AF ERR_loc OUT_loc IO_img IO_drv AF_DRV LIB_loc SM8 SSF8 SS00 SF8 MCPY BCMP BINIT BDES RF SBUF POUT SINIT PGIN SCLR YCLR DESTROY DEC ISAVE
AF_LIB FRE P2H2 CTL INIT8.
intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo rc eb
RUN EA0 EA1 ETP ERA D0 BSL BY PAY FR0 LVP LVR CRE S0C FD2 LIB0 ERR0 SSP0 ART0 MI0 FRM ST0 LOW LOR SPT SPA SP0L.
assert (HPRE : h_entry_pre RT ERR_rep Σ ra sp gp tp s0 a0 a1 m d bs lo).
{ assert (LVH : Z.of_nat (length (rt_live RT Σ)) + H_LIVE <= LIVE_MAX) by (unfold H_LIVE; unfold FUZZ_LIVE in LVR; lia).
assert (PAY' : (exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ bs = [])
by (destruct PAY as [PAY|(PAY & _)]; [left; exact PAY| right; exact PAY]).
exact (conj EA0 (conj EA1 (conj ETP (conj ERA (conj D0 (conj BSL (conj BY (conj PAY' (conj FR0 (conj LVP (conj LVH (conj CRE (conj S0C
(conj ERR0 (conj SSP0 (conj ART0 (conj MI0 (conj ST0 (conj LOW (conj LOR (conj SPT (conj SPA SP0L)))))))))))))))))))))). }
pose proof (h_entry_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img SM8 SSF8 SS00 MCPY BINIT AF_DRV F0 fs0
Σ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo FRM HPRE) as ENT.
change (SpecA.X1rn.evw 2 eb) with (Spec.X1nu.evw 2 eb).

assert (FIN : forall X c, h_entry_X RT X Σ ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m d bs lo ->
h_final RT OUT_rep ERR_rep IO_FP X F0 fs0 Σ LIB fc c ->
exists Σ' : rts RT, ASTA RT Σ' (PMfd F0 fs0) (fun ms => exists m', ret_stR fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (LIB_FP ++ IO_FP) m m'
/\ LIB m' /\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m')) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σ').
{ intros X c HXE HF.
destruct HXE as (EUSP & ELO & EGP & ED & EBS & ELV & ESP0 & ECR & EM0 & ERA' & ES0 & ES1 & ES2 & ES3 & ES4 & ES5 & ES6 & ES7 & ES8 & ES9 & ES10 & ES11).
unfold h_final in HF.
rewrite EUSP, ELO, EGP, EM0, ERA', ES0, ES1, ES2, ES3, ES4, ES5, ES6, ES7, ES8, ES9, ES10, ES11, Z_to_bv_bv_unsigned, <- ETP in HF. exact HF. }

unfold X1r8.p_fuzz_one, LLVMFuzzerTestOneInput in RUN. cbv zeta in RUN.
assert (ZL : zlength (map bv_unsigned bs) = Z.of_nat (length bs)) by (unfold zlength; rewrite length_map; reflexivity).
rewrite ZL in RUN.
destruct (Z.ltb_spec MAX_FUZZ_SIZE (Z.of_nat (length bs))) as [BIG|SMALL].
-
rewrite prun_ret in RUN. injection RUN as <- EEB. subst eb.
rewrite evw_nil. apply cpsE_nil. eapply cps_seq; [exact ENT|].
intros T c (X & HXE & [(BIG' & HEP & HAT) | (SMALL' & _)]) Hk; [| exfalso; lia].
pose proof HXE as (_ & _ & _ & _ & _ & ELV & ESP0 & ECR & EM0 & _).
refine (h_ep_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img LIB LIB_loc SSF8 SF8 X F0 fs0 Σ fc HEP (eq_sym ELV) FR0 (eq_sym ESP0) (eq_sym ECR)
ltac:(rewrite EM0; exact LIB0) T c HAT _).
intros c' HF. apply Hk. exact (FIN X c' HXE HF).
-
rewrite prun_bind in RUN. destruct (prun (speex_bits_init p_calloc) p0) as [[ob q0]|] eqn:EBI; [| discriminate RUN].
destruct (bits_init_prun p0 ob q0 EBI) as (-> & ->). cbn beta iota in RUN.
rewrite prun_bind in RUN.
lazymatch type of RUN with
| match prun ?C p0 with _ => _ end = _ => destruct (prun C p0) as [[o q1]|] eqn:ECL; [| discriminate RUN]
end.
assert (EQ1 : p_err q1 = p_err p0 ++ eb).
{ destruct o as [h1|].
- cbn beta iota in RUN. rewrite prun_bind in RUN. pose proof (prun_cleanup h1 q1) as PC. unfold hP_cleanup in PC. rewrite PC in RUN.
cbn beta iota in RUN. rewrite prun_ret in RUN. injection RUN as _ ->. reflexivity.
- rewrite prun_ret in RUN. injection RUN as _ ->. reflexivity. }
eapply cps_cpsE; [exact ENT|].
intros T c (X & HXE & [(BIG' & _) | (SMALL' & HX & HCH)]) Hk; [exfalso; lia|].
pose proof HXE as (_ & _ & _ & _ & EBS & ELV & ESP0 & ECR & EM0 & _).
assert (ECL' : prun (hP_chunk_loop (chunk_fuel (Z.of_nat (length bs))) (x_payload X) (h_init X)) p0 = Some (o, q1)).
{ unfold hP_chunk_loop, h_init, x_payload, x_size. rewrite EBS. exact ECL. }
assert (XTF : forall c', at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c' -> realizes asegs c' T).
{ intros c' HXT.
refine (h_xt_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img LIB LIB_loc SSF8 SF8 X F0 fs0 Σ fc HX (eq_sym ELV) FR0 (eq_sym ESP0) (eq_sym ECR)
ltac:(rewrite EM0; exact LIB0) T c' HXT _).
intros c'' HF. apply Hk. exact (FIN X c'' HXE HF). }
pose proof (h_clean_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV DESTROY BDES SCLR YCLR X F0 fs0) as CLEAN.

assert (BRI : 0 < h_bytes_remaining (h_init X) \/ (h_init X = h_init X /\ x_size X = 0 /\ x_d X <= x_lo X)).
{ destruct (Z.eq_dec (x_size X) 0) as [S0|SN]; [right| left; unfold h_init, x_size in *; cbn [h_bytes_remaining]; lia].
split; [reflexivity|]. split; [exact S0|].
pose proof HXE as (_ & ELO & _ & ED & EBS' & ELV' & _).
pose proof (hx_arith OUT_rep IO_FP X HX) as (_ & _ & _ & _ & _ & _ & _ & SHLO & _).
destruct PAY as [(p & n & INP & P1 & P2)|(_ & DS)].
- rewrite <- ELV' in INP. pose proof (hi_live_geo _ _ _ HX p n INP) as (PL & _). rewrite ED. unfold x_size in S0. rewrite EBS' in S0. lia.
- rewrite ED. unfold SH_HI, SEGTOP_A in *. lia. }
refine (h_cloop_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_drv AF_DRV DEC ISAVE RF BCMP X F0 fs0 FD2
(fun HX' => h_hdr_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_drv AF_DRV AF_LIB X HX' F0 fs0 BDES SCLR YCLR FRE DESTROY FD2 P2H2 CTL INIT8 HX')
(h_chunk_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV SBUF MCPY POUT X F0 fs0)
(h_pnext_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV POUT X F0 fs0)
(h_pexit_ok RT AF OUT_rep ERR_rep IO_FP X F0 fs0)
(h_page_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV SINIT PGIN X F0 fs0 CLEAN)
(h_chunk0_ok RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV SBUF MCPY POUT X F0 fs0) HX _ (h_init X) p0 o q1 eb BRI ECL' EQ1 T c HCH _).
intros c1 [(EO & HXT) | (h1 & EO & HCL)].
+ exact (XTF c1 HXT).
+ exact (CLEAN HX h1 T c1 HCL XTF).
Qed.
End Top.
