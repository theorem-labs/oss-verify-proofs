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
X0ae X09u X0af X09p X0ab X0a7 X05l X071 X06v X06r
X06u X073 X07j X072.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12c X14x X0r0 X0ra X0qz X0v9 X0rb X0wl X0wm X110 X10c X10x X10t X0xn X0xj X0xm X0xu X0ya X0xt.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xj OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ya OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xt.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Section PNext.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis POUT : ogg_sync_pageout_cps RT.
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.

Theorem h_pnext_ok : h_pnext_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Proof using AF ERR_loc OUT_loc IO_img AF_DRV POUT.
intros HX h nbr brem0 T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r2 & r5 & r8 & t3 & t4 & t5 & t6 & v48 & v56 & v88 & j224 & j232 & ogc & opc
& Hc & FRM & HS & HIT & SI1 & HR & OGJ & OPJ).
destruct OGJ as (g0 & g1 & g2 & g3 & ->). destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->).
pose proof HR as HR'. destruct HR' as (ART & MI & ST & _ & _ & _ & _ & SP & _ & _ & _ & _ & _ & SY & OGC & _ & _ & _ & _ & _ & _ & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
unfold h_regs in Hc. unfold h_spill in SP.
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).

refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply pn_w1; [exact SP | exact MI | exact S1R]. }
intros ms1 c1 -> Hc1. clear Hc.

pose proof HP as (SI2 & SI & _).
destruct (ogg_sync_pageout (h_oy h)) as [[[r ogo] oy2]|] eqn:EPO; [| exfalso; exact (ogg_sync_pageout_total _ SI EPO)].
assert (SYL : sync_live RT Σ1 (h_oy h) (a_Dsy a)).
{ intros NS. rewrite EL. apply in_or_app. left. apply (Permutation_in _ (Permutation_sym PERM)). exact (own_in_Dsy a h NS). }
assert (INF : In (x_F X, 8%nat) (rt_frames RT Σ1)) by (rewrite EF; left; reflexivity).
unfold HO_OY, HO_OG in SY, OGC.
Time cps_rt (POUT Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (x_F X + 8480) (x_F X + 8544) (a_Dsy a) (x_F X) (x_lo X) 8%nat
(h_oy h) (a_sybytes a) g0 g1 g2 g3 r ogo oy2).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ change (fs_size 8) with 16384. lia. }
{ change (fs_size 8) with 16384. lia. }
{ rewrite unsigned_lit by lia. exact ST. }
{ rewrite unsigned_lit by lia. unfold RT_STACK, H_STACK in *. lia. }
{ rewrite unsigned_lit by lia. unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by lia. clear - S32. Z.div_mod_to_equations. lia. }
intros c2 Hc2. clear Hc1.
Time cps_unpack_lib Hc2 as (m' & RS & RA & PR & SY' & OG').
destruct RS as (-> & ->).
destruct (hrep_pageout RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m' a h _ _ g0 g1 g2 g3 r ogo oy2 HS HR
ltac:(reflexivity) ltac:(reflexivity) EPO RA PR SY' OG') as (HS' & HR' & PGI).
clear HR SY OGC SY' OG' PR SP ART MI ST.
pose proof HR' as HR''. destruct HR'' as (_ & MI' & _ & _ & _ & _ & _ & SP' & _).
pose proof (pageout_ret _ _ _ _ EPO) as RR.

refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c2 (PMfd_mat_stable F0 fs0) Hc _ _).
{ unfold wz. eapply pn_w2; [reflexivity | lia | exact MI']. }
intros ms3 c3 POST Hc3. clear Hc.
cbv beta in POST.
apply Hk. exists r, ogo, oy2. split; [exact EPO|].
destruct POST as [(E1 & ->) | (NE & ->)].
-
destruct ogo as [og|]; [| exfalso; exact (PGI E1)]. destruct PGI as (_ & POK & PBUD).
left. split; [exact E1|]. exists og. split; [reflexivity|].
exists Σ1, a, Fx, fc, m', (Z64 618228), r0, r1, r3, (Z64 r), r6, r7, r9, r10, r11, r12, r2, (Z64 1), r8, r13, r14, r15, r16, v48, v56, v88, j224, j232,
[CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
split; [unfold h_regs; cbn [set_ogg h_stream_init h_packet_count h_channels h_eos]; rewrite SI1; exact Hc3|].
split; [exact FRM|]. split; [exact HS'|]. split; [exact HIT|]. split; [exact HR'|]. split; [do 6 eexists; reflexivity| split; [exact POK| exact PBUD]].
-
destruct ogo as [og|]; [exfalso; exact (NE (proj1 PGI))|].
right. split; [exact NE|].
exists Σ1, a, Fx, fc, m', (Z64 618228), r0, r1, r3, (Z64 r), (Z64 0), r6, r7, r9, r10, r11, r12, r2, r8, (Z64 (x_F X + 8544)), r13, r14, r15, r16, v48, v56, v88, j224, j232,
[CB 8 g0; CB 8 g1; CB 8 g2; CB 8 g3], [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
split; [unfold h_regs; cbn [set_ogg h_stream_init h_packet_count h_channels h_eos]; rewrite SI1; exact Hc3|].
split; [exact FRM|]. split; [exact HS'|]. split; [exact HIT|]. split; [exact HR'|]. split; [do 4 eexists; reflexivity| do 6 eexists; reflexivity].
Qed.
End PNext.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Section PNext.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis POUT : ogg_sync_pageout_cps RT.
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.

Theorem h_pnext_ok : h_pnext_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Proof using AF ERR_loc OUT_loc IO_img AF_DRV POUT.
intros HX h nbr brem0 T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r5 & r8 & t3 & t4 & t5 & t6 & j0 & j192 & j200 & ogc & opc
& Hc & FRM & HS & HIT & SI1 & HR & OGJ & OPJ).
destruct OGJ as (g0 & g1 & g2 & g3 & ->). destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->).
pose proof HR as HR'. destruct HR' as (ART & MI & ST & _ & _ & _ & _ & SP & _ & _ & _ & _ & _ & SY & OGC & _ & _ & _ & _ & _ & _ & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
unfold h_regs in Hc. unfold h_spill in SP.
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).

refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply pn_w1; [exact SP | exact MI | exact S1R]. }
intros ms1 c1 -> Hc1. clear Hc.

pose proof HP as (SI2 & SI & _).
destruct (ogg_sync_pageout (h_oy h)) as [[[r ogo] oy2]|] eqn:EPO; [| exfalso; exact (ogg_sync_pageout_total _ SI EPO)].
assert (SYL : sync_live RT Σ1 (h_oy h) (a_Dsy a)).
{ intros NS. rewrite EL. apply in_or_app. left. apply (Permutation_in _ (Permutation_sym PERM)). exact (own_in_Dsy a h NS). }
assert (INF : In (x_F X, 8%nat) (rt_frames RT Σ1)) by (rewrite EF; left; reflexivity).
unfold HO_OY, HO_OG in SY, OGC.
Time cps_rt (POUT Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (x_F X + 8480) (x_F X + 8544) (a_Dsy a) (x_F X) (x_lo X) 8%nat
(h_oy h) (a_sybytes a) g0 g1 g2 g3 r ogo oy2).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ change (fs_size 8) with 16384. lia. }
{ change (fs_size 8) with 16384. lia. }
{ rewrite unsigned_lit by lia. exact ST. }
{ rewrite unsigned_lit by lia. unfold RT_STACK, H_STACK in *. lia. }
{ rewrite unsigned_lit by lia. unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by lia. clear - S32. Z.div_mod_to_equations. lia. }
intros c2 Hc2. clear Hc1.
Time cps_unpack_lib Hc2 as (m' & RS & RA & PR & SY' & OG').
destruct RS as (-> & ->).
destruct (hrep_pageout RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m' a h _ _ g0 g1 g2 g3 r ogo oy2 HS HR
ltac:(reflexivity) ltac:(reflexivity) EPO RA PR SY' OG') as (HS' & HR' & PGI).
clear HR SY OGC SY' OG' PR SP ART MI ST.
pose proof HR' as HR''. destruct HR'' as (_ & MI' & _ & _ & _ & _ & _ & SP' & _).
pose proof (pageout_ret _ _ _ _ EPO) as RR.

refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c2 (PMfd_mat_stable F0 fs0) Hc _ _).
{ unfold wz. eapply pn_w2; [reflexivity | lia | exact SP' | exact MI' | exact S1R]. }
intros ms3 c3 POST Hc3. clear Hc.
cbv beta in POST. apply Hk. exists r, ogo, oy2. split; [exact EPO|].
destruct POST as [(E1 & ->) | (NE & ->)].
-
destruct ogo as [og|]; [| exfalso; exact (PGI E1)]. destruct PGI as (_ & POK & PBUD).
left. split; [exact E1|]. exists og. split; [reflexivity|].
exists Σ1, a, Fx, fc, m', (Z64 618840), r0, r1, r2, (Z64 r), r6, r7, r9, r10, r11, r5, (Z64 1), r12, r13, r14, r15, j0, j192, j200,
[CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
split; [unfold h_regs; cbn [set_ogg h_stream_init h_last_granule h_packet_count]; rewrite SI1; exact Hc3|].
split; [exact FRM|]. split; [exact HS'|]. split; [exact HIT|]. split; [exact HR'|]. split; [do 6 eexists; reflexivity| split; [exact POK| exact PBUD]].
-
destruct ogo as [og|]; [exfalso; exact (NE (proj1 PGI))|].
right. split; [exact NE|].
exists Σ1, a, Fx, fc, m', (Z64 618840), r0, r1, r2, (Z64 r), (Z64 0), r6, r7, r9, r10, r11, r5, r12, r13, r14, r15, j0, j192, j200,
[CB 8 g0; CB 8 g1; CB 8 g2; CB 8 g3], [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].
split; [unfold h_regs; cbn [set_ogg h_stream_init h_last_granule h_packet_count]; rewrite SI1; exact Hc3|].
split; [exact FRM|]. split; [exact HS'|]. split; [exact HIT|]. split; [exact HR'|]. split; [do 4 eexists; reflexivity| do 6 eexists; reflexivity].
Qed.
End PNext.
