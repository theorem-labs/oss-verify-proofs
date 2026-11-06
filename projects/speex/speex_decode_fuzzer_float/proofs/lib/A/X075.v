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
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1qy.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X000 X04b X00c X07z X05o X05p X05s X05t
X0ae X09j X09u X0af X09x X09p X0ab X09l X0a4 X0a5
X09v X09w X09n X05l X05m X06d X069 X068 X07m
X071 X06v X06y X06u X073 X07j X072 X079 X07h
X077 X076.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Section Page.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis SINIT : ogg_stream_init_cps RT.
Hypothesis PGIN : ogg_stream_pagein_cps RT.
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.
Hypothesis CLEAN : h_clean_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.

Theorem h_p3_ok : hinv_ok OUT_rep IO_FP X -> forall (h : hstate unit) (og : page) (nbr brem0 : Z),
cps asegs (at_P3 RT OUT_rep ERR_rep IO_FP X F0 fs0 h og nbr brem0) (page_post RT OUT_rep ERR_rep IO_FP X F0 fs0 h (page_header (h_oy h) og) nbr brem0).
Proof using AF ERR_loc OUT_loc IO_img AF_DRV CLEAN.
intros HX h og nbr brem0 T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r5 & t3 & t4 & t5 & t6 & j0 & j192 & j200 & opc
& Hc & FRM & HS & HIT & SI1 & HR & OPJ & POK).
pose proof HR as HR'. destruct HR' as (ART & MI & ST & _ & _ & _ & _ & SP & _ & _ & _ & FSZ & _ & SY & OGC & _ & _ & _ & _ & _ & _ & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART HS) as HSP.
unfold h_regs in Hc. unfold h_spill in SP.
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).
pose proof HP as (SI2 & SINV & _ & (SDN & SND) & _ & _ & _ & FSR & GFS & NFR & _ & _ & EXR & _ & _ & LGR & _ & EOR & _).

assert (NN : sy_data (h_oy h) <> None).
{ intros E. pose proof SY as (_ & _ & DAT & _). unfold sync_data in DAT. unfold bptr in *. rewrite E in DAT.
destruct DAT as (_ & _ & EB & _). pose proof POK as (P0 & P1 & P2 & P3 & P4 & P5 & P6). rewrite EB in P5.
unfold zlength in P5. cbn [length Z.of_nat] in P5. lia. }
destruct (page_hs_a m _ _ _ _ og SY SINV POK NN) as (HSB & BSB & LHS & LBS & EHS & EBS & HL27 & N26 & PG0 & PGE & BL0).
set (hs := firstn (Z.to_nat (pg_header_len og)) (skipn (Z.to_nat (pg_hdr og)) (a_sybytes a))) in *.
destruct (proj1 HSP _ _ (own_in_Dsy a h NN)) as (D0 & DLO & _).
assert (LSY : Z.of_nat (length (a_sybytes a)) = sy_storage (h_oy h)).
{ pose proof SY as (_ & _ & DAT & _). unfold sync_data in DAT. unfold bptr in *.
destruct (sy_data (h_oy h)); [exact (proj1 (proj2 (proj2 DAT)))| exfalso; exact (NN eq_refl)]. }
unfold RT_STACK, H_STACK in LR.
unfold HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS, HO_FSZ, HO_LOOK, HO_RATE, HO_ENH, HO_OY in Hc, SP, FSZ, OGC.
refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply (pb_w3 (x_S1 X) (x_F X) (a_Dsy a) og hs (h_frame_size h) (h_granule_frame_size h) (h_nframes h) (h_last_granule h) (h_extra_headers h) (h_eos h));
[reflexivity| exact S1R| lia| lia| lia| lia| exact OGC| exact HSB| lia| lia| exact FSZ| exact SP| lia| exact GFS| lia| lia| lia| exact EOR| exact MI]. }
intros ms1 c1 POST Hc1. clear Hc.
destruct POST as (m1 & ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & MU & WM & MI1 & SP1 & CASES).
set (pg := ogg_page_granulepos (ubytes hs)) in *.
pose proof (hrep_spill RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m1 a h _
(h_spill X (Z64 nbr) (Z64 brem0) (Z64 pg) (Z64 (h_speex_serialno h)) j0 j192 j200 h) _ _ HS HR
ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->); reflexivity) MU WM MI1 SP1) as HR1.
clear HR SP SP1 MU WM.
destruct (hrep_og_junk RT OUT_rep ERR_rep IO_FP X Σ1 m1 a h _ _ _ _ HR1) as (ogc & HR2 & OGJ).
clear HR1.
unfold bptr in EHS, EBS.
destruct CASES as [(GN & ->) | [(GS & NE & ->) | (GS & EQ & ->)]].
-
refine (CLEAN HX h T c1 _ _).
+ exists Σ1, a, Fx, fc, m1, ra', t0', t1', t2', a3', a4', a5', a6', a7', (Z64 pg), (Z64 (h_last_granule h)), t3', t4', t5', t6',
(Z64 nbr), (Z64 brem0), (Z64 pg), (Z64 (h_speex_serialno h)), j0, j192, j200, ogc, opc.
split; [unfold h_regs; rewrite SI1; unfold HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; exact Hc1|].
split; [exact FRM|]. split; [exact HS|]. split; [exact HR2|]. split; [exact OGJ| exact OPJ].
+ intros c2 Hc2. apply Hk. unfold page_post. rewrite granule_step_gstep, <- EHS. fold pg. rewrite GN. exact Hc2.
-
assert (PGR : -1 <= pg < 2^63).
{ split.
- revert GS. unfold gstep. destruct (Z.ltb_spec 0 pg) as [P|P]; [intros _; lia|]. cbn [andb].
destruct (Z.ltb_spec pg (-1)) as [P2|P2]; [intros C; exfalso; exact (C eq_refl)| intros _; lia].
- unfold pg, ogg_page_granulepos, s64. pose proof (Z.mod_pos_bound (le64_at (ubytes hs) 6 + 2^63) (2^64) ltac:(lia)). lia. }
destruct (gstep (h_frame_size h) (h_granule_frame_size h) (h_nframes h) (h_last_granule h) pg (ogg_page_packets (ubytes hs)) (ogg_page_eos (ubytes hs)))
as [skip|] eqn:EG; [| exfalso; exact (GS eq_refl)].
apply Hk. unfold page_post. rewrite granule_step_gstep, <- EHS. fold pg. rewrite EG. cbv zeta.
right. split; [cbn [set_granule h_eos]; exact NE|].
exists Σ1, a, Fx, fc, m1, ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', (Z64 pg), (Z64 (h_last_granule h)), t3', t4', t5', t6',
j0, j192, j200, ogc, opc.
split; [unfold h_regs; cbn [set_granule h_packet_count]; unfold HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; exact Hc1|].
split; [exact FRM|]. split; [exact (hsig_set_granule RT X Σ1 a h pg skip HS)|].
split; [exact HIT|]. split; [exact SI1|].
split; [exact (hrep_set_granule RT OUT_rep ERR_rep IO_FP X Σ1 m1 a h _ _ _ pg skip HR2 PGR)|].
split; [exact OGJ| exact OPJ].
-
assert (PGR : -1 <= pg < 2^63).
{ split.
- revert GS. unfold gstep. destruct (Z.ltb_spec 0 pg) as [P|P]; [intros _; lia|]. cbn [andb].
destruct (Z.ltb_spec pg (-1)) as [P2|P2]; [intros C; exfalso; exact (C eq_refl)| intros _; lia].
- unfold pg, ogg_page_granulepos, s64. pose proof (Z.mod_pos_bound (le64_at (ubytes hs) 6 + 2^63) (2^64) ltac:(lia)). lia. }
destruct (gstep (h_frame_size h) (h_granule_frame_size h) (h_nframes h) (h_last_granule h) pg (ogg_page_packets (ubytes hs)) (ogg_page_eos (ubytes hs)))
as [skip|] eqn:EG; [| exfalso; exact (GS eq_refl)].
apply Hk. unfold page_post. rewrite granule_step_gstep, <- EHS. fold pg. rewrite EG. cbv zeta.
left. split; [cbn [set_granule h_eos]; exact EQ|].
exists Σ1, a, Fx, fc, m1, ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', (Z64 pg), (Z64 (x_F X + HO_OS)), t3', t4', t5', t6',
j0, j192, j200, ogc, opc.
split; [unfold h_regs; cbn [set_granule h_packet_count h_extra_headers]; rewrite (Z.add_comm 1 (h_extra_headers h));
unfold HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; exact Hc1|].
split; [exact FRM|]. split; [exact (hsig_set_granule RT X Σ1 a h pg skip HS)|].
split; [exact HIT|]. split; [exact SI1|]. split; [cbn [set_granule h_eos]; exact EQ|]. split; [lia|].
split; [exact (hrep_set_granule RT OUT_rep ERR_rep IO_FP X Σ1 m1 a h _ _ _ pg skip HR2 PGR)|].
split; [exact OGJ| exact OPJ].
Qed.

Theorem h_pc_ok : hinv_ok OUT_rep IO_FP X -> forall (h : hstate unit) (og : page) (nbr brem0 : Z) (q q2 : pst) ro,
prun (ogg_stream_pagein (St := pst) p_realloc p_free (h_os h) (page_header (h_oy h) og) (page_body (h_oy h) og)) q = Some (ro, q2) ->
cps asegs (at_PC RT OUT_rep ERR_rep IO_FP X F0 fs0 h og nbr brem0)
(fun c => q2 = q /\ at_P3 RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_ogg h (h_oy h) (snd ro)) og nbr brem0 c).
Proof using AF ERR_loc OUT_loc IO_img AF_DRV PGIN.
intros HX h og nbr brem0 q q2 ro RUN T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & r5 & t3 & t4 & t5 & t6 & j0 & j192 & j200 & opc
& Hc & FRM & HS & HIT & SI1 & HR & OPJ & POK & PBUD).
pose proof HR as HR'. destruct HR' as (ART & MI & ST & _ & _ & _ & _ & SP & _ & _ & _ & FSZ & _ & SY & OGC & _ & OSR & _ & _ & _ & _ & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART HS) as HSP.
unfold h_regs in Hc.
assert (S1R : 0 <= x_S1 X < 2^62) by (unfold USTACK_TOP in UT; lia).
pose proof HP as (SI2 & SINV & _ & (SDN & SND) & _).

assert (NN : sy_data (h_oy h) <> None).
{ intros E. pose proof SY as (_ & _ & DAT & _). unfold sync_data in DAT. unfold bptr in *. rewrite E in DAT.
destruct DAT as (_ & _ & EB & _). pose proof POK as (P0 & P1 & P2 & P3 & P4 & P5 & P6). rewrite EB in P5.
unfold zlength in P5. cbn [length Z.of_nat] in P5. lia. }
destruct (page_hs_a m _ _ _ _ og SY SINV POK NN) as (HSB & BSB & LHS & LBS & EHS & EBS & HL27 & N26 & PG0 & PGE & BL0).
unfold bptr in EHS, EBS.
set (hs := firstn (Z.to_nat (pg_header_len og)) (skipn (Z.to_nat (pg_hdr og)) (a_sybytes a))) in *.
set (bs := firstn (Z.to_nat (pg_body_len og)) (skipn (Z.to_nat (pg_hdr og + pg_header_len og)) (a_sybytes a))) in *.
assert (LSY : Z.of_nat (length (a_sybytes a)) = sy_storage (h_oy h)).
{ pose proof SY as (_ & _ & DAT & _). unfold sync_data in DAT. unfold bptr in *.
destruct (sy_data (h_oy h)); [exact (proj1 (proj2 (proj2 DAT)))| exfalso; exact (NN eq_refl)]. }
destruct (page_ok_body_len (h_oy h) og SINV POK) as (ZSEQ & _ & _). rewrite <- EHS, <- EBS in ZSEQ.
rewrite <- EHS, <- EBS in RUN.

unfold h_os_rep in OSR. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0|_]; [rewrite SI1 in E0; discriminate E0|].
destruct OSR as (OS & LH & ARR & FOK & SINVo & BINV & LOK & GL & BD & LV & GV & LS & BS & NBL & NBG & NLG).
destruct (own_in_os a h ltac:(rewrite SI1; discriminate)) as (IB & IL & IG).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (SLV : stream_live RT Σ1 (h_os h) (a_Bd a) (a_L a) (a_G a)).
{ split; [exact (INL _ IB)|]. split; [exact (INL _ IL)|]. split; [exact (INL _ IG)|]. split; [exact NBL|]. split; [exact NBG| exact NLG]. }
pose proof (own_ne_Dsy a h (proj2 (proj2 HSP)) NN) as (_ & NSY & _).
destruct (NSY ltac:(rewrite SI1; discriminate)) as (NSB & NSL & NSG).

pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ.
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BR & _ & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
pose proof PBUD as (cold & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7).
unfold h_consumed, h_pend in *.
assert (BUDL : 8 * (os_lacing_storage (h_os h) + znth (ubytes hs) 26 + 33) <= 64512) by lia.
assert (BUDB : os_body_storage (h_os h) + pg_body_len og + 1024 <= 64512) by lia.
assert (LVR : Z.of_nat (length (rt_live RT Σ1)) < LIVE_MAX).
{ rewrite (h_live_len RT X Σ1 a h HS).
pose proof (h_own_len RT OUT_rep ERR_rep IO_FP X Σ1 m a h _ _ _ HR) as L24.
pose proof (hi_live _ _ _ HX) as (_ & LL). unfold H_LIVE in LL. lia. }
assert (INF : In (x_F X, 8%nat) (rt_frames RT Σ1)) by (rewrite EF; left; reflexivity).
assert (INSY : In (a_Dsy a, sy_storage (h_oy h)) (rt_live RT Σ1)) by exact (INL _ (own_in_Dsy a h NN)).
assert (LENH : length hs = (27 + Z.to_nat (znth (ubytes hs) 26))%nat) by lia.
assert (ZSLE : zsum (lacing_of (ubytes hs)) <= pg_body_len og) by (rewrite ZSEQ, zlength_ubytes; lia).
assert (PGIN' : pg_hdr og + pg_header_len og + pg_body_len og <= sy_storage (h_oy h)) by lia.
unfold HO_OS, HO_OG in OS, OGC.
Time cps_rt (PGIN Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (x_F X + 8688) (x_F X + 8544) (a_Dsy a)
(sy_storage (h_oy h)) (a_Bd a) (a_L a) (a_G a) (x_F X) (x_lo X) 8%nat og (h_os h) (a_shdr a) hs bs (a_body a) (a_lws a) (a_gws a) q q2 ro).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ change (fs_size 8) with 16384. lia. }
{ change (fs_size 8) with 16384. lia. }
{ exact (af_credit_nonneg RT AF Σ1 m ART). }
{ rewrite unsigned_lit by lia. exact ST. }
{ rewrite unsigned_lit by lia. unfold RT_STACK, H_STACK in *. lia. }
{ rewrite unsigned_lit by lia. unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by lia. clear - S32. Z.div_mod_to_equations. lia. }
intros c2 (Σ2 & Bd' & L' & Gv' & Hc2 & EQQ & ERES & SLV' & EL2 & SAME & EF2 & ES2 & EC2 & EP2). clear Hc.
Time cps_unpack_lib Hc2 as (m2 & body' & lws' & gws' & RS & RA & PR & OS' & ARR').
destruct RS as (-> & ->).
unfold bptr in *.

assert (LFS : os_lacing_fill (h_os h) <= os_lacing_storage (h_os h)).
{ destruct ARR as (_ & _ & _ & _ & (_ & WL) & LL & _). pose proof SINVo as (_ & _ & ZL & _). unfold zlength in ZL. unfold bptr in *. lia. }
assert (BFS : os_body_fill (h_os h) <= os_body_storage (h_os h)).
{ destruct ARR as (_ & LB & (_ & BL) & _). pose proof BINV as (ZB & _). unfold zlength in ZB. unfold bptr in *. lia. }
destruct (hpure_pagein OUT_rep IO_FP X HX h og hs (ubytes bs) HP PBUD
(conj FOK (conj SINVo (conj BINV (conj LOK (conj GL (conj BD (conj LV (conj GV (conj LS BS)))))))))
LFS BFS LENH LHS ltac:(rewrite zlength_ubytes; exact LBS) (ubytes_ok bs) ZSEQ) as (POS' & HP').
subst ro.
destruct (hrep_pagein RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 Σ2 m m2 a h _ _ _ hs (ubytes bs) Bd' L' Gv' body' lws' gws'
HS HR ltac:(reflexivity) ltac:(reflexivity) ltac:(destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->); reflexivity)
ltac:(rewrite SI1; discriminate) RA PR OS' ARR' SLV' EL2 SAME EF2 ES2 EC2 EP2 POS' HP') as (HS3 & HR3).
apply Hk. split; [exact EQQ|].
exists Σ2, (a_set_os a Bd' L' Gv' (a_shdr a) body' lws' gws' (pagein_live (a_P a) (h_os h) (ubytes hs) (ubytes bs) (a_Bd a) (a_L a) (a_G a) Bd' L' Gv')),
Fx, fc, m2, r, r0, r1, (wz (fst (pagein_res (h_os h) (ubytes hs) (ubytes bs)))), r2, r3, r4, r6, r7, r8, r9, r5, r10, r11, r12, r13, j0, j192, j200, opc.
split; [unfold h_regs; cbn [set_ogg h_packet_count h_last_granule a_set_os a_S]; exact Hc|].
split; [exact FRM|]. split; [exact HS3|]. split; [exact HIT|]. split; [exact SI1|].
split; [exact HR3|]. split; [exact OPJ| exact POK].
Qed.

Theorem h_p2_ok : hinv_ok OUT_rep IO_FP X -> forall (h1 : hstate unit) (og : page) (nbr brem0 : Z) (q q2 : pst) ro,
prun (ogg_stream_pagein (St := pst) p_realloc p_free (h_os (pb_h2 h1 (ogg_page_serialno (page_header (h_oy h1) og))))
(page_header (h_oy h1) og) (page_body (h_oy h1) og)) q = Some (ro, q2) ->
cps asegs (at_P2 RT OUT_rep ERR_rep IO_FP X F0 fs0 h1 og nbr brem0)
(fun c => q2 = q /\ page_post RT OUT_rep ERR_rep IO_FP X F0 fs0 (set_ogg (pb_h2 h1 (ogg_page_serialno (page_header (h_oy h1) og))) (h_oy h1) (snd ro))
(page_header (h_oy h1) og) nbr brem0 c).
Proof using AF ERR_loc OUT_loc IO_img AF_DRV PGIN CLEAN.
intros HX h1 og nbr brem0 q q2 ro RUN T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & r5 & t3 & t4 & t5 & t6 & j0 & j192 & j200 & opc
& Hc & FRM & HS & HIT & SI1 & HR & OPJ & POK & PBUD).
pose proof HR as HR'. destruct HR' as (ART & MI & ST & _ & _ & _ & _ & SP & _ & _ & _ & FSZ & _ & SY & OGC & _ & OSR & _ & _ & _ & _ & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h1 ART HS) as HSP.
unfold h_regs in Hc.
pose proof HP as (SI2 & SINV & _ & (SDN & SND) & _).
assert (NN : sy_data (h_oy h1) <> None).
{ intros E. pose proof SY as (_ & _ & DAT & _). unfold sync_data in DAT. unfold bptr in *. rewrite E in DAT.
destruct DAT as (_ & _ & EB & _). pose proof POK as (P0 & P1 & P2 & P3 & P4 & P5 & P6). rewrite EB in P5.
unfold zlength in P5. cbn [length Z.of_nat] in P5. lia. }
destruct (page_hs_a m _ _ _ _ og SY SINV POK NN) as (HSB & BSB & LHS & LBS & EHS & EBS & HL27 & N26 & PG0 & PGE & BL0).
unfold bptr in EHS, EBS.
set (hs := firstn (Z.to_nat (pg_header_len og)) (skipn (Z.to_nat (pg_hdr og)) (a_sybytes a))) in *.
unfold h_os_rep in OSR. destruct (Z.eqb_spec (h_stream_init h1) 0) as [E0|_]; [rewrite SI1 in E0; discriminate E0|].
destruct OSR as (OS & LH & ARR & FOK & SINVo & BINV & LOK & GL & BD & LV & GV & LS & BS & NBL & NBG & NLG).
destruct (own_in_os a h1 ltac:(rewrite SI1; discriminate)) as (IB & IL & IG).
destruct (proj1 HSP _ _ IB) as (B0 & BLO & _).
unfold HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS in Hc, OS, OGC.
refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply (pb_w2 (x_F X) (a_Dsy a) (a_Bd a) (a_L a) (a_G a) og hs (a_shdr a) (h_os h1));
[lia| unfold RT_STACK, H_STACK, USTACK_TOP in *; lia| exact LH| exact FOK| exact BD| exact OS| exact OGC| exact HSB| lia| exact MI]. }
intros ms1 c1 POST Hc1. clear Hc.
destruct POST as (m1 & os1 & t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & CASE & MI1 & OS1 & ->).
pose proof (h_s32_range (le32_at (ubytes hs) 14)) as SRr. fold (ogg_page_serialno (ubytes hs)) in SRr.

assert (TAIL : forall (h2 : hstate unit) (Σ2 : rts RT) (m2 : mem), h_oy h2 = h_oy h1 ->
pb_h2 h1 (ogg_page_serialno (page_header (h_oy h1) og)) = h2 ->
at_PC RT OUT_rep ERR_rep IO_FP X F0 fs0 h2 og nbr brem0 c1 -> realizes asegs c1 T).
{ intros h2 Σ2 m2 EOY E2 HPC. rewrite E2 in RUN, Hk. rewrite <- EOY in RUN.
refine (h_pc_ok HX h2 og nbr brem0 q q2 ro RUN T c1 HPC _).
intros c3 (EQQ & Hc3). refine (h_p3_ok HX _ og nbr brem0 T c3 Hc3 _).
intros c4 Hc4. apply Hk. split; [exact EQQ|]. cbn [set_ogg h_oy] in Hc4. rewrite EOY in Hc4. exact Hc4. }
destruct CASE as [(EQ & -> & ->) | (NE & -> & MU & WM & FOK1)].
-
apply (TAIL h1 Σ1 m eq_refl).
{ unfold pb_h2. rewrite <- EHS, EQ, Z.eqb_refl. reflexivity. }
exists Σ1, a, Fx, fc, m, t0', t1', t2', a2', a3', a4', a5', a6', a7', r5, t3', t4', t5', t6', j0, j192, j200, opc.
split; [unfold h_regs; unfold HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; exact Hc1|].
split; [exact FRM|]. split; [exact HS|]. split; [exact HIT|]. split; [exact SI1|]. split; [exact HR|].
split; [exact OPJ|]. split; [exact POK| exact PBUD].
-
destruct (hrep_reset RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 m m1 a h1 _ _ _ (ogg_page_serialno (ubytes hs)) HS HR
ltac:(reflexivity) ltac:(reflexivity) ltac:(destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->); reflexivity)
ltac:(rewrite SI1; discriminate) SRr MU WM MI1 OS1) as (HS2 & HR2).
destruct (reset_os_pure (h_os h1) (ogg_page_serialno (ubytes hs)) (conj FOK (conj SINVo (conj BINV (conj LOK (conj GL (conj BD (conj LV (conj GV (conj LS BS))))))))) SRr)
as (_ & ELS & EBS' & ELF & EBF & ELR & _).
unfold bptr in *.
apply (TAIL (set_ogg h1 (h_oy h1) (snd (ogg_stream_reset_serialno (h_os h1) (ogg_page_serialno (ubytes hs))))) Σ1 m1 eq_refl).
{ unfold pb_h2. rewrite <- EHS. destruct (Z.eqb_spec (ogg_page_serialno (ubytes hs)) (os_serialno (h_os h1))) as [E|_]; [exfalso; exact (NE (eq_sym E))|].
reflexivity. }
exists Σ1, a, Fx, fc, m1, t0', t1', t2', a2', a3', a4', a5', a6', a7', r5, t3', t4', t5', t6', j0, j192, j200, opc.
split; [unfold h_regs; cbn [set_ogg h_packet_count h_last_granule]; unfold HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; exact Hc1|].
split; [exact FRM|]. split; [exact HS2|]. split; [exact HIT|]. split; [exact SI1|]. split; [exact HR2|].
split; [exact OPJ|]. split; [exact POK|].
rewrite set_ogg_with. apply budget_with_os; [exact PBUD| exact ELF| exact EBF| exact ELR| rewrite ELS; lia| rewrite EBS'; lia].
Qed.

Theorem h_page_ok : h_page_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Proof using AF ERR_loc OUT_loc IO_img AF_DRV SINIT PGIN CLEAN.
intros HX h og nbr brem0 q q3 h3 RUN T c Hc Hk.
destruct (pb_pre_run h og q h3 q3 RUN) as (ro & RUN2 & ->). clear RUN.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a0 & a3 & a4 & a5 & a6 & a7 & r5 & r8 & t3 & t4 & t5 & t6 & j0 & j192 & j200 & opc
& Hc & FRM & HS & HIT & HR & OPJ & POK & PBUD).
pose proof HR as HR'. destruct HR' as (ART & MI & ST & PF & _ & _ & _ & SP & _ & _ & _ & FSZ & _ & SY & OGC & _ & OSR & _ & _ & _ & _ & HP).
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
unfold h_regs in Hc.
pose proof HP as (SI2 & SINV & _ & (SDN & SND) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SIR & _).
assert (NN : sy_data (h_oy h) <> None).
{ intros E. pose proof SY as (_ & _ & DAT & _). unfold sync_data in DAT. unfold bptr in *. rewrite E in DAT.
destruct DAT as (_ & _ & EB & _). pose proof POK as (P0 & P1 & P2 & P3 & P4 & P5 & P6). rewrite EB in P5.
unfold zlength in P5. cbn [length Z.of_nat] in P5. lia. }
destruct (page_hs_a m _ _ _ _ og SY SINV POK NN) as (HSB & BSB & LHS & LBS & EHS & EBS & HL27 & N26 & PG0 & PGE & BL0).
unfold bptr in EHS, EBS.
set (hs := firstn (Z.to_nat (pg_header_len og)) (skipn (Z.to_nat (pg_hdr og)) (a_sybytes a))) in *.
pose proof (h_s32_range (le32_at (ubytes hs) 14)) as SRr. fold (ogg_page_serialno (ubytes hs)) in SRr.
unfold HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS in Hc, OGC.
refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply (pb_w1 (x_F X) (a_Dsy a) og hs (h_stream_init h) (h_last_granule h)); [exact SIR| exact OGC| exact HSB| lia| exact MI]. }
intros ms1 c1 POST Hc1. clear Hc.
destruct POST as [(SI0 & t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->) | (SI1 & ->)].
2:{
assert (E1 : pb_h1 h (ogg_page_serialno (page_header (h_oy h) og)) = h) by (unfold pb_h1; rewrite SI1; reflexivity).
rewrite E1 in RUN2, Hk.
refine (h_p2_ok HX h og nbr brem0 q q3 ro RUN2 T c1 _ _).
- exists Σ1, a, Fx, fc, m, ra, t0, t1, t2, a0, (Z64 0), (Z64 (h_last_granule h)), a3, a4, a5, a6, a7, r5, t3, t4, t5, t6, j0, j192, j200, opc.
split; [unfold h_regs; unfold HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; exact Hc1|].
split; [exact FRM|]. split; [exact HS|]. split; [exact HIT|]. split; [exact SI1|]. split; [exact HR|].
split; [exact OPJ|]. split; [exact POK| exact PBUD].
- intros c2 (EQQ & Hc2). apply Hk. split; [exact EQQ|]. exact Hc2. }

unfold h_os_rep in OSR. rewrite SI0 in OSR. cbn [Z.eqb] in OSR. destruct OSR as ((jos & OSJ) & EOS0).
pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m PF) as (_ & _ & _ & _ & _ & _ & ACOS & _).
unfold HO_OS in OSJ, ACOS.
assert (INF : In (x_F X, 8%nat) (rt_frames RT Σ1)) by (rewrite EF; left; reflexivity).
assert (LV3 : Z.of_nat (length (rt_live RT Σ1)) + 3 <= LIVE_MAX).
{ rewrite (h_live_len RT X Σ1 a h HS).
assert (L21 : (length (h_own a h) <= 21)%nat).
{ pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DEC & _).
unfold h_own. rewrite SI0. cbn [Z.eqb]. rewrite !length_app. unfold h_dec_rep in DEC.
destruct (h_st h) as [d|]; [destruct DEC as (_ & _ & _ & _ & _ & _ & _ & _ & LL)|];
destruct (sy_data (h_oy h)); cbn [length]; unfold blocks_live; rewrite ?length_map; lia. }
pose proof (hi_live _ _ _ HX) as (_ & LL). unfold H_LIVE in LL. lia. }
Time cps_rt (SINIT Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (x_F X + 8688) (ogg_page_serialno (ubytes hs))
(x_F X) (x_lo X) 8%nat jos).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ change (fs_size 8) with 16384. lia. }
{ exact (af_credit_nonneg RT AF Σ1 m ART). }
{ rewrite unsigned_lit by (unfold USTACK_TOP in UT; lia). exact ST. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in UT; lia). unfold RT_STACK, H_STACK in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in UT; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in UT; lia). clear - S32. Z.div_mod_to_equations. lia. }
intros c2 (Σ2 & Bd & L & G & Hc2 & EL2 & EF2 & ES2 & EC2 & EP2 & SLV2 & AB & AL & AG). clear Hc1.
Time cps_unpack_lib Hc2 as (m2 & jb & lws & gws & RS & RA & PR & OS2 & UB & LB & UL & LL & UG & LG).
destruct RS as (-> & ->).
destruct (hrep_sinit RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV X HX Σ1 Σ2 m m2 a h _ _ _ (ogg_page_serialno (ubytes hs)) Bd L G jb lws gws
HS HR ltac:(reflexivity) ltac:(reflexivity) ltac:(destruct OPJ as (k0 & k1 & k2 & k3 & k4 & k5 & ->); reflexivity)
SI0 SRr RA PR OS2 UB LB UL LL UG LG EL2 EF2 ES2 EC2 EP2 SLV2) as (HS1 & HR1).
assert (E1 : pb_h1 h (ogg_page_serialno (page_header (h_oy h) og)) = set_stream_init h (init_os (Some tt) (Some tt) (Some tt) (ogg_page_serialno (ubytes hs))))
by (unfold pb_h1; rewrite SI0, <- EHS; reflexivity).
rewrite E1 in RUN2, Hk.
replace (ret_pc (Z64 617608)) with (Z64 617608) in Hc by (symmetry; apply ret_pc_even; [lia | reflexivity]).
refine (h_p2_ok HX _ og nbr brem0 q q3 ro RUN2 T c2 _ _).
- exists Σ2, (a_set_os a Bd L G zero_hdr jb lws gws ((G, 8192) :: (L, 4096) :: (Bd, 16384) :: a_P a)), Fx, fc, m2,
(Z64 617608), r, r0, r1, (Z64 0), r2, r3, r4, r6, r7, r9, r10, r5, r11, r12, r13, r14, j0, j192, j200, opc.
split; [unfold h_regs; cbn [set_stream_init h_packet_count h_last_granule a_set_os a_S]; unfold HO_OP, HO_OUT, HO_OS, HO_OG, HO_BITS; exact Hc|].
split; [exact FRM|]. split; [exact HS1|]. split; [exact HIT|]. split; [reflexivity|]. split; [exact HR1|].
split; [exact OPJ|]. split; [exact POK|].
rewrite set_stream_init_with. apply budget_with_os; [exact PBUD| reflexivity| reflexivity| reflexivity| |];
cbn [init_os os_lacing_storage os_body_storage]; lia.
- intros c3 (EQQ & Hc3). apply Hk. split; [exact EQQ|]. exact Hc3.
Qed.
End Page.
