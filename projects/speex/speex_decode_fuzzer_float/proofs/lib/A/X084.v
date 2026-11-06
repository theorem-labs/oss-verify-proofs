(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X089 X08a X087 X088.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0wm X12a X0z0 X0z1 X0yx X0yy X0yz.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yx OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yy OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yz.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma l2l8_rr1 : forall usp, usp mod 32 = 0 -> alloca_rr (usp + -256) 72 = usp + -128.
Proof. intros usp H. unfold alloca_rr. Z.div_mod_to_equations. lia. Qed.
Lemma l2l8_rr2 : forall usp, usp mod 32 = 0 -> alloca_rr (usp + -352) 32 = usp + -288.
Proof. intros usp H. unfold alloca_rr. Z.div_mod_to_equations. lia. Qed.

Section L2L8.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN : allocas_unpoison_contract RT.

Theorem lsp_to_lpc8_ok : lsp_to_lpc_cps8 RT.
Proof using AF APO AUN.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m IQ AK lo qs aks
FDO MST -> -> -> -> X LQ A LA INQ INA APQA FRN POA FRM ART0 MI0 ST0 LOW LOR SPT U32.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.

pose proof (POA _ INQ) as PQ. pose proof (POA _ INA) as PA. unfold pz_lo in PQ, PA. cbn [fst] in PQ, PA.
pose proof (af_pois_range RT AF Σ m IQ 32 ART0 INQ) as (Q32 & _ & _ & RQ). pose proof (af_pois_range RT AF Σ m AK 32 ART0 INA) as (A32 & _ & _ & RA).
assert (Q4 : IQ mod 4 = 0) by (clear - Q32; Z.div_mod_to_equations; lia). assert (A4 : AK mod 4 = 0) by (clear - A32; Z.div_mod_to_equations; lia).
pose proof (alloca_rr_bounds IQ 32) as (BQ & _). pose proof (alloca_rr_bounds AK 32) as (BA & _).
pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
assert (LOSH : SH_HI <= lo) by (clear - SPW LOW; unfold SH_HI, STACK_WIN in *; lia).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(AK, AK + 32)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
cps_norm. cps_hide.

cps_seg (l2l8_w1 IQ AK usp lo).
destruct POST as (j1 & j2 & jh & m1 & a2w & a3w & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HULL1).
unfold l2l_frame in FR1. cps_seg_post.

assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -288)) = usp + -288) by (apply unsigned_lit; ulc).
cps_rt (APO Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -256) 72 lo).
{ rewrite (l2l8_rr1 usp U32). ulc. }
{ rewrite (l2l8_rr1 usp U32). apply (pois_above_le _ usp); [exact POA| lia]. }
{ cps_callok. }
intros c2 (Σ1 & Hc2 & PO1 & LV1 & FRS1 & SP1 & CR1).
cps_unpack Hc2 as (m2 & v1 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACW & ACT2).
cps_sigma LV1 FRS1 SP1.
assert (INW : In (usp + -256, 72) (rt_pois RT Σ1)) by (rewrite PO1; left; reflexivity).

apply (rw_cells_split_CB bsegs _ _ [] 160 _ [] [32; 72; 56]%nat) in HULL1; [| reflexivity]. cbn [mk_CB_cells app] in HULL1.
chunk_uncons HULL1 as RZ1. chunk_uncons HULL1 as WP. rename HULL1 into PAD1.
replace (usp + -288 + 32) with (usp + -256) in * by (clear; lia). replace (usp + -256 + 72) with (usp + -184) in * by (clear; lia).
assert (OBW2 : aobj bsegs m2 (usp + -256) 72) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ1 m2 _ _ ART2 INW)).
cps_seg (l2l8_w2 IQ AK usp lo).
destruct POST as (jh2 & ws & m5 & a2x & a3x & a4x & -> & MU5 & WM5 & MI5 & ST5 & FR3 & WP5 & LWP5 & HULL2). clear FR1 WP.
clear OBW2. unfold l2l_frame in FR3. cps_seg_post.
assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -384)) = usp + -384) by (apply unsigned_lit; ulc).
cps_rt (APO Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (usp + -352) 32 lo).
{ rewrite (l2l8_rr2 usp U32). ulc. }
{ rewrite (l2l8_rr2 usp U32), PO1. apply pois_above_cons; [rewrite (l2l8_rr1 usp U32); apply (pois_above_le _ usp); [exact POA| lia]| lia| lia]. }
{ rewrite FRS1. exact FRN. }
{ cps_callok. }
intros c6 (Σ2 & Hc6 & PO2 & LV2 & FRS2 & SP2 & CR2).
cps_unpack Hc6 as (m6 & v6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & ACX & ACT6).
cps_sigma LV2 FRS2 SP2.
assert (INX : In (usp + -352, 32) (rt_pois RT Σ2)) by (rewrite PO2; left; reflexivity).
assert (INW2 : In (usp + -256, 72) (rt_pois RT Σ2)) by (rewrite PO2; right; exact INW).
assert (INQ2 : In (IQ, 32) (rt_pois RT Σ2)) by (rewrite PO2, PO1; right; right; exact INQ).
assert (INA2 : In (AK, 32) (rt_pois RT Σ2)) by (rewrite PO2, PO1; right; right; exact INA).

apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [32; 32; 32]%nat) in HULL2; [| reflexivity]. cbn [mk_CB_cells app] in HULL2.
chunk_uncons HULL2 as RZ2. chunk_uncons HULL2 as XF. rename HULL2 into PAD2.
replace (usp + -384 + 32) with (usp + -352) in * by (clear; lia). replace (usp + -352 + 32) with (usp + -320) in * by (clear; lia).

assert (OBW : aobj bsegs m6 (usp + -256) 72) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m6 _ _ ART6 INW2)).
assert (OBX : aobj bsegs m6 (usp + -352) 32) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m6 _ _ ART6 INX)).
assert (OBQ : aobj bsegs m6 IQ 32) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m6 _ _ ART6 INQ2)).
assert (OBA : aobj bsegs m6 AK 32) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m6 _ _ ART6 INA2)).
change (rw_cells bsegs m6 (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -288)) j1 j2 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) in FR3.
cps_seg (l2l8_body IQ AK usp lo qs aks ws).
{ right. ulc. } { ulc. } { ulc. }
destruct POST as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s9' & s10' & s11'
& t3' & t4' & t5' & t6' & F' & fc' & m7 & aks' & jw & jx' & -> & MU7 & WM7 & MI7 & FRM7 & FR7 & WP7 & XF7 & X7 & A7 & LA7).
clear FR3 WP5 XF X A OBW OBX OBQ OBA. unfold l2l_frame in FR7.
assert (ST6' : stk bsegs m6 lo (usp + -384)) by exact ST6.
cps_seg_post.

change (rw_cells bsegs m7 (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -384)) j1 j2 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) in FR7.
cps_seg (l2l8_w5 usp lo).
subst ms.
cps_rt (AUN Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 (usp + -384) (usp + -128) lo).
{ rewrite PO2, PO1. intros e [<-|[<-|He]].
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite (l2l8_rr2 usp U32). clear. lia.
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite (l2l8_rr1 usp U32). clear. lia.
- right. pose proof (POA e He). lia. }
{ cps_callok. }
intros c8 (Σ3 & Hc8 & PO3 & LV3 & FRS3 & SP3 & CR3).
cps_unpack Hc8 as (m8 & v8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & ACT8).

chunk_cat RZ1 WP7. chunk_cat RZ1 PAD1. apply rw_cells_to_CB in RZ1. cbn [cells_size csize Nat.add] in RZ1.
chunk_cat RZ2 XF7. chunk_cat RZ2 PAD2. apply rw_cells_to_CB in RZ2. cbn [cells_size csize Nat.add] in RZ2.
change (rw_cells bsegs m8 (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -384)) j1 j2 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) in FR7.
cps_seg (l2l8_w6 usp lo _ _ (usp + -384)).
destruct POST as (-> & ST9).
apply Hk. exists Σ3. split.
2:{ split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
rewrite PO3, PO2, PO1. rewrite !pois_drop_cons_below by (unfold pz_lo; cbn [fst]; clear; lia).
apply pois_drop_above. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v8, m8, aks'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM7]|].
split. { split; [exact ART8|]. split; [exact MI8|]. split; [cps_wmono| exact ST9]. }
split; [exact PF|]. split; [exact A7| exact LA7].
Qed.
End L2L8.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma l2l8_rr1 : forall usp, usp mod 32 = 0 -> alloca_rr (usp + -256) 72 = usp + -128.
Proof. intros usp H. unfold alloca_rr. Z.div_mod_to_equations. lia. Qed.
Lemma l2l8_rr2 : forall usp, usp mod 32 = 0 -> alloca_rr (usp + -352) 32 = usp + -288.
Proof. intros usp H. unfold alloca_rr. Z.div_mod_to_equations. lia. Qed.

Section L2L8.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN : allocas_unpoison_contract RT.
Hypothesis MEMS : memset_icontract RT e_asan_memset.

Theorem lsp_to_lpc8_ok : lsp_to_lpc_cps8 RT.
Proof using AF APO AUN MEMS.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m IQ AK lo qs aks
FDO MST -> -> -> -> X LQ A LA INQ INA APQA FRN POA FRM ART0 MI0 ST0 LOW LOR SPT U32.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.

pose proof (POA _ INQ) as PQ. pose proof (POA _ INA) as PA. unfold pz_lo in PQ, PA. cbn [fst] in PQ, PA.
pose proof (af_pois_range RT AF Σ m IQ 32 ART0 INQ) as (Q32 & _ & _ & RQ). pose proof (af_pois_range RT AF Σ m AK 32 ART0 INA) as (A32 & _ & _ & RA).
assert (Q4 : IQ mod 4 = 0) by (clear - Q32; Z.div_mod_to_equations; lia). assert (A4 : AK mod 4 = 0) by (clear - A32; Z.div_mod_to_equations; lia).
pose proof (alloca_rr_bounds IQ 32) as (BQ & _). pose proof (alloca_rr_bounds AK 32) as (BA & _).
pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
assert (LOSH : SH_HI <= lo) by (clear - SPW LOW; unfold SH_HI, STACK_WIN in *; lia).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(AK, AK + 32)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
cps_norm. cps_hide.

cps_seg (l2l8_w1 IQ AK usp lo).
destruct POST as (j1 & j2 & jh & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HULL1).
unfold l2l_frame in FR1. cps_seg_post.

assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -288)) = usp + -288) by (apply unsigned_lit; ulc).
cps_rt (APO Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -256) 72 lo).
{ rewrite (l2l8_rr1 usp U32). ulc. }
{ rewrite (l2l8_rr1 usp U32). apply (pois_above_le _ usp); [exact POA| lia]. }
{ cps_callok. }
intros c2 (Σ1 & Hc2 & PO1 & LV1 & FRS1 & SP1 & CR1).
cps_unpack Hc2 as (m2 & v1 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACW & ACT2).
cps_sigma LV1 FRS1 SP1.
assert (INW : In (usp + -256, 72) (rt_pois RT Σ1)) by (rewrite PO1; left; reflexivity).

cps_seg (l2l8_w2 IQ AK usp lo).
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & FR3). clear FR1. cps_seg_post.

apply (rw_cells_split_CB asegs _ _ [] 160 _ [] [32; 72; 56]%nat) in HULL1; [| reflexivity]. cbn [mk_CB_cells app] in HULL1.
chunk_uncons HULL1 as RZ1. chunk_uncons HULL1 as WP. rename HULL1 into PAD1.
replace (usp + -288 + 32) with (usp + -256) in * by (clear; lia). replace (usp + -256 + 72) with (usp + -184) in * by (clear; lia).
set (jw0 := firstn 72 (skipn 32 jh)) in *.

pose proof (af_pois_range RT AF Σ1 m3 _ _ ART INW) as (_ & _ & RW1 & RW2). rewrite (l2l8_rr1 usp U32) in RW2.
pose proof WP as [_ WRW]. cbn [cells_size csize Nat.add] in WRW. change (Z.of_nat 72) with 72 in WRW.
cps_rt (MEMS Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (usp + -256) 72 z8 lo).
{ unfold checked_dst. rewrite unsigned_lit by ulc. split; [intros _; split|split].
- exact (af_acc_pois RT AF Σ1 m3 _ _ ART INW).
- right; right; left. split; [ulc| ulc].
- intros i Hi. left. ulc.
- exact WRW. }
{ cps_callok. }
intros c4 Hc4.
cps_unpack Hc4 as (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BYW).
assert (WP4 : rw_cells asegs m4 (usp + -256) [CB 72 (repeat z8 72)]).
{ split; [split; [split; [reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BYW]|].
cbn [cells_size csize Nat.add]. exact (wr_at_transport asegs m3 m4 _ _ WRW WM4). }
clear WRW BYW.

cps_seg (l2l8_w3 IQ AK usp lo).
destruct POST as (jh2 & m5 & -> & MU5 & WM5 & MI5 & ST5 & HULL2). unfold l2l_frame in FR3. cps_seg_post.
assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -384)) = usp + -384) by (apply unsigned_lit; ulc).
cps_rt (APO Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (usp + -352) 32 lo).
{ rewrite (l2l8_rr2 usp U32). ulc. }
{ rewrite (l2l8_rr2 usp U32), PO1. apply pois_above_cons; [rewrite (l2l8_rr1 usp U32); apply (pois_above_le _ usp); [exact POA| lia]| lia| lia]. }
{ rewrite FRS1. exact FRN. }
{ cps_callok. }
intros c6 (Σ2 & Hc6 & PO2 & LV2 & FRS2 & SP2 & CR2).
cps_unpack Hc6 as (m6 & v6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & ACX & ACT6).
cps_sigma LV2 FRS2 SP2.
assert (INX : In (usp + -352, 32) (rt_pois RT Σ2)) by (rewrite PO2; left; reflexivity).
assert (INW2 : In (usp + -256, 72) (rt_pois RT Σ2)) by (rewrite PO2; right; exact INW).
assert (INQ2 : In (IQ, 32) (rt_pois RT Σ2)) by (rewrite PO2, PO1; right; right; exact INQ).
assert (INA2 : In (AK, 32) (rt_pois RT Σ2)) by (rewrite PO2, PO1; right; right; exact INA).

apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [32; 32; 32]%nat) in HULL2; [| reflexivity]. cbn [mk_CB_cells app] in HULL2.
chunk_uncons HULL2 as RZ2. chunk_uncons HULL2 as XF. rename HULL2 into PAD2.
replace (usp + -384 + 32) with (usp + -352) in * by (clear; lia). replace (usp + -352 + 32) with (usp + -320) in * by (clear; lia).

assert (OBW : aobj asegs m6 (usp + -256) 72) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m6 _ _ ART6 INW2)).
assert (OBX : aobj asegs m6 (usp + -352) 32) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m6 _ _ ART6 INX)).
assert (OBQ : aobj asegs m6 IQ 32) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m6 _ _ ART6 INQ2)).
assert (OBA : aobj asegs m6 AK 32) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m6 _ _ ART6 INA2)).
change (rw_cells asegs m6 (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -288)) j1 j2 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) in FR3.
cps_seg (l2l8_body IQ AK usp lo qs aks).
{ right. ulc. } { ulc. } { ulc. }
destruct POST as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s9' & s10' & s11'
& t3' & t4' & t5' & t6' & F' & fc' & m7 & aks' & jw & jx' & -> & MU7 & WM7 & MI7 & FRM7 & FR7 & WP7 & XF7 & X7 & A7 & LA7).
clear FR3 WP4 XF X A OBW OBX OBQ OBA. unfold l2l_frame in FR7.
assert (ST6' : stk asegs m6 lo (usp + -384)) by exact ST6.
cps_seg_post.

change (rw_cells asegs m7 (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -384)) j1 j2 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) in FR7.
cps_seg (l2l8_w5 usp lo).
subst ms.
cps_rt (AUN Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 (usp + -384) (usp + -128) lo).
{ rewrite PO2, PO1. intros e [<-|[<-|He]].
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite (l2l8_rr2 usp U32). clear. lia.
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite (l2l8_rr1 usp U32). clear. lia.
- right. pose proof (POA e He). lia. }
{ cps_callok. }
intros c8 (Σ3 & Hc8 & PO3 & LV3 & FRS3 & SP3 & CR3).
cps_unpack Hc8 as (m8 & v8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & ACT8).

chunk_cat RZ1 WP7. chunk_cat RZ1 PAD1. apply rw_cells_to_CB in RZ1. cbn [cells_size csize Nat.add] in RZ1.
chunk_cat RZ2 XF7. chunk_cat RZ2 PAD2. apply rw_cells_to_CB in RZ2. cbn [cells_size csize Nat.add] in RZ2.
change (rw_cells asegs m8 (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -384)) j1 j2 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) in FR7.
cps_seg (l2l8_w6 usp lo _ _ (usp + -384)).
destruct POST as (-> & ST9).
apply Hk. exists Σ3. split.
2:{ split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
rewrite PO3, PO2, PO1. rewrite !pois_drop_cons_below by (unfold pz_lo; cbn [fst]; clear; lia).
apply pois_drop_above. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v8, m8, aks'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM7]|].
split. { split; [exact ART8|]. split; [exact MI8|]. split; [cps_wmono| exact ST9]. }
split; [exact PF|]. split; [exact A7| exact LA7].
Qed.
End L2L8.
