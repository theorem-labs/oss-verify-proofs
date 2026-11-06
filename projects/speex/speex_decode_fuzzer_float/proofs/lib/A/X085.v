(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X05t X089 X086.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0wm X12a X0z0 X0yx.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yx.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma l2lF_rr1 : forall usp, usp mod 32 = 0 -> alloca_rr (usp + -256) 88 = usp + -128.
Proof. intros usp H. unfold alloca_rr. Z.div_mod_to_equations. lia. Qed.
Lemma l2lF_rr2 : forall usp, usp mod 32 = 0 -> alloca_rr (usp + -384) 40 = usp + -288.
Proof. intros usp H. unfold alloca_rr. Z.div_mod_to_equations. lia. Qed.

Section L2LF.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN : allocas_unpoison_contract RT.

Definition lsp_to_lpc_cpsF : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (IQ AK lo fq : Z) (kq : nat) (qs aks : list word),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 IQ -> a1 = Z_to_bv 64 AK -> a2 = Z_to_bv 64 10 -> tp = Z_to_bv 64 0x638c98 ->
rw_cells bsegs m IQ (f32 qs) -> length qs = 10%nat -> rw_cells bsegs m AK (f32 aks) -> length aks = 10%nat ->

In (fq, kq) (rt_frames RT Σ) -> fq <= IQ -> IQ + 40 <= fq + fs_size kq - 8 -> fq <= AK -> AK + 40 <= fq + fs_size kq - 8 ->
acc bsegs m IQ 40 -> acc bsegs m AK 40 -> IQ mod 4 = 0 -> AK mod 4 = 0 -> (AK + 40 <= IQ \/ IQ + 40 <= AK) ->
pois_above (rt_pois RT Σ) (bv_unsigned sp) -> X1cn.frm0 fc ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 416 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc 0xae6d8 m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m' aks',
ret_stL (fun F' fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(AK, AK + 40)] m m'
/\ rw_cells bsegs m' AK (f32 aks') /\ length aks' = 10%nat
/\ acc bsegs m' IQ 40 /\ acc bsegs m' AK 40) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem lsp_to_lpcF_ok : lsp_to_lpc_cpsF.
Proof using AF APO AUN.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m IQ AK lo fq kq qs aks
FDO MST -> -> -> -> X LQ A LA INF FQL FQH FAL FAH ACQ ACA Q4 A4 APQA POA FRM ART0 MI0 ST0 LOW LOR SPT U32.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
assert (FRN : rt_frames RT Σ <> []) by (intros E; rewrite E in INF; exact INF).
destruct (frame_below_lo RT AF Σ m fq kq lo ART0 INF LOW) as (BF0 & _ & _).
pose proof (frame_facts RT AF Σ m fq kq ART0 INF) as (FF0 & FF1 & FF2 & _ & FF4 & _).
assert (FP8 : fq mod 8 = 0) by (clear - FF1; Z.div_mod_to_equations; lia).
pose proof (fs_size_mod8 kq) as FS8.
pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
assert (LOSH : SH_HI <= lo) by (clear - SPW LOW; unfold SH_HI, STACK_WIN in *; lia).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(AK, AK + 40)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (FSZ : 0 <= fs_size kq) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
cps_norm.
assert (SHQ : forall i, 0 <= i < 40 -> SH_LO <= shad (IQ + i) < SH_HI) by (intros i Hi; apply shad_in_window; clear - Hi FQH FF0 FQL BF0 LOR SPT; lia).
assert (SHA : forall i, 0 <= i < 40 -> SH_LO <= shad (AK + i) < SH_HI) by (intros i Hi; apply shad_in_window; clear - Hi FAH FF0 FAL BF0 LOR SPT; lia).
cps_hide.

cps_seg (l2l_w1 IQ AK usp lo).
destruct POST as (j1 & j2 & jh & m1 & a2w & a3w & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HULL1).
assert (ACQ1 : acc bsegs m1 IQ 40) by (refine (proj2 (proj2 (aobj_munch bsegs _ m m1 IQ 40 _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACQ]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
assert (ACA1 : acc bsegs m1 AK 40) by (refine (proj2 (proj2 (aobj_munch bsegs _ m m1 AK 40 _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACA]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
unfold l2l_frame in FR1. cps_seg_post.
assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -288)) = usp + -288) by (apply unsigned_lit; ulc).
cps_rt (APO Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -256) 88 lo).
{ rewrite (l2lF_rr1 usp U32). ulc. }
{ rewrite (l2lF_rr1 usp U32). apply (pois_above_le _ usp); [exact POA| lia]. }
{ cps_callok. }
intros c2 (Σ1 & Hc2 & PO1 & LV1 & FRS1 & SP1 & CR1).
cps_unpack Hc2 as (m2 & v1 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACW & ACT2).
cps_sigma LV1 FRS1 SP1.
assert (INW : In (usp + -256, 88) (rt_pois RT Σ1)) by (rewrite PO1; left; reflexivity).
assert (ACQ2 : acc bsegs m2 IQ 40) by (apply (ACT2 IQ 40 ACQ1); [ulc| left; ulc]).
assert (ACA2 : acc bsegs m2 AK 40) by (apply (ACT2 AK 40 ACA1); [ulc| left; ulc]).

apply (rw_cells_split_CB bsegs _ _ [] 160 _ [] [32; 88; 40]%nat) in HULL1; [| reflexivity]. cbn [mk_CB_cells app] in HULL1.
chunk_uncons HULL1 as RZ1. chunk_uncons HULL1 as WP. rename HULL1 into PAD1.
replace (usp + -288 + 32) with (usp + -256) in * by (clear; lia). replace (usp + -256 + 88) with (usp + -168) in * by (clear; lia).
assert (OBW2 : aobj bsegs m2 (usp + -256) 88) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ1 m2 _ _ ART2 INW)).
cps_seg (l2l_w2 IQ AK usp lo).
destruct POST as (jh2 & ws & m5 & a2x & a3x & a4x & -> & MU5 & WM5 & MI5 & ST5 & FR3 & WP5 & LWP5 & HULL2). clear FR1 WP.
assert (ACQ5 : acc bsegs m5 IQ 40) by (refine (proj2 (proj2 (aobj_munch bsegs _ m2 m5 IQ 40 _ MU5 _))); [split; [ulc|]; split; [ulc| exact ACQ2]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
assert (ACA5 : acc bsegs m5 AK 40) by (refine (proj2 (proj2 (aobj_munch bsegs _ m2 m5 AK 40 _ MU5 _))); [split; [ulc|]; split; [ulc| exact ACA2]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
clear OBW2. unfold l2l_frame in FR3. cps_seg_post.
assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -416)) = usp + -416) by (apply unsigned_lit; ulc).
cps_rt (APO Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (usp + -384) 40 lo).
{ rewrite (l2lF_rr2 usp U32). ulc. }
{ rewrite (l2lF_rr2 usp U32), PO1. apply pois_above_cons; [rewrite (l2lF_rr1 usp U32); apply (pois_above_le _ usp); [exact POA| lia]| lia| lia]. }
{ rewrite FRS1. exact FRN. }
{ cps_callok. }
intros c6 (Σ2 & Hc6 & PO2 & LV2 & FRS2 & SP2 & CR2).
cps_unpack Hc6 as (m6 & v6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & ACX & ACT6).
cps_sigma LV2 FRS2 SP2.
assert (INX : In (usp + -384, 40) (rt_pois RT Σ2)) by (rewrite PO2; left; reflexivity).
assert (INW2 : In (usp + -256, 88) (rt_pois RT Σ2)) by (rewrite PO2; right; exact INW).
assert (ACQ6 : acc bsegs m6 IQ 40) by (apply (ACT6 IQ 40 ACQ5); [ulc| left; ulc]).
assert (ACA6 : acc bsegs m6 AK 40) by (apply (ACT6 AK 40 ACA5); [ulc| left; ulc]).

apply (rw_cells_split_CB bsegs _ _ [] 128 _ [] [32; 40; 56]%nat) in HULL2; [| reflexivity]. cbn [mk_CB_cells app] in HULL2.
chunk_uncons HULL2 as RZ2. chunk_uncons HULL2 as XF. rename HULL2 into PAD2.
replace (usp + -416 + 32) with (usp + -384) in * by (clear; lia). replace (usp + -384 + 40) with (usp + -344) in * by (clear; lia).

assert (OBW : aobj bsegs m6 (usp + -256) 88) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m6 _ _ ART6 INW2)).
assert (OBX : aobj bsegs m6 (usp + -384) 40) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m6 _ _ ART6 INX)).
assert (OBQ : aobj bsegs m6 IQ 40) by (split; [ulc|]; split; [ulc|]; exact ACQ6).
assert (OBA : aobj bsegs m6 AK 40) by (split; [ulc|]; split; [ulc|]; exact ACA6).
change (rw_cells bsegs m6 (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -288)) j1 j2 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) in FR3.
cps_seg (l2l_body IQ AK usp lo qs aks ws).
{ unfold APP_TOP. ulc. } { unfold APP_TOP. ulc. }
destruct POST as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s9' & s10' & s11'
& t3' & t4' & t5' & t6' & F' & fc' & m7 & aks' & jw & jx' & -> & MU7 & WM7 & MI7 & FRM7 & FR7 & WP7 & XF7 & X7 & A7 & LA7).
assert (ACQ7 : acc bsegs m7 IQ 40) by (refine (proj2 (proj2 (aobj_munch bsegs _ m6 m7 IQ 40 _ MU7 _))); [split; [ulc|]; split; [ulc| exact ACQ6]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
assert (ACA7 : acc bsegs m7 AK 40) by (refine (proj2 (proj2 (aobj_munch bsegs _ m6 m7 AK 40 _ MU7 _))); [split; [ulc|]; split; [ulc| exact ACA6]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
clear FR3 WP5 XF X A OBW OBX OBQ OBA. unfold l2l_frame in FR7.
assert (ST6' : stk bsegs m6 lo (usp + -416)) by exact ST6.
cps_seg_post.

change (rw_cells bsegs m7 (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -416)) j1 j2 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) in FR7.
cps_seg (l2l_w5 usp lo).
subst ms.
cps_rt (AUN Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 (usp + -416) (usp + -128) lo).
{ rewrite PO2, PO1. intros e [<-|[<-|He]].
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite (l2lF_rr2 usp U32). clear. lia.
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite (l2lF_rr1 usp U32). clear. lia.
- right. pose proof (POA e He). lia. }
{ cps_callok. }
intros c8 (Σ3 & Hc8 & PO3 & LV3 & FRS3 & SP3 & CR3).
cps_unpack Hc8 as (m8 & v8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & ACT8).
assert (ACQ8 : acc bsegs m8 IQ 40) by (apply (ACT8 IQ 40 ACQ7); [ulc| left; ulc]).
assert (ACA8 : acc bsegs m8 AK 40) by (apply (ACT8 AK 40 ACA7); [ulc| left; ulc]).

chunk_cat RZ1 WP7. chunk_cat RZ1 PAD1. apply rw_cells_to_CB in RZ1. cbn [cells_size csize Nat.add] in RZ1.
chunk_cat RZ2 XF7. chunk_cat RZ2 PAD2. apply rw_cells_to_CB in RZ2. cbn [cells_size csize Nat.add] in RZ2.
change (rw_cells bsegs m8 (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -416)) j1 j2 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) in FR7.
cps_seg (l2l_w6 usp lo _ _ (usp + -416)).
destruct POST as (-> & ST9).
apply Hk. exists Σ3. split.
2:{ split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
rewrite PO3, PO2, PO1. rewrite !pois_drop_cons_below by (unfold pz_lo; cbn [fst]; clear; lia).
apply pois_drop_above. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v8, m8, aks'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM7]|].
split. { split; [exact ART8|]. split; [exact MI8|]. split; [cps_wmono| exact ST9]. }
split; [exact PF|]. split; [exact A7|]. split; [exact LA7|]. split; [exact ACQ8| exact ACA8].
Qed.
End L2LF.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma l2lF_rr1 : forall usp, usp mod 32 = 0 -> alloca_rr (usp + -256) 88 = usp + -128.
Proof. intros usp H. unfold alloca_rr. Z.div_mod_to_equations. lia. Qed.
Lemma l2lF_rr2 : forall usp, usp mod 32 = 0 -> alloca_rr (usp + -384) 40 = usp + -288.
Proof. intros usp H. unfold alloca_rr. Z.div_mod_to_equations. lia. Qed.

Section L2LF.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN : allocas_unpoison_contract RT.
Hypothesis MEMS : memset_icontract RT e_asan_memset.

Definition lsp_to_lpc_cpsF : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (IQ AK lo fq : Z) (kq : nat) (qs aks : list word),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 IQ -> a1 = Z_to_bv 64 AK -> a2 = Z_to_bv 64 10 -> tp = Z_to_bv 64 0x630458 ->
rw_cells asegs m IQ (f32 qs) -> length qs = 10%nat -> rw_cells asegs m AK (f32 aks) -> length aks = 10%nat ->

In (fq, kq) (rt_frames RT Σ) -> fq <= IQ -> IQ + 40 <= fq + fs_size kq - 8 -> fq <= AK -> AK + 40 <= fq + fs_size kq - 8 ->
acc asegs m IQ 40 -> acc asegs m AK 40 -> IQ mod 4 = 0 -> AK mod 4 = 0 -> (AK + 40 <= IQ \/ IQ + 40 <= AK) ->
pois_above (rt_pois RT Σ) (bv_unsigned sp) -> X1cn.frm0 fc ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 416 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_lsp_to_lpc m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m' aks',
ret_stL (fun F' fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(AK, AK + 40)] m m'
/\ rw_cells asegs m' AK (f32 aks') /\ length aks' = 10%nat
/\ acc asegs m' IQ 40 /\ acc asegs m' AK 40) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem lsp_to_lpcF_ok : lsp_to_lpc_cpsF.
Proof using AF APO AUN MEMS.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m IQ AK lo fq kq qs aks
FDO MST -> -> -> -> X LQ A LA INF FQL FQH FAL FAH ACQ ACA Q4 A4 APQA POA FRM ART0 MI0 ST0 LOW LOR SPT U32.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
assert (FRN : rt_frames RT Σ <> []) by (intros E; rewrite E in INF; exact INF).
destruct (frame_below_lo RT AF Σ m fq kq lo ART0 INF LOW) as (BF0 & _ & _).
pose proof (frame_facts RT AF Σ m fq kq ART0 INF) as (FF0 & FF1 & FF2 & _ & FF4 & _).
assert (FP8 : fq mod 8 = 0) by (clear - FF1; Z.div_mod_to_equations; lia).
pose proof (fs_size_mod8 kq) as FS8.
pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
assert (LOSH : SH_HI <= lo) by (clear - SPW LOW; unfold SH_HI, STACK_WIN in *; lia).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(AK, AK + 40)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (FSZ : 0 <= fs_size kq) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
cps_norm.
assert (SHQ : forall i, 0 <= i < 40 -> SH_LO <= shad (IQ + i) < SH_HI) by (intros i Hi; apply shad_in_window; clear - Hi FQH FF0 FQL BF0 LOR SPT; lia).
assert (SHA : forall i, 0 <= i < 40 -> SH_LO <= shad (AK + i) < SH_HI) by (intros i Hi; apply shad_in_window; clear - Hi FAH FF0 FAL BF0 LOR SPT; lia).
cps_hide.

cps_seg (l2l_w1 IQ AK usp lo).
destruct POST as (j1 & j2 & jh & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HULL1).
assert (ACQ1 : acc asegs m1 IQ 40) by (refine (proj2 (proj2 (aobj_munch asegs _ m m1 IQ 40 _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACQ]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
assert (ACA1 : acc asegs m1 AK 40) by (refine (proj2 (proj2 (aobj_munch asegs _ m m1 AK 40 _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACA]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
unfold l2l_frame in FR1. cps_seg_post.
assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -288)) = usp + -288) by (apply unsigned_lit; ulc).
cps_rt (APO Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -256) 88 lo).
{ rewrite (l2lF_rr1 usp U32). ulc. }
{ rewrite (l2lF_rr1 usp U32). apply (pois_above_le _ usp); [exact POA| lia]. }
{ cps_callok. }
intros c2 (Σ1 & Hc2 & PO1 & LV1 & FRS1 & SP1 & CR1).
cps_unpack Hc2 as (m2 & v1 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACW & ACT2).
cps_sigma LV1 FRS1 SP1.
assert (INW : In (usp + -256, 88) (rt_pois RT Σ1)) by (rewrite PO1; left; reflexivity).
assert (ACQ2 : acc asegs m2 IQ 40) by (apply (ACT2 IQ 40 ACQ1); [ulc| left; ulc]).
assert (ACA2 : acc asegs m2 AK 40) by (apply (ACT2 AK 40 ACA1); [ulc| left; ulc]).

cps_seg (l2l_w2 IQ AK usp lo).
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & FR3). clear FR1.
assert (ACQ3 : acc asegs m3 IQ 40) by (refine (proj2 (proj2 (aobj_munch asegs _ m2 m3 IQ 40 _ MU3 _))); [split; [ulc|]; split; [ulc| exact ACQ2]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
assert (ACA3 : acc asegs m3 AK 40) by (refine (proj2 (proj2 (aobj_munch asegs _ m2 m3 AK 40 _ MU3 _))); [split; [ulc|]; split; [ulc| exact ACA2]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
cps_seg_post.

apply (rw_cells_split_CB asegs _ _ [] 160 _ [] [32; 88; 40]%nat) in HULL1; [| reflexivity]. cbn [mk_CB_cells app] in HULL1.
chunk_uncons HULL1 as RZ1. chunk_uncons HULL1 as WP. rename HULL1 into PAD1.
replace (usp + -288 + 32) with (usp + -256) in * by (clear; lia). replace (usp + -256 + 88) with (usp + -168) in * by (clear; lia).
set (jw0 := firstn 88 (skipn 32 jh)) in *.

pose proof (af_pois_range RT AF Σ1 m3 _ _ ART INW) as (_ & _ & RW1 & RW2). rewrite (l2lF_rr1 usp U32) in RW2.
pose proof WP as [_ WRW]. cbn [cells_size csize Nat.add] in WRW. change (Z.of_nat 88) with 88 in WRW.
cps_rt (MEMS Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (usp + -256) 88 z8 lo).
{ unfold checked_dst. rewrite unsigned_lit by ulc. split; [intros _; split|split].
- exact (af_acc_pois RT AF Σ1 m3 _ _ ART INW).
- right; right; left. split; [ulc| ulc].
- intros i Hi. left. ulc.
- exact WRW. }
{ cps_callok. }
intros c4 Hc4.
cps_unpack Hc4 as (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BYW).
assert (ACQ4 : acc asegs m4 IQ 40).
{ apply (acc_pres_ex_frame2 _ _ _ _ _ m3 m4 fq kq IQ 40 PRES4); [exact INF | exact FP8 | exact FS8 | ulc | exact FQL | ulc | | exact ACQ3].
intros i Hi. pose proof (SHQ i Hi) as [_ HS]. intros [Ha Hb]. clear - HS Ha LOSH LOR. unfold SH_HI in *. lia. }
assert (ACA4 : acc asegs m4 AK 40).
{ apply (acc_pres_ex_frame2 _ _ _ _ _ m3 m4 fq kq AK 40 PRES4); [exact INF | exact FP8 | exact FS8 | ulc | exact FAL | ulc | | exact ACA3].
intros i Hi. pose proof (SHA i Hi) as [_ HS]. intros [Ha Hb]. clear - HS Ha LOSH LOR. unfold SH_HI in *. lia. }
assert (WP4 : rw_cells asegs m4 (usp + -256) [CB 88 (repeat z8 88)]).
{ split; [split; [split; [reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BYW]|].
cbn [cells_size csize Nat.add]. exact (wr_at_transport asegs m3 m4 _ _ WRW WM4). }
clear WRW BYW.

cps_seg (l2l_w3 IQ AK usp lo).
destruct POST as (jh2 & m5 & -> & MU5 & WM5 & MI5 & ST5 & HULL2). unfold l2l_frame in FR3.
assert (ACQ5 : acc asegs m5 IQ 40) by (refine (proj2 (proj2 (aobj_munch asegs _ m4 m5 IQ 40 _ MU5 _))); [split; [ulc|]; split; [ulc| exact ACQ4]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
assert (ACA5 : acc asegs m5 AK 40) by (refine (proj2 (proj2 (aobj_munch asegs _ m4 m5 AK 40 _ MU5 _))); [split; [ulc|]; split; [ulc| exact ACA4]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
cps_seg_post.
assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -416)) = usp + -416) by (apply unsigned_lit; ulc).
cps_rt (APO Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (usp + -384) 40 lo).
{ rewrite (l2lF_rr2 usp U32). ulc. }
{ rewrite (l2lF_rr2 usp U32), PO1. apply pois_above_cons; [rewrite (l2lF_rr1 usp U32); apply (pois_above_le _ usp); [exact POA| lia]| lia| lia]. }
{ rewrite FRS1. exact FRN. }
{ cps_callok. }
intros c6 (Σ2 & Hc6 & PO2 & LV2 & FRS2 & SP2 & CR2).
cps_unpack Hc6 as (m6 & v6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & ACX & ACT6).
cps_sigma LV2 FRS2 SP2.
assert (INX : In (usp + -384, 40) (rt_pois RT Σ2)) by (rewrite PO2; left; reflexivity).
assert (INW2 : In (usp + -256, 88) (rt_pois RT Σ2)) by (rewrite PO2; right; exact INW).
assert (ACQ6 : acc asegs m6 IQ 40) by (apply (ACT6 IQ 40 ACQ5); [ulc| left; ulc]).
assert (ACA6 : acc asegs m6 AK 40) by (apply (ACT6 AK 40 ACA5); [ulc| left; ulc]).

apply (rw_cells_split_CB asegs _ _ [] 128 _ [] [32; 40; 56]%nat) in HULL2; [| reflexivity]. cbn [mk_CB_cells app] in HULL2.
chunk_uncons HULL2 as RZ2. chunk_uncons HULL2 as XF. rename HULL2 into PAD2.
replace (usp + -416 + 32) with (usp + -384) in * by (clear; lia). replace (usp + -384 + 40) with (usp + -344) in * by (clear; lia).

assert (OBW : aobj asegs m6 (usp + -256) 88) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m6 _ _ ART6 INW2)).
assert (OBX : aobj asegs m6 (usp + -384) 40) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m6 _ _ ART6 INX)).
assert (OBQ : aobj asegs m6 IQ 40) by (split; [ulc|]; split; [ulc|]; exact ACQ6).
assert (OBA : aobj asegs m6 AK 40) by (split; [ulc|]; split; [ulc|]; exact ACA6).
change (rw_cells asegs m6 (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -288)) j1 j2 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) in FR3.
cps_seg (l2l_body IQ AK usp lo qs aks).
{ unfold APP_TOP. ulc. } { unfold APP_TOP. ulc. }
destruct POST as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s9' & s10' & s11'
& t3' & t4' & t5' & t6' & F' & fc' & m7 & aks' & jw & jx' & -> & MU7 & WM7 & MI7 & FRM7 & FR7 & WP7 & XF7 & X7 & A7 & LA7).
assert (ACQ7 : acc asegs m7 IQ 40) by (refine (proj2 (proj2 (aobj_munch asegs _ m6 m7 IQ 40 _ MU7 _))); [split; [ulc|]; split; [ulc| exact ACQ6]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
assert (ACA7 : acc asegs m7 AK 40) by (refine (proj2 (proj2 (aobj_munch asegs _ m6 m7 AK 40 _ MU7 _))); [split; [ulc|]; split; [ulc| exact ACA6]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
clear FR3 WP4 XF X A OBW OBX OBQ OBA. unfold l2l_frame in FR7.
assert (ST6' : stk asegs m6 lo (usp + -416)) by exact ST6.
cps_seg_post.

change (rw_cells asegs m7 (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -416)) j1 j2 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) in FR7.
cps_seg (l2l_w5 usp lo).
subst ms.
cps_rt (AUN Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 (usp + -416) (usp + -128) lo).
{ rewrite PO2, PO1. intros e [<-|[<-|He]].
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite (l2lF_rr2 usp U32). clear. lia.
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite (l2lF_rr1 usp U32). clear. lia.
- right. pose proof (POA e He). lia. }
{ cps_callok. }
intros c8 (Σ3 & Hc8 & PO3 & LV3 & FRS3 & SP3 & CR3).
cps_unpack Hc8 as (m8 & v8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & ACT8).
assert (ACQ8 : acc asegs m8 IQ 40) by (apply (ACT8 IQ 40 ACQ7); [ulc| left; ulc]).
assert (ACA8 : acc asegs m8 AK 40) by (apply (ACT8 AK 40 ACA7); [ulc| left; ulc]).

chunk_cat RZ1 WP7. chunk_cat RZ1 PAD1. apply rw_cells_to_CB in RZ1. cbn [cells_size csize Nat.add] in RZ1.
chunk_cat RZ2 XF7. chunk_cat RZ2 PAD2. apply rw_cells_to_CB in RZ2. cbn [cells_size csize Nat.add] in RZ2.
change (rw_cells asegs m8 (usp + -128) (l2l_frame (Z_to_bv 64 (usp + -416)) j1 j2 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) in FR7.
cps_seg (l2l_w6 usp lo _ _ (usp + -416)).
destruct POST as (-> & ST9).
apply Hk. exists Σ3. split.
2:{ split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
rewrite PO3, PO2, PO1. rewrite !pois_drop_cons_below by (unfold pz_lo; cbn [fst]; clear; lia).
apply pois_drop_above. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v8, m8, aks'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM7]|].
split. { split; [exact ART8|]. split; [exact MI8|]. split; [cps_wmono| exact ST9]. }
split; [exact PF|]. split; [exact A7|]. split; [exact LA7|]. split; [exact ACQ8| exact ACA8].
Qed.
End L2LF.
