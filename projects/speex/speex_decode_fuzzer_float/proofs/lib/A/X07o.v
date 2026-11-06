(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j5 X0ec X001 X00b X04b X07z X05o X05p X05s X08k X05u
X081 X05l X05m X09f X06d X069 X07n.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19o X14x X0r0 X0ra X0v9 X0yr X0wl X0zb X0wn X0ys X0x2 X0yf.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yf.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma nb_init_prun : forall q r q',
prun (speex_decoder_init (St := pst) p_calloc p_free ModeNB) q = Some (r, q') -> r = Some (DecNB (nb_init_state tt)) /\ q' = q.
Proof.
intros q r q' H. unfold speex_decoder_init, nb_decoder_init_d, nb_decoder_init in H.
rewrite !prun_bind in H. rewrite (prun_calloc_ok SIZEOF_DECSTATE 1 q) in H by (unfold SIZEOF_DECSTATE; lia).
rewrite !prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Ltac piece X P :=
lazymatch type of X with
| rw_cells ?segs ?m ?A (?cs1 ++ ?cs2) =>
let n := eval vm_compute in (Z.of_nat (cells_size cs1)) in
apply (proj1 (rw_cells_app segs m A cs1 cs2)) in X; destruct X as [P X];
change (Z.of_nat (cells_size cs1)) with n in X;
repeat match type of X with rw_cells _ _ (?B + ?a + ?b) _ => let v := eval vm_compute in (a + b) in replace (B + a + b) with (B + v) in X by lia end
end.

Definition zw (n : nat) : list word := repeat (Z_to_bv 64 0) n.
Definition zcbs : list byte := zb 640.
Definition zjunk : nb_junk :=
NBJ (Z_to_bv 64 0) (zw 500) 0 (zw 10) (zw 10) (zw 10) (zw 2) (zw 4) (zw 3) (Z_to_bv 64 40) (Z_to_bv 64 0) (zw 3)
(Z_to_bv 64 1000) (zb 4) zcbs (zb 8, zb 16) (zw 3) (zb 4).

Lemma zjunk_ok : nb_junk_ok zjunk.
Proof. repeat split; reflexivity. Qed.

Lemma zjunk_cbs : forall SH SD, cbs_ok SH SD false (j_cbs zjunk).
Proof.
intros SH SD. exists (repeat (zb 8, zb 16) 16).
split; [reflexivity|]. split; [repeat constructor|].
apply byte_list_eq. vm_compute. reflexivity.
Qed.

Lemma nb_init_inv : forall blk : bptr, nb_inv (nb_init_state blk).
Proof. intros blk. unfold nb_inv. cbn. unfold NB_DEFAULT_SUBMODE. repeat split; try lia. Qed.

Lemma rw_cells_join : forall m A B cs1 cs2,
rw_cells bsegs m A cs1 -> rw_cells bsegs m B cs2 -> B = A + Z.of_nat (cells_size cs1) -> rw_cells bsegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 X Y ->. apply (proj2 (rw_cells_app _ _ _ _ _)). split; assumption. Qed.

Definition nb_mid_cells : list cell :=
f32 (zw 500) ++ [C8 (Z_to_bv 64 0)] ++ f32 (zw 10) ++ f32 (zw 10) ++ f32 (zw 10) ++ f32 (zw 2) ++ f32 (zw 4) ++ [C8 (Z_to_bv 64 0)] ++ f32 (zw 3).
Lemma nb_mid_recast : forall m A, rw_cells bsegs m A ([CB 1216 (zb 1216)] ++ [CB 956 (zb 956)]) -> rw_cells bsegs m A nb_mid_cells.
Proof.
intros m A X. apply (rw_cells_recast bsegs m A _ nb_mid_cells X).
- unfold nb_mid_cells. repeat (apply (proj2 (cells_wf_app _ _)); split); first [apply cells_wf_f32 | (cbn; tauto)].
- vm_compute. reflexivity.
Qed.
Lemma nb_pgb_recast : forall m A, rw_cells bsegs m A [CB 16 (zb 16)] -> rw_cells bsegs m A (f32 (zw 3) ++ [C4 (Z_to_bv 64 0)]).
Proof. intros m A X. apply (rw_cells_recast bsegs m A _ _ X); [cbn; tauto| vm_compute; reflexivity]. Qed.
Lemma nb_tailblk_recast : forall m A,
rw_cells bsegs m A ([CB 24 (zb 24)] ++ [C4 (Z_to_bv 64 1)] ++ [CB 4 (zb 4)]) ->
rw_cells bsegs m A (f32 (zw 3) ++ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); CB 4 (zb 4)]).
Proof. intros m A X. apply (rw_cells_recast bsegs m A _ _ X); [cbn; tauto| vm_compute; reflexivity]. Qed.
Lemma nb_cbs_recast : forall m A, rw_cells bsegs m A (cbs_zero 16) -> rw_cells bsegs m A [CB 640 zcbs].
Proof. intros m A X. apply (rw_cells_recast bsegs m A _ _ X); [cbn; split; [reflexivity| exact I]| vm_compute; reflexivity]. Qed.

Lemma ms2_recast : forall m A, rw_cells bsegs m A [CB 16 (zb 16)] -> rw_cells bsegs m A [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Proof. intros m A X. apply (rw_cells_recast bsegs m A _ _ X); [cbn; tauto| vm_compute; reflexivity]. Qed.
Lemma ms3_recast : forall m A, rw_cells bsegs m A [CB 24 (zb 24)] ->
rw_cells bsegs m A [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Proof. intros m A X. apply (rw_cells_recast bsegs m A _ _ X); [cbn; tauto| vm_compute; reflexivity]. Qed.
Lemma nb_pgb_recastB : forall m A, rw_cells bsegs m A [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
rw_cells bsegs m A (f32 (zw 3) ++ [C4 (Z_to_bv 64 0)]).
Proof. intros m A X. exact X. Qed.
Lemma nb_tailblk_recastB : forall m A,
rw_cells bsegs m A ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 1)] ++ [CB 4 (zb 4)]) ->
rw_cells bsegs m A (f32 (zw 3) ++ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); CB 4 (zb 4)]).
Proof. intros m A X. exact X. Qed.

Lemma ms_piece : forall (m m' : mem) d n, wr_at bsegs m d (Z.of_nat n) -> wmono bsegs m m' -> bytes_at bsegs m' d (repeat (Z_to_bv 8 0) n) ->
rw_cells bsegs m' d [CB n (zb n)].
Proof.
intros m m' d n WR WM BY. split; [split; [split; [unfold zb; apply repeat_length| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BY]|].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact (wr_at_transport bsegs m m' d _ WR WM).
Qed.

Section NbInitCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis CAL : calloc_contract RT.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Definition MSET0 (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (d n lo : Z) :=
MSET Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d n (Z_to_bv 8 0) lo.

Definition nb_decoder_init_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A_speex_nb_mode -> tp = Z_to_bv 64 0x638c98 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
uw_site m RA_nbinit_calloc s0 (bv_unsigned sp) lo ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 64 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_decoder_init m)))
(fun c => exists (Σ' : rts RT) (D : Z),
ASTA RT Σ' PMc (fun ms => exists m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 D) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [] m m'
/\ forall OUT STEREO, DREP OUT STEREO m' D (DecNB (nb_init_state tt)) [(tt, D, NBSTATE_SIZEOF)]) c
/\ rt_live RT Σ' = (D, NBSTATE_SIZEOF) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem nb_decoder_init_ok : nb_decoder_init_cps.
Proof using AF CAL MSET AF_LIB.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
FDO MST -> -> LVM CR0 UW ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (AF_LIB Σ m ART0) as LC0.
assert (OBM : aobj bsegs m A_speex_nb_mode 96)
by (apply (aobj_lit RT AF Σ m A_speex_nb_mode 96 ART0); [unfold ACC_LITS, A_speex_nb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_nb_mode; lia | unfold A_speex_nb_mode, APP_TOP; lia]).
pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
assert (LOS : SH_HI <= lo) by (unfold SH_HI, STACK_WIN in *; lia).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
cps_norm.

cps_seg (nbinit_w1 usp lo).
destruct POST as (m1 & j0 & xt1 & xa2 & xa3 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
assert (UW1 : unwind_ch m1 (Z_to_bv 64 RA_nbinit_calloc) s0 (Z_to_bv 64 (usp + -64))).
{ apply (uw_site_ch [(usp + -64, usp)] m m1 RA_nbinit_calloc s0 usp (usp + -64) lo UW MU1 WM1); [repeat constructor; cbn; lia| ulc| lia| ulc| unfold RA_nbinit_calloc; lia]. }
cps_seg_post.

cps_rt CAL.
{ cps_callok. }
intros c2 (Σ1 & D & Hc2 & LV1 & FRS1 & SP1 & CR1 & DPOS & D16 & DTOP & PO1).
change (2968 * 1) with 2968 in *. change (mcost 2968) with 0 in CR1. rewrite Z.sub_0_r in CR1. change (Z.to_nat 2968) with 2968%nat in *.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRD & ACD & BYD).
pose proof (fun a Ha => newchunk_apart RT AF Σ Σ1 m2 D 2968 usp a ART2 LV1 FRS1 SP1 ltac:(ulc) ltac:(lia) Ha) as NAD.
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m2 D 2968 lo ART2 INL LOW) as (_ & BD1 & _).
pose proof (live_facts RT AF Σ1 m2 D 2968 ART2 INL) as (_ & _ & DIMG & DHI).
assert (BLK : rw_cells bsegs m2 D [CB 2968 (zb 2968)]).
{ split; [split; [split; [vm_compute; reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BYD]| exact WRD]. }
apply zero_blob_recast in BLK. unfold nb_zero_cells in BLK.
piece BLK HD. piece BLK MS1. piece BLK MID. piece BLK LPG. piece BLK MS2. piece BLK SEED. piece BLK CFG. piece BLK CBS. piece BLK UCB. piece BLK MS3. piece BLK HPE.
rename BLK into PAD.
unfold nbz_hdr in HD. unfold nbz_cfg in CFG. cbn [cbs_zero app] in CBS. unfold cb_zero in CBS, UCB. cbn [app] in CBS.
assert (D8 : D mod 8 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
assert (OBD : aobj bsegs m2 D 2968) by (split; [lia|]; split; [ulc| exact ACD]).
assert (OBN : aobj bsegs m2 A_nb_mode 208)
by (apply (aobj_lit RT AF Σ1 m2 A_nb_mode 208 ART2); [unfold ACC_LITS, A_nb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_nb_mode; lia | unfold A_nb_mode; ulc]).
pose proof (AF_LIB Σ1 m2 ART2) as LC2.
cps_norm.

cps_seg (nbinit_w2 usp lo D).
destruct POST as (m3 & xa3' & -> & MU3 & WM3 & MI3 & HD3 & CFG3).
clear HD CFG OBD OBN LC2. cps_seg_post.

destruct (af_acc_live RT AF Σ1 m3 D 2968 ART INL) as (_ & ACL3).
pose proof (proj2 MS1) as WR1. cbn [cells_size csize Nat.add] in WR1.
cps_rt MSET0.
{ split; [intros _; split; [apply (acc_sub bsegs m3 D 2968 (D + 32) 1216 ACL3); lia| left; exists D, 2968; split; [exact INL| lia]]|].
split; [intros i Hi; right; right; left; exists D, 2968; split; [exact INL| lia]| exact (proj2 MS1)]. }
{ cps_callok. }
intros c4 Hc4. unfold icpt_postF in Hc4.
cps_unpack_ex Hc4 as (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BY4).
change (Z.to_nat 1216) with 1216%nat in BY4.
pose proof (ms_piece m3 m4 (D + 32) 1216 WR1 WM4 BY4) as MS1'. clear WR1 BY4 ACL3.

destruct (af_acc_live RT AF Σ1 m4 D 2968 ART4 INL) as (_ & ACL4).
assert (OBD4 : aobj bsegs m4 D 2968) by (split; [lia|]; split; [ulc| exact ACL4]).
pose proof (AF_LIB Σ1 m4 ART4) as LC4.
apply ms2_recast in MS2. apply ms3_recast in MS3.
cps_seg (nbinit_w3 usp lo D).
destruct POST as (m9 & ya1 & ya2 & ya3 & ya4 & ya5 & -> & MU9 & WM9 & MI9 & ST9 & HD9 & LPG9 & MS2' & SEED9 & CBS7 & UCB7 & MS3' & HPE9).
clear HD3 LPG MS2 SEED CBS UCB MS3 HPE OBD4 ACL4 LC4 FR1. cbn [cbs_zero app] in CBS7. unfold cb_zero in CBS7. cbn [app] in CBS7. cps_seg_post.

pose proof (rw_cells_join _ _ _ _ _ MS1' MID ltac:(cbn; lia)) as B1. clear MS1' MID.
apply nb_mid_recast in B1. unfold nb_mid_cells in B1.
piece B1 Q1. piece B1 Q2. piece B1 Q3. piece B1 Q4. piece B1 Q5. piece B1 Q6. piece B1 Q7. piece B1 Q8. rename B1 into Q9.
apply nb_pgb_recastB in MS2'. piece MS2' Q11. rename MS2' into Q12.
pose proof (rw_cells_join _ _ _ _ _ MS3' (rw_cells_join _ _ _ _ _ HPE9 PAD ltac:(cbn; lia)) ltac:(cbn; lia)) as BT. clear MS3' HPE9 PAD.
apply nb_tailblk_recastB in BT. piece BT Q17. rename BT into Q18.
assert (CBS9 : rw_cells bsegs m9 (D + 2256) [CB 640 zcbs]) by (apply nb_cbs_recast; cbn [cbs_zero app]; unfold cb_zero; cbn [app]; exact CBS7).
clear CBS7.
apply Hk. exists Σ1, D. split; [| unfold NBSTATE_SIZEOF; repeat split; congruence].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m9.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI9|]. split; [cps_wmono| exact ST9]. }
split; [exact PF|].
intros OUT STEREO. cbn [decst_rep]. split; [reflexivity|].
split; [exact D8|]. split; [exact DPOS|]. split; [apply nb_init_inv|].
exists zjunk. split; [exact zjunk_ok|]. split; [apply zjunk_cbs|].
apply nb_cells_of_pieces; [exact zjunk_ok|]. unfold nb_pieces.
cbn [nb_hdr_cells nb_cfg_cells nb_tail_cells nb_ucb_cells cb_cells nb_isave_ptr nb_init_state nb_first nb_count_lost nb_sampling_rate
nb_innov_save nb_pitch_gain_buf_idx nb_encode_submode nb_submodeID nb_lpc_enh_enabled nb_voc_offset nb_dtx_enabled nb_isWideband
nb_highpass_enabled zjunk j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch
j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2 fst snd].
repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.
End NbInitCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma nb_init_prun : forall q r q',
prun (speex_decoder_init (St := pst) p_calloc p_free ModeNB) q = Some (r, q') -> r = Some (DecNB (nb_init_state tt)) /\ q' = q.
Proof.
intros q r q' H. unfold speex_decoder_init, nb_decoder_init_d, nb_decoder_init in H.
rewrite !prun_bind in H. rewrite (prun_calloc_ok SIZEOF_DECSTATE 1 q) in H by (unfold SIZEOF_DECSTATE; lia).
rewrite !prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Ltac piece X P :=
lazymatch type of X with
| rw_cells ?segs ?m ?A (?cs1 ++ ?cs2) =>
let n := eval vm_compute in (Z.of_nat (cells_size cs1)) in
apply (proj1 (rw_cells_app segs m A cs1 cs2)) in X; destruct X as [P X];
change (Z.of_nat (cells_size cs1)) with n in X;
repeat match type of X with rw_cells _ _ (?B + ?a + ?b) _ => let v := eval vm_compute in (a + b) in replace (B + a + b) with (B + v) in X by lia end
end.

Definition zw (n : nat) : list word := repeat (Z_to_bv 64 0) n.
Definition zcbs : list byte := zb 640.
Definition zjunk : nb_junk :=
NBJ (Z_to_bv 64 0) (zw 500) 0 (zw 10) (zw 10) (zw 10) (zw 2) (zw 4) (zw 3) (Z_to_bv 64 40) (Z_to_bv 64 0) (zw 3)
(Z_to_bv 64 1000) (zb 4) zcbs (zb 8, zb 16) (zw 3) (zb 4).

Lemma zjunk_ok : nb_junk_ok zjunk.
Proof. repeat split; reflexivity. Qed.

Lemma zjunk_cbs : forall SH SD, cbs_ok SH SD false (j_cbs zjunk).
Proof.
intros SH SD. exists (repeat (zb 8, zb 16) 16).
split; [reflexivity|]. split; [repeat constructor|].
apply byte_list_eq. vm_compute. reflexivity.
Qed.

Lemma nb_init_inv : forall blk : bptr, nb_inv (nb_init_state blk).
Proof. intros blk. unfold nb_inv. cbn. unfold NB_DEFAULT_SUBMODE. repeat split; try lia. Qed.

Lemma rw_cells_join : forall m A B cs1 cs2,
rw_cells asegs m A cs1 -> rw_cells asegs m B cs2 -> B = A + Z.of_nat (cells_size cs1) -> rw_cells asegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 X Y ->. apply (proj2 (rw_cells_app _ _ _ _ _)). split; assumption. Qed.

Definition nb_mid_cells : list cell :=
f32 (zw 500) ++ [C8 (Z_to_bv 64 0)] ++ f32 (zw 10) ++ f32 (zw 10) ++ f32 (zw 10) ++ f32 (zw 2) ++ f32 (zw 4) ++ [C8 (Z_to_bv 64 0)] ++ f32 (zw 3).
Lemma nb_mid_recast : forall m A, rw_cells asegs m A ([CB 1216 (zb 1216)] ++ [CB 956 (zb 956)]) -> rw_cells asegs m A nb_mid_cells.
Proof.
intros m A X. apply (rw_cells_recast asegs m A _ nb_mid_cells X).
- unfold nb_mid_cells. repeat (apply (proj2 (cells_wf_app _ _)); split); first [apply cells_wf_f32 | (cbn; tauto)].
- vm_compute. reflexivity.
Qed.
Lemma nb_pgb_recast : forall m A, rw_cells asegs m A [CB 16 (zb 16)] -> rw_cells asegs m A (f32 (zw 3) ++ [C4 (Z_to_bv 64 0)]).
Proof. intros m A X. apply (rw_cells_recast asegs m A _ _ X); [cbn; tauto| vm_compute; reflexivity]. Qed.
Lemma nb_tailblk_recast : forall m A,
rw_cells asegs m A ([CB 24 (zb 24)] ++ [C4 (Z_to_bv 64 1)] ++ [CB 4 (zb 4)]) ->
rw_cells asegs m A (f32 (zw 3) ++ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); CB 4 (zb 4)]).
Proof. intros m A X. apply (rw_cells_recast asegs m A _ _ X); [cbn; tauto| vm_compute; reflexivity]. Qed.
Lemma nb_cbs_recast : forall m A, rw_cells asegs m A (cbs_zero 16) -> rw_cells asegs m A [CB 640 zcbs].
Proof. intros m A X. apply (rw_cells_recast asegs m A _ _ X); [cbn; split; [reflexivity| exact I]| vm_compute; reflexivity]. Qed.

Lemma ms_piece : forall (m m' : mem) d n, wr_at asegs m d (Z.of_nat n) -> wmono asegs m m' -> bytes_at asegs m' d (repeat (Z_to_bv 8 0) n) ->
rw_cells asegs m' d [CB n (zb n)].
Proof.
intros m m' d n WR WM BY. split; [split; [split; [unfold zb; apply repeat_length| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BY]|].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact (wr_at_transport asegs m m' d _ WR WM).
Qed.

Section NbInitCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis CAL : calloc_contract RT.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Definition MSET0 (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (d n lo : Z) :=
MSET Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d n (Z_to_bv 8 0) lo.

Definition nb_decoder_init_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A_speex_nb_mode -> tp = Z_to_bv 64 0x630458 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
uw_site m RA_nbinit_calloc s0 (bv_unsigned sp) lo ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 64 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_decoder_init m)))
(fun c => exists (Σ' : rts RT) (D : Z),
ASTA RT Σ' PMc (fun ms => exists m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 D) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [] m m'
/\ forall OUT STEREO, DREP OUT STEREO m' D (DecNB (nb_init_state tt)) [(tt, D, NBSTATE_SIZEOF)]) c
/\ rt_live RT Σ' = (D, NBSTATE_SIZEOF) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem nb_decoder_init_ok : nb_decoder_init_cps.
Proof using AF CAL MSET AF_LIB.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
FDO MST -> -> LVM CR0 UW ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (AF_LIB Σ m ART0) as LC0.
assert (OBM : aobj asegs m A_speex_nb_mode 96)
by (apply (aobj_lit RT AF Σ m A_speex_nb_mode 96 ART0); [unfold ACC_LITS, A_speex_nb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_nb_mode; lia | unfold A_speex_nb_mode, APP_TOP; lia]).
pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
assert (LOS : SH_HI <= lo) by (unfold SH_HI, STACK_WIN in *; lia).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
cps_norm.

cps_seg (nbinit_w1 usp lo).
destruct POST as (m1 & j0 & xt1 & xa2 & xa3 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
assert (UW1 : unwind_ch m1 (Z_to_bv 64 RA_nbinit_calloc) s0 (Z_to_bv 64 (usp + -64))).
{ apply (uw_site_ch [(usp + -64, usp)] m m1 RA_nbinit_calloc s0 usp (usp + -64) lo UW MU1 WM1); [repeat constructor; cbn; lia| ulc| lia| ulc| unfold RA_nbinit_calloc; lia]. }
cps_seg_post.

cps_rt CAL.
{ cps_callok. }
intros c2 (Σ1 & D & Hc2 & LV1 & FRS1 & SP1 & CR1 & DPOS & D16 & DTOP & PO1).
change (2968 * 1) with 2968 in *. change (mcost 2968) with 0 in CR1. rewrite Z.sub_0_r in CR1. change (Z.to_nat 2968) with 2968%nat in *.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRD & ACD & BYD).
pose proof (fun a Ha => newchunk_apart RT AF Σ Σ1 m2 D 2968 usp a ART2 LV1 FRS1 SP1 ltac:(ulc) ltac:(lia) Ha) as NAD.
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m2 D 2968 lo ART2 INL LOW) as (_ & BD1 & _).
pose proof (live_facts RT AF Σ1 m2 D 2968 ART2 INL) as (_ & _ & DIMG & DHI).
assert (BLK : rw_cells asegs m2 D [CB 2968 (zb 2968)]).
{ split; [split; [split; [vm_compute; reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BYD]| exact WRD]. }
apply zero_blob_recast in BLK. unfold nb_zero_cells in BLK.
piece BLK HD. piece BLK MS1. piece BLK MID. piece BLK LPG. piece BLK MS2. piece BLK SEED. piece BLK CFG. piece BLK CBS. piece BLK UCB. piece BLK MS3. piece BLK HPE.
rename BLK into PAD.
unfold nbz_hdr in HD. unfold nbz_cfg in CFG. cbn [cbs_zero app] in CBS. unfold cb_zero in CBS, UCB. cbn [app] in CBS.
assert (D8 : D mod 8 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
assert (OBD : aobj asegs m2 D 2968) by (split; [lia|]; split; [ulc| exact ACD]).
assert (OBN : aobj asegs m2 A_nb_mode 208)
by (apply (aobj_lit RT AF Σ1 m2 A_nb_mode 208 ART2); [unfold ACC_LITS, A_nb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_nb_mode; lia | unfold A_nb_mode; ulc]).
pose proof (AF_LIB Σ1 m2 ART2) as LC2.
cps_norm.

cps_seg (nbinit_w2 usp lo D).
destruct POST as (m3 & xa3' & -> & MU3 & WM3 & MI3 & HD3 & CFG3).
clear HD CFG OBD OBN LC2. cps_seg_post.

destruct (af_acc_live RT AF Σ1 m3 D 2968 ART INL) as (_ & ACL3).
pose proof (proj2 MS1) as WR1. cbn [cells_size csize Nat.add] in WR1.
cps_rt MSET0.
{ split; [intros _; split; [apply (acc_sub asegs m3 D 2968 (D + 32) 1216 ACL3); lia| left; exists D, 2968; split; [exact INL| lia]]|].
split; [intros i Hi; right; right; left; exists D, 2968; split; [exact INL| lia]| exact (proj2 MS1)]. }
{ cps_callok. }
intros c4 Hc4. unfold icpt_postF in Hc4.
cps_unpack_ex Hc4 as (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BY4).
change (Z.to_nat 1216) with 1216%nat in BY4.
pose proof (ms_piece m3 m4 (D + 32) 1216 WR1 WM4 BY4) as MS1'. clear WR1 BY4 ACL3.

destruct (af_acc_live RT AF Σ1 m4 D 2968 ART4 INL) as (_ & ACL4).
assert (OBD4 : aobj asegs m4 D 2968) by (split; [lia|]; split; [ulc| exact ACL4]).
cps_seg (nbinit_w3 usp lo D).
destruct POST as (m5 & -> & MU5 & WM5 & MI5 & HD5 & LPG5).
clear HD3 LPG OBD4 ACL4. cps_seg_post.
destruct (af_acc_live RT AF Σ1 m5 D 2968 ART INL) as (_ & ACL5).
pose proof (proj2 MS2) as WR2. cbn [cells_size csize Nat.add] in WR2.
cps_rt MSET0.
{ split; [intros _; split; [apply (acc_sub asegs m5 D 2968 (D + 2212) 16 ACL5); lia| left; exists D, 2968; split; [exact INL| lia]]|].
split; [intros i Hi; right; right; left; exists D, 2968; split; [exact INL| lia]| exact (proj2 MS2)]. }
{ cps_callok. }
intros c6 Hc6. unfold icpt_postF in Hc6.
cps_unpack_ex Hc6 as (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & BY6).
change (Z.to_nat 16) with 16%nat in BY6.
pose proof (ms_piece m5 m6 (D + 2212) 16 WR2 WM6 BY6) as MS2'. clear WR2 BY6 ACL5.

destruct (af_acc_live RT AF Σ1 m6 D 2968 ART6 INL) as (_ & ACL6).
assert (OBD6 : aobj asegs m6 D 2968) by (split; [lia|]; split; [ulc| exact ACL6]).
pose proof (AF_LIB Σ1 m6 ART6) as LC6.
cps_seg (nbinit_w4 usp lo D).
destruct POST as (m7 & xa3'' & -> & MU7 & WM7 & MI7 & HD7 & SEED7 & CBS7 & UCB7).
clear HD5 SEED CBS UCB OBD6 ACL6 LC6. cbn [cbs_zero app] in CBS7. unfold cb_zero in CBS7. cbn [app] in CBS7. cps_seg_post.
destruct (af_acc_live RT AF Σ1 m7 D 2968 ART INL) as (_ & ACL7).
pose proof (proj2 MS3) as WR3. cbn [cells_size csize Nat.add] in WR3.
cps_rt MSET0.
{ split; [intros _; split; [apply (acc_sub asegs m7 D 2968 (D + 2936) 24 ACL7); lia| left; exists D, 2968; split; [exact INL| lia]]|].
split; [intros i Hi; right; right; left; exists D, 2968; split; [exact INL| lia]| exact (proj2 MS3)]. }
{ cps_callok. }
intros c8 Hc8. unfold icpt_postF in Hc8.
cps_unpack_ex Hc8 as (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & BY8).
change (Z.to_nat 24) with 24%nat in BY8.
pose proof (ms_piece m7 m8 (D + 2936) 24 WR3 WM8 BY8) as MS3'. clear WR3 BY8 ACL7.

destruct (af_acc_live RT AF Σ1 m8 D 2968 ART8 INL) as (_ & ACL8).
assert (OBD8 : aobj asegs m8 D 2968) by (split; [lia|]; split; [ulc| exact ACL8]).
cps_seg (nbinit_w5 usp lo D).
destruct POST as (m9 & ya1 & ya2 & ya3 & -> & MU9 & WM9 & MI9 & ST9 & HPE9).
clear HPE OBD8 ACL8 FR1. cps_seg_post.

pose proof (rw_cells_join _ _ _ _ _ MS1' MID ltac:(cbn; lia)) as B1. clear MS1' MID.
apply nb_mid_recast in B1. unfold nb_mid_cells in B1.
piece B1 Q1. piece B1 Q2. piece B1 Q3. piece B1 Q4. piece B1 Q5. piece B1 Q6. piece B1 Q7. piece B1 Q8. rename B1 into Q9.
apply nb_pgb_recast in MS2'. piece MS2' Q11. rename MS2' into Q12.
pose proof (rw_cells_join _ _ _ _ _ MS3' (rw_cells_join _ _ _ _ _ HPE9 PAD ltac:(cbn; lia)) ltac:(cbn; lia)) as BT. clear MS3' HPE9 PAD.
apply nb_tailblk_recast in BT. piece BT Q17. rename BT into Q18.
assert (CBS9 : rw_cells asegs m9 (D + 2256) [CB 640 zcbs]) by (apply nb_cbs_recast; cbn [cbs_zero app]; unfold cb_zero; cbn [app]; exact CBS7).
clear CBS7.
apply Hk. exists Σ1, D. split; [| unfold NBSTATE_SIZEOF; repeat split; congruence].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m9.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI9|]. split; [cps_wmono| exact ST9]. }
split; [exact PF|].
intros OUT STEREO. cbn [decst_rep]. split; [reflexivity|].
split; [exact D8|]. split; [exact DPOS|]. split; [apply nb_init_inv|].
exists zjunk. split; [exact zjunk_ok|]. split; [apply zjunk_cbs|].
apply nb_cells_of_pieces; [exact zjunk_ok|]. unfold nb_pieces.
cbn [nb_hdr_cells nb_cfg_cells nb_tail_cells nb_ucb_cells cb_cells nb_isave_ptr nb_init_state nb_first nb_count_lost nb_sampling_rate
nb_innov_save nb_pitch_gain_buf_idx nb_encode_submode nb_submodeID nb_lpc_enh_enabled nb_voc_offset nb_dtx_enabled nb_isWideband
nb_highpass_enabled zjunk j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch
j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2 fst snd].
repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.
End NbInitCPS.
