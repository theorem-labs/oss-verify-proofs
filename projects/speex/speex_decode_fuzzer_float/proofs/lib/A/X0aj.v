(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ch X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1rh X1rg X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j5 X0ec X00a X001 X00b X000 X04b X07z X05o X05p X05s X08k X05u
X05l X05h X05c X05i X06e X0ak X0ai.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19o X14x X0r9 X0r0 X0ra X0qz X0v9 X0yr X0wl X0zb X0wn X0we X0w9 X0wf X0x6 X115 X113.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0we OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wf OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x6 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X115 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X113.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition p2h_bad_mode (pb : list byte) : Prop := ~ (0 <= s32 (fw pb 40) < 3).
Lemma p2h_prun : forall (pb : list byte) (size : Z) q r q', (80 <= size -> (80 <= length pb)%nat) ->
prun (speex_packet_to_header (St := pst) p_calloc p_free p_notify (map bv_unsigned pb) size) q = Some (r, q') ->
(size < 80 -> r = None /\ q' = p_app (notify_bytes MSG_HEADER_TOO_SMALL) q)
/\ (80 <= size -> firstn 8 pb <> MAGIC_BYTES -> r = None /\ q' = q)
/\ (80 <= size -> firstn 8 pb = MAGIC_BYTES -> p2h_bad_mode pb -> r = None /\ q' = p_app (notify_bytes MSG_INVALID_MODE_HEADER) q)
/\ (80 <= size -> firstn 8 pb = MAGIC_BYTES -> ~ p2h_bad_mode pb ->
r = Some (tt, set_nb_channels (header_of_bytes (map bv_unsigned pb)) (clamp_channels (hd_nb_channels (header_of_bytes (map bv_unsigned pb))))) /\ q' = q).
Proof.
intros pb size q r q' LEN H. unfold speex_packet_to_header in H.
assert (MGT : firstn 8 pb = MAGIC_BYTES -> list_eqb (ztake 8 (map bv_unsigned pb)) SPEEX_MAGIC = true).
{ intros EQ. apply list_eqb_eq. unfold ztake. change (Z.to_nat 8) with 8%nat. rewrite firstn_map, EQ. exact MAGIC_unsigned. }
assert (MGF : firstn 8 pb <> MAGIC_BYTES -> list_eqb (ztake 8 (map bv_unsigned pb)) SPEEX_MAGIC = false).
{ intros NE. destruct (list_eqb (ztake 8 (map bv_unsigned pb)) SPEEX_MAGIC) eqn:E; [|reflexivity]. exfalso. apply NE.
apply list_eqb_eq in E. unfold ztake in E. change (Z.to_nat 8) with 8%nat in E. rewrite firstn_map, <- MAGIC_unsigned in E.
apply byte_list_eq. exact E. }
split; [| split; [| split]].
- intros C. replace (size <? SIZEOF_SPEEX_HEADER) with true in H by (symmetry; apply Z.ltb_lt; unfold SIZEOF_SPEEX_HEADER; lia).
rewrite prun_bind, prun_notify in H. cbv beta iota in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- intros C NE. replace (size <? SIZEOF_SPEEX_HEADER) with false in H by (symmetry; apply Z.ltb_ge; unfold SIZEOF_SPEEX_HEADER; lia).
rewrite (MGF NE) in H. cbn [negb] in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- intros C EQ BAD. replace (size <? SIZEOF_SPEEX_HEADER) with false in H by (symmetry; apply Z.ltb_ge; unfold SIZEOF_SPEEX_HEADER; lia).
rewrite (MGT EQ) in H. cbn [negb] in H.
rewrite prun_bind, (prun_calloc_ok SIZEOF_SPEEX_HEADER 1 q) in H by (unfold SIZEOF_SPEEX_HEADER; lia). cbv beta iota in H.
destruct (header_fields pb (LEN C)) as (_ & _ & _ & E40 & _). cbv zeta in E40.
replace ((SPEEX_NB_MODES <=? hd_mode (header_of_bytes (map bv_unsigned pb))) || (hd_mode (header_of_bytes (map bv_unsigned pb)) <? 0)) with true in H.
2:{ symmetry. rewrite E40. unfold p2h_bad_mode in BAD. destruct (Z_lt_le_dec (s32 (fw pb 40)) 0) as [NEG|NN].
- rewrite (proj2 (Z.ltb_lt _ _) NEG). apply orb_true_r.
- unfold SPEEX_NB_MODES. rewrite (proj2 (Z.leb_le 3 (s32 (fw pb 40))) ltac:(lia)). reflexivity. }
rewrite !prun_bind, prun_notify in H. cbv beta iota in H. rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H.
injection H as <- <-. split; reflexivity.
- intros C EQ GOOD. replace (size <? SIZEOF_SPEEX_HEADER) with false in H by (symmetry; apply Z.ltb_ge; unfold SIZEOF_SPEEX_HEADER; lia).
rewrite (MGT EQ) in H. cbn [negb] in H.
rewrite prun_bind, (prun_calloc_ok SIZEOF_SPEEX_HEADER 1 q) in H by (unfold SIZEOF_SPEEX_HEADER; lia). cbv beta iota in H.
destruct (header_fields pb (LEN C)) as (_ & _ & _ & E40 & _). cbv zeta in E40.
replace ((SPEEX_NB_MODES <=? hd_mode (header_of_bytes (map bv_unsigned pb))) || (hd_mode (header_of_bytes (map bv_unsigned pb)) <? 0)) with false in H.
2:{ symmetry. rewrite E40. unfold p2h_bad_mode in GOOD. apply orb_false_intro; [apply Z.leb_gt; unfold SPEEX_NB_MODES; lia| apply Z.ltb_ge; lia]. }
rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Lemma p2h_magic_dec : forall pb : list byte, {firstn 8 pb = MAGIC_BYTES} + {firstn 8 pb <> MAGIC_BYTES}.
Proof.
intros pb. destruct (list_eqb (map bv_unsigned (firstn 8 pb)) SPEEX_MAGIC) eqn:E.
- left. apply list_eqb_eq in E. rewrite <- MAGIC_unsigned in E. apply byte_list_eq. exact E.
- right. intros EQ. rewrite EQ, MAGIC_unsigned in E. assert (X : list_eqb SPEEX_MAGIC SPEEX_MAGIC = true) by (apply list_eqb_eq; reflexivity). congruence.
Qed.
Lemma p2h_bad_mode_dec : forall pb, {p2h_bad_mode pb} + {~ p2h_bad_mode pb}.
Proof.
intros pb. unfold p2h_bad_mode. destruct (Z_le_dec 0 (s32 (fw pb 40))) as [A|A]; [destruct (Z_lt_dec (s32 (fw pb 40)) 3) as [B|B]|].
- right. intros X. apply X. split; assumption.
- left. intros [_ X]. exact (B X).
- left. intros [X _]. exact (A X).
Qed.

Lemma io_ssp_agree : forall (m m' : mem), io_ssp m -> drv_consts m' ->
(forall a : word, SSP_GUARD <= bv_unsigned a < SSP_GUARD + 8 -> m' a = m a) -> io_ssp m'.
Proof.
intros m m' (g & _ & G) DC AG. exists g. split; [exact (proj1 (proj2 DC))|].
apply (ro_cells_agree bsegs m m' _ _ G). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AG. unfold SSP_GUARD in *. lia.
Qed.
Lemma ssp_guard_static : forall x, SSP_GUARD <= x < SSP_GUARD + 8 -> client_static x.
Proof. intros x Hx. apply client_static_intro. unfold SSP_GUARD in Hx. lia. Qed.

Section P2HCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis AF_ERRV : forall Σ m, ART RT Σ m -> acc bsegs m STDERR_VAR 8.
Hypothesis FPL : fprintf_lib_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis CAL : calloc_contract RT.
Hypothesis MCPY : memcpy_icontract RT e_asan_memcpy.
Hypothesis FRE : free_contract RT.

Lemma aclient_live_remove_fresh : forall (Σ1 : rts RT) (m1 : mem) D n L frames sp a,
ART RT Σ1 m1 -> rt_live RT Σ1 = (D, n) :: L -> 0 < n -> aclient L frames sp a -> aclient (live_remove D L) frames sp a.
Proof using AF.
intros Σ1 m1 D n L frames sp a ART1 LV N0 [H|[H|[H|H]]]; [left; exact H| right; left; exact H| | right; right; right; exact H].
right; right; left. destruct H as (p' & n' & Hin & Hp). exists p', n'. split; [| exact Hp].
apply live_remove_keep; [exact Hin|]. cbn [fst]. intros ->.
destruct (af_live_disj RT AF Σ1 m1 D n D n' [] L ART1 LV Hin); lia.
Qed.

Definition p2h_result (m' : mem) (v : Z) (r : option (unit * spx_header)) (live live' : list (Z * Z)) : Prop :=
match r with
| None => v = 0 /\ (forall e, In e live -> 0 < snd e -> In e live') /\ (forall e, In e live' -> In e live)
/\ ((forall e, In e live -> 0 < snd e) -> live' = live)
| Some (_, hd) => exists junk28 w1 w2 w3 r1 r2,
0 < v /\ v mod 16 = 0 /\ live' = (v, SIZEOF_SPEEX_HEADER_Z) :: live
/\ rw_cells bsegs m' v (spx_header_cells junk28 hd w1 w2 w3 r1 r2)
/\ -2^31 <= hd_speex_version_id hd < 2^31 /\ -2^31 <= hd_rate hd < 2^31 /\ 0 <= hd_mode hd < SPEEX_NB_MODES
/\ -2^31 <= hd_mode_bitstream_version hd < 2^31 /\ 1 <= hd_nb_channels hd <= 2
/\ -2^31 <= hd_frames_per_packet hd < 2^31 /\ -2^31 <= hd_extra_headers hd < 2^31
end.

Definition speex_packet_to_header_cps : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (P pbase pn lo : Z) (pb : list byte) (size : Z) (q q' : pst) (r : option (unit * spx_header)),
prun (speex_packet_to_header (St := pst) p_calloc p_free p_notify (map bv_unsigned pb) size) q = Some (r, q') ->
a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 size -> tp = Z_to_bv 64 0x638c98 ->
u8ro bsegs m P pb -> 0 <= size <= Z.of_nat (length pb) -> size < 2^31 -> 0 < P -> P mod 4 = 0 ->
In (pbase, pn) (rt_live RT Σ) -> pbase <= P -> P + Z.of_nat (length pb) <= pbase + pn ->
fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> ERR_rep m -> io_ssp m ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
uw_site m RA_p2h_calloc s0 (bv_unsigned sp) lo ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 32 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
exists bs, p_err q' = p_err q ++ bs /\
cpsE bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_packet_to_header m)))
(Spec.X1nu.evw 2 bs)
(fun c => exists (Σ' : rts RT) (v : Z),
ASTA RT Σ' (PMfd F0 fs0) (fun ms => exists m',
ret_stL (fun F' fc' => X1cn.frm0 fc -> X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 v) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
/\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m')
/\ p2h_result m' v r (rt_live RT Σ) (rt_live RT Σ')) c
/\ Z.of_nat (length (rt_live RT Σ')) <= Z.of_nat (length (rt_live RT Σ)) + 1
/\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem speex_packet_to_header_ok : speex_packet_to_header_cps.
Proof using AF ERR_loc OUT_loc IO_img AF_DRV AF_ERRV FPL CAL MCPY FRE.
intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P pbase pn lo pb size q q' r
PRUN -> -> -> SRC Hsz S31 Ppos P4 INP PB1 PB2 FD2 ERR0 SSP0 LVM CR0 POA UW ART0 MI0 ST0 LOW LOR SPT SPA.
assert (LEN80 : 80 <= size -> (80 <= length pb)%nat) by (intros C; lia).
destruct (p2h_prun pb size q r q' LEN80 PRUN) as (PSMALL & PNOMAGIC & PBAD & PGOOD).
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
pose proof (PMfd_mat_stable F0 fs0) as MST. pose proof (PMfd_fdfs_only F0 fs0) as FDO.
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
destruct (live_below_lo RT AF Σ m pbase pn lo ART0 INP LOW) as (BP0 & BP1 & LOS).
pose proof (live_facts RT AF Σ m pbase pn ART0 INP) as (_ & _ & PIMG & PHI).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (AF_DRV Σ m ART0) as ((GOTE & VARE) & _). pose proof (AF_ERRV Σ m ART0) as ACV.
assert (OBV : aobj bsegs m RF_STDERR_VAR 8) by (split; [unfold RF_STDERR_VAR; lia|]; split; [unfold RF_STDERR_VAR, APP_TOP; lia| exact ACV]).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp IO_FP m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
cps_norm.
destruct (Z_lt_ge_dec size 80) as [SMALL|BIG].
-
destruct (PSMALL SMALL) as (-> & ->). exists (notify_bytes MSG_HEADER_TOO_SMALL). split; [reflexivity|].
intros T c Hc Hk. unfold entry_st in Hc. rewrite ESP in Hc.
destruct SSP0 as (gd & SSPa & SSPb).
cps_seg (p2h_small P size usp lo STDERR_FILE).
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
assert (ERR1 : ERR_rep m1).
{ apply (fp_local_munch IO_FP ERR_rep _ m m1 ERR_loc IO_img MU1); [| exact ERR0]. intros x Hx. cbn [outside]. repeat split; ulc. }
assert (OUT1 : forall so, OUT_rep so m -> OUT_rep so m1).
{ intros so. apply (fp_local_munch IO_FP (OUT_rep so) _ m m1 (OUT_loc so) IO_img MU1). intros x Hx. cbn [outside]. repeat split; ulc. }
clear OBV GOTE VARE. cps_seg_post.
assert (EU32 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ulc).
rewrite <- msg_too_small_unsigned, <- fpl_notify_bytes.
change (Spec.X1nu.evw 2 (fpl_msg FLnotify msg_too_small 0)) with (SpecA.X1rn.evw 2 (fpl_msg FLnotify msg_too_small 0)).
cps_rtE (FPL Σ F0 fs0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FLnotify P2H_FMT_NOTIFY P2H_MSG_TOO_SMALL 0 msg_too_small STDERR_FILE lo).
{ intros E; discriminate E. }
{ unfold fpl_fmts, P2H_FMT_NOTIFY. cbn [In]. right; left; reflexivity. }
{ exists 23. split; [unfold ACC_LITS, P2H_MSG_TOO_SMALL; cbn [In]; repeat (first [left; reflexivity | right])| vm_compute; intros X; discriminate X]. }
{ exact (msg_too_small_at m1 MI1). }
{ rewrite <- In0_map_unsigned. vm_compute. intuition discriminate. }
{ exists gd. split; assumption. }
{ cps_callok. }
{ rewrite EU32. apply (pois_above_le _ usp); [exact POA| lia]. }
intros c2 Hc2.
cps_unpack Hc2 as (rv & m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ERR2 & OUT2).
cps_seg (p2h_tail0 RA_p2h_fprintf_small usp lo).
destruct POST as (-> & ST3).
apply Hk. exists Σ, 0. split; [| split; [lia|]; repeat split; reflexivity].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m2.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact RS2]|].
split; [exact (conj ART2 (conj MI2 ST3))|].
split; [exact PF|]. split; [exact ERR2|]. split; [intros so Hso; exact (OUT2 so (OUT1 so Hso))|].
cbn [p2h_result]. split; [reflexivity|]. split; [intros e He _; exact He| split; [intros e He; exact He| intros _; reflexivity]].
-
assert (L80 : (80 <= length pb)%nat) by (clear - BIG Hsz; lia).
assert (OBP : aobj bsegs m P (Z.of_nat (length pb))).
{ split; [ulc|]. split; [ulc|]. apply (acc_sub bsegs m pbase pn); [exact (proj2 (af_acc_live RT AF Σ m pbase pn ART0 INP))| exact PB1| exact PB2]. }
assert (OBM : aobj bsegs m P2H_MAGIC 9)
by (apply (aobj_lit RT AF Σ m P2H_MAGIC 9 ART0); [unfold ACC_LITS, P2H_MAGIC; cbn [In]; repeat (first [left; reflexivity | right]) | unfold P2H_MAGIC; lia | unfold P2H_MAGIC, APP_TOP; lia]).
destruct (p2h_magic_dec pb) as [MAGIC|NOMAGIC].
2:{
destruct (PNOMAGIC ltac:(lia) NOMAGIC) as (-> & ->). exists []. split; [rewrite app_nil_r; reflexivity|].
apply cpsE_nil. intros T c Hc Hk. unfold entry_st in Hc. rewrite ESP in Hc.
cps_seg (p2h_magic P size usp lo pb).
destruct POST as (m1 & MU1 & WM1 & MI1 & [(_ & a1' & a2' & a5' & a6' & -> & ST1)|(EQ & _)]); [| exfalso; exact (NOMAGIC EQ)].
assert (ERR1 : ERR_rep m1).
{ apply (fp_local_munch IO_FP ERR_rep _ m m1 ERR_loc IO_img MU1); [| exact ERR0]. intros x Hx. cbn [outside]. repeat split; ulc. }
assert (OUT1 : forall so, OUT_rep so m -> OUT_rep so m1).
{ intros so. apply (fp_local_munch IO_FP (OUT_rep so) _ m m1 (OUT_loc so) IO_img MU1). intros x Hx. cbn [outside]. repeat split; ulc. }
clear OBV GOTE VARE OBP OBM. cps_seg_post.
apply Hk. exists Σ, 0. split; [| split; [lia|]; repeat split; reflexivity].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m1.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| intros X; exact X]|].
split; [exact (conj ART (conj MI1 ST1))|].
split; [exact PF|]. split; [exact ERR1|]. split; [exact OUT1|].
cbn [p2h_result]. split; [reflexivity|]. split; [intros e He _; exact He| split; [intros e He; exact He| intros _; reflexivity]]. }
destruct (p2h_bad_mode_dec pb) as [BAD|GOOD].
+
destruct (PBAD ltac:(lia) MAGIC BAD) as (-> & ->). exists (notify_bytes MSG_INVALID_MODE_HEADER). split; [reflexivity|].
intros T c Hc Hk. unfold entry_st in Hc. rewrite ESP in Hc.

cps_seg (p2h_magic P size usp lo pb).
destruct POST as (m1 & MU1 & WM1 & MI1 & [(NE & _)|(_ & a2' & a5' & a6' & -> & ST1 & FR1)]); [exfalso; exact (NE MAGIC)|].
assert (ERR1 : ERR_rep m1).
{ apply (fp_local_munch IO_FP ERR_rep _ m m1 ERR_loc IO_img MU1); [| exact ERR0]. intros x Hx. cbn [outside]. repeat split; ulc. }
assert (OUT1 : forall so, OUT_rep so m -> OUT_rep so m1).
{ intros so. apply (fp_local_munch IO_FP (OUT_rep so) _ m m1 (OUT_loc so) IO_img MU1). intros x Hx. cbn [outside]. repeat split; ulc. }
assert (SSP1 : io_ssp m1).
{ apply (io_ssp_agree m m1 SSP0); [| intros a Ha; apply MU1; cbn [outside]; split; [unfold SSP_GUARD in Ha; ulc| exact I]].
apply (AF_DRV Σ m1). apply (af_frame RT AF Σ m m1 lo ART0 LOW); [| exact WM1].
intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ulc. }
assert (UW1 : unwind_ch m1 (Z_to_bv 64 RA_p2h_calloc) s0 (Z_to_bv 64 (usp + -32))).
{ apply (uw_site_ch [(usp + -32, usp)] m m1 RA_p2h_calloc s0 usp (usp + -32) lo UW MU1 WM1); [repeat constructor; cbn; lia| ulc| lia| ulc| unfold RA_p2h_calloc; lia]. }
unfold u8ro in SRC. clear OBV GOTE VARE OBP OBM. cps_seg_post.
cps_rt CAL.
{ cps_callok. }
intros c2 (Σ1 & D & Hc2 & LV1 & FRS1 & SP1 & CR1 & DPOS & D16 & DTOP & PO1).
change (80 * 1) with 80 in *. change (mcost 80) with 0 in CR1. rewrite Z.sub_0_r in CR1. change (Z.to_nat 80) with 80%nat in *.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRD & ACD & BYD).
assert (ERR2 : ERR_rep m2) by exact (fp_local_pres IO_FP ERR_rep _ _ _ m1 m2 ERR_loc IO_img PRES2 ERR1).
assert (OUT2 : forall so, OUT_rep so m -> OUT_rep so m2).
{ intros so Hso. exact (fp_local_pres IO_FP (OUT_rep so) _ _ _ m1 m2 (OUT_loc so) IO_img PRES2 (OUT1 so Hso)). }
assert (SSP2 : io_ssp m2) by (apply (io_ssp_agree m1 m2 SSP1 (AF_DRV Σ1 m2 ART2)); intros a Ha; apply PRES2; right; left; exact (ssp_guard_static _ Ha)).
pose proof (fun a Ha => newchunk_apart RT AF Σ Σ1 m2 D 80 usp a ART2 LV1 FRS1 SP1 ltac:(ulc) ltac:(lia) Ha) as NAD.
pose proof (af_live_disj RT AF Σ1 m2 D 80 pbase pn [] _ ART2 LV1 INP) as APD.
assert (FRESH : forall n', In (D, n') (rt_live RT Σ) -> n' <= 0).
{ intros n' Hn. destruct (af_live_disj RT AF Σ1 m2 D 80 D n' [] _ ART2 LV1 Hn); lia. }
pose proof (fun frames sp a => aclient_live_remove_fresh Σ1 m2 D 80 (rt_live RT Σ) frames sp a ART2 LV1 ltac:(lia)) as ACLR.
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m2 D 80 lo ART2 INL LOW) as (_ & BD1 & _).
pose proof (live_facts RT AF Σ1 m2 D 80 ART2 INL) as (_ & _ & DIMG & DHI).
assert (D8 : D mod 8 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
cps_seg (p2h_copy P D usp). { ulc. } subst ms.

pose proof SRC as PK80. rewrite <- (firstn_skipn 80 pb) in PK80.
apply (proj1 (bytes_at_app bsegs m2 P (firstn 80 pb) (skipn 80 pb))) in PK80. destruct PK80 as [PK80 _].
assert (LB80 : Z.of_nat (length (firstn 80 pb)) = 80) by (rewrite length_firstn; lia).
cps_rt (MCPY Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 D P (firstn 80 pb) lo).
{ rewrite LB80. reflexivity. }
{ clear - Ppos PB2 BP1 LOR SPT Hsz. unfold RT_STACK in *. lia. }
{ unfold checked_src. rewrite LB80. split; [intros _; split; [apply (acc_sub bsegs m2 pbase pn P 80 (proj2 (af_acc_live RT AF Σ1 m2 pbase pn ART2 INP))); lia| left; exists pbase, pn; split; [exact INP| lia]]|].
left. clear - PB2 BP1 L80. lia. }
{ unfold checked_dst. rewrite LB80. split; [intros _; split; [exact ACD| left; exists D, 80; split; [exact INL| lia]]|].
split; [intros i Hi; right; right; left; exists D, 80; split; [exact INL| lia]| exact WRD]. }
{ cps_callok. }
intros c4 Hc4. unfold icpt_postF in Hc4. rewrite LB80 in Hc4.
cps_unpack_ex Hc4 as (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BY4).
assert (IMGD : forall x, D <= x < D + 80 -> x < 0x10000 \/ SEGTOP_A <= x) by (intros x Hx; clear - Hx DIMG; unfold SEGTOP_A in *; lia).
assert (ERR4 : ERR_rep m4).
{ apply (ERR_loc m2 m4 ERR2). intros a Ha. apply PRES4; [right; left; exact (IO_img _ Ha)|].
intros Hd. pose proof (client_static_range _ (IO_img _ Ha)) as R. destruct (IMGD _ Hd); lia. }
assert (OUT4 : forall so, OUT_rep so m -> OUT_rep so m4).
{ intros so Hso. apply (OUT_loc so m2 m4 (OUT2 so Hso)). intros a Ha. apply PRES4; [right; left; exact (IO_img _ Ha)|].
intros Hd. pose proof (client_static_range _ (IO_img _ Ha)) as R. destruct (IMGD _ Hd); lia. }
assert (SSP4 : io_ssp m4).
{ apply (io_ssp_agree m2 m4 SSP2 (AF_DRV Σ1 m4 ART4)). intros a Ha. apply PRES4; [right; left; exact (ssp_guard_static _ Ha)|].
intros Hd. pose proof (client_static_range _ (ssp_guard_static _ Ha)) as R. destruct (IMGD _ Hd); lia. }

assert (HDR4 : rw_cells bsegs m4 D (hdr_cells pb (Z_to_bv 64 (fw pb 48)))).
{ apply (hdr_cells_of_bytes m4 D pb L80).
split; [split; [split; [change (length (firstn 80 pb) = 80%nat); rewrite length_firstn; lia| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BY4]|].
cbn [cells_size csize Nat.add]. exact (wr_at_transport bsegs m2 m4 D _ WRD WM4). }
destruct (af_acc_live RT AF Σ1 m4 D 80 ART4 INL) as (_ & ACD4).
assert (OBD4 : aobj bsegs m4 D 80) by (split; [lia|]; split; [ulc| exact ACD4]).
pose proof (AF_DRV Σ1 m4 ART4) as ((GOTE4 & VARE4) & _). pose proof (AF_ERRV Σ1 m4 ART4) as ACV4.
assert (OBV4 : aobj bsegs m4 RF_STDERR_VAR 8) by (split; [unfold RF_STDERR_VAR; lia|]; split; [unfold RF_STDERR_VAR, APP_TOP; lia| exact ACV4]).
assert (DOFF : D + 80 <= SH_LO \/ SH_HI <= D) by (clear - DHI; unfold hid, SH_LO, SH_HI in *; lia).
cps_hide.
cps_seg (p2h_mode P D usp lo STDERR_FILE pb).
destruct POST as [(_ & a3x & ->)|(GOODM & _)]; [| exfalso; exact (BAD GOODM)].
assert (EU32 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ulc).
rewrite <- msg_bad_mode_unsigned, <- fpl_notify_bytes.
change (Spec.X1nu.evw 2 (fpl_msg FLnotify msg_bad_mode 0)) with (SpecA.X1rn.evw 2 (fpl_msg FLnotify msg_bad_mode 0)).
cps_rtE (FPL Σ1 F0 fs0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FLnotify P2H_FMT_NOTIFY P2H_MSG_BAD_MODE 0 msg_bad_mode STDERR_FILE lo).
{ intros E; discriminate E. }
{ unfold fpl_fmts, P2H_FMT_NOTIFY. cbn [In]. right; left; reflexivity. }
{ exists 39. split; [unfold ACC_LITS, P2H_MSG_BAD_MODE; cbn [In]; repeat (first [left; reflexivity | right])| vm_compute; intros X; discriminate X]. }
{ exact (msg_bad_mode_at m4 MI4). }
{ rewrite <- In0_map_unsigned. vm_compute. intuition discriminate. }
{ cps_callok. }
{ rewrite EU32. apply (pois_above_le _ usp); [exact POA| lia]. }
intros c6 Hc6.
cps_unpack Hc6 as (rv & m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & ERR6 & OUT6).
cps_seg (p2h_free P D usp). subst ms.

cps_rt (FRE Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 D 80 lo).
{ cps_callok. }
{ apply (unwind_ch_nf m6 _ _ _ lo); rewrite ?unsigned_lit by ulc;
[unfold ALLOC_RAS, RA_p2h_free; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc| ulc]. }
intros c8 (Σ2 & fv & Hc8 & LV2 & FRS2 & SP2 & CR2 & PO2).
revert PF.
cps_unpack Hc8 as (m8 & RS8 & (ART8 & MI8 & ST8) & PRES8).
intros PF.
pres_transport_g PRES8 ltac:(ulc).
assert (ERR8 : ERR_rep m8) by exact (fp_local_pres IO_FP ERR_rep _ _ _ m6 m8 ERR_loc IO_img PRES8 ERR6).
assert (OUT8 : forall so, OUT_rep so m -> OUT_rep so m8).
{ intros so Hso. exact (fp_local_pres IO_FP (OUT_rep so) _ _ _ m6 m8 (OUT_loc so) IO_img PRES8 (OUT6 so (OUT4 so Hso))). }
assert (SUB2 : forall e, In e (rt_live RT Σ) -> fst e <> D -> In e (rt_live RT Σ2)).
{ intros e He NE. rewrite LV2, LV1. apply live_remove_in. split; [right; exact He| exact NE]. }
assert (PF8 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp IO_FP m m8).
{ apply (pres_fp_trans _ _ _ _ m m6 m8 PF). intros a Ha _. apply PRES8.
pose proof (ACLR (rt_frames RT Σ) usp (bv_unsigned a) Ha) as Ha'.
destruct Ha' as [H|[H|[H|H]]]; [left; lia| right; left; exact H| | right; right; right; rewrite FRS1; exact H].
right; right; left. destruct H as (p' & n' & Hin & Hp). exists p', n'. split; [| exact Hp].
apply live_remove_in in Hin. destruct Hin as [Hin NE]. exact (SUB2 (p', n') Hin NE). }
clear PF. rename PF8 into PF.
cps_seg (p2h_tail0 RA_p2h_free usp lo).
destruct POST as (-> & ST9).
apply Hk. exists Σ2, 0. split.
2:{ split; [rewrite LV2, LV1; pose proof (list_basics.list.length_filter (fun e : Z * Z => negb (fst e =? D)) ((D, 80) :: rt_live RT Σ)) as LF; unfold live_remove; cbn [length] in LF |- *; lia|].
split; [rewrite FRS2; exact FRS1|]. split; [rewrite SP2; exact SP1|]. split; [rewrite CR2; exact CR1| rewrite PO2; exact PO1]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m8.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact RS6]|].
split; [exact (conj ART8 (conj MI8 ST9))|].
split; [exact PF|]. split; [exact ERR8|]. split; [exact OUT8|].
cbn [p2h_result]. split; [reflexivity|]. split.
* intros [p n] He POS. apply SUB2; [exact He|]. cbn [fst snd] in *. intros ->. pose proof (FRESH n He). lia.
* split; [intros e He; rewrite LV2, LV1 in He; apply live_remove_in in He; destruct He as [[<-|He] NE]; [exfalso; apply NE; reflexivity| exact He]|].
intros POS.
assert (LRC : forall pp ee ll, live_remove pp (ee :: ll) = if fst ee =? pp then live_remove pp ll else ee :: live_remove pp ll).
{ intros pp ee ll. unfold live_remove. rewrite stdpp.list_basics.list.filter_cons. destruct (fst ee =? pp); reflexivity. }
assert (LRN : forall pp ll, (forall ee, In ee ll -> fst ee <> pp) -> live_remove pp ll = ll).
{ intros pp ll HL. induction ll as [|xx ll IH]; [reflexivity|]. rewrite LRC.
replace (fst xx =? pp) with false by (symmetry; apply Z.eqb_neq; apply HL; left; reflexivity).
f_equal. apply IH. intros ee He. apply HL. right. exact He. }
rewrite LV2, LV1, LRC. cbn [fst]. rewrite Z.eqb_refl. apply LRN.
intros [pp nn] He E. cbn [fst] in E. subst pp. pose proof (FRESH nn He). pose proof (POS _ He). cbn [snd] in *. lia.
+
destruct (PGOOD ltac:(lia) MAGIC GOOD) as (-> & ->). exists []. split; [rewrite app_nil_r; reflexivity|].
apply cpsE_nil. intros T c Hc Hk. unfold entry_st in Hc. rewrite ESP in Hc.

cps_seg (p2h_magic P size usp lo pb).
destruct POST as (m1 & MU1 & WM1 & MI1 & [(NE & _)|(_ & a2' & a5' & a6' & -> & ST1 & FR1)]); [exfalso; exact (NE MAGIC)|].
assert (ERR1 : ERR_rep m1).
{ apply (fp_local_munch IO_FP ERR_rep _ m m1 ERR_loc IO_img MU1); [| exact ERR0]. intros x Hx. cbn [outside]. repeat split; ulc. }
assert (OUT1 : forall so, OUT_rep so m -> OUT_rep so m1).
{ intros so. apply (fp_local_munch IO_FP (OUT_rep so) _ m m1 (OUT_loc so) IO_img MU1). intros x Hx. cbn [outside]. repeat split; ulc. }
assert (SSP1 : io_ssp m1).
{ apply (io_ssp_agree m m1 SSP0); [| intros a Ha; apply MU1; cbn [outside]; split; [unfold SSP_GUARD in Ha; ulc| exact I]].
apply (AF_DRV Σ m1). apply (af_frame RT AF Σ m m1 lo ART0 LOW); [| exact WM1].
intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ulc. }
assert (UW1 : unwind_ch m1 (Z_to_bv 64 RA_p2h_calloc) s0 (Z_to_bv 64 (usp + -32))).
{ apply (uw_site_ch [(usp + -32, usp)] m m1 RA_p2h_calloc s0 usp (usp + -32) lo UW MU1 WM1); [repeat constructor; cbn; lia| ulc| lia| ulc| unfold RA_p2h_calloc; lia]. }
unfold u8ro in SRC. clear OBV GOTE VARE OBP OBM. cps_seg_post.
cps_rt CAL.
{ cps_callok. }
intros c2 (Σ1 & D & Hc2 & LV1 & FRS1 & SP1 & CR1 & DPOS & D16 & DTOP & PO1).
change (80 * 1) with 80 in *. change (mcost 80) with 0 in CR1. rewrite Z.sub_0_r in CR1. change (Z.to_nat 80) with 80%nat in *.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRD & ACD & BYD).
assert (ERR2 : ERR_rep m2) by exact (fp_local_pres IO_FP ERR_rep _ _ _ m1 m2 ERR_loc IO_img PRES2 ERR1).
assert (OUT2 : forall so, OUT_rep so m -> OUT_rep so m2).
{ intros so Hso. exact (fp_local_pres IO_FP (OUT_rep so) _ _ _ m1 m2 (OUT_loc so) IO_img PRES2 (OUT1 so Hso)). }
assert (SSP2 : io_ssp m2) by (apply (io_ssp_agree m1 m2 SSP1 (AF_DRV Σ1 m2 ART2)); intros a Ha; apply PRES2; right; left; exact (ssp_guard_static _ Ha)).
pose proof (fun a Ha => newchunk_apart RT AF Σ Σ1 m2 D 80 usp a ART2 LV1 FRS1 SP1 ltac:(ulc) ltac:(lia) Ha) as NAD.
pose proof (af_live_disj RT AF Σ1 m2 D 80 pbase pn [] _ ART2 LV1 INP) as APD.
assert (FRESH : forall n', In (D, n') (rt_live RT Σ) -> n' <= 0).
{ intros n' Hn. destruct (af_live_disj RT AF Σ1 m2 D 80 D n' [] _ ART2 LV1 Hn); lia. }
pose proof (fun frames sp a => aclient_live_remove_fresh Σ1 m2 D 80 (rt_live RT Σ) frames sp a ART2 LV1 ltac:(lia)) as ACLR.
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m2 D 80 lo ART2 INL LOW) as (_ & BD1 & _).
pose proof (live_facts RT AF Σ1 m2 D 80 ART2 INL) as (_ & _ & DIMG & DHI).
assert (D8 : D mod 8 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
cps_seg (p2h_copy P D usp). { ulc. } subst ms.

pose proof SRC as PK80. rewrite <- (firstn_skipn 80 pb) in PK80.
apply (proj1 (bytes_at_app bsegs m2 P (firstn 80 pb) (skipn 80 pb))) in PK80. destruct PK80 as [PK80 _].
assert (LB80 : Z.of_nat (length (firstn 80 pb)) = 80) by (rewrite length_firstn; lia).
cps_rt (MCPY Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 D P (firstn 80 pb) lo).
{ rewrite LB80. reflexivity. }
{ clear - Ppos PB2 BP1 LOR SPT Hsz. unfold RT_STACK in *. lia. }
{ unfold checked_src. rewrite LB80. split; [intros _; split; [apply (acc_sub bsegs m2 pbase pn P 80 (proj2 (af_acc_live RT AF Σ1 m2 pbase pn ART2 INP))); lia| left; exists pbase, pn; split; [exact INP| lia]]|].
left. clear - PB2 BP1 L80. lia. }
{ unfold checked_dst. rewrite LB80. split; [intros _; split; [exact ACD| left; exists D, 80; split; [exact INL| lia]]|].
split; [intros i Hi; right; right; left; exists D, 80; split; [exact INL| lia]| exact WRD]. }
{ cps_callok. }
intros c4 Hc4. unfold icpt_postF in Hc4. rewrite LB80 in Hc4.
cps_unpack_ex Hc4 as (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BY4).
assert (IMGD : forall x, D <= x < D + 80 -> x < 0x10000 \/ SEGTOP_A <= x) by (intros x Hx; clear - Hx DIMG; unfold SEGTOP_A in *; lia).
assert (ERR4 : ERR_rep m4).
{ apply (ERR_loc m2 m4 ERR2). intros a Ha. apply PRES4; [right; left; exact (IO_img _ Ha)|].
intros Hd. pose proof (client_static_range _ (IO_img _ Ha)) as R. destruct (IMGD _ Hd); lia. }
assert (OUT4 : forall so, OUT_rep so m -> OUT_rep so m4).
{ intros so Hso. apply (OUT_loc so m2 m4 (OUT2 so Hso)). intros a Ha. apply PRES4; [right; left; exact (IO_img _ Ha)|].
intros Hd. pose proof (client_static_range _ (IO_img _ Ha)) as R. destruct (IMGD _ Hd); lia. }
assert (SSP4 : io_ssp m4).
{ apply (io_ssp_agree m2 m4 SSP2 (AF_DRV Σ1 m4 ART4)). intros a Ha. apply PRES4; [right; left; exact (ssp_guard_static _ Ha)|].
intros Hd. pose proof (client_static_range _ (ssp_guard_static _ Ha)) as R. destruct (IMGD _ Hd); lia. }

assert (HDR4 : rw_cells bsegs m4 D (hdr_cells pb (Z_to_bv 64 (fw pb 48)))).
{ apply (hdr_cells_of_bytes m4 D pb L80).
split; [split; [split; [change (length (firstn 80 pb) = 80%nat); rewrite length_firstn; lia| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BY4]|].
cbn [cells_size csize Nat.add]. exact (wr_at_transport bsegs m2 m4 D _ WRD WM4). }
destruct (af_acc_live RT AF Σ1 m4 D 80 ART4 INL) as (_ & ACD4).
assert (OBD4 : aobj bsegs m4 D 80) by (split; [lia|]; split; [ulc| exact ACD4]).
pose proof (AF_DRV Σ1 m4 ART4) as ((GOTE4 & VARE4) & _). pose proof (AF_ERRV Σ1 m4 ART4) as ACV4.
assert (OBV4 : aobj bsegs m4 RF_STDERR_VAR 8) by (split; [unfold RF_STDERR_VAR; lia|]; split; [unfold RF_STDERR_VAR, APP_TOP; lia| exact ACV4]).
assert (DOFF : D + 80 <= SH_LO \/ SH_HI <= D) by (clear - DHI; unfold hid, SH_LO, SH_HI in *; lia).
cps_hide.
cps_seg (p2h_mode P D usp lo STDERR_FILE pb).
destruct POST as [(BADM & _)|(_ & m5 & a1' & a2'' & a3'' & -> & MU5 & WM5 & MI5 & ST5 & HDR5)]; [exfalso; exact (GOOD BADM)|].
assert (ERR5 : ERR_rep m5).
{ apply (fp_local_munch IO_FP ERR_rep _ m4 m5 ERR_loc IO_img MU5); [| exact ERR4]. intros x Hx. cbn [outside]. split; [| exact I].
intros Hd. destruct (IMGD _ Hd); unfold SEGTOP_A in *; lia. }
assert (OUT5 : forall so, OUT_rep so m -> OUT_rep so m5).
{ intros so Hso. apply (fp_local_munch IO_FP (OUT_rep so) _ m4 m5 (OUT_loc so) IO_img MU5); [| exact (OUT4 so Hso)]. intros x Hx. cbn [outside]. split; [| exact I].
intros Hd. destruct (IMGD _ Hd); unfold SEGTOP_A in *; lia. }
clear HDR4 FR1 OBD4 OBV4 GOTE4 VARE4. cps_seg_post.
apply Hk. exists Σ1, D. split.
2:{ split; [rewrite LV1; cbn [length]; lia|]. split; [exact FRS1|]. split; [exact SP1|]. split; [exact CR1| exact PO1]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m5.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| intros X; exact X]|].
split; [exact (conj ART (conj MI5 ST5))|].
split; [exact PF|]. split; [exact ERR5|]. split; [exact OUT5|].
cbn [p2h_result].
pose proof (header_fields pb L80) as HFS. cbv zeta in HFS. destruct HFS as (E28 & E32 & E36 & E40 & E44 & E48 & E64 & E68).
exists (firstn 28 pb), (Z_to_bv 64 (fw pb 52)), (Z_to_bv 64 (fw pb 56)), (Z_to_bv 64 (fw pb 60)), (Z_to_bv 64 (fw pb 72)), (Z_to_bv 64 (fw pb 76)).
split; [exact DPOS|]. split; [exact D16|]. split; [exact LV1|].
split; [rewrite E48; apply hdr_cells_post; [exact L80| exact HDR5]|].
cbn [hd_nb_channels hd_speex_version_id hd_rate hd_mode hd_mode_bitstream_version hd_frames_per_packet hd_extra_headers set_nb_channels].
rewrite E28, E36, E40, E44, E48, E64, E68.
pose proof (s32_range (fw pb 28)). pose proof (s32_range (fw pb 36)). pose proof (s32_range (fw pb 44)).
pose proof (s32_range (fw pb 48)). pose proof (s32_range (fw pb 64)). pose proof (s32_range (fw pb 68)).
unfold p2h_bad_mode in GOOD. unfold SPEEX_NB_MODES, clamp_channels.
destruct (2 <? s32 (fw pb 48)) eqn:C1; [|destruct (s32 (fw pb 48) <? 1) eqn:C2]; repeat split; lia.
Qed.
End P2HCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition p2h_bad_mode (pb : list byte) : Prop := ~ (0 <= s32 (fw pb 40) < 3).
Lemma p2h_prun : forall (pb : list byte) (size : Z) q r q', (80 <= size -> (80 <= length pb)%nat) ->
prun (speex_packet_to_header (St := pst) p_calloc p_free p_notify (map bv_unsigned pb) size) q = Some (r, q') ->
(size < 80 -> r = None /\ q' = p_app (notify_bytes MSG_HEADER_TOO_SMALL) q)
/\ (80 <= size -> firstn 8 pb <> MAGIC_BYTES -> r = None /\ q' = q)
/\ (80 <= size -> firstn 8 pb = MAGIC_BYTES -> p2h_bad_mode pb -> r = None /\ q' = p_app (notify_bytes MSG_INVALID_MODE_HEADER) q)
/\ (80 <= size -> firstn 8 pb = MAGIC_BYTES -> ~ p2h_bad_mode pb ->
r = Some (tt, set_nb_channels (header_of_bytes (map bv_unsigned pb)) (clamp_channels (hd_nb_channels (header_of_bytes (map bv_unsigned pb))))) /\ q' = q).
Proof.
intros pb size q r q' LEN H. unfold speex_packet_to_header in H.
assert (MGT : firstn 8 pb = MAGIC_BYTES -> list_eqb (ztake 8 (map bv_unsigned pb)) SPEEX_MAGIC = true).
{ intros EQ. apply list_eqb_eq. unfold ztake. change (Z.to_nat 8) with 8%nat. rewrite firstn_map, EQ. exact MAGIC_unsigned. }
assert (MGF : firstn 8 pb <> MAGIC_BYTES -> list_eqb (ztake 8 (map bv_unsigned pb)) SPEEX_MAGIC = false).
{ intros NE. destruct (list_eqb (ztake 8 (map bv_unsigned pb)) SPEEX_MAGIC) eqn:E; [|reflexivity]. exfalso. apply NE.
apply list_eqb_eq in E. unfold ztake in E. change (Z.to_nat 8) with 8%nat in E. rewrite firstn_map, <- MAGIC_unsigned in E.
apply byte_list_eq. exact E. }
split; [| split; [| split]].
- intros C. replace (size <? SIZEOF_SPEEX_HEADER) with true in H by (symmetry; apply Z.ltb_lt; unfold SIZEOF_SPEEX_HEADER; lia).
rewrite prun_bind, prun_notify in H. cbv beta iota in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- intros C NE. replace (size <? SIZEOF_SPEEX_HEADER) with false in H by (symmetry; apply Z.ltb_ge; unfold SIZEOF_SPEEX_HEADER; lia).
rewrite (MGF NE) in H. cbn [negb] in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- intros C EQ BAD. replace (size <? SIZEOF_SPEEX_HEADER) with false in H by (symmetry; apply Z.ltb_ge; unfold SIZEOF_SPEEX_HEADER; lia).
rewrite (MGT EQ) in H. cbn [negb] in H.
rewrite prun_bind, (prun_calloc_ok SIZEOF_SPEEX_HEADER 1 q) in H by (unfold SIZEOF_SPEEX_HEADER; lia). cbv beta iota in H.
destruct (header_fields pb (LEN C)) as (_ & _ & _ & E40 & _). cbv zeta in E40.
replace ((SPEEX_NB_MODES <=? hd_mode (header_of_bytes (map bv_unsigned pb))) || (hd_mode (header_of_bytes (map bv_unsigned pb)) <? 0)) with true in H.
2:{ symmetry. rewrite E40. unfold p2h_bad_mode in BAD. destruct (Z_lt_le_dec (s32 (fw pb 40)) 0) as [NEG|NN].
- rewrite (proj2 (Z.ltb_lt _ _) NEG). apply orb_true_r.
- unfold SPEEX_NB_MODES. rewrite (proj2 (Z.leb_le 3 (s32 (fw pb 40))) ltac:(lia)). reflexivity. }
rewrite !prun_bind, prun_notify in H. cbv beta iota in H. rewrite prun_bind, prun_free in H. cbv beta iota in H. rewrite prun_ret in H.
injection H as <- <-. split; reflexivity.
- intros C EQ GOOD. replace (size <? SIZEOF_SPEEX_HEADER) with false in H by (symmetry; apply Z.ltb_ge; unfold SIZEOF_SPEEX_HEADER; lia).
rewrite (MGT EQ) in H. cbn [negb] in H.
rewrite prun_bind, (prun_calloc_ok SIZEOF_SPEEX_HEADER 1 q) in H by (unfold SIZEOF_SPEEX_HEADER; lia). cbv beta iota in H.
destruct (header_fields pb (LEN C)) as (_ & _ & _ & E40 & _). cbv zeta in E40.
replace ((SPEEX_NB_MODES <=? hd_mode (header_of_bytes (map bv_unsigned pb))) || (hd_mode (header_of_bytes (map bv_unsigned pb)) <? 0)) with false in H.
2:{ symmetry. rewrite E40. unfold p2h_bad_mode in GOOD. apply orb_false_intro; [apply Z.leb_gt; unfold SPEEX_NB_MODES; lia| apply Z.ltb_ge; lia]. }
rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Lemma p2h_magic_dec : forall pb : list byte, {firstn 8 pb = MAGIC_BYTES} + {firstn 8 pb <> MAGIC_BYTES}.
Proof.
intros pb. destruct (list_eqb (map bv_unsigned (firstn 8 pb)) SPEEX_MAGIC) eqn:E.
- left. apply list_eqb_eq in E. rewrite <- MAGIC_unsigned in E. apply byte_list_eq. exact E.
- right. intros EQ. rewrite EQ, MAGIC_unsigned in E. assert (X : list_eqb SPEEX_MAGIC SPEEX_MAGIC = true) by (apply list_eqb_eq; reflexivity). congruence.
Qed.
Lemma p2h_bad_mode_dec : forall pb, {p2h_bad_mode pb} + {~ p2h_bad_mode pb}.
Proof.
intros pb. unfold p2h_bad_mode. destruct (Z_le_dec 0 (s32 (fw pb 40))) as [A|A]; [destruct (Z_lt_dec (s32 (fw pb 40)) 3) as [B|B]|].
- right. intros X. apply X. split; assumption.
- left. intros [_ X]. exact (B X).
- left. intros [X _]. exact (A X).
Qed.

Lemma io_ssp_agree : forall (m m' : mem), io_ssp m -> drv_consts m' ->
(forall a : word, SSP_GUARD <= bv_unsigned a < SSP_GUARD + 8 -> m' a = m a) -> io_ssp m'.
Proof.
intros m m' (g & _ & G) DC AG. exists g. split; [exact (proj1 (proj2 DC))|].
apply (ro_cells_agree asegs m m' _ _ G). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AG. unfold SSP_GUARD in *. lia.
Qed.
Lemma ssp_guard_static : forall x, SSP_GUARD <= x < SSP_GUARD + 8 -> client_static x.
Proof. intros x Hx. apply client_static_intro. unfold SSP_GUARD in Hx. lia. Qed.

Section P2HCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis AF_ERRV : forall Σ m, ART RT Σ m -> acc asegs m STDERR_VAR 8.
Hypothesis FPL : fprintf_lib_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis CAL : calloc_contract RT.
Hypothesis MCPY : memcpy_icontract RT e_asan_memcpy.
Hypothesis FRE : free_contract RT.

Lemma aclient_live_remove_fresh : forall (Σ1 : rts RT) (m1 : mem) D n L frames sp a,
ART RT Σ1 m1 -> rt_live RT Σ1 = (D, n) :: L -> 0 < n -> aclient L frames sp a -> aclient (live_remove D L) frames sp a.
Proof using AF.
intros Σ1 m1 D n L frames sp a ART1 LV N0 [H|[H|[H|H]]]; [left; exact H| right; left; exact H| | right; right; right; exact H].
right; right; left. destruct H as (p' & n' & Hin & Hp). exists p', n'. split; [| exact Hp].
apply live_remove_keep; [exact Hin|]. cbn [fst]. intros ->.
destruct (af_live_disj RT AF Σ1 m1 D n D n' [] L ART1 LV Hin); lia.
Qed.

Definition p2h_result (m' : mem) (v : Z) (r : option (unit * spx_header)) (live live' : list (Z * Z)) : Prop :=
match r with
| None => v = 0 /\ (forall e, In e live -> 0 < snd e -> In e live') /\ (forall e, In e live' -> In e live)
/\ ((forall e, In e live -> 0 < snd e) -> live' = live)
| Some (_, hd) => exists junk28 w1 w2 w3 r1 r2,
0 < v /\ v mod 16 = 0 /\ live' = (v, SIZEOF_SPEEX_HEADER_Z) :: live
/\ rw_cells asegs m' v (spx_header_cells junk28 hd w1 w2 w3 r1 r2)
/\ -2^31 <= hd_speex_version_id hd < 2^31 /\ -2^31 <= hd_rate hd < 2^31 /\ 0 <= hd_mode hd < SPEEX_NB_MODES
/\ -2^31 <= hd_mode_bitstream_version hd < 2^31 /\ 1 <= hd_nb_channels hd <= 2
/\ -2^31 <= hd_frames_per_packet hd < 2^31 /\ -2^31 <= hd_extra_headers hd < 2^31
end.

Definition speex_packet_to_header_cps : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (P pbase pn lo : Z) (pb : list byte) (size : Z) (q q' : pst) (r : option (unit * spx_header)),
prun (speex_packet_to_header (St := pst) p_calloc p_free p_notify (map bv_unsigned pb) size) q = Some (r, q') ->
a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 size -> tp = Z_to_bv 64 0x630458 ->
u8ro asegs m P pb -> 0 <= size <= Z.of_nat (length pb) -> size < 2^31 -> 0 < P ->
In (pbase, pn) (rt_live RT Σ) -> pbase <= P -> P + Z.of_nat (length pb) <= pbase + pn ->
fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> ERR_rep m -> io_ssp m ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
uw_site m RA_p2h_calloc s0 (bv_unsigned sp) lo ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 32 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
exists bs, p_err q' = p_err q ++ bs /\
cpsE asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_packet_to_header m)))
(Spec.X1nu.evw 2 bs)
(fun c => exists (Σ' : rts RT) (v : Z),
ASTA RT Σ' (PMfd F0 fs0) (fun ms => exists m',
ret_stL (fun F' fc' => X1cn.frm0 fc -> X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 v) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
/\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m')
/\ p2h_result m' v r (rt_live RT Σ) (rt_live RT Σ')) c
/\ Z.of_nat (length (rt_live RT Σ')) <= Z.of_nat (length (rt_live RT Σ)) + 1
/\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem speex_packet_to_header_ok : speex_packet_to_header_cps.
Proof using AF ERR_loc OUT_loc IO_img AF_DRV AF_ERRV FPL CAL MCPY FRE.
intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P pbase pn lo pb size q q' r
PRUN -> -> -> SRC Hsz S31 Ppos INP PB1 PB2 FD2 ERR0 SSP0 LVM CR0 POA UW ART0 MI0 ST0 LOW LOR SPT SPA.
assert (LEN80 : 80 <= size -> (80 <= length pb)%nat) by (intros C; lia).
destruct (p2h_prun pb size q r q' LEN80 PRUN) as (PSMALL & PNOMAGIC & PBAD & PGOOD).
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
pose proof (PMfd_mat_stable F0 fs0) as MST. pose proof (PMfd_fdfs_only F0 fs0) as FDO.
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
destruct (live_below_lo RT AF Σ m pbase pn lo ART0 INP LOW) as (BP0 & BP1 & LOS).
pose proof (live_facts RT AF Σ m pbase pn ART0 INP) as (_ & _ & PIMG & PHI).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (AF_DRV Σ m ART0) as ((GOTE & VARE) & _). pose proof (AF_ERRV Σ m ART0) as ACV.
assert (OBV : aobj asegs m RF_STDERR_VAR 8) by (split; [unfold RF_STDERR_VAR; lia|]; split; [unfold RF_STDERR_VAR, APP_TOP; lia| exact ACV]).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp IO_FP m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
cps_norm.
destruct (Z_lt_ge_dec size 80) as [SMALL|BIG].
-
destruct (PSMALL SMALL) as (-> & ->). exists (notify_bytes MSG_HEADER_TOO_SMALL). split; [reflexivity|].
intros T c Hc Hk. unfold entry_st in Hc. rewrite ESP in Hc.
destruct SSP0 as (gd & SSPa & SSPb).
cps_seg (p2h_small P size usp lo STDERR_FILE).
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
assert (ERR1 : ERR_rep m1).
{ apply (fp_local_munch IO_FP ERR_rep _ m m1 ERR_loc IO_img MU1); [| exact ERR0]. intros x Hx. cbn [outside]. repeat split; ulc. }
assert (OUT1 : forall so, OUT_rep so m -> OUT_rep so m1).
{ intros so. apply (fp_local_munch IO_FP (OUT_rep so) _ m m1 (OUT_loc so) IO_img MU1). intros x Hx. cbn [outside]. repeat split; ulc. }
clear OBV GOTE VARE. cps_seg_post.
assert (EU32 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ulc).
rewrite <- msg_too_small_unsigned, <- fpl_notify_bytes.
change (Spec.X1nu.evw 2 (fpl_msg FLnotify msg_too_small 0)) with (SpecA.X1rn.evw 2 (fpl_msg FLnotify msg_too_small 0)).
cps_rtE (FPL Σ F0 fs0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FLnotify P2H_FMT_NOTIFY P2H_MSG_TOO_SMALL 0 msg_too_small STDERR_FILE lo).
{ intros E; discriminate E. }
{ unfold fpl_fmts, P2H_FMT_NOTIFY. cbn [In]. right; left; reflexivity. }
{ exists 23. split; [unfold ACC_LITS, P2H_MSG_TOO_SMALL; cbn [In]; repeat (first [left; reflexivity | right])| vm_compute; intros X; discriminate X]. }
{ exact (msg_too_small_at m1 MI1). }
{ rewrite <- In0_map_unsigned. vm_compute. intuition discriminate. }
{ exists gd. split; assumption. }
{ cps_callok. }
{ rewrite EU32. apply (pois_above_le _ usp); [exact POA| lia]. }
intros c2 Hc2.
cps_unpack Hc2 as (rv & m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ERR2 & OUT2).
cps_seg (p2h_tail0 RA_p2h_fprintf_small usp lo).
destruct POST as (-> & ST3).
apply Hk. exists Σ, 0. split; [| split; [lia|]; repeat split; reflexivity].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m2.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact RS2]|].
split; [exact (conj ART2 (conj MI2 ST3))|].
split; [exact PF|]. split; [exact ERR2|]. split; [intros so Hso; exact (OUT2 so (OUT1 so Hso))|].
cbn [p2h_result]. split; [reflexivity|]. split; [intros e He _; exact He| split; [intros e He; exact He| intros _; reflexivity]].
-
assert (L80 : (80 <= length pb)%nat) by (clear - BIG Hsz; lia).
assert (OBP : aobj asegs m P (Z.of_nat (length pb))).
{ split; [ulc|]. split; [ulc|]. apply (acc_sub asegs m pbase pn); [exact (proj2 (af_acc_live RT AF Σ m pbase pn ART0 INP))| exact PB1| exact PB2]. }
assert (OBM : aobj asegs m P2H_MAGIC 9)
by (apply (aobj_lit RT AF Σ m P2H_MAGIC 9 ART0); [unfold ACC_LITS, P2H_MAGIC; cbn [In]; repeat (first [left; reflexivity | right]) | unfold P2H_MAGIC; lia | unfold P2H_MAGIC, APP_TOP; lia]).
destruct (p2h_magic_dec pb) as [MAGIC|NOMAGIC].
2:{
destruct (PNOMAGIC ltac:(lia) NOMAGIC) as (-> & ->). exists []. split; [rewrite app_nil_r; reflexivity|].
apply cpsE_nil. intros T c Hc Hk. unfold entry_st in Hc. rewrite ESP in Hc.
cps_seg (p2h_magic P size usp lo pb).
destruct POST as (m1 & MU1 & WM1 & MI1 & [(_ & a1' & a2' & a5' & a6' & -> & ST1)|(EQ & _)]); [| exfalso; exact (NOMAGIC EQ)].
assert (ERR1 : ERR_rep m1).
{ apply (fp_local_munch IO_FP ERR_rep _ m m1 ERR_loc IO_img MU1); [| exact ERR0]. intros x Hx. cbn [outside]. repeat split; ulc. }
assert (OUT1 : forall so, OUT_rep so m -> OUT_rep so m1).
{ intros so. apply (fp_local_munch IO_FP (OUT_rep so) _ m m1 (OUT_loc so) IO_img MU1). intros x Hx. cbn [outside]. repeat split; ulc. }
clear OBV GOTE VARE OBP OBM. cps_seg_post.
apply Hk. exists Σ, 0. split; [| split; [lia|]; repeat split; reflexivity].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m1.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| intros X; exact X]|].
split; [exact (conj ART (conj MI1 ST1))|].
split; [exact PF|]. split; [exact ERR1|]. split; [exact OUT1|].
cbn [p2h_result]. split; [reflexivity|]. split; [intros e He _; exact He| split; [intros e He; exact He| intros _; reflexivity]]. }
destruct (p2h_bad_mode_dec pb) as [BAD|GOOD].
+
destruct (PBAD ltac:(lia) MAGIC BAD) as (-> & ->). exists (notify_bytes MSG_INVALID_MODE_HEADER). split; [reflexivity|].
intros T c Hc Hk. unfold entry_st in Hc. rewrite ESP in Hc.

cps_seg (p2h_magic P size usp lo pb).
destruct POST as (m1 & MU1 & WM1 & MI1 & [(NE & _)|(_ & a2' & a5' & a6' & -> & ST1 & FR1)]); [exfalso; exact (NE MAGIC)|].
assert (ERR1 : ERR_rep m1).
{ apply (fp_local_munch IO_FP ERR_rep _ m m1 ERR_loc IO_img MU1); [| exact ERR0]. intros x Hx. cbn [outside]. repeat split; ulc. }
assert (OUT1 : forall so, OUT_rep so m -> OUT_rep so m1).
{ intros so. apply (fp_local_munch IO_FP (OUT_rep so) _ m m1 (OUT_loc so) IO_img MU1). intros x Hx. cbn [outside]. repeat split; ulc. }
assert (SSP1 : io_ssp m1).
{ apply (io_ssp_agree m m1 SSP0); [| intros a Ha; apply MU1; cbn [outside]; split; [unfold SSP_GUARD in Ha; ulc| exact I]].
apply (AF_DRV Σ m1). apply (af_frame RT AF Σ m m1 lo ART0 LOW); [| exact WM1].
intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ulc. }
assert (UW1 : unwind_ch m1 (Z_to_bv 64 RA_p2h_calloc) s0 (Z_to_bv 64 (usp + -32))).
{ apply (uw_site_ch [(usp + -32, usp)] m m1 RA_p2h_calloc s0 usp (usp + -32) lo UW MU1 WM1); [repeat constructor; cbn; lia| ulc| lia| ulc| unfold RA_p2h_calloc; lia]. }
unfold u8ro in SRC. clear OBV GOTE VARE OBP OBM. cps_seg_post.
cps_rt CAL.
{ cps_callok. }
intros c2 (Σ1 & D & Hc2 & LV1 & FRS1 & SP1 & CR1 & DPOS & D16 & DTOP & PO1).
change (80 * 1) with 80 in *. change (mcost 80) with 0 in CR1. rewrite Z.sub_0_r in CR1. change (Z.to_nat 80) with 80%nat in *.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRD & ACD & BYD).
assert (ERR2 : ERR_rep m2) by exact (fp_local_pres IO_FP ERR_rep _ _ _ m1 m2 ERR_loc IO_img PRES2 ERR1).
assert (OUT2 : forall so, OUT_rep so m -> OUT_rep so m2).
{ intros so Hso. exact (fp_local_pres IO_FP (OUT_rep so) _ _ _ m1 m2 (OUT_loc so) IO_img PRES2 (OUT1 so Hso)). }
assert (SSP2 : io_ssp m2) by (apply (io_ssp_agree m1 m2 SSP1 (AF_DRV Σ1 m2 ART2)); intros a Ha; apply PRES2; right; left; exact (ssp_guard_static _ Ha)).
pose proof (fun a Ha => newchunk_apart RT AF Σ Σ1 m2 D 80 usp a ART2 LV1 FRS1 SP1 ltac:(ulc) ltac:(lia) Ha) as NAD.
pose proof (af_live_disj RT AF Σ1 m2 D 80 pbase pn [] _ ART2 LV1 INP) as APD.
assert (FRESH : forall n', In (D, n') (rt_live RT Σ) -> n' <= 0).
{ intros n' Hn. destruct (af_live_disj RT AF Σ1 m2 D 80 D n' [] _ ART2 LV1 Hn); lia. }
pose proof (fun frames sp a => aclient_live_remove_fresh Σ1 m2 D 80 (rt_live RT Σ) frames sp a ART2 LV1 ltac:(lia)) as ACLR.
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m2 D 80 lo ART2 INL LOW) as (_ & BD1 & _).
pose proof (live_facts RT AF Σ1 m2 D 80 ART2 INL) as (_ & _ & DIMG & DHI).
assert (D8 : D mod 8 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
cps_seg (p2h_copy P D usp). subst ms.

pose proof SRC as PK80. rewrite <- (firstn_skipn 80 pb) in PK80.
apply (proj1 (bytes_at_app asegs m2 P (firstn 80 pb) (skipn 80 pb))) in PK80. destruct PK80 as [PK80 _].
assert (LB80 : Z.of_nat (length (firstn 80 pb)) = 80) by (rewrite length_firstn; lia).
cps_rt (MCPY Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 D P (firstn 80 pb) lo).
{ rewrite LB80. reflexivity. }
{ clear - Ppos PB2 BP1 LOR SPT Hsz. unfold RT_STACK in *. lia. }
{ unfold checked_src. rewrite LB80. split; [intros _; split; [apply (acc_sub asegs m2 pbase pn P 80 (proj2 (af_acc_live RT AF Σ1 m2 pbase pn ART2 INP))); lia| left; exists pbase, pn; split; [exact INP| lia]]|].
left. clear - PB2 BP1 L80. lia. }
{ unfold checked_dst. rewrite LB80. split; [intros _; split; [exact ACD| left; exists D, 80; split; [exact INL| lia]]|].
split; [intros i Hi; right; right; left; exists D, 80; split; [exact INL| lia]| exact WRD]. }
{ cps_callok. }
intros c4 Hc4. unfold icpt_postF in Hc4. rewrite LB80 in Hc4.
cps_unpack_ex Hc4 as (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BY4).
assert (IMGD : forall x, D <= x < D + 80 -> x < 0x10000 \/ SEGTOP_A <= x) by (intros x Hx; clear - Hx DIMG; unfold SEGTOP_A, IMG_TOP in *; lia).
assert (ERR4 : ERR_rep m4).
{ apply (ERR_loc m2 m4 ERR2). intros a Ha. apply PRES4; [right; left; exact (IO_img _ Ha)|].
intros Hd. pose proof (client_static_range _ (IO_img _ Ha)) as R. destruct (IMGD _ Hd); lia. }
assert (OUT4 : forall so, OUT_rep so m -> OUT_rep so m4).
{ intros so Hso. apply (OUT_loc so m2 m4 (OUT2 so Hso)). intros a Ha. apply PRES4; [right; left; exact (IO_img _ Ha)|].
intros Hd. pose proof (client_static_range _ (IO_img _ Ha)) as R. destruct (IMGD _ Hd); lia. }
assert (SSP4 : io_ssp m4).
{ apply (io_ssp_agree m2 m4 SSP2 (AF_DRV Σ1 m4 ART4)). intros a Ha. apply PRES4; [right; left; exact (ssp_guard_static _ Ha)|].
intros Hd. pose proof (client_static_range _ (ssp_guard_static _ Ha)) as R. destruct (IMGD _ Hd); lia. }

assert (HDR4 : rw_cells asegs m4 D (hdr_cells pb (Z_to_bv 64 (fw pb 48)))).
{ apply (hdr_cells_of_bytes m4 D pb L80).
split; [split; [split; [change (length (firstn 80 pb) = 80%nat); rewrite length_firstn; lia| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BY4]|].
cbn [cells_size csize Nat.add]. exact (wr_at_transport asegs m2 m4 D _ WRD WM4). }
destruct (af_acc_live RT AF Σ1 m4 D 80 ART4 INL) as (_ & ACD4).
assert (OBD4 : aobj asegs m4 D 80) by (split; [lia|]; split; [ulc| exact ACD4]).
pose proof (AF_DRV Σ1 m4 ART4) as ((GOTE4 & VARE4) & _). pose proof (AF_ERRV Σ1 m4 ART4) as ACV4.
assert (OBV4 : aobj asegs m4 RF_STDERR_VAR 8) by (split; [unfold RF_STDERR_VAR; lia|]; split; [unfold RF_STDERR_VAR, APP_TOP; lia| exact ACV4]).
assert (DOFF : D + 80 <= SH_LO \/ SH_HI <= D) by (clear - DHI; unfold hid, SH_LO, SH_HI in *; lia).
cps_hide.
cps_seg (p2h_mode P D usp lo STDERR_FILE pb).
destruct POST as [(_ & ->)|(GOODM & _)]; [| exfalso; exact (BAD GOODM)].
assert (EU32 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ulc).
rewrite <- msg_bad_mode_unsigned, <- fpl_notify_bytes.
change (Spec.X1nu.evw 2 (fpl_msg FLnotify msg_bad_mode 0)) with (SpecA.X1rn.evw 2 (fpl_msg FLnotify msg_bad_mode 0)).
cps_rtE (FPL Σ1 F0 fs0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FLnotify P2H_FMT_NOTIFY P2H_MSG_BAD_MODE 0 msg_bad_mode STDERR_FILE lo).
{ intros E; discriminate E. }
{ unfold fpl_fmts, P2H_FMT_NOTIFY. cbn [In]. right; left; reflexivity. }
{ exists 39. split; [unfold ACC_LITS, P2H_MSG_BAD_MODE; cbn [In]; repeat (first [left; reflexivity | right])| vm_compute; intros X; discriminate X]. }
{ exact (msg_bad_mode_at m4 MI4). }
{ rewrite <- In0_map_unsigned. vm_compute. intuition discriminate. }
{ cps_callok. }
{ rewrite EU32. apply (pois_above_le _ usp); [exact POA| lia]. }
intros c6 Hc6.
cps_unpack Hc6 as (rv & m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & ERR6 & OUT6).
cps_seg (p2h_free P D usp). subst ms.

cps_rt (FRE Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 D 80 lo).
{ cps_callok. }
{ apply (unwind_ch_nf m6 _ _ _ lo); rewrite ?unsigned_lit by ulc;
[unfold ALLOC_RAS, RA_p2h_free; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc| ulc]. }
intros c8 (Σ2 & fv & Hc8 & LV2 & FRS2 & SP2 & CR2 & PO2).
revert PF.
cps_unpack Hc8 as (m8 & RS8 & (ART8 & MI8 & ST8) & PRES8).
intros PF.
pres_transport_g PRES8 ltac:(ulc).
assert (ERR8 : ERR_rep m8) by exact (fp_local_pres IO_FP ERR_rep _ _ _ m6 m8 ERR_loc IO_img PRES8 ERR6).
assert (OUT8 : forall so, OUT_rep so m -> OUT_rep so m8).
{ intros so Hso. exact (fp_local_pres IO_FP (OUT_rep so) _ _ _ m6 m8 (OUT_loc so) IO_img PRES8 (OUT6 so (OUT4 so Hso))). }
assert (SUB2 : forall e, In e (rt_live RT Σ) -> fst e <> D -> In e (rt_live RT Σ2)).
{ intros e He NE. rewrite LV2, LV1. apply live_remove_in. split; [right; exact He| exact NE]. }
assert (PF8 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp IO_FP m m8).
{ apply (pres_fp_trans _ _ _ _ m m6 m8 PF). intros a Ha _. apply PRES8.
pose proof (ACLR (rt_frames RT Σ) usp (bv_unsigned a) Ha) as Ha'.
destruct Ha' as [H|[H|[H|H]]]; [left; lia| right; left; exact H| | right; right; right; rewrite FRS1; exact H].
right; right; left. destruct H as (p' & n' & Hin & Hp). exists p', n'. split; [| exact Hp].
apply live_remove_in in Hin. destruct Hin as [Hin NE]. exact (SUB2 (p', n') Hin NE). }
clear PF. rename PF8 into PF.
cps_seg (p2h_tail0 RA_p2h_free usp lo).
destruct POST as (-> & ST9).
apply Hk. exists Σ2, 0. split.
2:{ split; [rewrite LV2, LV1; pose proof (list_basics.list.length_filter (fun e : Z * Z => negb (fst e =? D)) ((D, 80) :: rt_live RT Σ)) as LF; unfold live_remove; cbn [length] in LF |- *; lia|].
split; [rewrite FRS2; exact FRS1|]. split; [rewrite SP2; exact SP1|]. split; [rewrite CR2; exact CR1| rewrite PO2; exact PO1]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m8.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact RS6]|].
split; [exact (conj ART8 (conj MI8 ST9))|].
split; [exact PF|]. split; [exact ERR8|]. split; [exact OUT8|].
cbn [p2h_result]. split; [reflexivity|]. split.
* intros [p n] He POS. apply SUB2; [exact He|]. cbn [fst snd] in *. intros ->. pose proof (FRESH n He). lia.
* split; [intros e He; rewrite LV2, LV1 in He; apply live_remove_in in He; destruct He as [[<-|He] NE]; [exfalso; apply NE; reflexivity| exact He]|].
intros POS.
assert (LRC : forall pp ee ll, live_remove pp (ee :: ll) = if fst ee =? pp then live_remove pp ll else ee :: live_remove pp ll).
{ intros pp ee ll. unfold live_remove. rewrite stdpp.list_basics.list.filter_cons. destruct (fst ee =? pp); reflexivity. }
assert (LRN : forall pp ll, (forall ee, In ee ll -> fst ee <> pp) -> live_remove pp ll = ll).
{ intros pp ll HL. induction ll as [|xx ll IH]; [reflexivity|]. rewrite LRC.
replace (fst xx =? pp) with false by (symmetry; apply Z.eqb_neq; apply HL; left; reflexivity).
f_equal. apply IH. intros ee He. apply HL. right. exact He. }
rewrite LV2, LV1, LRC. cbn [fst]. rewrite Z.eqb_refl. apply LRN.
intros [pp nn] He E. cbn [fst] in E. subst pp. pose proof (FRESH nn He). pose proof (POS _ He). cbn [snd] in *. lia.
+
destruct (PGOOD ltac:(lia) MAGIC GOOD) as (-> & ->). exists []. split; [rewrite app_nil_r; reflexivity|].
apply cpsE_nil. intros T c Hc Hk. unfold entry_st in Hc. rewrite ESP in Hc.

cps_seg (p2h_magic P size usp lo pb).
destruct POST as (m1 & MU1 & WM1 & MI1 & [(NE & _)|(_ & a2' & a5' & a6' & -> & ST1 & FR1)]); [exfalso; exact (NE MAGIC)|].
assert (ERR1 : ERR_rep m1).
{ apply (fp_local_munch IO_FP ERR_rep _ m m1 ERR_loc IO_img MU1); [| exact ERR0]. intros x Hx. cbn [outside]. repeat split; ulc. }
assert (OUT1 : forall so, OUT_rep so m -> OUT_rep so m1).
{ intros so. apply (fp_local_munch IO_FP (OUT_rep so) _ m m1 (OUT_loc so) IO_img MU1). intros x Hx. cbn [outside]. repeat split; ulc. }
assert (SSP1 : io_ssp m1).
{ apply (io_ssp_agree m m1 SSP0); [| intros a Ha; apply MU1; cbn [outside]; split; [unfold SSP_GUARD in Ha; ulc| exact I]].
apply (AF_DRV Σ m1). apply (af_frame RT AF Σ m m1 lo ART0 LOW); [| exact WM1].
intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ulc. }
assert (UW1 : unwind_ch m1 (Z_to_bv 64 RA_p2h_calloc) s0 (Z_to_bv 64 (usp + -32))).
{ apply (uw_site_ch [(usp + -32, usp)] m m1 RA_p2h_calloc s0 usp (usp + -32) lo UW MU1 WM1); [repeat constructor; cbn; lia| ulc| lia| ulc| unfold RA_p2h_calloc; lia]. }
unfold u8ro in SRC. clear OBV GOTE VARE OBP OBM. cps_seg_post.
cps_rt CAL.
{ cps_callok. }
intros c2 (Σ1 & D & Hc2 & LV1 & FRS1 & SP1 & CR1 & DPOS & D16 & DTOP & PO1).
change (80 * 1) with 80 in *. change (mcost 80) with 0 in CR1. rewrite Z.sub_0_r in CR1. change (Z.to_nat 80) with 80%nat in *.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRD & ACD & BYD).
assert (ERR2 : ERR_rep m2) by exact (fp_local_pres IO_FP ERR_rep _ _ _ m1 m2 ERR_loc IO_img PRES2 ERR1).
assert (OUT2 : forall so, OUT_rep so m -> OUT_rep so m2).
{ intros so Hso. exact (fp_local_pres IO_FP (OUT_rep so) _ _ _ m1 m2 (OUT_loc so) IO_img PRES2 (OUT1 so Hso)). }
assert (SSP2 : io_ssp m2) by (apply (io_ssp_agree m1 m2 SSP1 (AF_DRV Σ1 m2 ART2)); intros a Ha; apply PRES2; right; left; exact (ssp_guard_static _ Ha)).
pose proof (fun a Ha => newchunk_apart RT AF Σ Σ1 m2 D 80 usp a ART2 LV1 FRS1 SP1 ltac:(ulc) ltac:(lia) Ha) as NAD.
pose proof (af_live_disj RT AF Σ1 m2 D 80 pbase pn [] _ ART2 LV1 INP) as APD.
assert (FRESH : forall n', In (D, n') (rt_live RT Σ) -> n' <= 0).
{ intros n' Hn. destruct (af_live_disj RT AF Σ1 m2 D 80 D n' [] _ ART2 LV1 Hn); lia. }
pose proof (fun frames sp a => aclient_live_remove_fresh Σ1 m2 D 80 (rt_live RT Σ) frames sp a ART2 LV1 ltac:(lia)) as ACLR.
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m2 D 80 lo ART2 INL LOW) as (_ & BD1 & _).
pose proof (live_facts RT AF Σ1 m2 D 80 ART2 INL) as (_ & _ & DIMG & DHI).
assert (D8 : D mod 8 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
cps_seg (p2h_copy P D usp). subst ms.

pose proof SRC as PK80. rewrite <- (firstn_skipn 80 pb) in PK80.
apply (proj1 (bytes_at_app asegs m2 P (firstn 80 pb) (skipn 80 pb))) in PK80. destruct PK80 as [PK80 _].
assert (LB80 : Z.of_nat (length (firstn 80 pb)) = 80) by (rewrite length_firstn; lia).
cps_rt (MCPY Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 D P (firstn 80 pb) lo).
{ rewrite LB80. reflexivity. }
{ clear - Ppos PB2 BP1 LOR SPT Hsz. unfold RT_STACK in *. lia. }
{ unfold checked_src. rewrite LB80. split; [intros _; split; [apply (acc_sub asegs m2 pbase pn P 80 (proj2 (af_acc_live RT AF Σ1 m2 pbase pn ART2 INP))); lia| left; exists pbase, pn; split; [exact INP| lia]]|].
left. clear - PB2 BP1 L80. lia. }
{ unfold checked_dst. rewrite LB80. split; [intros _; split; [exact ACD| left; exists D, 80; split; [exact INL| lia]]|].
split; [intros i Hi; right; right; left; exists D, 80; split; [exact INL| lia]| exact WRD]. }
{ cps_callok. }
intros c4 Hc4. unfold icpt_postF in Hc4. rewrite LB80 in Hc4.
cps_unpack_ex Hc4 as (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BY4).
assert (IMGD : forall x, D <= x < D + 80 -> x < 0x10000 \/ SEGTOP_A <= x) by (intros x Hx; clear - Hx DIMG; unfold SEGTOP_A, IMG_TOP in *; lia).
assert (ERR4 : ERR_rep m4).
{ apply (ERR_loc m2 m4 ERR2). intros a Ha. apply PRES4; [right; left; exact (IO_img _ Ha)|].
intros Hd. pose proof (client_static_range _ (IO_img _ Ha)) as R. destruct (IMGD _ Hd); lia. }
assert (OUT4 : forall so, OUT_rep so m -> OUT_rep so m4).
{ intros so Hso. apply (OUT_loc so m2 m4 (OUT2 so Hso)). intros a Ha. apply PRES4; [right; left; exact (IO_img _ Ha)|].
intros Hd. pose proof (client_static_range _ (IO_img _ Ha)) as R. destruct (IMGD _ Hd); lia. }
assert (SSP4 : io_ssp m4).
{ apply (io_ssp_agree m2 m4 SSP2 (AF_DRV Σ1 m4 ART4)). intros a Ha. apply PRES4; [right; left; exact (ssp_guard_static _ Ha)|].
intros Hd. pose proof (client_static_range _ (ssp_guard_static _ Ha)) as R. destruct (IMGD _ Hd); lia. }

assert (HDR4 : rw_cells asegs m4 D (hdr_cells pb (Z_to_bv 64 (fw pb 48)))).
{ apply (hdr_cells_of_bytes m4 D pb L80).
split; [split; [split; [change (length (firstn 80 pb) = 80%nat); rewrite length_firstn; lia| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BY4]|].
cbn [cells_size csize Nat.add]. exact (wr_at_transport asegs m2 m4 D _ WRD WM4). }
destruct (af_acc_live RT AF Σ1 m4 D 80 ART4 INL) as (_ & ACD4).
assert (OBD4 : aobj asegs m4 D 80) by (split; [lia|]; split; [ulc| exact ACD4]).
pose proof (AF_DRV Σ1 m4 ART4) as ((GOTE4 & VARE4) & _). pose proof (AF_ERRV Σ1 m4 ART4) as ACV4.
assert (OBV4 : aobj asegs m4 RF_STDERR_VAR 8) by (split; [unfold RF_STDERR_VAR; lia|]; split; [unfold RF_STDERR_VAR, APP_TOP; lia| exact ACV4]).
assert (DOFF : D + 80 <= SH_LO \/ SH_HI <= D) by (clear - DHI; unfold hid, SH_LO, SH_HI in *; lia).
cps_hide.
cps_seg (p2h_mode P D usp lo STDERR_FILE pb).
destruct POST as [(BADM & _)|(_ & m5 & a1' & a2'' & -> & MU5 & WM5 & MI5 & ST5 & HDR5)]; [exfalso; exact (GOOD BADM)|].
assert (ERR5 : ERR_rep m5).
{ apply (fp_local_munch IO_FP ERR_rep _ m4 m5 ERR_loc IO_img MU5); [| exact ERR4]. intros x Hx. cbn [outside]. split; [| exact I].
intros Hd. destruct (IMGD _ Hd); unfold SEGTOP_A in *; lia. }
assert (OUT5 : forall so, OUT_rep so m -> OUT_rep so m5).
{ intros so Hso. apply (fp_local_munch IO_FP (OUT_rep so) _ m4 m5 (OUT_loc so) IO_img MU5); [| exact (OUT4 so Hso)]. intros x Hx. cbn [outside]. split; [| exact I].
intros Hd. destruct (IMGD _ Hd); unfold SEGTOP_A in *; lia. }
clear HDR4 FR1 OBD4 OBV4 GOTE4 VARE4. cps_seg_post.
apply Hk. exists Σ1, D. split.
2:{ split; [rewrite LV1; cbn [length]; lia|]. split; [exact FRS1|]. split; [exact SP1|]. split; [exact CR1| exact PO1]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m5.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| intros X; exact X]|].
split; [exact (conj ART (conj MI5 ST5))|].
split; [exact PF|]. split; [exact ERR5|]. split; [exact OUT5|].
cbn [p2h_result].
pose proof (header_fields pb L80) as HFS. cbv zeta in HFS. destruct HFS as (E28 & E32 & E36 & E40 & E44 & E48 & E64 & E68).
exists (firstn 28 pb), (Z_to_bv 64 (fw pb 52)), (Z_to_bv 64 (fw pb 56)), (Z_to_bv 64 (fw pb 60)), (Z_to_bv 64 (fw pb 72)), (Z_to_bv 64 (fw pb 76)).
split; [exact DPOS|]. split; [exact D16|]. split; [exact LV1|].
split; [rewrite E48; apply hdr_cells_post; [exact L80| exact HDR5]|].
cbn [hd_nb_channels hd_speex_version_id hd_rate hd_mode hd_mode_bitstream_version hd_frames_per_packet hd_extra_headers set_nb_channels].
rewrite E28, E36, E40, E44, E48, E64, E68.
pose proof (s32_range (fw pb 28)). pose proof (s32_range (fw pb 36)). pose proof (s32_range (fw pb 44)).
pose proof (s32_range (fw pb 48)). pose proof (s32_range (fw pb 64)). pose proof (s32_range (fw pb 68)).
unfold p2h_bad_mode in GOOD. unfold SPEEX_NB_MODES, clamp_channels.
destruct (2 <? s32 (fw pb 48)) eqn:C1; [|destruct (s32 (fw pb 48) <? 1) eqn:C2]; repeat split; lia.
Qed.
End P2HCPS.
