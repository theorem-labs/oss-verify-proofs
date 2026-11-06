(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ch.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s
X05l X05g X05h X05c.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0wl X0wd X0we X0w9.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wd OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0we OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma read_from_prun : forall (b : bits_st unit) (pkt : list Z) (len : Z) q r q',
prun (speex_bits_read_from (St := pst) p_realloc p_notify p_warning b pkt len) q = Some (r, q') ->
sb_owner b = 1 -> p_overflows len = false ->
(len <= sb_buf_size b ->
r = mkBits (sb_chars b) (ztake len pkt ++ zdrop len (sb_data b)) (len * 8) 0 0 (sb_owner b) 0 (sb_buf_size b) /\ q' = q)
/\ (sb_buf_size b < len ->
r = mkBits (sb_chars b) (ztake len pkt ++ zdrop len (sb_data b)) (len * 8) 0 0 (sb_owner b) 0 len
/\ q' = p_app (notify_bytes MSG_PACKET_LARGER) q).
Proof.
intros b pkt len q r q' H OWN OV. unfold speex_bits_read_from in H. split; intros C.
- replace (sb_buf_size b <? len) with false in H by (symmetry; apply Z.ltb_ge; lia).
rewrite prun_bind, prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- replace (sb_buf_size b <? len) with true in H by (symmetry; apply Z.ltb_lt; lia).
rewrite OWN in H. cbn [Z.eqb negb] in H.
rewrite !prun_bind, prun_notify in H. cbn beta iota in H. rewrite prun_bind, (prun_realloc_ok (sb_chars b) len _ OV) in H.
cbn beta iota in H. rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as <- <-.
split; [| reflexivity]. destruct (sb_chars b). rewrite OWN. reflexivity.
Qed.

Definition msg_larger : list byte := map (fun z => Z_to_bv 8 z) MSG_PACKET_LARGER.
Lemma msg_larger_at : forall m, mem_inv bsegs m -> bytes_at bsegs m RF_MSG_LARGER (msg_larger ++ [Z_to_bv 8 0]).
Proof.
intros m MI.
pose proof (ro_cells_image bsegs m RF_MSG_LARGER (msg_larger ++ [Z_to_bv 8 0]) MI ltac:(vm_compute; reflexivity) ltac:(unfold RF_MSG_LARGER; lia)
ltac:(vm_compute; intros X; discriminate X)) as [_ B].
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma msg_larger_nonul : ~ In (Z_to_bv 8 0) msg_larger.
Proof. rewrite <- In0_map_unsigned. vm_compute. intuition discriminate. Qed.
Lemma msg_larger_unsigned : map bv_unsigned msg_larger = MSG_PACKET_LARGER.
Proof. vm_compute. reflexivity. Qed.
Lemma fpl_notify_bytes : forall str, fpl_msg FLnotify str 0 = notify_bytes (map bv_unsigned str).
Proof. intros str. reflexivity. Qed.

Section ReadFromCPS.
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
Hypothesis REA : realloc_contract RT.

Definition READ_FROM_LEN_MAX : Z := 64512.

Definition speex_bits_read_from_cps : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A D P f pbase pn lo : Z) (k : nat) (b : bits_st unit) (pb : list byte) (len : Z) (q q' : pst) (r : bits_st unit),
prun (speex_bits_read_from (St := pst) p_realloc p_notify p_warning b (map bv_unsigned pb) len) q = Some (r, q') ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 P -> a2 = Z_to_bv 64 len -> tp = Z_to_bv 64 0x638c98 ->
bits_rep bsegs m A D b -> bits_ok b -> sb_owner b = 1 -> ro_cells bsegs m (shad A) bits_shadow ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 48 <= f + fs_size k - 8 ->
In (D, sb_buf_size b) (rt_live RT Σ) ->
u8ro bsegs m P pb -> 0 <= len <= Z.of_nat (length pb) -> len <= READ_FROM_LEN_MAX ->
In (pbase, pn) (rt_live RT Σ) -> pbase <= P -> P + Z.of_nat (length pb) <= pbase + pn -> pbase <> D ->
fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> ERR_rep m -> io_ssp m ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 160 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
exists bs, p_err q' = p_err q ++ bs /\
cpsE bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_bits_read_from m)))
(Spec.X1nu.evw 2 bs)
(fun c => exists (Σ' : rts RT) (D' : Z),
ASTA RT Σ' (PMfd F0 fs0) (fun ms => exists v m',
ret_stL (fun F' fc' => X1cn.frm0 fc -> X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) ((A, A + 48) :: IO_FP) m m'
/\ bits_rep bsegs m' A D' r /\ bits_ok r /\ ro_cells bsegs m' (shad A) bits_shadow
/\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m')) c
/\ In (D', sb_buf_size r) (rt_live RT Σ')
/\ ((len <= sb_buf_size b /\ D' = D /\ rt_live RT Σ' = rt_live RT Σ)
\/ (sb_buf_size b < len /\ rt_live RT Σ' = (D', len) :: live_remove D (rt_live RT Σ)))
/\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem speex_bits_read_from_ok : speex_bits_read_from_cps.
Proof using AF ERR_loc OUT_loc IO_img AF_DRV AF_ERRV FPL REA.
intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A D P f pbase pn lo k b pb len q q' r
PRUN -> -> -> -> REP OK OWN SHC INF FA1 FA2 INL SRC Hlen LMAX INP PB1 PB2 PND FD2 ERR0 SSP0 LVM CR0 POA ART0 MI0 ST0 LOW LOR SPT SPA.
unfold READ_FROM_LEN_MAX in LMAX.
assert (OV : p_overflows len = false) by (unfold p_overflows; apply Z.leb_gt; lia).
destruct (read_from_prun b (map bv_unsigned pb) len q r q' PRUN OWN OV) as [PFIT PBIG].
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold bits_shadow in SHC. cbn [map repeat] in SHC.
pose proof (PMfd_mat_stable F0 fs0) as MST. pose proof (PMfd_fdfs_only F0 fs0) as FDO.
pose proof REP as (_ & _ & (A8 & Apos & Dpos & _ & _ & SEPAD)).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (FS8 : fs_size k mod 8 = 0) by (unfold fs_size; rewrite Z.shiftl_mul_pow2 by lia; change 64 with (8 * 8); rewrite <- Z.mul_assoc, Z.mul_comm, Z.mod_mul by lia; reflexivity).
assert (LOT : lo + 80 <= APP_TOP) by (clear - LOR SPT; unfold APP_TOP, USTACK_TOP, RT_STACK in *; lia).
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).

destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
destruct (live_below_lo RT AF Σ m D (sb_buf_size b) lo ART0 INL LOW) as (BD0 & BD1 & _).
destruct (live_below_lo RT AF Σ m pbase pn lo ART0 INP LOW) as (BP0 & BP1 & _).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0' & F64 & FIMG & _ & FHI & _ & SHF1 & SHLO & _ & FSELF).
pose proof (live_facts RT AF Σ m D (sb_buf_size b) ART0 INL) as (_ & _ & DIMG & DHI).
pose proof (live_facts RT AF Σ m pbase pn ART0 INP) as (_ & _ & PIMG & PHI).
pose proof (live_remove_apart RT AF Σ m D (sb_buf_size b) pbase pn ART0 INL (live_remove_keep _ D (pbase, pn) INP PND)) as APD.
destruct (frame_live_apart RT AF Σ m f k pbase pn ART0 INF INP) as (FLP1 & FLP2).
destruct (frame_live_apart RT AF Σ m f k D (sb_buf_size b) ART0 INF INL) as (FLD1 & FLD2).
rewrite SHF1 in FLP2, FLD2.
destruct (shad_inside f (fs_size k) A 48 ltac:(clear - F64; Z.div_mod_to_equations; lia) A8 FS8 eq_refl ltac:(clear - F0'; lia) FA1 ltac:(clear - FA2; lia) ltac:(lia)) as (SHA1 & SHA2).
change (48 / 8) with 6 in SHA2.

assert (SEP1 : P + Z.of_nat (length pb) <= D \/ D + sb_buf_size b <= P) by (clear - APD PB1 PB2; lia).
assert (SEP3 : P + Z.of_nat (length pb) <= A \/ A + 48 <= P) by (clear - FLP1 PB1 PB2 FA1 FA2; lia).
assert (ASH : A + 48 <= SH_LO \/ SH_HI <= A) by (clear - FHI FA1 FA2 FSZ; unfold SH_LO, SH_HI; lia).
assert (DSH : D + sb_buf_size b <= SH_LO \/ SH_HI <= D) by (clear - DHI; unfold SH_LO, SH_HI; lia).
cps_hide.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (OBA : aobj bsegs m A 48) by (split; [ulc|]; split; [ulc|]; apply bits_shadow_acc; [exact SHC| exact A8| ulc]).
assert (OBD : aobj bsegs m D (sb_buf_size b)) by (split; [ulc|]; split; [ulc|]; exact (proj2 (af_acc_live RT AF Σ m D _ ART0 INL))).
assert (OBP : aobj bsegs m P (Z.of_nat (length pb))).
{ split; [ulc|]. split; [ulc|]. apply (acc_sub bsegs m pbase pn); [exact (proj2 (af_acc_live RT AF Σ m pbase pn ART0 INP))| exact PB1| exact PB2]. }
pose proof (pres_fp_refl (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp ((A, A + 48) :: IO_FP) m) as PF.
assert (SPL : forall a, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [apply live_remove_sub| auto| apply Z.le_refl]. }
pose proof (fun a => aclient_remove_apart RT AF Σ m D (sb_buf_size b) usp a ART0 INL LOU) as NAD.
cps_norm.
destruct (Z_le_gt_dec len (sb_buf_size b)) as [FITS|BIG].
-
destruct (PFIT FITS) as (-> & ->). exists []. split; [rewrite app_nil_r; reflexivity|].
apply cpsE_nil. intros T c Hc Hk. unfold entry_st in Hc. rewrite ESP in Hc.
cps_seg (read_from_fits_walk A P pb _ _ _ _ _ _ _ _ D len usp lo b).
destruct POST as (a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m2 & -> & MU2 & WM2 & MI2 & ST2 & REP2 & OK2 & SRC2).
assert (ERR2 : ERR_rep m2).
{ apply (fp_local_munch IO_FP ERR_rep _ m m2 ERR_loc IO_img MU2); [| exact ERR0]. intros x Hx. cbn [outside]. repeat split; ulc. }
assert (OUT2 : forall so, OUT_rep so m -> OUT_rep so m2).
{ intros so. apply (fp_local_munch IO_FP (OUT_rep so) _ m m2 (OUT_loc so) IO_img MU2). intros x Hx. cbn [outside]. repeat split; ulc. }
clear SRC OBA OBD OBP.
cps_seg_post.
apply Hk. exists Σ, D. split.
2:{ split; [exact INL|]. split; [left; split; [exact FITS| split; reflexivity]|]. repeat split; reflexivity. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists a0', m2.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| intros X; exact X]|].
split; [exact (conj ART (conj MI2 ST2))|].
split; [exact PF|]. split; [exact REP2|]. split; [exact OK2|].
split; [unfold bits_shadow; cbn [map repeat]; exact SHC|]. split; [exact ERR2| exact OUT2].
-
apply Z.gt_lt in BIG. destruct (PBIG BIG) as (-> & ->). exists (notify_bytes MSG_PACKET_LARGER). split; [reflexivity|].
intros T c Hc Hk. unfold entry_st in Hc. rewrite ESP in Hc.
pose proof (AF_DRV Σ m ART0) as ((GOTE & VARE) & _). pose proof (AF_ERRV Σ m ART0) as ACV.
assert (OBV : aobj bsegs m RF_STDERR_VAR 8) by (split; [unfold RF_STDERR_VAR; lia|]; split; [unfold RF_STDERR_VAR, APP_TOP; lia| exact ACV]).
destruct SSP0 as (gd & SSPa & SSPb).

cps_seg (read_from_big_w1 A P D len usp lo b _ _ _ _ _ _ STDERR_FILE).
destruct POST as (a3' & a4' & j0 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & REP1).
assert (ERR1 : ERR_rep m1).
{ apply (fp_local_munch IO_FP ERR_rep _ m m1 ERR_loc IO_img MU1); [| exact ERR0]. intros x Hx. cbn [outside]. repeat split; ulc. }
assert (OUT1 : forall so, OUT_rep so m -> OUT_rep so m1).
{ intros so. apply (fp_local_munch IO_FP (OUT_rep so) _ m m1 (OUT_loc so) IO_img MU1). intros x Hx. cbn [outside]. repeat split; ulc. }
unfold u8ro in SRC. clear OBA OBD OBP OBV GOTE VARE. cps_seg_post.
destruct REP1 as ((rj & Lrj & OBJ1) & (bs & ARR1 & Hbs) & SIDE1). apply u8arr_rw_CB in ARR1.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. clear - OK'. lia. }
unfold bits_cells in OBJ1.

assert (EU80 : bv_unsigned (Z_to_bv 64 (usp + -80)) = usp + -80) by (apply unsigned_lit; ulc).
rewrite <- msg_larger_unsigned, <- fpl_notify_bytes.
change (Spec.X1nu.evw 2 (fpl_msg FLnotify msg_larger 0)) with (SpecA.X1rn.evw 2 (fpl_msg FLnotify msg_larger 0)).
cps_rtE (FPL Σ F0 fs0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FLnotify RF_FMT_NOTIFY RF_MSG_LARGER 0 msg_larger STDERR_FILE lo).
{ intros E; discriminate E. }
{ left; reflexivity. }
{ exists 39. split; [unfold ACC_LITS, RF_MSG_LARGER; cbn [In]; repeat (first [left; reflexivity | right])| vm_compute; intros X; discriminate X]. }
{ exact (msg_larger_at m1 MI1). }
{ exact msg_larger_nonul. }
{ exists gd. split; assumption. }
{ cps_callok. }
{ rewrite EU80. apply (pois_above_le _ usp); [exact POA| lia]. }
intros c2 Hc2.
cps_unpack Hc2 as (rv & m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ERR2 & OUT2).

assert (REP2 : bits_rep bsegs m2 A D b).
{ split; [exists rj; split; [exact Lrj| exact OBJ1]|]. split; [exists bs; split; [apply u8arr_rw_CB; exact ARR1| exact Hbs]| exact SIDE1]. }
assert (OBA2 : aobj bsegs m2 A 48) by (split; [ulc|]; split; [ulc|]; apply bits_shadow_acc; [exact SHC| exact A8| ulc]).
cps_seg (read_from_big_w2 A P D len usp lo b).
destruct POST as (a2' & a3'' & ->).

assert (EU80' : bv_unsigned (Z_to_bv 64 (usp + -80)) = usp + -80) by (apply unsigned_lit; ulc).
cps_rt (REA Σ (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 D (sb_buf_size b) len lo bs).
{ destruct ARR1 as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. }
{ unfold mcost. replace (len <=? 64512) with true by (symmetry; apply Z.leb_le; exact LMAX). exact CR0. }
{ cps_callok. }
{ apply unwind_ok_ch. unfold unwind_ok, RA_rf_realloc. rewrite EU80', !unsigned_lit by ulc.
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]. }
intros c3 (Σ1 & qn & Hc3 & LV1 & FRS1 & SP1 & CR1 & QPOS & Q16 & QND & QTOP & PO1).
assert (INP' : In (pbase, pn) (live_remove D (rt_live RT Σ))) by (apply live_remove_keep; [exact INP| exact PND]).
cps_unpack Hc3 as (m3 & RS3 & (ART3 & MI3 & ST3) & PRES3 & WRQ & ACQ & BYQ).
assert (ERR3 : ERR_rep m3) by exact (fp_local_pres IO_FP ERR_rep _ _ _ m2 m3 ERR_loc IO_img PRES3 ERR2).
assert (OUT3 : forall so, OUT_rep so m -> OUT_rep so m3).
{ intros so Hso. exact (fp_local_pres IO_FP (OUT_rep so) _ _ _ m2 m3 (OUT_loc so) IO_img PRES3 (OUT2 so (OUT1 so Hso))). }
pose proof (fun a Ha => newchunk_apart_gen RT AF Σ Σ1 m3 qn len _ usp a ART3 LV1 FRS1 SP1 LOU ltac:(clear - Hlen; lia) Ha) as NAQ.
pose proof (af_live_disj RT AF Σ1 m3 qn len pbase pn [] _ ART3 LV1 INP') as APQ.
assert (INQ : In (qn, len) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m3 qn len lo ART3 INQ LOW) as (_ & BQ1 & _).
pose proof (live_facts RT AF Σ1 m3 qn len ART3 INQ) as (_ & _ & QIMG & QHI).
destruct (frame_live_apart RT AF Σ1 m3 f k qn len ART3 INF INQ) as (FLQ1 & FLQ2). rewrite SHF1 in FLQ2.
assert (SEPQ : P + Z.of_nat (length pb) <= qn \/ qn + len <= P) by (clear - APQ PB1 PB2; lia).
assert (SEPAQ : A + 48 <= qn \/ qn + len <= A) by (clear - FLQ1 FA1 FA2; lia).
assert (QSH : qn + len <= SH_LO \/ SH_HI <= qn) by (clear - QHI; unfold SH_LO, SH_HI; lia).
cps_norm. cps_hide.
destruct (wr_at_rw_CB m3 qn len WRQ ltac:(clear - Hlen; lia)) as (jq & BLKQ).
pose proof BLKQ as [[[LJ _] _] _].

assert (OBA3 : aobj bsegs m3 A 48) by (split; [ulc|]; split; [ulc|]; apply bits_shadow_acc; [exact SHC| exact A8| ulc]).
cps_seg (read_from_big_w3 A P D len usp lo b _ _ _ _ _ _ qn rj).
destruct POST as (a1' & m4 & -> & MU4 & WM4 & MI4 & OBJ4).
assert (ERR4 : ERR_rep m4).
{ apply (fp_local_munch IO_FP ERR_rep _ m3 m4 ERR_loc IO_img MU4); [| exact ERR3]. intros x Hx. cbn [outside]. repeat split; ulc. }
assert (OUT4 : forall so, OUT_rep so m -> OUT_rep so m4).
{ intros so Hso. apply (fp_local_munch IO_FP (OUT_rep so) _ m3 m4 (OUT_loc so) IO_img MU4); [| exact (OUT3 so Hso)]. intros x Hx. cbn [outside]. repeat split; ulc. }
clear OBJ1 OBA3 BYQ. cps_seg_post.

cbn [cell_wf] in LJ. rewrite <- LJ in BLKQ. apply u8arr_rw_CB in BLKQ.
assert (LJZ : Z.of_nat (length jq) = len) by (rewrite LJ; apply Z2Nat.id; clear - Hlen; lia).
assert (OBA4 : aobj bsegs m4 A 48) by (split; [ulc|]; split; [ulc|]; apply bits_shadow_acc; [exact SHC| exact A8| ulc]).
assert (OBQ4 : aobj bsegs m4 qn (Z.of_nat (length jq))).
{ rewrite LJZ. split; [ulc|]. split; [ulc|]. exact (proj2 (af_acc_live RT AF Σ1 m4 qn len ART INQ)). }
assert (OBP4 : aobj bsegs m4 P (Z.of_nat (length pb))).
{ split; [ulc|]. split; [ulc|]. apply (acc_sub bsegs m4 pbase pn); [exact (proj2 (af_acc_live RT AF Σ1 m4 pbase pn ART INP))| exact PB1| exact PB2]. }
set (b1 := mkBits (sb_chars b) (sb_data b) (sb_nbBits b) (sb_charPtr b) (sb_bitPtr b) (sb_owner b) (sb_overflow b) len) in *.
unfold rf_frame in FR1.
cps_seg (readfrom_tail A P pb _ _ _ _ _ _ _ _ len qn usp lo jq b1 rj j0).
{ subst b1. cbn [sb_buf_size]. clear - Hlen. lia. }
{ subst b1. cbn [sb_buf_size]. pose proof OK as (_ & OK1 & _). clear - BIG OK1 LMAX. lia. }
{ subst b1. cbn [sb_data]. unfold zdrop. pose proof OK as (OK0 & _). unfold zlength in OK0.
rewrite !skipn_all2; [reflexivity| clear - LJ; lia| clear - OK0 BIG; lia]. }
{ subst b1. cbn [sb_owner]. clear - OWN. lia. }
destruct POST as (a0' & a1'' & a2'' & a3''' & a4'' & a5' & a6' & a7' & m5 & -> & MU5 & WM5 & MI5 & ST5 & REP5 & OK5 & SRC5).
assert (ERR5 : ERR_rep m5).
{ apply (fp_local_munch IO_FP ERR_rep _ m4 m5 ERR_loc IO_img MU5); [| exact ERR4]. intros x Hx. cbn [outside]. repeat split; ulc. }
assert (OUT5 : forall so, OUT_rep so m -> OUT_rep so m5).
{ intros so Hso. apply (fp_local_munch IO_FP (OUT_rep so) _ m4 m5 (OUT_loc so) IO_img MU5); [| exact (OUT4 so Hso)]. intros x Hx. cbn [outside]. repeat split; ulc. }
clear SRC OBA4 OBQ4 OBP4 OBJ4 BLKQ FR1. cps_seg_post.
apply Hk. exists Σ1, qn. split.
2:{ split; [exact INQ|]. split; [right; split; [exact BIG| exact LV1]|]. split; [exact FRS1|]. split; [exact SP1|].
split; [| exact PO1]. rewrite CR1. unfold mcost. replace (len <=? 64512) with true by (symmetry; apply Z.leb_le; exact LMAX). apply Z.sub_0_r. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists a0', m5.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact RS2]|].
split; [exact (conj ART0 (conj MI5 ST5))|].
split; [exact PF|]. split; [exact REP5|]. split; [exact OK5|].
split; [unfold bits_shadow; cbn [map repeat]; exact SHC|]. split; [exact ERR5| exact OUT5].
Qed.
End ReadFromCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma read_from_prun : forall (b : bits_st unit) (pkt : list Z) (len : Z) q r q',
prun (speex_bits_read_from (St := pst) p_realloc p_notify p_warning b pkt len) q = Some (r, q') ->
sb_owner b = 1 -> p_overflows len = false ->
(len <= sb_buf_size b ->
r = mkBits (sb_chars b) (ztake len pkt ++ zdrop len (sb_data b)) (len * 8) 0 0 (sb_owner b) 0 (sb_buf_size b) /\ q' = q)
/\ (sb_buf_size b < len ->
r = mkBits (sb_chars b) (ztake len pkt ++ zdrop len (sb_data b)) (len * 8) 0 0 (sb_owner b) 0 len
/\ q' = p_app (notify_bytes MSG_PACKET_LARGER) q).
Proof.
intros b pkt len q r q' H OWN OV. unfold speex_bits_read_from in H. split; intros C.
- replace (sb_buf_size b <? len) with false in H by (symmetry; apply Z.ltb_ge; lia).
rewrite prun_bind, prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- replace (sb_buf_size b <? len) with true in H by (symmetry; apply Z.ltb_lt; lia).
rewrite OWN in H. cbn [Z.eqb negb] in H.
rewrite !prun_bind, prun_notify in H. cbn beta iota in H. rewrite prun_bind, (prun_realloc_ok (sb_chars b) len _ OV) in H.
cbn beta iota in H. rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as <- <-.
split; [| reflexivity]. destruct (sb_chars b). rewrite OWN. reflexivity.
Qed.

Definition msg_larger : list byte := map (fun z => Z_to_bv 8 z) MSG_PACKET_LARGER.
Lemma msg_larger_at : forall m, mem_inv asegs m -> bytes_at asegs m RF_MSG_LARGER (msg_larger ++ [Z_to_bv 8 0]).
Proof.
intros m MI.
pose proof (ro_cells_image asegs m RF_MSG_LARGER (msg_larger ++ [Z_to_bv 8 0]) MI ltac:(vm_compute; reflexivity) ltac:(unfold RF_MSG_LARGER; lia)
ltac:(vm_compute; intros X; discriminate X)) as [_ B].
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma msg_larger_nonul : ~ In (Z_to_bv 8 0) msg_larger.
Proof. rewrite <- In0_map_unsigned. vm_compute. intuition discriminate. Qed.
Lemma msg_larger_unsigned : map bv_unsigned msg_larger = MSG_PACKET_LARGER.
Proof. vm_compute. reflexivity. Qed.
Lemma fpl_notify_bytes : forall str, fpl_msg FLnotify str 0 = notify_bytes (map bv_unsigned str).
Proof. intros str. reflexivity. Qed.

Section ReadFromCPS.
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
Hypothesis REA : realloc_contract RT.

Definition READ_FROM_LEN_MAX : Z := 64512.

Definition speex_bits_read_from_cps : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A D P f pbase pn lo : Z) (k : nat) (b : bits_st unit) (pb : list byte) (len : Z) (q q' : pst) (r : bits_st unit),
prun (speex_bits_read_from (St := pst) p_realloc p_notify p_warning b (map bv_unsigned pb) len) q = Some (r, q') ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 P -> a2 = Z_to_bv 64 len -> tp = Z_to_bv 64 0x630458 ->
bits_rep asegs m A D b -> bits_ok b -> sb_owner b = 1 -> ro_cells asegs m (shad A) bits_shadow ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 48 <= f + fs_size k - 8 ->
In (D, sb_buf_size b) (rt_live RT Σ) ->
u8ro asegs m P pb -> 0 <= len <= Z.of_nat (length pb) -> len <= READ_FROM_LEN_MAX ->
In (pbase, pn) (rt_live RT Σ) -> pbase <= P -> P + Z.of_nat (length pb) <= pbase + pn -> pbase <> D ->
fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> ERR_rep m -> io_ssp m ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 160 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
exists bs, p_err q' = p_err q ++ bs /\
cpsE asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_bits_read_from m)))
(Spec.X1nu.evw 2 bs)
(fun c => exists (Σ' : rts RT) (D' : Z),
ASTA RT Σ' (PMfd F0 fs0) (fun ms => exists v m',
ret_stL (fun F' fc' => X1cn.frm0 fc -> X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) ((A, A + 48) :: IO_FP) m m'
/\ bits_rep asegs m' A D' r /\ bits_ok r /\ ro_cells asegs m' (shad A) bits_shadow
/\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m')) c
/\ In (D', sb_buf_size r) (rt_live RT Σ')
/\ ((len <= sb_buf_size b /\ D' = D /\ rt_live RT Σ' = rt_live RT Σ)
\/ (sb_buf_size b < len /\ rt_live RT Σ' = (D', len) :: live_remove D (rt_live RT Σ)))
/\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem speex_bits_read_from_ok : speex_bits_read_from_cps.
Proof using AF ERR_loc OUT_loc IO_img AF_DRV AF_ERRV FPL REA.
intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A D P f pbase pn lo k b pb len q q' r
PRUN -> -> -> -> REP OK OWN SHC INF FA1 FA2 INL SRC Hlen LMAX INP PB1 PB2 PND FD2 ERR0 SSP0 LVM CR0 POA ART0 MI0 ST0 LOW LOR SPT SPA.
unfold READ_FROM_LEN_MAX in LMAX.
assert (OV : p_overflows len = false) by (unfold p_overflows; apply Z.leb_gt; lia).
destruct (read_from_prun b (map bv_unsigned pb) len q r q' PRUN OWN OV) as [PFIT PBIG].
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold bits_shadow in SHC. cbn [map repeat] in SHC.
pose proof (PMfd_mat_stable F0 fs0) as MST. pose proof (PMfd_fdfs_only F0 fs0) as FDO.
pose proof REP as (_ & _ & (A8 & Apos & Dpos & _ & _ & SEPAD)).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (FS8 : fs_size k mod 8 = 0) by (unfold fs_size; rewrite Z.shiftl_mul_pow2 by lia; change 64 with (8 * 8); rewrite <- Z.mul_assoc, Z.mul_comm, Z.mod_mul by lia; reflexivity).
assert (LOT : lo + 80 <= APP_TOP) by (clear - LOR SPT; unfold APP_TOP, USTACK_TOP, RT_STACK in *; lia).
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).

destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
destruct (live_below_lo RT AF Σ m D (sb_buf_size b) lo ART0 INL LOW) as (BD0 & BD1 & _).
destruct (live_below_lo RT AF Σ m pbase pn lo ART0 INP LOW) as (BP0 & BP1 & _).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0' & F64 & FIMG & _ & FHI & _ & SHF1 & SHLO & _ & FSELF).
pose proof (live_facts RT AF Σ m D (sb_buf_size b) ART0 INL) as (_ & _ & DIMG & DHI).
pose proof (live_facts RT AF Σ m pbase pn ART0 INP) as (_ & _ & PIMG & PHI).
pose proof (live_remove_apart RT AF Σ m D (sb_buf_size b) pbase pn ART0 INL (live_remove_keep _ D (pbase, pn) INP PND)) as APD.
destruct (frame_live_apart RT AF Σ m f k pbase pn ART0 INF INP) as (FLP1 & FLP2).
destruct (frame_live_apart RT AF Σ m f k D (sb_buf_size b) ART0 INF INL) as (FLD1 & FLD2).
rewrite SHF1 in FLP2, FLD2.
destruct (shad_inside f (fs_size k) A 48 ltac:(clear - F64; Z.div_mod_to_equations; lia) A8 FS8 eq_refl ltac:(clear - F0'; lia) FA1 ltac:(clear - FA2; lia) ltac:(lia)) as (SHA1 & SHA2).
change (48 / 8) with 6 in SHA2.

assert (SEP1 : P + Z.of_nat (length pb) <= D \/ D + sb_buf_size b <= P) by (clear - APD PB1 PB2; lia).
assert (SEP3 : P + Z.of_nat (length pb) <= A \/ A + 48 <= P) by (clear - FLP1 PB1 PB2 FA1 FA2; lia).
assert (ASH : A + 48 <= SH_LO \/ SH_HI <= A) by (clear - FHI FA1 FA2 FSZ; unfold SH_LO, SH_HI; lia).
assert (DSH : D + sb_buf_size b <= SH_LO \/ SH_HI <= D) by (clear - DHI; unfold SH_LO, SH_HI; lia).
cps_hide.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (OBA : aobj asegs m A 48) by (split; [ulc|]; split; [ulc|]; apply bits_shadow_acc; [exact SHC| exact A8| ulc]).
assert (OBD : aobj asegs m D (sb_buf_size b)) by (split; [ulc|]; split; [ulc|]; exact (proj2 (af_acc_live RT AF Σ m D _ ART0 INL))).
assert (OBP : aobj asegs m P (Z.of_nat (length pb))).
{ split; [ulc|]. split; [ulc|]. apply (acc_sub asegs m pbase pn); [exact (proj2 (af_acc_live RT AF Σ m pbase pn ART0 INP))| exact PB1| exact PB2]. }
pose proof (pres_fp_refl (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp ((A, A + 48) :: IO_FP) m) as PF.
assert (SPL : forall a, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [apply live_remove_sub| auto| apply Z.le_refl]. }
pose proof (fun a => aclient_remove_apart RT AF Σ m D (sb_buf_size b) usp a ART0 INL LOU) as NAD.
cps_norm.
destruct (Z_le_gt_dec len (sb_buf_size b)) as [FITS|BIG].
-
destruct (PFIT FITS) as (-> & ->). exists []. split; [rewrite app_nil_r; reflexivity|].
apply cpsE_nil. intros T c Hc Hk. unfold entry_st in Hc. rewrite ESP in Hc.
cps_seg (read_from_fits_walk A P pb _ _ _ _ _ _ _ _ D len usp lo b).
destruct POST as (a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m2 & -> & MU2 & WM2 & MI2 & ST2 & REP2 & OK2 & SRC2).
assert (ERR2 : ERR_rep m2).
{ apply (fp_local_munch IO_FP ERR_rep _ m m2 ERR_loc IO_img MU2); [| exact ERR0]. intros x Hx. cbn [outside]. repeat split; ulc. }
assert (OUT2 : forall so, OUT_rep so m -> OUT_rep so m2).
{ intros so. apply (fp_local_munch IO_FP (OUT_rep so) _ m m2 (OUT_loc so) IO_img MU2). intros x Hx. cbn [outside]. repeat split; ulc. }
clear SRC OBA OBD OBP.
cps_seg_post.
apply Hk. exists Σ, D. split.
2:{ split; [exact INL|]. split; [left; split; [exact FITS| split; reflexivity]|]. repeat split; reflexivity. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists a0', m2.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| intros X; exact X]|].
split; [exact (conj ART (conj MI2 ST2))|].
split; [exact PF|]. split; [exact REP2|]. split; [exact OK2|].
split; [unfold bits_shadow; cbn [map repeat]; exact SHC|]. split; [exact ERR2| exact OUT2].
-
apply Z.gt_lt in BIG. destruct (PBIG BIG) as (-> & ->). exists (notify_bytes MSG_PACKET_LARGER). split; [reflexivity|].
intros T c Hc Hk. unfold entry_st in Hc. rewrite ESP in Hc.
pose proof (AF_DRV Σ m ART0) as ((GOTE & VARE) & _). pose proof (AF_ERRV Σ m ART0) as ACV.
assert (OBV : aobj asegs m RF_STDERR_VAR 8) by (split; [unfold RF_STDERR_VAR; lia|]; split; [unfold RF_STDERR_VAR, APP_TOP; lia| exact ACV]).
destruct SSP0 as (gd & SSPa & SSPb).

cps_seg (read_from_big_w1 A P D len usp lo b _ _ _ _ _ _ STDERR_FILE).
destruct POST as (a3' & a4' & j0 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & REP1).
assert (ERR1 : ERR_rep m1).
{ apply (fp_local_munch IO_FP ERR_rep _ m m1 ERR_loc IO_img MU1); [| exact ERR0]. intros x Hx. cbn [outside]. repeat split; ulc. }
assert (OUT1 : forall so, OUT_rep so m -> OUT_rep so m1).
{ intros so. apply (fp_local_munch IO_FP (OUT_rep so) _ m m1 (OUT_loc so) IO_img MU1). intros x Hx. cbn [outside]. repeat split; ulc. }
unfold u8ro in SRC. clear OBA OBD OBP OBV GOTE VARE. cps_seg_post.
destruct REP1 as ((rj & Lrj & OBJ1) & (bs & ARR1 & Hbs) & SIDE1). apply u8arr_rw_CB in ARR1.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. clear - OK'. lia. }
unfold bits_cells in OBJ1.

assert (EU80 : bv_unsigned (Z_to_bv 64 (usp + -80)) = usp + -80) by (apply unsigned_lit; ulc).
rewrite <- msg_larger_unsigned, <- fpl_notify_bytes.
change (Spec.X1nu.evw 2 (fpl_msg FLnotify msg_larger 0)) with (SpecA.X1rn.evw 2 (fpl_msg FLnotify msg_larger 0)).
cps_rtE (FPL Σ F0 fs0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FLnotify RF_FMT_NOTIFY RF_MSG_LARGER 0 msg_larger STDERR_FILE lo).
{ intros E; discriminate E. }
{ left; reflexivity. }
{ exists 39. split; [unfold ACC_LITS, RF_MSG_LARGER; cbn [In]; repeat (first [left; reflexivity | right])| vm_compute; intros X; discriminate X]. }
{ exact (msg_larger_at m1 MI1). }
{ exact msg_larger_nonul. }
{ exists gd. split; assumption. }
{ cps_callok. }
{ rewrite EU80. apply (pois_above_le _ usp); [exact POA| lia]. }
intros c2 Hc2.
cps_unpack Hc2 as (rv & m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ERR2 & OUT2).

assert (REP2 : bits_rep asegs m2 A D b).
{ split; [exists rj; split; [exact Lrj| exact OBJ1]|]. split; [exists bs; split; [apply u8arr_rw_CB; exact ARR1| exact Hbs]| exact SIDE1]. }
assert (OBA2 : aobj asegs m2 A 48) by (split; [ulc|]; split; [ulc|]; apply bits_shadow_acc; [exact SHC| exact A8| ulc]).
cps_seg (read_from_big_w2 A P D len usp lo b).
destruct POST as (a2' & a3'' & ->).

assert (EU80' : bv_unsigned (Z_to_bv 64 (usp + -80)) = usp + -80) by (apply unsigned_lit; ulc).
cps_rt (REA Σ (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 D (sb_buf_size b) len lo bs).
{ destruct ARR1 as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. }
{ unfold mcost. replace (len <=? 64512) with true by (symmetry; apply Z.leb_le; exact LMAX). exact CR0. }
{ cps_callok. }
{ apply unwind_ok_ch. unfold unwind_ok, RA_rf_realloc. rewrite EU80', !unsigned_lit by ulc.
split; [unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right])| left; ulc]. }
intros c3 (Σ1 & qn & Hc3 & LV1 & FRS1 & SP1 & CR1 & QPOS & Q16 & QND & QTOP & PO1).
assert (INP' : In (pbase, pn) (live_remove D (rt_live RT Σ))) by (apply live_remove_keep; [exact INP| exact PND]).
cps_unpack Hc3 as (m3 & RS3 & (ART3 & MI3 & ST3) & PRES3 & WRQ & ACQ & BYQ).
assert (ERR3 : ERR_rep m3) by exact (fp_local_pres IO_FP ERR_rep _ _ _ m2 m3 ERR_loc IO_img PRES3 ERR2).
assert (OUT3 : forall so, OUT_rep so m -> OUT_rep so m3).
{ intros so Hso. exact (fp_local_pres IO_FP (OUT_rep so) _ _ _ m2 m3 (OUT_loc so) IO_img PRES3 (OUT2 so (OUT1 so Hso))). }
pose proof (fun a Ha => newchunk_apart_gen RT AF Σ Σ1 m3 qn len _ usp a ART3 LV1 FRS1 SP1 LOU ltac:(clear - Hlen; lia) Ha) as NAQ.
pose proof (af_live_disj RT AF Σ1 m3 qn len pbase pn [] _ ART3 LV1 INP') as APQ.
assert (INQ : In (qn, len) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m3 qn len lo ART3 INQ LOW) as (_ & BQ1 & _).
pose proof (live_facts RT AF Σ1 m3 qn len ART3 INQ) as (_ & _ & QIMG & QHI).
destruct (frame_live_apart RT AF Σ1 m3 f k qn len ART3 INF INQ) as (FLQ1 & FLQ2). rewrite SHF1 in FLQ2.
assert (SEPQ : P + Z.of_nat (length pb) <= qn \/ qn + len <= P) by (clear - APQ PB1 PB2; lia).
assert (SEPAQ : A + 48 <= qn \/ qn + len <= A) by (clear - FLQ1 FA1 FA2; lia).
assert (QSH : qn + len <= SH_LO \/ SH_HI <= qn) by (clear - QHI; unfold SH_LO, SH_HI; lia).
cps_norm. cps_hide.
destruct (wr_at_rw_CB m3 qn len WRQ ltac:(clear - Hlen; lia)) as (jq & BLKQ).
pose proof BLKQ as [[[LJ _] _] _].

assert (OBA3 : aobj asegs m3 A 48) by (split; [ulc|]; split; [ulc|]; apply bits_shadow_acc; [exact SHC| exact A8| ulc]).
cps_seg (read_from_big_w3 A P D len usp lo b _ _ _ _ _ _ qn rj).
destruct POST as (a1' & m4 & -> & MU4 & WM4 & MI4 & OBJ4).
assert (ERR4 : ERR_rep m4).
{ apply (fp_local_munch IO_FP ERR_rep _ m3 m4 ERR_loc IO_img MU4); [| exact ERR3]. intros x Hx. cbn [outside]. repeat split; ulc. }
assert (OUT4 : forall so, OUT_rep so m -> OUT_rep so m4).
{ intros so Hso. apply (fp_local_munch IO_FP (OUT_rep so) _ m3 m4 (OUT_loc so) IO_img MU4); [| exact (OUT3 so Hso)]. intros x Hx. cbn [outside]. repeat split; ulc. }
clear OBJ1 OBA3 BYQ. cps_seg_post.

cbn [cell_wf] in LJ. rewrite <- LJ in BLKQ. apply u8arr_rw_CB in BLKQ.
assert (LJZ : Z.of_nat (length jq) = len) by (rewrite LJ; apply Z2Nat.id; clear - Hlen; lia).
assert (OBA4 : aobj asegs m4 A 48) by (split; [ulc|]; split; [ulc|]; apply bits_shadow_acc; [exact SHC| exact A8| ulc]).
assert (OBQ4 : aobj asegs m4 qn (Z.of_nat (length jq))).
{ rewrite LJZ. split; [ulc|]. split; [ulc|]. exact (proj2 (af_acc_live RT AF Σ1 m4 qn len ART INQ)). }
assert (OBP4 : aobj asegs m4 P (Z.of_nat (length pb))).
{ split; [ulc|]. split; [ulc|]. apply (acc_sub asegs m4 pbase pn); [exact (proj2 (af_acc_live RT AF Σ1 m4 pbase pn ART INP))| exact PB1| exact PB2]. }
set (b1 := mkBits (sb_chars b) (sb_data b) (sb_nbBits b) (sb_charPtr b) (sb_bitPtr b) (sb_owner b) (sb_overflow b) len) in *.
unfold rf_frame in FR1.
cps_seg (readfrom_tail A P pb _ _ _ _ _ _ _ _ len qn usp lo jq b1 rj j0).
{ subst b1. cbn [sb_buf_size]. clear - Hlen. lia. }
{ subst b1. cbn [sb_buf_size]. pose proof OK as (_ & OK1 & _). clear - BIG OK1 LMAX. lia. }
{ subst b1. cbn [sb_data]. unfold zdrop. pose proof OK as (OK0 & _). unfold zlength in OK0.
rewrite !skipn_all2; [reflexivity| clear - LJ; lia| clear - OK0 BIG; lia]. }
{ subst b1. cbn [sb_owner]. clear - OWN. lia. }
destruct POST as (a0' & a1'' & a2'' & a3''' & a4'' & a5' & a6' & a7' & m5 & -> & MU5 & WM5 & MI5 & ST5 & REP5 & OK5 & SRC5).
assert (ERR5 : ERR_rep m5).
{ apply (fp_local_munch IO_FP ERR_rep _ m4 m5 ERR_loc IO_img MU5); [| exact ERR4]. intros x Hx. cbn [outside]. repeat split; ulc. }
assert (OUT5 : forall so, OUT_rep so m -> OUT_rep so m5).
{ intros so Hso. apply (fp_local_munch IO_FP (OUT_rep so) _ m4 m5 (OUT_loc so) IO_img MU5); [| exact (OUT4 so Hso)]. intros x Hx. cbn [outside]. repeat split; ulc. }
clear SRC OBA4 OBQ4 OBP4 OBJ4 BLKQ FR1. cps_seg_post.
apply Hk. exists Σ1, qn. split.
2:{ split; [exact INQ|]. split; [right; split; [exact BIG| exact LV1]|]. split; [exact FRS1|]. split; [exact SP1|].
split; [| exact PO1]. rewrite CR1. unfold mcost. replace (len <=? 64512) with true by (symmetry; apply Z.leb_le; exact LMAX). apply Z.sub_0_r. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists a0', m5.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact RS2]|].
split; [exact (conj ART0 (conj MI5 ST5))|].
split; [exact PF|]. split; [exact REP5|]. split; [exact OK5|].
split; [unfold bits_shadow; cbn [map repeat]; exact SHC|]. split; [exact ERR5| exact OUT5].
Qed.
End ReadFromCPS.
