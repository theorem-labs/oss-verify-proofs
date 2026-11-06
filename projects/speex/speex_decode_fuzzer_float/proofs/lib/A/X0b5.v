(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1da X1dg X1cg X1ch X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X00a X000.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X05u X05t
X081 X05l X05m X09f X06d X069 X05w X063 X082 X08y X0b1 X0b0 X068 X05a
X0ay X0bf X07y X0b3 X0az X0b2 X0ar X07l X08b.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0r9 X0qz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0wn X0wm X0ys X0x2 X0wp X0yt X0zq X11l X11k X0x1 X0w7 X11i X122 X0yq X11n X11j X11c X0yd X0z2.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X0j9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X05m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X09f OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X06d.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w7 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X122 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yd OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma ctl_stack_le_dec : forall d : dec_state bptr, ctl_stack d <= dec_stack d.
Proof.
induction d as [st | s low IH]; cbn [ctl_stack dec_stack]; [unfold NBCTL_STACK, NBDEC_STACK; lia|].
unfold SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK. lia.
Qed.
Lemma ctl_stack_nonneg : forall d : dec_state bptr, 0 <= ctl_stack d.
Proof. induction d; cbn [ctl_stack]; unfold NBCTL_STACK; lia. Qed.

Lemma sbd_io_ssp_agree : forall (m m' : mem), io_ssp m -> drv_consts m' ->
(forall a : word, X0r9.SSP_GUARD <= bv_unsigned a < X0r9.SSP_GUARD + 8 -> m' a = m a) -> io_ssp m'.
Proof.
intros m m' (g & _ & G) DC AG. exists g. split; [exact (proj1 (proj2 DC))|].
apply (ro_cells_agree bsegs m m' _ _ G). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AG. unfold X0r9.SSP_GUARD in *. lia.
Qed.
Lemma sbd_ssp_static : forall x, X0r9.SSP_GUARD <= x < X0r9.SSP_GUARD + 8 -> client_static x.
Proof. intros x Hx. apply X0qz.client_static_intro. unfold X0r9.SSP_GUARD in Hx. lia. Qed.

Lemma cells_size_sb_fshadow : cells_size sb_fshadow = 8%nat. Proof. reflexivity. Qed.

Lemma sbd_low1_facts : forall (s : sbd_state bptr) (low : dec_state bptr) OUTL STEREO (m : mem) S' LBL,
sb_inv s -> dec_nestedR (DecSB s low) -> DREP OUTL STEREO m S' (snd (speex_decoder_ctl low (CtlSetInnovationSave (0 + sbd_frame_size s)))) LBL ->
isave_ok (snd (speex_decoder_ctl low (CtlSetInnovationSave (0 + sbd_frame_size s)))) /\
dec_nestedR (snd (speex_decoder_ctl low (CtlSetInnovationSave (0 + sbd_frame_size s)))).
Proof.
intros s low OUTL STEREO m S' LBL INV NEST R.
destruct INV as (IMODE & IFS & _). cbn [dec_nestedR] in NEST. destruct NEST as (NM & NL).
destruct low as [st | s' low']; cbn [speex_decoder_ctl nb_decoder_ctl snd isave_ok dec_nestedR] in *.
- replace (nb_innov_save (set_nb_innov_save st (Some (0 + sbd_frame_size s)))) with (Some (0 + sbd_frame_size s)) by (destruct st; reflexivity).
split; [| exact I]. rewrite IFS. destruct IMODE as [E|E]; rewrite E in NM |- *; cbn in NM |- *; [lia| discriminate NM].
- cbn [decst_rep] in R. destruct R as (a' & j' & LBL' & _ & _ & _ & INV' & _). cbn [dec_mode] in NM.
destruct INV' as (IMODE' & IFS' & _).
replace (sbd_innov_save (set_sbd_innov_save s' (Some (0 + sbd_frame_size s)))) with (Some (0 + sbd_frame_size s)) by (destruct s'; reflexivity).
replace (sbd_frame_size (set_sbd_innov_save s' (Some (0 + sbd_frame_size s)))) with (sbd_frame_size s') in * by (destruct s'; reflexivity).
replace (sbd_mode (set_sbd_innov_save s' (Some (0 + sbd_frame_size s)))) with (sbd_mode s') in * by (destruct s'; reflexivity).
split; [| exact NL].
rewrite IFS, IFS'. destruct IMODE as [E|E]; rewrite E in NM |- *; cbn [sbm_nb_mode] in NM; cbn [sbm_frameSize];
destruct IMODE' as [E'|E']; rewrite E' in NM |- *; cbn [sbm_frameSize]; first [discriminate NM | reflexivity].
Qed.

Lemma ctl_keeps_res : forall (d : dec_state bptr) r,
dec_frames (snd (speex_decoder_ctl d r)) = dec_frames d /\ dec_credit (snd (speex_decoder_ctl d r)) = dec_credit d
/\ dec_stack (snd (speex_decoder_ctl d r)) = dec_stack d.
Proof.
induction d as [st | s0 low0 IH]; intros r.
- cbn [speex_decoder_ctl]. destruct (nb_decoder_ctl st r). cbn [snd dec_frames dec_credit dec_stack]. repeat split; reflexivity.
- destruct r; cbn [speex_decoder_ctl];
first [ cbn [snd dec_frames dec_credit dec_stack]; repeat split; reflexivity
| match goal with |- context [speex_decoder_ctl low0 ?r'] =>
pose proof (IH r') as (F1 & C1 & S1); pose proof (ctl_keeps_depth low0 r') as D1;
destruct (speex_decoder_ctl low0 r') as [vx lx] eqn:E; cbn [snd] in F1, C1, S1, D1 |- *;
cbn [dec_frames dec_credit dec_stack]; rewrite F1, C1, S1, D1; repeat split; reflexivity end ].
Qed.

Lemma sbd_rz_dec : forall (RT0 : rt_sig) (Σ0 : rts RT0) PMc ms (e0 e1 bl : list Z) (Q : config -> Prop) T0 c0,
ASTA RT0 Σ0 PMc (eq ms) c0 -> e1 = e0 ++ bl ->
(exists bs, e1 = e0 ++ bs /\ cpsE bsegs (ASTA RT0 Σ0 PMc (eq ms)) (Spec.X1nu.evw 2 bs) Q) ->
(forall c', Q c' -> realizes bsegs c' T0) -> realizes bsegs c0 (t_emit (Spec.X1nu.evw 2 bl) T0).
Proof.
intros RT0 Σ0 PMc ms e0 e1 bl Q T0 c0 Hc E (bs & E' & CP) K.
assert (bs = bl) by (rewrite E in E'; apply app_inv_head in E'; congruence). subst bs. exact (CP T0 c0 Hc K).
Qed.

Lemma sbd_dtx_acc : forall (m : mem) f sf, rw_cells bsegs m sf sb_fshadow -> sf = Z.shiftr f 3 + SHB -> f mod 64 = 0 -> 0 <= f -> acc bsegs m (f + 32) 4.
Proof.
intros m0 f0 sf0 [[_ B] _] Esf F64 F0. unfold sb_fshadow in B. cbn [cells_bytes cbytes app] in B.
apply acc_ushadow; [clear - F64; Z.div_mod_to_equations; lia | lia | lia |].
change (ushadow 4) with [Z_to_bv 8 4].
replace (shad (f0 + 32)) with (sf0 + Z.of_nat 4).
- apply (bytes_at_nth1 bsegs m0 sf0 _ 4%nat _ B). reflexivity.
- rewrite Esf, shad_shiftr. unfold shad. clear - F64. Z.div_mod_to_equations. lia.
Qed.

Lemma dec_res_depth : forall d d' : dec_state bptr, dec_depth d = dec_depth d' ->
dec_stack d = dec_stack d' /\ dec_frames d = dec_frames d' /\ dec_credit d = dec_credit d' /\ ctl_stack d = ctl_stack d'.
Proof.
induction d as [st | s0 low0 IH]; intros [st' | s0' low0'] E; cbn [dec_depth] in E.
- cbn [dec_stack dec_frames dec_credit ctl_stack]. repeat split; reflexivity.
- pose proof (dec_depth_pos low0'). lia.
- pose proof (dec_depth_pos low0). lia.
- injection E as E. destruct (IH low0' E) as (E1 & E2 & E3 & E4). cbn [dec_stack dec_frames dec_credit ctl_stack]. rewrite E1, E2, E3, E4, E. repeat split; reflexivity.
Qed.

Lemma ctl_keeps_mode_nest : forall (d : dec_state bptr) r,
dec_mode (snd (speex_decoder_ctl d r)) = dec_mode d /\ (dec_nestedR d -> dec_nestedR (snd (speex_decoder_ctl d r))).
Proof.
induction d as [st | s0 low0 IH]; intros r.
- cbn [speex_decoder_ctl]. destruct (nb_decoder_ctl st r). cbn [snd dec_mode dec_nestedR]. split; [reflexivity| intros _; exact I].
- destruct r; cbn [speex_decoder_ctl];
first [ cbn [snd dec_mode dec_nestedR]; split; [destruct s0; reflexivity | intros H; destruct s0; exact H]
| match goal with |- context [speex_decoder_ctl low0 ?r'] =>
pose proof (IH r') as (M1 & N1);
destruct (speex_decoder_ctl low0 r') as [vx lx] eqn:E; cbn [snd] in M1, N1 |- *;
cbn [dec_mode dec_nestedR]; split; [destruct s0; reflexivity| intros (H1 & H2); split; [rewrite M1; destruct s0; exact H1 | exact (N1 H2)]] end ].
Qed.

Lemma rz_emit_nil : forall c0 T0, realizes bsegs c0 T0 -> realizes bsegs c0 (t_emit [] T0).
Proof. intros c0 T0 R. eapply rz_conseq; [exact R|]. apply t_eq_sym. apply t_emit_nil_eq. eapply realizes_nonempty. exact R. Qed.

Definition sb_msg_invalid : list byte := map (fun z => Z_to_bv 8 z) MSG_INVALID_MODE.
Lemma sb_msg_invalid_at : forall m, mem_inv bsegs m -> bytes_at bsegs m SB_MSG_INVALID (sb_msg_invalid ++ [Z_to_bv 8 0]).
Proof.
intros m MI.
pose proof (ro_cells_image bsegs m SB_MSG_INVALID (sb_msg_invalid ++ [Z_to_bv 8 0]) MI ltac:(vm_compute; reflexivity) ltac:(unfold SB_MSG_INVALID; lia)
ltac:(vm_compute; intros X; discriminate X)) as [_ B].
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma sb_msg_invalid_nonul : ~ In (Z_to_bv 8 0) sb_msg_invalid.
Proof. rewrite <- In0_map_unsigned. vm_compute. intuition discriminate. Qed.
Lemma sb_msg_invalid_unsigned : map bv_unsigned sb_msg_invalid = MSG_INVALID_MODE.
Proof. vm_compute. reflexivity. Qed.
Lemma sb_fpl_notify_bytes : forall str, fpl_msg FLnotify str 0 = notify_bytes (map bv_unsigned str).
Proof. intros str. reflexivity. Qed.

Definition bkeep (b b' : bits_st bptr) : Prop := sb_chars b' = sb_chars b /\ sb_owner b' = sb_owner b /\ sb_buf_size b' = sb_buf_size b.
Lemma bkeep_refl : forall b, bkeep b b. Proof. intros b. repeat split; reflexivity. Qed.
Lemma bkeep_trans : forall b1 b2 b3, bkeep b1 b2 -> bkeep b2 b3 -> bkeep b1 b3.
Proof. intros b1 b2 b3 (E1 & E2 & E3) (F1 & F2 & F3). unfold bkeep. rewrite F1, F2, F3. auto. Qed.
Lemma bkeep_ub : forall b n, bkeep b (ub b n).
Proof.
intros b n. unfold bkeep, ub, speex_bits_unpack_unsigned.
destruct ((sb_nbBits b <? bits_pos b + n) || negb (sb_overflow b =? 0)); cbn; [unfold set_overflow | unfold set_pos]; cbn; repeat split; reflexivity.
Qed.
Lemma bkeep_sbw : forall b, bkeep b (sbw_bits b).
Proof.
intros b. unfold sbw_bits, sbw_wb.
assert (P : bkeep b (snd (if 0 <? speex_bits_remaining b then speex_bits_peek b else (0, b)))).
{ destruct (0 <? speex_bits_remaining b); [| apply bkeep_refl]. unfold speex_bits_peek.
destruct ((sb_nbBits b <? bits_pos b + 1) || negb (sb_overflow b =? 0)); cbn; [unfold set_overflow; cbn; repeat split; reflexivity| apply bkeep_refl]. }
destruct (if 0 <? speex_bits_remaining b then speex_bits_peek b else (0, b)) as [wb b1]. cbn [snd] in P.
destruct (negb (wb =? 0)); [| exact P].
apply (bkeep_trans _ b1); [exact P|]. apply (bkeep_trans _ (ub b1 1)); apply bkeep_ub.
Qed.
Lemma bkeep_lsp : forall k b, bkeep b (lsp_bits k b).
Proof.
intros k b. destruct k; cbn [lsp_bits];
repeat (first [ apply bkeep_ub | eapply bkeep_trans; [| apply bkeep_ub] ]).
Qed.
Lemma bkeep_scb : forall n hs sh b, bkeep b (scb_bits n hs sh b).
Proof.
induction n as [|n IH]; intros hs sh b; cbn [scb_bits]; [apply bkeep_refl|].
eapply bkeep_trans; [| apply IH]. destruct (negb (hs =? 0)); [eapply bkeep_trans; [apply bkeep_ub| apply bkeep_ub] | apply bkeep_ub].
Qed.
Lemma bkeep_innov : forall k b, bkeep b (innov_bits k b).
Proof. intros [|p] b; cbn [innov_bits]; [apply bkeep_refl| apply bkeep_scb]. Qed.
Lemma bkeep_sbsub : forall sm b, bkeep b (sbsub_bits sm b).
Proof.
intros sm b. unfold sbsub_bits. destruct (sm_innovation_unquant sm) as [k|]; [| apply bkeep_ub].
eapply bkeep_trans; [apply bkeep_ub|]. eapply bkeep_trans; [apply bkeep_innov|].
destruct (negb (sm_double_codebook sm =? 0)); [apply bkeep_innov| apply bkeep_refl].
Qed.
Lemma bkeep_sbsubs : forall n sm b, bkeep b (sbsubs_bits n sm b).
Proof. induction n as [|n IH]; intros sm b; cbn [sbsubs_bits]; [apply bkeep_refl|]. eapply bkeep_trans; [apply bkeep_sbsub| apply IH]. Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma ctl_stack_le_dec : forall d : dec_state bptr, ctl_stack d <= dec_stack d.
Proof.
induction d as [st | s low IH]; cbn [ctl_stack dec_stack]; [unfold NBCTL_STACK, NBDEC_STACK; lia|].
unfold SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK. lia.
Qed.
Lemma ctl_stack_nonneg : forall d : dec_state bptr, 0 <= ctl_stack d.
Proof. induction d; cbn [ctl_stack]; unfold NBCTL_STACK; lia. Qed.

Lemma sbd_io_ssp_agree : forall (m m' : mem), io_ssp m -> drv_consts m' ->
(forall a : word, X00a.SSP_GUARD <= bv_unsigned a < X00a.SSP_GUARD + 8 -> m' a = m a) -> io_ssp m'.
Proof.
intros m m' (g & _ & G) DC AG. exists g. split; [exact (proj1 (proj2 DC))|].
apply (ro_cells_agree asegs m m' _ _ G). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AG. unfold X00a.SSP_GUARD in *. lia.
Qed.
Lemma sbd_ssp_static : forall x, X00a.SSP_GUARD <= x < X00a.SSP_GUARD + 8 -> client_static x.
Proof. intros x Hx. apply X000.client_static_intro. unfold X00a.SSP_GUARD in Hx. lia. Qed.

Lemma cells_size_sb_fshadow : cells_size sb_fshadow = 8%nat. Proof. reflexivity. Qed.

Lemma sbd_low1_facts : forall (s : sbd_state bptr) (low : dec_state bptr) OUTL STEREO (m : mem) S' LBL,
sb_inv s -> dec_nestedR (DecSB s low) -> DREP OUTL STEREO m S' (snd (speex_decoder_ctl low (CtlSetInnovationSave (0 + sbd_frame_size s)))) LBL ->
isave_ok (snd (speex_decoder_ctl low (CtlSetInnovationSave (0 + sbd_frame_size s)))) /\
dec_nestedR (snd (speex_decoder_ctl low (CtlSetInnovationSave (0 + sbd_frame_size s)))).
Proof.
intros s low OUTL STEREO m S' LBL INV NEST R.
destruct INV as (IMODE & IFS & _). cbn [dec_nestedR] in NEST. destruct NEST as (NM & NL).
destruct low as [st | s' low']; cbn [speex_decoder_ctl nb_decoder_ctl snd isave_ok dec_nestedR] in *.
- replace (nb_innov_save (set_nb_innov_save st (Some (0 + sbd_frame_size s)))) with (Some (0 + sbd_frame_size s)) by (destruct st; reflexivity).
split; [| exact I]. rewrite IFS. destruct IMODE as [E|E]; rewrite E in NM |- *; cbn in NM |- *; [lia| discriminate NM].
- cbn [decst_rep] in R. destruct R as (a' & j' & LBL' & _ & _ & _ & INV' & _). cbn [dec_mode] in NM.
destruct INV' as (IMODE' & IFS' & _).
replace (sbd_innov_save (set_sbd_innov_save s' (Some (0 + sbd_frame_size s)))) with (Some (0 + sbd_frame_size s)) by (destruct s'; reflexivity).
replace (sbd_frame_size (set_sbd_innov_save s' (Some (0 + sbd_frame_size s)))) with (sbd_frame_size s') in * by (destruct s'; reflexivity).
replace (sbd_mode (set_sbd_innov_save s' (Some (0 + sbd_frame_size s)))) with (sbd_mode s') in * by (destruct s'; reflexivity).
split; [| exact NL].
rewrite IFS, IFS'. destruct IMODE as [E|E]; rewrite E in NM |- *; cbn [sbm_nb_mode] in NM; cbn [sbm_frameSize];
destruct IMODE' as [E'|E']; rewrite E' in NM |- *; cbn [sbm_frameSize]; first [discriminate NM | reflexivity].
Qed.

Lemma ctl_keeps_res : forall (d : dec_state bptr) r,
dec_frames (snd (speex_decoder_ctl d r)) = dec_frames d /\ dec_credit (snd (speex_decoder_ctl d r)) = dec_credit d
/\ dec_stack (snd (speex_decoder_ctl d r)) = dec_stack d.
Proof.
induction d as [st | s0 low0 IH]; intros r.
- cbn [speex_decoder_ctl]. destruct (nb_decoder_ctl st r). cbn [snd dec_frames dec_credit dec_stack]. repeat split; reflexivity.
- destruct r; cbn [speex_decoder_ctl];
first [ cbn [snd dec_frames dec_credit dec_stack]; repeat split; reflexivity
| match goal with |- context [speex_decoder_ctl low0 ?r'] =>
pose proof (IH r') as (F1 & C1 & S1); pose proof (ctl_keeps_depth low0 r') as D1;
destruct (speex_decoder_ctl low0 r') as [vx lx] eqn:E; cbn [snd] in F1, C1, S1, D1 |- *;
cbn [dec_frames dec_credit dec_stack]; rewrite F1, C1, S1, D1; repeat split; reflexivity end ].
Qed.

Lemma sbd_rz_dec : forall (RT0 : rt_sig) (Σ0 : rts RT0) PMc ms (e0 e1 bl : list Z) (Q : config -> Prop) T0 c0,
ASTA RT0 Σ0 PMc (eq ms) c0 -> e1 = e0 ++ bl ->
(exists bs, e1 = e0 ++ bs /\ cpsE asegs (ASTA RT0 Σ0 PMc (eq ms)) (Spec.X1nu.evw 2 bs) Q) ->
(forall c', Q c' -> realizes asegs c' T0) -> realizes asegs c0 (t_emit (Spec.X1nu.evw 2 bl) T0).
Proof.
intros RT0 Σ0 PMc ms e0 e1 bl Q T0 c0 Hc E (bs & E' & CP) K.
assert (bs = bl) by (rewrite E in E'; apply app_inv_head in E'; congruence). subst bs. exact (CP T0 c0 Hc K).
Qed.

Lemma sbd_dtx_acc : forall (m : mem) f sf, rw_cells asegs m sf sb_fshadow -> sf = Z.shiftr f 3 + SHB -> f mod 64 = 0 -> 0 <= f -> acc asegs m (f + 32) 4.
Proof.
intros m0 f0 sf0 [[_ B] _] Esf F64 F0. unfold sb_fshadow in B. cbn [cells_bytes cbytes app] in B.
apply acc_ushadow; [clear - F64; Z.div_mod_to_equations; lia | lia | lia |].
change (ushadow 4) with [Z_to_bv 8 4].
replace (shad (f0 + 32)) with (sf0 + Z.of_nat 4).
- apply (bytes_at_nth1 asegs m0 sf0 _ 4%nat _ B). reflexivity.
- rewrite Esf, shad_shiftr. unfold shad. clear - F64. Z.div_mod_to_equations. lia.
Qed.

Lemma dec_res_depth : forall d d' : dec_state bptr, dec_depth d = dec_depth d' ->
dec_stack d = dec_stack d' /\ dec_frames d = dec_frames d' /\ dec_credit d = dec_credit d' /\ ctl_stack d = ctl_stack d'.
Proof.
induction d as [st | s0 low0 IH]; intros [st' | s0' low0'] E; cbn [dec_depth] in E.
- cbn [dec_stack dec_frames dec_credit ctl_stack]. repeat split; reflexivity.
- pose proof (dec_depth_pos low0'). lia.
- pose proof (dec_depth_pos low0). lia.
- injection E as E. destruct (IH low0' E) as (E1 & E2 & E3 & E4). cbn [dec_stack dec_frames dec_credit ctl_stack]. rewrite E1, E2, E3, E4, E. repeat split; reflexivity.
Qed.

Lemma ctl_keeps_mode_nest : forall (d : dec_state bptr) r,
dec_mode (snd (speex_decoder_ctl d r)) = dec_mode d /\ (dec_nestedR d -> dec_nestedR (snd (speex_decoder_ctl d r))).
Proof.
induction d as [st | s0 low0 IH]; intros r.
- cbn [speex_decoder_ctl]. destruct (nb_decoder_ctl st r). cbn [snd dec_mode dec_nestedR]. split; [reflexivity| intros _; exact I].
- destruct r; cbn [speex_decoder_ctl];
first [ cbn [snd dec_mode dec_nestedR]; split; [destruct s0; reflexivity | intros H; destruct s0; exact H]
| match goal with |- context [speex_decoder_ctl low0 ?r'] =>
pose proof (IH r') as (M1 & N1);
destruct (speex_decoder_ctl low0 r') as [vx lx] eqn:E; cbn [snd] in M1, N1 |- *;
cbn [dec_mode dec_nestedR]; split; [destruct s0; reflexivity| intros (H1 & H2); split; [rewrite M1; destruct s0; exact H1 | exact (N1 H2)]] end ].
Qed.

Lemma rz_emit_nil : forall c0 T0, realizes asegs c0 T0 -> realizes asegs c0 (t_emit [] T0).
Proof. intros c0 T0 R. eapply rz_conseq; [exact R|]. apply t_eq_sym. apply t_emit_nil_eq. eapply realizes_nonempty. exact R. Qed.

Definition sb_msg_invalid : list byte := map (fun z => Z_to_bv 8 z) MSG_INVALID_MODE.
Lemma sb_msg_invalid_at : forall m, mem_inv asegs m -> bytes_at asegs m SB_MSG_INVALID (sb_msg_invalid ++ [Z_to_bv 8 0]).
Proof.
intros m MI.
pose proof (ro_cells_image asegs m SB_MSG_INVALID (sb_msg_invalid ++ [Z_to_bv 8 0]) MI ltac:(vm_compute; reflexivity) ltac:(unfold SB_MSG_INVALID; lia)
ltac:(vm_compute; intros X; discriminate X)) as [_ B].
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma sb_msg_invalid_nonul : ~ In (Z_to_bv 8 0) sb_msg_invalid.
Proof. rewrite <- In0_map_unsigned. vm_compute. intuition discriminate. Qed.
Lemma sb_msg_invalid_unsigned : map bv_unsigned sb_msg_invalid = MSG_INVALID_MODE.
Proof. vm_compute. reflexivity. Qed.
Lemma sb_fpl_notify_bytes : forall str, fpl_msg FLnotify str 0 = notify_bytes (map bv_unsigned str).
Proof. intros str. reflexivity. Qed.

Definition bkeep (b b' : bits_st bptr) : Prop := sb_chars b' = sb_chars b /\ sb_owner b' = sb_owner b /\ sb_buf_size b' = sb_buf_size b.
Lemma bkeep_refl : forall b, bkeep b b. Proof. intros b. repeat split; reflexivity. Qed.
Lemma bkeep_trans : forall b1 b2 b3, bkeep b1 b2 -> bkeep b2 b3 -> bkeep b1 b3.
Proof. intros b1 b2 b3 (E1 & E2 & E3) (F1 & F2 & F3). unfold bkeep. rewrite F1, F2, F3. auto. Qed.
Lemma bkeep_ub : forall b n, bkeep b (ub b n).
Proof.
intros b n. unfold bkeep, ub, speex_bits_unpack_unsigned.
destruct ((sb_nbBits b <? bits_pos b + n) || negb (sb_overflow b =? 0)); cbn; [unfold set_overflow | unfold set_pos]; cbn; repeat split; reflexivity.
Qed.
Lemma bkeep_sbw : forall b, bkeep b (sbw_bits b).
Proof.
intros b. unfold sbw_bits, sbw_wb.
assert (P : bkeep b (snd (if 0 <? speex_bits_remaining b then speex_bits_peek b else (0, b)))).
{ destruct (0 <? speex_bits_remaining b); [| apply bkeep_refl]. unfold speex_bits_peek.
destruct ((sb_nbBits b <? bits_pos b + 1) || negb (sb_overflow b =? 0)); cbn; [unfold set_overflow; cbn; repeat split; reflexivity| apply bkeep_refl]. }
destruct (if 0 <? speex_bits_remaining b then speex_bits_peek b else (0, b)) as [wb b1]. cbn [snd] in P.
destruct (negb (wb =? 0)); [| exact P].
apply (bkeep_trans _ b1); [exact P|]. apply (bkeep_trans _ (ub b1 1)); apply bkeep_ub.
Qed.
Lemma bkeep_lsp : forall k b, bkeep b (lsp_bits k b).
Proof.
intros k b. destruct k; cbn [lsp_bits];
repeat (first [ apply bkeep_ub | eapply bkeep_trans; [| apply bkeep_ub] ]).
Qed.
Lemma bkeep_scb : forall n hs sh b, bkeep b (scb_bits n hs sh b).
Proof.
induction n as [|n IH]; intros hs sh b; cbn [scb_bits]; [apply bkeep_refl|].
eapply bkeep_trans; [| apply IH]. destruct (negb (hs =? 0)); [eapply bkeep_trans; [apply bkeep_ub| apply bkeep_ub] | apply bkeep_ub].
Qed.
Lemma bkeep_innov : forall k b, bkeep b (innov_bits k b).
Proof. intros [|p] b; cbn [innov_bits]; [apply bkeep_refl| apply bkeep_scb]. Qed.
Lemma bkeep_sbsub : forall sm b, bkeep b (sbsub_bits sm b).
Proof.
intros sm b. unfold sbsub_bits. destruct (sm_innovation_unquant sm) as [k|]; [| apply bkeep_ub].
eapply bkeep_trans; [apply bkeep_ub|]. eapply bkeep_trans; [apply bkeep_innov|].
destruct (negb (sm_double_codebook sm =? 0)); [apply bkeep_innov| apply bkeep_refl].
Qed.
Lemma bkeep_sbsubs : forall n sm b, bkeep b (sbsubs_bits n sm b).
Proof. induction n as [|n IH]; intros sm b; cbn [sbsubs_bits]; [apply bkeep_refl|]. eapply bkeep_trans; [apply bkeep_sbsub| apply IH]. Qed.
