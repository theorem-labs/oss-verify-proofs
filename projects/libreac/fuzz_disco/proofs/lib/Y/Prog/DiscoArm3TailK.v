(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_set_resweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxSetResweep.v, with its module paths, module names and numbers changed; 174 of its 248 lines of code are new or changed and 208 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacHuntHeardAnything.v, with its module names changed; 609 of its 645 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntSeat.v, with its module paths and module names changed; 60 of its 184 lines of code are new or changed and 521 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC1h YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoArm3 DiscoArm3TailDefs.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma a3t_dsh_check :
  forallb (fun k => Z.eqb (dsh_loop (Z.of_nat k)) (if a3t_shf (Z.of_nat k) then 0xf8 else dsh_ser2 (Z.of_nat k)))
    (seq 0 384) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma a3t_dsh : forall k, 0 <= k < 384 -> dsh_loop k = if a3t_shf k then 0xf8 else dsh_ser2 k.
Proof.
  intros k Hk. pose proof a3t_dsh_check as H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat k) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  apply Z.eqb_eq in H. exact H.
Qed.

Lemma a3t_ev : forall i, EV_HEAD i + 1 + 1 = EV_HEAD (i + 1).
Proof. intros i. unfold EV_HEAD, EV_PRO, EV_ITER. lia. Qed.
Lemma a3t_frm0 : forall c c' : bv 32, lib.Lib.FP.frm0 c ->
  c' = c \/ Z.land (Z.shiftr (bv_unsigned c') 5) 7 = 0 -> lib.Lib.FP.frm0 c'.
Proof. intros c c' H [E|E]; [rewrite E; exact H | exact E]. Qed.

Lemma byte_of_word_lit : forall v i, byte_of_word (Z_to_bv 64 v) i = Z_to_bv 8 (Z.shiftr (v mod 2 ^ 64) (8 * i)).
Proof. intros v i. unfold byte_of_word. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma Z_to_bv_mod8 : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H. Qed.
Lemma dsh_chunks_ok : forall segs E m base shf,
  (forall k, 0 <= k < DFRAME_SH -> 0 <= shf k < 256 /\ mbyte segs m (base + k) = Some (Z_to_bv 8 (shf k))) ->
  Forall (YP09.chunk_ok segs E m base) (dsh_chunks shf).
Proof.
  intros segs E m base shf H. unfold dsh_chunks. apply Forall_forall. intros c Hc.
  apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
  assert (Hk : 0 <= Z.of_nat j < DFRAME_SH) by (unfold DFRAME_SH in *; lia).
  destruct (H _ Hk) as (Hr & Hm).
  intros i Hi. unfold YP09.c_len, cv_len in Hi. cbn [YP09.c_val Z.of_N] in Hi.
  assert (i = 0) by lia. subst i.
  exists (Z_to_bv 8 (shf (Z.of_nat j))). cbn [YP09.c_off YP09.c_val cbyte sv_denot]. split.
  - f_equal. rewrite byte_of_word_lit. apply Z_to_bv_mod8.
    rewrite Z.mul_0_r, Z.shiftr_0_r, (Z.mod_small (shf (Z.of_nat j)) (2 ^ 64)) by lia. reflexivity.
  - rewrite Z.add_0_r. exact Hm.
Qed.
Lemma aview_range : forall segs H m a b, aview segs H m a = Some b -> 0 <= b < 256.
Proof.
  intros segs H m a b Hv. unfold aview in Hv. destruct (mbyte segs (mrestrict H m) a) as [x|]; [|discriminate Hv].
  cbn [option_map] in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range _ x) as Hr.
  change (bv_modulus 8) with 256 in Hr. exact Hr.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma d_env_old : forall cx E vals n, (n < AT_FL)%nat -> ew (d_env cx E vals) n = ew E n.
Proof. intros cx E vals n Hn. unfold d_env. apply ew_havoc_old. exact Hn. Qed.
Lemma d_env_fl : forall cx E vals,
  ew (d_env cx E vals) AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).
Proof.
  intros cx E vals. unfold d_env. replace AT_FL with (AT_FL + 0)%nat at 2 by lia.
  rewrite (ew_havoc_new _ AT_FL _ 0 (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.
Lemma d_env_x : forall cx E vals j, (j < length vals)%nat ->
  ew (d_env cx E vals) (AT_X + j) = nth j vals (Z_to_bv 64 0).
Proof.
  intros cx E vals j Hj. unfold d_env. replace (AT_X + j)%nat with (AT_FL + S j)%nat by (unfold AT_X, AT_FL; lia).
  rewrite (ew_havoc_new _ AT_FL _ (S j) (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.
Lemma d_env_agree : forall cx E vals, env_agree AT_FL E (d_env cx E vals).
Proof. intros cx E vals. split; [intros n Hn; apply d_env_old; exact Hn | reflexivity]. Qed.
Lemma d_E_env : forall cx E vals, d_E cx E -> d_E cx (d_env cx E vals).
Proof.
  intros cx E vals (EE & E32 & HEI & E60 & EF & ESH). unfold d_E.
  rewrite !d_env_old by (unfold AT_FL, AT_A, AT_F, AT_SH; lia).
  split; [|split; [exact E32 | split; [|split; [exact E60 | split; [exact EF | exact ESH]]]]].
  - intros n r Hn. rewrite d_env_old; [exact (EE n r Hn)|].
    pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr. unfold AT_FL. lia.
  - unfold d_env. apply img_env_havoc_hi; [exact HEI | unfold A_LIM, AT_FL; lia].
Qed.

Definition d_hslots (cx : dcx) (h : Z) (W : world SEGS) (mem : word -> option byte) : Prop :=
  val_mem SEGS (rd W mem) (d_A cx + 184) 8 h /\ val_mem SEGS (rd W mem) (d_A cx + 120) 8 (h + 440) /\
  val_mem SEGS (rd W mem) (d_A cx + 136) 8 0 /\
  val_mem SEGS (rd W mem) (d_A cx + 376) 8 (dnot (d_obj cx OG)) /\
  val_mem SEGS (rd W mem) (d_A cx + 280) 8 (dnot (d_obj cx OT)) /\
  val_mem SEGS (rd W mem) (d_A cx + 232) 8 (dnot (d_obj cx OO)) /\
  val_mem SEGS (rd W mem) (d_A cx + 264) 8 (dnot (d_obj cx OUSED)).

Lemma d_hslots_of_frame : forall cx h shf (W : world SEGS) mem,
  d_frame cx h shf W mem -> d_hslots cx h W mem.
Proof.
  intros cx h shf W mem (E & _ & _ & _ & H184 & H120 & H136 & H376 & H280 & H232 & H264).
  repeat split; assumption.
Qed.

Lemma d_hslots_kept : forall cx h (W W' : world SEGS) mem mem',
  (forall a, d_A cx + 120 <= a < d_A cx + 384 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  d_hslots cx h W mem -> d_hslots cx h W' mem'.
Proof.
  intros cx h W W' mem mem' KA (H184 & H120 & H136 & H376 & H280 & H232 & H264).
  repeat split; (eapply (val_mem_kept SEGS (w_H W) (w_H W') mem mem'); [|eassumption]);
    intros kk Hkk; change (Z.of_nat 8) with 8 in Hkk; apply KA; lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Lemma d_land_hs : d_land_stmt B MT XM_LIB RLO RHI tfib_K ->
  AR_laws SEGS B -> frame_flag_lawP SEGS B ->
  forall (fq : YK11.FPState) (cx : dcx) (h : Z) (shf : Z -> Z) ly3 S3 (W3 : world SEGS) md3 k
    (E : env) (ss : sstate) (ms : machine_state),
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 (ms_mem ms) md3 k ->
  d_E cx E -> ew E AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W3) ms) ->
  d_land_chk shf (ss_mem ss) = true ->
  d_hslots cx h W3 (ms_mem ms) ->
  d_frame cx h shf W3 (ms_mem ms) /\ d_shadow cx shf W3 (ms_mem ms).
Proof.
  intros DLAND LAWS FFL fq cx h shf ly3 S3 W3 md3 k E ss ms HC HE HFL HS HCHK
    (H184 & H120 & H136 & H376 & H280 & H232 & H264).
  exact (DLAND LAWS FFL fq cx h shf ly3 S3 W3 md3 k E ss ms HC HE HFL HS HCHK
    H184 H120 H136 H376 H280 H232 H264).
Qed.

Lemma d_geom : AR_laws SEGS B -> forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_S cx mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= d_S cx /\ d_S cx <= 2 ^ 47 /\
  4096 <= d_FB cx /\ d_FB cx + 4096 <= alloc_ceiling /\ in_app (d_FB cx) 4096 /\
  off_img (d_FB cx) 4096 /\ d_FB cx mod 32 = 0 /\
  (forall a, d_FB cx <= a < d_FB cx + 4096 -> apresent (w_H W3) mem3 a) /\
  (forall i, 0 <= i < 512 -> apresent (w_H W3) mem3 (shadow_addr (d_FB cx) + i)) /\
  (forall a, d_S cx - LLVMF_STK <= a < d_S cx -> apresent (w_H W3) mem3 a) /\
  AR SEGS B ly3 S3 W3 mem3 md3 /\ In (DFRAME_CLASS, c_fpos cx) (frames S3) /\
  frame_addr ly3 DFRAME_CLASS (c_fpos cx) = d_FB cx /\
  flag_addr ly3 DFRAME_CLASS (c_fpos cx) = flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx).
Proof.
  intros LAWS cx ly3 S3 W3 mem3 md3 k (HB & HJ & HFR).
  destruct HB as ((HPRE & _) & _).
  pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  assert (Hfin : In (DFRAME_CLASS, c_fpos cx) (frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & Efa & _).
  assert (Efl : flag_addr ly3 DFRAME_CLASS (c_fpos cx) = flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).
  { pose proof (Efa 0 0) as E00. unfold frame_addr in E00. unfold flag_addr. lia. }
  destruct (frames_bounds _ _ LAWS _ _ _ _ _ DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as (HF0 & HFc & HFia).
  pose proof (frm_off_imgP B ly3 S3 W3 mem3 md3 DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as HFo.
  destruct (al_frames _ _ LAWS _ _ _ _ _ DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as (Hal & _ & HFpres & HSpres).
  rewrite Efa in HF0, HFc, HFia, HFo, Hal, HFpres, HSpres.
  change (frame_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) with (d_FB cx) in *.
  change (fs_frame_bytes DFRAME_CLASS) with 4096 in *. change (4096 / 8) with 512 in HSpres.
  change (spZ (c_regs cx)) with (d_S cx) in *.
  split; [exact Hal16|]. split; [unfold LLVMF_STK in *; lia|]. split; [lia|].
  split; [exact HF0|]. split; [exact HFc|]. split; [exact HFia|]. split; [exact HFo|]. split; [exact Hal|].
  split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
  split; [intros i Hi; exact (proj1 (HSpres i Hi))|].
  split; [intros a Ha; apply HJpres; exact Ha|].
  split; [exact HAR3|]. split; [exact Hfin|]. split; [rewrite Efa; reflexivity|]. exact Efl.
Qed.
Lemma d_A_range : forall cx, 0 <= d_S cx - MFRAME ->
  d_S cx - MFRAME - 31 <= d_A cx <= d_S cx - MFRAME /\ d_A cx mod 32 = 0.
Proof.
  intros cx Hs. unfold d_A. pose proof (Z.div_mod (d_S cx - MFRAME) 32 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (d_S cx - MFRAME) 32 ltac:(lia)) as Hmp.
  split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

End h.
End f.
End d.
