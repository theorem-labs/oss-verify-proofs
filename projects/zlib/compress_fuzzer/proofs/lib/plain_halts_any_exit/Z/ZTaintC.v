(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateInitLib RefDeflateRel RefDeflSafeI1 RefDeflSafeI5b RefDeflSafeI6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintRel DeflateTaintCall DeflateTaintCore DeflateTaintInit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState Inflate HarnessSmall ZApiInst ZTaint HarnessCompress ZApiInstC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflPat2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition dinitC_of (g : N -> Z -> Z) (level : Z) : deflate_state :=
  dFg 0%N 1%N 2%N 3%N 4%N (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N) dinit_cs 1 15 8 level 0 8.

Definition dinitC_zr (level : Z) : ZRet := zret_of_cs (ds_strm (dinitC_of (fun _ => g0) level)) Z_OK.

Lemma di_level_C : forall level, 0 <= level <= 9 -> di_level level = level.
Proof. intros level Hl. unfold di_level, Z_DEFAULT_COMPRESSION. destruct (Z.eqb_spec level (-1)); [lia| reflexivity]. Qed.

Lemma di_bad_C : forall level, 0 <= level <= 9 -> di_bad level Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY = false.
Proof.
  intros level Hl. unfold di_bad, di_chk. rewrite (di_level_C level Hl).
  unfold di_wb, di_wrap, MAX_WBITS, DEF_MEM_LEVEL, MAX_MEM_LEVEL, Z_DEFLATED, Z_DEFAULT_STRATEGY, Z_FIXED.
  cbn [Z.ltb Z.leb Z.eqb Z.compare Pos.compare Pos.compare_cont negb andb orb Z.opp Z.sub].
  replace (level <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (9 <? level) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma dinitC_strm : forall g level, ds_strm (dinitC_of g level) = ds_strm (dinitC_of (fun _ => g0) level).
Proof. intros g level. unfold dinitC_of. rewrite !dFg_strm. reflexivity. Qed.

Lemma dinitC_run_safe : forall g level, 0 <= level <= 9 ->
  DeflateSafe.dpure (deflateInit2_m DeflateSafe.dhooks (zc_none zstrm0) level Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY) (dchs g)
  = Some (Some (dinitC_of g level), dinitC_zr level).
Proof.
  intros g level Hl.
  rewrite (RefDeflSafeI5b.dinit_run (zc_none zstrm0) level Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY (dchs g) (di_bad_C level Hl)).
  unfold dchs. cbn [ohd otl].
  pose proof (S5og_proj 0%N (g 0%N) (cs_init (zc_none zstrm0)) (di_wrap MAX_WBITS) (di_wb9 MAX_WBITS) DEF_MEM_LEVEL
                (Some (1%N, g 1%N)) (Some (2%N, g 2%N)) (Some (3%N, g 3%N)) (Some (4%N, g 4%N))) as PJ.
  cbv zeta in PJ. destruct PJ as (Ew & Ep & Eh & Eb).
  unfold dinit_body, all_some. rewrite Ew, Ep, Eh, Eb. cbn [option_map fst].
  change (S5og 0%N (g 0%N) (cs_init (zc_none zstrm0)) (di_wrap MAX_WBITS) (di_wb9 MAX_WBITS) DEF_MEM_LEVEL
               (Some (1%N, g 1%N)) (Some (2%N, g 2%N)) (Some (3%N, g 3%N)) (Some (4%N, g 4%N)))
    with (S5g 0%N 1%N 2%N 3%N 4%N (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N) (cs_init (zc_none zstrm0)) (di_wrap MAX_WBITS) (di_wb9 MAX_WBITS) DEF_MEM_LEVEL).
  rewrite (reset_S5g 0%N 1%N 2%N 3%N 4%N (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N) (cs_init (zc_none zstrm0)) (di_wrap MAX_WBITS) (di_wb9 MAX_WBITS)
             DEF_MEM_LEVEL (di_level level) Z_DEFAULT_STRATEGY Z_DEFLATED (proj1 (di_wrap_range MAX_WBITS))).
  rewrite (di_level_C level Hl). unfold dinitC_zr. rewrite <- (dinitC_strm g level). reflexivity.
Qed.

Theorem dinitC_run_of : forall g level, 0 <= level <= 9 ->
  HarnessCompress.dinitC_run level (dchs g) zstrm0 = Some (Some (dinitC_of g level), dinitC_zr level).
Proof. intros g level Hl. unfold HarnessCompress.dinitC_run. rewrite hs_dpure_eq, hs_dhooks_eq. exact (dinitC_run_safe g level Hl). Qed.

Theorem dsC_of : forall level, 0 <= level <= 9 -> dsC level = dinitC_of (fun _ => g0) level.
Proof. intros level Hl. unfold dsC, dinitC. rewrite (dinitC_run_of _ _ Hl). reflexivity. Qed.

Theorem dzC_of : forall level, 0 <= level <= 9 -> dzC level = zr_strm (dinitC_zr level).
Proof. intros level Hl. unfold dzC, dinitC. rewrite (dinitC_run_of _ _ Hl). reflexivity. Qed.

Definition cfg_table (level : Z) : Z * Z * Z * Z :=
  match level with
  | 0 => (0, 0, 0, 0) | 1 => (4, 4, 8, 4) | 2 => (4, 5, 16, 8) | 3 => (4, 6, 32, 32) | 4 => (4, 4, 16, 16)
  | 5 => (8, 16, 32, 32) | 6 => (8, 16, 128, 128) | 7 => (8, 32, 128, 256) | 8 => (32, 128, 258, 1024) | _ => (32, 258, 258, 4096)
  end.

Lemma dinitC_fields : forall g level, 0 <= level <= 9 ->
  let s := dinitC_of g level in
  ds_status s = INIT_STATE /\ ds_wrap s = 1 /\ ds_level s = level /\ ds_strategy s = 0 /\ ds_method s = 8
  /\ ds_w_bits s = 15 /\ ds_w_size s = 32768 /\ ds_w_mask s = 32767 /\ ds_window_size s = 65536
  /\ ds_hash_bits s = 15 /\ ds_hash_size s = 32768 /\ ds_hash_mask s = 32767 /\ ds_hash_shift s = 5
  /\ ds_lit_bufsize s = 16384 /\ ds_pending_buf_size s = 65536 /\ ds_sym_end s = 49149
  /\ ds_pending s = 0 /\ ds_pending_out s = 0 /\ ds_last_flush s = -2 /\ ds_gzhead s = 0
  /\ ds_strstart s = 0 /\ ds_block_start s = 0 /\ ds_lookahead s = 0 /\ ds_insert s = 0
  /\ ds_match_length s = 2 /\ ds_prev_length s = 2 /\ ds_match_available s = 0 /\ ds_ins_h s = 0
  /\ (ds_good_match s, ds_max_lazy_match s, ds_nice_match s, ds_max_chain_length s) = cfg_table level
  /\ cs_total_in (ds_strm s) = 0 /\ cs_total_out (ds_strm s) = 0 /\ cs_adler (ds_strm s) = 1.
Proof.
  intros g level Hl.
  assert (C : level = 0 \/ level = 1 \/ level = 2 \/ level = 3 \/ level = 4 \/ level = 5 \/ level = 6 \/ level = 7 \/ level = 8 \/ level = 9) by lia.
  destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; (repeat split; reflexivity).
Qed.

Lemma dinitC_dmode : forall g level, 0 <= level <= 9 ->
  dmode (dinitC_of g level) = (if level =? 0 then 0 else if level <=? 3 then 3 else 4).
Proof.
  intros g level Hl. pose proof (dinitC_fields g level Hl) as F. cbv zeta in F. destruct F as (_ & _ & EL & ES & _).
  unfold dmode. rewrite EL, ES. reflexivity.
Qed.

Theorem PATG2_dinitC : forall g level, 0 <= level <= 9 -> PATG2 (dinitC_of g level).
Proof.
  intros g level Hl. pose proof (dinitC_fields g level Hl) as F. cbv zeta in F. destruct F as (EST & EW & EL & ES & _).
  constructor.
  - rewrite (dinitC_dmode g level Hl). destruct (level =? 0); [left; reflexivity|]. destruct (level <=? 3); [right; left | right; right]; reflexivity.
  - left. exact ES.
  - left. exact EW.
  - left. exact EST.
Qed.

Lemma DCALL_initC : forall g g' level, 0 <= level <= 9 -> DCALL (dinitC_of g level) (dinitC_of g' level).
Proof.
  intros g g' level Hlv. destruct dinit_cs_ok as [Hai Hao].
  split; [exact (dFg_DQ 0%N 1%N 2%N 3%N 4%N dinit_cs level (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N) (g' 0%N) (g' 1%N) (g' 2%N) (g' 3%N) (g' 4%N))|].
  split; [exact (dFg_INV 0%N 1%N 2%N 3%N 4%N dinit_cs level Hlv Hai Hao (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N))|].
  split; [exact (dFg_INV 0%N 1%N 2%N 3%N 4%N dinit_cs level Hlv Hai Hao (g' 0%N) (g' 1%N) (g' 2%N) (g' 3%N) (g' 4%N))|].
  split.
  - pose proof (dFg_dreach (zc_none zstrm0) level Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY 0%N 1%N 2%N 3%N 4%N
             (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N) (di_bad_C level Hlv) ltac:(unfold DEF_MEM_LEVEL; lia)) as R.
    rewrite (di_level_C level Hlv) in R. exact R.
  - pose proof (dFg_dreach (zc_none zstrm0) level Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY 0%N 1%N 2%N 3%N 4%N
             (g' 0%N) (g' 1%N) (g' 2%N) (g' 3%N) (g' 4%N) (di_bad_C level Hlv) ltac:(unfold DEF_MEM_LEVEL; lia)) as R.
    rewrite (di_level_C level Hlv) in R. exact R.
Qed.

Theorem DREL_initC : forall g level, 0 <= level <= 9 -> DREL (dinitC_of g level) (zdc_init level).
Proof. intros g level Hl. unfold DREL, zdc_init. cbn [dz_s]. rewrite (dsC_of level Hl). apply DCALL_initC. exact Hl. Qed.

Theorem DREL_zdc : forall s_a inp x aout flush, DREL s_a x -> dcall_wf (mkZCall inp aout (dz_z x)) -> flush = Z_NO_FLUSH \/ flush = Z_FINISH ->
  let r_a := deflate_m s_a (mkZCall inp aout (dz_z x)) flush in
  let '(x', consumed, bs, rc) := zdc_deflate inp x aout flush in
  DREL (fst r_a) x' /\ zr_strm (snd r_a) = dz_z x'
  /\ consumed = zr_consumed (snd r_a) /\ bs = zr_output (snd r_a) /\ rc = zr_rc (snd r_a).
Proof.
  intros s_a inp x aout flush R Hz Hf. cbv zeta.
  destruct (DREL_step s_a x (mkZCall inp aout (dz_z x)) flush R Hz Hf) as [E R'].
  unfold zdc_deflate. rewrite E.
  destruct (deflate_m (dz_s x) (mkZCall inp aout (dz_z x)) flush) as [s' zr]. cbn [fst snd] in *.
  split; [exact R'|]. repeat split; reflexivity.
Qed.

Theorem DREL_dend_rc : forall s_a x, DREL s_a x -> dend_rc s_a = dend_rc (dz_s x).
Proof.
  intros s_a x R. destruct (DREL_facts s_a x R) as (_ & _ & _ & EC).
  unfold dend_rc. rewrite <- (clean_eq_fieldT deflateStateCheck _ _ EC ltac:(intros; reflexivity)),
    <- (clean_eq_fieldT ds_status _ _ EC ltac:(reflexivity)). reflexivity.
Qed.

