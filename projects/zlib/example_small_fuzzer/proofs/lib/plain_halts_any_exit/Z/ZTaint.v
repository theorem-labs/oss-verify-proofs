(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZProg ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflateInitLib RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeI6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflateInitLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflSafeI5b OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateTaintRel DeflateTaintCall DeflateTaintCore.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateTaintCore.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateTaintRel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateTaintCall OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateTaintCore OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateTaintCore.DeflateTaintInit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState Inflate HarnessSmall ZApiInst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition dinit_cs : cstrm := cs_init (zc_none zstrm0).

Definition dinit_of (g : N -> Z -> Z) : deflate_state :=
  dFg 0%N 1%N 2%N 3%N 4%N (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N) dinit_cs 1 15 8 6 0 8.

Definition dinit_zr : ZRet := zret_of_cs (ds_strm (dinit_of (fun _ => g0))) Z_OK.

Lemma di_bad_default : di_bad Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY = false.
Proof. reflexivity. Qed.

Lemma dinit_strm : forall g, ds_strm (dinit_of g) = ds_strm (dinit_of (fun _ => g0)).
Proof. intros g. unfold dinit_of. rewrite !dFg_strm. reflexivity. Qed.

Lemma dinit_run_safe : forall g,
  DeflateSafe.dpure (deflateInit2_m DeflateSafe.dhooks (zc_none zstrm0) Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY) (dchs g)
  = Some (Some (dinit_of g), dinit_zr).
Proof.
  intros g.
  rewrite (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflSafeI5b.dinit_run (zc_none zstrm0) Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY (dchs g) di_bad_default).
  unfold dchs. cbn [ohd otl].
  pose proof (S5og_proj 0%N (g 0%N) (cs_init (zc_none zstrm0)) (di_wrap MAX_WBITS) (di_wb9 MAX_WBITS) DEF_MEM_LEVEL
                (Some (1%N, g 1%N)) (Some (2%N, g 2%N)) (Some (3%N, g 3%N)) (Some (4%N, g 4%N))) as PJ.
  cbv zeta in PJ. destruct PJ as (Ew & Ep & Eh & Eb).
  unfold dinit_body, all_some. rewrite Ew, Ep, Eh, Eb. cbn [option_map fst].
  change (S5og 0%N (g 0%N) (cs_init (zc_none zstrm0)) (di_wrap MAX_WBITS) (di_wb9 MAX_WBITS) DEF_MEM_LEVEL
               (Some (1%N, g 1%N)) (Some (2%N, g 2%N)) (Some (3%N, g 3%N)) (Some (4%N, g 4%N)))
    with (S5g 0%N 1%N 2%N 3%N 4%N (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N) (cs_init (zc_none zstrm0)) (di_wrap MAX_WBITS) (di_wb9 MAX_WBITS) DEF_MEM_LEVEL).
  rewrite (reset_S5g 0%N 1%N 2%N 3%N 4%N (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N) (cs_init (zc_none zstrm0)) (di_wrap MAX_WBITS) (di_wb9 MAX_WBITS)
             DEF_MEM_LEVEL (di_level Z_DEFAULT_COMPRESSION) Z_DEFAULT_STRATEGY Z_DEFLATED (proj1 (di_wrap_range MAX_WBITS))).
  unfold dinit_zr. rewrite <- (dinit_strm g). reflexivity.
Qed.

Lemma hs_dpure_eq : @HarnessSmall.dpure = @DeflateSafe.dpure. Proof. reflexivity. Qed.
Lemma hs_dhooks_eq : HarnessSmall.dhooks = DeflateSafe.dhooks. Proof. reflexivity. Qed.

Theorem dinit_run_of : forall g, HarnessSmall.dinit_run (dchs g) zstrm0 = Some (Some (dinit_of g), dinit_zr).
Proof. intros g. unfold HarnessSmall.dinit_run. rewrite hs_dpure_eq, hs_dhooks_eq. exact (dinit_run_safe g). Qed.

Theorem ds0_of : ds0 = dinit_of (fun _ => g0).
Proof. unfold ds0, dinit0. rewrite dinit_run_of. reflexivity. Qed.

Theorem dz0_of : dz0 = zr_strm dinit_zr.
Proof. unfold dz0, dinit0. rewrite dinit_run_of. reflexivity. Qed.


Definition DREL (s_a : deflate_state) (x : dstream) : Prop := DCALL s_a (dz_s x).

Lemma dinit_cs_ok : 0 <= cs_avail_in dinit_cs /\ 0 <= cs_avail_out dinit_cs.
Proof. split; vm_compute; discriminate. Qed.

Lemma DCALL_init : forall g g', DCALL (dinit_of g) (dinit_of g').
Proof.
  intros g g'. destruct dinit_cs_ok as [Hai Hao].
  assert (Hlv : 0 <= 6 <= 9) by lia.
  split; [exact (dFg_DQ 0%N 1%N 2%N 3%N 4%N dinit_cs 6 (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N) (g' 0%N) (g' 1%N) (g' 2%N) (g' 3%N) (g' 4%N))|].
  split; [exact (dFg_INV 0%N 1%N 2%N 3%N 4%N dinit_cs 6 Hlv Hai Hao (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N))|].
  split; [exact (dFg_INV 0%N 1%N 2%N 3%N 4%N dinit_cs 6 Hlv Hai Hao (g' 0%N) (g' 1%N) (g' 2%N) (g' 3%N) (g' 4%N))|].
  split.
  - exact (dFg_dreach (zc_none zstrm0) Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY 0%N 1%N 2%N 3%N 4%N
             (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N) di_bad_default ltac:(unfold DEF_MEM_LEVEL; lia)).
  - exact (dFg_dreach (zc_none zstrm0) Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY 0%N 1%N 2%N 3%N 4%N
             (g' 0%N) (g' 1%N) (g' 2%N) (g' 3%N) (g' 4%N) di_bad_default ltac:(unfold DEF_MEM_LEVEL; lia)).
Qed.

Theorem DREL_init : forall g, DREL (dinit_of g) zd_init.
Proof. intros g. unfold DREL, zd_init. cbn [dz_s]. rewrite ds0_of. apply DCALL_init. Qed.

Theorem DREL_step : forall s_a x zc flush, DREL s_a x -> dcall_wf zc -> flush = Z_NO_FLUSH \/ flush = Z_FINISH ->
  snd (deflate_m s_a zc flush) = snd (deflate_m (dz_s x) zc flush)
  /\ DREL (fst (deflate_m s_a zc flush)) (mkDZ (fst (deflate_m (dz_s x) zc flush)) (zr_strm (snd (deflate_m (dz_s x) zc flush)))).
Proof. intros s_a x zc flush R Hz Hf. exact (deflate_m_rel s_a (dz_s x) zc flush R Hz Hf). Qed.

Theorem DREL_zd : forall s_a d x ain aout flush, DREL s_a x -> dcall_wf (zd_zcall d x ain aout) -> flush = Z_NO_FLUSH \/ flush = Z_FINISH ->
  let r_a := deflate_m s_a (zd_zcall d x ain aout) flush in
  let '(x', ain', aout', bs, rc) := zd_deflate d x ain aout flush in
  DREL (fst r_a) x' /\ zr_strm (snd r_a) = dz_z x'
  /\ ain' = zlength (zc_input (zd_zcall d x ain aout)) - zr_consumed (snd r_a)
  /\ aout' = aout - zlength (zr_output (snd r_a)) /\ bs = zr_output (snd r_a) /\ rc = zr_rc (snd r_a).
Proof.
  intros s_a d x ain aout flush R Hz Hf. cbv zeta.
  destruct (DREL_step s_a x (zd_zcall d x ain aout) flush R Hz Hf) as [E R'].
  unfold zd_deflate. cbv zeta. rewrite E.
  destruct (deflate_m (dz_s x) (zd_zcall d x ain aout) flush) as [s' zr]. cbn [fst snd] in *.
  split; [exact R'|]. repeat split; reflexivity.
Qed.

Theorem DREL_facts : forall s_a x, DREL s_a x -> dreach s_a /\ DD s_a /\ INV s_a /\ clean s_a = clean (dz_s x).
Proof.
  intros s_a x (Q & I1 & _ & R1 & _). split; [exact R1|]. split; [exact (dreach_DD _ R1)|]. split; [exact I1 | exact (DQ_clean _ _ Q)].
Qed.
