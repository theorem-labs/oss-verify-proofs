(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.

Module Z_tr_cb1.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel CompressModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.CompressModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition cbR (L : dlay) (LT DT sx : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp (wz 65535) (wz Z_LENGTH_CODE) (wz 4) s0 s1 (wz (dl_As L)) (wz LT) (wz DT) (wz (dl_As L + 5888)) (wz sx)
      (wz 16) (wz (-20)) (wz 257) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition cb_site_post (EXIT : Z) (L : dlay) (s : deflate_state) (LT DT sx : Z) (PB : arr) (PD BB BV : Z)
    (ra sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s3 s4 s5 t4 t5 t6 wbb m',
    ms' = MS (cbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz BV) t4 t5 t6) F (wz EXIT) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16.

Lemma cb_S1 : forall (L : dlay) (s : deflate_state) (lfc ldl : arr) (LT DT sx lc : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m LT lfc ldl 286 -> 0 <= lc < 286 -> 0 < LT -> LT + 4 * 286 < 2^63 ->
  0 <= arr_get lfc lc < 65536 -> 0 <= arr_get ldl lc <= 16 ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - arr_get ldl lc < BV -> PD + 2 <= 65536) ->
  evt psegs (cb_site_post 0x1c28c L s LT DT sx (sbF_PB PB PD BB BV (arr_get lfc lc) (arr_get ldl lc)) (sbF_PD PD BV (arr_get ldl lc))
                          (sbF_BB BB BV (arr_get lfc lc) (arr_get ldl lc)) (sbF_BV BV (arr_get ldl lc)) ra sp gp tp s6 s7 s8 s9 s10 s11 F fc m)
      (MS (cbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 (wz lc)) F (wz 0x1c370) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HBB MI LAY RDL Rlc RLT1 RLT2 RV Rl RBV RPD ROOM. unfold cbR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDL m (munch_refl _ _) (wmono_refl _ _) MI lc Rlc) as [RDc RDl].
  do 2 zstep. shl_norm.
  zs. rewrite (zx16_small (arr_get lfc lc)) by lia. zs. rewrite (zx16_small (arr_get ldl lc)) by lia.
  zs. zs. zs. zs. zs.
  set (V := arr_get lfc lc) in *. set (l := arr_get ldl lc) in *. clearbody V l.
  sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
  zs. zstep. br_cases K.
  -
    zs2. zs2.
    apply evt_done. unfold cb_site_post, cbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 11 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| exact LO].
  -
    sbf_b0 L Gpend PB PD (nbv BB BV V) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV V) LO.
    zs2. zs2. zs2. zs2. rewrite srlw_val16 by lia.
    zs2. zs2. zs2. zs2. reg_as (l + BV + -16) (BV + l - 16).
    apply evt_done. unfold cb_site_post, cbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. do 11 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.

Definition cb_site2_post (X : Z -> Prop) (L : dlay) (s : deflate_state) (LT DT sx : Z) (PB : arr) (PD BB BV : Z) (vs0 vt3 vt6 : Z)
    (ra sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s1 s2 s3 s4 s5 w wbb pcx m',
    ms' = MS (cbR L LT DT sx ra sp gp tp (wz vs0) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz vt3) w (wz BV) (wz vt6)) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16 /\ bv_unsigned w mod 2^16 = BB mod 2^16 /\ X pcx.

Lemma unsigned_wz_neg : forall z, - 2^63 <= z < 0 -> bv_unsigned (wz z) = z + 2^64.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite <- (Z.mod_add z 1 (2^64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma cb_range_test : forall code, 0 <= code < 29 -> bv_ltu (wz (code + -28)) (wz (-20)) = negb ((8 <=? code) && (code <=? 27)).
Proof.
  intros code H. unfold bv_ltu. rewrite (unsigned_wz_neg (-20)) by lia.
  destruct (Z.eq_dec code 28) as [->|NE].
  - change (28 + -28) with 0. rewrite unsigned_lit by lia. reflexivity.
  - rewrite unsigned_wz_neg by lia.
    destruct (Z.leb_spec 8 code), (Z.leb_spec code 27); cbn [andb negb]; [apply Z.ltb_ge| | apply Z.ltb_lt| apply Z.ltb_lt]; lia.
Qed.

Ltac cb_fin2 MU WM GA GD Gpend LOc LOr side EXT :=
  apply evt_done; unfold cb_site2_post, cbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV;
  rewrite ?(proj2 (Z.ltb_ge _ _)), ?(proj2 (Z.ltb_lt _ _)) by lia; do 9 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
  split; [close_EM GA GD Gpend|]; split; [LOc|]; split; [LOr|]; side; (split; [reflexivity| EXT]).

Lemma cb_S2 : forall (L : dlay) (s : deflate_state) (lfc ldl : arr) (LT DT sx lc dist code V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  code = arr_get length_code_a lc -> V = arr_get lfc (code + 257) -> l = arr_get ldl (code + 257) ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m LT lfc ldl 286 -> 0 <= lc < 256 -> 0 < LT -> LT + 4 * 286 < 2^63 ->
  0 <= V < 65536 -> 0 <= l <= 16 ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt psegs (cb_site2_post (fun pcx => (pcx = 0x1c3fc /\ 8 <= code <= 27) \/ (pcx = 0x1c498 /\ ~ (8 <= code <= 27)))
                           L s LT DT sx (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) (code * 4) dist lc
                           ra sp gp tp s6 s7 s8 s9 s10 s11 F fc m)
      (MS (cbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz dist) t4 t5 (wz lc)) F (wz 0x1c2e0) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros Ecode EV El EMH HBB MI LAY RDL Rlc RLT1 RLT2 RV Rl RBV RPD ROOM. unfold cbR.
  pose proof (length_code_range lc Rlc) as Rcode. rewrite <- Ecode in Rcode.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDL m (munch_refl _ _) (wmono_refl _ _) MI (code + 257) ltac:(lia)) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  pose proof (u8ro_read psegs m Z_LENGTH_CODE (av8 length_code_a 256) lc _ (wa (Z_LENGTH_CODE + lc)) (rod_length_code m MI)
                (av8_nth length_code_a 256 lc ltac:(lia)) ltac:(lia) eq_refl) as RDlc. rewrite <- Ecode in RDlc.
  unfold Z_LENGTH_CODE in *.
  zs2. zsb. rewrite (bv8_small code) by lia.
  zs2. shl_norm. zs2.
  zs2. rewrite (zx16_small V) by lia. zs2. rewrite (zx16_small l) by lia.
  clear Ecode EV El.
  zs2. zs2. zs2. zs2. zs2.
  sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
  zs2. zstep. br_cases K.
  -
    zs2. zs2. zs2. zstep. rewrite cb_range_test by lia.
    destruct ((8 <=? code) && (code <=? 27)) eqn:EX; cbn [negb].
    + cb_fin2 MU WM GA GD Gpend ltac:(exact LO) ltac:(exact LO) ltac:(left) ltac:(rewrite andb_true_iff, !Z.leb_le in EX; lia).
    + cb_fin2 MU WM GA GD Gpend ltac:(exact LO) ltac:(exact LO) ltac:(right) ltac:(rewrite andb_false_iff, !Z.leb_gt in EX; lia).
  -
    sbf_b0 L Gpend PB PD (nbv BB BV V) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV V) LO.
    zs2. zs2. zs2. zs2. rewrite srlw_val16 by lia.
    zs2. zs2. zs2. zs2. zstep. reg_as (l + BV + -16) (BV + l - 16). rewrite cb_range_test by lia.
    destruct ((8 <=? code) && (code <=? 27)) eqn:EX; cbn [negb].
    + cb_fin2 MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(apply lo16_unsigned_wz) ltac:(left) ltac:(rewrite andb_true_iff, !Z.leb_le in EX; lia).
    + zstep.
      cb_fin2 MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(apply lo16_unsigned_wz) ltac:(right) ltac:(rewrite andb_false_iff, !Z.leb_gt in EX; lia).
Qed.
End Z_tr_cb1.


Module Z_tr_cb2.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3.Z_tr_cb1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel CompressModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.CompressModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition cb_site3_post (L : dlay) (s : deflate_state) (LT DT sx : Z) (PB : arr) (PD BB BV : Z) (dist : Z)
    (ra sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s3 s4 s5 t6 w wbb m',
    ms' = MS (cbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz dist) w (wz BV) t6) F (wz 0x1c498) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16 /\ bv_unsigned w mod 2^16 = BB mod 2^16.

Lemma cb_S3 : forall (L : dlay) (s : deflate_state) (LT DT sx lc dist code V l : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  code = arr_get length_code_a lc -> V = lc - arr_get base_length_a code -> l = arr_get extra_lbits_a code ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> bv_unsigned w mod 2^16 = BB mod 2^16 ->
  mem_inv psegs m -> dlay_ok L -> 0 <= lc < 256 ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt psegs (cb_site3_post L s LT DT sx (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) dist
                           ra sp gp tp s6 s7 s8 s9 s10 s11 F fc m)
      (MS (cbR L LT DT sx ra sp gp tp (wz (code * 4)) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz dist) w (wz BV) (wz lc)) F (wz 0x1c3fc) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros Ecode EV El EMH HBB HW MI LAY Rlc RBV RPD ROOM. unfold cbR.
  pose proof (length_code_range lc Rlc) as Rcode. rewrite <- Ecode in Rcode.
  pose proof (extra_lbits_facts code Rcode) as (Rex & Rbase & _). rewrite <- El in Rex.
  pose proof (length_base_le lc Rlc) as RVlo. rewrite <- Ecode in RVlo.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  pose proof (u32ro_read m Z_BASE_LENGTH (av32 base_length_a 29) code _ (wa (Z_BASE_LENGTH + 4 * code)) (rod_base_length m MI)
                (av32_nth base_length_a 29 code ltac:(lia)) ltac:(lia) eq_refl) as RDb.
  pose proof (u32ro_read m Z_EXTRA_LBITS (av32 extra_lbits_a 29) code _ (wa (Z_EXTRA_LBITS + 4 * code)) (rod_extra_lbits m MI)
                (av32_nth extra_lbits_a 29 code ltac:(lia)) ltac:(lia) eq_refl) as RDe. rewrite <- El in RDe.
  unfold Z_BASE_LENGTH, Z_EXTRA_LBITS in *.
  do 6 zs2. zs2. zs2. zs2. rewrite <- EV. zs2. zs2.
  assert (RV : 0 <= V < 256) by lia. clear Ecode EV El. zstep. br_cases K.
  -
    zs2. sb_or w1 LO BB ltac:(exact HW). zs2. zs2. zs2. reg_as (l + BV) (BV + l).
    apply evt_done. unfold cb_site3_post, cbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 10 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend|]. split; exact LO.
  -
    zs2. zs2. zs2. sb_or w1 LO BB ltac:(exact HW).
    sbf_b0 L Gpend PB PD (nbv BB BV V) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV V) LO.
    zs2. zs2. zs2. zs2. zs2. rewrite srlw_val by lia.
    zs2. zs2. zs2. zs2. reg_as (l + BV + -16) (BV + l - 16).
    apply evt_done. unfold cb_site3_post, cbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. do 10 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend|]. split; apply lo16_unsigned_wz.
Qed.

Definition cb_site4_post (X : Z -> Prop) (L : dlay) (s : deflate_state) (LT DT sx : Z) (PB : arr) (PD BB BV : Z) (vs0 vt6 : Z)
    (ra sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s1 s2 s3 s4 s5 t5 w wbb pcx m',
    ms' = MS (cbR L LT DT sx ra sp gp tp (wz vs0) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz BV) w t5 (wz vt6)) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16 /\ bv_unsigned w mod 2^16 = BB mod 2^16 /\ X pcx.

Ltac cb_fin4 MU WM GA GD Gpend LOc LOr side EXT :=
  apply evt_done; unfold cb_site4_post, cbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV;
  rewrite ?(proj2 (Z.ltb_ge _ _)), ?(proj2 (Z.ltb_lt _ _)) by lia; do 10 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
  split; [close_EM GA GD Gpend|]; split; [LOc|]; split; [LOr|]; side; (split; [reflexivity| EXT]).

Lemma cb_S4 : forall (L : dlay) (s : deflate_state) (dfc ddl : arr) (LT DT sx dist dcode V l : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dcode = d_code (dist - 1) -> V = arr_get dfc dcode -> l = arr_get ddl dcode ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> bv_unsigned w mod 2^16 = BB mod 2^16 ->
  mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m DT dfc ddl 30 -> 1 <= dist <= 32768 -> 0 < DT -> DT + 4 * 30 < 2^63 ->
  0 <= V < 65536 -> 0 <= l <= 16 ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt psegs (cb_site4_post (fun pcx => (pcx = 0x1c28c /\ dcode < 4) \/ (pcx = 0x1c544 /\ 4 <= dcode))
                           L s LT DT sx (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) (dcode * 4) (dist - 1)
                           ra sp gp tp s6 s7 s8 s9 s10 s11 F fc m)
      (MS (cbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz dist) w (wz BV) t6) F (wz 0x1c498) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros Edc EV El EMH HBB HW MI LAY RDL Rdist RDT1 RDT2 RV Rl RBV RPD ROOM. unfold cbR.
  pose proof (dist_base_le (dist - 1) ltac:(lia)) as (Rdc & _). rewrite <- Edc in Rdc.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDL m (munch_refl _ _) (wmono_refl _ _) MI dcode ltac:(lia)) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  set (didx := if dist - 1 <? 256 then dist - 1 else 256 + Z.shiftr (dist - 1) 7).
  assert (Edi : dcode = arr_get dist_code_a didx) by (rewrite Edc; unfold d_code, didx; destruct (dist - 1 <? 256); reflexivity).
  assert (Rdi : 0 <= didx < 512).
  { unfold didx. destruct (Z.ltb_spec (dist - 1) 256); [lia|]. rewrite Z.shiftr_div_pow2 by lia. change (2^7) with 128.
    pose proof (Z.div_pos (dist - 1) 128 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (dist - 1) 128 256 ltac:(lia) ltac:(lia)). lia. }
  eapply (evt_cut psegs (fun ms' => ms' = MS (mkR ra sp gp tp (wz 65535) (wz Z_LENGTH_CODE) (wz 4) (wz didx) s1 (wz (dl_As L)) (wz LT) (wz DT) (wz (dl_As L + 5888)) (wz sx)
       (wz 16) (wz (-20)) (wz 257) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz Z_DIST_CODE) w (wz BV) (wz (dist - 1))) F (wz 0x1c4b4) fc None m (seg_rom psegs))).
  { do 3 zs2. br_cases K.
    - do 2 zs2. apply evt_done.
      state_eq ltac:(unfold didx; rewrite ?(proj2 (Z.ltb_lt _ _)) by lia; lia).
    - zs2. rewrite srliw7 by lia. do 3 zs2. apply evt_done.
      state_eq ltac:(unfold didx; rewrite ?(proj2 (Z.ltb_ge _ _)) by lia; try replace (dist + -1) with (dist - 1) by lia; lia). }
  intros ms' ->. clearbody didx.
  pose proof (u8ro_read psegs m Z_DIST_CODE (av8 dist_code_a 512) didx _ (wa (Z_DIST_CODE + didx)) (rod_dist_code m MI)
                (av8_nth dist_code_a 512 didx ltac:(lia)) ltac:(lia) eq_refl) as RDdc. rewrite <- Edi in RDdc.
  unfold Z_DIST_CODE in *.
  zs2. zsb. rewrite (bv8_small dcode) by lia.
  zs2. shl_norm. zs2.
  zs2. rewrite (zx16_small l) by lia. zs2. rewrite (zx16_small V) by lia.
  clear Edc EV El Edi.
  zs2. zs2. zs2.
  sb_or w1 LO BB (exact HW).
  zs2. zstep. br_cases K.
  -
    zs2. zs2. zstep. br_cases K4.
    + cb_fin4 MU WM GA GD Gpend ltac:(exact LO) ltac:(exact LO) ltac:(left) ltac:(lia).
    + cb_fin4 MU WM GA GD Gpend ltac:(exact LO) ltac:(exact LO) ltac:(right) ltac:(lia).
  -
    sbf_b0 L Gpend PB PD (nbv BB BV V) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV V) LO.
    zs2. zs2. zs2. zs2. rewrite srlw_val16 by lia.
    zs2. zs2. zs2. zstep. reg_as (l + BV + -16) (BV + l - 16). br_cases K4.
    + cb_fin4 MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(apply lo16_unsigned_wz) ltac:(left) ltac:(lia).
    + zstep. cb_fin4 MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(apply lo16_unsigned_wz) ltac:(right) ltac:(lia).
Qed.

Lemma cb_S5 : forall (L : dlay) (s : deflate_state) (LT DT sx dist dcode V l : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dcode = d_code (dist - 1) -> V = dist - 1 - arr_get base_dist_a dcode -> l = arr_get extra_dbits_a dcode ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> bv_unsigned w mod 2^16 = BB mod 2^16 ->
  mem_inv psegs m -> dlay_ok L -> 1 <= dist <= 32768 ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt psegs (cb_site_post 0x1c28c L s LT DT sx (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l)
                          ra sp gp tp s6 s7 s8 s9 s10 s11 F fc m)
      (MS (cbR L LT DT sx ra sp gp tp (wz (dcode * 4)) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz BV) w t5 (wz (dist - 1))) F (wz 0x1c544) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros Edc EV El EMH HBB HW MI LAY Rdist RBV RPD ROOM. unfold cbR.
  pose proof (dist_base_le (dist - 1) ltac:(lia)) as (Rdc & RVlo). rewrite <- Edc in Rdc, RVlo.
  pose proof (extra_dbits_facts dcode Rdc) as (Rex & Rbase & _). rewrite <- El in Rex.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  pose proof (u32ro_read m Z_BASE_DIST (av32 base_dist_a 30) dcode _ (wa (Z_BASE_DIST + 4 * dcode)) (rod_base_dist m MI)
                (av32_nth base_dist_a 30 dcode ltac:(lia)) ltac:(lia) eq_refl) as RDb.
  pose proof (u32ro_read m Z_EXTRA_DBITS (av32 extra_dbits_a 30) dcode _ (wa (Z_EXTRA_DBITS + 4 * dcode)) (rod_extra_dbits m MI)
                (av32_nth extra_dbits_a 30 dcode ltac:(lia)) ltac:(lia) eq_refl) as RDe. rewrite <- El in RDe.
  unfold Z_BASE_DIST, Z_EXTRA_DBITS in *.
  do 6 zs2. zs2. zs2. zs2. rewrite <- EV. zs2. zs2.
  assert (RV : 0 <= V < 32768) by lia. clear Edc EV El. zstep. br_cases K.
  -
    zs2. sb_or w1 LO BB (exact HW). zs2. zs2. zs2. zs2. reg_as (l + BV) (BV + l).
    apply evt_done. unfold cb_site_post, cbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 11 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| exact LO].
  -
    zs2. zs2. zs2. sb_or w1 LO BB (exact HW).
    sbf_b0 L Gpend PB PD (nbv BB BV V) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV V) LO.
    zs2. zs2. zs2. zs2. zs2. rewrite srlw_val by lia.
    zs2. zs2. zs2. zs2. reg_as (l + BV + -16) (BV + l - 16).
    apply evt_done. unfold cb_site_post, cbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. do 11 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.
End Z_tr_cb2.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3.Z_tr_cb1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3.Z_tr_cb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel CompressModel RefCompressBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.CompressModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCompressBlk1.

Module Z_tr_scan1.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel.ScanModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma le2_add_sx16 : forall v c, le2 (wz (bv_unsigned (sx16 (wz v)) + c)) = le2 (wz (wrap16 (v + c))).
Proof.
  intros v c. apply le2_wz_mod. rewrite lo16_unsigned_wz, wrap16_mod, lo16_idem.
  rewrite <- Z.add_mod_idemp_l by lia. rewrite lo16_sx16, lo16_unsigned_wz. rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Lemma counts_mx : forall c n, 0 <= c -> 0 <= n -> Z.lxor (Z.b2z (Z.lxor c n <? 1)) 7 = if c =? n then 6 else 7.
Proof.
  intros c n Hc Hn. destruct (Z.eqb_spec c n) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - assert (Z.lxor c n <> 0) by (rewrite Z.lxor_eq_0_iff; exact NE).
    assert (0 <= Z.lxor c n) by (apply Z.lxor_nonneg; lia).
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.
Lemma counts_mn : forall c n, 0 <= c -> 0 <= n -> 4 - Z.b2z (Z.lxor c n <? 1) = if c =? n then 3 else 4.
Proof.
  intros c n Hc Hn. destruct (Z.eqb_spec c n) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - assert (Z.lxor c n <> 0) by (rewrite Z.lxor_eq_0_iff; exact NE).
    assert (0 <= Z.lxor c n) by (apply Z.lxor_nonneg; lia).
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

Ltac decide_bools :=
  repeat match goal with
  | |- context [?a <? ?b] => first [rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia]
  | |- context [?a <=? ?b] => first [rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia]
  | |- context [?a =? ?b] => first [rewrite (proj2 (Z.eqb_eq a b)) by lia | rewrite (proj2 (Z.eqb_neq a b)) by lia]
  end; cbn [andb orb negb].


Definition scR (L : dlay) (T mc : Z) (vt0 vt1 vt2 va1 va3 vt4 : Z) (ra sp gp tp s0 s1 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) :=
  mkR ra sp gp tp (wz vt0) (wz vt1) (wz vt2) s0 s1 (wz (-1)) (wz va1) (wz (dl_As L + 2748)) (wz va3) (wz 4) (wz (T + 4 * (mc + 1) + 6)) (wz 9) a7
      s2 s3 s4 s5 (wz (dl_As L + 2506)) s7 s8 s9 s10 s11 t3 (wz vt4) t5 t6.

Notation Wbt L := [(dl_As L + 2748, dl_As L + 2904)] (only parsing).

Definition sc_iter_post (L : dlay) (s1 : deflate_state) (t : tree_id) (T mc n : Z) (dlT bdl : arr) (b : arr) (prevlen nextlen count mx mn : Z)
    (ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a7 t3 b' prevlen' count' mx' mn' pcx m',
    ms' = MS (scR L T mc mx' mn' count' (arr_get dlT (n + 1)) (T + 4 * (n + 1) + 6) prevlen' ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6)
             F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wbt L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' (dl_As L + 2748) (u16s (avct b' bdl 39)) /\ arr_len b' = 39
    /\ (forall f, scan_tree_loop (S f) (set_bl_tree_fc s1 b) t mc n prevlen nextlen count mx mn
                  = scan_tree_loop f (set_bl_tree_fc s1 b') t mc (n + 1) prevlen' (arr_get dlT (n + 1)) count' mx' mn')
    /\ 0 <= count' < mx' /\ (mx' = 138 \/ mx' = 6 \/ mx' = 7) /\ (mn' = 3 \/ mn' = 4) /\ -1 <= prevlen' <= 15
    /\ ((pcx = 0x1b0d8 /\ n + 1 <= mc) \/ (pcx = 0x1b190 /\ n = mc)).

Ltac destr_ifs := repeat match goal with |- context [if ?c then _ else _] => destruct c end.
Ltac sc_close T n MU WM ARR MOD :=
  let KE := fresh "KE" in
  zs2; zs2; zs2; zstep; reg_as (T + 4 * n + 10) (T + 4 * (n + 1) + 6); br_cases KE;
  (apply evt_done; unfold sc_iter_post, scR; do 9 eexists;
   split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
   split; [exact ARR|]; split; [rewrite ?arr_len_set; assumption|]; split; [MOD|];
   split; [destr_ifs; lia|]; split; [destr_ifs; auto|]; split; [destr_ifs; auto|]; split; [lia|];
   first [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]]).

Ltac fix_mn := match goal with |- context [bv_swrap 32 (if ?c then 3 else 4)] =>
  replace (bv_swrap 32 (if c then 3 else 4)) with (if c then 3 else 4) by (destruct c; reflexivity) end.
Ltac sc_mod HL CND :=
  intros f0; rewrite scan_loop_S; cbv zeta; rewrite !HL; rewrite CND; unfold tree_counts, st_upd, REP_3_6, REPZ_3_10, REPZ_11_138; decide_bools; rewrite ?andb_false_r, ?andb_true_r; decide_bools; destr_ifs; reflexivity.

Lemma sc_upd : forall (L : dlay) (s1 : deflate_state) (t : tree_id) (T NT mc n : Z) (dlT bdl : arr) (b : arr) (prevlen nextlen count mx mn : Z)
    (ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2748) (u16s (avct b bdl 39)) -> arr_len b = 39 -> mem_inv psegs m -> dlay_ok L ->
  0 < T -> T + 4 * NT < 2^62 -> mc + 1 < NT ->
  (forall i, Len s1 t i = arr_get dlT i) ->
  (forall i, 0 <= i < NT -> 0 <= arr_get dlT i < 65536) ->
  0 <= n <= mc -> nextlen = arr_get dlT n -> 0 <= nextlen <= 15 ->
  0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  (count + 1 <? mx) && (nextlen =? arr_get dlT (n + 1)) = false ->
  evt psegs (sc_iter_post L s1 t T mc n dlT bdl b prevlen nextlen count mx mn ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 F fc m)
      (MS (scR L T mc mx mn count (arr_get dlT (n + 1)) (T + 4 * n + 6) prevlen ra sp gp tp s0 s1r (wz nextlen) s2 s3 s4 s5 s7 s8 s9 s10 s11 (wz (count + 1)) t5 t6)
          F (wz 0x1b0ec) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR LNB MI LAY RT1 RT2 RNT HL HDL Rn Enl Rcl Rc Rmx Rmn Rpl CND. unfold scR.
  pose proof (munch_refl (Wbt L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. pose proof (avct_zlength b bdl 39 ltac:(lia)) as LCT.
  pose proof (HDL (n + 1) ltac:(lia)) as Rnl'.
  assert (CND' : mx <= count + 1 \/ nextlen <> arr_get dlT (n + 1)).
  { apply andb_false_iff in CND. destruct CND as [C|C]; [left; apply Z.ltb_ge in C; lia| right; apply Z.eqb_neq in C; exact C]. }
  zstep. br_cases K1.
  -
    zstep. br_cases_s K2.
    +
      zstep. br_cases K3.
      *
        pose proof (u16arr_read psegs m (dl_As L + 2748) (avct b bdl 39) (2 * 18) _ (wa (dl_As L + 2748 + 2 * (2 * 18))) ARR (avct_nth_fc b bdl 39 18 ltac:(lia)) ltac:(lia) eq_refl) as RD.
        zs2. zs2.
        ct_store_fc ARR b bdl 39 (dl_As L + 2748) 18 (wrap16 (arr_get b 18 + 1)) ltac:(apply le2_add_sx16).
        zs2. zstep. br_cases K4.
        { do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. sc_close T n MU WM ARR ltac:(sc_mod HL CND). }
        { zs2. do 3 zs2. sc_close T n MU WM ARR ltac:(sc_mod HL CND). }
      *
        pose proof (u16arr_read psegs m (dl_As L + 2748) (avct b bdl 39) (2 * 17) _ (wa (dl_As L + 2748 + 2 * (2 * 17))) ARR (avct_nth_fc b bdl 39 17 ltac:(lia)) ltac:(lia) eq_refl) as RD.
        zs2. zs2.
        ct_store_fc ARR b bdl 39 (dl_As L + 2748) 17 (wrap16 (arr_get b 17 + 1)) ltac:(apply le2_add_sx16).
        zs2. zstep. br_cases K4.
        { do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. sc_close T n MU WM ARR ltac:(sc_mod HL CND). }
        { zs2. do 3 zs2. sc_close T n MU WM ARR ltac:(sc_mod HL CND). }
    +
      zstep. br_cases_s K3.
      *
        pose proof (u16arr_read psegs m (dl_As L + 2748) (avct b bdl 39) (2 * 16) _ (wa (dl_As L + 2748 + 2 * (2 * 16))) ARR (avct_nth_fc b bdl 39 16 ltac:(lia)) ltac:(lia) eq_refl) as RD.
        zs2. zs2.
        ct_store_fc ARR b bdl 39 (dl_As L + 2748) 16 (wrap16 (arr_get b 16 + 1)) ltac:(apply le2_add_sx16).
        zs2. zstep. br_cases K4.
        { do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. sc_close T n MU WM ARR ltac:(sc_mod HL CND). }
        { do 3 zs2. sc_close T n MU WM ARR ltac:(sc_mod HL CND). }
      *
        pose proof (u16arr_read psegs m (dl_As L + 2748) (avct b bdl 39) (2 * nextlen) _ (wa (dl_As L + 2748 + 2 * (2 * nextlen))) ARR (avct_nth_fc b bdl 39 nextlen ltac:(lia)) ltac:(lia) eq_refl) as RD.
        zs2. shl_norm. zs2. zs2. zs2.
        ct_store_fc ARR b bdl 39 (dl_As L + 2748) nextlen (wrap16 (arr_get b nextlen + 1)) ltac:(apply le2_add_sx16).
        set (b1 := arr_set b nextlen (wrap16 (arr_get b nextlen + 1))) in *.
        lazymatch type of ARR with u8arr _ ?mc _ _ =>
          pose proof (u16arr_read psegs mc (dl_As L + 2748) (avct b1 bdl 39) (2 * 16) _ (wa (dl_As L + 2748 + 2 * (2 * 16))) ARR (avct_nth_fc b1 bdl 39 16 ltac:(lia)) ltac:(lia) eq_refl) as RD1 end.
        zs2. zs2.
        ct_store_fc ARR b1 bdl 39 (dl_As L + 2748) 16 (wrap16 (arr_get b1 16 + 1)) ltac:(apply le2_add_sx16).
        zs2. zstep. br_cases K4.
        { do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. subst b1. sc_close T n MU WM ARR ltac:(sc_mod HL CND). }
        { do 3 zs2. subst b1. sc_close T n MU WM ARR ltac:(sc_mod HL CND). }
  -
    pose proof (u16arr_read psegs m (dl_As L + 2748) (avct b bdl 39) (2 * nextlen) _ (wa (dl_As L + 2748 + 2 * (2 * nextlen))) ARR (avct_nth_fc b bdl 39 nextlen ltac:(lia)) ltac:(lia) eq_refl) as RD.
    zs2. shl_norm. zs2. zs2. zs2.
    ct_store_fc ARR b bdl 39 (dl_As L + 2748) nextlen (wrap16 (arr_get b nextlen + (count + 1))) ltac:(apply le2_add_sx16).
    zs2. zstep. br_cases K4.
    + do 3 zs2. sc_close T n MU WM ARR ltac:(sc_mod HL CND).
    + do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. sc_close T n MU WM ARR ltac:(sc_mod HL CND).
Qed.

Lemma sc_iter : forall (L : dlay) (s1 : deflate_state) (t : tree_id) (T NT mc n : Z) (fcT dlT bdl : arr) (b : arr) (prevlen nextlen count mx mn : Z)
    (ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2748) (u16s (avct b bdl 39)) -> arr_len b = 39 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wbt L) m T fcT dlT NT -> 0 < T -> T + 4 * NT < 2^62 -> mc + 1 < NT ->
  (forall i, Len s1 t i = arr_get dlT i) ->
  (forall i, 0 <= i < NT -> 0 <= arr_get dlT i < 65536) -> (forall i, 0 <= i <= mc -> 0 <= arr_get dlT i <= 15) ->
  0 <= n <= mc -> nextlen = arr_get dlT n ->
  0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  evt psegs (sc_iter_post L s1 t T mc n dlT bdl b prevlen nextlen count mx mn ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 F fc m)
      (MS (scR L T mc mx mn count nextlen (T + 4 * n + 6) prevlen ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1b0d8) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR LNB MI LAY RDT RT1 RT2 RNT HL HDL HLEN Rn Enl Rc Rmx Rmn Rpl.
  pose proof (HLEN n ltac:(lia)) as Rcl. rewrite <- Enl in Rcl.
  pose proof (HDL (n + 1) ltac:(lia)) as Rnl'.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (n + 1) ltac:(lia)) as [_ RDl].
  replace (T + 4 * (n + 1) + 2) with (T + 4 * n + 6) in RDl by lia.
  destruct ((count + 1 <? mx) && (nextlen =? arr_get dlT (n + 1))) eqn:CND.
  -
    apply andb_true_iff in CND. destruct CND as [C1 C2]. apply Z.ltb_lt in C1. apply Z.eqb_eq in C2.
    pose proof (munch_refl (Wbt L) m) as MU. pose proof (wmono_refl psegs m) as WM. lay_open LAY.
    unfold scR. zs2. zs2. rewrite (zx16_small (arr_get dlT (n + 1))) by lia. zs2.
    zstep. br_false. zstep. br_true. zs2.
    sc_close T n MU WM ARR ltac:(intros f0; rewrite scan_loop_S; cbv zeta; rewrite !HL; decide_bools; reflexivity).
  -
    unfold scR. zs2. zs2. rewrite (zx16_small (arr_get dlT (n + 1))) by lia. zs2.
    zstep. br_cases K1; [| zstep; br_cases_s K2; [exfalso; apply andb_false_iff in CND; destruct CND as [C|C]; [apply Z.ltb_ge in C; lia| apply Z.eqb_neq in C; lia]|]].
    all: eapply (sc_upd L s1 t T NT mc n dlT bdl b prevlen nextlen count mx mn); eassumption.
Qed.

Definition sc_loop_post (L : dlay) (s1 : deflate_state) (T mc : Z) (bdl : arr) (R : deflate_state)
    (ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists vt0 vt1 vt2 va1 va3 vt4 a7 t3 b' m',
    ms' = MS (scR L T mc vt0 vt1 vt2 va1 va3 vt4 ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1b190) fc None m' (seg_rom psegs)
    /\ munch (Wbt L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u8arr psegs m' (dl_As L + 2748) (u16s (avct b' bdl 39)) /\ arr_len b' = 39 /\ R = set_bl_tree_fc s1 b'.

Lemma sc_loop : forall (f : nat) (L : dlay) (s1 : deflate_state) (t : tree_id) (T NT mc : Z) (fcT dlT bdl : arr) (R : deflate_state) (m0 : mem)
    (n : Z) (b : arr) (prevlen nextlen count mx mn : Z)
    (ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2748) (u16s (avct b bdl 39)) -> arr_len b = 39 -> mem_inv psegs m -> dlay_ok L ->
  munch (Wbt L) m0 m -> wmono psegs m0 m ->
  ct_readable (Wbt L) m0 T fcT dlT NT -> 0 < T -> T + 4 * NT < 2^62 -> mc + 1 < NT ->
  (forall i, Len s1 t i = arr_get dlT i) ->
  (forall i, 0 <= i < NT -> 0 <= arr_get dlT i < 65536) -> (forall i, 0 <= i <= mc -> 0 <= arr_get dlT i <= 15) ->
  0 <= n <= mc -> nextlen = arr_get dlT n ->
  0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  mc + 1 - n <= Z.of_nat (S f) ->
  R = scan_tree_loop (S f) (set_bl_tree_fc s1 b) t mc n prevlen nextlen count mx mn ->
  evt psegs (sc_loop_post L s1 T mc bdl R ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 F fc m0)
      (MS (scR L T mc mx mn count nextlen (T + 4 * n + 6) prevlen ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1b0d8) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR LNB MI LAY MU WM RDT RT1 RT2 RNT HL HDL HLEN Rn Enl Rc Rmx Rmn Rpl FUEL ER.
  - call (sc_iter L s1 t T NT mc n fcT dlT bdl b prevlen nextlen count mx mn).
    1:{ exact ARR. } 1:{ exact LNB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RNT. } 1:{ exact HL. } 1:{ exact HDL. } 1:{ exact HLEN. } 1:{ exact Rn. } 1:{ exact Enl. }
    1:{ exact Rc. } 1:{ exact Rmx. } 1:{ exact Rmn. } 1:{ exact Rpl. }
    match goal with E : forall f : nat, scan_tree_loop (S f) _ _ _ _ _ _ _ _ _ = _ |- _ => rewrite E in ER end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [exfalso; lia|].
    rewrite scan_loop_0 in ER.
    apply evt_done. unfold sc_loop_post. do 10 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| exact ER].
  - call (sc_iter L s1 t T NT mc n fcT dlT bdl b prevlen nextlen count mx mn).
    1:{ exact ARR. } 1:{ exact LNB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RNT. } 1:{ exact HL. } 1:{ exact HDL. } 1:{ exact HLEN. } 1:{ exact Rn. } 1:{ exact Enl. }
    1:{ exact Rc. } 1:{ exact Rmx. } 1:{ exact Rmn. } 1:{ exact Rpl. }
    match goal with E : forall f : nat, scan_tree_loop (S f) _ _ _ _ _ _ _ _ _ = _ |- _ => rewrite E in ER end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end.
    + eapply (IH L s1 t T NT mc fcT dlT bdl R m0 (n + 1)); try eassumption; try lia; reflexivity.
    + rewrite scan_loop_out in ER by lia.
      apply evt_done. unfold sc_loop_post. do 10 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| exact ER].
Qed.
End Z_tr_scan1.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Definition byt (a : arr) : Prop := forall i, 0 <= i < arr_len a -> 0 <= arr_get a i < 256.

Lemma byt_set : forall a i v, byt a -> 0 <= v < 256 -> byt (arr_set a i v).
Proof.
  intros a i v H Hv j Hj. rewrite arr_len_set in Hj. rewrite arr_get_set. destruct ((i =? j) && arr_inb a i); [exact Hv| apply H; exact Hj].
Qed.
Lemma wrap8_range : forall z, 0 <= wrap8 z < 256.
Proof. intros. rewrite wrap8_mod. apply Z.mod_pos_bound. lia. Qed.
Lemma byt_sbF : forall PB PD BB BV V l, byt PB -> byt (sbF_PB PB PD BB BV V l).
Proof. intros. unfold sbF_PB. destruct (16 - l <? BV); [|assumption]. apply byt_set; [apply byt_set; [assumption|]|]; apply wrap8_range. Qed.

Lemma sbF_BV_range : forall BV l, 0 <= BV <= 16 -> 0 <= l <= 16 -> 0 <= sbF_BV BV l <= 16.
Proof. intros BV l H1 H2. unfold sbF_BV. destruct (Z.ltb_spec (16 - l) BV); lia. Qed.
Lemma sbF_PD_range : forall PD BV l, 0 <= PD -> PD <= sbF_PD PD BV l <= PD + 2.
Proof. intros PD BV l H. unfold sbF_PD. destruct (16 - l <? BV); lia. Qed.
Lemma sbF_PB_len : forall PB PD BB BV V l, arr_len (sbF_PB PB PD BB BV V l) = arr_len PB.
Proof. intros. unfold sbF_PB. destruct (16 - l <? BV); rewrite ?arr_len_set; reflexivity. Qed.

Lemma upd4_sym_buf_get : forall s PB PD BB BV i, sym_buf_get (upd4 s PB PD BB BV) i = arr_get PB (ds_lit_bufsize s + i).
Proof. reflexivity. Qed.
Lemma upd4_sym_next : forall s PB PD BB BV, ds_sym_next (upd4 s PB PD BB BV) = ds_sym_next s.
Proof. reflexivity. Qed.
Lemma upd4_lit_bufsize : forall s PB PD BB BV, ds_lit_bufsize (upd4 s PB PD BB BV) = ds_lit_bufsize s.
Proof. reflexivity. Qed.

Lemma land255_small : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof. intros x H. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma lor_shl8_add : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> Z.lor (Z.shiftl b 8) a = a + Z.shiftl b 8.
Proof.
  intros a b Ha Hb. rewrite Z.add_comm. symmetry. apply Z.add_nocarry_lor.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec n 8).
  - rewrite (Z.testbit_neg_r b (n - 8)) by lia. reflexivity.
  - rewrite (Z.bits_above_log2 a n); [apply andb_false_r| lia|].
    destruct (Z.eq_dec a 0) as [->|NE]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|]. eapply Z.lt_le_trans; [apply Ha|]. apply (Z.pow_le_mono_r 2 8 n); lia.
Qed.


Definition cb_S6_post (L : dlay) (s : deflate_state) (PB : arr) (PD BB BV : Z)
    (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 a0 a1 a2 a3 a4 a5 a6 a7 wbb m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c660) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16.

Lemma cb_S6 : forall (L : dlay) (s : deflate_state) (lfc ldl : arr) (LT V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get lfc 256 -> l = arr_get ldl 256 ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m LT lfc ldl 286 -> 0 < LT -> LT + 4 * 286 < 2^63 ->
  0 <= V < 65536 -> 0 <= l <= 16 ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt psegs (cb_S6_post L s (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l)
                        ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz BV) t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (dl_As L)) (wz LT) a2 (wz (dl_As L + 5888)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz BV) t4 t5 t6)
          F (wz 0x1c5e4) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDL RLT1 RLT2 RV Rl RBV RPD ROOM.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDL m (munch_refl _ _) (wmono_refl _ _) MI 256 ltac:(lia)) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  clear EV El.
  zs2. rewrite (zx16_small l) by lia. zs2. rewrite (zx16_small V) by lia.
  zs2. zs2. zs2. zs2. zs2.
  sb_or w LO BB (rewrite lo16_sx16; exact HBB).
  zs2. zstep. br_cases K.
  -
    zs2. zs2.
    apply evt_done. unfold cb_S6_post, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 11 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| exact LO].
  -
    sbf_b0 L Gpend PB PD (nbv BB BV V) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV V) LO.
    zs2. zs2. zs2. zs2. rewrite srlw_val16 by lia.
    zs2. zs2. zs2. zs2. reg_as (l + BV + -16) (BV + l - 16).
    apply evt_done. unfold cb_S6_post, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. do 11 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.


Lemma sub_fp_refl : forall W, sub_fp W W.
Proof. intros W x H. exact H. Qed.

Lemma sbs_ok_cons_flat : forall P s PB PD BB BV v l r, sbs_ok P (upd4 s PB PD BB BV) ((v, l) :: r) ->
  0 <= l <= 16 /\ (16 - l < BV -> PD + 2 <= P) /\ sbs_ok P (upd4 s (sbF_PB PB PD BB BV v l) (sbF_PD PD BV l) (sbF_BB BB BV v l) (sbF_BV BV l)) r.
Proof.
  intros P s PB PD BB BV v l r H. cbn [sbs_ok] in H. destruct H as (H1 & H2 & H3). rewrite send_bits_sbF in H3.
  unfold sb_room, Buf_size in H2. rewrite upd4_bi_valid, upd4_pending in H2. auto.
Qed.
Lemma sbs_run_cons_flat : forall s PB PD BB BV v l r,
  sbs_run (upd4 s PB PD BB BV) ((v, l) :: r) = sbs_run (upd4 s (sbF_PB PB PD BB BV v l) (sbF_PD PD BV l) (sbF_BB BB BV v l) (sbF_BV BV l)) r.
Proof. intros. cbn [sbs_run]. rewrite send_bits_sbF. reflexivity. Qed.

Definition dist_calls (dfc ddl : arr) (dist : Z) : list (Z * Z) :=
  let dcode := d_code (dist - 1) in
  [(arr_get dfc dcode, arr_get ddl dcode)]
  ++ (if negb (arr_get extra_dbits_a dcode =? 0) then [(wrap32 (dist - 1 - arr_get base_dist_a dcode), arr_get extra_dbits_a dcode)] else []).

Definition cb_dist_post (L : dlay) (s : deflate_state) (dfc ddl : arr) (LT DT sx dist : Z) (PB : arr) (PD BB BV : Z)
    (ra sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s3 s4 s5 t4 t5 t6 wbb PB' PD' BB' BV' m',
    ms' = MS (cbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz BV') t4 t5 t6) F (wz 0x1c28c) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB' PD' wbb (wz BV') /\ bv_unsigned wbb mod 2^16 = BB' mod 2^16
    /\ sbs_run (upd4 s PB PD BB BV) (dist_calls dfc ddl dist) = upd4 s PB' PD' BB' BV'
    /\ 0 <= BV' <= 16 /\ 0 <= PD' /\ byt PB'.

Lemma wrap32_small : forall z, 0 <= z < 2^32 -> wrap32 z = z.
Proof. intros z H. rewrite wrap32_mod. apply Z.mod_small. exact H. Qed.

Lemma cb_dist_part : forall (L : dlay) (s : deflate_state) (dfc ddl : arr) (LT DT sx dist : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> bv_unsigned w mod 2^16 = BB mod 2^16 ->
  mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m DT dfc ddl 30 -> 1 <= dist <= 32768 -> 0 < DT -> DT + 4 * 30 < 2^63 ->
  (forall i, 0 <= i < 30 -> 0 <= arr_get dfc i < 65536) ->
  0 <= BV <= 16 -> 0 <= PD -> byt PB ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (dist_calls dfc ddl dist) ->
  evt psegs (cb_dist_post L s dfc ddl LT DT sx dist PB PD BB BV ra sp gp tp s6 s7 s8 s9 s10 s11 F fc m)
      (MS (cbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz dist) w (wz BV) t6) F (wz 0x1c498) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HBB HW MI LAY RDD Rdist RDT1 RDT2 RDf RBV RPD BYT HSB.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold dist_calls in HSB. cbv zeta in HSB.
  remember (d_code (dist - 1)) as dcode eqn:Edc.
  pose proof (dist_base_le (dist - 1) ltac:(lia)) as (Rdc & RVlo). rewrite <- Edc in Rdc, RVlo.
  pose proof (extra_dbits_facts dcode Rdc) as (Rex & Rbase & EXB).
  cbn [app] in HSB. apply sbs_ok_cons_flat in HSB. destruct HSB as (Rl & ROOM & HSB2).
  call (cb_S4 L s dfc ddl LT DT sx dist dcode (arr_get dfc dcode) (arr_get ddl dcode) PB PD BB BV wbb w).
  1:{ exact Edc. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact HW. } 1:{ exact MI. } 1:{ exact LAY. }
  1:{ exact RDD. } 1:{ exact Rdist. } 1:{ exact RDT1. } 1:{ exact RDT2. } 1:{ apply RDf. lia. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. }
  set (V1 := arr_get dfc dcode) in *. set (l1 := arr_get ddl dcode) in *.
  pose proof (sbF_BV_range BV l1 RBV Rl) as RBV1. pose proof (sbF_PD_range PD BV l1 RPD) as RPD1. pose proof (byt_sbF PB PD BB BV V1 l1 BYT) as BYT1.
  match goal with H : _ \/ _ |- _ => destruct H as [[-> X4]|[-> X4]] end.
  -
    apply evt_done. unfold cb_dist_post. do 15 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|].
    split. { unfold dist_calls. cbv zeta. rewrite <- Edc. rewrite EXB. rewrite (proj2 (Z.leb_gt _ _)) by lia. cbn [app]. rewrite sbs_run_cons_flat. reflexivity. }
    split; [exact RBV1|]. split; [lia| exact BYT1].
  -
    rewrite EXB, (proj2 (Z.leb_le _ _)) in HSB2 by lia. rewrite wrap32_small in HSB2 by lia.
    apply sbs_ok_cons_flat in HSB2. destruct HSB2 as (Rl2 & ROOM2 & _).
    match goal with H : EM ?mm _ _ _ _ ?wb _, HB : bv_unsigned ?wb mod _ = _, HWr : bv_unsigned ?wr mod _ = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (cb_S5 L s LT DT sx dist dcode (dist - 1 - arr_get base_dist_a dcode) (arr_get extra_dbits_a dcode) _ _ _ _ wb wr);
      [exact Edc| reflexivity| reflexivity| exact H| exact HB| exact HWr| eassumption| exact LAY| exact Rdist| exact RBV1| lia| exact ROOM2|]
    end.
    apply evt_done. unfold cb_dist_post. do 15 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|].
    split. { unfold dist_calls. cbv zeta. rewrite <- Edc. rewrite EXB. rewrite (proj2 (Z.leb_le _ _)) by lia. cbn [app]. rewrite wrap32_small by lia.
             rewrite !sbs_run_cons_flat. reflexivity. }
    split; [apply sbF_BV_range; assumption|]. split; [|apply byt_sbF; exact BYT1].
    match goal with |- 0 <= sbF_PD ?p ?b ?l => pose proof (sbF_PD_range p b l ltac:(lia)); lia end.
Qed.

Lemma sym_calls_lit : forall X lfc ldl dfc ddl sx, sym_dist X sx = 0 ->
  sym_calls X lfc ldl dfc ddl sx = [(arr_get lfc (sym_lc X sx), arr_get ldl (sym_lc X sx))].
Proof. intros X lfc ldl dfc ddl sx Hd. unfold sym_calls. cbv zeta. rewrite (proj2 (Z.eqb_eq _ _) Hd). reflexivity. Qed.

Lemma sym_calls_match : forall X lfc ldl dfc ddl sx, sym_dist X sx <> 0 -> 0 <= sym_lc X sx < 256 ->
  sym_calls X lfc ldl dfc ddl sx =
  (arr_get lfc (arr_get length_code_a (sym_lc X sx) + 257), arr_get ldl (arr_get length_code_a (sym_lc X sx) + 257))
  :: (if (8 <=? arr_get length_code_a (sym_lc X sx)) && (arr_get length_code_a (sym_lc X sx) <=? 27)
      then [(sym_lc X sx - arr_get base_length_a (arr_get length_code_a (sym_lc X sx)), arr_get extra_lbits_a (arr_get length_code_a (sym_lc X sx)))] else [])
     ++ dist_calls dfc ddl (sym_dist X sx).
Proof.
  intros X lfc ldl dfc ddl sx Hd Hlc. unfold sym_calls, dist_calls. cbv zeta. rewrite (proj2 (Z.eqb_neq _ _) Hd).
  destruct (extra_lbits_facts _ (length_code_range _ Hlc)) as (_ & _ & E). rewrite E.
  replace (arr_get length_code_a (sym_lc X sx) + LITERALS + 1) with (arr_get length_code_a (sym_lc X sx) + 257) by (unfold LITERALS; lia).
  reflexivity.
Qed.

Definition cb_body_post (L : dlay) (s : deflate_state) (lfc ldl dfc ddl : arr) (LT DT sx : Z) (PB : arr) (PD BB BV : Z)
    (ra sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s3 s4 s5 t4 t5 t6 wbb PB' PD' BB' BV' m',
    ms' = MS (cbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz BV') t4 t5 t6) F (wz 0x1c28c) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB' PD' wbb (wz BV') /\ bv_unsigned wbb mod 2^16 = BB' mod 2^16
    /\ sbs_run (upd4 s PB PD BB BV) (sym_calls (upd4 s PB PD BB BV) lfc ldl dfc ddl sx) = upd4 s PB' PD' BB' BV'
    /\ 0 <= BV' <= 16 /\ 0 <= PD' /\ byt PB'.

Lemma cb_body : forall (L : dlay) (s : deflate_state) (lfc ldl dfc ddl : arr) (LT DT sx : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m LT lfc ldl 286 -> ct_readable (Wem L) m DT dfc ddl 30 ->
  0 < LT -> LT + 4 * 286 < 2^63 -> 0 < DT -> DT + 4 * 30 < 2^63 ->
  (forall i, 0 <= i < 286 -> 0 <= arr_get lfc i < 65536) -> (forall i, 0 <= i < 30 -> 0 <= arr_get dfc i < 65536) ->
  0 <= BV <= 16 -> 0 <= PD -> byt PB -> 0 <= ds_lit_bufsize s -> sx < 2^31 ->
  sym_ok 65536 (upd4 s PB PD BB BV) lfc ldl dfc ddl sx ->
  evt psegs (cb_body_post L s lfc ldl dfc ddl LT DT sx PB PD BB BV ra sp gp tp s6 s7 s8 s9 s10 s11 F fc m)
      (MS (cbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c298) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HBB MI LAY RDL RDD RLT1 RLT2 RDT1 RDT2 RLf RDf RBV RPD BYT Rlb Rsx (Hsx & Hlb & Hdist & HSB). unfold cbR.
  rewrite upd4_lit_bufsize in Hlb.
  pose proof EMH as (_ & _ & _ & LNPB).
  set (lb := ds_lit_bufsize s) in *.
  remember (arr_get PB (lb + sx)) as b0 eqn:Eb0. remember (arr_get PB (lb + (sx + 1))) as b1 eqn:Eb1. remember (arr_get PB (lb + (sx + 1 + 1))) as lc eqn:Elc.
  assert (Rb0 : 0 <= b0 < 256) by (rewrite Eb0; apply BYT; lia).
  assert (Rb1 : 0 <= b1 < 256) by (rewrite Eb1; apply BYT; lia).
  assert (Rlc : 0 <= lc < 256) by (rewrite Elc; apply BYT; lia).
  assert (Edist : sym_dist (upd4 s PB PD BB BV) sx = b0 + Z.shiftl b1 8).
  { unfold sym_dist, sym_d0, sym_d1. rewrite !upd4_sym_buf_get. fold lb. rewrite <- Eb0, <- Eb1, !land255_small by lia. reflexivity. }
  assert (Elc' : sym_lc (upd4 s PB PD BB BV) sx = lc) by (unfold sym_lc; rewrite upd4_sym_buf_get; fold lb; rewrite <- Elc; reflexivity).
  assert (Rsh : 0 <= Z.shiftl b1 8 <= 65280) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Edist in Hdist.
  set (dist := b0 + Z.shiftl b1 8) in *.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY.
  pose proof EMH as EMH'. open_EM EMH'.
  pose proof (u8arr_read psegs m (dl_Ab L) (av8 PB 65536) (lb + sx) _ (wa (dl_Ab L + (lb + sx))) Gpend (av8_nth PB 65536 (lb + sx) ltac:(lia)) ltac:(lia) eq_refl) as RD0.
  pose proof (u8arr_read psegs m (dl_Ab L) (av8 PB 65536) (lb + (sx + 1)) _ (wa (dl_Ab L + (lb + (sx + 1)))) Gpend (av8_nth PB 65536 (lb + (sx + 1)) ltac:(lia)) ltac:(lia) eq_refl) as RD1.
  pose proof (u8arr_read psegs m (dl_Ab L) (av8 PB 65536) (lb + (sx + 1 + 1)) _ (wa (dl_Ab L + (lb + (sx + 1 + 1)))) Gpend (av8_nth PB 65536 (lb + (sx + 1 + 1)) ltac:(lia)) ltac:(lia) eq_refl) as RD2.
  rewrite <- Eb0 in RD0. rewrite <- Eb1 in RD1. rewrite <- Elc in RD2.
  do 10 zs2. rewrite ?Z.mod_small by lia.
  zsb. rewrite (bv8_small b0) by lia. zsb. rewrite (bv8_small b1) by lia.
  zs2. rewrite ?Z.mod_small by lia. zs2. zsb. rewrite (bv8_small lc) by lia.
  zs2. zs2. rewrite (lor_shl8_add b0 b1) by lia. fold dist.
  clear GA GD Gpend RD0 RD1 RD2 LPB LNP.
  assert (Rdist : 0 <= dist < 65536) by (unfold dist; lia).
  zstep. br_cases K.
  -
    assert (SC := sym_calls_lit (upd4 s PB PD BB BV) lfc ldl dfc ddl sx ltac:(rewrite Edist; exact K)). rewrite Elc' in SC.
    rewrite SC in HSB. apply sbs_ok_cons_flat in HSB. destruct HSB as (Rl & ROOM & _).
    call (cb_S1 L s lfc ldl LT DT sx lc PB PD BB BV wbb).
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ assumption. } 1:{ exact RDL. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    1:{ apply RLf. lia. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. }
    apply evt_done. unfold cb_body_post. do 15 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|].
    split. { rewrite SC. rewrite sbs_run_cons_flat. reflexivity. }
    split; [apply sbF_BV_range; assumption|]. split; [pose proof (sbF_PD_range PD BV (arr_get ldl lc) RPD); lia| apply byt_sbF; exact BYT].
  -
    assert (SC := sym_calls_match (upd4 s PB PD BB BV) lfc ldl dfc ddl sx ltac:(rewrite Edist; exact K) ltac:(rewrite Elc'; exact Rlc)).
    rewrite Edist, Elc' in SC. fold dist in SC.
    pose proof HSB as HSB'. rewrite SC in HSB'. clear HSB.
    remember (arr_get length_code_a lc) as code eqn:Ecode.
    pose proof (length_code_range lc Rlc) as Rcode. rewrite <- Ecode in Rcode.
    apply sbs_ok_cons_flat in HSB'. destruct HSB' as (Rl & ROOM & HSB2).
    call (cb_S2 L s lfc ldl LT DT sx lc dist code (arr_get lfc (code + 257)) (arr_get ldl (code + 257)) PB PD BB BV wbb).
    1:{ exact Ecode. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ assumption. } 1:{ exact RDL. }
    1:{ exact Rlc. } 1:{ lia. } 1:{ lia. } 1:{ apply RLf. lia. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. }
    set (V1 := arr_get lfc (code + 257)) in *. set (l1 := arr_get ldl (code + 257)) in *.
    pose proof (sbF_BV_range BV l1 RBV Rl) as RBV1. pose proof (sbF_PD_range PD BV l1 RPD) as RPD1. pose proof (byt_sbF PB PD BB BV V1 l1 BYT) as BYT1.
    assert (Rd2 : 1 <= dist <= 32768) by lia.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X2]|[-> X2]] end.
    +
      rewrite (proj2 (andb_true_iff _ _)) in HSB2 by (rewrite !Z.leb_le; lia). cbn [app] in HSB2.
      apply sbs_ok_cons_flat in HSB2. destruct HSB2 as (Rl2 & ROOM2 & HSB3).
      match goal with H : EM ?mm _ _ _ _ ?wb _, HB : bv_unsigned ?wb mod _ = _, HWr : bv_unsigned ?wr mod _ = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (cb_S3 L s LT DT sx lc dist code (lc - arr_get base_length_a code) (arr_get extra_lbits_a code) _ _ _ _ wb wr);
        [exact Ecode| reflexivity| reflexivity| exact H| exact HB| exact HWr| eassumption| assumption| exact Rlc| exact RBV1| lia| exact ROOM2|]
      end.
      set (V2 := lc - arr_get base_length_a code) in *. set (l2 := arr_get extra_lbits_a code) in *.
      call (cb_dist_part L s dfc ddl LT DT sx dist).
      1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ assumption. }
      1:{ eapply ct_readable_rebase; [exact RDD| exact MU| exact WM| apply sub_fp_refl]. } 1:{ exact Rd2. } 1:{ exact RDT1. } 1:{ exact RDT2. } 1:{ exact RDf. }
      1:{ apply sbF_BV_range; assumption. } 1:{ pose proof (sbF_PD_range (sbF_PD PD BV l1) (sbF_BV BV l1) l2 ltac:(lia)); lia. } 1:{ apply byt_sbF; exact BYT1. } 1:{ exact HSB3. }
      apply evt_done. unfold cb_body_post. do 15 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|].
      split. { rewrite SC. rewrite (proj2 (andb_true_iff _ _)) by (rewrite !Z.leb_le; lia). cbn [app]. rewrite !sbs_run_cons_flat. eassumption. }
      split; [assumption|]. split; assumption.
    +
      rewrite (proj2 (andb_false_iff _ _)) in HSB2 by (rewrite !Z.leb_gt; lia). cbn [app] in HSB2.
      call (cb_dist_part L s dfc ddl LT DT sx dist).
      1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ assumption. }
      1:{ eapply ct_readable_rebase; [exact RDD| exact MU| exact WM| apply sub_fp_refl]. } 1:{ exact Rd2. } 1:{ exact RDT1. } 1:{ exact RDT2. } 1:{ exact RDf. }
      1:{ exact RBV1. } 1:{ lia. } 1:{ exact BYT1. } 1:{ exact HSB2. }
      apply evt_done. unfold cb_body_post. do 15 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|].
      split. { rewrite SC. rewrite (proj2 (andb_false_iff _ _)) by (rewrite !Z.leb_gt; lia). cbn [app]. rewrite !sbs_run_cons_flat. eassumption. }
      split; [assumption|]. split; assumption.
Qed.