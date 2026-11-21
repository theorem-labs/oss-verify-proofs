(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.

Module Z_tr_cb1.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require TreesTab SendModel BitsModel BitsModel2 FillWinModel TrSmallModel CompressModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreesTab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.CompressModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Definition CB_TRAP : Z := 0x1dd70.
Definition ucbR (L : dlay) (LT DT sx : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) :=
  mkR ra sp gp tp (wz (-20)) (wz 256) (wz 4) s0 s1 (wz (dl_As L)) (wz LT) (wz DT) (wz (dl_As L + 5888)) (wz sx) (wz 1) (wz 16) (wz 31)
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz 65535) (wz 72880) (wz 18446744073709478735) (wz 32768).

Definition ucb_post (EXIT : Z) (L : dlay) (s : deflate_state) (LT DT sx : Z) (PB : arr) (PD BB BV : Z)
    (ra sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 wbb m',
    ms' = MS (ucbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F (wz EXIT) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16.

Lemma cb_S1 : forall (L : dlay) (s : deflate_state) (lfc ldl : arr) (LT DT sx lc : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m LT lfc ldl 286 -> 0 <= lc < 286 -> 0 < LT -> LT + 4 * 286 < 2^63 -> LT mod 2 = 0 ->
  0 <= arr_get lfc lc < 32768 -> 0 <= arr_get ldl lc <= 16 ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - arr_get ldl lc < BV -> PD + 2 <= 65536) ->
  evt usegs (ucb_post 0x1d5d0 L s LT DT sx (sbF_PB PB PD BB BV (arr_get lfc lc) (arr_get ldl lc)) (sbF_PD PD BV (arr_get ldl lc))
                          (sbF_BB BB BV (arr_get lfc lc) (arr_get ldl lc)) (sbF_BV BV (arr_get ldl lc)) ra sp gp tp s11 F fc m)
      (MS (ucbR L LT DT sx ra sp gp tp s0 s1 (wz lc) s3 s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1d748) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HBB MI LAY RDL Rlc RLT1 RLT2 ALT RV Rl RBV RPD ROOM. unfold ucbR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDL m (munch_refl _ _) (wmono_refl _ _) MI lc Rlc) as [RDc RDl].
  ustep CB_TRAP. shl_norm. uwalk 0x1d76c CB_TRAP.
  zs. rewrite (zx16_small (arr_get ldl lc)) by lia. zs2. zs. rewrite (zx16_small (arr_get lfc lc)) by lia.
  set (V := arr_get lfc lc) in *. set (l := arr_get ldl lc) in *. clearbody V l.
  do 4 zs2.
  shl_g0. zs2. zs2. shl_g1.
  zstep. br_cases K.
  -
    ustep CB_TRAP. zs.
      zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zstep. zs2. zstep.
      reg_as (BV + l) (BV + l).
    apply evt_done. unfold ucb_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia. do 13 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| exact LO].
  -
    ustep CB_TRAP. zs. zs. zs. zs. zs.
      sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zs. zs. zstep. zs.
      uwalk 0x1d7d4 CB_TRAP.
      pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1d808 CB_TRAP.
      pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1d824 CB_TRAP.
      zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
    zs2. zs2. zs2. zstep.
      zstep. br_true. zstep.
      reg_as (l + BV + -16) (BV + l - 16).
    apply evt_done. unfold ucb_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia. do 13 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.

Definition cb_S6_post (L : dlay) (s : deflate_state) (PB : arr) (PD BB BV : Z)
    (ra sp gp tp t1 t2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 s0 s1 a0 a1 a2 a4 a5 a6 a7 wbb m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1dd3c) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16.

Lemma cb_S6 : forall (L : dlay) (s : deflate_state) (lfc ldl : arr) (LT V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get lfc 256 -> l = arr_get ldl 256 ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m LT lfc ldl 286 -> 0 < LT -> LT + 4 * 286 < 2^63 -> LT mod 2 = 0 ->
  0 <= V < 32768 -> 0 <= l <= 16 ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt usegs (cb_S6_post L s (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l)
                ra sp gp tp t1 t2 (wz (dl_As L + 5888)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (dl_As L)) (wz LT) a2 (wz (dl_As L + 5888)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1dc1c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDL RLT1 RLT2 ALT RV Rl RBV RPD ROOM.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDL m (munch_refl _ _) (wmono_refl _ _) MI 256 ltac:(lia)) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  uwalk 0x1dc40 CB_TRAP. at_pc 0x1dc40.
  zs. rewrite (zx16_small l) by lia. zs2. zs. rewrite (zx16_small V) by lia.
  clear EV El.
  do 5 zs2. shl_g0. zs2. zs2. shl_g1.
  zstep. br_cases K.
  -
    ustep CB_TRAP. zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zstep. zs2. zstep.
    apply evt_done. unfold cb_S6_post, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia. do 12 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| exact LO].
  -
    ustep CB_TRAP. zs. zs. zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zs. zs. zstep. zs.
    uwalk 0x1dcac CB_TRAP. at_pc 0x1dcac.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1dce0 CB_TRAP. at_pc 0x1dce0.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1dd04 CB_TRAP. at_pc 0x1dd04.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
    zs2. zs2. zs2. zstep.
    zstep. br_true. zstep.
    reg_as (l + BV + -16) (BV + l - 16).
    apply evt_done. unfold cb_S6_post, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia. do 12 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.
End Z_tr_cb1.


Module Z_tr_cb2.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4.Z_tr_cb1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require TreesTab SendModel BitsModel BitsModel2 FillWinModel TrSmallModel CompressModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreesTab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.CompressModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Definition cb_S2_post (L : dlay) (s : deflate_state) (LT DT sx : Z) (PB : arr) (PD BB BV BV0 : Z) (dist lc code : Z)
    (ra sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s6 s7 s8 s9 s10 w m',
    ms' = MS (ucbR L LT DT sx ra sp gp tp (wz dist) w (wz lc) (wz BV) (wz (code * 4)) (wz code) s6 s7 s8 s9 s10 s11) F (wz 0x1d858) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV0) /\ bv_unsigned w mod 2^16 = BB mod 2^16.

Lemma cb_S2 : forall (L : dlay) (s : deflate_state) (lfc ldl : arr) (LT DT sx lc dist code V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  code = arr_get length_code_a lc -> V = arr_get lfc (code + 257) -> l = arr_get ldl (code + 257) ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m LT lfc ldl 286 -> 0 <= lc < 256 -> 0 < LT -> LT + 4 * 286 < 2^63 -> LT mod 2 = 0 ->
  0 <= V < 32768 -> 0 <= l <= 16 ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt usegs (cb_S2_post L s LT DT sx (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) BV dist lc code
                ra sp gp tp s11 F fc m)
      (MS (ucbR L LT DT sx ra sp gp tp (wz dist) s1 (wz lc) s3 s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1d648) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros Ecode EV El EMH HBB MI LAY RDL Rlc RLT1 RLT2 ALT RV Rl RBV RPD ROOM. unfold ucbR.
  pose proof (length_code_range lc Rlc) as Rcode. rewrite <- Ecode in Rcode.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDL m (munch_refl _ _) (wmono_refl _ _) MI (code + 257) ltac:(lia)) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  pose proof (u8ro_read usegs m Z_LENGTH_CODE (av8 length_code_a 256) lc _ (wa (Z_LENGTH_CODE + lc)) (rod_length_code m MI)
                (av8_nth length_code_a 256 lc ltac:(lia)) ltac:(lia) eq_refl) as RDlc. rewrite <- Ecode in RDlc.
  unfold Z_LENGTH_CODE in *.
  ustep CB_TRAP. zs2. zsb. rewrite (bv8_small code) by lia.
  zs2. shl_norm.
  uwalk 0x1d674 CB_TRAP. at_pc 0x1d674.
  zs. rewrite (zx16_small l) by lia. zs2. zs. rewrite (zx16_small V) by lia.
  clear Ecode EV El.
  do 4 zs2. shl_g0. zs2. zs2. shl_g1.
  zstep. br_cases K.
  -
    ustep CB_TRAP. zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zstep. zs2.
      reg_as (BV + l) (BV + l).
    apply evt_done. unfold cb_S2_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia. do 7 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| exact LO].
  -
    ustep CB_TRAP. zs. zs. zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zs. zs. zstep. zs.
    uwalk 0x1d6dc CB_TRAP. at_pc 0x1d6dc.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1d710 CB_TRAP. at_pc 0x1d710.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1d72c CB_TRAP. at_pc 0x1d72c.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
    zs2. zs2. zs2. zstep.
      zstep. br_true.
    reg_as (l + BV + -16) (BV + l - 16).
    apply evt_done. unfold cb_S2_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia. do 7 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.

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

Definition cb_S3_post (L : dlay) (s : deflate_state) (LT DT sx : Z) (PB : arr) (PD BB BV : Z) (dist : Z)
    (ra sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s2 s4 s5 s6 s7 s8 s9 s10 w m',
    ms' = MS (ucbR L LT DT sx ra sp gp tp (wz dist) w s2 (wz BV) s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1d99c) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16.

Lemma cb_S3 : forall (L : dlay) (s : deflate_state) (LT DT sx lc dist code V l : Z) (X : bool) (PB : arr) (PD BB BV BV0 : Z) (w : word)
    (ra sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  code = arr_get length_code_a lc -> V = lc - arr_get base_length_a code -> l = arr_get extra_lbits_a code -> X = (8 <=? code) && (code <=? 27) ->
  EM m L s PB PD w (wz BV0) -> bv_unsigned w mod 2^16 = BB mod 2^16 ->
  mem_inv usegs m -> dlay_ok L -> 0 <= lc < 256 -> 0 <= BV0 < 2^32 ->
  0 <= BV <= 16 -> 0 <= PD -> (X = true -> 16 - l < BV -> PD + 2 <= 65536) ->
  evt usegs (cb_S3_post L s LT DT sx (if X then sbF_PB PB PD BB BV V l else PB) (if X then sbF_PD PD BV l else PD)
                (if X then sbF_BB BB BV V l else BB) (if X then sbF_BV BV l else BV) dist ra sp gp tp s11 F fc m)
      (MS (ucbR L LT DT sx ra sp gp tp (wz dist) w (wz lc) (wz BV) (wz (code * 4)) (wz code) s6 s7 s8 s9 s10 s11) F (wz 0x1d858) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros Ecode EV El EX EMH HW MI LAY Rlc RBV0 RBV RPD ROOM. unfold ucbR.
  pose proof (length_code_range lc Rlc) as Rcode. rewrite <- Ecode in Rcode.
  pose proof (extra_lbits_facts code Rcode) as (Rex & Rbase & _). rewrite <- El in Rex.
  pose proof (length_base_le lc Rlc) as RVlo. rewrite <- Ecode in RVlo.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  zs2. zs2. zs2. zstep.
  lazymatch goal with H : mem_inv usegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (u32ro_read mc Z_BASE_LENGTH (av32 base_length_a 29) code _ (wa (Z_BASE_LENGTH + 4 * code)) (rod_base_length mc H)
                (av32_nth base_length_a 29 code ltac:(lia)) ltac:(lia) eq_refl) as RDb;
    pose proof (u32ro_read mc Z_EXTRA_LBITS (av32 extra_lbits_a 29) code _ (wa (Z_EXTRA_LBITS + 4 * code)) (rod_extra_lbits mc H)
                (av32_nth extra_lbits_a 29 code ltac:(lia)) ltac:(lia) eq_refl) as RDe end.
  rewrite <- El in RDe. unfold Z_BASE_LENGTH, Z_EXTRA_LBITS in *.
  ustep CB_TRAP. zs2. zstep. rewrite cb_range_test by lia. rewrite <- EX.
  destruct X.
  -
    cbn [negb].
    assert (CX : 8 <= code <= 27) by (symmetry in EX; apply andb_true_iff in EX; rewrite !Z.leb_le in EX; lia).
    uwalk 0x1d888 CB_TRAP. at_pc 0x1d888.
    zs2. zs2. zs2.
    ustep CB_TRAP. zs2. zs2.
    rewrite <- EV. zs2. zs2. ustep CB_TRAP. zs2. zs2.
    assert (RV : 0 <= V < 256) by lia.
    zs2. rewrite (land16_small V) by lia.
    zs2. zs2. zs2. shl_g0. zs2. zs2. shl_g1.
    clear Ecode EV El.
    zstep. br_cases K.
    +
      ustep CB_TRAP. zs2. zs2. zs2.
      sb_or w1 LO BB ltac:(exact HW).
      zs2. zstep. ustep CB_TRAP. zstep.
      reg_as (BV + l) (BV + l).
      apply evt_done. unfold cb_S3_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia. do 10 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [close_EM GA GD Gpend| exact LO].
    +
      ustep CB_TRAP. zs. zs. zs. zs.
      sb_or w1 LO BB ltac:(exact HW).
      zs. zs. zstep. zs.
      uwalk 0x1d90c CB_TRAP. at_pc 0x1d90c.
      pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
      zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
      uwalk 0x1d940 CB_TRAP. at_pc 0x1d940.
      pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
      uwalk 0x1d95c CB_TRAP. at_pc 0x1d95c.
      zs2. rewrite srlw_val16 by lia.
      pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
      zs2. zstep. ustep CB_TRAP. zs2. zs2.
      rewrite swrap32_add_mod64, ?wz_add_mod64. strip32.
      zstep. br_true. zstep.
      reg_as (BV + (l + -16)) (BV + l - 16).
      apply evt_done. unfold cb_S3_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia. do 10 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
  -
    cbn [negb].
    apply evt_done. unfold cb_S3_post, ucbR. do 10 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| exact HW].
Qed.
End Z_tr_cb2.


Module Z_tr_cb3.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4.Z_tr_cb1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require TreesTab SendModel BitsModel BitsModel2 FillWinModel TrSmallModel CompressModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreesTab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.CompressModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Definition cb_S4_post (L : dlay) (s : deflate_state) (LT DT sx : Z) (PB : arr) (PD BB BV BV0 : Z) (dist dcode : Z)
    (ra sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s1 s5 s7 s8 s9 s10 w m',
    ms' = MS (ucbR L LT DT sx ra sp gp tp (wz (dcode * 4)) s1 (wz (dist - 1)) (wz BV) (wz dcode) s5 w s7 s8 s9 s10 s11) F (wz 0x1dae4) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV0) /\ bv_unsigned w mod 2^16 = BB mod 2^16.

Lemma cb_S4 : forall (L : dlay) (s : deflate_state) (dfc ddl : arr) (LT DT sx dist dcode V l : Z) (PB : arr) (PD BB BV : Z) (w : word)
    (ra sp gp tp s2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dcode = d_code (dist - 1) -> V = arr_get dfc dcode -> l = arr_get ddl dcode ->
  EM m L s PB PD w (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 ->
  mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m DT dfc ddl 30 -> 1 <= dist <= 32768 -> 0 < DT -> DT + 4 * 30 < 2^63 -> DT mod 2 = 0 ->
  0 <= V < 32768 -> 0 <= l <= 16 ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt usegs (cb_S4_post L s LT DT sx (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) BV dist dcode
                ra sp gp tp s11 F fc m)
      (MS (ucbR L LT DT sx ra sp gp tp (wz dist) w s2 (wz BV) s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1d99c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros Edc EV El EMH HW MI LAY RDL Rdist RDT1 RDT2 ADT RV Rl RBV RPD ROOM. unfold ucbR.
  pose proof (dist_base_le (dist - 1) ltac:(lia)) as (Rdc & _). rewrite <- Edc in Rdc.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDL m (munch_refl _ _) (wmono_refl _ _) MI dcode ltac:(lia)) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  set (didx := if dist - 1 <? 256 then dist - 1 else Z.shiftr (dist - 1) 7 + 256).
  assert (Edi : dcode = arr_get dist_code_a didx).
  { rewrite Edc; unfold d_code, didx; destruct (dist - 1 <? 256); [reflexivity|]. f_equal. lia. }
  assert (Rdi : 0 <= didx < 512).
  { unfold didx. destruct (Z.ltb_spec (dist - 1) 256); [lia|]. rewrite Z.shiftr_div_pow2 by lia. change (2^7) with 128.
    pose proof (Z.div_pos (dist - 1) 128 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (dist - 1) 128 256 ltac:(lia) ltac:(lia)). lia. }
  assert (RSH7 : 0 <= Z.shiftr (dist + -1) 7 < 256).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^7) with 128. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  zs2. zs2. zs2.
  eapply (evt_cut usegs (fun ms' => exists s5', ms' = MS (ucbR L LT DT sx ra sp gp tp (wz didx) w (wz (dist - 1)) (wz BV) (wz Z_DIST_CODE) s5' s6 s7 s8 s9 s10 s11)
                                                  F (wz 0x1d9d0) fc None m (seg_rom usegs))).
  { unfold ucbR, Z_DIST_CODE. zstep. br_cases K.
    - ustep CB_TRAP. zs2. rewrite srliw7 by lia. zs2. zs2. ustep CB_TRAP. apply evt_done. eexists.
      state_eq ltac:(unfold didx; rewrite ?(proj2 (Z.ltb_ge _ _)) by lia; try replace (dist + -1) with (dist - 1) by lia; lia).
    - zs2. zs2. zstep. br_true. apply evt_done. eexists.
      state_eq ltac:(unfold didx; rewrite ?(proj2 (Z.ltb_lt _ _)) by lia; lia). }
  intros ms' (s5' & ->). clearbody didx. unfold ucbR.
  pose proof (u8ro_read usegs m Z_DIST_CODE (av8 dist_code_a 512) didx _ (wa (Z_DIST_CODE + didx)) (rod_dist_code m MI)
                (av8_nth dist_code_a 512 didx ltac:(lia)) ltac:(lia) eq_refl) as RDdc. rewrite <- Edi in RDdc.
  unfold Z_DIST_CODE in *.
  zs2. zsb. rewrite (bv8_small dcode) by lia.
  zs2. shl_norm.
  uwalk 0x1da00 CB_TRAP. at_pc 0x1da00.
  zs. rewrite (zx16_small V) by lia. zs. rewrite (zx16_small l) by lia.
  clear Edc EV El Edi.
  do 5 zs2. shl_g0. zs2. zs2. shl_g1.
  zstep. br_cases K.
  -
    ustep CB_TRAP. zs2. zs2.
    sb_or w1 LO BB ltac:(exact HW).
    zstep. zs2.
    reg_as (BV + l) (BV + l).
    apply evt_done. unfold cb_S4_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| exact LO].
  -
    ustep CB_TRAP. zs. zs. zs. zs.
    sb_or w1 LO BB ltac:(exact HW).
    zs. zs. zstep. zs.
    uwalk 0x1da64 CB_TRAP. at_pc 0x1da64.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1da98 CB_TRAP. at_pc 0x1da98.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1dab4 CB_TRAP. at_pc 0x1dab4.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
    zs2. zs2. zs2. zstep.
    zstep. br_true.
    reg_as (l + BV + -16) (BV + l - 16).
    apply evt_done. unfold cb_S4_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.

Lemma cb_S5 : forall (L : dlay) (s : deflate_state) (LT DT sx dist dcode V l : Z) (X : bool) (PB : arr) (PD BB BV BV0 : Z) (w : word)
    (ra sp gp tp s1 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dcode = d_code (dist - 1) -> V = dist - 1 - arr_get base_dist_a dcode -> l = arr_get extra_dbits_a dcode -> X = (4 <=? dcode) ->
  EM m L s PB PD w (wz BV0) -> bv_unsigned w mod 2^16 = BB mod 2^16 ->
  mem_inv usegs m -> dlay_ok L -> 1 <= dist <= 32768 -> 0 <= BV0 < 2^32 ->
  0 <= BV <= 16 -> 0 <= PD -> (X = true -> 16 - l < BV -> PD + 2 <= 65536) ->
  evt usegs (ucb_post 0x1d5d0 L s LT DT sx (if X then sbF_PB PB PD BB BV V l else PB) (if X then sbF_PD PD BV l else PD)
                (if X then sbF_BB BB BV V l else BB) (if X then sbF_BV BV l else BV) ra sp gp tp s11 F fc m)
      (MS (ucbR L LT DT sx ra sp gp tp (wz (dcode * 4)) s1 (wz (dist - 1)) (wz BV) (wz dcode) s5 w s7 s8 s9 s10 s11) F (wz 0x1dae4) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros Edc EV El EX EMH HW MI LAY Rdist RBV0 RBV RPD ROOM. unfold ucbR.
  pose proof (dist_base_le (dist - 1) ltac:(lia)) as (Rdc & RVlo). rewrite <- Edc in Rdc, RVlo.
  pose proof (extra_dbits_facts dcode Rdc) as (Rex & Rbase & EXD). rewrite <- El in Rex.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  zs2. zs2. zs2. zstep.
  lazymatch goal with H : mem_inv usegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (u32ro_read mc Z_BASE_DIST (av32 base_dist_a 30) dcode _ (wa (Z_BASE_DIST + 4 * dcode)) (rod_base_dist mc H)
                (av32_nth base_dist_a 30 dcode ltac:(lia)) ltac:(lia) eq_refl) as RDb;
    pose proof (u32ro_read mc Z_EXTRA_DBITS (av32 extra_dbits_a 30) dcode _ (wa (Z_EXTRA_DBITS + 4 * dcode)) (rod_extra_dbits mc H)
                (av32_nth extra_dbits_a 30 dcode ltac:(lia)) ltac:(lia) eq_refl) as RDe end.
  rewrite <- El in RDe. unfold Z_BASE_DIST, Z_EXTRA_DBITS in *.
  ustep CB_TRAP. zstep. br_cases K.
  -
    replace X with false by (rewrite EX; symmetry; apply Z.leb_gt; lia).
    apply evt_done. unfold ucb_post, ucbR. do 13 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| exact HW].
  -
    replace X with true by (rewrite EX; symmetry; apply Z.leb_le; lia).
    assert (ROOM' : 16 - l < BV -> PD + 2 <= 65536) by (intros; apply ROOM; [rewrite EX; apply Z.leb_le; lia| assumption]).
    uwalk 0x1db10 CB_TRAP. at_pc 0x1db10.
    zs2. zs2. zs2. ustep CB_TRAP. zs2. zs2.
    zs2. zs2. zs2. zs2.
    rewrite <- EV. assert (RV : 0 <= V < 32768) by lia.
    zs2. rewrite (land16_small V) by lia.
    zs2. zs2. shl_g0. zs2. zs2. shl_g1.
    clear Edc EV El.
    zstep. br_cases K2.
    +
      ustep CB_TRAP. zs2. zs2. zs2.
      sb_or w1 LO BB ltac:(exact HW).
      zs2. zstep.
      zstep. br_true. zstep.
      reg_as (BV + l) (BV + l).
      apply evt_done. unfold ucb_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia. do 13 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [close_EM GA GD Gpend| exact LO].
    +
      ustep CB_TRAP. zs. zs. zs. zs.
      sb_or w1 LO BB ltac:(exact HW).
      zs. zs. zstep. zs.
      uwalk 0x1db8c CB_TRAP. at_pc 0x1db8c.
      pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
      zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
      uwalk 0x1dbc0 CB_TRAP. at_pc 0x1dbc0.
      pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
      uwalk 0x1dbdc CB_TRAP. at_pc 0x1dbdc.
      zs2. rewrite srlw_val16 by lia.
      pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
      zs2. zstep. ustep CB_TRAP. zs2. zs2. rewrite swrap32_add_mod64, ?wz_add_mod64. strip32.
      zstep. br_true. zstep.
      reg_as (BV + (l + -16)) (BV + l - 16).
      apply evt_done. unfold ucb_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia. do 13 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.
End Z_tr_cb3.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4.Z_tr_cb1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4.Z_tr_cb2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4.Z_tr_cb3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require TreesTab SendModel BitsModel BitsModel2 FillWinModel TrSmallModel CompressModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreesTab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.CompressModel.
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

Lemma wrap32_small : forall z, 0 <= z < 2^32 -> wrap32 z = z.
Proof. intros z H. rewrite wrap32_mod. apply Z.mod_small. exact H. Qed.

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

Definition c15 (fc : arr) (n : Z) : Prop := forall i, 0 <= i < n -> 0 <= arr_get fc i < 32768.

Definition cb_part_post (EXIT : Z) (L : dlay) (s : deflate_state) (LT DT sx : Z) (PB : arr) (PD BB BV : Z) (cs : list (Z * Z))
    (ra sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 wbb PB' PD' BB' BV' m',
    ms' = MS (ucbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F (wz EXIT) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB' PD' wbb (wz BV') /\ bv_unsigned wbb mod 2^16 = BB' mod 2^16
    /\ sbs_run (upd4 s PB PD BB BV) cs = upd4 s PB' PD' BB' BV'
    /\ 0 <= BV' <= 16 /\ 0 <= PD' /\ byt PB'.

Lemma cb_dist_part : forall (L : dlay) (s : deflate_state) (dfc ddl : arr) (LT DT sx dist : Z) (PB : arr) (PD BB BV : Z) (w : word)
    (ra sp gp tp s2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD w (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 ->
  mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m DT dfc ddl 30 -> 1 <= dist <= 32768 -> 0 < DT -> DT + 4 * 30 < 2^63 -> DT mod 2 = 0 ->
  c15 dfc 30 ->
  0 <= BV <= 16 -> 0 <= PD -> byt PB ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (dist_calls dfc ddl dist) ->
  evt usegs (cb_part_post 0x1d5d0 L s LT DT sx PB PD BB BV (dist_calls dfc ddl dist) ra sp gp tp s11 F fc m)
      (MS (ucbR L LT DT sx ra sp gp tp (wz dist) w s2 (wz BV) s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1d99c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY RDD Rdist RDT1 RDT2 ADT RDf RBV RPD BYT HSB.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold dist_calls in HSB. cbv zeta in HSB.
  remember (d_code (dist - 1)) as dcode eqn:Edc.
  pose proof (dist_base_le (dist - 1) ltac:(lia)) as (Rdc & RVlo). rewrite <- Edc in Rdc, RVlo.
  pose proof (extra_dbits_facts dcode Rdc) as (Rex & Rbase & EXB).
  cbn [app] in HSB. apply sbs_ok_cons_flat in HSB. destruct HSB as (Rl & ROOM & HSB2).
  call (cb_S4 L s dfc ddl LT DT sx dist dcode (arr_get dfc dcode) (arr_get ddl dcode) PB PD BB BV w).
  1:{ exact Edc. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HW. } 1:{ exact MI. } 1:{ exact LAY. }
  1:{ exact RDD. } 1:{ exact Rdist. } 1:{ exact RDT1. } 1:{ exact RDT2. } 1:{ exact ADT. } 1:{ apply RDf. lia. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. }
  set (V1 := arr_get dfc dcode) in *. set (l1 := arr_get ddl dcode) in *.
  pose proof (sbF_BV_range BV l1 RBV Rl) as RBV1. pose proof (sbF_PD_range PD BV l1 RPD) as RPD1. pose proof (byt_sbF PB PD BB BV V1 l1 BYT) as BYT1.
  match goal with H : EM ?mm _ _ _ _ ?wr _, HWr : bv_unsigned ?wr mod _ = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (cb_S5 L s LT DT sx dist dcode (dist - 1 - arr_get base_dist_a dcode) (arr_get extra_dbits_a dcode) (4 <=? dcode) _ _ _ _ BV wr);
    [exact Edc| reflexivity| reflexivity| reflexivity| exact H| exact HWr| eassumption| exact LAY| exact Rdist| lia| exact RBV1| lia| |]
  end.
  1:{ intros X4. rewrite EXB, X4 in HSB2. cbn [negb app] in HSB2. rewrite wrap32_small in HSB2 by lia.
      apply sbs_ok_cons_flat in HSB2. destruct HSB2 as (_ & ROOM2 & _). exact ROOM2. }
  apply evt_done. unfold cb_part_post. do 17 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|].
  split. { unfold dist_calls. cbv zeta. rewrite <- Edc. rewrite EXB.
           destruct (4 <=? dcode); cbn [negb app]; rewrite ?wrap32_small by lia; rewrite !sbs_run_cons_flat; reflexivity. }
  destruct (4 <=? dcode).
  - split; [apply sbF_BV_range; lia|]. split; [|apply byt_sbF; exact BYT1].
    match goal with |- 0 <= sbF_PD ?p ?b ?l => pose proof (sbF_PD_range p b l ltac:(lia)); lia end.
  - split; [exact RBV1|]. split; [lia| exact BYT1].
Qed.

Lemma cb_body : forall (L : dlay) (s : deflate_state) (lfc ldl dfc ddl : arr) (LT DT sx : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m LT lfc ldl 286 -> ct_readable (Wem L) m DT dfc ddl 30 ->
  0 < LT -> LT + 4 * 286 < 2^63 -> 0 < DT -> DT + 4 * 30 < 2^63 -> LT mod 2 = 0 -> DT mod 2 = 0 ->
  c15 lfc 286 -> c15 dfc 30 ->
  0 <= BV <= 16 -> 0 <= PD -> byt PB -> 0 <= ds_lit_bufsize s -> sx < 2^31 ->
  sym_ok 65536 (upd4 s PB PD BB BV) lfc ldl dfc ddl sx ->
  evt usegs (cb_part_post 0x1d5d0 L s LT DT sx PB PD BB BV (sym_calls (upd4 s PB PD BB BV) lfc ldl dfc ddl sx) ra sp gp tp s11 F fc m)
      (MS (ucbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1d5dc) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HBB MI LAY RDL RDD RLT1 RLT2 RDT1 RDT2 ALT ADT RLf RDf RBV RPD BYT Rlb Rsx (Hsx & Hlb & Hdist & HSB). unfold ucbR.
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
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY.
  pose proof EMH as EMH'. open_EM EMH'.
  pose proof (u8arr_read usegs m (dl_Ab L) (av8 PB 65536) (lb + sx) _ (wa (dl_Ab L + (lb + sx))) Gpend (av8_nth PB 65536 (lb + sx) ltac:(lia)) ltac:(lia) eq_refl) as RD0.
  pose proof (u8arr_read usegs m (dl_Ab L) (av8 PB 65536) (lb + (sx + 1)) _ (wa (dl_Ab L + (lb + (sx + 1)))) Gpend (av8_nth PB 65536 (lb + (sx + 1)) ltac:(lia)) ltac:(lia) eq_refl) as RD1.
  pose proof (u8arr_read usegs m (dl_Ab L) (av8 PB 65536) (lb + (sx + 1 + 1)) _ (wa (dl_Ab L + (lb + (sx + 1 + 1)))) Gpend (av8_nth PB 65536 (lb + (sx + 1 + 1)) ltac:(lia)) ltac:(lia) eq_refl) as RD2.
  rewrite <- Eb0 in RD0. rewrite <- Eb1 in RD1. rewrite <- Elc in RD2.
  zs2. zs2. zs2. rewrite ?Z.mod_small by lia.
  uwalk 0x1d604 CB_TRAP. at_pc 0x1d604.
  zs2. zs2. zs2. rewrite ?Z.mod_small by lia.
  uwalk 0x1d618 CB_TRAP. at_pc 0x1d618.
  zs2. zs2. zs2. rewrite ?Z.mod_small by lia.
  uwalk 0x1d62c CB_TRAP. at_pc 0x1d62c.
  zsb. rewrite (bv8_small b1) by lia. zsb. rewrite (bv8_small b0) by lia.
  zs2. zsb. rewrite (bv8_small lc) by lia.
  zs2. zs2. rewrite (lor_shl8_add b0 b1) by lia. fold dist.
  clear GA GD Gpend RD0 RD1 RD2 LPB LNP.
  assert (Rdist : 0 <= dist < 65536) by (unfold dist; lia).
  zstep. br_cases K.
  -
    assert (SC := sym_calls_lit (upd4 s PB PD BB BV) lfc ldl dfc ddl sx ltac:(rewrite Edist; exact K)). rewrite Elc' in SC.
    rewrite SC in HSB. apply sbs_ok_cons_flat in HSB. destruct HSB as (Rl & ROOM & _).
    call (cb_S1 L s lfc ldl LT DT sx lc PB PD BB BV wbb).
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ assumption. } 1:{ exact RDL. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact ALT. }
    1:{ apply RLf. lia. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. }
    apply evt_done. unfold cb_part_post. do 17 eexists.
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
    1:{ exact Rlc. } 1:{ lia. } 1:{ lia. } 1:{ exact ALT. } 1:{ apply RLf. lia. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. }
    set (V1 := arr_get lfc (code + 257)) in *. set (l1 := arr_get ldl (code + 257)) in *.
    pose proof (sbF_BV_range BV l1 RBV Rl) as RBV1. pose proof (sbF_PD_range PD BV l1 RPD) as RPD1. pose proof (byt_sbF PB PD BB BV V1 l1 BYT) as BYT1.
    assert (Rd2 : 1 <= dist <= 32768) by lia.
    match goal with H : EM ?mm _ _ _ _ ?wr _, HWr : bv_unsigned ?wr mod _ = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (cb_S3 L s LT DT sx lc dist code (lc - arr_get base_length_a code) (arr_get extra_lbits_a code) ((8 <=? code) && (code <=? 27)) _ _ _ _ BV wr);
      [exact Ecode| reflexivity| reflexivity| reflexivity| exact H| exact HWr| eassumption| assumption| exact Rlc| lia| exact RBV1| lia| |]
    end.
    1:{ intros X3. rewrite X3 in HSB2. cbn [app] in HSB2. apply sbs_ok_cons_flat in HSB2. destruct HSB2 as (_ & ROOM2 & _). exact ROOM2. }
    set (V2 := lc - arr_get base_length_a code) in *. set (l2 := arr_get extra_lbits_a code) in *.
    match goal with H : EM ?mm _ _ _ _ ?wr _, HWr : bv_unsigned ?wr mod _ = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (cb_dist_part L s dfc ddl LT DT sx dist _ _ _ _ wr);
      [exact H| exact HWr| eassumption| assumption| | exact Rd2| exact RDT1| exact RDT2| exact ADT| exact RDf| | | | |]
    end.
    1:{ eapply ct_readable_rebase; [exact RDD| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ destruct ((8 <=? code) && (code <=? 27)); [apply sbF_BV_range; [exact RBV1|]| exact RBV1].
        pose proof (extra_lbits_facts code Rcode) as (Rex & _); subst l2; lia. }
    1:{ destruct ((8 <=? code) && (code <=? 27)); [pose proof (sbF_PD_range (sbF_PD PD BV l1) (sbF_BV BV l1) l2 ltac:(lia)); lia| lia]. }
    1:{ destruct ((8 <=? code) && (code <=? 27)); [apply byt_sbF|]; exact BYT1. }
    1:{ destruct ((8 <=? code) && (code <=? 27)); cbn [app] in HSB2; [apply sbs_ok_cons_flat in HSB2; destruct HSB2 as (_ & _ & HSB3); exact HSB3| exact HSB2]. }
    apply evt_done. unfold cb_part_post. do 17 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|].
    split. { rewrite SC. rewrite sbs_run_cons_flat. destruct ((8 <=? code) && (code <=? 27)); cbn [app]; rewrite ?sbs_run_cons_flat; eassumption. }
    split; [assumption|]. split; assumption.
Qed.
