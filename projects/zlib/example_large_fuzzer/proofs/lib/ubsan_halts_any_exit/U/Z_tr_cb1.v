(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees TreesTab SendModel BitsModel BitsModel2 FillWinModel TrSmallModel CompressModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Definition CB_TRAP : Z := 0x1e194.
Definition ucbR (L : dlay) (LT DT sx : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) :=
  mkR ra sp gp tp (wz (-20)) (wz 256) (wz 4) s0 s1 (wz (dl_As L)) (wz LT) (wz DT) (wz (dl_As L + 5888)) (wz sx) (wz 1) (wz 16) (wz 31)
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz 65535) (wz 72976) (wz 18446744073709478639) (wz 32768).

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
  evt usegs (ucb_post 0x1d9f4 L s LT DT sx (sbF_PB PB PD BB BV (arr_get lfc lc) (arr_get ldl lc)) (sbF_PD PD BV (arr_get ldl lc))
                          (sbF_BB BB BV (arr_get lfc lc) (arr_get ldl lc)) (sbF_BV BV (arr_get ldl lc)) ra sp gp tp s11 F fc m)
      (MS (ucbR L LT DT sx ra sp gp tp s0 s1 (wz lc) s3 s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1db6c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HBB MI LAY RDL Rlc RLT1 RLT2 ALT RV Rl RBV RPD ROOM. unfold ucbR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDL m (munch_refl _ _) (wmono_refl _ _) MI lc Rlc) as [RDc RDl].
  ustep CB_TRAP. shl_norm. uwalk 0x1db90 CB_TRAP.
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
      uwalk 0x1dbf8 CB_TRAP.
      pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1dc2c CB_TRAP.
      pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1dc48 CB_TRAP.
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
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1e160) fc None m' (seg_rom usegs)
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
          F (wz 0x1e040) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDL RLT1 RLT2 ALT RV Rl RBV RPD ROOM.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDL m (munch_refl _ _) (wmono_refl _ _) MI 256 ltac:(lia)) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  uwalk 0x1e064 CB_TRAP. at_pc 0x1e064.
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
    uwalk 0x1e0d0 CB_TRAP. at_pc 0x1e0d0.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1e104 CB_TRAP. at_pc 0x1e104.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1e128 CB_TRAP. at_pc 0x1e128.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
    zs2. zs2. zs2. zstep.
    zstep. br_true. zstep.
    reg_as (l + BV + -16) (BV + l - 16).
    apply evt_done. unfold cb_S6_post, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia. do 12 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.
