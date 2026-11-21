(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_cb3 Z_tr_st1 Z_tr_st4 Z_tr_st5 Z_tr_st7.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition st_c10_post (L : dlay) (s : deflate_state) (T mc1 n nextlen curlen count : Z) (PB : arr) (PD BB BV : Z)
    (ra sp gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists w s5 s6 s7 wbb pcx m',
    ms' = MS (stR L T mc1 n nextlen ra sp gp tp (wz curlen) w (wz (65535 + count - 1)) (wz BV) (wz (bv_swrap 32 (Z.shiftl (65535 + count - 1) (BV mod 32)))) s5 s6 s7 s8 s9 s10 s11)
             F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1c9c4 /\ BV <= 13) \/ (pcx = 0x1cc18 /\ 14 <= BV)).

Ltac c10_fin MU WM GA GD Gpend LO side EXT :=
  apply evt_done; unfold st_c10_post, stR, sbF_PB, sbF_PD, sbF_BB, sbF_BV;
  rewrite ?(proj2 (Z.ltb_ge _ _)), ?(proj2 (Z.ltb_lt _ _)) by lia; do 7 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
  split; [close_EM GA GD Gpend|]; split; [LO|]; side; (split; [reflexivity| EXT]).

Lemma st_c10 : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc1 n nextlen curlen count V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s1 s4 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc 17 -> l = arr_get bdl 17 ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 ->
  0 <= V < 65536 -> 0 <= l <= 16 -> 0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) -> 0 <= count < 2^31 ->
  evt psegs (st_c10_post L s T mc1 n nextlen curlen count (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) ra sp gp tp s8 s9 s10 s11 F fc m)
      (MS (stR L T mc1 n nextlen ra sp gp tp (wz curlen) s1 (wz (65535 + count)) (wz BV) s4 s5 (zx16 wbb) s7 s8 s9 s10 s11) F (wz 0x1c950) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDB RV Rl RBV RPD ROOM Rcnt. unfold stR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDB m (munch_refl _ _) (wmono_refl _ _) MI 17 ltac:(lia)) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  clear EV El.
  zs2. rewrite (zx16_small l) by lia. zs2. rewrite (zx16_small V) by lia.
  zs2. zs2. zs2.
  sb_or w LO BB (rewrite lo16_zx16; exact HBB).
  zstep. br_cases K.
  -
    zs2. zs2. zs2. zs2. replace (65535 + count + -1) with (65535 + count - 1) by lia.
    zstep. br_cases K2.
    + c10_fin MU WM GA GD Gpend ltac:(exact LO) ltac:(left) ltac:(lia).
    + c10_fin MU WM GA GD Gpend ltac:(exact LO) ltac:(right) ltac:(lia).
  -
    sbf_b0 L Gpend PB PD (nbv BB BV V) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV V) LO.
    zs2. zs2. zs2. zs2. rewrite srlw_val16 by lia.
    zs2. zs2. reg_as (l + BV + -16) (BV + l - 16).
    zs2. zs2. replace (65535 + count + -1) with (65535 + count - 1) by lia.
    zstep. br_cases K2.
    + c10_fin MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(right) ltac:(lia).
    + c10_fin MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(left) ltac:(lia).
Qed.
