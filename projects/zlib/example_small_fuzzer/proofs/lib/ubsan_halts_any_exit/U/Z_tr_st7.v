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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_cb4 Z_tr_st4.

Module Z_tr_st1.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_cb4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Definition ST_TRAP : Z := 0x1eb5c.
Definition ST_BODY : Z := 0x1e29c.
Definition ST_LATCH : Z := 0x1e290.
Definition ST_EXIT : Z := 0x1eb20.
Definition ST_REP : Z := 0x1e2f8.
Definition ST_TAIL : Z := 0x1e400.
Definition ST_T138 : Z := 0x1eac4.

Definition ustR (L : dlay) (T mc n nextlen : Z) (x1 x8 x9 x18 x19 x23 x24 x25 x26 x27 : word) (sp gp tp : word) :=
  mkR x1 sp gp tp (wz 0) (wz (dl_As L + 2748)) (wz 38) x8 x9 (wz (dl_As L)) (wz T) (wz mc) (wz (dl_As L + 2047)) (wz n) (wz nextlen) (wz (dl_As L + 5936)) (wz 65535)
      x18 x19 (wz 10) (wz (-65)) (wz 15) x23 x24 x25 x26 x27 (wz 16) (wz 31) (wz 4) (wz 9).

Definition ust_tail_post (L : dlay) (s : deflate_state) (T mc n nextlen curlen : Z) (PB : arr) (PD BB BV : Z)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x1 x8 x9 x18 x19 x24 x26 x27 wbb pcx m',
    ms' = MS (ustR L T mc n nextlen x1 x8 x9 x18 x19 (wz curlen) x24 (wz 0) x26 x27 sp gp tp) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16
    /\ ((pcx = ST_TAIL /\ nextlen <> 0) \/ (pcx = ST_T138 /\ nextlen = 0)).

Definition ust_rep_post (L : dlay) (s : deflate_state) (T mc n nextlen curlen k : Z) (PB : arr) (PD BB BV : Z)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x8 x9 x18 x19 x26 x27 wbb pcx m',
    ms' = MS (ustR L T mc n nextlen (wz BV) x8 x9 x18 x19 (wz curlen) (wz (dl_As L + 2748 + curlen * 4)) (wz (k - 1)) x26 x27 sp gp tp) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16
    /\ ((pcx = ST_REP /\ k - 1 <> 0) \/ (pcx = 0x1e3f8 /\ k - 1 = 0)).

Lemma st_rep_iter : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc n nextlen curlen k V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (x8 x9 x18 x19 x26 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc curlen -> l = arr_get bdl curlen ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 -> 0 <= curlen < 39 ->
  0 <= V < 32768 -> 0 <= l <= 16 -> 0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) -> 1 <= k < 2^31 ->
  evt usegs (ust_rep_post L s T mc n nextlen curlen k (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) sp gp tp F fc m)
      (MS (ustR L T mc n nextlen (wz BV) x8 x9 x18 x19 (wz curlen) (wz (dl_As L + 2748 + curlen * 4)) (wz k) x26 x27 sp gp tp) F (wz ST_REP) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDB Rcl RV Rl RBV RPD ROOM Rk. unfold ustR, ST_REP.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDB m (munch_refl _ _) (wmono_refl _ _) MI curlen Rcl) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  replace (dl_As L + 2748 + 4 * curlen) with (dl_As L + 2748 + curlen * 4) in RDc, RDl by lia.
  clear EV El.
  zs. rewrite (zx16_small V) by lia. zs. rewrite (zx16_small l) by lia.
  do 5 zs2. shl_g0. zs2. zs2. shl_g1.
  zstep. br_cases K.
  -
    ustep ST_TRAP. zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zstep. zs2.
    zs2. reg_as (k + -1) (k - 1). zstep. ustep ST_TRAP. zs2.
    zstep. br_cases_s K2.
    + apply evt_done. unfold ust_rep_post, ustR, ST_REP, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia. do 9 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [close_EM GA GD Gpend|]. split; [exact LO|]. left. split; [reflexivity| lia].
    + apply evt_done. unfold ust_rep_post, ustR, ST_REP, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia. do 9 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [close_EM GA GD Gpend|]. split; [exact LO|]. right. split; [reflexivity| lia].
  -
    ustep ST_TRAP. zs. zs. zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zs. zs. zstep. zs.
    uwalk 0x1e360 ST_TRAP. at_pc 0x1e360.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1e394 ST_TRAP. at_pc 0x1e394.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1e3b0 ST_TRAP. at_pc 0x1e3b0.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
    zs2. zs2. zs2. zstep.
    zstep. br_true.
    reg_as (l + BV + -16) (BV + l - 16).
    zs2. reg_as (k + -1) (k - 1). zstep. ustep ST_TRAP. zs2.
    zstep. br_cases_s K2.
    + apply evt_done. unfold ust_rep_post, ustR, ST_REP, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia. do 9 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [close_EM GA GD Gpend|]. split; [apply lo16_unsigned_wz|]. left. split; [reflexivity| lia].
    + apply evt_done. unfold ust_rep_post, ustR, ST_REP, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia. do 9 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [close_EM GA GD Gpend|]. split; [apply lo16_unsigned_wz|]. right. split; [reflexivity| lia].
Qed.

Definition ust_rep_loop_post (L : dlay) (s : deflate_state) (T mc n nextlen curlen : Z) (R : deflate_state)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists x8 x9 x18 x19 x26 x27 wbb PB' PD' BB' BV' m',
    ms' = MS (ustR L T mc n nextlen (wz BV') x8 x9 x18 x19 (wz curlen) (wz (dl_As L + 2748 + curlen * 4)) (wz 0) x26 x27 sp gp tp) F (wz 0x1e3f8) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ EM m' L s PB' PD' wbb (wz BV') /\ bv_unsigned wbb mod 2^16 = BB' mod 2^16
    /\ R = upd4 s PB' PD' BB' BV' /\ 0 <= BV' <= 16 /\ 0 <= PD'.

Lemma st_rep : forall (k : nat) (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc n nextlen curlen V l : Z) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV : Z) (wbb : word)
    (x8 x9 x18 x19 x26 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc curlen -> l = arr_get bdl curlen ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono usegs m0 m ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> 0 <= curlen < 39 ->
  0 <= V < 32768 -> 0 <= BV <= 16 -> 0 <= PD -> Z.of_nat (S k) < 2^31 ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (repeat (V, l) (S k)) ->
  R = sbs_run (upd4 s PB PD BB BV) (repeat (V, l) (S k)) ->
  evt usegs (ust_rep_loop_post L s T mc n nextlen curlen R sp gp tp F fc m0)
      (MS (ustR L T mc n nextlen (wz BV) x8 x9 x18 x19 (wz curlen) (wz (dl_As L + 2748 + curlen * 4)) (wz (Z.of_nat (S k))) x26 x27 sp gp tp) F (wz ST_REP) fc None m (seg_rom usegs)).
Proof.
  induction k as [|k IH]; intros until m; intros EV El EMH HBB MI LAY MU WM RDB Rcl RV RBV RPD Rk HSB ER.
  all: cbn [repeat] in HSB, ER; apply sbs_ok_cons_flat in HSB; destruct HSB as (Rl & ROOM & HSB2); rewrite sbs_run_cons_flat in ER.
  - call (st_rep_iter L s bfc bdl T mc n nextlen curlen (Z.of_nat 1) V l PB PD BB BV wbb).
    1:{ exact EV. } 1:{ exact El. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ exact Rcl. } 1:{ exact RV. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. } 1:{ lia. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [exfalso; lia|].
    cbn [repeat sbs_run] in ER. change (Z.of_nat 1 - 1) with 0.
    apply evt_done. unfold ust_rep_loop_post. do 12 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact ER|]. split; [apply sbF_BV_range; assumption| pose proof (sbF_PD_range PD BV l RPD); lia].
  - call (st_rep_iter L s bfc bdl T mc n nextlen curlen (Z.of_nat (S (S k))) V l PB PD BB BV wbb).
    1:{ exact EV. } 1:{ exact El. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ exact Rcl. } 1:{ exact RV. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. } 1:{ lia. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [|exfalso; lia].
    replace (Z.of_nat (S (S k)) - 1) with (Z.of_nat (S k)) by lia.
    eapply (IH L s bfc bdl T mc n nextlen curlen V l R m0); try eassumption; try lia.
    + apply sbF_BV_range; assumption.
    + pose proof (sbF_PD_range PD BV l RPD). lia.
Qed.
End Z_tr_st1.


Module Z_tr_st2.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_cb4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.Z_tr_st1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition ust_siteB_post (L : dlay) (s : deflate_state) (T mc n nextlen curlen : Z) (PB : arr) (PD BB BV : Z)
    (x1 x24 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x8 x9 x18 x19 x26 x27 wbb m',
    ms' = MS (ustR L T mc n nextlen x1 x8 x9 x18 x19 (wz curlen) x24 (wz BV) x26 x27 sp gp tp) F (wz 0x1e874) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16.

Lemma st_siteB : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc n nextlen curlen V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (x1 x8 x9 x18 x19 x24 x25 x26 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc curlen -> l = arr_get bdl curlen ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 -> 0 <= curlen < 39 ->
  0 <= V < 32768 -> 0 <= l <= 16 -> 0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt usegs (ust_siteB_post L s T mc n nextlen curlen (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) x1 x24 sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 x8 x9 x18 x19 (wz curlen) x24 x25 x26 x27 sp gp tp) F (wz 0x1e5c8) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDB Rcl RV Rl RBV RPD ROOM. unfold ustR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDB m (munch_refl _ _) (wmono_refl _ _) MI curlen Rcl) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  replace (dl_As L + 2748 + 4 * curlen) with (dl_As L + 2748 + curlen * 4) in RDc, RDl by lia.
  clear EV El.
  ustep ST_TRAP. ustep ST_TRAP. zs2. shl_norm. zs2. ustep ST_TRAP.
  zs. rewrite (zx16_small l) by lia. zs2. zs2.
  zstep. br_cases K.
  -
    ustep ST_TRAP. ustep ST_TRAP. zs. rewrite (zx16_small V) by lia. zs2. zs2. shl_g0. ustep ST_TRAP.
    zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zstep. zs2. zstep.
    apply evt_done. unfold ust_siteB_post, ustR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend| exact LO].
  -
    ustep ST_TRAP. ustep ST_TRAP. zs. rewrite (zx16_small V) by lia. zs2. zs2. shl_g0. ustep ST_TRAP.
    zs. zs. zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zs. zs. zstep. zs.
    uwalk 0x1e640 ST_TRAP. at_pc 0x1e640.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1e674 ST_TRAP. at_pc 0x1e674.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1e690 ST_TRAP. at_pc 0x1e690.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
    zs2. zs2. zs2. zstep.
    zstep. br_true.
    reg_as (l + BV + -16) (BV + l - 16). zstep.
    apply evt_done. unfold ust_siteB_post, ustR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.
End Z_tr_st2.


Module Z_tr_st3.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_cb4 Z_tr_st4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.Z_tr_st1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Lemma land16_x : forall x, 0 <= x < 65536 -> Z.land (65535 + (x + 3) + -2) 65535 = x.
Proof.
  intros x Hx. change 65535 with (Z.ones 16) at 2. rewrite Z.land_ones by lia. change (2 ^ 16) with 65536.
  replace (65535 + (x + 3) + -2) with (x + 1 * 65536) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. exact Hx.
Qed.
Lemma cnt36_eqm : forall cnt, (65535 + cnt + -2) mod 2^16 = (cnt - 3) mod 2^16.
Proof. intros. replace (65535 + cnt + -2) with (cnt - 3 + 1 * 2^16) by lia. apply Z.mod_add. lia. Qed.

Definition ust_c36_post (L : dlay) (s : deflate_state) (T mc n nextlen curlen cnt : Z) (PB : arr) (PD BB BV : Z)
    (x1 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists w x9 x18 x19 x27 pcx m',
    ms' = MS (ustR L T mc n nextlen x1 (wz BV) x9 x18 x19 (wz curlen) (wz cnt) (wz BV) w x27 sp gp tp) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1ea30 /\ BV <= 14) \/ (pcx = 0x1e954 /\ 15 <= BV)).

Ltac c36_fin MU WM GA GD Gpend DEC LO side EXT :=
  apply evt_done; unfold ust_c36_post, ustR, sbF_PB, sbF_PD, sbF_BB, sbF_BV; DEC; do 7 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
  split; [close_EM GA GD Gpend|]; split; [LO|]; side; (split; [reflexivity| EXT]).

Lemma st_c36 : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc n nextlen curlen cnt V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (x1 x8 x9 x18 x19 x25 x26 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc 16 -> l = arr_get bdl 16 ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 ->
  0 <= V < 32768 -> 0 <= l <= 16 -> 0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt usegs (ust_c36_post L s T mc n nextlen curlen cnt (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) x1 sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 x8 x9 x18 x19 (wz curlen) (wz cnt) x25 x26 x27 sp gp tp) F (wz 0x1e874) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDB RV Rl RBV RPD ROOM. unfold ustR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDB m (munch_refl _ _) (wmono_refl _ _) MI 16 ltac:(lia)) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  clear EV El.
  ustep ST_TRAP.
  zs. rewrite (zx16_small l) by lia. zs2. zs. rewrite (zx16_small V) by lia.
  do 4 zs2. shl_g0. zs2. zs2. shl_g1.
  zstep. br_cases K.
  -
    ustep ST_TRAP. zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zstep. zs2. zs2. zstep.
    zstep. br_cases K2.
    + c36_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia) ltac:(exact LO) ltac:(right) ltac:(lia).
    + c36_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia) ltac:(exact LO) ltac:(left) ltac:(lia).
  -
    ustep ST_TRAP. zs. zs. zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zs. zs. zstep. zs.
    uwalk 0x1e8e0 ST_TRAP. at_pc 0x1e8e0.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1e914 ST_TRAP. at_pc 0x1e914.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1e930 ST_TRAP. at_pc 0x1e930.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
    zs2. zs2. zs2. zstep. ustep ST_TRAP. zs2.
    zstep. reg_as (l + BV + -16) (BV + l - 16).
    zstep. br_cases K2.
    + c36_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(left) ltac:(lia).
    + c36_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(right) ltac:(lia).
Qed.

Ltac x_fin MU WM GA GD Gpend DEC LO :=
  apply evt_done; unfold ust_tail_post, ustR, sbF_PB, sbF_PD, sbF_BB, sbF_BV; DEC; do 11 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [close_EM GA GD Gpend|]; split; [LO|];
  first [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]].

Lemma st_x36_keep : forall (L : dlay) (s : deflate_state) (T mc n nextlen curlen cnt : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (x1 x9 x18 x19 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  0 <= BV <= 14 -> 0 <= PD -> 0 <= nextlen < 65536 -> 0 <= cnt < 2^31 ->
  evt usegs (ust_tail_post L s T mc n nextlen curlen (sbF_PB PB PD BB BV (cnt - 3) 2) (sbF_PD PD BV 2) (sbF_BB BB BV (cnt - 3) 2) (sbF_BV BV 2) sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 (wz BV) x9 x18 x19 (wz curlen) (wz cnt) (wz BV) w x27 sp gp tp) F (wz 0x1ea30) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY RBV RPD Rnl Rcnt. unfold ustR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  ustep ST_TRAP. zs2. zs2. zs2. zs2.
  sb_or w1 LO BB (exact HW). rewrite (nbv_eqm BB BV (cnt - 3) (65535 + cnt + -2) (cnt36_eqm cnt)) in LO.
  zstep. zs2. zstep. zs2.
  zstep. br_cases K.
  - x_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 2) BV)) by lia) ltac:(exact LO).
  - zstep. x_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 2) BV)) by lia) ltac:(exact LO).
Qed.

Lemma st_x36_flush : forall (L : dlay) (s : deflate_state) (T mc n nextlen curlen cnt : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (x1 x9 x18 x19 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  15 <= BV <= 16 -> 0 <= PD -> PD + 2 <= 65536 -> 0 <= nextlen < 65536 -> 3 <= cnt < 32768 ->
  evt usegs (ust_tail_post L s T mc n nextlen curlen (sbF_PB PB PD BB BV (cnt - 3) 2) (sbF_PD PD BV 2) (sbF_BB BB BV (cnt - 3) 2) (sbF_BV BV 2) sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 (wz BV) x9 x18 x19 (wz curlen) (wz cnt) (wz BV) w x27 sp gp tp) F (wz 0x1e954) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY RBV RPD ROOM Rnl Rcnt. unfold ustR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  ustep ST_TRAP. zs2. zs2. zs2. replace (65535 + cnt + -2) with (65535 + (cnt - 3 + 3) + -2) by lia. rewrite (land16_x (cnt - 3)) by lia.
  zs2. zs2. shl_g0. ustep ST_TRAP.
  zs. zs. zs. zs.
  sb_or w1 LO BB (exact HW).
  replace (65535 + (cnt - 3 + 3) + -2) with (65535 + cnt + -2) in LO by lia. rewrite (nbv_eqm BB BV (cnt - 3) (65535 + cnt + -2) (cnt36_eqm cnt)) in LO.
  zs. zs. zstep. zs.
  uwalk 0x1e9a8 ST_TRAP. at_pc 0x1e9a8.
  pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV (cnt - 3)) 255)) ltac:(apply lo8_wrap8_land; exact LO).
  zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
  uwalk 0x1e9dc ST_TRAP. at_pc 0x1e9dc.
  pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV (cnt - 3)) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV (cnt - 3))) 8)) ltac:(apply hi8_lo16; exact LO).
  uwalk 0x1e9f8 ST_TRAP. at_pc 0x1e9f8.
  zs2. rewrite srlw_val16 by lia.
  pose proof (shiftr_wrap16_range (cnt - 3) (16 - BV) ltac:(lia)) as RSH.
  zs2. zstep. zstep. br_true. zstep. zs2. reg_as (BV + -14) (BV + 2 - 16).
  zstep. br_cases K.
  - x_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 2) BV)) by lia) ltac:(apply lo16_unsigned_wz).
  - x_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 2) BV)) by lia) ltac:(apply lo16_unsigned_wz).
Qed.

Lemma st_rep36 : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc n nextlen curlen cnt V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (x1 x8 x9 x18 x19 x25 x26 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc 16 -> l = arr_get bdl 16 ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 ->
  0 <= V < 32768 -> 0 <= BV <= 16 -> 0 <= PD -> 3 <= cnt < 32768 -> 0 <= nextlen < 65536 ->
  sbs_ok 65536 (upd4 s PB PD BB BV) [(V, l); (cnt - 3, 2)] ->
  evt usegs (ust_tail_post L s T mc n nextlen curlen
               (sbF_PB (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) (cnt - 3) 2) (sbF_PD (sbF_PD PD BV l) (sbF_BV BV l) 2)
               (sbF_BB (sbF_BB BB BV V l) (sbF_BV BV l) (cnt - 3) 2) (sbF_BV (sbF_BV BV l) 2) sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 x8 x9 x18 x19 (wz curlen) (wz cnt) x25 x26 x27 sp gp tp) F (wz 0x1e874) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDB RV RBV RPD Rcnt Rnl HSB.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (Rl & ROOM & HSB2). apply sbs_ok_cons_flat in HSB2. destruct HSB2 as (_ & ROOM2 & _).
  pose proof (sbF_BV_range BV l RBV Rl) as RBV1. pose proof (sbF_PD_range PD BV l RPD) as RPD1.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  call (st_c36 L s bfc bdl T mc n nextlen curlen cnt V l PB PD BB BV wbb).
  1:{ exact EV. } 1:{ exact El. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDB. } 1:{ exact RV. } 1:{ exact Rl. }
  1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. }
  match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end.
  - eapply evt_mono; [eapply (st_x36_keep L s T mc n nextlen curlen cnt); try eassumption; lia|].
    intros ms' (r1 & r8 & r9 & r18 & r19 & r24 & r26 & r27 & wb & pcx & m' & E & MU' & WM' & MI' & EM' & HB' & X').
    unfold ust_tail_post. exists r1, r8, r9, r18, r19, r24, r26, r27, wb, pcx, m'.
    split; [exact E|]. split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact EM'|]. split; [exact HB'| exact X'].
  - eapply evt_mono; [eapply (st_x36_flush L s T mc n nextlen curlen cnt); try eassumption; lia|].
    intros ms' (r1 & r8 & r9 & r18 & r19 & r24 & r26 & r27 & wb & pcx & m' & E & MU' & WM' & MI' & EM' & HB' & X').
    unfold ust_tail_post. exists r1, r8, r9, r18, r19, r24, r26, r27, wb, pcx, m'.
    split; [exact E|]. split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact EM'|]. split; [exact HB'| exact X'].
Qed.
End Z_tr_st3.


Module Z_tr_st5.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_cb4 Z_tr_st4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.Z_tr_st1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.Z_tr_st3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Lemma cnt10_eqm : forall cnt, (65535 + cnt + -1) mod 2^16 = (cnt - 2) mod 2^16.
Proof. intros. replace (65535 + cnt + -1) with (cnt - 2 + 1 * 2^16) by lia. apply Z.mod_add. lia. Qed.
Lemma land16_c10 : forall cnt, 2 <= cnt < 65538 -> Z.land (65535 + cnt + -1) 65535 = cnt - 2.
Proof. intros cnt H. replace (65535 + cnt + -1) with (65535 + (cnt - 2 + 3) + -2) by lia. apply land16_x. lia. Qed.

Definition ust_c10_post (L : dlay) (s : deflate_state) (T mc n nextlen curlen cnt : Z) (PB : arr) (PD BB BV : Z)
    (x1 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists w x9 x18 x19 x27 pcx m',
    ms' = MS (ustR L T mc n nextlen x1 (wz BV) x9 x18 x19 (wz curlen) (wz cnt) (wz BV) w x27 sp gp tp) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1ea9c /\ BV <= 13) \/ (pcx = 0x1e518 /\ 14 <= BV)).

Ltac c10_fin MU WM GA GD Gpend DEC LO side EXT :=
  apply evt_done; unfold ust_c10_post, ustR, sbF_PB, sbF_PD, sbF_BB, sbF_BV; DEC; do 7 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
  split; [close_EM GA GD Gpend|]; split; [LO|]; side; (split; [reflexivity| EXT]).

Lemma st_c10 : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc n nextlen curlen cnt V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (x1 x8 x9 x18 x19 x25 x26 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc 17 -> l = arr_get bdl 17 ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 ->
  0 <= V < 32768 -> 0 <= l <= 16 -> 0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt usegs (ust_c10_post L s T mc n nextlen curlen cnt (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) x1 sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 x8 x9 x18 x19 (wz curlen) (wz cnt) x25 x26 x27 sp gp tp) F (wz 0x1e42c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDB RV Rl RBV RPD ROOM. unfold ustR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDB m (munch_refl _ _) (wmono_refl _ _) MI 17 ltac:(lia)) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  clear EV El.
  ustep ST_TRAP. zs2. ustep ST_TRAP.
  zs. rewrite (zx16_small l) by lia. zs2. zs2.
  zstep. br_cases K.
  -
    zs2. ustep ST_TRAP. ustep ST_TRAP. zs. rewrite (zx16_small V) by lia. zs2. zs2. shl_g0. ustep ST_TRAP.
    zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zstep. zs2. zs2. zstep. zs2.
    zstep. br_cases K2.
    + c10_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia) ltac:(exact LO) ltac:(right) ltac:(lia).
    + c10_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia) ltac:(exact LO) ltac:(left) ltac:(lia).
  -
    zs2. ustep ST_TRAP. ustep ST_TRAP. zs. rewrite (zx16_small V) by lia. zs2. zs2. shl_g0. ustep ST_TRAP.
    zs. zs. zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zs. zs. zstep. zs.
    uwalk 0x1e4a0 ST_TRAP. at_pc 0x1e4a0.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1e4d4 ST_TRAP. at_pc 0x1e4d4.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1e4f0 ST_TRAP. at_pc 0x1e4f0.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
    zs2. zs2. zs2. zstep. ustep ST_TRAP. zs2. zstep. reg_as (l + BV + -16) (BV + l - 16). zs2.
    zstep. br_cases K2.
    + c10_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(left) ltac:(lia).
    + c10_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(right) ltac:(lia).
Qed.

Lemma st_x10_keep : forall (L : dlay) (s : deflate_state) (T mc n nextlen curlen cnt : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (x1 x9 x18 x19 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  0 <= BV <= 13 -> 0 <= PD -> 0 <= nextlen < 65536 -> 0 <= cnt < 2^31 ->
  evt usegs (ust_tail_post L s T mc n nextlen curlen (sbF_PB PB PD BB BV (cnt - 2) 3) (sbF_PD PD BV 3) (sbF_BB BB BV (cnt - 2) 3) (sbF_BV BV 3) sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 (wz BV) x9 x18 x19 (wz curlen) (wz cnt) (wz BV) w x27 sp gp tp) F (wz 0x1ea9c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY RBV RPD Rnl Rcnt. unfold ustR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  ustep ST_TRAP. zs2. zs2. zs2. zs2.
  sb_or w1 LO BB (exact HW). rewrite (nbv_eqm BB BV (cnt - 2) (65535 + cnt + -1) (cnt10_eqm cnt)) in LO.
  zstep. zs2. zstep. zs2.
  zstep. br_cases K.
  - x_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 3) BV)) by lia) ltac:(exact LO).
  - x_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 3) BV)) by lia) ltac:(exact LO).
Qed.

Lemma st_x10_flush : forall (L : dlay) (s : deflate_state) (T mc n nextlen curlen cnt : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (x1 x9 x18 x19 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  14 <= BV <= 16 -> 0 <= PD -> PD + 2 <= 65536 -> 0 <= nextlen < 65536 -> 2 <= cnt < 32768 ->
  evt usegs (ust_tail_post L s T mc n nextlen curlen (sbF_PB PB PD BB BV (cnt - 2) 3) (sbF_PD PD BV 3) (sbF_BB BB BV (cnt - 2) 3) (sbF_BV BV 3) sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 (wz BV) x9 x18 x19 (wz curlen) (wz cnt) (wz BV) w x27 sp gp tp) F (wz 0x1e518) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY RBV RPD ROOM Rnl Rcnt. unfold ustR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  ustep ST_TRAP. zs2. zs2. zs2. rewrite land16_c10 by lia.
  zs2. zs2. shl_g0. ustep ST_TRAP.
  zs. zs. zs. zs.
  sb_or w1 LO BB (exact HW). rewrite (nbv_eqm BB BV (cnt - 2) (65535 + cnt + -1) (cnt10_eqm cnt)) in LO.
  zs. zs. zstep. zs.
  uwalk 0x1e56c ST_TRAP. at_pc 0x1e56c.
  pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV (cnt - 2)) 255)) ltac:(apply lo8_wrap8_land; exact LO).
  zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
  uwalk 0x1e5a0 ST_TRAP. at_pc 0x1e5a0.
  pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV (cnt - 2)) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV (cnt - 2))) 8)) ltac:(apply hi8_lo16; exact LO).
  uwalk 0x1e5bc ST_TRAP. at_pc 0x1e5bc.
  zs2. rewrite srlw_val16 by lia.
  pose proof (shiftr_wrap16_range (cnt - 2) (16 - BV) ltac:(lia)) as RSH.
  zs2. zstep. zstep. zstep. br_true. zstep. zs2. reg_as (BV + -13) (BV + 3 - 16).
  zstep. br_cases K.
  - x_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 3) BV)) by lia) ltac:(apply lo16_unsigned_wz).
  - x_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 3) BV)) by lia) ltac:(apply lo16_unsigned_wz).
Qed.

Lemma st_repz10 : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc n nextlen curlen cnt V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (x1 x8 x9 x18 x19 x25 x26 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc 17 -> l = arr_get bdl 17 ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 ->
  0 <= V < 32768 -> 0 <= BV <= 16 -> 0 <= PD -> 2 <= cnt < 32768 -> 0 <= nextlen < 65536 ->
  sbs_ok 65536 (upd4 s PB PD BB BV) [(V, l); (cnt - 2, 3)] ->
  evt usegs (ust_tail_post L s T mc n nextlen curlen
               (sbF_PB (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) (cnt - 2) 3) (sbF_PD (sbF_PD PD BV l) (sbF_BV BV l) 3)
               (sbF_BB (sbF_BB BB BV V l) (sbF_BV BV l) (cnt - 2) 3) (sbF_BV (sbF_BV BV l) 3) sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 x8 x9 x18 x19 (wz curlen) (wz cnt) x25 x26 x27 sp gp tp) F (wz 0x1e42c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDB RV RBV RPD Rcnt Rnl HSB.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (Rl & ROOM & HSB2). apply sbs_ok_cons_flat in HSB2. destruct HSB2 as (_ & ROOM2 & _).
  pose proof (sbF_BV_range BV l RBV Rl) as RBV1. pose proof (sbF_PD_range PD BV l RPD) as RPD1.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  call (st_c10 L s bfc bdl T mc n nextlen curlen cnt V l PB PD BB BV wbb).
  1:{ exact EV. } 1:{ exact El. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDB. } 1:{ exact RV. } 1:{ exact Rl. }
  1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. }
  match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end.
  - eapply evt_mono; [eapply (st_x10_keep L s T mc n nextlen curlen cnt); try eassumption; lia|].
    intros ms' (r1 & r8 & r9 & r18 & r19 & r24 & r26 & r27 & wb & pcx & m' & E & MU' & WM' & MI' & EM' & HB' & X').
    unfold ust_tail_post. exists r1, r8, r9, r18, r19, r24, r26, r27, wb, pcx, m'.
    split; [exact E|]. split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact EM'|]. split; [exact HB'| exact X'].
  - eapply evt_mono; [eapply (st_x10_flush L s T mc n nextlen curlen cnt); try eassumption; lia|].
    intros ms' (r1 & r8 & r9 & r18 & r19 & r24 & r26 & r27 & wb & pcx & m' & E & MU' & WM' & MI' & EM' & HB' & X').
    unfold ust_tail_post. exists r1, r8, r9, r18, r19, r24, r26, r27, wb, pcx, m'.
    split; [exact E|]. split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact EM'|]. split; [exact HB'| exact X'].
Qed.
End Z_tr_st5.


Module Z_tr_st6.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_cb4 Z_tr_st4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.Z_tr_st1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.Z_tr_st3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.Z_tr_st5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Lemma cnt138_eqm : forall cnt, (65535 + cnt + -9) mod 2^16 = (cnt - 10) mod 2^16.
Proof. intros. replace (65535 + cnt + -9) with (cnt - 10 + 1 * 2^16) by lia. apply Z.mod_add. lia. Qed.
Lemma land16_c138 : forall cnt, 10 <= cnt < 65546 -> Z.land (65535 + cnt + -9) 65535 = cnt - 10.
Proof. intros cnt H. replace (65535 + cnt + -9) with (65535 + (cnt - 10 + 3) + -2) by lia. apply land16_x. lia. Qed.

Definition ust_c138_post (L : dlay) (s : deflate_state) (T mc n nextlen curlen cnt : Z) (PB : arr) (PD BB BV : Z)
    (x1 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists w x9 x18 x19 x27 pcx m',
    ms' = MS (ustR L T mc n nextlen x1 (wz BV) x9 x18 x19 (wz curlen) (wz cnt) (wz BV) w x27 sp gp tp) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1eaf4 /\ BV <= 9) \/ (pcx = 0x1e794 /\ 10 <= BV)).

Ltac c138_fin MU WM GA GD Gpend DEC LO side EXT :=
  apply evt_done; unfold ust_c138_post, ustR, sbF_PB, sbF_PD, sbF_BB, sbF_BV; DEC; do 7 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
  split; [close_EM GA GD Gpend|]; split; [LO|]; side; (split; [reflexivity| EXT]).

Lemma st_c138 : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc n nextlen curlen cnt V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (x1 x8 x9 x18 x19 x25 x26 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc 18 -> l = arr_get bdl 18 ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 ->
  0 <= V < 32768 -> 0 <= l <= 16 -> 0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt usegs (ust_c138_post L s T mc n nextlen curlen cnt (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) x1 sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 x8 x9 x18 x19 (wz curlen) (wz cnt) x25 x26 x27 sp gp tp) F (wz 0x1e6ac) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDB RV Rl RBV RPD ROOM. unfold ustR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDB m (munch_refl _ _) (wmono_refl _ _) MI 18 ltac:(lia)) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  clear EV El.
  ustep ST_TRAP. zs2. ustep ST_TRAP.
  zs. rewrite (zx16_small l) by lia. zs2. zs. rewrite (zx16_small V) by lia.
  do 4 zs2. shl_g0. zs2. zs2. shl_g1.
  zstep. br_cases K.
  -
    ustep ST_TRAP. zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zstep. zs2. zs2. zstep.
    zstep. br_cases K2.
    + c138_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia) ltac:(exact LO) ltac:(right) ltac:(lia).
    + c138_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia) ltac:(exact LO) ltac:(left) ltac:(lia).
  -
    ustep ST_TRAP. zs. zs. zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zs. zs. zstep. zs.
    uwalk 0x1e720 ST_TRAP. at_pc 0x1e720.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1e754 ST_TRAP. at_pc 0x1e754.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1e770 ST_TRAP. at_pc 0x1e770.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
    zs2. zs2. zs2. zstep. ustep ST_TRAP. zs2. zstep. reg_as (l + BV + -16) (BV + l - 16).
    zstep. br_cases K2.
    + c138_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(left) ltac:(lia).
    + c138_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(right) ltac:(lia).
Qed.

Lemma st_x138_keep : forall (L : dlay) (s : deflate_state) (T mc n nextlen curlen cnt : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (x1 x9 x18 x19 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  0 <= BV <= 9 -> 0 <= PD -> 0 <= nextlen < 65536 -> 0 <= cnt < 2^31 ->
  evt usegs (ust_tail_post L s T mc n nextlen curlen (sbF_PB PB PD BB BV (cnt - 10) 7) (sbF_PD PD BV 7) (sbF_BB BB BV (cnt - 10) 7) (sbF_BV BV 7) sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 (wz BV) x9 x18 x19 (wz curlen) (wz cnt) (wz BV) w x27 sp gp tp) F (wz 0x1eaf4) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY RBV RPD Rnl Rcnt. unfold ustR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  ustep ST_TRAP. zs2. zs2. zs2. zs2.
  sb_or w1 LO BB (exact HW). rewrite (nbv_eqm BB BV (cnt - 10) (65535 + cnt + -9) (cnt138_eqm cnt)) in LO.
  zstep. zs2. zstep. zs2.
  zstep. br_cases K.
  - x_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 7) BV)) by lia) ltac:(exact LO).
  - zstep. x_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 7) BV)) by lia) ltac:(exact LO).
Qed.

Lemma st_x138_flush : forall (L : dlay) (s : deflate_state) (T mc n nextlen curlen cnt : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (x1 x9 x18 x19 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  10 <= BV <= 16 -> 0 <= PD -> PD + 2 <= 65536 -> 0 <= nextlen < 65536 -> 10 <= cnt < 32768 ->
  evt usegs (ust_tail_post L s T mc n nextlen curlen (sbF_PB PB PD BB BV (cnt - 10) 7) (sbF_PD PD BV 7) (sbF_BB BB BV (cnt - 10) 7) (sbF_BV BV 7) sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 (wz BV) x9 x18 x19 (wz curlen) (wz cnt) (wz BV) w x27 sp gp tp) F (wz 0x1e794) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY RBV RPD ROOM Rnl Rcnt. unfold ustR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  ustep ST_TRAP. zs2. zs2. zs2. rewrite land16_c138 by lia.
  zs2. zs2. shl_g0. ustep ST_TRAP.
  zs. zs. zs. zs.
  sb_or w1 LO BB (exact HW). rewrite (nbv_eqm BB BV (cnt - 10) (65535 + cnt + -9) (cnt138_eqm cnt)) in LO.
  zs. zs. zstep. zs.
  uwalk 0x1e7e8 ST_TRAP. at_pc 0x1e7e8.
  pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV (cnt - 10)) 255)) ltac:(apply lo8_wrap8_land; exact LO).
  zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
  uwalk 0x1e81c ST_TRAP. at_pc 0x1e81c.
  pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV (cnt - 10)) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV (cnt - 10))) 8)) ltac:(apply hi8_lo16; exact LO).
  uwalk 0x1e838 ST_TRAP. at_pc 0x1e838.
  zs2. rewrite srlw_val16 by lia.
  pose proof (shiftr_wrap16_range (cnt - 10) (16 - BV) ltac:(lia)) as RSH.
  zs2. zstep. zstep. zstep. br_true. zstep. zs2. reg_as (BV + -9) (BV + 7 - 16).
  zstep. br_cases K.
  - x_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 7) BV)) by lia) ltac:(apply lo16_unsigned_wz).
  - x_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 7) BV)) by lia) ltac:(apply lo16_unsigned_wz).
Qed.

Lemma st_repz138 : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc n nextlen curlen cnt V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (x1 x8 x9 x18 x19 x25 x26 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc 18 -> l = arr_get bdl 18 ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 ->
  0 <= V < 32768 -> 0 <= BV <= 16 -> 0 <= PD -> 10 <= cnt < 32768 -> 0 <= nextlen < 65536 ->
  sbs_ok 65536 (upd4 s PB PD BB BV) [(V, l); (cnt - 10, 7)] ->
  evt usegs (ust_tail_post L s T mc n nextlen curlen
               (sbF_PB (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) (cnt - 10) 7) (sbF_PD (sbF_PD PD BV l) (sbF_BV BV l) 7)
               (sbF_BB (sbF_BB BB BV V l) (sbF_BV BV l) (cnt - 10) 7) (sbF_BV (sbF_BV BV l) 7) sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 x8 x9 x18 x19 (wz curlen) (wz cnt) x25 x26 x27 sp gp tp) F (wz 0x1e6ac) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDB RV RBV RPD Rcnt Rnl HSB.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (Rl & ROOM & HSB2). apply sbs_ok_cons_flat in HSB2. destruct HSB2 as (_ & ROOM2 & _).
  pose proof (sbF_BV_range BV l RBV Rl) as RBV1. pose proof (sbF_PD_range PD BV l RPD) as RPD1.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  call (st_c138 L s bfc bdl T mc n nextlen curlen cnt V l PB PD BB BV wbb).
  1:{ exact EV. } 1:{ exact El. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDB. } 1:{ exact RV. } 1:{ exact Rl. }
  1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. }
  match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end.
  - eapply evt_mono; [eapply (st_x138_keep L s T mc n nextlen curlen cnt); try eassumption; lia|].
    intros ms' (r1 & r8 & r9 & r18 & r19 & r24 & r26 & r27 & wb & pcx & m' & E & MU' & WM' & MI' & EM' & HB' & X').
    unfold ust_tail_post. exists r1, r8, r9, r18, r19, r24, r26, r27, wb, pcx, m'.
    split; [exact E|]. split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact EM'|]. split; [exact HB'| exact X'].
  - eapply evt_mono; [eapply (st_x138_flush L s T mc n nextlen curlen cnt); try eassumption; lia|].
    intros ms' (r1 & r8 & r9 & r18 & r19 & r24 & r26 & r27 & wb & pcx & m' & E & MU' & WM' & MI' & EM' & HB' & X').
    unfold ust_tail_post. exists r1, r8, r9, r18, r19, r24, r26, r27, wb, pcx, m'.
    split; [exact E|]. split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact EM'|]. split; [exact HB'| exact X'].
Qed.
End Z_tr_st6.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_scan1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.Z_tr_st1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.Z_tr_st2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.Z_tr_st3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.Z_tr_st5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.Z_tr_st6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_scan1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Lemma st_step_keep : forall f X t mc n prevlen nextlen count mx mn,
  1 <= mn -> n <= mc -> count + 1 < mx -> nextlen = Len X t (n + 1) ->
  send_tree_loop (S f) X t mc n prevlen nextlen count mx mn = send_tree_loop f X t mc (n + 1) prevlen (Len X t (n + 1)) (count + 1) mx mn.
Proof.
  intros f X t mc n prevlen nextlen count mx mn Hmn Hn Hc E. rewrite send_loop_S by exact Hmn. cbv zeta.
  rewrite (proj2 (Z.leb_le _ _) Hn), (proj2 (Z.ltb_lt _ _) Hc), (proj2 (Z.eqb_eq _ _) E). reflexivity.
Qed.
Lemma st_step_emit : forall f X t mc n prevlen nextlen count mx mn,
  1 <= mn -> n <= mc -> (mx <= count + 1 \/ nextlen <> Len X t (n + 1)) ->
  send_tree_loop (S f) X t mc n prevlen nextlen count mx mn
  = send_tree_loop f (sbs_run X (st_calls X mn nextlen prevlen (count + 1))) t mc (n + 1) nextlen (Len X t (n + 1)) 0
      (fst (tree_counts nextlen (Len X t (n + 1)))) (snd (tree_counts nextlen (Len X t (n + 1)))).
Proof.
  intros f X t mc n prevlen nextlen count mx mn Hmn Hn Hc. rewrite send_loop_S by exact Hmn. cbv zeta.
  rewrite (proj2 (Z.leb_le _ _) Hn).
  replace ((count + 1 <? mx) && (nextlen =? Len X t (n + 1))) with false.
  2:{ symmetry. apply andb_false_iff. destruct Hc as [Hc|Hc]; [left; apply Z.ltb_ge; exact Hc| right; apply Z.eqb_neq; exact Hc]. }
  destruct (tree_counts nextlen (Len X t (n + 1))); reflexivity.
Qed.
Lemma st_ok_keep : forall P f X t mc n prevlen nextlen count mx mn,
  n <= mc -> count + 1 < mx -> nextlen = Len X t (n + 1) ->
  send_tree_ok P (S f) X t mc n prevlen nextlen count mx mn -> send_tree_ok P f X t mc (n + 1) prevlen (Len X t (n + 1)) (count + 1) mx mn.
Proof.
  intros P f X t mc n prevlen nextlen count mx mn Hn Hc E H. cbn [send_tree_ok] in H. cbv zeta in H.
  rewrite (proj2 (Z.leb_le _ _) Hn), (proj2 (Z.ltb_lt _ _) Hc), (proj2 (Z.eqb_eq _ _) E) in H. exact H.
Qed.
Lemma st_ok_emit : forall P f X t mc n prevlen nextlen count mx mn,
  n <= mc -> (mx <= count + 1 \/ nextlen <> Len X t (n + 1)) ->
  send_tree_ok P (S f) X t mc n prevlen nextlen count mx mn ->
  sbs_ok P X (st_calls X mn nextlen prevlen (count + 1))
  /\ send_tree_ok P f (sbs_run X (st_calls X mn nextlen prevlen (count + 1))) t mc (n + 1) nextlen (Len X t (n + 1)) 0
       (fst (tree_counts nextlen (Len X t (n + 1)))) (snd (tree_counts nextlen (Len X t (n + 1)))).
Proof.
  intros P f X t mc n prevlen nextlen count mx mn Hn Hc H. cbn [send_tree_ok] in H. cbv zeta in H.
  rewrite (proj2 (Z.leb_le _ _) Hn) in H.
  replace ((count + 1 <? mx) && (nextlen =? Len X t (n + 1))) with false in H.
  2:{ symmetry. apply andb_false_iff. destruct Hc as [Hc|Hc]; [left; apply Z.ltb_ge; exact Hc| right; apply Z.eqb_neq; exact Hc]. }
  destruct (tree_counts nextlen (Len X t (n + 1))); exact H.
Qed.
Lemma tree_counts_0 : forall c, tree_counts c 0 = (138, 3).
Proof. reflexivity. Qed.
Lemma tree_counts_nz : forall c n, n <> 0 -> tree_counts c n = (if c =? n then 6 else 7, if c =? n then 3 else 4).
Proof. intros c n H. unfold tree_counts. rewrite (proj2 (Z.eqb_neq _ _) H). destruct (c =? n); reflexivity. Qed.
Lemma blc_flat : forall s PB PD BB BV c, blc (upd4 s PB PD BB BV) c = (arr_get (ds_bl_tree_fc s) c, arr_get (ds_bl_tree_dl s) c).
Proof. intros. unfold blc, Code, Len. rewrite upd4_tree_fc, upd4_tree_dl. reflexivity. Qed.
Lemma sbF_PD_nonneg : forall PD BV l, 0 <= PD -> 0 <= sbF_PD PD BV l.
Proof. intros PD BV l H. pose proof (sbF_PD_range PD BV l H). lia. Qed.

Definition ust_trip_post (L : dlay) (s : deflate_state) (t : tree_id) (T mc n1 nextlen' : Z) (f : nat) (R : deflate_state)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists x8 x9 x18 x19 wbb PB' PD' BB' BV' prevlen' count' mx' mn' pcx m',
    ms' = MS (ustR L T mc n1 nextlen' (wz prevlen') x8 x9 x18 x19 (wz prevlen') (wz count') (wz count') (wz mx') (wz mn') sp gp tp)
             F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ EM m' L s PB' PD' wbb (wz BV') /\ bv_unsigned wbb mod 2^16 = BB' mod 2^16
    /\ R = send_tree_loop f (upd4 s PB' PD' BB' BV') t mc n1 prevlen' nextlen' count' mx' mn'
    /\ send_tree_ok 65536 f (upd4 s PB' PD' BB' BV') t mc n1 prevlen' nextlen' count' mx' mn'
    /\ 0 <= BV' <= 16 /\ 0 <= PD' /\ 0 <= count' < mx' /\ (mx' = 138 \/ mx' = 6 \/ mx' = 7) /\ (mn' = 3 \/ mn' = 4)
    /\ -1 <= prevlen' <= 15 /\ (mn' = 4 \/ prevlen' = nextlen' \/ nextlen' = 0)
    /\ ((pcx = ST_BODY /\ n1 <= mc) \/ (pcx = ST_EXIT /\ n1 = mc + 1)).

Lemma st_latch : forall (L : dlay) (s : deflate_state) (t : tree_id) (T mc n1 nextlen' : Z) (f : nat) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV prevlen' count' mx' mn' : Z) (wbb : word)
    (x1 x8 x9 x18 x19 x24 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m ->
  munch (Wem L) m0 m -> wmono usegs m0 m ->
  R = send_tree_loop f (upd4 s PB PD BB BV) t mc n1 prevlen' nextlen' count' mx' mn' ->
  send_tree_ok 65536 f (upd4 s PB PD BB BV) t mc n1 prevlen' nextlen' count' mx' mn' ->
  0 <= BV <= 16 -> 0 <= PD -> 0 <= count' < mx' -> (mx' = 138 \/ mx' = 6 \/ mx' = 7) -> (mn' = 3 \/ mn' = 4) -> -1 <= prevlen' <= 15 ->
  (mn' = 4 \/ prevlen' = nextlen' \/ nextlen' = 0) ->
  0 <= n1 <= mc + 1 -> mc + 1 < 2^31 ->
  evt usegs (ust_trip_post L s t T mc n1 nextlen' f R sp gp tp F fc m0)
      (MS (ustR L T mc n1 nextlen' x1 x8 x9 x18 x19 (wz prevlen') x24 (wz count') (wz mx') (wz mn') sp gp tp) F (wz ST_LATCH) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HBB MI MU WM ER OK RBV RPD Rc Rmx Rmn Rpl INV Rn Rmc. unfold ustR, ST_LATCH.
  zs2. zs2. zstep. br_cases K.
  - apply evt_done. unfold ust_trip_post, ustR. exists x8, x9, x18, x19, wbb, PB, PD, BB, BV, prevlen', count', mx', mn'. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact EMH|]. split; [exact HBB|].
    split; [exact ER|]. split; [exact OK|]. split; [exact RBV|]. split; [exact RPD|]. split; [exact Rc|].
    split; [exact Rmx|]. split; [exact Rmn|]. split; [exact Rpl|]. split; [exact INV|]. right. split; [reflexivity| lia].
  - apply evt_done. unfold ust_trip_post, ustR. exists x8, x9, x18, x19, wbb, PB, PD, BB, BV, prevlen', count', mx', mn'. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact EMH|]. split; [exact HBB|].
    split; [exact ER|]. split; [exact OK|]. split; [exact RBV|]. split; [exact RPD|]. split; [exact Rc|].
    split; [exact Rmx|]. split; [exact Rmn|]. split; [exact Rpl|]. split; [exact INV|]. left. split; [reflexivity| lia].
Qed.

Lemma st_tail : forall (L : dlay) (s : deflate_state) (t : tree_id) (T mc n1 curlen nextlen' : Z) (f : nat) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV pcx : Z) (wbb : word)
    (x1 x8 x9 x18 x19 x24 x26 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m ->
  munch (Wem L) m0 m -> wmono usegs m0 m ->
  R = send_tree_loop f (upd4 s PB PD BB BV) t mc n1 curlen nextlen' 0 (fst (tree_counts curlen nextlen')) (snd (tree_counts curlen nextlen')) ->
  send_tree_ok 65536 f (upd4 s PB PD BB BV) t mc n1 curlen nextlen' 0 (fst (tree_counts curlen nextlen')) (snd (tree_counts curlen nextlen')) ->
  0 <= BV <= 16 -> 0 <= PD -> 0 <= curlen <= 15 -> 0 <= nextlen' < 65536 -> 0 <= n1 <= mc + 1 -> mc + 1 < 2^31 ->
  ((pcx = ST_TAIL /\ nextlen' <> 0) \/ (pcx = ST_T138 /\ nextlen' = 0)) ->
  evt usegs (ust_trip_post L s t T mc n1 nextlen' f R sp gp tp F fc m0)
      (MS (ustR L T mc n1 nextlen' x1 x8 x9 x18 x19 (wz curlen) x24 (wz 0) x26 x27 sp gp tp) F (wz pcx) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HBB MI MU WM ER OK RBV RPD Rcl Rnl Rn Rmc [[-> NZ]|[-> ZE]]; unfold ustR, ST_TAIL, ST_T138.
  - rewrite tree_counts_nz in ER, OK by exact NZ. cbn [fst snd] in ER, OK.
    do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn.
    eapply (st_latch L s t T mc n1 nextlen' f R m0 PB PD BB BV curlen 0 (if curlen =? nextlen' then 6 else 7) (if curlen =? nextlen' then 3 else 4) wbb);
      try eassumption; try lia; destruct (Z.eqb_spec curlen nextlen'); auto; lia.
  - subst nextlen'. rewrite tree_counts_0 in ER, OK. cbn [fst snd] in ER, OK.
    do 3 zs2.
    eapply (st_latch L s t T mc n1 0 f R m0 PB PD BB BV curlen 0 138 3 wbb); try eassumption; try lia; auto.
Qed.

Ltac st_fin L s t T mc n1 curlen nextlen' f R m0 MU WM ER OK2 :=
  match goal with H : EM ?mm _ _ ?pb ?pd ?wb (wz ?bv), HB : bv_unsigned ?wb mod _ = ?bb mod _, HP : (_ /\ _) \/ (_ /\ _) |- evt _ _ (MS _ _ (wz ?pcx) _ _ ?mm _) =>
    eapply (st_tail L s t T mc n1 curlen nextlen' f R m0 pb pd bb bv pcx wb); [exact H| exact HB| eassumption| exact MU| exact WM| exact ER| exact OK2| | | | | | | exact HP] end.

Lemma st_emit : forall (L : dlay) (s : deflate_state) (t : tree_id) (bfc bdl : arr) (T mc n1 : Z) (f : nat) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV prevlen curlen nextlen' count mx mn : Z) (wbb : word)
    (x8 x9 x18 x19 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono usegs m0 m ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> bfc = ds_bl_tree_fc s -> bdl = ds_bl_tree_dl s ->
  (forall i, 0 <= i < 19 -> 0 <= arr_get bfc i < 32768) ->
  0 <= curlen <= 15 -> 0 <= nextlen' < 65536 -> 0 <= n1 <= mc + 1 -> mc + 1 < 2^31 ->
  0 <= BV <= 16 -> 0 <= PD -> 0 <= count < 138 -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  (mn = 4 \/ prevlen = curlen \/ curlen = 0) ->
  R = send_tree_loop f (sbs_run (upd4 s PB PD BB BV) (st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1))) t mc n1 curlen nextlen' 0
        (fst (tree_counts curlen nextlen')) (snd (tree_counts curlen nextlen')) ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1)) ->
  send_tree_ok 65536 f (sbs_run (upd4 s PB PD BB BV) (st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1))) t mc n1 curlen nextlen' 0
        (fst (tree_counts curlen nextlen')) (snd (tree_counts curlen nextlen')) ->
  evt usegs (ust_trip_post L s t T mc n1 nextlen' f R sp gp tp F fc m0)
      (MS (ustR L T mc n1 nextlen' (wz prevlen) x8 x9 x18 x19 (wz curlen) (wz count) (wz (count + 1)) (wz mx) (wz mn) sp gp tp) F (wz 0x1e2dc) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HBB MI LAY MU WM RDB Ebfc Ebdl RBf Rcl Rnl Rn Rmc RBV RPD Rc Rmn Rpl INV ER OK1 OK2.
  assert (RDBm : ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39) by (eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]).
  pose proof LAY as LAY'. lay_open LAY'.
  unfold ustR. zstep. br_cases K1.
  -
    zstep. br_cases_s K2.
    +
      zstep. br_cases K5.
      *
        assert (ESC : st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1) = [(arr_get bfc 18, arr_get bdl 18); (count - 10, 7)]).
        { unfold st_calls, REPZ_11_138. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq curlen 0)) by lia.
          rewrite (proj2 (Z.leb_gt _ _)) by lia. cbn [negb]. rewrite blc_flat, <- Ebfc, <- Ebdl. replace (count + 1 - 11) with (count - 10) by lia. reflexivity. }
        rewrite ESC in ER, OK1, OK2. clear ESC. rewrite !sbs_run_cons_flat in ER, OK2. cbn [sbs_run] in ER, OK2.
        pose proof OK1 as OKc. apply sbs_ok_cons_flat in OKc. destruct OKc as (Rl1 & _ & _).
        call (st_repz138 L s bfc bdl T mc n1 nextlen' curlen count (arr_get bfc 18) (arr_get bdl 18) PB PD BB BV wbb).
        1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDBm. }
        1:{ apply RBf. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ lia. } 1:{ exact Rnl. } 1:{ exact OK1. }
        st_fin L s t T mc n1 curlen nextlen' f R m0 MU WM ER OK2; try assumption; try lia.
        { repeat (apply sbF_BV_range; [|first [assumption| lia]]). exact RBV. }
        { repeat apply sbF_PD_nonneg. exact RPD. }
      *
        assert (ESC : st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1) = [(arr_get bfc 17, arr_get bdl 17); (count - 2, 3)]).
        { unfold st_calls, REPZ_3_10. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq curlen 0)) by lia.
          rewrite (proj2 (Z.leb_le _ _)) by lia. cbn [negb]. rewrite blc_flat, <- Ebfc, <- Ebdl. replace (count + 1 - 3) with (count - 2) by lia. reflexivity. }
        rewrite ESC in ER, OK1, OK2. clear ESC. rewrite !sbs_run_cons_flat in ER, OK2. cbn [sbs_run] in ER, OK2.
        pose proof OK1 as OKc. apply sbs_ok_cons_flat in OKc. destruct OKc as (Rl1 & _ & _).
        call (st_repz10 L s bfc bdl T mc n1 nextlen' curlen count (arr_get bfc 17) (arr_get bdl 17) PB PD BB BV wbb).
        1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDBm. }
        1:{ apply RBf. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ lia. } 1:{ exact Rnl. } 1:{ exact OK1. }
        st_fin L s t T mc n1 curlen nextlen' f R m0 MU WM ER OK2; try assumption; try lia.
        { repeat (apply sbF_BV_range; [|first [assumption| lia]]). exact RBV. }
        { repeat apply sbF_PD_nonneg. exact RPD. }
    +
      zstep. br_cases_s K4.
      *
        assert (ESC : st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1)
                      = [(arr_get bfc curlen, arr_get bdl curlen); (arr_get bfc 16, arr_get bdl 16); (count - 3, 2)]).
        { unfold st_calls, REP_3_6. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_neq curlen 0)) by lia.
          rewrite (proj2 (Z.eqb_neq curlen prevlen)) by lia. cbn [negb app]. rewrite !blc_flat, <- Ebfc, <- Ebdl. replace (count + 1 - 1 - 3) with (count - 3) by lia. reflexivity. }
        rewrite ESC in ER, OK1, OK2. clear ESC. rewrite !sbs_run_cons_flat in ER, OK2. cbn [sbs_run] in ER, OK2.
        apply sbs_ok_cons_flat in OK1. destruct OK1 as (Rl1 & ROOM1 & OK1).
        pose proof OK1 as OKc. apply sbs_ok_cons_flat in OKc. destruct OKc as (Rl2 & _ & _).
       
        call (st_siteB L s bfc bdl T mc n1 nextlen' curlen (arr_get bfc curlen) (arr_get bdl curlen) PB PD BB BV wbb).
        1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDBm. } 1:{ lia. }
        1:{ apply RBf. lia. } 1:{ exact Rl1. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM1. }
        pose proof (sbF_BV_range BV (arr_get bdl curlen) RBV Rl1) as RBV1. pose proof (sbF_PD_range PD BV (arr_get bdl curlen) RPD) as RPD1.
        match goal with H : EM ?mm _ _ ?pb ?pd ?wb (wz ?bv), HB : bv_unsigned ?wb mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          call (st_rep36 L s bfc bdl T mc n1 nextlen' curlen count (arr_get bfc 16) (arr_get bdl 16) pb pd bb bv wb);
          [reflexivity| reflexivity| exact H| exact HB| eassumption| exact LAY
          | eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]
          | apply RBf; lia| exact RBV1| lia| lia| exact Rnl| exact OK1|] end.
        st_fin L s t T mc n1 curlen nextlen' f R m0 MU WM ER OK2; try assumption; try lia.
        { repeat (apply sbF_BV_range; [|first [assumption| lia]]). exact RBV. }
        { repeat apply sbF_PD_nonneg. exact RPD. }
      *
        assert (ESC : st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1) = [(arr_get bfc 16, arr_get bdl 16); (count + 1 - 3, 2)]).
        { unfold st_calls, REP_3_6. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_neq curlen 0)) by lia.
          rewrite (proj2 (Z.eqb_eq curlen prevlen)) by lia. cbn [negb app]. rewrite !blc_flat, <- Ebfc, <- Ebdl. reflexivity. }
        rewrite ESC in ER, OK1, OK2. clear ESC. rewrite !sbs_run_cons_flat in ER, OK2. cbn [sbs_run] in ER, OK2.
        pose proof OK1 as OKc. apply sbs_ok_cons_flat in OKc. destruct OKc as (Rl1 & _ & _).
        zs2. zstep. br_true.
        call (st_rep36 L s bfc bdl T mc n1 nextlen' curlen (count + 1) (arr_get bfc 16) (arr_get bdl 16) PB PD BB BV wbb).
        1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDBm. }
        1:{ apply RBf. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ lia. } 1:{ exact Rnl. } 1:{ exact OK1. }
        st_fin L s t T mc n1 curlen nextlen' f R m0 MU WM ER OK2; try assumption; try lia.
        { repeat (apply sbF_BV_range; [|first [assumption| lia]]). exact RBV. }
        { repeat apply sbF_PD_nonneg. exact RPD. }
  -
    assert (ESC : st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1) = repeat (arr_get bfc curlen, arr_get bdl curlen) (S (Z.to_nat count))).
    { unfold st_calls. rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite blc_flat, <- Ebfc, <- Ebdl. f_equal. lia. }
    rewrite ESC in ER, OK1, OK2. clear ESC.
    pose proof EMH as EMo. open_EM EMo.
    ustep ST_TRAP. ustep ST_TRAP. zs2. shl_norm. zs2. ustep ST_TRAP. zs2. clear GA GD Gpend LPB LNP.
    reg_as (count + 1) (Z.of_nat (S (Z.to_nat count))).
    call (st_rep (Z.to_nat count) L s bfc bdl T mc n1 nextlen' curlen (arr_get bfc curlen) (arr_get bdl curlen)
                 (sbs_run (upd4 s PB PD BB BV) (repeat (arr_get bfc curlen, arr_get bdl curlen) (S (Z.to_nat count)))) m PB PD BB BV wbb).
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ exact RDBm. } 1:{ lia. } 1:{ apply RBf. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ lia. } 1:{ exact OK1. } 1:{ reflexivity. }
    match goal with E : sbs_run _ _ = upd4 _ _ _ _ _ |- _ => rewrite E in ER, OK2 end.
    unfold ustR. zs2. zstep. br_cases K3.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wb (wz ?bv), HB : bv_unsigned ?wb mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (st_tail L s t T mc n1 curlen nextlen' f R m0 pb pd bb bv ST_T138 wb); [exact H| exact HB| eassumption| exact MU| exact WM| exact ER| exact OK2| | | | | | |] end;
        try assumption; try lia.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wb (wz ?bv), HB : bv_unsigned ?wb mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (st_tail L s t T mc n1 curlen nextlen' f R m0 pb pd bb bv ST_TAIL wb); [exact H| exact HB| eassumption| exact MU| exact WM| exact ER| exact OK2| | | | | | |] end;
        try assumption; try lia.
Qed.

Lemma st_iter : forall (L : dlay) (s : deflate_state) (t : tree_id) (tfc tdl bfc bdl : arr) (T N mc n : Z) (f : nat) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV prevlen nextlen count mx mn : Z) (wbb : word)
    (x8 x9 x18 x19 x23 x25 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono usegs m0 m ->
  ct_readable (Wem L) m0 T tfc tdl N -> tdl = tree_dl s t -> 0 < T -> T + 4 * N < 2^62 -> mc + 1 < N -> N <= 573 ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> bfc = ds_bl_tree_fc s -> bdl = ds_bl_tree_dl s ->
  (forall i, 0 <= i < 19 -> 0 <= arr_get bfc i < 32768) ->
  (forall i, 0 <= i <= mc -> 0 <= arr_get tdl i <= 15) -> (forall i, 0 <= i < N -> 0 <= arr_get tdl i < 65536) ->
  0 <= n <= mc -> nextlen = arr_get tdl n ->
  0 <= BV <= 16 -> 0 <= PD -> 0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  (mn = 4 \/ prevlen = nextlen \/ nextlen = 0) ->
  R = send_tree_loop (S f) (upd4 s PB PD BB BV) t mc n prevlen nextlen count mx mn ->
  send_tree_ok 65536 (S f) (upd4 s PB PD BB BV) t mc n prevlen nextlen count mx mn ->
  evt usegs (ust_trip_post L s t T mc (n + 1) (arr_get tdl (n + 1)) f R sp gp tp F fc m0)
      (MS (ustR L T mc n nextlen (wz prevlen) x8 x9 x18 x19 x23 (wz count) x25 (wz mx) (wz mn) sp gp tp) F (wz ST_BODY) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HBB MI LAY MU WM RDT Etdl RT1 RT2 RmcN RN RDB Ebfc Ebdl RBf RTl RTn Rn Enl RBV RPD Rc Rmx Rmn Rpl INV ER OK.
  assert (HL : forall i, Len (upd4 s PB PD BB BV) t i = arr_get tdl i) by (intros i; unfold Len; rewrite upd4_tree_dl, <- Etdl; reflexivity).
  pose proof (RTl n Rn) as Rcl. rewrite <- Enl in Rcl.
  pose proof (RTn (n + 1) ltac:(lia)) as Rnl'.
  destruct (RDT m MU WM MI (n + 1) ltac:(lia)) as [_ RDl].
  assert (Rmn1 : 1 <= mn) by lia.
  pose proof LAY as LAY'. lay_open LAY'.
  unfold ustR, ST_BODY.
  do 4 ustep ST_TRAP. ustep ST_TRAP. shl_norm. do 7 ustep ST_TRAP. at_pc 0x1e2cc.
  reg_as ((n + 1) * 4 + T + 2) (T + 4 * (n + 1) + 2).
  zs2. rewrite (zx16_small (arr_get tdl (n + 1))) by lia. zs2.
  zstep. br_cases K1.
  -
    rewrite st_step_emit in ER by (try lia; left; lia). apply st_ok_emit in OK; [|lia| left; lia]. destruct OK as [OK1 OK2]. rewrite HL in ER, OK2.
    eapply (st_emit L s t bfc bdl T mc (n + 1) f R m0 PB PD BB BV prevlen nextlen (arr_get tdl (n + 1)) count mx mn wbb); try eassumption; lia.
  - zstep. br_cases_s K2.
    +
      rewrite st_step_keep in ER by (try lia; rewrite HL; exact K2). apply st_ok_keep in OK; [|lia|lia| rewrite HL; exact K2]. rewrite HL in ER, OK.
      zs2.
      eapply (st_latch L s t T mc (n + 1) (arr_get tdl (n + 1)) f R m0 PB PD BB BV prevlen (count + 1) mx mn wbb); try eassumption; lia.
    + rewrite st_step_emit in ER by (try lia; right; rewrite HL; exact K2). apply st_ok_emit in OK; [|lia| right; rewrite HL; exact K2]. destruct OK as [OK1 OK2]. rewrite HL in ER, OK2.
      eapply (st_emit L s t bfc bdl T mc (n + 1) f R m0 PB PD BB BV prevlen nextlen (arr_get tdl (n + 1)) count mx mn wbb); try eassumption; lia.
Qed.
