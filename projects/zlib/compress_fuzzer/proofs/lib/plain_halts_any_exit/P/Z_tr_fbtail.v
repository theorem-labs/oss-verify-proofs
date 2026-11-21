(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition wuF_PB (PB : arr) (PD BB BV : Z) : arr :=
  if 8 <? BV then arr_set (arr_set PB PD (wrap8 (Z.land BB 255))) (PD + 1) (wrap8 (Z.shiftr (wrap16 BB) 8))
  else if 0 <? BV then arr_set PB PD (wrap8 BB) else PB.
Definition wuF_PD (PD BV : Z) : Z := if 8 <? BV then PD + 1 + 1 else if 0 <? BV then PD + 1 else PD.

Lemma bi_windup_wuF : forall s PB PD BB BV, bi_windup (upd4 s PB PD BB BV) = upd4 s (wuF_PB PB PD BB BV) (wuF_PD PD BV) 0 0.
Proof.
  intros. unfold wuF_PB, wuF_PD. destruct (Z.ltb_spec 8 BV) as [C|C].
  - rewrite bi_windup_eq2 by (rewrite upd4_bi_valid; exact C). rewrite !upd4_pending_buf, !upd4_pending, !upd4_bi_buf. apply upd4_upd4.
  - destruct (Z.ltb_spec 0 BV) as [C0|C0].
    + rewrite bi_windup_eq1 by (rewrite upd4_bi_valid; lia). rewrite !upd4_pending_buf, !upd4_pending, !upd4_bi_buf. apply upd4_upd4.
    + rewrite bi_windup_eq0 by (rewrite upd4_bi_valid; lia). rewrite !upd4_pending_buf, !upd4_pending. apply upd4_upd4.
Qed.

Definition tfb_windup_post (L : dlay) (s : deflate_state) (PB : arr) (PD : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b9a0) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD (wz 0) (wz 0).

Lemma tfb_windup : forall (L : dlay) (s : deflate_state) (PB : arr) (PD BB BV : Z)
    (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD (wz BB) (wz BV) -> mem_inv psegs m -> dlay_ok L ->
  0 <= BV <= 16 -> 0 <= BB < 2^16 -> 0 <= PD -> wuF_PD PD BV <= 65536 ->
  evt psegs (tfb_windup_post L s (wuF_PB PB PD BB BV) (wuF_PD PD BV)
                ra sp gp tp t0 t1 t2 (wz (dl_As L)) s1 a4 a5 a6 a7 s2 s3 s4 (wz (dl_As L + 5912)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz (dl_As L + 5912)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b92c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH MI LAY RBV RBB RPD ROOM.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH. unfold wuF_PD in ROOM.
  zs2. zs2. zstep. br_cases K.
  -
    zstep. br_cases K0.
    +
      zs2. zs2. zs2. zs2. zs2. zs2. zs2. (* 1.4 bi_windup: lw, sh, add, and, add, sw, sw bi_used *)
      apply evt_done. unfold tfb_windup_post, wuF_PB, wuF_PD. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 5 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. close_EM GA GD Gpend.
    +
      rewrite (proj2 (Z.ltb_ge 8 BV)), (proj2 (Z.ltb_lt 0 BV)) in ROOM by lia.
      zs2. zs2. rd_c2 GD 55%nat 0. zsb. zs2. zs2. zs2.
      pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 BB) ltac:(apply b0_val_w; lia).
      zs2. zs2. zs2. zs2. zs2. zs2. zs2. (* 1.4 bi_windup: lw, sh, add, and, add, sw, sw bi_used *)
      apply evt_done. unfold tfb_windup_post, wuF_PB, wuF_PD. rewrite (proj2 (Z.ltb_ge 8 BV)), (proj2 (Z.ltb_lt 0 BV)) by lia. do 5 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. close_EM GA GD Gpend.
  -
    rewrite (proj2 (Z.ltb_lt 8 BV)) in ROOM by lia.
    zs2. zs2. rd_c2 GD 55%nat 0. zsb. zs2. zs2. zs2.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land BB 255)) ltac:(apply b0_val_land; lia).
    zs2. zs2. rd_c2 GD 55%nat 1. zsb. zs2. zs2. zs2. zs2.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land BB 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 BB) 8)) ltac:(apply b1_val; lia).
    zs2. zs2. zs2. zs2. zs2. zs2. zs2. (* 1.4 bi_windup: lw, sh, add, and, add, sw, sw bi_used *)
    apply evt_done. unfold tfb_windup_post, wuF_PB, wuF_PD. rewrite (proj2 (Z.ltb_lt 8 BV)) by lia. do 5 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. close_EM GA GD Gpend.
Qed.
