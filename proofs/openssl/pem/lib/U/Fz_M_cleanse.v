(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import F_memset Fz_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_CLEANSE : Z := 0xe9868.

Lemma openssl_cleanse_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (D N lo : Z) (junk : list byte),
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 N -> 0 <= D -> 0 <= N < 2^64 -> D + N <= 2^64 ->
  D + N <= lo \/ bv_unsigned sp <= D ->
  cimg m -> rw_cells usegs m D [CB (Z.to_nat N) junk] ->
  stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom usegs)
               /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (D, D + N)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
               /\ rw_cells usegs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 0) (Z.to_nat N))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FZ_CLEANSE) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros A0 A1 HD HN HDN APART CIMG DST ST GLO SLO MI. subst a0 a1.
  unfold FZ_CLEANSE, GLOBALS_TOP in *.
  cimg_cell CIMG m 0x31d4f8 [C8 (Z_to_bv 64 0x2bb4b0)] FN.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (D, D + N)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. carve_frame 16%nat ST. do 11 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  eapply evt_cut; [eapply (memset_callZ ra sp) with (D := D) (C := 0) (N := N); [eassumption| eassumption| lia| lia| lia| lia]|].
  intros ms2 (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & ZB).
  apply evt_done. do 14 eexists. exists m2. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside] in *. tauto. }
  split; [eapply wmono_trans; eassumption|]. split; [exact MI2|]. split; [| exact ZB].
  eapply stk_transport_disjoint; [exact ST| exact MU2| exact WM2|]. cbn [disjoint_from].
  pose proof (rw_cells_bound _ _ _ _ DST) as BD. cbn [cells_size csize Nat.add] in BD. lia.
Qed.
End WithCeiling0.
