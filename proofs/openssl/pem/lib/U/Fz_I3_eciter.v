(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_free. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).

(* [comment removed for export] *)
Lemma crypto_free_null_c : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  a0 = Z_to_bv 64 0 ->
  rw_cells usegs m 0x31c088 [C8 (wz FZ_CRYPTO_FREE)] -> rw_cells usegs m 0x31d4f0 [C8 (wz FZ_CRYPTO_FREE)] ->
  stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom usegs)
               /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FZ_CRYPTO_FREE) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros -> GOTF IMPL ST GLO SLO MI.
  unfold FZ_CRYPTO_FREE, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. carve_frame 16%nat ST. do 7 step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
  do 4 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  eapply evt_mono; [eapply rfree_null_spec; reflexivity|].
  intros ms2 ->. do 15 eexists. exists m1. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
Definition es_pre (k : nat) (ls : list word) : list cell :=
  repeat (C4 z64) 16 ++ repeat (C4 z64) 16 ++ repeat (C8 z64) 16 ++ repeat (C8 z64) 16 ++ repeat (C8 z64) 16
  ++ (repeat (C4 z64) k ++ repeat (CB 4 (zeros 4)) (16 - k)) ++ repeat (C8 z64) 16 ++ map C4 ls ++ repeat (C8 z64) 16 ++ [CB 8 (zeros 8)].

Definition FZ_ECL_LOOP : Z := 0xe80fc.
Definition FZ_ECL_DONE : Z := 0xe8114.

Definition eclear_iter_stmt (k : nat) (lnw : word) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo E : Z) (ls : list word),
  s1 = Z_to_bv 64 E -> s2 = Z_to_bv 64 (Z.of_nat k) -> s3 = Z_to_bv 64 16 ->
  length ls = 16%nat ->
  rw_cells usegs m E (es_pre k ls) -> 0 < E -> E mod 8 = 0 -> E + 904 <= alloc_ceiling -> (E + 904 <= 0x10000 \/ 0x353000 <= E) ->
  rw_cells usegs m 0x31c088 [C8 (wz FZ_CRYPTO_FREE)] -> rw_cells usegs m 0x31d4f0 [C8 (wz FZ_CRYPTO_FREE)] ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 80 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
       ms' = MS (mkR (Z_to_bv 64 0xe810c) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (Z.of_nat (S k))) s3 s4
                     s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 (if Nat.eqb k 15 then FZ_ECL_DONE else FZ_ECL_LOOP)) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (E, E + 904)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' E (es_pre (S k) (upd ls k lnw)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_ECL_LOOP) fc None m (seg_rom usegs)).

Definition ECL_LNW : word := Z_to_bv 64 18446744073709551615.
End WithCeiling0.

Ltac es_wf := cbn [cells_wf cell_wf repeat map app length Nat.sub]; repeat (split; [first [exact I| reflexivity]|]); exact I.

Ltac ec_ref K := exfalso; rewrite ?unsigned_lit in K by lia; rewrite ?ubs_land7, ?zb_lxor_ones in K by lia; lia.
Ltac ec_F := first [ ubs_if | let K := fresh "K" in if_cases K; zify_cond K; [ec_ref K | try clear K] ].
Ltac ec_T := let K := fresh "K" in if_cases K; zify_cond K; [try clear K | ec_ref K].

Ltac eclear_iter_tac k :=
  unfold eclear_iter_stmt;
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo E ls;
  intros -> -> -> LEN EB E0 E8 EC EIMG GOTF IMPL ST LO SLO MI;
  assert (GLO : GLOBALS_TOP <= lo) by (unfold GLOBALS_TOP; lia);
  let z := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with z;
  destruct ls as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 [|b9 [|b10 [|b11 [|b12 [|b13 [|b14 [|b15 [|b16 ls']]]]]]]]]]]]]]]]]; try discriminate LEN;
  unfold es_pre, FZ_ECL_LOOP, FZ_ECL_DONE, GLOBALS_TOP, FZ_CRYPTO_FREE in *; cbn [repeat map app Nat.sub upd Nat.eqb] in EB |- *;
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (E, E + 904)]%Z m) as MU; pose proof (wmono_refl usegs m) as WM;
  pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR;
  do 4 step;
  step; th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST; do 8 ths; step;
  step; ec_F; step; step; step; ec_F;
  step; step; ec_F; step; step; step; step; ec_F;
  (* [comment removed for export] *)
  step;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with EBh : rw_cells usegs mm E ?cs |- _ =>
        apply (th_cells_congr usegs mm E cs (es_pre k [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15])) in EBh;
        [ unfold es_pre in EBh; cbn [repeat map app Nat.sub] in EBh | reflexivity | reflexivity | unfold es_pre; es_wf ] end end;
  step; step; step; th_if_lit;
  step; step; step; ec_F; step; step; step; cstep; step; ec_T;
  step; cstep; step; ec_F; step; cstep;
  (* [comment removed for export] *)
  step; step; step; ec_F; step; step; cstep; step; ec_F;
  step; step; cstep; step; ec_F; step; step; step; cstep; step; ec_F;
  step; step; step; step; cstep; step; ec_F;
  step; step; step; step; step;
  tcallr crypto_free_null_c; [ first [eassumption | reflexivity | lia] .. | ];
  cbv beta delta [mkR]; try th_ret_lit;
  (* [comment removed for export] *)
  step; ec_F; step; step; cstep; step; ec_F;
  step; step; step; step; step;
  tcallr crypto_free_null_c; [ first [eassumption | reflexivity | lia] .. | ];
  cbv beta delta [mkR]; try th_ret_lit;
  step; ec_F; cstep; do 8 step;
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => th_release FRh (bv_unsigned sp) end;
  step; step; try th_ret_lit;
  step; step; th_if_lit;
  apply evt_done; do 16 eexists; split; [reflexivity|]; repeat match goal with |- _ /\ _ => split end; eassumption.

Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma eclear_iter_0 : eclear_iter_stmt 0 ECL_LNW.
Proof. pose proof ceil_window_holds as CW0. unfold ceil_window in CW0. unfold ECL_LNW. eclear_iter_tac 0%nat. Qed.
Lemma eclear_iter_1 : eclear_iter_stmt 1 ECL_LNW.
Proof. pose proof ceil_window_holds as CW0. unfold ceil_window in CW0. unfold ECL_LNW. eclear_iter_tac 1%nat. Qed.
Lemma eclear_iter_2 : eclear_iter_stmt 2 ECL_LNW.
Proof. pose proof ceil_window_holds as CW0. unfold ceil_window in CW0. unfold ECL_LNW. eclear_iter_tac 2%nat. Qed.
Lemma eclear_iter_3 : eclear_iter_stmt 3 ECL_LNW.
Proof. pose proof ceil_window_holds as CW0. unfold ceil_window in CW0. unfold ECL_LNW. eclear_iter_tac 3%nat. Qed.
Lemma eclear_iter_4 : eclear_iter_stmt 4 ECL_LNW.
Proof. pose proof ceil_window_holds as CW0. unfold ceil_window in CW0. unfold ECL_LNW. eclear_iter_tac 4%nat. Qed.

End WithCeiling1.
