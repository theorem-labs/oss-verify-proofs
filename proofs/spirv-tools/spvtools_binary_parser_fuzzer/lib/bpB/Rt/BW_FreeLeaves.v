(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics BllocWalkKit BW_Leaves BsDepotInv.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Definition free_hooks_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Section FreeHooks.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 32 <= bv_unsigned sp.
  Hypothesis CHOOKS : rw_cells asegs m AHOOKS (repeat (C8 (wz 0)) 10).

  Theorem run_free_hooks_spec :
    evt asegs (free_hooks_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc8a64) fc None m (seg_rom asegs)).
  Proof.
    unfold AHOOKS in *. cbn [repeat] in CHOOKS.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.

    step. carve_frame 32%nat ST. step. step. step. step.

    step. step. step. replace (ret_pc (Z_to_bv 64 0xc8a7c)) with (Z_to_bv 64 0xc8a7c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    step. if_cases K; [| exfalso; revert K; vm_compute; discriminate]. clear K.

    step. step. step. replace (ret_pc (Z_to_bv 64 0xc8aa0)) with (Z_to_bv 64 0xc8aa0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    step. step. step. step. if_cases K; zify_cond K. 2:{ exfalso. revert K. rewrite ?wz_unsigned, ?unsigned_lit by lia. lia. } clear K.

    step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End FreeHooks.

Lemma upd_repeat_same {X} : forall (x : X) k i, upd (repeat x k) i x = repeat x k.
Proof. intros x k. induction k as [|k IH]; intros [|i]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma firstn_repeat' {X} : forall (x : X) i k, firstn i (repeat x k) = repeat x (Nat.min i k).
Proof. intros x i k. revert i. induction k as [|k IH]; intros [|i]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma skipn_repeat' {X} : forall (x : X) i k, skipn i (repeat x k) = repeat x (k - i).
Proof. intros x i k. revert i. induction k as [|k IH]; intros [|i]; cbn; try reflexivity. apply IH. Qed.
Lemma upd_bytes_repeat_same : forall (x : byte) k i j, (i + j <= k)%nat -> upd_bytes (repeat x k) i (repeat x j) = repeat x k.
Proof.
  intros x k i j H. unfold upd_bytes. rewrite firstn_repeat', skipn_repeat', repeat_length.
  rewrite <- !repeat_app. f_equal. lia.
Qed.
Lemma le8_zero : le8 (wz 0) = repeat (b8 0) 8.
Proof. vm_compute. reflexivity. Qed.

Definition imz_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (dst n : Z) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(dst, dst + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' dst (repeat (b8 0) (Z.to_nat n)).

Section IMemsetZero.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (dst n : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis RNG : 0 <= dst /\ dst + n <= 2^47 /\ 0 < n.
  Hypothesis ZER : u8arr asegs m dst (repeat (b8 0) (Z.to_nat n)).
  Notation POST := (imz_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m dst n).

  Lemma imz_loop1 : forall (K : nat) (i : Z) (m1 : mem),
    Z.to_nat (n - i) = K -> 0 <= i < n ->
    u8arr asegs m1 dst (repeat (b8 0) (Z.to_nat n)) -> mem_inv asegs m1 -> munch [(dst, dst + n)]%Z m m1 -> wmono asegs m m1 ->
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz 0) (wz (dst + n)) (wz (dst + i)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xcbd68) fc None m1 (seg_rom asegs)).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros i m1 HK Hi ARR MI1 MU WM. unfold wz.
    pose proof (u8arr_store_ok asegs m1 dst _ i (wa (dst + i)) ARR ltac:(hci; rewrite repeat_length; lia) eq_refl) as HS.
    step. match goal with |- context [write_to_mem _ _ ?bs] => idtac "BYTES:" bs end.
    match goal with |- context [write_to_mem _ _ ?bs] => change bs with [b8 0] end.
    pose proof (u8arr_write asegs m1 dst _ i (b8 0) ARR ltac:(hci; rewrite repeat_length; lia)) as ARR'. rewrite upd_repeat_same in ARR'. clear ARR. store_done.

    zstep. step. if_cases K1; zify_cond K1.
    - replace (dst + i + 1) with (dst + (i + 1)) by lia.
      eapply (IH (Z.to_nat (n - (i + 1))) ltac:(hci; lia) (i + 1)); try eassumption; lia.
    -
      step. step. apply evt_done. unfold imz_post. do 4 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ARR'].
  Qed.

  Lemma imz_loop16 : forall (K : nat) (i : Z) (m1 : mem),
    Z.to_nat (n - i) = K -> 0 <= i < n -> i mod 16 = 0 -> n mod 16 = 0 ->
    u8arr asegs m1 dst (repeat (b8 0) (Z.to_nat n)) -> mem_inv asegs m1 -> munch [(dst, dst + n)]%Z m m1 -> wmono asegs m m1 ->
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz 0) (wz (dst + n)) (wz (dst + i)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xcbd9c) fc None m1 (seg_rom asegs)).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros i m1 HK Hi I16 N16 ARR MI1 MU WM. unfold wz.
    assert (IR : i + 16 <= n) by (clear - Hi I16 N16; try acb; Z.div_mod_to_equations; lia).

    pose proof (u8arr_store_ok_n asegs m1 dst _ i 8 (wa (dst + i)) ARR ltac:(hci; lia) ltac:(hci; rewrite repeat_length; clear - Hi IR; try acb; lia) eq_refl) as HS.
    step. match goal with |- context [write_to_mem _ _ ?bs] => change bs with [b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0] end.
    pose proof (u8arr_write_n asegs m1 dst _ i [b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0] ARR ltac:(hci; lia) ltac:(hci; rewrite repeat_length; cbn [length]; clear - Hi IR; try acb; lia)) as ARR'.
    change [b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0] with (repeat (b8 0) 8) in ARR' at 2.
    rewrite upd_bytes_repeat_same in ARR' by (clear - Hi IR; try acb; lia). clear ARR. store_done.

    pose proof (u8arr_store_ok_n asegs _ dst _ (i + 8) 8 (wa (dst + (i + 8))) ARR' ltac:(hci; lia) ltac:(hci; rewrite repeat_length; clear - Hi IR; try acb; lia) eq_refl) as HS.
    step. match goal with |- context [write_to_mem _ _ ?bs] => change bs with [b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0] end.
    lazymatch goal with |- context [write_to_mem ?mm _ _] =>
      pose proof (u8arr_write_n asegs mm dst _ (i + 8) [b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0] ARR' ltac:(hci; lia) ltac:(hci; rewrite repeat_length; cbn [length]; clear - Hi IR; try acb; lia)) as ARR'' end.
    change [b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0] with (repeat (b8 0) 8) in ARR'' at 2.
    rewrite upd_bytes_repeat_same in ARR'' by (clear - Hi IR; try acb; lia).
    clear ARR'. store_done.

    zstep. step. if_cases K1; zify_cond K1.
    - replace (dst + i + 16) with (dst + (i + 16)) by lia.
      eapply (IH (Z.to_nat (n - (i + 16))) ltac:(hci; lia) (i + 16)); try eassumption; try lia.
    -
      step. apply evt_done. unfold imz_post. do 4 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ARR''].
  Qed.

  Theorem internal_memset0_bytes_spec : Z.land (Z.lor n dst) 15 <> 0 ->
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz 0) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xcbd50) fc None m (seg_rom asegs)).
  Proof.
    intros AL. unfold wz.
    pose proof (munch_refl [(dst, dst + n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.

    zstep. zstep. step. if_cases K1; zify_cond K1.
    { exfalso. apply AL. revert K1. rewrite ?unsigned_lit by lia. clear. intros K1. lia. }
    clear K1. step. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit by aunf; lia; clear - RNG; try acb; lia|]. clear K1.
    zstep. zstep. replace (Z_to_bv 64 dst) with (Z_to_bv 64 (dst + 0)) at 1 by (f_equal; lia).
    eapply (imz_loop1 (Z.to_nat (n - 0)) 0 m); try eassumption; try lia.
  Qed.

  Theorem internal_memset0_16_spec : dst mod 16 = 0 -> n mod 16 = 0 ->
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz 0) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xcbd50) fc None m (seg_rom asegs)).
  Proof.
    intros D16 N16. unfold wz.
    pose proof (munch_refl [(dst, dst + n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (AL : Z.land (Z.lor n dst) 15 = 0).
    { change 15 with (Z.ones 4). rewrite Z.land_lor_distr_l, !Z.land_ones by lia. change (2^4) with 16. rewrite N16, D16. reflexivity. }

    zstep. zstep. step. if_cases K1; zify_cond K1; [| exfalso; revert K1; rewrite ?unsigned_lit by lia; rewrite AL; clear; lia]. clear K1.
    step. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit by aunf; lia; clear - RNG; try acb; lia|]. clear K1.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 dst) with (Z_to_bv 64 (dst + 0)) at 1 by (f_equal; lia).
    eapply (imz_loop16 (Z.to_nat (n - 0)) 0 m); try eassumption; try lia.
  Qed.
End IMemsetZero.

End HCW.

