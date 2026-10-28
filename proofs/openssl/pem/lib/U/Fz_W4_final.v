(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Ubs SFModel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W4_defs Fz_W4_block.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition W4_decode_final_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (C T OL lo num : Z) (K : nat) (ln old : word) (ed bs0 : list byte),
    a0 = Z_to_bv 64 C -> a1 = Z_to_bv 64 T -> a2 = Z_to_bv 64 OL ->
    0 < C -> C mod 4 = 0 -> 0 < OL -> OL mod 4 = 0 -> 0 < T ->
    rw_cells usegs m C (ectx_cells (Z_to_bv 64 num) ed ln z64) -> length ed = 80%nat -> 0 <= num <= 64 ->
    rw_cells usegs m T [CB K bs0] -> 3 * (num / 4) <= Z.of_nat K ->
    rw_cells usegs m OL [C4 old] ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 96 ->
    (C + 92 <= T \/ T + Z.of_nat K <= C) -> (C + 92 <= OL \/ OL + 4 <= C) -> (T + Z.of_nat K <= OL \/ OL + 4 <= T) ->
    (C + 92 <= lo \/ bv_unsigned sp <= C) -> (T + Z.of_nat K <= lo \/ bv_unsigned sp <= T) -> (OL + 4 <= lo \/ bv_unsigned sp <= OL) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (rv dl num' : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (bs' : list byte) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 rv) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (C, C + 4); (T, T + 3 * (num / 4)); (OL, OL + 4)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ ((rv = 1 /\ num' = 0 /\ 0 <= dl <= 3 * (num / 4)) \/ (rv = -1 /\ num' = num /\ dl = 0))
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' C (ectx_cells (Z_to_bv 64 num') ed ln z64)
                 /\ rw_cells usegs m' T [CB K bs']
                 /\ rw_cells usegs m' OL [C4 (Z_to_bv 64 dl)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1924d8) fc None m (seg_rom usegs)).

Theorem W4_decode_final_proof : W4_decode_final_stmt.
Proof.
  unfold W4_decode_final_stmt, ectx_cells. intros until bs0.
  intros -> -> -> HC HCA HO HOA HT CTX LED HN DST HK OLC ST LO0 LO S1 S2 S3 S4 S5 S6 MI.
  pose proof (rw_cells_bound _ _ _ _ CTX) as CB. cbn [cells_size csize Nat.add] in CB.
  pose proof (rw_cells_bound _ _ _ _ DST) as TB. cbn [cells_size csize Nat.add] in TB.
  pose proof (rw_cells_bound _ _ _ _ OLC) as OB. cbn [cells_size csize Nat.add] in OB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (HD : 0 <= num / 4) by (apply Z.div_pos; lia).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (C, C + 4); (T, T + 3 * (num / 4)); (OL, OL + 4)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  do 7 ths.
  ths. ubs_if.
  do 4 ths. ubs_if.
  do 2 ths. ubs_if.
  do 2 ths. ubs_if.
  ths. rewrite (t_sx32_small num) by lia.
  do 2 ths. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    do 8 ths.
    th_release FR (bv_unsigned sp).
    apply evt_done. exists 1, 0, 0. do 14 eexists. exists bs0. eexists.
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [left; lia|]. split; [exact ST|].
    replace num with 0 in CTX by lia. split; [exact CTX|]. split; [exact DST | exact OLC].
  - do 5 ths.
    pose proof (proj1 CTX : ro_cells usegs _ C (ectx_cells (Z_to_bv 64 num) ed ln z64)) as CRO.
    tcall (dblock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C T K num (-1) (Z_to_bv 64 num) ln ed bs0 lo).
    1-21: first [reflexivity | eassumption | lia].
    clear PC1. cbv beta delta [mkR].
    destruct PC as [-> | PC].
    + (* [comment removed for export] *)
      ths. th_if_lit.
      do 8 ths.
      th_release FR (bv_unsigned sp).
      apply evt_done. exists (-1), 0, num. do 14 eexists. exists x14. eexists.
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [right; lia|].
      split; [eassumption|]. split; [exact CTX|]. split; [exact POST | exact OLC].
    + ths. if_cases KD; zify_cond KD; signed_lits_in KD. { exfalso. lia. }
      do 3 ths.
      do 8 ths.
      th_release FR (bv_unsigned sp).
      apply evt_done. exists 1, x, 0. do 14 eexists. exists x14. eexists.
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [left; lia|].
      split; [eassumption|]. split; [exact CTX|]. split; [exact POST | exact OLC].
Qed.
