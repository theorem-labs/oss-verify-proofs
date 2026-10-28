(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_realloc Fz_kit_ra.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_sk Fz_K_skstmt.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma u8arr_of_CB : forall (m : mem) A n bs, rw_cells usegs m A [CB n bs] -> u8arr usegs m A bs.
Proof.
  intros m A n bs [[[WF _] B] W]. cbn [cell_wf] in WF. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. cbn [cells_size csize Nat.add] in W.
  split; [exact B| rewrite <- WF, Nat.add_0_r in W; exact W].
Qed.
Lemma CB_of_u8arr : forall (m : mem) A bs, u8arr usegs m A bs -> rw_cells usegs m A [CB (length bs) bs].
Proof.
  intros m A bs [B W]. split; [split; [cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact B]|].
  cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact W.
Qed.

(* [comment removed for export] *)
Lemma land_full : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma sk_lxor_sign : forall n, 0 <= n < 2^63 -> Z.lxor n 9223372036854775808 = n + 9223372036854775808.
Proof.
  intros n Hn. symmetry. rewrite Z.add_nocarry_lxor; [reflexivity|]. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0. destruct (Z.eq_dec i 63) as [->|NE].
  - replace (Z.testbit n 63) with false; [reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
    destruct (Z.eq_dec n 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  - change 9223372036854775808 with (2^63). rewrite (Z.pow2_bits_eqb 63 i) by lia. replace (63 =? i) with false by (symmetry; apply Z.eqb_neq; lia). apply Bool.andb_false_r.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition T_sk_reserve_room_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A D num nalloc : Z) (pad srt cmpt freet copyt : word),
    a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 1 -> a2 = z64 -> 0 < A -> 0 < D ->
    rw_cells usegs m A (sk_cells (Z_to_bv 64 num) pad (Z_to_bv 64 D) srt (Z_to_bv 64 nalloc) z64 cmpt freet copyt) ->
    0 <= num -> num + 1 <= nalloc -> 4 <= nalloc < 2 ^ 20 ->
    stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 48 -> A + 56 <= lo -> D + 8 * nalloc <= lo ->
    mem_inv usegs m -> A mod 8 = 0 ->
    evt usegs (fun ms' => exists (a1' a3' a4' a5' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2 a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FZ_SK_RESERVE) fc None m (seg_rom usegs)).
Theorem T_sk_reserve_room_proof : T_sk_reserve_room_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  unfold T_sk_reserve_room_stmt. intros until copyt. intros -> -> -> A0 D0 HC NUM0 NUM1 NAL ST GLO LO SEPA SEPD MI AAL.
  unfold FZ_SK_RESERVE, GLOBALS_TOP, ceil_window, sk_cells in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (SGS : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z) by (intros z Hz; rewrite zb_signed; rewrite unsigned_lit by lia; destruct (Z.ltb_spec z (2 ^ 63)); lia).
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  do 7 ths. ths.
  ths. ths. ubs_if.
  ths. ths. ths. ths. ths. ths.
  rewrite (t_sx32_small num) by lia. rewrite (unsigned_lit num) by lia. rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
  if_cases KS; zify_cond KS. { exfalso. rewrite ?unsigned_lit in KS by lia. lia. } clear KS.
  ths. ths. if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; rewrite ?Z.add_0_r in K1; rewrite ?bv_swrap_small in K1 by (change (bv_half_modulus 32) with (2 ^ 31); lia); rewrite ?SGS in K1 by lia; lia].
  ths. ths. ths. rewrite (unsigned_lit num) by lia.
  if_cases KA; zify_cond KA. { exfalso. rewrite bv_swrap_small in KA by (change (bv_half_modulus 32) with (2 ^ 31); lia). rewrite land_full in KA by lia. lia. } clear KA.
  ths. rewrite ?(t_sx32_small (num + 1)) by lia.
  ths. ths. if_cases K2; zify_cond K2.
  - (* [comment removed for export] *)
    ths. ths. if_cases K3; zify_cond K3; [exfalso; rewrite ?land_full in K3 by (clear - D0 SEPD LO RSP NAL; lia); clear - K3 D0; lia|].
    ths. rewrite (t_sx32_small nalloc) by lia. ths. th_if_lit.
    ths. if_cases K4; zify_cond K4; [| exfalso; rewrite ?Z.add_0_r in K4; rewrite ?bv_swrap_small in K4 by (change (bv_half_modulus 32) with (2 ^ 31); lia); rewrite ?SGS, ?unsigned_lit in K4 by lia; clear - K4 NUM1 NAL NUM0; lia].
    ths. do 6 ths. th_release FR (bv_unsigned sp). ths. finish.
  - (* [comment removed for export] *)
    ths. ths. ths. if_cases K3; zify_cond K3; [exfalso; rewrite ?land_full in K3 by (clear - D0 SEPD LO RSP NAL; lia); clear - K3 D0; lia|].
    ths. rewrite (t_sx32_small nalloc) by lia. ths. th_if_lit.
    ths. if_cases K4; zify_cond K4; [| exfalso; rewrite ?Z.add_0_r in K4; rewrite ?bv_swrap_small in K4 by (change (bv_half_modulus 32) with (2 ^ 31); lia); rewrite ?SGS, ?unsigned_lit in K4 by lia; clear - K4 NUM1 NAL NUM0; lia].
    ths. do 6 ths. th_release FR (bv_unsigned sp). ths. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition T_sk_insert_room_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A D num nalloc s01 : Z) (pad cmpt freet copyt : word) (junk : list byte),
    a0 = Z_to_bv 64 A -> a2 = Z_to_bv 64 num -> 0 < A -> 0 < D ->
    rw_cells usegs m A (sk_cells (Z_to_bv 64 num) pad (Z_to_bv 64 D) (Z_to_bv 64 s01) (Z_to_bv 64 nalloc) z64 cmpt freet copyt) ->
    (s01 = 0 \/ s01 = 1) -> 1 <= num -> num + 1 <= nalloc -> 4 <= nalloc < 2 ^ 20 ->
    u8arr usegs m D junk -> Z.of_nat (length junk) = 8 * nalloc ->
    stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 96 ->
    A + 56 <= lo -> D + 8 * nalloc <= lo -> (A + 56 <= D \/ D + 8 * nalloc <= A) ->
    mem_inv usegs m -> A mod 8 = 0 -> D mod 8 = 0 ->
    evt usegs (fun ms' => exists (a1' a2' a3' a4' a5' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (num + 1)) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 56); (D, D + 8 * nalloc)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' A (sk_cells (Z_to_bv 64 (num + 1)) pad (Z_to_bv 64 D) z64 (Z_to_bv 64 nalloc) z64 cmpt freet copyt)
                 /\ u8arr usegs m' D (upd_bytes junk (Z.to_nat (8 * num)) (le8 a1)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FZ_SK_INSERT) fc None m (seg_rom usegs)).
Theorem T_sk_insert_room_proof : T_sk_insert_room_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  unfold T_sk_insert_room_stmt. intros until junk. intros -> -> A0 D0 HC S01 NUM1 NUMN NAL DB LJ ST GLO LO SEPA SEPD APAD MI AAL DAL.
  unfold FZ_SK_INSERT, GLOBALS_TOP, ceil_window, sk_cells in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 56); (D, D + 8 * nalloc)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (SGS : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z) by (intros z Hz; rewrite zb_signed; rewrite unsigned_lit by lia; destruct (Z.ltb_spec z (2 ^ 63)); lia).
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  do 8 ths.
  ths. if_cases K0; zify_cond K0. { exfalso. rewrite ?land_full in K0 by (clear - A0 SEPA LO RSP; lia). clear - K0 A0; lia. }
  ths. ths. ths. ubs_if.
  ths. ths. ths. ths. ths. rewrite (t_sx32_small num) by lia.
  if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia; [| exfalso; lia]. clear K1.
  ths. ths. ths. ths. ths.
  pose proof T_sk_reserve_room_proof as X. unfold T_sk_reserve_room_stmt, GLOBALS_TOP, FZ_SK_RESERVE in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo A D num nalloc pad (Z_to_bv 64 s01) cmpt freet copyt).
  all: try first [reflexivity | eassumption | clear X; lia].
  clear X. cbv beta delta [mkR].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m2 end.
  ths. th_if_lit. ths. ths. ths.
  if_cases K2; zify_cond K2; [exfalso; rewrite ?Z.add_0_r in K2; rewrite ?bv_swrap_small in K2 by (change (bv_half_modulus 32) with (2 ^ 31); lia); rewrite ?SGS, ?unsigned_lit in K2 by lia; lia|]. clear K2.
  ths. rewrite (t_sx32_small num) by lia. if_cases K3; zify_cond K3; [| exfalso; rewrite ?Z.add_0_r in K3; rewrite ?bv_swrap_small in K3 by (change (bv_half_modulus 32) with (2 ^ 31); lia); rewrite ?SGS, ?unsigned_lit in K3 by lia; lia]. clear K3.
  ths. ths. ths. ths. ths.
  if_cases KP1; zify_cond KP1.
  { exfalso. rewrite Z.shiftl_mul_pow2 in KP1 by lia. change (2 ^ 3) with 8 in KP1. rewrite land_full in KP1 by lia.
    rewrite (proj2 (Z.ltb_lt 0 D)), (proj2 (Z.ltb_ge (D + num * 8) 1)) in KP1 by lia. cbv in KP1. discriminate KP1. }
  ths. ths. ths. ths. ths.
  if_cases KP2; zify_cond KP2.
  { exfalso. rewrite Z.shiftl_mul_pow2 in KP2 by lia. change (2 ^ 3) with 8 in KP2. rewrite land_full in KP2 by lia.
    rewrite (sk_lxor_sign num) in KP2 by lia.
    rewrite (proj2 (Z.ltb_ge (D + num * 8) D)), (proj2 (Z.ltb_ge (num + 9223372036854775808) (0 + 9223372036854775808))) in KP2 by lia. cbv in KP2. discriminate KP2. }
  ths. ubs_if.
  ths. ths. rewrite (unsigned_lit num) by lia. rewrite (Z.shiftl_mul_pow2 num 3) by lia. change (2 ^ 3) with 8. ubs_if.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u8arr_store_ok_n usegs mX D junk (8 * num) 8%nat (Z_to_bv 64 (D + num * 8)) DB ltac:(lia) ltac:(rewrite LJ; lia) ltac:(unfold wa; f_equal; lia)) as SOK end.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ ?bs) _) =>
      pose proof (u8arr_write_bytes usegs mX D junk (8 * num) bs DB ltac:(lia) ltac:(rewrite length_le8; lia)) as AZ end.
  replace (D + 8 * num) with (D + num * 8) in AZ by lia.
  pose proof (upd_bytes_length junk (Z.to_nat (8 * num)) (le8 a1) ltac:(rewrite length_le8; lia)) as LJ2.
  remember (upd_bytes junk (Z.to_nat (8 * num)) (le8 a1)) as junk2 eqn:EJ2 in AZ, LJ2. apply (f_equal Z.of_nat) in LJ2. rewrite LJ in LJ2.
  clear DB. store_done. rename AZ into DB.
  ths.
  ths. ths. rewrite (unsigned_lit num) by lia. if_cases K5; zify_cond K5; [exfalso; rewrite ?Z.add_0_r in K5; rewrite ?bv_swrap_small in K5 by (change (bv_half_modulus 32) with (2 ^ 31); lia); rewrite ?SGS, ?unsigned_lit in K5 by lia; lia|]. clear K5.
  ths. ths. ths.
  destruct S01 as [-> | ->].
  - rewrite (t_sx32_small 0) by lia. th_if_lit.
    ths. ths. rewrite ?bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia). rewrite ?(t_sx32_small (num + 1)) by lia.
    do 5 ths. th_release FR (bv_unsigned sp). ths. ths. subst junk2. rewrite (bv_swrap_small 32 (num + 1)) in * by (change (bv_half_modulus 32) with (2 ^ 31); lia). finish.
  - rewrite (t_sx32_small 1) by lia. th_if_lit.
    ths. ths. if_cases K6; zify_cond K6; [exfalso; rewrite ?Z.add_0_r in K6; rewrite ?bv_swrap_small in K6 by (change (bv_half_modulus 32) with (2 ^ 31); lia); rewrite ?SGS, ?unsigned_lit in K6 by lia; lia|]. clear K6.
    ths. ths. th_if_lit.
    ths.
    ths. ths. rewrite ?bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia). rewrite ?(t_sx32_small (num + 1)) by lia.
    do 5 ths. th_release FR (bv_unsigned sp). ths. ths. subst junk2. rewrite (bv_swrap_small 32 (num + 1)) in * by (change (bv_half_modulus 32) with (2 ^ 31); lia). finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem T_sk_push_room_proof : T_sk_push_room_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  unfold T_sk_push_room_stmt. intros until junk. intros -> A0 D0 HC S01 NUM1 NUMN NAL DBC AAL DAL ST GLO LO SEPA SEPD APAD MI.
  unfold FZ_SK_PUSH, SK_PUSH_ROOM_STACK, GLOBALS_TOP, ceil_window, sk_cells in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_CB_length _ _ _ _ _ DBC) as LJ. apply (f_equal Z.of_nat) in LJ. rewrite Z2Nat.id in LJ by lia.
  apply u8arr_of_CB in DBC. rename DBC into DB.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (A, A + 56); (D, D + 8 * nalloc)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 ths.
  ths. if_cases K0; zify_cond K0. { exfalso. rewrite ?land_full in K0 by (clear - A0 SEPA LO RSP; lia). clear - K0 A0; lia. }
  ths. ths. ubs_if.
  ths. rewrite (t_sx32_small num) by lia.
  ths. ths. th_release FR (bv_unsigned sp). ths. ths.
  pose proof T_sk_insert_room_proof as X. unfold T_sk_insert_room_stmt, GLOBALS_TOP, FZ_SK_INSERT in X.
  eapply evt_cut.
  { eapply (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo A D num nalloc s01 pad cmpt freet copyt junk);
      first [reflexivity | eassumption | clear X; lia]. }
  clear X. intros ms' PO. destruct PO as (a1' & a2' & a3' & a4' & a5' & m' & -> & MUc & WMc & MIc & STc & HCc & DBc).
  apply evt_done. do 16 eexists. split; [cbv delta [mkR]; reflexivity|].
  split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. unfold sub_fp; cbn [outside]; intros; lia. }
  split; [exact (wmono_trans _ _ _ _ WM WMc)|]. split; [exact MIc|]. split; [exact STc|]. split; [exact HCc|].
  apply CB_of_u8arr in DBc. rewrite upd_bytes_length, <- (Nat2Z.id (length junk)), LJ in DBc by (rewrite length_le8; lia). exact DBc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SK_RESERVE_GROW_STACK : Z := 48 + CRE_STACK.
Definition sk_reserve_grow_res (psk pd : bptr) (A D : Z) (pad srt cmpt freet copyt : word) (src : list byte) (LBall : list block) (L : @clist bptr)
    : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (q : bptr) (D' : Z) (tail : list byte),
       v = Z_to_bv 64 1 /\ LBall' = (q, D', 48) :: lb_remove pd LBall /\ rblock_range D' 48
    /\ rw_cells usegs m' A (sk_cells (Z_to_bv 64 4) pad (Z_to_bv 64 D') srt (Z_to_bv 64 6) z64 cmpt freet copyt)
    /\ rw_cells usegs m' D' [CB 48%nat (src ++ tail)]
    /\ ((q = pd /\ D' = D /\ L' = L) \/ (exists i, nth_error L i = Some (pd, 32) /\ L' = (q, 48) :: cremove i L)).
Definition T_sk_reserve_grow_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z)
         (psk pd : bptr) (A D : Z) (pad srt cmpt freet copyt : word) (src : list byte),
    (2 <= f)%nat -> croom L (wA 48) (wB 48) (wBig 48) ->
    cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - SK_RESERVE_GROW_STACK -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 1 -> a2 = z64 ->
    In (psk, A, 56) LBall -> cown LBall L pd D 32 32 -> psk <> pd ->
    rw_cells usegs m A (sk_cells (Z_to_bv 64 4) pad (Z_to_bv 64 D) srt (Z_to_bv 64 4) z64 cmpt freet copyt) ->
    rw_cells usegs m D [CB 32%nat src] ->
    climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 FZ_SK_RESERVE) fc None m (seg_rom usegs))
           (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun q => q = psk \/ q = pd) [] 2 (wA 48) (wB 48) (wBig 48)
                  (sk_reserve_grow_res psk pd A D pad srt cmpt freet copyt src LBall L)).

Theorem T_sk_reserve_grow_spec : crypto_realloc_stmt -> T_sk_reserve_grow_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B psk pd A D
         pad srt cmpt freet copyt src Hf ROOM CST SLO -> -> -> INSK OWND NE HC BLK.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INSK) as (A0 & A16 & _ & AC & AIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWND)) as (D0 & D16 & _ & DC & DIMG).
  unfold SK_RESERVE_GROW_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK, FZ_SK_RESERVE, GLOBALS_TOP, sk_cells in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. carve_frame 48%nat ST. do 5 step. do 2 step. ths. ths. ubs_if.
  do 6 ths. th_if_lit.
  rewrite (t_sx32_small 4) by lia. ths. ths. th_if_lit.
  ths. ths. ths. th_if_lit.
  ths. ths. ths. th_if_lit.
  ths. ths. if_cases K1; zify_cond K1. { exfalso. rewrite ?land_full in K1 by (clear - D0 DC; lia). clear - K1 D0. lia. }
  ths. ths. th_if_lit. ths. th_if_lit. ths. ths. ths. ths. ths. ths. ths. ths. th_if_lit. ths. ths. ths. ths. ths. ths. th_if_lit. ths. ths. ths. ths. ths.
  step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -48) _ |- _ => rename FRh into FR end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (fun q => q = psk \/ q = pd) [] (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_seq.
  { eapply (crypto_realloc_array_spec CR) with (p := pd) (A := D) (n0 := 32) (nm := 32) (num := 6) (sz := 8) (src := src);
      [exact Hf| exact ROOM| lia| lia| unfold MMAP_THRESHOLD; lia| exact OWND| exact BLK| exact CSTc
      | rewrite unsigned_lit by lia; unfold CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity| reflexivity]. }
  change (6 * 8) with 48.
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU & GR & CST1 & FRM1 & (q & D' & tail & -> & -> & RNG & BLK1 & ALT)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (psk, A, 56) CFR1 HC INSK ltac:(intros X; exact (NE (eq_sym X)))
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as HC1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (Dn0 & Dn16 & _ & DnC & DnIMG).
  assert (INS : In (psk, A, 56) ((q, D', 48) :: lb_remove pd LBall)) by (right; apply lb_remove_In; split; [exact INSK| cbn; exact NE]).
  assert (INB : In (q, D', 48) ((q, D', 48) :: lb_remove pd LBall)) by (left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  assert (SEPB : A + 56 <= D' \/ D' + 48 <= A).
  { cbn [map] in ND1. inversion ND1 as [|hd tl NI _]; subst.
    apply (RHEAP_blocks_disjoint_proof _ _ _ (psk, A, 56) (q, D', 48) HP1 INS INB).
    unfold blk_id. cbn [fst snd]. intros E. apply NI. cbn [blk_id fst snd]. rewrite <- E. apply in_map_iff. exists (psk, A, 56). split; [reflexivity| apply lb_remove_In; split; [exact INSK| cbn; exact NE]]. }
  change (Z.to_nat 48) with 48%nat in BLK1. rewrite firstn_all2 in BLK1 by (pose proof (rw_cells_CB_length _ _ _ _ _ BLK); lia).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 56)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. ths. if_cases K3; zify_cond K3. { exfalso. rewrite ?land_full in K3 by (clear - Dn0 DnC; lia). clear - K3 Dn0. lia. }
  ths. ths. ths. do 5 step.
  release_frame FR1 ST1 (bv_unsigned sp).
  step. step. chere.
  apply climpl_done.
  lazymatch goal with |- cpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
  exists (Z_to_bv 64 1), m2, ((q, D', 48) :: lb_remove pd LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU|]. split; [exact GR|].
  split. { eapply (cstate_seg [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 56)]%Z _ _ _ _ m1 m2 _ sp tp lo B (bv_unsigned sp));
           [exact CST1| exact MU1| exact WM1| eassumption| | lia| lia| | eassumption | exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (psk, A, 56)); [exact INS| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q0 _ X E; apply X; right; symmetry; exact E]| exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (psk, A, 56)); [exact INS| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
    intros b0 _ NT E. apply NT. unfold blk_id in E |- *. cbn [fst snd] in E |- *. left. exact E. }
  exists q, D', tail. split; [reflexivity|]. split; [reflexivity|]. split; [exact RNG|]. split; [exact HC1|]. split; [exact BLK1| exact ALT].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SK_INSERT_GROW_STACK : Z := 48 + SK_RESERVE_GROW_STACK.
Definition T_sk_insert_grow_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z)
         (psk pd : bptr) (A D : Z) (pad cmpt freet copyt : word) (src : list byte),
    (2 <= f)%nat -> croom L (wA 48) (wB 48) (wBig 48) ->
    cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - SK_INSERT_GROW_STACK -> a0 = Z_to_bv 64 A -> a2 = Z_to_bv 64 4 ->
    In (psk, A, 56) LBall -> cown LBall L pd D 32 32 -> psk <> pd ->
    rw_cells usegs m A (sk_cells (Z_to_bv 64 4) pad (Z_to_bv 64 D) z64 (Z_to_bv 64 4) z64 cmpt freet copyt) ->
    rw_cells usegs m D [CB 32%nat src] ->
    climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 FZ_SK_INSERT) fc None m (seg_rom usegs))
           (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun q => q = psk \/ q = pd) [] 2 (wA 48) (wB 48) (wBig 48)
                  (sk_push_grow_res psk pd A D pad cmpt freet copyt src LBall L)).

Theorem T_sk_insert_grow_spec : crypto_realloc_stmt -> T_sk_insert_grow_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B psk pd A D
         pad cmpt freet copyt src Hf ROOM CST SLO -> -> INSK OWND NE HC BLK.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INSK) as (A0 & A16 & _ & AC & AIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWND)) as (D0 & D16 & _ & DC & DIMG).
  unfold SK_INSERT_GROW_STACK, SK_RESERVE_GROW_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK, FZ_SK_INSERT, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold sk_cells in HC.
  cprefix. step. carve_frame 48%nat ST. do 6 step. step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?land_full in K0 by (clear - A0 AC; lia). clear - K0 A0. lia. }
  step. step. step. ubs_if.
  ths. ths. ths. ths. ths. th_if_lit. ths. ths. ths. ths.
  step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (fun q => q = psk \/ q = pd) [] (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_seq.
  { eapply (T_sk_reserve_grow_spec CR) with (psk := psk) (pd := pd) (A := A) (D := D);
      [exact Hf| exact ROOM| exact CSTc| rewrite unsigned_lit by lia; unfold SK_RESERVE_GROW_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; lia
      | reflexivity| reflexivity| reflexivity| exact INSK| exact OWND| exact NE| exact HC| exact BLK]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU & GR & CST1 & FRM1 & (q & D' & tail & -> & -> & RNG & HC1 & BLK1 & ALT)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (Dn0 & Dn16 & _ & DnC & DnIMG).
  assert (INS : In (psk, A, 56) ((q, D', 48) :: lb_remove pd LBall)) by (right; apply lb_remove_In; split; [exact INSK| cbn; exact NE]).
  assert (INB : In (q, D', 48) ((q, D', 48) :: lb_remove pd LBall)) by (left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  assert (SEPB : A + 56 <= D' \/ D' + 48 <= A).
  { cbn [map] in ND1. inversion ND1 as [|hd tl NI _]; subst.
    apply (RHEAP_blocks_disjoint_proof _ _ _ (psk, A, 56) (q, D', 48) HP1 INS INB).
    unfold blk_id. cbn [fst snd]. intros E. apply NI. cbn [blk_id fst snd]. rewrite <- E. apply in_map_iff. exists (psk, A, 56). split; [reflexivity| apply lb_remove_In; split; [exact INSK| cbn; exact NE]]. }
  unfold sk_cells in HC1.
  pose proof (rw_cells_CB_length _ _ _ _ _ BLK) as LSRC.
  apply (rw_cells_split_CB usegs _ _ [] 48%nat _ _ [32; 8; 8]%nat) in BLK1; [|reflexivity].
  cbn [mk_CB_cells app] in BLK1. rewrite firstn_app, LSRC, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in BLK1 by lia.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 56); (D', D' + 48)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. ths. th_if_lit. ths. ths. ths. th_if_lit. ths. th_if_lit. ths. ths. ths. ths. ths.
  rewrite (t_sx32_small 4) by lia. rewrite (unsigned_lit 4) by lia.
  if_cases KQ1; zify_cond KQ1.
  { exfalso. rewrite (proj2 (Z.ltb_lt 0 D')), (proj2 (Z.ltb_ge (D' + 32) 1)) in KQ1 by lia. cbv in KQ1. discriminate KQ1. }
  ths. ths. ths. ths. ths.
  if_cases KQ2; zify_cond KQ2.
  { exfalso. rewrite (proj2 (Z.ltb_ge (D' + 32) D')) in KQ2 by lia. cbv in KQ2. discriminate KQ2. }
  ths. ubs_if.
  ths. ths. ubs_if.
  ths. ths. ths. ths. th_if_lit. ths. ths. ths. th_if_lit. ths. ths. ths. ths. ths. ths. ths.
  release_frame FR1 ST1 (bv_unsigned sp).
  step. step. chere.
  apply climpl_done.
  lazymatch goal with |- cpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
  exists (Z_to_bv 64 5), m2, ((q, D', 48) :: lb_remove pd LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU|]. split; [exact GR|].
  split. { eapply (cstate_seg [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 56); (D', D' + 48)]%Z _ _ _ _ m1 m2 _ sp tp lo B (bv_unsigned sp));
           [exact CST1| exact MU1| exact WM1| eassumption| | lia| lia| | eassumption | exact HB].
    - apply Forall_cons; [apply cwin_stack; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (psk, A, 56)); [exact INS| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (q, D', 48)); [exact INB| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q0 _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
    - apply (cseg_ok_block _ _ _ _ _ (psk, A, 56)); [exact INS| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      intros b0 _ NT E. apply NT. unfold blk_id in E |- *. cbn [fst snd] in E |- *. left. exact E.
    - apply (cseg_ok_block _ _ _ _ _ (q, D', 48)); [exact INB| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      cbn [map] in ND1. inversion ND1 as [|hd tl NI _]; subst.
      intros b0 Hb0 NT E. apply NI. cbn [blk_id fst snd]. unfold blk_id in E. cbn [fst snd] in E. rewrite <- E.
      apply in_map_iff. exists b0. split; [reflexivity|]. apply lb_remove_In. split; [exact Hb0|]. intros E2. apply NT. right. exact E2. }
  destruct (rw_cells_forget _ _ _ _ BLK1) as [junk' BLK2]. cbn [cells_size csize Nat.add] in BLK2.
  exists q, D', junk'. split; [reflexivity|]. split; [reflexivity|]. split; [exact RNG|]. split; [exact HC1|]. split; [exact BLK2| exact ALT].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem T_sk_push_grow_proof : crypto_realloc_stmt -> T_sk_push_grow_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  unfold T_sk_push_grow_stmt. intros CR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B psk pd A D
         pad cmpt freet copyt src Hf ROOM CST SLO -> INSK OWND NE HC BLK.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INSK) as (A0 & A16 & _ & AC & AIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWND)) as (D0 & D16 & _ & DC & DIMG).
  unfold SK_PUSH_GROW_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK, FZ_SK_PUSH, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold sk_cells in HC.
  cprefix. step. carve_frame 16%nat ST. do 3 step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?land_full in K0 by (clear - A0 AC; lia). clear - K0 A0. lia. }
  step. step. ubs_if.
  step. rewrite (t_sx32_small 4) by lia.
  do 2 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  do 2 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m1 end.
  assert (CSTc : cstate st LBall LB L m1 sp tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m1 sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FR0 : cframe (fun q => q = psk \/ q = pd) [] (bv_unsigned sp) st LBall L m st LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  eapply climpl_mono.
  { eapply (T_sk_insert_grow_spec CR) with (psk := psk) (pd := pd) (A := A) (D := D);
      [exact Hf| exact ROOM| exact CSTc| unfold SK_INSERT_GROW_STACK, SK_RESERVE_GROW_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity
      | exact INSK| exact OWND| exact NE| exact HC| exact BLK]. }
  intros f' L' s' ms'. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X].
Qed.
End WithCeiling0.
