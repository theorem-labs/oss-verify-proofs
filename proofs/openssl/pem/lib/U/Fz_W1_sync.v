(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Str_memmove. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_W1_defs Fz_W1_bits.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Definition readp_cells (len D off : Z) (rmaxw flw : word) : list cell := [C8 (Z_to_bv 64 (len - off)); C8 (Z_to_bv 64 (D + off)); C8 rmaxw; C8 flw].

Definition W1_sync_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo BI BB BM RP D len max off : Z) (rmaxw flw : word) (junk : list byte),
    a0 = Z_to_bv 64 BI -> 0 < BI ->
    ro_cells usegs m (BI + 40) [C4 (Z_to_bv 64 1)] -> ro_cells usegs m (BI + 64) [C8 (Z_to_bv 64 BB)] ->
    0 < BB -> ro_cells usegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)] ->
    0 < BM -> rw_cells usegs m BM (bufmem_cells len D max flw) ->
    0 < RP -> rw_cells usegs m RP (readp_cells len D off rmaxw flw) ->
    0 < D -> 0 <= off <= len -> len <= max -> max < 2 ^ 31 -> D + max < 2 ^ 63 -> length junk = Z.to_nat max -> rw_cells usegs m D [CB (Z.to_nat max) junk] ->
    BI mod 8 = 0 -> BB mod 8 = 0 -> BM mod 8 = 0 -> RP mod 8 = 0 ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 32 ->
    BI + 72 <= lo -> BB + 16 <= lo -> BM + 32 <= lo -> RP + 32 <= lo -> D + max <= lo ->
    (D + max <= BB \/ BB + 16 <= D) -> (D + max <= BM \/ BM + 32 <= D) -> (D + max <= RP \/ RP + 32 <= D) -> (BM + 32 <= RP \/ RP + 32 <= BM) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' rmaxw' : word) (junk' : list byte) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (D, D + max); (BM, BM + 8); (RP + 8, RP + 16)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' BM (bufmem_cells (len - off) D max flw)
                 /\ rw_cells usegs m' RP (readp_cells (len - off) D 0 rmaxw' flw)
                 /\ length junk' = Z.to_nat max /\ rw_cells usegs m' D [CB (Z.to_nat max) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x183ad0) fc None m (seg_rom usegs)).

Theorem W1_sync_proof : W1_sync_stmt.
Proof.
  unfold W1_sync_stmt, bufmem_cells, readp_cells. intros until junk.
  intros -> HBI INITC PTRC HBB BBC HBM BMC HRP RPC HD HOFF HLEN HMAX HD63 LJ DBLK ALBI ALBB ALBM ALRP ST LO0 LO SBI SBB SBM SRP SD APDB APDM APDR APMR MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (D, D + max); (BM, BM + 8); (RP + 8, RP + 16)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  ths. th_frame 32%nat [8; 8; 8; 8]%nat ST. do 4 ths.
  ths. ths. ubs_if.
  ths. rewrite (t_sx32_small 1) by lia. ths. th_if_lit.
  ths. ths. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ubs_if.
  ths. ths.
  ths. if_cases K2; zify_cond K2.
  - (* [comment removed for export] *)
    assert (off = 0) by lia. subst off.
    do 3 ths.
    lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ => th_release FRh (bv_unsigned sp) end.
    ths. ths.
    replace (len - 0) with len in * by lia. replace (D + 0) with D in * by lia.
    apply evt_done. do 16 eexists. exists junk. eexists. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; [replace (len - 0) with len by lia; eassumption|]. split; [exact LJ| exact DBLK].
  - (* [comment removed for export] *)
    ths. ths.
    rewrite <- LJ in DBLK.
    tcall (memmove_fwd_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ junk off).
    all: try first [eassumption | lia].
    cbv beta delta [mkR].
    ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ubs_if.
    ths. ths. ths. ths.
    do 3 ths.
    lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ => th_release FRh (bv_unsigned sp) end.
    ths. ths.
    apply evt_done. do 16 eexists. exists (mv_cur (Z.to_nat off) junk (Z.to_nat (len - off))). eexists. split; [cbv delta [mkR]; reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; [replace (len - off - 0) with (len - off) by lia; replace (D + 0) with D by lia; eassumption|].
    split; [rewrite mv_cur_length by lia; exact LJ|].
    rewrite <- LJ. eassumption.
Qed.

(* [comment removed for export] *)
Definition W1_sync_nodata_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo BI BB BM RP : Z) (lenw maxw flw rlenw rmaxw rflw : word),
    a0 = Z_to_bv 64 BI -> 0 < BI ->
    ro_cells usegs m (BI + 40) [C4 (Z_to_bv 64 1)] -> ro_cells usegs m (BI + 64) [C8 (Z_to_bv 64 BB)] ->
    0 < BB -> ro_cells usegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)] ->
    ro_cells usegs m BM [C8 lenw; C8 z64; C8 maxw; C8 flw] -> ro_cells usegs m RP [C8 rlenw; C8 z64; C8 rmaxw; C8 rflw] ->
    0 < BM -> 0 < RP -> BI mod 8 = 0 -> BB mod 8 = 0 -> BM mod 8 = 0 -> RP mod 8 = 0 ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 32 ->
    BI + 72 <= lo -> BB + 16 <= lo -> BM + 32 <= lo -> RP + 32 <= lo ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x183ad0) fc None m (seg_rom usegs)).

Theorem W1_sync_nodata_proof : W1_sync_nodata_stmt.
Proof.
  unfold W1_sync_nodata_stmt. intros until rflw.
  intros -> HBI INITC PTRC HBB BBC BMC RPC HBM HRP ALBI ALBB ALBM ALRP ST LO0 LO SBI SBB SBM SRP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  ths. th_frame 32%nat [8; 8; 8; 8]%nat ST. do 4 ths.
  ths. ths. ubs_if.
  ths. rewrite (t_sx32_small 1) by lia. ths. th_if_lit.
  ths. ths. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ubs_if. ths. ths. ubs_if.
  ths. ths.
  ths. th_if_lit.
  do 3 ths.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ => th_release FRh (bv_unsigned sp) end.
  ths. ths. finish.
Qed.
