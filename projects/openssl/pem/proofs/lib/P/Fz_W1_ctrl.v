(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP SFModel.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Layout Str_cpy Th_kit Fz_T_kit Fz_T_ekit Fz_W1_defs Fz_W1_bits Fz_W1_bits2 Fz_W1_sync Fz_W1_write Fz_W1_misc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition W1_ctrl_ptr_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo BI BB BM RP D len max off fl PP : Z) (rmaxw flw oldpp : word) (junk : list byte),
    a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 115 -> a3 = Z_to_bv 64 PP -> 0 < BI -> 0 < PP -> PP + 8 <= 2 ^ 64 ->
    ro_cells psegs m (BI + 40) [C4 (Z_to_bv 64 1)] -> ro_cells psegs m (BI + 48) [C4 (Z_to_bv 64 fl)] -> fl_ok fl -> ro_cells psegs m (BI + 64) [C8 (Z_to_bv 64 BB)] ->
    0 < BB -> BB + 16 < 2 ^ 63 -> ro_cells psegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)] ->
    0 < BM -> rw_cells psegs m BM (bufmem_cells len D max flw) ->
    0 < RP -> rw_cells psegs m RP (readp_cells len D off rmaxw flw) ->
    0 < D -> 0 <= off <= len -> len <= max -> max < 2 ^ 31 -> D + max < 2 ^ 63 ->
    length junk = Z.to_nat max -> rw_cells psegs m D [CB (Z.to_nat max) junk] ->
    rw_cells psegs m PP [C8 oldpp] ->
    stk psegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 96 ->
    BI + 72 <= lo -> BB + 16 <= lo -> BM + 32 <= lo -> RP + 32 <= lo -> D + max <= lo ->
    (D + max <= BB \/ BB + 16 <= D) -> (D + max <= BM \/ BM + 32 <= D) -> (D + max <= RP \/ RP + 32 <= D) -> (BM + 32 <= RP \/ RP + 32 <= BM) ->
    tbox ((PP + 8 <= lo \/ bv_unsigned sp <= PP) /\ (PP + 8 <= D \/ D + max <= PP) /\ (PP + 8 <= BM \/ BM + 32 <= PP) /\ (PP + 8 <= RP \/ RP + 32 <= PP)
          /\ (BB + 16 <= BM \/ BM + 32 <= BB) /\ (BB + 16 <= RP \/ RP + 32 <= BB)) ->
    mem_inv psegs m ->
    evt psegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' rmaxw' : word) (junk' : list byte) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom psegs)
                 /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (D, D + max); (BM, BM + 8); (RP + 8, RP + 16); (PP, PP + 8)] m m'
                 /\ wmono psegs m m' /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
                 /\ rw_cells psegs m' BM (bufmem_cells (len - off) D max flw)
                 /\ rw_cells psegs m' RP (readp_cells (len - off) D 0 rmaxw' flw)
                 /\ length junk' = Z.to_nat max /\ rw_cells psegs m' D [CB (Z.to_nat max) junk']
                 /\ rw_cells psegs m' PP [C8 (Z_to_bv 64 BM)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x167aec) fc None m (seg_rom psegs)).

Theorem W1_ctrl_ptr_proof : W1_ctrl_ptr_stmt.
Proof.
  unfold W1_ctrl_ptr_stmt, bufmem_cells, readp_cells. intros until junk.
  intros -> -> -> HBI HPP HPP64 INITC FLC FLOK PTRC HBB HBB63 BBC HBM BMC HRP RPC HD HOFF HLEN HMAX HD63 LJ DBLK PPC ST LO0 LO SBI SBB SBM SRP SD APDB APDM APDR APMR BOX MI.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (D, D + max); (BM, BM + 8); (RP + 8, RP + 16); (PP, PP + 8)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold tbox in BOX. destruct BOX as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof FLOK as [FLR FLB].
  ths. th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST. do 8 ths.
  do 3 ths. ths. rewrite (t_zx32_small fl) by lia. ths. ths. rewrite (unsigned_lit fl) by lia. rewrite FLB.
  ths. ths. ths.
  change (bv_unsigned (v_sltiu (Z_to_bv 64 0) 1) ≪ 3) with 8.
  ths. ths. ths.
  ths. ths. th_if_lit. ths. ths. th_if_lit.
  ths. ths. th_if_lit. ths. ths. th_if_lit. ths.
  ths. if_cases KP; zify_cond KP. { exfalso. rewrite ?unsigned_lit in KP by lia. lia. }
  ths. th_if_lit. ths. ths.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into ma end.
  box PPC. box BBC.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (D, D + max); (BM, BM + 8); (RP + 8, RP + 16)]%Z ma) as MUs. pose proof (wmono_refl psegs ma) as WMs.
  pose proof BBC as BBCv. unbox BBCv.
  box B2. box B3. box B4. box B5. box B6.
  tcallr W1_sync_proof.
  all: try first [eassumption | lia].
  cbv beta delta [mkR]. unfold bufmem_cells, readp_cells in *.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mb end.
  unbox PPC. unbox BBC. unbox B2. unbox B3. unbox B4. unbox B5. unbox B6.
  assert (PPCb : rw_cells psegs mb PP [C8 oldpp])
    by (eapply rw_cells_transport; [exact PPC| exact MUs| exact WMs|]; clear - B1 B2 B3 B4 HPP LO; cbn [disjoint_from cells_size csize Nat.add]; lia).
  assert (BBCb : ro_cells psegs mb BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)])
    by (eapply ro_cells_transport; [exact BBC| exact MUs|]; clear - APDB B5 B6 SBB LO; cbn [disjoint_from cells_size csize Nat.add]; lia).
  clear PPC BBC MUs WMs B5 B6.
  ths. ths. ths. ths. do 7 ths.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => th_release FRh (bv_unsigned sp) end.
  ths. ths.
  apply evt_done. do 15 eexists. eexists. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  replace (D + 0) with D in * by lia.
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

(* [comment removed for export] *)
Definition W1_ctrl_ptr0_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo BI BB BM RP fl PP : Z) (lenw maxw flw rlenw rmaxw rflw oldpp : word),
    a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 115 -> a3 = Z_to_bv 64 PP -> 0 < BI -> 0 < PP -> PP + 8 <= 2 ^ 64 ->
    ro_cells psegs m (BI + 40) [C4 (Z_to_bv 64 1)] -> ro_cells psegs m (BI + 48) [C4 (Z_to_bv 64 fl)] -> fl_ok fl -> ro_cells psegs m (BI + 64) [C8 (Z_to_bv 64 BB)] ->
    0 < BB -> BB + 16 < 2 ^ 63 -> ro_cells psegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)] ->
    ro_cells psegs m BM [C8 lenw; C8 z64; C8 maxw; C8 flw] -> 0 < RP -> ro_cells psegs m RP [C8 rlenw; C8 z64; C8 rmaxw; C8 rflw] ->
    rw_cells psegs m PP [C8 oldpp] ->
    stk psegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 96 ->
    BI + 72 <= lo -> BB + 16 <= lo -> BM + 32 <= lo -> RP + 32 <= lo ->
    (PP + 8 <= lo \/ bv_unsigned sp <= PP) ->
    mem_inv psegs m ->
    evt psegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom psegs)
                 /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (PP, PP + 8)] m m'
                 /\ wmono psegs m m' /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
                 /\ rw_cells psegs m' PP [C8 (Z_to_bv 64 BM)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x167aec) fc None m (seg_rom psegs)).

Theorem W1_ctrl_ptr0_proof : W1_ctrl_ptr0_stmt.
Proof.
  unfold W1_ctrl_ptr0_stmt. intros until oldpp.
  intros -> -> -> HBI HPP HPP64 INITC FLC FLOK PTRC HBB HBB63 BBC BMC HRP RPC PPC ST LO0 LO SBI SBB SBM SRP B1 MI.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (PP, PP + 8)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof FLOK as [FLR FLB].
  ths. th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST. do 8 ths.
  do 3 ths. ths. rewrite (t_zx32_small fl) by lia. ths. ths. rewrite (unsigned_lit fl) by lia. rewrite FLB.
  ths. ths. ths.
  change (bv_unsigned (v_sltiu (Z_to_bv 64 0) 1) ≪ 3) with 8.
  ths. ths. ths.
  ths. ths. th_if_lit. ths. ths. th_if_lit.
  ths. ths. th_if_lit. ths. ths. th_if_lit. ths.
  ths. if_cases KP; zify_cond KP. { exfalso. rewrite ?unsigned_lit in KP by lia. lia. }
  ths. th_if_lit. ths. ths.
  tcallr W1_sync_nodata_proof.
  all: try first [eassumption | lia].
  cbv beta delta [mkR].
  ths. ths. ths. ths. do 7 ths.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => th_release FRh (bv_unsigned sp) end.
  ths. ths.
  apply evt_done. do 14 eexists. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.
