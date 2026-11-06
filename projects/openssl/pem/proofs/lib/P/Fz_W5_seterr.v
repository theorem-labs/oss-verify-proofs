(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac Arr SysStep.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.openssl.pem.lib.MallocP Require Import RMallocRep.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Layout Th_kit Th_key Th_errno Fz_T_kit Fz_T_local Fz_T_once Fz_T_sa Fz_T_master Fz_I3_base Fz_W5_glx Fz_W5_gsi Fz_W5_defs Fz_W5_vset.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition FZ_SETERR : Z := 0xe256c.
Definition SETERR_STACK : Z := 80 + VSET_STACK.

Definition T_set_error_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T k MK SA NODES E lib reason top bot : Z) (errv od pad tw ne : word)
         (fl mk buf fs ls fn : list word),
    a0 = Z_to_bv 64 lib -> a1 = Z_to_bv 64 reason -> a2 = z64 -> 0 < lib < 256 -> lib <> 2 -> 0 < reason < 2 ^ 31 ->
    164 <= bv_unsigned tp ->
    (* [comment removed for export] *)
    rw_cells psegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] -> rw_cells psegs m (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] -> rw_cells psegs m (IC_S + 96) [C8 od] ->
    ro_cells psegs m 0x2e8704 [C4 (Z_to_bv 64 2)] ->
    ro_cells psegs m 0x2e8708 [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
    ro_cells psegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 0 <= T ->
    ro_cells psegs m (T + 8 * k) [C8 (Z_to_bv 64 MK)] -> 0 < MK < 2 ^ 64 ->
    ro_cells psegs m (MK + 8 * 3) [C8 (Z_to_bv 64 SA)] -> 0 < SA < 2 ^ 64 ->
    ro_cells psegs m SA (sa_hdr (Z_to_bv 64 1) pad tw ne (Z_to_bv 64 NODES)) -> 0 < NODES < 2 ^ 64 ->
    ro_cells psegs m NODES [C8 (Z_to_bv 64 E)] -> bv_unsigned ne <> 0 ->
    rw_cells psegs m (bv_unsigned tp + -164) [C4 errv] ->
    (* [comment removed for export] *)
    es_rep m E top bot fl mk buf fs ls fn -> 0 < E -> E mod 8 = 0 -> (E + 904 <= 0x10000 \/ 0x30d000 <= E) -> bv_unsigned tp = RATP ->
    stk psegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - SETERR_STACK ->
    0x2e8708 + 4 <= lo -> IC_S + 104 <= lo -> E + 904 <= lo ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -164) ->
    (T + 8 * k + 8 <= lo \/ bv_unsigned sp <= T + 8 * k) ->
    (MK + 8 * 3 + 8 <= lo \/ bv_unsigned sp <= MK + 8 * 3) ->
    (SA + 32 <= lo \/ bv_unsigned sp <= SA) ->
    (NODES + 8 <= lo \/ bv_unsigned sp <= NODES) ->
    mem_inv psegs m ->
    evt psegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (buf' : list word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom psegs)
                 /\ munch [(bv_unsigned sp - SETERR_STACK, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160); (E + 128, E + 576)] m m'
                 /\ wmono psegs m m' /\ mem_inv psegs m'
                 /\ rw_cells psegs m' (bv_unsigned tp + -164) [C4 (sx32 errv)]
                 /\ stk psegs m' lo (bv_unsigned sp)
                 /\ es_rep m' E top bot fl mk buf' fs ls fn)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FZ_SETERR) fc None m (seg_rom psegs)).

Theorem T_set_error_proof : T_set_error_stmt.
Proof.
  unfold T_set_error_stmt, SETERR_STACK, VSET_STACK, GSI_STACK, FZ_SETERR, sa_hdr. intros until fn.
  intros -> -> -> HLIB HLIB2 HREA TP STOP ONCE OD OC KC HK TS T0 MKC HMK SAC HSA HC HNO VC NE0 ERR ES E0 EAL EIMG TPV ST GLO LO S6 S7 SE S0 S1 S2 S3 S4 MI.
  unfold IC_S, GLOBALS_TOP, RATP in *. change (80 + (80 + (48 + 96)))%Z with 304%Z in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB). clear ES.
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (ro_cells_bound _ _ _ _ MKC) as MKB. cbn [cells_size csize Nat.add] in MKB.
  pose proof (ro_cells_bound _ _ _ _ SAC) as SAB. cbn [cells_size csize Nat.add] in SAB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160); (E + 128, E + 576)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  set (Pk := T + 8 * k) in *. set (P3 := MK + 8 * 3) in *.
  th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  (* [comment removed for export] *)
  do 4 ths. do 5 ths. ths. ths. ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (ES1 : es_rep mX E top bot fl mk buf fs ls fn) by (unfold es_rep; repeat (split; [first [eassumption | lia]|]); lia) end.
  pose proof T_vset_error_proof as VSE. unfold T_vset_error_stmt, VSET_STACK, GSI_STACK, sa_hdr, IC_S, GLOBALS_TOP, RATP in VSE.
  tcall (VSE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T k MK SA NODES E lib reason top bot errv od pad tw ne fl mk buf fs ls fn).
  all: try first [eassumption | reflexivity | lia].
  clear VSE. cbv beta delta [mkR].
  (* [comment removed for export] *)
  ths. ths. th_release FR (bv_unsigned sp). ths. ths.
  apply evt_done. do 17 eexists. split; [cbv delta [mkR]; rewrite ?(Z_to_bv_bv_unsigned sp); reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  lazymatch goal with H : es_rep _ E top bot fl mk _ fs ls fn |- _ => exact H end.
Qed.
End WithCeiling0.
