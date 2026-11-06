(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the -1 twins of the arm statements of lib/U/Reusable/YL10.v ... lib/U/Reusable/YL19.v (return value of the fuzz target 0 or -1) *)
(* Donor: reac-repacer/fuzz_lock, proofs/reac-repacer/fuzz_lock/lib/U/Reusable/YL10.v ... U/Reusable/YL19.v (the arm
   statements) at 901d1549395.
   Module: OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog.FrameRetD3. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YH00 YH01 YH03 YH02 YN3e.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL0f YL02 YL0a YL00 YL04 YL0c YL09 YL05 YL0g YL0k YL0o YL0m YL0u YL0r YL0s.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YI06 YI16 YI14 YI5b YI5c YL0i YL06 YL03 YL0l YL0t GIWalk.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import FrameRet FrameRetD1 FrameRetD2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
(* an E arm (empty payload: payload_len data = 0) with every call returning -1; cl0: config_len data = 0 (sQ0) or
   config_len data <> 0 (sQ1); k calls *)
Definition arm_E_m1 (cl0 : bool) (k : nat) : Prop :=
forall (API : AllocAPI src0_msyms) (AX : AllocExtra src0_msyms (aa_MR API))
  (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (RI : list byte -> nat -> list (Z * Z) -> astate -> Prop)
  (OUT : list byte -> list byte),
G_local_T src0segs src0_G GI ->
(forall mem, G_img src0segs src0_G mem -> GI 0%nat [] mem) ->
lib_contract_x_R_all_r src0_msyms API (fun _ => -1) RI src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK ->
frm_zero fp_csr ->
forall (data : list byte) (fs : Fs) (cap0 : Z) (L' : layout) (A' : astate) (b0 : sptr),
user_blocks A' = [(b0, cap0)] -> 65536 <= cap0 <= 67108864 ->
WF A' -> bounded A' -> st_init_done A' = true ->
6 + config_len data <= dlen data -> dlen data < cap0 ->
(if cl0 then config_len data = 0 else config_len data <> 0) ->
calls data = k -> payload_len data = 0 ->
forall E ms md,
run_env E data (ptr_addr L' b0) -> env_top E ->
st_ok src0segs E (if cl0 then sQ0 else sQ1) ms -> aa_MR API L' A' (ms_mem ms) md -> md_invX fs md ->
RI (payload data) 0%nat [] A' ->
realizes src0segs (mkCfg ms md) (leaf_shapeX_r data fs (DL_run b0 cap0 None, A')).

(* an M arm (malloc'd payload: 0 < payload_len data) with every call returning -1 *)
Definition arm_M_m1 (cl0 : bool) (k : nat) : Prop :=
forall (API : AllocAPI src0_msyms) (AX : AllocExtra src0_msyms (aa_MR API))
  (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (RI : list byte -> nat -> list (Z * Z) -> astate -> Prop)
  (OUT : list byte -> list byte),
G_local_T src0segs src0_G GI ->
(forall mem, G_img src0segs src0_G mem -> GI 0%nat [] mem) ->
lib_contract_x_R_all_r src0_msyms API (fun _ => -1) RI src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK ->
frm_zero fp_csr ->
forall (data : list byte) (fs : Fs) (cap0 : Z) (L' : layout) (A' : astate) (b0 : sptr),
user_blocks A' = [(b0, cap0)] -> 65536 <= cap0 <= 67108864 ->
WF A' -> bounded A' -> st_init_done A' = true ->
6 + config_len data <= dlen data -> dlen data < cap0 ->
(if cl0 then config_len data = 0 else config_len data <> 0) ->
calls data = k -> 0 < payload_len data ->
forall E ms md,
run_env E data (ptr_addr L' b0) -> env_top E ->
st_ok src0segs E (if cl0 then sQ0 else sQ1) ms -> aa_MR API L' A' (ms_mem ms) md -> md_invX fs md ->
blk_data src0_msyms (ms_mem ms) (ptr_addr L' b0) data ->
(forall tr q A2, cpath (malloc (payload_len data) A') tr (Some q, A2) -> RI (payload data) 0%nat [] A2) ->
forall K : option sptr * astate -> TSet,
jinv K (malloc (payload_len data) A') -> gtree mgrant (malloc (payload_len data) A') ->
(forall r, t_eq (K r) (leaf_shapeX_r data fs (payload_leaf b0 cap0 r))) ->
realizes src0segs (mkCfg ms md) (tset (malloc (payload_len data) A') K).
End a.

(* The ten arms, by the kit's names: 0E1 (YL10), 0M1 (YL11), 1E1 (YL12), 1E2 (YL13), 1E3 (YL14), 1E4 (YL15),
   1M1 (YL16), 1M2 (YL17), 1M3 (YL18), 1M4 (YL19). *)
Definition arm_0E1_m1 : Prop := forall fx rc LS, @arm_E_m1 fx rc LS true 1.
Definition arm_0M1_m1 : Prop := forall fx rc LS, @arm_M_m1 fx rc LS true 1.
Definition arm_1E1_m1 : Prop := forall fx rc LS, @arm_E_m1 fx rc LS false 1.
Definition arm_1E2_m1 : Prop := forall fx rc LS, @arm_E_m1 fx rc LS false 2.
Definition arm_1E3_m1 : Prop := forall fx rc LS, @arm_E_m1 fx rc LS false 3.
Definition arm_1E4_m1 : Prop := forall fx rc LS, @arm_E_m1 fx rc LS false 4.
Definition arm_1M1_m1 : Prop := forall fx rc LS, @arm_M_m1 fx rc LS false 1.
Definition arm_1M2_m1 : Prop := forall fx rc LS, @arm_M_m1 fx rc LS false 2.
Definition arm_1M3_m1 : Prop := forall fx rc LS, @arm_M_m1 fx rc LS false 3.
Definition arm_1M4_m1 : Prop := forall fx rc LS, @arm_M_m1 fx rc LS false 4.

Definition arms_m1 : Prop :=
  arm_0E1_m1 /\ arm_0M1_m1 /\ arm_1E1_m1 /\ arm_1E2_m1 /\ arm_1E3_m1 /\ arm_1E4_m1 /\
  arm_1M1_m1 /\ arm_1M2_m1 /\ arm_1M3_m1 /\ arm_1M4_m1.
