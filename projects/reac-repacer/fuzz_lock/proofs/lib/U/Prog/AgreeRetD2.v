(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the twin of lib/Reusable/YO06.v (SPECX, the Copyright and SPDX lines) and of the arm statements of lib/U/Reusable/YL10_cfw.v ... YL19_cfw.v (no licence line) for a return value of the fuzz target of 0 or -1 *)
(* Donor: reac-repacer/fuzz_lock, proofs/reac-repacer/fuzz_lock/lib/Reusable/YO06.v and lib/U/Reusable/YL10_cfw.v ...
   U/Reusable/YL19_cfw.v at 901d1549395.
   Module: OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog.AgreeRetD2.
   SPECX_q ret is YO06.v SPECX with the driver leaf chosen on the payload of the input file: the kit's leaf_shapeX where
   ret is 0 on that payload, U/Prog/FrameRetD2.v leaf_shapeX_r where it is -1. The agreement step takes any shape LS, so
   the frame's rewrite LIBK LS pl fs K = K (LL (ret pl) fs []) is not at hand; on a payload where ret is 0 the kit's
   cut-free arms walk the kit's leaf_shapeX unchanged. arm_E_m1_cf / arm_M_m1_cf are the arm statements of
   YL10_cfw.v ... YL19_cfw.v for every call returning -1, with the post of U/Prog/AgreeRetD1.v
   lib_contract_x_Rc_all_r (fun _ => -1) and the leaf leaf_shapeX_r. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YH00 YH01 YH03 YH02 YN3e.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL0f YL02 YL0a YL00 YL04 YL0c YL09 YL05 YL0g YL0k YL0o YL0m YL0u YL0r YL0s.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YI06 YI16 YI14 YI5b YI5c YL0i YL06 YL03 YL0l YL0t GIWalk.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YM0b YO03 YO04 DriverSlots YI04.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0d_cf YO04_cfw YK15_cfw YL0k_cfw YL0i_cfw YL0l_cfw.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YL0u_cfw YL0r_cfw YL0t_cfw.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract AllocSI AllocGS AllocSlots SlotAgree.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import FrameRet FrameRetD1 FrameRetD2 AgreeRetD1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section q. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
(* the driver leaf on the payload of data: the kit's leaf_shapeX where ret is 0 there, leaf_shapeX_r where it is not *)
Definition leaf_shapeX_q (ret : list byte -> Z) (data : list byte) (fs : Fs) : dleaf * astate -> TSet :=
  if ret (payload data) =? 0 then leaf_shapeX data fs else leaf_shapeX_r data fs.
Definition SPECX_loaded_q (ret : list byte -> Z) (data : list byte) (fs : Fs) : TSet :=
  tset (driver_tree data) (leaf_shapeX_q ret data fs).
Definition SPECX_args_q (ret : list byte -> Z) (argv : list (list byte)) (fs : Fs) : TSet :=
  match argv with
  | [_; p] =>
    match classify_open p fs with
    | OpenFails => diag (msg_cannot_open p) fs
    | OpenDir => t_alt2 (diag (msg_cannot_open p) fs) (SPEC_dir p fs)
    | OpenFile data => t_alt2 (diag (msg_cannot_open p) fs) (SPECX_loaded_q ret data fs)
    end
  | _ => diag (msg_usage (nth 0 argv [])) fs
  end.
Definition SPECX_q (ret : list byte -> Z) (inp : ProcInput) : TSet := SPECX_args_q ret (in_argv inp) (in_fs inp).

Lemma do_jinvX_q : forall ret data fs, jinv (leaf_shapeX_q ret data fs) (driver_tree data).
Proof.
  intros ret data fs. unfold leaf_shapeX_q.
  destruct (ret (payload data) =? 0); [exact (do_jinvX_proved data fs) | exact (do_jinvX_r_proved data fs)].
Qed.

(* the shape under which the kit's leaf_shapeX on data is leaf_shapeX_q (the read loop takes the kit's leaf_shapeX) *)
Definition shape_q (ret : list byte -> Z) (data : list byte) : lib_shape :=
  if ret (payload data) =? 0 then LS else shape_at (fun fs0 => run_shape_r (LS:=LS) (payload data) (calls data) fs0).

Lemma leaf_shapeX_q_at : forall ret data fs r,
  t_eq (leaf_shapeX_q ret data fs r) (leaf_shapeX (LS:=shape_q ret data) data fs r).
Proof.
  intros ret data fs r. unfold leaf_shapeX_q, shape_q.
  destruct (ret (payload data) =? 0); [apply t_eq_refl | apply leaf_shapeX_r_at].
Qed.
End q.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
(* U/Reusable/YL10_cfw.v (and YL12_cfw ... YL15_cfw): an E arm (payload_len data = 0) with every call returning -1;
   cl0: config_len data = 0 (sQ0) or <> 0 (sQ1); k calls *)
Definition arm_E_m1_cf (cl0 : bool) (k : nat) : Prop :=
forall (API : AllocAPI src0_msyms) (AX : AllocExtra src0_msyms (aa_MR API))
  (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (RI : list byte -> nat -> list (Z * Z) -> astate -> Prop)
  (OUT : list byte -> list byte),
G_local_T src0segs src0_G GI ->
(forall mem, G_img src0segs src0_G mem -> GI 0%nat [] mem) ->
lib_contract_x_Rc_all_r src0_msyms API (fun _ => -1) RI src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK ->
(forall fx' : FPState, @free_contract_cf fx' rc src0_msyms API) ->
(forall L A mem md, aa_MR API L A mem md -> forall a, static_owned src0_msyms a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr src0segs (Z_to_bv 64 a) = true -> mbyte src0segs mem a = seg_rom src0segs (Z_to_bv 64 a)) ->
(forall pl j T A, RI pl j T A -> exists b, res_ok_slots A b) ->
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
crealizes src0_msyms (mkCfg ms md) (leaf_shapeX_r data fs (DL_run b0 cap0 None, A')).

(* U/Reusable/YL11_cfw.v (and YL16_cfw ... YL19_cfw): an M arm (0 < payload_len data) with every call returning -1 *)
Definition arm_M_m1_cf (cl0 : bool) (k : nat) : Prop :=
forall (API : AllocAPI src0_msyms) (AX : AllocExtra src0_msyms (aa_MR API))
  (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (RI : list byte -> nat -> list (Z * Z) -> astate -> Prop)
  (OUT : list byte -> list byte),
G_local_T src0segs src0_G GI ->
(forall mem, G_img src0segs src0_G mem -> GI 0%nat [] mem) ->
lib_contract_x_Rc_all_r src0_msyms API (fun _ => -1) RI src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK ->
(forall fx' : FPState, @free_contract_cf fx' rc src0_msyms API) ->
(forall L A mem md, aa_MR API L A mem md -> forall a, static_owned src0_msyms a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr src0segs (Z_to_bv 64 a) = true -> mbyte src0segs mem a = seg_rom src0segs (Z_to_bv 64 a)) ->
(forall pl j T A, RI pl j T A -> exists b, res_ok_slots A b) ->
(forall fx' : FPState, @malloc_realizes_cf fx' rc src0_msyms (aa_MR API)) ->
(forall L A mem md, aa_MR API L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md)) ->
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
(forall tr A2, cpath (malloc (payload_len data) A') tr (None, A2) -> exists b, res_ok_slots A2 b) ->
forall K : option sptr * astate -> TSet,
jinv K (malloc (payload_len data) A') -> gtree mgrant (malloc (payload_len data) A') ->
roomcf SRC_LIM_MIN (malloc (payload_len data) A') ->
(forall r, t_eq (K r) (leaf_shapeX_r data fs (payload_leaf b0 cap0 r))) ->
crealizes src0_msyms (mkCfg ms md) (tset (malloc (payload_len data) A') K).
End a.

(* The ten arms, by the kit's names: 0E1 (YL10_cfw), 0M1 (YL11_cfw), 1E1 (YL12_cfw), 1E2 (YL13_cfw), 1E3 (YL14_cfw),
   1E4 (YL15_cfw), 1M1 (YL16_cfw), 1M2 (YL17_cfw), 1M3 (YL18_cfw), 1M4 (YL19_cfw). *)
Definition arm_0E1_m1_cf : Prop := forall fx rc LS, @arm_E_m1_cf fx rc LS true 1.
Definition arm_0M1_m1_cf : Prop := forall fx rc LS, @arm_M_m1_cf fx rc LS true 1.
Definition arm_1E1_m1_cf : Prop := forall fx rc LS, @arm_E_m1_cf fx rc LS false 1.
Definition arm_1E2_m1_cf : Prop := forall fx rc LS, @arm_E_m1_cf fx rc LS false 2.
Definition arm_1E3_m1_cf : Prop := forall fx rc LS, @arm_E_m1_cf fx rc LS false 3.
Definition arm_1E4_m1_cf : Prop := forall fx rc LS, @arm_E_m1_cf fx rc LS false 4.
Definition arm_1M1_m1_cf : Prop := forall fx rc LS, @arm_M_m1_cf fx rc LS false 1.
Definition arm_1M2_m1_cf : Prop := forall fx rc LS, @arm_M_m1_cf fx rc LS false 2.
Definition arm_1M3_m1_cf : Prop := forall fx rc LS, @arm_M_m1_cf fx rc LS false 3.
Definition arm_1M4_m1_cf : Prop := forall fx rc LS, @arm_M_m1_cf fx rc LS false 4.

Definition arms_m1_cf : Prop :=
  arm_0E1_m1_cf /\ arm_0M1_m1_cf /\ arm_1E1_m1_cf /\ arm_1E2_m1_cf /\ arm_1E3_m1_cf /\ arm_1E4_m1_cf /\
  arm_1M1_m1_cf /\ arm_1M2_m1_cf /\ arm_1M3_m1_cf /\ arm_1M4_m1_cf.
