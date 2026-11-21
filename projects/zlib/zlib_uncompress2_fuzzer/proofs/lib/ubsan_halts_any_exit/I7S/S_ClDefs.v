(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.I7S Require Import SBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Definition L_CL_HEAD : Z := 88620.
Definition L_CL_DONE : Z := 89216.

Definition s_regs_cl (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  s_fix cx Rb l /\ s_vars cx st Rb l /\ zget_l Rb l kS11 = c_q cx + t_cin st /\ zget_l Rb l kA3 = t_shave st.

Definition clhead_stmt {RCa1 : RunCtx}  : Prop :=
  forall (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem)
         (Rb : tree Z) (l : list (positive * Z)) (M : mem) (st : ist) (lf cf : Z -> Z),
    ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
    t_mode st = CODELENS -> sinv cx st lf cf ->
    s_regs_cl cx st Rb l -> k_mem cx fin M0 st lf cf M ->
    KALL cx fin MD T M0 (meas cx st) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_HEAD (zupd Rb l) M MD) T.

Definition s_regs_cld (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  s_fix cx Rb l /\ s_vars cx st Rb l /\ zget_l Rb l kS11 = c_q cx + t_cin st /\
  zget_l Rb l kA2 = t_nlen st /\ zget_l Rb l kA4 = t_nlen st + t_ndist st.

Definition cldone_stmt {RCa1 : RunCtx}  : Prop :=
  forall (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem)
         (Rb : tree Z) (l : list (positive * Z)) (M : mem) (st : ist) (lf cf : Z -> Z),
    ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
    t_mode st = CODELENS -> t_nlen st + t_ndist st <= t_shave st -> sinv cx st lf cf ->
    s_regs_cld cx st Rb l -> k_mem cx fin M0 st lf cf M ->
    KALL cx fin MD T M0 (meas cx st) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_DONE (zupd Rb l) M MD) T.
