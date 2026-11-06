(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsImgSh AsIface AsIface5 AsIface6 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import X8Kit X8SRKit X8_asio_stmt_alloc.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Inductive cfgkey := KChint | KAcont | KLocking | KSpin | KTask | KWait.
Definition akey_lit (k : cfgkey) : Z :=
  match k with
  | KChint => AL_STR_CONCURRENCY_HINT | KAcont => AL_STR_ASSUME_CONT | KLocking => AL_STR_LOCKING
  | KSpin => AL_STR_SPIN | KTask => AL_STR_TASK_USEC | KWait => AL_STR_WAIT_USEC
  end.
Definition gv_res (k : cfgkey) (buf : Z) : Z :=
  match k with KChint => buf | KLocking => AL_STR_ONE | _ => 0 end.
Definition gv_buf (k : cfgkey) (junk : list byte) : list cell :=
  match k with
  | KChint => [C1 (Z_to_bv 8 45); C1 (Z_to_bv 8 49); C1 (Z_to_bv 8 0); CB 19 (skipn 3 junk)]
  | _ => [CB 22 junk]
  end.
(* [comment removed for export] *)
Definition gv_null (k : cfgkey) : bool := match k with KChint | KLocking => false | _ => true end.

(* [comment removed for export] *)
Definition AGET_VALUE_STACK : Z := 64 + ASNPRINTF_STACK.
(* [comment removed for export] *)
Definition ACONFIG_GET_STACK : Z := 112 + AGET_VALUE_STACK.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition get_value_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (k : cfgkey) (buf lo shi : Z) (junk : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (gv_res k buf)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (buf, buf + 22)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' buf (gv_buf k junk)
    /\ rw_cells asegs m' (sh (buf - 32)) [C8 (wz ASNP_HEAD)]
    /\ ACONST m' /\ stack0 m' lo shi /\ acanary m'.

Definition get_value_stmt (k : cfgkey) : Prop :=
  forall (c buf lo shi : Z) ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (junk : list byte),
  F = bvmap_empty -> fc = Z_to_bv 32 0 ->
  (* [comment removed for export] *)
  ro_cells asegs m (c + O_CFG_HINT) [C4 (wz 4294967295)] -> c mod 8 = 0 -> 0 < c -> c + SZ_CFG <= aceil -> accessible m (c + O_CFG_HINT) 8 ->
  (* [comment removed for export] *)
  rw_cells asegs m buf [CB 22 junk] -> buf mod 64 = 32 -> aapp (buf - 32) 64 -> buf + 32 <= aceil ->
  rw_cells asegs m (sh (buf - 32)) [C8 (wz ASNP_HEAD)] ->
  bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 0x7fffffffffff ->
  stk asegs m lo (bv_unsigned sp) -> lo + AGET_VALUE_STACK <= bv_unsigned sp -> aceil <= lo ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  ACONST m -> stack0 m lo shi -> bv_unsigned sp <= shi -> acanary m ->
  evt asegs (get_value_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc k buf lo shi junk m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz c) (wz AL_STR_SCHEDULER) (wz (akey_lit k)) (wz buf) (wz 22) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_CONFIG_GET_VALUE) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ACG_FSZ : Z := 256.   (* [comment removed for export] *)
Definition ACG_FSHN : Z := 32.   (* [comment removed for export] *)

Section W.
  Variable H : asr.

Definition cg_W (lo : Z) (sp : word) (ff fp : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + ACG_FSZ); (sh ff, sh ff + ACG_FSHN); (AERRNO, AERRNO + 4)]%Z.

Definition cg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (res errv' : word) (LF : list fframe) (lo shi : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ff fp : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 res a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (cg_W lo sp ff fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned tp + -164) [C4 errv']
    /\ fresh_frame H LF 2 ff fp /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi /\ acanary m' /\ AXStatics2 m'.

(* [comment removed for export] *)
Definition cg_stmt (pc : Z) (k : cfgkey) (dflt res : word) (errz : bool) : Prop :=
  forall (c lo shi : Z) (LF : list fframe) ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (errv : word),
  F = bvmap_empty -> fc = Z_to_bv 32 0 ->
  (* [comment removed for export] *)
  ro_cells asegs m c [C8 (wz AVP_CONFIG_SVC)] -> ro_cells asegs m (c + O_CFG_HINT) [C4 (wz 4294967295)] ->
  aapp c SZ_CFG -> fsobj H LF c SZ_CFG -> accessible m c SZ_CFG -> c mod 16 = 0 ->
  AXStatics2 m ->
  rw_cells asegs m (bv_unsigned tp + -164) [C4 errv] -> tp = Z_to_bv 64 ATP ->
  bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 0x7fffffffffff ->
  stk asegs m lo (bv_unsigned sp) -> lo + ACONFIG_GET_STACK <= bv_unsigned sp -> aceil <= lo ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  ACONST m -> athr_cells m -> as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat ->
  stack0 m lo shi -> bv_unsigned sp <= shi -> acanary m ->
  evt asegs (cg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc res (if errz then wz 0 else errv) LF lo shi m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz c) (wz AL_STR_SCHEDULER) (wz (akey_lit k)) dflt (wz 0) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition cg_int_chint_stmt : Prop := forall dflt : word, cg_stmt P_A_CONFIG_GET_INT KChint dflt (wz 18446744073709551615) true.
Definition cg_int_default_stmt (k : cfgkey) : Prop :=
  forall d : Z, gv_null k = true -> 0 <= d < 2^31 -> cg_stmt P_A_CONFIG_GET_INT k (wz d) (wz d) false.
Definition cg_bool_locking_stmt : Prop := forall dflt : word, cg_stmt P_A_CONFIG_GET_BOOL KLocking dflt (wz 1) true.
Definition cg_bool_default_stmt (k : cfgkey) : Prop :=
  forall dflt : word, gv_null k = true -> cg_stmt P_A_CONFIG_GET_BOOL k dflt dflt false.
Definition cg_long_default_stmt (k : cfgkey) : Prop :=
  forall dflt : word, gv_null k = true -> cg_stmt P_A_CONFIG_GET_LONG k dflt dflt false.

End W.
End HCW.
