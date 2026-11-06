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
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import X8Kit X8SRKit XL_mutex XL_cond X8_asio_stmt_alloc.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition ACEM_CTOR_STACK : Z := 144 + AFS_STACK.
Definition APEV_CTOR_STACK : Z := 144 + AFS_STACK.

Section HCW.
  Context {HCEIL : HeapCeil}.
Section W.
  Variable H : asr.

(* [comment removed for export] *)
Definition actor_W (lo : Z) (sp : word) (M ff fp : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (M, M + 56); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 256); (sh ff, sh ff + 32)]%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition acem_ctor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (M en spin : Z) (LF : list fframe) (lo shi : Z) (junk : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ff fp : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (actor_W lo sp M ff fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' M [CB 8 (firstn 8 junk)]
    /\ APMutex m' (M + 8) 0
    /\ (exists j3, rw_cells asegs m' (M + 48) [C4 (wz spin); CB 1 [b8 en]; CB 3 j3])
    /\ ACanaryReads m' /\ AXStatics2 m'
    /\ fresh_frame H LF 2 ff fp /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

Definition acem_ctor_stmt : Prop :=
  forall (M en spin lo shi : Z) (LF : list fframe) ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (junk : list byte),
  rw_cells asegs m M [CB 56 junk] -> M mod 8 = 0 ->
  aapp M 56 -> fsobj H LF M 56 -> accessible m M 56 ->
  (en = 0 \/ en = 1) -> 0 <= spin < 2^31 ->
  AXStatics2 m -> ACanaryReads m ->
  stk asegs m lo (bv_unsigned sp) -> lo + ACEM_CTOR_STACK <= bv_unsigned sp -> aceil <= lo ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  bv_unsigned sp mod 16 = 0 -> tp = Z_to_bv 64 ATP -> ACONST m -> athr_cells m ->
  as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> stack0 m lo shi ->
  evt asegs (acem_ctor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc M en spin LF lo shi junk m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz M) (wz en) (wz spin) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_CEM_CTOR) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition apev_ctor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C : Z) (LF : list fframe) (lo shi : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ff fp : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (actor_W lo sp C ff fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ APCond m' C CLOCK_MONOTONIC
    /\ rw_cells asegs m' (C + 48) [C8 (wz 0)]
    /\ ACanaryReads m' /\ AXStatics2 m'
    /\ fresh_frame H LF 2 ff fp /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

Definition apev_ctor_stmt : Prop :=
  forall (C lo shi : Z) (LF : list fframe) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (junk : list byte),
  rw_cells asegs m C [CB 56 junk] -> C mod 8 = 0 ->
  aapp C 56 -> fsobj H LF C 56 -> accessible m C 56 ->
  AXStatics2 m -> ACanaryReads m ->
  stk asegs m lo (bv_unsigned sp) -> lo + APEV_CTOR_STACK <= bv_unsigned sp -> aceil <= lo ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  bv_unsigned sp mod 16 = 0 -> tp = Z_to_bv 64 ATP -> ACONST m -> athr_cells m ->
  as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> stack0 m lo shi ->
  evt asegs (apev_ctor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc C LF lo shi m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz C) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_POSIX_EVENT_CTOR) fc None m (seg_rom asegs)).

End W.
End HCW.
