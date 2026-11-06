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
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import X8Kit X8SRKit XL_mutex XL_cond X8_asio_stmt_alloc X8_asio_stmt_sched2 X8_asio_stmt_sched3.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition acem_scoped_lock_post (ra sp gp tp s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (L M lo shi : Z) (j3 : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 m' j7,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -48, bv_unsigned sp); (L, L + 16); (M + 8, M + 48)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' L [C8 (wz M); CB 1 [b8 1]; CB 7 j7]
    /\ rw_cells asegs m' (M + 48) [C4 (wz 0); CB 1 [b8 1]; CB 3 j3]
    /\ APMutex m' (M + 8) EBUSY
    /\ ACONST m' /\ stack0 m' lo shi.

Definition acem_scoped_lock_stmt : Prop :=
  forall (L M lo shi : Z) (j3 jl : list byte) ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells asegs m L [CB 16 jl] -> L mod 8 = 0 -> bv_unsigned sp <= L -> L + 16 <= shi ->
  rw_cells asegs m (M + 48) [C4 (wz 0); CB 1 [b8 1]; CB 3 j3] -> APMutex m (M + 8) 0 -> 0 < M -> M mod 8 = 0 -> M + 56 <= aceil ->
  aapp M 56 -> accessible m (M + 48) 8 ->
  stk asegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> aceil <= lo ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  ACONST m -> stack0 m lo shi ->
  evt asegs (acem_scoped_lock_post ra sp gp tp s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 F fc L M lo shi j3 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz L) (wz M) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_CEM_SCOPED_LOCK) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASHUT_STACK : Z := 176 + AFS_STACK.

Definition sch_shut (S : schv) : schv := mkSCH (sch_hdr S) 0 (sch_stopped S) 1.

Section W.
  Variable H : asr.

Definition ashut_W (lo : Z) (sp : word) (S ff fp : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (S, S + SZ_SCH); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 128); (sh ff, sh ff + 16)]%Z.

Definition asched_shutdown_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (S lo shi : Z) (Sv : schv) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ff fp : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (ashut_W lo sp S ff fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ AScheduler LB m' S (sch_shut Sv) /\ as_RHEAP H s LB m'
    /\ fresh_frame H LF 1 ff fp /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

Definition asched_shutdown_stmt : Prop :=
  forall (s : as_St H) (S lo shi : Z) (LB : list block) (LF : list fframe) (Sv : schv)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  AScheduler LB m S Sv -> sch_lk Sv = 0 -> as_RHEAP H s LB m ->
  stk asegs m lo (bv_unsigned sp) -> lo + ASHUT_STACK <= bv_unsigned sp -> aceil <= lo ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  bv_unsigned sp mod 16 = 0 -> tp = Z_to_bv 64 ATP -> ACONST m ->
  as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat ->
  stack0 m lo shi -> bv_unsigned sp <= shi ->
  evt asegs (asched_shutdown_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF S lo shi Sv m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_SCHED_SHUTDOWN) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AOPQ_DTOR_STACK : Z := 176 + AFS_STACK.

Definition aopq_W (lo : Z) (sp : word) (ff fp : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 128); (sh ff, sh ff + 16)]%Z.

Definition aopq_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LF : list fframe) (lo shi : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ff fp : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (aopq_W lo sp ff fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ fresh_frame H LF 1 ff fp /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

Definition aopq_dtor_stmt : Prop :=
  forall (Q lo shi : Z) (LF : list fframe)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  ro_cells asegs m Q [C8 (wz 0)] -> aapp Q 8 -> fsobj H LF Q 8 -> accessible m Q 8 -> Q mod 8 = 0 ->
  stk asegs m lo (bv_unsigned sp) -> lo + AOPQ_DTOR_STACK <= bv_unsigned sp -> aceil <= lo ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  bv_unsigned sp mod 16 = 0 -> tp = Z_to_bv 64 ATP -> ACONST m -> athr_cells m ->
  as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> stack0 m lo shi ->
  evt asegs (aopq_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF lo shi m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz Q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_OPQUEUE_DTOR) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASCHED_DTOR_STACK : Z := 64 + AOPQ_DTOR_STACK.

Definition asdtor_W (lo : Z) (sp : word) (S ff fp : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (S, S + 8); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 128); (sh ff, sh ff + 16)]%Z.

Definition asched_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (S lo shi : Z) (Sv : schv) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ff fp : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (asdtor_W lo sp S ff fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ AScheduler LB m' S Sv /\ as_RHEAP H s LB m'
    /\ fresh_frame H LF 1 ff fp /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

Definition asched_dtor_stmt : Prop :=
  forall (s : as_St H) (S lo shi : Z) (LB : list block) (LF : list fframe) (Sv : schv)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  AScheduler LB m S Sv -> as_RHEAP H s LB m ->
  stk asegs m lo (bv_unsigned sp) -> lo + ASCHED_DTOR_STACK <= bv_unsigned sp -> aceil <= lo ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  bv_unsigned sp mod 16 = 0 -> tp = Z_to_bv 64 ATP -> ACONST m ->
  as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> stack0 m lo shi ->
  evt asegs (asched_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF S lo shi Sv m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_SCHED_DTOR) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dealloc_obj_sched_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (o allocb lo B shi : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (bp : bptr) (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
    /\ In (bp, o, NEWSZ_SCH) LB
    /\ as_RHEAP H s' (as_lb_remove H bp LB) m'
    /\ AAllocImpl (as_lb_remove H bp LB) m' allocb
    /\ AXStatics2 m'
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H (as_lb_remove H bp LB) (bv_unsigned sp) ([(o, o + NEWSZ_SCH)]%Z ++ XS) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - as_Cf H NEWSZ_SCH.

Definition dealloc_obj_sched_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (AT S allocb lo B shi : Z) (errv : word) (Sv : schv),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_DEALLOC_OBJ_SCHED) fc None m (seg_rom asegs) ->
    a0 = Z_to_bv 64 AT -> a1 = Z_to_bv 64 S ->
    ro_cells asegs m AT [C8 (wz allocb)] -> bv_unsigned sp <= AT -> AT + 8 <= shi -> AT mod 8 = 0 ->
    AScheduler LB m S Sv -> AAllocImpl LB m allocb -> AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ADOBJ_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> ACONST m -> stack0 m lo shi ->
    as_Cf H NEWSZ_SCH <= as_AL H s ->
    as_SR H (dealloc_obj_sched_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF S allocb lo B shi errv m mo)
      (mkCfg msF mo).

(* [comment removed for export] *)
Definition destroy_alloc_sched_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (S ioc allocb lo B shi : Z) (errv : word) (Sv : schv),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_DESTROY_ALLOC_SCHED) fc None m (seg_rom asegs) ->
    a0 = Z_to_bv 64 S ->
    AScheduler LB m S Sv -> sv_owner (sch_hdr Sv) = ioc ->
    ro_cells asegs m ioc [C8 (wz allocb)] -> 0 < ioc -> ioc mod 8 = 0 -> ioc + 8 <= aceil -> accessible m ioc 8 ->
    AAllocImpl LB m allocb -> AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ADALL_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> ACONST m -> stack0 m lo shi -> bv_unsigned sp <= shi ->
    as_Cf H NEWSZ_SCH <= as_AL H s ->
    as_SR H (dealloc_obj_sched_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF S allocb lo B shi errv m mo)
      (mkCfg msF mo).

End W.
End HCW.
