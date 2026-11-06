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
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsIface5 AsIface6 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import X8SRKit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ADEALLOCATE_STACK : Z := AFREE_STACK.
Definition AALLOCIMPL_DESTROY_STACK : Z := AFREE_STACK.
(* [comment removed for export] *)
Definition AALLOCATE_STACK : Z := 144 + AOPNEW_STACK.

Section HCW.
  Context {HCEIL : HeapCeil}.

Section W.
  Variable H : asr.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition allocate_cost (size : Z) : Z := as_Cm H (size + 15).

Definition allocate_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (size lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (p : bptr) (A : Z) junk j7 (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ rblock_range A (size + 15) /\ as_RHEAP H s' ((p, A, size + 15) :: LB) m'
    /\ rw_cells asegs m' A [CB (Z.to_nat size) junk]
    /\ rw_cells asegs m' (A + size) (CookieCells j7)
    /\ addressable m' A (size + 15)
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) XS m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - allocate_cost size.

Definition allocate_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (size lo B shi : Z) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_ALLOCIMPL_ALLOCATE) fc None m (seg_rom asegs) ->
    a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 8 ->
    0 <= size -> size mod 8 = 0 -> size + 15 <= 2^28 ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    lb_bytes LB + (size + 15) <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AALLOCATE_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> ACONST m ->
    stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
    allocate_cost size <= as_AL H s ->
    as_SR H (allocate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF size lo B shi m mo)
      (mkCfg msF mo).

(* [comment removed for export] *)
Definition deallocate_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (p : bptr) (A size lo B : Z) (errv : word) (CH : list (Z * Z))
         (body : list cell) (j7 : list byte),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_ALLOCIMPL_DEALLOCATE) fc None m (seg_rom asegs) ->
    a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
    0 <= size -> size mod 8 = 0 -> In (p, A, size + 15) LB ->
    rw_cells asegs m A (body ++ CookieCells j7) -> Z.of_nat (cells_size body) = size ->
    addressable m A (size + 15) ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ADEALLOCATE_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 -> ACONST m ->
    as_chain H m (bv_unsigned s0) CH -> trace_ok (as_TR H) APC0_FREE (bv_unsigned ra :: map snd CH) ->
    (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->          (* [comment removed for export] *)
    as_Cf H (size + 15) <= as_AL H s ->
    as_SR H (free_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p (size + 15) lo B errv m mo)
      (mkCfg msF mo).

(* [comment removed for export] *)
Definition allocimpl_destroy_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (p : bptr) (a lo B : Z) (errv : word) (CH : list (Z * Z)) (junk : list byte),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_ALLOCIMPL_DESTROY) fc None m (seg_rom asegs) ->
    a0 = Z_to_bv 64 a ->
    In (p, a, SZ_ALLOCIMPL) LB -> rw_cells asegs m a [C8 (wz AVP_ALLOCIMPL); CB 8 junk] -> addressable m a SZ_ALLOCIMPL ->
    AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AALLOCIMPL_DESTROY_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 -> ACONST m ->
    as_chain H m (bv_unsigned s0) CH -> trace_ok (as_TR H) APC0_FREE (bv_unsigned ra :: map snd CH) ->
    (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
    as_Cf H SZ_ALLOCIMPL <= as_AL H s ->
    as_SR H (free_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p SZ_ALLOCIMPL lo B errv m mo)
      (mkCfg msF mo).

End W.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dobj_entry_ok (E : Z) : Prop := E = P_A_DEALLOC_OBJ_CONFIG \/ E = P_A_DEALLOC_OBJ_SCHED \/ E = P_A_DEALLOC_OBJ_SSVC.
Definition dobj_size (E : Z) : Z := if E =? P_A_DEALLOC_OBJ_CONFIG then SZ_CFG else if E =? P_A_DEALLOC_OBJ_SCHED then SZ_SCH else SZ_SSVC.
Definition dobj_vp (E : Z) : Z := if E =? P_A_DEALLOC_OBJ_CONFIG then AVP_CONFIG_SVC else if E =? P_A_DEALLOC_OBJ_SCHED then AVP_SCHED else AVP_SSVC.
Definition dobj_dtor (E : Z) : Z := if E =? P_A_DEALLOC_OBJ_CONFIG then P_A_NONCOPYABLE_DTOR else if E =? P_A_DEALLOC_OBJ_SCHED then P_A_SCHED_DTOR else P_A_SSVC_DTOR.
(* [comment removed for export] *)
Definition dobj_tail_ok (T size : Z) : Prop :=
  (T = P_A_DEALLOC_OBJ_CONFIG + 0x68 /\ size = SZ_CFG) \/ (T = P_A_DEALLOC_OBJ_SCHED + 0x68 /\ size = SZ_SCH)
  \/ (T = P_A_DEALLOC_OBJ_SSVC + 0x68 /\ size = SZ_SSVC) \/ (T = P_A_DEALLOC_OBJ_REGISTRY + 0x40 /\ size = SZ_REG).
Definition dobj_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].
Definition ADOBJ_STACK : Z := 32 + ADEALLOCATE_STACK.       (* [comment removed for export] *)
Definition ADALL_STACK : Z := 16 + ADOBJ_STACK.             (* [comment removed for export] *)

Definition dobj_segA_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (E p allocb lo : Z) (s2 s1 s0 ra : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 m',
    ms' = MS (mkR (Z_to_bv 64 (E + 0x68)) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 p) (Z_to_bv 64 allocb)
                  (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 (dobj_dtor E)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -32)
    /\ rw_cells asegs m' (bv_unsigned sp + -32) (dobj_frame s2 s1 s0 ra).

(* [comment removed for export] *)
Definition dobj_segA_stmt (E : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         (F : bvmap 5 word) fc (m : mem) (AT p allocb lo shi : Z),
    ro_cells asegs m AT [C8 (wz allocb)] -> bv_unsigned sp <= AT -> AT + 8 <= shi -> AT mod 8 = 0 ->
    ro_cells asegs m p [C8 (wz (dobj_vp E))] -> 0 < p -> p mod 8 = 0 -> p + 8 <= aceil -> accessible m p 8 ->
    0 <= allocb < 2^64 ->
    AXStatics2 m ->
    stk asegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> aceil <= lo ->
    mem_inv asegs m -> ACONST m -> stack0 m lo shi ->
    evt asegs (dobj_segA_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc E p allocb lo s2 s1 s0 ra m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AT) (Z_to_bv 64 p) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 E) fc None m (seg_rom asegs)).

Section W2.
  Variable H : asr.

(* [comment removed for export] *)
Definition dobj_tail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (bp : bptr) (size allocb lo B shi : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
    /\ as_RHEAP H s' (as_lb_remove H bp LB) m'
    /\ AAllocImpl (as_lb_remove H bp LB) m' allocb
    /\ AXStatics2 m'
    /\ apres H (as_lb_remove H bp LB) (bv_unsigned sp) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - as_Cf H (size + 15).

Definition dobj_tail_stmt (T size : Z) : Prop :=
  forall (pcv rax sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (s2v s1v s0v rav : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (bp : bptr) (p allocb lo B shi : Z) (errv : word)
         (body : list cell) (j7 : list byte),
    as_VIS H s msF = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 p) (Z_to_bv 64 allocb)
                             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F pcv fc None m (seg_rom asegs) ->
    (pcv = Z_to_bv 64 T \/ pcv = ret_pc (Z_to_bv 64 T)) ->
    rw_cells asegs m (bv_unsigned sp + -32) (dobj_frame s2v s1v s0v rav) ->
    In (bp, p, size + 15) LB ->
    rw_cells asegs m p (body ++ CookieCells j7) -> Z.of_nat (cells_size body) = size -> addressable m p (size + 15) ->
    AAllocImpl LB m allocb -> AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp + -32) -> aceil <= lo -> lo <= bv_unsigned sp - ADOBJ_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned rav mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    as_Cf H (size + 15) <= as_AL H s ->
    as_SR H (dobj_tail_post rav sp gp tp s0v s1v s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF bp size allocb lo B shi errv m mo)
      (mkCfg msF mo).

(* [comment removed for export] *)
Definition dealloc_obj_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (o nsz allocb lo B shi : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (bp : bptr),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
    /\ In (bp, o, nsz) LB
    /\ as_RHEAP H s' (as_lb_remove H bp LB) m'
    /\ AAllocImpl (as_lb_remove H bp LB) m' allocb
    /\ AXStatics2 m'
    /\ apres H (as_lb_remove H bp LB) (bv_unsigned sp) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - as_Cf H nsz.

Definition dealloc_obj_config_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (AT c allocb lo B shi : Z) (errv : word) (S : svch),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_DEALLOC_OBJ_CONFIG) fc None m (seg_rom asegs) ->
    a0 = Z_to_bv 64 AT -> a1 = Z_to_bv 64 c ->
    ro_cells asegs m AT [C8 (wz allocb)] -> bv_unsigned sp <= AT -> AT + 8 <= shi -> AT mod 8 = 0 ->
    AConfigSvc LB m c S -> AAllocImpl LB m allocb -> AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ADOBJ_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    as_Cf H NEWSZ_CFG <= as_AL H s ->
    as_SR H (dealloc_obj_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF c NEWSZ_CFG allocb lo B shi errv m mo)
      (mkCfg msF mo).

Definition dealloc_obj_registry_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (AT r allocb owner first lk lo B shi : Z) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_DEALLOC_OBJ_REGISTRY) fc None m (seg_rom asegs) ->
    a0 = Z_to_bv 64 AT -> a1 = Z_to_bv 64 r ->
    ro_cells asegs m AT [C8 (wz allocb)] -> bv_unsigned sp <= AT -> AT + 8 <= shi -> AT mod 8 = 0 ->
    ARegistry LB m r owner first lk -> AAllocImpl LB m allocb -> AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ADOBJ_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    as_Cf H NEWSZ_REG <= as_AL H s ->
    as_SR H (dealloc_obj_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF r NEWSZ_REG allocb lo B shi errv m mo)
      (mkCfg msF mo).

End W2.

(* [comment removed for export] *)
Definition dall_entry_ok (E' : Z) : Prop := E' = P_A_DESTROY_ALLOC_CONFIG \/ E' = P_A_DESTROY_ALLOC_SCHED \/ E' = P_A_DESTROY_ALLOC_SSVC.
Definition dall_target (E' : Z) : Z :=
  if E' =? P_A_DESTROY_ALLOC_CONFIG then P_A_DEALLOC_OBJ_CONFIG else if E' =? P_A_DESTROY_ALLOC_SCHED then P_A_DEALLOC_OBJ_SCHED else P_A_DEALLOC_OBJ_SSVC.

Definition dall_segA_post (sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (E' svc allocb lo : Z) (ra : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a2 a3 m',
    ms' = MS (mkR (Z_to_bv 64 (E' + 0x50)) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1
                  (Z_to_bv 64 (bv_unsigned sp + -16)) (Z_to_bv 64 svc) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 (dall_target E')) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 (wz allocb); C8 ra].

Definition dall_segA_stmt (E' : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         (F : bvmap 5 word) fc (m : mem) (svc ioc allocb lo : Z),
    ro_cells asegs m (svc + O_SVC_OWNER) [C8 (wz ioc)] -> 0 < svc -> svc mod 8 = 0 -> svc + 32 <= aceil -> accessible m (svc + O_SVC_OWNER) 8 ->
    ro_cells asegs m ioc [C8 (wz allocb)] -> 0 < ioc -> ioc mod 8 = 0 -> ioc + 8 <= aceil -> accessible m ioc 8 ->
    0 <= allocb < 2^64 ->
    stk asegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> aceil <= lo ->
    mem_inv asegs m -> ACONST m ->
    evt asegs (dall_segA_post sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc E' svc allocb lo ra m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 svc) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 E') fc None m (seg_rom asegs)).

Definition dall_segC_stmt (E' : Z) : Prop :=
  forall (pcv rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (atv rav : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    (pcv = Z_to_bv 64 (E' + 0x50) \/ pcv = ret_pc (Z_to_bv 64 (E' + 0x50))) ->
    rw_cells asegs m (bv_unsigned sp + -16) [C8 atv; C8 rav] ->
    stk asegs m lo (bv_unsigned sp + -16) -> lo + 16 <= bv_unsigned sp -> aceil <= lo ->
    mem_inv asegs m ->
    evt asegs (fun ms' =>
        ms' = MS (mkR rav sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc rav) fc None m (seg_rom asegs)
        /\ stk asegs m lo (bv_unsigned sp))
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F pcv fc None m (seg_rom asegs)).

Section W3.
  Variable H : asr.

(* [comment removed for export] *)
Definition destroy_alloc_config_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (c ioc allocb lo B shi : Z) (errv : word) (S : svch),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_DESTROY_ALLOC_CONFIG) fc None m (seg_rom asegs) ->
    a0 = Z_to_bv 64 c ->
    AConfigSvc LB m c S -> sv_owner S = ioc ->
    ro_cells asegs m ioc [C8 (wz allocb)] -> 0 < ioc -> ioc mod 8 = 0 -> ioc + 8 <= aceil -> accessible m ioc 8 ->
    AAllocImpl LB m allocb -> AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ADALL_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi -> bv_unsigned sp <= shi ->
    as_Cf H NEWSZ_CFG <= as_AL H s ->
    as_SR H (dealloc_obj_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF c NEWSZ_CFG allocb lo B shi errv m mo)
      (mkCfg msF mo).

End W3.
End HCW.
