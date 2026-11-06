(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXRep_fields AXRep_mbuf X8_mbuf_stmt.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import N8Kit N8Kit2 N8Kit3 X8Kit X8SRKit.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape RBTac RBSafe DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mballoc_cost (n : Z) : Z := as_Cm H (mb_block_size n).

Definition mballoc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (n lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (p : bptr) (A : Z) j16 junk (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ rblock_range A (mb_block_size n) /\ as_RHEAP H s' ((p, A, mb_block_size n) :: LB) m'
    /\ rw_cells asegs m' A [CB 16 j16]
    /\ rw_cells asegs m' (A + 16) [C8 (Z_to_bv 64 n); CB (Z.to_nat (mb_block_size n - 24)) junk]
    /\ addressable m' A (mb_block_size n)
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) XS m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - mballoc_cost n.

Definition mballoc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (n lo B shi : Z) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_MB_ALLOC) fc None m (seg_rom asegs) ->
    a1 = Z_to_bv 64 n -> 1 <= n -> n <= 2^28 - 32 ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    lb_bytes LB + mb_block_size n <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - MB_ALLOC_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> ACONST m ->
    stack0 m lo shi ->
    mballoc_cost n <= as_AL H s ->
    as_SR H (mballoc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF n lo B shi m mo)
      (mkCfg msF mo).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition prep_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (res b : Z) (es : list mbe) (insz n lo B shi : Z)
    (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (p : bptr) (x : Z) (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ as_RHEAP H s' (mb_new_blocks es insz n p x ++ LB) m'
    /\ (mb_need es insz n = true -> ablock_range H x (mb_block_size (mb_grow es insz n)))
    /\ rw_cells asegs m' res [C8 (wz b); C8 (wz (mb_mid_out b es insz x)); C8 (wz (b + 8)); C8 (wz (mb_outpos es insz)); C8 (wz (mb_mid_outend es insz n))]
                                                                            (* [comment removed for export] *)
    /\ AMBmid m' b es insz n x
    /\ AMBufOwn (mb_new_blocks es insz n p x ++ LB) (mb_put_es es insz n x)
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) (((res, res + 40) :: (b, b + 64) :: mb_elemsW es) ++ XS) m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - put_cost H es insz n.

Definition prep_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (res b : Z) (es : list mbe) (insz n lo B shi : Z)
         (rj : list byte) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_MB_PREPARE) fc None m (seg_rom asegs) ->
    a0 = wz res -> a1 = wz b -> a2 = wz n ->
    AMBuf m b es insz -> AMBufOwn LB es -> 1 <= n -> insz + n <= 2^26 ->
    rw_cells asegs m res [CB 40 rj] ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    (mb_need es insz n = true -> lb_bytes LB + mb_block_size (mb_grow es insz n) <= as_LIVE_MAX H) ->
    (mb_need es insz n = true -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - MB_PREP_STACK -> bv_unsigned sp mod 16 = 0 ->
    bv_unsigned ra mod 2 = 0 ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    (* [comment removed for export] *)
    aobj LB LF b 64 ->
    aobj LB LF res 40 -> res mod 8 = 0 -> accessible m res 40 -> mb_off b es res 40 ->
    as_RFS H LF m -> (length LF + 1 < AFS_MAXLIVE)%nat -> ACONST m ->
    stack0 m lo shi -> bv_unsigned sp <= shi ->
    (mb_need es insz n = true -> as_Cm H (mb_block_size (mb_grow es insz n)) <= as_AL H s) ->
    as_SR H (prep_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF res b es insz n lo B shi m mo)
      (mkCfg msF mo).

End HCW.
