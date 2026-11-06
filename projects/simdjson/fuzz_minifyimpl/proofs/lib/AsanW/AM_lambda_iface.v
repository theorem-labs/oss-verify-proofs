(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase ARep AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_parts_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AM_kitA AM_kitB AM_iface AM_model.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition ALAMBDA : Z := 0xb1b84.           (* [comment removed for export] *)
Definition ALAM_STRDEL_RET : Z := 0xb1df0.   (* [comment removed for export] *)
Definition ALAMBDA_STACK : Z := 4352.        (* [comment removed for export] *)

Section S.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Variable K : ALooseKit AI fflag rng_fs.

  Definition lambda_post (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : APS) (LB : list ablock) (R C D : Z) (payload : list Z) (lo : Z) (m : amem)
      (b' : option AsanCtrl.aptr) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem) (beg k cap : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ aps_rest s' = aps_rest s /\ aps_cl s' = aps_cl s
      (* [comment removed for export] *)
      /\ aheap_pres_x CI LB (bv_unsigned sp) R 24 m m'
      /\ harness_invA m'
      (* [comment removed for export] *)
      /\ rw_cells asegs m' C [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 (zlength payload))]
      /\ rw_cells asegs m' (shad C) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
      (* [comment removed for export] *)
      /\ rw_cells asegs m' R [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 (beg + k)); C8 (Z_to_bv 64 (beg + cap))]
      /\ rw_cells asegs m' (shad R) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
      /\ 0 <= k <= cap
      /\ match b' with
         | None =>   (* [comment removed for export] *)
             beg = 0 /\ cap = 0 /\ AHEAP AI L RNG' (aps_m s') LB m'
         | Some p => (* [comment removed for export] *)
             0 < cap <= AREQMAX /\ ablock_range beg cap
             /\ AHL AI fflag rng_fs K (lk_setb AI fflag rng_fs K L p beg cap (Some (vpat cap k))) RNG' (aps_m s') (HB p beg cap :: LB) m'
             /\ rw_cells asegs m' (shad beg) [CB (Z.to_nat (granules cap)) (vpat cap k)]
             /\ rng RNG' beg cap /\ rng RNG' (shad beg) (granules cap)
         end.

  Definition lambda_stmt : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (lo R C D : Z) (payload : list Z) (r0 r1 r2 : word) (cls FA FN RLO2 RHI2 : Z) (tr : list Z),
      AHEAP AI L RNG (aps_m s) LB m ->
      (forall F1 n1, ~ In (mkABlock (ABFake 1) F1 n1) LB) ->          (* [comment removed for export] *)
      (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b mod 8 = 0) ->
                                                                          (* [comment removed for export] *)
      mem_inv asegs m ->
      stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ALAMBDA_STACK ->
      bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 32 = 0 ->
      tp = Z_to_bv 64 ATP ->
      (* [comment removed for export] *)
      payload_atA LB D payload ->
      bytes_at asegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
      D mod 16 = 0 -> zlength payload < 2^26 ->
      (* [comment removed for export] *)
      In (mkABlock (ABFake cls) FA FN) LB -> FA <= R -> R + 24 <= FA + FN -> R mod 8 = 0 -> ablk R (R + 24) ->
      rw_cells asegs m R [C8 r0; C8 r1; C8 r2] ->
      rw_cells asegs m (shad R) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
      FA <= RLO2 -> RLO2 <= R -> R + 24 <= RHI2 -> RHI2 <= FA + FN -> RLO2 mod 64 = 0 -> RHI2 mod 64 = 0 ->
      wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
      (* [comment removed for export] *)
      bv_unsigned sp <= C -> C + 16 <= 2^47 -> C mod 16 = 0 ->
      rw_cells asegs m C [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 (zlength payload))] ->
      rw_cells asegs m (shad C) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
      (* [comment removed for export] *)
      rw_cells asegs m AFALLBACK [C8 (Z_to_bv 64 AFALLBACK_VT)] ->
      harness_invA m ->
      (* [comment removed for export] *)
      In [AMALLOC_PC; AOPNEW_RET] (al_U L) -> In [AFREE_PC; 0xb2e04] (al_U L) ->
      bv_unsigned sp + 16 <= bv_unsigned s0 ->                                (* [comment removed for export] *)
      uchain m (al_top L) AFREE_PC (bv_unsigned sp) (bv_unsigned s0) (Nat.pred UDEPTH) tr ->
      In (AFREE_PC :: ALAM_STRDEL_RET :: bv_unsigned ra :: tr) (al_U L) -> (length tr <= 27)%nat ->
      4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
      (* [comment removed for export] *)
      rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
      rng RNG R 24 -> rng RNG (shad R) 3 -> rng RNG C 16 -> rng RNG (shad C) 2 ->
      aps_ok L s ->
      a0 = Z_to_bv 64 R -> a1 = Z_to_bv 64 C -> a2 = Z_to_bv 64 AFALLBACK ->
      implMA RNG (lamA payload) s
             (lambda_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB R C D payload lo m)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 ALAMBDA) fc None m (seg_rom asegs)).
End S.
End CANSEC1.
