(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed ProgA AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Spec Require Import CMonad CMonadX ProgAC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Spec Require AdapterC DriverC HarnessC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AUri_kit Stdio_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AsanW Require Import CProto CProtoX.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AObj U2AIface InfAIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation rng_aimg_sh RNG := (rng RNG 0x7fffa000 0xc9c24).

Section CANSEC1. Context {rc : runConstT}.
Definition AFUZZ_ENTRY : Z := 0x8cb14.
Definition ATRUN_RET : Z := 0x8ca10.
Definition AEMPTY : Z := 0x60af20.

Definition AHARNESS_STACK : Z := 16384.

Definition harness_invA (m : amem) : Prop :=
     u2_tabsh m /\ ver_sh m
  /\ shadow_bytes m 2148242920 2148275688 (fun _ => 0)
  /\ (exists bs, rw_cells asegs m 0x60af40 [CB (Z.to_nat 262144) bs]).

Definition HU (L : alayout) : Prop :=
     (* 1.4: inflateInit2_ calls zalloc with s0 = strm + 80, and uncompress keeps s0 = destLen (a fake-frame
        address), so the init chain stops after the zalloc return and the window chains after uncompress (0x8d248) *)
     In [AMALLOC_PC; RA_INIT_ZALLOC] (al_U L)
  /\ In [AMALLOC_PC; RA_UW_ZALLOC; 0x8d11c; 0x8d278] (al_U L)
  /\ In [AMALLOC_PC; RA_UW_ZALLOC; 0x8d160; 0x8d278] (al_U L)
  /\ In [AFREE_PC; RA_END_ZFREE_W] (al_U L) /\ In [AFREE_PC; RA_END_ZFREE_S] (al_U L).

Section FuzzOneA.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Definition astk_shadow_pres (SP : Z) (m m' : amem) : Prop :=
    forall a, shad ATOP <= a < shad SP -> m' (wa a) = m (wa a).

  Definition harness_presA (LB : list ablock) (SP : Z) (m m' : amem) : Prop :=
    forall a, 0 <= a < 2^64 -> aclient_addr CI LB SP a -> ~ (0x60af40 <= a < 0x60af40 + 262144) ->
      m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

  Definition payload_atA (LB : list ablock) (D : Z) (payload : list Z) : Prop :=
    (exists p, In (HB p D (zlength payload)) LB /\ 0 < zlength payload) \/ (payload = [] /\ D = AEMPTY).

  Definition fuzz_oneA_post (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : APS) (LB : list ablock) (lo : Z) (m : amem)
      (r : Z) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : amem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ -2^31 <= r < 2^31
      /\ mem_inv asegs m' /\ frm0 fc'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ harness_presA LB (bv_unsigned sp) m m'
      /\ astk_shadow_pres (bv_unsigned sp) m m'
      /\ AHEAP AI L RNG' (aps_m s') LB m'
      /\ harness_invA m'
      /\ aps_rest s' = aps_rest s.

  Definition fuzz_oneA_stmt : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (D : Z) (payload : list Z) (lo : Z) (rstk : region),
      AHEAP AI L RNG (aps_m s) LB m ->
      (forall b, In b LB -> exists p A n, b = HB p A n) ->
      payload_atA LB D payload ->
      bytes_at asegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
      D mod 16 = 0 -> zlength payload < 2^26 ->
      harness_invA m ->
      stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AHARNESS_STACK ->
      bv_unsigned sp + 208 = al_sp0 L -> bv_unsigned sp mod 16 = 0 ->
      rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
      s0 = Z_to_bv 64 (zlength payload) ->
      mem_inv asegs m -> frm0 fc ->
      tp = Z_to_bv 64 ATP ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (zlength payload) -> ra = Z_to_bv 64 ATRUN_RET ->
      HU L ->
      rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
      aps_ok L s ->
      implMAC RNG (fuzz_oneAC AAllocAsan payload) s
             (fuzz_oneA_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 AFUZZ_ENTRY) fc None m (seg_rom asegs)).
End FuzzOneA.
End CANSEC1.
