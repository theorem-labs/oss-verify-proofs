(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed ProgA AsanProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AUri_kit Stdio_kit.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation rng_aimg_sh RNG := (rng RNG 0x7fffa000 0xbce00).

Section CANSEC1. Context {rc : runConstT}.
Definition AFUZZ_ENTRY : Z := 0x8049c.
Definition ATRUN_RET : Z := 0x80398.
Definition AEMPTY : Z := 0x5d4160.

Definition AHARNESS_STACK : Z := 16384.

Definition harness_invA (m : amem) : Prop :=
     shadow_bytes m (shad 0x20fe0) (shad 0x20fe0 + 128) (fun _ => 0)
  /\ shadow_bytes m (shad 0x214e0) (shad 0x214e0 + 512) (fun _ => 0)
  /\ shadow_bytes m (shad 0x228e0) (shad 0x228e0 + 16) (fun _ => 0).

Definition HU (L : alayout) : Prop := True.

Section FuzzOneA.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Definition astk_shadow_pres (SP : Z) (m m' : amem) : Prop :=
    forall a, shad ATOP <= a < shad SP -> m' (wa a) = m (wa a).

  Definition payload_atA (LB : list ablock) (D : Z) (payload : list Z) : Prop :=
    (exists p, In (HB p D (zlength payload)) LB /\ 0 < zlength payload) \/ (payload = [] /\ D = AEMPTY).

  Definition fuzz_oneA_post (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : APS) (LB : list ablock) (lo : Z) (m : amem)
      (r : Z) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : amem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ -2^31 <= r < 2^31
      /\ mem_inv bsegs m' /\ frm0 fc'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ aheap_pres CI LB (bv_unsigned sp) m m'
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
      bytes_at bsegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
      D mod 16 = 0 -> zlength payload < 2^26 ->
      harness_invA m ->
      stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AHARNESS_STACK ->
      bv_unsigned sp + 208 = al_sp0 L -> bv_unsigned sp mod 16 = 0 ->
      rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
      s0 = Z_to_bv 64 (zlength payload) ->
      mem_inv bsegs m -> frm0 fc ->
      tp = Z_to_bv 64 ATP ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (zlength payload) -> ra = Z_to_bv 64 ATRUN_RET ->
      HU L ->
      rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
      aps_ok L s ->
      implMA RNG (fuzz_oneA AAllocAsan payload) s
             (fuzz_oneA_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 AFUZZ_ENTRY) fc None m (seg_rom bsegs)).
End FuzzOneA.
End CANSEC1.
