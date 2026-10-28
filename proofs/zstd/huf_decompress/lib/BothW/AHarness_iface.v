(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition AFUZZ_ENTRY : Z := 0x7ff8c.   (* [comment removed for export] *)
Definition ATRUN_RET : Z := 0x7fe88.     (* [comment removed for export] *)
Definition ATRUN_DEPTH : Z := 208.       (* [comment removed for export] *)
Definition AEMPTY : Z := 0x5ec960.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AHARNESS_STACK : Z := 16384.

(* [comment removed for export] *)
Definition harness_invA (m : amem) : Prop := True.

(* [comment removed for export] *)
End CANSEC1.
Notation rng_aimg_sh RNG := (rng RNG 0x7fffa000 0xbfe00).   (* [comment removed for export] *)
Section CANSEC1b. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition AFMALLOC_RET : Z := 0x9b19c.  (* [comment removed for export] *)
Definition AFREE_DT_RET : Z := 0x801f0.   (* [comment removed for export] *)
Definition AFREE_WK_RET : Z := 0x801f8.   (* [comment removed for export] *)
Definition AFREE_DB_RET : Z := 0x80200.   (* [comment removed for export] *)
Definition AFREEP_RET : Z := 0x80208.     (* [comment removed for export] *)
Definition HU (L : alayout) : Prop :=
     In [AMALLOC_PC; AFMALLOC_RET] (al_U L)
  /\ In [AFREE_PC; AFREE_DT_RET] (al_U L) /\ In [AFREE_PC; AFREE_WK_RET] (al_U L)
  /\ In [AFREE_PC; AFREE_DB_RET] (al_U L) /\ In [AFREE_PC; AFREEP_RET] (al_U L).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FuzzOneA.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  (* [comment removed for export] *)
  Variable rng_fs : alayout -> footprint -> Prop.
  (* [comment removed for export] *)
  Definition astk_shadow_pres (SP : Z) (m m' : amem) : Prop :=
    forall a, shad ATOP <= a < shad SP -> m' (wa a) = m (wa a).

  (* [comment removed for export] *)
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
      (* [comment removed for export] *)
      (forall b, In b LB -> exists p A n, b = HB p A n) ->
      (* [comment removed for export] *)
      payload_atA LB D payload ->
      bytes_at bsegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
      D mod 16 = 0 -> zlength payload < 2^26 ->
      (* [comment removed for export] *)
      harness_invA m ->
      (* [comment removed for export] *)
      stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AHARNESS_STACK ->
      bv_unsigned sp + ATRUN_DEPTH = al_sp0 L -> bv_unsigned sp mod 16 = 0 ->
      (* [comment removed for export] *)
      rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
      s0 = Z_to_bv 64 (zlength payload) ->
      mem_inv bsegs m -> frm0 fc ->
      tp = Z_to_bv 64 ATP ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (zlength payload) -> ra = Z_to_bv 64 ATRUN_RET ->
      (* [comment removed for export] *)
      HU L ->
      (* [comment removed for export] *)
      rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
      (* [comment removed for export] *)
      aps_ok L s ->
      implMA RNG (fuzz_oneA AAllocAsan payload) s
             (fuzz_oneA_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 AFUZZ_ENTRY) fc None m (seg_rom bsegs)).
End FuzzOneA.
End CANSEC1b.
