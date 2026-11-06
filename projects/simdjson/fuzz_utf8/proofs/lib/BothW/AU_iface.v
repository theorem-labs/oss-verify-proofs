(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg RtCells AProto AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import AU_kit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition AGOT_SHBASE : Z := 0x171ff8. (* [comment removed for export] *)
Definition AGOT_SUAR : Z := 0x172050.   (* [comment removed for export] *)
Definition ASUAR : Z := 0x17b080.       (* [comment removed for export] *)
Definition AMEMCPY : Z := 0x7f9f4.      (* [comment removed for export] *)
Definition ASTKMALLOC0 : Z := 0x657d0.  (* [comment removed for export] *)
Definition ASTKMALLOC1 : Z := 0x65944.  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AVTAB_SRS : Z := 0x16c340.   (* [comment removed for export] *)
Definition AVTAB_VU8 : Z := 0x16c358.   (* [comment removed for export] *)
Definition ASRS_FN : Z := 0xe881c.
Definition AVU8_FN : Z := 0xb7cc4.

Definition AMEMCPY_STACK : Z := 2224.
Definition SM0_STACK : Z := 4096.
Definition SM1_STACK : Z := 4096.

(* [comment removed for export] *)
Definition client_img (m : amem) : Prop :=
  rw_cells bsegs m AGOT_SUAR [C8 (Z_to_bv 64 ASUAR)]
  /\ rw_cells bsegs m AVTAB_SRS [C8 (Z_to_bv 64 ASRS_FN)]
  /\ rw_cells bsegs m AVTAB_VU8 [C8 (Z_to_bv 64 AVU8_FN)].

(* [comment removed for export] *)
Definition client_ranges : list (Z * Z) :=
  [(0x16c330, 0x16c370); (0x6ad740, 0x6ad780); (0x6ad7a0, 0x6ad7a2); (0x6ad860, 0x6ad862); (0x6ad880, 0x6ad890);
   (0x6ad8a0, 0x6ad8a2); (0x6ad8c0, 0x6ad8c8); (0x6ad8e0, 0x6ad90c); (0x6ad940, 0x6ad942);
   (* [comment removed for export] *)
   (0x174000, 0x174008); (0x6cfb58, 0x6cfd78); (0x6cfd98, 0x6cfda0)].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_suar (m : amem) : Prop := rw_cells bsegs m ASUAR [C4 (Z_to_bv 64 1)].

(* [comment removed for export] *)
Definition client_sh_addrs : list Z := [0x16c340; 0x16c358; 0x6ad760; 0x6ad768; 0x6ad770; 0x6ad8c0; 0x6ad8e0; 0x6ad908].
Definition client_sh (m : amem) : Prop := forall X, In X client_sh_addrs -> m (wa (shad X)) = Some (Z_to_bv 8 0).
End CANSEC1.
(* [comment removed for export] *)
Notation rng_aimg_sh RNG := (rng RNG 0x7fffa000 0xd8400).
(* [comment removed for export] *)
Notation uri_img := client_img (only parsing).
Notation uri_sh := client_sh (only parsing).
Notation uri_img_ranges := client_ranges (only parsing).

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition fcell (m : amem) (LB : list ablock) (C k : Z) : Prop :=
  (exists cls FA FN, In (mkABlock (ABFake cls) FA FN) LB /\ FA <= C /\ C + k <= FA + FN /\ ablk FA (FA + FN) /\ FA + FN + 8 <= KEND /\ FA mod 8 = 0)
  /\ unpoisoned m C (C + k).


Section Stmts.
Variable AI : AMallocIface.
Notation CI := (aci AI).

(* [comment removed for export] *)
Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.

(* [comment removed for export] *)
Variable fflag : alayout -> Z -> Z -> Z.      (* [comment removed for export] *)
(* [comment removed for export] *)
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.

Notation FB0 F := (mkABlock (ABFake 0) F 64).

Hypothesis AI_fake_flag : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Hypothesis AI_fake_release : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).

Definition sm0_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP AI L RNG st (FB0 F :: LB) m'
    /\ F mod 64 = 0 /\ ablk F (F + 64) /\ F + 64 <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 (fflag L 0 F))]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0)]
    /\ rng RNG F 64 /\ rng RNG (shad F) 8.

Definition stack_malloc_0_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP AI L RNG st LB m ->
  (forall F n, ~ In (mkABlock (ABFake 0) F n) LB) ->      (* [comment removed for export] *)
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM0_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 64 ->
  client_img m ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
  evtF bsegs RNG (sm0_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Notation FB1 F := (mkABlock (ABFake 1) F 128).
Definition sm1_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP AI L RNG st (FB1 F :: LB) m'
    /\ F mod 128 = 0 /\ ablk F (F + 128) /\ F + 128 <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 96 junk; C8 (Z_to_bv 64 (fflag L 1 F))]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rng RNG F 128 /\ rng RNG (shad F) 16.

Definition stack_malloc_1_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP AI L RNG st LB m ->
  (forall F n, ~ In (mkABlock (ABFake 1) F n) LB) ->      (* [comment removed for export] *)
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM1_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
  evtF bsegs RNG (sm1_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC1) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition amemcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (src : list byte) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2224, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at bsegs m' (bv_unsigned a1) src.

Definition asan_memcpy_stmt : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (src junk : list byte) (RLO1 RHI1 RLO2 RHI2 : Z),
  let D := bv_unsigned a0 in let S := bv_unsigned a1 in let n := bv_unsigned a2 in
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - AMEMCPY_STACK -> KHIGH <= lo ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  bytes_at bsegs m S src -> length src = Z.to_nat n ->
  rw_cells bsegs m D [CB (Z.to_nat n) junk] ->
  (S + n <= D \/ D + n <= S) ->
  (S + n <= bv_unsigned sp - AMEMCPY_STACK \/ bv_unsigned sp <= S) ->
  (D + n <= lo \/ bv_unsigned sp <= D) ->
  app_blk S (S + n) -> app_blk D (D + n) ->
  unpoisoned m S (S + n) -> unpoisoned m D (D + n) ->
  n <= 2^40 ->
  (RLO1 <= S /\ S + n <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND) ->
  (RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND) ->
  wr_at bsegs m (shad RLO1) (shad RHI1 - shad RLO1) -> wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S n -> rng RNG D n ->
  rng RNG (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  evtF bsegs RNG (amemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc a0 a1 a2 src lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AMEMCPY) fc None m (seg_rom bsegs)).
End Stmts.
End CANSEC2.
