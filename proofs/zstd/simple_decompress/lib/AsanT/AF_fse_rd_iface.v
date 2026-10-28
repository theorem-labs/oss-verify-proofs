(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseHarness.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AFSE_RD_ENTRY : Z := 0xab28c.     (* [comment removed for export] *)
Definition AFSE_RD_BODY : Z := 0xaaac0.      (* [comment removed for export] *)
Definition AFSE_SM0 : Z := 0x3ee8c.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition SM0R_STACK : Z := 4096.
Definition FSE_READ_STACK_A : Z := 8192.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fcellA (m : amem) (LB : list ablock) (C k : Z) : Prop :=
  (exists cls FA FN, In (mkABlock (ABFake cls) FA FN) LB /\ FA <= C /\ C + k <= FA + FN /\ ablk FA (FA + FN) /\ FA mod 8 = 0)
  /\ unpoisoned m C (C + k).

(* [comment removed for export] *)
Definition shullA (RNG : footprint) (m : amem) (LB : list ablock) (A n : Z) : Prop :=
  exists cls FA FN, In (mkABlock (ABFake cls) FA FN) LB /\ FA <= A /\ A + n <= FA + FN
    /\ FA mod 64 = 0 /\ FN mod 64 = 0 /\ 0 <= FA /\ FA + FN <= KEND
    /\ wr_at bsegs m (shad FA) (FN / 8) /\ rng RNG (shad FA) (FN / 8).

(* [comment removed for export] *)
Definition fake0_le1 (LB : list ablock) : Prop :=
  forall F1 n1 F2 n2, In (mkABlock (ABFake 0) F1 n1) LB -> In (mkABlock (ABFake 0) F2 n2) LB -> F1 = F2 /\ n1 = n2.

Lemma fake0_le1_none : forall LB, (forall F n, ~ In (mkABlock (ABFake 0) F n) LB) -> fake0_le1 LB.
Proof. intros LB H F1 n1 F2 n2 H1 _. exfalso. exact (H F1 n1 H1). Qed.

Lemma fake0_le1_cons : forall F n LB, (forall F' n', ~ In (mkABlock (ABFake 0) F' n') LB) ->
  fake0_le1 (mkABlock (ABFake 0) F n :: LB).
Proof.
  intros F n LB H F1 n1 F2 n2 [E1|H1] [E2|H2].
  - injection E1 as -> ->. injection E2 as -> ->. split; reflexivity.
  - exfalso. exact (H F2 n2 H2).
  - exfalso. exact (H F1 n1 H1).
  - exfalso. exact (H F1 n1 H1).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stmts.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.        (* [comment removed for export] *)
Variable rng_fs : alayout -> footprint -> Prop.  (* [comment removed for export] *)

Notation FB0 F := (mkABlock (ABFake 0) F 64).

(* [comment removed for export] *)
Definition fake_flag_law : Prop :=
  forall L RNG st LB m cls F N,
  AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Definition fake_release_law : Prop :=
  forall L RNG st LB m cls F N,
  AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).

(* [comment removed for export] *)
Definition sm0r_post (L : alayout) (RNG : footprint)
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

Definition stack_malloc_0r_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP AI L RNG st LB m ->
  fake0_le1 LB ->                                          (* [comment removed for export] *)
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM0R_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
  evtF bsegs RNG (sm0r_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AFSE_SM0) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fse_read_postA (L : alayout) (RNG : footprint)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (SPV NC MSVP TLP : Z) (rt0 rt : list Z) (msv tl n lo : Z) (m : amem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo SPV
    /\ magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (NC <= a < NC + 2 * zlen rt0)
                              /\ ~ (MSVP <= a < MSVP + 4) /\ ~ (TLP <= a < TLP + 4)) m m'
    /\ AHEAP AI L RNG st LB m'
    /\ u8arr bsegs m' NC (u16s (map (Z_to_bv 64) rt))
    /\ rw_cells bsegs m' MSVP [C4 (Z_to_bv 64 msv)]
    /\ rw_cells bsegs m' TLP [C4 (Z_to_bv 64 tl)].

Definition fse_read_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
         (SPV NC MSVP TLP BUF : Z) (p : aptr) (rt0 rt buf : list Z) (msv0 msv tl n lo : Z) (tl0 : word),
  AHEAP AI L RNG st LB m ->
  (forall F k, ~ In (mkABlock (ABFake 0) F k) LB) ->       (* [comment removed for export] *)
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->   (* [comment removed for export] *)
  (* [comment removed for export] *)
  u8arr bsegs m NC (u16s (map (Z_to_bv 64) rt0)) ->
  rw_cells bsegs m MSVP [C4 (Z_to_bv 64 msv0)] ->
  rw_cells bsegs m TLP [C4 tl0] ->
  bytes_at bsegs m BUF (map (Z_to_bv 8) buf) -> Forall (fun c => 0 <= c < 256) buf ->
  (* [comment removed for export] *)
  read_ncount rt0 msv0 buf = Ok (rt, msv, tl, n) ->
  0 <= msv0 <= 255 -> zlen buf <= 1048576 -> zlen rt0 <= 65536 ->
  (* [comment removed for export] *)
  fcellA m LB NC (2 * zlen rt0) -> NC mod 8 = 0 -> shullA RNG m LB NC (2 * zlen rt0) ->
  fcellA m LB MSVP 4 -> MSVP mod 4 = 0 ->
  fcellA m LB TLP 4 -> TLP mod 4 = 0 ->
  In (mkABlock (ABHeap p) BUF (zlen buf)) LB ->
  (NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC) -> (NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC) ->
  (NC + 2 * zlen rt0 <= BUF \/ BUF + zlen buf <= NC) ->
  (MSVP + 4 <= TLP \/ TLP + 4 <= MSVP) ->
  (MSVP + 4 <= BUF \/ BUF + zlen buf <= MSVP) -> (TLP + 4 <= BUF \/ BUF + zlen buf <= TLP) ->
  (* [comment removed for export] *)
  stk bsegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - FSE_READ_STACK_A ->
  SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
  rng RNG NC (2 * zlen rt0) -> rng RNG (shad NC) (nshad (2 * zlen rt0)) ->
  rng RNG MSVP 4 -> rng RNG (shad MSVP) 1 -> rng RNG TLP 4 -> rng RNG (shad TLP) 1 ->
  a0 = Z_to_bv 64 NC -> a1 = Z_to_bv 64 MSVP -> a2 = Z_to_bv 64 TLP -> a3 = Z_to_bv 64 BUF -> a4 = Z_to_bv 64 (zlen buf) ->
  evtF bsegs RNG (fse_read_postA L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB SPV NC MSVP TLP rt0 rt msv tl n lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AFSE_RD_ENTRY) fc None m (seg_rom bsegs)).
End Stmts.
End CANSEC1.
