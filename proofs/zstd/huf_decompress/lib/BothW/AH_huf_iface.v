(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AHUF_FUZZ : Z := 0x7ff8c.        (* [comment removed for export] *)
Definition AHUF_RDT_X1 : Z := 0x80298.      (* [comment removed for export] *)
Definition AHUF_RDT_X2 : Z := 0x81e48.      (* [comment removed for export] *)
Definition AHUF_DEC_1X : Z := 0x846a4.      (* [comment removed for export] *)
Definition AHUF_DEC_4X : Z := 0x84fe4.      (* [comment removed for export] *)
Definition AHUF_ISERROR : Z := 0x9ae5c.     (* [comment removed for export] *)
Definition APROD_U32R : Z := 0x9aefc.       (* [comment removed for export] *)
Definition APROD_I32R : Z := 0x9b064.       (* [comment removed for export] *)
Definition APROD_REM : Z := 0x9b130.        (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HUF_RDT_STACK_A : Z := 8192.
Definition HUF_DEC_STACK_A : Z := 8192.

(* [comment removed for export] *)
Definition DTABLE_BYTES (mtl : Z) : Z := HufHarness.DT_BYTES mtl.     (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition prod_atA (m : amem) (P D size : Z) : Prop :=
  rw_cells bsegs m P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 size)].
Definition payload_atA (m : amem) (D : Z) (pl : list Z) : Prop :=
  bytes_at bsegs m D (map (Z_to_bv 8) pl) /\ Forall (fun c => 0 <= c < 256) pl.

Definition prod_u32r_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV P D : Z) (pl : list Z) (size mn mx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (uint32Range pl size mn mx))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(P + 8, P + 16); (SPV - 16, SPV)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ prod_atA m' P D (snd (uint32Range pl size mn mx)).

Definition prod_u32r_stmtA : Prop :=
  forall (RNG : footprint)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV P D : Z) (pl : list Z) (size mn mx lo : Z),
  prod_atA m P D size -> payload_atA m D pl -> 0 <= size <= zlen pl ->
  0 < P -> P mod 8 = 0 -> 0 < D ->
  stk bsegs m lo SPV -> lo <= SPV - 16 -> 0 <= SPV < 2^64 ->
  P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) ->
  mem_inv bsegs m ->
  0 <= mn <= mx -> mx < 2^31 ->                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  ablk P (P + 16) -> (0 < zlen pl -> ablk D (D + zlen pl)) -> D mod 8 = 0 -> KHIGH <= lo ->
  rt_got m -> rt_shbase m ->
  unpoisoned m P (P + 16) -> unpoisoned m D (D + zlen pl) ->
  rng_aimg RNG -> rng RNG lo (SPV - lo) ->
  rng RNG P 16 -> rng RNG (shad P) 2 -> rng RNG D (zlen pl) -> rng RNG (shad D) (nshad (zlen pl)) ->
  a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 mn -> a2 = Z_to_bv 64 mx ->
  evtF bsegs RNG (prod_u32r_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV P D pl size mn mx lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 APROD_U32R) fc None m (seg_rom bsegs)).

Definition prod_i32r_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV P D : Z) (pl : list Z) (size mn mx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (int32Range pl size mn mx))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(P + 8, P + 16); (SPV - 32, SPV)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ prod_atA m' P D (snd (int32Range pl size mn mx)).

Definition prod_i32r_stmtA : Prop :=
  forall (RNG : footprint)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV P D : Z) (pl : list Z) (size mn mx lo : Z),
  prod_atA m P D size -> payload_atA m D pl -> 0 <= size <= zlen pl ->
  0 < P -> P mod 8 = 0 -> 0 < D ->
  stk bsegs m lo SPV -> lo <= SPV - 32 -> 0 <= SPV < 2^64 ->
  P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) ->
  mem_inv bsegs m ->
  - 2^31 <= mn <= mx -> mx < 2^31 -> mx - mn < 2^31 ->
  ablk P (P + 16) -> (0 < zlen pl -> ablk D (D + zlen pl)) -> D mod 8 = 0 -> KHIGH <= lo ->
  rt_got m -> rt_shbase m ->
  unpoisoned m P (P + 16) -> unpoisoned m D (D + zlen pl) ->
  rng_aimg RNG -> rng RNG lo (SPV - lo) ->
  rng RNG P 16 -> rng RNG (shad P) 2 -> rng RNG D (zlen pl) -> rng RNG (shad D) (nshad (zlen pl)) ->
  a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 mn -> a2 = Z_to_bv 64 mx ->
  evtF bsegs RNG (prod_i32r_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV P D pl size mn mx lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 APROD_I32R) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition prod_rem_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV size lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 size) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(SPV - 16, SPV)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV.

Definition prod_rem_stmtA : Prop :=
  forall (RNG : footprint)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV P D size lo : Z),
  prod_atA m P D size -> 0 <= size < 2^64 ->
  0 < P -> P mod 8 = 0 ->
  stk bsegs m lo SPV -> lo <= SPV - 16 -> 0 <= SPV < 2^64 -> P + 16 <= lo ->
  mem_inv bsegs m ->
  ablk P (P + 16) -> KHIGH <= lo -> rt_got m -> rt_shbase m -> unpoisoned m P (P + 16) ->
  rng_aimg RNG -> rng RNG lo (SPV - lo) -> rng RNG P 16 -> rng RNG (shad P) 2 ->
  a0 = Z_to_bv 64 P ->
  evtF bsegs RNG (prod_rem_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV size lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 APROD_REM) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition huf_iserror_postA (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (c : Z) (m : amem) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.b2z (2^64 - 119 <=? c))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom bsegs).

Definition huf_iserror_stmtA : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (c : Z),
  0 <= c < 2^64 -> a0 = Z_to_bv 64 c ->
  evtF bsegs RNG (huf_iserror_postA ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc c m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 AHUF_ISERROR) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stmts.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.    (* [comment removed for export] *)
  Variable dt_ok : amem -> Z -> Z -> Prop.           (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition src_inA (LB : list ablock) (S : Z) (src : list Z) : Prop :=
    0 < zlen src -> exists p A n, In (HB p A n) LB /\ A <= S /\ S + zlen src <= A + n.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition huf_rdt_postA (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
      (st : astate) (LB : list ablock) (DT W mtl lo : Z) (m : amem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r : Z) (m' : amem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ magree bsegs (fun a => aclient_addr CI LB (bv_unsigned sp) a
                                /\ ~ (DT <= a < DT + DTABLE_BYTES mtl) /\ ~ (W <= a < W + 8704)) m m'
      /\ AHEAP AI L RNG st LB m'
      /\ 0 <= r < 2^64
      /\ (r < 2^64 - 119 -> dt_ok m' DT mtl).

  Definition huf_rdt_stmtA (E : Z) : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
           (DT W S mtl flags : Z) (pdt pw : aptr) (src : list Z) (jdt : list byte) (lo : Z) (rstk : region),
    AHEAP AI L RNG st LB m ->
    (forall F k, ~ In (mkABlock (ABFake 0) F k) LB) ->                  (* [comment removed for export] *)
    (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->  (* [comment removed for export] *)
    (* [comment removed for export] *)
    1 <= mtl <= 12 ->
    In (HB pdt DT (DTABLE_BYTES mtl)) LB ->
    rw_cells bsegs m DT [C4 (Z_to_bv 64 (mtl * 0x01000001)); CB (Z.to_nat (4 * 2^mtl)) jdt] ->
    In (HB pw W 8704) LB ->
    (* [comment removed for export] *)
    bytes_at bsegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
    zlen src < 2^26 -> 16 <= S -> src_inA LB S src ->
    (DT + DTABLE_BYTES mtl <= S \/ S + zlen src <= DT) -> (W + 8704 <= S \/ S + zlen src <= W) ->
    (* [comment removed for export] *)
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - HUF_RDT_STACK_A ->
    (* [comment removed for export] *)
    rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
    bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
    mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    0 <= flags < 64 ->
    (* [comment removed for export] *)
    harness_invA m ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
    a0 = Z_to_bv 64 DT -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlen src) -> a3 = Z_to_bv 64 W -> a4 = Z_to_bv 64 8704 ->
    a5 = Z_to_bv 64 flags ->
    evtF bsegs RNG (huf_rdt_postA L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DT W mtl lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (Z_to_bv 64 E) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition huf_dec_postA (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
      (st : astate) (LB : list ablock) (DST dcap lo : Z) (m : amem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ magree bsegs (fun a => aclient_addr CI LB (bv_unsigned sp) a /\ ~ (DST <= a < DST + dcap)) m m'
      /\ AHEAP AI L RNG st LB m'.

  Definition huf_dec_stmtA (E : Z) : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
           (DST dcap S DT mtl flags : Z) (pdt : aptr) (src : list Z) (lo : Z) (rstk : region),
    AHEAP AI L RNG st LB m ->
    (forall F k, ~ In (mkABlock (ABFake 0) F k) LB) ->
    (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
    (* [comment removed for export] *)
    1 <= mtl <= 12 -> In (HB pdt DT (DTABLE_BYTES mtl)) LB -> dt_ok m DT mtl ->
    (* [comment removed for export] *)
    ((DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB)) ->
    0 <= dcap < 2^32 ->
    (* [comment removed for export] *)
    bytes_at bsegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
    zlen src < 2^26 -> 16 <= S -> src_inA LB S src ->
    (DT + DTABLE_BYTES mtl <= S \/ S + zlen src <= DT) -> (DST + dcap <= S \/ S + zlen src <= DST) ->
    (DT + DTABLE_BYTES mtl <= DST \/ DST + dcap <= DT) ->
    (* [comment removed for export] *)
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - HUF_DEC_STACK_A ->
    (* [comment removed for export] *)
    rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
    bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
    mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    0 <= flags < 64 ->
    (* [comment removed for export] *)
    harness_invA m ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
    a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 dcap -> a2 = Z_to_bv 64 S -> a3 = Z_to_bv 64 (zlen src) -> a4 = Z_to_bv 64 DT ->
    a5 = Z_to_bv 64 flags ->
    evtF bsegs RNG (huf_dec_postA L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (Z_to_bv 64 E) fc None m (seg_rom bsegs)).
End Stmts.
End CANSEC1.
