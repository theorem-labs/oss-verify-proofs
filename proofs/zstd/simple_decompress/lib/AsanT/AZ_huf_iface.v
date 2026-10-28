(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AZ_kit AZ_globals AZ_globalsR.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Notation BITINIT_STACK_A := 2224 (only parsing).      (* [comment removed for export] *)
Notation FASTARGS_STACK_A := 48 (only parsing).   (* [comment removed for export] *)
Notation HUF_1X_STACK_A := 2368 (only parsing).   (* [comment removed for export] *)         (* [comment removed for export] *)
Notation HUF_1XI_STACK_A := 2352 (only parsing).   (* [comment removed for export] *)        (* [comment removed for export] *)
Notation HUF_4X_STACK_A := 3152 (only parsing).   (* [comment removed for export] *)       (* [comment removed for export] *)
Notation HUF_4X1I_STACK_A := 2720 (only parsing).   (* [comment removed for export] *)     (* [comment removed for export] *)
Notation HUF_4X2I_STACK_A := 3136 (only parsing).   (* [comment removed for export] *)     (* [comment removed for export] *)
Notation HUF_TBL_STACK_A := 5936 (only parsing).   (* [comment removed for export] *)      (* [comment removed for export] *)
Notation HUF_1X1W_STACK_A := 5984 (only parsing).   (* [comment removed for export] *)
Notation HUF_4XW_STACK_A := 6000 (only parsing).   (* [comment removed for export] *)      (* [comment removed for export] *)
Notation HUF_TBL_DEPTH := 4 (only parsing).           (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition APHUF_1X2 : Z := 0x99a40.          (* [comment removed for export] *)
Definition APHUF_1X1_WKSP : Z := 0x9af84.     (* [comment removed for export] *)
Definition APHUF_1X : Z := 0x9b030.           (* [comment removed for export] *)
Definition APHUF_1X1 : Z := 0x9b088.          (* [comment removed for export] *)
Definition APHUF_4X : Z := 0x9baa8.           (* [comment removed for export] *)
Definition APHUF_4X2 : Z := 0x9bb00.          (* [comment removed for export] *)
Definition APHUF_4X1 : Z := 0xa4cbc.          (* [comment removed for export] *)
Definition APHUF_4X_WKSP : Z := 0xa98f0.      (* [comment removed for export] *)
Definition APHUF_BITINIT : Z := 0xa9b34.      (* [comment removed for export] *)
Definition APHUF_FASTARGS : Z := 0xaa0d8.     (* [comment removed for export] *)
Definition APHUF_RDX1 : Z := 0x96138.         (* [comment removed for export] *)
Definition APHUF_RDX2 : Z := 0x97374.         (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bitd_ptr (SRC n : Z) : Z := if 8 <=? n then SRC + n - 8 else SRC.

Definition bitd_cells (cont bc : word) (pad : list byte) (p SRC : Z) : list cell :=
  [C8 cont; C4 bc; CB 4 pad; C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 SRC); C8 (Z_to_bv 64 (SRC + 8))].

Definition bit_init_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV BD SRC n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(BD, BD + 40); (SPV - BITINIT_STACK_A, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ ((r = n /\ 1 <= n /\ exists cont bc pad, 1 <= bc <= 64 /\ (8 <= n -> bc <= 8) /\
                                rw_cells bsegs m' BD (bitd_cells cont (Z_to_bv 64 bc) pad (bitd_ptr SRC n) SRC))
        \/ (zd_is_error r = true /\ r < 2^64 /\ exists bs, rw_cells bsegs m' BD [CB 40 bs])).

Definition bit_init_stmtA_at (ENTRY : Z) : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV BD SRC n lo : Z) (src junk : list byte),
  mem_inv bsegs m ->
  rw_cells bsegs m BD [CB 40 junk] -> BD mod 8 = 0 ->      (* [comment removed for export] *)
  bytes_at bsegs m SRC src -> zlen src = n ->
  4096 <= BD -> BD + 40 < 2^47 -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
  (BD + 40 <= SRC \/ SRC + n <= BD) ->
  stk bsegs m lo SPV -> lo <= SPV - BITINIT_STACK_A -> SPV < 2^47 ->
  (BD + 40 <= lo \/ SPV <= BD) -> (SRC + n <= lo \/ SPV <= SRC) ->
  (* [comment removed for export] *)
  app_blk BD (BD + 40) -> aro RNG m BD 40 -> ahull RNG m BD 40 -> aro RNG m SRC n ->
  art m -> astk RNG lo SPV ->
  evtF bsegs RNG (bit_init_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV BD SRC n lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom bsegs)).

Definition bit_init_stmtA : Prop := bit_init_stmtA_at APHUF_BITINIT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fast_args_cells (DST dsz SRC n DT l1 l2 l3 : Z) (b0 b1 b2 b3 : word) : list cell :=
  let q := (dsz + 3) / 4 in
  [C8 (Z_to_bv 64 (SRC + 6 + l1 - 8)); C8 (Z_to_bv 64 (SRC + 6 + l1 + l2 - 8));
   C8 (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3 - 8)); C8 (Z_to_bv 64 (SRC + n - 8));
   C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + q)); C8 (Z_to_bv 64 (DST + 2 * q)); C8 (Z_to_bv 64 (DST + 3 * q));
   C8 b0; C8 b1; C8 b2; C8 b3;
   C8 (Z_to_bv 64 (DT + 4)); C8 (Z_to_bv 64 SRC); C8 (Z_to_bv 64 (DST + dsz));
   C8 (Z_to_bv 64 (SRC + 6)); C8 (Z_to_bv 64 (SRC + 6 + l1)); C8 (Z_to_bv 64 (SRC + 6 + l1 + l2));
   C8 (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))].

Definition fast_args_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV ARGS DST dsz SRC n DT lo : Z) (m : amem) (dth : list byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(ARGS, ARGS + 152); (SPV - FASTARGS_STACK_A, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ ((r = 1 /\ exists l1 l2 l3 b0 b1 b2 b3,
           8 <= l1 /\ 8 <= l2 /\ 8 <= l3 /\ 6 + l1 + l2 + l3 + 8 <= n /\ DST + 3 * ((dsz + 3) / 4) < DST + dsz /\
           rw_cells bsegs m' ARGS (fast_args_cells DST dsz SRC n DT l1 l2 l3 b0 b1 b2 b3) /\
           nth_error dth 2 = Some (Z_to_bv 8 11))
        \/ ((r = 0 \/ zd_is_error r = true) /\ 0 <= r < 2^64 /\ exists bs, rw_cells bsegs m' ARGS [CB 152 bs])).

Definition fast_args_stmtA : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV ARGS DST dsz SRC n DT lo : Z) (src dth junk : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo SPV -> 4096 <= lo -> lo <= SPV - FASTARGS_STACK_A -> SPV < 2^47 ->
  rw_cells bsegs m ARGS [CB 152 junk] -> ARGS mod 8 = 0 -> DT mod 4 = 0 ->      (* [comment removed for export] *)
  bytes_at bsegs m SRC src -> zlen src = n ->
  bytes_at bsegs m DT dth -> zlen dth = 4 ->
  4096 <= ARGS -> ARGS + 152 < 2^47 -> (ARGS + 152 <= lo \/ SPV <= ARGS) ->
  4096 <= SRC -> SRC + n < 2^47 -> (SRC + n <= lo \/ SPV <= SRC) -> n < 2^32 ->
  4096 <= DT -> DT + 4 < 2^47 -> (DT + 4 <= lo \/ SPV <= DT) -> 0 <= DST -> 0 <= dsz < 2^32 -> DST + dsz < 2^47 ->
  (ARGS + 152 <= SRC \/ SRC + n <= ARGS) -> (ARGS + 152 <= DT \/ DT + 4 <= ARGS) ->
  (* [comment removed for export] *)
  app_blk ARGS (ARGS + 152) -> aro RNG m ARGS 152 -> aro RNG m SRC n -> aro RNG m DT 4 -> art m -> astk RNG lo SPV ->
  evtF bsegs RNG (fast_args_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV ARGS DST dsz SRC n DT lo m dth)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ARGS) (Z_to_bv 64 DST) (Z_to_bv 64 dsz) (Z_to_bv 64 SRC)
               (Z_to_bv 64 n) (Z_to_bv 64 DT) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APHUF_FASTARGS) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HUF_DTABLE_BYTES : Z := 16388.
Definition HUF_WKSP_BYTES : Z := 2560.          (* [comment removed for export] *)

Definition huf_hdr_ok (dtb : list byte) : Prop := zlen dtb = HUF_DTABLE_BYTES /\ nth_error dtb 0 = Some (Z_to_bv 8 12).
Definition huf_x2_ok (dtb : list byte) (tl : Z) : Prop :=
  forall i, 0 <= i < 2^tl -> exists b, nth_error dtb (Z.to_nat (4 * i + 7)) = Some b /\ 1 <= bv_unsigned b <= 2.
Definition huf_nb_ok (x2 : bool) (dtb : list byte) (tl : Z) : Prop :=
  forall i, 0 <= i < 2^tl ->
    exists b, nth_error dtb (Z.to_nat (if x2 then 4 * i + 6 else 2 * i + 4)) = Some b /\ bv_unsigned b <= tl.      (* [comment removed for export] *)

Definition huf_tbl_ok (dtb : list byte) : Prop :=
  huf_hdr_ok dtb /\
  exists ty tl, nth_error dtb 1 = Some ty /\ nth_error dtb 2 = Some (Z_to_bv 8 tl) /\ 1 <= tl <= 12 /\
                (bv_unsigned ty <> 0 -> huf_x2_ok dtb tl) /\
                huf_nb_ok (negb (bv_unsigned ty =? 0)) dtb tl.
Definition huf_tbl_at (m : amem) (DT : Z) : Prop := exists dtb, bytes_at bsegs m DT dtb /\ huf_tbl_ok dtb.

Definition HUFINV (m : amem) (DCTX : Z) (huf le : word) : Prop :=
  huf = Z_to_bv 64 (DCTX + 10296) /\
  exists dtb, bytes_at bsegs m (DCTX + 10296) dtb /\ huf_hdr_ok dtb /\ (bv_unsigned le mod 2^32 <> 0 -> huf_tbl_ok dtb).

Lemma HUFINV_tbl : forall m DCTX huf le, HUFINV m DCTX huf le -> bv_unsigned le mod 2^32 <> 0 ->
  huf = Z_to_bv 64 (DCTX + 10296) /\ huf_tbl_at m (DCTX + 10296).
Proof. intros m DCTX huf le (E & dtb & B & _ & T) NZ. split; [exact E|]. exists dtb. split; [exact B | exact (T NZ)]. Qed.

(* [comment removed for export] *)
Definition huf_dec_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DST dcap lo fr : Z) (extra : list (Z * Z)) (m : amem) (Q : amem -> Z -> Prop) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch ((DST, DST + dcap) :: extra ++ [(SPV - fr, SPV)]) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV /\ stk bsegs m' DST (DST + dcap)
    /\ (r = dcap \/ zd_is_error r = true) /\ 0 <= r < 2^64 /\ Q m' r.

(* [comment removed for export] *)
Definition huf_dec_preA (RNG : footprint) (m : amem) (SPV lo fr DST dcap SRC n : Z) (src : list byte) : Prop :=
  mem_inv bsegs m /\
  stk bsegs m lo SPV /\ 4096 <= lo /\ lo <= SPV - fr /\ SPV < 2^47 /\
  stk bsegs m DST (DST + dcap) /\ 4096 <= DST /\ 0 <= dcap < 2^32 /\ DST + dcap < 2^47 /\
  bytes_at bsegs m SRC src /\ zlen src = n /\ 4096 <= SRC /\ n < 2^32 /\ SRC + n < 2^47 /\
  (DST + dcap <= lo \/ SPV <= DST) /\ (SRC + n <= lo \/ SPV <= SRC) /\ (DST + dcap <= SRC \/ SRC + n <= DST) /\
  areg RNG m DST dcap /\ areg RNG m SRC n /\ art m /\ astk RNG lo SPV /\ azstk RNG m lo SPV /\ aro_client RNG m /\
  SPV mod 16 = 0.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition huf_dt_preA (RNG : footprint) (m : amem) (SPV lo DST dcap DT : Z) (dtb : list byte) : Prop :=
  bytes_at bsegs m DT dtb /\ zlen dtb = HUF_DTABLE_BYTES /\ 4096 <= DT /\ DT + HUF_DTABLE_BYTES < 2^47 /\
  (DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT) /\ (DST + dcap <= DT \/ DT + HUF_DTABLE_BYTES <= DST) /\
  aro RNG m DT HUF_DTABLE_BYTES /\ DT mod 4 = 0.      (* [comment removed for export] *)

Definition huf_noQ : amem -> Z -> Prop := fun _ _ => True.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition huf_using_stmtA_at (ENTRY fr : Z) : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV DST dcap SRC n DT lo : Z) (src dtb : list byte),
  huf_dec_preA RNG m SPV lo fr DST dcap SRC n src ->
  huf_dt_preA RNG m SPV lo DST dcap DT dtb -> huf_tbl_ok dtb ->
  evtF bsegs RNG (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo fr [] m huf_noQ)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom bsegs)).

Definition huf_1x_stmtA : Prop := huf_using_stmtA_at APHUF_1X HUF_1X_STACK_A.
Definition huf_4x_stmtA : Prop := huf_using_stmtA_at APHUF_4X HUF_4X_STACK_A.

Definition huf_int_stmtA_at (ENTRY fr : Z) (x2 : bool) : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV DST dcap SRC n DT tl lo : Z) (src dtb : list byte),
  huf_dec_preA RNG m SPV lo fr DST dcap SRC n src ->
  huf_dt_preA RNG m SPV lo DST dcap DT dtb ->
  nth_error dtb 2 = Some (Z_to_bv 8 tl) -> 1 <= tl <= 12 -> (x2 = true -> huf_x2_ok dtb tl) -> huf_nb_ok x2 dtb tl ->
  evtF bsegs RNG (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo fr [] m huf_noQ)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom bsegs)).

Definition huf_1x1_stmtA : Prop := huf_int_stmtA_at APHUF_1X1 HUF_1XI_STACK_A false.
Definition huf_1x2_stmtA : Prop := huf_int_stmtA_at APHUF_1X2 HUF_1XI_STACK_A true.
Definition huf_4x1_stmtA : Prop := huf_int_stmtA_at APHUF_4X1 HUF_4X1I_STACK_A false.
Definition huf_4x2_stmtA : Prop := huf_int_stmtA_at APHUF_4X2 HUF_4X2I_STACK_A true.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section StmtsF.
Variable AI : AMallocIface.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.

(* [comment removed for export] *)
Definition huf_dec_postF (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DST dcap lo fr : Z) (extra : list (Z * Z)) (m : amem) (Q : amem -> Z -> Prop) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (((DST, DST + dcap) :: extra ++ [(SPV - fr, SPV)]) ++ fake_area L) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV /\ stk bsegs m' DST (DST + dcap)
    /\ ffr_pres ((DST, DST + dcap) :: extra) LB m m' /\ AHEAP AI L RNG st LB m'
    /\ (r = dcap \/ zd_is_error r = true) /\ 0 <= r < 2^64 /\ Q m' r.

Definition huf_built (DT : Z) : amem -> Z -> Prop :=
  fun m' r => exists dtb', u8arr bsegs m' DT dtb' /\ huf_hdr_ok dtb' /\ (zd_is_error r = false -> huf_tbl_ok dtb').

(* [comment removed for export] *)
Definition huf_wksp_stmtA_at (ENTRY fr : Z) : Prop :=
  forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (ra gp tp t0 t1 t2 s0 s1 flags s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV DST dcap SRC n DT WK wksz lo : Z) (src dtb : list byte),
  huf_dec_preA RNG m SPV lo fr DST dcap SRC n src ->
  (* [comment removed for export] *)
  u8arr bsegs m DT dtb -> huf_hdr_ok dtb -> 4096 <= DT -> DT + HUF_DTABLE_BYTES < 2^47 -> DT mod 4 = 0 ->
  (* [comment removed for export] *)
  stk bsegs m WK (WK + wksz) -> 4096 <= WK -> 0 <= wksz < 2^32 -> WK + wksz < 2^47 -> WK mod 4 = 0 ->
  (* [comment removed for export] *)
  (DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT) -> (WK + wksz <= lo \/ SPV <= WK) ->
  (DST + dcap <= DT \/ DT + HUF_DTABLE_BYTES <= DST) -> (DST + dcap <= WK \/ WK + wksz <= DST) ->
  (DT + HUF_DTABLE_BYTES <= WK \/ WK + wksz <= DT) ->
  (DT + HUF_DTABLE_BYTES <= SRC \/ SRC + n <= DT) -> (WK + wksz <= SRC \/ SRC + n <= WK) ->
  (* [comment removed for export] *)
  afpre AI rng_fs L RNG st LB m lo SPV HUF_TBL_DEPTH -> tp = Z_to_bv 64 ATP -> aro_client RNG m ->
  areg RNG m DT HUF_DTABLE_BYTES -> ahull RNG m DT HUF_DTABLE_BYTES -> ainblk LB DT HUF_DTABLE_BYTES ->
  areg RNG m WK wksz -> ahull RNG m WK wksz -> ainblk LB WK wksz -> ainblk LB DST dcap -> (0 < n -> ainimg LB SRC n) ->
  (0 < n -> ahull RNG m SRC n) ->     (* [comment removed for export] *)
  evtF bsegs RNG (huf_dec_postF L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo fr
               [(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz)] m
               (fun m' r => huf_built DT m' r /\ stk bsegs m' WK (WK + wksz)))
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC)
               (Z_to_bv 64 n) (Z_to_bv 64 WK) (Z_to_bv 64 wksz) flags s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom bsegs)).

Definition huf_1x1_wksp_stmtA : Prop := huf_wksp_stmtA_at APHUF_1X1_WKSP HUF_1X1W_STACK_A.
Definition huf_4x_wksp_stmtA : Prop := huf_wksp_stmtA_at APHUF_4X_WKSP HUF_4XW_STACK_A.

(* [comment removed for export] *)
Definition huf_rd_postA (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DT WK wksz lo : Z) (x2 : bool) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r dtb',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch ([(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz); (SPV - HUF_TBL_STACK_A, SPV)] ++ fake_area L) m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV /\ stk bsegs m' WK (WK + wksz)
    /\ ffr_pres [(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz)] LB m m' /\ AHEAP AI L RNG st LB m'
    /\ u8arr bsegs m' DT dtb' /\ huf_hdr_ok dtb' /\ 0 <= r < 2^64
    /\ (zd_is_error r = false ->
        huf_tbl_ok dtb' /\ exists ty, nth_error dtb' 1 = Some ty /\ (bv_unsigned ty <> 0 <-> x2 = true)).

Definition huf_rd_stmtA_at (ENTRY : Z) (x2 : bool) : Prop :=
  forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV SRC n DT WK wksz lo : Z) (src dtb : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo SPV -> 4096 <= lo -> lo <= SPV - HUF_TBL_STACK_A -> SPV < 2^47 ->
  bytes_at bsegs m SRC src -> zlen src = n -> 4096 <= SRC -> n < 2^32 -> SRC + n < 2^47 ->
  u8arr bsegs m DT dtb -> huf_hdr_ok dtb -> 4096 <= DT -> DT + HUF_DTABLE_BYTES < 2^47 -> DT mod 4 = 0 ->
  stk bsegs m WK (WK + wksz) -> 4096 <= WK -> 0 <= wksz < 2^32 -> WK + wksz < 2^47 -> WK mod 4 = 0 ->
  (DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT) -> (WK + wksz <= lo \/ SPV <= WK) -> (SRC + n <= lo \/ SPV <= SRC) ->
  (DT + HUF_DTABLE_BYTES <= WK \/ WK + wksz <= DT) ->
  (DT + HUF_DTABLE_BYTES <= SRC \/ SRC + n <= DT) -> (WK + wksz <= SRC \/ SRC + n <= WK) ->
  (* [comment removed for export] *)
  afpre AI rng_fs L RNG st LB m lo SPV HUF_TBL_DEPTH -> azstk RNG m lo SPV -> tp = Z_to_bv 64 ATP -> aro_client RNG m ->
  areg RNG m SRC n -> (0 < n -> ainimg LB SRC n) ->
  (0 < n -> ahull RNG m SRC n) ->     (* [comment removed for export] *)
  areg RNG m DT HUF_DTABLE_BYTES -> ahull RNG m DT HUF_DTABLE_BYTES -> ainblk LB DT HUF_DTABLE_BYTES ->
  areg RNG m WK wksz -> ahull RNG m WK wksz -> ainblk LB WK wksz ->
  evtF bsegs RNG (huf_rd_postA L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT WK wksz lo x2 m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 WK)
               (Z_to_bv 64 wksz) flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom bsegs)).

Definition huf_rdx1_stmtA : Prop := huf_rd_stmtA_at APHUF_RDX1 false.
Definition huf_rdx2_stmtA : Prop := huf_rd_stmtA_at APHUF_RDX2 true.
End StmtsF.
End CANSEC1.
