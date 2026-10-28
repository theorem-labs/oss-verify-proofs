(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.

Notation fmem := (word -> option byte).
Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PHUF_1X2 : Z := 0x1fb64.          (* [comment removed for export] *)
Definition PHUF_1X1_WKSP : Z := 0x20734.     (* [comment removed for export] *)
Definition PHUF_1X : Z := 0x207f8.           (* [comment removed for export] *)
Definition PHUF_1X1 : Z := 0x20814.          (* [comment removed for export] *)
Definition PHUF_4X : Z := 0x20d78.           (* [comment removed for export] *)
Definition PHUF_4X2 : Z := 0x20d94.          (* [comment removed for export] *)
Definition PHUF_4X1 : Z := 0x22194.          (* [comment removed for export] *)
Definition PHUF_4X_WKSP : Z := 0x25418.      (* [comment removed for export] *)
Definition PHUF_BITINIT : Z := 0x25a0c.      (* [comment removed for export] *)
Definition PHUF_FASTARGS : Z := 0x29690.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bitd_ptr (SRC n : Z) : Z := if 8 <=? n then SRC + n - 8 else SRC.

Definition bitd_cells (cont bc : word) (pad : list byte) (p SRC : Z) : list cell :=
  [C8 cont; C4 bc; CB 4 pad; C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 SRC); C8 (Z_to_bv 64 (SRC + 8))].

Definition bit_init_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (BD SRC n : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(BD, BD + 40)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ ((r = n /\ 1 <= n /\ exists cont bc pad, 1 <= bc <= 64 /\ (8 <= n -> bc <= 8) /\
                                rw_cells usegs m' BD (bitd_cells cont (Z_to_bv 64 bc) pad (bitd_ptr SRC n) SRC))
        \/ (zd_is_error r = true /\ r < 2^64 /\ exists bs, rw_cells usegs m' BD [CB 40 bs])).

Definition bit_init_stmt_at (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (BD SRC n : Z) (src junk : list byte),
  mem_inv usegs m ->
  rw_cells usegs m BD [CB 40 junk] -> BD mod 8 = 0 ->
  bytes_at usegs m SRC src -> zlen src = n ->
  4096 <= BD -> BD + 40 < 2^47 -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
  (BD + 40 <= SRC \/ SRC + n <= BD) ->
  evt usegs (bit_init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc BD SRC n m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).

Definition bit_init_stmt : Prop := bit_init_stmt_at PHUF_BITINIT.

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

Definition fast_args_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV ARGS DST dsz SRC n DT lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(ARGS, ARGS + 152); (SPV - 16, SPV)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ ((r = 1 /\ exists l1 l2 l3 b0 b1 b2 b3,
           8 <= l1 /\ 8 <= l2 /\ 8 <= l3 /\ 6 + l1 + l2 + l3 + 8 <= n /\ DST + 3 * ((dsz + 3) / 4) < DST + dsz /\
           rw_cells usegs m' ARGS (fast_args_cells DST dsz SRC n DT l1 l2 l3 b0 b1 b2 b3))
        \/ ((r = 0 \/ zd_is_error r = true) /\ 0 <= r < 2^64 /\ exists bs, rw_cells usegs m' ARGS [CB 152 bs])).

Definition fast_args_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV ARGS DST dsz SRC n DT lo : Z) (src dth junk : list byte),
  mem_inv usegs m ->
  stk usegs m lo SPV -> 4096 <= lo -> lo <= SPV - 16 -> SPV < 2^47 ->
  rw_cells usegs m ARGS [CB 152 junk] -> ARGS mod 8 = 0 -> DT mod 4 = 0 ->
  bytes_at usegs m SRC src -> zlen src = n ->
  bytes_at usegs m DT dth -> zlen dth = 4 ->
  4096 <= ARGS -> ARGS + 152 < 2^47 -> (ARGS + 152 <= lo \/ SPV <= ARGS) ->
  4096 <= SRC -> SRC + n < 2^47 -> (SRC + n <= lo \/ SPV <= SRC) -> n < 2^32 ->
  4096 <= DT -> DT + 4 < 2^47 -> (DT + 4 <= lo \/ SPV <= DT) -> 4096 <= DST -> 0 <= dsz < 2^32 -> DST + dsz < 2^47 ->
  (ARGS + 152 <= SRC \/ SRC + n <= ARGS) -> (ARGS + 152 <= DT \/ DT + 4 <= ARGS) ->
  evt usegs (fast_args_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV ARGS DST dsz SRC n DT lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ARGS) (Z_to_bv 64 DST) (Z_to_bv 64 dsz) (Z_to_bv 64 SRC)
               (Z_to_bv 64 n) (Z_to_bv 64 DT) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PHUF_FASTARGS) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HUF_DTABLE_BYTES : Z := 16388.
Definition HUF_WKSP_BYTES : Z := 2560.          (* [comment removed for export] *)

Definition huf_hdr_ok (dtb : list byte) : Prop := zlen dtb = HUF_DTABLE_BYTES /\ nth_error dtb 0 = Some (Z_to_bv 8 12).
Definition huf_x2_ok (dtb : list byte) (tl : Z) : Prop :=
  forall i, 0 <= i < 2^tl -> exists b, nth_error dtb (Z.to_nat (4 * i + 7)) = Some b /\ 1 <= bv_unsigned b <= 2.
(* [comment removed for export] *)
Definition huf_nb_ok (x2 : bool) (dtb : list byte) (tl : Z) : Prop :=
  forall i, 0 <= i < 2^tl ->
    exists b, nth_error dtb (Z.to_nat (if x2 then 4 * i + 6 else 2 * i + 4)) = Some b /\ bv_unsigned b <= tl.

Definition huf_tbl_ok (dtb : list byte) : Prop :=
  huf_hdr_ok dtb /\
  exists ty tl, nth_error dtb 1 = Some ty /\ nth_error dtb 2 = Some (Z_to_bv 8 tl) /\ 1 <= tl <= 12 /\
                (bv_unsigned ty <> 0 -> huf_x2_ok dtb tl) /\
                huf_nb_ok (negb (bv_unsigned ty =? 0)) dtb tl.
Definition huf_tbl_at (m : fmem) (DT : Z) : Prop := exists dtb, bytes_at usegs m DT dtb /\ huf_tbl_ok dtb.

Definition HUFINV (m : fmem) (DCTX : Z) (huf le : word) : Prop :=
  huf = Z_to_bv 64 (DCTX + 10296) /\
  exists dtb, bytes_at usegs m (DCTX + 10296) dtb /\ huf_hdr_ok dtb /\ (bv_unsigned le mod 2^32 <> 0 -> huf_tbl_ok dtb).

Lemma HUFINV_tbl : forall m DCTX huf le, HUFINV m DCTX huf le -> bv_unsigned le mod 2^32 <> 0 ->
  huf = Z_to_bv 64 (DCTX + 10296) /\ huf_tbl_at m (DCTX + 10296).
Proof. intros m DCTX huf le (E & dtb & B & _ & T) NZ. split; [exact E|]. exists dtb. split; [exact B | exact (T NZ)]. Qed.

(* [comment removed for export] *)
Definition HUF_1X_STACK : Z := 144.
Definition HUF_4X_STACK : Z := 912.             (* [comment removed for export] *)
Definition HUF_TBL_STACK : Z := 1024.
Definition HUF_1X1W_STACK : Z := 48 + HUF_TBL_STACK.
Definition HUF_4XW_STACK : Z := 64 + HUF_TBL_STACK.

(* [comment removed for export] *)
Definition huf_dec_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DST dcap lo fr : Z) (extra : list (Z * Z)) (m : fmem) (Q : fmem -> Z -> Prop) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch ((DST, DST + dcap) :: extra ++ [(SPV - fr, SPV)]) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV /\ stk usegs m' DST (DST + dcap)
    /\ (r = dcap \/ zd_is_error r = true) /\ 0 <= r < 2^64 /\ Q m' r.

(* [comment removed for export] *)
Definition huf_dec_pre (m : fmem) (SPV lo fr DST dcap SRC n : Z) (src : list byte) : Prop :=
  mem_inv usegs m /\
  stk usegs m lo SPV /\ 4096 <= lo /\ lo <= SPV - fr /\ SPV < 2^47 /\
  stk usegs m DST (DST + dcap) /\ 4096 <= DST /\ 0 <= dcap < 2^32 /\ DST + dcap < 2^47 /\
  bytes_at usegs m SRC src /\ zlen src = n /\ 4096 <= SRC /\ n < 2^32 /\ SRC + n < 2^47 /\
  (DST + dcap <= lo \/ SPV <= DST) /\ (SRC + n <= lo \/ SPV <= SRC) /\ (DST + dcap <= SRC \/ SRC + n <= DST) /\ SPV mod 16 = 0.

(* [comment removed for export] *)
Definition huf_dt_pre (m : fmem) (SPV lo DST dcap DT : Z) (dtb : list byte) : Prop :=
  bytes_at usegs m DT dtb /\ zlen dtb = HUF_DTABLE_BYTES /\ 4096 <= DT /\ DT + HUF_DTABLE_BYTES < 2^47 /\
  (DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT) /\ (DST + dcap <= DT \/ DT + HUF_DTABLE_BYTES <= DST) /\ DT mod 4 = 0.

Definition huf_noQ : fmem -> Z -> Prop := fun _ _ => True.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition huf_using_stmt_at (ENTRY fr : Z) : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV DST dcap SRC n DT lo : Z) (src dtb : list byte),
  huf_dec_pre m SPV lo fr DST dcap SRC n src ->
  huf_dt_pre m SPV lo DST dcap DT dtb -> huf_tbl_ok dtb ->
  evt usegs (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo fr [] m huf_noQ)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).

Definition huf_1x_stmt : Prop := huf_using_stmt_at PHUF_1X HUF_1X_STACK.
Definition huf_4x_stmt : Prop := huf_using_stmt_at PHUF_4X HUF_4X_STACK.

(* [comment removed for export] *)
Definition huf_built (DT : Z) : fmem -> Z -> Prop :=
  fun m' r => exists dtb', u8arr usegs m' DT dtb' /\ huf_hdr_ok dtb' /\ (zd_is_error r = false -> huf_tbl_ok dtb').

Definition huf_wksp_stmt_at (ENTRY fr : Z) : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 flags s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV DST dcap SRC n DT WK wksz lo : Z) (src dtb : list byte),
  huf_dec_pre m SPV lo fr DST dcap SRC n src ->
  (* [comment removed for export] *)
  u8arr usegs m DT dtb -> huf_hdr_ok dtb -> 4096 <= DT -> DT + HUF_DTABLE_BYTES < 2^47 -> DT mod 4 = 0 ->
  (* [comment removed for export] *)
  stk usegs m WK (WK + wksz) -> 4096 <= WK -> 0 <= wksz < 2^32 -> WK + wksz < 2^47 -> WK mod 4 = 0 ->
  (* [comment removed for export] *)
  (DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT) -> (WK + wksz <= lo \/ SPV <= WK) ->
  (DST + dcap <= DT \/ DT + HUF_DTABLE_BYTES <= DST) -> (DST + dcap <= WK \/ WK + wksz <= DST) ->
  (DT + HUF_DTABLE_BYTES <= WK \/ WK + wksz <= DT) ->
  (DT + HUF_DTABLE_BYTES <= SRC \/ SRC + n <= DT) -> (WK + wksz <= SRC \/ SRC + n <= WK) ->
  evt usegs (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo fr
               [(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz)] m
               (fun m' r => huf_built DT m' r /\ stk usegs m' WK (WK + wksz)))
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC)
               (Z_to_bv 64 n) (Z_to_bv 64 WK) (Z_to_bv 64 wksz) flags s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).

Definition huf_1x1_wksp_stmt : Prop := huf_wksp_stmt_at PHUF_1X1_WKSP HUF_1X1W_STACK.
Definition huf_4x_wksp_stmt : Prop := huf_wksp_stmt_at PHUF_4X_WKSP HUF_4XW_STACK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PHUF_RDX1 : Z := 0x1e73c.
Definition PHUF_RDX2 : Z := 0x1f334.

Definition huf_rd_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DT WK wksz lo : Z) (x2 : bool) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r dtb',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz); (SPV - HUF_TBL_STACK, SPV)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV /\ stk usegs m' WK (WK + wksz)
    /\ u8arr usegs m' DT dtb' /\ huf_hdr_ok dtb' /\ 0 <= r < 2^64
    /\ (zd_is_error r = false ->
        huf_tbl_ok dtb' /\ exists ty, nth_error dtb' 1 = Some ty /\ (bv_unsigned ty <> 0 <-> x2 = true)).

Definition huf_rd_stmt_at (ENTRY : Z) (x2 : bool) : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV SRC n DT WK wksz lo : Z) (src dtb : list byte),
  mem_inv usegs m ->
  stk usegs m lo SPV -> 4096 <= lo -> lo <= SPV - HUF_TBL_STACK -> SPV < 2^47 -> SPV mod 16 = 0 ->
  bytes_at usegs m SRC src -> zlen src = n -> 4096 <= SRC -> n < 2^32 -> SRC + n < 2^47 ->
  u8arr usegs m DT dtb -> huf_hdr_ok dtb -> 4096 <= DT -> DT + HUF_DTABLE_BYTES < 2^47 -> DT mod 4 = 0 ->
  stk usegs m WK (WK + wksz) -> 4096 <= WK -> 0 <= wksz < 2^32 -> WK + wksz < 2^47 -> WK mod 4 = 0 ->
  (DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT) -> (WK + wksz <= lo \/ SPV <= WK) -> (SRC + n <= lo \/ SPV <= SRC) ->
  (DT + HUF_DTABLE_BYTES <= WK \/ WK + wksz <= DT) ->
  (DT + HUF_DTABLE_BYTES <= SRC \/ SRC + n <= DT) -> (WK + wksz <= SRC \/ SRC + n <= WK) ->
  evt usegs (huf_rd_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT WK wksz lo x2 m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 WK)
               (Z_to_bv 64 wksz) flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).

Definition huf_rdx1_stmt : Prop := huf_rd_stmt_at PHUF_RDX1 false.
Definition huf_rdx2_stmt : Prop := huf_rd_stmt_at PHUF_RDX2 true.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition huf_int_stmt_at (ENTRY fr : Z) (x2 : bool) : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV DST dcap SRC n DT tl lo : Z) (src dtb : list byte),
  huf_dec_pre m SPV lo fr DST dcap SRC n src ->
  huf_dt_pre m SPV lo DST dcap DT dtb ->
  nth_error dtb 2 = Some (Z_to_bv 8 tl) -> 1 <= tl <= 12 -> (x2 = true -> huf_x2_ok dtb tl) -> huf_nb_ok x2 dtb tl ->
  evt usegs (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo fr [] m huf_noQ)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).

Definition huf_1x1_stmt : Prop := huf_int_stmt_at PHUF_1X1 HUF_1X_STACK false.
Definition huf_1x2_stmt : Prop := huf_int_stmt_at PHUF_1X2 HUF_1X_STACK true.
Definition huf_4x1_stmt : Prop := huf_int_stmt_at PHUF_4X1 HUF_4X_STACK false.
Definition huf_4x2_stmt : Prop := huf_int_stmt_at PHUF_4X2 HUF_4X_STACK true.
