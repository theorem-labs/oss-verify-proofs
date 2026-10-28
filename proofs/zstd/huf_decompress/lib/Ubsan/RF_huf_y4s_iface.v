(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_h_iface RF_huf_dec_iface.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition PY4_BODY : Z := 0x1a838.
Definition PY4_RET : Z := 0x16d68.

Definition SPLB (v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 : Z) (j0 : list byte) : list cell :=
  [CB 8 j0; C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v16); C8 (Z_to_bv 64 v24); C8 (Z_to_bv 64 v32); C8 (Z_to_bv 64 v40);
   C8 (Z_to_bv 64 v48); C8 (Z_to_bv 64 v56); C8 (Z_to_bv 64 v64); C8 (Z_to_bv 64 v72); C8 (Z_to_bv 64 v80);
   C8 (Z_to_bv 64 v88); C8 (Z_to_bv 64 v96); C8 (Z_to_bv 64 v104); C8 (Z_to_bv 64 v112); C8 (Z_to_bv 64 v120);
   C8 (Z_to_bv 64 v128)].

Section CANSEC1. Context {rc : runConstT}.
Section Y4S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition Y4S (mm : fmem) : Prop :=
    (exists buf, u8arr usegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at usegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at usegs mm (DT + 4) cbs
    /\ bytes_at usegs mm DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ stk usegs mm lo (SP + -104)
    /\ rw_cells usegs mm (SP + -104) FRS
    /\ mem_inv usegs mm /\ munch DW m0 mm /\ wmono usegs m0 mm.

  Definition Y4F (mm : fmem) (spl b4 b3 b2 b1 : list cell) : Prop :=
    (exists buf, u8arr usegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at usegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at usegs mm (DT + 4) cbs
    /\ stk usegs mm lo (SP + -912)
    /\ rw_cells usegs mm (SP + -912) spl /\ cells_size spl = 136%nat
    /\ rw_cells usegs mm (SP + -776) b4 /\ cells_size b4 = 40%nat
    /\ rw_cells usegs mm (SP + -736) b3 /\ cells_size b3 = 40%nat
    /\ rw_cells usegs mm (SP + -696) b2 /\ cells_size b2 = 40%nat
    /\ rw_cells usegs mm (SP + -656) b1 /\ cells_size b1 = 40%nat
    /\ (exists u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11, rw_cells usegs mm (SP + -616)
          [C8 u11; C8 u10; C8 u9; C8 u8; C8 u7; C8 u6; C8 u5; C8 u4; C8 u3; C8 u2; C8 u1; C8 u0; C8 (Z_to_bv 64 PY4_RET)])
    /\ (exists jl, rw_cells usegs mm (SP + -512) [CB 408 jl])
    /\ rw_cells usegs mm (SP + -104) FRS
    /\ mem_inv usegs mm /\ munch DW m0 mm /\ wmono usegs m0 mm.

  Definition SPS4 (w0 w8 w64 w72 w80 w88 w96 w104 w112 : Z) : list word :=
    map (Z_to_bv 64) [w0; w8; SS; n; DT; DST; dcap; DST + dcap; w64; w72; w80; w88; w96; w104; w112; DT + 4].

  Definition Y4M (mm : fmem) (sps ws ops ips bts : list word) : Prop :=
    (exists buf, u8arr usegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at usegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at usegs mm (DT + 4) cbs
    /\ stk usegs mm lo (SP + -512)
    /\ u64arr usegs mm (SP + -512) sps /\ length sps = 16%nat
    /\ u64arr usegs mm (SP + -384) ws /\ length ws = 19%nat
    /\ (exists jo, rw_cells usegs mm (SP + -232) [CB 32 jo])
    /\ u64arr usegs mm (SP + -200) ops /\ length ops = 4%nat
    /\ u64arr usegs mm (SP + -168) ips /\ length ips = 4%nat
    /\ u64arr usegs mm (SP + -136) bts /\ length bts = 4%nat
    /\ rw_cells usegs mm (SP + -104) FRS
    /\ mem_inv usegs mm /\ munch DW m0 mm /\ wmono usegs m0 mm.

  (* [comment removed for export] *)
  Definition y4_slow_goal : Prop :=
    forall mm (t0 t1 t2 x8 x9 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    Y4S mm ->
    evt usegs POST (MS (mkR (Z_to_bv 64 PY4_RET) (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9
                           (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SS) (Z_to_bv 64 n) (Z_to_bv 64 DT) a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 PY4_BODY) fc None mm (seg_rom usegs)).
End Y4S.

(* [comment removed for export] *)
Definition y4_slow_stmt : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte),
  x2_table_ok cells tl ->
  cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells) ->
  zlen cbs = 4 * 2^tl ->
  1 <= mtl <= 12 -> tl <= mtl ->
  0 <= DST -> (0 < dcap -> 8 <= DST) -> 0 <= dcap < 2^32 -> DST + dcap <= lo ->
  16 <= SS -> SS + zlen src <= lo -> zlen src < 2^26 -> Forall (fun c => 0 <= c < 256) src ->
  0 < DT -> DT mod 4 = 0 -> DT + 4 + 4 * 2^tl <= lo ->
  (DT + 4 + 4 * 2^tl <= DST \/ DST + dcap <= DT) -> (DST + dcap <= SS \/ SS + zlen src <= DST) ->
  lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2^47 ->
  y4_slow_goal ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs.
End CANSEC1.
