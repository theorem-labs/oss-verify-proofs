(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 huf41_kit_x41ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41Q.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Lemma x41_ft : forall (k : nat) mb mm j pe
      (x1 x5 x6 x8 x9 x10 x11 x12 x14 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    pe - j <= Z.of_nat k -> 0 <= j < pe -> pe <= dcap ->
    (forall mm' (y12 y13 y14 y15 y17 y27 : word),
        munch WD mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        evt usegs POST (ST 0x22b2c mm' x1 x5 x6 (Z_to_bv 64 2) x8 x9 x10 x11 y12 y13 y14 y15 (Z_to_bv 64 (-1 * DT + -5)) y17 x18 x19 x20 (Z_to_bv 64 (DT + 4)) x22 x23 x24 x25 x26 y27 x28 x29 x30 x31)) ->
    evt usegs POST (ST 0x22aec mm x1 x5 x6 (Z_to_bv 64 2) x8 x9 x10 x11 x12 (Z_to_bv 64 (pe - j)) x14 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (DST + j)) x18 x19 x20 (Z_to_bv 64 (DT + 4)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mb mm j pe x1 x5 x6 x8 x9 x10 x11 x12 x14 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      MU WM MI OUT DTB HK HJ HPE K; [exfalso; lia|].
    kx_autoLx [0x22aec; 0x22b2c; 0x253c0] 40%nat
      [KZRange (pe - j) 1 (2^32); KZRange (dcap - j) 1 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32);
       KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZWr DST dcap; KZDisj DST dcap DT 16388]
      [(DT, 16388)].
    all: x41_ck.
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 142060) _ _ _ _) =>
             replace (j + DST + 1) with (DST + (j + 1)) in * by lia;
             replace (pe + -1 * j + -1) with (pe - (j + 1)) in * by lia;
             eapply (IH mb _ (j + 1) pe); try eassumption; try lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 142124) _ _ _ _) => eapply K; eassumption
         end.
  Qed.

  Notation SINV := RZ_huf_dx41.SINV.
  Ltac x41_fl_run ROOM ROOM2 OFF :=
    lazymatch goal with
    | SB : bytes_at usegs _ ?SRC ?src, SL : zlen ?src = ?n
      |- evt _ _ (MS (mkR (Z_to_bv 64 (?SRC + ?off)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?j)) _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?pe)) _ (Z_to_bv 64 ?bc) _ _ _ _) _ _ _ _ _ _) =>
        kx_autoLx [0x22824; 0x22aec; 0x22b2c; 0x253c0] 160%nat
          [ROOM2; ROOM; KZRange (n - off) 8 (2^32); OFF; KZRange bc 0 64;
           KZRange n 9 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
           KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange DT 4096 (2^47);
           KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap SRC n]
          [(DT, 16388); (SRC, n)]
    end.

  (* [comment removed for export] *)
  Lemma x41_fl : forall (k : nat) mb mm j pe off bc SRC n src
      (x5 x6 x9 x10 x11 x12 x13 x14 x19 x20 x26 x29 x31 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 -> (DST + dcap <= SRC \/ SRC + n <= DST) ->
    pe - j <= Z.of_nat k -> 0 <= j <= pe -> pe <= dcap -> SINV off n bc -> 0 <= bc < 2^64 ->
    (forall mm' (y1 y5 y6 y8 y9 y12 y13 y14 y15 y17 y18 y19 y20 y22 y23 y24 y27 : word),
        munch WD mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        evt usegs POST (ST 0x22b2c mm' y1 y5 y6 (Z_to_bv 64 2) y8 y9 x10 x11 y12 y13 y14 y15 (Z_to_bv 64 (-1 * DT + -5)) y17 y18 y19 y20 (Z_to_bv 64 (DT + 4)) y22 y23 y24 (Z_to_bv 64 (DST + pe)) x26 y27 (Z_to_bv 64 (-1)) x29 (Z_to_bv 64 64) x31)) ->
    evt usegs POST (ST 0x22824 mm (Z_to_bv 64 (SRC + off)) x5 x6 (Z_to_bv 64 2) (Z_to_bv 64 SRC) x9 x10 x11 x12 x13 x14 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (SRC + 8)) x19 x20 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + pe - 3)) (Z_to_bv 64 (DST + j + 3)) (Z_to_bv 64 (DST + pe)) x26 (Z_to_bv 64 bc) (Z_to_bv 64 (-1)) x29 (Z_to_bv 64 64) x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH];
      intros mb mm j pe off bc SRC n src x5 x6 x9 x10 x11 x12 x13 x14 x19 x20 x26 x29 x31
        MU WM MI OUT DTB SB SL S0 S1 SL32 DJS HK HJ HPE HS HB K.
    all: destruct HS as [-> | (O1 & O2 & B1)].
    all: try (destruct (Z_lt_le_dec (pe - j) 4) as [RM|RM]);
         try (destruct (Z_lt_le_dec off 8) as [O8|O8]).
    all: try solve [exfalso; lia].
    all: lazymatch goal with
         | RM : 4 <= _ - _, O8 : 8 <= _ |- _ => x41_fl_run (KZRange (pe - j) 4 (2^32)) (KZRange (dcap - j) 4 (2^32)) (KZRange off 8 (2^32))
         | RM : 4 <= _ - _, O8 : _ < 8 |- _ => x41_fl_run (KZRange (pe - j) 4 (2^32)) (KZRange (dcap - j) 4 (2^32)) (KZRange off 1 7)
         | RM : _ - _ < 4, O8 : 8 <= _ |- _ => x41_fl_run (KZRange (pe - j) 0 3) (KZRange (dcap - j) 0 (2^32)) (KZRange off 8 (2^32))
         | RM : _ - _ < 4, O8 : _ < 8 |- _ => x41_fl_run (KZRange (pe - j) 0 3) (KZRange (dcap - j) 0 (2^32)) (KZRange off 1 7)
         | _ => kx_autoLx [0x22824; 0x22aec; 0x22b2c; 0x253c0] 30%nat
                  [KZRange SRC 4096 (2^47); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)]
                  (@nil (Z * Z))
         end.
    all: x41_ck.
    all: kx_ev_ranges; kx_mem; rewrite ?(Z.mod_small bc (2^64)) in * by lia; kx_land_ranges; kx_strip_mod.
    all: try replace (DST + j + 4) with (DST + (j + 4)) in * by lia.
    all: try replace (DST + j + 7) with (DST + (j + 4) + 3) in * by lia.
    all: try replace (-1 * j + pe + -4) with (pe - (j + 4)) in * by lia.
    all: try replace (-1 * j + pe) with (pe - j) in * by lia.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 142060) _ _ _ _) =>
             eapply (x41_ft (Z.to_nat dcap) mb); try eassumption; try lia; intros; eapply K; eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 142124) _ _ _ _) => eapply K; eassumption
         | |- evt _ _ (MS (mkR (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 141348) _ _ _ _) =>
             replace X with (SRC + (X - SRC)) by lia;
             eapply (IH mb); try eassumption; try lia; try solve [unfold RZ_huf_dx41.SINV; lia];
             try solve [exact (bv_unsigned_in_range 64 _)]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_fe : forall mb mm j pe off bc SRC n src
      (x5 x6 x9 x10 x11 x12 x13 x14 x15 x19 x20 x23 x24 x26 x29 x31 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 -> (DST + dcap <= SRC \/ SRC + n <= DST) ->
    0 <= j <= pe -> pe <= dcap -> SINV off n bc -> 0 <= bc < 2^64 ->
    (forall mm' (y1 y5 y6 y8 y9 y12 y13 y14 y15 y17 y18 y19 y20 y22 y23 y24 y27 : word),
        munch WD mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        evt usegs POST (ST 0x22b2c mm' y1 y5 y6 (Z_to_bv 64 2) y8 y9 x10 x11 y12 y13 y14 y15 (Z_to_bv 64 (-1 * DT + -5)) y17 y18 y19 y20 (Z_to_bv 64 (DT + 4)) y22 y23 y24 (Z_to_bv 64 (DST + pe)) x26 y27 (Z_to_bv 64 (-1)) x29 (Z_to_bv 64 64) x31)) ->
    evt usegs POST (ST 0x229d0 mm (Z_to_bv 64 (SRC + off)) x5 x6 (Z_to_bv 64 2) (Z_to_bv 64 SRC) x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (SRC + 8)) x19 x20 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + pe)) x23 x24 (Z_to_bv 64 (DST + pe)) x26 (Z_to_bv 64 bc) (Z_to_bv 64 (-1)) x29 (Z_to_bv 64 64) x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe off bc SRC n src x5 x6 x9 x10 x11 x12 x13 x14 x15 x19 x20 x23 x24 x26 x29 x31
      MU WM MI OUT DTB SB SL S0 S1 SL32 DJS HJ HPE HS HB K.
    destruct HS as [-> | (O1 & O2 & B1)]; [|destruct (Z_lt_le_dec off 8) as [O8|O8]].
    all: lazymatch goal with
         | O8 : _ < 8 |- _ =>
             kx_autoLx [0x22aec; 0x22b2c; 0x253c0] 120%nat
               [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange bc 0 64; KZRange n 9 (2^32); KZRange SRC 4096 (2^47);
                KZRange (SRC + n) 4096 (2^47); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)]
               [(SRC, n)]
         | O8 : 8 <= _ |- _ =>
             kx_autoLx [0x22aec; 0x22b2c; 0x253c0] 120%nat
               [KZRange (n - off) 8 (2^32); KZRange off 8 (2^32); KZRange bc 0 64; KZRange n 9 (2^32); KZRange SRC 4096 (2^47);
                KZRange (SRC + n) 4096 (2^47); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)]
               [(SRC, n)]
         | _ => kx_autoLx [0x22aec; 0x22b2c; 0x253c0] 30%nat
                  [KZRange SRC 4096 (2^47); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32);
                   KZRange DST 4096 (2^47)] (@nil (Z * Z))
         end.
    all: x41_ck.
    all: try replace (-1 * j + pe) with (pe - j) in * by lia.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 142060) _ _ _ _) =>
             eapply (x41_ft (Z.to_nat dcap) mb); try eassumption; try lia; intros; eapply K; eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 142124) _ _ _ _) => eapply K; eassumption
         end.
  Qed.

End DX41Q.
