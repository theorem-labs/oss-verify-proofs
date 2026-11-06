(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41Q.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 432 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -416)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  (* [comment removed for export] *)
  Lemma x41_ft : forall (k : nat) mb mm j pe
      (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x30 x31 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    pe - j <= Z.of_nat k -> 0 <= j < pe -> pe <= dcap ->
    (forall mm' (y11 y12 y20 y21 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        evt psegs POST (ST 0x22688 mm' x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (DT + 4)) y11 y12 x13 x14 x15 x16 x17 x18 x19 y20 y21 x22 x23 x24 x25 x26 x27 x28 (Z_to_bv 64 (DST + pe)) x30 x31)) ->
    evt psegs POST (ST 0x2265c mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (DT + 4)) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (DST + j)) x21 x22 x23 x24 x25 x26 x27 x28 (Z_to_bv 64 (DST + pe)) x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mb mm j pe x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x30 x31
      MU WM MI OUT DTB HK HJ HPE K; [exfalso; lia|].
    kx_autoLx [0x2265c; 0x22688] 30%nat
      [KZRange (dcap - j) 1 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
       KZRange DT 4096 (2^47); KZWr DST dcap; KZDisj DST dcap DT 16388]
      [(DT, 16388)].
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 140892) _ _ _ _) =>
             replace (DST + j + 1) with (DST + (j + 1)) in * by lia;
             eapply (IH mb _ (j + 1) pe); try eassumption; try lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 140936) _ _ _ _) => eapply K; eassumption
         end.
  Qed.

  Notation SINV := RZ_huf_dx41.SINV.
  Ltac x41_fl_run ROOM ROOM2 OFF :=
    lazymatch goal with
    | SB : bytes_at psegs _ ?SRC ?src, SL : zlen ?src = ?n
      |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 (?SRC + ?off)) _ (Z_to_bv 64 (DST + ?j)) _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?bc) _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?pe)) _ _) _ _ _ _ _ _) =>
        kx_autoLx [0x22414; 0x2265c; 0x2268c] 120%nat
          [ROOM2; ROOM; KZRange (n - off) 8 (2^32); OFF; KZRange bc 0 64;
           KZRange n 9 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
           KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange DT 4096 (2^47);
           KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap SRC n]
          [(DT, 16388); (SRC, n)]
    end.

  (* [comment removed for export] *)
  Lemma x41_fl : forall (k : nat) mb mm j pe off bc SRC n src
      (x1 x5 x6 x7 x8 x12 x14 x15 x16 x17 x18 x19 x20 x24 x25 x26 x27 x30 x31 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    bytes_at psegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 -> (DST + dcap <= SRC \/ SRC + n <= DST) ->
    pe - j <= Z.of_nat k -> 0 <= j <= pe -> pe <= dcap -> SINV off n bc -> 0 <= bc < 2^64 ->
    (forall mm' (y9 y11 y12 y18 y19 y20 y21 y24 y25 y26 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        evt psegs POST (ST 0x22688 mm' x1 x5 x6 x7 x8 y9 (Z_to_bv 64 (DT + 4)) y11 y12 (Z_to_bv 64 (DST + pe - 3)) x14 x15 x16 x17 y18 y19 y20 y21 (Z_to_bv 64 SRC) (Z_to_bv 64 (SRC + 8)) y24 y25 y26 x27 (Z_to_bv 64 64) (Z_to_bv 64 (DST + pe)) x30 x31)) ->
    (forall mm' (y9 y11 y12 y18 y19 y20 y21 y24 y25 y26 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        evt psegs POST (ST 0x2268c mm' x1 x5 x6 x7 x8 y9 (Z_to_bv 64 (DT + 4)) y11 y12 (Z_to_bv 64 (DST + pe - 3)) x14 x15 x16 x17 y18 y19 y20 y21 (Z_to_bv 64 SRC) (Z_to_bv 64 (SRC + 8)) y24 y25 y26 x27 (Z_to_bv 64 64) (Z_to_bv 64 (DST + pe)) x30 x31)) ->
    evt psegs POST (ST 0x22414 mm x1 x5 x6 x7 x8 (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + j)) x12 (Z_to_bv 64 (DST + pe - 3)) x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 bc) (Z_to_bv 64 SRC) (Z_to_bv 64 (SRC + 8)) x24 x25 x26 x27 (Z_to_bv 64 64) (Z_to_bv 64 (DST + pe)) x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH];
      intros mb mm j pe off bc SRC n src x1 x5 x6 x7 x8 x12 x14 x15 x16 x17 x18 x19 x20 x24 x25 x26 x27 x30 x31
        MU WM MI OUT DTB SB SL S0 S1 SL32 DJS HK HJ HPE HS HB K2 K1.
    all: destruct HS as [-> | (O1 & O2 & B1)].
    all: try (destruct (Z_lt_le_dec (pe - j) 4) as [RM|RM]);
         try (destruct (Z_lt_le_dec off 8) as [O8|O8]).
    all: try solve [exfalso; lia].
    all: lazymatch goal with
         | RM : 4 <= _ - _, O8 : 8 <= _ |- _ => x41_fl_run (KZRange (pe - j) 4 (2^32)) (KZRange (dcap - j) 4 (2^32)) (KZRange off 8 (2^32))
         | RM : 4 <= _ - _, O8 : _ < 8 |- _ => x41_fl_run (KZRange (pe - j) 4 (2^32)) (KZRange (dcap - j) 4 (2^32)) (KZRange off 1 7)
         | RM : _ - _ < 4, O8 : 8 <= _ |- _ => x41_fl_run (KZRange (pe - j) 0 3) (KZRange (dcap - j) 0 (2^32)) (KZRange off 8 (2^32))
         | RM : _ - _ < 4, O8 : _ < 8 |- _ => x41_fl_run (KZRange (pe - j) 0 3) (KZRange (dcap - j) 0 (2^32)) (KZRange off 1 7)
         | _ => kx_autoLx [0x22414; 0x2265c; 0x2268c] 20%nat
                  [KZRange SRC 4096 (2^47); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)]
                  (@nil (Z * Z))
         end.
    all: kx_ev_ranges; kx_mem; rewrite ?(Z.mod_small bc (2^64)) in * by lia; kx_land_ranges; kx_strip_mod.
    all: try replace (DST + j + 4) with (DST + (j + 4)) in * by lia.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 140892) _ _ _ _) =>
             eapply (x41_ft (Z.to_nat dcap) mb); try eassumption; try lia; intros; eapply K2; eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 140940) _ _ _ _) => eapply K1; eassumption
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 140308) _ _ _ _) =>
             replace X with (SRC + (X - SRC)) by lia;
             eapply (IH mb); try eassumption; try lia; try solve [unfold RZ_huf_dx41.SINV; lia];
             try solve [exact (bv_unsigned_in_range 64 _)]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_fe : forall mb mm j pe off bc SRC n src
      (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x24 x25 x26 x27 x28 x30 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    bytes_at psegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 -> (DST + dcap <= SRC \/ SRC + n <= DST) ->
    0 <= j <= pe -> pe <= dcap -> SINV off n bc -> 0 <= bc < 2^64 ->
    (forall mm' (y9 y11 y12 y13 y18 y19 y20 y21 y24 y25 y26 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        evt psegs POST (ST 0x22688 mm' x1 x5 x6 x7 x8 y9 (Z_to_bv 64 (DT + 4)) y11 y12 y13 x14 x15 x16 x17 y18 y19 y20 y21 (Z_to_bv 64 SRC) (Z_to_bv 64 (SRC + 8)) y24 y25 y26 x27 x28 (Z_to_bv 64 (DST + pe)) x30 (Z_to_bv 64 (DST + j)))) ->
    (forall mm' (y9 y11 y12 y13 y18 y19 y20 y21 y24 y25 y26 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        evt psegs POST (ST 0x2268c mm' x1 x5 x6 x7 x8 y9 (Z_to_bv 64 (DT + 4)) y11 y12 y13 x14 x15 x16 x17 y18 y19 y20 y21 (Z_to_bv 64 SRC) (Z_to_bv 64 (SRC + 8)) y24 y25 y26 x27 x28 (Z_to_bv 64 (DST + pe)) x30 (Z_to_bv 64 (DST + j)))) ->
    evt psegs POST (ST 0x22548 mm x1 x5 x6 x7 x8 (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (DT + 4)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 bc) (Z_to_bv 64 SRC) (Z_to_bv 64 (SRC + 8)) x24 x25 x26 x27 x28 (Z_to_bv 64 (DST + pe)) x30 (Z_to_bv 64 (DST + j))).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe off bc SRC n src x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x24 x25 x26 x27 x28 x30
      MU WM MI OUT DTB SB SL S0 S1 SL32 DJS HJ HPE HS HB K2 K1.
    destruct HS as [-> | (O1 & O2 & B1)]; [|destruct (Z_lt_le_dec off 8) as [O8|O8]].
    all: lazymatch goal with
         | O8 : _ < 8 |- _ =>
             kx_autoLx [0x2265c; 0x2268c] 120%nat
               [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange bc 0 64; KZRange n 9 (2^32); KZRange SRC 4096 (2^47);
                KZRange (SRC + n) 4096 (2^47); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)]
               [(SRC, n)]
         | O8 : 8 <= _ |- _ =>
             kx_autoLx [0x2265c; 0x2268c] 120%nat
               [KZRange (n - off) 8 (2^32); KZRange off 8 (2^32); KZRange bc 0 64; KZRange n 9 (2^32); KZRange SRC 4096 (2^47);
                KZRange (SRC + n) 4096 (2^47); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)]
               [(SRC, n)]
         | _ => kx_autoLx [0x2265c; 0x2268c] 30%nat
                  [KZRange SRC 4096 (2^47); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32);
                   KZRange DST 4096 (2^47)] (@nil (Z * Z))
         end.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 140892) _ _ _ _) =>
             eapply (x41_ft (Z.to_nat dcap) mb); try eassumption; try lia; intros; eapply K2; eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 140940) _ _ _ _) => eapply K1; eassumption
         end.
  Qed.

End DX41Q.
