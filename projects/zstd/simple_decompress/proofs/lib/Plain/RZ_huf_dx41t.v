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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_fkit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41T.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 432 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -416)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).


  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Lemma x41_fi : forall (r : nat) mb mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3 f0 f1 f2 f3
      (x1 x8 x9 x10 x11 x12 x13 x15 x16 x18 x20 x22 x23 x26 x27 x28 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    bytes_at psegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 -> (DST + dcap <= SRC \/ SRC + n <= DST) ->
    (1 <= r)%nat -> f0 = o0 + 5 * Z.of_nat r -> f1 = o1 + 5 * Z.of_nat r -> f2 = o2 + 5 * Z.of_nat r -> f3 = o3 + 5 * Z.of_nat r ->
    0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 -> f0 <= dcap -> f1 <= dcap -> f2 <= dcap -> f3 <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n ->
    (forall mm' I0 I1 I2 I3 (y1 y8 y9 y11 y12 y13 y15 y16 y18 y20 y22 y26 y27 y28 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        0 <= I0 -> 0 <= I1 -> 0 <= I2 -> 0 <= I3 -> I0 + 8 <= n -> I1 + 8 <= n -> I2 + 8 <= n -> I3 + 8 <= n ->
        evt psegs POST (ST 0x21e28 mm' y1 (Z_to_bv 64 (SRC + I2)) (Z_to_bv 64 (SRC + I1)) (Z_to_bv 64 (SRC + I0)) y8 y9 x10 y11 y12 y13 (Z_to_bv 64 69944) y15 y16 (Z_to_bv 64 (SRC + I3)) y18 (Z_to_bv 64 (DT + 4)) y20 (Z_to_bv 64 (DST + f3)) y22 x23 (Z_to_bv 64 69156) (Z_to_bv 64 (DST + f3)) y26 y27 y28 (Z_to_bv 64 (DST + f0)) (Z_to_bv 64 (DST + f1)) (Z_to_bv 64 (DST + f2)))) ->
    evt psegs POST (ST 0x21e84 mm x1 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i0)) x8 x9 x10 x11 x12 x13 (Z_to_bv 64 69944) x15 x16 (Z_to_bv 64 (SRC + i3)) x18 (Z_to_bv 64 (DT + 4)) x20 (Z_to_bv 64 (DST + o3)) x22 x23 (Z_to_bv 64 69156) (Z_to_bv 64 (DST + f3)) x26 x27 x28 (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2))).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction r as [|r IH]; intros mb mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3 f0 f1 f2 f3 x1 x8 x9 x10 x11 x12 x13 x15 x16 x18 x20 x22 x23 x26 x27 x28
      MU WM MI OUT DTB SB SL S0 S1 SL32 DJS HR HF0 HF1 HF2 HF3 HO0 HO1 HO2 HO3 HD0 HD1 HD2 HD3 HI0 HI1 HI2 HI3 HN0 HN1 HN2 HN3 K;
      [exfalso; lia|].
    assert (TBLC : tbl_in psegs mm HUF_CTZ_TBL 64 1 0 0 63) by exact (huf_ctz_tbl mm MI).
    clear OS1.
    Time kx_auto [0x21e84; 0x21e28] 400%nat
      [KZRange (dcap - o0) 5 (2^32); KZRange (dcap - o1) 5 (2^32); KZRange (dcap - o2) 5 (2^32); KZRange (dcap - o3) 5 (2^32);
       KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32); KZRange f3 0 (2^32);
       KZRange i0 7 (2^32); KZRange i1 7 (2^32); KZRange i2 7 (2^32); KZRange i3 7 (2^32);
       KZRange (n - i0) 8 (2^32); KZRange (n - i1) 8 (2^32); KZRange (n - i2) 8 (2^32); KZRange (n - i3) 8 (2^32);
       KZRange n 15 (2^32); KZRange dcap 5 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange DST 4096 (2^47);
       KZRange DT 4096 (2^47); KZTbl HUF_CTZ_TBL 64 1 0 0 63; KZImg 0x10000 0x14000;
       KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap SRC n]
      [(DT, 16388); (SRC, n); (0x11138, 64); (0x110e0, 8)].
    all: kx_ev_ranges; kx_mem.
    all: replace (DST + o0 + 5) with (DST + (o0 + 5)) by lia; replace (DST + o1 + 5) with (DST + (o1 + 5)) by lia;
         replace (DST + o2 + 5) with (DST + (o2 + 5)) by lia; replace (DST + o3 + 5) with (DST + (o3 + 5)) by lia.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ (Z_to_bv 64 (_ + ?I2)) (Z_to_bv 64 (_ + ?I1)) (Z_to_bv 64 (_ + ?I0)) _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (_ + ?I3)) _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 138884) _ _ ?m2 _) =>
             eapply (IH mb m2 SRC n src I0 I1 I2 I3 (o0 + 5) (o1 + 5) (o2 + 5) (o3 + 5) f0 f1 f2 f3); try eassumption; try lia
         | |- evt _ _ (MS (mkR _ _ _ _ (Z_to_bv 64 (_ + ?I2)) (Z_to_bv 64 (_ + ?I1)) (Z_to_bv 64 (_ + ?I0)) _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (_ + ?I3)) _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 138792) _ _ ?m2 _) =>
             replace (o0 + 5) with f0 by lia; replace (o1 + 5) with f1 by lia; replace (o2 + 5) with f2 by lia;
             replace (o3 + 5) with f3 by lia;
             eapply (K m2 I0 I1 I2 I3); try eassumption; try lia
         end.
  Qed.

End DX41T.
