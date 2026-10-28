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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f huf411_kit_rs huf417_kit_rlk huf417_kit_rld.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import huf417_kit_rhi huf417_kit_rlo huf417_kit_rl2 huf417_kit_rl3 huf417_kit_rl4 huf417_kit_rlt.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41H.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis SPVA : rsk_al SPV 16.
  Hypothesis DTA : rsk_al DT 4.

  Notation KH := (huf417_kit_rld.KH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb).
  Notation K4264 := (huf417_kit_rld.K4264 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb).
  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].   (* [comment removed for export] *)

  Lemma x41_r : forall (rest : list byte) (j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 : Z) (b1 b2 b3 b4 pad1 pad2 pad3 pad4 : list byte) (w0 : word),
    KH rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 ->
    K4264 rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0.
  Proof using CTX DJ3 SPVA DTA.
    intros rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 KHH.
    assert (K5 : huf417_kit_rlk.K5004 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb
                   rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0)
      by (eapply x41_rlt; eassumption).
    assert (K47 : huf417_kit_rlk.K4796 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb
                    rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0)
      by (eapply x41_rl4; eassumption).
    assert (K46 : huf417_kit_rlk.K4608 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb
                    rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0)
      by (eapply x41_rl3; eassumption).
    assert (K44 : huf417_kit_rlk.K4448 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb
                    rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0)
      by (eapply x41_rl2; eassumption).
    unfold huf417_kit_rld.K4264.
    intros mm k1 k2 k3 k4 p1 o1 p2 o2 p3 o3 p4 o4 x7 x8 x9 x21 x22 x27 w12 w15 KB FA B1 B2 B3 B4 D1 D2 D3 D4.
    destruct (Z_lt_le_dec o1 8) as [O1 | O1].
    - eapply x41_rlo_k; eassumption.
    - eapply x41_r_hi; eassumption.
  Qed.

End DX41H.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
