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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_fkit2.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_20.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis TL11 : tl = 11.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 432 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation WDF := [(DST, DST + dcap); (SPV - 416, SPV - 216)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -416)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 :=
    (rw_cells psegs mm (SPV + -416) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16; C8 w17; C8 w18; C8 w19]).
  Notation SINV := RZ_huf_dx41.SINV.
  Notation WD4 := [(DST, DST + dcap); (SPV - 256, SPV - 216)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells psegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).

  (* [comment removed for export] *)
  Lemma x42_tblf : forall mm, bytes_at psegs mm DT dtb -> tbl_in psegs mm DT 8196 4 7 1 2.
  Proof using X2OK TL11.
    intros mm DTB i I0 I1.
    destruct (X2OK i) as (b & Hn & Hr); [rewrite TL11; lia|].
    replace (DT + 4 * i + 7) with (DT + (4 * i + 7)) by lia.
    rewrite (rdval_bytes_at_1 psegs mm DT dtb (4 * i + 7) b DTB ltac:(lia) Hn). exact Hr.
  Qed.

  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Lemma x42_fi : forall (r : nat) mb mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3 OL E0 E1 E2 E3
      (x1 x6 x9 x10 x11 x12 x13 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    bytes_at psegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 -> (DST + dcap <= SRC \/ SRC + n <= DST) ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r ->
    0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= E0 -> o1 + 10 * Z.of_nat r <= E1 -> o2 + 10 * Z.of_nat r <= E2 -> o3 + 10 * Z.of_nat r <= E3 ->
    E0 <= dcap -> E1 <= dcap -> E2 <= dcap -> E3 <= dcap -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n ->
    (forall mm' I0 I1 I2 I3 F0 F1 F2 F3 (y1 y6 y9 y11 y12 y13 y18 y19 y20 y21 y29 y30 y31 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        0 <= I0 -> 0 <= I1 -> 0 <= I2 -> 0 <= I3 -> I0 + 8 <= n -> I1 + 8 <= n -> I2 + 8 <= n -> I3 + 8 <= n ->
        o0 <= F0 <= E0 -> o1 <= F1 <= E1 -> o2 <= F2 <= E2 -> o3 + 5 <= F3 <= E3 ->
        evt psegs POST (ST 0x1e97c mm' y1 (Z_to_bv 64 (SRC + I0)) y6 (Z_to_bv 64 (DST + F2)) (Z_to_bv 64 (DT + 4)) y9 x10 y11 y12 y13 (Z_to_bv 64 69880) (Z_to_bv 64 (SRC + I3)) (Z_to_bv 64 (SRC + I2)) (Z_to_bv 64 (SRC + I1)) y18 y19 y20 y21 x22 (Z_to_bv 64 67960) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (DST + F0)) (Z_to_bv 64 (DST + F1)) (Z_to_bv 64 (DST + F3)) x28 y29 y30 y31)) ->
    evt psegs POST (ST 0x1ea58 mm x1 (Z_to_bv 64 (SRC + i0)) x6 (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DT + 4)) x9 x10 x11 x12 x13 (Z_to_bv 64 69880) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i1)) x18 x19 x20 x21 x22 (Z_to_bv 64 67960) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o3)) x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction r as [|r IH]; intros mb mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3 OL E0 E1 E2 E3 x1 x6 x9 x10 x11 x12 x13 x18 x19 x20 x21 x22 x28 x29 x30 x31
      MU WM MI OUT DTB SB SL S0 S1 SL32 DJS HR HOL HO0 HO1 HO2 HO3 HD0 HD1 HD2 HD3 HE0 HE1 HE2 HE3 HOLR HI0 HI1 HI2 HI3 HN0 HN1 HN2 HN3 K;
      [exfalso; lia|].
    assert (TBLC : tbl_in psegs mm HUF_CTZ_TBL2 64 1 0 0 63) by exact (huf_ctz_tbl2 mm MI).
    assert (TBL : tbl_in psegs mm DT 8196 4 7 1 2) by (apply x42_tblf; exact DTB).
    clear OS1.
    Time kx_auto [0x1ea58; 0x1e97c] 500%nat
      [KZRange (dcap - o0) 10 (2^32); KZRange (dcap - o1) 10 (2^32); KZRange (dcap - o2) 10 (2^32); KZRange (dcap - o3) 10 (2^32);
       KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32); KZRange OL 0 (2^32);
       KZRange i0 7 (2^32); KZRange i1 7 (2^32); KZRange i2 7 (2^32); KZRange i3 7 (2^32);
       KZRange (n - i0) 8 (2^32); KZRange (n - i1) 8 (2^32); KZRange (n - i2) 8 (2^32); KZRange (n - i3) 8 (2^32);
       KZRange n 15 (2^32); KZRange dcap 10 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange DST 4096 (2^47);
       KZRange DT 4096 (2^47); KZTbl HUF_CTZ_TBL2 64 1 0 0 63; KZTbl DT 8196 4 7 1 2; KZImg 0x10000 0x14000;
       KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap SRC n]
      [(DT, 16388); (SRC, n); (0x110f8, 64); (0x110e0, 8)].
    all: kx_ev_ranges; kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ (Z_to_bv 64 (_ + ?I0)) _ (Z_to_bv 64 (DST + ?F2)) _ _ _ _ _ _ _ (Z_to_bv 64 (_ + ?I3)) (Z_to_bv 64 (_ + ?I2)) (Z_to_bv 64 (_ + ?I1)) _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?F0)) (Z_to_bv 64 (DST + ?F1)) (Z_to_bv 64 (DST + ?F3)) _ _ _ _) _ (Z_to_bv 64 125528) _ _ ?m2 _) =>
             eapply (IH mb m2 SRC n src I0 I1 I2 I3 F0 F1 F2 F3 OL E0 E1 E2 E3); try eassumption; try lia;
             intros; eapply K; try eassumption; lia
         | |- evt _ _ (MS (mkR _ _ _ _ (Z_to_bv 64 (_ + ?I0)) _ (Z_to_bv 64 (DST + ?F2)) _ _ _ _ _ _ _ (Z_to_bv 64 (_ + ?I3)) (Z_to_bv 64 (_ + ?I2)) (Z_to_bv 64 (_ + ?I1)) _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?F0)) (Z_to_bv 64 (DST + ?F1)) (Z_to_bv 64 (DST + ?F3)) _ _ _ _) _ (Z_to_bv 64 125308) _ _ ?m2 _) =>
             eapply (K m2 I0 I1 I2 I3 F0 F1 F2 F3); try eassumption; try lia
         end.
  Qed.

End DX42_20.
