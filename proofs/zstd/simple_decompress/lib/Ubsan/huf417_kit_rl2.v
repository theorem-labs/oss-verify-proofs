(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f huf41_kit_x41ck huf417_kit_rlk.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41RL2.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation BDAT mm A c b pad p st lm :=
    (rw_cells usegs mm A [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD2 mm c b pad p st lm := (BDAT mm (SPV + -144) c b pad p st lm).
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation WR2 := [(SPV - 144, SPV - 104)].
  Notation WDF := [(DST, DST + dcap); (SPV - 512, SPV - 336); (SPV - 224, SPV - 104)].
  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Lemma x41_rl2_w : forall mm S2 n2 b2 o2 p2 (k2 : word) pad2
      (x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    8 <= o2 -> o2 + 8 <= n2 -> 0 <= p2 <= 56 ->
    mem_inv usegs mm ->
    BD2 mm k2 (Z_to_bv 64 p2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
    SBUF mm S2 n2 b2 ->
    (forall mm' (c y7 y8 y9 y22 y27 : word),
        munch WR2 mm mm' -> wmono usegs mm mm' -> mem_inv usegs mm' ->
        BD2 mm' c (Z_to_bv 64 (Z.land p2 7)) pad2 (Z_to_bv 64 (S2 + (o2 - p2 / 8))) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
        evt usegs POST (ST 0x23394 mm' (Z_to_bv 64 (Z.land p2 7)) (Z_to_bv 64 (S2 + (o2 - p2 / 8))) x6 y7 y8 y9 x10 x11
                         (Z_to_bv 64 (S2 + (o2 - p2 / 8))) x13 x14 x15 x16 x17 x18 x19 c (Z_to_bv 64 0) y22 x23 x24 x25 x26 y27
                         x28 x29 x30 x31)) ->
    evt usegs POST (ST 0x232f4 mm (Z_to_bv 64 p2) (Z_to_bv 64 (S2 + o2)) x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                     x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using CTX.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm S2 n2 b2 o2 p2 k2 pad2 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      O2 N2 HP2 MI BD SB K.
    destruct SB as (B2 & L2 & R20 & R21 & R22 & D21 & D22).
    assert (K2 : S2 + n2 <= SPV - 912 \/ SPV <= S2) by (clear - D22 LO; lia).
    clear D21 D22.
    assert (MU : munch WR2 mm mm) by apply munch_refl.
    assert (WM : wmono usegs mm mm) by apply wmono_refl.
    kx_autoLx [0x23394] 80%nat
      [KZRange o2 8 (2^32); KZRange (n2 - o2) 8 (2^32); KZRange p2 0 56; KZRange n2 0 (2^32);
       KZRange S2 4096 (2^47); KZRange (S2 + n2) 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 144) 40;
       KZDisj (SPV - 144) 40 S2 n2]
      [(S2, n2); (SPV - 144, 40)].
    all: x41_ck.
    all: kx_mem.
    all: try replace (p2 mod 2 ^ 64) with p2 in * by (rewrite Z.mod_small; lia).
    all: try replace (S2 + (o2 + -1 * (p2 / 8))) with (S2 + (o2 - p2 / 8)) in * by lia.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23394) _ _ _ _) => eapply K
         end.
    all: try first [ eassumption | lia ].
  Qed.

  Lemma x41_rl2 : forall rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0,
    K4608 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb
      rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 ->
    K4448 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb
      rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0.
  Proof using CTX DJ3.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 K.
    unfold K4448. intros mm K1 c1 o1 Q1 k2 k3 k4 p2 o2 p3 o3 p4 o4 x7 x8 x9 x12 x20 x21 x22 x23 x27
      (PV & MI & OUT & DTB & NBOK & SB1 & SB2 & SB3 & SB4 & HJ & HE & HROOM & HDL & HTL & HRSV) FA BD1 BD2 BD3 BD4 RS1 DI2 DI3 DI4 O2.
    pose proof SB2 as SB2c. destruct SB2c as (B2 & L2 & R20 & R21 & R22 & D21 & D22).
    destruct DI2 as (HP2 & HO2 & [HX2 | (N2 & HP2')]); [lia|].
    eapply (x41_rl2_w mm S2 n2 b2 o2 p2 k2 pad2); try eassumption; try lia.
    intros mm' c y7 y8 y9 y22 y27 MU WM MI' BD2'.
    assert (MUF : munch WDF mm mm')
      by (eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia).
    eapply (K mm' K1 c c1 o1 Q1 (Z.land p2 7) (o2 - p2 / 8) 0 k3 k4 p3 o3 p4 o4 y7 y8 y9
              (Z_to_bv 64 (S2 + (o2 - p2 / 8))) y22 x23 y27).
    - split.
      { eapply RZ_huf_dx41f.x41p_transport.
        all: first [exact CTX | exact DJ3 | exact PV | exact MUF | exact WM | exact gp | exact F | exact fc | exact m0]. }
      split; [exact MI'|].
      split; [eapply (stk_transport_disjoint usegs _ mm mm' _ _ OUT MU WM); cbn [disjoint_from]; lia|].
      split; [eapply (bytes_at_transport usegs _ mm mm' DT dtb DTB MU); cbn [disjoint_from]; lia|].
      split; [exact NBOK|].
      split. { eapply RZ_huf_dx41f.sbuf_transport.
        all: first [exact CTX | exact DJ3 | exact SB1 | exact MUF | exact gp | exact F | exact fc | exact m0]. }
      split. { eapply RZ_huf_dx41f.sbuf_transport.
        all: first [exact CTX | exact DJ3 | exact SB2 | exact MUF | exact gp | exact F | exact fc | exact m0]. }
      split. { eapply RZ_huf_dx41f.sbuf_transport.
        all: first [exact CTX | exact DJ3 | exact SB3 | exact MUF | exact gp | exact F | exact fc | exact m0]. }
      split. { eapply RZ_huf_dx41f.sbuf_transport.
        all: first [exact CTX | exact DJ3 | exact SB4 | exact MUF | exact gp | exact F | exact fc | exact m0]. }
      repeat split; lia.
    - eapply (rw_cells_transport usegs _ mm mm' _ _ FA MU WM);
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - eapply (rw_cells_transport usegs _ mm mm' _ _ BD1 MU WM);
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - exact BD2'.
    - eapply (rw_cells_transport usegs _ mm mm' _ _ BD3 MU WM);
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - eapply (rw_cells_transport usegs _ mm mm' _ _ BD4 MU WM);
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - exact RS1.
    - unfold x41_rls, x41_hinv, RZ_huf_dx41.SINV.
      assert (LE : Z.land p2 7 = p2 mod 8)
        by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
      assert (LB : 0 <= Z.land p2 7 <= 7)
        by (rewrite LE; pose proof (Z.mod_pos_bound p2 8 ltac:(lia)); lia).
      assert (0 <= p2 / 8 <= 7) by (Z.div_mod_to_equations; lia).
      repeat split; lia.
    - exact DI3.
    - exact DI4.
  Qed.
End DX41RL2.
