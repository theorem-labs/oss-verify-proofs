(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost ZdCellKit KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_fkit RZ_huf_dx41r RZ_huf_dx41u huf411_kit_rs huf41_kit_x41ck.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.BothW Require Import AZ_hufkit42e.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require ZBridge.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section H413V.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis NBOK : huf_nb_ok false dtb tl.
  Hypothesis BITINIT : bit_init_stmt.
  Hypothesis SPVA : rsk_al SPV 16.
  Hypothesis DTA : rsk_al DT 4.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11;
                                     C8 w12; C8 w13; C8 w14; C8 w15; C8 w16]).
  Notation LOC mm p0 p1 p2 p3 g0 i0 i1 i2 i3 g1 c0 c1 c2 c3 :=
    (rw_cells usegs mm (SPV + -224) [C8 p0; C8 p1; C8 p2; C8 p3; C8 g0; C8 i0; C8 i1; C8 i2; C8 i3; C8 g1; C8 c0; C8 c1; C8 c2; C8 c3]).
  Notation TOP mm g2 := (rw_cells usegs mm (SPV + -112) [C8 g2]).
  Notation X41PF := (RZ_huf_dx41r.X41PF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Lemma h413v_f0_ok : forall mm SRC n src l1 l2 l3 (b0 b1 b2 b3 : word)
      (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w15 : word)
      (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 : word),
    tl = 11 ->
    X41PF mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 (Z_to_bv 64 SRC) (Z_to_bv 64 DT) (Z_to_bv 64 n) (Z_to_bv 64 dcap) (Z_to_bv 64 DST)
        w15 (Z_to_bv 64 (DST + dcap)) ->
    rw_cells usegs mm (SPV + -376) (fast_args_cells DST dcap SRC n DT l1 l2 l3 b0 b1 b2 b3) ->
    LOC mm u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 -> TOP mm u14 ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n -> DST + 3 * ((dcap + 3) / 4) < DST + dcap ->
    bv_unsigned b0 mod 512 <> 0 -> bv_unsigned b1 mod 512 <> 0 -> bv_unsigned b2 mod 512 <> 0 -> bv_unsigned b3 mod 512 <> 0 ->
    evt usegs POST (ST 0x22250 mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (DT + 4))
                      x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm SRC n src l1 l2 l3 b0 b1 b2 b3
      x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w15 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14
      TL11 PV MI OUT DTB FS AR LC TP SB SL S0 S1 SL32 DJS DKS HL1 HL2 HL3 HLN HQ3 HM0 HM1 HM2 HM3.
    assert (HB0 : LBW 8 b0) by exact (lb_of_mod512 _ HM0). assert (HB1 : LBW 8 b1) by exact (lb_of_mod512 _ HM1).
    assert (HB2 : LBW 8 b2) by exact (lb_of_mod512 _ HM2). assert (HB3 : LBW 8 b3) by exact (lb_of_mod512 _ HM3).
    clear HM0 HM1 HM2 HM3.
    unfold fast_args_cells in AR. cbv zeta in AR.
    assert (HDC : 1 <= dcap) by (Z.div_mod_to_equations; lia).
    destruct PV as (SV & STK & MUP & WMP).
    kx_auto [0x253c0; 0x23618] 160%nat
      [KZImg 0x10000 0x14000; KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47);
       KZRange SRC 4096 (2^47); KZWr (SPV - 512) 136; KZWr (SPV - 224) 112]
      [(SPV - 512, 136); (SPV - 376, 152); (SPV - 224, 112); (SPV - 112, 8)].
    all: x41_ck.
    all: kx_ev_ranges; kx_mem.
    rewrite ?(Z.add_comm dcap DST) in FS.
    set (q := (dcap + 3) / 4) in *.
    rewrite (ZBridge.Z_to_bv_eqm 18446744073709551600 (-16)) by reflexivity.
    rewrite (ZBridge.Z_to_bv_eqm 18446744073709551591 (-25)) by reflexivity.
    rewrite (ZBridge.Z_to_bv_eqm 18446744073709551599 (-17)) by reflexivity.
    rewrite (ZBridge.Z_to_bv_eqm 18446744073709551592 (-24)) by reflexivity.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
        let HF := fresh "HF" in
        pose proof (RZ_huf_dx41u.x41_fo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl
                      TL11 NBOK DJ3 DTA (Z.to_nat (dcap + 1)) m2 SRC n src l1 l2 l3
                      (l1 + -2) ((l1 + l2) + -2) ((l1 + (l2 + l3)) + -2) (n + -8) 0 q (2 * q) (3 * q)) as HF;
        unfold HUF_CTZ_TBL in HF;
        replace (SRC + (l1 + -2)) with (SRC + l1 + -2) in HF by lia;
        replace (SRC + (l1 + l2 + -2)) with (SRC + (l1 + l2) + -2) in HF by lia;
        replace (SRC + (l1 + (l2 + l3) + -2)) with (SRC + (l1 + (l2 + l3)) + -2) in HF by lia;
        replace (SRC + (n + -8)) with (SRC + n + -8) in HF by lia;
        replace (DST + 0) with DST in HF by lia;
        eapply HF
    end.
    all: first [ exact (conj SV (conj STK (conj MUP WMP))) | eassumption | subst q; lia ].
  Qed.

End H413V.
