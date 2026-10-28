(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost ZdCellKit KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_fkit RZ_huf_dx41r RZ_huf_dx41u RZ_huf_dx41f RZ_huf_dx41o huf411_kit_rs huf41_kit_x41ck huf413_kit_v_ok.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.BothW Require Import AZ_hufkit42e.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require ZBridge.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41V.
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
  Notation x41_einv_f := (RZ_huf_dx41r.x41_einv_f ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX).
  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Lemma x41_f0_ok : forall mm SRC n src l1 l2 l3 (b0 b1 b2 b3 : word)
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
    exact (h413v_f0_ok ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV DJ3 NBOK BITINIT SPVA DTA).
  Qed.

  Lemma x41_f0_no : forall mm SRC n src r bs
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w15 : word)
      (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 : word),
    X41PF mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    nth_error dtb 2 = Some (Z_to_bv 8 tl) -> nth_error dtb 3 = Some (Z_to_bv 8 rsv) ->
    FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 (Z_to_bv 64 SRC) (Z_to_bv 64 DT) (Z_to_bv 64 n) (Z_to_bv 64 dcap) (Z_to_bv 64 DST)
        w15 (Z_to_bv 64 (DST + dcap)) ->
    rw_cells usegs mm (SPV + -376) [CB 152 bs] ->
    LOC mm u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 -> TOP mm u14 ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    (r = 0 \/ zd_is_error r = true) -> 0 <= r < 2^64 ->
    evt usegs POST (ST 0x22250 mm x1 x5 x6 x7 (Z_to_bv 64 SRC) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                      x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm SRC n src r bs
      x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w15 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14
      PV MI OUT DTB DT2 DT3 FS AR LC TP SB SL S0 S1 SL32 DJS DKS HR HRB.
    pose proof (rsk_al_e _ _ SPVA) as SPV16. pose proof (rsk_al_e _ _ DTA) as DT4.
    assert (J : rw_cells usegs mm (SPV + -512)
                  ([C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 (Z_to_bv 64 SRC); C8 (Z_to_bv 64 DT);
                    C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 w15; C8 (Z_to_bv 64 (DST + dcap))]
                   ++ ([CB 152 bs] ++ ([C8 u0; C8 u1; C8 u2; C8 u3; C8 u4; C8 u5; C8 u6; C8 u7; C8 u8; C8 u9; C8 u10; C8 u11;
                                       C8 u12; C8 u13] ++ [C8 u14])))).
    { apply (proj2 (ZdWalkKit.rw_cells_app usegs _ (SPV + -512) _ _)); split; [exact FS|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -376) by (cbn; clear; lia) end.
      apply (proj2 (ZdWalkKit.rw_cells_app usegs _ (SPV + -376) [CB 152 bs] _)); split; [exact AR|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -224) by (cbn; clear; lia) end.
      apply (proj2 (ZdWalkKit.rw_cells_app usegs _ (SPV + -224) _ _)); split; [exact LC|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -112) by (cbn; clear; lia) end. exact TP. }
    pose proof (x41_einv_f mm _ PV MI OUT J eq_refl) as EI.
    destruct (rw_cells_forget _ _ _ _ FS) as [jA FA]. cbn [cells_size csize Nat.add] in FA.
    destruct (cb_carve usegs mm (SPV + -376) 152 bs 40 112 AR ltac:(lia) ltac:(lia) ltac:(lia)) as (k1 & k2 & k3 & B1 & B2 & _).
    change (Z.to_nat 40) with 40%nat in B1. change (Z.to_nat 112) with 112%nat in B2.
    replace (SPV + -376 + 40) with (SPV + -336) in B2 by lia.
    assert (C1 : rw_cells usegs mm (SPV + -512) ([CB 136 jA] ++ [CB 40 k1])).
    { apply (proj2 (ZdWalkKit.rw_cells_app usegs _ (SPV + -512) _ _)); split; [exact FA|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -376) by (cbn; clear; lia) end. exact B1. }
    destruct (rw_cells_forget _ _ _ _ C1) as [j1 C1']. cbn [cells_size csize Nat.add app] in C1'.
    assert (C2 : rw_cells usegs mm (SPV + -224)
                   ([C8 u0; C8 u1; C8 u2; C8 u3; C8 u4; C8 u5; C8 u6; C8 u7; C8 u8; C8 u9; C8 u10; C8 u11; C8 u12; C8 u13] ++ [C8 u14])).
    { apply (proj2 (ZdWalkKit.rw_cells_app usegs _ (SPV + -224) _ _)); split; [exact LC|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -112) by (cbn; clear; lia) end. exact TP. }
    destruct (rw_cells_forget _ _ _ _ C2) as [j2 C2']. cbn [cells_size csize Nat.add app] in C2'.
    destruct PV as (SV & STK & MUP & WMP).
    clear J C1 C2 AR LC TP B1 FA.
    destruct HR as [HR0 | HRE].
    - subst r.
      kx_auto [0x22b84; 0x23594] 20%nat [KZRange SPV 4096 (2^47)] [(SPV - 512, 136)].
      all: lazymatch goal with
           | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22b84) _ _ _ _) =>
               eapply (x41_s0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 BITINIT mm k2 SRC n src tl rsv j1 j2);
               first [ exact (conj SV (conj STK (conj B2 (conj MUP WMP)))) | exact C1' | exact C2' | eassumption | lia ]
           end.
    - assert (HERR : 2^64 - 119 <= r < 2^64) by (unfold zd_is_error, ZE_maxCode in HRE; apply Z.ltb_lt in HRE; clear - HRE HRB; lia).
      kx_auto [0x22b84; 0x23594] 20%nat [KZRange r (2^64 - 119) (2^64 - 1); KZRange SPV 4096 (2^47)] [(SPV - 512, 136)].
      all: lazymatch goal with
           | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23594) _ _ _ _) =>
               eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm r);
               [exact EI | right; split; [exact HRE | lia]]
           end.
  Qed.

End DX41V.
