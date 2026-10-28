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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_fkit2 RZ_huf_dx41f RZ_huf_dx41r RZ_huf_dx42_5 RZ_huf_dx42_14 RZ_huf_dx42_23 huf411_kit_rs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.BothW Require Import AZ_hufkit42e.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require ZBridge.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_24.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis NBOK : huf_nb_ok true dtb tl.
  Hypothesis BITINIT : bit_init_stmt.
  Hypothesis SPVA : rsk_al SPV 16.
  Hypothesis DTA : rsk_al DT 4.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11;
                                     C8 w12; C8 w13; C8 w14; C8 w15]).
  Notation LOC mm e0 e1 e2 e3 p0 p1 p2 p3 i0 i1 i2 i3 c0 c1 c2 c3 :=
    (rw_cells usegs mm (SPV + -232) [C8 e0; C8 e1; C8 e2; C8 e3; C8 p0; C8 p1; C8 p2; C8 p3; C8 i0; C8 i1; C8 i2; C8 i3;
                                     C8 c0; C8 c1; C8 c2; C8 c3]).
  Notation X41PF := (RZ_huf_dx41r.X41PF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation X42S := (RZ_huf_dx42_0.X42S ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x41_einv_f := (RZ_huf_dx41r.x41_einv_f ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX).
  Notation x42_retf := (RZ_huf_dx42_5.x42_retf ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Ltac f0_ck := lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22180) _ _ _ _) => kx_trap_fast
    | _ => idtac end.

  Lemma x42_f0_ok : forall mm SRC n src l1 l2 l3 (b0 b1 b2 b3 : word)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w8 w9 w10 w11 w12 w13 w14 : word)
      (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 : word),
    tl = 11 ->
    X41PF mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRS mm w0 w1 (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 DT) (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + dcap))
        w8 w9 w10 w11 w12 w13 w14 (Z_to_bv 64 (DT + 4)) ->
    rw_cells usegs mm (SPV + -384) (fast_args_cells DST dcap SRC n DT l1 l2 l3 b0 b1 b2 b3) ->
    LOC mm u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n -> DST + 3 * ((dcap + 3) / 4) < DST + dcap ->
    bv_unsigned b0 mod 512 <> 0 -> bv_unsigned b1 mod 512 <> 0 -> bv_unsigned b2 mod 512 <> 0 -> bv_unsigned b3 mod 512 <> 0 ->
    evt usegs POST (ST 0x20e64 mm x1 x5 x6 x7 (Z_to_bv 64 DT) (Z_to_bv 64 n) (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17
                      (Z_to_bv 64 SRC) (Z_to_bv 64 dcap) (Z_to_bv 64 DST) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm SRC n src l1 l2 l3 b0 b1 b2 b3
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w0 w1 w8 w9 w10 w11 w12 w13 w14 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15
      TL11 PV MI OUT DTB FS AR LC SB SL S0 S1 SL32 DJS DKS HL1 HL2 HL3 HLN HQ3 HM0 HM1 HM2 HM3.
    assert (HB0 : LBW 8 b0) by exact (lb_of_mod512 _ HM0). assert (HB1 : LBW 8 b1) by exact (lb_of_mod512 _ HM1).
    assert (HB2 : LBW 8 b2) by exact (lb_of_mod512 _ HM2). assert (HB3 : LBW 8 b3) by exact (lb_of_mod512 _ HM3).
    clear HM0 HM1 HM2 HM3.
    unfold fast_args_cells in AR. cbv zeta in AR.
    assert (HDC : 1 <= dcap) by (Z.div_mod_to_equations; lia).
    destruct PV as (SV & STK & MUP & WMP).
    kx_auto [0x20fe4; 0x22180] 120%nat
      [KZImg 0x10000 0x14000; KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47);
       KZRange SRC 4096 (2^47); KZWr (SPV - 512) 128; KZWr (SPV - 232) 128]
      [(SPV - 512, 128); (SPV - 384, 152); (SPV - 232, 128)].
    all: f0_ck.
    all: kx_ev_ranges; kx_mem.
    set (q := (dcap + 3) / 4) in *.
    replace (dcap + DST) with (DST + dcap) in FS, LC by lia.
    rewrite (ZBridge.Z_to_bv_eqm 18446744073709551591 (-25)) by reflexivity.
    rewrite (ZBridge.Z_to_bv_eqm 18446744073709551600 (-16)) by reflexivity.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
        let HF := fresh "HF" in
        pose proof (RZ_huf_dx42_23.x42_fo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK
                      TL11 DJ3 NBOK DTA (Z.to_nat (dcap + 1)) m2 SRC n src q l1 l2 l3
                      (l1 + -2) ((l1 + l2) + -2) ((l1 + (l2 + l3)) + -2) (n + -8) 0 q (2 * q) (3 * q)) as HF;
        replace (SRC + (l1 + -2)) with (SRC + l1 + -2) in HF by lia;
        replace (SRC + (l1 + l2 + -2)) with (SRC + (l1 + l2) + -2) in HF by lia;
        replace (SRC + (l1 + (l2 + l3) + -2)) with (SRC + (l1 + (l2 + l3)) + -2) in HF by lia;
        replace (SRC + (n + -8)) with (n + SRC + -8) in HF by lia;
        replace (DST + 0) with DST in HF by lia;
        eapply HF
    end.
    all: first [ exact (conj SV (conj STK (conj MUP WMP))) | eassumption | subst q; lia ].
  Qed.

  Lemma x42_f0_no : forall mm SRC n src r bs
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : word)
      (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 : word),
    X41PF mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    nth_error dtb 2 = Some (Z_to_bv 8 tl) -> nth_error dtb 3 = Some (Z_to_bv 8 rsv) ->
    FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ->
    rw_cells usegs mm (SPV + -384) [CB 152 bs] ->
    LOC mm u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    (r = 0 \/ zd_is_error r = true) -> 0 <= r < 2^64 ->
    evt usegs POST (ST 0x20e64 mm x1 x5 x6 x7 (Z_to_bv 64 DT) (Z_to_bv 64 n) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                      (Z_to_bv 64 SRC) (Z_to_bv 64 dcap) (Z_to_bv 64 DST) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm SRC n src r bs
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15
      PV MI OUT DTB DT2 DT3 FS AR LC SB SL S0 S1 SL32 DJS DKS HR HRB.
    assert (J : rw_cells usegs mm (SPV + -512)
                  ([C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13; C8 w14; C8 w15]
                   ++ ([CB 152 bs] ++ [C8 u0; C8 u1; C8 u2; C8 u3; C8 u4; C8 u5; C8 u6; C8 u7; C8 u8; C8 u9; C8 u10; C8 u11;
                                      C8 u12; C8 u13; C8 u14; C8 u15]))).
    { apply (proj2 (ZdWalkKit.rw_cells_app usegs _ (SPV + -512) _ _)); split; [exact FS|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -384) by (cbn; clear; lia) end.
      apply (proj2 (ZdWalkKit.rw_cells_app usegs _ (SPV + -384) [CB 152 bs] _)); split; [exact AR|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -232) by (cbn; clear; lia) end. exact LC. }
    pose proof (x41_einv_f mm _ PV MI OUT J eq_refl) as EI.
    destruct (rw_cells_forget _ _ _ _ J) as [rest JR]. cbn [cells_size csize Nat.add app] in JR.
    destruct PV as (SV & STK & MUP & WMP).
    assert (XS : X42S mm rest) by exact (conj SV (conj JR (conj STK (conj MUP WMP)))).
    clear J JR FS AR LC SV STK MUP WMP.
    destruct HR as [HR0 | HRE].
    - subst r.
      kx_auto [0x22084; 0x22098] 20%nat [KZRange SPV 4096 (2^47)] [].
      all: lazymatch goal with
           | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22084) _ _ _ _) =>
               eapply (RZ_huf_dx42_14.x42_s0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV
                         X2OK DJ3 NBOK BITINIT SPVA DTA mm rest SRC n src);
               first [ exact XS | eassumption | lia ]
           end.
    - assert (HERR : 2^64 - 119 <= r < 2^64) by (unfold zd_is_error, ZE_maxCode in HRE; apply Z.ltb_lt in HRE; clear - HRE HRB; lia).
      kx_auto [0x22084; 0x22098] 20%nat [KZRange r (2^64 - 119) (2^64 - 1); KZRange SPV 4096 (2^47)] [].
      all: lazymatch goal with
           | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22098) _ _ _ _) =>
               eapply (x42_retf mm r); [exact EI | right; split; [exact HRE | lia]]
           end.
  Qed.

End DX42_24.
