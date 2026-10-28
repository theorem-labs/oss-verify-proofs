(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2 ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx2 huf411_kit_x2_l2 huf411_kit_x2_la huf411_kit_x2_lb RZ_huf_bitinit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX2E.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x1_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis X2OK : huf_x2_ok dtb tl.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 144 [] m0 huf_noQ).
  Notation DINV2 := (x2_dinv ra s0 s1 s2 s3 s4 s5 s6 s7 m0 SPV DST dcap SRC DT lo src dtb).
  Notation BDC2 := (x2_bdc SPV SRC).
  Notation PINV := (x2_pinv SRC n).
  Notation ST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -112)) gp tp x5 x6 x7 (Z_to_bv 64 dcap) x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Ltac dinv_open DI :=
    let OUT := fresh "OUT" in
    destruct DI as (OUT & FR & STK & SRCB & DTB & MU & WM & MI).
  Ltac dinv_close := unfold x2_dinv; repeat (split; [eassumption|]); eassumption.
  Ltac tp_close := lazymatch goal with |- context [Z_to_bv 64 0x20714] => kx_trap_fast | _ => idtac end.
  Ltac ext_pre := try first [exact CTX | exact X2OK].
  Ltac mclose := first [ reflexivity | lia | rewrite ?(neg_dl_sh tl rsv ltac:(lia)); lia
                       | rewrite ?Z.shiftr_div_pow2 by lia; lia ].

  (* [comment removed for export] *)
  Lemma hdr_read : forall b0 b1, nth_error dtb 0 = Some b0 -> nth_error dtb 1 = Some b1 ->
    extz false 4 (bytes_le_to_Z (firstn 4 (skipn (Z.to_nat 0) dtb))) = bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * tl + 16777216 * rsv.
  Proof.
    intros b0 b1 DT0 DT1. pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    assert (E : firstn 4 (skipn (Z.to_nat 0) dtb) = [b0; b1; Z_to_bv 8 tl; Z_to_bv 8 rsv]).
    { change (Z.to_nat 0) with 0%nat.
      destruct dtb as [|y0 [|y1 [|y2 [|y3 r]]]]; cbn in DT0, DT1, DT2, DT3; try discriminate.
      injection DT0 as ->. injection DT1 as ->. injection DT2 as ->. injection DT3 as ->. reflexivity. }
    rewrite E. unfold extz. rewrite Bytes.bytes_le_to_Z_le_val. cbn [map Bytes.le_val].
    rewrite !Z_to_bv_unsigned, !bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_small : forall mm cw bc P pad (x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word)
                     (e9 e10 e11 e12 e13 : Z),
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 1 <= bc <= 64 -> PINV P -> dcap < 8 ->
    e9 mod 2^64 = DST mod 2^64 -> e10 mod 2^64 = (DT + 4) mod 2^64 -> e11 mod 2^64 = (DST + dcap) mod 2^64 ->
    e12 mod 2^64 = 2^61 mod 2^64 -> e13 mod 2^64 = (tl + 256 * rsv) mod 2^64 ->
    evt usegs POST (ST 0x1ff64 mm x1 x5 x6 x7 (Z_to_bv 64 e9) (Z_to_bv 64 e10) (Z_to_bv 64 e11) (Z_to_bv 64 e12)
                       (Z_to_bv 64 e13) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros mm cw bc P pad x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 e9 e10 e11 e12 e13
      DI BD HN HBC INV HD H9 H10 H11 H12 H13.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. unfold x2_bdc in BD.
    rewrite (zbv_eqm _ _ H9), (zbv_eqm _ _ H10), (zbv_eqm _ _ H11), (zbv_eqm _ _ H12), (zbv_eqm _ _ H13).
    clear H9 H10 H11 H12 H13.
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); lia).
    destruct QR as (q & r & -> & HQ & HR).
    destruct INV as [-> | (O1 & O2)];
      [ kx_autoLx [0x203b4] 60%nat
          [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 1 64; KZRange n 1 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
           KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 7; KZRange (DST + dcap) 4096 (2^47);
           KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
           KZWr (SPV + -112) 40; KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
          [(SRC, n); (SPV + -112, 40)]
      | assert (O : exists off, P = SRC + off) by (exists (P - SRC); lia); destruct O as (off & ->);
        destruct (Z_lt_le_dec off 8) as [C8|C8];
        [ destruct (Z_lt_le_dec off q) as [CQ|CQ];
          [ kx_autoLx [0x203b4] 120%nat
              [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange (q - off) 1 8; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 1 64;
               KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
               KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 7; KZRange (DST + dcap) 4096 (2^47);
               KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
               KZWr (SPV + -112) 40; KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
              [(SRC, n); (SPV + -112, 40)]
          | kx_autoLx [0x203b4] 120%nat
              [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange (off - q) 0 7; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 1 64;
               KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
               KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 7; KZRange (DST + dcap) 4096 (2^47);
               KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
               KZWr (SPV + -112) 40; KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
              [(SRC, n); (SPV + -112, 40)] ]
        | kx_autoLx [0x203b4] 120%nat
            [KZRange (n - off) 8 (2^32); KZRange off 8 (2^32); KZRange (off - q) 0 (2^32); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 1 64;
             KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
             KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 7; KZRange (DST + dcap) 4096 (2^47);
             KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
             KZWr (SPV + -112) 40; KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
            [(SRC, n); (SPV + -112, 40)] ] ].
    all: tp_close.
    all: kx_mem.
    all: kx_read_ranges.
    all: eapply x2_fcc with (j := 0); ext_pre;
      [ dinv_close | unfold x2_bdc; eassumption | exact HN | lia
      | lia | intros; unfold x2_pinv; lia | lia | mclose | mclose | mclose | mclose | mclose ].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_hdr : forall mm cw bc P pad (x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word)
                   (e9 e10 e11 e12 e13 : Z),
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 1 <= bc <= 64 -> PINV P ->
    e9 mod 2^64 = DST mod 2^64 -> e10 mod 2^64 = (DT + 4) mod 2^64 -> e11 mod 2^64 = (DST + dcap) mod 2^64 ->
    e12 mod 2^64 = 2^61 mod 2^64 -> e13 mod 2^64 = (tl + 256 * rsv) mod 2^64 ->
    evt usegs POST (ST 0x1fbf8 mm x1 x5 x6 x7 (Z_to_bv 64 e9) (Z_to_bv 64 e10) (Z_to_bv 64 e11) (Z_to_bv 64 e12)
                       (Z_to_bv 64 e13) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros mm cw bc P pad x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 e9 e10 e11 e12 e13
      DI BD HN HBC INV H9 H10 H11 H12 H13.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. unfold x2_bdc in BD.
    rewrite (zbv_eqm _ _ H9), (zbv_eqm _ _ H10), (zbv_eqm _ _ H11), (zbv_eqm _ _ H12), (zbv_eqm _ _ H13).
    clear H9 H10 H11 H12 H13.
    assert (PR : 4096 <= P < 2^47) by (unfold x2_pinv in INV; lia).
    kx_autoLx [0x1fc48; 0x20034] 40%nat
      [KZRange bc 1 64; KZRange n 1 (2^32); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange (DST + dcap) 4096 (2^47);
       KZRange SPV 4096 (2^47); KZRange SRC 4096 (2^47); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange P 4096 (2^47)]
      [(SPV + -112, 40)].
    all: tp_close.
    all: kx_mem.
    all: kx_read_ranges.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1fc48) _ _ _ _) =>
             eapply x2_la_entry; ext_pre;
             [ dinv_close | unfold x2_bdc; eassumption | exact HN
             | first [reflexivity | apply definitions.Z_to_bv_bv_unsigned] | lia | exact INV
             | mclose | mclose | mclose | mclose | mclose | mclose | mclose | mclose
             | mclose | mclose | mclose | mclose | mclose | mclose ]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20034) _ _ _ _) =>
             eapply x2_lb_entry; ext_pre;
             [ dinv_close | unfold x2_bdc; eassumption | exact HN
             | first [reflexivity | apply definitions.Z_to_bv_bv_unsigned] | lia | exact INV
             | mclose | mclose | mclose | mclose | mclose | mclose | mclose | mclose ]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_main : forall mm cw bc pad P (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 1 <= bc <= 64 -> PINV P ->
    evt usegs POST (ST 0x1fba8 mm x1 x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 DT) x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros mm cw bc pad P x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 DI BD HN HBC INV.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA.
    pose proof DI as DI'. dinv_open DI'.
    destruct (Z.eq_dec dcap 0) as [DC0|DC1]; [| destruct (Z_lt_le_dec dcap 8) as [D8|D8]].
    1: kx_autoLx [0x1ff64; 0x1fbf8] 40%nat
         [KZRange bc 1 64; KZRange n 1 (2^32); KZRange dcap 0 0; KZRange DST 4096 (2^47); KZRange (DST + dcap) 4096 (2^47);
          KZRange SPV 4096 (2^47); KZRange SRC 4096 (2^47); KZRange DT 4096 (2^47); KZAlign DT 4; KZRange tl 1 12; KZRange rsv 0 255]
         [(DT, 16388)].
    2: kx_autoLx [0x1ff64; 0x1fbf8] 40%nat
         [KZRange bc 1 64; KZRange n 1 (2^32); KZRange dcap 1 7; KZRange DST 4096 (2^47); KZRange (DST + dcap) 4096 (2^47);
          KZRange SPV 4096 (2^47); KZRange SRC 4096 (2^47); KZRange DT 4096 (2^47); KZAlign DT 4; KZRange tl 1 12; KZRange rsv 0 255]
         [(DT, 16388)].
    3: kx_autoLx [0x1ff64; 0x1fbf8] 40%nat
         [KZRange bc 1 64; KZRange n 1 (2^32); KZRange dcap 8 (2^32); KZRange DST 4096 (2^47); KZRange (DST + dcap) 4096 (2^47);
          KZRange SPV 4096 (2^47); KZRange SRC 4096 (2^47); KZRange DT 4096 (2^47); KZAlign DT 4; KZRange tl 1 12; KZRange rsv 0 255]
         [(DT, 16388)].
    all: tp_close.
    all: try clear DTA.
    all: lazymatch goal with KXA : atoms_ok ?zs _ |- _ => let nz := kx_len zs in kx_read_eq nz RD end.
    all: destruct (nth_error dtb 0) as [b0|] eqn:DT0; [| apply nth_error_None in DT0; exfalso; lia].
    all: destruct (nth_error dtb 1) as [b1|] eqn:DT1; [| apply nth_error_None in DT1; exfalso; lia].
    all: rewrite (rdval_bytes_at usegs _ DT dtb 0 4 false DTB ltac:(lia) ltac:(change (Z.to_nat 0) with 0%nat; lia)),
                 (hdr_read b0 b1 DT0 DT1) in RD.
    all: pose proof (bv_unsigned_in_range 8 b0) as RB0; pose proof (bv_unsigned_in_range 8 b1) as RB1;
         unfold bv_modulus in RB0, RB1; change (2 ^ Z.of_N 8) with 256 in RB0, RB1.
    all: lazymatch type of RD with
         | ?a = Z_to_bv 64 ?v =>
             assert (HX : bv_unsigned a = v)
               by (rewrite RD, Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia);
             rewrite ?HX; rewrite ?RD
         end.
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ff64) _ _ _ _) =>
             eapply x2_small;
             [ dinv_close | unfold x2_bdc; eassumption | exact HN | lia | exact INV | lia
             | mclose | mclose | mclose | mclose | mclose ]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1fbf8) _ _ _ _) =>
             eapply x2_hdr;
             [ dinv_close | unfold x2_bdc; eassumption | exact HN | lia | exact INV
             | mclose | mclose | mclose | mclose | mclose ]
         end.
  Qed.

  Lemma x2_cerr : forall mm r bs (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
    DINV2 mm -> rw_cells usegs mm (SPV + -112) [CB 40 bs] -> zd_is_error r = true -> r < 2^64 ->
    evt usegs POST (ST 0x1fba8 mm x1 x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 DT) x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros mm r bs x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 DI CS HER HRB.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'.
    pose proof HER as HER'. unfold zd_is_error, ZE_maxCode in HER'. apply Z.ltb_lt in HER'.
    kx_autoLx [0x206e8] 10%nat [KZRange r (2^64 - 119) (2^64 - 1); KZRange SPV 4096 (2^47)] (@nil (Z * Z)).
    all: kx_mem.
    all: eapply x2_err; ext_pre;
      [ dinv_close | exact CS | reflexivity | right; rewrite bvu_mod, Z.mod_small by lia; exact HER ].
  Qed.

  Lemma x2_call : forall mm junk (y1 ysp y8 y9 y10 y11 y12 y18 : Z) (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    DINV2 mm -> rw_cells usegs mm (SPV + -112) [CB 40 junk] ->
    y1 mod 2^64 = 0x1fba8 mod 2^64 -> ysp mod 2^64 = (SPV + -112) mod 2^64 -> y8 mod 2^64 = dcap mod 2^64 ->
    y9 mod 2^64 = DST mod 2^64 -> y10 mod 2^64 = (SPV + -112) mod 2^64 -> y11 mod 2^64 = SRC mod 2^64 ->
    y12 mod 2^64 = n mod 2^64 -> y18 mod 2^64 = DT mod 2^64 ->
    evt usegs POST
      (MS (mkR (Z_to_bv 64 y1) (Z_to_bv 64 ysp) gp tp x5 x6 x7 (Z_to_bv 64 y8) (Z_to_bv 64 y9) (Z_to_bv 64 y10) (Z_to_bv 64 y11)
               (Z_to_bv 64 y12) x13 x14 x15 x16 x17 (Z_to_bv 64 y18) s3 s4 s5 s6 s7 s8 s9 s10 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x25a0c) fc None mm (seg_rom usegs)).
  Proof.
    intros mm junk y1 ysp y8 y9 y10 y11 y12 y18 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31
      DI BJ H1 HSP H8 H9 H10 H11 H12 H18.
    pose proof CTX as CTX'. x1_ctx_open CTX'.
    assert (BD8 : (SPV + -112) mod 8 = 0) by (clear - SPA; lia). clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'.
    rewrite (zbv_eqm _ _ H1), (zbv_eqm _ _ HSP), (zbv_eqm _ _ H8), (zbv_eqm _ _ H9), (zbv_eqm _ _ H10), (zbv_eqm _ _ H11),
            (zbv_eqm _ _ H12), (zbv_eqm _ _ H18).
    clear H1 HSP H8 H9 H10 H11 H12 H18.
    eapply evt_cut.
    { eapply (bit_init_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm (SPV + -112) SRC n src junk);
        first [exact BD8 | eassumption | clear BD8; lia]. }
    unfold bit_init_post. clear BD8. post_call usegs mm.
    try rewrite (ret_pc_even 0x1fba8) by lia.
    lazymatch goal with
    | H : (_ = n /\ _) \/ _ |- _ => destruct H as [(HR & HN1 & cont & bc & pad & HB1 & HB2 & BDCH) | (HER & HRB & bs & BDCH)]
    end.
    - lazymatch type of HR with ?r = n => subst r end.
      unfold bitd_cells in BDCH.
      eapply x2_main; [dinv_close | unfold x2_bdc; exact BDCH | exact HN1 | lia | ].
      unfold x2_pinv, bitd_ptr. destruct (8 <=? n) eqn:E8; [apply Z.leb_le in E8 | apply Z.leb_gt in E8]; lia.
    - eapply x2_cerr; [dinv_close | exact BDCH | exact HER | exact HRB].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_entry : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv usegs m0 -> stk usegs m0 lo SPV -> stk usegs m0 DST (DST + dcap) -> bytes_at usegs m0 SRC src -> bytes_at usegs m0 DT dtb ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1fb64) fc None m0 (seg_rom usegs)).
  Proof.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 MI STK OUT SRCB DTB.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    assert (MU : munch [(DST, DST + dcap); (SPV - 144, SPV)] m0 m0) by apply munch_refl.
    assert (WM : wmono usegs m0 m0) by apply wmono_refl.
    carve_frame 112%nat STK.
    destruct (cb_carve usegs m0 (SPV + -112) 112 junk 40 72 FR ltac:(lia) ltac:(lia) ltac:(lia)) as (j1 & j2 & j3 & C1 & C2 & C3).
    change (Z.to_nat 40) with 40%nat in C1. change (Z.to_nat 72) with 72%nat in C2.
    replace (SPV + -112 + 40) with (SPV + -72) in C2 by lia.
    assert (FRW : wr_at usegs m0 (SPV + -112) 112) by kx_wr_at.
    clear FR C3.
    kx_autoLx [0x25a0c] 40%nat
      [KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange (DST + dcap) 4096 (2^47); KZRange SRC 4096 (2^47);
       KZRange n 0 (2^32); KZRange DT 4096 (2^47); KZWr (SPV + -112) 112; KZDisj (SPV + -112) 112 DT 16388; KZDisj (SPV + -112) 112 SRC n]
      (@nil (Z * Z)).
    all: tp_close.
    all: kx_mem.
    all: eapply x2_call; [dinv_close | exact C1 | first [reflexivity | lia] | first [reflexivity | lia] | first [reflexivity | lia]
                         | first [reflexivity | lia] | first [reflexivity | lia] | first [reflexivity | lia] | first [reflexivity | lia]
                         | first [reflexivity | lia]].
  Qed.
End DX2E.

(* [comment removed for export] *)
Theorem huf_1x2_proof : huf_1x2_stmt.
Proof.
  unfold huf_1x2_stmt, huf_int_stmt_at, PHUF_1X2, HUF_1X_STACK.
  intros until dtb.
  intros (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SL & S0 & S1 & S2 & OS1 & OS2 & DJ1 & SP16)
         (DTB & DL & T0 & T1 & OS3 & DJ2 & DT4) DT2 TL X2 _.
  unfold HUF_DTABLE_BYTES in *.
  destruct (nth_error dtb 3) as [b3|] eqn:DT3;
    [| apply nth_error_None in DT3; exfalso; lia].
  assert (CTX : x1_ctx SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb).
  { pose proof (bv_unsigned_in_range 8 b3) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
    assert (EB : Z_to_bv 8 (bv_unsigned b3) = b3)
      by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
    unfold x1_ctx. rewrite EB. repeat split; try assumption; lia. }
  pose proof (X2 eq_refl) as X2OK.
  eapply x2_entry; first [exact CTX | exact X2OK | eassumption].
Qed.
