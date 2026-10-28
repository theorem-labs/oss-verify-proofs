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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_bitinit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX1E.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x1_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 144 [] m0 huf_noQ).
  Notation DINVc := (DINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 SPV DST dcap SRC DT lo src dtb).
  Notation BDCc := (BDC SPV SRC).
  Notation LINVc := (LINV SRC n).
  Notation STpc pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -144)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * rsv)) x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Ltac dinv_open DI :=
    let OUT := fresh "OUT" in
    destruct DI as (OUT & FR & STK & SRCB & DTB & MU & WM & MI).
  Ltac dinv_close := unfold DINV; repeat (split; [eassumption|]); eassumption.
  Ltac trap_close := lazymatch goal with |- context [Z_to_bv 64 0x20d74] => kx_trap_fast | _ => idtac end.

  Lemma x1_loop_entry : forall mm cw cwr bc bcr bcs P Pr pad (x1 x9 x23 x24 x25 x26 : word)
                          (e5 e6 e7 e12 e13 e14 e15 e16 e17 e28 e29 e30 e31 : Z),
    DINVc mm -> BDCc mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> cwr = cw ->
    bcr mod 2^64 = bc mod 2^64 -> bcs mod 2^64 = bc mod 2^64 -> Pr mod 2^64 = P mod 2^64 -> LINVc P bc ->
    e5 mod 2^64 = 65 mod 2^64 -> e6 mod 2^64 = 4611686018427387904 mod 2^64 -> e7 mod 2^64 = (64 - tl) mod 2^64 ->
    e12 mod 2^64 = DST mod 2^64 -> e13 mod 2^64 = SRC mod 2^64 -> e14 mod 2^64 = (SRC + 8) mod 2^64 ->
    e15 mod 2^64 = (dcap + DST + -3) mod 2^64 -> e16 mod 2^64 = (-1 * DT + -5) mod 2^64 -> e17 mod 2^64 = (DST + 3) mod 2^64 ->
    e28 mod 2^64 = 70160 mod 2^64 -> e29 mod 2^64 = 3 mod 2^64 -> e30 mod 2^64 = 2 mod 2^64 ->
    e31 mod 2^64 = 18446744073709551615 mod 2^64 ->
    evt usegs POST (STpc 0x208f8 mm x1 (Z_to_bv 64 e5) (Z_to_bv 64 e6) (Z_to_bv 64 e7) (Z_to_bv 64 dcap) x9 (Z_to_bv 64 bcr) (Z_to_bv 64 bcs)
                         (Z_to_bv 64 e12) (Z_to_bv 64 e13) (Z_to_bv 64 e14) (Z_to_bv 64 e15) (Z_to_bv 64 e16) (Z_to_bv 64 e17)
                         cwr (Z_to_bv 64 Pr) x23 x24 x25 x26 (Z_to_bv 64 e28) (Z_to_bv 64 e29) (Z_to_bv 64 e30) (Z_to_bv 64 e31)).
  Proof.
    intros mm cw cwr bc bcr bcs P Pr pad x1 x9 x23 x24 x25 x26 e5 e6 e7 e12 e13 e14 e15 e16 e17 e28 e29 e30 e31
      DI BD HN HCW HBR HBS HPR INV H5 H6 H7 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA. subst cwr.
    rewrite (zbv_eqm _ _ H5), (zbv_eqm _ _ H6), (zbv_eqm _ _ H7), (zbv_eqm _ _ H13), (zbv_eqm _ _ H14), (zbv_eqm _ _ H15),
            (zbv_eqm _ _ H16), (zbv_eqm _ _ H28), (zbv_eqm _ _ H29), (zbv_eqm _ _ H30), (zbv_eqm _ _ H31).
    clear H5 H6 H7 H13 H14 H15 H16 H28 H29 H30 H31.
    pose proof (x1_loop ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX) as LOOP.
    eapply (LOOP (Z.to_nat dcap) mm 0 e12 e17 P Pr bc bcr bcs cw pad x1 x9 x23 x24 x25 x26);
      first [exact DI | exact BD | exact INV | exact HN | exact HBR | exact HBS | exact HPR
            | rewrite Z.add_0_r; first [exact H12 | exact H17] | clear - R1; lia].
  Qed.

  Lemma x1_small : forall mm cw bc bcr P pad (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (e9 : Z),
    DINVc mm -> BDCc mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 0 <= dcap < 4 ->
    e9 mod 2^64 = DST mod 2^64 -> bcr mod 2^64 = bc mod 2^64 -> LINVc P bc ->
    evt usegs POST (STpc 0x20b80 mm x1 x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 e9) (Z_to_bv 64 bcr) x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x23 x24 x25 x26 x28 x29 x30 x31).
  Proof.
    intros mm cw bc bcr P pad x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 e9
      DI BD HN HD H9 HBR INV.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. unfold BDC in BD.
    rewrite (zbv_eqm _ _ H9), (zbv_eqm _ _ HBR).
    pose proof (x1_tset ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX) as TSET.
    pose proof (x1_tail ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX) as TAIL.
    pose proof (x1_end ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX) as XEND.
    destruct INV as (HBC & INV).
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); lia).
    destruct QR as (q & r & -> & HQ & HR).
    destruct INV as [-> | (O1 & O2)];
      [ destruct (Z.eq_dec dcap 0) as [D0|D1];
        [ kx_autoLx [0x20c80; 0x20ca4; 0x20cfc] 40%nat
            [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
             KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 0; KZRange (DST + dcap) 4096 (2^47);
             KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
             KZWr (SPV + -136) 40; KZDisj (SPV + -136) 40 SRC n; KZDisj (SPV + -136) 40 DT 16388]
            [(SRC, n); (SPV + -136, 40)]
        | kx_autoLx [0x20c80; 0x20ca4; 0x20cfc] 40%nat
            [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
             KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 1 3; KZRange (DST + dcap) 4096 (2^47);
             KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
             KZWr (SPV + -136) 40; KZDisj (SPV + -136) 40 SRC n; KZDisj (SPV + -136) 40 DT 16388]
            [(SRC, n); (SPV + -136, 40)] ]
      | assert (O : exists off, P = SRC + off) by (exists (P - SRC); lia); destruct O as (off & ->);
        destruct (Z_lt_le_dec off 8) as [C8|C8];
        [ destruct (Z_lt_le_dec off q) as [CQ|CQ];
          [ kx_autoLx [0x20c80; 0x20ca4; 0x20cfc] 120%nat
              [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange (q - off) 1 8; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
               KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
               KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 3; KZRange (DST + dcap) 4096 (2^47);
               KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
               KZWr (SPV + -136) 40; KZDisj (SPV + -136) 40 SRC n; KZDisj (SPV + -136) 40 DT 16388]
              [(SRC, n); (SPV + -136, 40)]
          | kx_autoLx [0x20c80; 0x20ca4; 0x20cfc] 120%nat
              [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange (off - q) 0 7; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
               KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
               KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 3; KZRange (DST + dcap) 4096 (2^47);
               KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
               KZWr (SPV + -136) 40; KZDisj (SPV + -136) 40 SRC n; KZDisj (SPV + -136) 40 DT 16388]
              [(SRC, n); (SPV + -136, 40)] ]
        | kx_autoLx [0x20c80; 0x20ca4; 0x20cfc] 120%nat
            [KZRange (n - off) 8 (2^32); KZRange off 8 (2^32); KZRange (off - q) 0 (2^32); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
             KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
             KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 3; KZRange (DST + dcap) 4096 (2^47);
             KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
             KZWr (SPV + -136) 40; KZDisj (SPV + -136) 40 SRC n; KZDisj (SPV + -136) 40 DT 16388]
            [(SRC, n); (SPV + -136, 40)] ] ].
    all: trap_close.
    all: kx_mem.
    all: kx_read_ranges.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20c80) _ _ _ _) =>
             eapply (TSET _ 0); [dinv_close | unfold BDC; eassumption | lia | lia | lia]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20ca4) _ _ _ _) =>
             eapply (TAIL (Z.to_nat dcap) _ 0); [dinv_close | unfold BDC; eassumption | lia | lia | lia | lia | lia | | lia | lia | lia];
             rewrite ?(neg_dl_sh tl rsv TL); lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20cfc) _ _ _ _) =>
             eapply XEND; [dinv_close | unfold BDC; eassumption]
         end.
  Qed.

  Lemma x1_cerr : forall mm r bs (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    DINVc mm -> rw_cells usegs mm (SPV + -136) [CB 40 bs] -> zd_is_error r = true -> r < 2^64 ->
    evt usegs POST (STpc 0x20890 mm x1 x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x23 x24 x25 x26 x28 x29 x30 x31).
  Proof.
    intros mm r bs x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 DI CS HER HRB.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'.
    pose proof (x1_err ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX) as XERR.
    pose proof HER as HER'. unfold zd_is_error, ZE_maxCode in HER'. apply Z.ltb_lt in HER'.
    kx_autoLx [0x20d1c] 10%nat [KZRange r (2^64 - 119) (2^64 - 1); KZRange SPV 4096 (2^47)] (@nil (Z * Z)).
    all: kx_mem.
    all: eapply XERR; [dinv_close | exact CS | reflexivity | right; rewrite bvu_mod, Z.mod_small by lia; exact HER].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_main : forall mm cw bc pad P (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    DINVc mm -> BDCc mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 1 <= bc <= 64 -> LINVc P bc ->
    evt usegs POST (STpc 0x20890 mm x1 x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17
                         x21 x22 x23 x24 x25 x26 x28 x29 x30 x31).
  Proof.
    intros mm cw bc pad P x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 DI BD HN HBC INV.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. unfold BDC in BD.
    destruct (Z_lt_le_dec dcap 4) as [D4|D4];
      [ kx_autoLx [0x208f8; 0x20b80] 40%nat
          [KZRange bc 1 64; KZRange n 1 (2^32); KZRange dcap 0 3; KZRange DST 4096 (2^47); KZRange (DST + dcap) 4096 (2^47);
           KZRange SPV 4096 (2^47); KZRange SRC 4096 (2^47); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
           KZWr (SPV + -136) 40]
          [(SPV + -136, 40)]
      | kx_autoLx [0x208f8; 0x20b80] 40%nat
          [KZRange bc 1 64; KZRange n 1 (2^32); KZRange dcap 4 (2^32); KZRange DST 4096 (2^47); KZRange (DST + dcap) 4096 (2^47);
           KZRange SPV 4096 (2^47); KZRange SRC 4096 (2^47); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
           KZWr (SPV + -136) 40]
          [(SPV + -136, 40)] ].
    all: trap_close.
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20b80) _ _ _ _) =>
             eapply x1_small; [dinv_close | unfold BDC; eassumption | lia | lia | first [reflexivity | lia] | first [reflexivity | lia] | exact INV]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x208f8) _ _ _ _) =>
             eapply x1_loop_entry;
               [dinv_close | unfold BDC; eassumption | lia | first [reflexivity | apply definitions.Z_to_bv_bv_unsigned]
               | first [reflexivity | lia] | first [reflexivity | lia] | first [reflexivity | lia] | exact INV
               | first [reflexivity | lia] | first [reflexivity | lia] | rewrite ?(neg_dl_sh tl rsv TL); first [reflexivity | lia]
               | first [reflexivity | lia] | first [reflexivity | lia] | first [reflexivity | lia] | first [reflexivity | lia]
               | first [reflexivity | lia] | first [reflexivity | lia] | first [reflexivity | lia] | first [reflexivity | lia]
               | first [reflexivity | lia] | first [reflexivity | lia]]
         end.
  Qed.

  Lemma x1_call : forall mm junk (y1 ysp y8 y9 y10 y11 y12 y18 y19 y20 : Z) (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    DINVc mm -> rw_cells usegs mm (SPV + -136) [CB 40 junk] ->
    y1 mod 2^64 = 0x20890 mod 2^64 -> ysp mod 2^64 = (SPV + -144) mod 2^64 -> y8 mod 2^64 = dcap mod 2^64 ->
    y9 mod 2^64 = DST mod 2^64 -> y10 mod 2^64 = (SPV + -136) mod 2^64 -> y11 mod 2^64 = SRC mod 2^64 ->
    y12 mod 2^64 = n mod 2^64 -> y18 mod 2^64 = (DT + 4) mod 2^64 -> y19 mod 2^64 = (DST + dcap) mod 2^64 ->
    y20 mod 2^64 = (tl + 256 * rsv) mod 2^64 ->
    evt usegs POST
      (MS (mkR (Z_to_bv 64 y1) (Z_to_bv 64 ysp) gp tp x5 x6 x7 (Z_to_bv 64 y8) (Z_to_bv 64 y9) (Z_to_bv 64 y10) (Z_to_bv 64 y11)
               (Z_to_bv 64 y12) x13 x14 x15 x16 x17 (Z_to_bv 64 y18) (Z_to_bv 64 y19) (Z_to_bv 64 y20) s5 s6 s7 s8 s9 s10 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x25a0c) fc None mm (seg_rom usegs)).
  Proof.
    intros mm junk y1 ysp y8 y9 y10 y11 y12 y18 y19 y20 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31
      DI BJ H1 HSP H8 H9 H10 H11 H12 H18 H19 H20.
    pose proof CTX as CTX'. x1_ctx_open CTX'.
    assert (BD8 : (SPV + -136) mod 8 = 0) by (clear - SPA; lia). clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'.
    rewrite (zbv_eqm _ _ H1), (zbv_eqm _ _ HSP), (zbv_eqm _ _ H8), (zbv_eqm _ _ H9), (zbv_eqm _ _ H10), (zbv_eqm _ _ H11),
            (zbv_eqm _ _ H12), (zbv_eqm _ _ H18), (zbv_eqm _ _ H19), (zbv_eqm _ _ H20).
    clear H1 HSP H8 H9 H10 H11 H12 H18 H19 H20.
    eapply evt_cut.
    { eapply (bit_init_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm (SPV + -136) SRC n src junk);
        first [exact BD8 | eassumption | clear BD8; lia]. }
    unfold bit_init_post. clear BD8. post_call usegs mm.
    try rewrite (ret_pc_even 0x20890) by lia.
    lazymatch goal with
    | H : (_ = n /\ _) \/ _ |- _ => destruct H as [(HR & HN1 & cont & bc & pad & HB1 & HB2 & BDCH) | (HER & HRB & bs & BDCH)]
    end.
    - lazymatch type of HR with ?r = n => subst r end.
      unfold bitd_cells in BDCH.
      eapply x1_main; [dinv_close | unfold BDC; exact BDCH | exact HN1 | lia | ].
      unfold LINV, bitd_ptr. destruct (8 <=? n) eqn:E8; [apply Z.leb_le in E8 | apply Z.leb_gt in E8]; lia.
    - eapply x1_cerr; [dinv_close | exact BDCH | exact HER | exact HRB].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_entry : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv usegs m0 -> stk usegs m0 lo SPV -> stk usegs m0 DST (DST + dcap) -> bytes_at usegs m0 SRC src -> bytes_at usegs m0 DT dtb ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20814) fc None m0 (seg_rom usegs)).
  Proof.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 MI STK OUT SRCB DTB.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA.
    assert (MU : munch [(DST, DST + dcap); (SPV - 144, SPV)] m0 m0) by apply munch_refl.
    assert (WM : wmono usegs m0 m0) by apply wmono_refl.
    carve_frame 136%nat STK.
    destruct (cb_carve usegs m0 (SPV + -136) 136 junk 40 96 FR ltac:(lia) ltac:(lia) ltac:(lia)) as (j1 & j2 & j3 & C1 & C2 & C3).
    change (Z.to_nat 40) with 40%nat in C1. change (Z.to_nat 96) with 96%nat in C2.
    replace (SPV + -136 + 40) with (SPV + -96) in C2 by lia.
    assert (FRW : wr_at usegs m0 (SPV + -136) 136) by kx_wr_at.
    clear FR C3.
    pose proof (dl_read SPV DST dcap SRC n DT tl rsv lo src dtb CTX) as DLR.
    assert (N0 : 0 <= n) by lia.
    destruct (Z.eq_dec dcap 0) as [DC0|DC1];
      [ kx_autoLx [0x25a0c] 60%nat
          [KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 0; KZRange (DST + dcap) 4096 (2^47); KZRange SRC 4096 (2^47);
           KZRange n 0 (2^32); KZRange DT 4096 (2^47); KZAlign DT 4; KZWr (SPV + -136) 136; KZDisj (SPV + -136) 136 DT 16388]
          [(DT, 16388)]
      | kx_autoLx [0x25a0c] 60%nat
          [KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange (DST + dcap) 4096 (2^47); KZRange SRC 4096 (2^47);
           KZRange n 0 (2^32); KZRange DT 4096 (2^47); KZAlign DT 4; KZWr (SPV + -136) 136; KZDisj (SPV + -136) 136 DT 16388]
          [(DT, 16388)] ].
    all: trap_close.
    all: try clear DTA.
    all: lazymatch goal with KXA : atoms_ok ?zs _ |- _ => let nz := kx_len zs in kx_read_eq nz RD end.
    all: rewrite (rdval_bytes_at usegs _ DT dtb 2 2 false DTB ltac:(lia) ltac:(change (Z.to_nat 2) with 2%nat; lia)), DLR in RD.
    all: rewrite RD.
    all: kx_mem.
    all: eapply x1_call; [dinv_close | exact C1 | first [reflexivity | lia] | first [reflexivity | lia] | first [reflexivity | lia]
                         | first [reflexivity | lia] | first [reflexivity | lia] | first [reflexivity | lia] | first [reflexivity | lia]
                         | first [reflexivity | lia] | first [reflexivity | lia] | first [reflexivity | lia]].
  Qed.
End DX1E.

(* [comment removed for export] *)
Theorem huf_1x1_proof : huf_1x1_stmt.
Proof.
  unfold huf_1x1_stmt, huf_int_stmt_at, PHUF_1X1, HUF_1X_STACK.
  intros until dtb.
  intros (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SL & S0 & S1 & S2 & OS1 & OS2 & DJ1 & SP16)
         (DTB & DL & T0 & T1 & OS3 & DJ2 & DT4) DT2 TL _ _.
  unfold HUF_DTABLE_BYTES in *.
  destruct (nth_error dtb 3) as [b3|] eqn:DT3;
    [| apply nth_error_None in DT3; exfalso; lia].
  assert (CTX : x1_ctx SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb).
  { pose proof (bv_unsigned_in_range 8 b3) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
    assert (EB : Z_to_bv 8 (bv_unsigned b3) = b3)
      by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
    unfold x1_ctx. rewrite EB. repeat split; try assumption; lia. }
  exact (x1_entry ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb CTX
                  t0 t1 t2 flags a6 a7 t3 t4 t5 t6 MI STK OUT SRCB DTB).
Qed.
