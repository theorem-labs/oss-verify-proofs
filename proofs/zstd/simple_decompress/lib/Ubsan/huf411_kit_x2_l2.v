(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2 ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx2.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma x2l2_swr : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. intros z. reflexivity. Qed.

Lemma x2l2_eqc : forall a c, a mod 2^64 = c -> 0 <= c < 2^64 -> Z_to_bv 64 a = Z_to_bv 64 c.
Proof. intros a c H R. apply zbv_eqm. rewrite H. symmetry. apply Z.mod_small. exact R. Qed.

Lemma x2l2_sxw : forall M x b, M = 2^64 -> x mod 2^32 = b -> 0 <= b < 2^31 -> bv_swrap 32 (x mod M + 0) = b.
Proof. intros M x b -> H B. rewrite x2l2_swr. Z.div_mod_to_equations. lia. Qed.

Lemma x2l2_sxwh : forall M x b, M = 2^64 -> x mod 2^32 = b -> 2^31 <= b < 2^32 -> bv_swrap 32 (x mod M + 0) = b - 2^32.
Proof. intros M x b -> H B. rewrite x2l2_swr. Z.div_mod_to_equations. lia. Qed.

Lemma x2l2_srlw : forall M x q r, M = 2^64 -> x mod 2^32 = 8 * q + r -> 0 <= q <= 8 -> 0 <= r <= 7 ->
  bv_swrap 32 (bv_wrap 32 (x mod M) ≫ 3) = q.
Proof.
  intros M x q r -> H Q R. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32).
  rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite x2l2_swr. Z.div_mod_to_equations. lia.
Qed.

Lemma x2l2_land : forall M x q r, M = 2^64 -> x mod 2^32 = 8 * q + r -> 0 <= r <= 7 -> Z.land (x mod M) 7 = r.
Proof.
  intros M x q r -> H R. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8.
  Z.div_mod_to_equations. lia.
Qed.

Lemma x2l2_subw : forall M x b z, M = 2^64 -> x mod 2^32 = b -> 0 <= z <= b -> b < 2^31 ->
  bv_swrap 32 (x mod M - z) = b - z.
Proof. intros M x b z -> H Z1 B. rewrite x2l2_swr. Z.div_mod_to_equations. lia. Qed.

Section X2L2.
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

  Notation x2_last := (RZ_huf_dx2.x2_last ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX).
  Notation x2_tail := (RZ_huf_dx2.x2_tail ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK).

  Notation LST pc mm x1 x6 x14 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 e5 e7 e9 e10 e11 e12 e13 e15 e16 e17 :=
    (ST pc mm x1 (Z_to_bv 64 e5) x6 (Z_to_bv 64 e7) (Z_to_bv 64 e9) (Z_to_bv 64 e10) (Z_to_bv 64 e11) (Z_to_bv 64 e12)
        (Z_to_bv 64 e13) x14 (Z_to_bv 64 e15) (Z_to_bv 64 e16) (Z_to_bv 64 e17) x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).

  Definition LRG (j e5 e7 e9 e10 e11 e12 e13 e15 e16 e17 : Z) : Prop :=
    e5 mod 2^64 = 65 /\ e7 mod 2^64 = 3 /\ e9 mod 2^64 = (DST + j) mod 2^64 /\ e10 mod 2^64 = (DT + 4) mod 2^64 /\
    e11 mod 2^64 = (DST + dcap) mod 2^64 /\ e12 mod 2^64 = 2^61 /\ e13 mod 2^64 = (tl + 256 * rsv) mod 2^64 /\
    e15 mod 2^64 = (DST + dcap - 2) mod 2^64 /\ e16 mod 2^64 = (-1 * DT + -5) mod 2^64 /\ e17 mod 2^64 = (64 - tl) mod 2^64.

  Ltac lrg_rw LR :=
    let H5 := fresh "H5" in let H7 := fresh "H7" in let H9 := fresh "H9" in let H10 := fresh "H10" in
    let H11 := fresh "H11" in let H12 := fresh "H12" in let H13 := fresh "H13" in let H15 := fresh "H15" in
    let H16 := fresh "H16" in let H17 := fresh "H17" in
    destruct LR as (H5 & H7 & H9 & H10 & H11 & H12 & H13 & H15 & H16 & H17);
    rewrite (x2l2_eqc _ _ H5) by lia; rewrite (x2l2_eqc _ _ H7) by lia; rewrite (x2l2_eqc _ _ H12) by lia;
    rewrite (zbv_eqm _ _ H9), (zbv_eqm _ _ H10), (zbv_eqm _ _ H11), (zbv_eqm _ _ H13), (zbv_eqm _ _ H15),
            (zbv_eqm _ _ H16), (zbv_eqm _ _ H17);
    clear H5 H7 H9 H10 H11 H12 H13 H15 H16 H17.

  Ltac x2c :=
    first [ reflexivity
          | (unfold LRG; repeat match goal with |- _ /\ _ => split end; first [reflexivity | lia | f_equal; lia]; fail)
          | (unfold x2_pinv; lia)
          | lia
          | f_equal; lia ].

  Lemma x2_l2body : forall mm j bc P fl cw pad (x1 x6 x14 x18 x19 x20 x21 x22 x23 x29 x30 x31 : word)
                      (e5 e7 e9 e10 e11 e12 e13 e15 e16 e17 e28 : Z),
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 0 <= j <= dcap -> 0 <= bc <= 64 -> (fl = 0 \/ fl = 1) ->
    LRG j e5 e7 e9 e10 e11 e12 e13 e15 e16 e17 -> e28 mod 2^64 = fl ->
    (forall mm' j' bc' bcx' cw' pad' (y1 y6 y18 y19 y20 y21 y22 y23 y28 y29 y30 y31 : word)
            (f5 f7 f9 f10 f11 f12 f13 f15 f16 f17 : Z),
        DINV2 mm' -> BDC2 mm' cw' (Z_to_bv 64 bc') pad' (Z_to_bv 64 P) -> j < j' <= dcap -> 0 <= bc' <= 64 ->
        bcx' mod 2^32 = bc' -> LRG j' f5 f7 f9 f10 f11 f12 f13 f15 f16 f17 ->
        evt usegs POST (LST 0x203e8 mm' y1 y6 (Z_to_bv 64 bcx') y18 y19 y20 y21 y22 y23 y28 y29 y30 y31
                           f5 f7 f9 f10 f11 f12 f13 f15 f16 f17)) ->
    evt usegs POST (LST 0x20564 mm x1 x6 x14 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 e28) x29 x30 x31
                       e5 e7 e9 e10 e11 e12 e13 e15 e16 e17).
  Proof.
    intros mm j bc P fl cw pad x1 x6 x14 x18 x19 x20 x21 x22 x23 x29 x30 x31 e5 e7 e9 e10 e11 e12 e13 e15 e16 e17 e28
      DI BD HJ HBC HFL LR H28 KH.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. unfold x2_bdc in BD.
    lrg_rw LR.
    rewrite (x2l2_eqc _ _ H28) by lia. clear H28.
    remember (64 - tl) as sh eqn:HSH.
    assert (TBL : tbl_in_log usegs mm DT sh 4 7 1 2) by (rewrite HSH; eapply x2_tbl; eauto).
    destruct (Z_lt_le_dec (dcap - j) 2) as [SM|BG].
    - clear KH.
      destruct HFL as [-> | ->].
      all: kx_autoLx [0x205e0] 20%nat
             [KZRange (dcap - j) 0 1; KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
              KZRange (DST + j) 4096 (2^47); KZRange (DST + dcap) 4096 (2^47)] (@nil (Z * Z)).
      all: lazymatch goal with
           | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 ?E) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x205e0) _ _ _ _) =>
               eapply (x2_tail _ (E - DST)); [exact DI | unfold x2_bdc; exact BD | ..]
           end.
      all: subst sh; x2c.
    - destruct HFL as [-> | ->].
      + clear KH.
        kx_autoLx [0x205e0] 20%nat
          [KZRange (dcap - j) 2 (2^32); KZRange j 0 (2^32); KZRange dcap 2 (2^32); KZRange DST 4096 (2^47);
           KZRange (DST + j) 4096 (2^47); KZRange (DST + dcap) 4096 (2^47)] (@nil (Z * Z)).
        all: lazymatch goal with
             | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 ?E) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x205e0) _ _ _ _) =>
                 eapply (x2_tail _ (E - DST)); [exact DI | unfold x2_bdc; exact BD | ..]
             end.
        all: subst sh; x2c.
      + Time kx_autoLx [0x203e8; 0x205e0] 80%nat
          [KZRange (dcap - j) 2 (2^32); KZRange j 0 (2^32); KZRange dcap 2 (2^32); KZRange SPV 4096 (2^47);
           KZRange DST 4096 (2^47); KZRange (DST + j) 4096 (2^47); KZRange (DST + dcap) 4096 (2^47);
           KZRange DT 4096 (2^47); KZRange sh 52 63; KZRange tl 1 12; KZRange rsv 0 255; KZRange bc 0 64;
           KZWr DST dcap; KZWr (SPV + -112) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV + -112) 40;
           KZDisj (SPV + -112) 40 DT 16388; KZTblLog DT sh 4 7 1 2]
          [(DT, 16388); (SPV + -112, 40)].
        all: tp_close.
        all: kx_ev_ranges; kx_mem; kx_strip_mod.
        all: lazymatch goal with
             | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 ?E) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x203e8) _ _ _ _) =>
                 eapply (KH _ (E - DST)); [dinv_close | unfold x2_bdc; eassumption | ..]
             | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 ?E) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x205e0) _ _ _ _) =>
                 eapply (x2_tail _ (E - DST)); [dinv_close | unfold x2_bdc; eassumption | ..]
             end.
        all: subst sh; x2c.
  Qed.

  Lemma x2_l2rl : forall mm j bc bcx P cw pad (x1 x6 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word)
                    (e5 e7 e9 e10 e11 e12 e13 e15 e16 e17 : Z),
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 0 <= j <= dcap -> 0 <= bc <= 64 -> PINV P ->
    bcx mod 2^32 = bc -> LRG j e5 e7 e9 e10 e11 e12 e13 e15 e16 e17 ->
    (forall mm' fl bc' P' cw' pad' (y1 y6 y14 y18 y19 y20 y21 y22 y23 y29 y30 y31 : word)
            (f5 f7 f9 f10 f11 f12 f13 f15 f16 f17 f28 : Z),
        DINV2 mm' -> BDC2 mm' cw' (Z_to_bv 64 bc') pad' (Z_to_bv 64 P') -> 0 <= bc' <= 64 -> (fl = 0 \/ fl = 1) ->
        PINV P' -> LRG j f5 f7 f9 f10 f11 f12 f13 f15 f16 f17 -> f28 mod 2^64 = fl ->
        evt usegs POST (LST 0x20564 mm' y1 y6 y14 y18 y19 y20 y21 y22 y23 (Z_to_bv 64 f28) y29 y30 y31
                           f5 f7 f9 f10 f11 f12 f13 f15 f16 f17)) ->
    evt usegs POST (LST 0x203e8 mm x1 x6 (Z_to_bv 64 bcx) x18 x19 x20 x21 x22 x23 x28 x29 x30 x31
                       e5 e7 e9 e10 e11 e12 e13 e15 e16 e17).
  Proof.
    intros mm j bc bcx P cw pad x1 x6 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 e5 e7 e9 e10 e11 e12 e13 e15 e16 e17
      DI BD HN HJ HBC HP HBX LR KB.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. unfold x2_bdc in BD.
    lrg_rw LR.
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); lia).
    destruct QR as (q & r & -> & HQ & HR).
    destruct HP as [-> | (O1 & O2)].
    - Time kx_autoLx [0x20564] 40%nat
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^32); KZRange SRC 4096 (2^47);
         KZRange (SRC + n) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32);
         KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47); KZRange DT 4096 (2^47); KZWr (SPV + -112) 40;
         KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
        [(SRC, n); (SPV + -112, 40)].
      all: tp_close.
      all: try kx_mem.
      all: eapply (KB _ 0); [dinv_close | unfold x2_bdc; eassumption | ..].
      all: x2c.
    - assert (O : exists off, P = SRC + off) by (exists (P - SRC); lia). destruct O as (off & ->).
      destruct (Z_lt_le_dec off 8) as [C8|C8].
      + Time kx_autoLx [0x203fc] 40%nat
          [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
           KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
           KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32);
           KZRange (DST + dcap) 4096 (2^47); KZRange DT 4096 (2^47); KZWr (SPV + -112) 40;
           KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
          [(SRC, n); (SPV + -112, 40)].
        all: tp_close.
        all: try kx_mem.
        zstep. rewrite (x2l2_srlw _ bcx q r) by first [reflexivity | assumption | lia].
        destruct (Z_lt_le_dec off q) as [CQ|CQ].
        * Time kx_autoLx [0x20448] 80%nat
            [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange (q - off) 1 8; KZRange q 0 8; KZRange r 0 7;
             KZRange (8 * q + r) 0 64; KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
             KZRange (SRC + off) 4097 (2^47 - 8); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32);
             KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47); KZRange DT 4096 (2^47); KZWr (SPV + -112) 40;
             KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
            [(SRC, n); (SPV + -112, 40)].
          all: tp_close.
          all: try kx_mem.
          zstep.
          lazymatch goal with |- context [bv_swrap 32 (bcx mod ?M - ?z)] =>
            rewrite (x2l2_subw M bcx (8 * q + r) z) by first [reflexivity | assumption | lia] end.
          Time kx_autoLx [0x20564] 80%nat
            [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange (q - off) 1 8; KZRange q 0 8; KZRange r 0 7;
             KZRange (8 * q + r) 0 64; KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
             KZRange (SRC + off) 4097 (2^47 - 8); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32);
             KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47); KZRange DT 4096 (2^47); KZWr (SPV + -112) 40;
             KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
            [(SRC, n); (SPV + -112, 40)].
          all: tp_close.
          all: kx_mem.
          all: kx_read_ranges.
          all: first [ eapply (KB _ 0); [dinv_close | unfold x2_bdc; eassumption | ..]; x2c
                     | eapply (KB _ 1); [dinv_close | unfold x2_bdc; eassumption | ..]; x2c ].
        * Time kx_autoLx [0x20448] 80%nat
            [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange (off - q) 0 7; KZRange q 0 8; KZRange r 0 7;
             KZRange (8 * q + r) 0 64; KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
             KZRange (SRC + off) 4097 (2^47 - 8); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32);
             KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47); KZRange DT 4096 (2^47); KZWr (SPV + -112) 40;
             KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
            [(SRC, n); (SPV + -112, 40)].
          all: tp_close.
          all: try kx_mem.
          zstep.
          lazymatch goal with |- context [bv_swrap 32 (bcx mod ?M - ?z)] =>
            rewrite (x2l2_subw M bcx (8 * q + r) z) by first [reflexivity | assumption | lia] end.
          Time kx_autoLx [0x20564] 80%nat
            [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange (off - q) 0 7; KZRange q 0 8; KZRange r 0 7;
             KZRange (8 * q + r) 0 64; KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
             KZRange (SRC + off) 4097 (2^47 - 8); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32);
             KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47); KZRange DT 4096 (2^47); KZWr (SPV + -112) 40;
             KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
            [(SRC, n); (SPV + -112, 40)].
          all: tp_close.
          all: kx_mem.
          all: kx_read_ranges.
          all: first [ eapply (KB _ 0); [dinv_close | unfold x2_bdc; eassumption | ..]; x2c
                     | eapply (KB _ 1); [dinv_close | unfold x2_bdc; eassumption | ..]; x2c ].
      + Time kx_autoLx [0x204c4] 40%nat
          [KZRange (n - off) 8 (2^32); KZRange off 8 (2^32); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
           KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
           KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32);
           KZRange (DST + dcap) 4096 (2^47); KZRange DT 4096 (2^47); KZWr (SPV + -112) 40;
           KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
          [(SRC, n); (SPV + -112, 40)].
        all: tp_close.
        all: try kx_mem.
        zstep. rewrite (x2l2_srlw _ bcx q r) by first [reflexivity | assumption | lia].
        Time kx_autoLx [0x204e4] 40%nat
          [KZRange (n - off) 8 (2^32); KZRange off 8 (2^32); KZRange (off - q) 0 (2^32); KZRange q 0 8; KZRange r 0 7;
           KZRange (8 * q + r) 0 64; KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
           KZRange (SRC + off) 4097 (2^47 - 8); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32);
           KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47); KZRange DT 4096 (2^47); KZWr (SPV + -112) 40;
           KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
          [(SRC, n); (SPV + -112, 40)].
        all: tp_close.
        all: try kx_mem.
        zstep. rewrite (x2l2_land _ bcx q r) by first [reflexivity | assumption | lia].
        Time kx_autoLx [0x20564] 80%nat
          [KZRange (n - off) 8 (2^32); KZRange off 8 (2^32); KZRange (off - q) 0 (2^32); KZRange q 0 8; KZRange r 0 7;
           KZRange (8 * q + r) 0 64; KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
           KZRange (SRC + off) 4097 (2^47 - 8); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32);
           KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47); KZRange DT 4096 (2^47); KZWr (SPV + -112) 40;
           KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
          [(SRC, n); (SPV + -112, 40)].
        all: tp_close.
        all: kx_mem.
        all: kx_read_ranges.
        all: eapply (KB _ 1); [dinv_close | unfold x2_bdc; eassumption | ..].
        all: x2c.
  Qed.

  Lemma x2_loop2 : forall (k : nat) mm j bc bcx P cw pad (x1 x6 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word)
                     (e5 e7 e9 e10 e11 e12 e13 e15 e16 e17 : Z),
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 0 <= j <= dcap -> dcap - j <= Z.of_nat k ->
    0 <= bc <= 64 -> PINV P -> bcx mod 2^32 = bc -> LRG j e5 e7 e9 e10 e11 e12 e13 e15 e16 e17 ->
    evt usegs POST (LST 0x203e8 mm x1 x6 (Z_to_bv 64 bcx) x18 x19 x20 x21 x22 x23 x28 x29 x30 x31
                       e5 e7 e9 e10 e11 e12 e13 e15 e16 e17).
  Proof.
    induction k as [|k IH]; intros mm j bc bcx P cw pad x1 x6 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31
      e5 e7 e9 e10 e11 e12 e13 e15 e16 e17 DI BD HN HJ HK HBC HP HBX LR.
    all: eapply x2_l2rl; [exact DI | exact BD | exact HN | exact HJ | exact HBC | exact HP | exact HBX | exact LR |].
    all: intros mm' fl bc' P' cw' pad' y1 y6 y14 y18 y19 y20 y21 y22 y23 y29 y30 y31
           f5 f7 f9 f10 f11 f12 f13 f15 f16 f17 f28 DI' BD' HBC' HFL HP' LR' H28.
    all: eapply x2_l2body; [exact DI' | exact BD' | exact HJ | exact HBC' | exact HFL | exact LR' | exact H28 |].
    all: intros mm'' j' bc'' bcx'' cw'' pad'' z1 z6 z18 z19 z20 z21 z22 z23 z28 z29 z30 z31
           g5 g7 g9 g10 g11 g12 g13 g15 g16 g17 DI'' BD'' HJ' HBC'' HBX'' LR''.
    - exfalso. lia.
    - eapply (IH _ j'); [exact DI'' | exact BD'' | exact HN | lia | lia | exact HBC'' | exact HP' | exact HBX'' | exact LR''].
  Qed.

  Lemma x2_fcc2 : forall mm j bc bcx P cw pad (x1 x5 x6 x7 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word)
                   (e9 e10 e11 e12 e13 : Z),
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 0 <= j <= dcap ->
    0 <= bc < 2^32 -> (bc <= 64 -> PINV P) -> bcx mod 2^32 = bc ->
    e9 mod 2^64 = (DST + j) mod 2^64 -> e10 mod 2^64 = (DT + 4) mod 2^64 -> e11 mod 2^64 = (DST + dcap) mod 2^64 ->
    e12 mod 2^64 = 2^61 -> e13 mod 2^64 = (tl + 256 * rsv) mod 2^64 ->
    evt usegs POST (ST 0x203c0 mm x1 x5 x6 x7 (Z_to_bv 64 e9) (Z_to_bv 64 e10) (Z_to_bv 64 e11) (Z_to_bv 64 e12)
                      (Z_to_bv 64 e13) (Z_to_bv 64 bcx) x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros mm j bc bcx P cw pad x1 x5 x6 x7 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 e9 e10 e11 e12 e13
      DI BD HN HJ HBC HP HBX H9 H10 H11 H12 H13.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. unfold x2_bdc in BD.
    rewrite (zbv_eqm _ _ H9), (zbv_eqm _ _ H10), (zbv_eqm _ _ H11), (zbv_eqm _ _ H13).
    rewrite (x2l2_eqc _ _ H12) by lia.
    clear H9 H10 H11 H12 H13.
    kx_autoLx [0x203e0] 20%nat
      [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange (DST + j) 4096 (2^47);
       KZRange (DST + dcap) 4096 (2^47); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255] (@nil (Z * Z)).
    all: tp_close.
    all: try kx_mem.
    zstep.
    destruct (Z_lt_le_dec bc 65) as [B64|B65].
    - rewrite (x2l2_sxw _ bcx bc) by first [reflexivity | assumption | lia].
      kx_autoLx [0x203e8] 20%nat
        [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange (DST + j) 4096 (2^47);
         KZRange (DST + dcap) 4096 (2^47); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
         KZRange bc 0 64] (@nil (Z * Z)).
      all: tp_close.
      all: eapply (x2_loop2 (Z.to_nat (dcap - j)) _ j bc bcx P); [dinv_close | unfold x2_bdc; eassumption | ..].
      all: first [ apply HP; lia | x2c | rewrite ?(neg_dl_sh tl rsv TL); x2c ].
    - destruct (Z_lt_le_dec bc (2^31)) as [BL|BH].
      + rewrite (x2l2_sxw _ bcx bc) by first [reflexivity | assumption | lia].
        kx_autoLx [0x205e0] 30%nat
          [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange (DST + j) 4096 (2^47);
           KZRange (DST + dcap) 4096 (2^47); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
           KZRange bc 65 (2^31 - 1); KZRange SPV 4096 (2^47); KZWr (SPV + -112) 40] [(SPV + -112, 40)].
        all: tp_close.
        all: kx_mem.
        all: eapply (x2_tail _ j); [dinv_close | unfold x2_bdc; eassumption | ..].
        all: first [ x2c | rewrite ?(neg_dl_sh tl rsv TL); x2c ].
      + rewrite (x2l2_sxwh _ bcx bc) by first [reflexivity | assumption | lia].
        kx_autoLx [0x205e0] 30%nat
          [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange (DST + j) 4096 (2^47);
           KZRange (DST + dcap) 4096 (2^47); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
           KZRange bc (2^31) (2^32 - 1); KZRange SPV 4096 (2^47); KZWr (SPV + -112) 40] [(SPV + -112, 40)].
        all: tp_close.
        all: kx_mem.
        all: eapply (x2_tail _ j); [dinv_close | unfold x2_bdc; eassumption | ..].
        all: first [ x2c | rewrite ?(neg_dl_sh tl rsv TL); x2c ].
  Qed.

  Lemma x2_fcc : forall mm j bc bcx P cw pad (x1 x5 x6 x7 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word)
                   (e9 e10 e11 e12 e13 : Z),
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 0 <= j <= dcap ->
    0 <= bc < 2^32 -> (bc <= 64 -> PINV P) -> bcx mod 2^32 = bc ->
    e9 mod 2^64 = (DST + j) mod 2^64 -> e10 mod 2^64 = (DT + 4) mod 2^64 -> e11 mod 2^64 = (DST + dcap) mod 2^64 ->
    e12 mod 2^64 = 2^61 -> e13 mod 2^64 = (tl + 256 * rsv) mod 2^64 ->
    evt usegs POST (ST 0x203b4 mm x1 x5 x6 x7 (Z_to_bv 64 e9) (Z_to_bv 64 e10) (Z_to_bv 64 e11) (Z_to_bv 64 e12)
                      (Z_to_bv 64 e13) (Z_to_bv 64 bcx) x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros mm j bc bcx P cw pad x1 x5 x6 x7 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 e9 e10 e11 e12 e13
      DI BD HN HJ HBC HP HBX H9 H10 H11 H12 H13.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    rewrite (zbv_eqm _ _ H9), (zbv_eqm _ _ H11).
    kx_autoLx [0x203c0; 0x2063c] 6%nat
      [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange (DST + j) 4096 (2^47);
       KZRange (DST + dcap) 4096 (2^47)] (@nil (Z * Z)).
    all: lazymatch goal with
         | |- context [Z_to_bv 64 0x203c0] =>
             eapply (x2_fcc2 mm j bc bcx P cw pad); [exact DI | exact BD | exact HN | exact HJ | exact HBC | exact HP | exact HBX | ..]
         | |- _ => eapply (x2_last mm j); [exact DI | exact BD | ..]
         end.
    all: first [reflexivity | eassumption | lia].
  Qed.
End X2L2.
