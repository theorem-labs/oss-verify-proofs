(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2 ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx2 huf411_kit_x2_l2.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section X2LA.
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
  Ltac la_evr j := try (let H := fresh "KXVR" in kx_erange H (EVar j); cbn [edenot] in H).

  Notation LA pc mm x1 p1 bc cw x18 x19 x20 x21 x22 x23 t5 x31 :=
    (ST pc mm x1 (Z_to_bv 64 (DST + dcap - 9)) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 65) (Z_to_bv 64 p1)
        (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (tl + 256 * rsv)) (Z_to_bv 64 bc)
        (Z_to_bv 64 SRC) (Z_to_bv 64 (SRC + 8)) cw x18 x19 x20 x21 x22 x23 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 1)
        (Z_to_bv 64 t5) x31).

  Lemma la_fcc : forall mm bc bcx P cw pad (x1 x5 x6 x7 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word)
                   (e9 e10 e11 e12 e13 : Z),
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> DST <= e9 <= DST + dcap ->
    0 <= bc < 2^32 -> (bc <= 64 -> PINV P) -> bcx mod 2^32 = bc ->
    e10 mod 2^64 = (DT + 4) mod 2^64 -> e11 mod 2^64 = (DST + dcap) mod 2^64 ->
    e12 mod 2^64 = 2^61 -> e13 mod 2^64 = (tl + 256 * rsv) mod 2^64 ->
    evt usegs POST (ST 0x203b4 mm x1 x5 x6 x7 (Z_to_bv 64 e9) (Z_to_bv 64 e10) (Z_to_bv 64 e11) (Z_to_bv 64 e12)
                      (Z_to_bv 64 e13) (Z_to_bv 64 bcx) x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros mm bc bcx P cw pad x1 x5 x6 x7 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 e9 e10 e11 e12 e13
      DI BD HN H9 HB HP HX H10 H11 H12 H13.
    eapply x2_fcc with (j := e9 - DST).
    all: first [eassumption | lia | (replace (DST + (e9 - DST)) with e9 by lia; reflexivity)].
  Qed.

  Lemma x2_la_body : forall mm j bc fl P cw pad (x1 x18 x20 x21 x22 x23 : word) t5,
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 0 <= j <= dcap -> (fl = 0 \/ fl = 1) ->
    0 <= bc <= 64 -> PINV P ->
    (forall mm' bc' cw' pad' (y1 y19 y20 y21 y22 y23 y31 : word) e9 e14,
        DINV2 mm' -> BDC2 mm' cw' (Z_to_bv 64 bc') pad' (Z_to_bv 64 P) -> DST + j < e9 <= DST + dcap -> 0 <= bc' <= 64 ->
        e14 mod 2^64 = bc' mod 2^64 ->
        evt usegs POST (LA 0x1fc4c mm' y1 e9 e14 cw' (Z_to_bv 64 P) y19 y20 y21 y22 y23 t5 y31)) ->
    evt usegs POST (LA 0x1fdc0 mm x1 (DST + j) bc cw x18 (Z_to_bv 64 fl) x20 x21 x22 x23 t5 (Z_to_bv 64 P)).
  Proof.
    intros mm j bc fl P cw pad x1 x18 x20 x21 x22 x23 t5 DI BD HN HJ HFL HBC HP KH.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. pose proof BD as BD'. unfold x2_bdc in BD'.
    destruct (Z_lt_le_dec (dcap - j) 10) as [SM|BG].
    - clear KH.
      destruct HFL as [-> | ->].
      all: kx_autoLx [0x203b4] 20%nat
             [KZRange (dcap - j) 0 9; KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
              KZRange (DST + dcap) 4096 (2^47)] (@nil (Z * Z)).
      all: kx_mem.
      all: eapply la_fcc; [dinv_close | unfold x2_bdc; eassumption | exact HN | lia | lia | intros; exact HP | | | | |]; first [reflexivity | lia].
    - destruct HFL as [-> | ->].
      + clear KH.
        kx_autoLx [0x203b4] 20%nat
          [KZRange (dcap - j) 10 (2^32); KZRange j 0 (2^32); KZRange dcap 10 (2^32); KZRange DST 4096 (2^47);
           KZRange (DST + dcap) 4096 (2^47)] (@nil (Z * Z)).
        all: kx_mem.
      all: eapply la_fcc; [dinv_close | unfold x2_bdc; eassumption | exact HN | lia | lia | intros; exact HP | | | | |]; first [reflexivity | lia].
      + remember (64 - tl) as sh eqn:HSH.
        assert (TBL : tbl_in_log usegs mm DT sh 4 7 1 2) by (subst sh; eapply x2_tbl; eassumption).
        assert (SHR : 52 <= sh <= 63) by lia.
        Time kx_autoLx [0x203b4; 0x1fc4c] 200%nat
          [KZRange (dcap - j) 10 (2^32); KZRange j 0 (2^32); KZRange (DST + j) 4096 (2^47 - 10); KZRange dcap 10 (2^32);
           KZRange DST 4096 (2^47); KZRange (DST + dcap) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange tl 1 12; KZRange bc 0 64;
           KZRange DT 4096 (2^47); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange n 1 (2^32); KZRange sh 52 63;
          KZWr DST dcap; KZWr (SPV + -112) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV + -112) 40; KZDisj DST dcap (SPV + -72) 72;
           KZDisj (SPV + -112) 40 DT 16388; KZDisj DST dcap SRC n; KZDisj (SPV + -112) 40 SRC n; KZTblLog DT sh 4 7 1 2]
          [(DT, 16388); (SPV + -112, 40)].
        all: tp_close.
        all: kx_read_ranges.
        all: kx_ev_ranges.
        all: la_evr 37%nat. all: la_evr 40%nat. all: la_evr 43%nat. all: la_evr 46%nat. all: la_evr 49%nat.
        all: kx_mem.
        all: subst sh.
        all: lazymatch goal with
             | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1fc4c) _ _ _ _) =>
                 eapply KH; [dinv_close | unfold x2_bdc; eassumption | lia | lia | lia]
             | |- evt _ _ (MS _ _ (Z_to_bv 64 0x203b4) _ _ _ _) =>
                 eapply la_fcc; [dinv_close | unfold x2_bdc; eassumption | exact HN | lia | lia | intros; exfalso; lia | lia | | | |];
                 first [reflexivity | lia]
             end.
  Qed.

  Lemma x2_la_rl : forall mm j bc P cw pad (x1 x19 x20 x21 x22 x23 x31 : word) t5,
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 0 <= j <= dcap -> 0 <= bc <= 64 -> PINV P ->
    (forall mm' fl bc' P' cw' pad' (y18 y20 y21 y22 y23 : word) e14 e19 e31,
        DINV2 mm' -> BDC2 mm' cw' (Z_to_bv 64 bc') pad' (Z_to_bv 64 P') -> (fl = 0 \/ fl = 1) -> 0 <= bc' <= 64 -> PINV P' ->
        e14 mod 2^64 = bc' mod 2^64 -> e19 mod 2^64 = fl mod 2^64 -> e31 mod 2^64 = P' mod 2^64 ->
        evt usegs POST (LA 0x1fdc0 mm' x1 (DST + j) e14 cw' y18 (Z_to_bv 64 e19) y20 y21 y22 y23 t5 (Z_to_bv 64 e31))) ->
    evt usegs POST (LA 0x1fc4c mm x1 (DST + j) bc cw (Z_to_bv 64 P) x19 x20 x21 x22 x23 t5 x31).
  Proof.
    intros mm j bc P cw pad x1 x19 x20 x21 x22 x23 x31 t5 DI BD HN HJ HBC HP KB.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. unfold x2_bdc in BD.
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); lia).
    destruct QR as (q & r & -> & HQ & HR).
    unfold x2_pinv in HP. destruct HP as [-> | (O1 & O2)].
    - Time kx_autoLx [0x1fdc0] 40%nat
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
         KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47);
         KZRange DT 4096 (2^47); KZWr (SPV + -112) 40; KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
        [(SRC, n); (SPV + -112, 40)].
      all: tp_close.
      all: kx_mem.
      all: first [ eapply (KB _ 0); [dinv_close | unfold x2_bdc; eassumption | | | unfold x2_pinv | | |]; lia
                 | eapply (KB _ 1); [dinv_close | unfold x2_bdc; eassumption | | | unfold x2_pinv | | |]; lia ].
    - assert (O : exists off, P = SRC + off) by (exists (P - SRC); lia). destruct O as (off & ->).
      destruct (Z_lt_le_dec off 8) as [C8|C8]; [destruct (Z_lt_le_dec off q) as [CQ|CQ]|].
      3: kx_autoLx [0x1fdc0] 120%nat
        [KZRange (n - off) 8 (2^32); KZRange off 8 (2^32); KZRange (off - q) 0 (2^32); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
         KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
         KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47);
         KZRange DT 4096 (2^47); KZWr (SPV + -112) 40; KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
        [(SRC, n); (SPV + -112, 40)].
      2: kx_autoLx [0x1fdc0] 120%nat
        [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange (off - q) 0 7; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
         KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
         KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47);
         KZRange DT 4096 (2^47); KZWr (SPV + -112) 40; KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
        [(SRC, n); (SPV + -112, 40)].
      1: kx_autoLx [0x1fdc0] 120%nat
        [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange (q - off) 1 8; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
         KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
         KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47);
         KZRange DT 4096 (2^47); KZWr (SPV + -112) 40; KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
        [(SRC, n); (SPV + -112, 40)].
      all: tp_close.
      all: kx_mem.
      all: kx_read_ranges.
      all: first [ eapply (KB _ 0); [dinv_close | unfold x2_bdc; eassumption | | | unfold x2_pinv | | |]; lia
                 | eapply (KB _ 1); [dinv_close | unfold x2_bdc; eassumption | | | unfold x2_pinv | | |]; lia ].
  Qed.

  Lemma x2_la_loop : forall (k : nat) mm j bc P cw pad (x1 x19 x20 x21 x22 x23 x31 : word) t5,
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 0 <= j <= dcap -> dcap - j <= Z.of_nat k ->
    0 <= bc <= 64 -> PINV P ->
    evt usegs POST (LA 0x1fc4c mm x1 (DST + j) bc cw (Z_to_bv 64 P) x19 x20 x21 x22 x23 t5 x31).
  Proof.
    induction k as [|k IH]; intros mm j bc P cw pad x1 x19 x20 x21 x22 x23 x31 t5 DI BD HN HJ HK HBC HP.
    all: eapply x2_la_rl; [exact DI | exact BD | exact HN | exact HJ | exact HBC | exact HP |].
    all: intros mm' fl bc' P' cw' pad' y18 y20 y21 y22 y23 e14 e19 e31 DI' BD' HFL HBC' HP' H14 H19 H31.
    all: rewrite (zbv_eqm e14 _ H14), (zbv_eqm e19 _ H19), (zbv_eqm e31 _ H31).
    all: eapply x2_la_body; [exact DI' | exact BD' | exact HN | exact HJ | exact HFL | exact HBC' | exact HP' |].
    all: intros mm'' bc'' cw'' pad'' z1 z19 z20 z21 z22 z23 z31 e9 e14' DI'' BD'' H9 HBC'' H14'.
    - exfalso. lia.
    - rewrite (zbv_eqm e14' _ H14'). replace e9 with (DST + (e9 - DST)) by lia.
      eapply IH; [exact DI'' | exact BD'' | exact HN | lia | lia | exact HBC'' | exact HP'].
  Qed.

  Lemma x2_la_entry : forall mm cw cwr bc P pad (x1 x19 x20 x21 x22 x23 x31 : word)
                        (e5 e6 e7 e9 e10 e11 e12 e13 e14 e15 e16 e18 e28 e29 e30 : Z),
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> cwr = cw -> 0 <= bc <= 64 -> PINV P ->
    e5 mod 2^64 = (DST + dcap - 9) mod 2^64 -> e6 mod 2^64 = (-1 * DT + -5) mod 2^64 -> e7 mod 2^64 = 65 ->
    e9 mod 2^64 = DST mod 2^64 -> e10 mod 2^64 = (DT + 4) mod 2^64 -> e11 mod 2^64 = (DST + dcap) mod 2^64 ->
    e12 mod 2^64 = 2^61 -> e13 mod 2^64 = (tl + 256 * rsv) mod 2^64 -> e14 mod 2^64 = bc mod 2^64 ->
    e15 mod 2^64 = SRC mod 2^64 -> e16 mod 2^64 = (SRC + 8) mod 2^64 -> e18 mod 2^64 = P mod 2^64 ->
    e28 mod 2^64 = (64 - tl) mod 2^64 -> e29 mod 2^64 = 1 ->
    evt usegs POST (ST 0x1fc48 mm x1 (Z_to_bv 64 e5) (Z_to_bv 64 e6) (Z_to_bv 64 e7) (Z_to_bv 64 e9) (Z_to_bv 64 e10)
                       (Z_to_bv 64 e11) (Z_to_bv 64 e12) (Z_to_bv 64 e13) (Z_to_bv 64 e14) (Z_to_bv 64 e15)
                       (Z_to_bv 64 e16) cwr (Z_to_bv 64 e18) x19 x20 x21 x22 x23 (Z_to_bv 64 e28) (Z_to_bv 64 e29)
                       (Z_to_bv 64 e30) x31).
  Proof using All.
    intros mm cw cwr bc P pad x1 x19 x20 x21 x22 x23 x31 e5 e6 e7 e9 e10 e11 e12 e13 e14 e15 e16 e18 e28 e29 e30
      DI BD HN HCW HBC HP H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H18 H28 H29.
    subst cwr.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    assert (H7' : e7 mod 2^64 = 65 mod 2^64) by (rewrite H7; reflexivity).
    assert (H9' : e9 mod 2^64 = (DST + 0) mod 2^64) by (rewrite Z.add_0_r; exact H9).
    assert (H12' : e12 mod 2^64 = (2^61) mod 2^64) by (rewrite H12; reflexivity).
    assert (H29' : e29 mod 2^64 = 1 mod 2^64) by (rewrite H29; reflexivity).
    rewrite (zbv_eqm e5 _ H5), (zbv_eqm e6 _ H6), (zbv_eqm e7 _ H7'), (zbv_eqm e9 _ H9'), (zbv_eqm e10 _ H10),
      (zbv_eqm e11 _ H11), (zbv_eqm e12 _ H12'), (zbv_eqm e13 _ H13), (zbv_eqm e14 _ H14), (zbv_eqm e15 _ H15),
      (zbv_eqm e16 _ H16), (zbv_eqm e18 _ H18), (zbv_eqm e28 _ H28), (zbv_eqm e29 _ H29').
    kx_autoLx [0x1fc4c] 4%nat
      [KZRange bc 0 64; KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange (DST + dcap) 4096 (2^47); KZRange tl 1 12]
      (@nil (Z * Z)).
    all: eapply (x2_la_loop (Z.to_nat dcap)); [exact DI | exact BD | exact HN | lia | rewrite Z2Nat.id by lia; lia | exact HBC | exact HP].
  Qed.

End X2LA.
