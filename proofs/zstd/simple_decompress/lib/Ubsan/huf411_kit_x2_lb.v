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

Section X2LB.
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

  Notation LST pc mm x1 p bc P cw x19 x20 x21 x22 x23 sh zf x31 :=
    (ST pc mm x1 (Z_to_bv 64 (dcap + DST + -7)) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 65) (Z_to_bv 64 p)
        (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (tl + 256 * rsv))
        (Z_to_bv 64 bc) (Z_to_bv 64 SRC) (Z_to_bv 64 (SRC + 8)) cw (Z_to_bv 64 P) x19 x20 x21 x22 x23
        (Z_to_bv 64 sh) (Z_to_bv 64 zf) (Z_to_bv 64 8) x31).
  Notation BST mm x1 j bc fl P cw x18 x20 x21 x22 x23 sh zf :=
    (ST 0x201d0 mm x1 (Z_to_bv 64 (dcap + DST + -7)) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 65) (Z_to_bv 64 (DST + j))
        (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (tl + 256 * rsv))
        (Z_to_bv 64 bc) (Z_to_bv 64 SRC) (Z_to_bv 64 (SRC + 8)) cw x18 (Z_to_bv 64 fl) x20 x21 x22 x23
        (Z_to_bv 64 sh) (Z_to_bv 64 zf) (Z_to_bv 64 8) (Z_to_bv 64 P)).
  Notation x2_fcc := (huf411_kit_x2_l2.x2_fcc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK).

  Ltac meq :=
    first [ reflexivity | (f_equal; lia) | lia | (rewrite ?bvu_mod, ?Zmod_mod; first [reflexivity | lia])
          | lazymatch goal with TLH : 1 <= tl <= 12 |- _ => rewrite ?(neg_dl_sh tl rsv TLH); first [reflexivity | lia] end ].
  Ltac lb_exit :=
    lazymatch goal with
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 ?S1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        eapply (x2_fcc _ (S1 - DST));
        [ dinv_close | unfold x2_bdc; eassumption | assumption | lia | lia
        | intros; first [assumption | unfold x2_pinv in *; lia | exfalso; lia]
        | first [lia | rewrite Z.mod_small by lia; reflexivity]
        | meq | meq | meq | meq | meq ]
    end.
  Ltac lb_kb KB :=
    first [ eapply (KB _ 0); [dinv_close | unfold x2_bdc; eassumption | idtac | idtac | idtac | idtac | idtac | unfold x2_pinv]; lia
          | eapply (KB _ 1); [dinv_close | unfold x2_bdc; eassumption | idtac | idtac | idtac | idtac | idtac | unfold x2_pinv]; lia ].

  Lemma x2_lb_rl : forall mm j p bc bcr P Pr cw pad sh zf (x1 x19 x20 x21 x22 x23 x31 : word),
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 0 <= j <= dcap ->
    p mod 2^64 = (DST + j) mod 2^64 -> bcr mod 2^64 = bc mod 2^64 -> Pr mod 2^64 = P mod 2^64 -> 0 <= bc <= 64 -> PINV P ->
    (forall mm' fl flr bc' bcr' P' Pr' cw' pad' (y18 y20 y21 y22 y23 : word),
        DINV2 mm' -> BDC2 mm' cw' (Z_to_bv 64 bc') pad' (Z_to_bv 64 P') -> (fl = 0 \/ fl = 1) -> flr mod 2^64 = fl mod 2^64 ->
        bcr' mod 2^64 = bc' mod 2^64 -> Pr' mod 2^64 = P' mod 2^64 -> 0 <= bc' <= 64 -> PINV P' ->
        evt usegs POST (BST mm' x1 j bcr' flr Pr' cw' y18 y20 y21 y22 y23 sh zf)) ->
    evt usegs POST (LST 0x2005c mm x1 p bcr Pr cw x19 x20 x21 x22 x23 sh zf x31).
  Proof.
    intros mm j p bc bcr P Pr cw pad sh zf x1 x19 x20 x21 x22 x23 x31 DI BD HN HJ HP HBR HPR HBC HPI KB.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. unfold x2_bdc in BD.
    rewrite (zbv_eqm p _ HP), (zbv_eqm bcr _ HBR), (zbv_eqm Pr _ HPR).
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); lia).
    destruct QR as (q & r & -> & HQ & HR).
    destruct HPI as [-> | (O1 & O2)].
    - Time kx_autoLx [0x201d0] 40%nat
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
         KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47);
         KZRange DT 4096 (2^47); KZWr (SPV + -112) 40; KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
        [(SRC, n); (SPV + -112, 40)].
      all: tp_close.
      all: kx_mem.
      all: lb_kb KB.
    - assert (O : exists off, P = SRC + off) by (exists (P - SRC); lia). destruct O as (off & ->).
      destruct (Z_lt_le_dec off 8) as [C8|C8]; [destruct (Z_lt_le_dec off q) as [CQ|CQ]|].
      3: kx_autoLx [0x201d0] 120%nat
        [KZRange (n - off) 8 (2^32); KZRange off 8 (2^32); KZRange (off - q) 0 (2^32); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
         KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
         KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47);
         KZRange DT 4096 (2^47); KZWr (SPV + -112) 40; KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
        [(SRC, n); (SPV + -112, 40)].
      2: kx_autoLx [0x201d0] 120%nat
        [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange (off - q) 0 7; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
         KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
         KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47);
         KZRange DT 4096 (2^47); KZWr (SPV + -112) 40; KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
        [(SRC, n); (SPV + -112, 40)].
      1: kx_autoLx [0x201d0] 120%nat
        [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange (q - off) 1 8; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
         KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
         KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47);
         KZRange DT 4096 (2^47); KZWr (SPV + -112) 40; KZDisj (SPV + -112) 40 SRC n; KZDisj (SPV + -112) 40 DT 16388]
        [(SRC, n); (SPV + -112, 40)].
      all: tp_close.
      all: kx_mem.
      all: kx_read_ranges.
      all: lb_kb KB.
  Qed.

  Lemma x2_lb_body : forall mm j bc bcr P Pr fl flr cw pad sh zf (x1 x18 x20 x21 x22 x23 : word),
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 0 <= j <= dcap -> (fl = 0 \/ fl = 1) ->
    0 <= bc <= 64 -> PINV P -> sh = 64 - tl ->
    bcr mod 2^64 = bc mod 2^64 -> Pr mod 2^64 = P mod 2^64 -> flr mod 2^64 = fl mod 2^64 ->
    (j + 8 <= dcap -> forall mm' p' bcn bcr' Pr' (y19 y20 y21 y22 y23 y31 : word),
        DINV2 mm' -> BDC2 mm' cw (Z_to_bv 64 bcn) pad (Z_to_bv 64 P) -> j + 4 <= p' - DST <= dcap -> 0 <= bcn <= 64 ->
        bcr' mod 2^64 = bcn mod 2^64 -> Pr' mod 2^64 = P mod 2^64 ->
        evt usegs POST (LST 0x2005c mm' x1 p' bcr' Pr' cw y19 y20 y21 y22 y23 sh zf y31)) ->
    evt usegs POST (BST mm x1 j bcr flr Pr cw x18 x20 x21 x22 x23 sh zf).
  Proof.
    intros mm j bc bcr P Pr fl flr cw pad sh zf x1 x18 x20 x21 x22 x23 DI BD HN HJ HFL HBC HPI HSH HBR HPR HFR KH.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. unfold x2_bdc in BD.
    rewrite (zbv_eqm bcr _ HBR), (zbv_eqm Pr _ HPR), (zbv_eqm flr _ HFR).
    destruct (Z_lt_le_dec (dcap - j) 8) as [SM|BG].
    - clear KH. destruct HFL as [-> | ->].
      all: kx_autoLx [0x203b4] 20%nat
             [KZRange (dcap - j) 0 7; KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
              KZRange (DST + dcap) 4096 (2^47)] (@nil (Z * Z)).
      all: tp_close.
      all: kx_mem.
      all: lb_exit.
    - destruct HFL as [-> | ->].
      + clear KH.
        kx_autoLx [0x203b4] 20%nat
          [KZRange (dcap - j) 8 (2^32); KZRange j 0 (2^32); KZRange dcap 8 (2^32); KZRange DST 4096 (2^47);
           KZRange (DST + dcap) 4096 (2^47)] (@nil (Z * Z)).
        all: tp_close.
        all: kx_mem.
        all: lb_exit.
      + assert (TBL : tbl_in_log usegs mm DT sh 4 7 1 2) by (rewrite HSH; eapply x2_tbl; eassumption).
        Time kx_autoLx [0x2005c; 0x203b4] 200%nat
          [KZRange (dcap - j) 8 (2^32); KZRange j 0 (2^32); KZRange (DST + j) 4096 (2^47 - 8); KZRange dcap 8 (2^32);
           KZRange DST 4096 (2^47); KZRange (DST + dcap) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange bc 0 64;
           KZRange DT 4096 (2^47); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange n 1 (2^32); KZRange sh 52 63;
           KZWr DST dcap; KZWr (SPV + -112) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV + -112) 40;
           KZDisj (SPV + -112) 40 DT 16388; KZDisj DST dcap SRC n; KZDisj (SPV + -112) 40 SRC n; KZTblLog DT sh 4 7 1 2]
          [(DT, 16388); (SPV + -112, 40)].
        all: tp_close.
        Time all: kx_ev_ranges; kx_mem; kx_strip_mod.
        all: kx_read_ranges.
        all: lazymatch goal with
             | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2005c) _ _ _ _) =>
                 eapply KH; [lia | dinv_close | unfold x2_bdc; eassumption | lia | lia | meq | meq]
             | |- evt _ _ (MS _ _ (Z_to_bv 64 0x203b4) _ _ _ _) => lb_exit
             end.
  Qed.

  Lemma x2_lb_loop : forall (k : nat) mm j p bc bcr P Pr cw pad sh zf (x1 x19 x20 x21 x22 x23 x31 : word),
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 0 <= j <= dcap -> dcap - j <= Z.of_nat k ->
    p mod 2^64 = (DST + j) mod 2^64 -> bcr mod 2^64 = bc mod 2^64 -> Pr mod 2^64 = P mod 2^64 -> 0 <= bc <= 64 -> PINV P ->
    sh = 64 - tl ->
    evt usegs POST (LST 0x2005c mm x1 p bcr Pr cw x19 x20 x21 x22 x23 sh zf x31).
  Proof.
    induction k as [|k IH]; intros mm j p bc bcr P Pr cw pad sh zf x1 x19 x20 x21 x22 x23 x31 DI BD HN HJ HK HP HBR HPR HBC HPI HSH.
    all: eapply x2_lb_rl; [exact DI | exact BD | exact HN | exact HJ | exact HP | exact HBR | exact HPR | exact HBC | exact HPI |].
    all: intros mm' fl flr bc' bcr' P' Pr' cw' pad' y18 y20 y21 y22 y23 DI' BD' HFL HFR HBR' HPR' HBC' HPI'.
    all: eapply x2_lb_body;
           [exact DI' | exact BD' | exact HN | exact HJ | exact HFL | exact HBC' | exact HPI' | exact HSH | exact HBR' | exact HPR' | exact HFR |].
    - intros HR. exfalso. lia.
    - intros HR mm'' p' bcn bcr'' Pr'' z19 z20 z21 z22 z23 z31 DI'' BD'' HJ' HBCN HBR'' HPR''.
      eapply (IH _ (p' - DST));
        [exact DI'' | exact BD'' | exact HN | lia | lia | f_equal; lia | exact HBR'' | exact HPR'' | exact HBCN | exact HPI' | exact HSH].
  Qed.

  Lemma x2_lb_head : forall mm cw bc P pad (x1 x19 x20 x21 x22 x23 x31 : word)
                       (e5 e6 e7 e9 e10 e11 e12 e13 e14 e15 e16 e18 e28 e29 e30 : Z),
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 0 <= bc <= 64 -> PINV P ->
    e5 mod 2^64 = (dcap + DST + -7) mod 2^64 -> e6 mod 2^64 = (-1 * DT + -5) mod 2^64 -> e7 mod 2^64 = 65 mod 2^64 ->
    e9 mod 2^64 = DST mod 2^64 -> e10 mod 2^64 = (DT + 4) mod 2^64 -> e11 mod 2^64 = (DST + dcap) mod 2^64 ->
    e12 mod 2^64 = 2305843009213693952 mod 2^64 -> e13 mod 2^64 = (tl + 256 * rsv) mod 2^64 -> e14 mod 2^64 = bc mod 2^64 ->
    e15 mod 2^64 = SRC mod 2^64 -> e16 mod 2^64 = (SRC + 8) mod 2^64 -> e18 mod 2^64 = P mod 2^64 ->
    e28 mod 2^64 = (64 - tl) mod 2^64 -> e30 mod 2^64 = 8 mod 2^64 ->
    evt usegs POST (ST 0x2005c mm x1 (Z_to_bv 64 e5) (Z_to_bv 64 e6) (Z_to_bv 64 e7) (Z_to_bv 64 e9) (Z_to_bv 64 e10)
                      (Z_to_bv 64 e11) (Z_to_bv 64 e12) (Z_to_bv 64 e13) (Z_to_bv 64 e14) (Z_to_bv 64 e15) (Z_to_bv 64 e16) cw
                      (Z_to_bv 64 e18) x19 x20 x21 x22 x23 (Z_to_bv 64 e28) (Z_to_bv 64 e29) (Z_to_bv 64 e30) x31).
  Proof.
    intros mm cw bc P pad x1 x19 x20 x21 x22 x23 x31 e5 e6 e7 e9 e10 e11 e12 e13 e14 e15 e16 e18 e28 e29 e30
      DI BD HN HBC HPI H5 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H18 H28 H30.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    rewrite (zbv_eqm _ _ H5), (zbv_eqm _ _ H6), (zbv_eqm _ _ H7), (zbv_eqm _ _ H10), (zbv_eqm _ _ H11), (zbv_eqm _ _ H12),
            (zbv_eqm _ _ H13), (zbv_eqm _ _ H15), (zbv_eqm _ _ H16), (zbv_eqm _ _ H28), (zbv_eqm _ _ H30).
    clear H5 H6 H7 H10 H11 H12 H13 H15 H16 H28 H30.
    eapply (x2_lb_loop (Z.to_nat dcap) mm 0 e9 bc e14 P e18);
      [exact DI | exact BD | exact HN | clear - R1; lia | clear - R1; lia | rewrite Z.add_0_r; exact H9 | exact H14 | exact H18
      | exact HBC | exact HPI | reflexivity].
  Qed.

  Lemma x2_lb_entry : forall mm cw cwr bc P pad (x1 x5 x6 x7 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word)
                        (e9 e10 e11 e12 e13 e14 e15 e16 : Z),
    DINV2 mm -> BDC2 mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> cwr = cw -> 0 <= bc <= 64 -> PINV P ->
    e9 mod 2^64 = DST mod 2^64 -> e10 mod 2^64 = (DT + 4) mod 2^64 -> e11 mod 2^64 = (DST + dcap) mod 2^64 ->
    e12 mod 2^64 = 2^61 -> e13 mod 2^64 = (tl + 256 * rsv) mod 2^64 -> e14 mod 2^64 = bc mod 2^64 ->
    e15 mod 2^64 = SRC mod 2^64 -> e16 mod 2^64 = (SRC + 8) mod 2^64 ->
    evt usegs POST (ST 0x20034 mm x1 x5 x6 x7 (Z_to_bv 64 e9) (Z_to_bv 64 e10) (Z_to_bv 64 e11) (Z_to_bv 64 e12)
                       (Z_to_bv 64 e13) (Z_to_bv 64 e14) (Z_to_bv 64 e15) (Z_to_bv 64 e16) cwr x18 x19 x20 x21 x22 x23
                       x28 x29 x30 x31).
  Proof.
    intros mm cw cwr bc P pad x1 x5 x6 x7 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 e9 e10 e11 e12 e13 e14 e15 e16
      DI BD HN HCW HBC HPI H9 H10 H11 H12 H13 H14 H15 H16.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA. subst cwr.
    pose proof DI as DI'. dinv_open DI'. unfold x2_bdc in BD.
    rewrite (zbv_eqm _ _ H9), (zbv_eqm _ _ H10), (zbv_eqm _ _ H11), (zbv_eqm e12 2305843009213693952 ltac:(rewrite H12; reflexivity)),
            (zbv_eqm _ _ H13), (zbv_eqm _ _ H14), (zbv_eqm _ _ H15), (zbv_eqm _ _ H16).
    clear H9 H10 H11 H12 H13 H14 H15 H16.
    Time kx_autoLx [0x2005c] 30%nat
      [KZRange bc 0 64; KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange (DST + dcap) 4096 (2^47);
       KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255; KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
       KZWr (SPV + -112) 40]
      [(SPV + -112, 40)].
    all: tp_close.
    all: kx_mem.
    all: eapply x2_lb_head;
           [dinv_close | unfold x2_bdc; eassumption | exact HN | exact HBC | exact HPI
           | meq | meq | meq | meq | meq | meq | meq | meq | meq | meq | meq | meq | meq | meq].
  Qed.

End X2LB.
