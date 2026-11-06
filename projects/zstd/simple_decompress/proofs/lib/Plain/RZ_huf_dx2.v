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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX2.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis LO : 4096 <= lo /\ lo <= SPV - 48.
  Hypothesis SPB : SPV < 2^47.
  Hypothesis SL : zlen src = n.
  Hypothesis DL : zlen dtb = 16388.
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis R1 : 4096 <= DST /\ 0 <= dcap < 2^32 /\ DST + dcap < 2^47.
  Hypothesis R2 : 4096 <= SRC /\ n < 2^32 /\ SRC + n < 2^47.
  Hypothesis R3 : 4096 <= DT /\ DT + 16388 < 2^47.
  Hypothesis OS1 : DST + dcap <= lo \/ SPV <= DST.
  Hypothesis OS2 : SRC + n <= lo \/ SPV <= SRC.
  Hypothesis OS3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis DJ1 : DST + dcap <= SRC \/ SRC + n <= DST.
  Hypothesis DJ2 : DST + dcap <= DT \/ DT + 16388 <= DST.
  Hypothesis X2OK : huf_x2_ok dtb tl.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 48 [] m0 huf_noQ).
  (* [comment removed for export] *)
  Notation DINV := (RZ_huf_dx1.DINV s0 s1 s2 s3 s4 s5 m0 SPV DST dcap SRC DT lo src dtb).

  Ltac dinv_open DI :=
    let OUT := fresh "OUT" in
    destruct DI as (OUT & FR & STK & SRCB & DTB & MU & WM & MI).
  Ltac dinv_close := unfold RZ_huf_dx1.DINV; repeat (split; [eassumption|]); eassumption.

  (* [comment removed for export] *)
  Lemma x2_tbl : forall mm, bytes_at psegs mm DT dtb -> tbl_in_log psegs mm DT (64 - tl) 4 7 1 2.
  Proof.
    intros mm DTB. apply (tbl_in_log_bytes_at psegs mm DT dtb (64 - tl) 4 7 1 2 DTB); [lia | lia |].
    intros i Hi. replace (64 - (64 - tl)) with tl in Hi by lia. exact (X2OK i Hi).
  Qed.

  Notation STpc pc mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 (SPV + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  (* [comment removed for export] *)
  Lemma x2_end : forall mm (x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV mm ->
    evt psegs POST (STpc 0x1e234 mm x5 x6 x7 x8 x9 x10 (Z_to_bv 64 dcap) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mm x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 DI.
    dinv_open DI.
    kx_autoLx [] 30%nat [KZRange SPV 4096 (2^47); KZRange dcap 0 (2^32)] [(SPV - 48, 48)].
    all: kx_mem.
    all: zstep.
    all: release_frame FR STK SPV.
    all: apply evt_done; unfold huf_dec_post; repeat (lazymatch goal with |- ex _ => eexists end).
    all: (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact STK|]);
         (split; [exact OUT|]); (split; [|split; [clear - R1; lia|exact I]]).
    all: first [left; reflexivity | right; vm_compute; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_last_b : forall mm idx (x5 x6 x7 x8 x9 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV mm -> 0 <= idx <= 4095 ->
    evt psegs POST (STpc 0x1e200 mm x5 x6 x7 x8 x9 x10 (Z_to_bv 64 dcap) x12 (Z_to_bv 64 (DT + 4 + 4 * idx)) x14 x15 x16 x17
                         x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mm idx x5 x6 x7 x8 x9 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 DI HI.
    pose proof DI as DI'. dinv_open DI'.
    kx_autoLx [0x1e234] 30%nat [KZRange idx 0 4095; KZRange DT 4096 (2^47)] [(DT, 16388)].
    all: apply x2_end; exact DI.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_last : forall mm j dl (x5 x6 x7 x8 x9 x12 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV mm -> 0 <= j <= dcap -> dl = tl + 256 * rsv ->
    evt psegs POST (STpc 0x1e1e0 mm x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 dcap) x12 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dl)
                         (Z_to_bv 64 (DST + dcap)) x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mm j dl x5 x6 x7 x8 x9 x12 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 DI HJ HDL.
    dinv_open DI.
    destruct (Z_lt_le_dec j dcap) as [ROOM|FULL]; cycle 1.
    - kx_autoLx [0x1e234] 10%nat [KZRange (j - dcap) 0 (2^32); KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)] (@nil (Z * Z)).
      apply x2_end. dinv_close.
    - (* [comment removed for export] *)
      subst dl.
      assert (TLC : tl = 1 \/ tl = 2 \/ tl = 3 \/ tl = 4 \/ tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9 \/ tl = 10 \/ tl = 11 \/ tl = 12) by lia.
      Time repeat (destruct TLC as [TLC|TLC]); rewrite TLC;
        kx_autoLx [0x1e200] 40%nat
          [KZRange (dcap - j) 1 (2^32); KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47);
           KZRange rsv 0 255; KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 48) 48; KZRange SPV 4096 (2^47)]
          [(DT, 16388)].
      all: kx_mem.
      all: match goal with |- context [DT + 4 * ?q + 4] =>
             replace (DT + 4 * q + 4) with (DT + 4 + 4 * q) by lia; apply x2_last_b; [dinv_close | kx_lia] end.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_tail : forall (k : nat) mm j dl sh (x6 x8 x9 x12 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV mm -> dcap - j <= Z.of_nat k -> 0 <= j -> j + 2 <= dcap -> dl = tl + 256 * rsv -> sh = 64 - tl ->
    evt psegs POST (STpc 0x1e1a8 mm (Z_to_bv 64 (DST + dcap - 2)) x6 (Z_to_bv 64 sh) x8 x9 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 dcap) x12
                         (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap)) x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros mm j dl sh x6 x8 x9 x12 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 DI HK HJ0 HJ HDL HSH;
      [exfalso; lia|].
    dinv_open DI.
    assert (TBL : tbl_in_log psegs mm DT sh 4 7 1 2) by (rewrite HSH; apply x2_tbl; exact DTB).
    Time kx_autoLx [0x1e1a8; 0x1e1e0] 40%nat
      [KZRange (dcap - j) 2 (2^32); KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47);
       KZRange dl 0 65535; KZRange sh 52 63; KZRange SPV 4096 (2^47);
       KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 48) 48; KZTblLog DT sh 4 7 1 2]
      [(DT, 16388)].
    all: kx_ev_ranges; kx_mem; kx_strip_mod.
    - eapply IH; [dinv_close | lia | lia | lia | exact HDL | exact HSH].
    - eapply x2_last; [dinv_close | lia | exact HDL].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_0d8 : forall mm j dl sh (x6 x8 x9 x12 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV mm -> 0 <= j <= dcap -> dl = tl + 256 * rsv -> sh = 64 - tl ->
    evt psegs POST (STpc 0x1e1a4 mm (Z_to_bv 64 (DST + dcap - 2)) x6 (Z_to_bv 64 sh) x8 x9 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 dcap) x12
                         (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap)) x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mm j dl sh x6 x8 x9 x12 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 DI HJ HDL HSH.
    kx_autoLx [0x1e1a8; 0x1e1e0] 10%nat
      [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)] (@nil (Z * Z)).
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 123304) _ _ _ _) =>
             eapply (x2_tail (Z.to_nat dcap)); [exact DI | lia | lia | lia | exact HDL | exact HSH]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 123360) _ _ _ _) => eapply x2_last; [exact DI | lia | exact HDL]
         end.
  Qed.

  (* [comment removed for export] *)
  Definition OINV (off : Z) : Prop := off = 0 \/ (1 <= off /\ off + 8 <= n).

  Notation L2ST mm j dl sh off bc x8 x9 x17 x18 x19 x20 x21 x28 x31 :=
    (STpc 0x1e0c4 mm (Z_to_bv 64 (DST + dcap - 2)) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 sh) x8 x9 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 dcap)
          (Z_to_bv 64 SRC) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 bc) x17 x18 x19 x20 x21
          x28 (Z_to_bv 64 64) (Z_to_bv 64 (SRC + 8)) x31).

  Ltac x2_l2_kzs ROOM OFF :=
    lazymatch goal with
    | TBL : tbl_in_log psegs _ DT ?sh 4 7 1 2 |- evt _ _ (MS (mkR _ _ _ _ _ (Z_to_bv 64 (SRC + ?off)) _ _ _ (Z_to_bv 64 (DST + ?j)) _ _ _
                                                            (Z_to_bv 64 ?dl) _ (Z_to_bv 64 ?bc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        kx_autoLx [0x1e0c4; 0x1e1a4] 100%nat
          [ROOM; KZRange (n - off) 8 (2^32); OFF; KZRange bc 0 64; KZRange n 9 (2^32);
           KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535; KZRange SPV 4096 (2^47);
           KZRange SRC 4096 (2^47); KZRange DT 4096 (2^47); KZRange sh 52 63; KZRange (SRC + n) 4096 (2^47);
           KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap SRC n; KZDisj DST dcap (SPV - 48) 48; KZTblLog DT sh 4 7 1 2]
          [(DT, 16388); (SRC, n)]
    end.

  (* [comment removed for export] *)
  Lemma x2_loop2_full : forall mm j dl sh off bc (x8 x9 x17 x18 x19 x20 x21 x28 x31 : word),
    DINV mm -> 0 <= j <= dcap -> (dcap - j < 2 \/ off = 0) -> dl = tl + 256 * rsv -> sh = 64 - tl -> OINV off -> 0 <= bc <= 64 ->
    evt psegs POST (L2ST mm j dl sh off bc x8 x9 x17 x18 x19 x20 x21 x28 x31).
  Proof.
    intros mm j dl sh off bc x8 x9 x17 x18 x19 x20 x21 x28 x31 DI HJ HF HDL HSH HO HB.
    pose proof DI as DI'; dinv_open DI'.
    assert (TBL : tbl_in_log psegs mm DT sh 4 7 1 2) by (rewrite HSH; apply x2_tbl; exact DTB).
    destruct HO as [-> | (O1 & O2)].
    - kx_autoLx [0x1e0c4; 0x1e1a4] 20%nat [KZRange SRC 4096 (2^47)] (@nil (Z * Z)).
      eapply x2_0d8; [exact DI | lia | exact HDL | exact HSH].
    - destruct HF as [HF | ->]; [|exfalso; lia].
      destruct (Z_lt_le_dec off 8) as [O8|O8].
      + Time x2_l2_kzs (KZRange (dcap - j) 0 1) (KZRange off 1 7).
        all: eapply x2_0d8; [exact DI | lia | exact HDL | exact HSH].
      + Time x2_l2_kzs (KZRange (dcap - j) 0 1) (KZRange off 8 (2^32)).
        all: eapply x2_0d8; [exact DI | lia | exact HDL | exact HSH].
  Qed.

  Lemma x2_loop2 : forall (k : nat) mm j dl sh off bc (x8 x9 x17 x18 x19 x20 x21 x28 x31 : word),
    DINV mm -> dcap - j <= Z.of_nat k -> 0 <= j <= dcap -> dl = tl + 256 * rsv -> sh = 64 - tl -> OINV off -> 0 <= bc <= 64 ->
    evt psegs POST (L2ST mm j dl sh off bc x8 x9 x17 x18 x19 x20 x21 x28 x31).
  Proof.
    induction k as [|k IH]; intros mm j dl sh off bc x8 x9 x17 x18 x19 x20 x21 x28 x31 DI HK HJ HDL HSH HO HB.
    { apply x2_loop2_full; try assumption. left; lia. }
    destruct (Z_lt_le_dec (dcap - j) 2) as [SM|ROOM]; [apply x2_loop2_full; try assumption; left; lia|].
    destruct HO as [-> | (O1 & O2)]; [apply x2_loop2_full; try assumption; [right; reflexivity | left; reflexivity]|].
    pose proof DI as DI'; dinv_open DI'.
    assert (TBL : tbl_in_log psegs mm DT sh 4 7 1 2) by (rewrite HSH; apply x2_tbl; exact DTB).
    destruct (Z_lt_le_dec off 8) as [O8|O8].
    - x2_l2_kzs (KZRange (dcap - j) 2 (2^32)) (KZRange off 1 7).
      all: kx_ev_ranges; kx_mem; rewrite ?(Z.mod_small bc (2^64)) in * by lia; kx_land_ranges; kx_strip_mod.
      all: lazymatch goal with
           | |- evt _ _ (MS _ _ (Z_to_bv 64 123300) _ _ _ _) => eapply x2_0d8; [dinv_close | lia | exact HDL | exact HSH]
           | |- evt _ _ (MS _ _ (Z_to_bv 64 123076) _ _ _ _) =>
               eapply IH; [dinv_close | lia | lia | exact HDL | exact HSH | unfold OINV; lia | lia]
           end.
    - x2_l2_kzs (KZRange (dcap - j) 2 (2^32)) (KZRange off 8 (2^32)).
      all: kx_ev_ranges; kx_mem; rewrite ?(Z.mod_small bc (2^64)) in * by lia; kx_land_ranges; kx_strip_mod.
      all: lazymatch goal with
           | |- evt _ _ (MS _ _ (Z_to_bv 64 123300) _ _ _ _) => eapply x2_0d8; [dinv_close | lia | exact HDL | exact HSH]
           | |- evt _ _ (MS _ _ (Z_to_bv 64 123076) _ _ _ _) =>
               eapply IH; [dinv_close | lia | lia | exact HDL | exact HSH | unfold OINV; lia | lia]
           end.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_fcc : forall mm j dl bc (x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV mm -> 0 <= j <= dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2^64 ->
    (bc <= 64 -> exists off, x6 = Z_to_bv 64 (SRC + off) /\ OINV off) ->
    evt psegs POST (STpc 0x1e098 mm x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 (DT + 4))
                         (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 bc) x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mm j dl bc x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x28 x29 x30 x31 DI HJ HDL HB HP.
    destruct (Z_le_gt_dec bc 64) as [B64|B64].
    - destruct (HP B64) as (off & -> & HO).
      kx_autoLx [0x1e0c4; 0x1e1e0; 0x1e1a4] 30%nat
        [KZRange bc 0 64; KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535; KZRange SRC 4096 (2^47)]
        (@nil (Z * Z)).
      all: subst dl; rewrite ?(neg_dl_sh tl rsv TL).
      all: lazymatch goal with
           | |- evt _ _ (MS _ _ (Z_to_bv 64 123360) _ _ _ _) => eapply x2_last; [exact DI | lia | reflexivity]
           | |- evt _ _ (MS _ _ (Z_to_bv 64 123076) _ _ _ _) =>
               replace (DST + dcap + -2) with (DST + dcap - 2) by lia;
               eapply (x2_loop2 (Z.to_nat dcap)); [exact DI | lia | lia | reflexivity | reflexivity | exact HO | lia]
           end.
    - kx_autoLx [0x1e0c4; 0x1e1e0; 0x1e1a4] 30%nat
        [KZRange bc 65 (2^64 - 1); KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535]
        (@nil (Z * Z)).
      all: subst dl; rewrite ?(neg_dl_sh tl rsv TL).
      all: lazymatch goal with
           | |- evt _ _ (MS _ _ (Z_to_bv 64 123360) _ _ _ _) => eapply x2_last; [exact DI | lia | reflexivity]
           | |- evt _ _ (MS _ _ (Z_to_bv 64 123300) _ _ _ _) =>
               replace (DST + dcap + -2) with (DST + dcap - 2) by lia;
               eapply x2_0d8; [exact DI | lia | reflexivity | reflexivity]
           end.
  Qed.

  (* [comment removed for export] *)
  Definition LINV (off bc : Z) : Prop := off = 0 \/ (1 <= off /\ off + 8 <= n /\ bc <= 64).

  Notation LST pc lim mm j dl sh off bc x6 x8 x9 x17 x18 x19 x20 x21 :=
    (STpc pc mm (Z_to_bv 64 off) x6 (Z_to_bv 64 sh) x8 x9 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC)
          (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 bc) x17 x18 x19 x20 x21
          (Z_to_bv 64 0x11320) (Z_to_bv 64 (DST + dcap - lim)) (Z_to_bv 64 8) (Z_to_bv 64 64)).

  Ltac x2_lp_kzs HEAD ROOM :=
    lazymatch goal with
    | TBL : tbl_in_log psegs _ DT ?sh 4 7 1 2 |- evt _ _ (MS (mkR _ _ _ _ (Z_to_bv 64 ?off) _ _ _ _ (Z_to_bv 64 (DST + ?j)) _ _ _
                                                            (Z_to_bv 64 ?dl) _ (Z_to_bv 64 ?bc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        kx_autoLx [HEAD; 0x1e098] 200%nat
          [ROOM; KZRange (n - off) 8 (2^32); KZRange off 1 (2^32); KZRange bc 0 64; KZRange n 9 (2^32);
           KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535; KZRange SPV 4096 (2^47);
           KZRange SRC 4096 (2^47); KZRange DT 4096 (2^47); KZRange sh 52 63; KZRange (SRC + n) 4096 (2^47);
           KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap SRC n; KZDisj DST dcap (SPV - 48) 48; KZTblLog DT sh 4 7 1 2]
          [(DT, 16388); (SRC, n)]
    end.

  (* [comment removed for export] *)
  Ltac x2_to_fcc DI HDL :=
    eapply x2_fcc; [exact DI || dinv_close | lia | exact HDL | lia |
                    let B := fresh "B" in intro B;
                    first [ exfalso; lia
                          | lazymatch goal with
                            | |- exists o, Z_to_bv 64 ?X = Z_to_bv 64 (SRC + o) /\ _ =>
                                exists (X - SRC); split; [f_equal; lia | unfold OINV; lia]
                            end ] ].

  Lemma x2_loop5_off0 : forall mm j dl sh bc (x6 x8 x9 x17 x18 x19 x20 x21 : word),
    DINV mm -> 0 <= j <= dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2^64 ->
    evt psegs POST (LST 0x1dc70 9 mm j dl sh 0 bc x6 x8 x9 x17 x18 x19 x20 x21).
  Proof.
    intros mm j dl sh bc x6 x8 x9 x17 x18 x19 x20 x21 DI HJ HDL HB.
    kx_autoLx [0x1dc70; 0x1e098] 20%nat [KZRange SRC 4096 (2^47)] (@nil (Z * Z)).
    x2_to_fcc DI HDL.
  Qed.

  Ltac x2_lp_leaves HEAD IH DI HDL HSH :=
    kx_ev_ranges; kx_mem;
    repeat match goal with |- context [?z mod 2^64] => rewrite (Z.mod_small z (2^64)) by lia end;
    repeat match goal with H : context [?z mod 2^64] |- _ => rewrite (Z.mod_small z (2^64)) in H by lia end;
    kx_land_ranges; kx_strip_mod;
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 123032) _ _ _ _) => x2_to_fcc DI HDL
    | |- evt _ _ (MS _ _ (Z_to_bv 64 HEAD) _ _ _ _) =>
        eapply IH; first [dinv_close | exact HDL | exact HSH | lia | (unfold LINV; lia)]
    end.

  Lemma x2_loop5_small : forall mm j dl sh off bc (x6 x8 x9 x17 x18 x19 x20 x21 : word),
    DINV mm -> 0 <= j <= dcap -> dcap - j < 10 -> dl = tl + 256 * rsv -> sh = 64 - tl -> 0 <= bc < 2^64 -> LINV off bc ->
    evt psegs POST (LST 0x1dc70 9 mm j dl sh off bc x6 x8 x9 x17 x18 x19 x20 x21).
  Proof.
    intros mm j dl sh off bc x6 x8 x9 x17 x18 x19 x20 x21 DI HJ SM HDL HSH HB INV.
    destruct INV as [-> | (O1 & O2 & B1)]; [apply x2_loop5_off0; assumption|].
    pose proof DI as DI'; dinv_open DI'.
    assert (TBL : tbl_in_log psegs mm DT sh 4 7 1 2) by (rewrite HSH; apply x2_tbl; exact DTB).
    x2_lp_kzs 0x1dc70 (KZRange (dcap - j) 0 9).
    all: x2_lp_leaves 0x1dc70 x2_loop5_off0 DI HDL HSH.
  Qed.

  Lemma x2_loop5 : forall (k : nat) mm j dl sh off bc (x6 x8 x9 x17 x18 x19 x20 x21 : word),
    DINV mm -> dcap - j <= Z.of_nat k -> 0 <= j <= dcap -> dl = tl + 256 * rsv -> sh = 64 - tl -> 0 <= bc < 2^64 -> LINV off bc ->
    evt psegs POST (LST 0x1dc70 9 mm j dl sh off bc x6 x8 x9 x17 x18 x19 x20 x21).
  Proof.
    induction k as [|k IH]; intros mm j dl sh off bc x6 x8 x9 x17 x18 x19 x20 x21 DI HK HJ HDL HSH HB INV.
    { apply x2_loop5_small; try assumption; lia. }
    destruct (Z_lt_le_dec (dcap - j) 10) as [SM|ROOM]; [apply x2_loop5_small; try assumption; lia|].
    destruct INV as [-> | (O1 & O2 & B1)]; [apply x2_loop5_off0; assumption|].
    pose proof DI as DI'; dinv_open DI'.
    assert (TBL : tbl_in_log psegs mm DT sh 4 7 1 2) by (rewrite HSH; apply x2_tbl; exact DTB).
    x2_lp_kzs 0x1dc70 (KZRange (dcap - j) 10 (2^32)).
    all: x2_lp_leaves 0x1dc70 IH DI HDL HSH.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_loop4_off0 : forall mm j dl sh bc (x6 x8 x9 x17 x18 x19 x20 x21 : word),
    DINV mm -> 0 <= j <= dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2^64 ->
    evt psegs POST (LST 0x1debc 7 mm j dl sh 0 bc x6 x8 x9 x17 x18 x19 x20 x21).
  Proof.
    intros mm j dl sh bc x6 x8 x9 x17 x18 x19 x20 x21 DI HJ HDL HB.
    kx_autoLx [0x1debc; 0x1e098] 20%nat [KZRange SRC 4096 (2^47)] (@nil (Z * Z)).
    x2_to_fcc DI HDL.
  Qed.

  Lemma x2_loop4_small : forall mm j dl sh off bc (x6 x8 x9 x17 x18 x19 x20 x21 : word),
    DINV mm -> 0 <= j <= dcap -> dcap - j < 8 -> dl = tl + 256 * rsv -> sh = 64 - tl -> 0 <= bc < 2^64 -> LINV off bc ->
    evt psegs POST (LST 0x1debc 7 mm j dl sh off bc x6 x8 x9 x17 x18 x19 x20 x21).
  Proof.
    intros mm j dl sh off bc x6 x8 x9 x17 x18 x19 x20 x21 DI HJ SM HDL HSH HB INV.
    destruct INV as [-> | (O1 & O2 & B1)]; [apply x2_loop4_off0; assumption|].
    pose proof DI as DI'; dinv_open DI'.
    assert (TBL : tbl_in_log psegs mm DT sh 4 7 1 2) by (rewrite HSH; apply x2_tbl; exact DTB).
    x2_lp_kzs 0x1debc (KZRange (dcap - j) 0 7).
    all: x2_lp_leaves 0x1debc x2_loop4_off0 DI HDL HSH.
  Qed.

  Lemma x2_loop4 : forall (k : nat) mm j dl sh off bc (x6 x8 x9 x17 x18 x19 x20 x21 : word),
    DINV mm -> dcap - j <= Z.of_nat k -> 0 <= j <= dcap -> dl = tl + 256 * rsv -> sh = 64 - tl -> 0 <= bc < 2^64 -> LINV off bc ->
    evt psegs POST (LST 0x1debc 7 mm j dl sh off bc x6 x8 x9 x17 x18 x19 x20 x21).
  Proof.
    induction k as [|k IH]; intros mm j dl sh off bc x6 x8 x9 x17 x18 x19 x20 x21 DI HK HJ HDL HSH HB INV.
    { apply x2_loop4_small; try assumption; lia. }
    destruct (Z_lt_le_dec (dcap - j) 8) as [SM|ROOM]; [apply x2_loop4_small; try assumption; lia|].
    destruct INV as [-> | (O1 & O2 & B1)]; [apply x2_loop4_off0; assumption|].
    pose proof DI as DI'; dinv_open DI'.
    assert (TBL : tbl_in_log psegs mm DT sh 4 7 1 2) by (rewrite HSH; apply x2_tbl; exact DTB).
    x2_lp_kzs 0x1debc (KZRange (dcap - j) 8 (2^32)).
    all: x2_lp_leaves 0x1debc IH DI HDL HSH.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_fcc_p : forall mm p pe dl bc (x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV mm -> DST <= p <= DST + dcap -> pe = DST + dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2^64 ->
    (bc <= 64 -> exists off, x6 = Z_to_bv 64 (SRC + off) /\ OINV off) ->
    evt psegs POST (STpc 0x1e098 mm x5 x6 x7 x8 x9 (Z_to_bv 64 p) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 (DT + 4))
                         (Z_to_bv 64 dl) (Z_to_bv 64 pe) (Z_to_bv 64 bc) x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mm p pe dl bc x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x28 x29 x30 x31 DI HP PE HDL HB HX.
    subst pe. replace p with (DST + (p - DST)) by lia. apply x2_fcc; [exact DI | lia | exact HDL | exact HB | exact HX].
  Qed.

End DX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition x2_ctx (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte) : Prop :=
  x1_ctx SPV DST dcap SRC n DT tl rsv lo src dtb /\ huf_x2_ok dtb tl.

Ltac x2_ctx_open CTX :=
  let X2OK := fresh "X2OK" in let C1 := fresh "C1" in
  destruct CTX as (C1 & X2OK); x1_ctx_open C1.

Section DX2C.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x2_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.

  Definition x2_loop5_c := ltac:(x2_ctx_open CTX;
    exact (x2_loop5 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb
                    LO SPB SL DL TL RSV R1 R2 R3 OS1 OS2 OS3 DJ1 DJ2 X2OK)).
  Definition x2_loop4_c := ltac:(x2_ctx_open CTX;
    exact (x2_loop4 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb
                    LO SPB SL DL TL RSV R1 R2 R3 OS1 OS2 OS3 DJ1 DJ2 X2OK)).
  Definition x2_fcc_p_c := ltac:(x2_ctx_open CTX;
    exact (x2_fcc_p ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb
                    LO SPB SL DL TL RSV R1 R2 R3 OS1 OS2 OS3 DJ1 DJ2 X2OK)).
End DX2C.
