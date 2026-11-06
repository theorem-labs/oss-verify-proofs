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

Section DX41.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis LO : 4096 <= lo /\ lo <= SPV - 432.
  Hypothesis SPB : SPV < 2^47.
  Hypothesis R1 : 4096 <= DST /\ 0 <= dcap < 2^32 /\ DST + dcap < 2^47.
  Hypothesis OS1 : DST + dcap <= lo \/ SPV <= DST.
  Hypothesis DL : zlen dtb = 16388.
  Hypothesis R3 : 4096 <= DT /\ DT + 16388 < 2^47.
  Hypothesis DJ2 : DST + dcap <= DT \/ DT + 16388 <= DST.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 432 [] m0 huf_noQ).

  (* [comment removed for export] *)
  Definition EINV (mm : fmem) : Prop :=
    stk psegs mm DST (DST + dcap) /\
    rw_cells psegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    stk psegs mm lo (SPV + -104) /\
    munch [(DST, DST + dcap); (SPV - 432, SPV)] m0 mm /\ wmono psegs m0 mm /\ mem_inv psegs mm.

  (* [comment removed for export] *)
  Lemma x41_ret : forall mm r (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EINV mm -> (r = dcap \/ (zd_is_error r = true /\ r < 2^64)) ->
    evt psegs POST (MS (mkR x1 (Z_to_bv 64 (SPV + -416)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                            x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x23454) fc None mm (seg_rom psegs)).
  Proof.
    intros mm r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 EI HR.
    destruct EI as (OUT & FR & STK & MU & WM & MI).
    kx_autoLx [] 30%nat [KZRange SPV 4096 (2^47)] [(SPV - 104, 104)].
    kx_mem. zstep. release_frame FR STK SPV.
    apply evt_done; unfold huf_dec_post; repeat (lazymatch goal with |- ex _ => eexists end).
    (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact STK|]);
      (split; [exact OUT|]); (split; [|split; [|exact I]]).
    - destruct HR as [HR|[HR _]]; [left; exact HR | right; exact HR].
    - destruct HR as [->|[HR1 HR2]]; [clear - R1; lia|]. unfold zd_is_error, ZE_maxCode in HR1. apply Z.ltb_lt in HR1. clear - HR1 HR2. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -416)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  (* [comment removed for export] *)
  Lemma x41_t1 : forall (k : nat) mb mm j c sh
      (x1 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    c <= Z.of_nat k -> 1 <= c -> 0 <= j -> j + c <= dcap -> 52 <= sh <= 63 ->
    (forall mm' (y11 y13 y19 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        evt psegs POST (ST 0x235dc mm' x1 (Z_to_bv 64 (DST + (j + c))) (Z_to_bv 64 0) x7 x8 x9 x10 y11 x12 y13 x14 x15 (Z_to_bv 64 sh) x17
                           (Z_to_bv 64 (DT + 4)) y19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)) ->
    evt psegs POST (ST 0x235b0 mm x1 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 c) x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 sh) x17
                       (Z_to_bv 64 (DT + 4)) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros mb mm j c sh x1 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      MU WM MI OUT DTB HK HC HJ HJC HSH K; [exfalso; lia|].
    kx_autoLx [0x235b0; 0x235dc] 30%nat
      [KZRange (dcap - j) 1 (2^32); KZRange j 0 (2^32); KZRange c 1 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
       KZRange DT 4096 (2^47); KZRange sh 52 63; KZWr DST dcap; KZDisj DST dcap DT 16388]
      [(DT, 16388)].
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 144816) _ _ _ _) =>
             replace (DST + j + 1) with (DST + (j + 1)) by lia;
             eapply (IH mb _ (j + 1) (c + -1) sh); try eassumption; try lia;
             intros; replace (j + 1 + (c + -1)) with (j + c) by lia; eapply K; eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 144860) _ _ _ _) =>
             replace (DST + j + 1) with (DST + (j + c)) by lia; replace (c + -1) with 0 by lia;
             eapply K; eassumption
         end.
  Qed.

  (* [comment removed for export] *)
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 :=
    (rw_cells psegs mm (SPV + -416) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16; C8 w17; C8 w18; C8 w19]).

  (* [comment removed for export] *)
  Ltac x41_g1_tac :=
    intros mb mm j pe dl tl rsv x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 MU WM MI OUT DTB FA HJ HPE HDL HTL HRSV K;
    kx_autoLx [0x235b0; 0x235dc] 30%nat
      [KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535; KZRange SPV 4096 (2^47)]
      [(SPV - 416, 160)];
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 144860) _ _ _ _) => eapply (K mm j); try eassumption; lia
    | |- evt _ _ (MS _ _ (Z_to_bv 64 144816) _ _ _ _) =>
        subst dl; rewrite (neg_dl_sh tl rsv HTL);
        eapply (x41_t1 (Z.to_nat (pe - j)) mm mm j (pe + -1 * j) (64 - tl));
          [apply munch_refl | apply wmono_refl | assumption | exact OUT | exact DTB | lia | lia | lia | lia | lia | ];
        let mm' := fresh "mm'" in let MU' := fresh "MU'" in let WM' := fresh "WM'" in let MI' := fresh "MI'" in
        let OUT' := fresh "OUT'" in let DTB' := fresh "DTB'" in
        intros mm' ? ? ? MU' WM' MI' OUT' DTB';
        replace (j + (pe + -1 * j)) with pe by lia;
        eapply (K mm' pe); [exact (munch_trans _ mb mm mm' MU MU') | exact (wmono_trans psegs mb mm mm' WM WM') | exact MI' | exact OUT'
                           | exact DTB' | | lia];
        eapply (rw_cells_transport psegs _ mm mm' _ _ FA MU' WM');
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia
    end.

  Lemma x41_g1 : forall mb mm j pe dl tl rsv
      (x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
    0 <= j <= dcap -> 0 <= pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    (forall mm' j' (y6 y10 y11 y13 y16 y19 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
        j <= j' ->
        evt psegs POST (ST 0x235dc mm' (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j')) y6 x7 x8 x9 y10 y11 x12 y13 x14 x15 y16 x17
                           (Z_to_bv 64 (DT + 4)) y19 (Z_to_bv 64 DST) x21 x22 x23 x24 w19 x26 x27 x28 x29 x30 x31)) ->
    evt psegs POST (ST 0x23590 mm (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j)) x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 DST) x21 x22 x23 x24 (Z_to_bv 64 pe) x26 x27 x28 x29 x30 x31).
  Proof. x41_g1_tac. Qed.

  Lemma x41_g1b : forall mb mm j pe dl tl rsv
      (x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
    0 <= j <= dcap -> 0 <= pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    (forall mm' j' (y6 y10 y11 y13 y16 y19 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
        j <= j' ->
        evt psegs POST (ST 0x235dc mm' (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j')) y6 x7 x8 x9 y10 y11 x12 y13 x14 x15 y16 x17
                           (Z_to_bv 64 (DT + 4)) y19 (Z_to_bv 64 DST) x21 x22 x23 x24 w19 x26 x27 x28 x29 x30 x31)) ->
    evt psegs POST (ST 0x23580 mm (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j)) x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 DST) x21 x22 x23 x24 (Z_to_bv 64 pe) x26 x27 x28 x29 x30 x31).
  Proof. x41_g1_tac. Qed.

  Lemma x41_g1c : forall mb mm j pe dl tl rsv
      (x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
    0 <= j <= dcap -> 0 <= pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    (forall mm' j' (y6 y10 y11 y13 y16 y19 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
        j <= j' ->
        evt psegs POST (ST 0x235dc mm' (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j')) y6 x7 x8 x9 y10 y11 x12 y13 x14 x15 y16 x17
                           (Z_to_bv 64 (DT + 4)) y19 (Z_to_bv 64 DST) x21 x22 x23 x24 w19 x26 x27 x28 x29 x30 x31)) ->
    evt psegs POST (ST 0x23594 mm (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j)) x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 DST) x21 x22 x23 x24 (Z_to_bv 64 pe) x26 x27 x28 x29 x30 x31).
  Proof. x41_g1_tac. Qed.

  Lemma x41_g1d : forall mb mm j pe dl tl rsv
      (x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
    0 <= j <= dcap -> 0 <= pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    (forall mm' j' (y6 y10 y11 y13 y16 y19 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
        j <= j' ->
        evt psegs POST (ST 0x235dc mm' (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j')) y6 x7 x8 x9 y10 y11 x12 y13 x14 x15 y16 x17
                           (Z_to_bv 64 (DT + 4)) y19 (Z_to_bv 64 DST) x21 x22 x23 x24 w19 x26 x27 x28 x29 x30 x31)) ->
    evt psegs POST (ST 0x23f10 mm (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j)) x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 DST) x21 x22 x23 x24 (Z_to_bv 64 pe) x26 x27 x28 x29 x30 x31).
  Proof. x41_g1_tac. Qed.


  (* [comment removed for export] *)
  Lemma x41_fin : forall mb mm j pe S bs dl tl rsv
      (x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word) jmin,
      munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
      FRA mm w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
      bytes_at psegs mm S bs -> (DST + dcap <= S \/ S + zlen bs <= DST) ->
      jmin <= j -> 0 <= j <= dcap -> 0 <= pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
      (forall mm' j' (y6 y10 y11 y13 y14 y16 y19 y24 y27 y28 y29 : word),
          munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
          FRA mm' w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
          bytes_at psegs mm' S bs -> jmin <= j' ->
          evt psegs POST (ST 0x235dc mm' (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j')) y6 x7 x8 x9 y10 y11 x12
                             y13 y14 x15 y16 x17 (Z_to_bv 64 (DT + 4)) y19 (Z_to_bv 64 DST) x21 x22 x23 y24 w19 x26 y27 y28 y29 x30 x31)) ->
      evt psegs POST (ST 0x23590 mm (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j)) x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 DST) x21 x22 x23 x24 (Z_to_bv 64 pe) x26 x27 x28 x29 x30 x31).
  Proof.
    intros mb mm j pe S bs dl tl rsv x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 jmin MU WM MI OUT DTB FA SB DJS HJM HJ HPE HDL HTL HRSV K.
    eapply (x41_g1 mm mm j pe dl tl rsv); [apply munch_refl | apply wmono_refl | exact MI | exact OUT | exact DTB | exact FA | lia | lia
                                          | exact HDL | exact HTL | exact HRSV | ].
    intros mm' j' y6 y10 y11 y13 y16 y19 MU' WM' MI' OUT' DTB' FA' HJ'.
    eapply (K mm' j'); [exact (munch_trans _ mb mm mm' MU MU') | exact (wmono_trans psegs mb mm mm' WM WM') | exact MI' | exact OUT'
                       | exact DTB' | exact FA' | | lia].
    eapply (bytes_at_transport psegs _ mm mm' S bs SB MU'). cbn [disjoint_from]. lia.
  Qed.

  Lemma x41_finb : forall mb mm j pe S bs dl tl rsv
      (x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word) jmin,
      munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
      FRA mm w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
      bytes_at psegs mm S bs -> (DST + dcap <= S \/ S + zlen bs <= DST) ->
      jmin <= j -> 0 <= j <= dcap -> 0 <= pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
      (forall mm' j' (y6 y10 y11 y13 y14 y16 y19 y24 y27 y28 y29 : word),
          munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
          FRA mm' w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
          bytes_at psegs mm' S bs -> jmin <= j' ->
          evt psegs POST (ST 0x235dc mm' (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j')) y6 x7 x8 x9 y10 y11 x12
                             y13 y14 x15 y16 x17 (Z_to_bv 64 (DT + 4)) y19 (Z_to_bv 64 DST) x21 x22 x23 y24 w19 x26 y27 y28 y29 x30 x31)) ->
      evt psegs POST (ST 0x23580 mm (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j)) x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 DST) x21 x22 x23 x24 (Z_to_bv 64 pe) x26 x27 x28 x29 x30 x31).
  Proof.
    intros mb mm j pe S bs dl tl rsv x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 jmin MU WM MI OUT DTB FA SB DJS HJM HJ HPE HDL HTL HRSV K.
    eapply (x41_g1b mm mm j pe dl tl rsv); [apply munch_refl | apply wmono_refl | exact MI | exact OUT | exact DTB | exact FA | lia | lia
                                          | exact HDL | exact HTL | exact HRSV | ].
    intros mm' j' y6 y10 y11 y13 y16 y19 MU' WM' MI' OUT' DTB' FA' HJ'.
    eapply (K mm' j'); [exact (munch_trans _ mb mm mm' MU MU') | exact (wmono_trans psegs mb mm mm' WM WM') | exact MI' | exact OUT'
                       | exact DTB' | exact FA' | | lia].
    eapply (bytes_at_transport psegs _ mm mm' S bs SB MU'). cbn [disjoint_from]. lia.
  Qed.

  Lemma x41_finc : forall mb mm j pe S bs dl tl rsv
      (x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word) jmin,
      munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
      FRA mm w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
      bytes_at psegs mm S bs -> (DST + dcap <= S \/ S + zlen bs <= DST) ->
      jmin <= j -> 0 <= j <= dcap -> 0 <= pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
      (forall mm' j' (y6 y10 y11 y13 y14 y16 y19 y24 y27 y28 y29 : word),
          munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
          FRA mm' w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
          bytes_at psegs mm' S bs -> jmin <= j' ->
          evt psegs POST (ST 0x235dc mm' (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j')) y6 x7 x8 x9 y10 y11 x12
                             y13 y14 x15 y16 x17 (Z_to_bv 64 (DT + 4)) y19 (Z_to_bv 64 DST) x21 x22 x23 y24 w19 x26 y27 y28 y29 x30 x31)) ->
      evt psegs POST (ST 0x23594 mm (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j)) x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 DST) x21 x22 x23 x24 (Z_to_bv 64 pe) x26 x27 x28 x29 x30 x31).
  Proof.
    intros mb mm j pe S bs dl tl rsv x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 jmin MU WM MI OUT DTB FA SB DJS HJM HJ HPE HDL HTL HRSV K.
    eapply (x41_g1c mm mm j pe dl tl rsv); [apply munch_refl | apply wmono_refl | exact MI | exact OUT | exact DTB | exact FA | lia | lia
                                          | exact HDL | exact HTL | exact HRSV | ].
    intros mm' j' y6 y10 y11 y13 y16 y19 MU' WM' MI' OUT' DTB' FA' HJ'.
    eapply (K mm' j'); [exact (munch_trans _ mb mm mm' MU MU') | exact (wmono_trans psegs mb mm mm' WM WM') | exact MI' | exact OUT'
                       | exact DTB' | exact FA' | | lia].
    eapply (bytes_at_transport psegs _ mm mm' S bs SB MU'). cbn [disjoint_from]. lia.
  Qed.

  Lemma x41_find : forall mb mm j pe S bs dl tl rsv
      (x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word) jmin,
      munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
      FRA mm w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
      bytes_at psegs mm S bs -> (DST + dcap <= S \/ S + zlen bs <= DST) ->
      jmin <= j -> 0 <= j <= dcap -> 0 <= pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
      (forall mm' j' (y6 y10 y11 y13 y14 y16 y19 y24 y27 y28 y29 : word),
          munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
          FRA mm' w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
          bytes_at psegs mm' S bs -> jmin <= j' ->
          evt psegs POST (ST 0x235dc mm' (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j')) y6 x7 x8 x9 y10 y11 x12
                             y13 y14 x15 y16 x17 (Z_to_bv 64 (DT + 4)) y19 (Z_to_bv 64 DST) x21 x22 x23 y24 w19 x26 y27 y28 y29 x30 x31)) ->
      evt psegs POST (ST 0x23f10 mm (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j)) x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 DST) x21 x22 x23 x24 (Z_to_bv 64 pe) x26 x27 x28 x29 x30 x31).
  Proof.
    intros mb mm j pe S bs dl tl rsv x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 jmin MU WM MI OUT DTB FA SB DJS HJM HJ HPE HDL HTL HRSV K.
    eapply (x41_g1d mm mm j pe dl tl rsv); [apply munch_refl | apply wmono_refl | exact MI | exact OUT | exact DTB | exact FA | lia | lia
                                          | exact HDL | exact HTL | exact HRSV | ].
    intros mm' j' y6 y10 y11 y13 y16 y19 MU' WM' MI' OUT' DTB' FA' HJ'.
    eapply (K mm' j'); [exact (munch_trans _ mb mm mm' MU MU') | exact (wmono_trans psegs mb mm mm' WM WM') | exact MI' | exact OUT'
                       | exact DTB' | exact FA' | | lia].
    eapply (bytes_at_transport psegs _ mm mm' S bs SB MU'). cbn [disjoint_from]. lia.
  Qed.

  (* [comment removed for export] *)
  Definition SINV (off len bc : Z) : Prop := off = 0 \/ (1 <= off /\ off + 8 <= len /\ bc <= 64).

  Notation L1ST mm j pe off S sh bc x9 x11 x12 x13 x14 x15 x17 x21 x22 x23 x26 x27 x28 x29 x30 x31 :=
    (ST 0x23310 mm (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 0x11320) (Z_to_bv 64 sh) (Z_to_bv 64 S) x9
        (Z_to_bv 64 (DST + pe - 3)) x11 x12 x13 x14 x15 (Z_to_bv 64 64) x17 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 bc) (Z_to_bv 64 DST)
        x21 x22 x23 (Z_to_bv 64 (S + off)) (Z_to_bv 64 pe) x26 x27 x28 x29 x30 x31).

  Ltac x41_l1_run ROOM ROOM2 OFF :=
    lazymatch goal with
    | SB : bytes_at psegs _ ?S ?bs, SL : zlen ?bs = ?len
      |- evt _ _ (MS (mkR (Z_to_bv 64 (DST + ?pe)) _ _ _ (Z_to_bv 64 (DST + ?j)) _ (Z_to_bv 64 (64 - ?tl)) _ _ _ _ _ _ _ _ _ _ _
                          (Z_to_bv 64 ?bc) _ _ _ _ (Z_to_bv 64 (?S + ?off)) _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        kx_autoLx [0x23310; 0x23590] 120%nat
          [ROOM2; ROOM; KZRange (len - off) 8 (2^32); OFF; KZRange bc 0 64;
           KZRange len 9 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
           KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange SPV 4096 (2^47);
           KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap S len; KZDisj DST dcap (SPV - 416) 160]
          [(DT, 16388); (S, len); (SPV - 416, 160)]
    end.

  Lemma x41_l1 : forall (k : nat) mb mm j pe off S len bs dl tl rsv bc
      (x9 x11 x12 x13 x14 x15 x17 x21 x22 x23 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w17 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 (S + 8)) w17 w18 w19 ->
    bytes_at psegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    pe - j <= Z.of_nat k -> 0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc < 2^64 ->
    (forall mm' j' (y6 y10 y11 y13 y14 y16 y19 y24 y27 y28 y29 y30 y31 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 (S + 8)) w17 w18 w19 ->
        bytes_at psegs mm' S bs -> j <= j' ->
        evt psegs POST (ST 0x235dc mm' (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j')) y6 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 S) x9 y10 y11 x12
                           y13 y14 x15 y16 x17 (Z_to_bv 64 (DT + 4)) y19 (Z_to_bv 64 DST) x21 x22 x23 y24 w19 x26 y27 y28 y29 y30 y31)) ->
    evt psegs POST (L1ST mm j pe off S (64 - tl) bc x9 x11 x12 x13 x14 x15 x17 x21 x22 x23 x26 x27 x28 x29 x30 x31).
  Proof.
    assert (LEAF : True) by exact I.
    induction k as [|k IH];
      intros mb mm j pe off S len bs dl tl rsv bc x9 x11 x12 x13 x14 x15 x17 x21 x22 x23 x26 x27 x28 x29 x30 x31
        w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w17 w18 w19 MU WM MI OUT DTB FA SB SL S0 S1 SL32 DJS HK HJ HPE HDL HTL HRSV HS HB K.
    all: destruct HS as [-> | (O1 & O2 & B1)].
    (* [comment removed for export] *)
    all: try (destruct (Z_lt_le_dec (pe - j) 4) as [RM|RM]);
         try (destruct (Z_lt_le_dec off 8) as [O8|O8]).
    all: try solve [exfalso; lia].
    all: lazymatch goal with
         | RM : 4 <= _ - _, O8 : 8 <= _ |- _ => x41_l1_run (KZRange (pe - j) 4 (2^32)) (KZRange (dcap - j) 4 (2^32)) (KZRange off 8 (2^32))
         | RM : 4 <= _ - _, O8 : _ < 8 |- _ => x41_l1_run (KZRange (pe - j) 4 (2^32)) (KZRange (dcap - j) 4 (2^32)) (KZRange off 1 7)
         | RM : _ - _ < 4, O8 : 8 <= _ |- _ => x41_l1_run (KZRange (pe - j) 0 3) (KZRange (dcap - j) 0 (2^32)) (KZRange off 8 (2^32))
         | RM : _ - _ < 4, O8 : _ < 8 |- _ => x41_l1_run (KZRange (pe - j) 0 3) (KZRange (dcap - j) 0 (2^32)) (KZRange off 1 7)
         | _ => kx_autoLx [0x23310; 0x23590] 20%nat [KZRange S 4096 (2^47); KZRange SPV 4096 (2^47)] [(SPV - 416, 160)]
         end.
    all: kx_ev_ranges; kx_mem; rewrite ?(Z.mod_small bc (2^64)) in * by lia; kx_land_ranges; kx_strip_mod.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 144784) _ _ _ _) =>
             try replace (DST + j + 4) with (DST + (j + 4)) by lia;
             eapply (x41_fin mb) with (jmin := j); try eassumption; try lia; try (rewrite SL; exact DJS);
             intros; eapply K; try eassumption; lia
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _) _ (Z_to_bv 64 144144) _ _ _ _) =>
             replace X with (S + (X - S)) by lia;
             replace (DST + j + 4) with (DST + (j + 4)) by lia;
             eapply (IH mb); try eassumption; try lia; [unfold SINV; lia | intros; eapply K; try eassumption; lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_e1 : forall mb mm j pe off S len bs dl tl rsv bc
      (x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w17 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 (S + 8)) w17 w18 w19 ->
    bytes_at psegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    0 <= j <= dcap -> 0 <= pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc < 2^64 ->
    (forall mm' j' (y6 y7 y10 y11 y13 y14 y16 y19 y24 y27 y28 y29 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 (S + 8)) w17 w18 w19 ->
        bytes_at psegs mm' S bs -> j <= j' ->
        evt psegs POST (ST 0x235dc mm' (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j')) y6 y7 (Z_to_bv 64 S) x9 y10 y11 x12
                           y13 y14 x15 y16 x17 (Z_to_bv 64 (DT + 4)) y19 (Z_to_bv 64 DST) x21 x22 x23 y24 w19 x26 y27
                           y28 y29 x30 x31)) ->
    evt psegs POST (ST 0x23490 mm (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j)) x6 x7 (Z_to_bv 64 S) x9 x10 x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 bc) (Z_to_bv 64 DST) x21 x22 x23 (Z_to_bv 64 (S + off)) (Z_to_bv 64 pe) x26 x27
                       x28 x29 x30 x31).
  Proof.
    intros mb mm j pe off S len bs dl tl rsv bc x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w17 w18 w19 MU WM MI OUT DTB FA SB SL S0 S1 SL32 DJS HJ HPE HDL HTL HRSV HS HB K.
    destruct (Z_le_gt_dec bc 64) as [B64|B64].
    2: { kx_autoLx [0x23580; 0x23594; 0x23f10] 20%nat [KZRange bc 65 (2^64 - 1)] (@nil (Z * Z)).
         eapply (x41_finc mb) with (jmin := j); try eassumption; try lia; try (rewrite SL; exact DJS).
         all: try (intros; eapply K; try eassumption; lia). }
    destruct HS as [-> | (O1 & O2 & B1)].
    { kx_autoLx [0x23580; 0x23594; 0x23f10] 20%nat [KZRange bc 0 64; KZRange S 4096 (2^47); KZRange SPV 4096 (2^47)] [(SPV - 416, 160)].
      eapply (x41_find mb) with (jmin := j); try eassumption; try lia; try (rewrite SL; exact DJS).
      all: try (intros; eapply K; try eassumption; lia). }
    destruct (Z_lt_le_dec off 8) as [O8|O8].
    all: lazymatch goal with
         | O8 : _ < 8 |- _ =>
             kx_autoLx [0x23580; 0x23594; 0x23f10] 120%nat
               [KZRange (len - off) 8 (2^32); KZRange off 1 7; KZRange bc 0 64; KZRange len 9 (2^32); KZRange S 4096 (2^47);
                KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47)]
               [(S, len); (SPV - 416, 160)]
         | O8 : 8 <= _ |- _ =>
             kx_autoLx [0x23580; 0x23594; 0x23f10] 120%nat
               [KZRange (len - off) 8 (2^32); KZRange off 8 (2^32); KZRange bc 0 64; KZRange len 9 (2^32); KZRange S 4096 (2^47);
                KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47)]
               [(S, len); (SPV - 416, 160)]
         end.
    all: eapply (x41_finb mb) with (jmin := j); try eassumption; try lia; try (rewrite SL; exact DJS).
    all: try (intros; eapply K; try eassumption; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma x41_d1 : forall mb mm j pe off S len bs dl tl rsv bc
      (x6 x7 x9 x10 x11 x12 x14 x15 x16 x17 x19 x21 x22 x23 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w17 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 (S + 8)) w17 w18 w19 ->
    bytes_at psegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc < 2^64 ->
    (forall mm' j' (y6 y7 y10 y11 y13 y14 y16 y19 y24 y27 y28 y29 y30 y31 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 (S + 8)) w17 w18 w19 ->
        bytes_at psegs mm' S bs -> j <= j' ->
        evt psegs POST (ST 0x235dc mm' (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j')) y6 y7 (Z_to_bv 64 S) x9 y10 y11 x12
                           y13 y14 x15 y16 x17 (Z_to_bv 64 (DT + 4)) y19 (Z_to_bv 64 DST) x21 x22 x23 y24 w19 x26 y27 y28 y29 y30 y31)) ->
    evt psegs POST (ST 0x232d8 mm (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j)) x6 x7 (Z_to_bv 64 S) x9 x10 x11 x12 (Z_to_bv 64 bc) x14 x15
                       x16 x17 (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 DST) x21 x22 x23 (Z_to_bv 64 (S + off)) (Z_to_bv 64 pe) x26 x27
                       x28 x29 x30 x31).
  Proof.
    intros mb mm j pe off S len bs dl tl rsv bc x6 x7 x9 x10 x11 x12 x14 x15 x16 x17 x19 x21 x22 x23 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w17 w18 w19 MU WM MI OUT DTB FA SB SL S0 S1 SL32 DJS HJ HPE HDL HTL HRSV HS HB K.
    kx_autoLx [0x23490; 0x23594; 0x23310] 40%nat
      [KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange bc 0 (2^64 - 1);
       KZRange dl 0 65535; KZRange SPV 4096 (2^47)]
      [(SPV - 416, 160)].
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 144528) _ _ _ _) =>
             eapply (x41_e1 mb); try eassumption; try lia; intros; eapply K; try eassumption; lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 144788) _ _ _ _) =>
             eapply (x41_finc mb) with (jmin := j); try eassumption; try lia; try (rewrite SL; exact DJS);
             intros; eapply K; try eassumption; lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 144144) _ _ _ _) =>
             subst dl; rewrite (neg_dl_sh tl rsv HTL);
             replace (DST + pe + -3) with (DST + pe - 3) by lia;
             eapply (x41_l1 (Z.to_nat (pe - j)) mb); try eassumption; try lia; try reflexivity;
             intros; eapply K; try eassumption; lia
         end.
  Qed.

End DX41.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition x41_ctx (SPV DST dcap DT lo : Z) (dtb : list byte) : Prop :=
  (4096 <= lo /\ lo <= SPV - 432) /\ SPV < 2^47 /\ (4096 <= DST /\ 0 <= dcap < 2^32 /\ DST + dcap < 2^47) /\
  (DST + dcap <= lo \/ SPV <= DST) /\ zlen dtb = 16388 /\ (4096 <= DT /\ DT + 16388 < 2^47) /\ (DST + dcap <= DT \/ DT + 16388 <= DST).

Ltac x41_ctx_open CTX := destruct CTX as (LO & SPB & R1 & OS1 & DL & R3 & DJ2).

Section DX41C.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.

  Definition x41_ret_c := ltac:(x41_ctx_open CTX;
    exact (x41_ret ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb LO SPB R1 OS1 R3 DJ2)).
  Definition x41_d1_c := ltac:(x41_ctx_open CTX;
    exact (x41_d1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb LO SPB R1 OS1 DL R3 DJ2)).
End DX41C.
