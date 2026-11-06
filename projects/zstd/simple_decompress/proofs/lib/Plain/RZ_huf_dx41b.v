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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41B.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 432 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -416)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 :=
    (rw_cells psegs mm (SPV + -416) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16; C8 w17; C8 w18; C8 w19]).

  (* [comment removed for export] *)
  Lemma x41_t2 : forall (k : nat) mb mm j pe sh
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x15 x16 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    pe - j <= Z.of_nat k -> 0 <= j < pe -> pe <= dcap -> 52 <= sh <= 63 ->
    (forall mm' (y11 y13 y25 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        evt psegs POST (ST 0x238cc mm' x1 x5 x6 x7 x8 x9 x10 y11 x12 y13 (Z_to_bv 64 sh) x15 x16 (Z_to_bv 64 (DST + pe))
                           (Z_to_bv 64 (DT + 4)) x19 x20 x21 x22 x23 x24 y25 x26 (Z_to_bv 64 (DST + pe)) x28 x29 x30 x31)) ->
    evt psegs POST (ST 0x238a0 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 (Z_to_bv 64 sh) x15 x16 (Z_to_bv 64 (DST + j))
                       (Z_to_bv 64 (DT + 4)) x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (DST + pe)) x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mb mm j pe sh x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x15 x16 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
      MU WM MI OUT DTB HK HJ HPE HSH K; [exfalso; lia|].
    kx_autoLx [0x238a0; 0x238cc] 30%nat
      [KZRange (dcap - j) 1 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
       KZRange DT 4096 (2^47); KZRange sh 52 63; KZWr DST dcap; KZDisj DST dcap DT 16388]
      [(DT, 16388)].
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 145568) _ _ _ _) =>
             replace (DST + j + 1) with (DST + (j + 1)) by lia;
             eapply (IH mb _ (j + 1) pe sh); try eassumption; try lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 145612) _ _ _ _) =>
             replace (DST + j + 1) with (DST + pe) by lia; eapply K; eassumption
         end.
  Qed.
  (* [comment removed for export] *)
  Ltac x41_g2_tac :=
    pose proof CTX as CTX'; x41_ctx_open CTX';
    intros mb mm j pe dl tl rsv S bs jmin x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 MU WM MI OUT DTB FA SB DJS HJM HJ HPE HDL HTL HRSV K;
    kx_autoLx [0x238a0; 0x238cc] 30%nat
      [KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535; KZRange SPV 4096 (2^47)]
      [(SPV - 416, 160)];
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 145612) _ _ _ _) => eapply (K mm j); try eassumption; lia
    | |- evt _ _ (MS _ _ (Z_to_bv 64 145568) _ _ _ _) =>
        subst dl; rewrite (neg_dl_sh tl rsv HTL);
        eapply (x41_t2 (Z.to_nat (pe - j)) mm mm j pe (64 - tl));
          [apply munch_refl | apply wmono_refl | assumption | exact OUT | exact DTB | lia | lia | lia | lia | ];
        let mm' := fresh "mm'" in let MU' := fresh "MU'" in let WM' := fresh "WM'" in let MI' := fresh "MI'" in
        let OUT' := fresh "OUT'" in let DTB' := fresh "DTB'" in
        intros mm' ? ? ? MU' WM' MI' OUT' DTB';
        eapply (K mm' pe); [exact (munch_trans _ mb mm mm' MU MU') | exact (wmono_trans psegs mb mm mm' WM WM') | exact MI' | exact OUT'
                           | exact DTB' | | | lia];
        [ eapply (rw_cells_transport psegs _ mm mm' _ _ FA MU' WM');
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia
        | eapply (bytes_at_transport psegs _ mm mm' S bs SB MU'); cbn [disjoint_from]; lia ]
    end.

  Lemma x41_g2b : forall mb mm j pe dl tl rsv S bs jmin
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
    bytes_at psegs mm S bs -> (DST + dcap <= S \/ S + zlen bs <= DST) -> jmin <= j ->
    0 <= j <= dcap -> 0 <= pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    (forall mm' j' (y11 y13 y14 y16 y25 y28 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
        bytes_at psegs mm' S bs -> jmin <= j' ->
        evt psegs POST (ST 0x238cc mm' x1 x5 x6 w8 x8 x9 x10 y11 x12 y13 y14 x15 y16 (Z_to_bv 64 (DST + j')) (Z_to_bv 64 (DT + 4)) x19
                           (Z_to_bv 64 dl) w7 x22 x23 x24 y25 x26 (Z_to_bv 64 (DST + pe)) y28 x29 x30 x31)) ->
    evt psegs POST (ST 0x237fc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 dl) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (DST + pe)) x28 x29 x30 x31).
  Proof. x41_g2_tac. Qed.

  Lemma x41_g2a : forall mb mm j pe dl tl rsv S bs jmin
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
    bytes_at psegs mm S bs -> (DST + dcap <= S \/ S + zlen bs <= DST) -> jmin <= j ->
    0 <= j <= dcap -> 0 <= pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    (forall mm' j' (y11 y13 y14 y16 y25 y28 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
        bytes_at psegs mm' S bs -> jmin <= j' ->
        evt psegs POST (ST 0x238cc mm' x1 x5 x6 w8 x8 x9 x10 y11 x12 y13 y14 x15 y16 (Z_to_bv 64 (DST + j')) (Z_to_bv 64 (DT + 4)) x19
                           (Z_to_bv 64 dl) w7 x22 x23 x24 y25 x26 (Z_to_bv 64 (DST + pe)) y28 x29 x30 x31)) ->
    evt psegs POST (ST 0x23750 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 dl) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DST + j)) x29 x30 x31).
  Proof. x41_g2_tac. Qed.

  Lemma x41_g2c : forall mb mm j pe dl tl rsv S bs jmin
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
    bytes_at psegs mm S bs -> (DST + dcap <= S \/ S + zlen bs <= DST) -> jmin <= j ->
    0 <= j <= dcap -> 0 <= pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    (forall mm' j' (y11 y13 y14 y16 y25 y28 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
        bytes_at psegs mm' S bs -> jmin <= j' ->
        evt psegs POST (ST 0x238cc mm' x1 x5 x6 w8 x8 x9 x10 y11 x12 y13 y14 x15 y16 (Z_to_bv 64 (DST + j')) (Z_to_bv 64 (DT + 4)) x19
                           (Z_to_bv 64 dl) w7 x22 x23 x24 y25 x26 (Z_to_bv 64 (DST + pe)) y28 x29 x30 x31)) ->
    evt psegs POST (ST 0x23874 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 dl) x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (DST + pe)) x29 x30 x31).
  Proof. x41_g2_tac. Qed.

  Lemma x41_g2d : forall mb mm j pe dl tl rsv S bs jmin
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
    bytes_at psegs mm S bs -> (DST + dcap <= S \/ S + zlen bs <= DST) -> jmin <= j ->
    0 <= j <= dcap -> 0 <= pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    (forall mm' j' (y11 y13 y14 y16 y25 y28 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
        bytes_at psegs mm' S bs -> jmin <= j' ->
        evt psegs POST (ST 0x238cc mm' x1 x5 x6 w8 x8 x9 x10 y11 x12 y13 y14 x15 y16 (Z_to_bv 64 (DST + j')) (Z_to_bv 64 (DT + 4)) x19
                           (Z_to_bv 64 dl) w7 x22 x23 x24 y25 x26 (Z_to_bv 64 (DST + pe)) y28 x29 x30 x31)) ->
    evt psegs POST (ST 0x23888 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 dl) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (DST + pe)) x28 x29 x30 x31).
  Proof. x41_g2_tac. Qed.

  (* [comment removed for export] *)
  Lemma x41_g2e : forall mb mm j pe dl tl rsv S bs jmin
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
    bytes_at psegs mm S bs -> (DST + dcap <= S \/ S + zlen bs <= DST) -> jmin <= j ->
    0 <= j <= dcap -> 0 <= pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    (forall mm' j' (y11 y13 y14 y16 y25 y28 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ->
        bytes_at psegs mm' S bs -> jmin <= j' ->
        evt psegs POST (ST 0x238cc mm' x1 x5 x6 w8 x8 x9 x10 y11 x12 y13 y14 x15 y16 (Z_to_bv 64 (DST + j')) (Z_to_bv 64 (DT + 4)) x19
                           (Z_to_bv 64 dl) w7 x22 x23 x24 y25 x26 (Z_to_bv 64 (DST + pe)) y28 x29 x30 x31)) ->
    evt psegs POST (ST 0x23f24 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DT + 4)) x19 x20 x21
                       x22 x23 x24 x25 x26 (Z_to_bv 64 (DST + pe)) x28 x29 x30 x31).
  Proof.
    intros mb mm j pe dl tl rsv S bs jmin x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 MU WM MI OUT DTB FA SB DJS HJM HJ HPE HDL HTL HRSV K.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    kx_autoLx [0x238a0; 0x238cc] 30%nat
      [KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535; KZRange SPV 4096 (2^47)]
      [(SPV - 416, 160)].
    all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 145612) _ _ _ _) => eapply (K mm j); try eassumption; lia
    | |- evt _ _ (MS _ _ (Z_to_bv 64 145568) _ _ _ _) =>
        subst dl; rewrite (neg_dl_sh tl rsv HTL);
        eapply (x41_t2 (Z.to_nat (pe - j)) mm mm j pe (64 - tl));
          [apply munch_refl | apply wmono_refl | assumption | exact OUT | exact DTB | lia | lia | lia | lia | ];
        intros mm' ? ? ? MU' WM' MI' OUT' DTB';
        eapply (K mm' pe); [exact (munch_trans _ mb mm mm' MU MU') | exact (wmono_trans psegs mb mm mm' WM WM') | exact MI' | exact OUT'
                           | exact DTB' | | | lia];
        [ eapply (rw_cells_transport psegs _ mm mm' _ _ FA MU' WM');
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia
        | eapply (bytes_at_transport psegs _ mm mm' S bs SB MU'); cbn [disjoint_from]; lia ]
    end.
  Qed.

  (* [comment removed for export] *)
  Notation SINV := RZ_huf_dx41.SINV.
  Notation L2ST mm j pe off S tl dl bc x1 x8 x10 x11 x12 x13 x14 x15 x19 x22 x23 x24 x26 x28 x29 x30 x31 :=
    (ST 0x2361c mm x1 (Z_to_bv 64 64) (Z_to_bv 64 (DST + pe - 3)) (Z_to_bv 64 (64 - tl)) x8 (Z_to_bv 64 S) x10 x11 x12 x13 x14 x15
        (Z_to_bv 64 0x11320) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 dl) (Z_to_bv 64 (S + off)) x22 x23 x24
        (Z_to_bv 64 bc) x26 (Z_to_bv 64 (DST + pe)) x28 x29 x30 x31).

  Ltac x41_l2_run ROOM ROOM2 OFF :=
    lazymatch goal with
    | SB : bytes_at psegs _ ?S ?bs, SL : zlen ?bs = ?len
      |- evt _ _ (MS (mkR _ _ _ _ _ _ (Z_to_bv 64 (64 - ?tl)) _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?j)) _ _ _ (Z_to_bv 64 (?S + ?off)) _ _ _
                          (Z_to_bv 64 ?bc) _ (Z_to_bv 64 (DST + ?pe)) _ _ _ _) _ _ _ _ _ _) =>
        kx_autoLx [0x2361c; 0x237fc; 0x23750; 0x23888] 120%nat
          [ROOM2; ROOM; KZRange (len - off) 8 (2^32); OFF; KZRange bc 0 64;
           KZRange len 9 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
           KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange SPV 4096 (2^47);
           KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap S len; KZDisj DST dcap (SPV - 416) 160]
          [(DT, 16388); (S, len); (SPV - 416, 160)]
    end.

  Lemma x41_l2 : forall (k : nat) mb mm j pe off S len bs dl tl rsv bc
      (x1 x8 x10 x11 x12 x13 x14 x15 x19 x22 x23 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 (Z_to_bv 64 (S + 8)) w18 w19 ->
    bytes_at psegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    pe - j <= Z.of_nat k -> 0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc < 2^64 ->
    (forall mm' j' (y11 y13 y14 y16 y25 y26 y28 y29 y30 y31 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 (Z_to_bv 64 (S + 8)) w18 w19 ->
        bytes_at psegs mm' S bs -> j <= j' ->
        evt psegs POST (ST 0x238cc mm' x1 (Z_to_bv 64 64) (Z_to_bv 64 (DST + pe - 3)) w8 x8 (Z_to_bv 64 S) x10 y11 x12 y13 y14 x15 y16
                           (Z_to_bv 64 (DST + j')) (Z_to_bv 64 (DT + 4)) x19 (Z_to_bv 64 dl) w7 x22 x23 x24 y25 y26 (Z_to_bv 64 (DST + pe))
                           y28 y29 y30 y31)) ->
    evt psegs POST (L2ST mm j pe off S tl dl bc x1 x8 x10 x11 x12 x13 x14 x15 x19 x22 x23 x24 x26 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH];
      intros mb mm j pe off S len bs dl tl rsv bc x1 x8 x10 x11 x12 x13 x14 x15 x19 x22 x23 x24 x26 x28 x29 x30 x31
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w18 w19 MU WM MI OUT DTB FA SB SL S0 S1 SL32 DJS HK HJ HPE HDL HTL HRSV HS HB K.
    all: destruct HS as [-> | (O1 & O2 & B1)].
    all: try (destruct (Z_lt_le_dec (pe - j) 4) as [RM|RM]);
         try (destruct (Z_lt_le_dec off 8) as [O8|O8]).
    all: try solve [exfalso; lia].
    all: lazymatch goal with
         | RM : 4 <= _ - _, O8 : 8 <= _ |- _ => x41_l2_run (KZRange (pe - j) 4 (2^32)) (KZRange (dcap - j) 4 (2^32)) (KZRange off 8 (2^32))
         | RM : 4 <= _ - _, O8 : _ < 8 |- _ => x41_l2_run (KZRange (pe - j) 4 (2^32)) (KZRange (dcap - j) 4 (2^32)) (KZRange off 1 7)
         | RM : _ - _ < 4, O8 : 8 <= _ |- _ => x41_l2_run (KZRange (pe - j) 0 3) (KZRange (dcap - j) 0 (2^32)) (KZRange off 8 (2^32))
         | RM : _ - _ < 4, O8 : _ < 8 |- _ => x41_l2_run (KZRange (pe - j) 0 3) (KZRange (dcap - j) 0 (2^32)) (KZRange off 1 7)
         | _ => kx_autoLx [0x2361c; 0x237fc; 0x23750; 0x23888] 20%nat [KZRange S 4096 (2^47); KZRange SPV 4096 (2^47)] [(SPV - 416, 160)]
         end.
    all: kx_ev_ranges; kx_mem; rewrite ?(Z.mod_small bc (2^64)) in * by lia; kx_land_ranges; kx_strip_mod.
    all: try replace (DST + j + 4) with (DST + (j + 4)) by lia.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 145404) _ _ _ _) =>
             eapply (x41_g2b mb) with (jmin := j) (S := S) (bs := bs); try eassumption; try lia; try (rewrite SL; exact DJS);
             intros; eapply K; try eassumption; lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 145232) _ _ _ _) =>
             eapply (x41_g2a mb) with (jmin := j) (S := S) (bs := bs); try eassumption; try lia; try (rewrite SL; exact DJS);
             intros; eapply K; try eassumption; lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 145544) _ _ _ _) =>
             eapply (x41_g2d mb) with (jmin := j) (S := S) (bs := bs); try eassumption; try lia; try (rewrite SL; exact DJS);
             intros; eapply K; try eassumption; lia
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 144924) _ _ _ _) =>
             replace X with (S + (X - S)) by lia;
             eapply (IH mb); try eassumption; try lia; [unfold RZ_huf_dx41.SINV; lia | intros; eapply K; try eassumption; lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_e2 : forall mb mm j pe off S len bs dl tl rsv bc
      (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x19 x20 x22 x23 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 (Z_to_bv 64 (S + 8)) w18 w19 ->
    bytes_at psegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc < 2^64 ->
    (forall mm' j' (y5 y6 y11 y13 y14 y16 y25 y26 y28 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 (Z_to_bv 64 (S + 8)) w18 w19 ->
        bytes_at psegs mm' S bs -> j <= j' ->
        evt psegs POST (ST 0x238cc mm' x1 y5 y6 w8 w12 (Z_to_bv 64 S) x10 y11 x12 y13 y14 x15 y16 (Z_to_bv 64 (DST + j')) (Z_to_bv 64 (DT + 4))
                           x19 (Z_to_bv 64 dl) w7 x22 x23 x24 y25 y26 (Z_to_bv 64 (DST + pe)) y28 x29 x30 x31)) ->
    evt psegs POST (ST 0x23764 mm x1 x5 x6 x7 x8 (Z_to_bv 64 S) x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DT + 4))
                       x19 x20 (Z_to_bv 64 (S + off)) x22 x23 x24 (Z_to_bv 64 bc) x26 (Z_to_bv 64 (DST + pe)) x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe off S len bs dl tl rsv bc x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x19 x20 x22 x23 x24 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w18 w19 MU WM MI OUT DTB FA SB SL S0 S1 SL32 DJS HJ HPE HDL HTL HRSV HS HB K.
    destruct (Z_le_gt_dec bc 64) as [B64|B64]; [destruct HS as [-> | (O1 & O2 & B1)]; [|destruct (Z_lt_le_dec off 8) as [O8|O8]]|].
    all: lazymatch goal with
         | B64 : _ > 64 |- _ => kx_autoLx [0x23874] 30%nat [KZRange bc 65 (2^64 - 1); KZRange SPV 4096 (2^47)] [(SPV - 416, 160)]
         | O8 : _ < 8 |- _ =>
             kx_autoLx [0x23874] 120%nat
               [KZRange (len - off) 8 (2^32); KZRange off 1 7; KZRange bc 0 64; KZRange len 9 (2^32); KZRange S 4096 (2^47);
                KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47)] [(S, len); (SPV - 416, 160)]
         | O8 : 8 <= _ |- _ =>
             kx_autoLx [0x23874] 120%nat
               [KZRange (len - off) 8 (2^32); KZRange off 8 (2^32); KZRange bc 0 64; KZRange len 9 (2^32); KZRange S 4096 (2^47);
                KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47)] [(S, len); (SPV - 416, 160)]
         | _ => kx_autoLx [0x23874] 30%nat [KZRange bc 0 64; KZRange S 4096 (2^47); KZRange SPV 4096 (2^47)] [(SPV - 416, 160)]
         end.
    all: eapply (x41_g2c mb) with (jmin := j) (S := S) (bs := bs); try eassumption; try lia; try (rewrite SL; exact DJS).
    all: try (intros; eapply K; try eassumption; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma x41_d2 : forall mb mm j pe off S len bs dl tl rsv bc
      (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x19 x20 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w6 w7 w8 w9 w11 w12 w13 w14 w15 w16 w18 w19 : word),
    munch WD mb mm -> wmono psegs mb mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 (Z_to_bv 64 (DST + pe)) w11 w12 w13 w14 w15 w16 (Z_to_bv 64 (S + 8)) w18 w19 ->
    bytes_at psegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc < 2^64 ->
    (forall mm' j' (y5 y6 y11 y13 y14 y16 y25 y26 y28 y29 y30 y31 : word),
        munch WD mb mm' -> wmono psegs mb mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 (Z_to_bv 64 dl) w6 w7 w8 w9 (Z_to_bv 64 (DST + pe)) w11 w12 w13 w14 w15 w16 (Z_to_bv 64 (S + 8)) w18 w19 ->
        bytes_at psegs mm' S bs -> j <= j' ->
        evt psegs POST (ST 0x238cc mm' w6 y5 y6 w8 w12 (Z_to_bv 64 S) x10 y11 x12 y13 y14 x15 y16 (Z_to_bv 64 (DST + j')) (Z_to_bv 64 (DT + 4))
                           x8 (Z_to_bv 64 dl) w7 x22 x23 x19 y25 y26 (Z_to_bv 64 (DST + pe)) y28 y29 y30 y31)) ->
    evt psegs POST (ST 0x235dc mm x1 x5 x6 x7 x8 (Z_to_bv 64 S) x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DT + 4))
                       x19 x20 (Z_to_bv 64 (S + off)) x22 x23 x24 (Z_to_bv 64 bc) x26 x27 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe off S len bs dl tl rsv bc x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x19 x20 x22 x23 x24 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w6 w7 w8 w9 w11 w12 w13 w14 w15 w16 w18 w19 MU WM MI OUT DTB FA SB SL S0 S1 SL32 DJS HJ HPE HDL HTL HRSV HS HB K.
    kx_autoLx [0x23764; 0x23f24; 0x2361c] 40%nat
      [KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange bc 0 (2^64 - 1);
       KZRange dl 0 65535; KZRange SPV 4096 (2^47)]
      [(SPV - 416, 160)].
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 145252) _ _ _ _) =>
             eapply (x41_e2 mb); try eassumption; try lia; intros; eapply K; try eassumption; lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 147236) _ _ _ _) =>
             eapply (x41_g2e mb) with (jmin := j) (S := S) (bs := bs); try eassumption; try lia; try (rewrite SL; exact DJS);
             intros; eapply K; try eassumption; lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 144924) _ _ _ _) =>
             subst dl; rewrite (neg_dl_sh tl rsv HTL);
             replace (DST + pe + -3) with (DST + pe - 3) by lia;
             eapply (x41_l2 (Z.to_nat (pe - j)) mb); try eassumption; try lia; try reflexivity;
             intros; eapply K; try eassumption; lia
         end.
  Qed.

End DX41B.
