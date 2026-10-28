(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import huf41_kit_reload huf41_kit_x41ck huf411_kit_rs.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41B.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.

  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap); (SPV - 144, SPV - 104)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).
  Notation BDAT mm A c b pad p st lm :=
    (rw_cells usegs mm A [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD2 mm c b pad p st lm := (BDAT mm (SPV + -144) c b pad p st lm).
  Notation SINV := RZ_huf_dx41.SINV.
  Notation K2 mb S pad dl x9 x18 x21 x22 x24 x26 pe w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 :=
    (forall mm' (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 c' b' p' : word),
        munch WD mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (DST + pe)) w12 w13 w14 w15 w16 ->
        BD2 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        evt usegs POST (ST 149596 mm' y1 y5 y6 y7 y8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21 x22 y23 x24
                          (Z_to_bv 64 (DT + 4)) x26 w8 y28 y29 y30 y31)).

  Ltac x41_side := lazymatch goal with |- evt _ _ _ => idtac | |- _ => try solve [lia] end.
  Ltac x41_fl :=
    lazymatch goal with
    | A : atoms_ok ?zs ?E |- context [bv_unsigned (edenot ?E (EAlu ALU_SLTU ?a ?b))] =>
        rewrite (kxub_sltu zs E a b A);
        lazymatch goal with |- context [Z.b2z ?c] => destruct c end; cbn; lia
    end.
  Ltac x41_res :=
    match goal with
    | SB : bytes_at usegs _ _ _ |- sc_resid _ _ _ (SCReadBase _ _ _ _) => kx_rd SB
    | |- sc_resid _ _ _ _ => kx_z
    | |- _ => idtac
    end.
  Ltac x41_post := lazymatch goal with |- evt _ _ _ => kx_ev_ranges; kx_mem; kx_srlw; kx_land_ranges; kx_strip_mod | |- _ => idtac end.

  (* [comment removed for export] *)
  Ltac x41_t2_walk j pe sh ROOM :=
    kx_autoLx [149516; 149596] 40%nat
      [ROOM; KZRange (dcap - j) 1 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
       KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47); KZRange sh 52 63;
       KZWr DST dcap; KZWr (SPV - 144) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 144) 40; KZDisj DST dcap (SPV - 512) 136;
       KZDisj (SPV - 144) 40 DT 16388; KZDisj (SPV - 144) 40 (SPV - 512) 136]
      [(DT, 16388); (SPV - 512, 136); (SPV - 144, 40)].

  Lemma x41_t2 : forall (k : nat) mb mm j pe sh dl S pad (c b p : word)
      (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x21 x22 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (DST + pe)) w12 w13 w14 w15 w16 ->
    BD2 mm c b pad p (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    pe - j <= Z.of_nat k -> 0 <= j < pe -> pe <= dcap -> 52 <= sh <= 63 ->
    K2 mb S pad dl x9 x18 x21 x22 x24 x26 pe w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 ->
    evt usegs POST (ST 149516 mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 sh) (Z_to_bv 64 2) (Z_to_bv 64 (DST + j))
                       x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21 x22 (Z_to_bv 64 (DST + j)) x24 (Z_to_bv 64 (DT + 4))
                       x26 w8 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mb mm j pe sh dl S pad c b p x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x21 x22 x24 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD DJT HK HJ HPE HSH K; [exfalso; lia|].
    destruct (Z.eq_dec (j + 1) pe) as [LST|LST];
      [ x41_t2_walk j pe sh (KZRange (pe - j) 1 1) | x41_t2_walk j pe sh (KZRange (pe - j) 2 (2^32)) ].
    all: x41_side.
    all: x41_ck.
    all: x41_post.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?A) _ _ _ _ _ _ _ _) _ (Z_to_bv 64 149516) _ _ _ _) =>
             replace A with (DST + (A - DST)) by lia;
             eapply (IH mb _ (A - DST) pe sh dl S pad); try eassumption; try lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 149596) _ _ _ _) => eapply K; eassumption
         end.
  Qed.
  (* [comment removed for export] *)
  Ltac x41_g2_walk j pe dl ROOM :=
    kx_autoLx [149516; 149596] 40%nat
      [ROOM; KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47);
       KZRange dl 1 65292; KZRange SPV 4096 (2^47);
       KZWr (SPV - 144) 40; KZDisj DST dcap (SPV - 144) 40; KZDisj (SPV - 144) 40 DT 16388; KZDisj (SPV - 144) 40 (SPV - 512) 136]
      [(SPV - 512, 136); (SPV - 144, 40)].
  Ltac x41_g2_disp mb pe dl tl rsv S pad K :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 149596) _ _ _ _) => eapply K; eassumption
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?A) _ _ _ _ _ _ _ _) _ (Z_to_bv 64 149516) _ _ _ _) =>
        replace A with (DST + (A - DST)) by lia;
        subst dl; rewrite (neg_dl_sh tl rsv ltac:(lia));
        eapply (x41_t2 (Z.to_nat (pe - (A - DST))) mb _ (A - DST) pe (64 - tl) (tl + 256 * rsv) S pad); try eassumption; try lia
    end.
  Ltac x41_g2_intro :=
    pose proof CTX as CTX'; x41_ctx_open CTX';
    intros mb mm j pe dl tl rsv S pad c b p x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x24 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD DJT HJ HPE HDL HTL HRSV K;
    destruct (Z.eq_dec j pe) as [HJE|HJE];
      [ x41_g2_walk j pe dl (KZRange (pe - j) 0 0) | x41_g2_walk j pe dl (KZRange (pe - j) 1 (2^32)) ].
  Ltac x41_g2x L mb pe dl tl rsv S pad K :=
    lazymatch goal with
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?A) _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        replace A with (DST + (A - DST)) by lia;
        eapply (L mb _ (A - DST) pe dl tl rsv S pad); try eassumption; try lia
    end.

  Lemma x41_g2b : forall mb mm j pe dl tl rsv S pad (c b p : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (DST + pe)) w12 w13 w14 w15 w16 ->
    BD2 mm c b pad p (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    K2 mb S pad dl x9 x18 x21 x22 x24 x26 pe w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 ->
    evt usegs POST (ST 149224 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21 x22
                       (Z_to_bv 64 (DST + j)) x24 (Z_to_bv 64 (DT + 4)) x26 w8 x28 x29 x30 x31).
  Proof using All.
    x41_g2_intro.
    all: x41_side.
    all: x41_ck.
    all: x41_post.
    all: x41_g2_disp mb pe dl tl rsv S pad K.
  Qed.

  Lemma x41_g2a : forall mb mm j pe dl tl rsv S pad (c b p : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (DST + pe)) w12 w13 w14 w15 w16 ->
    BD2 mm c b pad p (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    K2 mb S pad dl x9 x18 x21 x22 x24 x26 pe w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 ->
    evt usegs POST (ST 149488 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21 x22
                       (Z_to_bv 64 (DST + j)) x24 (Z_to_bv 64 (DT + 4)) x26 w8 x28 x29 x30 x31).
  Proof using All.
    x41_g2_intro.
    all: x41_side.
    all: x41_ck.
    all: x41_post.
    all: x41_g2_disp mb pe dl tl rsv S pad K.
  Qed.

  Lemma x41_g2c : forall mb mm j pe dl tl rsv S pad (c b p : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (DST + pe)) w12 w13 w14 w15 w16 ->
    BD2 mm c b pad p (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    K2 mb S pad dl x9 x18 x21 x22 x24 x26 pe w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 ->
    evt usegs POST (ST 151652 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21 x22
                       (Z_to_bv 64 (DST + j)) x24 (Z_to_bv 64 (DT + 4)) x26 w8 x28 x29 x30 x31).
  Proof using All.
    x41_g2_intro.
    all: x41_side.
    all: x41_ck.
    all: x41_post.
    all: x41_g2_disp mb pe dl tl rsv S pad K.
  Qed.

  Ltac x41_g2d_walk S len P j pe bc tl STOPS FUEL ROOM ROOM2 :=
    kx_autoLx STOPS FUEL
      [ROOM; ROOM2; KZRange (P - S) 0 (2^32); KZRange (S + len - P) 8 (2^32); KZRange bc 0 64; KZRange len 8 (2^32);
       KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange S 4096 (2^47);
       KZRange (S + len) 4096 (2^47); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange SPV 4096 (2^47);
       KZWr DST dcap; KZWr (SPV - 144) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap S len; KZDisj DST dcap (SPV - 512) 136;
       KZDisj DST dcap (SPV - 144) 40; KZDisj (SPV - 144) 40 DT 16388; KZDisj (SPV - 144) 40 S len; KZDisj (SPV - 144) 40 (SPV - 512) 136]
      [(DT, 16388); (S, len); (SPV - 512, 136); (SPV - 144, 40)].

  Lemma x41_g2d : forall mb mm j pe P S len bs dl tl rsv bc fl S7 (c0 b0 : word) pad
      (x1 x8 x9 x18 x21 x22 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (DST + pe)) w12 w13 w14 w15 w16 ->
    BD2 mm c0 b0 pad (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    S <= P -> P + 8 <= S + len -> 0 <= bc <= 64 -> (fl = 0 \/ fl = 1) -> S7 = DST + j ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    (forall mm' bc' A3 A7 (c' b' y6 y7 y8 y23 y28 y29 y30 y31 : word),
        munch WD mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (DST + pe)) w12 w13 w14 w15 w16 ->
        BD2 mm' c' b' pad (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> bytes_at usegs mm' S bs ->
        0 <= bc' <= 64 -> A3 = DST + (j + 4) + 3 -> A7 = DST + (j + 4) -> j + 4 <= pe ->
        evt usegs POST (ST 148684 mm' x1 (Z_to_bv 64 bc') y6 y7 y8 x9 (Z_to_bv 64 64) (Z_to_bv 64 (DST + pe - 3)) (Z_to_bv 64 (-1 * DT + -5))
                           (Z_to_bv 64 A3) (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1)) (Z_to_bv 64 A7) x18 (Z_to_bv 64 dl)
                           (Z_to_bv 64 (2^62)) x21 x22 y23 x24 (Z_to_bv 64 (DT + 4)) x26 w8 y28 y29 y30 y31)) ->
    K2 mb S pad dl x9 x18 x21 x22 x24 x26 pe w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 ->
    evt usegs POST (ST 148864 mm x1 (Z_to_bv 64 bc) (Z_to_bv 64 fl) (Z_to_bv 64 P) x8 x9 (Z_to_bv 64 64) (Z_to_bv 64 (DST + pe - 3))
                       (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (DST + j + 3)) (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1))
                       (Z_to_bv 64 (DST + j)) x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21 x22 (Z_to_bv 64 S7) x24 (Z_to_bv 64 (DT + 4))
                       x26 w8 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe P S len bs dl tl rsv bc fl S7 c0 b0 pad x1 x8 x9 x18 x21 x22 x24 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK DJT
      HP0 HP1 HB HFL HS7 HJ HPE HDL HTL HRSV KB K.
    subst S7.
    destruct (Z_lt_le_dec (j + 3) pe) as [RM|RM];
      [ destruct HFL as [HF|HF]; subst fl;
          [ x41_g2d_walk S len P j pe bc tl (149488 :: nil) 60%nat (KZRange (pe - j) 4 (2^32)) (KZRange (dcap - j) 4 (2^32))
          | x41_g2d_walk S len P j pe bc tl (149488 :: 148684 :: 149224 :: nil) 200%nat (KZRange (pe - j) 4 (2^32)) (KZRange (dcap - j) 4 (2^32)) ]
      | x41_g2d_walk S len P j pe bc tl (149488 :: nil) 60%nat (KZRange (pe - j) 0 3) (KZRange (dcap - j) 0 (2^32)) ].
    all: x41_side.
    all: x41_ck.
    all: x41_res.
    all: x41_post.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 149488) _ _ _ _) => x41_g2x x41_g2a mb pe dl tl rsv S pad K
         | |- evt _ _ (MS _ _ (Z_to_bv 64 148684) _ _ _ _) => eapply KB; try eassumption; try lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 149224) _ _ _ _) => x41_g2x x41_g2b mb pe dl tl rsv S pad K
         end.
  Qed.
  (* [comment removed for export] *)
  Ltac x41_g2e_walk S len off bc j pe BLO BHI OLO OHI :=
    kx_autoLx [148864] 60%nat
      [KZRange bc BLO BHI; KZRange off OLO OHI; KZRange (len - off) 8 (2^32); KZRange len 9 (2^32); KZRange S 4096 (2^47);
       KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange DT 4096 (2^47);
       KZRange j 0 (2^32); KZRange pe 0 (2^32);
       KZWr (SPV - 144) 40; KZDisj (SPV - 144) 40 S len; KZDisj (SPV - 144) 40 (SPV - 512) 136; KZDisj DST dcap (SPV - 144) 40;
       KZDisj (SPV - 144) 40 DT 16388]
      [(S, len); (SPV - 512, 136); (SPV - 144, 40)].

  Lemma x41_g2e : forall mb mm j pe off S len bs dl tl bc (c0 b0 : word) pad
      (x1 x6 x7 x8 x9 x18 x21 x22 x23 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (DST + pe)) w12 w13 w14 w15 w16 ->
    BD2 mm c0 b0 pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    0 <= j <= pe -> pe <= dcap -> 1 <= off <= 7 -> off + 8 <= len -> 0 <= bc <= 64 ->
    (forall mm' P bc' fl S7 (c' b' y8 y28 y29 y30 y31 : word),
        munch WD mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (DST + pe)) w12 w13 w14 w15 w16 ->
        BD2 mm' c' b' pad (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> bytes_at usegs mm' S bs ->
        S <= P -> P + 8 <= S + len -> 0 <= bc' <= 64 -> (fl = 0 \/ fl = 1) -> S7 = DST + j ->
        evt usegs POST (ST 148864 mm' x1 (Z_to_bv 64 bc') (Z_to_bv 64 fl) (Z_to_bv 64 P) y8 x9 (Z_to_bv 64 64) (Z_to_bv 64 (DST + pe - 3))
                           (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (DST + j + 3)) (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1))
                           (Z_to_bv 64 (DST + j)) x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21 x22 (Z_to_bv 64 S7) x24 (Z_to_bv 64 (DT + 4))
                           x26 w8 y28 y29 y30 y31)) ->
    evt usegs POST (ST 148684 mm x1 (Z_to_bv 64 bc) x6 x7 x8 x9 (Z_to_bv 64 64) (Z_to_bv 64 (DST + pe - 3)) (Z_to_bv 64 (-1 * DT + -5))
                       (Z_to_bv 64 (DST + j + 3)) (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (DST + j)) x18
                       (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21 x22 x23 x24 (Z_to_bv 64 (DT + 4)) x26 w8 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe off S len bs dl tl bc c0 b0 pad x1 x6 x7 x8 x9 x18 x21 x22 x23 x24 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK DJT HJ HPE HO HOL HB K.
    assert (QC : 0 <= bc <= 7 \/ 8 <= bc <= 15 \/ 16 <= bc <= 23 \/ 24 <= bc <= 31 \/ 32 <= bc <= 39 \/ 40 <= bc <= 47 \/
                 48 <= bc <= 55 \/ 56 <= bc <= 63 \/ 64 <= bc <= 64) by lia.
    destruct QC as [QC|[QC|[QC|[QC|[QC|[QC|[QC|[QC|QC]]]]]]]];
      [ x41_g2e_walk S len off bc j pe 0 7 1 7
      | x41_g2e_walk S len off bc j pe 8 15 1 7
      | destruct (Z_lt_le_dec off 2) as [OQ|OQ]; [x41_g2e_walk S len off bc j pe 16 23 1 1 | x41_g2e_walk S len off bc j pe 16 23 2 7]
      | destruct (Z_lt_le_dec off 3) as [OQ|OQ]; [x41_g2e_walk S len off bc j pe 24 31 1 2 | x41_g2e_walk S len off bc j pe 24 31 3 7]
      | destruct (Z_lt_le_dec off 4) as [OQ|OQ]; [x41_g2e_walk S len off bc j pe 32 39 1 3 | x41_g2e_walk S len off bc j pe 32 39 4 7]
      | destruct (Z_lt_le_dec off 5) as [OQ|OQ]; [x41_g2e_walk S len off bc j pe 40 47 1 4 | x41_g2e_walk S len off bc j pe 40 47 5 7]
      | destruct (Z_lt_le_dec off 6) as [OQ|OQ]; [x41_g2e_walk S len off bc j pe 48 55 1 5 | x41_g2e_walk S len off bc j pe 48 55 6 7]
      | destruct (Z_lt_le_dec off 7) as [OQ|OQ]; [x41_g2e_walk S len off bc j pe 56 63 1 6 | x41_g2e_walk S len off bc j pe 56 63 7 7]
      | x41_g2e_walk S len off bc j pe 64 64 1 7 ].
    all: x41_side.
    all: x41_ck.
    all: x41_post.
    all: eapply K; try eassumption; try lia; try x41_fl.
  Qed.

  (* [comment removed for export] *)
  Ltac x41_kb IH mb j pe S len bs dl tl rsv pad :=
    let mm2 := fresh "mm2" in let bc2 := fresh "bc2" in let A3 := fresh "A3" in let A7 := fresh "A7" in
    let c2 := fresh "c2" in let b2 := fresh "b2" in
    intros mm2 bc2 A3 A7 c2 b2; intros;
    lazymatch goal with BDX : rw_cells usegs mm2 (SPV + -144) [_; _; _; C8 (Z_to_bv 64 ?P); _; _] |- _ =>
      eapply (IH mb mm2 (j + 4) pe (P - S) S len bs dl tl rsv bc2 c2 b2 pad (DST + pe - 3) A3 A7); try eassumption; try lia;
      try (replace (S + (P - S)) with P by lia; exact BDX); try (unfold RZ_huf_dx41.SINV; lia)
    end.

  Lemma x41_l2 : forall (k : nat) mb mm j pe off S len bs dl tl rsv bc (c0 b0 : word) pad A1 A3 A7
      (x1 x6 x7 x8 x9 x18 x21 x22 x23 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (DST + pe)) w12 w13 w14 w15 w16 ->
    BD2 mm c0 b0 pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    pe - j < Z.of_nat k -> 0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc <= 64 -> A1 = DST + pe - 3 -> A3 = DST + j + 3 -> A7 = DST + j ->
    K2 mb S pad dl x9 x18 x21 x22 x24 x26 pe w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 ->
    evt usegs POST (ST 148684 mm x1 (Z_to_bv 64 bc) x6 x7 x8 x9 (Z_to_bv 64 64) (Z_to_bv 64 A1) (Z_to_bv 64 (-1 * DT + -5))
                       (Z_to_bv 64 A3) (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1)) (Z_to_bv 64 A7) x18 (Z_to_bv 64 dl)
                       (Z_to_bv 64 (2^62)) x21 x22 x23 x24 (Z_to_bv 64 (DT + 4)) x26 w8 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mb mm j pe off S len bs dl tl rsv bc c0 b0 pad A1 A3 A7 x1 x6 x7 x8 x9 x18 x21 x22 x23 x24 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK DJT
      HK HJ HPE HDL HTL HRSV HS HB HA1 HA3 HA7 K; [exfalso; lia|].
    subst A1 A3 A7.
    destruct HS as [HO|(O1 & O2 & B1)]; [subst off| destruct (Z_lt_le_dec off 8) as [O8|O8]];
      [ kx_autoLx [149488] 30%nat
          [KZRange bc 0 64; KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
           KZRange S 4096 (2^47); KZRange SPV 4096 (2^47)]
          [(SPV - 512, 136); (SPV - 144, 40)]
      | eapply (x41_g2e mb mm j pe off S len bs dl tl bc c0 b0 pad); try eassumption; try lia;
        let mm1 := fresh "mm1" in let P := fresh "P" in let bc1 := fresh "bc1" in let fl := fresh "fl" in
        let S7 := fresh "S7" in let c1 := fresh "c1" in let b1 := fresh "b1" in
        intros mm1 P bc1 fl S7 c1 b1; intros;
        eapply (x41_g2d mb mm1 j pe P S len bs dl tl rsv bc1 fl S7 c1 b1 pad); try eassumption; try lia;
        x41_kb IH mb j pe S len bs dl tl rsv pad
      | kx_autoLx [148864] 40%nat
          [KZRange off 8 (2^32); KZRange (len - off) 8 (2^32); KZRange bc 0 64; KZRange len 16 (2^32); KZRange S 4096 (2^47);
           KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32);
           KZRange DT 4096 (2^47); KZRange j 0 (2^32); KZRange pe 0 (2^32);
           KZWr (SPV - 144) 40; KZDisj (SPV - 144) 40 S len; KZDisj (SPV - 144) 40 (SPV - 512) 136; KZDisj DST dcap (SPV - 144) 40;
           KZDisj (SPV - 144) 40 DT 16388]
          [(S, len); (SPV - 512, 136); (SPV - 144, 40)] ].
    all: x41_side.
    all: x41_ck.
    all: x41_post.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 149488) _ _ _ _) => x41_g2x x41_g2a mb pe dl tl rsv S pad K
         | |- evt _ _ (MS _ _ (Z_to_bv 64 148864) _ _ _ _) =>
             eapply (x41_g2d mb _ j pe); try eassumption; try lia; try x41_fl;
             x41_kb IH mb j pe S len bs dl tl rsv pad
         end.
  Qed.

  Ltac x41_r2_walk S len off bc j pe dl ROOM BLO BHI OLO OHI :=
    kx_autoLx [149516; 149596] 80%nat
      [ROOM; KZRange bc BLO BHI; KZRange off OLO OHI; KZRange (len - off) 8 (2^32); KZRange len 9 (2^32); KZRange S 4096 (2^47);
       KZRange (S + len) 4096 (2^47); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
       KZRange DT 4096 (2^47); KZRange dl 1 65292; KZRange SPV 4096 (2^47);
       KZWr (SPV - 144) 40; KZDisj (SPV - 144) 40 S len; KZDisj (SPV - 144) 40 (SPV - 512) 136; KZDisj DST dcap (SPV - 144) 40;
       KZDisj (SPV - 144) 40 DT 16388]
      [(S, len); (SPV - 512, 136); (SPV - 144, 40)].
  Ltac x41_r2_split S len off bc j pe dl ROOM :=
    assert (QC : 0 <= bc <= 7 \/ 8 <= bc <= 15 \/ 16 <= bc <= 23 \/ 24 <= bc <= 31 \/ 32 <= bc <= 39 \/ 40 <= bc <= 47 \/
                 48 <= bc <= 55 \/ 56 <= bc <= 63 \/ 64 <= bc <= 64) by lia;
    destruct QC as [QC|[QC|[QC|[QC|[QC|[QC|[QC|[QC|QC]]]]]]]];
      [ x41_r2_walk S len off bc j pe dl ROOM 0 7 1 7
      | x41_r2_walk S len off bc j pe dl ROOM 8 15 1 7
      | destruct (Z_lt_le_dec off 2) as [OQ|OQ]; [x41_r2_walk S len off bc j pe dl ROOM 16 23 1 1 | x41_r2_walk S len off bc j pe dl ROOM 16 23 2 7]
      | destruct (Z_lt_le_dec off 3) as [OQ|OQ]; [x41_r2_walk S len off bc j pe dl ROOM 24 31 1 2 | x41_r2_walk S len off bc j pe dl ROOM 24 31 3 7]
      | destruct (Z_lt_le_dec off 4) as [OQ|OQ]; [x41_r2_walk S len off bc j pe dl ROOM 32 39 1 3 | x41_r2_walk S len off bc j pe dl ROOM 32 39 4 7]
      | destruct (Z_lt_le_dec off 5) as [OQ|OQ]; [x41_r2_walk S len off bc j pe dl ROOM 40 47 1 4 | x41_r2_walk S len off bc j pe dl ROOM 40 47 5 7]
      | destruct (Z_lt_le_dec off 6) as [OQ|OQ]; [x41_r2_walk S len off bc j pe dl ROOM 48 55 1 5 | x41_r2_walk S len off bc j pe dl ROOM 48 55 6 7]
      | destruct (Z_lt_le_dec off 7) as [OQ|OQ]; [x41_r2_walk S len off bc j pe dl ROOM 56 63 1 6 | x41_r2_walk S len off bc j pe dl ROOM 56 63 7 7]
      | x41_r2_walk S len off bc j pe dl ROOM 64 64 1 7 ].

  Lemma x41_r2 : forall mb mm j pe off S len bs dl tl rsv bc (c0 : word) pad
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (DST + pe)) w12 w13 w14 w15 w16 ->
    BD2 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    0 <= j <= pe -> pe - j < 4 -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    1 <= off <= 7 -> off + 8 <= len -> 0 <= bc <= 64 ->
    K2 mb S pad dl x9 x18 x21 x22 x24 x26 pe w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 ->
    evt usegs POST (ST 149252 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21 x22
                       (Z_to_bv 64 (DST + j)) x24 (Z_to_bv 64 (DT + 4)) x26 w8 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe off S len bs dl tl rsv bc c0 pad x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x24 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK DJT
      HJ HJ4 HPE HDL HTL HRSV HO HOL HB K.
    destruct (Z.eq_dec j pe) as [HJE|HJE];
      [ x41_r2_split S len off bc j pe dl (KZRange (pe - j) 0 0) | x41_r2_split S len off bc j pe dl (KZRange (pe - j) 1 3) ].
    all: x41_side.
    all: x41_ck.
    all: x41_res.
    all: x41_post.
    all: x41_g2_disp mb pe dl tl rsv S pad K.
  Qed.
  (* [comment removed for export] *)
  Ltac x41_e2_walk S len off bc j pe STOPS BLO BHI OLO OHI :=
    kx_autoLx STOPS 40%nat
      [KZRange bc BLO BHI; KZRange off OLO OHI; KZRange (len - off) 0 (2^32); KZRange len 0 (2^32); KZRange S 4096 (2^47);
       KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32);
       KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange (pe - j) 0 3]
      [(SPV - 512, 136); (SPV - 144, 40)].
  Ltac x41_e2s_walk S bc j pe STOPS BLO BHI :=
    kx_autoLx STOPS 30%nat
      [KZRange bc BLO BHI; KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange S 4096 (2^47);
       KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange (pe - j) 0 3]
      [(SPV - 512, 136); (SPV - 144, 40)].

  Lemma x41_e2 : forall mb mm j pe off S len bs dl tl rsv bc (c0 : word) pad
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (DST + pe)) w12 w13 w14 w15 w16 ->
    BD2 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) -> (DT + 16388 <= lo \/ SPV <= DT) -> rsk_al SPV 16 ->
    0 <= j <= pe -> pe - j < 4 -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc < 2^32 ->
    K2 mb S pad dl x9 x18 x21 x22 x24 x26 pe w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 ->
    evt usegs POST (ST 149252 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21 x22
                       (Z_to_bv 64 (DST + j)) x24 (Z_to_bv 64 (DT + 4)) x26 w8 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    pose proof huf_reload_proof as HRL. unfold huf_reload_stmt, huf_reload_stmt_at, bitd_cells in HRL.
    intros mb mm j pe off S len bs dl tl rsv bc c0 pad x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x24 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK DJT SPA
      HJ HJ4 HPE HDL HTL HRSV HS HB K.
    destruct (Z_le_gt_dec bc 64) as [B64|B64];
      [ destruct HS as [HO|(O1 & O2 & B1)]; [subst off| destruct (Z_lt_le_dec off 8) as [O8|O8]];
          [ x41_e2s_walk S bc j pe (149488 :: nil) 0 64
          | eapply (x41_r2 mb mm j pe off S len bs dl tl rsv bc c0 pad); try eassumption; try lia
          | x41_e2_walk S len off bc j pe (154784 :: nil) 0 64 8 (2^32) ]
      | destruct (Z_lt_le_dec bc (2^31)) as [B31|B31];
          [ x41_e2s_walk S bc j pe (151652 :: nil) 65 (2^31 - 1) | x41_e2s_walk S bc j pe (151652 :: nil) (2^31) (2^32 - 1) ] ].
    all: x41_side.
    all: x41_ck.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 154784) _ _ _ _) =>
             assert (BDA : (SPV + -144) mod 8 = 0) by (apply rsk_al_e in SPA; clear - SPA; Z.div_mod_to_equations; lia);
             eapply evt_cut;
             [ eapply HRL; [ exact MI | exact BD | exact BDA | exact SB | exact SL | lia | lia | lia | lia | lia | lia | lia | lia ]
             | post_call usegs mm ];
             unfold bitd_cells in *; clear BDA;
             destruct (Z.eq_dec j pe) as [HJE|HJE];
             [ x41_g2_walk j pe dl (KZRange (pe - j) 0 0) | x41_g2_walk j pe dl (KZRange (pe - j) 1 3) ]
         | |- _ => idtac
         end.
    all: x41_side.
    all: x41_ck.
    all: x41_post.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 149488) _ _ _ _) => x41_g2x x41_g2a mb pe dl tl rsv S pad K
         | |- evt _ _ (MS _ _ (Z_to_bv 64 151652) _ _ _ _) => x41_g2x x41_g2c mb pe dl tl rsv S pad K
         | |- evt _ _ _ => x41_g2_disp mb pe dl tl rsv S pad K
         end.
  Qed.
  (* [comment removed for export] *)
  Ltac x41_d2_walk j pe dl STOPS ROOM BCR :=
    kx_autoLx STOPS 30%nat
      [ROOM; BCR; KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange DT 4096 (2^47);
       KZRange dl 1 65292; KZRange SPV 4096 (2^47)]
      [(SPV - 512, 136); (SPV - 144, 40)].

  Lemma x41_d2 : forall mb mm j pe off S len bs dl tl rsv bc (c0 : word) pad
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (DST + pe)) w12 w13 w14 w15 w16 ->
    BD2 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) -> (DT + 16388 <= lo \/ SPV <= DT) -> rsk_al SPV 16 ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc < 2^32 ->
    K2 mb S pad dl x9 x18 x21 x22 x24 x26 pe w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 ->
    evt usegs POST (ST 148620 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21 x22
                       (Z_to_bv 64 (DST + j)) x24 (Z_to_bv 64 (DT + 4)) x26 w8 x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe off S len bs dl tl rsv bc c0 pad x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x24 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJK DJT SPA
      HJ HPE HDL HTL HRSV HS HB K.
    destruct (Z_lt_le_dec (pe - j) 4) as [E4|E4];
      [ x41_d2_walk j pe dl (149252 :: nil) (KZRange (pe - j) 0 3) (KZRange bc 0 (2^32 - 1))
      | destruct (Z_le_gt_dec bc 64) as [B64|B64];
          [ x41_d2_walk j pe dl (148684 :: nil) (KZRange (pe - j) 4 (2^32)) (KZRange bc 0 64)
          | destruct (Z_lt_le_dec bc (2^31)) as [B31|B31];
              [ x41_d2_walk j pe dl (149224 :: nil) (KZRange (pe - j) 4 (2^32)) (KZRange bc 65 (2^31 - 1))
              | x41_d2_walk j pe dl (149224 :: nil) (KZRange (pe - j) 4 (2^32)) (KZRange bc (2^31) (2^32 - 1)) ] ] ].
    all: x41_side.
    all: x41_ck.
    all: x41_post.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 149252) _ _ _ _) =>
             eapply (x41_e2 mb mm j pe off S len bs dl tl rsv bc c0 pad); try eassumption; try lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 149224) _ _ _ _) => x41_g2x x41_g2b mb pe dl tl rsv S pad K
         | |- evt _ _ (MS _ _ (Z_to_bv 64 148684) _ _ _ _) =>
             try replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity);
             subst dl; rewrite (neg_dl_sh tl rsv HTL);
             eapply (x41_l2 (Z.to_nat (pe - j + 1)) mb _ j pe off S len bs (tl + 256 * rsv) tl rsv bc); try eassumption; try lia
         end.
  Qed.

End DX41B.
