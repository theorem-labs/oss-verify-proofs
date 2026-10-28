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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import huf41_kit_reload huf41_kit_x41ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41C3.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap); (SPV - 184, SPV - 144)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).
  Notation BDAT mm A c b pad p st lm :=
    (rw_cells usegs mm A [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD3 mm c b pad p st lm := (BDAT mm (SPV + -184) c b pad p st lm).

  (* [comment removed for export] *)
  Lemma x41_t3 : forall (k : nat) mb mm j pe sh (c b : word) (pad : list byte) (p st lm : word)
      (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x21 x23 x26 x27 x28 x29 x30 x31 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    BD3 mm c b pad p st lm -> (DT + 16388 <= lo \/ SPV <= DT) ->
    pe - j <= Z.of_nat k -> 0 <= j < pe -> pe <= dcap -> 52 <= sh <= 63 ->
    (forall mm' (y10 y11 y12 y13 y14 y15 y16 c' b' : word),
        munch WD mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        BD3 mm' c' b' pad p st lm ->
        evt usegs POST (ST 0x24c18 mm' x1 x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 y16 x17 x18 x19 (Z_to_bv 64 (2^62)) x21
                         (Z_to_bv 64 (DST + pe)) x23 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) x26 x27 x28 x29 x30 x31)) ->
    evt usegs POST (ST 0x24bcc mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 sh) (Z_to_bv 64 2) (Z_to_bv 64 (DST + j))
                     x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (2^62)) x21
                     (Z_to_bv 64 (DST + j)) x23 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) x26 x27 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mb mm j pe sh c b pad p st lm x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x21 x23 x26 x27 x28 x29 x30 x31
      MU WM MI OUT DTB BD DJD HK HJ HPE HSH K; [exfalso; lia|].
    kx_autoLx [0x24bcc; 0x24c18; 0x253c0] 30%nat
      [KZRange (dcap - j) 1 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
       KZRange DT 4096 (2^47); KZRange sh 52 63; KZRange SPV 4096 (2^47); KZWr DST dcap; KZWr (SPV - 184) 40;
       KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 184) 40; KZDisj (SPV - 184) 40 DT 16388]
      [(DT, 16388); (SPV - 184, 40)].
    all: x41_ck.
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24bcc) _ _ _ _) =>
             replace (DST + j + 1) with (DST + (j + 1)) by lia;
             eapply (IH mb _ (j + 1) pe sh); try eassumption; try lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24c18) _ _ _ _) =>
             replace (DST + j + 1) with (DST + pe) by lia; eapply K; eassumption
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_g3a : forall mb mm j pe dl tl rsv S bs jmin (c b : word) (pad : list byte) (p : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
    BD3 mm c b pad p (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> (DST + dcap <= S \/ S + zlen bs <= DST) -> (S + zlen bs <= lo \/ SPV <= S) ->
    (DT + 16388 <= lo \/ SPV <= DT) -> jmin <= j ->
    0 <= j < pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    (forall mm' j' (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 c' b' p' : word),
        munch WD mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
        BD3 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> bytes_at usegs mm' S bs -> jmin <= j' ->
        evt usegs POST (ST 0x24c18 mm' y1 y5 y6 y7 y8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21
                         (Z_to_bv 64 (DST + j')) x23 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) x26 w8 y28 y29 y30 y31)) ->
    evt usegs POST (ST 0x24bb8 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21
                     (Z_to_bv 64 (DST + j)) x23 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) x26 w8 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe dl tl rsv S bs jmin c b pad p x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD SB DJS DJL DJD HJM HJ HPE HDL HTL HRSV K.
    kx_autoLx [0x24bcc] 10%nat
      [KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535;
       KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47)]
      [].
    subst dl; rewrite ?(neg_dl_sh tl rsv HTL).
    eapply (x41_t3 (Z.to_nat (pe - j)) mm mm j pe (64 - tl) c b pad p (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)));
      [apply munch_refl | apply wmono_refl | exact MI | exact OUT | exact DTB | exact BD | exact DJD | lia | lia | lia | lia | ].
    intros mm' y10 y11 y12 y13 y14 y15 y16 c' b' MU' WM' MI' OUT' DTB' BD'.
    eapply (K mm' pe); [exact (munch_trans _ mb mm mm' MU MU') | exact (wmono_trans usegs mb mm mm' WM WM') | exact MI' | exact OUT'
                       | exact DTB' | | exact BD' | | lia].
    + eapply (rw_cells_transport usegs _ mm mm' _ _ FA MU' WM');
      cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    + eapply (bytes_at_transport usegs _ mm mm' S bs SB MU'); cbn [disjoint_from]; lia.
  Qed.

  Lemma x41_g3b : forall mb mm j pe dl tl rsv S bs jmin (c b : word) (pad : list byte) (p : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
    BD3 mm c b pad p (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> (DST + dcap <= S \/ S + zlen bs <= DST) -> (S + zlen bs <= lo \/ SPV <= S) ->
    (DT + 16388 <= lo \/ SPV <= DT) -> jmin <= j ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    (forall mm' j' (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 c' b' p' : word),
        munch WD mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
        BD3 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> bytes_at usegs mm' S bs -> jmin <= j' ->
        evt usegs POST (ST 0x24c18 mm' y1 y5 y6 y7 y8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21
                         (Z_to_bv 64 (DST + j')) x23 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) x26 w8 y28 y29 y30 y31)) ->
    evt usegs POST (ST 0x24bb4 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21
                     (Z_to_bv 64 (DST + j)) x23 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) x26 w8 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe dl tl rsv S bs jmin c b pad p x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD SB DJS DJL DJD HJM HJ HPE HDL HTL HRSV K.
    kx_autoLx [0x24bb8; 0x24c18] 20%nat
      [KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535;
       KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47)]
      [].
    all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24c18) _ _ _ _) => eapply (K mm j); try eassumption; lia
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24bb8) _ _ _ _) =>
        eapply (x41_g3a mb mm j pe dl tl rsv S bs jmin c b pad p); try eassumption; lia
    end.
  Qed.

  Lemma x41_g3c : forall mb mm j pe dl tl rsv S bs jmin (c b : word) (pad : list byte) (p : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
    BD3 mm c b pad p (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> (DST + dcap <= S \/ S + zlen bs <= DST) -> (S + zlen bs <= lo \/ SPV <= S) ->
    4096 <= S -> S + zlen bs < 2^47 -> (DT + 16388 <= lo \/ SPV <= DT) -> jmin <= j ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    (forall mm' j' (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 c' b' p' : word),
        munch WD mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
        BD3 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> bytes_at usegs mm' S bs -> jmin <= j' ->
        evt usegs POST (ST 0x24c18 mm' y1 y5 y6 y7 y8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21
                         (Z_to_bv 64 (DST + j')) x23 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) x26 w8 y28 y29 y30 y31)) ->
    evt usegs POST (ST 0x24ab4 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21
                     (Z_to_bv 64 (DST + j)) x23 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) x26 x27 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe dl tl rsv S bs jmin c b pad p x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD SB DJS DJL S0 S1 DJD HJM HJ HPE HDL HTL HRSV K.
    kx_autoLx [0x24bb8; 0x24c18] 30%nat
      [KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535;
       KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 184) 40; KZDisj DST dcap (SPV - 184) 40;
       KZDisj (SPV - 184) 40 DT 16388; KZDisj (SPV - 184) 40 S (zlen bs)]
      [(SPV - 512, 136); (SPV - 184, 40)].
    all: kx_mem.
    all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24c18) _ _ _ _) => eapply (K _ j); try eassumption; lia
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24bb8) _ _ _ _) =>
        eapply (x41_g3a mb _ j pe dl tl rsv S bs jmin); try eassumption; lia
    end.
  Qed.

  Lemma x41_g3d : forall mb mm j pe dl tl rsv S bs jmin (c b : word) (pad : list byte) (p : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
    BD3 mm c b pad p (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> (DST + dcap <= S \/ S + zlen bs <= DST) -> (S + zlen bs <= lo \/ SPV <= S) ->
    4096 <= S -> S + zlen bs < 2^47 -> (DT + 16388 <= lo \/ SPV <= DT) -> jmin <= j ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    (forall mm' j' (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 c' b' p' : word),
        munch WD mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
        BD3 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> bytes_at usegs mm' S bs -> jmin <= j' ->
        evt usegs POST (ST 0x24c18 mm' y1 y5 y6 y7 y8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21
                         (Z_to_bv 64 (DST + j')) x23 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) x26 w8 y28 y29 y30 y31)) ->
    evt usegs POST (ST 0x2507c mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21
                     (Z_to_bv 64 (DST + j)) x23 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) x26 w8 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe dl tl rsv S bs jmin c b pad p x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 MU WM MI OUT DTB FA BD SB DJS DJL S0 S1 DJD HJM HJ HPE HDL HTL HRSV K.
    kx_autoLx [0x24bb8; 0x24c18] 30%nat
      [KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535;
       KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 184) 40; KZDisj DST dcap (SPV - 184) 40;
       KZDisj (SPV - 184) 40 DT 16388; KZDisj (SPV - 184) 40 S (zlen bs)]
      [(SPV - 184, 40)].
    all: kx_mem.
    all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24c18) _ _ _ _) => eapply (K _ j); try eassumption; lia
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24bb8) _ _ _ _) =>
        eapply (x41_g3a mb _ j pe dl tl rsv S bs jmin); try eassumption; lia
    end.
  Qed.

  (* [comment removed for export] *)
  Notation SINV := RZ_huf_dx41.SINV.
  Lemma x41_l3 : forall (k : nat) mb mm j pe off S len bs dl tl rsv bc (c : word) (pad : list byte)
      (x1 x6 x7 x8 x9 x18 x21 x22 x23 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
    BD3 mm c (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    pe - j <= Z.of_nat k -> 0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc <= 64 ->
    (forall mm' j' (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 c' b' p' : word),
        munch WD mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
        BD3 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> bytes_at usegs mm' S bs -> j <= j' ->
        evt usegs POST (ST 0x24c18 mm' y1 y5 y6 y7 y8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21
                         (Z_to_bv 64 (DST + j')) x23 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) x26 w8 y28 y29 y30 y31)) ->
    evt usegs POST (ST 0x24898 mm x1 (Z_to_bv 64 bc) x6 x7 x8 x9 (Z_to_bv 64 64) (Z_to_bv 64 (DST + pe - 3)) (Z_to_bv 64 (-1 * DT + -5))
                     (Z_to_bv 64 (DST + j + 3)) (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (DST + j))
                     x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21 x22 x23 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) x26 w8 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH];
      intros mb mm j pe off S len bs dl tl rsv bc c pad x1 x6 x7 x8 x9 x18 x21 x22 x23 x26 x28 x29 x30 x31
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
        MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJL DJD HK HJ HPE HDL HTL HRSV HS HB K.
    all: destruct HS as [-> | (O1 & O2 & B1)].
    all: try (destruct (Z_lt_le_dec (pe - j) 4) as [RM|RM]);
         try (destruct (Z_lt_le_dec off 8) as [O8|O8]).
    all: try solve [exfalso; lia].
    all: try lazymatch goal with
         | RM : 4 <= _ - _, O8 : _ < 8 |- _ =>
             assert (QB : 0 <= bc <= 7 \/ 8 <= bc <= 15 \/ 16 <= bc <= 23 \/ 24 <= bc <= 31 \/ 32 <= bc <= 39 \/ 40 <= bc <= 47 \/
                          48 <= bc <= 55 \/ 56 <= bc <= 63 \/ 64 <= bc <= 64) by lia;
             destruct QB as [QB|[QB|[QB|[QB|[QB|[QB|[QB|[QB|QB]]]]]]]]
         end.
    all: lazymatch goal with
         | RM : 4 <= _ - _, O8 : 8 <= _ |- _ =>
             kx_autoLx [0x24898; 0x24bb4; 0x24ab4; 0x253c0] 150%nat
               [KZRange (pe - j) 4 (2^32); KZRange (dcap - j) 4 (2^32); KZRange (len - off) 8 (2^32); KZRange off 8 (2^32);
                KZRange bc 0 64; KZRange len 9 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32);
                KZRange DST 4096 (2^47); KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange DT 4096 (2^47);
                KZRange tl 1 12; KZRange SPV 4096 (2^47);
                KZWr DST dcap; KZWr (SPV - 184) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap S len;
                KZDisj DST dcap (SPV - 184) 40; KZDisj (SPV - 184) 40 DT 16388; KZDisj (SPV - 184) 40 S len]
               [(DT, 16388); (S, len); (SPV - 184, 40)]
         | RM : 4 <= _ - _, O8 : _ < 8 |- _ =>
             lazymatch type of QB with ?blo <= _ <= ?bhi =>
             kx_autoLx [0x24898; 0x24bb4; 0x24ab4; 0x253c0] 150%nat
               [KZRange (pe - j) 4 (2^32); KZRange (dcap - j) 4 (2^32); KZRange (len - off) 8 (2^32); KZRange off 1 7;
                KZRange bc blo bhi; KZRange len 9 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32);
                KZRange DST 4096 (2^47); KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange DT 4096 (2^47);
                KZRange tl 1 12; KZRange SPV 4096 (2^47);
                KZWr DST dcap; KZWr (SPV - 184) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap S len;
                KZDisj DST dcap (SPV - 184) 40; KZDisj (SPV - 184) 40 DT 16388; KZDisj (SPV - 184) 40 S len]
               [(DT, 16388); (S, len); (SPV - 184, 40)] end
         | RM : _ - _ < 4, O8 : 8 <= _ |- _ =>
             kx_autoLx [0x24898; 0x24bb4; 0x24ab4; 0x253c0] 150%nat
               [KZRange (pe - j) 0 3; KZRange (dcap - j) 0 (2^32); KZRange (len - off) 8 (2^32); KZRange off 8 (2^32);
                KZRange bc 0 64; KZRange len 9 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32);
                KZRange DST 4096 (2^47); KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange DT 4096 (2^47);
                KZRange tl 1 12; KZRange SPV 4096 (2^47);
                KZWr DST dcap; KZWr (SPV - 184) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap S len;
                KZDisj DST dcap (SPV - 184) 40; KZDisj (SPV - 184) 40 DT 16388; KZDisj (SPV - 184) 40 S len]
               [(DT, 16388); (S, len); (SPV - 184, 40)]
         | RM : _ - _ < 4, O8 : _ < 8 |- _ =>
             kx_autoLx [0x24898; 0x24bb4; 0x24ab4; 0x253c0] 150%nat
               [KZRange (pe - j) 0 3; KZRange (dcap - j) 0 (2^32); KZRange (len - off) 8 (2^32); KZRange off 1 7;
                KZRange bc 0 64; KZRange len 9 (2^32); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32);
                KZRange DST 4096 (2^47); KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange DT 4096 (2^47);
                KZRange tl 1 12; KZRange SPV 4096 (2^47);
                KZWr DST dcap; KZWr (SPV - 184) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap S len;
                KZDisj DST dcap (SPV - 184) 40; KZDisj (SPV - 184) 40 DT 16388; KZDisj (SPV - 184) 40 S len]
               [(DT, 16388); (S, len); (SPV - 184, 40)]
         | _ =>
             kx_autoLx [0x24898; 0x24bb4; 0x24ab4; 0x253c0] 20%nat
               [KZRange bc 0 64; KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
                KZRange S 4096 (2^47); KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47)]
               [(SPV - 184, 40)]
         end.
    all: x41_ck.
    all: kx_ev_ranges; kx_mem; kx_land_ranges; kx_strip_mod.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24bb4) _ _ _ _) =>
             eapply (x41_g3b mb) with (jmin := j) (S := S) (bs := bs); try eassumption; try lia; try (rewrite SL; first [exact DJS | exact DJL | lia]);
             intros; eapply K; try eassumption; lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24ab4) _ _ _ _) =>
             replace (DST + j + 4) with (DST + (j + 4)) by lia;
             eapply (x41_g3c mb) with (jmin := j) (S := S) (bs := bs); try eassumption; try lia; try (rewrite SL; first [exact DJS | exact DJL | lia]);
             intros; eapply K; try eassumption; lia
         | BDX : rw_cells usegs ?m (SPV + -184) [_; _; _; C8 (Z_to_bv 64 ?X); _; _] |- evt _ _ (MS _ _ (Z_to_bv 64 0x24898) _ _ ?m _) =>
             first [ solve [exfalso; lia]
                   | solve [exfalso;
                           lazymatch goal with KXA : atoms_ok ?zs ?E |- _ =>
                           match goal with H : context [bv_unsigned (edenot E (EAlu ALU_SLTU ?a ?b))] |- _ =>
                             change (edenot E (EAlu ALU_SLTU a b)) with (alu64 ALU_SLTU (edenot E a) (edenot E b)) in H;
                             rewrite u_sltu64, (uz_sound zs E a KXA), (uz_sound zs E b KXA) in H;
                              cbn [uz ez Nat.ltb Nat.leb length znth] in H;
                              lazymatch type of H with context [if (?x <? ?y) then _ else _] =>
                               destruct (Z.ltb_spec x y) as [LT|LT]; vm_compute in H; rewrite ?Z.mod_small in LT by lia; lia end
                            end end]
                  | replace X with (S + (X - S)) in BDX by lia;
                     replace (DST + j + 7) with (DST + (j + 4) + 3) by lia;
                     replace (DST + j + 4) with (DST + (j + 4)) by lia;
                     eapply (IH mb); try eassumption; try lia; try (unfold SINV; lia); try (intros; eapply K; try eassumption; lia) ]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_e3 : forall mb mm j pe off S len bs dl tl rsv bc (c : word) (pad : list byte)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
    BD3 mm c (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) -> (DT + 16388 <= lo \/ SPV <= DT) -> SPV mod 16 = 0 ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc < 2^31 ->
    (forall mm' j' (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 c' b' p' : word),
        munch WD mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
        BD3 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> bytes_at usegs mm' S bs -> j <= j' ->
        evt usegs POST (ST 0x24c18 mm' y1 y5 y6 y7 y8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21
                         (Z_to_bv 64 (DST + j')) x23 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) x26 w8 y28 y29 y30 y31)) ->
    evt usegs POST (ST 0x24acc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21
                     (Z_to_bv 64 (DST + j)) x23 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) x26 w8 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe off S len bs dl tl rsv bc c pad x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
      MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJL DJD SPA HJ HPE HDL HTL HRSV HS HB K.
    assert (BDA : (SPV + -184) mod 8 = 0).
    { pose proof (Z.div_mod SPV 16 ltac:(lia)) as E. rewrite SPA, Z.add_0_r in E. rewrite E.
      replace (16 * (SPV / 16) + -184) with ((2 * (SPV / 16) - 23) * 8) by lia. apply Z.mod_mul. lia. }
    clear SPA.
    destruct (Z_le_gt_dec bc 64) as [B64|B64]; [destruct HS as [-> | (O1 & O2 & B1)]; [|destruct (Z_lt_le_dec off 8) as [O8|O8]]|].
    all: lazymatch goal with
         | B64 : _ > 64 |- _ =>
             kx_autoLx [0x2507c; 0x24bb4; 0x24bb8; 0x24c18; 0x25ca0; 0x253c0] 30%nat
               [KZRange bc 65 (2^31 - 1); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange j 0 (2^32); KZRange pe 0 (2^32)]
               [(SPV - 184, 40)]
         | O8 : _ < 8 |- _ =>
             kx_autoLx [0x2507c; 0x24bb4; 0x24bb8; 0x24c18; 0x25ca0; 0x253c0] 120%nat
               [KZRange (len - off) 8 (2^32); KZRange off 1 7; KZRange bc 0 64; KZRange len 9 (2^32); KZRange S 4096 (2^47);
                KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32);
                KZRange DST 4096 (2^47); KZRange dl 0 65535; KZRange DT 4096 (2^47);
                KZWr (SPV - 184) 40; KZDisj (SPV - 184) 40 S len; KZDisj DST dcap (SPV - 184) 40; KZDisj (SPV - 184) 40 DT 16388]
               [(S, len); (SPV - 184, 40)]
         | O8 : 8 <= _ |- _ =>
             kx_autoLx [0x2507c; 0x24bb4; 0x24bb8; 0x24c18; 0x25ca0; 0x253c0] 60%nat
               [KZRange (len - off) 8 (2^32); KZRange off 8 (2^32); KZRange bc 0 64; KZRange len 9 (2^32); KZRange S 4096 (2^47);
                KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32);
                KZRange DST 4096 (2^47); KZRange dl 0 65535; KZRange DT 4096 (2^47)]
               [(SPV - 184, 40)]
         | _ =>
             kx_autoLx [0x2507c; 0x24bb4; 0x24bb8; 0x24c18; 0x25ca0; 0x253c0] 30%nat
               [KZRange bc 0 64; KZRange S 4096 (2^47); KZRange SPV 4096 (2^47); KZRange j 0 (2^32); KZRange pe 0 (2^32);
                KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535]
               [(SPV - 184, 40)]
         end.
    all: x41_ck.
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x25ca0) _ _ _ _) => idtac | |- _ => kx_mem end.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24c18) _ _ _ _) => eapply (K _ j); try eassumption; lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24bb8) _ _ _ _) =>
             eapply (x41_g3a mb) with (jmin := j) (S := S) (bs := bs); try eassumption; try lia; try (rewrite SL; first [exact DJS | exact DJL | lia]);
             intros; eapply K; try eassumption; lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24bb4) _ _ _ _) =>
             eapply (x41_g3b mb) with (jmin := j) (S := S) (bs := bs); try eassumption; try lia; try (rewrite SL; first [exact DJS | exact DJL | lia]);
             intros; eapply K; try eassumption; lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2507c) _ _ _ _) =>
             eapply (x41_g3d mb) with (jmin := j) (S := S) (bs := bs); try eassumption; try lia; try (rewrite SL; first [exact DJS | exact DJL | lia]);
             intros; eapply K; try eassumption; lia
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?A) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x25ca0) _ _ _ _) =>
             replace A with (SPV + -184) by lia;
             pose proof huf_reload_proof as RL; unfold huf_reload_stmt, huf_reload_stmt_at, PHUF_RELOAD in RL;
             eapply evt_cut;
             [ eapply (RL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm (SPV + -184) S len bc (S + off) c pad bs);
               [exact MI | exact BD | exact BDA | exact SB | exact SL | lia | lia | lia | lia | lia | lia | lia | lia]
             | ];
             clear RL; cbv beta; intros ms' P; unfold huf_reload_post in P;
             destruct P as (a1' & a2' & a3' & a4' & a5' & a6' & m' & cont' & -> & MUc & WMc & MIc & BDc);
             unfold bitd_cells in BDc;
             lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
               replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end;
             eapply (x41_g3b mb m' j pe dl tl rsv S bs j cont' _ pad _);
             [ eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros; lia]
             | exact (wmono_trans usegs mb mm m' WM WMc) | exact MIc
             | eapply (stk_transport_disjoint usegs _ mm m' _ _ OUT MUc WMc); cbn [disjoint_from]; lia
             | eapply (bytes_at_transport usegs _ mm m' DT dtb DTB MUc); cbn [disjoint_from]; lia
             | eapply (rw_cells_transport usegs _ mm m' _ _ FA MUc WMc);
               cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia
             | exact BDc
             | eapply (bytes_at_transport usegs _ mm m' S bs SB MUc); cbn [disjoint_from]; lia
             | rewrite SL; exact DJS | rewrite SL; exact DJL | exact DJD | lia | lia | lia | exact HDL | exact HTL | exact HRSV
             | intros; eapply K; try eassumption; lia ]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_d3 : forall mb mm j pe off S len bs dl tl rsv bc (c : word) (pad : list byte)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
    BD3 mm c (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (DST + dcap <= S \/ S + len <= DST) ->
    (S + len <= lo \/ SPV <= S) -> (DT + 16388 <= lo \/ SPV <= DT) -> SPV mod 16 = 0 ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SINV off len bc -> 0 <= bc < 2^31 ->
    (forall mm' j' (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 c' b' p' : word),
        munch WD mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
        BD3 mm' c' b' pad p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> bytes_at usegs mm' S bs -> j <= j' ->
        evt usegs POST (ST 0x24c18 mm' y1 y5 y6 y7 y8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21
                         (Z_to_bv 64 (DST + j')) x23 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) x26 w8 y28 y29 y30 y31)) ->
    evt usegs POST (ST 0x2485c mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 dl) (Z_to_bv 64 (2^62)) x21
                     (Z_to_bv 64 (DST + j)) x23 (Z_to_bv 64 (DST + pe)) (Z_to_bv 64 (DT + 4)) x26 w8 x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm j pe off S len bs dl tl rsv bc c pad x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x26 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
      MU WM MI OUT DTB FA BD SB SL S0 S1 SL32 DJS DJL DJD SPA HJ HPE HDL HTL HRSV HS HB K.
    kx_autoLx [0x24acc; 0x24ab4; 0x24898; 0x253c0] 40%nat
      [KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange bc 0 (2^31 - 1);
       KZRange dl 0 65535; KZRange DT 4096 (2^47); KZRange SPV 4096 (2^47)]
      [(SPV - 184, 40)].
    all: x41_ck.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24acc) _ _ _ _) =>
             eapply (x41_e3 mb); try eassumption; try lia; intros; eapply K; try eassumption; lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24ab4) _ _ _ _) =>
             eapply (x41_g3c mb) with (jmin := j) (S := S) (bs := bs); try eassumption; try lia;
             try (rewrite SL; first [exact DJS | exact DJL | lia]);
             intros; eapply K; try eassumption; lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24898) _ _ _ _) =>
             subst dl; rewrite ?(neg_dl_sh tl rsv HTL);
             replace (DST + pe + -3) with (DST + pe - 3) by lia;
             replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) by (apply bv_eq; reflexivity);
             eapply (x41_l3 (Z.to_nat (pe - j)) mb); try eassumption; try lia; try reflexivity;
             intros; eapply K; try eassumption; lia
         end.
  Qed.

End DX41C3.
