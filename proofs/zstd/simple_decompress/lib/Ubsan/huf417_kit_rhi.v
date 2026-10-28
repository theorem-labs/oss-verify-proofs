(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f huf41_kit_x41ck huf417_kit_rlk.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41RHI.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).
  Notation BDAT mm A c b pad p st lm :=
    (rw_cells usegs mm A [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD1 mm c b pad p st lm := (BDAT mm (SPV + -376) c b pad p st lm).
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation WR1 := [(SPV - 512, SPV - 336)].
  Notation BD2 mm c b pad p st lm := (BDAT mm (SPV + -144) c b pad p st lm).
  Notation BD3 mm c b pad p st lm := (BDAT mm (SPV + -184) c b pad p st lm).
  Notation BD4 mm c b pad p st lm := (BDAT mm (SPV + -224) c b pad p st lm).
  Notation X41P := (RZ_huf_dx41f.X41P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation WDF := [(DST, DST + dcap); (SPV - 512, SPV - 336); (SPV - 224, SPV - 104)].
  Notation K4448 := (huf417_kit_rlk.K4448 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb).
  Notation K4608 := (huf417_kit_rlk.K4608 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb).
  Notation FRK mm j e1 dl S2 S3 S4 w0 w12 w15 w16 :=
    (rw_cells usegs mm (SPV + -512)
       [C8 w0; C8 (Z_to_bv 64 (DST + 3 * e1)); C8 (Z_to_bv 64 dl); C8 (Z_to_bv 64 (S4 + 8)); C8 (Z_to_bv 64 (S3 + 8));
        C8 (Z_to_bv 64 (S2 + 8)); C8 (Z_to_bv 64 (3 * e1)); C8 (Z_to_bv 64 (2 * e1)); C8 (Z_to_bv 64 (DST + dcap));
        C8 (Z_to_bv 64 (DST + e1)); C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 (DST + 2 * e1)); C8 w12;
        C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 w15; C8 w16]).
  Notation KBASE mm rest j e1 dl tl rsv S1 n1 b1 S2 n2 b2 S3 n3 b3 S4 n4 b4 :=
    (X41P mm rest /\ mem_inv usegs mm /\ stk usegs mm DST (DST + dcap) /\ bytes_at usegs mm DT dtb /\ huf_nb_ok false dtb tl /\
     SBUF mm S1 n1 b1 /\ SBUF mm S2 n2 b2 /\ SBUF mm S3 n3 b3 /\ SBUF mm S4 n4 b4 /\
     0 <= j /\ 0 <= e1 /\ j + 3 * e1 + 4 <= dcap /\ dl = tl + 256 * rsv /\ 1 <= tl <= 12 /\ 0 <= rsv <= 255).

  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Lemma x41_rhi_w : forall mm S1 n1 b1 o1 p1 S2 o2 (k1 : word) pad1
      (x1 x6 x7 x8 x9 x10 x11 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x31 : word)
      (w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word),
    8 <= o1 -> o1 + 8 <= n1 -> 0 <= p1 <= 56 -> 4096 <= S2 -> 0 <= o2 -> S2 + o2 < 2^47 ->
    mem_inv usegs mm ->
    FRA mm w0 w1 w2 w3 w4 (Z_to_bv 64 (S2 + 8)) w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
    BD1 mm k1 (Z_to_bv 64 p1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
    SBUF mm S1 n1 b1 ->
    (forall mm' (c y8 y9 y22 y23 y27 : word),
        8 <= o2 -> munch WR1 mm mm' -> wmono usegs mm mm' -> mem_inv usegs mm' ->
        FRA mm' w0 w1 w2 w3 w4 (Z_to_bv 64 (S2 + 8)) w6 w7 w8 w9 w10 w11 (Z_to_bv 64 0) w13 w14 c w16 ->
        BD1 mm' c (Z_to_bv 64 (Z.land p1 7)) pad1 (Z_to_bv 64 (S1 + (o1 - p1 / 8))) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
        evt usegs POST (ST 0x232f4 mm' x1 (Z_to_bv 64 (S2 + o2)) x6 c y8 y9 x10 x11 (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (Z.land p1 7))
                         x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 3) y22 y23 x24 x25 x26 y27 x23 x29 (Z_to_bv 64 (S1 + (o1 - p1 / 8))) x31)) ->
    (forall mm' (c y8 y9 y22 y23 y27 : word),
        o2 < 8 -> munch WR1 mm mm' -> wmono usegs mm mm' -> mem_inv usegs mm' ->
        FRA mm' w0 w1 w2 w3 w4 (Z_to_bv 64 (S2 + 8)) w6 w7 w8 w9 w10 w11 (Z_to_bv 64 0) w13 w14 c w16 ->
        BD1 mm' c (Z_to_bv 64 (Z.land p1 7)) pad1 (Z_to_bv 64 (S1 + (o1 - p1 / 8))) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
        evt usegs POST (ST 0x23394 mm' x1 (Z_to_bv 64 (S2 + o2)) x6 c y8 y9 x10 x11 (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (Z.land p1 7))
                         x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 3) y22 y23 x24 x25 x26 y27 x23 x29 (Z_to_bv 64 (S1 + (o1 - p1 / 8))) x31)) ->
    evt usegs POST (ST 0x2323c mm x1 (Z_to_bv 64 (S2 + o2)) x6 x7 x8 x9 x10 x11 (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 p1)
                     x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 (Z_to_bv 64 (S1 + o1)) x31).
  Proof using CTX.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm S1 n1 b1 o1 p1 S2 o2 k1 pad1 x1 x6 x7 x8 x9 x10 x11 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x31
      w0 w1 w2 w3 w4 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 O1 N1 HP1 RS2 RO2 RS2O MI FA BD SB KA KB.
    destruct SB as (B1 & L1 & R10 & R11 & R12 & D11 & D12).
    assert (K1 : S1 + n1 <= SPV - 912 \/ SPV <= S1) by (clear - D12 LO; lia).
    clear D11 D12.
    assert (MU : munch WR1 mm mm) by apply munch_refl.
    assert (WM : wmono usegs mm mm) by apply wmono_refl.
    kx_autoLx [0x232f4; 0x23394] 80%nat
      [KZRange o1 8 (2^32); KZRange (n1 - o1) 8 (2^32); KZRange p1 0 56; KZRange n1 0 (2^32);
       KZRange S1 4096 (2^47); KZRange (S1 + n1) 4096 (2^47); KZRange S2 4096 (2^47); KZRange o2 0 (2^47); KZRange (S2 + o2) 4096 (2^47);
       KZRange SPV 4096 (2^47); KZWr (SPV - 512) 136; KZWr (SPV - 376) 40;
       KZDisj (SPV - 512) 136 S1 n1; KZDisj (SPV - 376) 40 S1 n1; KZDisj (SPV - 512) 136 (SPV - 376) 40]
      [(S1, n1); (SPV - 512, 136); (SPV - 376, 40)].
    all: x41_ck.
    all: kx_mem.
    all: replace (p1 mod 2 ^ 64) with p1 in * by (rewrite Z.mod_small; lia).
    all: replace (S1 + (o1 + -1 * (p1 / 8))) with (S1 + (o1 - p1 / 8)) in * by lia.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x232f4) _ _ _ _) => eapply KA
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23394) _ _ _ _) => eapply KB
         end.
    all: try first [ eassumption | lia ].
  Qed.

  Lemma x41_rhi_k : forall rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0,
    K4448 rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 ->
    K4608 rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 ->
    forall mm (k1 k2 k3 k4 : word) o1 p1 o2 p2 o3 p3 o4 p4 (x7 x8 x9 x21 x22 x27 w12 w15 : word),
    X41P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb -> huf_nb_ok false dtb tl ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    0 <= j -> 0 <= e1 -> j + 3 * e1 + 4 <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    rw_cells usegs mm (SPV + -512)
       [C8 w0; C8 (Z_to_bv 64 (DST + 3 * e1)); C8 (Z_to_bv 64 dl); C8 (Z_to_bv 64 (S4 + 8)); C8 (Z_to_bv 64 (S3 + 8));
        C8 (Z_to_bv 64 (S2 + 8)); C8 (Z_to_bv 64 (3 * e1)); C8 (Z_to_bv 64 (2 * e1)); C8 (Z_to_bv 64 (DST + dcap));
        C8 (Z_to_bv 64 (DST + e1)); C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 (DST + 2 * e1)); C8 w12;
        C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 w15; C8 (Z_to_bv 64 (S4 + o4))] ->
    BD1 mm k1 (Z_to_bv 64 p1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
    BD2 mm k2 (Z_to_bv 64 p2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
    BD3 mm k3 (Z_to_bv 64 p3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
    BD4 mm k4 (Z_to_bv 64 p4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    x41_dinv o1 n1 p1 -> x41_dinv o2 n2 p2 -> x41_dinv o3 n3 p3 -> x41_dinv o4 n4 p4 -> 8 <= o1 ->
    evt usegs POST (ST 0x2323c mm (Z_to_bv 64 p2) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S3 + o3)) x7 x8 x9
                     (Z_to_bv 64 (-20)) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 p1)
                     (Z_to_bv 64 (DST + (j + 3 * e1 + 3))) (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1))
                     (Z_to_bv 64 p4) (Z_to_bv 64 p3) k2 x21 x22 k4 (Z_to_bv 64 (DST + (j + 3))) (Z_to_bv 64 (DT + 4))
                     (Z_to_bv 64 e1) x27 k1 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (S1 + o1)) k3).
  Proof using CTX DJ3.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 KA KB
      mm k1 k2 k3 k4 o1 p1 o2 p2 o3 p3 o4 p4 x7 x8 x9 x21 x22 x27 w12 w15
      PV MI OUT DTB NB SB1 SB2 SB3 SB4 HJ HE HJE HDL HTL HRSV FA HB1 HB2 HB3 HB4 D1 D2 D3 D4 O1.
    pose proof SB1 as SB1'. pose proof SB2 as SB2'.
    destruct SB1' as (B1 & L1 & R10 & R11 & R12 & _ & _). destruct SB2' as (B2 & L2 & R20 & R21 & R22 & _ & _).
    pose proof D1 as D1'. pose proof D2 as D2'. unfold x41_dinv in D1', D2'.
    eapply (x41_rhi_w mm S1 n1 b1 o1 p1 S2 o2 k1 pad1);
      try exact MI; try exact FA; try exact HB1; try exact SB1; try lia.
    all: intros mm' c y8 y9 y22 y23 y27 O2 MU WM MI' FA' BD1'.
    all: assert (MUF : munch WDF mm mm') by (eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia).
    all: assert (PV' : X41P mm' rest) by (eapply x41p_transport; [exact CTX | exact DJ3 | exact PV | exact MUF | exact WM]).
    all: assert (OUT' : stk usegs mm' DST (DST + dcap)) by (eapply (stk_transport_disjoint usegs _ mm mm' _ _ OUT MU WM); cbn [disjoint_from]; lia).
    all: assert (DTB' : bytes_at usegs mm' DT dtb) by (eapply (bytes_at_transport usegs _ mm mm' DT dtb DTB MU); cbn [disjoint_from]; lia).
    all: assert (SB1n : SBUF mm' S1 n1 b1) by (eapply sbuf_transport; [exact CTX | exact DJ3 | exact SB1 | exact MUF]).
    all: assert (SB2n : SBUF mm' S2 n2 b2) by (eapply sbuf_transport; [exact CTX | exact DJ3 | exact SB2 | exact MUF]).
    all: assert (SB3n : SBUF mm' S3 n3 b3) by (eapply sbuf_transport; [exact CTX | exact DJ3 | exact SB3 | exact MUF]).
    all: assert (SB4n : SBUF mm' S4 n4 b4) by (eapply sbuf_transport; [exact CTX | exact DJ3 | exact SB4 | exact MUF]).
    all: assert (BD2' : BD2 mm' k2 (Z_to_bv 64 p2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)))
           by (eapply (rw_cells_transport usegs _ mm mm' _ _ HB2 MU WM);
               cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    all: assert (BD3' : BD3 mm' k3 (Z_to_bv 64 p3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)))
           by (eapply (rw_cells_transport usegs _ mm mm' _ _ HB3 MU WM);
               cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    all: assert (BD4' : BD4 mm' k4 (Z_to_bv 64 p4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)))
           by (eapply (rw_cells_transport usegs _ mm mm' _ _ HB4 MU WM);
               cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    all: assert (LE7 : Z.land p1 7 = p1 mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones; [reflexivity | lia]).
    all: assert (RS1 : x41_rls 0 (o1 - p1 / 8) n1 (Z.land p1 7))
           by (rewrite LE7; pose proof (Z.mod_pos_bound p1 8 ltac:(lia)) as LU;
               assert (0 <= p1 / 8 <= 7) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia);
               unfold x41_rls, x41_hinv, RZ_huf_dx41.SINV; repeat split; try lia; intros; right; lia).
    all: assert (KBN : X41P mm' rest /\ mem_inv usegs mm' /\ stk usegs mm' DST (DST + dcap) /\ bytes_at usegs mm' DT dtb /\
                       huf_nb_ok false dtb tl /\ SBUF mm' S1 n1 b1 /\ SBUF mm' S2 n2 b2 /\ SBUF mm' S3 n3 b3 /\ SBUF mm' S4 n4 b4 /\
                       0 <= j /\ 0 <= e1 /\ j + 3 * e1 + 4 <= dcap /\ dl = tl + 256 * rsv /\ 1 <= tl <= 12 /\ 0 <= rsv <= 255)
           by (refine (conj PV' (conj MI' (conj OUT' (conj DTB' (conj NB (conj SB1n (conj SB2n (conj SB3n (conj SB4n _)))))))));
               lia).
    - eapply (KA mm' c (Z.land p1 7) (o1 - p1 / 8) 0 k2 k3 k4 p2 o2 p3 o3 p4 o4);
        first [ exact KBN | exact FA' | exact BD1' | exact BD2' | exact BD3' | exact BD4' | exact RS1 | exact D2 | exact D3 | exact D4 | lia ].
    - assert (RS2 : x41_rls 3 o2 n2 p2)
        by (unfold x41_dinv in D2; unfold x41_rls, x41_hinv, RZ_huf_dx41.SINV; repeat split; try lia; intros; lia).
      eapply (KB mm' c k2 (Z.land p1 7) (o1 - p1 / 8) 0 p2 o2 3 k3 k4 p3 o3 p4 o4);
        first [ exact KBN | exact FA' | exact BD1' | exact BD2' | exact BD3' | exact BD4' | exact RS1 | exact RS2 | exact D3 | exact D4 | lia ].
  Qed.

  Lemma x41_r_hi : forall rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0,
    K4448 rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 ->
    K4608 rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 ->
    forall mm (k1 k2 k3 k4 : word) p1 o1 p2 o2 p3 o3 p4 o4 (x7 x8 x9 x21 x22 x27 w12 w15 : word),
      KBASE mm rest j e1 dl tl rsv S1 n1 b1 S2 n2 b2 S3 n3 b3 S4 n4 b4 ->
      FRK mm j e1 dl S2 S3 S4 w0 w12 w15 (Z_to_bv 64 (S4 + o4)) ->
      BD1 mm k1 (Z_to_bv 64 p1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
      BD2 mm k2 (Z_to_bv 64 p2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
      BD3 mm k3 (Z_to_bv 64 p3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
      BD4 mm k4 (Z_to_bv 64 p4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
      x41_dinv o1 n1 p1 -> x41_dinv o2 n2 p2 -> x41_dinv o3 n3 p3 -> x41_dinv o4 n4 p4 -> 8 <= o1 ->
      evt usegs POST (ST 0x2323c mm (Z_to_bv 64 p2) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (S3 + o3)) x7 x8 x9
                       (Z_to_bv 64 (-20)) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 p1) (Z_to_bv 64 (DST + (j + 3 * e1 + 3)))
                       (Z_to_bv 64 (2^62)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (-1)) (Z_to_bv 64 p4) (Z_to_bv 64 p3)
                       k2 x21 x22 k4 (Z_to_bv 64 (DST + (j + 3))) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 e1) x27
                       k1 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (S1 + o1)) k3).
  Proof using CTX DJ3.
    intros rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 KA KB
      mm k1 k2 k3 k4 p1 o1 p2 o2 p3 o3 p4 o4 x7 x8 x9 x21 x22 x27 w12 w15
      (PV & MI & OUT & DTB & NB & SB1 & SB2 & SB3 & SB4 & HJ & HE & HJE & HDL & HTL & HRSV) FA HB1 HB2 HB3 HB4 D1 D2 D3 D4 O1.
    exact (x41_rhi_k rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 KA KB
             mm k1 k2 k3 k4 o1 p1 o2 p2 o3 p3 o4 p4 x7 x8 x9 x21 x22 x27 w12 w15
             PV MI OUT DTB NB SB1 SB2 SB3 SB4 HJ HE HJE HDL HTL HRSV FA HB1 HB2 HB3 HB4 D1 D2 D3 D4 O1).
  Qed.
End DX41RHI.
