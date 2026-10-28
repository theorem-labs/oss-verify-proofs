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

Section DX41RL4.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.

  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

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
  Notation BD2 mm c b pad p st lm := (BDAT mm (SPV + -144) c b pad p st lm).
  Notation BD3 mm c b pad p st lm := (BDAT mm (SPV + -184) c b pad p st lm).
  Notation BD4 mm c b pad p st lm := (BDAT mm (SPV + -224) c b pad p st lm).
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation X41P := (RZ_huf_dx41f.X41P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation WR4 := [(SPV - 512, SPV - 376); (SPV - 224, SPV - 184)].
  Notation WDF := [(DST, DST + dcap); (SPV - 512, SPV - 336); (SPV - 224, SPV - 104)].
  Notation K4796 := (huf417_kit_rlk.K4796 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb).
  Notation K5004 := (huf417_kit_rlk.K5004 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb).

  Ltac rl4_side := lazymatch goal with |- evt _ _ _ => idtac | |- _ => try solve [lia] end.
  Ltac rl4_res :=
    match goal with
    | SB : bytes_at usegs _ _ _ |- sc_resid _ _ _ (SCReadBase _ _ _ _) => kx_rd SB
    | |- sc_resid _ _ _ _ => kx_z
    | |- _ => idtac
    end.
  Ltac rl4_post := lazymatch goal with |- evt _ _ _ => kx_ev_ranges; kx_mem; kx_srlw; kx_land_ranges; kx_strip_mod | |- _ => idtac end.
  Ltac rl4_walk S len off bc :=
    kx_autoLx [144672] 80%nat
      [KZRange bc 0 64; KZRange off 8 (2^32); KZRange (len - off) 8 (2^32); KZRange len 16 (2^32); KZRange S 4096 (2^47);
       KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47);
       KZWr (SPV - 512) 136; KZWr (SPV - 224) 40; KZDisj (SPV - 512) 136 S len; KZDisj (SPV - 224) 40 S len;
       KZDisj (SPV - 224) 40 (SPV - 512) 136]
      [(S, len); (SPV - 512, 136); (SPV - 224, 40)].

  Lemma x41_rl4_w : forall mb mm S len bs off bc (c0 b0 p0 st lm : word) pad
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : word),
    munch WR4 mb mm -> wmono usegs mb mm -> mem_inv usegs mm ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 (S + off)) ->
    BD4 mm c0 b0 pad p0 st lm ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 -> (S + len <= lo \/ SPV <= S) ->
    8 <= off -> off + 8 <= len -> 0 <= bc <= 64 ->
    (forall mm' P bc' (c' y7 y8 y12 y20 y27 : word),
        munch WR4 mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 P) ->
        BD4 mm' c' (Z_to_bv 64 bc') pad (Z_to_bv 64 P) st lm -> bytes_at usegs mm' S bs ->
        P = S + off - bc / 8 -> S <= P -> P + 8 <= S + len -> 0 <= bc' <= 7 ->
        evt usegs POST (ST 144672 mm' x1 x5 x6 y7 y8 (Z_to_bv 64 0) x10 x11 y12 x13 x14 x15 x16 (Z_to_bv 64 (-1)) (Z_to_bv 64 bc')
                           x19 y20 x21 x22 x23 x24 x25 x26 y27 c' x29 x30 x31)) ->
    evt usegs POST (ST 144464 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 bc) x19 (Z_to_bv 64 (S + off))
                       x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using CTX DJ3.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mb mm S len bs off bc c0 b0 p0 st lm pad
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 MU WM MI FA BD SB SL S0 S1 SL32 DJK HO HOL HB K.
    assert (QB : 0 <= bc / 8 <= 8) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    rl4_walk S len off bc.
    all: rl4_side.
    all: x41_ck.
    all: rl4_res.
    all: rl4_post.
    all: try replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) by (apply Z_to_bv_eqm; reflexivity).
    all: eapply K; try eassumption; try lia.
  Qed.

  Lemma x41_rl4 : forall rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0,
    K5004 rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 ->
    K4796 rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0.
  Proof using CTX DJ3.
    pose proof CTX as CTX'. destruct CTX' as (LO & SPB & RD & OS1 & DL & RT & DJ2).
    intros rest j e1 dl tl rsv S1 n1 S2 n2 S3 n3 S4 n4 b1 b2 b3 b4 pad1 pad2 pad3 pad4 w0 KN.
    unfold huf417_kit_rlk.K4796.
    intros mm K1 K2 K3 c1 o1 R1 c2 o2 R2 c3 o3 R3 k4 p4 o4 x7 x8 x9 x12 x27 x28 KB FA HB1 HB2 HB3 HB4 RS1 RS2 RS3 D4 O4.
    destruct KB as (PV & MI & OUT & DTB & NB & SB1 & SB2 & SB3 & SB4 & HJ & HE & HJE & HDL & HTL & HRSV).
    pose proof SB4 as SB4'. destruct SB4' as (B4 & L4 & R40 & R41 & R42 & D41 & D42).
    pose proof D4 as D4'. unfold x41_dinv in D4'.
    assert (QB : 0 <= p4 / 8 <= 7) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    eapply (x41_rl4_w mm mm S4 n4 b4 o4 p4 k4 (Z_to_bv 64 p4) (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) pad4).
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | |- munch _ _ _ => apply munch_refl
         | |- wmono _ _ _ => apply wmono_refl
         | |- _ => first [ exact MI | exact FA | exact HB4 | exact B4 | exact L4 | exact D42 | lia ]
         end.
    intros mm' P bc' c' y7 y8 y12 y20 y27 MU WM MI' FA' BD' SB' HP HSP HPL HBC.
    assert (MUF : munch WDF mm mm') by (eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia).
    assert (PV' : X41P mm' rest) by (eapply x41p_transport; [exact CTX | exact DJ3 | exact PV | exact MUF | exact WM]).
    assert (OUT' : stk usegs mm' DST (DST + dcap)) by (eapply (stk_transport_disjoint usegs _ mm mm' _ _ OUT MU WM); cbn [disjoint_from]; lia).
    assert (DTB' : bytes_at usegs mm' DT dtb) by (eapply (bytes_at_transport usegs _ mm mm' DT dtb DTB MU); cbn [disjoint_from]; lia).
    assert (SB1n : SBUF mm' S1 n1 b1) by (eapply sbuf_transport; [exact CTX | exact DJ3 | exact SB1 | exact MUF]).
    assert (SB2n : SBUF mm' S2 n2 b2) by (eapply sbuf_transport; [exact CTX | exact DJ3 | exact SB2 | exact MUF]).
    assert (SB3n : SBUF mm' S3 n3 b3) by (eapply sbuf_transport; [exact CTX | exact DJ3 | exact SB3 | exact MUF]).
    assert (SB4n : SBUF mm' S4 n4 b4) by (eapply sbuf_transport; [exact CTX | exact DJ3 | exact SB4 | exact MUF]).
    assert (BD1' : BD1 mm' K1 (Z_to_bv 64 c1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)))
      by (eapply (rw_cells_transport usegs _ mm mm' _ _ HB1 MU WM);
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    assert (BD2' : BD2 mm' K2 (Z_to_bv 64 c2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)))
      by (eapply (rw_cells_transport usegs _ mm mm' _ _ HB2 MU WM);
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    assert (BD3' : BD3 mm' K3 (Z_to_bv 64 c3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)))
      by (eapply (rw_cells_transport usegs _ mm mm' _ _ HB3 MU WM);
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    assert (RS4 : x41_rls 0 (P - S4) n4 bc')
      by (unfold x41_rls, x41_hinv, RZ_huf_dx41.SINV; repeat split; try lia; intros; right; lia).
    assert (KBN : X41P mm' rest /\ mem_inv usegs mm' /\ stk usegs mm' DST (DST + dcap) /\ bytes_at usegs mm' DT dtb /\
                  huf_nb_ok false dtb tl /\ SBUF mm' S1 n1 b1 /\ SBUF mm' S2 n2 b2 /\ SBUF mm' S3 n3 b3 /\ SBUF mm' S4 n4 b4 /\
                  0 <= j /\ 0 <= e1 /\ j + 3 * e1 + 4 <= dcap /\ dl = tl + 256 * rsv /\ 1 <= tl <= 12 /\ 0 <= rsv <= 255)
      by (refine (conj PV' (conj MI' (conj OUT' (conj DTB' (conj NB (conj SB1n (conj SB2n (conj SB3n (conj SB4n _)))))))));
          lia).
    replace (Z_to_bv 64 P) with (Z_to_bv 64 (S4 + (P - S4))) in FA', BD' by (f_equal; lia).
    eapply (KN mm' K1 K2 K3 c' c1 o1 R1 c2 o2 R2 c3 o3 R3 bc' (P - S4) 0 y7 y8 y12 y20 y27);
      first [ exact KBN | exact FA' | exact BD1' | exact BD2' | exact BD3' | exact BD' | exact RS1 | exact RS2 | exact RS3 | exact RS4 ].
  Qed.
End DX41RL4.
