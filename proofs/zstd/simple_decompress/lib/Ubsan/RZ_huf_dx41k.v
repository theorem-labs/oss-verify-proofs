(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2 ZdWalkKit ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f RZ_huf_dx41g RZ_huf_dx41j huf41_kit_x41ck huf411_kit_rs.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41K.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis BITINIT : bit_init_stmt.
  Hypothesis SPVA : rsk_al SPV 16.
  Hypothesis DTA : rsk_al DT 4.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).


  Notation BD1 mm c b pad p st lm := (rw_cells usegs mm (SPV + -376) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD2 mm c b pad p st lm := (rw_cells usegs mm (SPV + -144) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD3 mm c b pad p st lm := (rw_cells usegs mm (SPV + -184) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD4 mm c b pad p st lm := (rw_cells usegs mm (SPV + -224) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation SINV := RZ_huf_dx41.SINV.

  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation X41P := (RZ_huf_dx41f.X41P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation HINV := RZ_huf_dx41g.HINV.

  (* [comment removed for export] *)
  Lemma x41_einv_gen : forall mm rest csA cs1 cs2 cs3 cs4,
    X41P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) ->
    rw_cells usegs mm (SPV + -512) csA -> cells_size csA = 136%nat ->
    rw_cells usegs mm (SPV + -376) cs1 -> cells_size cs1 = 40%nat ->
    rw_cells usegs mm (SPV + -144) cs2 -> cells_size cs2 = 40%nat ->
    rw_cells usegs mm (SPV + -184) cs3 -> cells_size cs3 = 40%nat ->
    rw_cells usegs mm (SPV + -224) cs4 -> cells_size cs4 = 40%nat -> EINV mm.
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest csA cs1 cs2 cs3 cs4 (SV & STK & RS & MU & WM) MI OUT FA SZA B1 SZ1 B2 SZ2 B3 SZ3 B4 SZ4.
    pose proof (stk_of_rw_cells usegs mm _ _ FA) as HA.
    pose proof (stk_of_rw_cells usegs mm _ _ B1) as H1.
    pose proof (stk_of_rw_cells usegs mm _ _ RS) as HR.
    pose proof (stk_of_rw_cells usegs mm _ _ B4) as H4.
    pose proof (stk_of_rw_cells usegs mm _ _ B3) as H3.
    pose proof (stk_of_rw_cells usegs mm _ _ B2) as H2.
    rewrite SZA in HA. rewrite SZ1 in H1. rewrite SZ2 in H2. rewrite SZ3 in H3. rewrite SZ4 in H4.
    cbn [cells_size csize Nat.add] in HR.
    change (Z.of_nat 136) with 136 in HA. change (Z.of_nat 40) with 40 in H1, H2, H3, H4. change (Z.of_nat 112) with 112 in HR.
    replace (SPV + -512 + 136) with (SPV + -376) in HA by lia.
    replace (SPV + -376 + 40) with (SPV + -336) in H1 by lia.
    replace (SPV + -336 + 112) with (SPV + -224) in HR by lia.
    replace (SPV + -224 + 40) with (SPV + -184) in H4 by lia.
    replace (SPV + -184 + 40) with (SPV + -144) in H3 by lia.
    replace (SPV + -144 + 40) with (SPV + -104) in H2 by lia.
    unfold RZ_huf_dx41.EINV. split; [exact OUT|]. split; [exact SV|]. split; [|split; [exact MU|split; [exact WM|exact MI]]].
    eapply (stk_merge usegs mm lo (SPV + -144)); [|exact H2|lia].
    eapply (stk_merge usegs mm lo (SPV + -184)); [|exact H3|lia].
    eapply (stk_merge usegs mm lo (SPV + -224)); [|exact H4|lia].
    eapply (stk_merge usegs mm lo (SPV + -336)); [|exact HR|lia].
    eapply (stk_merge usegs mm lo (SPV + -376)); [|exact H1|lia].
    eapply (stk_merge usegs mm lo (SPV + -512)); [exact STK|exact HA|lia].
  Qed.

  Lemma x41_bitd_hinv : forall m BD S n cont bc pad, 1 <= bc <= 64 -> (8 <= n -> bc <= 8) -> 0 <= n ->
    rw_cells usegs m BD (bitd_cells cont (Z_to_bv 64 bc) pad (bitd_ptr S n) S) ->
    exists o, HINV o n bc /\
      rw_cells usegs m BD [C8 cont; C4 (Z_to_bv 64 bc); CB 4 pad; C8 (Z_to_bv 64 (S + o)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))].
  Proof.
    intros m BD S n cont bc pad HB1 HB2 HN BDC. unfold bitd_cells, bitd_ptr in BDC. revert BDC.
    destruct (8 <=? n) eqn:E8; [apply Z.leb_le in E8 | apply Z.leb_gt in E8]; intro BDC.
    - exists (n - 8). split; [unfold RZ_huf_dx41g.HINV; lia|]. replace (S + (n - 8)) with (S + n - 8) by lia. exact BDC.
    - exists 0. split; [unfold RZ_huf_dx41g.HINV; lia|]. replace (S + 0) with S by lia. exact BDC.
  Qed.

  Lemma x41_i4 : forall mm rest e1 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 dl tl rsv
      (k1 k2 k3 : word) pad1 pad2 pad3 junk4
      (x1 x5 x6 x7 x8 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w10 w12 w15 w16 : word),
    X41P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb -> huf_nb_ok false dtb tl ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 (Z_to_bv 64 (DST + e1)) w10 (Z_to_bv 64 (DST + 2 * e1)) w12 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) w15 w16 ->
    BD1 mm k1 (Z_to_bv 64 c1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
    BD2 mm k2 (Z_to_bv 64 c2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
    BD3 mm k3 (Z_to_bv 64 c3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
    rw_cells usegs mm (SPV + -224) [CB 40 junk4] ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    HINV o1 n1 c1 -> HINV o2 n2 c2 -> HINV o3 n3 c3 ->
    0 <= e1 -> 3 * e1 <= dcap -> e1 = (dcap + 3) / 4 -> 6 <= dcap ->
    dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    evt usegs POST (ST 0x22d1c mm x1 x5 x6 x7 x8 (Z_to_bv 64 (-120)) (Z_to_bv 64 (SPV + -224)) (Z_to_bv 64 S4) (Z_to_bv 64 n4) x13 x14 x15 x16 x17
                     x18 (Z_to_bv 64 dl) x20 x21 x22 x23 (Z_to_bv 64 (DST + 3 * e1)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 e1) (Z_to_bv 64 (DST + dcap)) x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest e1 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 dl tl rsv k1 k2 k3 pad1 pad2 pad3 junk4 x1 x5 x6 x7 x8 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w10 w12 w15 w16 PV MI OUT DTB NBOK FA BD1 BD2 BD3 BJ4 SB1 SB2 SB3 SB4 HI1 HI2 HI3 HE1 HE3 HE4 HDC HDL HTL HRSV.
    kx_autoLx [0x25a0c] 10%nat [KZRange SPV 4096 (2^47)] (@nil (Z * Z)).
    destruct PV as (SV & STK & RS & MU & WM).
    destruct SB1 as (B1 & SF1). destruct SB2 as (B2 & SF2). destruct SB3 as (B3 & SF3). destruct SB4 as (B4 & SF4).
    clear KXK KXA KXRD.
    assert (BDA : (SPV + -224) mod 8 = 0) by (pose proof (rsk_al_e _ _ SPVA) as SPA; clear - SPA; lia).
    eapply evt_cut.
    { eapply (BITINIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm (SPV + -224) S4 n4 b4 junk4);
        first [exact BDA | eassumption | clear BDA; lia]. }
    unfold bit_init_post. clear BDA. post_call usegs mm.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
        assert (PV1 : X41P m1 rest) by exact (conj SV (conj STK (conj RS (conj MU WM))));
        assert (SB1' : SBUF m1 S1 n1 b1) by exact (conj B1 SF1);
        assert (SB2' : SBUF m1 S2 n2 b2) by exact (conj B2 SF2);
        assert (SB3' : SBUF m1 S3 n3 b3) by exact (conj B3 SF3);
        assert (SB4' : SBUF m1 S4 n4 b4) by exact (conj B4 SF4)
    end.
    lazymatch goal with
    | H : (_ = n4 /\ _) \/ _ |- _ => destruct H as [(HR & HN1 & cont & bc & pad & HB1 & HB2 & BDC) | (HER & HRB & bs & BDC)]
    end.
    - lazymatch type of HR with ?r = n4 => subst r end.
      destruct (x41_bitd_hinv _ _ _ _ _ _ _ HB1 HB2 ltac:(lia) BDC) as (o4 & HI4 & BDK). clear BDC.
      kx_autoLx [0x23594; 0x22d24] 10%nat [KZRange n4 1 (2^32); KZRange SPV 4096 (2^47)] (@nil (Z * Z)).
      all: lazymatch goal with
           | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22d24) _ _ ?m1 _) =>
               eapply (x41_m0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 SPVA DTA m1 rest e1 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 bc dl tl rsv k1 k2 k3 cont pad1 pad2 pad3 pad)
           | _ => exfalso; lia
           end.
      all: first [ exact PV1 | exact SB1' | exact SB2' | exact SB3' | exact SB4' | exact BDK | eassumption | lia | unfold RZ_huf_dx41g.HINV; lia ].
    - lazymatch type of HER with zd_is_error ?r = true =>
        assert (HRG : 2^64 - 119 <= r) by (unfold zd_is_error, ZE_maxCode in HER; apply Z.ltb_lt in HER; lia);
        kx_autoLx [0x23594; 0x22d24] 10%nat [KZRange r (2^64 - 119) (2^64 - 1); KZRange SPV 4096 (2^47)] (@nil (Z * Z))
      end.
      all: lazymatch goal with
           | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23594) _ _ ?m2 _) =>
               eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX m2);
               [ eapply (x41_einv_gen m2 rest);
                 first [exact PV1 | eassumption | reflexivity]
               | right; exact (conj HER HRB) ]
           | _ => exfalso; lia
           end.
  Qed.

End DX41K.
