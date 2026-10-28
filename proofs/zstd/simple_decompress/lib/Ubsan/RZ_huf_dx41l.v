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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f RZ_huf_dx41g RZ_huf_dx41j RZ_huf_dx41k huf41_kit_x41ck huf411_kit_rs.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41L.
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
  Ltac kreg i E :=
    lazymatch goal with
    | |- evt _ _ (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20
                          ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) _ _ _ _ _ _) =>
        let xs := constr:([x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20;
                           x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31]) in
        let j := eval vm_compute in (pred i) in
        let xi := kx_nth j xs in
        lazymatch xi with
        | Z_to_bv 64 E => idtac
        | Z_to_bv 64 ?X => replace (Z_to_bv 64 X) with (Z_to_bv 64 E) in * by (apply zbv_eqm; first [reflexivity | f_equal; lia | lia])
        end
    end.

  Lemma x41_i3 : forall mm rest e1 n tot S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 S4 n4 b4 dl tl rsv
      (k1 k2 : word) pad1 pad2 junk3 junk4
      (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w10 w12 w15 w16 : word),
    X41P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb -> huf_nb_ok false dtb tl ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 (Z_to_bv 64 (DST + e1)) w10 (Z_to_bv 64 (DST + 2 * e1)) w12 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) w15 w16 ->
    BD1 mm k1 (Z_to_bv 64 c1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
    BD2 mm k2 (Z_to_bv 64 c2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
    rw_cells usegs mm (SPV + -184) [CB 40 junk3] -> rw_cells usegs mm (SPV + -224) [CB 40 junk4] ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    HINV o1 n1 c1 -> HINV o2 n2 c2 ->
    S4 = S3 + n3 -> n4 = n - tot -> 0 <= tot <= n -> n < 2^32 ->
    0 <= e1 -> 3 * e1 <= dcap -> e1 = (dcap + 3) / 4 -> 6 <= dcap ->
    dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    evt usegs POST (ST 0x22d04 mm x1 x5 x6 x7 (Z_to_bv 64 tot) x9 (Z_to_bv 64 (SPV + -184)) (Z_to_bv 64 S3) (Z_to_bv 64 n3) x13 x14 x15 x16 x17
                     (Z_to_bv 64 n) (Z_to_bv 64 dl) (Z_to_bv 64 S3) (Z_to_bv 64 n3) x22 x23 (Z_to_bv 64 (DST + 3 * e1)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 e1) (Z_to_bv 64 (DST + dcap)) x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest e1 n tot S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 S4 n4 b4 dl tl rsv k1 k2 pad1 pad2 junk3 junk4 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w10 w12 w15 w16 PV MI OUT DTB NBOK FA BD1 BD2 BJ3 BJ4 SB1 SB2 SB3 SB4 HI1 HI2 HS4 HN4 HTOT HN HE1 HE3 HE4 HDC HDL HTL HRSV.
    kx_autoLx [0x25a0c] 10%nat [KZRange SPV 4096 (2^47)] (@nil (Z * Z)).
    destruct PV as (SV & STK & RS & MU & WM).
    destruct SB1 as (B1 & SF1). destruct SB2 as (B2 & SF2). destruct SB3 as (B3 & SF3). destruct SB4 as (B4 & SF4).
    clear KXK KXA KXRD.
    assert (BDA : (SPV + -184) mod 8 = 0) by (pose proof (rsk_al_e _ _ SPVA) as SPA; clear - SPA; lia).
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (BITINIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm (SPV + -184) S3 n3 b3 junk3);
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
    | H : (_ = n3 /\ _) \/ _ |- _ => destruct H as [(HR & HN1 & cont & bc & pad & HB1 & HB2 & BDC) | (HER & HRB & bs & BDC)]
    end.
    - lazymatch type of HR with ?r = n3 => subst r end.
      destruct (RZ_huf_dx41k.x41_bitd_hinv _ _ _ _ _ _ _ HB1 HB2 ltac:(lia) BDC) as (o3 & HI3 & BDK). clear BDC.
      kx_autoLx [0x23594; 0x22d1c] 10%nat [KZRange n3 1 (2^32); KZRange SPV 4096 (2^47); KZRange n 0 (2^32); KZRange tot 0 (2^32)] (@nil (Z * Z)).
      all: lazymatch goal with
           | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22d1c) _ _ ?m1 _) =>
               kreg 9%nat (-120); kreg 10%nat (SPV + -224); kreg 11%nat S4; kreg 12%nat n4;
               eapply (x41_i4 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 BITINIT SPVA DTA m1 rest e1 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 bc S4 n4 b4 dl tl rsv k1 k2 cont pad1 pad2 pad junk4)
           | _ => exfalso; lia
           end.
      all: first [ exact PV1 | exact SB1' | exact SB2' | exact SB3' | exact SB4' | exact BDK | eassumption | lia | unfold RZ_huf_dx41g.HINV; lia ].
    - lazymatch type of HER with zd_is_error ?r = true =>
        assert (HRG : 2^64 - 119 <= r) by (unfold zd_is_error, ZE_maxCode in HER; apply Z.ltb_lt in HER; lia);
        kx_autoLx [0x23594; 0x22d1c] 10%nat [KZRange r (2^64 - 119) (2^64 - 1); KZRange SPV 4096 (2^47)] (@nil (Z * Z))
      end.
      all: lazymatch goal with
           | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23594) _ _ ?m2 _) =>
               eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX m2);
               [ eapply (RZ_huf_dx41k.x41_einv_gen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX m2 rest);
                 first [exact PV1 | eassumption | reflexivity]
               | right; exact (conj HER HRB) ]
           | _ => exfalso; lia
           end.
  Qed.

End DX41L.
