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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_dx42_0b RZ_huf_dx41f RZ_huf_dx41g RZ_huf_dx42_5 RZ_huf_dx42_9 huf411_kit_rs huf421_kit_c1_entry huf42_2_bi_kit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_10.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis NBOK : huf_nb_ok true dtb tl.
  Hypothesis BITINIT : bit_init_stmt.
  Hypothesis SPVA : rsk_al SPV 16.
  Hypothesis DTA : rsk_al DT 4.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -912)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -912) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).
  Notation SINV := RZ_huf_dx41.SINV.
  Notation WD4 := [(DST, DST + dcap); (SPV - 776, SPV - 736)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -776) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD3 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -736) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD2 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -696) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD1 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -656) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).

  Notation WDF := [(DST, DST + dcap); (SPV - 912, SPV - 616)].
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation X42P := (RZ_huf_dx42_5.X42P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x42p_transport := (RZ_huf_dx42_5.x42p_transport ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX).
  Notation sbuf_transport := (RZ_huf_dx42_5.x42_sbuf_transport SPV DST dcap DT lo dtb CTX).
  Notation x42_ret := (RZ_huf_dx42_5.x42_ret ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation HINV := RZ_huf_dx41g.HINV.
  Notation x42_m0 := (RZ_huf_dx42_9.x42_m0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).

  Lemma x42_i4 : forall mm rest e1 S1 n1 b1 k1 c1 pad1 S2 n2 b2 k2 c2 pad2 S3 n3 b3 k3 c3 pad3 S4 n4 b4 dl r
      (y8 y19 y24 y25 y26 y27 : Z)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w14 : word),
    X42P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 (Z_to_bv 64 (DST + e1)) (Z_to_bv 64 (DST + 2 * e1)) w14
        (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DT + 4)) ->
    rw_cells usegs mm (SPV + -656) (bitd_cells k1 (Z_to_bv 64 c1) pad1 (bitd_ptr S1 n1) S1) ->
    rw_cells usegs mm (SPV + -696) (bitd_cells k2 (Z_to_bv 64 c2) pad2 (bitd_ptr S2 n2) S2) ->
    rw_cells usegs mm (SPV + -736) (bitd_cells k3 (Z_to_bv 64 c3) pad3 (bitd_ptr S3 n3) S3) ->
    ((r = n4 /\ 1 <= n4 /\ exists k4 c4 pad4, 1 <= c4 <= 64 /\ (8 <= n4 -> c4 <= 8) /\
        rw_cells usegs mm (SPV + -776) (bitd_cells k4 (Z_to_bv 64 c4) pad4 (bitd_ptr S4 n4) S4))
     \/ (zd_is_error r = true /\ r < 2^64 /\ exists bs, rw_cells usegs mm (SPV + -776) [CB 40 bs])) ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    1 <= c1 <= 64 -> (8 <= n1 -> c1 <= 8) -> 1 <= c2 <= 64 -> (8 <= n2 -> c2 <= 8) -> 1 <= c3 <= 64 -> (8 <= n3 -> c3 <= 8) ->
    0 <= e1 -> 3 * e1 <= dcap -> dcap <= 4 * e1 -> dl = tl + 256 * rsv ->
    y8 mod 2^64 = DST mod 2^64 -> y19 mod 2^64 = (-120) mod 2^64 ->
    y24 mod 2^64 = dl mod 2^64 -> y25 mod 2^64 = (DST + 2 * e1) mod 2^64 -> y26 mod 2^64 = dcap mod 2^64 ->
    y27 mod 2^64 = (DST + 3 * e1) mod 2^64 ->
    evt usegs POST (ST 0x25f4c mm x1 x5 x6 x7 (Z_to_bv 64 y8) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 y19) x20
       x21 x22 x23 (Z_to_bv 64 y24) (Z_to_bv 64 y25) (Z_to_bv 64 y26) (Z_to_bv 64 y27) x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest e1 S1 n1 b1 k1 c1 pad1 S2 n2 b2 k2 c2 pad2 S3 n3 b3 k3 c3 pad3 S4 n4 b4 dl r
      y8 y19 y24 y25 y26 y27
      x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w14
      PV MI OUT DTB FA BD1 BD2 BD3 HP SB1 SB2 SB3 SB4 HC1 HC18 HC2 HC28 HC3 HC38 HE1 HE3 HE4 HDL
      H8 H19 H24 H25 H26 H27.
    rewrite (zbv_eqm _ _ H8), (zbv_eqm _ _ H19), (zbv_eqm _ _ H24), (zbv_eqm _ _ H25), (zbv_eqm _ _ H26), (zbv_eqm _ _ H27).
    clear H8 H19 H24 H25 H26 H27.
    pose proof SB4 as (_ & _ & _ & _ & N4 & _).
    destruct HP as [(HR & HN4 & k4 & c4 & pad4 & HC4 & HC48 & BD4) | (HER & HRB & bs & BD4)].
    - subst r.
      destruct (bi_bd_hinv mm _ k1 c1 pad1 S1 n1 HC1 HC18 BD1) as (o1 & HI1 & BD1').
      destruct (bi_bd_hinv mm _ k2 c2 pad2 S2 n2 HC2 HC28 BD2) as (o2 & HI2 & BD2').
      destruct (bi_bd_hinv mm _ k3 c3 pad3 S3 n3 HC3 HC38 BD3) as (o3 & HI3 & BD3').
      destruct (bi_bd_hinv mm _ k4 c4 pad4 S4 n4 HC4 HC48 BD4) as (o4 & HI4 & BD4').
      step. if_cases K; zify_cond K; try solve [exfalso; clear - K HN4 N4; lia].
      cbv_concl_iota.
      eapply (x42_m0 mm rest e1 (2 * e1) (3 * e1) S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl
                k1 k2 k3 k4 pad1 pad2 pad3 pad4).
      all: first [eassumption | lia].
    - pose proof HER as HER'. unfold zd_is_error, ZE_maxCode in HER'. apply Z.ltb_lt in HER'.
      step. if_cases K; zify_cond K; try solve [exfalso; clear - K HER' HRB; lia].
      cbv_concl_iota. step.
      eapply (x42_ret mm).
      + eapply huf421_kit_c1_entry.c1_einvb_x42p; first [exact PV | eassumption | reflexivity].
      + right. exact (conj HER HRB).
  Qed.

End DX42_10.
