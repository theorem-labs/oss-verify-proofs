(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_hft_iface RZ_hft_kit RZ_hft_fdec_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section L1.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DST cap WK wksz SRCI ni DT tl fast : Z) (srci : list byte) (tb : list Z).
  Hypothesis HY : fd_hyps SPV lo DST cap SRCI ni DT tl.
  Hypothesis TBL : fd_tbl tl fast tb.
  Hypothesis SRCLEN : Z.of_nat (length srci) = ni.
  Notation POST := (fse_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST cap WK wksz lo m).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -160)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation FDm := (FD s0 s1 s2 s3 s4 s5 s6 s7 ra m SPV lo DST cap WK wksz SRCI DT srci tb).

  (* [comment removed for export] *)
  Notation STL1 pc mm x1 bc st2 st1 x8 x9 ptr cont x18 x22 x23 j x30 x31 :=
    (STF pc mm x1 (Z_to_bv 64 bc) (Z_to_bv 64 st2) (Z_to_bv 64 st1) x8 x9 (Z_to_bv 64 (SRCI + 8)) (Z_to_bv 64 FBITMASK) (Z_to_bv 64 ptr)
         (Z_to_bv 64 SRCI) (Z_to_bv 64 FSE_ZEROFILLED) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) cont
         x18 (Z_to_bv 64 DST) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap + -3)) x22 x23
         (Z_to_bv 64 (DST + j)) (Z_to_bv 64 64) x30 x31).

  Ltac ldnb CELB DT tb st :=
      let a := cur_mem_addr in
      let RDc := fresh "RDc" in
      pose proof (u8ro_znth psegs _ (DT + 4) tb (4 * st + 3) a CELB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDc;
      zstep; cbv beta; fold (fc_nb tb st); rewrite (byte_lit (fc_nb tb st)) by lia; clear RDc.
  Ltac ldsy CELB DT tb st :=
      let a := cur_mem_addr in
      let RDc := fresh "RDc" in
      pose proof (u8ro_znth psegs _ (DT + 4) tb (4 * st + 2) a CELB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDc;
      zstep; cbv beta; fold (fc_sy tb st); rewrite (byte_lit (fc_sy tb st)) by lia; clear RDc.
  Ltac ldnx CELB DT tb st :=
      let a := cur_mem_addr in
      let RDc := fresh "RDc" in
      pose proof (fc_nx_rd _ (DT + 4) tb st a CELB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDc;
      zstep; rewrite (zx16_u (fc_nx tb st)) by lia; clear RDc.
  Ltac ldmask MI nb :=
      let a := cur_mem_addr in
      let RDc := fresh "RDc" in
      pose proof (fbitmask_rd _ nb a MI ltac:(lia) ltac:(unfold wa, FBITMASK; f_equal; lia)) as RDc;
      zstep; clear RDc.

  (* [comment removed for export] *)
  Lemma fd1_dec : forall m1 out x1 bc st2 st1 x8 x9 ptr cont x18 x22 x23 j x30 x31,
    FDm out m1 ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> 0 <= j -> j + 4 <= cap ->
    (forall m2 out' bc' st2' st1' y8 y9 y30 y31, FDm out' m2 ->
       0 <= st1' < 2^tl -> 0 <= st2' < 2^tl -> 0 <= bc' <= 100 ->
       (bc' <= 64 -> evt psegs POST (STL1 0x25a48 m2 x1 bc' st2' st1' y8 y9 ptr cont x18 x22 x23 (j + 4) y30 y31)) /\
       (64 < bc' -> evt psegs POST (STL1 0x25bdc m2 x1 bc' st2' st1' y8 y9 ptr cont x18 x22 x23 (j + 4) y30 y31))) ->
    evt psegs POST (STL1 0x25aec m1 x1 bc st2 st1 x8 x9 ptr cont x18 x22 x23 j x30 x31).
  Proof.
    intros until x31; intros I S1 S2 BCR HJ HJC KONT. open_fh HY.
    open_fd I.
    destruct TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    destruct (fd_cell tl fast tb st1 TBL ltac:(lia) S1) as (NB1 & _ & NX1a & NX1b & SY1 & B10 & B11).
    destruct (fd_cell tl fast tb st2 TBL ltac:(lia) S2) as (NB2 & _ & NX2a & NX2b & SY2 & B20 & B21).
    zstep. zstep.
    replace (DT + 4 + st1 ≪ 2) with (DT + 4 + 4 * st1) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    ldnb CELB DT tb st1. ldnx CELB DT tb st1. ldsy CELB DT tb st1.
    zstep. zstep.
    replace (DT + 4 + st2 ≪ 2) with (DT + 4 + 4 * st2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. zstep. zstep. zstep. zstep.
    replace (FBITMASK + fc_nb tb st1 ≪ 2) with (FBITMASK + 4 * fc_nb tb st1) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    ldmask MI (fc_nb tb st1).
    assert (M1 : 1 <= 2^(fc_nb tb st1) <= 2^tl) by (split; [pose proof (Z.pow_pos_nonneg 2 (fc_nb tb st1) ltac:(lia) ltac:(lia)); lia | apply Z.pow_le_mono_r; lia]).
    rewrite (zx32w_small (2^(fc_nb tb st1) - 1)) by lia.
    outst OUT OLEN.
    ldnx CELB DT tb st2. ldsy CELB DT tb st2. ldnb CELB DT tb st2.
    zstep. zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 30 in lazymatch v with Z_to_bv 64 ?e => set (b1 := e) end end.
    assert (B1R : 0 <= b1 < 2^(fc_nb tb st1)) by (apply fland_mask_lt; lia). clearbody b1.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    set (st1a := fc_nx tb st1 + b1).
    assert (S1a : 0 <= st1a < 2^tl) by (unfold st1a; lia).
    replace (DT + 4 + fc_nx tb st1 ≪ 2 + b1 ≪ 2) with (DT + 4 + 4 * st1a) by (unfold st1a; rewrite !Z.shiftl_mul_pow2 by lia; lia).
    clearbody st1a.
    destruct (fd_cell tl fast tb st1a TBL ltac:(lia) S1a) as (NB3 & _ & NX3a & NX3b & SY3 & B30 & B31).
    replace (FBITMASK + fc_nb tb st2 ≪ 2) with (FBITMASK + 4 * fc_nb tb st2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    ldmask MI (fc_nb tb st2).
    assert (M2 : 1 <= 2^(fc_nb tb st2) <= 2^tl) by (split; [pose proof (Z.pow_pos_nonneg 2 (fc_nb tb st2) ltac:(lia) ltac:(lia)); lia | apply Z.pow_le_mono_r; lia]).
    rewrite (zx32w_small (2^(fc_nb tb st2) - 1)) by lia.
    outst OUT OLEN.
    ldnx CELB DT tb st1a. ldsy CELB DT tb st1a. ldnb CELB DT tb st1a.
    zstep. zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 6 in lazymatch v with Z_to_bv 64 ?e => set (b2 := e) end end.
    assert (B2R : 0 <= b2 < 2^(fc_nb tb st2)) by (apply fland_mask_lt; lia). clearbody b2.
    zstep. zstep. zstep. zstep. zstep. zstep.
    set (st2a := fc_nx tb st2 + b2).
    assert (S2a : 0 <= st2a < 2^tl) by (unfold st2a; lia).
    replace (DT + 4 + fc_nx tb st2 ≪ 2 + b2 ≪ 2) with (DT + 4 + 4 * st2a) by (unfold st2a; rewrite !Z.shiftl_mul_pow2 by lia; lia).
    clearbody st2a.
    destruct (fd_cell tl fast tb st2a TBL ltac:(lia) S2a) as (NB4 & _ & NX4a & NX4b & SY4 & B40 & B41).
    replace (FBITMASK + fc_nb tb st1a ≪ 2) with (FBITMASK + 4 * fc_nb tb st1a) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    ldmask MI (fc_nb tb st1a).
    assert (M3 : 1 <= 2^(fc_nb tb st1a) <= 2^tl) by (split; [pose proof (Z.pow_pos_nonneg 2 (fc_nb tb st1a) ltac:(lia) ltac:(lia)); lia | apply Z.pow_le_mono_r; lia]).
    rewrite (zx32w_small (2^(fc_nb tb st1a) - 1)) by lia.
    outst OUT OLEN.
    ldnx CELB DT tb st2a. ldsy CELB DT tb st2a. ldnb CELB DT tb st2a.
    zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 7 in lazymatch v with Z_to_bv 64 ?e => set (b3 := e) end end.
    assert (B3R : 0 <= b3 < 2^(fc_nb tb st1a)) by (apply fland_mask_lt; lia). clearbody b3.
    zstep. zstep.
    rewrite (swrap32_small (bc + fc_nb tb st1 + fc_nb tb st2 + fc_nb tb st1a + fc_nb tb st2a)) by lia.
    set (bc4 := bc + fc_nb tb st1 + fc_nb tb st2 + fc_nb tb st1a + fc_nb tb st2a) in *.
    assert (BC4 : 0 <= bc4 <= 100) by (unfold bc4; lia). clearbody bc4.
    zstep. zstep.
    replace (FBITMASK + fc_nb tb st2a ≪ 2) with (FBITMASK + 4 * fc_nb tb st2a) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    ldmask MI (fc_nb tb st2a).
    assert (M4 : 1 <= 2^(fc_nb tb st2a) <= 2^tl) by (split; [pose proof (Z.pow_pos_nonneg 2 (fc_nb tb st2a) ltac:(lia) ltac:(lia)); lia | apply Z.pow_le_mono_r; lia]).
    rewrite (zx32w_small (2^(fc_nb tb st2a) - 1)) by lia.
    zstep. zstep.
    outst OUT OLEN.
    zstep.
    lazymatch goal with |- _ => let v := reg_val 6 in lazymatch v with Z_to_bv 64 ?e => set (b4 := e) end end.
    assert (B4R : 0 <= b4 < 2^(fc_nb tb st2a)) by (apply fland_mask_lt; lia). clearbody b4.
    zstep. zstep.
    replace (DST + j + 4) with (DST + (j + 4)) by lia.
    set (st1b := b3 + fc_nx tb st1a). assert (S1b : 0 <= st1b < 2^tl) by (unfold st1b; lia). clearbody st1b.
    set (st2b := b4 + fc_nx tb st2a). assert (S2b : 0 <= st2b < 2^tl) by (unfold st2b; lia). clearbody st2b.
    zstep. if_cases K; zify_cond K.
    - eapply (proj1 (KONT _ _ bc4 st2b st1b _ _ _ _ ltac:(close_fd) S1b S2b BC4)). lia.
    - eapply (proj2 (KONT _ _ bc4 st2b st1b _ _ _ _ ltac:(close_fd) S1b S2b BC4)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_load : forall m1 x1 bc st2 st1 x8 x9 ptr nb x18 x22 x23 j flag x31,
    bytes_at psegs m1 SRCI srci ->
    0 <= nb <= 8 -> SRCI <= ptr - nb -> ptr - nb + 8 <= SRCI + ni -> 0 <= flag <= 1 -> 0 <= j <= cap ->
    (forall cont' y8 y9 y18 y22 y30 y31, flag = 1 -> j + 4 <= cap ->
       evt psegs POST (STL1 0x25aec m1 x1 bc st2 st1 y8 y9 (ptr - nb) cont' y18 y22 x23 j y30 y31)) ->
    (forall cont' y8 y9 y18 y22 y30 y31,
       evt psegs POST (STL1 0x25be0 m1 x1 bc st2 st1 y8 y9 (ptr - nb) cont' y18 y22 x23 j y30 y31)) ->
    evt psegs POST (STL1 0x25a80 m1 x1 bc st2 st1 x8 x9 ptr (Z_to_bv 64 nb) x18 x22 x23 j (Z_to_bv 64 flag) x31).
  Proof.
    intros until x31; intros SRCB NBR PLO PHI FLR HJ KD KT. open_fh HY.
    zstep. zstep.
    rewrite (Z.mod_small nb 4294967296) by lia. zstep.
    lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB. do 4 zstep. lbyte SRCB. lbyte SRCB. zstep. lbyte SRCB. lbyte SRCB. do 9 zstep.
    forget_reg 17. forget_reg 8. forget_reg 9. forget_reg 18. forget_reg 22. forget_reg 31.
    zstep. if_cases K; zify_cond K.
    - eapply KT.
    - zstep. if_cases K2; zify_cond K2.
      + eapply KT.
      + eapply KD; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_head : forall m1 x1 bc st2 st1 x8 x9 ptr cont x18 x22 x23 j x30 x31,
    bytes_at psegs m1 SRCI srci ->
    0 <= bc <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) -> 0 <= j <= cap ->
    (forall bc' ptr' cont' y8 y9 y18 y22 y30 y31, 0 <= bc' <= 64 -> 8 <= ni /\ SRCI <= ptr' <= SRCI + ni - 8 -> j + 4 <= cap ->
       evt psegs POST (STL1 0x25aec m1 x1 bc' st2 st1 y8 y9 ptr' cont' y18 y22 x23 j y30 y31)) ->
    (forall bc' ptr' cont' y8 y9 y18 y22 y30 y31, 0 <= bc' <= 64 -> (ptr' = SRCI \/ (8 <= ni /\ SRCI <= ptr' <= SRCI + ni - 8)) ->
       evt psegs POST (STL1 0x25be0 m1 x1 bc' st2 st1 y8 y9 ptr' cont' y18 y22 x23 j y30 y31)) ->
    evt psegs POST (STL1 0x25a48 m1 x1 bc st2 st1 x8 x9 ptr cont x18 x22 x23 j x30 x31).
  Proof.
    intros until x31; intros SRCB BCR PV HJ KD KT. open_fh HY.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. rewrite (srliw_val bc 3) by lia. rewrite (Z.mod_small bc 4294967296) by lia. change (2^3) with 8.
      zstep. replace (Z.land bc 7) with (bc mod 8) by (symmetry; apply land_7).
      zstep.
      assert (QR : 0 <= bc / 8 <= 8 /\ 0 <= bc mod 8 <= 7) by (clear - BCR; Z.div_mod_to_equations; lia).
      remember (bc / 8) as q eqn:EQ. remember (bc mod 8) as r eqn:ER. clear EQ ER.
      eapply (fd1_load m1 x1 r st2 st1 _ _ ptr q _ _ x23 j 1); [exact SRCB | lia | lia | lia | lia | exact HJ | |].
      + intros. eapply KD; lia.
      + intros. eapply KT; [lia | right; lia].
    - zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        eapply KT; [exact BCR | left; lia].
      + (* [comment removed for export] *)
        zstep. rewrite (srliw_val bc 3) by lia. rewrite (Z.mod_small bc 4294967296) by lia. change (2^3) with 8.
        assert (QR : 0 <= bc / 8 <= 8 /\ 8 * (bc / 8) <= bc) by (clear - BCR; Z.div_mod_to_equations; lia).
        remember (bc / 8) as q eqn:EQ. clear EQ.
        zstep. zstep. if_cases K3; zify_cond K3.
        * zstep. zstep. replace (q ≪ 3) with (8 * q) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
          zstep. zstep. rewrite (swrap32_small (bc - 8 * q)) by lia.
          replace (Z.lxor (Z.b2z (ptr - q <? SRCI)) 1) with 1 by (destruct (Z.ltb_spec (ptr - q) SRCI); [lia| reflexivity]).
          zstep.
          eapply (fd1_load m1 x1 (bc - 8 * q) st2 st1 _ _ ptr q _ _ x23 j 1); [exact SRCB | lia | lia | lia | lia | exact HJ | |].
          -- intros. eapply KD; lia.
          -- intros. eapply KT; [lia | right; lia].
        * (* [comment removed for export] *)
          zstep. zstep. zstep.
          assert (DR : 1 <= ptr - SRCI <= 7 /\ 8 <= ni) by (clear - PV K K2 K3 QR; lia).
          replace ((ptr - SRCI) ≪ 3) with (8 * (ptr - SRCI)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
          zstep. zstep. rewrite (swrap32_small (bc - 8 * (ptr - SRCI))) by lia.
          replace (Z.lxor (Z.b2z (ptr - q <? SRCI)) 1) with 0 by (destruct (Z.ltb_spec (ptr - q) SRCI); [reflexivity| lia]).
          zstep.
          eapply (fd1_load m1 x1 (bc - 8 * (ptr - SRCI)) st2 st1 _ _ ptr (ptr - SRCI) _ _ x23 j 0); [exact SRCB | lia | lia | lia | lia | exact HJ | |].
          -- intros. exfalso; lia.
          -- intros. eapply KT; [lia | left; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_loop : forall (f : nat) m1 out x1 bc st2 st1 x8 x9 ptr cont x18 x22 x23 j x30 x31,
    cap - j <= 4 * Z.of_nat f ->
    FDm out m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    0 <= bc <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) -> 0 <= j <= cap ->
    (forall m2 out' bc' st2' st1' y8 y9 ptr' cont' y18 y22 j' y30 y31, FDm out' m2 ->
       0 <= st1' < 2^tl -> 0 <= st2' < 2^tl -> 0 <= j' <= cap -> fbit_ok SRCI ni bc' ptr' ->
       evt psegs POST (STL1 0x25be0 m2 x1 bc' st2' st1' y8 y9 ptr' cont' y18 y22 x23 j' y30 y31)) ->
    evt psegs POST (STL1 0x25a48 m1 x1 bc st2 st1 x8 x9 ptr cont x18 x22 x23 j x30 x31).
  Proof.
    induction f as [|f IH]; intros until x31; intros HF I S1 S2 BCR PV HJ KT.
    - eapply fd1_head; [destruct I as (_ & _ & _ & SRCB & _); exact SRCB | exact BCR | exact PV | exact HJ | intros; exfalso; lia |].
      intros bc' ptr' cont' y8 y9 y18 y22 y30 y31 B' P'. eapply KT; [exact I | exact S1 | exact S2 | exact HJ |].
      unfold fbit_ok. split; [lia| intros _; exact P'].
    - eapply fd1_head; [destruct I as (_ & _ & _ & SRCB & _); exact SRCB | exact BCR | exact PV | exact HJ | |].
      + intros bc' ptr' cont' y8 y9 y18 y22 y30 y31 B' P' J4.
        eapply fd1_dec; [exact I | exact S1 | exact S2 | exact B' | lia | exact J4 |].
        intros m2 out' bc2 st2' st1' z8 z9 z30 z31 I2 S1' S2' B2. split.
        * intros LE. eapply (IH m2 out' x1 bc2 st2' st1' _ _ ptr' cont' _ _ x23 (j + 4)); [lia | exact I2 | exact S1' | exact S2' | lia | right; exact P' | lia | exact KT].
        * intros GT. zstep.
          eapply KT; [exact I2 | exact S1' | exact S2' | lia |]. unfold fbit_ok. split; [lia| intros; lia].
      + intros bc' ptr' cont' y8 y9 y18 y22 y30 y31 B' P'. eapply KT; [exact I | exact S1 | exact S2 | exact HJ |].
        unfold fbit_ok. split; [lia| intros _; exact P'].
  Qed.
End L1.
