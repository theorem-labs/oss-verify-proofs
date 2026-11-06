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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_hft_iface RZ_hft_kit RZ_hft_fdec_defs RZ_hft_fdec_epi.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section T1.
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
  Notation STT pc mm x1 x5 x6 x7 x8 x9 ptr x17 x18 x21 x22 x23 j x30 x31 :=
    (STF pc mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (SRCI + 8)) (Z_to_bv 64 FBITMASK) (Z_to_bv 64 ptr)
         (Z_to_bv 64 SRCI) (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) x17
         x18 (Z_to_bv 64 DST) (Z_to_bv 64 (DST + cap + -2)) x21 x22 x23
         (Z_to_bv 64 (DST + j + 1)) (Z_to_bv 64 64) x30 x31).

  (* [comment removed for export] *)
  Lemma fd1_t_err : forall m1 out x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    FDm out m1 ->
    evt psegs POST (STF 0x25610 m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 (Z_to_bv 64 18446744073709551546) x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I. eapply fd_epi; [exact HY | exact I | lia | left; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_t_j2 : forall m1 out x1 bcB st1' nx2 nb2 bcx x9 ptrB contB x18 x21 x22 x23 j contA,
    FDm out m1 -> 0 <= nx2 -> 0 <= nb2 <= tl -> nx2 + 2^nb2 <= 2^tl -> 0 <= j <= cap ->
    (forall st2' y8 y30, 0 <= st2' < 2^tl -> j + 4 <= cap ->
       evt psegs POST (STT 0x25c8c m1 x1 (Z_to_bv 64 bcB) (Z_to_bv 64 st2') (Z_to_bv 64 st1') y8 x9 ptrB contB x18 x21 x22 x23 (j + 2)
                           y30 (Z_to_bv 64 (2^nb2 - 1)))) ->
    evt psegs POST (STT 0x25c70 m1 x1 (Z_to_bv 64 bcB) (Z_to_bv 64 nx2) (Z_to_bv 64 st1') bcx x9 ptrB contB x18 x21 x22 x23 j
                        contA (Z_to_bv 64 (2^nb2 - 1))).
  Proof.
    intros until contA; intros I NX NB NXB HJ KH. open_fh HY.
    assert (M2 : 1 <= 2^nb2 <= 2^tl) by (split; [pose proof (Z.pow_pos_nonneg 2 nb2 ltac:(lia) ltac:(lia)); lia | apply Z.pow_le_mono_r; lia]).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 30 in lazymatch v with Z_to_bv 64 ?e => set (b2 := e) end end.
    assert (B2R : 0 <= b2 < 2^nb2) by (apply fland_mask_lt; lia). clearbody b2.
    zstep. zstep.
    set (st2' := b2 + nx2). assert (S2 : 0 <= st2' < 2^tl) by (unfold st2'; lia). clearbody st2'.
    zstep. if_cases K; zify_cond K.
    - eapply fd1_t_err; exact I.
    - replace (DST + j + 3) with (DST + (j + 2) + 1) by lia.
      eapply KH; [exact S2 | lia].
  Qed.

  (* [comment removed for export] *)
  Definition t1_KH (x1 : word) (j : Z) : Prop :=
    forall m2 out' bcB st2' st1' y8 y9 ptrB contB y18 y21 y22 y23 y30 y31, FDm out' m2 ->
      0 <= bcB <= 64 -> (ptrB = SRCI \/ (8 <= ni /\ SRCI <= ptrB <= SRCI + ni - 8)) -> 0 <= st1' < 2^tl -> 0 <= st2' < 2^tl -> j + 4 <= cap ->
      evt psegs POST (STT 0x25c8c m2 x1 (Z_to_bv 64 bcB) (Z_to_bv 64 st2') (Z_to_bv 64 st1') y8 y9 ptrB contB y18 y21 y22 y23 (j + 2) y30 y31).

  (* [comment removed for export] *)
  Lemma fd1_t_rB_load : forall m1 out x1 x5 nx2 st1' bc2 x9 ptr nb x18 x21 x22 x23 j contA nb2,
    FDm out m1 -> 0 <= nb <= 8 -> 8 * nb <= bc2 <= 64 -> SRCI <= ptr - nb -> ptr - nb + 8 <= SRCI + ni ->
    0 <= nx2 -> 0 <= nb2 <= tl -> nx2 + 2^nb2 <= 2^tl -> 0 <= j <= cap ->
    0 <= st1' < 2^tl -> t1_KH x1 j ->
    evt psegs POST (STT 0x25e10 m1 x1 x5 (Z_to_bv 64 nx2) (Z_to_bv 64 st1') (Z_to_bv 64 bc2) x9 ptr (Z_to_bv 64 nb) x18 x21 x22 x23 j
                        contA (Z_to_bv 64 (2^nb2 - 1))).
  Proof.
    intros until nb2; intros I NBR BCR PLO PHI NX NB NXB HJ S1' KH. open_fh HY.
    pose proof I as I0. open_fd I0.
    zstep. zstep. rewrite (Z.mod_small nb 4294967296) by lia. zstep.
    lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB. do 4 zstep. lbyte SRCB. lbyte SRCB. zstep. lbyte SRCB. lbyte SRCB.
    do 5 zstep. zstep.
    replace (nb ≪ 3) with (8 * nb) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. rewrite (swrap32_small (bc2 - 8 * nb)) by lia.
    do 5 zstep.
    forget_reg 17. forget_reg 9. forget_reg 18. forget_reg 21. forget_reg 22. forget_reg 23.
    eapply (fd1_t_j2 m1 out x1 (bc2 - 8 * nb) st1' nx2 nb2 _ _ (ptr - nb)); [exact I | exact NX | exact NB | exact NXB | exact HJ |].
    intros st2' y8 y30 S2 J4. eapply KH; [exact I | lia | right; lia | exact S1' | exact S2 | exact J4].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_t_rB : forall m1 out x1 x5 nx2 st1' bc2 x9 ptr x17 x18 x21 x22 x23 j contA nb2,
    FDm out m1 -> 0 <= bc2 <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) ->
    0 <= nx2 -> 0 <= nb2 <= tl -> nx2 + 2^nb2 <= 2^tl -> 0 <= j <= cap ->
    0 <= st1' < 2^tl -> t1_KH x1 j ->
    evt psegs POST (STT 0x25df8 m1 x1 x5 (Z_to_bv 64 nx2) (Z_to_bv 64 st1') (Z_to_bv 64 bc2) x9 ptr x17 x18 x21 x22 x23 j
                        contA (Z_to_bv 64 (2^nb2 - 1))).
  Proof.
    intros until nb2; intros I BCR PV NX NB NXB HJ S1' KH. open_fh HY.
    pose proof I as I0. open_fd I0.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. rewrite (srliw_val bc2 3) by lia. rewrite (Z.mod_small bc2 4294967296) by lia. change (2^3) with 8.
      assert (QR : 0 <= bc2 / 8 <= 8 /\ 0 <= bc2 mod 8 <= 7) by (clear - BCR; Z.div_mod_to_equations; lia).
      remember (bc2 / 8) as q eqn:EQ.
      zstep.
      lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB. do 4 zstep. lbyte SRCB. lbyte SRCB. zstep. lbyte SRCB. lbyte SRCB.
      do 5 zstep. zstep. replace (Z.land bc2 7) with (bc2 mod 8) by (symmetry; apply land_7).
      do 4 zstep.
      forget_reg 17. forget_reg 9. forget_reg 18. forget_reg 21. forget_reg 22.
      eapply (fd1_t_j2 m1 out x1 (bc2 mod 8) st1' nx2 nb2 _ _ (ptr - q)); [exact I | exact NX | exact NB | exact NXB | exact HJ |].
      intros st2' y8 y30 S2 J4. eapply KH; [exact I | lia | right; lia | exact S1' | exact S2 | exact J4].
    - zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        zstep. zstep. zstep.
        eapply (fd1_t_j2 m1 out x1 bc2 st1' nx2 nb2 _ _ ptr); [exact I | exact NX | exact NB | exact NXB | exact HJ |].
        intros st2' y8 y30 S2 J4. eapply KH; [exact I | lia | left; lia | exact S1' | exact S2 | exact J4].
      + (* [comment removed for export] *)
        zstep. rewrite (srliw_val bc2 3) by lia. rewrite (Z.mod_small bc2 4294967296) by lia. change (2^3) with 8.
        assert (QR : 0 <= bc2 / 8 <= 8 /\ 8 * (bc2 / 8) <= bc2) by (clear - BCR; Z.div_mod_to_equations; lia).
        remember (bc2 / 8) as q eqn:EQ. clear EQ.
        zstep. zstep. if_cases K3; zify_cond K3.
        * eapply (fd1_t_rB_load m1 out x1 _ nx2 st1' bc2 _ ptr q); [exact I | lia | lia | lia | lia | exact NX | exact NB | exact NXB | exact HJ | exact S1' | exact KH].
        * zstep.
          eapply (fd1_t_rB_load m1 out x1 _ nx2 st1' bc2 _ ptr (ptr - SRCI)); [exact I | lia | lia | lia | lia | exact NX | exact NB | exact NXB | exact HJ | exact S1' | exact KH].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_t_mid : forall m1 out x1 x5 st2 nx1 nb1 bcA x9 ptr x17 x18 x21 x22 x23 j contA,
    FDm out m1 -> 0 <= st2 < 2^tl -> 0 <= nx1 -> 0 <= nb1 <= tl -> nx1 + 2^nb1 <= 2^tl ->
    0 <= bcA <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) -> 0 <= j -> j + 3 <= cap ->
    t1_KH x1 j ->
    evt psegs POST (STT 0x25dbc m1 x1 x5 (Z_to_bv 64 st2) (Z_to_bv 64 nx1) (Z_to_bv 64 bcA) x9 ptr x17 x18 x21 x22 x23 j
                        contA (Z_to_bv 64 (2^nb1 - 1))).
  Proof.
    intros until contA; intros I S2 NX NB NXB BCR PV HJ HJC KH. open_fh HY. open_fd I.
    destruct (fd_cell tl fast tb st2 TBL ltac:(lia) S2) as (NB2 & _ & NX2a & NX2b & SY2 & B20 & B21).
    destruct TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    assert (M1 : 1 <= 2^nb1 <= 2^tl) by (split; [pose proof (Z.pow_pos_nonneg 2 nb1 ltac:(lia) ltac:(lia)); lia | apply Z.pow_le_mono_r; lia]).
    zstep. zstep. replace (DT + 4 + st2 ≪ 2) with (DT + 4 + 4 * st2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    ldnx CELB DT tb st2. ldsy CELB DT tb st2. ldnb CELB DT tb st2.
    zstep. zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 17 in lazymatch v with Z_to_bv 64 ?e => set (b1 := e) end end.
    assert (B1R : 0 <= b1 < 2^nb1) by (apply fland_mask_lt; lia). clearbody b1.
    zstep. zstep.
    replace (FBITMASK + fc_nb tb st2 ≪ 2) with (FBITMASK + 4 * fc_nb tb st2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    ldmask MI (fc_nb tb st2).
    assert (M2 : 1 <= 2^(fc_nb tb st2) <= 2^tl) by (split; [pose proof (Z.pow_pos_nonneg 2 (fc_nb tb st2) ltac:(lia) ltac:(lia)); lia | apply Z.pow_le_mono_r; lia]).
    rewrite (zx32w_small (2^(fc_nb tb st2) - 1)) by lia.
    zstep.
    set (st1' := b1 + nx1). assert (S1' : 0 <= st1' < 2^tl) by (unfold st1'; lia). clearbody st1'.
    zstep. rewrite (swrap32_small (bcA + fc_nb tb st2)) by lia.
    outst OUT OLEN.
    zstep. if_cases K; zify_cond K.
    - eapply (fd1_finB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DST cap WK wksz SRCI ni DT tl fast srci tb HY
                (conj TBLEN (conj TBBY TBOK)) SRCLEN _ _ st1' j); [close_fd | exact S1' | exact HJ | exact HJC].
    - eapply (fd1_t_rB _ _ x1 _ (fc_nx tb st2) st1' (bcA + fc_nb tb st2) _ ptr _ _ _ _ _ j _ (fc_nb tb st2));
        [close_fd | lia | exact PV | lia | lia | lia | lia | exact S1' | exact KH].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_t_rA_load : forall m1 out x1 bc1 st2 nx1 nb1 x8 x9 ptr x17 x18 x21 x22 x23 j nb,
    FDm out m1 -> 0 <= nb <= 8 -> 8 * nb <= bc1 <= 64 -> SRCI <= ptr - nb -> ptr - nb + 8 <= SRCI + ni ->
    0 <= st2 < 2^tl -> 0 <= nx1 -> 0 <= nb1 <= tl -> nx1 + 2^nb1 <= 2^tl -> 0 <= j <= cap ->
    t1_KH x1 j ->
    evt psegs POST (STT 0x25cd0 m1 x1 (Z_to_bv 64 bc1) (Z_to_bv 64 st2) (Z_to_bv 64 nx1) x8 x9 ptr x17 x18 x21 x22 x23 j
                        (Z_to_bv 64 nb) (Z_to_bv 64 (2^nb1 - 1))).
  Proof.
    intros until nb; intros I NBR BCR PLO PHI S2 NX NB NXB HJ KH. open_fh HY.
    pose proof I as I0. open_fd I0.
    zstep. zstep. rewrite (Z.mod_small nb 4294967296) by lia. zstep.
    lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB. do 4 zstep. lbyte SRCB. lbyte SRCB. zstep. lbyte SRCB. lbyte SRCB.
    do 5 zstep. zstep.
    replace (nb ≪ 3) with (8 * nb) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. rewrite (swrap32_small (bc1 - 8 * nb)) by lia.
    do 4 zstep.
    forget_reg 30. forget_reg 9. forget_reg 18. forget_reg 21. forget_reg 22. forget_reg 23.
    zstep. if_cases K; zify_cond K.
    - eapply (fd1_t_mid m1 out x1 _ st2 nx1 nb1 (bc1 - 8 * nb) _ (ptr - nb)); [exact I | exact S2 | exact NX | exact NB | exact NXB | lia | right; lia | lia | lia | exact KH].
    - zstep. eapply fd1_t_err; exact I.
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_t_rA : forall m1 out x1 bc1 st2 nx1 nb1 x8 x9 ptr cont x18 x21 x22 x23 j x30,
    FDm out m1 -> 0 <= bc1 <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) ->
    0 <= st2 < 2^tl -> 0 <= nx1 -> 0 <= nb1 <= tl -> nx1 + 2^nb1 <= 2^tl -> 0 <= j <= cap ->
    t1_KH x1 j ->
    evt psegs POST (STT 0x25cb8 m1 x1 (Z_to_bv 64 bc1) (Z_to_bv 64 st2) (Z_to_bv 64 nx1) x8 x9 ptr cont x18 x21 x22 x23 j
                        x30 (Z_to_bv 64 (2^nb1 - 1))).
  Proof.
    intros until x30; intros I BCR PV S2 NX NB NXB HJ KH. open_fh HY.
    pose proof I as I0. open_fd I0.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. rewrite (srliw_val bc1 3) by lia. rewrite (Z.mod_small bc1 4294967296) by lia. change (2^3) with 8.
      assert (QR : 0 <= bc1 / 8 <= 8 /\ 0 <= bc1 mod 8 <= 7) by (clear - BCR; Z.div_mod_to_equations; lia).
      remember (bc1 / 8) as q eqn:EQ.
      zstep.
      lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB. do 4 zstep. lbyte SRCB. lbyte SRCB. zstep. lbyte SRCB. lbyte SRCB.
      do 5 zstep. zstep. replace (Z.land bc1 7) with (bc1 mod 8) by (symmetry; apply land_7).
      do 4 zstep.
      forget_reg 30. forget_reg 9. forget_reg 18. forget_reg 21. forget_reg 22.
      zstep. if_cases K1; zify_cond K1.
      + eapply (fd1_t_mid m1 out x1 _ st2 nx1 nb1 (bc1 mod 8) _ (ptr - q)); [exact I | exact S2 | exact NX | exact NB | exact NXB | lia | right; lia | lia | lia | exact KH].
      + zstep. eapply fd1_t_err; exact I.
    - zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        zstep. zstep. zstep. if_cases K1; zify_cond K1.
        * eapply fd1_t_err; exact I.
        * eapply (fd1_t_mid m1 out x1 _ st2 nx1 nb1 bc1 _ ptr); [exact I | exact S2 | exact NX | exact NB | exact NXB | lia | left; lia | lia | lia | exact KH].
      + (* [comment removed for export] *)
        zstep. rewrite (srliw_val bc1 3) by lia. rewrite (Z.mod_small bc1 4294967296) by lia. change (2^3) with 8.
        assert (QR : 0 <= bc1 / 8 <= 8 /\ 8 * (bc1 / 8) <= bc1) by (clear - BCR; Z.div_mod_to_equations; lia).
        remember (bc1 / 8) as q eqn:EQ. clear EQ.
        zstep. zstep. if_cases K3; zify_cond K3.
        * eapply (fd1_t_rA_load m1 out x1 bc1 st2 nx1 nb1 _ _ ptr _ _ _ _ _ j q); [exact I | lia | lia | lia | lia | exact S2 | exact NX | exact NB | exact NXB | exact HJ | exact KH].
        * zstep.
          eapply (fd1_t_rA_load m1 out x1 bc1 st2 nx1 nb1 _ _ ptr _ _ _ _ _ j (ptr - SRCI)); [exact I | lia | lia | lia | lia | exact S2 | exact NX | exact NB | exact NXB | exact HJ | exact KH].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_t_head : forall m1 out x1 bc st2 st1 x8 x9 ptr cont x18 x21 x22 x23 j x30 x31,
    FDm out m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> fbit_ok SRCI ni bc ptr -> 0 <= j -> j + 2 <= cap ->
    t1_KH x1 j ->
    evt psegs POST (STT 0x25c8c m1 x1 (Z_to_bv 64 bc) (Z_to_bv 64 st2) (Z_to_bv 64 st1) x8 x9 ptr cont x18 x21 x22 x23 j x30 x31).
  Proof.
    intros until x31; intros I S1 S2 (BCR & BOK) HJ HJC KH. open_fh HY. open_fd I.
    destruct (fd_cell tl fast tb st1 TBL ltac:(lia) S1) as (NB1 & _ & NX1a & NX1b & SY1 & B10 & B11).
    destruct TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zstep. zstep. replace (DT + 4 + st1 ≪ 2) with (DT + 4 + 4 * st1) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    ldnb CELB DT tb st1. ldnx CELB DT tb st1. ldsy CELB DT tb st1.
    zstep. zstep.
    replace (FBITMASK + fc_nb tb st1 ≪ 2) with (FBITMASK + 4 * fc_nb tb st1) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    ldmask MI (fc_nb tb st1).
    assert (M1 : 1 <= 2^(fc_nb tb st1) <= 2^tl) by (split; [pose proof (Z.pow_pos_nonneg 2 (fc_nb tb st1) ltac:(lia) ltac:(lia)); lia | apply Z.pow_le_mono_r; lia]).
    rewrite (zx32w_small (2^(fc_nb tb st1) - 1)) by lia.
    zstep. rewrite (swrap32_small (bc + fc_nb tb st1)) by lia.
    outst OUT OLEN.
    zstep. if_cases K; zify_cond K.
    - eapply (fd1_finA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DST cap WK wksz SRCI ni DT tl fast srci tb HY
                (conj TBLEN (conj TBBY TBOK)) SRCLEN _ _ st2 j); [close_fd | exact S2 | exact HJ | exact HJC].
    - eapply (fd1_t_rA _ _ x1 (bc + fc_nb tb st1) st2 (fc_nx tb st1) (fc_nb tb st1) _ _ ptr);
        [close_fd | lia | apply BOK; lia | exact S2 | lia | lia | lia | lia | exact KH].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_t_loop : forall (f : nat) m1 out x1 bc st2 st1 x8 x9 ptr cont x18 x21 x22 x23 j x30 x31,
    cap - j <= 2 * Z.of_nat f ->
    FDm out m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> fbit_ok SRCI ni bc ptr -> 0 <= j -> j + 2 <= cap ->
    evt psegs POST (STT 0x25c8c m1 x1 (Z_to_bv 64 bc) (Z_to_bv 64 st2) (Z_to_bv 64 st1) x8 x9 ptr cont x18 x21 x22 x23 j x30 x31).
  Proof.
    induction f as [|f IH]; intros until x31; intros HF I S1 S2 BOK HJ HJC; [exfalso; lia|].
    eapply fd1_t_head; [exact I | exact S1 | exact S2 | exact BOK | exact HJ | exact HJC |].
    unfold t1_KH. intros m2 out' bcB st2' st1' y8 y9 ptrB contB y18 y21 y22 y23 y30 y31 I2 BB PB S1' S2' J4.
    eapply (IH m2 out' x1 bcB st2' st1'); [lia | exact I2 | exact S1' | exact S2' | unfold fbit_ok; split; [lia| intros _; exact PB] | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_tprep : forall m1 out x1 bc st2 st1 x8 x9 ptr cont x18 x22 x23 j x30 x31,
    FDm out m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= j <= cap -> fbit_ok SRCI ni bc ptr ->
    evt psegs POST
      (STF 0x25be0 m1 x1 (Z_to_bv 64 bc) (Z_to_bv 64 st2) (Z_to_bv 64 st1) x8 x9 (Z_to_bv 64 (SRCI + 8)) (Z_to_bv 64 FBITMASK) (Z_to_bv 64 ptr)
           (Z_to_bv 64 SRCI) (Z_to_bv 64 FSE_ZEROFILLED) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) cont
           x18 (Z_to_bv 64 DST) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap + -3)) x22 x23
           (Z_to_bv 64 (DST + j)) (Z_to_bv 64 64) x30 x31).
  Proof.
    intros until x31; intros I S1 S2 HJ BOK. open_fh HY. open_fd I.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    do 5 zstep. zstep. zstep.
    replace (Z_to_bv 64 (-70)) with (Z_to_bv 64 18446744073709551546) by (apply bv_eq; reflexivity).
    zstep. if_cases K; zify_cond K.
    - eapply fd1_t_err. close_fd.
    - zstep. zstep. zstep.
      eapply (fd1_t_loop (Z.to_nat cap) _ _ x1 bc st2 st1 _ _ ptr); [lia | close_fd | exact S1 | exact S2 | exact BOK | lia | lia].
  Qed.
End T1.
