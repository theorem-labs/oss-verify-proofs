(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_blk_iface RZ_bfse_defs seqH_kit seqH_kit_fse.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


Section P1.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DT NC BASE BITS W maxSV tl : Z) (k : seq_kind) (wlen : nat) (norm : list Z).
  Hypothesis HY : bf_hyps SPV lo DT NC BASE BITS W maxSV tl k wlen norm.
  Hypothesis AL : bf_al DT W NC BASE.
  Notation POST t := (bf_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W tl wlen lo m t).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation BFm := (BFU ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC BASE BITS W tl k wlen norm).

  (* [comment removed for export] *)
  Definition p1_step (s : Z) (st : list seqsym * list Z * Z * Z) : list seqsym * list Z * Z * Z :=
    let '(cells, symNext, high, fast) := st in
    if Znth s norm =? -1 then (set_base high s cells, Zupd s 1 symNext, high + -1, fast)
    else (cells, Zupd s (Znth s norm mod 2^16) symNext, high, if 2^(tl + -1) <=? Znth s norm then 0 else fast).

  Lemma lowprob_S : forall f s cells symNext high fast,
    lowprob (S f) norm (2^(tl + -1)) s cells symNext high fast =
    (let '(c1, n1, h1, f1) := p1_step s (cells, symNext, high, fast) in lowprob f norm (2^(tl + -1)) (s + 1) c1 n1 h1 f1).
  Proof.
    intros. cbn [lowprob p1_step]. destruct (Znth s norm =? -1); [replace (high - 1) with (high + -1) by lia|]; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Notation STP pc mm xra xs0 xs1 xa0 xa2 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x29 x30 x31 :=
    (ST pc mm xra (Z_to_bv 64 (18446744073709551615 - W)) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 (2^tl + -1)) xs0 xs1 xa0 (Z_to_bv 64 NC) xa2
        (Z_to_bv 64 BASE) (Z_to_bv 64 BITS) (Z_to_bv 64 tl) (Z_to_bv 64 W) (Z_to_bv 64 (DT + 8)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
        (Z_to_bv 64 (18446744073709551615 - (DT + 8))) x29 x30 x31).
  Notation ST1 pc mm xra xa0 xa2 xs0 xs2 xs8 xs9 xs10 xs11 x29 x31 :=
    (STP pc mm xra xs0 (Z_to_bv 64 0) xa0 xa2 xs2 (Z_to_bv 64 (18446744073709551615 - NC)) (Z_to_bv 64 1) (Z_to_bv 64 65535)
         (Z_to_bv 64 (2^(tl + -1))) (Z_to_bv 64 (2 * (maxSV + 1))) xs8 xs9 xs10 xs11 x29 (Z_to_bv 64 (maxSV + 1)) x31).

  (* [comment removed for export] *)
  Lemma bf_p1_body : forall (t : seq_table) m1 h0 h1 w8 w16 s cells symNext spread high fast xra xa0 xa2 xs8 xs9 xs10 xs11,
    BFm h0 h1 w8 w16 cells symNext spread m1 ->
    0 <= s <= maxSV -> 0 <= fast <= 1 ->
    2^tl - 1 - high = FseReadSound.pws norm s - nsum norm s ->
    (forall m2 c1 n1 h1' f1 ya0 ya2, p1_step s (cells, symNext, high, fast) = (c1, n1, h1', f1) -> s + 1 < maxSV + 1 ->
       BFm h0 h1 w8 w16 c1 n1 spread m2 -> 0 <= f1 <= 1 ->
       evt usegs (POST t) (ST1 0x16ef4 m2 xra ya0 ya2 (Z_to_bv 64 (2 * (s + 1))) (Z_to_bv 64 f1) xs8 xs9 xs10 xs11
                               (Z_to_bv 64 h1') (Z_to_bv 64 (s + 1)))) ->
    (forall m2 c1 n1 h1' f1 ya0 ya2, p1_step s (cells, symNext, high, fast) = (c1, n1, h1', f1) -> s + 1 = maxSV + 1 ->
       BFm h0 h1 w8 w16 c1 n1 spread m2 -> 0 <= f1 <= 1 ->
       evt usegs (POST t) (ST1 0x16f58 m2 xra ya0 ya2 (Z_to_bv 64 (2 * (maxSV + 1))) (Z_to_bv 64 f1) xs8 xs9 xs10 xs11
                               (Z_to_bv 64 h1') (Z_to_bv 64 (maxSV + 1)))) ->
    evt usegs (POST t) (ST1 0x16ef4 m1 xra xa0 xa2 (Z_to_bv 64 (2 * s)) (Z_to_bv 64 fast) xs8 xs9 xs10 xs11
                            (Z_to_bv 64 high) (Z_to_bv 64 s)).
  Proof.
    intros until xs11; intros I HS HFA HH KH KE; open_bh HY; open_bfu I. pose proof AL as (DTA & WAL & NCA & BASEA).
    destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
    assert (LBASE : Z.of_nat (length (kind_base k)) <= 53) by (destruct k; vm_compute; discriminate).
    assert (LBITS : Z.of_nat (length (kind_bits k)) <= 53) by (destruct k; vm_compute; discriminate).
    unfold FseNCount.Zlength in *.
    assert (NR : -1 <= Znth s norm <= 2^tl).
    { pose proof (NGE s ltac:(lia)). pose proof (count_le_size norm maxSV tl TL9 NLEN NGE NSUM s ltac:(lia)) as CL. unfold weight in CL.
      destruct (Z.eqb_spec (Znth s norm) (-1)); lia. }
    zstep. uck. zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u16_znth usegs m1 NC norm s a NCB ltac:(lia) ltac:(addr_tac)) as RD end.
    zstep. rewrite (zx16_short (Znth s norm)) by lia.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (NM1 : Znth s norm = -1) by (Z.div_mod_to_equations; lia).
      assert (PS : p1_step s (cells, symNext, high, fast) = (set_base high s cells, Zupd s 1 symNext, high + -1, fast)).
      { cbn [p1_step]. rewrite NM1. reflexivity. }
      assert (HHI : 0 <= high <= 2^tl - 1).
      { pose proof (low_step norm maxSV tl TL9 NLEN NGE s ltac:(lia)) as LS. rewrite NM1 in LS. cbn in LS.
        pose proof (low_mono norm maxSV tl TL9 NLEN NGE (s + 1) (maxSV + 1) ltac:(lia) ltac:(lia)) as LM.
        pose proof (low_mono norm maxSV tl TL9 NLEN NGE 0 s ltac:(lia) ltac:(lia)) as LM0.
        pose proof (nsum_nonneg norm maxSV tl TL9 NLEN (maxSV + 1) ltac:(lia)) as NN.
        change (FseReadSound.pws norm 0) with 0 in LM0. change (nsum norm 0) with 0 in LM0.
        unfold FseReadSound.pws in *. rewrite NSUM in LM. lia. }
      zstep. zstep. rewrite (zext32_sh29 high) by lia.
      zstep. uck. zstep. zstep. zstep. uck.
      cst CEL high 4 4%nat cellsB_store_base (2^32).
      rewrite (Z.mod_small s (2^32)) in CEL by lia.
      rewrite <- (set_base_as_set_cell cells high s) in CEL by (unfold FseNCount.Zlength; lia).
      zstep. uck. zstep. uck.
      zstep. rewrite (swrap32_small (high + -1)) by lia.
      zstep.
      snst SNX s 1 1.
      assert (SNLEN' : zlenF (upd_nat (Z.to_nat s) 1 symNext) = 53)
        by (unfold FseNCount.Zlength; rewrite FseLemmas.upd_nat_length; exact SNLEN).
      assert (CLEN' : zlenF (set_base high s cells) = 2^tl) by (unfold FseNCount.Zlength; rewrite set_base_length; exact CLEN).
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + replace (2 * s + 2) with (2 * (s + 1)) by lia.
        eapply KH; [exact PS | lia | unfold Zupd; close_bfu | exact HFA].
      + zstep. replace (2 * s + 2) with (2 * (maxSV + 1)) by lia. replace (s + 1) with (maxSV + 1) by lia.
        eapply KE; [exact PS | lia | unfold Zupd; close_bfu | exact HFA].
    - (* [comment removed for export] *)
      assert (NN : 0 <= Znth s norm) by (destruct (Z.eq_dec (Znth s norm) (-1)) as [E|E]; [rewrite E in K; exfalso; apply K; reflexivity | lia]).
      assert (PS : p1_step s (cells, symNext, high, fast)
                   = (cells, Zupd s (Znth s norm mod 2^16) symNext, high, if 2^(tl + -1) <=? Znth s norm then 0 else fast)).
      { cbn [p1_step]. destruct (Z.eqb_spec (Znth s norm) (-1)); [lia| reflexivity]. }
      rewrite (Z.mod_small (Znth s norm) 65536) by lia.
      zstep. uck. zstep. if_true.
      zstep. zstep. rewrite (sext16_shl48 (Znth s norm)) by lia.
      zstep.
      assert (P1 : 16 <= 2^(tl + -1) <= 256).
      { assert (2^4 <= 2^(tl + -1)) by (apply Z.pow_le_mono_r; lia). assert (2^(tl + -1) <= 2^8) by (apply Z.pow_le_mono_r; lia).
        change (2^4) with 16 in *. change (2^8) with 256 in *. lia. }
      rewrite (Z.mod_small (2^(tl + -1)) 18446744073709551616) by lia.
      rewrite (slt_small (Znth s norm) (2^(tl + -1))) by lia.
      zstep. zstep. rewrite swrap32_negb2z. rewrite (neg_mask _ fast) by lia.
      replace (if Znth s norm <? 2 ^ (tl + -1) then fast else 0) with (if 2 ^ (tl + -1) <=? Znth s norm then 0 else fast)
        by (destruct (Z.ltb_spec (Znth s norm) (2 ^ (tl + -1))); destruct (Z.leb_spec (2 ^ (tl + -1)) (Znth s norm)); lia).
      zstep.
      snst SNX s (Znth s norm) (Znth s norm mod 2^16).
      assert (SNLEN' : zlenF (upd_nat (Z.to_nat s) (Znth s norm mod 2 ^ 16) symNext) = 53)
        by (unfold FseNCount.Zlength; rewrite FseLemmas.upd_nat_length; exact SNLEN).
      assert (F1 : 0 <= (if 2 ^ (tl + -1) <=? Znth s norm then 0 else fast) <= 1) by (destruct (2 ^ (tl + -1) <=? Znth s norm); lia).
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + replace (2 * s + 2) with (2 * (maxSV + 1)) by lia. replace (s + 1) with (maxSV + 1) by lia.
        eapply KE; [exact PS | lia | unfold Zupd; close_bfu | exact F1].
      + replace (2 * s + 2) with (2 * (s + 1)) by lia.
        eapply KH; [exact PS | lia | unfold Zupd; close_bfu | exact F1].
  Qed.

  (* [comment removed for export] *)
  Lemma bf_p1_loop : forall (t : seq_table) (f : nat) m1 h0 h1 w8 w16 s cells symNext spread high fast xra xa0 xa2 xs8 xs9 xs10 xs11,
    BFm h0 h1 w8 w16 cells symNext spread m1 ->
    0 <= s -> s + Z.of_nat (S f) = maxSV + 1 -> 0 <= fast <= 1 ->
    2^tl - 1 - high = FseReadSound.pws norm s - nsum norm s ->
    (forall m2 cells' symNext' high' fast' ya0 ya2,
       lowprob (S f) norm (2^(tl + -1)) s cells symNext high fast = (cells', symNext', high', fast') ->
       BFm h0 h1 w8 w16 cells' symNext' spread m2 -> 0 <= fast' <= 1 ->
       evt usegs (POST t) (ST1 0x16f58 m2 xra ya0 ya2 (Z_to_bv 64 (2 * (maxSV + 1))) (Z_to_bv 64 fast') xs8 xs9 xs10 xs11
                               (Z_to_bv 64 high') (Z_to_bv 64 (maxSV + 1)))) ->
    evt usegs (POST t) (ST1 0x16ef4 m1 xra xa0 xa2 (Z_to_bv 64 (2 * s)) (Z_to_bv 64 fast) xs8 xs9 xs10 xs11
                            (Z_to_bv 64 high) (Z_to_bv 64 s)).
  Proof.
    induction f as [|f IH]; intros until xs11; intros I HS HSF HFA HH KONT.
    - eapply bf_p1_body; [exact I | lia | exact HFA | exact HH | |].
      + intros; exfalso; lia.
      + intros m2 c1 n1 h1' f1 ya0 ya2 PS _ I2 F1. eapply KONT; [| exact I2 | exact F1].
        rewrite lowprob_S, PS. reflexivity.
    - eapply bf_p1_body; [exact I | lia | exact HFA | exact HH | |].
      + intros m2 c1 n1 h1' f1 ya0 ya2 PS LT I2 F1.
        eapply (IH m2 h0 h1 w8 w16 (s + 1) c1 n1 spread h1' f1); [exact I2 | lia | lia | exact F1 | |].
        * open_bh HY. destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
          pose proof (low_step norm maxSV tl TL9 NLEN NGE s ltac:(lia)) as LS.
          cbn [p1_step] in PS. destruct (Znth s norm =? -1); injection PS as <- <- <- <-; lia.
        * intros m3 cells' symNext' high' fast' yb0 yb2 LP I3 F3. eapply KONT; [| exact I3 | exact F3].
          rewrite lowprob_S, PS. exact LP.
      + intros; exfalso; lia.
  Qed.
End P1.
