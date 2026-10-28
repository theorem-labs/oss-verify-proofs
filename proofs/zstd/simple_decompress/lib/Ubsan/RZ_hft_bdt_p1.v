(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqBuild ZdSeqBuildThm ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdSeqBuildW4 ZdHufW.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_hft_iface RZ_hft_bdt_defs RZ_fse_bdt_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section P1.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DT NC W wlen maxSV tl : Z) (norm : list Z).
  Hypothesis HY : bd_hyps SPV lo DT NC W wlen maxSV tl norm.
  Hypothesis HU : lo <= SPV - 128 /\ DT mod 4 = 0 /\ W mod 2 = 0 /\ NC mod 2 = 0.
  Notation POST := (fse_bdt_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W wlen tl lo m).
  Notation ST pc mm x1 x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation BDm := (BDU ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC W wlen maxSV tl norm).

  (* [comment removed for export] *)
  Notation ST1 pc mm high s x7 xs2 xs8 xs9 xs10 xs11 fast :=
    (ST pc mm ra (Z_to_bv 64 (znot (DT + 4))) (Z_to_bv 64 (2^tl + -1)) x7 (Z_to_bv 64 s) (Z_to_bv 64 (maxSV + 1))
        (Z_to_bv 64 1) (Z_to_bv 64 NC) (Z_to_bv 64 maxSV) (Z_to_bv 64 tl) (Z_to_bv 64 W) (Z_to_bv 64 (2^tl))
        (Z_to_bv 64 (znot W)) (Z_to_bv 64 (DT + 4)) xs2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 fast)
        (Z_to_bv 64 (2^(tl - 1))) (Z_to_bv 64 65535) xs8 xs9 xs10 xs11
        (Z_to_bv 64 (znot NC)) (Z_to_bv 64 (W + 2 * maxSV + 2)) (Z_to_bv 64 high) (Z_to_bv 64 (maxSV + 1))).

  (* [comment removed for export] *)
  Lemma bd_p1_body : forall m1 h0 h1 s tb sn sp high fast x7 xs2 xs8 xs9 xs10 xs11,
    BDm h0 h1 tb sn sp m1 -> p1_inv norm maxSV tl s tb sn high fast -> 0 <= s <= maxSV ->
    (forall m2 tb' sn' high' fast' y7 ys2 ys8, BDm h0 h1 tb' sn' sp m2 -> p1_inv norm maxSV tl (s + 1) tb' sn' high' fast' -> s + 1 < maxSV + 1 ->
       evt usegs POST (ST1 0x2a794 m2 high' (s + 1) y7 ys2 ys8 xs9 xs10 xs11 fast')) ->
    (forall m2 tb' sn' high' fast' y7 ys2 ys8, BDm h0 h1 tb' sn' sp m2 -> p1_inv norm maxSV tl (maxSV + 1) tb' sn' high' fast' ->
       evt usegs POST (ST1 0x2a808 m2 high' (maxSV + 1) y7 ys2 ys8 xs9 xs10 xs11 fast')) ->
    evt usegs POST (ST1 0x2a794 m1 high s x7 xs2 xs8 xs9 xs10 xs11 fast).
  Proof.
    intros until xs11; intros I P1 HS KH KE; open_bh HY; open_bd I.
    destruct HU as (LOU & DTA & WA & NCA).
    destruct (bd_size_rng _ _ _ _ _ _ _ _ _ HY) as (SZ & LLR & LL2).
    unfold FseNCount.Zlength in *.
    assert (NR : -1 <= Znth s norm <= 2^tl) by (apply (hnorm_range norm maxSV tl TLR MSVR NLEN NGE NSUM); exact HS).
    assert (HFA : 0 <= fast <= 1) by (destruct P1 as (_ & _ & _ & _ & _ & FR1 & _); exact FR1).
    zstep. replace (s ≪ 1) with (2 * s) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. bd_chk.
    zstep. try bd_chk.
    zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u16_znth usegs m1 NC norm s a NCB ltac:(lia) ltac:(addr_tac)) as RD end.
    zstep. rewrite (zx16_short (Znth s norm)) by lia.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (NM1 : Znth s norm = -1) by (Z.div_mod_to_equations; lia).
      destruct (p1_low norm maxSV tl TLR MSVR NLEN NGE NSUM s tb sn high fast P1 HS NM1) as (HHI & P1').
      zstep. zstep.
      rewrite (zext32_sh30 high) by lia.
      zstep. bd_chk.
      zstep. zstep. zstep. bd_chk.
      tbst CEL (4 * high + 2) s.
      { reflexivity. }
      assert (CLEN' : Z.of_nat (length (Zupd (4 * high + 2) s tb)) = 4 * 2^tl) by (rewrite FseLemmas.Zupd_length; exact CLEN).
      assert (CBY' : Forall isbyte (Zupd (4 * high + 2) s tb)) by (apply Forall_Zupd; [exact CBY| lia]).
      zstep. bd_chk.
      zstep. try bd_chk.
      zstep. rewrite (swrap32_small (high + -1)) by lia.
      zstep.
      snst SNX s 1 1.
      assert (SNLEN' : Z.of_nat (length (upd_nat (Z.to_nat s) 1 sn)) = maxSV + 1)
        by (rewrite FseLemmas.upd_nat_length; exact SNLEN).
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + replace (s + 1) with (maxSV + 1) by lia. replace (s + 1) with (maxSV + 1) in P1' by lia.
        replace (high + -1) with (high - 1) by lia.
        eapply KE; [unfold Zupd in P1' |- *; unfold FseNCount.Zlength; close_bd | exact P1'].
      + replace (high + -1) with (high - 1) by lia.
        eapply KH; [unfold Zupd in P1' |- *; unfold FseNCount.Zlength; close_bd | exact P1' | lia].
    - (* [comment removed for export] *)
      assert (NN : 0 <= Znth s norm) by (destruct (Z.eq_dec (Znth s norm) (-1)) as [E|E]; [rewrite E in K; exfalso; apply K; reflexivity | lia]).
      destruct (p1_norm norm maxSV tl TLR MSVR NLEN NGE NSUM s tb sn high fast P1 HS ltac:(lia)) as (_ & P1').
      rewrite (Z.mod_small (Znth s norm) 65536) by lia.
      zstep. bd_chk.
      zstep. try bd_chk.
      zstep. zstep. zstep. rewrite (sext16_shl48 (Znth s norm)) by lia.
      zstep.
      rewrite (slt_small (Znth s norm) (2^(tl - 1))) by lia.
      zstep. zstep. rewrite (neg_mask _ fast) by lia.
      replace (if Znth s norm <? 2 ^ (tl - 1) then fast else 0) with (if 2 ^ (tl - 1) <=? Znth s norm then 0 else fast)
        by (destruct (Z.ltb_spec (Znth s norm) (2 ^ (tl - 1))); destruct (Z.leb_spec (2 ^ (tl - 1)) (Znth s norm)); lia).
      snst SNX s (Znth s norm) (Znth s norm).
      assert (SNLEN' : Z.of_nat (length (upd_nat (Z.to_nat s) (Znth s norm) sn)) = maxSV + 1)
        by (rewrite FseLemmas.upd_nat_length; exact SNLEN).
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + replace (s + 1) with (maxSV + 1) by lia. replace (s + 1) with (maxSV + 1) in P1' by lia.
        eapply KE; [unfold Zupd in P1' |- *; unfold FseNCount.Zlength; close_bd | exact P1'].
      + eapply KH; [unfold Zupd in P1' |- *; unfold FseNCount.Zlength; close_bd | exact P1' | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma bd_p1_loop : forall (f : nat) m1 h0 h1 s tb sn sp high fast x7 xs2 xs8 xs9 xs10 xs11,
    BDm h0 h1 tb sn sp m1 -> p1_inv norm maxSV tl s tb sn high fast -> 0 <= s -> s + Z.of_nat (S f) = maxSV + 1 ->
    (forall m2 tb' sn' high' fast' y7 ys2 ys8, BDm h0 h1 tb' sn' sp m2 -> p1_inv norm maxSV tl (maxSV + 1) tb' sn' high' fast' ->
       evt usegs POST (ST1 0x2a808 m2 high' (maxSV + 1) y7 ys2 ys8 xs9 xs10 xs11 fast')) ->
    evt usegs POST (ST1 0x2a794 m1 high s x7 xs2 xs8 xs9 xs10 xs11 fast).
  Proof.
    induction f as [|f IH]; intros until xs11; intros I P1 HS HSF KONT.
    - eapply bd_p1_body; [exact I | exact P1 | lia | intros; exfalso; lia | exact KONT].
    - eapply bd_p1_body; [exact I | exact P1 | lia | | exact KONT].
      intros m2 tb' sn' high' fast' y7 ys2 ys8 I2 P2 LT.
      eapply (IH m2 h0 h1 (s + 1)); [exact I2 | exact P2 | lia | lia | exact KONT].
  Qed.
End P1.
