(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqBuild ZdSeqBuildThm ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdSeqBuildW4 ZdHufW ZdHufWM.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_hft_iface RZ_hft_bdt_defs RZ_fse_bdt_kit RZ_hft_bdt_p3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section P2B.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DT NC W wlen maxSV tl : Z) (norm : list Z).
  Hypothesis HY : bd_hyps SPV lo DT NC W wlen maxSV tl norm.
  Hypothesis HUB : lo <= SPV - 128 /\ DT mod 4 = 0 /\ W mod 2 = 0 /\ NC mod 2 = 0.
  Notation POST := (fse_bdt_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W wlen tl lo m).
  Notation ST pc mm x1 x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation BDm := (BDU ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC W wlen maxSV tl norm).
  Notation HIGH := (hhigh norm maxSV tl).
  Notation STEP := (fse_tablestep (2^tl)).
  Notation PITER k := (pos_iter (Z.to_nat k) (2^tl) STEP HIGH 0).

  (* [comment removed for export] *)
  Notation STC pc mm x1 xpos xs xi xs1 xn xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 :=
    (ST pc mm x1 (Z_to_bv 64 (znot (DT + 4))) (Z_to_bv 64 (2^tl + -1)) xs xi xs1 xn (Z_to_bv 64 NC) xpos xa3
        (Z_to_bv 64 W) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 (znot W)) (Z_to_bv 64 (DT + 4)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
        (Z_to_bv 64 (znot NC)) (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 HIGH) (Z_to_bv 64 STEP)).

  Lemma bd_step_rng : 0 <= STEP < 1048576.
  Proof. destruct (bd_size_rng _ _ _ _ _ _ _ _ _ HY) as (SZ & _). unfold fse_tablestep. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma bd_skip : forall (fu : nat) m1 p x1 xs xi xs1 xn xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11,
    0 <= HIGH -> 0 <= p < 2^tl ->
    skip_low fu (2^tl) STEP HIGH ((p + STEP) mod 2^tl) <= HIGH ->
    evt usegs POST
       (STC 0x2a994 m1 x1 (Z_to_bv 64 (skip_low fu (2^tl) STEP HIGH ((p + STEP) mod 2^tl))) xs xi xs1 xn xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) ->
    evt usegs POST (STC 0x2a988 m1 x1 (Z_to_bv 64 p) xs xi xs1 xn xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11).
  Proof.
    intros fu. induction fu as [|fu IH]; intros until xs11; intros HH HP SK KONT.
    all: destruct (bd_size_rng _ _ _ _ _ _ _ _ _ HY) as (SZ & _); pose proof bd_step_rng as HST; open_bh HY.
    all: pose proof (hhigh_range norm maxSV tl TLR ltac:(lia) NLEN NGE NSUM) as HR.
    all: assert (QR : 0 <= (p + STEP) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
    all: zstep; rewrite (swrap32_small (STEP + p)) by lia; zstep;
         replace (2^tl + -1) with (Z.ones tl) by (rewrite Z.ones_equiv; lia); rewrite (Z.land_ones (STEP + p) tl) by lia;
         replace (STEP + p) with (p + STEP) by lia;
         replace (Z.ones tl) with (2^tl + -1) by (rewrite Z.ones_equiv; lia).
    all: zstep; if_cases K; zify_cond K.
    - exfalso. cbn [skip_low] in SK. lia.
    - cbn [skip_low] in SK, KONT. apply KONT.
    - cbn [skip_low] in SK, KONT. destruct (Z.ltb_spec HIGH ((p + STEP) mod 2^tl)); [|lia].
      eapply (IH m1 ((p + STEP) mod 2^tl)); [exact HH | exact QR | exact SK | exact KONT].
    - cbn [skip_low] in SK, KONT. destruct (Z.ltb_spec HIGH ((p + STEP) mod 2^tl)); [lia|]. apply KONT.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_place_n : forall (kk : nat) m1 h0 h1 tb sn sp s i x1 xs1 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11,
    BDm h0 h1 tb sn sp m1 -> p2_inv norm maxSV tl (nsrc norm s + i) tb ->
    0 <= s <= maxSV -> 0 <= i -> i + Z.of_nat (S kk) = Znth s norm ->
    (forall m2 tb' ys1, BDm h0 h1 tb' sn sp m2 -> p2_inv norm maxSV tl (nsrc norm (s + 1)) tb' ->
       evt usegs POST
         (STC 0x2a99c m2 x1 (Z_to_bv 64 (PITER (nsrc norm (s + 1)))) (Z_to_bv 64 s) (Z_to_bv 64 (Znth s norm)) ys1 (Z_to_bv 64 (Znth s norm)) xa3
              xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11)) ->
    evt usegs POST
      (STC 0x2a978 m1 x1 (Z_to_bv 64 (PITER (nsrc norm s + i))) (Z_to_bv 64 s) (Z_to_bv 64 i) xs1 (Z_to_bv 64 (Znth s norm)) xa3
           xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11).
  Proof.
    intros kk. induction kk as [|kk IH]; intros until xs11; intros I P2 HS HI HIN KONT; open_bh HY; open_bd I.
    all: pose proof HUB as (LOU & _ & _ & _).
    all: destruct (bd_size_rng _ _ _ _ _ _ _ _ _ HY) as (SZ & _); pose proof bd_step_rng as HST.
    all: unfold FseNCount.Zlength in *.
    all: pose proof (hhigh_range norm maxSV tl TLR ltac:(lia) NLEN NGE NSUM) as HR.
    all: pose proof (nsrc_S norm s ltac:(lia)) as NS1; pose proof (nsrc_mono norm (s + 1) (maxSV + 1) ltac:(lia)) as NS2;
         pose proof (hSRC_total norm maxSV tl TLR MSVR NLEN NGE NSUM) as NS3; pose proof (nsrc_nonneg norm s) as NS4.
    all: assert (KR : 0 <= nsrc norm s + i <= HIGH) by lia.
    all: destruct (p2_step norm maxSV tl TLR MSVR NLEN NGE NSUM (nsrc norm s + i) tb P2 KR) as (PR & P2').
    all: rewrite (Znth_hpos tl HIGH (nsrc norm s + i) KR) in PR, P2'.
    all: rewrite (hSRC_at norm maxSV tl TLR MSVR NLEN NGE NSUM s i HS ltac:(lia)) in P2'.
    all: set (position := PITER (nsrc norm s + i)) in *.
    all: zstep; rewrite ?(Z.mod_small position 18446744073709551616) by lia;
         rewrite ?(Z.mod_small (position ≪ 2) 18446744073709551616) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
         replace (position ≪ 2) with (4 * position) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    all: zstep; bd_chk.
    all: zstep.
    all: tbst CEL (4 * position + 2) s; [reflexivity|].
    all: assert (CLEN' : Z.of_nat (length (Zupd (4 * position + 2) s tb)) = 4 * 2^tl) by (rewrite FseLemmas.Zupd_length; exact CLEN).
    all: assert (CBY' : Forall isbyte (Zupd (4 * position + 2) s tb)) by (apply Forall_Zupd; [exact CBY| lia]).
    all: assert (QR : 0 <= (position + STEP) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
    all: pose proof (hskip_low_term tl HIGH ((position + STEP) mod 2^tl) TLR ltac:(lia) QR) as SKT.
    all: eapply (bd_skip (Z.to_nat (2^tl)) _ position); [lia | lia | exact SKT |].
    all: fold (next_pos (2^tl) STEP HIGH position).
    all: assert (NPE : next_pos (2^tl) STEP HIGH position = PITER (nsrc norm s + i + 1))
           by (unfold position; replace (Z.to_nat (nsrc norm s + i + 1)) with (S (Z.to_nat (nsrc norm s + i))) by lia; rewrite pos_iter_S; reflexivity).
    all: rewrite NPE.
    all: zstep; rewrite (swrap32_small (i + 1)) by lia; zstep; if_cases K; zify_cond K.
    - exfalso; lia.
    - replace (i + 1) with (Znth s norm) by lia.
      replace (nsrc norm s + i + 1) with (nsrc norm (s + 1)) in * by lia.
      eapply KONT; [unfold Zupd in *; unfold FseNCount.Zlength; close_bd | exact P2'].
    - replace (nsrc norm s + i + 1) with (nsrc norm s + (i + 1)) in * by lia.
      eapply (IH _ h0 h1 (Zupd (4 * position + 2) s tb) sn sp s (i + 1));
        [unfold Zupd in *; unfold FseNCount.Zlength; close_bd | exact P2' | exact HS | lia | lia | exact KONT].
    - exfalso; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_slow_next : forall m1 s x1 xpos xi xs1 xn xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11,
    0 <= s <= maxSV ->
    (s + 1 < maxSV + 1 -> evt usegs POST (STC 0x2a954 m1 x1 xpos (Z_to_bv 64 (s + 1)) xi xs1 xn xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11)) ->
    (s + 1 = maxSV + 1 -> evt usegs POST (STC 0x2aa10 m1 x1 xpos (Z_to_bv 64 (maxSV + 1)) xi xs1 xn xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11)) ->
    evt usegs POST (STC 0x2a94c m1 x1 xpos (Z_to_bv 64 s) xi xs1 xn xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11).
  Proof.
    intros until xs11; intros HS KH KE. open_bh HY.
    zstep. rewrite (swrap32_small (s + 1)) by lia. zstep. if_cases K; zify_cond K.
    - replace (s + 1) with (maxSV + 1) by lia. apply KE. lia.
    - apply KH. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_slow_body : forall m1 h0 h1 tb sn sp s x1 xi xs1 xn xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11,
    BDm h0 h1 tb sn sp m1 -> p2_inv norm maxSV tl (nsrc norm s) tb -> 0 <= s <= maxSV ->
    (forall m2 tb' yi ys1 yn ya3, BDm h0 h1 tb' sn sp m2 -> p2_inv norm maxSV tl (nsrc norm (s + 1)) tb' ->
       evt usegs POST (STC 0x2a94c m2 x1 (Z_to_bv 64 (PITER (nsrc norm (s + 1)))) (Z_to_bv 64 s) yi ys1 yn ya3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11)) ->
    evt usegs POST (STC 0x2a954 m1 x1 (Z_to_bv 64 (PITER (nsrc norm s))) (Z_to_bv 64 s) xi xs1 xn xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11).
  Proof.
    intros until xs11; intros I P2 HS KN. open_bh HY. pose proof I as I0. open_bd I.
    destruct (bd_size_rng _ _ _ _ _ _ _ _ _ HY) as (SZ & _).
    unfold FseNCount.Zlength in *.
    assert (NR : -1 <= Znth s norm <= 2^tl) by (apply (hnorm_range norm maxSV tl TLR MSVR NLEN NGE NSUM); exact HS).
    pose proof (nsrc_S norm s ltac:(lia)) as NS1.
    zstep. zstep. rewrite (shl32_shr31 s) by lia.
    zstep. bd_chk.
    zstep. rewrite (Z.mod_small s 4294967296) by lia.
    zstep. zstep.
    replace (NC + s ≪ 1) with (NC + 2 * s) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u16_znth usegs m1 NC norm s a NCB ltac:(lia) ltac:(addr_tac)) as RD end.
    zstep. rewrite (sx16_short (Znth s norm)) by lia.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (NLE : Znth s norm <= 0).
      { destruct (Z_le_gt_dec (Znth s norm) 0) as [|G]; [assumption|]. exfalso. rewrite Z.mod_small in K by lia.
        destruct (Z.ltb_spec 0 (Znth s norm)), (Z.ltb_spec (Znth s norm) 9223372036854775808); cbn in K; try discriminate; lia. }
      replace (nsrc norm s) with (nsrc norm (s + 1)) in * by lia.
      eapply KN; [exact I0 | exact P2].
    - assert (NPOS : 0 < Znth s norm).
      { destruct (Z_le_gt_dec (Znth s norm) 0) as [L|G]; [|lia]. exfalso.
        assert (E : Znth s norm = 0 \/ Znth s norm = -1) by lia. destruct E as [E|E]; rewrite E in K0, K1; [cbn in K0; lia | change ((-1) mod 18446744073709551616) with 18446744073709551615 in K1; lia]. }
      zstep.
      replace (nsrc norm s) with (nsrc norm s + 0) by lia.
      eapply (bd_place_n (Z.to_nat (Znth s norm - 1)) m1 h0 h1 tb sn sp s 0); [exact I0 | rewrite Z.add_0_r; exact P2 | exact HS | lia | lia |].
      intros m2 tb' ys1 I2 P2'.
      zstep.
      eapply KN; [exact I2 | exact P2'].
  Qed.

  (* [comment removed for export] *)
  Lemma bd_slow_loop : forall (f : nat) m1 h0 h1 tb sn sp s x1 xi xs1 xn xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11,
    BDm h0 h1 tb sn sp m1 -> p2_inv norm maxSV tl (nsrc norm s) tb -> 0 <= s -> s + Z.of_nat (S f) = maxSV + 1 ->
    (forall m2 tb' yi ys1 yn ya3, BDm h0 h1 tb' sn sp m2 -> p2_inv norm maxSV tl (HIGH + 1) tb' ->
       evt usegs POST (STC 0x2aa10 m2 x1 (Z_to_bv 64 (PITER (HIGH + 1))) (Z_to_bv 64 (maxSV + 1)) yi ys1 yn ya3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11)) ->
    evt usegs POST (STC 0x2a954 m1 x1 (Z_to_bv 64 (PITER (nsrc norm s))) (Z_to_bv 64 s) xi xs1 xn xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11).
  Proof.
    induction f as [|f IH]; intros until xs11; intros I P2 HS HSF KE; open_bh HY.
    all: pose proof (hSRC_total norm maxSV tl TLR MSVR NLEN NGE NSUM) as NS3.
    - eapply bd_slow_body; [exact I | exact P2 | lia |].
      intros m2 tb' yi ys1 yn ya3 I2 P2'.
      eapply bd_slow_next; [lia | intros; exfalso; lia |]. intros _.
      replace (s + 1) with (maxSV + 1) in * by lia. rewrite NS3 in *.
      eapply KE; [exact I2 | exact P2'].
    - eapply bd_slow_body; [exact I | exact P2 | lia |].
      intros m2 tb' yi ys1 yn ya3 I2 P2'.
      eapply bd_slow_next; [lia | | intros; exfalso; lia]. intros _.
      eapply (IH m2 h0 h1 tb' sn sp (s + 1)); [exact I2 | exact P2' | lia | lia | exact KE].
  Qed.

  (* [comment removed for export] *)
  Lemma bd_slow : forall m1 h0 h1 tb sn sp x1 x7 xs0 xa0 xa2 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x29,
    BDm h0 h1 tb sn sp m1 -> p2_inv norm maxSV tl 0 tb ->
    (forall m2 tb' y1 y5 y6 y7 ys0 ys1 ya0 ya1 ya2 ya3 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31,
       BDm h0 h1 tb' sn sp m2 -> symtab_ok norm maxSV tl tb' -> zlenF tb' = 4 * 2^tl ->
       evt usegs POST (ST 0x2aa1c m2 y1 y5 y6 y7 ys0 ys1 ya0 ya1 ya2 ya3 (Z_to_bv 64 W) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 (znot W)) (Z_to_bv 64 (DT + 4))
                          ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31)) ->
    evt usegs POST (ST 0x2a92c m1 x1 (Z_to_bv 64 (znot (DT + 4))) (Z_to_bv 64 (2^tl + -1)) x7 xs0 (Z_to_bv 64 (2^tl / 2)) xa0
                       (Z_to_bv 64 NC) xa2 xa3 (Z_to_bv 64 W) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 (znot W)) (Z_to_bv 64 (DT + 4))
                       xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (znot NC)) x29 (Z_to_bv 64 HIGH) (Z_to_bv 64 (maxSV + 1))).
  Proof.
    intros until x29; intros I P2 KP3. open_bh HY.
    destruct (bd_size_rng _ _ _ _ _ _ _ _ _ HY) as (SZ & _).
    zstep. zstep. zstep.
    rewrite (srliw_val (2^tl) 3) by lia. rewrite (Z.mod_small (2^tl) 4294967296) by lia. change (2^3) with 8.
    zstep. zstep. zstep.
    replace (maxSV + 1 + Z.b2z (maxSV + 1 <? 1)) with (maxSV + 1) by (destruct (Z.ltb_spec (maxSV + 1) 1); cbn [Z.b2z]; lia).
    rewrite (swrap32_small (maxSV + 1)) by lia.
    zstep. zstep.
    replace (2 ^ tl / 8 + 2 ^ tl / 2 + 3) with STEP by (unfold fse_tablestep; lia).
    eapply (bd_slow_loop (Z.to_nat maxSV) m1 h0 h1 tb sn sp 0); [exact I | exact P2 | lia | lia |].
    intros m2 tb' yi ys1 yn ya3 I2 P2'.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      pose proof I2 as I2'. open_bd I2'.
      eapply KP3; [exact I2 | apply (p2_done norm maxSV tl TLR MSVR NLEN NGE NSUM); exact P2' | exact CLEN].
    - (* [comment removed for export] *)
      zstep. zstep.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; reflexivity).
      eapply (bd_epi ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DT NC W wlen maxSV tl norm HY HUB m2 h0 h1 tb' sn sp 18446744073709551615); [exact I2| lia |].
      right. reflexivity.
  Qed.
End P2B.
