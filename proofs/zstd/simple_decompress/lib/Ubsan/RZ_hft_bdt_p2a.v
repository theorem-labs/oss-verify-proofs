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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_hft_iface RZ_hft_bdt_defs RZ_fse_bdt_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma sv_byte_mod : forall s j, 0 <= s < 256 -> 0 <= j < 8 -> (Z.shiftr (s * 72340172838076673) (8 * j)) mod 256 = s mod 256.
Proof. intros s j Hs Hj. rewrite (sv_byte s j Hs Hj). symmetry. apply Z.mod_small. exact Hs. Qed.
Lemma sv_byte_mod0 : forall s, 0 <= s < 256 -> (s * 72340172838076673) mod 256 = s mod 256.
Proof. intros s Hs. pose proof (sv_byte_mod s 0 Hs ltac:(lia)) as H. rewrite Z.shiftr_0_r in H. exact H. Qed.

Section P2A.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DT NC W wlen maxSV tl : Z) (norm : list Z).
  Hypothesis HY : bd_hyps SPV lo DT NC W wlen maxSV tl norm.
  Hypothesis HU : lo <= SPV - 128 /\ DT mod 4 = 0 /\ W mod 2 = 0 /\ NC mod 2 = 0.
  Notation POST := (fse_bdt_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W wlen tl lo m).
  Notation ST pc mm x1 x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation BDm := (BDU ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC W wlen maxSV tl norm).
  Notation HIGH := (hhigh norm maxSV tl).
  Notation STEP := (fse_tablestep (2^tl)).
  Notation SRC := (hSRC norm maxSV).
  Notation KK := 72340172838076673.

  Hypothesis NOLOW : HIGH = 2^tl - 1.

  (* [comment removed for export] *)
  Notation STL pc mm x1 x7 xs0 xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x30 pos :=
    (ST pc mm x1 (Z_to_bv 64 (znot (DT + 4))) (Z_to_bv 64 (2^tl + -1)) x7 xs0 (Z_to_bv 64 KK) xa0
        (Z_to_bv 64 NC) (Z_to_bv 64 maxSV) (Z_to_bv 64 STEP) (Z_to_bv 64 W) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 (znot W)) (Z_to_bv 64 (DT + 4))
        xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (znot NC)) (Z_to_bv 64 (W + 2 * maxSV + 2)) x30 (Z_to_bv 64 pos)).
  (* [comment removed for export] *)
  Notation STLB pc mm s pos x1 x7 xa0 xs2 x30 :=
    (STL pc mm x1 x7 (Z_to_bv 64 (s * KK)) xa0 xs2 (Z_to_bv 64 s)
         (Z_to_bv 64 ((s * KK) ≫ 56)) (Z_to_bv 64 ((s * KK) ≫ 48)) (Z_to_bv 64 ((s * KK) ≫ 40)) (Z_to_bv 64 ((s * KK) ≫ 32))
         (Z_to_bv 64 ((s * KK) ≫ 24)) (Z_to_bv 64 ((s * KK) ≫ 16)) (Z_to_bv 64 (Znth s norm)) (Z_to_bv 64 ((s * KK) ≫ 8)) x30 pos).
  Notation RAL pos := (Z_to_bv 64 (znot (W + 2 * maxSV + 2 + pos))).
  Notation T2L pos := (Z_to_bv 64 (W + 2 * maxSV + pos)).

  (* [comment removed for export] *)
  Ltac sb1 SPRD p k s := u8_sok SPRD (p + k); zstep; hide_not_mentioning W; u8_store SPRD (p + k) s;
                         [ first [ apply sv_byte_mod0; lia | exact (sv_byte_mod s k ltac:(lia) ltac:(lia)) ] | unhide ].

  (* [comment removed for export] *)
  Lemma bd_lay_inner_body : forall m1 h0 h1 tb sn sp s i xs2,
    BDm h0 h1 tb sn sp m1 -> lay_inv norm maxSV s sp -> 0 <= s <= maxSV -> 8 <= i -> i < Znth s norm ->
    (forall j, nsrc norm s <= j < nsrc norm s + i -> Znth j sp = s) ->
    (forall m2 sp' ys2, BDm h0 h1 tb sn sp' m2 -> lay_inv norm maxSV s sp' -> i + 8 < Znth s norm ->
       (forall j, nsrc norm s <= j < nsrc norm s + (i + 8) -> Znth j sp' = s) ->
       evt usegs POST (STLB 0x2a8f0 m2 s (nsrc norm s) (RAL (nsrc norm s)) (T2L (nsrc norm s)) (Z_to_bv 64 (i + 8)) ys2 (Z_to_bv 64 (i + 8 + 2)))) ->
    (forall m2 sp' y1 y7 ya0 ys2 y30, BDm h0 h1 tb sn sp' m2 -> lay_inv norm maxSV (s + 1) sp' ->
       evt usegs POST (STLB 0x2a928 m2 s (nsrc norm s) y1 y7 ya0 ys2 y30)) ->
    evt usegs POST (STLB 0x2a8f0 m1 s (nsrc norm s) (RAL (nsrc norm s)) (T2L (nsrc norm s)) (Z_to_bv 64 i) xs2 (Z_to_bv 64 (i + 2))).
  Proof.
    intros until xs2; intros I LI HS HI8 HIN HSP KH KONT; open_bh HY; open_bd I. pose proof HU as (LOU & _ & _ & _).
    destruct (bd_size_rng _ _ _ _ _ _ _ _ _ HY) as (SZ & _).
    unfold FseNCount.Zlength in *.
    pose proof (nsrc_S norm s ltac:(lia)) as NS1; pose proof (nsrc_mono norm (s + 1) (maxSV + 1) ltac:(lia)) as NS2;
      pose proof (hSRC_total norm maxSV tl TLR MSVR NLEN NGE NSUM) as NS3; pose proof (nsrc_nonneg norm s) as NS4.
    zstep. zstep. bd_chk.
    zstep. zstep. rewrite (swrap32_small (i + 8)) by lia.
    set (p := nsrc norm s + i) in *.
    sb1 SPRD p 4 s. sb1 SPRD p 5 s. sb1 SPRD p 6 s. sb1 SPRD p 7 s.
    sb1 SPRD p 0 s. sb1 SPRD p 1 s. sb1 SPRD p 2 s. sb1 SPRD p 3 s.
    replace (p + 0) with p in SPRD by lia.
    change (Zupd (p + 3) s (Zupd (p + 2) s (Zupd (p + 1) s (Zupd p s (Zupd (p + 7) s (Zupd (p + 6) s (Zupd (p + 5) s (Zupd (p + 4) s sp))))))))
           with (wr8m sp p s) in SPRD.
    rewrite (wr8m_eq sp p s) in SPRD by (unfold FseNCount.Zlength; lia).
    destruct (lay_write8 norm maxSV tl TLR MSVR NLEN NGE NSUM s i sp HS ltac:(lia) ltac:(unfold FseNCount.Zlength; lia) LI HSP) as (LI' & HSP').
    fold p in LI', HSP'.
    assert (SPLEN' : Z.of_nat (length (write8 sp p s)) = wlen - 2 * (maxSV + 1)) by (rewrite write8_length; exact SPLEN).
    assert (SPBY' : Forall isbyte (write8 sp p s)) by (apply write8_bytes; [lia| exact SPBY]).
    zstep; zstep; if_cases K; zify_cond K; try rewrite !signed_lit in K by lia.
    - replace (i + 10) with (i + 8 + 2) by lia.
      eapply KH; [unfold FseNCount.Zlength; close_bd | exact LI' | lia |].
      intros j Hj. apply HSP'. unfold p. lia.
    - eapply KONT; [unfold FseNCount.Zlength; close_bd|].
      apply (lay_next norm maxSV tl TLR MSVR NLEN NGE NSUM s (i + 8)); [exact HS | lia | lia | exact LI' |].
      intros j Hj. apply HSP'. unfold p. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_lay_inner : forall (f : nat) m1 h0 h1 tb sn sp s i xs2,
    BDm h0 h1 tb sn sp m1 -> lay_inv norm maxSV s sp -> 0 <= s <= maxSV -> 8 <= i -> i < Znth s norm -> Znth s norm <= i + 8 * Z.of_nat (S f) ->
    (forall j, nsrc norm s <= j < nsrc norm s + i -> Znth j sp = s) ->
    (forall m2 sp' y1 y7 ya0 ys2 y30, BDm h0 h1 tb sn sp' m2 -> lay_inv norm maxSV (s + 1) sp' ->
       evt usegs POST (STLB 0x2a928 m2 s (nsrc norm s) y1 y7 ya0 ys2 y30)) ->
    evt usegs POST (STLB 0x2a8f0 m1 s (nsrc norm s) (RAL (nsrc norm s)) (T2L (nsrc norm s)) (Z_to_bv 64 i) xs2 (Z_to_bv 64 (i + 2))).
  Proof.
    induction f as [|f IH]; intros until xs2; intros I LI HS HI8 HIN HF HSP KONT.
    - eapply bd_lay_inner_body; [exact I | exact LI | exact HS | exact HI8 | exact HIN | exact HSP | | exact KONT].
      intros; exfalso; lia.
    - eapply bd_lay_inner_body; [exact I | exact LI | exact HS | exact HI8 | exact HIN | exact HSP | | exact KONT].
      intros m2 sp' ys2 I2 LI2 LT HSP2.
      eapply (IH m2 h0 h1 tb sn sp' s (i + 8)); [exact I2 | exact LI2 | exact HS | lia | lia | lia | exact HSP2 | exact KONT].
  Qed.

  (* [comment removed for export] *)
  Lemma bd_lay_body : forall m1 h0 h1 tb sn sp s x1 x7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x30,
    BDm h0 h1 tb sn sp m1 -> lay_inv norm maxSV s sp -> 0 <= s <= maxSV ->
    (forall m2 sp' y1 y7 ya0 ys2 y30, BDm h0 h1 tb sn sp' m2 -> lay_inv norm maxSV (s + 1) sp' ->
       evt usegs POST (STLB 0x2a85c m2 s (nsrc norm s) y1 y7 ya0 ys2 y30)) ->
    evt usegs POST (STL 0x2a86c m1 x1 x7 (Z_to_bv 64 (s * KK)) (Z_to_bv 64 s) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x30 (nsrc norm s)).
  Proof.
    intros until x30; intros I LI HS KN; open_bh HY; open_bd I. pose proof HU as (LOU & _ & _ & _).
    destruct (bd_size_rng _ _ _ _ _ _ _ _ _ HY) as (SZ & _).
    unfold FseNCount.Zlength in *.
    pose proof (nsrc_S norm s ltac:(lia)) as NS1; pose proof (nsrc_mono norm (s + 1) (maxSV + 1) ltac:(lia)) as NS2;
      pose proof (hSRC_total norm maxSV tl TLR MSVR NLEN NGE NSUM) as NS3; pose proof (nsrc_nonneg norm s) as NS4.
    pose proof (hnolow norm maxSV tl TLR MSVR NLEN NGE NSUM s NOLOW HS) as NN.
    assert (NR : -1 <= Znth s norm <= 2^tl) by (apply (hnorm_range norm maxSV tl TLR MSVR NLEN NGE NSUM); exact HS).
    zstep. zstep. zstep. rewrite (shl32_shr31 s) by lia.
    zstep. bd_chk.
    zstep. zstep. bd_chk.
    zstep. rewrite (Z.mod_small s 4294967296) by lia.
    do 6 zstep.
    zstep. zstep.
    replace (NC + s ≪ 1) with (NC + 2 * s) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u16_znth usegs m1 NC norm s a NCB ltac:(lia) ltac:(addr_tac)) as RD end.
    zstep. rewrite (sx16_short (Znth s norm)) by lia.
    set (p := nsrc norm s) in *.
    sb1 SPRD p 4 s. sb1 SPRD p 5 s. sb1 SPRD p 6 s. sb1 SPRD p 7 s.
    zstep.
    sb1 SPRD p 0 s. sb1 SPRD p 1 s. sb1 SPRD p 2 s. sb1 SPRD p 3 s.
    replace (p + 0) with p in SPRD by lia.
    change (Zupd (p + 3) s (Zupd (p + 2) s (Zupd (p + 1) s (Zupd p s (Zupd (p + 7) s (Zupd (p + 6) s (Zupd (p + 5) s (Zupd (p + 4) s sp))))))))
           with (wr8m sp p s) in SPRD.
    rewrite (wr8m_eq sp p s) in SPRD by (unfold FseNCount.Zlength; lia).
    destruct (lay_write8 norm maxSV tl TLR MSVR NLEN NGE NSUM s 0 sp HS ltac:(lia) ltac:(unfold FseNCount.Zlength; fold p; lia) LI ltac:(intros; lia)) as (LI' & HSP').
    fold p in LI', HSP'. rewrite Z.add_0_r in LI', HSP'.
    assert (SPLEN' : Z.of_nat (length (write8 sp p s)) = wlen - 2 * (maxSV + 1)) by (rewrite write8_length; exact SPLEN).
    assert (SPBY' : Forall isbyte (write8 sp p s)) by (apply write8_bytes; [lia| exact SPBY]).
    zstep. zstep. if_cases K; zify_cond K.
    - rewrite signed_lit in K by lia.
      eapply KN; [unfold FseNCount.Zlength; close_bd|].
      apply (lay_next norm maxSV tl TLR MSVR NLEN NGE NSUM s 8); [exact HS | lia | lia | exact LI' | exact HSP'].
    - rewrite signed_lit in K by lia.
      zstep. bd_chk.
      zstep. zstep. zstep. zstep. zstep.
      eapply (bd_lay_inner (Z.to_nat (Znth s norm / 8)) _ h0 h1 tb sn (write8 sp p s) s 8);
        [unfold FseNCount.Zlength; close_bd | exact LI' | exact HS | lia | lia | | exact HSP' |].
      + clear - K NR. Z.div_mod_to_equations. lia.
      + intros mz spz y1 y7 ya0 ys2 y30 I2 LI2. zstep. eapply KN; [exact I2 | exact LI2].
  Qed.

  (* [comment removed for export] *)
  Lemma bd_lay_loop : forall (f : nat) m1 h0 h1 tb sn sp s x1 x7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x30,
    BDm h0 h1 tb sn sp m1 -> lay_inv norm maxSV s sp -> 0 <= s -> s + Z.of_nat (S f) = maxSV + 1 ->
    (forall m2 sp' y1 y7 ys0 ya0 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y30, BDm h0 h1 tb sn sp' m2 -> lay_inv norm maxSV (maxSV + 1) sp' ->
       evt usegs POST (STL 0x2a9a0 m2 y1 y7 ys0 ya0 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y30 (2^tl))) ->
    evt usegs POST (STL 0x2a86c m1 x1 x7 (Z_to_bv 64 (s * KK)) (Z_to_bv 64 s) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x30 (nsrc norm s)).
  Proof.
    induction f as [|f IH]; intros until x30; intros I LI HS HSF KE; open_bh HY.
    all: pose proof (hSRC_total norm maxSV tl TLR MSVR NLEN NGE NSUM) as NS3; rewrite NOLOW in NS3.
    all: pose proof (nsrc_S norm s ltac:(lia)) as NS1; pose proof (hnolow norm maxSV tl TLR MSVR NLEN NGE NSUM s NOLOW ltac:(lia)) as NN.
    all: eapply bd_lay_body; [exact I | exact LI | lia |]; intros m2 sp' y1 y7 ya0 ys2 y30 I2 LI2.
    all: zstep; replace (nsrc norm s + Znth s norm) with (nsrc norm (s + 1)) by lia;
         zstep; rewrite (swrap32_small (s + 1)) by lia;
         zstep; replace (s * KK + KK) with ((s + 1) * KK) by lia; zstep; if_cases K; zify_cond K.
    - replace (s + 1) with (maxSV + 1) in * by lia. replace (nsrc norm (maxSV + 1)) with (2^tl) by lia.
      eapply KE; [exact I2 | exact LI2].
    - exfalso; lia.
    - exfalso; lia.
    - eapply (IH m2 h0 h1 tb sn sp' (s + 1)); [exact I2 | exact LI2 | lia | lia | exact KE].
  Qed.

  (* [comment removed for export] *)
  Notation STPL pc mm x1 xs0 xs1 xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x30 j pos :=
    (ST pc mm x1 (Z_to_bv 64 (znot (DT + 4))) (Z_to_bv 64 (2^tl + -1)) (Z_to_bv 64 (W + 2 * maxSV + 3)) xs0 xs1 xa0
        (Z_to_bv 64 j) (Z_to_bv 64 (znot (W + 2 * maxSV + 2))) (Z_to_bv 64 STEP) (Z_to_bv 64 W) (Z_to_bv 64 (2^tl))
        (Z_to_bv 64 (znot W)) (Z_to_bv 64 (DT + 4)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
        (Z_to_bv 64 (2 * STEP)) (Z_to_bv 64 (W + 2 * maxSV + 2)) x30 (Z_to_bv 64 pos)).

  (* [comment removed for export] *)
  Lemma bd_place_body : forall m1 h0 h1 tb sn sp j x1 xs0 xs1 xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x30,
    BDm h0 h1 tb sn sp m1 -> lay_inv norm maxSV (maxSV + 1) sp -> p2_inv norm maxSV tl j tb ->
    0 <= j -> j + 2 <= 2^tl ->
    (forall m2 tb' ya0 y30, BDm h0 h1 tb' sn sp m2 -> p2_inv norm maxSV tl (j + 2) tb' -> j + 2 < 2^tl ->
       evt usegs POST (STPL 0x2a9b8 m2 x1 xs0 xs1 ya0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 y30 (j + 2) (((j + 2) * STEP) mod 2^tl))) ->
    (forall m2 tb' ya0 y30 pos', BDm h0 h1 tb' sn sp m2 -> p2_inv norm maxSV tl (2^tl) tb' ->
       evt usegs POST (STPL 0x2aa0c m2 x1 xs0 xs1 ya0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 y30 (2^tl) pos')) ->
    evt usegs POST (STPL 0x2a9b8 m1 x1 xs0 xs1 xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x30 j ((j * STEP) mod 2^tl)).
  Proof.
    intros until x30; intros I LI P2 HJ HJF KH KE; open_bh HY; open_bd I. pose proof HU as (LOU & _ & _ & _).
    destruct (bd_size_rng _ _ _ _ _ _ _ _ _ HY) as (SZ & _).
    unfold FseNCount.Zlength in *.
    pose proof (hSRC_total norm maxSV tl TLR MSVR NLEN NGE NSUM) as NS3; rewrite NOLOW in NS3.
    assert (STEPR : 0 <= STEP < 1048576) by (unfold fse_tablestep; Z.div_mod_to_equations; lia).
    assert (PR0 : 0 <= (j * STEP) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
    assert (PR1 : 0 <= ((j + 1) * STEP) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
    assert (E1 : ((j * STEP) mod 2^tl + STEP) mod 2^tl = ((j + 1) * STEP) mod 2^tl)
      by (rewrite Z.add_mod_idemp_l by lia; f_equal; lia).
    assert (E2 : ((j * STEP) mod 2^tl + 2 * STEP) mod 2^tl = ((j + 2) * STEP) mod 2^tl)
      by (rewrite Z.add_mod_idemp_l by lia; f_equal; lia).
    assert (HP : forall k, 0 <= k <= 2^tl - 1 -> Znth k (hpos tl HIGH) = (k * STEP) mod 2^tl)
      by (intros k Hk; rewrite NOLOW; rewrite (Znth_hpos tl (2^tl - 1) k Hk), (pos_iter_nohigh tl TLR); rewrite Z2Nat.id by lia; reflexivity).
    destruct (p2_step norm maxSV tl TLR MSVR NLEN NGE NSUM j tb P2 ltac:(rewrite NOLOW; lia)) as (_ & P2a).
    rewrite (HP j ltac:(lia)) in P2a. rewrite <- (LI j ltac:(lia)) in P2a.
    destruct (p2_step norm maxSV tl TLR MSVR NLEN NGE NSUM (j + 1) _ P2a ltac:(rewrite NOLOW; lia)) as (_ & P2b).
    rewrite (HP (j + 1) ltac:(lia)) in P2b. rewrite <- (LI (j + 1) ltac:(lia)) in P2b.
    replace (j + 1 + 1) with (j + 2) in P2b by lia.
    clear HP P2 P2a.
    (* [comment removed for export] *)
    remember ((j * STEP) mod 2^tl) as pos eqn:EPOS. remember (((j + 1) * STEP) mod 2^tl) as pos1 eqn:EPOS1.
    remember (((j + 2) * STEP) mod 2^tl) as pos2 eqn:EPOS2. clear EPOS EPOS1 EPOS2.
    assert (LAND : forall x, 0 <= x -> Z.land x (2^tl + -1) = x mod 2^tl)
      by (intros x Hx; replace (2^tl + -1) with (Z.ones tl) by (rewrite Z.ones_equiv; lia); apply Z.land_ones; lia).
    assert (JR : 0 <= j /\ j + 1 < 2^tl) by lia.
    assert (SB0 : 0 <= Znth j sp < 256) by (apply (Forall_Znth _ sp j SPBY); lia).
    assert (SB1 : 0 <= Znth (j + 1) sp < 256) by (apply (Forall_Znth _ sp (j + 1) SPBY); lia).
    zstep. bd_chk.
    zstep. rewrite (LAND pos) by lia; rewrite (Z.mod_small pos (2^tl)) by lia.
    zstep. rewrite ?(Z.mod_small pos 18446744073709551616) by lia.
    replace (pos ≪ 2) with (4 * pos) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. bd_chk.
    zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u8_znth usegs m1 (W + 2 * (maxSV + 1)) sp j a SPRD ltac:(lia) ltac:(addr_tac)) as RD end.
    zstep; cbv beta; rewrite (byte_lit (Znth j sp)) by lia.
    zstep.
    tbst CEL (4 * pos + 2) (Znth j sp); [reflexivity|].
    zstep. bd_chk.
    zstep. zstep. rewrite (LAND (pos + STEP)) by lia. rewrite E1.
    zstep. rewrite ?(Z.mod_small pos1 18446744073709551616) by lia.
    replace (pos1 ≪ 2) with (4 * pos1) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. bd_chk.
    zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u8_znth usegs _ (W + 2 * (maxSV + 1)) sp (j + 1) a SPRD ltac:(lia) ltac:(addr_tac)) as RD1 end.
    zstep; cbv beta; rewrite (byte_lit (Znth (j + 1) sp)) by lia.
    zstep. zstep. zstep.
    tbst CEL (4 * pos1 + 2) (Znth (j + 1) sp); [reflexivity|].
    zstep.
    replace (Z.land (pos + 2 * STEP) (2^tl + -1)) with pos2
      by (replace (2^tl + -1) with (Z.ones tl) by (rewrite Z.ones_equiv; lia); rewrite Z.land_ones by lia; symmetry; exact E2).
    set (tb2 := Zupd (4 * pos1 + 2) (Znth (j + 1) sp) (Zupd (4 * pos + 2) (Znth j sp) tb)) in *.
    assert (CLEN' : Z.of_nat (length tb2) = 4 * 2^tl) by (unfold tb2; rewrite !FseLemmas.Zupd_length; exact CLEN).
    assert (CBY' : Forall isbyte tb2) by (unfold tb2; repeat apply Forall_Zupd; [exact CBY | lia | lia]).
    zstep; if_cases K; zify_cond K.
    - eapply KH; [unfold tb2, Zupd in *; unfold FseNCount.Zlength; close_bd | exact P2b | lia].
    - replace (j + 2) with (2^tl) in P2b |- * by lia.
      eapply KE; [unfold tb2, Zupd in *; unfold FseNCount.Zlength; close_bd | exact P2b].
  Qed.

  (* [comment removed for export] *)
  Lemma bd_place_loop : forall (f : nat) m1 h0 h1 tb sn sp j x1 xs0 xs1 xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x30,
    BDm h0 h1 tb sn sp m1 -> lay_inv norm maxSV (maxSV + 1) sp -> p2_inv norm maxSV tl j tb ->
    0 <= j -> j + 2 * Z.of_nat (S f) = 2^tl ->
    (forall m2 tb' y1 y5 y6 y7 ys0 ys1 ya0 ya1 ya2 ya3 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31,
       BDm h0 h1 tb' sn sp m2 -> symtab_ok norm maxSV tl tb' -> zlenF tb' = 4 * 2^tl ->
       evt usegs POST (ST 0x2aa1c m2 y1 y5 y6 y7 ys0 ys1 ya0 ya1 ya2 ya3 (Z_to_bv 64 W) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 (znot W)) (Z_to_bv 64 (DT + 4))
                          ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31)) ->
    evt usegs POST (STPL 0x2a9b8 m1 x1 xs0 xs1 xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x30 j ((j * STEP) mod 2^tl)).
  Proof.
    induction f as [|f IH]; intros until x30; intros I LI P2 HJ HJF KP3; open_bh HY.
    - eapply bd_place_body; [exact I | exact LI | exact P2 | exact HJ | lia | intros; exfalso; lia |].
      intros m2 tb' ya0 y30 pos' I2 P2'. zstep.
      pose proof I2 as I2'. open_bd I2'.
      eapply KP3; [exact I2 | | exact CLEN].
      apply (p2_done norm maxSV tl TLR MSVR NLEN NGE NSUM). rewrite NOLOW. replace (2^tl - 1 + 1) with (2^tl) by lia. exact P2'.
    - eapply bd_place_body; [exact I | exact LI | exact P2 | exact HJ | lia | |].
      + intros m2 tb' ya0 y30 I2 P2' LT.
        eapply (IH m2 h0 h1 tb' sn sp (j + 2)); [exact I2 | exact LI | exact P2' | lia | lia | exact KP3].
      + intros m2 tb' ya0 y30 pos' I2 P2'. zstep.
        pose proof I2 as I2'. open_bd I2'.
        eapply KP3; [exact I2 | | exact CLEN].
        apply (p2_done norm maxSV tl TLR MSVR NLEN NGE NSUM). rewrite NOLOW. replace (2^tl - 1 + 1) with (2^tl) by lia. exact P2'.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_fast : forall m1 h0 h1 tb sn sp x1 x7 xs0 xa0 xa3 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x30 x31,
    BDm h0 h1 tb sn sp m1 -> p2_inv norm maxSV tl 0 tb ->
    (forall m2 tb' sp' y1 y5 y6 y7 ys0 ys1 ya0 ya1 ya2 ya3 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31,
       BDm h0 h1 tb' sn sp' m2 -> symtab_ok norm maxSV tl tb' -> zlenF tb' = 4 * 2^tl ->
       evt usegs POST (ST 0x2aa1c m2 y1 y5 y6 y7 ys0 ys1 ya0 ya1 ya2 ya3 (Z_to_bv 64 W) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 (znot W)) (Z_to_bv 64 (DT + 4))
                          ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31)) ->
    evt usegs POST (ST 0x2a830 m1 x1 (Z_to_bv 64 (znot (DT + 4))) (Z_to_bv 64 (2^tl + -1)) x7 xs0 (Z_to_bv 64 (2^tl / 2)) xa0
                       (Z_to_bv 64 NC) (Z_to_bv 64 maxSV) xa3 (Z_to_bv 64 W) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 (znot W)) (Z_to_bv 64 (DT + 4))
                       xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (znot NC)) (Z_to_bv 64 (W + 2 * maxSV + 2)) x30 x31).
  Proof.
    intros until x31; intros I P2 KP3. open_bh HY.
    destruct (bd_size_rng _ _ _ _ _ _ _ _ _ HY) as (SZ & _).
    zstep. zstep. zstep.
    zstep. rewrite (srliw_val (2^tl) 3) by lia. rewrite (Z.mod_small (2^tl) 4294967296) by lia. change (2^3) with 8.
    zstep. zstep. zstep. zstep.
    rewrite (swrap32_small (2 ^ tl / 8 + 2 ^ tl / 2 + 3)) by (Z.div_mod_to_equations; lia).
    replace (2 ^ tl / 8 + 2 ^ tl / 2 + 3) with STEP by (unfold fse_tablestep; lia).
    zstep. zstep. zstep.
    eapply (bd_lay_loop (Z.to_nat maxSV) m1 h0 h1 tb sn sp 0); [exact I | intros j Hj; rewrite nsrc_0 in Hj; lia | lia | lia |].
    intros m2 sp' y1 y7 ys0 ya0 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y30 I2 LI2.
    pose proof I2 as I2'. open_bd I2'.
    zstep. zstep. zstep. zstep. zstep. zstep.
    assert (STEPR : 0 <= STEP < 1048576) by (unfold fse_tablestep; Z.div_mod_to_equations; lia).
    rewrite ?(Z.mod_small STEP 18446744073709551616) by lia.
    replace (STEP ≪ 1) with (2 * STEP) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    eapply (bd_place_loop (Z.to_nat (2^tl / 2 - 1)) m2 h0 h1 tb sn sp' 0); [exact I2 | exact LI2 | exact P2 | lia | | intros; eapply KP3; eassumption].
    destruct (bd_size_rng _ _ _ _ _ _ _ _ _ HY) as (_ & _ & E2). clear - E2 SZ. Z.div_mod_to_equations. lia.
  Qed.
End P2A.
