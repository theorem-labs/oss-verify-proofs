(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqBuild ZdSeqBuildThm ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdSeqBuildW4 ZdHufW ZdHufWM ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_bdt_defs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

(* [comment removed for export] *)
Lemma sv_b0 : forall s, 0 <= s < 256 -> (72340172838076673 * s) mod 256 = s.
Proof. intros s Hs. pose proof (sv_byte s 0 Hs ltac:(lia)) as H. rewrite Z.shiftr_0_r, Z.mul_comm in H. exact H. Qed.
Lemma sv_bd : forall s j D, 0 <= s < 256 -> 0 <= j < 8 -> D = 2^(8 * j) -> ((72340172838076673 * s) mod 2^64 / D) mod 256 = s.
Proof.
  intros s j D Hs Hj ->. rewrite (Z.mod_small (72340172838076673 * s) (2^64)) by lia.
  rewrite <- (Z.shiftr_div_pow2 _ (8 * j)) by lia. rewrite Z.mul_comm. apply sv_byte; lia.
Qed.
(* [comment removed for export] *)
Lemma zupd8_wr8m : forall (sp : list Z) p s i0 i1 i2 i3 i4 i5 i6 i7,
  i0 = p + 4 -> i1 = p + 5 -> i2 = p + 6 -> i3 = p + 7 -> i4 = p -> i5 = p + 1 -> i6 = p + 2 -> i7 = p + 3 ->
  Zupd i7 s (Zupd i6 s (Zupd i5 s (Zupd i4 s (Zupd i3 s (Zupd i2 s (Zupd i1 s (Zupd i0 s sp))))))) = wr8m sp p s.
Proof. intros; subst; reflexivity. Qed.
(* [comment removed for export] *)
Ltac sv_vals s :=
  repeat match goal with
  | H : hidden (?x = (72340172838076673 * s) mod 256) |- _ => unfold hidden in H; rewrite (sv_b0 s) in H by lia; subst x
  | H : hidden (?x = ((72340172838076673 * s) mod 2^64 / ?D) mod 256) |- _ =>
      unfold hidden in H;
      let j := lazymatch D with
               | 256 => constr:(1) | 65536 => constr:(2) | 16777216 => constr:(3) | 4294967296 => constr:(4)
               | 1099511627776 => constr:(5) | 281474976710656 => constr:(6) | 72057594037927936 => constr:(7) end in
      rewrite (sv_bd s j D) in H by (first [reflexivity | lia]); subst x
  end.

Section CANSEC1. Context {rc : runConstT}.
Section P2A.
  Variables (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem)
            (SPV lo DT NC W wlen maxSV tl : Z) (norm : list Z).
  Hypothesis HY : bdA_hyps RNG SPV lo DT NC W wlen maxSV tl norm.
  Hypothesis UDT : unpoisoned m DT (DT + 4 + 4 * 2^tl).
  Hypothesis UW : unpoisoned m W (W + wlen).
  Hypothesis UNC : unpoisoned m NC (NC + 2 * zlen norm).
  Hypothesis ART0 : art m.
  (* [comment removed for export] *)
  Notation BDm := (BDA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC W wlen maxSV tl norm (Z_to_bv 64 (2 * maxSV + W + 10)) (Z_to_bv 64 (fse_tablestep (2^tl)))).
  (* [comment removed for export] *)
  Local Ltac kx_lia ::= kx_lia_sep5 DT NC SPV lo W.
  Local Ltac kxl_lia ::= kx_lia_sep5 DT NC SPV lo W.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac bd_reunp :=
    repeat match goal with H : unpoisoned ?mx _ _ |- _ => lazymatch mx with m => fail | _ => clear H end end;
    lazymatch goal with
    | MU : munch _ m ?m2 |- _ =>
        pose proof (bd_unp_dtM _ _ _ _ _ _ _ _ _ _ _ HY UDT m2 MU) as UDT1;
        pose proof (bd_unp_wM _ _ _ _ _ _ _ _ _ _ _ HY UW m2 MU) as UW1;
        pose proof (bd_unp_ncM _ _ _ _ _ _ _ _ _ _ _ HY UNC m2 MU) as UNC1
    end.
  (* [comment removed for export] *)
  Local Ltac bd_lens :=
    lazymatch goal with
    | CEL : u8arr _ _ (DT + 4) (map _ ?tb), SNX : u8arr _ _ W (u16s (map _ ?sn)), SPRD : u8arr _ _ (W + _) (map _ ?sp) |- _ =>
        first [ assert (zlen tb = 4 * 2^tl) by assumption | assert (zlen tb = 4 * 2^tl) by (rewrite ?Zupd_length2; assumption) ];
        first [ assert (zlen (map (Z_to_bv 8) tb) = 4 * 2^tl) by assumption
              | assert (zlen (map (Z_to_bv 8) tb) = 4 * 2^tl) by (rewrite length_map, ?Zupd_length2; assumption) ];
        first [ assert (zlen sn = maxSV + 1) by assumption | assert (zlen sn = maxSV + 1) by (rewrite ?Zupd_length2; assumption) ];
        first [ assert (zlen (u16s (map (Z_to_bv 64) sn)) = 2 * (maxSV + 1)) by assumption
              | assert (zlen (u16s (map (Z_to_bv 64) sn)) = 2 * (maxSV + 1)) by (rewrite u16s_length, length_map, ?Zupd_length2; lia) ];
        first [ assert (zlen sp = wlen - 2 * (maxSV + 1)) by assumption | assert (zlen sp = wlen - 2 * (maxSV + 1)) by (rewrite ?Zupd_length2, ?write8_length, ?Zupd_length2; assumption) ];
        first [ assert (zlen (map (Z_to_bv 8) sp) = wlen - 2 * (maxSV + 1)) by assumption
              | assert (zlen (map (Z_to_bv 8) sp) = wlen - 2 * (maxSV + 1)) by (rewrite length_map, ?Zupd_length2, ?write8_length, ?Zupd_length2; assumption) ]
    end.
  Local Ltac bd_open I :=
    open_hy HY; open_bd I; unfold KHIGH in *; bd_reunp;
    pose proof (bd_bands _ _ _ _ _ _ _ _ _ _ HY) as (BDT & BW & BSP & B5 & B6 & B7 & B8);
    hide_all_disj;
    pose proof (bdA_size_rng _ _ _ _ _ _ _ _ _ _ HY) as (SZ & LLR & LL2);
    assert (LNC : zlen (u16s (map (Z_to_bv 64) norm)) = 2 * zlen norm) by (rewrite u16s_length, length_map; lia);
    bd_lens.
  (* [comment removed for export] *)
  Local Ltac bd_reopen I :=
    repeat match goal with
           | H : rw_cells _ _ _ _ |- _ => clear H | H : u8arr _ _ _ _ |- _ => clear H | H : bytes_at _ _ _ _ |- _ => clear H
           | H : stk _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H
           | H : wmono _ _ _ |- _ => clear H | H : Z.of_nat (length _) = _ |- _ => clear H | H : Forall _ _ |- _ => clear H
           | H : list byte |- _ => clear H
           end;
    open_bd I; bd_reunp;
    assert (LNC : zlen (u16s (map (Z_to_bv 64) norm)) = 2 * zlen norm) by (rewrite u16s_length, length_map; lia);
    bd_lens.
  (* [comment removed for export] *)
  Notation KZB := [KZRange SPV (0x10007fff8000 + 192) (2^47); KZRange maxSV 0 255; KZRange tl 5 9; KZRange (2^tl) 32 512;
     KZRange NC 4096 (2^47); KZRange DT 4096 (2^47); KZRange W 4096 (2^47); KZRange wlen 40 (2^32); KZRange (zlen norm) 1 (2^46);
     KZRange (NC + 2 * zlen norm) 0 (2^47); KZRange (W + wlen) 0 (2^47 - 8); KZRange (DT + 4 + 4 * 2^tl) 0 (2^47 - 8);
     KZRange (wlen - 2 * maxSV - 2) 40 (2^32); KZAlign DT 4; KZAlign W 2; KZAlign NC 2] (only parsing).
  Notation POST := (fse_bdt_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W wlen tl lo m).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -144)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation HIGH := (hhigh norm maxSV tl).
  Notation STEP := (fse_tablestep (2^tl)).
  Notation SRC := (hSRC norm maxSV).
  Notation KK := 72340172838076673.

  Hypothesis NOLOW : HIGH = 2^tl - 1.

  (* [comment removed for export] *)
  Notation SP0 := (W + 2 * (maxSV + 1)).
  Notation STL pc mm s pos xra xt0 xt2 xs1 xa0 xa2 xa3 xa5 xa6 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 :=
    (ST pc mm xra xt0 (Z_to_bv 64 0x7fff8000) xt2 (Z_to_bv 64 (s * KK)) xs1 xa0 (Z_to_bv 64 NC) xa2 xa3 (Z_to_bv 64 9) xa5 xa6
        (Z_to_bv 64 pos) (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 (SP0 + 8)) (Z_to_bv 64 16843009) xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 SP0) (Z_to_bv 64 s) xt5 xt6).

  (* [comment removed for export] *)
  Notation STLB pc mm s pos xt0 xt2 xs1 xa0 xa2 xa3 xa5 xa6 xt5 xt6 :=
    (ST pc mm (Z_to_bv 64 ((KK * s) mod 2^64 / 256)) xt0 (Z_to_bv 64 0x7fff8000) xt2 (Z_to_bv 64 (s * KK)) xs1 xa0 (Z_to_bv 64 NC) xa2 xa3 (Z_to_bv 64 9) xa5 xa6
        (Z_to_bv 64 pos) (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 (SP0 + 8)) (Z_to_bv 64 16843009) (Z_to_bv 64 (Znth s norm))
        (Z_to_bv 64 ((KK * s) mod 2^64 / 72057594037927936)) (Z_to_bv 64 ((KK * s) mod 2^64 / 281474976710656)) (Z_to_bv 64 ((KK * s) mod 2^64 / 1099511627776))
        (Z_to_bv 64 ((KK * s) mod 2^64 / 4294967296)) (Z_to_bv 64 ((KK * s) mod 2^64 / 16777216)) (Z_to_bv 64 ((KK * s) mod 2^64 / 65536))
        (Z_to_bv 64 SP0) (Z_to_bv 64 s) xt5 xt6).

  (* [comment removed for export] *)
  Lemma bd_lay_inner_bodyA : forall m1 tb sn sp fast s i xt0 xt2 xs1 xa0 xa2 xa3 xa6,
    BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp m1 -> lay_inv norm maxSV s sp -> 0 <= s <= maxSV -> 8 <= i -> i < Znth s norm ->
    (forall j, nsrc norm s <= j < nsrc norm s + i -> Znth j sp = s) ->
    (forall m2 sp' ys1 ya0 ya2, BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp' m2 -> lay_inv norm maxSV s sp' -> i + 8 < Znth s norm ->
       (forall j, nsrc norm s <= j < nsrc norm s + (i + 8) -> Znth j sp' = s) ->
       evtF bsegs RNG POST (STLB 0xaba40 m2 s (nsrc norm s) xt0 xt2 ys1 ya0 ya2 xa3 (Z_to_bv 64 (SP0 + nsrc norm s + (i + 8))) xa6
                              (Z_to_bv 64 (i + 8)) (Z_to_bv 64 (SP0 + nsrc norm s + (i + 8))))) ->
    (forall m2 sp' ys1 ya0 ya2 ya5 yt5 yt6, BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp' m2 -> lay_inv norm maxSV (s + 1) sp' ->
       evtF bsegs RNG POST (STLB 0xab998 m2 s (nsrc norm s) xt0 xt2 ys1 ya0 ya2 xa3 ya5 xa6 yt5 yt6)) ->
    evtF bsegs RNG POST (STLB 0xaba40 m1 s (nsrc norm s) xt0 xt2 xs1 xa0 xa2 xa3 (Z_to_bv 64 (SP0 + nsrc norm s + i)) xa6
                           (Z_to_bv 64 i) (Z_to_bv 64 (SP0 + nsrc norm s + i))).
  Proof.
    intros until xa6; intros I LI HS HI8 HIN HSP KH KONT; bd_open I.
    pose proof (nsrc_S norm s ltac:(lia)) as NS1. pose proof (nsrc_mono norm (s + 1) (maxSV + 1) ltac:(lia)) as NS2.
    pose proof (hSRC_total norm maxSV tl TLR MSVR NLEN NGE NSUM) as NS3. pose proof (nsrc_nonneg norm s) as NS4.
    assert (NR : -1 <= Znth s norm <= 2^tl) by (apply (hnorm_range norm maxSV tl TLR MSVR NLEN NGE NSUM); exact HS).
    rewrite NOLOW in NS3.
    set (p := nsrc norm s + i) in *.
    kx_autoFLAc (FR, HDR) [KAUnp (SP0 + p) 8; KAApp (SP0 + p) 8] [0xaba40; 0xab998] 40%nat
      (KZB ++ [KZRange s 0 255; KZRange p 8 512; KZRange i 8 512; KZRange (Znth s norm - i) 1 512; KZRange (Znth s norm) 9 512;
               KZRange (nsrc norm s) 0 512; KZRange (p - nsrc norm s - i) 0 0;
               KZRange (SP0 + p) 4096 (2^47 - 8); KZRange (wlen - 2 * maxSV - 10 - p) 0 (2^32); KZRange (KK * s) 0 (2^64 - 1);
               KZWr (SP0 + p) 8; KZDisj (SP0 + p) 8 NC (2 * zlen norm); KZDisj (SP0 + p) 8 (SPV - 144) 144;
               KZDisj (SP0 + p) 8 (DT + 4) (4 * 2^tl); KZDisj (SP0 + p) 8 DT 4; KZDisj (SP0 + p) 8 W (2 * (maxSV + 1))])
      (@nil (Z * Z)) [(SP0 + p, 8)].
    all: try kx_z. all: try kx_acc RW. all: try kx_acc RSTK. all: try kx_sh_rd_any. all: try (kx_sh_acc RSW).
    all: kxk_keepg SPRD. all: kx_mem. all: kx_tidy_run. all: bd_reunp.
    all: sv_vals s.
    all: erewrite (zupd8_wr8m sp p s) in * by lia.
    all: rewrite (wr8m_eq sp p s) in * by (unfold FseNCount.Zlength; lia).
    all: destruct (lay_write8 norm maxSV tl TLR MSVR NLEN NGE NSUM s i sp HS ltac:(lia) ltac:(unfold FseNCount.Zlength; fold p; lia) LI HSP) as (LI' & HSP');
         fold p in LI', HSP'.
    all: assert (SPBY' : Forall isbyte (write8 sp p s)) by (apply write8_bytes; [lia| exact SPBY]).
    all: bd_lens.
    all: kx_gen_regsF [9%nat; 10%nat; 12%nat].
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xaba40) _ _ _ _) =>
             kx_setreg 15 (SP0 + nsrc norm s + (i + 8)); kx_setreg 30 (i + 8); kx_setreg 31 (SP0 + nsrc norm s + (i + 8));
             eapply KH; [close_bd | exact LI' | lia | intros j Hj; apply HSP'; unfold p; lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xab998) _ _ _ _) =>
             eapply KONT; [close_bd | ];
             apply (lay_next norm maxSV tl TLR MSVR NLEN NGE NSUM s (i + 8)); [exact HS | lia | lia | exact LI' | intros j Hj; apply HSP'; unfold p; lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_lay_innerA : forall (f : nat) m1 tb sn sp fast s i xt0 xt2 xs1 xa0 xa2 xa3 xa6,
    BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp m1 -> lay_inv norm maxSV s sp -> 0 <= s <= maxSV -> 8 <= i -> i < Znth s norm ->
    Znth s norm <= i + 8 * Z.of_nat (S f) ->
    (forall j, nsrc norm s <= j < nsrc norm s + i -> Znth j sp = s) ->
    (forall m2 sp' ys1 ya0 ya2 ya5 yt5 yt6, BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp' m2 -> lay_inv norm maxSV (s + 1) sp' ->
       evtF bsegs RNG POST (STLB 0xab998 m2 s (nsrc norm s) xt0 xt2 ys1 ya0 ya2 xa3 ya5 xa6 yt5 yt6)) ->
    evtF bsegs RNG POST (STLB 0xaba40 m1 s (nsrc norm s) xt0 xt2 xs1 xa0 xa2 xa3 (Z_to_bv 64 (SP0 + nsrc norm s + i)) xa6
                           (Z_to_bv 64 i) (Z_to_bv 64 (SP0 + nsrc norm s + i))).
  Proof.
    induction f as [|f IH]; intros until xa6; intros I LI HS HI8 HIN HF HSP KONT.
    - eapply bd_lay_inner_bodyA; [exact I | exact LI | exact HS | exact HI8 | exact HIN | exact HSP | | exact KONT].
      intros; exfalso; lia.
    - eapply bd_lay_inner_bodyA; [exact I | exact LI | exact HS | exact HI8 | exact HIN | exact HSP | | exact KONT].
      intros m2 sp' ys1 ya0 ya2 I2 LI2 LT HSP2.
      eapply (IH m2 tb sn sp' fast s (i + 8)); [exact I2 | exact LI2 | exact HS | lia | lia | lia | exact HSP2 | exact KONT].
  Qed.

  (* [comment removed for export] *)
  Lemma bd_lay_bodyA : forall m1 tb sn sp fast s xra xt0 xt2 xs1 xa0 xa2 xa3 xa5 xa6 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6,
    BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp m1 -> lay_inv norm maxSV s sp -> 0 <= s <= maxSV ->
    (forall m2 sp' ys1 ya0 ya2 ya5 yt5 yt6, BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp' m2 -> lay_inv norm maxSV (s + 1) sp' ->
       evtF bsegs RNG POST (STLB 0xab998 m2 s (nsrc norm s) xt0 xt2 ys1 ya0 ya2 xa3 ya5 xa6 yt5 yt6)) ->
    evtF bsegs RNG POST (STL 0xab9b0 m1 s (nsrc norm s) xra xt0 xt2 xs1 xa0 xa2 xa3 xa5 xa6 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6).
  Proof.
    intros until xt6; intros I LI HS KN. pose proof I as I0. bd_open I.
    pose proof (nsrc_S norm s ltac:(lia)) as NS1. pose proof (nsrc_mono norm (s + 1) (maxSV + 1) ltac:(lia)) as NS2.
    pose proof (hSRC_total norm maxSV tl TLR MSVR NLEN NGE NSUM) as NS3. pose proof (nsrc_nonneg norm s) as NS4.
    pose proof (hnolow norm maxSV tl TLR MSVR NLEN NGE NSUM s NOLOW HS) as NN.
    assert (NR : -1 <= Znth s norm <= 2^tl) by (apply (hnorm_range norm maxSV tl TLR MSVR NLEN NGE NSUM); exact HS).
    rewrite NOLOW in NS3.
    set (p := nsrc norm s) in *.
    kx_autoFLAc (FR, HDR) [KAUnp (NC + 2 * s) 2; KAUnp (SP0 + p) 8; KAApp (SP0 + p) 8] [0xab998; 0xaba40] 60%nat
      (KZB ++ [KZRange s 0 255; KZRange (maxSV - s) 0 255; KZRange (NC + 2 * s) 4096 (2^47); KZRange p 0 512; KZRange (2^tl - p) 0 512;
               KZRange (SP0 + p) 4096 (2^47 - 8); KZRange (wlen - 2 * maxSV - 10 - p) 0 (2^32); KZRange (KK * s) 0 (2^64 - 1);
               KZWr (SP0 + p) 8; KZDisj (SP0 + p) 8 NC (2 * zlen norm); KZDisj (SP0 + p) 8 (SPV - 144) 144;
               KZDisj (SP0 + p) 8 (DT + 4) (4 * 2^tl); KZDisj (SP0 + p) 8 DT 4; KZDisj (SP0 + p) 8 W (2 * (maxSV + 1))])
      [(NC + 2 * s, 2)] [(NC + 2 * s, 2); (SP0 + p, 8)].
    all: try kx_z. all: try kx_acc RNC. all: try kx_acc RW. all: try kx_acc RSTK. all: try kx_sh_rd_any. all: try (kx_sh_acc RSW).
    all: kx_read_reg 21 RD.
    all: rewrite (rdval_s16Z bsegs m1 NC norm s _ NCB) in RD by lia.
    all: kxk_keepg SPRD. all: kx_mem. all: rewrite RD in *. all: kx_tidy_run. all: bd_reunp.
    all: rewrite ?(unsigned_lit (Znth s norm)) in * by lia. all: rewrite ?(signed_lit (Znth s norm)) in * by lia.
    all: sv_vals s.
    all: erewrite (zupd8_wr8m sp p s) in * by lia.
    all: rewrite (wr8m_eq sp p s) in * by (unfold FseNCount.Zlength; lia).
    all: destruct (lay_write8 norm maxSV tl TLR MSVR NLEN NGE NSUM s 0 sp HS ltac:(lia) ltac:(unfold FseNCount.Zlength; fold p; lia) LI ltac:(intros; lia)) as (LI' & HSP');
         fold p in LI', HSP'; rewrite Z.add_0_r in LI', HSP'.
    all: assert (SPBY' : Forall isbyte (write8 sp p s)) by (apply write8_bytes; [lia| exact SPBY]).
    all: bd_lens.
    all: kx_gen_regsF [9%nat; 10%nat; 12%nat].
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xab998) _ _ _ _) =>     (* [comment removed for export] *)
             eapply KN; [close_bd |];
             apply (lay_next norm maxSV tl TLR MSVR NLEN NGE NSUM s 8); [exact HS | lia | lia | exact LI' | exact HSP']
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xaba40) _ _ _ _) =>     (* [comment removed for export] *)
             kx_setreg 15 (SP0 + nsrc norm s + 8); kx_setreg 30 8; kx_setreg 31 (SP0 + nsrc norm s + 8);
             (* [comment removed for export] *)
             eapply (bd_lay_innerA (Z.to_nat (Znth s norm / 8)) _ tb sn (write8 sp p s) fast s 8);
             [close_bd | exact LI' | exact HS | lia | lia | clear - NR; Z.div_mod_to_equations; lia | exact HSP'
             | intros; eapply KN; eassumption]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_lay_loopA : forall (f : nat) m1 tb sn sp fast s xra xt0 xt2 xs1 xa0 xa2 xa3 xa5 xa6 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6,
    BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp m1 -> lay_inv norm maxSV s sp -> 0 <= s -> s + Z.of_nat (S f) = maxSV + 1 ->
    (forall m2 sp' yra ys1 ya0 ya2 ya5 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt5 yt6, BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp' m2 -> lay_inv norm maxSV (maxSV + 1) sp' ->
       evtF bsegs RNG POST (STL 0xabb94 m2 (maxSV + 1) (2^tl) yra xt0 xt2 ys1 ya0 ya2 xa3 ya5 xa6 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt5 yt6)) ->
    evtF bsegs RNG POST (STL 0xab9b0 m1 s (nsrc norm s) xra xt0 xt2 xs1 xa0 xa2 xa3 xa5 xa6 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6).
  Proof.
    induction f as [|f IH]; intros until xt6; intros I LI HS HSF KE.
    all: eapply bd_lay_bodyA; [exact I | exact LI | lia |]; intros m2 sp' ys1 ya0 ya2 ya5 yt5 yt6 I2 LI2.
    all: pose proof I2 as I3; bd_open I2.
    all: pose proof (hSRC_total norm maxSV tl TLR MSVR NLEN NGE NSUM) as NS3; rewrite NOLOW in NS3.
    all: pose proof (nsrc_S norm s ltac:(lia)) as NS1; pose proof (hnolow norm maxSV tl TLR MSVR NLEN NGE NSUM s NOLOW ltac:(lia)) as NN.
    all: pose proof (nsrc_mono norm (s + 1) (maxSV + 1) ltac:(lia)) as NS2; pose proof (nsrc_nonneg norm s) as NS4.
    all: assert (NR : -1 <= Znth s norm <= 2^tl) by (apply (hnorm_range norm maxSV tl TLR MSVR NLEN NGE NSUM); lia).
    all: kx_autoFLAc tt (@nil kza) [0xab9b0; 0xabb94] 10%nat
           (KZB ++ [KZRange s 0 255; KZRange (maxSV - s) 0 255; KZRange (nsrc norm s) 0 512; KZRange (Znth s norm) 0 512; KZRange (KK * s) 0 (2^64 - 1)])
           (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z. all: kx_mem. all: kx_tidy_run.
    all: try (exfalso; lia).
    - replace (s + 1) with (maxSV + 1) in NS1, LI2 by lia.
      kx_setreg 29 (maxSV + 1). kx_setreg 17 (2^tl). kx_setreg 8 ((maxSV + 1) * KK).
      eapply KE; [exact I3 | exact LI2].
    - kx_setreg 29 (s + 1). kx_setreg 17 (nsrc norm (s + 1)). kx_setreg 8 ((s + 1) * KK).
      eapply (IH m2 tb sn sp' fast (s + 1)); [exact I3 | exact LI2 | lia | lia | exact KE].
  Qed.

End P2A.
End CANSEC1.
