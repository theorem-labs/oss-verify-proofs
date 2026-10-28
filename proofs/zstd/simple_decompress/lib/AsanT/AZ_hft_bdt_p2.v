(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqBuild ZdSeqBuildThm ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdHufW ZdHufWM ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_bdt_defs AZ_hft_bdt_p3.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC1. Context {rc : runConstT}.
Section P2B.
  Variables (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem)
            (SPV lo DT NC W wlen maxSV tl : Z) (norm : list Z).
  Hypothesis HY : bdA_hyps RNG SPV lo DT NC W wlen maxSV tl norm.
  Hypothesis UDT : unpoisoned m DT (DT + 4 + 4 * 2^tl).
  Hypothesis UW : unpoisoned m W (W + wlen).
  Hypothesis UNC : unpoisoned m NC (NC + 2 * zlen norm).
  Hypothesis ART0 : art m.
  Variables (f8 f16 : word).   (* [comment removed for export] *)
  Notation BDm := (BDA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC W wlen maxSV tl norm f8 f16).
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
           | H : rw_cells _ _ _ (CB 8 _ :: C8 ?a :: C8 ?b :: _) |- _ => clear H; try clear a; try clear b   (* [comment removed for export] *)
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
  Notation PITER k := (pos_iter (Z.to_nat k) (2^tl) STEP HIGH 0).

  (* [comment removed for export] *)
  Notation STC pc mm xpos xs xn xi xt0 xt1 xa2 xa4 xs5 xt6 :=
    (ST pc mm ra (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (2^tl + -1)) (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 maxSV)
        xt0 (Z_to_bv 64 NC) xa2 xt1 xa4 xs xpos xn
        (Z_to_bv 64 (2^tl)) (Z_to_bv 64 W) (Z_to_bv 64 DT) xs5 xt6
        s7 s8 s9 s10 s11 (Z_to_bv 64 STEP) (Z_to_bv 64 HIGH) (Z_to_bv 64 (maxSV + 1)) xi).

  Lemma bd_step_rngA : 0 <= STEP < 1048576.
  Proof. destruct (bdA_size_rng _ _ _ _ _ _ _ _ _ _ HY) as (SZ & _). unfold fse_tablestep. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma bd_skipA : forall (fu : nat) m1 p xs xn xi xt0 xt1 xa2 xa4 xs5 xt6,
    0 <= HIGH -> 0 <= p < 2^tl ->
    skip_low fu (2^tl) STEP HIGH ((p + STEP) mod 2^tl) <= HIGH ->
    (forall y, evtF bsegs RNG POST (STC 0xabb5c m1 (Z_to_bv 64 (skip_low fu (2^tl) STEP HIGH ((p + STEP) mod 2^tl))) xs xn xi y xt1 xa2 xa4 xs5 xt6)) ->
    evtF bsegs RNG POST (STC 0xabb50 m1 (Z_to_bv 64 p) xs xn xi xt0 xt1 xa2 xa4 xs5 xt6).
  Proof.
    intros fu. induction fu as [|fu IH]; intros until xt6; intros HH HP SK KONT.
    all: destruct (bdA_size_rng _ _ _ _ _ _ _ _ _ _ HY) as (SZ & _); pose proof bd_step_rngA as HST; open_hy HY.
    all: pose proof (hhigh_range norm maxSV tl TLR ltac:(lia) NLEN NGE NSUM) as HR.
    all: assert (QR : 0 <= (p + STEP) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
    all: zstep; rewrite (FseWalkKit.swrap32_small (STEP + p)) by lia; zstep;
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
  Lemma bd_place_nA : forall (kk : nat) m1 h0 h1 tb sn sp s i xt0 xt1 xa2 xa4 xs5 xt6,
    BDm h0 h1 tb sn sp m1 -> p2_inv norm maxSV tl (nsrc norm s + i) tb ->
    0 <= s <= maxSV -> 0 <= i -> i + Z.of_nat (S kk) = Znth s norm ->
    (forall m2 tb' yt0 ya2 ya4, BDm h0 h1 tb' sn sp m2 -> p2_inv norm maxSV tl (nsrc norm (s + 1)) tb' ->
       evtF bsegs RNG POST
         (STC 0xabb64 m2 (Z_to_bv 64 (PITER (nsrc norm (s + 1)))) (Z_to_bv 64 s) (Z_to_bv 64 (Znth s norm)) (Z_to_bv 64 (Znth s norm))
              yt0 xt1 ya2 ya4 xs5 xt6)) ->
    evtF bsegs RNG POST
      (STC 0xabb2c m1 (Z_to_bv 64 (PITER (nsrc norm s + i))) (Z_to_bv 64 s) (Z_to_bv 64 (Znth s norm)) (Z_to_bv 64 i)
           xt0 xt1 xa2 xa4 xs5 xt6).
  Proof.
    intros kk. induction kk as [|kk IH]; intros until xt6; intros I P2 HS HI HIN KONT; bd_open I.
    all: pose proof bd_step_rngA as HST.
    all: pose proof (hhigh_range norm maxSV tl TLR ltac:(lia) NLEN NGE NSUM) as HR.
    all: pose proof (nsrc_S norm s ltac:(lia)) as NS1; pose proof (nsrc_mono norm (s + 1) (maxSV + 1) ltac:(lia)) as NS2;
         pose proof (hSRC_total norm maxSV tl TLR MSVR NLEN NGE NSUM) as NS3; pose proof (nsrc_nonneg norm s) as NS4.
    all: assert (KR : 0 <= nsrc norm s + i <= HIGH) by lia.
    all: destruct (p2_step norm maxSV tl TLR MSVR NLEN NGE NSUM (nsrc norm s + i) tb P2 KR) as (PR & P2').
    all: rewrite (Znth_hpos tl HIGH (nsrc norm s + i) KR) in PR, P2'.
    all: rewrite (hSRC_at norm maxSV tl TLR MSVR NLEN NGE NSUM s i HS ltac:(lia)) in P2'.
    all: set (position := PITER (nsrc norm s + i)) in *.
    all: assert (NR : -1 <= Znth s norm <= 2^tl) by (apply (hnorm_range norm maxSV tl TLR MSVR NLEN NGE NSUM); exact HS).
    (* [comment removed for export] *)
    all: kx_autoFLAc (FR, HDR) [KAUnp (DT + 4 + 4 * position + 2) 1; KAApp (DT + 4 + 4 * position + 2) 1] [0xabb50] 20%nat
           (KZB ++ [KZRange position 0 511; KZRange (2^tl - position) 1 512; KZRange s 0 255; KZRange i 0 512; KZRange (Znth s norm) 1 512;
                    KZRange (DT + 4 + 4 * position + 2) 4096 (2^47 - 8); KZRange (4 * 2^tl - 4 * position) 4 2048;
                    KZWr (DT + 4 + 4 * position + 2) 1; KZDisj (DT + 4 + 4 * position + 2) 1 NC (2 * zlen norm);
                    KZDisj (DT + 4 + 4 * position + 2) 1 (SPV - 144) 144; KZDisj (DT + 4 + 4 * position + 2) 1 W wlen;
                    KZDisj (DT + 4 + 4 * position + 2) 1 DT 4; KZDisj (DT + 4 + 4 * position + 2) 1 W (2 * (maxSV + 1));
                    KZDisj (DT + 4 + 4 * position + 2) 1 (W + 2 * (maxSV + 1)) (wlen - 2 * (maxSV + 1))])
           (@nil (Z * Z)) [(DT + 4 + 4 * position + 2, 1)].
    all: try kx_z. all: try kx_acc RDT.
    all: kxk_keep CEL. all: kx_mem. all: kx_tidy_run. all: bd_reunp.
    all: kxk_ix CEL (4 * position + 2). all: kxk_vl CEL s.
    all: kx_gen_regsF [10%nat; 14%nat].
    all: bd_lens.
    all: assert (CBY' : Forall isbyte (Zupd (4 * position + 2) s tb)) by (apply Forall_Zupd; [exact CBY| lia]).
    (* [comment removed for export] *)
    all: assert (QR : 0 <= (position + STEP) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
    all: pose proof (hskip_low_term tl HIGH ((position + STEP) mod 2^tl) TLR ltac:(lia) QR) as SKT.
    all: eapply (bd_skipA (Z.to_nat (2^tl)) _ position); [lia | lia | exact SKT |]; intros ?.
    all: fold (next_pos (2^tl) STEP HIGH position).
    all: assert (NPE : next_pos (2^tl) STEP HIGH position = PITER (nsrc norm s + i + 1))
           by (unfold position; replace (Z.to_nat (nsrc norm s + i + 1)) with (S (Z.to_nat (nsrc norm s + i))) by lia; rewrite pos_iter_S; reflexivity).
    all: rewrite NPE.
    all: zstep; rewrite (FseWalkKit.swrap32_small (i + 1)) by lia; zstep; if_cases K; zify_cond K.
    - exfalso; lia.
    - replace (i + 1) with (Znth s norm) by lia.
      replace (nsrc norm s + i + 1) with (nsrc norm (s + 1)) in * by lia.
      eapply KONT; [close_bd | exact P2'].
    - replace (nsrc norm s + i + 1) with (nsrc norm s + (i + 1)) in * by lia.
      eapply (IH _ h0 h1 (Zupd (4 * position + 2) s tb) sn sp s (i + 1)); [close_bd | exact P2' | exact HS | lia | lia | exact KONT].
    - exfalso; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_slow_nextA : forall m1 s xpos xn xi xt0 xt1 xa2 xa4 xs5 xt6,
    0 <= s <= maxSV ->
    (s + 1 < maxSV + 1 -> evtF bsegs RNG POST (STC 0xabb08 m1 xpos (Z_to_bv 64 (s + 1)) xn xi xt0 xt1 xa2 xa4 xs5 xt6)) ->
    (s + 1 = maxSV + 1 -> evtF bsegs RNG POST (STC 0xabb88 m1 xpos (Z_to_bv 64 (maxSV + 1)) xn xi xt0 xt1 xa2 xa4 xs5 xt6)) ->
    evtF bsegs RNG POST (STC 0xabb00 m1 xpos (Z_to_bv 64 s) xn xi xt0 xt1 xa2 xa4 xs5 xt6).
  Proof.
    intros until xt6; intros HS KH KE. open_hy HY.
    zstep. rewrite ?(FseWalkKit.swrap32_small (s + 1)) by lia. zstep. if_cases K; zify_cond K.
    - replace (s + 1) with (maxSV + 1) by lia.
      apply KE. lia.
    - apply KH. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_slow_bodyA : forall m1 h0 h1 tb sn sp s xn xi xt0 xt1 xa2 xa4 xs5 xt6,
    BDm h0 h1 tb sn sp m1 -> p2_inv norm maxSV tl (nsrc norm s) tb -> 0 <= s <= maxSV ->
    (forall m2 tb' yn yi yt0 ya2 ya4, BDm h0 h1 tb' sn sp m2 -> p2_inv norm maxSV tl (nsrc norm (s + 1)) tb' ->
       evtF bsegs RNG POST (STC 0xabb00 m2 (Z_to_bv 64 (PITER (nsrc norm (s + 1)))) (Z_to_bv 64 s) yn yi yt0 xt1 ya2 ya4 xs5 xt6)) ->
    evtF bsegs RNG POST (STC 0xabb08 m1 (Z_to_bv 64 (PITER (nsrc norm s))) (Z_to_bv 64 s) xn xi xt0 xt1 xa2 xa4 xs5 xt6).
  Proof.
    intros until xt6; intros I P2 HS KN. pose proof I as I0. bd_open I.
    assert (NR : -1 <= Znth s norm <= 2^tl) by (apply (hnorm_range norm maxSV tl TLR MSVR NLEN NGE NSUM); exact HS).
    pose proof (nsrc_S norm s ltac:(lia)) as NS1.
    pose proof (hhigh_range norm maxSV tl TLR ltac:(lia) NLEN NGE NSUM) as HR.
    kx_autoFLAc (FR, HDR) [KAUnp (NC + 2 * s) 2] [0xabb00; 0xabb2c] 20%nat
      (KZB ++ [KZRange s 0 255; KZRange (maxSV - s) 0 255; KZRange (NC + 2 * s) 4096 (2^47)])
      [(NC + 2 * s, 2)] [(NC + 2 * s, 2)].
    all: try kx_z. all: try kx_acc RNC. all: try kx_acc RSTK.
    all: kx_read_reg 17 RD.
    all: rewrite (rdval_s16Z bsegs m1 NC norm s _ NCB) in RD by lia.
    all: rewrite RD in *; rewrite Z_to_bv_unsigned in *; unfold bv_wrap, bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *.
    all: kx_tidy_run.
    - (* [comment removed for export] *)
      assert (NLE : Znth s norm <= 0).
      { destruct (Z_le_gt_dec (Znth s norm) 0) as [|G]; [assumption|]. exfalso. rewrite (Z.mod_small (Znth s norm) (2^64)) in KXBR by lia.
        destruct (Z.ltb_spec 0 (Znth s norm)), (Z.ltb_spec (Znth s norm) 9223372036854775808); cbn in KXBR; try discriminate; lia. }
      replace (nsrc norm s) with (nsrc norm (s + 1)) in * by lia.
      eapply KN; [exact I0 | exact P2].
    - (* [comment removed for export] *)
      assert (NPOS : 0 < Znth s norm).
      { destruct (Z_le_gt_dec (Znth s norm) 0) as [L|G]; [|lia]. exfalso.
        assert (E : Znth s norm = 0 \/ Znth s norm = -1) by lia.
        destruct E as [E|E]; rewrite E in KXBR0, KXBR1; [cbn in KXBR0; lia | change ((-1) mod 2^64) with 18446744073709551615 in KXBR1; lia]. }
      replace (nsrc norm s) with (nsrc norm s + 0) by lia.
      eapply (bd_place_nA (Z.to_nat (Znth s norm - 1)) m1 h0 h1 tb sn sp s 0); [exact I0 | rewrite Z.add_0_r; exact P2 | exact HS | lia | lia |].
      intros m2 tb' yt0 ya2 ya4 I2 P2'.
      kx_autoFLAc tt (@nil kza) [0xabb00] 4%nat (KZB ++ []) (@nil (Z * Z)) (@nil (Z * Z)).
      all: kx_mem.
      eapply KN; [exact I2 | exact P2'].
  Qed.

  (* [comment removed for export] *)
  Lemma bd_slow_loopA : forall (f : nat) m1 h0 h1 tb sn sp s xn xi xt0 xt1 xa2 xa4 xs5 xt6,
    BDm h0 h1 tb sn sp m1 -> p2_inv norm maxSV tl (nsrc norm s) tb -> 0 <= s -> s + Z.of_nat (S f) = maxSV + 1 ->
    (forall m2 tb' yn yi yt0 ya2 ya4, BDm h0 h1 tb' sn sp m2 -> p2_inv norm maxSV tl (HIGH + 1) tb' ->
       evtF bsegs RNG POST (STC 0xabb88 m2 (Z_to_bv 64 (PITER (HIGH + 1))) (Z_to_bv 64 (maxSV + 1)) yn yi yt0 xt1 ya2 ya4 xs5 xt6)) ->
    evtF bsegs RNG POST (STC 0xabb08 m1 (Z_to_bv 64 (PITER (nsrc norm s))) (Z_to_bv 64 s) xn xi xt0 xt1 xa2 xa4 xs5 xt6).
  Proof.
    induction f as [|f IH]; intros until xt6; intros I P2 HS HSF KE; open_hy HY.
    all: pose proof (hSRC_total norm maxSV tl TLR MSVR NLEN NGE NSUM) as NS3.
    - eapply bd_slow_bodyA; [exact I | exact P2 | lia |].
      intros m2 tb' yn yi yt0 ya2 ya4 I2 P2'.
      eapply bd_slow_nextA; [lia | intros; exfalso; lia |]. intros _.
      replace (s + 1) with (maxSV + 1) in * by lia. rewrite NS3 in *.
      eapply KE; [exact I2 | exact P2'].
    - eapply bd_slow_bodyA; [exact I | exact P2 | lia |].
      intros m2 tb' yn yi yt0 ya2 ya4 I2 P2'.
      eapply bd_slow_nextA; [lia | | intros; exfalso; lia]. intros _.
      eapply (IH m2 h0 h1 tb' sn sp (s + 1)); [exact I2 | exact P2' | lia | lia | exact KE].
  Qed.

  (* [comment removed for export] *)
  Lemma bd_slowA : forall m1 tb sn sp fast xa4 xa5 xa7,
    BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp m1 -> p2_inv norm maxSV tl 0 tb ->
    (forall m2 tb' sp' yra y7 ys0 ys1 ya0 ya1 ya2 ya4 ya5 ya6 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31,
       BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb' sn sp' m2 -> symtab_ok norm maxSV tl tb' -> zlen tb' = 4 * 2^tl ->
       evtF bsegs RNG POST (ST 0xabc84 m2 yra (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2147450880) y7 ys0 ys1 ya0 ya1 ya2 (Z_to_bv 64 tl) ya4 ya5 ya6 (Z_to_bv 64 (DT + 7))
                              (Z_to_bv 64 (2^tl)) (Z_to_bv 64 W) ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (ST 0xabae0 m1 ra (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (2^tl + -1)) (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 maxSV)
                           (Z_to_bv 64 851192) (Z_to_bv 64 NC) (Z_to_bv 64 (2^tl / 2)) (Z_to_bv 64 tl) xa4 xa5 (Z_to_bv 64 (W + 2 * (maxSV + 1))) xa7
                           (Z_to_bv 64 (2^tl)) (Z_to_bv 64 W) (Z_to_bv 64 DT) (Z_to_bv 64 (NC + 2 * (maxSV + 1))) (Z_to_bv 64 (W + 2 * (maxSV + 1)))
                           s7 s8 s9 s10 s11 (Z_to_bv 64 (2 * maxSV + W + 2)) (Z_to_bv 64 HIGH) (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 fast)).
  Proof.
    intros until xa7; intros I P2 KP3. pose proof I as I0. bd_open I.
    pose proof (hhigh_range norm maxSV tl TLR ltac:(lia) NLEN NGE NSUM) as HR.
    kx_autoFLAc tt (@nil kza) [0xabb08] 12%nat (KZB ++ [KZRange (2^tl / 2) 16 256; KZRange (2^tl / 8) 4 64]) (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z. all: kx_mem. all: kx_tidy_run.
    rewrite ?(Z.mod_small (2^tl) (2^64)) by lia.
    replace (2 ^ tl / 2 + 2 ^ tl / 8 + 3) with STEP by (unfold fse_tablestep; lia).
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (PITER (nsrc norm 0))) at 3 by reflexivity.
    eapply (bd_slow_loopA (Z.to_nat maxSV) m1 _ _ tb sn sp 0); [exact I0 | exact P2 | lia | lia |].
    intros m2 tb' yn yi yt0 ya2 ya4 I2 P2'. bd_reopen I2.
    kx_autoFLAc tt (@nil kza) [0xabc84; 0xabdcc] 12%nat (KZB ++ []) (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z. all: kx_mem. all: kx_tidy_run.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xabc84) _ _ _ _) =>   (* [comment removed for export] *)
             eapply (KP3 _ _ sp); [close_bd | apply (p2_done norm maxSV tl TLR MSVR NLEN NGE NSUM); exact P2' | assumption]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xabdcc) _ _ _ _) =>   (* [comment removed for export] *)
            eapply (bd_epiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UDT UW UNC f8 f16); [close_bd | lia | right; reflexivity]
         end.
  Qed.
End P2B.
End CANSEC1.
