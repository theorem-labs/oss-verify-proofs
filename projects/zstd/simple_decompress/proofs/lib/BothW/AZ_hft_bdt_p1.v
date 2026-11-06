(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqBuild ZdSeqBuildThm ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdHufW ZdHufWM ZdHufWX SepHide.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_bdt_defs.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC1. Context {rc : runConstT}.
Section P1.
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
    (MS (mkR xra (Z_to_bv 64 (SPV + -192)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Notation ST1 pc mm high s xt0 xt1 xa0 xa3 xa4 xa5 xt5 xt6 fast :=
    (ST pc mm ra xt0 xt1 (Z_to_bv 64 2147450880) s0 (Z_to_bv 64 (maxSV + 1))
        xa0 (Z_to_bv 64 (-1 * NC + -1)) (Z_to_bv 64 maxSV) xa3 xa4 xa5 (Z_to_bv 64 high) (Z_to_bv 64 (DT + 4))
        (Z_to_bv 64 s) (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 1) (Z_to_bv 64 fast) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (2^(tl + -1))) (Z_to_bv 64 65535)
        s10 s11 (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (2^tl + -1)) xt5 xt6).
  (* [comment removed for export] *)
  Notation ST1X pc mm high s xt0 xt1 xa0 xa3 xa4 xa5 xt5 xt6 fast := (ST1 pc mm high s xt0 xt1 xa0 xa3 xa4 xa5 xt5 xt6 fast) (only parsing).

  (* [comment removed for export] *)
  Lemma bd_p1_bodyA : forall m1 h0 h1 s tb sn sp high fast xt0 xt1 xa0 xa3 xa4 xa5 xt5 xt6,
    BDm h0 h1 tb sn sp m1 -> p1_inv norm maxSV tl s tb sn high fast -> 0 <= s <= maxSV ->
    (forall m2 tb' sn' high' fast' yt0 yt1 ya0 ya3 ya4 ya5 yt5 yt6, BDm h0 h1 tb' sn' sp m2 -> p1_inv norm maxSV tl (s + 1) tb' sn' high' fast' -> s + 1 < maxSV + 1 ->
       evtF bsegs RNG POST (ST1 0xaf280 m2 high' (s + 1) yt0 yt1 ya0 ya3 ya4 ya5 yt5 yt6 fast')) ->
    (forall m2 tb' sn' high' fast' yt0 yt1 ya0 ya3 ya4 ya5 yt5 yt6, BDm h0 h1 tb' sn' sp m2 -> p1_inv norm maxSV tl (maxSV + 1) tb' sn' high' fast' ->
       evtF bsegs RNG POST (ST1X 0xaf378 m2 high' (maxSV + 1) yt0 yt1 ya0 ya3 ya4 ya5 yt5 yt6 fast')) ->
    evtF bsegs RNG POST (ST1 0xaf280 m1 high s xt0 xt1 xa0 xa3 xa4 xa5 xt5 xt6 fast).
  Proof.
    intros until xt6; intros I P1 HS KH KE. bd_open I.
    assert (NR : -1 <= Znth s norm <= 2^tl) by (apply (hnorm_range norm maxSV tl TLR MSVR NLEN NGE NSUM); exact HS).
    assert (HFA : 0 <= fast <= 1) by (destruct P1 as (_ & _ & _ & _ & _ & FR1 & _); exact FR1).
    (* [comment removed for export] *)
    kx_autoFLAc (FR, HDR) [KAUnp (NC + 2 * s) 2] [0xaf2ac; 0xaf2e0] 20%nat
      (KZB ++ [KZRange s 0 255; KZRange (NC + 2 * s) 4096 (2^47)])
      [(NC + 2 * s, 2)] [(NC + 2 * s, 2)].
    all: try kx_z. all: try kx_acc RNC. all: try kx_acc RSTK.
    all: kx_the_read RD.
    all: rewrite (rdval_u16Z bsegs m1 NC norm s _ NCB) in RD by lia.
    - (* [comment removed for export] *)
      assert (NM1 : Znth s norm = -1).
      { rewrite RD, Z_to_bv_unsigned in KXBR. unfold bv_wrap, bv_modulus in KXBR. change (2 ^ Z.of_N 64) with (2^64) in KXBR.
        clear - KXBR NR SZ. Z.div_mod_to_equations. lia. }
      destruct (p1_low norm maxSV tl TLR MSVR NLEN NGE NSUM s tb sn high fast P1 HS NM1) as (HHI & P1').
      rewrite RD. kx_abs. clear KXE KXA KXRD KXK KXBR RD.
      kx_autoFLAc (FR, HDR) [KAUnp (DT + 4 + 4 * high + 2) 1; KAUnp (W + 2 * s) 2; KAApp (DT + 4 + 4 * high + 2) 1; KAApp (W + 2 * s) 2]
        [0xaf280; 0xaf378] 40%nat
        (KZB ++ [KZRange s 0 255; KZRange high 0 511; KZRange (2^tl - high) 1 512; KZRange (maxSV - s) 0 255;
         KZRange (W + 2 * s) 4096 (2^47 - 8); KZRange (DT + 4 + 4 * high + 2) 4096 (2^47 - 8);
         KZRange (wlen - 2 * s - 2) 40 (2^32); KZRange (4 * 2^tl - 4 * high) 4 2048;
         KZWr (DT + 4 + 4 * high + 2) 1; KZWr (W + 2 * s) 2;
         KZDisj (DT + 4 + 4 * high + 2) 1 NC (2 * zlen norm); KZDisj (W + 2 * s) 2 NC (2 * zlen norm);
         KZDisj (DT + 4 + 4 * high + 2) 1 (SPV - 192) 192; KZDisj (W + 2 * s) 2 (SPV - 192) 192;
         KZDisj (DT + 4 + 4 * high + 2) 1 W wlen; KZDisj (W + 2 * s) 2 (DT + 4) (4 * 2^tl); KZDisj (W + 2 * s) 2 DT 4;
         KZDisj (DT + 4 + 4 * high + 2) 1 DT 4; KZDisj (W + 2 * s) 2 (W + 2 * (maxSV + 1)) (wlen - 2 * (maxSV + 1));
         KZDisj (DT + 4 + 4 * high + 2) 1 W (2 * (maxSV + 1)); KZDisj (DT + 4 + 4 * high + 2) 1 (W + 2 * (maxSV + 1)) (wlen - 2 * (maxSV + 1))])
        (@nil (Z * Z)) [(DT + 4 + 4 * high + 2, 1); (W + 2 * s, 2)].
      all: try kx_z. all: try kx_acc RDT. all: try kx_acc RW. all: try kx_acc RSTK.
      all: kxk_keep CEL. all: kxk_keep_ix SNX [s]. all: kx_mem.
      all: kx_tidy_run.
      all: kxk_ix CEL (4 * high + 2); rewrite (Z.mod_small s 256) in CEL by lia; change (1 mod 65536) with 1 in SNX.
      all: assert (CLEN' : zlen (Zupd (4 * high + 2) s tb) = 4 * 2^tl) by (rewrite Zupd_length2; exact CLEN);
           assert (CBY' : Forall isbyte (Zupd (4 * high + 2) s tb)) by (apply Forall_Zupd; [exact CBY| lia]);
           assert (SNLEN' : zlen (Zupd s 1 sn) = maxSV + 1) by (rewrite Zupd_length2; exact SNLEN).
      + (* [comment removed for export] *)
        replace (2 * s + NC + 2) with (NC + 2 * (s + 1)) by lia. replace (2 * s + W + 2) with (W + 2 * (s + 1)) by lia.
        replace (high + -1) with (high - 1) by lia.
        eapply KH; [close_bd | exact P1' | lia].
      + (* [comment removed for export] *)
        replace (s + 1) with (maxSV + 1) in P1' |- * by lia. replace (high + -1) with (high - 1) by lia.
        eapply KE; [close_bd | exact P1'].
    - (* [comment removed for export] *)
      assert (NN : 0 <= Znth s norm).
      { rewrite RD, Z_to_bv_unsigned in KXBR. unfold bv_wrap, bv_modulus in KXBR. change (2 ^ Z.of_N 64) with (2^64) in KXBR.
        clear - KXBR NR SZ. Z.div_mod_to_equations. lia. }
      destruct (p1_norm norm maxSV tl TLR MSVR NLEN NGE NSUM s tb sn high fast P1 HS ltac:(lia)) as (_ & P1').
      rewrite RD. rewrite (Z.mod_small (Znth s norm) 65536) in * by lia. kx_abs. clear KXE KXA KXRD KXK KXBR RD.
      (* [comment removed for export] *)
      kx_autoFLAc (FR, HDR) [KAUnp (W + 2 * s) 2] [0xaf260] 20%nat
        (KZB ++ [KZRange s 0 255; KZRange (maxSV - s) 0 255; KZRange (W + 2 * s) 4096 (2^47 - 8); KZRange (Znth s norm) 0 512;
         KZRange (wlen - 2 * s - 2) 40 (2^32)])
        (@nil (Z * Z)) (@nil (Z * Z)).
      all: try kx_z. all: try kx_acc RW. all: try kx_acc RSTK. all: try kx_sh_rd_any. all: try (kx_sh_acc RSW).
      all: try (kx_sh_dead UW1 2).
      all: kx_mem. all: kx_tidy_run.
      (* [comment removed for export] *)
      zstep. zstep. rewrite (sext16_shl48 (Znth s norm)) by lia.
      zstep. (* [comment removed for export] *)
      replace (2 ^ (tl + -1) mod 18446744073709551616) with (2 ^ (tl - 1)) by (replace (tl + -1) with (tl - 1) by lia; rewrite Z.mod_small; lia).
      rewrite (slt_small (Znth s norm) (2^(tl - 1))) by lia.
      zstep. zstep. rewrite (neg_mask _ fast) by lia.
      replace (if Znth s norm <? 2 ^ (tl - 1) then fast else 0) with (if 2 ^ (tl - 1) <=? Znth s norm then 0 else fast)
        by (destruct (Z.ltb_spec (Znth s norm) (2 ^ (tl - 1))); destruct (Z.leb_spec (2 ^ (tl - 1)) (Znth s norm)); lia).
      set (fast' := if 2 ^ (tl - 1) <=? Znth s norm then 0 else fast) in *.
      assert (HFA' : 0 <= fast' <= 1) by (subst fast'; destruct (2 ^ (tl - 1) <=? Znth s norm); lia).
      clearbody fast'.
      (* [comment removed for export] *)
      kx_autoFLAc (FR, HDR) [KAUnp (W + 2 * s) 2; KAApp (W + 2 * s) 2] [0xaf280; 0xaf378] 40%nat
        (KZB ++ [KZRange s 0 255; KZRange (maxSV - s) 0 255; KZRange (W + 2 * s) 4096 (2^47 - 8); KZRange (Znth s norm) 0 512;
         KZRange (wlen - 2 * s - 2) 40 (2^32); KZRange fast' 0 1;
         KZWr (W + 2 * s) 2; KZDisj (W + 2 * s) 2 NC (2 * zlen norm); KZDisj (W + 2 * s) 2 (SPV - 192) 192;
         KZDisj (W + 2 * s) 2 (DT + 4) (4 * 2^tl); KZDisj (W + 2 * s) 2 DT 4; KZDisj (W + 2 * s) 2 (W + 2 * (maxSV + 1)) (wlen - 2 * (maxSV + 1))])
        (@nil (Z * Z)) [(W + 2 * s, 2)].
      all: try kx_z. all: try kx_acc RW. all: try kx_acc RSTK. all: try kx_sh_rd_any. all: try (kx_sh_acc RSW).
      all: try (kx_sh_dead UW1 2).
      all: kxk_keep CEL. all: kxk_keep_ix SNX [s]. all: kx_mem.
      all: kx_tidy_run.
      all: rewrite (Z.mod_small (Znth s norm) 65536) in SNX by lia.
      all: assert (SNLEN' : zlen (Zupd s (Znth s norm) sn) = maxSV + 1) by (rewrite Zupd_length2; exact SNLEN).
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xaf280) _ _ _ _) =>   (* [comment removed for export] *)
               replace (2 * s + NC + 2) with (NC + 2 * (s + 1)) by lia; replace (2 * s + W + 2) with (W + 2 * (s + 1)) by lia;
               eapply KH; [close_bd | exact P1' | lia]
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xaf378) _ _ _ _) =>   (* [comment removed for export] *)
               replace (s + 1) with (maxSV + 1) in P1' |- * by lia;
               eapply KE; [close_bd | exact P1']
           end.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_p1_loopA : forall (f : nat) m1 h0 h1 s tb sn sp high fast xt0 xt1 xa0 xa3 xa4 xa5 xt5 xt6,
    BDm h0 h1 tb sn sp m1 -> p1_inv norm maxSV tl s tb sn high fast -> 0 <= s -> s + Z.of_nat (S f) = maxSV + 1 ->
    (forall m2 tb' sn' high' fast' yt0 yt1 ya0 ya3 ya4 ya5 yt5 yt6, BDm h0 h1 tb' sn' sp m2 -> p1_inv norm maxSV tl (maxSV + 1) tb' sn' high' fast' ->
       evtF bsegs RNG POST (ST1X 0xaf378 m2 high' (maxSV + 1) yt0 yt1 ya0 ya3 ya4 ya5 yt5 yt6 fast')) ->
    evtF bsegs RNG POST (ST1 0xaf280 m1 high s xt0 xt1 xa0 xa3 xa4 xa5 xt5 xt6 fast).
  Proof.
    induction f as [|f IH]; intros until xt6; intros I P1 HS HSF KONT.
    - eapply bd_p1_bodyA; [exact I | exact P1 | lia | intros; exfalso; lia | exact KONT].
    - eapply bd_p1_bodyA; [exact I | exact P1 | lia | | exact KONT].
      intros m2 tb' sn' high' fast' yt0 yt1 ya0 ya3 ya4 ya5 yt5 yt6 I2 P2 LT.
      eapply (IH m2 h0 h1 (s + 1)); [exact I2 | exact P2 | lia | lia | exact KONT].
  Qed.

  (* [comment removed for export] *)
  Lemma bd_p1_0A : forall (f : nat) m1 h0 h1 tb sn sp high fast xt0 xt1 xa0 xa3 xa4 xa5 xt5 xt6,
    BDm h0 h1 tb sn sp m1 -> p1_inv norm maxSV tl 0 tb sn high fast -> Z.of_nat (S f) = maxSV + 1 ->
    (forall m2 tb' sn' high' fast' yt0 yt1 ya0 ya3 ya4 ya5 yt5 yt6, BDm h0 h1 tb' sn' sp m2 -> p1_inv norm maxSV tl (maxSV + 1) tb' sn' high' fast' ->
       evtF bsegs RNG POST (ST1X 0xaf378 m2 high' (maxSV + 1) yt0 yt1 ya0 ya3 ya4 ya5 yt5 yt6 fast')) ->
    evtF bsegs RNG POST (ST1 0xaf280 m1 high 0 xt0 xt1 xa0 xa3 xa4 xa5 xt5 xt6 fast).
  Proof.
    intros until xt6; intros I P1 HF KONT.
    eapply (bd_p1_loopA f m1 h0 h1 0); [exact I | exact P1 | lia | lia | exact KONT].
  Qed.
End P1.
End CANSEC1.
