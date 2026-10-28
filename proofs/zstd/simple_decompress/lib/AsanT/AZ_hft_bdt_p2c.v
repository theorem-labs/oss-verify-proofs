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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_bdt_defs AZ_hft_bdt_p2a.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC1. Context {rc : runConstT}.
Section P2C.
  Variables (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem)
            (SPV lo DT NC W wlen maxSV tl : Z) (norm : list Z).
  Hypothesis HY : bdA_hyps RNG SPV lo DT NC W wlen maxSV tl norm.
  Hypothesis UDT : unpoisoned m DT (DT + 4 + 4 * 2^tl).
  Hypothesis UW : unpoisoned m W (W + wlen).
  Hypothesis UNC : unpoisoned m NC (NC + 2 * zlen norm).
  Hypothesis ART0 : art m.
  (* [comment removed for export] *)
  Notation BDm := (BDA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC W wlen maxSV tl norm (Z_to_bv 64 (2 * maxSV + W + 10)) (Z_to_bv 64 (fse_tablestep (2^tl)))).
  Notation BDg xf8 xf16 := (BDA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC W wlen maxSV tl norm xf8 xf16).
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

  Notation SP0 := (W + 2 * (maxSV + 1)).

  (* [comment removed for export] *)
  Notation STP pc mm j pos xra xs0 xs1 xa0 xa2 xa4 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt6 :=
    (ST pc mm xra (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (2^tl + -1)) xs0 xs1 xa0 (Z_to_bv 64 (SP0 + j)) xa2
        (Z_to_bv 64 tl) xa4 (Z_to_bv 64 j) (Z_to_bv 64 STEP) xa7 (Z_to_bv 64 (2^tl)) (Z_to_bv 64 W) (Z_to_bv 64 DT) xs5 xs6 xs7 xs8 xs9 xs10 xs11
        (Z_to_bv 64 (2 * STEP)) (Z_to_bv 64 pos) (Z_to_bv 64 (SP0 + 1)) xt6).
  (* [comment removed for export] *)
  Notation STE mm xra x7 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (ST 0xabc84 mm xra (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 0x7fff8000) x7 xs0 xs1 xa0 xa1 xa2 (Z_to_bv 64 tl) xa4 xa5 xa6 (Z_to_bv 64 (DT + 7))
        (Z_to_bv 64 (2^tl)) (Z_to_bv 64 W) xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma bd_place_bodyA : forall m1 tb sn sp fast j xra xs0 xs1 xa0 xa2 xa4 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt6,
    BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp m1 -> lay_inv norm maxSV (maxSV + 1) sp -> p2_inv norm maxSV tl j tb ->
    0 <= j -> j + 2 <= 2^tl ->
    (forall m2 tb' yra ys0 ys1 ya0 ya2 ya4 ya7 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt6, BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb' sn sp m2 -> p2_inv norm maxSV tl (j + 2) tb' -> j + 2 < 2^tl ->
       evtF bsegs RNG POST (STP 0xabbb8 m2 (j + 2) (((j + 2) * STEP) mod 2^tl) yra ys0 ys1 ya0 ya2 ya4 ya7 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt6)) ->
    (forall m2 tb' yra y7 ys0 ys1 ya0 ya1 ya2 ya4 ya5 ya6 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31, BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb' sn sp m2 -> p2_inv norm maxSV tl (2^tl) tb' ->
       evtF bsegs RNG POST (STE m2 yra y7 ys0 ys1 ya0 ya1 ya2 ya4 ya5 ya6 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STP 0xabbb8 m1 j ((j * STEP) mod 2^tl) xra xs0 xs1 xa0 xa2 xa4 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt6).
  Proof.
    intros until xt6; intros I LI P2 HJ HJF KH KE; bd_open I.
    pose proof (hSRC_total norm maxSV tl TLR MSVR NLEN NGE NSUM) as NS3; rewrite NOLOW in NS3.
    assert (STEPR : 0 <= STEP < 1048576) by (unfold fse_tablestep; Z.div_mod_to_equations; lia).
    assert (PR0 : 0 <= (j * STEP) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
    assert (PR1 : 0 <= ((j + 1) * STEP) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
    assert (PR2 : 0 <= ((j + 2) * STEP) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
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
    assert (SB0 : 0 <= Znth j sp < 256) by (apply (Forall_Znth _ sp j SPBY); lia).
    assert (SB1 : 0 <= Znth (j + 1) sp < 256) by (apply (Forall_Znth _ sp (j + 1) SPBY); lia).
    pose proof (LI j ltac:(lia)) as SY0. pose proof (LI (j + 1) ltac:(lia)) as SY1.
    (* [comment removed for export] *)
    kx_autoFLAc (FR, HDR) (@nil kza) [0xabbd4] 16%nat
      (KZB ++ [KZRange j 0 511; KZRange (2^tl - j) 2 512; KZRange pos 0 511; KZRange STEP 0 1048576])
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z. all: try kx_acc RW. all: try kx_acc RSTK. all: try kx_sh_rd_any. all: try (kx_sh_acc RSW). all: try (kx_sh_dead UW1 2).
    kx_mem. kx_tidy_run.
    rewrite ?(Z.mod_small pos (2^64)) by lia. rewrite ?(Z.mod_small (2^tl + -1) (2^64)) by lia. try rewrite (LAND pos) by lia. try rewrite (Z.mod_small pos (2^tl)) by lia.
    (* [comment removed for export] *)
    bd_lens.
    kx_autoFLAc (FR, HDR) [KAUnp (DT + 4 + 4 * pos + 2) 1; KAApp (DT + 4 + 4 * pos + 2) 1; KAUnp (SP0 + j) 2] [0xabbf4; 0xabc34; 0xabc84] 40%nat
      (KZB ++ [KZRange j 0 511; KZRange (2^tl - j) 2 512; KZRange pos 0 511; KZRange (2^tl - pos) 1 512; KZRange (4 * 2^tl - 4 * pos) 4 2048;
               KZRange STEP 0 1048576; KZRange (SP0 + j) 4096 (2^47 - 8); KZRange (wlen - 2 * maxSV - 4 - j) 0 (2^32); KZRange (DT + 4 + 4 * pos + 2) 4096 (2^47 - 8);
               KZWr (DT + 4 + 4 * pos + 2) 1; KZDisj (DT + 4 + 4 * pos + 2) 1 NC (2 * zlen norm); KZDisj (DT + 4 + 4 * pos + 2) 1 (SPV - 144) 144;
               KZDisj (DT + 4 + 4 * pos + 2) 1 W (2 * (maxSV + 1)); KZDisj (DT + 4 + 4 * pos + 2) 1 SP0 (wlen - 2 * (maxSV + 1));
               KZDisj (DT + 4 + 4 * pos + 2) 1 W wlen; KZDisj (DT + 4 + 4 * pos + 2) 1 DT 4])
      [(SP0 + j, 2)] [(SP0 + j, 2); (DT + 4 + 4 * pos + 2, 1)].
    all: try kx_z. all: try kx_acc RW. all: try kx_acc RDT. all: try kx_acc RSTK. all: try kx_sh_rd_any. all: try (kx_sh_acc RSDT). all: try (kx_sh_dead UDT1 1).
    let rd r := (let v := StepF.reg_val r in lazymatch v with context [ev _ ?k] => kx_read_eq k RD | context [EVar ?k] => kx_read_eq k RD end;
                 rewrite (rdval_u8Zb bsegs _ SP0 sp j _ SPRD) in RD; [| lia | lia | exact SPBY]) in
    first [ rd 10 | rd 12 | rd 9 | rd 11 | rd 13 | rd 14 | rd 17 | rd 19 | rd 20 | rd 21 | rd 1 | rd 8 | rd 31 ].
    kxk_keep CEL. kx_gen_regsF [8%nat; 10%nat; 31%nat]. kx_mem. rewrite RD in *. kx_tidy_run. bd_reunp.
    kxk_ix CEL (4 * pos + 2). rewrite ?(unsigned_lit (Znth j sp)) in * by lia. kxk_vl CEL (Znth j sp).
    (* [comment removed for export] *)
    bd_lens.
    assert (PL1a : Z.land ((pos + STEP) mod 2^64) ((2^tl + -1) mod 2^64) = pos1)
      by (rewrite !Z.mod_small by lia; rewrite LAND by lia; rewrite <- E1; f_equal; lia).
    try assert (PL1b : Z.land ((pos mod 2^64 + STEP mod 2^64) mod 2^64) ((2^tl + -1) mod 2^64) = pos1)
      by (rewrite (Z.mod_small pos), (Z.mod_small STEP), !Z.mod_small by lia; rewrite LAND by lia; rewrite <- E1; f_equal; lia).
    try assert (PL1c : Z.land (pos + STEP) (2^tl + -1) = pos1) by (rewrite LAND by lia; rewrite <- E1; f_equal; lia).
    (* [comment removed for export] *)
    bd_lens.
    kx_autoFLAc (FR, HDR) [KAUnp (DT + 4 + 4 * pos1 + 2) 1; KAApp (DT + 4 + 4 * pos1 + 2) 1; KAUnp (SP0 + j) 2] [0xabc10] 12%nat
      (KZB ++ [KZRange j 0 511; KZRange (2^tl - j) 2 512; KZRange pos1 0 511; KZRange (2^tl - pos1) 1 512; KZRange (4 * 2^tl - 4 * pos1) 4 2048;
               KZRange pos 0 511; KZRange STEP 0 1048576;
               KZRange (SP0 + j) 4096 (2^47 - 8); KZRange (wlen - 2 * maxSV - 4 - j) 0 (2^32); KZRange (DT + 4 + 4 * pos1 + 2) 4096 (2^47 - 8)])
      [(SP0 + j, 2)] [(SP0 + j, 2); (DT + 4 + 4 * pos1 + 2, 1)].
    all: try kx_z. all: try kx_acc RW. all: try kx_acc RDT. all: try kx_acc RSTK. all: try kx_sh_rd_any.
    all: try (kx_sh_acc RSW). all: try (kx_sh_acc RSDT). all: try (kx_sh_dead UW1 2). all: try (kx_sh_dead UDT1 1).
    all: kx_mem. all: kx_tidy_run. all: bd_reunp.
    all: repeat match goal with |- context [Z.land ?a ?b] =>
      replace (Z.land a b) with pos1 by (first [ exact PL1a | exact PL1b | exact PL1c
                                               | (rewrite !Z.mod_small by lia; rewrite LAND by lia; rewrite <- E1; f_equal; lia) ]) end.
    bd_lens.
    kx_autoFLAc (FR, HDR) [KAUnp (DT + 4 + 4 * pos1 + 2) 1; KAApp (DT + 4 + 4 * pos1 + 2) 1; KAUnp (SP0 + j) 2] [0xabc34; 0xabc84] 40%nat
      (KZB ++ [KZRange j 0 511; KZRange (2^tl - j) 2 512; KZRange pos1 0 511; KZRange (2^tl - pos1) 1 512; KZRange (4 * 2^tl - 4 * pos1) 4 2048;
               KZRange pos 0 511; KZRange STEP 0 1048576;
               KZRange (SP0 + j) 4096 (2^47 - 8); KZRange (wlen - 2 * maxSV - 4 - j) 0 (2^32); KZRange (DT + 4 + 4 * pos1 + 2) 4096 (2^47 - 8);
               KZWr (DT + 4 + 4 * pos1 + 2) 1; KZDisj (DT + 4 + 4 * pos1 + 2) 1 NC (2 * zlen norm); KZDisj (DT + 4 + 4 * pos1 + 2) 1 (SPV - 144) 144;
               KZDisj (DT + 4 + 4 * pos1 + 2) 1 W (2 * (maxSV + 1)); KZDisj (DT + 4 + 4 * pos1 + 2) 1 SP0 (wlen - 2 * (maxSV + 1));
               KZDisj (DT + 4 + 4 * pos1 + 2) 1 W wlen; KZDisj (DT + 4 + 4 * pos1 + 2) 1 DT 4])
      [(SP0 + j, 2)] [(SP0 + j, 2); (DT + 4 + 4 * pos1 + 2, 1)].
    all: try kx_z. all: try kx_acc RW. all: try kx_acc RDT. all: try kx_acc RSTK. all: try kx_sh_rd_any.
    all: try (kx_sh_acc RSW). all: try (kx_sh_acc RSDT). all: try (kx_sh_dead UW1 2). all: try (kx_sh_dead UDT1 1).
    let rd r := (let v := StepF.reg_val r in lazymatch v with context [ev _ ?k] => kx_read_eq k RD1 | context [EVar ?k] => kx_read_eq k RD1 end;
                 match goal with H : u8arr bsegs _ SP0 (map (Z_to_bv 8) sp) |- _ =>
                   rewrite (rdval_u8Zb bsegs _ SP0 sp (j + 1) _ H) in RD1; [| lia | lia | exact SPBY] end) in
    first [ rd 10 | rd 12 | rd 9 | rd 11 | rd 13 | rd 14 | rd 17 | rd 19 | rd 20 | rd 21 | rd 1 | rd 8 | rd 31 | rd 18 | rd 22 | rd 23 | rd 24
          | rd 25 | rd 26 | rd 27 | rd 5 | rd 6 | rd 7 | rd 15 | rd 16 | rd 28 | rd 29 | rd 30 ].
    kxk_keep CEL. kx_mem. rewrite RD1 in *. kx_tidy_run. bd_reunp.
    kxk_ix CEL (4 * pos1 + 2). rewrite ?(unsigned_lit (Znth (j + 1) sp)) in * by lia. kxk_vl CEL (Znth (j + 1) sp).
    (* [comment removed for export] *)
    bd_lens.
    kx_autoFLAc (FR, HDR) (@nil kza) [0xabc40] 12%nat
      (KZB ++ [KZRange j 0 511; KZRange (2^tl - j) 2 512; KZRange pos 0 511; KZRange pos1 0 511; KZRange STEP 0 1048576])
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z. all: try kx_acc RSTK.
    all: kx_mem. all: kx_tidy_run. all: bd_reunp.
    match goal with |- context [Z.land ?a ?b] =>
      replace (Z.land a b) with pos2 by (rewrite !Z.mod_small by lia; rewrite LAND by lia; rewrite <- E2; f_equal; lia) end.
    (* [comment removed for export] *)
    bd_lens.
    kx_autoFLAc (FR, HDR) (@nil kza) [0xabbb8; 0xabc84] 10%nat (KZB ++ [KZRange j 0 511; KZRange (2^tl - j) 2 512; KZRange pos2 0 511]) (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z. all: try kx_acc RSTK. all: kx_mem. all: kx_tidy_run.
    all: set (tb2 := Zupd (4 * pos1 + 2) (Znth (j + 1) sp) (Zupd (4 * pos + 2) (Znth j sp) tb)) in *.
    all: assert (CBY' : Forall isbyte tb2) by (unfold tb2; repeat apply Forall_Zupd; [exact CBY | lia | lia]).
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xabc84) _ _ _ _) =>
             replace (j + 2) with (2^tl) in P2b by lia; eapply KE; [close_bd | exact P2b]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) =>
             match goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?a) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => replace a with (SP0 + (j + 2)) by lia end;
             eapply KH; [close_bd | exact P2b | lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_place_loopA : forall (f : nat) m1 tb sn sp fast j xra xs0 xs1 xa0 xa2 xa4 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt6,
    BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp m1 -> lay_inv norm maxSV (maxSV + 1) sp -> p2_inv norm maxSV tl j tb ->
    0 <= j -> j + 2 * Z.of_nat (S f) = 2^tl ->
    (forall m2 tb' yra y7 ys0 ys1 ya0 ya1 ya2 ya4 ya5 ya6 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31, BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb' sn sp m2 -> symtab_ok norm maxSV tl tb' -> zlen tb' = 4 * 2^tl ->
       evtF bsegs RNG POST (STE m2 yra y7 ys0 ys1 ya0 ya1 ya2 ya4 ya5 ya6 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STP 0xabbb8 m1 j ((j * STEP) mod 2^tl) xra xs0 xs1 xa0 xa2 xa4 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt6).
  Proof.
    induction f as [|f IH]; intros until xt6; intros I LI P2 HJ HJF KP3; open_hy HY.
    - eapply bd_place_bodyA; [exact I | exact LI | exact P2 | exact HJ | lia | intros; exfalso; lia |].
      intros m2 tb' yra y7 ys0 ys1 ya0 ya1 ya2 ya4 ya5 ya6 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31 I2 P2'.
      pose proof I2 as I2'. open_bd I2'.
      eapply KP3; [exact I2 | | exact CLEN].
      apply (p2_done norm maxSV tl TLR MSVR NLEN NGE NSUM). rewrite NOLOW. replace (2^tl - 1 + 1) with (2^tl) by lia. exact P2'.
    - eapply bd_place_bodyA; [exact I | exact LI | exact P2 | exact HJ | lia | |].
      + intros m2 tb' yra ys0 ys1 ya0 ya2 ya4 ya7 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt6 I2 P2' LT.
        eapply (IH m2 tb' sn sp fast (j + 2)); [exact I2 | exact LI | exact P2' | lia | lia | exact KP3].
      + intros m2 tb' yra y7 ys0 ys1 ya0 ya1 ya2 ya4 ya5 ya6 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31 I2 P2'.
        pose proof I2 as I2'. open_bd I2'.
        eapply KP3; [exact I2 | | exact CLEN].
        apply (p2_done norm maxSV tl TLR MSVR NLEN NGE NSUM). rewrite NOLOW. replace (2^tl - 1 + 1) with (2^tl) by lia. exact P2'.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_fastA : forall xf8 xf16 m1 tb sn sp fast xra xa4 xa5 xa7 xs7 xs8 xs9 xs10 xs11,
    BDg xf8 xf16 (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp m1 -> p2_inv norm maxSV tl 0 tb ->
    (forall m2 tb' sp' yra y7 ys0 ys1 ya0 ya1 ya2 ya4 ya5 ya6 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31,
       BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb' sn sp' m2 -> symtab_ok norm maxSV tl tb' -> zlen tb' = 4 * 2^tl ->
       evtF bsegs RNG POST (STE m2 yra y7 ys0 ys1 ya0 ya1 ya2 ya4 ya5 ya6 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (ST 0xab95c m1 xra (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (2^tl + -1))
                           (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 maxSV) (Z_to_bv 64 851192) (Z_to_bv 64 NC) (Z_to_bv 64 (2^tl / 2))
                           (Z_to_bv 64 tl) xa4 xa5 (Z_to_bv 64 SP0) xa7 (Z_to_bv 64 (2^tl)) (Z_to_bv 64 W) (Z_to_bv 64 DT)
                           (Z_to_bv 64 (NC + 2 * (maxSV + 1))) (Z_to_bv 64 SP0) xs7 xs8 xs9 xs10 xs11
                           (Z_to_bv 64 (2 * maxSV + W + 2)) (Z_to_bv 64 HIGH) (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 fast)).
  Proof.
    intros until xs11; intros I P2 KP3. bd_open I.
    pose proof (hhigh_range norm maxSV tl TLR ltac:(lia) NLEN NGE NSUM) as HR.
    assert (STEPR : 19 <= STEP <= 1048575) by (destruct (bdA_size_rng _ _ _ _ _ _ _ _ _ _ HY) as (SZ' & _); unfold fse_tablestep; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    kx_autoFLAc FR [KAApp (SPV - 144) 144] [0xab9b0] 20%nat (KZB ++ [KZRange (2^tl / 2) 16 256; KZRange (2^tl / 8) 4 64; KZWr (SPV - 144) 144;
                                                           KZDisj (SPV - 144) 144 NC (2 * zlen norm); KZDisj (SPV - 144) 144 DT 4;
                                                           KZDisj (SPV - 144) 144 (DT + 4) (4 * 2^tl); KZDisj (SPV - 144) 144 W (2 * (maxSV + 1));
                                                           KZDisj (SPV - 144) 144 SP0 (wlen - 2 * (maxSV + 1))])
      [(SPV - 144, 144)] [(SPV - 144, 144)].
    all: try kx_z. all: try kx_acc RSTK. all: kx_mem. all: kx_tidy_run. all: bd_reunp.
    (* [comment removed for export] *)
    replace (2 * maxSV + W + 10) with (SP0 + 8) by lia. replace (2 * maxSV + W + 2) with SP0 by lia.
    replace (2 ^ tl mod 2 ^ 64) with (2 ^ tl) by (symmetry; apply Z.mod_small; split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
    change (2 ^ tl / 2 + 2 ^ tl / 8 + 3) with STEP.
    (* [comment removed for export] *)
    eapply bd_lay_loopA with (f := Z.to_nat maxSV) (tb := tb) (sn := sn) (sp := sp) (fast := fast) (s := 0);
      [eassumption .. | close_bd | | lia | lia |].
    { intros jj Hj. exfalso. rewrite nsrc_0 in Hj. lia. }
    intros m2 sp' yra ys0 ya3 ya4 ya6 ys4 ys5 ys7 ys8 ys9 ys10 ys11 yt5 yt6 I2 LI2. bd_reopen I2.
    (* [comment removed for export] *)
    kx_autoFLAc FR (@nil kza) [0xabbb8] 12%nat (KZB ++ [KZRange STEP 19 1048575]) [(SPV - 144, 144)] [(SPV - 144, 144)].
    all: try kx_z. all: try kx_acc RSTK. all: kx_mem. all: kx_tidy_run.
    replace (2 * maxSV + W + 2) with (SP0 + 0) by lia. replace (2 * maxSV + W + 3) with (SP0 + 1) by lia.
    change (Z_to_bv 64 0) with (Z_to_bv 64 ((0 * STEP) mod 2^tl)).
    eapply (bd_place_loopA (Z.to_nat (2^(tl - 1) - 1)) m2 tb sn sp' fast 0); [close_bd | exact LI2 | exact P2 | lia | lia |].
    intros until 0. intros I4 OK4 L4. eapply KP3; [exact I4 | exact OK4 | exact L4].
  Qed.
End P2C.
End CANSEC1.
