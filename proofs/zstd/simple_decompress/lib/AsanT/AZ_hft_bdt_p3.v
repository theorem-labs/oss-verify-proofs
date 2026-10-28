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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_bdt_defs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC1. Context {rc : runConstT}.
Section P3.
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

  (* [comment removed for export] *)
  Lemma bd_wk_stkA : forall h0 h1 tb sn sp m1, BDm h0 h1 tb sn sp m1 ->
    stk bsegs m1 W (W + wlen) /\ stk bsegs m1 DT (DT + 4 + 4 * 2^tl).
  Proof.
    intros h0 h1 tb sn sp m1 I. open_hy HY. open_bd I. split.
    - apply rw_cells_of_u8arr in SNX. apply stk_of_rw_cells in SNX. apply rw_cells_of_u8arr in SPRD. apply stk_of_rw_cells in SPRD.
      cbn [cells_size csize] in SNX, SPRD. rewrite u16s_length, length_map in SNX. rewrite length_map in SPRD.
      apply (stk_merge bsegs m1 W (W + 2 * (maxSV + 1)) (W + wlen)); [| |lia].
      + replace (W + 2 * (maxSV + 1)) with (W + Z.of_nat (2 * length sn + 0)) by lia. exact SNX.
      + replace (W + wlen) with (W + 2 * (maxSV + 1) + Z.of_nat (length sp + 0)) by lia. exact SPRD.
    - apply stk_of_rw_cells in HDR. apply rw_cells_of_u8arr in CEL. apply stk_of_rw_cells in CEL.
      cbn [cells_size csize] in HDR, CEL. rewrite length_map in CEL.
      apply (stk_merge bsegs m1 DT (DT + 4) (DT + 4 + 4 * 2^tl)); [| |lia].
      + replace (DT + 4) with (DT + Z.of_nat (2 + (2 + 0))) at 2 by lia. exact HDR.
      + replace (DT + 4 + 4 * 2^tl) with (DT + 4 + Z.of_nat (length tb + 0)) by lia. exact CEL.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_epiA : forall h0 h1 tb sn sp m1 r xra x5 x6 x7 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    BDm h0 h1 tb sn sp m1 ->
    0 <= r < 2^64 ->
    ((r = 0 /\ exists fast, h0 = Z_to_bv 64 tl /\ h1 = Z_to_bv 64 fast /\ 0 <= fast <= 1 /\ forall u, 0 <= u < 2^tl -> fse_cell_ok tl fast tb u)
     \/ zd_is_error r = true) ->
    evtF bsegs RNG POST
      (ST 0xabdcc m1 xra x5 x6 x7 xs0 xs1 (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I RR RES. pose proof (bd_wk_stkA _ _ _ _ _ _ I) as (WKS & DTS). bd_open I.
    kx_autoFLAc FR [KAApp (SPV - 144) 144] (@nil Z) 20%nat (KZB ++ [KZRange r 0 (2^64 - 1); KZWr (SPV - 144) 144]) [(SPV - 144, 144)] [(SPV - 144, 144)].
    all: try kx_z. all: try kx_acc RSTK.
    all: kx_mem. all: zstep.
    release_frame FR STK SPV.
    apply evtF_done. unfold fse_bdt_postA.
    do 14 eexists. exists m1, r.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|]. split; [exact WKS|]. split; [exact RR|].
    destruct RES as [(R0 & fast & E0 & E1 & FR01 & OK)|ERR].
    - left. split; [exact R0|]. exists fast, tb. subst h0 h1. unfold fse_dtable.
      split; [exact HDR|]. split; [exact CEL|]. split; [exact CLEN|]. split; [exact FR01|]. split; [exact CBY| exact OK].
    - right. split; [exact ERR| exact DTS].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (T : Z -> Z) (fast : Z).
  Hypothesis TGOOD : forall v, 0 <= v < 2^tl -> good norm maxSV (T v).
  Hypothesis TCNT : forall s, 0 <= s <= maxSV -> hocc T s (2^tl) = weight (Znth s norm).
  Hypothesis FASTH : fast = 1 -> forall i, 0 <= i <= maxSV -> Znth i norm < 2^(tl - 1).
  Hypothesis FASTR : 0 <= fast <= 1.

  (* [comment removed for export] *)
  Notation ST3 pc mm u xra xs0 xs1 xa0 xa1 xa4 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 :=
    (ST pc mm xra (Z_to_bv 64 (DT + 4 + 4 * u)) (Z_to_bv 64 2147450880) (Z_to_bv 64 16843009) xs0 xs1 xa0 xa1 (Z_to_bv 64 1431655765) (Z_to_bv 64 tl) xa4 (Z_to_bv 64 858993459) (Z_to_bv 64 252645135) (Z_to_bv 64 (DT + 7 + 4 * u))
        (Z_to_bv 64 (2^tl)) (Z_to_bv 64 W) xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (2^tl - u)) xt4 xt5 xt6).

  (* [comment removed for export] *)
  Lemma bd_p3_bodyA : forall m1 u tb sn sp xra xs0 xs1 xa0 xa1 xa4 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6,
    BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp m1 -> p3_inv norm maxSV tl T fast u tb sn -> 0 <= u < 2^tl ->
    (forall m2 tb' sn' ya0 ya1 ya4 yt4 yt5, BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb' sn' sp m2 -> p3_inv norm maxSV tl T fast (u + 1) tb' sn' ->
       evtF bsegs RNG POST (ST3 0xabd84 m2 (u + 1) xra xs0 xs1 ya0 ya1 ya4 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt4 yt5 xt6)) ->
    evtF bsegs RNG POST (ST3 0xabca8 m1 u xra xs0 xs1 xa0 xa1 xa4 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6).
  Proof.
    intros until xt6; intros I P3 HU KONT. bd_open I.
    pose proof (p3_step norm maxSV tl TLR MSVR NLEN NGE NSUM T fast TGOOD TCNT FASTH u tb sn P3 HU) as STEP. cbv zeta in STEP.
    set (sym := hsym tb u) in *. set (ns := Znth sym sn) in *.
    destruct STEP as (SYR & NSR & LGR & NXR & P3').
    (* [comment removed for export] *)
    kx_autoFLAc (FR, HDR) [KAUnp (DT + 4 + 4 * u + 2) 1] [0xabcc0] 20%nat
      (KZB ++ [KZRange u 0 511; KZRange (2^tl - u) 1 512; KZRange (DT + 4 + 4 * u + 2) 4096 (2^47 - 8); KZRange (4 * 2^tl - 4 * u) 4 2048])
      [(DT + 4 + 4 * u + 2, 1)] [(DT + 4 + 4 * u + 2, 1)].
    all: try kx_z. all: try kx_acc RDT. all: try kx_acc RSTK.
    kx_read_reg 10 RD.
    rewrite (rdval_u8Zb bsegs m1 (DT + 4) tb (4 * u + 2) _ CEL) in RD; [| lia | lia | exact CBY].
    change (Znth (4 * u + 2) tb) with (hsym tb u) in RD. fold sym in RD.
    rewrite RD. kx_tidy_run. kx_gen_regsF [11%nat; 14%nat].
    (* [comment removed for export] *)
    bd_lens. kx_autoFLAc (FR, HDR) [KAUnp (W + 2 * sym) 2] [0xabcdc] 30%nat
      (KZB ++ [KZRange u 0 511; KZRange sym 0 255; KZRange (maxSV - sym) 0 255; KZRange (W + 2 * sym) 4096 (2^47 - 8); KZRange (wlen - 2 * sym - 2) 40 (2^32)])
      [(W + 2 * sym, 2)] [(W + 2 * sym, 2)].
    all: try kx_z. all: try kx_acc RW. all: try kx_acc RSTK.
    kx_read_reg 29 RD2.
    rewrite (rdval_u16Z bsegs m1 W sn sym _ (proj1 SNX)) in RD2 by lia. fold ns in RD2. rewrite (Z.mod_small ns 65536) in RD2 by lia.
    rewrite RD2. kx_tidy_run. kx_gen_regsF [10%nat; 14%nat].
    (* [comment removed for export] *)
    bd_lens. kx_autoFLAc (FR, HDR) [KAUnp (W + 2 * sym) 2; KAApp (W + 2 * sym) 2; KAUnp (DT + 4 + 4 * u + 3) 1] [0xabcf8] 30%nat
      (KZB ++ [KZRange u 0 511; KZRange (2^tl - u) 1 512; KZRange sym 0 255; KZRange (maxSV - sym) 0 255; KZRange ns 1 65535;
               KZRange (W + 2 * sym) 4096 (2^47 - 8); KZRange (DT + 4 + 4 * u + 3) 4096 (2^47 - 8); KZRange (4 * 2^tl - 4 * u) 4 2048;
               KZRange (wlen - 2 * sym - 2) 40 (2^32);
               KZWr (W + 2 * sym) 2; KZDisj (W + 2 * sym) 2 NC (2 * zlen norm); KZDisj (W + 2 * sym) 2 (SPV - 144) 144;
               KZDisj (W + 2 * sym) 2 (DT + 4) (4 * 2^tl); KZDisj (W + 2 * sym) 2 DT 4; KZDisj (W + 2 * sym) 2 (W + 2 * (maxSV + 1)) (wlen - 2 * (maxSV + 1))])
      (@nil (Z * Z)) [(W + 2 * sym, 2); (DT + 4 + 4 * u + 3, 1)].
    all: try kx_z. all: try kx_acc RW. all: try kx_acc RDT.
    kxk_keep CEL. kxk_keep_ix SNX [sym]. kx_mem. kx_tidy_run. bd_reunp.
    rewrite ?(unsigned_lit ns) in SNX by lia. rewrite (Z.mod_small (ns + 1) 65536) in SNX by lia.
    assert (SNLEN' : zlen (Zupd sym (ns + 1) sn) = maxSV + 1) by (rewrite Zupd_length2; exact SNLEN).
    kx_gen_regsF [10%nat; 14%nat].
    (* [comment removed for export] *)
    zstep. zstep. set (sa := Z.lor ns (ns ≫ 1)). zstep. zstep. set (sb := Z.lor sa (sa ≫ 2)). zstep. zstep. set (sc := Z.lor sb (sb ≫ 4)).
    zstep. zstep. zstep.
    lazymatch goal with |- _ => let v := StepF.reg_val 10 in lazymatch v with Z_to_bv 64 ?e => change e with (smear16 ns) end end.
    rewrite (smear16_ok ns) by lia.
    set (L := Z.log2 ns) in *.
    assert (HL : 0 <= L <= 10).
    { subst L. split; [apply Z.log2_nonneg|]. assert (Z.log2 ns < 11); [|lia]. apply Z.log2_lt_pow2; [lia|]. change (2^11) with 2048. lia. }
    do 15 zstep.
    lazymatch goal with |- _ => let v := StepF.reg_val 10 in lazymatch v with Z_to_bv 64 ?e =>
      replace e with L by (clear - HL; clearbody L;
        assert (C : L = 0 \/ L = 1 \/ L = 2 \/ L = 3 \/ L = 4 \/ L = 5 \/ L = 6 \/ L = 7 \/ L = 8 \/ L = 9 \/ L = 10) by lia;
        destruct C as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]; rewrite E; vm_compute; reflexivity) end end.
    zstep.                                                     (* [comment removed for export] *)
                                                               (* [comment removed for export] *)
                                                               (* [comment removed for export] *)
    rewrite (FseWalkKit.swrap32_small (tl - L)) by lia.
    subst sa sb sc.
    replace (Z_to_bv 64 ((DT + 4 + 4 * u) ≫ 3)) with (Z_to_bv 64 ((DT + 4 + 4 * u) / 8)) by (f_equal; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    (* [comment removed for export] *)
    bd_lens. kx_autoFLAc (FR, HDR) [KAUnp (DT + 4 + 4 * u) 4; KAApp (DT + 4 + 4 * u) 4; KAShp (2147450880 + (DT + 4 + 4 * u) / 8) (DT + 4 + 4 * u)] [0xabd6c] 30%nat
      (KZB ++ [KZRange u 0 511; KZRange (2^tl - u) 1 512; KZRange L 0 10; KZRange (tl - L) 0 9;
               KZRange (DT + 4 + 4 * u) 4096 (2^47 - 8); KZRange (4 * 2^tl - 4 * u) 4 2048;
               KZWr (DT + 4 + 4 * u) 4; KZDisj (DT + 4 + 4 * u) 4 NC (2 * zlen norm); KZDisj (DT + 4 + 4 * u) 4 (SPV - 144) 144;
               KZDisj (DT + 4 + 4 * u) 4 W wlen; KZDisj (DT + 4 + 4 * u) 4 DT 4; KZDisj (DT + 4 + 4 * u) 4 W (2 * (maxSV + 1));
               KZDisj (DT + 4 + 4 * u) 4 (W + 2 * (maxSV + 1)) (wlen - 2 * (maxSV + 1))])
      (@nil (Z * Z)) [(DT + 4 + 4 * u, 4)].
    all: try kx_z. all: try kx_acc RDT.
    all: try (kx_side_pre; unfold hidden in BDT; Z.div_mod_to_equations; lia).
    kxk_keep CEL. kx_mem. kx_tidy_run. bd_reunp.
    kxk_ix CEL (4 * u + 3). kxk_vl CEL (tl - L). kx_gen_regsF [10%nat; 14%nat; 30%nat].
    (* [comment removed for export] *)
    zstep. rewrite (shiftl_mod32 ns (tl - L)) by lia.
    pose proof (shl_hb_range ns tl ltac:(lia) ltac:(lia) ltac:(lia)) as NSB. fold L in NSB.
    rewrite (FseWalkKit.swrap32_small (ns * 2^(tl - L))) by lia.
    zstep.
    zstep.                                                     (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    rewrite (FseWalkKit.swrap32_small (ns * 2^(tl - L) - 2^tl)) by lia.
    set (nxt := ns * 2^(tl - L) - 2^tl) in *.
    (* [comment removed for export] *)
    bd_lens. kx_autoFLAc (FR, HDR) [KAApp (DT + 4 + 4 * u) 4] [0xabd84] 20%nat
      (KZB ++ [KZRange u 0 511; KZRange (2^tl - u) 1 512; KZRange nxt 0 511;
               KZRange (DT + 4 + 4 * u) 4096 (2^47 - 8); KZRange (4 * 2^tl - 4 * u) 4 2048;
               KZWr (DT + 4 + 4 * u) 4; KZDisj (DT + 4 + 4 * u) 4 NC (2 * zlen norm); KZDisj (DT + 4 + 4 * u) 4 (SPV - 144) 144;
               KZDisj (DT + 4 + 4 * u) 4 W wlen; KZDisj (DT + 4 + 4 * u) 4 DT 4; KZDisj (DT + 4 + 4 * u) 4 W (2 * (maxSV + 1));
               KZDisj (DT + 4 + 4 * u) 4 (W + 2 * (maxSV + 1)) (wlen - 2 * (maxSV + 1))])
      (@nil (Z * Z)) [(DT + 4 + 4 * u, 4)].
    all: try kx_z. all: try kx_acc RDT.
    kxk_keep CEL. kx_mem. kx_tidy_run. bd_reunp.
    kxk_ix CEL (4 * u + 1). kxk_ix2 CEL (4 * u). kxk_vl CEL (nxt / 256).
    (* [comment removed for export] *)
    rewrite (Zupd_comm (4 * u) (4 * u + 3) (nxt mod 256) (tl - L) tb) in CEL by lia.
    rewrite (Zupd_comm (4 * u + 1) (4 * u + 3) (nxt / 256) (tl - L) (Zupd (4 * u) (nxt mod 256) tb)) in CEL by lia.
    bd_lens.
    assert (CBY' : Forall isbyte (Zupd (4 * u + 3) (tl - L) (Zupd (4 * u + 1) (nxt / 256) (Zupd (4 * u) (nxt mod 256) tb)))).
    { repeat apply Forall_Zupd; [exact CBY | | | ]; clear - NXR SZ HL TLR LGR; Z.div_mod_to_equations; lia. }
    replace (4 * u + 4) with (4 * (u + 1)) by lia.
    lazymatch goal with |- _ => let v := StepF.reg_val 5 in lazymatch v with Z_to_bv 64 ?e => replace e with (DT + 4 + 4 * (u + 1)) by lia end end.
    lazymatch goal with |- _ => let v := StepF.reg_val 17 in lazymatch v with Z_to_bv 64 ?e => replace e with (DT + 7 + 4 * (u + 1)) by lia end end.
    lazymatch goal with |- _ => let v := StepF.reg_val 28 in lazymatch v with Z_to_bv 64 ?e => replace e with (2^tl - (u + 1)) by lia end end.
    eapply KONT; [close_bd | exact P3'].
  Qed.

  (* [comment removed for export] *)
  Lemma bd_p3_loopA : forall (f : nat) m1 u tb sn sp xra xs0 xs1 xa0 xa1 xa4 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6,
    BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb sn sp m1 -> p3_inv norm maxSV tl T fast u tb sn -> 0 <= u -> u + Z.of_nat (S f) = 2^tl ->
    evtF bsegs RNG POST (ST3 0xabca8 m1 u xra xs0 xs1 xa0 xa1 xa4 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6).
  Proof.
    induction f as [|f IH]; intros until xt6; intros I P3 HU HUF.
    - eapply bd_p3_bodyA; [exact I | exact P3 | lia |].
      intros m2 tb' sn' ya0 ya1 ya4 yt4 yt5 I2 P3'. bd_open I2.
      kx_autoFLAc FR (@nil kza) [0xabca8; 0xabdcc] 10%nat (KZB ++ [KZRange u 0 511; KZRange (2^tl - (u + 1)) 0 0]) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try kx_z. all: kx_mem. all: try (exfalso; lia).
      eapply (bd_epiA _ _ tb' sn' sp m2 0); [close_bd| lia |].
      left. split; [reflexivity|]. exists fast. split; [reflexivity|]. split; [reflexivity|]. split; [exact FASTR|].
      replace (u + 1) with (2^tl) in P3' by lia.
      exact (p3_done norm maxSV tl TLR MSVR NLEN NGE NSUM T fast TGOOD TCNT FASTH tb' sn' P3').
    - eapply bd_p3_bodyA; [exact I | exact P3 | lia |].
      intros m2 tb' sn' ya0 ya1 ya4 yt4 yt5 I2 P3'. bd_open I2.
      kx_autoFLAc FR (@nil kza) [0xabca8; 0xabdcc] 10%nat (KZB ++ [KZRange u 0 511; KZRange (2^tl - (u + 1)) 1 512]) (@nil (Z * Z)) (@nil (Z * Z)).
      all: try kx_z. all: kx_mem. all: try (exfalso; lia).
      eapply (IH m2 (u + 1)); [close_bd | exact P3' | lia | lia].
  Qed.

End P3.

Section P3E.
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


  (* [comment removed for export] *)
  Lemma bd_p3_entryA : forall fast m1 tb1 tb2 sn sp high xra x7 xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    BDm (Z_to_bv 64 tl) (Z_to_bv 64 fast) tb2 sn sp m1 -> p1_inv norm maxSV tl (maxSV + 1) tb1 sn high fast ->
    symtab_ok norm maxSV tl tb2 -> zlen tb2 = 4 * 2^tl ->
    evtF bsegs RNG POST (ST 0xabc84 m1 xra (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2147450880) x7 xs0 xs1 xa0 xa1 xa2 (Z_to_bv 64 tl) xa4 xa5 xa6 (Z_to_bv 64 (DT + 7))
                          (Z_to_bv 64 (2^tl)) (Z_to_bv 64 W) xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I P1 OK L2. bd_open I.
    assert (FASTR : 0 <= fast <= 1) by (destruct P1 as (_ & _ & _ & _ & _ & FR1 & _); exact FR1).
    destruct (p3_init norm maxSV tl TLR MSVR NLEN NGE NSUM tb1 sn high fast P1 tb2 OK L2) as (TGOOD' & TCNT' & FASTH' & P3).
    kx_autoFLAc FR (@nil kza) [0xabca8] 20%nat (KZB ++ []) (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_z. all: try kx_acc RSTK. all: kx_mem.
    replace (Z_to_bv 64 (DT + 4)) with (Z_to_bv 64 (DT + 4 + 4 * 0)) by (f_equal; lia).
    replace (Z_to_bv 64 (DT + 7)) with (Z_to_bv 64 (DT + 7 + 4 * 0)) by (f_equal; lia).
    assert (E0 : Z_to_bv 64 (2^tl) = Z_to_bv 64 (2^tl - 0)) by (f_equal; lia). rewrite E0 at 2. clear E0.
    eapply (bd_p3_loopA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UDT UW UNC f8 f16 (hsym tb2) fast TGOOD' TCNT' FASTH' FASTR (Z.to_nat (2^tl - 1)) _ 0 tb2 sn sp);
      [close_bd | exact P3 | lia | lia].
  Qed.
End P3E.
End CANSEC1.
