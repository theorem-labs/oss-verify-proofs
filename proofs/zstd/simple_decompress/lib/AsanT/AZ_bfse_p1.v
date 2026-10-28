(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdSeqBuildWU SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_blk_iface AZ_kx AZ_bfse_defs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit AZ_bfse_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

(* [comment removed for export] *)
Definition p1_step (norm : list Z) (tl s : Z) (st : list seqsym * list Z * Z * Z) : list seqsym * list Z * Z * Z :=
  let '(cells, symNext, high, fast) := st in
  if Znth s norm =? -1 then (set_base high s cells, Zupd s 1 symNext, high + -1, fast)
  else (cells, Zupd s (Znth s norm mod 2^16) symNext, high, if 2^(tl - 1) <=? Znth s norm then 0 else fast).

Lemma lowprob_S : forall norm tl f s cells symNext high fast,
  lowprob (S f) norm (2^(tl - 1)) s cells symNext high fast =
  (let '(c1, n1, h1, f1) := p1_step norm tl s (cells, symNext, high, fast) in lowprob f norm (2^(tl - 1)) (s + 1) c1 n1 h1 f1).
Proof.
  intros. cbn [lowprob p1_step]. destruct (Znth s norm =? -1); [replace (high - 1) with (high + -1) by lia|]; reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section P1.
  Variables (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem)
            (SPV lo DT NC BASE BITS W wlen maxSV tl : Z) (k : seq_kind) (norm : list Z).
  Hypothesis HY : bfA_hyps RNG SPV lo DT NC BASE BITS W wlen maxSV tl k norm.
  Hypothesis UDT : unpoisoned m DT (DT + 8 + 8 * 2^tl).
  Hypothesis UW : unpoisoned m W (W + wlen).
  Hypothesis UNC : unpoisoned m NC (NC + 2 * zlen norm).
  Hypothesis UBA : unpoisoned m BASE (BASE + 4 * (kind_max k + 1)).
  Hypothesis UBI : unpoisoned m BITS (BITS + (kind_max k + 1)).
  Hypothesis ART0 : art m.
  Notation BFm := (BFA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC BASE BITS W wlen maxSV tl k norm).
  (* [comment removed for export] *)
  Local Ltac kx_lia ::= kx_lia_sep7 DT NC SPV lo W BASE BITS.
  Local Ltac kxl_lia ::= kx_lia_sep7 DT NC SPV lo W BASE BITS.
  (* [comment removed for export] *)
  Local Ltac bf_reunp :=
    repeat match goal with H : unpoisoned ?mx _ _ |- _ => lazymatch mx with m => fail | _ => clear H end end;
    lazymatch goal with
    | MU : munch _ m ?m2 |- _ =>
        pose proof (bf_unp_dtM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UDT m2 MU) as UDT1;
        pose proof (bf_unp_wM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UW m2 MU) as UW1;
        pose proof (bf_unp_ncM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UNC m2 MU) as UNC1;
        pose proof (bf_unp_baM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UBA m2 MU) as UBA1;
        pose proof (bf_unp_biM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UBI m2 MU) as UBI1
    end.
  (* [comment removed for export] *)
  Local Ltac bf_lens :=
    lazymatch goal with
    | CEL : u8arr _ _ (DT + 8) (map _ ?cb), SNX : u8arr _ _ W (u16s (map _ ?sn)), SPRD : u8arr _ _ (W + 106) (map _ ?sp) |- _ =>
        first [ assert (zlen cb = 8 * 2^tl) by assumption
              | assert (zlen cb = 8 * 2^tl) by (rewrite ?Zupd_length2, sqb_len, ?set_base_length2, ?set_cell_length2; lia) ];
        first [ assert (zlen (map (Z_to_bv 8) cb) = 8 * 2^tl) by assumption
              | assert (zlen (map (Z_to_bv 8) cb) = 8 * 2^tl) by (rewrite length_map, ?Zupd_length2, sqb_len, ?set_base_length2, ?set_cell_length2; lia) ];
        first [ assert (zlen sn = 53) by assumption | assert (zlen sn = 53) by (rewrite ?Zupd_length2; assumption) ];
        first [ assert (zlen (u16s (map (Z_to_bv 64) sn)) = 106) by assumption
              | assert (zlen (u16s (map (Z_to_bv 64) sn)) = 106) by (rewrite u16s_length, length_map, ?Zupd_length2; lia) ];
        first [ assert (zlen sp = wlen - 106) by assumption
              | assert (zlen sp = wlen - 106) by (rewrite ?Zupd_length2, ?write8_length, ?Zupd_length2; assumption) ];
        first [ assert (zlen (map (Z_to_bv 8) sp) = wlen - 106) by assumption
              | assert (zlen (map (Z_to_bv 8) sp) = wlen - 106) by (rewrite length_map, ?Zupd_length2, ?write8_length, ?Zupd_length2; assumption) ]
    end.
  Local Ltac bf_consts :=
    try match goal with H : zlen (kind_base k) = _ |- _ => clear H end; try match goal with H : zlen (kind_bits k) = _ |- _ => clear H end;
    pose proof (kind_lens k) as (LKB & LKBI);
    assert (LNC : zlen (u16s (map (Z_to_bv 64) norm)) = 2 * zlen norm) by (rewrite u16s_length, length_map; lia);
    assert (LBA4 : zlen (u32s (map (Z_to_bv 64) (kind_base k))) = 4 * (kind_max k + 1)) by (rewrite u32s_length, length_map; lia);
    assert (LBI1 : zlen (map (Z_to_bv 8) (kind_bits k)) = kind_max k + 1) by (rewrite length_map; lia);
    try match goal with H : 0 <= kind_max k <= 52 |- _ => clear H end; pose proof (kind_max_range k) as KM.
  Local Ltac bf_open I :=
    open_hy HY; open_bf I; unfold KHIGH in *; bf_reunp;
    pose proof (bf_bands _ _ _ _ _ _ _ _ _ _ _ _ _ HY) as (BDT & BW & BSP & B5 & B6 & B7 & B8);
    hide_all_disj;
    pose proof (bfA_size_rng _ _ _ _ _ _ _ _ _ _ _ _ _ HY) as (SZ & LLR & LL2);
    bf_consts; bf_lens.
  (* [comment removed for export] *)
  Local Ltac bf_reopen I :=
    repeat match goal with
           | H : rw_cells _ _ _ _ |- _ => clear H | H : u8arr _ _ _ _ |- _ => clear H | H : bytes_at _ _ _ _ |- _ => clear H
           | H : stk _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H
           | H : wmono _ _ _ |- _ => clear H | H : Z.of_nat (length _) = _ |- _ => clear H | H : Forall _ _ |- _ => clear H
           | H : list byte |- _ => clear H
           end;
    open_bf I; bf_reunp; bf_consts; bf_lens.
  (* [comment removed for export] *)
  Notation KZB := [KZRange SPV (0x10007fff8000 + 176) (2^47); KZRange maxSV 0 52; KZRange tl 5 9; KZRange (2^tl) 32 512; KZRange (2^(tl - 1)) 16 256;
     KZRange NC 4096 (2^47); KZRange DT 4096 (2^47); KZRange W 4096 (2^47); KZRange BASE 4096 (2^47 - 212); KZRange BITS 4096 (2^47 - 53);
     KZRange wlen 626 (2^47); KZRange (zlen norm) 1 (2^46); KZRange (kind_max k) 0 52;
     KZRange (NC + 2 * zlen norm) 0 (2^47); KZRange (W + wlen) 0 (2^47 - 8); KZRange (DT + 8 + 8 * 2^tl) 0 (2^47 - 8);
     KZAlign DT 4; KZAlign W 2; KZAlign NC 2; KZAlign BASE 4] (only parsing).
  Variable t : seq_table.
  Notation POST := (bfA_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W wlen tl lo m t).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -144)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Notation ST1 pc mm high s fast xa0 xa1 xa5 x5 x31 :=
    (ST pc mm ra x5 (Z_to_bv 64 2147450880) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 high) (Z_to_bv 64 fast)
        xa0 xa1 (Z_to_bv 64 (NC + 2 * s)) (Z_to_bv 64 BASE) (Z_to_bv 64 BITS) xa5 (Z_to_bv 64 W) (Z_to_bv 64 (W + 2 * s))
        (Z_to_bv 64 s) (Z_to_bv 64 (2^(tl - 1))) (Z_to_bv 64 65535) (Z_to_bv 64 (NC + 2 * s)) (Z_to_bv 64 (W + 2 * s)) (Z_to_bv 64 (maxSV + 1 - s)) (Z_to_bv 64 NC) (Z_to_bv 64 (maxSV + 1))
        s10 s11 (Z_to_bv 64 (DT + 8)) (Z_to_bv 64 (2^tl + -1)) (Z_to_bv 64 (W + 106)) x31).
  (* [comment removed for export] *)
  Notation ST1X pc mm high s fast xa0 xa1 xa5 x5 x31 := (ST1 pc mm high s fast xa0 xa1 xa5 x5 x31) (only parsing).

  (* [comment removed for export] *)
  Lemma bf_p1_bodyA : forall m1 h0 h1 w0 w8 w16 w24 s cells sn sp high fast xa0 xa1 xa5 x5 x31,
    BFm h0 h1 w0 w8 w16 w24 cells sn sp m1 -> 0 <= s <= maxSV -> 0 <= fast <= 1 ->
    2^tl - 1 - high = pws norm s - nsum norm s ->
    (forall m2 c1 n1 h1' f1 ya0 ya1 ya5 y5 y31, p1_step norm tl s (cells, sn, high, fast) = (c1, n1, h1', f1) -> s + 1 < maxSV + 1 ->
       BFm h0 h1 w0 w8 w16 w24 c1 n1 sp m2 -> 0 <= f1 <= 1 ->
       evtF bsegs RNG POST (ST1 0x88150 m2 h1' (s + 1) f1 ya0 ya1 ya5 y5 y31)) ->
    (forall m2 c1 n1 h1' f1 ya0 ya1 ya5 y5 y31, p1_step norm tl s (cells, sn, high, fast) = (c1, n1, h1', f1) -> s + 1 = maxSV + 1 ->
       BFm h0 h1 w0 w8 w16 w24 c1 n1 sp m2 -> 0 <= f1 <= 1 ->
       evtF bsegs RNG POST (ST1X 0x88224 m2 h1' (maxSV + 1) f1 ya0 ya1 ya5 y5 y31)) ->
    evtF bsegs RNG POST (ST1 0x88150 m1 high s fast xa0 xa1 xa5 x5 x31).
  Proof.
    intros until x31; intros I HS HFA HH KH KE. bf_open I.
    assert (NR : -1 <= Znth s norm <= 2^tl).
    { pose proof (NGE s ltac:(lia)). pose proof (count_le_size norm maxSV tl TLR NLEN NGE NSUM s ltac:(lia)) as CL.
      unfold weight in CL. destruct (Z.eqb_spec (Znth s norm) (-1)); lia. }
    (* [comment removed for export] *)
    kx_autoFLAc (FR, HDR) [KAUnp (NC + 2 * s) 2] [0x88168; 0x88190] 20%nat
      (KZB ++ [KZRange s 0 52; KZRange (NC + 2 * s) 4096 (2^47 - 2); KZRange (2 * zlen norm - 2 * s) 2 (2^47)])
      [(NC + 2 * s, 2)] [(NC + 2 * s, 2)].
    all: try kx_z. all: try kx_acc RNC. all: try kx_acc RSTK.
    all: kx_the_read RD.
    all: rewrite (rdval_u16Z bsegs m1 NC norm s _ NCB) in RD by lia.
    - (* [comment removed for export] *)
      assert (NM1 : Znth s norm = -1).
      { rewrite RD, Z_to_bv_unsigned in KXBR. unfold bv_wrap, bv_modulus in KXBR. change (2 ^ Z.of_N 64) with (2^64) in KXBR.
        clear - KXBR NR SZ. Z.div_mod_to_equations. lia. }
      assert (PS : p1_step norm tl s (cells, sn, high, fast) = (set_base high s cells, Zupd s 1 sn, high + -1, fast)).
      { cbn [p1_step]. rewrite NM1. reflexivity. }
      assert (HHI : 0 <= high <= 2^tl - 1).
      { pose proof (low_step norm maxSV tl TLR NLEN NGE s ltac:(lia)) as LS. rewrite NM1 in LS. cbn in LS.
        pose proof (low_mono norm maxSV tl TLR NLEN NGE (s + 1) (maxSV + 1) ltac:(lia) ltac:(lia)) as LM.
        pose proof (low_mono norm maxSV tl TLR NLEN NGE 0 s ltac:(lia) ltac:(lia)) as LM0.
        pose proof (nsum_nonneg norm maxSV tl TLR NLEN (maxSV + 1) ltac:(lia)) as NN.
        change (pws norm 0) with 0 in LM0. change (nsum norm 0) with 0 in LM0.
        unfold pws in *. rewrite NSUM in LM. clear - LS LM LM0 NN HH HS. lia. }
      clear RD. kx_tidy_run.
      bf_lens.
      kx_autoFLAc (FR, HDR) [KAUnp (DT + 8 + 8 * high + 4) 4; KAUnp (W + 2 * s) 2; KAApp (DT + 8 + 8 * high + 4) 4; KAApp (W + 2 * s) 2]
        [0x88150; 0x88224] 40%nat
        (KZB ++ [KZRange s 0 52; KZRange high 0 511; KZRange (2^tl - high) 1 512; KZRange (maxSV - s) 0 52;
         KZRange (W + 2 * s) 4096 (2^47 - 8); KZRange (DT + 8 + 8 * high + 4) 4096 (2^47 - 8); KZRange (8 * 2^tl - 8 * high) 8 4096;
         KZWr (DT + 8 + 8 * high + 4) 4; KZWr (W + 2 * s) 2;
         KZDisj (DT + 8 + 8 * high + 4) 4 NC (2 * zlen norm); KZDisj (W + 2 * s) 2 NC (2 * zlen norm);
         KZDisj (DT + 8 + 8 * high + 4) 4 (SPV - 144) 144; KZDisj (W + 2 * s) 2 (SPV - 144) 144;
         KZDisj (DT + 8 + 8 * high + 4) 4 W 106; KZDisj (DT + 8 + 8 * high + 4) 4 (W + 106) (wlen - 106);
         KZDisj (W + 2 * s) 2 (DT + 8) (8 * 2^tl); KZDisj (W + 2 * s) 2 DT 8; KZDisj (DT + 8 + 8 * high + 4) 4 DT 8;
         KZDisj (W + 2 * s) 2 (W + 106) (wlen - 106);
         KZDisj (DT + 8 + 8 * high + 4) 4 BASE (4 * (kind_max k + 1)); KZDisj (W + 2 * s) 2 BASE (4 * (kind_max k + 1));
         KZDisj (DT + 8 + 8 * high + 4) 4 BITS (kind_max k + 1); KZDisj (W + 2 * s) 2 BITS (kind_max k + 1)])
        (@nil (Z * Z)) [(DT + 8 + 8 * high + 4, 4); (W + 2 * s, 2)].
      all: try kx_z. all: try kx_acc RDT. all: try kx_acc RW. all: try kx_acc RSTK.
      all: kxk_keep CEL. all: kxk_keep_ix SNX [s]. all: kx_mem.
      all: kx_tidy_run.
      all: try kx_gen_regsF [5%nat; 11%nat; 31%nat].
      all: erewrite (sqb_base4 cells high s) in CEL by lia; change (1 mod 65536) with 1 in SNX.
      all: assert (CLEN' : zlen (set_base high s cells) = 2^tl) by (rewrite set_base_length2; exact CLEN);
           assert (SNLEN' : zlen (Zupd s 1 sn) = 53) by (rewrite Zupd_length2; exact SNLEN).
      all: kx_setreg 12 (NC + 2 * (s + 1)). all: kx_setreg 21 (NC + 2 * (s + 1)). all: kx_setreg 17 (W + 2 * (s + 1)). all: kx_setreg 22 (W + 2 * (s + 1)). all: kx_setreg 23 (maxSV + 1 - (s + 1)).
      + (* [comment removed for export] *)
        eapply KH; [exact PS | lia | close_bf | exact HFA].
      + (* [comment removed for export] *)
        replace (s + 1) with (maxSV + 1) by lia.
        eapply KE; [exact PS | lia | close_bf | exact HFA].
    - (* [comment removed for export] *)
      assert (NN : 0 <= Znth s norm).
      { rewrite RD, Z_to_bv_unsigned in KXBR. unfold bv_wrap, bv_modulus in KXBR. change (2 ^ Z.of_N 64) with (2^64) in KXBR.
        clear - KXBR NR SZ. Z.div_mod_to_equations. lia. }
      assert (PS : p1_step norm tl s (cells, sn, high, fast)
                   = (cells, Zupd s (Znth s norm mod 2^16) sn, high, if 2^(tl - 1) <=? Znth s norm then 0 else fast)).
      { cbn [p1_step]. destruct (Z.eqb_spec (Znth s norm) (-1)); [lia| reflexivity]. }
      rewrite RD. rewrite (Z.mod_small (Znth s norm) 65536) in * by lia. kx_abs. clear KXE KXA KXRD KXK KXBR RD.
      (* [comment removed for export] *)
      zstep. zstep. rewrite (sext16_shl48 (Znth s norm)) by lia.
      zstep. rewrite (slt_small (Znth s norm) (2^(tl - 1))) by lia.
      zstep. zstep. rewrite (neg_mask _ fast) by lia.   (* [comment removed for export] *)
      replace (if Znth s norm <? 2 ^ (tl - 1) then fast else 0) with (if 2 ^ (tl - 1) <=? Znth s norm then 0 else fast)
        by (destruct (Z.ltb_spec (Znth s norm) (2 ^ (tl - 1))); destruct (Z.leb_spec (2 ^ (tl - 1)) (Znth s norm)); lia).
      set (fast' := if 2 ^ (tl - 1) <=? Znth s norm then 0 else fast) in *.
      assert (HFA' : 0 <= fast' <= 1) by (subst fast'; destruct (2 ^ (tl - 1) <=? Znth s norm); lia).
      clearbody fast'.
      bf_lens.
      kx_autoFLAc (FR, HDR) [KAUnp (W + 2 * s) 2; KAApp (W + 2 * s) 2] [0x88150; 0x88224] 40%nat
        (KZB ++ [KZRange s 0 52; KZRange (maxSV - s) 0 52; KZRange (W + 2 * s) 4096 (2^47 - 8); KZRange (Znth s norm) 0 512;
         KZRange fast' 0 1;
         KZWr (W + 2 * s) 2; KZDisj (W + 2 * s) 2 NC (2 * zlen norm); KZDisj (W + 2 * s) 2 (SPV - 144) 144;
         KZDisj (W + 2 * s) 2 (DT + 8) (8 * 2^tl); KZDisj (W + 2 * s) 2 DT 8; KZDisj (W + 2 * s) 2 (W + 106) (wlen - 106);
         KZDisj (W + 2 * s) 2 BASE (4 * (kind_max k + 1)); KZDisj (W + 2 * s) 2 BITS (kind_max k + 1)])
        (@nil (Z * Z)) [(W + 2 * s, 2)].
      all: try kx_z. all: try kx_acc RW. all: try kx_acc RSTK.
      all: kxk_keep CEL. all: kxk_keep_ix SNX [s]. all: kx_mem.
      all: kx_tidy_run.
      all: assert (SNLEN' : zlen (Zupd s (Znth s norm mod 65536) sn) = 53) by (rewrite Zupd_length2; exact SNLEN).
      all: kx_setreg 12 (NC + 2 * (s + 1)). all: kx_setreg 21 (NC + 2 * (s + 1)). all: kx_setreg 17 (W + 2 * (s + 1)). all: kx_setreg 22 (W + 2 * (s + 1)). all: kx_setreg 23 (maxSV + 1 - (s + 1)).
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x88150) _ _ _ _) =>   (* [comment removed for export] *)
               eapply KH; [exact PS | lia | close_bf | exact HFA']
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x88224) _ _ _ _) =>   (* [comment removed for export] *)
               replace (s + 1) with (maxSV + 1) by lia;
               eapply KE; [exact PS | lia | close_bf | exact HFA']
           end.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_p1_loopA : forall (f : nat) m1 h0 h1 w0 w8 w16 w24 s cells sn sp high fast xa0 xa1 xa5 x5 x31,
    BFm h0 h1 w0 w8 w16 w24 cells sn sp m1 -> 0 <= s -> s + Z.of_nat (S f) = maxSV + 1 -> 0 <= fast <= 1 ->
    2^tl - 1 - high = pws norm s - nsum norm s ->
    (forall m2 cells' sn' high' fast' ya0 ya1 ya5 y5 y31,
       lowprob (S f) norm (2^(tl - 1)) s cells sn high fast = (cells', sn', high', fast') ->
       BFm h0 h1 w0 w8 w16 w24 cells' sn' sp m2 -> 0 <= fast' <= 1 ->
       evtF bsegs RNG POST (ST1X 0x88224 m2 high' (maxSV + 1) fast' ya0 ya1 ya5 y5 y31)) ->
    evtF bsegs RNG POST (ST1 0x88150 m1 high s fast xa0 xa1 xa5 x5 x31).
  Proof.
    induction f as [|f IH]; intros until x31; intros I HS HSF HFA HH KONT.
    - eapply bf_p1_bodyA; [exact I | lia | exact HFA | exact HH | intros; exfalso; lia |].
      intros m2 c1 n1 h1' f1 ya0 ya1 ya5 y5 y31 PS _ I2 HF1.
      eapply KONT; [| exact I2 | exact HF1]. rewrite lowprob_S, PS. reflexivity.
    - eapply bf_p1_bodyA; [exact I | lia | exact HFA | exact HH | | intros; exfalso; lia].
      intros m2 c1 n1 h1' f1 ya0 ya1 ya5 y5 y31 PS LT I2 HF1.
      eapply (IH m2 h0 h1 w0 w8 w16 w24 (s + 1)); [exact I2 | lia | lia | exact HF1 | |].
      + open_hy HY. rewrite (low_step norm maxSV tl TLR NLEN NGE s) by lia.
        unfold p1_step in PS. destruct (Znth s norm =? -1); injection PS; intros; subst; lia.
      + intros m3 cells' sn' high' fast' za0 za1 za5 z5 z31 LP I3 HF3.
        eapply KONT; [| exact I3 | exact HF3]. rewrite lowprob_S, PS. exact LP.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_p1_0A : forall (f : nat) m1 h0 h1 w0 w8 w16 w24 cells sn sp high fast xa0 xa1 xa5 x5 x31,
    BFm h0 h1 w0 w8 w16 w24 cells sn sp m1 -> Z.of_nat (S f) = maxSV + 1 -> 0 <= fast <= 1 -> high = 2^tl - 1 ->
    (forall m2 cells' sn' high' fast' ya0 ya1 ya5 y5 y31,
       lowprob (S f) norm (2^(tl - 1)) 0 cells sn high fast = (cells', sn', high', fast') ->
       BFm h0 h1 w0 w8 w16 w24 cells' sn' sp m2 -> 0 <= fast' <= 1 ->
       evtF bsegs RNG POST (ST1X 0x88224 m2 high' (maxSV + 1) fast' ya0 ya1 ya5 y5 y31)) ->
    evtF bsegs RNG POST (ST1 0x88150 m1 high 0 fast xa0 xa1 xa5 x5 x31).
  Proof.
    intros until x31; intros I HF HFA HH KONT.
    pose proof (bf_p1_loopA f m1 h0 h1 w0 w8 w16 w24 0 cells sn sp high fast xa0 xa1 xa5 x5 x31) as L.
    apply L; [exact I | lia | lia | exact HFA | change (pws norm 0) with 0; change (nsum norm 0) with 0; lia | exact KONT].
  Qed.
End P1.
End CANSEC1.
