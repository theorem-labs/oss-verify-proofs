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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdHufW ZdHufWM ZdHufWX SepHide.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_bdt_defs AZ_hft_bdt_p1 AZ_hft_bdt_p2 AZ_hft_bdt_p2a AZ_hft_bdt_p2c AZ_hft_bdt_p3.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

(* [comment removed for export] *)
Lemma le2_of_bytes : forall bs : list byte, length bs = 2%nat -> le2 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le2, le_bytes_to_word.
  pose proof (le_val_range _ (bytes_ok_map bs)) as HR. rewrite length_map, HL in HR.
  change (256 ^ Z.of_nat 2) with 65536 in HR. rewrite <- bytes_le_to_Z_le_val in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.
Lemma cb2_as_c2 : forall segs m A pre j post,
  rw_cells segs m A (pre ++ CB 2 j :: post) -> exists w, rw_cells segs m A (pre ++ C2 w :: post).
Proof.
  intros segs m A pre j post H. exists (le_bytes_to_word j).
  pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [WF1 [WFJ WF2]]. cbn in WFJ.
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact WF1|]. split; [exact I| exact WF2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite le2_of_bytes by exact WFJ. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hdr_wordA : forall tl fast, 5 <= tl <= 9 -> 0 <= fast <= 1 ->
  le4 (Z_to_bv 64 (65536 * fast + tl)) = le2 (Z_to_bv 64 tl) ++ le2 (Z_to_bv 64 fast).
Proof.
  intros tl fast Ht Hf.
  assert (C : (tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9) /\ (fast = 0 \/ fast = 1)) by lia.
  destruct C as ([E|[E|[E|[E|E]]]] & [E2|E2]); subst tl fast; unfold le4, le2; cbn [Z_to_le_bytes app];
    repeat (f_equal; try (apply bv_eq; vm_compute; reflexivity)).
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section G.
  Variables (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem)
            (SPV lo DT NC W wlen maxSV tl : Z) (norm : list Z).
  Hypothesis HY : bdA_hyps RNG SPV lo DT NC W wlen maxSV tl norm.
  Hypothesis UDT : unpoisoned m DT (DT + 4 + 4 * 2^tl).
  Hypothesis UW : unpoisoned m W (W + wlen).
  Hypothesis UNC : unpoisoned m NC (NC + 2 * zlen norm).
  Hypothesis ART0 : art m.
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
    (MS (mkR xra (Z_to_bv 64 (SPV + -192)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation HIGH := (hhigh norm maxSV tl).

  (* [comment removed for export] *)
  Lemma bd_after1A : forall f8 f16 m1 h0 h1 tb sn sp high fast yt0 yt1 ya0 ya3 ya4 ya5 yt5 yt6,
    BDg f8 f16 h0 h1 tb sn sp m1 -> p1_inv norm maxSV tl (maxSV + 1) tb sn high fast ->
    evtF bsegs RNG POST
      (ST 0xaf378 m1 ra yt0 yt1 (Z_to_bv 64 2147450880) s0 (Z_to_bv 64 (maxSV + 1))
          ya0 (Z_to_bv 64 (-1 * NC + -1)) (Z_to_bv 64 maxSV) ya3 ya4 ya5 (Z_to_bv 64 high) (Z_to_bv 64 (DT + 4))
          (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 1) (Z_to_bv 64 fast) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (2^(tl + -1))) (Z_to_bv 64 65535)
          s10 s11 (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (2^tl + -1)) yt5 yt6).
  Proof.
    intros until yt6; intros I P1. bd_open I.
    destruct (p2_init norm maxSV tl TLR MSVR NLEN NGE NSUM tb sn high fast P1) as (EH & P2).
    pose proof (hhigh_range norm maxSV tl TLR ltac:(lia) NLEN NGE NSUM) as HR.
    assert (FASTR : 0 <= fast <= 1) by (destruct P1 as (_ & _ & _ & _ & _ & FR1 & _); exact FR1).
    (* [comment removed for export] *)
    assert (HDR4 : rw_cells bsegs m1 DT [C4 (le_bytes_to_word (le2 h0 ++ le2 h1))]).
    { eapply rw_cells_recell; [exact HDR | cbn; split; exact Logic.I |].
      cbn [cells_bytes cbytes app]. rewrite app_nil_r.
      pose proof (le_val_range _ (bytes_ok_map (le2 h0 ++ le2 h1))) as HR4. rewrite length_map, length_app, !length_le2 in HR4.
      change (256 ^ Z.of_nat (2 + 2)) with 4294967296 in HR4. rewrite <- bytes_le_to_Z_le_val in HR4.
      unfold le4, le_bytes_to_word. rewrite unsigned_lit by lia.
      change 4%nat with (length (le2 h0 ++ le2 h1)) at 1. rewrite Z_to_le_bytes_to_Z. reflexivity. }
    clear HDR.
    kx_autoFLAc (FR, HDR4) [KAUnp DT 4; KAApp DT 4; KAApp (SPV - 192) 192] [0xaf3b8; 0xaf578] 40%nat
      (KZB ++ [KZRange fast 0 1; KZRange DT 4096 (2^47 - 8);
               KZWr DT 4; KZDisj DT 4 NC (2 * zlen norm); KZDisj DT 4 (SPV - 192) 192; KZDisj DT 4 W wlen; KZDisj DT 4 (DT + 4) (4 * 2^tl);
               KZDisj DT 4 W (2 * (maxSV + 1)); KZDisj DT 4 (W + 2 * (maxSV + 1)) (wlen - 2 * (maxSV + 1))])
      [(SPV - 192, 192)] [(SPV - 192, 192); (DT, 4)].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xaf8fc) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: try kx_z. all: try kx_acc RSTK. all: try kx_acc RDT.
    all: try (kx_side_pre; unfold hidden in BDT; Z.div_mod_to_equations; lia).
    all: kx_mem. all: kx_tidy_run. all: bd_reunp.
    all: kx_gen_regsF [14%nat; 21%nat].
    (* [comment removed for export] *)
    all: lazymatch goal with H4 : rw_cells _ ?mx DT [C4 (Z_to_bv 64 ?v)] |- _ =>
           assert (HDR : rw_cells bsegs mx DT [C2 (Z_to_bv 64 tl); C2 (Z_to_bv 64 fast)]);
           [ eapply rw_cells_recell; [exact H4 | cbn; repeat split |];
             cbn [cells_bytes cbytes app]; rewrite app_nil_r; symmetry;
             replace v with (65536 * fast + tl) by lia;
             apply hdr_wordA; lia
           | clear H4 ] end.
    all: rewrite ?(Z.mod_small (2^tl) (2^64)) by lia.
    all: rewrite ?(srliw_val (2^tl) 1), ?(srliw_val (2^tl) 3) by lia; rewrite ?(Z.mod_small (2^tl) 4294967296) by lia.
    all: change (2^1) with 2; change (2^3) with 8.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xaf578) _ _ _ _) =>   (* [comment removed for export] *)
             subst high;
             eapply (bd_slowA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UDT UW UNC f8 f16 _ tb sn sp fast);
             [close_bd | exact P2 | intros; eapply (bd_p3_entryA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UDT UW UNC); eassumption]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xaf3b8) _ _ _ _) =>   (* [comment removed for export] *)
             assert (NOLOW : HIGH = 2^tl - 1) by lia;
             replace (Z_to_bv 64 high) with (Z_to_bv 64 HIGH) by (f_equal; lia);
             eapply (bd_fastA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UDT UW UNC NOLOW f8 f16 _ tb sn sp fast);
             [close_bd | subst high; exact P2 | intros; eapply (bd_p3_entryA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UDT UW UNC); eassumption]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_mainA : forall m1 j0 j8 j16 j56 j64 x6 x7 x28 x29 x30 x31,
    munch [(DT, DT + 4 + 4 * 2^tl); (W, W + wlen); (SPV - 192, SPV)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
    stk bsegs m1 lo (SPV + -192) -> stk bsegs m1 DT (DT + 4 + 4 * 2^tl) -> stk bsegs m1 W (W + wlen) ->
    bytes_at bsegs m1 NC (u16s (map (Z_to_bv 64) norm)) ->
    rw_cells bsegs m1 (SPV + -192) [CB 8 j0; CB 8 j8; CB 8 j16; C8 (Z_to_bv 64 (2 * maxSV + W + 2)); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (2 * maxSV + W)); C8 (Z_to_bv 64 tl);
                                    CB 8 j56; CB 8 j64; C8 (Z_to_bv 64 NC); C8 (Z_to_bv 64 W);
                                    C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    evtF bsegs RNG POST
      (ST 0xaf20c m1 ra (Z_to_bv 64 (2^tl)) x6 x7 s0 (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 (4294967296 * maxSV + 4294967296)) (Z_to_bv 64 tl)
          (Z_to_bv 64 maxSV) (Z_to_bv 64 1) (Z_to_bv 64 831992) (Z_to_bv 64 (tl + -1)) (Z_to_bv 64 18446744073709551570) (Z_to_bv 64 (DT + 4))
          (Z_to_bv 64 0) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31).
  Proof.
    intros until x31; intros MU WM MI STK DTS WS NCB FR.
    pose proof (bd_artM _ _ _ _ _ _ _ _ _ _ _ HY ART0 m1 MU WM) as ART1. destruct ART1 as (GOT & RIC & SHB & INI & LAY & REAL).
    open_hy HY. unfold KHIGH in *. pose proof (bd_bands _ _ _ _ _ _ _ _ _ _ HY) as (BDT & BW & BSP & B5 & B6 & B7 & B8). hide_all_disj.
    pose proof (bdA_size_rng _ _ _ _ _ _ _ _ _ _ HY) as (SZ & LLR & LL2).
    assert (LNC : zlen (u16s (map (Z_to_bv 64) norm)) = 2 * zlen norm) by (rewrite u16s_length, length_map; lia).
    (* [comment removed for export] *)
    zstep. rewrite (sllw_pow2 tl) by lia.
    (* [comment removed for export] *)
    kx_autoFLAc (FR, GOT, SHB) [KAApp (SPV - 192) 192] [0xaf240] 20%nat (KZB ++ [KZWr (SPV - 192) 192; KZDisj (SPV - 192) 192 NC (2 * zlen norm)])
      [(SPV - 192, 192)] [(SPV - 192, 192)].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xaf8fc) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: try kx_cell_lit. all: try kx_z. all: try kx_acc RSTK. all: try kx_acc RI.
    all: kx_mem. all: kx_tidy_run.
    (* [comment removed for export] *)
    zstep. rewrite (sllw_pow2 (tl + -1)) by lia.
    (* [comment removed for export] *)
    kx_autoFLAc (FR, GOT, SHB) [KAApp (SPV - 192) 192] [0xaf280] 20%nat (KZB ++ [KZWr (SPV - 192) 192; KZDisj (SPV - 192) 192 NC (2 * zlen norm)])
      [(SPV - 192, 192)] [(SPV - 192, 192)].
    all: try kx_cell_lit. all: try kx_z. all: try kx_acc RSTK. all: try kx_acc RI.
    all: kx_mem. all: kx_tidy_run.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    destruct (stk_open bsegs _ DT (DT + 4 + 4 * 2^tl) DT (Z.to_nat (4 + 4 * 2^tl)) DTS ltac:(lia) ltac:(lia)) as (jd & DTC & _ & _).
    assert (LJD : length jd = Z.to_nat (4 + 4 * 2^tl)) by (destruct DTC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; exact LJ).
    apply u8arr_of_rw_cells in DTC.
    rewrite <- (firstn_skipn 4 jd) in DTC. apply u8arr_app in DTC. destruct DTC as [HDRU CELU].
    assert (LH : length (firstn 4 jd) = 4%nat) by (rewrite firstn_length; lia).
    rewrite LH in CELU. change (Z.of_nat 4) with 4 in CELU.
    apply rw_cells_of_u8arr in HDRU. rewrite LH in HDRU.
    apply (rw_cells_split_CB bsegs _ _ [] 4 _ [] [2; 2]%nat) in HDRU; [| reflexivity]. cbn [mk_CB_cells app] in HDRU.
    lazymatch type of HDRU with rw_cells _ _ _ (CB 2 ?j :: ?post) => destruct (cb2_as_c2 bsegs _ _ [] j post HDRU) as [h0 HDR1] end. cbn [app] in HDR1. clear HDRU.
    lazymatch type of HDR1 with rw_cells _ _ _ (?c0 :: CB 2 ?j :: ?post) => destruct (cb2_as_c2 bsegs _ _ [c0] j post HDR1) as [h1 HDR] end. cbn [app] in HDR. clear HDR1.
    rewrite <- (bytes_of_unsigned (skipn 4 jd)) in CELU.
    set (tb0 := map bv_unsigned (skipn 4 jd)) in *.
    assert (CLEN : zlen tb0 = 4 * 2^tl) by (unfold tb0; rewrite length_map, length_skipn; lia).
    assert (CBY : Forall isbyte tb0) by (apply bytes_unsigned_range).
    (* [comment removed for export] *)
    destruct (stk_open bsegs _ W (W + wlen) W (Z.to_nat wlen) WS ltac:(lia) ltac:(lia)) as (jw & WC & _ & _).
    assert (LJW : length jw = Z.to_nat wlen) by (destruct WC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; exact LJ).
    apply u8arr_of_rw_cells in WC.
    rewrite <- (firstn_skipn (2 * Z.to_nat (maxSV + 1)) jw) in WC. apply u8arr_app in WC. destruct WC as [SNU SPU].
    assert (LS : length (firstn (2 * Z.to_nat (maxSV + 1)) jw) = (2 * Z.to_nat (maxSV + 1))%nat) by (rewrite firstn_length; lia).
    rewrite LS in SPU. replace (W + Z.of_nat (2 * Z.to_nat (maxSV + 1))) with (W + 2 * (maxSV + 1)) in SPU by lia.
    destruct (u16s_of_bytes (Z.to_nat (maxSV + 1)) _ LS) as (sn0 & LN0 & _ & EN0). rewrite EN0 in SNU.
    rewrite <- (bytes_of_unsigned (skipn (2 * Z.to_nat (maxSV + 1)) jw)) in SPU.
    set (sp0 := map bv_unsigned (skipn (2 * Z.to_nat (maxSV + 1)) jw)) in *.
    assert (SPLEN : zlen sp0 = wlen - 2 * (maxSV + 1)) by (unfold sp0; rewrite length_map, length_skipn; lia).
    assert (SPBY : Forall isbyte sp0) by (apply bytes_unsigned_range).
    assert (SNLEN : zlen sn0 = maxSV + 1) by lia.
    clear DTS WS EN0 LS LJW LJD LH.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells _ _ (SPV + -192) (?c0 :: CB 8 ?a :: ?post) |- _ =>
      destruct (cb8_as_c8 bsegs _ _ [c0] a post FRx) as [w8 FR1]; cbn [app] in FR1; clear FRx end.
    lazymatch goal with FRx : rw_cells _ _ (SPV + -192) (?c0 :: ?c1 :: CB 8 ?a :: ?post) |- _ =>
      destruct (cb8_as_c8 bsegs _ _ [c0; c1] a post FRx) as [w16 FR2]; cbn [app] in FR2; clear FRx end.
    lazymatch goal with FRx : rw_cells _ _ (SPV + -192) (_ :: _ :: _ :: C8 (Z_to_bv 64 ?a) :: _ :: C8 (Z_to_bv 64 ?b) :: _ :: C8 (Z_to_bv 64 ?c) :: C8 (Z_to_bv 64 ?d) :: _) |- _ =>
      replace a with (W + 2 * (maxSV + 1)) in FRx by lia; replace b with (W + 2 * maxSV) in FRx by lia;
      try (replace c with (2^tl) in FRx by lia); replace d with (-1 * W + -1) in FRx by lia end.
    assert (I : BDg w8 w16 h0 h1 tb0 sn0 sp0 m5) by close_bd.
    eapply (bd_p1_0A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY UDT UW UNC w8 w16 (Z.to_nat maxSV) m5 h0 h1 tb0 sn0 sp0 (2^tl + -1) 1); [exact I | | lia |].
    - replace (2^tl + -1) with (2^tl - 1) by lia.
      apply (p1_init norm maxSV tl TLR MSVR NLEN NGE NSUM); unfold FseNCount.Zlength; assumption.
    - intros m6 tb' sn' high' fast' yt0 yt1 ya0 ya3 ya4 ya5 yt5 yt6 I2 P1'.
      eapply (bd_after1A w8 w16 _ _ _ tb' sn' sp0); [exact I2 | exact P1'].
  Qed.
End G.

(* [comment removed for export] *)
Ltac conj_spine := first [ simple apply conj; [ | conj_spine ] | idtac ].

(* [comment removed for export] *)
Theorem fse_bdt_proofA : fse_bdt_stmtA.
Proof.
  unfold fse_bdt_stmtA, APFSE_BDT. intros until norm.
  intros ADT AW ANC ART AST MI STK LO0 LOS SPR DT4 W2 NC2 DTS DTL DTH WS WL WLEN WH NCB NCL NCH TLR MSVR NLEN NGE NSUM OFFDT OFFW OFFNC DTW DTNC WNC.
  assert (SZ : 32 <= 2^tl <= 512).
  { assert (2^5 <= 2^tl) by (apply Z.pow_le_mono_r; lia). assert (2^tl <= 2^9) by (apply Z.pow_le_mono_r; lia).
    change (2^5) with 32 in *. change (2^9) with 512 in *. lia. }
  pose proof ART as ART0. destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
  destruct (ADT ltac:(lia)) as (ABDT & UDT & RDT & RSDT). clear ADT.
  replace (DT + (4 + 4 * 2^tl)) with (DT + 4 + 4 * 2^tl) in * by lia.
  destruct ANC as (UNC & RNC & RSNC).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  assert (MU : munch [(DT, DT + 4 + 4 * 2^tl); (W, W + wlen); (SPV - 192, SPV)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  assert (LNC : zlen (u16s (map (Z_to_bv 64) norm)) = 2 * zlen norm) by (rewrite u16s_length, length_map; lia).
  carve_frame 192%nat STK.
  apply (rw_cells_split_CB bsegs _ _ [] 192 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  (* [comment removed for export] *)
  kx_autoFLAc FR [KAApp (SPV - 192) 192] [0xaf1c0] 60%nat
    [KZRange SPV (0x10007fff8000 + 192) (2^47); KZRange maxSV 0 255; KZRange (zlen norm) 1 (2^46); KZRange NC 4096 (2^47); KZRange (NC + 2 * zlen norm) 0 (2^47);
     KZRange W 4096 (2^47); KZRange wlen 0 (2^32); KZRange (W + wlen) 0 (2^47); KZRange DT 4096 (2^47); KZRange tl 5 9; KZAlign DT 4; KZAlign W 2; KZAlign NC 2;
     KZWr (SPV - 192) 192; KZDisj (SPV - 192) 192 NC (2 * zlen norm)]
    [(SPV - 192, 192)] [(SPV - 192, 192)].
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xaf8fc) _ _ _ _) => kx_trap_fast | _ => idtac end.
  all: try kx_cell_lit. all: try kx_z. all: try kx_acc RSTK. all: try kx_acc RI.
  all: kx_mem. all: kx_tidy_run.
  zstep. replace (1 ≪ (tl mod 64)) with (2^tl) by (rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
  (* [comment removed for export] *)
  kx_autoFLAc FR [KAApp (SPV - 192) 192] [0xaf20c] 60%nat
    [KZRange SPV (0x10007fff8000 + 192) (2^47); KZRange maxSV 0 255; KZRange tl 5 9; KZRange (2^tl) 32 512; KZRange wlen 0 (2^32);
     KZRange (zlen norm) 1 (2^46); KZRange NC 4096 (2^47); KZRange (NC + 2 * zlen norm) 0 (2^47); KZRange W 4096 (2^47); KZRange (W + wlen) 0 (2^47); KZRange DT 4096 (2^47);
     KZAlign DT 4; KZAlign W 2; KZAlign NC 2;
     KZWr (SPV - 192) 192; KZDisj (SPV - 192) 192 NC (2 * zlen norm)]
    [(SPV - 192, 192)] [(SPV - 192, 192)].
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xaf8fc) _ _ _ _) => kx_trap_fast | _ => idtac end.
  all: try kx_cell_lit. all: try kx_z. all: try kx_acc RSTK. all: try kx_acc RI.
  all: kx_mem. all: kx_tidy_run.
  all: lazymatch goal with
       | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xaf8f8) _ _ ?mx _) =>     (* [comment removed for export] *)
           zstep; release_frame FR STK SPV;
           apply evtF_done; unfold fse_bdt_postA;
           do 14 eexists; exists mx, 18446744073709551570;
           split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|];
           split; [exact STK|]; split; [exact WS|]; split; [lia|]; right; split; [reflexivity| exact DTS]
       | |- _ => idtac
       end.
  (* [comment removed for export] *)
  destruct (AW ltac:(lia)) as (ABW & UW & RW & RSW). clear AW.
  assert (HY : bdA_hyps RNG SPV lo DT NC W wlen maxSV tl norm).
  { unfold bdA_hyps, pws. conj_spine. all: first [assumption | lia | unfold KHIGH; lia]. }
  lazymatch goal with
  | FRq : rw_cells _ ?mx (SPV + -192) (CB 8 ?j0 :: CB 8 ?j8 :: CB 8 ?j16 :: _ :: _ :: _ :: _ :: CB 8 ?j56 :: CB 8 ?j64 :: _) |- _ =>
      eapply (bd_mainA RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DT NC W wlen maxSV tl norm HY UDT UW UNC ART0 mx j0 j8 j16 j56 j64);
      [exact MU | exact WM | assumption | exact STK | exact DTS | exact WS | exact NCB | exact FRq]
  end.
Qed.
End CANSEC1.
