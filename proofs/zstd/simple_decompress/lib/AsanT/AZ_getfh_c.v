(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit ZdFrameW ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_frame_iface AZ_libc_iface AZ_kx AZ_getfh_a.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
(* [comment removed for export] *)
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation zlen l := (Z.of_nat (length l)).
Notation FB0 F := (mkABlock (ABFake 0) F 64).
Notation SHB := 2147450880.

Section CANSEC1. Context {rc : runConstT}.
Section GF.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Hypothesis FRL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
            (m0 m2 m3 : amem) (SPV SPA ZFH SRC : Z) (src : list Z) (off size lo FF SHF FLG : Z) (jF : list byte).
  (* [comment removed for export] *)
  Hypothesis OK : all_bytes src.
  Hypothesis OFF0 : 0 <= off.
  Hypothesis N5 : 5 <= size.
  Hypothesis OFS : off + size <= zlen src.
  Hypothesis Z8 : ZFH mod 8 = 0.
  (* [comment removed for export] *)
  Hypothesis G_lo : ATOP + 4096 <= lo /\ lo <= SPA - 2208 /\ SPV - 144 <= SPA <= SPV - 128 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0.
  Hypothesis G_zfh : ablk ZFH (ZFH + 48) /\ (ZFH + 48 <= lo \/ SPV <= ZFH).
  Hypothesis G_src : ablk SRC (SRC + zlen src) /\ (SRC + zlen src <= lo \/ SPV <= SRC) /\ (ZFH + 48 <= SRC \/ SRC + zlen src <= ZFH).
  Hypothesis G_ff : ablk FF (FF + 64) /\ FF mod 64 = 0 /\ FF + 64 <= ATOP /\ SHF = shad FF /\ al_fake L <= FF /\ FF + 64 <= al_fake L + FAKESZ
                    /\ (ZFH + 48 <= FF \/ FF + 64 <= ZFH) /\ (SRC + zlen src <= FF \/ FF + 64 <= SRC).
  Hypothesis G_flg : FLG = fflag L 0 FF /\ ablk FLG (FLG + 1) /\ FLG + 1 <= ATOP /\ (al_fake L <= FLG /\ FLG + 1 <= al_fake L + FAKESZ)
                     /\ (forall b, In b (FB0 FF :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG)
                     /\ (ZFH + 48 <= FLG \/ FLG + 1 <= ZFH).
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis R_src : rng RNG SRC (zlen src) /\ rng RNG (shad SRC) (shspan SRC (zlen src)).
  Hypothesis R_zfh : rng RNG ZFH 48 /\ rng RNG (shad ZFH) (shspan ZFH 48).
  Hypothesis R_ff : rng RNG FF 64 /\ rng RNG SHF 8 /\ rng RNG FLG 1.
  Hypothesis R_tbl : rng RNG 136800 32 /\ rng RNG (shad 136800) (shspan 136800 32) /\ rng RNG 136864 32 /\ rng RNG (shad 136864) (shspan 136864 32).
  (* [comment removed for export] *)
  Hypothesis LBH : ablkLB LB.
  Hypothesis AINZ : ainblk LB ZFH 48.
  Hypothesis AH2 : AHEAP AI L RNG st (FB0 FF :: LB) m2.
  Hypothesis FFR2 : ffr_pres [] LB m0 m2.
  Hypothesis MU23 : munch [(ZFH, ZFH + 48); (SPA - 2208, SPA + 32); (FF, FF + 24); (SHF, SHF + 8)] m2 m3.
  Hypothesis WM23 : wmono bsegs m2 m3.
  Hypothesis MU03 : munch ([(ZFH, ZFH + 48); (SPV - 4320, SPV)] ++ fake_area L) m0 m3.
  Hypothesis WM03 : wmono bsegs m0 m3.

  Notation WB := [(ZFH, ZFH + 48)].
  Notation WX := [(ZFH, ZFH + 48); (FF, FF + 8); (SHF, SHF + 8); (FLG, FLG + 1)].
  Notation POST := (zd_getfh_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV ZFH src off size lo m0).

  Notation fhd := (Znth (off + 4) src).
  Notation sseg := (fhd_singleSegment fhd).
  Notation dcode := (fhd_dictIDSizeCode fhd).
  Notation fcsid := (fhd_fcsID fhd).
  Notation P1 := (off + 5 + (if fhd_singleSegment fhd =? 0 then 1 else 0)).
  Notation P2 := (off + 5 + (if fhd_singleSegment fhd =? 0 then 1 else 0) + did_fieldSize (fhd_dictIDSizeCode fhd)).
  Notation DID := (fh_read_dictID src P1 dcode).
  Notation FCS := (fh_read_fcs src P2 fcsid sseg).
  Notation WS := (if fhd_singleSegment fhd =? 0 then wl_windowSize (Znth (off + 5) src) else FCS).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 FF) (Z_to_bv 64 ZFH) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 size) (Z_to_bv 64 0) (Z_to_bv 64 FF)
             (Z_to_bv 64 SHF) (Z_to_bv 64 SHB) (Z_to_bv 64 5) s11 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Notation XINV := (AZ_getfh_a.XINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m3 SPV SPA ZFH SRC src lo FF SHF FLG jF).
  Notation MINV := (AZ_getfh_a.MINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m3 SPV SPA ZFH SRC src lo FF SHF FLG jF).
  Notation MAINP := (AZ_getfh_a.MAINP src off size).
  Ltac xinv_i SAV FRA STL STG XF XS XL US UZ UT1 UT2 MU WM MI :=
    split; [exact SAV|]; split; [eexists; exact FRA|]; split; [exact STL|]; split; [exact STG|];
    split; [exact XF|]; split; [exact XS|]; split; [exact XL|]; split; [exact US|]; split; [exact UZ|];
    split; [exact UT1|]; split; [exact UT2|]; split; [exact MU|]; split; [exact WM| exact MI].
  Ltac xinv_e XI SAV jA FRA STL STG XF XS XL US UZ UT1 UT2 MU WM MI :=
    destruct XI as (SAV & [jA FRA] & STL & STG & XF & XS & XL & US & UZ & UT1 & UT2 & MU & WM & MI).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis PFCS : forall m1 ws0 (x1 x5 x6 x7 x10 x12 x17 x28 x29 x30 x31 : word),
    MAINP -> MINV m1 (Z0A (Z_to_bv 64 (fhd_header_size fhd))) -> (sseg = 0 -> ws0 = wl_windowSize (Znth (off + 5) src)) -> 0 <= ws0 < 18446744073709551616 ->
    evtF bsegs RNG POST (STpc 0x8384c m1 x1 x5 x6 x7 x10 (Z_to_bv 64 ws0) x12 (Z_to_bv 64 fhd) (Z_to_bv 64 (32 * sseg)) (Z_to_bv 64 (P2 - off))
                              (Z_to_bv 64 DID) x17 x28 x29 x30 x31).

  Ltac gf_src_hold :=
    repeat match goal with
    | H : rw_cells bsegs _ _ _ |- _ => fk_hold H
    | H : stk bsegs _ _ _ |- _ => fk_hold H
    | H : munch _ _ _ |- _ => fk_hold H
    | H : wmono bsegs _ _ |- _ => fk_hold H
    | H : unpoisoned _ ZFH _ |- _ => fk_hold H
    | H : unpoisoned _ 136800 _ |- _ => fk_hold H
    | H : unpoisoned _ 136864 _ |- _ => fk_hold H
    | H : rng RNG ZFH _ |- _ => fk_hold H
    | H : rng RNG (shad ZFH) _ |- _ => fk_hold H
    | H : _ \/ _ |- _ => fk_hold H
    | H : ffr_pres _ _ _ _ |- _ => fk_hold H
    | H : AHEAP _ _ _ _ _ _ |- _ => fk_hold H
    | H : ablk _ _ /\ _ |- _ => fk_hold H                 (* [comment removed for export] *)
    | H : _ = fflag _ _ _ /\ _ |- _ => fk_hold H          (* [comment removed for export] *)
    | H : ATOP + 4096 <= _ /\ _ |- _ => fk_hold H
    end.
  Ltac gf_unhold := unfold fk_held in *.
  (* [comment removed for export] *)
  Ltac gf_hold_all :=
    repeat match goal with H : ?T |- _ =>
      lazymatch T with
      | fk_held _ => fail
      | (0 <= Znth _ _ < 256)%Z => fail
      | bytes_at _ _ _ _ => fail
      | mem_inv _ _ => fail
      | (0 <= _ + _ /\ _ /\ _)%Z => fail
      | all_bytes _ => fail
      | rng _ _ _ => fail
      | (rng _ _ _ /\ _) => fail
      | unpoisoned _ _ _ => fail
      | stk _ _ _ _ => fail
      | _ => lazymatch type of T with Prop => fk_hold H end
      end
    end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac keep_byte_facts := repeat match goal with H : ?T |- _ => lazymatch T with (0 <= Znth _ _ < 256)%Z => fail | _ => clear H end end.
  Ltac lor2add_sideF := keep_byte_facts; first [ lia | split; lia | Z.div_mod_to_equations; lia ].
  Ltac lor2add1F x y :=
    first [ rewrite (lor_add_disj 8 x y) by lor2add_sideF | rewrite (lor_add_disj 16 x y) by lor2add_sideF
          | rewrite (lor_add_disj 24 x y) by lor2add_sideF | rewrite (lor_add_disj 32 x y) by lor2add_sideF
          | rewrite (lor_add_disj 40 x y) by lor2add_sideF | rewrite (lor_add_disj 48 x y) by lor2add_sideF
          | rewrite (lor_add_disj 56 x y) by lor2add_sideF ].
  Ltac lor2addF := match goal with |- context [Z.lor ?x ?y] => first [ lor2add1F x y | rewrite (Z.lor_comm x y); lor2add1F y x ] end.
  Ltac clear_hyps := repeat match goal with H : _ |- _ => clear H end.
  Ltac shl2mulF :=
    repeat match goal with
    | |- context [Z.shiftl ?x ?k] => is_Zlit_zb k; rewrite (Z.shiftl_mul_pow2 x k) by (clear_hyps; lia);
          let v := eval vm_compute in (2^k) in change (2^k) with v
    end.
  (* [comment removed for export] *)
  Ltac zlbF SB OK IB i :=
    lazymatch type of SB with
    | bytes_at ?segs ?m ?SRC (map (Z_to_bv 8) ?src) =>
        let RD := fresh "RD" in
        assert (RD : ov_read_bytes segs m (Z_to_bv 64 (SRC + i)) 1 = Some [Z_to_bv 8 (Znth i src)])
          by (eapply zd_src_rd; [exact SB | clear - IB; lia | reflexivity]);
        first [ assert (0 <= Znth i src < 256) by assumption | let RB := fresh "RB" in assert (RB : 0 <= Znth i src < 256) by (apply OK) ];
        zstep; cbv beta; rewrite (byte_lit8 (Znth i src)) by assumption; clear RD; shl2mulF; repeat lor2addF
    end.
  Ltac zsF := zstep; shl2mulF; repeat lor2addF.

  (* [comment removed for export] *)
  Ltac gf_src_run p k STOP FUEL :=
    kx_autoFA [KAUnp (SRC + off + p) k; KAApp (SRC + off + p) k] [STOP] FUEL
      [KZRange SRC 6443008 (2^47); KZRange off 0 (2^47); KZRange p 4 24] [] [];
    [ .. | kx_mem; gf_unhold ].

  (* [comment removed for export] *)
  Lemma p_did : forall m1 ws0 (x1 x5 x6 x7 x10 x12 x16 x17 x28 x29 x30 x31 : word),
    MAINP -> MINV m1 (Z0A (Z_to_bv 64 (fhd_header_size fhd))) -> (sseg = 0 -> ws0 = wl_windowSize (Znth (off + 5) src)) -> 0 <= ws0 < 18446744073709551616 ->
    evtF bsegs RNG POST (STpc 0x83778 m1 x1 x5 x6 x7 x10 (Z_to_bv 64 ws0) x12 (Z_to_bv 64 fhd) (Z_to_bv 64 (32 * sseg)) (Z_to_bv 64 (P1 - off))
                              x16 x17 x28 x29 x30 x31).
  Proof.
    intros m1 ws0 x1 x5 x6 x7 x10 x12 x16 x17 x28 x29 x30 x31 MP MV WS0 RWS0.
    pose proof MP as (MG & NF & RSV & WOK). pose proof MV as (SB1 & ZC1 & XI).
    xinv_e XI SAV jA FRA STL STG XF XS XL US UZ UT1 UT2 MU WM MI.
    destruct G_src as (S1 & S2 & S3). destruct R_src as (RS1 & RS2).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (fk_ablk_lits _ _ S1) as SL.
    pose proof (OK (off + 4)) as RF. pose proof (fhd_singleSegment_range fhd) as RSG.
    pose proof (fhd_dictIDSizeCode_range fhd) as RDC. pose proof (fhd_fcsID_range fhd RF) as RFC.
    pose proof (fhd_rp1_range fhd) as RP1. unfold fhd_rp1 in RP1. pose proof (did_fieldSize_range dcode) as RDS.
    pose proof (fhd_header_size_split fhd) as FS. unfold fhd_rp1 in FS. pose proof (fcs_fieldSize_range fcsid) as RFS.
    pose proof (fhd_extra_range fhd) as REX.
    pose proof (fh_read_dictID_range src OK P1 dcode) as RDID. change (2^32) with 4294967296 in RDID.
    pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
    assert (SRr : 6443008 <= SRC /\ SRC + zlen src + 8 <= 2^47) by (clear - SL ATR; lia).
    remember (P1 - off) as p eqn:EP.
    assert (RP : 5 <= p <= 6 /\ off + p + did_fieldSize dcode + fcs_fieldSize fcsid + fhd_extra fhd <= off + size) by (clear - EP RP1 RDS FS RFS REX NF; lia).
    zsF. replace (Z.land fhd 3) with dcode
      by (unfold fhd_dictIDSizeCode; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
    zsF. zsF. if_cases K; zify_lts K.
    - (* [comment removed for export] *)
      zsF. zsF. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        assert (D3 : dcode = 3) by lia. assert (SZ : did_fieldSize dcode = 4) by (rewrite D3; reflexivity).
        gf_src_hold. unfold fk_held in SL. gf_src_run p 4 0x83820 40%nat. gf_src_hold.
        assert (IB : 0 <= off + p /\ off + p + 4 <= zlen src /\ 0 <= SRC) by lia. gf_hold_all.
        zlbF SB1 OK IB (off + p + 1). zlbF SB1 OK IB (off + p). zlbF SB1 OK IB (off + p + 2). zlbF SB1 OK IB (off + p + 3).
        do 7 zsF.
        unfold fk_held in D3, SZ, EP.
        let w := getreg 16 in replace w with (Z_to_bv 64 DID)
          by (f_equal; unfold fh_read_dictID; rewrite D3; cbn [Z.eqb Pos.eqb]; subst p; replace (off + (P1 - off)) with P1 by lia; rewrite le32_bytes; lia).
        replace (p + 4) with (P2 - off) by (clear - EP SZ; lia).
        gf_unhold. apply PFCS; assumption.
      + (* [comment removed for export] *)
        assert (D2 : dcode = 2) by lia. assert (SZ : did_fieldSize dcode = 2) by (rewrite D2; reflexivity).
        gf_src_hold. unfold fk_held in SL. gf_src_run p 2 0x837d8 40%nat. gf_src_hold.
        assert (IB : 0 <= off + p /\ off + p + 2 <= zlen src /\ 0 <= SRC) by lia. gf_hold_all.
        zlbF SB1 OK IB (off + p + 1). zlbF SB1 OK IB (off + p).
        zsF. zsF. zsF. zsF.
        unfold fk_held in D2, SZ, EP.
        let w := getreg 16 in replace w with (Z_to_bv 64 DID)
          by (f_equal; unfold fh_read_dictID; rewrite D2; cbn [Z.eqb Pos.eqb]; subst p; replace (off + (P1 - off)) with P1 by lia; rewrite le16_bytes; lia).
        replace (p + 2) with (P2 - off) by (clear - EP SZ; lia).
        gf_unhold. apply PFCS; assumption.
    - zsF. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        assert (D0 : dcode = 0) by lia.
        replace (Z_to_bv 64 p) with (Z_to_bv 64 (P2 - off)) by (f_equal; rewrite EP, D0; change (did_fieldSize 0) with 0; clear - RSG; lia).
        replace (Z_to_bv 64 dcode) with (Z_to_bv 64 DID) by (unfold fh_read_dictID; rewrite D0; reflexivity).
        apply PFCS; assumption.
      + (* [comment removed for export] *)
        assert (D1 : dcode = 1) by lia. assert (SZ : did_fieldSize dcode = 1) by (rewrite D1; reflexivity).
        gf_src_hold. unfold fk_held in SL. gf_src_run p 1 0x8379c 40%nat. gf_src_hold.
        assert (IB : 0 <= off + p /\ off + p + 1 <= zlen src /\ 0 <= SRC) by lia. gf_hold_all.
        zlbF SB1 OK IB (off + p).
        zsF. zsF.
        unfold fk_held in D1, SZ, EP.
        let w := getreg 16 in replace w with (Z_to_bv 64 DID)
          by (f_equal; unfold fh_read_dictID; rewrite D1; cbn [Z.eqb Pos.eqb]; subst p; replace (off + (P1 - off)) with P1 by lia; reflexivity).
        replace (p + 1) with (P2 - off) by (clear - EP SZ; lia).
        gf_unhold. apply PFCS; assumption.
  Qed.
End GF.
End CANSEC1.
