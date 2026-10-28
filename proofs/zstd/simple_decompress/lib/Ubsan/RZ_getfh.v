(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_frame_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import frame_kit.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma tbl_did_rd : forall m k, mem_inv usegs m -> 0 <= k < 4 ->
  ov_read_bytes usegs m (Z_to_bv 64 (67392 + k * 8)) 8 = Some (le8 (Z_to_bv 64 (did_fieldSize k))).
Proof.
  intros m k MI Hk. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct C as [-> | [-> | [-> | ->]]]; (apply img_rd8; [exact MI | vm_compute; reflexivity | lia | lia]).
Qed.
Lemma tbl_fcs_rd : forall m k, mem_inv usegs m -> 0 <= k < 4 ->
  ov_read_bytes usegs m (Z_to_bv 64 (67424 + k * 8)) 8 = Some (le8 (Z_to_bv 64 (fcs_fieldSize k))).
Proof.
  intros m k MI Hk. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct C as [-> | [-> | [-> | ->]]]; (apply img_rd8; [exact MI | vm_compute; reflexivity | lia | lia]).
Qed.

Section GETFH.
  Variables (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP ZFH SRC : Z) (src : list Z) (off size : Z) (cs0 : list cell) (lo : Z).
  Hypothesis SB : bytes_at usegs m SRC (map (Z_to_bv 8) src).
  Hypothesis OK : all_bytes src.
  Hypothesis OFF0 : 0 <= off.
  Hypothesis N5 : 5 <= size.
  Hypothesis OFS : off + size <= zlen src.
  Hypothesis SRC0 : 0 < SRC.
  Hypothesis ZC0 : rw_cells usegs m ZFH cs0.
  Hypothesis ZSZ : cells_size cs0 = 48%nat.
  Hypothesis ZFH8 : ZFH mod 8 = 0.
  Hypothesis ST : stk usegs m lo SP.
  Hypothesis LO : lo <= SP - 48.
  Hypothesis RSP : 0 <= SP < 2^64.
  Hypothesis ZS : ZFH + 48 <= lo \/ SP <= ZFH.
  Hypothesis SS : SRC + zlen src <= lo \/ SP <= SRC.
  Hypothesis ZSRC : ZFH + 48 <= SRC \/ SRC + zlen src <= ZFH.
  Hypothesis MI : mem_inv usegs m.

  Notation W := [(ZFH, ZFH + 48); (SP - 48, SP)].
  Notation POST := (zd_getfh_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc SP ZFH src off size lo m).

  Notation fhd := (Znth (off + 4) src).
  Notation sseg := (fhd_singleSegment fhd).
  Notation dcode := (fhd_dictIDSizeCode fhd).
  Notation fcsid := (fhd_fcsID fhd).
  (* [comment removed for export] *)
  Notation P1 := (off + 5 + (if fhd_singleSegment fhd =? 0 then 1 else 0)).
  Notation P2 := (off + 5 + (if fhd_singleSegment fhd =? 0 then 1 else 0) + did_fieldSize (fhd_dictIDSizeCode fhd)).
  Notation DID := (fh_read_dictID src P1 dcode).
  Notation FCS := (fh_read_fcs src P2 fcsid sseg).
  Notation WS := (if fhd_singleSegment fhd =? 0 then wl_windowSize (Znth (off + 5) src) else FCS).

  (* [comment removed for export] *)
  Notation STpc pc mm x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 x8 s1 x10 x11 x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition XINV (m1 : fmem) : Prop :=
    (exists j8, rw_cells usegs m1 (SP + -48) [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk usegs m1 lo (SP + -48)
    /\ munch W m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

  (* [comment removed for export] *)
  Lemma p_exit : forall m1 cs r res (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 : word),
    XINV m1 -> rw_cells usegs m1 ZFH cs -> cells_size cs = 48%nat ->
    get_frame_header src off size = res ->
    Z_to_bv 64 r = Z_to_bv 64 (fh_retval res) ->
    (forall h, res = FH_ok h -> cs = zfh_cells h) ->
    evt usegs POST (STpc 0x14bc8 m1 x5 x6 x7 (Z_to_bv 64 r) x10 x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 cs r res x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 ([j8 FR1] & ST1 & MU1 & WM1 & MI1) ZC1 SZ1 ERES ER HD.
    do 7 zs.
    release_frame FR1 ST1 SP.
    zs. rewrite ER.
    apply evt_done. unfold zd_getfh_post. rewrite ERES.
    do 10 eexists. exists m1, cs. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact ZC1|]. split; [exact SZ1| exact HD].
  Qed.

  (* [comment removed for export] *)
  Definition MAINP : Prop :=
    le32 src off = ZD_MAGICNUMBER /\ fhd_header_size fhd <= size /\ fhd_reserved fhd = 0 /\ (sseg = 0 -> Znth (off + 5) src <= 175).
  Definition Z0 (hs : word) : list cell :=
    [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 hs; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
     C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
  Definition MINV (m1 : fmem) : Prop :=
    bytes_at usegs m1 SRC (map (Z_to_bv 8) src) /\ rw_cells usegs m1 ZFH (Z0 (Z_to_bv 64 (fhd_header_size fhd))) /\ XINV m1.

  Lemma gfh_magic : le32 src off = ZD_MAGICNUMBER -> get_frame_header src off size = get_frame_header_zstd src off size.
  Proof.
    intros MG. unfold get_frame_header, ZD_FRAMEHEADERSIZE_PREFIX.
    replace (size <? 5) with false by (symmetry; apply Z.ltb_ge; lia). cbv zeta. rewrite MG, Z.eqb_refl. reflexivity.
  Qed.

  Lemma main_ok : MAINP ->
    get_frame_header src off size = FH_ok (mkFH FCS WS (Z.min WS ZD_BLOCKSIZE_MAX) 0 (fhd_header_size fhd) DID (fhd_checksumFlag fhd)).
  Proof.
    intros (MG & NF & RSV & WOK). rewrite (gfh_magic MG). unfold get_frame_header_zstd.
    rewrite frame_header_size_ge5 by (unfold ZD_FRAMEHEADERSIZE_PREFIX; lia). cbv zeta.
    replace (size <? fhd_header_size fhd) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite RSV. change (negb (0 =? 0)) with false. cbv iota.
    rewrite wl_windowLog_ok_iff by (apply OK).
    destruct (Z.eqb_spec sseg 0) as [E|E]; cbn [andb]; [| reflexivity].
    replace (175 <? Znth (off + 5) src) with false by (symmetry; apply Z.ltb_ge; auto). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma p_fin : forall m1 (x5 x6 x7 x8 x13 x16 x17 : word),
    MAINP -> MINV m1 ->
    evt usegs POST (STpc 0x14fe8 m1 x5 x6 x7 x8 (Z_to_bv 64 ZFH) (Z_to_bv 64 FCS)
                         (Z_to_bv 64 (fhd * 2305843009213693952)) x13
                         (Z_to_bv 64 WS) (Z_to_bv 64 DID) x16 x17).
  Proof.
    intros m1 x5 x6 x7 x8 x13 x16 x17 MP (SB1 & ZC1 & XI).
    pose proof MP as (MG & NF & RSV & WOK).
    destruct XI as ([j8 FR1] & ST1 & MU1 & WM1 & MI1).
    pose proof (OK (off + 4)) as RF.
    pose proof (fh_read_fcs_range src OK P2 fcsid sseg) as RFCS. change (2^64) with 18446744073709551616 in RFCS.
    pose proof (fh_read_dictID_range src OK P1 dcode) as RDID. change (2^32) with 4294967296 in RDID.
    assert (RWS : 0 <= WS < 18446744073709551616).
    { destruct (Z.eqb_spec sseg 0) as [E|E]; [| exact RFCS].
      pose proof (wl_windowSize_range (Znth (off + 5) src) ltac:(apply OK)) as RW.
      pose proof (wl_windowLog_ok_iff (Znth (off + 5) src) ltac:(apply OK)) as WI.
      replace (175 <? Znth (off + 5) src) with false in WI by (symmetry; apply Z.ltb_ge; auto).
      apply Z.ltb_ge in WI. specialize (RW WI). change (2^32) with 4294967296 in RW. change (2^10) with 1024 in RW. lia. }
    unfold Z0 in ZC1.
    zs. replace (((fhd * 2305843009213693952) mod 18446744073709551616) ≫ 63) with (fhd_checksumFlag fhd)
      by (unfold fhd_checksumFlag; byte_brute fhd).
    zs. zs. zs. zs. zs.
    assert (FIN : forall mm (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 : word) bsm,
      bsm = Z.min WS ZD_BLOCKSIZE_MAX ->
      rw_cells usegs mm ZFH [C8 (Z_to_bv 64 FCS); C8 (Z_to_bv 64 WS); C4 (Z_to_bv 64 bsm);
                             C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (fhd_header_size fhd)); C4 (Z_to_bv 64 DID);
                             C4 (Z_to_bv 64 (fhd_checksumFlag fhd)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
      XINV mm ->
      evt usegs POST (STpc 0x14bc8 mm y5 y6 y7 (Z_to_bv 64 0) y10 y11 y12 y13 y14 y15 y16 y17)).
    { intros mm y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 bsm EB ZCm XIm.
      eapply (p_exit mm _ 0 _); [exact XIm | exact ZCm | reflexivity | exact (main_ok MP) | reflexivity |].
      intros h EH. injection EH as <-. unfold zfh_cells. cbn [fh_fcs fh_window fh_bsmax fh_type fh_hsize fh_dictID fh_checksum].
      rewrite EB. reflexivity. }
    if_cases K; zify_cond K.
    - do 5 zs. eapply (FIN _ _ _ _ _ _ _ _ _ _ _ _ WS); [unfold ZD_BLOCKSIZE_MAX; lia | exact ZC1 |].
      split; [eexists; exact FR1|]. split; [exact ST1|]. split; [exact MU1|]. split; [exact WM1| exact MI1].
    - do 6 zs. eapply (FIN _ _ _ _ _ _ _ _ _ _ _ _ 131072); [unfold ZD_BLOCKSIZE_MAX; lia | exact ZC1 |].
      split; [eexists; exact FR1|]. split; [exact ST1|]. split; [exact MU1|]. split; [exact WM1| exact MI1].
  Qed.

  Notation FHD61 := (Z_to_bv 64 (fhd * 2305843009213693952)).

  (* [comment removed for export] *)
  Lemma p_fcs : forall m1 ws0 (x5 x6 x7 x16 x17 : word),
    MAINP -> MINV m1 -> (sseg = 0 -> ws0 = wl_windowSize (Znth (off + 5) src)) -> 0 <= ws0 < 18446744073709551616 ->
    evt usegs POST (STpc 0x14f50 m1 x5 x6 x7 (Z_to_bv 64 (P2 - off)) (Z_to_bv 64 ZFH) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 fhd)
                         (Z_to_bv 64 (32 * sseg)) (Z_to_bv 64 ws0) (Z_to_bv 64 DID)
                         x16 x17).
  Proof.
    intros m1 ws0 x5 x6 x7 x16 x17 MP MV WS0 RWS0.
    pose proof MP as (MG & NF & RSV & WOK). pose proof MV as (SB1 & ZC1 & XI).
    pose proof (OK (off + 4)) as RF. pose proof (fhd_singleSegment_range fhd) as RSG.
    pose proof (fhd_fcsID_range fhd RF) as RFC.
    pose proof (fhd_rp1_range fhd) as RP1. unfold fhd_rp1 in RP1. pose proof (did_fieldSize_range dcode) as RDS.
    pose proof (fhd_header_size_split fhd) as FS. unfold fhd_rp1 in FS. pose proof (fcs_fieldSize_range fcsid) as RFS.
    pose proof (fhd_extra_range fhd) as REX.
    pose proof (fh_read_fcs_range src OK P2 fcsid sseg) as RFCS. change (2^64) with 18446744073709551616 in RFCS.
    pose proof (fh_read_dictID_range src OK P1 dcode) as RDID. change (2^32) with 4294967296 in RDID.
    pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
    (* [comment removed for export] *)
    assert (WSE : WS = if sseg =? 1 then FCS else ws0).
    { destruct (Z.eqb_spec sseg 0) as [E|E]; [rewrite E; cbn [Z.eqb]; symmetry; apply WS0; exact E|].
      replace (sseg =? 1) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
    assert (TAILJ : forall (y5 y6 y7 y8 y13 y16 y17 : word), sseg = 1 ->
       evt usegs POST (STpc 0x14fe4 m1 y5 y6 y7 y8 (Z_to_bv 64 ZFH) (Z_to_bv 64 FCS) FHD61 y13
                            (Z_to_bv 64 ws0) (Z_to_bv 64 DID) y16 y17)).
    { intros. zs. replace (Z_to_bv 64 FCS) with (Z_to_bv 64 WS) at 2
        by (rewrite WSE; replace (sseg =? 1) with true by (symmetry; apply Z.eqb_eq; assumption); reflexivity).
      apply p_fin; assumption. }
    assert (TAILN : forall (y5 y6 y7 y8 y13 y16 y17 : word), sseg = 0 ->
       evt usegs POST (STpc 0x14fe8 m1 y5 y6 y7 y8 (Z_to_bv 64 ZFH) (Z_to_bv 64 FCS) FHD61 y13
                            (Z_to_bv 64 ws0) (Z_to_bv 64 DID) y16 y17)).
    { intros. replace (Z_to_bv 64 ws0) with (Z_to_bv 64 WS)
        by (rewrite WSE; replace (sseg =? 1) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      apply p_fin; assumption. }
    zs. replace (fhd ≫ 6) with fcsid by (unfold fhd_fcsID; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    zs. zs. if_cases K; zify_lts K.
    - (* [comment removed for export] *)
      zs. zs. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        assert (F3 : fcsid = 3) by lia.
        assert (SZ8 : fcs_fieldSize fcsid = 8) by (rewrite F3; reflexivity).
        zs. rewrite zb_lxor_ones by lia. zs. fck. zs.
        zlb SB1 OK (P2 + 1). zlb SB1 OK (P2 + 2). zlb SB1 OK (P2 + 3). zlb SB1 OK P2.
        do 4 zs. zlb SB1 OK (P2 + 4). zlb SB1 OK (P2 + 5). zs.
        zlb SB1 OK (P2 + 6). zlb SB1 OK (P2 + 7).
        do 9 zs.
        let w := getreg 11 in replace w with (Z_to_bv 64 FCS)
          by (f_equal; unfold fh_read_fcs; rewrite F3; cbn [Z.eqb Pos.eqb]; rewrite le64_bytes; lia).
        zs. zs. if_cases K3; zify_cond K3; [apply TAILN; lia | zs; apply TAILJ; lia].
      + (* [comment removed for export] *)
        assert (F2 : fcsid = 2) by lia.
        assert (SZ4 : fcs_fieldSize fcsid = 4) by (rewrite F2; reflexivity).
        zs. rewrite zb_lxor_ones by lia. zs. fck. zs.
        zlb SB1 OK (P2 + 1). zlb SB1 OK P2. zlb SB1 OK (P2 + 2). zlb SB1 OK (P2 + 3).
        do 6 zs.
        let w := getreg 11 in replace w with (Z_to_bv 64 FCS)
          by (f_equal; unfold fh_read_fcs; rewrite F2; cbn [Z.eqb Pos.eqb]; rewrite le32_bytes; lia).
        zs. zs. if_cases K3; zify_cond K3; [apply TAILJ; lia | zs; apply TAILN; lia].
    - zs. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        assert (F1 : fcsid = 1) by lia.
        assert (SZ2 : fcs_fieldSize fcsid = 2) by (rewrite F1; reflexivity).
        zs. rewrite zb_lxor_ones by lia. zs. fck. zs. zlb SB1 OK (P2 + 1). zlb SB1 OK P2. zs. zs. zs.
        let w := getreg 11 in replace w with (Z_to_bv 64 FCS)
          by (f_equal; unfold fh_read_fcs; rewrite F1; cbn [Z.eqb Pos.eqb]; rewrite le16_bytes; lia).
        zs. zs. if_cases K3; zify_cond K3; [apply TAILN; lia | apply TAILJ; lia].
      + (* [comment removed for export] *)
        assert (F0 : fcsid = 0) by lia.
        zs. if_cases K3; zify_cond K3.
        * (* [comment removed for export] *)
          assert (S1 : sseg = 1) by lia.
          assert (EX1 : fhd_extra fhd = 1) by (unfold fhd_extra; rewrite S1, F0; reflexivity).
          zs. rewrite zb_lxor_ones by lia. zs. fck. zs. zlb SB1 OK P2.
          let w := getreg 11 in replace w with (Z_to_bv 64 FCS)
            by (unfold fh_read_fcs; rewrite F0, S1; reflexivity).
          zs. zs. if_cases K4; zify_cond K4; [apply TAILJ; lia | exfalso; lia].
        * (* [comment removed for export] *)
          zs. zs.
          let w := getreg 11 in replace w with (Z_to_bv 64 FCS)
            by (unfold fh_read_fcs; rewrite F0; cbn [Z.eqb];
                replace (sseg =? 0) with true by (symmetry; apply Z.eqb_eq; lia); apply Z_to_bv_eqm; reflexivity).
          zs. if_cases K4; zify_cond K4; [exfalso; lia | zs; apply TAILN; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma p_did : forall m1 ws0 (x5 x6 x7 x15 x16 x17 : word),
    MAINP -> MINV m1 -> (sseg = 0 -> ws0 = wl_windowSize (Znth (off + 5) src)) -> 0 <= ws0 < 18446744073709551616 ->
    evt usegs POST (STpc 0x14ebc m1 x5 x6 x7 (Z_to_bv 64 (P1 - off)) (Z_to_bv 64 ZFH) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 fhd)
                         (Z_to_bv 64 (32 * sseg)) (Z_to_bv 64 ws0) x15 x16 x17).
  Proof.
    intros m1 ws0 x5 x6 x7 x15 x16 x17 MP MV WS0 RWS0.
    pose proof MP as (MG & NF & RSV & WOK). pose proof MV as (SB1 & ZC1 & XI).
    pose proof (OK (off + 4)) as RF. pose proof (fhd_singleSegment_range fhd) as RSG.
    pose proof (fhd_dictIDSizeCode_range fhd) as RDC.
    pose proof (fhd_rp1_range fhd) as RP1. unfold fhd_rp1 in RP1.
    pose proof (fhd_header_size_split fhd) as FS. unfold fhd_rp1 in FS. pose proof (fcs_fieldSize_range fcsid) as RFS.
    pose proof (fhd_extra_range fhd) as REX.
    pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
    zs. replace (Z.land fhd 3) with dcode
      by (unfold fhd_dictIDSizeCode; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
    zs. zs. if_cases K; zify_lts K.
    - zs. zs. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        assert (D3 : dcode = 3) by lia.
        assert (SZ : did_fieldSize dcode = 4) by (rewrite D3; reflexivity).
        zs. rewrite zb_lxor_ones by lia. zs. fck. zs. zlb SB1 OK (P1 + 1). zlb SB1 OK P1. zlb SB1 OK (P1 + 2). zlb SB1 OK (P1 + 3).
        do 7 zs.
        let w := getreg 15 in replace w with (Z_to_bv 64 DID)
          by (f_equal; unfold fh_read_dictID; rewrite D3; cbn [Z.eqb Pos.eqb]; rewrite le32_bytes; lia).
        replace (P1 - off + 4) with (P2 - off) by lia.
        apply p_fcs; assumption.
      + (* [comment removed for export] *)
        assert (D2 : dcode = 2) by lia.
        assert (SZ : did_fieldSize dcode = 2) by (rewrite D2; reflexivity).
        zs. rewrite zb_lxor_ones by lia. zs. fck. zs. zlb SB1 OK (P1 + 1). zlb SB1 OK P1. do 4 zs.
        let w := getreg 15 in replace w with (Z_to_bv 64 DID)
          by (f_equal; unfold fh_read_dictID; rewrite D2; cbn [Z.eqb Pos.eqb]; rewrite le16_bytes; lia).
        replace (P1 - off + 2) with (P2 - off) by lia.
        apply p_fcs; assumption.
    - zs. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        assert (D0 : dcode = 0) by lia.
        assert (SZ : did_fieldSize dcode = 0) by (rewrite D0; reflexivity).
        replace (Z_to_bv 64 dcode) with (Z_to_bv 64 DID)
          by (unfold fh_read_dictID; rewrite D0; reflexivity).
        replace (Z_to_bv 64 (P1 - off)) with (Z_to_bv 64 (P2 - off)) by (f_equal; lia).
        apply p_fcs; assumption.
      + (* [comment removed for export] *)
        assert (D1 : dcode = 1) by lia.
        assert (SZ : did_fieldSize dcode = 1) by (rewrite D1; reflexivity).
        zs. rewrite zb_lxor_ones by lia. zs. fck. zs. zlb SB1 OK P1. zs. zs.
        let w := getreg 15 in replace w with (Z_to_bv 64 DID)
          by (f_equal; unfold fh_read_dictID; rewrite D1; cbn [Z.eqb Pos.eqb]; reflexivity).
        replace (P1 - off + 1) with (P2 - off) by lia.
        apply p_fcs; assumption.
  Qed.

  Lemma getfh_body : evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ZFH) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 size) (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_GETFH) fc None m (seg_rom usegs)).
  Proof.
    unfold PZD_GETFH.
    destruct (rw_cells_forget _ _ _ _ ZC0) as [junk ZC]. rewrite ZSZ in ZC.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    pose proof (rw_cells_bound _ _ _ _ ZC) as ZB. cbn [cells_size csize Nat.add] in ZB.
    pose proof ST as (LO0 & _ & _).
    pose proof (OK (off + 4)) as RF. pose proof (OK (off + 5)) as RWL.
    carve_frame 48%nat ST.
    do 6 zs.
    zs. if_cases K; zify_cond K; [| exfalso; lia]. clear K.
    zs. zs. if_cases K; zify_cond K; [clear K| exfalso; lia].
    zs. if_cases K; zify_cond K; [clear K| exfalso; lia].
    do 7 zs. zs. if_true. zs. fck.
    (* [comment removed for export] *)
    apply (rw_cells_recell usegs _ ZFH _ (Z0 (Z_to_bv 64 0))) in ZC; [| cbn; tauto | vm_compute; reflexivity]. unfold Z0 in ZC.
    assert (XI : forall mm, rw_cells usegs mm (SP + -48) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk0))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
                 stk usegs mm lo (SP + -48) -> munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> XINV mm).
    { intros mm A1 A2 A3 A4 A5. split; [eexists; exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4| exact A5]. }
    zlb SB OK (off + 1). zlb SB OK off. zlb SB OK (off + 2). zlbs SB OK (off + 3).
    do 8 zs.
    rewrite sx_le32_form by assumption.
    replace (Znth off src + 256 * Znth (off + 1) src + 65536 * Znth (off + 2) src + 16777216 * Znth (off + 3) src) with (le32 src off) by (rewrite le32_bytes; reflexivity).
    pose proof (le32_range src OK off) as RM. change (2^32) with 4294967296 in RM. pose proof (zsx32_range _ RM) as RMX.
    assert (SZ5 : (size <? ZD_FRAMEHEADERSIZE_PREFIX) = false) by (apply Z.ltb_ge; unfold ZD_FRAMEHEADERSIZE_PREFIX; lia).
    zs. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (NM : le32 src off <> ZD_MAGICNUMBER).
      { intros E. apply K. rewrite E. reflexivity. }
      zs. rewrite srliw4_zsx32 by exact RM.
      zs. zs. zs. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        assert (RES : get_frame_header src off size = FH_ret (ZERR ZE_prefix_unknown)).
        { unfold get_frame_header. rewrite SZ5. cbv zeta. replace (le32 src off =? ZD_MAGICNUMBER) with false by (symmetry; apply Z.eqb_neq; exact NM).
          unfold is_skippable_magic. replace (le32 src off / 16 =? 25481893) with false by (symmetry; apply Z.eqb_neq; exact K1). reflexivity. }
        zs. zs. eapply (p_exit _ _ (-10) _); [apply XI; assumption | exact ZC | reflexivity | exact RES | apply Z_to_bv_eqm; reflexivity | ].
        intros h E. discriminate E.
      + assert (RES : get_frame_header src off size = if size <? 8 then FH_ret 8 else FH_ok (mkFH (le32 src (off + 4)) 0 0 1 8 (le32 src off - ZD_MAGIC_SKIPPABLE_START) 0)).
        { unfold get_frame_header. rewrite SZ5. cbv zeta. replace (le32 src off =? ZD_MAGICNUMBER) with false by (symmetry; apply Z.eqb_neq; exact NM).
          unfold is_skippable_magic. rewrite K1, Z.eqb_refl. reflexivity. }
        zs. zs. if_cases K2; zify_cond K2.
        * (* [comment removed for export] *)
          replace (size <? 8) with true in RES by (symmetry; apply Z.ltb_lt; lia).
          eapply (p_exit _ _ 8 _); [apply XI; assumption | exact ZC | reflexivity | exact RES | reflexivity | ].
          intros h E. discriminate E.
        * replace (size <? 8) with false in RES by (symmetry; apply Z.ltb_ge; lia).
          zs. zs. fck. zs. zs.
          zlb SB OK (off + 1). zlb SB OK off. zlb SB OK (off + 2). zlbs SB OK (off + 3).
          do 11 zs.
          rewrite sx_le32_form by assumption.
          replace (Znth off src + 256 * Znth (off + 1) src + 65536 * Znth (off + 2) src + 16777216 * Znth (off + 3) src) with (le32 src off) by (rewrite le32_bytes; reflexivity).
          replace (Z_to_bv 64 (zsx32 (le32 src off) + -407710288)) with (Z_to_bv 64 (le32 src off - ZD_MAGIC_SKIPPABLE_START))
            by (rewrite zsx32_small by (Z.div_mod_to_equations; lia); f_equal; unfold ZD_MAGIC_SKIPPABLE_START; lia).
          zs. zs. zs. zs. fck. zs.
          zlb SB OK (off + 5). zlb SB OK (off + 4). zlb SB OK (off + 6). zlb SB OK (off + 7).
          do 6 zs.
          let w := getreg 11 in replace w with (Z_to_bv 64 (le32 src (off + 4)))
            by (f_equal; rewrite le32_bytes; replace (off + 4 + 1) with (off + 5) by lia; replace (off + 4 + 2) with (off + 6) by lia;
                replace (off + 4 + 3) with (off + 7) by lia; lia).
          zs. zs.
          eapply (p_exit _ _ 0 _); [apply XI; assumption | exact ZC | reflexivity | exact RES | reflexivity | ].
          intros h E. injection E as <-. reflexivity.
    - (* [comment removed for export] *)
      apply (proj1 (zsx32_eq_lit (le32 src off) 4247762216 RM ltac:(lia))) in K.
      assert (GZ := gfh_magic K). unfold get_frame_header_zstd in GZ.
      rewrite frame_header_size_ge5 in GZ by (unfold ZD_FRAMEHEADERSIZE_PREFIX; lia). cbv zeta in GZ.
      zs. zs. rewrite zb_lxor_ones by lia. zs. fck. zs.
      zlb SB OK (off + 4).
      pose proof (fhd_fcsID_range fhd RF) as RFC.
      do 5 zs. rewrite ?zb_lxor_ones by lia. zs. fck.
      zs. replace (fhd ≫ 6) with fcsid by (unfold fhd_fcsID; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      do 4 zs. rewrite ?zb_lxor_ones by lia. zs. fck.
      do 12 zs.
      assert (RDD := tbl_did_rd _ (Z.land fhd 3) MI ltac:(change 3 with (Z.ones 2); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia)).
      zs. clear RDD.
      assert (RDF := tbl_fcs_rd _ fcsid MI ltac:(unfold fhd_fcsID; Z.div_mod_to_equations; lia)).
      zs. clear RDF.
      do 5 zs.
      let w := getreg 13 in replace w with (Z_to_bv 64 (fhd_header_size fhd))
        by (f_equal; unfold fhd_header_size, ZD_FRAMEHEADERSIZE_PREFIX, fhd_singleSegment, fhd_dictIDSizeCode, fhd_fcsID, did_fieldSize, fcs_fieldSize; byte_brute fhd).
      pose proof (fhd_header_size_range fhd) as RFS. unfold ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX in RFS.
      zs. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        replace (size <? fhd_header_size fhd) with false in GZ by (symmetry; apply Z.ltb_ge; lia).
        zs. zs. fck. zs. zs. zs. zs. fck. zs. fck. zlb SB OK (off + 4).
        zs. replace (Z.land fhd 8) with (8 * fhd_reserved fhd) by (unfold fhd_reserved; byte_brute fhd).
        pose proof (fhd_reserved_range fhd) as RRSV.
        zs. if_cases K3; zify_cond K3.
        * (* [comment removed for export] *)
          replace (fhd_reserved fhd =? 0) with false in GZ by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in GZ.
          zs. zs. eapply (p_exit _ _ (-14) _); [apply XI; assumption | exact ZC | reflexivity | exact GZ | apply Z_to_bv_eqm; reflexivity | ].
          intros h E. discriminate E.
        * zs. replace (Z.land fhd 32) with (32 * sseg) by (unfold fhd_singleSegment; byte_brute fhd).
          pose proof (fhd_singleSegment_range fhd) as RSG.
          zs. if_cases K4; zify_cond K4.
          -- (* [comment removed for export] *)
             zs. replace (Z_to_bv 64 5) with (Z_to_bv 64 (P1 - off))
               by (replace (sseg =? 0) with false by (symmetry; apply Z.eqb_neq; lia); f_equal; lia).
             apply (p_did _ 0); [ | | intros; lia | lia].
             ++ split; [exact K|]. split; [lia|]. split; [lia|]. intros; lia.
             ++ split; [exact SB|]. split; [exact ZC|]. apply XI; assumption.
          -- (* [comment removed for export] *)
             assert (S0 : sseg = 0) by lia.
             pose proof (fhd_header_size_split fhd) as FS. unfold fhd_rp1 in FS. pose proof (fcs_fieldSize_range fcsid) as RFCS.
             pose proof (did_fieldSize_range dcode) as RDS. pose proof (fhd_extra_range fhd) as REX.
             rewrite S0 in FS. cbn [Z.eqb] in FS.
             zs. rewrite zb_lxor_ones by lia. zs. fck. zs. zlb SB OK (off + 5). zs. zs. if_cases K5; zify_cond K5.
             ++ (* [comment removed for export] *)
                replace (fhd_reserved fhd =? 0) with true in GZ by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in GZ.
                rewrite wl_windowLog_ok_iff in GZ by lia. rewrite S0 in GZ. cbn [Z.eqb andb] in GZ.
                replace (175 <? Znth (off + 5) src) with true in GZ by (symmetry; apply Z.ltb_lt; lia).
                zs. zs. eapply (p_exit _ _ (-16) _); [apply XI; assumption | exact ZC | reflexivity | exact GZ | apply Z_to_bv_eqm; reflexivity | ].
                intros h E. discriminate E.
             ++ do 9 zs.
                let w := getreg 14 in replace w with (Z_to_bv 64 (wl_windowSize (Znth (off + 5) src)))
                  by (f_equal; unfold wl_windowSize, wl_windowLog, ZD_WINDOWLOG_ABSOLUTEMIN; byte_brute (Znth (off + 5) src)).
                zs.
                replace (Z_to_bv 64 6) with (Z_to_bv 64 (P1 - off)) by (rewrite S0; cbn [Z.eqb]; f_equal; lia).
                pose proof (wl_windowSize_range (Znth (off + 5) src) ltac:(lia)) as RWIN.
                pose proof (wl_windowLog_ok_iff (Znth (off + 5) src) ltac:(lia)) as WI.
                replace (175 <? Znth (off + 5) src) with false in WI by (symmetry; apply Z.ltb_ge; lia).
                apply Z.ltb_ge in WI. specialize (RWIN WI). change (2^32) with 4294967296 in RWIN. change (2^10) with 1024 in RWIN.
                apply (p_did _ (wl_windowSize (Znth (off + 5) src))); [ | | intros; reflexivity | lia].
                ** split; [exact K|]. split; [lia|]. split; [lia|]. intros; lia.
                ** split; [exact SB|]. split; [exact ZC|]. apply XI; assumption.
      + (* [comment removed for export] *)
        replace (size <? fhd_header_size fhd) with true in GZ by (symmetry; apply Z.ltb_lt; lia).
        zs. zs. eapply (p_exit _ _ (fhd_header_size fhd) _); [apply XI; assumption | exact ZC | reflexivity | exact GZ | reflexivity | ].
        intros h E. discriminate E.
  Qed.
End GETFH.

Theorem zd_getfh_proof : zd_getfh_stmt.
Proof.
  intros until lo. intros SB OK OFF0 N5 OFS SRC0 ZC ZSZ ZFH8 ST LO RSP ZS SS ZSRC MI -> -> -> ->.
  eapply getfh_body; eassumption.
Qed.
Print Assumptions zd_getfh_proof.
