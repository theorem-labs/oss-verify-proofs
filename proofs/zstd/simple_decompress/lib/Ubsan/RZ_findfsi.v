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
Definition fsi_fin (off : Z) (h : frame_header) (fl : fsi_loop_result) : fsi_result :=
  match fl with
  | FL_err v => FSI_err v
  | FL_done ip rem nb =>
      if negb (fh_checksum h =? 0) && (rem <? 4) then FSI_err (ZERR ZE_srcSize_wrong)
      else
        let ip' := if fh_checksum h =? 0 then ip else ip + 4 in
        FSI nb (ip' - off) (if fh_fcs h =? ZD_CONTENTSIZE_UNKNOWN then nb * fh_bsmax h else fh_fcs h)
  end.

Lemma ffsi_main : forall src off size h,
  ((ZD_SKIPPABLEHEADERSIZE <=? size) && is_skippable_magic (le32 src off)) = false ->
  get_frame_header src off size = FH_ok h ->
  find_frame_size_info src off size = fsi_fin off h (fsi_blocks src (off + fh_hsize h) (size - fh_hsize h) 0).
Proof. intros src off size h SK G. unfold find_frame_size_info. rewrite SK, G. reflexivity. Qed.

Lemma ffsi_hdr_err : forall src off size v,
  ((ZD_SKIPPABLEHEADERSIZE <=? size) && is_skippable_magic (le32 src off)) = false ->
  get_frame_header src off size = FH_ret v ->
  find_frame_size_info src off size = if zd_is_error v then FSI_err v else FSI_err (ZERR ZE_srcSize_wrong).
Proof. intros src off size v SK G. unfold find_frame_size_info. rewrite SK, G. reflexivity. Qed.

Lemma fsi_blocks_err : forall src ip rem nb, all_bytes src ->
  zd_is_error (cblock_ret (get_cblock_size src ip rem)) = true ->
  fsi_blocks src ip rem nb = FL_err (cblock_ret (get_cblock_size src ip rem)).
Proof.
  intros src ip rem nb OK E. rewrite (fsi_blocks_eq src OK).
  destruct (get_cblock_size src ip rem) as [[cbs bp]|]; cbn [cblock_ret] in *; [rewrite E|]; reflexivity.
Qed.

Lemma cblock_ret_range : forall src ip rem, all_bytes src ->
  0 <= cblock_ret (get_cblock_size src ip rem) < 18446744073709551616.
Proof.
  intros src ip rem OK. unfold get_cblock_size.
  destruct (rem <? ZD_blockHeaderSize); cbn [cblock_ret].
  - unfold ZERR, ZE_srcSize_wrong. change (2^64) with 18446744073709551616. lia.
  - pose proof (cblock_props_range (le24 src ip) (le24_range src OK ip)) as (_ & _ & RO2). change (2^21) with 2097152 in RO2.
    unfold bt_rle, bt_reserved, ZERR, ZE_corruption_detected. change (2^64) with 18446744073709551616.
    destruct (_ =? 1); [lia|]. destruct (_ =? 3); lia.
Qed.

Section FINDFSI.
  Hypothesis GETFH : zd_getfh_stmt.
  Hypothesis GETCB : zd_getcblock_stmt.
  Variables (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP FSIP SRC : Z) (src : list Z) (off size : Z) (cs0 : list cell) (lo : Z).
  Hypothesis SB : bytes_at usegs m SRC (map (Z_to_bv 8) src).
  Hypothesis OK : all_bytes src.
  Hypothesis OFF0 : 0 <= off.
  Hypothesis N5 : 5 <= size.
  Hypothesis N40 : size < 1099511627776.
  Hypothesis OFS : off + size <= zlen src.
  Hypothesis SRC0 : 0 < SRC.
  Hypothesis SRCE : SRC + zlen src < 2^64.
  Hypothesis FC0 : rw_cells usegs m FSIP cs0.
  Hypothesis FSZ : cells_size cs0 = 24%nat.
  Hypothesis ST : stk usegs m lo SP.
  Hypothesis LO : lo <= SP - 176.
  Hypothesis RSP : 0 <= SP < 2^64.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis FS : FSIP + 24 <= lo \/ SP <= FSIP.
  Hypothesis SS : SRC + zlen src <= lo \/ SP <= SRC.
  Hypothesis FSRC : FSIP + 24 <= SRC \/ SRC + zlen src <= FSIP.
  Hypothesis MI : mem_inv usegs m.

  Notation W := [(FSIP, FSIP + 24); (SP - 176, SP)].
  Notation POST := (zd_findfsi_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc SP FSIP src off size lo m).
  Notation RES := (find_frame_size_info src off size).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition XINV (m1 : fmem) : Prop :=
    (exists j12, rw_cells usegs m1 (SP + -128) [CB 4 j12])
    /\ (exists csb, rw_cells usegs m1 (SP + -124) csb /\ cells_size csb = 12%nat)
    /\ (exists csz, rw_cells usegs m1 (SP + -112) csz /\ cells_size csz = 48%nat)
    /\ rw_cells usegs m1 (SP + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk usegs m1 lo (SP + -128)
    /\ munch W m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

  (* [comment removed for export] *)
  Lemma p_epi : forall m1 j0 (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : word),
    XINV m1 ->
    rw_cells usegs m1 FSIP [CB 8 j0; C8 (Z_to_bv 64 (fsi_csize RES)); C8 (Z_to_bv 64 (fsi_bound RES))] ->
    evt usegs POST (STpc 0x15418 m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22).
  Proof.
    intros m1 j0 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
           ([j12 J12] & (csb & BPC & BSZ) & (csz & ZFC & ZSZ) & SAVED & ST1 & MU1 & WM1 & MI1) FC1.
    do 8 zs.
    (* [comment removed for export] *)
    assert (FR : rw_cells usegs m1 (SP + -128) ([CB 4 j12] ++ csb ++ csz ++ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact J12|]. cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app _ _ _ _ _)). split; [replace (SP + -128 + Z.of_nat 4) with (SP + -124) by lia; exact BPC|].
      apply (proj2 (rw_cells_app _ _ _ _ _)). rewrite BSZ.
      split; [replace (SP + -128 + Z.of_nat 4 + Z.of_nat 12) with (SP + -112) by lia; exact ZFC|].
      rewrite ZSZ. replace (SP + -128 + Z.of_nat 4 + Z.of_nat 12 + Z.of_nat 48) with (SP + -64) by lia. exact SAVED. }
    eapply stk_release in FR; [| exact ST1 | lia].
    rewrite !cells_size_app, BSZ, ZSZ in FR. cbn [cells_size csize Nat.add] in FR.
    replace (SP + -128 + Z.of_nat 128) with SP in FR by lia.
    zs. zs.
    apply evt_done. unfold zd_findfsi_post.
    do 11 eexists. exists m1, j0. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact FR| exact FC1].
  Qed.
  Definition MINV (m1 : fmem) : Prop :=
    bytes_at usegs m1 SRC (map (Z_to_bv 8) src) /\ (exists j24, rw_cells usegs m1 FSIP [CB 24 j24]) /\ XINV m1.

  (* [comment removed for export] *)
  Lemma p_err : forall m1 v (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : word),
    MINV m1 -> RES = FSI_err v ->
    evt usegs POST (STpc 0x1540c m1 x1 x5 x6 x7 (Z_to_bv 64 FSIP) x9 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22).
  Proof.
    intros m1 v x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (SB1 & [j24 FC1] & XI) ER.
    destruct XI as ([j12 J12] & (csb & BPC & BSZ) & (csz & ZFC & ZSZ) & SAVED & ST1 & MU1 & WM1 & MI1).
    pose proof (rw_cells_bound _ _ _ _ FC1) as FB. cbn [cells_size csize Nat.add] in FB.
    zs. replace (Z_to_bv 64 (-2)) with (Z_to_bv 64 ZD_CONTENTSIZE_ERROR) by (apply Z_to_bv_eqm; reflexivity).
    zs. zs.
    eapply p_epi; [| rewrite ER; cbn [fsi_csize fsi_bound]; exact FC1].
    split; [eexists; exact J12|]. split; [eexists; split; [exact BPC| exact BSZ]|]. split; [eexists; split; [exact ZFC| exact ZSZ]|].
    split; [exact SAVED|]. split; [exact ST1|]. split; [exact MU1|]. split; [exact WM1| exact MI1].
  Qed.

  (* [comment removed for export] *)
  Lemma p_done : forall m1 h ip' rem' nb' (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 : word),
    bytes_at usegs m1 SRC (map (Z_to_bv 8) src) -> (exists j24, rw_cells usegs m1 FSIP [CB 24 j24]) ->
    (exists j12, rw_cells usegs m1 (SP + -128) [CB 4 j12]) ->
    (exists csb, rw_cells usegs m1 (SP + -124) csb /\ cells_size csb = 12%nat) ->
    rw_cells usegs m1 (SP + -112) (zfh_cells h) ->
    rw_cells usegs m1 (SP + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m1 lo (SP + -128) -> munch W m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    get_frame_header src off size = FH_ok h ->
    RES = fsi_fin off h (FL_done ip' rem' nb') ->
    off <= ip' -> 0 <= rem' -> ip' + rem' <= off + size -> 0 <= nb' -> 3 * nb' <= ip' - off ->
    evt usegs POST (STpc 0x15440 m1 x1 x5 x6 x7 (Z_to_bv 64 FSIP) (Z_to_bv 64 (SRC + off)) x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 rem') (Z_to_bv 64 (SRC + ip')) x20 (Z_to_bv 64 nb') x22).
  Proof.
    intros m1 h ip' rem' nb' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 SB1 [j24 FC1] [j12 J12] (csb & BPC & BSZ) ZFC SAVED ST1 MU1 WM1 MI1
           GFH ER B1 B2 B3 B4 B5.
    pose proof (get_frame_header_ok src OK off size h GFH) as (_ & _ & _ & RFCS & _ & RBSM & _ & RCK & _).
    change (2^64) with 18446744073709551616 in RFCS. unfold ZD_BLOCKSIZE_MAX in RBSM.
    pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
    pose proof (rw_cells_bound _ _ _ _ FC1) as FB. cbn [cells_size csize Nat.add] in FB.
    unfold zfh_cells in ZFC.
    assert (FINISH : forall mm ipf (y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y20 y22 : word),
      bytes_at usegs mm SRC (map (Z_to_bv 8) src) -> rw_cells usegs mm FSIP [CB 24 j24] ->
      rw_cells usegs mm (SP + -128) [CB 4 j12] -> rw_cells usegs mm (SP + -124) csb ->
      rw_cells usegs mm (SP + -112) (zfh_cells h) ->
      rw_cells usegs mm (SP + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk usegs mm lo (SP + -128) -> munch W m mm -> wmono usegs m mm -> mem_inv usegs mm ->
      RES = FSI nb' (ipf - off) (if fh_fcs h =? ZD_CONTENTSIZE_UNKNOWN then nb' * fh_bsmax h else fh_fcs h) ->
      off <= ipf <= off + size ->
      evt usegs POST (STpc 0x1545c mm y1 y5 y6 y7 (Z_to_bv 64 FSIP) (Z_to_bv 64 (SRC + off)) y10 x11 y12 y13 y14 y15 y16 y17
                           (Z_to_bv 64 rem') (Z_to_bv 64 (SRC + ipf)) y20 (Z_to_bv 64 nb') y22)).
    { intros mm ipf y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y20 y22 SBm FCm J12m BPCm ZFCm SAVEDm STm MUm WMm MIm ERm BIP.
      unfold zfh_cells in ZFCm.
      zs. zs. zs. replace (SRC + ipf - (SRC + off)) with (ipf - off) by lia.
      assert (FIN2 : forall mm2 bound (z1 z5 z6 z7 z12 z13 z14 z15 z16 z17 z20 z22 : word),
        bound = (if fh_fcs h =? ZD_CONTENTSIZE_UNKNOWN then nb' * fh_bsmax h else fh_fcs h) ->
        rw_cells usegs mm2 FSIP [CB 24 j24] ->
        rw_cells usegs mm2 (SP + -128) [CB 4 j12] -> rw_cells usegs mm2 (SP + -124) csb ->
        rw_cells usegs mm2 (SP + -112) (zfh_cells h) ->
        rw_cells usegs mm2 (SP + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        stk usegs mm2 lo (SP + -128) -> munch W m mm2 -> wmono usegs m mm2 -> mem_inv usegs mm2 ->
        evt usegs POST (STpc 0x15474 mm2 z1 z5 z6 z7 (Z_to_bv 64 FSIP) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 bound) (Z_to_bv 64 (ipf - off)) z12 z13 z14 z15 z16 z17
                             (Z_to_bv 64 rem') (Z_to_bv 64 (SRC + ipf)) z20 (Z_to_bv 64 nb') z22)).
      { intros mm2 bound z1 z5 z6 z7 z12 z13 z14 z15 z16 z17 z20 z22 EBD FC2 J122 BPC2 ZFC2 SAVED2 ST2 MU2 WM2 MI2.
        unfold zfh_cells in ZFC2.
        zs. zs. zs. zs.
        apply (rw_cells_merge usegs _ FSIP [] [C8 (Z_to_bv 64 nb')] _) in FC2. cbn [app cells_size csize Nat.add cells_bytes cbytes] in FC2.
        eapply p_epi; [| rewrite ERm; cbn [fsi_csize fsi_bound]; rewrite <- EBD; exact FC2].
        split; [eexists; exact J122|]. split; [eexists; split; [exact BPC2| exact BSZ]|]. split; [eexists; split; [exact ZFC2| reflexivity]|].
        split; [exact SAVED2|]. split; [exact ST2|]. split; [exact MU2|]. split; [exact WM2| exact MI2]. }
      zs. if_cases KU; zify_cond KU.
      - (* [comment removed for export] *)
        eapply (FIN2 _ (fh_fcs h)); try eassumption.
        replace (fh_fcs h =? ZD_CONTENTSIZE_UNKNOWN) with false by (symmetry; apply Z.eqb_neq; unfold ZD_CONTENTSIZE_UNKNOWN; change (2^64) with 18446744073709551616; lia).
        reflexivity.
      - (* [comment removed for export] *)
        zs. rewrite zx32w_small by lia. zs.
        replace ((nb' * fh_bsmax h) mod 18446744073709551616) with (nb' * fh_bsmax h) by (rewrite Z.mod_small by nia; reflexivity).
        eapply (FIN2 _ (nb' * fh_bsmax h)); try eassumption.
        replace (fh_fcs h =? ZD_CONTENTSIZE_UNKNOWN) with true by (symmetry; apply Z.eqb_eq; unfold ZD_CONTENTSIZE_UNKNOWN; change (2^64) with 18446744073709551616; lia).
        reflexivity. }
    zs. rewrite sx32w_small by lia.
    zs. if_cases KC; zify_cond KC.
    - (* [comment removed for export] *)
      eapply (FINISH _ ip'); try eassumption; [| lia].
      rewrite ER. unfold fsi_fin. rewrite KC. cbn [Z.eqb negb andb]. reflexivity.
    - zs. zs. if_cases K3; zify_cond K3.
      + (* [comment removed for export] *)
        zs. zs. replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) by (apply Z_to_bv_eqm; reflexivity).
        eapply p_err.
        * split; [exact SB1|]. split; [eexists; exact FC1|].
          split; [eexists; exact J12|]. split; [eexists; split; [exact BPC| exact BSZ]|]. split; [eexists; split; [exact ZFC| reflexivity]|].
          split; [exact SAVED|]. split; [exact ST1|]. split; [exact MU1|]. split; [exact WM1| exact MI1].
        * rewrite ER. unfold fsi_fin. replace (fh_checksum h =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
          replace (rem' <? 4) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      + zs. replace (SRC + ip' + 4) with (SRC + (ip' + 4)) by lia. zs. zs. fck.
        eapply (FINISH _ (ip' + 4)); try eassumption; [| lia].
        rewrite ER. unfold fsi_fin. replace (fh_checksum h =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (rem' <? 4) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma p_loop : forall (n : nat) m1 h ip rem nb cbs bp (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 : word),
    rem <= Z.of_nat n ->
    bytes_at usegs m1 SRC (map (Z_to_bv 8) src) -> (exists j24, rw_cells usegs m1 FSIP [CB 24 j24]) ->
    (exists j12, rw_cells usegs m1 (SP + -128) [CB 4 j12]) ->
    rw_cells usegs m1 (SP + -124) (bp_cells bp) ->
    rw_cells usegs m1 (SP + -112) (zfh_cells h) ->
    rw_cells usegs m1 (SP + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m1 lo (SP + -128) -> munch W m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    get_frame_header src off size = FH_ok h ->
    RES = fsi_fin off h (fsi_blocks src ip rem nb) ->
    get_cblock_size src ip rem = Some (cbs, bp) -> zd_is_error cbs = false ->
    off <= ip -> 0 <= rem -> ip + rem <= off + size -> 0 <= nb -> 3 * nb <= ip - off ->
    evt usegs POST (STpc 0x153cc m1 x1 x5 x6 x7 (Z_to_bv 64 FSIP) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 cbs) x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 rem) x19 (Z_to_bv 64 (SRC + ip)) (Z_to_bv 64 (nb + 1)) (Z_to_bv 64 (-119))).
  Proof.
    induction n as [|n IH]; intros m1 h ip rem nb cbs bp x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 RN SB1 [j24 FC1] [j12 J12] BPC ZFC SAVED ST1 MU1 WM1 MI1
           GFH ER G E B1 B2 B3 B4 B5.
    - (* [comment removed for export] *)
      exfalso. unfold get_cblock_size, ZD_blockHeaderSize in G. replace (rem <? 3) with true in G by (symmetry; apply Z.ltb_lt; lia). discriminate G.
    - pose proof (get_cblock_size_ok src OK ip rem cbs bp G) as (R3 & _ & RT & RL & RO & RC). specialize (RC E).
      destruct RC as (_ & RCBS & _). change (2^21) with 2097152 in *. unfold ZD_blockHeaderSize in *.
      pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
      rewrite (fsi_blocks_eq src OK), G, E in ER. unfold ZD_blockHeaderSize in ER.
      unfold bp_cells in BPC. unfold zfh_cells in ZFC.
      zs. zs. if_cases K; zify_cond K.
      + (* [comment removed for export] *)
        zs. zs. replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) by (apply Z_to_bv_eqm; reflexivity).
        eapply p_err.
        * split; [exact SB1|]. split; [eexists; exact FC1|].
          split; [eexists; exact J12|]. split; [eexists; split; [exact BPC| reflexivity]|]. split; [eexists; split; [exact ZFC| reflexivity]|].
          split; [exact SAVED|]. split; [exact ST1|]. split; [exact MU1|]. split; [exact WM1| exact MI1].
        * rewrite ER. replace (rem <? 3 + cbs) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      + replace (rem <? 3 + cbs) with false in ER by (symmetry; apply Z.ltb_ge; lia).
        zs. replace (SRC + ip + (cbs + 3)) with (SRC + (ip + (3 + cbs))) by lia.
        zs. fck. zs. fck. zs. fck.
        zs. rewrite sx32w_small by lia.
        zs. replace (rem - (cbs + 3)) with (rem - (3 + cbs)) by lia.
        zs. if_cases KL; zify_cond KL.
        * (* [comment removed for export] *)
          replace (bp_last bp =? 0) with false in ER by (symmetry; apply Z.eqb_neq; lia).
          eapply (p_done _ h (ip + (3 + cbs)) (rem - (3 + cbs)) (nb + 1)); try eassumption; try lia;
            [eexists; exact FC1 | eexists; exact J12 | eexists; split; [exact BPC| reflexivity]].
        * replace (bp_last bp =? 0) with true in ER by (symmetry; apply Z.eqb_eq; lia).
          zs. zs. zs. zs.
          unfold PZD_GETCBLOCK in GETCB.
          assert (LENP : zlen (map (Z_to_bv 8) src) = zlen src) by (rewrite length_map; reflexivity).
          call (GETCB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SRC (SP + -124) src (ip + (3 + cbs)) (rem - (3 + cbs)) _);
            [ exact SB1 | exact OK | lia | lia | lia | exact SRC0 | exact BPC | reflexivity
            | pose proof ST1 as (LO0 & _ & _); lia | clear - SP16; Z.div_mod_to_equations; lia
            | exact MI1 | reflexivity | reflexivity | reflexivity | ].
          rename PC into BPC'. rename PC0 into BSZ'. rename POST into BPP. rename MI0 into MI2.
          set (ip2 := ip + (3 + cbs)) in *. set (rem2 := rem - (3 + cbs)) in *.
          pose proof (cblock_ret_range src ip2 rem2 OK) as RRET.
          zs. zs. zs. if_cases KE; zify_cond KE.
          -- (* [comment removed for export] *)
             destruct (get_cblock_size src ip2 rem2) as [[v2 bp2]|] eqn:G2; cbn [cblock_ret] in *;
               [| exfalso; unfold ZERR, ZE_srcSize_wrong in KE; change (2^64) with 18446744073709551616 in KE; lia].
             rewrite (BPP v2 bp2 eq_refl) in BPC'.
             replace (Z_to_bv 64 (nb + 2)) with (Z_to_bv 64 (nb + 1 + 1)) by (f_equal; lia).
             eapply (IH _ h ip2 rem2 (nb + 1) v2 bp2); try eassumption; try (unfold ip2, rem2; lia);
               [eexists; exact FC1 | eexists; exact J12 | ].
             apply zd_is_error_false_iff. change (2^64) with 18446744073709551616. lia.
          -- (* [comment removed for export] *)
             eapply p_err.
             ++ split; [exact SB1|]. split; [eexists; exact FC1|].
                split; [eexists; exact J12|]. split; [eexists; split; [exact BPC'| exact BSZ']|]. split; [eexists; split; [exact ZFC| reflexivity]|].
                split; [exact SAVED|]. split; [exact ST1|]. split; [exact MU1|]. split; [exact WM1| exact MI2].
             ++ rewrite ER. rewrite (fsi_blocks_err src ip2 rem2 (nb + 1) OK); [reflexivity|].
                apply zd_is_error_true_iff. change (2^64) with 18446744073709551616. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma p_main : forall m1 (x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x19 x20 x21 x22 : word),
    MINV m1 ->
    ((ZD_SKIPPABLEHEADERSIZE <=? size) && is_skippable_magic (le32 src off)) = false ->
    evt usegs POST (STpc 0x15368 m1 x1 x5 x6 x7 (Z_to_bv 64 FSIP) (Z_to_bv 64 (SRC + off)) x10 x11 x12 (Z_to_bv 64 0) x14 x15 x16 x17
                         (Z_to_bv 64 size) x19 x20 x21 x22).
  Proof.
    intros m1 x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x19 x20 x21 x22 (SB1 & [j24 FC1] & XI) SK.
    destruct XI as ([j12 J12] & (csb & BPC & BSZ) & (csz & ZFC & ZSZ) & SAVED & ST1 & MU1 & WM1 & MI1).
    pose proof (bytes_at_bound _ _ _ _ SB1) as DB. rewrite length_map in DB.
    pose proof (rw_cells_bound _ _ _ _ FC1) as FB. cbn [cells_size csize Nat.add] in FB.
    assert (LENP : zlen (map (Z_to_bv 8) src) = zlen src) by (rewrite length_map; reflexivity).
    pose proof ST1 as (LO0 & _ & _).
    zs. zs. zs. zs.
    unfold PZD_GETFH in GETFH.
    call (GETFH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -128) (SP + -112) SRC src off size _ lo);
      [ exact SB1 | exact OK | exact OFF0 | exact N5 | exact OFS | exact SRC0 | exact ZFC | exact ZSZ
      | clear - SP16; Z.div_mod_to_equations; lia | exact ST1
      | lia | lia | lia | lia | lia | exact MI1 | reflexivity | reflexivity | reflexivity | reflexivity | ].
    rename PC into ST2. rename PC0 into ZFC'. rename PC1 into ZSZ'. rename POST into ZFP. rename MI0 into MI2.
    set (gfh := get_frame_header src off size) in *.
    assert (RRET : 0 <= fh_retval gfh < 18446744073709551616).
    { destruct gfh as [hh|v] eqn:G; cbn [fh_retval]; [lia|]. pose proof (gfh_ret_pos src off size v N5 G). lia. }
    zs. zs. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      eapply p_err.
      + split; [exact SB1|]. split; [eexists; exact FC1|].
        split; [eexists; exact J12|]. split; [eexists; split; [exact BPC| exact BSZ]|]. split; [eexists; split; [exact ZFC'| exact ZSZ']|].
        split; [exact SAVED|]. split; [exact ST2|]. split; [exact MU1|]. split; [exact WM1| exact MI2].
      + destruct gfh as [hh|v] eqn:G; cbn [fh_retval] in *; [exfalso; lia|].
        rewrite (ffsi_hdr_err src off size v SK G).
        replace (zd_is_error v) with true by (symmetry; apply zd_is_error_true_iff; change (2^64) with 18446744073709551616; lia). reflexivity.
    - zs. if_cases K0; zify_cond K0.
      + (* [comment removed for export] *)
        destruct gfh as [h|v] eqn:G; cbn [fh_retval] in *; [| exfalso; pose proof (gfh_ret_pos src off size v N5 G); lia].
        rewrite (ZFP h eq_refl) in ZFC'. clear ZFP.
        pose proof (get_frame_header_ok src OK off size h G) as (_ & _ & RHS & _ & _ & _ & _ & _ & HT0 & HT1).
        assert (RHS0 : 5 <= fh_hsize h <= 18).
        { pose proof (get_frame_header_ok src OK off size h G) as (TY & _). destruct TY as [T|T].
          - destruct (HT0 T) as (_ & _ & RR & _). unfold ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX in RR. lia.
          - destruct (HT1 T) as (_ & RR & _). unfold ZD_SKIPPABLEHEADERSIZE in RR. lia. }
        pose proof (ffsi_main src off size h SK G) as ER.
        unfold zfh_cells in ZFC'.
        zs. rewrite zx32w_small by lia.
        zs. let w := getreg 20 in replace w with (Z_to_bv 64 (SRC + (off + fh_hsize h))) by (f_equal; lia).
        zs. fck.
        zs. zs. zs. zs.
        replace (0 <? SRC + off) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (SRC + (off + fh_hsize h) <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
        if_false.
        zs. zs. zs. zs. zs.
        unfold PZD_GETCBLOCK in GETCB.
        call (GETCB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SRC (SP + -124) src (off + fh_hsize h) (size - fh_hsize h) _);
          [ exact SB1 | exact OK | lia | lia | lia | exact SRC0 | exact BPC | exact BSZ
          | lia | clear - SP16; Z.div_mod_to_equations; lia
          | exact MI2 | reflexivity | reflexivity | reflexivity | ].
        rename PC into BPC'. rename PC0 into BSZ'. rename POST into BPP. rename MI0 into MI3.
        set (ip2 := off + fh_hsize h) in *. set (rem2 := size - fh_hsize h) in *.
        pose proof (cblock_ret_range src ip2 rem2 OK) as RRET2.
        zs. zs. if_cases KE2; zify_cond KE2.
        * (* [comment removed for export] *)
          eapply p_err.
          -- split; [exact SB1|]. split; [eexists; exact FC1|].
             split; [eexists; exact J12|]. split; [eexists; split; [exact BPC'| exact BSZ']|]. split; [eexists; split; [exact ZFC'| reflexivity]|].
             split; [exact SAVED|]. split; [exact ST2|]. split; [exact MU1|]. split; [exact WM1| exact MI3].
          -- rewrite ER. rewrite (fsi_blocks_err src ip2 rem2 0 OK); [reflexivity|].
             apply zd_is_error_true_iff. change (2^64) with 18446744073709551616. lia.
        * destruct (get_cblock_size src ip2 rem2) as [[v2 bp2]|] eqn:G2; cbn [cblock_ret] in *;
            [| exfalso; unfold ZERR, ZE_srcSize_wrong in KE2; change (2^64) with 18446744073709551616 in KE2; lia].
          rewrite (BPP v2 bp2 eq_refl) in BPC'.
          zs. zs. change (Z_to_bv 64 1) with (Z_to_bv 64 (0 + 1)).
          eapply (p_loop (Z.to_nat rem2) _ h ip2 rem2 0 v2 bp2); try eassumption; try (unfold ip2, rem2; lia);
            [eexists; exact FC1 | eexists; exact J12 | ].
          apply zd_is_error_false_iff. change (2^64) with 18446744073709551616. lia.
      + (* [comment removed for export] *)
        zs. zs. replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) by (apply Z_to_bv_eqm; reflexivity).
        eapply p_err.
        * split; [exact SB1|]. split; [eexists; exact FC1|].
          split; [eexists; exact J12|]. split; [eexists; split; [exact BPC| exact BSZ]|]. split; [eexists; split; [exact ZFC'| exact ZSZ']|].
          split; [exact SAVED|]. split; [exact ST2|]. split; [exact MU1|]. split; [exact WM1| exact MI2].
        * destruct gfh as [hh|v] eqn:G; cbn [fh_retval] in *; [exfalso; lia|].
          rewrite (ffsi_hdr_err src off size v SK G).
          replace (zd_is_error v) with false by (symmetry; apply zd_is_error_false_iff; change (2^64) with 18446744073709551616; lia). reflexivity.
  Qed.


  Lemma findfsi_body : evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FSIP) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 size) (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_FINDFSI) fc None m (seg_rom usegs)).
  Proof.
    unfold PZD_FINDFSI.
    destruct (rw_cells_forget _ _ _ _ FC0) as [junk FC]. rewrite FSZ in FC.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size csize Nat.add] in FB.
    pose proof ST as (LO0 & _ & _).
    carve_frame 128%nat ST.
    do 9 zs.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB usegs _ _ [] _ _ _ [4; 12; 48]%nat) in FR; [| reflexivity].
    cbn [mk_CB_cells app] in FR.
    apply (proj1 (rw_cells_app _ _ _ [CB 4 _] _)) in FR. destruct FR as [J12 FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app _ _ _ [CB 12 _] _)) in FR. destruct FR as [BPC FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app _ _ _ [CB 48 _] _)) in FR. destruct FR as [ZFC SAVED]. cbn [cells_size csize Nat.add] in SAVED.
    replace (SP + -128 + Z.of_nat 4) with (SP + -124) in * by lia.
    replace (SP + -124 + Z.of_nat 12) with (SP + -112) in * by lia.
    replace (SP + -112 + Z.of_nat 48) with (SP + -64) in * by lia.
    assert (LENP : zlen (map (Z_to_bv 8) src) = zlen src) by (rewrite length_map; reflexivity).
    assert (MV : forall mm ja jb jc, bytes_at usegs mm SRC (map (Z_to_bv 8) src) -> rw_cells usegs mm FSIP [CB 24 junk] ->
       rw_cells usegs mm (SP + -128) [CB 4 ja] ->
       rw_cells usegs mm (SP + -124) [CB 12 jb] ->
       rw_cells usegs mm (SP + -112) [CB 48 jc] ->
       rw_cells usegs mm (SP + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
       stk usegs mm lo (SP + -128) -> munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> MINV mm).
    { intros mm ja jb jc A0 A1 A2 A3 A4 A5 A6 A7 A8 A9. split; [exact A0|]. split; [eexists; exact A1|].
      split; [eexists; exact A2|]. split; [eexists; split; [exact A3| reflexivity]|]. split; [eexists; split; [exact A4| reflexivity]|].
      split; [exact A5|]. split; [exact A6|]. split; [exact A7|]. split; [exact A8| exact A9]. }
    zs. zs. zs. zs.
    zs. if_cases K8; zify_cond K8.
    { (* [comment removed for export] *)
      eapply p_main; [eapply MV; eassumption|].
      unfold ZD_SKIPPABLEHEADERSIZE. replace (8 <=? size) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
    zs. if_false. zs. fck.
    zlb SB OK (off + 1). zlb SB OK off. zlb SB OK (off + 2). zlb SB OK (off + 3).
    do 8 zs.
    match goal with |- context [Z.shiftr ?e 4] => replace e with (le32 src off) by (rewrite le32_bytes; lia) end.
    pose proof (le32_range src OK off) as RM. change (2^32) with 4294967296 in RM.
    rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16.
    zs. zs. if_cases KS; zify_cond KS.
    { (* [comment removed for export] *)
      eapply p_main; [eapply MV; eassumption|].
      unfold is_skippable_magic. replace (le32 src off / 16 =? 25481893) with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r. }
    (* [comment removed for export] *)
    assert (ER : RES = FSI 0 (read_skippable_frame_size src off size) 0).
    { unfold find_frame_size_info, ZD_SKIPPABLEHEADERSIZE, is_skippable_magic. replace (8 <=? size) with true by (symmetry; apply Z.leb_le; lia).
      rewrite KS, Z.eqb_refl. reflexivity. }
    zs. zs. zs. fck.
    zlb SB OK (off + 5). zlb SB OK (off + 4). zlb SB OK (off + 6). zlb SB OK (off + 7).
    do 7 zs.
    match goal with |- context [Z_to_bv 64 (?e + 8)] => replace e with (le32 src (off + 4))
      by (rewrite le32_bytes; replace (off + 4 + 1) with (off + 5) by lia; replace (off + 4 + 2) with (off + 6) by lia;
          replace (off + 4 + 3) with (off + 7) by lia; lia) end.
    pose proof (le32_range src OK (off + 4)) as RS. change (2^32) with 4294967296 in RS.
    set (s32 := le32 src (off + 4)) in *.
    assert (RSK : read_skippable_frame_size src off size =
                  if 4294967287 <? s32 then ZERR ZE_frameParameter_unsupported else if size <? 8 + s32 then ZERR ZE_srcSize_wrong else 8 + s32).
    { unfold read_skippable_frame_size, ZD_SKIPPABLEHEADERSIZE. replace (size <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
      cbv zeta. fold s32. pose proof (skippable_wrap_iff s32 ltac:(change (2^32) with 4294967296; lia)) as WI.
      unfold ZD_SKIPPABLEHEADERSIZE in WI. rewrite WI. reflexivity. }
    assert (SKIPFIN : forall mm v (y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 : word),
       MINV mm -> Z_to_bv 64 v = Z_to_bv 64 (read_skippable_frame_size src off size) ->
       evt usegs POST (STpc 0x15358 mm y1 y5 y6 y7 (Z_to_bv 64 FSIP) y9 (Z_to_bv 64 v) y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22)).
    { intros mm v y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 (SBm & [j24 FCm] & XIm) EV.
      destruct XIm as ([j12 J12m] & (csb & BPCm & BSZm) & (csz & ZFCm & ZSZm) & SAVEDm & STm & MUm & WMm & MIm).
      pose proof (rw_cells_bound _ _ _ _ FCm) as FBm. cbn [cells_size csize Nat.add] in FBm.
      rewrite EV. zs. zs. zs. zs.
      apply (rw_cells_merge usegs _ FSIP [] [C8 (Z_to_bv 64 0)] _) in FCm. cbn [app cells_size csize Nat.add cells_bytes cbytes] in FCm.
      eapply p_epi; [| rewrite ER; cbn [fsi_csize fsi_bound]; exact FCm].
      split; [eexists; exact J12m|]. split; [eexists; split; [exact BPCm| exact BSZm]|]. split; [eexists; split; [exact ZFCm| exact ZSZm]|].
      split; [exact SAVEDm|]. split; [exact STm|]. split; [exact MUm|]. split; [exact WMm| exact MIm]. }
    zs. if_cases KA; zify_cond KA.
    - (* [comment removed for export] *)
      zs. zs. zs. zs. if_cases KW; zify_cond KW.
      + eapply (SKIPFIN _ (s32 + 8)); [eapply MV; eassumption|].
        rewrite RSK. replace (4294967287 <? s32) with false by (symmetry; apply Z.ltb_ge; lia).
        replace (size <? 8 + s32) with false by (symmetry; apply Z.ltb_ge; lia). f_equal. lia.
      + zs. eapply (SKIPFIN _ (-14)); [eapply MV; eassumption|].
        rewrite RSK. replace (4294967287 <? s32) with true by (symmetry; apply Z.ltb_lt; lia). apply Z_to_bv_eqm. reflexivity.
    - zs. zs. zs. zs. zs. if_cases KW; zify_cond KW.
      + eapply (SKIPFIN _ (-72)); [eapply MV; eassumption|].
        rewrite RSK. replace (4294967287 <? s32) with false by (symmetry; apply Z.ltb_ge; lia).
        replace (size <? 8 + s32) with true by (symmetry; apply Z.ltb_lt; lia). apply Z_to_bv_eqm. reflexivity.
      + zs. eapply (SKIPFIN _ (-14)); [eapply MV; eassumption|].
        rewrite RSK. replace (4294967287 <? s32) with true by (symmetry; apply Z.ltb_lt; lia). apply Z_to_bv_eqm. reflexivity.
  Qed.
End FINDFSI.

Theorem zd_findfsi_proof : zd_getfh_stmt -> zd_getcblock_stmt -> zd_findfsi_stmt.
Proof.
  intros GETFH GETCB. intros until lo. intros SB OK OFF0 N5 N40 OFS SRC0 SRCE FC FSZ ST LO RSP SP16 FS SS FSRC MI -> -> -> ->.
  change (2^40) with 1099511627776 in N40.
  eapply findfsi_body; eassumption.
Qed.
Print Assumptions zd_findfsi_proof.
