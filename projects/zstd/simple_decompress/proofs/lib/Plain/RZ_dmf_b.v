(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdFrameW ZdWalkKit ZdCellKit ZdDctxRep.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_libc_iface RZ_frame_iface RZ_block_iface RZ_dframe_iface RZ_dmf_a.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DMFB.
  Variable TBL : tbl_pred.
  Hypothesis TBLL : tbl_laws TBL.
  Hypothesis DBLOCK : zd_dblock_stmt TBL.
  Hypothesis DBEGIN : zd_dbegin_stmt.
  Hypothesis CHECKCONT : zd_checkcont_stmt.
  Hypothesis DECODEFH : zd_decodefh_stmt.
  Hypothesis GETCB : zd_getcblock_stmt.
  Hypothesis ERRCODE : zd_errcode_stmt.
  Hypothesis XXHUPD : zd_xxh_update_stmt.
  Hypothesis XXHDIG : zd_xxh_digest_stmt.
  Hypothesis MEMMOVE : zd_memmoveZ_stmt.
  Hypothesis MEMSET : zd_memsetZ_stmt.

  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP lo DCTX DST CAP SRC : Z) (src : list Z) (size : Z).
  Hypothesis RD0 : 4096 <= DCTX.  Hypothesis RD1 : DCTX + 95992 < 2^47.  Hypothesis RD8 : DCTX mod 8 = 0.
  Hypothesis OK : all_bytes src.
  Hypothesis N0 : 0 <= size.  Hypothesis NLEN : size <= zlen src.  Hypothesis N40 : size < 1099511627776.
  Hypothesis RS0 : 4096 <= SRC.  Hypothesis RS1 : SRC + zlen src < 2^47.
  Hypothesis RC0 : 0 <= CAP.  Hypothesis RC40 : CAP < 1099511627776.
  Hypothesis DNULL : DST = 0 -> CAP = 0.  Hypothesis DNN : DST <> 0 -> 4096 <= DST.  Hypothesis RDST : DST + CAP < 2^47.
  Hypothesis RLO : 4096 <= lo.  Hypothesis LO : lo <= SP - 2368.  Hypothesis RSP : SP < 2^47.
  Hypothesis S_DC : DCTX + 95992 <= lo \/ SP <= DCTX.
  Hypothesis S_DS : DST + CAP <= lo \/ SP <= DST.
  Hypothesis S_SR : SRC + zlen src <= lo \/ SP <= SRC.
  Hypothesis S_GT : 0x30d00 + 16 <= lo \/ SP <= 0x30d00.
  Hypothesis D_DC : DST + CAP <= DCTX \/ DCTX + 95992 <= DST.
  Hypothesis D_SR : DST + CAP <= SRC \/ SRC + zlen src <= DST.
  Hypothesis SR_DC : SRC + zlen src <= DCTX \/ DCTX + 95992 <= SRC.
  Hypothesis GT_DC : 0x30d00 + 16 <= DCTX \/ DCTX + 95992 <= 0x30d00.
  Hypothesis GT_DS : 0x30d00 + 16 <= DST \/ DST + CAP <= 0x30d00.

  Notation W := [(DCTX, DCTX + 95992); (DST, DST + CAP); (SP - 2368, SP)].
  Notation POST := (zd_dmf_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP DCTX DST CAP src size lo m).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -320)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  Notation frl_cells := (RZ_dmf_a.frl_cells DCTX).
  Notation frh_cells := (RZ_dmf_a.frh_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation ENV := (RZ_dmf_a.ENV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SP lo DCTX DST CAP SRC src).
  Notation A_INV := (RZ_dmf_a.A_INV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SP lo DCTX DST CAP SRC src size).
  Notation ASt mm off sz tot mt1 x5 x6 x7 x12 x13 x14 x15 x16 x26 x28 x29 :=
    (STpc 0x15330 mm (Z_to_bv 64 (-120)) x5 x6 x7 (Z_to_bv 64 (DST + tot)) (Z_to_bv 64 sz) (Z_to_bv 64 5) (Z_to_bv 64 1) x12 x13 x14 x15 x16
          (Z_to_bv 64 4294967287) (Z_to_bv 64 (DCTX + 29912)) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 0) (Z_to_bv 64 mt1)
          (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 DST) (Z_to_bv 64 0) x26 (Z_to_bv 64 25481893) x28 x29 (Z_to_bv 64 4) (Z_to_bv 64 8)).


  (* [comment removed for export] *)
  Hypothesis HRES : forall m1 off sz tot mt1 res sl0 sl1 sl2 sl3 sl4
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word),
    ENV m1 -> rw_cells psegs m1 (SP + -320) (frl_cells sl0 sl1 sl2 sl3 sl4) -> dctx_any m1 DCTX ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) -> 0 <= res < 2^64 ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    (zd_is_error res = false -> exists off' sz',
        x9 = Z_to_bv 64 sz' /\ x23 = Z_to_bv 64 (SRC + off') /\ res <= CAP - tot /\ off <= off' /\ off' + sz' <= size /\ 0 <= sz' < sz /\
        (forall r, dmulti src off' sz' (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r)) ->
    (forall m' off' sz' tot' (y5 y6 y7 y12 y13 y14 y15 y16 y26 y28 y29 : word), sz' < sz -> A_INV m' off' sz' tot' 1 ->
        evt psegs POST (ASt m' off' sz' tot' 1 y5 y6 y7 y12 y13 y14 y15 y16 y26 y28 y29)) ->
    evt psegs POST (STpc 0x1559c m1 x1 x5 x6 x7 (Z_to_bv 64 (DST + tot)) x9 x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 (DCTX + 29912)) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 0) (Z_to_bv 64 mt1)
                         x23 (Z_to_bv 64 DST) (Z_to_bv 64 0) (Z_to_bv 64 (-72)) (Z_to_bv 64 res) x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma h5_keep : forall ws ws' i, (forall j, h5_block_owned j = false -> wnth ws' j = wnth ws j) -> h5_block_owned i = false ->
    wnth ws' i = wnth ws i.
  Proof. intros ws ws' i H Hi. apply H. exact Hi. Qed.
  Lemma h5_frame_ok_keep : forall ws ws', h5_frame_ok ws -> (forall j, h5_block_owned j = false -> wnth ws' j = wnth ws j) ->
    h5_frame_ok ws'.
  Proof.
    intros ws ws' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13) H. unfold h5_frame_ok.
    rewrite (H H5_format eq_refl), (H H5_forceIgnoreChecksum eq_refl), (H H5_refMultipleDDicts eq_refl), (H H5_maxBlockSizeParam eq_refl),
            (H H5_customAlloc eq_refl), (H H5_customFree eq_refl), (H H5_customOpaque eq_refl), (H H5_staticSize eq_refl),
            (H H5_ddictLocal eq_refl), (H H5_ddict eq_refl), (H H5_dictUses eq_refl), (H H5_ddictSet eq_refl), (H H5_inBuff eq_refl).
    repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition B_DCTX (m1 : fmem) (h : frame_header) (PFX : Z) (llt mlt oft huf pde expd pcs dsz bt stg le fe : word)
      (xs : list cell) (ws : list word) : Prop :=
    dctx_ptrs psegs m1 DCTX llt mlt oft huf /\
    dctx_h1 psegs m1 DCTX pde (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 0) expd /\
    rw_cells psegs m1 (DCTX + 29928) (zfh_cells h) /\
    dctx_h3 psegs m1 DCTX pcs dsz bt stg le fe /\
    dctx_xs psegs m1 DCTX xs /\ (fh_checksum h <> 0 -> exists j1 msz j2, xs = xxh_cells j1 msz j2 /\ 0 <= msz < 32) /\
    dctx_h5 psegs m1 DCTX ws /\ h5_frame_ok ws /\
    wnth ws H5_validateChecksum = Z_to_bv 64 (if fh_checksum h =? 0 then 0 else 1) /\
    wnth ws H5_isFrameDecompression = Z_to_bv 64 1 /\
    (exists jhb ovd dcb dce trace, dctx_tx psegs m1 DCTX jhb ovd dcb dce trace) /\
    dctx_owned psegs m1 DCTX /\
    TBL m1 DCTX llt mlt oft huf le fe.


  (* [comment removed for export] *)
  Definition FRAME_OK (off sz tot mt1 hsz : Z) (h : frame_header) : Prop :=
    0 <= off /\ off + sz <= size /\ 0 <= tot <= CAP /\ (mt1 = 0 \/ mt1 = 1) /\
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) /\
    9 <= sz /\ hsz = frame_header_size src off ZD_FRAMEHEADERSIZE_PREFIX /\ hsz + 3 <= sz /\
    is_skippable_magic (le32 src off) = false /\ get_frame_header src off hsz = FH_ok h.

  (* [comment removed for export] *)
  Definition KA_T (sz : Z) : Prop :=
    forall m' off' sz' tot' (y5 y6 y7 y12 y13 y14 y15 y16 y26 y28 y29 : word), sz' < sz -> A_INV m' off' sz' tot' 1 ->
        evt psegs POST (ASt m' off' sz' tot' 1 y5 y6 y7 y12 y13 y14 y15 y16 y26 y28 y29).

  Notation FRLB mm mt1 := (rw_cells psegs mm (SP + -320) (frl_cells (Z_to_bv 64 DST) (Z_to_bv 64 mt1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (DST + CAP)))).

  Lemma B_DCTX_any : forall mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws,
    B_DCTX mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws -> dctx_any mm DCTX.
  Proof.
    intros mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws
           (A1 & A2 & A3 & A4 & A5 & _ & A6 & A7 & _ & _ & (j1 & j2 & j3 & j4 & j5 & A8) & A9 & _).
    exists llt, mlt, oft, huf, pde, (Z_to_bv 64 PFX), (Z_to_bv 64 PFX), (Z_to_bv 64 0), expd, (zfh_cells h), pcs, dsz, bt, stg, le, fe, xs, ws, j1, j2, j3, j4, j5.
    split; [exact A1|]. split; [exact A2|]. split; [split; [exact A3| reflexivity]|]. split; [exact A4|]. split; [exact A5|].
    split; [exact A6|]. split; [exact A7|]. split; [exact A8| exact A9].
  Qed.

  (* [comment removed for export] *)
  Lemma L_errx : forall mm off sz tot mt1 res
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y23 y24 y25 y28 y29 y30 y31 : word),
    ENV mm -> FRLB mm mt1 -> dctx_any mm DCTX ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    zd_is_error res = true -> 0 <= res < 2^64 -> KA_T sz ->
    evt psegs POST (STpc 0x15790 mm y1 y5 y6 y7 (Z_to_bv 64 (DST + tot)) (Z_to_bv 64 sz) y10 y11 y12 y13 y14 y15 y16 y17
                       (Z_to_bv 64 (DCTX + 29912)) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) y21 y22 y23 y24 y25 (Z_to_bv 64 (-72)) (Z_to_bv 64 res) y28 y29 y30 y31).
  Proof.
    intros mm off sz tot mt1 res y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y23 y24 y25 y28 y29 y30 y31
           ENm FRLm DAm ROFF RSZ RT RMT ACC ERm RRm KA.
    pose proof FRLm as FRLm'. unfold RZ_dmf_a.frl_cells in FRLm'.
    zs. zs. zs. zs. zs.
    eapply (HRES mm off sz tot mt1 res); try eassumption.
    intros NE. rewrite ERm in NE. discriminate NE.
  Qed.

  (* [comment removed for export] *)
  Lemma L_errx2 : forall mm off sz tot mt1 res
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y23 y28 y29 y30 y31 : word),
    ENV mm -> FRLB mm mt1 -> dctx_any mm DCTX ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    zd_is_error res = true -> 0 <= res < 2^64 -> KA_T sz ->
    evt psegs POST (STpc 0x15798 mm y1 y5 y6 y7 (Z_to_bv 64 (DST + tot)) (Z_to_bv 64 sz) y10 y11 y12 y13 y14 y15 y16 y17
                       (Z_to_bv 64 (DCTX + 29912)) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) y21 y22 y23 (Z_to_bv 64 DST) (Z_to_bv 64 0)
                       (Z_to_bv 64 (-72)) (Z_to_bv 64 res) y28 y29 y30 y31).
  Proof.
    intros mm off sz tot mt1 res y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y23 y28 y29 y30 y31
           ENm FRLm DAm ROFF RSZ RT RMT ACC ERm RRm KA.
    pose proof FRLm as FRLm'. unfold RZ_dmf_a.frl_cells in FRLm'.
    zs. zs. zs.
    eapply (HRES mm off sz tot mt1 res); try eassumption.
    intros NE. rewrite ERm in NE. discriminate NE.
  Qed.

  (* [comment removed for export] *)
  Lemma L_tail : forall mm off sz tot mt1 res ipF remF
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y28 y29 y30 y31 : word),
    ENV mm -> FRLB mm mt1 -> dctx_any mm DCTX ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    0 <= res <= CAP - tot -> off <= ipF -> ipF + remF <= size -> 0 <= remF < sz ->
    (forall r, dmulti src ipF remF (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r) ->
    KA_T sz ->
    evt psegs POST (STpc 0x1585c mm y1 y5 y6 y7 (Z_to_bv 64 (DST + tot)) (Z_to_bv 64 remF) y10 y11 y12 y13 y14 y15 y16 y17
                       (Z_to_bv 64 (DCTX + 29912)) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) y21 (Z_to_bv 64 (SRC + ipF))
                       (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 DST) (Z_to_bv 64 0) (Z_to_bv 64 (-72)) (Z_to_bv 64 res) y28 y29 y30 y31).
  Proof.
    intros mm off sz tot mt1 res ipF remF y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y28 y29 y30 y31
           ENm FRLm DAm ROFF RSZ RT RMT ACC RRES RF1 RF2 RF3 STEP KA.
    pose proof FRLm as FRLm'. unfold RZ_dmf_a.frl_cells in FRLm'.
    pose proof ENm as (GOTm & _).
    zs. zs. zs. unfold wz0. zs. if_true. zs. zs. zs. zs.
    assert (NE : zd_is_error res = false) by (apply zd_is_error_false_iff; change (2^64) with 18446744073709551616; lia).
    eapply (HRES mm off sz tot mt1 res); try eassumption.
    - change (2^64) with 18446744073709551616. lia.
    - intros _. exists ipF, remF. split; [reflexivity|]. split; [reflexivity|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. exact STEP.
  Qed.

  (* [comment removed for export] *)
  Lemma L_cksum : forall mm off sz tot mt1 res ipE remE h PFX (llt mlt oft huf pde expd pcs dsz bt stg le fe : word) xs ws
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
    ENV mm -> FRLB mm mt1 -> B_DCTX mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    0 <= fh_checksum h <= 1 ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    0 <= res <= CAP - tot -> off <= ipE -> ipE + remE <= size -> 0 <= remE < sz ->
    (forall ipF remF, (if fh_checksum h =? 0 then ipF = ipE /\ remF = remE else 4 <= remE /\ ipF = ipE + 4 /\ remF = remE - 4) ->
        forall r, dmulti src ipF remF (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r) ->
    KA_T sz ->
    evt psegs POST (STpc 0x157d8 mm y1 y5 y6 y7 (Z_to_bv 64 (DST + tot)) (Z_to_bv 64 sz) y10 y11 y12 y13 y14 y15 y16 y17
                       (Z_to_bv 64 (DCTX + 29912)) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 remE) (Z_to_bv 64 (SRC + ipE))
                       (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (DST + tot + res)) (Z_to_bv 64 0) (Z_to_bv 64 (-72)) (Z_to_bv 64 res) y28 y29 y30 y31).
  Proof.
    intros mm off sz tot mt1 res ipE remE h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws
           y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31
           ENm FRLm BDm RCK ROFF RSZ RT RMT ACC RRES RE1 RE2 RE3 FIN KA.
    pose proof (B_DCTX_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BDm) as DAm.
    destruct BDm as (_ & _ & FPm & _ & [XSCm XSSZm] & _ & [H5Cm H5Lm] & H5OKm & _).
    pose proof H5OKm as (_ & K_FICm & _). clear H5OKm.
    pose proof FRLm as FRLm'. unfold RZ_dmf_a.frl_cells in FRLm'. unfold zfh_cells in FPm.
    pose proof ENm as (_ & SBm & _ & _ & _ & _ & _ & _ & MIm).
    zs. zs. rewrite sx32w_small by lia. if_cases KC; zify_cond KC.
    - (* [comment removed for export] *)
      zs. zs. zs.
      eapply (L_tail mm off sz tot mt1 res ipE remE); try eassumption.
      apply FIN. rewrite KC. cbn [Z.eqb]. split; reflexivity.
    - zs. zs. if_cases K4; zify_cond K4.
      + h5_open ws H5Lm. unfold wz0 in *. subst b1. zs. zs. zs. if_false. zs.
        pose proof XSCm as [[XWF XBA] _].
        assert (XLEN : zlen (cells_bytes xs) = 88).
        { rewrite (cells_bytes_length _ XWF), XSSZm. reflexivity. }
        unfold PZD_XXH_DIGEST in XXHDIG.
        zs.
        call_pure (XXHDIG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (DCTX + 30008) (cells_bytes xs)).
        1: exact XBA. 1: exact XLEN. 1: lia. 1: lia. 1: exact MIm. 1: reflexivity.
        zlb SBm OK (ipE + 1). zlb SBm OK ipE. zlb SBm OK (ipE + 2). zlbs SBm OK (ipE + 3).
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_cases KM; clear KM.
        * zstep. zstep.
          replace (Z_to_bv 64 (-22)) with (Z_to_bv 64 (ZERR ZE_checksum_wrong)) by (apply Z_to_bv_eqm; reflexivity).
          eapply (L_errx2 mm off sz tot mt1 (ZERR ZE_checksum_wrong)); try eassumption.
          -- apply zd_is_error_ZERR. unfold ZE_checksum_wrong, ZE_maxCode. lia.
          -- unfold ZERR, ZE_checksum_wrong. lia.
        * zstep. zstep.
          replace (remE + -4) with (remE - 4) by lia.
          replace (SRC + ipE + 4) with (SRC + (ipE + 4)) by lia.
          eapply (L_tail mm off sz tot mt1 res (ipE + 4) (remE - 4)); try eassumption; try lia.
          apply FIN. replace (fh_checksum h =? 0) with false by (symmetry; apply Z.eqb_neq; exact KC).
          split; [lia|]. split; reflexivity.
      + (* [comment removed for export] *)
        zs. zs. zs.
        replace (Z_to_bv 64 (-22)) with (Z_to_bv 64 (ZERR ZE_checksum_wrong)) by (apply Z_to_bv_eqm; reflexivity).
        eapply (L_errx2 mm off sz tot mt1 (ZERR ZE_checksum_wrong)); try eassumption.
        * apply zd_is_error_ZERR. unfold ZE_checksum_wrong, ZE_maxCode. lia.
        * unfold ZERR, ZE_checksum_wrong. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma L_fend : forall mm off sz tot mt1 res ipE remE h PFX (llt mlt oft huf pde expd pcs dsz bt stg le fe : word) xs ws
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y25 y27 y28 y29 y30 y31 : word),
    ENV mm -> FRLB mm mt1 -> B_DCTX mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    0 <= fh_checksum h <= 1 -> 0 <= fh_fcs h < 2^64 ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    0 <= res <= CAP - tot -> off <= ipE -> ipE + remE <= size -> 0 <= remE < sz ->
    (forall ipF remF, (if fh_checksum h =? 0 then ipF = ipE /\ remF = remE else 4 <= remE /\ ipF = ipE + 4 /\ remF = remE - 4) ->
        (fh_fcs h <> ZD_CONTENTSIZE_UNKNOWN -> res = fh_fcs h) ->
        forall r, dmulti src ipF remF (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r) ->
    KA_T sz ->
    evt psegs POST (STpc 0x157ac mm y1 y5 y6 y7 (Z_to_bv 64 (DST + tot)) (Z_to_bv 64 sz) y10 y11 y12 y13 y14 y15 y16 y17
                       (Z_to_bv 64 (DCTX + 29912)) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 remE) (Z_to_bv 64 (SRC + ipE))
                       (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 (DST + tot + res)) y25 (Z_to_bv 64 (-72)) y27 y28 y29 y30 y31).
  Proof.
    intros mm off sz tot mt1 res ipE remE h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws
           y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y25 y27 y28 y29 y30 y31
           ENm FRLm BDm RCK RFCS ROFF RSZ RT RMT ACC RRES RE1 RE2 RE3 FIN KA.
    pose proof (B_DCTX_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BDm) as DAm.
    pose proof BDm as (_ & _ & FPm & _).
    pose proof FRLm as FRLm'. unfold RZ_dmf_a.frl_cells in FRLm'. unfold zfh_cells in FPm.
    change (2^64) with 18446744073709551616 in RFCS.
    zs. zs. replace (DST + tot + res - (DST + tot)) with res by lia.
    zs. zs. zs. if_cases KU; zify_cond KU.
    - eapply (L_cksum mm off sz tot mt1 res ipE remE h PFX); try eassumption.
      intros ipF remF CKC. apply FIN; [exact CKC|]. intros NE. exfalso. apply NE. unfold ZD_CONTENTSIZE_UNKNOWN. lia.
    - zs. if_cases KEQ; zify_cond KEQ.
      + eapply (L_cksum mm off sz tot mt1 res ipE remE h PFX); try eassumption.
        intros ipF remF CKC. apply FIN; [exact CKC|]. intros _. lia.
      + zs. zs. zs.
        replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (ZERR ZE_corruption_detected)) by (apply Z_to_bv_eqm; reflexivity).
        eapply (L_errx2 mm off sz tot mt1 (ZERR ZE_corruption_detected)); try eassumption.
        * apply zd_is_error_ZERR. unfold ZE_corruption_detected, ZE_maxCode. lia.
        * unfold ZERR, ZE_corruption_detected. lia.
  Qed.
End DMFB.
