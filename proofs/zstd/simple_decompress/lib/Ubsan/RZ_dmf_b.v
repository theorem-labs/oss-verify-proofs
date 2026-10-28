(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdFrameW ZdWalkKit ZdCellKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_libc_iface RZ_frame_iface RZ_block_iface RZ_dframe_iface RZ_dmf_a.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import frame_kit.
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
  Hypothesis GETFH : zd_getfh_stmt.
  Hypothesis XXHRESET : zd_xxh_reset_stmt.
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
  Hypothesis S_GT : 0x36e40 + 16 <= lo \/ SP <= 0x36e40.
  Hypothesis D_DC : DST + CAP <= DCTX \/ DCTX + 95992 <= DST.
  Hypothesis D_SR : DST + CAP <= SRC \/ SRC + zlen src <= DST.
  Hypothesis SR_DC : SRC + zlen src <= DCTX \/ DCTX + 95992 <= SRC.
  Hypothesis GT_DC : 0x36e40 + 16 <= DCTX \/ DCTX + 95992 <= 0x36e40.
  Hypothesis GT_DS : 0x36e40 + 16 <= DST \/ DST + CAP <= 0x36e40.

  Notation W := [(DCTX, DCTX + 95992); (DST, DST + CAP); (SP - 2368, SP)].
  Notation POST := (zd_dmf_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP DCTX DST CAP src size lo m).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -272)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Notation frl_cells := (RZ_dmf_a.frl_cells DCTX DST).
  Notation frh_cells := (RZ_dmf_a.frh_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation ENV := (RZ_dmf_a.ENV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SP lo DCTX DST CAP SRC src).
  Notation A_INV := (RZ_dmf_a.A_INV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SP lo DCTX DST CAP SRC src size).
  Notation ASt mm off sz tot mt1 x1 x5 x8 x11 x12 x13 x14 x26 x27 x28 x29 x30 x31 :=
    (STpc 0x155a8 mm x1 x5 (Z_to_bv 64 (-120)) (Z_to_bv 64 25481893) x8 (Z_to_bv 64 (DST + tot)) (Z_to_bv 64 5) x11 x12 x13 x14
          (Z_to_bv 64 5) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 sz) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 0)
          (Z_to_bv 64 mt1) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 4294967287) (Z_to_bv 64 (DCTX + 29928)) x26 x27 x28 x29 x30 x31).


  (* [comment removed for export] *)
  Hypothesis HRES : forall m1 off sz tot mt1 res sl0 sl1 sl2
      (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x26 x28 x29 x30 x31 : word),
    ENV m1 -> rw_cells usegs m1 (SP + -272) (frl_cells sl0 sl1 sl2 (Z_to_bv 64 mt1)) -> dctx_any m1 DCTX ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) -> 0 <= res < 2^64 ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    (zd_is_error res = false -> exists off' sz',
        x18 = Z_to_bv 64 sz' /\ x23 = Z_to_bv 64 (SRC + off') /\ res <= CAP - tot /\ off <= off' /\ off' + sz' <= size /\ 0 <= sz' < sz /\
        (forall r, dmulti src off' sz' (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r)) ->
    (forall m' off' sz' tot' (y1 y5 y8 y11 y12 y13 y14 y26 y27 y28 y29 y30 y31 : word), sz' < sz -> A_INV m' off' sz' tot' 1 ->
        evt usegs POST (ASt m' off' sz' tot' 1 y1 y5 y8 y11 y12 y13 y14 y26 y27 y28 y29 y30 y31)) ->
    evt usegs POST (STpc 0x15764 m1 x1 x5 x6 x7 x8 (Z_to_bv 64 (DST + tot)) x10 x11 x12 x13 x14 x15 x16 x17
                         x18 (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) x21 x22 x23 (Z_to_bv 64 res) (Z_to_bv 64 (DCTX + 29928))
                         x26 (Z_to_bv 64 (-72)) x28 x29 x30 x31).

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
    dctx_ptrs usegs m1 DCTX llt mlt oft huf /\
    dctx_h1 usegs m1 DCTX pde (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 0) expd /\
    rw_cells usegs m1 (DCTX + 29928) (zfh_cells h) /\
    dctx_h3 usegs m1 DCTX pcs dsz bt stg le fe /\
    dctx_xs usegs m1 DCTX xs /\ (fh_checksum h <> 0 -> exists j1 msz j2, xs = xxh_cells j1 msz j2 /\ 0 <= msz < 32) /\
    dctx_h5 usegs m1 DCTX ws /\ h5_frame_ok ws /\
    wnth ws H5_validateChecksum = Z_to_bv 64 (if fh_checksum h =? 0 then 0 else 1) /\
    wnth ws H5_isFrameDecompression = Z_to_bv 64 1 /\
    (exists jhb ovd dcb dce trace, dctx_tx usegs m1 DCTX jhb ovd dcb dce trace) /\
    dctx_owned usegs m1 DCTX /\
    TBL m1 DCTX llt mlt oft huf le fe.


  (* [comment removed for export] *)
  Definition FRAME_OK (off sz tot mt1 hsz : Z) (h : frame_header) : Prop :=
    0 <= off /\ off + sz <= size /\ 0 <= tot <= CAP /\ (mt1 = 0 \/ mt1 = 1) /\
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) /\
    9 <= sz /\ hsz = frame_header_size src off ZD_FRAMEHEADERSIZE_PREFIX /\ hsz + 3 <= sz /\
    is_skippable_magic (le32 src off) = false /\ get_frame_header src off hsz = FH_ok h.

  (* [comment removed for export] *)
  Definition KA_T (sz : Z) : Prop :=
    forall m' off' sz' tot' (y1 y5 y8 y11 y12 y13 y14 y26 y27 y28 y29 y30 y31 : word), sz' < sz -> A_INV m' off' sz' tot' 1 ->
        evt usegs POST (ASt m' off' sz' tot' 1 y1 y5 y8 y11 y12 y13 y14 y26 y27 y28 y29 y30 y31).

  Notation FRLB mm mt1 sl0 sl1 sl2 := (rw_cells usegs mm (SP + -272) (frl_cells sl0 sl1 sl2 (Z_to_bv 64 mt1))).

  Lemma B_DCTX_any : forall mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws,
    B_DCTX mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws -> dctx_any mm DCTX.
  Proof.
    intros mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws
           (A1 & A2 & A3 & A4 & A5 & _ & A6 & A7 & _ & _ & (j1 & j2 & j3 & j4 & j5 & A8) & A9 & _).
    exists llt, mlt, oft, huf, pde, (Z_to_bv 64 PFX), (Z_to_bv 64 PFX), (Z_to_bv 64 0), expd, (zfh_cells h), pcs, dsz, bt, stg, le, fe, xs, ws, j1, j2, j3, j4, j5.
    split; [exact A1|]. split; [exact A2|]. split; [split; [exact A3| reflexivity]|]. split; [exact A4|]. split; [exact A5|].
    split; [exact A6|]. split; [exact A7|]. split; [exact A8| exact A9].
  Qed.

  Lemma disjoint_from_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
  Proof.
    induction W as [|[l hh] W IH]; cbn; intros a n a' n' D L1 L2; [exact I|].
    destruct D as [D1 D2]. split; [lia|]. eapply IH; eauto.
  Qed.

  Lemma B_DCTX_transport : forall W' m1 m2 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws,
    B_DCTX m1 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    munch W' m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m1 -> mem_inv usegs m2 ->
    disjoint_from W' DCTX 95992 ->
    B_DCTX m2 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws.
  Proof.
    intros W' m1 m2 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws
           (PT & H1 & FP & H3 & [XSC XSSZ] & XSI & [H5C H5L] & H5OK & K_VCK & K_ISF & (jhb & ovd & dcb & dce & trace & TX) & [OWE OWX] & TB)
           MU WM MI1 MI2 DJ.
    assert (TR : forall A cs, rw_cells usegs m1 A cs -> DCTX <= A -> A + Z.of_nat (cells_size cs) <= DCTX + 95992 -> rw_cells usegs m2 A cs).
    { intros A cs RC L1 L2. eapply rw_cells_transport; [exact RC | exact MU | exact WM |]. eapply disjoint_from_sub; [exact DJ | lia | lia]. }
    assert (TS : forall a b, stk usegs m1 a b -> DCTX <= a -> a <= b -> b <= DCTX + 95992 -> stk usegs m2 a b).
    { intros a b SK L1 L2 L3. eapply stk_transport_disjoint; [exact SK | exact MU | exact WM |]. eapply disjoint_from_sub; [exact DJ | lia | lia]. }
    unfold dctx_ptrs, dctx_h1, dctx_h3, dctx_xs, dctx_h5, dctx_tx, dctx_owned in *.
    split; [apply TR; [exact PT | lia | cbn; lia]|].
    split; [apply TR; [exact H1 | lia | cbn; lia]|].
    split; [apply TR; [exact FP | lia | cbn; lia]|].
    split; [apply TR; [exact H3 | lia | cbn; lia]|].
    split; [split; [apply TR; [exact XSC | lia | rewrite XSSZ; lia]| exact XSSZ]|].
    split; [exact XSI|].
    split; [split; [apply TR; [exact H5C | lia | rewrite (h5_cells_size _ H5L); lia]| exact H5L]|].
    split; [exact H5OK|]. split; [exact K_VCK|]. split; [exact K_ISF|].
    split; [exists jhb, ovd, dcb, dce, trace; apply TR; [exact TX | lia | cbn; lia]|].
    split; [split; apply TS; try assumption; lia|].
    eapply (tbl_frame TBL TBLL m1 m2 W'); [exact TB | exact MU | exact MI1 | exact MI2 |].
    intros x Hx. eapply disjoint_outside; [exact DJ | lia].
  Qed.

  Ltac djb := cbn [disjoint_from]; simpl_sizes; repeat split; first [exact I | lia].

  Lemma digest_keep : forall mm m' mt1 sl0 sl1 sl2 h PFX (llt mlt oft huf pde expd pcs dsz bt stg le fe : word) xs ws,
    ENV mm -> FRLB mm mt1 sl0 sl1 sl2 -> B_DCTX mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    munch [(SP + -272 - 16, SP + -272)] mm m' -> wmono usegs mm m' -> mem_inv usegs m' -> stk usegs m' lo (SP + -272) ->
    ENV m' /\ FRLB m' mt1 sl0 sl1 sl2 /\ B_DCTX m' h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws.
  Proof.
    intros mm m' mt1 sl0 sl1 sl2 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws
           (GOT & SB & DSK & (csb & BPC & BSZ) & (jt & FRH) & ST & MU & WM & MI) FRL BD MU' WM' MI' ST'.
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    pose proof DSK as (DST0 & _ & _).
    split; [|split].
    - split; [eapply rw_cells_transport; [exact GOT | exact MU' | exact WM' | djb]|].
      split; [eapply bytes_at_transport; [exact SB | exact MU' | rewrite length_map; djb]|].
      split; [eapply stk_transport_disjoint; [exact DSK | exact MU' | exact WM' | djb]|].
      split; [exists csb; split; [eapply rw_cells_transport; [exact BPC | exact MU' | exact WM' | rewrite BSZ; djb] | exact BSZ]|].
      split; [exists jt; eapply rw_cells_transport; [exact FRH | exact MU' | exact WM' | unfold RZ_dmf_a.frh_cells; djb]|].
      split; [exact ST'|].
      split; [eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU']]; unfold sub_fp; cbn [outside]; intros; slia|].
      split; [eapply wmono_trans; [exact WM | exact WM'] | exact MI'].
    - eapply rw_cells_transport; [exact FRL | exact MU' | exact WM' | unfold RZ_dmf_a.frl_cells; djb].
    - eapply B_DCTX_transport; [exact BD | exact MU' | exact WM' | exact MI | exact MI' | djb].
  Qed.

  (* [comment removed for export] *)
  Lemma L_errx : forall mm off sz tot mt1 res sl0 sl1 sl2
      (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 y26 y28 y29 y30 y31 : word),
    ENV mm -> FRLB mm mt1 sl0 sl1 sl2 -> dctx_any mm DCTX ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    zd_is_error res = true -> 0 <= res < 2^64 -> KA_T sz ->
    evt usegs POST (STpc 0x15764 mm y1 y5 y6 y7 y8 (Z_to_bv 64 (DST + tot)) y10 y11 y12 y13 y14 y15 y16 y17 y18
                       (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) y21 y22 y23 (Z_to_bv 64 res) (Z_to_bv 64 (DCTX + 29928))
                       y26 (Z_to_bv 64 (-72)) y28 y29 y30 y31).
  Proof.
    intros mm off sz tot mt1 res sl0 sl1 sl2 y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 y26 y28 y29 y30 y31
           ENm FRLm DAm ROFF RSZ RT RMT ACC ERm RRm KA.
    eapply (HRES mm off sz tot mt1 res); try eassumption.
    intros NE. rewrite ERm in NE. discriminate NE.
  Qed.

  (* [comment removed for export] *)
  Lemma L_errx2 : forall mm off sz tot mt1 sl0 sl1 sl2
      (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 y24 y26 y28 y29 y30 y31 : word),
    ENV mm -> FRLB mm mt1 sl0 sl1 sl2 -> dctx_any mm DCTX ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    KA_T sz ->
    evt usegs POST (STpc 0x15760 mm y1 y5 y6 y7 y8 (Z_to_bv 64 (DST + tot)) y10 y11 y12 y13 y14 y15 y16 y17 y18
                       (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) y21 y22 y23 y24 (Z_to_bv 64 (DCTX + 29928))
                       y26 (Z_to_bv 64 (-72)) y28 y29 y30 y31).
  Proof.
    intros mm off sz tot mt1 sl0 sl1 sl2 y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 y24 y26 y28 y29 y30 y31
           ENm FRLm DAm ROFF RSZ RT RMT ACC KA.
    zs.
    first [ replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) at 1 by (apply Z_to_bv_eqm; reflexivity);
            eapply (L_errx mm off sz tot mt1 (ZERR ZE_srcSize_wrong))
          | replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (ZERR ZE_srcSize_wrong)) at 2 by (apply Z_to_bv_eqm; reflexivity);
            eapply (L_errx mm off sz tot mt1 (ZERR ZE_srcSize_wrong)) ]; try eassumption.
    - apply zd_is_error_ZERR. unfold ZE_srcSize_wrong, ZE_maxCode. lia.
    - unfold ZERR, ZE_srcSize_wrong. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma L_tail : forall mm off sz tot mt1 res ipF remF sl0 sl1 sl2
      (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y21 y23 y26 y28 y29 y30 y31 : word),
    ENV mm -> FRLB mm mt1 sl0 sl1 sl2 -> dctx_any mm DCTX ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    0 <= res <= CAP - tot -> off <= ipF -> ipF + remF <= size -> 0 <= remF < sz ->
    (forall r, dmulti src ipF remF (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r) ->
    KA_T sz ->
    evt usegs POST (STpc 0x15a58 mm y1 y5 y6 y7 y8 (Z_to_bv 64 (DST + tot)) y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 remF)
                       (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) y21 (Z_to_bv 64 (SRC + ipF)) y23 (Z_to_bv 64 res)
                       (Z_to_bv 64 (DCTX + 29928)) y26 (Z_to_bv 64 (-72)) y28 y29 y30 y31).
  Proof.
    intros mm off sz tot mt1 res ipF remF sl0 sl1 sl2 y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y21 y23 y26 y28 y29 y30 y31
           ENm FRLm DAm ROFF RSZ RT RMT ACC RRES RF1 RF2 RF3 STEP KA.
    pose proof FRLm as FRLm'. unfold RZ_dmf_a.frl_cells in FRLm'.
    pose proof ENm as (GOTm & _).
    zs. zs. unfold wz0. zs. if_true. zs. zs.
    assert (NE : zd_is_error res = false) by (apply zd_is_error_false_iff; change (2^64) with 18446744073709551616; lia).
    eapply (HRES mm off sz tot mt1 res); try eassumption.
    - change (2^64) with 18446744073709551616. lia.
    - intros _. exists ipF, remF. split; [reflexivity|]. split; [reflexivity|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. exact STEP.
  Qed.

  (* [comment removed for export] *)
  Lemma L_cksum : forall mm off sz tot mt1 res ipE remE h PFX (llt mlt oft huf pde expd pcs dsz bt stg le fe : word) xs ws sl0 sl1 sl2
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y23 y26 y28 y29 y30 y31 : word),
    ENV mm -> FRLB mm mt1 sl0 sl1 sl2 -> B_DCTX mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    0 <= fh_checksum h <= 1 ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    0 <= res <= CAP - tot -> off <= ipE -> ipE + remE <= size -> 0 <= remE < sz ->
    (forall ipF remF, (if fh_checksum h =? 0 then ipF = ipE /\ remF = remE else 4 <= remE /\ ipF = ipE + 4 /\ remF = remE - 4) ->
        forall r, dmulti src ipF remF (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r) ->
    KA_T sz ->
    evt usegs POST (STpc 0x159e0 mm y1 y5 y6 y7 (Z_to_bv 64 remE) (Z_to_bv 64 (DST + tot)) y10 y11 y12 y13 y14 y15 y16 y17
                       y18 (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) y21 (Z_to_bv 64 (SRC + ipE)) y23 (Z_to_bv 64 res)
                       (Z_to_bv 64 (DCTX + 29928)) y26 (Z_to_bv 64 (-72)) y28 y29 y30 y31).
  Proof.
    intros mm off sz tot mt1 res ipE remE h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws sl0 sl1 sl2
           y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y23 y26 y28 y29 y30 y31
           ENm FRLm BDm RCK ROFF RSZ RT RMT ACC RRES RE1 RE2 RE3 FIN KA.
    pose proof (B_DCTX_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BDm) as DAm.
    pose proof BDm as (_ & _ & FPm & _ & [XSCm XSSZm] & _ & [H5Cm H5Lm] & H5OKm & _).
    pose proof H5OKm as (_ & K_FICm & _). clear H5OKm.
    pose proof FRLm as FRLm'. unfold RZ_dmf_a.frl_cells in FRLm'. unfold zfh_cells in FPm.
    pose proof ENm as (_ & SBm & _ & _ & _ & STm & _ & _ & MIm).
    pose proof (bytes_at_bound _ _ _ _ SBm) as DB. rewrite length_map in DB.
    zs. zs. rewrite sx32w_small by lia. if_cases KC; zify_cond KC.
    - (* [comment removed for export] *)
      zs. zs.
      eapply (L_tail mm off sz tot mt1 res ipE remE); try eassumption.
      apply FIN. rewrite KC. cbn [Z.eqb]. split; reflexivity.
    - zs. zs. if_cases K4; zify_cond K4.
      + h5_open ws H5Lm. unfold wz0 in *. subst b1. zs. rewrite ?sx32w_small by lia. zs. if_false. zs.
        pose proof XSCm as [[XWF XBA] _].
        assert (XLEN : zlen (cells_bytes xs) = 88).
        { rewrite (cells_bytes_length _ XWF), XSSZm. reflexivity. }
        unfold PZD_XXH_DIGEST in XXHDIG.
        zs.
        eapply evt_cut; [eapply (XXHDIG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -272) (DCTX + 30008) (cells_bytes xs) lo) |].
        1: exact XBA. 1: exact XLEN. 1: lia. 1: lia. 1: lia. 1: exact STm. 1: exact RLO. 1: lia. 1: lia. 1: lia. 1: exact MIm. 1: reflexivity.
        intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & ST').
        lazymatch goal with
        | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
            replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
        end.
        pose proof (digest_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ENm FRLm BDm MU' WM' MI' ST') as (ENm' & FRLm2 & BDm2).
        pose proof (B_DCTX_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BDm2) as DAm'.
        pose proof ENm' as (_ & SBm' & _).
        clear SBm FRLm' MIm STm.
        zlb SBm' OK (ipE + 1). zlb SBm' OK ipE. zlb SBm' OK (ipE + 2). zlbs SBm' OK (ipE + 3).
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_cases KM; clear KM.
        * zstep. zstep.
          replace (Z_to_bv 64 (-22)) with (Z_to_bv 64 (ZERR ZE_checksum_wrong)) by (apply Z_to_bv_eqm; reflexivity).
          eapply (L_errx m' off sz tot mt1 (ZERR ZE_checksum_wrong)); try eassumption.
          -- apply zd_is_error_ZERR. unfold ZE_checksum_wrong, ZE_maxCode. lia.
          -- unfold ZERR, ZE_checksum_wrong. lia.
        * zstep. zstep. zstep. fck. zstep.
          replace (remE + -4) with (remE - 4) by lia.
          replace (SRC + ipE + 4) with (SRC + (ipE + 4)) by lia.
          eapply (L_tail m' off sz tot mt1 res (ipE + 4) (remE - 4)); try eassumption; try lia.
          apply FIN. replace (fh_checksum h =? 0) with false by (symmetry; apply Z.eqb_neq; exact KC).
          split; [lia|]. split; reflexivity.
      + (* [comment removed for export] *)
        zs. zs.
        replace (Z_to_bv 64 (-22)) with (Z_to_bv 64 (ZERR ZE_checksum_wrong)) by (apply Z_to_bv_eqm; reflexivity).
        eapply (L_errx mm off sz tot mt1 (ZERR ZE_checksum_wrong)); try eassumption.
        * apply zd_is_error_ZERR. unfold ZE_checksum_wrong, ZE_maxCode. lia.
        * unfold ZERR, ZE_checksum_wrong. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma L_fend : forall mm off sz tot mt1 res ipE remE h PFX (llt mlt oft huf pde expd pcs dsz bt stg le fe : word) xs ws sl0 sl1 sl2
      (y1 y5 y6 y7 y8 y10 y12 y14 y15 y16 y17 y18 y21 y23 y24 y26 y28 y29 y30 y31 : word),
    ENV mm -> FRLB mm mt1 sl0 sl1 sl2 -> B_DCTX mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    0 <= fh_checksum h <= 1 -> 0 <= fh_fcs h < 2^64 ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    0 <= res <= CAP - tot -> off <= ipE -> ipE + remE <= size -> 0 <= remE < sz ->
    (forall ipF remF, (if fh_checksum h =? 0 then ipF = ipE /\ remF = remE else 4 <= remE /\ ipF = ipE + 4 /\ remF = remE - 4) ->
        (fh_fcs h <> ZD_CONTENTSIZE_UNKNOWN -> res = fh_fcs h) ->
        forall r, dmulti src ipF remF (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r) ->
    KA_T sz ->
    evt usegs POST (STpc 0x159b8 mm y1 y5 y6 y7 y8 (Z_to_bv 64 (DST + tot)) y10 (Z_to_bv 64 remE) y12 (Z_to_bv 64 (DST + tot + res))
                       y14 y15 y16 y17 y18 (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) y21 (Z_to_bv 64 (SRC + ipE)) y23 y24
                       (Z_to_bv 64 (DCTX + 29928)) y26 (Z_to_bv 64 (-72)) y28 y29 y30 y31).
  Proof.
    intros mm off sz tot mt1 res ipE remE h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws sl0 sl1 sl2
           y1 y5 y6 y7 y8 y10 y12 y14 y15 y16 y17 y18 y21 y23 y24 y26 y28 y29 y30 y31
           ENm FRLm BDm RCK RFCS ROFF RSZ RT RMT ACC RRES RE1 RE2 RE3 FIN KA.
    pose proof (B_DCTX_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BDm) as DAm.
    pose proof BDm as (_ & _ & FPm & _).
    pose proof FRLm as FRLm'. unfold RZ_dmf_a.frl_cells in FRLm'. unfold zfh_cells in FPm.
    change (2^64) with 18446744073709551616 in RFCS.
    zs. zs. zs. replace (DST + tot + res - (DST + tot)) with res by lia.
    zs. zs. if_cases KU; zify_cond KU.
    - eapply (L_cksum mm off sz tot mt1 res ipE remE h PFX); try eassumption.
      intros ipF remF CKC. apply FIN; [exact CKC|]. intros NE. exfalso. apply NE. unfold ZD_CONTENTSIZE_UNKNOWN. lia.
    - zs. if_cases KEQ; zify_cond KEQ.
      + eapply (L_cksum mm off sz tot mt1 res ipE remE h PFX); try eassumption.
        intros ipF remF CKC. apply FIN; [exact CKC|]. intros _. lia.
      + zs. zs.
        replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (ZERR ZE_corruption_detected)) by (apply Z_to_bv_eqm; reflexivity).
        eapply (L_errx mm off sz tot mt1 (ZERR ZE_corruption_detected)); try eassumption.
        * apply zd_is_error_ZERR. unfold ZE_corruption_detected, ZE_maxCode. lia.
        * unfold ZERR, ZE_corruption_detected. lia.
  Qed.

  Definition B_HEAD (off sz tot mt1 : Z) (h : frame_header) (PFX ipb rem o : Z) : Prop :=
    forall m1 cbs bp (llt mlt oft huf pde expd pcs dsz bt stg le fe : word) (xs : list cell) (ws : list word) (sl0 sl1 : word)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x28 x29 x30 x31 : word),
      ENV m1 -> FRLB m1 mt1 sl0 sl1 (Z_to_bv 64 (DST + tot + o)) -> rw_cells usegs m1 (SP + -168) (bp_cells bp) ->
      B_DCTX m1 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
      get_cblock_size src ipb rem = Some (cbs, bp) -> zd_is_error cbs = false ->
      evt usegs POST (STpc 0x15860 m1 x1 x5 x6 x7 (Z_to_bv 64 (DST + CAP)) (Z_to_bv 64 (DST + tot)) x10 x11 x12 x13 x14 x15 x16 x17
                           x18 (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 cbs) (Z_to_bv 64 (SRC + ipb))
                           x23 x24 (Z_to_bv 64 (DCTX + 29928)) (Z_to_bv 64 rem) (Z_to_bv 64 (-72)) x28 x29 x30 x31).
End DMFB.
