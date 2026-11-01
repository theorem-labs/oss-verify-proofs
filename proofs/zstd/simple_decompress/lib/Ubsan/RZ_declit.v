(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdLit.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit ZdDctxRep SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memset F_memmove RZ_libc_stk RZ_frame_iface RZ_huf_iface RZ_block_iface
     RZ_blk_iface4 RZ_blk_iface5 RZ_alloclit RZ_huf_reg RZ_hufinv seqH_kit seqH_kit_lit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_hide segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_hide segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_hide segs m m' MU WM.

(* [comment removed for export] *)
Definition dl_hyps (SPV lo DCTX DST CAP B0 B1 LSRC slen : Z) : Prop :=
  4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ DCTX mod 8 = 0 /\ 0 <= slen <= 131072 /\ 4096 <= LSRC /\ LSRC + slen < 2^47
  /\ B0 <= DST /\ DST + CAP <= B1 /\ 0 <= CAP /\ B1 < 2^47 /\ (DST = 0 -> CAP = 0) /\ (DST <> 0 -> 4096 <= B0)
  /\ 4096 <= lo /\ lo <= SPV - 1184 /\ SPV < 2^47
  /\ (DCTX + 95992 <= lo \/ SPV <= DCTX) /\ (B1 <= lo \/ SPV <= B0) /\ (LSRC + slen <= lo \/ SPV <= LSRC)
  /\ (B1 <= DCTX \/ DCTX + 95992 <= B0) /\ (B1 <= LSRC \/ LSRC + slen <= B0) /\ (LSRC + slen <= DCTX \/ DCTX + 95992 <= LSRC).
Ltac open_dlh HY := pose proof HY as (DCL & DCH & DCA & SLEN & SRCL & SRCH & B0D & DCB & CAP0 & B1H & DNULL & DNN & LO0 & LOS & SPH
                                      & OFFD & OFFB & OFFSRC & BD & BSRC & SRCD);
  (* [comment removed for export] *)
  lazymatch type of B0D with _ <= ?DSTv =>
    lazymatch type of DCB with _ + ?CAPv <= _ =>
      lazymatch type of OFFB with _ <= ?lov \/ ?SPVv <= _ =>
        lazymatch type of BD with _ <= ?DCTXv \/ _ =>
          lazymatch type of BSRC with _ <= ?LSRCv \/ _ + ?slenv <= _ =>
            assert (OFFDST : DSTv + CAPv <= lov \/ SPVv <= DSTv) by (clear - OFFB B0D DCB; lia);
            assert (DSTD : DSTv + CAPv <= DCTXv \/ DCTXv + 95992 <= DSTv) by (clear - BD B0D DCB; lia);
            assert (DSTSRC : DSTv + CAPv <= LSRCv \/ LSRCv + slenv <= DSTv) by (clear - BSRC B0D DCB; lia)
          end end end end end;
  hide_all_disj.

(* [comment removed for export] *)
Lemma sx32_nz_mod : forall w : word, bv_unsigned (sx32 w) <> 0 -> bv_unsigned w mod 4294967296 <> 0.
Proof.
  intros w H E. apply H. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with 18446744073709551616 in R.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
  Lemma stk_bytes_u8arr : forall (m1 : fmem) a (bs : list byte), stk usegs m1 a (a + Z.of_nat (length bs)) -> bytes_at usegs m1 a bs -> u8arr usegs m1 a bs.
  Proof.
    intros m1 a bs (Base & Top & Room) Bytes.
    split; [exact Bytes|].
    refine (conj Base (conj Top _)).
    intros off OffIn.
    exact (proj1 (Room (a + off) ltac:(lia))).
  Qed.

  Lemma u8arr_stk : forall (m1 : fmem) a (bs : list byte), u8arr usegs m1 a bs -> stk usegs m1 a (a + Z.of_nat (length bs)).
  Proof.
    intros m1 a bs [(Base & Top & Reads) (_ & _ & Writable)].
    refine (conj Base (conj Top _)).
    intros x XIn.
    pose (k := Z.to_nat (x - a)).
    assert (AtK : x = a + Z.of_nat k) by (unfold k; lia).
    split.
    - replace x with (a + (x - a)) by lia. apply Writable. lia.
    - rewrite AtK, (Reads k ltac:(unfold k; lia)).
      destruct (nth_error bs k) as [b|] eqn:Pick; [exists b; reflexivity|].
      apply nth_error_None in Pick. unfold k in Pick. lia.
  Qed.

  Lemma bytes_at_mid : forall (m1 : fmem) A (bs : list byte) i n, bytes_at usegs m1 A bs -> 0 <= i -> 0 <= n -> i + n <= Z.of_nat (length bs) ->
    bytes_at usegs m1 (A + i) (firstn (Z.to_nat n) (skipn (Z.to_nat i) bs)) /\ Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat i) bs))) = n.
  Proof.
    intros m1 A bs i n Whole Ipos Npos Fits.
    set (tail := skipn (Z.to_nat i) bs).
    assert (TailLen : length tail = (length bs - Z.to_nat i)%nat) by (unfold tail; apply length_skipn).
    assert (PieceLen : zlen (firstn (Z.to_nat n) tail) = n) by (rewrite firstn_length_le; lia).
    split; [|exact PieceLen].
    rewrite <- (firstn_skipn (Z.to_nat i) bs) in Whole.
    apply bytes_at_app in Whole as [_ AfterI].
    rewrite firstn_length_le in AfterI by lia.
    rewrite Z2Nat.id in AfterI by lia.
    fold tail in AfterI.
    rewrite <- (firstn_skipn (Z.to_nat n) tail) in AfterI.
    exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) AfterI)).
  Qed.

  (* [comment removed for export] *)
  Lemma h5_isf_cell : forall (m1 : fmem) D wsq, dctx_h5 usegs m1 D wsq -> rw_cells usegs m1 (D + 30176) [C4 (wnth wsq H5_isFrameDecompression)].
  Proof.
    intros m1 D wsq (Block & Count).
    h5_open wsq Count.
    lazymatch type of Block with
    | rw_cells _ _ _ ?row =>
        let front := eval cbn [firstn] in (firstn 12 row) in
        let back := eval cbn [skipn] in (skipn 12 row) in
        change row with (front ++ back) in Block
    end.
    apply rw_cells_app in Block as [_ Rest].
    lazymatch type of Rest with
    | rw_cells _ _ _ (?c :: ?more) => change (c :: more) with ([c] ++ more) in Rest
    end.
    apply rw_cells_app in Rest as [Flag _].
    cbn [cells_size csize Nat.add] in Flag.
    replace (D + 30096 + Z.of_nat 80) with (D + 30176) in Flag by lia.
    exact Flag.
  Qed.

Section DL.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DCTX DST CAP B0 B1 LSRC : Z) (src : list Z) (h : frame_header) (llt mlt oft pcs dsz bt stg fe : word) (ws : list word).
  Hypothesis HY : dl_hyps SPV lo DCTX DST CAP B0 B1 LSRC (Z.of_nat (length src)).
  Hypothesis FBY : Forall (fun c => 0 <= c < 256) src.
  Hypothesis BSM : 0 <= fh_bsmax h <= 131072.
  Hypothesis SPA : SPV mod 16 = 0.
  Notation POST := (zd_declit_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST CAP B0 B1 LSRC (Z.of_nat (length src))
                                   llt mlt oft pcs dsz bt stg fe ws lo m).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -96)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FOOT := [(DST, DST + CAP); (DCTX + 24, DCTX + 32); (DCTX + 10296, DCTX + 26684); (DCTX + 27324, DCTX + 29884);
                    (DCTX + 30000, DCTX + 30004); (DCTX + 30096, DCTX + 95940); (SPV - 1184, SPV)].

  (* [comment removed for export] *)
  Definition DLB (hufv lev : word) (wsv : list word) (m1 : fmem) : Prop :=
    dctx_ptrs usegs m1 DCTX llt mlt oft hufv
    /\ stk usegs m1 (DCTX + 10296) (DCTX + 26684)
    /\ stk usegs m1 (DCTX + 27324) (DCTX + 29884)
    /\ rw_cells usegs m1 (DCTX + 29928) (zfh_cells h)
    /\ dctx_h3 usegs m1 DCTX pcs dsz bt stg lev fe
    /\ dctx_h5 usegs m1 DCTX wsv
    /\ stk usegs m1 (DCTX + 30372) (DCTX + 95940)
    /\ bytes_at usegs m1 LSRC (map (Z_to_bv 8) src)
    /\ stk usegs m1 B0 B1
    /\ stk usegs m1 lo (SPV + -96)
    /\ (exists pad, rw_cells usegs m1 (SPV + -96)
                      [CB 8 pad; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ mem_inv usegs m1
    /\ munch FOOT m m1
    /\ wmono usegs m m1.
  Ltac open_dlb I := destruct I as (PTRS & EHUF & EWK & FP & H3 & H5 & XB & SRCB & BUF & STK & (j & FR) & MI & MU & WM);
                     unfold dctx_ptrs in PTRS; unfold dctx_h3 in H3; unfold zfh_cells in FP.

  (* [comment removed for export] *)
  Lemma dl_ret : forall m1 hufv lev wsv r xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> 0 <= r < 2^64 -> xa7 = Z_to_bv 64 r ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    (zd_is_error r = true
     \/ (1 <= r <= Z.of_nat (length src) /\ HUFINVw m1 DCTX hufv lev /\ declit_placed DCTX DST CAP LSRC (Z.of_nat (length src)) wsv)) ->
    evt usegs POST (ST 0x16750 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I HR -> KEEP RES. open_dlb I. open_dlh HY.
    zstep. do 11 zstep. zstep.
    release_frame FR STK SPV.
    zstep. apply evt_done. unfold zd_declit_post.
    do 14 eexists. exists m1, r, hufv, lev, wsv.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|]. split; [exact BUF|].
    split; [exact PTRS|]. split; [exact EHUF|]. split; [exact EWK|]. split; [exact H3|]. split; [exact H5|]. split; [exact KEEP|].
    split; [exact XB|]. split; [exact HR| exact RES].
  Qed.
  Ltac cells_words cs :=
    lazymatch cs with
    | nil => constr:(@nil word)
    | C8 ?w :: ?r => let t := cells_words r in constr:(w :: t)
    | C4 ?w :: ?r => let t := cells_words r in constr:(w :: t)
    end.

  (* [comment removed for export] *)
  Lemma dl_raw : forall m1 hufv lev wsv litSize lhSize dtb xra x7 xa6 xs1 xs4 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    bytes_at usegs m1 (DCTX + 10296) dtb -> huf_hdr_ok dtb -> (bv_unsigned lev mod 2^32 <> 0 -> huf_tbl_ok dtb) -> hufv = Z_to_bv 64 (DCTX + 10296) ->
    1 <= lhSize <= 3 -> 0 <= litSize < 2^20 -> (DST = 0 -> litSize = 0) ->
    evt usegs POST (ST 0x1698c m1 xra (Z_to_bv 64 (Z.min (fh_bsmax h) CAP)) (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 litSize) xs1
                       (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (Z.of_nat (length src))) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                       xa6 (Z_to_bv 64 (-70)) (Z_to_bv 64 (DCTX + 30120)) (Z_to_bv 64 (DCTX + 29944)) xs4 (Z_to_bv 64 lhSize) xs6 xs7 xs8 xs9 x28 x29 x30 x31).
  Proof using HY BSM SPA.
    intros until x31. intros Bund IsFrame Keep HufB HufH HufT HufP LhR LitR NullLit.
    pose proof Bund as Whole.
    open_dlb Bund. open_dlh HY.
    destruct H5 as [H5c H5n]. revert Keep IsFrame. h5_open wsv H5n. intros Keep IsFrame.
    subst.
    pose proof (proj1 HufH) as TblLen. unfold HUF_DTABLE_BYTES in TblLen.
    zstep. if_cases TooBig; zify_cond TooBig.
    { zstep. eapply (dl_ret m1 _ lev _ (2^64 - 20)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity]. }
    zstep. if_cases NoRoom; zify_cond NoRoom.
    { eapply (dl_ret m1 _ lev _ (2^64 - 70)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity]. }
    do 10 zstep.
    pose proof zd_alloclit_proof as Alloc. unfold zd_alloclit_stmt in Alloc.
    lazymatch goal with Cells : rw_cells _ ?mm (DCTX + 30096) ?cs |- _ =>
      let wl := cells_words cs in
      eapply evt_cut;
      [ eapply Alloc with (SPV := SPV + -96) (DCTX := DCTX) (DST := DST) (CAP := CAP) (litSize := litSize)
                          (ews := Z.min (fh_bsmax h) CAP) (imm := true) (h := h) (ws := wl)
      | unfold zd_alloclit_post, DCTX_litBuffer; post_call usegs mm ] end.
    all: first [ exact FP | exact BSM | exact MI | (split; [exact H5c | reflexivity]) | reflexivity | assumption | lia | idtac ].
    rename POST into Placed.
    remember (alloc_lit_buffer (fh_bsmax h) CAP litSize (Z.min (fh_bsmax h) CAP) true) as Plc eqn:PlcDef.
    destruct Placed as [H5c H5n].
    cbv beta iota delta [h5_placed wupd h5_cells mk_wcells h5_sizes H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in H5c.
    do 4 zstep. if_cases Direct; zify_cond Direct.
    - zstep. zstep. uckb. do 4 zstep. zstep. uckb. do 5 zstep.
      lazymatch goal with Cells : rw_cells _ ?mm (DCTX + 30096) ?cs |- _ =>
        let wl := cells_words cs in
        eapply (dl_ret mm (Z_to_bv 64 (DCTX + 10296)) lev wl (lhSize + litSize)) end.
      all: try lia.
      all: try reflexivity.
      all: try (apply bv_eq; reflexivity).
      all: try (hnf; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ eq_refl) (conj _ (conj _ (conj _ (conj _
                  (conj (ex_intro _ _ _) (conj _ (conj _ _))))))))))))); eassumption).
      all: try (intros idx Owned; etransitivity; [|exact (Keep idx Owned)];
                do 44 (destruct idx as [|idx]; [first [discriminate Owned | reflexivity] |]); reflexivity).
      all: first [ left; reflexivity
                 | right; split; [lia|]; split;
                   [ apply (hufw_of_full _ _ _ _ dtb); [reflexivity | assumption | assumption | assumption]
                   | unfold declit_placed; do 5 eexists; do 5 (split; [reflexivity|]);
                     unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, DCTX_litExtraBuffer, ZSTD_LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH;
                     lia ] ].
    - zstep. zstep. if_cases Short; zify_cond Short.
      + lazymatch goal with Cells : rw_cells _ ?mm (DCTX + 30096) ?cs |- _ =>
          let wl := cells_words cs in
          eapply (dl_ret mm (Z_to_bv 64 (DCTX + 10296)) lev wl (2^64 - 20)) end.
        all: try lia.
        all: try reflexivity.
        all: try (apply bv_eq; reflexivity).
        all: try (hnf; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ eq_refl) (conj _ (conj _ (conj _ (conj _
                    (conj (ex_intro _ _ _) (conj _ (conj _ _))))))))))))); eassumption).
        all: try (intros idx Owned; etransitivity; [|exact (Keep idx Owned)];
                  do 44 (destruct idx as [|idx]; [first [discriminate Owned | reflexivity] |]); reflexivity).
        all: first [ left; reflexivity
                   | right; split; [lia|]; split;
                     [ apply (hufw_of_full _ _ _ _ dtb); [reflexivity | assumption | assumption | assumption]
                     | unfold declit_placed; do 5 eexists; do 5 (split; [reflexivity|]);
                       unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, DCTX_litExtraBuffer, ZSTD_LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH;
                       lia ] ].
      + pose proof (alloc_lit_buffer_regions (fh_bsmax h) CAP litSize (Z.min (fh_bsmax h) CAP) true ltac:(lia) eq_refl
                      ltac:(unfold ZSTD_BLOCKSIZE_MAX; lia)) as Shape.
        cbv zeta in Shape. rewrite <- PlcDef in Shape.
        unfold ZSTD_in_dst, ZSTD_split, ZSTD_not_in_dst, WILDCOPY_OVERLENGTH, ZSTD_LITBUFFEREXTRASIZE in Shape.
        destruct (lp_base Plc) eqn:BaseK; [destruct Shape as [InDst | Spl] | | contradiction];
          cbn [lit_base_addr] in H5c.
        * destruct InDst as (LocIs & BufIs & EndIs & EndRoom).
          rewrite LocIs, BufIs in H5c. rewrite EndIs, BufIs in H5c.
          do 3 zstep. rewrite (sx32w_small 1) by lia. if_true.
          zstep. zstep. uckb. do 4 zstep.
          destruct (stk_split usegs _ B0 (DST + (fh_bsmax h + 32)) B1 BUF ltac:(lia)) as [BufLo BufRest].
          destruct (stk_split usegs _ (DST + (fh_bsmax h + 32)) (DST + (fh_bsmax h + 32) + litSize) B1 BufRest ltac:(lia))
            as [BufMid BufHi].
          pose proof (rdbl_sub usegs _ _ _ (LSRC + lhSize) (LSRC + lhSize + litSize) (rdbl_of_bytes_at usegs _ _ _ SRCB)
                        ltac:(lia) ltac:(rewrite length_map; lia)) as SrcRd.
          clear BUF BufRest.
          call (memcpy_stk (DST + (fh_bsmax h + 32)) (LSRC + lhSize) litSize).
          { exact BufMid. }
          { exact SrcRd. }
          all: try lia.
          all: try (unfold hidden in DSTSRC; lia).
          all: try assumption.
          all: try reflexivity.
          rename POST into BufMid.
          pose proof (stk_merge usegs _ _ _ _ (stk_merge usegs _ _ _ _ BufLo BufMid ltac:(lia)) BufHi ltac:(lia)) as BUF.
          clear BufLo BufMid BufHi.
          do 5 zstep.
          lazymatch goal with Cells : rw_cells _ ?mm (DCTX + 30096) ?cs |- _ =>
            let wl := cells_words cs in
            eapply (dl_ret mm (Z_to_bv 64 (DCTX + 10296)) lev wl (lhSize + litSize)) end.
          all: try lia.
          all: try reflexivity.
          all: try (apply bv_eq; reflexivity).
          all: try (hnf; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ eq_refl) (conj _ (conj _ (conj _ (conj _
                      (conj (ex_intro _ _ _) (conj _ (conj _ _))))))))))))); eassumption).
          all: try (intros idx Owned; etransitivity; [|exact (Keep idx Owned)];
                    do 44 (destruct idx as [|idx]; [first [discriminate Owned | reflexivity] |]); reflexivity).
          all: first [ left; reflexivity
                     | right; split; [lia|]; split;
                       [ apply (hufw_of_full _ _ _ _ dtb); [reflexivity | assumption | assumption | assumption]
                       | unfold declit_placed; do 5 eexists; do 5 (split; [reflexivity|]);
                         unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, DCTX_litExtraBuffer, ZSTD_LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH;
                         lia ] ].
        * destruct Spl as (LocIs & BigLit & BufPos & EndRel & EwsCap). destruct EndRel as [EndIs EndEws].
          rewrite LocIs in H5c.
          do 3 zstep. rewrite (sx32w_small 2) by lia. if_false.
          zstep. zstep. uck. do 5 zstep.
          destruct (stk_split usegs _ B0 (DST + lp_buf Plc) B1 BUF ltac:(lia)) as [BufLo BufRest].
          destruct (stk_split usegs _ (DST + lp_buf Plc) (DST + lp_buf Plc + (litSize + -65536)) B1 BufRest ltac:(lia))
            as [BufMid BufHi].
          pose proof (rdbl_sub usegs _ _ _ (LSRC + lhSize) (LSRC + lhSize + (litSize + -65536)) (rdbl_of_bytes_at usegs _ _ _ SRCB)
                        ltac:(lia) ltac:(rewrite length_map; lia)) as SrcRd.
          clear BUF BufRest.
          call (memcpy_stk (DST + lp_buf Plc) (LSRC + lhSize) (litSize + -65536)).
          { exact BufMid. }
          { exact SrcRd. }
          all: try lia.
          all: try (unfold hidden in DSTSRC; lia).
          all: try assumption.
          all: try reflexivity.
          rename POST into BufMid.
          pose proof (stk_merge usegs _ _ _ _ (stk_merge usegs _ _ _ _ BufLo BufMid ltac:(lia)) BufHi ltac:(lia)) as BUF.
          clear BufLo BufMid BufHi SrcRd.
          zstep. uck. zstep. zstep. uckb. do 3 zstep. uck. zstep. zstep. uckb. do 8 zstep.
          destruct (stk_split usegs _ (DCTX + 30372) (DCTX + 30372 + 65536) (DCTX + 95940) XB ltac:(lia)) as [ExtraLo ExtraHi].
          pose proof (rdbl_sub usegs _ _ _ (LSRC + lhSize + litSize + -65536) (LSRC + lhSize + litSize + -65536 + 65536)
                        (rdbl_of_bytes_at usegs _ _ _ SRCB) ltac:(lia) ltac:(rewrite length_map; lia)) as SrcRd.
          clear XB.
          call (memcpy_stk (DCTX + 30372) (LSRC + lhSize + litSize + -65536) 65536).
          { exact ExtraLo. }
          { exact SrcRd. }
          all: try lia.
          all: try (unfold hidden in SRCD; lia).
          all: try assumption.
          all: try reflexivity.
          rename POST into ExtraLo.
          pose proof (stk_merge usegs _ _ _ _ ExtraLo ExtraHi ltac:(lia)) as XB.
          clear ExtraLo ExtraHi.
          do 5 zstep.
          lazymatch goal with Cells : rw_cells _ ?mm (DCTX + 30096) ?cs |- _ =>
            let wl := cells_words cs in
            eapply (dl_ret mm (Z_to_bv 64 (DCTX + 10296)) lev wl (lhSize + litSize)) end.
          all: try lia.
          all: try reflexivity.
          all: try (apply bv_eq; reflexivity).
          all: try (hnf; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ eq_refl) (conj _ (conj _ (conj _ (conj _
                      (conj (ex_intro _ _ _) (conj _ (conj _ _))))))))))))); eassumption).
          all: try (intros idx Owned; etransitivity; [|exact (Keep idx Owned)];
                    do 44 (destruct idx as [|idx]; [first [discriminate Owned | reflexivity] |]); reflexivity).
          all: first [ left; reflexivity
                     | right; split; [lia|]; split;
                       [ apply (hufw_of_full _ _ _ _ dtb); [reflexivity | assumption | assumption | assumption]
                       | unfold declit_placed; do 5 eexists; do 5 (split; [reflexivity|]);
                         unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, DCTX_litExtraBuffer, ZSTD_LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH;
                         lia ] ].
        * destruct Shape as (LocIs & BufIs & EndIs & SmallLit).
          unfold DCTX_litExtraBuffer in H5c. rewrite LocIs, BufIs, EndIs, Z.add_0_r in H5c.
          do 3 zstep. rewrite (sx32w_small 0) by lia. if_true.
          zstep. zstep. uckb. do 4 zstep.
          destruct (stk_split usegs _ (DCTX + 30372) (DCTX + 30372 + litSize) (DCTX + 95940) XB ltac:(lia)) as [ExtraLo ExtraHi].
          pose proof (rdbl_sub usegs _ _ _ (LSRC + lhSize) (LSRC + lhSize + litSize) (rdbl_of_bytes_at usegs _ _ _ SRCB)
                        ltac:(lia) ltac:(rewrite length_map; lia)) as SrcRd.
          clear XB.
          call (memcpy_stk (DCTX + 30372) (LSRC + lhSize) litSize).
          { exact ExtraLo. }
          { exact SrcRd. }
          all: try lia.
          all: try (unfold hidden in SRCD; lia).
          all: try assumption.
          all: try reflexivity.
          rename POST into ExtraLo.
          pose proof (stk_merge usegs _ _ _ _ ExtraLo ExtraHi ltac:(lia)) as XB.
          clear ExtraLo ExtraHi.
          do 5 zstep.
          lazymatch goal with Cells : rw_cells _ ?mm (DCTX + 30096) ?cs |- _ =>
            let wl := cells_words cs in
            eapply (dl_ret mm (Z_to_bv 64 (DCTX + 10296)) lev wl (lhSize + litSize)) end.
          all: try lia.
          all: try reflexivity.
          all: try (apply bv_eq; reflexivity).
          all: try (hnf; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ eq_refl) (conj _ (conj _ (conj _ (conj _
                      (conj (ex_intro _ _ _) (conj _ (conj _ _))))))))))))); eassumption).
          all: try (intros idx Owned; etransitivity; [|exact (Keep idx Owned)];
                    do 44 (destruct idx as [|idx]; [first [discriminate Owned | reflexivity] |]); reflexivity).
          all: first [ left; reflexivity
                     | right; split; [lia|]; split;
                       [ apply (hufw_of_full _ _ _ _ dtb); [reflexivity | assumption | assumption | assumption]
                       | unfold declit_placed; do 5 eexists; do 5 (split; [reflexivity|]);
                         unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, DCTX_litExtraBuffer, ZSTD_LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH;
                         lia ] ].
  Qed.

  (* [comment removed for export] *)
  Lemma dl_rle_b : forall m1 hufv lev wsv litSize lhSize dtb xra x7 xa2 xa6 xa7 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    bytes_at usegs m1 (DCTX + 10296) dtb -> huf_hdr_ok dtb -> (bv_unsigned lev mod 2^32 <> 0 -> huf_tbl_ok dtb) -> hufv = Z_to_bv 64 (DCTX + 10296) ->
    1 <= lhSize <= 3 -> lhSize + 1 <= Z.of_nat (length src) -> 0 <= litSize < 2^20 -> (DST = 0 -> litSize = 0) ->
    evt usegs POST (ST 0x16a4c m1 xra (Z_to_bv 64 (Z.min (fh_bsmax h) CAP)) (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 litSize) (Z_to_bv 64 lhSize)
                       (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) xa2 (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                       xa6 xa7 (Z_to_bv 64 (DCTX + 30120)) (Z_to_bv 64 (DCTX + 29944)) xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31).
  Proof using HY FBY BSM SPA.
    intros until x31. intros Bund IsFrame Keep HufB HufH HufT HufP LhR LhFit LitR NullLit.
    pose proof Bund as Whole.
    open_dlb Bund. open_dlh HY.
    destruct H5 as [H5c H5n]. revert Keep IsFrame. h5_open wsv H5n. intros Keep IsFrame.
    subst.
    pose proof (proj1 HufH) as TblLen. unfold HUF_DTABLE_BYTES in TblLen.
    pose proof (Forall_Znth (fun c => 0 <= c < 256) src lhSize FBY ltac:(lia)) as RleByte. cbv beta in RleByte.
    zstep. zstep. if_cases TooBig; zify_cond TooBig.
    { eapply (dl_ret m1 _ lev _ (2^64 - 20)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity]. }
    zstep. zstep. if_cases NoRoom; zify_cond NoRoom.
    { eapply (dl_ret m1 _ lev _ (2^64 - 70)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity]. }
    do 9 zstep.
    pose proof zd_alloclit_proof as Alloc. unfold zd_alloclit_stmt in Alloc.
    lazymatch goal with Cells : rw_cells _ ?mm (DCTX + 30096) ?cs |- _ =>
      let wl := cells_words cs in
      eapply evt_cut;
      [ eapply Alloc with (SPV := SPV + -96) (DCTX := DCTX) (DST := DST) (CAP := CAP) (litSize := litSize)
                          (ews := Z.min (fh_bsmax h) CAP) (imm := true) (h := h) (ws := wl)
      | unfold zd_alloclit_post, DCTX_litBuffer; post_call usegs mm ] end.
    all: first [ exact FP | exact BSM | exact MI | (split; [exact H5c | reflexivity]) | reflexivity | assumption | lia | idtac ].
    rename POST into Placed.
    remember (alloc_lit_buffer (fh_bsmax h) CAP litSize (Z.min (fh_bsmax h) CAP) true) as Plc eqn:PlcDef.
    destruct Placed as [H5c H5n].
    cbv beta iota delta [h5_placed wupd h5_cells mk_wcells h5_sizes H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in H5c.
    pose proof (alloc_lit_buffer_regions (fh_bsmax h) CAP litSize (Z.min (fh_bsmax h) CAP) true ltac:(lia) eq_refl
                  ltac:(unfold ZSTD_BLOCKSIZE_MAX; lia)) as Shape.
    cbv zeta in Shape. rewrite <- PlcDef in Shape.
    unfold ZSTD_in_dst, ZSTD_split, ZSTD_not_in_dst, WILDCOPY_OVERLENGTH, ZSTD_LITBUFFEREXTRASIZE in Shape.
    destruct (lp_base Plc) eqn:BaseK; [destruct Shape as [InDst | Spl] | | contradiction];
      cbn [lit_base_addr] in H5c.
    - destruct InDst as (LocIs & BufIs & EndIs & EndRoom).
      rewrite LocIs, BufIs in H5c. rewrite EndIs, BufIs in H5c.
      do 6 zstep. rewrite (sx32w_small 1) by lia. if_true.
      zstep. zstep. uckb. zlb SRCB FBY lhSize. zstep. zstep.
      destruct (stk_split usegs _ B0 (DST + (fh_bsmax h + 32)) B1 BUF ltac:(lia)) as [BufLo BufRest].
      destruct (stk_split usegs _ (DST + (fh_bsmax h + 32)) (DST + (fh_bsmax h + 32) + litSize) B1 BufRest ltac:(lia))
        as [BufMid BufHi].
      clear BUF BufRest.
      call (memset_stk (DST + (fh_bsmax h + 32)) 0 litSize).
      { exact BufMid. }
      all: try lia.
      all: try assumption.
      all: try reflexivity.
      rename POST into BufMid.
      pose proof (stk_merge usegs _ _ _ _ (stk_merge usegs _ _ _ _ BufLo BufMid ltac:(lia)) BufHi ltac:(lia)) as BUF.
      clear BufLo BufMid BufHi.
      do 5 zstep.
      lazymatch goal with Cells : rw_cells _ ?mm (DCTX + 30096) ?cs |- _ =>
        let wl := cells_words cs in
        eapply (dl_ret mm (Z_to_bv 64 (DCTX + 10296)) lev wl (lhSize + 1)) end.

      all: try lia.
      all: try reflexivity.
      all: try (apply bv_eq; reflexivity).
      all: try (hnf; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ eq_refl) (conj _ (conj _ (conj _ (conj _
                  (conj (ex_intro _ _ _) (conj _ (conj _ _))))))))))))); eassumption).
      all: try (intros idx Owned; etransitivity; [|exact (Keep idx Owned)];
                do 44 (destruct idx as [|idx]; [first [discriminate Owned | reflexivity] |]); reflexivity).
      all: first [ left; reflexivity
                 | right; split; [lia|]; split;
                   [ apply (hufw_of_full _ _ _ _ dtb); [reflexivity | assumption | assumption | assumption]
                   | unfold declit_placed; do 5 eexists; do 5 (split; [reflexivity|]);
                     unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, DCTX_litExtraBuffer, ZSTD_LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH;
                     lia ] ].
    - destruct Spl as (LocIs & BigLit & BufPos & EndRel & EwsCap). destruct EndRel as [EndIs EndEws].
      rewrite LocIs in H5c.
      do 6 zstep. rewrite (sx32w_small 2) by lia. if_false.
      zstep. uck. zlb SRCB FBY lhSize. zstep. zstep. zstep.
      destruct (stk_split usegs _ B0 (DST + lp_buf Plc) B1 BUF ltac:(lia)) as [BufLo BufRest].
      destruct (stk_split usegs _ (DST + lp_buf Plc) (DST + lp_buf Plc + (litSize + -65536)) B1 BufRest ltac:(lia))
        as [BufMid BufHi].
      clear BUF BufRest.
      call (memset_stk (DST + lp_buf Plc) 0 (litSize + -65536)).
      { exact BufMid. }
      all: try lia.
      all: try assumption.
      all: try reflexivity.
      rename POST into BufMid.
      pose proof (stk_merge usegs _ _ _ _ (stk_merge usegs _ _ _ _ BufLo BufMid ltac:(lia)) BufHi ltac:(lia)) as BUF.
      clear BufLo BufMid BufHi.
      zstep. uck. zlb SRCB FBY lhSize. do 6 zstep.
      destruct (stk_split usegs _ (DCTX + 30372) (DCTX + 30372 + 65536) (DCTX + 95940) XB ltac:(lia)) as [ExtraLo ExtraHi].
      clear XB.
      call (memset_stk (DCTX + 30372) 0 65536).
      { exact ExtraLo. }
      all: try lia.
      all: try assumption.
      all: try reflexivity.
      rename POST into ExtraLo.
      pose proof (stk_merge usegs _ _ _ _ ExtraLo ExtraHi ltac:(lia)) as XB.
      clear ExtraLo ExtraHi.
      do 5 zstep.
      lazymatch goal with Cells : rw_cells _ ?mm (DCTX + 30096) ?cs |- _ =>
        let wl := cells_words cs in
        eapply (dl_ret mm (Z_to_bv 64 (DCTX + 10296)) lev wl (lhSize + 1)) end.

      all: try lia.
      all: try reflexivity.
      all: try (apply bv_eq; reflexivity).
      all: try (hnf; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ eq_refl) (conj _ (conj _ (conj _ (conj _
                  (conj (ex_intro _ _ _) (conj _ (conj _ _))))))))))))); eassumption).
      all: try (intros idx Owned; etransitivity; [|exact (Keep idx Owned)];
                do 44 (destruct idx as [|idx]; [first [discriminate Owned | reflexivity] |]); reflexivity).
      all: first [ left; reflexivity
                 | right; split; [lia|]; split;
                   [ apply (hufw_of_full _ _ _ _ dtb); [reflexivity | assumption | assumption | assumption]
                   | unfold declit_placed; do 5 eexists; do 5 (split; [reflexivity|]);
                     unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, DCTX_litExtraBuffer, ZSTD_LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH;
                     lia ] ].
    - destruct Shape as (LocIs & BufIs & EndIs & SmallLit).
      unfold DCTX_litExtraBuffer in H5c. rewrite LocIs, BufIs, EndIs, Z.add_0_r in H5c.
      do 6 zstep. rewrite (sx32w_small 0) by lia. if_true.
      zstep. zstep. uckb. zlb SRCB FBY lhSize. zstep. zstep.
      destruct (stk_split usegs _ (DCTX + 30372) (DCTX + 30372 + litSize) (DCTX + 95940) XB ltac:(lia)) as [ExtraLo ExtraHi].
      clear XB.
      call (memset_stk (DCTX + 30372) 0 litSize).
      { exact ExtraLo. }
      all: try lia.
      all: try assumption.
      all: try reflexivity.
      rename POST into ExtraLo.
      pose proof (stk_merge usegs _ _ _ _ ExtraLo ExtraHi ltac:(lia)) as XB.
      clear ExtraLo ExtraHi.
      do 5 zstep.
      lazymatch goal with Cells : rw_cells _ ?mm (DCTX + 30096) ?cs |- _ =>
        let wl := cells_words cs in
        eapply (dl_ret mm (Z_to_bv 64 (DCTX + 10296)) lev wl (lhSize + 1)) end.

      all: try lia.
      all: try reflexivity.
      all: try (apply bv_eq; reflexivity).
      all: try (hnf; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ eq_refl) (conj _ (conj _ (conj _ (conj _
                  (conj (ex_intro _ _ _) (conj _ (conj _ _))))))))))))); eassumption).
      all: try (intros idx Owned; etransitivity; [|exact (Keep idx Owned)];
                do 44 (destruct idx as [|idx]; [first [discriminate Owned | reflexivity] |]); reflexivity).
      all: first [ left; reflexivity
                 | right; split; [lia|]; split;
                   [ apply (hufw_of_full _ _ _ _ dtb); [reflexivity | assumption | assumption | assumption]
                   | unfold declit_placed; do 5 eexists; do 5 (split; [reflexivity|]);
                     unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, DCTX_litExtraBuffer, ZSTD_LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH;
                     lia ] ].
  Qed.

  (* [comment removed for export] *)
  Lemma dl_rle : forall m1 hufv lev wsv litSize lhSize dtb xra x7 xa2 xa6 xa7 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    bytes_at usegs m1 (DCTX + 10296) dtb -> huf_hdr_ok dtb -> (bv_unsigned lev mod 2^32 <> 0 -> huf_tbl_ok dtb) -> hufv = Z_to_bv 64 (DCTX + 10296) ->
    1 <= lhSize <= 3 -> lhSize + 1 <= Z.of_nat (length src) -> 0 <= litSize < 2^20 ->
    evt usegs POST (ST 0x16a40 m1 xra (Z_to_bv 64 (Z.min (fh_bsmax h) CAP)) (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 litSize) (Z_to_bv 64 lhSize)
                       (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) xa2 (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                       xa6 xa7 (Z_to_bv 64 (DCTX + 30120)) (Z_to_bv 64 (DCTX + 29944)) xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31).
  Proof using HY FBY BSM SPA.
    intros until x31. intros Bund IsFrame Keep HufB HufH HufT HufP LhR LhFit LitR.
    pose proof Bund as Whole.
    pose proof HY as Hyps. open_dlh Hyps.
    zstep. zstep. if_cases DstNZ; zify_cond DstNZ.
    - eapply (dl_rle_b m1 hufv lev wsv litSize lhSize dtb); try eassumption. intros DstZ. lia.
    - zstep. if_cases LitNZ; zify_cond LitNZ.
      + eapply (dl_ret m1 _ lev _ (2^64 - 70)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity].
      + eapply (dl_rle_b m1 hufv lev wsv litSize lhSize dtb); try eassumption. intros _. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dl_fin2 : forall m1 hufv lev wsv litSize RV ty r LB LE loc dtb xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    DLB hufv lev wsv m1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    wnth wsv H5_litBuffer = Z_to_bv 64 LB -> wnth wsv H5_litBufferEnd = Z_to_bv 64 LE -> wnth wsv H5_litBufferLocation = Z_to_bv 64 loc ->
    bytes_at usegs m1 (DCTX + 10296) dtb -> huf_hdr_ok dtb -> (zd_is_error r = false -> huf_tbl_ok dtb) -> hufv = Z_to_bv 64 (DCTX + 10296) ->
    0 <= litSize <= 131072 -> 1 <= RV <= Z.of_nat (length src) -> ty = 2 \/ ty = 3 -> 0 <= r < 2^64 ->
    ((loc = 0 /\ LE = LB + litSize /\ LB = DCTX + 30372 /\ litSize <= 65536)
     \/ (loc = 1 /\ LE = LB + litSize /\ DST <= LB /\ LE + 32 <= DST + CAP)
     \/ (loc = 2 /\ 65536 < litSize /\ DST <= LB /\ LE + 32 <= DST + CAP /\ LB <= LE)) ->
    evt usegs POST (ST 0x16da4 m1 xra x5 x6 x7 (Z_to_bv 64 litSize) (Z_to_bv 64 DCTX) (Z_to_bv 64 DCTX) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 r) (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 ty) (Z_to_bv 64 RV) xs6 xs7 xs8 xs9 x28 x29 x30 x31).
  Proof using HY SPA.
    intros until x31. intros Bund Keep LBw LEw LOCw HufB HufH HufT HufP LitR RVR TyC RR Place.
    pose proof Bund as Whole.
    open_dlb Bund. open_dlh HY.
    destruct H5 as [H5c H5n]. revert Keep. h5_open wsv H5n. intros Keep.
    subst.
    pose proof (proj1 HufH) as TblLen. unfold HUF_DTABLE_BYTES in TblLen.
    zstep. zstep. zstep. if_cases Big; zify_cond Big.
    - eapply (dl_ret m1 _ lev _ (2^64 - 20)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity].
    - assert (NoErr : zd_is_error r = false) by (unfold zd_is_error, ZE_maxCode; apply Z.ltb_ge; lia).
      specialize (HufT NoErr).
      assert (TyR : 2 <= ty <= 3) by (unfold hidden in TyC; lia).
      do 7 zstep.
      if_cases NotTwo; zify_cond NotTwo; [do 2 zstep | do 6 zstep].
      all: lazymatch goal with Cells : rw_cells _ ?mm (DCTX + 30096) ?cs |- _ =>
             let wl := cells_words cs in
             eapply (dl_ret mm (Z_to_bv 64 (DCTX + 10296)) (Z_to_bv 64 1) wl RV) end.
      all: try lia; try reflexivity.
      all: try (hnf; refine (conj PTRS (conj EHUF (conj EWK (conj FP (conj H3 (conj (conj H5c eq_refl)
                  (conj XB (conj SRCB (conj BUF (conj STK (conj (ex_intro _ j FR) (conj MI (conj MU WM)))))))))))))).
      all: try (intros idx Owned; etransitivity; [|exact (Keep idx Owned)];
                do 44 (destruct idx as [|idx]; [first [discriminate Owned | reflexivity] |]); reflexivity).
      all: right; split; [lia|].
      all: split; [apply (hufw_of_full _ _ _ _ dtb); [reflexivity | exact HufB | exact HufH | intros _; exact HufT] |].
      all: unfold declit_placed; exists LB, litSize, LB, LE, loc.
      all: do 5 (split; [reflexivity|]).
      all: unfold hidden in Place; unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, DCTX_litExtraBuffer, ZSTD_LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH.
      all: lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dl_fin : forall m1 hufv lev wsv litSize RV ty r LB LE loc E dtb xra x5 x6 x7 xs2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    DLB hufv lev wsv m1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    wnth wsv H5_litBuffer = Z_to_bv 64 LB -> wnth wsv H5_litBufferEnd = Z_to_bv 64 LE -> wnth wsv H5_litBufferLocation = Z_to_bv 64 loc ->
    bytes_at usegs m1 (DCTX + 10296) dtb -> huf_hdr_ok dtb -> (zd_is_error r = false -> huf_tbl_ok dtb) -> hufv = Z_to_bv 64 (DCTX + 10296) ->
    0 <= litSize <= 131072 -> 1 <= RV <= Z.of_nat (length src) -> ty = 2 \/ ty = 3 -> 0 <= r < 2^64 ->
    ((loc = 0 /\ LE = LB + litSize /\ LB = DCTX + 30372 /\ litSize <= 65536)
     \/ (loc = 1 /\ LE = LB + litSize /\ DST <= LB /\ LE + 32 <= DST + CAP)
     \/ (loc = 2 /\ 65536 < litSize /\ LB = DST + (E - litSize) /\ LE = DST + E /\ litSize <= E <= CAP)) ->
    evt usegs POST (ST 0x16ce8 m1 xra x5 x6 x7 (Z_to_bv 64 litSize) (Z_to_bv 64 DCTX) (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       xs2 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 ty) (Z_to_bv 64 RV) xs6 xs7 xs8 xs9 x28 x29 x30 x31).
  Proof using HY BSM SPA.
    intros until x31. intros Bund Keep LBw LEw LOCw HufB HufH HufT HufP LitR RVR TyC RR Place.
    pose proof Bund as Whole.
    open_dlb Bund. open_dlh HY.
    destruct H5 as [H5c H5n]. revert Keep. h5_open wsv H5n. intros Keep.
    subst.
    pose proof (proj1 HufH) as TblLen. unfold HUF_DTABLE_BYTES in TblLen.
    assert (LocR : 0 <= loc <= 2) by (unfold hidden in Place; lia).
    do 5 zstep. rewrite (sx32w_small loc) by lia.
    if_cases NotSplit; zify_cond NotSplit.
    - eapply (dl_fin2 m1 _ lev _ litSize RV ty r LB LE loc dtb); try exact Whole; try exact Keep; try reflexivity; try assumption.
      unfold hidden in Place. lia.
    - assert (Split : 65536 < litSize /\ LB = DST + (E - litSize) /\ LE = DST + E /\ litSize <= E <= CAP) by (unfold hidden in Place; lia).
      destruct Split as (BigLit & LBis & LEis & ERange). subst LB LE.
      assert (DstFar : 4096 <= DST).
      { destruct (Z.eq_dec DST 0) as [Zero|NonZero]; [specialize (DNULL Zero); lia | specialize (DNN NonZero); lia]. }
      destruct (stk_split usegs m1 (DCTX + 30372) (DCTX + 95908) (DCTX + 95940) XB ltac:(lia)) as [ExtraLo ExtraHi]. clear XB.
      zstep. zstep. zstep. uckb. zstep. zstep. uck.
      do 7 zstep.
      call (memcpy_stk (DCTX + 30372) (DST + E + -65536) 65536).
      { replace (DCTX + 30372 + 65536) with (DCTX + 95908) by lia. exact ExtraLo. }
      { eapply rdbl_sub; [apply rdbl_of_stk; exact BUF | lia | lia]. }
      all: try lia.
      all: try (unfold hidden in DSTD; lia).
      all: try exact MI.
      all: try reflexivity.
      rename POST into ExtraNew.
      zstep. zstep. uck. zstep. zstep. uck. do 4 zstep. uck. zstep. uck.
      do 6 zstep.
      destruct (stk_split usegs _ B0 (DST + (E - litSize) + 65504) B1 BUF ltac:(lia)) as [BufLo BufRest].
      destruct (stk_split usegs _ (DST + (E - litSize) + 65504) (DST + (E - litSize) + 65504 + (litSize + -65536)) B1 BufRest ltac:(lia))
        as [BufMid BufHi].
      pose proof (rdbl_sub usegs _ B0 B1 (DST + (E - litSize)) (DST + (E - litSize) + (litSize + -65536))
                    (rdbl_of_stk usegs _ B0 B1 BUF) ltac:(lia) ltac:(lia)) as SrcRd.
      clear BUF BufRest.
      call (memmove_stk (DST + (E - litSize) + 65504) (DST + (E - litSize)) (litSize + -65536)).
      { exact BufMid. }
      { exact SrcRd. }
      all: try lia.
      all: try assumption.
      all: try reflexivity.
      rename POST into MovedNew.
      do 2 zstep. uck. do 2 zstep. uck.
      do 7 zstep. uck. zstep. uck. do 3 zstep.
      replace (DCTX + 30372 + 65536) with (DCTX + 95908) in ExtraNew by lia.
      pose proof (stk_merge usegs _ _ _ _ ExtraNew ExtraHi ltac:(lia)) as XB.
      pose proof (stk_merge usegs _ _ _ _ (stk_merge usegs _ _ _ _ BufLo MovedNew ltac:(lia)) BufHi ltac:(lia)) as BUF.
      clear ExtraNew ExtraHi BufLo MovedNew BufHi.
      lazymatch goal with Cells : rw_cells _ ?mm (DCTX + 30096) ?cs |- _ =>
        let wl := cells_words cs in
        eapply (dl_fin2 mm _ lev wl litSize RV ty r _ _ 2 dtb) end.
      all: try reflexivity.
      + hnf. refine (conj PTRS (conj EHUF (conj EWK (conj FP (conj H3 (conj (conj H5c eq_refl)
                (conj XB (conj SRCB (conj BUF (conj STK (conj (ex_intro _ j FR) (conj MI (conj MU WM))))))))))))).
      + intros idx Owned. etransitivity; [|exact (Keep idx Owned)].
        do 44 (destruct idx as [|idx]; [first [discriminate Owned | reflexivity] |]). reflexivity.
      + rewrite NotSplit. reflexivity.
      + exact HufB.
      + exact HufH.
      + exact HufT.
      + exact LitR.
      + exact RVR.
      + unfold hidden in TyC. exact TyC.
      + exact RR.
      + lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dl_pf : forall (n : nat) k m1 xra x5 x6 x7 xs0 xs1 xa3 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    Z.of_nat n = 256 - k -> 0 <= k ->
    (forall xa4 xa6', evt usegs POST (ST 0x16b9c m1 xra x5 x6 x7 xs0 xs1 (Z_to_bv 64 (DCTX + 10296)) (Z_to_bv 64 1) (Z_to_bv 64 16324) xa3 xa4 xa5 xa6' xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31)) ->
    evt usegs POST (ST 0x16b7c m1 xra x5 x6 x7 xs0 xs1 (Z_to_bv 64 (DCTX + 10296)) (Z_to_bv 64 1) (Z_to_bv 64 16324) xa3 (Z_to_bv 64 (64 * k)) xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31).
  Proof using HY.
    intros n. open_dlh HY.
    induction n as [|n More]; intros k m1 xra x5 x6 x7 xs0 xs1 xa3 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31 Count Kpos Exit;
      assert (Kmax : k <= 256) by lia;
      zstep; zstep; zstep; uck; zstep; zstep; zstep; uckb; zstep; zstep; if_cases Again; zify_cond Again.
    all: try (exfalso; lia).
    - apply Exit.
    - replace (64 * k + 64) with (64 * (k + 1)) by lia.
      apply More; [lia | lia | exact Exit].
  Qed.

  Hypothesis H1X : huf_1x_stmt.
  Hypothesis H4X : huf_4x_stmt.
  Hypothesis H1W : huf_1x1_wksp_stmt.
  Hypothesis H4W : huf_4x_wksp_stmt.

  (* [comment removed for export] *)
  Ltac huf_call_using ENTRY FRS HX LBv RLOv RHIv :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let HU := fresh "HU" in
      pose proof (huf_using_reg ENTRY FRS ltac:(lia) HX) as HU;
      eapply evt_cut; [ eapply evt_mono; [ eapply HU with (SPV := SPV + -96) (DST := LBv) (RLO := RLOv) (RHI := RHIv) (DT := DCTX + 10296) (lo := lo);
          first [ eassumption | reflexivity | lia | sep_solve
                | (unfold huf_reg_pre; repeat (split; [first [eassumption | lia | sep_solve]|]); first [eassumption | lia | sep_solve]) ]
          | intros ms' P; unfold huf_reg_post in P; cbn [app] in P; exact P ]
        | clear HU; post_call usegs mx ]
    end.
  Ltac huf_call_wksp ENTRY FRS HX LBv RLOv RHIv :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let HU := fresh "HU" in
      pose proof (huf_wksp_reg ENTRY FRS ltac:(lia) HX) as HU;
      eapply evt_cut; [ eapply evt_mono; [ eapply HU with (SPV := SPV + -96) (DST := LBv) (RLO := RLOv) (RHI := RHIv) (DT := DCTX + 10296) (WK := DCTX + 27324)
                                             (wksz := 2560) (lo := lo);
          first [ eassumption | reflexivity | lia | sep_solve
                | (unfold huf_reg_pre; repeat (split; [first [eassumption | lia | sep_solve]|]); first [eassumption | lia | sep_solve]) ]
          | intros ms' P; unfold huf_reg_post in P; cbn [app] in P; exact P ]
        | clear HU; post_call usegs mx ]
    end.
  Ltac close_dlb_tac :=
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
    split; [split; [eassumption | reflexivity]|];
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eexists; eassumption|];
    split; [assumption|]; split; eassumption.
  Ltac close_keep_tac K := let i := fresh "i" in let Hi := fresh "Hi" in
    intros i Hi; specialize (K i Hi); do 44 (destruct i as [|i]; [first [discriminate Hi | exact K]|]); exact K.
  Ltac keep_by_hyp := lazymatch goal with K : forall i, h5_block_owned i = false -> _ |- _ => close_keep_tac K end.
  Ltac huf_after_using LBv LEv locv Ev :=
    lazymatch goal with RESq : ?r = _ \/ zd_is_error ?r = true |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let RR := fresh "RR" in
      assert (RR : 0 <= r < 2^64) by assumption;
      lazymatch goal with H5q : rw_cells _ mx (DCTX + 30096) ?cs |- _ => let wl := cells_words cs in
        eapply (dl_fin mx _ _ wl _ _ 3 r LBv LEv locv Ev _);
          [ close_dlb_tac | keep_by_hyp | reflexivity | reflexivity | reflexivity | eassumption | eassumption
          | intros _; eassumption | reflexivity | lia | lia | right; reflexivity | exact RR | unfold hidden in *; lia ] end
    end.
  Ltac huf_after_wksp LBv LEv locv Ev :=
    lazymatch goal with RESq : ?r = _ \/ zd_is_error ?r = true, HB : huf_built _ ?mx ?r, WKq : stk _ ?mx (DCTX + 27324) (DCTX + 27324 + 2560) |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let RR := fresh "RR" in let dtb' := fresh "dtb'" in let DTU' := fresh "DTU'" in let HOK' := fresh "HOK'" in let VAL' := fresh "VAL'" in
      let EHUF' := fresh "EHUF'" in let LD' := fresh "LD'" in
      assert (RR : 0 <= r < 2^64) by assumption;
      destruct HB as (dtb' & DTU' & HOK' & VAL');
      assert (LD' : Z.of_nat (length dtb') = 16388) by (destruct HOK' as [L _]; exact L);
      pose proof (u8arr_stk _ _ _ DTU') as EHUF'; rewrite LD' in EHUF'; replace (DCTX + 10296 + 16388) with (DCTX + 26684) in EHUF' by lia;
      replace (DCTX + 27324 + 2560) with (DCTX + 29884) in WKq by lia;
      destruct DTU' as [DTU' _];
      lazymatch goal with H5q : rw_cells _ mx (DCTX + 30096) ?cs |- _ => let wl := cells_words cs in
        eapply (dl_fin mx _ _ wl _ _ 2 r LBv LEv locv Ev dtb');
          [ close_dlb_tac | keep_by_hyp | reflexivity | reflexivity | reflexivity | exact DTU' | exact HOK'
          | exact VAL' | reflexivity | lia | lia | left; reflexivity | exact RR | unfold hidden in *; lia ] end
    end.

  (* [comment removed for export] *)
  Lemma dl_huf : forall m1 hufv lev wsv0 litSize litCSize lhSize ty four dtb xra x5 x6 x7 xa0 xa1 xa2 xa4 xa6 xa7 xs9v x28 x29 x30 x31,
    DLB hufv lev (h5_placed wsv0 DCTX DST (alloc_lit_buffer (fh_bsmax h) CAP litSize (Z.min (fh_bsmax h) CAP) false)) m1 ->
    length wsv0 = 44%nat -> (forall i, h5_block_owned i = false -> wnth wsv0 i = wnth ws i) ->
    bytes_at usegs m1 (DCTX + 10296) dtb -> huf_hdr_ok dtb -> (ty = 3 -> huf_tbl_ok dtb) -> hufv = Z_to_bv 64 (DCTX + 10296) ->
    3 <= lhSize <= 5 -> 0 <= litSize <= Z.min (fh_bsmax h) CAP -> 0 <= litCSize -> lhSize + litCSize <= Z.of_nat (length src) ->
    four = 0 \/ four = 1 -> ty = 2 \/ ty = 3 -> (DST = 0 -> litSize = 0) ->
    evt usegs POST (ST 0x16b9c m1 xra x5 x6 x7 (Z_to_bv 64 litSize) (Z_to_bv 64 DCTX) xa0 xa1 xa2 (Z_to_bv 64 LSRC) xa4 (Z_to_bv 64 DCTX) xa6 xa7
                       (Z_to_bv 64 litCSize) (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 ty) (Z_to_bv 64 (lhSize + litCSize)) (Z_to_bv 64 lhSize) xs9v
                       (Z_to_bv 64 four) (Z_to_bv 64 LSRC) x28 x29 x30 x31).
  Proof using HY BSM SPA H1X H4X H1W H4W.
    intros until x31. intros Bund Wlen Keep HufB HufH HufT HufP LhR LitR CszPos CszFit FourC TyC NullLit.
    open_dlb Bund. open_dlh HY.
    destruct H5 as [H5c _]. revert Keep. h5_open wsv0 Wlen. intros Keep.
    subst hufv.
    remember (alloc_lit_buffer (fh_bsmax h) CAP litSize (Z.min (fh_bsmax h) CAP) false) as Plc eqn:PlcDef.
    cbv beta iota delta [h5_placed wupd h5_cells mk_wcells h5_sizes H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in H5c.
    pose proof (alloc_lit_buffer_regions (fh_bsmax h) CAP litSize (Z.min (fh_bsmax h) CAP) false ltac:(lia) eq_refl
                  ltac:(unfold ZSTD_BLOCKSIZE_MAX; lia)) as Shape.
    cbv zeta iota in Shape. rewrite <- PlcDef in Shape.
    unfold ZSTD_in_dst, ZSTD_split, ZSTD_not_in_dst, WILDCOPY_OVERLENGTH, ZSTD_LITBUFFEREXTRASIZE in Shape.
    pose proof (proj1 HufH) as TblLen. unfold HUF_DTABLE_BYTES in TblLen.
    assert (DtBytes : HUF_DTABLE_BYTES = 16388) by reflexivity.
    destruct (bytes_at_mid _ _ _ lhSize litCSize SRCB ltac:(lia) ltac:(lia) ltac:(rewrite length_map; lia)) as [Piece PieceLen].
    unfold hidden in TyC, FourC.
    destruct (lp_base Plc) eqn:BaseK; cbv iota in Shape; [ | | contradiction]; cbn [lit_base_addr] in H5c.
    - assert (BufPos : 0 <= lp_buf Plc) by lia.
      assert (EndIs : lp_end Plc = lp_buf Plc + litSize) by lia.
      assert (EndFit : lp_end Plc <= CAP) by lia.
      assert (DstBig : 4096 <= DST).
      { destruct (Z.eq_dec DST 0) as [Zero|NonZero]; [specialize (DNULL Zero); lia | specialize (DNN NonZero); lia]. }
      destruct TyC as [Two | Three]; subst ty; destruct FourC as [One | Four]; subst four.
      + (* wksp, single stream, literals in dst *)
        pose proof (stk_bytes_u8arr _ _ dtb ltac:(rewrite TblLen; replace (DCTX + 10296 + 16388) with (DCTX + 26684) by lia; exact EHUF) HufB) as HufU.
        assert (WkRoom : stk usegs _ (DCTX + 27324) (DCTX + 27324 + 2560)) by (replace (DCTX + 27324 + 2560) with (DCTX + 29884) by lia; exact EWK).
        zstep. zstep. zstep. zstep. if_true.
        do 5 zstep.
        if_true. zstep. uckb. do 10 zstep.
        huf_call_wksp 0x20734 1072 H1W (DST + lp_buf Plc) B0 B1.
        clear OFFD OFFB OFFSRC BD BSRC SRCD OFFDST DSTD DSTSRC.
        huf_after_wksp (DST + lp_buf Plc) (DST + lp_end Plc) (lp_loc Plc) (Z.min (fh_bsmax h) CAP).
      + (* wksp, four streams, literals in dst *)
        pose proof (stk_bytes_u8arr _ _ dtb ltac:(rewrite TblLen; replace (DCTX + 10296 + 16388) with (DCTX + 26684) by lia; exact EHUF) HufB) as HufU.
        assert (WkRoom : stk usegs _ (DCTX + 27324) (DCTX + 27324 + 2560)) by (replace (DCTX + 27324 + 2560) with (DCTX + 29884) by lia; exact EWK).
        zstep. zstep. zstep. zstep. if_true.
        do 5 zstep.
        if_false. zstep. uckb. do 10 zstep.
        huf_call_wksp 0x25418 1088 H4W (DST + lp_buf Plc) B0 B1.
        zstep. clear OFFD OFFB OFFSRC BD BSRC SRCD OFFDST DSTD DSTSRC.
        huf_after_wksp (DST + lp_buf Plc) (DST + lp_end Plc) (lp_loc Plc) (Z.min (fh_bsmax h) CAP).
      + (* table reuse, single stream, literals in dst *)
        specialize (HufT eq_refl).
        zstep. zstep. zstep. zstep. if_false.
        zstep. zstep. zstep.
        zstep. if_true. zstep. uckb. do 5 zstep.
        huf_call_using 0x207f8 144 H1X (DST + lp_buf Plc) B0 B1.
        zstep. clear OFFD OFFB OFFSRC BD BSRC SRCD OFFDST DSTD DSTSRC.
        huf_after_using (DST + lp_buf Plc) (DST + lp_end Plc) (lp_loc Plc) (Z.min (fh_bsmax h) CAP).
      + (* table reuse, four streams, literals in dst *)
        specialize (HufT eq_refl).
        zstep. zstep. zstep. zstep. if_false.
        zstep. zstep. zstep.
        zstep. if_false. zstep. uckb. do 5 zstep.
        huf_call_using 0x20d78 912 H4X (DST + lp_buf Plc) B0 B1.
        zstep. clear OFFD OFFB OFFSRC BD BSRC SRCD OFFDST DSTD DSTSRC.
        huf_after_using (DST + lp_buf Plc) (DST + lp_end Plc) (lp_loc Plc) (Z.min (fh_bsmax h) CAP).
    - destruct Shape as (LocIs & BufIs & EndIs & SmallLit).
      unfold DCTX_litExtraBuffer in H5c. rewrite LocIs, BufIs, EndIs, Z.add_0_r in H5c.
      destruct TyC as [Two | Three]; subst ty; destruct FourC as [One | Four]; subst four.
      + pose proof (stk_bytes_u8arr _ _ dtb ltac:(rewrite TblLen; replace (DCTX + 10296 + 16388) with (DCTX + 26684) by lia; exact EHUF) HufB) as HufU.
        assert (WkRoom : stk usegs _ (DCTX + 27324) (DCTX + 27324 + 2560)) by (replace (DCTX + 27324 + 2560) with (DCTX + 29884) by lia; exact EWK).
        zstep. zstep. zstep. zstep. if_true.
        do 5 zstep.
        if_true. zstep. uckb. do 10 zstep.
        huf_call_wksp 0x20734 1072 H1W (DCTX + 30372) (DCTX + 30372) (DCTX + 95940).
        clear OFFD OFFB OFFSRC BD BSRC SRCD OFFDST DSTD DSTSRC.
        huf_after_wksp (DCTX + 30372) (DCTX + 30372 + litSize) 0 0.
      + pose proof (stk_bytes_u8arr _ _ dtb ltac:(rewrite TblLen; replace (DCTX + 10296 + 16388) with (DCTX + 26684) by lia; exact EHUF) HufB) as HufU.
        assert (WkRoom : stk usegs _ (DCTX + 27324) (DCTX + 27324 + 2560)) by (replace (DCTX + 27324 + 2560) with (DCTX + 29884) by lia; exact EWK).
        zstep. zstep. zstep. zstep. if_true.
        do 5 zstep.
        if_false. zstep. uckb. do 10 zstep.
        huf_call_wksp 0x25418 1088 H4W (DCTX + 30372) (DCTX + 30372) (DCTX + 95940).
        zstep. clear OFFD OFFB OFFSRC BD BSRC SRCD OFFDST DSTD DSTSRC.
        huf_after_wksp (DCTX + 30372) (DCTX + 30372 + litSize) 0 0.
      + specialize (HufT eq_refl).
        zstep. zstep. zstep. zstep. if_false.
        zstep. zstep. zstep.
        zstep. if_true. zstep. uckb. do 5 zstep.
        huf_call_using 0x207f8 144 H1X (DCTX + 30372) (DCTX + 30372) (DCTX + 95940).
        zstep. clear OFFD OFFB OFFSRC BD BSRC SRCD OFFDST DSTD DSTSRC.
        huf_after_using (DCTX + 30372) (DCTX + 30372 + litSize) 0 0.
      + specialize (HufT eq_refl).
        zstep. zstep. zstep. zstep. if_false.
        zstep. zstep. zstep.
        zstep. if_false. zstep. uckb. do 5 zstep.
        huf_call_using 0x20d78 912 H4X (DCTX + 30372) (DCTX + 30372) (DCTX + 95940).
        zstep. clear OFFD OFFB OFFSRC BD BSRC SRCD OFFDST DSTD DSTSRC.
        huf_after_using (DCTX + 30372) (DCTX + 30372 + litSize) 0 0.
  Qed.

  (* [comment removed for export] *)
  Lemma dl_comp : forall m1 hufv lev wsv litSize litCSize lhSize ty four dtb (dha : word) xra x5 x7 xs1 xs5 xs9 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    bytes_at usegs m1 (DCTX + 10296) dtb -> huf_hdr_ok dtb -> (ty = 3 -> huf_tbl_ok dtb) -> hufv = Z_to_bv 64 (DCTX + 10296) ->
    3 <= lhSize <= 5 -> 0 <= litSize < 2^18 -> 0 <= litCSize < 2^18 ->
    four = 0 \/ four = 1 -> ty = 2 \/ ty = 3 -> (DST = 0 -> litSize = 0) ->
    evt usegs POST (ST 0x16b08 m1 xra x5 (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 litSize) xs1
                       (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (Z.of_nat (length src))) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                       (Z_to_bv 64 (Z.min (fh_bsmax h) CAP)) (Z_to_bv 64 (-70)) (Z_to_bv 64 litCSize) (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 ty) xs5
                       (Z_to_bv 64 lhSize) dha (Z_to_bv 64 four) xs9 x28 x29 x30 x31).
  Proof using HY BSM SPA H1X H4X H1W H4W.
    intros until x31. intros Bund IsFrame Keep HufB HufH HufT HufP LhR LitR CszR FourC TyC NullLit.
    pose proof Bund as Whole.
    open_dlb Bund. open_dlh HY.
    destruct H5 as [H5c H5n]. revert Keep IsFrame. h5_open wsv H5n. intros Keep IsFrame.
    subst hufv.
    pose proof (proj1 HufH) as TblLen. unfold HUF_DTABLE_BYTES in TblLen.
    assert (FourR : 0 <= four <= 1) by (unfold hidden in FourC; lia).
    assert (TyR : 2 <= ty <= 3) by (unfold hidden in TyC; lia).
    zstep. if_cases TooBig; zify_cond TooBig.
    { zstep. eapply (dl_ret m1 _ lev _ (2^64 - 20)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity]. }
    zstep. zstep. zstep. if_cases Gate; zify_cond Gate.
    2: { zstep. zstep. eapply (dl_ret m1 _ lev _ (2^64 - 24)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity]. }
    zstep. zstep. if_cases Short; zify_cond Short.
    { zstep. eapply (dl_ret m1 _ lev _ (2^64 - 20)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity]. }
    zstep. if_cases NoRoom; zify_cond NoRoom.
    { eapply (dl_ret m1 _ lev _ (2^64 - 70)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity]. }
    do 9 zstep.
    pose proof zd_alloclit_proof as Alloc. unfold zd_alloclit_stmt in Alloc.
    lazymatch goal with Cells : rw_cells _ ?mm (DCTX + 30096) ?cs |- _ =>
      let wl := cells_words cs in
      eapply evt_cut;
      [ eapply Alloc with (SPV := SPV + -96) (DCTX := DCTX) (DST := DST) (CAP := CAP) (litSize := litSize)
                          (ews := Z.min (fh_bsmax h) CAP) (imm := false) (h := h) (ws := wl)
      | unfold zd_alloclit_post, DCTX_litBuffer; post_call usegs mm ] end.
    all: first [ exact FP | exact BSM | exact MI | (split; [exact H5c | reflexivity]) | reflexivity | assumption | lia | idtac ].
    rename POST into Placed.
    pose proof (proj1 Placed) as View.
    cbv beta iota delta [h5_placed wupd h5_cells mk_wcells h5_sizes H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in View.
    do 4 zstep. if_cases Warm.
    { eapply (dl_huf _ (Z_to_bv 64 (DCTX + 10296)) lev _ litSize litCSize lhSize ty four dtb);
        [ hnf; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj Placed (conj _ (conj _ (conj _ (conj _
                (conj (ex_intro _ _ _) (conj _ (conj _ _))))))))))))); eassumption
        | reflexivity | exact Keep | .. ].
      all: try eassumption.
      all: try reflexivity.
      all: try lia.
      all: unfold hidden in *; assumption.
 }
    zstep. zstep. if_cases Small; zify_cond Small.
    { eapply (dl_huf _ (Z_to_bv 64 (DCTX + 10296)) lev _ litSize litCSize lhSize ty four dtb);
        [ hnf; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj Placed (conj _ (conj _ (conj _ (conj _
                (conj (ex_intro _ _ _) (conj _ (conj _ _))))))))))))); eassumption
        | reflexivity | exact Keep | .. ].
      all: try eassumption.
      all: try reflexivity.
      all: try lia.
      all: unfold hidden in *; assumption.
 }
    do 5 zstep. zb_fix.
    eapply (dl_pf 256 0); [reflexivity | lia | intros xa4 xa6'].
    eapply (dl_huf _ (Z_to_bv 64 (DCTX + 10296)) lev _ litSize litCSize lhSize ty four dtb);
      [ hnf; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj Placed (conj _ (conj _ (conj _ (conj _
              (conj (ex_intro _ _ _) (conj _ (conj _ _))))))))))))); eassumption
      | reflexivity | exact Keep | .. ].
    all: try eassumption.
    all: try reflexivity.
    all: try lia.
    all: unfold hidden in *; assumption.
  Qed.

  Ltac ldsrc Bytes k :=
    let Rng := fresh "SrcByte" in
    pose proof (Forall_Znth (fun c => 0 <= c < 256) src k FBY ltac:(lia)) as Rng; cbv beta in Rng;
    zlb Bytes FBY k.


  (* [comment removed for export] *)
  Lemma dl_hdr_raw2 : forall m1 hufv lev wsv dtb lhlv xra x7 xa7 xs1 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    bytes_at usegs m1 (DCTX + 10296) dtb -> huf_hdr_ok dtb -> (bv_unsigned lev mod 2^32 <> 0 -> huf_tbl_ok dtb) -> hufv = Z_to_bv 64 (DCTX + 10296) ->
    2 <= Z.of_nat (length src) ->
    evt usegs POST (ST 0x167e0 m1 xra (Z_to_bv 64 (Z.min (fh_bsmax h) CAP)) (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 (Znth 0 src)) xs1
                       (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (Z.of_nat (length src))) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                       (Z_to_bv 64 lhlv) xa7 (Z_to_bv 64 (DCTX + 30120)) (Z_to_bv 64 (DCTX + 29944)) xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31).
  Proof using HY FBY BSM SPA.
    intros until x31. intros Bund IsFrame Keep HufB HufH HufT HufP TwoMin.
    pose proof Bund as Whole.
    open_dlb Bund. open_dlh HY.
    assert (DstR : 0 <= DST) by (pose proof (proj1 BUF); lia).
    zstep. zstep. if_cases One; zify_cond One.
    { ldsrc SRCB 1. ldsrc SRCB 0. zs. zs. zstep. shr2div. zstep. zstep.
      zstep. if_cases DstNull; zify_cond DstNull.
      + zstep. if_cases LitNZ; zify_cond LitNZ.
        * eapply (dl_ret m1 _ lev _ (2^64 - 70)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity].
        * eapply (dl_raw m1 _ lev wsv _ 2 dtb); try eassumption; try reflexivity; try lia.
      + zstep. eapply (dl_raw m1 _ lev wsv _ 2 dtb); try eassumption; try reflexivity; try lia. }
    zstep. zstep. if_cases NotThree; zify_cond NotThree.
    { pose proof (Forall_Znth (fun c => 0 <= c < 256) src 0 FBY ltac:(lia)) as Byte0. cbv beta in Byte0.
      zstep. shr2div. zstep. zstep. zstep. if_cases DstNZ; zify_cond DstNZ.
      - eapply (dl_raw m1 _ lev wsv _ 1 dtb); try eassumption; try reflexivity; try lia.
      - zstep. if_cases LitNZ; zify_cond LitNZ.
        + eapply (dl_ret m1 _ lev _ (2^64 - 70)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity].
        + eapply (dl_raw m1 _ lev wsv _ 1 dtb); try eassumption; try reflexivity; try lia. }
    zstep. zstep. if_cases TwoOnly; zify_cond TwoOnly.
    { zstep. eapply (dl_ret m1 _ lev _ (2^64 - 20)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity]. }
    zstep. zstep. uck.
    ldsrc SRCB 1. ldsrc SRCB 0. ldsrc SRCB 2. zs. zs. zs. zs. zstep. shr2div. zstep. zstep.
    zstep. if_cases DstNull; zify_cond DstNull.
    + zstep. if_cases LitNZ; zify_cond LitNZ.
      * eapply (dl_ret m1 _ lev _ (2^64 - 70)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity].
      * eapply (dl_raw m1 _ lev wsv _ 3 dtb); try eassumption; try reflexivity; try lia.
    + zstep. eapply (dl_raw m1 _ lev wsv _ 3 dtb); try eassumption; try reflexivity; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dl_hdr_rle2 : forall m1 hufv lev wsv dtb lhlv xra x7 xa7 xs1 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    bytes_at usegs m1 (DCTX + 10296) dtb -> huf_hdr_ok dtb -> (bv_unsigned lev mod 2^32 <> 0 -> huf_tbl_ok dtb) -> hufv = Z_to_bv 64 (DCTX + 10296) ->
    2 <= Z.of_nat (length src) ->
    evt usegs POST (ST 0x168e0 m1 xra (Z_to_bv 64 (Z.min (fh_bsmax h) CAP)) (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 (Znth 0 src)) xs1
                       (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (Z.of_nat (length src))) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                       (Z_to_bv 64 lhlv) xa7 (Z_to_bv 64 (DCTX + 30120)) (Z_to_bv 64 (DCTX + 29944)) xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31).
  Proof using HY FBY BSM SPA.
    intros until x31. intros Bund IsFrame Keep HufB HufH HufT HufP TwoMin.
    pose proof Bund as Whole.
    open_dlb Bund. open_dlh HY.
    zstep. zstep. if_cases One; zify_cond One.
    { zstep. zstep. if_cases TwoOnly; zify_cond TwoOnly.
      { zstep. eapply (dl_ret m1 _ lev _ (2^64 - 20)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity]. }
      ldsrc SRCB 1. ldsrc SRCB 0. zs. zs. zstep. shr2div. zstep.
      eapply (dl_rle m1 _ lev wsv _ 2 dtb); try eassumption; try reflexivity; lia. }
    zstep. zstep. if_cases NotThree; zify_cond NotThree.
    { pose proof (Forall_Znth (fun c => 0 <= c < 256) src 0 FBY ltac:(lia)) as Byte0. cbv beta in Byte0.
      zstep. shr2div. zstep.
      eapply (dl_rle m1 _ lev wsv _ 1 dtb); try eassumption; try reflexivity; lia. }
    zstep. zstep. if_cases UnderFour; zify_cond UnderFour.
    { zstep. eapply (dl_ret m1 _ lev _ (2^64 - 20)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity]. }
    zstep. zstep. zstep. uck.
    ldsrc SRCB 1. ldsrc SRCB 0. ldsrc SRCB 2. zs. zs. zs. zs. zstep. shr2div. zstep. zstep.
    eapply (dl_rle m1 _ lev wsv _ 3 dtb); try eassumption; try reflexivity; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dl_hdr_comp2 : forall m1 hufv lev wsv dtb ty T0 T2 lhlv xra xs0 xs1 xa7' xs2 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    bytes_at usegs m1 (DCTX + 10296) dtb -> huf_hdr_ok dtb -> (ty = 3 -> huf_tbl_ok dtb) -> hufv = Z_to_bv 64 (DCTX + 10296) ->
    5 <= Z.of_nat (length src) -> ty = 2 \/ ty = 3 -> 0 <= T0 < 2^16 -> 0 <= T2 < 2^32 -> T2 mod 2^16 = 0 -> 0 <= lhlv < 2^64 -> xa7' = Z_to_bv 64 lhlv ->
    evt usegs POST (ST 0x1688c m1 xra xa7' (Z_to_bv 64 (fh_bsmax h)) (Z_to_bv 64 T2) xs0 xs1
                       (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (Z.of_nat (length src))) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                       (Z_to_bv 64 (Z.min (fh_bsmax h) CAP)) (Z_to_bv 64 T0) xs2 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 ty) xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31).
  Proof using HY FBY BSM SPA H1X H4X H1W H4W.
    intros until x31. intros Bund IsFrame Keep HufB HufH HufT HufP FiveMin TyC T0R T2R T2Low LhlR LhlW.
    pose proof Bund as Whole.
    open_dlb Bund. open_dlh HY.
    destruct H5 as [H5c H5n]. revert Keep IsFrame Whole. h5_open wsv H5n. intros Keep IsFrame Whole.
    subst xa7'.
    zstep. zstep. zs. zstep. if_cases LhlTwo; zify_cond LhlTwo.
    { zs. zstep. shr2div. zstep. zstep. shr2div. zstep. zstep.
      zstep. if_cases DstNull; zify_cond DstNull.
      + zstep. if_cases LitNZ; zify_cond LitNZ.
        * eapply (dl_ret m1 _ lev _ (2^64 - 70)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity].
        * eapply (dl_comp m1 hufv lev _ _ _ 4 ty 1 dtb); try eassumption; try reflexivity; try lia.
      + zstep. eapply (dl_comp m1 hufv lev _ _ _ 4 ty 1 dtb); try eassumption; try reflexivity; try lia. }
    zstep. zstep. if_cases LhlLow; zify_cond LhlLow.
    { zstep. zs. zs. zstep. shr2div. zstep. shr2div. zstep.
      zstep. if_cases DstNZ; zify_cond DstNZ.
      + eapply (dl_comp m1 hufv lev _ _ _ 3 ty _ dtb); try eassumption; try reflexivity; try lia;
          destruct (0 <? lhlv); [right | left]; reflexivity.
      + zstep. if_cases LitNZ; zify_cond LitNZ.
        * eapply (dl_ret m1 _ lev _ (2^64 - 70)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity].
        * eapply (dl_comp m1 hufv lev _ _ _ 3 ty _ dtb); try eassumption; try reflexivity; try lia;
          destruct (0 <? lhlv); [right | left]; reflexivity. }
    zstep. zstep. uck. zstep. shr2div. ldsrc SRCB 4. zs. zstep. zstep. shr2div. zs. zstep.
    rewrite (lor_add_disj 10) by lor2add_side.
    zstep. zstep.
    zstep. if_cases DstNull; zify_cond DstNull.
    + zstep. if_cases LitNZ; zify_cond LitNZ.
      * eapply (dl_ret m1 _ lev _ (2^64 - 70)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity].
      * eapply (dl_comp m1 hufv lev _ _ _ 5 ty 1 dtb); try eassumption; try reflexivity; try lia.
    + zstep. eapply (dl_comp m1 hufv lev _ _ _ 5 ty 1 dtb); try eassumption; try reflexivity; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dl_hdr_comp : forall m1 hufv lev wsv dtb ty xra x5 x7 xs1 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    bytes_at usegs m1 (DCTX + 10296) dtb -> huf_hdr_ok dtb -> (ty = 3 -> huf_tbl_ok dtb) -> hufv = Z_to_bv 64 (DCTX + 10296) ->
    2 <= Z.of_nat (length src) -> ty = 2 \/ ty = 3 ->
    evt usegs POST (ST 0x1684c m1 xra x5 (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 (Znth 0 src)) xs1
                       (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (Z.of_nat (length src))) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                       xa6 xa7 xs2 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 ty) xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31).
  Proof using HY FBY BSM SPA H1X H4X H1W H4W.
    intros until x31. intros Bund IsFrame Keep HufB HufH HufT HufP TwoMin TyC.
    pose proof Bund as Whole.
    open_dlb Bund. open_dlh HY.
    zstep. zstep. if_cases UnderFive; zify_cond UnderFive.
    { zstep. eapply (dl_ret m1 _ lev _ (2^64 - 20)); [exact Whole | lia | apply bv_eq; reflexivity | exact Keep | left; reflexivity]. }
    ldsrc SRCB 1. ldsrc SRCB 0. ldsrc SRCB 2. ldsrc SRCB 3.
    zs. zs. zs. zstep. shr2div. zs. zs. zs. zstep. zstep.
    pose proof (dl_hdr_comp2 m1 hufv lev wsv dtb ty) as Next.
    if_cases BsSmall; zify_cond BsSmall; [ | zstep ];
      [ rewrite (Z.min_l (fh_bsmax h) CAP) in Next by lia | rewrite (Z.min_r (fh_bsmax h) CAP) in Next by lia ];
      eapply Next.
    all: try reflexivity.
    all: try eassumption.
    all: try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dl_main : forall (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) hufv lev dtb,
    dctx_ptrs usegs m DCTX llt mlt oft hufv ->
    stk usegs m (DCTX + 10296) (DCTX + 26684) -> stk usegs m (DCTX + 27324) (DCTX + 29884) ->
    rw_cells usegs m (DCTX + 29928) (zfh_cells h) -> dctx_h3 usegs m DCTX pcs dsz bt stg lev fe -> dctx_h5 usegs m DCTX ws ->
    wnth ws H5_isFrameDecompression = Z_to_bv 64 1 ->
    stk usegs m (DCTX + 30372) (DCTX + 95940) -> bytes_at usegs m LSRC (map (Z_to_bv 8) src) -> stk usegs m B0 B1 ->
    stk usegs m lo SPV -> mem_inv usegs m ->
    bytes_at usegs m (DCTX + 10296) dtb -> huf_hdr_ok dtb -> (bv_unsigned lev mod 2^32 <> 0 -> huf_tbl_ok dtb) -> hufv = Z_to_bv 64 (DCTX + 10296) ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (Z.of_nat (length src))) (Z_to_bv 64 DST)
               (Z_to_bv 64 CAP) (Z_to_bv 64 0) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16714) fc None m (seg_rom usegs)).
  Proof using HY FBY BSM SPA H1X H4X H1W H4W.
    intros t0 t1 t2 a6 a7 t3 t4 t5 t6 hufv lev dtb PTRS EHUF EWK FP H3 H5 IsFrame XB SRCB BUF STK MI HufB HufH HufT HufP.
    open_dlh HY.
    pose proof (h5_isf_cell _ _ _ H5) as Isf. rewrite IsFrame in Isf.
    unfold dctx_ptrs in PTRS. unfold dctx_h3 in H3. unfold zfh_cells in FP.
    destruct H5 as [H5c H5n]. pose proof (h5_cells_size ws H5n) as H5sz.
    pose proof (proj1 HufH) as TblLen. unfold HUF_DTABLE_BYTES in TblLen.
    assert (MU : munch [(DST, DST + CAP); (DCTX + 24, DCTX + 32); (DCTX + 10296, DCTX + 26684); (DCTX + 27324, DCTX + 29884);
                        (DCTX + 30000, DCTX + 30004); (DCTX + 30096, DCTX + 95940); (SPV - 1184, SPV)] m m) by apply munch_refl.
    assert (WM : wmono usegs m m) by apply wmono_refl.
    carve_frame 96%nat STK.
    do 12 zstep.
    zstep. zstep. if_cases Long; zify_cond Long.
    2: { zstep. eapply (dl_ret _ hufv lev ws (2^64 - 20)); [ hnf; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ _) (conj _ (conj _ (conj _ (conj _
              (conj (ex_intro _ _ _) (conj _ (conj _ _))))))))))))); eassumption | lia | apply bv_eq; reflexivity | intros; reflexivity | left; reflexivity ]. }
    zstep. uck. zstep. uck. zstep. zstep. uck.
    do 3 zstep. ldsrc SRCB 0. zstep. rewrite (sx32w_small 1) by lia.
    zstep. rewrite land3_mod4. zstep. if_false.
    zstep. rewrite (zx32w_small (fh_bsmax h)) by lia.
    zstep. zstep. if_cases Comp; zify_lts Comp.
    - zstep. zstep. if_cases IsTwo; zify_cond IsTwo.
      + rewrite IsTwo.
        eapply (dl_hdr_comp m0 hufv lev ws dtb 2); try eassumption; try reflexivity; try lia.
        all: try (intros Absurd; discriminate Absurd).
        all: hnf; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ _) (conj _ (conj _ (conj _ (conj _
              (conj (ex_intro _ _ _) (conj _ (conj _ _))))))))))))); eassumption.
      + assert (IsThree : Znth 0 src mod 4 = 3) by lia.
        zstep. zstep. if_cases NoEnt; zify_cond NoEnt.
        * zstep. zstep. eapply (dl_ret _ hufv lev ws (2^64 - 30)); [ hnf; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ _) (conj _ (conj _ (conj _ (conj _
              (conj (ex_intro _ _ _) (conj _ (conj _ _))))))))))))); eassumption | lia | apply bv_eq; reflexivity | intros; reflexivity | left; reflexivity ].
        * rewrite IsThree.
          eapply (dl_hdr_comp m0 hufv lev ws dtb 3); try eassumption; try reflexivity; try lia.
          all: try (intros _; apply HufT; apply sx32_nz_mod; exact NoEnt).
          all: hnf; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ _) (conj _ (conj _ (conj _ (conj _
              (conj (ex_intro _ _ _) (conj _ (conj _ _))))))))))))); eassumption.
    - zstep. zstep. zs. zstep. shr2div. zstep. zstep. if_cases Rle; zify_cond Rle.
      + zstep. pose proof (dl_hdr_rle2 m0 hufv lev ws dtb) as Next.
        if_cases BsSmall; zify_cond BsSmall; [ | zstep ];
          [ rewrite (Z.min_l (fh_bsmax h) CAP) in Next by lia | rewrite (Z.min_r (fh_bsmax h) CAP) in Next by lia ];
          eapply Next; clear Next.
        all: try eassumption.
        all: try (intros; reflexivity).
        all: try lia.
        all: hnf; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ _) (conj _ (conj _ (conj _ (conj _
              (conj (ex_intro _ _ _) (conj _ (conj _ _))))))))))))); eassumption.
      + zstep. pose proof (dl_hdr_raw2 m0 hufv lev ws dtb) as Next.
        if_cases BsSmall; zify_cond BsSmall; [ | zstep ];
          [ rewrite (Z.min_l (fh_bsmax h) CAP) in Next by lia | rewrite (Z.min_r (fh_bsmax h) CAP) in Next by lia ];
          eapply Next; clear Next.
        all: try eassumption.
        all: try (intros; reflexivity).
        all: try lia.
        all: hnf; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ _) (conj _ (conj _ (conj _ (conj _
              (conj (ex_intro _ _ _) (conj _ (conj _ _))))))))))))); eassumption.
  Qed.

End DL.

Theorem zd_declit_proof : huf_1x_stmt -> huf_4x_stmt -> huf_1x1_wksp_stmt -> huf_4x_wksp_stmt -> zd_declit_stmt.
Proof.
  intros H1X H4X H1W H4W. unfold zd_declit_stmt, PZD_DECLIT. intros until ws.
  intros PTRS EHUF HINV EWK FP BSM H3 H5 ISF XB DCL DCH DCA SRCB FBY SLEN SRCL SRCH BUF B0D DCB CAP0 B1H DNULL DNN STK LO0 LOS SPH
         OFFD OFFB OFFSRC BD BSRC SRCD SPA MI -> -> -> -> -> ->.
  pose proof (proj1 HINV) as HUFE. destruct (hufw_full _ _ _ _ HINV EHUF) as (dtb & HTB & HOK & HTOK).
  assert (HY : dl_hyps SPV lo DCTX DST CAP B0 B1 LSRC (Z.of_nat (length src))).
  { unfold dl_hyps. repeat (split; [first [assumption | lia]|]). assumption. }
  eapply (dl_main ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe ws HY FBY BSM SPA
            H1X H4X H1W H4W t0 t1 t2 a6 a7 t3 t4 t5 t6 huf le dtb); eassumption.
Qed.
