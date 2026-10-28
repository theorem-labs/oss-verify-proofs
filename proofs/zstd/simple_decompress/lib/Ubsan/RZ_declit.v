(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
    intros m1 a bs (S0 & S1 & SW) BA. split; [exact BA|]. split; [lia|]. split; [lia|]. intros i Hi. apply (SW (a + i)). lia.
  Qed.

  Lemma u8arr_stk : forall (m1 : fmem) a (bs : list byte), u8arr usegs m1 a bs -> stk usegs m1 a (a + Z.of_nat (length bs)).
  Proof.
    intros m1 a bs U. apply rw_cells_of_u8arr in U. apply stk_of_rw_cells in U. cbn [cells_size csize] in U. rewrite Nat.add_0_r in U. exact U.
  Qed.

  Lemma bytes_at_mid : forall (m1 : fmem) A (bs : list byte) i n, bytes_at usegs m1 A bs -> 0 <= i -> 0 <= n -> i + n <= Z.of_nat (length bs) ->
    bytes_at usegs m1 (A + i) (firstn (Z.to_nat n) (skipn (Z.to_nat i) bs)) /\ Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat i) bs))) = n.
  Proof.
    intros m1 A bs i n (B0' & B1' & B) Hi Hn HL.
    assert (LEN : length (firstn (Z.to_nat n) (skipn (Z.to_nat i) bs)) = Z.to_nat n) by (rewrite firstn_length, skipn_length; lia).
    split; [|lia]. split; [lia|]. split; [lia|].
    intros j Hj. rewrite LEN in Hj.
    replace (A + i + Z.of_nat j) with (A + Z.of_nat (Z.to_nat i + j)) by lia. rewrite B by lia.
    rewrite nth_error_firstn. replace (j <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_error_skipn. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma h5_isf_cell : forall (m1 : fmem) D wsq, dctx_h5 usegs m1 D wsq -> rw_cells usegs m1 (D + 30176) [C4 (wnth wsq H5_isFrameDecompression)].
  Proof.
    intros m1 D wsq (C & L). h5_open wsq L.
    lazymatch type of C with rw_cells _ _ _ ?cs =>
      change cs with (firstn 12 cs ++ [nth 12 cs (C1 (Z_to_bv 8 0))] ++ skipn 13 cs) in C end.
    cbn [firstn skipn nth] in C.
    apply rw_cells_app in C. destruct C as [_ C]. apply rw_cells_app in C. destruct C as [C _].
    cbn [cells_size csize Nat.add] in C. replace (D + 30096 + Z.of_nat 80) with (D + 30176) in C by lia. exact C.
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
    /\ stk usegs m1 (DCTX + 10296) (DCTX + 26684) /\ stk usegs m1 (DCTX + 27324) (DCTX + 29884)
    /\ rw_cells usegs m1 (DCTX + 29928) (zfh_cells h)
    /\ dctx_h3 usegs m1 DCTX pcs dsz bt stg lev fe
    /\ dctx_h5 usegs m1 DCTX wsv
    /\ stk usegs m1 (DCTX + 30372) (DCTX + 95940)
    /\ bytes_at usegs m1 LSRC (map (Z_to_bv 8) src)
    /\ stk usegs m1 B0 B1
    /\ stk usegs m1 lo (SPV + -96)
    /\ (exists j, rw_cells usegs m1 (SPV + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ mem_inv usegs m1 /\ munch FOOT m m1 /\ wmono usegs m m1.
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
  Proof.
    intros until x31. intros I ISF KEEP HTB HOK HTOK HUFE LHR LSR DNL. pose proof I as DLI. open_dlb I. open_dlh HY.
    assert (EOFF : Z.of_nat (length dtb) = 16388) by (destruct HOK as [L _]; exact L).
    zstep. if_cases K1; zify_cond K1.
    { zstep. eapply (dl_ret _ hufv lev wsv (2^64 - 20)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity]. }
    zstep. if_cases K2; zify_cond K2.
    { eapply (dl_ret _ hufv lev wsv (2^64 - 70)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity]. }
    clear DLI. destruct H5 as [H5 L5]. h5_open wsv L5. unfold zfh_cells in FP.
    lazymatch type of ISF with ?x = _ => subst x end.
    do 9 zstep. zstep.
    assert (ELB : DCTX_litBuffer = 30352) by reflexivity.
    pose proof zd_alloclit_proof as AL. unfold zd_alloclit_stmt, PZD_ALLOCLIT in AL.
    lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
      eapply evt_cut; [ eapply AL with (SPV := SPV + -96) (DCTX := DCTX) (DST := DST) (CAP := CAP) (litSize := litSize) (ews := Z.min (fh_bsmax h) CAP) (imm := true)
                          (h := h) (ws := wl);
          first [ eassumption | reflexivity | lia | split; [exact H5 | reflexivity] ]
        | clear AL; post_call usegs m1 ] end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
    set (ews := Z.min (fh_bsmax h) CAP) in *.
    pose proof (alloc_lit_buffer_regions (fh_bsmax h) CAP litSize ews true ltac:(lia) eq_refl ltac:(unfold ZSTD_BLOCKSIZE_MAX; lia)) as REG.
    set (p := alloc_lit_buffer (fh_bsmax h) CAP litSize ews true) in *.
    destruct POST as [H5 _].
    cbv [h5_placed h5_cells mk_wcells h5_sizes wupd H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in H5.
    set (LB := lit_base_addr DCTX DST (lp_base p) + lp_buf p) in *. set (LE := lit_base_addr DCTX DST (lp_base p) + lp_end p) in *.
    zstep. zstep. zstep. zstep. if_cases K3; zify_cond K3.
    - (* [comment removed for export] *)
      zstep. zstep. uckb. zstep. zstep. zstep. zstep. zstep. uckb. zstep. zstep. zstep. zstep. zstep.
      lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
        eapply (dl_ret _ hufv lev wl (lhSize + litSize)); [ | lia | reflexivity | | ] end.
      + split; [exact PTRS|]. split; [exact EHUF|]. split; [exact EWK|]. split; [exact FP|]. split; [exact H3|]. split; [split; [exact H5| reflexivity]|].
        split; [exact XB|]. split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM].
      + intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
      + right. split; [lia|]. split.
        { exact (hufw_of_full _ _ _ _ dtb HUFE HTB HOK HTOK). }
        exists (LSRC + lhSize), litSize, LB, (LSRC + lhSize + litSize), 0.
        repeat (split; [first [reflexivity | lia]|]). left. split; [reflexivity|]. split; [reflexivity|]. right. unfold WILDCOPY_OVERLENGTH. lia.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases K4; zify_cond K4.
      { lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
          eapply (dl_ret _ hufv lev wl (2^64 - 20)); [ | lia | apply bv_eq; reflexivity | | left; reflexivity ] end.
        + split; [exact PTRS|]. split; [exact EHUF|]. split; [exact EWK|]. split; [exact FP|]. split; [exact H3|]. split; [split; [exact H5| reflexivity]|].
          split; [exact XB|]. split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM].
        + intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP. }
      pose proof (rdbl_of_bytes_at usegs _ _ _ SRCB) as RSRC. rewrite length_map in RSRC.
      cbv zeta iota in REG. unfold ZSTD_in_dst, ZSTD_split, ZSTD_not_in_dst, WILDCOPY_OVERLENGTH, ZSTD_LITBUFFEREXTRASIZE in REG.
      destruct (lp_base p) eqn:EB; [ | | contradiction].
      + destruct REG as [(ELOC & EBUF & EEND & EFIT) | (ELOC & BIG & BUF0 & (EEND & EEWS) & EWC)].
        * (* [comment removed for export] *)
          subst LB LE. cbn [lit_base_addr] in H5. rewrite ELOC, EEND, EBUF in H5.
          zstep. rewrite (sx32w_small 1) by lia. zstep. zstep. if_true.
          zstep. zstep. uckb. zstep. zstep. zstep. zstep.
          set (LB := DST + (fh_bsmax h + 32)) in *.
          destruct (stk_split usegs _ B0 LB B1 BUF ltac:(subst LB; lia)) as [BUFa BUF2].
          destruct (stk_split usegs _ LB (LB + litSize) B1 BUF2 ltac:(subst LB; lia)) as [BUFm BUFb].
          clear BUF BUF2. subst LB.
          eapply evt_cut; [ eapply (memcpy_stk (DST + (fh_bsmax h + 32)) (LSRC + lhSize) litSize);
              first [ eassumption | reflexivity | lia | (eapply rdbl_sub; [exact RSRC | lia | lia]) | (unfold hidden in DSTSRC; lia) ]
            | post_call usegs mc ].
          rename POST into BUFm.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into md end.
          pose proof (stk_merge usegs _ _ _ _ (stk_merge usegs _ _ _ _ BUFa BUFm ltac:(lia)) BUFb ltac:(lia)) as BUF. clear BUFa BUFm BUFb RSRC.
          zstep. zstep. zstep. zstep. zstep.
          lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
            eapply (dl_ret _ hufv lev wl (lhSize + litSize)); [ | lia | reflexivity | | ] end.
          -- split; [exact PTRS|]. split; [exact EHUF|]. split; [exact EWK|]. split; [exact FP|]. split; [exact H3|]. split; [split; [exact H5| reflexivity]|].
             split; [exact XB|]. split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM].
          -- intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
          -- right. split; [lia|]. split.
             { exact (hufw_of_full _ _ _ _ dtb HUFE HTB HOK HTOK). }
             exists (DST + (fh_bsmax h + 32)), litSize, (DST + (fh_bsmax h + 32)), (DST + (fh_bsmax h + 32 + litSize)), 1.
             repeat (split; [first [reflexivity | lia]|]). right. left. unfold ZSTD_in_dst, WILDCOPY_OVERLENGTH. repeat (split; [first [reflexivity | lia]|]). lia.
        * (* [comment removed for export] *)
          subst LB LE. cbn [lit_base_addr] in H5. rewrite ELOC in H5.
          assert (EBUF : lp_buf p = ews - 32 - litSize + 65536) by lia. rewrite EEND, EBUF in H5.
          zstep. rewrite (sx32w_small 2) by lia. zstep. zstep. if_false.
          zstep. zstep. uck. zstep. zstep. zstep. zstep. zstep.
          set (D1 := DST + (ews - 32 - litSize + 65536)) in *.
          destruct (stk_split usegs _ B0 D1 B1 BUF ltac:(subst D1; lia)) as [BUFa BUF2].
          destruct (stk_split usegs _ D1 (D1 + (litSize + -65536)) B1 BUF2 ltac:(subst D1; lia)) as [BUFm BUFb].
          clear BUF BUF2. subst D1.
          eapply evt_cut; [ eapply (memcpy_stk (DST + (ews - 32 - litSize + 65536)) (LSRC + lhSize) (litSize + -65536));
              first [ eassumption | reflexivity | lia | (eapply rdbl_sub; [exact RSRC | lia | lia]) | (unfold hidden in DSTSRC; lia) ]
            | post_call usegs mc ].
          rename POST into BUFm.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into md end.
          pose proof (stk_merge usegs _ _ _ _ (stk_merge usegs _ _ _ _ BUFa BUFm ltac:(lia)) BUFb ltac:(lia)) as BUF. clear BUFa BUFm BUFb RSRC.
          pose proof (rdbl_of_bytes_at usegs _ _ _ SRCB) as RSRC. rewrite length_map in RSRC.
          zstep. uck. zstep. zstep. uckb. zstep. zstep. zstep. uck. zstep. zstep. uckb. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
          destruct (stk_split usegs _ (DCTX + 30372) (DCTX + 30372 + 65536) (DCTX + 95940) XB ltac:(lia)) as [XBm XBb]. clear XB.
          eapply evt_cut; [ eapply (memcpy_stk (DCTX + 30372) (LSRC + lhSize + litSize + -65536) 65536);
              first [ eassumption | reflexivity | lia | (eapply rdbl_sub; [exact RSRC | lia | lia]) | (unfold hidden in SRCD; lia) ]
            | post_call usegs md ].
          rename POST into XBm.
          pose proof (stk_merge usegs _ _ _ _ XBm XBb ltac:(lia)) as XB. clear XBm XBb RSRC.
          zstep. zstep. zstep. zstep. zstep.
          lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
            eapply (dl_ret _ hufv lev wl (lhSize + litSize)); [ | lia | reflexivity | | ] end.
          -- split; [exact PTRS|]. split; [exact EHUF|]. split; [exact EWK|]. split; [exact FP|]. split; [exact H3|]. split; [split; [exact H5| reflexivity]|].
             split; [exact XB|]. split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM].
          -- intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
          -- right. split; [lia|]. split.
             { exact (hufw_of_full _ _ _ _ dtb HUFE HTB HOK HTOK). }
             exists (DST + (ews - 32 - litSize + 65536)), litSize, (DST + (ews - 32 - litSize + 65536)), (DST + (ews - 32 - litSize + 65536 + litSize - 65536)), 2.
             repeat (split; [first [reflexivity | lia]|]). right. right. unfold ZSTD_split, ZSTD_LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH. repeat (split; [first [reflexivity | lia]|]). lia.
      + (* [comment removed for export] *)
        destruct REG as (ELOC & EBUF & EEND & SMALL).
        subst LB LE. cbn [lit_base_addr] in H5. unfold DCTX_litExtraBuffer in H5. rewrite ELOC, EEND, EBUF in H5.
        replace (DCTX + 30372 + 0) with (DCTX + 30372) in H5 by lia.
        zstep. rewrite (sx32w_small 0) by lia. zstep. zstep. if_true.
        zstep. zstep. uckb. zstep. zstep. zstep. zstep.
        destruct (stk_split usegs _ (DCTX + 30372) (DCTX + 30372 + litSize) (DCTX + 95940) XB ltac:(lia)) as [XBm XBb]. clear XB.
        eapply evt_cut; [ eapply (memcpy_stk (DCTX + 30372) (LSRC + lhSize) litSize);
            first [ eassumption | reflexivity | lia | (eapply rdbl_sub; [exact RSRC | lia | lia]) | (unfold hidden in SRCD; lia) ]
          | post_call usegs mc ].
        rename POST into XBm.
        pose proof (stk_merge usegs _ _ _ _ XBm XBb ltac:(lia)) as XB. clear XBm XBb RSRC.
        zstep. zstep. zstep. zstep. zstep.
        lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
          eapply (dl_ret _ hufv lev wl (lhSize + litSize)); [ | lia | reflexivity | | ] end.
        * split; [exact PTRS|]. split; [exact EHUF|]. split; [exact EWK|]. split; [exact FP|]. split; [exact H3|]. split; [split; [exact H5| reflexivity]|].
          split; [exact XB|]. split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM].
        * intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
        * right. split; [lia|]. split.
          { exact (hufw_of_full _ _ _ _ dtb HUFE HTB HOK HTOK). }
          exists (DCTX + 30372), litSize, (DCTX + 30372), (DCTX + 30372 + litSize), 0.
          repeat (split; [first [reflexivity | lia]|]). left. unfold ZSTD_not_in_dst, ZSTD_LITBUFFEREXTRASIZE, DCTX_litExtraBuffer. repeat (split; [first [reflexivity | lia]|]). left. split; [reflexivity| lia].
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
  Proof.
    intros until x31. intros I ISF KEEP HTB HOK HTOK HUFE LHR LHS LSR DNL. pose proof I as DLI. open_dlb I. open_dlh HY.
    assert (EOFF : Z.of_nat (length dtb) = 16388) by (destruct HOK as [L _]; exact L).
    zstep. zstep. if_cases K1; zify_cond K1.
    { eapply (dl_ret _ hufv lev wsv (2^64 - 20)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity]. }
    zstep. zstep. if_cases K2; zify_cond K2.
    { eapply (dl_ret _ hufv lev wsv (2^64 - 70)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity]. }
    clear DLI. destruct H5 as [H5 L5]. h5_open wsv L5.
    lazymatch type of ISF with ?x = _ => subst x end.
    do 8 zstep. zstep.
    assert (ELB : DCTX_litBuffer = 30352) by reflexivity.
    pose proof zd_alloclit_proof as AL. unfold zd_alloclit_stmt, PZD_ALLOCLIT in AL.
    lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
      eapply evt_cut; [ eapply AL with (SPV := SPV + -96) (DCTX := DCTX) (DST := DST) (CAP := CAP) (litSize := litSize) (ews := Z.min (fh_bsmax h) CAP) (imm := true)
                          (h := h) (ws := wl);
          first [ eassumption | reflexivity | lia | split; [exact H5 | reflexivity] ]
        | clear AL; post_call usegs m1 ] end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
    set (ews := Z.min (fh_bsmax h) CAP) in *.
    pose proof (alloc_lit_buffer_regions (fh_bsmax h) CAP litSize ews true ltac:(lia) eq_refl ltac:(unfold ZSTD_BLOCKSIZE_MAX; lia)) as REG.
    set (p := alloc_lit_buffer (fh_bsmax h) CAP litSize ews true) in *.
    destruct POST as [H5 _].
    cbv [h5_placed h5_cells mk_wcells h5_sizes wupd H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in H5.
    set (LB := lit_base_addr DCTX DST (lp_base p) + lp_buf p) in *. set (LE := lit_base_addr DCTX DST (lp_base p) + lp_end p) in *.
    cbv zeta iota in REG. unfold ZSTD_in_dst, ZSTD_split, ZSTD_not_in_dst, WILDCOPY_OVERLENGTH, ZSTD_LITBUFFEREXTRASIZE in REG.
    set (rb := Znth lhSize src).
    pose proof (Forall_Znth _ _ lhSize FBY ltac:(lia)) as RBR. cbv beta in RBR. fold rb in RBR.
    pose proof (u8ro_read usegs mc LSRC _ lhSize _ (wa (LSRC + lhSize)) SRCB (nth_error_map_Znth (Z_to_bv 8) src lhSize ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD0.
    fold rb in RD0.
    destruct (lp_base p) eqn:EB; [ | | contradiction].
    + destruct REG as [(ELOC & EBUF & EEND & EFIT) | (ELOC & BIG & BUF0 & (EEND & EEWS) & EWC)].
      * (* [comment removed for export] *)
        subst LB LE. cbn [lit_base_addr] in H5. rewrite ELOC, EEND, EBUF in H5.
        zstep. zstep. rewrite (sx32w_small 1) by lia. zstep. zstep. zstep. zstep. if_true.
        zstep. zstep. uckb. zstep. cbv beta. rewrite (byte_lit rb) by lia. zstep. zstep.
        set (D1 := DST + (fh_bsmax h + 32)) in *.
        destruct (stk_split usegs _ B0 D1 B1 BUF ltac:(subst D1; lia)) as [BUFa BUF2].
        destruct (stk_split usegs _ D1 (D1 + litSize) B1 BUF2 ltac:(subst D1; lia)) as [BUFm BUFb].
        clear BUF BUF2. subst D1.
        eapply evt_cut; [ eapply (memset_stk (DST + (fh_bsmax h + 32)) rb litSize); first [ eassumption | reflexivity | lia ]
          | post_call usegs mc ].
        rename POST into BUFm.
        pose proof (stk_merge usegs _ _ _ _ (stk_merge usegs _ _ _ _ BUFa BUFm ltac:(lia)) BUFb ltac:(lia)) as BUF. clear BUFa BUFm BUFb.
        zstep. zstep. zstep. zstep. zstep.
        lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
          eapply (dl_ret _ hufv lev wl (lhSize + 1)); [ | lia | reflexivity | | ] end.
        -- split; [exact PTRS|]. split; [exact EHUF|]. split; [exact EWK|]. split; [exact FP|]. split; [exact H3|]. split; [split; [exact H5| reflexivity]|].
           split; [exact XB|]. split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM].
        -- intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
        -- right. split; [lia|]. split.
           { exact (hufw_of_full _ _ _ _ dtb HUFE HTB HOK HTOK). }
           exists (DST + (fh_bsmax h + 32)), litSize, (DST + (fh_bsmax h + 32)), (DST + (fh_bsmax h + 32 + litSize)), 1.
           repeat (split; [first [reflexivity | lia]|]). right. left. unfold ZSTD_in_dst, WILDCOPY_OVERLENGTH. repeat (split; [first [reflexivity | lia]|]). lia.
      * (* [comment removed for export] *)
        subst LB LE. cbn [lit_base_addr] in H5. rewrite ELOC in H5.
        assert (EBUF : lp_buf p = ews - 32 - litSize + 65536) by lia. rewrite EEND, EBUF in H5.
        zstep. zstep. rewrite (sx32w_small 2) by lia. zstep. zstep. zstep. zstep. if_false.
        zstep. uck. zstep. cbv beta. rewrite (byte_lit rb) by lia. zstep. zstep. zstep.
        set (D1 := DST + (ews - 32 - litSize + 65536)) in *.
        destruct (stk_split usegs _ B0 D1 B1 BUF ltac:(subst D1; lia)) as [BUFa BUF2].
        destruct (stk_split usegs _ D1 (D1 + (litSize + -65536)) B1 BUF2 ltac:(subst D1; lia)) as [BUFm BUFb].
        clear BUF BUF2. subst D1.
        eapply evt_cut; [ eapply (memset_stk (DST + (ews - 32 - litSize + 65536)) rb (litSize + -65536)); first [ eassumption | reflexivity | lia ]
          | post_call usegs mc ].
        rename POST into BUFm.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into md end.
        pose proof (stk_merge usegs _ _ _ _ (stk_merge usegs _ _ _ _ BUFa BUFm ltac:(lia)) BUFb ltac:(lia)) as BUF. clear BUFa BUFm BUFb.
        pose proof (u8ro_read usegs md LSRC _ lhSize _ (wa (LSRC + lhSize)) SRCB (nth_error_map_Znth (Z_to_bv 8) src lhSize ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD1.
        fold rb in RD1.
        zstep. uck. zstep. cbv beta. rewrite (byte_lit rb) by lia. zstep. zstep. zstep. zstep. zstep. zstep.
        destruct (stk_split usegs _ (DCTX + 30372) (DCTX + 30372 + 65536) (DCTX + 95940) XB ltac:(lia)) as [XBm XBb]. clear XB.
        eapply evt_cut; [ eapply (memset_stk (DCTX + 30372) rb 65536); first [ eassumption | reflexivity | lia ]
          | post_call usegs md ].
        rename POST into XBm.
        pose proof (stk_merge usegs _ _ _ _ XBm XBb ltac:(lia)) as XB. clear XBm XBb.
        zstep. zstep. zstep. zstep. zstep.
        lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
          eapply (dl_ret _ hufv lev wl (lhSize + 1)); [ | lia | reflexivity | | ] end.
        -- split; [exact PTRS|]. split; [exact EHUF|]. split; [exact EWK|]. split; [exact FP|]. split; [exact H3|]. split; [split; [exact H5| reflexivity]|].
           split; [exact XB|]. split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM].
        -- intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
        -- right. split; [lia|]. split.
           { exact (hufw_of_full _ _ _ _ dtb HUFE HTB HOK HTOK). }
           exists (DST + (ews - 32 - litSize + 65536)), litSize, (DST + (ews - 32 - litSize + 65536)), (DST + (ews - 32 - litSize + 65536 + litSize - 65536)), 2.
           repeat (split; [first [reflexivity | lia]|]). right. right. unfold ZSTD_split, ZSTD_LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH. repeat (split; [first [reflexivity | lia]|]). lia.
    + (* [comment removed for export] *)
      destruct REG as (ELOC & EBUF & EEND & SMALL).
      subst LB LE. cbn [lit_base_addr] in H5. unfold DCTX_litExtraBuffer in H5. rewrite ELOC, EEND, EBUF in H5.
      replace (DCTX + 30372 + 0) with (DCTX + 30372) in H5 by lia.
      zstep. zstep. rewrite (sx32w_small 0) by lia. zstep. zstep. zstep. zstep. if_true.
      zstep. zstep. uckb. zstep. cbv beta. rewrite (byte_lit rb) by lia. zstep. zstep.
      destruct (stk_split usegs _ (DCTX + 30372) (DCTX + 30372 + litSize) (DCTX + 95940) XB ltac:(lia)) as [XBm XBb]. clear XB.
      eapply evt_cut; [ eapply (memset_stk (DCTX + 30372) rb litSize); first [ eassumption | reflexivity | lia ]
        | post_call usegs mc ].
      rename POST into XBm.
      pose proof (stk_merge usegs _ _ _ _ XBm XBb ltac:(lia)) as XB. clear XBm XBb.
      zstep. zstep. zstep. zstep. zstep.
      lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
        eapply (dl_ret _ hufv lev wl (lhSize + 1)); [ | lia | reflexivity | | ] end.
      * split; [exact PTRS|]. split; [exact EHUF|]. split; [exact EWK|]. split; [exact FP|]. split; [exact H3|]. split; [split; [exact H5| reflexivity]|].
        split; [exact XB|]. split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM].
      * intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
      * right. split; [lia|]. split.
        { exact (hufw_of_full _ _ _ _ dtb HUFE HTB HOK HTOK). }
        exists (DCTX + 30372), litSize, (DCTX + 30372), (DCTX + 30372 + litSize), 0.
        repeat (split; [first [reflexivity | lia]|]). left. unfold ZSTD_not_in_dst, ZSTD_LITBUFFEREXTRASIZE, DCTX_litExtraBuffer. repeat (split; [first [reflexivity | lia]|]). left. split; [reflexivity| lia].
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
  Proof.
    intros until x31. intros I ISF KEEP HTB HOK HTOK HUFE LHR LHS LSR. open_dlh HY.
    zstep. zstep. if_cases K0; zify_cond K0.
    - eapply (dl_rle_b m1 hufv lev wsv litSize lhSize dtb); try eassumption; lia.
    - zstep. if_cases K1; zify_cond K1.
      + eapply (dl_ret _ hufv lev wsv (2^64 - 70)); [exact I | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity].
      + eapply (dl_rle_b m1 hufv lev wsv litSize lhSize dtb); try eassumption; lia.
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
  Proof.
    intros until x31. intros I KEEP ELB ELE ELOC HTB HOK VAL HUFE LSR RVR TYR RR PLACED. pose proof I as DLI. open_dlb I. open_dlh HY.
    assert (EOFF : Z.of_nat (length dtb) = 16388) by (destruct HOK as [L _]; exact L).
    zstep. zstep. zstep. if_cases K1; zify_cond K1.
    { eapply (dl_ret _ hufv lev wsv (2^64 - 20)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity]. }
    assert (NERR : zd_is_error r = false) by (unfold zd_is_error, ZE_maxCode; apply Z.ltb_ge; lia).
    clear DLI. destruct H5 as [H5 L5]. h5_open wsv L5.
    lazymatch type of ELB with ?x = _ => subst x end. lazymatch type of ELE with ?x = _ => subst x end. lazymatch type of ELOC with ?x = _ => subst x end.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. zstep.
      lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
        eapply (dl_ret _ hufv (Z_to_bv 64 1) wl RV); [ | lia | reflexivity | | ] end.
      + split; [exact PTRS|]. split; [exact EHUF|]. split; [exact EWK|]. split; [exact FP|]. split; [exact H3|]. split; [split; [exact H5| reflexivity]|].
        split; [exact XB|]. split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM].
      + intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
      + right. split; [lia|]. split.
        { exact (hufw_of_full _ _ _ _ dtb HUFE HTB HOK (fun _ => VAL NERR)). }
        unfold hidden in PLACED. exists LB, litSize, LB, LE, loc.
        repeat (split; [first [reflexivity | lia]|]).
        unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, ZSTD_LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH, DCTX_litExtraBuffer.
        destruct PLACED as [P|[P|P]]; [left | right; left | right; right]; repeat (split; [first [reflexivity | lia]|]); first [lia | left; lia].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
        eapply (dl_ret _ (Z_to_bv 64 (DCTX + 10296)) (Z_to_bv 64 1) wl RV); [ | lia | reflexivity | | ] end.
      + split; [exact PTRS|]. split; [exact EHUF|]. split; [exact EWK|]. split; [exact FP|]. split; [exact H3|]. split; [split; [exact H5| reflexivity]|].
        split; [exact XB|]. split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM].
      + intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
      + right. split; [lia|]. split.
        { exact (hufw_of_full _ _ _ _ dtb eq_refl HTB HOK (fun _ => VAL NERR)). }
        unfold hidden in PLACED. exists LB, litSize, LB, LE, loc.
        repeat (split; [first [reflexivity | lia]|]).
        unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, ZSTD_LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH, DCTX_litExtraBuffer.
        destruct PLACED as [P|[P|P]]; [left | right; left | right; right]; repeat (split; [first [reflexivity | lia]|]); first [lia | left; lia].
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
  Proof.
    intros until x31. intros I KEEP ELB ELE ELOC HTB HOK VAL HUFE LSR RVR TYR RR PLACED. pose proof I as DLI.
    destruct PLACED as [P | [P | (L2 & BIG & -> & -> & ER)]].
    - (* [comment removed for export] *)
      destruct P as (-> & P). open_dlb I. open_dlh HY. destruct H5 as [H5 L5]. h5_open wsv L5.
      lazymatch type of ELOC with ?x = _ => subst x end.
      zstep. zstep. rewrite (sx32w_small 0) by lia. zstep. zstep. zstep. if_true.
      eapply (dl_fin2 _ hufv lev _ litSize RV ty r LB LE 0 dtb); try eassumption; try reflexivity. left. tauto.
    - destruct P as (-> & P). open_dlb I. open_dlh HY. destruct H5 as [H5 L5]. h5_open wsv L5.
      lazymatch type of ELOC with ?x = _ => subst x end.
      zstep. zstep. rewrite (sx32w_small 1) by lia. zstep. zstep. zstep. if_true.
      eapply (dl_fin2 _ hufv lev _ litSize RV ty r LB LE 1 dtb); try eassumption; try reflexivity. right. left. tauto.
    - subst loc. open_dlb I. open_dlh HY. destruct H5 as [H5 L5]. h5_open wsv L5.
      lazymatch type of ELB with ?x = _ => subst x end. lazymatch type of ELE with ?x = _ => subst x end. lazymatch type of ELOC with ?x = _ => subst x end.
      assert (EOFF : Z.of_nat (length dtb) = 16388) by (destruct HOK as [L _]; exact L).
      zstep. zstep. rewrite (sx32w_small 2) by lia. zstep. zstep. zstep. if_false.
      zstep. zstep. zstep. uckb. zstep. zstep. uck. do 6 zstep. zstep.
      pose proof (rdbl_of_stk usegs _ _ _ BUF) as RB.
      destruct (stk_split usegs _ (DCTX + 30372) (DCTX + 30372 + 65536) (DCTX + 95940) XB ltac:(lia)) as [XBm XBb]. clear XB.
      eapply evt_cut; [ eapply (memcpy_stk (DCTX + 30372) (DST + E + -65536) 65536);
          first [ eassumption | reflexivity | lia | (eapply rdbl_sub; [exact RB | lia | lia]) | (unfold hidden in DSTD; lia) ]
        | post_call usegs m1 ].
      rename POST into XBm.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
      pose proof (stk_merge usegs _ _ _ _ XBm XBb ltac:(lia)) as XB. clear XBm XBb RB.
      zstep. zstep. uck. zstep. zstep. uck. zstep. zstep. zstep. zstep. uck. zstep. uck. zstep. zstep. zstep. zstep. zstep. zstep.
      pose proof (rdbl_of_stk usegs _ _ _ BUF) as RB.
      set (D1 := DST + (E - litSize) + 65504) in *.
      destruct (stk_split usegs _ B0 D1 B1 BUF ltac:(subst D1; lia)) as [BUFa BUF2].
      destruct (stk_split usegs _ D1 (D1 + (litSize + -65536)) B1 BUF2 ltac:(subst D1; lia)) as [BUFm BUFb].
      clear BUF BUF2. subst D1.
      eapply evt_cut; [ eapply (memmove_stk (DST + (E - litSize) + 65504) (DST + (E - litSize)) (litSize + -65536));
          first [ eassumption | reflexivity | lia | (eapply rdbl_sub; [exact RB | lia | lia]) ]
        | post_call usegs mc ].
      rename POST into BUFm.
      pose proof (stk_merge usegs _ _ _ _ (stk_merge usegs _ _ _ _ BUFa BUFm ltac:(lia)) BUFb ltac:(lia)) as BUF. clear BUFa BUFm BUFb RB.
      zstep. zstep. uck. zstep. zstep. uck. zstep. zstep. zstep. zstep. zstep. zstep. zstep. uck. zstep. uck. zstep. zstep. zstep.
      lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
        eapply (dl_fin2 _ hufv lev wl litSize RV ty r (DST + (E - litSize) + 65504) (DST + E + -32) 2 dtb); try eassumption; try reflexivity end.
      + split; [exact PTRS|]. split; [exact EHUF|]. split; [exact EWK|]. split; [exact FP|]. split; [exact H3|]. split; [split; [exact H5| reflexivity]|].
        split; [exact XB|]. split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM].
      + intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
      + right. right. repeat (split; [lia|]). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dl_pf : forall (n : nat) k m1 xra x5 x6 x7 xs0 xs1 xa3 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    Z.of_nat n = 256 - k -> 0 <= k ->
    (forall xa4 xa6', evt usegs POST (ST 0x16b9c m1 xra x5 x6 x7 xs0 xs1 (Z_to_bv 64 (DCTX + 10296)) (Z_to_bv 64 1) (Z_to_bv 64 16324) xa3 xa4 xa5 xa6' xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31)) ->
    evt usegs POST (ST 0x16b7c m1 xra x5 x6 x7 xs0 xs1 (Z_to_bv 64 (DCTX + 10296)) (Z_to_bv 64 1) (Z_to_bv 64 16324) xa3 (Z_to_bv 64 (64 * k)) xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31).
  Proof.
    induction n as [|n IH]; intros until x31; intros EN K0 KONT; pose proof HY as (DCL & DCH & _).
    - assert (k = 256) by lia. subst k.
      zstep. zstep. zstep. uck. zstep. zstep. zstep. uckb. zstep. zstep. if_false. apply KONT.
    - zstep. zstep. zstep. uck. zstep. zstep. zstep. uckb. zstep. zstep. if_cases KL; zify_cond KL; [| exfalso; lia].
      replace (64 * k + 64) with (64 * (k + 1)) by lia.
      eapply IH; [lia | lia | exact KONT].
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
  Proof.
    intros until x31. intros I L0 KEEP0 HTB HOK VALR HUFE LHR LSR LCR RVR FOURR TYR DNL. open_dlb I. open_dlh HY.
    assert (EOFF : Z.of_nat (length dtb) = 16388) by (destruct HOK as [L _]; exact L).
    set (ews := Z.min (fh_bsmax h) CAP) in *.
    pose proof (alloc_lit_buffer_regions (fh_bsmax h) CAP litSize ews false ltac:(lia) eq_refl ltac:(unfold ZSTD_BLOCKSIZE_MAX; lia)) as REG.
    set (p := alloc_lit_buffer (fh_bsmax h) CAP litSize ews false) in *.
    destruct H5 as [H5 _]. h5_open wsv0 L0.
    cbv [h5_placed h5_cells mk_wcells h5_sizes wupd H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in H5.
    set (LB := lit_base_addr DCTX DST (lp_base p) + lp_buf p) in *. set (LE := lit_base_addr DCTX DST (lp_base p) + lp_end p) in *.
    cbv zeta iota in REG. unfold ZSTD_in_dst, ZSTD_split, ZSTD_not_in_dst, WILDCOPY_OVERLENGTH, ZSTD_LITBUFFEREXTRASIZE in REG.
    subst hufv.
    pose proof (bytes_at_mid _ _ _ lhSize litCSize SRCB ltac:(lia) ltac:(lia) ltac:(rewrite length_map; lia)) as [HSRC HSL].
    set (hsrc := firstn (Z.to_nat litCSize) (skipn (Z.to_nat lhSize) (map (Z_to_bv 8) src))) in *.
    unfold hidden in TYR, FOURR.
    destruct (lp_base p) eqn:EB; [ | | contradiction].
    + destruct REG as [(ELOC & EBUF & EEND & EFIT) | (ELOC & BIG & BUF0 & (EEND & EEWS) & EWC)].
      * (* [comment removed for export] *)
        subst LB LE. cbn [lit_base_addr] in H5. rewrite ELOC, EEND, EBUF in H5.
        assert (EDB : HUF_DTABLE_BYTES = 16388) by reflexivity.
        assert (E1X : HUF_1X_STACK = 144) by reflexivity. assert (E4X : HUF_4X_STACK = 912) by reflexivity.
        assert (E1W : HUF_1X1W_STACK = 1072) by reflexivity. assert (E4W : HUF_4XW_STACK = 1088) by reflexivity.
        destruct TYR as [-> | ->]; destruct FOURR as [-> | ->].
        -- pose proof (stk_bytes_u8arr _ _ _ ltac:(rewrite EOFF; replace (DCTX + 10296 + 16388) with (DCTX + 26684) by lia; exact EHUF) HTB) as DTU.
           replace (DCTX + 29884) with (DCTX + 27324 + 2560) in EWK by lia.
           zstep. zstep. zstep. zstep. if_true. do 4 zstep. zstep. if_true. zstep. uckb. do 9 zstep. zstep.
           huf_call_wksp PHUF_1X1_WKSP HUF_1X1W_STACK H1W (DST + (fh_bsmax h + 32)) B0 B1.
           huf_after_wksp (DST + (fh_bsmax h + 32)) (DST + (fh_bsmax h + 32 + litSize)) 1 0.
        -- pose proof (stk_bytes_u8arr _ _ _ ltac:(rewrite EOFF; replace (DCTX + 10296 + 16388) with (DCTX + 26684) by lia; exact EHUF) HTB) as DTU.
           replace (DCTX + 29884) with (DCTX + 27324 + 2560) in EWK by lia.
           zstep. zstep. zstep. zstep. if_true. do 4 zstep. zstep. if_false. zstep. uckb. do 9 zstep. zstep.
           huf_call_wksp PHUF_4X_WKSP HUF_4XW_STACK H4W (DST + (fh_bsmax h + 32)) B0 B1.
           zstep.
           huf_after_wksp (DST + (fh_bsmax h + 32)) (DST + (fh_bsmax h + 32 + litSize)) 1 0.
        -- pose proof (VALR eq_refl) as VOK.
           zstep. zstep. zstep. zstep. if_false. do 3 zstep. zstep. if_true. zstep. uckb. do 4 zstep. zstep.
           huf_call_using PHUF_1X HUF_1X_STACK H1X (DST + (fh_bsmax h + 32)) B0 B1.
           zstep.
           huf_after_using (DST + (fh_bsmax h + 32)) (DST + (fh_bsmax h + 32 + litSize)) 1 0.
        -- pose proof (VALR eq_refl) as VOK.
           zstep. zstep. zstep. zstep. if_false. do 3 zstep. zstep. if_false. zstep. uckb. do 4 zstep. zstep.
           huf_call_using PHUF_4X HUF_4X_STACK H4X (DST + (fh_bsmax h + 32)) B0 B1.
           zstep.
           huf_after_using (DST + (fh_bsmax h + 32)) (DST + (fh_bsmax h + 32 + litSize)) 1 0.
      * (* [comment removed for export] *)
        subst LB LE. cbn [lit_base_addr] in H5. rewrite ELOC in H5.
        assert (EBUF : lp_buf p = ews - litSize) by lia. rewrite EEWS, EBUF in H5.
        assert (EDB : HUF_DTABLE_BYTES = 16388) by reflexivity.
        assert (E1X : HUF_1X_STACK = 144) by reflexivity. assert (E4X : HUF_4X_STACK = 912) by reflexivity.
        assert (E1W : HUF_1X1W_STACK = 1072) by reflexivity. assert (E4W : HUF_4XW_STACK = 1088) by reflexivity.
        destruct TYR as [-> | ->]; destruct FOURR as [-> | ->].
        -- pose proof (stk_bytes_u8arr _ _ _ ltac:(rewrite EOFF; replace (DCTX + 10296 + 16388) with (DCTX + 26684) by lia; exact EHUF) HTB) as DTU.
           replace (DCTX + 29884) with (DCTX + 27324 + 2560) in EWK by lia.
           zstep. zstep. zstep. zstep. if_true. do 4 zstep. zstep. if_true. zstep. uckb. do 9 zstep. zstep.
           huf_call_wksp PHUF_1X1_WKSP HUF_1X1W_STACK H1W (DST + (ews - litSize)) B0 B1.
           huf_after_wksp (DST + (ews - litSize)) (DST + ews) 2 ews.
        -- pose proof (stk_bytes_u8arr _ _ _ ltac:(rewrite EOFF; replace (DCTX + 10296 + 16388) with (DCTX + 26684) by lia; exact EHUF) HTB) as DTU.
           replace (DCTX + 29884) with (DCTX + 27324 + 2560) in EWK by lia.
           zstep. zstep. zstep. zstep. if_true. do 4 zstep. zstep. if_false. zstep. uckb. do 9 zstep. zstep.
           huf_call_wksp PHUF_4X_WKSP HUF_4XW_STACK H4W (DST + (ews - litSize)) B0 B1.
           zstep.
           huf_after_wksp (DST + (ews - litSize)) (DST + ews) 2 ews.
        -- pose proof (VALR eq_refl) as VOK.
           zstep. zstep. zstep. zstep. if_false. do 3 zstep. zstep. if_true. zstep. uckb. do 4 zstep. zstep.
           huf_call_using PHUF_1X HUF_1X_STACK H1X (DST + (ews - litSize)) B0 B1.
           zstep.
           huf_after_using (DST + (ews - litSize)) (DST + ews) 2 ews.
        -- pose proof (VALR eq_refl) as VOK.
           zstep. zstep. zstep. zstep. if_false. do 3 zstep. zstep. if_false. zstep. uckb. do 4 zstep. zstep.
           huf_call_using PHUF_4X HUF_4X_STACK H4X (DST + (ews - litSize)) B0 B1.
           zstep.
           huf_after_using (DST + (ews - litSize)) (DST + ews) 2 ews.
    + (* [comment removed for export] *)
      destruct REG as (ELOC & EBUF & EEND & SMALL).
      subst LB LE. cbn [lit_base_addr] in H5. unfold DCTX_litExtraBuffer in H5. rewrite ELOC, EEND, EBUF in H5.
      replace (DCTX + 30372 + 0) with (DCTX + 30372) in H5 by lia.
      assert (EDB : HUF_DTABLE_BYTES = 16388) by reflexivity.
      assert (E1X : HUF_1X_STACK = 144) by reflexivity. assert (E4X : HUF_4X_STACK = 912) by reflexivity.
      assert (E1W : HUF_1X1W_STACK = 1072) by reflexivity. assert (E4W : HUF_4XW_STACK = 1088) by reflexivity.
      destruct TYR as [-> | ->]; destruct FOURR as [-> | ->].
      * pose proof (stk_bytes_u8arr _ _ _ ltac:(rewrite EOFF; replace (DCTX + 10296 + 16388) with (DCTX + 26684) by lia; exact EHUF) HTB) as DTU.
        replace (DCTX + 29884) with (DCTX + 27324 + 2560) in EWK by lia.
        zstep. zstep. zstep. zstep. if_true. do 4 zstep. zstep. if_true. zstep. uckb. do 9 zstep. zstep.
        huf_call_wksp PHUF_1X1_WKSP HUF_1X1W_STACK H1W (DCTX + 30372) (DCTX + 30372) (DCTX + 95940).
        huf_after_wksp (DCTX + 30372) (DCTX + 30372 + litSize) 0 0.
      * pose proof (stk_bytes_u8arr _ _ _ ltac:(rewrite EOFF; replace (DCTX + 10296 + 16388) with (DCTX + 26684) by lia; exact EHUF) HTB) as DTU.
        replace (DCTX + 29884) with (DCTX + 27324 + 2560) in EWK by lia.
        zstep. zstep. zstep. zstep. if_true. do 4 zstep. zstep. if_false. zstep. uckb. do 9 zstep. zstep.
        huf_call_wksp PHUF_4X_WKSP HUF_4XW_STACK H4W (DCTX + 30372) (DCTX + 30372) (DCTX + 95940).
        zstep.
        huf_after_wksp (DCTX + 30372) (DCTX + 30372 + litSize) 0 0.
      * pose proof (VALR eq_refl) as VOK.
        zstep. zstep. zstep. zstep. if_false. do 3 zstep. zstep. if_true. zstep. uckb. do 4 zstep. zstep.
        huf_call_using PHUF_1X HUF_1X_STACK H1X (DCTX + 30372) (DCTX + 30372) (DCTX + 95940).
        zstep.
        huf_after_using (DCTX + 30372) (DCTX + 30372 + litSize) 0 0.
      * pose proof (VALR eq_refl) as VOK.
        zstep. zstep. zstep. zstep. if_false. do 3 zstep. zstep. if_false. zstep. uckb. do 4 zstep. zstep.
        huf_call_using PHUF_4X HUF_4X_STACK H4X (DCTX + 30372) (DCTX + 30372) (DCTX + 95940).
        zstep.
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
  Proof.
    intros until x31. intros I ISF KEEP HTB HOK VALR HUFE LHR LSR LCR FOURR TYR DNL. pose proof I as DLI. open_dlb I. open_dlh HY.
    assert (EOFF : Z.of_nat (length dtb) = 16388) by (destruct HOK as [L _]; exact L).
    zstep. if_cases K1; zify_cond K1.
    { zstep. eapply (dl_ret _ hufv lev wsv (2^64 - 20)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity]. }
    zstep. zstep.
    assert (EL : Z.land (four mod 18446744073709551616) (Z.b2z (litSize <? 6)) = if (four =? 1) && (litSize <? 6) then 1 else 0).
    { unfold hidden in FOURR. destruct FOURR as [-> | ->]; destruct (litSize <? 6); reflexivity. }
    rewrite EL. clear EL.
    zstep. if_cases K2; zify_cond K2.
    2:{ zstep. zstep. eapply (dl_ret _ hufv lev wsv (2^64 - 24)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity]. }
    clear K2.
    zstep. zstep. if_cases K3; zify_cond K3.
    { zstep. eapply (dl_ret _ hufv lev wsv (2^64 - 20)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity]. }
    zstep. if_cases K4; zify_cond K4.
    { eapply (dl_ret _ hufv lev wsv (2^64 - 70)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity]. }
    clear DLI. destruct H5 as [H5 L5]. h5_open wsv L5.
    lazymatch type of ISF with ?x = _ => subst x end.
    do 8 zstep. zstep.
    assert (ELB : DCTX_litBuffer = 30352) by reflexivity.
    pose proof zd_alloclit_proof as AL. unfold zd_alloclit_stmt, PZD_ALLOCLIT in AL.
    lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
      eapply evt_cut; [ eapply AL with (SPV := SPV + -96) (DCTX := DCTX) (DST := DST) (CAP := CAP) (litSize := litSize) (ews := Z.min (fh_bsmax h) CAP) (imm := false)
                          (h := h) (ws := wl);
          first [ eassumption | reflexivity | lia | split; [exact H5 | reflexivity] ]
        | clear AL; post_call usegs m1 ] end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end. rename POST into H5P.
    assert (HUFGO : forall xra x5 x6 x7 xa0 xa1 xa2 xa4 xa6 xa7 xs9v x28 x29 x30 x31,
              evt usegs POST (ST 0x16b9c mc xra x5 x6 x7 (Z_to_bv 64 litSize) (Z_to_bv 64 DCTX) xa0 xa1 xa2 (Z_to_bv 64 LSRC) xa4 (Z_to_bv 64 DCTX) xa6 xa7
                       (Z_to_bv 64 litCSize) (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 ty) (Z_to_bv 64 (lhSize + litCSize)) (Z_to_bv 64 lhSize) xs9v
                       (Z_to_bv 64 four) (Z_to_bv 64 LSRC) x28 x29 x30 x31)).
    { intros. lazymatch type of H5P with dctx_h5 _ _ _ (h5_placed ?wl _ _ _) =>
        eapply (dl_huf mc hufv lev wl litSize litCSize lhSize ty four dtb); try eassumption; try reflexivity; try lia end.
      split; [exact PTRS|]. split; [exact EHUF|]. split; [exact EWK|]. split; [exact FP|]. split; [exact H3|]. split; [exact H5P|].
        split; [exact XB|]. split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM].
      }
    destruct H5P as [H5 _]. cbv [h5_placed h5_cells mk_wcells h5_sizes wupd H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in H5.
    subst hufv. zstep. zstep. zstep. zstep. if_cases K5; zify_cond K5.
    - apply HUFGO.
    - zstep. zstep. if_cases K6; zify_cond K6.
      + apply HUFGO.
      + zstep. zstep. zstep. zstep. zstep. b2z_decide.
        eapply (dl_pf 256 0); [reflexivity | lia |]. intros. apply HUFGO.
  Qed.

  Ltac ldsrc i A :=
    let RD := fresh "RD" in let R := fresh "BR" in
    pose proof (Forall_Znth _ _ i FBY ltac:(lia)) as R; cbv beta in R;
    lazymatch goal with SRCBq : bytes_at _ ?mx LSRC _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u8ro_read usegs mx LSRC _ i _ (wa A) SRCBq (nth_error_map_Znth (Z_to_bv 8) src i ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end;
    zstep; cbv beta; rewrite (byte_lit (Znth i src)) by lia.


  (* [comment removed for export] *)
  Lemma dl_hdr_raw2 : forall m1 hufv lev wsv dtb lhlv xra x7 xa7 xs1 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    bytes_at usegs m1 (DCTX + 10296) dtb -> huf_hdr_ok dtb -> (bv_unsigned lev mod 2^32 <> 0 -> huf_tbl_ok dtb) -> hufv = Z_to_bv 64 (DCTX + 10296) ->
    2 <= Z.of_nat (length src) ->
    evt usegs POST (ST 0x167e0 m1 xra (Z_to_bv 64 (Z.min (fh_bsmax h) CAP)) (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 (Znth 0 src)) xs1
                       (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (Z.of_nat (length src))) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                       (Z_to_bv 64 lhlv) xa7 (Z_to_bv 64 (DCTX + 30120)) (Z_to_bv 64 (DCTX + 29944)) xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I ISF KEEP HTB HOK HTOK HUFE S2. pose proof I as DLI. open_dlb I. open_dlh HY.
    pose proof (Forall_Znth _ _ 0 FBY ltac:(lia)) as B0R. cbv beta in B0R. set (b0 := Znth 0 src) in *.
    zstep. zstep. if_cases KA; zify_cond KA.
    - (* [comment removed for export] *)
      ldsrc 1 (LSRC + 1). fold b0. ldsrc 0 LSRC. fold b0.
      zstep. zstep. zstep. zstep. zstep. zstep.
      set (LS := Z.lor (Znth 1 src ≪ 8 mod 18446744073709551616) b0 ≫ 4).
      assert (LSR : 0 <= LS < 2^20).
      { subst LS. rewrite Z.shiftl_mul_pow2, Z.mod_small by lia. rewrite (lor_add_disj 8) by (first [lia | apply Z_mod_mult]).
        rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
      clearbody LS.
      if_cases KD; zify_cond KD.
      + zstep. if_cases KZ; zify_cond KZ.
        * eapply (dl_ret _ hufv lev wsv (2^64 - 70)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity].
        * eapply (dl_raw m1 hufv lev wsv LS 2 dtb); try eassumption; try lia.
      + zstep. eapply (dl_raw m1 hufv lev wsv LS 2 dtb); try eassumption; try lia.
    - zstep. zstep. if_cases KB; zify_cond KB.
      + (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        set (LS := b0 ≫ 3).
        assert (LSR : 0 <= LS < 2^20) by (subst LS; rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
        clearbody LS.
        if_cases KD; zify_cond KD.
        * eapply (dl_raw m1 hufv lev wsv LS 1 dtb); try eassumption; try lia.
        * zstep. if_cases KZ; zify_cond KZ.
          -- eapply (dl_ret _ hufv lev wsv (2^64 - 70)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity].
          -- eapply (dl_raw m1 hufv lev wsv LS 1 dtb); try eassumption; try lia.
      + (* [comment removed for export] *)
        zstep. zstep. if_cases KS; zify_cond KS.
        { zstep. eapply (dl_ret _ hufv lev wsv (2^64 - 20)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity]. }
        zstep. zstep. uck. ldsrc 1 (LSRC + 1). fold b0. ldsrc 0 LSRC. fold b0. ldsrc 2 (LSRC + 2). fold b0.
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        set (LS := Z.lor (Znth 2 src ≪ 16 mod 18446744073709551616) (Z.lor (Znth 1 src ≪ 8 mod 18446744073709551616) b0) ≫ 4).
        assert (LSR : 0 <= LS < 2^20).
        { subst LS. rewrite !Z.shiftl_mul_pow2 by lia. rewrite !Z.mod_small by lia. rewrite (lor_add_disj 8 (Znth 1 src * 2^8)) by (first [lia | apply Z_mod_mult]).
          rewrite (lor_add_disj 16) by (first [lia | apply Z_mod_mult]).
          rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
        clearbody LS.
        if_cases KD; zify_cond KD.
        * zstep. if_cases KZ; zify_cond KZ.
          -- eapply (dl_ret _ hufv lev wsv (2^64 - 70)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity].
          -- eapply (dl_raw m1 hufv lev wsv LS 3 dtb); try eassumption; try lia.
        * zstep. eapply (dl_raw m1 hufv lev wsv LS 3 dtb); try eassumption; try lia.
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
  Proof.
    intros until x31. intros I ISF KEEP HTB HOK HTOK HUFE S2. pose proof I as DLI. open_dlb I. open_dlh HY.
    pose proof (Forall_Znth _ _ 0 FBY ltac:(lia)) as B0R. cbv beta in B0R. set (b0 := Znth 0 src) in *.
    zstep. zstep. if_cases KA; zify_cond KA.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases KS; zify_cond KS.
      { zstep. eapply (dl_ret _ hufv lev wsv (2^64 - 20)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity]. }
      ldsrc 1 (LSRC + 1). fold b0. ldsrc 0 LSRC. fold b0.
      zstep. zstep. zstep. zstep.
      set (LS := Z.lor (Znth 1 src ≪ 8 mod 18446744073709551616) b0 ≫ 4).
      assert (LSR : 0 <= LS < 2^20).
      { subst LS. rewrite Z.shiftl_mul_pow2, Z.mod_small by lia. rewrite (lor_add_disj 8) by (first [lia | apply Z_mod_mult]).
        rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
      clearbody LS.
      eapply (dl_rle m1 hufv lev wsv LS 2 dtb); try eassumption; try lia.
    - zstep. zstep. if_cases KB; zify_cond KB.
      + (* [comment removed for export] *)
        zstep. zstep.
        set (LS := b0 ≫ 3).
        assert (LSR : 0 <= LS < 2^20) by (subst LS; rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
        clearbody LS.
        eapply (dl_rle m1 hufv lev wsv LS 1 dtb); try eassumption; try lia.
      + (* [comment removed for export] *)
        zstep. zstep. if_cases KS; zify_cond KS.
        { zstep. eapply (dl_ret _ hufv lev wsv (2^64 - 20)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity]. }
        zstep. zstep. zstep. uck. ldsrc 1 (LSRC + 1). fold b0. ldsrc 0 LSRC. fold b0. ldsrc 2 (LSRC + 2). fold b0.
        zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        set (LS := Z.lor (Znth 2 src ≪ 16 mod 18446744073709551616) (Z.lor (Znth 1 src ≪ 8 mod 18446744073709551616) b0) ≫ 4).
        assert (LSR : 0 <= LS < 2^20).
        { subst LS. rewrite !Z.shiftl_mul_pow2 by lia. rewrite !Z.mod_small by lia. rewrite (lor_add_disj 8 (Znth 1 src * 2^8)) by (first [lia | apply Z_mod_mult]).
          rewrite (lor_add_disj 16) by (first [lia | apply Z_mod_mult]).
          rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
        clearbody LS.
        eapply (dl_rle m1 hufv lev wsv LS 3 dtb); try eassumption; try lia.
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
  Proof.
    intros until x31. intros I ISF KEEP HTB HOK VALR HUFE S5 TYR T0R T2R T2M LHR ->. pose proof I as DLI. open_dlb I. open_dlh HY.
    destruct H5 as [H5 L5]. h5_open wsv L5.
    assert (ELHC : Z.lor T2 T0 = T2 + T0) by (apply (lor_add_disj 16); [lia | lia | exact T2M]).
    zstep. zstep. zstep. rewrite ELHC. set (lhc := T2 + T0) in *. assert (LHCR : 0 <= lhc < 2^32) by (subst lhc; lia). clearbody lhc.
    zstep. if_cases KA; zify_cond KA.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      set (LS := (lhc ≪ 46 mod 18446744073709551616) ≫ 50). set (LC := lhc ≫ 18).
      assert (LSR : 0 <= LS < 2^18).
      { subst LS. pose proof (Z.mod_pos_bound (lhc ≪ 46) 18446744073709551616 ltac:(lia)). rewrite Z.shiftr_div_pow2 by lia.
        split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
      assert (LCR : 0 <= LC < 2^18) by (subst LC; rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      clearbody LS LC.
      zstep. if_cases KD; zify_cond KD.
      + zstep. if_cases KZ; zify_cond KZ.
        * eapply (dl_ret _ hufv lev _ (2^64 - 70)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity].
        * lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
            eapply (dl_comp m1 hufv lev wl LS LC 4 ty 1 dtb); try eassumption; try reflexivity; try lia; try exact DLI end.
      + zstep.
        lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
          eapply (dl_comp m1 hufv lev wl LS LC 4 ty 1 dtb); try eassumption; try reflexivity; try lia; try exact DLI end.
    - zstep. zstep. if_cases KB; zify_cond KB.
      + (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep.
        set (LS := (lhc ≪ 50 mod 18446744073709551616) ≫ 54). set (LC := (lhc ≪ 40 mod 18446744073709551616) ≫ 54).
        set (FO := Z.b2z (0 <? lhlv)).
        assert (LSR : 0 <= LS < 2^18).
        { subst LS. pose proof (Z.mod_pos_bound (lhc ≪ 50) 18446744073709551616 ltac:(lia)). rewrite Z.shiftr_div_pow2 by lia.
          split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
        assert (LCR : 0 <= LC < 2^18).
        { subst LC. pose proof (Z.mod_pos_bound (lhc ≪ 40) 18446744073709551616 ltac:(lia)). rewrite Z.shiftr_div_pow2 by lia.
          split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
        assert (FOR : FO = 0 \/ FO = 1) by (subst FO; destruct (0 <? lhlv); auto).
        clearbody LS LC FO.
        zstep. if_cases KD; zify_cond KD.
        * lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
            eapply (dl_comp m1 hufv lev wl LS LC 3 ty FO dtb); try eassumption; try reflexivity; try lia; try exact DLI end.
        * zstep. if_cases KZ; zify_cond KZ.
          -- eapply (dl_ret _ hufv lev _ (2^64 - 70)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity].
          -- lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
               eapply (dl_comp m1 hufv lev wl LS LC 3 ty FO dtb); try eassumption; try reflexivity; try lia; try exact DLI end.
      + (* [comment removed for export] *)
        zstep. zstep. uck. zstep. ldsrc 4 (LSRC + 4). zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        set (LS := (lhc ≪ 42 mod 18446744073709551616) ≫ 46). set (LC := Z.lor (Znth 4 src ≪ 10 mod 18446744073709551616) (lhc ≫ 22)).
        assert (LSR : 0 <= LS < 2^18).
        { subst LS. pose proof (Z.mod_pos_bound (lhc ≪ 42) 18446744073709551616 ltac:(lia)). rewrite Z.shiftr_div_pow2 by lia.
          split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
        assert (LCR : 0 <= LC < 2^18).
        { subst LC. assert (Q : 0 <= lhc ≫ 22 < 2^10) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
          rewrite Z.shiftl_mul_pow2, Z.mod_small by lia. rewrite (lor_add_disj 10) by (first [lia | apply Z_mod_mult]). lia. }
        clearbody LS LC.
        zstep. if_cases KD; zify_cond KD.
        * zstep. if_cases KZ; zify_cond KZ.
          -- eapply (dl_ret _ hufv lev _ (2^64 - 70)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity].
          -- lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
               eapply (dl_comp m1 hufv lev wl LS LC 5 ty 1 dtb); try eassumption; try reflexivity; try lia; try exact DLI end.
        * zstep.
          lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
            eapply (dl_comp m1 hufv lev wl LS LC 5 ty 1 dtb); try eassumption; try reflexivity; try lia; try exact DLI end.
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
  Proof.
    intros until x31. intros I ISF KEEP HTB HOK VALR HUFE S2 TYR. pose proof I as DLI. open_dlb I. open_dlh HY.
    pose proof (Forall_Znth _ _ 0 FBY ltac:(lia)) as B0R. cbv beta in B0R. set (b0 := Znth 0 src) in *.
    zstep. zstep. if_cases KS; zify_cond KS.
    { zstep. eapply (dl_ret _ hufv lev wsv (2^64 - 20)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity]. }
    ldsrc 1 (LSRC + 1). fold b0. ldsrc 0 LSRC. fold b0. ldsrc 2 (LSRC + 2). fold b0. ldsrc 3 (LSRC + 3). fold b0.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    set (T0 := Z.lor (Znth 1 src ≪ 8 mod 18446744073709551616) b0).
    set (T2 := Z.lor (Znth 3 src ≪ 24 mod 18446744073709551616) (Znth 2 src ≪ 16 mod 18446744073709551616)).
    set (LHL := (b0 ≪ 60 mod 18446744073709551616) ≫ 62).
    assert (T0R : 0 <= T0 < 2^16).
    { subst T0. rewrite Z.shiftl_mul_pow2, Z.mod_small by lia. rewrite (lor_add_disj 8) by (first [lia | apply Z_mod_mult]). lia. }
    assert (T2E : T2 = Znth 3 src * 2^24 + Znth 2 src * 2^16).
    { subst T2. rewrite !Z.shiftl_mul_pow2 by lia. rewrite !Z.mod_small by lia. apply (lor_add_disj 24); [lia | lia | apply Z_mod_mult]. }
    assert (T2R : 0 <= T2 < 2^32) by lia.
    assert (T2M : T2 mod 2^16 = 0).
    { rewrite T2E. replace (Znth 3 src * 2 ^ 24 + Znth 2 src * 2 ^ 16) with ((Znth 3 src * 2^8 + Znth 2 src) * 2^16) by lia. apply Z_mod_mult. }
    assert (LHR : 0 <= LHL < 2^64).
    { subst LHL. pose proof (Z.mod_pos_bound (b0 ≪ 60) 18446744073709551616 ltac:(lia)). rewrite Z.shiftr_div_pow2 by lia.
      split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    clearbody T0 T2 LHL. clear T2E.
    zstep. if_cases KE; zify_cond KE.
    - pose proof (dl_hdr_comp2 m1 hufv lev wsv dtb ty T0 T2 LHL) as L. replace (Z.min (fh_bsmax h) CAP) with (fh_bsmax h) in L by lia.
      eapply L; try eassumption; try reflexivity; try lia.
    - zstep. pose proof (dl_hdr_comp2 m1 hufv lev wsv dtb ty T0 T2 LHL) as L. replace (Z.min (fh_bsmax h) CAP) with CAP in L by lia.
      eapply L; try eassumption; try reflexivity; try lia.
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
  Proof.
    intros until dtb. intros PTRS EHUF EWK FP H3 H5 ISF XB SRCB BUF STK MI HTB HOK HTOK HUFE. open_dlh HY.
    assert (EOFF : Z.of_nat (length dtb) = 16388) by (destruct HOK as [L _]; exact L).
    assert (MU : munch FOOT m m) by apply munch_refl. assert (WM : wmono usegs m m) by apply wmono_refl.
    assert (KEEP : forall i, h5_block_owned i = false -> wnth ws i = wnth ws i) by reflexivity.
    pose proof (h5_isf_cell _ _ _ H5) as ISFC. rewrite ISF in ISFC.
    unfold zfh_cells in FP. unfold dctx_ptrs in PTRS. unfold dctx_h3 in H3. destruct H5 as [H5 L5].
    assert (H5SZ : Z.of_nat (cells_size (h5_cells ws)) = 276) by (rewrite (h5_cells_size ws L5); reflexivity).
    zstep. carve_frame 96%nat STK.
    do 11 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mp end.
    assert (DLI : DLB hufv lev ws mp).
    { split; [exact PTRS|]. split; [exact EHUF|]. split; [exact EWK|]. split; [exact FP|]. split; [exact H3|]. split; [split; [exact H5 | exact L5]|].
      split; [exact XB|]. split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM]. }
    zstep. zstep. if_cases K0; zify_cond K0.
    2:{ (* [comment removed for export] *)
        zstep. eapply (dl_ret _ hufv lev ws (2^64 - 20)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity]. }
    pose proof (Forall_Znth _ _ 0 FBY ltac:(lia)) as B0R. cbv beta in B0R.
    zstep. uck. zstep. uck. zstep. zstep. uck. zstep. zstep. zstep. ldsrc 0 LSRC. set (b0 := Znth 0 src) in *.
    zstep. rewrite (sx32w_small 1) by lia. zstep. zstep. if_false.
    zstep. rewrite (zx32w_small (fh_bsmax h)) by lia. zstep. zstep. if_cases KT; zify_cond KT.
    - (* [comment removed for export] *)
      set (ty := Z.land b0 3) in *.
      assert (EL : Z.land b0 3 = b0 mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
      assert (TYB : 0 <= ty <= 3) by (subst ty; rewrite EL; pose proof (Z.mod_pos_bound b0 4 ltac:(lia)); lia). clear EL.
      rewrite (signed_lit ty) in KT by lia. clearbody ty.
      zstep. zstep. if_cases K2; zify_cond K2.
      + eapply (dl_hdr_comp mp hufv lev ws dtb ty); try eassumption; try lia.
      + zstep. zstep. if_cases K3; zify_cond K3.
        * zstep. zstep. eapply (dl_ret _ hufv lev ws (2^64 - 30)); [exact DLI | lia | apply bv_eq; reflexivity | exact KEEP | left; reflexivity].
        * eapply (dl_hdr_comp mp hufv lev ws dtb ty); try eassumption; try lia.
          intros _. apply HTOK. apply sx32_nz_mod. exact K3.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases KR; zify_cond KR.
      + (* [comment removed for export] *)
        zstep. if_cases KE; zify_cond KE.
        * pose proof (dl_hdr_rle2 mp hufv lev ws dtb) as L. replace (Z.min (fh_bsmax h) CAP) with (fh_bsmax h) in L by lia.
          eapply L; try eassumption; try lia.
        * zstep. pose proof (dl_hdr_rle2 mp hufv lev ws dtb) as L. replace (Z.min (fh_bsmax h) CAP) with CAP in L by lia.
          eapply L; try eassumption; try lia.
      + (* [comment removed for export] *)
        zstep. if_cases KE; zify_cond KE.
        * pose proof (dl_hdr_raw2 mp hufv lev ws dtb) as L. replace (Z.min (fh_bsmax h) CAP) with (fh_bsmax h) in L by lia.
          eapply L; try eassumption; try lia.
        * zstep. pose proof (dl_hdr_raw2 mp hufv lev ws dtb) as L. replace (Z.min (fh_bsmax h) CAP) with CAP in L by lia.
          eapply L; try eassumption; try lia.
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
