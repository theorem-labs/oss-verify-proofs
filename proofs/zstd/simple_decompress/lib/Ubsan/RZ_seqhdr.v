(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit ZdTbl ZdDctxRep SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_blk_iface RZ_blk_iface2 RZ_blk_iface3 RZ_tbl RZ_imgfacts RZ_bst_stk seqH_kit seqH_kit_seq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_hide segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_hide segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_hide segs m m' MU WM.

(* [comment removed for export] *)
Definition PLL_BASE : Z := 0x10798.  Definition PLL_BITS : Z := 0x10828.
Definition POF_BASE : Z := 0x10a54.  Definition POF_BITS : Z := 0x10ad4.
Definition PML_BASE : Z := 0x10bfc.  Definition PML_BITS : Z := 0x10cd0.

Lemma pll_base_at : forall m, mem_inv usegs m -> bytes_at usegs m PLL_BASE (u32s (map (Z_to_bv 64) (kind_base K_LL))).
Proof. intros m INV. refine (img_bytes_at m PLL_BASE _ INV _ _ _); vm_compute; [reflexivity | discriminate | discriminate]. Qed.
Lemma pll_bits_at : forall m, mem_inv usegs m -> bytes_at usegs m PLL_BITS (map (Z_to_bv 8) (kind_bits K_LL)).
Proof. intros m INV. refine (img_bytes_at m PLL_BITS _ INV _ _ _); vm_compute; [reflexivity | discriminate | discriminate]. Qed.
Lemma pof_base_at : forall m, mem_inv usegs m -> bytes_at usegs m POF_BASE (u32s (map (Z_to_bv 64) (kind_base K_OF))).
Proof. intros m INV. refine (img_bytes_at m POF_BASE _ INV _ _ _); vm_compute; [reflexivity | discriminate | discriminate]. Qed.
Lemma pof_bits_at : forall m, mem_inv usegs m -> bytes_at usegs m POF_BITS (map (Z_to_bv 8) (kind_bits K_OF)).
Proof. intros m INV. refine (img_bytes_at m POF_BITS _ INV _ _ _); vm_compute; [reflexivity | discriminate | discriminate]. Qed.
Lemma pml_base_at : forall m, mem_inv usegs m -> bytes_at usegs m PML_BASE (u32s (map (Z_to_bv 64) (kind_base K_ML))).
Proof. intros m INV. refine (img_bytes_at m PML_BASE _ INV _ _ _); vm_compute; [reflexivity | discriminate | discriminate]. Qed.
Lemma pml_bits_at : forall m, mem_inv usegs m -> bytes_at usegs m PML_BITS (map (Z_to_bv 8) (kind_bits K_ML)).
Proof. intros m INV. refine (img_bytes_at m PML_BITS _ INV _ _ _); vm_compute; [reflexivity | discriminate | discriminate]. Qed.

(* [comment removed for export] *)
Definition tab_info (DCTX : Z) (k : seq_kind) (own dflt : Z) (d : seq_table) (pv : word) (T : Z) (bs : list byte) : Prop :=
  exists t, pv = Z_to_bv 64 T /\ bs = map (Z_to_bv 8) (seq_table_bytes t) /\ seq_table_ok k t /\ tbl_ptr DCTX own dflt d T t.

Lemma tab_info_tab : forall m DCTX k own dflt d pv T bs,
  tab_info DCTX k own dflt d pv T bs -> bytes_at usegs m T bs -> seqhdr_tab m DCTX k own dflt d pv.
Proof.
  intros m DCTX k own dflt d pv T bs INFO HERE.
  destruct INFO as (t & PVT & BSE & TOK & PTR). rewrite BSE in HERE.
  exists T, t. exact (conj PVT (conj PTR (conj HERE TOK))).
Qed.

Lemma tab_info_len : forall DCTX k own dflt d pv T bs, tab_info DCTX k own dflt d pv T bs -> Z.of_nat (length bs) <= TSZ k.
Proof. intros DCTX k own dflt d pv T bs (t & _ & -> & OK & _). pose proof (seq_tbl_len_le k t OK). lia. Qed.

Lemma tab_after_call : forall (m m' : fmem) W DCTX k own dflt d (oldp pv frw : word) (ty : Z) T0 bs0,
  bytes_at usegs m T0 bs0 -> Z.of_nat (length bs0) <= TSZ k ->
  (frw <> Z_to_bv 64 0 -> tab_info DCTX k own dflt d oldp T0 bs0) ->
  (T0 = DCTX + own \/ disjoint_from W T0 (Z.of_nat (length bs0))) ->
  (forall A bs, bytes_at usegs m A bs -> disjoint_from W A (Z.of_nat (length bs)) -> bytes_at usegs m' A bs) ->
  seq_tbl_at usegs m' k dflt d ->
  ((ty = 0 /\ pv = Z_to_bv 64 dflt)
   \/ (ty = 3 /\ frw <> Z_to_bv 64 0 /\ pv = oldp /\
       forall bs, bytes_at usegs m (DCTX + own) bs -> Z.of_nat (length bs) <= TSZ k -> bytes_at usegs m' (DCTX + own) bs)
   \/ ((ty = 1 \/ ty = 2) /\ pv = Z_to_bv 64 (DCTX + own) /\
       exists t, seq_table_ok k t /\ bytes_at usegs m' (DCTX + own) (map (Z_to_bv 8) (seq_table_bytes t)))) ->
  exists T bs, tab_info DCTX k own dflt d pv T bs /\ bytes_at usegs m' T bs.
Proof.
  intros m m' W DCTX k own dflt d oldp pv frw ty T0 bs0 OLDAT OLDLEN OLDINFO OLDPLACE KEEP DFLT RESULT.
  destruct RESULT as [[_ ->] | [[_ [LIVE [-> OWNKEEP]]] | [_ [-> [t [TOK NEWAT]]]]]].
  - destruct DFLT as [DAT DOK].
    exists dflt, (map (Z_to_bv 8) (seq_table_bytes d)). split; [|exact DAT].
    exists d. refine (conj eq_refl (conj eq_refl (conj DOK (or_intror (conj eq_refl eq_refl))))).
  - exists T0, bs0. split; [exact (OLDINFO LIVE)|].
    destruct OLDPLACE as [OWNSPOT | APART].
    + subst T0. exact (OWNKEEP bs0 OLDAT OLDLEN).
    + exact (KEEP T0 bs0 OLDAT APART).
  - exists (DCTX + own), (map (Z_to_bv 8) (seq_table_bytes t)). split; [|exact NEWAT].
    exists t. refine (conj eq_refl (conj eq_refl (conj TOK (or_introl eq_refl)))).
Qed.

(* [comment removed for export] *)
Lemma tab_info_geo : forall DCTX k own dflt d pv T bs lo SPV,
  tab_info DCTX k own dflt d pv T bs ->
  0x10000 <= dflt -> dflt + TSZ k <= 0x36000 -> 32 <= own -> own + TSZ k <= 10296 ->
  (DCTX + 30372 <= 0x10000 \/ 0x36000 <= DCTX) -> (SPV <= 0x10000 \/ 0x36000 <= lo) -> (DCTX + 95992 <= lo \/ SPV <= DCTX) ->
  (T = DCTX + own \/ (T + TSZ k <= DCTX \/ DCTX + 30372 <= T)) /\ (T + TSZ k <= lo \/ SPV <= T).
Proof.
  intros DCTX k own dflt d pv T bs lo SPV INFO DLO DHI OLO OHI IMGD IMGS OFFD.
  destruct INFO as (t & _ & _ & _ & [OWNSPOT | [DFLTSPOT _]]); subst T; split; lia.
Qed.

Lemma tab_info_rng : forall (frw pv : word) DCTX k own dflt d T bs,
  (frw <> Z_to_bv 64 0 -> tab_info DCTX k own dflt d pv T bs) ->
  4096 <= dflt < 2^46 -> 4096 <= DCTX -> DCTX + own < 2^47 -> 0 <= own ->
  frw <> Z_to_bv 64 0 -> 4096 <= bv_unsigned pv < 2^47.
Proof.
  intros frw pv DCTX k own dflt d T bs TI D0 C0 C1 O0 NZ.
  destruct (TI NZ) as (t & -> & _ & _ & [-> | [-> _]]); rewrite unsigned_lit by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma h5_cold_cell : forall m DCTX ws, dctx_h5 usegs m DCTX ws -> rw_cells usegs m (DCTX + 30204) [C4 (wnth ws H5_ddictIsCold)].
Proof.
  intros m DCTX ws [CELLS COUNT].
  h5_open ws COUNT.
  match type of CELLS with rw_cells _ _ _ ?cs => rewrite <- (firstn_skipn 17 cs) in CELLS end.
  apply rw_cells_app in CELLS as [_ TAIL].
  match type of TAIL with rw_cells _ _ _ ?cs => rewrite <- (firstn_skipn 1 cs) in TAIL end.
  apply rw_cells_app in TAIL as [ONE _].
  cbn [firstn skipn cells_size csize Nat.add] in ONE.
  replace (DCTX + 30096 + Z.of_nat 108) with (DCTX + 30204) in ONE by lia.
  exact ONE.
Qed.

(* [comment removed for export] *)
Definition sh_hyps (SPV lo DCTX NBP SRC slen : Z) : Prop :=
  4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= NBP /\ NBP + 4 < 2^47 /\
  slen <= 1048576 /\ 4096 <= SRC /\ SRC + slen < 2^47 /\
  4096 <= lo /\ lo <= SPV - 544 /\ SPV < 2^47 /\
  (DCTX + 95992 <= lo \/ SPV <= DCTX) /\ (NBP + 4 <= lo \/ SPV <= NBP) /\ (SRC + slen <= lo \/ SPV <= SRC) /\
  (DCTX + 95992 <= NBP \/ NBP + 4 <= DCTX) /\ (DCTX + 95992 <= SRC \/ SRC + slen <= DCTX) /\ (NBP + 4 <= SRC \/ SRC + slen <= NBP) /\
  (DCTX + 30372 <= 65536 \/ 221184 <= DCTX) /\ (SPV <= 65536 \/ 221184 <= lo).
Ltac open_shh HY := pose proof HY as (DCL & DCH & NBL & NBH & SLEN & SRCL & SRCH & LO0 & LOS & SPH & OFFD & OFFNB & OFFSRC & DNB & DSRC & NBSRC & IMGD & IMGS);
                    hide_all_disj.

Section SH.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DCTX NBP SRC : Z) (src : list Z) (llt mlt oft huf pcs dsz bt stg le fe cold : word).
  Hypothesis HY : sh_hyps SPV lo DCTX NBP SRC (Z.of_nat (length src)).
  Hypothesis FBY : Forall (fun c => 0 <= c < 256) src.
  Hypothesis ALD : DCTX mod 8 = 0.
  Hypothesis ALN : NBP mod 4 = 0.
  Hypothesis ALS : SPV mod 16 = 0.
  Notation POST := (zd_seqhdr_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX NBP (Z.of_nat (length src)) llt mlt oft huf lo m).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -96)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FOOT := [(DCTX, DCTX + 24); (DCTX + 32, DCTX + 10296); (DCTX + 27324, DCTX + 29884); (NBP, NBP + 4); (SPV - 544, SPV)].

  (* [comment removed for export] *)
  Definition SHB (p0 p1 p2 nbw : word) (m1 : fmem) : Prop :=
    rw_cells usegs m1 DCTX [C8 p0] /\ rw_cells usegs m1 (DCTX + 8) [C8 p1] /\ rw_cells usegs m1 (DCTX + 16) [C8 p2] /\
    rw_cells usegs m1 (DCTX + 24) [C8 huf] /\
    stk usegs m1 (DCTX + 32) (DCTX + 4136) /\ stk usegs m1 (DCTX + 4136) (DCTX + 6192) /\
    stk usegs m1 (DCTX + 6192) (DCTX + 10296) /\ stk usegs m1 (DCTX + 27324) (DCTX + 29884) /\
    rw_cells usegs m1 (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 fe] /\
    rw_cells usegs m1 (DCTX + 30204) [C4 cold] /\
    rw_cells usegs m1 NBP [C4 nbw] /\
    bytes_at usegs m1 SRC (map (Z_to_bv 8) src) /\
    stk usegs m1 lo (SPV + -96) /\
    (exists fa, rw_cells usegs m1 (SPV + -96) [CB 24 fa; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
    mem_inv usegs m1 /\ munch FOOT m m1 /\ wmono usegs m m1.
  Ltac open_shb I := destruct I as (P0 & P1 & P2 & P3 & ELL & EOF & EML & EWK & H3 & COLD & NB & SRCB & STK & (fa & FR) & MI & MU & WM).

  (* [comment removed for export] *)
  Lemma sh_ret : forall m1 p0 p1 p2 nbw r xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31,
    SHB p0 p1 p2 nbw m1 -> 0 <= r < 2^64 -> xa4 = Z_to_bv 64 r ->
    (zd_is_error r = true
     \/ (r <= Z.of_nat (length src) /\ exists nbSeq, nbw = Z_to_bv 64 nbSeq /\ 0 <= nbSeq <= 98047 /\
        ((nbSeq = 0 /\ p0 = llt /\ p1 = mlt /\ p2 = oft /\ munch [(NBP, NBP + 4); (SPV - 544, SPV)] m m1)
          \/ (nbSeq <> 0 /\
              seqhdr_tab m1 DCTX K_LL DCTX_entropy_LLTable PZD_LL_DEFAULT LL_defaultDTable p0 /\
              seqhdr_tab m1 DCTX K_OF DCTX_entropy_OFTable PZD_OF_DEFAULT OF_defaultDTable p2 /\
              seqhdr_tab m1 DCTX K_ML DCTX_entropy_MLTable PZD_ML_DEFAULT ML_defaultDTable p1)))) ->
    evt usegs POST (ST 0x1753c m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 s8 x28 x29 x30 x31).
  Proof.
    intros m1 p0 p1 p2 nbw r xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31
           BODY RRANGE A4 RESULT.
    clear FBY ALD ALN ALS.
    open_shh HY. open_shb BODY. subst xa4.
    do 12 zstep.
    release_frame FR STK SPV.
    assert (PTRS : rw_cells usegs m1 DCTX [C8 p0; C8 p1; C8 p2; C8 huf]).
    { assert (HI : rw_cells usegs m1 (DCTX + 16) ([C8 p2] ++ [C8 huf])).
      { apply rw_cells_app. split; [exact P2|]. cbn [cells_size csize Nat.add]. replace (DCTX + 16 + Z.of_nat 8) with (DCTX + 24) by lia. exact P3. }
      assert (MID : rw_cells usegs m1 (DCTX + 8) ([C8 p1] ++ [C8 p2; C8 huf])).
      { apply rw_cells_app. split; [exact P1|]. cbn [cells_size csize Nat.add]. replace (DCTX + 8 + Z.of_nat 8) with (DCTX + 16) by lia. exact HI. }
      change [C8 p0; C8 p1; C8 p2; C8 huf] with ([C8 p0] ++ [C8 p1; C8 p2; C8 huf]).
      apply rw_cells_app. split; [exact P0|]. cbn [cells_size csize Nat.add]. replace (DCTX + Z.of_nat 8) with (DCTX + 8) by lia. exact MID. }
    assert (TABLES : stk usegs m1 (DCTX + 32) (DCTX + 10296)).
    { apply (stk_merge usegs m1 _ (DCTX + 6192)); [apply (stk_merge usegs m1 _ (DCTX + 4136)); [exact ELL | exact EOF | lia] | exact EML | lia]. }
    unfold hidden in RESULT.
    apply evt_done. unfold zd_seqhdr_post.
    do 14 eexists. exists m1, r, p0, p1, p2, nbw.
    split; [reflexivity|].
    refine (conj MU (conj WM (conj MI (conj STK (conj PTRS (conj TABLES (conj EWK (conj NB (conj RRANGE RESULT))))))))).
  Qed.

  Lemma bytes_at_skipn_src : forall m1 i, bytes_at usegs m1 SRC (map (Z_to_bv 8) src) -> 0 <= i <= Z.of_nat (length src) ->
    bytes_at usegs m1 (SRC + i) (map (Z_to_bv 8) (skipn (Z.to_nat i) src)).
  Proof.
    intros m1 i WHOLE RANGE.
    rewrite <- (firstn_skipn (Z.to_nat i) src), map_app in WHOLE.
    apply bytes_at_app in WHOLE as [_ TAIL].
    rewrite length_map, length_firstn in TAIL.
    replace (SRC + Z.of_nat (Nat.min (Z.to_nat i) (length src))) with (SRC + i) in TAIL by mlia.
    exact TAIL.
  Qed.

  (* [comment removed for export] *)
  Lemma sh_frame : forall m1 a b x,
    rw_cells usegs m1 (SPV + -96) [C8 a; C8 b] ->
    rw_cells usegs m1 (SPV + -80) [CB 8 x; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    exists fa, rw_cells usegs m1 (SPV + -96) [CB 24 fa; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Proof.
    intros m1 a b x ARGS SAVED.
    assert (JOIN : rw_cells usegs m1 (SPV + -96)
                     ([C8 a; C8 b] ++ [CB 8 x; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply rw_cells_app. split; [exact ARGS|].
      cbn [cells_size csize Nat.add]. replace (SPV + -96 + Z.of_nat 16) with (SPV + -80) by mlia. exact SAVED. }
    pose proof (rw_cells_merge usegs m1 (SPV + -96) [] [C8 a; C8 b; CB 8 x]
                  [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) as MERGE.
    cbn [app cells_size csize Nat.add] in MERGE, JOIN.
    eexists. exact (MERGE JOIN).
  Qed.

  (* [comment removed for export] *)
  Lemma sh_ml : forall m1 p0 p1 p2 nbSeq i2 r2 tb T0 bs0 T2 bs2 TM bsM xra x5 x6 x7 xs1v xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31,
    SHB p0 p1 p2 (Z_to_bv 64 nbSeq) m1 ->
    1 <= nbSeq <= 98047 -> 0 <= tb < 256 -> 0 <= i2 -> 0 <= r2 -> i2 + r2 <= Z.of_nat (length src) ->
    tab_info DCTX K_LL 32 PZD_LL_DEFAULT LL_defaultDTable p0 T0 bs0 -> bytes_at usegs m1 T0 bs0 ->
    tab_info DCTX K_OF 4136 PZD_OF_DEFAULT OF_defaultDTable p2 T2 bs2 -> bytes_at usegs m1 T2 bs2 ->
    bytes_at usegs m1 TM bsM -> Z.of_nat (length bsM) <= 4104 ->
    (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_ML 6192 PZD_ML_DEFAULT ML_defaultDTable p1 TM bsM) ->
    (TM = DCTX + 6192 \/ (TM + 4104 <= DCTX \/ DCTX + 30372 <= TM)) -> (TM + 4104 <= lo \/ SPV <= TM) ->
    xs1v = Z_to_bv 64 nbSeq ->
    evt usegs POST (ST 0x17478 m1 xra x5 x6 x7 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + Z.of_nat (length src))) (Z_to_bv 64 r2) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       xs1v (Z_to_bv 64 SRC) (Z_to_bv 64 (DCTX + 27324)) (Z_to_bv 64 tb)
                       (Z_to_bv 64 (DCTX + 30004)) (Z_to_bv 64 DCTX) s8 x28 x29 x30 x31).
  Proof.
    intros m1 p0 p1 p2 nbSeq i2 r2 tb T0 bs0 T2 bs2 TM bsM xra x5 x6 x7 xs1v xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31
           BODY NBR TBR I2P R2P IRS LLI LLAT OFI OFAT MLAT MLLEN MLOLD MLWHERE MLSTK NBV.
    subst xs1v. open_shh HY. open_shb BODY.
    (* where the two built tables sit, so that stores and the call keep them *)
    pose proof (tab_info_len _ _ _ _ _ _ _ _ LLI) as LLLEN. pose proof (tab_info_len _ _ _ _ _ _ _ _ OFI) as OFLEN.
    change (TSZ K_LL) with 4104 in LLLEN. change (TSZ K_OF) with 2056 in OFLEN.
    assert (LLG : (T0 = DCTX + 32 \/ T0 + 4104 <= DCTX \/ DCTX + 30372 <= T0) /\ (T0 + 4104 <= lo \/ SPV <= T0)).
    { refine (tab_info_geo _ _ _ _ _ _ _ _ lo SPV LLI _ _ _ _ IMGD IMGS OFFD); unfold PZD_LL_DEFAULT; cbn; lia. }
    assert (OFG : (T2 = DCTX + 4136 \/ T2 + 2056 <= DCTX \/ DCTX + 30372 <= T2) /\ (T2 + 2056 <= lo \/ SPV <= T2)).
    { refine (tab_info_geo _ _ _ _ _ _ _ _ lo SPV OFI _ _ _ _ IMGD IMGS OFFD); unfold PZD_OF_DEFAULT; cbn; lia. }
    destruct LLG as [LLWHERE LLSTK]. destruct OFG as [OFWHERE OFSTK]. hide_all_disj.
    (* the ip + r2 overflow check never fires *)
    zstep. zstep. if_cases OVF; zify_cond OVF.
    { rewrite lxor_ones64 in OVF by lia. exfalso. lia. }
    clear OVF.
    do 22 zstep.
    (* the two outgoing argument slots, apart from the saved registers *)
    match type of FR with rw_cells _ _ _ ?cs => rewrite <- (firstn_skipn 2 cs) in FR end.
    apply rw_cells_app in FR as [ARGS SAVED].
    cbn [firstn skipn cells_size csize Nat.add] in ARGS, SAVED.
    replace (SPV + -96 + Z.of_nat 16) with (SPV + -80) in SAVED by lia.
    (* the old ML table, kept out of reach of the transport *)
    pose proof MLAT as MLAT0. hide MLAT0. clear MLAT.
    pose proof FBY as SUFFIX. rewrite <- (firstn_skipn (Z.to_nat (i2 + r2)) src) in SUFFIX.
    apply Forall_app in SUFFIX as [_ SUFFIX].
    pose proof (bytes_at_skipn_src m1 (i2 + r2) SRCB ltac:(lia)) as TAILB. rewrite Z.add_assoc in TAILB.
    lazymatch goal with |- context [Z_to_bv 64 (Z.shiftr ?e 62)] => set (ty := Z.shiftr e 62) end.
    eapply evt_cut.
    { apply (zd_buildseq_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (SPV + -96) lo (DCTX + 6192) (DCTX + 8)
               (SRC + i2 + r2) (DCTX + 27324) PZD_ML_DEFAULT PML_BASE PML_BITS ty 2560 K_ML (skipn (Z.to_nat (i2 + r2)) src)
               p1 (Z_to_bv 64 nbSeq)).
      all: try change (8 + 8 * 2 ^ kind_maxLog K_ML) with 4104.
      all: lazymatch goal with
           | |- stk _ _ (DCTX + 6192) _ => replace (DCTX + 6192 + 4104) with (DCTX + 10296) by lia; exact EML
           | |- stk _ _ (DCTX + 27324) _ => replace (DCTX + 27324 + 2560) with (DCTX + 29884) by lia; exact EWK
           | |- stk _ _ lo _ => exact STK
           | |- rw_cells _ _ (DCTX + 8) _ => exact P1
           | |- rw_cells _ _ (SPV + -96) _ => exact ARGS
           | |- bytes_at _ _ PML_BASE _ => exact (pml_base_at m1 MI)
           | |- bytes_at _ _ PML_BITS _ => exact (pml_bits_at m1 MI)
           | |- bytes_at _ _ _ _ => exact TAILB
           | |- Forall _ _ => exact SUFFIX
           | |- mem_inv _ _ => exact MI
           | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; rewrite length_skipn; lia]
           | |- sx32 fe <> _ -> _ =>
               intro LIVE; refine (tab_info_rng (sx32 fe) p1 DCTX K_ML 6192 PZD_ML_DEFAULT ML_defaultDTable TM bsM MLOLD _ DCL _ _ LIVE);
               unfold PZD_ML_DEFAULT; lia
           | |- 0 <= _ <= 3 =>
               subst ty; rewrite Z.shiftr_div_pow2 by lia; change (2^62) with 4611686018427387904; mlia
           | |- off_stack _ _ _ _ =>
               rewrite ?length_skipn; unfold off_stack, PML_BASE, PML_BITS; unfold hidden in OFFD, OFFSRC, IMGS; lia
           | |- apart _ _ _ _ =>
               rewrite ?length_skipn; unfold apart, PML_BASE, PML_BITS; unfold hidden in OFFD, DSRC, OFFSRC, IMGD; lia
           | |- _ => rewrite ?length_skipn; unfold PML_BASE, PML_BITS; mlia
           end. }
    intros ms' PO. unfold zd_buildseq_stk_post in PO.
    change (8 + 8 * 2 ^ kind_maxLog K_ML) with 4104 in PO.
    revert ms' PO. post_call usegs m1.
    rename x16 into m2, x17 into rML, x18 into pML.
    rename PC into STK2, PC0 into EML2, PC1 into EWK2, PC2 into P1N, PC3 into KEEP, PC4 into RML, POST into RES, MI0 into MI2.
    (* the frame and the whole block hold again in the new memory *)
    destruct (sh_frame m2 _ _ _ ARGS SAVED) as [fa2 FR2].
    replace (DCTX + 6192 + 4104) with (DCTX + 10296) in EML2 by lia.
    replace (DCTX + 27324 + 2560) with (DCTX + 29884) in EWK2 by lia.
    assert (BODY2 : SHB p0 pML p2 (Z_to_bv 64 nbSeq) m2).
    { unfold SHB. repeat (split; [eassumption|]).
      split; [exists fa2; exact FR2|]. split; [exact MI2|]. exact (conj MU WM). }
    zstep. zstep. zstep. if_cases BAD; zify_cond BAD.
    - apply (sh_ret m2 p0 pML p2 (Z_to_bv 64 nbSeq) (2^64 - 20)); [exact BODY2 | lia | apply Z_to_bv_eqm; reflexivity |].
      left. reflexivity.
    - destruct RES as [ERR | [RLEN RCASES]].
      { exfalso. unfold zd_is_error, ZE_maxCode in ERR. apply Z.ltb_lt in ERR. lia. }
      rewrite length_skipn in RLEN.
      unfold hidden in MLAT0.
      assert (MLPLACE : TM = DCTX + 6192 \/
                        disjoint_from [(DCTX + 6192, DCTX + 6192 + 4104); (DCTX + 8, DCTX + 8 + 8);
                                       (DCTX + 27324, DCTX + 27324 + 2560); (SPV + -96 - 448, SPV + -96)]
                                      TM (Z.of_nat (length bsM))).
      { unfold hidden in MLWHERE, MLSTK.
        destruct MLWHERE as [MLOWN | MLAWAY]; [left; exact MLOWN | right; cbn [disjoint_from]; lia]. }
      destruct (tab_after_call m1 m2 _ DCTX K_ML 6192 PZD_ML_DEFAULT ML_defaultDTable p1 pML (sx32 fe) ty TM bsM
                  MLAT0 MLLEN MLOLD MLPLACE KEEP (conj (pml_default_at m2 MI2) ML_default_ok) RCASES)
        as (TN & bsN & MLI & MLAT2).
      zstep. zstep. if_cases OVF2; zify_cond OVF2.
      { rewrite lxor_ones64 in OVF2 by lia. exfalso. lia. }
      clear OVF2.
      do 3 zstep.
      apply (sh_ret m2 p0 pML p2 (Z_to_bv 64 nbSeq) (i2 + r2 + rML)); [exact BODY2 | lia | f_equal; lia |].
      right. split; [lia|]. exists nbSeq. split; [reflexivity|]. split; [lia|]. right.
      split; [lia|]. split; [exact (tab_info_tab _ _ _ _ _ _ _ _ _ LLI LLAT)|].
      split; [exact (tab_info_tab _ _ _ _ _ _ _ _ _ OFI OFAT)|]. exact (tab_info_tab _ _ _ _ _ _ _ _ _ MLI MLAT2).
  Qed.

  (* [comment removed for export] *)
  Lemma sh_of : forall m1 p0 p1 p2 nbSeq i1 r1 tb T0 bs0 TO bsO TM bsM xra x5 x6 x7 xs1v xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31,
    SHB p0 p1 p2 (Z_to_bv 64 nbSeq) m1 ->
    1 <= nbSeq <= 98047 -> 0 <= tb < 256 -> 0 <= i1 -> 0 <= r1 -> i1 + r1 <= Z.of_nat (length src) ->
    tab_info DCTX K_LL 32 PZD_LL_DEFAULT LL_defaultDTable p0 T0 bs0 -> bytes_at usegs m1 T0 bs0 ->
    bytes_at usegs m1 TO bsO -> Z.of_nat (length bsO) <= 2056 ->
    (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_OF 4136 PZD_OF_DEFAULT OF_defaultDTable p2 TO bsO) ->
    (TO = DCTX + 4136 \/ (TO + 2056 <= DCTX \/ DCTX + 30372 <= TO)) -> (TO + 2056 <= lo \/ SPV <= TO) ->
    bytes_at usegs m1 TM bsM -> Z.of_nat (length bsM) <= 4104 ->
    (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_ML 6192 PZD_ML_DEFAULT ML_defaultDTable p1 TM bsM) ->
    (TM = DCTX + 6192 \/ (TM + 4104 <= DCTX \/ DCTX + 30372 <= TM)) -> (TM + 4104 <= lo \/ SPV <= TM) ->
    xs1v = Z_to_bv 64 nbSeq ->
    evt usegs POST (ST 0x17410 m1 xra x5 x6 x7 (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + Z.of_nat (length src))) (Z_to_bv 64 r1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       xs1v (Z_to_bv 64 SRC) (Z_to_bv 64 (DCTX + 27324)) (Z_to_bv 64 tb)
                       (Z_to_bv 64 (DCTX + 30004)) (Z_to_bv 64 DCTX) s8 x28 x29 x30 x31).
  Proof.
    intros m1 p0 p1 p2 nbSeq i1 r1 tb T0 bs0 TO bsO TM bsM xra x5 x6 x7 xs1v xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31
           BODY NBR TBR I1P R1P IRS LLI LLAT OFAT OFLEN OFOLD OFWHERE OFSTK MLAT MLLEN MLOLD MLWHERE MLSTK NBV.
    subst xs1v. open_shh HY. open_shb BODY.
    (* the LL table built just before stays where it was put *)
    pose proof (tab_info_len _ _ _ _ _ _ _ _ LLI) as LLLEN. change (TSZ K_LL) with 4104 in LLLEN.
    assert (LLG : (T0 = DCTX + 32 \/ T0 + 4104 <= DCTX \/ DCTX + 30372 <= T0) /\ (T0 + 4104 <= lo \/ SPV <= T0)).
    { refine (tab_info_geo _ _ _ _ _ _ _ _ lo SPV LLI _ _ _ _ IMGD IMGS OFFD); unfold PZD_LL_DEFAULT; cbn; lia. }
    destruct LLG as [LLWHERE LLSTK]. hide_all_disj.
    (* ip + r1 does not wrap *)
    zstep. zstep. if_cases WRAP; zify_cond WRAP.
    { rewrite lxor_ones64 in WRAP by lia. exfalso. lia. }
    clear WRAP.
    do 22 zstep.
    pose proof (bytes_at_skipn_src m1 (i1 + r1) SRCB ltac:(lia)) as TAILB. rewrite Z.add_assoc in TAILB.
    pose proof FBY as SUFFIX. rewrite <- (firstn_skipn (Z.to_nat (i1 + r1)) src) in SUFFIX.
    apply Forall_app in SUFFIX as [_ SUFFIX].
    pose proof OFAT as OFAT0. hide OFAT0. clear OFAT.
    match type of FR with rw_cells _ _ _ ?cs => rewrite <- (firstn_skipn 2 cs) in FR end.
    apply rw_cells_app in FR as [ARGS SAVED].
    cbn [firstn skipn cells_size csize Nat.add] in ARGS, SAVED.
    replace (SPV + -96 + Z.of_nat 16) with (SPV + -80) in SAVED by lia.
    lazymatch goal with |- context [Z_to_bv 64 (Z.shiftr ?e 62)] => set (ty := Z.shiftr e 62) end.
    eapply evt_cut.
    { apply (zd_buildseq_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (SPV + -96) lo (DCTX + 4136) (DCTX + 16)
               (SRC + i1 + r1) (DCTX + 27324) PZD_OF_DEFAULT POF_BASE POF_BITS ty 2560 K_OF (skipn (Z.to_nat (i1 + r1)) src)
               p2 (Z_to_bv 64 nbSeq)).
      all: try change (8 + 8 * 2 ^ kind_maxLog K_OF) with 2056.
      all: lazymatch goal with
           | |- stk _ _ (DCTX + 4136) _ => replace (DCTX + 4136 + 2056) with (DCTX + 6192) by lia; exact EOF
           | |- stk _ _ (DCTX + 27324) _ => replace (DCTX + 27324 + 2560) with (DCTX + 29884) by lia; exact EWK
           | |- stk _ _ lo _ => exact STK
           | |- rw_cells _ _ (DCTX + 16) _ => exact P2
           | |- rw_cells _ _ (SPV + -96) _ => exact ARGS
           | |- bytes_at _ _ POF_BASE _ => exact (pof_base_at m1 MI)
           | |- bytes_at _ _ POF_BITS _ => exact (pof_bits_at m1 MI)
           | |- bytes_at _ _ _ _ => exact TAILB
           | |- Forall _ _ => exact SUFFIX
           | |- mem_inv _ _ => exact MI
           | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; rewrite length_skipn; lia]
           | |- sx32 fe <> _ -> _ =>
               intro LIVE; refine (tab_info_rng (sx32 fe) p2 DCTX K_OF 4136 PZD_OF_DEFAULT OF_defaultDTable TO bsO OFOLD _ DCL _ _ LIVE);
               unfold PZD_OF_DEFAULT; lia
           | |- 0 <= _ <= 3 =>
               subst ty; rewrite Z.shiftr_div_pow2 by lia; change (2^62) with 4611686018427387904; mlia
           | |- off_stack _ _ _ _ =>
               rewrite ?length_skipn; unfold off_stack, POF_BASE, POF_BITS; unfold hidden in OFFD, OFFSRC, IMGS; lia
           | |- apart _ _ _ _ =>
               rewrite ?length_skipn; unfold apart, POF_BASE, POF_BITS; unfold hidden in OFFD, DSRC, OFFSRC, IMGD; lia
           | |- _ => rewrite ?length_skipn; unfold POF_BASE, POF_BITS; mlia
           end. }
    intros ms' PO. unfold zd_buildseq_stk_post in PO.
    change (8 + 8 * 2 ^ kind_maxLog K_OF) with 2056 in PO.
    revert ms' PO. post_call usegs m1.
    rename x16 into m2, x17 into rOF, x18 into pOF.
    rename PC into STK2, PC0 into EOF2, PC1 into EWK2, PC2 into P2N, PC3 into KEEP, PC4 into ROF, POST into RES, MI0 into MI2.
    destruct (sh_frame m2 _ _ _ ARGS SAVED) as [fa2 FR2].
    replace (DCTX + 4136 + 2056) with (DCTX + 6192) in EOF2 by lia.
    replace (DCTX + 27324 + 2560) with (DCTX + 29884) in EWK2 by lia.
    assert (BODY2 : SHB p0 p1 pOF (Z_to_bv 64 nbSeq) m2).
    { unfold SHB. repeat (split; [eassumption|]).
      split; [exists fa2; exact FR2|]. split; [exact MI2|]. exact (conj MU WM). }
    zstep. zstep. if_cases BAD; zify_cond BAD.
    - zstep. zstep.
      apply (sh_ret m2 p0 p1 pOF (Z_to_bv 64 nbSeq) (2^64 - 20)); [exact BODY2 | lia | apply Z_to_bv_eqm; reflexivity |].
      left. reflexivity.
    - destruct RES as [ERR | [RLEN RCASES]].
      { exfalso. unfold zd_is_error, ZE_maxCode in ERR. apply Z.ltb_lt in ERR. lia. }
      rewrite length_skipn in RLEN.
      unfold hidden in OFAT0.
      assert (OFPLACE : TO = DCTX + 4136 \/
                        disjoint_from [(DCTX + 4136, DCTX + 4136 + 2056); (DCTX + 16, DCTX + 16 + 8);
                                       (DCTX + 27324, DCTX + 27324 + 2560); (SPV + -96 - 448, SPV + -96)]
                                      TO (Z.of_nat (length bsO))).
      { unfold hidden in OFWHERE, OFSTK.
        destruct OFWHERE as [OFOWN | OFAWAY]; [left; exact OFOWN | right; cbn [disjoint_from]; lia]. }
      destruct (tab_after_call m1 m2 _ DCTX K_OF 4136 PZD_OF_DEFAULT OF_defaultDTable p2 pOF (sx32 fe) ty TO bsO
                  OFAT0 OFLEN OFOLD OFPLACE KEEP (conj (pof_default_at m2 MI2) OF_default_ok) RCASES)
        as (TN & bsN & OFI & OFAT2).
      replace (SRC + i1 + r1) with (SRC + (i1 + r1)) by lia.
      unfold hidden in MLWHERE, MLSTK.
      eapply (sh_ml m2 p0 p1 pOF nbSeq (i1 + r1) rOF tb T0 bs0 TN bsN TM bsM); try eassumption; try reflexivity; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sh_ll : forall m1 p0 p1 p2 nbSeq hl TL bsL TO bsO TM bsM xra x5 x6 x7 xs1v xa1 xa3 xa4 xa6 xa7 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31,
    SHB p0 p1 p2 (Z_to_bv 64 nbSeq) m1 ->
    1 <= nbSeq <= 98047 -> 1 <= hl -> hl + 1 <= Z.of_nat (length src) ->
    bytes_at usegs m1 TL bsL -> Z.of_nat (length bsL) <= 4104 ->
    (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_LL 32 PZD_LL_DEFAULT LL_defaultDTable p0 TL bsL) ->
    (TL = DCTX + 32 \/ (TL + 4104 <= DCTX \/ DCTX + 30372 <= TL)) -> (TL + 4104 <= lo \/ SPV <= TL) ->
    bytes_at usegs m1 TO bsO -> Z.of_nat (length bsO) <= 2056 ->
    (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_OF 4136 PZD_OF_DEFAULT OF_defaultDTable p2 TO bsO) ->
    (TO = DCTX + 4136 \/ (TO + 2056 <= DCTX \/ DCTX + 30372 <= TO)) -> (TO + 2056 <= lo \/ SPV <= TO) ->
    bytes_at usegs m1 TM bsM -> Z.of_nat (length bsM) <= 4104 ->
    (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_ML 6192 PZD_ML_DEFAULT ML_defaultDTable p1 TM bsM) ->
    (TM = DCTX + 6192 \/ (TM + 4104 <= DCTX \/ DCTX + 30372 <= TM)) -> (TM + 4104 <= lo \/ SPV <= TM) ->
    xs1v = Z_to_bv 64 nbSeq ->
    evt usegs POST (ST 0x17384 m1 xra x5 x6 x7 (Z_to_bv 64 (SRC + hl + 1)) (Z_to_bv 64 (SRC + Z.of_nat (length src))) (Z_to_bv 64 DCTX) xa1 (Z_to_bv 64 SRC) xa3 xa4 (Z_to_bv 64 (SRC + hl)) xa6 xa7
                       xs1v xs3 xs4 xs5 xs6 xs7 s8 x28 x29 x30 x31).
  Proof.
    intros m1 p0 p1 p2 nbSeq hl TL bsL TO bsO TM bsM xra x5 x6 x7 xs1v xa1 xa3 xa4 xa6 xa7 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31
           BODY NBR HL1 HLN LLAT LLLEN LLOLD LLWHERE LLSTK OFAT OFLEN OFOLD OFWHERE OFSTK MLAT MLLEN MLOLD MLWHERE MLSTK NBV.
    subst xs1v. open_shh HY. pose proof BODY as PARTS. open_shb PARTS. hide_all_disj.
    (* the type byte that follows the sequence count *)
    assert (TBYTE : 0 <= Znth hl src < 256).
    { pose proof FBY as ALLB. rewrite Forall_forall in ALLB. apply ALLB. unfold Znth. apply nth_In. lia. }
    zlb SRCB FBY hl.
    zstep. zstep. zstep. if_cases RSV; zify_cond RSV.
    { apply (sh_ret m1 p0 p1 p2 (Z_to_bv 64 nbSeq) (2^64 - 20)); [exact BODY | lia | apply Z_to_bv_eqm; reflexivity |].
      left. reflexivity. }
    clear BODY RSV.
    (* the dctx pointer is neither null nor misaligned *)
    zstep. uck. zstep. zstep. uck.
    do 26 zstep.
    pose proof (bytes_at_skipn_src m1 (hl + 1) SRCB ltac:(lia)) as TAILB. rewrite Z.add_assoc in TAILB.
    pose proof FBY as SUFFIX. rewrite <- (firstn_skipn (Z.to_nat (hl + 1)) src) in SUFFIX.
    apply Forall_app in SUFFIX as [_ SUFFIX].
    pose proof LLAT as LLAT0. hide LLAT0. clear LLAT.
    match type of FR with rw_cells _ _ _ ?cs => rewrite <- (firstn_skipn 2 cs) in FR end.
    apply rw_cells_app in FR as [ARGS SAVED].
    cbn [firstn skipn cells_size csize Nat.add] in ARGS, SAVED.
    replace (SPV + -96 + Z.of_nat 16) with (SPV + -80) in SAVED by lia.
    lazymatch goal with |- context [Z_to_bv 64 (Z.shiftr ?e 6)] => set (ty := Z.shiftr e 6) end.
    eapply evt_cut.
    { apply (zd_buildseq_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (SPV + -96) lo (DCTX + 32) DCTX
               (SRC + hl + 1) (DCTX + 27324) PZD_LL_DEFAULT PLL_BASE PLL_BITS ty 2560 K_LL (skipn (Z.to_nat (hl + 1)) src)
               p0 (Z_to_bv 64 nbSeq)).
      all: try change (8 + 8 * 2 ^ kind_maxLog K_LL) with 4104.
      all: lazymatch goal with
           | |- stk _ _ (DCTX + 32) _ => replace (DCTX + 32 + 4104) with (DCTX + 4136) by lia; exact ELL
           | |- stk _ _ (DCTX + 27324) _ => replace (DCTX + 27324 + 2560) with (DCTX + 29884) by lia; exact EWK
           | |- stk _ _ lo _ => exact STK
           | |- rw_cells _ _ DCTX _ => exact P0
           | |- rw_cells _ _ (SPV + -96) _ => exact ARGS
           | |- bytes_at _ _ PLL_BASE _ => exact (pll_base_at m1 MI)
           | |- bytes_at _ _ PLL_BITS _ => exact (pll_bits_at m1 MI)
           | |- bytes_at _ _ _ _ => exact TAILB
           | |- Forall _ _ => exact SUFFIX
           | |- mem_inv _ _ => exact MI
           | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; rewrite length_skipn; lia]
           | |- sx32 fe <> _ -> _ =>
               intro LIVE; refine (tab_info_rng (sx32 fe) p0 DCTX K_LL 32 PZD_LL_DEFAULT LL_defaultDTable TL bsL LLOLD _ DCL _ _ LIVE);
               unfold PZD_LL_DEFAULT; lia
           | |- 0 <= _ <= 3 =>
               subst ty; rewrite Z.shiftr_div_pow2 by lia; change (2^6) with 64; mlia
           | |- off_stack _ _ _ _ =>
               rewrite ?length_skipn; unfold off_stack, PLL_BASE, PLL_BITS; unfold hidden in OFFD, OFFSRC, IMGS; lia
           | |- apart _ _ _ _ =>
               rewrite ?length_skipn; unfold apart, PLL_BASE, PLL_BITS; unfold hidden in OFFD, DSRC, OFFSRC, IMGD; lia
           | |- _ => rewrite ?length_skipn; unfold PLL_BASE, PLL_BITS; mlia
           end. }
    intros ms' PO. unfold zd_buildseq_stk_post in PO.
    change (8 + 8 * 2 ^ kind_maxLog K_LL) with 4104 in PO.
    revert ms' PO. post_call usegs m1.
    rename x16 into m2, x17 into rLL, x18 into pLL.
    rename PC into STK2, PC0 into ELL2, PC1 into EWK2, PC2 into P0N, PC3 into KEEP, PC4 into RLL, POST into RES, MI0 into MI2.
    destruct (sh_frame m2 _ _ _ ARGS SAVED) as [fa2 FR2].
    replace (DCTX + 32 + 4104) with (DCTX + 4136) in ELL2 by lia.
    replace (DCTX + 27324 + 2560) with (DCTX + 29884) in EWK2 by lia.
    assert (BODY2 : SHB pLL p1 p2 (Z_to_bv 64 nbSeq) m2).
    { unfold SHB. repeat (split; [eassumption|]).
      split; [exists fa2; exact FR2|]. split; [exact MI2|]. exact (conj MU WM). }
    zstep. zstep. if_cases BAD; zify_cond BAD.
    - zstep. zstep.
      apply (sh_ret m2 pLL p1 p2 (Z_to_bv 64 nbSeq) (2^64 - 20)); [exact BODY2 | lia | apply Z_to_bv_eqm; reflexivity |].
      left. reflexivity.
    - destruct RES as [ERR | [RLEN RCASES]].
      { exfalso. unfold zd_is_error, ZE_maxCode in ERR. apply Z.ltb_lt in ERR. lia. }
      rewrite length_skipn in RLEN.
      unfold hidden in LLAT0.
      assert (LLPLACE : TL = DCTX + 32 \/
                        disjoint_from [(DCTX + 32, DCTX + 32 + 4104); (DCTX, DCTX + 8);
                                       (DCTX + 27324, DCTX + 27324 + 2560); (SPV + -96 - 448, SPV + -96)]
                                      TL (Z.of_nat (length bsL))).
      { unfold hidden in LLWHERE, LLSTK.
        destruct LLWHERE as [LLOWN | LLAWAY]; [left; exact LLOWN | right; cbn [disjoint_from]; lia]. }
      destruct (tab_after_call m1 m2 _ DCTX K_LL 32 PZD_LL_DEFAULT LL_defaultDTable p0 pLL (sx32 fe) ty TL bsL
                  LLAT0 LLLEN LLOLD LLPLACE KEEP (conj (pll_default_at m2 MI2) LL_default_ok) RCASES)
        as (TN & bsN & LLI & LLAT2).
      replace (SRC + hl + 1) with (SRC + (hl + 1)) by lia.
      unfold hidden in OFWHERE, OFSTK, MLWHERE, MLSTK.
      eapply (sh_of m2 pLL p1 p2 nbSeq (hl + 1) rLL (Znth hl src) TN bsN TO bsO TM bsM); try eassumption; try reflexivity; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sh_zero : forall m1 hl xra x5 x6 x7 xs0 xa0 xa1 xa2 xa4 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31,
    SHB llt mlt oft (Z_to_bv 64 0) m1 -> munch [(NBP, NBP + 4); (SPV - 544, SPV)] m m1 ->
    1 <= hl <= Z.of_nat (length src) ->
    evt usegs POST (ST 0x17530 m1 xra x5 x6 x7 xs0 (Z_to_bv 64 (SRC + Z.of_nat (length src))) xa0 xa1 xa2 (Z_to_bv 64 (Z.of_nat (length src))) xa4 (Z_to_bv 64 (SRC + hl)) xa6 xa7
                       xs2 xs3 xs4 xs5 xs6 xs7 s8 x28 x29 x30 x31).
  Proof.
    intros m1 hl xra x5 x6 x7 xs0 xa0 xa1 xa2 xa4 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31 BODY SMALL HLR.
    clear FBY ALD ALN ALS.
    open_shh HY.
    zstep. if_cases ATEND; zify_cond ATEND.
    - zstep.
      apply (sh_ret m1 llt mlt oft (Z_to_bv 64 0) (Z.of_nat (length src))); [exact BODY | lia | reflexivity |].
      right. split; [lia|]. exists 0. split; [reflexivity|]. split; [lia|].
      left. exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl SMALL)))).
    - zstep. zstep.
      apply (sh_ret m1 llt mlt oft (Z_to_bv 64 0) (2^64 - 20)); [exact BODY | lia | apply Z_to_bv_eqm; reflexivity |].
      left. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sh_b3c : forall m1 nbSeq hl TL bsL TO bsO TM bsM xra x5 x6 x7 xs0 xs1v xa1 xa3 xa6 xa7 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31,
    SHB llt mlt oft (Z_to_bv 64 nbSeq) m1 ->
    1 <= nbSeq <= 98047 -> 1 <= hl <= Z.of_nat (length src) ->
    bytes_at usegs m1 TL bsL -> Z.of_nat (length bsL) <= 4104 ->
    (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_LL 32 PZD_LL_DEFAULT LL_defaultDTable llt TL bsL) ->
    (TL = DCTX + 32 \/ (TL + 4104 <= DCTX \/ DCTX + 30372 <= TL)) -> (TL + 4104 <= lo \/ SPV <= TL) ->
    bytes_at usegs m1 TO bsO -> Z.of_nat (length bsO) <= 2056 ->
    (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_OF 4136 PZD_OF_DEFAULT OF_defaultDTable oft TO bsO) ->
    (TO = DCTX + 4136 \/ (TO + 2056 <= DCTX \/ DCTX + 30372 <= TO)) -> (TO + 2056 <= lo \/ SPV <= TO) ->
    bytes_at usegs m1 TM bsM -> Z.of_nat (length bsM) <= 4104 ->
    (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_ML 6192 PZD_ML_DEFAULT ML_defaultDTable mlt TM bsM) ->
    (TM = DCTX + 6192 \/ (TM + 4104 <= DCTX \/ DCTX + 30372 <= TM)) -> (TM + 4104 <= lo \/ SPV <= TM) ->
    xs1v = Z_to_bv 64 nbSeq ->
    evt usegs POST (ST 0x17374 m1 xra x5 x6 x7 xs0 (Z_to_bv 64 (SRC + Z.of_nat (length src))) (Z_to_bv 64 DCTX) xa1 (Z_to_bv 64 SRC) xa3 (Z_to_bv 64 (-72)) (Z_to_bv 64 (SRC + hl)) xa6 xa7
                       xs1v xs3 xs4 xs5 xs6 xs7 s8 x28 x29 x30 x31).
  Proof.
    intros m1 nbSeq hl TL bsL TO bsO TM bsM xra x5 x6 x7 xs0 xs1v xa1 xa3 xa6 xa7 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31
           BODY NBR HLR LLAT LLLEN LLOLD LLWHERE LLSTK OFAT OFLEN OFOLD OFWHERE OFSTK MLAT MLLEN MLOLD MLWHERE MLSTK NBV.
    open_shh HY.
    (* ip + 1 cannot wrap: ip is far below 2^64 - 1 *)
    zstep. zstep. if_cases WRAP; zify_cond WRAP.
    { exfalso. lia. }
    clear WRAP.
    zstep. zstep. if_cases SHORT; zify_cond SHORT.
    - apply (sh_ret m1 llt mlt oft (Z_to_bv 64 nbSeq) (2^64 - 72)); [exact BODY | lia | apply Z_to_bv_eqm; reflexivity |].
      left. reflexivity.
    - subst xs1v.
      eapply (sh_ll m1 llt mlt oft nbSeq hl TL bsL TO bsO TM bsM); try eassumption; try reflexivity; lia.
  Qed.

  Lemma sh_nb : forall m1 nb0 nbSeq hl TL bsL TO bsO TM bsM xra x5 x6 x7 xs0 xa6 xa7 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31,
    SHB llt mlt oft nb0 m1 -> munch [(NBP, NBP + 4); (SPV - 544, SPV)] m m1 ->
    0 <= nbSeq <= 98047 -> 1 <= hl <= Z.of_nat (length src) ->
    bytes_at usegs m1 TL bsL -> Z.of_nat (length bsL) <= 4104 ->
    (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_LL 32 PZD_LL_DEFAULT LL_defaultDTable llt TL bsL) ->
    (TL = DCTX + 32 \/ (TL + 4104 <= DCTX \/ DCTX + 30372 <= TL)) -> (TL + 4104 <= lo \/ SPV <= TL) -> (TL + 4104 <= NBP \/ NBP + 4 <= TL) ->
    bytes_at usegs m1 TO bsO -> Z.of_nat (length bsO) <= 2056 ->
    (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_OF 4136 PZD_OF_DEFAULT OF_defaultDTable oft TO bsO) ->
    (TO = DCTX + 4136 \/ (TO + 2056 <= DCTX \/ DCTX + 30372 <= TO)) -> (TO + 2056 <= lo \/ SPV <= TO) -> (TO + 2056 <= NBP \/ NBP + 4 <= TO) ->
    bytes_at usegs m1 TM bsM -> Z.of_nat (length bsM) <= 4104 ->
    (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_ML 6192 PZD_ML_DEFAULT ML_defaultDTable mlt TM bsM) ->
    (TM = DCTX + 6192 \/ (TM + 4104 <= DCTX \/ DCTX + 30372 <= TM)) -> (TM + 4104 <= lo \/ SPV <= TM) -> (TM + 4104 <= NBP \/ NBP + 4 <= TM) ->
    evt usegs POST (ST 0x17360 m1 xra x5 x6 x7 xs0 (Z_to_bv 64 (SRC + Z.of_nat (length src))) (Z_to_bv 64 DCTX) (Z_to_bv 64 NBP) (Z_to_bv 64 SRC)
                       (Z_to_bv 64 (Z.of_nat (length src))) (Z_to_bv 64 (-72)) (Z_to_bv 64 (SRC + hl)) xa6 xa7
                       (Z_to_bv 64 nbSeq) xs3 xs4 xs5 xs6 xs7 s8 x28 x29 x30 x31).
  Proof.
    intros m1 nb0 nbSeq hl TL bsL TO bsO TM bsM xra x5 x6 x7 xs0 xa6 xa7 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31
           BODY SMALL NBR HLR LLAT LLLEN LLOLD LLWHERE LLSTK LLNB OFAT OFLEN OFOLD OFWHERE OFSTK OFNB
           MLAT MLLEN MLOLD MLWHERE MLSTK MLNB.
    open_shh HY. open_shb BODY. hide_all_disj.
    (* the count pointer is neither null nor misaligned *)
    zstep. uck. zstep. zstep. uck.
    (* *nbSeqPtr = nbSeq *)
    zstep.
    assert (BODY2 : SHB llt mlt oft (Z_to_bv 64 nbSeq) m0).
    { unfold SHB. repeat (split; [eassumption|]).
      split; [exists fa; exact FR|]. split; [exact MI|]. exact (conj MU WM). }
    zstep. if_cases NONE; zify_cond NONE.
    - rewrite NONE in BODY2. eapply (sh_zero m0 hl); [exact BODY2 | exact SMALL | lia].
    - eapply (sh_b3c m0 nbSeq hl TL bsL TO bsO TM bsM); try eassumption; try reflexivity; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sh_main : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 nb0 : word) TL bsL TO bsO TM bsM,
    rw_cells usegs m DCTX [C8 llt] -> rw_cells usegs m (DCTX + 8) [C8 mlt] -> rw_cells usegs m (DCTX + 16) [C8 oft] -> rw_cells usegs m (DCTX + 24) [C8 huf] ->
    stk usegs m (DCTX + 32) (DCTX + 4136) -> stk usegs m (DCTX + 4136) (DCTX + 6192) -> stk usegs m (DCTX + 6192) (DCTX + 10296) ->
    stk usegs m (DCTX + 27324) (DCTX + 29884) ->
    rw_cells usegs m (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 fe] -> rw_cells usegs m (DCTX + 30204) [C4 cold] ->
    rw_cells usegs m NBP [C4 nb0] -> bytes_at usegs m SRC (map (Z_to_bv 8) src) -> stk usegs m lo SPV -> mem_inv usegs m ->
    bytes_at usegs m TL bsL -> Z.of_nat (length bsL) <= 4104 ->
    (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_LL 32 PZD_LL_DEFAULT LL_defaultDTable llt TL bsL) ->
    (TL = DCTX + 32 \/ (TL + 4104 <= DCTX \/ DCTX + 30372 <= TL)) -> (TL + 4104 <= lo \/ SPV <= TL) -> (TL + 4104 <= NBP \/ NBP + 4 <= TL) ->
    bytes_at usegs m TO bsO -> Z.of_nat (length bsO) <= 2056 ->
    (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_OF 4136 PZD_OF_DEFAULT OF_defaultDTable oft TO bsO) ->
    (TO = DCTX + 4136 \/ (TO + 2056 <= DCTX \/ DCTX + 30372 <= TO)) -> (TO + 2056 <= lo \/ SPV <= TO) -> (TO + 2056 <= NBP \/ NBP + 4 <= TO) ->
    bytes_at usegs m TM bsM -> Z.of_nat (length bsM) <= 4104 ->
    (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_ML 6192 PZD_ML_DEFAULT ML_defaultDTable mlt TM bsM) ->
    (TM = DCTX + 6192 \/ (TM + 4104 <= DCTX \/ DCTX + 30372 <= TM)) -> (TM + 4104 <= lo \/ SPV <= TM) -> (TM + 4104 <= NBP \/ NBP + 4 <= TM) ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DCTX) (Z_to_bv 64 NBP) (Z_to_bv 64 SRC) (Z_to_bv 64 (Z.of_nat (length src)))
               a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x172fc) fc None m (seg_rom usegs)).
  Proof.
    intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 nb0 TL bsL TO bsO TM bsM
           P0 P1 P2 P3 ELL EOF EML EWK H3 COLD NB SRCB STK MI
           LLAT LLLEN LLOLD LLWHERE LLSTK LLNB OFAT OFLEN OFOLD OFWHERE OFSTK OFNB MLAT MLLEN MLOLD MLWHERE MLSTK MLNB.
    open_shh HY. hide_all_disj.
    pose proof (munch_refl FOOT m) as MU. pose proof (munch_refl [(NBP, NBP + 4); (SPV - 544, SPV)] m) as SMALL.
    pose proof (wmono_refl usegs m) as WM.
    (* the 96-byte frame and the nine saved registers *)
    zstep. carve_frame 96%nat STK.
    do 9 zstep.
    assert (BODY : SHB llt mlt oft nb0 m0).
    { unfold SHB. repeat (split; [eassumption|]).
      split; [eexists; exact FR|]. split; [exact MI|]. exact (conj MU WM). }
    (* iend = src + srcSize, with the two pointer-overflow checks *)
    zstep. zstep. uck.
    do 4 zstep. uckz.
    zstep. zstep. if_cases EMPTY; zify_cond EMPTY.
    { apply (sh_ret m0 llt mlt oft nb0 (2^64 - 72)); [exact BODY | lia | apply Z_to_bv_eqm; reflexivity |].
      left. reflexivity. }
    assert (BYTE : forall i, 0 <= i < Z.of_nat (length src) -> 0 <= Znth i src < 256).
    { intros i RNG. pose proof FBY as ALLB. rewrite Forall_forall in ALLB. apply ALLB. unfold Znth. apply nth_In. lia. }
    pose proof (BYTE 0 ltac:(lia)) as B0.
    do 3 zstep. uck. zstep. uck.
    zlb SRCB FBY 0.
    zstep. zstep. if_cases BIG; zify_cond BIG.
    2: { eapply (sh_nb m0 nb0 (Znth 0 src) 1 TL bsL TO bsO TM bsM); try eassumption; lia. }
    rewrite Z.shiftl_mul_pow2 in BIG by lia. change (2^56) with 72057594037927936 in BIG.
    rewrite Z.mod_small in BIG by lia.
    (* srai by 56 brings the byte back sign-extended; all ones means 0xff *)
    assert (SX : Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (Znth 0 src) 56))) 56 mod 18446744073709551616
                 = if Znth 0 src <? 128 then Znth 0 src else Znth 0 src + 18446744073709551360).
    { byte_brute (Znth 0 src). }
    zstep. zstep. zstep. if_cases ALLONES; zify_cond ALLONES.
    all: rewrite SX in ALLONES; replace (Znth 0 src <? 128) with false in ALLONES by (symmetry; apply Z.ltb_ge; lia).
    - (* 0xff: count in the next two bytes *)
      zstep. zstep. uck.
      zstep. zstep. if_cases SHORT3; zify_cond SHORT3.
      { apply (sh_ret m0 llt mlt oft nb0 (2^64 - 72)); [exact BODY | lia | apply Z_to_bv_eqm; reflexivity |].
        left. reflexivity. }
      pose proof (BYTE 1 ltac:(lia)) as B1. pose proof (BYTE 2 ltac:(lia)) as B2.
      zstep. zstep. uck.
      zlb SRCB FBY 2. zlb SRCB FBY 1.
      do 8 zs.
      eapply (sh_nb m0 nb0 _ 3 TL bsL TO bsO TM bsM); try eassumption; lia.
    - (* 0x80..0xfe: count in this byte and the next *)
      zstep. zstep. if_cases SHORT2; zify_cond SHORT2.
      { apply (sh_ret m0 llt mlt oft nb0 (2^64 - 72)); [exact BODY | lia | apply Z_to_bv_eqm; reflexivity |].
        left. reflexivity. }
      pose proof (BYTE 1 ltac:(lia)) as B1.
      zstep. zstep. uck.
      zlb SRCB FBY 1.
      do 6 zs.
      eapply (sh_nb m0 nb0 _ 2 TL bsL TO bsO TM bsM); try eassumption; lia.
  Qed.

End SH.

From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require F_fmt_fp_lib.

Theorem zd_seqhdr_proof : zd_seqhdr_stmt.
Proof.
  unfold zd_seqhdr_stmt, PZD_SEQHDR, off_stack, apart. intros until ws.
  intros PTRS ESEQ EWK H3 H5 TBLS DCL DCH NB NBL NBH SRCB FBY SLEN SRCL SRCH STK LO0 LOS SPH OFFD OFFNB OFFSRC DNB DSRC NBSRC ALD ALN ALS MI -> -> -> ->.
  (* [comment removed for export] *)
  pose proof (stk_not_ro m lo SPV MI STK ltac:(lia)) as IMGS.
  pose proof (rw_cells_not_ro m DCTX _ MI PTRS ltac:(cbn; lia)) as IM1. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in IM1.
  pose proof (stk_not_ro m _ _ MI ESEQ ltac:(lia)) as IM2. pose proof (stk_not_ro m _ _ MI EWK ltac:(lia)) as IM3.
  pose proof (rw_cells_not_ro m _ _ MI (proj1 H5) ltac:(rewrite (h5_cells_size ws (proj2 H5)); lia)) as IM4. rewrite (h5_cells_size ws (proj2 H5)) in IM4.
  assert (IMGD : DCTX + 30372 <= 0x10000 \/ 0x36000 <= DCTX) by lia. clear IM1 IM2 IM3 IM4.
  pose proof (rw_cells_not_ro m NBP _ MI NB ltac:(cbn; lia)) as IMNB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in IMNB.
  assert (HY : sh_hyps SPV lo DCTX NBP SRC (Z.of_nat (length src))).
  { unfold sh_hyps. repeat (split; [first [assumption | lia]|]). assumption. }
  (* [comment removed for export] *)
  assert (OLD : exists TL bsL TO bsO TM bsM,
            (bytes_at usegs m TL bsL /\ Z.of_nat (length bsL) <= 4104 /\
             (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_LL 32 PZD_LL_DEFAULT LL_defaultDTable llt TL bsL) /\
             (TL = DCTX + 32 \/ (TL + 4104 <= DCTX \/ DCTX + 30372 <= TL)) /\ (TL + 4104 <= lo \/ SPV <= TL) /\ (TL + 4104 <= NBP \/ NBP + 4 <= TL)) /\
            (bytes_at usegs m TO bsO /\ Z.of_nat (length bsO) <= 2056 /\
             (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_OF 4136 PZD_OF_DEFAULT OF_defaultDTable oft TO bsO) /\
             (TO = DCTX + 4136 \/ (TO + 2056 <= DCTX \/ DCTX + 30372 <= TO)) /\ (TO + 2056 <= lo \/ SPV <= TO) /\ (TO + 2056 <= NBP \/ NBP + 4 <= TO)) /\
            (bytes_at usegs m TM bsM /\ Z.of_nat (length bsM) <= 4104 /\
             (sx32 fe <> Z_to_bv 64 0 -> tab_info DCTX K_ML 6192 PZD_ML_DEFAULT ML_defaultDTable mlt TM bsM) /\
             (TM = DCTX + 6192 \/ (TM + 4104 <= DCTX \/ DCTX + 30372 <= TM)) /\ (TM + 4104 <= lo \/ SPV <= TM) /\ (TM + 4104 <= NBP \/ NBP + 4 <= TM))).
  { destruct (Z.eq_dec (bv_unsigned fe mod 4294967296) 0) as [FZ | FNZ].
    - assert (SZ : sx32 fe = Z_to_bv 64 0) by (apply bv_eq; rewrite (proj2 (F_fmt_fp_lib.sx32_zero fe) FZ); reflexivity).
      exists (DCTX + 32), [], (DCTX + 4136), [], (DCTX + 6192), [].
      assert (BE : forall A, 0 <= A -> A <= 2^64 -> bytes_at usegs m A []) by (intros A A0 A1; split; [exact A0|]; split; [cbn [length]; lia|]; intros i Hi; cbn in Hi; lia).
      split; [|split].
      + split; [apply BE; clear - DCL DCH; lia|]. split; [cbn [length]; lia|]. split; [intros NZ; exfalso; exact (NZ SZ)|]. split; [left; reflexivity|].
        split; [clear - OFFD; lia | clear - DNB; lia].
      + split; [apply BE; clear - DCL DCH; lia|]. split; [cbn [length]; lia|]. split; [intros NZ; exfalso; exact (NZ SZ)|]. split; [left; reflexivity|].
        split; [clear - OFFD; lia | clear - DNB; lia].
      + split; [apply BE; clear - DCL DCH; lia|]. split; [cbn [length]; lia|]. split; [intros NZ; exfalso; exact (NZ SZ)|]. split; [left; reflexivity|].
        split; [clear - OFFD; lia | clear - DNB; lia].
    - destruct (TBLS FNZ) as (LLT & MLT & OFT & tLL & tOF & tML & -> & -> & -> & PL & PO & PM & (BL & OKL) & (BO & OKO) & (BM & OKM)).
      assert (TIL : tab_info DCTX K_LL 32 PZD_LL_DEFAULT LL_defaultDTable (Z_to_bv 64 LLT) LLT (map (Z_to_bv 8) (seq_table_bytes tLL))) by (exists tLL; auto).
      assert (TIO : tab_info DCTX K_OF 4136 PZD_OF_DEFAULT OF_defaultDTable (Z_to_bv 64 OFT) OFT (map (Z_to_bv 8) (seq_table_bytes tOF))) by (exists tOF; auto).
      assert (TIM : tab_info DCTX K_ML 6192 PZD_ML_DEFAULT ML_defaultDTable (Z_to_bv 64 MLT) MLT (map (Z_to_bv 8) (seq_table_bytes tML))) by (exists tML; auto).
      pose proof (tab_info_len _ _ _ _ _ _ _ _ TIL) as LENL. pose proof (tab_info_len _ _ _ _ _ _ _ _ TIO) as LENO. pose proof (tab_info_len _ _ _ _ _ _ _ _ TIM) as LENM.
      cbn [kind_maxLog] in LENL, LENO, LENM. change (2^9) with 512 in LENL, LENM. change (2^8) with 256 in LENO.
      destruct (tab_info_geo _ _ _ _ _ _ _ _ lo SPV TIL ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(lia) ltac:(cbn; lia) IMGD IMGS OFFD) as [LOCL OFFL].
      destruct (tab_info_geo _ _ _ _ _ _ _ _ lo SPV TIO ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(lia) ltac:(cbn; lia) IMGD IMGS OFFD) as [LOCO OFFO].
      destruct (tab_info_geo _ _ _ _ _ _ _ _ lo SPV TIM ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(lia) ltac:(cbn; lia) IMGD IMGS OFFD) as [LOCM OFFM].
      cbn [kind_maxLog] in LOCL, OFFL, LOCO, OFFO, LOCM, OFFM. change (2^9) with 512 in LOCL, OFFL, LOCM, OFFM. change (2^8) with 256 in LOCO, OFFO.
      exists LLT, (map (Z_to_bv 8) (seq_table_bytes tLL)), OFT, (map (Z_to_bv 8) (seq_table_bytes tOF)), MLT, (map (Z_to_bv 8) (seq_table_bytes tML)).
      split; [|split].
      + split; [exact BL|]. split; [clear - LENL; lia|]. split; [intros _; exact TIL|]. split; [clear - LOCL; lia|]. split; [clear - OFFL; lia|].
        destruct PL as [-> | [-> _]]; [clear - DNB; unfold DCTX_entropy_LLTable; lia | clear - IMNB; unfold PZD_LL_DEFAULT; lia].
      + split; [exact BO|]. split; [clear - LENO; lia|]. split; [intros _; exact TIO|]. split; [clear - LOCO; lia|]. split; [clear - OFFO; lia|].
        destruct PO as [-> | [-> _]]; [clear - DNB; unfold DCTX_entropy_OFTable; lia | clear - IMNB; unfold PZD_OF_DEFAULT; lia].
      + split; [exact BM|]. split; [clear - LENM; lia|]. split; [intros _; exact TIM|]. split; [clear - LOCM; lia|]. split; [clear - OFFM; lia|].
        destruct PM as [-> | [-> _]]; [clear - DNB; unfold DCTX_entropy_MLTable; lia | clear - IMNB; unfold PZD_ML_DEFAULT; lia]. }
  destruct OLD as (TL & bsL & TO & bsO & TM & bsM & (L1 & L2 & L3 & L4 & L5 & L6) & (O1 & O2 & O3 & O4 & O5 & O6) & (M1 & M2 & M3 & M4 & M5 & M6)).
  (* [comment removed for export] *)
  unfold dctx_ptrs in PTRS. change [C8 llt; C8 mlt; C8 oft; C8 huf] with ([C8 llt] ++ [C8 mlt] ++ [C8 oft] ++ [C8 huf]) in PTRS.
  apply rw_cells_app in PTRS. destruct PTRS as [P0 PTRS]. cbn [cells_size csize Nat.add] in PTRS. replace (DCTX + Z.of_nat 8) with (DCTX + 8) in PTRS by lia.
  apply rw_cells_app in PTRS. destruct PTRS as [P1 PTRS]. cbn [cells_size csize Nat.add] in PTRS. replace (DCTX + 8 + Z.of_nat 8) with (DCTX + 16) in PTRS by lia.
  apply rw_cells_app in PTRS. destruct PTRS as [P2 P3]. cbn [cells_size csize Nat.add] in P3. replace (DCTX + 16 + Z.of_nat 8) with (DCTX + 24) in P3 by lia.
  destruct (stk_split usegs m _ (DCTX + 4136) _ ESEQ ltac:(lia)) as [ELL E2].
  destruct (stk_split usegs m _ (DCTX + 6192) _ E2 ltac:(lia)) as [EOF EML].
  pose proof (h5_cold_cell m DCTX ws H5) as COLD.
  unfold dctx_h3 in H3.
  eapply (sh_main ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX NBP SRC src llt mlt oft huf pcs dsz bt stg le fe _ HY FBY ALD ALN ALS
            t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 nb0 TL bsL TO bsO TM bsM); eassumption.
Qed.
