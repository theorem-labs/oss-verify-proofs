(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.
Lemma pll_bits_at : forall m, mem_inv usegs m -> bytes_at usegs m PLL_BITS (map (Z_to_bv 8) (kind_bits K_LL)).
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.
Lemma pof_base_at : forall m, mem_inv usegs m -> bytes_at usegs m POF_BASE (u32s (map (Z_to_bv 64) (kind_base K_OF))).
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.
Lemma pof_bits_at : forall m, mem_inv usegs m -> bytes_at usegs m POF_BITS (map (Z_to_bv 8) (kind_bits K_OF)).
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.
Lemma pml_base_at : forall m, mem_inv usegs m -> bytes_at usegs m PML_BASE (u32s (map (Z_to_bv 64) (kind_base K_ML))).
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.
Lemma pml_bits_at : forall m, mem_inv usegs m -> bytes_at usegs m PML_BITS (map (Z_to_bv 8) (kind_bits K_ML)).
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.

(* [comment removed for export] *)
Definition tab_info (DCTX : Z) (k : seq_kind) (own dflt : Z) (d : seq_table) (pv : word) (T : Z) (bs : list byte) : Prop :=
  exists t, pv = Z_to_bv 64 T /\ bs = map (Z_to_bv 8) (seq_table_bytes t) /\ seq_table_ok k t /\ tbl_ptr DCTX own dflt d T t.

Lemma tab_info_tab : forall m DCTX k own dflt d pv T bs,
  tab_info DCTX k own dflt d pv T bs -> bytes_at usegs m T bs -> seqhdr_tab m DCTX k own dflt d pv.
Proof. intros m DCTX k own dflt d pv T bs (t & -> & -> & OK & TP) BA. exists T, t. split; [reflexivity|]. split; [exact TP|]. split; assumption. Qed.

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
  intros m m' W DCTX k own dflt d oldp pv frw ty T0 bs0 OB OL OV LOC FRAME (DB & DOK) [(_ & ->) | [(_ & FRN & -> & SAME) | (_ & -> & t & TOK & TB)]].
  - exists dflt, (map (Z_to_bv 8) (seq_table_bytes d)). split; [|exact DB].
    exists d. split; [reflexivity|]. split; [reflexivity|]. split; [exact DOK|]. right. auto.
  - exists T0, bs0. split; [exact (OV FRN)|]. destruct LOC as [-> | DJ]; [apply SAME; assumption | apply FRAME; assumption].
  - exists (DCTX + own), (map (Z_to_bv 8) (seq_table_bytes t)). split; [|exact TB].
    exists t. split; [reflexivity|]. split; [reflexivity|]. split; [exact TOK|]. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tab_info_geo : forall DCTX k own dflt d pv T bs lo SPV,
  tab_info DCTX k own dflt d pv T bs ->
  0x10000 <= dflt -> dflt + TSZ k <= 0x36000 -> 32 <= own -> own + TSZ k <= 10296 ->
  (DCTX + 30372 <= 0x10000 \/ 0x36000 <= DCTX) -> (SPV <= 0x10000 \/ 0x36000 <= lo) -> (DCTX + 95992 <= lo \/ SPV <= DCTX) ->
  (T = DCTX + own \/ (T + TSZ k <= DCTX \/ DCTX + 30372 <= T)) /\ (T + TSZ k <= lo \/ SPV <= T).
Proof.
  intros DCTX k own dflt d pv T bs lo SPV (t & _ & _ & _ & [-> | [-> _]]) D0 D1 O0 O1 IMGD IMGS OFFD; split; lia.
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
  intros m DCTX ws (C & L). h5_open ws L.
  lazymatch type of C with rw_cells _ _ _ ?cs =>
    change cs with (firstn 17 cs ++ [nth 17 cs (C1 (Z_to_bv 8 0))] ++ skipn 18 cs) in C end.
  cbn [firstn skipn nth] in C.
  apply rw_cells_app in C. destruct C as [_ C]. apply rw_cells_app in C. destruct C as [C _].
  cbn [cells_size csize Nat.add] in C. replace (DCTX + 30096 + Z.of_nat 108) with (DCTX + 30204) in C by lia. exact C.
Qed.

(* [comment removed for export] *)
Definition sh_hyps (SPV lo DCTX NBP SRC slen : Z) : Prop :=
  4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= NBP /\ NBP + 4 < 2^47 /\ 0 <= slen <= 1048576 /\ 4096 <= SRC /\ SRC + slen < 2^47
  /\ 4096 <= lo /\ lo <= SPV - 544 /\ SPV < 2^47
  /\ (DCTX + 95992 <= lo \/ SPV <= DCTX) /\ (NBP + 4 <= lo \/ SPV <= NBP) /\ (SRC + slen <= lo \/ SPV <= SRC)
  /\ (DCTX + 95992 <= NBP \/ NBP + 4 <= DCTX) /\ (DCTX + 95992 <= SRC \/ SRC + slen <= DCTX) /\ (NBP + 4 <= SRC \/ SRC + slen <= NBP)
  /\ (DCTX + 30372 <= 0x10000 \/ 0x36000 <= DCTX) /\ (SPV <= 0x10000 \/ 0x36000 <= lo).
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
    rw_cells usegs m1 DCTX [C8 p0] /\ rw_cells usegs m1 (DCTX + 8) [C8 p1] /\ rw_cells usegs m1 (DCTX + 16) [C8 p2]
    /\ rw_cells usegs m1 (DCTX + 24) [C8 huf]
    /\ stk usegs m1 (DCTX + 32) (DCTX + 4136) /\ stk usegs m1 (DCTX + 4136) (DCTX + 6192) /\ stk usegs m1 (DCTX + 6192) (DCTX + 10296)
    /\ stk usegs m1 (DCTX + 27324) (DCTX + 29884)
    /\ rw_cells usegs m1 (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 fe]
    /\ rw_cells usegs m1 (DCTX + 30204) [C4 cold]
    /\ rw_cells usegs m1 NBP [C4 nbw]
    /\ bytes_at usegs m1 SRC (map (Z_to_bv 8) src)
    /\ stk usegs m1 lo (SPV + -96)
    /\ (exists fa, rw_cells usegs m1 (SPV + -96) [CB 24 fa; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ mem_inv usegs m1 /\ munch FOOT m m1 /\ wmono usegs m m1.
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
    intros until x31. intros I HR -> RES. open_shb I. open_shh HY.
    zstep. do 9 zstep. zstep.
    release_frame FR STK SPV.
    zstep. apply evt_done. unfold zd_seqhdr_post.
    do 14 eexists. exists m1, r, p0, p1, p2, nbw.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
    split.
    { unfold dctx_ptrs. change [C8 p0; C8 p1; C8 p2; C8 huf] with ([C8 p0] ++ [C8 p1] ++ [C8 p2] ++ [C8 huf]).
      apply rw_cells_app. split; [exact P0|]. cbn [cells_size csize Nat.add]. replace (DCTX + Z.of_nat 8) with (DCTX + 8) by lia.
      apply rw_cells_app. split; [exact P1|]. cbn [cells_size csize Nat.add]. replace (DCTX + 8 + Z.of_nat 8) with (DCTX + 16) by lia.
      apply rw_cells_app. split; [exact P2|]. cbn [cells_size csize Nat.add]. replace (DCTX + 16 + Z.of_nat 8) with (DCTX + 24) by lia. exact P3. }
    split; [eapply stk_merge; [eapply stk_merge; [exact ELL | exact EOF | lia] | exact EML | lia]|].
    split; [exact EWK|]. split; [exact NB|]. split; [exact HR| exact RES].
  Qed.

  Lemma bytes_at_skipn_src : forall m1 i, bytes_at usegs m1 SRC (map (Z_to_bv 8) src) -> 0 <= i <= Z.of_nat (length src) ->
    bytes_at usegs m1 (SRC + i) (map (Z_to_bv 8) (skipn (Z.to_nat i) src)).
  Proof.
    intros m1 i (B0 & B1 & B) Hi. rewrite length_map in *. split; [lia|]. split; [rewrite length_map, skipn_length; lia|].
    intros j Hj. rewrite length_map, skipn_length in Hj.
    replace (SRC + i + Z.of_nat j) with (SRC + Z.of_nat (Z.to_nat i + j)) by lia. rewrite B by lia.
    rewrite <- skipn_map. rewrite nth_error_skipn. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sh_frame : forall m1 a b x,
    rw_cells usegs m1 (SPV + -96) [C8 a; C8 b] ->
    rw_cells usegs m1 (SPV + -80) [CB 8 x; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    exists fa, rw_cells usegs m1 (SPV + -96) [CB 24 fa; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Proof.
    intros m1 a b x ARGS FRR.
    assert (FA : rw_cells usegs m1 (SPV + -96) ([] ++ [C8 a; C8 b; CB 8 x] ++ [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { change ([] ++ [C8 a; C8 b; CB 8 x] ++ [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
        with ([C8 a; C8 b] ++ [CB 8 x; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      apply rw_cells_app. split; [exact ARGS|]. cbn [cells_size csize Nat.add]. replace (SPV + -96 + Z.of_nat 16) with (SPV + -80) by lia. exact FRR. }
    pose proof (rw_cells_merge usegs m1 (SPV + -96) [] _ _ FA) as FM. cbn [app cells_size csize Nat.add] in FM. eexists. exact FM.
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
    intros until x31. intros I NBR TBR I2 R2 IR TI0 TB0 TI2 TB2 OLDB OLDL OLDV LOCM OFFM ->. open_shb I. open_shh HY.
    pose proof (tab_info_len _ _ _ _ _ _ _ _ TI0) as LEN0. pose proof (tab_info_len _ _ _ _ _ _ _ _ TI2) as LEN2.
    cbn [kind_maxLog] in LEN0, LEN2. change (2^9) with 512 in LEN0. change (2^8) with 256 in LEN2.
    destruct (tab_info_geo DCTX K_LL 32 PZD_LL_DEFAULT LL_defaultDTable p0 T0 bs0 lo SPV TI0 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(lia) ltac:(cbn; lia) ltac:(unfold hidden in IMGD; exact IMGD) ltac:(unfold hidden in IMGS; exact IMGS) ltac:(unfold hidden in OFFD; exact OFFD)) as [LOC0 OFF0].
    destruct (tab_info_geo DCTX K_OF 4136 PZD_OF_DEFAULT OF_defaultDTable p2 T2 bs2 lo SPV TI2 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(lia) ltac:(cbn; lia) ltac:(unfold hidden in IMGD; exact IMGD) ltac:(unfold hidden in IMGS; exact IMGS) ltac:(unfold hidden in OFFD; exact OFFD)) as [LOC2 OFF2].
    cbn [kind_maxLog] in LOC0, OFF0, LOC2, OFF2. change (2^9) with 512 in LOC0, OFF0. change (2^8) with 256 in LOC2, OFF2.
    hide_all_disj.
    zstep. zstep. rewrite lxor_ones64 by lia. uck.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    do 8 zstep.
    zstep. zstep. zstep. zstep.
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?c2 :: ?rest) => change (c1 :: c2 :: rest) with ([c1; c2] ++ rest) in FR end.
    apply rw_cells_app in FR. destruct FR as [ARGS FRR]. cbn [cells_size csize Nat.add] in FRR.
    replace (SPV + -96 + Z.of_nat 16) with (SPV + -80) in FRR by lia.
    set (i3 := i2 + r2) in *. replace (SRC + i2 + r2) with (SRC + i3) by lia.
    pose proof (bytes_at_skipn_src _ i3 SRCB ltac:(lia)) as SRC3.
    assert (LSK : Z.of_nat (length (skipn (Z.to_nat i3) src)) = Z.of_nat (length src) - i3) by (rewrite skipn_length; lia).
    assert (FSK : Forall (fun c => 0 <= c < 256) (skipn (Z.to_nat i3) src)).
    { pose proof FBY as FB. rewrite <- (firstn_skipn (Z.to_nat i3) src) in FB. apply Forall_app in FB. exact (proj2 FB). }
    pose proof (pml_base_at _ MI) as BASEB. pose proof (pml_bits_at _ MI) as BITSB.
    assert (E9 : 2 ^ kind_maxLog K_ML = 512) by reflexivity.
    assert (TYR : 0 <= (tb ≪ 60 mod 18446744073709551616) ≫ 62 <= 3).
    { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.mod_pos_bound (tb ≪ 60) 18446744073709551616 ltac:(lia)) as MB.
      split; [apply Z.div_pos; lia|]. assert (X : (tb ≪ 60 mod 18446744073709551616) / 2 ^ 62 < 4) by (apply Z.div_lt_upper_bound; lia). lia. }
    hide OLDB.
    pose proof zd_buildseq_stk as BS. unfold off_stack, apart in BS.
    eapply evt_cut; [ eapply BS with (SPV := SPV + -96) (lo := lo) (DTS := DCTX + 6192) (DTP := DCTX + 8) (SRC := SRC + i3) (W := DCTX + 27324)
        (DFLT := PZD_ML_DEFAULT) (BASE := PML_BASE) (BITS := PML_BITS) (ty := (tb ≪ 60 mod 18446744073709551616) ≫ 62) (wlen := 2560) (k := K_ML)
        (srcb := skipn (Z.to_nat i3) src) (oldp := p1) (nbw := Z_to_bv 64 nbSeq);
        first [ eassumption | reflexivity
              | replace (DCTX + 6192 + (8 + 8 * 2 ^ kind_maxLog K_ML)) with (DCTX + 10296) by (rewrite E9; lia); exact EML
              | replace (DCTX + 27324 + 2560) with (DCTX + 29884) by lia; exact EWK
              | unfold PML_BASE, PML_BITS; lia | sep_solve
              | unfold PML_BASE, PML_BITS; unfold hidden in IMGD, IMGS; lia
              | f_equal; lia
              | intros FN; eapply (tab_info_rng _ _ _ _ _ _ _ _ _ OLDV); try exact FN; unfold PZD_ML_DEFAULT; lia ]
      | clear BS; post_call usegs m1 ].
    rename PC into STK. rename PC0 into EML. rename PC1 into EWK. rename PC2 into P1. rename PC3 into FRAME. rename POST into RES.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
    lazymatch type of P1 with rw_cells _ _ _ [C8 ?v] => rename v into pvn end.
    lazymatch type of PC4 with 0 <= ?r < _ => rename r into rr end.
    rewrite E9 in EML. replace (DCTX + 6192 + (8 + 8 * 512)) with (DCTX + 10296) in EML by lia.
    replace (DCTX + 27324 + 2560) with (DCTX + 29884) in EWK by lia.
    pose proof (sh_frame _ _ _ _ ARGS FRR) as FRM.
    assert (SHI : SHB p0 pvn p2 (Z_to_bv 64 nbSeq) mc).
    { split; [exact P0|]. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact ELL|]. split; [exact EOF|]. split; [exact EML|].
      split; [exact EWK|]. split; [exact H3|]. split; [exact COLD|]. split; [exact NB|]. split; [exact SRCB|]. split; [exact STK|].
      split; [exact FRM|]. split; [assumption|]. split; [exact MU| exact WM]. }
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - eapply (sh_ret _ p0 _ p2 _ (2^64 - 20)); [exact SHI | lia | apply bv_eq; reflexivity | left; reflexivity].
    - destruct RES as [ER | (RL & RES)]; [exfalso; unfold zd_is_error, ZE_maxCode in ER; apply Z.ltb_lt in ER; lia|].
      unfold hidden in OLDB.
      assert (LOCW : TM = DCTX + 6192 \/
                disjoint_from [(DCTX + 6192, DCTX + 6192 + (8 + 8 * 2 ^ kind_maxLog K_ML)); (DCTX + 8, DCTX + 8 + 8);
                               (DCTX + 27324, DCTX + 27324 + 2560); (SPV + -96 - 448, SPV + -96)] TM (Z.of_nat (length bsM))).
      { unfold hidden in LOCM, OFFM. destruct LOCM as [L|L]; [left; exact L | right; cbn [disjoint_from]; rewrite E9; repeat split; lia]. }
      destruct (tab_after_call m1 mc _ DCTX K_ML 6192 PZD_ML_DEFAULT ML_defaultDTable p1 _ (sx32 fe) _ TM bsM OLDB
                  ltac:(rewrite E9; lia) OLDV LOCW FRAME
                  (conj (pml_default_at mc ltac:(assumption)) ML_default_ok) RES) as (TM' & bsM' & TIM & TBM).
      zstep. zstep. rewrite lxor_ones64 by lia. uck. zstep. zstep. zstep.
      eapply (sh_ret _ p0 _ p2 _ (i3 + rr)); [exact SHI | lia | f_equal; lia | ].
      right. split; [lia|]. exists nbSeq. split; [reflexivity|]. split; [lia|]. right. split; [lia|].
      split; [exact (tab_info_tab _ _ _ _ _ _ _ _ _ TI0 TB0)|]. split; [exact (tab_info_tab _ _ _ _ _ _ _ _ _ TI2 TB2)|].
      exact (tab_info_tab _ _ _ _ _ _ _ _ _ TIM TBM).
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
    intros until x31. intros I NBR TBR I1 R1 IR TI0 TB0 OLDB OLDL OLDV LOCO OFFO OLDBM OLDLM OLDVM LOCM OFFM ->. open_shb I. open_shh HY.
    pose proof (tab_info_len _ _ _ _ _ _ _ _ TI0) as LEN0. cbn [kind_maxLog] in LEN0. change (2^9) with 512 in LEN0.
    destruct (tab_info_geo DCTX K_LL 32 PZD_LL_DEFAULT LL_defaultDTable p0 T0 bs0 lo SPV TI0 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(lia) ltac:(cbn; lia) ltac:(unfold hidden in IMGD; exact IMGD) ltac:(unfold hidden in IMGS; exact IMGS) ltac:(unfold hidden in OFFD; exact OFFD)) as [LOC0 OFF0].
    cbn [kind_maxLog] in LOC0, OFF0. change (2^9) with 512 in LOC0, OFF0.
    hide_all_disj.
    zstep. zstep. rewrite lxor_ones64 by lia. uck.
    do 10 zstep. do 8 zstep.
    zstep. zstep. zstep. zstep.
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?c2 :: ?rest) => change (c1 :: c2 :: rest) with ([c1; c2] ++ rest) in FR end.
    apply rw_cells_app in FR. destruct FR as [ARGS FRR]. cbn [cells_size csize Nat.add] in FRR.
    replace (SPV + -96 + Z.of_nat 16) with (SPV + -80) in FRR by lia.
    set (i2 := i1 + r1) in *. replace (SRC + i1 + r1) with (SRC + i2) by lia.
    pose proof (bytes_at_skipn_src _ i2 SRCB ltac:(lia)) as SRC2.
    assert (LSK : Z.of_nat (length (skipn (Z.to_nat i2) src)) = Z.of_nat (length src) - i2) by (rewrite skipn_length; lia).
    assert (FSK : Forall (fun c => 0 <= c < 256) (skipn (Z.to_nat i2) src)).
    { pose proof FBY as FB. rewrite <- (firstn_skipn (Z.to_nat i2) src) in FB. apply Forall_app in FB. exact (proj2 FB). }
    pose proof (pof_base_at _ MI) as BASEB. pose proof (pof_bits_at _ MI) as BITSB.
    assert (E8 : 2 ^ kind_maxLog K_OF = 256) by reflexivity.
    assert (TYR : 0 <= (tb ≪ 58 mod 18446744073709551616) ≫ 62 <= 3).
    { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.mod_pos_bound (tb ≪ 58) 18446744073709551616 ltac:(lia)) as MB.
      split; [apply Z.div_pos; lia|]. assert (X : (tb ≪ 58 mod 18446744073709551616) / 2 ^ 62 < 4) by (apply Z.div_lt_upper_bound; lia). lia. }
    hide OLDB.
    pose proof zd_buildseq_stk as BS. unfold off_stack, apart in BS.
    eapply evt_cut; [ eapply BS with (SPV := SPV + -96) (lo := lo) (DTS := DCTX + 4136) (DTP := DCTX + 16) (SRC := SRC + i2) (W := DCTX + 27324)
        (DFLT := PZD_OF_DEFAULT) (BASE := POF_BASE) (BITS := POF_BITS) (ty := (tb ≪ 58 mod 18446744073709551616) ≫ 62) (wlen := 2560) (k := K_OF)
        (srcb := skipn (Z.to_nat i2) src) (oldp := p2) (nbw := Z_to_bv 64 nbSeq);
        first [ eassumption | reflexivity
              | replace (DCTX + 4136 + (8 + 8 * 2 ^ kind_maxLog K_OF)) with (DCTX + 6192) by (rewrite E8; lia); exact EOF
              | replace (DCTX + 27324 + 2560) with (DCTX + 29884) by lia; exact EWK
              | unfold POF_BASE, POF_BITS; lia | sep_solve
              | unfold POF_BASE, POF_BITS; unfold hidden in IMGD, IMGS; lia
              | f_equal; lia
              | intros FN; eapply (tab_info_rng _ _ _ _ _ _ _ _ _ OLDV); try exact FN; unfold PZD_OF_DEFAULT; lia ]
      | clear BS; post_call usegs m1 ].
    rename PC into STK. rename PC0 into EOF. rename PC1 into EWK. rename PC2 into P2. rename PC3 into FRAME. rename POST into RES.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
    lazymatch type of P2 with rw_cells _ _ _ [C8 ?v] => rename v into pvn end.
    lazymatch type of PC4 with 0 <= ?r < _ => rename r into rr end.
    rewrite E8 in EOF. replace (DCTX + 4136 + (8 + 8 * 256)) with (DCTX + 6192) in EOF by lia.
    replace (DCTX + 27324 + 2560) with (DCTX + 29884) in EWK by lia.
    pose proof (sh_frame _ _ _ _ ARGS FRR) as FRM.
    assert (SHI : SHB p0 p1 pvn (Z_to_bv 64 nbSeq) mc).
    { split; [exact P0|]. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact ELL|]. split; [exact EOF|]. split; [exact EML|].
      split; [exact EWK|]. split; [exact H3|]. split; [exact COLD|]. split; [exact NB|]. split; [exact SRCB|]. split; [exact STK|].
      split; [exact FRM|]. split; [assumption|]. split; [exact MU| exact WM]. }
    zstep. zstep. if_cases K; zify_cond K.
    - zstep. zstep.
      eapply (sh_ret _ p0 p1 _ _ (2^64 - 20)); [exact SHI | lia | apply bv_eq; reflexivity | left; reflexivity].
    - destruct RES as [ER | (RL & RES)]; [exfalso; unfold zd_is_error, ZE_maxCode in ER; apply Z.ltb_lt in ER; lia|].
      unfold hidden in OLDB.
      assert (LOCW : TO = DCTX + 4136 \/
                disjoint_from [(DCTX + 4136, DCTX + 4136 + (8 + 8 * 2 ^ kind_maxLog K_OF)); (DCTX + 16, DCTX + 16 + 8);
                               (DCTX + 27324, DCTX + 27324 + 2560); (SPV + -96 - 448, SPV + -96)] TO (Z.of_nat (length bsO))).
      { unfold hidden in LOCO, OFFO. destruct LOCO as [L|L]; [left; exact L | right; cbn [disjoint_from]; rewrite E8; repeat split; lia]. }
      destruct (tab_after_call m1 mc _ DCTX K_OF 4136 PZD_OF_DEFAULT OF_defaultDTable p2 _ (sx32 fe) _ TO bsO OLDB
                  ltac:(rewrite E8; lia) OLDV LOCW FRAME
                  (conj (pof_default_at mc ltac:(assumption)) OF_default_ok) RES) as (TO' & bsO' & TIO & TBO).
      eapply (sh_ml mc p0 p1 pvn nbSeq i2 rr tb T0 bs0 TO' bsO' TM bsM); try eassumption; try lia; try reflexivity.
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
    intros until x31. intros I NBR HL1 HLS OLDB OLDL OLDV LOCL OFFL OLDBO OLDLO OLDVO LOCO OFFO OLDBM OLDLM OLDVM LOCM OFFM ->.
    pose proof I as SHI0. open_shb I. open_shh HY.
    hide_all_disj.
    set (tb := Znth hl src).
    pose proof (Forall_Znth _ _ hl FBY ltac:(lia)) as TBR. cbv beta in TBR. fold tb in TBR.
    pose proof (u8ro_read usegs m1 SRC _ hl _ (wa (SRC + hl)) SRCB (nth_error_map_Znth (Z_to_bv 8) src hl ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD0.
    fold tb in RD0.
    zstep. cbv beta. rewrite (byte_lit tb) by lia.
    zstep. zstep. zstep. if_cases K0; zify_cond K0.
    { eapply (sh_ret _ p0 p1 p2 _ (2^64 - 20)); [exact SHI0 | lia | apply bv_eq; reflexivity | left; reflexivity]. }
    clear SHI0.
    zstep. uck. zstep. zstep. uck.
    do 11 zstep. do 8 zstep.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mb end.
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?c2 :: ?rest) => change (c1 :: c2 :: rest) with ([c1; c2] ++ rest) in FR end.
    apply rw_cells_app in FR. destruct FR as [ARGS FRR]. cbn [cells_size csize Nat.add] in FRR.
    replace (SPV + -96 + Z.of_nat 16) with (SPV + -80) in FRR by lia.
    set (i1 := hl + 1) in *. replace (SRC + hl + 1) with (SRC + i1) by lia.
    pose proof (bytes_at_skipn_src _ i1 SRCB ltac:(lia)) as SRC1.
    assert (LSK : Z.of_nat (length (skipn (Z.to_nat i1) src)) = Z.of_nat (length src) - i1) by (rewrite skipn_length; lia).
    assert (FSK : Forall (fun c => 0 <= c < 256) (skipn (Z.to_nat i1) src)).
    { pose proof FBY as FB. rewrite <- (firstn_skipn (Z.to_nat i1) src) in FB. apply Forall_app in FB. exact (proj2 FB). }
    pose proof (pll_base_at _ MI) as BASEB. pose proof (pll_bits_at _ MI) as BITSB.
    assert (E9 : 2 ^ kind_maxLog K_LL = 512) by reflexivity.
    assert (TYR : 0 <= tb ≫ 6 <= 3).
    { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. assert (X : tb / 2 ^ 6 < 4) by (apply Z.div_lt_upper_bound; lia). lia. }
    hide OLDB.
    pose proof zd_buildseq_stk as BS. unfold off_stack, apart in BS.
    eapply evt_cut; [ eapply BS with (SPV := SPV + -96) (lo := lo) (DTS := DCTX + 32) (DTP := DCTX) (SRC := SRC + i1) (W := DCTX + 27324)
        (DFLT := PZD_LL_DEFAULT) (BASE := PLL_BASE) (BITS := PLL_BITS) (ty := tb ≫ 6) (wlen := 2560) (k := K_LL)
        (srcb := skipn (Z.to_nat i1) src) (oldp := p0) (nbw := Z_to_bv 64 nbSeq);
        first [ eassumption | reflexivity
              | replace (DCTX + 32 + (8 + 8 * 2 ^ kind_maxLog K_LL)) with (DCTX + 4136) by (rewrite E9; lia); exact ELL
              | replace (DCTX + 27324 + 2560) with (DCTX + 29884) by lia; exact EWK
              | unfold PLL_BASE, PLL_BITS; lia | sep_solve
              | unfold PLL_BASE, PLL_BITS; unfold hidden in IMGD, IMGS; lia
              | f_equal; lia
              | intros FN; eapply (tab_info_rng _ _ _ _ _ _ _ _ _ OLDV); try exact FN; unfold PZD_LL_DEFAULT; lia ]
      | clear BS; post_call usegs mb ].
    rename PC into STK. rename PC0 into ELL. rename PC1 into EWK. rename PC2 into P0. rename PC3 into FRAME. rename POST into RES.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
    lazymatch type of P0 with rw_cells _ _ _ [C8 ?v] => rename v into pvn end.
    lazymatch type of PC4 with 0 <= ?r < _ => rename r into rr end.
    rewrite E9 in ELL. replace (DCTX + 32 + (8 + 8 * 512)) with (DCTX + 4136) in ELL by lia.
    replace (DCTX + 27324 + 2560) with (DCTX + 29884) in EWK by lia.
    pose proof (sh_frame _ _ _ _ ARGS FRR) as FRM.
    assert (SHI : SHB pvn p1 p2 (Z_to_bv 64 nbSeq) mc).
    { split; [exact P0|]. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact ELL|]. split; [exact EOF|]. split; [exact EML|].
      split; [exact EWK|]. split; [exact H3|]. split; [exact COLD|]. split; [exact NB|]. split; [exact SRCB|]. split; [exact STK|].
      split; [exact FRM|]. split; [assumption|]. split; [exact MU| exact WM]. }
    zstep. zstep. if_cases K; zify_cond K.
    - zstep. zstep.
      eapply (sh_ret _ _ p1 p2 _ (2^64 - 20)); [exact SHI | lia | apply bv_eq; reflexivity | left; reflexivity].
    - destruct RES as [ER | (RL & RES)]; [exfalso; unfold zd_is_error, ZE_maxCode in ER; apply Z.ltb_lt in ER; lia|].
      unfold hidden in OLDB.
      assert (LOCW : TL = DCTX + 32 \/
                disjoint_from [(DCTX + 32, DCTX + 32 + (8 + 8 * 2 ^ kind_maxLog K_LL)); (DCTX, DCTX + 8);
                               (DCTX + 27324, DCTX + 27324 + 2560); (SPV + -96 - 448, SPV + -96)] TL (Z.of_nat (length bsL))).
      { unfold hidden in LOCL, OFFL. destruct LOCL as [L|L]; [left; exact L | right; cbn [disjoint_from]; rewrite E9; repeat split; lia]. }
      destruct (tab_after_call mb mc _ DCTX K_LL 32 PZD_LL_DEFAULT LL_defaultDTable p0 _ (sx32 fe) _ TL bsL OLDB
                  ltac:(rewrite E9; lia) OLDV LOCW FRAME
                  (conj (pll_default_at mc ltac:(assumption)) LL_default_ok) RES) as (TL' & bsL' & TIL & TBL).
      eapply (sh_of mc pvn p1 p2 nbSeq i1 rr tb TL' bsL' TO bsO TM bsM); try eassumption; try lia; try reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sh_zero : forall m1 hl xra x5 x6 x7 xs0 xa0 xa1 xa2 xa4 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 x28 x29 x30 x31,
    SHB llt mlt oft (Z_to_bv 64 0) m1 -> munch [(NBP, NBP + 4); (SPV - 544, SPV)] m m1 ->
    1 <= hl <= Z.of_nat (length src) ->
    evt usegs POST (ST 0x17530 m1 xra x5 x6 x7 xs0 (Z_to_bv 64 (SRC + Z.of_nat (length src))) xa0 xa1 xa2 (Z_to_bv 64 (Z.of_nat (length src))) xa4 (Z_to_bv 64 (SRC + hl)) xa6 xa7
                       xs2 xs3 xs4 xs5 xs6 xs7 s8 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I MU0 HL. pose proof I as SHI. open_shb I. open_shh HY.
    zstep. if_cases K; zify_cond K.
    - zstep.
      eapply (sh_ret _ llt mlt oft _ (Z.of_nat (length src))); [exact SHI | lia | reflexivity | ].
      right. split; [lia|]. exists 0. split; [reflexivity|]. split; [lia|]. left. auto.
    - zstep. zstep.
      eapply (sh_ret _ llt mlt oft _ (2^64 - 20)); [exact SHI | lia | apply bv_eq; reflexivity | left; reflexivity].
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
    intros until x31. intros I NBR HL OLDB OLDL OLDV LOCL OFFL OLDBO OLDLO OLDVO LOCO OFFO OLDBM OLDLM OLDVM LOCM OFFM ->.
    pose proof I as SHI. open_shb I. open_shh HY.
    zstep. zstep. uck. zstep. zstep. if_cases K; zify_cond K.
    - eapply (sh_ret _ llt mlt oft _ (2^64 - 72)); [exact SHI | lia | apply bv_eq; reflexivity | left; reflexivity].
    - eapply (sh_ll m1 llt mlt oft nbSeq hl TL bsL TO bsO TM bsM); try eassumption; try lia; try reflexivity.
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
    intros until x31. intros I MU0 NBR HL OLDB OLDL OLDV LOCL OFFL NBL' OLDBO OLDLO OLDVO LOCO OFFO NBO' OLDBM OLDLM OLDVM LOCM OFFM NBM'.
    open_shb I. open_shh HY.
    zstep. uck. zstep. zstep. uck.
    zstep.
    zstep. if_cases K; zify_cond K.
    - assert (NZ : nbSeq = 0) by lia. subst nbSeq.
      eapply (sh_zero _ hl); [ | eassumption | lia].
      repeat (split; [first [eassumption | eexists; eassumption]|]). eassumption.
    - eapply (sh_b3c _ nbSeq hl TL bsL TO bsO TM bsM); try eassumption; try lia; try reflexivity.
      repeat (split; [first [eassumption | eexists; eassumption]|]). eassumption.
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
    intros until bsM. intros P0 P1 P2 P3 ELL EOF EML EWK H3 COLD NB SRCB STK MI
                             OLDB OLDL OLDV LOCL OFFL NBL' OLDBO OLDLO OLDVO LOCO OFFO NBO' OLDBM OLDLM OLDVM LOCM OFFM NBM'.
    open_shh HY. hide_all_disj.
    assert (MU : munch FOOT m m) by apply munch_refl.
    assert (MU0 : munch [(NBP, NBP + 4); (SPV - 544, SPV)] m m) by apply munch_refl.
    assert (WM : wmono usegs m m) by apply wmono_refl.
    zstep. carve_frame 96%nat STK.
    do 9 zstep.
    zstep. zstep. uck.
    zstep. zstep. zstep. zstep. uckz.
    zstep. zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      eapply (sh_ret _ llt mlt oft nb0 (2^64 - 72)); [ | lia | apply bv_eq; reflexivity | left; reflexivity].
      repeat (split; [first [eassumption | eexists; eassumption]|]). eassumption. }
    zstep. zstep. zstep. uck.
    zstep. uck.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mp end.
    set (b0 := Znth 0 src).
    pose proof (Forall_Znth _ _ 0 FBY ltac:(lia)) as B0R. cbv beta in B0R. fold b0 in B0R.
    pose proof (u8ro_read usegs mp SRC _ 0 _ (wa SRC) SRCB (nth_error_map_Znth (Z_to_bv 8) src 0 ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD0.
    fold b0 in RD0.
    zstep. cbv beta. rewrite (byte_lit b0) by lia.
    zstep. zstep. if_cases K1; zify_cond K1.
    - assert (B128 : 128 <= b0) by (rewrite Z.shiftl_mul_pow2, Z.mod_small in K1 by lia; lia).
      assert (SGN : bv_signed (Z_to_bv 64 (b0 ≪ 56)) ≫ 56 = b0 - 256).
      { rewrite bv_signed_hi by (rewrite unsigned_lit by (rewrite Z.shiftl_mul_pow2 by lia; lia); rewrite Z.shiftl_mul_pow2 by lia; lia).
        rewrite unsigned_lit by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
        replace (b0 * 2 ^ 56 - 2 ^ 64) with ((b0 - 256) * 2 ^ 56) by lia. apply Z.div_mul. lia. }
      zstep. rewrite SGN. zstep. zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        assert (B255 : b0 = 255) by lia.
        zstep. zstep. uck. zstep. zstep. if_cases K3; zify_cond K3.
        { eapply (sh_ret _ llt mlt oft nb0 (2^64 - 72)); [ | lia | apply bv_eq; reflexivity | left; reflexivity].
          repeat (split; [first [eassumption | eexists; eassumption]|]). eassumption. }
        zstep. zstep. uck.
        set (b1 := Znth 1 src). set (b2 := Znth 2 src).
        pose proof (Forall_Znth _ _ 1 FBY ltac:(lia)) as B1R. cbv beta in B1R. fold b1 in B1R.
        pose proof (Forall_Znth _ _ 2 FBY ltac:(lia)) as B2R. cbv beta in B2R. fold b2 in B2R.
        pose proof (u8ro_read usegs mp SRC _ 2 _ (wa (SRC + 2)) SRCB (nth_error_map_Znth (Z_to_bv 8) src 2 ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD2.
        fold b2 in RD2.
        zstep. cbv beta. rewrite (byte_lit b2) by lia.
        pose proof (u8ro_read usegs mp SRC _ 1 _ (wa (SRC + 1)) SRCB (nth_error_map_Znth (Z_to_bv 8) src 1 ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD1.
        fold b1 in RD1.
        zstep. cbv beta. rewrite (byte_lit b1) by lia.
        zstep. zstep. zstep. zstep. zstep. zstep.
        set (nbSeq := b2 * 256 + b1 + 32512).
        assert (EN : Z.lor (b2 ≪ 8 mod 18446744073709551616) b1 + 32512 = nbSeq).
        { rewrite Z.shiftl_mul_pow2, Z.mod_small by lia. rewrite (lor_add_disj 8) by (first [lia | apply Z_mod_mult]). reflexivity. }
        rewrite EN.
        assert (NBR : 32512 <= nbSeq <= 98047) by (subst nbSeq; lia). clearbody nbSeq. clear EN.
        zstep. zstep.
        eapply (sh_nb _ nb0 nbSeq 3 TL bsL TO bsO TM bsM); try eassumption; try lia; try reflexivity.
        repeat (split; [first [eassumption | eexists; eassumption]|]). eassumption.
      + (* [comment removed for export] *)
        assert (B254 : b0 <= 254) by lia.
        zstep. zstep. if_cases K3; zify_cond K3.
        { eapply (sh_ret _ llt mlt oft nb0 (2^64 - 72)); [ | lia | apply bv_eq; reflexivity | left; reflexivity].
          repeat (split; [first [eassumption | eexists; eassumption]|]). eassumption. }
        zstep. zstep. uck.
        set (b1 := Znth 1 src).
        pose proof (Forall_Znth _ _ 1 FBY ltac:(lia)) as B1R. cbv beta in B1R. fold b1 in B1R.
        pose proof (u8ro_read usegs mp SRC _ 1 _ (wa (SRC + 1)) SRCB (nth_error_map_Znth (Z_to_bv 8) src 1 ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD1.
        fold b1 in RD1.
        zstep. cbv beta. rewrite (byte_lit b1) by lia.
        zstep. zstep. zstep. zstep. zstep.
        set (nbSeq := (b0 - 128) * 256 + b1).
        assert (EN : Z.lor (b0 ≪ 8 mod 18446744073709551616) b1 + -32768 = nbSeq).
        { rewrite Z.shiftl_mul_pow2, Z.mod_small by lia. rewrite (lor_add_disj 8) by (first [lia | apply Z_mod_mult]). subst nbSeq. lia. }
        rewrite EN.
        assert (NBR : 0 <= nbSeq <= 98047) by (subst nbSeq; lia). clearbody nbSeq. clear EN.
        zstep.
        eapply (sh_nb _ nb0 nbSeq 2 TL bsL TO bsO TM bsM); try eassumption; try lia; try reflexivity.
        repeat (split; [first [eassumption | eexists; eassumption]|]). eassumption.
    - (* [comment removed for export] *)
      assert (B127 : b0 < 128) by (rewrite Z.shiftl_mul_pow2, Z.mod_small in K1 by lia; lia).
      eapply (sh_nb _ nb0 b0 1 TL bsL TO bsO TM bsM); try eassumption; try lia; try reflexivity.
      repeat (split; [first [eassumption | eexists; eassumption]|]). eassumption.
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
