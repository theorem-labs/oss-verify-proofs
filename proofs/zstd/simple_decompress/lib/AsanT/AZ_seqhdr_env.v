(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdSeqTable.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr Bytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit ZdTbl ZdDctxRep SepHide DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXSafe.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AZ_kit AZ_globals AZ_globalsR AZ_tbl AZ_kx
     AZ_fkit AZ_blk_iface AZ_blk_iface2 AZ_blk_iface3 AZ_bst_stk AZ_seqhdr_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation zlen l := (Z.of_nat (length l)).

Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC1. Context {rc : runConstT}.

Lemma sh_artcells_art : forall m, artcells m -> art m.
Proof.
  intros m (C0 & GOT & RIC & REAL & SHB & SUA & INI & LAY & _). unfold art.
  split; [exact GOT|]. split; [exact RIC|]. split; [exact SHB|]. split; [exact INI|]. split; [exact LAY| exact REAL].
Qed.

Section SHS.
Variable AI : AMallocIface.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.

Lemma ahull_sub : forall RNG (m : amem) A n A' n', ahull RNG m A n -> A <= A' -> A' + n' <= A + n -> ahull RNG m A' n'.
Proof.
  intros RNG m A n A' n' (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W0 & R) Ha Hb. exists RLO, RHI.
  repeat (split; [first [assumption | lia]|]). exact R.
Qed.

Lemma ahull_wmono : forall RNG (m m' : amem) X k, wmono bsegs m m' -> ahull RNG m X k -> ahull RNG m' X k.
Proof.
  intros RNG m m' X k WM (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W0 & R). exists RLO, RHI.
  do 6 (split; [assumption|]). split; [eapply wr_at_transport; [exact W0 | exact WM] | exact R].
Qed.

Lemma ffr_pres_weaken : forall W W' LB (m m' : amem), ffr_pres W LB m m' -> sub_fp W W' -> ffr_pres W' LB m m'.
Proof.
  intros W W' LB m m' H HS. unfold ffr_pres in *. eapply magree_mono; [exact H|].
  intros a [[IFa OW]|EX]; [left; split; [exact IFa| apply HS; exact OW] | right; exact EX].
Qed.

Lemma ainblk_sub : forall LB A n A' n', ainblk LB A n -> A <= A' -> A' + n' <= A + n -> ainblk LB A' n'.
Proof. intros LB A n A' n' (b & Hb & H1 & H2) Ha Hn. exists b. split; [exact Hb| lia]. Qed.

(* [comment removed for export] *)
Definition sh_hypsA (L : alayout) (RNG : footprint) (LB : list ablock) (SPV lo DCTX NBP SRC slen : Z) : Prop :=
  4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= NBP /\ NBP + 4 < 2^47 /\ 0 <= slen <= 1048576 /\ 4096 <= SRC /\ SRC + slen < 2^47
  /\ 4096 <= lo /\ lo <= SPV - 5248 /\ SPV < 2^47
  /\ (DCTX + 95992 <= lo \/ SPV <= DCTX) /\ (NBP + 4 <= lo \/ SPV <= NBP) /\ (SRC + slen <= lo \/ SPV <= SRC)
  /\ (DCTX + 95992 <= NBP \/ NBP + 4 <= DCTX) /\ (DCTX + 95992 <= SRC \/ SRC + slen <= DCTX) /\ (NBP + 4 <= SRC \/ SRC + slen <= NBP)
  /\ 0x625000 <= DCTX /\ 0x625000 <= NBP /\ 17594333495296 <= lo
  /\ DCTX mod 8 = 0
  (* [comment removed for export] *)
  /\ ashort LB 3 /\ astk RNG lo SPV /\ rng_fs L RNG /\ ATOP + 4096 <= lo /\ SPV + 16 < al_top L /\ SPV mod 16 = 0
  /\ rng RNG lo (al_top L - lo) /\ ablkLB LB
  /\ rng RNG DCTX 95992 /\ rng RNG (shad DCTX) (shspan DCTX 95992) /\ ainblk LB DCTX 95992
  /\ rng RNG NBP 4 /\ rng RNG (shad NBP) (shspan NBP 4) /\ ainblk LB NBP 4
  /\ (0 < slen -> rng RNG SRC slen /\ rng RNG (shad SRC) (shspan SRC slen) /\ ainimg LB SRC slen /\ ablk SRC (SRC + slen))
  /\ (DCTX + 95992 <= 0x7fff7000 \/ 0x10007fff8000 <= DCTX) /\ (NBP + 4 <= 0x7fff7000 \/ 0x10007fff8000 <= NBP)
  /\ ablk DCTX (DCTX + 95992) /\ ablk NBP (NBP + 4).

Ltac open_shhA HY := pose proof HY as (DCL & DCH & NBL & NBH & SLEN & SRCL & SRCH & LO0 & LOS & SPH & OFFD & OFFNB & OFFSRC & DNB & DSRC & NBSRC
                                        & DCA & NBA & KLO & D8 & ASH & AST & RFS & BOT & SPT & SP16 & RSTKT & LBH
                                        & RD & RDS & IBD & RNB & RNBS & IBN & SRCF & DCB & NBB & ABD & ABN);
                    hide_all_disj.

(* [comment removed for export] *)
Notation FOOTA L DCTX NBP SPV := ([(DCTX, DCTX + 24); (DCTX + 32, DCTX + 10296); (DCTX + 27324, DCTX + 29884); (NBP, NBP + 4); (SPV - 5248, SPV)] ++ fake_area L) (only parsing).
Notation W4 DCTX NBP := [(DCTX, DCTX + 24); (DCTX + 32, DCTX + 10296); (DCTX + 27324, DCTX + 29884); (NBP, NBP + 4)] (only parsing).

Definition SHBA (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word) (m : amem) (SPV lo DCTX NBP SRC : Z) (src : list Z)
    (huf pcs dsz bt stg le fe cold : word) (p0 p1 p2 nbw : word) (m1 : amem) : Prop :=
  rw_cells bsegs m1 DCTX [C8 p0] /\ rw_cells bsegs m1 (DCTX + 8) [C8 p1] /\ rw_cells bsegs m1 (DCTX + 16) [C8 p2]
  /\ rw_cells bsegs m1 (DCTX + 24) [C8 huf]
  /\ stk bsegs m1 (DCTX + 32) (DCTX + 4136) /\ stk bsegs m1 (DCTX + 4136) (DCTX + 6192) /\ stk bsegs m1 (DCTX + 6192) (DCTX + 10296)
  /\ stk bsegs m1 (DCTX + 27324) (DCTX + 29884)
  /\ rw_cells bsegs m1 (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 fe]
  /\ rw_cells bsegs m1 (DCTX + 30204) [C4 cold]
  /\ rw_cells bsegs m1 NBP [C4 nbw]
  /\ bytes_at bsegs m1 SRC (map (Z_to_bv 8) src)
  /\ stk bsegs m1 lo (SPV + -112)
  /\ (exists a b, rw_cells bsegs m1 (SPV + -112) [C8 a; C8 b; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
  /\ mem_inv bsegs m1 /\ munch (FOOTA L DCTX NBP SPV) m m1 /\ wmono bsegs m m1
  (* [comment removed for export] *)
  /\ AHEAP AI L RNG st LB m1 /\ ffr_pres (W4 DCTX NBP) LB m m1
  /\ unpoisoned m1 DCTX (DCTX + 95992) /\ unpoisoned m1 NBP (NBP + 4) /\ (0 < zlen src -> unpoisoned m1 SRC (SRC + zlen src))
  /\ (0 < zlen src -> ahull RNG m1 SRC (zlen src)) /\ aro_client RNG m1.

Ltac open_shbA I := destruct I as (P0 & P1 & P2 & P3 & ELL & EOF & EML & EWK & H3 & COLD & NB & SRCB & STK & (fa & fb & FR) & MI & MU & WM
                                   & AH & FFR & UD & UNB & USRC & HSRC & ROC).

(* [comment removed for export] *)
Section SH.
  Hypothesis FHL : fake_heap_law AI.
  Hypothesis HBST : zd_buildseq_stmtA AI rng_fs.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
            (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem)
            (SPV lo DCTX NBP SRC : Z) (src : list Z) (llt mlt oft huf pcs dsz bt stg le fe cold : word).
  Hypothesis HY : sh_hypsA L RNG LB SPV lo DCTX NBP SRC (zlen src).
  Hypothesis FBY : Forall (fun c => 0 <= c < 256) src.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Notation POST := (zd_seqhdr_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX NBP (zlen src) llt mlt oft huf lo m).
  Notation SHB := (SHBA L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m SPV lo DCTX NBP SRC src huf pcs dsz bt stg le fe cold).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -112)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition sh_resA (m1 : amem) (r : Z) (nbw p0 p1 p2 : word) : Prop :=
    zd_is_error r = true
    \/ (r <= zlen src /\ exists nbSeq, nbw = Z_to_bv 64 nbSeq /\ 0 <= nbSeq <= 98047 /\
        ((nbSeq = 0 /\ p0 = llt /\ p1 = mlt /\ p2 = oft /\ munch [(NBP, NBP + 4); (SPV - 5248, SPV)] m m1)
         \/ (nbSeq <> 0 /\
             seqhdr_tab m1 DCTX K_LL DCTX_entropy_LLTable APZD_LL_DEFAULT LL_defaultDTable p0 /\
             seqhdr_tab m1 DCTX K_OF DCTX_entropy_OFTable APZD_OF_DEFAULT OF_defaultDTable p2 /\
             seqhdr_tab m1 DCTX K_ML DCTX_entropy_MLTable APZD_ML_DEFAULT ML_defaultDTable p1))).

  (* [comment removed for export] *)
  Lemma sh_retA : forall m1 p0 p1 p2 nbw r xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31,
    SHB p0 p1 p2 nbw m1 -> 0 <= r < 2^64 -> sh_resA m1 r nbw p0 p1 p2 ->
    evtF bsegs RNG POST (ST 0x88bb8 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 r) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I HR RES. open_shbA I. open_shhA HY.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    kx_autoFLAx [KAApp (SPV - 112) 112] [] 30%nat
      [KZRange SPV (17594333495296 + 5248) (2^47); KZWr (SPV - 112) 112]
      [(SPV - 112, 112)] [(SPV - 112, 112)].
    all: try kx_z. all: try (kx_acc RSTKT).
    all: kx_mem.
    all: zstep.
    all: lazymatch goal with FRc : rw_cells _ ?mc (?S + -112) _, STc : stk _ ?mc ?l (?S + -112) |- _ => release_frame FRc STc S end.
    all: kx_mkR_fold.
    all: apply evtF_done; unfold zd_seqhdr_postA.
    all: lazymatch goal with |- context [MS _ _ _ _ _ ?mc _] => do 14 eexists; exists mc, r, p0, p1, p2, nbw end.
    all: split; [reflexivity|].
    all: split; [exact MU|]. all: split; [exact WM|]. all: split; [assumption|]. all: split; [assumption|].
    all: split; [exact FFR|]. all: split; [exact AH|].
    all: split.
    { unfold dctx_ptrs. change [C8 p0; C8 p1; C8 p2; C8 huf] with ([C8 p0] ++ [C8 p1] ++ [C8 p2] ++ [C8 huf]).
      apply rw_cells_app. split; [exact P0|]. cbn [cells_size csize Nat.add]. replace (DCTX + Z.of_nat 8) with (DCTX + 8) by lia.
      apply rw_cells_app. split; [exact P1|]. cbn [cells_size csize Nat.add]. replace (DCTX + 8 + Z.of_nat 8) with (DCTX + 16) by lia.
      apply rw_cells_app. split; [exact P2|]. cbn [cells_size csize Nat.add]. replace (DCTX + 16 + Z.of_nat 8) with (DCTX + 24) by lia. exact P3. }
    all: split; [eapply stk_merge; [eapply stk_merge; [exact ELL | exact EOF | lia] | exact EML | lia]|].
    all: split; [exact EWK|]. all: split; [exact NB|]. all: split; [exact HR| exact RES].
  Qed.

  (* [comment removed for export] *)
  Lemma sh_mlA : forall m1 p0 p1 p2 nbSeq i2 r2 tb T0 bs0 T2 bs2 TM bsM xra x5 x6 x7 xs4v xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31,
    SHB p0 p1 p2 (Z_to_bv 64 nbSeq) m1 ->
    1 <= nbSeq <= 98047 -> 0 <= tb < 256 -> 1 <= i2 -> 0 <= r2 -> i2 + r2 <= zlen src ->
    tab_infoA DCTX K_LL 32 APZD_LL_DEFAULT LL_defaultDTable p0 T0 bs0 -> bytes_at bsegs m1 T0 bs0 ->
    tab_infoA DCTX K_OF 4136 APZD_OF_DEFAULT OF_defaultDTable p2 T2 bs2 -> bytes_at bsegs m1 T2 bs2 ->
    bytes_at bsegs m1 TM bsM -> zlen bsM <= 4104 ->
    (Mem.sx32 fe <> Z_to_bv 64 0 -> tab_infoA DCTX K_ML 6192 APZD_ML_DEFAULT ML_defaultDTable p1 TM bsM) ->
    (TM = DCTX + 6192 \/ (TM + 4104 <= DCTX \/ DCTX + 30372 <= TM)) -> (TM + 4104 <= lo \/ SPV <= TM) -> (TM = DCTX + 6192 \/ TM + 4104 <= 0x30000) ->
    xs4v = Z_to_bv 64 nbSeq ->
    evtF bsegs RNG POST (ST 0x88a4c m1 xra x5 x6 x7 (Z_to_bv 64 (DCTX + 30204)) (Z_to_bv 64 (DCTX + 30004))
                       (Z_to_bv 64 r2) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + zlen src)) xs4v (Z_to_bv 64 SRC) (Z_to_bv 64 tb) (Z_to_bv 64 (DCTX + 27324))
                       (Z_to_bv 64 (2147450880 + (DCTX + 30004) / 8)) (Z_to_bv 64 (2147450880 + (DCTX + 30204) / 8)) (Z_to_bv 64 DCTX)
                       x28 x29 x30 x31).
  Proof.
    intros until x31. intros I NBR TBR I2 R2 IR TI0 TB0 TI2 TB2 OLDB OLDL OLDV LOCM OFFM IMGM ->. open_shbA I. open_shhA HY.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (tab_infoA_len _ _ _ _ _ _ _ _ TI0) as LEN0. pose proof (tab_infoA_len _ _ _ _ _ _ _ _ TI2) as LEN2.
    cbn [kind_maxLog] in LEN0, LEN2. change (2^9) with 512 in LEN0. change (2^8) with 256 in LEN2.
    (* [comment removed for export] *)
    hide MU. hide TB0. hide TB2. hide OLDB. hide FFR.
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = zlen src) by (rewrite length_map; reflexivity).
    assert (MUr : munch [(SPV - 112, SPV - 96)] m1 m1) by apply munch_refl.
    assert (WMr : wmono bsegs m1 m1) by apply wmono_refl.
    kx_autoFLAx [KAUnp DCTX 95992; KAShp (2147450880 + (DCTX + 30004) / 8) (DCTX + 30004); KAShp (2147450880 + (DCTX + 30204) / 8) (DCTX + 30204);
               KAApp (SPV - 112) 16]
      [0x88bb8] 60%nat
      [KZRange SPV (17594333495296 + 5248) (2^47); KZRange DCTX 0x625000 (2^47 - 95992); KZRange SRC 4096 (2^47); KZRange NBP 0x625000 (2^47 - 4);
       KZRange i2 0 1048576; KZRange r2 0 1048576; KZRange (zlen src) 0 1048576; KZRange tb 0 255; KZRange nbSeq 1 98047; KZAlign DCTX 8;
       KZWr (SPV - 112) 16; KZDisj (SPV - 112) 16 DCTX 95992; KZDisj (SPV - 112) 16 NBP 4; KZDisj (SPV - 112) 16 SRC (zlen src)]
      [(SPV - 112, 112); (DCTX + 29976, 32); (DCTX + 30204, 4)] [(SPV - 112, 112); (DCTX, 95992)].
    all: try kx_cell_lit. all: try kx_z. all: try (kx_acc RSTKT).
    all: match goal with |- evtF _ _ _ _ => idtac | |- _ => repeat split; try lia; unfold off_stack, apart in *; sep_solve end.
    all: kx_mem.
    (* [comment removed for export] *)
    all: lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned (edenot ?E (EExt true 0 4 (EVar ?j))))] =>
           let H := fresh "T5E" in
           assert (H : Z_to_bv 64 (bv_unsigned (edenot E (EExt true 0 4 (EVar j)))) = Mem.sx32 fe)
             by (rewrite Z_to_bv_bv_unsigned; cbn [edenot]; rewrite (KXA j) by (cbn; lia); cbn [znth nth Z.to_nat Pos.to_nat];
                 unfold ext_val, ext_Z, Mem.sx32; rewrite Z_to_bv_bv_unsigned; apply Zbv_eq_mod;
                 unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296;
                 change (2 ^ Z.of_N (32 - 1)) with 2147483648; change (2 ^ (8 * Z.of_nat 0)) with 1; change (2 ^ (8 * Z.of_nat 4)) with 4294967296;
                 rewrite Z.div_1_r; pose proof (bv_unsigned_in_range 64 fe); Z.div_mod_to_equations; lia);
           rewrite H
         end.
    all: kx_abs.
    (* [comment removed for export] *)
    set (i3 := i2 + r2) in *.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mq end.
    replace (r2 + (SRC + i2)) with (SRC + i3) by lia.
    replace (-1 * r2 + (-1 * i2 + zlen src)) with (zlen (skipn (Z.to_nat i3) src)) by (rewrite length_skipn; lia).
    assert (LSK : zlen (skipn (Z.to_nat i3) src) = zlen src - i3) by (rewrite length_skipn; lia).
    assert (FSK : Forall (fun c => 0 <= c < 256) (skipn (Z.to_nat i3) src)).
    { pose proof FBY as FB. rewrite <- (firstn_skipn (Z.to_nat i3) src) in FB. apply Forall_app in FB. exact (proj2 FB). }
    pose proof (abytes_at_skipn _ _ _ i3 SRCB ltac:(lia)) as SRC3.
    assert (TYR : 0 <= (1152921504606846976 * tb) mod 2 ^ 64 / 4611686018427387904 <= 3).
    { pose proof (Z.mod_pos_bound (1152921504606846976 * tb) (2^64) ltac:(lia)) as MB.
      split; [apply Z.div_pos; lia|].
      assert (X4 : (1152921504606846976 * tb) mod 2 ^ 64 / 4611686018427387904 < 4) by (apply Z.div_lt_upper_bound; lia). lia. }
    assert (AH1 : AHEAP AI L RNG st LB mq).
    { eapply (AI_frame AI); [exact AH| exact MUr| exact WMr|]. constructor; [| constructor]. left; left. cbn. lia. }
    assert (ART1 : art mq) by (apply sh_artcells_art; exact (AI_rtcells AI _ _ _ _ _ AH1)).
    assert (DSH : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(SPV - 112, SPV - 96)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb. cbn [disjoint_from]. split; [| exact I]. left. rewrite !shad_div. unfold ASHOFF in *. clear - X0 Hn Hb KLO LOS. Z.div_mod_to_equations. lia. }
    assert (UD1 : unpoisoned mq DCTX (DCTX + 95992)) by (eapply unpoisoned_munch; [exact UD| exact MUr| apply DSH; lia]).
    assert (UNB1 : unpoisoned mq NBP (NBP + 4)) by (eapply unpoisoned_munch; [exact UNB| exact MUr| apply DSH; lia]).
    assert (ROC1 : aro_client RNG mq).
    { eapply aro_client_transport; [exact ROC| exact MUr| exact WMr|]. constructor; [| constructor]. right. cbn. unfold KHIGH. lia. }
    pose proof (aro_tables _ _ ROC1) as (_ & _ & _ & _ & _ & _ & OBASE & OBITS & ODFLT).
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?c2 :: ?rest) => change (c1 :: c2 :: rest) with ([c1; c2] ++ rest) in FR end.
    apply rw_cells_app in FR. destruct FR as [ARGS FRR]. cbn [cells_size csize Nat.add] in FRR.
    replace (SPV + -112 + Z.of_nat 16) with (SPV + -96) in FRR by lia.
    destruct AST as (KLO' & RSTK & RIMG).
    assert (AFP : afpre AI rng_fs L RNG st LB mq lo (SPV + -112) 3).
    { split; [exact AH1|]. split; [exact ASH|]. split; [exact ART1|]. split; [split; [exact KLO'| split; [eapply rng_sub'; [exact RSTK| lia]| exact RIMG]]|].
      split; [exact RFS|]. split; [exact BOT|]. split; [lia|]. split; [clear - SP16; Z.div_mod_to_equations; lia|]. split; [exact RSTKT| exact LBH]. }
    (* [comment removed for export] *)
    pose proof (zd_buildseq_stkA AI rng_fs HBST) as BS. change (Z_to_bv 64 562804) with (Z_to_bv 64 APZD_BUILDSEQ).
    eapply evtF_cut; [ eapply BS with (SPV := SPV + -112) (lo := lo) (DTS := DCTX + 6192) (DTP := DCTX + 8) (SRC := SRC + i3) (W := DCTX + 27324)
        (DFLT := APZD_ML_DEFAULT) (BASE := APML_BASE) (BITS := APML_BITS) (ty := (1152921504606846976 * tb) mod 2 ^ 64 / 4611686018427387904)
        (wlen := 2560) (k := K_ML) (srcb := skipn (Z.to_nat i3) src) (oldp := p1) (nbw := Z_to_bv 64 nbSeq) (L := L) (st := st) (LB := LB);
      first [ eassumption | reflexivity
            | replace (DCTX + 6192 + (8 + 8 * 2 ^ kind_maxLog K_ML)) with (DCTX + 10296) by (cbn [kind_maxLog]; lia); exact EML
            | replace (DCTX + 27324 + 2560) with (DCTX + 29884) by lia; exact EWK
            | apply apml_base_at; assumption | apply apml_bits_at; assumption
            | intros Hfz; destruct (OLDV Hfz) as (tq & -> & _ & _ & [-> | [-> _]]); rewrite unsigned_lit by (unfold APZD_ML_DEFAULT; lia); unfold APZD_ML_DEFAULT; lia   (* [comment removed for export] *)
            | idtac ] | ].
    all: cbn [kind_maxLog].
    all: try lazymatch goal with
         | |- aregU _ _ ?A ?n =>
                 destruct (SRCF ltac:(lia)) as (Q1 & Q2 & Q3 & Q4);
                     split; [eapply ablk_sub; [exact Q4| lia| lia]|];
                     split; [eapply unpoisoned_sub; [eapply unpoisoned_munch; [eapply USRC; lia| exact MUr| apply DSH; lia]| lia| lia]|];
                     split; [eapply rng_sub'; [exact Q1| lia]|];
                     pose proof (shspan_sub SRC (zlen src) A n ltac:(lia) ltac:(lia) ltac:(lia)) as SS; eapply rng_sub'; [exact Q2| lia]
         | |- areg _ _ ?A ?n =>
             first [ (* [comment removed for export] *)
                     intros _; split; [eapply ablk_sub; [exact ABD| lia| lia]|];
                     split; [eapply unpoisoned_sub; [exact UD1| lia| lia]|];
                     split; [eapply rng_sub'; [exact RD| lia]|];
                     pose proof (shspan_sub DCTX 95992 A n ltac:(lia) ltac:(lia) ltac:(lia)) as SS; eapply rng_sub'; [exact RDS| lia]
                   | (* [comment removed for export] *)
                     intros Hn; destruct (SRCF ltac:(lia)) as (Q1 & Q2 & Q3 & Q4);
                     split; [eapply ablk_sub; [exact Q4| lia| lia]|];
                     split; [eapply unpoisoned_sub; [eapply unpoisoned_munch; [eapply USRC; lia| exact MUr| apply DSH; lia]| lia| lia]|];
                     split; [eapply rng_sub'; [exact Q1| lia]|];
                     pose proof (shspan_sub SRC (zlen src) A n ltac:(lia) ltac:(lia) ltac:(lia)) as SS; eapply rng_sub'; [exact Q2| lia] ]
         | |- ainblk _ ?A ?n => eapply ainblk_sub; [exact IBD| lia| lia]
         | |- 0 < _ -> ainimg _ _ _ => intros Hn; destruct (SRCF ltac:(lia)) as (Q1 & Q2 & Q3 & Q4); eapply ainimg_sub; [exact Q3| lia| lia]
         | |- ahull _ _ _ _ => eapply ahull_sub; [eapply ahull_wmono; [exact WMr| eapply HSRC; lia]| lia| lia]
         | |- 0 < _ -> ahull _ _ _ _ => intros Hn; eapply ahull_sub; [eapply ahull_wmono; [exact WMr| eapply HSRC; lia]| lia| lia]
         | |- ainimg _ _ _ => first [ destruct (SRCF ltac:(lia)) as (Q1 & Q2 & Q3 & Q4); eapply ainimg_sub; [exact Q3| lia| lia] | right; cbn; unfold APML_BASE, APML_BITS, AIMG_HI; lia ]
         | |- _ <= AIMG_HI => cbn; unfold APML_BASE, APML_BITS, AIMG_HI; lia
         | |- forall _, _ => idtac
         | |- _ => unfold APML_BASE, APML_BITS, APZD_ML_DEFAULT, off_stack, apart; first [lia | sep_solve | unhide; lia]
         end.
    (* [comment removed for export] *)
    cbv beta. intros ms' PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mc & rr & pv & -> & MUc & WMc & MIc & STKc & FFRc & AHc & DTSc & WKc & DTPc & FRAMEc & RR & RESc).
    replace (ret_pc (Z_to_bv 64 559804)) with (Z_to_bv 64 559804) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [kind_maxLog] in MUc, FFRc, DTSc, FRAMEc, RESc.
    replace (DCTX + 6192 + (8 + 8 * 2 ^ 9)) with (DCTX + 10296) in * by lia.
    replace (DCTX + 8 + 8) with (DCTX + 16) in * by lia.
    replace (DCTX + 27324 + 2560) with (DCTX + 29884) in * by lia.
    pose proof (AI_layout AI _ _ _ _ _ AHc) as (_ & _ & _ & _ & _ & _ & FKLO & FKHI).
    assert (FFRc4 : ffr_pres [(DCTX + 6192, DCTX + 10296); (DCTX + 8, DCTX + 16); (DCTX + 27324, DCTX + 29884); (SPV + -112 - 5136, SPV + -112)] LB mq mc).
    { eapply ffr_pres_weaken; [exact FFRc|]. unfold sub_fp. cbn [outside]. intros x Hx. tauto. }
    (* [comment removed for export] *)
    assert (DJ : forall X n, 0 <= n -> DCTX <= X -> (X + n <= DCTX + 8 \/ DCTX + 16 <= X) -> (X + n <= DCTX + 6192 \/ DCTX + 10296 <= X) ->
                 (X + n <= DCTX + 27324 \/ DCTX + 29884 <= X) -> X + n <= DCTX + 95992 ->
                 disjoint_from [(DCTX + 6192, DCTX + 10296); (DCTX + 8, DCTX + 16); (DCTX + 27324, DCTX + 29884); (SPV + -112 - 5136, SPV + -112)] X n).
    { intros X n Hn G0 G1 G2 G3 G4. cbn [disjoint_from]. pose proof OFFD as OFFD'; unfold hidden in OFFD'. repeat split; lia. }
    assert (P0c : rw_cells bsegs mc DCTX [C8 p0]).
    { eapply (shc_cells_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| cbn; lia| cbn; lia]| apply DJ; cbn; lia| exact MUc| exact WMc| exact FFRc4| exact P0]. }
    assert (P2c : rw_cells bsegs mc (DCTX + 16) [C8 p2]).
    { eapply (shc_cells_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| cbn; lia| cbn; lia]| apply DJ; cbn; lia| exact MUc| exact WMc| exact FFRc4| exact P2]. }
    assert (P3c : rw_cells bsegs mc (DCTX + 24) [C8 huf]).
    { eapply (shc_cells_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| cbn; lia| cbn; lia]| apply DJ; cbn; lia| exact MUc| exact WMc| exact FFRc4| exact P3]. }
    assert (H3c : rw_cells bsegs mc (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 fe]).
    { eapply (shc_cells_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| cbn; lia| cbn; lia]| apply DJ; cbn; lia| exact MUc| exact WMc| exact FFRc4| exact H3]. }
    assert (COLDc : rw_cells bsegs mc (DCTX + 30204) [C4 cold]).
    { eapply (shc_cells_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| cbn; lia| cbn; lia]| apply DJ; cbn; lia| exact MUc| exact WMc| exact FFRc4| exact COLD]. }
    assert (ELLc : stk bsegs mc (DCTX + 32) (DCTX + 4136)).
    { eapply (shc_stk_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| lia| lia]| apply DJ; lia| exact MUc| exact WMc| exact FFRc4| exact ELL]. }
    assert (EOFc : stk bsegs mc (DCTX + 4136) (DCTX + 6192)).
    { eapply (shc_stk_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| lia| lia]| apply DJ; lia| exact MUc| exact WMc| exact FFRc4| exact EOF]. }
    assert (DJN : disjoint_from [(DCTX + 6192, DCTX + 10296); (DCTX + 8, DCTX + 16); (DCTX + 27324, DCTX + 29884); (SPV + -112 - 5136, SPV + -112)] NBP 4).
    { cbn [disjoint_from]. pose proof OFFNB as X1; unfold hidden in X1. pose proof DNB as X2; unfold hidden in X2. repeat split; lia. }
    assert (NBc : rw_cells bsegs mc NBP [C4 (Z_to_bv 64 nbSeq)]).
    { eapply (shc_cells_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBN| cbn; lia| cbn; lia]| exact DJN| exact MUc| exact WMc| exact FFRc4| exact NB]. }
    (* [comment removed for export] *)
    assert (DJF : disjoint_from ([(DCTX + 6192, DCTX + 10296); (DCTX + 8, DCTX + 16); (DCTX + 27324, DCTX + 29884); (SPV + -112 - 5136, SPV + -112)] ++ fake_area L) (SPV + -112) 112).
    { pose proof OFFD as X1; unfold hidden in X1. unfold fake_area, FAKESZ. cbn [disjoint_from app]. rewrite !shad_div. unfold ASHOFF.
      repeat split; first [lia | clear - FKHI BOT LOS KLO ATR; Z.div_mod_to_equations; lia]. }
    assert (FRc : rw_cells bsegs mc (SPV + -112) ([C8 (Z_to_bv 64 nbSeq); C8 (Z_to_bv 64 (DCTX + 27324))] ++ [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { eapply rw_cells_transport; [| exact MUc| exact WMc| exact DJF]. apply rw_cells_app. split; [exact ARGS|]. cbn [cells_size csize Nat.add].
      replace (SPV + -112 + Z.of_nat 16) with (SPV + -96) by lia. exact FRR. }
    cbn [app] in FRc.
    (* [comment removed for export] *)
    assert (SRCc : bytes_at bsegs mc SRC (map (Z_to_bv 8) src)).
    { destruct (Z.eq_dec (zlen src) 0) as [Z0|Zp].
      - destruct SRCB as (B0 & B1 & _). split; [exact B0|]. split; [exact B1|]. intros i Hi. rewrite length_map in Hi. lia.
      - destruct (SRCF ltac:(lia)) as (Q1 & Q2 & [Q3|Q3] & Q4).
        + eapply (shc_bytes_pres AI FHL); [exact AH1| rewrite length_map; exact Q3| | exact MUc| exact FFRc4| exact SRCB].
          rewrite length_map. cbn [disjoint_from]. pose proof OFFSRC as X1; unfold hidden in X1. pose proof DSRC as X2; unfold hidden in X2. repeat split; lia.
        + eapply bytes_at_transport; [exact SRCB| exact MUc|]. rewrite length_map. unfold fake_area, FAKESZ, AIMG_HI in *. cbn [disjoint_from app].
          rewrite !shad_div. unfold ASHOFF. repeat split; first [lia | clear - Q3 FKLO SRCL; Z.div_mod_to_equations; lia]. }
    (* [comment removed for export] *)
    assert (AAW : aappW [(DCTX + 6192, DCTX + 10296); (DCTX + 8, DCTX + 16); (DCTX + 27324, DCTX + 29884); (SPV + -112 - 5136, SPV + -112)]).
    { pose proof DCB as X1; unfold hidden in X1. unfold aappW, KLOW, KHIGH. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    assert (UDc : unpoisoned mc DCTX (DCTX + 95992)).
    { eapply (shc_unp_pres AI FHL); [exact AH1| exact IBD| lia| unfold KEND; lia| exact AAW| exact MUc| exact FFRc4| exact UD1]. }
    assert (UNBc : unpoisoned mc NBP (NBP + 4)).
    { eapply (shc_unp_pres AI FHL); [exact AH1| exact IBN| lia| unfold KEND; lia| exact AAW| exact MUc| exact FFRc4| exact UNB1]. }
    assert (USRCc : 0 < zlen src -> unpoisoned mc SRC (SRC + zlen src)).
    { intros Zp. destruct (SRCF ltac:(lia)) as (Q1 & Q2 & [Q3|Q3] & Q4).
      - eapply (shc_unp_pres AI FHL); [exact AH1| exact Q3| lia| unfold KEND; lia| exact AAW| exact MUc| exact FFRc4|].
        eapply unpoisoned_munch; [eapply USRC; lia| exact MUr| apply DSH; lia].
      - eapply unpoisoned_munch; [eapply unpoisoned_munch; [eapply USRC; lia| exact MUr| apply DSH; lia]| exact MUc|].
        pose proof (proj1 (FHL _ _ _ _ _ AHc)) as AFB. unfold ablk, AIMG_HI, KLS in AFB.
        unfold fake_area, FAKESZ, AIMG_HI in *. cbn [disjoint_from app]. rewrite !shad_div. unfold ASHOFF. pose proof DCB as X1; unfold hidden in X1.
        repeat split; (clear - Q3 FKLO SRCL Zp X1 DCA KLO LOS AFB ATR; Z.div_mod_to_equations; lia). }
    assert (HSRCc : 0 < zlen src -> ahull RNG mc SRC (zlen src)) by (intros Zp; eapply ahull_wmono; [exact WMc| eapply ahull_wmono; [exact WMr| exact (HSRC Zp)]]).
    assert (ROCc : aro_client RNG mc) by (eapply aro_client_transport_F; [exact ROC1| exact MUc| exact WMc| exact AAW| exact (proj1 (FHL _ _ _ _ _ AHc))]).
    (* [comment removed for export] *)
    unfold hidden in MU. unfold hidden in FFR.
    assert (MUq : munch (FOOTA L DCTX NBP SPV) m mq).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUr]. unfold sub_fp. cbn [outside app]. intros x Hx. repeat split; lia. }
    assert (MUt : munch (FOOTA L DCTX NBP SPV) m mc).
    { eapply munch_trans; [exact MUq|]. eapply munch_weaken; [| exact MUc]. unfold sub_fp, fake_area. cbn [outside app]. intros x Hx. repeat split; try lia; tauto. }
    first [assert (WMt : wmono bsegs m mc) by (eapply wmono_trans; [exact WM| exact WMc]) | assert (WMt : wmono bsegs m mc) by (eapply wmono_trans; [eapply wmono_trans; [exact WM| exact WMr]| exact WMc])].
    assert (FFRq : ffr_pres [] LB m1 mq).
    { eapply (fk_ffr_stack AI); [exact AH| exact MUr| exact WMr|]. constructor; [cbn; lia| constructor]. }
    assert (FFRt : ffr_pres (W4 DCTX NBP) LB m mc).
    { eapply ffr_pres_trans; [exact FFR|]. eapply ffr_pres_trans; [eapply ffr_pres_weaken; [exact FFRq| unfold sub_fp; cbn; intros; exact I]|].
      eapply ffr_pres_weaken; [exact FFRc|]. unfold sub_fp. cbn [outside]. intros x Hx. repeat split; lia. }
    (* [comment removed for export] *)
    unfold hidden in TB0. unfold hidden in TB2. unfold hidden in OLDB.
    pose proof OFFD as OFFD1. unfold hidden in OFFD1.
    assert (SHT0 : seqhdr_tab mc DCTX K_LL DCTX_entropy_LLTable APZD_LL_DEFAULT LL_defaultDTable p0).
    { destruct TI0 as (tL & EpL & EbL & OKL & [TL0 | [TL0 EtL]]).
      - exists T0, tL. split; [exact EpL|]. split; [left; exact TL0|]. split; [|exact OKL]. rewrite <- EbL.
        assert (B1 : bytes_at bsegs mq T0 bs0).
        { eapply bytes_at_transport; [exact TB0| exact MUr|]. cbn [disjoint_from]. split; [|exact I]. clear - TL0 LEN0 OFFD1 LOS DCL. lia. }
        eapply (shc_bytes_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| lia| lia]| apply DJ; lia| exact MUc| exact FFRc4| exact B1].
      - exists T0, tL. split; [exact EpL|]. split; [right; split; assumption|]. split; [|exact OKL]. rewrite TL0, EtL. exact (all_default_at mc MIc). }
    assert (SHT2 : seqhdr_tab mc DCTX K_OF DCTX_entropy_OFTable APZD_OF_DEFAULT OF_defaultDTable p2).
    { destruct TI2 as (tO & EpO & EbO & OKO & [TO0 | [TO0 EtO]]).
      - exists T2, tO. split; [exact EpO|]. split; [left; exact TO0|]. split; [|exact OKO]. rewrite <- EbO.
        assert (B2 : bytes_at bsegs mq T2 bs2).
        { eapply bytes_at_transport; [exact TB2| exact MUr|]. cbn [disjoint_from]. split; [|exact I]. clear - TO0 LEN2 OFFD1 LOS DCL. lia. }
        eapply (shc_bytes_pres AI FHL); [exact AH1| eapply ainblk_sub; [exact IBD| lia| lia]| apply DJ; lia| exact MUc| exact FFRc4| exact B2].
      - exists T2, tO. split; [exact EpO|]. split; [right; split; assumption|]. split; [|exact OKO]. rewrite TO0, EtO. exact (aof_default_at mc MIc). }
    assert (SHI : SHB p0 pv p2 (Z_to_bv 64 nbSeq) mc).
    { split; [exact P0c|]. split; [exact DTPc|]. split; [exact P2c|]. split; [exact P3c|]. split; [exact ELLc|]. split; [exact EOFc|]. split; [exact DTSc|].
      split; [exact WKc|]. split; [exact H3c|]. split; [exact COLDc|]. split; [exact NBc|]. split; [exact SRCc|]. split; [exact STKc|].
      split; [eexists; eexists; exact FRc|]. split; [exact MIc|]. split; [exact MUt|]. split; [exact WMt|].
      split; [exact AHc|]. split; [exact FFRt|]. split; [exact UDc|]. split; [exact UNBc|]. split; [exact USRCc|]. split; [exact HSRCc| exact ROCc]. }
    (* [comment removed for export] *)
    destruct RESc as [ER | (RL & RES3)].
    - (* [comment removed for export] *) unfold zd_is_error, ZE_maxCode in ER. apply Z.ltb_lt in ER.
      kx_autoFLAx [] [0x88bb8] 12%nat
        [KZRange rr (2^64 - 119) (2^64 - 1); KZRange i3 0 1048576; KZRange SRC 4096 (2^47); KZRange (zlen src) 0 1048576]
        [] [].
      all: try kx_z.
      all: kx_mem.
      eapply (sh_retA mc p0 pv p2 (Z_to_bv 64 nbSeq) 18446744073709551596); [exact SHI| lia| left; reflexivity].
    - kx_autoFLAx [] [0x88bb8] 12%nat
        [KZRange rr 0 1048576; KZRange i3 0 1048576; KZRange SRC 4096 (2^47); KZRange (zlen src) 0 1048576]
        [] [].
      all: try kx_z.
      all: kx_mem.
      assert (SHTM : seqhdr_tab mc DCTX K_ML DCTX_entropy_MLTable APZD_ML_DEFAULT ML_defaultDTable pv).
      { destruct RES3 as [(T0' & ->) | [(T3 & FRN & -> & SAME) | (T12 & -> & t & TOK & TB)]].
        - exists APZD_ML_DEFAULT, ML_defaultDTable. split; [reflexivity|]. split; [right; split; reflexivity|]. split; [exact (aml_default_at mc MIc)| exact ML_default_ok].
        - destruct (OLDV FRN) as (tM & EpM & EbM & OKM & [TM0 | [TM0 EtM]]).
          + exists TM, tM. split; [exact EpM|]. split; [left; exact TM0|]. split; [|exact OKM]. rewrite <- EbM. rewrite TM0. apply SAME; [| lia].
            rewrite <- TM0. eapply bytes_at_transport; [exact OLDB| exact MUr|]. cbn [disjoint_from]. split; [|exact I]. clear - TM0 OLDL OFFD1 LOS DCL. lia.
          + exists TM, tM. split; [exact EpM|]. split; [right; split; assumption|]. split; [|exact OKM]. rewrite TM0, EtM. exact (aml_default_at mc MIc).
        - exists (DCTX + 6192), t. split; [reflexivity|]. split; [left; reflexivity|]. split; [exact TB| exact TOK]. }
      eapply (sh_retA mc p0 pv p2 (Z_to_bv 64 nbSeq) (rr + i3)); [exact SHI| lia|].
      right. split; [lia|]. exists nbSeq. split; [reflexivity|]. split; [lia|]. right. split; [lia|].
      split; [exact SHT0|]. split; [exact SHT2| exact SHTM].
  Qed.

End SH.
End SHS.
End CANSEC1.
