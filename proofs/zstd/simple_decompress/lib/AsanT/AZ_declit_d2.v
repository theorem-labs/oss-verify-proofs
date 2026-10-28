(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdLit.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit ZdFrameW ZdWalkKit ZdCellKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_globals AZ_globalsR AZ_frame_iface AZ_huf_iface AZ_block_iface AZ_blk_iface4 AZ_blk_iface5 AZ_libc_iface AZ_hufinv AZ_kx AZ_declit_a AZ_declit_b.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation zlen l := (Z.of_nat (length l)).
Notation SHB := 2147450880.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma dl_stk_bytes_u8arr : forall (m1 : amem) a (bs : list byte), stk bsegs m1 a (a + Z.of_nat (length bs)) -> bytes_at bsegs m1 a bs -> u8arr bsegs m1 a bs.
Proof.
  intros m1 a bs (S0 & S1 & SW) BA. split; [exact BA|]. split; [lia|]. split; [lia|]. intros i Hi. apply (SW (a + i)). lia.
Qed.
Lemma dl_u8arr_stk : forall (m1 : amem) a (bs : list byte), u8arr bsegs m1 a bs -> stk bsegs m1 a (a + Z.of_nat (length bs)).
Proof.
  intros m1 a bs U. apply rw_cells_of_u8arr in U. apply stk_of_rw_cells in U. cbn [cells_size csize] in U. rewrite Nat.add_0_r in U. exact U.
Qed.
Lemma dl_disjoint_from_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[x y] W IH]; intros a n a' n' D H1 H2; cbn in *; [exact I|].
  destruct D as [D1 D2]. split; [lia| exact (IH _ _ _ _ D2 H1 H2)].
Qed.

(* [comment removed for export] *)
Section FC.
Variable AI : AMallocIface.
Hypothesis FHL : fake_heap_law AI.
Lemma dl_fcall_bytes_pres : forall L RNG st LB m0 (m m' : amem) W X bs,
  AHEAP AI L RNG st LB m0 -> ainblk LB X (zlen bs) -> disjoint_from W X (zlen bs) ->
  munch (W ++ fake_area L) m m' -> ffr_pres W LB m m' -> bytes_at bsegs m X bs -> bytes_at bsegs m' X bs.
Proof.
  intros L RNG st LB m0 m m' W X bs AH (b & Hb & H1 & H2) DJ MU FP B.
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [DF _].
    eapply bytes_at_transport; [exact B| exact MU|]. apply disjoint_from_app2; [exact DJ| eapply dl_disjoint_from_sub; [exact DF| lia| lia]].
  - eapply bytes_at_magree; [exact FP| exact B|]. intros a Ha. left. split.
    + exists c, A, n. split; [exact Hb| lia].
    + eapply disjoint_outside; [exact DJ| lia].
Qed.
Lemma dl_fcall_cells_pres : forall L RNG st LB m0 (m m' : amem) W X cs,
  AHEAP AI L RNG st LB m0 -> ainblk LB X (Z.of_nat (cells_size cs)) -> disjoint_from W X (Z.of_nat (cells_size cs)) ->
  munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> ffr_pres W LB m m' -> rw_cells bsegs m X cs -> rw_cells bsegs m' X cs.
Proof.
  intros L RNG st LB m0 m m' W X cs AH IB DJ MU WM FP [[Hwf HB] HW]. split; [split; [exact Hwf|]|].
  - eapply dl_fcall_bytes_pres; [exact AH| rewrite cells_bytes_length by assumption; exact IB| rewrite cells_bytes_length by assumption; exact DJ| exact MU| exact FP| exact HB].
  - eapply wr_at_transport; [exact HW| exact WM].
Qed.
Lemma dl_fcall_stk_pres : forall L RNG st LB m0 (m m' : amem) W lo hi,
  AHEAP AI L RNG st LB m0 -> ainblk LB lo (hi - lo) -> disjoint_from W lo (hi - lo) ->
  munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> ffr_pres W LB m m' -> stk bsegs m lo hi -> stk bsegs m' lo hi.
Proof.
  intros L RNG st LB m0 m m' W lo hi AH (b & Hb & H1 & H2) DJ MU WM FP ST.
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [DF _].
    eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. apply disjoint_from_app2; [exact DJ| eapply dl_disjoint_from_sub; [exact DF| lia| lia]].
  - eapply stk_magree; [exact FP| exact ST|]. intros a Ha. left. split.
    + exists c, A, n. split; [exact Hb| lia].
    + eapply disjoint_outside; [exact DJ| lia].
Qed.
Lemma dl_fcall_unp_pres : forall L RNG st LB m0 (m m' : amem) W X k,
  AHEAP AI L RNG st LB m0 -> ainblk LB X k -> 0 < k -> X + k <= KEND -> aappW W ->
  munch (W ++ fake_area L) m m' -> ffr_pres W LB m m' -> unpoisoned m X (X + k) -> unpoisoned m' X (X + k).
Proof.
  intros L RNG st LB m0 m m' W X k AH (b & Hb & H1 & H2) Hk XH HW MU FP U.
  pose proof U as (U0 & U1 & _).
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [_ DSF].
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hb) as (N & (BR & _) & _). pose proof (ablk_lin _ _ BR) as (L1 & L2 & L3 & L4).
    eapply unpoisoned_munch; [exact U| exact MU|]. apply disjoint_from_app2.
    + apply aappW_shadow_disjoint; [exact HW| | | |]; rewrite ?shad_div; unfold ASHOFF, KEND in *; Z.div_mod_to_equations; lia.
    + eapply dl_disjoint_from_sub; [exact DSF| |]; unfold shspan; rewrite ?shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
  - eapply unpoisoned_agree; [exact U|]. intros s Hs.
    set (a' := Z.max X (8 * (s - ASHOFF))).
    assert (Ra : X <= a' < X + k).
    { subst a'. rewrite !shad_div in Hs. unfold ASHOFF in *. destruct (Z.max_spec X (8 * (s - 2147450880))) as [[Hm ->]|[Hm ->]]; Z.div_mod_to_equations; lia. }
    assert (Ea : shad a' = s).
    { subst a'. rewrite !shad_div in Hs. rewrite shad_div. unfold ASHOFF in *. destruct (Z.max_spec X (8 * (s - 2147450880))) as [[Hm ->]|[Hm ->]]; Z.div_mod_to_equations; lia. }
    destruct (FP s ltac:(rewrite !shad_div in Hs; unfold ASHOFF in Hs; unfold KEND in XH; Z.div_mod_to_equations; lia)
                 ltac:(right; exists a'; split; [exists c, A, n; split; [exact Hb| lia]| symmetry; exact Ea])) as [E _].
    exact E.
Qed.
End FC.
Lemma dl_inblk_sub : forall LB' X n X' n', ainblk LB' X n -> X <= X' -> X' + n' <= X + n -> ainblk LB' X' n'.
Proof. intros LB' X n X' n' (bb & Hb & H1 & H2) A B. exists bb. split; [exact Hb| clear - H1 H2 A B; lia]. Qed.


Section DL.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
            (SPV lo DCTX DST CAP B0 B1 LSRC : Z) (src : list Z) (h : frame_header) (llt mlt oft pcs dsz bt stg fe : word) (ws : list word).

  Hypothesis CTX : AZ_declit_a.DLCTX AI rng_fs L RNG st LB tp m0 SPV lo DCTX DST CAP B0 B1 LSRC src h ws.

  Notation FOOT := [(DST, DST + CAP); (DCTX + 24, DCTX + 32); (DCTX + 10296, DCTX + 26684); (DCTX + 27324, DCTX + 29884);
                    (DCTX + 30000, DCTX + 30004); (DCTX + 30096, DCTX + 95940); (SPV - 6096, SPV)].
  Notation FFR6 := [(DST, DST + CAP); (DCTX + 24, DCTX + 32); (DCTX + 10296, DCTX + 26684); (DCTX + 27324, DCTX + 29884);
                    (DCTX + 30000, DCTX + 30004); (DCTX + 30096, DCTX + 95940)].
  Notation POST := (zd_declit_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DCTX DST CAP B0 B1 LSRC (zlen src)
                                    llt mlt oft pcs dsz bt stg fe ws lo m0).
  Notation DSAVED := [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -96)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 (Z_to_bv 64 SHB) xs6 xs7 xs8 xs9 xs10 s11 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Notation DLB := (AZ_declit_a.DLB AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe).
  Ltac dl_open C :=
    pose proof C as ((DCL & DCH & DCA & SLEN & SRCL & SRCH & B0D & DCB & CAP0 & B1H & DNULL & DNN & LO0 & LOS & SPH)
                     & (OFFD & OFFB & OFFSRC & BD & BSRC & SRCD) & (FBY & BSM & ISF)
                     & (AFP & TP & ARD & AHD & AID & ARS & AHS & AIS & ADST));
    pose proof AFP as (AH0 & ASH & ART0 & (KHI & RSTK & RI) & RFS & BOT & SPT & SP16 & RSTKT & LBH).
  Ltac open_dlb I := unfold AZ_declit_a.DLB in I; destruct I as (PTRS & EHUF & EWK & FP & H3 & H5 & XB & SRCB & BUF & STK & FRA & MI & MU & WM & AH & FFR & UD & US & UB & ARO & AZS);
                     unfold dctx_ptrs in PTRS; unfold dctx_h3 in H3; unfold zfh_cells in FP.

  Notation dl_ret := (AZ_declit_a.dl_ret AI rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe ws CTX).
  Notation dl_e20 := (AZ_declit_a.dl_e20 AI rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe ws CTX).
  Hypothesis FHL : fake_heap_law AI.
  Hypothesis H1X : huf_1x_stmtA.
  Hypothesis H4X : huf_4x_stmtA.
  (* [comment removed for export] *)
  Hypothesis H1W : huf_wksp_stmtA_at AI rng_fs APHUF_1X1_WKSP 5984.
  Hypothesis H4W : huf_4x_wksp_stmtA AI rng_fs.
  Notation dlbK := (AZ_declit_b.dlb_keep AI rng_fs L RNG st LB ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe ws CTX).
  Notation dlbK2 := (AZ_declit_b.dlb_keep2 AI rng_fs L RNG st LB ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe ws CTX).
  Ltac hlia := unfold fk_held in *; lia.
  (* [comment removed for export] *)
  Ltac nrm_not_by tac := match goal with |- context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) by tac end.

  Ltac cells_words cs :=
    lazymatch cs with
    | nil => constr:(@nil word)
    | C8 ?w :: ?r => let t := cells_words r in constr:(w :: t)
    | C4 ?w :: ?r => let t := cells_words r in constr:(w :: t)
    end.
  (* [comment removed for export] *)
  Ltac dl_chk mm p UDx RDSx DG :=
    let RDz := fresh "RDz" in let RTz := fresh "RTz" in
    pose proof (dl_sh_rd0s mm DCTX 95992 p UDx ltac:(clear; lia) ltac:(clear - DG; Z.div_mod_to_equations; lia) ltac:(clear - DG; lia) ltac:(clear - DG; lia)) as RDz;
    pose proof (dl_sh_rng1 RNG DCTX p RDSx (proj1 DG) ltac:(clear; lia) ltac:(clear; lia)) as RTz;
    zstep; clear RDz RTz;
    try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity; try replace (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity;
    zstep; if_false.
  (* [comment removed for export] *)
  Lemma dlb_keepF : forall hufv' lev' ws1 (ma mb : amem) W Wf,
    DLB hufv' lev' ws1 ma -> 0 < zlen src ->
    munch (W ++ fake_area L) ma mb -> wmono bsegs ma mb -> mem_inv bsegs mb ->
    stk bsegs mb lo (SPV + -96) -> stk bsegs mb B0 B1 -> stk bsegs mb (DCTX + 30372) (DCTX + 95940) ->
    stk bsegs mb (DCTX + 10296) (DCTX + 26684) -> stk bsegs mb (DCTX + 27324) (DCTX + 29884) ->
    AHEAP AI L RNG st LB mb -> ffr_pres Wf LB ma mb -> sub_fp Wf W -> sub_fp Wf FFR6 ->
    Forall (fun iv => fst iv <= snd iv /\ ((0 < CAP /\ DST <= fst iv /\ snd iv <= DST + CAP) \/ (DCTX + 10296 <= fst iv /\ snd iv <= DCTX + 26684)
                                           \/ (DCTX + 27324 <= fst iv /\ snd iv <= DCTX + 29884) \/ (DCTX + 30372 <= fst iv /\ snd iv <= DCTX + 95940)
                                           \/ (SPV - 6096 <= fst iv /\ snd iv <= SPV + -96))) W ->
    DLB hufv' lev' ws1 mb.
  Proof.
    intros hufv' lev' ws1 ma mb W Wf I NZ MUx WMx MIx STKx BUFx XBx EHx EWx AHx FFRf SFW SF6 HW. dl_open CTX.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold KHIGH in KHI.
    pose proof (ARD ltac:(clear; lia)) as (ABD & _). pose proof (fk_ablk_lits _ _ ABD) as DL.
    pose proof (ARS NZ) as (ABS & _). pose proof (fk_ablk_lits _ _ ABS) as SBB.
    unfold AZ_declit_a.DLB in I. destruct I as (PTRS & EHUF & EWK & FP & H3 & H5 & XB & SRCB & BUF & STK & FRA & MI & MU & WM & AH & FFR & UD & US & UB & ARO & AZS).
    pose proof (bytes_at_bound _ _ _ _ SRCB) as SBL. rewrite length_map in SBL. pose proof BUF as (B00 & _).
    destruct (FHL _ _ _ _ _ AH) as [FAB _]. pose proof (fk_ablk_lits _ _ FAB) as FAL.
    assert (DBL : 0 < CAP -> 6443008 <= B0 /\ B1 <= ATOP /\ (B1 <= KLOW \/ KHIGH <= B0)).
    { intros HC. destruct (ADST ltac:(clear - HC B0D DCB; lia)) as (ARb & _). destruct (ARb ltac:(clear - HC B0D DCB; lia)) as (ABb & _).
      pose proof (fk_ablk_lits _ _ ABb) as X. pose proof (ablk_disj_band _ _ ABb) as Y. unfold KLS, KLOW, KHIGH in *. clear - X Y HC; lia. }
    pose proof (dl_ffr_pres_weaken _ _ _ _ _ FFRf SFW) as FFRW.
    assert (DJ : forall X n, 0 <= n -> (0 < CAP -> X + n <= DST \/ DST + CAP <= X) -> (X + n <= DCTX + 10296 \/ DCTX + 26684 <= X) ->
                 (X + n <= DCTX + 27324 \/ DCTX + 29884 <= X) -> (X + n <= DCTX + 30372 \/ DCTX + 95940 <= X) -> (X + n <= SPV - 6096 \/ SPV + -96 <= X) ->
                 disjoint_from W X n).
    { intros X n Hn A B B' C D. clear - HW Hn A B B' C D. induction HW as [|[x y] W [Hle Hc] HW IH]; cbn; [exact I|]. cbn in Hle, Hc. split; [| exact IH].
      destruct Hc as [(HC & Hx & Hy)|[[Hx Hy]|[[Hx Hy]|[[Hx Hy]|[Hx Hy]]]]]; [specialize (A HC); lia| lia| lia| lia| lia]. }
    assert (AW : aappW W).
    { unfold aappW. clear - HW DL DBL KHI LOS SPH ATR B0D DCB. induction HW as [|[x y] W [Hle Hc] HW IH]; [apply Forall_nil|]. apply Forall_cons; [| exact IH].
      cbn [fst snd] in *. unfold KLOW, KHIGH in *. destruct Hc as [(HC & Hx & Hy)|[[Hx Hy]|[[Hx Hy]|[[Hx Hy]|[Hx Hy]]]]]; [specialize (DBL HC); lia| lia| lia| lia| lia]. }
    (* [comment removed for export] *)
    assert (DSTK : disjoint_from (W ++ fake_area L) (SPV + -96) 96).
    { apply disjoint_from_app2.
      - apply DJ; [clear; lia| intros HC; clear - HC OFFB B0D DCB LOS; lia| clear - OFFD LOS; lia| clear - OFFD LOS; lia| clear - OFFD LOS; lia| clear; lia].
      - cbn [disjoint_from fake_area]. rewrite !shad_div. unfold FAKESZ, ASHOFF in *. clear - FAL ATR BOT LOS KHI. repeat split; Z.div_mod_to_equations; lia. }
    assert (IS : ainblk LB LSRC (zlen src)).
    { destruct (AIS NZ) as [IB|[H0 HI]]; [exact IB|]. exfalso. unfold ablk, AIMG_HI, KLS in ABS. unfold AIMG_HI in HI. clear - ABS HI NZ. lia. }
    unfold dctx_ptrs, dctx_h3, zfh_cells in *.
    split; [eapply (dl_fcall_cells_pres AI FHL _ _ _ _ _ _ _ W) in PTRS; [exact PTRS| exact AH| eapply dl_inblk_sub; [exact AID| clear; lia| cbn; clear; lia]| apply DJ; cbn; [clear| clear - BD B0D DCB| clear| clear| clear| clear - DL LOS OFFD]; lia| exact MUx| exact WMx| exact FFRW]|].
    split; [exact EHx|]. split; [exact EWx|].
    split; [eapply (dl_fcall_cells_pres AI FHL _ _ _ _ _ _ _ W) in FP; [exact FP| exact AH| eapply dl_inblk_sub; [exact AID| clear; lia| cbn; clear; lia]| apply DJ; cbn; [clear| clear - BD B0D DCB| clear| clear| clear| clear - DL LOS OFFD]; lia| exact MUx| exact WMx| exact FFRW]|].
    split; [eapply (dl_fcall_cells_pres AI FHL _ _ _ _ _ _ _ W) in H3; [exact H3| exact AH| eapply dl_inblk_sub; [exact AID| clear; lia| cbn; clear; lia]| apply DJ; cbn; [clear| clear - BD B0D DCB| clear| clear| clear| clear - DL LOS OFFD]; lia| exact MUx| exact WMx| exact FFRW]|].
    split.
    { destruct H5 as [H5C H5L]. split; [| exact H5L].
      eapply (dl_fcall_cells_pres AI FHL _ _ _ _ _ _ _ W) in H5C; [exact H5C| exact AH| rewrite (h5_cells_size _ H5L); eapply dl_inblk_sub; [exact AID| clear; lia| clear; lia]| rewrite (h5_cells_size _ H5L); apply DJ; cbn; [clear| clear - BD B0D DCB| clear| clear| clear| clear - DL LOS OFFD]; lia| exact MUx| exact WMx| exact FFRW]. }
    split; [exact XBx|].
    split; [eapply (dl_fcall_bytes_pres AI FHL _ _ _ _ _ _ _ W) in SRCB; [exact SRCB| exact AH| rewrite length_map; exact IS| rewrite length_map; apply DJ; [clear - SBL| clear - BSRC B0D DCB| clear - SRCD| clear - SRCD| clear - SRCD| clear - OFFSRC LOS]; lia| exact MUx| exact FFRW]|].
    split; [exact BUFx|]. split; [exact STKx|].
    split; [eapply rw_cells_transport; [exact FRA| exact MUx| exact WMx| exact DSTK]|].
    split; [exact MIx|].
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUx]]; unfold sub_fp; intros x Hx; apply (proj1 (fk_outside_app _ _ _)) in Hx; destruct Hx as [Hx Hf];
            apply (proj2 (fk_outside_app _ _ _)); split; [| exact Hf];
            clear - Hx HW; induction HW as [|[u v] W [Hle Hc] HW IH]; cbn; [exact I|]; cbn in Hle, Hc, Hx; unfold outside in Hx; cbn in Hx; split; [lia| exact IH]|].
    split; [exact (wmono_trans _ _ _ _ WM WMx)|].
    split; [exact AHx|].
    split; [eapply ffr_pres_trans; [exact FFR| exact (dl_ffr_pres_weaken _ _ _ _ _ FFRf SF6)]|].
    split; [eapply (dl_fcall_unp_pres AI FHL _ _ _ _ _ _ _ W); [exact AH| exact AID| clear; lia| unfold KEND; clear - DCH; lia| exact AW| exact MUx| exact FFRW| exact UD]|].
    split; [intros _; eapply (dl_fcall_unp_pres AI FHL _ _ _ _ _ _ _ W); [exact AH| exact IS| exact NZ| unfold KEND; clear - SRCH; lia| exact AW| exact MUx| exact FFRW| exact (US NZ)]|].
    split.
    { intros HB. destruct (ADST HB) as (_ & _ & IB). replace B1 with (B0 + (B1 - B0)) by (clear; lia).
      eapply (dl_fcall_unp_pres AI FHL _ _ _ _ _ _ _ W); [exact AH| exact IB| clear - HB; lia| unfold KEND; clear - B1H; lia| exact AW| exact MUx| exact FFRW| replace (B0 + (B1 - B0)) with B1 by (clear; lia); exact (UB HB)]. }
    split; [eapply aro_client_transport_F; [exact ARO| exact MUx| exact WMx| exact AW| exact FAB]|].
    eapply azstk_transport_F; [exact AZS| exact MUx| exact WMx| exact AW| exact FAB| unfold al_fake; clear; Z.div_mod_to_equations; lia| clear - FAL ATR BOT; lia| clear - LOS; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma dl_callL : forall ENTRY fr RA m hufv lev wsv litSize litCSize lhSize A dtb
      (x5 x6 x7 flags xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31 : word),
    huf_using_stmtA_at ENTRY fr -> 0 <= fr <= 6000 -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
    DLB hufv lev wsv m -> 0 < zlen src ->
    3 <= lhSize <= 5 -> 0 <= litCSize -> lhSize + litCSize <= zlen src -> 0 <= litSize <= Z.min (fh_bsmax h) CAP ->
    bytes_at bsegs m (DCTX + 10296) dtb -> huf_hdr_ok dtb -> huf_tbl_ok dtb ->
    ((0 < CAP /\ DST <= A /\ A + litSize <= DST + CAP) \/ (A = DCTX + 30372 /\ litSize <= 65536)) ->
    (forall m' r (y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word),
        DLB hufv lev wsv m' -> bytes_at bsegs m' (DCTX + 10296) dtb -> (r = litSize \/ zd_is_error r = true) -> 0 <= r < 2^64 ->
        evtF bsegs RNG POST (ST RA m' (Z_to_bv 64 RA) y5 y6 y7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize) (Z_to_bv 64 r) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                               xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (ST ENTRY m (Z_to_bv 64 RA) x5 x6 x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize)
                           (Z_to_bv 64 A) (Z_to_bv 64 litSize) (Z_to_bv 64 (LSRC + lhSize)) (Z_to_bv 64 litCSize) (Z_to_bv 64 (DCTX + 10296)) flags xa6 xa7
                           xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros HX FRR RAR RAE I NZ LHR LCS LHS LSR HTB HOK TOK PL K. pose proof I as DLI. open_dlb I. dl_open CTX.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold KHIGH in KHI.
    pose proof (ARD ltac:(clear; lia)) as (ABD & _ & RDc & RDS). pose proof (fk_ablk_lits _ _ ABD) as DL.
    pose proof (ARS NZ) as (ABS & _ & RSa & RSb). pose proof (fk_ablk_lits _ _ ABS) as SBB.
    pose proof (bytes_at_bound _ _ _ _ SRCB) as SBL. rewrite length_map in SBL.
    assert (DG : DCTX mod 8 = 0 /\ 0 <= DCTX /\ DCTX + 95992 <= 2^47) by (clear - DCA DCL DCH; lia).
    assert (EOFF : zlen dtb = 16388) by (destruct HOK as [EL _]; exact EL).
    (* [comment removed for export] *)
    assert (AW1 : 4096 <= A /\ A + litSize < 2^47 /\ (A + litSize <= lo \/ SPV <= A) /\ (A + litSize <= LSRC \/ LSRC + zlen src <= A)
                  /\ (A + litSize <= DCTX + 10296 \/ DCTX + 26684 <= A)).
    { destruct PL as [(HC & P1 & P2)|[-> P2]].
      - assert (HD : DST <> 0) by (intros HD; pose proof (DNULL HD); clear - HC H; lia).
        pose proof (DNN HD) as B4. clear - HC P1 P2 B4 B0D DCB B1H OFFB BSRC BD LSR. lia.
      - clear - P2 DCL DCH OFFD SRCD LSR. lia. }
    destruct AW1 as (A4 & AH47 & AOFF & ASRC & ADT).
    (* [comment removed for export] *)
    pose proof (dl_bytes_at_slice _ _ _ (Z.to_nat lhSize) (Z.to_nat litCSize) SRCB ltac:(rewrite length_map; clear - LHR LCS LHS; lia)) as SL1.
    rewrite Z2Nat.id in SL1 by (clear - LHR; lia).
    assert (SL1L : zlen (firstn (Z.to_nat litCSize) (skipn (Z.to_nat lhSize) (map (Z_to_bv 8) src))) = litCSize).
    { rewrite firstn_length_le; [clear - LCS; lia|]. rewrite length_skipn, length_map. clear - LHR LCS LHS; lia. }
    (* [comment removed for export] *)
    assert (WIN : stk bsegs m A (A + litSize)
                  /\ (forall (m' : amem) W, stk bsegs m' A (A + litSize) -> munch W m m' -> wmono bsegs m m' ->
                        (DST <= A /\ A + litSize <= DST + CAP -> disjoint_from W B0 (A - B0) /\ disjoint_from W (A + litSize) (B1 - (A + litSize))
                                                               /\ disjoint_from W (DCTX + 30372) (DCTX + 95940 - (DCTX + 30372))) ->
                        (A = DCTX + 30372 -> disjoint_from W (A + litSize) (DCTX + 95940 - (A + litSize)) /\ disjoint_from W B0 (B1 - B0)) ->
                        stk bsegs m' B0 B1 /\ stk bsegs m' (DCTX + 30372) (DCTX + 95940))).
    { destruct PL as [(HC & P1 & P2)|[EA P2]].
      - destruct (stk_split bsegs m B0 A B1 BUF ltac:(clear - P1 P2 B0D DCB LSR; lia)) as [BUFa BUF2].
        destruct (stk_split bsegs m A (A + litSize) B1 BUF2 ltac:(clear - P1 P2 B0D DCB LSR; lia)) as [BUFw BUFb].
        split; [exact BUFw|]. intros m' W ST' MU' WM' DD _. destruct (DD ltac:(clear - P1 P2; lia)) as (D1 & D2 & D5). split.
        + eapply stk_merge; [eapply stk_merge; [| exact ST'| clear - P1 B0D LSR; lia]| | clear - P1 P2 B0D DCB LSR; lia].
          * eapply stk_transport_disjoint; [exact BUFa| exact MU'| exact WM'| exact D1].
          * eapply stk_transport_disjoint; [exact BUFb| exact MU'| exact WM'| exact D2].
        + eapply stk_transport_disjoint; [exact XB| exact MU'| exact WM'| exact D5].
      - subst A. destruct (stk_split bsegs m (DCTX + 30372) (DCTX + 30372 + litSize) (DCTX + 95940) XB ltac:(clear - P2 LSR; lia)) as [XBw XBb].
        split; [exact XBw|]. intros m' W ST' MU' WM' _ DE. destruct (DE eq_refl) as [D4 D6]. split.
        + eapply stk_transport_disjoint; [exact BUF| exact MU'| exact WM'| exact D6].
        + eapply stk_merge; [exact ST'| eapply stk_transport_disjoint; [exact XBb| exact MU'| exact WM'| exact D4]| clear - P2 LSR; lia]. }
    destruct WIN as [STW WBACK].
    assert (ARW : areg RNG m A litSize).
    { destruct PL as [(HC & P1 & P2)|[EA P2]].
      - destruct (ADST ltac:(clear - HC B0D DCB; lia)) as (ARb & _). eapply (areg_sub RNG m B0 (B1 - B0) A litSize); [| clear - P1 B0D; lia| clear - LSR; lia| clear - P2 DCB; lia].
        intros _. destruct (ARb ltac:(clear - HC B0D DCB; lia)) as (ABb & _ & RBa & RBb). split; [exact ABb|]. split; [replace (B0 + (B1 - B0)) with B1 by (clear; lia); exact (UB ltac:(clear - HC B0D DCB; lia))|]. split; [exact RBa| exact RBb].
      - subst A. eapply (areg_sub RNG m DCTX 95992 (DCTX + 30372) litSize); [| clear; lia| clear - LSR; lia| clear - P2; lia]. intros _. split; [exact ABD|]. split; [exact UD|]. split; [exact RDc| exact RDS]. }
    assert (ART1 : art m) by exact (dl_art_of_aheap AI _ _ _ _ _ AH).
    assert (PRE1 : huf_dec_preA RNG m (SPV + -96) lo fr A litSize (LSRC + lhSize) litCSize (firstn (Z.to_nat litCSize) (skipn (Z.to_nat lhSize) (map (Z_to_bv 8) src)))).
    { unfold huf_dec_preA.
      split; [exact MI|]. split; [exact STK|]. split; [exact LO0|]. split; [clear - LOS FRR; lia|]. split; [clear - SPH; lia|].
      split; [exact STW|]. split; [exact A4|]. split; [clear - LSR BSM; lia|]. split; [exact AH47|].
      split; [exact SL1|]. split; [exact SL1L|]. split; [clear - SRCL LHR; lia|]. split; [clear - LCS LHS SLEN LHR; lia|]. split; [clear - LHS SRCH LCS; lia|].
      split; [clear - AOFF LOS; lia|]. split; [clear - OFFSRC LOS LHR LHS LCS; lia|]. split; [clear - ASRC LHR LHS LCS; lia|].
      split; [exact ARW|].
      split; [eapply (areg_sub RNG m LSRC (zlen src) (LSRC + lhSize) litCSize); [intros _; split; [exact ABS| split; [exact (US NZ)| split; [exact RSa| exact RSb]]]| clear - LHR; lia| exact LCS| clear - LHS; lia]|].
      split; [exact ART1|].
      split; [split; [unfold KHIGH; clear - KHI; lia| split; [eapply rng_sub'; [exact RSTK| clear - LOS; lia]| exact RI]]|].
      split; [eapply azstk_sub; [exact AZS| clear; lia| clear - LOS; lia| clear; lia]|].
      split; [exact ARO|]. clear - SP16. Z.div_mod_to_equations. lia. }
    assert (PRE2 : huf_dt_preA RNG m (SPV + -96) lo A litSize (DCTX + 10296) dtb).
    { unfold huf_dt_preA, HUF_DTABLE_BYTES.
      split; [exact HTB|]. split; [exact EOFF|]. split; [clear - DCL; lia|]. split; [clear - DCH; lia|].
      split; [clear - OFFD LOS; lia|]. split; [clear - ADT; lia|].
      split; [| clear - DCA; Z.div_mod_to_equations; lia].      (* [comment removed for export] *)
      split; [eapply unpoisoned_sub; [exact UD| clear; lia| clear; lia]|].
      split; [eapply rng_sub'; [exact RDc| clear; lia]|].
      eapply rng_sub'; [exact RDS| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - DG; Z.div_mod_to_equations; lia]. }
    fk_hold K. fk_hold WBACK. fk_hold PL. fk_hold DLI.
    unfold huf_using_stmtA_at in HX.
    eapply evtF_cut; [eapply (HX RNG); [exact PRE1| exact PRE2| exact TOK]|].
    cbv beta. intros ms' (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m' & r & -> & MUc & WMc & MI' & STK' & STA' & RES & RR & _).
    cbn [app] in MUc.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [exact RAR| exact RAE]).
    unfold fk_held in WBACK, PL, DLI, K.
    destruct (WBACK m' _ STA' MUc WMc
                ltac:(intros [P1 P2]; cbn [disjoint_from]; clear - P1 P2 OFFB OFFD B0D DCB B1H LOS LSR FRR BD; repeat split; lia)
                ltac:(intros EA; cbn [disjoint_from]; clear - EA OFFB OFFD B0D DCB LOS LSR FRR BD PL; repeat split; lia)) as [BUF' XB'].
    assert (DLI' : DLB hufv lev wsv m').
    { eapply (dlbK2 hufv lev wsv m m' _ DLI MUc WMc MI' STK' BUF' XB').
      apply Forall_cons; [cbn [fst snd]; clear - PL LSR; lia|]. apply Forall_cons; [cbn [fst snd]; clear - LOS FRR; lia| apply Forall_nil]. }
    assert (HTB' : bytes_at bsegs m' (DCTX + 10296) dtb).
    { eapply bytes_at_transport; [exact HTB| exact MUc|]. rewrite EOFF. cbn [disjoint_from]. clear - ADT OFFD LOS FRR. repeat split; lia. }
    eapply K; [exact DLI'| exact HTB'| exact RES| exact RR].
  Qed.
  (* [comment removed for export] *)
  Lemma dl_callF : forall ENTRY fr RA m hufv lev wsv litSize litCSize lhSize A dtb
      (x5 x6 x7 flags xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31 : word),
    huf_wksp_stmtA_at AI rng_fs ENTRY fr -> 0 <= fr <= 6000 -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
    DLB hufv lev wsv m -> 0 < zlen src ->
    3 <= lhSize <= 5 -> 0 <= litCSize -> lhSize + litCSize <= zlen src -> 0 <= litSize <= Z.min (fh_bsmax h) CAP ->
    bytes_at bsegs m (DCTX + 10296) dtb -> huf_hdr_ok dtb ->
    ((0 < CAP /\ DST <= A /\ A + litSize <= DST + CAP) \/ (A = DCTX + 30372 /\ litSize <= 65536)) ->
    (forall m' r dtb' (y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word),
        DLB hufv lev wsv m' -> bytes_at bsegs m' (DCTX + 10296) dtb' -> huf_hdr_ok dtb' -> (zd_is_error r = false -> huf_tbl_ok dtb') ->
        (r = litSize \/ zd_is_error r = true) -> 0 <= r < 2^64 ->
        evtF bsegs RNG POST (ST RA m' (Z_to_bv 64 RA) y5 y6 y7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize) (Z_to_bv 64 r) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                               xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (ST ENTRY m (Z_to_bv 64 RA) x5 x6 x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize)
                           (Z_to_bv 64 (DCTX + 10296)) (Z_to_bv 64 A) (Z_to_bv 64 litSize) (Z_to_bv 64 (LSRC + lhSize)) (Z_to_bv 64 litCSize)
                           (Z_to_bv 64 (DCTX + 27324)) (Z_to_bv 64 2560) flags
                           xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros HX FRR RAR RAE I NZ LHR LCS LHS LSR HTB HOK PL K. pose proof I as DLI. open_dlb I. dl_open CTX.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold KHIGH in KHI.
    pose proof (ARD ltac:(clear; lia)) as (ABD & _ & RDc & RDS). pose proof (fk_ablk_lits _ _ ABD) as DL.
    pose proof (ARS NZ) as (ABS & _ & RSa & RSb). pose proof (fk_ablk_lits _ _ ABS) as SBB.
    pose proof (bytes_at_bound _ _ _ _ SRCB) as SBL. rewrite length_map in SBL.
    assert (DG : DCTX mod 8 = 0 /\ 0 <= DCTX /\ DCTX + 95992 <= 2^47) by (clear - DCA DCL DCH; lia).
    assert (EOFF : zlen dtb = 16388) by (destruct HOK as [EL _]; exact EL).
    (* [comment removed for export] *)
    assert (AW1 : 4096 <= A /\ A + litSize < 2^47 /\ (A + litSize <= lo \/ SPV <= A) /\ (A + litSize <= LSRC \/ LSRC + zlen src <= A)
                  /\ (A + litSize <= DCTX + 10296 \/ DCTX + 26684 <= A) /\ (A + litSize <= DCTX + 27324 \/ DCTX + 29884 <= A)).
    { destruct PL as [(HC & P1 & P2)|[-> P2]].
      - assert (HD : DST <> 0) by (intros HD; pose proof (DNULL HD); clear - HC H; lia).
        pose proof (DNN HD) as B4. clear - HC P1 P2 B4 B0D DCB B1H OFFB BSRC BD LSR. lia.
      - clear - P2 DCL DCH OFFD SRCD LSR. lia. }
    destruct AW1 as (A4 & AH47 & AOFF & ASRC & ADT & AWK).
    (* [comment removed for export] *)
    pose proof (dl_bytes_at_slice _ _ _ (Z.to_nat lhSize) (Z.to_nat litCSize) SRCB ltac:(rewrite length_map; clear - LHR LCS LHS; lia)) as SL1.
    rewrite Z2Nat.id in SL1 by (clear - LHR; lia).
    assert (SL1L : zlen (firstn (Z.to_nat litCSize) (skipn (Z.to_nat lhSize) (map (Z_to_bv 8) src))) = litCSize).
    { rewrite firstn_length_le; [clear - LCS; lia|]. rewrite length_skipn, length_map. clear - LHR LCS LHS; lia. }
    (* [comment removed for export] *)
    assert (WIN : stk bsegs m A (A + litSize)
                  /\ (forall (m' : amem) W, stk bsegs m' A (A + litSize) -> munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> ffr_pres W LB m m' ->
                        (DST <= A /\ A + litSize <= DST + CAP -> disjoint_from W B0 (A - B0) /\ disjoint_from W (A + litSize) (B1 - (A + litSize))
                                                               /\ disjoint_from W (DCTX + 30372) (DCTX + 95940 - (DCTX + 30372))) ->
                        (A = DCTX + 30372 -> disjoint_from W (A + litSize) (DCTX + 95940 - (A + litSize)) /\ (B0 < B1 -> disjoint_from W B0 (B1 - B0))) ->
                        stk bsegs m' B0 B1 /\ stk bsegs m' (DCTX + 30372) (DCTX + 95940))).
    { destruct PL as [(HC & P1 & P2)|[EA P2]].
      - destruct (stk_split bsegs m B0 A B1 BUF ltac:(clear - P1 P2 B0D DCB LSR; lia)) as [BUFa BUF2].
        destruct (stk_split bsegs m A (A + litSize) B1 BUF2 ltac:(clear - P1 P2 B0D DCB LSR; lia)) as [BUFw BUFb].
        destruct (ADST ltac:(clear - HC B0D DCB; lia)) as (_ & _ & IB).
        split; [exact BUFw|]. intros m' W ST' MU' WM' FP' DD _. destruct (DD ltac:(clear - P1 P2; lia)) as (D1 & D2 & D5). split.
        + eapply stk_merge; [eapply stk_merge; [| exact ST'| clear - P1 B0D LSR; lia]| | clear - P1 P2 B0D DCB LSR; lia].
          * eapply (dl_fcall_stk_pres AI FHL _ _ _ _ _ _ _ W); [exact AH| eapply dl_inblk_sub; [exact IB| clear; lia| clear - P1 P2 B0D DCB LSR; lia]| exact D1| exact MU'| exact WM'| exact FP'| exact BUFa].
          * eapply (dl_fcall_stk_pres AI FHL _ _ _ _ _ _ _ W); [exact AH| eapply dl_inblk_sub; [exact IB| clear - P1 B0D LSR; lia| clear - P2 DCB; lia]| exact D2| exact MU'| exact WM'| exact FP'| exact BUFb].
        + eapply (dl_fcall_stk_pres AI FHL _ _ _ _ _ _ _ W); [exact AH| eapply dl_inblk_sub; [exact AID| clear; lia| clear; lia]| exact D5| exact MU'| exact WM'| exact FP'| exact XB].
      - subst A. destruct (stk_split bsegs m (DCTX + 30372) (DCTX + 30372 + litSize) (DCTX + 95940) XB ltac:(clear - P2 LSR; lia)) as [XBw XBb].
        split; [exact XBw|]. intros m' W ST' MU' WM' FP' _ DE. destruct (DE eq_refl) as [D4 D6]. split.
        + destruct (Z.lt_ge_cases B0 B1) as [HB|HB].
          * destruct (ADST HB) as (_ & _ & IB).
            eapply (dl_fcall_stk_pres AI FHL _ _ _ _ _ _ _ W); [exact AH| exact IB| exact (D6 HB)| exact MU'| exact WM'| exact FP'| exact BUF].
          * destruct BUF as (X & Y & _). split; [exact X|]. split; [exact Y|]. intros a Ha. exfalso. clear - HB Ha. lia.
        + eapply stk_merge; [exact ST'| | clear - P2 LSR; lia].
          eapply (dl_fcall_stk_pres AI FHL _ _ _ _ _ _ _ W); [exact AH| eapply dl_inblk_sub; [exact AID| clear - LSR; lia| clear - P2; lia]| exact D4| exact MU'| exact WM'| exact FP'| exact XBb]. }
    destruct WIN as [STW WBACK].
    assert (ARDm : areg RNG m DCTX 95992) by (intros _; split; [exact ABD| split; [exact UD| split; [exact RDc| exact RDS]]]).
    assert (ARW : areg RNG m A litSize).
    { destruct PL as [(HC & P1 & P2)|[EA P2]].
      - destruct (ADST ltac:(clear - HC B0D DCB; lia)) as (ARb & _). eapply (areg_sub RNG m B0 (B1 - B0) A litSize); [| clear - P1 B0D; lia| clear - LSR; lia| clear - P2 DCB; lia].
        intros _. destruct (ARb ltac:(clear - HC B0D DCB; lia)) as (ABb & _ & RBa & RBb). split; [exact ABb|]. split; [replace (B0 + (B1 - B0)) with B1 by (clear; lia); exact (UB ltac:(clear - HC B0D DCB; lia))|]. split; [exact RBa| exact RBb].
      - subst A. eapply (areg_sub RNG m DCTX 95992 (DCTX + 30372) litSize); [exact ARDm| clear; lia| clear - LSR; lia| clear - P2; lia]. }
    assert (AIW : ainblk LB A litSize).
    { destruct PL as [(HC & P1 & P2)|[EA P2]].
      - destruct (ADST ltac:(clear - HC B0D DCB; lia)) as (_ & _ & IB). eapply dl_inblk_sub; [exact IB| clear - P1 B0D; lia| clear - P2 DCB; lia].
      - subst A. eapply dl_inblk_sub; [exact AID| clear; lia| clear - P2; lia]. }
    assert (ART1 : art m) by exact (dl_art_of_aheap AI _ _ _ _ _ AH).
    assert (AHDm : ahull RNG m DCTX 95992) by (eapply dl_ahull_wmono; [exact AHD| exact WM]).
    assert (PRE1 : huf_dec_preA RNG m (SPV + -96) lo fr A litSize (LSRC + lhSize) litCSize (firstn (Z.to_nat litCSize) (skipn (Z.to_nat lhSize) (map (Z_to_bv 8) src)))).
    { unfold huf_dec_preA.
      split; [exact MI|]. split; [exact STK|]. split; [exact LO0|]. split; [clear - LOS FRR; lia|]. split; [clear - SPH; lia|].
      split; [exact STW|]. split; [exact A4|]. split; [clear - LSR BSM; lia|]. split; [exact AH47|].
      split; [exact SL1|]. split; [exact SL1L|]. split; [clear - SRCL LHR; lia|]. split; [clear - LCS LHS SLEN LHR; lia|]. split; [clear - LHS SRCH LCS; lia|].
      split; [clear - AOFF LOS; lia|]. split; [clear - OFFSRC LOS LHR LHS LCS; lia|]. split; [clear - ASRC LHR LHS LCS; lia|].
      split; [exact ARW|].
      split; [eapply (areg_sub RNG m LSRC (zlen src) (LSRC + lhSize) litCSize); [intros _; split; [exact ABS| split; [exact (US NZ)| split; [exact RSa| exact RSb]]]| clear - LHR; lia| exact LCS| clear - LHS; lia]|].
      split; [exact ART1|].
      split; [split; [unfold KHIGH; clear - KHI; lia| split; [eapply rng_sub'; [exact RSTK| clear - LOS; lia]| exact RI]]|].
      split; [eapply azstk_sub; [exact AZS| clear; lia| clear - LOS; lia| clear; lia]|].
      split; [exact ARO|]. clear - SP16. Z.div_mod_to_equations. lia. }
    pose proof (dl_stk_bytes_u8arr m (DCTX + 10296) dtb ltac:(rewrite EOFF; replace (DCTX + 10296 + 16388) with (DCTX + 26684) by (clear; lia); exact EHUF) HTB) as DTU.
    pose proof EWK as EWK'. replace (DCTX + 29884) with (DCTX + 27324 + 2560) in EWK' by (clear; lia).
    assert (AFP' : afpre AI rng_fs L RNG st LB m lo (SPV + -96) 4).
    { unfold afpre, astk. split; [exact AH|]. split; [exact ASH|]. split; [exact ART1|].
      split; [split; [unfold KHIGH; clear - KHI; lia| split; [eapply rng_sub'; [exact RSTK| clear - LOS; lia]| exact RI]]|].
      split; [exact RFS|]. split; [exact BOT|]. split; [clear - SPT; lia|]. split; [clear - SP16; Z.div_mod_to_equations; lia|]. split; [exact RSTKT| exact LBH]. }
    idtac "CALL-F0".
    fk_hold K. fk_hold WBACK. fk_hold DLI.
    unfold huf_wksp_stmtA_at in HX.
    eapply evtF_cut.
    { eapply (HX L RNG st LB) with (lo := lo);
        first [ exact PRE1 | exact DTU | exact HOK | exact EWK' | exact AFP' | exact TP | exact ARO | exact AIW
              | lazymatch goal with
                | |- areg _ _ (DCTX + 10296) _ => eapply (areg_sub RNG m DCTX 95992 (DCTX + 10296) HUF_DTABLE_BYTES); [exact ARDm| clear; lia| unfold HUF_DTABLE_BYTES; clear; lia| unfold HUF_DTABLE_BYTES; clear; lia]
                | |- areg _ _ (DCTX + 27324) _ => eapply (areg_sub RNG m DCTX 95992 (DCTX + 27324) 2560); [exact ARDm| clear; lia| clear; lia| clear; lia]
                | |- ahull _ _ (DCTX + 10296) _ => eapply dl_ahull_sub; [exact AHDm| clear; lia| unfold HUF_DTABLE_BYTES; clear; lia]
                | |- ahull _ _ (DCTX + 27324) _ => eapply dl_ahull_sub; [exact AHDm| clear; lia| clear; lia]
                | |- ainblk _ (DCTX + 10296) _ => eapply dl_inblk_sub; [exact AID| clear; lia| unfold HUF_DTABLE_BYTES; clear; lia]
                | |- ainblk _ (DCTX + 27324) _ => eapply dl_inblk_sub; [exact AID| clear; lia| clear; lia]
                | |- 0 < _ -> ainimg _ _ _ => intros _; eapply ainimg_sub; [exact (AIS NZ)| clear - LHR; lia| clear - LHS; lia]
                | |- 0 < _ -> ahull _ _ _ _ => intros _; eapply dl_ahull_sub; [eapply dl_ahull_wmono; [exact (AHS NZ)| exact WM]| clear - LHR; lia| clear - LHS; lia]
                | |- _ mod 4 = 0 => clear - DCA; Z.div_mod_to_equations; lia
                | |- _ => unfold HUF_DTABLE_BYTES; clear - PL DCL DCH OFFD LOS ADT AWK ASRC SRCD LHR LHS LCS LSR; lia
                end
              | lazymatch goal with |- ?Gg => idtac "HUFW-LEFT:" Gg end ]. }
    cbv beta. intros ms' (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m' & r & -> & MUc & WMc & MI' & STK' & STA' & FFRc & AH' & RES & RR & (dtb' & DTU' & HOK' & VAL') & WK').
    unfold HUF_DTABLE_BYTES in MUc, FFRc.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [exact RAR| exact RAE]).
    unfold fk_held in WBACK, DLI, K.
    set (W4 := [(A, A + litSize); (DCTX + 10296, DCTX + 10296 + 16388); (DCTX + 27324, DCTX + 27324 + 2560); (SPV + -96 - fr, SPV + -96)]).
    assert (MU4 : munch (W4 ++ fake_area L) m m') by (eapply munch_weaken; [| exact MUc]; subst W4; unfold sub_fp; cbn [outside app]; intros x Hx; exact Hx).
    assert (FFR4 : ffr_pres W4 LB m m') by (eapply dl_ffr_pres_weaken; [exact FFRc|]; subst W4; unfold sub_fp; cbn [outside]; intros x (X1 & X2 & X3 & _); repeat split; assumption).
    destruct (WBACK m' W4 STA' MU4 WMc FFR4
                ltac:(intros [P1 P2]; subst W4; cbn [disjoint_from]; clear - P1 P2 OFFB OFFD B0D DCB B1H LOS LSR FRR BD; repeat split; lia)
                ltac:(intros EA; subst W4; split; [| intros HB]; cbn [disjoint_from]; clear - EA OFFB OFFD B0D DCB LOS LSR FRR BD PL; repeat split; lia)) as [BUF' XB'].
    assert (LD' : zlen dtb' = 16388) by (destruct HOK' as [EL _]; exact EL).
    pose proof (dl_u8arr_stk _ _ _ DTU') as EH'. rewrite LD' in EH'. replace (DCTX + 10296 + 16388) with (DCTX + 26684) in EH' by (clear; lia).
    replace (DCTX + 27324 + 2560) with (DCTX + 29884) in WK' by (clear; lia).
    assert (DLI' : DLB hufv lev wsv m').
    { eapply (dlb_keepF hufv lev wsv m m' W4 _ DLI NZ MU4 WMc MI' STK' BUF' XB' EH' WK' AH' FFRc).
      - subst W4. unfold sub_fp. cbn [outside]. intros x (X1 & X2 & X3 & _). repeat split; assumption.
      - unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx PL LSR. repeat split; lia.
      - subst W4. apply Forall_cons; [cbn [fst snd]; clear - PL LSR; lia|]. apply Forall_cons; [cbn [fst snd]; clear; lia|].
        apply Forall_cons; [cbn [fst snd]; clear; lia|]. apply Forall_cons; [cbn [fst snd]; clear - LOS FRR; lia| apply Forall_nil]. }
    destruct DTU' as [HTB' _].
    eapply K; [exact DLI'| exact HTB'| exact HOK'| exact VAL'| exact RES| exact RR].
  Qed.
  (* [comment removed for export] *)
  Hypothesis PJOIN : forall m3 hufv lev wsv litSize litCSize lhSize ty A loc r dtb
      (xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs9 xs10 x28 x29 x30 x31 : word),
    DLB hufv lev wsv m3 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    wnth wsv H5_litBuffer = Z_to_bv 64 A -> wnth wsv H5_litBufferEnd = Z_to_bv 64 (A + litSize) -> wnth wsv H5_litBufferLocation = Z_to_bv 64 loc ->
    bytes_at bsegs m3 (DCTX + 10296) dtb -> huf_hdr_ok dtb -> (zd_is_error r = false -> huf_tbl_ok dtb) -> hufv = Z_to_bv 64 (DCTX + 10296) ->
    3 <= lhSize <= 5 -> 0 <= litCSize -> lhSize + litCSize <= zlen src -> 0 <= litSize <= Z.min (fh_bsmax h) CAP ->
    (ty = 2 \/ ty = 3) -> 0 <= r < 2^64 ->
    ((loc = 0 /\ A = DCTX + 30372 /\ litSize <= 65536)
     \/ (loc = 1 /\ 0 < CAP /\ DST <= A /\ A + litSize + 32 <= DST + CAP)
     \/ (loc = 2 /\ 65536 < litSize /\ 0 < CAP /\ DST <= A /\ A + litSize <= DST + CAP)) ->
    evtF bsegs RNG POST (ST 0x87cd0 m3 xra x5 x6 x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize)
                           (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                           xs2 xs3 xs4 (Z_to_bv 64 ty) (Z_to_bv 64 (lhSize + litCSize)) (Z_to_bv 64 DCTX) xs9 xs10 x28 x29 x30 x31).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dl_hufw : forall m2 hufv lev wsv litSize litCSize lhSize four ty A loc dtb (dha xra x5 x6 x7 xa0 xa1 xa3 xa4 xa6 xa7 x28 x29 x30 x31 : word),
    DLB hufv lev wsv m2 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    wnth wsv H5_litBuffer = Z_to_bv 64 A -> wnth wsv H5_litBufferEnd = Z_to_bv 64 (A + litSize) -> wnth wsv H5_litBufferLocation = Z_to_bv 64 loc ->
    bytes_at bsegs m2 (DCTX + 10296) dtb -> huf_hdr_ok dtb -> (ty = 3 -> huf_tbl_ok dtb) -> hufv = Z_to_bv 64 (DCTX + 10296) ->
    3 <= lhSize <= 5 -> 0 <= litCSize -> lhSize + litCSize <= zlen src -> 0 <= litSize <= Z.min (fh_bsmax h) CAP ->
    (four = 0 \/ (four = 1 /\ 6 <= litSize)) -> (ty = 2 \/ ty = 3) ->
    ((loc = 0 /\ A = DCTX + 30372 /\ litSize <= 65536)
     \/ (loc = 1 /\ 0 < CAP /\ DST <= A /\ A + litSize + 32 <= DST + CAP)
     \/ (loc = 2 /\ 65536 < litSize /\ 0 < CAP /\ DST <= A /\ A + litSize <= DST + CAP)) ->
    evtF bsegs RNG POST (ST 0x87b0c m2 xra x5 x6 x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize)
                           xa0 xa1 (Z_to_bv 64 LSRC) xa3 xa4 (Z_to_bv 64 DCTX) xa6 xa7
                           (Z_to_bv 64 litCSize) (Z_to_bv 64 lhSize) (Z_to_bv 64 four) (Z_to_bv 64 ty) (Z_to_bv 64 (lhSize + litCSize))
                           (Z_to_bv 64 DCTX) dha (Z_to_bv 64 LSRC) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I KEEP ELB ELE ELOC HTB HOK TOK HUFE LHR LCS LHS LSR FOUR TYR PL3. pose proof I as DLI. open_dlb I. dl_open CTX.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold KHIGH in KHI.
    pose proof (ARD ltac:(clear; lia)) as (ABD & _ & RDc & RDS). pose proof (fk_ablk_lits _ _ ABD) as DL.
    assert (DG : DCTX mod 8 = 0 /\ 0 <= DCTX /\ DCTX + 95992 <= 2^47) by (clear - DCA DCL DCH; lia).
    assert (NZ : 0 < zlen src) by (clear - LHR LCS LHS; lia).
    assert (PL : (0 < CAP /\ DST <= A /\ A + litSize <= DST + CAP) \/ (A = DCTX + 30372 /\ litSize <= 65536)) by (clear - PL3; lia).
    pose proof (proj2 H5) as L5. destruct H5 as [H5C _].
    fk_hold OFFD. fk_hold OFFB. fk_hold OFFSRC. fk_hold BD. fk_hold BSRC. fk_hold SRCD. fk_hold DNULL. fk_hold DNN. fk_hold ADST. fk_hold AIS. fk_hold US. fk_hold UB.
    fk_hold KEEP. fk_hold MU. fk_hold FFR. fk_hold DLI. fk_hold DL. fk_hold FOUR. fk_hold TYR. fk_hold PL3. fk_hold PL. fk_hold TOK. fk_hold PJOIN.
    fk_hold H1X. fk_hold H4X. fk_hold H1W. fk_hold H4W.
    h5_open wsv L5.
    lazymatch type of ELB with ?x = _ => subst x end. lazymatch type of ELE with ?x = _ => subst x end. lazymatch type of ELOC with ?x = _ => subst x end.
    subst hufv.
    zstep. zstep. zstep.                                   (* [comment removed for export] *)
    unfold fk_held in TYR. destruct TYR as [-> | ->].
    - (* [comment removed for export] *)
      zstep. if_true.
      zstep. zstep. zstep. dl_chk m2 (DCTX + 30352) UD RDS DG.    (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.                 (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      unfold fk_held in FOUR. destruct FOUR as [-> | [-> F6]].
      + (* [comment removed for export] *)
        zstep. if_true.
        zstep.                                             (* [comment removed for export] *)
        unfold fk_held in DLI, PL, H1W.
        eapply (dl_callF APHUF_1X1_WKSP 5984 0x87cc8);
          [ exact H1W | clear; lia | clear; lia | reflexivity | exact DLI | exact NZ | exact LHR | exact LCS | exact LHS | exact LSR | exact HTB | exact HOK | exact PL |].
        intros m' r dtb' y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 DLI' HTB' HOK' VAL' RES RR.
        zstep.                                             (* [comment removed for export] *)
        unfold fk_held in KEEP, PL3, PJOIN.
        eapply (PJOIN m' _ lev _ litSize litCSize lhSize 2 A loc r dtb');
          [ exact DLI' | exact KEEP | reflexivity | reflexivity | reflexivity | exact HTB' | exact HOK' | exact VAL' | reflexivity
          | exact LHR | exact LCS | exact LHS | exact LSR | left; reflexivity | exact RR | exact PL3 ].
      + (* [comment removed for export] *)
        zstep. if_false.
        zstep.                                             (* [comment removed for export] *)
        unfold fk_held in DLI, PL, H4W.
        eapply (dl_callF APHUF_4X_WKSP 6000 0x87cc0);
          [ exact H4W | clear; lia | clear; lia | reflexivity | exact DLI | exact NZ | exact LHR | exact LCS | exact LHS | exact LSR | exact HTB | exact HOK | exact PL |].
        intros m' r dtb' y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 DLI' HTB' HOK' VAL' RES RR.
        zstep.                                             (* [comment removed for export] *)
        unfold fk_held in KEEP, PL3, PJOIN.
        eapply (PJOIN m' _ lev _ litSize litCSize lhSize 2 A loc r dtb');
          [ exact DLI' | exact KEEP | reflexivity | reflexivity | reflexivity | exact HTB' | exact HOK' | exact VAL' | reflexivity
          | exact LHR | exact LCS | exact LHS | exact LSR | left; reflexivity | exact RR | exact PL3 ].
    - (* [comment removed for export] *)
      zstep. if_false.
      zstep. zstep. zstep. dl_chk m2 (DCTX + 30352) UD RDS DG.      (* [comment removed for export] *)
      zstep. zstep. zstep. dl_chk m2 (DCTX + 24) UD RDS DG.        (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
      unfold fk_held in TOK. specialize (TOK eq_refl).
      unfold fk_held in FOUR. destruct FOUR as [-> | [-> F6]].
      + (* [comment removed for export] *)
        zstep. if_true.
        zstep.                                             (* [comment removed for export] *)
        unfold fk_held in DLI, PL, H1X.
        eapply (dl_callL APHUF_1X HUF_1X_STACK_A 0x87cd0);
          [ exact H1X | clear; lia | clear; lia | reflexivity | exact DLI | exact NZ | exact LHR | exact LCS | exact LHS | exact LSR | exact HTB | exact HOK | exact TOK | exact PL |].
        intros m' r y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 DLI' HTB' RES RR.
        unfold fk_held in KEEP, PL3, PJOIN.
        eapply (PJOIN m' _ lev _ litSize litCSize lhSize 3 A loc r dtb);
          [ exact DLI' | exact KEEP | reflexivity | reflexivity | reflexivity | exact HTB' | exact HOK | intros _; exact TOK | reflexivity
          | exact LHR | exact LCS | exact LHS | exact LSR | right; reflexivity | exact RR | exact PL3 ].
      + (* [comment removed for export] *)
        zstep. if_false.
        zstep.                                             (* [comment removed for export] *)
        unfold fk_held in DLI, PL, H4X.
        eapply (dl_callL APHUF_4X HUF_4X_STACK_A 0x87b64);
          [ exact H4X | clear; lia | clear; lia | reflexivity | exact DLI | exact NZ | exact LHR | exact LCS | exact LHS | exact LSR | exact HTB | exact HOK | exact TOK | exact PL |].
        intros m' r y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 DLI' HTB' RES RR.
        zstep.                                             (* [comment removed for export] *)
        unfold fk_held in KEEP, PL3, PJOIN.
        eapply (PJOIN m' _ lev _ litSize litCSize lhSize 3 A loc r dtb);
          [ exact DLI' | exact KEEP | reflexivity | reflexivity | reflexivity | exact HTB' | exact HOK | intros _; exact TOK | reflexivity
          | exact LHR | exact LCS | exact LHS | exact LSR | right; reflexivity | exact RR | exact PL3 ].
  Qed.

  (* [comment removed for export] *)
  Lemma dl_huf : forall m2 hufv lev wsv litSize litCSize lhSize four ty dha (xra x5 x6 x7 xa0 xa1 xa3 xa4 xa6 xa7 x28 x29 x30 x31 : word),
    DLB hufv lev (h5_placed wsv DCTX DST (alloc_lit_buffer (fh_bsmax h) CAP litSize (Z.min (fh_bsmax h) CAP) false)) m2 ->
    wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m2 DCTX hufv lev ->
    3 <= lhSize <= 5 -> 0 <= litCSize -> lhSize + litCSize <= zlen src -> 0 <= litSize <= Z.min (fh_bsmax h) CAP -> (DST = 0 -> litSize = 0) ->
    (four = 0 \/ (four = 1 /\ 6 <= litSize)) -> (ty = 2 \/ (ty = 3 /\ bv_unsigned lev mod 2^32 <> 0)) ->
    evtF bsegs RNG POST (ST 0x87b0c m2 xra x5 x6 x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize)
                           xa0 xa1 (Z_to_bv 64 LSRC) xa3 xa4 (Z_to_bv 64 DCTX) xa6 xa7
                           (Z_to_bv 64 litCSize) (Z_to_bv 64 lhSize) (Z_to_bv 64 four) (Z_to_bv 64 ty) (Z_to_bv 64 (lhSize + litCSize))
                           (Z_to_bv 64 DCTX) dha (Z_to_bv 64 LSRC) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I ISFv KEEP HW LHR LCS LHS LSR DNL FOUR TY. dl_open CTX.
    pose proof I as (_ & EHUF & _ & _ & _ & H5 & _).
    destruct (hufw_full _ _ _ _ HW EHUF) as (dtb & HTB & HOK & TOKl). pose proof HW as (HUFE & _).
    assert (TOK : ty = 3 -> huf_tbl_ok dtb) by (intros E3; apply TOKl; destruct TY as [E2|[_ NZL]]; [exfalso; clear - E2 E3; lia| exact NZL]).
    assert (TYR : ty = 2 \/ ty = 3) by (clear - TY; lia).
    assert (L5 : length wsv = 44%nat) by (pose proof (proj2 H5) as Lq; unfold h5_placed in Lq; rewrite !dl_wupd_length in Lq; exact Lq).
    set (ews := Z.min (fh_bsmax h) CAP) in *.
    pose proof (alloc_lit_buffer_regions (fh_bsmax h) CAP litSize ews false LSR eq_refl ltac:(unfold ZSTD_BLOCKSIZE_MAX; clear - BSM; lia)) as REG.
    set (p := alloc_lit_buffer (fh_bsmax h) CAP litSize ews false) in *.
    unfold h5_placed in I. h5_open wsv L5.
    cbv zeta iota in REG. unfold ZSTD_in_dst, ZSTD_split, ZSTD_not_in_dst, WILDCOPY_OVERLENGTH, ZSTD_LITBUFFEREXTRASIZE in REG.
    destruct (lp_base p) eqn:EB; [ | | contradiction].
    - cbn [lit_base_addr] in I. destruct REG as [(ELOC & EBUF & EEND & EFIT) | (ELOC & BIG & BUF0 & (EEND & EEWS) & EWC)].
      + (* [comment removed for export] *)
        rewrite EEND, ELOC in I. replace (DST + (lp_buf p + litSize)) with (DST + lp_buf p + litSize) in I by (clear; lia).
        eapply (dl_hufw m2 hufv lev _ litSize litCSize lhSize four ty (DST + lp_buf p) 1 dtb);
          [ exact I | intros i Hi; specialize (KEEP i Hi); do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]); exact KEEP | reflexivity | reflexivity | reflexivity | exact HTB | exact HOK | exact TOK | exact HUFE
          | exact LHR | exact LCS | exact LHS | exact LSR | exact FOUR | exact TYR | right; left; clear - EBUF EEND EFIT LSR BSM; lia ].
      + (* [comment removed for export] *)
        rewrite EEND, ELOC in I. replace (DST + (lp_buf p + litSize)) with (DST + lp_buf p + litSize) in I by (clear; lia).
        eapply (dl_hufw m2 hufv lev _ litSize litCSize lhSize four ty (DST + lp_buf p) 2 dtb);
          [ exact I | intros i Hi; specialize (KEEP i Hi); do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]); exact KEEP | reflexivity | reflexivity | reflexivity | exact HTB | exact HOK | exact TOK | exact HUFE
          | exact LHR | exact LCS | exact LHS | exact LSR | exact FOUR | exact TYR | right; right; clear - BIG BUF0 EEND EEWS EWC LSR BSM; lia ].
    - (* [comment removed for export] *)
      cbn [lit_base_addr] in I. unfold DCTX_litExtraBuffer in I. destruct REG as (ELOC & EBUF & EEND & SMALL).
      rewrite EEND, ELOC, EBUF in I. replace (DCTX + 30372 + 0) with (DCTX + 30372) in I by (clear; lia).
      eapply (dl_hufw m2 hufv lev _ litSize litCSize lhSize four ty (DCTX + 30372) 0 dtb);
        [ exact I | intros i Hi; specialize (KEEP i Hi); do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]); exact KEEP | reflexivity | reflexivity | reflexivity | exact HTB | exact HOK | exact TOK | exact HUFE
        | exact LHR | exact LCS | exact LHS | exact LSR | exact FOUR | exact TYR | left; clear - SMALL; lia ].
  Qed.
End DL.
End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
