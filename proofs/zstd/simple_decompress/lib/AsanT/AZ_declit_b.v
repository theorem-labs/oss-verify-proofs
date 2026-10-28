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
     AZ_globals AZ_globalsR AZ_frame_iface AZ_huf_iface AZ_block_iface AZ_blk_iface4 AZ_blk_iface5 AZ_libc_iface AZ_hufinv AZ_kx AZ_declit_a.
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
  Hypothesis ALLOCLIT : zd_alloclit_stmtA.
  Hypothesis MEMCPY : zd_memcpyZ_stmtA.

  Ltac hlia := unfold fk_held in *; lia.
  (* [comment removed for export] *)
  Ltac nrm_not_by tac := match goal with |- context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) by tac end.

  (* [comment removed for export] *)
  Lemma dlb_keep : forall hufv' lev' ws1 ws2 (ma mb : amem) W,
    DLB hufv' lev' ws1 ma ->
    munch W ma mb -> wmono bsegs ma mb -> mem_inv bsegs mb -> stk bsegs mb lo (SPV + -96) -> dctx_h5 bsegs mb DCTX ws2 ->
    Forall (fun iv => fst iv <= snd iv /\ ((DCTX + 30096 <= fst iv /\ snd iv <= DCTX + 30372) \/ (SPV - 6096 <= fst iv /\ snd iv <= SPV + -96))) W ->
    DLB hufv' lev' ws2 mb.
  Proof.
    intros hufv' lev' ws1 ws2 ma mb W I MUx WMx MIx STKx H5x HW. dl_open CTX.
      pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold KHIGH in KHI.
      pose proof (ARD ltac:(clear; lia)) as (ABD & _). pose proof (fk_ablk_lits _ _ ABD) as DL.
      unfold AZ_declit_a.DLB in I. destruct I as (PTRS & EHUF & EWK & FP & H3 & H5 & XB & SRCB & BUF & STK & FRA & MI & MU & WM & AH & FFR & UD & US & UB & ARO & AZS).
      pose proof (bytes_at_bound _ _ _ _ SRCB) as SBL. rewrite length_map in SBL.
      assert (DJ : forall X n, 0 <= n -> (X + n <= DCTX + 30096 \/ DCTX + 30372 <= X) -> (X + n <= SPV - 6096 \/ SPV + -96 <= X) -> disjoint_from W X n).
      { intros X n Hn A B. clear - HW Hn A B. induction HW as [|[x y] W [Hle Hc] HW IH]; cbn; [exact I|]. cbn in Hle, Hc. split; [lia| exact IH]. }
      assert (DJS : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from W (shad X) (shad (X + n - 1) + 1 - shad X)).
      { intros X n A B C. rewrite !shad_div. unfold ASHOFF. apply DJ; clear - A B C DL KHI LOS ATR; Z.div_mod_to_equations; lia. }
      assert (AW : aappW W).
      { unfold aappW. clear - HW DL KHI LOS SPH ATR. induction HW as [|[x y] W [Hle Hc] HW IH]; [apply Forall_nil|]. apply Forall_cons; [| exact IH].
        cbn [fst snd] in *. unfold KLOW, KHIGH. lia. }
      unfold dctx_ptrs, dctx_h3, zfh_cells in *.
      split; [eapply rw_cells_transport; [exact PTRS| exact MUx| exact WMx| apply DJ; cbn; clear - DL LOS OFFD; lia]|].
      split; [eapply stk_transport_disjoint; [exact EHUF| exact MUx| exact WMx| apply DJ; clear - DL LOS OFFD; lia]|].
      split; [eapply stk_transport_disjoint; [exact EWK| exact MUx| exact WMx| apply DJ; clear - DL LOS OFFD; lia]|].
      split; [eapply rw_cells_transport; [exact FP| exact MUx| exact WMx| apply DJ; cbn; clear - DL LOS OFFD; lia]|].
      split; [eapply rw_cells_transport; [exact H3| exact MUx| exact WMx| apply DJ; cbn; clear - DL LOS OFFD; lia]|].
      split; [exact H5x|].
      split; [eapply stk_transport_disjoint; [exact XB| exact MUx| exact WMx| apply DJ; clear - DL LOS OFFD; lia]|].
      split; [eapply bytes_at_transport; [exact SRCB| exact MUx| rewrite length_map; apply DJ; [clear - SBL| clear - SRCD| clear - OFFSRC LOS]; lia]|].
      split; [eapply stk_transport_disjoint; [exact BUF| exact MUx| exact WMx| apply DJ; [clear - B0D DCB CAP0| clear - BD| clear - OFFB LOS]; lia]|].
      split; [exact STKx|].
      split; [eapply rw_cells_transport; [exact FRA| exact MUx| exact WMx| apply DJ; cbn; clear - DL LOS OFFD; lia]|].
      split; [exact MIx|].
      split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUx]]; unfold sub_fp; intros x Hx; apply (proj1 (fk_outside_app _ _ _)) in Hx; destruct Hx as [Hx _];
              clear - Hx HW; induction HW as [|[u v] W [Hle Hc] HW IH]; cbn; [exact I|]; cbn in Hle, Hc, Hx; unfold outside in Hx; cbn in Hx; split; [lia| exact IH]|].
      split; [exact (wmono_trans _ _ _ _ WM WMx)|].
      assert (AHx : AHEAP AI L RNG st LB mb).
      { eapply (AI_frame AI); [exact AH| exact MUx| exact WMx|]. clear - HW AID BOT SPH LOS. induction HW as [|[x y] W [Hle Hc] HW IH]; [apply Forall_nil|].
        apply Forall_cons; [| exact IH]. cbn [fst snd] in *. destruct Hc as [Hc|Hc].
        - apply fk_acr_inblk. destruct AID as (bb & Hb & Hb1 & Hb2). exists bb. split; [exact Hb| clear - Hle Hc Hb1 Hb2; lia].
        - eapply fk_acr_stack; [exact BOT| clear - Hc LOS; lia| clear - Hc Hle SPH; lia]. }
      split; [exact AHx|].
      split.
      { eapply ffr_pres_trans; [exact FFR|].
        eapply dl_ffr_pres_weaken.
        - eapply (dl_ffr_pres_app1 AI L RNG st LB ma mb [(DCTX + 30096, DCTX + 30372)] W); [exact AH| exact LBH| | exact MUx| exact WMx].
          clear - HW OFFD BOT SPH LOS ABD. induction HW as [|[x y] W [Hle Hc] HW IH]; [apply Forall_nil|]. apply Forall_cons; [| exact IH]. cbn [fst snd] in *.
          split; [exact Hle|]. destruct Hc as [Hc|Hc].
          + right. split; [exists DCTX, (DCTX + 95992); split; [exact ABD| clear - Hle Hc; lia]|]. exists (DCTX + 30096, DCTX + 30372). split; [left; reflexivity| cbn [fst snd]; clear - Hc; lia].
          + left. clear - Hc Hle BOT LOS SPH. lia.
        - unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx. lia. }
      split; [eapply unpoisoned_munch; [exact UD| exact MUx| apply DJS; clear - DL ATR; lia]|].
      split; [intros NZ; eapply unpoisoned_munch; [exact (US NZ)| exact MUx| apply DJS; clear - SRCL SRCH NZ; lia]|].
      pose proof BUF as (B00 & _).
      split; [intros NZ; eapply unpoisoned_munch; [exact (UB NZ)| exact MUx| replace B1 with (B0 + (B1 - B0)) at 1 by (clear; lia); apply DJS; clear - NZ B1H B00; lia]|].
      split; [eapply aro_client_transport; [exact ARO| exact MUx| exact WMx| exact AW]|].
      eapply azstk_transport; [exact AZS| exact MUx| exact WMx| exact AW| clear - LOS; lia].
  Qed.

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
  Lemma dlb_keep2 : forall hufv' lev' ws1 (ma mb : amem) W,
    DLB hufv' lev' ws1 ma ->
    munch W ma mb -> wmono bsegs ma mb -> mem_inv bsegs mb -> stk bsegs mb lo (SPV + -96) ->
    stk bsegs mb B0 B1 -> stk bsegs mb (DCTX + 30372) (DCTX + 95940) ->
    Forall (fun iv => fst iv <= snd iv /\ ((0 < CAP /\ DST <= fst iv /\ snd iv <= DST + CAP) \/ (DCTX + 30372 <= fst iv /\ snd iv <= DCTX + 95940)
                                           \/ (SPV - 6096 <= fst iv /\ snd iv <= SPV + -96))) W ->
    DLB hufv' lev' ws1 mb.
  Proof.
    intros hufv' lev' ws1 ma mb W I MUx WMx MIx STKx BUFx XBx HW. dl_open CTX.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold KHIGH in KHI.
    pose proof (ARD ltac:(clear; lia)) as (ABD & _). pose proof (fk_ablk_lits _ _ ABD) as DL.
    unfold AZ_declit_a.DLB in I. destruct I as (PTRS & EHUF & EWK & FP & H3 & H5 & XB & SRCB & BUF & STK & FRA & MI & MU & WM & AH & FFR & UD & US & UB & ARO & AZS).
    pose proof (bytes_at_bound _ _ _ _ SRCB) as SBL. rewrite length_map in SBL. pose proof BUF as (B00 & _).
    assert (DBL : 0 < CAP -> 6443008 <= B0 /\ B1 <= ATOP /\ (B1 <= KLOW \/ KHIGH <= B0)).
    { intros HC. destruct (ADST ltac:(clear - HC B0D DCB; lia)) as (ARb & _). destruct (ARb ltac:(clear - HC B0D DCB; lia)) as (ABb & _).
      pose proof (fk_ablk_lits _ _ ABb) as X. pose proof (ablk_disj_band _ _ ABb) as Y. unfold KLS, KLOW, KHIGH in *. clear - X Y HC; lia. }
    assert (DJ : forall X n, 0 <= n -> (0 < CAP -> X + n <= DST \/ DST + CAP <= X) -> (X + n <= DCTX + 30372 \/ DCTX + 95940 <= X) -> (X + n <= SPV - 6096 \/ SPV + -96 <= X) ->
                 disjoint_from W X n).
    { intros X n Hn A B C. clear - HW Hn A B C. induction HW as [|[x y] W [Hle Hc] HW IH]; cbn; [exact I|]. cbn in Hle, Hc. split; [| exact IH].
      destruct Hc as [(HC & Hx & Hy)|[[Hx Hy]|[Hx Hy]]]; [specialize (A HC); lia| lia| lia]. }
    assert (DJS : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from W (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X n A B C. rewrite !shad_div. unfold ASHOFF. unfold KLOW, KHIGH in DBL. apply DJ; [| intros HC; specialize (DBL HC)| |]; clear - A B C DL DBL KHI LOS ATR B0D DCB; Z.div_mod_to_equations; lia. }
    assert (AW : aappW W).
    { unfold aappW. clear - HW DL DBL KHI LOS SPH ATR B0D DCB. induction HW as [|[x y] W [Hle Hc] HW IH]; [apply Forall_nil|]. apply Forall_cons; [| exact IH].
      cbn [fst snd] in *. unfold KLOW, KHIGH in *. destruct Hc as [(HC & Hx & Hy)|[[Hx Hy]|[Hx Hy]]]; [specialize (DBL HC); lia| lia| lia]. }
    unfold dctx_ptrs, dctx_h3, zfh_cells in *.
    split; [eapply rw_cells_transport; [exact PTRS| exact MUx| exact WMx| apply DJ; cbn; [clear| clear - BD B0D DCB| clear| clear - DL LOS OFFD]; lia]|].
    split; [eapply stk_transport_disjoint; [exact EHUF| exact MUx| exact WMx| apply DJ; [clear| clear - BD B0D DCB| clear| clear - DL LOS OFFD]; lia]|].
    split; [eapply stk_transport_disjoint; [exact EWK| exact MUx| exact WMx| apply DJ; [clear| clear - BD B0D DCB| clear| clear - DL LOS OFFD]; lia]|].
    split; [eapply rw_cells_transport; [exact FP| exact MUx| exact WMx| apply DJ; cbn; [clear| clear - BD B0D DCB| clear| clear - DL LOS OFFD]; lia]|].
    split; [eapply rw_cells_transport; [exact H3| exact MUx| exact WMx| apply DJ; cbn; [clear| clear - BD B0D DCB| clear| clear - DL LOS OFFD]; lia]|].
    split; [destruct H5 as [H5C H5L]; split; [| exact H5L]; eapply rw_cells_transport; [exact H5C| exact MUx| exact WMx| rewrite (h5_cells_size _ H5L); apply DJ; cbn; [clear| clear - BD B0D DCB| clear| clear - DL LOS OFFD]; lia]|].
    split; [exact XBx|].
    split; [eapply bytes_at_transport; [exact SRCB| exact MUx| rewrite length_map; apply DJ; [clear - SBL| clear - BSRC B0D DCB| clear - SRCD| clear - OFFSRC LOS]; lia]|].
    split; [exact BUFx|]. split; [exact STKx|].
    split; [eapply rw_cells_transport; [exact FRA| exact MUx| exact WMx| apply DJ; cbn; [clear| clear - OFFB B0D DCB LOS| clear - OFFD LOS| clear]; lia]|].
    split; [exact MIx|].
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUx]]; unfold sub_fp; intros x Hx; apply (proj1 (fk_outside_app _ _ _)) in Hx; destruct Hx as [Hx _];
            clear - Hx HW; induction HW as [|[u v] W [Hle Hc] HW IH]; cbn; [exact I|]; cbn in Hle, Hc, Hx; unfold outside in Hx; cbn in Hx; split; [lia| exact IH]|].
    split; [exact (wmono_trans _ _ _ _ WM WMx)|].
    assert (AHx : AHEAP AI L RNG st LB mb).
    { eapply (AI_frame AI); [exact AH| exact MUx| exact WMx|]. clear - HW AID ADST BOT SPH LOS B0D DCB. induction HW as [|[x y] W [Hle Hc] HW IH]; [apply Forall_nil|].
      apply Forall_cons; [| exact IH]. cbn [fst snd] in *. destruct Hc as [(HC & Hx & Hy)|[[Hx Hy]|[Hx Hy]]].
      - apply fk_acr_inblk. destruct (ADST ltac:(clear - HC B0D DCB; lia)) as (_ & _ & bb & Hb & Hb1 & Hb2). exists bb. split; [exact Hb| clear - Hle Hx Hy Hb1 Hb2 B0D DCB; lia].
      - apply fk_acr_inblk. destruct AID as (bb & Hb & Hb1 & Hb2). exists bb. split; [exact Hb| clear - Hle Hx Hy Hb1 Hb2; lia].
      - eapply fk_acr_stack; [exact BOT| clear - Hx LOS; lia| clear - Hy Hle SPH; lia]. }
    split; [exact AHx|].
    split.
    { eapply ffr_pres_trans; [exact FFR|].
      eapply (dl_ffr_pres_app1 AI L RNG st LB ma mb _ W); [exact AH| exact LBH| | exact MUx| exact WMx].
      clear - HW BOT SPH LOS ABD ADST B0D DCB. induction HW as [|[x y] W [Hle Hc] HW IH]; [apply Forall_nil|]. apply Forall_cons; [| exact IH]. cbn [fst snd] in *.
      split; [exact Hle|]. destruct Hc as [(HC & Hx & Hy)|[[Hx Hy]|[Hx Hy]]].
      + right. destruct (ADST ltac:(clear - HC B0D DCB; lia)) as (ARb & _). destruct (ARb ltac:(clear - HC B0D DCB; lia)) as (ABb & _).
        split; [exists B0, (B0 + (B1 - B0)); split; [exact ABb| clear - Hx Hy B0D DCB; lia]|]. exists (DST, DST + CAP). split; [left; reflexivity| cbn [fst snd]; clear - Hx Hy; lia].
      + right. split; [exists DCTX, (DCTX + 95992); split; [exact ABD| clear - Hx Hy; lia]|]. exists (DCTX + 30096, DCTX + 95940). split; [do 5 right; left; reflexivity| cbn [fst snd]; clear - Hx Hy; lia].
      + left. clear - Hx Hy Hle BOT LOS SPH. lia. }
    split; [eapply unpoisoned_munch; [exact UD| exact MUx| apply DJS; clear - DL ATR; lia]|].
    split; [intros NZ; eapply unpoisoned_munch; [exact (US NZ)| exact MUx| apply DJS; clear - SRCL SRCH NZ; lia]|].
    split; [intros NZ; eapply unpoisoned_munch; [exact (UB NZ)| exact MUx| replace B1 with (B0 + (B1 - B0)) at 1 by (clear; lia); apply DJS; clear - NZ B1H B00; lia]|].
    split; [eapply aro_client_transport; [exact ARO| exact MUx| exact WMx| exact AW]|].
    eapply azstk_transport; [exact AZS| exact MUx| exact WMx| exact AW| clear - LOS; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma dl_raw : forall m1 hufv lev wsv litSize lhSize xra x5 x7 xa6 xs2 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m1 DCTX hufv lev ->
    1 <= lhSize <= 3 -> 0 <= litSize <= Z.min (fh_bsmax h) CAP -> (DST = 0 -> litSize = 0) ->
    evtF bsegs RNG POST (ST 0x878b4 m1 xra x5 (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize)
                           (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                           xa6 (Z_to_bv 64 (Z.min (fh_bsmax h) CAP)) xs2 (Z_to_bv 64 lhSize) xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I ISFv KEEP HW LHR LSR DNL. pose proof I as DLI. open_dlb I. dl_open CTX.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold KHIGH in KHI.
    pose proof (ARD ltac:(clear; lia)) as (ABD & _ & RDc & RDS). pose proof (fk_ablk_lits _ _ ABD) as DL.
    pose proof (bytes_at_bound _ _ _ _ SRCB) as SBL. rewrite length_map in SBL.
    assert (DG : DCTX mod 8 = 0 /\ 0 <= DCTX /\ DCTX + 95992 <= 2^47) by (clear - DCA DCL DCH; lia).
    pose proof (proj2 H5) as L5.
    fk_hold OFFD. fk_hold OFFB. fk_hold OFFSRC. fk_hold BD. fk_hold BSRC. fk_hold SRCD. fk_hold DNULL. fk_hold DNN. fk_hold ADST. fk_hold AIS. fk_hold US. fk_hold UB.
    fk_hold KEEP. fk_hold MU. fk_hold FFR. fk_hold DLI. fk_hold HW. fk_hold DNL. fk_hold DL.
    do 9 zstep.                                            (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (ART1 : art m1) by exact (dl_art_of_aheap AI _ _ _ _ _ AH).
    unfold zd_alloclit_stmtA, APZD_ALLOCLIT in ALLOCLIT.
    eapply evtF_cut.
    { eapply (ALLOCLIT RNG) with (SPV := SPV + -96) (lo := lo) (DCTX := DCTX) (DST := DST) (CAP := CAP) (litSize := litSize) (ews := Z.min (fh_bsmax h) CAP) (imm := true) (h := h) (ws := wsv);
        first [ exact FP | exact BSM | exact H5 | exact ISFv | exact DCL | exact DCH | exact DCA | exact STK | exact ART1 | exact MI | reflexivity
              | lazymatch goal with
                | |- 0 <= DST => clear - B0D DNULL DNN; hlia
                | |- 0 <= CAP => exact CAP0
                | |- DST + CAP < _ => clear - DCB B1H; hlia
                | |- DST = 0 -> CAP = 0 => clear - DNULL; hlia
                | |- 0 <= litSize <= _ => exact LSR
                | |- lo <= SPV + -96 - _ => clear - LOS; hlia
                | |- 0 <= SPV + -96 < _ => clear - LOS LO0 SPH; hlia
                | |- SPV + -96 < _ => clear - SPH; hlia
                | |- AZ_blk_iface.off_stack _ _ _ _ => unfold AZ_blk_iface.off_stack; clear - OFFD; hlia
                | |- areg _ _ DCTX _ => intros _; split; [exact ABD| split; [exact UD| split; [exact RDc| exact RDS]]]
                | |- astk _ _ _ => split; [unfold KHIGH; clear - KHI; hlia| split; [eapply rng_sub'; [exact RSTK| clear - LOS; hlia]| exact RI]]
                end ]. }
    clear ALLOCLIT. cbv beta. intros ms' (c0 & c1 & c2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & c3 & c4 & c5 & c6 & m2 & -> & MUc & WMc & MI2 & STK2 & H52).
    unfold fk_held in DLI.
    pose proof (dlb_keep hufv lev wsv _ m1 m2 _ DLI MUc WMc MI2 STK2 H52
                  ltac:(unfold DCTX_litBuffer; apply Forall_cons; [cbn [fst snd]; clear; lia|]; apply Forall_cons; [cbn [fst snd]; clear - LOS; hlia| apply Forall_nil])) as DLI2.
    assert (HW2 : HUFINVw m2 DCTX hufv lev).
    { unfold fk_held in HW. eapply hufw_fine; [exact HW| exact MUc|]. unfold DCTX_litBuffer. cbn [outside]. intros x Hx. clear - Hx LOS OFFD; hlia. }
    clear PTRS EHUF EWK FP H3 H5 XB SRCB BUF STK FRA MI MU WM AH FFR UD ARO AZS ART1 MUc WMc STK2 H52 DLI HW US UB.
    pose proof DLI2 as I. open_dlb I. fk_hold DLI2. fk_hold HW2. fk_hold MU. fk_hold FFR. fk_hold US. fk_hold UB.
    (* [comment removed for export] *)
    h5_open wsv L5. lazymatch type of ISFv with ?x = _ => subst x end.
    set (ews := Z.min (fh_bsmax h) CAP) in *.
    pose proof (alloc_lit_buffer_regions (fh_bsmax h) CAP litSize ews true LSR eq_refl ltac:(unfold ZSTD_BLOCKSIZE_MAX; clear - BSM; lia)) as REG.
    set (p := alloc_lit_buffer (fh_bsmax h) CAP litSize ews true) in *.
    destruct H5 as [H5C _].
    cbv [h5_placed h5_cells mk_wcells h5_sizes wupd H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in H5C.
    set (LBv := lit_base_addr DCTX DST (lp_base p) + lp_buf p) in *. set (LEv := lit_base_addr DCTX DST (lp_base p) + lp_end p) in *.
    assert (UDm : forall mm, munch [(DCTX + 30096, DCTX + 30372)] m2 mm -> unpoisoned mm DCTX (DCTX + 95992)).
    { intros mm MUm. eapply unpoisoned_munch; [exact UD| exact MUm|]. cbn [disjoint_from]. split; [| exact I]. rewrite !shad_div. unfold ASHOFF. clear - DL ATR; hlia. }
    pose proof (munch_refl [(DCTX + 30096, DCTX + 30372)] m2) as MUs. pose proof (wmono_refl bsegs m2) as WMs.
    replace (ret_pc (Z_to_bv 64 0x878dc)) with (Z_to_bv 64 0x878dc) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    zstep. zstep. zstep.                                   (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      clear PTRS EHUF EWK FP H3 XB SRCB BUF STK FRA AH ARO AZS.
      zstep. zstep. zstep. dl_chk m2 (DCTX + 30120) UD RDS DG.
      zstep. zstep.                                        (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep. zstep. lazymatch type of MUs with munch _ _ ?mm => dl_chk mm (DCTX + 30152) (UDm mm MUs) RDS DG end.
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep. zstep. lazymatch type of MUs with munch _ _ ?mm => dl_chk mm (DCTX + 30360) (UDm mm MUs) RDS DG end.
      zstep. zstep.                                        (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep. zstep. lazymatch type of MUs with munch _ _ ?mm => dl_chk mm (DCTX + 30368) (UDm mm MUs) RDS DG end.
      zstep.                                               (* [comment removed for export] *)
      zstep. zstep.                                        (* [comment removed for export] *)
      unfold fk_held in DLI2. pose proof DLI2 as I'. unfold AZ_declit_a.DLB in I'. destruct I' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & STK2 & _).
      lazymatch type of H5C with rw_cells _ ?mm _ ?cs => let wl := cells_words cs in
        assert (DLBx : AZ_declit_a.DLB AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe hufv lev wl mm);
        [ eapply (dlb_keep hufv lev _ wl m2 mm _ DLI2 MUs WMs MI);
          [ eapply stk_transport_disjoint; [exact STK2| exact MUs| exact WMs| cbn [disjoint_from]; clear - OFFD LOS; hlia]
          | split; [exact H5C| reflexivity]
          | apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil] ]
        | eapply (dl_ret mm hufv lev wl (lhSize + litSize)); [exact DLBx| clear - LHR LSR SLEN BSM; lia| | ] ] end.
      + unfold fk_held in KEEP. intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
      + right. split; [clear - LHR LSR KR; lia|]. split.
        { unfold fk_held in HW2. eapply hufw_fine; [exact HW2| exact MUs|]. cbn [outside]. intros x Hx. clear - Hx; lia. }
        exists (LSRC + lhSize), litSize, LBv, (LSRC + lhSize + litSize), 0.
        repeat (split; [first [reflexivity | clear - LSR BSM LHR; lia]|]). left. split; [reflexivity|]. split; [reflexivity|]. right. unfold WILDCOPY_OVERLENGTH. clear - KR LHR LSR; lia.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases K1; zify_cond K1.
      { (* [comment removed for export] *)
        unfold fk_held in DLI2. replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply Z_to_bv_eqm; reflexivity).
        eapply (dl_ret m2 hufv lev _ (2^64 - 20)); [exact DLI2| clear; lia| | left; reflexivity].
        unfold fk_held in KEEP. intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP. }
      zstep. zstep.                                        (* [comment removed for export] *)
      zstep. zstep. zstep. dl_chk m2 (DCTX + 30368) UD RDS DG.
      zstep. zstep. zstep. dl_chk m2 (DCTX + 30352) UD RDS DG.
      cbv zeta iota in REG. unfold ZSTD_in_dst, ZSTD_split, ZSTD_not_in_dst, WILDCOPY_OVERLENGTH, ZSTD_LITBUFFEREXTRASIZE in REG.
      destruct (lp_base p) eqn:EB; [ | | contradiction].
      + destruct REG as [(ELOC & EBUF & EEND & EFIT) | (ELOC & BIG & BUF0 & (EEND & EEWS) & EWC)].
        * (* [comment removed for export] *)
          subst LBv LEv. cbn [lit_base_addr] in H5C. rewrite ELOC, EEND, EBUF in H5C.
          zstep. rewrite (sx32w_small 1) by (clear; lia). zstep. zstep. zstep. zstep. if_true.      (* [comment removed for export] *)
          zstep. zstep.                                    (* [comment removed for export] *)
          (* [comment removed for export] *)
          assert (NZ : 0 < zlen src) by (clear - K1 LHR LSR; lia).
          assert (HC : 0 < CAP) by (clear - EFIT EEND EBUF LSR BSM; lia).
          unfold fk_held in ADST, US, UB, OFFB, OFFSRC, BSRC, BD.
          destruct (ADST ltac:(clear - HC B0D DCB; lia)) as (ARb & AHb & AIb). destruct (ARb ltac:(clear - HC B0D DCB; lia)) as (ABb & _ & RBa & RBb).
          pose proof (fk_ablk_lits _ _ ABb) as BBL.
          destruct (stk_open bsegs m2 B0 B1 (DST + (fh_bsmax h + 32)) (Z.to_nat litSize) BUF ltac:(clear - B0D BSM; lia) ltac:(rewrite Z2Nat.id by (clear - LSR; lia); clear - EFIT EEND EBUF DCB; lia)) as (jk & DSTC & BUFa & BUFb).
          rewrite Z2Nat.id in BUFb by (clear - LSR; lia).
          pose proof (dl_bytes_at_slice _ _ _ (Z.to_nat lhSize) (Z.to_nat litSize) SRCB ltac:(rewrite length_map; clear - K1 LHR LSR; lia)) as SL1.
          rewrite Z2Nat.id in SL1 by (clear - LHR; lia).
          assert (SL1L : length (firstn (Z.to_nat litSize) (skipn (Z.to_nat lhSize) (map (Z_to_bv 8) src))) = Z.to_nat litSize).
          { rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn, length_map. clear - K1 LHR LSR; lia. }
          assert (ART2 : art m2) by exact (dl_art_of_aheap AI _ _ _ _ _ AH).
          pose proof (ARS NZ) as (ABS & _ & RSa & RSb). pose proof (fk_ablk_lits _ _ ABS) as SBB.
          fk_hold BUFa. fk_hold BUFb. fk_hold H5C.
          zstep.                                           (* [comment removed for export] *)
          unfold zd_memcpyZ_stmtA in MEMCPY.
          eapply evtF_cut.
          { eapply (MEMCPY RNG (DST + (fh_bsmax h + 32)) (LSRC + lhSize) litSize (SPV + -96)) with (lo := lo);
              first [ exact SL1 | exact SL1L | exact DSTC | exact STK | exact ART2 | exact MI | reflexivity
                    | lazymatch goal with
                      | |- 0 <= litSize <= _ => clear - LSR BSM; lia
                      | |- lo <= SPV + -96 - _ => clear - LOS; lia
                      | |- SPV + -96 < _ => clear - SPH; lia
                      | |- LSRC + lhSize + litSize <= DST + _ \/ _ => clear - BSRC B0D DCB K1 EFIT EEND EBUF LHR BSM LSR; lia
                      | |- LSRC + lhSize + litSize <= SPV + -96 - _ \/ _ => clear - OFFSRC LOS K1 LHR; lia
                      | |- DST + _ + litSize <= lo \/ _ => clear - OFFB B0D DCB EFIT EEND EBUF LOS BSM LSR; lia
                      | |- app_blk (LSRC + _) _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABS| clear - LHR; lia| clear - K1; lia]| clear - LSR; lia]
                      | |- app_blk _ _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABb| clear - B0D BSM; lia| clear - DCB EFIT EEND EBUF; lia]| clear - LSR; lia]
                      | |- aro _ _ (LSRC + _) _ => split; [eapply unpoisoned_sub; [exact (US NZ)| clear - LHR; lia| clear - K1; lia]| split; [eapply rng_sub'; [exact RSa| clear - LHR K1; lia]| eapply rng_sub'; [exact RSb| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - LHR K1 LSR; Z.div_mod_to_equations; lia]]]
                      | |- aro _ _ _ _ => split; [eapply unpoisoned_sub; [exact (UB ltac:(clear - HC B0D DCB; lia))| clear - B0D BSM; lia| clear - DCB EFIT EEND EBUF; lia]| split; [eapply rng_sub'; [exact RBa| clear - B0D BSM DCB EFIT EEND EBUF; lia]| eapply rng_sub'; [exact RBb| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - B0D BSM DCB EFIT EEND EBUF LSR; Z.div_mod_to_equations; lia]]]
                      | |- ahull _ _ (LSRC + _) _ => eapply dl_ahull_sub; [eapply dl_ahull_wmono; [exact (AHS NZ)| exact WM]| clear - LHR; lia| clear - K1; lia]
                      | |- ahull _ _ _ _ => eapply dl_ahull_sub; [eapply dl_ahull_wmono; [exact AHb| exact WM]| clear - B0D BSM; lia| clear - DCB EFIT EEND EBUF; lia]
                      | |- astk _ _ _ => split; [unfold KHIGH; clear - KHI; lia| split; [eapply rng_sub'; [exact RSTK| clear - LOS; lia]| exact RI]]
                      end
                    | lazymatch goal with |- ?Gg => idtac "MEMCPY-LEFT:" Gg end ]. }
          cbv beta. intros ms' (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & -> & MU3 & WM3 & MI3 & STK3 & DSTC3 & SB3).
          replace (ret_pc (Z_to_bv 64 0x87c30)) with (Z_to_bv 64 0x87c30) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
          clear MEMCPY SL1 SL1L ART2.
          (* [comment removed for export] *)
          unfold fk_held in BUFa, BUFb, DLI2, H5C.
          pose proof (stk_of_rw_cells bsegs _ _ _ DSTC3) as DSTS3. cbn [cells_size csize length] in DSTS3. rewrite Nat.add_0_r, Z2Nat.id in DSTS3 by (clear - LSR; lia).
          assert (BUF3 : stk bsegs m3 B0 B1).
          { eapply stk_merge; [eapply stk_merge; [| exact DSTS3| clear - B0D BSM LSR; lia]| | clear - B0D BSM LSR DCB EFIT EEND EBUF; lia].
            - eapply stk_transport_disjoint; [exact BUFa| exact MU3| exact WM3| cbn [disjoint_from]; clear - OFFB B0D DCB LOS EFIT EEND EBUF LSR BSM; repeat split; lia].
            - eapply stk_transport_disjoint; [exact BUFb| exact MU3| exact WM3| cbn [disjoint_from]; clear - OFFB B0D DCB LOS EFIT EEND EBUF LSR BSM B1H; repeat split; lia]. }
          assert (XB3 : stk bsegs m3 (DCTX + 30372) (DCTX + 95940)).
          { eapply stk_transport_disjoint; [exact XB| exact MU3| exact WM3| cbn [disjoint_from]; clear - OFFD LOS BD B0D DCB EFIT EEND EBUF BSM LSR; repeat split; hlia]. }
          pose proof (dlb_keep2 hufv lev _ m2 m3 _ DLI2 MU3 WM3 MI3 STK3 BUF3 XB3
                        ltac:(apply Forall_cons; [cbn [fst snd]; clear - LOS; lia|]; apply Forall_cons; [cbn [fst snd]; clear - HC LSR BSM EFIT EEND EBUF; lia| apply Forall_nil])) as DLI3.
          assert (H53 : rw_cells bsegs m3 (DCTX + 30096) ltac:(lazymatch type of H5C with rw_cells _ _ _ ?cs => exact cs end)).
          { eapply rw_cells_transport; [exact H5C| exact MU3| exact WM3| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; clear - OFFD LOS BD B0D DCB EFIT EEND EBUF BSM LSR; repeat split; hlia]. }
          assert (HW3 : HUFINVw m3 DCTX hufv lev).
          { unfold fk_held in HW2. eapply hufw_fine; [exact HW2| exact MU3|]. cbn [outside]. intros x Hx. clear - Hx LOS OFFD BD B0D DCB EFIT EEND EBUF BSM LSR; hlia. }
          pose proof DLI3 as I3. unfold AZ_declit_a.DLB in I3. destruct I3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UD3 & _).
          clear H5C XB BUFa BUFb DSTC3 DSTS3 SB3 BUF3 XB3 MU3 WM3 STK3 PTRS EHUF EWK FP H3 SRCB STK FRA AH ARO AZS UD MUs WMs UDm DLI2 HW2 MI.
          assert (UDm : forall mm, munch [(DCTX + 30096, DCTX + 30372)] m3 mm -> unpoisoned mm DCTX (DCTX + 95992)).
          { intros mm MUm. eapply unpoisoned_munch; [exact UD3| exact MUm|]. cbn [disjoint_from]. split; [| exact I]. rewrite !shad_div. unfold ASHOFF. clear - DL ATR; hlia. }
          pose proof (munch_refl [(DCTX + 30096, DCTX + 30372)] m3) as MUs. pose proof (wmono_refl bsegs m3) as WMs.
          fk_hold DLI3. fk_hold HW3.
          dl_chk m3 (DCTX + 30352) UD3 RDS DG.      (* [comment removed for export] *)
          zstep. zstep. zstep. dl_chk m3 (DCTX + 30120) UD3 RDS DG.      (* [comment removed for export] *)
          zstep.                                                 (* [comment removed for export] *)
          zstep.                                                 (* [comment removed for export] *)
          zstep.                                                 (* [comment removed for export] *)
          zstep. zstep. lazymatch type of MUs with munch _ _ ?mm => dl_chk mm (DCTX + 30152) (UDm mm MUs) RDS DG end.
          zstep.                                                 (* [comment removed for export] *)
          zstep. zstep.                                          (* [comment removed for export] *)
          unfold fk_held in DLI3. pose proof DLI3 as I'. unfold AZ_declit_a.DLB in I'. destruct I' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & STK3 & _).
          lazymatch type of H53 with rw_cells _ ?mm _ ?cs => let wl := cells_words cs in
            assert (DLBx : AZ_declit_a.DLB AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe hufv lev wl mm);
            [ eapply (dlb_keep hufv lev _ wl m3 mm _ DLI3 MUs WMs MI3);
              [ eapply stk_transport_disjoint; [exact STK3| exact MUs| exact WMs| cbn [disjoint_from]; clear - OFFD LOS; hlia]
              | split; [exact H53| reflexivity]
              | apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil] ]
            | eapply (dl_ret mm hufv lev wl (lhSize + litSize)); [exact DLBx| clear - LHR LSR SLEN BSM; lia| | ] ] end.
          -- unfold fk_held in KEEP. intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
          -- right. split; [clear - LHR LSR K1; lia|]. split.
             { unfold fk_held in HW3. eapply hufw_fine; [exact HW3| exact MUs|]. cbn [outside]. intros x Hx. clear - Hx; lia. }
             exists (DST + (fh_bsmax h + 32)), litSize, (DST + (fh_bsmax h + 32)), (DST + (fh_bsmax h + 32 + litSize)), 1.
             repeat (split; [first [reflexivity | clear - LSR BSM LHR; lia]|]). right. left. unfold ZSTD_in_dst, WILDCOPY_OVERLENGTH.
             repeat (split; [first [reflexivity | clear - LSR BSM EFIT EEND EBUF B0D DCB; lia]|]). clear - LSR BSM EFIT EEND EBUF B0D DCB; lia.
        * (* [comment removed for export] *)
          subst LBv LEv. cbn [lit_base_addr] in H5C. rewrite ELOC in H5C.
          assert (EBUF : lp_buf p = ews - 32 - litSize + 65536) by (clear - EEND EEWS; lia). rewrite EEND, EBUF in H5C.
          zstep. rewrite (sx32w_small 2) by (clear; lia). zstep. zstep. zstep. zstep. if_false.     (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. zstep.               (* [comment removed for export] *)
          (* [comment removed for export] *)
          assert (NZ : 0 < zlen src) by (clear - K1 LHR LSR; lia).
          assert (HC : 0 < CAP) by (clear - EWC EEWS EEND EBUF LSR BSM BIG; lia).
          unfold fk_held in ADST, US, UB, OFFB, OFFSRC, BSRC, BD, OFFD.
          destruct (ADST ltac:(clear - HC B0D DCB; lia)) as (ARb & AHb & AIb). destruct (ARb ltac:(clear - HC B0D DCB; lia)) as (ABb & _ & RBa & RBb).
          pose proof (fk_ablk_lits _ _ ABb) as BBL.
          set (A1 := DST + (ews - 32 - litSize + 65536)) in *.
          assert (A1R : DST <= A1 /\ A1 + (litSize + -65536) + 32 <= DST + CAP /\ 65536 < litSize) by (subst A1; clear - EWC EEWS EEND EBUF LSR BSM BIG; lia).
          destruct (stk_open bsegs m2 B0 B1 A1 (Z.to_nat (litSize + -65536)) BUF ltac:(clear - B0D A1R; lia) ltac:(rewrite Z2Nat.id by (clear - BIG; lia); clear - A1R DCB; lia)) as (jk & DSTC & BUFa & BUFb).
          rewrite Z2Nat.id in BUFb by (clear - BIG; lia).
          pose proof (dl_bytes_at_slice _ _ _ (Z.to_nat lhSize) (Z.to_nat (litSize + -65536)) SRCB ltac:(rewrite length_map; clear - K1 LHR LSR BIG; lia)) as SL1.
          rewrite Z2Nat.id in SL1 by (clear - LHR; lia).
          assert (SL1L : length (firstn (Z.to_nat (litSize + -65536)) (skipn (Z.to_nat lhSize) (map (Z_to_bv 8) src))) = Z.to_nat (litSize + -65536)).
          { rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn, length_map. clear - K1 LHR LSR BIG; lia. }
          assert (ART2 : art m2) by exact (dl_art_of_aheap AI _ _ _ _ _ AH).
          pose proof (ARS NZ) as (ABS & _ & RSa & RSb). pose proof (fk_ablk_lits _ _ ABS) as SBB.
          fk_hold BUFa. fk_hold BUFb. fk_hold H5C.
          zstep.                                           (* [comment removed for export] *)
          pose proof MEMCPY as MEMCPY1. unfold zd_memcpyZ_stmtA in MEMCPY1.
          eapply evtF_cut.
          { eapply (MEMCPY1 RNG A1 (LSRC + lhSize) (litSize + -65536) (SPV + -96)) with (lo := lo);
              first [ exact SL1 | exact SL1L | exact DSTC | exact STK | exact ART2 | exact MI | reflexivity
                    | lazymatch goal with
                      | |- 0 <= litSize + -65536 <= _ => clear - LSR BSM BIG; lia
                      | |- lo <= SPV + -96 - _ => clear - LOS; lia
                      | |- SPV + -96 < _ => clear - SPH; lia
                      | |- LSRC + lhSize + _ <= A1 \/ _ => clear - BSRC B0D DCB K1 A1R LHR BSM LSR; lia
                      | |- LSRC + lhSize + _ <= SPV + -96 - _ \/ _ => clear - OFFSRC LOS K1 LHR BIG; lia
                      | |- A1 + _ <= lo \/ _ => clear - OFFB B0D DCB A1R LOS BSM LSR; lia
                      | |- app_blk (LSRC + _) _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABS| clear - LHR; lia| clear - K1 BIG; lia]| clear - LSR BIG; lia]
                      | |- app_blk _ _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABb| clear - B0D A1R; lia| clear - DCB A1R; lia]| clear - BIG; lia]
                      | |- aro _ _ (LSRC + _) _ => split; [eapply unpoisoned_sub; [exact (US NZ)| clear - LHR; lia| clear - K1 BIG; lia]| split; [eapply rng_sub'; [exact RSa| clear - LHR K1 BIG; lia]| eapply rng_sub'; [exact RSb| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - LHR K1 LSR BIG; Z.div_mod_to_equations; lia]]]
                      | |- aro _ _ _ _ => split; [eapply unpoisoned_sub; [exact (UB ltac:(clear - HC B0D DCB; lia))| clear - B0D A1R; lia| clear - DCB A1R; lia]| split; [eapply rng_sub'; [exact RBa| clear - B0D DCB A1R; lia]| eapply rng_sub'; [exact RBb| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - B0D DCB A1R; Z.div_mod_to_equations; lia]]]
                      | |- ahull _ _ (LSRC + _) _ => eapply dl_ahull_sub; [eapply dl_ahull_wmono; [exact (AHS NZ)| exact WM]| clear - LHR; lia| clear - K1 BIG; lia]
                      | |- ahull _ _ _ _ => eapply dl_ahull_sub; [eapply dl_ahull_wmono; [exact AHb| exact WM]| clear - B0D A1R; lia| clear - DCB A1R; lia]
                      | |- astk _ _ _ => split; [unfold KHIGH; clear - KHI; lia| split; [eapply rng_sub'; [exact RSTK| clear - LOS; lia]| exact RI]]
                      end
                    | lazymatch goal with |- ?Gg => idtac "MEMCPY-LEFT:" Gg end ]. }
          cbv beta. intros ms' (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & -> & MU3 & WM3 & MI3 & STK3 & DSTC3 & SB3).
          replace (ret_pc (Z_to_bv 64 0x87950)) with (Z_to_bv 64 0x87950) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
          clear MEMCPY1 SL1 SL1L ART2.
          unfold fk_held in BUFa, BUFb, DLI2, H5C.
          pose proof (stk_of_rw_cells bsegs _ _ _ DSTC3) as DSTS3. cbn [cells_size csize length] in DSTS3. rewrite Nat.add_0_r, Z2Nat.id in DSTS3 by (clear - BIG; lia).
          assert (BUF3 : stk bsegs m3 B0 B1).
          { eapply stk_merge; [eapply stk_merge; [| exact DSTS3| clear - B0D A1R; lia]| | clear - B0D A1R DCB; lia].
            - eapply stk_transport_disjoint; [exact BUFa| exact MU3| exact WM3| cbn [disjoint_from]; clear - OFFB B0D DCB LOS A1R; repeat split; lia].
            - eapply stk_transport_disjoint; [exact BUFb| exact MU3| exact WM3| cbn [disjoint_from]; clear - OFFB B0D DCB LOS A1R B1H; repeat split; lia]. }
          assert (XB3 : stk bsegs m3 (DCTX + 30372) (DCTX + 95940)).
          { eapply stk_transport_disjoint; [exact XB| exact MU3| exact WM3| cbn [disjoint_from]; clear - OFFD LOS BD B0D DCB A1R; repeat split; lia]. }
          pose proof (dlb_keep2 hufv lev _ m2 m3 _ DLI2 MU3 WM3 MI3 STK3 BUF3 XB3
                        ltac:(apply Forall_cons; [cbn [fst snd]; clear - LOS; lia|]; apply Forall_cons; [cbn [fst snd]; clear - HC A1R; lia| apply Forall_nil])) as DLI3.
          assert (H53 : rw_cells bsegs m3 (DCTX + 30096) ltac:(lazymatch type of H5C with rw_cells _ _ _ ?cs => exact cs end)).
          { eapply rw_cells_transport; [exact H5C| exact MU3| exact WM3| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; clear - OFFD LOS BD B0D DCB A1R; repeat split; lia]. }
          assert (HW3 : HUFINVw m3 DCTX hufv lev).
          { unfold fk_held in HW2. eapply hufw_fine; [exact HW2| exact MU3|]. cbn [outside]. intros x Hx. clear - Hx LOS OFFD BD B0D DCB A1R; lia. }
          pose proof DLI3 as I3. unfold AZ_declit_a.DLB in I3.
          destruct I3 as (_ & _ & _ & _ & _ & _ & _ & SRCB3 & _ & _ & _ & _ & _ & WM03 & AH3 & _ & UD3 & US3 & _).
          clear H5C XB BUFa BUFb DSTC3 DSTS3 SB3 BUF3 MU3 WM3 PTRS EHUF EWK FP H3 SRCB STK FRA AH ARO AZS UD MUs WMs UDm DLI2 HW2 MI.
          (* [comment removed for export] *)
          zstep. zstep. zstep.                             (* [comment removed for export] *)
          zstep. zstep.                                    (* [comment removed for export] *)
          zstep.                                           (* [comment removed for export] *)
          (* [comment removed for export] *)
          destruct (stk_open bsegs m3 (DCTX + 30372) (DCTX + 95940) (DCTX + 30372) (Z.to_nat 65536) XB3 ltac:(clear; lia) ltac:(clear; lia)) as (jx & XBC & _ & XBb).
          change (Z.of_nat (Z.to_nat 65536)) with 65536 in XBb.
          pose proof (dl_bytes_at_slice _ _ _ (Z.to_nat (lhSize + (litSize + -65536))) (Z.to_nat 65536) SRCB3 ltac:(rewrite length_map; clear - K1 LHR LSR BIG; lia)) as SL2.
          rewrite Z2Nat.id in SL2 by (clear - LHR BIG; lia).
          assert (SL2L : length (firstn (Z.to_nat 65536) (skipn (Z.to_nat (lhSize + (litSize + -65536))) (map (Z_to_bv 8) src))) = Z.to_nat 65536).
          { rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn, length_map. clear - K1 LHR LSR BIG; lia. }
          assert (ART3 : art m3) by exact (dl_art_of_aheap AI _ _ _ _ _ AH3).
          fk_hold XBb. fk_hold H53.
          zstep.                                           (* [comment removed for export] *)
          pose proof MEMCPY as MEMCPY2. unfold zd_memcpyZ_stmtA in MEMCPY2.
          eapply evtF_cut.
          { eapply (MEMCPY2 RNG (DCTX + 30372) (LSRC + lhSize + (litSize + -65536)) 65536 (SPV + -96)) with (lo := lo);
              first [ exact SL2L | exact XBC | exact STK3 | exact ART3 | exact MI3 | reflexivity
                    | lazymatch goal with
                      | |- bytes_at _ _ _ _ => replace (LSRC + lhSize + (litSize + -65536)) with (LSRC + (lhSize + (litSize + -65536))) by (clear; lia); exact SL2
                      | |- 0 <= 65536 <= _ => clear; lia
                      | |- lo <= SPV + -96 - _ => clear - LOS; lia
                      | |- SPV + -96 < _ => clear - SPH; lia
                      | |- LSRC + _ + _ + _ <= DCTX + _ \/ _ => clear - SRCD K1 LHR BIG LSR; hlia
                      | |- LSRC + _ + _ + _ <= SPV + -96 - _ \/ _ => clear - OFFSRC LOS K1 LHR BIG; hlia
                      | |- DCTX + _ + _ <= lo \/ _ => clear - OFFD LOS; hlia
                      | |- app_blk (DCTX + _) _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABD| clear; lia| clear; lia]| clear; lia]
                      | |- app_blk _ _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABS| clear - LHR BIG; lia| clear - K1; lia]| clear; lia]
                      | |- aro _ _ (DCTX + _) _ => split; [eapply unpoisoned_sub; [exact UD3| clear; lia| clear; lia]| split; [eapply rng_sub'; [exact RDc| clear; lia]| eapply rng_sub'; [exact RDS| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - DCA; Z.div_mod_to_equations; lia]]]
                      | |- aro _ _ _ _ => split; [eapply unpoisoned_sub; [exact (US3 NZ)| clear - LHR BIG; lia| clear - K1; lia]| split; [eapply rng_sub'; [exact RSa| clear - LHR K1 BIG; lia]| eapply rng_sub'; [exact RSb| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - LHR K1 LSR BIG; Z.div_mod_to_equations; lia]]]
                      | |- ahull _ _ (DCTX + _) _ => eapply dl_ahull_sub; [eapply dl_ahull_wmono; [exact AHD| exact WM03]| clear; lia| clear; lia]
                      | |- ahull _ _ _ _ => eapply dl_ahull_sub; [eapply dl_ahull_wmono; [exact (AHS NZ)| exact WM03]| clear - LHR BIG; lia| clear - K1; lia]
                      | |- astk _ _ _ => split; [unfold KHIGH; clear - KHI; lia| split; [eapply rng_sub'; [exact RSTK| clear - LOS; lia]| exact RI]]
                      | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; clear; lia
                      end
                    | lazymatch goal with |- ?Gg => idtac "MEMCPY-LEFT:" Gg end ]. }
          cbv beta. intros ms' (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4 & -> & MU4 & WM4 & MI4 & STK4 & XBC4 & SB4).
          replace (ret_pc (Z_to_bv 64 0x87c30)) with (Z_to_bv 64 0x87c30) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
          clear MEMCPY2 SL2 SL2L ART3.
          unfold fk_held in XBb, DLI3, H53.
          pose proof (stk_of_rw_cells bsegs _ _ _ XBC4) as XBS4. cbn [cells_size csize length] in XBS4. rewrite Nat.add_0_r in XBS4. change (Z.of_nat (Z.to_nat 65536)) with 65536 in XBS4.
          assert (XB4 : stk bsegs m4 (DCTX + 30372) (DCTX + 95940)).
          { eapply stk_merge; [exact XBS4| | clear; lia]. eapply stk_transport_disjoint; [exact XBb| exact MU4| exact WM4| cbn [disjoint_from]; clear - OFFD LOS; repeat split; hlia]. }
          pose proof DLI3 as I3. unfold AZ_declit_a.DLB in I3. destruct I3 as (_ & _ & _ & _ & _ & _ & _ & _ & BUF3 & _).
          assert (BUF4 : stk bsegs m4 B0 B1).
          { eapply stk_transport_disjoint; [exact BUF3| exact MU4| exact WM4| cbn [disjoint_from]; clear - OFFB LOS BD B0D DCB B1H; repeat split; hlia]. }
          pose proof (dlb_keep2 hufv lev _ m3 m4 _ DLI3 MU4 WM4 MI4 STK4 BUF4 XB4
                        ltac:(apply Forall_cons; [cbn [fst snd]; clear - LOS; lia|]; apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil])) as DLI4.
          assert (H54 : rw_cells bsegs m4 (DCTX + 30096) ltac:(lazymatch type of H53 with rw_cells _ _ _ ?cs => exact cs end)).
          { eapply rw_cells_transport; [exact H53| exact MU4| exact WM4| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; clear - OFFD LOS; repeat split; hlia]. }
          assert (HW4 : HUFINVw m4 DCTX hufv lev).
          { eapply hufw_fine; [exact HW3| exact MU4|]. cbn [outside]. intros x Hx. clear - Hx LOS OFFD; hlia. }
          pose proof DLI4 as I4. unfold AZ_declit_a.DLB in I4. destruct I4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UD4 & _).
          clear H53 XBb XBC4 XBS4 SB4 XB4 BUF3 BUF4 MU4 WM4 XB3 SRCB3 WM03 AH3 UD3 DLI3 HW3 MI3 STK3. try clear US3.
          assert (UDm : forall mm, munch [(DCTX + 30096, DCTX + 30372)] m4 mm -> unpoisoned mm DCTX (DCTX + 95992)).
          { intros mm MUm. eapply unpoisoned_munch; [exact UD4| exact MUm|]. cbn [disjoint_from]. split; [| exact I]. rewrite !shad_div. unfold ASHOFF. clear - DL ATR; hlia. }
          pose proof (munch_refl [(DCTX + 30096, DCTX + 30372)] m4) as MUs. pose proof (wmono_refl bsegs m4) as WMs.
          fk_hold DLI4. fk_hold HW4.
          dl_chk m4 (DCTX + 30352) UD4 RDS DG.      (* [comment removed for export] *)
          zstep. zstep. zstep. dl_chk m4 (DCTX + 30120) UD4 RDS DG.      (* [comment removed for export] *)
          zstep.                                                 (* [comment removed for export] *)
          zstep.                                                 (* [comment removed for export] *)
          zstep.                                                 (* [comment removed for export] *)
          zstep. zstep. lazymatch type of MUs with munch _ _ ?mm => dl_chk mm (DCTX + 30152) (UDm mm MUs) RDS DG end.
          zstep.                                                 (* [comment removed for export] *)
          zstep. zstep.                                          (* [comment removed for export] *)
          unfold fk_held in DLI4. pose proof DLI4 as I'. unfold AZ_declit_a.DLB in I'. destruct I' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & STK4' & _).
          lazymatch type of H54 with rw_cells _ ?mm _ ?cs => let wl := cells_words cs in
            assert (DLBx : AZ_declit_a.DLB AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe hufv lev wl mm);
            [ eapply (dlb_keep hufv lev _ wl m4 mm _ DLI4 MUs WMs MI4);
              [ eapply stk_transport_disjoint; [exact STK4'| exact MUs| exact WMs| cbn [disjoint_from]; clear - OFFD LOS; hlia]
              | split; [exact H54| reflexivity]
              | apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil] ]
            | eapply (dl_ret mm hufv lev wl (lhSize + litSize)); [exact DLBx| clear - LHR LSR SLEN BSM; lia| | ] ] end.
          -- unfold fk_held in KEEP. intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
          -- right. split; [clear - LHR LSR K1; lia|]. split.
             { unfold fk_held in HW4. eapply hufw_fine; [exact HW4| exact MUs|]. cbn [outside]. intros x Hx. clear - Hx; lia. }
             exists (DST + (ews - 32 - litSize + 65536)), litSize, (DST + (ews - 32 - litSize + 65536)), (DST + (ews - 32 - litSize + 65536 + litSize - 65536)), 2.
             repeat (split; [first [reflexivity | clear - LSR BSM LHR BIG; lia]|]). right. right. unfold ZSTD_split, ZSTD_LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH.
             repeat (split; [first [reflexivity | clear - LSR BSM BIG A1R; lia]|]). clear - LSR BSM BIG A1R; lia.
      + (* [comment removed for export] *)
        destruct REG as (ELOC & EBUF & EEND & SMALL).
        subst LBv LEv. cbn [lit_base_addr] in H5C. unfold DCTX_litExtraBuffer in H5C. rewrite ELOC, EEND, EBUF in H5C.
        replace (DCTX + 30372 + 0) with (DCTX + 30372) in H5C by (clear; lia).
        zstep. rewrite (sx32w_small 0) by (clear; lia). zstep. zstep. zstep. zstep. if_true.        (* [comment removed for export] *)
        zstep. zstep.                                      (* [comment removed for export] *)
        (* [comment removed for export] *)
        assert (NZ : 0 < zlen src) by (clear - K1 LHR LSR; lia).
        unfold fk_held in US, OFFSRC, SRCD, OFFD.
        destruct (stk_open bsegs m2 (DCTX + 30372) (DCTX + 95940) (DCTX + 30372) (Z.to_nat litSize) XB ltac:(clear; lia) ltac:(rewrite Z2Nat.id by (clear - LSR; lia); clear - SMALL LSR; lia)) as (jx & XBC & _ & XBb).
        rewrite Z2Nat.id in XBb by (clear - LSR; lia).
        pose proof (dl_bytes_at_slice _ _ _ (Z.to_nat lhSize) (Z.to_nat litSize) SRCB ltac:(rewrite length_map; clear - K1 LHR LSR; lia)) as SL1.
        rewrite Z2Nat.id in SL1 by (clear - LHR; lia).
        assert (SL1L : length (firstn (Z.to_nat litSize) (skipn (Z.to_nat lhSize) (map (Z_to_bv 8) src))) = Z.to_nat litSize).
        { rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn, length_map. clear - K1 LHR LSR; lia. }
        assert (ART2 : art m2) by exact (dl_art_of_aheap AI _ _ _ _ _ AH).
        pose proof (ARS NZ) as (ABS & _ & RSa & RSb).
        fk_hold XBb. fk_hold H5C.
        zstep.                                             (* [comment removed for export] *)
        pose proof MEMCPY as MEMCPY1. unfold zd_memcpyZ_stmtA in MEMCPY1.
        eapply evtF_cut.
        { eapply (MEMCPY1 RNG (DCTX + 30372) (LSRC + lhSize) litSize (SPV + -96)) with (lo := lo);
            first [ exact SL1 | exact SL1L | exact XBC | exact STK | exact ART2 | exact MI | reflexivity
                  | lazymatch goal with
                    | |- 0 <= litSize <= _ => clear - LSR BSM; lia
                    | |- lo <= SPV + -96 - _ => clear - LOS; lia
                    | |- SPV + -96 < _ => clear - SPH; lia
                    | |- LSRC + _ + _ <= DCTX + _ \/ _ => clear - SRCD K1 LHR LSR SMALL; lia
                    | |- LSRC + _ + _ <= SPV + -96 - _ \/ _ => clear - OFFSRC LOS K1 LHR; lia
                    | |- DCTX + _ + _ <= lo \/ _ => clear - OFFD LOS SMALL LSR; lia
                    | |- app_blk (DCTX + _) _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABD| clear; lia| clear - SMALL; lia]| clear - LSR; lia]
                    | |- app_blk _ _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABS| clear - LHR; lia| clear - K1; lia]| clear - LSR; lia]
                    | |- aro _ _ (DCTX + _) _ => split; [eapply unpoisoned_sub; [exact UD| clear; lia| clear - SMALL; lia]| split; [eapply rng_sub'; [exact RDc| clear - SMALL LSR; lia]| eapply rng_sub'; [exact RDS| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - DCA SMALL LSR; Z.div_mod_to_equations; lia]]]
                    | |- aro _ _ _ _ => split; [eapply unpoisoned_sub; [exact (US NZ)| clear - LHR; lia| clear - K1; lia]| split; [eapply rng_sub'; [exact RSa| clear - LHR K1; lia]| eapply rng_sub'; [exact RSb| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - LHR K1 LSR; Z.div_mod_to_equations; lia]]]
                    | |- ahull _ _ (DCTX + _) _ => eapply dl_ahull_sub; [eapply dl_ahull_wmono; [exact AHD| exact WM]| clear; lia| clear - SMALL; lia]
                    | |- ahull _ _ _ _ => eapply dl_ahull_sub; [eapply dl_ahull_wmono; [exact (AHS NZ)| exact WM]| clear - LHR; lia| clear - K1; lia]
                    | |- astk _ _ _ => split; [unfold KHIGH; clear - KHI; lia| split; [eapply rng_sub'; [exact RSTK| clear - LOS; lia]| exact RI]]
                    end
                  | lazymatch goal with |- ?Gg => idtac "MEMCPY-LEFT:" Gg end ]. }
        cbv beta. intros ms' (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & -> & MU3 & WM3 & MI3 & STK3 & XBC3 & SB3).
        replace (ret_pc (Z_to_bv 64 0x87c30)) with (Z_to_bv 64 0x87c30) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
        clear MEMCPY1 SL1 SL1L ART2.
        unfold fk_held in XBb, DLI2, H5C, OFFB, BD.
        pose proof (stk_of_rw_cells bsegs _ _ _ XBC3) as XBS3. cbn [cells_size csize length] in XBS3. rewrite Nat.add_0_r, Z2Nat.id in XBS3 by (clear - LSR; lia).
        assert (XB3 : stk bsegs m3 (DCTX + 30372) (DCTX + 95940)).
        { eapply stk_merge; [exact XBS3| | clear - LSR SMALL; lia]. eapply stk_transport_disjoint; [exact XBb| exact MU3| exact WM3| cbn [disjoint_from]; clear - OFFD LOS LSR SMALL; repeat split; lia]. }
        assert (BUF3 : stk bsegs m3 B0 B1).
        { eapply stk_transport_disjoint; [exact BUF| exact MU3| exact WM3| cbn [disjoint_from]; clear - OFFB LOS BD B0D DCB B1H LSR SMALL; repeat split; lia]. }
        pose proof (dlb_keep2 hufv lev _ m2 m3 _ DLI2 MU3 WM3 MI3 STK3 BUF3 XB3
                      ltac:(apply Forall_cons; [cbn [fst snd]; clear - LOS; lia|]; apply Forall_cons; [cbn [fst snd]; clear - LSR SMALL; lia| apply Forall_nil])) as DLI3.
        assert (H53 : rw_cells bsegs m3 (DCTX + 30096) ltac:(lazymatch type of H5C with rw_cells _ _ _ ?cs => exact cs end)).
        { eapply rw_cells_transport; [exact H5C| exact MU3| exact WM3| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; clear - OFFD LOS LSR; repeat split; lia]. }
        assert (HW3 : HUFINVw m3 DCTX hufv lev).
        { unfold fk_held in HW2. eapply hufw_fine; [exact HW2| exact MU3|]. cbn [outside]. intros x Hx. clear - Hx LOS OFFD LSR; lia. }
        pose proof DLI3 as I3. unfold AZ_declit_a.DLB in I3. destruct I3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UD3 & _).
        clear H5C XB XBb XBC3 XBS3 SB3 BUF3 XB3 MU3 WM3 STK3 PTRS EHUF EWK FP H3 SRCB BUF STK FRA AH ARO AZS UD MUs WMs UDm DLI2 HW2 MI.
        assert (UDm : forall mm, munch [(DCTX + 30096, DCTX + 30372)] m3 mm -> unpoisoned mm DCTX (DCTX + 95992)).
        { intros mm MUm. eapply unpoisoned_munch; [exact UD3| exact MUm|]. cbn [disjoint_from]. split; [| exact I]. rewrite !shad_div. unfold ASHOFF. clear - DL ATR; hlia. }
        pose proof (munch_refl [(DCTX + 30096, DCTX + 30372)] m3) as MUs. pose proof (wmono_refl bsegs m3) as WMs.
        fk_hold DLI3. fk_hold HW3.
        dl_chk m3 (DCTX + 30352) UD3 RDS DG.        (* [comment removed for export] *)
        zstep. zstep. zstep. dl_chk m3 (DCTX + 30120) UD3 RDS DG.        (* [comment removed for export] *)
        zstep.                                                   (* [comment removed for export] *)
        zstep.                                                   (* [comment removed for export] *)
        zstep.                                                   (* [comment removed for export] *)
        zstep. zstep. lazymatch type of MUs with munch _ _ ?mm => dl_chk mm (DCTX + 30152) (UDm mm MUs) RDS DG end.
        zstep.                                                   (* [comment removed for export] *)
        zstep. zstep.                                            (* [comment removed for export] *)
        unfold fk_held in DLI3. pose proof DLI3 as I'. unfold AZ_declit_a.DLB in I'. destruct I' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & STK3 & _).
        lazymatch type of H53 with rw_cells _ ?mm _ ?cs => let wl := cells_words cs in
          assert (DLBx : AZ_declit_a.DLB AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe hufv lev wl mm);
          [ eapply (dlb_keep hufv lev _ wl m3 mm _ DLI3 MUs WMs MI3);
            [ eapply stk_transport_disjoint; [exact STK3| exact MUs| exact WMs| cbn [disjoint_from]; clear - OFFD LOS; hlia]
            | split; [exact H53| reflexivity]
            | apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil] ]
          | eapply (dl_ret mm hufv lev wl (lhSize + litSize)); [exact DLBx| clear - LHR LSR SLEN BSM; lia| | ] ] end.
        * unfold fk_held in KEEP. intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
        * right. split; [clear - LHR LSR K1; lia|]. split.
          { unfold fk_held in HW3. eapply hufw_fine; [exact HW3| exact MUs|]. cbn [outside]. intros x Hx. clear - Hx; lia. }
          exists (DCTX + 30372), litSize, (DCTX + 30372), (DCTX + 30372 + litSize), 0.
          repeat (split; [first [reflexivity | clear - LSR BSM LHR; lia]|]). left. unfold ZSTD_not_in_dst, ZSTD_LITBUFFEREXTRASIZE, DCTX_litExtraBuffer.
          repeat (split; [first [reflexivity | clear - LSR SMALL; lia]|]). left. split; [reflexivity| clear - SMALL; lia].
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
