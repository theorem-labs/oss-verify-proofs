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
     AZ_globals AZ_globalsR AZ_frame_iface AZ_huf_iface AZ_block_iface AZ_blk_iface4 AZ_blk_iface5 AZ_libc_iface AZ_hufinv AZ_kx AZ_declit_a AZ_declit_b AZ_declit_c.
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
  Hypothesis MEMMOVE : zd_memmoveZ_stmtA.
  Hypothesis H1X : huf_1x_stmtA.
  Hypothesis H4X : huf_4x_stmtA.
  Hypothesis H1W : huf_1x1_wksp_stmtA AI rng_fs.
  Hypothesis H4W : huf_4x_wksp_stmtA AI rng_fs.
  Notation dlbK := (AZ_declit_b.dlb_keep AI rng_fs L RNG st LB ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe ws CTX).
  Notation dlbK2 := (AZ_declit_b.dlb_keep2 AI rng_fs L RNG st LB ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe ws CTX).
  Ltac hlia := unfold fk_held in *; lia.
  (* [comment removed for export] *)
  Ltac b2z_norm G :=
    repeat match type of G with
           | context [Z.ltb ?a ?b] =>
               first [ replace (Z.ltb a b) with true in G by (symmetry; apply Z.ltb_lt; lia)
                     | replace (Z.ltb a b) with false in G by (symmetry; apply Z.ltb_ge; lia) ]
           | context [Z.eqb ?a ?b] =>
               first [ replace (Z.eqb a b) with true in G by (symmetry; apply Z.eqb_eq; lia)
                     | replace (Z.eqb a b) with false in G by (symmetry; apply Z.eqb_neq; lia) ]
           end; cbn [Z.b2z] in G.
  Ltac grdb := let G := fresh "G" in if_cases G; zify_cond G; [ exfalso; b2z_norm G; first [ congruence | lia | vm_compute in G; first [ congruence | lia | apply G; reflexivity ] ] | clear G ].

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
  Lemma dl_pf : forall (n : nat) k m1 xra x5 x6 x7 xs0 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31,
    Z.of_nat n = 256 - k -> 0 <= k ->
    (forall xa0' xa3', evtF bsegs RNG POST (ST 0x87b0c m1 xra x5 x6 x7 xs0 xs1 xa0' (Z_to_bv 64 16324) xa2 xa3' xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31)) ->
    evtF bsegs RNG POST (ST 0x87b00 m1 xra x5 x6 x7 xs0 xs1 (Z_to_bv 64 (64 * k)) (Z_to_bv 64 16324) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31).
  Proof.
    induction n as [|n IH]; intros until x31; intros EN K0 KONT.
    - assert (k = 256) by (clear - EN; lia). subst k.
      zstep. zstep. zstep. if_false. apply KONT.
    - zstep. zstep. zstep. if_cases KL; zify_cond KL; [| exfalso; clear - KL EN K0; lia].
      replace (64 * k + 64) with (64 * (k + 1)) by (clear; lia).
      eapply IH; [clear - EN; lia | clear - K0; lia | exact KONT].
  Qed.

  (* [comment removed for export] *)
  Hypothesis PHUF : forall m2 hufv lev wsv litSize litCSize lhSize four ty dha (xra x5 x6 x7 xa0 xa1 xa3 xa4 xa6 xa7 x28 x29 x30 x31 : word),
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

  (* [comment removed for export] *)
  Lemma dl_cmp : forall m1 hufv lev wsv litSize litCSize lhSize four ty dha xra x5 x7 x17 xs8 xs10 x28 x29 x30 x31,
    DLB hufv lev wsv m1 -> wnth wsv H5_isFrameDecompression = Z_to_bv 64 1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m1 DCTX hufv lev ->
    3 <= lhSize <= 5 -> 0 <= litCSize -> lhSize + litCSize <= zlen src -> 0 <= litSize <= Z.min (fh_bsmax h) CAP -> (DST = 0 -> litSize = 0) ->
    (four = 0 \/ (four = 1 /\ 6 <= litSize)) -> (ty = 2 \/ (ty = 3 /\ bv_unsigned lev mod 2^32 <> 0)) ->
    evtF bsegs RNG POST (ST 0x87a90 m1 xra x5 (Z_to_bv 64 (fh_bsmax h)) x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize)
                           (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 0)
                           (Z_to_bv 64 (Z.min (fh_bsmax h) CAP)) x17 (Z_to_bv 64 litCSize) (Z_to_bv 64 lhSize) (Z_to_bv 64 four) (Z_to_bv 64 ty)
                           (Z_to_bv 64 (lhSize + litCSize)) xs8 dha xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I ISFv KEEP HW LHR LCS LHS LSR DNL FOUR TY. pose proof I as DLI. open_dlb I. dl_open CTX.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold KHIGH in KHI.
    pose proof (ARD ltac:(clear; lia)) as (ABD & _ & RDc & RDS). pose proof (fk_ablk_lits _ _ ABD) as DL.
    pose proof (bytes_at_bound _ _ _ _ SRCB) as SBL. rewrite length_map in SBL.
    assert (DG : DCTX mod 8 = 0 /\ 0 <= DCTX /\ DCTX + 95992 <= 2^47) by (clear - DCA DCL DCH; lia).
    pose proof (proj2 H5) as L5.
    fk_hold OFFD. fk_hold OFFB. fk_hold OFFSRC. fk_hold BD. fk_hold BSRC. fk_hold SRCD. fk_hold DNULL. fk_hold DNN. fk_hold ADST. fk_hold AIS. fk_hold US. fk_hold UB.
    fk_hold KEEP. fk_hold MU. fk_hold FFR. fk_hold DLI. fk_hold HW. fk_hold DNL. fk_hold DL. fk_hold FOUR. fk_hold TY.
    fk_hold MEMCPY. fk_hold MEMMOVE. fk_hold H1X. fk_hold H4X. fk_hold H1W. fk_hold H4W.
    do 8 zstep.                                            (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    assert (ART1 : art m1) by exact (dl_art_of_aheap AI _ _ _ _ _ AH).
    unfold zd_alloclit_stmtA, APZD_ALLOCLIT in ALLOCLIT.
    eapply evtF_cut.
    { eapply (ALLOCLIT RNG) with (SPV := SPV + -96) (lo := lo) (DCTX := DCTX) (DST := DST) (CAP := CAP) (litSize := litSize) (ews := Z.min (fh_bsmax h) CAP) (imm := false) (h := h) (ws := wsv);
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
    pose proof (dlbK hufv lev wsv _ m1 m2 _ DLI MUc WMc MI2 STK2 H52
                  ltac:(unfold DCTX_litBuffer; apply Forall_cons; [cbn [fst snd]; clear; lia|]; apply Forall_cons; [cbn [fst snd]; clear - LOS; hlia| apply Forall_nil])) as DLI2.
    assert (HW2 : HUFINVw m2 DCTX hufv lev).
    { unfold fk_held in HW. eapply hufw_fine; [exact HW| exact MUc|]. unfold DCTX_litBuffer. cbn [outside]. intros x Hx. clear - Hx LOS OFFD; hlia. }
    clear PTRS EHUF EWK FP H3 H5 XB SRCB BUF STK FRA MI MU WM AH FFR UD ARO AZS ART1 MUc WMc STK2 H52 DLI HW US UB.
    pose proof DLI2 as I. open_dlb I. fk_hold DLI2. fk_hold MU. fk_hold FFR. fk_hold UB.
    h5_open wsv L5. lazymatch type of ISFv with ?x = _ => subst x end.
    set (ews := Z.min (fh_bsmax h) CAP) in *.
    pose proof (alloc_lit_buffer_regions (fh_bsmax h) CAP litSize ews false LSR eq_refl ltac:(unfold ZSTD_BLOCKSIZE_MAX; clear - BSM; lia)) as REG.
    set (p := alloc_lit_buffer (fh_bsmax h) CAP litSize ews false) in *.
    destruct H5 as [H5C _].
    cbv [h5_placed h5_cells mk_wcells h5_sizes wupd H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in H5C.
    set (LBv := lit_base_addr DCTX DST (lp_base p) + lp_buf p) in *. set (LEv := lit_base_addr DCTX DST (lp_base p) + lp_end p) in *.
    assert (UDm : forall mm, munch [(DCTX + 30096, DCTX + 30372)] m2 mm -> unpoisoned mm DCTX (DCTX + 95992)).
    { intros mm MUm. eapply unpoisoned_munch; [exact UD| exact MUm|]. cbn [disjoint_from]. split; [| exact I]. rewrite !shad_div. unfold ASHOFF. clear - DL ATR; hlia. }
    replace (ret_pc (Z_to_bv 64 0x87ab4)) with (Z_to_bv 64 0x87ab4) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    zstep. zstep. zstep. dl_chk m2 (DCTX + 30204) UD RDS DG.      (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    zstep. zstep.                                              (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (GO : forall xa0 xa1 xa3 xa4 xa6, evtF bsegs RNG POST (ST 0x87b0c m2 (Z_to_bv 64 0x87ab4) c0 c1 c2 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize)
                           xa0 xa1 (Z_to_bv 64 LSRC) xa3 xa4 (Z_to_bv 64 DCTX) xa6 d7
                           (Z_to_bv 64 litCSize) (Z_to_bv 64 lhSize) (Z_to_bv 64 four) (Z_to_bv 64 ty) (Z_to_bv 64 (lhSize + litCSize))
                           (Z_to_bv 64 DCTX) dha (Z_to_bv 64 LSRC) c3 c4 c5 c6)).
    { intros xa0 xa1 xa3 xa4 xa6. unfold fk_held in DLI2, HW2, KEEP, DNL, FOUR, TY.
      eapply (PHUF m2 hufv lev _ litSize litCSize lhSize four ty dha); [exact DLI2| reflexivity| exact KEEP| exact HW2| exact LHR| exact LCS| exact LHS| exact LSR| exact DNL| exact FOUR| exact TY]. }
    zstep. if_cases KC.
    { (* [comment removed for export] *) apply GO. }
    zstep. zstep. if_cases K7; zify_cond K7.
    { (* [comment removed for export] *) apply GO. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. dl_chk m2 (DCTX + 24) UD RDS DG.
    zstep.                                                 (* [comment removed for export] *)
    zstep. zstep.                                          (* [comment removed for export] *)
    eapply (dl_pf 256 0); [reflexivity| clear; lia|]. intros xa0' xa3'. apply GO.
  Qed.
End DL.
End CANSEC1.
(* [comment removed for export] *)
