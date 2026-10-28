(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdLit.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit ZdFrameW ZdWalkKit ZdCellKit MemRange ZdDctxRep.
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
  Hypothesis MEMCPY : zd_memcpyZ_stmtA.
  Hypothesis MEMMOVE : zd_memmoveZ_stmtA.
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
  Lemma dlb_keep3 : forall hufv lev hufv' lev' ws1 ws2 (ma mb : amem) W,
    DLB hufv lev ws1 ma ->
    munch W ma mb -> wmono bsegs ma mb -> mem_inv bsegs mb -> stk bsegs mb lo (SPV + -96) ->
    dctx_ptrs bsegs mb DCTX llt mlt oft hufv' -> dctx_h3 bsegs mb DCTX pcs dsz bt stg lev' fe -> dctx_h5 bsegs mb DCTX ws2 ->
    Forall (fun iv => fst iv <= snd iv /\ ((DCTX + 24 <= fst iv /\ snd iv <= DCTX + 32) \/ (DCTX + 30000 <= fst iv /\ snd iv <= DCTX + 30004)
                                           \/ (DCTX + 30096 <= fst iv /\ snd iv <= DCTX + 30372) \/ (SPV - 6096 <= fst iv /\ snd iv <= SPV + -96))) W ->
    DLB hufv' lev' ws2 mb.
  Proof.
    intros hufv lev hufv' lev' ws1 ws2 ma mb W I MUx WMx MIx STKx PTx H3x H5x HW. dl_open CTX.
      pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold KHIGH in KHI.
      pose proof (ARD ltac:(clear; lia)) as (ABD & _). pose proof (fk_ablk_lits _ _ ABD) as DL.
      unfold AZ_declit_a.DLB in I. destruct I as (PTRS & EHUF & EWK & FP & H3 & H5 & XB & SRCB & BUF & STK & FRA & MI & MU & WM & AH & FFR & UD & US & UB & ARO & AZS).
      pose proof (bytes_at_bound _ _ _ _ SRCB) as SBL. rewrite length_map in SBL.
      assert (DJ : forall X n, 0 <= n -> (X + n <= DCTX + 24 \/ DCTX + 32 <= X) -> (X + n <= DCTX + 30000 \/ DCTX + 30004 <= X) ->
                   (X + n <= DCTX + 30096 \/ DCTX + 30372 <= X) -> (X + n <= SPV - 6096 \/ SPV + -96 <= X) -> disjoint_from W X n).
      { intros X n Hn A A' B C. clear - HW Hn A A' B C. induction HW as [|[x y] W [Hle Hc] HW IH]; cbn; [exact I|]. cbn in Hle, Hc. split; [lia| exact IH]. }
      assert (DJS : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from W (shad X) (shad (X + n - 1) + 1 - shad X)).
      { intros X n A B C. rewrite !shad_div. unfold ASHOFF. apply DJ; clear - A B C DL KHI LOS ATR; Z.div_mod_to_equations; lia. }
      assert (AW : aappW W).
      { unfold aappW. clear - HW DL KHI LOS SPH ATR. induction HW as [|[x y] W [Hle Hc] HW IH]; [apply Forall_nil|]. apply Forall_cons; [| exact IH].
        cbn [fst snd] in *. unfold KLOW, KHIGH. lia. }
      unfold dctx_ptrs, dctx_h3, zfh_cells in *.
      split; [exact PTx|].
      split; [eapply stk_transport_disjoint; [exact EHUF| exact MUx| exact WMx| apply DJ; clear - DL LOS OFFD; lia]|].
      split; [eapply stk_transport_disjoint; [exact EWK| exact MUx| exact WMx| apply DJ; clear - DL LOS OFFD; lia]|].
      split; [eapply rw_cells_transport; [exact FP| exact MUx| exact WMx| apply DJ; cbn; clear - DL LOS OFFD; lia]|].
      split; [exact H3x|].
      split; [exact H5x|].
      split; [eapply stk_transport_disjoint; [exact XB| exact MUx| exact WMx| apply DJ; clear - DL LOS OFFD; lia]|].
      split; [eapply bytes_at_transport; [exact SRCB| exact MUx| rewrite length_map; apply DJ; [clear - SBL| clear - SRCD| clear - SRCD| clear - SRCD| clear - OFFSRC LOS]; lia]|].
      split; [eapply stk_transport_disjoint; [exact BUF| exact MUx| exact WMx| apply DJ; [clear - B0D DCB CAP0| clear - BD| clear - BD| clear - BD| clear - OFFB LOS]; lia]|].
      split; [exact STKx|].
      split; [eapply rw_cells_transport; [exact FRA| exact MUx| exact WMx| apply DJ; cbn; clear - DL LOS OFFD; lia]|].
      split; [exact MIx|].
      split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUx]]; unfold sub_fp; intros x Hx; apply (proj1 (fk_outside_app _ _ _)) in Hx; destruct Hx as [Hx _];
              clear - Hx HW; induction HW as [|[u v] W [Hle Hc] HW IH]; cbn; [exact I|]; cbn in Hle, Hc, Hx; unfold outside in Hx; cbn in Hx; split; [lia| exact IH]|].
      split; [exact (wmono_trans _ _ _ _ WM WMx)|].
      assert (AHx : AHEAP AI L RNG st LB mb).
      { eapply (AI_frame AI); [exact AH| exact MUx| exact WMx|]. clear - HW AID BOT SPH LOS. induction HW as [|[x y] W [Hle Hc] HW IH]; [apply Forall_nil|].
        apply Forall_cons; [| exact IH]. cbn [fst snd] in *. destruct Hc as [Hc|[Hc|[Hc|Hc]]].
        - apply fk_acr_inblk. destruct AID as (bb & Hb & Hb1 & Hb2). exists bb. split; [exact Hb| clear - Hle Hc Hb1 Hb2; lia].
        - apply fk_acr_inblk. destruct AID as (bb & Hb & Hb1 & Hb2). exists bb. split; [exact Hb| clear - Hle Hc Hb1 Hb2; lia].
        - apply fk_acr_inblk. destruct AID as (bb & Hb & Hb1 & Hb2). exists bb. split; [exact Hb| clear - Hle Hc Hb1 Hb2; lia].
        - eapply fk_acr_stack; [exact BOT| clear - Hc LOS; lia| clear - Hc Hle SPH; lia]. }
      split; [exact AHx|].
      split.
      { eapply ffr_pres_trans; [exact FFR|].
        eapply (dl_ffr_pres_app1 AI L RNG st LB ma mb _ W); [exact AH| exact LBH| | exact MUx| exact WMx].
        clear - HW OFFD BOT SPH LOS ABD. induction HW as [|[x y] W [Hle Hc] HW IH]; [apply Forall_nil|]. apply Forall_cons; [| exact IH]. cbn [fst snd] in *.
        split; [exact Hle|]. destruct Hc as [Hc|[Hc|[Hc|Hc]]].
        + right. split; [exists DCTX, (DCTX + 95992); split; [exact ABD| clear - Hle Hc; lia]|]. exists (DCTX + 24, DCTX + 32). split; [right; left; reflexivity| cbn [fst snd]; clear - Hc; lia].
        + right. split; [exists DCTX, (DCTX + 95992); split; [exact ABD| clear - Hle Hc; lia]|]. exists (DCTX + 30000, DCTX + 30004). split; [do 4 right; left; reflexivity| cbn [fst snd]; clear - Hc; lia].
        + right. split; [exists DCTX, (DCTX + 95992); split; [exact ABD| clear - Hle Hc; lia]|]. exists (DCTX + 30096, DCTX + 95940). split; [do 5 right; left; reflexivity| cbn [fst snd]; clear - Hc; lia].
        + left. clear - Hc Hle BOT LOS SPH. lia. }
      split; [eapply unpoisoned_munch; [exact UD| exact MUx| apply DJS; clear - DL ATR; lia]|].
      split; [intros NZ; eapply unpoisoned_munch; [exact (US NZ)| exact MUx| apply DJS; clear - SRCL SRCH NZ; lia]|].
      pose proof BUF as (B00 & _).
      split; [intros NZ; eapply unpoisoned_munch; [exact (UB NZ)| exact MUx| replace B1 with (B0 + (B1 - B0)) at 1 by (clear; lia); apply DJS; clear - NZ B1H B00; lia]|].
      split; [eapply aro_client_transport; [exact ARO| exact MUx| exact WMx| exact AW]|].
      eapply azstk_transport; [exact AZS| exact MUx| exact WMx| exact AW| clear - LOS; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma dl_fin2 : forall m1 hufv lev wsv litSize RV ty r LITB LBE loc dtb (xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs9 xs10 x28 x29 x30 x31 : word),
    DLB hufv lev wsv m1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    wnth wsv H5_litBuffer = Z_to_bv 64 LITB -> wnth wsv H5_litBufferEnd = Z_to_bv 64 LBE -> wnth wsv H5_litBufferLocation = Z_to_bv 64 loc ->
    bytes_at bsegs m1 (DCTX + 10296) dtb -> huf_hdr_ok dtb -> (zd_is_error r = false -> huf_tbl_ok dtb) -> hufv = Z_to_bv 64 (DCTX + 10296) ->
    0 <= litSize <= 131072 -> 1 <= RV <= zlen src -> (ty = 2 \/ ty = 3) -> 0 <= r < 2^64 ->
    ((loc = 0 /\ LBE = LITB + litSize /\ LITB = DCTX + 30372 /\ litSize <= 65536)
     \/ (loc = 1 /\ LBE = LITB + litSize /\ DST <= LITB /\ LBE + 32 <= DST + CAP)
     \/ (loc = 2 /\ 65536 < litSize /\ DST <= LITB /\ LBE + 32 <= DST + CAP /\ LITB <= LBE /\ LBE = LITB + litSize - 65536)) ->
    evtF bsegs RNG POST (ST 0x87d74 m1 xra x5 x6 x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize)
                           xa0 (Z_to_bv 64 DCTX) xa2 xa3 xa4 xa5 xa6 xa7
                           (Z_to_bv 64 r) xs3 xs4 (Z_to_bv 64 ty) (Z_to_bv 64 RV) (Z_to_bv 64 DCTX) xs9 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I KEEP ELB ELE ELOC HTB HOK VAL HUFE LSR RVR TYR RR PLACED. pose proof I as DLI. open_dlb I. dl_open CTX.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold KHIGH in KHI.
    pose proof (ARD ltac:(clear; lia)) as (ABD & _ & RDc & RDS). pose proof (fk_ablk_lits _ _ ABD) as DL.
    assert (DG : DCTX mod 8 = 0 /\ 0 <= DCTX /\ DCTX + 95992 <= 2^47) by (clear - DCA DCL DCH; lia).
    assert (EOFF : zlen dtb = 16388) by (destruct HOK as [EL _]; exact EL).
    pose proof (proj2 H5) as L5. destruct H5 as [H5C _].
    fk_hold OFFD. fk_hold OFFB. fk_hold OFFSRC. fk_hold BD. fk_hold BSRC. fk_hold SRCD. fk_hold DNULL. fk_hold DNN. fk_hold ADST. fk_hold AIS. fk_hold US. fk_hold UB.
    fk_hold KEEP. fk_hold MU. fk_hold FFR. fk_hold DLI. fk_hold DL. fk_hold TYR. fk_hold PLACED. fk_hold VAL. fk_hold RVR.
    clear MEMCPY MEMMOVE.
    zstep. zstep.                                          (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply Z_to_bv_eqm; reflexivity).
      unfold fk_held in DLI, KEEP. eapply (dl_ret m1 hufv lev wsv (2^64 - 20)); [exact DLI| clear; lia| exact KEEP| left; reflexivity]. }
    assert (NERR : zd_is_error r = false) by (unfold zd_is_error, ZE_maxCode; apply Z.ltb_ge; clear - K1 RR; lia).
    unfold fk_held in VAL. specialize (VAL NERR).
    h5_open wsv L5.
    lazymatch type of ELB with ?x = _ => subst x end. lazymatch type of ELE with ?x = _ => subst x end. lazymatch type of ELOC with ?x = _ => subst x end.
    assert (UDm : forall mm, munch [(DCTX + 24, DCTX + 32); (DCTX + 30000, DCTX + 30004); (DCTX + 30096, DCTX + 30372)] m1 mm -> unpoisoned mm DCTX (DCTX + 95992)).
    { intros mm MUm. eapply unpoisoned_munch; [exact UD| exact MUm|]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. unfold fk_held in DL. clear - DL ATR; repeat split; lia. }
    pose proof (munch_refl [(DCTX + 24, DCTX + 32); (DCTX + 30000, DCTX + 30004); (DCTX + 30096, DCTX + 30372)] m1) as MUs. pose proof (wmono_refl bsegs m1) as WMs.
    fk_hold HTB. fk_hold UDm. fk_hold SRCB. fk_hold XB. fk_hold BUF. fk_hold EHUF. fk_hold EWK. fk_hold FP. fk_hold ARO. fk_hold AZS. fk_hold AH. fk_hold US. fk_hold UB. fk_hold WM.
    zstep. zstep. zstep. dl_chk m1 (DCTX + 30352) UD RDS DG.      (* [comment removed for export] *)
    zstep. zstep. zstep. dl_chk m1 (DCTX + 30120) UD RDS DG.      (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    zstep. zstep. lazymatch type of MUs with munch _ _ ?mm => dl_chk mm (DCTX + 30152) (UDm mm MUs) RDS DG end.
    zstep.                                                 (* [comment removed for export] *)
    zstep. zstep. zstep. lazymatch type of MUs with munch _ _ ?mm => dl_chk mm (DCTX + 30000) (UDm mm MUs) RDS DG end.   (* [comment removed for export] *)
    zstep. zstep.                                          (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (FINISH : forall mm hufv2 (x5' xa0' xa1' xa2' xa3' : word),
              rw_cells bsegs mm DCTX [C8 llt; C8 mlt; C8 oft; C8 hufv2] -> hufv2 = Z_to_bv 64 (DCTX + 10296) ->
              rw_cells bsegs mm (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 (Z_to_bv 64 1); C4 fe] ->
              rw_cells bsegs mm (DCTX + 30096) ltac:(lazymatch type of H5C with rw_cells _ _ _ ?cs => exact cs end) ->
              munch [(DCTX + 24, DCTX + 32); (DCTX + 30000, DCTX + 30004); (DCTX + 30096, DCTX + 30372)] m1 mm -> wmono bsegs m1 mm -> mem_inv bsegs mm -> stk bsegs mm lo (SPV + -96) ->
              evtF bsegs RNG POST (ST 0x87e10 mm xra x5' x6 x7 (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize)
                           xa0' xa1' xa2' xa3' xa4 xa5 xa6 xa7
                           (Z_to_bv 64 r) xs3 xs4 (Z_to_bv 64 ty) (Z_to_bv 64 RV) (Z_to_bv 64 DCTX) xs9 xs10 x28 x29 x30 x31)).
    { intros mm hufv2 x5' xa0' xa1' xa2' xa3' PTq HUFE2 H3q H5q MUq WMq MIq STKq.
      zstep. zstep.                                        (* [comment removed for export] *)
      unfold fk_held in DLI, KEEP, HTB, RVR, PLACED.
      lazymatch type of H5q with rw_cells _ _ _ ?cs => let wl := cells_words cs in
        assert (DLBx : DLB hufv2 (Z_to_bv 64 1) wl mm);
        [ eapply (dlb_keep3 hufv lev hufv2 (Z_to_bv 64 1) _ wl m1 mm _ DLI MUq WMq MIq STKq PTq H3q (conj H5q eq_refl));
          apply Forall_cons; [cbn [fst snd]; clear; lia|]; apply Forall_cons; [cbn [fst snd]; clear; lia|]; apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil]
        | eapply (dl_ret mm hufv2 (Z_to_bv 64 1) wl RV); [exact DLBx| clear - RVR SLEN; lia| | ] ] end.
      - intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
      - right. split; [exact RVR|]. split.
        { eapply (hufw_of_full _ _ _ _ dtb HUFE2); [| exact HOK| intros _; exact VAL].
          eapply bytes_at_transport; [exact HTB| exact MUq|]. rewrite EOFF. cbn [disjoint_from]. clear. repeat split; lia. }
        exists LITB, litSize, LITB, LBE, loc.
        repeat (split; [first [reflexivity | clear - LSR PLACED; lia]|]).
        unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, ZSTD_LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH, DCTX_litExtraBuffer.
        destruct PLACED as [P|[P|P]]; [left | right; left | right; right]; repeat (split; [first [reflexivity | clear - P LSR; lia]|]); first [clear - P LSR; lia | left; clear - P LSR; lia]. }
    unfold fk_held in TYR. destruct TYR as [-> | ->].
    - (* [comment removed for export] *)
      zstep. if_false.
      zstep. zstep. zstep. lazymatch type of MUs with munch _ _ ?mm => dl_chk mm (DCTX + 24) (UDm mm MUs) RDS DG end.
      zstep. zstep. zstep.                                 (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      eapply FINISH; [exact PTRS| apply Z_to_bv_eqm; clear; f_equal; lia| exact H3| exact H5C| exact MUs| exact WMs| exact MI| exact STK].
    - (* [comment removed for export] *)
      zstep. if_true.
      eapply FINISH; [exact PTRS| exact HUFE| exact H3| exact H5C| exact MUs| exact WMs| exact MI| exact STK].
  Qed.

  (* [comment removed for export] *)
  Lemma dl_fin : forall m3 hufv lev wsv litSize litCSize lhSize ty A loc r dtb
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
  Proof.
    intros until x31. intros I KEEP ELB ELE ELOC HTB HOK VAL HUFE LHR LCS LHS LSR TYR RR PL3. pose proof I as DLI. open_dlb I. dl_open CTX.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold KHIGH in KHI.
    pose proof (ARD ltac:(clear; lia)) as (ABD & _ & RDc & RDS). pose proof (fk_ablk_lits _ _ ABD) as DL.
    assert (DG : DCTX mod 8 = 0 /\ 0 <= DCTX /\ DCTX + 95992 <= 2^47) by (clear - DCA DCL DCH; lia).
    assert (EOFF : zlen dtb = 16388) by (destruct HOK as [EL _]; exact EL).
    pose proof (proj2 H5) as L5. destruct H5 as [H5C _].
    fk_hold OFFD. fk_hold OFFB. fk_hold OFFSRC. fk_hold BD. fk_hold BSRC. fk_hold SRCD. fk_hold DNULL. fk_hold DNN. fk_hold ADST. fk_hold AIS. fk_hold US. fk_hold UB.
    fk_hold KEEP. fk_hold MU. fk_hold FFR. fk_hold DLI. fk_hold DL. fk_hold TYR. fk_hold VAL. fk_hold MEMCPY. fk_hold MEMMOVE.
    h5_open wsv L5.
    lazymatch type of ELB with ?x = _ => subst x end. lazymatch type of ELE with ?x = _ => subst x end. lazymatch type of ELOC with ?x = _ => subst x end.
    fk_hold SRCB. fk_hold XB. fk_hold BUF. fk_hold EHUF. fk_hold EWK. fk_hold FP. fk_hold ARO. fk_hold AZS. fk_hold AH. fk_hold WM. fk_hold HTB.
    zstep.                                                 (* [comment removed for export] *)
    zstep. zstep. zstep. dl_chk m3 (DCTX + 30368) UD RDS DG.      (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (GOFIN : forall mm ws9 LITB LBE (xra' x5' x6' x7' xa0' xa2' xa3' xa4' xa5' xa6' xa7' xs3' xs4' xs9' xs10' x28' x29' x30' x31' : word),
              DLB hufv lev ws9 mm -> (forall i, h5_block_owned i = false -> wnth ws9 i = wnth ws i) ->
              wnth ws9 H5_litBuffer = Z_to_bv 64 LITB -> wnth ws9 H5_litBufferEnd = Z_to_bv 64 LBE -> wnth ws9 H5_litBufferLocation = Z_to_bv 64 loc ->
              bytes_at bsegs mm (DCTX + 10296) dtb ->
              ((loc = 0 /\ LBE = LITB + litSize /\ LITB = DCTX + 30372 /\ litSize <= 65536)
               \/ (loc = 1 /\ LBE = LITB + litSize /\ DST <= LITB /\ LBE + 32 <= DST + CAP)
               \/ (loc = 2 /\ 65536 < litSize /\ DST <= LITB /\ LBE + 32 <= DST + CAP /\ LITB <= LBE /\ LBE = LITB + litSize - 65536)) ->
              evtF bsegs RNG POST (ST 0x87d74 mm xra' x5' x6' x7' (Z_to_bv 64 (DCTX + 29944)) (Z_to_bv 64 litSize)
                           xa0' (Z_to_bv 64 DCTX) xa2' xa3' xa4' xa5' xa6' xa7'
                           (Z_to_bv 64 r) xs3' xs4' (Z_to_bv 64 ty) (Z_to_bv 64 (lhSize + litCSize)) (Z_to_bv 64 DCTX) xs9' xs10' x28' x29' x30' x31')).
    { intros mm ws9 LITB LBE xra' x5' x6' x7' xa0' xa2' xa3' xa4' xa5' xa6' xa7' xs3' xs4' xs9' xs10' x28' x29' x30' x31' I9 K9 E1 E2 E3 HTB9 PL9. unfold fk_held in TYR, VAL.
      eapply (dl_fin2 mm hufv lev ws9 litSize (lhSize + litCSize) ty r LITB LBE loc dtb);
        [exact I9| exact K9| exact E1| exact E2| exact E3| exact HTB9| exact HOK| exact VAL| exact HUFE| clear - LSR BSM; lia| clear - LHR LCS LHS; lia| exact TYR| exact RR| exact PL9]. }
    destruct PL3 as [(-> & EA & SMALL) | [(-> & HC & P1 & P2) | (-> & BIG & HC & P1 & P2)]].
    - (* [comment removed for export] *)
      zstep. rewrite (sx32w_small 0) by (clear; lia). zstep. zstep. zstep. if_true.      (* [comment removed for export] *)
      unfold fk_held in DLI, KEEP, HTB.
      eapply (GOFIN m3 _ A (A + litSize)); [exact DLI| exact KEEP| reflexivity| reflexivity| reflexivity| exact HTB| left; clear - EA SMALL; lia].
    - (* [comment removed for export] *)
      zstep. rewrite (sx32w_small 1) by (clear; lia). zstep. zstep. zstep. if_true.
      unfold fk_held in DLI, KEEP, HTB.
      eapply (GOFIN m3 _ A (A + litSize)); [exact DLI| exact KEEP| reflexivity| reflexivity| reflexivity| exact HTB| right; left; clear - P1 P2; lia].
    - (* [comment removed for export] *)
      zstep. rewrite (sx32w_small 2) by (clear; lia). zstep. zstep. zstep. if_false.
      zstep. zstep. zstep. dl_chk m3 (DCTX + 30360) UD RDS DG.    (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      (* [comment removed for export] *)
      unfold fk_held in ADST, UB, OFFB, OFFD, BD, BUF, XB, WM.
      destruct (ADST ltac:(clear - HC B0D DCB; lia)) as (ARb & AHb & AIb). destruct (ARb ltac:(clear - HC B0D DCB; lia)) as (ABb & _ & RBa & RBb).
      pose proof (fk_ablk_lits _ _ ABb) as BBL.
      destruct (stk_split bsegs m3 B0 (A + litSize + -65536) B1 BUF ltac:(clear - P1 P2 B0D DCB BIG; lia)) as [_ BS1].
      destruct (stk_split bsegs m3 (A + litSize + -65536) (A + litSize + -65536 + 65536) B1 BS1 ltac:(clear - P1 P2 B0D DCB BIG; lia)) as [BSw _]. clear BS1.
      destruct (stk_bytes bsegs m3 _ _ BSw ltac:(clear; lia)) as (sb & SBL1 & SBA1). clear BSw.
      replace (A + litSize + -65536 + 65536 - (A + litSize + -65536)) with 65536 in SBL1 by (clear; lia).
      destruct (stk_open bsegs m3 (DCTX + 30372) (DCTX + 95940) (DCTX + 30372) (Z.to_nat 65536) XB ltac:(clear; lia) ltac:(clear; lia)) as (jk & DSTC & _ & XBb).
      assert (ART3 : art m3) by exact (dl_art_of_aheap AI _ _ _ _ _ AH).
      fk_hold XBb. fk_hold H5C. fk_hold BUF.
      zstep.                                               (* [comment removed for export] *)
      pose proof MEMCPY as MEMCPY1. unfold fk_held in MEMCPY1. unfold zd_memcpyZ_stmtA in MEMCPY1.
      eapply evtF_cut.
      { eapply (MEMCPY1 RNG (DCTX + 30372) (A + litSize + -65536) 65536 (SPV + -96)) with (lo := lo);
          first [ exact SBA1 | exact SBL1 | exact DSTC | exact STK | exact ART3 | exact MI | reflexivity
                | lazymatch goal with
                  | |- 0 <= 65536 <= _ => clear; lia
                  | |- lo <= SPV + -96 - _ => clear - LOS; lia
                  | |- SPV + -96 < _ => clear - SPH; lia
                  | |- A + litSize + -65536 + 65536 <= DCTX + 30372 \/ _ => clear - BD P1 P2 B0D DCB BIG; lia
                  | |- A + litSize + -65536 + 65536 <= SPV + -96 - _ \/ _ => clear - OFFB P1 P2 B0D DCB BIG LOS; lia
                  | |- DCTX + 30372 + 65536 <= lo \/ _ => clear - OFFD LOS; lia
                  | |- app_blk (A + _ + _) _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABb| clear - P1 B0D BIG; lia| clear - P2 DCB; lia]| clear; lia]
                  | |- app_blk _ _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABD| clear; lia| clear; lia]| clear; lia]
                  | |- aro _ _ (A + _ + _) _ => split; [eapply unpoisoned_sub; [exact (UB ltac:(clear - HC B0D DCB; lia))| clear - P1 B0D BIG; lia| clear - P2 DCB; lia]| split; [eapply rng_sub'; [exact RBa| clear - P1 P2 B0D DCB BIG; lia]| eapply rng_sub'; [exact RBb| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - P1 P2 B0D DCB BIG; Z.div_mod_to_equations; lia]]]
                  | |- aro _ _ _ _ => split; [eapply unpoisoned_sub; [exact UD| clear; lia| clear; lia]| split; [eapply rng_sub'; [exact RDc| clear; lia]| eapply rng_sub'; [exact RDS| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - DG; Z.div_mod_to_equations; lia]]]
                  | |- ahull _ _ (A + _ + _) _ => eapply dl_ahull_sub; [eapply dl_ahull_wmono; [exact AHb| exact WM]| clear - P1 B0D BIG; lia| clear - P2 DCB; lia]
                  | |- ahull _ _ _ _ => eapply dl_ahull_sub; [eapply dl_ahull_wmono; [exact AHD| exact WM]| clear; lia| clear; lia]
                  | |- astk _ _ _ => split; [unfold KHIGH; clear - KHI; lia| split; [eapply rng_sub'; [exact RSTK| clear - LOS; lia]| exact RI]]
                  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => apply Z_to_bv_eqm; clear; f_equal; lia
                  end
                | lazymatch goal with |- ?Gg => idtac "MEMCPY-LEFT:" Gg end ]. }
      cbv beta. intros ms' (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m4 & -> & MU4 & WM4 & MI4 & STK4 & DSTC4 & SB4).
      replace (ret_pc (Z_to_bv 64 0x87d30)) with (Z_to_bv 64 0x87d30) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      clear MEMCPY1 MEMCPY SBA1 SBL1 SB4 ART3.
      (* [comment removed for export] *)
      unfold fk_held in XBb, H5C, BUF, DLI.
      pose proof (stk_of_rw_cells bsegs _ _ _ DSTC4) as DSTS4. cbn [cells_size csize length] in DSTS4. rewrite Nat.add_0_r, Z2Nat.id in DSTS4 by (clear; lia).
      assert (BUF4 : stk bsegs m4 B0 B1).
      { eapply stk_transport_disjoint; [exact BUF| exact MU4| exact WM4| cbn [disjoint_from]; clear - OFFB BD B0D DCB B1H LOS HC; repeat split; lia]. }
      assert (XB4 : stk bsegs m4 (DCTX + 30372) (DCTX + 95940)).
      { eapply stk_merge; [exact DSTS4| | clear; lia]. eapply stk_transport_disjoint; [exact XBb| exact MU4| exact WM4| cbn [disjoint_from]; clear - OFFD LOS; repeat split; lia]. }
      pose proof (dlbK2 hufv lev _ m3 m4 _ DLI MU4 WM4 MI4 STK4 BUF4 XB4
                    ltac:(apply Forall_cons; [cbn [fst snd]; clear - LOS; lia|]; apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil])) as DLI4.
      assert (H54 : rw_cells bsegs m4 (DCTX + 30096) ltac:(lazymatch type of H5C with rw_cells _ _ _ ?cs => exact cs end)).
      { eapply rw_cells_transport; [exact H5C| exact MU4| exact WM4| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; clear - OFFD LOS; repeat split; lia]. }
      unfold fk_held in HTB.
      assert (HTB4 : bytes_at bsegs m4 (DCTX + 10296) dtb).
      { eapply bytes_at_transport; [exact HTB| exact MU4|]. rewrite EOFF. cbn [disjoint_from]. clear - OFFD LOS. repeat split; lia. }
      pose proof DLI4 as I4. unfold AZ_declit_a.DLB in I4. destruct I4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WM04 & AH4 & _ & UD4 & _ & UB4 & _).
      clear H5C XB XBb BUF DSTC4 DSTS4 MU4 WM4 PTRS EHUF EWK FP H3 SRCB STK FRA AH ARO AZS UD DLI MI HTB WM UB.
      fk_hold DLI4. fk_hold HTB4.
      zstep. zstep. zstep. dl_chk m4 (DCTX + 30352) UD4 RDS DG.    (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      (* [comment removed for export] *)
      destruct (stk_split bsegs m4 B0 (A + 65504) B1 BUF4 ltac:(clear - P1 P2 B0D DCB BIG; lia)) as [BUFa BU2].
      destruct (stk_split bsegs m4 (A + 65504) (A + 65504 + (litSize + -65536)) B1 BU2 ltac:(clear - P1 P2 B0D DCB BIG; lia)) as [DW BUFb]. clear BU2.
      pose proof (rdbl_of_stk bsegs _ _ _ BUF4) as RB4.
      assert (ART4 : art m4) by exact (dl_art_of_aheap AI _ _ _ _ _ AH4).
      fk_hold BUFa. fk_hold BUFb. fk_hold H54. fk_hold BUF4.
      zstep.                                               (* [comment removed for export] *)
      pose proof MEMMOVE as MEMMOVE1. unfold fk_held in MEMMOVE1. unfold zd_memmoveZ_stmtA in MEMMOVE1.
      eapply evtF_cut.
      { eapply (MEMMOVE1 RNG (A + 65504) A (litSize + -65536) (SPV + -96)) with (lo := lo);
          first [ exact DW | exact STK4 | exact ART4 | exact MI4 | reflexivity
                | lazymatch goal with
                  | |- rdbl _ _ _ _ => eapply rdbl_sub; [exact RB4| clear - P1 B0D; lia| clear - P2 DCB BIG; lia]
                  | |- 0 <= litSize + -65536 <= _ => clear - BIG LSR BSM; lia
                  | |- lo <= SPV + -96 - _ => clear - LOS; lia
                  | |- SPV + -96 < _ => clear - SPH; lia
                  | |- A + (litSize + -65536) <= SPV + -96 - _ \/ _ => clear - OFFB P1 P2 B0D DCB BIG LOS; lia
                  | |- A + 65504 + (litSize + -65536) <= lo \/ _ => clear - OFFB P1 P2 B0D DCB BIG LOS; lia
                  | |- app_blk (A + 65504) _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABb| clear - P1 B0D BIG; lia| clear - P2 DCB BIG; lia]| clear - BIG; lia]
                  | |- app_blk A _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABb| clear - P1 B0D; lia| clear - P2 DCB BIG; lia]| clear - BIG; lia]
                  | |- aro _ _ (A + 65504) _ => split; [eapply unpoisoned_sub; [exact (UB4 ltac:(clear - HC B0D DCB; lia))| clear - P1 B0D BIG; lia| clear - P2 DCB BIG; lia]| split; [eapply rng_sub'; [exact RBa| clear - P1 P2 B0D DCB BIG; lia]| eapply rng_sub'; [exact RBb| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - P1 P2 B0D DCB BIG; Z.div_mod_to_equations; lia]]]
                  | |- aro _ _ A _ => split; [eapply unpoisoned_sub; [exact (UB4 ltac:(clear - HC B0D DCB; lia))| clear - P1 B0D; lia| clear - P2 DCB BIG; lia]| split; [eapply rng_sub'; [exact RBa| clear - P1 P2 B0D DCB BIG; lia]| eapply rng_sub'; [exact RBb| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - P1 P2 B0D DCB BIG; Z.div_mod_to_equations; lia]]]
                  | |- ahull _ _ (A + 65504) _ => eapply dl_ahull_sub; [eapply dl_ahull_wmono; [exact AHb| exact WM04]| clear - P1 B0D BIG; lia| clear - P2 DCB BIG; lia]
                  | |- ahull _ _ A _ => eapply dl_ahull_sub; [eapply dl_ahull_wmono; [exact AHb| exact WM04]| clear - P1 B0D; lia| clear - P2 DCB BIG; lia]
                  | |- astk _ _ _ => split; [unfold KHIGH; clear - KHI; lia| split; [eapply rng_sub'; [exact RSTK| clear - LOS; lia]| exact RI]]
                  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => apply Z_to_bv_eqm; clear; f_equal; lia
                  end
                | lazymatch goal with |- ?Gg => idtac "MEMMOVE-LEFT:" Gg end ]. }
      cbv beta. intros ms' (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m5 & -> & MU5 & WM5 & MI5 & STK5 & DW5).
      replace (ret_pc (Z_to_bv 64 0x87d58)) with (Z_to_bv 64 0x87d58) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      clear MEMMOVE1 MEMMOVE RB4 ART4 DW.
      (* [comment removed for export] *)
      unfold fk_held in BUFa, BUFb, H54, DLI4, HTB4, BUF4.
      assert (BUF5 : stk bsegs m5 B0 B1).
      { eapply stk_merge; [eapply stk_merge; [| exact DW5| clear - P1 B0D BIG; lia]| | clear - P1 P2 B0D DCB BIG; lia].
        - eapply stk_transport_disjoint; [exact BUFa| exact MU5| exact WM5| cbn [disjoint_from]; clear - OFFB P1 P2 B0D DCB BIG LOS; repeat split; lia].
        - eapply stk_transport_disjoint; [exact BUFb| exact MU5| exact WM5| cbn [disjoint_from]; clear - OFFB P1 P2 B0D DCB BIG LOS B1H; repeat split; lia]. }
      assert (XB5 : stk bsegs m5 (DCTX + 30372) (DCTX + 95940)).
      { eapply stk_transport_disjoint; [exact XB4| exact MU5| exact WM5| cbn [disjoint_from]; clear - OFFD LOS BD P1 P2 B0D DCB BIG; repeat split; lia]. }
      pose proof (dlbK2 hufv lev _ m4 m5 _ DLI4 MU5 WM5 MI5 STK5 BUF5 XB5
                    ltac:(apply Forall_cons; [cbn [fst snd]; clear - LOS; lia|]; apply Forall_cons; [cbn [fst snd]; clear - HC P1 P2 BIG; lia| apply Forall_nil])) as DLI5.
      assert (H55 : rw_cells bsegs m5 (DCTX + 30096) ltac:(lazymatch type of H54 with rw_cells _ _ _ ?cs => exact cs end)).
      { eapply rw_cells_transport; [exact H54| exact MU5| exact WM5| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; clear - OFFD LOS BD P1 P2 B0D DCB BIG; repeat split; lia]. }
      assert (HTB5 : bytes_at bsegs m5 (DCTX + 10296) dtb).
      { eapply bytes_at_transport; [exact HTB4| exact MU5|]. rewrite EOFF. cbn [disjoint_from]. clear - OFFD LOS BD P1 P2 B0D DCB BIG. repeat split; lia. }
      clear BUFa BUFb H54 DLI4 HTB4 BUF4 DW5 MU5 WM5 STK4 MI4 AH4 UD4 UB4 WM04 BUF5 XB5.
      pose proof (munch_refl [(DCTX + 30096, DCTX + 30372)] m5) as MUs. pose proof (wmono_refl bsegs m5) as WMs.
      fk_hold DLI5. fk_hold HTB5.
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      zstep.                                               (* [comment removed for export] *)
      unfold fk_held in DLI5, HTB5, KEEP.
      lazymatch type of H55 with rw_cells _ ?mm _ ?cs => let wl := cells_words cs in
        assert (DLBx : DLB hufv lev wl mm);
        [ eapply (dlbK hufv lev _ wl m5 mm _ DLI5 MUs WMs MI5 STK5 (conj H55 eq_refl));
          apply Forall_cons; [cbn [fst snd]; clear; lia| apply Forall_nil]
        | eapply (GOFIN mm wl (A + 65504) (A + litSize + -32));
          [ exact DLBx
          | intros i Hi; specialize (KEEP i Hi); do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]); exact KEEP
          | reflexivity | reflexivity | reflexivity
          | eapply bytes_at_transport; [exact HTB5| exact MUs| rewrite EOFF; cbn [disjoint_from]; clear; repeat split; lia]
          | right; right; clear - BIG P1 P2; lia ] ] end.
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
