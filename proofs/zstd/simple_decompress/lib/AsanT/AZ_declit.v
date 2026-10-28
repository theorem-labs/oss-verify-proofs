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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_globals AZ_globalsR AZ_frame_iface AZ_huf_iface AZ_block_iface AZ_blk_iface4 AZ_blk_iface5 AZ_libc_iface AZ_hufinv AZ_kx AZ_declit_a
     AZ_declit_b AZ_declit_c AZ_declit_d AZ_declit_d2 AZ_declit_d3 AZ_declit_e AZ_declit_f AZ_declit_g.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac kx_rd_at ::=
  lazymatch goal with
  | |- rd_at ?segs ?m ?A ?N =>
      match goal with
      | H : bytes_at segs m ?A0 ?bs |- _ => apply (rd_at_sub segs m A0 (Z.of_nat (length bs)) A N (rd_at_bytes_at segs m A0 bs H)); kx_lia
      | H : u8arr segs m ?A0 ?bs |- _ => apply (rd_at_sub segs m A0 (Z.of_nat (length bs)) A N (rd_at_u8arr segs m A0 bs H)); kx_lia
      | H : rw_cells segs m ?A0 ?cs |- _ =>
          let n := eval lazy in (Z.of_nat (cells_size cs)) in
          apply (rd_at_sub segs m A0 n A N (rd_at_rw_cells segs m A0 cs H)); kx_lia
      | H : ro_cells segs m ?A0 ?cs |- _ =>
          let n := eval lazy in (Z.of_nat (cells_size cs)) in
          apply (rd_at_sub segs m A0 n A N (rd_at_ro_cells segs m A0 cs H)); kx_lia
      | H : stk segs m ?lo ?hi |- _ => apply (rd_at_sub segs m lo (hi - lo) A N); [apply (rd_at_stk segs m lo hi H); kx_lia | kx_lia | kx_lia]
      | _ => (* [comment removed for export] *)
          let A' := eval lazy in A in
          lazymatch A' with
          | Z0 => idtac | Zpos _ => idtac
          | _ => fail 0 "kx_rd_at: no chunk hypothesis justifies the region at" A
          end;
          apply (rd_at_imgZ segs m A N); [lia | lia | lia | vm_compute; reflexivity]
      end
  end.

Notation zlen l := (Z.of_nat (length l)).
Notation SHB := 2147450880.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma dl_h5_isf_cell : forall (m1 : amem) D wsq, dctx_h5 bsegs m1 D wsq -> rw_cells bsegs m1 (D + 30176) [C4 (wnth wsq H5_isFrameDecompression)].
Proof.
  intros m1 D wsq (C & L). h5_open wsq L.
  lazymatch type of C with rw_cells _ _ _ ?cs =>
    change cs with (firstn 12 cs ++ [nth 12 cs (C1 (Z_to_bv 8 0))] ++ skipn 13 cs) in C end.
  cbn [firstn skipn nth] in C.
  apply rw_cells_app in C. destruct C as [_ C]. apply rw_cells_app in C. destruct C as [C _].
  cbn [cells_size csize Nat.add] in C. replace (D + 30096 + Z.of_nat 80) with (D + 30176) in C by lia. exact C.
Qed.

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
  Ltac hlia := unfold fk_held in *; lia.

  (* [comment removed for export] *)
  Ltac dl_kx_gen :=
    repeat match goal with |- context [bv_unsigned (ev ?E ?j)] => let c := fresh "c" in set (c := bv_unsigned (ev E j)) in *; clearbody c end;
    repeat match goal with |- context [ev ?E ?j] => let w := fresh "kw" in set (w := ev E j) in *; clearbody w end.

  (* [comment removed for export] *)
  Hypothesis ALLOCLIT : zd_alloclit_stmtA.
  Hypothesis MEMCPY : zd_memcpyZ_stmtA.
  Hypothesis MEMSET : zd_memsetZ_stmtA.
  Hypothesis MEMMOVE : zd_memmoveZ_stmtA.
  Hypothesis FHL : fake_heap_law AI.
  Hypothesis H1X : huf_1x_stmtA.
  Hypothesis H4X : huf_4x_stmtA.
  Hypothesis H1W : huf_1x1_wksp_stmtA AI rng_fs.
  Hypothesis H4W : huf_4x_wksp_stmtA AI rng_fs.

  (* [comment removed for export] *)
  Let PJOINi := (AZ_declit_d3.dl_fin AI rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe ws
                   CTX MEMCPY MEMMOVE).
  Let PHUFi := (AZ_declit_d2.dl_huf AI rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe ws
                   CTX FHL H1X H4X H1W H4W PJOINi).
  Let PCMPi := (AZ_declit_d.dl_cmp AI rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe ws
                   CTX ALLOCLIT MEMCPY MEMMOVE H1X H4X H1W H4W PHUFi).
  Let PRAWi := (AZ_declit_b.dl_raw AI rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe ws
                   CTX ALLOCLIT MEMCPY).
  Let PRLEi := (AZ_declit_c.dl_rle AI rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe ws
                   CTX ALLOCLIT MEMSET).
  Let HRAWi := (AZ_declit_e.dl_hdr_raw2 AI rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe ws
                   CTX PRAWi).
  Let HRLEi := (AZ_declit_f.dl_hdr_rle2 AI rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe ws
                   CTX PRLEi).
  Let HCMPi := (AZ_declit_g.dl_hdr_comp AI rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe ws
                   CTX PCMPi).

  (* [comment removed for export] *)
  Lemma dlb_init : forall hufv lev (mp : amem),
    dctx_ptrs bsegs m0 DCTX llt mlt oft hufv ->
    stk bsegs m0 (DCTX + 10296) (DCTX + 26684) -> stk bsegs m0 (DCTX + 27324) (DCTX + 29884) ->
    rw_cells bsegs m0 (DCTX + 29928) (zfh_cells h) -> dctx_h3 bsegs m0 DCTX pcs dsz bt stg lev fe -> dctx_h5 bsegs m0 DCTX ws ->
    stk bsegs m0 (DCTX + 30372) (DCTX + 95940) -> bytes_at bsegs m0 LSRC (map (Z_to_bv 8) src) -> stk bsegs m0 B0 B1 ->
    aro_client RNG m0 -> azstk RNG m0 lo SPV ->
    munch [(SPV + -96, SPV)] m0 mp -> wmono bsegs m0 mp -> mem_inv bsegs mp ->
    rw_cells bsegs mp (SPV + -96) DSAVED -> stk bsegs mp lo (SPV + -96) ->
    DLB hufv lev ws mp.
  Proof.
    intros hufv lev mp PTRS EHUF EWK FP H3 H5 XB SRCB BUF ARO AZS MUx WMx MIx FRA STKx. dl_open CTX.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold KHIGH in KHI.
    pose proof (ARD ltac:(clear; lia)) as (ABD & UD & _). pose proof (fk_ablk_lits _ _ ABD) as DL.
    pose proof (bytes_at_bound _ _ _ _ SRCB) as SBL. rewrite length_map in SBL.
    assert (DJ : forall X n, 0 <= n -> (X + n <= SPV + -96 \/ SPV <= X) -> disjoint_from [(SPV + -96, SPV)] X n).
    { intros X n Hn A. cbn [disjoint_from]. split; [clear - Hn A; lia| exact I]. }
    assert (DJS : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(SPV + -96, SPV)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X n A B C. rewrite !shad_div. unfold ASHOFF. apply DJ; clear - A B C DL KHI LOS ATR; Z.div_mod_to_equations; lia. }
    assert (AW : aappW [(SPV + -96, SPV)]).
    { unfold aappW. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold KLOW, KHIGH. clear - DL KHI LOS SPH ATR. lia. }
    unfold dctx_ptrs, dctx_h3, zfh_cells in *.
    split; [eapply rw_cells_transport; [exact PTRS| exact MUx| exact WMx| apply DJ; cbn; clear - DL LOS OFFD; lia]|].
    split; [eapply stk_transport_disjoint; [exact EHUF| exact MUx| exact WMx| apply DJ; clear - DL LOS OFFD; lia]|].
    split; [eapply stk_transport_disjoint; [exact EWK| exact MUx| exact WMx| apply DJ; clear - DL LOS OFFD; lia]|].
    split; [eapply rw_cells_transport; [exact FP| exact MUx| exact WMx| apply DJ; cbn; clear - DL LOS OFFD; lia]|].
    split; [eapply rw_cells_transport; [exact H3| exact MUx| exact WMx| apply DJ; cbn; clear - DL LOS OFFD; lia]|].
    split; [destruct H5 as [H5C L5]; split; [| exact L5]; eapply rw_cells_transport; [exact H5C| exact MUx| exact WMx| rewrite (h5_cells_size ws L5); apply DJ; cbn; clear - DL LOS OFFD; lia]|].
    split; [eapply stk_transport_disjoint; [exact XB| exact MUx| exact WMx| apply DJ; clear - DL LOS OFFD; lia]|].
    split; [eapply bytes_at_transport; [exact SRCB| exact MUx| rewrite length_map; apply DJ; [clear - SBL| clear - OFFSRC LOS]; lia]|].
    split; [eapply stk_transport_disjoint; [exact BUF| exact MUx| exact WMx| apply DJ; [clear - B0D DCB CAP0| clear - OFFB LOS]; lia]|].
    split; [exact STKx|].
    split; [exact FRA|].
    split; [exact MIx|].
    split; [eapply munch_weaken; [| exact MUx]; unfold sub_fp; intros x Hx; apply (proj1 (fk_outside_app _ _ _)) in Hx; destruct Hx as [Hx _];
            cbn [outside] in Hx |- *; clear - Hx; lia|].
    split; [exact WMx|].
    assert (AHx : AHEAP AI L RNG st LB mp).
    { eapply (AI_frame AI); [exact AH0| exact MUx| exact WMx|]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      eapply fk_acr_stack; [exact BOT| clear - LOS; lia| clear - SPH; lia]. }
    split; [exact AHx|].
    split.
    { eapply dl_ffr_pres_weaken.
      - eapply (dl_ffr_pres_app1 AI L RNG st LB m0 mp (@nil (Z * Z)) [(SPV + -96, SPV)]); [exact AH0| exact LBH| | exact MUx| exact WMx].
        apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. split; [clear; lia|]. left. clear - BOT LOS SPH. lia.
      - unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx. lia. }
    split; [eapply unpoisoned_munch; [exact UD| exact MUx| apply DJS; clear - DL ATR; lia]|].
    split; [intros NZ; pose proof (ARS NZ) as (_ & USv & _); eapply unpoisoned_munch; [exact USv| exact MUx| apply DJS; clear - SRCL SRCH NZ; lia]|].
    pose proof BUF as (B00 & _).
    split; [intros NZ; pose proof (proj1 (ADST NZ) ltac:(clear - NZ; lia)) as (_ & UBv & _); replace (B0 + (B1 - B0)) with B1 in UBv by (clear; lia);
            eapply unpoisoned_munch; [exact UBv| exact MUx| replace B1 with (B0 + (B1 - B0)) at 1 by (clear; lia); apply DJS; clear - NZ B1H B00; lia]|].
    split; [eapply aro_client_transport; [exact ARO| exact MUx| exact WMx| exact AW]|].
    eapply azstk_transport; [exact AZS| exact MUx| exact WMx| exact AW| clear - LOS; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma dl_top : forall m1 hufv lev xra x5 x6 x7 xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 x28 x29 x30 x31,
    DLB hufv lev ws m1 -> HUFINVw m1 DCTX hufv lev -> 2 <= zlen src ->
    evtF bsegs RNG POST
      (MS (mkR xra (Z_to_bv 64 (SPV + -96)) gp tp x5 x6 x7 xs0 xs1 (Z_to_bv 64 DCTX) (Z_to_bv 64 LSRC) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 DST)
               (Z_to_bv 64 CAP) (Z_to_bv 64 0) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x875a4) fc None m1 (seg_rom bsegs)).
  Proof.
    intros until x31. intros I HW S2. pose proof I as DLI. open_dlb I. dl_open CTX.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold KHIGH in KHI.
    pose proof (bytes_at_bound _ _ _ _ SRCB) as SBL. rewrite length_map in SBL.
    assert (NZ : 0 < zlen src) by (clear - S2; lia).
    pose proof (US NZ) as USv. pose proof (ARS NZ) as (ABS & _ & RSa & RSb). pose proof (fk_ablk_lits _ _ ABS) as SBB.
    pose proof (ARD ltac:(clear; lia)) as (ABD & _ & RDc & RDS). pose proof (fk_ablk_lits _ _ ABD) as DL.
    assert (DG : DCTX mod 8 = 0 /\ 0 <= DCTX /\ DCTX + 95992 <= 2^47) by (clear - DCA DCL DCH; lia).
    assert (LSM : Z.of_nat (length (map (Z_to_bv 8) src)) = zlen src) by (rewrite length_map; reflexivity).
    assert (KEEP : forall i, h5_block_owned i = false -> wnth ws i = wnth ws i) by (intros i _; reflexivity).
    pose proof (dl_art_of_aheap _ _ _ _ _ _ AH) as (GOT & _ & SHBc & _).
    pose proof (dl_h5_isf_cell _ _ _ H5) as ISFC. rewrite ISF in ISFC.
    pose proof (proj2 H5) as L5. destruct H5 as [H5C _].
    set (b0 := Znth 0 src) in *.
    assert (B0R : 0 <= b0 < 256) by (subst b0; apply AZ_declit_e.dl_byte_range; [exact FBY| clear - S2; lia]).
    (* [comment removed for export] *)
    clear EHUF EWK H3 XB BUF STK MU WM FFR UB AZS US AH ARO.
    clear AFP AH0 ASH ART0 RSTK RFS BOT SPT SP16 RSTKT LBH ARD AHD AID AHS AIS ADST OFFD OFFB OFFSRC BD BSRC SRCD.
    fk_hold DLI. fk_hold KEEP. fk_hold HW. fk_hold DNULL. fk_hold DNN. fk_hold ARS. fk_hold PTRS. fk_hold FP. fk_hold H5C. fk_hold ISFC. fk_hold FRA.
    kx_autoFLAx [KAUnp LSRC 2; KAApp LSRC 2] [0x875c0] 30%nat [KZRange LSRC 6443008 (2^47 - 131072); KZRange DCTX 6443008 (2^47 - 95992); KZAlign DCTX 8] (@nil (Z * Z)) (@nil (Z * Z)).
    all: try kx_cell_lit.
    all: try (kx_acc RI).
    all: try kx_mem.
    all: kx_abs.
    all: dl_kx_gen.
    all: repeat match goal with H : context [ev ?E _] |- _ => clear H end.
    all: clear KXA KXRD KXK KXMI; clear KXE.
    unfold fk_held in PTRS, FP, ISFC, FRA.
    (* [comment removed for export] *)
    zstep. zstep. zstep.                                       (* [comment removed for export] *)
    rewrite !(Z.mod_small LSRC 18446744073709551616) by (clear - SBL SRCH; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep.                                       (* [comment removed for export] *)
    pose proof (dl_sh_rd0s m1 DCTX 95992 (DCTX + 30176) UD ltac:(clear; lia) ltac:(clear - DG; Z.div_mod_to_equations; lia) ltac:(clear - DG; lia) ltac:(clear - DG; lia)) as RDz.
    pose proof (dl_sh_rng1 RNG DCTX (DCTX + 30176) RDS (proj1 DG) ltac:(clear; lia) ltac:(clear; lia)) as RTz.
    zstep. clear RDz RTz.                                      (* [comment removed for export] *)
    try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
    assert (RD : ov_read_bytes bsegs m1 (Z_to_bv 64 LSRC) 1 = Some [Z_to_bv 8 b0])
      by (subst b0; eapply zd_src_rd; [exact SRCB | clear - S2; lia | clear; lia]).
    zstep. cbv beta. rewrite (byte_lit8 b0) by exact B0R. clear RD.   (* [comment removed for export] *)
    zstep; if_false.                                           (* [comment removed for export] *)
    zstep. try rewrite (sx32w_small 1) by (clear; lia).        (* [comment removed for export] *)
    zstep; if_cases KI; zify_cond KI; [exfalso; clear - KI; lia|].   (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep.                                              (* [comment removed for export] *)
    pose proof (dl_sh_rd0s m1 DCTX 95992 (DCTX + 29944) UD ltac:(clear; lia) ltac:(clear - DG; Z.div_mod_to_equations; lia) ltac:(clear - DG; lia) ltac:(clear - DG; lia)) as RDz.
    pose proof (dl_sh_rng1 RNG DCTX (DCTX + 29944) RDS (proj1 DG) ltac:(clear; lia) ltac:(clear; lia)) as RTz.
    zstep. clear RDz RTz.                                      (* [comment removed for export] *)
    try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
    zstep; if_false.                                           (* [comment removed for export] *)
    zstep. rewrite (zx32w_small (fh_bsmax h)) by (clear - BSM; lia).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep.                                              (* [comment removed for export] *)
    set (ty := Z.land b0 3) in *.
    assert (TYB : 0 <= ty <= 3).
    { subst ty. change 3 with (Z.ones 2). rewrite Z.land_ones by (clear; lia). change (Z.ones 2) with 3. change (2^2) with 4.
      pose proof (Z.mod_pos_bound b0 4 ltac:(clear; lia)) as X. clear - X. lia. }
    unfold fk_held in DLI, KEEP, HW, DNN, DNULL.
    replace (LSRC / 8 + 2147450880) with (2147450880 + LSRC / 8) by (clear; lia).
    zstep; if_cases KT; zify_cond KT; rewrite (signed_lit ty) in KT by (clear - TYB; lia).   (* [comment removed for export] *)
    { (* [comment removed for export] *)
      eapply (HCMPi m1 hufv lev ws ty); [exact DLI| exact ISF| exact KEEP| exact HW| exact S2| clear - KT TYB; lia]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep.                                       (* [comment removed for export] *)
    set (lhlv := Z.shiftr (Z.shiftl b0 60 mod 18446744073709551616) 62) in *.
    assert (LHLR : 0 <= lhlv < 2^64) by (subst lhlv; rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by (clear; lia); clear - B0R; Z.div_mod_to_equations; lia).
    zstep; if_cases KR; zify_cond KR.                          (* [comment removed for export] *)
    - (* [comment removed for export] *)
      zstep; if_cases KE; zify_cond KE.                        (* [comment removed for export] *)
      + pose proof (HRLEi m1 hufv lev ws lhlv) as Lx. replace (Z.min (fh_bsmax h) CAP) with (fh_bsmax h) in Lx by (clear - KE; lia).
        eapply Lx; [exact DLI| exact ISF| exact KEEP| exact HW| exact S2| exact LHLR].
      + zstep.                                                 (* [comment removed for export] *)
        pose proof (HRLEi m1 hufv lev ws lhlv) as Lx. replace (Z.min (fh_bsmax h) CAP) with CAP in Lx by (clear - KE; lia).
        eapply Lx; [exact DLI| exact ISF| exact KEEP| exact HW| exact S2| exact LHLR].
    - (* [comment removed for export] *)
      zstep; if_cases KE; zify_cond KE.                        (* [comment removed for export] *)
      + pose proof (HRAWi m1 hufv lev ws lhlv) as Lx. replace (Z.min (fh_bsmax h) CAP) with (fh_bsmax h) in Lx by (clear - KE; lia).
        eapply Lx; [exact DLI| exact ISF| exact KEEP| exact HW| exact S2| exact LHLR].
      + zstep.                                                 (* [comment removed for export] *)
        pose proof (HRAWi m1 hufv lev ws lhlv) as Lx. replace (Z.min (fh_bsmax h) CAP) with CAP in Lx by (clear - KE; lia).
        eapply Lx; [exact DLI| exact ISF| exact KEEP| exact HW| exact S2| exact LHLR].
  Qed.
End DL.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section THM.
  Variable AI : AMallocIface.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis ALLOCLIT : zd_alloclit_stmtA.
  Hypothesis MEMCPY : zd_memcpyZ_stmtA.
  Hypothesis MEMSET : zd_memsetZ_stmtA.
  Hypothesis MEMMOVE : zd_memmoveZ_stmtA.
  Hypothesis FHL : fake_heap_law AI.
  Hypothesis H1X : huf_1x_stmtA.
  Hypothesis H4X : huf_4x_stmtA.
  Hypothesis H1W : huf_1x1_wksp_stmtA AI rng_fs.
  Hypothesis H4W : huf_4x_wksp_stmtA AI rng_fs.

  Theorem zd_declit_proofA : zd_declit_stmtA AI rng_fs.
  Proof.
    unfold zd_declit_stmtA, APZD_DECLIT. intros until ws.
    intros PTRS EHUF HINV EWK FP BSM H3 H5 ISF XB DCL DCH DCA SRCB FBY SLEN SRCL SRCH BUF B0D DCB CAP0 B1H DNULL DNN STK LO0 LOS SPH
           OFFD OFFB OFFSRC BD BSRC SRCD AFP TP AZS ARO DCA2 ARD AHD AID ARS AHS AIS ADST MI -> -> -> -> -> ->.
    assert (CTX : AZ_declit_a.DLCTX AI rng_fs L RNG st LB tp m SPV lo DCTX DST CAP B0 B1 LSRC src h ws).
    { split; [| split; [| split]].
      - repeat split; first [assumption | lia].
      - repeat split; assumption.
      - repeat split; first [assumption | lia].
      - exact (conj AFP (conj TP (conj ARD (conj AHD (conj AID (conj ARS (conj AHS (conj AIS ADST)))))))). }
    pose proof AFP as (AH0 & ASH & ART0 & (KHI & RSTK & RI) & RFS & BOT & SPT & SP16 & RSTKT & LBH).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold KHIGH in KHI.
    pose proof (ARD ltac:(clear; lia)) as (ABD & _). pose proof (fk_ablk_lits _ _ ABD) as DL.
    pose proof (bytes_at_bound _ _ _ _ SRCB) as SBL. rewrite length_map in SBL.
    pose proof (munch_refl [(SPV + -96, SPV)] m) as MUs. pose proof (wmono_refl bsegs m) as WMs.
    fk_hold PTRS. fk_hold EHUF. fk_hold HINV. fk_hold EWK. fk_hold FP. fk_hold H3. fk_hold H5. fk_hold XB. fk_hold SRCB. fk_hold BUF.
    fk_hold AFP. fk_hold AZS. fk_hold ARO. fk_hold ARD. fk_hold AHD. fk_hold ARS. fk_hold AHS. fk_hold ADST. fk_hold AH0. fk_hold ART0.
    (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    carve_frame 96%nat STK.
    do 12 zstep.                                               (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mp end.
    unfold fk_held in *.
    assert (DLI : AZ_declit_a.DLB AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m SPV lo DCTX DST CAP B0 B1 LSRC src h llt mlt oft pcs dsz bt stg fe huf le ws mp).
    { eapply dlb_init; [exact CTX| exact PTRS| exact EHUF| exact EWK| exact FP| exact H3| exact H5| exact XB| exact SRCB| exact BUF| exact ARO| exact AZS
                       | exact MUs| exact WMs| exact MI| exact FR| exact STK]. }
    assert (HW : HUFINVw mp DCTX huf le).
    { eapply hufw_fine; [exact HINV| exact MUs|]. intros x Hx. cbn [outside]. clear - Hx LOS OFFD DL. lia. }
    clear PTRS EHUF HINV EWK FP H3 H5 XB SRCB BUF.
    zstep. zstep; if_cases K0; zify_cond K0.                   (* [comment removed for export] *)
    - (* [comment removed for export] *)
      eapply dl_top; [exact CTX| exact ALLOCLIT| exact MEMCPY| exact MEMSET| exact MEMMOVE| exact FHL| exact H1X| exact H4X| exact H1W| exact H4W
                    | exact DLI| exact HW| clear - K0; lia].
    - (* [comment removed for export] *)
      unfold AZ_declit_a.DLB in DLI.
      destruct DLI as (PTRS & EHUF & EWK & FP & H3 & H5 & XB & SRCB & BUF & STK' & FRA & MI' & MU & WM & AH & FFR & UD & US & UB & ARO' & AZS').
      zstep.                                                   (* [comment removed for export] *)
      replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply Z_to_bv_eqm; reflexivity).
      zstep.                                                   (* [comment removed for export] *)
      do 12 zstep.                                             (* [comment removed for export] *)
      zstep. zstep.                                            (* [comment removed for export] *)
      apply evtF_done. unfold zd_declit_postA.
      do 14 eexists. exists mp, (2^64 - 20), huf, le, ws. split; [reflexivity|].
      pose proof (stk_of_rw_cells bsegs _ _ _ FRA) as FRAS. cbn [cells_size csize Nat.add length] in FRAS.
      split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
      split; [eapply stk_merge; [exact STK'| replace SPV with (SPV + -96 + Z.of_nat 96) at 2 by (clear; lia); exact FRAS| clear - LOS; lia]|].
      split; [exact FFR|]. split; [exact AH|]. split; [exact BUF|].
      split; [exact PTRS|]. split; [exact EHUF|]. split; [exact EWK|]. split; [exact H3|]. split; [exact H5|]. split; [intros i _; reflexivity|].
      split; [exact XB|]. split; [clear; lia| left; reflexivity].
  Qed.
End THM.
End CANSEC1.
(* [comment removed for export] *)
