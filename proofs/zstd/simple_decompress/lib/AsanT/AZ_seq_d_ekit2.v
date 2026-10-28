(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_ibase AZ_seq_d_iat.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sqd_at_anchor (P : sqp) : Prop :=
  forall (ja jb jc jds jp jm : list byte) (x1 x5 x6 x7 x17 x25 x28 x29 x30 x31 : word),
  rw_cells bsegs (w_m P) (w_FRB P) [CB 96 ja; C8 (Z_to_bv 64 (w_DST P)); CB 56 jb; CB 16 (w_j224 P); CB 40 jc] ->
  rw_cells bsegs (w_m P) (w_FF P) [CB 32 (w_jfh P); CB 88 jds; CB 24 jp; CB 104 (w_j144 P); C8 (Z_to_bv 64 (w_fflag P (w_L P) 2 (w_FF P)))] ->
  rw_cells bsegs (w_m P) (w_SHF P) [CB 4 (w_jsh0 P); CB 14 jm; CB 14 (w_jsh1 P)] ->
  stk bsegs (w_m P) (w_lo P) (w_FRB P) -> stk bsegs (w_m P) (w_FRB P + 216) (w_SPV P + -104) ->
  rw_cells bsegs (w_m P) (w_SPV P + -104) (sqd_saved P) ->
  evtF bsegs (w_RNG P) (sqd_post P)
    (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P))
             (Z_to_bv 64 (w_DCTX P + 29896)) (Z_to_bv 64 (w_DCTX P + 30368)) (Z_to_bv 64 (Z.shiftr (w_DCTX P + 30368) 3 + 2147450880))
             (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 0x92de0) (Z_to_bv 64 18446744073709551601) (Z_to_bv 64 (w_FF P)) x17
             (Z_to_bv 64 (w_SHF P)) (Z_to_bv 64 (w_CAP P)) (Z_to_bv 64 28672) (Z_to_bv 64 (zlen (w_sq P))) (Z_to_bv 64 (w_SEQ P)) (Z_to_bv 64 (w_FF P)) (Z_to_bv 64 (w_nbSeq P))
             x25 (Z_to_bv 64 2147450880) (Z_to_bv 64 (w_DCTX P)) x28 x29 x30 x31)
        (w_F P) (Z_to_bv 64 0x92f54) (w_fc P) None (w_m P) (seg_rom bsegs)).

(* [comment removed for export] *)
Lemma sqd_art_trW : forall (m m' : amem) W, art m -> munch W m m' -> wmono bsegs m m' ->
  (forall A k, 0 <= A -> A + k <= 6443008 -> disjoint_from W A k) -> art m'.
Proof.
  intros m m' W (G1 & G2 & G3 & G4 & G5 & G6) MU WM HW.
  assert (TC : forall A cs, rw_cells bsegs m A cs -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 6443008 -> rw_cells bsegs m' A cs).
  { intros A cs H HA HB. eapply rw_cells_transport; [exact H | exact MU | exact WM | apply HW; [exact HA | exact HB]]. }
  unfold art. split; [apply TC; [exact G1 | cbn; clear; lia | cbn; clear; lia]|]. split; [apply TC; [exact G2 | cbn; clear; lia | cbn; clear; lia]|].
  split; [apply TC; [exact G3 | cbn; clear; lia | cbn; clear; lia]|]. split; [apply TC; [exact G4 | cbn; clear; lia | cbn; clear; lia]|].
  split; [apply TC; [exact G5 | cbn; clear; lia | cbn; clear; lia]|]. apply TC; [exact G6 | cbn; clear; lia | cbn; clear; lia].
Qed.

(* [comment removed for export] *)
Definition zb1 : cell := CB 1 (le1 (Z_to_bv 64 0)).
Lemma sqd_sh14 : forall (m1 : amem) A a b,
  rw_cells bsegs m1 A [CB 4 a; zb1; zb1; zb1; zb1; zb1; zb1; zb1; zb1; zb1; zb1; zb1; zb1; zb1; zb1; CB 14 b] ->
  rw_cells bsegs m1 A [CB 4 a; C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); CB 14 b].
Proof.
  intros m1 A a b H. pose proof H as [[WF _] _]. cbn [cells_wf cell_wf zb1] in WF.
  eapply rw_cells_recell; [exact H | | ].
  - cbn [cells_wf cell_wf]. tauto.
  - cbn [cells_bytes cbytes zb1 app]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sqd_iinv_anchor : forall P OEND LLO LEND LOCV (m1 : amem) fr ff,
  sqd_static P OEND LLO LEND LOCV -> sqd_mem P -> sqd_tables P -> LOCV = w_LOC P -> w_LOC P <> 2 ->
  (w_LLT P + 4104 <= 2147446784 \/ 17594333495296 <= w_LLT P) -> (w_OFT P + 2056 <= 2147446784 \/ 17594333495296 <= w_OFT P) ->
  (w_MLT P + 4104 <= 2147446784 \/ 17594333495296 <= w_MLT P) ->
  munch [(w_FRB P, w_FRB P + 216); (w_FF P, w_FF P + 256); (w_SHF P, w_SHF P + 32); (w_DCTX P + 30004, w_DCTX P + 30004 + 4)] (w_m P) m1 ->
  wmono bsegs (w_m P) m1 -> mem_inv bsegs m1 ->
  rw_cells bsegs m1 (w_FRB P) fr -> rw_cells bsegs m1 (w_FF P) ff ->
  rw_cells bsegs m1 (w_SHF P) [CB 4 (w_jsh0 P); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); CB 14 (w_jsh1 P)] ->
  dctx_h3 bsegs m1 (w_DCTX P) (w_pcs P) (w_dsz P) (w_bt P) (w_stg P) (w_le P) (sqd_fe P) ->
  stk bsegs (w_m P) (w_lo P) (w_FRB P) -> stk bsegs (w_m P) (w_FRB P + 216) (w_SPV P + -104) ->
  rw_cells bsegs (w_m P) (w_SPV P + -104) (sqd_saved P) ->
  sqd_iinv P OEND LLO LEND LOCV m1 fr ff.
Proof.
  intros P OEND LLO LEND LOCV m1 fr ff ST MEM TBL ELOC NL2 TB1 TB2 TB3 MU WM MI1 FR FRF SHS HH3 STK GAP SAV.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  unfold sqd_iinv. cbn [sqd_mem sqd_tables sqd_xinv sqd_Wb sqd_saved sqd_fe w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in *.
  subst LOCV.
  destruct MEM as ((PT & REP & HH1 & _ & HH5) & (L1 & L2 & L3 & L4) & SQB & BUF & LRD & MI).
  destruct TBL as ((TLL & _) & (TOF & _) & (TML & _) & _).
  pose proof (h5_view2 m DCTX ws HH5) as (H5V & H5L). rewrite L4 in H5V.
  sd_static_open ST. unfold held in *.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  unfold dctx_ptrs, dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, h5_vcells in *.
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { cbn [sqd_asan] in S62. destruct S62 as (ARD & _). destruct (ARD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (BD & _). pose proof (ablk_lits _ _ BD) as BL. unfold DCTX_SIZEOF in BL. exact BL. }
  assert (BLT : LITP + LITSZ + 32 <= 2147446784 \/ 17594333495296 <= LITP).
  { cbn [sqd_asan] in S62. destruct S62 as (_ & _ & _ & _ & _ & _ & ALT & _). destruct (ALT ltac:(unfold WILDCOPY_OVERLENGTH; clear - S10 S67; lia)) as (BL0 & _).
    pose proof (ablk_lits _ _ BL0) as BL. unfold WILDCOPY_OVERLENGTH in BL. clear - BL. lia. }
  assert (DL : forall X n, 0 <= n -> (X + n <= lo \/ SPV <= X) -> (X + n <= DCTX + 26684 \/ DCTX + 95992 <= X) -> (FF + 256 <= X \/ X + n <= FF) ->
            (X + n <= 2147446784 \/ 17594333495296 <= X) ->
            disjoint_from [(FRB, FRB + 216); (FF, FF + 256); (SHF, SHF + 32); (DCTX + 30004, DCTX + 30004 + 4)] X n).
  { intros X n Hn D1 D2 D3 D4. cbn [disjoint_from]. split; [clear - Hn D1 S18 S47; lia|]. split; [clear - Hn D3; lia|].
    split; [clear - Hn D4 S52 S53; lia|]. split; [clear - Hn D2; lia| exact I]. }
  (* [comment removed for export] *)
  assert (DD : forall off n, 0 <= off -> 0 <= n -> off + n <= 95992 -> (off + n <= 30004 \/ 30008 <= off) ->
            disjoint_from [(FRB, FRB + 216); (FF, FF + 256); (SHF, SHF + 32); (DCTX + 30004, DCTX + 30004 + 4)] (DCTX + off) n).
  { intros off n H0 Hn H1 H2. cbn [disjoint_from]. split; [clear - H0 Hn H1 S27 S18 S47; lia|]. split; [clear - H0 Hn H1 S54; lia|].
    split; [clear - H0 Hn H1 BDL S52 S53; pose proof atop_range as ATR; lia|]. split; [clear - H0 Hn H1 H2; lia| exact I]. }
  split; [exact FR|]. split; [exact FRF|].
  split; [eapply rw_cells_transport; [exact PT | exact MU | exact WM | pose proof (DD 0 32) as DD0; rewrite Z.add_0_r in DD0; cbn [cells_size csize Nat.add]; apply DD0; clear; lia]|].
  split; [eapply bytes_at_transport; [exact TLL | exact MU | apply DL; [clear; lia | clear - S28 LLL; lia | clear - S37 LLL; lia | clear - S58 LLL; lia | clear - TB1 LLL; lia]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MU | apply DL; [clear; lia | clear - S29 LOF; lia | clear - S38 LOF; lia | clear - S59 LOF; lia | clear - TB2 LOF; lia]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MU | apply DL; [clear; lia | clear - S30 LML; lia | clear - S39 LML; lia | clear - S60 LML; lia | clear - TB3 LML; lia]]|].
  split.
  { destruct sq as [|b sq'].
    - cbn [map]. unfold bytes_at in SQB |- *. destruct SQB as (SQW & _).
      split; [exact SQW|]. split; [cbn [zlen length]; clear - S14; lia|]. intros i Hi. cbn [length] in Hi. exfalso. clear - Hi. lia.
    - cbn [sqd_asan] in S62. destruct S62 as (_ & _ & ASQ & _). destruct (ASQ ltac:(cbn [zlen length]; clear; lia)) as (BSQ & _).
      pose proof (ablk_lits _ _ BSQ) as BL.
      eapply bytes_at_transport; [exact SQB | exact MU | rewrite length_map; apply DL; [clear; lia | clear - S25; unfold zlen in *; lia | clear - S40; unfold zlen in *; lia | clear - S56; unfold zlen in *; lia | clear - BL; unfold zlen in *; lia]]. }
  split.
  { destruct S67 as (-> & ->). eapply rdbl_transport; [exact LRD | exact MU |]. intros x Hx; left. unfold WILDCOPY_OVERLENGTH in Hx. cbn [outside].
    split; [clear - Hx S10 S26 S18 S47; lia|]. split; [clear - Hx S10 S57; lia|]. split; [clear - Hx S10 BLT S52 S53; lia|]. split; [clear - Hx S10 S36; lia | exact I]. }
  split; [intros EL2; exfalso; exact (NL2 EL2)|].
  split.
  { unfold h5_viewed. split; [| exact H5L]. eapply rw_cells_transport; [exact H5V | exact MU | exact WM |].
    cbn [h5_vcells cells_size csize Nat.add]. apply DD; clear; lia. }
  split; [exists r0, r1, r2; eapply rw_cells_transport; [exact REP | exact MU | exact WM | cbn [cells_size csize Nat.add]; apply DD; clear; lia]|].
  split; [exact HH3|].
  split; [eapply stk_transport_disjoint; [exact BUF | exact MU | exact WM | apply DL; [clear - S68; lia | clear - S24; lia | clear - S32; lia | clear - S55; lia | clear - S69; lia]]|].
  split; [eapply stk_transport_disjoint; [exact STK | exact MU | exact WM | cbn [disjoint_from]; split; [clear - S18 S47; lia| split; [clear - S50 S18 S47; lia| split; [clear - S53 S18; lia | split; [clear - S27 S18 S47; lia | exact I]]]]]|].
  split; [eapply rw_cells_transport; [exact SAV | exact MU | exact WM | cbn [cells_size csize Nat.add disjoint_from]; split; [clear - S47; lia| split; [clear - S50 S18 S47; lia| split; [clear - S53 S18 S47; lia | split; [clear - S27 S18 S47; lia | exact I]]]]]|].
  split; [eapply stk_transport_disjoint; [exact GAP | exact MU | exact WM | cbn [disjoint_from]; split; [clear; lia| split; [clear - S50 S18 S47; lia| split; [clear - S53 S18 S47; lia | split; [clear - S27 S18 S47; lia | exact I]]]]]|].
  split; [exact SHS|].
  split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx S47; lia|].
  split; [exact WM | exact MI1].
Qed.

End CANSEC1.
