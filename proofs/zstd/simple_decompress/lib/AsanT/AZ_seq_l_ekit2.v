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
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_ibase AZ_seq_l_iat.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sql_at_anchor (P : slq) : Prop :=
  forall (ja jb jc jd je jds jp jm : list byte) (x1 x5 x6 x7 x12 x13 x14 x17 x26 x28 x29 x30 : word),
  rw_cells bsegs (l_m P) (l_FRB P) [CB 8 (l_j0 P); CB 224 ja; C8 (Z_to_bv 64 (l_DST P)); CB 8 jb; C8 (Z_to_bv 64 (l_FF P)); CB 8 jc; C8 (Z_to_bv 64 (2147450880 + l_D8 P + 3796)); CB 48 jd; CB 24 (l_j384 P); CB 224 je] ->
  rw_cells bsegs (l_m P) (l_FF P) [CB 32 (l_jfh P); CB 88 jds; CB 24 jp; CB 104 (l_j144 P); C8 (Z_to_bv 64 (l_fflag P (l_L P) 2 (l_FF P)))] ->
  rw_cells bsegs (l_m P) (l_SHF P) [CB 4 (l_jsh0 P); CB 14 jm; CB 14 (l_jsh1 P)] ->
  stk bsegs (l_m P) (l_lo P) (l_FRB P) -> stk bsegs (l_m P) (l_FRB P + 568) (l_SPV P + -104) ->
  rw_cells bsegs (l_m P) (l_SPV P + -104) (sql_saved P) ->
  evtF bsegs (l_RNG P) (sql_post P)
    (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P))
             (Z_to_bv 64 (l_DCTX P + 29896)) (Z_to_bv 64 0) x12 x13 x14 (Z_to_bv 64 (-15)) (Z_to_bv 64 (-13)) x17 (Z_to_bv 64 2147450880)
             (Z_to_bv 64 (l_SEQ P)) (Z_to_bv 64 (l_CAP P)) (Z_to_bv 64 28672) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 (l_DCTX P)) (Z_to_bv 64 (l_nbSeq P)) (Z_to_bv 64 (l_FF P))
             x26 (Z_to_bv 64 (zlen (l_sq P))) x28 x29 x30 (Z_to_bv 64 (l_DCTX P + 30368)))
        (l_F P) (Z_to_bv 64 0x89ae0) (l_fc P) None (l_m P) (seg_rom bsegs)).

(* [comment removed for export] *)
Lemma sql_art_trW : forall (m m' : amem) W, art m -> munch W m m' -> wmono bsegs m m' ->
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
Lemma sql_sh14 : forall (m1 : amem) A a b,
  rw_cells bsegs m1 A [CB 4 a; zb1; zb1; zb1; zb1; zb1; zb1; zb1; zb1; zb1; zb1; zb1; zb1; zb1; zb1; CB 14 b] ->
  rw_cells bsegs m1 A [CB 4 a; C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); CB 14 b].
Proof.
  intros m1 A a b H. pose proof H as [[WF _] _]. cbn [cells_wf cell_wf zb1] in WF.
  eapply rw_cells_recell; [exact H | | ].
  - cbn [cells_wf cell_wf]. tauto.
  - cbn [cells_bytes cbytes zb1 app]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sql_iinv_anchor : forall P OEND (m1 : amem) fr ff,
  sql_static P OEND (l_LITP P) (l_LBE P) (l_LOC P) -> sql_mem P -> sql_tables P ->
  (l_LLT P + 4104 <= 2147446784 \/ 17594333495296 <= l_LLT P) -> (l_OFT P + 2056 <= 2147446784 \/ 17594333495296 <= l_OFT P) ->
  (l_MLT P + 4104 <= 2147446784 \/ 17594333495296 <= l_MLT P) ->
  munch [(l_FRB P, l_FRB P + 568); (l_FF P, l_FF P + 256); (l_SHF P, l_SHF P + 32); (l_DCTX P + 30004, l_DCTX P + 30004 + 4)] (l_m P) m1 ->
  wmono bsegs (l_m P) m1 -> mem_inv bsegs m1 ->
  rw_cells bsegs m1 (l_FRB P) fr -> rw_cells bsegs m1 (l_FF P) ff ->
  rw_cells bsegs m1 (l_SHF P) [CB 4 (l_jsh0 P); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); CB 14 (l_jsh1 P)] ->
  dctx_h3 bsegs m1 (l_DCTX P) (l_pcs P) (l_dsz P) (l_bt P) (l_stg P) (l_le P) (sql_fe P) ->
  stk bsegs (l_m P) (l_lo P) (l_FRB P) -> stk bsegs (l_m P) (l_FRB P + 568) (l_SPV P + -104) ->
  rw_cells bsegs (l_m P) (l_SPV P + -104) (sql_saved P) ->
  sql_iinv P OEND (l_LITP P) (l_LBE P) (l_LOC P) m1 fr ff.
Proof.
  intros P OEND m1 fr ff ST MEM TBL TB1 TB2 TB3 MU WM MI1 FR FRF SHS HH3 STK GAP SAV.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  unfold sql_iinv. cbn [sql_mem sql_tables sql_xinv sql_Wb sql_saved sql_fe l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in *.
  destruct MEM as ((PT & REP & HH1 & _ & HH5) & (L1 & L2 & L3 & L4) & SQB & BUF & LRD & XRD & MI).
  destruct TBL as ((TLL & _) & (TOF & _) & (TML & _) & _).
  pose proof (h5_view2 m DCTX ws HH5) as (H5V & H5L). rewrite L4 in H5V.
  sd_static_open ST. unfold held in *.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  unfold dctx_ptrs, dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, h5_vcells in *.
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { cbn [sql_asan] in S62. destruct S62 as (ARD & _). destruct (ARD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (BD & _). pose proof (ablk_lits _ _ BD) as BL. unfold DCTX_SIZEOF in BL. exact BL. }
  assert (BLT : LBE + 32 <= 2147446784 \/ 17594333495296 <= LITP).
  { cbn [sql_asan] in S62. destruct S62 as (_ & _ & _ & _ & _ & _ & ALT & _). destruct (ALT ltac:(unfold WILDCOPY_OVERLENGTH; clear - S70; lia)) as (BL0 & _).
    pose proof (ablk_lits _ _ BL0) as BL. unfold WILDCOPY_OVERLENGTH in BL. clear - BL. lia. }
  assert (DL : forall X n, 0 <= n -> (X + n <= lo \/ SPV <= X) -> (X + n <= DCTX + 26684 \/ DCTX + 95992 <= X) -> (FF + 256 <= X \/ X + n <= FF) ->
            (X + n <= 2147446784 \/ 17594333495296 <= X) ->
            disjoint_from [(FRB, FRB + 568); (FF, FF + 256); (SHF, SHF + 32); (DCTX + 30004, DCTX + 30004 + 4)] X n).
  { intros X n Hn D1 D2 D3 D4. cbn [disjoint_from]. split; [clear - Hn D1 S18 S47; lia|]. split; [clear - Hn D3; lia|].
    split; [clear - Hn D4 S52 S53; lia|]. split; [clear - Hn D2; lia| exact I]. }
  (* [comment removed for export] *)
  assert (DD : forall off n, 0 <= off -> 0 <= n -> off + n <= 95992 -> (off + n <= 30004 \/ 30008 <= off) ->
            disjoint_from [(FRB, FRB + 568); (FF, FF + 256); (SHF, SHF + 32); (DCTX + 30004, DCTX + 30004 + 4)] (DCTX + off) n).
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
    - cbn [sql_asan] in S62. destruct S62 as (_ & _ & ASQ & _). destruct (ASQ ltac:(cbn [zlen length]; clear; lia)) as (BSQ & _).
      pose proof (ablk_lits _ _ BSQ) as BL.
      eapply bytes_at_transport; [exact SQB | exact MU | rewrite length_map; apply DL; [clear; lia | clear - S25; unfold zlen in *; lia | clear - S40; unfold zlen in *; lia | clear - S56; unfold zlen in *; lia | clear - BL; unfold zlen in *; lia]]. }
  split.
  { eapply rdbl_transport; [exact LRD | exact MU |]. intros x Hx; left. unfold WILDCOPY_OVERLENGTH in Hx. cbn [outside].
    split; [clear - Hx S10 S26 S18 S47; lia|]. split; [clear - Hx S10 S57; lia|]. split; [clear - Hx S10 BLT S52 S53; lia|]. split; [clear - Hx S10 S36; lia | exact I]. }
  split.
  { intros NL2. unfold ZSTD_split, DCTX_litExtraBuffer, DCTX_litExtraBuffer_sz in XRD. replace (DCTX + 95940) with (DCTX + 30372 + 65568) by (clear; lia). eapply rdbl_transport; [exact (XRD NL2) | exact MU |]. intros x Hx; left.
    apply (disjoint_outside _ x 1 x); [| clear; lia]. replace x with (DCTX + (x - DCTX)) at 1 by (clear; lia). apply DD; clear - Hx; lia. }
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
