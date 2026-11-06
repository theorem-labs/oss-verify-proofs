(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From Stdlib Require Permutation FunctionalExtensionality.
From stdpp Require list.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9.

(* [comment removed for export] *)
Module CRebuildRM.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "@Corelib.Init.Datatypes"; "bool"; "list"; "prod"; "fst"; "pair"; "app"; "false"; "snd"; "true"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.CRebuildRM"; "sub1"; "sub2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "AA"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_depot"; "aa_ptr_committed"; "aa_sec"; "ageom"; "depot_state"; "sec_chunk"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "alloc_top"; "m_vm_lazy"; "vm_limit"; "vm_maps"; "vm_noaccess"; "vm_reserved"; "maps_subtract"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "ivs_wf"; "covered"; "model_ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kSpaceSize"; "HIGH_SHADOW_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "model_inv"; "band_page"; "inv3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "budget_boundD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "prim_credit"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra LedgerA Virt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.CInvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.InvReveal.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition sub1 (b : bool) (lo hi : Z) (l : list (word * word)) : list (word * word) := ltac2:(tb__ "0|1|
S8S9SaS12Q40A1M0G0A2A1Lb;Vb;S2aVl;Vlo;Vhi;A3Vl;X8x2").
Definition sub2 (b1 : bool) (lo1 hi1 : Z) (b2 : bool) (lo2 hi2 : Z) (l : list (word * word)) : list (word * word) := ltac2:(tb__ "0|0|
S13Vb2;Vlo2;Vhi2;S13Vb1;Vlo1;Vhi1;Vl;A4A4").

Lemma sub1_wf : ltac2:(tb__ "0|1|
S8S0S0S9SaS12Q40A1M0G0A2A1S2bR1A1S1R4R3A2S2bS13R6R5R4R3A4A1F_;F_;Fl;Fhi;Flo;Fb;").
Proof. intros [|] lo hi l Hwf Hlh; cbn [sub1]; [apply maps_subtract_wf; assumption | exact Hwf]. Qed.
Lemma sub1_cov_false : ltac2:(tb__ "0|1|
S8S0S0S9SaS12Q40A1M0G0A2A1S0S2bR2A1S1R5R4A2S4S8S2cR4R3A2SeA3S4S8S2cS13R8R7R6R5A4R4A2SeA3F_;F_;F_;Fx;Fl;Fhi;Flo;Fb;").
Proof. intros [|] lo hi l x Hwf Hlh H; cbn [sub1]; [apply covered_subtract_false; assumption | exact H]. Qed.
Lemma sub1_cov_true : ltac2:(tb__ "0|1|
S8S0S0S9SaS12Q40A1M0G0A2A1S0S2bR2A1S1R5R4A2S4S8S2cS13R7R6R5R4A4R3A2S10A3S4S8S2cR5R4A2S10A3F_;F_;F_;Fx;Fl;Fhi;Flo;Fb;").
Proof. intros [|] lo hi l x Hwf Hlh H; cbn [sub1] in H; [exact (covered_subtract_true l lo hi x Hwf Hlh H) | exact H]. Qed.
Lemma sub1_keeps : ltac2:(tb__ "0|4|
S8S0S0S9SaS12Q40M0A1M1G1A2M2A1G2S0S0S2bR4A1S1R7R6A2S21G2R5R6A3S1S11G0SbG1G1R6A3A2R5A2S1R5S2S11G0SbG1G1R7A3A2S11G0SfG1G1R7A3A2A2A2S3R7R6A2S6S1R7RcA2S1RbR8A2A2S7G2G2S5S21G2R1S13RfReRdRcA4A3S5S1S11G0SbG1G1R1A3A2M3RaA2S1R9S2G3S11G0SfG1G1R1A3A2A2A2A2A2Lr';A2F_;F_;F_;F_;F_;F_;F_;Fq;Fp;Fr;Fl;Fhi;Flo;Fb;").
Proof.
  intros [|] lo hi l r p q Hwf Hlh Hin H1 H2 H3 H4; cbn [sub1]; [exact (maps_subtract_keeps l lo hi r p q Hwf Hlh Hin H1 H2 H3 H4)|].
  exists r. split; [exact Hin | split; assumption].
Qed.
Lemma sub1_in_apart : ltac2:(tb__ "0|4|
S8S0S0S9SaS12Q40M0A1M1G1A2M2A1G1G1S3R5R4A2S3Z0S11G0R2A2A2S6S1S2S11G0R4A2M3S11G0R3A2A2R7A2S1R6G3A2A2S21G2ScG1G1R5R4A4R6A3S21G2ScG1G1R6R5A4S13RaR9R8R7A4A3F_;F_;F_;F_;Fsz;Fa;Fl;Fhi;Flo;Fb;").
Proof. intros [|] lo hi l a sz Hlh Hs Hd Hin; cbn [sub1]; [apply in_maps_subtract_apart; assumption | exact Hin]. Qed.
Lemma sub1_pos : ltac2:(tb__ "0|5|
S8S0S0S9SaS12Q40M0A1M1G1A2M2A1G1G1S21G2ScG1G1R2R1A4M3R3A3S3Z0S11G0R2A2A2M4F_;Fs;Fb';G1G1S21G2G3S13R7R6R5R4A4A3G4F_;Fs;Fb';F_;Fl;Fhi;Flo;Fb;").
Proof. intros [|] lo hi l H; cbn [sub1]; [apply maps_subtract_pos; exact H | exact H]. Qed.

Section M.
Let segs : list Segment := segsA.

Lemma model_inv_sub2 : ltac2:(tb__ "0|9|
S17S17S9S12Q40M0A1M1A1M2G2S23S23S8S8S0S0S0S0S4S1eS15RbA1S15RcA1A3S4S9S20A1S1dRcA1S1dRdA1A3S4S1fS1bRdA1S1bReA1A3S4S0S1cReA1S1cRfA1A3S4S0S1aRfA1S1aR10A1A3S4S0S19R10A1S19R11A1A3S4S0S18R11A1S18R12A1A3S32R13A1S2dR10A1S3RdRcA2S3RcRbA2S1S16S15R17A1A1RfA2S1RfS2S2S16S15R18A1A1S2eA2Z1000M3A2A2S1S16S15R19A1A1RfA2S1RfS2S2S16S15R1aA1A1S2eA2G3A2A2S1S2fS16S15R1bA1A1A2S4S9SaG1G1A2A1M4S27S22R17A1A1S27S22R18A1M5A1A3S4G4S29G5A1S29S22R19A1M6A1A3S4S0S26G6A1S26S22R1aA1M7A1A3S4S0S24G7A1S24S22R1bA1M8A1A3S4G4S28G8A1S14R1aR18R17R19R16R15S28S22R1cA1A1A7A3S4G4S25R1cA1S14R1bR19R18R1aR17R16S25R1dA1A7A3G1S21G1R1R20A3S31S11G0R2A2A1F_;Fp;S1S2S33R1eSdG1R20R21A3A2S35R22A1A2S34R23A1A2S30Vsegs;R24R22R20A4S30Vsegs;R24SdG1R22R23A3R20A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fhi2;Flo2;Fhi1;Flo1;Fb2;Fb1;Fmd;Fmd0;Ftp1;Ftp0;FA';FA;").
Proof.
  intros A A' tp0 tp1 md0 md b1 b2 lo1 hi1 lo2 hi2 EG ES ED EP EV EKm EKf HI3 (Wm & Wn & Wl) LH1 LH2 SL1 SH1 SL2 SH2 SBH EM ER ELIM ETOP EN EL HBP HPAID HM.
  pose proof HI3 as (_ & _ & _ & _ & DEP3 & _).
  unfold model_inv in HM |- *. destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
  assert (Wn1 : ivs_wf (sub1 b1 lo1 hi1 (vm_noaccess (m_vmmaps md0)))) by (apply sub1_wf; [exact Wn | lia]).
  assert (Wl1 : ivs_wf (sub1 b1 lo1 hi1 (m_vm_lazy md0))) by (apply sub1_wf; [exact Wl | lia]).
  assert (COVF : forall x, covered (vm_noaccess (m_vmmaps md0)) x = false -> covered (vm_noaccess (m_vmmaps md)) x = false).
  { intros x H. rewrite EN. unfold sub2. apply sub1_cov_false; [exact Wn1 | lia|]. apply sub1_cov_false; [exact Wn | lia | exact H]. }
  assert (COVT : forall x, covered (vm_noaccess (m_vmmaps md)) x = true -> covered (vm_noaccess (m_vmmaps md0)) x = true).
  { intros x H. rewrite EN in H. unfold sub2 in H. apply (sub1_cov_true b1 lo1 hi1 _ x Wn ltac:(lia)). exact (sub1_cov_true b2 lo2 hi2 _ x Wn1 ltac:(lia) H). }
  rewrite kSpaceSize_val in SH1, SH2. unfold HIGH_SHADOW_END in SBH.
  split.
  { unfold vm_geom, in_maps in V1 |- *. rewrite EG, ES, EM.
    destruct V1 as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
    split.
    { intros e x He Hx.
      assert (CV : covered (vm_noaccess (m_vmmaps md)) x = true).
      { unfold covered. apply existsb_exists. exists e. split; [exact He|]. unfold in_iv, in_rng, ivB, ivS. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      apply COVT in CV. unfold covered in CV. apply existsb_exists in CV as (e0 & He0 & Hx0). unfold in_iv, in_rng, ivB, ivS in Hx0. apply andb_prop in Hx0 as [X1 X2].
      apply Z.leb_le in X1. apply Z.ltb_lt in X2. exact (N1 e0 x He0 (conj X1 X2)). }
    split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|]. split; [exact N7|]. split; [exact N8|].
    intros p Hal Hband. destruct (N9 p Hal Hband) as [L1 L2]. split.
    - apply page_in_ranges_spec in L1 as (r & Hr & Hpr). apply page_in_range_spec in Hpr as [Q1 Q2]. change page_size with 4096 in Q2.
      assert (OUT1 : bv_unsigned p + 4096 <= lo1 \/ hi1 <= bv_unsigned p).
      { clear -Hband SL1 SBH. unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG in *. lia. }
      assert (OUT2 : bv_unsigned p + 4096 <= lo2 \/ hi2 <= bv_unsigned p).
      { clear -Hband SL2 SBH. unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG in *. lia. }
      destruct (sub1_keeps b1 lo1 hi1 (m_vm_lazy md0) r (bv_unsigned p) (bv_unsigned p + 4096) Wl ltac:(lia) Hr Q1 Q2 ltac:(clear; lia) OUT1) as (r1 & Hr1 & X1 & X2).
      destruct (sub1_keeps b2 lo2 hi2 _ r1 (bv_unsigned p) (bv_unsigned p + 4096) Wl1 ltac:(lia) Hr1 X1 X2 ltac:(clear; lia) OUT2) as (r2 & Hr2 & Y1 & Y2).
      rewrite EL. unfold sub2. apply page_in_ranges_spec. exists r2. split; [exact Hr2|]. apply page_in_range_spec. change page_size with 4096. clear -Y1 Y2. lia.
    - intros j Hj. apply COVF. exact (L2 j Hj). }
  split; [unfold budget_boundD in HPAID |- *; rewrite EV, EKm, EKf, EP, ED; exact HPAID|].
  split; [rewrite ELIM; exact V3|]. split; [rewrite EV; exact V4|]. split; [rewrite EKm; exact V5|]. split; [rewrite EKf; exact V6|].
  split; [rewrite ETOP, EG; exact V7|].
  unfold ledger_inv in V8 |- *. cbn zeta in V8 |- *.
  destruct V8 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
  split; [rewrite ER; exact L1|]. split; [rewrite EM; exact L2|]. split; [rewrite ER, EM; exact L3|].
  split.
  { unfold gap_ok, gapN_ok, gapS_ok, blocks_left, ledger in L4 |- *. rewrite EV, ED, ER, EM. exact L4. }
  split.
  { rewrite ED. pose proof (depot_vm_grow_band A md0 tp0 tp1 HI3 L5 HBP) as L5'. destruct L5' as [D1 D2 D3 D4 D5 D6]. constructor.
    - intros bn Hbn. rewrite EM. exact (D1 bn Hbn).
    - intros b Hb. rewrite EL. unfold sub2.
      destruct (DEP3 (b, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists b; split; [reflexivity | exact Hb])) as (DY & _ & _ & _ & _ & SPb & _).
      unfold sepZ in SPb. cbn [fst snd] in SPb, DY. rewrite kSpaceSize_val in SPb.
      pose proof (dyn_in_big _ _ _ DY ltac:(unfold FBSZ; clear; lia)) as BB. destruct DY as (_ & _ & DT & _).
      pose proof (topG_range (aa_geom A)) as TR.
      assert (UB : bv_unsigned (Z_to_bv 64 b) = b) by (apply u64_lit; unfold FBSZ, IMG_HI in *; clear -BB DT TR; lia).
      assert (UF : bv_unsigned (Z_to_bv 64 FBSZ) = FBSZ) by (apply u64_lit; unfold FBSZ; clear; lia).
      apply sub1_in_apart; [exact LH2 | rewrite UF; unfold FBSZ; clear; lia | rewrite UB, UF; clear -SPb SL2 SH2; lia|].
      apply sub1_in_apart; [exact LH1 | rewrite UF; unfold FBSZ; clear; lia | rewrite UB, UF; clear -SPb SL1 SH1; lia|]. exact (D2 b Hb).
    - intros b j Hb Hj. apply COVF. exact (D3 b j Hb Hj).
    - exact D4.
    - intros bn Hbn. rewrite ETOP. exact (D5 bn Hbn).
    - rewrite ETOP. exact D6. }
  split; [rewrite ED, EKm, EKf; exact L6|]. split; [rewrite EP, EKm; exact L7|]. split; [unfold in_maps; rewrite ?EM; exact L8|]. split; [rewrite ES, EKm; exact L9|].
  rewrite EN. unfold sub2. apply sub1_pos. apply sub1_pos. exact L10.
Qed.
End M.
End CRebuildRM.

(* [comment removed for export] *)
Module InvQ3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "modulo"; "sub"; "div"; "mul"; "of_nat"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "and"; "or"; "eq"; "not"; "ex"; "False"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "maskv"; "bview"; "restrictv"; "rtc_inv"; "RTC_A"; "cell_ok"; "cells_footb"; "mkACell"; "present"; "rtc_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "rl"; "rw"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "ag_thread"; "sec_chunk"; "aa_live"; "AA"; "ag_ctx"; "ag_dtls"; "ag_fsb"; "topG"; "aa_sec"; "ageom"; "cs_allocated_user"; "sc_map_beg"; "sc_map_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "Sh"; "IMG_HI"; "IMG_LO"; "rz"; "PG"; "is_primary"; "ClassID"; "dyn_in"; "kQuarantineMin"; "kUserSpaceSize"; "needed"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "QG"; "fs_footb"; "secondary_repr"; "bandtp_inv"; "depot_wf"; "fs_inv"; "ia_inv"; "inv3"; "live_block_repr"; "thread_inv"; "misc_inv"; "present_but"; "live_ids"; "live_sep"; "primary_repr"; "slot_zone"; "@Corelib.Init.Datatypes"; "option"; "list"; "bool"; "None"; "prod"; "Some"; "nat"; "pair"; "true"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3.QWG"; "QT"; "qslot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "QW"; "cls_of"; "qzone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "czone"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "K0"; "AInvQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3.QWG.View"; "view_parts_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "q_ids"; "qall"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull SMGlue RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma mod8_of_slot : ltac2:(tb__ "0|3|
S9S9S0Z10M0R2A2SdS9S4R3G0A2Z0M1A3SdS9S4R3R4A2G1A3SbSdS9S4R4Z8M2A2G1A3SdS9S4R5G2A2G1A3A2F_;F_;F_;Fo;Fs;").
Proof.
  intros s o Hs Hs16 Ho.
  destruct (proj1 (Z.mod_divide s 16 ltac:(lia)) Hs16) as [k Hk]. destruct (proj1 (Z.mod_divide o s ltac:(lia)) Ho) as [j Hj].
  split; apply Z.mod_divide; try lia.
  - exists (j * k * 2). subst o. subst s. ring.
  - exists (k * 2). subst s. ring.
Qed.

Lemma cell_ok_some : ltac2:(tb__ "0|1|
S15S9S54S9S9S19R5S1bR4R3R2A3A2SbS0R5R2A2S2R2S1R5S8R4A1A2A2A2SeSdS4eS3dQ8A1M0A1R7R3A1S51G0A1A3A1F_;F_;Fz;Fv;Fw;Fa;Fm;").
Proof.
  intros m a w v z H Hz. specialize (H (Z.to_nat (z - a)) ltac:(cbn [c_w]; lia)). cbn [c_addr] in H.
  replace (a + Z.of_nat (Z.to_nat (z - a))) with z in H by lia. rewrite H. discriminate.
Qed.

Lemma czone_slots_disj : ltac2:(tb__ "0|5|
S9S9S9S9S9S9S0Z10007fff8000R6A2S0S1S1R7S3Z2M0Z25A2A2Z1000A2Z7fffff800000A2SdS9S4R8Z8A2Z0M1A3SbS0Z1M2R8A2S0R8Z1eM3A2A2SbS0G2R7A2S0R7G3A2A2S0G1R9A2S0G1R8A2SdS9S4RbS31RcA1A2G1A3SdS9S4RaS31RbA1A2G1A3S0S1RdS31ReA1A2S5S3G0Z20A2S3G0Z1dA2A2M4A2S0S1RcS31RdA1A2G4A2ScSeSdS9R10ReA3A1SeSdS9RfRdA3A1A2S5dR12R11R10S31R11A1RdA5S5dR13R10RfS31R10A1ReA5S10F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fz;Fo2;Fc2;Fo1;Fc1;FSB;").
Proof.
  intros SB c1 o1 c2 o2 z S1 S2 S8 C1 C2 O1 O2 M1 M2 E1 E2 NE Z1 Z2.
  pose proof (Size_facts c1 C1) as (SZ1 & SM1). pose proof (Size_facts c2 C2) as (SZ2 & SM2).
  destruct (mod8_of_slot _ _ (proj1 SZ1) SM1 M1) as [Mo1 Ms1]. destruct (mod8_of_slot _ _ (proj1 SZ2) SM2 M2) as [Mo2 Ms2].
  assert (SEP : c1 <> c2 \/ o1 + Size c1 <= o2 \/ o2 + Size c2 <= o1).
  { destruct (Z.eq_dec c1 c2) as [EC|NC]; [right | left; exact NC]. subst c2.
    destruct NE as [NE|NE]; [exfalso; apply NE; reflexivity|].
    exact (mod0_apart o1 o2 (Size c1) ltac:(lia) M1 M2 NE). }
  refine (czone_disj SB c1 c2 o1 o2 (Size c1) (Size c2) z S1 S2 S8 _ _ O1 E1 O2 E2 _ _ Mo1 Mo2 Ms1 Ms2 SEP Z1 Z2); lia.
Qed.

Section QWG.
Variable A : AA.
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis H3 : sep_geom3 (aa_geom A).
Hypothesis HQP : q_pure A.
Hypothesis HAU : ltac2:(tb__ "0|1|
S9SbS0Z1R1A2S0R1Z1eA2A2SbS0Z0S2eS5bVA;R2A2A1M0A2S0G0S3bA2A2F_;Fc;").
Local Abbreviation Gq := (aa_geom A).
Local Abbreviation SBq := (ag_spacebeg (aa_geom A)).
Local Abbreviation Tq := (ag_thread (aa_geom A)).

Lemma geoQ : ltac2:(tb__ "0|8|
SbS0Z1000M0S24S22VA;A1M1A1M2A2SbS0S1G2G0A2M3S2bG1A1M4A2SbS0Z10007fff8000M5S23G1A1M6A2SbS0S1S1G6S3Z2Z25A2A2G0A2M7G4A2SbSdS9S4G6Z8A2Z0A3SbScS0G3G6A2S0G7G2A2A2SbScS0G3Z7fff7000A2S0G5G2A2A2SbScS0G3Z10000A2S0Z643000G2A2A2SbS0Z7fff7f800000G4A2S0G4Z7fffff800000A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof (geom_numsS _ HG) as (F0 & F1 & F2 & T1 & T2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG).
  pose proof (geom_old _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S16 & S1 & S2 & _).
  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & _).
  destruct H3 as (ST & _). rewrite kSpaceSize_val in ST, S2. unfold HIGH_SHADOW_END in S1.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in TB, TI.
  assert (S8 : SBq mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (2 ^ 16)); [exists (2 ^ 13); reflexivity | apply Z.mod_divide; [lia | exact S16]]. }
  split; [exact T1|]. split; [exact T2|]. split; [exact S1|]. split; [exact S2|]. split; [exact S8|].
  split; [exact ST|]. split; [exact TB|]. split; [exact TI | exact TG].
Qed.

Definition QT (z : Z) : Prop := ltac2:(tb__ "0|1|
ScS5aVA;Vz;A2SbS0S1S24S22VA;A1A1M0Zd0A2Vz;A2S2Vz;S1G0Zad0A2A2A2A2").
Lemma QT_QW : ltac2:(tb__ "0|0|
S9S5aVA;R1A2S58R2A1F_;Fz;"). Proof. intros z H. left. exact H. Qed.

Lemma QW_num : ltac2:(tb__ "0|5|
S9S5aVA;R1A2ScSbS0S1S23S22VA;A1M0A1M1S3Z2M2Z20A2A2R2A2S2R2S1G1S3G2Z25A2A2M3A2A2ScSbSbS0S32G1A1R2A2S2R2S32G3A1A2A2SbS0Z7fff8000R2A2S2R2Z10007fff8000A2A2A2ScSbS0S1S24G0A1M4Z50A2R2A2S2R2S1G4Z70A2A2A2ScSbS0S1G4Zad0A2R2A2S2R2S1G4Zc60A2A2A2SbS0S1S3eZ98A2R2A2S2R2S1S3eZc0A2A2A2A2A2A2A2F_;Fz;").
Proof.
  intros z HQ. pose proof (QW_where A HG HQP HAU z HQ) as W. unfold qw_where in W.
  pose proof geoQ as (T1 & T2 & S1 & S2 & S8 & _ & _ & _ & TG).
  rewrite kSpaceSize_val, kUserSpaceSize_val in W.
  destruct W as [(c & Hc & W)|[W|[W|[W|W]]]].
  - left. clear -Hc W. nia.
  - right; left. split; [exact W|].
    pose proof (Sh_in_band SBq ltac:(clear -S1 S2 TG; lia)) as B1. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep.Sh_lt_HSE (SBq + 2 ^ 37) ltac:(clear -S1 S2 TG; lia)) as B2.
    unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. clear -W B1 B2. lia.
  - right; right; left. clear -W. lia.
  - do 4 right. exact W.
  - right; right; right; left. exact W.
Qed.

Lemma QW_T : ltac2:(tb__ "0|1|
S9ScSbS0S24S22VA;A1A1M0R1A2S2R1S1G0Z50A2A2A2ScSbS0S1G0Z70A2R1A2S2R1S1G0Zad0A2A2A2SbS0S1G0Zc60A2R1A2S2R1S1G0Z1000A2A2A2A2A2SeS5aVA;R2A2A1F_;Fz;").
Proof.
  intros z Hz HQ. pose proof (QW_num z HQ) as W. pose proof geoQ as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  unfold QG in *. destruct W as [W|[[_ W]|[W|[W|W]]]]; clear -Hz W ST TB TI; lia.
Qed.

Lemma QT_num : ltac2:(tb__ "0|5|
S9S58R1A1ScSbS0S1S23S22VA;A1M0A1M1S3Z2M2Z20A2A2R2A2S2R2S1G1S3G2Z25A2A2M3A2A2ScSbSbS0S32G1A1R2A2S2R2S32G3A1A2A2SbS0Z7fff8000R2A2S2R2Z10007fff8000A2A2A2ScSbS0S1S24G0A1M4Z50A2R2A2S2R2S1G4Z70A2A2A2ScSbS0S1G4Zd0A2R2A2S2R2S1G4Zc60A2A2A2SbS0S1S3eZ98A2R2A2S2R2S1S3eZc0A2A2A2A2A2A2A2F_;Fz;").
Proof.
  intros z [HQ|HP]; [|right; right; right; left; clear -HP; lia].
  destruct (QW_num z HQ) as [W|[W|[W|[W|W]]]]; [left; exact W | right; left; exact W | right; right; left; exact W | right; right; right; left; clear -W; lia | do 4 right; exact W].
Qed.

Lemma QT_out : ltac2:(tb__ "0|4|
S9S9S9SbS0R3R1A2S2R1R2A2A2ScS0R3S23S22VA;A1M0A1M1A2S0S1S1G1S3Z2Z25A2A2Z1000M2A2R4A2A2ScS0R4S24G0A1M3A2S0S1G3G2A2R5A2A2ScS0R5Z7fff7000A2S0Z10007fff8000R6A2A2ScS0R6S34A2S0S33R7A2A2SeS58R6A1A1F_;F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z Hz OS OT OB OI HQ. pose proof (QT_num z HQ) as W. unfold QG, IMG_LO, IMG_HI in *.
  destruct W as [W|[[_ W]|[W|[W|W]]]]; clear -Hz OS OT OB OI W; lia.
Qed.

Lemma QT_img : ltac2:(tb__ "0|0|
S9SbS0S34R1A2S2R1S33A2A2SeSbS0S1S3eZ98A2R2A2S2R2S1S3eZc0A2A2A2A1SeS58R3A1A1F_;F_;Fz;").
Proof.
  intros z Hz NQ HQ. pose proof (QT_num z HQ) as W. pose proof geoQ as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  unfold QG, IMG_LO, IMG_HI in *. destruct W as [W|[[_ W]|[W|[W|W]]]]; clear -Hz NQ W S1 TI; lia.
Qed.

Lemma QT_T : ltac2:(tb__ "0|1|
S9ScSbS0S24S22VA;A1A1M0R1A2S2R1S1G0Z50A2A2A2ScSbS0S1G0Z70A2R1A2S2R1S1G0Zd0A2A2A2SbS0S1G0Zc60A2R1A2S2R1S1G0Z1000A2A2A2A2A2SeS58R2A1A1F_;Fz;").
Proof.
  intros z Hz HQ. pose proof (QT_num z HQ) as W. pose proof geoQ as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  unfold QG in *. destruct W as [W|[[_ W]|[W|[W|W]]]]; clear -Hz W ST TB TI; lia.
Qed.

Lemma QT_fs : ltac2:(tb__ "0|0|
S9S58R1A1SdS50S3fS22VA;A1R2A2S57A3F_;Fz;").
Proof.
  intros z HQ. pose proof (QT_num z HQ) as W. pose proof geoQ as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  destruct W as [W|[[W _]|[W|[W|W]]]].
  - apply fs_footb_space; [exact HG|]. rewrite kSpaceSize_val. clear -W. lia.
  - apply fs_footb_space_sh; [exact HG|]. rewrite kSpaceSize_val. pose proof (Geometry.Sh_mono (SBq + 2 ^ 37) (SBq + 2 ^ 37 + 4096) ltac:(lia)). clear -W H. lia.
  - apply fs_footb_T; [exact HG|]. clear -W. lia.
  - apply fs_footb_T; [exact HG|]. clear -W. lia.
  - apply fs_footb_img; [exact HG|]. unfold QG in W. clear -W. lia.
Qed.

Lemma QT_sh_out : ltac2:(tb__ "0|1|
S9S9S9SbS0S32R3A1R1A2S2R1S32R2A1A2A2S0Z0R4A2S0R4Z7fffff800000A2ScS0R5S23S22VA;A1A1M0A2S0S1S1G0S3Z2Z25A2A2Z1000A2R6A2A2SeS58R5A1A1F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z Hz L0 HT OS HQ. pose proof (QT_num z HQ) as W. pose proof geoQ as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  assert (B1 : 2147450880 <= Sh lo) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos lo 8 L0 ltac:(lia)); lia).
  assert (B2 : Sh hi <= 17594332446720).
  { unfold Sh, SHADOW_OFF. pose proof (Z.div_le_mono hi 140737479966720 8 ltac:(lia) HT) as M. change (140737479966720 / 8) with 17592184995840 in M. lia. }
  unfold QG in *.
  destruct W as [W|[[W _]|[W|[W|W]]]]; try (clear -Hz B1 B2 W S1 TB; lia).
  destruct OS as [O|O].
  - pose proof (Geometry.Sh_mono hi SBq O). clear -Hz W H. lia.
  - pose proof (Geometry.Sh_mono (SBq + 2 ^ 37) lo ltac:(clear -O; lia)). clear -Hz W H. lia.
Qed.

Lemma czone_where : ltac2:(tb__ "0|5|
S9S9S9SbS0Z1R3A2S0R3Z1eA2A2S0Z0M0R3A2SdS9S4R4S31R5A1A2G0A3S0S1R5S31R6A1A2S5S3Z2M1Z20A2M2S3G1Z1dA2A2A2S5dS23S22VA;A1A1M3R7R6S31R7A1R5A5ScSbS0S1G3G2A2R6A2S2R6S1G3S3G1Z25A2A2M4A2A2SbSbS0S32G3A1R6A2S2R6S32G4A1A2A2SbS0Z7fff8000R6A2S2R6Z10007fff8000A2A2A2A2F_;F_;F_;F_;F_;Fz;Fo;Fc;").
Proof.
  intros c o z Hc O0 OM OE CZ. pose proof geoQ as (T1 & T2 & S1 & S2 & S8 & _ & _ & _ & TG).
  pose proof (Size_facts c Hc) as (SZ & SM). destruct (mod8_of_slot _ _ (proj1 SZ) SM OM) as [Mo Ms].
  unfold czone in CZ. cbn zeta in CZ. destruct CZ as [CZ|CZ]; [left; clear -CZ Hc O0 OE SZ; nia | right].
  assert (AB8 : (SBq + c * 2 ^ 32 + o) mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.divide_add_r|].
    - apply Z.mod_divide; [lia | exact S8].
    - exists (c * 2 ^ 29). lia.
    - apply Z.mod_divide; [lia | exact Mo]. }
  rewrite <- (Sh_SB (SBq + c * 2 ^ 32 + o) (Size c) AB8) in CZ.
  pose proof (Geometry.Sh_mono SBq (SBq + c * 2 ^ 32 + o) ltac:(clear -Hc O0; nia)) as M1.
  pose proof (Geometry.Sh_mono (SBq + c * 2 ^ 32 + o + Size c) (SBq + 2 ^ 37) ltac:(clear -Hc OE; nia)) as M2.
  pose proof (Sh_in_band SBq ltac:(clear -S1 S2 TG; lia)) as B1. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep.Sh_lt_HSE (SBq + 2 ^ 37) ltac:(clear -S1 S2 TG; lia)) as B2.
  unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. clear -CZ M1 M2 B1 B2. lia.
Qed.

Lemma czone_out : ltac2:(tb__ "0|3|
S9S9S9S9S9SbS0Z1R5A2S0R5Z1eA2A2S0Z0M0R5A2SdS9S4R6S31R7A1A2G0A3S0S1R7S31R8A1A2S5S3Z2M1Z20A2S3G1Z1dA2A2A2SbS0R7R5A2S2R5R6A2A2ScS0R7S23S22VA;A1A1M2A2S0S1S1G2S3G1Z25A2A2Z1000A2R8A2A2ScS0R8Z7fff7000A2S0Z10007fff8000R9A2A2S5dG2RcRbS31RcA1R8A5S10F_;F_;F_;F_;F_;F_;F_;F_;Fz;Fhi;Flo;Fo;Fc;").
Proof.
  intros c o lo hi z Hc O0 OM OE Hz OS OB CZ. pose proof (czone_where c o z Hc O0 OM OE CZ) as W.
  destruct W as [W|[_ W]]; clear -Hz OS OB W; lia.
Qed.
Lemma czone_sh_out : ltac2:(tb__ "0|3|
S9S9S9S9S9SbS0Z1R5A2S0R5Z1eA2A2S0Z0M0R5A2SdS9S4R6S31R7A1A2G0A3S0S1R7S31R8A1A2S5S3Z2M1Z20A2S3G1Z1dA2A2A2SbS0S32R7A1R5A2S2R5S32R6A1A2A2S0G0R8A2S0R8Z7fffff800000A2ScS0R9S23S22VA;A1A1M2A2S0S1S1G2S3G1Z25A2A2Z1000A2RaA2A2S5dG2RdRcS31RdA1R9A5S10F_;F_;F_;F_;F_;F_;F_;F_;F_;Fz;Fhi;Flo;Fo;Fc;").
Proof.
  intros c o lo hi z Hc O0 OM OE Hz L0 HT OS CZ. pose proof (czone_where c o z Hc O0 OM OE CZ) as W.
  pose proof geoQ as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  assert (B2 : Sh hi <= 17594332446720).
  { unfold Sh, SHADOW_OFF. pose proof (Z.div_le_mono hi 140737479966720 8 ltac:(lia) HT) as M. change (140737479966720 / 8) with 17592184995840 in M. lia. }
  destruct W as [W|[W _]]; [clear -Hz B2 W S1; lia|].
  destruct OS as [O|O].
  - pose proof (Geometry.Sh_mono hi SBq O). clear -Hz W H. lia.
  - pose proof (Geometry.Sh_mono (SBq + 2 ^ 37) lo ltac:(clear -O; lia)). clear -Hz W H. lia.
Qed.
Lemma slot_czone : ltac2:(tb__ "0|1|
S9S9S9S11S4dS22VA;A1M0R3R2R1A4S5dS23G0A1R3S7Z10R2A2S31R3A1R1A5A2Fz;Fx;Fc;").
Proof. intros c x z. unfold slot_zone, czone, region_beg, kRegionSize. cbn zeta. tauto. Qed.

Definition qslot (c o : Z) : Prop := ltac2:(tb__ "0|3|
SbSbS0Z1Vc;A2S0Vc;Z1eA2A2SbS0Z0M0Vo;A2SbSdS9S4Vo;S31Vc;A1M1A2G0A3SbS0S1Vo;G1A2S5S3Z2M2Z20A2S3G2Z1dA2A2A2S5eS9S6Vo;Z10A2S66S22VA;A1S67VA;A1Vc;A3A3A2A2A2A2").

Lemma qzone_czone : ltac2:(tb__ "0|0|
S9S5cVA;R1A2SfS9S9SfS9S9SbS59R2R1A2S5dS23S22VA;A1A1R2R1S31R2A1R4A5A2Lo;A2Lc;A2F_;Fz;").
Proof.
  intros z HZ. unfold qzone in HZ. apply Exists_exists in HZ as (b & Hb & HZ).
  pose proof geoQ as (T1 & T2 & S1 & S2 & S8 & _).
  destruct HZ as [HZ|HZ].
  - destruct (batch_slot A HQP HAU HG b Hb) as (y & E & Y0 & YM & Y1 & _).
    exists 24, (16 * y). split.
    + unfold qslot. change (Size 24) with 8192. rewrite kUserSpaceSize_val in Y1.
      split; [lia|]. split; [lia|]. split; [|split; [lia|]].
      * destruct (proj1 (Z.mod_divide y 512 ltac:(lia)) YM) as [k Hk]. subst y. replace (16 * (k * 512)) with (k * 8192) by lia. apply Z_mod_mult.
      * replace (16 * y / 16) with y by (rewrite Z.mul_comm, Z.div_mul; lia).
        replace y with (qb_id Gq b); [exact (q_ids_batch A b Hb)|].
        unfold qb_id, ptr_to_compact, kCompactPtrScale, region_beg, kRegionSize. rewrite E.
        replace (SBq + 24 * 2 ^ 32 + 16 * y - (SBq + 24 * 2 ^ 32)) with (y * 2 ^ 4) by lia. rewrite Z.shiftr_div_pow2, Z.div_mul by lia. reflexivity.
    + unfold czone. cbn zeta. left. change (Size 24) with 8192. unfold kQuarantineBatchSize in HZ. clear -HZ E. lia.
  - apply Exists_exists in HZ as (it & Hit & EP & HZ).
    assert (Hit' : In it (qitems (qall A))) by (unfold qitems; apply in_flat_map; exists b; exact (conj Hb Hit)).
    pose proof (item_slot A HQP HAU HG it Hit' EP) as IS. cbv zeta in IS.
    destruct IS as (C1 & R1 & M1 & U1 & A16 & Z1 & Z2 & RZ & RZ16 & EU & UN & N1 & HS & TOP).
    pose proof (item_zones A HQP HAU HG it Hit' EP) as IZ. cbv zeta in IZ. destruct IZ as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
    exists (it_cls it), (it_ab it - (SBq + it_cls it * 2 ^ 32)). split.
    + unfold qslot. rewrite kUserSpaceSize_val in U1. split; [exact C1|]. split; [lia|]. split; [exact M1|]. split; [lia|].
      replace ((it_ab it - (SBq + it_cls it * 2 ^ 32)) / 16) with (it_id Gq it); [exact (q_ids_item A it (it_cls it) Hit' EP eq_refl)|].
      unfold it_id, ptr_to_compact, kCompactPtrScale, region_beg, kRegionSize. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
    + unfold czone. cbn zeta. replace (SBq + it_cls it * 2 ^ 32 + (it_ab it - (SBq + it_cls it * 2 ^ 32))) with (it_ab it) by lia.
      destruct HZ as [HZ|HZ]; [left; clear -HZ UN N1; lia | right].
      assert (AB8 : it_ab it mod 8 = 0).
      { destruct (proj1 (Z.mod_divide (it_ab it) 16 ltac:(lia)) A16) as [k Hk]. apply Z.mod_divide; [lia|]. exists (k * 2). lia. }
      rewrite <- (Sh_SB (it_ab it) (Size (it_cls it)) AB8). clear -HZ I4 I5. lia.
Qed.

Section Live.
Variable mq : bview.
Hypothesis HLS : live_sep A.
Hypothesis HPR : primary_repr mq A.
Hypothesis HSR : secondary_repr mq A.
Hypothesis HI3 : inv3 A.

Lemma live_prim_czone : ltac2:(tb__ "0|a|
S9S9S5eS52S9S9A2S55S9S9R2R1A4S26VA;A1A3SdS50S37R2A1S56A3S38S3cR3A1A1S9S5S5R5S35R4A1A2S1S23S22VA;A1M0A1M1S7R1S3Z2M2Z20A2M3A2A2A2S9SbSbS0Z1M4R2A2S0R2Z1eA2A2SbS0Z0M5R1A2SbSdS9S4R1S31R2A1M6A2G5A3SbS0S1R1G6A2S5G3S3G2Z1dA2A2A2SbS5eS9S6R1Z10M7A2S4aG0VA;R2A3A3SbSbS0S1S35R5A1M8R5A2G6A2SbSbS0G7G8A2S0G8Z800A2A2S0G4R5A2A2A2S9ScSbS0S5R7S35R6A1A2R1A2S2R1S1R7R6A2A2A2SbS0S32R7A1M9R1A2S2R1S1G9S6S1R6Z7A2Z8A2A2A2A2A2S5dG1R4R3S31R4A1R2A5F_;Fz;A2A2A2A2A2A2To;Tc;F_;F_;Fn;Fb;").
Proof.
  intros b n Hin HP c o. destruct (HLS b n Hin) as (Hn1 & _).
  pose proof geoQ as (T1 & T2 & S1 & S2 & S8 & _).
  assert (Hn : 1 <= n <= 64512).
  { split; [exact Hn1|]. destruct (Z_le_dec 64513 n) as [L|L]; [|lia]. rewrite (not_primary_large n L) in HP. discriminate. }
  pose proof (slot_ok_all n Hn) as SO. unfold slot_ok in SO.
  apply andb_prop in SO as [SO S5]. apply andb_prop in SO as [SO S4]. apply andb_prop in SO as [SO SM]. apply andb_prop in SO as [_ SN].
  apply Z.leb_le in SN, S4, S5. apply Z.eqb_eq in SM. unfold slot in SN, SM. fold c in SN, SM, S4, S5.
  destruct HPR as (_ & _ & _ & P4).
  destruct (P4 c (conj S4 S5)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _).
  destruct (LV b n Hin HP eq_refl) as (L1 & L2 & L3). unfold region_beg, kRegionSize in L1, L2, L3. rewrite kUserSpaceSize_val in N3. unfold kUserMapSize in N3.
  fold o in L2, L3.
  pose proof (rz_bound n) as RZ.
  assert (RZ16 : rz n mod 16 = 0).
  { unfold rz. rewrite Z.shiftl_mul_pow2 by (unfold rz_log; repeat destruct (_ <=? _); lia). rewrite Z.mul_comm. apply Z_mod_mult. }
  assert (ND : rz n + n <= needed n).
  { unfold needed, kChunkHeader2Size. pose proof (Z.div_mod (Z.max n 16 + 8 - 1) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (Z.max n 16 + 8 - 1) 8 ltac:(lia)) as MB. unfold round_up. lia. }
  assert (SZ16 : 16 <= Size c) by (clear -RZ ND SN Hn; lia).
  destruct (mod8_of_slot _ _ SZ16 SM L2) as [Mo Ms].
  assert (O0 : 0 <= o) by (unfold o; clear -L1; lia).
  split; [exact (conj S4 S5)|]. split; [exact O0|]. split; [exact L2|]. split; [clear -L3 N2 N3; lia|].
  split.
  { pose proof (live_id_in Gq A b n c Hin HP eq_refl) as IDin. unfold region_beg, kRegionSize in IDin. exact IDin. }
  split; [clear -RZ ND SN Hn; lia|].
  intros z Hz. unfold czone. cbn zeta.
  assert (EAB : SBq + c * 2 ^ 32 + o = b - rz n) by (unfold o; lia). rewrite EAB.
  destruct Hz as [Hz|Hz]; [left; clear -Hz RZ ND SN Hn; lia | right].
  assert (AB8 : (b - rz n) mod 8 = 0).
  { rewrite <- EAB. apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.divide_add_r|].
    - apply Z.mod_divide; [lia | exact S8].
    - exists (c * 2 ^ 29). lia.
    - apply Z.mod_divide; [lia | exact Mo]. }
  assert (RZ8 : rz n mod 8 = 0).
  { destruct (proj1 (Z.mod_divide (rz n) 16 ltac:(lia)) RZ16) as [k Hk]. apply Z.mod_divide; [lia|]. exists (k * 2). lia. }
  destruct (shadow_zone_in_slot (b - rz n) (rz n) n (Size c) AB8 RZ8 Ms ltac:(lia) ltac:(lia) ltac:(clear -ND SN; lia)) as [X1 X2].
  replace (b - rz n + rz n) with b in X1, X2 by lia.
  rewrite <- (Sh_SB (b - rz n) (Size c) AB8). clear -Hz X1 X2. lia.
Qed.

Lemma live_sec_map : ltac2:(tb__ "0|4|
S9S9S5eS52S9S9A2S55S9S9R2R1A4S26VA;A1A3SdS50S37R2A1S57A3SfS54S54SfS25S25SbSdS4eS25A1S5fS25S2cVA;A1R2A3S53S25R1A2A3SbSdS9R6S1S1S2fR1A1M0S36A2Z800M1A2A3SbSdS9S35R5A1G1A3SbS0Z1R5A2SbS0S1S1R6R5A2G1A2S1G0S30R1A1M2A2A2SbSdS9S4G0S36A2Z0M3A3SbS0G3G2A2S39S2bS22VA;A1A1G0G2A3A2A2A2A2A2A2A2Lch;A2Li;A2F_;F_;Fn;Fb;").
Proof.
  intros b n Hin HP. destruct (HLS b n Hin) as (Hn1 & _).
  destruct HI3 as (_ & LIV3 & _). destruct (LIV3 b n Hin) as [E|(ch & Hch & Eb & Esz)]; [rewrite E in HP; discriminate|].
  destruct (In_nth_error _ _ Hch) as (i & Hi). exists i, ch. split; [exact Hi|]. split; [exact Eb|]. split; [exact (rz_sec n Hn1 HP)|]. split; [exact Hn1|].
  destruct HSR as (HS1 & _). destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & _).
  pose proof (round_up_ge8 n) as R8. unfold PG in *. split; [lia|]. split; [exact D6|]. split; [lia | exact D10].
Qed.

Lemma live_not_QT : ltac2:(tb__ "0|1|
S9S9S9S5eS52S9S9A2S55S9S9R3R2A4S26VA;A1A3ScSbS0S5R4S35R3A1A2R2A2S2R2S1R4R3A2A2A2SbS0S32R4A1M0R2A2S2R2S1G0S6S1R3Z7A2Z8A2A2A2A2A2SeS58R3A1A1F_;F_;Fz;Fn;Fb;").
Proof.
  intros b n z Hin Hz HQ. pose proof geoQ as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  destruct (is_primary n) eqn:HP.
  - pose proof (live_prim_czone b n Hin HP) as L. cbv zeta in L. destruct L as (C1 & O0 & OM & OE & IDin & _ & CZ). specialize (CZ z Hz).
    assert (HQ' : qzone A z \/ (Tq + 80 <= z < Tq + 3168 \/ QG + 152 <= z < QG + 192)).
    { destruct HQ as [[HQ|[HQ|HQ]]|HQ]; [left; exact HQ | right | right | right].
      - unfold qhdr_zone in HQ. clear -HQ. lia.
      - unfold qstat_zone in HQ. clear -HQ. lia.
      - clear -HQ. lia. }
    destruct HQ' as [HQ'|HQ'].
    + destruct (qzone_czone z HQ') as (c' & o' & (C1' & O0' & OM' & OE' & IDin') & CZ').
      apply (czone_slots_disj SBq (ClassID (needed n)) (b - rz n - (SBq + ClassID (needed n) * 2 ^ 32)) c' o' z S1 ltac:(clear -S2 TG; lia) S8 C1 C1' O0 O0' OM OM' OE OE'); [|exact CZ|exact CZ'].
      destruct (Z.eq_dec (ClassID (needed n)) c') as [EC|NC]; [right | left; exact NC]. subst c'. intros EO. rewrite <- EO in IDin'.
      destruct HPR as (_ & _ & _ & P4).
      destruct (P4 _ C1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDI & _).
      apply NoDup_app_r in NDI. apply NoDup_app_r in NDI. exact (NoDup_app_disj _ _ _ NDI IDin IDin').
    + pose proof (czone_where _ _ z C1 O0 OM OE CZ) as W.
      unfold QG in HQ'. clear -HQ' W S1 ST TB. lia.
  - destruct (live_sec_map b n Hin HP) as (i & ch & Hi & Eb & RZ & N1 & BN & MP & MS0 & DI).
    destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 i ch Hi) as (X1 & X2 & _). rewrite kSpaceSize_val in X1.
    destruct DI as (D1 & D2 & D3 & D4 & D5). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in D5. unfold PG in *.
    destruct Hz as [Hz|Hz].
    + revert HQ. apply (QT_out (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z); [clear -Hz Eb RZ BN N1; lia | clear -X1; lia | clear -X2; lia | exact D5 | exact D4].
    + revert HQ. apply (QT_sh_out (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z); [| clear -D1; lia | clear -D3 TG; lia | clear -X1; lia].
      assert (B8 : b mod 8 = 0).
      { destruct (proj1 (Z.mod_divide (sc_map_beg ch) 4096 ltac:(lia)) MP) as [k Hk]. apply Z.mod_divide; [lia|]. exists (k * 512 + 768). lia. }
      pose proof (Sh_SB b (8 * ((n + 7) / 8)) B8) as E8. rewrite (Z.mul_comm 8), Z.div_mul in E8 by lia.
      pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as MB.
      pose proof (Geometry.Sh_mono (sc_map_beg ch) b ltac:(clear -Eb; lia)) as M1.
      pose proof (Geometry.Sh_mono (b + (n + 7) / 8 * 8) (sc_map_beg ch + sc_map_size ch) ltac:(clear -BN DM MB; lia)) as M2.
      clear -Hz E8 M1 M2. lia.
Qed.
End Live.

Local Abbreviation Cq := (ag_ctx (aa_geom A)).
Local Abbreviation Dq := (ag_dtls (aa_geom A)).
Local Abbreviation Fq := (ag_fsb (aa_geom A)).
Lemma geoQ2 : ltac2:(tb__ "0|10|
SbSbS0Z643000M0S2aS22VA;A1M1A1M2A2SbScS0S1G2Zb09000A2M3S24G1A1M4A2S0S1G4Z1000M5A2M6G2A2A2SbScS0G3S23G1A1M7A2S0S1S1G7S3Z2Z25A2A2G5A2M8G2A2A2ScS0G3Z7fff7000M9A2S0Z10007fff8000MaG2A2A2A2A2A2SbSbScS0G6S28G1A1MbA2S0S1GbG5A2McG4A2A2SbScS0GcG7A2S0G8GbA2A2SbScS0GcG9A2S0GaGbA2A2ScS0GcZ10000MdA2S0G0GbA2A2A2A2A2SbScS0G6S29G1A1MeA2S0S1GeG5A2MfG4A2A2SbScS0GfG7A2S0G8GeA2A2SbScS0GfG9A2S0GaGeA2A2ScS0GfGdA2S0G0GeA2A2A2A2A2A2A2").
Proof.
  pose proof (geom_numsS _ HG) as (F0 & F1 & F2 & T1 & T2 & C1 & C2 & D1 & D2 & FT & FC & FD & TC & TD & CD & _ & _ & TG).
  pose proof (geom_old _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S16 & S1 & S2 & _ & _ & _ & FS & _).
  pose proof (geom_bands _ HG) as (FB & TB & CB & DB & TI & CI & DI).
  destruct H3 as (ST & SC & SD & _). rewrite kSpaceSize_val in ST, SC, SD.
  rewrite FS_total_val, kSpaceSize_val in FS.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in FB, TB, CB, DB, TI, CI, DI. rewrite FS_total_val in FB.
  split; [|split].
  - split; [exact F1|]. split; [exact FT|]. split; [exact FS | exact FB].
  - split; [exact TC|]. split; [exact SC|]. split; [exact CB | exact CI].
  - split; [exact TD|]. split; [exact SD|]. split; [exact DB | exact DI].
Qed.

Lemma rtc_foot_cases_q : ltac2:(tb__ "0|4|
S2dS9SdS50S1aS1dS18R2A2R1A2S56A3ScSbSbS0S34R2A2S2R2S33A2A2SeSbS0S1S3eZ98A2R2A2S2R2S1S3eZc0A2A2A2A1A2ScSbS0S24R3A1M0R2A2S2R2S1G0Z50A2A2A2ScSbS0S28R3A1M1R2A2S2R2S1G1Za0A2A2A2ScSbS0S29R3A1M2R2A2S2R2S1G2Z20A2A2A2SbS0S2aR3A1M3R2A2S2R2S1G3Z61A2A2A2A2A2A2A2F_;Fz;FG;").
Proof.
  intros G z Hz. unfold cells_footb in Hz. apply existsb_exists in Hz as (c & Hc & Hin).
  unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
  unfold rtc_cells in Hc. apply in_app_or in Hc as [Hc|Hc].
  - left. unfold rtc_cells_img in Hc. unfold IMG_LO, IMG_HI, QG.
    repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; lia|]). destruct Hc.
  - right. unfold rtc_cells_geom in Hc. unfold fs_log_cell, fs_needs_gc_cell in Hc.
    repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; lia|]). destruct Hc.
Qed.

Lemma rtc_not_QT : ltac2:(tb__ "0|0|
S9SdS50S1aS1dS18S22VA;A1A2R1A2S56A3SeS58R2A1A1F_;Fz;").
Proof.
  intros z Hz. pose proof geoQ2 as ((F1 & FT & FS & FB) & (TC & SC & CB & CI) & (TD & SD & DB & DI)).
  destruct (rtc_foot_cases_q Gq z Hz) as [[K NK]|[K|[K|[K|K]]]].
  - exact (QT_img z K NK).
  - apply QT_T. left. clear -K. lia.
  - apply (QT_out Cq (Cq + 4096) z); [clear -K; lia | exact SC | clear -TC; lia | exact CB | unfold IMG_LO, IMG_HI; exact CI].
  - apply (QT_out Dq (Dq + 4096) z); [clear -K; lia | exact SD | clear -TD; lia | exact DB | unfold IMG_LO, IMG_HI; exact DI].
  - apply (QT_out Fq (Fq + 11571200) z); [clear -K; lia | exact FS | exact FT | exact FB | unfold IMG_LO, IMG_HI; clear -F1; lia].
Qed.

Lemma ia_inv_agree_q : ltac2:(tb__ "0|0|
S15S15S27S9SbS0S34R1A2S2R1S33A2A2SeSbS0S1S3eZ98A2R2A2S2R2S1S3eZc0A2A2A2A1SdS4eS3dQ8A1A1R5R3A1R6R3A1A3F_;F_;Fz;S44R4R2A2S44R4R3A2F_;F_;FA0;Fm';Fm;").
Proof.
  intros m m' A0 AG H. unfold ia_inv in *. unfold IA_MAP1, IA_MAP1_SZ, IA_BEG, IA_END, IMG_LO, IMG_HI, QG in *.
  rewrite !AG by lia. destruct H as (H1 & H2 & H3' & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3'|].
  destruct (aa_internal_inited A0); destruct H4 as [H5 H6]; (split; [exact H5|]); intros z Hz; rewrite AG by lia; exact (H6 z Hz).
Qed.
Lemma misc_inv_agree_q : ltac2:(tb__ "0|1|
S15S15S9SbS0S34R1A2S2R1S33A2A2SeSbS0S1S3eZ98A2R2A2S2R2S1S3eZc0A2A2A2A1SdS4eS3dQ8A1A1R4R3A1R5R3A1A3F_;F_;Fz;S48R3A1M0G0F_;F_;Fm';Fm;").
Proof.
  intros m m' AG (H1 & H2 & H3'). split; [|split].
  - eapply cells_ok_frame; [|exact H1]. intros z Hz. unfold cells_footb in Hz.
    apply existsb_exists in Hz as (c & Hc & Hin). unfold in_cellb in Hin. apply andb_prop in Hin as [X Y].
    apply Z.leb_le in X. apply Z.ltb_lt in Y. unfold rtc_extra in Hc.
    destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn in X, Y; apply AG; unfold IMG_LO, IMG_HI, QG; lia.
  - intros z Hz. rewrite AG by (unfold IMG_LO, IMG_HI, QG; lia). exact (H2 z Hz).
  - intros z Hz. rewrite AG by (unfold ERRNO_A, IMG_LO, IMG_HI, QG in *; lia). exact (H3' z Hz).
Qed.

Section View.
Variables (rho0 rho1 : valuation).
Variable PZ : Z -> Prop.
Hypothesis HPZ : ltac2:(tb__ "0|1|
S9VPZ;R1A1SbS0S1S24S22VA;A1A1M0Zd0A2R2A2S2R2S1G0Zad0A2A2A2F_;Fz;").
Local Abbreviation v0 := (view segsA (rm rho0)).
Local Abbreviation v1 := (view segsA (rm rho1)).
Hypothesis HOUT : ltac2:(tb__ "0|0|
S9SeS5aVA;R1A2A1SeVPZ;R2A1A1SdS4eS3dQ8A1A1S13S12S1eVrho1;A1R3A3S13S12S1eVrho0;A1R3A3A3F_;F_;Fz;").
Hypothesis HIN : ltac2:(tb__ "0|3|
S9ScS5aVA;R1A2VPZ;R1A1A2SeSdS4eS3dQ8A1M0A1M1S13S12S1eVrho0;A1R2A3S51G0A1M2A3A1SeSdG1S13S12S1eVrho1;A1R3A3G2A3A1F_;F_;Fz;").
Local Abbreviation mm := (maskv (fs_footb (aa_geom A)) (view segsA (rm rho0))).
Local Abbreviation mm' := (maskv (fs_footb (aa_geom A)) (view segsA (rm rho1))).

Lemma CH_QT : ltac2:(tb__ "0|0|
S9ScS5aVA;R1A2VPZ;R1A1A2S58R2A1F_;Fz;").
Proof. intros z [H|H]; [left; exact H | right; exact (HPZ z H)]. Qed.
Lemma VOUT : ltac2:(tb__ "0|0|
S9SeS58R1A1A1SdS4eS3dQ8A1A1S13S12S1eVrho1;A1R2A3S13S12S1eVrho0;A1R2A3A3F_;Fz;").
Proof. intros z Hz. apply HOUT; intros H; apply Hz; apply CH_QT; [left | right]; exact H. Qed.
Lemma MOUT : ltac2:(tb__ "0|1|
S9SeS58R1A1A1SdS4eS3dQ8A1A1S14S3fS22VA;A1A1M0S13S12S1eVrho1;A1A2R2A3S14G0S13S12S1eVrho0;A1A2R2A3A3F_;Fz;").
Proof. intros z Hz. unfold maskv. rewrite (VOUT z Hz). reflexivity. Qed.
Lemma MOUT_QW : ltac2:(tb__ "0|1|
S9SeVPZ;R1A1A1Fz;S9SeS5aVA;R1A2A1SdS4eS3dQ8A1A1S14S3fS22VA;A1A1M0S13S12S1eVrho1;A1A2R2A3S14G0S13S12S1eVrho0;A1A2R2A3A3F_;Fz;F_;").
Proof. intros NP z Hz. unfold maskv. rewrite (HOUT z Hz (NP z)). reflexivity. Qed.
Lemma MIN : ltac2:(tb__ "0|4|
S9ScS5aVA;R1A2VPZ;R1A1A2SeSdS4eS3dQ8A1M0A1M1S14S3fS22VA;A1A1M2S13S12S1eVrho0;A1A2R2A3S51G0A1M3A3A1SeSdG1S14G2S13S12S1eVrho1;A1A2R3A3G3A3A1F_;F_;Fz;").
Proof. intros z Hz. unfold maskv. rewrite (QT_fs z (CH_QT z Hz)). exact (HIN z Hz). Qed.
Lemma VSOME : ltac2:(tb__ "0|3|
S9SfS3dQ8A1M0G0SdS4eG0A1M1S13S12S1eVrho0;A1R2A3S53G0R1A2M2A3Lb;A2SfG0G0SdG1S13S12S1eVrho1;A1R3A3G2A3Lb;A2F_;Fz;").
Proof.
  intros z [b Hb]. destruct (v1 z) as [b'|] eqn:E; [exists b'; reflexivity|]. exfalso.
  assert (NQ : ~ ~ (QW A z \/ PZ z)).
  { intros NQ. rewrite (HOUT z (fun H => NQ (or_introl H)) (fun H => NQ (or_intror H))), Hb in E. discriminate. }
  apply NQ. intros HQ. apply (HIN z HQ); [rewrite Hb; discriminate | exact E].
Qed.
Lemma MSOME : ltac2:(tb__ "0|4|
S9SfS3dQ8A1M0G0SdS4eG0A1M1S14S3fS22VA;A1A1M2S13S12S1eVrho0;A1A2R2A3S53G0R1A2M3A3Lb;A2SfG0G0SdG1S14G2S13S12S1eVrho1;A1A2R3A3G3A3Lb;A2F_;Fz;").
Proof.
  intros z [b Hb]. destruct (mm' z) as [b'|] eqn:E; [exists b'; reflexivity|]. exfalso.
  assert (NQ : ~ ~ (QW A z \/ PZ z)).
  { intros NQ. unfold maskv in Hb, E. rewrite (HOUT z (fun H => NQ (or_introl H)) (fun H => NQ (or_intror H))), Hb in E. discriminate. }
  apply NQ. intros HQ. apply (MIN z HQ); [rewrite Hb; discriminate | exact E].
Qed.
Lemma MPRES : ltac2:(tb__ "0|1|
S9S9S1cS14S3fS22VA;A1A1M0S13S12S1eVrho0;A1A2A2R2R1A3S1cS14G0S13S12S1eVrho1;A1A2A2R3R2A3F_;Fhi;Flo;").
Proof. intros lo hi H z Hz. exact (MSOME z (H z Hz)). Qed.
Lemma MPRESB : ltac2:(tb__ "0|1|
S9S9S4fS52S9S9A2A1S49S14S3fS22VA;A1A1M0S13S12S1eVrho0;A1A2A2R3R2R1A4S49S14G0S13S12S1eVrho1;A1A2A2R4R3R2A4F_;FL;Fhi;Flo;").
Proof. intros lo hi L H z Hz Hn. exact (MSOME z (H z Hz Hn)). Qed.

Lemma view_rtc : ltac2:(tb__ "0|1|
S17S13S12S1eVrho0;A1A2S22VA;A1M0A2S17S13S12S1eVrho1;A1A2G0A2F_;").
Proof. intros HR. unfold rtc_inv in *. eapply cells_ok_frame; [|exact HR]. intros z Hz. apply VOUT. exact (rtc_not_QT z Hz). Qed.

Lemma view_fs : ltac2:(tb__ "0|1|
S43S16S3fS22VA;A1A1M0S13S12S1eVrho0;A1A2A2VA;A2S43S16G0S13S12S1eVrho1;A1A2A2VA;A2F_;").
Proof.
  intros HF. rewrite (restrictv_ext (fs_footb Gq) v0 v1); [exact HF|].
  intros z Hz. apply VOUT. intros HQ. rewrite (QT_fs z HQ) in Hz. discriminate.
Qed.

Lemma view_live : ltac2:(tb__ "0|2|
S4bVA;A1S4cS14S3fS22VA;A1A1M0S13S12S1eVrho0;A1A2A2M1VA;A2S40G1VA;A2S45VA;A1S46G1VA;A2S46S14G0S13S12S1eVrho1;A1A2A2VA;A2F_;F_;F_;F_;F_;").
Proof.
  intros HLS HPR HSR HI3 HLB b n Hin. destruct (HLB b n Hin) as (L1 & L2 & L3 & L4 & L5 & L6).
  pose proof (rz_bound n) as RZ. destruct (HLS b n Hin) as (Hn1 & _).
  assert (NQ : forall z, (b - rz n <= z < b \/ Sh b <= z < Sh b + (n + 7) / 8) -> mm' z = mm z).
  { intros z Hz. apply MOUT. apply (live_not_QT mm HLS HPR HSR HI3 b n z Hin). destruct Hz as [Hz|Hz]; [left; clear -Hz Hn1; lia | right; exact Hz]. }
  pose proof (Z.div_mod n 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as MN.
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as DN7. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as MN7.
  split; [rewrite NQ by (left; clear -RZ; lia); exact L1|].
  split; [eapply cell_ok_agree; [|exact L2]; cbn [c_addr c_w]; intros k Hk; apply NQ; left; clear -RZ Hk; lia|].
  split; [eapply cell_ok_agree; [|exact L3]; cbn [c_addr c_w]; intros k Hk; apply NQ; left; clear -RZ Hk; lia|].
  split.
  { destruct L4 as [S1 S2]. split.
    - intros g Hg. rewrite NQ by (right; clear -Hg DN MN DN7 MN7; lia). exact (S1 g Hg).
    - intros Hne. rewrite NQ by (right; clear -Hne Hn1 DN MN DN7 MN7; lia). exact (S2 Hne). }
  split; [apply (alloc_magic_ok_agree mm mm' b n); [intros z Hz; apply NQ; left; exact Hz | clear -RZ; lia | exact L5]|].
  destruct L6 as (t & Ht & Hm). exists t. split; [rewrite NQ by (left; clear -RZ; lia); exact Ht | exact Hm].
Qed.

Lemma view_secondary : ltac2:(tb__ "0|1|
S45VA;A1S40S14S3fS22VA;A1A1M0S13S12S1eVrho0;A1A2A2VA;A2S40S14G0S13S12S1eVrho1;A1A2A2VA;A2F_;F_;").
Proof.
  intros HI3 HSR. pose proof geoQ as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  destruct HI3 as ((_ & _ & _ & PS & PT & _) & _ & SEC3 & _). rewrite kSpaceSize_val in PS.
  pose proof HSR as (HS1 & _ & (PC1 & PC2) & _ & PABD & _).
  apply (secondary_repr_agree_gen mm mm' A A eq_refl eq_refl eq_refl); [| | | | exact HSR].
  - intros i ch z Hi Hz. apply MOUT.
    destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
    destruct (SEC3 i ch Hi) as (X1 & X2 & _). rewrite kSpaceSize_val in X1.
    destruct D10 as (E1 & E2 & E3 & E4 & E5). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in E5. unfold PG in *.
    destruct Hz as [Hz|Hz].
    + apply (QT_out (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z); [clear -Hz D8 D9; lia | clear -X1; lia | clear -X2; lia | exact E5 | exact E4].
    + apply (QT_sh_out (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z); [exact Hz | clear -E1; lia | clear -E3 TG; lia | clear -X1; lia].
  - intros z Hz. apply MOUT. destruct PABD as (_ & (E1 & E2 & E3 & E4 & E5)). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in E5.
    apply (QT_out (ag_pab Gq) (ag_pab Gq + kPtrArrayReserve) z); [clear -Hz PC2; lia | clear -PS; lia | clear -PT; lia | exact E5 | exact E4].
  - intros z Hz. apply MOUT. apply QT_img; unfold SEC_INST, IMG_LO, IMG_HI, QG in *; clear -Hz; lia.
  - intros i ch Hi. destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D13 & _).
    exact (MPRESB _ _ _ D13).
Qed.

Lemma view_depot : ltac2:(tb__ "0|1|
S45VA;A1S42S14S3fS22VA;A1A1M0S13S12S1eVrho0;A1A2A2VA;A2S42S14G0S13S12S1eVrho1;A1A2A2VA;A2F_;F_;").
Proof.
  intros HI3 HD. destruct HI3 as (_ & _ & _ & _ & DEP3 & _).
  unfold depot_wf in *. eapply depot_mem_frame; [|exact HD]. intros a Ha. apply MOUT.
  assert (BLK : forall bb L, In (bb, L) (dblocks (aa_depot A)) -> bb <= a < bb + L -> ~ QT a).
  { intros bb L Hbb Hab. destruct (DEP3 (bb, L) Hbb) as (DI & DT & _ & _ & _ & SS & _). unfold sepZ in DT, SS. cbn [fst snd] in DI, DT, SS.
    destruct DI as (_ & _ & _ & WI & WB). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WB. rewrite kSpaceSize_val in SS.
    apply (QT_out bb (bb + L) a Hab); [clear -SS; lia | clear -DT; lia | exact WB | exact WI]. }
  destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
  - apply QT_img; unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs; unfold IMG_LO, IMG_HI, QG; clear -Hs; lia.
  - apply (BLK bb NBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. left. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
  - apply (BLK bb FBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. right. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
Qed.

Lemma view_img : ltac2:(tb__ "0|1|
S9SbS0S34R1A2S2R1S33A2A2SeSbS0S1S3eZ98A2R2A2S2R2S1S3eZc0A2A2A2A1SdS4eS3dQ8A1A1S14S3fS22VA;A1A1M0S13S12S1eVrho1;A1A2R3A3S14G0S13S12S1eVrho0;A1A2R3A3A3F_;F_;Fz;").
Proof. intros z Hz NQ. apply MOUT. exact (QT_img z Hz NQ). Qed.

Lemma view_thread : ltac2:(tb__ "0|2|
S47S14S3fS22VA;A1M0A1M1S13S12S1eVrho0;A1A2A2G0A2S47S14G1S13S12S1eVrho1;A1A2A2G0A2F_;").
Proof.
  intros [TH1 TH2]. split.
  - rewrite MOUT; [exact TH1|]. apply QT_T. right; right. clear. lia.
  - exact (MPRES _ _ TH2).
Qed.

Lemma view_bandtp : ltac2:(tb__ "0|0|
S4fS3dQ40A1A1S41S13S12S1eVrho0;A1A2R1A2S41S13S12S1eVrho1;A1A2R2A2F_;Ftp;").
Proof.
  intros tp HB. eapply bandtp_mono; [|exact HB]. intros z _ Hz.
  destruct (v0 z) as [b|] eqn:E; [|exfalso; exact (Hz eq_refl)].
  destruct (VSOME z (ex_intro _ b E)) as [b' Hb']. rewrite Hb'. discriminate.
Qed.

Definition view_parts_stmt (tp : list word) : Prop := ltac2:(tb__ "0|4|
SbS17S13S12S1eVrho1;A1A2M0S22VA;A1M1A2SbS43S16S3fG1A1M2G0A2VA;A2SbS46S14G2G0A2M3VA;A2SbS40G3VA;A2SbS19G3S1bS1S3eZ48A2U8S3aA3A2SbS42G3VA;A2SbS44G3VA;A2SbS47G3G1A2SbS48G3A1S41G0Vtp;A2A2A2A2A2A2A2A2A2A2").
Lemma view_parts : ltac2:(tb__ "0|0|
S4fS3dQ40A1A1S60S63VA;Vrho0;R2R1A4S65R3A1F_;Fmd;Ftp;").
Proof.
  intros tp md (HG0 & HR & HF & HRest & HM & HI3 & HB). cbn zeta in *.
  destruct HRest as (R1 & R2 & R3 & R4 & (R5 & R5m) & R6 & R7 & R8 & R9). unfold view_parts_stmt.
  split; [exact (view_rtc HR)|]. split; [exact (view_fs HF)|]. split; [exact (view_live R1 R3 R4 HI3 R2)|].
  split; [exact (view_secondary HI3 R4)|].
  split.
  { eapply cell_ok_agree; [|exact R5m]. cbn [c_addr c_w]. intros k Hk. apply view_img; unfold IMG_LO, IMG_HI, QG; clear -Hk; lia. }
  split; [exact (view_depot HI3 R6)|].
  split; [exact (ia_inv_agree_q mm mm' A view_img R7)|].
  split; [exact (view_thread R8)|]. split; [exact (misc_inv_agree_q mm mm' view_img R9) | exact (view_bandtp tp HB)].
Qed.
End View.
End QWG.

Theorem K0_view : ltac2:(tb__ "0|5|
S64S27S21S21S4fS3dQ40A1M0A1S4fS61A1S60SaSdG0S20R5R1A2S20R6R1A2A3Fi;SaSdS4fS3dQ8A1M1A1S1fR6R1A2S1fR7R1A2A3Fl;S9SeS5aR9R1A2A1SdS4eG1A1M2S13S12S1eR8A1R2A3S13S12S1eR9A1R2A3A3F_;Fz;S9S5aRaR1A2SeSdG2S13S12S1eRaA1M3R2A3S51G1A1M4A3A1SeSdG2S13S12G3R3A3G4A3A1F_;F_;Fz;S62RbRaR9R7R6R5A6S62RcRbR9R8R7R6A6F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;FA;FKc;").
Proof.
  intros Kc A rho rho' tp tr md Hw Hl HOUT HIN (HA & HK & Htp & Htop & HRG).
  split; [|split; [exact HK|split; [|split]]].
  - pose proof HA as (HG & _ & _ & HRest & HM & HI3 & _). cbn zeta in HRest.
    destruct HRest as (R1 & _ & R3 & _ & (R5 & _) & _). pose proof HI3 as (H3 & _).
    assert (HAU : forall c, 1 <= c <= 30 -> 0 <= cs_allocated_user (cls_of A c) <= kUserSpaceSize).
    { intros c Hc. destruct R3 as (_ & _ & _ & P4). pose proof (P4 c Hc) as HC. unfold class_repr in HC. cbn zeta in HC.
      destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _). unfold cls_of, kUserMapSize in *. lia. }
    assert (HOUT' : forall z, ~ QW A z -> ~ False -> view segsA (rm rho') z = view segsA (rm rho) z) by (intros z Hz _; exact (HOUT z Hz)).
    assert (HIN' : forall z, QW A z \/ False -> view segsA (rm rho) z <> None -> view segsA (rm rho') z <> None) by (intros z [Hz|[]]; exact (HIN z Hz)).
    pose proof (view_parts A HG H3 R5 HAU rho rho' (fun _ => False) ltac:(intros z []) HOUT' HIN' tp md HA) as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
    unfold AInvQ. cbn zeta.
    split; [exact HG|]. split; [exact V1|]. split; [exact V2|]. split; [|split; [exact HM | split; [exact HI3 | exact V10]]].
    split; [exact R1|]. split; [exact V3|].
    split.
    { apply (primary_repr_view A (maskv (fs_footb (aa_geom A)) (view segsA (rm rho))) (maskv (fs_footb (aa_geom A)) (view segsA (rm rho')))); [| | exact HG | exact H3 | exact R5 | exact R3].
      - intros z Hz. exact (MOUT_QW A rho rho' (fun _ => False) HOUT' (fun _ F => F) z Hz).
      - intros z Hz. exact (MIN A HG H3 R5 HAU rho rho' (fun _ => False) ltac:(intros z0 []) HIN' z (or_introl Hz)). }
    split; [exact V4|]. split; [exact (conj R5 V5)|]. split; [exact V6|]. split; [exact V7|]. split; [exact V8 | exact V9].
  - unfold tp_ok in *. rewrite (Hw 24%positive). exact Htp.
  - unfold top_high in *. rewrite (Hw 10%positive), (Hw V_DEPTH). exact Htop.
  - destruct HRG as (E1 & E2 & E3 & E4). unfold rigidQ. rewrite !Hw. exact (conj E1 (conj E2 (conj E3 E4))).
Qed.
End InvQ3.

(* [comment removed for export] *)
Module RebuildRM.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "@Corelib.Init.Datatypes"; "bool"; "list"; "prod"; "fst"; "pair"; "app"; "false"; "snd"; "true"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.RebuildRM"; "sub1"; "sub2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "AA"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_depot"; "aa_ptr_committed"; "aa_sec"; "ageom"; "depot_state"; "sec_chunk"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "alloc_top"; "m_vm_lazy"; "vm_limit"; "vm_maps"; "vm_noaccess"; "vm_reserved"; "maps_subtract"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "ivs_wf"; "covered"; "model_ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kSpaceSize"; "HIGH_SHADOW_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "model_inv"; "band_page"; "inv3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "budget_boundD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "prim_credit"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra LedgerA Virt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.InvReveal.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition sub1 (b : bool) (lo hi : Z) (l : list (word * word)) : list (word * word) := ltac2:(tb__ "0|1|
S8S9SaS12Q40A1M0G0A2A1Lb;Vb;S2aVl;Vlo;Vhi;A3Vl;X8x2").
Definition sub2 (b1 : bool) (lo1 hi1 : Z) (b2 : bool) (lo2 hi2 : Z) (l : list (word * word)) : list (word * word) := ltac2:(tb__ "0|0|
S13Vb2;Vlo2;Vhi2;S13Vb1;Vlo1;Vhi1;Vl;A4A4").

Lemma sub1_wf : ltac2:(tb__ "0|1|
S8S0S0S9SaS12Q40A1M0G0A2A1S2bR1A1S1R4R3A2S2bS13R6R5R4R3A4A1F_;F_;Fl;Fhi;Flo;Fb;").
Proof. intros [|] lo hi l Hwf Hlh; cbn [sub1]; [apply maps_subtract_wf; assumption | exact Hwf]. Qed.
Lemma sub1_cov_false : ltac2:(tb__ "0|1|
S8S0S0S9SaS12Q40A1M0G0A2A1S0S2bR2A1S1R5R4A2S4S8S2cR4R3A2SeA3S4S8S2cS13R8R7R6R5A4R4A2SeA3F_;F_;F_;Fx;Fl;Fhi;Flo;Fb;").
Proof. intros [|] lo hi l x Hwf Hlh H; cbn [sub1]; [apply covered_subtract_false; assumption | exact H]. Qed.
Lemma sub1_cov_true : ltac2:(tb__ "0|1|
S8S0S0S9SaS12Q40A1M0G0A2A1S0S2bR2A1S1R5R4A2S4S8S2cS13R7R6R5R4A4R3A2S10A3S4S8S2cR5R4A2S10A3F_;F_;F_;Fx;Fl;Fhi;Flo;Fb;").
Proof. intros [|] lo hi l x Hwf Hlh H; cbn [sub1] in H; [exact (covered_subtract_true l lo hi x Hwf Hlh H) | exact H]. Qed.
Lemma sub1_keeps : ltac2:(tb__ "0|4|
S8S0S0S9SaS12Q40M0A1M1G1A2M2A1G2S0S0S2bR4A1S1R7R6A2S21G2R5R6A3S1S11G0SbG1G1R6A3A2R5A2S1R5S2S11G0SbG1G1R7A3A2S11G0SfG1G1R7A3A2A2A2S3R7R6A2S6S1R7RcA2S1RbR8A2A2S7G2G2S5S21G2R1S13RfReRdRcA4A3S5S1S11G0SbG1G1R1A3A2M3RaA2S1R9S2G3S11G0SfG1G1R1A3A2A2A2A2A2Lr';A2F_;F_;F_;F_;F_;F_;F_;Fq;Fp;Fr;Fl;Fhi;Flo;Fb;").
Proof.
  intros [|] lo hi l r p q Hwf Hlh Hin H1 H2 H3 H4; cbn [sub1]; [exact (maps_subtract_keeps l lo hi r p q Hwf Hlh Hin H1 H2 H3 H4)|].
  exists r. split; [exact Hin | split; assumption].
Qed.
Lemma sub1_in_apart : ltac2:(tb__ "0|4|
S8S0S0S9SaS12Q40M0A1M1G1A2M2A1G1G1S3R5R4A2S3Z0S11G0R2A2A2S6S1S2S11G0R4A2M3S11G0R3A2A2R7A2S1R6G3A2A2S21G2ScG1G1R5R4A4R6A3S21G2ScG1G1R6R5A4S13RaR9R8R7A4A3F_;F_;F_;F_;Fsz;Fa;Fl;Fhi;Flo;Fb;").
Proof. intros [|] lo hi l a sz Hlh Hs Hd Hin; cbn [sub1]; [apply in_maps_subtract_apart; assumption | exact Hin]. Qed.
Lemma sub1_pos : ltac2:(tb__ "0|5|
S8S0S0S9SaS12Q40M0A1M1G1A2M2A1G1G1S21G2ScG1G1R2R1A4M3R3A3S3Z0S11G0R2A2A2M4F_;Fs;Fb';G1G1S21G2G3S13R7R6R5R4A4A3G4F_;Fs;Fb';F_;Fl;Fhi;Flo;Fb;").
Proof. intros [|] lo hi l H; cbn [sub1]; [apply maps_subtract_pos; exact H | exact H]. Qed.

Section M.
Let segs : list Segment := segsA.

Lemma model_inv_sub2 : ltac2:(tb__ "0|9|
S17S17S9S12Q40M0A1M1A1M2G2S23S23S8S8S0S0S0S0S4S1eS15RbA1S15RcA1A3S4S9S20A1S1dRcA1S1dRdA1A3S4S1fS1bRdA1S1bReA1A3S4S0S1cReA1S1cRfA1A3S4S0S1aRfA1S1aR10A1A3S4S0S19R10A1S19R11A1A3S4S0S18R11A1S18R12A1A3S32R13A1S2dR10A1S3RdRcA2S3RcRbA2S1S16S15R17A1A1RfA2S1RfS2S2S16S15R18A1A1S2eA2Z1000M3A2A2S1S16S15R19A1A1RfA2S1RfS2S2S16S15R1aA1A1S2eA2G3A2A2S1S2fS16S15R1bA1A1A2S4S9SaG1G1A2A1M4S27S22R17A1A1S27S22R18A1M5A1A3S4G4S29G5A1S29S22R19A1M6A1A3S4S0S26G6A1S26S22R1aA1M7A1A3S4S0S24G7A1S24S22R1bA1M8A1A3S4G4S28G8A1S14R1aR18R17R19R16R15S28S22R1cA1A1A7A3S4G4S25R1cA1S14R1bR19R18R1aR17R16S25R1dA1A7A3G1S21G1R1R20A3S31S11G0R2A2A1F_;Fp;S1S2S33R1eSdG1R20R21A3A2S35R22A1A2S34R23A1A2S30Vsegs;R24R22R20A4S30Vsegs;R24SdG1R22R23A3R20A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fhi2;Flo2;Fhi1;Flo1;Fb2;Fb1;Fmd;Fmd0;Ftp1;Ftp0;FA';FA;").
Proof.
  intros A A' tp0 tp1 md0 md b1 b2 lo1 hi1 lo2 hi2 EG ES ED EP EV EKm EKf HI3 (Wm & Wn & Wl) LH1 LH2 SL1 SH1 SL2 SH2 SBH EM ER ELIM ETOP EN EL HBP HPAID HM.
  pose proof HI3 as (_ & _ & _ & _ & DEP3 & _).
  unfold model_inv in HM |- *. destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
  assert (Wn1 : ivs_wf (sub1 b1 lo1 hi1 (vm_noaccess (m_vmmaps md0)))) by (apply sub1_wf; [exact Wn | lia]).
  assert (Wl1 : ivs_wf (sub1 b1 lo1 hi1 (m_vm_lazy md0))) by (apply sub1_wf; [exact Wl | lia]).
  assert (COVF : forall x, covered (vm_noaccess (m_vmmaps md0)) x = false -> covered (vm_noaccess (m_vmmaps md)) x = false).
  { intros x H. rewrite EN. unfold sub2. apply sub1_cov_false; [exact Wn1 | lia|]. apply sub1_cov_false; [exact Wn | lia | exact H]. }
  assert (COVT : forall x, covered (vm_noaccess (m_vmmaps md)) x = true -> covered (vm_noaccess (m_vmmaps md0)) x = true).
  { intros x H. rewrite EN in H. unfold sub2 in H. apply (sub1_cov_true b1 lo1 hi1 _ x Wn ltac:(lia)). exact (sub1_cov_true b2 lo2 hi2 _ x Wn1 ltac:(lia) H). }
  rewrite kSpaceSize_val in SH1, SH2. unfold HIGH_SHADOW_END in SBH.
  split.
  { unfold vm_geom, in_maps in V1 |- *. rewrite EG, ES, EM.
    destruct V1 as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
    split.
    { intros e x He Hx.
      assert (CV : covered (vm_noaccess (m_vmmaps md)) x = true).
      { unfold covered. apply existsb_exists. exists e. split; [exact He|]. unfold in_iv, in_rng, ivB, ivS. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      apply COVT in CV. unfold covered in CV. apply existsb_exists in CV as (e0 & He0 & Hx0). unfold in_iv, in_rng, ivB, ivS in Hx0. apply andb_prop in Hx0 as [X1 X2].
      apply Z.leb_le in X1. apply Z.ltb_lt in X2. exact (N1 e0 x He0 (conj X1 X2)). }
    split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|]. split; [exact N7|]. split; [exact N8|].
    intros p Hal Hband. destruct (N9 p Hal Hband) as [L1 L2]. split.
    - apply page_in_ranges_spec in L1 as (r & Hr & Hpr). apply page_in_range_spec in Hpr as [Q1 Q2]. change page_size with 4096 in Q2.
      assert (OUT1 : bv_unsigned p + 4096 <= lo1 \/ hi1 <= bv_unsigned p).
      { clear -Hband SL1 SBH. unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG in *. lia. }
      assert (OUT2 : bv_unsigned p + 4096 <= lo2 \/ hi2 <= bv_unsigned p).
      { clear -Hband SL2 SBH. unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG in *. lia. }
      destruct (sub1_keeps b1 lo1 hi1 (m_vm_lazy md0) r (bv_unsigned p) (bv_unsigned p + 4096) Wl ltac:(lia) Hr Q1 Q2 ltac:(clear; lia) OUT1) as (r1 & Hr1 & X1 & X2).
      destruct (sub1_keeps b2 lo2 hi2 _ r1 (bv_unsigned p) (bv_unsigned p + 4096) Wl1 ltac:(lia) Hr1 X1 X2 ltac:(clear; lia) OUT2) as (r2 & Hr2 & Y1 & Y2).
      rewrite EL. unfold sub2. apply page_in_ranges_spec. exists r2. split; [exact Hr2|]. apply page_in_range_spec. change page_size with 4096. clear -Y1 Y2. lia.
    - intros j Hj. apply COVF. exact (L2 j Hj). }
  split; [unfold budget_boundD in HPAID |- *; rewrite EV, EKm, EKf, EP, ED; exact HPAID|].
  split; [rewrite ELIM; exact V3|]. split; [rewrite EV; exact V4|]. split; [rewrite EKm; exact V5|]. split; [rewrite EKf; exact V6|].
  split; [rewrite ETOP, EG; exact V7|].
  unfold ledger_inv in V8 |- *. cbn zeta in V8 |- *.
  destruct V8 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
  split; [rewrite ER; exact L1|]. split; [rewrite EM; exact L2|]. split; [rewrite ER, EM; exact L3|].
  split.
  { unfold gap_ok, gapN_ok, gapS_ok, blocks_left, ledger in L4 |- *. rewrite EV, ED, ER, EM. exact L4. }
  split.
  { rewrite ED. pose proof (depot_vm_grow_band A md0 tp0 tp1 HI3 L5 HBP) as L5'. destruct L5' as [D1 D2 D3 D4 D5 D6]. constructor.
    - intros bn Hbn. rewrite EM. exact (D1 bn Hbn).
    - intros b Hb. rewrite EL. unfold sub2.
      destruct (DEP3 (b, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists b; split; [reflexivity | exact Hb])) as (DY & _ & _ & _ & _ & SPb & _).
      unfold sepZ in SPb. cbn [fst snd] in SPb, DY. rewrite kSpaceSize_val in SPb.
      pose proof (dyn_in_big _ _ _ DY ltac:(unfold FBSZ; clear; lia)) as BB. destruct DY as (_ & _ & DT & _).
      pose proof (topG_range (aa_geom A)) as TR.
      assert (UB : bv_unsigned (Z_to_bv 64 b) = b) by (apply u64_lit; unfold FBSZ, IMG_HI in *; clear -BB DT TR; lia).
      assert (UF : bv_unsigned (Z_to_bv 64 FBSZ) = FBSZ) by (apply u64_lit; unfold FBSZ; clear; lia).
      apply sub1_in_apart; [exact LH2 | rewrite UF; unfold FBSZ; clear; lia | rewrite UB, UF; clear -SPb SL2 SH2; lia|].
      apply sub1_in_apart; [exact LH1 | rewrite UF; unfold FBSZ; clear; lia | rewrite UB, UF; clear -SPb SL1 SH1; lia|]. exact (D2 b Hb).
    - intros b j Hb Hj. apply COVF. exact (D3 b j Hb Hj).
    - exact D4.
    - intros bn Hbn. rewrite ETOP. exact (D5 bn Hbn).
    - rewrite ETOP. exact D6. }
  split; [rewrite ED, EKm, EKf; exact L6|]. split; [rewrite EP, EKm; exact L7|]. split; [unfold in_maps; rewrite ?EM; exact L8|]. split; [rewrite ES, EKm; exact L9|].
  rewrite EN. unfold sub2. apply sub1_pos. apply sub1_pos. exact L10.
Qed.
End M.
End RebuildRM.

(* [comment removed for export] *)
Module SpineMallocR3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sv"; "rw"; "SLit"; "SVar"; "SAlu"; "rm"; "cell"; "ss_objs"; "sprop"; "ss_facts"; "SPBranch"; "eval"; "mkCell"; "obj_range"; "ss_lenient"; "ss_next"; "SExt"; "SPNot"; "ext_low"; "smatch"; "sstate"; "swf"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "sub"; "to_nat"; "of_nat"; "pow"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nil"; "bool"; "true"; "pair"; "prod"; "false"; "nat"; "option"; "app"; "Some"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "entailsA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "PV4"; "PV6"; "PV7"; "keepn"; "GR"; "O_cell"; "PNX"; "O_pcm"; "O_ri"; "vK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3.POP"; "JRpop"; "phK"; "O_dstc"; "O_srcc"; "e_end"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "JR"; "FAb"; "PCE"; "ph_fill"; "frozen"; "ghosts"; "mkPh"; "ph_cnt"; "ph_f"; "ph_pop"; "ph_ri"; "ph_u"; "phase"; "rmlink"; "entryR"; "gh_new"; "gh_nf"; "rlink"; "zoneR"; "@Corelib.Lists.ListDef"; "nth"; "firstn"; "map"; "skipn"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "wsub_id_below"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "cell_ok"; "view"; "acell"; "c_addr"; "c_w"; "mkACell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "pc_base"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Init.Nat"; "add"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "IMG_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_thread"; "cs_cache"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refill_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "JK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2"; "BASEF"; "BASEO"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sext32_small : ltac2:(tb__ "0|2|
S0S3S1fZ0R1A2S20R1S25Z2Z1fA2A2A2S2S35Q40M0A1S1aS2aQ20S36G0R2A2M1A3G1A3F_;Fz;").
Proof.
  intros z Hz. unfold ext_low. apply bv_eq.
  assert (E : bv_unsigned (bv_extract 0 32 (Z_to_bv 64 z)) = z).
  { rewrite bv_extract_unsigned. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.shiftr_0_r.
    change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). rewrite (Z.mod_small z (2 ^ 64)) by lia. apply Z.mod_small. lia. }
  rewrite sext64_32_small by (rewrite E; lia). rewrite E. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). symmetry. apply Z.mod_small. lia.
Qed.

Lemma view_absorb_out : ltac2:(tb__ "0|1|
S7S27S6A1S6fS0S6S68S6R1R4A3S4S3S1fS32S0S0S15R6R2A2M0A3R3A2S20R3S33S0S0G0A3A2A2A1F_;Fo;S2S2fS35Q8A1A1S74S34SdS6dR5R4R3A3A1R2A3S74S34SdR5A1R2A3A3F_;Fz;Fms;FR;Frho;").
Proof.
  intros rho R ms z Hout. unfold view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  unfold rd_of. rewrite rm_absorb_out; [reflexivity|].
  intros (o & Ho & Hr). apply (Hout o Ho). rewrite u64_lit in Hr by lia. exact Hr.
Qed.

Lemma rmlink_absorb : ltac2:(tb__ "0|1|
S35Q40A1S2fS35Q8A1A1F_;S7S27S6A1S6fS5eR4SdR3A1A2S6S68S6R1R4A3S5S1fS33S0S0S15R6R2A2M0A3S87A2S1fS86S32S0S0G0A3A2A2F_;Fo;S5eR6SdS6dR5R4R3A3A1A2F_;F_;Fms;FR;Frho;Ff0;").
Proof.
  intros f0 rho R ms H HR a Ha. rewrite rm_absorb_out; [exact (H a Ha)|].
  intros (o & Ho & Hr). rewrite u64_lit in Hr by (unfold IMG_LO, IMG_HI in Ha; lia). destruct (HR o Ho); lia.
Qed.

Lemma cell_ok_agree_range : ltac2:(tb__ "0|1|
S72S72S75S0S3S1fS76R2A1M0R1A2S20R1S1eG0S24S77R2A1A1A2A2A2S2S2fS35Q8A1A1R4R2A1R5R2A1A3F_;Fz;S73R4R2A2S73R4R3A2F_;F_;Fcc;Fm';Fm;").
Proof. intros m m' cc H Hc j Hj. rewrite H by lia. exact (Hc j Hj). Qed.

Lemma ph_eta : ltac2:(tb__ "0|0|
S5dS2S5dR1S57S5cR1A1S59R1A1S54R1A1S5aR1A1S58R1A1S5bR1A1A6A3Fp;").
Proof. intros p. destruct p. reflexivity. Qed.

Lemma nth_skipn_Z : ltac2:(tb__ "0|0|
S27S0A1S2eS2eS0S2S0S64S0R2S67S0R3R4A3R1A4S64S0S82R3R2A2R4R1A4A3Fd;Fi;Fn;Fl;").
Proof. intros l n. revert l. induction n as [|n IH]; intros l i d; [reflexivity|]. destruct l as [|x l]; [destruct i; reflexivity|]. cbn [skipn Nat.add nth]. apply IH. Qed.

Section POP.

Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
S2S7eVst;S7dA3S2S27S7cA1VW;S28S7cA1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S5fVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let k : Z := kchunks c.

Variable ph : phase.
Hypothesis PH0 : ltac2:(tb__ "0|0|
S3S2S0S5aVph;A1Z0A3S3S2S29S58Vph;A1S2dA3S2S29S5bVph;A1S2dA3A2A2").
Definition phK (i : Z) : phase := ltac2:(tb__ "0|0|
S57S5cVph;A1S59Vph;A1S54Vph;A1Vi;S2dS2dA6").
Variable faP : list Z.
Let nfP : Z := Z.of_nat (length faP).
Hypothesis HSRC : ltac2:(tb__ "0|1|
S0S72S3S1fZ0M0R2A2S1fR2Vk;A2A2S62VA;Vrb;S4aR3A1S74S34SdVrb;A1A2R2A5S0S3S1fG0R1A2S20R1VnfP;A2A2S73R5S78S1eS52VA;Vrb;A2S21Z4R2A2A2U4S64S0S23R2A1VfaP;G0A4A3A2F_;Fidx;F_;F_;Fm;Fi;").
Hypothesis HKF : k <= nfP.
Hypothesis HNFP : 4 * nfP <= 536870912.
Hypothesis HFILLR : ltac2:(tb__ "0|4|
S20Z0M0S54Vph;A1M1A2S3S1fG0S61VA;Vrb;A2M2A2S3S2S0S1eG2S60VA;Vrb;A2M3A2VnfP;A3S1fG1G3A2A2A2F_;").
Hypothesis HIDS : ltac2:(tb__ "0|0|
S0S68S0R1VfaP;A3S3S1fZ0R2A2S20R2S25Z2Z1cA2A2A2F_;Fx;").
Hypothesis HCACHE : ltac2:(tb__ "0|0|
S2S27S0A1S8aS8bVc;S8dVA;Vnv;A2A2A1S67S0S23S22VnfP;Vk;A2A1VfaP;A3A3").

Lemma zone_thread : ltac2:(tb__ "0|2|
S0S0S3S1fS1eS89S88VA;A1A1M0Z120A2R1A2S20R1S1eG0Zc60A2A2A2S63VA;Vrb;S4aR3A1R2A4S3S1fS1eS53VA;Vrb;A2Z10A2M1R3A2S20R3S1eG1S21Z4R4A2A2A2A2F_;F_;Fz;Fi;").
Proof.
  intros i z Hz HZ.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF.
  destruct CF as ((_ & C1 & _) & _ & (_ & MU0 & MU1 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  pose proof (Zle_0_nat (length (cs_free_array (cst_of A nv)))) as NF0.
  unfold zoneR, phK in HZ. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri] in HZ. fold nv c in HZ.
  unfold U0, F0, FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize, kFreeArrayMapSize, Sh, SHADOW_OFF in HZ. fold nv c in HZ.
  destruct HZ as [[_ X]|[[_ X]|[[_ X]|[[_ X]|[[X X2]|[X|[[X _]|[X _]]]]]]]]; try discriminate X; try exact X; exfalso.
  - clear -X Hz MU0 MU1 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MU0 MU1 C1 G13 G14 TG PS1 T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG PS1 T1 T2. lia.
  - destruct (HFILLR X2) as (F1 & F2 & F3). unfold gh_nf, gh_new in *. fold nv c in F1, F2, F3, X.
    clear -X Hz F1 F2 F3 HNFP C1 G13 G14 TG PS1 T1 T2. lia.
Qed.

Definition JRpop (i : Z) : jpredA := ltac2:(tb__ "0|3|
S7S27S35Q40M0A1M1A1S27S6bA1S6aS3S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVi;A1R4R3R2R1AaS3S2G1S9R4S3dA2S36G0S1eS1eS53VA;Vrb;A2Z10A2S21Z4M2Vi;A2A2A2A3S2G1S9R4S3eA2S36G0S1eS52VA;Vrb;A2S21G2S1eS22VnfP;Vk;A2Vi;A2A2A2A2A3A2A2Lmd;Ltr;Ltp;Lr;").
Lemma JRpop_K : ltac2:(tb__ "0|0|
S0S8cVKc;S49R1A1A2Fi;").
Proof. intros i r t tr md [H _]. exact (JR_K A Kc rb tp0 md0 _ r t tr md H). Qed.
Lemma JRpop_stable : ltac2:(tb__ "0|0|
S0S1S2S29S80S43R1A2S2aA3S48S34R2S49R3A1A3F_;Fn;Fi;").
Proof.
  intros i n Hn r r' tp tr md md' Hag Hme (HJ & H4 & H6). apply Pos.leb_le in Hn. unfold PNX in Hn.
  split; [|split].
  - eapply (JR_stable A Kc rb tp0 md0 (phK i) n HKc); [unfold GR; lia | exact Hag | exact Hme | exact HJ].
  - destruct Hag as (Hw & _). rewrite <- (Hw PV4) by (unfold PV4; lia). exact H4.
  - destruct Hag as (Hw & _). rewrite <- (Hw PV6) by (unfold PV6; lia). exact H6.
Qed.

Definition O_srcc : sobj := ltac2:(tb__ "0|0|
S42S3eS26SeS14SaZ0A1Z4SbS3fA1A3S28SeA1A3A2").
Definition O_dstc : sobj := ltac2:(tb__ "0|0|
S42S3dS26SeS14SaZ0A1Z4S18S2aQ20SbS3fA1A3A3S28SeA1A3A2").

Lemma pop_release : ltac2:(tb__ "0|6|
S1cS27S6A1M0S7S27S35Q40M1A1M2A1S27S6bA1M3S6fS6aS6aS0S3S1fZ0M4R1A2S20R1Vk;A2A2S2G0SfRaA1S30S6R9S26S6S4cS26S6S4bS28S6A1A3A3M5A3A3S1bS34R9RbS2bG3S83R7S84R6R5A2A4A4S2G2S9RaS3fA2S36G1S64S0S23S1eS22VnfP;Vk;A2R4A2A1VfaP;G4A4A2A3S49R5RbRaR9R6A5S6dRcG5R9A3S7S3S51VA;VKc;Vrb;Vtp0;Vmd0;S4aS1eR7Z1A2A1R1RcRbR8AaS3S2G2S9R1S3dA2S9RdS3dA2A3S2G2S9R1S3eA2S9RdS3eA2A3A2A2Tr3;F_;F_;F_;F_;F_;Fi;FmdJ;Fmd;Fms;Ftr;Ftp;Fr2;FK;FS;").
Proof.
  intros S K r2 tp tr ms md mdJ i Hi HO Hsm H7 ((HFz & HGh & HKc' & HM & HR & HRM) & H4 & H6) r3.
  split; [|split; reflexivity].
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _ & _) & _ & (_ & N6) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB). fold k in K1.
  set (idv := nth (Z.to_nat (nfP - k + i)) faP 0) in *.
  assert (Hid : 0 <= idv < 2 ^ 28).
  { apply HIDS. unfold idv. apply nth_In. unfold nfP in *. lia. }
  set (Si := FAb A rb + 4 * (nfP - k + i)) in *. set (Di := PCE A rb + 16 + 4 * i) in *.
  idtac "pr:1".
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. lia. }
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  assert (RS : obj_range r2 O_srcc = (Si, Si + 4)).
  { unfold O_srcc, O_cell. rewrite obj_range_mk by lia. cbn [eval]. rewrite H6, u64_lit by (unfold Si in *; lia). f_equal; lia. }
  assert (RD : obj_range r2 O_dstc = (Di, Di + 4)).
  { unfold O_dstc, O_cell. rewrite obj_range_mk by lia. cbn [eval]. rewrite H4, u64_lit by (unfold Di in *; lia). f_equal; lia. }
  set (m2 := view segs (rm r2)) in *. set (m3 := view segs (rm r3)).

  assert (M3S : forall j, (j < 4)%nat -> m3 (Si + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. destruct (absorb_obj r2 S tr ms md K [O_srcc; O_dstc] O_srcc Hsm HO (or_introl eq_refl)) as (_ & AS & _).
    destruct (AS (mkCell (SLit 0) 4 (SVar PV7)) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_srcc O_cell eval c_off SymState.c_val c_width] in ASb. rewrite H6, soff_lit_small, u64_lit in ASb by (unfold Si in *; lia).
    rewrite H7 in ASb. unfold m3. rewrite view_in by (unfold Si in *; lia). fold Si in ASb. replace (Si + 0 + Z.of_nat j) with (Si + Z.of_nat j) in ASb by lia. exact ASb. }
  assert (M3D : forall j, (j < 4)%nat -> m3 (Di + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. destruct (absorb_obj r2 S tr ms md K [O_srcc; O_dstc] O_dstc Hsm HO (or_intror (or_introl eq_refl))) as (_ & AS & _).
    destruct (AS (mkCell (SLit 0) 4 (SExt true 32 (SVar PV7))) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_dstc O_cell eval c_off SymState.c_val c_width] in ASb. rewrite H4, soff_lit_small, u64_lit in ASb by (unfold Di in *; lia).
    rewrite H7, sext32_small in ASb by lia. unfold m3. rewrite view_in by (unfold Di in *; lia). fold Di in ASb. replace (Di + 0 + Z.of_nat j) with (Di + Z.of_nat j) in ASb by lia. exact ASb. }
  assert (M2S : forall j, (j < 4)%nat -> m2 (Si + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. pose proof (HSRC i m2 ltac:(lia) HR (nfP - k + i) ltac:(lia)) as Hc. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
    unfold Si. exact Hc. }
  assert (AGR : forall z, ~ (Di <= z < Di + 4) -> m3 z = m2 z).
  { intros z Hz. destruct (Z_le_dec Si z) as [H1|H1]; [destruct (Z_lt_dec z (Si + 4)) as [H2|H2]|].
    - replace z with (Si + Z.of_nat (Z.to_nat (z - Si))) by lia. rewrite M3S, M2S by lia. reflexivity.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RS | rewrite RD]; cbn [fst snd]; lia.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RS | rewrite RD]; cbn [fst snd]; lia. }
  idtac "pr:2".
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HKc'|]. split; [exact HM|].
  split; [|apply (rmlink_absorb _ r2 [O_srcc; O_dstc] ms HRM); intros o [<-|[<-|[]]]; [rewrite RS | rewrite RD]; cbn [fst snd];
           unfold IMG_LO, IMG_HI, Si, Di; rewrite ?FAr, ?PCr; unfold nfP in *; lia].
  fold m3. unfold rlink in HR |- *. fold m2 in HR.
  destruct HR as (L1 & L2 & L3 & L4 & L5 & L6).
  assert (ZI : forall z, zoneR A rb (phK (i + 1)) z <-> (zoneR A rb (phK i) z \/ Di <= z < Di + 4)).
  { intros z. unfold zoneR, phK. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri]. fold nv c. unfold Di. split.
    - intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
      + left; left; exact H.
      + left; right; left; exact H.
      + left; right; right; left; exact H.
      + left; right; right; right; left; exact H.
      + left; right; right; right; right; left; exact H.
      + destruct (Z_lt_dec z (PCE A rb + 16 + 4 * i)); [left; right; right; right; right; right; left; lia | right; lia].
      + left; right; right; right; right; right; right; left; exact H.
      + left; right; right; right; right; right; right; right; exact H.
    - intros [[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|H].
      + left; exact H.
      + right; left; exact H.
      + right; right; left; exact H.
      + right; right; right; left; exact H.
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; lia.
      + right; right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; right; exact H.
      + right; right; right; right; right; left; lia. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros z Hz. rewrite AGR by (intros X; apply Hz; apply ZI; right; exact X). apply L1. intros X. apply Hz. apply ZI. left. exact X.
  - intros z Hz. apply ZI in Hz. destruct (Z_le_dec Di z) as [H1|H1]; [destruct (Z_lt_dec z (Di + 4)) as [H2|H2]|].
    + replace z with (Di + Z.of_nat (Z.to_nat (z - Di))) by lia. rewrite M3D by lia. discriminate.
    + rewrite AGR by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
    + rewrite AGR by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
  - intros j Hj. cbn [ph_fill phK] in Hj |- *. eapply cell_ok_agree_range; [|exact (L3 j Hj)]. cbn [c_addr c_w]. intros z Hz. apply AGR.
    destruct (HFILLR ltac:(lia)) as (F1 & F2 & F3). unfold Di. rewrite PCr. rewrite FAr in Hz. change (Z.of_nat 4) with 4 in Hz.
    clear -Hz C1 PS1 T1 T2 G13 G14 TG Hj Hi K1 HNFP F1 F2 F3. lia.
  - intros i' Hi'. cbn [ph_pop phK] in Hi'. destruct (Z.eq_dec i' i) as [->|Hne].
    + intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *. fold Di. rewrite M3D by exact Hj. do 3 f_equal. fold nv c. rewrite HCACHE, nth_skipn_Z.
      unfold idv. replace (Z.to_nat (nfP - k) + Z.to_nat i)%nat with (Z.to_nat (nfP - k + i)) by (clear -HKF Hi; lia). reflexivity.
    + eapply cell_ok_agree_range; [|exact (L4 i' ltac:(cbn [ph_pop phK]; lia))]. cbn [c_addr c_w]. intros z Hz. apply AGR. unfold Di. lia.
  - intros X. discriminate X.
  - intros X. discriminate X.
Qed.

Variable F : nat.
Variable CT0 : axst.
Variables LB LX : leafA.
Variable nob : nat.
Variable s_bk : wsub.
Let CT1 : axst := cT1 CT0.
Definition e_end : sv := ltac2:(tb__ "0|0|
ScS4eScS4eS79SaZ10A1A3ScS50S46SaZ2A1A3A3").
Definition NPOP : list carve_spec := ltac2:(tb__ "0|9|
S26S2cS2cS2cS8S0A2M0S0A2M1S27S2cS2cS0S2eA2M2S8A2M3A1M4A2M5S2bG1G4S2bG0S0S2bS8S0SbS3eA1Z0M6A4Z4M7A4S26G3S2bG2S8S2bS0S2eG6U4A4SbS3fA1A4S28G3A1M8A3A4S26G5S2bG1G4S2bG0S0S2bS8S0SbS3dA1G6A4G7A4G8A4S28G5A1A3A3").
Hypothesis SK_t : ltac2:(tb__ "0|1|
S2S27S2cS2cS8S8A2S8A2M0A1S66S6G0S7fSfS38VCT0;A1A1A4S66S6G0S7fS30S6S8fVW;A1S26S6S7aS26S6S7bS26S6S44S26S6S45S28S6A1A3A3A3A3A3A4A3").
Hypothesis XX_t : ax_X CT0 = [].
Hypothesis XF_t : ltac2:(tb__ "0|0|
S69S10S8eVW;Vst;A2S11S38VCT0;A1A1A3").
Hypothesis NX_t : ltac2:(tb__ "0|0|
S2S29S81S17S38VCT0;A1A1S43A2S2aA3").
Hypothesis W_t1 : ltac2:(tb__ "0|0|
S2S29S1dS38VCT1;A1A1S2aA3").
Hypothesis R_t1 : ltac2:(tb__ "0|1|
S2S2fS27S3aA1M0A1S3cS34VF;S26S0Z41570S26S0Z41584S28S0A1A3A3VCT1;S2aA5S31G0S26S3aVLB;S26S3aVLX;S28S3aA1A3A3A2A3").
Hypothesis LN_t1 : ltac2:(tb__ "0|0|
S2S29S16S38VCT1;A1A1S2dA3").
Hypothesis OB_b : ltac2:(tb__ "0|1|
S2S27S6A1SfS38S39VLB;A1A1A1M0S30S6S65S6Vnob;G0A3S26S6S4cS26S6S4bS28S6A1A3A3A3A3").
Hypothesis OB_x : ltac2:(tb__ "0|1|
S2S27S6A1SfS38S39VLX;A1A1A1M0S30S6S65S6Vnob;G0A3S26S6S4cS26S6S4bS28S6A1A3A3A3A3").
Hypothesis ENT_bk : ltac2:(tb__ "0|0|
S2S29S3bS40S39VLB;A1Vnob;A2VCT0;Vs_bk;A3S2aA3").
Hypothesis SID_bk : ltac2:(tb__ "0|0|
S2S29S6eVs_bk;S41A2S2aA3").
Hypothesis S_bk4 : ltac2:(tb__ "0|0|
S2S8S6cVs_bk;S3dA2ScS4eSbS3dA1SaZ4A1A3A3").
Hypothesis S_bk6 : ltac2:(tb__ "0|0|
S2S8S6cVs_bk;S3eA2ScS4eSbS3eA1SaZ4A1A3A3").
Hypothesis FB_b : ltac2:(tb__ "0|0|
S68S10S12S4fScS4eSbS3dA1SaZ4A1A3S4dA3S11S38S39VLB;A1A1A1A3").
Hypothesis FB_x : ltac2:(tb__ "0|0|
S68S10S19S12S4fScS4eSbS3dA1SaZ4A1A3S4dA3A1S11S38S39VLX;A1A1A1A3").

Lemma pop_carve : ltac2:(tb__ "0|5|
S0S7S27S35Q40M0A1M1A1S71S3S1fZ0M2R4A2S20R4Vk;A2A2S47S34S49R5A1VCT0;R4R3R2A6S85R5S26S2cS1G1A2M3S2bS1G1S3fS36G0S64S0S23S1eS22VnfP;Vk;A2M4R6A2A1VfaP;G2A4A2A4S28G3A1A3A2S7S3S47S34S49R7A1VCT1;R1R5R4A6S2G1S9R1S3fA2S36G0S64S0S23S1eG4R7A2A1VfaP;G2A4A2A3A2Tr1;F_;F_;Fw;Ftp;Fr;Fi;").
Proof.
  intros i r tp w Hi H r1.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _ & _) & (_ & MU0 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB). fold k in K1.
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. lia. }
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  set (idv := nth (Z.to_nat (nfP - k + i)) faP 0) in *.
  assert (E7 : rw r1 PV7 = Z_to_bv 64 idv).
  { unfold r1. apply (rw_rho_sets_in r _ PV7); [repeat constructor; intros [] | left; reflexivity]. }
  split; [|exact E7].
  assert (AG1 : agree_below PNX r r1). { unfold r1. apply agree_below_rho_sets. intros j v [X|[]]. injection X as <- _. unfold PNX, PV7. lia. }
  assert (Erm1 : rm r1 = rm r) by (unfold r1; apply rm_rho_sets).
  assert (H1 : SPA segs (JRpop i) CT0 r1 tp w).
  { destruct H as [Hsm HJ]. split.
    - eapply smatchA_agree; [|exact Hsm]. apply Pos.eqb_eq in NX_t. rewrite NX_t. exact AG1.
    - eapply (JRpop_stable i PNX ltac:(reflexivity)); [exact AG1 | apply mat_equiv_refl | exact HJ]. }
  idtac "pc:1".
  destruct H1 as [HsmA1 HJ1]. pose proof HJ1 as ((HFz & HGh & _ & _ & HR & _) & H4 & H6). pose proof (proj1 HJ1) as HJ1'.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0.
  pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r1 CF0 RG HGh) as (EB & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
  pose proof (proj1 HsmA1) as Hsm1. unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S CT0) [O_pcc0; O_st; O_pcm; O_ri] r1 _ HW HE HFz Hsm1 SK_t XF_t) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|om [|ori [|? ?]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
  rewrite <- (obj_range_skel r1 oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r1 os O_st SKs) in RNs.
  rewrite <- (obj_range_skel r1 om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r1 ori O_ri SKr) in RNr.
  set (Si := FAb A rb + 4 * (nfP - k + i)) in *. set (Di := PCE A rb + 16 + 4 * i) in *.
  set (m1 := view segs (rm r1)) in *. unfold rlink in HR. fold m1 in HR.
  assert (ES : bv_unsigned (eval r1 (SVar PV6)) = Si) by (cbn [eval]; rewrite H6; apply u64_lit; unfold Si; lia).
  assert (ED : bv_unsigned (eval r1 (SVar PV4)) = Di) by (cbn [eval]; rewrite H4; apply u64_lit; unfold Di; lia).

  assert (MS : forall j, (j < 4)%nat -> m1 (Si + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. pose proof (HSRC i m1 ltac:(lia) (proj1 (proj2 (proj2 (proj2 (proj2 HJ1'))))) (nfP - k + i) ltac:(lia)) as Hc. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc. exact Hc. }
  assert (PD : forall z, Di <= z < Di + 4 -> exists b, m1 z = Some b).
  { intros z Hz. destruct HR as (L1 & L2 & _).
    assert (ZD : zoneR A rb (phK i) z \/ ~ zoneR A rb (phK i) z).
    { destruct (Z_lt_dec z (PCE A rb + 16 + 4 * i)) as [Y|Y]; [left; unfold zoneR, phK; cbn [ph_pop]; do 5 right; left; unfold Di in Hz; lia|].
      right. intros X. apply (zone_thread i z) in X; [lia|]. unfold Di in Hz. rewrite PCr in Hz. lia. }
    destruct ZD as [ZD|ZD].
    - specialize (L2 z ZD). destruct (m1 z) as [b|] eqn:Em; [exists b; reflexivity | exfalso; apply L2; first [exact Em | reflexivity]].
    - rewrite (L1 z ZD). destruct HE as (_ & HA & _ & _ & _ & Hnv & _ & Hcnt & _).
      destruct (pc_entry_facts0 segs A rb tp0 md0 nv HA Hnv Hcnt) as (_ & PE & _). cbn zeta in PE. fold c in PE. apply PE. unfold Di in Hz. rewrite PCr in Hz. lia. }
  idtac "pc:2".
  assert (SiR : ag_spacebeg (aa_geom A) <= Si /\ Si + 4 <= ag_spacebeg (aa_geom A) + 137438953472) by (unfold Si; rewrite FAr; lia).
  assert (DiR : ag_thread (aa_geom A) + 288 <= Di /\ Di + 4 <= ag_thread (aa_geom A) + 2656) by (unfold Di; rewrite PCr; lia).
  assert (HS1 : SPA segs (JRpop i) CT0 r1 tp w) by (split; [exact HsmA1 | exact HJ1]).
  apply (SPA_carve_list segs _ r1 CT0 tp w NPOP PNX1 HS1 W_t1).
  - apply Pos.eqb_eq in NX_t. rewrite NX_t. unfold PNX, PNX1. lia.
  - unfold NPOP. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + rewrite ES. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [repeat apply Forall_cons; try apply Forall_nil; lia|].
      split.
      { intros off Hoff. rewrite Erm1. specialize (MS (Z.to_nat off) ltac:(lia)). replace (Si + Z.of_nat (Z.to_nat off)) with (Si + off) in MS by lia.
        unfold m1 in MS. rewrite Erm1 in MS. rewrite view_in in MS by lia. eapply wok_rd_off_image; [|exact MS]. lia. }
      split; [|unfold xwords_clear; rewrite XX_t; intros rr y j []].
      apply Forall_cons; [|apply Forall_nil]. intros j Hj. cbn [eval]. rewrite E7. specialize (MS j Hj). unfold m1 in MS. rewrite view_in in MS by lia.
      replace (Si + 0 + Z.of_nat j) with (Si + Z.of_nat j) by lia. exact MS.
    + rewrite ED. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [apply Forall_nil|].
      split.
      { intros off Hoff. destruct (PD (Di + off) ltac:(lia)) as [b Hb]. unfold m1 in Hb. rewrite view_in in Hb by lia.
        eapply wok_rd_off_image2; [| |exact Hb]; lia. }
      split; [apply Forall_nil | unfold xwords_clear; rewrite XX_t; intros rr y j []].
  - cbn [map carve_obj NPOP]. unfold carved.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; rewrite obj_range_mk by lia; rewrite ?ES, ?ED; rewrite EO; apply Forall_app; split.
    + apply BZ. right; left. rewrite kSpaceSize_val. lia.
    + repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr; unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; lia.
    + apply BZ. left. lia.
    + repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr; unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; unfold Di in *; rewrite ?PCr in *; lia.
  - cbn [map carve_obj NPOP pairwise_disjoint]. unfold carved. split; [|split; [constructor | exact I]].
    apply Forall_cons; [|apply Forall_nil]. rewrite !obj_range_mk by lia. rewrite ES, ED. unfold ranges_disjoint; cbn [fst snd]. lia.
Qed.

Lemma e_end_val : ltac2:(tb__ "0|0|
S7S55Vrb;R1A2S56VA;Vrb;R2A3S2S0S37Q40S13R3S4dA2A2S1eS1eS53VA;Vrb;A2Z10A2S21Z4Vk;A2A2A3F_;F_;Fr;").
Proof.
  intros r HFz HGh.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & _).
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB). fold k in K1.
  destruct HGh as (_ & _ & _ & _ & _ & _ & _ & Q227 & _). fold nv c k in Q227.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  unfold e_end, vK. cbn [eval]. rewrite add_val, add_val, sll_val. rewrite EB, Q227, !u64_lit by lia. change (2 mod 64) with 2.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (k * 2 ^ 2)) by lia. rewrite (Z.mod_small (PCE A rb + 16)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition JRrel (i : Z) : jpredA := ltac2:(tb__ "0|3|
S7S27S35Q40M0A1M1A1S27S6bA1S6aS3S51VA;VKc;Vrb;Vtp0;Vmd0;S4aS1eVi;Z1A2A1R4R3R2R1AaS3S2G1S9R4S3dA2S36G0S1eS1eS53VA;Vrb;A2Z10A2S21Z4M2Vi;A2A2A2A3S2G1S9R4S3eA2S36G0S1eS52VA;Vrb;A2S21G2S1eS22VnfP;Vk;A2Vi;A2A2A2A2A3A2A2Lmd;Ltr;Ltp;Lr;").

Lemma pop_iter : ltac2:(tb__ "0|1|
S0S7S27S35Q40A1A1S70S3S1fZ0R4A2S20R4Vk;A2A2S20S1eR5Z1M0A2Vk;A2S7VTR;S47S34S49S1eR7G0A2A1VCT0;R1R5A5R4A2Fr';F_;S2S0S1eR6G0A2Vk;A3S7VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVk;A1A6S40S39VLX;A1Vnob;A2R1R6A5R5A2Fr';F_;VTR;S47S34S49R7A1VCT0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;").
Proof.
  intros i r tp Q Hi HKb HKx.
  assert (NUM : 0 <= PCE A rb /\ PCE A rb + 16 + 4 * k + 8 < 2 ^ 62 /\ 1 <= k <= 8).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
    destruct CF0 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & _ & (T1 & T2 & _) & _). fold k in K1. pose proof (topG_range (aa_geom A)) as TG. unfold PCE. fold nv c. lia. }
  set (idv := nth (Z.to_nat (nfP - k + i)) faP 0).
  set (r1 := rho_sets r [(PV7, Z_to_bv 64 idv)]).
  assert (E7 : rw r1 PV7 = Z_to_bv 64 idv).
  { unfold r1. apply (rw_rho_sets_in r _ PV7); [repeat constructor; intros [] | left; reflexivity]. }
  apply (tr_pre Kc TR KIT (SPA segs (JRpop i) CT1 r1 tp)); [intros w Hw; exact (proj1 (pop_carve i r tp w Hi Hw))|].
  apply (tr_run Kc TR KIT F [0x41570; 0x41584] CT1 [LB; LX] (JRpop i) r1 tp Q (JRpop_K i) (JRpop_stable i (ss_next (ax_S CT1)) eq_refl) R_t1 LN_t1).
  intros L r2 HL Hag.
  assert (NX1 : ss_next (ax_S CT1) = PNX1) by reflexivity. rewrite NX1 in Hag.
  assert (E72 : rw r2 PV7 = Z_to_bv 64 idv) by (destruct Hag as (Hw & _); rewrite <- (Hw PV7) by (unfold PV7, PNX1; lia); exact E7).

  assert (REL : forall (LL : leafA), ss_objs (ax_S (la_state LL)) = firstn nob (ss_objs (ax_S (la_state LL))) ++ [O_srcc; O_dstc] ->
            forall w, SPA segs (JRpop i) (la_state LL) r2 tp w -> exists r3, SPA segs (JRrel i) (keepn (la_state LL) nob) r3 tp w).
  { intros LL HO [tr [ms md]] Hw. exists (rho_absorb r2 [O_srcc; O_dstc] (vms md tp ms)).
    apply (SPA_unobj_J (JRpop i) (JRrel i) r2 (la_state LL) _ [O_srcc; O_dstc] tp tr ms md HO Hw).
    intros Hsm HJ. pose proof HJ as (_ & H4 & H6).
    destruct (pop_release (ax_S (la_state LL)) _ r2 tp tr (vms md tp ms) (vmd md) md i Hi HO Hsm E72 HJ) as (P1 & P2 & P3). cbn zeta in P1, P2, P3.
    split; [exact P1|]. split; [rewrite P2; exact H4 | rewrite P3; exact H6]. }
  destruct HL as [<-|[<-|[]]].
  -
    apply (tr_facts Kc TR KIT). intros HF.
    pose proof (proj1 (Forall_forall _ _) HF _ FB_b) as BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 < k)).
    { intros w [_ ((HFz & HGh & _) & H4 & _)]. unfold branch_taken, bv_eqb in BF. apply negb_true_iff in BF. apply Z.eqb_neq in BF.
      rewrite (e_end_val r2 HFz HGh) in BF. cbn [eval] in BF. rewrite add_val, H4, !u64_lit in BF by lia.
      rewrite Z.mod_small in BF by lia. lia. }
    intros Hlt.
    apply (tr_cut Kc TR KIT valuation _ (fun r3 => SPA segs (JRrel i) (keepn (la_state LB) nob) r3 tp) Q (REL LB OB_b)).
    intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRpop (i + 1)) CT0 (rho_sub r3 s_bk) tp)); [|exact (HKb Hlt _)].
    intros w Hw. apply (SPA_entails_J (JRrel i) (JRpop (i + 1)) _ CT0 s_bk r3 tp w ENT_bk); [|exact Hw].
    intros (HJ & H4 & H6). pose proof (rho_sub_agree s_bk GR r3 SID_bk) as AGs.
    split; [|split].
    + eapply (JR_stable A Kc rb tp0 md0 (phK (i + 1)) GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
    + cbn [rho_sub rw]. rewrite S_bk4. cbn [eval]. rewrite H4. apply bv_eq. rewrite add_val, !u64_lit by lia. rewrite Z.mod_small by lia. lia.
    + cbn [rho_sub rw]. rewrite S_bk6. cbn [eval]. rewrite H6. apply bv_eq.
      assert (FAR : 0 <= FAb A rb /\ FAb A rb + 536870912 + 8 < 2 ^ 62).
      { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
        destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _).
        unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. lia. }
      rewrite add_val, !u64_lit by lia. rewrite Z.mod_small by lia. lia.
  -
    apply (tr_facts Kc TR KIT). intros HF.
    pose proof (proj1 (Forall_forall _ _) HF _ FB_x) as BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 = k)).
    { intros w [_ ((HFz & HGh & _) & H4 & _)]. unfold branch_taken, bv_eqb in BF. apply not_true_is_false in BF. apply negb_false_iff in BF. apply Z.eqb_eq in BF.
      rewrite (e_end_val r2 HFz HGh) in BF. cbn [eval] in BF. rewrite add_val, H4, !u64_lit in BF by lia.
      rewrite Z.mod_small in BF by lia. lia. }
    intros Heq.
    apply (tr_cut Kc TR KIT valuation _ (fun r3 => SPA segs (JRrel i) (keepn (la_state LX) nob) r3 tp) Q (REL LX OB_x)).
    intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRp (phK k)) (keepn (la_state LX) nob) r3 tp)); [|exact (HKx Heq _)].
    intros w Hw. apply (SPA_J (JRrel i) (JRp (phK k)) _ r3 tp w); [|exact Hw]. intros (HJ & _). rewrite <- Heq. exact HJ.
Qed.

Lemma pop_loop : ltac2:(tb__ "0|0|
S2eS0S7S27S35Q40A1A1S70S2S0S22Vk;R4A2S24R5A1A3S3S1fZ0R5A2S20R5Vk;A2A2S7VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVk;A1A6S40S39VLX;A1Vnob;A2R1R5A5R4A2Fr';VTR;S47S34S49R7A1VCT0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;Fn;").
Proof.
  induction n as [|n IH]; intros i r tp Q Hn Hi HX; [lia|].
  apply (pop_iter i r tp Q Hi).
  - intros Hlt r'. apply (IH (i + 1) r' tp Q); [lia | lia | exact HX].
  - intros _ r'. apply HX.
Qed.

Variable J0 : axst.
Variable LT0 : leafA.
Variable s_in : wsub.
Variable e_src : sv.
Hypothesis R_t0 : ltac2:(tb__ "0|1|
S2S2fS27S3aA1M0A1S3cS34VF;S26S0Z41570S26S0Z41584S28S0A1A3A3VJ0;S2aA5S31G0S26S3aVLT0;S28S3aA1A3A2A3").
Hypothesis LN_t0 : ltac2:(tb__ "0|0|
S2S29S16S38VJ0;A1A1S2dA3").
Hypothesis NX_t0 : ltac2:(tb__ "0|0|
S2S29S80S41S17S38VJ0;A1A1A2S2aA3").
Hypothesis ENT_in : ltac2:(tb__ "0|0|
S2S29S3bS39VLT0;A1VCT0;Vs_in;A3S2aA3").
Hypothesis SID_in : ltac2:(tb__ "0|0|
S2S29S6eVs_in;S41A2S2aA3").
Hypothesis S_in4 : ltac2:(tb__ "0|0|
S2S8S6cVs_in;S3dA2ScS4eS79SaZ10A1A3A3").
Hypothesis S_in6 : ltac2:(tb__ "0|0|
S2S8S6cVs_in;S3eA2Ve_src;A3").
Hypothesis HSRCP : ltac2:(tb__ "0|1|
S7S55Vrb;R1A2S56VA;Vrb;R2A3S2S35Q40M0A1S13R3Ve_src;A2S36G0S1eS52VA;Vrb;A2S21Z4S22VnfP;Vk;A2A2A2A2A3F_;F_;Fr;").

Lemma phK0 : phK 0 = ph.
Proof.
  destruct PH0 as (P1 & P2 & P3).
  transitivity (mkPh (ph_u ph) (ph_f ph) (ph_fill ph) (ph_pop ph) (ph_cnt ph) (ph_ri ph)); [unfold phK; rewrite P1, P2, P3; reflexivity | symmetry; apply ph_eta].
Qed.

Lemma pop_all : ltac2:(tb__ "0|0|
S7S27S35Q40A1A1S70S7VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVk;A1A6S40S39VLX;A1Vnob;A2R1R3A5R2A2Fr';VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VJ0;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HX.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x41570; 0x41584] J0 [LT0] ph r tp Q R_t0 LN_t0 NX_t0).
  intros L r1 [<-|[]] _.
  assert (K1 : 1 <= k).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0. destruct CF0 as (_ & (K1 & _) & _). fold k in K1. lia. }
  apply (tr_pre Kc TR KIT (SPA segs (JRpop 0) CT0 (rho_sub r1 s_in) tp)); [|apply (pop_loop (Z.to_nat k) 0 _ tp Q); [lia | lia | exact HX]].
  intros w Hw. apply (SPA_entails_J (JRp ph) (JRpop 0) _ CT0 s_in r1 tp w ENT_in); [|exact Hw].
  intros HJ. pose proof (rho_sub_agree s_in GR r1 SID_in) as AGs. pose proof HJ as (HFz & HGh & _).
  split; [|split].
  - rewrite phK0. eapply (JR_stable A Kc rb tp0 md0 ph GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
  - cbn [rho_sub rw]. rewrite S_in4. cbn [eval].
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
    destruct (arm_extra_ranges A rb r1 CF0 RG HGh) as (EB & _).
    apply bv_eq. rewrite add_val, EB, !u64_lit.
    + rewrite Z.mod_small; [lia|]. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
      destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & _ & (T1 & T2 & _) & _). pose proof (topG_range (aa_geom A)) as TG. unfold PCE. fold nv c. lia.
    + unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
      destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & _ & (T1 & T2 & _) & _). pose proof (topG_range (aa_geom A)) as TG. unfold PCE. fold nv c. lia.
    + lia.
  - cbn [rho_sub rw]. rewrite S_in6. rewrite (HSRCP r1 HFz HGh). f_equal. lia.
Qed.
End POP.
End SpineMallocR3.

