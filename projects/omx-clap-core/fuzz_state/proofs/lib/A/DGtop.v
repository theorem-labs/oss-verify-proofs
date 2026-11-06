(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGtop.v (a working branch 84ee52cd012, file sha256 6b9a7e54f057) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 6 image addresses moved by code-verified function pairs (6 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated to omx-clap-core fuzz_state image A (fs.asan): fs C5 - the two cgif corollaries take DIface / DIfaceR at the instance's trace premise tr_admit (as_universe B) S tr and give DeallocGcgif's contracts at FS_U (In tr (as_universe B) \/ st_nev S < EV_MAX), bridging dealloc_pre with DeallocGcgif.dealloc_pre_admit. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The frame-generic Deallocate contract from the four arms, in both forms, and its cgif_file corollaries.

   DeallocG.adealloc_realizes frames the memory on the view ([aview]), as the released callee contracts state it;
   DeallocG.adealloc_realizes_raw frames the raw bytes as well.  The NULL and the "last batch has room" arms prove
   the raw frame outright (no callee with an aview-only post is crossed).  The two arms that call
   QuarantineCache::Enqueue (and, on the drain path, Quarantine::Drain) prove whichever form their contracts give:
   they are parametric in [rawb], with DGif0.DIface giving the [false] contracts and DIfaceR.DIfaceR the [true]
   ones (DIfaceR.enq_spec_b_false / _true, drain_spec_b_false / _true).

   Ported from cgif_file's released free top (YFfs.afree_realizes_of, YFfs.v:36-62): the same case split (NULL;
   then on the thread quarantine cache, the arm whose last batch has room, the new-batch arm, the drain arm), with
   the caller's frame made abstract and the callee contracts taken from the interfaces.  The arms are DGg3
   (dealloc_null_arm), DGfy (dealloc_common, its seed record from DGfu.FH_c), DGg2 (dealloc_mid) and DGfz
   (dealloc_drn).  The bound on the last batch's item count, which the released top reads from Wf, comes from the
   interface's view (DGif0.db_slots). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DeallocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import DeallocGcgif DGbase DGgi.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DGif0 DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import DGfu DGfy DGg1 DGg2 DGg3 DGfz.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require ErrnoG ErrnoApart DGleafE.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBase ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.
Local Open Scope am_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variables (ARX ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop).
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world tfibsegs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Hypothesis IF : DIface B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq.

(* The four arms, at whichever form the Enqueue / Drain contracts give. *)
Lemma realizes_b : forall rawb : bool,
enq_spec_b B U ARX AOX rpre lpost fpre dpost L24 QB rawb ->
drain_spec_b B ARX AOX dbody L24 QB rawb ->
forall inst so bp ly S W regs mem md p n tr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x31be0 regs mem md)
(dealloc_leaf_b B ft ARX AOX lpost rawb inst ly S W regs mem md p n tr).
Proof.
intros rawb ENQb DRNb inst so bp ly S W regs mem md p n tr PRE0.
pose proof PRE0 as PRE1.
destruct PRE1 as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
destruct Hp0 as [HN|HBLK].
{ eapply amreal_mono; [| exact (DGg3.dealloc_null_arm B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF
    inst so bp ly S W regs mem md p n tr PRE0 HN)].
  intros r W' c' H. exact (leaf_raw_b B ft ARX AOX lpost rawb inst ly S W regs mem md p n tr r W' c' H). }
destruct (Z_le_gt_dec (qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0)) kQuarantineCacheMax) as [ND|DR].
2:{ exact (DGfz.dealloc_drn B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq rawb IF ENQb DRNb
    inst so bp ly S W regs mem md p n tr PRE0 HBLK ltac:(lia)). }
destruct (need_new_batch (st_qthread S)) eqn:NB.
- exact (DGg2.dealloc_mid B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq rawb IF ENQb
    inst so bp ly S W regs mem md p n tr PRE0 HBLK NB ltac:(rewrite NB; exact ND)).
- pose proof (di_view B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF inst ly S W mem md p n HARX HRP HFP HBLK) as DV.
  assert (ER : exists lastb initr, rev (qc_list (st_qthread S)) = lastb :: initr).
  { revert NB. unfold need_new_batch. destruct (rev (qc_list (st_qthread S))) as [|lastb initr] eqn:E; [discriminate|].
    intros _. exists lastb, initr. reflexivity. }
  destruct ER as (lastb & initr & ER).
  assert (BL : Z.of_nat (length (b_items lastb)) < kBatchSlots).
  { pose proof (db_slots W ly mem (st_qthread S) lastb (sptr_addr B ly p) (req_size n) (dv_batch B W ly inst mem S p n DV lastb initr ER)) as HS.
    unfold DGgiC.BCv in HS. revert NB. unfold need_new_batch. rewrite ER. intros NB'. apply Z.eqb_neq in NB'. lia. }
  rewrite Z.add_0_r in ND.
  eapply amreal_mono; [| exact (DGfy.dealloc_common B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF (DGfu.FH_c B TS)
    inst so bp ly S W regs mem md p n tr lastb initr PRE0 HBLK ER BL ND)].
  intros r W' c' H. exact (leaf_raw_b B ft ARX AOX lpost rawb inst ly S W regs mem md p n tr r W' c' H).
Qed.

(* The contract with the frame on the view (the interface DIface alone). *)
Theorem adealloc_realizes_g : DeallocG.adealloc_realizes tfibsegs B U ft ARX AOX rpre lpost fpre 0x31be0 1.
Proof.
unfold DeallocG.adealloc_realizes. intros inst so bp ly S W regs mem md p n tr PRE0.
eapply amreal_mono; [| exact (realizes_b false
  (enq_spec_b_false B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF)
  (drain_spec_b_false B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF)
  inst so bp ly S W regs mem md p n tr PRE0)].
intros r W' c' H. exact (leaf_b_aview B ft ARX AOX lpost false inst ly S W regs mem md p n tr r W' c' H).
Qed.

(* The contract with the frame on the raw memory as well (DIface and DIfaceR). *)
Hypothesis IR : DIfaceR B U ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq.

Theorem adealloc_realizes_raw_g : DeallocG.adealloc_realizes_raw tfibsegs B U ft ARX AOX rpre lpost fpre 0x31be0 1.
Proof.
unfold DeallocG.adealloc_realizes_raw. intros inst so bp ly S W regs mem md p n tr PRE0.
eapply amreal_mono; [| exact (realizes_b true
  (enq_spec_b_true B U ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IR)
  (drain_spec_b_true B U ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IR)
  inst so bp ly S W regs mem md p n tr PRE0)].
intros r W' c' H. exact (leaf_b_raw B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c' H).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The errno-kept twins.  The NULL and the "last batch has room" arms keep errno outright (they cross no callee with
   a memory frame), so they give DGleafE.dealloc_leaf_raw_ee at either form; the two arms that call Enqueue (and, on
   the drain path, Drain) keep it at whichever form those contracts give, as they do for the raw frame.
   The four image facts are a Theorem Labs lane's ErrnoApart Props, which the two calling arms take: errno-apart is stated
   once per image and discharged once per image (a Theorem Labs lane, 12:40Z), so they pass through to the corollaries. *)
Hypothesis EAimg : ErrnoApart.errno_in_img.
Hypothesis EAz3 : ErrnoApart.errno_apart_zone3_d.
Hypothesis EAdz : ErrnoApart.errno_apart_dzone_d.
Hypothesis EAiz : ErrnoApart.errno_apart_izone.

Lemma realizes_b_e : forall rawb : bool,
DGleafE.enq_spec_b_e B U ARX AOX rpre lpost fpre dpost L24 QB rawb ->
DGleafE.drain_spec_b_e B ARX AOX dbody L24 QB rawb ->
forall inst so bp ly S W regs mem md p n tr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x31be0 regs mem md)
(DGleafE.dealloc_leaf_b_e B ft ARX AOX lpost rawb inst ly S W regs mem md p n tr).
Proof.
intros rawb ENQe DRNe inst so bp ly S W regs mem md p n tr PRE0.
pose proof PRE0 as PRE1.
destruct PRE1 as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
destruct Hp0 as [HN|HBLK].
{ eapply amreal_mono; [| exact (DGg3.dealloc_null_arm_e B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF
    inst so bp ly S W regs mem md p n tr PRE0 HN)].
  intros r W' c' H. exact (DGleafE.leaf_raw_ee_b_e B ft ARX AOX lpost rawb inst ly S W regs mem md p n tr r W' c' H). }
destruct (Z_le_gt_dec (qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0)) kQuarantineCacheMax) as [ND|DR].
2:{ exact (DGfz.dealloc_drn_e B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq rawb IF ENQe DRNe
    EAimg EAz3 EAdz EAiz inst so bp ly S W regs mem md p n tr PRE0 HBLK ltac:(lia)). }
destruct (need_new_batch (st_qthread S)) eqn:NB.
- exact (DGg2.dealloc_mid_e B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq rawb IF ENQe
    EAimg EAz3 EAdz EAiz inst so bp ly S W regs mem md p n tr PRE0 HBLK NB ltac:(rewrite NB; exact ND)).
- pose proof (di_view B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF inst ly S W mem md p n HARX HRP HFP HBLK) as DV.
  assert (ER : exists lastb initr, rev (qc_list (st_qthread S)) = lastb :: initr).
  { revert NB. unfold need_new_batch. destruct (rev (qc_list (st_qthread S))) as [|lastb initr] eqn:E; [discriminate|].
    intros _. exists lastb, initr. reflexivity. }
  destruct ER as (lastb & initr & ER).
  assert (BL : Z.of_nat (length (b_items lastb)) < kBatchSlots).
  { pose proof (db_slots W ly mem (st_qthread S) lastb (sptr_addr B ly p) (req_size n) (dv_batch B W ly inst mem S p n DV lastb initr ER)) as HS.
    unfold DGgiC.BCv in HS. revert NB. unfold need_new_batch. rewrite ER. intros NB'. apply Z.eqb_neq in NB'. lia. }
  rewrite Z.add_0_r in ND.
  eapply amreal_mono; [| exact (DGfy.dealloc_common_e B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF TS (DGfu.FH_c B TS)
    inst so bp ly S W regs mem md p n tr lastb initr PRE0 HBLK ER BL ND)].
  intros r W' c' H. exact (DGleafE.leaf_raw_ee_b_e B ft ARX AOX lpost rawb inst ly S W regs mem md p n tr r W' c' H).
Qed.

(* The errno-kept contract with the frame on the view (ErrnoG's DIfaceE: the add-ons an instance with DIface alone
   can give, which is what the closed cgif Deallocate top has). *)
Hypothesis IE : ErrnoG.DIfaceE B U ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq.

Theorem adealloc_realizes_e_g : ErrnoG.adealloc_realizes_e tfibsegs B U ft ARX AOX rpre lpost fpre 0x31be0 1.
Proof.
unfold ErrnoG.adealloc_realizes_e. intros inst so bp ly S W regs mem md p n tr PRE0.
eapply amreal_mono; [| exact (realizes_b_e false
  (DGleafE.enq_spec_b_e_false B U ARX AOX rpre lpost fpre dpost L24 QB (ErrnoG.de_enqueue_v _ _ _ _ _ _ _ _ _ _ _ _ _ IE))
  (DGleafE.drain_spec_b_e_false B ARX AOX dbody L24 QB (ErrnoG.de_drain_v _ _ _ _ _ _ _ _ _ _ _ _ _ IE))
  inst so bp ly S W regs mem md p n tr PRE0)].
intros r W' c' H. exact (DGleafE.leaf_b_e_view B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c' H).
Qed.

(* The errno-kept contract with the frame on the raw memory as well (ErrnoG's DIfaceRE). *)
Hypothesis IRE : ErrnoG.DIfaceRE B U ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq.

Theorem adealloc_realizes_raw_e_g : ErrnoG.adealloc_realizes_raw_e tfibsegs B U ft ARX AOX rpre lpost fpre 0x31be0 1.
Proof.
unfold ErrnoG.adealloc_realizes_raw_e. intros inst so bp ly S W regs mem md p n tr PRE0.
eapply amreal_mono; [| exact (realizes_b_e true
  (DGleafE.enq_spec_b_e_true B U ARX AOX rpre lpost fpre dpost L24 QB (ErrnoG.de_enqueue _ _ _ _ _ _ _ _ _ _ _ _ _ IRE))
  (DGleafE.drain_spec_b_e_true B ARX AOX dbody L24 QB (ErrnoG.de_drain _ _ _ _ _ _ _ _ _ _ _ _ _ IRE))
  inst so bp ly S W regs mem md p n tr PRE0)].
intros r W' c' H. exact (DGleafE.leaf_b_e_raw B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c' H).
Qed.
End b.

(* The cgif_file corollaries: the generic contracts at cgif's image, model and predicates. *)
Theorem adealloc_realizes_cgif_of : forall B, TfibSyms B ->
forall ARXr dpost dbody L24 QB DRq,
DIface B (fun tr S => tr_admit (as_universe B) S tr) free (ARX_cgif B) ARXr (aowned B) rpre_dealloc_cgif qtight fpre_cgif
  dpost dbody L24 QB DRq ->
adealloc_realizes_cgif B.
Proof.
intros B TS ARXr dpost dbody L24 QB DRq IF. unfold adealloc_realizes_cgif, adealloc_realizes.
intros inst so bp ly S W regs mem md p n tr PRE.
exact (adealloc_realizes_g B TS (fun tr S => tr_admit (as_universe B) S tr) free (ARX_cgif B) ARXr (aowned B)
  rpre_dealloc_cgif qtight fpre_cgif dpost dbody L24 QB DRq IF inst so bp ly S W regs mem md p n tr
  (dealloc_pre_admit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE)).
Qed.

Theorem adealloc_realizes_cgif_raw_of : forall B, TfibSyms B ->
forall ARXr dpost dbody L24 QB DRq,
DIface B (fun tr S => tr_admit (as_universe B) S tr) free (ARX_cgif B) ARXr (aowned B) rpre_dealloc_cgif qtight fpre_cgif
  dpost dbody L24 QB DRq ->
DIfaceR B (fun tr S => tr_admit (as_universe B) S tr) (ARX_cgif B) ARXr (aowned B) rpre_dealloc_cgif qtight fpre_cgif
  dpost dbody L24 QB DRq ->
adealloc_realizes_cgif_raw B.
Proof.
intros B TS ARXr dpost dbody L24 QB DRq IF IR. unfold adealloc_realizes_cgif_raw, adealloc_realizes_raw.
intros inst so bp ly S W regs mem md p n tr PRE.
exact (adealloc_realizes_raw_g B TS (fun tr S => tr_admit (as_universe B) S tr) free (ARX_cgif B) ARXr (aowned B)
  rpre_dealloc_cgif qtight fpre_cgif dpost dbody L24 QB DRq IF IR inst so bp ly S W regs mem md p n tr
  (dealloc_pre_admit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE)).
Qed.
End a.
