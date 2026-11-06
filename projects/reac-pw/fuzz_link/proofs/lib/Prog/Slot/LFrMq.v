(* The slot LLVMFuzzerTestOneInput (fuzz_link.c:764-790), plain image: the mark_quietly step at the SR level
   (S-FR item 6), lfr_mark. From a CUT at mark_quietly's entry 0x15d88 (the calls at 0x13dac, ra 0x13db0, and
   0x13c70, ra 0x13c74) to a CUT at ra with the memory FILE f kept ([(f, MF_BLOCK)]) and, when this driver call
   opened it, among the slot's heap blocks (LFrMqDefs.lmq_hb).
   The callee's contract is lib/Prog/mark_quietly_c.v mark_quietly_contract (with AMEND-slot items 9-14), a
   Section hypothesis over every FP state. The step supplies every FILE / stdio / allocator conjunct of its Pre
   from LFR (LFrMqPre.v), takes the rest from the arm's cut as LFrMqDefs.lmq_arm (over the cut's registers and
   view, moved to the config by LFrMqLib.v), and gives the arm the Post as LFrMqDefs.lmq_post with LFR at ra
   (LFrMqPost.v, over LFrCall.lfr_call_core). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memfile_c reac_served_mark_c mark_quietly_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require StdioModel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LFrCall LFrAl.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LFrMqDefs LFrMqLib LFrMqPre LFrMqPost.
Import ListNotations.
Local Open Scope Z_scope.

Section MQ.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.
Hypothesis MQ : forall fx' : YK11.FPState, @mark_quietly_contract fx' rc B API.

Lemma lfr_mark : forall g hb T ra (P : machine_state -> Prop) (P' : Z -> machine_state -> Prop) c,
  lroom_hb hb -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
  CUT B API g MARK_QUIETLY hb T P c ->
  (forall ms, P ms -> getr (ms_regs ms) 1 = Z_to_bv 64 ra /\
     getr (ms_regs ms) 2 = Z_to_bv 64 (lg_S g - SLOT_FRAME) /\ getr (ms_regs ms) 4 = Z_to_bv 64 A_TP) ->
  (forall ms sink, P ms -> lmq_sink B g hb T sink ->
     exists tab kbs nm, lmq_arm g hb (ms_regs ms) (ms_mem ms) sink tab kbs nm) ->
  (forall R F fc m sink tab kbs nm regs' F' fc' m' sink',
     P (MS R F (Z_to_bv 64 MARK_QUIETLY) fc None m (seg_rom rsegs)) -> lmq_sink B g hb T sink ->
     lmq_arm g hb R m sink tab kbs nm ->
     lmq_post B g hb T R m sink tab kbs nm regs' fc' m' sink' ->
     P' sink' (MS regs' F' (Z_to_bv 64 ra) fc' None m' (seg_rom rsegs))) ->
  SR (ms_segs B) c (fun c' => exists f, CUT B API g ra (lmq_hb T f hb) [(f, MF_BLOCK)] (P' f) c').
Proof.
  intros g hb T ra P P' c Hroom Hra Hra2 HCUT HPR HARM HK.
  pose proof (lff_segs B API FF) as SEG.
  apply (cut_open B API g MARK_QUIETLY hb T P c _ HCUT).
  intros fx' L A regs mem md Hfz HF Heqv.
  destruct (lc_rep P fx' regs MARK_QUIETLY mem Heqv) as (R & HPc & HR).
  destruct (HPR _ HPc) as (G1 & G2 & G4). cbn [ms_regs MState.MS] in G1, G2, G4.
  assert (R1 : YK11.getr regs 1 = Z_to_bv 64 ra) by (rewrite (lc_getr R regs 1 HR); exact G1).
  assert (R2 : YK11.getr regs 2 = Z_to_bv 64 (lg_S g - SLOT_FRAME)) by (rewrite (lc_getr R regs 2 HR); exact G2).
  assert (R4 : YK11.getr regs 4 = Z_to_bv 64 A_TP) by (rewrite (lc_getr R regs 4 HR); exact G4).
  assert (HK0 : 0 <= MARK_QUIETLY_K <= SLOT_STACK - SLOT_FRAME) by (unfold MARK_QUIETLY_K, SLOT_STACK, SLOT_FRAME; lia).
  destruct (la_pre B API FF g hb T L A regs mem md ra MARK_QUIETLY_K HF Hra Hra2 HK0 R1 R2 R4) as (HSP & PRE).
  pose proof HF as (HGV & HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & HRS & HP & _).
  assert (HROm : ro_agree rsegs mem) by (rewrite SEG in HRO; exact HRO).
  (* the FILE the call finds, and the arm's premises at it *)
  destruct (lmq_sink_lfr B API FF g hb T L A mem md HF) as (sink & Hsink).
  destruct (HARM _ sink HPc Hsink) as (tab & kbs & nm & Harm). cbn [ms_regs ms_mem MState.MS] in Harm.
  pose proof (lmq_arm_regs g hb R regs mem sink tab kbs nm HR (lmq_arm_back g hb R mem sink tab kbs nm HROm Harm))
    as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
  destruct (lmq_pre_frame B API g hb T L A mem md regs HF HSP) as (F1 & F2 & F3).
  destruct (lmq_pre_sink B API FF g hb T L A mem md regs sink HF HSP Hsink) as (S1 & S2 & S3 & S4).
  assert (HMB : bv_unsigned (getr regs 10) <> 0 ->
    exists q n, In (q, n) (blocks L A) /\ q <= bv_unsigned (getr regs 10) /\ bv_unsigned (getr regs 10) + MK_SIZE <= q + n).
  { intros H0. destruct (A11 H0) as (q & n & Hq & Q1 & Q2). exists q, n.
    split; [|split; [exact Q1 | exact Q2]].
    apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hq. }
  assert (HROOM : room_slots (sb_hb (lg_b g) hb) FILE_SIZE)
    by (apply (lroom B API g hb FILE_SIZE HGV Hroom); unfold FILE_SIZE; lia).
  pose proof (MQ fx' L A regs mem md (sb_hb (lg_b g) hb) tab kbs nm sink SEG PRE HRO A1 A2 A3 A4 F1 A5 A6 A7 A8
    S1 A9 A10 F2 HMB S2 A12 A13 A14 A15 F3 A16 S3 S4 Hfz HRS HROOM) as HSR.
  eapply SR_mono; [exact HSR|].
  intros c' (fx'' & L' & A' & regs' & mem' & md' & sink' & Ec & Hfz' & HPK & HRO' & HS1 & HS2 & HS3 & Hs0 & HMF
    & HNZ & HZ & HA0 & HA1).
  exists sink'.
  destruct (lmq_ret B API FF fx'' g hb T L A regs mem md R sink tab kbs nm L' A' regs' mem' md' sink'
    HF HSP HR Hsink Harm Hfz' HPK HRO' HS1 HS2 HS3 Hs0 HMF HNZ HZ HA0 HA1) as (HLF & HPOST).
  assert (R1' : getr regs 1 = Z_to_bv 64 ra) by exact R1.
  rewrite Ec, R1'.
  apply (cut_close B API fx'' g ra (lmq_hb T sink' hb) [(sink', MF_BLOCK)] (P' sink') L' A' regs' mem' md' Hfz' HLF).
  apply lc_eqv_self. unfold lcanon.
  exact (HK R (@fp_regs fx') (@fp_csr fx') (normalize_cj rsegs mem) sink tab kbs nm regs' (@fp_regs fx'')
    (@fp_csr fx'') (normalize_cj rsegs mem') sink' HPc Hsink Harm HPOST).
Qed.

(* the statement LFrMqDefs.v gives the glue *)
Lemma lfr_mark_ok : lfr_mark_stmt B API.
Proof. exact lfr_mark. Qed.

End MQ.

Print Assumptions lfr_mark.
Print Assumptions lfr_mark_ok.
