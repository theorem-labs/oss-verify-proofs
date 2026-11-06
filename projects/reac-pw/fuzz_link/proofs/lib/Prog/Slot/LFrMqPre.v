(* The slot LLVMFuzzerTestOneInput (fuzz_link.c:764-790), plain image: the mark_quietly step's Pre from the frame
   relation LFR at the call (lib/Prog/Slot/LFrMq.v puts them together).
   - lmq_sink_lfr: the FILE the call finds (LFrMqDefs.lmq_sink), from LFR's mf_gi and lkept;
   - lmq_pre_frame: the callee's stack window (frame_apart_gnl, below TASK_SIZE, above the image);
   - lmq_pre_sink: every FILE / stdio conjunct of the Pre: g_sink; the open FILE (memfile_k: mf_gi's
     memfile_at and its window, the block and g_said writable, mf_place_ok), g_say and the list head; or, on
     the first mark, stdio_ok (closed_stdio_env, carried from the entry, and the allocator's libc + 3 byte),
     ofl_empty, guard_ok and g_said writable. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YH02 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memfile_c reac_served_mark_c mark_quietly_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require StdioModel memfile_place.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LFrCall LFrEn LFrRun LFrPo.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LFrMqDefs LFrMqLib.
Import ListNotations.
Local Open Scope Z_scope.

Section MQP.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

Lemma lmq_sink_lfr : forall g hb T L A mem md, LFR B API g hb T L A mem md -> exists sink, lmq_sink B g hb T sink.
Proof.
  intros g hb T L A mem md HF.
  pose proof HF as (HGV & HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & HKT & HGI).
  destruct HGI as [(H0 & ->) | (f & Hf & -> & Hm)].
  - exists 0. left. split; reflexivity.
  - exists f. right. split; [reflexivity|].
    assert (Hin : In (f, MF_BLOCK) (blocks L A))
      by (apply (lc_T_blk B API g hb _ L A mem md _ HF); left; reflexivity).
    destruct (lc_gv B API g HGV) as (HS & _ & HS47 & _).
    assert (HB : forall i, 0 <= i < MF_BLOCK -> 4096 <= f /\ f + MF_BLOCK <= YM05.alloc_ceiling /\ ~ in_img B (f + i)).
    { intros i Hi. destruct (lc_blk B API FF L A mem md f MF_BLOCK i HM Hin Hi) as (_ & H1 & H2 & _ & H5).
      split; [exact H1|]. split; [exact H2 | exact H5]. }
    destruct (HB 0 ltac:(unfold MF_BLOCK; lia)) as (H1 & H2 & _).
    split; [exact H1|]. split; [unfold SLOT_STACK in *; lia|].
    split.
    { apply memfile_place.mf_place_of_fresh; [exact H1|]. intros i Hi.
      apply (lmq_img_src0 B API FF). exact (proj2 (proj2 (HB i Hi))). }
    split; [intros i Hi; exact (proj2 (proj2 (HB i Hi)))|].
    pose proof (lc_pw B API L A mem md _ HM HP) as Hpw.
    assert (HinL : In (f, MF_BLOCK) (hb ++ blocks (lg_L g) (lg_A g))) by (apply (Permutation_in _ HP); exact Hin).
    assert (D : forall a k, In (a, k) (hb ++ blocks (lg_L g) (lg_A g)) -> (a, k) <> (f, MF_BLOCK) ->
      f + MF_BLOCK <= a \/ a + k <= f).
    { intros a k Hak Hne. destruct (lfr_pw_in2 ranges_disjoint _ (a, k) (f, MF_BLOCK) Hpw Hak HinL Hne) as [D|D];
        unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
    split; [intros a k Hak Hne; apply D; [apply in_or_app; left; exact Hak | exact Hne]|].
    split; [intros a k Hak Hne; apply D; [apply in_or_app; right; exact Hak | exact Hne]|].
    intros Hin0. destruct HKT as [(_ & HT) | (_ & [HT | (f' & HT & Hf')])].
    + symmetry. exact HT.
    + discriminate HT.
    + exfalso. injection HT as E. subst f'.
      pose proof (lc_hb_b0 B API L A mem md hb _ (f, MF_BLOCK) (f, MF_BLOCK) HM HP Hf' Hin0) as D'.
      unfold ranges_disjoint in D'. cbn [fst snd] in D'. unfold MF_BLOCK in D'. lia.
Qed.

Lemma lmq_pre_frame : forall g hb T L A mem md regs,
  LFR B API g hb T L A mem md -> spZ regs = lg_S g - SLOT_FRAME ->
  frame_apart_gnl regs MARK_QUIETLY_K /\ spZ regs <= TASK_SIZE /\ A_IMG_TOP <= spZ regs - MARK_QUIETLY_K.
Proof.
  intros g hb T L A mem md regs HF Hsp. destruct HF as (HGV & _).
  destruct (lc_gv B API g HGV) as (HS & _ & HS47 & _).
  pose proof (@lc_ceil rc) as [HC1 HC2].
  unfold frame_apart_gnl, apart_gnl. rewrite Hsp.
  unfold LF_TOP, SLOT_STACK, SLOT_FRAME, MARK_QUIETLY_K, A_G_NL, NK_SIZE, TASK_SIZE, A_IMG_TOP in *. lia.
Qed.

Lemma lmq_pre_sink : forall g hb T L A mem md regs sink,
  LFR B API g hb T L A mem md -> spZ regs = lg_S g - SLOT_FRAME -> lmq_sink B g hb T sink ->
  u64_at mem A_G_SINK sink /\
  (sink <> 0 -> In (sink, FILE_SIZE) (blocks L A)) /\
  (sink <> 0 ->
     (exists k, memfile_k mem sink k) /\ u64_at mem A_G_SAY sink /\ u64_at mem StdioModel.A_OFL_HEAD sink /\
     sink + link_mem.FILE_BLOCK <= spZ regs - MARK_QUIETLY_K) /\
  (sink = 0 ->
     StdioModel.stdio_ok mem /\ StdioModel.ofl_empty mem /\ StdioModel.guard_ok mem /\
     wr_at rsegs mem A_G_SAID SAID_SIZE).
Proof.
  intros g hb T L A mem md regs sink HF Hsp Hsink.
  pose proof FF as (SEG & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR & TP
    & EOFF & REP & VML & DBL & OFH & OFL & THR & CTXRO & ALLOC).
  pose proof HF as (HGV & HM & _ & _ & _ & _ & _ & Himg & _ & _ & _ & _ & HRO & HRS & HP & HKT & HGI).
  destruct (lc_gv B API g HGV) as (HS & _ & HS47 & _).
  pose proof (@lc_ceil rc) as [HC1 HC2]. unfold LF_TOP in HC1.
  assert (HH : forall v, mf_heads B link_mf mem v -> 0 <= v < 2 ^ 64 ->
    u64_at mem A_G_SINK v /\ u64_at mem A_G_SAY v /\ u64_at mem StdioModel.A_OFL_HEAD v).
  { intros v (W1 & W2 & W3) Hv. rewrite SEG in W1, W2, W3. rewrite OFH in W3.
    split; [|split].
    - apply (lmq_word_u64 mem A_G_SINK v Hv); [unfold A_G_SINK; lia | unfold A_G_SINK; lia | exact W1].
    - apply (lmq_word_u64 mem A_G_SAY v Hv); [unfold A_G_SAY; lia | unfold A_G_SAY; lia | exact W2].
    - apply (lmq_word_u64 mem StdioModel.A_OFL_HEAD v Hv);
        [unfold StdioModel.A_OFL_HEAD; lia | unfold StdioModel.A_OFL_HEAD; lia | exact W3]. }
  destruct Hsink as [(-> & ->) | (-> & K1 & K2 & K3 & K4 & K5 & K6 & K7)].
  - (* the first mark of the run: no FILE yet *)
    destruct HGI as [(H0 & _) | (f & _ & HT & _)]; [|discriminate HT].
    destruct (HH 0 H0 ltac:(lia)) as (S1 & _ & S3).
    split; [exact S1|]. split; [intros C; contradiction|]. split; [intros C; contradiction|].
    intros _.
    assert (HENV : closed_stdio_env B mem)
      by exact (lpo_env_keep B API FF (lg_mem g) mem Himg (proj1 (lgv_sink B API g HGV))).
    destruct HENV as [HT HL]. rewrite SEG, THR in HT. rewrite SEG, OFL in HL.
    split; [|split; [|split]].
    + split; [|split].
      * apply lmq_byte1; [unfold StdioModel.A_LIBC; lia|].
        pose proof (HT 0%nat ltac:(lia)) as E. rewrite lmq_le_byte0 in E.
        replace (0x95898 + 1 + Z.of_nat 0) with (StdioModel.A_LIBC + 1) in E by (unfold StdioModel.A_LIBC; lia).
        exact E.
      * apply lmq_byte1; [unfold StdioModel.A_LIBC; lia|].
        destruct (ax_statics (lc_ax B API FF) L A mem md HM) as (_ & _ & E). rewrite SEG, LIBC in E. exact E.
      * replace (le4 (StdioModel.wz 0)) with (repeat (Z_to_bv 8 0) 4) by (symmetry; exact lmq_le4_0).
        apply lmq_val0_bytes;
          [unfold StdioModel.A_OFL_LOCK; lia | unfold StdioModel.A_OFL_LOCK; lia | exact HL].
    + unfold StdioModel.ofl_empty, rw_cells, cells_at. split; [split; [cbn; tauto|]|].
      * cbn [cells_bytes cbytes]. rewrite app_nil_r. exact S3.
      * exact (lmq_ofl_wr mem).
    + destruct (ax_statics (lc_ax B API FF) L A mem md HM) as (GG1 & (gv & Hgv & GG2) & _).
      rewrite SEG, (lff_got B API FF), (lff_guard B API FF) in GG1. rewrite SEG, (lff_guard B API FF) in GG2.
      split.
      * apply (KindBGlue.word_mem_le8 rsegs); [exact GG1 | ..];
          unfold StdioModel.A_GUARD, StdioModel.A_GOT_GUARD; lia.
      * exists (Z_to_bv 64 gv). apply (KindBGlue.word_mem_le8 rsegs); [exact GG2 | exact Hgv | ..];
          unfold StdioModel.A_GUARD; lia.
    + exact (lmq_said_wr mem).
  - (* the FILE kept from an earlier mark *)
    destruct HGI as [(_ & HT) | (f & Hf & HT & Hm)]; [discriminate HT|].
    injection HT as <-.
    assert (Hin : In (sink, MF_BLOCK) (blocks L A))
      by (apply (lc_T_blk B API g hb _ L A mem md _ HF); left; reflexivity).
    destruct (lc_blk B API FF L A mem md sink MF_BLOCK 0 HM Hin ltac:(unfold MF_BLOCK; lia)) as (_ & B1 & B2 & _).
    destruct (HH sink Hf ltac:(unfold MF_BLOCK in *; lia)) as (S1 & S2 & S3).
    split; [exact S1|].
    split; [intros _; exact Hin|].
    split; [|intros C; lia].
    intros _. split; [|split; [exact S2 | split; [exact S3|]]].
    + pose proof Hm as (Hf0 & Hf1 & Hf2 & Hst & Hfl & Hom & (Hw8 & Hw16 & Hw) & Hck).
      destruct (lc_fa B API FF YK11.fx0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBW & _).
      assert (W : wr_at rsegs mem sink MF_BLOCK).
      { split; [lia|]. split; [unfold MF_BLOCK in *; lia|]. intros i Hi.
        pose proof (HBW L A mem md sink MF_BLOCK i HM Hin Hi) as W. rewrite SEG in W. exact W. }
      rewrite SEG in Hw.
      destruct Hw as [(W1 & W2 & W3) | (k & Hk & W1 & W2 & W3)].
      * exists 0. split; [exact (lmq_mfat_src0 B API FF mem sink Hm)|].
        split; [left; split; [reflexivity|]; split; [exact W1|]; split; [exact W2 | exact W3]|].
        split; [exact W | split; [exact (lmq_said_wr mem) | exact K3]].
      * exists k. split; [exact (lmq_mfat_src0 B API FF mem sink Hm)|].
        split; [right; split; [exact Hk|]; split; [exact W1|]; split; [exact W2 | exact W3]|].
        split; [exact W | split; [exact (lmq_said_wr mem) | exact K3]].
    + rewrite Hsp. unfold link_mem.FILE_BLOCK, MF_BLOCK, MARK_QUIETLY_K, SLOT_STACK, SLOT_FRAME in *. lia.
Qed.

End MQP.
