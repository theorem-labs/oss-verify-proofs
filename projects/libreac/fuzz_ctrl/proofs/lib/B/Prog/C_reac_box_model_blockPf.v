(* reac_box_model_block (image B, asan-ubsan, libreac v1.9.0): the pieces of pb_reac_box_model_block, the proof of
   treac_box_model_block_spec (lib/B/Prog/C_reac_box_model_block.v), a Theorem Labs lane.  Each piece is a Qed lemma
   of its own; the composition follows the plan of record pb_reac_box_model_block.plan.md section "The composition" (a working note, not in this delivery):
     A  the stretch from the entry 0x865d8 to the class-0 request (jal 0x86644): mbB_SA_run, lifted by mbB_SA;
     E  the class-0 request (YCbq.aj_stack_malloc_at 0);
     B  the stretch from the return 0x86648 to ret: mb_post_rebaseRB (lib/B/Prog/C_reac_box_model_blockRBLib.v),
        lifted by GlueLift.rrB_lift.
   The lift is a Theorem Labs lane's shared rrB_lift (lib/B/Prog/GlueLift.v, a working branch
   b9b1631c5b8 / 7c18eb11bbd), used as is, with its wx premise discharged by ProgBridgeData.rsegs_wx_nowrap (a Theorem Labs lane,
   a working branch 9f8ab5fbe2f).


   rule 24: no function proved (the re-base and lift of the proved run reac_box_model_block_holds_F). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcParseLib RcKindLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c dt1_head_c name_field_c reac_box_model_block_c
  reac_box_model_block reac_box_model_blockF reac_box_model_block_holdsF C_reac_box_model_blockLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YK0s YK1b YA0n YA0o YM05 YI16 YG00 YG01 YG0f YG0d YG0n YG0v YP09 YCbq YCbqMalloc.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr ProgBridge ProgBridgeData.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require GlueLift.
Import ListNotations.
Open Scope Z_scope.

(* ---- A: the entry to the class-0 request --------------------------------------------------------------------- *)

(* Stretch A's run on the normalized caller memory: mb_preF at m := B.MemNorm.normalize rsegs memc, with its
   continuation closed at the call state.  The premises are single-memory facts at the REAL memory memc (the spec's
   journal gives them through AR: stk / asan_cells by ctlrt_of_AR, fp by ctl_fp_of_AR; the footprint by
   rng_of_visible), each moved to the normalized memory by image B's MemNormTr. *)
Lemma mbB_SA_run : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (memc : word -> option byte) (p b o FS A : Z) (row nb : list byte) (RNG : footprint)
    (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    B.MemNorm.ro_agree rsegs memc ->
    A = (bv_unsigned sp - 160) / 32 * 32 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs memc (bv_unsigned sp - 4272) (bv_unsigned sp) ->
    asan_cells memc ->
    HIGHMEM_BEG <= bv_unsigned sp - 4272 -> bv_unsigned sp <= APPMEM_END ->
    fp [0%nat] memc (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
      (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) ->
    mbF_rng RNG (B.MemNorm.normalize rsegs memc) sp tp p b o FS row nb ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 : word -> option byte,
         mb_pre_facts ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 (B.MemNorm.normalize rsegs memc) m1 /\
         ms' = mb_call_state sp gp tp s2 s5 s7 s8 s10 s11 F fc p b o ASAN_K A t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 b) (Z_to_bv 64 o) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None (B.MemNorm.normalize rsegs memc) (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc memc p b o FS A row nb RNG
    t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 RO HA HS16 ST0 AC0 HHM HAE FP0 HRNG.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
  (* stk_normalize_ro's guard, as its own fact: the window from HIGHMEM_BEG <= sp - 4272 *)
  assert (GW : ImgBounds.IMG_HI <= bv_unsigned sp - 4272) by (unfold ImgBounds.IMG_HI; lia).
  apply (mb_preF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (B.MemNorm.normalize rsegs memc) p b o FS ASAN_K
           A row nb RNG eq_refl HA HS16 (MemNormTr.stk_normalize_ro _ _ _ RO GW ST0)
           (B.MemNorm.mem_inv_normalize rsegs memc) (MemNormTr.asan_cells_normalize _ RO AC0) HHM HAE
           (MemNormTr.fp_normalize _ _ _ _ _ _ _ _ RO FP0) HRNG
           t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 _ _ eq_refl).
  intros m1 PF. apply evtF_done. exists m1. split; [exact PF | reflexivity].
Qed.

(* Stretch A lifted to the world (rrB_lift, the shared lift pattern). *)
Lemma mbB_SA : forall (W : lib.Reusable.YA0n.world rsegs) (md : Model)
    (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (memc : word -> option byte) (p b o FS A : Z) (row nb : list byte)
    (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    B.MemNorm.ro_agree rsegs memc ->
    A = (bv_unsigned sp - 160) / 32 * 32 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs memc (bv_unsigned sp - 4272) (bv_unsigned sp) ->
    asan_cells memc ->
    HIGHMEM_BEG <= bv_unsigned sp - 4272 -> bv_unsigned sp <= APPMEM_END ->
    fp [0%nat] memc (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
      (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) ->
    mbF_rng (ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (B.MemNorm.normalize rsegs memc) sp tp p b o FS row nb ->
    (forall ms' md',
       (exists s0', (exists m1 : word -> option byte,
                       mb_pre_facts ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 (B.MemNorm.normalize rsegs memc) m1 /\
                       s0' = mb_call_state sp gp tp s2 s5 s7 s8 s10 s11 F fc p b o ASAN_K A
                               t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1) /\
                    B.MemNorm.ms_rel rsegs ms' s0' /\ B.MemNorm.ro_same rsegs memc (ms_mem ms')) ->
       (forall x : word, lib.Reusable.YA0n.w_H W x = true -> ms_mem ms' x = memc x) ->
       lib.Reusable.YK04.same_but_materialized md md' -> lib.Reusable.YA0n.SRr rsegs W (mkCfg ms' md') Q) ->
    lib.Reusable.YA0n.SRr rsegs W
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 b) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None memc (seg_rom rsegs)) md) Q.
Proof.
  intros W md Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc memc p b o FS A row nb
    t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 RO HA HS16 ST0 AC0 HHM HAE FP0 HRNG K.
  exact (GlueLift.rrB_lift ProgBridgeData.rsegs_wx_nowrap W md _ _ _ _ _ memc _ _ Q RO
           (mbB_SA_run ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc memc p b o FS A row nb
              (ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6
              RO HA HS16 ST0 AC0 HHM HAE FP0 HRNG) K).
Qed.


(* ---- The journal across stretch A: it writes only the function's own window [sp - 4272, sp) (mb_pre_facts' munch),
   so a Theorem Labs lane's generic rrB_journal_win applies with lo := sp - 4272, hi := sp.  The window is readable at the run's
   end memory: stk over [sp - 4272, sp - 160) and [sp - 160, sp - 88) (mb_pre_facts), and the saved registers'
   cells at [sp - 88, sp) (stk_of_rw_cells). ---- *)
Section JournalA.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
(* YCbq's Section a0 premises for B's bundle (as rrB_journal_win takes them).  segs_low: core, PENDING THE RECORD CORE
   (YCeg.v:25 refused name); its statement is Reusable.YCeg.tfib_segs_low (YCeg.v:64). *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
Hypothesis segs_low : forall a, lib.Reusable.YG0d.in_img rsegs a -> 0 <= a < lib.Reusable.YG0f.kLowMemEnd.

Lemma mbB_journal_A :
  forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc (W : lib.Reusable.YA0n.world rsegs)
         memc mdc k (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (m1 : word -> option byte) (ms' s0' : machine_state) mdc',
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ->
    sp0 - STK <= bv_unsigned sp - 4272 -> bv_unsigned sp <= sp0 -> HIGHMEM_BEG <= bv_unsigned sp - 4272 ->
    mb_pre_facts ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 (B.MemNorm.normalize rsegs memc) m1 ->
    ms_mem s0' = m1 -> B.MemNorm.ms_rel rsegs ms' s0' -> B.MemNorm.ro_same rsegs memc (ms_mem ms') ->
    (forall x : word, lib.Reusable.YA0n.w_H W x = true -> ms_mem ms' x = memc x) ->
    lib.Reusable.YK04.same_but_materialized mdc mdc' ->
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W (ms_mem ms') mdc' k.
Proof using LAWS segs_low.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m1 ms' s0' mdc'
    HJ Hlo Hhi HHM PF Em1 REL ROS Hhid Hsame.
  destruct PF as (MU & _ & _ & _ & FR & STa & STb).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
  pose proof (stk_of_rw_cells rsegs m1 _ _ FR) as STc. cbn [cells_size csize Nat.add Z.of_nat] in STc.
  apply (GlueLift.rrB_journal_win B LAWS segs_low STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W
           memc mdc k (ms_mem ms') m1 mdc' (bv_unsigned sp - 4272) (bv_unsigned sp) HJ Hlo Hhi
           ltac:(unfold ImgBounds.IMG_HI; lia) ltac:(lia) MU).
  - intros a Ha.
    destruct (Z_lt_le_dec a (bv_unsigned sp - 160)) as [L|L];
      [destruct STa as (_ & _ & H); exact (proj2 (H a ltac:(lia)))|].
    destruct (Z_lt_le_dec a (bv_unsigned sp + -88)) as [L2|L2];
      [destruct STb as (_ & _ & H); exact (proj2 (H a ltac:(lia)))|].
    destruct STc as (_ & _ & H). exact (proj2 (H a ltac:(lia))).
  - destruct REL as (_ & _ & _ & _ & _ & _ & _ & R). rewrite Em1 in R. exact R.
  - exact ROS.
  - exact Hhid.
  - exact Hsame.
Qed.

(* S-A and the journal across it, to the class-0 request (the model_block twin of a Theorem Labs lane's rrB_to_E1): the lifted
   stretch A (mbB_SA), then mbB_journal_A at the run's end memory.  The continuation gets the end memories (real m1,
   normalized mc), mb_pre_facts at mc, their relation, and the journal at m1. *)
Lemma mbB_to_E0 :
  forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc (W : lib.Reusable.YA0n.world rsegs)
    memc mdc k (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p b o FS A : Z) (row nb : list byte) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ->
    sp0 - STK <= bv_unsigned sp - 4272 -> bv_unsigned sp <= sp0 ->
    B.MemNorm.ro_agree rsegs memc ->
    A = (bv_unsigned sp - 160) / 32 * 32 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs memc (bv_unsigned sp - 4272) (bv_unsigned sp) ->
    asan_cells memc ->
    HIGHMEM_BEG <= bv_unsigned sp - 4272 -> bv_unsigned sp <= APPMEM_END ->
    fp [0%nat] memc (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
      (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) ->
    mbF_rng (ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (B.MemNorm.normalize rsegs memc) sp tp p b o FS row nb ->
    (forall (m1 mc : word -> option byte) mdc1,
       mb_pre_facts ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 (B.MemNorm.normalize rsegs memc) mc ->
       B.MemNorm.mem_rel rsegs m1 mc -> B.MemNorm.ro_same rsegs memc m1 ->
       (forall x : word, lib.Reusable.YA0n.w_H W x = true -> m1 x = memc x) ->
       lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k ->
       lib.Reusable.YA0n.SRr rsegs W
         (mkCfg (mb_call_state sp gp tp s2 s5 s7 s8 s10 s11 F fc p b o ASAN_K A
                   t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1) mdc1) Q) ->
    lib.Reusable.YA0n.SRr rsegs W
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 b) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None memc (seg_rom rsegs)) mdc) Q.
Proof using LAWS segs_low.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    p b o FS A row nb t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q HJ Hlo Hhi RO HA HS16 ST0 AC0 HHM HAE FP0 HRNG K.
  apply (mbB_SA W mdc Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc memc p b o FS A row nb
           t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 RO HA HS16 ST0 AC0 HHM HAE FP0 HRNG).
  intros ms' md' (s' & (mc & PF & Es') & HREL & HROS) Hhid Hsame.
  rewrite Es' in HREL. unfold mb_call_state in HREL.
  destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL) as [Ems HMR].
  rewrite Ems. unfold mb_call_state in K.
  apply (K (ms_mem ms') mc md' PF HMR HROS Hhid).
  exact (mbB_journal_A STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
           mc ms' (mb_call_state sp gp tp s2 s5 s7 s8 s10 s11 F fc p b o ASAN_K A t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mc)
           md' HJ Hlo Hhi HHM PF eq_refl HREL HROS Hhid Hsame).
Qed.
End JournalA.


(* ---- E: the class-0 fake-stack request, by the core's YCbqMalloc.aj_stack_malloc_at_fc at cid := 0 (a Theorem Labs lane
   08:11Z: aj_stack_malloc_at with ecall_pre, the frame condition and the presence clauses passed on), the shape of
   a Theorem Labs lane's rrB_E1 (class 1, C_reac_ctrl_identity_replyPf.v) at model_block's call state (mb_call_state: ra = 0x86648,
   sp = A, a0 = 64).  Section premises for B's bundle (each NAMED, with its owner):
     LAWS, segs_low, errno_low, ML   core (the TfibLib record; YCeg.v:25 refused name, pending the record core)
     SMP, ASM0                       a Theorem Labs lane's class-0 fake-stack rules, a working branch
     PC0                             the class-0 entry of B's code table is __asan_stack_malloc_0 (0x3d6f4); core, the
                                     TfibLib code table, same pending file. ---- *)
Section EventA.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
Hypothesis segs_low : forall a, lib.Reusable.YG0d.in_img rsegs a -> 0 <= a < lib.Reusable.YG0f.kLowMemEnd.
Hypothesis errno_low : lib.Reusable.YCbq.api_env rsegs B.
Hypothesis ML : lib.Reusable.YG0d.model_laws (lib.Reusable.YG0f.as_universe B).
Hypothesis SMP : lib.Reusable.YCbq.stack_malloc_progressP B.
Hypothesis ASM0 : lib.Reusable.YG0d.astack_malloc_realizes rsegs B 0.
Hypothesis PC0 : lib.Reusable.YG0f.pc_stack_malloc (lib.Reusable.YG0f.as_code B) 0 = 0x3d6f4.

Lemma mbB_E0 :
  forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc (W : lib.Reusable.YA0n.world rsegs)
    (m1 : word -> option byte) mdc1 k (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word)
    (p b o A : Z) (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k ->
    sp0 - STK <= bv_unsigned sp - 4272 -> bv_unsigned sp <= sp0 ->
    A = (bv_unsigned sp - 160) / 32 * 32 -> bv_unsigned sp mod 16 = 0 -> 4272 <= bv_unsigned sp ->
    gp = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_gp B) -> tp = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B) ->
    lib.Reusable.YG01.count_cid 0 (lib.Reusable.YG01.frames Sc) < lib.Reusable.YG00.fs_frames 0 ->
    (forall S2 regs2 mem2 md2 pos,
       lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((0, pos) :: own) lyc S2 W mem2 md2 k ->
       lib.Reusable.YG0d.aregs_preserved (mkR (Z_to_bv 64 0x86648) (Z_to_bv 64 A) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 64) (wa 693944)
              (sx32 (wa 1)) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 o) (Z_to_bv 64 p) s5 (Z_to_bv 64 b) s7 s8 (wa ASAN_K) s10 s11
              t3 t4 t5 t6) regs2 ->
       lib.Reusable.YK11.getr regs2 10 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.frame_addr lyc 0 pos) ->
       lib.Reusable.YG0d.ablocks B lyc S2 = lib.Reusable.YG0d.ablocks B lyc Sc ->
       lib.Reusable.YG01.frames S2 = (0, pos) :: lib.Reusable.YG01.frames Sc ->
       ~ In (0, pos) (lib.Reusable.YG01.frames Sc) ->
       lib.Reusable.YG00.st_nev S2 = lib.Reusable.YG00.st_nev Sc ->
       lib.Reusable.YG01.blocks_bytes S2 = lib.Reusable.YG01.blocks_bytes Sc ->
       lib.Reusable.YG0v.zero_shadow (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2)
         lib.Reusable.YG0f.SHADOW_OFF (lib.Reusable.YG0f.frame_addr lyc 0 pos) (lib.Reusable.YG00.fs_frame_bytes 0) ->
       lib.Reusable.YG0d.rdword (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2)
         (lib.Reusable.YG0f.frame_addr lyc 0 pos + lib.Reusable.YG00.fs_frame_bytes 0 - 8) =
         Some (lib.Reusable.YG0f.flag_addr lyc 0 pos) ->
       lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W m1 W mem2
         (sp0 + (A - sp0) - lib.Reusable.YG0d.ESTACK) (sp0 + (A - sp0)) (fun _ => False) ->
       (* aj_stack_malloc_at_fc's additions: ecall_pre at the call configuration and astack_malloc_realizes' post
          (YG0d.v:297-300), the premises B.ProgWorldAstack.ctl_fs_of_astack takes *)
       lib.Reusable.YG0d.ecall_pre rsegs B lyc Sc W (mkR (Z_to_bv 64 0x86648) (Z_to_bv 64 A) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 64) (wa 693944)
              (sx32 (wa 1)) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 o) (Z_to_bv 64 p) s5 (Z_to_bv 64 b) s7 s8 (wa ASAN_K) s10 s11
              t3 t4 t5 t6) m1 mdc1 ->
       (forall a, lib.Reusable.YG0f.frame_addr lyc 0 pos <= a <
                  lib.Reusable.YG0f.frame_addr lyc 0 pos + lib.Reusable.YG00.fs_frame_bytes 0 ->
                  lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem2 a) ->
       (forall a, 0 <= a < 2 ^ 64 -> ~ lib.Reusable.YG0n.aowned B lyc Sc a -> ~ lib.Reusable.YG0n.aowned B lyc S2 a ->
                  ~ (A - lib.Reusable.YG0d.ESTACK <= a < A) ->
                  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2 a =
                  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m1 a) ->
       (forall a, A - lib.Reusable.YG0d.ESTACK <= a < A -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem2 a) ->
       lib.Reusable.YA0n.SRr rsegs W
         (mkCfg (lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 0x86648) mem2 (lib.Reusable.YK11.seg_rom rsegs)) md2) Q) ->
    lib.Reusable.YA0n.SRr rsegs W
      (mkCfg (mb_call_state sp gp tp s2 s5 s7 s8 s10 s11 lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr p b o ASAN_K A
                t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1) mdc1) Q.
Proof using LAWS segs_low errno_low ML SMP ASM0 PC0.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11
    t3 t4 t5 t6 p b o A Q HJ Hlo Hhi HA S16 HSK Egp Etp Hcnt K.
  unfold mb_call_state.
  set (regsT := (mkR (Z_to_bv 64 0x86648) (Z_to_bv 64 A) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 64) (wa 693944)
              (sx32 (wa 1)) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 o) (Z_to_bv 64 p) s5 (Z_to_bv 64 b) s7 s8 (wa ASAN_K) s10 s11
              t3 t4 t5 t6)).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (HAb : A mod 32 = 0 /\ bv_unsigned sp - 176 <= A <= bv_unsigned sp - 160)
    by (rewrite HA; Z.div_mod_to_equations; lia).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H16 & _) & _).
  assert (Hsp : lib.Reusable.YG0d.spZ regsT = sp0 + (A - sp0)).
  { unfold lib.Reusable.YG0d.spZ.
    change (lib.Reusable.YK11.getr regsT 2) with (Z_to_bv 64 A).
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_small by lia. lia. }
  assert (Hal : (A - sp0) mod 16 = 0) by (Z.div_mod_to_equations; lia).
  assert (Hraw : lib.Reusable.YK0s.ret_ok (Z_to_bv 64 0x86648)) by (unfold lib.Reusable.YK0s.ret_ok; vm_compute; reflexivity).
  change (Z_to_bv 64 0x3d6f4) with (Z_to_bv 64 0x3d6f4). rewrite <- PC0.
  eapply lib.Reusable.YA0n.SRr_bind.
  - exact (lib.Reusable.YCbqMalloc.aj_stack_malloc_at_fc rsegs B LAWS segs_low errno_low ML SMP 0 ASM0 ltac:(lia) W
             regsT m1 STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc mdc1 k (A - sp0) (Z_to_bv 64 0x86648) HJ Hsp Hal ltac:(lia)
             ltac:(unfold lib.Reusable.YG0d.ESTACK; lia) ltac:(subst gp; reflexivity) ltac:(subst tp; reflexivity)
             eq_refl Hraw Hcnt).
  - intros W2 c2 Hle (EW & S2 & regs2 & mem2 & md2 & pos & Ec & HJ2 & HP & H10 & HAB & HFR & HNI & HNEV & HBB & HZ &
      HFL & HKEPT & HPRE & HPRES & HFC & HWIN).
    subst W2 c2.
    rewrite Hsp in HFC, HWIN. replace (sp0 + (A - sp0)) with A in HFC, HWIN by lia.
    exact (K S2 regs2 mem2 md2 pos HJ2 HP H10 HAB HFR HNI HNEV HBB HZ HFL HKEPT HPRE HPRES HFC HWIN).
Qed.
End EventA.


(* rrB_journal_free (the journal across a stretch that frees one fake frame, generic in cid) moved UNCHANGED to
   lib/B/Prog/GlueLift.v Section JournalFree (a working branch d83cc3a1d97); use
   GlueLift.rrB_journal_free. *)

Print Assumptions mbB_SA.
Print Assumptions mbB_E0.
Print Assumptions mbB_journal_A.
