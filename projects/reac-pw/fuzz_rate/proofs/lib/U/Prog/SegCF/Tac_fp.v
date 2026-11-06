(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 457 of its 575 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/SegCF/Tac_slot.v, with its module paths changed; 103 of its 160 lines of code are new or changed and 518 lines of the source are left out. *)
(* Cut-free (agreement) copy of lib/U/Prog/Seg/Tac_fp.v, over U/Prog/SlotInvCF.v (SR := SRcf). Model:
   reac-pw/fuzz_role's U/Prog/SegCF/*.v copies (role has no Tac_fp), as libreac/fuzz_ctrl's released
   U/Prog/SegCF/*.v copy its U/Prog/Seg/*.v: the same text with SlotFR, SlotInv -> SlotInvCF, Seg -> SegCF, the
   segment statements from SegCF/StmtsCF.v, frame_facts_ubsan -> SlotInvCF.frame_facts_cf and the allocator
   contracts in their cut-free forms (frame_allocator_cf, malloc_contract_cfg, free_contract_cf).
   The text of the original follows. *)
(* Helpers of the segments of reac-pw/fuzz_rate LLVMFuzzerTestOneInput (UBSan) whose evt changes the FP state and
   writes one block of the live harness blocks hb (the plain file lib/Prog/Seg/Tac_fp.v, same text, plus sl_relro_cj): M02 (rate_check_contract: the copy into the pod block, the
   parse and pod_nearest write FP registers and accrue fflags) and M03 (rate_csv_contract: memset and the csv into
   the buf block, snprintf's post returns any fflags with rounding mode 0).
   Their callees (pod_nearest's soft-float routines, snprintf's printf chain) state their contracts over the CJ
   memory invariant, so the evt runs on MemNorm.normalize_cj of the cut's memory (which has MemNorm.task_mem by
   MemNorm.mem_inv_cj_normalize) rather than on MemNorm.normalize.
   - sl_cj_keep, sl_cj_hi, sl_stk_cj, sl_blk_cj, sl_run_fp_cj: reac-pw/fuzz_role's Prog/Seg/M02.v m02_cj_keep,
     m02_cj_hi, m02_stk_cj, m02_blk_cj, m02_run_cj (lines 37-129), renamed;
     sl_run_fp_cj is Tac_slot.sl_run_fp with normalize_cj, as libreac/fuzz_boxreg's released
     Prog/LLVMFuzzerTestOneInput_fr.v llvm_run_norm_cj (origin/ossv/recipes 25e3d17bdb50).
   - sl_mid_fp_blk (new): Tac_slot.sl_mid_fp on normalize_cj, with Tac_b1.b1_fr_hb in place of Tac_slot.sl_fr_run,
     so the run may write the stack window [S - K, S - 104) and one block (phi, n) of hb. It is the composition
     fuzz_role's seg_M02 does inline (M02.v:172-229: m02_run_cj, munch_rel_cj / wmono_rel_cj / ro_agree_same_cj,
     b1_fr_hb), stated once. No function is proved here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.SegCF Require Import Tac_slot Tac_b1.
Import ListNotations.
Open Scope Z_scope.

(* ---- The CJ normalization keeps every byte the segment reads ---- *)

(* A byte outside every image segment and below TASK_SIZE survives normalize_cj. *)
Lemma sl_cj_keep : forall (w : word), bv_unsigned w < TASK_SIZE ->
  find_segment rsegs (bv_unsigned w) 1 = None -> MemNorm.cj_drop rsegs w = false.
Proof.
  intros w Ht Hns. apply MemNorm.cj_drop_false_intro; [|right; exact Ht].
  unfold Mem.ro_addr. rewrite Hns. reflexivity.
Qed.

(* A byte above the image and below TASK_SIZE (the stack window) survives normalize_cj. *)
Lemma sl_cj_hi : forall (w : word), SL_TOP <= bv_unsigned w -> bv_unsigned w < TASK_SIZE ->
  MemNorm.cj_drop rsegs w = false.
Proof.
  intros w Hlo Ht. apply sl_cj_keep; [exact Ht|].
  destruct (find_segment rsegs (bv_unsigned w) 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (sl_find_top (bv_unsigned w) 1 seg E). unfold SL_TOP in *. lia.
Qed.

(* The stack region on the CJ-normalized memory (Tac_slot.sl_stk_norm with normalize_cj). *)
Lemma sl_stk_cj : forall m lo hi, ro_agree rsegs m -> SL_TOP <= lo -> hi <= TASK_SIZE ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) ->
  stk rsegs (MemNorm.normalize_cj rsegs m) lo hi.
Proof.
  intros m lo hi Hro Hlo Hhi H.
  assert (Htask : TASK_SIZE < 2 ^ 64) by (unfold TASK_SIZE; lia).
  apply sl_stk_of_writable; [exact Hlo | lia|].
  intros a Ha. unfold writable_at.
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply MState.unsigned_lit; unfold SL_TOP in *; lia).
  rewrite (MemNorm.wview_rel_cj rsegs m _ (Z_to_bv 64 a) (MemNorm.mem_rel_cj_normalize rsegs m Hro)
             (sl_cj_hi (Z_to_bv 64 a) ltac:(rewrite Hu; unfold SL_TOP in *; lia) ltac:(rewrite Hu; lia))).
  exact (H a Ha).
Qed.

Section R.
Context {fx : FPState}.

(* Tac_slot.sl_run_fp with MemNorm.normalize_cj: libreac/fuzz_boxreg's llvm_run_norm_cj. The configuration's FP
   state fx' is any (a cut's), and the continuation runs at the run's own FP state mkFP F fc. *)
Lemma sl_run_fp_cj : forall (fx' : FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (MemNorm.normalize_cj rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m', ms = MState.MS R F pc' fc None m' (seg_rom rsegs)) ->
  (forall R F pc' fc m0', Q (MState.MS R F pc' fc None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> MemNorm.mem_rel_cj rsegs m' m0' ->
     MemNorm.cj_same rsegs mem m' ->
     SR rsegs (mkCfg (@YK11.mkst (mkFP F fc) regs' pc' m' (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (@YK11.mkst fx' regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros fx' regs pc mem md Q P Hh Hl Hro HE Hform HK.
  apply (evt_SR_canon rsegs _ (fun s => exists s0, Q s0 /\ MemNorm.ms_rel_cj rsegs s s0 /\
                                          MemNorm.cj_same rsegs mem (ms_mem s)) md P);
    [| exact Hh | exact Hl |].
  - change (RegisterBridge.canonical_register_state (@YK11.mkst fx' regs pc mem (seg_rom rsegs)))
      with (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None mem (seg_rom rsegs)).
    apply MemNorm.evt_normalize_cj; [exact wx_apart_rsegs | exact Hro | exact HE].
  - intros ms' (can & (s0 & HQ & Hrel & Hsame) & Heq).
    destruct (Hform s0 HQ) as (R & F & pc' & fc & m0' & ->).
    destruct can as [cr cf cp cs cv cc cm co].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS] in *.
    subst cr cf cp cs cv cc co.
    destruct (sl_eqv_mkst R F pc' fc cm (seg_rom rsegs) ms' Heq) as [Ems Hx].
    rewrite Ems.
    exact (HK R F pc' fc m0' HQ _ cm Hx E8 Hsame).
Qed.

End R.

Section F.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_cf B APIf LS SH SK ra empty.

(* A live block's bytes on the CJ-normalized memory (Tac_b1.b1_blk with normalize_cj). *)
Lemma sl_blk_cj : forall L A mem md a n, aa_MR (APIf rc) L A mem md -> In (a, n) (blocks L A) ->
  stk rsegs (MemNorm.normalize_cj rsegs mem) a (a + n).
Proof.
  intros L A mem md a n HM Hin.
  pose proof Hin as Hin0. apply blocks_In in Hin0 as (p & Ep & Hp).
  destruct (mr_blocks_range B _ (aa_laws (APIf rc)) _ _ _ _ _ _ HM Hp) as [R1 R2]. rewrite Ep in R1, R2.
  pose proof alloc_ceiling_value as Hac.
  split; [lia|]. split; [lia|].
  intros x Hx.
  destruct (mr_blocks B _ (aa_laws (APIf rc)) L A mem md p n (x - a) HM Hp ltac:(lia)) as ([b Hb] & _).
  rewrite Ep in Hb. replace (a + (x - a)) with x in Hb by lia.
  pose proof (b1_blk_noseg B APIf ra empty FF L A mem md a n x HM Hin ltac:(lia)) as Hns.
  assert (Hcj : MemNorm.cj_drop rsegs (wa x) = false).
  { apply sl_cj_keep.
    - rewrite wa_unsigned by lia. unfold TASK_SIZE. lia.
    - rewrite wa_unsigned by lia. exact Hns. }
  assert (E : MemNorm.normalize_cj rsegs mem (wa x) = Some b)
    by (unfold MemNorm.normalize_cj; rewrite Hcj; exact Hb).
  split.
  - exact (YL01.present_writable rsegs _ x (ex_intro _ b E)).
  - exists b. unfold Mem.mrd. rewrite E. reflexivity.
Qed.

(* Tac_b8.b8_relro_norm with MemNorm.normalize_cj: frame_RELRO's first block (FrameAPI.v: (0x1ecb8, 448)) reads as
   the image on the CJ-normalized memory (refuse_code's absolute codes[] table 0x1edc0 lies in it); fuzz_role's
   U/Prog/Seg/M02.v m02_relro_cj with rate's block. *)
Lemma sl_relro_cj : forall mem a, relro B mem -> MI B mem -> 0x1ecb8 <= a < 0x1ecb8 + 448 ->
  mrd rsegs (MemNorm.normalize_cj rsegs mem) (wa a) = seg_rom rsegs (wa a).
Proof.
  intros mem a HR HMI Ha. unfold MI in HMI. rewrite (sl_segs B APIf ra empty FF) in HMI.
  rewrite (MemNorm.mrd_normalize_cj rsegs mem (wa a) HMI
             ltac:(right; right; rewrite wa_unsigned by lia; unfold TASK_SIZE; lia)).
  change (mrd rsegs mem (wa a)) with (mbyte rsegs mem a).
  unfold relro, G_img_c in HR. rewrite (sl_segs B APIf ra empty FF) in HR. apply HR.
  exists 0x1ecb8, 448. split; [left; reflexivity | lia].
Qed.

(* sl_mid_fp on the CJ-normalized memory for a run that writes the stack window [S - K, S - 104) and one block
   (phi, n) of hb, and ends with its own FP registers F' and fcsr fc' with rounding mode 0: FR at hb carries over
   (Tac_b1.b1_fr_hb), and the continuation runs at the FP state mkFP F' fc'. *)
Lemma sl_mid_fp_blk : forall (fx' : FPState) g hb phi n L A regs mem md pc (Q : machine_state -> Prop)
    (P : config -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (phi, n) hb ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (MemNorm.normalize_cj rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F' pc' fc' m', ms = MState.MS R F' pc' fc' None m' (seg_rom rsegs) /\
     frm_zero fc' /\
     (exists W, Frame.munch W (MemNorm.normalize_cj rsegs mem) m' /\
        Frame.wmono rsegs (MemNorm.normalize_cj rsegs mem) m' /\
        (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
           g_S g - SLOT_K <= x < g_S g - 104 \/ phi <= x < phi + n)) /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R F' pc' fc' m0' regs' m', Q (MState.MS R F' pc' fc' None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> MemNorm.mem_rel_cj rsegs m' m0' -> MemNorm.cj_same rsegs mem m' ->
     frm_zero fc' -> FR B APIf ra empty g hb L A regs' m' md ->
     SR (ms_segs B) (mkCfg (@YK11.mkst (mkFP F' fc') regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros fx' g hb phi n L A regs mem md pc Q P HFR HP Hin HE Hform HK.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  apply (sl_run_fp_cj fx' regs pc mem md Q P Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & F' & pc' & fc' & m' & -> & _).
    exists R, F', pc', fc', m'. reflexivity.
  - intros R F' pc' fc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & F1 & pc1 & fc1 & m1 & E & Hfrm & (W & MU & WM & HW) & E2 & E3 & E4).
    injection E; intros; subst.
    pose proof (MemNorm.mem_rel_cj_normalize rsegs mem HMI) as HR0.
    pose proof (MemNorm.munch_rel_cj rsegs W mem (MemNorm.normalize_cj rsegs mem) m' m1 HR0 Hrel Hsame MU) as MU'.
    pose proof (MemNorm.wmono_rel_cj rsegs mem (MemNorm.normalize_cj rsegs mem) m' m1 HR0 Hrel Hsame WM) as WM'.
    pose proof (MemNorm.ro_agree_same_cj rsegs mem m' HMI Hsame) as Hro'.
    rewrite <- SEGS. apply (HK R1 F1 pc1 fc1 m1 regs' m' HQ Hx Hrel Hsame Hfrm).
    apply (b1_fr_hb B APIf ra empty FF g hb phi n L A regs mem md regs' m' HFR HP Hin).
    + intros a Ha Hs Hb. apply MU'. rewrite MState.unsigned_lit by lia.
      destruct (sl_outside_dec W a) as [O|O]; [exact O|].
      exfalso. destruct (HW a Ha O) as [H|H]; [exact (Hs H) | exact (Hb H)].
    + exact WM'.
    + exact Hro'.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E2.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E3.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E4.
Qed.

End F.
