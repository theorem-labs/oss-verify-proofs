(* Cut-free (agreement) copy of lib/U/Prog/Seg/Tac_seg.v over U/Prog/SlotInvCF.v (SR := SRcf), as reac-pw/fuzz_pin's
   U/Prog/SegCF/*.v copy its U/Prog/Seg/*.v (commit a2a7540da98): the same text with
   SlotInvCF imported after SlotFR / SlotInv, Seg -> SegCF for the slot's tactic files, frame_facts_ubsan ->
   SlotInvCF.frame_facts_cf and the allocator contracts in their cut-free forms (frame_allocator_cf,
   malloc_contract_cfg, free_contract_cf, calloc_contract_cfg).
   The text of the original follows. *)
(* The evt body of a segment of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan) and its lift to the slot:
   - seg_W g Wb: a body's write set, the stack window below the saved registers [S - 65536, S - 104), longl's written
     bytes [LONGL, LONGL + LONGL_W) and the blocks Wb of hb (each as [a, a + n));
   - seg_evt g hb Wb pc pc' Pre Pst: from every cut state at pc (FR with the live harness blocks hb, the allocator's
     block list, the cut predicate Pre) at an FP state with frm = 0 (the cut's: CUTST carries it) the run on the
     normalized memory reaches pc' at some FP state with frm = 0,
     writes only seg_W g Wb, keeps writability, keeps sp, gp, tp, and every state related to its end state satisfies
     Pst (libreac/fuzz_ctrl's sl_seg_fp premise, origin/ossv/recipes 25e3d17bdb50 Prog/Seg/Tac_slot.v, with the
     written blocks and longl in the write set);
   - b1_seg_hb: such a run closes the cut at pc' with the same hb (FR across it by Tac_b1.b1_fr_hb), so H(cut at pc')
     gives H of the start state. This is reac-pw/fuzz_role's Tac_slot.sl_seg_fp with b1_fr_hb in place of sl_fr_run;
   - seg_We, seg_evt_e, b1_seg_hb_e, b1_seg_evt_e: the same with the errno cell [ERRNO_CELL, ERRNO_CELL + 4) in the
     write set (FR across it by Tac_b1.b1_fr_hb_e), for a body whose callee writes errno: V01's reac_segconf_declared
     (reac_declared_vlan_split's strtol) puts errno's value back, but the raw cell may go from unwritten to written.
   Segment lemma: the slot's lift of a segment body. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import SlotFR SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.SegCF Require Import Tac_slot Tac_b1.
Import ListNotations.
Open Scope Z_scope.

Definition seg_W (g : ghost) (Wb : list (Z * Z)) : list (Z * Z) :=
  (g_S g - SLOT_K, g_S g - 104) :: (LONGL, LONGL + LONGL_W) :: map (fun x => (fst x, fst x + snd x)) Wb.

Lemma outside_wb : forall Wb a, ~ in_wb Wb a -> Frame.outside (map (fun x => (fst x, fst x + snd x)) Wb) a.
Proof.
  induction Wb as [|[phi n] Wb IH]; intros a H; cbn [map Frame.outside fst snd]; [exact I|]. split.
  - intros Hr. apply H. exists phi, n. split; [left; reflexivity | exact Hr].
  - apply IH. intros (p & k & Hin & Hr). apply H. exists p, k. split; [right; exact Hin | exact Hr].
Qed.

Lemma outside_seg_W : forall g Wb a, ~ (g_S g - SLOT_K <= a < g_S g - 104) -> ~ in_wb Wb a ->
  ~ (LONGL <= a < LONGL + LONGL_W) -> Frame.outside (seg_W g Wb) a.
Proof.
  intros g Wb a H1 H2 H3. unfold seg_W. cbn [Frame.outside].
  split; [exact H1|]. split; [exact H3|]. exact (outside_wb Wb a H2).
Qed.

(* The errno cell of the build: errno_addr B = ms_tp B + ms_errno_off B = 0x335b0 - 164 (Tac_slot.sl_errno_val). *)
Definition ERRNO_CELL : Z := 0x335b0 - 164.

Definition seg_We (g : ghost) (Wb : list (Z * Z)) : list (Z * Z) := (ERRNO_CELL, ERRNO_CELL + 4) :: seg_W g Wb.

Lemma outside_seg_We : forall g Wb a, ~ (g_S g - SLOT_K <= a < g_S g - 104) -> ~ in_wb Wb a ->
  ~ (LONGL <= a < LONGL + LONGL_W) -> ~ (ERRNO_CELL <= a < ERRNO_CELL + 4) -> Frame.outside (seg_We g Wb) a.
Proof.
  intros g Wb a H1 H2 H3 H4. unfold seg_We. cbn [Frame.outside].
  split; [exact H4 | exact (outside_seg_W g Wb a H1 H2 H3)].
Qed.

Section TS.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Let API := APIf rc.

(* The evt body of a segment from the cut at pc (predicate Pre) to the cut at pc' (predicate Pst), same hb. *)
Definition seg_evt (g : ghost) (hb Wb : list (Z * Z)) (pc pc' : Z)
    (Pre Pst : bvmap 5 word -> (word -> option byte) -> Prop) : Prop :=
  forall L A regs mem md,
    FR B APIf ra empty g hb L A regs mem md ->
    Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
    Pre regs mem -> frm_zero fp_csr ->
    Exec.evt rsegs
      (fun ms => exists R F' fc' m', ms = MState.MS R F' (Z_to_bv 64 pc') fc' None m' (seg_rom rsegs) /\
         frm_zero fc' /\
         Frame.munch (seg_W g Wb) (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
         YK11.getr R 2 = YK11.getr regs 2 /\ YK11.getr R 3 = YK11.getr regs 3 /\ YK11.getr R 4 = YK11.getr regs 4 /\
         (forall regs' m, Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m m' -> Pst regs' m))
      (MState.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 pc) fp_csr None (normalize rsegs mem) (seg_rom rsegs)).

Hypothesis FF : frame_facts_cf B APIf LS SH SK ra empty.

(* A segment body closes the cut at pc' with the same hb: H(cut at pc') -> H of the start state. *)
Lemma b1_seg_hb : forall g hb Wb L A regs mem md pc pc' (P' : bvmap 5 word -> (word -> option byte) -> Prop)
    (Q : machine_state -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> (forall x, In x Wb -> In x hb) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F' fc' m', ms = MState.MS R F' (Z_to_bv 64 pc') fc' None m' (seg_rom rsegs) /\
     frm_zero fc' /\
     Frame.munch (seg_W g Wb) (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
     YK11.getr R 2 = YK11.getr regs 2 /\ YK11.getr R 3 = YK11.getr regs 3 /\ YK11.getr R 4 = YK11.getr regs 4 /\
     (forall regs' m, Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m m' -> P' regs' m)) ->
  (forall c, CUTST B APIf ra empty g pc' hb P' c -> SR (ms_segs B) c (Post B APIf ra g)) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs pc mem (YK11.seg_rom (ms_segs B))) md) (Post B APIf ra g).
Proof.
  intros g hb Wb L A regs mem md pc pc' P' Q HFR HP HWb HE Hform HK.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  apply (sl_run_fp regs pc mem md Q (Post B APIf ra g) Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & F' & fc' & m' & -> & _).
    exists R, F', (Z_to_bv 64 pc'), fc', m'. reflexivity.
  - intros R F' pc1 fc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & F1 & fc1 & m1 & E & Hz & MU & WM & E2 & E3 & E4 & HP').
    injection E; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    assert (MU' : Frame.munch (seg_W g Wb) mem m')
      by exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame MU).
    assert (WM' : Frame.wmono rsegs mem m')
      by exact (wmono_rel rsegs mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame WM).
    assert (MI' : ro_agree rsegs m') by exact (ro_agree_same rsegs mem m' HMI Hsame).
    assert (HFR' : FR B APIf ra empty g hb L A regs' m' md).
    { apply (b1_fr_hb B APIf ra empty FF g hb Wb L A regs mem md regs' m' HFR HP HWb).
      - intros a Ha H1 H2 H3. apply MU'. rewrite (MState.unsigned_lit a Ha).
        exact (outside_seg_W g Wb a H1 H2 H3).
      - exact WM'.
      - exact MI'.
      - rewrite (sl_getr_eqv _ _ _ Hx). exact E2.
      - rewrite (sl_getr_eqv _ _ _ Hx). exact E3.
      - rewrite (sl_getr_eqv _ _ _ Hx). exact E4. }
    rewrite <- SEGS. apply HK. exists (mkFP F1 fc1), L, A, regs', m', md.
    split; [reflexivity|]. split; [exact Hz|]. split; [exact HFR'|]. split; [exact HP|].
    exact (HP' regs' m' Hx Hrel).
Qed.

(* seg_evt's run, at the FP state of the cut it starts from, closes the cut at pc'. *)
Lemma b1_seg_evt : forall g hb Wb pc pc' (Pre Pst : bvmap 5 word -> (word -> option byte) -> Prop) L A regs mem md,
  seg_evt g hb Wb pc pc' Pre Pst -> (forall x, In x Wb -> In x hb) ->
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> Pre regs mem -> frm_zero fp_csr ->
  (forall c, CUTST B APIf ra empty g pc' hb Pst c -> SR (ms_segs B) c (Post B APIf ra g)) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs (Z_to_bv 64 pc) mem (YK11.seg_rom (ms_segs B))) md) (Post B APIf ra g).
Proof.
  intros g hb Wb pc pc' Pre Pst L A regs mem md EVT HWb HFR HP HPre Hfrm HK.
  apply (b1_seg_hb g hb Wb L A regs mem md (Z_to_bv 64 pc) pc' Pst _ HFR HP HWb (EVT L A regs mem md HFR HP HPre Hfrm)).
  - intros ms HQ. exact HQ.
  - exact HK.
Qed.

(* seg_evt with the errno cell in the write set (seg_We). *)
Definition seg_evt_e (g : ghost) (hb Wb : list (Z * Z)) (pc pc' : Z)
    (Pre Pst : bvmap 5 word -> (word -> option byte) -> Prop) : Prop :=
  forall L A regs mem md,
    FR B APIf ra empty g hb L A regs mem md ->
    Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
    Pre regs mem -> frm_zero fp_csr ->
    Exec.evt rsegs
      (fun ms => exists R F' fc' m', ms = MState.MS R F' (Z_to_bv 64 pc') fc' None m' (seg_rom rsegs) /\
         frm_zero fc' /\
         Frame.munch (seg_We g Wb) (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
         YK11.getr R 2 = YK11.getr regs 2 /\ YK11.getr R 3 = YK11.getr regs 3 /\ YK11.getr R 4 = YK11.getr regs 4 /\
         (forall regs' m, Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m m' -> Pst regs' m))
      (MState.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 pc) fp_csr None (normalize rsegs mem) (seg_rom rsegs)).

(* b1_seg_hb for a body that may also write the errno cell. *)
Lemma b1_seg_hb_e : forall g hb Wb L A regs mem md pc pc' (P' : bvmap 5 word -> (word -> option byte) -> Prop)
    (Q : machine_state -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> (forall x, In x Wb -> In x hb) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F' fc' m', ms = MState.MS R F' (Z_to_bv 64 pc') fc' None m' (seg_rom rsegs) /\
     frm_zero fc' /\
     Frame.munch (seg_We g Wb) (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
     YK11.getr R 2 = YK11.getr regs 2 /\ YK11.getr R 3 = YK11.getr regs 3 /\ YK11.getr R 4 = YK11.getr regs 4 /\
     (forall regs' m, Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m m' -> P' regs' m)) ->
  (forall c, CUTST B APIf ra empty g pc' hb P' c -> SR (ms_segs B) c (Post B APIf ra g)) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs pc mem (YK11.seg_rom (ms_segs B))) md) (Post B APIf ra g).
Proof.
  intros g hb Wb L A regs mem md pc pc' P' Q HFR HP HWb HE Hform HK.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof (sl_errno_val B APIf ra empty FF) as Ev.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  apply (sl_run_fp regs pc mem md Q (Post B APIf ra g) Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & F' & fc' & m' & -> & _).
    exists R, F', (Z_to_bv 64 pc'), fc', m'. reflexivity.
  - intros R F' pc1 fc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & F1 & fc1 & m1 & E & Hz & MU & WM & E2 & E3 & E4 & HP').
    injection E; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    assert (MU' : Frame.munch (seg_We g Wb) mem m')
      by exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame MU).
    assert (WM' : Frame.wmono rsegs mem m')
      by exact (wmono_rel rsegs mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame WM).
    assert (MI' : ro_agree rsegs m') by exact (ro_agree_same rsegs mem m' HMI Hsame).
    assert (HFR' : FR B APIf ra empty g hb L A regs' m' md).
    { apply (b1_fr_hb_e B APIf ra empty FF g hb Wb L A regs mem md regs' m' HFR HP HWb).
      - intros a Ha H1 H2 H3 H4. apply MU'. rewrite (MState.unsigned_lit a Ha).
        apply (outside_seg_We g Wb a H1 H2 H3). unfold ERRNO_CELL. rewrite <- Ev. exact H4.
      - exact WM'.
      - exact MI'.
      - rewrite (sl_getr_eqv _ _ _ Hx). exact E2.
      - rewrite (sl_getr_eqv _ _ _ Hx). exact E3.
      - rewrite (sl_getr_eqv _ _ _ Hx). exact E4. }
    rewrite <- SEGS. apply HK. exists (mkFP F1 fc1), L, A, regs', m', md.
    split; [reflexivity|]. split; [exact Hz|]. split; [exact HFR'|]. split; [exact HP|].
    exact (HP' regs' m' Hx Hrel).
Qed.

(* seg_evt_e's run, at the FP state of the cut it starts from, closes the cut at pc'. *)
Lemma b1_seg_evt_e : forall g hb Wb pc pc' (Pre Pst : bvmap 5 word -> (word -> option byte) -> Prop) L A regs mem md,
  seg_evt_e g hb Wb pc pc' Pre Pst -> (forall x, In x Wb -> In x hb) ->
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> Pre regs mem -> frm_zero fp_csr ->
  (forall c, CUTST B APIf ra empty g pc' hb Pst c -> SR (ms_segs B) c (Post B APIf ra g)) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs (Z_to_bv 64 pc) mem (YK11.seg_rom (ms_segs B))) md) (Post B APIf ra g).
Proof.
  intros g hb Wb pc pc' Pre Pst L A regs mem md EVT HWb HFR HP HPre Hfrm HK.
  apply (b1_seg_hb_e g hb Wb L A regs mem md (Z_to_bv 64 pc) pc' Pst _ HFR HP HWb
           (EVT L A regs mem md HFR HP HPre Hfrm)).
  - intros ms HQ. exact HQ.
  - exact HK.
Qed.

End TS.
