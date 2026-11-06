From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_call verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_br.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require VerbsMem rec_shape_of_c RecKindB reply rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
Import ListNotations.
Local Open Scope Z_scope.

Section T0.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Definition vr_post (S : vstart) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' O' b',
    c' = mkCfg (@mkst fx' regs' (getr (s_regs S) 1) mem' (seg_rom (ms_segs B))) md' /\
    RecKindB.fp_kept (s_fx S) fx' /\
    RecKindB.call_post_rec B (aa_MR API) VR_K (s_L S) (s_A S) (s_regs S) (s_mem S) (s_md S) vr_writes
      (fun a => In a (map fst (s_O S))) L' A' regs' mem' md' /\
    ro_agree (ms_segs B) mem' /\
    (let '(R', x, quit) := vr_run (s_R S) (s_D S) in
       g_rec_rep (ms_segs B) L' A' mem' R' O' /\
       le_at B mem' G_QUIT (Mem.le4 (Z_to_bv 64 (if quit then 1 else s_q0 S)))) /\
    In (s_data S, Z.max (s_n S) 1) (blocks L' A') /\ le_at B mem' (s_data S) (s_D S) /\
    ~ In (s_data S, Z.max (s_n S) 1) O' /\
    (forall pn, In pn (blocks (s_L S) (s_A S)) -> ~ In pn (s_O S) -> In pn (blocks L' A')) /\
    (forall pn, In pn (blocks (s_L S) (s_A S)) -> ~ In pn (s_O S) -> ~ In pn O') /\
    (st_init_done (s_A S) = true -> st_init_done A' = true) /\
    (length (st_regions (s_A S)) <= length (st_regions A'))%nat /\
    le_at B mem' (s_msg S) (Mem.le4 (Z_to_bv 64 (s_fd S))) /\
    le_at B mem' (s_msg S + 8) (Mem.le8 (Z_to_bv 64 (s_data S))) /\
    le_at B mem' (s_msg S + 16) (Mem.le8 (Z_to_bv 64 (s_n S))) /\
    (forall pn, In pn (blocks L' A') -> (In pn (blocks (s_L S) (s_A S)) /\ ~ In pn (s_O S)) \/ In pn O') /\
    blocks_kept B (s_L S) (s_A S) (s_mem S) mem' (owned_by (s_O S)) /\
    (exists can', vr_tables B mem' can') /\
    Mem.bytes_at (ms_segs B) mem' rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes /\
    res_ok_slots A' b' /\ sb_cap b' = sb_cap (s_b S).

End T0.

Section T1.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.

Definition tl_state (rg : bvmap 5 word) (pc : Z) (mem1 : word -> option byte) (md1 : Model) (L1 : layout)
    (A1 : astate) (R1 : rstate) (O1 : list (Z * Z)) (k1 : nat) (qv : Z) (X : list (Z * Z))
    (jk : list byte) (c : config) : Prop :=
  c = mkCfg (mkst rg (Z_to_bv 64 pc) mem1 (seg_rom rsegs)) md1 /\
  RecKindB.fp_kept (s_fx S) fx /\ vregs S rg /\ vtail B API S L1 A1 mem1 md1 R1 O1 k1 X /\ vfr S mem1 jk /\
  bytes_at rsegs mem1 G_QUIT (le4 (Z_to_bv 64 qv)) /\ (forall i, 0 <= i < 4 -> writable_at rsegs mem1 (G_QUIT + i)).

Lemma tl_bridge : forall rg pc mem1 md1 L1 A1 R1 O1 k1 qv X jk c (W : list (Z * Z)) (QQ : machine_state -> Prop) P,
  tl_state rg pc mem1 md1 L1 A1 R1 O1 k1 qv X jk c ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ (s_regs S) - VR_K <= x < spZ (s_regs S)) -> ~ (G_QUIT <= x < G_QUIT + 4) ->
     Frame.outside W x) ->
  evt rsegs (fun ms' => QQ ms' /\ exists R' pc' m', ms' = MS R' fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
                 munch W (normalize rsegs mem1) m' /\ wmono rsegs (normalize rsegs mem1) m')
    (MS (Regs6ss.mkR_of rg) fp_regs (Z_to_bv 64 pc) fp_csr None (normalize rsegs mem1) (seg_rom rsegs)) ->
  (forall R' pc' m' mem2 rg', QQ (MS R' fp_regs pc' fp_csr None m' (seg_rom rsegs)) -> Regs6ss.xregs_eqv R' rg' ->
     mem_rel rsegs mem2 m' -> munch W mem1 mem2 -> wmono rsegs mem1 mem2 ->
     vtail B API S L1 A1 mem2 md1 R1 O1 k1 X ->
     (forall a k s bs, In (a, k) (blocks L1 A1) -> a <= s -> s + Z.of_nat (length bs) <= a + k ->
        bytes_at rsegs mem1 s bs -> bytes_at rsegs mem2 s bs) ->
     SR rsegs (mkCfg (mkst rg' pc' mem2 (seg_rom rsegs)) md1) P) ->
  SR rsegs c P.
Proof using HF HS.
  intros rg pc mem1 md1 L1 A1 R1 O1 k1 qv X jk c W QQ P (-> & FPK & VR & H & FR & GQ & GW) WO EVT K.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  pose proof (t_rel _ _ _ _ _ _ _ _ _ _ _ H) as REL. pose proof REL as (HM1 & _).
  pose proof (t_ro _ _ _ _ _ _ _ _ _ _ _ H) as RO1. rewrite SEGS in RO1.
  pose proof (aa_laws API) as LAWS.
  destruct (mr_model _ _ LAWS _ _ _ _ HM1) as (Hh & Hl & Hmat).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. apply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO1 | exact EVT]. }
  intros ms5 (can5 & (s5 & (Q5 & R' & pc' & m' & E5 & MU' & WM') & REL5 & ROS5) & EQ5).
  subst s5.
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL5) as [CAN5 HR5].
  remember (ms_mem can5) as mem2 eqn:Em2. subst can5. clear Em2.
  assert (RN1 : mem_rel rsegs mem1 (normalize rsegs mem1)) by (apply mem_rel_normalize; exact RO1).
  pose proof (munch_rel rsegs _ _ _ _ _ RN1 HR5 ROS5 MU') as MU.
  pose proof (wmono_rel rsegs _ _ _ _ RN1 HR5 ROS5 WM') as WM.
  pose proof (ro_agree_same rsegs _ _ RO1 ROS5) as RO2.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (rg' & -> & X5).
  assert (NOQ : forall a, owned B L1 A1 a -> ~ (G_QUIT <= a < G_QUIT + 4)).
  { intros a Ho Hq. apply (vf_globo B API HF L1 A1 mem1 md1 a HM1); [|exact Ho].
    replace a with (G_QUIT + (a - G_QUIT)) by ring. apply gq_glob. lia. }
  assert (TM : vtail B API S L1 A1 mem2 md1 R1 O1 k1 X /\
    (forall a k s bs, In (a, k) (blocks L1 A1) -> a <= s -> s + Z.of_nat (length bs) <= a + k ->
       bytes_at rsegs mem1 s bs -> bytes_at rsegs mem2 s bs)).
  { apply (tail_mem B API HF S HS L1 A1 mem1 md1 R1 O1 k1 X mem2 H).
    - eapply (mr_frame B _ LAWS L1 A1 mem1 mem2 md1 md1 HM1).
      + intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HM1 Ho) as [Ha1 Ha2].
        rewrite SEGS. eapply munch_mbyte; [exact MU | lia | apply WO; [lia | lia | exact (NOQ a Ho)]].
      + intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HM1 Ho) as [Ha1 Ha2].
        eapply munch_present; [exact MU | lia | apply WO; [lia | lia | exact (NOQ a Ho)] | exact Hp].
      + intros p k i Hin Hi. destruct (mr_blocks B _ LAWS L1 A1 mem1 md1 p k i HM1 Hin Hi) as (Hp & H4 & Hc & Hno).
        assert (Hni : ~ in_img B (ptr_addr L1 p + i)) by exact (ax_blocks_img (vf_ax B API HF) L1 A1 mem1 md1 p k i HM1 Hin Hi).
        eapply munch_present; [exact MU | lia | apply WO; [lia | lia | ] | exact Hp].
        intros Hq. apply Hni. replace (ptr_addr L1 p + i) with (G_QUIT + (ptr_addr L1 p + i - G_QUIT)) by ring.
        exact (proj1 (vf_globs B API HF _ (gq_glob (ptr_addr L1 p + i - G_QUIT) ltac:(lia)))).
      + reflexivity.
      + exact Hh.
      + exact Hl.
      + exact Hmat.
    - rewrite SEGS. exact RO2.
    - intros a Ra Hs Hq. split; [eapply munch_mbyte | eapply munch_writable]; (exact MU || exact Ra || (apply WO; assumption)).
    - intros a _ W1. apply WM. exact W1. }
  destruct TM as [T KB].
  exact (K R' pc' m' mem2 rg' Q5 X5 HR5 MU WM T KB).
Qed.

Lemma tl_w : forall rg pc mem1 md1 L1 A1 R1 O1 k1 qv X jk c (W : list (Z * Z)) (QQ : machine_state -> Prop) P,
  tl_state rg pc mem1 md1 L1 A1 R1 O1 k1 qv X jk c ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ (s_regs S) - VR_K <= x < s_spf S) -> Frame.outside W x) ->
  evt rsegs (fun ms' => QQ ms' /\ exists R' pc' m', ms' = MS R' fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
                 munch W (normalize rsegs mem1) m' /\ wmono rsegs (normalize rsegs mem1) m')
    (MS (Regs6ss.mkR_of rg) fp_regs (Z_to_bv 64 pc) fp_csr None (normalize rsegs mem1) (seg_rom rsegs)) ->
  (forall R' pc' m' rg' mem2, QQ (MS R' fp_regs pc' fp_csr None m' (seg_rom rsegs)) -> Regs6ss.xregs_eqv R' rg' ->
     (forall pz, pc' = Z_to_bv 64 pz -> vregs S rg' ->
        tl_state rg' pz mem2 md1 L1 A1 R1 O1 k1 qv X jk (mkCfg (mkst rg' pc' mem2 (seg_rom rsegs)) md1)) ->
     SR rsegs (mkCfg (mkst rg' pc' mem2 (seg_rom rsegs)) md1) P) ->
  SR rsegs c P.
Proof using HF HS.
  intros rg pc mem1 md1 L1 A1 R1 O1 k1 qv X jk c W QQ P HST WO EVT K.
  pose proof HST as (_ & FPK & _ & _ & FR & GQ & GW).
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  apply (tl_bridge rg pc mem1 md1 L1 A1 R1 O1 k1 qv X jk c W QQ P HST).
  - intros x Hx H1 _. apply WO; [exact Hx|]. unfold s_spf. lia.
  - exact EVT.
  - intros R' pc' m' mem2 rg' HQ X' _ MU _ T2 _.
    apply (K R' pc' m' rg' mem2 HQ X'). intros pz Epz VR'. subst pc'.
    assert (KP : forall a, s_spf S <= a < s_spf S + 608 \/ G_QUIT <= a < G_QUIT + 4 ->
              mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)).
    { intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (unfold s_spf, G_QUIT, VR_K in *; lia).
      assert (Oa : Frame.outside W a) by (apply WO; [exact Ra | unfold s_spf, G_QUIT, VR_K in *; lia]).
      split; [exact (munch_mbyte rsegs W mem1 mem2 a MU Ra Oa) | exact (munch_writable rsegs W mem1 mem2 a MU Ra Oa)]. }
    split; [reflexivity|]. split; [exact FPK|]. split; [exact VR'|]. split; [exact T2|].
    split.
    + apply (vfr_keep B API S HS mem1 mem2 jk); [|exact FR]. intros a Ha. apply KP. left. exact Ha.
    + apply (gq_transfer mem1 mem2 qv); [|exact GQ|exact GW]. intros i Hi. apply KP. right. lia.
Qed.

End T1.
