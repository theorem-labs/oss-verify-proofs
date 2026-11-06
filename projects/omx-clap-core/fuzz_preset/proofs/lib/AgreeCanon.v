From Stdlib Require Import ZArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Statements Images.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require RoomShapesDraft.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Uniform.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
  YK0i YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  SlotAgree Agree AgreeTop AgreeZlib.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require AgreeZlib.
Import ListNotations.
Open Scope Z_scope.

Section Rz.
Variable segs : list Segment.

Inductive star_nb : config -> list event -> config -> Prop :=
| snb_refl : forall c, star_nb c [] c
| snb_step : forall c1 evs c2 tr c3,
    ~ budget_refused_at segs c1 -> sstep_cfg segs ACFG c1 evs (SNext c2) -> star_nb c2 tr c3 ->
    star_nb c1 (evs ++ tr) c3.

Lemma guarded_nb : forall c tr c', RoomShapesDraft.star_guarded segs ACFG c tr c' -> star_nb c tr c'.
Proof.
  intros c tr c' H. induction H as [c | c1 evs c2 tr c3 _ NB Hs _ IH].
  - apply snb_refl.
  - exact (snb_step c1 evs c2 tr c3 NB Hs IH).
Qed.

Lemma canon_nb : forall p dev s st c tr c',
  RoomShapesDraft.star_canon_fb p segs ACFG dev s st c tr c' ->
  (forall tr0 c0, RoomShapesDraft.star_canon_fb p segs ACFG dev s st c tr0 c0 -> ~ budget_refused_at segs c0) ->
  star_nb c tr c'.
Proof.
  intros p dev s st c tr c' H.
  induction H as [dev s st c | dev s s' st st' c1 evs c2 tr c3 Hu Hs Hc Hsn Hstn _ IH
                  | dev s s' st st' c1 evs c2 tr c3 Hn Hu Hs Hsn Hstn _ IH];
    intros NB.
  - apply snb_refl.
  - apply (snb_step c1 evs c2 tr c3); [exact (NB [] c1 (RoomShapesDraft.scf_refl p segs ACFG dev s st c1)) | exact Hs |].
    apply IH. intros tr0 c0 H0.
    exact (NB (evs ++ tr0) c0
      (RoomShapesDraft.scf_canon p segs ACFG dev s s' st st' c1 evs c2 tr0 c0 Hu Hs Hc Hsn Hstn H0)).
  - apply (snb_step c1 evs c2 tr c3); [exact (NB [] c1 (RoomShapesDraft.scf_refl p segs ACFG dev s st c1)) | exact Hs |].
    apply IH. intros tr0 c0 H0.
    exact (NB (evs ++ tr0) c0
      (RoomShapesDraft.scf_fallback p segs ACFG dev s s' st st' c1 evs c2 tr0 c0 Hn Hu Hs Hsn Hstn H0)).
Qed.

Lemma rz_step_nb : forall c T e c', realizes segs c T -> ~ budget_refused_at segs c ->
  sstep_cfg segs ACFG c e (SNext c') -> exists T', realizes segs c' T'.
Proof.
  intros c T e c' H; revert e c'.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq | c I nx T i0 Hnode Hcont IH | c T Hb];
    intros e c' NB Hss.
  - destruct Hnode as [_ Hsound]. destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_halted_none; exact Hss.
  - exact (IH e c' NB Hss).
  - destruct Hnode as [_ Hsound]. destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. exact (NB Hb).
Qed.

Lemma rz_no_error_nb : forall c T e, realizes segs c T -> ~ budget_refused_at segs c ->
  ~ sstep_cfg segs ACFG c e SError.
Proof.
  intros c T e H; revert e.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq | c I nx T i0 Hnode Hcont IH | c T Hb];
    intros e NB Hss.
  - destruct Hnode as [_ Hsound]. destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_halted_none; exact Hss.
  - exact (IH e NB Hss).
  - destruct Hnode as [_ Hsound]. destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - exact (NB Hb).
Qed.

Lemma rz_nb_reach : forall c tr c', star_nb c tr c' -> forall T, realizes segs c T -> exists T', realizes segs c' T'.
Proof.
  intros c tr c' H. induction H as [c | c1 evs c2 tr c3 NB Hs _ IH]; intros T R.
  - exists T. exact R.
  - destruct (rz_step_nb c1 T evs c2 R NB Hs) as (T2 & R2). exact (IH T2 R2).
Qed.

Lemma rz_nb_traces : forall c T, realizes segs c T -> forall tr' c', star_nb c tr' c' ->
  forall tr, is_prefix tr tr' -> tr <> [] -> T tr.
Proof.
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq | c I nx T i0 Hnode Hcont IH | c T Hb];
    intros tr' c' Hp tr Hpre Hne.
  - destruct Hnode as [_ Hsound].
    inversion Hp as [c0 | c1 e c2 tr2 c3 NB Hs Hrest]; subst.
    + exfalso. apply Hne. apply is_prefix_nil_r. exact Hpre.
    + destruct (Hsound e (SNext c2) Hs) as (i & -> & Heq2). inversion Heq2; subst c2.
      exists i. destruct (is_prefix_app_split (evs i) tr2 tr Hpre) as [Hl | (b & -> & Hb)].
      * left. exact Hl.
      * destruct b as [| x b].
        -- left. rewrite app_nil_r. apply is_prefix_refl.
        -- right. exists (x :: b). split; [reflexivity |].
           eapply IH; [exact Hrest | exact Hb | discriminate].
  - inversion Hp as [c0 | c1 e c2 tr2 c3 NB Hs Hrest]; subst.
    + exfalso. apply Hne. apply is_prefix_nil_r. exact Hpre.
    + exfalso. apply Hh. eapply sstep_halted_none; exact Hs.
  - cbn in Heq. apply Heq. exact (IH tr' c' Hp tr Hpre Hne).
  - destruct Hnode as [_ Hsound].
    inversion Hp as [c0 | c1 e c2 tr2 c3 NB Hs Hrest]; subst.
    + exfalso. apply Hne. apply is_prefix_nil_r. exact Hpre.
    + destruct (Hsound e (SNext c2) Hs) as (i & -> & Heq2). inversion Heq2; subst c2.
      exists i. eapply IH; [exact Hrest | exact Hpre | exact Hne].
  - inversion Hp as [c0 | c1 e c2 tr2 c3 NB Hs Hrest]; subst.
    + exfalso. apply Hne. apply is_prefix_nil_r. exact Hpre.
    + exfalso. exact (NB Hb).
Qed.

Definition reach_all (P : config -> Prop) (c0 : config) : Prop :=
  forall tr c, star_cfg segs ACFG c0 tr c -> P c.

Definition no_unplaced (c : config) : Prop := ~ RoomShapesDraft.unplaced_at segs c.

Lemma reach_all_here : forall P c, reach_all P c -> P c.
Proof. intros P c H. exact (H [] c (star_cfg_refl segs ACFG c)). Qed.

Lemma reach_all_step : forall P c e c', reach_all P c -> sstep_cfg segs ACFG c e (SNext c') -> reach_all P c'.
Proof.
  intros P c e c' H Hs tr c'' Hstar. apply (H (e ++ tr) c''). eapply star_cfg_step; [exact Hs | exact Hstar].
Qed.

Lemma canon_branch : forall p s st dev c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet),
  node_ok segs c I evs nx -> (forall i, realizes segs (nx i) (T i)) -> cut_free segs c ->
  uniform segs c -> reach_all no_unplaced c ->
  (forall i, cut_free segs (nx i) -> uniform segs (nx i) -> reach_all no_unplaced (nx i) ->
     forall dev' s' st' tr, T i tr ->
     exists tr' c', RoomShapesDraft.star_canon_fb p segs ACFG dev' s' st' (nx i) tr' c' /\ is_prefix tr tr') ->
  forall i tr, t_emit (evs i) (T i) tr ->
  exists tr' c', RoomShapesDraft.star_canon_fb p segs ACFG dev s st c tr' c' /\ is_prefix tr tr'.
Proof.
  intros p s st dev c I evs nx T [Hcomp Hsound] Hcont NR HU HN IH i tr Htr.
  assert (IHj : forall j dev' s' st' tr0, T j tr0 ->
      exists tr' c', RoomShapesDraft.star_canon_fb p segs ACFG dev' s' st' (nx j) tr' c' /\ is_prefix tr0 tr').
  { intros j. apply IH.
    - exact (cut_free_step segs c (evs j) (nx j) NR (Hcomp j)).
    - exact (uniform_step segs c (evs j) (nx j) HU (Hcomp j)).
    - exact (reach_all_step _ c (evs j) (nx j) HN (Hcomp j)). }
  assert (HNc : dev = true -> ~ RoomShapesDraft.unplaced_at segs c) by (intros _; exact (reach_all_here _ c HN)).
  (* The step's own vDSO state and stack low end: the reviewed form fixes both by the step. *)
  assert (NXT : forall j, exists s' st', RoomShapesDraft.strip_next p segs c (nx j) s s' /\
                                         RoomShapesDraft.stack_next segs c (nx j) st st').
  { intros j. destruct (RoomShapesDraft.strip_next_total p segs c (nx j) s) as (s' & Hs').
    destruct (RoomShapesDraft.stack_next_total segs c (nx j) st) as (st' & Hst').
    exists s', st'. exact (conj Hs' Hst'). }
  assert (GO : forall j, evs j = evs i -> (forall tr0, T i tr0 -> T j tr0) ->
      RoomShapesDraft.canonical_step p s st segs c (nx j) ->
      exists tr' c', RoomShapesDraft.star_canon_fb p segs ACFG dev s st c tr' c' /\ is_prefix tr tr').
  { intros j Ee HT Hc. destruct (NXT j) as (s' & st' & Hs' & Hst'). destruct Htr as [Hp | (tr0 & -> & H0)].
    - exists (evs j ++ []), (nx j). split.
      + exact (RoomShapesDraft.scf_canon p segs ACFG dev s s' st st' c (evs j) (nx j) [] (nx j) HNc (Hcomp j) Hc
          Hs' Hst' (RoomShapesDraft.scf_refl p segs ACFG dev s' st' (nx j))).
      + rewrite app_nil_r, Ee. exact Hp.
    - destruct (IHj j dev s' st' tr0 (HT tr0 H0)) as (tr' & c' & Hs & Hp).
      exists (evs j ++ tr'), c'. split.
      + exact (RoomShapesDraft.scf_canon p segs ACFG dev s s' st st' c (evs j) (nx j) tr' c' HNc (Hcomp j) Hc
          Hs' Hst' Hs).
      + rewrite Ee. apply is_prefix_app_mono. exact Hp. }
  destruct (classic (RoomShapesDraft.canonical_step p s st segs c (nx i))) as [Hc | Hnc].
  - exact (GO i eq_refl (fun tr0 H0 => H0) Hc).
  - destruct (classic (RoomShapesDraft.canon_can_step p s st segs ACFG c)) as [(e2 & c2 & Hs2 & Hc2) | Hno].
    + destruct (Hsound e2 (SNext c2) Hs2) as (j & -> & Ej). injection Ej as Ej. subst c2.
      assert (Hpl : exists x8 len, RoomShapesDraft.placement_at segs c x8 len).
      { apply NNPP. intros Hnp. apply Hnc. intros x8 len Hx. exfalso. apply Hnp. exists x8, len. exact Hx. }
      destruct Hpl as (x8 & len & Hpl).
      destruct (uniform_here segs c HU x8 len Hpl (evs i) (nx i) (evs j) (nx j) (Hcomp i) (Hcomp j)) as (Ee & Hobs).
      apply (GO j (eq_sym Ee)); [| exact Hc2].
      intros tr0 H0.
      apply (proj1 (realizes_obs_iff segs (nx j) (T j) (Hcont j) (cut_free_step segs c (evs j) (nx j) NR (Hcomp j)) tr0)).
      apply (proj1 (Hobs tr0)).
      exact (proj2 (realizes_obs_iff segs (nx i) (T i) (Hcont i) (cut_free_step segs c (evs i) (nx i) NR (Hcomp i)) tr0) H0).
    + destruct (NXT i) as (s' & st' & Hs' & Hst'). destruct Htr as [Hp | (tr0 & -> & H0)].
      * exists (evs i ++ []), (nx i). split.
        -- exact (RoomShapesDraft.scf_fallback p segs ACFG dev s s' st st' c (evs i) (nx i) [] (nx i) Hno
             (reach_all_here _ c HN) (Hcomp i) Hs' Hst' (RoomShapesDraft.scf_refl p segs ACFG true s' st' (nx i))).
        -- rewrite app_nil_r. exact Hp.
      * destruct (IHj i true s' st' tr0 H0) as (tr' & c' & Hs & Hp).
        exists (evs i ++ tr'), c'. split.
        -- exact (RoomShapesDraft.scf_fallback p segs ACFG dev s s' st st' c (evs i) (nx i) tr' c' Hno
             (reach_all_here _ c HN) (Hcomp i) Hs' Hst' Hs).
        -- apply is_prefix_app_mono. exact Hp.
Qed.

Lemma canon_cover : forall p c T, realizes segs c T -> cut_free segs c ->
  uniform segs c -> reach_all no_unplaced c ->
  forall dev s st tr, T tr ->
  exists tr' c', RoomShapesDraft.star_canon_fb p segs ACFG dev s st c tr' c' /\ is_prefix tr tr'.
Proof.
  intros p c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq | c I nx T i0 Hnode Hcont IH | c T Hb];
    intros NR HU HN dev s st tr HT.
  - destruct HT as [i Hi]. exact (canon_branch p s st dev c I evs nx T Hnode Hcont NR HU HN IH i tr Hi).
  - cbv [t_nil] in HT. subst tr. exists [], c. split; [apply RoomShapesDraft.scf_refl | apply is_prefix_nil].
  - cbn in Heq. exact (IH NR HU HN dev s st tr (proj2 (Heq tr) HT)).
  - destruct HT as [i Hi].
    apply (canon_branch p s st dev c I (fun _ => []) nx T Hnode Hcont NR HU HN IH i tr).
    right. exists tr. split; [reflexivity | exact Hi].
  - exfalso. exact (cut_free_here segs c NR Hb).
Qed.

End Rz.

Lemma bh_traces_nil : forall cfg img lim en inp, bh_traces (run_scfg cfg img lim en inp) [].
Proof.
  intros cfg [segs pc ph] lim [sp brk0 mbase rnd] inp. cbn [run_scfg bh_traces]. unfold obs_trace_cfg.
  exists [], (init_config segs pc ph sp brk0 mbase rnd lim inp). split; [apply star_cfg_refl | apply is_prefix_nil].
Qed.

Theorem room_parts_of_rz : forall img lim (T : TSet) p en inp,
  rz_run img lim en inp T -> ~ RoomShapesDraft.canon_budget_refused ACFG p img lim en inp ->
  ~ RoomShapesDraft.guarded_reaches_error ACFG p img lim en inp
  /\ (forall tr, RoomShapesDraft.canon_trace ACFG p img lim en inp tr -> tr <> [] -> T tr).
Proof.
  intros [segs pc ph] lim T p [sp brk0 mbase rnd] inp R Hb.
  cbn [rz_run RoomShapesDraft.canon_budget_refused RoomShapesDraft.guarded_reaches_error
    RoomShapesDraft.canon_trace] in R, Hb |- *.
  set (c0 := init_config segs pc ph sp brk0 mbase rnd lim inp) in *.
  set (st0 := RoomShapesDraft.stack_low (m_vmmaps (cfg_model c0)) p).
  assert (NB : forall tr0 c,
    RoomShapesDraft.star_canon_fb p segs ACFG false RoomShapesDraft.full_strip st0 c0 tr0 c ->
    ~ budget_refused_at segs c).
  { intros tr0 c Hr Hbr. apply Hb. exists tr0, c. split; [exact Hr | exact Hbr]. }
  split.
  - intros (tr & c & evs & Hs & He).
    destruct Hs as [(Hg & _ & Hbr) | Hr].
    + destruct (rz_nb_reach segs c0 tr c (guarded_nb segs c0 tr c Hg) T R) as (T' & R').
      exact (rz_no_error_nb segs c T' evs R' Hbr He).
    + destruct (rz_nb_reach segs c0 tr c (canon_nb segs p false RoomShapesDraft.full_strip st0 c0 tr c Hr NB) T R)
        as (T' & R').
      exact (rz_no_error_nb segs c T' evs R' (NB tr c Hr) He).
  - intros tr (tr' & c & Hr & Hp) Hne.
    exact (rz_nb_traces segs c0 T R tr' c (canon_nb segs p false RoomShapesDraft.full_strip st0 c0 tr' c Hr NB)
      tr Hp Hne).
Qed.

Definition placed_run (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
    reach_all segs (no_unplaced segs) (init_config segs pc ph sp brk0 mbase rnd lim inp)
  end.

Theorem canon_complete_of_rz : forall (vi : ProcInput -> Prop) img lim,
  (forall en inp, valid_entry img en inp -> vi inp ->
     (exists T, rz_run img lim en inp T) /\ cf_run img lim en inp /\ placed_run img lim en inp) ->
  RoomShapesDraft.canon_complete vi ACFG img lim.
Proof.
  intros vi [segs pc ph] lim H p [sp brk0 mbase rnd] inp _ Hv Hi tr Ht.
  destruct (H _ _ Hv Hi) as ((T & R) & C & N).
  cbn [rz_run cf_run placed_run] in R, C, N. destruct C as [C U].
  cbn [run_scfg bh_traces] in Ht.
  cbn [RoomShapesDraft.canon_trace]. unfold RoomShapesDraft.canon_run.
  exact (canon_cover segs p _ T R C U N false RoomShapesDraft.full_strip _ tr
    (proj1 (realizes_obs_iff segs _ T R C tr) Ht)).
Qed.

Theorem ubsan_agree_inputs_of_slots : forall (LS : lib_shape)
    (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop)
    (Gu : list (Z * Z)) (GIu : nat -> (word -> option byte) -> Prop),
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_cg fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  (forall data, @room_calls LS (payload_len data) (calls data) U.AgreeZlib.SBD_AG) ->
  (forall a, U.Reusable.YL0g.in_globals Gu a -> U.Reusable.YL0g.in_globals U.FrameAPI.frame_G a) ->
  U.Contract.G_local_c U.Reusable.YH02.src0_msyms Gu GIu ->
  (forall mem, U.Contract.G_img_c U.Reusable.YH02.src0_msyms Gu mem -> GIu 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @U.SlotAgree.lib_contract_cg fx rc LS U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)
       U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
       Gu U.FrameAPI.frame_RELRO GIu j U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY
       U.FrameAPI.SLOT_STACK) ->
  forall en_p en_s inp,
    valid_entry Images.plain en_p inp -> valid_entry Images.ubsan en_s inp -> valid_input inp ->
    error_free (run_scfg Env.alloc_forced_only Images.plain Budgets.Standard.lim_source en_p inp)
    /\ error_free (run_scfg Env.alloc_forced_only Images.ubsan Budgets.Standard.lim_target en_s inp)
    /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only Images.plain Budgets.Standard.lim_source en_p inp))
                   (bh_traces (run_scfg Env.alloc_forced_only Images.ubsan Budgets.Standard.lim_target en_s inp)).
Proof.
  intros LS G GI Gu GIu HG GIL GI0 Hp HROOM HGu GILu GI0u Hu en_p en_s inp Hpe Hse Hin.
  assert (HP : rz_run Images.plain Budgets.Standard.lim_source en_p inp (SPECX (LS:=LS) inp) /\
    cf_run Images.plain Budgets.Standard.lim_source en_p inp).
  { exact (plain_crealizes_of_cg LS G GI HROOM HG GIL GI0 Hp en_p inp Budgets.Standard.lim_source Hpe Hin
      ltac:(apply Z.leb_le; vm_compute; reflexivity)). }
  assert (HS : rz_run Images.ubsan Budgets.Standard.lim_target en_s inp (SPECX (LS:=LS) inp) /\
    cf_run Images.ubsan Budgets.Standard.lim_target en_s inp).
  { exact (U.AgreeZlib.ubsan_crealizes_of_cg LS Gu GIu HROOM HGu GILu GI0u Hu en_s inp Budgets.Standard.lim_target
      Hse Hin ltac:(apply Z.leb_le; vm_compute; reflexivity)). }
  exact (agree_frame Images.plain Budgets.Standard.lim_source en_p Images.ubsan Budgets.Standard.lim_target en_s inp
    (SPECX (LS:=LS) inp) (SPECX (LS:=LS) inp) (proj1 HP) (proj1 HS) (t_eq_refl _)
    (budget_of_cf_run _ _ _ _ (proj2 HP)) (budget_of_cf_run _ _ _ _ (proj2 HS))).
Qed.

Definition plain_canon_complete : Prop :=
  RoomShapesDraft.canon_complete valid_input Env.alloc_forced_only Images.plain Budgets.Standard.lim_source.

Definition ubsan_canon_complete : Prop :=
  RoomShapesDraft.canon_complete valid_input Env.alloc_forced_only Images.ubsan Budgets.Standard.lim_target.

Definition plain_placed : Prop :=
  forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
    placed_run Images.plain Budgets.Standard.lim_source en inp.

Definition ubsan_placed : Prop :=
  forall en inp, valid_entry Images.ubsan en inp -> valid_input inp ->
    placed_run Images.ubsan Budgets.Standard.lim_target en inp.

Definition plain_canon_cover (LS : lib_shape) : Prop :=
  forall p en inp, RoomShapesDraft.policy_ok p -> valid_entry Images.plain en inp -> valid_input inp ->
    ~ RoomShapesDraft.canon_budget_refused Env.alloc_forced_only p Images.plain Budgets.Standard.lim_source en inp ->
    forall tr, SPECX (LS:=LS) inp tr ->
      RoomShapesDraft.canon_trace Env.alloc_forced_only p Images.plain Budgets.Standard.lim_source en inp tr.

Theorem plain_canon_complete_of_placed : forall (LS : lib_shape)
    (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_cg fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  (forall data, @room_calls LS (payload_len data) (calls data) U.AgreeZlib.SBD_AG) ->
  plain_placed -> plain_canon_complete.
Proof.
  intros LS G GI HG GIL GI0 Hp HROOM Hpl.
  unfold plain_canon_complete.
  apply (canon_complete_of_rz valid_input Images.plain Budgets.Standard.lim_source).
  intros en inp Hv Hi.
  assert (HP : rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=LS) inp) /\
    cf_run Images.plain Budgets.Standard.lim_source en inp).
  { exact (plain_crealizes_of_cg LS G GI HROOM HG GIL GI0 Hp en inp Budgets.Standard.lim_source Hv Hi
      ltac:(apply Z.leb_le; vm_compute; reflexivity)). }
  split; [exists (SPECX (LS:=LS) inp); exact (proj1 HP) | split; [exact (proj2 HP) | exact (Hpl en inp Hv Hi)]].
Qed.

Theorem ubsan_canon_complete_of_placed : forall (LS : lib_shape)
    (Gu : list (Z * Z)) (GIu : nat -> (word -> option byte) -> Prop),
  (forall data, @room_calls LS (payload_len data) (calls data) U.AgreeZlib.SBD_AG) ->
  (forall a, U.Reusable.YL0g.in_globals Gu a -> U.Reusable.YL0g.in_globals U.FrameAPI.frame_G a) ->
  U.Contract.G_local_c U.Reusable.YH02.src0_msyms Gu GIu ->
  (forall mem, U.Contract.G_img_c U.Reusable.YH02.src0_msyms Gu mem -> GIu 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @U.SlotAgree.lib_contract_cg fx rc LS U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)
       U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
       Gu U.FrameAPI.frame_RELRO GIu j U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY
       U.FrameAPI.SLOT_STACK) ->
  ubsan_placed -> ubsan_canon_complete.
Proof.
  intros LS Gu GIu HROOM HGu GILu GI0u Hu Hpl.
  unfold ubsan_canon_complete.
  apply (canon_complete_of_rz valid_input Images.ubsan Budgets.Standard.lim_target).
  intros en inp Hv Hi.
  assert (HS : rz_run Images.ubsan Budgets.Standard.lim_target en inp (SPECX (LS:=LS) inp) /\
    cf_run Images.ubsan Budgets.Standard.lim_target en inp).
  { exact (U.AgreeZlib.ubsan_crealizes_of_cg LS Gu GIu HROOM HGu GILu GI0u Hu en inp Budgets.Standard.lim_target
      Hv Hi ltac:(apply Z.leb_le; vm_compute; reflexivity)). }
  split; [exists (SPECX (LS:=LS) inp); exact (proj1 HS) | split; [exact (proj2 HS) | exact (Hpl en inp Hv Hi)]].
Qed.

Theorem ubsan_agrees_room_of_slots : forall (LS : lib_shape)
    (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop)
    (Gu : list (Z * Z)) (GIu : nat -> (word -> option byte) -> Prop),
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_cg fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  (forall data, @room_calls LS (payload_len data) (calls data) U.AgreeZlib.SBD_AG) ->
  (forall a, U.Reusable.YL0g.in_globals Gu a -> U.Reusable.YL0g.in_globals U.FrameAPI.frame_G a) ->
  U.Contract.G_local_c U.Reusable.YH02.src0_msyms Gu GIu ->
  (forall mem, U.Contract.G_img_c U.Reusable.YH02.src0_msyms Gu mem -> GIu 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @U.SlotAgree.lib_contract_cg fx rc LS U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)
       U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
       Gu U.FrameAPI.frame_RELRO GIu j U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY
       U.FrameAPI.SLOT_STACK) ->
  plain_canon_complete -> ubsan_canon_complete ->
  RoomShapesDraft.agrees_in_room Env.alloc_forced_only Budgets.Standard.lim_source Budgets.Standard.lim_target
    Images.plain Images.ubsan.
Proof.
  intros LS G GI Gu GIu HG GIL GI0 Hp HROOM HGu GILu GI0u Hu Cp Cs.
  apply (RoomShapesDraft.agrees_in_canon_of_parts _ _ _ _ _); [| exact Cp | exact Cs].
  intros p en_p en_s inp _ Hpe Hse Hin _.
  exact (ubsan_agree_inputs_of_slots LS G GI Gu GIu HG GIL GI0 Hp HROOM HGu GILu GI0u Hu en_p en_s inp Hpe Hse Hin).
Qed.

Theorem ubsan_agrees_room_of_spec : forall (LS : lib_shape)
    (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop)
    (Gu : list (Z * Z)) (GIu : nat -> (word -> option byte) -> Prop),
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_g fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  (forall data, @room_calls LS (payload_len data) (calls data) U.AgreeZlib.SBD_AG) ->
  (forall a, U.Reusable.YL0g.in_globals Gu a -> U.Reusable.YL0g.in_globals U.FrameAPI.frame_G a) ->
  U.Contract.G_local_c U.Reusable.YH02.src0_msyms Gu GIu ->
  (forall mem, U.Contract.G_img_c U.Reusable.YH02.src0_msyms Gu mem -> GIu 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @U.SlotAgree.lib_contract_cg fx rc LS U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)
       U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
       Gu U.FrameAPI.frame_RELRO GIu j U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY
       U.FrameAPI.SLOT_STACK) ->
  plain_canon_cover LS -> ubsan_canon_complete ->
  RoomShapesDraft.agrees_in_room Env.alloc_forced_only Budgets.Standard.lim_source Budgets.Standard.lim_target
    Images.plain Images.ubsan.
Proof.
  intros LS G GI Gu GIu HG GIL GI0 Hp HROOM HGu GILu GI0u Hu Vp Cs.
  assert (HROOMp : forall data, @room_calls LS (payload_len data) (calls data) SBD_AG) by exact HROOM.
  assert (HC : zlib_runtime_contracts_R LS (@RI_G LS) G frame_RELRO (fun j T m => T = [] /\ GI j m) (fun _ => [])).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G LS) G frame_RELRO _ (fun _ => [])
      LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step LS GI)).
    intros fx j Hj.
    exact (lib_contract_x_T_of_G src0_msyms (@zlib_API rc) G frame_RELRO GI (fun _ => []) j LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_of_g src0_msyms (@zlib_API rc) (zlib_tables rc) G frame_RELRO GI j LIBPC RA_LIB EMPTY LIB_STACK
        (Hp rc fx j Hj))). }
  apply (RoomShapesDraft.agrees_in_canon_of_spec _ _ _ _ _ (fun _ _ _ inp => SPECX (LS:=LS) inp)).
  intros p en_p en_s inp Hpol Hpe Hse Hin Hb. cbv beta.
  pose proof (plain_rz_of_contracts_R LS (@RI_G LS) G frame_RELRO (fun j T m => T = [] /\ GI j m) (fun _ => [])
    (driver_RI_AG LS HROOMp) (fun a h => frame_G_src0 a (HG a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs G GI GIL) (fun mem H => conj eq_refl (GI0 mem H)) HC en_p inp Hpe Hin) as Rp.
  assert (HS : rz_run Images.ubsan Budgets.Standard.lim_target en_s inp (SPECX (LS:=LS) inp) /\
    cf_run Images.ubsan Budgets.Standard.lim_target en_s inp).
  { exact (U.AgreeZlib.ubsan_crealizes_of_cg LS Gu GIu HROOM HGu GILu GI0u Hu en_s inp Budgets.Standard.lim_target
      Hse Hin ltac:(apply Z.leb_le; vm_compute; reflexivity)). }
  destruct (run_exact_of_rz Images.ubsan Budgets.Standard.lim_target en_s inp _ (proj1 HS)
    (budget_of_cf_run _ _ _ _ (proj2 HS))) as [Es Ts].
  destruct (room_parts_of_rz Images.plain Budgets.Standard.lim_source (SPECX (LS:=LS) inp) p en_p inp Rp Hb)
    as [Ep Tp].
  split; [exact Ep |].
  split; [intros Hr; exact (Es (RoomShapesDraft.guarded_reaches_error_sub _ _ _ _ _ _ Hr)) |].
  split.
  - intros tr. split.
    + intros Ht. destruct tr as [| e tr].
      * exact (proj1 (Ts []) (bh_traces_nil _ _ _ _ _)).
      * exact (Tp (e :: tr) Ht ltac:(discriminate)).
    + intros Ht. exact (Vp p en_p inp Hpol Hpe Hin Hb tr Ht).
  - intros tr. split.
    + intros Ht. apply (Ts tr). exact (RoomShapesDraft.canon_trace_sub _ _ _ _ _ _ _ Ht).
    + intros Ht. apply (Cs p en_s inp Hpol Hse Hin). apply (Ts tr). exact Ht.
Qed.
