From Stdlib Require Import ZArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_knock Require Statements Images.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require RoomShapesDraft.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import Uniform.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
  YK0i YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  SlotAgree Agree AgreeTop AgreeZlib.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U Require AgreeZlib.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require SlotAgreeV AgreeZlibO.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U Require SlotAgreeV AgreeZlibO.
Import ListNotations.
Open Scope Z_scope.

Inductive canon_reach (p : RoomShapesDraft.policy) (segs : list Segment) (cfg : SpuriousCfg)
    : RoomShapesDraft.strip -> Z -> config -> RoomShapesDraft.strip -> Z -> config -> Prop :=
| cr_refl : forall s st c, canon_reach p segs cfg s st c s st c
| cr_step : forall s s' s'' st st' st'' c1 evs c2 c3,
    sstep_cfg segs cfg c1 evs (SNext c2) ->
    RoomShapesDraft.canonical_step p s st segs c1 c2 ->
    RoomShapesDraft.strip_next p segs c1 c2 s s' ->
    RoomShapesDraft.stack_next segs c1 c2 st st' ->
    canon_reach p segs cfg s' st' c2 s'' st'' c3 ->
    canon_reach p segs cfg s st c1 s'' st'' c3.

Definition fit_from (p : RoomShapesDraft.policy) (segs : list Segment) (s : RoomShapesDraft.strip) (st : Z)
    (c : config) : Prop :=
  forall s' st' c' x8 len, canon_reach p segs ACFG s st c s' st' c' ->
    RoomShapesDraft.placement_at segs c' x8 len ->
    (exists evs c'', sstep_cfg segs ACFG c' evs (SNext c'')) ->
    RoomShapesDraft.canon_can_step p s' st' segs ACFG c'.

Definition canon_fit (img : Image) (lim : Z) : Prop :=
  forall p en inp, RoomShapesDraft.policy_ok p -> valid_entry img en inp -> valid_input inp ->
  match img, en with
  | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
    let c0 := init_config segs pc ph sp brk0 mbase rnd lim inp in
    fit_from p segs RoomShapesDraft.full_strip (RoomShapesDraft.stack_low (m_vmmaps (cfg_model c0)) p) c0
  end.

Section Rz.
Variable segs : list Segment.

Lemma fit_from_here : forall p s st c x8 len, fit_from p segs s st c ->
  RoomShapesDraft.placement_at segs c x8 len -> (exists evs c', sstep_cfg segs ACFG c evs (SNext c')) ->
  RoomShapesDraft.canon_can_step p s st segs ACFG c.
Proof. intros p s st c x8 len H Hp He. exact (H s st c x8 len (cr_refl p segs ACFG s st c) Hp He). Qed.

Lemma fit_from_step : forall p s s' st st' c evs c', fit_from p segs s st c ->
  sstep_cfg segs ACFG c evs (SNext c') -> RoomShapesDraft.canonical_step p s st segs c c' ->
  RoomShapesDraft.strip_next p segs c c' s s' -> RoomShapesDraft.stack_next segs c c' st st' ->
  fit_from p segs s' st' c'.
Proof.
  intros p s s' st st' c evs c' H Hs Hc Hst Hk s2 st2 c2 x8 len Hr.
  exact (H s2 st2 c2 x8 len (cr_step p segs ACFG s s' s2 st st' st2 c evs c' c2 Hs Hc Hst Hk Hr)).
Qed.

Lemma canon_branch_fit : forall p s st c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet),
  node_ok segs c I evs nx -> (forall i, realizes segs (nx i) (T i)) -> cut_free segs c ->
  uniform segs c -> fit_from p segs s st c ->
  (forall i, cut_free segs (nx i) -> uniform segs (nx i) ->
     forall s' st', fit_from p segs s' st' (nx i) -> forall tr, T i tr ->
     exists tr' c', RoomShapesDraft.star_canon_fb p segs ACFG false s' st' (nx i) tr' c' /\ is_prefix tr tr') ->
  forall i tr, t_emit (evs i) (T i) tr ->
  exists tr' c', RoomShapesDraft.star_canon_fb p segs ACFG false s st c tr' c' /\ is_prefix tr tr'.
Proof.
  intros p s st c I evs nx T [Hcomp Hsound] Hcont NR HU HF IH i tr Htr.
  assert (GO : forall j, evs j = evs i -> (forall tr0, T i tr0 -> T j tr0) ->
      RoomShapesDraft.canonical_step p s st segs c (nx j) ->
      exists tr' c', RoomShapesDraft.star_canon_fb p segs ACFG false s st c tr' c' /\ is_prefix tr tr').
  { intros j Ee HT Hc.
    destruct (RoomShapesDraft.strip_next_total p segs c (nx j) s) as (s' & Hs').
    destruct (RoomShapesDraft.stack_next_total segs c (nx j) st) as (st' & Hst').
    assert (HF' : fit_from p segs s' st' (nx j)) by exact (fit_from_step p s s' st st' c (evs j) (nx j) HF (Hcomp j) Hc Hs' Hst').
    assert (Hd : false = true -> ~ RoomShapesDraft.unplaced_at segs c) by (intros E; discriminate E).
    destruct Htr as [Hp | (tr0 & -> & H0)].
    - exists (evs j ++ []), (nx j). split.
      + exact (RoomShapesDraft.scf_canon p segs ACFG false s s' st st' c (evs j) (nx j) [] (nx j) Hd (Hcomp j) Hc
          Hs' Hst' (RoomShapesDraft.scf_refl p segs ACFG false s' st' (nx j))).
      + rewrite app_nil_r, Ee. exact Hp.
    - destruct (IH j (cut_free_step segs c (evs j) (nx j) NR (Hcomp j)) (uniform_step segs c (evs j) (nx j) HU (Hcomp j))
                  s' st' HF' tr0 (HT tr0 H0)) as (tr' & c' & Hs & Hp).
      exists (evs j ++ tr'), c'. split.
      + exact (RoomShapesDraft.scf_canon p segs ACFG false s s' st st' c (evs j) (nx j) tr' c' Hd (Hcomp j) Hc
          Hs' Hst' Hs).
      + rewrite Ee. apply is_prefix_app_mono. exact Hp. }
  destruct (classic (exists x8 len, RoomShapesDraft.placement_at segs c x8 len)) as [(x8 & len & Hpl) | Hnp].
  - destruct (fit_from_here p s st c x8 len HF Hpl (ex_intro _ (evs i) (ex_intro _ (nx i) (Hcomp i))))
      as (e2 & c2 & Hs2 & Hc2).
    destruct (Hsound e2 (SNext c2) Hs2) as (j & -> & Ej). injection Ej as Ej. subst c2.
    destruct (uniform_here segs c HU x8 len Hpl (evs i) (nx i) (evs j) (nx j) (Hcomp i) (Hcomp j)) as (Ee & Hobs).
    apply (GO j (eq_sym Ee)); [| exact Hc2].
    intros tr0 H0.
    apply (proj1 (realizes_obs_iff segs (nx j) (T j) (Hcont j) (cut_free_step segs c (evs j) (nx j) NR (Hcomp j)) tr0)).
    apply (proj1 (Hobs tr0)).
    exact (proj2 (realizes_obs_iff segs (nx i) (T i) (Hcont i) (cut_free_step segs c (evs i) (nx i) NR (Hcomp i)) tr0) H0).
  - apply (GO i eq_refl (fun tr0 H0 => H0)).
    intros x8 len Hx. exfalso. apply Hnp. exists x8, len. exact Hx.
Qed.

Lemma canon_cover_fit : forall p c T, realizes segs c T -> cut_free segs c -> uniform segs c ->
  forall s st, fit_from p segs s st c -> forall tr, T tr ->
  exists tr' c', RoomShapesDraft.star_canon_fb p segs ACFG false s st c tr' c' /\ is_prefix tr tr'.
Proof.
  intros p c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq | c I nx T i0 Hnode Hcont IH | c T Hb];
    intros NR HU s st HF tr HT.
  - destruct HT as [i Hi]. exact (canon_branch_fit p s st c I evs nx T Hnode Hcont NR HU HF IH i tr Hi).
  - cbv [t_nil] in HT. subst tr. exists [], c. split; [apply RoomShapesDraft.scf_refl | apply is_prefix_nil].
  - cbn in Heq. exact (IH NR HU s st HF tr (proj2 (Heq tr) HT)).
  - destruct HT as [i Hi].
    apply (canon_branch_fit p s st c I (fun _ => []) nx T Hnode Hcont NR HU HF IH i tr).
    right. exists tr. split; [reflexivity | exact Hi].
  - exfalso. exact (cut_free_here segs c NR Hb).
Qed.

End Rz.

Lemma bh_traces_nil : forall cfg img lim en inp, bh_traces (run_scfg cfg img lim en inp) [].
Proof.
  intros cfg [segs pc ph] lim [sp brk0 mbase rnd] inp. cbn [run_scfg bh_traces]. unfold obs_trace_cfg.
  exists [], (init_config segs pc ph sp brk0 mbase rnd lim inp). split; [apply star_cfg_refl | apply is_prefix_nil].
Qed.

Theorem canon_spec_of_rz : forall img lim (T : TSet) p en inp,
  RoomShapesDraft.policy_ok p -> valid_entry img en inp -> valid_input inp ->
  rz_run img lim en inp T -> cf_run img lim en inp -> canon_fit img lim ->
  ~ RoomShapesDraft.guarded_reaches_error ACFG p img lim en inp
  /\ (forall tr, RoomShapesDraft.canon_trace ACFG p img lim en inp tr <-> T tr).
Proof.
  intros img lim T p en inp Hpol Hv Hi R C F.
  destruct (run_exact_of_rz img lim en inp T R (budget_of_cf_run img lim en inp C)) as [E Ts].
  split; [intros Hr; exact (E (RoomShapesDraft.guarded_reaches_error_sub _ _ _ _ _ _ Hr)) |].
  intros tr. split.
  - intros Ht. apply (Ts tr). exact (RoomShapesDraft.canon_trace_sub _ _ _ _ _ _ _ Ht).
  - intros Ht. pose proof (F p en inp Hpol Hv Hi) as F0.
    destruct img as [segs pc ph], en as [sp brk0 mbase rnd].
    cbn [rz_run cf_run run_scfg bh_traces] in R, C, Ts, F0 |- *. destruct C as [C U].
    cbn [RoomShapesDraft.canon_trace]. unfold RoomShapesDraft.canon_run.
    exact (canon_cover_fit segs p _ T R C U _ _ F0 tr Ht).
Qed.

Definition plain_canon_fit : Prop := canon_fit Images.plain Budgets.Standard.lim_source.

Definition ubsan_canon_fit : Prop := canon_fit Images.ubsan Budgets.Standard.lim_target.

Theorem agrees_room_of_runs : forall (T : ProcInput -> TSet),
  (forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
     rz_run Images.plain Budgets.Standard.lim_source en inp (T inp) /\
     cf_run Images.plain Budgets.Standard.lim_source en inp) ->
  (forall en inp, valid_entry Images.ubsan en inp -> valid_input inp ->
     rz_run Images.ubsan Budgets.Standard.lim_target en inp (T inp) /\
     cf_run Images.ubsan Budgets.Standard.lim_target en inp) ->
  plain_canon_fit -> ubsan_canon_fit ->
  RoomShapesDraft.agrees_in_room Env.alloc_forced_only Budgets.Standard.lim_source Budgets.Standard.lim_target
    Images.plain Images.ubsan.
Proof.
  intros T HP HS Fp Fs.
  apply (RoomShapesDraft.agrees_in_canon_of_spec _ _ _ _ _ (fun _ _ _ inp => T inp)).
  intros p en_p en_s inp Hpol Hpe Hse Hin _. cbv beta.
  destruct (HP en_p inp Hpe Hin) as [Rp Cp]. destruct (HS en_s inp Hse Hin) as [Rs Cs].
  destruct (canon_spec_of_rz Images.plain Budgets.Standard.lim_source _ p en_p inp Hpol Hpe Hin Rp Cp Fp) as [Ep Tp].
  destruct (canon_spec_of_rz Images.ubsan Budgets.Standard.lim_target _ p en_s inp Hpol Hse Hin Rs Cs Fs) as [Es Ts].
  exact (conj Ep (conj Es (conj Tp Ts))).
Qed.

Theorem ubsan_agrees_room_of_spec : forall (LS : lib_shape)
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
  plain_canon_fit -> ubsan_canon_fit ->
  RoomShapesDraft.agrees_in_room Env.alloc_forced_only Budgets.Standard.lim_source Budgets.Standard.lim_target
    Images.plain Images.ubsan.
Proof.
  intros LS G GI Gu GIu HG GIL GI0 Hp HROOM HGu GILu GI0u Hu Fp Fs.
  apply (agrees_room_of_runs (fun inp => SPECX (LS:=LS) inp)); [| | exact Fp | exact Fs].
  - intros en inp Hv Hi. exact (plain_crealizes_of_cg LS G GI HROOM HG GIL GI0 Hp en inp Budgets.Standard.lim_source
      Hv Hi ltac:(apply Z.leb_le; vm_compute; reflexivity)).
  - intros en inp Hv Hi. exact (U.AgreeZlib.ubsan_crealizes_of_cg LS Gu GIu HROOM HGu GILu GI0u Hu en inp
      Budgets.Standard.lim_target Hv Hi ltac:(apply Z.leb_le; vm_compute; reflexivity)).
Qed.

Theorem ubsan_agrees_room_of_spec_o : forall (LS : lib_shape) (f : list byte -> list byte)
    (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop)
    (Gu : list (Z * Z)) (GIu : nat -> (word -> option byte) -> Prop),
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @OSSVerify.Proofs.libreac.fuzz_knock.lib.SlotAgreeV.lib_contract_cgo fx rc LS src0_msyms
       (@zlib_API rc) src0_sink_head src0_sink
       f G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  (forall data, @room_calls LS (payload_len data) (calls data) U.AgreeZlib.SBD_AG) ->
  (forall a, U.Reusable.YL0g.in_globals Gu a -> U.Reusable.YL0g.in_globals U.FrameAPI.frame_G a) ->
  U.Contract.G_local_c U.Reusable.YH02.src0_msyms Gu GIu ->
  (forall mem, U.Contract.G_img_c U.Reusable.YH02.src0_msyms Gu mem -> GIu 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @U.SlotAgreeV.lib_contract_cgo fx rc LS U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)
       U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
       f Gu U.FrameAPI.frame_RELRO GIu j U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY
       U.FrameAPI.SLOT_STACK) ->
  plain_canon_fit -> ubsan_canon_fit ->
  RoomShapesDraft.agrees_in_room Env.alloc_forced_only Budgets.Standard.lim_source Budgets.Standard.lim_target
    Images.plain Images.ubsan.
Proof.
  intros LS f G GI Gu GIu HG GIL GI0 Hp HROOM HGu GILu GI0u Hu Fp Fs.
  apply (agrees_room_of_runs (fun inp => SPECX (LS:=LS) inp)); [| | exact Fp | exact Fs].
  - intros en inp Hv Hi.
    exact (OSSVerify.Proofs.libreac.fuzz_knock.lib.AgreeZlibO.plain_crealizes_of_cgo LS f G GI HROOM
      HG GIL GI0 Hp en inp
      Budgets.Standard.lim_source Hv Hi ltac:(apply Z.leb_le; vm_compute; reflexivity)).
  - intros en inp Hv Hi. exact (U.AgreeZlibO.ubsan_crealizes_of_cgo LS f Gu GIu HROOM HGu GILu GI0u Hu en inp
      Budgets.Standard.lim_target Hv Hi ltac:(apply Z.leb_le; vm_compute; reflexivity)).
Qed.
