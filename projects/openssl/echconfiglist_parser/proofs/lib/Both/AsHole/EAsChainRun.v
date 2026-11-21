(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (P_main is stated over AsanInitL's SINV0L; Section Chain takes the channel-reader and launch premises, with chain_launch for the holes; the realizes inductions carry the robustness premise); the chain is proved for walks with leaves (srealizes_of_cfg, cfg_of_srealizes, hole_srealizes and as_chain_srealizes_leaf are generic in the Leaf class and replace hole_realizes; as_chain_srealizes is its leaf_none case), for the run's walk from its own start in Both/AsHole/EAsChainRun.v; the trailing Check is dropped. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/echconfiglist_parser/lib/Both/AsHole/EAsChain.v: its walk from the run's start and the vDSO pair's lemmas, moved out unchanged; 5 of its 152 lines of code are new or changed and 121 lines of the source are left out; taken from projects/openssl/echconfiglist_parser/proofs/lib/Both/AsHole/EAsChain.v, lines 5-19, 27-30, 49-62, 90-106, 130-131, 161 and 185, as in the LPS 727298f3 update. *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the ASan+UBSan copy of [AsHole/EAsChainRun.v]: the run's
   walk from its own start ([as_chain_run]) and the launch's vDSO pair along the start-up ([vcm_run],
   [vcm_run_step], [vcm_run_init]), moved here from [Both/AsHole/EAsChain.v] unchanged, so that
   [EAsChain], and through it [Both/AsMainState] and every main-phase file, does not load the vDSO
   pair's libraries (with them, the global [lia] tuning of [Lib/LiaTuning.v]); [P_mainK], the main
   entry with what [as_chain_run] carries there, moved here from [Both/AsMainState]. *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxRel FxImage FxHandoff FxDrive FxDrive3.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec ShapeAlg SpinAlg Scfg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanInitL AsHSTab.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages EAsStartupHSA EAsS6State EAsStartupTop.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import CXI BrHole Br3Trans.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.AsHole Require Import ES6Start ES6End0 ES6End1 ES6End2 ES6End3 ES6End4 ES6End5 ES6Hole0 ES6Hole1 ES6Hole2 ES6Hole3 ES6Hole4 ES6Hole5 EAsChain.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both Require AsMainState.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Amb.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require RomBase RomStable.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import Leaf LeafLift KernOk.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require PinsOk MapsOff PairCleanAll.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require VdsoClean.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require MmVdso.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require VdsoLaunch.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As Require ASegs VdsoLaunch.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** * The launch's vDSO pair along the start-up

    The run's pair is the vvar entry [vd_lo, vd_mid) and the text entry [vd_mid, vd_top) of
    [Ref/VdsoLaunch.v].  [PairCleanAll.vcm_cfg] of each (the overlay holds none of its bytes, it
    is one of the launch's reserved pair, no map meets it, the pins are well formed;
    [AsDriverLaws.vcm2] at the launch's windows) holds at the launch ([vcm_run_init]) and every
    step over the binary's segments keeps it ([vcm_run_step]: [PairCleanAll.pc_step_clean], no
    segment of the binary reaching the pair). *)
Definition vcm_run (inp : ProcInput) (sp0 mbase : word) (c : config) : Prop :=
     PairCleanAll.vcm_cfg (Ref.VdsoLaunch.vd_lo (in_kernel inp) sp0 mbase)
       (Ref.VdsoLaunch.vd_mid (in_kernel inp) sp0 mbase) c
  /\ PairCleanAll.vcm_cfg (Ref.VdsoLaunch.vd_mid (in_kernel inp) sp0 mbase)
       (Ref.VdsoLaunch.vd_top sp0 mbase) c.

(* no segment of the binary holds a byte at or above its image's top *)
Lemma asegs_nw_win : forall wlo whi : Z, Both.As.ASegs.AIMG_TOP <= wlo -> forall (x : word) s,
  wlo <= bv_unsigned x < whi -> find_segment ASEGS (bv_unsigned x) 1 = Some s -> seg_writable s = false.
Proof.
  intros wlo whi HT x s Hx Hf. change ASEGS with Both.As.ASegs.asegs in Hf.
  rewrite (Both.As.VdsoLaunch.av_find_none (bv_unsigned x) 1 ltac:(lia) ltac:(lia)) in Hf. discriminate Hf.
Qed.

Lemma vcm_run_step : forall inp (sp0 mbase : word), valid_sp sp0 -> valid_mmap_base mbase ->
  forall c evs c', vcm_run inp sp0 mbase c -> sstep_cfg ASEGS the_scfg c evs (Run.SNext c') ->
  vcm_run inp sp0 mbase c'.
Proof.
  intros inp sp0 mbase Hsp Hmb c evs c' [V1 V2] Hs.
  assert (LB : Both.As.ASegs.AIMG_TOP <= Ref.VdsoLaunch.vd_lo (in_kernel inp) sp0 mbase)
    by (eapply proj1; eapply Both.As.VdsoLaunch.av_lo_bounds; first [exact Hsp | exact Hmb]).
  assert (LM : Ref.VdsoLaunch.vd_lo (in_kernel inp) sp0 mbase <= Ref.VdsoLaunch.vd_mid (in_kernel inp) sp0 mbase)
    by (eapply proj1; eapply Both.As.VdsoLaunch.av_order; first [exact Hsp | exact Hmb]).
  split.
  - exact (PairCleanAll.pc_step_clean ASEGS _ _
             (asegs_nw_win (Ref.VdsoLaunch.vd_lo (in_kernel inp) sp0 mbase)
                (Ref.VdsoLaunch.vd_mid (in_kernel inp) sp0 mbase) LB) the_scfg c evs c' Hs V1).
  - exact (PairCleanAll.pc_step_clean ASEGS _ _
             (asegs_nw_win (Ref.VdsoLaunch.vd_mid (in_kernel inp) sp0 mbase)
                (Ref.VdsoLaunch.vd_top sp0 mbase) ltac:(lia)) the_scfg c evs c' Hs V2).
Qed.

(* At the launch: the entry memory ([PropExec.wrap_mem]) has no byte below the stack's window
   ([Run.stack_window_lo], at or above the mmap base) and below [sp]; the model's ledger is
   [State.vm_reserved_init_model] with the pair at [State.vdso_top_init_model], as
   [RefTop.pair_inv_model0] reads it; the launch maps nothing; the pins are [PinsOk.pins_ok_init]. *)
Lemma vcm_run_init : forall vsegs pc ph (sp brk0 mbase : word) rnd lim inp,
  valid_sp sp -> valid_mmap_base mbase ->
  vcm_run inp sp mbase (init_config vsegs pc ph sp brk0 mbase rnd lim inp).
Proof.
  intros vsegs pc ph sp brk0 mbase rnd lim inp Hsp Hmb.
  set (top := Ref.VdsoLaunch.vd_top sp mbase).
  assert (TF : top mod 4096 = 0 /\ Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size) - 8192 < top
               /\ top <= bv_unsigned mbase /\ top <= bv_unsigned sp - stack_max_size)
    by (unfold top; eapply Ref.VdsoLaunch.top_facts; first [exact Hsp | exact Hmb]).
  assert (MT : Ref.VdsoLaunch.vd_mid (in_kernel inp) sp mbase + 8192 = top)
    by (unfold top; eapply Ref.VdsoLaunch.mid_top; first [exact Hsp | exact Hmb]).
  assert (SM : 0 <= stack_max_size) by (unfold stack_max_size; lia).
  set (c0 := init_config vsegs pc ph sp brk0 mbase rnd lim inp).
  set (mo0 := init_model (segments_reserved vsegs) brk0 mbase sp lim inp).
  assert (EK : m_kernel (cfg_model c0) = in_kernel inp)
    by (unfold c0, init_config; cbn [cfg_model]; rewrite m_kernel_with_vdso; apply m_kernel_init_model).
  assert (EV : m_vmmaps (cfg_model c0) = m_vmmaps mo0)
    by (unfold c0, mo0, init_config; cbn [cfg_model]; apply m_vmmaps_with_vdso).
  assert (ET0 : vdso_top (m_vmmaps mo0) = top).
  { unfold mo0, top. rewrite vdso_top_init_model. unfold Ref.VdsoLaunch.vd_top. symmetry. apply page_round_down_Z_min_r. }
  assert (ET : vdso_top (m_vmmaps (cfg_model c0)) = top) by (rewrite EV; exact ET0).
  assert (ER : vm_reserved (m_vmmaps (cfg_model c0)) = segments_reserved vsegs ++ vdso_reserved (in_kernel inp) top).
  { rewrite EV. unfold mo0. rewrite vm_reserved_init_model. fold mo0. rewrite ET0. reflexivity. }
  assert (EM : vm_maps (m_vmmaps (cfg_model c0)) = []) by (rewrite EV; reflexivity).
  assert (VC : forall w1 w2, w2 <= top -> VdsoClean.vclean w1 w2 (ms_mem (cfg_ms c0))).
  { intros w1 w2 Hw x Hx.
    change (wrap_mem inp mbase ph (Z_to_bv 64 (Z.of_N pc)) sp rnd x = None).
    unfold wrap_mem.
    replace (stack_to_mem sp (entry_stack_image inp mbase ph (Z_to_bv 64 (Z.of_N pc)) sp rnd) x) with (@None byte)
      by (symmetry; unfold stack_to_mem;
          replace (Z.leb (bv_unsigned sp) (bv_unsigned x)) with false by (symmetry; apply Z.leb_gt; lia);
          reflexivity).
    assert (G : 0 <= stack_guard_gap_bytes (in_kernel inp)).
    { unfold stack_guard_gap_bytes. pose proof (stack_guard_gap_pages_bounds (in_kernel inp)).
      apply Z.mul_nonneg_nonneg; [vm_compute; discriminate | lia]. }
    replace (Z.leb (stack_window_lo (in_kernel inp) mbase rnd) (bv_unsigned x)) with false
      by (symmetry; apply Z.leb_gt; unfold stack_window_lo; lia).
    reflexivity. }
  assert (W1 : MmVdso.win_in (Ref.VdsoLaunch.vd_lo (in_kernel inp) sp mbase) (Ref.VdsoLaunch.vd_mid (in_kernel inp) sp mbase)
                 (vdso_reserved (in_kernel inp) top))
    by (unfold top; eapply Ref.VdsoLaunch.pair_win_lo; eassumption).
  assert (W2 : MmVdso.win_in (Ref.VdsoLaunch.vd_mid (in_kernel inp) sp mbase) top (vdso_reserved (in_kernel inp) top))
    by (unfold top; eapply Ref.VdsoLaunch.pair_win_hi; eassumption).
  assert (I : incl (vdso_reserved (in_kernel inp) top) (vm_reserved (m_vmmaps (cfg_model c0))))
    by (rewrite ER; intros e He; apply in_or_app; right; exact He).
  pose proof (PinsOk.pins_ok_init vsegs pc ph sp brk0 mbase rnd lim inp) as PO. fold c0 in PO.
  unfold vcm_run, PairCleanAll.vcm_cfg, MmVdso.vc_cfg, MmVdso.mm_vinv, MapsOff.maps_off.
  fold top. rewrite EK, ET, EM.
  split; (split; [split; [apply VC; lia | split; [first [exact W1 | exact W2] | exact I]] | split; [constructor | exact PO]]).
Qed.


(* the main entry with the run's kernel build and mmap base, and the launch's vDSO pair clean,
   reserved and met by no map with the pins well formed ([vcm_run]): the launch makes them and
   every step keeps them, so [as_chain_run] carries them to the main entry ([KernOk.kern_step],
   [vcm_run_step], [LeafLift.srz_inv]); the instance reads them at the vDSO pair *)
Definition P_mainK (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config) : Prop :=
  Both.AsMainState.P_main sp0 brk0 mbase rdraw inp c /\ kern_ok (in_kernel inp) mbase (cfg_model c) /\ vcm_run inp sp0 mbase c.

Section Chain.
  Variables sp0 brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp0.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hfit : entry_stack_fits sp0 (in_argv inp) (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).
  (* 08b1429: [Run.valid_input]'s reader clause *)
  Hypothesis Hrdr : in_channel_reader inp = true.
  (** #38: [Run.valid_input]'s launch clause and [Run.valid_entry]'s fifth conjunct *)
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp.

  (** The run's walk from its own start, over [run_segments ASEGS inp sp0 mbase] = [ASEGS] and
      the launch's vDSO pair.  The start-up and the S6 holes stay over [ASEGS], where their
      certificates are computed; the main entry's continuation [MAINR] is over the run's list,
      from the main entry's configuration with that list's read-only view, and is their leaf
      ([LeafLift.leaf_run]); [LeafLift.srz_lift] lifts the whole walk.  [MAINR] also reads, at
      the main entry, the run's kernel build and mmap base and the launch's vDSO pair clean,
      reserved and met by no map, with the pins well formed: the launch makes them
      ([KernOk.kern_ok_init], [vcm_run_init]) and every step keeps them ([KernOk.kern_step],
      [vcm_run_step]), so [LeafLift.srz_inv] carries them to every leaf. *)
  Section Run.
    Variable T : ShapeAlgBase.TSet.
    Hypothesis T_nil : T [].
    Hypothesis MAINR : forall c, P_main sp0 brk0 mbase rdraw inp c ->
      kern_ok (in_kernel inp) mbase (cfg_model c) -> vcm_run inp sp0 mbase c ->
      ShapeAlg.realizes (ASEGS ++ vdso_segments (in_kernel inp) sp0 mbase)
        (RomBase.cwrom c (seg_rom (ASEGS ++ vdso_segments (in_kernel inp) sp0 mbase))) T.

    (** [Proof using All]: the arity is the Section's premises, then [T], [T_nil], [MAINR] *)
    Theorem as_chain_run :
      ShapeAlg.realizes (run_segments ASEGS inp sp0 mbase)
        (init_config (run_segments ASEGS inp sp0 mbase) AsanUbsan.M.init_pc APH sp0 brk0 mbase rdraw AsanInit.LIMIT inp) T.
    Proof using All.
      rewrite RomStable.init_config_run_segments.
      change (run_segments ASEGS inp sp0 mbase) with (ASEGS ++ vdso_segments (in_kernel inp) sp0 mbase).
      change (RomStable.seg_rom1 (ASEGS ++ vdso_segments (in_kernel inp) sp0 mbase))
        with (seg_rom (ASEGS ++ vdso_segments (in_kernel inp) sp0 mbase)).
      apply (srz_lift ASEGS (vdso_segments (in_kernel inp) sp0 mbase)
               (RomStable.vdso_segments_nx (in_kernel inp) sp0 mbase)
               (RomStable.vdso_segments_nw (in_kernel inp) sp0 mbase) ASEGS_vdso_none).
      - apply (srz_inv ASEGS (fun c => kern_ok (in_kernel inp) mbase (cfg_model c) /\ vcm_run inp sp0 mbase c)).
        + intros c evs c' [Hk Hp] Hs. split.
          * exact (kern_step (in_kernel inp) mbase ASEGS the_scfg c evs c' Hs Hk).
          * exact (vcm_run_step inp sp0 mbase Hsp Hmb c evs c' Hp Hs).
        + apply as_chain_srealizes_leaf; try assumption.
          intros c Hc. apply srz_leaf. hnf. split; [exact T_nil |]. intros [Hk Hp].
          hnf. split; [reflexivity |]. split; [| exact (MAINR c Hc Hk Hp)].
          destruct Hc as [_ (h & ch & E & R & FULL & m & _ & _ & -> & _)].
          exact (rom_ext_seg_rom_app ASEGS (vdso_segments (in_kernel inp) sp0 mbase)).
        + split.
          * exact (kern_ok_init ASEGS AsanUbsan.M.init_pc APH sp0 brk0 mbase rdraw AsanInit.LIMIT inp).
          * exact (vcm_run_init ASEGS AsanUbsan.M.init_pc APH sp0 brk0 mbase rdraw AsanInit.LIMIT inp Hsp Hmb).
      - rewrite RomStable.init_config_rom.
        exact (rom_ext_seg_rom_app ASEGS (vdso_segments (in_kernel inp) sp0 mbase)).
    Qed.
  End Run.
End Chain.
