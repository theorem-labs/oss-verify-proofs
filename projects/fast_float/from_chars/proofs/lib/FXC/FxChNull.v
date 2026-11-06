(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxRgs FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.

Module FxChSeg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg AsanAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep FxPlan FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Seg.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
#[using="HH Hwx"] Theorem rzc_fx_check_acct : forall t img ins depth p S finals A E ms model T,
  tbl_ok segs t -> img_ok segs img -> check t img ins depth p S = Some finals ->
  sden segs E S (restrict H ms) ->
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
  (forall L E' msr' model', In L finals -> sden segs E' L msr' -> (forall x, In x ins -> E' x = E x) ->
      MInv A model' -> same_but_materialized model model' -> hclean H msr' ->
      realizes_cfg segs cfg (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (HH Hwx : LiaFast.U) => LiaFast.u0).
  intros t img ins depth p S finals A E ms model T Ht Himg Hck Hden Hcov Hwf Hinv Hh Hk.
  destruct (check_sound segs t img ins depth p S finals Ht Himg Hck E (restrict H ms) Hden) as (L & msr' & E' & HL & Hst & Hd' & Hi).
  apply (rzc_fx_isteps segs cfg H HH Hwx A (restrict H ms) msr' ms model T eq_refl Hcov Hwf Hinv Hh Hst).
  intros model' Hinv' Hsb' Hcl'. exact (Hk L E' msr' model' HL Hd' Hi Hinv' Hsb' Hcl').
Qed.

(* [comment removed for export] *)
#[using="HH Hwx"] Theorem rzc_fx_ecall_acct : forall t A E L msr ms model T,
  ecall_ok segs t -> tlookup t (s_pc L) = XEcall -> sden segs E L msr ->
  restrict H ms = msr ->
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
      realizes_cfg segs cfg (mkCfg (unrestrict H (ms_mem ms) (svc_set msr)) model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (HH Hwx : LiaFast.U) => LiaFast.u0).
  intros t A E L msr ms model T Ht Hx Hd Hr Hcov Hwf Hinv Hh Hk.
  destruct (fx_ecall_step segs t E L msr Ht Hx Hd) as [Hstep Hsvc].
  assert (Hst : FxStep.isteps segs msr (svc_set msr)) by (eapply ist_step; [exact Hsvc | exact Hstep | apply ist_refl]).
  apply (rzc_fx_isteps segs cfg H HH Hwx A msr (svc_set msr) ms model T Hr Hcov Hwf Hinv Hh Hst).
  intros model' Hinv' Hsb' _. exact (Hk model' Hinv' Hsb').
Qed.
End Seg.
End FxChSeg.


Module FxChNode.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Fork.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxRgs FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Instance chn_fx : FPState := fx0.

Section Node.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
#[using="Type"] Lemma den_sbm : forall E S M ms model model',
  DEN segs LIMIT model0 mem0 E S M ms model -> same_but_materialized model model' -> MInv (AM model0 E M) model' ->
  DEN segs LIMIT model0 mem0 E S M ms model'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model model' Hd Hsb Hinv'.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  destruct (same_but_materialized_frame model model' Hsb) as (Hfd & Hvm & Hlz & Hio & Hfs & Hpr & Hli & Htm & _ & _ & _ & _ & Hhl & Htd & _).
  assert (HH : Hof E M model' = Hof E M model) by (unfold Hof; rewrite Hlz; reflexivity).
  constructor; rewrite ?HH, ?Hvm, ?Hlz, ?Hhl, ?Htd, ?Hpr; try assumption.
  - unfold kind_ok in *. rewrite Forall_forall in *. intros g Hg. rewrite Hvm, Hlz. exact (Hkind g Hg).
  - unfold rl_ok, app_pt in *. rewrite Forall_forall in *. intros R HR. rewrite Hvm. exact (Hrl R HR).
  - destruct Hvmo as (H1 & H2 & H3 & H4 & H5). rewrite Hfd, Hio, Hfs, Hli, Htm. repeat split; assumption.
  - intros q Hq w Hw. destruct (Hown q Hq w Hw) as [Hv Hm]. split; [rewrite HH; exact Hv | exact Hm].
  - exact (blob_ok_same E M M model model' _ eq_refl (f_equal alloc_top Hvm) Hblob).
Qed.

(* [comment removed for export] *)
#[using="Hwx"] Theorem den_ecall : forall t E L M ms model T,
  ecall_ok segs t -> tlookup t (s_pc L) = XEcall ->
  DEN segs LIMIT model0 mem0 E L M ms model ->
  (forall model', DEN segs LIMIT model0 mem0 E L M ms model' -> realizes_cfg segs cfg (mkCfg (svc_set ms) model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros t E L M ms model T Hect Hx Hd Hk. pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf _ Hminv Hhoff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  set (H := Hof E M model) in *.
  assert (Hcov : lazy_cover H (m_vm_lazy model) (AM model0 E M)) by (apply lazy_cover_mkH_app; intros x Hx'; exact Hx').
  apply (rzc_fx_ecall_acct segs cfg H Hhoff Hwx t (AM model0 E M) E L (restrict H ms) ms model T Hect Hx Hsd eq_refl Hcov (A_wf_app _ _ Hawf (A_wf_blobA _)) Hminv Hh).
  intros model' Hinv' Hsb'. rewrite unrestrict_svc. apply Hk. exact (den_sbm E L M ms model model' Hd Hsb' Hinv').
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_sys_na : forall ms model x8 (I : Type)
    (EF : I -> SyscallEffect) (MD : I -> Model) (EV : I -> list event) (T : I -> TSet) (i0 : I),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall j, syscall_spec (sys_input segs ms x8) model (Ok (EF j) (MD j) (EV j))) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     exists j, eff = EF j /\ m' = MD j /\ evs = EV j) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff, ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff) ->
  (forall j, m_halted (MD j) = None) ->
  (forall j, syscall_effect_accesses (EF j) = []) ->
  (forall j, realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms (EF j))) (MD j)) (T j)) ->
  realizes_cfg segs cfg (mkCfg ms model) (t_alt (fun j => t_emit (EV j) (T j))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model x8 I EF MD EV T i0 Hh Hsvc Hcomp Hsound Hnu Hns HhM Hacc HK.
  apply (rzc_node segs cfg (mkCfg ms model) I EV
           (fun j => mkCfg (advance_past_svc (apply_effect ms (EF j))) (MD j)) T i0); [| exact HK].
  apply (node_sys_cfg segs cfg ms model x8 I EF MD MD EV Hh Hsvc Hcomp); try assumption.
  - intros j. apply Hns.
  - intros eff m' evs Hs _. exact (Hsound eff m' evs Hs).
  - intros eff m' evs Hs. destruct (Hsound eff m' evs Hs) as (j & _ & -> & _). apply HhM.
  - intros j. rewrite Hacc. apply materialize_nil.
Qed.

(* [comment removed for export] *)
Definition post_fresh (L : sst) (fs : lin -> list fact) : sst :=
  SST (s_pc L + 4) (rset (s_regs L) (rkey a0r) (lvar (s_next L))) (s_rgs L) (fs (lvar (s_next L)) ++ s_facts L)
      (Pos.succ (s_next L)) (s_resv L).
Definition sm_with_tid (M : smodel) (l : lin) : smodel :=
  SM (sm_maps M) (sm_allow M) (sm_zr M) (Some l) (sm_brk M) (sm_sbrk M) (sm_sp M) (sm_frz M) (sm_own M).
Definition TID_FACTS (x : lin) : list fact := [FRange x 1 (2 ^ 22 - 1)].

#[using="Type"] Lemma with_tid_vmmaps : forall t m, m_vmmaps (with_tid t m) = m_vmmaps m. Proof. LiaFast.lf_pins LiaFast.u0. intros t m; destruct m; reflexivity. Qed.
#[using="Type"] Lemma with_tid_mat : forall t m, m_vm_materialized (with_tid t m) = m_vm_materialized m. Proof. LiaFast.lf_pins LiaFast.u0. intros t m; destruct m; reflexivity. Qed.
#[using="Type"] Lemma with_tid_tid : forall t m, m_tid (with_tid t m) = Some t. Proof. LiaFast.lf_pins LiaFast.u0. intros t m; destruct m; reflexivity. Qed.
#[using="Type"] Lemma eager_used_with_tid : forall t m, eager_used (with_tid t m) = eager_used m. Proof. LiaFast.lf_pins LiaFast.u0. intros t m; destruct m; reflexivity. Qed.

#[using="Type"] Lemma MInv_with_tid : forall A t m, MInv A m -> MInv A (with_tid t m).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros A t m [H1 H2 H3 H4 H5]. constructor; rewrite ?with_tid_mat, ?with_tid_lazy, ?with_tid_vmmaps, ?eager_used_with_tid; assumption.
Qed.

#[using="Type"] Theorem den_set_tid : forall E L M ms model T,
  DEN segs LIMIT model0 mem0 E L M ms model -> sm_tid M = None ->
  is_const (rget (s_regs L) (rkey (Z_to_bv 5 17))) = Some 96 ->
  (forall E' ms' model', DEN segs LIMIT model0 mem0 E' (post_fresh L TID_FACTS) (sm_with_tid M (lvar (s_next L))) ms' model' ->
      agree (s_next L) E E' -> realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E L M ms model T Hd HtM H17 Hk. pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htd Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  rewrite HtM in Htd. cbn [option_map] in Htd.
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  set (x8 := ms_reg ms 17).
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc0 & Hsv0 & Hrv0 & HR0 & _ & _ & _ & Hfrm0).
  assert (Hx8 : x8 = Z_to_bv 64 96).
  { destruct (is_const_sound E _ 96 H17) as [H17' _]. specialize (HR0 (Z_to_bv 5 17)).
    unfold x8, ms_reg. cbn in HR0 |- *. rewrite <- H17', <- HR0. reflexivity. }
  assert (Hno : bv_unsigned (in_sysno (sys_input segs ms1 x8)) = 96%Z) by (cbn; rewrite Hx8; reflexivity).
  assert (Hsp' : forall o, syscall_spec (sys_input segs ms1 x8) model o <-> set_tid_address_spec (sys_input segs ms1 x8) model o)
    by (intro o; exact (syscall_spec_no _ _ _ 96 _ Hno eq_refl)).
  set (I := {v : word | (0 < bv_unsigned v < PID_MAX_ENVELOPE)%Z}).
  assert (i0 : I) by (exists (Z_to_bv 64 1); split; vm_compute; reflexivity).
  assert (Hcont : forall j : I, realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms1 (mkEffect (proj1_sig j) [] [])))
                                                        (with_tid (proj1_sig j) model)) T).
  { intros [v Hv]. cbn [proj1_sig].
    set (E' := upd E (s_next L) v).
    assert (Ha : agree (s_next L) E E') by apply agree_upd.
    apply (Hk E' _ _); [|exact Ha].
    assert (HA : allowA E' (sm_with_tid M (lvar (s_next L))) = allowA E M) by exact (allowA_agree (s_next L) E E' M Hwf Ha).
    assert (HH : Hof E' (sm_with_tid M (lvar (s_next L))) (with_tid v model) = H) by (unfold Hof, H; rewrite with_tid_lazy, HA; reflexivity).
    assert (Hwf' : sm_wf (Pos.succ (s_next L)) (sm_with_tid M (lvar (s_next L))) = true).
    { destruct (sm_wf_parts (s_next L) M Hwf) as (Hwg & Hwa & _ & Hwb & Hwsb & Hwsp). pose proof (sm_wf_frz _ M Hwf) as Hwz.
      assert (Hlv : lwf (Pos.succ (s_next L)) (lvar (s_next L)) = true) by (unfold lwf, lvar; cbn; rewrite andb_true_r; apply Pos.ltb_lt; lia).
      apply sm_wf_intro; cbn [sm_maps sm_allow sm_tid sm_brk sm_sbrk sm_sp sm_frz sm_own sm_with_tid];
        try (apply (lwf_mono (s_next L)); [lia | assumption]).
      - exact (sm_wf_maps_mono (s_next L) (Pos.succ (s_next L)) M Hwf ltac:(lia)).
      - apply (Forall_lwf_mono _ (s_next L)); [lia | exact Hwa].
      - exact Hlv.
      - apply (Forall_frz_mono (s_next L)); [lia | exact Hwz].
      - apply (Forall_frz_mono (s_next L)); [lia | exact (sm_wf_own _ M Hwf)]. }
    destruct (sm_wf_parts (s_next L) M Hwf) as (Hwg & Hwa & _ & Hwb & Hwsb & Hwsp).
    constructor.
    - rewrite HH. unfold ms1. rewrite (restrict_adv_eff H ms v [] [] [] (s_pc L)) by exact Hpc0.
      cbn [apply_zeros apply_unmaps].
      destruct (res_sound_gen segs E L (restrict H ms) a0r None TID_FACTS (s_pc L + 4) v (ms_fregs ms) (ms_fcsr ms) (s_resv L) (ms_resv ms) Hsd)
        as (E2 & Ha2 & _ & Hs2).
      + intros E'' _ _ l Hl. discriminate.
      + intros E'' _ Hv''. unfold TID_FACTS. constructor; [|constructor]. cbn [fact_ok]. rewrite lden_lvar, Hv''.
        unfold PID_MAX_ENVELOPE in Hv. lia.
      + exact Hfrm0.
      + intros E'' Ha''. destruct (Hsd E'' Ha'') as (_ & _ & Hrv & _). exact Hrv.
      + rewrite with_resv_same in Hs2. unfold set_res in Hs2. cbn [s_next] in Hs2.
        assert (HE2 : E2 (s_next L) = v).
        { destruct (sden_0 _ _ _ _ Hs2) as (_ & _ & _ & HR2 & _). specialize (HR2 a0r). cbn [s_regs mks ms_regs] in HR2.
          rewrite rget_rset_same in HR2 by (unfold a0r, rkey; discriminate). rewrite lden_lvar in HR2.
          unfold rupd in HR2. assert (E10 : bv_eqb a0r 0 = false) by reflexivity. rewrite E10 in HR2.
          rewrite getr_same in HR2 by (unfold a0r; discriminate). symmetry. exact HR2. }
        intros E'' Ha''. apply Hs2. intros x Hx. rewrite <- (Ha'' x Hx).
        unfold E'. destruct (Pos.eqb_spec x (s_next L)) as [->|Hne].
        * unfold upd. rewrite Pos.eqb_refl. exact HE2.
        * unfold upd. rewrite (proj2 (Pos.eqb_neq x (s_next L)) Hne). symmetry. apply Ha2. cbn [s_next] in Hx. lia.
    - exact Hwf'.
    - cbn [post_fresh s_next s_rgs]. eapply bases_wf_shape; [|reflexivity|exact Hbw]. lia.
    - rewrite with_tid_halted. exact Hh.
    - rewrite HA. exact Hawf.
    - exact Hanz.
    - unfold AM. rewrite HA. exact (MInv_with_tid _ v _ Hminv).
    - rewrite HH. exact Hhoff.
    - rewrite with_tid_vmmaps. exact Hres.
    - rewrite with_tid_vmmaps. exact Hlim.
    - rewrite with_tid_vmmaps, Hsp. cbn [sm_with_tid sm_sp]. symmetry. exact (lden_agree_wf _ E E' _ Hwsp Ha).
    - rewrite with_tid_vmmaps. exact Hspok.
    - rewrite with_tid_vmmaps, Hbrk. cbn [sm_with_tid sm_brk]. symmetry. exact (lden_agree_wf _ E E' _ Hwb Ha).
    - rewrite with_tid_vmmaps, Hsbrk. cbn [sm_with_tid sm_sbrk]. symmetry. exact (lden_agree_wf _ E E' _ Hwsb Ha).
    - rewrite with_tid_tid. cbn [sm_with_tid sm_tid option_map]. rewrite lden_lvar. unfold E', upd. rewrite Pos.eqb_refl. reflexivity.
    - rewrite with_tid_vmmaps, Hmaps. cbn [sm_with_tid sm_maps]. symmetry. exact (lden_maps_agree _ E E' _ M Hwf Ha).
    - apply (Forall_agree_maps (s_next L) E E' M gshape_ok Hwf Ha); [|exact Hgsh].
      intros g Hg Hgs. unfold gshape_ok, gsz, uE. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
    - apply (Forall_agree_maps (s_next L) E E' M (fun E g => uE E (fst (fst g)) + gsz E g <= alloc_top (m_vmmaps (with_tid v model))) Hwf Ha).
      + intros g Hg Hgs. unfold gsz, uE. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
      + rewrite with_tid_vmmaps. exact Hgtop.
    - rewrite with_tid_vmmaps, with_tid_lazy. exact Hivwf.
    - rewrite with_tid_vmmaps. exact Hpd.
    - rewrite with_tid_vmmaps. exact Hmres.
    - apply (Forall_agree_maps (s_next L) E E' M (fun E g => kind_ok E (with_tid v model) g) Hwf Ha).
      + intros g Hg Hgs. unfold kind_ok, gden. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
      + unfold kind_ok. rewrite with_tid_vmmaps, with_tid_lazy. exact Hkind.
    - rewrite with_tid_lazy, with_tid_vmmaps. exact Hlzm.
    - exact Hzrsh.
    - rewrite with_tid_vmmaps. exact Hzrm.
    - intros w Hw Hout Hnow Hnb. unfold ms1. rewrite adv_eff_mem. cbn [apply_zeros apply_unmaps ms_mem svc_set].
      apply (Hzr w Hw); [exact (outside_agree_shape (s_next L) E E' (s_rgs L) (s_rgs L) _ Hbw Ha eq_refl Hout) | | exact Hnb].
      exact (own_pt_keep _ E E' M (sm_with_tid M (lvar (s_next L))) w Hwf Ha eq_refl Hnow).
    - exact (rl_ok_agree_shape (s_next L) E E' model (with_tid v model) (s_rgs L) (s_rgs L) Hbw Ha eq_refl (with_tid_vmmaps v model) Hrl).
    - destruct Hvmo as (H1 & H2 & H3 & H4 & H5). destruct model. cbn in *. repeat split; assumption.
    - rewrite with_tid_tid. rewrite Htd in Hproc. unfold with_tid. cbn [m_proc]. unfold m_halted, m_creds, m_setsid_succeeded, m_sigmask,
        m_utsname, m_sigaltstack_installed, m_sigabrt_pending, m_abort_terminal, m_statpins. rewrite Hproc. reflexivity.
    - apply (frz_keep mem0 E E' L (post_fresh L TID_FACTS) M (sm_with_tid M (lvar (s_next L))) ms _ model (with_tid v model) Hwf Ha eq_refl);
        [rewrite with_tid_vmmaps; reflexivity | | | exact Hfrz].
      + intros w _ Ho. cbn [post_fresh s_rgs]. apply (proj1 (outside_agree (s_next L) E E' (s_rgs L) _ Hbw Ha)). exact Ho.
      + intros w _ _. unfold ms1. rewrite adv_eff_mem. reflexivity.
    - rom_tac.
    - apply (own_keep mem0 E E' L (post_fresh L TID_FACTS) M (sm_with_tid M (lvar (s_next L))) ms _ model (with_tid v model) Hwf Ha eq_refl);
        [| | | exact Hown].
      + intros w Ho. cbn [post_fresh s_rgs] in Ho. exact (proj2 (outside_agree (s_next L) E E' (s_rgs L) _ Hbw Ha) Ho).
      + intros w _. unfold ms1. rewrite adv_eff_mem. reflexivity.
      + intros x Hx. rewrite HH. exact Hx.
    - apply (blob_ok_step (s_next L) E E' M _ model _ _ Hwf Ha eq_refl); [rewrite with_tid_vmmaps; reflexivity | exact Hblob]. }
  eapply rzc_conseq.
  - apply (rzc_sys_na ms1 model x8 I (fun j => mkEffect (proj1_sig j) [] [])
             (fun j => with_tid (proj1_sig j) model) (fun _ => []) (fun _ => T) i0);
      [exact Hh | reflexivity | | | | | | | exact Hcont].
    + intros [v Hv]. apply Hsp'. apply set_tid_fresh_ok; [exact Htd|]. exists v. auto.
    + intros eff m' evs Hs. apply Hsp' in Hs. apply set_tid_fresh_ok in Hs as (v & Hv & -> & -> & ->); [|exact Htd].
      exists (exist _ v Hv). auto.
    + intros Hs. apply Hsp' in Hs. exact (set_tid_fresh_unmodeled _ _ Htd Hs).
    + intros eff. apply not_spurious_uninjected. rewrite Hno. reflexivity.
    + intros j. rewrite with_tid_halted. exact Hh.
    + intros j. reflexivity.
  - apply t_alt_const_nil; [exact i0|]. exact (realizes_cfg_nonempty segs cfg _ _ (Hcont i0)).
Qed.
End Node.
End FxChNode.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition TOPW : Z := 0x7fffff800000.
Definition LS_B : Z := 0x7fff7000.      Definition LS_K : Z := 0x10000000.
Definition GAP_B : Z := 0x8fff7000.     Definition GAP_K : Z := 0x20000000000.
Definition HS_B : Z := 0x2008fff7000.   Definition HS_K : Z := 0xdfff0001000.

Definition has_const_grant (gs : list (lin * lin * gkind)) (b k : Z) : bool :=
  existsb (fun g => match is_const (fst (fst g)), is_const (snd (fst g)) with Some c, Some z => Z.eqb c b && Z.eqb z k | _, _ => false end) gs.
Definition shadow_ok (M : smodel) : bool :=
  (has_const_grant (sm_maps M) LS_B LS_K && has_const_grant (sm_maps M) GAP_B GAP_K && has_const_grant (sm_maps M) HS_B HS_K)%bool.
Definition zr_has (zr : list (Z * Z)) (lo hi : Z) : bool := existsb (fun p => (fst p <=? lo) && (hi <=? snd p)) zr.
Definition zr_ok (M : smodel) : bool := (zr_has (sm_zr M) LS_B (LS_B + LS_K) && zr_has (sm_zr M) HS_B (HS_B + HS_K))%bool.

(* [comment removed for export] *)
Lemma u_lt : forall w : word, 0 <= bv_unsigned w < two64.
Proof. intros w. exact (bv_unsigned_in_range _ w). Qed.

Lemma fg64 : forall z, 0 <= z < two64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply fg_lit. unfold two64 in Hz. change (2 ^ 64) with 18446744073709551616. lia. Qed.

Lemma has_const_grant_In : forall E gs b k, has_const_grant gs b k = true ->
  exists g, In g gs /\ gden E g = (Z_to_bv 64 b, Z_to_bv 64 k).
Proof.
  intros E gs b k H. unfold has_const_grant in H. apply existsb_exists in H as (g & Hin & Hc).
  destruct (is_const (fst (fst g))) as [c|] eqn:Ec; [|discriminate]. destruct (is_const (snd (fst g))) as [z|] eqn:Ez; [|discriminate].
  apply andb_prop in Hc as [H1 H2].
  apply Z.eqb_eq in H1, H2. exists g. split; [exact Hin|]. unfold gden. destruct (is_const_sound E _ _ Ec) as [He _].
  destruct (is_const_sound E _ _ Ez) as [Hz _]. rewrite He, Hz, H1, H2. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma is_mark_base : forall E g, is_mark g = true -> lden E (fst (fst g)) = Z_to_bv 64 MARKB.
Proof.
  intros E g H. unfold is_mark in H. destruct (is_const (fst (fst g))) as [c|] eqn:Ec; [|discriminate].
  destruct (Z.eqb c MARKB) eqn:Hc; [|discriminate]. apply Z.eqb_eq in Hc. subst c. exact (proj1 (is_const_sound E _ _ Ec)).
Qed.
Lemma has_const_grant_In' : forall E gs b k, has_const_grant gs b k = true -> 0 <= b < two64 -> b <> MARKB ->
  exists g, In g gs /\ gden E g = (Z_to_bv 64 b, Z_to_bv 64 k) /\ is_mark g = false.
Proof.
  intros E gs b k H Hb Hne. destruct (has_const_grant_In E gs b k H) as (g & Hin & Hg). exists g. split; [exact Hin|]. split; [exact Hg|].
  destruct (is_mark g) eqn:Hm; [|reflexivity]. exfalso. pose proof (is_mark_base E g Hm) as Hbm. unfold gden in Hg.
  pose proof (f_equal (fun q => bv_unsigned (fst q)) Hg) as Hg1. cbn [fst] in Hg1.
  rewrite Hbm in Hg1. unfold MARKB in *. rewrite !fg_lit in Hg1 by (unfold two64 in *; lia). lia.
Qed.

Lemma iv_overlap_false : forall (lo n b s : word), iv_overlap lo n b s = false ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo.
Proof. intros lo n b s H. unfold iv_overlap in H. apply andb_false_iff in H as [H|H]; apply Z.ltb_ge in H; lia. Qed.

Lemma region_free_avoid : forall l (lo n b s : word), region_free l lo n = true -> In (b, s) l ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo.
Proof. intros l lo n b s Hf Hin. exact (iv_overlap_false _ _ _ _ (region_free_In l lo n b s Hf Hin)). Qed.

Lemma region_free_pt : forall l (lo n : word) x, region_free l lo n = true ->
  bv_unsigned lo <= x < bv_unsigned lo + bv_unsigned n -> covered l x = false.
Proof.
  intros l lo n x Hf Hx. unfold covered. apply not_true_iff_false. intros He. apply existsb_exists in He as ([b s] & Hin & Hi).
  destruct (region_free_avoid l lo n b s Hf Hin) as [H|H]; unfold in_iv, in_rng, B, S in Hi; cbn [fst snd] in Hi;
    apply andb_prop in Hi as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; lia.
Qed.

Lemma covered_In : forall l p x, In p l -> in_iv p x = true -> covered l x = true.
Proof. intros l p x Hin Hx. unfold covered. apply existsb_exists. exists p. auto. Qed.

Lemma covered_app_l : forall l1 l2 x, covered l1 x = true -> covered (l1 ++ l2) x = true.
Proof. intros l1 l2 x H. rewrite covered_app, H. reflexivity. Qed.
Lemma covered_app_r : forall l1 l2 x, covered l2 x = true -> covered (l1 ++ l2) x = true.
Proof. intros l1 l2 x H. rewrite covered_app, H, orb_true_r. reflexivity. Qed.

(* [comment removed for export] *)
Record place_facts (a : word) (nZ : Z) : Prop := mkPF {
  pf_al   : bv_unsigned a mod 4096 = 0;
  pf_lo   : 4096 <= bv_unsigned a;
  pf_hi   : bv_unsigned a + nZ <= TOPW;
  pf_sh   : bv_unsigned a + nZ <= SH_LO \/ SH_HI <= bv_unsigned a
}.

Lemma place_facts_of : forall E M model BL nZ a,
  vm_maps (m_vmmaps model) = lden_maps E BL (sm_maps M) -> shadow_ok M = true ->
  bv_unsigned (vm_init_sp (m_vmmaps model)) <= sp_window_hi -> 0 < nZ ->
  place_ok model nZ a -> place_facts a nZ.
Proof.
  intros E M model BL nZ a Hm Hsh Hsp Hn (Hal & Hpos & Htop & Hfree). unfold page_size in Hal.
  assert (Hu : bv_unsigned (Z_to_bv 64 nZ) = nZ).
  { unfold alloc_top in Htop. pose proof (u_lt a). pose proof (u_lt (vm_init_sp (m_vmmaps model))). apply fg_lit. unfold stack_max_size in Htop.
    unfold two64 in *. change (2 ^ 64) with 18446744073709551616. lia. }
  constructor; [exact Hal| |unfold TOPW, alloc_top, stack_max_size, sp_window_hi in *; lia|].
  - pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)). rewrite Hal in H. lia.
  - unfold shadow_ok in Hsh. apply andb_prop in Hsh as [Hsh Hh]. apply andb_prop in Hsh as [Hl Hg].
    destruct (has_const_grant_In' E _ _ _ Hl ltac:(unfold LS_B, two64; lia) ltac:(unfold LS_B, MARKB; lia)) as (g1 & Hg1 & Hd1 & Hm1).
    destruct (has_const_grant_In' E _ _ _ Hg ltac:(unfold GAP_B, two64; lia) ltac:(unfold GAP_B, MARKB; lia)) as (g2 & Hg2 & Hd2 & Hm2).
    destruct (has_const_grant_In' E _ _ _ Hh ltac:(unfold HS_B, two64; lia) ltac:(unfold HS_B, MARKB; lia)) as (g3 & Hg3 & Hd3 & Hm3).
    assert (HI : forall g b k, In g (sm_maps M) -> is_mark g = false -> gden E g = (Z_to_bv 64 b, Z_to_bv 64 k) -> 0 <= b < two64 -> 0 <= k < two64 ->
               bv_unsigned a + nZ <= b \/ b + k <= bv_unsigned a).
    { intros g b k Hin Hmk Hd Hb Hk. assert (Hin' : In (Z_to_bv 64 b, Z_to_bv 64 k) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))).
      { apply in_or_app. right. rewrite Hm. rewrite <- Hd. exact (lden_maps_in E BL _ g Hin Hmk). }
      destruct (region_free_avoid _ _ _ _ _ Hfree Hin') as [H|H]; rewrite ?Hu, !fg64 in H by lia; lia. }
    pose proof (HI _ _ _ Hg1 Hm1 Hd1 ltac:(unfold LS_B, two64; lia) ltac:(unfold LS_K, two64; lia)).
    pose proof (HI _ _ _ Hg2 Hm2 Hd2 ltac:(unfold GAP_B, two64; lia) ltac:(unfold GAP_K, two64; lia)).
    pose proof (HI _ _ _ Hg3 Hm3 Hd3 ltac:(unfold HS_B, two64; lia) ltac:(unfold HS_K, two64; lia)).
    unfold SH_LO, SH_HI, LS_B, LS_K, GAP_B, GAP_K, HS_B, HS_K in *. lia.
Qed.

(* [comment removed for export] *)
Lemma blob_sh_fresh : forall E M model BL (a n : word) y, vm_maps (m_vmmaps model) = lden_maps E BL (sm_maps M) -> blob_ok E M model BL ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a n = true ->
  bv_unsigned a / 8 + SH_OFF <= y < (bv_unsigned a + bv_unsigned n) / 8 + SH_OFF -> ~ blob_sh BL y.
Proof.
  intros E M model BL a n y Hm Hb Hfree Hy ([b k] & Hp & Hs). unfold SHz in Hs. cbn [fst snd] in Hs.
  assert (Hin : In (b, k) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))).
  { apply in_or_app. right. rewrite Hm. exact (blob_in_maps E M model BL _ Hb Hp). }
  destruct (region_free_avoid _ _ _ _ _ Hfree Hin) as [H|H].
  - assert ((bv_unsigned a + bv_unsigned n) / 8 <= bv_unsigned b / 8) by (apply Z.div_le_mono; lia). lia.
  - assert ((bv_unsigned b + bv_unsigned k) / 8 <= bv_unsigned a / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

(* [comment removed for export] *)
Definition zmax (nZ : Z) : Z := (TOPW - nZ) / 65536.
Definition NA (n : positive) : lin := ladd (lscale 65536 (lvar n)) (lscale 4096 (lvar (Pos.succ n))).
(* [comment removed for export] *)
Lemma is_const_NA : forall n, is_const (NA n) = None.
Proof.
  intros n. unfold is_const, NA, ladd, lscale, lvar. cbn [l_t l_c tscale].
  change (Z.eqb (w64 (65536 * 1)) 0) with false. change (Z.eqb (w64 (4096 * 1)) 0) with false. cbn [tscale tadd].
  assert (H : Pos.compare n (Pos.succ n) = Lt) by (apply Pos.compare_lt_iff; lia). rewrite H. reflexivity.
Qed.
Lemma is_mark_NA : forall n sz k, is_mark (NA n, sz, k) = false.
Proof. intros n sz k. unfold is_mark. cbn [fst snd]. rewrite is_const_NA. reflexivity. Qed.
Definition NP (n : positive) : lin := laddc (ladd (lscale 8192 (lvar n)) (lscale 512 (lvar (Pos.succ n)))) SH_OFF.
Definition null_facts (n : positive) (nZ : Z) : list fact :=
  [FRange (lvar n) 0 (zmax nZ); FRange (lvar (Pos.succ n)) 0 15; FRange (NA n) 4096 (TOPW - nZ);
   FRange (laddc (NA n) (- SH_HI)) 0 (two64 + SH_LO - nZ - SH_HI)].
Definition null_rgs (n : positive) (nZ : Z) (vis piece : bool) : list region :=
  (if vis then [RGz (NA n) nZ RZ TEmpty] else []) ++ (if piece then [RGz (NP n) (nZ / 8) RZ TEmpty] else []).
Definition null_post (L : sst) (nZ : Z) (vis piece : bool) : sst :=
  SST (s_pc L + 4) (rset (s_regs L) (rkey a0r) (NA (s_next L))) (null_rgs (s_next L) nZ vis piece ++ s_rgs L)
      (null_facts (s_next L) nZ ++ s_facts L) (Pos.succ (Pos.succ (s_next L))) (s_resv L).
Definition null_allow (n : positive) (nZ : Z) (k : gkind) (vis piece : bool) : list (lin * Z) :=
  (if (vis && gkind_eqb k GL)%bool then [(NA n, nZ)] else []) ++ (if piece then [(NP n, nZ / 8)] else []).
Definition null_M (M : smodel) (n : positive) (nZ : Z) (k : gkind) (vis piece : bool) : smodel :=
  SM ((NA n, lconst nZ, k) :: sm_maps M) (null_allow n nZ k vis piece ++ sm_allow M)
     (sm_zr M) (sm_tid M) (sm_brk M) (sm_sbrk M) (sm_sp M) (sm_frz M) (sm_own M).

Lemma lz_lvar : forall E x, lz E (lvar x) = vz E x.
Proof. intros E x. unfold lz, lvar. cbn [l_c l_t tsum]. lia. Qed.

Lemma NA_den : forall E n, lden E (NA n) = Z_to_bv 64 (65536 * vz E n + 4096 * vz E (Pos.succ n)).
Proof.
  intros E n. unfold lden. apply Z_to_bv_eqm. unfold NA. eapply eqm_trans; [apply lz_ladd|].
  apply eqm_add; (eapply eqm_trans; [apply lz_lscale|]); rewrite lz_lvar; apply eqm_refl.
Qed.

Lemma NP_den : forall E n, lden E (NP n) = Z_to_bv 64 (8192 * vz E n + 512 * vz E (Pos.succ n) + SH_OFF).
Proof.
  intros E n. unfold lden. apply Z_to_bv_eqm. unfold NP. eapply eqm_trans; [apply lz_laddc|]. apply eqm_add; [|apply eqm_refl].
  eapply eqm_trans; [apply lz_ladd|].
  apply eqm_add; (eapply eqm_trans; [apply lz_lscale|]); rewrite lz_lvar; apply eqm_refl.
Qed.

(* [comment removed for export] *)
Definition zval (a : word) : word := Z_to_bv 64 (bv_unsigned a / 65536).
Definition rval (a : word) : word := Z_to_bv 64 ((bv_unsigned a / 4096) mod 16).

Lemma vz_zval : forall a, bv_unsigned (zval a) = bv_unsigned a / 65536.
Proof. intros a. unfold zval. apply fg64. pose proof (u_lt a). split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ (bv_unsigned a)); [apply Z.div_le_upper_bound; lia | lia]. Qed.
Lemma vz_rval : forall a, bv_unsigned (rval a) = (bv_unsigned a / 4096) mod 16.
Proof. intros a. unfold rval. apply fg64. pose proof (Z.mod_pos_bound (bv_unsigned a / 4096) 16 ltac:(lia)). unfold two64. lia. Qed.

Lemma decomp_a : forall a : word, bv_unsigned a mod 4096 = 0 ->
  65536 * (bv_unsigned a / 65536) + 4096 * ((bv_unsigned a / 4096) mod 16) = bv_unsigned a.
Proof.
  intros a Hal. set (u := bv_unsigned a).
  assert (H1 : u = 4096 * (u / 4096)) by (pose proof (Z.div_mod u 4096 ltac:(lia)); lia).
  assert (H2 : u / 65536 = (u / 4096) / 16) by (rewrite Z.div_div by lia; reflexivity).
  pose proof (Z.div_mod (u / 4096) 16 ltac:(lia)). rewrite H2. lia.
Qed.

Lemma decomp_p : forall a : word, bv_unsigned a mod 4096 = 0 ->
  8192 * (bv_unsigned a / 65536) + 512 * ((bv_unsigned a / 4096) mod 16) = bv_unsigned a / 8.
Proof.
  intros a Hal. pose proof (decomp_a a Hal) as H. set (u := bv_unsigned a) in *.
  apply Z.div_unique_exact; lia.
Qed.

Section NullVal.
Variable E : valu.
Variable n : positive.
Variable a : word.
Variable E2 : valu.
Hypothesis Hz : E2 n = zval a.
Hypothesis Hr : E2 (Pos.succ n) = rval a.
Hypothesis Hal : bv_unsigned a mod 4096 = 0.

#[using="Hz Hr Hal"] Lemma NA_val : lden E2 (NA n) = a.
Proof. LiaFast.lf_pins (fun (Hz Hr Hal : LiaFast.U) => LiaFast.u0).
  rewrite NA_den. unfold vz. rewrite Hz, Hr, vz_zval, vz_rval, (decomp_a a Hal). apply bv_eq. rewrite fg64 by exact (u_lt a). reflexivity.
Qed.

#[using="Hz Hr Hal"] Lemma NP_val : uE E2 (NP n) = bv_unsigned a / 8 + SH_OFF.
Proof. LiaFast.lf_pins (fun (Hz Hr Hal : LiaFast.U) => LiaFast.u0).
  unfold uE. rewrite NP_den. unfold vz. rewrite Hz, Hr, vz_zval, vz_rval, (decomp_p a Hal). apply fg64.
  pose proof (u_lt a). split; [unfold SH_OFF; pose proof (Z.div_pos (bv_unsigned a) 8 ltac:(lia) ltac:(lia)); lia|].
  assert (bv_unsigned a / 8 < 2305843009213693952) by (apply Z.div_lt_upper_bound; unfold two64 in *; lia).
  unfold SH_OFF, two64. lia.
Qed.
End NullVal.

(* [comment removed for export] *)
Definition fresh_next (na : bool) (flags a n : word) (m : Model) : Model :=
  if na then fresh_na_next flags a n m else fresh_rw_next flags a n m.

Lemma fn_vmmaps : forall na flags a n m, m_vmmaps (fresh_next na flags a n m) =
  mkVmMapsFull (vm_reserved (m_vmmaps m)) ((a, n) :: vm_maps (m_vmmaps m))
    (if na then (a, n) :: vm_noaccess (m_vmmaps m) else vm_noaccess (m_vmmaps m))
    (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).
Proof.
  intros na flags a n m. unfold fresh_next, fresh_na_next, fresh_rw_next, with_mmap_backing, vm_add_lazy.
  destruct na, (mmap_noreserve_b flags); destruct m; reflexivity.
Qed.
Lemma fn_lazy : forall na flags a n m, m_vm_lazy (fresh_next na flags a n m) =
  (if mmap_noreserve_b flags then lazy_interior a n else []) ++ m_vm_lazy m.
Proof.
  intros na flags a n m. unfold fresh_next, fresh_na_next, fresh_rw_next, with_mmap_backing, vm_add_lazy.
  destruct na, (mmap_noreserve_b flags); destruct m; reflexivity.
Qed.
Lemma fn_mat : forall na flags a n m, m_vm_materialized (fresh_next na flags a n m) = m_vm_materialized m.
Proof.
  intros na flags a n m. unfold fresh_next, fresh_na_next, fresh_rw_next, with_mmap_backing, vm_add_lazy.
  destruct na, (mmap_noreserve_b flags); destruct m; reflexivity.
Qed.
Lemma fn_other : forall na flags a n m, let m' := fresh_next na flags a n m in
  m_proc m' = m_proc m /\ m_fd m' = m_fd m /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_lim m' = m_lim m /\ m_time m' = m_time m.
Proof.
  intros na flags a n m. unfold fresh_next, fresh_na_next, fresh_rw_next, with_mmap_backing, vm_add_lazy.
  destruct na, (mmap_noreserve_b flags); destruct m; cbn; repeat split; reflexivity.
Qed.
Lemma fn_halted : forall na flags a n m, m_halted (fresh_next na flags a n m) = m_halted m.
Proof. intros. unfold m_halted. rewrite (proj1 (fn_other na flags a n m)). reflexivity. Qed.
Lemma fn_tid : forall na flags a n m, m_tid (fresh_next na flags a n m) = m_tid m.
Proof. intros. unfold m_tid. rewrite (proj1 (fn_other na flags a n m)). reflexivity. Qed.

Definition fresh_eff (na : bool) (a n : word) : SyscallEffect :=
  if na then mkEffectU a [] [] [(a, n)] [] [] else mkEffect a [] [(a, n)].
Definition fresh_mem (na : bool) (mem : word -> option byte) (a n : word) : word -> option byte :=
  if na then apply_unmaps mem [(a, n)] else apply_zeros mem [(a, n)].

Lemma fresh_restrict : forall H ms na a n pcz, ms_pc_val ms = Z_to_bv 64 pcz ->
  restrict H (advance_past_svc (apply_effect (svc_set ms) (fresh_eff na a n))) =
  mks (ms_fregs ms) (ms_fcsr ms) (rupd (ms_regs ms) a0r a) (Z_to_bv 64 (pcz + 4)) (ms_resv ms)
      (mrestrict H (fresh_mem na (ms_mem ms) a n)) (ms_rom ms).
Proof.
  intros H ms na a n pcz Hpc. unfold fresh_eff, fresh_mem. destruct na.
  - rewrite (restrict_adv_eff H ms a [] [(a, n)] [] pcz Hpc). reflexivity.
  - rewrite (restrict_adv_eff H ms a [(a, n)] [] [] pcz Hpc). reflexivity.
Qed.
Lemma fresh_full_mem : forall ms na a n,
  ms_mem (advance_past_svc (apply_effect (svc_set ms) (fresh_eff na a n))) = fresh_mem na (ms_mem ms) a n.
Proof.
  intros ms na a n. unfold fresh_eff, fresh_mem. destruct na.
  - rewrite (adv_eff_mem ms a [] [(a, n)] []). reflexivity.
  - rewrite (adv_eff_mem ms a [(a, n)] [] []). reflexivity.
Qed.

Lemma fresh_mem_out : forall na mem (a n w : word), ~ (bv_unsigned a <= bv_unsigned w < bv_unsigned a + bv_unsigned n) ->
  fresh_mem na mem a n w = mem w.
Proof.
  intros na mem a n w Hw. assert (Hc : zeros_cover [(a, n)] w = false).
  { rewrite zeros_cover_one. apply not_true_iff_false. intros Hb. apply andb_prop in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. }
  unfold fresh_mem. destruct na; [apply apply_unmaps_out | apply apply_zeros_out]; exact Hc.
Qed.
Lemma fresh_mem_in : forall mem (a n w : word), bv_unsigned a <= bv_unsigned w < bv_unsigned a + bv_unsigned n ->
  fresh_mem false mem a n w = Some (Z_to_bv 8 0).
Proof.
  intros mem a n w Hw. unfold fresh_mem. apply apply_zeros_in. rewrite zeros_cover_one.
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma rgs_disj_app : forall E new old, rgs_disj E new -> rgs_disj E old ->
  (forall R1 R2, In R1 new -> In R2 old -> rg_disj E R1 R2) -> rgs_disj E (new ++ old).
Proof.
  intros E new. induction new as [|R rs IH]; intros old Hn Ho Hx; cbn [app rgs_disj] in *; [exact Ho|].
  destruct Hn as [Hn1 Hn2]. split.
  - apply Forall_app. split; [exact Hn1|]. apply Forall_forall. intros R2 HR2. apply Hx; [left; reflexivity | exact HR2].
  - apply IH; [exact Hn2 | exact Ho |]. intros R1 R2 H1 H2. apply Hx; [right; exact H1 | exact H2].
Qed.

Lemma upd_other : forall E x y v, y <> x -> upd E x v y = E y.
Proof. intros E x y v H. unfold upd. rewrite (proj2 (Pos.eqb_neq y x) H). reflexivity. Qed.
Lemma upd_same : forall E x v, upd E x v x = v.
Proof. intros E x v. unfold upd. rewrite Pos.eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)
Lemma agree2 : forall n E z r E'', agree (Pos.succ (Pos.succ n)) (upd (upd E n z) (Pos.succ n) r) E'' ->
  agree n E E'' /\ E'' n = z /\ E'' (Pos.succ n) = r.
Proof.
  intros n E z r E'' Ha. split; [|split].
  - intros x Hx. rewrite <- (Ha x ltac:(lia)). rewrite !upd_other by lia. reflexivity.
  - rewrite <- (Ha n ltac:(lia)). rewrite upd_other by lia. apply upd_same.
  - rewrite <- (Ha (Pos.succ n) ltac:(lia)). apply upd_same.
Qed.

(* [comment removed for export] *)
Lemma zr_has_in : forall zr lo hi w, zr_has zr lo hi = true -> lo <= w < hi -> in_zr zr w = true.
Proof.
  intros zr lo hi w H Hw. unfold zr_has in H. apply existsb_exists in H as (p & Hin & Hp). apply andb_prop in Hp as [H1 H2].
  apply Z.leb_le in H1, H2. unfold in_zr. apply existsb_exists. exists p. split; [exact Hin|].
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma const_grant_covered : forall E BL gs b k w, has_const_grant gs b k = true -> 0 <= b < two64 -> 0 <= k < two64 -> b <> MARKB ->
  b <= w < b + k -> covered (lden_maps E BL gs) w = true.
Proof.
  intros E BL gs b k w H Hb Hk Hne Hw. destruct (has_const_grant_In' E gs b k H Hb Hne) as (g & Hin & Hg & Hmk).
  apply (covered_In _ (gden E g)); [exact (lden_maps_in E BL gs g Hin Hmk)|]. rewrite Hg, in_iv_word, !fg64 by assumption.
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma piece_pts : forall E BL M (a : word) nZ w, shadow_ok M = true -> place_facts a nZ -> 0 < nZ -> nZ mod 4096 = 0 ->
  bv_unsigned a / 8 + SH_OFF <= w < (bv_unsigned a + nZ) / 8 + SH_OFF ->
  in_shadow w = true /\ (zr_ok M = true -> in_zr (sm_zr M) w = true) /\ covered (lden_maps E BL (sm_maps M)) w = true.
Proof.
  intros E BL M a nZ w Hsh [Hal Hlo Hhi Hshd] HnZ Hnal Hw. unfold shadow_ok in Hsh. apply andb_prop in Hsh as [Hsh Hh].
  apply andb_prop in Hsh as [Hl _].
  assert (Hd1 : (bv_unsigned a + nZ) / 8 <= (bv_unsigned a + nZ)) by (apply Z.div_le_upper_bound; lia).
  assert (Hd0 : 0 <= bv_unsigned a / 8) by (apply Z.div_pos; lia).
  destruct Hshd as [Hlow|Hhigh].
  - assert (Hup : (bv_unsigned a + nZ) / 8 <= SH_LO / 8) by (apply Z.div_le_mono; lia).
    unfold SH_LO, SH_OFF in *. change (2147446784 / 8) with 268430848 in Hup.
    split; [unfold in_shadow, SH_LO, SH_HI; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia|].
    split; [intros Hz; unfold zr_ok in Hz; apply andb_prop in Hz as [Hz _]; apply (zr_has_in _ _ _ _ Hz); unfold LS_B, LS_K; lia|].
    apply (const_grant_covered E BL _ LS_B LS_K); [exact Hl | unfold LS_B, two64; lia | unfold LS_K, two64; lia | unfold LS_B, MARKB; lia | unfold LS_B, LS_K; lia].
  - assert (Hup : (bv_unsigned a + nZ) / 8 <= TOPW / 8) by (apply Z.div_le_mono; lia).
    assert (Hdn : SH_HI / 8 <= bv_unsigned a / 8) by (apply Z.div_le_mono; lia).
    unfold SH_HI, SH_OFF, TOPW in *. change (17594333528064 / 8) with 2199291691008 in Hdn.
    change (140737479966720 / 8) with 17592184995840 in Hup.
    split; [unfold in_shadow, SH_LO, SH_HI; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia|].
    split; [intros Hz; unfold zr_ok in Hz; apply andb_prop in Hz as [_ Hz]; apply (zr_has_in _ _ _ _ Hz); unfold HS_B, HS_K; lia|].
    apply (const_grant_covered E BL _ HS_B HS_K); [exact Hh | unfold HS_B, two64; lia | unfold HS_K, two64; lia | unfold HS_B, MARKB; lia | unfold HS_B, HS_K; lia].
Qed.

(* [comment removed for export] *)
Lemma old_pts : forall E model (a : word) nZ R w,
  place_facts a nZ -> 0 < nZ -> nZ mod 4096 = 0 ->
  (forall x, bv_unsigned a <= x < bv_unsigned a + nZ -> covered (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) x = false) ->
  bv_unsigned a + nZ <= alloc_top (m_vmmaps model) ->
  rl_ok E model R -> uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R ->
  ~ (bv_unsigned a <= w < bv_unsigned a + nZ) /\
  ((forall y, bv_unsigned a / 8 + SH_OFF <= y < (bv_unsigned a + nZ) / 8 + SH_OFF -> in_shadow y = true) ->
   ~ (bv_unsigned a / 8 + SH_OFF <= w < (bv_unsigned a + nZ) / 8 + SH_OFF)).
Proof.
  intros E model a nZ R w [Hal Hlo Hhi Hshd] HnZ Hnal Hnc Htop0 [Hpos [Happ | (Hoff & HX & Hpc)]] Hw;
    pose proof (grant_le_atop_pg _ _ _ Hal Hnal Htop0) as Htop.
  - destruct (Happ w Hw) as (Hcv & Hns & _). split.
    + intros Hin. destruct Hcv as [Hc | Hc]; [rewrite (Hnc w Hin) in Hc; discriminate | lia].
    + intros Hps Hin. rewrite (Hps w Hin) in Hns. discriminate.
  - destruct (Hpc w Hw) as [_ Hcm]. split.
    + intros Hin. pose proof (Hnc w Hin) as Hf. rewrite covered_app, Hcm, orb_true_r in Hf. discriminate.
    + intros _ Hin. set (x := 8 * (w - SH_OFF)).
      assert (Hx : 8 * (uE E (rg_base R) - SH_OFF) <= x < 8 * (uE E (rg_base R) - SH_OFF + rsz E R)) by (unfold x; lia).
      destruct (HX x Hx) as (Hcv & _ & _).
      assert (Hxa : bv_unsigned a <= x < bv_unsigned a + nZ).
      { unfold x. pose proof (Z.div_mod (bv_unsigned a) 8 ltac:(lia)). pose proof (Z.div_mod (bv_unsigned a + nZ) 8 ltac:(lia)).
        pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)). pose proof (Z.div_mod nZ 4096 ltac:(lia)).
        assert (bv_unsigned a mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (bv_unsigned a / 4096 * 512); lia).
        assert ((bv_unsigned a + nZ) mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists ((bv_unsigned a / 4096 + nZ / 4096) * 512); lia).
        lia. }
      destruct Hcv as [Hc | Hc]; [rewrite (Hnc x Hxa) in Hc; discriminate | lia].
Qed.

Section NullPost.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.

#[using="Hsegb"] Theorem null_den : forall E L M ms model (nZ : Z) (k : gkind) (vis piece : bool) (flags : word) (na : bool) (a : word),
  DEN segs LIMIT model0 mem0 E L M ms model ->
  place_ok model nZ a -> shadow_ok M = true -> (piece = true -> zr_ok M = true) ->
  0 < nZ -> nZ mod 4096 = 0 ->
  k = (if na then GN else if mmap_noreserve_b flags then GL else GE) ->
  (vis = true -> na = false) ->
  eager_sum (s_facts L) ((NA (s_next L), lconst nZ, k) :: sm_maps M) + allow_bound (null_allow (s_next L) nZ k vis piece ++ sm_allow M) <= LIMIT ->
  own_avoid E M (bv_unsigned a) (bv_unsigned a + nZ) ->
  (piece = true -> own_avoid E M (bv_unsigned a / 8 + SH_OFF) ((bv_unsigned a + nZ) / 8 + SH_OFF)) ->
  DEN segs LIMIT model0 mem0 (upd (upd E (s_next L) (zval a)) (Pos.succ (s_next L)) (rval a))
      (null_post L nZ vis piece) (null_M M (s_next L) nZ k vis piece)
      (advance_past_svc (apply_effect (svc_set ms) (fresh_eff na a (Z_to_bv 64 nZ)))) (fresh_next na flags a (Z_to_bv 64 nZ) model).
Proof. LiaFast.lf_pins (fun (Hsegb : LiaFast.U) => LiaFast.u0).
  intros E L M ms model nZ k vis piece flags na a Hd Hplace Hsh Hzrok HnZ Hnal Hk Hvis Hbud Hav Havp.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  pose proof (place_facts_of E M model _ nZ a Hmaps Hsh (proj2 Hspok) HnZ Hplace) as PF.
  pose proof PF as PF0. destruct PF0 as [Hal Hlo Hhi Hshd].
  destruct Hplace as (_ & _ & Htop & Hfree).
  assert (HnZw : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply fg64; unfold TOPW, two64 in *; pose proof (u_lt a); lia).
  assert (Hnc : forall x, bv_unsigned a <= x < bv_unsigned a + nZ ->
                  covered (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) x = false).
  { intros x Hx. apply (region_free_pt _ a (Z_to_bv 64 nZ)); [exact Hfree | rewrite HnZw; exact Hx]. }
  set (E' := upd (upd E (s_next L) (zval a)) (Pos.succ (s_next L)) (rval a)).
  assert (Ha : agree (s_next L) E E') by (exact (proj1 (agree2 (s_next L) E (zval a) (rval a) E' (agree_refl _ _)))).
  set (model' := fresh_next na flags a (Z_to_bv 64 nZ) model).
  set (M' := null_M M (s_next L) nZ k vis piece).
  set (H := Hof E M model) in *.
  set (H' := Hof E' M' model').
  destruct (sm_wf_parts _ M Hwf) as (Hwg & Hwa & Hwt & Hwb & Hwsb & Hwsp).
  (* [comment removed for export] *)
  assert (HA' : allowA E' M' = List.map (allow1 E') (null_allow (s_next L) nZ k vis piece) ++ allowA E M).
  { unfold allowA, M', null_M. cbn [sm_allow]. rewrite map_app. f_equal. exact (allowA_agree _ E E' M Hwf Ha). }
  assert (Hlz' : m_vm_lazy model' = (if mmap_noreserve_b flags then lazy_interior a (Z_to_bv 64 nZ) else []) ++ m_vm_lazy model)
    by exact (fn_lazy na flags a (Z_to_bv 64 nZ) model).
  assert (Hli : lazy_interior a (Z_to_bv 64 nZ) = [(a, Z_to_bv 64 nZ)]).
  { apply lazy_interior_aligned; rewrite ?HnZw; unfold page_size; try lia. unfold TOPW in Hhi. lia. }
  (* [comment removed for export] *)
  assert (HNA : forall E'', agree (Pos.succ (Pos.succ (s_next L))) E' E'' -> lden E'' (NA (s_next L)) = a).
  { intros E'' Ha''. destruct (agree2 _ _ _ _ _ Ha'') as (_ & Hz & Hr). exact (NA_val (s_next L) a E'' Hz Hr Hal). }
  assert (HNP : forall E'', agree (Pos.succ (Pos.succ (s_next L))) E' E'' -> uE E'' (NP (s_next L)) = bv_unsigned a / 8 + SH_OFF).
  { intros E'' Ha''. destruct (agree2 _ _ _ _ _ Ha'') as (_ & Hz & Hr). exact (NP_val (s_next L) a E'' Hz Hr Hal). }
  assert (Hsd0 := sden_0 _ _ _ _ Hsd). destruct Hsd0 as (Hpc0 & Hsv0 & Hrv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  (* [comment removed for export] *)
  assert (Hpp : forall y, bv_unsigned a / 8 + SH_OFF <= y < (bv_unsigned a + nZ) / 8 + SH_OFF ->
                  in_shadow y = true /\ (zr_ok M = true -> in_zr (sm_zr M) y = true) /\ covered (lden_maps E (blob_of model0) (sm_maps M)) y = true)
    by (intros y Hy; exact (piece_pts E (blob_of model0) M a nZ y Hsh PF HnZ Hnal Hy)).
  (* [comment removed for export] *)
  assert (Hold : forall R, In R (s_rgs L) -> forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R ->
             ~ (bv_unsigned a <= w < bv_unsigned a + nZ) /\ ~ (bv_unsigned a / 8 + SH_OFF <= w < (bv_unsigned a + nZ) / 8 + SH_OFF)).
  { intros R HR w Hw. rewrite Forall_forall in Hrl.
    destruct (old_pts E model a nZ R w PF HnZ Hnal Hnc Htop (Hrl R HR) Hw) as [H1 H2]. split; [exact H1|].
    apply H2. intros y Hy. exact (proj1 (Hpp y Hy)). }
  assert (Hrgw : forall R, In R (s_rgs L) -> uE E (rg_base R) + rsz E R <= two64 /\ 0 <= rsz E R).
  { intros R HR. rewrite Forall_forall in HG0. destruct (HG0 R HR) as (Hs & Hw & _). unfold uE. lia. }
  assert (Hua : 0 <= bv_unsigned a < two64) by exact (u_lt a).
  (* [comment removed for export] *)
  assert (Hvold : forall R, In R (s_rgs L) -> forall i, 0 <= i < rsz E R -> H' (Z_to_bv 64 (uE E (rg_base R) + i)) = false).
  { intros R HR i Hi. rewrite Forall_forall in HG0.
    pose proof (rg_ok_visible segs H (ms_mem ms) E R Hhoff (HG0 R HR) i Hi) as Hv.
    destruct (Hrgw R HR) as [Hw1 Hw2]. pose proof (u_lt (lden E (rg_base R))) as HuR. unfold uE in *.
    unfold H', Hof. rewrite Hlz', HA'. apply mkH_grow; [exact Hv|].
    intros Hp. destruct (mmap_noreserve_b flags); [|discriminate]. rewrite Hli in Hp. apply page_in_one in Hp.
    rewrite HnZw in Hp. rewrite fg64 in Hp by lia.
    apply (proj1 (Hold R HR (bv_unsigned (lden E (rg_base R)) + i) ltac:(unfold uE; lia))). exact Hp. }
  assert (Hvapp : vis = true -> forall i, 0 <= i < nZ -> H' (Z_to_bv 64 (bv_unsigned a + i)) = false).
  { intros Hv i Hi. pose proof (Hvis Hv) as Hna. unfold H', Hof. rewrite Hlz', HA'.
    destruct (mmap_noreserve_b flags) eqn:Hnr.
    - apply mkH_allowed. apply page_allowedb_app_l. rewrite Hk, Hna; rewrite ?Hnr. unfold null_allow. rewrite Hv. cbn [andb gkind_eqb app List.map].
      change (allow1 E' (NA (s_next L), nZ) :: List.map (allow1 E') (if piece then [(NP (s_next L), nZ / 8)] else []))
        with ([allow1 E' (NA (s_next L), nZ)] ++ List.map (allow1 E') (if piece then [(NP (s_next L), nZ / 8)] else [])).
      apply page_allowedb_app_l. apply allow1_covers; [unfold TOPW, two64 in *; lia|]. cbn [fst snd].
      unfold uE. rewrite (HNA E' (agree_refl _ _)). lia.
    - apply mkH_notlazy. rewrite app_nil_l. apply not_true_iff_false. intros Hp.
      destruct (pb_bounds (Z_to_bv 64 (bv_unsigned a + i))) as [Hb _].
      pose proof (Hlzm _ (page_in_covered _ _ _ Hp Hb)) as Hc. rewrite fg64 in Hc by (unfold TOPW, two64 in *; lia).
      pose proof (Hnc (bv_unsigned a + i) ltac:(lia)) as Hf. rewrite covered_app, Hc, orb_true_r in Hf. discriminate. }
  assert (Hvpc : piece = true -> forall y, bv_unsigned a / 8 + SH_OFF <= y < (bv_unsigned a + nZ) / 8 + SH_OFF ->
                   H' (Z_to_bv 64 y) = false).
  { intros Hpc y Hy. unfold H', Hof. rewrite Hlz', HA'. apply mkH_allowed. apply page_allowedb_app_l.
    unfold null_allow. rewrite Hpc, map_app. apply page_allowedb_app_r. cbn [List.map].
    apply allow1_covers; [|cbn [fst snd]; rewrite (HNP E' (agree_refl _ _))].
    - assert ((bv_unsigned a + nZ) / 8 <= bv_unsigned a + nZ) by (apply Z.div_le_upper_bound; lia). unfold SH_OFF, TOPW, two64 in *. lia.
    - assert ((bv_unsigned a + nZ) / 8 = bv_unsigned a / 8 + nZ / 8).
      { pose proof (Z.div_mod nZ 4096 ltac:(lia)). rewrite Hnal in H0.
        replace (bv_unsigned a + nZ) with (bv_unsigned a + (nZ / 4096 * 512) * 8) by lia.
        rewrite Z.div_add by lia. f_equal. pose proof (Z.div_mod nZ 8 ltac:(lia)).
        assert (nZ mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (nZ / 4096 * 512); lia). lia. }
      lia. }
  (* [comment removed for export] *)
  set (mem' := fresh_mem na (ms_mem ms) a (Z_to_bv 64 nZ)).
  assert (Hmold : forall R, In R (s_rgs L) -> forall i, 0 <= i < rsz E R ->
                    mem' (Z_to_bv 64 (uE E (rg_base R) + i)) = ms_mem ms (Z_to_bv 64 (uE E (rg_base R) + i))).
  { intros R HR i Hi. destruct (Hrgw R HR) as [Hw1 Hw2]. pose proof (u_lt (lden E (rg_base R))) as HuR. unfold uE in *.
    apply fresh_mem_out. rewrite HnZw. rewrite fg64 by lia. exact (proj1 (Hold R HR (bv_unsigned (lden E (rg_base R)) + i) ltac:(unfold uE; lia))). }
  assert (Hmapp : vis = true -> forall i, 0 <= i < nZ -> mem' (Z_to_bv 64 (bv_unsigned a + i)) = Some (Z_to_bv 8 0)).
  { intros Hv i Hi. unfold mem'. rewrite (Hvis Hv). apply fresh_mem_in. rewrite HnZw, fg64 by (unfold TOPW, two64 in *; lia). lia. }
  assert (Hnotpl : forall y, in_shadow y = true -> ~ (bv_unsigned a <= y < bv_unsigned a + nZ)).
  { intros y Hy Hin. unfold in_shadow in Hy. apply andb_prop in Hy as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. }
  assert (Hmpc : piece = true -> forall y, bv_unsigned a / 8 + SH_OFF <= y < (bv_unsigned a + nZ) / 8 + SH_OFF ->
                   mem' (Z_to_bv 64 y) = Some (Z_to_bv 8 0)).
  { intros Hpc y Hy. destruct (Hpp y Hy) as (Hys & Hyz & _).
    assert (Hy64 : 0 <= y < two64) by (assert ((bv_unsigned a + nZ) / 8 <= bv_unsigned a + nZ) by (apply Z.div_le_upper_bound; lia);
                                        unfold SH_OFF, TOPW, two64 in *; lia).
    unfold mem'. rewrite fresh_mem_out by (rewrite HnZw, fg64 by exact Hy64; exact (Hnotpl y Hys)).
    apply Hzr; [exact (Hyz (Hzrok Hpc))| |exact (own_avoid_pt E M _ _ y (Havp Hpc) Hy64 Hy)
                | apply (blob_sh_fresh E M model _ a (Z_to_bv 64 nZ) y Hmaps Hblob Hfree); rewrite HnZw; exact Hy].
    unfold outside. apply Forall_forall. intros R HR. rewrite fg64 by exact Hy64.
    destruct (Hrgw R HR) as [Hw1 Hw2].
    destruct (Z_lt_le_dec y (bv_unsigned (lden E (rg_base R)))) as [Hlt|Hge]; [left; exact Hlt|].
    destruct (Z_lt_le_dec y (bv_unsigned (lden E (rg_base R)) + rsz E R)) as [Hlt2|Hge2]; [|right; exact Hge2].
    exfalso. apply (proj2 (Hold R HR y ltac:(unfold uE; lia))). exact Hy. }
  (* [comment removed for export] *)
  assert (Hpw : (bv_unsigned a + nZ) / 8 + SH_OFF <= two64).
  { assert ((bv_unsigned a + nZ) / 8 <= bv_unsigned a + nZ) by (apply Z.div_le_upper_bound; lia). unfold SH_OFF, TOPW, two64 in *. lia. }
  assert (Hn8 : (bv_unsigned a + nZ) / 8 = bv_unsigned a / 8 + nZ / 8).
  { pose proof (Z.div_mod nZ 4096 ltac:(lia)). rewrite Hnal in H0.
    replace (bv_unsigned a + nZ) with (bv_unsigned a + (nZ / 4096 * 512) * 8) by lia.
    rewrite Z.div_add by lia. f_equal. pose proof (Z.div_mod nZ 8 ltac:(lia)).
    assert (nZ mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (nZ / 4096 * 512); lia). lia. }
  (* [comment removed for export] *)
  assert (Hsden : sden segs E' (null_post L nZ vis piece)
                    (restrict H' (advance_past_svc (apply_effect (svc_set ms) (fresh_eff na a (Z_to_bv 64 nZ)))))).
  { rewrite (fresh_restrict H' ms na a (Z_to_bv 64 nZ) (s_pc L) Hpc0).
    intros E'' Ha''. destruct (agree2 _ _ _ _ _ Ha'') as (Ha0 & Hz & Hr).
    destruct (Hsd E'' Ha0) as (_ & _ & Hrv & HR & HG & HD & HF & Hfrm).
    assert (HbE : forall R, In R (s_rgs L) -> uE E'' (rg_base R) = uE E (rg_base R) /\ rsz E'' R = rsz E R).
    { intros R HR'. unfold uE, rsz. unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R HR')) as [Hb1 Hb2].
      rewrite (lden_agree_wf _ E E'' _ Hb1 Ha0), (lden_agree_wf _ E E'' _ Hb2 Ha0). split; reflexivity. }
    unfold sden0, null_post. cbn [s_pc s_regs s_rgs s_facts s_resv mks ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrv|].
    split; [apply regs_ok_upd; [exact HR | exact (HNA E'' Ha'')]|].
    split; [|split; [|split; [|exact Hfrm]]].
    - (* [comment removed for export] *)
      apply Forall_app. split.
      + unfold null_rgs. apply Forall_app. split.
        * destruct vis eqn:Hv; [|constructor]. constructor; [|constructor].
          apply rg_ok_fresh_rz; [unfold TOPW, two64 in *; lia | unfold uE; rewrite (HNA E'' Ha''); unfold TOPW, two64 in *; lia|].
          intros i Hi. unfold uE. rewrite (HNA E'' Ha''). unfold mrestrict. rewrite (Hvapp eq_refl i Hi). exact (Hmapp eq_refl i Hi).
        * destruct piece eqn:Hpc; [|constructor]. constructor; [|constructor].
          apply rg_ok_fresh_rz; [split; [apply Z.div_pos; lia | assert (nZ / 8 <= nZ) by (apply Z.div_le_upper_bound; lia); unfold TOPW, two64 in *; lia] | rewrite (HNP E'' Ha''); lia|].
          intros i Hi. rewrite (HNP E'' Ha''). unfold mrestrict.
          rewrite (Hvpc eq_refl) by lia. exact (Hmpc eq_refl (bv_unsigned a / 8 + SH_OFF + i) ltac:(lia)).
      + apply Forall_forall. intros R HR'. rewrite Forall_forall in HG. apply (rg_ok_mem_eq segs E'' (ms_mem (restrict H ms))); [exact (HG R HR')|].
        intros i Hi. rewrite (proj2 (HbE R HR')) in Hi. rewrite (proj1 (HbE R HR')). cbn [ms_mem restrict]. unfold mrestrict.
        rewrite (Hvold R HR' i Hi). rewrite Forall_forall in HG0.
        rewrite (rg_ok_visible segs H (ms_mem ms) E R Hhoff (HG0 R HR') i Hi). exact (Hmold R HR' i Hi).
    - (* [comment removed for export] *)
      apply rgs_disj_app; [| exact HD |].
      + unfold null_rgs. destruct vis, piece; cbn [app rgs_disj];
          try (split; [apply Forall_nil | exact I]); try exact I.
        split; [apply Forall_cons; [|apply Forall_nil] | split; [apply Forall_nil | exact I]].
        assert (Hn64 : 0 <= nZ < two64) by (unfold TOPW, two64 in *; lia).
        assert (Hn864 : 0 <= nZ / 8 < two64) by (split; [apply Z.div_pos; lia | assert (nZ / 8 <= nZ) by (apply Z.div_le_upper_bound; lia); lia]).
        unfold rg_disj. cbv zeta. rewrite (rsz_RGz E'' _ _ _ _ Hn64), (rsz_RGz E'' _ _ _ _ Hn864). unfold RGz. cbn [rg_base].
        change (bv_unsigned (lden E'' (NP (s_next L)))) with (uE E'' (NP (s_next L))). rewrite (HNA E'' Ha''), (HNP E'' Ha'').
        apply iv_pts_disj; [lia | apply Z.div_str_pos; lia|]. intros w Hw1 Hw2. apply (Hnotpl w); [|lia].
        exact (proj1 (Hpp w ltac:(lia))).
      + intros R1 R2 H1 H2. unfold rg_disj. cbv zeta.
        assert (Hn64 : 0 <= nZ < two64) by (unfold TOPW, two64 in *; lia).
        assert (Hn864 : 0 <= nZ / 8 < two64) by (split; [apply Z.div_pos; lia | assert (nZ / 8 <= nZ) by (apply Z.div_le_upper_bound; lia); lia]).
        change (bv_unsigned (lden E'' (rg_base R2))) with (uE E'' (rg_base R2)). rewrite (proj1 (HbE R2 H2)), (proj2 (HbE R2 H2)).
        pose proof Hrl as Hrl2. rewrite Forall_forall in Hrl2. destruct (Hrl2 R2 H2) as [Hpos2 _].
        unfold null_rgs in H1. apply in_app_iff in H1 as [H1|H1].
        * destruct vis; [|destruct H1]. destruct H1 as [<-|[]]. rewrite (rsz_RGz E'' _ _ _ _ Hn64). unfold RGz. cbn [rg_base].
          rewrite (HNA E'' Ha'').
          apply iv_pts_disj; [lia | lia|]. intros w Hw1 Hw2. exact (proj1 (Hold R2 H2 w Hw2) Hw1).
        * destruct piece; [|destruct H1]. destruct H1 as [<-|[]]. rewrite (rsz_RGz E'' _ _ _ _ Hn864). unfold RGz. cbn [rg_base].
          change (bv_unsigned (lden E'' (NP (s_next L)))) with (uE E'' (NP (s_next L))). rewrite (HNP E'' Ha'').
          apply iv_pts_disj; [apply Z.div_str_pos; lia | lia|]. intros w Hw1 Hw2.
          exact (proj2 (Hold R2 H2 w Hw2) ltac:(lia)).
    - (* [comment removed for export] *)
      apply Forall_app. split; [|exact HF]. unfold null_facts. cbn [fact_ok].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]; cbn [fact_ok].
      + rewrite lden_lvar, Hz, vz_zval. split; [apply Z.div_pos; lia|]. unfold zmax. apply Z.div_le_mono; lia.
      + rewrite lden_lvar, Hr, vz_rval. pose proof (Z.mod_pos_bound (bv_unsigned a / 4096) 16 ltac:(lia)). lia.
      + rewrite (HNA E'' Ha''). lia.
      + rewrite lden_laddc, (HNA E'' Ha''), u_Z_to_bv. destruct Hshd as [Hlw|Hhg].
        * replace (bv_unsigned a + - SH_HI) with ((bv_unsigned a - SH_HI + two64) + (-1) * two64) by ring.
          rewrite Z_mod_plus_full. rewrite Z.mod_small by (unfold SH_HI, SH_LO, two64 in *; lia). unfold SH_HI, SH_LO, two64 in *. lia.
        * rewrite Z.mod_small by (unfold SH_HI, TOPW, two64 in *; lia). unfold SH_HI, SH_LO, TOPW, two64 in *. lia. }
  (* [comment removed for export] *)
  assert (Hvm' : m_vmmaps model' = mkVmMapsFull (vm_reserved (m_vmmaps model)) ((a, Z_to_bv 64 nZ) :: vm_maps (m_vmmaps model))
    (if na then (a, Z_to_bv 64 nZ) :: vm_noaccess (m_vmmaps model) else vm_noaccess (m_vmmaps model))
    (vm_start_brk (m_vmmaps model)) (vm_brk (m_vmmaps model)) (vm_limit (m_vmmaps model)) (vm_mmap_base (m_vmmaps model))
    (vm_init_sp (m_vmmaps model))) by exact (fn_vmmaps na flags a (Z_to_bv 64 nZ) model).
  assert (Hmat' : m_vm_materialized model' = m_vm_materialized model) by exact (fn_mat na flags a (Z_to_bv 64 nZ) model).
  assert (Hhl' : m_halted model' = m_halted model) by exact (fn_halted na flags a (Z_to_bv 64 nZ) model).
  assert (Htd' : m_tid model' = m_tid model) by exact (fn_tid na flags a (Z_to_bv 64 nZ) model).
  assert (Hoth' : m_proc model' = m_proc model /\ m_fd model' = m_fd model /\ m_io model' = m_io model /\ m_fsys model' = m_fsys model
                  /\ m_lim model' = m_lim model /\ m_time model' = m_time model) by exact (fn_other na flags a (Z_to_bv 64 nZ) model).
  assert (Hmaps' : vm_maps (m_vmmaps model') = lden_maps E' (blob_of model0) (sm_maps M')).
  { rewrite Hvm'. cbn [vm_maps sm_maps M' null_M lden_maps]. rewrite is_mark_NA. unfold gden at 1. cbn [fst snd]. rewrite (HNA E' (agree_refl _ _)), lden_lconst.
    f_equal. rewrite Hmaps. symmetry. exact (lden_maps_agree _ E E' _ M Hwf Ha). }
  assert (Hblob' : blob_ok E' M' model' (blob_of model0)).
  { pose proof (blob_ok_agree (s_next L) E E' M model model' _ Hwf Ha ltac:(rewrite Hvm'; reflexivity) Hblob) as (B1 & B2 & B3).
    split; [exact B1 | split].
    - cbn [sm_maps M' null_M nomark forallb]. rewrite is_mark_NA. cbn [negb andb]. exact B2.
    - intros g Hg Hmk. cbn [sm_maps M' null_M] in Hg. destruct Hg as [<-|Hg]; [rewrite is_mark_NA in Hmk; discriminate | exact (B3 g Hg Hmk)]. }
  assert (Hgsh' : Forall (gshape_ok E') (sm_maps M')).
  { cbn [sm_maps M' null_M]. constructor.
    - unfold gshape_ok, gsz, uE. cbn [fst snd]. rewrite (HNA E' (agree_refl _ _)), lden_lconst, fg64 by (unfold TOPW, two64 in *; pose proof (u_lt a); lia). unfold TOPW in Hhi. lia.
    - apply (Forall_agree_maps (s_next L) E E' M gshape_ok Hwf Ha); [|exact Hgsh].
      intros g Hg Hgs. unfold gshape_ok, gsz, uE. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto. }
  assert (Hcovm : forall x, covered (vm_maps (m_vmmaps model')) x = (in_iv (a, Z_to_bv 64 nZ) x || covered (vm_maps (m_vmmaps model)) x)%bool)
    by (intros x; rewrite Hvm'; reflexivity).
  assert (Hcovl : forall x, covered (m_vm_lazy model') x = true -> covered (m_vm_lazy model) x = true \/ in_iv (a, Z_to_bv 64 nZ) x = true).
  { intros x Hx. rewrite Hlz', covered_app in Hx. destruct (mmap_noreserve_b flags); [|left; exact Hx].
    rewrite Hli in Hx. cbn [covered existsb] in Hx. rewrite orb_false_r in Hx. apply orb_prop in Hx as [Hx|Hx]; [right|left]; exact Hx. }
  assert (Hinv : forall x, in_iv (a, Z_to_bv 64 nZ) x = true -> bv_unsigned a <= x < bv_unsigned a + nZ).
  { intros x Hx. rewrite in_iv_word, HnZw in Hx. apply andb_prop in Hx as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. }
  assert (Hinv' : forall x, bv_unsigned a <= x < bv_unsigned a + nZ -> in_iv (a, Z_to_bv 64 nZ) x = true).
  { intros x Hx. rewrite in_iv_word, HnZw. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (Hlzm' : forall x, covered (m_vm_lazy model') x = true -> covered (vm_maps (m_vmmaps model')) x = true).
  { intros x Hx. rewrite Hcovm. destruct (Hcovl x Hx) as [H1|H1]; [rewrite (Hlzm x H1), orb_true_r; reflexivity | rewrite H1; reflexivity]. }
  assert (Hmres' : forall x, covered (vm_maps (m_vmmaps model')) x = true -> covered (vm_reserved (m_vmmaps model')) x = false).
  { intros x Hx. rewrite Hvm'. cbn [vm_reserved]. rewrite Hcovm in Hx. apply orb_prop in Hx as [Hx|Hx]; [|exact (Hmres x Hx)].
    pose proof (Hnc x (Hinv x Hx)) as Hf. rewrite covered_app in Hf. apply orb_false_iff in Hf. exact (proj1 Hf). }
  assert (Hkind' : Forall (kind_ok E' model') (sm_maps M')).
  { cbn [sm_maps M' null_M]. constructor.
    - unfold kind_ok, gden. cbn [fst snd]. rewrite (HNA E' (agree_refl _ _)), lden_lconst. split.
      2:{ intros Hgn. rewrite Hvm'. cbn [vm_noaccess]. rewrite Hk in Hgn. destruct na; [left; reflexivity|].
          destruct (mmap_noreserve_b flags); discriminate. }
      intros Hne x Hx. rewrite Hvm'. cbn [vm_noaccess].
      rewrite covered_app. rewrite Hk in Hne. destruct na.
      + cbn [covered existsb]. rewrite Hx. reflexivity.
      + destruct (mmap_noreserve_b flags) eqn:Hnr; [|exfalso; exact (Hne eq_refl)].
        rewrite Hlz'; rewrite ?Hnr, ?Hli. cbn [covered existsb app]. rewrite Hx, orb_true_r. reflexivity.
    - apply (Forall_agree_maps (s_next L) E E' M (fun E g => kind_ok E model' g) Hwf Ha).
      + intros g Hg Hgs. unfold kind_ok, gden. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
      + rewrite Forall_forall in Hkind |- *. intros g Hg. split.
        2:{ intros Hgn. rewrite Hvm'. cbn [vm_noaccess]. pose proof (proj2 (Hkind g Hg) Hgn) as Hi0. destruct na; [right; exact Hi0 | exact Hi0]. }
        intros Hne x Hx. pose proof (proj1 (Hkind g Hg) Hne x Hx) as Hkx.
        rewrite Hvm'. cbn [vm_noaccess]. rewrite Hlz'. rewrite !covered_app in *. apply orb_prop in Hkx as [H1|H1].
        * destruct na; [rewrite covered_cons, H1, orb_true_r; reflexivity | rewrite H1; reflexivity].
        * rewrite H1, !orb_true_r. reflexivity. }
  assert (Hnan : Forall (fun p => 0 <= snd p) (null_allow (s_next L) nZ k vis piece)).
  { unfold null_allow. apply Forall_app. split.
    - destruct (vis && gkind_eqb k GL)%bool; [apply Forall_cons; [cbn; lia | apply Forall_nil] | apply Forall_nil].
    - destruct piece; [apply Forall_cons; [cbn [snd]; apply Z.div_pos; lia | apply Forall_nil] | apply Forall_nil]. }
  assert (Hanz' : Forall (fun p => 0 <= snd p) (sm_allow M')) by (cbn [sm_allow M' null_M]; apply Forall_app; split; assumption).
  assert (Hbud' : eager_used model' + A_bytes (AM model0 E' M') <= LIMIT).
  { assert (HFL' : Forall (fact_ok E') (s_facts L)) by (destruct (Hsd E' Ha) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
    pose proof (eager_le E' M' model' (s_facts L) _ HFL' Hmaps' Hgsh' Hkind' Hblob') as He.
    pose proof (A_bytes_allowA E' M' Hanz') as Hb. unfold AM. rewrite A_bytes_app. cbn [sm_maps sm_allow M' null_M] in He, Hb. lia. }
  assert (HNAw : lwf (Pos.succ (Pos.succ (s_next L))) (NA (s_next L)) = true)
    by (unfold NA; apply lwf_ladd; apply lwf_lscale; apply lwf_lvar; lia).
  assert (HNPw : lwf (Pos.succ (Pos.succ (s_next L))) (NP (s_next L)) = true)
    by (unfold NP; apply lwf_laddc, lwf_ladd; apply lwf_lscale; apply lwf_lvar; lia).
  assert (Hcovrm : forall x, covered (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) x = true ->
                     covered (vm_reserved (m_vmmaps model') ++ vm_maps (m_vmmaps model')) x = true).
  { intros x Hx. rewrite Hvm'. cbn [vm_reserved vm_maps]. rewrite covered_app in *. apply orb_prop in Hx as [Hx|Hx];
      [rewrite Hx; reflexivity | rewrite covered_cons, Hx, !orb_true_r; reflexivity]. }
  assert (Hcovm' : forall x, covered (vm_maps (m_vmmaps model)) x = true -> covered (vm_maps (m_vmmaps model')) x = true)
    by (intros x Hx; rewrite Hcovm, Hx, orb_true_r; reflexivity).
  assert (Htop' : alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model)) by (rewrite Hvm'; reflexivity).
  assert (Happ' : forall w, bv_unsigned a <= w < bv_unsigned a + nZ -> app_pt model' w).
  { intros w Hw. split; [left|split].
    - rewrite Hvm'. cbn [vm_reserved vm_maps]. rewrite covered_app, covered_cons, (Hinv' w Hw), orb_true_r. reflexivity.
    - apply not_true_iff_false. intros Hs. exact (Hnotpl w Hs Hw).
    - unfold TOPW in Hhi. lia. }
  constructor.
  - exact Hsden.
  - cbn [null_post s_next]. unfold M', null_M. apply sm_wf_cons_own; [exact (sm_wf_mono (s_next L) (Pos.succ (Pos.succ (s_next L))) M ltac:(lia) Hwf) | exact HNAw | apply lwf_lconst |].
    unfold null_allow. rewrite forallb_app. apply andb_true_intro. split.
    + destruct (vis && gkind_eqb k GL)%bool; cbn [forallb fst]; [rewrite HNAw; reflexivity | reflexivity].
    + destruct piece; cbn [forallb fst]; [rewrite HNPw; reflexivity | reflexivity].
  - cbn [null_post s_next s_rgs]. unfold bases_wf. rewrite forallb_app. apply andb_true_intro. split.
    + unfold null_rgs. rewrite forallb_app. apply andb_true_intro. split.
      * destruct vis; unfold RGz; cbn [forallb rg_base rg_size]; [rewrite HNAw, lwf_lconst; reflexivity | reflexivity].
      * destruct piece; unfold RGz; cbn [forallb rg_base rg_size]; [rewrite HNPw, lwf_lconst; reflexivity | reflexivity].
    + unfold bases_wf in Hbw. rewrite forallb_forall in *. intros R HR. destruct (andb_prop _ _ (Hbw R HR)) as [Hb1 Hb2].
      apply andb_true_intro. split; apply (lwf_mono (s_next L)); [lia | exact Hb1 | lia | exact Hb2].
  - rewrite Hhl'. exact Hh.
  - rewrite HA'. unfold A_wf. apply Forall_app. split; [exact (A_wf_map_allow1 E' _ Hnan) | exact Hawf].
  - exact Hanz'.
  - destruct Hminv as [N1 N2 N3 N4 N5]. constructor; rewrite ?Hmat'.
    + exact N1.
    + exact N2.
    + intros p Hp. unfold AM. rewrite HA', <- app_assoc. apply page_allowedb_app_r. exact (N3 p Hp).
    + intros p Hp. rewrite Hlz', page_in_ranges_app, (N4 p Hp), orb_true_r. reflexivity.
    + rewrite Hvm'. cbn [vm_limit]. rewrite Hlim. exact Hbud'.
  - unfold H', Hof. apply (hoff_of segs _ _ (vm_maps (m_vmmaps model')) (vm_reserved (m_vmmaps model')) Hsegb);
      [rewrite Hvm'; exact Hres | exact Hlzm' | exact Hmres'].
  - rewrite Hvm'. exact Hres.
  - rewrite Hvm'. exact Hlim.
  - rewrite Hvm'. cbn [vm_init_sp sm_sp M' null_M]. rewrite Hsp. symmetry. exact (lden_agree_wf _ E E' _ Hwsp Ha).
  - rewrite Hvm'. exact Hspok.
  - rewrite Hvm'. cbn [vm_brk sm_brk M' null_M]. rewrite Hbrk. symmetry. exact (lden_agree_wf _ E E' _ Hwb Ha).
  - rewrite Hvm'. cbn [vm_start_brk sm_sbrk M' null_M]. rewrite Hsbrk. symmetry. exact (lden_agree_wf _ E E' _ Hwsb Ha).
  - rewrite Htd', Htid. cbn [sm_tid M' null_M]. destruct (sm_tid M) as [l|]; [cbn; f_equal; symmetry; exact (lden_agree_wf _ E E' l Hwt Ha) | reflexivity].
  - exact Hmaps'.
  - exact Hgsh'.
  - cbn [sm_maps M' null_M]. constructor.
    + cbn [fst snd]. unfold gsz, uE. cbn [fst snd]. rewrite (HNA E' (agree_refl _ _)), Htop', lden_lconst, HnZw. exact Htop.
    + apply (Forall_agree_maps (s_next L) E E' M (fun E g => uE E (fst (fst g)) + gsz E g <= alloc_top (m_vmmaps model')) Hwf Ha).
      * intros g Hg Hgs. unfold gsz, uE. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
      * rewrite Htop'. exact Hgtop.
  - rewrite Hvm', Hlz'. cbn [vm_noaccess]. destruct Hivwf as [Hw1 Hw2]. split.
    + destruct na; [apply ivs_wf_cons; [unfold iv_wf, B, S; cbn [fst snd]; rewrite HnZw; unfold TOPW in Hhi; lia | exact Hw1] | exact Hw1].
    + apply ivs_wf_app; [|exact Hw2]. destruct (mmap_noreserve_b flags); [rewrite Hli; apply ivs_wf_cons; [|apply ivs_wf_nil] | apply ivs_wf_nil].
      unfold iv_wf, B, S; cbn [fst snd]; rewrite HnZw; unfold TOPW in Hhi; lia.
  - rewrite Hvm'. cbn [vm_maps pdisj]. split; [|exact Hpd]. apply Forall_forall. intros q Hq. destruct q as [b sz].
    assert (Hq' : In (b, sz) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) by (apply in_or_app; right; exact Hq).
    destruct (region_free_avoid _ _ _ _ _ Hfree Hq') as [H1|H1]; unfold iv_disj, B, S; cbn [fst snd]; lia.
  - exact Hmres'.
  - exact Hkind'.
  - exact Hlzm'.
  - cbn [sm_zr M' null_M]. exact Hzrsh.
  - cbn [sm_zr M' null_M]. intros w Hw. exact (Hcovm' w (Hzrm w Hw)).
  - intros w Hw Hout Hnow Hnb. cbn [sm_zr M' null_M] in Hw. rewrite fresh_full_mem. unfold outside in Hout. cbn [null_post s_rgs] in Hout.
    apply Forall_app in Hout as [_ Hout]. pose proof (Hzrsh w Hw) as Hws.
    assert (Hw64 : 0 <= w < two64) by (unfold in_shadow, SH_LO, SH_HI in Hws; apply andb_prop in Hws as [H1 H2];
                                        apply Z.leb_le in H1; apply Z.ltb_lt in H2; unfold two64; lia).
    rewrite fresh_mem_out by (rewrite HnZw, fg64 by exact Hw64; exact (Hnotpl w Hws)).
    apply (Hzr w Hw); [apply (outside_agree (s_next L) E E' (s_rgs L) _ Hbw Ha); exact Hout | | exact Hnb].
    exact (own_pt_keep _ E E' M M' w Hwf Ha eq_refl Hnow).
  - cbn [null_post s_rgs]. apply Forall_app. split.
    + assert (Hn64 : 0 <= nZ < two64) by (unfold TOPW, two64 in *; lia).
      assert (Hn864 : 0 <= nZ / 8 < two64) by (split; [apply Z.div_pos; lia | assert (nZ / 8 <= nZ) by (apply Z.div_le_upper_bound; lia); lia]).
      unfold null_rgs. apply Forall_app. split.
      * destruct vis; [|constructor]. constructor; [|constructor]. unfold rl_ok. rewrite (rsz_RGz E' _ _ _ _ Hn64).
        split; [exact HnZ|]. left. unfold RGz. cbn [rg_base]. unfold uE. rewrite (HNA E' (agree_refl _ _)). exact Happ'.
      * destruct piece; [|constructor]. constructor; [|constructor]. unfold rl_ok. rewrite (rsz_RGz E' _ _ _ _ Hn864).
        split; [apply Z.div_str_pos; lia|]. right. unfold RGz. cbn [rg_base]. rewrite (HNP E' (agree_refl _ _)). split; [pose proof (Z.div_pos (bv_unsigned a) 8 ltac:(lia) ltac:(lia)); lia|].
        split.
        -- intros x Hx. apply Happ'. pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)). pose proof (Z.div_mod nZ 4096 ltac:(lia)).
           assert (Ha8 : bv_unsigned a = 8 * (bv_unsigned a / 8)).
           { assert (bv_unsigned a mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (bv_unsigned a / 4096 * 512); lia).
             pose proof (Z.div_mod (bv_unsigned a) 8 ltac:(lia)). lia. }
           assert (Hn8' : nZ = 8 * (nZ / 8)).
           { assert (nZ mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (nZ / 4096 * 512); lia).
             pose proof (Z.div_mod nZ 8 ltac:(lia)). lia. }
           lia.
        -- intros w Hw. destruct (Hpp w ltac:(lia)) as (Hs & _ & Hc). split; [exact Hs|]. apply Hcovm'. rewrite Hmaps. exact Hc.
    + rewrite Forall_forall in Hrl |- *. intros R HR. apply (rl_ok_mono E' model model' R Hcovrm Hcovm' Htop').
      unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R HR)) as [Hb1 Hb2].
      exact (rl_ok_agree _ E E' model R Hb1 Hb2 Ha (Hrl R HR)).
  - destruct Hvmo as (H1 & H2 & H3 & H4 & H5). destruct Hoth' as (Hp & Hf & Hi & Hs & Hl & Ht).
    rewrite Hf, Hi, Hs, Hl, Ht. repeat split; assumption.
  - destruct Hoth' as (Hp & _). rewrite Hp, Htd'. exact Hproc.
  - pose proof (alloc_top_lo _ (proj1 Hspok)) as Hatl.
    apply (frz_keep mem0 E E' L (null_post L nZ vis piece) M M' ms _ model model' Hwf Ha eq_refl Htop'); [| | exact Hfrz].
    + intros w Hw Ho. unfold outside in *. cbn [null_post s_rgs]. apply Forall_app. split.
      * assert (Hw64 : bv_unsigned (Z_to_bv 64 w) = w) by (apply fg64; unfold two64; lia).
        assert (Hn64 : 0 <= nZ < two64) by (unfold TOPW, two64 in *; lia).
        assert (Hn864 : 0 <= nZ / 8 < two64) by (split; [apply Z.div_pos; lia | assert (nZ / 8 <= nZ) by (apply Z.div_le_upper_bound; lia); lia]).
        unfold null_rgs. apply Forall_app. split.
        -- destruct vis; [|constructor]. constructor; [|constructor]. right. rewrite (rsz_RGz E' _ _ _ _ Hn64). unfold RGz. cbn [rg_base].
           rewrite (HNA E' (agree_refl _ _)), Hw64. lia.
        -- destruct piece; [|constructor]. constructor; [|constructor]. right. rewrite (rsz_RGz E' _ _ _ _ Hn864). unfold RGz. cbn [rg_base].
           fold (uE E' (NP (s_next L))). rewrite (HNP E' (agree_refl _ _)), Hw64.
           assert (bv_unsigned a / 8 + nZ / 8 <= (bv_unsigned a + nZ) / 8).
           { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le (bv_unsigned a) 8 ltac:(lia)). pose proof (Z.mul_div_le nZ 8 ltac:(lia)). lia. }
           assert ((bv_unsigned a + nZ) / 8 <= TOPW / 8) by (apply Z.div_le_mono; [lia | exact Hhi]).
           unfold TOPW, SH_OFF in *. lia.
      * apply (proj1 (outside_agree (s_next L) E E' (s_rgs L) _ Hbw Ha)). exact Ho.
    + intros w Hw Ho. rewrite fresh_full_mem. rewrite fresh_mem_out; [reflexivity|].
      rewrite HnZw, fg64 by (unfold two64; lia). lia.
  - rom_tac.
  - apply (own_keep2 mem0 E E' L (null_post L nZ vis piece) M M' ms _ model model' Hwf Ha eq_refl); [| | exact Hown].
    + intros w Hop Ho. unfold outside in Ho. cbn [null_post s_rgs] in Ho. apply Forall_app in Ho as [_ Ho]. split.
      * apply (proj2 (outside_agree (s_next L) E E' (s_rgs L) _ Hbw Ha)). exact Ho.
      * rewrite fresh_full_mem. apply fresh_mem_out. rewrite HnZw. exact (Hav w Hop).
    + intros w Hop Hv. unfold H', Hof. rewrite Hlz', HA'. apply mkH_grow; [exact Hv|].
      intros Hp. destruct (mmap_noreserve_b flags); [|discriminate]. rewrite Hli in Hp. apply page_in_one in Hp.
      rewrite HnZw in Hp. exact (Hav w Hop Hp).
  - exact Hblob'.
Qed.
End NullPost.

(* [comment removed for export] *)
Definition arg (L : sst) (i : Z) : option Z := is_const (rget (s_regs L) (rkey (Z_to_bv 5 (10 + i)))).
Definition a7c (L : sst) : option Z := is_const (rget (s_regs L) (rkey (Z_to_bv 5 17))).

Lemma gpr_const : forall segs E L (msr ms : machine_state) (k : nat) c, sden segs E L msr -> ms_regs msr = ms_regs ms -> (k <= 5)%nat ->
  arg L (Z.of_nat k) = Some c -> ms_gpr (svc_set ms) k = Z_to_bv 64 c.
Proof.
  intros segs E L msr ms k c Hd Hr Hk Hc. destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & HR & _).
  specialize (HR (Z_to_bv 5 (10 + Z.of_nat k))). destruct (is_const_sound E _ c Hc) as [Hc' _]. rewrite Hc' in HR.
  unfold ms_gpr. cbn [svc_set ms_regs]. rewrite <- Hr. unfold getr in HR.
  assert (Hne : bv_eqb (Z_to_bv 5 (10 + Z.of_nat k)) 0 = false).
  { destruct k as [|[|[|[|[|[|k]]]]]]; try lia; reflexivity. }
  rewrite Hne in HR. exact HR.
Qed.

Lemma a7_const : forall segs E L (msr ms : machine_state) c, sden segs E L msr -> ms_regs msr = ms_regs ms ->
  a7c L = Some c -> ms_reg ms 17 = Z_to_bv 64 c.
Proof.
  intros segs E L msr ms c Hd Hr Hc. destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & HR & _).
  specialize (HR (Z_to_bv 5 17)). destruct (is_const_sound E _ c Hc) as [Hc' _]. rewrite Hc' in HR.
  unfold ms_reg. rewrite <- Hr. unfold getr in HR. exact HR.
Qed.


Definition gsize_sum (fs : list fact) (gs : list (lin * lin * gkind)) : Z := fold_right (fun g acc => gsz_hi fs g + acc) 0 gs.

Lemma ledger_size_gden : forall E fs gs, Forall (fact_ok E) fs -> Forall (gshape_ok E) gs -> ledger_size (List.map (gden E) gs) <= gsize_sum fs gs.
Proof.
  intros E fs gs HF H. induction H as [|g gs Hg Hgs IH]; [cbn; lia|]. cbn [List.map ledger_size gsize_sum fold_right].
  fold (gsize_sum fs gs). pose proof (gsz_bounds E fs g HF) as Hb. unfold gden at 1. cbn [snd]. unfold gsz, uE in Hb. lia.
Qed.

(* [comment removed for export] *)
Definition mark_len (fs : list fact) (gs : list (lin * lin * gkind)) : Z :=
  fold_right (fun g acc => (if is_mark g then gsz_hi fs g / 4096 else 0) + acc) 0 gs.
Lemma mark_len_nonneg : forall fs gs, 0 <= mark_len fs gs.
Proof.
  intros fs gs. induction gs as [|g r IH]; [cbn; lia|]. cbn [mark_len fold_right]. fold (mark_len fs r).
  destruct (is_mark g); [|lia]. pose proof (gsz_hi_nonneg fs g). assert (0 <= gsz_hi fs g / 4096) by (apply Z.div_pos; lia). lia.
Qed.
Lemma ledger_lden_bounds : forall E model fs BL gs, Forall (fact_ok E) fs -> Forall (gshape_ok E) gs -> Forall (blob_ent_ok model) BL ->
  (forall g, In g gs -> is_mark g = true -> snd g = GE /\ 4 * ledger_size BL <= gsz E g) ->
  ledger_size (lden_maps E BL gs) <= gsize_sum fs gs /\
  Z.of_nat (length (lden_maps E BL gs)) <= Z.of_nat (length gs) + mark_len fs gs.
Proof.
  intros E model fs BL gs HF H HB HT. pose proof (blob_len_le model BL HB) as Hlen. pose proof (ledger_size_nonneg BL) as Hnn.
  induction H as [|g gs Hg Hgs IH]; [cbn; lia|]. cbn [lden_maps gsize_sum mark_len fold_right length].
  fold (gsize_sum fs gs). fold (mark_len fs gs). specialize (IH (fun g' Hg' => HT g' (or_intror Hg'))). destruct IH as [IH1 IH2].
  pose proof (gsz_bounds E fs g HF) as Hb. destruct (is_mark g) eqn:Hm.
  - pose proof (proj2 (HT g (or_introl eq_refl) Hm)) as Hgz. rewrite ledger_size_app, length_app.
    rewrite Nat2Z.inj_add, Nat2Z.inj_succ.
    assert (Hq : Z.of_nat (length BL) <= gsz_hi fs g / 4096) by (apply Z.div_le_lower_bound; lia). lia.
  - cbn [ledger_size length]. unfold gden at 1. cbn [snd]. unfold gsz, uE in Hb. rewrite Nat2Z.inj_succ. rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
Definition null_ok (res : list (word * word)) (LIMIT : Z) (L : sst) (M : smodel) (nZ : Z) (k : gkind) (vis piece na : bool) : bool :=
  match a7c L, arg L 0, arg L 1, arg L 2, arg L 3, arg L 5 with
  | Some c7, Some c0, Some len, Some prot, Some flags, Some off =>
      (Z.eqb c7 222 && Z.eqb c0 0 && mmap_off_aligned_b (Z_to_bv 64 off) && mmap_anon_b (Z_to_bv 64 flags) && negb (w_is0 (Z_to_bv 64 len)) &&
       Z.ltb nZ 0x800000000000 &&
       (if na then negb (mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off))
                   && mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)
        else mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 off)) &&
       Z.eqb nZ (page_round_up_Z len) && shadow_ok M && (negb piece || zr_ok M) &&
       gkind_eqb k (if na then GN else if mmap_noreserve_b (Z_to_bv 64 flags) then GL else GE) && (negb vis || negb na) &&
       (page_size + ledger_size res + gsize_sum (s_facts L) (sm_maps M)
          + (Z.of_nat (length res + length (sm_maps M)) + mark_len (s_facts L) (sm_maps M)) * (nZ + page_size) + nZ
          <=? 0x7fff7f800000) &&
       (eager_sum (s_facts L) ((NA (s_next L), lconst nZ, k) :: sm_maps M) + allow_bound (null_allow (s_next L) nZ k vis piece ++ sm_allow M) <=? LIMIT))%bool
  | _, _, _, _, _, _ => false
  end.

Lemma allow_bound_app : forall a b, Forall (fun p => 0 <= snd p) a -> allow_bound b <= allow_bound (a ++ b).
Proof.
  intros a b H. induction H as [|p a Hp Ha IH]; [cbn [app]; lia|].
  change (allow_bound ((p :: a) ++ b)) with (snd p + 8192 + allow_bound (a ++ b)). lia.
Qed.

Section NullNode.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hsegb : segs_below_b segs 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.

#[using="Hsegb Hoff"] Theorem den_null : forall E L M ms model T nZ k vis piece na,
  DEN segs LIMIT model0 mem0 E L M ms model ->
  null_ok (segments_reserved segs) LIMIT L M nZ k vis piece na = true ->
  (forall a : word, place_ok model nZ a -> own_avoid E M (bv_unsigned a) (bv_unsigned a + nZ) /\
     (piece = true -> own_avoid E M (bv_unsigned a / 8 + SH_OFF) ((bv_unsigned a + nZ) / 8 + SH_OFF))) ->
  (forall E' ms' model', DEN segs LIMIT model0 mem0 E' (null_post L nZ vis piece) (null_M M (s_next L) nZ k vis piece) ms' model' ->
      agree (s_next L) E E' -> realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg (svc_set ms) model) T.
Proof. LiaFast.lf_pins (fun (Hsegb Hoff : LiaFast.U) => LiaFast.u0).
  intros E L M ms model T nZ k vis piece na Hd Hok Havoid Hk.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  unfold null_ok in Hok.
  destruct (a7c L) as [c7|] eqn:H7; [|discriminate]. destruct (arg L 0) as [c0|] eqn:H0; [|discriminate].
  destruct (arg L 1) as [len|] eqn:H1; [|discriminate]. destruct (arg L 2) as [prot|] eqn:H2; [|discriminate].
  destruct (arg L 3) as [flags|] eqn:H3; [|discriminate]. destruct (arg L 5) as [off|] eqn:H5; [|discriminate].
  repeat (apply andb_prop in Hok as [Hok ?]).
  match goal with H : (_ <=? LIMIT) = true |- _ => apply Z.leb_le in H; rename H into Hbud end.
  match goal with H : (_ <=? 0x7fff7f800000) = true |- _ => apply Z.leb_le in H; rename H into Hex end.
  match goal with H : (nZ <? 0x800000000000) = true |- _ => apply Z.ltb_lt in H; rename H into HnZ47 end.
  apply Z.eqb_eq in Hok. subst c7.
  set (H := Hof E M model) in *.
  set (ms1 := svc_set ms).
  assert (Hx8 : ms_reg ms 17 = Z_to_bv 64 222) by exact (a7_const segs E L (restrict H ms) ms 222 Hsd eq_refl H7).
  assert (Hg1 : ms_gpr ms1 1 = Z_to_bv 64 len) by exact (gpr_const segs E L (restrict H ms) ms 1 len Hsd eq_refl ltac:(lia) H1).
  assert (Hg2 : ms_gpr ms1 2 = Z_to_bv 64 prot) by exact (gpr_const segs E L (restrict H ms) ms 2 prot Hsd eq_refl ltac:(lia) H2).
  assert (Hg3 : ms_gpr ms1 3 = Z_to_bv 64 flags) by exact (gpr_const segs E L (restrict H ms) ms 3 flags Hsd eq_refl ltac:(lia) H3).
  assert (Hg5 : ms_gpr ms1 5 = Z_to_bv 64 off) by exact (gpr_const segs E L (restrict H ms) ms 5 off Hsd eq_refl ltac:(lia) H5).
  destruct (is_const_sound E _ len H1) as [_ Hlen].
  assert (HnZ : page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = nZ).
  { rewrite fg64 by exact Hlen. match goal with H : Z.eqb nZ _ = true |- _ => apply Z.eqb_eq in H; symmetry; exact H end. }
  assert (Hnz0 : w_is0 (Z_to_bv 64 len) = false) by (match goal with H : negb (w_is0 _) = true |- _ => apply negb_true_iff in H; exact H end).
  assert (HnZpos : 0 < nZ) by (rewrite <- HnZ; exact (len_nZ_pos _ Hnz0)).
  assert (HnZal : nZ mod 4096 = 0) by (rewrite <- HnZ; exact (page_round_up_Z_aligned' _)).
  assert (Hbud0 : vm_backing_used model + (if gkind_eqb k GE then nZ else 0) <= LIMIT).
  { assert (HFL : Forall (fact_ok E) (s_facts L)) by (destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
    pose proof (den_backing_le segs LIMIT model0 mem0 E L M ms model (s_facts L) Hd HFL) as Hv.
    assert (Hnan : Forall (fun p => 0 <= snd p) (null_allow (s_next L) nZ k vis piece)).
    { unfold null_allow. apply Forall_app. split.
      - destruct (vis && gkind_eqb k GL)%bool; [apply Forall_cons; [cbn; lia | apply Forall_nil] | apply Forall_nil].
      - destruct piece; [apply Forall_cons; [cbn [snd]; apply Z.div_pos; lia | apply Forall_nil] | apply Forall_nil]. }
    pose proof (allow_bound_app _ (sm_allow M) Hnan) as Hab. cbn [eager_sum fold_right fst snd] in Hbud. fold (eager_sum (s_facts L) (sm_maps M)) in Hbud.
    assert (Hhi0 : nZ <= gsz_hi (s_facts L) (NA (s_next L), lconst nZ, k)).
    { pose proof (gsz_bounds E (s_facts L) (NA (s_next L), lconst nZ, k) HFL) as Gb. unfold gsz, uE in Gb. cbn [fst snd] in Gb.
      rewrite lden_lconst, fg64 in Gb by (unfold two64; lia). lia. }
    destruct (gkind_eqb k GE); lia. }
  assert (Hex' : page_size + ledger_size (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))
                 + Z.of_nat (length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) * (nZ + page_size) + nZ
                 <= alloc_top (m_vmmaps model)).
  { assert (HFL : Forall (fact_ok E) (s_facts L)) by (destruct (sden_0 _ _ _ _ Hsd) as (_ & _ & _ & _ & _ & _ & X & _); exact X).
    rewrite ledger_size_app, length_app, Hres, Hmaps.
    destruct (ledger_lden_bounds E model (s_facts L) _ _ HFL Hgsh (proj1 Hblob) (proj2 (proj2 Hblob))) as [Hls Hln].
    destruct Hspok as [Hsp1 _]. unfold init_sp_ok, sp_window_lo in Hsp1. unfold alloc_top, stack_max_size.
    rewrite Nat2Z.inj_add in *.
    assert (Hmul : (Z.of_nat (length (segments_reserved segs)) + Z.of_nat (length (lden_maps E (blob_of model0) (sm_maps M)))) * (nZ + page_size)
                   <= (Z.of_nat (length (segments_reserved segs)) + Z.of_nat (length (sm_maps M)) + mark_len (s_facts L) (sm_maps M)) * (nZ + page_size))
      by (apply Z.mul_le_mono_nonneg_r; [unfold page_size; lia | lia]).
    lia. }
  assert (Hkk : k = (if na then GN else if mmap_noreserve_b (Z_to_bv 64 flags) then GL else GE)).
  { match goal with H : gkind_eqb k _ = true |- _ => destruct k, na, (mmap_noreserve_b (Z_to_bv 64 flags)); try discriminate; reflexivity end. }
  assert (Hvn : vis = true -> na = false).
  { intros Hv. match goal with H : (negb vis || negb na)%bool = true |- _ => rewrite Hv in H; destruct na; [discriminate | reflexivity] end. }
  assert (Hsh' : shadow_ok M = true) by assumption.
  assert (Hzr' : piece = true -> zr_ok M = true).
  { intros Hp. match goal with H : (negb piece || zr_ok M)%bool = true |- _ => rewrite Hp in H; exact H end. }
  assert (Hsvc : ms_svc_pending ms1 = Some (ms_reg ms 17)) by reflexivity.
  assert (Hno : bv_unsigned (ms_reg ms 17) = 222) by (rewrite Hx8; reflexivity).
  destruct na.
  - (* [comment removed for export] *)
    match goal with H : (negb (mmap_modeled_b _ _ _) && mmap_noaccess_b _ _ _)%bool = true |- _ => apply andb_prop in H as [Hm Hna0] end.
    apply negb_true_iff in Hm.
    apply (rzc_mmap_fresh_na segs cfg Hoff ms1 model (ms_reg ms 17) T Hh Hsvc Hno); rewrite ?Hg1, ?Hg2, ?Hg3, ?Hg5; try assumption.
    + rewrite HnZ. exact (place_ok_exists model nZ HnZpos Hex').
    + intros a Hplace. rewrite HnZ in Hplace |- *.
      apply (Hk _ _ _ (null_den segs LIMIT model0 mem0 Hsegb E L M ms model nZ k vis piece (Z_to_bv 64 flags) true a Hd Hplace Hsh' Hzr'
                          HnZpos HnZal Hkk Hvn Hbud (proj1 (Havoid a Hplace)) (proj2 (Havoid a Hplace)))).
      exact (proj1 (agree2 (s_next L) E (zval a) (rval a) _ (agree_refl _ _))).
  - (* [comment removed for export] *)
    apply (rzc_mmap_fresh_rw segs cfg Hoff ms1 model (ms_reg ms 17) T Hh Hsvc Hno); rewrite ?Hg1, ?Hg2, ?Hg3, ?Hg5; try assumption.
    + rewrite HnZ. apply (fresh_rw_guard_exists (Z_to_bv 64 flags) model nZ HnZpos); [|exact Hex'].
      unfold mmap_noreserve_backed_ok. destruct (mmap_noreserve_b (Z_to_bv 64 flags)) eqn:Hnr; [reflexivity|].
      apply Z.leb_le. rewrite Hlim. rewrite Hkk in Hbud0; rewrite ?Hnr in Hbud0. cbn in Hbud0. lia.
    + intros a Hg. rewrite HnZ in Hg |- *. apply fresh_rw_guard_iff in Hg as [Hplace _].
      apply (Hk _ _ _ (null_den segs LIMIT model0 mem0 Hsegb E L M ms model nZ k vis piece (Z_to_bv 64 flags) false a Hd Hplace Hsh' Hzr'
                          HnZpos HnZal Hkk Hvn Hbud (proj1 (Havoid a Hplace)) (proj2 (Havoid a Hplace)))).
      exact (proj1 (agree2 (s_next L) E (zval a) (rval a) _ (agree_refl _ _))).
Qed.
End NullNode.
