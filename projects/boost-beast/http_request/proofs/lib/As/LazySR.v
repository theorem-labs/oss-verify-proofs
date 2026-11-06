(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  Scfg PropExec CatSim ShapeAlg SReach LazyRestrict LazyRestrictRun LazyRestrictAlg.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Exec MState Mem.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma msteps_of_cj : forall ms ms',
  Exec.msteps segs ms ms' -> msteps segs ms ms'.
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 [Hsvc Hstep] _ IH].
  - apply mst_refl.
  - eapply mst_step; [exact Hsvc | exact Hstep | exact IH].
Qed.

Lemma msteps_to_cj : forall ms ms',
  msteps segs ms ms' -> Exec.msteps segs ms ms'.
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hstep _ IH].
  - apply Exec.msteps_refl.
  - eapply Exec.msteps_cons; [split; [exact Hsvc | exact Hstep] | exact IH].
Qed.

(* [comment removed for export] *)
Lemma evt_cj_iff : forall (P : machine_state -> Prop) ms,
  Exec.evt segs P ms <-> exists ms', msteps segs ms ms' /\ P ms'.
Proof.
  intros P ms. split; intros (ms' & H & HP); exists ms'; split; auto using msteps_of_cj, msteps_to_cj.
Qed.

(* [comment removed for export] *)
Lemma restrict_MS : forall L S R F pc fc rv m ro,
  restrict L S (MState.MS R F pc fc rv m ro) = MState.MS R F pc fc rv (restrict_mem L S m) ro.
Proof. reflexivity. Qed.

Lemma restrict_mkst : forall L S regs pc mem rom,
  restrict L S (mkst regs pc mem rom) = mkst regs pc (restrict_mem L S mem) rom.
Proof. reflexivity. Qed.

Lemma restrict_with_mem : forall L S ms m,
  restrict L S (with_mem ms m) = with_mem ms (restrict_mem L S m).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma restrict_mem_nil : forall S m, restrict_mem [] S m = m.
Proof. intros S m. reflexivity. Qed.

Lemma restrict_nil_MS : forall S R F pc fc rv m ro,
  restrict [] S (MState.MS R F pc fc rv m ro) = MState.MS R F pc fc rv m ro.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma restrict_regs : forall L S ms, ms_regs (restrict L S ms) = ms_regs ms.
Proof. reflexivity. Qed.
Lemma restrict_pc : forall L S ms, ms_pc (restrict L S ms) = ms_pc ms.
Proof. reflexivity. Qed.
Lemma restrict_svc : forall L S ms, ms_svc_pending (restrict L S ms) = ms_svc_pending ms.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hidden_zero_on (L S Zr : list (word * word)) (msF : machine_state) : Prop :=
  forall a, hiddenb L S a = true -> in_rangesb a Zr = true -> ms_mem msF a = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Definition rsub (A B : list (word * word)) : Prop :=
  forall x, in_rangesb x A = true -> in_rangesb x B = true.

Lemma rsub_refl : forall A, rsub A A.
Proof. intros A x H; exact H. Qed.
Lemma rsub_trans : forall A B C, rsub A B -> rsub B C -> rsub A C.
Proof. intros A B C H1 H2 x Hx. apply H2, H1, Hx. Qed.
Lemma rsub_cons_r : forall A r B, rsub A B -> rsub A (r :: B).
Proof. intros A r B H x Hx. rewrite in_rangesb_cons, (H x Hx). apply orb_true_r. Qed.
Lemma rsub_cons_2 : forall r A B, rsub A B -> rsub (r :: A) (r :: B).
Proof.
  intros r A B H x Hx. rewrite in_rangesb_cons in *.
  destruct (zin_rangeb (bv_unsigned x) r); [reflexivity|]. cbn in *. apply H, Hx.
Qed.
Lemma rsub_nil : forall B, rsub [] B.
Proof. intros B x Hx. discriminate Hx. Qed.

(* [comment removed for export] *)
Record lzok (L S Zr : list (word * word)) (c : config) : Prop := {
  lzok_ranges : lazy_ranges_okb segs L = true;
  lzok_inv    : lazy_inv L S (cfg_model c);
  lzok_halted : m_halted (cfg_model c) = None;
  lzok_zero   : hidden_zero_on L S Zr (cfg_ms c);
  lzok_SZr    : rsub S Zr;
  lzok_ZrL    : rsub Zr L;
  lzok_LM     : rsub L (vm_maps (m_vmmaps (cfg_model c)))
}.


(* [comment removed for export] *)
Definition hid_same (L S : list (word * word)) (msF msF' : machine_state) : Prop :=
  forall a, hiddenb L S a = true -> ms_mem msF' a = ms_mem msF a.

Lemma hid_same_refl : forall L S msF, hid_same L S msF msF.
Proof. intros L S msF a _. reflexivity. Qed.

Lemma hid_same_trans : forall L S m1 m2 m3,
  hid_same L S m1 m2 -> hid_same L S m2 m3 -> hid_same L S m1 m3.
Proof. intros L S m1 m2 m3 H12 H23 a Ha. rewrite (H23 a Ha). apply H12. exact Ha. Qed.

Lemma hid_same_unrestrict : forall L S msF ms1,
  hid_same L S msF (unrestrict_to L S msF ms1).
Proof.
  intros L S msF ms1 a Ha. unfold unrestrict_to.
  exact (unrestrict_by_hidden (hiddenb L S) msF ms1 a Ha).
Qed.

Lemma hidden_zero_on_frame : forall L S Zr msF msF',
  hidden_zero_on L S Zr msF -> hid_same L S msF msF' -> hidden_zero_on L S Zr msF'.
Proof. intros L S Zr msF msF' HZ Hs a Ha Hz. rewrite (Hs a Ha). exact (HZ a Ha Hz). Qed.

(* [comment removed for export] *)
Lemma lzok_lifted : forall L S Zr msF mo msF' mo',
  lzok L S Zr (mkCfg msF mo) ->
  lazy_inv L S mo' -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
  lzok L S Zr (mkCfg msF' mo').
Proof.
  intros L S Zr msF mo msF' mo' [HL Hinv Hh HZ HSZ HZL HLM] Hinv' Hsame Hs. split; cbn in *.
  - exact HL.
  - exact Hinv'.
  - rewrite (same_but_materialized_halted _ _ Hsame). exact Hh.
  - eapply hidden_zero_on_frame; eassumption.
  - exact HSZ.
  - exact HZL.
  - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact HLM.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sreach_dsteps : forall c c' (Q : config -> Prop),
  dsteps segs c c' -> sreach segs Q c' -> sreach segs Q c.
Proof.
  intros c c' Q H; induction H as [c | ms model ms' model' c3 Hh Hsvc Hacc H IH]; intros HQ; [exact HQ|].
  eapply sreach_silent1; [apply node_account; [exact Hh | exact Hsvc | exact Hacc] | apply IH; exact HQ].
Qed.

Section WithLazy.
Variables L S Zr : list (word * word).

(* [comment removed for export] *)
Lemma sreach_step1_lazy : forall msF ms1 mo (Q : config -> Prop),
  lzok L S Zr (mkCfg msF mo) ->
  ms_svc_pending msF = None ->
  RiscvSemantics.step segs (restrict L S msF) = MachineOk ms1 ->
  (forall mo', lzok L S Zr (mkCfg (unrestrict_to L S msF ms1) mo') ->
              same_but_materialized mo mo' ->
              restrict L S (unrestrict_to L S msF ms1) = ms1 ->
              sreach segs Q (mkCfg (unrestrict_to L S msF ms1) mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros msF ms1 mo Q Hok Hsvc Hstep Hk.
  destruct (account_step_restrict segs L S (lzok_ranges _ _ _ _ Hok) msF ms1 mo (lzok_inv _ _ _ _ Hok) Hstep)
    as (mo' & Hacc & Hinv' & Hsame & Hnone).
  eapply sreach_silent1.
  - apply node_account; [exact (lzok_halted _ _ _ _ Hok) | exact Hsvc | exact Hacc].
  - apply Hk; [| exact Hsame | apply restrict_unrestrict_to; exact Hnone].
    eapply lzok_lifted; [exact Hok | exact Hinv' | exact Hsame | apply hid_same_unrestrict].
Qed.

(* [comment removed for export] *)
Theorem sreach_msteps_lazy : forall msF ms1 mo (Q : config -> Prop),
  lzok L S Zr (mkCfg msF mo) ->
  msteps segs (restrict L S msF) ms1 ->
  (forall msF' mo', lzok L S Zr (mkCfg msF' mo') ->
                    same_but_materialized mo mo' ->
                    restrict L S msF' = ms1 ->
                    hid_same L S msF msF' ->
                    sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros msF ms1 mo Q Hok Hms Hk.
  destruct (msteps_restrict segs L S (lzok_ranges _ _ _ _ Hok) msF ms1 mo (lzok_inv _ _ _ _ Hok) (lzok_halted _ _ _ _ Hok) Hms)
    as (mo' & Hd & Hinv' & Hsame & Hh' & Hr).
  eapply sreach_dsteps; [exact Hd|].
  apply Hk; [| exact Hsame | exact Hr | apply hid_same_unrestrict].
  eapply lzok_lifted; [exact Hok | exact Hinv' | exact Hsame | apply hid_same_unrestrict].
Qed.

(* [comment removed for export] *)
Theorem evt_sreach_lazy : forall (P : machine_state -> Prop) msF mo,
  lzok L S Zr (mkCfg msF mo) ->
  Exec.evt segs P (restrict L S msF) ->
  sreach segs (fun c => P (restrict L S (cfg_ms c))
                     /\ lzok L S Zr c
                     /\ same_but_materialized mo (cfg_model c)
                     /\ hid_same L S msF (cfg_ms c))
         (mkCfg msF mo).
Proof.
  intros P msF mo Hok Hevt. apply evt_cj_iff in Hevt. destruct Hevt as (ms1 & Hms & HP).
  eapply sreach_msteps_lazy; [exact Hok | exact Hms |].
  intros msF' mo' Hok' Hsame Hr Hs. apply sr_done. cbn. rewrite Hr. auto.
Qed.

(* [comment removed for export] *)
Theorem evt_sreach_lazy_k : forall (P : machine_state -> Prop) msF mo (Q : config -> Prop),
  lzok L S Zr (mkCfg msF mo) ->
  Exec.evt segs P (restrict L S msF) ->
  (forall msF' mo', lzok L S Zr (mkCfg msF' mo') ->
                    same_but_materialized mo mo' ->
                    hid_same L S msF msF' ->
                    P (restrict L S msF') ->
                    sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros P msF mo Q Hok Hevt Hk.
  eapply sreach_seq; [exact (evt_sreach_lazy P msF mo Hok Hevt)|].
  intros [msF' mo'] (HP & Hok' & Hsame & Hs). cbn in HP, Hok', Hsame, Hs.
  apply Hk; assumption.
Qed.

(* [comment removed for export] *)
Corollary evt_sreach_lazy_at : forall (P : machine_state -> Prop) msF ms mo (Q : config -> Prop),
  lzok L S Zr (mkCfg msF mo) ->
  restrict L S msF = ms ->
  Exec.evt segs P ms ->
  (forall msF' mo', lzok L S Zr (mkCfg msF' mo') ->
                    same_but_materialized mo mo' ->
                    hid_same L S msF msF' ->
                    P (restrict L S msF') ->
                    sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof. intros P msF ms mo Q Hok <- Hevt Hk. eapply evt_sreach_lazy_k; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem lzok_open_window : forall W msF mo,
  lzok L S Zr (mkCfg msF mo) ->
  (forall a, zin_rangeb (bv_unsigned a) W = true -> in_rangesb a Zr = true) ->
  (eager_used mo + pages_total (W :: S) * page_size <= vm_limit (m_vmmaps mo))%Z ->
  lzok L (W :: S) Zr (mkCfg msF mo)
  /\ restrict L (W :: S) msF
     = with_mem (restrict L S msF)
         (fun a => if zin_rangeb (bv_unsigned a) W && hiddenb L S a
                   then Some (Z_to_bv 8 0) else ms_mem (restrict L S msF) a).
Proof.
  intros W msF mo [HL Hinv Hh HZ HSZ HZL HLM] HW Hb. cbn in *. split.
  - split; cbn; [exact HL | apply lazy_inv_open_window; assumption | exact Hh | | | exact HZL | exact HLM].
    + intros a Ha Hz. apply HZ; [| exact Hz]. eapply hiddenb_mono_cons. exact Ha.
    + intros x Hx. rewrite in_rangesb_cons in Hx. apply orb_true_iff in Hx.
      destruct Hx as [Hx | Hx]; [apply HW; exact Hx | apply HSZ; exact Hx].
  - rewrite (restrict_open_window_eq L W S msF).
    match goal with |- with_mem ?x ?f = with_mem ?y ?g => replace g with f; [reflexivity|] end.
    apply functional_extensionality. intros a.
    destruct (zin_rangeb (bv_unsigned a) W) eqn:EW; cbn [andb]; [|reflexivity].
    destruct (hiddenb L S a) eqn:Eh.
    + apply HZ; [exact Eh | apply HW; exact EW].
    + unfold restrict_mem_by. rewrite Eh. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem lzok_open_hidden_window : forall W msF mo,
  lzok L S Zr (mkCfg msF mo) ->
  (forall a, zin_rangeb (bv_unsigned a) W = true -> in_rangesb a Zr = true) ->
  (forall a, zin_rangeb (bv_unsigned a) W = true -> hiddenb L S a = true) ->
  (eager_used mo + pages_total (W :: S) * page_size <= vm_limit (m_vmmaps mo))%Z ->
  lzok L (W :: S) Zr (mkCfg msF mo)
  /\ restrict L (W :: S) msF
     = with_mem (restrict L S msF)
         (fun a => if zin_rangeb (bv_unsigned a) W
                   then Some (Z_to_bv 8 0) else ms_mem (restrict L S msF) a).
Proof.
  intros W msF mo Hok HW Hhid Hb.
  destruct (lzok_open_window W msF mo Hok HW Hb) as [Hok' E]. split; [exact Hok'|].
  rewrite E. f_equal. apply functional_extensionality. intros a.
  destruct (zin_rangeb (bv_unsigned a) W) eqn:EW; cbn [andb]; [|reflexivity].
  rewrite (Hhid a EW). reflexivity.
Qed.

(* [comment removed for export] *)
Corollary lzok_open_hidden_window_wb : forall W msF mo (B : Z),
  lzok L S Zr (mkCfg msF mo) ->
  (forall a, zin_rangeb (bv_unsigned a) W = true -> in_rangesb a Zr = true) ->
  (forall a, zin_rangeb (bv_unsigned a) W = true -> hiddenb L S a = true) ->
  (pages_total S <= B)%Z ->
  (eager_used mo + (bv_unsigned (snd W) / page_size + 2 + B) * page_size <= vm_limit (m_vmmaps mo))%Z ->
  lzok L (W :: S) Zr (mkCfg msF mo)
  /\ restrict L (W :: S) msF
     = with_mem (restrict L S msF)
         (fun a => if zin_rangeb (bv_unsigned a) W
                   then Some (Z_to_bv 8 0) else ms_mem (restrict L S msF) a).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazySR.WithSegs.lzok); constr:(L); constr:(S); constr:(Zr); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.zin_rangeb); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.in_rangesb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.hiddenb); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.pages_total); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.eager_used); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Corelib.Init.Datatypes.snd); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_limit); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazySR.WithSegs.WithLazy.lzok_open_hidden_window); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.win_npagesZ); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.cl_bounds); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.cl_lo); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.cl_hi); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.pages_total_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.LiaTuning.zify_done); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.pages_total_cons)|] [|@a; @z; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__x6; @__x7; @__x8; @__x9; @__x10; @__p1; @__p2; @__p3; @__p4; @__arith; @H2; @H8; @H14; @H18; @H17; @H16; @H15; @H13; @H12; @H11; @H10; @H9; @H7; @H6; @H5; @H4; @H3; @H1; @__sat1; @__sat2; @__sat3; @H0; @H; @Hb; @HB; @Hhid; @HW; @Hok; @B; @mo; @msF; @W|] "#(\#G$N#Q$:#n$;$9#+#*#e$A#%#G#(#T#X#[#)#$###'$H#F#-#/#1#,$@#N#&#.#0#~#@#D$(#S#U#Y#_#p#t#v#2#5#=#>#?$$#B#C$,$/$'#L#K#J#V#R#\#]#l#u#w#y#3#4#6#7#8#9#:#;#<#A$&$%$)$0$1$2$4$6$8$<$B$J$K$M$N$L$O$P#j#i#P#O#^#M#m#`#W#s#Z#r#b#d#c#o#q$C$>$=$G$3$E#a#h#g$7#k$.$-$+$5$D$F$I#f#x#z#{#|#}$#$*$?K$&%$'$$(%$)%$*&$+%$,%$-%$.%$/&$0%$1$$2$$3%$4'$5*$6*$7'$8&$9$$:$$;$$<+$=$$>$$?%$@&$A%$B$$C&$D)$E$$F%$G%$H%$I%$J%$K%$L&$M%$S-$#$#$#$#$#USG#USH#VSI##VSJLS#XSKS5OS6#)'S$VS7#N'P#QVSLS#S6'P#Qk##%#k#$,#VS7)R'P#QWSMS5OS#'P#Qk##%#k#$2#US8O##S.6N,66I)8#-#JB@&$#&#S%+#J&*#7N8##%#:H&#16I+S$J&$#7I8##%#j#%C#USNH.H#E#WS9s#-s#-H)s#/##&#%&#,s#1s#1H)s#3#&'#/H#$#&%J*%#%%#(0J'C#E()J'C#E#E>-.J&#s#(#A#%&#+s##JVS:1:'C$#%&#%,#%/#%2#%;#USOO#Es#:/S($s#O$#$#$#$#$#B#VS;*##E+#E%/S)(#'#E#k##&#k##(#,s#\s#\S/)s#^#VSP#-#E$,s#`s#`S0)s#b#-#1#E#k##0#k##(#.S)VS;#6#E$.S*(#9#E#k##8#k##'#C/='C>EUSQ#,s#qs#qS*)s#s#-#B+s###(%s#$&$#'C'#k##*#D)s#(*Es#),s#{s#{S<)s#}#(#s#,#E#*$s#.%$#k##)#E(s#1*s#2E,s$(s$(SR)s$*#(#s#5*s#6##$E%$#k##)#F(s#:,s$0s$0SS)s$2#-#s#='C#Ek##s###G&s#@,s$6s$6S=)s$8#(#s#C'C#$k##s#)#H&s#Fm#S1#.STC#s#I.SU-#s#K+s#L#(%s#M&$#'C'#k##s#3#D)s#Q.SV(#s#S#E#*$s#U%$#k##s#0#E(s#X.SW(#s#Z*s#[##$E%$#k##s#.#F(s#_.SX-#s#a'C#Ek##s#G#G&s#d.SY(#s#f'C#$k##s#L#H&s#im#S1#/SZC#s#l/S>-#s#n+s#o#(%s#p&$#'C'#k##s#V#D)s#t/S?(#s#v#E#*$s#x%$#k##s#S#E(s#{/S@(#s#}*s#~##$E%$#k##s#Q#F(s$&/S2-#s$('C#Ek##s#j#G&s$+/S[(#s$-'C#$k##s#o#H&s$0m#S1#VS\Es$2VSAS]#m##s#iUS%#/SB(#s$7#E#*$s$9%$#US/).SC(#s$=#E#*$s$?%$#US=/,s%7s%7S3)s%9#(#s$D#E#*$s$F%$#$s$I$#$#$#$#$#$#$#$#$#$#$#B#VSDC#;SE;#;#;#<C#=C(#VSDCs$\<C(=C$#<C+=C-#<CSE=C(#IC%#IC(#IC,#VS^#S_US`S4WSFS4$#USaS4USbC>CS+4C$S%#>CH4C#R&4C%L#>CN>CS(4C*I#4C%S.#4C'S##UScCUSdCJCs$wJCE1C$S,#2&GDDF#KZSe'GDDF#USfD?s%y$#0C#?S-?#?#0C#@C/#$'$#0C#5C&#1C,S,#26GDDF#K97GDDF21#0C-1C7S&#2:GDDF#KA;GDDFS)3<GDDF$#A=GDDFS0A>GDDFS*1C.S,=2@GDDF#KAAGDDFS<0Cs&60C4JCs%v5C$#1C&S&#2s#'GDDF#K3s#(GDDF)#@C)s#(WSgCA41C$S,#2s#,GDDF#K3s#-GDDF'#3s#.GDDF0#3s#/GDDF3#3s#0GDDF5#3s#1GDDF7#0CS-0Cs#,5C1#@C#s#45C&#0Cs&J1C$S&#2s#9GDDF#K0Cs#01C#S&*2s#<GDDF#K5C=%@C#s#=5C/#1C#S&+2s#AGDDF#K9s#BGDDF(s#<#9s#CGDDF,s#=#9s#DGDDF5s#>#9s#EGDDFs#0s#?#VShs#FFVSAPQVSiS$L'P#Qm$%#WSjCES#XSkS$L$#l#&*)#l#'s#Ps#O#l#(s#]s#\#j#)C#j#*C#j#+C#j#,C#j#-C#j#.C#j#/C#j#0C#j#1C#j#2C#j#3M#j#4M#j#5M#j#6M#k##s%ZSl+s%wS(&#S+'CH#k##&##EI%#S/'CS+E&Rs&\#L#%S*#+Ls&%VS:HI'C$#%&#%*#%S0#%S)#%.#&Is&g&#R+#s&/&L###N#NI&NR+#s&4&S%###Ik##'#k##)#k##/#k##>#k#)C#k#*C#k#+C#k#,C#k#-C#k#.C#k#/C#k#0C#k#1C#k#2C#k#3M#k#4M#k#5M#k#6M#:S'#E#.S'(#s&L'C#EWS9s'Cs'CS')s'E#,s'Es'ES')s'G#&%#/S'#$#&%s&U*%#%%##/+-(s&Y()s&Z-,s&[7S38#6S3fS$74*)('.6&SC$s'C8#S+S>S?S@l#7s#I:#l#8s$~s$x#l#9s%)s%$#l#:s%0s%+#6S2:SB&#s'J+#s&g&&#7S28##%#m#+#l#;s%>s%?#l#<s%Es%A#l#=s%Ks%G#l#>s%Ss%M#l#:s%[s%U#l#?s%ds%]#l#@s%gs%h#l#As%ns%j#l#Bs%ts%p#l#Cs%|s%v#l#9s&(s%~#l#Ds&1s&*#l#Es&4s&5#l#Fs&<s&7#l#Gs&Cs&>#l#Hs&Ms&E#l#8s&Ws&O#l#Is&cs&Y#l#Js&ks&e#l#Ks&us&n#l#Ls'$s&y#6H:S(&#s'h+#J&&#7H8##%#m#+#l#Ms'8s'7#l#Ns'Ys':#WSFs(%HOUS8#VSmHOZSnCs'es'^&$#[SoHIRS%S.L#j#Os'i#j#Ps'v#j#Qs'y#j#Rs($#j#Ss(,#j#TC#j#USp#j#VSq#j#Ws(2##"). Qed.

End WithLazy.

(* [comment removed for export] *)
Lemma lazy_inv_rewindow : forall L S S' m,
  lazy_inv L S m ->
  incl (m_vm_materialized m) (all_pages S') ->
  (eager_used m + pages_total S' * page_size <= vm_limit (m_vmmaps m))%Z ->
  lazy_inv L S' m.
Proof. intros L S S' m [Hl Hnd _ _] Hincl Hb. split; assumption. Qed.

(* [comment removed for export] *)
Lemma materialized_forget_outside : forall lo hi m p,
  In p (m_vm_materialized (vm_forget_range lo hi m)) ->
  In p (m_vm_materialized m) /\ ~ (lo <= bv_unsigned p < hi)%Z.
Proof.
  intros lo hi m p Hp. rewrite m_vm_materialized_vm_forget_range in Hp.
  apply filter_In in Hp. destruct Hp as [Hin Hout]. split; [exact Hin|].
  unfold page_outside_range in Hout. intros [H1 H2].
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.ltb_lt _ _) H2) in Hout. discriminate.
Qed.

(* [comment removed for export] *)
Lemma lazy_inv_forget_drop : forall L S1 S2 lo hi m,
  lazy_inv L (S1 ++ S2) m ->
  (forall p, In p (all_pages S1) -> (lo <= bv_unsigned p < hi)%Z) ->
  (eager_used (vm_forget_range lo hi m) + pages_total S2 * page_size <= vm_limit (m_vmmaps m))%Z ->
  lazy_inv (maps_subtract L lo hi) S2 (vm_forget_range lo hi m).
Proof.
  intros L S1 S2 lo hi m Hinv HS1 Hb.
  pose proof (lazy_inv_vm_forget_range L (S1 ++ S2) lo hi m Hinv) as H.
  assert (Hb' : (eager_used (vm_forget_range lo hi m) + pages_total (S1 ++ S2) * page_size
                 <= vm_limit (m_vmmaps m))%Z -> lazy_inv (maps_subtract L lo hi) (S1 ++ S2) (vm_forget_range lo hi m))
    by exact H. clear H.
  (* [comment removed for export] *)
  destruct Hinv as [Hl Hnd Hincl Hbud]. split.
  - rewrite m_vm_lazy_vm_forget_range, Hl. reflexivity.
  - rewrite m_vm_materialized_vm_forget_range. apply NoDup_filter. exact Hnd.
  - intros p Hp. destruct (materialized_forget_outside lo hi m p Hp) as [Hin Hout].
    specialize (Hincl p Hin). rewrite all_pages_app in Hincl. apply in_app_iff in Hincl.
    destruct Hincl as [H1 | H2]; [| exact H2]. exfalso. apply Hout. apply HS1. exact H1.
  - rewrite m_vmmaps_vm_forget_range. exact Hb.
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.ex Sort Prop.

(* [comment removed for export] *)
Lemma win_pages_inside : forall r lo hi p,
  (lo <= cl_lo r)%Z -> (cl_hi r <= hi)%Z -> (hi <= 2 ^ 64)%Z ->
  In p (win_pages r) -> (lo <= bv_unsigned p < hi)%Z.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.cl_lo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.cl_hi); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.Lists.List.In); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.win_pages); (KReplay.sort_at constr:(@Stdlib.Lists.List.count_occ_map) [0]); (KReplay.sort_at constr:(@Stdlib.Lists.List.count_occ_map) [1; 0]); constr:(@Corelib.Init.Datatypes.list); constr:(@kc__1); constr:(@Corelib.Lists.ListDef.map); constr:(@Corelib.Init.Logic.ex); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.Lists.List.in_map_iff); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.win_page); constr:(@Corelib.Lists.ListDef.seq); constr:(@Corelib.Init.Datatypes.O); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.win_npages); constr:(@kc__2); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Peano.le); constr:(@Corelib.Init.Peano.lt); constr:(@Corelib.Init.Nat.add); constr:(@Stdlib.Lists.List.in_seq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.cl_bounds); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.fst); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.snd); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.win_npagesZ); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_lt); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.Arith.PeanoNat.Nat.add); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_add); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.micromega.ZifyInst.of_nat_to_nat_eq); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.LiaTuning.zify_done); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Corelib.Init.Logic.False); constr:(@stdpp.bitvector.definitions.bv_unsigned_in_range); constr:(@stdpp.bitvector.definitions.bv_modulus); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@stdpp.bitvector.definitions.bv_wrap); constr:(@stdpp.bitvector.definitions.bv_wrap_small); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@stdpp.bitvector.definitions.Z_to_bv_unsigned); constr:(@kc__2 (@Corelib.Init.Datatypes.nat))|] [|@x; @y; @l; @f; @B; @A; @p; @n; @start; @len; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__x6; @__x7; @__x8; @__p1; @__p2; @__p3; @__p4; @__p5; @__arith; @__sat3; @__sat1; @__sat2; @__sat4; @__sat5; @z0; @H0; @cstr; @Hi0; @a; @__x9; @zh; @H1; @H7; @H13; @H17; @H16; @H15; @H14; @H12; @H11; @H10; @H9; @H8; @H6; @H5; @H4; @H3; @H2; @H; @z; @__p6; @__sat6; @__sat7; @__sat8; @z3; @Hr; @Hi'; @Hb; @Hi; @i; @Hp; @Hnw; @Hhi; @Hlo; @hi; @lo; @r|] "#1E#[%%#c$W$&$X$V#t#[##$a#%#$#&#,#w#'#)#+#*$*$2#($d#/#.#-#0$`$I#6$N$e#A#B#1#2$1#F#5#:#;#Z#b#4#}#d$(#~#{#D#E#3$6$<$=$9$:$;$8$4$0$>#9$?#=#<$B#>$D#?$b#8#@$m$o#C$p$q$r$t$s$x$}#m#l#k#u$G$F$Y$i$j#G#N#S%#%%#`#_#^#g#j#s$$$%#7$C$E$O$R$S$U$c$g$k$l$h$n#H#I#J#K#L#M#O#P#Q#R#T#U$v$z$y$w${$~%$%&%(%'%)%*#|#y#q#r$]$\$Z$+#z$T$K#e$P#f#i#a$.$)$-$L$^#v$M$,#x$7$f$3$J$H$[$#$Q$5$A$_#p$'$/$@$u$|#h#o#nU$V%#O%$W&#R%#P%$X'$Y*$Z*$[%$\%$]+$^&$_$$`'$a$$b&$c$$d%$e&$f%$g%$h%$i%$j$$k$$l$$m%$n&#6$#x%$o%$p%$q&$r)#N%$s%#Q%$t%$u/$v%$w$$x%$y&$z%${%$|&$}&$~$%#'%$(3S<3#3#3#3#3#USs#USt#VSu##/N$L#1Q$#LR/R+VSv$#$N#USwR2-N#k##MMUSeLSQNLM2NJ#UQJ%S'#L2RJN#$#j#$S'#LS'#k##)#UNJ%Q#M2S'JL#$#j#$Q#LQ#SS'QNL2QM#k##%##,#US'J%R#N2S$JQ#$#j#$R#LR#k##+#j##*#SRS'QN2S'L#k##8#j###Mj##9#YSxQNLMJT;2)$#j#%L#j#&s#&#j#'s#(#j#(Sf#j#)Sg#k#%LAk#&s#+#k#'s#-#k#(Sf#k#)Sg#UShS#<S#9P#ZJHs#?%#S'M@OJ%s#A#R<O9P#2HJ##&#j#$H#LH#@S+J%s#I#S$<S+9P#2HJ##&#j#$H#LH#,s#QS$$O#&$S##$#j##'#@S*J%s#V#S#<S*9P#2HJ##&#j#$H#U#J@S)J%s#^#O<S)9P#2HJ##&#@S,M%s#d#S+<S,9P#2HM##&#,s#jS*$S,#&$S)#$#j##'#<S49P#2HL#@S5N%s#r#S)@SEQ<S=9P#2HS'#,s#xM$S=#&$SE#$#k##'#j#*s#|#<SE9P#2HQ#9ML2HJ#ELMFLNGM##%#k##'#EMJFMLGJ##%#9LN2HM#k##%##*#ENLFNQGL##%#k##)#j##(#9NQ2HL#k##4#j###Mj##5#WSyLMJT70)$#j#+H#j#,H#j#-H#k#+H;k#,H#k#-H#<S8XJ#PRMEPRFP%GR##%#USzS//S/$E#Ms$Os$OS/,s$Q#$&##&#5s$Ss$SS/,s$U#''#1S/$$#'%S%&%##%#+0S%%C#E+)S%%C#E;S/$E#6/S%'#s$\$&##&#4(S%N2;%C$##&##-##0##3##<#EPS#;S{US6#FP#GS###'#?S#$E#AE)'E#&&##&#AEJj#$C#U#/'E#&,#=CE=C.IHCS>S&S?SFPE$S#/#j#$CJ=C6`SGCHCCS6$S&+SH77#fSIHHHCCCSJS&S&S&S@SKPE(7+#IHCSAS&SBSLS#4(7+#ZSM;74+(#XSN71#MUSOO?O$E#;SPVSQE#&E$AE%%C#&#%#$(E%C&E#$#O&#;S9AE#1S:J#S%$E$$ES%1SR+#S%$E#k##&#k##(#5s%Ds%DSS,s%F#VST#S%$E$5s%Hs%HSU,s%J#6#S%$E#k##0#k##(#VS|s%Hs%G&Es%I$Es%I&Es%Ik##$#k##&#$Es%NWS}s%Os%NMj##SV#j#.%#$Es%Pk##SV#k#.(#/SWJ#S%$E$/S2+#S%$E#k##s#%#k##'#VSiEs%]=Sj#m##8UL#:P:#:#:#:#:#7C#7C%7C'.C$#.C&#B#S07CP.C'#.C*#B#S0US~S.CS.$#CS.)#USeS.HCRUT#C0C$N#0C#L$HCS$HCS#0C$Q#HCS'0C$S##0C(M#UT$CUT%CD#GDDFS+KS<3#K#8C#8Cs&7(C$S-#)*GDDF#K*+GDDF*#D,GDDFS*VSXCE(C)S-#)/GDDF#K*0GDDF&#[Sk1GDDF(#UT&D8CS<(C)S(#)5GDDF#KD6GDDFS)>C,2(C'S1#)9GDDF#K*:GDDF&#8Cs&I(C1S(#)=GDDF#KD>GDDFS,*?GDDF$#K>8C#8Cs&O>C$#Ks&S8C#(C%S(#)s#'GDDF#KKs&V8C#>C)#(C(S1#)s#,GDDF#K*s#-GDDF(#Ds#.GDDFS4*s#/GDDF$#*s#0GDDF3#(C@S1s#+)s#2GDDF#K-s#3GDDF%s###-s#4GDDF<s#$#-s#5GDDFBs#%#-s#6GDDFs#'s#&#VT's#7F=SlSmVT(JL%Sl#Smm$%#WT)CEMXT*JL$#l#/*)#l#0s#As#@#l#1s#Ms#L#j#2C#j#3C#j#4C#j#5C#j#6C#j#7C#j#8C#j#9C#j#:I#j#;I#j#<I#j#=I#j#>I#%CS$M#S##%CS$E#O#O%#$EM'EO&L##S)#$ES'##S4'S$S#$#R'$O&R##%###S5#)#&QS'k##$#k##.#k##2#k##4#k#2C#k#3C#k#4C#k#5C#k#6C#k#7C#k#8C#k#9C#k#:I#k#;I#k#<I#k#=I#k#>I#/S3+#S%%C#E1S3+#S%%C#E;S3$E#5s'Fs'FS3,s'H#6#S%'#s'C$(##(#4*S%N.1%C$##&##/##3#Ms'Rs'RS3,s'T#$8#?S/$E#$5E&E6eJ*'%$#S$S%4(:=7&S#OS+S*l#?s#C?#l#@s$Ss$g#l#As$^s$X#l#Bs$ds$a#l#@s$ns$i#l#Cs$ws$p#l#Ds%&s${#l#Es%)C#l#Fs%4s%,#l#Gs%9s%7#l#Hs%;s%J#&s%Ps%UEPO;SYUS6#FP#GO##'#AE''E#&s%C##s%C#Us%T+'E#&s%G#=Cs%HIHCS>S&S?SFPEs%TOs%I#=C0`SGCHCCS6s%SS&s%ZSH11#fSIHHHCCCSJS&S&S&S@SKPEs%W1)#IHCSAS&SBSLOs%M'1)#ZSM51s%M)'#XSN1-#LUSOS+?S+$E#VSQEs%G&Es%H%Cs%Hs%I#$#$s%KE%Cs%KE#$#O&#;S:AE#1SS3s(/3#3#3#3#3#R#J*#$E+$E%1SU+#'$E#k##&#k##(#5s(<s(<SR,s(>#VST#-$E$5s(@s(@SW,s(B#6#1$E#k##0#k##(#/SZJ#6$E$+s#i8$E#k##7#k##&#5s(Ms(MS2,s(O#VS[#>%C?EUT+#6s#iA4B#+s#ks##'$#%Cs#m#k##(#VS\s#os#'&Es#(5s(Zs(ZS],s(\#+#s#+$E#&$s#-#$#k##)#VS^(s#0&s#1E5s(cs(cSC,s(e#+#s#4&s#5#$$E#$#k##)#VS_(s#95s(ks(kSD,s(m#6#s#<%C#Ek##A#VS`&s#?5s(qs(qS7,s(s#+#s#B%C#$k##s#'#VSa&s#Em#Sb#/SnVS[#s#H/T,6#s#J4s#K#+%s#L'$#%C'#k##s#1#VS\)s#P/T-+#s#R$E#&$s#T#$#k##s#0#VS^(s#W/T.+#s#Y&s#Z#$$E#$#k##s#.#VS_(s#^/T/6#s#`%C#Ek##s#E#VS`&s#c/T0+#s#e%C#$k##s#J#VSa&s#hm#Sb#1T1VS[#s#k1So6#s#m4s#n#+%s#o'$#%C'#k##s#T#VS\)s#s1T2+#s#u$E#&$s#w#$#k##s#S#VS^(s#z1T3+#s#|&s#}#$$E#$#k##s#Q#VS_(s$%1T46#s$'%C#Ek##s#h#VS`&s$*1T5+#s$,%C#$k##s#m#VSa&s$/m#Sb#VSiEs$1=Sj#m##s#iUQ#1Sp+#s$6$E#&$s$8#$#US*)/T6+#s$<$E#&$s$>#$#US8/5s)rs)rT7,s)t#+#s$C$E#&$s$E#$#VS:JMj#Is''#k#Is'(s'$USSs&tVT8Cs$K:s&o:#7C#PC&#7C&PC(#PC)s&s.C$#.C'#B#S0UT9S<VT:C#:-:#:#7C#WScC'#7C&7Cs'(7Cs'*WScC+#.C#s&}.C&#.C(#.C*#PC<s'%:.7C#7C2PC@#WScC5s'..C/..C$#.C>#.C'#.C5#.C+#.C.#B#S0VT;1#CS.#s'0CS.B#HCQ0C#Os'+0Cs'0Os'+0C$L#0Cs'+Os'1HCO0Cs'3O#0C%N#0C'M#VSXCs%#(C#S-s&~)s'.GDDF#KZT<s'/GDDF#8Cs'.Ks&o8C#QC)#>C#s&i(C'S-#)s'6GDDF#K-s'7GDDF*s''#3s&v8C#QC0#>C#s&w(Cs'+S-#)s'=GDDF#K-s'>GDDF1s'.#3s&y8C#(Cs'6S1#)s'BGDDF#K3s'@8C#(C#S-')s'FGDDF#K*s'GGDDF'#(C*S(s'=)s'IGDDF#K*s'JGDDF#s'@[Sks'KGDDF&#(Cs'AS(s'F)s'MGDDF#K>Cs'C,(Cs'IS1#)s'PGDDF#K*s'QGDDFs'=#(Cs'LS14)s'SGDDF#K*s'TGDDFs'As'8(Cs'5S-s'J)s'VGDDF#K(Cs'0S-s'L)s'XGDDF#KDs'YGDDFS5QC<s#0WSdCs#-s'J(C$S-#)s']GDDF#K*s'^GDDF'#*s'_GDDF)#*s'`GDDF,#*s'aGDDFs'5#*s'bGDDF0#QCs#9s']>Cs'S#>C#s#;(C#S(s#8)s'gGDDF#K-s'hGDDF(s'X#-s'iGDDF8s'Y#-s'jGDDF;s'Z#-s'kGDDF@s'[#-s'lGDDFs##s'\#-s'mGDDFs#1s']#-s'nGDDFs#9s'^#l#/#s':s'4l#0s#Gs'q#l#1s#Qs'}#j#2C#j#3C#j#4C#j#5C#j#6C#j#7C#j#8C#j#9C#j#JC#j#:I#j#;I#j#<I#j#=I#j#>I#k##s%ZT=4s%xO'#S'%CN#k##&#%CL%k##(#&ES$%CS#S$#$#$S$E##S*O%#$EQ'ES+&S'##S4#&RS+$ER##S=%COE%CS+E4S*s&1NS#R%C$##S/##'##)##S8##,#4s&9S#'S$#'#s&;$#Ok##'#k##4#k##6#k##:#k##<#k##s###k##s#&#k#2C#k#3C#k#4C#k#5C#k#6C#k#7C#k#8C#k#9C#k#JC#k#:I#k#;I#k#<I#k#=I#k#>I#;S;$E#5s,)s,)S;,s,+#6#s&V'#s,&$(##(#Ms,/s,/S;,s,1#'#)1S;$$#'%s&_&%##%#/S;$#*?So$E#%CS2E6,s&g6(s&h+.s&i+*s&ji#8J4,*('&%S2;$#0)+S)S8S3S]SCSDS7l#?s#T=#l#@s%%s)N#l#Bs%(s%'#l#KNSV#l#Ls%2s%,#l#Ms%9s%4#l#Ns%@s%;#/Sp?Sn4s&u#'%#'#s&w$#s%Em#)#l#Os%Ls%M#l#Ps%Ss%O#l#Qs%Ys%U#l#Rs%as%[#l#Ns%is%c#l#Ss%rs%k#l#Ts%us%v#l#Us%|s%x#l#Vs&&s%~#l#Ws&.s&(#l#Ms&6s&0#l#Xs&?s&8#l#Ys&Bs&C#l#Zs&Js&E#l#[s&Qs&L#l#\s&[s&S#l#Ls&es&]#l#]s&os&g#l#As&xs&s#l#Bs)is)f#l#@s)ss)n#l#Cs'(s&}#l#Ds'3s',#l#Es'=C#l#Fs'Gs'@#l#Gs'Ks'I#l#Hs'Ms'X#/SY4S%s*@'$#'#S%1SY$$#m#)#Ms,qs,qSPVSqs,s#,s,t$$E#UT>s,v&%##%#5s,xs,xS9VSqs,z#,s,{$$E#&$)#$#/S:?S)4S%#'%#VT?s-'#$S:J&JS9#$#j#^C#EPS)US6s'`FP#GS)##&#$E/'Es'd&1##%#Us*ts'h'E#&5#=C6IHCS>S&S?SFPEs*tS)7#=Cs'm`SGCHCCS6s*sS&s*zSHs'ns'n#fSIHHHCCCSJS&S&S&S@SKPEs*w1)#IHCSAS&SBSLS);'1)#ZSM41/)'#XSN1-#S'USOS,?S,$E#;SRVSQE#&E$AE%%C#&#%#$(E%C&E#$#O&#;SUAE#1SWJ#s'z$E$1S2+#s'}$E#k##s'|#k##'#5s-Vs-VSZ,s-X#VST#s('$E$$Es'fk##s('#k##%#/S]J#s(-$E$/SD+#s(0$E#k##s(/#k##'#7Cs*\.C#s*Q.Cs&C#B#S0.Cs&7s*T.Cs*Z#B#S0CS.#s*SCS.'#0Cs*MS$s*P0Cs&&L#0Cs*LNs*S0C$M#(Cs*?S(s%x)s*KGDDF#K(Cs*AS(s*-)s*MGDDF#KDs*NGDDFO*s*OGDDF$#QCs&&s%~>Cs*K#>C#s&((C#S(s*0)s*TGDDF#K*s*UGDDFs%fs*TWSdCs*3s*P(Cs%[S-#)s*XGDDF#K*s*YGDDFs*-#*s*ZGDDFs*>#*s*[GDDFs*G#*s*\GDDFs*R#*s*]GDDF*#(Cs*;S(s*E)s*_GDDF#K(Cs*OS(s*Z)s*aGDDF#K(Cs*QS(3)s*cGDDF#K(C5S1s*K)s*eGDDF#K*s*fGDDF%#-s*gGDDF(s*W#-s*hGDDF+s*X#-s*iGDDF.s*Y#-s*jGDDF8s*Z#-s*kGDDF>s*[#-s*lGDDFs##s*\#l#/#s*8s*2l#0s#'s*o#l#1s#,s*{#j#2C#j#3C#j#4C#j#5C#j#6C#j#7C#j#8C#j#:I#j#;I#j#<I#j#=I#j#>I#j#_I#$EL#s%JS#4s(vQ'N#'#s(x$#R#s%TS*4Os({NS$Q%C$##S5##S4##S,##S)##*#$S#S$$S'R$Rs%M&s%NO#$#k##&#k##(#k##*#k##4#k##9#k##;#k#2C#k#3C#k#4C#k#5C#k#6C#k#7C#k#8C#k#:I#k#;I#k#<I#k#=I#k#>I#k#_I#;S7$E#6s(^s)A'#s.m$&##&#1S7+#s)F%C#E/S7+#s)I%C#EMs.|s.|S7,s.~#'#s(j$#+'$s)O&-##%#$,(&s(ps.|?S9gJ30-&%$8s(r2SC#/SDOS*S,S5S2S3l#?s#A:#l#`s,$s,8#l#Cs$-s$'#l#Ds,5s,2#l#`s,?s,:#l#as$6s$2#l#bs$@s$:#l#cs$CC#l#[s$Ns$F#l#Gs$Ss$Q#l#Hs$Us$`#$S9s$o&s$pSP#$#m#&#.Cs'rs,$B#S0.Cs'fs$4.Cs,-#B#S0CS.#s,&CS.'#HCN0Cs,%Rs,$0C$L#0Cs'WRs+|0C$M#Ds+zGDDFS#*s+{GDDFs$0#(Cs&uS(s+c)s+}GDDF#K*s+~GDDFs+ks$2WSdCs+fs+n(Cs'(S-#)s,%GDDF#K*s,&GDDFs+f#*s,'GDDFs+o#*s,(GDDFs+z#*s,)GDDFs,(#*s,*GDDF*#VSXCs/MWT@C#s/U(Cs+fS(#)s,.GDDF#K(Cs+rS(s+h)s,0GDDF#K(Cs,&S(s'+)s,2GDDF#K(Cs'-S1))s,4GDDF#K*s,5GDDF%#-s,6GDDF(s,&#-s,7GDDF+s,'#-s,8GDDF0s,(#-s,9GDDF:s,)#-s,:GDDF=s,*#-s,;GDDFs'Ls,+#l#/#s+cs+]l#0Bs,>#l#1s#(s,J#j#2C#j#3C#j#4C#j#5C#j#6C#j#7C#j#:I#j#;I#j#<I#j#=I#j#>I#j#_I##s+RS$4s*CN'L#'#s*E$#Q$EN##S+4S#s*INS'N%C$##S4##S,##S)##S*##*#$S$s/z$S$S#4s*SS$'R#$E#&$s0##$#k##(#k##*#k##,#k##7#k##<#k##s+q#k#2C#k#3C#k#4C#k#5C#k#6C#k#7C#k#:I#k#;I#k#<I#k#=I#k#>I#k#_I#fJs$(s$%s#~s#ws#vs#us$-s*+SCs$'s#ts$$OS*S,S5SZS2l#?s#,$#l#`s-9s-M#l#Cs%Bs%<#l#Ds-Js-G#l#`s-Ts-O#l#as%Ks%G#l#bs%Us%O#l#cs%XC#l#[s%cs%[#l#Gs%hs%f#l#Hs%js%u#$Es&(&s&)s0D#$#m#&#WTAs0Ps&,#ZSrCs&-s&(s#us&,#VTBs0Rs&.,s0S#VTCs0Ts&0ZSrCs&0s&,&$#l#\s&:s&6#l#Ls&Bs&=#l#ds&Es&F#l#es+Rs+Q#l#fs.ks.K#@S/S$,s0\#$S8#&$S=#$#m#(#l#gs.ws.s#l#]s.}s.z#j#gs/A#ZTDs0cs/Ns/E#S,Jj#]s/P#V#MJj##s/T#j##s/a#Ts/bs/_s/Y#Jj#]s/e#j#hH#V#MJj##s/n#j#$H#YTEHs/~s/x#Jl#is02s0*#l#]s0<s07#j#is0f#j#js0i#j#ks0n#j#ls0q#j#*s0u#j#mC#j#nC#j#os0w##"). Qed.

Lemma all_pages_inside : forall S1 lo hi p,
  (hi <= 2 ^ 64)%Z ->
  (forall r, In r S1 -> (lo <= cl_lo r)%Z /\ (cl_hi r <= hi)%Z) ->
  In p (all_pages S1) -> (lo <= bv_unsigned p < hi)%Z.
Proof.
  induction S1 as [|r S1 IH]; intros lo hi p Hnw HS Hp; cbn [all_pages] in Hp; [destruct Hp|].
  apply in_app_iff in Hp. destruct Hp as [Hp | Hp].
  - destruct (HS r (or_introl eq_refl)) as [H1 H2]. eapply win_pages_inside; eassumption.
  - apply (IH lo hi p Hnw); [| exact Hp]. intros r' Hr'. apply HS. right. exact Hr'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lzok_vm_frame : forall L S Zr msF mo msF' mo',
  lzok L S Zr (mkCfg msF mo) ->
  m_vm mo' = m_vm mo -> m_halted mo' = None -> hid_same L S msF msF' ->
  lzok L S Zr (mkCfg msF' mo').
Proof.
  intros L S Zr msF mo msF' mo' [HL Hinv Hh HZ HSZ HZL HLM] Evm Hh' Hs. split; cbn in *.
  - exact HL.
  - eapply lazy_inv_vm_frame; [exact Evm | exact Hinv].
  - exact Hh'.
  - eapply hidden_zero_on_frame; eassumption.
  - exact HSZ.
  - exact HZL.
  - unfold m_vmmaps in *. rewrite Evm. exact HLM.
Qed.

(* [comment removed for export] *)
Lemma lzok_backing_used_le : forall L S Zr c,
  lzok L S Zr c ->
  (vm_backing_used (cfg_model c) <= eager_used (cfg_model c) + pages_total S * page_size)%Z.
Proof.
  intros L S Zr c [_ [Hl Hnd Hincl Hb] _ _ _ _ _]. rewrite vm_backing_used_split.
  rewrite <- all_pages_length.
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen. unfold page_size. nia.
Qed.

Lemma lzok_backing_within_limit : forall L S Zr c,
  lzok L S Zr c -> (vm_backing_used (cfg_model c) <= vm_limit (m_vmmaps (cfg_model c)))%Z.
Proof.
  intros L S Zr c Hok. pose proof (lzok_backing_used_le L S Zr c Hok).
  pose proof (li_budget _ _ _ (lzok_inv _ _ _ _ Hok)). lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lazy_not_in_segment : forall L a seg,
  lazy_ranges_okb segs L = true -> in_rangesb a L = true ->
  In seg segs -> ~ seg_covers seg (bv_unsigned a).
Proof.
  intros L a seg HL Ha Hin Hcov.
  pose proof (proj1 (lazy_ranges_ok_avoids segs L [] HL) a seg Hin Hcov) as H.
  unfold hiddenb in H. rewrite Ha in H. cbn in H. discriminate H.
Qed.

Lemma lazy_not_ro : forall L a,
  lazy_ranges_okb segs L = true -> in_rangesb a L = true -> Mem.ro_addr segs a = false.
Proof.
  intros L a HL Ha. unfold Mem.ro_addr.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. destruct (find_segment_spec segs (bv_unsigned a) 1 seg E) as (Hin & H1 & H2).
  apply (lazy_not_in_segment L a seg HL Ha Hin). unfold seg_covers. lia.
Qed.

(* [comment removed for export] *)
Lemma mem_inv_change_lazy : forall L (M M' : word -> option byte),
  lazy_ranges_okb segs L = true -> Mem.mem_inv segs M ->
  (forall a, M' a = M a \/ in_rangesb a L = true) ->
  Mem.mem_inv segs M'.
Proof.
  intros L M M' HL HM Hd a b Hb. destruct (Hd a) as [E | Ha].
  - rewrite E in Hb. exact (HM a b Hb).
  - exact (lazy_not_ro L a HL Ha).
Qed.

(* [comment removed for export] *)
Lemma mem_inv_restrict : forall L S M,
  Mem.mem_inv segs M -> Mem.mem_inv segs (restrict_mem L S M).
Proof.
  intros L S M HM a b Hb. unfold restrict_mem, restrict_mem_by in Hb.
  destruct (hiddenb L S a); [discriminate Hb|]. exact (HM a b Hb).
Qed.

End WithSegs.

Arguments lzok segs L S Zr c : clear implicits.
Arguments lzok_ranges {segs L S Zr c}.
Arguments lzok_inv {segs L S Zr c}.
Arguments lzok_halted {segs L S Zr c}.
Arguments lzok_zero {segs L S Zr c}.
Arguments lzok_SZr {segs L S Zr c}.
Arguments lzok_ZrL {segs L S Zr c}.
Arguments lzok_LM {segs L S Zr c}.
Arguments hidden_zero_on L S Zr msF : clear implicits.
Arguments hid_same L S msF msF' : clear implicits.
