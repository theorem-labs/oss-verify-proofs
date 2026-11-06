(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  Scfg PropExec CatSim ShapeAlg SReach LazyRestrict LazyRestrictRun LazyRestrictAlg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Exec MState Mem.
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
  intros W msF mo B Hok HW Hhid HB Hb. apply lzok_open_hidden_window; try assumption.
  rewrite pages_total_cons. pose proof (cl_bounds W). pose proof (pages_total_nonneg S).
  unfold page_size in *. nia.
Qed.

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

(* [comment removed for export] *)
Lemma win_pages_inside : forall r lo hi p,
  (lo <= cl_lo r)%Z -> (cl_hi r <= hi)%Z -> (hi <= 2 ^ 64)%Z ->
  In p (win_pages r) -> (lo <= bv_unsigned p < hi)%Z.
Proof.
  intros r lo hi p Hlo Hhi Hnw Hp. unfold win_pages in Hp. apply in_map_iff in Hp.
  destruct Hp as (i & <- & Hi). apply in_seq in Hi. unfold win_page.
  pose proof (cl_bounds r) as Hb. unfold win_npages in Hi.
  assert (Hi' : (Z.of_nat i < win_npagesZ r)%Z) by lia.
  assert (Hr : (cl_lo r + page_size * Z.of_nat i + page_size <= cl_hi r)%Z)
    by (unfold page_size in *; nia).
  pose proof (bv_unsigned_in_range 64 (fst r)) as H1.
  pose proof (bv_unsigned_in_range 64 (snd r)) as H2.
  change (bv_modulus 64) with (2^64)%Z in H1, H2.
  rewrite Z_to_bv_unsigned. rewrite bv_wrap_small.
  - unfold page_size in *. lia.
  - change (bv_modulus 64) with (2^64)%Z. unfold page_size in *. lia.
Qed.

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
