(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec SeqExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt FxChStart FxChWv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import FxRunPost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section M.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap segs.

#[using="Hwx"] Theorem den_isteps_m : forall E S M ms model T L msr' E',
  DEN segs LIMIT model0 mem0 E S M ms model ->
  isteps segs (restrict (Hof E M model) ms) msr' ->
  sden segs E' L msr' -> agree (s_next S) E E' -> (s_next S <= s_next L)%positive ->
  (forall x, outside E (s_rgs S) x -> ms_mem msr' x = ms_mem (restrict (Hof E M model) ms) x) ->
  shape (s_rgs L) = shape (s_rgs S) ->
  (forall E' ms' model', DEN segs LIMIT model0 mem0 E' L M ms' model' -> agree (s_next S) E E' ->
      (forall w, Hof E' M model' w = false -> ms_mem ms' w = ms_mem msr' w) ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros E S M ms model T L msr' E' Hd Hst Hd' Ha Hn Hfr Hsh Hk.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  assert (Hcov : lazy_cover H (m_vm_lazy model) (AM model0 E M)) by (apply lazy_cover_mkH_app; intros x Hx; exact Hx).
  apply (rzc_fx_isteps segs cfg H Hhoff Hwx (AM model0 E M) (restrict H ms) msr' ms model T eq_refl Hcov (A_wf_app _ _ Hawf (A_wf_blobA _)) Hminv Hh Hst).
  intros model' Hinv' Hsb' Hcl'.
  destruct (same_but_materialized_frame model model' Hsb') as (Hfd & Hvm & Hlz & Hio & Hfs & Hpr & Hli & Htm & _ & _ & _ & _ & Hhl & Htd & _).
  assert (HA : allowA E' M = allowA E M) by exact (allowA_agree (s_next S) E E' M Hwf Ha).
  assert (HH : Hof E' M model' = H) by (unfold Hof, H; rewrite Hlz, HA; reflexivity).
  apply (Hk E' _ model'); [|exact Ha| intros w Hw; cbn [unrestrict ms_mem]; unfold munrestrict; rewrite HH in Hw; rewrite Hw; reflexivity].
  assert (Hwf' : sm_wf (s_next L) M = true) by exact (sm_wf_mono _ _ M Hn Hwf).
  destruct (sm_wf_parts _ M Hwf) as (Hwg & Hwa & Hwt & Hwb & Hwsb & Hwsp).
  constructor.
  - rewrite HH. rewrite restrict_unrestrict_clean by exact Hcl'. exact Hd'.
  - exact Hwf'.
  - exact (bases_wf_shape _ _ _ _ Hn Hsh Hbw).
  - rewrite Hhl. exact Hh.
  - rewrite HA. exact Hawf.
  - exact Hanz.
  - rewrite (AM_agree (s_next S) model0 E E' M Hwf Ha). exact Hinv'.
  - rewrite HH. exact Hhoff.
  - rewrite Hvm. exact Hres.
  - rewrite Hvm. exact Hlim.
  - rewrite Hvm, Hsp. symmetry. exact (lden_agree_wf _ E E' _ Hwsp Ha).
  - rewrite Hvm. exact Hspok.
  - rewrite Hvm, Hbrk. symmetry. exact (lden_agree_wf _ E E' _ Hwb Ha).
  - rewrite Hvm, Hsbrk. symmetry. exact (lden_agree_wf _ E E' _ Hwsb Ha).
  - rewrite Htd, Htid. destruct (sm_tid M) as [l|]; [cbn; f_equal; symmetry; exact (lden_agree_wf _ E E' l Hwt Ha) | reflexivity].
  - rewrite Hvm, Hmaps. symmetry. exact (lden_maps_agree _ E E' _ M Hwf Ha).
  - apply (Forall_agree_maps (s_next S) E E' M gshape_ok Hwf Ha); [|exact Hgsh].
    intros g Hg Hgs. unfold gshape_ok, gsz, uE. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
  - apply (Forall_agree_maps (s_next S) E E' M (fun E g => uE E (fst (fst g)) + gsz E g <= alloc_top (m_vmmaps model')) Hwf Ha).
    + intros g Hg Hgs. unfold gsz, uE. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
    + rewrite Hvm. exact Hgtop.
  - rewrite Hvm, Hlz. exact Hivwf.
  - rewrite Hvm. exact Hpd.
  - rewrite Hvm. exact Hmres.
  - apply (Forall_agree_maps (s_next S) E E' M (fun E g => kind_ok E model' g) Hwf Ha).
    + intros g Hg Hgs. unfold kind_ok, gden. rewrite (lden_agree_wf _ E E' _ Hg Ha), (lden_agree_wf _ E E' _ Hgs Ha). tauto.
    + unfold kind_ok. rewrite Hvm, Hlz. exact Hkind.
  - rewrite Hlz, Hvm. exact Hlzm.
  - exact Hzrsh.
  - rewrite Hvm. exact Hzrm.
  - intros w Hw Hout Hno Hnb. cbn [unrestrict ms_mem].
    assert (Hout0 : outside E (s_rgs S) (Z_to_bv 64 w)) by exact (outside_agree_shape _ E E' _ _ _ Hbw Ha Hsh Hout).
    rewrite (munrestrict_outside H (ms_mem ms) (restrict H ms) msr' _ eq_refl (Hfr _ Hout0)).
    exact (Hzr w Hw Hout0 (own_pt_keep _ E E' M M w Hwf Ha eq_refl Hno) Hnb).
  - exact (rl_ok_agree_shape _ E E' model model' (s_rgs S) (s_rgs L) Hbw Ha Hsh Hvm Hrl).
  - destruct Hvmo as (H1 & H2 & H3 & H4 & H5). rewrite Hfd, Hio, Hfs, Hli, Htm. repeat split; assumption.
  - rewrite Hpr, Htd. exact Hproc.
  - intros q Hq w Hw. pose proof (sm_wf_frz _ M Hwf) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw q Hq) as [Hf1 Hf2].
    assert (Hw0 : uE E (fst q) <= w < uE E (fst q) + uE E (snd q)) by (unfold uE in *; rewrite <- (lden_agree_wf _ E E' _ Hf1 Ha), <- (lden_agree_wf _ E E' _ Hf2 Ha); exact Hw).
    destruct (Hfrz q Hq w Hw0) as (Htp & Hout & Hm). split; [unfold alloc_top in *; rewrite Hvm; exact Htp|]. split.
    + apply (outside_shape E' (s_rgs S) (s_rgs L) _ Hsh). apply (proj1 (outside_agree (s_next S) E E' (s_rgs S) _ Hbw Ha)). exact Hout.
    + cbn [unrestrict ms_mem]. rewrite (munrestrict_outside H (ms_mem ms) (restrict H ms) msr' _ eq_refl (Hfr _ Hout)). exact Hm.
  - cbn [unrestrict ms_rom]. rewrite (fx_rom segs _ _ Hst). cbn [restrict ms_rom]. exact Hrom.
  - intros q Hq w Hw. pose proof (sm_wf_own _ M Hwf) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw q Hq) as [Hf1 Hf2].
    assert (Hw0 : uE E (fst q) <= w < uE E (fst q) + uE E (snd q)) by (unfold uE in *; rewrite <- (lden_agree_wf _ E E' _ Hf1 Ha), <- (lden_agree_wf _ E E' _ Hf2 Ha); exact Hw).
    destruct (Hown q Hq w Hw0) as [Hv Hm]. split; [rewrite HH; exact Hv|]. intros Hout'.
    assert (Hout : outside E (s_rgs S) (Z_to_bv 64 w)).
    { apply (proj2 (outside_agree (s_next S) E E' (s_rgs S) _ Hbw Ha)). apply (outside_shape E' (s_rgs L) (s_rgs S) _ (eq_sym Hsh)). exact Hout'. }
    cbn [unrestrict ms_mem]. rewrite (munrestrict_outside H (ms_mem ms) (restrict H ms) msr' _ eq_refl (Hfr _ Hout)). exact (Hm Hout).
  - apply (blob_ok_agree (s_next S) E E' M model model' _ Hwf Ha); [rewrite Hvm; reflexivity | exact Hblob].
Qed.


#[using="Hwx"] Theorem den_run_post_fw_m : forall E S M ms model T (regs' : bvmap 5 word) (pc' : Z) (sets : list (reg * lin)) (havs : list reg)
    (j0 : nat) (R0 : region) (lo hi : Z) (mem' : word -> option byte),
  DEN segs LIMIT model0 mem0 E S M ms model -> s_resv S = RNone ->
  nth_error (s_rgs S) j0 = Some R0 -> rg_kind R0 = RW -> 0 <= lo -> lo <= hi -> hi <= rsz E R0 ->
  isteps segs (restrict (Hof E M model) ms)
    (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (Z_to_bv 64 pc') mem' (ms_rom ms)) ->
  (forall w : word, ~ (uE E (rg_base R0) + lo <= bv_unsigned w < uE E (rg_base R0) + hi) -> mem' w = mrestrict (Hof E M model) (ms_mem ms) w) ->
  (forall i, lo <= i < hi -> rd1 segs mem' (Z_to_bv 64 (uE E (rg_base R0) + i)) <> None /\ wview segs mem' (Z_to_bv 64 (uE E (rg_base R0) + i)) <> None) ->
  Forall (fun p => fst p <> 0%bv /\ lwf (s_next S) (snd p) = true /\ getr regs' (fst p) = lden E (snd p)) sets ->
  Forall (fun r => r <> 0%bv) havs ->
  (forall r, existsb (fun p => bv_eqb (fst p) r) sets = false -> existsb (fun h => bv_eqb h r) havs = false ->
     getr regs' r = getr (ms_regs ms) r) ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN segs LIMIT model0 mem0 E' (run_post_fw S pc' sets havs j0 lo hi) M ms' model' ->
     (forall w, Hof E' M model' w = false -> ms_mem ms' w = mem' w) ->
     realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros E S M ms model T regs' pc' sets havs j0 R0 lo hi mem' Hd Hrv Hj0 Hk0 Hlo Hlh Hhi Hst Hfr Hwr Hsets Hnz Ho Hk.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  set (n := s_next S) in *.
  set (E1 := hav_val E regs' havs n).
  assert (Ha1 : agree n E E1) by apply hav_val_agree.
  set (S1 := bump S (pos_add n (length havs))).
  assert (Hnx : (s_next S <= s_next S1)%positive) by (unfold S1, bump; cbn [s_next]; apply pos_add_le).
  assert (HdS1 : DEN segs LIMIT model0 mem0 E1 S1 M ms model)
    by (apply den_bump; [exact (den_agree segs LIMIT model0 mem0 E E1 S M ms model Hd Ha1) | apply pos_add_le]).
  assert (HH1 : Hof E1 M model = H) by (unfold Hof, H; rewrite (allowA_agree (s_next S) E E1 M Hwf Ha1); reflexivity).
  set (R0' := RG (rg_base R0) (rg_size R0) (rg_kind R0) (havoc_range (rg_cont R0) lo hi)).
  assert (Hpw : run_post_fw S pc' sets havs j0 lo hi = SST pc' (hav_regs (set_regs (s_regs S) sets) havs n) (upd_nth (s_rgs S) j0 R0')
                   (s_facts S) (pos_add n (length havs)) (s_resv S)) by (unfold run_post_fw; rewrite Hj0; reflexivity).
  set (msr' := @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (Z_to_bv 64 pc') mem' (ms_rom ms)).
  assert (Hpost : sden segs E1 (run_post_fw S pc' sets havs j0 lo hi) msr').
  { rewrite Hpw. intros E' Ha'.
    assert (HaE : agree n E E') by exact (agree_trans _ E E1 E' Ha1 (agree_mono _ _ E1 E' (pos_add_le (length havs) n) Ha')).
    destruct (Hsd E' HaE) as (Hpc' & Hsvc' & Hrsv' & HR' & HG' & HD' & HF' & Hfrm').
    cbn [restrict ms_regs ms_mem ms_fcsr ms_resv] in HR', HG', Hfrm', Hrsv'.
    assert (HbE : lden E' (rg_base R0) = lden E (rg_base R0)).
    { unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 (nth_error_In _ _ Hj0))) as [B1 _].
      exact (lden_agree_wf n E E' _ B1 HaE). }
    assert (HsE : rsz E' R0 = rsz E R0).
    { unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 (nth_error_In _ _ Hj0))) as [_ B2].
      unfold rsz. rewrite (lden_agree_wf n E E' _ B2 HaE). reflexivity. }
    unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv msr' mkst ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr fp_csr].
    split; [reflexivity|]. split; [reflexivity|]. split; [rewrite Hrv; reflexivity|]. split.
    - apply (regs_ok_ext E' _ (upd_havs (upd_sets (ms_regs ms) sets regs') havs regs')).
      + apply regs_ok_hav'; [| exact Hnz |].
        * apply regs_ok_set'; [exact HR'|]. rewrite Forall_forall in Hsets |- *. intros p Hp.
          destruct (Hsets p Hp) as (Hp0 & Hpw' & Hpv). split; [exact Hp0|]. rewrite Hpv. symmetry. exact (lden_agree_wf n E E' _ Hpw' HaE).
        * intros i Hi. rewrite <- (hav_val_at havs E regs' n i Hi). symmetry. apply Ha'. cbn [s_next]. apply pos_add_lt. exact Hi.
      + intros r. rewrite upd_havs_get, upd_sets_get.
        destruct (existsb (fun h => bv_eqb h r) havs) eqn:Eh; [reflexivity|].
        destruct (existsb (fun p => bv_eqb (fst p) r) sets) eqn:Es; [reflexivity|].
        symmetry. exact (Ho r Es Eh).
    - split; [|split; [|split; [exact HF' | exact Hfrm']]].
      + (* [comment removed for export] *)
        apply Forall_nth'. intros j R HRj. rewrite Forall_nth' in HG'.
        destruct (Nat.eq_dec j j0) as [->|Hne].
        * rewrite (nth_upd_same (s_rgs S) j0 R0' R0 Hj0) in HRj. injection HRj as <-.
          destruct (HG' j0 R0 Hj0) as (Hsz & Hflat & Hall & Hcont).
          assert (Hrsz : rsz E' R0' = rsz E R0) by (unfold R0', rsz; cbn [rg_size]; unfold rsz in HsE; exact HsE).
          assert (Hbase : lden E' (rg_base R0') = lden E (rg_base R0)) by (unfold R0'; cbn [rg_base]; exact HbE).
          assert (HkR' : rg_kind R0' = RW) by (unfold R0'; cbn [rg_kind]; exact Hk0).
          assert (Hcont' : rg_cont R0' = havoc_range (rg_cont R0) lo hi) by reflexivity.
          unfold rg_ok. rewrite Hrsz, Hbase, HkR', Hcont'. rewrite Hk0 in Hall. rewrite HbE, HsE in *. fold (uE E (rg_base R0)) in *.
          split; [exact Hsz|]. split; [exact Hflat|]. split.
          -- intros i Hi. specialize (Hall i Hi).
             destruct (Z_lt_le_dec i lo) as [Hl|Hl]; [|destruct (Z_lt_le_dec i hi) as [Hh2|Hh2]].
             ++ unfold rd1, wview in *. rewrite Hfr; [exact Hall|]. pose proof (uE_range E (rg_base R0)). rewrite u_small64 by (unfold two64 in *; lia). lia.
             ++ exact (Hwr i ltac:(lia)).
             ++ unfold rd1, wview in *. rewrite Hfr; [exact Hall|]. pose proof (uE_range E (rg_base R0)). rewrite u_small64 by (unfold two64 in *; lia). lia.
          -- intros p v Hp. unfold havoc_range in Hp. rewrite tget_tfilter in Hp.
             destruct (tget p (rg_cont R0)) as [x|] eqn:Hx; [|discriminate].
             destruct (negb (Z.leb lo (Zpos p - 1) && Z.ltb (Zpos p - 1) hi)) eqn:Hn; [|discriminate]. injection Hp as <-.
             destruct (Hcont p x Hx) as [Hp1 Hp2]. rewrite ?HbE, ?HsE in Hp1, Hp2. fold (uE E (rg_base R0)) in Hp2. split; [exact Hp1|].
             apply negb_true_iff in Hn. apply andb_false_iff in Hn.
             unfold rd1 in *. rewrite Hfr; [exact Hp2|]. pose proof (Pos2Z.is_pos p). pose proof (uE_range E (rg_base R0)).
             rewrite u_small64 by (unfold two64 in *; lia).
             destruct Hn as [Hn|Hn]; [apply Z.leb_gt in Hn | apply Z.ltb_ge in Hn]; lia.
        * rewrite (nth_upd_other (s_rgs S) j0 j R0' ltac:(lia)) in HRj.
          apply (rg_ok_frame segs E' (mrestrict H (ms_mem ms)) mem' R (HG' j R HRj)).
          intros x Hx. apply Hfr.
          pose proof (rgs_disj_nth E' (s_rgs S) j j0 R R0 HD' Hne HRj Hj0) as Hdis. unfold rg_disj in Hdis.
          rewrite HbE, HsE in Hdis. fold (uE E (rg_base R0)) in Hdis. unfold uE in *. lia.
      + apply (rgs_disj_upd E' (s_rgs S) j0 R0' R0 Hj0 eq_refl eq_refl HD'). }
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (Z_to_bv 64 (s_pc S)) (mrestrict H (ms_mem ms)) (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. subst pcv. reflexivity. }
  apply (den_isteps_m E1 S1 M ms model T (run_post_fw S pc' sets havs j0 lo hi) msr' E1 HdS1).
  - rewrite HH1. exact Hst.
  - exact Hpost.
  - apply agree_refl.
  - rewrite Hpw. unfold S1, bump. cbn [s_next]. apply Pos.le_refl.
  - intros y Hy. rewrite HH1. unfold msr', mkst. cbn [ms_mem]. apply Hfr.
    unfold outside in Hy. rewrite Forall_forall in Hy. specialize (Hy R0 (nth_error_In _ _ Hj0)).
    cbn [S1 bump s_rgs] in Hy.
    unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 (nth_error_In _ _ Hj0))) as [B1 B2].
    assert (HbE1 : lden E1 (rg_base R0) = lden E (rg_base R0)) by exact (lden_agree_wf n E E1 _ B1 Ha1).
    assert (HsE1 : rsz E1 R0 = rsz E R0) by (unfold rsz; rewrite (lden_agree_wf n E E1 _ B2 Ha1); reflexivity).
    rewrite HbE1, HsE1 in Hy. unfold uE. lia.
  - rewrite Hpw. cbn [s_rgs S1 bump]. exact (shape_upd (s_rgs S) j0 R0' R0 Hj0 eq_refl eq_refl).
  - intros E2 ms2 model2 HD2 Ha2 Hm2. apply (Hk E2 ms2 model2); [| exact HD2 | exact Hm2].
    exact (agree_trans _ E E1 E2 Ha1 (agree_mono _ _ E1 E2 Hnx Ha2)).
Qed.
(* [comment removed for export] *)
Definition rk_wz (k : rkind) : bool := match k with RW | RZ => true | _ => false end.
Definition run_post_fw2 (S : sst) (pc' : Z) (sets : list (reg * lin)) (havs : list reg) (j0 : nat) (lo hi : Z) : sst :=
  match nth_error (s_rgs S) j0 with
  | Some R0 => SST pc' (hav_regs (set_regs (s_regs S) sets) havs (s_next S))
                   (upd_nth (s_rgs S) j0 (RG (rg_base R0) (rg_size R0) RW (havoc_range (rg_cont R0) lo hi)))
                   (s_facts S) (pos_add (s_next S) (length havs)) (s_resv S)
  | None => run_post S pc' sets havs
  end.

#[using="Hwx"] Theorem den_run_post_fw2_m : forall E S M ms model T (regs' : bvmap 5 word) (pc' : Z) (sets : list (reg * lin)) (havs : list reg)
    (j0 : nat) (R0 : region) (lo hi : Z) (mem' : word -> option byte),
  DEN segs LIMIT model0 mem0 E S M ms model -> s_resv S = RNone ->
  nth_error (s_rgs S) j0 = Some R0 -> rk_wz (rg_kind R0) = true -> 0 <= lo -> lo <= hi -> hi <= rsz E R0 ->
  isteps segs (restrict (Hof E M model) ms)
    (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (Z_to_bv 64 pc') mem' (ms_rom ms)) ->
  (forall w : word, ~ (uE E (rg_base R0) + lo <= bv_unsigned w < uE E (rg_base R0) + hi) -> mem' w = mrestrict (Hof E M model) (ms_mem ms) w) ->
  (forall i, lo <= i < hi -> rd1 segs mem' (Z_to_bv 64 (uE E (rg_base R0) + i)) <> None /\ wview segs mem' (Z_to_bv 64 (uE E (rg_base R0) + i)) <> None) ->
  Forall (fun p => fst p <> 0%bv /\ lwf (s_next S) (snd p) = true /\ getr regs' (fst p) = lden E (snd p)) sets ->
  Forall (fun r => r <> 0%bv) havs ->
  (forall r, existsb (fun p => bv_eqb (fst p) r) sets = false -> existsb (fun h => bv_eqb h r) havs = false ->
     getr regs' r = getr (ms_regs ms) r) ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN segs LIMIT model0 mem0 E' (run_post_fw2 S pc' sets havs j0 lo hi) M ms' model' ->
     (forall w, Hof E' M model' w = false -> ms_mem ms' w = mem' w) ->
     realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros E S M ms model T regs' pc' sets havs j0 R0 lo hi mem' Hd Hrv Hj0 Hk0 Hlo Hlh Hhi Hst Hfr Hwr Hsets Hnz Ho Hk.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  set (n := s_next S) in *.
  set (E1 := hav_val E regs' havs n).
  assert (Ha1 : agree n E E1) by apply hav_val_agree.
  set (S1 := bump S (pos_add n (length havs))).
  assert (Hnx : (s_next S <= s_next S1)%positive) by (unfold S1, bump; cbn [s_next]; apply pos_add_le).
  assert (HdS1 : DEN segs LIMIT model0 mem0 E1 S1 M ms model)
    by (apply den_bump; [exact (den_agree segs LIMIT model0 mem0 E E1 S M ms model Hd Ha1) | apply pos_add_le]).
  assert (HH1 : Hof E1 M model = H) by (unfold Hof, H; rewrite (allowA_agree (s_next S) E E1 M Hwf Ha1); reflexivity).
  set (R0' := RG (rg_base R0) (rg_size R0) RW (havoc_range (rg_cont R0) lo hi)).
  assert (Hpw : run_post_fw2 S pc' sets havs j0 lo hi = SST pc' (hav_regs (set_regs (s_regs S) sets) havs n) (upd_nth (s_rgs S) j0 R0')
                   (s_facts S) (pos_add n (length havs)) (s_resv S)) by (unfold run_post_fw2; rewrite Hj0; reflexivity).
  set (msr' := @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (Z_to_bv 64 pc') mem' (ms_rom ms)).
  assert (Hpost : sden segs E1 (run_post_fw2 S pc' sets havs j0 lo hi) msr').
  { rewrite Hpw. intros E' Ha'.
    assert (HaE : agree n E E') by exact (agree_trans _ E E1 E' Ha1 (agree_mono _ _ E1 E' (pos_add_le (length havs) n) Ha')).
    destruct (Hsd E' HaE) as (Hpc' & Hsvc' & Hrsv' & HR' & HG' & HD' & HF' & Hfrm').
    cbn [restrict ms_regs ms_mem ms_fcsr ms_resv] in HR', HG', Hfrm', Hrsv'.
    assert (HbE : lden E' (rg_base R0) = lden E (rg_base R0)).
    { unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 (nth_error_In _ _ Hj0))) as [B1 _].
      exact (lden_agree_wf n E E' _ B1 HaE). }
    assert (HsE : rsz E' R0 = rsz E R0).
    { unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 (nth_error_In _ _ Hj0))) as [_ B2].
      unfold rsz. rewrite (lden_agree_wf n E E' _ B2 HaE). reflexivity. }
    unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv msr' mkst ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr fp_csr].
    split; [reflexivity|]. split; [reflexivity|]. split; [rewrite Hrv; reflexivity|]. split.
    - apply (regs_ok_ext E' _ (upd_havs (upd_sets (ms_regs ms) sets regs') havs regs')).
      + apply regs_ok_hav'; [| exact Hnz |].
        * apply regs_ok_set'; [exact HR'|]. rewrite Forall_forall in Hsets |- *. intros p Hp.
          destruct (Hsets p Hp) as (Hp0 & Hpw' & Hpv). split; [exact Hp0|]. rewrite Hpv. symmetry. exact (lden_agree_wf n E E' _ Hpw' HaE).
        * intros i Hi. rewrite <- (hav_val_at havs E regs' n i Hi). symmetry. apply Ha'. cbn [s_next]. apply pos_add_lt. exact Hi.
      + intros r. rewrite upd_havs_get, upd_sets_get.
        destruct (existsb (fun h => bv_eqb h r) havs) eqn:Eh; [reflexivity|].
        destruct (existsb (fun p => bv_eqb (fst p) r) sets) eqn:Es; [reflexivity|].
        symmetry. exact (Ho r Es Eh).
    - split; [|split; [|split; [exact HF' | exact Hfrm']]].
      + (* [comment removed for export] *)
        apply Forall_nth'. intros j R HRj. rewrite Forall_nth' in HG'.
        destruct (Nat.eq_dec j j0) as [->|Hne].
        * rewrite (nth_upd_same (s_rgs S) j0 R0' R0 Hj0) in HRj. injection HRj as <-.
          destruct (HG' j0 R0 Hj0) as (Hsz & Hflat & Hall & Hcont).
          assert (Hrsz : rsz E' R0' = rsz E R0) by (unfold R0', rsz; cbn [rg_size]; unfold rsz in HsE; exact HsE).
          assert (Hbase : lden E' (rg_base R0') = lden E (rg_base R0)) by (unfold R0'; cbn [rg_base]; exact HbE).
          assert (HkR' : rg_kind R0' = RW) by reflexivity.
          assert (Hcont' : rg_cont R0' = havoc_range (rg_cont R0) lo hi) by reflexivity.
          assert (Hall2 : forall i, 0 <= i < rsz E' R0 -> rd1 segs (mrestrict H (ms_mem ms)) (Z_to_bv 64 (bv_unsigned (lden E' (rg_base R0)) + i)) <> None /\
                    wview segs (mrestrict H (ms_mem ms)) (Z_to_bv 64 (bv_unsigned (lden E' (rg_base R0)) + i)) <> None).
          { intros i Hi. specialize (Hall i Hi). unfold rk_wz in Hk0. destruct (rg_kind R0); try discriminate; [exact Hall | exact (proj1 Hall)]. }
          clear Hall. rename Hall2 into Hall.
          unfold rg_ok. rewrite Hrsz, Hbase, HkR', Hcont'. rewrite HbE, HsE in *. fold (uE E (rg_base R0)) in *.
          split; [exact Hsz|]. split; [exact Hflat|]. split.
          -- intros i Hi. specialize (Hall i Hi).
             destruct (Z_lt_le_dec i lo) as [Hl|Hl]; [|destruct (Z_lt_le_dec i hi) as [Hh2|Hh2]].
             ++ unfold rd1, wview in *. rewrite Hfr; [exact Hall|]. pose proof (uE_range E (rg_base R0)). rewrite u_small64 by (unfold two64 in *; lia). lia.
             ++ exact (Hwr i ltac:(lia)).
             ++ unfold rd1, wview in *. rewrite Hfr; [exact Hall|]. pose proof (uE_range E (rg_base R0)). rewrite u_small64 by (unfold two64 in *; lia). lia.
          -- intros p v Hp. unfold havoc_range in Hp. rewrite tget_tfilter in Hp.
             destruct (tget p (rg_cont R0)) as [x|] eqn:Hx; [|discriminate].
             destruct (negb (Z.leb lo (Zpos p - 1) && Z.ltb (Zpos p - 1) hi)) eqn:Hn; [|discriminate]. injection Hp as <-.
             destruct (Hcont p x Hx) as [Hp1 Hp2]. rewrite ?HbE, ?HsE in Hp1, Hp2. fold (uE E (rg_base R0)) in Hp2. split; [exact Hp1|].
             apply negb_true_iff in Hn. apply andb_false_iff in Hn.
             unfold rd1 in *. rewrite Hfr; [exact Hp2|]. pose proof (Pos2Z.is_pos p). pose proof (uE_range E (rg_base R0)).
             rewrite u_small64 by (unfold two64 in *; lia).
             destruct Hn as [Hn|Hn]; [apply Z.leb_gt in Hn | apply Z.ltb_ge in Hn]; lia.
        * rewrite (nth_upd_other (s_rgs S) j0 j R0' ltac:(lia)) in HRj.
          apply (rg_ok_frame segs E' (mrestrict H (ms_mem ms)) mem' R (HG' j R HRj)).
          intros x Hx. apply Hfr.
          pose proof (rgs_disj_nth E' (s_rgs S) j j0 R R0 HD' Hne HRj Hj0) as Hdis. unfold rg_disj in Hdis.
          rewrite HbE, HsE in Hdis. fold (uE E (rg_base R0)) in Hdis. unfold uE in *. lia.
      + apply (rgs_disj_upd E' (s_rgs S) j0 R0' R0 Hj0 eq_refl eq_refl HD'). }
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (Z_to_bv 64 (s_pc S)) (mrestrict H (ms_mem ms)) (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. subst pcv. reflexivity. }
  apply (den_isteps_m E1 S1 M ms model T (run_post_fw2 S pc' sets havs j0 lo hi) msr' E1 HdS1).
  - rewrite HH1. exact Hst.
  - exact Hpost.
  - apply agree_refl.
  - rewrite Hpw. unfold S1, bump. cbn [s_next]. apply Pos.le_refl.
  - intros y Hy. rewrite HH1. unfold msr', mkst. cbn [ms_mem]. apply Hfr.
    unfold outside in Hy. rewrite Forall_forall in Hy. specialize (Hy R0 (nth_error_In _ _ Hj0)).
    cbn [S1 bump s_rgs] in Hy.
    unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. destruct (andb_prop _ _ (Hbw R0 (nth_error_In _ _ Hj0))) as [B1 B2].
    assert (HbE1 : lden E1 (rg_base R0) = lden E (rg_base R0)) by exact (lden_agree_wf n E E1 _ B1 Ha1).
    assert (HsE1 : rsz E1 R0 = rsz E R0) by (unfold rsz; rewrite (lden_agree_wf n E E1 _ B2 Ha1); reflexivity).
    rewrite HbE1, HsE1 in Hy. unfold uE. lia.
  - rewrite Hpw. cbn [s_rgs S1 bump]. exact (shape_upd (s_rgs S) j0 R0' R0 Hj0 eq_refl eq_refl).
  - intros E2 ms2 model2 HD2 Ha2 Hm2. apply (Hk E2 ms2 model2); [| exact HD2 | exact Hm2].
    exact (agree_trans _ E E1 E2 Ha1 (agree_mono _ _ E1 E2 Hnx Ha2)).
Qed.
End M.
