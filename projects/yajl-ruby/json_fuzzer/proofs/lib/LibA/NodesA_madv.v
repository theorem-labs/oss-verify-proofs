(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap Madvise.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec ITree Nodes NodesCfg SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import ExecA LazyModel ITreeA NodesA ImplRzA NodesA_mm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition at_madvise (addr len : Z) (ms : machine_state) : Prop :=
  ms_svc_pending ms = Some (Z_to_bv 64 233) /\
  areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\ areg ms 12 = Z_to_bv 64 4.

(* [comment removed for export] *)
Definition madvise_CHK (addr len : Z) (mo : Model) (eff : SyscallEffect) : check_result :=
  check_madvise (Z_to_bv 64 addr) (Z_to_bv 64 len) (int32 (Z_to_bv 64 4)) eff mo.

(* [comment removed for export] *)
Definition madv_eff (addr n : Z) : SyscallEffect :=
  mkEffectU (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 n)] [] [] [].

(* [comment removed for export] *)
Definition m_madv (mo : Model) (addr n : Z) : Model :=
  madvise_dontneed_next mo (Z_to_bv 64 addr) (Z_to_bv 64 n).

(* [comment removed for export] *)
Definition madvise_gate (mo : Model) (addr n : Z) : Prop :=
  madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 n) = true.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Lemma m_madv_vmmaps : forall mo a n, m_vmmaps (m_madv mo a n) = m_vmmaps mo.
Proof. intros. unfold m_madv, madvise_dontneed_next. apply m_vmmaps_with_vm_backing. Qed.
Lemma m_madv_lazy : forall mo a n, m_vm_lazy (m_madv mo a n) = m_vm_lazy mo.
Proof. intros mo a n. destruct mo as [fd [maps lz mat] io fs proc lim tm]. reflexivity. Qed.
Lemma m_madv_mat : forall mo a n,
  m_vm_materialized (m_madv mo a n)
  = List.filter (page_outside_range (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 a) + bv_unsigned (Z_to_bv 64 n))) (m_vm_materialized mo).
Proof. intros mo a n. destruct mo as [fd [maps lz mat] io fs proc lim tm]. reflexivity. Qed.
Lemma m_madv_mat_Z : forall mo a n, 0 <= a < 2^64 -> 0 <= n < 2^64 ->
  m_vm_materialized (m_madv mo a n) = List.filter (page_outside_range a (a + n)) (m_vm_materialized mo).
Proof. intros mo a n Ha Hn. rewrite m_madv_mat, !unsigned_lit by lia. reflexivity. Qed.
Lemma m_madv_vm_only : forall mo a n, vm_only mo (m_madv mo a n).
Proof. intros. unfold m_madv, madvise_dontneed_next. apply vm_only_with_vm_backing. Qed.
Lemma m_madv_frame : forall mo a n,
  m_fds (m_madv mo a n) = m_fds mo /\ m_fs (m_madv mo a n) = m_fs mo /\ m_halted (m_madv mo a n) = m_halted mo /\
  m_tid (m_madv mo a n) = m_tid mo /\ m_stdin (m_madv mo a n) = m_stdin mo.
Proof. intros mo a n. destruct mo as [fd [maps lz mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
Lemma m_madv_eager : forall mo a n, eager_used (m_madv mo a n) = eager_used mo.
Proof. intros. unfold eager_used. rewrite m_madv_vmmaps, m_madv_lazy. reflexivity. Qed.

(* [comment removed for export] *)
Lemma m_madv_in : forall mo a n p, 0 <= a < 2^64 -> 0 <= n < 2^64 ->
  (In p (m_vm_materialized (m_madv mo a n)) <-> In p (m_vm_materialized mo) /\ ~ (a <= bv_unsigned p < a + n)).
Proof.
  intros mo a n p Ha Hn. rewrite m_madv_mat_Z by assumption. rewrite filter_In. unfold page_outside_range.
  rewrite Bool.negb_true_iff, Bool.andb_false_iff, Z.leb_gt, Z.ltb_ge. intuition lia.
Qed.
Lemma m_madv_not_in : forall mo a n p, 0 <= a < 2^64 -> 0 <= n < 2^64 ->
  In p (m_vm_materialized (m_madv mo a n)) -> ~ (a <= bv_unsigned p < a + n).
Proof. intros mo a n p Ha Hn H. apply (m_madv_in mo a n p Ha Hn) in H. tauto. Qed.

(* [comment removed for export] *)
Lemma LI_madvise : forall (S : word -> Prop) N EB mo a n, LI S N EB mo -> LI S N EB (m_madv mo a n).
Proof.
  intros S N EB mo a n L. eapply LI_transfer; [exact L| | | |].
  - intros p Hp. rewrite m_madv_mat in Hp. apply filter_In in Hp. tauto.
  - rewrite m_madv_mat. apply NoDup_filter. exact (li_nodup _ _ _ _ L).
  - rewrite m_madv_eager. exact (li_eager _ _ _ _ L).
  - rewrite m_madv_vmmaps. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma madvise_gate_magree : forall mo mo1 a n, magree mo mo1 -> madvise_gate mo a n -> madvise_gate mo1 a n.
Proof. intros mo mo1 a n Hag H. unfold madvise_gate in *. rewrite (magree_vmmaps _ _ Hag). exact H. Qed.
Lemma madvise_gate_intro : forall mo a n,
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  region_free (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  madvise_gate mo a n.
Proof. intros mo a n H1 H2 H3. unfold madvise_gate, madvise_dontneed_ok. rewrite H1, H2, H3. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition madvise_match (addr n : Z) (mo : Model) (eff : SyscallEffect) : check_result :=
  match eff with
  | mkEffectU r [] zs [] [] [] =>
      if w_is0 r && listNN_eqb zs [(Z_to_bv 64 addr, Z_to_bv 64 n)] then CheckOk (m_madv mo addr n) [] else CheckReject
  | _ => CheckReject
  end.

Lemma chk_madvise_red : forall addr len mo eff,
  0 <= addr -> addr mod 4096 = 0 -> 0 < len < 2^64 ->
  addr + page_round_up_Z len < 2^64 ->
  madvise_gate mo addr (page_round_up_Z len) ->
  madvise_CHK addr len mo eff = madvise_match addr (page_round_up_Z len) mo eff.
Proof.
  intros addr len mo eff HA AA HL HE G.
  assert (HnZ : 0 <= page_round_up_Z len) by (apply page_round_up_Z_nonneg; lia).
  unfold madvise_CHK, check_madvise.
  rewrite !unsigned_lit by lia.
  replace (addr mod page_size =? 0) with true by (symmetry; apply Z.eqb_eq; exact AA). cbn [negb].
  change (madvise_dontneed_b (int32 (Z_to_bv 64 4))) with true. cbn [negb].
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (two_pow_64 <=? addr + page_round_up_Z len) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  cbv zeta. unfold madvise_gate in G. rewrite G. reflexivity.
Qed.

Lemma madvise_match_nu : forall addr n mo eff, madvise_match addr n mo eff <> CheckUnmodeled.
Proof.
  intros addr n mo [r ws zs us cs ci]. unfold madvise_match.
  destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (w_is0 r && listNN_eqb zs [(Z_to_bv 64 addr, Z_to_bv 64 n)]); discriminate.
Qed.

Lemma madvise_match_grant : forall addr n mo, madvise_match addr n mo (madv_eff addr n) = CheckOk (m_madv mo addr n) [].
Proof.
  intros addr n mo. unfold madvise_match, madv_eff. unfold w_is0. rewrite bv_eqb_refl.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma madvise_match_inv : forall addr n mo eff mo' evs,
  madvise_match addr n mo eff = CheckOk mo' evs -> eff = madv_eff addr n /\ mo' = m_madv mo addr n /\ evs = [].
Proof.
  intros addr n mo [r ws zs us cs ci] mo' evs H. unfold madvise_match in H.
  destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (w_is0 r && listNN_eqb zs [(Z_to_bv 64 addr, Z_to_bv 64 n)]) eqn:C; [|discriminate].
  apply andb_true_iff in C as [Hr Hz]. unfold w_is0 in Hr. apply bv_eqb_eq in Hr. apply listNN_eqb_eq in Hz. subst r zs.
  injection H as <- <-. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma check_madvise_only : forall addr len advice eff m m' evs,
  check_madvise addr len advice eff m = CheckOk m' evs -> mm_answer m eff m' evs.
Proof.
  intros until evs; intros H. unfold check_madvise in H. crush_checkA H;
    try (split; [apply vm_only_refl| split; [reflexivity| split; [reflexivity| split; reflexivity]]]).
  split; [unfold madvise_dontneed_next; apply vm_only_with_vm_backing|].
  split; [unfold madvise_dontneed_next; rewrite m_vmmaps_with_vm_backing; reflexivity|].
  split; [reflexivity| split; reflexivity].
Qed.

End RC__1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section AT.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition mm_at (at_ : machine_state -> Prop) (CHK : Model -> resp -> check_result) : Prop :=
  forall ms mo, at_ ms ->
    exists x8, ms_svc_pending ms = Some x8 /\
    (forall eff, check_syscall (sys_input segs ms x8) eff mo = CHK mo eff) /\
    (forall eff mo' evs, CHK mo eff = CheckOk mo' evs -> mm_answer mo eff mo' evs) /\
    (forall cfg, injected_family_off cfg (sys_input segs ms x8) = false).

Lemma mm_at_madvise : forall addr len, mm_at (at_madvise addr len) (madvise_CHK addr len).
Proof.
  intros addr len ms mo (Hsvc & Ha0 & Ha1 & Ha2).
  exists (Z_to_bv 64 233). split; [exact Hsvc|]. split; [| split].
  - intros eff. rewrite check_syscall_madvise by (rewrite in_sysno_si; reflexivity).
    rewrite ?in_a0_si, ?in_a1_si, ?in_a2_si. rewrite Ha0, Ha1, Ha2. reflexivity.
  - intros eff mo' evs. apply check_madvise_only.
  - intros cfg. unfold injected_family_off. rewrite in_sysno_si. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma at_kit : forall at_ CHK ms mo,
  mm_at at_ CHK -> at_ ms -> m_halted mo = None ->
  (forall eff, CHK mo eff <> CheckUnmodeled) ->
  (forall evs X, sstep segs (mkCfg ms mo) evs X ->
     exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ evs = [] /\ CHK mo eff = CheckOk mo' [])
  /\ (forall eff mo', CHK mo eff = CheckOk mo' [] -> sstep segs (mkCfg ms mo) [] (SNext (mkCfg (nret ms eff) mo')))
  /\ (exists eff mo', CHK mo eff = CheckOk mo' []).
Proof.
  intros at_ CHK ms mo Hmm Hat Hh Hnu. destruct (Hmm ms mo Hat) as (x8 & Hsvc & Hchk & Hans & _).
  assert (MAT : forall eff mo' evs, CHK mo eff = CheckOk mo' evs -> materialize_model_accesses mo' (syscall_effect_accesses eff) = Some mo').
  { intros eff mo' evs Hc. rewrite (mm_answer_accesses _ _ _ _ (Hans _ _ _ Hc)). apply materialize_model_accesses_nil. }
  split; [|split].
  - intros evs X Hst. destruct (sstep_svc_invA segs ms mo x8 evs X Hsvc Hst)
      as [(eff & mo' & mo'' & Hs & Hh' & Hm & ->) | [(eff & mo' & evs0 & Hs & Hh' & Hm & -> & ->) | [(eff & mo' & evs0 & code & Hs & Hh' & Hk' & -> & ->) | [(eff & mo' & evs0 & sig & Hs & Hk' & -> & ->) | (Hs & -> & ->)]]]].
    + apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs. pose proof (Hans _ _ _ Hs) as HA.
      rewrite (MAT _ _ _ Hs) in Hm. inversion Hm; subst. destruct HA as (_ & _ & -> & _).
      exists eff, mo''. repeat split; auto.
    + exfalso. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs. rewrite (MAT _ _ _ Hs) in Hm. discriminate.
    + exfalso. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs. pose proof (mm_answer_halted _ _ _ _ (Hans _ _ _ Hs)). congruence.
    + exfalso. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs. pose proof (mm_answer_halted _ _ _ _ (Hans _ _ _ Hs)) as Hh0.
      rewrite Hh in Hh0. rewrite (m_killed_of_m_halted_none _ Hh0) in Hk'. discriminate Hk'.
    + exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hs. rewrite Hchk in Hs. exact (Hnu _ Hs).
  - intros eff mo' Hc. eapply sstep_syscall; [exact Hh| exact Hsvc| | | exact (MAT _ _ _ Hc)].
    + apply check_syscall_ok_iff. rewrite Hchk. exact Hc.
    + rewrite (mm_answer_halted _ _ _ _ (Hans _ _ _ Hc)). exact Hh.
  - pose proof (receptive (sys_input segs ms x8) mo) as Hr.
    destruct (syscall_spec_witness (sys_input segs ms x8) mo) as [eff mo' evs|] eqn:E.
    + apply check_syscall_ok_iff in Hr. rewrite Hchk in Hr. exists eff, mo'.
      destruct (Hans _ _ _ Hr) as (_ & _ & -> & _). exact Hr.
    + exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr. rewrite Hchk in Hr. exact (Hnu _ Hr).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Variables (S : word -> Prop) (N : nat) (EB : Z).
Variable P : acc -> Prop.
#[warnings="-notation-for-abbreviation"] Local Notation KIPn := (KIP S N EB P).

(* [comment removed for export] *)
Theorem rzA_at_cfg : forall at_ CHK (Sh : resp -> Prop) (Q : resp -> machine_state -> Prop) ms mo (K : TSet),
  mm_at at_ CHK ->
  evtA segs P (fun ms1 => at_ ms1 /\ forall rsp, Sh rsp -> evtA segs P (Q rsp) (nret ms1 rsp)) ms ->
  KIPn mo -> K [] ->
  (forall mo1, magree mo mo1 -> KIA S N EB mo1 ->
     (forall eff, CHK mo1 eff <> CheckUnmodeled)
     /\ (forall eff mo', CHK mo1 eff = CheckOk mo' [] ->
           Sh eff /\
           exists (S' : word -> Prop) (N' : nat) (EB' : Z),
             LI S' N' EB' mo' /\ (forall x, P x -> acc_ok (m_vm_lazy mo') S' x) /\
             forall ms' moa', Q eff ms' -> magree mo' moa' -> KIA S' N' EB' moa' ->
               (forall x, P x -> acc_ok (m_vm_lazy moa') S' x) -> realizes_cfg acfg segs (mkCfg ms' moa') K)) ->
  realizes_cfg acfg segs (mkCfg ms mo) K.
Proof.
  intros at_ CHK Sh Q ms mo K Hmm IM HKP HK HUSER.
  eapply (rzA_seg_cfg segs S N EB P); [exact IM| exact HKP|].
  intros ms1 mo1 [Hat Hcont] Hag [HK1 HPS1]. pose proof HK1 as (HLI1 & Hmi1 & Hh1).
  destruct (HUSER mo1 Hag HK1) as (Hnu & HALL).
  destruct (at_kit at_ CHK ms1 mo1 Hmm Hat Hh1 Hnu) as (Hcomp & Hsound & (effg & mog & Hcg)).
  destruct (Hmm ms1 mo1 Hat) as (x8 & Hsvc & Hchk & Hans & Hfam).
  assert (MAT : forall eff mo' evs, CHK mo1 eff = CheckOk mo' evs -> materialize_model_accesses mo' (syscall_effect_accesses eff) = Some mo').
  { intros eff mo' evs Hc. rewrite (mm_answer_accesses _ _ _ _ (Hans _ _ _ Hc)). apply materialize_model_accesses_nil. }
  assert (NSP : forall eff, ~ spurious_refusal_cfg acfg (sys_input segs ms1 x8) mo1 eff).
  { intros eff (Hoff & _). rewrite Hfam in Hoff. discriminate Hoff. }
  set (I := { p : resp * Model | CHK mo1 (fst p) = CheckOk (snd p) [] }).
  eapply rz_conseq_cfg.
  - apply (rz_node_cfg acfg segs (mkCfg ms1 mo1) I (fun _ => []) (fun i : I => match i with exist _ p _ => mkCfg (nret ms1 (fst p)) (snd p) end)
             (fun _ => K) (exist _ (effg, mog) Hcg)).
    + split.
      * intros [[eff mo'] Hc]; cbn [fst snd] in *; cbn. unfold nret.
        eapply (sstep_cfg_syscall segs acfg ms1 mo1 x8 eff mo' mo' []); [exact Hh1| exact Hsvc| | exact (NSP _)| | exact (MAT _ _ _ Hc)].
        -- apply check_syscall_ok_iff. rewrite Hchk. exact Hc.
        -- rewrite (mm_answer_halted _ _ _ _ (Hans _ _ _ Hc)). exact Hh1.
      * intros e st Hst. destruct (Hcomp e st (sstep_cfg_sub _ _ _ _ _ Hst)) as (eff & mo' & -> & -> & Hc).
        exists (exist _ (eff, mo') Hc). split; reflexivity.
    + intros [[eff mo'] Hc]; cbn [fst snd] in *; cbn.
      destruct (HALL _ _ Hc) as (HSh & S' & N' & EB' & HLI' & HPS' & CONT).
      specialize (Hcont eff HSh).
      pose proof (mm_answer_minvA _ _ _ _ (Hans _ _ _ Hc) Hmi1) as Hmi'.
      pose proof (mm_answer_halted _ _ _ _ (Hans _ _ _ Hc)) as Hh'. rewrite Hh1 in Hh'.
      eapply (rzA_evt_cfg segs acfg S' N' EB' (m_vm_lazy mo')); [ | exact Hh' | exact HLI' | reflexivity |].
      * eapply evtA_weaken; [|exact Hcont]. exact HPS'.
      * intros ms' moa' HQ Hag' HLI'' Hh''. apply CONT; [exact HQ| exact Hag'| |].
        -- split; [exact HLI''|]. split; [eapply minvA_magree; eauto| exact Hh''].
        -- rewrite (magree_lazy _ _ Hag'). exact HPS'.
  - intros tr. split.
    + intros [i Hi]. apply t_emit_nil_l in Hi. destruct Hi as [->|Hi]; [exact HK| exact Hi].
    + intros Htr. exists (exist _ (effg, mog) Hcg). apply t_emit_nil_l. right. exact Htr.
Qed.

(* [comment removed for export] *)
Theorem rzA_madvise_cfg : forall addr len (Q : machine_state -> Prop) ms mo (K : TSet),
  0 <= addr -> addr mod 4096 = 0 -> 0 < len < 2^64 -> addr + page_round_up_Z len < 2^64 ->
  evtA segs P (fun ms1 => at_madvise addr len ms1 /\ evtA segs P Q (nret ms1 (madv_eff addr (page_round_up_Z len)))) ms ->
  KIPn mo -> K [] ->
  (forall mo1, magree mo mo1 -> KIA S N EB mo1 ->
     madvise_gate mo1 addr (page_round_up_Z len)
     /\ exists (S' : word -> Prop) (N' : nat) (EB' : Z),
          LI S' N' EB' (m_madv mo1 addr (page_round_up_Z len)) /\ (forall x, P x -> acc_ok (m_vm_lazy mo1) S' x) /\
          forall ms' moa', Q ms' -> magree (m_madv mo1 addr (page_round_up_Z len)) moa' -> KIA S' N' EB' moa' ->
            (forall x, P x -> acc_ok (m_vm_lazy moa') S' x) -> realizes_cfg acfg segs (mkCfg ms' moa') K) ->
  realizes_cfg acfg segs (mkCfg ms mo) K.
Proof.
  intros addr len Q ms mo K HA AA HL HE IM HKP HK HUSER.
  eapply (rzA_at_cfg (at_madvise addr len) (madvise_CHK addr len) (fun rsp => rsp = madv_eff addr (page_round_up_Z len)) (fun _ => Q) ms mo K).
  - apply mm_at_madvise.
  - eapply evtA_mono; [exact IM|]. intros ms1 [Hat Hc]. split; [exact Hat|]. intros rsp ->. exact Hc.
  - exact HKP.
  - exact HK.
  - intros mo1 Hag HK1. destruct (HUSER mo1 Hag HK1) as (G & S' & N' & EB' & HLI' & HPS' & CONT).
    split.
    + intros eff. rewrite (chk_madvise_red addr len mo1 eff HA AA HL HE G). apply madvise_match_nu.
    + intros eff mo' Hc. rewrite (chk_madvise_red addr len mo1 eff HA AA HL HE G) in Hc.
      apply madvise_match_inv in Hc as (-> & -> & _). split; [reflexivity|].
      exists S', N', EB'. split; [exact HLI'|]. split; [rewrite m_madv_lazy; exact HPS'|]. exact CONT.
Qed.

(* [comment removed for export] *)
Theorem rzA_madvise_cfg_same : forall addr len (Q : machine_state -> Prop) ms mo (K : TSet),
  0 <= addr -> addr mod 4096 = 0 -> 0 < len < 2^64 -> addr + page_round_up_Z len < 2^64 ->
  evtA segs P (fun ms1 => at_madvise addr len ms1 /\ evtA segs P Q (nret ms1 (madv_eff addr (page_round_up_Z len)))) ms ->
  KIPn mo -> K [] ->
  (forall mo1, magree mo mo1 -> KIA S N EB mo1 -> madvise_gate mo1 addr (page_round_up_Z len)) ->
  (forall ms' mo1 moa', Q ms' -> magree mo mo1 -> KIA S N EB mo1 -> magree (m_madv mo1 addr (page_round_up_Z len)) moa' -> KIPn moa' ->
     realizes_cfg acfg segs (mkCfg ms' moa') K) ->
  realizes_cfg acfg segs (mkCfg ms mo) K.
Proof.
  intros addr len Q ms mo K HA AA HL HE IM HKP HK HG CONT.
  eapply (rzA_madvise_cfg addr len Q ms mo K HA AA HL HE IM HKP HK).
  intros mo1 Hag HK1. split; [exact (HG mo1 Hag HK1)|].
  exists S, N, EB. split; [apply LI_madvise; exact (proj1 HK1)|].
  split.
  - intros x Hx. rewrite (magree_lazy _ _ Hag). exact (proj2 HKP x Hx).
  - intros ms' moa' HQ Hag' HKIA' HPS'. eapply (CONT ms' mo1 moa'); [exact HQ| exact Hag| exact HK1| exact Hag'|]. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_al : forall L, 0 <= L -> L mod 4096 = 0 -> page_round_up_Z L = L.
Proof. intros L H0 HL. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.

Theorem rzA_madvise_al_cfg : forall (Q : machine_state -> Prop) A L ms mo (K : TSet),
  0 <= A -> A mod 4096 = 0 -> 0 < L -> L mod 4096 = 0 -> A + L < 2^64 ->
  evtA segs P (fun ms1 => at_madvise A L ms1 /\ evtA segs P Q (nret ms1 (madv_eff A L))) ms ->
  KIPn mo -> K [] ->
  (forall mo1, magree mo mo1 -> KIA S N EB mo1 ->
     madvise_gate mo1 A L
     /\ exists (S' : word -> Prop) (N' : nat) (EB' : Z),
          LI S' N' EB' (m_madv mo1 A L) /\ (forall x, P x -> acc_ok (m_vm_lazy mo1) S' x) /\
          forall ms' moa', Q ms' -> magree (m_madv mo1 A L) moa' -> KIA S' N' EB' moa' ->
            (forall x, P x -> acc_ok (m_vm_lazy moa') S' x) -> realizes_cfg acfg segs (mkCfg ms' moa') K) ->
  realizes_cfg acfg segs (mkCfg ms mo) K.
Proof.
  intros Q A L ms mo K HA AA HL LA HE IM HKP HK HUSER.
  pose proof (page_round_up_Z_al L ltac:(lia) LA) as EL.
  eapply (rzA_madvise_cfg A L Q ms mo K HA AA ltac:(lia)); rewrite ?EL; first [eassumption | lia].
Qed.

Theorem rzA_madvise_al_cfg_same : forall (Q : machine_state -> Prop) A L ms mo (K : TSet),
  0 <= A -> A mod 4096 = 0 -> 0 < L -> L mod 4096 = 0 -> A + L < 2^64 ->
  evtA segs P (fun ms1 => at_madvise A L ms1 /\ evtA segs P Q (nret ms1 (madv_eff A L))) ms ->
  KIPn mo -> K [] ->
  (forall mo1, magree mo mo1 -> KIA S N EB mo1 -> madvise_gate mo1 A L) ->
  (forall ms' mo1 moa', Q ms' -> magree mo mo1 -> KIA S N EB mo1 -> magree (m_madv mo1 A L) moa' -> KIPn moa' ->
     realizes_cfg acfg segs (mkCfg ms' moa') K) ->
  realizes_cfg acfg segs (mkCfg ms mo) K.
Proof.
  intros Q A L ms mo K HA AA HL LA HE IM HKP HK HG CONT.
  pose proof (page_round_up_Z_al L ltac:(lia) LA) as EL.
  eapply (rzA_madvise_cfg_same A L Q ms mo K HA AA ltac:(lia)); rewrite ?EL; first [eassumption | lia].
Qed.

End AT.
End RC__2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section RC__3.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section ZSAME.
Variable segs : list Segment.

Lemma apply_zeros_same : forall (m : word -> option byte) a n,
  0 <= a < 2^64 -> 0 <= n < 2^64 -> a + n <= 2^64 ->
  (forall x, a <= x < a + n -> mrd segs m (wa x) = Some (Z_to_bv 8 0) /\ seg_rom segs (wa x) = None) ->
  forall y : word, apply_zeros m [(wa a, Z_to_bv 64 n)] y = m y.
Proof.
  intros m a n Ha Hn Han HZ y. rewrite apply_zeros_spec by assumption. unfold in_range.
  destruct ((a <=? bv_unsigned y) && (bv_unsigned y <? a + n)) eqn:C; [|reflexivity].
  apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
  destruct (HZ (bv_unsigned y) (conj C1 C2)) as [H1 H2]. rewrite wa_unsigned_id in H1, H2.
  unfold mrd in H1. destruct (m y) as [b|]; [congruence|]. rewrite H2 in H1. discriminate H1.
Qed.

Lemma zeros_same_frame : forall (m : word -> option byte) a n,
  0 <= a < 2^64 -> 0 <= n < 2^64 -> a + n <= 2^64 ->
  (forall x, a <= x < a + n -> mrd segs m (wa x) = Some (Z_to_bv 8 0) /\ seg_rom segs (wa x) = None) ->
  munch [] m (apply_zeros m [(wa a, Z_to_bv 64 n)]) /\ wmono segs m (apply_zeros m [(wa a, Z_to_bv 64 n)])
  /\ (mem_inv segs m -> mem_inv segs (apply_zeros m [(wa a, Z_to_bv 64 n)])).
Proof.
  intros m a n Ha Hn Han HZ. pose proof (apply_zeros_same m a n Ha Hn Han HZ) as E.
  split; [| split].
  - intros y _. apply E.
  - intros y Hy. unfold wview in *. rewrite E. exact Hy.
  - intros MI y b Hy. rewrite E in Hy. exact (MI y b Hy).
Qed.

(* [comment removed for export] *)
Lemma zero_chunk_covers : forall (m : word -> option byte) B k a n,
  rw_cells segs m B [CB k (repeat (Z_to_bv 8 0) k)] -> B <= a -> 0 <= n -> a + n <= B + Z.of_nat k ->
  (forall x, a <= x < a + n -> seg_rom segs (wa x) = None) ->
  forall x, a <= x < a + n -> mrd segs m (wa x) = Some (Z_to_bv 8 0) /\ seg_rom segs (wa x) = None.
Proof.
  intros m B k a n RW HB Hn HE HR x Hx. split; [| exact (HR x Hx)].
  pose proof (rw_cells_bytes_at segs m B _ RW) as (B0 & B1 & BY). cbn [cells_bytes cbytes] in BY, B1. rewrite app_nil_r in BY, B1.
  rewrite repeat_length in BY, B1.
  specialize (BY (Z.to_nat (x - B)) ltac:(lia)). rewrite Z2Nat.id in BY by lia. replace (B + (x - B)) with x in BY by lia.
  rewrite BY. apply nth_error_repeat. lia.
Qed.

End ZSAME.
End RC__3.
