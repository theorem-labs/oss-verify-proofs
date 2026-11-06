(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import ExecA LazyModel ITreeA NodesA ImplRzA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Export BackingAlgebraA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition mm_answer (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  vm_only mo mo' /\ alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo)     (* [comment removed for export] *)
  /\ evs = [] /\ eff_copyins eff = [] /\ eff_writes eff = [].

Lemma vm_only_refl : forall m, vm_only m m. Proof. intros; repeat split; reflexivity. Qed.
Lemma vm_only_trans : forall m1 m2 m3, vm_only m1 m2 -> vm_only m2 m3 -> vm_only m1 m3.
Proof. intros m1 m2 m3 (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5). repeat split; congruence. Qed.
Lemma vm_only_with_vmmaps : forall h m, vm_only m (with_vmmaps h m).
Proof. intros h m. destruct m; unfold vm_only, with_vmmaps; cbn. unfold m_fds, m_fs, m_halted, m_tid, m_stdin; cbn. repeat split; reflexivity. Qed.
Lemma vm_only_with_vm_backing : forall l p m, vm_only m (with_vm_backing l p m).
Proof. intros l p m. destruct m; unfold vm_only, with_vm_backing; cbn. unfold m_fds, m_fs, m_halted, m_tid, m_stdin; cbn. repeat split; reflexivity. Qed.
Lemma vm_only_vm_forget_range : forall lo hi m, vm_only m (vm_forget_range lo hi m).
Proof. intros. unfold vm_forget_range. apply vm_only_with_vm_backing. Qed.
Lemma vm_only_vm_add_lazy : forall a n m, vm_only m (vm_add_lazy a n m).
Proof. intros. unfold vm_add_lazy. apply vm_only_with_vm_backing. Qed.
Lemma vm_only_with_mmap_backing : forall flags a n m m0, vm_only m0 m -> vm_only m0 (with_mmap_backing flags a n m).
Proof.
  intros flags a n m m0 H. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); [|exact H].
  eapply vm_only_trans; [exact H| apply vm_only_vm_add_lazy].
Qed.
Lemma vm_only_with_mmap_replacement : forall flags a n h m, vm_only m (with_mmap_replacement flags a n (with_vmmaps h m)).
Proof.
  intros. unfold with_mmap_replacement. apply vm_only_with_mmap_backing.
  eapply vm_only_trans; [apply vm_only_with_vmmaps| apply vm_only_vm_forget_range].
Qed.
Lemma vm_only_with_mmap_destroyed : forall a n h m, vm_only m (with_mmap_destroyed a n h m).
Proof. intros. unfold with_mmap_destroyed. eapply vm_only_trans; [apply vm_only_with_vmmaps| apply vm_only_vm_forget_range]. Qed.

(* [comment removed for export] *)
Lemma m_vmmaps_with_vm_backing : forall l p m, m_vmmaps (with_vm_backing l p m) = m_vmmaps m.
Proof. intros l p m. destruct m; reflexivity. Qed.
Lemma m_vmmaps_vm_forget_range : forall lo hi m, m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. intros. unfold vm_forget_range. apply m_vmmaps_with_vm_backing. Qed.
Lemma m_vmmaps_with_mmap_backing : forall flags a n m, m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_backing, vm_add_lazy. destruct (mmap_noreserve_b flags); [apply m_vmmaps_with_vm_backing| reflexivity]. Qed.
Lemma m_vmmaps_with_mmap_replacement : forall flags a n m, m_vmmaps (with_mmap_replacement flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_replacement. rewrite m_vmmaps_with_mmap_backing. apply m_vmmaps_vm_forget_range. Qed.
Lemma m_vmmaps_with_mmap_destroyed : forall a n h m, m_vmmaps (with_mmap_destroyed a n h m) = h.
Proof. intros. unfold with_mmap_destroyed. rewrite m_vmmaps_vm_forget_range. apply m_vmmaps_with_vmmaps. Qed.

End RC__1.
Ltac crush_checkA H :=
  repeat (cbv zeta beta iota in H;
          lazymatch type of H with
          | CheckReject = _ => discriminate H
          | CheckUnmodeled = _ => discriminate H
          | CheckOk _ _ = CheckOk _ _ => fail
          | check_ret_only _ _ _ _ = CheckOk _ _ =>
              let E := fresh "E" in
              apply check_ret_only_ok_iff in H as (E & ? & ?); first [subst | inversion E; subst; clear E]
          | (match ?x with _ => _ end) = _ => destruct x eqn:?
          end);
  try (lazymatch goal with G : CheckOk _ _ = CheckOk _ _ |- _ => injection G as <- <- end).

Ltac mm_answer_done :=
  split; [ first [ apply vm_only_refl
                 | apply vm_only_with_mmap_backing; apply vm_only_with_vmmaps
                 | apply vm_only_with_mmap_replacement
                 | apply vm_only_with_mmap_destroyed
                 | apply vm_only_with_vmmaps ]
         | split; [ rewrite ?m_vmmaps_with_mmap_backing, ?m_vmmaps_with_mmap_replacement, ?m_vmmaps_with_mmap_destroyed, ?m_vmmaps_with_vmmaps; reflexivity
                  | split; [reflexivity| split; reflexivity] ] ].

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma check_mmap_only : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> mm_answer m eff m' evs.
Proof. intros until evs; intros H. unfold check_mmap in H. crush_checkA H; mm_answer_done. Qed.

Lemma check_munmap_only : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs -> mm_answer m eff m' evs.
Proof. intros until evs; intros H. unfold check_munmap in H. crush_checkA H; mm_answer_done. Qed.

(* [comment removed for export] *)
Lemma materialize_model_accesses_nil : forall m, materialize_model_accesses m [] = Some m.
Proof. intros m. unfold materialize_model_accesses, materialize_accesses. cbn. rewrite with_vm_backing_id. reflexivity. Qed.

Lemma mm_answer_accesses : forall mo eff mo' evs, mm_answer mo eff mo' evs -> syscall_effect_accesses eff = [].
Proof. intros mo eff mo' evs (_ & _ & _ & Hc & Hw). unfold syscall_effect_accesses. rewrite Hc, Hw. reflexivity. Qed.

Lemma mm_answer_minvA : forall mo eff mo' evs, mm_answer mo eff mo' evs -> minvA mo -> minvA mo'.
Proof. intros mo eff mo' evs ((Hf & Hs & _ & Ht & _) & Ha & _) H. eapply minvA_by_fields; [exact Hf| exact Hs| exact Ht| exact Ha| exact H]. Qed.

Lemma mm_answer_halted : forall mo eff mo' evs, mm_answer mo eff mo' evs -> m_halted mo' = m_halted mo.
Proof. intros mo eff mo' evs ((_ & _ & Hh & _) & _). exact Hh. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_emit_nil_l : forall T tr, t_emit [] T tr <-> (tr = [] \/ T tr).
Proof.
  intros T tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & Ht)]; [left; apply is_prefix_nil_r in Hp; exact Hp | right; exact Ht].
  - intros [-> | Ht]; [left; apply is_prefix_nil | right; exists tr; split; [reflexivity| exact Ht]].
Qed.

Section MM.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition mm_node (n : node) (CHK : Model -> resp -> check_result) : Prop :=
  forall ms mo, at_node segs n ms ->
    exists x8, ms_svc_pending ms = Some x8 /\
    (forall eff, check_syscall (sys_input segs ms x8) eff mo = CHK mo eff) /\
    (forall eff mo' evs, CHK mo eff = CheckOk mo' evs -> mm_answer mo eff mo' evs).

Lemma mm_node_mmap : forall addr len prot flags,
  mm_node (NMmap addr len prot flags)
          (fun mo eff => check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                                    (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo).
Proof.
  intros addr len prot flags ms mo (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5).
  exists (Z_to_bv 64 222). split; [exact Hsvc|]. split.
  - intros eff. unfold check_syscall. rewrite in_sysno_si. change (bv_unsigned (Z_to_bv 64 222)) with 222.
    replace (lookup_ca checked_table 222) with (Some arm_mmap) by reflexivity.
    cbn [arm_mmap ca_check]. rewrite ?in_a0_si, ?in_a1_si, ?in_a2_si, ?in_a3_si, ?in_a4_si, ?in_a5_si.
    rewrite Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. reflexivity.
  - intros eff mo' evs. apply check_mmap_only.
Qed.

Lemma mm_node_munmap : forall addr len,
  mm_node (NMunmap addr len) (fun mo eff => check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo).
Proof.
  intros addr len ms mo (Hsvc & Ha0 & Ha1).
  exists (Z_to_bv 64 215). split; [exact Hsvc|]. split.
  - intros eff. unfold check_syscall. rewrite in_sysno_si. change (bv_unsigned (Z_to_bv 64 215)) with 215.
    replace (lookup_ca checked_table 215) with (Some arm_munmap) by reflexivity.
    cbn [arm_munmap ca_check]. rewrite ?in_a0_si, ?in_a1_si. rewrite Ha0, Ha1. reflexivity.
  - intros eff mo' evs. apply check_munmap_only.
Qed.

(* [comment removed for export] *)
Lemma mm_kit : forall n CHK ms mo,
  mm_node n CHK -> at_node segs n ms -> m_halted mo = None ->
  (forall eff, CHK mo eff <> CheckUnmodeled) ->
  (forall evs X, sstep segs (mkCfg ms mo) evs X ->
     exists eff mo', X = SNext (mkCfg (nret ms eff) mo') /\ evs = [] /\ CHK mo eff = CheckOk mo' [])
  /\ (forall eff mo', CHK mo eff = CheckOk mo' [] -> sstep segs (mkCfg ms mo) [] (SNext (mkCfg (nret ms eff) mo')))
  /\ (exists eff mo', CHK mo eff = CheckOk mo' []).
Proof.
  intros n CHK ms mo Hmm Hat Hh Hnu. destruct (Hmm ms mo Hat) as (x8 & Hsvc & Hchk & Hans).
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

Local Notation KIPn := (KIP S N EB P).


(* [comment removed for export] *)
Theorem rzA_mm : forall {A} n CHK (dec : resp -> option A) (Q : A -> machine_state -> Prop) ms mo (K : TSet),
  mm_node n CHK ->
  implA segs (at_nodeA segs) P (enode n dec) (epost Q) ms ->
  KIPn mo -> K [] ->
  (forall mo1, magree mo mo1 -> KIA S N EB mo1 ->
     (forall eff, CHK mo1 eff <> CheckUnmodeled)
     /\ (forall eff mo', CHK mo1 eff = CheckOk mo' [] ->
           exists a, dec eff = Some a /\
           exists (S' : word -> Prop) (N' : nat) (EB' : Z),
             LI S' N' EB' mo' /\ (forall x, P x -> acc_ok (m_vm_lazy mo') S' x) /\
             forall ms' moa', Q a ms' -> magree mo' moa' -> KIA S' N' EB' moa' ->
               (forall x, P x -> acc_ok (m_vm_lazy moa') S' x) -> realizes segs (mkCfg ms' moa') K)) ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros A n CHK dec Q ms mo K Hmm IM HKP HK HUSER.
  cbn [implA enode] in IM.
  eapply (rzA_seg segs S N EB P); [exact IM| exact HKP|].
  intros ms1 mo1 [[Hat Hpol] Hcont] Hag [HK1 HPS1]. pose proof HK1 as (HLI1 & Hmi1 & Hh1).
  destruct (HUSER mo1 Hag HK1) as (Hnu & HALL).
  destruct (mm_kit n CHK ms1 mo1 Hmm Hat Hh1 Hnu) as (Hcomp & Hsound & (eff0' & mo0' & Hc0)).
  destruct (Hmm ms1 mo1 Hat) as (x8m & _ & _ & Hans).
  set (I := { p : resp * Model | CHK mo1 (fst p) = CheckOk (snd p) [] }).
  eapply rz_conseq.
  - apply (rz_node segs (mkCfg ms1 mo1) I (fun _ => []) (fun i : I => match i with exist _ p _ => mkCfg (nret ms1 (fst p)) (snd p) end)
             (fun _ => K) (exist _ (eff0', mo0') Hc0)).
    + split.
      * intros [[eff mo'] Hc]; cbn. apply Hsound. exact Hc.
      * intros e st Hst. destruct (Hcomp e st Hst) as (eff & mo' & -> & -> & Hc).
        exists (exist _ (eff, mo') Hc). split; reflexivity.
    + intros [[eff mo'] Hc]; cbn [fst snd] in *; cbn.
      destruct (HALL _ _ Hc) as (a & D & S' & N' & EB' & HLI' & HPS' & CONT).
      specialize (Hcont eff). rewrite D in Hcont. cbn in Hcont.
      pose proof (mm_answer_minvA _ _ _ _ (Hans _ _ _ Hc) Hmi1) as Hmi'.
      pose proof (mm_answer_halted _ _ _ _ (Hans _ _ _ Hc)) as Hh'. rewrite Hh1 in Hh'.
      eapply (rzA_evt segs S' N' EB' (m_vm_lazy mo')); [ | exact Hh' | exact HLI' | reflexivity |].
      * eapply evtA_weaken; [|exact Hcont]. exact HPS'.
      * intros ms' moa' HQ Hag' HLI'' Hh''. apply CONT; [exact HQ| exact Hag'| |].
        -- split; [exact HLI''|]. split; [eapply minvA_magree; eauto| exact Hh''].
        -- rewrite (magree_lazy _ _ Hag'). exact HPS'.
  - intros tr. split.
    + intros [i Hi]. apply t_emit_nil_l in Hi. destruct Hi as [->|Hi]; [exact HK| exact Hi].
    + intros Htr. exists (exist _ (eff0', mo0') Hc0). apply t_emit_nil_l. right. exact Htr.
Qed.

(* [comment removed for export] *)
Theorem rzA_mm_cfg : forall {A} n CHK (dec : resp -> option A) (Q : A -> machine_state -> Prop) ms mo (K : TSet),
  mm_node n CHK ->
  (node_off acfg n = true \/ forall mo r, node_refusal n mo r = false) ->
  implA segs (at_nodeA segs) P (enode n dec) (epost Q) ms ->
  KIPn mo -> K [] ->
  (forall mo1, magree mo mo1 -> KIA S N EB mo1 ->
     (forall eff, CHK mo1 eff <> CheckUnmodeled)
     /\ (exists eff mo', CHK mo1 eff = CheckOk mo' [] /\ node_refusal n mo1 (eff_ret eff) = false)
     /\ (forall eff mo', CHK mo1 eff = CheckOk mo' [] -> node_refusal n mo1 (eff_ret eff) = false ->
           exists a, dec eff = Some a /\
           exists (S' : word -> Prop) (N' : nat) (EB' : Z),
             LI S' N' EB' mo' /\ (forall x, P x -> acc_ok (m_vm_lazy mo') S' x) /\
             forall ms' moa', Q a ms' -> magree mo' moa' -> KIA S' N' EB' moa' ->
               (forall x, P x -> acc_ok (m_vm_lazy moa') S' x) -> realizes_cfg acfg segs (mkCfg ms' moa') K)) ->
  realizes_cfg acfg segs (mkCfg ms mo) K.
Proof.
  intros A n CHK dec Q ms mo K Hmm NOFF IM HKP HK HUSER.
  cbn [implA enode] in IM.
  eapply (rzA_seg_cfg segs S N EB P); [exact IM| exact HKP|].
  intros ms1 mo1 [[Hat Hpol] Hcont] Hag [HK1 HPS1]. pose proof HK1 as (HLI1 & Hmi1 & Hh1).
  destruct (HUSER mo1 Hag HK1) as (Hnu & (effg & mog & Hcg & Hgr) & HALL).
  destruct (mm_kit n CHK ms1 mo1 Hmm Hat Hh1 Hnu) as (Hcomp & Hsound & _).
  destruct (Hmm ms1 mo1 Hat) as (x8 & Hsvc & Hchk & Hans).
  assert (MAT : forall eff mo' evs, CHK mo1 eff = CheckOk mo' evs -> materialize_model_accesses mo' (syscall_effect_accesses eff) = Some mo').
  { intros eff mo' evs Hc. rewrite (mm_answer_accesses _ _ _ _ (Hans _ _ _ Hc)). apply materialize_model_accesses_nil. }
  (* [comment removed for export] *)
  assert (NSP : forall eff, node_refusal n mo1 (eff_ret eff) = false -> ~ spurious_refusal_cfg acfg (sys_input segs ms1 x8) mo1 eff).
  { intros eff Hr (_ & Hrb & _). rewrite (node_refusal_link segs n ms1 x8 mo1 _ Hat Hsvc) in Hrb. rewrite Hr in Hrb. discriminate Hrb. }
  assert (NRF : forall eff mo', CHK mo1 eff = CheckOk mo' [] ->
            ~ spurious_refusal_cfg acfg (sys_input segs ms1 x8) mo1 eff -> node_refusal n mo1 (eff_ret eff) = false).
  { intros eff mo' Hc Hns. destruct NOFF as [Hoff | Hnone]; [| apply Hnone].
    destruct (node_refusal n mo1 (eff_ret eff)) eqn:E; [| reflexivity]. exfalso. apply Hns.
    split; [rewrite (node_off_link segs acfg n ms1 x8 Hat Hsvc); exact Hoff|].
    split; [rewrite (node_refusal_link segs n ms1 x8 mo1 _ Hat Hsvc); exact E|].
    exists effg, mog, []. split; [apply check_syscall_ok_iff; rewrite Hchk; exact Hcg|].
    rewrite (node_refusal_link segs n ms1 x8 mo1 _ Hat Hsvc). exact Hgr. }
  set (I := { p : resp * Model | CHK mo1 (fst p) = CheckOk (snd p) [] /\ node_refusal n mo1 (eff_ret (fst p)) = false }).
  eapply rz_conseq_cfg.
  - apply (rz_node_cfg acfg segs (mkCfg ms1 mo1) I (fun _ => []) (fun i : I => match i with exist _ p _ => mkCfg (nret ms1 (fst p)) (snd p) end)
             (fun _ => K) (exist _ (effg, mog) (conj Hcg Hgr))).
    + split.
      * intros [[eff mo'] [Hc Hr]]; cbn [fst snd] in *; cbn. unfold nret.
        eapply (sstep_cfg_syscall segs acfg ms1 mo1 x8 eff mo' mo' []); [exact Hh1| exact Hsvc| | exact (NSP _ Hr)| | exact (MAT _ _ _ Hc)].
        -- apply check_syscall_ok_iff. rewrite Hchk. exact Hc.
        -- rewrite (mm_answer_halted _ _ _ _ (Hans _ _ _ Hc)). exact Hh1.
      * intros e st Hst. destruct (Hcomp e st (sstep_cfg_sub _ _ _ _ _ Hst)) as (eff & mo' & -> & -> & Hc).
        destruct (sstep_cfg_moved_inv segs acfg ms1 mo1 x8 [] _ _ Hsvc (advance_past_svc_svc _) Hst) as (eff2 & m2 & Hs2 & Hns2 & E2).
        unfold nret in E2. pose proof (advance_apply_effect_ret _ _ _ E2) as Er.
        assert (Hr : node_refusal n mo1 (eff_ret eff) = false).
        { rewrite Er. apply check_syscall_ok_iff in Hs2. rewrite Hchk in Hs2.
          apply (NRF eff2 m2); [exact Hs2| exact Hns2]. }
        exists (exist _ (eff, mo') (conj Hc Hr)). split; reflexivity.
    + intros [[eff mo'] [Hc Hr]]; cbn [fst snd] in *; cbn.
      destruct (HALL _ _ Hc Hr) as (a & D & S' & N' & EB' & HLI' & HPS' & CONT).
      specialize (Hcont eff). rewrite D in Hcont. cbn in Hcont.
      pose proof (mm_answer_minvA _ _ _ _ (Hans _ _ _ Hc) Hmi1) as Hmi'.
      pose proof (mm_answer_halted _ _ _ _ (Hans _ _ _ Hc)) as Hh'. rewrite Hh1 in Hh'.
      eapply (rzA_evt_cfg segs acfg S' N' EB' (m_vm_lazy mo')); [ | exact Hh' | exact HLI' | reflexivity |].
      * eapply evtA_weaken; [|exact Hcont]. exact HPS'.
      * intros ms' moa' HQ Hag' HLI'' Hh''. apply CONT; [exact HQ| exact Hag'| |].
        -- split; [exact HLI''|]. split; [eapply minvA_magree; eauto| exact Hh''].
        -- rewrite (magree_lazy _ _ Hag'). exact HPS'.
  - intros tr. split.
    + intros [i Hi]. apply t_emit_nil_l in Hi. destruct Hi as [->|Hi]; [exact HK| exact Hi].
    + intros Htr. exists (exist _ (effg, mog) (conj Hcg Hgr)). apply t_emit_nil_l. right. exact Htr.
Qed.

End MM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_unmodeled_free : forall addr len prot flags mo mo1,
  magree mo mo1 ->
  mmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) (m_vmmaps mo) = true ->   (* [comment removed for export] *)
  forall eff, check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo1 <> CheckUnmodeled.
Proof. intros addr len prot flags mo mo1 Hag Hs eff. apply mmap_safe_no_unmodeled. rewrite (magree_vmmaps _ _ Hag). exact Hs. Qed.

Lemma munmap_unmodeled_free : forall addr len mo mo1,
  magree mo mo1 ->
  munmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (m_vmmaps mo) = true ->
  forall eff, check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo1 <> CheckUnmodeled.
Proof. intros addr len mo mo1 Hag Hs eff. apply munmap_safe_no_unmodeled. rewrite (magree_vmmaps _ _ Hag). exact Hs. Qed.
End RC__2.
