(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Classical_Prop Classical_Pred_Type.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree ITreeCfg Nodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Abbreviation acfg := (alloc_only_cfg false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition node_off (cfg : SpuriousCfg) (n : node) : bool :=
  match n with
  | NBrk _ | NMmap _ _ _ _ | NMprotect _ _ _ | NMremap _ _ _ _ => negb (sc_alloc cfg)
  | NOpen _ => negb (sc_fs cfg)
  | _ => false
  end.

Definition node_refusal (n : node) (mo : Model) (r : word) : bool :=
  match n with
  | NBrk req => brk_refusal_b mo (Z_to_bv 64 req) r
  | NMmap _ _ _ _ => ret_in_errnos mmap_errnos r
  | NMremap _ _ _ _ => ret_in_errnos mremap_errnos r
  | NMprotect _ _ _ => ret_in_errnos mprotect_errnos r
  | NOpen _ => ret_in_errnos openat_errnos r
  | _ => false
  end.

(* [comment removed for export] *)
Definition ncan (n : node) (mo : Model) : Prop :=
  exists rsp' mo' evs', nstep n mo rsp' mo' evs' /\ node_refusal n mo (eff_ret rsp') = false.

(* [comment removed for export] *)
Definition nforced (n : node) (mo : Model) : Prop :=
  forall rsp' mo' evs', nstep n mo rsp' mo' evs' -> node_refusal n mo (eff_ret rsp') = true.

Lemma nforced_not_ncan : forall n mo, nforced n mo <-> ~ ncan n mo.
Proof.
  intros n mo. split.
  - intros F (rsp' & mo' & evs' & Hst & Hr). rewrite (F _ _ _ Hst) in Hr. discriminate Hr.
  - intros NC rsp' mo' evs' Hst. destruct (node_refusal n mo (eff_ret rsp')) eqn:E; [reflexivity|].
    exfalso. apply NC. exists rsp', mo', evs'. auto.
Qed.

(* [comment removed for export] *)
Definition nspur (cfg : SpuriousCfg) (n : node) (mo : Model) (r : word) : Prop :=
  node_off cfg n = true /\ node_refusal n mo r = true /\ ncan n mo.

Definition nstep_cfg (cfg : SpuriousCfg) (n : node) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
  if node_off cfg n then nstep n mo rsp mo' evs /\ (node_refusal n mo (eff_ret rsp) = true -> nforced n mo)
  else nstep n mo rsp mo' evs.

Lemma nstep_cfg_iff : forall cfg n mo rsp mo' evs,
  nstep_cfg cfg n mo rsp mo' evs <-> nstep n mo rsp mo' evs /\ ~ nspur cfg n mo (eff_ret rsp).
Proof.
  intros cfg n mo rsp mo' evs. unfold nstep_cfg, nspur.
  destruct (node_off cfg n).
  - split.
    + intros [Hst Hf]. split; [exact Hst|]. intros (_ & Hr & Hc). exact (proj1 (nforced_not_ncan n mo) (Hf Hr) Hc).
    + intros [Hst Hn]. split; [exact Hst|]. intros Hr. apply nforced_not_ncan. intros Hc. apply Hn. auto.
  - split; [intros Hst | intros [Hst _]; exact Hst]. split; [exact Hst|]. intros (E & _). discriminate E.
Qed.

Lemma nstep_cfg_sub : forall cfg n mo rsp mo' evs,
  nstep_cfg cfg n mo rsp mo' evs -> nstep n mo rsp mo' evs.
Proof. intros cfg n mo rsp mo' evs H. apply nstep_cfg_iff in H. exact (proj1 H). Qed.

Lemma nstep_cfg_off : forall cfg n mo rsp mo' evs,
  node_off cfg n = false -> (nstep_cfg cfg n mo rsp mo' evs <-> nstep n mo rsp mo' evs).
Proof. intros cfg n mo rsp mo' evs E. unfold nstep_cfg. rewrite E. reflexivity. Qed.

Lemma nstep_cfg_nonrefusal : forall cfg n mo rsp mo' evs,
  nstep n mo rsp mo' evs -> node_refusal n mo (eff_ret rsp) = false -> nstep_cfg cfg n mo rsp mo' evs.
Proof.
  intros cfg n mo rsp mo' evs Hst Hr. apply nstep_cfg_iff. split; [exact Hst|].
  intros (_ & Hr' & _). rewrite Hr in Hr'. discriminate Hr'.
Qed.

Lemma nstep_cfg_forced : forall cfg n mo rsp mo' evs,
  nstep n mo rsp mo' evs -> nforced n mo -> nstep_cfg cfg n mo rsp mo' evs.
Proof.
  intros cfg n mo rsp mo' evs Hst Hf. apply nstep_cfg_iff. split; [exact Hst|].
  intros (_ & _ & Hc). exact (proj1 (nforced_not_ncan n mo) Hf Hc).
Qed.

(* [comment removed for export] *)
Lemma nstep_cfg_succ_only : forall cfg n mo rsp mo' evs,
  node_off cfg n = true -> ncan n mo ->
  nstep_cfg cfg n mo rsp mo' evs ->
  nstep n mo rsp mo' evs /\ node_refusal n mo (eff_ret rsp) = false.
Proof.
  intros cfg n mo rsp mo' evs Hoff Hc H. apply nstep_cfg_iff in H as [Hst Hn]. split; [exact Hst|].
  destruct (node_refusal n mo (eff_ret rsp)) eqn:E; [|reflexivity].
  exfalso. apply Hn. split; [exact Hoff|]. split; [exact E | exact Hc].
Qed.

Section RC__.
Context {RC__ : RunCeiling}.

Lemma nstep_cfg_minv_preserved : forall cfg n mo eff mo' evs,
  lazy_free_node n -> minv mo -> m_halted mo = None -> nstep_cfg cfg n mo eff mo' evs ->
  m_halted mo' = None /\ minv mo'.
Proof. intros cfg n mo eff mo' evs Hl Hm Hh H. eapply minv_preserved; eauto using nstep_cfg_sub. Qed.

(* [comment removed for export] *)
Definition alloc_node (n : node) : bool :=
  match n with NBrk _ | NMmap _ _ _ _ | NMprotect _ _ _ | NMremap _ _ _ _ => true | _ => false end.

Lemma node_off_acfg : forall n, node_off acfg n = alloc_node n.
Proof. intros n; destruct n; reflexivity. Qed.

Lemma nstep_acfg_nonalloc : forall n mo rsp mo' evs,
  alloc_node n = false -> (nstep_cfg acfg n mo rsp mo' evs <-> nstep n mo rsp mo' evs).
Proof. intros n mo rsp mo' evs E. apply nstep_cfg_off. rewrite node_off_acfg. exact E. Qed.

(* [comment removed for export] *)
Lemma node_off_may_fail : forall n, node_off may_fail_cfg n = false.
Proof. intros n; destruct n; reflexivity. Qed.

Lemma nstep_may_fail : forall n mo rsp mo' evs,
  nstep_cfg may_fail_cfg n mo rsp mo' evs <-> nstep n mo rsp mo' evs.
Proof. intros. apply nstep_cfg_off. apply node_off_may_fail. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Link.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma at_node_svc : forall n ms, at_node segs n ms ->
  exists x8, ms_svc_pending ms = Some x8 /\
    ((exists K, x8 = Z_to_bv 64 K /\ injected_arm K = match n with
        | NBrk _ => Some (mkInjectedArm 214 FamAlloc [])
        | NMmap _ _ _ _ => Some (mkInjectedArm 222 FamAlloc mmap_errnos)
        | NMremap _ _ _ _ => Some (mkInjectedArm 216 FamAlloc mremap_errnos)
        | NMprotect _ _ _ => Some (mkInjectedArm 226 FamAlloc mprotect_errnos)
        | NOpen _ => Some (mkInjectedArm 56 FamFs openat_errnos)
        | _ => None end
      /\ bv_unsigned (Z_to_bv 64 K) = K /\ (K = 214 <-> exists req, n = NBrk req))).
Proof.
  intros n ms Hat.
  destruct n; cbn [at_node] in Hat;
  match goal with
  | [ H : (ms_svc_pending ms = Some ?a \/ ms_svc_pending ms = Some ?b) /\ _ |- _ ] =>
      destruct H as [[Hs|Hs] _]; eexists; split; [exact Hs| |exact Hs|]
  | [ H : ms_svc_pending ms = Some ?a /\ _ |- _ ] => destruct H as [Hs _]; eexists; split; [exact Hs|]
  | [ H : ms_svc_pending ms = Some ?a |- _ ] => eexists; split; [exact H|]
  end;
  match goal with
  | [ |- exists K, Z_to_bv 64 ?k = Z_to_bv 64 K /\ _ ] =>
      exists k; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
      split; [first [intros _; eexists; reflexivity | intros E; discriminate E]
            | first [intros _; reflexivity | intros [? E]; discriminate E]]
  end.
Qed.

Lemma node_off_link : forall cfg n ms x8,
  at_node segs n ms -> ms_svc_pending ms = Some x8 ->
  injected_family_off cfg (sys_input segs ms x8) = node_off cfg n.
Proof.
  intros cfg n ms x8 Hat Hsvc.
  destruct (at_node_svc n ms Hat) as (x8' & Hsvc' & K & -> & Harm & HK & _).
  assert (x8 = Z_to_bv 64 K) by congruence. subst x8.
  unfold injected_family_off. rewrite in_sysno_si, HK, Harm.
  destruct n; reflexivity.
Qed.

Lemma node_refusal_link : forall n ms x8 mo r,
  at_node segs n ms -> ms_svc_pending ms = Some x8 ->
  refusal_b (sys_input segs ms x8) mo r = node_refusal n mo r.
Proof.
  intros n ms x8 mo r Hat Hsvc.
  destruct (at_node_svc n ms Hat) as (x8' & Hsvc' & K & -> & Harm & HK & Hbrk).
  assert (x8 = Z_to_bv 64 K) by congruence. subst x8.
  unfold refusal_b. rewrite in_sysno_si, HK.
  destruct (Z.eqb_spec K 214) as [E|NE].
  - destruct (proj1 Hbrk E) as [req ->]. rewrite in_a0_si. cbn [node_refusal].
    cbn [at_node] in Hat. destruct Hat as [_ Ha0]. rewrite Ha0. reflexivity.
  - rewrite Harm. destruct n; try reflexivity. exfalso. apply NE. apply Hbrk. eexists; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma spurious_iff : forall cfg n ms mo x8 eff,
  at_node segs n ms -> minv mo -> m_halted mo = None -> nsafe n mo ->
  ms_svc_pending ms = Some x8 ->
  (spurious_refusal_cfg cfg (sys_input segs ms x8) mo eff <-> nspur cfg n mo (eff_ret eff)).
Proof.
  intros cfg n ms mo x8 eff Hat Hminv Hh Hsafe Hsvc.
  unfold spurious_refusal_cfg, nspur.
  rewrite (node_off_link cfg n ms x8 Hat Hsvc), (node_refusal_link n ms x8 mo (eff_ret eff) Hat Hsvc).
  destruct (node_off cfg n) eqn:Hoff.
  2:{ split; intros (E & _); discriminate E. }
  assert (Hne : match n with NExit _ => False | _ => True end).
  { destruct n; try exact I. cbn in Hoff. discriminate Hoff. }
  destruct (all_facts segs n ms mo Hne Hat Hminv Hh Hsafe) as (x8' & Hsvc' & Hcmp & Hsnd & _ & _).
  assert (x8' = x8) by congruence. subst x8'.
  split; intros (_ & Hr & Hex); (split; [reflexivity|]); (split; [exact Hr|]).
  - destruct Hex as (eff' & m' & evs' & Hspec & Hnr).
    apply check_syscall_ok_iff in Hspec. apply Hcmp in Hspec.
    exists (ceff eff'), m', evs'. split; [exact Hspec|].
    rewrite eff_ret_ceff, <- (node_refusal_link n ms x8 mo _ Hat Hsvc). exact Hnr.
  - destruct Hex as (rsp' & mo' & evs' & Hst & Hnr).
    destruct (Hsnd _ _ _ Hst) as [ci Hchk]. apply check_syscall_ok_iff in Hchk.
    exists (with_ci ci rsp'), mo', evs'. split; [exact Hchk|].
    rewrite (node_refusal_link n ms x8 mo _ Hat Hsvc).
    destruct rsp' as [r ws zs us cs ci']; cbn [with_ci eff_ret] in *. exact Hnr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Let NS := nodes_sound segs.

(* [comment removed for export] *)
Lemma sstep_cfg_moved_inv : forall cfg ms mo x8 evs ms' mo',
  ms_svc_pending ms = Some x8 -> ms_svc_pending ms' = None ->
  sstep_cfg segs cfg (mkCfg ms mo) evs (SNext (mkCfg ms' mo')) ->
  exists eff m1, syscall_spec (sys_input segs ms x8) mo (Ok eff m1 evs)
    /\ ~ spurious_refusal_cfg cfg (sys_input segs ms x8) mo eff
    /\ ms' = nret ms eff.
Proof.
  intros cfg ms mo x8 evs ms' mo' Hsvc Hsvc' Hss.
  inversion Hss; subst; try congruence.
  match goal with
  | [ H : ms_svc_pending ms = Some ?x |- _ ] => assert (x = x8) by congruence; subst x
  end.
  eexists _, _. split; [eassumption|]. split; [eassumption | reflexivity].
Qed.

Theorem nodes_sound_cfg_segs : forall cfg,
  node_sound_cfg cfg node segs (at_node segs) (nstep_cfg cfg) nexit minv nsafe.
Proof.
  intros cfg. constructor.
  - (* [comment removed for export] *) exact (ns_pending _ _ _ _ _ _ _ NS).
  - (* [comment removed for export] *)
    intros n ms mo evs X Hat Hh Hminv Hsafe Hst.
    pose proof (sstep_cfg_sub _ _ _ _ _ Hst) as Hst0.
    destruct (ns_complete _ _ _ _ _ _ _ NS n ms mo evs X Hat Hh Hminv Hsafe Hst0)
      as [(rsp & mo' & -> & Hn) | (code & mo' & -> & Hx & ->)].
    + left. exists rsp, mo'. split; [reflexivity|]. apply nstep_cfg_iff. split; [exact Hn|].
      assert (Hx8 : exists x8, ms_svc_pending ms = Some x8).
      { destruct (ms_svc_pending ms) as [x8|] eqn:E; [exists x8; reflexivity|].
        exfalso. exact (ns_pending _ _ _ _ _ _ _ NS n ms Hat E). }
      destruct Hx8 as [x8 Hsvc].
      destruct (sstep_cfg_moved_inv cfg ms mo x8 evs (nret ms rsp) mo' Hsvc (nret_svc ms rsp) Hst)
        as (eff & m1 & Hspec & Hns & Heq).
      intros Hsp. apply Hns. rewrite <- (advance_apply_effect_ret ms eff rsp (eq_sym Heq)) in Hsp.
      apply (proj2 (spurious_iff cfg n ms mo x8 eff Hat Hminv Hh Hsafe Hsvc)). exact Hsp.
    + right. exists code, mo'. auto.
  - (* [comment removed for export] *)
    intros n ms mo rsp mo' evs Hat Hh Hminv Hsafe HP.
    pose proof HP as HP0. apply nstep_cfg_iff in HP0 as [Hn Hns].
    destruct (ns_sound _ _ _ _ _ _ _ NS n ms mo rsp mo' evs Hat Hh Hminv Hsafe Hn) as (Hh' & Hminv' & Hss).
    split; [exact Hh'|]. split; [exact Hminv'|].
    assert (Hx8 : exists x8, ms_svc_pending ms = Some x8).
    { destruct (ms_svc_pending ms) as [x8|] eqn:E; [exists x8; reflexivity|].
      exfalso. exact (ns_pending _ _ _ _ _ _ _ NS n ms Hat E). }
    destruct Hx8 as [x8 Hsvc].
    apply (sstep_cfg_of_sstep_syscall cfg segs ms mo x8); [exact Hsvc | apply nret_svc | exact Hss |].
    intros eff m1 evs1 Hspec Heq Hsp. apply Hns.
    rewrite <- (advance_apply_effect_ret ms eff rsp Heq).
    apply (proj1 (spurious_iff cfg n ms mo x8 eff Hat Hminv Hh Hsafe Hsvc)). exact Hsp.
  - (* [comment removed for export] *)
    intros n ms mo code mo' Hat Hh Hminv Hsafe HX.
    destruct (ns_exit _ _ _ _ _ _ _ NS n ms mo code mo' Hat Hh Hminv Hsafe HX) as [Hh' Hss].
    split; [exact Hh'|]. apply sstep_cfg_of_sstep_inplace; [| exact Hss].
    exact (ns_pending _ _ _ _ _ _ _ NS n ms Hat).
  - (* [comment removed for export] *)
    intros n ms mo Hat Hh Hminv Hsafe.
    destruct (ns_progress _ _ _ _ _ _ _ NS n ms mo Hat Hh Hminv Hsafe) as [(rsp & mo' & evs & Hn) | Hx]; [| right; exact Hx].
    left. destruct (node_refusal n mo (eff_ret rsp)) eqn:Hr.
    + destruct (classic (nforced n mo)) as [F | NF].
      * exists rsp, mo', evs. apply nstep_cfg_forced; assumption.
      * apply not_all_ex_not in NF as [rsp' NF]. apply not_all_ex_not in NF as [mo'' NF].
        apply not_all_ex_not in NF as [evs' NF].
        assert (Hn' : nstep n mo rsp' mo'' evs') by (apply NNPP; intros K; apply NF; intros H; exact (False_ind _ (K H))).
        exists rsp', mo'', evs'. apply nstep_cfg_nonrefusal; [exact Hn'|].
        destruct (node_refusal n mo (eff_ret rsp')) eqn:E; [| reflexivity]. exfalso. apply NF. intros _. reflexivity.
    + exists rsp, mo', evs. apply nstep_cfg_nonrefusal; assumption.
  - (* [comment removed for export] *) exact (ns_lazy _ _ _ _ _ _ _ NS).
Qed.

End Link.

Theorem nodes_sound_cfg : forall cfg segs,
  node_sound_cfg cfg node segs (at_node segs) (nstep_cfg cfg) nexit minv nsafe.
Proof. intros cfg segs. apply nodes_sound_cfg_segs. Qed.

End RC__.
