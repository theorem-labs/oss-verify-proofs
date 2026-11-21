(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed A_bytes_flat_map_split, BINV_awf, BINV_elim and 299 more; added grant_exists_na, grant_ok_na, grant_ok_na_pin_of_grant_ok_na and 9 more; removed grant_ok_na_pin_eq; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/AsanNodesMmLibK.v, 1699 lines within its lines 24-4133. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap. From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Common.Cfg Require RomBase.
Module KitNodesS.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.   (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.AllocSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.Scfg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.AsanCeil.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition alloc_enomem_sysno_b (n : Z) : bool :=
  match injected_arm n with Some _ => true | None => false end.
(* [comment removed for export] *)
Definition alloc_mm_sysno_b (n : Z) : bool := (n =? 222)%Z || (n =? 226)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition grant_ok_na_pin (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).

(* [comment removed for export] *)
Lemma grant_ok_na_pin_unpack : forall m a n,
  (0 < n)%Z -> (n mod page_size = 0)%Z ->
  grant_ok_na_pin m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z
  /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
  intros m a n Hn Hnal H. unfold grant_ok_na_pin in H.
  apply andb_true_iff in H as [H Hrf].
  apply andb_true_iff in H as [H Htop].
  apply andb_true_iff in H as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop.
  repeat split; assumption.
Qed.
Definition grant_ok_na (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a
  && (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n)
  && hint_placement_ok_b hint (m_vmmaps m) (bv_unsigned a) n.

(* [comment removed for export] *)
Lemma grant_ok_na_pin_of_na : forall hint m a n,
  grant_ok_na hint m a n = true -> grant_ok_na_pin m a n = true.
Proof.
  intros hint m a n H. unfold grant_ok_na, grant_ok_na_pin in *.
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H Hrf].
  apply andb_true_iff in H as [H Htop].
  apply andb_true_iff in H as [H Hpos].
  apply andb_true_iff in H as [_ Hal].
  rewrite Hal, Hpos, Htop, Hrf. reflexivity.
Qed.

Lemma grant_ok_na_pin_of_grant_ok : forall hint m a n, grant_ok hint m a n = true -> grant_ok_na_pin m a n = true.
Proof.
  (* [comment removed for export] *)
  intros hint m a n H. unfold grant_ok, grant_ok_na_pin in *. rewrite !andb_true_iff in H.
  destruct H as [[[[[_ Hal] Hpos] Htop] Hrf] _]. rewrite Hal, Hpos, Htop, Hrf. reflexivity.
Qed.
Lemma grant_ok_na_place : forall hint m a n,
  grant_ok_na hint m a n = true ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true.
Proof.
  intros hint m a n H. unfold grant_ok_na in H.
  rewrite !andb_true_iff in H. tauto.
Qed.

(* [comment removed for export] *)
Lemma grant_na_pin_not_errno : forall m a n,
  (0 < n)%Z -> (n mod page_size = 0)%Z -> grant_ok_na_pin m a n = true ->
  errno_ret_in mmap_errnos a = false.
Proof.
  intros m a n Hn Hnal Hg.
  destruct (grant_ok_na_pin_unpack _ _ _ Hn Hnal Hg) as (_ & _ & Htop & _).
  apply errno_ret_in_below; [reflexivity|]. alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.

Section Shim.
Context {fx : PropExec.FPState}.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

Lemma not_unforced_na : forall ms model x8 eff,
  alloc_enomem_sysno_b (bv_unsigned x8) = false ->
  ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model eff.
Proof.
  intros ms model x8 eff Hal. unfold alloc_enomem_sysno_b in Hal.
  destruct (injected_arm (bv_unsigned x8)) eqn:E; [discriminate|].
  intros (Hoff & _ & _). unfold injected_family_off in Hoff. cbn [in_sysno sys_input] in Hoff. rewrite E in Hoff. discriminate.
Qed.

Lemma alloc_nonrefusal_step : forall ms model x8 eff,
  refusal_b (sys_input segs ms x8) model (eff_ret eff) = false ->
  ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model eff.
Proof. intros. apply not_spurious_nonrefusal. assumption. Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_of_check_noacc : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model eff ->
  m_halted m' = None ->
  syscall_effect_accesses eff = [] ->
  sstep_cfg segs scfg (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hns Hh' Hacc.
  apply (sstep_cfg_syscall segs scfg ms model x8 eff m' m' evs Hh Hsvc).
  - apply check_syscall_ok_iff. exact Hc.
  - exact Hns.
  - exact Hh'.
  - rewrite Hacc. apply materialize_model_accesses_nil.
Qed.

(* [comment removed for export] *)
Lemma node_chk_ev_gen : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model eff ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev -> m_halted m' = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs scfg (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hnf Hinv Hnu Hnh Hlazy. split.
  - intros i. apply (sstep_cfg_of_check segs scfg ms model x8); auto. exact (Hnh _ _ _ (Hok i)).
  - intros e st Hss.
    destruct (sstep_cfg_svc_inv segs scfg ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(Hnsp & Hh2 & [(m'' & -> & Hmat & ->) | (-> & Hmat & ->)]) | (code & Hh2 & -> & ->)])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc Hnsp) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
      injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc Hnsp) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
    + rewrite (Hnh _ _ _ Hc) in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

(* [comment removed for export] *)
Lemma node_chk_ev_gen_noacc : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  (forall m, materialize_model_accesses m [] = Some m) ->
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model eff ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev -> m_halted m' = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs scfg (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs mat_nil Hh Hsvc Hok Hnf Hinv Hnu Hnh Hacc. split.
  - intros i. apply (sstep_cfg_of_check_noacc ms model x8); auto. exact (Hnh _ _ _ (Hok i)).
  - intros e st Hss.
    destruct (sstep_cfg_svc_inv segs scfg ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(Hnsp & Hh2 & [(m'' & -> & Hmat & ->) | (-> & Hmat & ->)]) | (code & Hh2 & -> & ->)])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc Hnsp) as (i & -> & -> & ->).
      rewrite (Hacc i), mat_nil in Hmat. injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc Hnsp) as (i & -> & -> & ->).
      rewrite (Hacc i), mat_nil in Hmat. discriminate.
    + rewrite (Hnh _ _ _ Hc) in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

(* [comment removed for export] *)
Lemma refusal_b_mmap_sys : forall ms x8 model r,
  bv_unsigned x8 = 222%Z ->
  refusal_b (sys_input segs ms x8) model r = errno_ret_in mmap_errnos r.
Proof.
  intros ms x8 model r Hno. unfold refusal_b. cbn [in_sysno sys_input]. rewrite Hno. reflexivity.
Qed.

Section Alloc.
Hypothesis Halloc : sc_alloc scfg = false.

(* [comment removed for export] *)
Lemma alloc_refusal_unforced : forall ms model x8 eff effS mS evS,
  alloc_mm_sysno_b (bv_unsigned x8) = true ->
  check_syscall (sys_input segs ms x8) effS model = CheckOk mS evS ->
  refusal_b (sys_input segs ms x8) model (eff_ret effS) = false ->
  refusal_b (sys_input segs ms x8) model (eff_ret eff) = true ->
  spurious_refusal_cfg scfg (sys_input segs ms x8) model eff.
Proof.
  intros ms model x8 eff effS mS evS Hal HcS HnS Hr.
  apply (spurious_intro scfg _ model eff effS mS evS); [| exact Hr | apply check_syscall_ok_iff; exact HcS | exact HnS].
  unfold alloc_mm_sysno_b in Hal. apply orb_prop in Hal as [E | E]; apply Z.eqb_eq in E.
  - apply (injected_family_off_222 segs scfg ms x8 E Halloc).
  - apply (injected_family_off_226 segs scfg ms x8 E Halloc).
Qed.
End Alloc.
End Shim.
End KitNodesS.
From Stdlib Require FunctionalExtensionality. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BackingAlgebra. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AsanPlanSoundK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.
Module AsanNodesLibEK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.   (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BackingAlgebra. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.AllocSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.AgentNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.AsanPlacement OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BackingAlgebra.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.Scfg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.KitNodesS.   (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.AsanCeil. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).  (* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Common.Cfg Require RomBase.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Noacc.
Context {fxg : PropExec.FPState}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.   (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_of_check_noacc : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model eff ->   (* [comment removed for export] *)
  m_halted m' = None ->
  syscall_effect_accesses eff = [] ->
  sstep_cfg segs scfg (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof. exact (sstep_cfg_of_check_noacc segs scfg). Qed.

Lemma node_chk_ev_noacc : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  alloc_enomem_sysno_b (bv_unsigned x8) = false ->   (* [comment removed for export] *)
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs scfg (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hal Hok Hinv Hnu Hh' Hacc.
  (* [comment removed for export] *)
  apply (node_chk_ev_gen_noacc segs scfg ms model x8 I effs ms' evs materialize_model_accesses_nil Hh Hsvc Hok).
  - intros i. apply not_unforced_na. exact Hal.
  - intros eff m' ev Hc _. exact (Hinv eff m' ev Hc).
  - exact Hnu.
  - intros eff m' ev Hc. destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). apply Hh'.
  - exact Hacc.
Qed.

Lemma node_chk_noacc : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  alloc_enomem_sysno_b (bv_unsigned x8) = false ->   (* [comment removed for export] *)
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
  (forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
     exists i, eff = effs i /\ m' = ms' i /\ evs = []) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs scfg (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' Hh Hsvc Hal Hok Hinv Hnu Hh' Hacc.
  apply (node_chk_ev_noacc ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hal Hok); auto.
Qed.

Lemma node_det_noacc : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  alloc_enomem_sysno_b (bv_unsigned x8) = false ->   (* [comment removed for export] *)
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  node_ok segs scfg (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hal Hchk Hnu Hh0 Hacc.
  apply (node_chk_ev_noacc ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc Hal).
  - intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
  - intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto.
  - exact Hnu.
  - intros []; exact Hh0.
  - intros []; exact Hacc.
Qed.

Lemma rz_det_noacc : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  alloc_enomem_sysno_b (bv_unsigned x8) = false ->   (* [comment removed for export] *)
  RomBase.sys_rob segs (mkCfg ms model) ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  realizes segs scfg (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  realizes segs scfg (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hal Hrob Hchk Hnu Hh0 Hacc Hc.
  eapply rz_silent1; [eapply node_det_noacc; eassumption | exact Hrob | exact Hc].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_det_noacc : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  alloc_enomem_sysno_b (bv_unsigned x8) = false ->   (* [comment removed for export] *)
  RomBase.sys_rob segs (mkCfg ms model) ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  syscall_effect_accesses eff0 = [] ->
  srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  srealizes segs scfg (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hal Hrob Hchk Hnu Hh0 Hacc Hc.
  eapply srz_silent1; [eapply node_det_noacc; eassumption | exact Hrob | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma srz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs scfg c I (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  (forall i, srealizes segs scfg (nx i) (T i)) ->
  srealizes segs scfg c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hrob Hc.
  apply (srz_conseq segs scfg c (t_alt (fun i => t_emit [] (T i)))).
  - apply (srz_node segs scfg c I (fun _ => []) nx T i0 Hnode Hrob Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (srealizes_nonempty segs scfg _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (srealizes_nonempty segs scfg _ _ (Hc i)) tr) Hi).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma with_vm_backing_halted : forall l p m, m_halted (with_vm_backing l p m) = m_halted m.
Proof. reflexivity. Qed.

Lemma vm_add_lazy_halted : forall a n m, m_halted (vm_add_lazy a n m) = m_halted m.
Proof. reflexivity. Qed.

Lemma with_mmap_backing_halted : forall flags a n m,
  m_halted (with_mmap_backing flags a n m) = m_halted m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma with_mmap_replacement_halted : forall flags a n m,
  m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
  intros. unfold with_mmap_replacement. rewrite with_mmap_backing_halted.
  apply vm_forget_range_halted.
Qed.

Lemma with_mmap_destroyed_halted : forall a n h m,
  m_halted (with_mmap_destroyed a n h m) = m_halted m.
Proof. intros. unfold with_mmap_destroyed. rewrite vm_forget_range_halted. apply with_vmmaps_halted. Qed.

Lemma forget_vm_ranges_halted : forall ranges m,
  m_halted (forget_vm_ranges ranges m) = m_halted m.
Proof.
  induction ranges as [|[a n] r IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. apply vm_forget_range_halted.
Qed.

Lemma brk_model_halted : forall req r m, m_halted (brk_model req r m) = m_halted m.
Proof.
  intros. unfold brk_model, with_brk_next. cbv zeta.
  rewrite forget_vm_ranges_halted. apply with_vmmaps_halted.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stepacc_ecall_epend : forall regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom)
  = MachineOk (@mkAccessReport machine_state (epend regs pc mem rom (getr regs 17)) []).
Proof.
  intros regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_instr_noacc : forall ms model ms',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  node_ok segs scfg (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hsvc Hstep.
  assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
  { unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }
  (* [comment removed for export] *)
  apply (node_ok_of_pnode_instr segs scfg); [exact Hsvc |].
  split.
  - intros []. apply (sstep_instr segs ms model ms' model Hh Hsvc Hacc).
  - intros e st Hss. exists tt.
    inversion Hss; subst;
      match goal with
      | H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
      | H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
      end.
Qed.

Lemma rz_sys_lazy : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  realizes segs scfg (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  realizes segs scfg (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply rz_silent1; [| apply RomBase.sys_rob_instr; reflexivity | exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)
Lemma epend_len : forall regs pc mem rom (len : Z),
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  bv_unsigned (ms_gpr (epend regs pc mem rom (getr regs 17)) 1) = len
  /\ ms_gpr (epend regs pc mem rom (getr regs 17)) 1 <> Z_to_bv 64 0.
Proof.
  intros regs pc mem rom len H11 Hlen. rewrite ms_gpr_epend1, H11. split.
  - apply u64_lit. lia.
  - intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia.
Qed.

(* [comment removed for export] *)

Lemma srz_sys_lazy : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  srealizes segs scfg (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply srz_silent1; [| apply RomBase.sys_rob_instr; reflexivity | exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma srz_munmap_lazy : forall regs (pc : word) mem rom model w (a : word) (len : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->  (* [comment removed for export] *)
  map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                             (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) rom)
                      (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w a len K HF HE Hh H17 H10 Hal H11 Hlen Hnw Hhas Hc.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE, two_pow_64 in *. lia. }
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 215%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hargs : munmap_args_ok ms model).
  { unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
    intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
  (* [comment removed for export] *)
  apply (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.NoReserveK.srz_munmap_lazy segs scfg ms model (getr regs 17) K
           Halloc Hh eq_refl Hno Hargs).
  unfold munmap_eff. rewrite H0, Hpr.
  unfold ms. rewrite adv_unmaps1_epend. exact Hc.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma node_brk_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  node_ok segs scfg (mkCfg ms model)
    {r : word | brk_adm scfg model (ms_gpr ms 0) r}
    (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms
                       (mkEffectU (proj1_sig i) []
                          (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                          (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
                    (brk_model (ms_gpr ms 0) (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hsvc Hno.
  set (req := ms_gpr ms 0).
  assert (Hfam : sc_alloc scfg = false -> injected_family_off scfg (sys_input segs ms x8) = true).
  { intros Ealloc. rewrite (injected_family_off_alloc scfg _ 214%Z);
      [rewrite Ealloc; reflexivity | rewrite in_sysno_sys_input; exact Hno | auto]. }
  apply (node_chk_ev_gen_noacc segs scfg ms model x8 {r : word | brk_adm scfg model req r}
           (fun i => brk_eff ms model (proj1_sig i))
           (fun i => brk_model req (proj1_sig i) model) (fun _ => []) materialize_model_accesses_nil Hh Hsvc).
  - intros [r [Hr Hf]]. cbn [proj1_sig]. apply check_syscall_ok_iff. exact (brk_ok_intro segs ms x8 model r Hno Hr).
  - intros [r [Hr Hf]]. cbn [proj1_sig].
    destruct (sc_alloc scfg) eqn:Ealloc.
    + apply not_spurious_on. rewrite (injected_family_off_alloc scfg _ 214%Z);
        [rewrite Ealloc; reflexivity | rewrite in_sysno_sys_input; exact Hno | auto].
    + destruct (brk_refusal_b model req r) eqn:Eref.
      * apply not_spurious_forced. intros eff' m' evs' Hspec.
        apply (brk_ok_iff segs ms x8 model eff' m' evs' Hno) in Hspec.
        destruct Hspec as (_ & _ & Hok' & _).
        rewrite (refusal_b_brk_ms segs ms x8 model _ Hno). apply (Hf eq_refl eq_refl). exact Hok'.
      * apply not_spurious_nonrefusal. unfold brk_eff. cbn [eff_ret].
        rewrite (refusal_b_brk_ms segs ms x8 model _ Hno). exact Eref.
  - intros eff m' ev Hc Hnsp. apply check_syscall_ok_iff in Hc.
    pose proof (proj1 (brk_ok_iff segs ms x8 model eff m' ev Hno) Hc) as (Heff & -> & Hok & ->).
    fold req in Heff, Hok.
    assert (Hadm : brk_adm scfg model req (eff_ret eff)).
    { split; [exact Hok|]. intros Ealloc Eref r' Hr'.
      destruct (brk_refusal_b model req r') eqn:E'; [reflexivity|]. exfalso. apply Hnsp.
      apply (spurious_intro scfg (sys_input segs ms x8) model eff (brk_eff ms model r') (brk_model req r' model) []).
      - exact (Hfam Ealloc).
      - rewrite (refusal_b_brk_ms segs ms x8 model _ Hno). exact Eref.
      - exact (brk_ok_intro segs ms x8 model r' Hno Hr').
      - unfold brk_eff. cbn [eff_ret]. rewrite (refusal_b_brk_ms segs ms x8 model _ Hno). exact E'. }
    exists (exist _ (eff_ret eff) Hadm). cbn [proj1_sig]. unfold brk_eff. fold req.
    split; [exact Heff | split; reflexivity].
  - intros eff Hc. apply (brk_no_unmodeled segs ms x8 model Hno).
    exact (proj1 (check_syscall_err_iff _ _ _) Hc).
  - intros eff m' ev Hc. apply check_syscall_ok_iff in Hc.
    pose proof (proj1 (brk_ok_iff segs ms x8 model eff m' ev Hno) Hc) as (_ & _ & _ & ->).
    rewrite brk_model_halted. exact Hh.
  - intros [r Hr]. reflexivity.
Qed.

Lemma srz_brk_query_lazy : forall regs (pc : word) mem rom model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w K HF HE Hh H17 H10 Hc.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hq : brk_adm scfg model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) by (rewrite H0; apply brk_adm_query; reflexivity).
  apply (srz_cases1 segs scfg _ _ _ K (exist _ _ Hq) (node_brk_lazy ms model (getr regs 17) Hh eq_refl Hno)
           (RomBase.sys_rob_memfree segs ms model (getr regs 17) eq_refl ltac:(rewrite Hno; exact RomBase.memfree_214))).
  intros [r Hr]. cbn [proj1_sig].
  assert (Er : r = vm_brk (m_vmmaps model)) by (apply (brk_adm_query scfg model); rewrite <- H0; exact Hr). subst r.
  rewrite H0, brk_zeros_query, brk_unmaps_keep.
  rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
  unfold ms. rewrite adv_ret_epend. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma srz_brk_grow_lazy : forall regs (pc : word) mem rom model w (d : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
  (* [comment removed for export] *)
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                             (zfill b (Z_to_bv 64 d) mem) rom)
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) KB ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w d KB HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HB.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_adm scfg model (ms_gpr ms 0) r <-> r = req).
  { intros r. rewrite H0. rewrite (brk_adm_grow_cases scfg model req r Halloc); [| fold h; fold b; rewrite Hureq; lia ..].
    rewrite Hadm. reflexivity. }
  assert (Hr0 : brk_adm scfg model (ms_gpr ms 0) req) by (apply Hcases; reflexivity).
  apply (srz_cases1 segs scfg _ _ _ KB (exist _ req Hr0) (node_brk_lazy ms model (getr regs 17) Hh eq_refl Hno)
           (RomBase.sys_rob_memfree segs ms model (getr regs 17) eq_refl ltac:(rewrite Hno; exact RomBase.memfree_214))).
  intros [r Hr]. cbn [proj1_sig]. fold h.
  pose proof (proj1 (Hcases r) Hr) as Er. subst r.
  assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
  unfold brk_page_range.
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned req))
    by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _) Hlt).
  replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
  rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
  unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption.
  unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

Lemma srz_brk_grow_blocked_lazy : forall regs (pc : word) mem rom model w (req : word) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  getr regs 10 = req ->
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned b <= bv_unsigned req)%Z ->
  Mmap.brk_grow_ok model req req = false ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) KA ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KA.
Proof.
  intros regs pc mem rom model w req KA HF HE Hh H17 h b H10 Hpos Hs Hb Hblk HA.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hres : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = b).
  { intros r. rewrite H0, (brk_r_ok_grow_cases model req r Hpos Hs Hb). fold h. fold b. split.
    - intros [-> | [-> Hg]]; [reflexivity | rewrite Hblk in Hg; discriminate].
    - intros ->. left. reflexivity. }
  (* [comment removed for export] *)
  assert (Hkeep : brk_adm scfg model (ms_gpr ms 0) b).
  { split; [apply Hres; reflexivity|]. intros _ E r' Hr'. apply Hres in Hr'. subst r'. exact E. }
  apply (srz_cases1 segs scfg _ _ _ KA (exist _ b Hkeep) (node_brk_lazy ms model (getr regs 17) Hh eq_refl Hno)
           (RomBase.sys_rob_memfree segs ms model (getr regs 17) eq_refl ltac:(rewrite Hno; exact RomBase.memfree_214))).
  intros [r [Hr Hf]]. cbn [proj1_sig]. fold h.
  pose proof (proj1 (Hres r) Hr) as Er. subst r. fold b.
  rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
  unfold ms. rewrite adv_ret_epend. exact HA.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma node_set_tid_lazy : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  node_ok segs scfg (mkCfg ms model) tid_I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (proj1_sig i) [] [] [] [] [])))
                    (with_tid (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hsvc Hno Htid.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model =
     match eff with
     | mkEffectU ret [] [] [] [] [] =>
         if ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool
         then CheckOk (with_tid ret model) [] else CheckReject
     | _ => CheckReject end).
  { intros eff. rewrite (check_syscall_96 segs ms x8 eff model Hno). unfold check_set_tid_address. rewrite Htid. reflexivity. }
  apply (node_chk_noacc ms model x8 tid_I
           (fun i => mkEffectU (proj1_sig i) [] [] [] [] [])
           (fun i => with_tid (proj1_sig i) model) Hh Hsvc ltac:(rewrite Hno; reflexivity)).
  - intros [t [Ht1 Ht2]]. cbn [proj1_sig]. rewrite Hchk.
    rewrite (proj2 (Z.ltb_lt _ _) Ht1), (proj2 (Z.ltb_lt _ _) Ht2). reflexivity.
  - intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool eqn:Eb; [|discriminate].
    apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
    injection Hc as <- <-. exists (exist _ ret (conj E1 E2)). repeat split; reflexivity.
  - intros [ret ws zs us cs ci] Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool; discriminate.
  - intros [t Ht]. cbn [proj1_sig]. rewrite with_tid_halted. exact Hh.
  - intros [t Ht]. reflexivity.
Qed.

Lemma srz_set_tid_lazy : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh H17 Htid Hk.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  apply (srz_conseq segs scfg _ (t_alt (fun _ : tid_I => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
  eapply srz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
                   | eapply node_set_tid_lazy; [exact Hh | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid]
                   | eapply RomBase.sys_rob_memfree; [reflexivity | rewrite H17, u64_lit by lia; exact RomBase.memfree_96] |].
  intros [t Ht]. cbn [proj1_sig].
  change (mkEffectU t [] [] [] [] []) with (mkEffect t [] []).
  rewrite apply_effect_no_write, adv_set_epend. apply Hk. exact Ht.
Qed.

(* [comment removed for export] *)
Lemma srz_exit_at_lazy : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh H17 H10.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply srz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_gates_core50 : forall flags prot,
  mmap_flags_core flags = 50%Z ->
  mmap_modeled_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true.
Proof.
  intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b.
  rewrite Hc. repeat split; try (vm_compute; reflexivity).
  all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.

Lemma srz_alt3 : forall c (nx : three -> config) (A B C : TSet),
  node_ok segs scfg c three (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  srealizes segs scfg (nx T1) A -> srealizes segs scfg (nx T2) B -> srealizes segs scfg (nx T3) C ->
  srealizes segs scfg c (t_alt3 A B C).
Proof.
  intros c nx A B C Hnode Hrob HA HB HC.
  apply (srz_conseq segs scfg c (t_alt (fun i => match i with T1 => A | T2 => B | T3 => C end))).
  - apply (srz_cases c three nx _ T1 Hnode Hrob). intros [| |]; assumption.
  - intros tr. unfold t_alt3, t_alt2, t_alt. split.
    + intros [[| |] H]; tauto.
    + intros [H | [H | H]]; [exists T1 | exists T2 | exists T3]; exact H.
Qed.

(* [comment removed for export] *)
Definition fixedin_ok_vmmaps (prot : Z) (addr n : word) (h : VmMaps) : VmMaps :=
  if Z.eqb prot 0
  then mkVmMapsFull (vm_reserved h) (vm_maps h)
         ((addr, n) :: maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  else mmap_fixed_rw_next h addr n.

Definition fixedin_destroyed_vmmaps (addr n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h)
    (maps_subtract (vm_maps h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition fixedin_ok_model (prot : Z) (flags addr n : word) (m : Model) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (fixedin_ok_vmmaps prot addr n (m_vmmaps m)) m).
Definition fixedin_destroyed_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n (fixedin_destroyed_vmmaps addr n (m_vmmaps m)) m.

(* [comment removed for export] *)
Definition fixedin_ok_eff (prot : Z) (addr n : word) : SyscallEffect :=
  if Z.eqb prot 0 then mkEffectU addr [] [] [(addr, n)] [] [] else mkEffectU addr [] [(addr, n)] [] [] [].

Lemma with_mmap_replacement_halted' : forall flags a n m,
  m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
  intros. unfold with_mmap_replacement, with_mmap_backing, vm_forget_range.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.
Lemma with_mmap_destroyed_halted' : forall a n h m,
  m_halted (with_mmap_destroyed a n h m) = m_halted m.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_fixedin_check : forall ms x8 model eff (prot : Z) (flags addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  (prot = 0 \/ prot = 3)%Z ->
  mmap_flags_core flags = 50%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->   (* [comment removed for export] *)
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs us [] [] =>
        if errno_ret_in mmap_errnos r
        then match zs, us with
             | [], [] => CheckOk model []
             | [], _ => if listNN_eqb us [(addr, n)]
                        then CheckOk (fixedin_destroyed_model addr n model) []
                        else CheckReject
             | _, _ => CheckReject
             end
        else if (Z.eqb prot 0)
             then match zs with
                  | [] => if bv_eqb r addr && listNN_eqb us [(addr, n)]
                          then CheckOk (fixedin_ok_model prot flags addr n model) []
                          else CheckReject
                  | _ => CheckReject
                  end
             else match us with
                  | [] => if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                          then CheckOk (fixedin_ok_model prot flags addr n model) []
                          else CheckReject
                  | _ => CheckReject
                  end
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Htop n Hrf Hmc Hbud.
  pose proof (alloc_top_room (m_vmmaps model)) as Hcv. unfold stack_max_size, two_pow_64 in Hcv.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap, check_mmap_fixed_overflow.
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros Hz. rewrite Hz in Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hu1. lia. }
  rewrite E1, H2, H3, H5, H0, Hu1.
  destruct (mmap_gates_core50 flags (Z_to_bv 64 prot) Hcore) as (G1 & G2 & G3 & G4 & G5).
  rewrite G1, G2, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl). cbn [negb].
  pose proof (u64_range addr) as Har.
  destruct Hprot as [-> | ->].
  - (* [comment removed for export] *)
    rewrite G3. cbv beta iota zeta.
    rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
    rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
    rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct zs; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
    reflexivity.
  - (* [comment removed for export] *)
    rewrite G4, G5. cbv beta iota zeta.
    rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
    rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
    rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
    rewrite (Hbud eq_refl).
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; reflexivity].
    destruct (errno_ret_in mmap_errnos r); [reflexivity|].
    destruct us; [|reflexivity]. rewrite andb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_fixedin_lazy : forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  (prot = 0 \/ prot = 3)%Z -> mmap_flags_core flags = 50%Z ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->   (* [comment removed for export] *)
  getr regs 12 = Z_to_bv 64 prot -> getr regs 13 = flags ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4)
                             (if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem) rom)
                       (fixedin_ok_model prot flags addr n model)) KB ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w prot flags addr len KB HF HE Hh H17 Hprot Hcore H10 Hal Hpos H11 Hlen Htop H12 H13 H14 H15 n Hrf Hmc Hbud HB.
  pose proof (alloc_top_room (m_vmmaps model)) as Hcv. unfold stack_max_size, two_pow_64 in Hcv. pose proof (u64_range addr) as Har.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hlen' : (len < 2 ^ 64)%Z) by (pose proof (page_round_up_Z_bounds len ltac:(lia)); lia).
  pose proof (fun eff => mmap_fixedin_check ms (getr regs 17) model eff prot flags addr len Hno Hprot Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13)
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)
                           Htop Hrf Hmc Hbud) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  assert (Haddr_ne : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. unfold two_pow_64.
    pose proof (page_round_up_Z_bounds len ltac:(lia)). lia. }
  pose (effs := fun _ : unit => fixedin_ok_eff prot addr n).
  pose (ms' := fun _ : unit => fixedin_ok_model prot flags addr n model).
  assert (Hp0 : Z.eqb prot 0 = true <-> prot = 0%Z) by (apply Z.eqb_eq).
  (* [comment removed for export] *)
  assert (HokS : check_syscall (sys_input segs ms (getr regs 17)) (fixedin_ok_eff prot addr n) model
                 = CheckOk (fixedin_ok_model prot flags addr n model) []).
  { unfold fixedin_ok_eff. destruct (Z.eqb prot 0) eqn:Ep; rewrite Hchk, Haddr_ne, ?Ep, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity. }
  assert (HretS : eff_ret (fixedin_ok_eff prot addr n) = addr) by (unfold fixedin_ok_eff; destruct (Z.eqb prot 0); reflexivity).
  assert (Hrb : forall r, refusal_b (sys_input segs ms (getr regs 17)) model r = errno_ret_in mmap_errnos r).
  { intros r. apply refusal_b_mmap_sys. exact Hno. }
  assert (HB0 : KB []) by (eapply srealizes_nonempty; exact HB).
  apply (srz_conseq segs scfg (mkCfg ms model) (t_alt (fun i : unit => t_emit [] KB))).
  2:{ intro tr. split; [intros [i Hi]; exact (proj1 (t_emit_nil_eq KB HB0 tr) Hi) | intros H; exists tt; exact (proj2 (t_emit_nil_eq KB HB0 tr) H)]. }
  apply (srz_node segs scfg (mkCfg ms model) unit (fun _ => []) (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))
           (fun _ => KB) tt);
    [| eapply RomBase.sys_rob_memfree; [reflexivity | rewrite Hno; exact RomBase.memfree_222] |].
  - apply (node_chk_ev_gen_noacc segs scfg ms model (getr regs 17) unit effs ms' (fun _ => []) materialize_model_accesses_nil Hh eq_refl).
    + intros []. exact HokS.
    + intros []. apply alloc_nonrefusal_step. cbv delta [effs] beta. rewrite HretS, Hrb. exact Haddr_ne.
    + intros [r ws zs us cs ci] m' evs Hc Hu.
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * (* [comment removed for export] *)
        exfalso. apply Hu. apply (alloc_refusal_unforced segs scfg Halloc ms model (getr regs 17) _ _ _ _ ltac:(rewrite Hno; reflexivity) HokS).
        -- rewrite HretS, Hrb. exact Haddr_ne.
        -- cbn [eff_ret]. rewrite Hrb. exact Er.
      * rewrite Hchk in Hc. rewrite Er in Hc.
        destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
        destruct (Z.eqb prot 0) eqn:Ep.
        -- destruct zs; [|discriminate].
           destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
           destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
           apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
           exists tt. cbv delta [effs ms'] beta. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
        -- destruct us; [|discriminate].
           destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
           destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
           apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
           exists tt. cbv delta [effs ms'] beta. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; [|discriminate]; destruct us; [discriminate|]; destruct (listNN_eqb _ _); discriminate|].
      destruct (Z.eqb prot 0); [destruct zs; [|discriminate] | destruct us; [|discriminate]];
        destruct (bv_eqb r addr && listNN_eqb _ _)%bool; discriminate.
    + (* [comment removed for export] *)
      intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r).
      * destruct zs; [|discriminate]. destruct us.
        -- injection Hc as <- <-. exact Hh.
        -- destruct (listNN_eqb _ _); [|discriminate]. injection Hc as <- <-.
           unfold fixedin_destroyed_model. rewrite with_mmap_destroyed_halted'. cbn. exact Hh.
      * destruct (Z.eqb prot 0); [destruct zs; [|discriminate] | destruct us; [|discriminate]];
          (destruct (bv_eqb r addr && listNN_eqb _ _)%bool; [|discriminate]); injection Hc as <- <-;
          unfold fixedin_ok_model; rewrite with_mmap_replacement_halted', with_vmmaps_halted; exact Hh.
    + intros []; cbv delta [effs] beta; unfold fixedin_ok_eff; destruct (Z.eqb prot 0); reflexivity.
  - intros []. cbv delta [effs ms'] beta. unfold ms, fixedin_ok_eff. destruct (Z.eqb prot 0).
    + rewrite adv_unmaps1_epend. exact HB.
    + rewrite adv_zeros1_epend. exact HB.
Qed.

End Noacc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope Z_scope.
Import AX2K AX2SK APK APSK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma is_ecall_at_sound : forall SEGS cs,
  is_ecall_at SEGS cs = true ->
  0 <= pc cs /\ pc cs + 4 < two64 /\
  exists w, fetch_word SEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true.
Proof.
  intros SEGS cs H. unfold is_ecall_at in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4].
  apply Z.leb_le in H0. apply Z.ltb_lt in H4.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hw; [|discriminate].
  repeat split; try assumption. exists w. auto.
Qed.

Lemma bv_and_255 : forall c0, 0 <= c0 < two64 ->
  bv_and (Z_to_bv 64 c0) (Z_to_bv 64 255) = Z_to_bv 64 (Z.land c0 255).
Proof.
  intros c0 Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by (unfold two64 in *; lia).
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
  symmetry. apply u64_lit. unfold two64 in *.
  pose proof (Z.mod_pos_bound c0 (2 ^ 8) ltac:(lia)). lia.
Qed.

Lemma Some_inj : forall {T : Type} (a b : T), Some a = Some b -> a = b.
Proof. intros T a b H. congruence. Qed.

Lemma v_addi_pc : forall p, 0 <= p -> p + 4 < two64 ->
  v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4).
Proof.
  intros p H0 H4. unfold v_addi. f_equal. unfold two64 in *. rewrite u64_lit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CsOk.
Variable SEGS : list Segment.
Variable scfg : SpuriousCfg.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
#[local] Notation cs_ok := (APSK.cs_ok SEGS A LIMIT SINV argH FS0).

(* [comment removed for export] *)
Lemma cs_ok_refuse : forall E cs R FULL model,
  cs_ok E cs R FULL model ->
  cs_ok E (refuse cs) (regupd R 10 (Z_to_bv 64 ENOMEM_RET)) FULL model.
Proof.
  intros E cs R FULL model HC.
  assert (HMr : Mr A argH E (refuse cs) model FULL = Mr A argH E cs model FULL) by reflexivity.
  assert (HA : allowA A E (refuse cs) = allowA A E cs) by reflexivity.
  destruct HC; constructor; unfold refuse, set_pc, set_reg, with_ss, mk_ss in *;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn s_regs s_log s_know s_pc s_next] in *;
    try assumption; try reflexivity.
  apply regs_ok_set_n; [exact co_regs0 | lia | rewrite edenot_lit; reflexivity].
Qed.

Lemma pc_refuse : forall cs, pc (refuse cs) = pc cs + 4.
Proof. reflexivity. Qed.
Lemma nxt_refuse : forall cs, nxt (refuse cs) = nxt cs.
Proof. reflexivity. Qed.
End CsOk.
End AsanNodesLibEK.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Madvise.
Module AsanNodesMadvK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Madvise.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.   (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.AllocSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.AgentNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.Scfg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.KitNodesS.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.AsanNodesLibEK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Common.Cfg Require RomBase.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Madv.
Context {fxg : PropExec.FPState}.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.

Lemma madvise_check : forall ms x8 model eff,
  bv_unsigned x8 = 233 ->
  check_syscall (sys_input segs ms x8) eff model
  = Madvise.check_madvise (ms_gpr ms 0) (ms_gpr ms 1) (int32 (ms_gpr ms 2)) eff model.
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

Lemma srz_madvise_lazy : forall regs (pc : word) mem rom model w (a : word) (len : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 233 ->
  getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z -> (len mod 4096 = 0)%Z -> (bv_unsigned a + len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 4 ->
  madvise_dontneed_ok (m_vmmaps model) a (Z_to_bv 64 len) = true ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill a (Z_to_bv 64 len) mem) rom)
                      (madvise_dontneed_next model a (Z_to_bv 64 len))) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w a len K HF HE Hh H17 H10 Hal H11 Hlen Hll Hend H12 Hok Hc.
  pose proof (u64_range a) as Hra.
  assert (Hlen' : (len < 2 ^ 64)%Z) by lia.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 233%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (unfold ms; rewrite ms_gpr_epend1, H11; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (H2 : int32 (ms_gpr ms 2) = Z_to_bv 64 4) by (unfold ms; rewrite ms_gpr_epend2, H12; vm_compute; reflexivity).
  assert (Hpr : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia | exact Hll]).
  assert (Hchk : forall eff, check_syscall (sys_input segs ms (getr regs 17)) eff model
                 = match eff with
                   | mkEffectU r [] zs [] [] [] =>
                       if (w_is0 r && listNN_eqb zs [(a, Z_to_bv 64 len)])%bool
                       then CheckOk (madvise_dontneed_next model a (Z_to_bv 64 len)) [] else CheckReject
                   | _ => CheckReject
                   end).
  { intros eff. rewrite (madvise_check ms (getr regs 17) model eff Hno). unfold Madvise.check_madvise.
    rewrite H0, H2, Hu1, Hpr.
    replace (bv_unsigned a mod page_size =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact Hal).
    cbn [negb]. change (madvise_dontneed_b (Z_to_bv 64 4)) with true. cbn [negb].
    replace (w_is0 (ms_gpr ms 1)) with false.
    2:{ symmetry. unfold w_is0. apply bv_eqb_neq. intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
    replace (two_pow_64 <=? bv_unsigned a + len)%Z with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
    rewrite Hok. reflexivity. }
  eapply (srz_det_noacc segs scfg ms model (getr regs 17)
            (mkEffectU (Z_to_bv 64 0) [] [(a, Z_to_bv 64 len)] [] [] [])
            (madvise_dontneed_next model a (Z_to_bv 64 len)));
    [exact Hh | reflexivity | rewrite Hno; reflexivity
    | exact (RomBase.sys_rob_memfree segs ms model (getr regs 17) eq_refl ltac:(rewrite Hno; exact RomBase.memfree_233))
    | | | | reflexivity |].
  - intros eff m' evs. split.
    + intros Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (w_is0 r) eqn:E0; [|discriminate].
      destruct (listNN_eqb zs [(a, Z_to_bv 64 len)]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst zs. cbn [andb] in Hck. injection Hck as <- <-.
      unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r. repeat split; reflexivity.
    + intros (-> & -> & ->). rewrite Hchk. unfold w_is0. rewrite bv_eqb_refl.
      rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - intros eff Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
    destruct ws; [|discriminate]. destruct us; [destruct cs; [destruct ci; [|discriminate]|discriminate]|discriminate].
    destruct (w_is0 r && listNN_eqb zs _)%bool; discriminate.
  - exact Hh.
  - unfold ms. rewrite adv_zeros1_epend. exact Hc.
Qed.
End Madv.
End AsanNodesMadvK.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mprotect. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module AsanNodesMmLibK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BackingAlgebra. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.AgentNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.AllocSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.AsanPlacement OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BackingAlgebra OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.NoReserveK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.Scfg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.KitNodesS.   (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.AsanCeil.  (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_AsanNodesMmLibK () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List:fold_rightC46Stdlib5Lists4List7existsbC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appc59OSSVerify5KrLib7Mh_01099KitNodesS?node_chk_ev_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg7node_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099KitNodesSEnode_chk_ev_gen_noaccC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00c59OSSVerify5KrLib7Mh_0109>AsanNodesLibEKAnode_chk_ev_noaccC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109>AsanNodesLibEK>node_chk_noaccC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109>AsanNodesLibEK9srz_casesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg5t_altC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg8srz_nodeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg8wr_indexC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlgFnode_ok_of_pnode_sysnoC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5Nodes6open_IC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg@node_ok_of_pnodeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib7Mh_0109>AsanNodesLibEK8Some_injC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes5tid_IC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:concat_mapC46Stdlib5Lists4List7map_mapC46Stdlib5Lists4List9fold_leftK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbK47Corelib4Init5Logic2eq01C59OSSVerify5KrLib>AsanPlanSoundK4APSK6in_ivsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra7coveredC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00C47Corelib4Init9Datatypes3orbC46Stdlib5Lists4List;existsb_appC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C47Corelib4Init5Logic3iffI47Corelib4Init5Logic3and00C46Stdlib5Lists4List>existsb_existsC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init9Datatypes?andb_true_introK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C47Corelib7Classes?RelationClasses>iff_TransitiveI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205C47Corelib4Init5Logic3notc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<in_ivs_true'C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib>AsanPlanSoundK4APSK9sum_sizesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesK47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib7Mh_00948RefNodes>live_bytes_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK>sum_sizes_liveC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;region_freec59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<in_ivs_falseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes>region_free_InC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool:andb_assocC4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasC49OSSVerify5KrLib>BackingAlgebra<model_ivs_wfC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebraCvm_backing_used_semC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC49OSSVerify5KrLib>BackingAlgebra9sum_countC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib7Mh_00368AsanAcct:eager_usedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctEvm_backing_used_splitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr05I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeK46Stdlib9micromega=RingMicromega3Op201I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct4A_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct7A_bytesC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib7Mh_00368AsanAcct=page_allowedbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC59OSSVerify5KrLib7Mh_00368AsanAcctCallowed_pages_boundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKDmat_pages_le_A_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKBvm_backing_used_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct;minv_budgetC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC49OSSVerify5KrLib>BackingAlgebra>sum_count_monoC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra5iv_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;iv_subtractC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC46Stdlib5Lists4List:in_app_iffC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8max_specC49OSSVerify5KrLib>BackingAlgebra6ivs_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC49OSSVerify5KrLib>BackingAlgebra?ivs_wf_cons_invC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKBiv_subtract_piecesC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC56Stdlib6ZArith6BinInt1Z5min_lC56Stdlib6ZArith6BinInt1Z5max_lc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKDiv_subtract_disjointC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKCpage_in_ranges_trueC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC56Stdlib6ZArith6BinInt1Z8leb_specC46Stdlib4Bool4Bool;orb_false_rc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKBpage_in_ranges_appC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKCpage_in_ranges_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKEpage_in_ranges_coversC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK>in_ivs_coveredC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebraAmaps_subtract_semC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra6in_rngC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z6leb_gtC56Stdlib6ZArith6BinInt1Z6ltb_geC46Stdlib4Bool4Bool<orb_true_iffC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_mulC4ELinuxProcessSemantics?LinuxProcessSem5State9page_basec59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK?page_base_factsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib7Mh_00387MmapSim5zfillC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim6unfillC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;is_ecall_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK2pcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5two64C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3acs00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7page_upC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC49OSSVerify5KrLib:AxSymRun3K9env_agreeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K2evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K2ebC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_leI69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3env00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK4ext1C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat8eqb_specC56Stdlib5Arith8PeanoNat3Nat3eqbI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:sr_vars_ltC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr01C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<expr_vars_ltC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat5Nat2Z8inj_succI69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK5elenZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K9aluop_eqbC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5aluop00C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K9mulop_eqbC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5mulop00C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_reflC56Stdlib5Arith8PeanoNat3Nat8eqb_reflK69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K8expr_eqbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK>aluop_eqb_reflC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK>mulop_eqb_reflC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr06C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool3eqbC46Stdlib4Bool4Bool9eqb_reflxK69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K8expr_indC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8amap_eqbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9mkind_eqbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK=expr_eqb_reflC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4amap01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7am_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6am_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7am_kindC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4amap00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib>AsanPlanSoundK4APSK4seps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterC59OSSVerify5KrLib>AsanPlanSoundK4APSK;iv_disjointC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List9filter_InC47Corelib4Init5Logic5proj1K59OSSVerify5KrLib>AsanPlanSoundK4APSK4seps02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8seps_indC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib>AsanPlanSoundK4APSK4seps01C1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<A_bytes_app'C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<flat_map_appC47Corelib7Classes?RelationClasses?Equivalence_PERc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKFA_bytes_flat_map_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;in_flat_mapC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib7Classes?RelationClasses?iff_equivalencec59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKAin_flat_map_splitC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra1BC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra1SC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra8iv_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC49OSSVerify5KrLib>BackingAlgebra6zcountC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra7S_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith4Znat5Z2Nat2idC49OSSVerify5KrLib>BackingAlgebra:zcount_extC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra=zcount_nonnegC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC46Stdlib9micromega8ZifyInst7Inj_Z_Zc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK>filter_map_extC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_flags_coreC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAwith_mmap_backingC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>mmap_modeled_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_noaccess_bC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9PROT_READC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi:PROT_WRITEC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi;MAP_PRIVATEC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi=MAP_ANONYMOUSC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9PROT_NONEC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEmmap_fixed_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_fixed_rw_bC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9MAP_FIXEDC46Stdlib4Bool4BoolBnot_true_iff_falseC46Stdlib4Bool4Bool=andb_true_iffC4ELinuxProcessSemantics?LinuxProcessSem5State>region_free_InC4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_errnosC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8Mprotect?mprotect_errnosC45stdpp9bitvector;definitions5bv_eqC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retI47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0094:AgentNodes5ependC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics5Riscv3Sem4core00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC59OSSVerify5KrLib7Mh_00368AsanAcctNmaterialize_model_accesses_nilC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedC4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specK4ELinuxProcessSemantics?LinuxProcessSem5State5event03K4ELinuxProcessSemantics?LinuxProcessSem5State5event04K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C59OSSVerify5KrLib7Mh_00368ShapeAlgFnode_ok_of_pnode_instrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcI4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKCstepacc_ecall_ependC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK@node_instr_noaccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg;srz_silent1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprC59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlgBsrealizes_nonemptyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg=t_emit_nil_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg:srz_conseqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9srz_node1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6in_argC4ELinuxProcessSemantics?LinuxProcessSem3Run=brk_refusal_bC4ELinuxProcessSemantics?LinuxProcessSem3Run<injected_armC4ELinuxProcessSemantics?LinuxProcessSem3Run9ia_errnosC4ELinuxProcessSemantics?LinuxProcessSem3Run=ret_in_errnosC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<errno_ret_inC4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoC4ELinuxProcessSemantics?LinuxProcessSem3Run9refusal_bI4ELinuxProcessSemantics?LinuxProcessSem3Run;InjectedArm00c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKAmmap_gates_core34C1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecs=check_syscallK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01c59OSSVerify5KrLib7Mh_01099KitNodesS?grant_ok_na_pinC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okC59OSSVerify5KrLib7Mh_00387MmapSim:mmap_modelC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap:check_mmapC49OSSVerify5KrLib8PropExec:bv_eqb_neqC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_off_aligned_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_pglen_ok_bC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_anon_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAmmap_plain_anon_bC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:listNN_eqbC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_fixed_destroyed_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCwith_mmap_destroyedC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapMmmap_fixed_noaccess_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapLmmap_fixed_rw_span_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_noreplace_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCmmap_noreplace_rw_bC46Stdlib4Bool4Bool;andb_true_rC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z7testbitC59OSSVerify5KrLib7Mh_00238AsanCeilCmmap_anon_b_of_coreC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes:mmap_checkC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEwith_mmap_replacementI6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02C4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C4ELinuxProcessSemantics?LinuxProcessSem5State6EEXISTC59OSSVerify5KrLib7Mh_00238AsanCeilDmmap_off_aligned_b_0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9epend_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend5C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK=mmap_rw_checkC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4MmapFpage_round_up_Z_nonnegI47Corelib4Init6Specif3sig00K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude=listNN_eqb_eqc59OSSVerify5KrLib7Mh_01099KitNodesSFgrant_na_pin_not_errnoC1?~~~~~~~~~~~~~~~K47Corelib4Init6Specif3sig01c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKDrefusal_b_mmap_ependC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retc59OSSVerify5KrLib7Mh_01099KitNodesSEalloc_nonrefusal_stepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099KitNodesS@alloc_mm_sysno_bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099KitNodesSFalloc_refusal_unforcedC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos4landC56Stdlib6ZArith6BinInt1Z4of_NC57Corelib7BinNums6PosDef3Pos6pred_NC57Corelib7BinNums6NatDef1N5ldiffC57Corelib7BinNums6NatDef1N3lorC57Corelib7BinNums6NatDef1N8succ_posC57Corelib7BinNums6PosDef3Pos3eqbC59OSSVerify5KrLib7Mh_00388AllocSimBwith_vmmaps_haltedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKHwith_mmap_backing_haltedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes@adv_zeros1_ependC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<srz_sys_lazyC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap=MAP_NORESERVEC59OSSVerify5KrLib7Mh_00948RefNodes>noaccess_modelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK?mmap_none_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodesAadv_unmaps1_ependC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeil:init_sp_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00388AllocSimFpage_round_up_Z_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeilGalloc_top_ge_of_ceilingC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib7Mh_00238AsanCeil=alloc_ceilingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeilAalloc_ceiling_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKDmmap_fixed_gate_openC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKAmmap_gates_core50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes?region_free_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKHregion_free_not_containsC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys4UapiCMAP_FIXED_NOREPLACEc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKDmmap_gates_noreplaceC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeBerrno_ret_in_belowC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK>asanreflect_fxC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_budget_okC59OSSVerify5KrLib7Mh_00948RefNodes>mprotect_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes>mprotect_checkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKHrefusal_b_mprotect_ependC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdK4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK?fixed_free_coreC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKHmmap_fixed_rw_free_checkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKLmmap_noreplace_rw_free_checkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKGsrz_mmap_fixed_rw_free1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKJmmap_fixed_none_free_checkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKNmmap_noreplace_none_free_checkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKIsrz_mmap_fixed_none_free1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKBmmap_flags_core_32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKDmmap_flags_core_4032C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKFmmap_flags_core_104022C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKFmmap_flags_core_104032C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5max_rC56Stdlib6ZArith6BinInt1Z5min_rC46Stdlib5Lists4List6concatC46Stdlib5Lists4List<flat_map_extC46Stdlib5Lists4ListCflat_map_concat_mapC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK=replace_entryC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKAmap_replace_entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK;amap_eqb_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK=amap_eqb_reflC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_appK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK@seps_iv_subtractC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKDmaps_subtract_piecesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK>seps_app_introC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;le_gt_casesC46Stdlib5Lists4List?Forall_cons_iffc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKBiv_subtract_boundsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebraDlive_bytes_sum_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0037=AsanPlacement<ledger_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6is_fogC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK:maps_matchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8amap_denC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK2uEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK6is_fogC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK8amap_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK=maps_match_InC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKBmaps_match_app_pcsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKImaps_subtract_disjoint_idC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKCreplace_entry_notinC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib>AsanPlanSoundK4APSK5cs_ok00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8mmap_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_knowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK2MrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK2knC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7know_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5n_resC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<mmap_len_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;mmap_len_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7reg_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3xloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3xhiC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC56Stdlib6ZArith6BinInt1Z<pos_div_euclC56Stdlib6ZArith6BinInt1Z3oppC57Corelib7BinNums6PosDef3Pos3mulC59OSSVerify5KrLib7Mh_00238AsanCeilHpage_round_up_Z_aligned'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK:page_up_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9xlo_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9xhi_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK<ealign_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6ealignC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1Z9mul_assocC56Stdlib5omega8PreOmega1Z:divide_altC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3KHIC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K9sym_state00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK8some_injC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4CEILC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5FLOORC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeil>bottomup_floorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeilBbottomup_floor_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib7Mh_00948RefNodesAregion_free_introC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7vis_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;vis_add_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:vis_add_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K9split_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9shadow_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6flat_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3nxtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K>ranges_apart_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_ghostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8a_abytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8vis_costC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6a_mapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_totszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_yloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_brkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4a_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8a_tidsetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_hnaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_hlzC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3acs01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<shadow_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK?find_containingC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;shadow_bandC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5saddr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4a_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mk_ssC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8in_allowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK5sh_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK5sh_hiC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityi59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK:grant_post00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7in_hullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK4utopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9kind_noneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9kind_lazyC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_modc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKHpage_of_byte_out_alignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKGpage_in_ranges_cons_outC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK;in_ivs_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<in_allow_extC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK7gp_lazyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK8gp_noaccC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK7gp_mapsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK3visC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra;ivs_wf_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6gp_ispC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK8grant_wfC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra;covered_appC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra5in_ivC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool:orb_true_rc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKKsum_count_negb_covered_monoC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>negb_false_iffC46Stdlib4Bool4Bool8orb_propC49OSSVerify5KrLib>BackingAlgebra<zcount_falseC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra=zcount_le_lenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK>eager_used_semC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK?region_free_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK:maps_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;inside_mapsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK=xinside_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5a_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK6estartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K7xinsideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9isp_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8pagedownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK;utop_boundsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7mod_addC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_lit64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_add64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK:edenot_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5mkAluC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK;mkAlu_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5e_sp0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6e_sppgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5e_topC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7lit_ivsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076<PlaceLemmasK:lit_ivs_InC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK7am_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK6am_lenC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK4amap00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076<PlaceLemmasK4runsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK7lit_ivsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK=lit_ivs_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076<PlaceLemmasK:runs_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;inside_runsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K:base_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK@base_range_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK@runs_apart_grantC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7iv_sortC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;iv_coalesceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:safe_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK=lin_ge0_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK6xt_denC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK7u_e_topC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKAinside_maps_apartC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKAinside_runs_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K7lin_ge0C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry01C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3lebC56Stdlib5Arith8PeanoNat3Nat6leb_lec59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK@safe_range_apartC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK;elenZ_lit''C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry09C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry0:C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK;kfoot_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<grant_keep_bC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5saddr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9kimg_clipC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK<kimg_in_hullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9kentry_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK>kimg_clip_inclC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK?kn_grant_filterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK@grant_keep_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7regs_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6sr_getC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:getr_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK?region_free_semC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8co_nasubC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega5Tauto4kind02c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9grant_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7is_holeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9add_entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6co_ispC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_mapsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKImaps_apart_of_region_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK5co_wfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK?grant_new_factsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK=vis_grant_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK3hidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7hid_extC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5s_logC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6fds_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC59OSSVerify5KrLib>AsanPlanSoundK4APSK7hole_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6allowAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8in_ghostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK3RNAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK3RLZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:kind_nonebC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3hop01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:kind_lazybC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKBkn_grant_filter_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9gp_haltedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C59OSSVerify5KrLib>AsanPlanSoundK4APSK4fds3C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC59OSSVerify5KrLib>AsanPlanSoundK4APSK4flenC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC59OSSVerify5KrLib>AsanPlanSoundK4APSK5chunkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK5gp_fsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6gp_fdsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6gp_tidC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6gp_resC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK8gp_limitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK?maps_match_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKGpage_of_byte_in_alignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKFpage_in_ranges_cons_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK=sum_sizes_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6gp_brkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK7gp_sbrkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK>grant_eager_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6gp_matC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00368AsanAcct4MInv01C1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C46Stdlib4Bool4Bool=orb_false_iffC59OSSVerify5KrLib>AsanPlanSoundK4APSK7hreplayC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib>AsanPlanSoundK4APSK5cs_ok01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;is_tok_kindC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind04C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3hop00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6sentry00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7PID_MAXC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3afd00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7fds_stdC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8fresh_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6gap_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9budget_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8no_holesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK8null_cs1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9null_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9contra_csC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9first_runC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6zcdiv'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK8null_vloC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK8null_vhiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6set_knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4eaddC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions?bv_add_unsignedC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9null_kendC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4TOPCC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_mul64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4mkMdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK:mkMd_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6escaleC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK7hull_ltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<alloc_top_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSKBle_utop_of_alignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKEgrant_ok_na_pin_partsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK7le_utopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<utop_le_TOPCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6co_resC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK@grant_hull_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_sub64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9e_stk_lenC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<kdisj_mergedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:kdisj_new1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_flat_mapC59OSSVerify5KrLib7Mh_0076<PlaceLemmasK;runs_boundsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9kdisj_newC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK@null_grant_factsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKAescale_4096_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9grant_vloC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076<PlaceLemmasK?grant_vlo_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;div_le_monoc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<null_kend_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;kdisj_fixedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK;u_e_stk_lenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK7null_kdC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK7null_kvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APKAkdisj_shadow_twinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSKEkdisj_shadow_twins_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK;null_kfactsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:e_stk_len0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK?kdisj_stk_extraC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK>null_kend_pureC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<null_kd_pureC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKFkdisj_shadow_twin_pureC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>forallb_forallc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK>mmap_len_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<ext1_agree''C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK>fresh_ok_partsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<maps_vars_ltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK=env_agree_le'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7ext1_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK?nth_sr_vars_lt'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK=edenot_agree'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK>null_kfacts_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6sr_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK7is_holeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<grant_cs1_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK=pairs_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:fd_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076<PlaceLemmasK<first_run_InC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C59OSSVerify5KrLib>AsanPlanSoundK4APSK<cs_ok_set_knC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK4flatC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib7Mh_00387StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK;vis_add_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK5in_shC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK7kmem_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK<hid_cons_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0037=AsanPlacement:gap_weightC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4succC46Stdlib5Lists4List:length_appC59OSSVerify5KrLib>AsanPlanSoundK4APSK8co_totszC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSKAmaps_match_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0037=AsanPlacement@gap_weight_sizesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0037=AsanPlacement8gw_sizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK=gap_weight_eqC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:shadow_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0037=AsanPlacementBfree_gap_of_totalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeilChint_placement_ok_bC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK7CEIL_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK8FLOOR_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_minvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8co_eagerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK9co_abytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8co_limitC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebraElazy_interior_alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7with_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:ENOMEM_RETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctJsame_but_materialized_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6refuseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9refuse_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK@errno_ret_ENOMEMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6cfg_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK?env_agree_refl'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9refuse_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9refuse_pcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9v_addi_pcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>AsanPlanSoundK>asanreflect_fxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6bv5_10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<page_alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:fixed_argsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;off_image_xC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SKDranges_apart_x_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK<flat_x_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK:u_of_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKBpage_aligned_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6no_fogC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKHreserved_free_hull_apartC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_map_iffC46Stdlib5Lists4List8map_consC69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5mkSrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSKCshadow_facts_holderC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_srl64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK;mkSrl_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK?split_lit_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6in_visC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK@fixed_args_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKAsplit_flat_estartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6unholeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8same_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK;expr_eqb_eqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9find_someC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9find_holeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK>same_val_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:with_maps0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKAmaps_match_unholeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8utop_modC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9fixed_preC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<CEIL_le_utopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKCregs_ok_regupd_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKCshadow_facts_new_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9fixed_cs1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKDregion_free_of_apartC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK?find_hole_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8co_holesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<cs_ok_unholeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6in_mapC49OSSVerify5KrLib>BackingAlgebra;overlap_sumC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebraBiv_count_in_rng_leC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebraHiv_count_in_rng_disjointC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra@overlap_sum_consC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_extC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6rekindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK9co_boundsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9sl_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSKAin_ivs_maps_matchC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK5sl_nnC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra@maps_subtract_wfC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra:ivs_wf_appC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK:slice_hyps00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK4sh_CC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK4sh_mC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK5sh_nfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK5sh_UnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6sh_posC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6sh_nalC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK5sh_alC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6sh_in1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6sh_in2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK7sh_postC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK:slice_post00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6sh_memC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9slice_memC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK4sh_FC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK5sh_nFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6sp_ispC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK7sp_lazyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK8sp_noaccC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK7sp_mapsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK7sl_lohiC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK5slarm00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra:ivs_wf_nilC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK5slarm02C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK5slarm01C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK5slarm03C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK5slarm04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKEcovered_maps_subtractC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK:in_ivs_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKKpage_in_ranges_subtract_outC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKJpage_in_ranges_subtract_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK;sl_lazy_outC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<sl_noacc_outC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK:sl_vis_outC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK:sl_lazy_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK;sl_noacc_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK:sl_in_mapsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8co_kindsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9sl_chargeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra?sum_count_or_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_sepsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKEoverlap_sum_containedC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra=sum_count_extC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebraBzcount_const_falseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6sl_wf'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6sl_hnaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6sl_hlzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKCmaps_match_disjointC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indC59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_noneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKCmaps_subtract_keepsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9sp_haltedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK5sp_fsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6sp_fdsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6sp_tidC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6sp_resC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK8sp_limitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSKAmaps_match_rekindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9in_rekindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6sp_brkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK7sp_sbrkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK6sp_matC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC46Stdlib5Lists4List<NoDup_filterc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKApage_base_alignedC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3hop02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK8sl_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9kn_unfillC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6kimg_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K8mk_sprepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK?kentry_apart_bpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK>kentry_apart_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSKBkentry_apart_bp_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9kn_rezeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK@kn_rezero_ok_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK<mkind_eqb_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKEfind_containing_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKBmap_contains_introC1?~~~~~~~~~~~~~~~".      (* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Common.Cfg Require RomBase.
Import ListNotations.
Open Scope Z_scope.

Import AX2K. Import AX2SK. Import APK. Import APSK.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RES_hull_def (SEGS : list Segment) (A : APK.atable) : Prop :=
  Forall (fun iv : word * word => img_lo A <= bv_unsigned (fst iv)
                                  /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
         (segments_reserved SEGS).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_ivs_covered : forall z l, in_ivs z l = covered l z.
Proof.
  intros z l. unfold in_ivs, covered, in_iv, in_rng, B, S. reflexivity.
Qed.

Lemma in_ivs_cons : forall z iv l,
  in_ivs z (iv :: l) = (((bv_unsigned (fst iv) <=? z) && (z <? bv_unsigned (fst iv) + bv_unsigned (snd iv))) || in_ivs z l)%bool.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h02ivh11lh21zp;1p;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0g003iR2p4p710p8P0P2p4p7210p8P0p1004FR3p4p710p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R4p1006Np4p710R5p8P4p1006jp4p710R6p8P4p1007Hp4p7210R7p8P4p1007ep4p710R4p8p1008Cp4p710R8P5p8P8P4p8p1008`p4p70R8P1p8P8P5p8P8P6p8P8P7p8P8P4p8P8p1009Np4p710p8p1009kp4p76111110p100;1p4p741110R8p8p100;np4p76111110R1P8p8p100=:p4p7210R9P5p8P9P6p8P9P7p8P9P4p8P9p100=fp4p710p8p100>mp4p76111110R9P1p8P9P8p8p100@:p4p76111110R1P9p8P1P8p8p100ADp4p741110R9p100BIp4p710R:p8P9P8p8P9p100CDp4p7511110R;p8p100DAp4p711R<P:p8P<p100E?p4p771111110p8P<P;p8p100FKp4p711R;P8p8P;p100G<p4p741110p8p100HBp4p70R;P5p8P;P6p8P;P7p8P;P4p8p100I8p4p710R;P6p8P;P7p8p100J<p4p70R7P1p8P7P9p8P7P:p8P7P8p8P3p4p7210R3P5p8P3P4p8p100K7p4p7210P4p8p100KVp4p73110P4p8p100L2p4p710P4p8P0P4p8g00LPj10Tg00M5j1>Tg00MSj13Tg00N6j22Tg00NVj1=TP2j3:Tg00O6j21Tg00O`j24Tg00P=j35Tg00PZj26Tg00Q7j27Tg00QTj28Tg00RLj29Tg00VCj2<Tg00R2j2;Tg00T`g00U>#0#0#0#0#0#0#>R2#3R4/24R0%=0g00Ucf1R09:44,12R3f2R5'4A5440,12,63,75'8f0,95'<';W1W0W2o"). Qed.

Lemma in_ivs_app : forall z l1 l2, in_ivs z (l1 ++ l2) = (in_ivs z l1 || in_ivs z l2)%bool.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h02ivh12l1h22l2h31zp;1p;2p;3p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0g003iR2p4p710p8P0P2p4p7210p8P0p1004FR3p4p710p8P0p1004cp4p7210p8P0g00V`R0p4p710R4p8p1005^p4p70R5p1006Np4p710R6p8P5p1006jp4p710R7p8P5p1007Hp4p7210R8p8P5p1007ep4p710R5p8p1008Cp4p710R9P6p8P9P5p8p1008`p4p70R9P1p8P9P6p8P9P7p8P9P8p8P9P5p8P9g009NR9p4p710p8p1009kp4p76111110p100;1p4p741110R1p8p100;np4p76111110R:P1p8p100=:p4p7210R;P6p8P;P7p8P;P8p8P;P5p8P;p100=fp4p710p8p100>mp4p76111110R;P:p8P;P1p8p100@:p4p76111110R:P;p8P:P1p8p100ADp4p741110R;p100BIp4p710R<p8P;P1p8P;p100CDp4p7511110R=p8p100DAp4p711R>P<p8P>p100E?p4p771111110p8P>P=p8p100FKp4p711R=P1p8P=p100G<p4p741110p8p100HBp4p70R=P6p8P=P7p8P=P8p8P=P5p8p100I8p4p710R=P7p8P=P8p8p100J<p4p70R8P:p8P8P;p8P8P<p8P8P1p8P3p4p7210R3P6p8P3P5p8p100K7p4p7210P5p8p100KVp4p73110P5p8p100L2p4p710P5p8P4P5p8g00LPj10Tg00M5j1@Tg00MSj14Tg00N6j23Tg00NVj1?TP2j3;Tg00O6j22Tg00O`j25Tg00P=j36Tg00PZj27Tg00Q7j28Tg00QTj29TP0j4:TP9j3>Tg00RLj21Tg00VCj2=Tg00TFj3<Tg00T`g00U>#0#0#0#0#0#0#@R9#4R0/30R2#?R5P2f0R49;00,29R3f3R6'5A6004,29,73,86'9X02f1R6P4C:g00Ucf2R3A>264'111361134'=3<eX25W1W3o"). Qed.

Lemma in_ivs_true' : forall z l, in_ivs z l = true <-> exists iv, In iv l /\ bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv).
Proof.
  intros z l. unfold in_ivs. rewrite existsb_exists. split.
  - intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. eauto.
  - intros [iv [Hin Hb]]. exists iv. split; [exact Hin|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma in_ivs_false : forall z l,
  in_ivs z l = false <-> forall iv, In iv l -> ~ (bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv)).
Proof.
  intros z l. split.
  - intros H iv Hin Hz. assert (T : in_ivs z l = true) by (apply (proj2 (in_ivs_true' z l)); eauto). congruence.
  - intros H. destruct (in_ivs z l) eqn:E; [|reflexivity]. exfalso.
    apply in_ivs_true' in E as [iv [Hin Hz]]. exact (H iv Hin Hz).
Qed.

Lemma sum_sizes_live : forall l, sum_sizes l = live_bytes l.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p'0h01lh12IHh21ah32a0h41sh51zi001bi011pp;1p;2p;3p;6p;4p;5p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0p1003iR2p4p710p8P0P2p4p7210p8P0p1004FR2p4p710p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R3p1006Np4p710R4p8P3p1006jp4p710R5p8P3p1007Hp4p7210R6p8P3g007eR3p4p710R7p8p1008Cp4p710R8P4p8P8P7p8p1008`p4p70R8P1p8P8P4p8P8P5p8P8P6p8P8P7p8P8p1009Np4p710p8p1009kp4p76111110p100;1p4p741110R8p8p100;np4p76111110R1P8p8p100=:p4p7210R9P4p8P9P5p8P9P6p8P9P7p8P9p100=fp4p710p8p100>mp4p76111110R9P1p8P9P8p8p100@:p4p76111110R1P9p8P1P8p8p100ADp4p741110R9p100BIp4p710R:p8P9P8p8P9p100CDp4p7511110R;p8p100DAp4p711R<P:p8P<p100E?p4p771111110p8P<P;p8p100FKp4p711R;P8p8P;p100G<p4p741110p8p100HBp4p70R;P4p8P;P5p8P;P6p8P;P7p8p100I8p4p710R;P5p8P;P6p8p100J<p4p70R6P1p8P6P9p8P6P:p8P6P8p8P2p4p7210R2P4p8P2P7p8p100K7p4p7210P7p8p100KVp4p73110P7p8p100L2p4p710P7p8P0P7p8g00LPj11Tg00M5j1?Tg00MSj1:Tg00N6R7j28Tg00NVj1>Tg013fj13Tg014hj10Tg00TFj32Tg00R2j27Tg00^>j19Tg015aj36Tg00O6j25Tg00PZj24TP3j6=Tg016Aj4<Tg016aj5;Tg00U>#1#1#1#1#1#1#?R3#:R0/80R2#>R4P2g00T`R8f0R6#3%0632R:X04g00n4,78%92R9#3%09528eP7P0P0f2R7f1R9562R1#3%01528\:^04P6P8%09R1f3R;,53R5/46%07,45528X581537/41,78%39P6E=P0P0P;P7C<=629R7#3%07528eX1:X04X40X20P9P6O2n2001101000121100100X32P6D;W0o"). Qed.

Lemma sum_sizes_app : forall l1 l2, sum_sizes (l1 ++ l2) = sum_sizes l1 + sum_sizes l2.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h01zh12l1h22l2p;1p;2p;3p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0p1003iR2p4p710p8P0P2p4p7210p8P0p1004FR2p4p710p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R3p1006Np4p710R4p8P3p1006jp4p710R5p8P3p1007Hp4p7210R6p8P3g007eR3p4p710R7p8p1008Cp4p710R8P4p8P8P7p8p1008`p4p70R8P1p8P8P4p8P8P5p8P8P6p8P8P7p8P8g009NR8p4p710p8p1009kp4p76111110p100;1p4p741110R1p8p100;np4p76111110R9P1p8p100=:p4p7210R:P4p8P:P5p8P:P6p8P:P7p8P:p100=fp4p710p8p100>mp4p76111110R:P9p8P:P1p8p100@:p4p76111110R9P:p8P9P1p8p100ADp4p741110R:p100BIp4p710R;p8P:P1p8P:p100CDp4p7511110R<p8p100DAp4p711R=P;p8P=p100E?p4p771111110p8P=P<p8p100FKp4p711R<P1p8P<p100G<p4p741110p8p100HBp4p70R<P4p8P<P5p8P<P6p8P<P7p8p100I8p4p710R<P5p8P<P6p8p100J<p4p70R6P9p8P6P:p8P6P;p8P6P1p8P2p4p7210R2P4p8P2P7p8p100K7p4p7210P7p8p100KVp4p73110P7p8p100L2p4p710P7p8P0P7p8g00LPj10Tg00M5j1<Tg00MSj1:Tg00N6j29Tg00NVj1;TP8j37Tg014hj11Tg013fj12Tg00PZj24Tg00TFj33Tg017Cj28Tg018Gj15TP3j66Tg00U>#0#0#0#0#0#0#<#:R3/93R3#;R8g00T`R7f1R0f0R2573R4#1f2R1#2%20R6'49372X07P7%10A7310#1R31426537X07P7%12%11/429373X071802%22%52E6P6%50E6%24%54E6X28W1o"). Qed.

(* [comment removed for export] *)
Lemma region_free_sem : forall l (lo n : word) z,
  region_free l lo n = true -> 0 < bv_unsigned n ->
  bv_unsigned lo <= z < bv_unsigned lo + bv_unsigned n -> in_ivs z l = false.
Proof.
  intros l lo n z Hrf Hn Hz. apply (proj2 (in_ivs_false z l)). intros [b s] Hin Hin2. cbn [fst snd] in Hin2.
  pose proof (region_free_In l lo n b s Hrf Hin) as Hov. lia.
Qed.

Lemma region_free_app : forall l1 l2 lo n,
  region_free (l1 ++ l2) lo n = (region_free l1 lo n && region_free l2 lo n)%bool.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p'0h02l2h12loh21nh32l1h41bi001bh52IHh61ah72a0h81lh91si011pp;1p;2p;3p;4p;6p;5p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0p1003iR2p4p710p8P0P2p4p7210p8P0p1004FR2p4p710p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R3p1006Np4p710R4p8P3p1006jp4p710R5p8P3p1007Hp4p7210R6p8P3g007eR3p4p710R7p8p1008Cp4p710R8P4p8P8P7p8p1008`p4p70R8P1p8P8P4p8P8P5p8P8P6p8P8P7p8P8g009NR8p4p710p8p1009kp4p76111110p100;1p4p741110R1p8p100;np4p76111110R9P1p8p100=:p4p7210R:P4p8P:P5p8P:P6p8P:P7p8P:p100=fp4p710p8p100>mp4p76111110R:P9p8P:P1p8p100@:p4p76111110R9P:p8P9P1p8p100ADp4p741110R:p100BIp4p710R;p8P:P1p8P:p100CDp4p7511110R<p8p100DAp4p711R=P;p8P=p100E?p4p771111110p8P=P<p8p100FKp4p711R<P1p8P<p100G<p4p741110p8p100HBp4p70R<P4p8P<P5p8P<P6p8P<P7p8p100I8p4p710R<P5p8P<P6p8p100J<p4p70R6P9p8P6P:p8P6P;p8P6P1p8P2p4p7210R2P4p8P2P7p8p100K7p4p7210P7p8p100KVp4p73110P7p8p100L2p4p710P7p8P0P7p8g00LPj12Tg00M5j1BTg00MSj1<Tg00N6R7j2;Tg00NVj1ATP8j34Tg019Rj30Tg00QTj21Tg00R2j26Tg00^>j1:Tg015aj37Tg01A?j45Tg01B8j19Tg01BVj3@TP3j68Tg016Aj4=Tg016aj5>Tg00TFj3?Tg00UcR3f1R8f0R03?p=3g00U>#2#2#2#2#2#2#B#<R2/;2R4#AR1P4f3R6f2R;544?080A0680A0;80R:'1'3^22^12^01R9X31163:%:4R<=44;?080A0<80/1:'3eX22X12X01P7P2P2f5R7f4R<574R5=44;?080A0580/1:'3^22^12^01\9^81P0P3A0<80R5/1:R=P;P8f7f6R>C5#9R?/10A07;8,1?A06;8'1R?'3X43P3P8P0P>P7C5#9R@/15/1:RA130?X43163A11@=A@@5:E8A44<;?080P6P;P8P0O3E8P2P2P>P7C==74<R<=44;?080A0<80/1:'3eX22X12X01X59X31X92X62P8P0O2n2001101010121100100X74P0D>W3o"). Qed.

(* [comment removed for export] *)
Lemma map_contains_intro : forall l (lo n : word) b s,
  In (b, s) l -> bv_unsigned b <= bv_unsigned lo -> bv_unsigned lo + bv_unsigned n <= bv_unsigned b + bv_unsigned s ->
  map_contains l lo n = true.
Proof.
  intros l lo n b s Hin H1 H2. unfold map_contains. apply existsb_exists. exists (b, s). split; [exact Hin|].
  cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma map_has_intro : forall l (lo n : word), In (lo, n) l -> map_has l lo n = true.
Proof.
  intros l lo n Hin. unfold map_has. apply existsb_exists. exists (lo, n). split; [exact Hin|].
  cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma eager_used_sem : forall m,
  model_ivs_wf m ->
  eager_used m = sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m)).
Proof.
  intros m Hwf. pose proof (vm_backing_used_sem m Hwf) as H. rewrite vm_backing_used_split in H. lia.
Qed.

Lemma mat_pages_le_A_bytes : forall A m,
  MInv A m -> A_wf A -> Z.of_nat (length (m_vm_materialized m)) * page_size <= A_bytes A.
Proof.
  intros A m [N1 N2 N3 N4 N5] Hwf. apply allowed_pages_bound; assumption.
Qed.

Lemma vm_backing_used_le : forall A m,
  MInv A m -> A_wf A -> vm_backing_used m <= eager_used m + A_bytes A.
Proof.
  intros A m HM Hwf. rewrite vm_backing_used_split. pose proof (mat_pages_le_A_bytes A m HM Hwf). lia.
Qed.

Lemma vm_backing_used_limit : forall A m,
  MInv A m -> A_wf A -> vm_backing_used m <= vm_limit (m_vmmaps m).
Proof.
  intros A m HM Hwf. pose proof (vm_backing_used_le A m HM Hwf). pose proof (minv_budget _ _ HM). lia.
Qed.

(* [comment removed for export] *)
Lemma sum_count_negb_covered_mono : forall C C' l,
  (forall x, covered C x = true -> covered C' x = true) ->
  sum_count (fun x => negb (covered C' x)) l <= sum_count (fun x => negb (covered C x)) l.
Proof.
  intros C C' l H. apply sum_count_mono. intros x Hx. apply negb_true_iff in Hx. apply negb_true_iff.
  destruct (covered C x) eqn:E; [|reflexivity]. rewrite (H x E) in Hx. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iv_subtract_pieces : forall a sz lo hi q,
  iv_wf (a, sz) -> In q (iv_subtract a sz lo hi) ->
  bv_unsigned a <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned a + bv_unsigned sz
  /\ (bv_unsigned (fst q) + bv_unsigned (snd q) <= lo \/ hi <= bv_unsigned (fst q)).
Proof.
  intros a sz lo hi q Hwf Hin. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:El; [|destruct Hin]. apply Z.ltb_lt in El.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite u64_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.

Lemma maps_subtract_pieces : forall l lo hi q,
  ivs_wf l -> In q (maps_subtract l lo hi) ->
  exists r, In r l /\ bv_unsigned (fst r) <= bv_unsigned (fst q)
            /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst r) + bv_unsigned (snd r)
            /\ (bv_unsigned (fst q) + bv_unsigned (snd q) <= lo \/ hi <= bv_unsigned (fst q)).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q Hwf Hin; [destruct Hin|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity|]. cbn [fst snd]. exact (iv_subtract_pieces a sz lo hi q Ha Hin).
  - destruct (IH lo hi q Hl Hin) as (r & Hr & H). exists r. split; [right; exact Hr | exact H].
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : forall (a sz : word) lo hi,
  lo < hi -> 0 < bv_unsigned sz -> (bv_unsigned a + bv_unsigned sz <= lo \/ hi <= bv_unsigned a) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hlh Hsz Hd. pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract.
  destruct Hd as [Hd|Hd].
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; [|exfalso; lia].
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned.
    destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [exfalso; lia | reflexivity].
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; [exfalso; lia|].
    destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er]; [|exfalso; lia].
    cbn [app]. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_keeps : forall l (b s : word) lo hi,
  lo < hi -> 0 < bv_unsigned s -> In (b, s) l ->
  (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b) ->
  In (b, s) (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros b s lo hi Hlh Hs Hin Hd; [destruct Hin|].
  cbn [maps_subtract]. apply in_app_iff. destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. left. rewrite (iv_subtract_disjoint b s lo hi Hlh Hs Hd). left. reflexivity.
  - right. apply IH; assumption.
Qed.

(* [comment removed for export] *)

Lemma page_in_ranges_cons : forall p iv l,
  page_in_ranges p (iv :: l)
  = (((bv_unsigned (fst iv) <=? bv_unsigned p) && (bv_unsigned p + page_size <=? bv_unsigned (fst iv) + bv_unsigned (snd iv)))
     || page_in_ranges p l)%bool.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h02ivh11lh21pp;1p;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0g003iR2p4p710p8P0P2p4p7210p8P0p1004FR3p4p710p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R4p1006Np4p710R5p8P4p1006jp4p710R6p8P4p1007Hp4p7210R7p8P4p1007ep4p710R4p8p1008Cp4p710R8P5p8P8P4p8p1008`p4p70R8P1p8P8P5p8P8P6p8P8P7p8P8P4p8P8p1009Np4p710p8p1009kp4p76111110p100;1p4p741110R8p8p100;np4p76111110R1P8p8p100=:p4p7210R9P5p8P9P6p8P9P7p8P9P4p8P9p100=fp4p710p8p100>mp4p76111110R9P1p8P9P8p8p100@:p4p76111110R1P9p8P1P8p8p100ADp4p741110R9p100BIp4p710R:p8P9P8p8P9p100CDp4p7511110R;p8p100DAp4p711R<P:p8P<p100E?p4p771111110p8P<P;p8p100FKp4p711R;P8p8P;p100G<p4p741110p8p100HBp4p70R;P5p8P;P6p8P;P7p8P;P4p8p100I8p4p710R;P6p8P;P7p8p100J<p4p70R7P1p8P7P9p8P7P:p8P7P8p8P3p4p7210R3P5p8P3P4p8p100K7p4p7210P4p8p100KVp4p73110P4p8p100L2p4p710P4p8P0P4p8g00LPj10Tg00M5j1=Tg00MSj15Tg00N6j24Tg00NVj1<TP2j3:Tg00O6j21Tg00O`j22Tg00PZj23Tg00P=j36Tg00QTj27Tg01\Kj28Tg00VCj29Tg00R2j2;Tg00U>#0#0#0#0#0#0#=R2#5R41444R0%<0g00Ucf1R09:44,12R3f2R5,12R8'2g01V:,38A6440,12,33'2'7f0,85'9';W1W0W2o"). Qed.

Lemma page_in_ranges_app : forall p l1 l2,
  page_in_ranges p (l1 ++ l2) = (page_in_ranges p l1 || page_in_ranges p l2)%bool.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h02l1h12l2h21ph31rp;1p;2p;3p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0g003iR2p4p710p8P0P2p4p7210p8P0p1004FR3p4p710p8P0p1004cp4p7210p8P0g00V`R0p4p710R4p8p1005^p4p70R5p1006Np4p710R6p8P5p1006jp4p710R7p8P5p1007Hp4p7210R8p8P5p1007ep4p710R5p8p1008Cp4p710R9P6p8P9P5p8p1008`p4p70R9P1p8P9P6p8P9P7p8P9P8p8P9P5p8P9g009NR9p4p710p8p1009kp4p76111110p100;1p4p741110R1p8p100;np4p76111110R:P1p8p100=:p4p7210R;P6p8P;P7p8P;P8p8P;P5p8P;p100=fp4p710p8p100>mp4p76111110R;P:p8P;P1p8p100@:p4p76111110R:P;p8P:P1p8p100ADp4p741110R;p100BIp4p710R<p8P;P1p8P;p100CDp4p7511110R=p8p100DAp4p711R>P<p8P>p100E?p4p771111110p8P>P=p8p100FKp4p711R=P1p8P=p100G<p4p741110p8p100HBp4p70R=P6p8P=P7p8P=P8p8P=P5p8p100I8p4p710R=P7p8P=P8p8p100J<p4p70R8P:p8P8P;p8P8P<p8P8P1p8P3p4p7210R3P6p8P3P5p8p100K7p4p7210P5p8p100KVp4p73110P5p8p100L2p4p710P5p8P4P5p8g00LPj10Tg00M5j1?Tg00MSj16Tg00N6j25Tg00NVj1>TP2j3;Tg00O6j21Tg00O`j23Tg00PZj24Tg00P=j37Tg00QTj28TP0j49TP9j3:Tg01\Kj22Tg00VCj2=Tg00TFj3<Tg00U>#0#0#0#0#0#0#?R9#6R01500R2#>R5P2f0R49;00,19R3f3,19R6'3g01V:,46A7004,19,43'3'8X32f1R3P4C9g00Ucf2R9A:234'212931294'=3<eX15W0W2o"). Qed.

Lemma page_in_ranges_true : forall p l,
  page_in_ranges p l = true <->
  exists iv, In iv l /\ bv_unsigned (fst iv) <= bv_unsigned p /\ bv_unsigned p + page_size <= bv_unsigned (fst iv) + bv_unsigned (snd iv).
Proof.
  intros p l. unfold page_in_ranges. rewrite existsb_exists. split.
  - intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. eauto.
  - intros (iv & Hin & H1 & H2). exists iv. split; [exact Hin|]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma page_in_ranges_false : forall p l,
  page_in_ranges p l = false <->
  forall iv, In iv l -> ~ (bv_unsigned (fst iv) <= bv_unsigned p /\ bv_unsigned p + page_size <= bv_unsigned (fst iv) + bv_unsigned (snd iv)).
Proof.
  intros p l. split.
  - intros H iv Hin Hc. assert (T : page_in_ranges p l = true) by (apply (proj2 (page_in_ranges_true p l)); exists iv; tauto). congruence.
  - intros H. destruct (page_in_ranges p l) eqn:E; [|reflexivity]. exfalso.
    apply page_in_ranges_true in E as (iv & Hin & H1 & H2). exact (H iv Hin (conj H1 H2)).
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_covers : forall p l z,
  page_in_ranges p l = true -> bv_unsigned p <= z < bv_unsigned p + page_size -> in_ivs z l = true.
Proof.
  intros p l z Hp Hz. apply page_in_ranges_true in Hp as (iv & Hin & H1 & H2).
  apply (proj2 (in_ivs_true' z l)). exists iv. split; [exact Hin | lia].
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_subtract_out : forall (p : word) l lo hi,
  ivs_wf l -> lo <= hi ->
  (bv_unsigned p + page_size <= lo \/ hi <= bv_unsigned p) ->
  page_in_ranges p (maps_subtract l lo hi) = page_in_ranges p l.
Proof.
  intros p l lo hi Hwf Hlh Hout. pose proof (u64_range p) as Rp. unfold page_size in *.
  induction l as [|[a sz] l IH]; [reflexivity|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract]. rewrite page_in_ranges_app, page_in_ranges_cons, (IH Hl). f_equal.
  cbn [fst snd]. unfold iv_wf, B, S in Ha. cbn [fst snd] in Ha.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract. rewrite page_in_ranges_app.
  destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er];
    cbn [page_in_ranges existsb fst snd app orb]; unfold page_size; rewrite ?u64_lit by lia; rewrite ?orb_false_r.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout].
    + destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
    + destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_subtract_in : forall (p : word) l lo hi,
  ivs_wf l -> lo <= bv_unsigned p < hi ->
  page_in_ranges p (maps_subtract l lo hi) = false.
Proof.
  intros p l lo hi Hwf Hp. pose proof (u64_range p) as Rp.
  destruct (page_in_ranges p (maps_subtract l lo hi)) eqn:E; [|reflexivity]. exfalso.
  pose proof (page_in_ranges_covers p _ (bv_unsigned p) E ltac:(unfold page_size; lia)) as C.
  rewrite in_ivs_covered in C.
  destruct (maps_subtract_sem l lo hi Hwf ltac:(lia)) as (_ & _ & Cv). rewrite Cv in C.
  apply andb_prop in C as [_ C]. apply negb_true_iff in C. unfold in_rng in C.
  apply andb_false_iff in C as [C|C]; [apply Z.leb_gt in C | apply Z.ltb_ge in C]; lia.
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_cons_in : forall (p a n : word) l,
  bv_unsigned a <= bv_unsigned p -> bv_unsigned p + page_size <= bv_unsigned a + bv_unsigned n ->
  page_in_ranges p ((a, n) :: l) = true.
Proof.
  intros p a n l H1 H2. rewrite page_in_ranges_cons. cbn [fst snd]. apply orb_true_iff. left.
  apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma page_in_ranges_cons_out : forall (p a n : word) l,
  (bv_unsigned p + page_size <= bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned p) ->
  0 < bv_unsigned n ->
  page_in_ranges p ((a, n) :: l) = page_in_ranges p l.
Proof.
  intros p a n l H Hn. rewrite page_in_ranges_cons. cbn [fst snd]. unfold page_size in *.
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned n)); cbn; try reflexivity. exfalso. lia.
Qed.

(* [comment removed for export] *)
Lemma page_base_facts : forall a : word,
  bv_unsigned (page_base a) <= bv_unsigned a /\ bv_unsigned a < bv_unsigned (page_base a) + 4096
  /\ bv_unsigned (page_base a) mod 4096 = 0.
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
  rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma page_of_byte_in_aligned : forall (x : word) lo hi,
  lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= bv_unsigned x < hi ->
  lo <= bv_unsigned (page_base x) /\ bv_unsigned (page_base x) + 4096 <= hi.
Proof.
  intros x lo hi Hlo Hhi Hx. pose proof (page_base_facts x) as (P1 & P2 & P3).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma page_of_byte_out_aligned : forall (x : word) lo hi,
  lo mod 4096 = 0 -> hi mod 4096 = 0 -> (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
  bv_unsigned (page_base x) + 4096 <= lo \/ hi <= bv_unsigned (page_base x).
Proof.
  intros x lo hi Hlo Hhi Hx. pose proof (page_base_facts x) as (P1 & P2 & P3).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zfill_in : forall (a n : word) m (x : word),
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> zfill a n m x = Some (Z_to_bv 8 0).
Proof.
  intros a n m x Hx. unfold zfill, zmem.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma unfill_in : forall (a n : word) m (x : word),
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> unfill a n m x = None.
Proof.
  intros a n m x Hx. unfold unfill.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma mrestrict_at : forall (H : word -> bool) M (x : word),
  mrestrict H M x = if H x then None else M x.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h01Hh11Mh21xp;1p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0p1003iR2p4p710p8P0P2p4p7210p8P0p1004FR2p4p710p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R3p1006Np4p710R4p8P3p1006jp4p710R5p8P3p1007Hp4p7210R6p8P3p1007ep4p710R3p8p1008Cp4p710R7P4p8P7P3p8p1008`p4p70R7P1p8P7P4p8P7P5p8P7P6p8P7P3p8P7p1009Np4p710p8p1009kp4p76111110p100;1p4p741110R7p8p100;np4p76111110R1P7p8p100=:p4p7210R8P4p8P8P5p8P8P6p8P8P3p8P8p100=fp4p710p8p100>mp4p76111110R8P1p8P8P7p8p100@:p4p76111110R1P8p8P1P7p8p100ADp4p741110R8p100BIp4p710R9p8P8P7p8P8p100CDp4p7511110R:p8p100DAp4p711R;P9p8P;p100E?p4p771111110p8P;P:p8p100FKp4p711R:P7p8P:p100G<p4p741110p8p100HBp4p70R:P4p8P:P5p8P:P6p8P:P3p8p100I8p4p710R:P5p8P:P6p8p100J<p4p70R6P1p8P6P8p8P6P9p8P6P7p8P2p4p7210R2P4p8P2P3p8p100K7p4p7210P3p8p100KVp4p73110P3p8p100L2p4p710P3p8P0P3p8g00LPj10Tg00M5j12Tg00MSj11Tg02NOj13Tg00bOj15Tg00R2j24Tg00U>#0#0#0R3#0#0#0#2#1R0g00UcR2[%23#1R3#3R4\0P2P4f2f0R2O1%53f1P2O1n0100000020000,44X20W1W0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_addi_pc : forall p, 0 <= p -> p + 4 < 2 ^ 64 -> v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h02Hah14__x1h22H0h32H4h47__arithh54__ffh66__sat5h76__sat6h88__varmaph95__with:1ph;1zp;1p;2p;3p;4p;7p;6p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0p1003iR2p4p710p8P0P2p4p7210p8P0p1004FR2p4p710p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R3p1006Np4p710R4p8P3p1006jp4p710R5p8P3p1007Hp4p7210R6p8P3g007eR3p4p710R7p8p1008Cp4p710R8P4p8P8P7p8p1008`p4p70R8P1p8P8P4p8P8P5p8P8P6p8P8P7p8P8p1009Np4p710p8p1009kp4p76111110p100;1p4p741110R8p8p100;np4p76111110R1P8p8p100=:p4p7210R9P4p8P9P5p8P9P6p8P9P7p8P9p100=fp4p710p8p100>mp4p76111110R9P1p8P9P8p8p100@:p4p76111110R1P9p8P1P8p8p100ADp4p741110R9p100BIp4p710R:p8P9P8p8P9p100CDp4p7511110R;p8p100DAp4p711R<P:p8P<p100E?p4p771111110p8P<P;p8p100FKp4p711R;P8p8P;p100G<p4p741110p8p100HBp4p70R;P4p8P;P5p8P;P6p8P;P7p8p100I8p4p710R;P5p8P;P6p8p100J<p4p70R6P1p8P6P9p8P6P:p8P6P8p8P2p4p7210R2P4p8P2P7p8p100K7p4p7210P7p8p100KVp4p73110P7p8p100L2p4p710P7p8P0P7p8g00LPj11Tg01g6j15Tg00PZj23Tg01gTj2VTg00\Mj22Tg00M5j1FTg00MSj1CTg01hPj24Tg00TFj36Tg00R2j2;Tg00O6j2=Tg01joj2<Tg01kWj3UTg00^>j1TTg00NVj1STg00^^j2LTg00`8j1KTg00`Vj1HTg00aAj2ETg01l^j27Tg00f5j3DTg01mAj3BTg00adj49Tg00bOj1ATg00hIj7GTg00c1j2@Tg00cSj2ITg00d?j3JTg00d^j4?Tg00Z0j2>Tg01mdj2MTP3j6NTg02QHj2OTg00[Qj2PTg00gAj7QTg00hmj8RTg00n4R3f0R7'Pp=0f1R0g00j1R2g00jPR4P4g00k0R8P7g00kPFQp=8f3R6P2P4P4P8f2R:P0P7GRp=:g00T`R9%07g00U>R1#1R;#1R5#5R<,30%5;R;%15#1#1#1R5#5R='VR>'2P9P:%F5R5#CR?137<R@,45136<,4536X;913:<,45RA,;?145:RB,=51<;=123;%0=123>[[%0;RCg012QRDAU;=0UW0%0>\D^0Cg00laRC#T%SC1L90%K9%H9RCP91E91R1179<5D9g00nRRD179;=B95R5C9,8C%A4R;PCP91793g00mMP1C9,8CR=P;PCP2P4P4P8P=P9P1PDP5C9,8CFGC:C:1@C8P7P:g00UcRCg00iQR8';1I7:=6C8dAJ930C?b5b8b9X1912@>%00%0:12:>'>[[^19P7f5P6f4O3b4b6b7,M:EN1OB<=6?AeW3W2W:o"). Qed.

Lemma is_ecall_at_sound : forall SEGS cs, is_ecall_at SEGS cs = true ->
  exists w, fetch_word SEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true /\ 0 <= pc cs /\ pc cs + 4 < 2 ^ 64.
Proof.
  intros SEGS cs H. unfold is_ecall_at in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4]. apply Z.leb_le in H0. apply Z.ltb_lt in H4.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hw; [|discriminate].
  exists w. unfold two64 in H4. auto.
Qed.

Lemma page_up_eq : forall len, page_up len = page_round_up_Z len.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with53lenp;1p;2p;3p;4p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0p1003iR2p4p710p8P0P2p4p7210p8P0p1004FR2p4p710p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R3p1006Np4p710R4p8P3p1006jp4p710R5p8P3p1007Hp4p7210R6p8P3p1007ep4p710R3p8p1008Cp4p710R7P4p8P7P3p8p1008`p4p70R7P1p8P7P4p8P7P5p8P7P6p8P7P3p8P7p1009Np4p710p8p1009kp4p76111110p100;1p4p741110R7p8p100;np4p76111110R1P7p8p100=:p4p7210R8P4p8P8P5p8P8P6p8P8P3p8P8p100=fp4p710p8p100>mp4p76111110R8P1p8P8P7p8p100@:p4p76111110R1P8p8P1P7p8p100ADp4p741110R8p100BIp4p710R9p8P8P7p8P8p100CDp4p7511110R:p8p100DAp4p711R;P9p8P;p100E?p4p771111110p8P;P:p8p100FKp4p711R:P7p8P:p100G<p4p741110p8p100HBp4p70R:P4p8P:P5p8P:P6p8P:P3p8p100I8p4p710R:P5p8P:P6p8p100J<p4p70R6P1p8P6P8p8P6P9p8P6P7p8P2p4p7210R2P4p8P2P3p8p100K7p4p7210P3p8p100KVp4p73110P3p8p100L2p4p710P3p8P0P3p8g00ePj17Tg01g6j14Tg00PZj28Tg02E?R3j2:j19Tg01OlR0j1;Tg01iSj2DTg00R2j22Tg00^>j1@Tg00NVj1?Tg00^^j2>Tg00`8j1MTg00`Vj1LTg00aAj2KTg01l^j26Tg00f5j3<Tg01l;j3JTg00adj4ITg00gAj7HTg00c1j2FTg00cSj2CTg00TFj35Tg00d?j3ETg00d^j4BTg02<Cj83Tg02YCj1GTg02ZEj1ATg00LPj1=Tf0R2#7#7p=1%=2#=p=0g00T`R4P4P4g00U>R7#7#1#1#1#1#1#4R6,82R9%07#0#0#0#0#0#4R8':R1#;1828%47R:'DR5/:8R;#;P8P8P4P4\4R<P0P0P1P;P<\4R;/20P4P4%99%95P8P8P4P<P3P3P9P512;3g00laR;#@%?;f1R;,>4%M4%L4R3g00j1g00jPR<P<g00k0R<P41K47R716465<4g01W216489<47164:5J4CIg00kPFH1F3<P2f2R<g00UcR3g00iQR:'21C2<=53:dg00n4=E4;CBb2b3b4X04A5495^04P2P;O1b1G31248R8G3G3P8G3%G2%A2554eW5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma env_agree_le' : forall b b' E E', env_agree b' E E' -> (b <= b')%nat -> env_agree b E E'.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h01nh14__x1h24__x2h34__x3h41Eh52E'h61Hh72H1h82H2h93Hleh:4Hle0h;2Hnh<3Hn0h=7__arithh>4__ffh?8__varmaph@5__withA1bhB2b'hC4cstrhD5cstr0hE5cstr1p;3p;2p;1p;4p;<p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0p1003iR2p4p710p8P0P2p4p7210p8P0p1004FR2p4p710p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R3p1006Np4p710R4p8P3p1006jp4p710R5p8P3p1007Hp4p7210R6p8P3p1007ep4p710R3p8p1008Cp4p710R7P4p8P7P3p8p1008`p4p70R7P1p8P7P4p8P7P5p8P7P6p8P7P3p8P7p1009Np4p710p8p1009kp4p76111110p100;1p4p741110R7p8p100;np4p76111110R1P7p8p100=:p4p7210R8P4p8P8P5p8P8P6p8P8P3p8P8p100=fp4p710p8p100>mp4p76111110R8P1p8P8P7p8p100@:p4p76111110R1P8p8P1P7p8p100ADp4p741110R8p100BIp4p710R9p8P8P7p8P8p100CDp4p7511110R:p8p100DAp4p711R;P9p8P;p100E?p4p771111110p8P;P:p8p100FKp4p711R:P7p8P:p100G<p4p741110p8p100HBp4p70R:P4p8P:P5p8P:P6p8P:P3p8p100I8p4p710R:P5p8P:P6p8p100J<p4p70R6P1p8P6P8p8P6P9p8P6P7p8P2p4p7210R2P4p8P2P3p8p100K7p4p7210P3p8p100KVp4p73110P3p8p100L2p4p710P3p8P0P3p8g02[Cj3ITg02\<R3j27Tg00LPj14Tg00M5j1?Tg00MSj1ETg02\Tj23Tg00TFj31Tg00NVj1BTg02]Tj12Tg02^TR0j2;Tg01OLR2j10Tg00\MR4j28Tg00R2j25Tg02^nj4GTg00[QR7j26Tg01RTj1>Tg01=3j1FTg01=Rj2<Tg01>;j3DTg01>dj2WTg00^>j1VTg015aj3UTg00^^j2ATg00_Zj4RTg00`8j1QTg00`Vj1NTg00ePj1MTg00aAj29Tg00adj4=Tg00bOj1LTg00c1j2KTg00cSj2OTg00d?j3PTg00d^j4JTg02_Uj4STg00]Ij4TTg02`@l<HTg00gAj7ZTg00hmj8YTg02`eR6g00T`R9P3P2P4g02aDf5R4f4R3f3R8f2R1f1R:f0R5M<Hp=CP6P9P0P2P7g02afP4P3P8P1P:P5M<Hp=XP:g00j1R7g00jPR2P2g00k0R0P5g00kPFZp=:P8P7P2P2P0P1P:P5GYp=@g02bHR7AI1:5g00Z01753g00U>R;#4R<#4#4R=#4#4#4#?#ER>133:138:31[^06%?=#E#B\6R=%21%2:311;43f6R??I38[P5175?13?:134:51>[^06%24%2351=f8R@f7RA';f:RB,75RCf9/3:13@:51>[^06%2A%2?51=P3P:17:B%0:R=%0BR?'8P:P=159=R>PBP?159?ECf;R?,7:%0?RB,8=R@P:P=P>P?PB159BR>ECP5CGP@f<R@/;?%0@R=/6BRDP@P=159=P?PBP>EXP8CGPD%>@g00n4R@/6=%>3%03,6@f?R=#>%0=,6@g00laR=g01@4RD#FR>#F,<91<9>1<9D5D95D9g01@S'W%V=3U%B=P91A91P:1A98CR%Q9%N9R=P9%M;,99RDg00mM199<R<C=,:=%L2R2P=P9199;R;g00nRR>PDC=,:=P2P9P;P>P<C=,:=C@C@1K=0P5P1g00UcR=g00iQR0'51O51=1=0dAP9@:CJb>b?b@X19X29X39161:18:81818[[^19^29^39P5fA#0f@#0%0AP3P4O5b=bEbDbCb:b<CSO2X;CX06P:CTW9W8W7P:P5O2n2001000000121000000W6X57W4XB6XA6o"). Qed.

Lemma env_agree_refl' : forall b E, env_agree b E E.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h01nh11Eh21bp;2p;1p;3p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0p1003iR2p4p710p8P0P2p4p7210p8P0p1004FR2p4p710p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R3p1006Np4p710R4p8P3p1006jp4p710R5p8P3p1007Hp4p7210R6p8P3p1007ep4p710R3p8p1008Cp4p710R7P4p8P7P3p8p1008`p4p70R7P1p8P7P4p8P7P5p8P7P6p8P7P3p8P7p1009Np4p710p8p1009kp4p76111110p100;1p4p741110R7p8p100;np4p76111110R1P7p8p100=:p4p7210R8P4p8P8P5p8P8P6p8P8P3p8P8p100=fp4p710p8p100>mp4p76111110R8P1p8P8P7p8p100@:p4p76111110R1P8p8P1P7p8p100ADp4p741110R8p100BIp4p710R9p8P8P7p8P8p100CDp4p7511110R:p8p100DAp4p711R;P9p8P;p100E?p4p771111110p8P;P:p8p100FKp4p711R:P7p8P:p100G<p4p741110p8p100HBp4p70R:P4p8P:P5p8P:P6p8P:P3p8p100I8p4p710R:P5p8P:P6p8p100J<p4p70R6P1p8P6P8p8P6P9p8P6P7p8P2p4p7210R2P4p8P2P3p8p100K7p4p7210P3p8p100KVp4p73110P3p8p100L2p4p710P3p8P0P3p8g02\<j29Tg00LPj10Tg00M5j13Tg00MSj11Tg02\Tj28Tg00TFj34Tg00NVj17Tg02]Tj15Tg00R2j22Tg00]Ij46Tg02`eR3g02bHf0R0f2R2'9R4g00U>#0#0#0R7#0#0#0#3#1R6f1,82R2;42[^03%37#1#7\3R7%50R0;401262V4X031270C6W1W2o"). Qed.

Lemma env_agree_trans' : forall b E1 E2 E3, env_agree b E1 E2 -> env_agree b E2 E3 -> env_agree b E1 E3.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h01nh11Hh24__x1h34__x2h41bh52A1h62A2h72B1h82B2h92E1h:2E2h;2E3h<2Hnh=3Hn0h>7__arithh?4__ffh@8__varmaphA5__withB4cstrhC5cstr0p;3p;2p;1p;4p;7p;8p;6p;<p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0p1003iR2p4p710p8P0P2p4p7210p8P0p1004FR2p4p710p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R3p1006Np4p710R4p8P3g006jR5p4p710R6p8P3p1007Hp4p7210R7p8P3g007eR3p4p710R8p8p1008Cp4p710R9P4p8P9P8p8p1008`p4p70R9P1p8P9P4p8P9P6p8P9P7p8P9P8p8P9p1009Np4p710p8p1009kp4p76111110p100;1p4p741110R9p8p100;np4p76111110R1P9p8p100=:p4p7210R:P4p8P:P6p8P:P7p8P:P8p8P:p100=fp4p710p8p100>mp4p76111110R:P1p8P:P9p8p100@:p4p76111110R1P:p8P1P9p8p100ADp4p741110R:p100BIp4p710R;p8P:P9p8P:p100CDp4p7511110R<p8p100DAp4p711R=P;p8P=p100E?p4p771111110p8P=P<p8p100FKp4p711R<P9p8P<p100G<p4p741110p8p100HBp4p70R<P4p8P<P6p8P<P7p8P<P8p8p100I8p4p710R<P6p8P<P7p8p100J<p4p70R7P1p8P7P:p8P7P;p8P7P9p8P2p4p7210R2P4p8P2P8p8p100K7p4p7210P8p8p100KVp4p73110P8p8p100L2p4p710P8p8P0P8p8g02[Cj36Tg02\<R8j25Tg00LPj14Tg00M5j1;Tg00MSj1>Tg02\Tj21Tg00TFj30Tg00NVj19Tg02]Tj12Tg01OLR0j13Tg00\MR2j28Tg00R2j27Tg02^nj4STg01RTj1=Tg00[Qj2<Tg00^>j1RTg00^^j2QTg00_<j1PTg00_Zj4MTg00`8j1LTg00`Vj1KTg00aAj2:Tg00adj4FTg00gAj7ETg00bOj1DTg00hmj8GTg00c1j2HTg00cSj2CTg00d?j3ITg00d^j4JTg02_Uj4BTP3j6ATP5j6NTg00]Ij4@Tg02`@l<OTg02`eR5g00T`R3P8P0P2g02aDf5R2f4R0f3R8f2R4f1R9f0R7M<Op=?g02bHR;A6849g00Z0R:1572g00U>R1#4R<#4#4R6#4#4#4#;#>R=1129110930[^05%;6#>#9\5R6%28%2430A6284f6R0?628[P7f7R>,5711>9110950=[^05%20R?%22506f8R@?602P:f:R:,57f9R0/1911@950=[^05%2>=06?A6:0>P7f<R>,57f;R?/1911:950=[^05%2:R:%20506f>R0,57RA1109R011>950=[^05%2>R>=06:P=f=RB/1911B490=7X4=P8P9f?R=,59RB%39RC%3=RD'8REP9PC173CP=PD173DE?RDPBPEPDP7CSPE%=4g00n4RE%34'<fARD#=%3D,<Eg00laRD#R%9DP31Q34P9%P3CM%L3%K3RDg00j1RBg00jPR=P=g00k0RCPDPBP=P=PCP31:31g00nR1:3<CFg00kPFER<%D=P<GG1HDCP7P4g00UcRCg00iQRD'71C74=0CDdAI3E9CJb?b@bAX23X3318791894[^23^33P7fC#3%32P8O3b>bCbBb=CBR8O2P0P@P9P8O2EAX<AX05P6P>%2?P:P2P7ENC@W8W6P9P7O2n2001000000121000000W1W7W5P9P7O2n2001000000121000000W1X;;X:;W9X45o"). Qed.

Lemma ext1_agree'' : forall E v a, env_agree v E (ext1 E v a).
Proof.
  intros E v a. split; [|reflexivity]. intros n Hn. cbn [ext1 ev].
  destruct (Nat.eqb_spec n v); [lia | reflexivity].
Qed.

Lemma nth_sr_vars_lt' : forall b sr r, APK.sr_vars_lt b sr = true -> (r < 32)%nat -> APK.expr_vars_lt b (nth r sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [APK.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma elenZ_lit'' : forall E z, 0 <= z < 2 ^ 64 -> elenZ E (ELit z) = z.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h02Hah14__x1h21zh31Eh42Hzh57__arithh64__ffh76__sat0h86__sat1h98__varmaph:5__witp;2p;1p;3p;4p;7p;8p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0p1003iR2p4p710p8P0P2p4p7210p8P0p1004FR2p4p710p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R3p1006Np4p710R4p8P3p1006jp4p710R5p8P3p1007Hp4p7210R6p8P3g007eR3p4p710R7p8p1008Cp4p710R8P4p8P8P7p8p1008`p4p70R8P1p8P8P4p8P8P5p8P8P6p8P8P7p8P8p1009Np4p710p8p1009kp4p76111110p100;1p4p741110R8p8p100;np4p76111110R1P8p8p100=:p4p7210R9P4p8P9P5p8P9P6p8P9P7p8P9p100=fp4p710p8p100>mp4p76111110R9P1p8P9P8p8p100@:p4p76111110R1P9p8P1P8p8p100ADp4p741110R9p100BIp4p710R:p8P9P8p8P9p100CDp4p7511110R;p8p100DAp4p711R<P:p8P<p100E?p4p771111110p8P<P;p8p100FKp4p711R;P8p8P;p100G<p4p741110p8p100HBp4p70R;P4p8P;P5p8P;P6p8P;P7p8p100I8p4p710R;P5p8P;P6p8p100J<p4p70R6P1p8P6P9p8P6P:p8P6P8p8P2p4p7210R2P4p8P2P7p8p100K7p4p7210P7p8p100KVp4p73110P7p8p100L2p4p710P7p8P0P7p8g00[Qj21Tg00LPj10Tg01g6j16Tg01gTj2>Tg00\Mj22Tg00Z0j28Tg00TFj33Tg00R2j25Tg00M5j1@Tg01hPj2?Tg00O6j2:Tg01joj2<Tg01kWj3;Tg00^>j1STg00NVj1RTg00^^j2QTg00`8j1LTg00`Vj1KTg01l^j24Tg00aAj2CTg00adj47Tg01mAj3BTg00hIj7ATg00bOj1DTg00hmj8ETg00c1j2FTg00cSj2GTg00d?j3HTg00d^j4ITg01mdj2JTP3j6=Tg02h5j1MTg02lij2NTg02mmj2OTg00gAj7PTf1R3g00j1R7g00jPR0P0g00k0R2f0R4g00kPFPp=9g02bHg00T`R8g00n4R6/14g00U>R:#0R9#6R1%09#0#0#0#0R9#6R;'>R5,24'8R<P8P3f2R=9384X281583%@9R91?93':1<1;1261116;1265[[1161R>g012QR?A;1;3UW01165\?^0>g00laR>#S%R>1Q83%L8%K8R>P7P0P0P2P>P7P0P0P2P81486g00mM1C8:R:C7,9>P8P:g00nR1481=B89C7,9>FAR1%D0P1GE1F>2P4P=g00UcR>g00iQR2'51G4==3>2dAH863CIb6b9b:X1811631235'8\<^18P4f4f3O2b5b7b8,J3E=%M3R4,N=,:9=383e1O=4=383eW4W2W3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma aluop_eqb_refl : forall o, aluop_eqb o o = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p'0h01oi001ap;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0p1003iR2p4p710p8P0P2p4p7210p8P0p1004FR2p4p710p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R3p1006Np4p710R4p8P3p1006jp4p710R5p8P3p1007Hp4p7210R6p8P3p1007ep4p710R3p8p1008Cp4p710R7P4p8P7P3p8p1008`p4p70R7P1p8P7P4p8P7P5p8P7P6p8P7P3p8P7p1009Np4p710p8p1009kp4p76111110p100;1p4p741110R7p8p100;np4p76111110R1P7p8p100=:p4p7210R8P4p8P8P5p8P8P6p8P8P3p8P8p100=fp4p710p8p100>mp4p76111110R8P1p8P8P7p8p100@:p4p76111110R1P8p8P1P7p8p100ADp4p741110R8p100BIp4p710R9p8P8P7p8P8p100CDp4p7511110R:p8p100DAp4p711R;P9p8P;p100E?p4p771111110p8P;P:p8p100FKp4p711R:P7p8P:p100G<p4p741110p8p100HBp4p70R:P4p8P:P5p8P:P6p8P:P3p8p100I8p4p710R:P5p8P:P6p8p100J<p4p70R6P1p8P6P8p8P6P9p8P6P7p8P2p4p7210R2P4p8P2P3p8p100K7p4p7210P3p8p100KVp4p73110P3p8p100L2p4p710P3p8P0P3p8g02nnj22Tg00TFj31Tg00R2j20Tg0305R3P3g00UcR3f0R0/20g00iQR231P01032R2P2P2P2P2P2P2P2P2P2n01100000:00000000000000000000W0o"). Qed.
Lemma mulop_eqb_refl : forall o, mulop_eqb o o = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p'0h01oi001mp;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0p1003iR2p4p710p8P0P2p4p7210p8P0p1004FR2p4p710p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R3p1006Np4p710R4p8P3p1006jp4p710R5p8P3p1007Hp4p7210R6p8P3p1007ep4p710R3p8p1008Cp4p710R7P4p8P7P3p8p1008`p4p70R7P1p8P7P4p8P7P5p8P7P6p8P7P3p8P7p1009Np4p710p8p1009kp4p76111110p100;1p4p741110R7p8p100;np4p76111110R1P7p8p100=:p4p7210R8P4p8P8P5p8P8P6p8P8P3p8P8p100=fp4p710p8p100>mp4p76111110R8P1p8P8P7p8p100@:p4p76111110R1P8p8P1P7p8p100ADp4p741110R8p100BIp4p710R9p8P8P7p8P8p100CDp4p7511110R:p8p100DAp4p711R;P9p8P;p100E?p4p771111110p8P;P:p8p100FKp4p711R:P7p8P:p100G<p4p741110p8p100HBp4p70R:P4p8P:P5p8P:P6p8P:P3p8p100I8p4p710R:P5p8P:P6p8p100J<p4p70R6P1p8P6P8p8P6P9p8P6P7p8P2p4p7210R2P4p8P2P3p8p100K7p4p7210P3p8p100KVp4p73110P3p8p100L2p4p710P3p8P0P3p8g030aj22Tg00TFj31Tg00R2j20Tg031hR3P3g00UcR3f0R0/20g00iQR231P01032R2P2P2P2P2P2P2P2n0110000080000000000000000W0o"). Qed.
Lemma expr_eqb_refl : forall e, expr_eqb e e = true.
Proof.
  induction e; cbn; rewrite ?aluop_eqb_refl, ?mulop_eqb_refl, ?IHe1, ?IHe2, ?IHe, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
Lemma amap_eqb_refl : forall m, amap_eqb m m = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p'0h01bh11kh21lh31mi001mi011ai027am_basei037am_kindi046am_lenp;2p;1p;6p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0p1003iR2p4p710p8P0P2p4p7210p8P0p1004FR2p4p710p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R3p1006Np4p710R4p8P3p1006jp4p710R5p8P3p1007Hp4p7210R6p8P3g007eR3p4p710R7p8p1008Cp4p710R8P4p8P8P7p8p1008`p4p70R8P1p8P8P4p8P8P5p8P8P6p8P8P7p8P8p1009Np4p710p8p1009kp4p76111110p100;1p4p741110R8p8p100;np4p76111110R1P8p8p100=:p4p7210R9P4p8P9P5p8P9P6p8P9P7p8P9p100=fp4p710p8p100>mp4p76111110R9P1p8P9P8p8p100@:p4p76111110R1P9p8P1P8p8p100ADp4p741110R9p100BIp4p710R:p8P9P8p8P9p100CDp4p7511110R;p8p100DAp4p711R<P:p8P<p100E?p4p771111110p8P<P;p8p100FKp4p711R;P8p8P;p100G<p4p741110p8p100HBp4p70R;P4p8P;P5p8P;P6p8P;P7p8p100I8p4p710R;P5p8P;P6p8p100J<p4p70R6P1p8P6P9p8P6P:p8P6P8p8P2p4p7210R2P4p8P2P7p8p100K7p4p7210P7p8p100KVp4p73110P7p8p100L2p4p710P7p8P0P7p8g03@jj26Tg035<j22Tg00QTj20Tg03Amj23Tg00R2j2<Tg03C1j15TP3j64Tg03D;j3;Tg03E<j1:Tg03F>j17Tg03G?j18Tg00TFj39Tg00UcR3f0R7g00iQR039p=1g03HAR2P21677#1P7g02keR2g03IBR4P3P0f2R8/28R6,07f1R:/3:R9'0#1X03P3P01007/09#1X03P410001377'0#1P71<30R0P0P0P0P0P0n01100000600000000000012::%5:E4P6%58E4A;8:7R6#:R0/20%76R0/20'0%86R0/30'0#1e1666#1eW1X22W0P8P:P7O3n01101000130102104103W3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma seps_filter : forall f l, seps l -> seps (List.filter f l).
Proof.
  intros f l H. induction H as [|p l Hf Hl IH]; cbn; [constructor|].
  destruct (f p); [|exact IH]. constructor; [|exact IH].
  apply Forall_forall. intros q Hq. apply filter_In in Hq as [Hq _]. exact (proj1 (Forall_forall _ _) Hf q Hq).
Qed.

Lemma sum_sizes_filter_le : forall f l, sum_sizes (List.filter f l) <= sum_sizes l.
Proof.
  intros f l. induction l as [|[b s] l IH]; cbn; [lia|]. pose proof (u64_range s). destruct (f (b, s)); cbn; lia.
Qed.

Lemma A_bytes_app' : forall l1 l2, A_bytes (l1 ++ l2) = A_bytes l1 + A_bytes l2.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h04__x1h12l1h27__arithh34__ffh48__varmaph55__with64__x2h74__x3h84__x4h94IHl1h:1ah;2l2h<1zp;2p;1p;3p;4p;6p;5p;7p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710p8P0p1002lR1p4p710p8P0P1p4p7210R1p8P0p1003Hp4p710p8P0g00P=R2p4p710p8P0P2p4p7210p8P0p1004FR3p4p710p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R4p1006Np4p710R5p8P4p1006jp4p710R6p8P4p1007Hp4p7210R7p8P4g007eR4p4p710R8p8p1008Cp4p710R9P5p8P9P8p8p1008`p4p70R9P1p8P9P5p8P9P6p8P9P7p8P9P8p8P9g009NR9p4p710p8p1009kp4p76111110p100;1p4p741110R1p8p100;np4p76111110R:P1p8p100=:p4p7210R;P5p8P;P6p8P;P7p8P;P8p8P;p100=fp4p710p8p100>mp4p76111110R;P:p8P;P1p8p100@:p4p76111110R:P;p8P:P1p8p100ADp4p741110R;p100BIp4p710R<p8P;P1p8P;p100CDp4p7511110R=p8p100DAp4p711R>P<p8P>p100E?p4p771111110p8P>P=p8p100FKp4p711R=P1p8P=p100G<p4p741110p8p100HBp4p70R=P5p8P=P6p8P=P7p8P=P8p8p100I8p4p710R=P6p8P=P7p8p100J<p4p70R7P:p8P7P;p8P7P<p8P7P1p8P3p4p7210R3P5p8P3P8p8p100K7p4p7210P8p8p100KVp4p73110P8p8p100L2p4p710P8p8P0P8p8g00N6j2PTg00NVj1>TP9j33Tg01YOj11Tg00PZj20Tg00^>j19Tg00^^j26Tg00`8j1CTg00`Vj1BTg00aAj25Tg01l^j2?Tg00f5j34Tg00adj4=Tg00c1j2OTg00R2j2NTg00cSj2MTg00TFj3:Tg00d?j3LTg00d^j4KTP2j3FTg003ij3ETg01iSj2<Tg00_<j1DTg00_Zj48Tg00LPj17Tg01l;j3GTg00ePj1HTP4j6ITg015aj3JTg016aj5ATg00gAj7@Tg00T`R4f1R2f0R93:p=2P2g00j1g00jPR8P8g00k0R8P9g00kPF@p=;1P44R0#>R3P0A3092#1%19R5%12R1'0'2X13g00laR7#9R<%>7R71642%C4R;%B4R:P4g00U>R=,54R6g01W2R>g00n4R?,?4=446C=';1O:8R8P9f2R@g00UcRAg00iQRB'N1M9@=:ABdAL4?2CKRBb3b4b5X0410?9,29^04P9P1O1b2%90R?=309#1%1?/05'2eA309@#1%1@R?,05'2P4f3R5#1RA,01AF445R1AE445RC'<RD/0910D?f4RD#1RE'0'2X<4P<P7P4P4164DP@%D4C8P21645C8P;P4%7=R;,549G46R6%H=,54R=%7;,54R;544544P>A446==44;C=,;:P8PBb3b4b5X04X64X74X841<92RB10@5'010B@/05'2^04^64^74^84P9PEP?PCP1O4b2A3025#1P9EIAJ0@2R@=305#1%1@/0A'2eW9X13X:0P2DAX;3W1o"). Qed.

Lemma A_bytes_flat_map_split : forall {T} (f : T -> list (Z * Z)) (g : T -> bool) l r,
  A_bytes (flat_map f (List.filter g l ++ (List.filter (fun x => negb (g x)) l ++ r))) = A_bytes (flat_map f (l ++ r)).
Proof.
  intros T f g l r. rewrite !flat_map_app, !A_bytes_app'. induction l as [|x l IH]; cbn; [lia|].
  destruct (g x); cbn; rewrite !A_bytes_app'; lia.
Qed.

Lemma in_flat_map_split : forall {T U} (f : T -> list U) (g : T -> bool) l r y,
  In y (flat_map f (List.filter g l ++ (List.filter (fun x => negb (g x)) l ++ r))) <-> In y (flat_map f (l ++ r)).
Proof.
  intros T U f g l r y. rewrite !in_flat_map. split.
  - intros (x & Hx & Hy). exists x. split; [|exact Hy]. apply in_app_iff in Hx as [Hx|Hx]; [apply filter_In in Hx as [Hx _]; apply in_app_iff; left; exact Hx|].
    apply in_app_iff in Hx as [Hx|Hx]; [apply filter_In in Hx as [Hx _]; apply in_app_iff; left; exact Hx|]. apply in_app_iff; right; exact Hx.
  - intros (x & Hx & Hy). exists x. split; [|exact Hy]. apply in_app_iff in Hx as [Hx|Hx].
    + destruct (g x) eqn:E; [apply in_app_iff; left; apply filter_In; auto|].
      apply in_app_iff; right. apply in_app_iff; left. apply filter_In. rewrite E. auto.
    + apply in_app_iff; right. apply in_app_iff; right. exact Hx.
Qed.

Lemma sum_count_filter_le : forall (P P' : Z -> bool) (f : word * word -> bool) l,
  (forall q, In q l -> f q = true -> forall x, B q <= x < B q + S q -> P' x = P x) ->
  sum_count P' (List.filter f l) <= sum_count P l.
Proof.
  intros P P' f l H. induction l as [|q l IH]; cbn; [lia|].
  assert (IH' := IH ltac:(intros q' Hq'; apply H; right; exact Hq')).
  destruct (f q) eqn:E; cbn; [|unfold iv_count in *; pose proof (zcount_nonneg P (B q) (Z.to_nat (S q))); lia].
  unfold iv_count in *. rewrite (zcount_ext P' P); [lia|].
  intros x Hx. apply (H q (or_introl eq_refl) E). pose proof (S_range q). rewrite Z2Nat.id in Hx by lia. lia.
Qed.

Lemma filter_map_ext : forall {T U} (h : T -> U) (f : U -> bool) (f' : T -> bool) l,
  (forall x, In x l -> f (h x) = f' x) -> List.filter f (map h l) = map h (List.filter f' l).
Proof.
  intros T U h f f' l H. induction l as [|x l IH]; cbn; [reflexivity|].
  rewrite (H x (or_introl eq_refl)). rewrite (IH ltac:(intros y Hy; apply H; right; exact Hy)).
  destruct (f' x); reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma mmap_flags_core_22 : mmap_flags_core (Z_to_bv 64 34) = 34%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p;1p;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp4p76111110p100;1p4p741110R<p8p100;np4p76111110R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp4p76111110R>P=p8P>P<p8p100@:p4p76111110R=P>p8P=P<p8p100ADp4p741110R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711R@P<p8P@p100G<p4p741110p8p100HBp4p70R@P7p8P@P8p8P@P9p8P@P6p8p100I8p4p710R@P8p8P@P9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p4p710R7p1016ap4p710R<p8P7P;p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P:p8P9P;p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P<p8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8g00LPj10Tg00ePj17Tg01g6j12Tg00R2j21Tg00M5j16Tg01hPj25Tg03dgj13Tg00TFj34Tg00T`R6g00U>#0#0#0R0#7#0#2R4'1%00#0#0#6/54#3=464do"). Qed.
Lemma mmap_flags_core_32 : mmap_flags_core (Z_to_bv 64 50) = 50%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p;1p;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp4p76111110p100;1p4p741110R<p8p100;np4p76111110R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp4p76111110R>P=p8P>P<p8p100@:p4p76111110R=P>p8P=P<p8p100ADp4p741110R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711R@P<p8P@p100G<p4p741110p8p100HBp4p70R@P7p8P@P8p8P@P9p8P@P6p8p100I8p4p710R@P8p8P@P9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p4p710R7p1016ap4p710R<p8P7P;p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P:p8P9P;p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P<p8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8g00ePj11Tg00LPj10Tg01g6j13Tg00R2j22Tg00M5j17Tg01hPj26Tg03dgj15Tg00TFj34Tg00T`R6g00U>R0#1#0#0#1#0#3R4'2%00#0#0#0#0#0#7/64#5=464do"). Qed.
Lemma mmap_flags_core_4022 : mmap_flags_core (Z_to_bv 64 16418) = 34%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p;1p;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp4p76111110p100;1p4p741110R<p8p100;np4p76111110R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp4p76111110R>P=p8P>P<p8p100@:p4p76111110R=P>p8P=P<p8p100ADp4p741110R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711R@P<p8P@p100G<p4p741110p8p100HBp4p70R@P7p8P@P8p8P@P9p8P@P6p8p100I8p4p710R@P8p8P@P9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p4p710R7p1016ap4p710R<p8P7P;p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P:p8P9P;p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P<p8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8g00LPj10Tg00ePj11Tg01g6j12Tg00R2j23Tg00M5j17Tg01hPj26Tg03dgj15Tg00TFj34Tg00T`R6g00U>#0#0#0R0#1#0#2R4'3%00#0#0R0#7%00#0#1#0#0#0#1#0#2'6#5=464do"). Qed.
Lemma mmap_flags_core_4032 : mmap_flags_core (Z_to_bv 64 16434) = 50%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p;1p;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp4p76111110p100;1p4p741110R<p8p100;np4p76111110R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp4p76111110R>P=p8P>P<p8p100@:p4p76111110R=P>p8P=P<p8p100ADp4p741110R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711R@P<p8P@p100G<p4p741110p8p100HBp4p70R@P7p8P@P8p8P@P9p8P@P6p8p100I8p4p710R@P8p8P@P9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p4p710R7p1016ap4p710R<p8P7P;p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P:p8P9P;p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P<p8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8g00ePj11Tg00LPj12Tg01g6j13Tg00R2j28Tg00M5j17Tg01hPj26Tg03dgj14Tg00TFj35Tf0#2#2p=0g00T`R6g00U>R0#1#0#1#2#3R4'8%00#0#0R0#7%00#1#1#0#1#2#3'6#4=564do"). Qed.
Lemma mmap_noreserve_b_22 : mmap_noreserve_b (Z_to_bv 64 34) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p;2p;1p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp4p76111110p100;1p4p741110R<p8p100;np4p76111110R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp4p76111110R>P=p8P>P<p8p100@:p4p76111110R=P>p8P=P<p8p100ADp4p741110R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711R@P<p8P@p100G<p4p741110p8p100HBp4p70R@P7p8P@P8p8P@P9p8P@P6p8p100I8p4p710R@P8p8P@P9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p4p710R7p1016ap4p710R<p8P7P;p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P:p8P9P;p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P<p8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8g00R2j27Tg00LPj10Tg00M5j12Tg00ePj11Tg01g6j16Tg01hPj25Tg03ekj13Tg00TFj34Tg00UcR6g0121R0'7g00U>#0#0#0R4#0#0#0#2%14#0#6'5#3=460do"). Qed.
Lemma mmap_noreserve_b_32 : mmap_noreserve_b (Z_to_bv 64 50) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p;2p;1p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp4p76111110p100;1p4p741110R<p8p100;np4p76111110R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp4p76111110R>P=p8P>P<p8p100@:p4p76111110R=P>p8P=P<p8p100ADp4p741110R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711R@P<p8P@p100G<p4p741110p8p100HBp4p70R@P7p8P@P8p8P@P9p8P@P6p8p100I8p4p710R@P8p8P@P9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p4p710R7p1016ap4p710R<p8P7P;p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P:p8P9P;p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P<p8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8g00R2j27Tg00LPj10Tg00M5j12Tg00ePj11Tg01g6j16Tg01hPj25Tg03ekj13Tg00TFj34Tg00UcR6g0121R0'7g00U>R4#0#0#0#0#0#0#2%14#0#0#1#0#6'5#3=460do"). Qed.
Lemma mmap_noreserve_b_4022 : mmap_noreserve_b (Z_to_bv 64 16418) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p;2p;1p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp4p76111110p100;1p4p741110R<p8p100;np4p76111110R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp4p76111110R>P=p8P>P<p8p100@:p4p76111110R=P>p8P=P<p8p100ADp4p741110R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711R@P<p8P@p100G<p4p741110p8p100HBp4p70R@P7p8P@P8p8P@P9p8P@P6p8p100I8p4p710R@P8p8P@P9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p4p710R7p1016ap4p710R<p8P7P;p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P:p8P9P;p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P<p8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8g00R2j28Tg00M5j13Tg00ePj12Tg00LPj11Tg01g6j17Tg01hPj26Tg03ekj14Tg00TFj35Tf0#1#1p=0g00UcR6g00iQR0'8g00U>#0#0#0R4#3%04#2#1#0#2#1#7'6#4=560do"). Qed.
Lemma mmap_noreserve_b_4032 : mmap_noreserve_b (Z_to_bv 64 16434) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p;2p;1p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp4p76111110p100;1p4p741110R<p8p100;np4p76111110R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp4p76111110R>P=p8P>P<p8p100@:p4p76111110R=P>p8P=P<p8p100ADp4p741110R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711R@P<p8P@p100G<p4p741110p8p100HBp4p70R@P7p8P@P8p8P@P9p8P@P6p8p100I8p4p710R@P8p8P@P9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p4p710R7p1016ap4p710R<p8P7P;p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P:p8P9P;p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P<p8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8g00R2j27Tg00LPj10Tg00M5j12Tg00ePj11Tg01g6j16Tg01hPj25Tg03ekj13Tg00TFj34Tg00UcR6g00iQR0'7g00U>#0#0#0#0#0#0R4#2%04#0#1#1#0#0#1#0#6'5#3=460do"). Qed.
(* [comment removed for export] *)
Lemma mmap_flags_core_104022 : mmap_flags_core (Z_to_bv 64 1064994) = 1048610%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p;1p;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp4p76111110p100;1p4p741110R<p8p100;np4p76111110R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp4p76111110R>P=p8P>P<p8p100@:p4p76111110R=P>p8P=P<p8p100ADp4p741110R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711R@P<p8P@p100G<p4p741110p8p100HBp4p70R@P7p8P@P8p8P@P9p8P@P6p8p100I8p4p710R@P8p8P@P9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p4p710R7p1016ap4p710R<p8P7P;p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P:p8P9P;p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P<p8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8g00LPj11Tg00ePj12Tg01g6j13Tg00R2j28Tg00M5j17Tg01hPj26Tg03dgj14Tg00TFj35Tf0#1#1p=0g00T`R6g00U>#1#0#0R0#1R4#0#0#0#0#2#1#0#2#1#3R2'8%74%20#0#0#0#0#2#1#0#2#1#3'6#4=562do"). Qed.
Lemma mmap_flags_core_104032 : mmap_flags_core (Z_to_bv 64 1065010) = 1048626%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p;1p;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp4p76111110p100;1p4p741110R<p8p100;np4p76111110R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp4p76111110R>P=p8P>P<p8p100@:p4p76111110R=P>p8P=P<p8p100ADp4p741110R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711R@P<p8P@p100G<p4p741110p8p100HBp4p70R@P7p8P@P8p8P@P9p8P@P6p8p100I8p4p710R@P8p8P@P9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p4p710R7p1016ap4p710R<p8P7P;p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P:p8P9P;p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P<p8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8g00LPj12Tg00ePj11Tg01g6j13Tg00R2j28Tg00M5j17Tg01hPj26Tg03dgj14Tg00TFj35Tf0#2#2p=0g00T`R6g00U>#2#0#0R0#2R4#0#0#0#0#1#1#0#1#2#3R2'8%74%10#0#0#0#0#1#1#0#1#2#3'6#4=562do"). Qed.
Lemma mmap_noreserve_b_104022 : mmap_noreserve_b (Z_to_bv 64 1064994) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p;2p;1p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp4p76111110p100;1p4p741110R<p8p100;np4p76111110R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp4p76111110R>P=p8P>P<p8p100@:p4p76111110R=P>p8P=P<p8p100ADp4p741110R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711R@P<p8P@p100G<p4p741110p8p100HBp4p70R@P7p8P@P8p8P@P9p8P@P6p8p100I8p4p710R@P8p8P@P9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p4p710R7p1016ap4p710R<p8P7P;p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P:p8P9P;p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P<p8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8g00R2j28Tg00LPj11Tg00M5j13Tg00ePj12Tg01g6j17Tg01hPj26Tg03ekj14Tg00TFj35Tf0#1#1p=0g00UcR6g00iQR0'8g00U>#1#0#0R4#1#3%24#0#0#0#0#2#1#0#2#1#7'6#4=560do"). Qed.
Lemma mmap_noreserve_b_104032 : mmap_noreserve_b (Z_to_bv 64 1065010) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p;2p;1p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp4p76111110p100;1p4p741110R<p8p100;np4p76111110R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp4p76111110R>P=p8P>P<p8p100@:p4p76111110R=P>p8P=P<p8p100ADp4p741110R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711R@P<p8P@p100G<p4p741110p8p100HBp4p70R@P7p8P@P8p8P@P9p8P@P6p8p100I8p4p710R@P8p8P@P9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p4p710R7p1016ap4p710R<p8P7P;p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P:p8P9P;p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P<p8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8g00R2j28Tg00LPj11Tg00M5j13Tg00ePj12Tg01g6j17Tg01hPj26Tg03ekj14Tg00TFj35Tf0#1#1p=0g00UcR6g00iQR0'8g00U>#1#0#0R4#1#3%24#0#0#0#0#2#2#0#2#1#7'6#4=560do"). Qed.

Lemma with_mmap_backing_plain : forall flags a n m,
  mmap_noreserve_b flags = false -> with_mmap_backing flags a n m = m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h01Hh11ah21bh35flagsh41mh51np;1p;3p;2p;6p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6g007eR6p4p710R:p8p1008Cp4p710R;P7p8P;P:p8p1008`p4p70R<P2p8P<P7p8P<P8p8P<P9p8P<P:p8P<p1009Np4p710R<p8p1009kp4p76111110p100;1p4p741110R=p8p100;np4p76111110R>P=p8p100=:p4p7210R?P7p8P?P8p8P?P9p8P?P:p8P?p100=fp4p710p8p100>mp4p76111110R?P>p8P?P=p8p100@:p4p76111110R>P?p8P>P=p8p100ADp4p741110R?p100BIp4p710R@p8P?P=p8P?p100CDp4p7511110RAp8p100DAp4p711RBP@p8PBp100E?p4p771111110p8PBPAp8p100FKp4p711RAP=p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP:p8p100I8p4p710RAP8p8PAP9p8p100J<p4p70R9P>p8P9P?p8P9P@p8P9P=p8P4p4p7210R4P7p8P4P:p8p100K7p4p7210P:p8p100KVp4p73110P:p8p103T5p4p710R7p1016ap4p710R=p8P7P<p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P;p8P9P<p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P=p8P7P0p8P4p4p7210R4P2p8P4P:p8P4P0p8p100L2p4p710P:p8P0P:p8g00LPj10Tg00M5j18Tg00MSj13Tg03ekj12Tg00TFj31Tg03g0j37Tg00R2j26TP6j64Tg03gjj45Tg00U>#0#0#0#0#0#0#8#3R6g01UDR:g00UcR0f3R4#2g0121R231P0P2P0P:f0R2f4R7f2R=774P=n0100000020000=1:=X20f1R0,6:%27P2E4P7P4P=P0C5=1:0eW0W4X56X16W3o"). Qed.

Lemma with_mmap_backing_lazy : forall flags a n m,
  mmap_noreserve_b flags = true -> with_mmap_backing flags a n m = vm_add_lazy a n m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h01Hh11ah21bh35flagsh41mh51np;1p;3p;2p;6p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6g007eR6p4p710R:p8p1008Cp4p710R;P7p8P;P:p8p1008`p4p70R<P2p8P<P7p8P<P8p8P<P9p8P<P:p8P<p1009Np4p710R<p8p1009kp4p76111110p100;1p4p741110R=p8p100;np4p76111110R>P=p8p100=:p4p7210R?P7p8P?P8p8P?P9p8P?P:p8P?p100=fp4p710p8p100>mp4p76111110R?P>p8P?P=p8p100@:p4p76111110R>P?p8P>P=p8p100ADp4p741110R?p100BIp4p710R@p8P?P=p8P?p100CDp4p7511110RAp8p100DAp4p711RBP@p8PBp100E?p4p771111110p8PBPAp8p100FKp4p711RAP=p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP:p8p100I8p4p710RAP8p8PAP9p8p100J<p4p70R9P>p8P9P?p8P9P@p8P9P=p8P4p4p7210R4P7p8P4P:p8p100K7p4p7210P:p8p100KVp4p73110P:p8p103T5p4p710R7p1016ap4p710R=p8P7P<p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P;p8P9P<p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P=p8P7P0p8P4p4p7210R4P2p8P4P:p8P4P0p8p100L2p4p710P:p8P0P:p8g00LPj10Tg00M5j18Tg00MSj14Tg03ekj12Tg00TFj31Tg03g0j33Tg00R2j27TP6j65Tg03gjj46Tg00U>#0#0#0#0#0#0#8#4R6g01UDR:g00UcR0f3R4#2g00iQR231P0P2P0P:f0R2f4R7f2R=734R3P=n0100000020000=1:3X20f1R0934=R3,7:%27P2E5P7P4P=P0C6=1:3eW0W4X56X16W3o"). Qed.

Lemma with_mmap_backing_halted : forall flags a n m,
  m_halted (with_mmap_backing flags a n m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p'0h01ah11bi001bh25flagsh31mh41np;1p;3p;2p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp4p76111110p100;1p4p741110R<p8p100;np4p76111110R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp4p76111110R>P=p8P>P<p8p100@:p4p76111110R=P>p8P=P<p8p100ADp4p741110R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711R@P<p8P@p100G<p4p741110p8p100HBp4p70R@P7p8P@P8p8P@P9p8P@P6p8p100I8p4p710R@P8p8P@P9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p4p710R7p1016ap4p710R<p8P7P;p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P:p8P9P;p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P<p8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8g00LPj10Tg00M5j19Tg00MSj14Tg03ekj13Tg02NOj18Tg03g0j37Tg03i0j11Tg00TFj32Tg00R2j25Tg03gjj46Tg00U>#0#0#0#0#0#0#9#4R6g01UDR0f3R4#3g00UcR2P2%86R7P2P0f0R0f4f2R2774P2n0100000020000#1%1232P0f1R<#1,57R3P3n0110000020000b1P4P2P<P0C6#1%10527eW3X46X06W2o"). Qed.

Lemma with_mmap_backing_fs : forall flags a n m,
  m_fs (with_mmap_backing flags a n m) = m_fs m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p'0h01ah11bi001bh25flagsh31mh41np;1p;3p;2p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8g008`R;p4p70R<P2p8P<P7p8P<P8p8P<P9p8P<P6p8P<p1009Np4p710R<p8p1009kp4p76111110p100;1p4p741110R=p8p100;np4p76111110R>P=p8p100=:p4p7210R?P7p8P?P8p8P?P9p8P?P6p8P?p100=fp4p710p8p100>mp4p76111110R?P>p8P?P=p8p100@:p4p76111110R>P?p8P>P=p8p100ADp4p741110R?p100BIp4p710R@p8P?P=p8P?p100CDp4p7511110RAp8p100DAp4p711RBP@p8PBp100E?p4p771111110p8PBPAp8p100FKp4p711RAP=p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p4p710RAP8p8PAP9p8p100J<p4p70R9P>p8P9P?p8P9P@p8P9P=p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p4p710R7p1016ap4p710R=p8P7P<p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P:p8P9P<p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P=p8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8g00LPj10Tg00M5j18Tg00MSj14Tg03ekj13Tg03g0j37Tg03igj11Tg00TFj32Tg00R2j25Tg03gjj46Tg00U>#0#0#0#0#0#0#8#4R6g01UDR0f3R4#3g00UcR2P2P2P0f0R0f4f2R2774P2n0100000020000#1%1252;P0f1R7#1,5;R=P=n0110000020000b1P4P2P7P0C6#1%1052;eW3X46X06W2o"). Qed.

Lemma with_mmap_backing_vmmaps : forall flags a n m,
  m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "p'0h01ah11bi001bh25flagsh31mh41np;1p;3p;2p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp4p76111110p100;1p4p741110R<p8p100;np4p76111110R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp4p76111110R>P=p8P>P<p8p100@:p4p76111110R=P>p8P=P<p8p100ADp4p741110R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711R@P<p8P@p100G<p4p741110p8p100HBp4p70R@P7p8P@P8p8P@P9p8P@P6p8p100I8p4p710R@P8p8P@P9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p4p710R7p1016ap4p710R<p8P7P;p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P:p8P9P;p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P<p8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8g00LPj10Tg00M5j18Tg00MSj14Tg03ekj13Tg03g0j37Tg01IPj11Tg00TFj32Tg00R2j25Tg03gjj46Tg00U>#0#0#0#0#0#0#8#4R6g01UDR0f3R4#3g00UcR2P2g03jZR7P2P0f0R0f4f2R2774P2n0100000020000#1%1232P0f1R<#1,57R3P3n0110000020000b1P4P2P<P0C6#1%10527eW3X46X06W2o"). Qed.

(* [comment removed for export] *)
Lemma mmap_gates_core34 : forall flags,
  mmap_flags_core flags = 34%Z ->
  mmap_modeled_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true
  /\ mmap_modeled_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true.
Proof.
  intros flags Hc. unfold mmap_modeled_b, mmap_noaccess_b. rewrite Hc.
  repeat split; vm_compute; reflexivity.
Qed.

Lemma mmap_gates_core50 : forall flags prot,
  mmap_flags_core flags = 50%Z ->
  mmap_modeled_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true.
Proof.
  intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b.
  rewrite Hc. repeat split; try (vm_compute; reflexivity).
  all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_not_contains : forall l (lo n : word),
  (0 < bv_unsigned n)%Z ->
  region_free l lo n = true -> map_contains l lo n = false.
Proof.
  intros l lo n Hn Hfree. unfold map_contains.
  apply Bool.not_true_iff_false. intros H. apply existsb_exists in H as ([b s] & Hin & H).
  cbn [fst snd] in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (State.region_free_In _ _ _ _ _ Hfree Hin) as Hov.
  unfold iv_overlap in Hov. apply andb_false_iff in Hov as [Hov|Hov]; apply Z.ltb_ge in Hov; lia.
Qed.

Lemma mmap_errnos_ENOMEM : forall e, In e mmap_errnos -> e = ENOMEM.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h01Hh11ep;3p;1p;2p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0g00XfR1p4p710R2p8P0p1002lR3p4p710R4p8P0P3p4p7210R3p8P0p1003Hp4p710p8P0p1003iR5p4p710p8P0P5p4p7210p8P0p1004FR5p4p710R6p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R7g006NR8p4p710R9p8P7p1006jp4p710R:p8P7p1007Hp4p7210R;p8P7p1007ep4p710R7p8p1008Cp4p710R<P9p8P<P7p8p1008`p4p70R=P3p8P=P9p8P=P:p8P=P;p8P=P7p8P=p1009Np4p710R=p8p1009kp4p76111110p100;1p4p741110R>p8p100;np4p76111110R?P>p8p100=:p4p7210R@P9p8P@P:p8P@P;p8P@P7p8P@p100=fp4p710p8p100>mp4p76111110R@P?p8P@P>p8p100@:p4p76111110R?P@p8P?P>p8p100ADp4p741110R@p100BIp4p710RAp8P@P>p8P@p100CDp4p7511110RBp8p100DAp4p711RCPAp8PCp100E?p4p771111110p8PCPBp8p100FKp4p711RBP>p8PBp100G<p4p741110p8p100HBp4p70RBP9p8PBP:p8PBP;p8PBP7p8p100I8p4p710RBP:p8PBP;p8p100J<p4p70R;P?p8P;P@p8P;PAp8P;P>p8P5p4p7210R5P9p8P5P7p8p100K7p4p7210P7p8p100KVp4p73110P7p8p103T5p4p710R9p1016ap4p710R>p8P9P=p8P9P6p8P9P0p8p103WUR9p4p710R;P2p8P;P<p8P;P=p8P;P6p8P;P0p8P9p4p7210R9P2p8P9P5p8p103c\R5p4p710R9P2p8P9P4p8P9P>p8P9P0p8P5p4p7210R5P3p8P5P7p8P5P0p8p100L2p4p710P7p8P0P7p8P1j30Tg00TFj32Tg00^>j13Tg00R2j25TP8j64Tg00T`R8f0R1g048MR732p=1g049B9081g01<Yf1R09287%38R59080f2R0#1P1A2870P8P7%11X181587f3P1E4W0P1O1A0805g012mf4#1P1n010000000W0P1O1n200100000021000010000W0X18o"). Qed.
Lemma mprotect_errnos_ENOMEM : forall e, In e mprotect_errnos -> e = ENOMEM.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h01Hh11ep;3p;1p;2p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0g00XfR1p4p710R2p8P0p1002lR3p4p710R4p8P0P3p4p7210R3p8P0p1003Hp4p710p8P0p1003iR5p4p710p8P0P5p4p7210p8P0p1004FR5p4p710R6p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R7g006NR8p4p710R9p8P7p1006jp4p710R:p8P7p1007Hp4p7210R;p8P7p1007ep4p710R7p8p1008Cp4p710R<P9p8P<P7p8p1008`p4p70R=P3p8P=P9p8P=P:p8P=P;p8P=P7p8P=p1009Np4p710R=p8p1009kp4p76111110p100;1p4p741110R>p8p100;np4p76111110R?P>p8p100=:p4p7210R@P9p8P@P:p8P@P;p8P@P7p8P@p100=fp4p710p8p100>mp4p76111110R@P?p8P@P>p8p100@:p4p76111110R?P@p8P?P>p8p100ADp4p741110R@p100BIp4p710RAp8P@P>p8P@p100CDp4p7511110RBp8p100DAp4p711RCPAp8PCp100E?p4p771111110p8PCPBp8p100FKp4p711RBP>p8PBp100G<p4p741110p8p100HBp4p70RBP9p8PBP:p8PBP;p8PBP7p8p100I8p4p710RBP:p8PBP;p8p100J<p4p70R;P?p8P;P@p8P;PAp8P;P>p8P5p4p7210R5P9p8P5P7p8p100K7p4p7210P7p8p100KVp4p73110P7p8p103T5p4p710R9p1016ap4p710R>p8P9P=p8P9P6p8P9P0p8p103WUR9p4p710R;P2p8P;P<p8P;P=p8P;P6p8P;P0p8P9p4p7210R9P2p8P9P5p8p103c\R5p4p710R9P2p8P9P4p8P9P>p8P9P0p8P5p4p7210R5P3p8P5P7p8P5P0p8p100L2p4p710P7p8P0P7p8P1j30Tg00TFj32Tg00^>j13Tg00R2j25TP8j64Tg00T`R8f0R1g048MR732p=1g04:B9081g01<Yf1R09287%38R59080f2R0#1P1A2870P8P7%11X181587f3P1E4W0P1O1A0805g012mf4#1P1n010000000W0P1O1n200100000021000010000W0X18o"). Qed.

Lemma errno_ret_ENOMEM : errno_ret ENOMEM = Z_to_bv 64 (two64 - 12).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) [] "h02b1h12b2h21nh31Hp;1p;3p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp4p76111110p100;1p4p741110R<p8p100;np4p76111110R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp4p76111110R>P=p8P>P<p8p100@:p4p76111110R=P>p8P=P<p8p100ADp4p741110R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711R@P<p8P@p100G<p4p741110p8p100HBp4p70R@P7p8P@P8p8P@P9p8P@P6p8p100I8p4p710R@P8p8P@P9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p4p710R7p1016ap4p710R<p8P7P;p8P7P5p8P7P0p8p103WUR7p4p710R9P1p8P9P:p8P9P;p8P9P5p8P9P0p8P7p4p7210R7P1p8P7P4p8p103c\R4p4p710R7P1p8P7P3p8P7P<p8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8g00MSj12Tg00TFj33Tg00O6j21Tg04;Jj34Tg00LPj10Tg00M5j1;Tg04;nj1:Tg00ePj15Tg01g6j16Tg01iSj27Tg01hPj28Tg00R2j29Tg04<fR6f0R0#2R4f1R2#2R7g00Z0f2R<#2?320g00T`R3f3R1/1<111233R9[11<211<0533%21?3<2[R5f4#2?31<\9A4<20P0n2001000000120000000W1W0W2P5^17^04^26P0g00U>R0#0#0#0#0#0#0#;R6g048M#:g02VA%50#0#0#6'7,86R01160,93O4b3o"). Qed.

Section OurSpecNodes.
Context {fxg : PropExec.FPState}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.   (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stepacc_ecall_epend : forall regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom)
  = MachineOk (@mkAccessReport machine_state (epend regs pc mem rom (getr regs 17)) []).
Proof.
  intros regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_instr_noacc : forall ms model ms',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  ShapeAlg.node_ok segs scfg (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hsvc Hstep.
  assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
  { unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }
  (* [comment removed for export] *)
  apply (node_ok_of_pnode_instr segs scfg); [exact Hsvc |].
  split.
  - intros []. apply (sstep_instr segs ms model ms' model Hh Hsvc Hacc).
  - intros e st Hss. exists tt.
    inversion Hss; subst;
      match goal with
      | H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
      | H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
      end.
Qed.

Lemma srz_sys_lazy : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  srealizes segs scfg (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply srz_silent1; [| apply RomBase.sys_rob_instr; reflexivity | exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma epend_len : forall regs pc mem rom (len : Z),
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  bv_unsigned (ms_gpr (epend regs pc mem rom (getr regs 17)) 1) = len
  /\ ms_gpr (epend regs pc mem rom (getr regs 17)) 1 <> Z_to_bv 64 0.
Proof.
  intros regs pc mem rom len H11 Hlen. rewrite ms_gpr_epend1, H11. split.
  - apply u64_lit. lia.
  - intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia.
Qed.

(* [comment removed for export] *)
Lemma srz_node1 : forall c (IB : Type) (nx : IB -> config) (B : TSet) (b0 : IB),
  ShapeAlg.node_ok segs scfg c IB (fun _ => []) nx ->
  RomBase.sys_rob segs c ->
  (forall i, srealizes segs scfg (nx i) B) ->
  srealizes segs scfg c B.
Proof.
  intros c IB nx B b0 Hnode Hrob HB.
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB b0)).
  apply (srz_conseq segs scfg c (t_alt (fun i : IB => t_emit [] B))).
  - apply (srz_node segs scfg c IB (fun _ => []) nx (fun _ => B) b0 Hnode Hrob). exact HB.
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq B HB0 tr) Hi).
    + intros H. exists b0. exact (proj2 (t_emit_nil_eq B HB0 tr) H).
Qed.

(* [comment removed for export] *)
Lemma refusal_b_mmap_epend : forall ms x8 model r, bv_unsigned x8 = 222%Z ->
  refusal_b (sys_input segs ms x8) model r = errno_ret_in mmap_errnos r.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["OurSpecNodes"] "p'0h03Hnoh15modelh22msh31rh42x8h51zi001ai011xp;1p;2p;3p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6g007eR6p4p710R:p8p1008Cp4p710R;P7p8P;P:p8p1008`p4p70R<P2p8P<P7p8P<P8p8P<P9p8P<P:p8P<p1009Np4p710R<p8p1009kp605611111000p100;1p4p741110R=p8p100;np605611111000R>P=p8p100=:p4p7210R?P7p8P?P8p8P?P9p8P?P:p8P?p100=fp4p710p8p100>mp605611111000R?P>p8P?P=p8p100@:p605611111000R>P?p8P>P=p8p100ADp6054111000R?p100BIp4p710R@p8P?P=p8P?p100CDp4p7511110RAp8p100DAp4p711RBP@p8PBp100E?p4p771111110p8PBPAp8p100FKp4p711RBP=p8PBp100G<p4p741110p8p100HBp4p70RBP7p8PBP8p8PBP9p8PBP:p8p100I8p6051000RBP8p8PBP9p8p100J<p4p70R9P>p8P9P?p8P9P@p8P9P=p8P4p4p7210R4P7p8P4P:p8p100K7p4p7210P:p8p100KVp4p73110P:p8p103T5p6051000R7p1016ap4p710R9p8P7P<p8P7P5p8P7P0p8p103WUR7p6051001R?P1p8P?P;p8P?P<p8P?P5p8P?P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7P9p8P7P0p8P4p60521000R4P2p8P4P:p8P4P0p8p100L2p4p710P:p8P0P:p8p105Eip6054111000R:P@p8P:P=p8P:PAp8g00LPj10Tg00M5j1BTg00MSj1=Tg00O6j23Tg00ePj11Tg01g6j19Tg00TFj32Tg032Tj25Tg04j;j36Tg05Foj27Tg05Gdj34Tg05H^j18Tg05IWj1<Tg05JMj2;Tg05KGj2:Tg00R2j2ATP6j6@Tg05LOj1?Tg05MFj3>Tg04^hg00U>R6#0#0#0#0#0#0#BRA#=R:g01UDg00T`R=f2R@,3A%16#0#1R6#1#1#1#0#9R032P=P0g00UcR0P0P0f0R4%06#1#1#0#9R6'5f3R2p,4segsR7f5f4R936g01@4R3'7;4@g02NOR1g05N<R?P0%84%<4R5/;2g0121R<n10110100021010000n0100000020000g049BR;/:@32X5=f1R=,:;R;,A013A2P4E@P0P0A6792R9#?,3ARA/561793=4@=P1P?P0%8A1;5@P<n10110100021010000n0100000020000=20;eA>9@==20;eW0X3:W1W4W2o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_rw_check : forall ms x8 model eff flags,
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 1 <> Z_to_bv 64 0 -> ms_gpr ms 2 = Z_to_bv 64 3 ->
  ms_gpr ms 3 = flags -> mmap_flags_core flags = 34%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (* [comment removed for export] *)
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mmap_errnos r
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        (* [comment removed for export] *)
        (* [comment removed for export] *)
        else if Placement.linux_place_is (m_vmmaps model) (kb_thp (m_kernel model)) (ms_gpr ms 0) nZ r
                && mmap_noreserve_backed_ok flags model nZ
                && listNN_eqb zs [(r, Z_to_bv 64 nZ)]
        then CheckOk (with_mmap_backing flags r (Z_to_bv 64 nZ) (mmap_model r (Z_to_bv 64 nZ) model)) []
        else CheckReject
    | _ => CheckReject
    end.
(* [comment removed for export] *)
Proof.
  intros ms x8 model eff flags Hno H1 H2 H3 Hcore H4 H5 Hdecl. cbv zeta.
  rewrite (mmap_check segs ms x8 model eff Hno).
  assert (Hoff : mmap_off_aligned_b (ms_gpr ms 5) = true) by (rewrite H5; reflexivity).
  assert (Hanon : mmap_anon_b (ms_gpr ms 3) = true)
    by (rewrite H3; exact (mmap_anon_b_of_core flags 34%Z Hcore eq_refl)).
  assert (Hl : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  assert (Hmb : mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true)
    by (rewrite H2, H3, H5; exact (proj1 (mmap_gates_core34 flags Hcore))).
  unfold check_mmap. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  (* [comment removed for export] *)
  rewrite Hdecl.
  (* [comment removed for export] *)
  rewrite H3. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma linux_place_is_of_grant_ok_na : forall hint m a n,
  OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.grant_ok_na hint m a n = true ->
  Placement.linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true.
Proof.
  intros hint m a n H. unfold OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.grant_ok_na in H.
  (* [comment removed for export] *)
  rewrite !Bool.andb_true_iff in H. destruct H as [[[[HP _] _] _] _]. exact HP.
Qed.

Lemma grant_ok_na_pin_of_grant_ok_na : forall hint m a n,
  OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.grant_ok_na hint m a n = true -> grant_ok_na_pin m a n = true.
Proof.
  (* [comment removed for export] *)
  intros hint m a n H. unfold OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.grant_ok_na in H. unfold grant_ok_na_pin.
  rewrite !Bool.andb_true_iff in H. destruct H as [[[[_ HA] HB] HC] HD].
  rewrite !Bool.andb_true_iff. repeat split; assumption.
Qed.

Lemma srz_mmap_rw1 : forall regs (pc : word) mem rom model w (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 34%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  (* [comment removed for export] *)
  place_declined_b (m_kernel model) (m_vmmaps model) (getr regs 10)
    (page_round_up_Z len) = false ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (* [comment removed for export] *)
  (exists a, OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.grant_ok_na (getr regs 10) model a nZ = true) ->
  mmap_noreserve_backed_ok flags model nZ = true ->
  (forall a, grant_ok_na_pin model a nZ = true ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom)
                          (with_mmap_backing flags a n (mmap_model a n model))) KB) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
(* [comment removed for export] *)
Proof.
  (* [comment removed for export] *)
  intros regs pc mem rom model w len flags KB HF HE Hh H17 H11 Hlen H12 H13 Hcore H14 H15 Hdecl nZ n (a0 & Ha0) Hb0 HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
  pose proof (fun eff => mmap_rw_check ms (getr regs 17) model eff flags Hno Hne1
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)
                           ltac:(rewrite Hl1; unfold ms; rewrite ms_gpr_epend0; exact Hdecl)) as Hchk.
  cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk.
  rewrite Hb0 in Hchk.
  assert (Hn0 : (0 <= nZ)%Z) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
  (* [comment removed for export] *)
  assert (HnZpos : (0 < nZ)%Z) by (unfold nZ; apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.AsanCeil.page_round_up_Z_pos'; lia).
  assert (HnZal : (nZ mod page_size = 0)%Z) by (unfold nZ; apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.AsanCeil.page_round_up_Z_aligned').
  assert (Hm0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; apply ms_gpr_epend0).
  assert (Hadm : forall r, Placement.linux_place_is (m_vmmaps model) (kb_thp (m_kernel model))
                             (ms_gpr ms 0) nZ r = true ->
                           OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.grant_ok_na (getr regs 10) model r nZ = true).
  { intros r Hpl. rewrite Hm0 in Hpl.
    pose proof (Placement.linux_place_is_admissible _ _ _ _ _ HnZpos HnZal Hpl)
      as (Hal & Hpos & Htop & Hfree).
    unfold OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.grant_ok_na. rewrite !Bool.andb_true_iff. repeat split.
    - exact Hpl.
    - apply Z.eqb_eq; exact Hal.
    - apply Z.ltb_lt; exact Hpos.
    - apply Z.leb_le; exact Htop.
    - exact Hfree. }
  (* [comment removed for export] *)
  pose (IB := {a : word | OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.grant_ok_na (getr regs 10) model a nZ = true}).
  pose (effs := fun i : IB => match i with exist _ a _ => mkEffectU a [] [(a, n)] [] [] [] end).
  pose (ms' := fun i : IB => match i with exist _ a _ => with_mmap_backing flags a n (mmap_model a n model) end).
  assert (HokS : forall a, OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.grant_ok_na (getr regs 10) model a nZ = true ->
            check_syscall (sys_input segs ms (getr regs 17)) (mkEffectU a [] [(a, n)] [] [] []) model
            = CheckOk (with_mmap_backing flags a n (mmap_model a n model)) []).
  { intros a Hna.
    pose proof (grant_ok_na_pin_of_grant_ok_na _ _ _ _ Hna) as Ha.
    pose proof (linux_place_is_of_grant_ok_na _ _ _ _ Hna) as Hpl.
    (* [comment removed for export] *)
    rewrite Hchk, Hm0. rewrite (grant_na_pin_not_errno model a nZ HnZpos HnZal Ha), Hpl. cbn [andb].
    rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
  eapply (srz_node1 (mkCfg ms model) IB (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB (exist _ a0 Ha0)).
  - apply (node_chk_ev_gen_noacc segs scfg ms model (getr regs 17) IB effs ms' (fun _ => []) materialize_model_accesses_nil Hh eq_refl).
    + intros [a Hna]; cbn [effs ms']. exact (HokS a Hna).
    + intros [a Hna]; cbn [effs ms']. apply alloc_nonrefusal_step. cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno).
      exact (grant_na_pin_not_errno model a nZ HnZpos HnZal (grant_ok_na_pin_of_grant_ok_na _ _ _ _ Hna)).
    + intros [r ws zs us cs ci] m' evs Hc Hu.
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * exfalso. apply Hu. apply (alloc_refusal_unforced segs scfg Halloc ms model (getr regs 17) _ _ _ _ ltac:(rewrite Hno; reflexivity) (HokS a0 Ha0)).
        -- cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno). exact (grant_na_pin_not_errno model a0 nZ HnZpos HnZal (grant_ok_na_pin_of_grant_ok_na _ _ _ _ Ha0)).
        -- cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno). exact Er.
      * rewrite Hchk in Hc. rewrite Er in Hc.
        destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
        (* [comment removed for export] *)
        destruct (Placement.linux_place_is (m_vmmaps model) (kb_thp (m_kernel model))
                    (ms_gpr ms 0) nZ r) eqn:Hg; [|discriminate]. cbn [andb] in Hc.
        destruct (listNN_eqb zs [(r, n)]) eqn:Hl; [|discriminate].
        apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
        exists (exist _ r (Hadm r Hg)). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
      destruct (Placement.linux_place_is (m_vmmaps model) (kb_thp (m_kernel model))
                  (ms_gpr ms 0) nZ r && true && listNN_eqb zs [(r, n)])%bool; discriminate.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; [|discriminate]; injection Hc as <- <-; exact Hh|].
      destruct (Placement.linux_place_is (m_vmmaps model) (kb_thp (m_kernel model))
                  (ms_gpr ms 0) nZ r && true && listNN_eqb zs [(r, n)])%bool; [|discriminate].
      injection Hc as <- <-. rewrite with_mmap_backing_halted. unfold mmap_model. rewrite with_vmmaps_halted. exact Hh.
    + intros [a Ha]; reflexivity.
  (* [comment removed for export] *)
  - exact (RomBase.sys_rob_memfree segs ms model (getr regs 17) eq_refl
             ltac:(rewrite Hno; exact RomBase.memfree_222)).
  - intros [a Ha]. cbn [effs ms']. unfold ms. rewrite adv_zeros1_epend. apply HB. exact (grant_ok_na_pin_of_grant_ok_na _ _ _ _ Ha).
Qed.

Lemma mmap_none_check : forall ms x8 model eff flags,
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 1 <> Z_to_bv 64 0 -> ms_gpr ms 2 = Z_to_bv 64 0 ->
  ms_gpr ms 3 = flags -> mmap_flags_core flags = 34%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (* [comment removed for export] *)
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with [] => CheckOk model [] | _ => CheckReject end
        (* [comment removed for export] *)
        else if Placement.linux_place_is (m_vmmaps model) (kb_thp (m_kernel model)) (ms_gpr ms 0) nZ r
                && listNN_eqb us [(r, Z_to_bv 64 nZ)]
        then CheckOk (with_mmap_backing flags r (Z_to_bv 64 nZ) (noaccess_model r (Z_to_bv 64 nZ) model)) []
        else CheckReject
    | _ => CheckReject
    end.
(* [comment removed for export] *)
Proof.
  intros ms x8 model eff flags Hno H1 H2 H3 Hcore H4 H5 Hdecl nZ.
  destruct (mmap_gates_core34 flags Hcore) as (_ & Gm & Gn).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn. cbn [negb]. cbv beta iota zeta.
  (* [comment removed for export] *)
  rewrite Hdecl. fold nZ.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
  destruct (errno_ret_in mmap_errnos r); [reflexivity|].
  unfold noaccess_model. reflexivity.
Qed.

Lemma srz_mmap_none1 : forall regs (pc : word) mem rom model w (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = flags -> mmap_flags_core flags = 34%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  (* [comment removed for export] *)
  place_declined_b (m_kernel model) (m_vmmaps model) (getr regs 10)
    (page_round_up_Z len) = false ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (* [comment removed for export] *)
  (exists a, OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.grant_ok_na (getr regs 10) model a nZ = true) ->
  (forall a, grant_ok_na_pin model a nZ = true ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (unfill a n mem) rom)
                          (with_mmap_backing flags a n (noaccess_model a n model))) KB) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
(* [comment removed for export] *)
Proof.
  (* [comment removed for export] *)
  intros regs pc mem rom model w len flags KB HF HE Hh H17 H11 Hlen H12 H13 Hcore H14 H15 Hdecl nZ n (a0 & Ha0) HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
  pose proof (fun eff => mmap_none_check ms (getr regs 17) model eff flags Hno Hne1
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)
                           ltac:(rewrite Hl1; unfold ms; rewrite ms_gpr_epend0; exact Hdecl)) as Hchk.
  cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk.
  assert (Hn0 : (0 <= nZ)%Z) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
  (* [comment removed for export] *)
  assert (HnZpos : (0 < nZ)%Z) by (unfold nZ; apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.AsanCeil.page_round_up_Z_pos'; lia).
  assert (HnZal : (nZ mod page_size = 0)%Z) by (unfold nZ; apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.AsanCeil.page_round_up_Z_aligned').
  assert (Hm0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; apply ms_gpr_epend0).
  assert (Hadm : forall r, Placement.linux_place_is (m_vmmaps model) (kb_thp (m_kernel model))
                             (ms_gpr ms 0) nZ r = true ->
                           OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.grant_ok_na (getr regs 10) model r nZ = true).
  { intros r Hpl. rewrite Hm0 in Hpl.
    pose proof (Placement.linux_place_is_admissible _ _ _ _ _ HnZpos HnZal Hpl)
      as (Hal & Hpos & Htop & Hfree).
    unfold OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.grant_ok_na. rewrite !Bool.andb_true_iff. repeat split.
    - exact Hpl.
    - apply Z.eqb_eq; exact Hal.
    - apply Z.ltb_lt; exact Hpos.
    - apply Z.leb_le; exact Htop.
    - exact Hfree. }
  (* [comment removed for export] *)
  pose (IB := {a : word | OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.grant_ok_na (getr regs 10) model a nZ = true}).
  pose (effs := fun i : IB => match i with exist _ a _ => mkEffectU a [] [] [(a, n)] [] [] end).
  pose (ms' := fun i : IB => match i with exist _ a _ => with_mmap_backing flags a n (noaccess_model a n model) end).
  assert (HokS : forall a, OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.grant_ok_na (getr regs 10) model a nZ = true ->
            check_syscall (sys_input segs ms (getr regs 17)) (mkEffectU a [] [] [(a, n)] [] []) model
            = CheckOk (with_mmap_backing flags a n (noaccess_model a n model)) []).
  { intros a Hna.
    pose proof (grant_ok_na_pin_of_grant_ok_na _ _ _ _ Hna) as Ha.
    pose proof (linux_place_is_of_grant_ok_na _ _ _ _ Hna) as Hpl.
    (* [comment removed for export] *)
    rewrite Hchk, Hm0. rewrite (grant_na_pin_not_errno model a nZ HnZpos HnZal Ha), Hpl. cbn [andb].
    rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
  eapply (srz_node1 (mkCfg ms model) IB (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB (exist _ a0 Ha0)).
  - apply (node_chk_ev_gen_noacc segs scfg ms model (getr regs 17) IB effs ms' (fun _ => []) materialize_model_accesses_nil Hh eq_refl).
    + intros [a Hna]; cbn [effs ms']. exact (HokS a Hna).
    + intros [a Hna]; cbn [effs ms']. apply alloc_nonrefusal_step. cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno).
      exact (grant_na_pin_not_errno model a nZ HnZpos HnZal (grant_ok_na_pin_of_grant_ok_na _ _ _ _ Hna)).
    + intros [r ws zs us cs ci] m' evs Hc Hu.
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * exfalso. apply Hu. apply (alloc_refusal_unforced segs scfg Halloc ms model (getr regs 17) _ _ _ _ ltac:(rewrite Hno; reflexivity) (HokS a0 Ha0)).
        -- cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno). exact (grant_na_pin_not_errno model a0 nZ HnZpos HnZal (grant_ok_na_pin_of_grant_ok_na _ _ _ _ Ha0)).
        -- cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno). exact Er.
      * rewrite Hchk in Hc. rewrite Er in Hc.
        destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
        (* [comment removed for export] *)
        destruct (Placement.linux_place_is (m_vmmaps model) (kb_thp (m_kernel model))
                    (ms_gpr ms 0) nZ r) eqn:Hg; [|discriminate]. cbn [andb] in Hc.
        destruct (listNN_eqb us [(r, n)]) eqn:Hl; [|discriminate].
        apply listNN_eqb_eq in Hl. subst us. injection Hc as <- <-.
        exists (exist _ r (Hadm r Hg)). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
      destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (Placement.linux_place_is (m_vmmaps model) (kb_thp (m_kernel model))
                  (ms_gpr ms 0) nZ r && listNN_eqb us [(r, n)])%bool; discriminate.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
      destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; [|discriminate]; injection Hc as <- <-; exact Hh|].
      destruct (Placement.linux_place_is (m_vmmaps model) (kb_thp (m_kernel model))
                  (ms_gpr ms 0) nZ r && listNN_eqb us [(r, n)])%bool; [|discriminate].
      injection Hc as <- <-. rewrite with_mmap_backing_halted. unfold noaccess_model. rewrite with_vmmaps_halted. exact Hh.
    + intros [a Ha]; reflexivity.
  (* [comment removed for export] *)
  - exact (RomBase.sys_rob_memfree segs ms model (getr regs 17) eq_refl
             ltac:(rewrite Hno; exact RomBase.memfree_222)).
  - intros [a Ha]. cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. apply HB. exact (grant_ok_na_pin_of_grant_ok_na _ _ _ _ Ha).
Qed.
End OurSpecNodes.



Section OurSpecNodes2.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma refusal_b_mprotect_epend : forall ms x8 model r, bv_unsigned x8 = 226%Z ->
  refusal_b (sys_input segs ms x8) model r = errno_ret_in mprotect_errnos r.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["OurSpecNodes2"] "p'0h03Hnoh15modelh22msh31rh42x8h51zi001ai011xp;1p;2p;3p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6g007eR6p4p710R:p8p1008Cp4p710R;P7p8P;P:p8p1008`p4p70R<P2p8P<P7p8P<P8p8P<P9p8P<P:p8P<p1009Np4p710R<p8p1009kp605611111000p100;1p4p741110R=p8p100;np605611111000R>P=p8p100=:p4p7210R?P7p8P?P8p8P?P9p8P?P:p8P?p100=fp4p710p8p100>mp605611111000R?P>p8P?P=p8p100@:p605611111000R>P?p8P>P=p8p100ADp6054111000R?p100BIp4p710R@p8P?P=p8P?p100CDp4p7511110RAp8p100DAp4p711RBP@p8PBp100E?p4p771111110p8PBPAp8p100FKp4p711RBP=p8PBp100G<p4p741110p8p100HBp4p70RBP7p8PBP8p8PBP9p8PBP:p8p100I8p6051000RBP8p8PBP9p8p100J<p4p70R9P>p8P9P?p8P9P@p8P9P=p8P4p4p7210R4P7p8P4P:p8p100K7p4p7210P:p8p100KVp4p73110P:p8p103T5p6051000R7p1016ap4p710R9p8P7P<p8P7P5p8P7P0p8p103WUR7p6051001R?P1p8P?P;p8P?P<p8P?P5p8P?P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7P9p8P7P0p8P4p60521000R4P2p8P4P:p8P4P0p8p100L2p4p710P:p8P0P:p8p105Eip6054111000R:P@p8P:P=p8P:PAp8g00LPj10Tg00M5j1BTg00MSj1=Tg00O6j23Tg00ePj11Tg01g6j19Tg00TFj32Tg032Tj25Tg04j;j36Tg05Foj27Tg05Gdj34Tg05H^j18Tg05IWj1<Tg05JMj2;Tg05KGj2:Tg00R2j2ATP6j6@Tg05LOj1?Tg05MFj3>Tg04^hg00U>R6#0#0#0#0#0#0#BRA#=R:g01UDg00T`R=f2R@,3A%16R6#1#0#0#0#1#0#9R032P=P0g00UcR0P0P0f0R4%06#1#0#1#1#0#9R6'5f3R2p,4segsR7f5f4R936g01@4R3'7;4@g02NOR1g05N<R?P0%84%<4R5/;2g0121R<n10110100021010000n0100000020000g04:BR;/:@32X5=f1R=,:;R;,A013A2P4E@P0P0A6792R9#?,3ARA/561793=4@=P1P?P0%8A1;5@P<n10110100021010000n0100000020000=20;eA>9@==20;eW0X3:W1W4W2o"). Qed.

Lemma mmap_fixed_gate_open : forall (h : VmMaps) (addr : word) (len : Z),
  (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok h ->
  (two_pow_64 <=? bv_unsigned addr + page_round_up_Z len)%Z = false
  /\ negb (bv_unsigned addr + page_round_up_Z len <=? alloc_top h)%Z = false
  /\ negb (bv_unsigned addr mod page_size =? 0)%Z = false
  /\ negb (0 <? bv_unsigned addr)%Z = false
  /\ (len < 2 ^ 64)%Z /\ (0 < page_round_up_Z len < 2 ^ 64)%Z.
Proof.
  intros h addr len Hal Hpos Hlen Hce Hisp. pose proof alloc_ceiling_val.
  pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr).
  repeat split.
  - apply Z.leb_gt. unfold two_pow_64. lia.
  - rewrite (proj2 (Z.leb_le _ _) (alloc_top_ge_of_ceiling _ _ Hisp Hce)). reflexivity.
  - rewrite (proj2 (Z.eqb_eq _ _) Hal). reflexivity.
  - rewrite (proj2 (Z.ltb_lt _ _) Hpos). reflexivity.
  - lia. - lia. - lia.
Qed.

(* [comment removed for export] *)

Lemma mmap_fixed_rw_free_check : forall ms x8 model eff flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  ms_gpr ms 2 = Z_to_bv 64 3 -> ms_gpr ms 3 = flags -> mmap_flags_core flags = 50%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mmap_errnos r
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags model nZ
        then CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hcore H4 H5 nZ n Hrf.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (G1 & G2 & G3 & G4 & Hlen' & HnZ).
  destruct (mmap_gates_core50 flags (Z_to_bv 64 3) Hcore) as (Gm & Gn & _ & Gfn & Gfr).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap, check_mmap_fixed_overflow.
  rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn, Gfn, Gfr. cbn [negb]. cbv beta iota zeta.
  rewrite G1, G2, G3, G4. fold nZ. fold n.
  assert (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = false).
  { apply region_free_not_contains; [unfold n; rewrite u64_lit by lia; lia|].
    rewrite OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.region_free_app in Hrf. apply andb_true_iff in Hrf. tauto. }
  rewrite Hmc, andb_false_r, Hrf.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct us; [|destruct (errno_ret_in mmap_errnos r); [destruct zs|]; reflexivity].
  destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
  unfold mmap_model. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_gates_noreplace : forall flags prot,
  (mmap_flags_core flags = 1048610 \/ mmap_flags_core flags = 1048626)%Z ->   (* [comment removed for export] *)
  mmap_modeled_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noreplace_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true
  /\ mmap_noreplace_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_noreplace_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true
  /\ mmap_anon_b flags = true.
Proof.
  intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b,
    mmap_noreplace_noaccess_b, mmap_noreplace_rw_b, mmap_noreplace_flags_b.
  destruct Hc as [Hc|Hc]; rewrite Hc; (repeat split; try (vm_compute; reflexivity));
    try (destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity);
    (apply (mmap_anon_b_of_core flags _ Hc); reflexivity).
Qed.

Lemma mmap_noreplace_rw_free_check : forall ms x8 model eff flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  ms_gpr ms 2 = Z_to_bv 64 3 -> ms_gpr ms 3 = flags ->
  (mmap_flags_core flags = 1048610 \/ mmap_flags_core flags = 1048626)%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mmap_errnos r
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags model nZ
        then CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hcore H4 H5 nZ n Hrf.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (G1 & G2 & G3 & G4 & Hlen' & HnZ).
  destruct (mmap_gates_noreplace flags (Z_to_bv 64 3) Hcore) as (Gm & Gn & Gfn & Gfr & _ & Gnn & Gnr & Ga).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap, check_mmap_fixed_overflow.
  rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, Ga, Gm, Gn, Gfn, Gfr, Gnn, Gnr. cbn [negb]. cbv beta iota zeta.
  rewrite G1, G2, G3, G4. fold nZ. fold n. rewrite Hrf.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct us; [|destruct (errno_ret_in mmap_errnos r); [destruct zs|]; reflexivity].
  destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
  unfold mmap_model. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_fixed_rw_free1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  (0 < len)%Z -> (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  (forall eff, check_syscall (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) eff model
     = match eff with
       | mkEffectU r [] zs [] [] [] =>
           if errno_ret_in mmap_errnos r
           then match zs with [] => CheckOk model [] | _ => CheckReject end
           else if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags model nZ
           then CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []
           else CheckReject
       | _ => CheckReject
       end) ->
  mmap_noreserve_backed_ok flags model nZ = true ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (zfill addr n mem) rom)
                       (with_mmap_backing flags addr n (mmap_model addr n model))) KB ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 Hlen Hnw nZ n Hchk Hbk HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)). fold ms in Hchk.
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  rewrite Hbk in Hchk.
  assert (Hna : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof alloc_ceiling_val. unfold two_pow_64. lia. }
  pose (effs := fun _ : unit => mkEffectU addr [] [(addr, n)] [] [] []).
  pose (ms' := fun _ : unit => with_mmap_backing flags addr n (mmap_model addr n model)).
  assert (HokS : check_syscall (sys_input segs ms (getr regs 17)) (mkEffectU addr [] [(addr, n)] [] [] []) model
                 = CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []).
  { rewrite Hchk, Hna, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
  eapply (srz_node1 segs scfg (mkCfg ms model) unit (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB tt).
  - apply (node_chk_ev_gen_noacc segs scfg ms model (getr regs 17) unit effs ms' (fun _ => []) materialize_model_accesses_nil Hh eq_refl).
    + intros []; exact HokS.
    + intros []; cbv delta [effs] beta iota. apply alloc_nonrefusal_step. cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Hna.
    + intros [r ws zs us cs ci] m' evs Hc Hu.
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * exfalso. apply Hu. apply (alloc_refusal_unforced segs scfg Halloc ms model (getr regs 17) _ _ _ _ ltac:(rewrite Hno; reflexivity) HokS).
        -- cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Hna.
        -- cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Er.
      * rewrite Hchk, Er in Hc.
        destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
        destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r zs. cbn [andb] in Hc. injection Hc as <- <-.
        exists tt. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)] && true)%bool; discriminate.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; [|discriminate]; injection Hc as <- <-; exact Hh|].
      destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)] && true)%bool; [|discriminate].
      injection Hc as <- <-. rewrite with_mmap_backing_halted. unfold mmap_model. rewrite with_vmmaps_halted. exact Hh.
    + intros []; reflexivity.
  - exact (RomBase.sys_rob_memfree segs ms model (getr regs 17) eq_refl
             ltac:(rewrite Hno; exact RomBase.memfree_222)).
  - intros []. cbv delta [effs ms'] beta iota. unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

(* [comment removed for export] *)

Lemma mmap_fixed_none_free_check : forall ms x8 model eff flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  ms_gpr ms 2 = Z_to_bv 64 0 -> ms_gpr ms 3 = flags -> mmap_flags_core flags = 50%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with [] => CheckOk model [] | _ => CheckReject end
        else if bv_eqb r addr && listNN_eqb us [(addr, n)]
        then CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hcore H4 H5 nZ n Hrf.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (G1 & G2 & G3 & G4 & Hlen' & HnZ).
  destruct (mmap_gates_core50 flags (Z_to_bv 64 0) Hcore) as (Gm & Gn & Gfn & _ & _).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap, check_mmap_fixed_overflow.
  rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn, Gfn. cbn [negb]. cbv beta iota zeta.
  rewrite G1, G2, G3, G4. fold nZ. fold n.
  assert (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = false).
  { apply region_free_not_contains; [unfold n; rewrite u64_lit by lia; lia|].
    rewrite OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.region_free_app in Hrf. apply andb_true_iff in Hrf. tauto. }
  rewrite Hmc, andb_false_r, Hrf.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct zs; [|reflexivity].
  destruct cs; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
  destruct ci; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
  unfold noaccess_model. reflexivity.
Qed.

Lemma mmap_noreplace_none_free_check : forall ms x8 model eff flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  ms_gpr ms 2 = Z_to_bv 64 0 -> ms_gpr ms 3 = flags ->
  (mmap_flags_core flags = 1048610 \/ mmap_flags_core flags = 1048626)%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with [] => CheckOk model [] | _ => CheckReject end
        else if bv_eqb r addr && listNN_eqb us [(addr, n)]
        then CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hcore H4 H5 nZ n Hrf.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (G1 & G2 & G3 & G4 & Hlen' & HnZ).
  destruct (mmap_gates_noreplace flags (Z_to_bv 64 0) Hcore) as (Gm & Gn & Gfn & Gfr & Gnn & _ & _ & Ga).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap, check_mmap_fixed_overflow.
  rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, Ga, Gm, Gn, Gfn, Gfr, Gnn. cbn [negb]. cbv beta iota zeta.
  rewrite G1, G2, G3, G4. fold nZ. fold n. rewrite Hrf.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct zs; [|reflexivity].
  destruct cs; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
  destruct ci; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
  unfold noaccess_model. reflexivity.
Qed.

Lemma srz_mmap_fixed_none_free1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  (0 < len)%Z -> (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  (forall eff, check_syscall (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) eff model
     = match eff with
       | mkEffectU r [] [] us [] [] =>
           if errno_ret_in mmap_errnos r
           then match us with [] => CheckOk model [] | _ => CheckReject end
           else if bv_eqb r addr && listNN_eqb us [(addr, n)]
           then CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []
           else CheckReject
       | _ => CheckReject
       end) ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom)
                       (with_mmap_backing flags addr n (noaccess_model addr n model))) KB ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 Hlen Hnw nZ n Hchk HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)). fold ms in Hchk.
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hna : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof alloc_ceiling_val. unfold two_pow_64. lia. }
  pose (effs := fun _ : unit => mkEffectU addr [] [] [(addr, n)] [] []).
  pose (ms' := fun _ : unit => with_mmap_backing flags addr n (noaccess_model addr n model)).
  assert (HokS : check_syscall (sys_input segs ms (getr regs 17)) (mkEffectU addr [] [] [(addr, n)] [] []) model
                 = CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []).
  { rewrite Hchk, Hna, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
  eapply (srz_node1 segs scfg (mkCfg ms model) unit (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB tt).
  - apply (node_chk_ev_gen_noacc segs scfg ms model (getr regs 17) unit effs ms' (fun _ => []) materialize_model_accesses_nil Hh eq_refl).
    + intros []; exact HokS.
    + intros []; cbv delta [effs] beta iota. apply alloc_nonrefusal_step. cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Hna.
    + intros [r ws zs us cs ci] m' evs Hc Hu.
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * exfalso. apply Hu. apply (alloc_refusal_unforced segs scfg Halloc ms model (getr regs 17) _ _ _ _ ltac:(rewrite Hno; reflexivity) HokS).
        -- cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Hna.
        -- cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Er.
      * rewrite Hchk, Er in Hc.
        destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
        destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r us. cbn [andb] in Hc. injection Hc as <- <-.
        exists tt. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
      destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
      destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; [|discriminate]; injection Hc as <- <-; exact Hh|].
      destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; [|discriminate].
      injection Hc as <- <-. rewrite with_mmap_backing_halted. unfold noaccess_model. rewrite with_vmmaps_halted. exact Hh.
    + intros []; reflexivity.
  - exact (RomBase.sys_rob_memfree segs ms model (getr regs 17) eq_refl
             ltac:(rewrite Hno; exact RomBase.memfree_222)).
  - intros []. cbv delta [effs ms'] beta iota. unfold ms. rewrite adv_unmaps1_epend. exact HB.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_mprotect1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 226 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  getr regs 12 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vdso_reserved (m_kernel model) (vdso_top (m_vmmaps model))) addr n = true ->
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = true ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mem) rom)
                       (mprotect_model addr n model)) KB ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len KB HF HE Hh H17 H10 Hal H11 Hlen Hnw H12 n Hvd Hna Hma Hbud HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 226%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mprotect_check segs ms (getr regs 17) model eff addr len Hno
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hnw
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12) Hvd Hna Hma) as Hchk.
  cbv zeta in Hchk. fold n in Hchk. rewrite Hbud in Hchk.
  assert (Hz : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false) by reflexivity.
  pose (effs := fun _ : unit => mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] []).
  pose (ms' := fun _ : unit => mprotect_model addr n model).
  assert (HokS : check_syscall (sys_input segs ms (getr regs 17)) (mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] []) model
                 = CheckOk (mprotect_model addr n model) []).
  { rewrite Hchk, Hz. unfold w_is0. rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
  eapply (srz_node1 segs scfg (mkCfg ms model) unit (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB tt).
  - apply (node_chk_ev_gen_noacc segs scfg ms model (getr regs 17) unit effs ms' (fun _ => []) materialize_model_accesses_nil Hh eq_refl).
    + intros []; exact HokS.
    + intros []; cbv delta [effs] beta iota. apply alloc_nonrefusal_step. cbn [eff_ret]. rewrite (refusal_b_mprotect_epend _ _ _ _ Hno). exact Hz.
    + intros [r ws zs us cs ci] m' evs Hc Hu.
      destruct (errno_ret_in mprotect_errnos r) eqn:Er.
      * exfalso. apply Hu. apply (alloc_refusal_unforced segs scfg Halloc ms model (getr regs 17) _ _ _ _ ltac:(rewrite Hno; reflexivity) HokS).
        -- cbn [eff_ret]. rewrite (refusal_b_mprotect_epend _ _ _ _ Hno). exact Hz.
        -- cbn [eff_ret]. rewrite (refusal_b_mprotect_epend _ _ _ _ Hno). exact Er.
      * rewrite Hchk, Er in Hc.
        destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
        cbn [andb] in Hc. destruct (w_is0 r) eqn:E0; [|discriminate].
        destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
        apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
        unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r.
        exists tt. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
      cbn [andb] in Hc. destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; discriminate.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mprotect_errnos r); [destruct zs; [|discriminate]; injection Hc as <- <-; exact Hh|].
      cbn [andb] in Hc. destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; [|discriminate].
      injection Hc as <- <-. unfold mprotect_model. rewrite with_vmmaps_halted. exact Hh.
    + intros []; reflexivity.
  - exact (RomBase.sys_rob_memfree segs ms model (getr regs 17) eq_refl
             ltac:(rewrite Hno; exact RomBase.memfree_226)).
  - intros []. cbv delta [effs ms'] beta iota. unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

(* [comment removed for export] *)
Definition fixed_free_core (c : Z) : Prop := (c = 50 \/ (c = 1048610 \/ c = 1048626))%Z.

Lemma srz_mmap_fixed_rw_free1R : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> fixed_free_core (mmap_flags_core flags) ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  mmap_noreserve_backed_ok flags model nZ = true ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (zfill addr n mem) rom)
                       (with_mmap_backing flags addr n (mmap_model addr n model))) KB ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15 nZ n Hrf Hbk HB.
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  eapply (srz_mmap_fixed_rw_free1 regs pc mem rom model w addr len flags KB HF HE Hh H17 Hlen Hce); [|exact Hbk|exact HB].
  intros eff. destruct Hcore as [Hc|Hc].
  - apply (mmap_fixed_rw_free_check _ _ model eff flags addr len Hno);
      rewrite ?ms_gpr_epend0, ?ms_gpr_epend1, ?ms_gpr_epend2, ?ms_gpr_epend3, ?ms_gpr_epend4, ?ms_gpr_epend5; try assumption.
  - apply (mmap_noreplace_rw_free_check _ _ model eff flags addr len Hno);
      rewrite ?ms_gpr_epend0, ?ms_gpr_epend1, ?ms_gpr_epend2, ?ms_gpr_epend3, ?ms_gpr_epend4, ?ms_gpr_epend5; try assumption.
Qed.

Lemma srz_mmap_fixed_none_free1R : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = flags -> fixed_free_core (mmap_flags_core flags) ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom)
                       (with_mmap_backing flags addr n (noaccess_model addr n model))) KB ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15 nZ n Hrf HB.
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  eapply (srz_mmap_fixed_none_free1 regs pc mem rom model w addr len flags KB HF HE Hh H17 Hlen Hce); [|exact HB].
  intros eff. destruct Hcore as [Hc|Hc].
  - apply (mmap_fixed_none_free_check _ _ model eff flags addr len Hno);
      rewrite ?ms_gpr_epend0, ?ms_gpr_epend1, ?ms_gpr_epend2, ?ms_gpr_epend3, ?ms_gpr_epend4, ?ms_gpr_epend5; try assumption.
  - apply (mmap_noreplace_none_free_check _ _ model eff flags addr len Hno);
      rewrite ?ms_gpr_epend0, ?ms_gpr_epend1, ?ms_gpr_epend2, ?ms_gpr_epend3, ?ms_gpr_epend4, ?ms_gpr_epend5; try assumption.
Qed.

Lemma fixed_free_core_32 : fixed_free_core (mmap_flags_core (Z_to_bv 64 50)).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["OurSpecNodes2"] "p;1p;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710R9p8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7P9p8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8g00M5j19Tg00ePj12Tg00LPj11Tg01g6j14Tg01hPj28Tg03dgj17Tg00TFj33Tg01<Yj25Tg022<j36Tf0#1#1p=0g00T`R@g00U>R6#0#0#0R<#9%26#0#2#1#4R6'8#7R?;36%0<#0#0#0#2R<#1#0#2#1#493@?%2<#0#2#1#493@?'5g07CM36o"). Qed.
Lemma fixed_free_core_4032 : fixed_free_core (mmap_flags_core (Z_to_bv 64 16434)).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["OurSpecNodes2"] "p;1p;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710R9p8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7P9p8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8g00M5j19Tg00ePj11Tg00LPj12Tg01g6j13Tg01hPj28Tg03dgj17Tg00TFj34Tg01<Yj25Tg022<j36Tf0#2#2p=0g00T`R@g00U>R6#0#0#0R<#9%0<R<#1#1#0#1#2#3'8#7R?%16#0#1#2#334%0<#0#0#1R<#2#0#1#2#394@?%1<#0#1#2#394@?'5g07D\36o"). Qed.
Lemma fixed_free_core_104022 : fixed_free_core (mmap_flags_core (Z_to_bv 64 1064994)).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["OurSpecNodes2"] "p;1p;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710R9p8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7P9p8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8g00LPj11Tg00M5j1:Tg00ePj12Tg01g6j14Tg01hPj2;Tg03dgj19Tg00TFj35Tg01<Yj27Tg022<j36Tg023ej38Tf0R@#1#1p=0%2@#1p=3g00T`R@g00U>R6#1#0#0R<#1R?#:%2<#0#0#0#0#3#0#3#4';#9R<%26#0#3#435%0?#0#0#0#2R?#1#0#3#495@<R6%2?#0#3#495@<R<'7g07Em966<38o"). Qed.
Lemma fixed_free_core_104032 : fixed_free_core (mmap_flags_core (Z_to_bv 64 1065010)).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["OurSpecNodes2"] "p;1p;2p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710R9p8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7P9p8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8g00LPj12Tg00M5j19Tg00ePj11Tg01g6j13Tg01hPj2:Tg03dgj18Tg00TFj35Tg01<Yj27Tg023ej36Tf0R@#2#2p=0%1@#2p=4g00T`R@g00U>R6#2#0#0R<#2R?#9%1<#0#0#0#0#1#1#0#4#3':#8R<%16#0#4#335%0?#0#0#0#1R?#2#0#4#395@<R6%1?#0#4#395@<R<'7g07G@966<36o"). Qed.

End OurSpecNodes2.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma page_base_aligned' : forall p : word, bv_unsigned p mod 4096 = 0 -> page_base p = p.
Proof.
  intros p Hp. unfold page_base, page_base_of, page_size. apply bv_eq. pose proof (u64_range p).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  rewrite u64_lit; lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma iv_subtract_contained : forall (a sz : word) lo hi,
  bv_unsigned a <= lo -> hi <= bv_unsigned a + bv_unsigned sz -> lo <= hi ->
  iv_subtract a sz lo hi
  = (if bv_unsigned a <? lo then [(a, Z_to_bv 64 (lo - bv_unsigned a))] else [])
    ++ (if hi <? bv_unsigned a + bv_unsigned sz then [(Z_to_bv 64 hi, Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - hi))] else []).
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite Z.min_r by lia. rewrite Z.max_r by lia. reflexivity.
Qed.

Lemma map_replace_entry : forall (f : amap -> word * word) l m pcs,
  map f (replace_entry l m pcs) = flat_map (fun m' => if amap_eqb m' m then map f pcs else [f m']) l.
Proof.
  intros f l m pcs. unfold replace_entry. rewrite flat_map_concat_map, concat_map, map_map, <- flat_map_concat_map.
  apply flat_map_ext. intros m'. destruct (amap_eqb m' m); reflexivity.
Qed.

Lemma maps_subtract_map_replace : forall (f : amap -> word * word) l m pcs lo hi,
  (forall m', In m' l -> amap_eqb m' m = false -> iv_subtract (fst (f m')) (snd (f m')) lo hi = [f m']) ->
  (forall m', In m' l -> amap_eqb m' m = true -> iv_subtract (fst (f m')) (snd (f m')) lo hi = map f pcs) ->
  maps_subtract (map f l) lo hi = map f (replace_entry l m pcs).
Proof.
  intros f l m pcs lo hi Hout Hin. rewrite map_replace_entry.
  induction l as [|m' l IH]; [reflexivity|]. cbn [map flat_map maps_subtract].
  destruct (f m') as [a sz] eqn:Ef. cbn [maps_subtract].
  rewrite (IH ltac:(intros x Hx; apply Hout; right; exact Hx) ltac:(intros x Hx; apply Hin; right; exact Hx)). f_equal.
  destruct (amap_eqb m' m) eqn:Heq.
  - rewrite <- (Hin m' (or_introl eq_refl) Heq), Ef. reflexivity.
  - pose proof (Hout m' (or_introl eq_refl) Heq) as X. rewrite Ef in X. cbn [fst snd] in X. exact X.
Qed.

Lemma in_replace_entry : forall l m pcs m',
  In m' (replace_entry l m pcs) -> (In m' l /\ m' <> m) \/ (In m l /\ In m' pcs).
Proof.
  intros l m pcs m' H. unfold replace_entry in H. apply in_flat_map in H as (m0 & Hm0 & Hin).
  destruct (amap_eqb m0 m) eqn:He.
  - apply APSK.amap_eqb_eq in He. subst m0. right. auto.
  - destruct Hin as [<-|[]]. left. split; [exact Hm0|]. intros ->. rewrite amap_eqb_refl in He. discriminate.
Qed.

Lemma maps_subtract_in_pieces : forall l (b s : word) lo hi q,
  In (b, s) l -> In q (iv_subtract b s lo hi) -> In q (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros b s lo hi q Hin Hq; [destruct Hin|].
  cbn [maps_subtract]. apply in_app_iff. destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. left. exact Hq.
  - right. eapply IH; eassumption.
Qed.

Lemma seps_app_intro : forall l1 l2,
  seps l1 -> seps l2 -> (forall p q, In p l1 -> In q l2 -> iv_disjoint p q) -> seps (l1 ++ l2).
Proof.
  induction l1 as [|p l1 IH]; intros l2 H1 H2 H12; [exact H2|].
  inversion H1 as [|p' l' Hf Hl]; subst. cbn [app]. constructor.
  - apply Forall_app. split; [exact Hf|]. apply Forall_forall. intros q Hq. apply H12; [left; reflexivity | exact Hq].
  - apply IH; [exact Hl | exact H2 |]. intros a b Ha Hb. apply H12; [right; exact Ha | exact Hb].
Qed.

Lemma seps_iv_subtract : forall (a sz : word) lo hi,
  iv_wf (a, sz) -> lo <= hi -> seps (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hwf Hlh. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract.
  assert (S1 : forall p : word * word, seps [p]) by (intros p; apply seps_cons; [apply Forall_nil | apply seps_nil]).
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app];
    try apply S1; try apply seps_nil.
  apply seps_cons; [|apply S1]. apply Forall_cons; [|apply Forall_nil].
  unfold iv_disjoint. cbn [fst snd]. rewrite !u64_lit by lia. left. lia.
Qed.

Lemma seps_maps_subtract : forall l lo hi,
  seps l -> ivs_wf l -> lo <= hi -> seps (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hs Hwf Hlh; [constructor|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. inversion Hs as [|p' l' Hf Htl]; subst.
  cbn [maps_subtract]. apply seps_app_intro; [apply seps_iv_subtract; assumption | apply IH; assumption |].
  intros p q Hp Hq.
  destruct (iv_subtract_pieces a sz lo hi p Ha Hp) as (P1 & P2 & P3).
  destruct (maps_subtract_pieces l lo hi q Hl Hq) as (r & Hr & Q1 & Q2 & Q3).
  pose proof (proj1 (Forall_forall _ _) Hf r Hr) as D. unfold iv_disjoint in *. cbn [fst snd] in *. lia.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_bounds : forall (a sz : word) lo hi q (ih ce : Z),
  lo mod 4096 = 0 -> hi mod 4096 = 0 ->
  0 < bv_unsigned sz -> bv_unsigned a mod 4096 = 0 -> bv_unsigned sz mod 4096 = 0 ->
  ih <= bv_unsigned a -> bv_unsigned a + bv_unsigned sz <= ce -> ce <= 2 ^ 64 ->
  In q (iv_subtract a sz lo hi) ->
  0 < bv_unsigned (snd q) /\ bv_unsigned (fst q) mod 4096 = 0 /\ bv_unsigned (snd q) mod 4096 = 0
  /\ ih <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= ce.
Proof.
  intros a sz lo hi q ih ce Hlo Hhi Hsz Hal Hszl Hih Hce Hce64 Hq.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract in Hq. apply in_app_iff in Hq as [Hq|Hq].
  - destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hq]. destruct Hq as [<-|[]]. cbn [fst snd].
    rewrite u64_lit by lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    destruct (Z.le_gt_cases (bv_unsigned sz) (lo - bv_unsigned a)); [rewrite Z.min_l by lia | rewrite Z.min_r by lia]; repeat split; try lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hq]. destruct Hq as [<-|[]]. cbn [fst snd].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    destruct (Z.le_gt_cases hi (bv_unsigned a)); [rewrite !Z.max_l by lia | rewrite !Z.max_r by lia]; rewrite !u64_lit by lia; repeat split; try lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma maps_subtract_bounds : forall l lo hi (ih ce : Z),
  lo mod 4096 = 0 -> hi mod 4096 = 0 -> ce <= 2 ^ 64 ->
  Forall (fun iv => 0 < bv_unsigned (snd iv) /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                    /\ ih <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ce) l ->
  Forall (fun iv => 0 < bv_unsigned (snd iv) /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                    /\ ih <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ce) (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi ih ce Hlo Hhi Hce HB; [constructor|].
  apply Forall_cons_iff in HB as [(B1 & B2 & B3 & B4 & B5) HBl]. cbn [fst snd] in B1, B2, B3, B4, B5.
  cbn [maps_subtract]. apply Forall_app. split; [|apply IH; assumption].
  apply Forall_forall. intros q Hq. exact (iv_subtract_bounds a sz lo hi q ih ce Hlo Hhi B1 B2 B3 B4 B5 Hce Hq).
Qed.

Lemma sum_sizes_maps_subtract_le : forall l lo hi, ivs_wf l -> lo <= hi -> sum_sizes (maps_subtract l lo hi) <= sum_sizes l.
Proof.
  intros l lo hi Hwf Hlh. rewrite !sum_sizes_live, !live_bytes_sum_count.
  rewrite (proj1 (proj2 (maps_subtract_sem l lo hi Hwf Hlh))). apply sum_count_mono. intros; reflexivity.
Qed.

Lemma ledger_split_maps_subtract : forall l lo hi K Y, ivs_wf l -> ledger_split l K Y -> ledger_split (maps_subtract l lo hi) K Y.
Proof.
  intros l lo hi K Y Hwf H b s Hin. destruct (maps_subtract_pieces l lo hi (b, s) Hwf Hin) as ([b' s'] & Hr & R1 & R2 & _).
  cbn [fst snd] in R1, R2. destruct (H b' s' Hr); lia.
Qed.

Lemma replace_entry_notin : forall ms m pcs, ~ In m ms -> replace_entry ms m pcs = ms.
Proof.
  intros ms m pcs H. induction ms as [|h t IH]; [reflexivity|]. unfold replace_entry in *. cbn [flat_map].
  destruct (amap_eqb h m) eqn:He.
  - apply APSK.amap_eqb_eq in He. subst h. exfalso. apply H. left. reflexivity.
  - cbn [app]. f_equal. apply IH. intros Hin. apply H. right. exact Hin.
Qed.

Lemma maps_subtract_disjoint_id : forall l lo hi,
  lo < hi ->
  (forall iv, In iv l -> 0 < bv_unsigned (snd iv) /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= lo \/ hi <= bv_unsigned (fst iv))) ->
  maps_subtract l lo hi = l.
Proof.
  intros l lo hi Hlh H. induction l as [|[a sz] l IH]; [reflexivity|]. cbn [maps_subtract].
  destruct (H (a, sz) (or_introl eq_refl)) as [P D]. cbn [fst snd] in P, D.
  rewrite (iv_subtract_disjoint a sz lo hi Hlh P D). cbn [app]. f_equal. apply IH. intros iv Hiv. apply H. right. exact Hiv.
Qed.

Lemma maps_match_app_pcs : forall E pcs ms l,
  (forall pc, In pc pcs -> is_fog pc = false) -> maps_match E ms l ->
  maps_match E (pcs ++ ms) (map (amap_den E) pcs ++ l).
Proof.
  intros E pcs ms l Hpf HM. induction pcs as [|pc pcs IH]; [exact HM|]. cbn [app map maps_match].
  rewrite (Hpf pc (or_introl eq_refl)). exists (map (amap_den E) pcs ++ l). split; [reflexivity|].
  apply IH. intros x Hx. apply Hpf. right. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma maps_match_subtract : forall E ms l m pcs lo hi,
  maps_match E ms l -> seps l -> (forall iv, In iv l -> 0 < bv_unsigned (snd iv)) ->
  In m ms -> is_fog m = false -> lo < hi ->
  bv_unsigned (edenot E (am_base m)) <= lo -> hi <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
  map (amap_den E) pcs = iv_subtract (edenot E (am_base m)) (edenot E (am_len m)) lo hi ->
  (forall pc, In pc pcs -> is_fog pc = false) ->
  maps_match E (replace_entry ms m pcs) (maps_subtract l lo hi).
Proof.
  intros E ms. induction ms as [|h t IH]; intros l m pcs lo hi HM Hs Hpos Hm Hf Hlh Hc1 Hc2 Hpcs Hpf; [destruct Hm|].
  cbn [maps_match] in HM. unfold replace_entry. cbn [flat_map]. fold (replace_entry t m pcs).
  destruct (is_fog h) eqn:Hfh.
  - assert (He : amap_eqb h m = false).
    { destruct (amap_eqb h m) eqn:He; [|reflexivity]. apply APSK.amap_eqb_eq in He. subst h. congruence. }
    rewrite He. cbn [app maps_match]. rewrite Hfh.
    assert (Hmt : In m t) by (destruct Hm as [<-|Hm]; [congruence | exact Hm]).
    destruct HM as [HM | ([a sz] & l' & -> & Hsz & HM)].
    + left. eapply IH; eassumption.
    + right. inversion Hs as [|p l0 Hfa Hl]; subst. cbn [maps_subtract].
      pose proof (proj1 (Forall_forall _ _) Hfa (amap_den E m) (maps_match_In E t l' m HM Hmt Hf)) as D.
      unfold iv_disjoint, amap_den in D. cbn [fst snd] in D.
      rewrite (iv_subtract_disjoint a sz lo hi Hlh (Hpos (a, sz) (or_introl eq_refl)) ltac:(lia)). cbn [app].
      exists (a, sz), (maps_subtract l' lo hi). split; [reflexivity|]. split; [exact Hsz|].
      eapply IH; try eassumption. intros iv Hiv. apply Hpos. right. exact Hiv.
  - destruct HM as (l' & -> & HM). inversion Hs as [|p l0 Hfa Hl]; subst.
    unfold amap_den at 1. cbn [maps_subtract].
    destruct (amap_eqb h m) eqn:He.
    + apply APSK.amap_eqb_eq in He. subst h.
      assert (Hnot : ~ In m t).
      { intros Hmt. pose proof (proj1 (Forall_forall _ _) Hfa (amap_den E m) (maps_match_In E t l' m HM Hmt Hf)) as D.
        pose proof (Hpos (amap_den E m) (or_introl eq_refl)) as P. unfold iv_disjoint, amap_den in D, P. cbn [fst snd] in D, P. lia. }
      rewrite (replace_entry_notin t m pcs Hnot). rewrite <- Hpcs.
      rewrite (maps_subtract_disjoint_id l' lo hi Hlh).
      2:{ intros iv Hiv. split; [apply Hpos; right; exact Hiv|].
          pose proof (proj1 (Forall_forall _ _) Hfa iv Hiv) as D. unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. lia. }
      apply maps_match_app_pcs; [exact Hpf | exact HM].
    + assert (Hmt : In m t) by (destruct Hm as [<-|Hm]; [rewrite amap_eqb_refl in He; discriminate | exact Hm]).
      pose proof (proj1 (Forall_forall _ _) Hfa (amap_den E m) (maps_match_In E t l' m HM Hmt Hf)) as D.
      unfold iv_disjoint, amap_den in D. cbn [fst snd] in D.
      pose proof (Hpos _ (or_introl eq_refl)) as P. unfold amap_den in P. cbn [snd] in P.
      rewrite (iv_subtract_disjoint (edenot E (am_base h)) (edenot E (am_len h)) lo hi Hlh P ltac:(lia)). cbn [app maps_match]. rewrite Hfh.
      exists (maps_subtract l' lo hi). split; [reflexivity|].
      eapply IH; try eassumption. intros iv Hiv. apply Hpos. right. exact Hiv.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hull_lt (A : atable) : Prop := img_lo A < img_hi A.

Section Nodes.
Variable SEGS : list Segment.
Variable scfg : SpuriousCfg.              (* [comment removed for export] *)
Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Variable rz : Z.                        (* [comment removed for export] *)
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                             (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.                  Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.  (* [comment removed for export] *)
Hypothesis e_sp0_init : expr_vars_lt nx0 e_sp0 = true.                                                              (* [comment removed for export] *)
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
(* [comment removed for export] *)
Hypothesis HULL_tiled : forall z, img_lo A <= z < img_hi A -> in_ivs z (segments_reserved SEGS) = true.

#[local] Notation CSOK := (APSK.cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation HID := (APSK.hid A argH).
#[local] Notation VIS := (APSK.vis A).
#[local] Notation MR := (APSK.Mr A argH).
#[local] Notation ALLOW := (APSK.allowA A).
#[local] Notation cfg := (cfg_of SEGS).

(* [comment removed for export] *)
Let HS : nat -> option acs := fun _ => None.
Let XN : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let XE : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let XB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
Let RES_len' : length (segments_reserved SEGS) = n_res A := RES_len.
Let HULL_ok' : 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI := HULL_ok.
Let SHADOW_ok' : 0 <= shadow_off A <= 2 ^ 47 := SHADOW_ok.
Let RES_hullH : RES_hull_def SEGS A := RES_hull.

(* [comment removed for export] *)
Let reg_sound' := APSK.reg_sound SEGS A LIMIT SINV argH FS0.
Let reg_lit_sound' := APSK.reg_lit_sound SEGS A LIMIT SINV argH FS0.
Let kentry_keep_sem' := APSK.kentry_keep_sem SEGS.
Let kentry_apart_b_sem' := APSK.kentry_apart_b_sem SEGS.
Let regs_ok_set_n' := APSK.regs_ok_set_n.
Let in_ivs_map_den' := APSK.in_ivs_map_den.
Let kimg_clip_in_hull' := APSK.kimg_clip_in_hull A.
Let cs_ok_agree' := APSK.cs_ok_agree SEGS A nx0 LIMIT SINV argH e_sp0_init argH_agree SINV_agree FS0.
Let cs_ok_frame' := APSK.cs_ok_frame SEGS A LIMIT SINV argH SINV_frame FS0.
Let hid_agree' := APSK.hid_agree A nx0 argH e_sp0_init argH_agree.
Let vis_add_sound' := APSK.vis_add_sound SEGS A LIMIT HS XN XE XB SHADOW_ok SINV argH argH_high FS0 0%nat.
Let A_wf_allowA' := APSK.A_wf_allowA A HS XN XE XB 0%nat.
Let know_ok_unhide' := APSK.know_ok_unhide SEGS A.
Let hid_hull' := APSK.hid_hull A HULL_ok argH argH_high.
Let H_off_segments_cs' := APSK.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high.
Let maps_match_exact' := APSK.maps_match_exact nx0 HS XN XE XB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_len_sound : forall E cs R FULL model ne nlo nhi,
  CSOK E cs R FULL model -> mmap_len cs = Some (ne, nlo, nhi) ->
  let len := bv_unsigned (edenot E (reg cs 11)) in
  getr R (Z_to_bv 5 11) = Z_to_bv 64 len
  /\ 0 < len < 2 ^ 64
  /\ edenot E ne = Z_to_bv 64 (page_round_up_Z len)
  /\ 0 < nlo /\ nlo <= page_round_up_Z len <= nhi
  /\ page_round_up_Z len mod 4096 = 0
  /\ (forall E', edenot E' (reg cs 11) = edenot E (reg cs 11) -> edenot E' ne = edenot E ne).
Proof.
  intros E cs R FULL model ne nlo nhi HC HML len.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (reg_sound' E cs R FULL model 11 HC ltac:(lia)) as R11. change (Z.of_nat 11) with 11 in R11.
  pose proof (u64_range (edenot E (reg cs 11))) as Hr.
  rewrite mmap_len_eq in HML. (* [comment removed for export] *) unfold mmap_len_ref in HML.
  destruct (reg_lit cs 11) as [lz|] eqn:H11.
  - destruct (Z.ltb_spec 0 lz); [|discriminate]. injection HML as <- <- <-.
    destruct (reg_lit_sound' E cs R FULL model 11 lz HC ltac:(lia) H11) as [R11' Hlz]. change (Z.of_nat 11) with 11 in R11'.
    assert (Hlen : len = lz).
    { unfold len. rewrite <- R11, R11'. apply u64_lit. unfold two64 in Hlz. lia. }
    rewrite Hlen. pose proof (page_round_up_Z_bounds lz ltac:(lia)) as PB. unfold page_size in PB.
    rewrite page_up_eq.
    split; [exact R11'|]. split; [unfold two64 in Hlz; lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [apply page_round_up_Z_aligned'|]. intros E' _. reflexivity.
  - destruct (xlo (kn cs) (reg cs 11)) as [lo|] eqn:Hxl; [|discriminate].
    destruct (xhi (kn cs) (reg cs 11)) as [hi|] eqn:Hxh; [|discriminate].
    match type of HML with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    injection HML as <- <- <-.
    apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hlo Hal].
    apply Z.ltb_lt in Hlo. apply Z.leb_le in Hal. apply Z.leb_le in Hhi.
    pose proof (xlo_sound SEGS E _ (kn cs) _ lo HK Hxl) as B1.
    pose proof (xhi_sound SEGS E _ (kn cs) _ hi HK Hxh) as B2.
    destruct (ealign_sound SEGS E _ (kn cs) (reg cs 11) HK) as [_ Hdiv].
    assert (Hmod : len mod 4096 = 0).
    { unfold len. destruct Hdiv as [q Hq]. rewrite Hq.
      replace (2 ^ ealign (kn cs) (reg cs 11)) with (2 ^ (ealign (kn cs) (reg cs 11) - 12) * 4096)
        by (rewrite <- (Z.pow_add_r 2 _ 12) by lia; f_equal; lia).
      rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
    assert (Hpr : page_round_up_Z len = len).
    { unfold page_round_up_Z, page_size.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). unfold len in *. lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    rewrite Hpr.
    split; [rewrite R11; symmetry; apply Z_to_bv_bv_unsigned|].
    split; [unfold len in *; lia|]. split; [symmetry; apply Z_to_bv_bv_unsigned|].
    split; [lia|]. split; [unfold len in *; lia|]. split; [exact Hmod|].
    intros E' HE'. exact HE'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv5_of_nat : forall n, (n < 32)%nat -> Z_to_bv 5 (Z.of_nat n) = Z_to_bv 5 (Z.of_nat n).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h01np;2p;1p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710R9p8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7P9p8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8g02\<j29Tg00LPj13Tg00ePj12Tg00M5j18Tg00MSj17Tg01OLj16Tg01hPj24Tg00R2j25Tg01=3j11Tf0R@#1#1#1#1p=0g02`eg01@4#0#0#0#0#0#0#0#0,9@g00U>#3#2#8R@#7f1#6,4@'5UW0o"). Qed.
Lemma bv5_10 : (10%bv : bv 5) = Z_to_bv 5 (Z.of_nat 10).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h02b1h12b2h21nh31Hp;1p;3p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710R9p8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7P9p8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8g00MSj13Tg00TFj32Tg00O6j20Tg04;Jj36Tg00LPj15Tg00ePj1=Tg00M5j1<Tg01g6j1;Tg04H0j3:Tg01OLj17Tg01hPj28Tg00R2j29Tg01=3j14Tf0R@#4#4p=1g04<fR6%3@R<f1R?#3R0g00Z0f2R4#3?2?@g00T`R2f3R7/04107?32R9[104?104@522%37?24?[R3f4#3?274\9A64?@P@n2001000000120000000W1W0W2P3^10^0<^26P@g00U>#5#=R@#<R6%5@#;g013J5:6g01@4#1#1#1#1#1#7,86R@106@,92O4b3o"). Qed.
Lemma bv5_11 : (11%bv : bv 5) = Z_to_bv 5 (Z.of_nat 11).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h02b1h12b2h21nh31Hp;1p;3p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710R9p8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7P9p8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8g00MSj13Tg00TFj32Tg00O6j21Tg04;Jj36Tg00LPj1=Tg00ePj15Tg00M5j1;Tg01g6j18Tg04H0j37Tg01=3j14Tg01OLj19Tg01hPj2:Tg00R2j2<Tf0R@#4#4p=0g04<fR6%3@R<f1R?#3R0g00Z0f2R4#3?2?@g00T`R2f3R7/14117?32R9[114?114@522%37?24?[R3f4#3?274\9A64?@P@n2001000000120000000W1W0W2P3^10^0<^26P@g00U>#=#5R@#;R6%5@#8g013J576g01@4#4#0#0#0#0#0#9,:6R@116@,<2O4b3o"). Qed.
Lemma bv5_12 : (12%bv : bv 5) = Z_to_bv 5 (Z.of_nat 12).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h02b1h12b2h21nh31Hp;1p;3p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710R9p8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7P9p8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8g00MSj11Tg00TFj33Tg00O6j22Tg04;Jj37Tg00LPj14Tg00ePj15Tg00M5j1=Tg01g6j1<Tg04H0j3;Tg01OLj18Tg01hPj29Tg00R2j2:Tg01=3j16Tf0R@#6#6p=0g04<fR6%1@R<f1R?#1R0g00Z0f2R4#1?3?@g00T`R2f3R7/24127?33R9[124?124@532%17?34?[R3f4#1?374\9A74?@P@n2001000000120000000W1W0W2P3^10^0<^26P@g00U>R@#4#5#=R6%5@#4#4#<g013J5;6g01@4#0#0#0#0#0#0#8,96R@126@,:2O4b3o"). Qed.
Lemma bv5_13 : (13%bv : bv 5) = Z_to_bv 5 (Z.of_nat 13).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h02b1h12b2h21nh31Hp;1p;3p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710R9p8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7P9p8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8g00MSj12Tg00TFj33Tg00O6j21Tg04;Jj37Tg00LPj16Tg00ePj15Tg00M5j1<Tg01g6j1;Tg04H0j3:Tg01=3j14Tg01OLj18Tg01hPj29Tg00R2j2=Tf0R@#4#4p=0g04<fR6%2@R<f1R?#2R0g00Z0f2R4#2?3?@g00T`R2f3R7/14117?33R9[114?114@532%27?34?[R3f4#2?374\9A74?@P@n2001000000120000000W1W0W2P3^10^0<^26P@g00U>R@#6#5#<R6%5@#6#5#;g013J5:6g01@4#4#0#0#0#0#0#0#8,96R@116@,=2O4b3o"). Qed.
Lemma bv5_14 : (14%bv : bv 5) = Z_to_bv 5 (Z.of_nat 14).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h02b1h12b2h21nh31Hp;1p;3p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710R9p8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7P9p8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8g00MSj11Tg00TFj33Tg00O6j22Tg04;Jj37Tg00LPj16Tg00ePj14Tg00M5j1=Tg01g6j1<Tg04H0j3;Tg01OLj18Tg01hPj29Tg00R2j2:Tg01=3j15Tf0R@#5#5p=0g04<fR6%1@R<f1R?#1R0g00Z0f2R4#1?3?@g00T`R2f3R7/24127?33R9[124?124@532%17?34?[R3f4#1?374\9A74?@P@n2001000000120000000W1W0W2P3^10^0<^26P@g00U>R@#6#4#=R6%4@#4#6#<g013J5;6g01@4#0#0#0#0#0#0#0#8,96R@126@,:2O4b3o"). Qed.
Lemma bv5_15 : (15%bv : bv 5) = Z_to_bv 5 (Z.of_nat 15).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h02b1h12b2h21nh31Hp;1p;3p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710R9p8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7P9p8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8g00MSj13Tg00TFj32Tg00O6j21Tg04;Jj36Tg00LPj1=Tg00ePj14Tg00M5j1;Tg01g6j18Tg04H0j37Tg01=3j15Tg01OLj19Tg01hPj2:Tg00R2j2<Tf0R@#5#5p=0g04<fR6%3@R<f1R?#3R0g00Z0f2R4#3?2?@g00T`R2f3R7/14117?32R9[114?114@522%37?24?[R3f4#3?274\9A64?@P@n2001000000120000000W1W0W2P3^10^0<^26P@g00U>R@#=#4#;R6%4@#4#4#8g013J576g01@4#5#0#0#0#0#0#0#0#9,:6R@116@,<2O4b3o"). Qed.
Lemma bv5_17 : (17%bv : bv 5) = Z_to_bv 5 (Z.of_nat 17).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h02b1h12b2h21nh31Hp;1p;3p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70R9P=p8P9P>p8P9P?p8P9P<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710R9p8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7P9p8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8g00MSj12Tg00TFj31Tg00O6j23Tg04;Jj37Tg00LPj15Tg00ePj16Tg00M5j1<Tg01g6j1;Tg04H0j3:Tg01=3j14Tg01OLj18Tg01hPj29Tg00R2j2=Tf0R@#4#4p=0g04<fR6%2@R<f1R?#2R0g00Z0f2R4#2?1?@g00T`R2f3R7/34137?31R9[134?134@512%27?14?[R3f4#2?174\9A74?@P@n2001000000120000000W1W0W2P3^10^0<^26P@g00U>#5R@#6#<R6%5@#5#6#;g013J5:6g01@4#4#0#0#0#0#0#0#0#0#8,96R@136@,=2O4b3o"). Qed.

Lemma some_inj : forall {T} (a b : T), Some a = Some b -> a = b.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "p'0h01Hh12H0h22H1h31Th41ah51bh61ei001oi011tp;1p;2p;3p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6g007HR8p4p710R9p8P6P8p4p7210R:p8P6p1007ep4p710R6p8p1008Cp4p710R;P7p8P;P6p8p1008`p4p70R<P2p8P<P7p8P<P9p8P<P:p8P<P6p8P<p1009Np4p710R<p8p1009kp605611111000p100;1p4p741110R=p8p100;np605611111000R>P=p8p100=:p4p7210R?P7p8P?P9p8P?P:p8P?P6p8P?p100=fp4p710p8p100>mp605611111000R?P>p8P?P=p8p100@:p605611111000R>P?p8P>P=p8p100ADp6054111000R?p100BIp4p710R@p8P?P=p8P?p100CDp4p7511110RAp8p100DAp4p711RBP@p8PBp100E?p4p771111110p8PBPAp8p100FKp4p711RBP=p8PBp100G<p4p741110p8p100HBp4p70RBP7p8PBP9p8PBP:p8PBP6p8p100I8p6051000RBP9p8PBP:p8p100J<p4p70RBP>p8PBP?p8PBP@p8PBP=p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710RBp8P7P<p8P7P5p8P7P0p8p103WUR7p6051001R?P1p8P?P;p8P?P<p8P?P5p8P?P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7PBp8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P@p8P6P=p8P6PAp8p200RAP9p8PAP:p8g02NOR:j12Tg02O1j20Tg00TFj31TP8j63Tf0R8f1R9f2R6#21069106831f3R=#2R@P=P:f4R:f5P8P8P=n10110000021010100X6@10=610=9P8E3A1=69A1:=6P8W2P8O1b1W0W5W4X3Ao"). Qed.

Lemma CEIL_eq : alloc_ceiling = CEIL.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70RAP=p8PAP>p8PAP?p8PAP<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710RAp8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7PAp8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8p108BCp6051000R@P8p8P@P9p8g00R2j20Tg00T`g08CH'0o"). Qed.
Lemma KHI_eq : kHighMemBeg = KHI.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70RAP=p8PAP>p8PAP?p8PAP<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710RAp8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7PAp8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8p108BCp6051000R@P8p8P@P9p8g00R2j20Tg00T`g08@<'0o"). Qed.
Lemma FLOOR_eq : bottomup_floor = FLOOR.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h01zp;1p;3p;2p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6g007eR6p4p710R:p8p1008Cp4p710R;P7p8P;P:p8p1008`p4p70R<P2p8P<P7p8P<P8p8P<P9p8P<P:p8P<p1009Np4p710R<p8p1009kp605611111000p100;1p4p741110R=p8p100;np605611111000R>P=p8p100=:p4p7210R?P7p8P?P8p8P?P9p8P?P:p8P?p100=fp4p710p8p100>mp605611111000R?P>p8P?P=p8p100@:p605611111000R>P?p8P>P=p8p100ADp6054111000R?p100BIp4p710R@p8P?P=p8P?p100CDp4p7511110RAp8p100DAp4p711RBP@p8PBp100E?p4p771111110p8PBPAp8p100FKp4p711RBP=p8PBp100G<p4p741110p8p100HBp4p70RBP7p8PBP8p8PBP9p8PBP:p8p100I8p6051000RBP8p8PBP9p8p100J<p4p70RBP>p8PBP?p8PBP@p8PBP=p8P4p4p7210R4P7p8P4P:p8p100K7p4p7210P:p8p100KVp4p73110P:p8p103T5p6051000R7p1016ap4p710RBp8P7P<p8P7P5p8P7P0p8p103WUR7p6051001R?P1p8P?P;p8P?P<p8P?P5p8P?P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7PBp8P7P0p8P4p60521000R4P2p8P4P:p8P4P0p8p100L2p4p710P:p8P0P:p8p105Eip6054111000R:P@p8P:P=p8P:PAp8p108BCp6051000RAP8p8PAP9p8g00ePj13Tg01g6j14Tg00TFj37Tg00R2j26TP6j65Tg00LPj12Tf0R6#2#3#2#3p=0%26#2p=1g00T`R9g00U>#0#0#0#0#0#0#0#0#3#1#1#1#1#1#1#4g08DGRA9796X09169Ag08EGg08FKE5o"). Qed.

Lemma Z_to_bv64_m1 : forall m1, m1 = two64 - 1 -> Z_to_bv 64 m1 = Z_to_bv 64 (-1).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h01Hh12b1h22b2h32m1h41nh51zp;1p;2p;3p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6g007eR6p4p710R:p8p1008Cp4p710R;P7p8P;P:p8p1008`p4p70R<P2p8P<P7p8P<P8p8P<P9p8P<P:p8P<p1009Np4p710R<p8p1009kp605611111000p100;1p4p741110R=p8p100;np605611111000R>P=p8p100=:p4p7210R?P7p8P?P8p8P?P9p8P?P:p8P?p100=fp4p710p8p100>mp605611111000R?P>p8P?P=p8p100@:p605611111000R>P?p8P>P=p8p100ADp6054111000R?p100BIp4p710R@p8P?P=p8P?p100CDp4p7511110RAp8p100DAp4p711RBP@p8PBp100E?p4p771111110p8PBPAp8p100FKp4p711RBP=p8PBp100G<p4p741110p8p100HBp4p70RBP7p8PBP8p8PBP9p8PBP:p8p100I8p6051000RBP8p8PBP9p8p100J<p4p70RBP>p8PBP?p8PBP@p8PBP=p8P4p4p7210R4P7p8P4P:p8p100K7p4p7210P:p8p100KVp4p73110P:p8p103T5p6051000R7p1016ap4p710RBp8P7P<p8P7P5p8P7P0p8p103WUR7p6051001R?P1p8P?P;p8P?P<p8P?P5p8P?P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7PBp8P7P0p8P4p60521000R4P2p8P4P:p8P4P0p8p100L2p4p710P:p8P0P:p8p105Eip6054111000R:P@p8P:P=p8P:PAp8p108BCp6051000RAP8p8PAP9p8g01g6j1=Tg01iSj2<Tg00TFj30Tg00LPj11Tg00M5j1;Tg00MSj12Tg01hPj24Tg01S9j1:Tg00O6j23Tg04;Jj39Tg08GSj26Tg00R2j28Tg08H9j27TP6j65Tg00T`R6f0R9g02VAg00U>RA#='<R8506P6P8%1A#1#1#1#1#1#;R:#214:9%:ARA,4:R=30X36g04<fR@%29R0f1R4#2R2g00Z0f2R7#2?049f3RB/3713B4506R3[13741379506%2B?074[R1f4#2?0B7\3A9749P9n2001000000120000000W2W1W4P1^22^10^4@P9P:14:8R@P=P616:8R013:=R=9069X56P616:AR2A0609X561862P=17:AE513:@17:8E5O4b0P4P9E5W0W3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma reserved_free_above : forall model (lo n : word),
  (exists rx : list (word * word),
     vm_reserved (m_vmmaps model) = segments_reserved SEGS ++ rx
     /\ Forall (resx_entry_ok A) rx
     /\ (length rx <= n_resx A)%nat
     /\ sum_sizes rx <= resx_bytes A) ->
  img_hi A <= bv_unsigned lo ->
  bv_unsigned lo + bv_unsigned n <= KHI ->
  region_free (vm_reserved (m_vmmaps model)) lo n = true.
Proof.
  intros model lo n (rx & Hres & HG & _ & _) Hlo Hkhi. rewrite Hres.
  apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.region_free_intro. intros b s Hin. apply in_app_iff in Hin as [Hin|Hin].
  - pose proof (proj1 (Forall_forall _ _) RES_hullH _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2. right. lia.
  - (* [comment removed for export] *)
    pose proof (proj1 (Forall_forall _ _) HG _ Hin) as (_ & _ & _ & _ & Hk & _).
    cbn [fst] in Hk. left. lia.
Qed.

(* [comment removed for export] *)
Lemma reserved_free_hull_apart : forall model (lo n : word),
  (exists rx : list (word * word),
     vm_reserved (m_vmmaps model) = segments_reserved SEGS ++ rx
     /\ Forall (resx_entry_ok A) rx
     /\ (length rx <= n_resx A)%nat
     /\ sum_sizes rx <= resx_bytes A) ->
  (bv_unsigned lo + bv_unsigned n <= img_lo A \/ img_hi A <= bv_unsigned lo) ->
  bv_unsigned lo + bv_unsigned n <= KHI ->
  region_free (vm_reserved (m_vmmaps model)) lo n = true.
Proof.
  intros model lo n (rx & Hres & HG & _ & _) Hlo Hkhi. rewrite Hres.
  apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.region_free_intro. intros b s Hin. apply in_app_iff in Hin as [Hin|Hin].
  - pose proof (proj1 (Forall_forall _ _) RES_hullH _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2.
    pose proof (u64_range s). destruct Hlo; [left | right]; lia.
  - pose proof (proj1 (Forall_forall _ _) HG _ Hin) as (_ & _ & _ & _ & Hk & _).
    cbn [fst] in Hk. left. lia.
Qed.

(* [comment removed for export] *)
Lemma reserved_free_inside : forall E cs R FULL model (iv : word * word) (lo n : word),
  CSOK E cs R FULL model ->
  In iv (vm_maps (m_vmmaps model)) ->
  bv_unsigned (fst iv) <= bv_unsigned lo ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned (fst iv) + bv_unsigned (snd iv) ->
  region_free (vm_reserved (m_vmmaps model)) lo n = true.
Proof.
  intros E cs R FULL model iv lo n HC Hin H1 H2.
  pose proof (proj1 (Forall_forall _ _) (co_mres _ _ _ _ _ _ _ _ _ _ _ HC) iv Hin) as HD.
  apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.region_free_intro. intros b s Hb.
  pose proof (proj1 (Forall_forall _ _) HD (b, s) Hb) as D.
  unfold iv_disjoint in D. cbn [fst snd] in D. destruct D as [D|D]; [left|right]; lia.
Qed.

(* [comment removed for export] *)
Lemma vis_add_inv : forall cs b n k cs2,
  vis_add A LIMIT cs b n k = Some cs2 ->
  exists nhi, xhi (kn cs) n = Some nhi /\
  cs2 = ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_facts A (kn cs) (a_maps cs) b n ++ k) (nxt cs))
            (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
            ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs) (a_hna cs) (a_hlz cs).
Proof.
  intros cs b n k cs2 Hv. rewrite vis_add_eq in Hv. (* [comment removed for export] *) unfold vis_add_ref in Hv.
  destruct (split_lit b) as [bb bk]. destruct (shadow_of A (kn cs) b n) as [[sb sk] sn] eqn:Hsh.
  destruct (xhi (kn cs) n) as [nhi|]; [|discriminate].
  match type of Hv with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  injection Hv as <-. exists nhi. split; [reflexivity|]. unfold shadow_facts. rewrite Hsh. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma in_allow_ext : forall E cs cs', a_vis cs' = a_vis cs -> in_allow A E cs' = in_allow A E cs.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h01ph11Eh21Hh32csh43cs'h51lh61zp;2p;1p;3p;6p;4p;5p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0g003iR4p4p710p8P0P4p4p7210p8P0p1004FR5p4p710R6p8P0p1004cp4p7210p8P0g005BR0p4p710R7p8p1005^p4p70R8p1006Np4p710R9p8P8p1006jp4p710R:p8P8p1007Hp4p7210R;p8P8g007eR8p4p710R<p8p1008Cp4p710R=P9p8P=P<p8p1008`p4p70R>P2p8P>P9p8P>P:p8P>P;p8P>P<p8P>p1009Np4p710R>p8p1009kp605611111000p100;1p4p741110R?p8p100;np605611111000R@P?p8p100=:p4p7210RAP9p8PAP:p8PAP;p8PAP<p8PAp100=fp4p710p8p100>mp605611111000RAP@p8PAP?p8p100@:p605611111000R@PAp8P@P?p8p100ADp6054111000RAp100BIp4p710RBp8PAP?p8PAp100CDp4p7511110RCp8p100DAp4p711RDPBp8PDp100E?p4p771111110p8PDPCp8p100FKp4p711RDP?p8PDp100G<p4p741110p8p100HBp4p70RDP9p8PDP:p8PDP;p8PDP<p8p100I8p6051000RDP:p8PDP;p8p100J<p4p70RDP@p8PDPAp8PDPBp8PDP?p8P5p4p7210R5P9p8P5P<p8p100K7p4p7210P<p8p100KVp4p73110P<p8p103T5p6051000R9p1016ap4p710RDp8P9P>p8P9P6p8P9P7p8p103WUR9p6051001RAP1p8PAP=p8PAP>p8PAP6p8PAP7p8P9p60521000R9P1p8P9P5p8p103c\R5p6051001R9P1p8P9P3p8P9PDp8P9P7p8P5p60521000R5P2p8P5P<p8P5P7p8p100L2p4p710P<p8P7P<p8p105Eip6054111000R<PBp8P<P?p8P<PCp8p108BCp6051000RCP:p8PCP;p8g00N6j2CTg00NVj1BTg08Rnj11Tg00TFj36Tg08m0j3<j4:TP4j3ATg07\Oj24Tg00O`j23Tg00P=j3=Tg00PZj29Tg00Q7j22Tg00QTj25TP0j30Tg08n1j3;Tg08noj38Tg00VCj27Tg00R2j2@TP8j6?Tg08omj5>Tg02bHg02XCR8g02keR0/C0R4#BR;f0RC#1f1R:#136g00T`R<g00UcR?p,1ARBf3R7;<:f2R59<B7P;%17R2f6R9AA00CRD'4R3/35A=00CR0,49,93,25'5X04R3=04CA;B9C/35A8B9C,25'5X04R9=04C'7f4R1#1RA9043A049A'756?X5;f5R;/4DRD/3:14;0,9D,2:'5X04=042A;B;C/3:A8B;C,2:'5X04=042'7,@?%15P:E?PBP1P5PCC:PBP1P7PCC:56?eX6<D>W2X48W3W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kind_none (k : mkind) : bool := match k with KNONE | KNONELAZY => true | _ => false end.
Definition kind_lazy (k : mkind) : bool := match k with KRWLAZY | KNONELAZY => true | _ => false end.

Record grant_post (kd : mkind) (a n : word) (model model' : Model) : Prop := GP {
  gp_maps : vm_maps (m_vmmaps model') = (a, n) :: vm_maps (m_vmmaps model);
  gp_res : vm_reserved (m_vmmaps model') = vm_reserved (m_vmmaps model);
  gp_noacc : vm_noaccess (m_vmmaps model') = (if kind_none kd then (a, n) :: vm_noaccess (m_vmmaps model) else vm_noaccess (m_vmmaps model));
  gp_lazy : m_vm_lazy model' = (if kind_lazy kd then (a, n) :: m_vm_lazy model else m_vm_lazy model);
  gp_mat : m_vm_materialized model' = m_vm_materialized model;
  gp_limit : vm_limit (m_vmmaps model') = vm_limit (m_vmmaps model);
  gp_brk : vm_brk (m_vmmaps model') = vm_brk (m_vmmaps model);
  gp_sbrk : vm_start_brk (m_vmmaps model') = vm_start_brk (m_vmmaps model);
  gp_mbase : vm_mmap_base (m_vmmaps model') = vm_mmap_base (m_vmmaps model);
  gp_halted : m_halted model' = m_halted model;
  gp_fds : m_fds model' = m_fds model;
  gp_fs : m_fs model' = m_fs model;
  gp_tid : m_tid model' = m_tid model;
  gp_isp : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model);  (* [comment removed for export] *)
  gp_kernel : m_kernel model' = m_kernel model;
  gp_rdr : m_channel_reader model' = m_channel_reader model }.

(* [comment removed for export] *)
Lemma vdso_top_eq : forall h h',
  vm_mmap_base h' = vm_mmap_base h -> vm_init_sp h' = vm_init_sp h ->
  vdso_top h' = vdso_top h.
Proof. intros h h' E1 E2. unfold vdso_top, mmap_top, alloc_top. rewrite E1, E2. reflexivity. Qed.

Definition grant_mem (kd : mkind) (a n : word) (FULL FULL' : word -> option byte) : Prop :=
  (forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x -> FULL' x = FULL x)
  /\ (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n ->
        FULL' x = if kind_none kd then None else Some (Z_to_bv 8 0)).

(* [comment removed for export] *)
Lemma vis_grant_out : forall kd (a n : word) model model' E cs cs1 (x : word),
  grant_post kd a n model model' ->
  a_vis cs1 = a_vis cs ->
  0 < bv_unsigned n -> bv_unsigned a mod 4096 = 0 -> bv_unsigned n mod 4096 = 0 ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x) ->
  VIS E cs1 model' x = VIS E cs model x.
Proof.
  intros kd a n model model' E cs cs1 x GPo Hvis Hn Hal Hnl Hx.
  unfold vis. rewrite (gp_maps _ _ _ _ _ GPo), (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo).
  rewrite (in_allow_ext E cs cs1 Hvis).
  rewrite in_ivs_cons. cbn [fst snd].
  assert (T : ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + bv_unsigned n))%bool = false).
  { apply andb_false_iff. destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
  rewrite T. cbn [orb].
  assert (P : page_in_ranges (page_base x) ((a, n) :: m_vm_lazy model) = page_in_ranges (page_base x) (m_vm_lazy model)).
  { apply page_in_ranges_cons_out; [|exact Hn].
    pose proof (page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + bv_unsigned n) Hal ltac:(rewrite Z.add_mod, Hal, Hnl by lia; reflexivity) Hx).
    unfold page_size. lia. }
  destruct (kind_none kd); destruct (kind_lazy kd); rewrite ?in_ivs_cons; cbn [fst snd]; rewrite ?T, ?P; cbn [orb]; reflexivity.
Qed.

Lemma grant_wf : forall kd a n model model',
  grant_post kd a n model model' -> model_ivs_wf model ->
  bv_unsigned a + bv_unsigned n <= 2 ^ 64 -> model_ivs_wf model'.
Proof.
  intros kd a n model model' GPo (W1 & W2 & W3 & Wsp) Hb. unfold model_ivs_wf.
  rewrite (gp_maps _ _ _ _ _ GPo), (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo).
  assert (iv_wf (a, n)) by (unfold iv_wf, B, S; cbn; lia).
  split; [apply ivs_wf_cons; assumption|].
  split; [destruct (kind_none kd); try apply ivs_wf_cons; assumption|].
  split; [destruct (kind_lazy kd); try apply ivs_wf_cons; assumption|].
  unfold init_sp_ok in *. rewrite (gp_isp _ _ _ _ _ GPo). exact Wsp.
Qed.

(* [comment removed for export] *)
Lemma grant_eager_le : forall kd a n model model',
  grant_post kd a n model model' -> model_ivs_wf model -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  eager_used model' <= eager_used model + (if (kind_none kd || kind_lazy kd)%bool then 0 else bv_unsigned n).
Proof.
  intros kd a n model model' GPo Hwf Hb.
  pose proof (grant_wf kd a n model model' GPo Hwf Hb) as Hwf'.
  rewrite (eager_used_sem model' Hwf'), (eager_used_sem model Hwf).
  rewrite (gp_maps _ _ _ _ _ GPo).
  set (C := vm_noaccess (m_vmmaps model) ++ m_vm_lazy model).
  set (C' := vm_noaccess (m_vmmaps model') ++ m_vm_lazy model').
  cbn [sum_count].
  assert (MONO : sum_count (fun x => negb (covered C' x)) (vm_maps (m_vmmaps model))
                 <= sum_count (fun x => negb (covered C x)) (vm_maps (m_vmmaps model))).
  { apply sum_count_negb_covered_mono. intros x Hx. subst C C'.
    rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). rewrite covered_app in Hx. rewrite covered_app.
    apply orb_true_iff in Hx. apply orb_true_iff.
    destruct Hx as [Hx|Hx]; [left|right]; [destruct (kind_none kd) | destruct (kind_lazy kd)]; try exact Hx;
      unfold covered in *; cbn [existsb]; rewrite Hx; apply orb_true_r. }
  assert (HEAD : iv_count (fun x => negb (covered C' x)) (a, n) <= (if (kind_none kd || kind_lazy kd)%bool then 0 else bv_unsigned n)).
  { destruct (kind_none kd || kind_lazy kd)%bool eqn:Hk.
    - unfold iv_count, B, S. cbn [fst snd]. rewrite zcount_false; [lia|]. intros x Hx.
      pose proof (u64_range n). rewrite Z2Nat.id in Hx by lia. apply negb_false_iff.
      subst C'. rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). rewrite covered_app.
      assert (IN : in_iv (a, n) x = true).
      { unfold in_iv, in_rng, B, S. cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      apply orb_prop in Hk as [Hk|Hk]; rewrite Hk; unfold covered; cbn [existsb]; rewrite IN; cbn [orb];
        [reflexivity | apply orb_true_r].
    - unfold iv_count, S. cbn [snd]. pose proof (u64_range n).
      pose proof (zcount_le_len (fun x => negb (covered C' x)) (B (a, n)) (Z.to_nat (bv_unsigned n))). lia. }
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition maps_apart (E : env) (ms : list amap) (lo n : Z) : Prop :=
  forall m, In m ms -> is_fog m = false ->
    lo + n <= bv_unsigned (edenot E (am_base m)) \/
    bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= lo.

Lemma maps_apart_of_region_free : forall E ms model (a n : word),
  maps_match E ms (vm_maps (m_vmmaps model)) ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a n = true ->
  maps_apart E ms (bv_unsigned a) (bv_unsigned n).
Proof.
  intros E ms model a n Hmaps Hrf m Hin Hnf.
  rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf].
  exact (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.region_free_In _ a n (edenot E (am_base m)) (edenot E (am_len m)) Hrf (maps_match_In E ms _ m Hmaps Hin Hnf)).
Qed.

Lemma inside_maps_apart : forall E M k ms b o l lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n ->
  inside_maps k ms b o l = true ->
  estart E (SA b o) + elenZ E l <= lo \/ lo + n <= estart E (SA b o).
Proof.
  intros E M k ms b o l lo n HK Hap. induction ms as [|m ms IH]; intros H; [discriminate|].
  cbn [inside_maps] in H. apply orb_prop in H as [H|H].
  - apply andb_prop in H as [Hnf H]. apply negb_true_iff in Hnf.
    pose proof (xinside_sound SEGS E M k b o l (am_base m) 0 (am_len m) HK H) as [I1 I2].
    unfold estart in I1, I2 |- *. cbn [a_base a_off] in *. unfold elenZ in *.
    destruct (Hap m (or_introl eq_refl) Hnf); lia.
  - apply IH; [|exact H]. intros m' Hm'. apply Hap. right. exact Hm'.
Qed.

(* [comment removed for export] *)
Definition isp_facts (E : env) : Prop :=
  sp_window_lo <= uE E e_sp0 <= sp_window_hi /\ uE E e_sppg = pagedown (uE E e_sp0).

(* [comment removed for export] *)
Lemma u_e_top : forall E, isp_facts E -> uE E e_top = utop E.
Proof.
  intros E [Hsp Hpg]. pose proof (utop_bounds E) as UB. unfold utop in UB |- *.
  unfold e_top, eaddz, uE in *. rewrite mkAlu_denot, edenot_lit, u_add64, u_lit64. rewrite Hpg.
  unfold two64, sp_window_lo in *. pose proof (u64_range (edenot E e_sp0)).
  replace ((-8388608) mod 2 ^ 64) with (2 ^ 64 - 8388608) by reflexivity.
  replace (pagedown (bv_unsigned (edenot E e_sp0)) + (2 ^ 64 - 8388608))
    with ((pagedown (bv_unsigned (edenot E e_sp0)) - 8388608) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small; lia.
Qed.

(* [comment removed for export] *)
Lemma lit_ivs_apart : forall E ms lo n a' m,
  maps_apart E ms lo n -> In (a', m) (lit_ivs ms) -> lo + n <= a' \/ a' + m <= lo.
Proof.
  intros E ms lo n a' m Hap Hin.
  destruct (PlaceLemmasK.lit_ivs_In ms a' m Hin) as ((B0 & B1 & B2) & m0 & Hm0 & Hnf & Hb & Hl).
  pose proof (Hap m0 Hm0 Hnf) as D. rewrite Hb, Hl in D. cbn [edenot] in D.
  unfold two64 in B2. rewrite !u64_lit in D by lia. exact D.
Qed.

(* [comment removed for export] *)
Lemma runs_apart_grant : forall E ms lo n rlo rn k,
  maps_apart E ms lo n -> 0 < n -> In (rlo, rn, k) (PlaceLemmasK.runs ms) -> lo + n <= rlo \/ rlo + rn <= lo.
Proof.
  intros E ms lo n rlo rn k Hap Hn Hin. eapply PlaceLemmasK.runs_apart; [exact Hin | exact Hn |].
  intros a' m Hin'. eapply lit_ivs_apart; [exact Hap | exact Hin'].
Qed.

(* [comment removed for export] *)
Lemma inside_runs_apart : forall E M k ms b o l lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n -> 0 < n ->
  inside_runs k ms b o l = true ->
  estart E (SA b o) + elenZ E l <= lo \/ lo + n <= estart E (SA b o).
Proof.
  intros E M k ms b o l lo n HK Hap Hn H. unfold inside_runs in H.
  destruct (base_range k b) as [[blo bhi]|] eqn:Hb; [|discriminate]. destruct (xhi k l) as [lh|] eqn:Hlh; [|discriminate].
  pose proof (xhi_sound SEGS E M k l lh HK Hlh) as L1. pose proof (base_range_sound SEGS E M k b blo bhi HK Hb) as [B1 B2].
  apply existsb_exists in H as ([[ra rn] rk] & Hin & Hr). apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.leb_le in Hr2.
  pose proof (runs_apart_grant E ms lo n ra rn rk Hap Hn Hin) as D.
  unfold estart, elenZ. cbn [a_base a_off]. lia.
Qed.

Lemma safe_range_apart : forall E M k ms b o l lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n ->
  0 <= lo -> (lo + n <= img_lo A \/ img_hi A <= lo) -> lo + n <= utop E -> isp_facts E -> 0 < n ->   (* [comment removed for export] *)
  safe_range A k ms b o l = true ->
  estart E (SA b o) + elenZ E l <= lo \/ lo + n <= estart E (SA b o).
Proof.
  intros E M k ms b o l lo n HK Hap Hlo0 Hlo Hhi Hsp Hn H. unfold safe_range in H. apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
  - destruct (xhi k l) as [lh|] eqn:Hlh; [|discriminate]. destruct (base_range k b) as [[blo bhi]|] eqn:Hb; [|discriminate].
    pose proof (xhi_sound SEGS E M k l lh HK Hlh) as L1. pose proof (base_range_sound SEGS E M k b blo bhi HK Hb) as [B1 B2].
    unfold estart, elenZ. cbn [a_base a_off].
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H2.
    + (* [comment removed for export] *)
      pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as G. cbn [xt_den] in G.
      pose proof (u_e_top E Hsp) as T. unfold uE in T. rewrite T in G. lia.
    + apply Z.leb_le in H1. lia.
  - eapply inside_maps_apart; eassumption.
  - eapply inside_runs_apart; eassumption.
Qed.

Lemma grant_keep_apart : forall E M k ms K lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n ->
  0 <= lo -> (lo + n <= img_lo A \/ img_hi A <= lo) -> lo + n <= utop E -> isp_facts E -> 0 < n ->   (* [comment removed for export] *)
  grant_keep_b A k ms K = true ->
  match K with KImg _ _ => False | _ => True end ->
  kfoot_apart E K lo n.
Proof.
  intros E M k ms K lo n HK Hap Hlo0 Hlo Hhi Hsp Hn H HnI. unfold kfoot_apart, kfoot.
  destruct K as [[b o] w v|[b o] l|[b o] l kb|ilo ihi|e m|e rlo rhi|[b o] l|a1 n1 a2 n2|[b o] l fc|[b o] l]; cbn [grant_keep_b] in H;
    try exact I; [apply andb_prop in H as [Hw H]; apply Nat.leb_le in Hw| | | destruct HnI | | |];
    pose proof (safe_range_apart E M k ms b o _ lo n HK Hap Hlo0 Hlo Hhi Hsp Hn H) as D; try lia.
  rewrite elenZ_lit'' in D by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma kn_grant_filter_ok : forall E M M' k ms lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n ->
  0 <= lo -> (lo + n <= img_lo A \/ img_hi A <= lo) -> lo + n <= utop E -> isp_facts E -> 0 < n ->   (* [comment removed for export] *)
  (forall x : word, bv_unsigned x < lo \/ lo + n <= bv_unsigned x -> M' x = M x) ->
  know_ok SEGS E M' (kn_grant_filter A k ms).
Proof.
  intros E M M' k ms lo n HK Hap Hlo0 Hlo Hhi Hsp Hn Hout. unfold kn_grant_filter.
  pose proof (kimg_clip_in_hull' (List.filter (grant_keep_b A k ms) k)) as Hhull.
  unfold know_ok. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) Hhull K Hin) as HKh.
  apply kimg_clip_incl in Hin. apply filter_In in Hin as [Hin Hkeep].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  eapply kentry_keep_sem'; [exact HKK | | exact Hout].
  destruct K as [| | |ilo ihi| | | | | |];
    try (eapply grant_keep_apart; [exact HK | exact Hap | exact Hlo0 | exact Hlo | exact Hhi | exact Hsp | exact Hn | exact Hkeep | exact I]).
  (* [comment removed for export] *)
  unfold kfoot_apart, kfoot. cbn in HKh. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma regs_ok_regupd_same : forall E sr R n (v : word),
  regs_ok E sr R -> (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = v ->
  regs_ok E sr (regupd R (Z_to_bv 5 (Z.of_nat n)) v).
Proof.
  intros E sr R n v HR Hn Hv r.
  assert (Hne : Z_to_bv 5 (Z.of_nat n) <> 0%bv).
  { intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz.
    change (bv_modulus 5) with 32%Z in Hz. rewrite Z.mod_small in Hz by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z in Hz by reflexivity. lia. }
  destruct (bv_eqb r (Z_to_bv 5 (Z.of_nat n))) eqn:Hr.
  - apply (proj1 (bv_eqb_eq _ _)) in Hr. subst r. rewrite getr_same by exact Hne. rewrite <- Hv. apply HR.
  - assert (Hr' : r <> Z_to_bv 5 (Z.of_nat n)) by (intros ->; rewrite bv_eqb_refl in Hr; discriminate).
    rewrite getr_other by exact Hr'. apply HR.
Qed.

(* [comment removed for export] *)
Lemma grant_new_facts : forall E cs R FULL model (a n : word) nZ,
  CSOK E cs R FULL model ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a n = true ->
  bv_unsigned n = nZ -> 0 < nZ ->
  (bv_unsigned a + nZ <= img_lo A \/ img_hi A <= bv_unsigned a) -> bv_unsigned a + nZ <= utop E ->   (* [comment removed for export] *)
  forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
    in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model)) = false
    /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false
    /\ argH E x = false /\ in_hull A (bv_unsigned x) = false /\ (utop E <=? bv_unsigned x) = false
    /\ VIS E cs model x = false.
Proof.
  intros E cs R FULL model a n nZ HC Hrf Un HnZ Himg HaC x Hx.
  rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf2].
  pose proof (region_free_sem _ a n (bv_unsigned x) Hrf2 ltac:(rewrite Un; lia) ltac:(rewrite Un; lia)) as M0.
  assert (N0 : in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false).
  { destruct (in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model))) eqn:En; [|reflexivity]. exfalso.
    apply (co_nasub _ _ _ _ _ _ _ _ _ _ _ HC) in En. congruence. }
  assert (Hh : in_hull A (bv_unsigned x) = false).
  { unfold in_hull. apply andb_false_iff. destruct Himg; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
  assert (Hc : (utop E <=? bv_unsigned x) = false) by (apply Z.leb_gt; lia).
  repeat split; try assumption.
  - destruct (argH E x) eqn:Ea; [|reflexivity]. pose proof (argH_high _ _ Ea). pose proof (utop_bounds E). lia.
  - unfold vis. rewrite Hh, Hc, M0. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grant_cs1_ok : forall E cs R FULL model kd (a n : word) nZ model' FULL' sr' R' knew be ne nhi (eager : bool) ylo' nx',
  CSOK E cs R FULL model ->
  bv_unsigned n = nZ -> 0 < nZ -> nZ mod 4096 = 0 -> bv_unsigned a mod 4096 = 0 ->
  (bv_unsigned a + nZ <= img_lo A \/ img_hi A <= bv_unsigned a) -> bv_unsigned a + nZ <= utop E ->   (* [comment removed for export] *)
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a n = true ->
  grant_post kd a n model model' -> grant_mem kd a n FULL FULL' ->
  regs_ok E sr' R' ->
  edenot E be = a -> edenot E ne = n ->
  know_ok SEGS E (MR E cs model' FULL') knew ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false -> nZ <= nhi ->
  (eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
  ylo' <= a_ylo cs ->      (* [comment removed for export] *)
  (forall m, In m (a_maps cs) -> is_hole m = true ->      (* [comment removed for export] *)
     bv_unsigned a + nZ <= uE E (am_base m) \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned a) ->
  let cs1 := add_entry cs sr' (knew ++ kn_grant_filter A (kn cs) (a_maps cs)) nx' (AM be ne kd) nhi eager ylo' in
  CSOK E cs1 R' FULL' model'
  /\ (forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
        MR E cs1 model' FULL' x = MR E cs model FULL x)
  /\ MR E cs1 model' FULL' = MR E cs model' FULL'.
Proof.
  intros E cs R FULL model kd a n nZ model' FULL' sr' R' knew be ne nhi eager ylo' nx'
         HC Un HnZpos HnZal Hal Himg_a HaC Hrf GPo [GM1 GM2] Hregs Hbase HneE Hknew Hkind Hkfog Hnhi Hbudget Hylo Hholes cs1.
  pose proof (u64_range a) as Ra. pose proof (utop_bounds E) as UB.
  pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as [ISP1 ISP2]. pose proof ISP2 as ISP. unfold sp_window_lo, sp_window_hi in ISP2.
  pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3).
  pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) as Hmaps.
  pose proof (maps_apart_of_region_free E (a_maps cs) model a n Hmaps Hrf) as Hapart. rewrite Un in Hapart.
  pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
  pose proof (grant_new_facts E cs R FULL model a n nZ HC Hrf Un HnZpos Himg_a HaC) as NEW.
  (* [comment removed for export] *)
  assert (VISOUT : forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
                    VIS E cs1 model' x = VIS E cs model x).
  { intros x Hx. eapply vis_grant_out; [exact GPo | reflexivity | rewrite Un; lia | exact Hal | rewrite Un; exact HnZal | rewrite Un; exact Hx]. }
  assert (HIDOUT : forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
                    HID E cs1 model' x = HID E cs model x).
  { intros x Hx. unfold hid. rewrite (VISOUT x Hx). reflexivity. }
  assert (MROUT : forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
                   MR E cs1 model' FULL' x = MR E cs model FULL x).
  { intros x Hx. unfold Mr, mrestrict. rewrite (HIDOUT x Hx). rewrite (GM1 x) by (rewrite Un; exact Hx). reflexivity. }
  assert (MRSAME : MR E cs1 model' FULL' = MR E cs model' FULL').
  { unfold Mr. rewrite (hid_ext A argH E cs cs1 model') by reflexivity. reflexivity. }
  split; [| split; [exact MROUT | exact MRSAME]].
  (* [comment removed for export] *)
  pose proof (grant_wf kd a n model model' GPo Hwf ltac:(rewrite Un; lia)) as Hwf'.
  destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xhna Xhlz Xtidv Xmres Xvdso Xrdr].
  constructor.
  all: unfold cs1, add_entry; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn s_regs s_log s_know s_next mk_ss].
  all: try change (ALLOW E (ACS ?s ?m ?t ?y ?e (a_vis cs) (a_ghost cs) ?ab ?br ?fd ?ti ?hn ?hl)) with (ALLOW E cs).
  - (* [comment removed for export] *) exact Hregs.
  - (* [comment removed for export] *) reflexivity.
  - (* [comment removed for export] *) apply Forall_app. split.
    + unfold cs1, add_entry in MRSAME. cbn [kn a_ss s_know mk_ss] in MRSAME. rewrite MRSAME. exact Hknew.
    + eapply kn_grant_filter_ok; [exact Xknow | exact Hapart | lia | exact Himg_a | exact HaC | exact ISP | exact HnZpos | exact MROUT].
  - (* [comment removed for export] *) rewrite (gp_halted _ _ _ _ _ GPo). exact Xhalt.
  - (* [comment removed for export] *) unfold fds_ok in *. rewrite (gp_fds _ _ _ _ _ GPo), (gp_fs _ _ _ _ _ GPo). exact Xfds.
  - (* [comment removed for export] *) rewrite (gp_fs _ _ _ _ _ GPo). exact Xfs.
  - (* [comment removed for export] *) rewrite (gp_tid _ _ _ _ _ GPo). exact Xtid.
  - (* [comment removed for export] *) rewrite (gp_res _ _ _ _ _ GPo). exact Xres.
  - (* [comment removed for export] *) rewrite (gp_limit _ _ _ _ _ GPo). exact Xlimit.
  - (* [comment removed for export] *) rewrite (gp_maps _ _ _ _ _ GPo). rewrite <- Hbase, <- HneE. apply maps_match_cons; [exact Hkfog | exact Xmaps].
  - (* [comment removed for export] *)
    rewrite (gp_res _ _ _ _ _ GPo), (gp_maps _ _ _ _ _ GPo). apply Forall_cons.
    + intros Hh. exfalso. unfold is_hole in Hh. cbn [am_kind] in Hh. destruct kd; cbn in Hkfog, Hh; discriminate.
    + apply Forall_forall. intros m Hm Hk. destruct (proj1 (Forall_forall _ _) Xholes m Hm Hk) as [F1 F2]. split; [|lia].
      intros iv Hiv. apply in_app_iff in Hiv as [Hiv|[<-|Hiv]].
      * apply F1. apply in_app_iff. left. exact Hiv.
      * cbn [fst snd]. rewrite Un. pose proof (Hholes m Hm Hk). lia.
      * apply F1. apply in_app_iff. right. exact Hiv.
  - (* [comment removed for export] *) rewrite (gp_maps _ _ _ _ _ GPo). constructor; [|exact Xseps].
    apply Forall_forall. intros [b s] Hin. unfold iv_disjoint. cbn [fst snd]. rewrite Un.
    rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf2].
    pose proof (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.region_free_In _ a n b s Hrf2 Hin). rewrite Un in *. lia.
  - (* [comment removed for export] *) exact Hwf'.
  - (* [comment removed for export] *) rewrite (gp_maps _ _ _ _ _ GPo). apply Forall_cons; [|exact Xbounds]. cbn [fst snd]. rewrite Un. repeat split; lia.
  - (* [comment removed for export] *) rewrite (gp_lazy _ _ _ _ _ GPo). destruct (kind_lazy kd); [apply Forall_cons; [cbn [fst snd]; rewrite Un; lia|]|]; exact Xlazyb.
  - (* [comment removed for export] *) intros z Hz. rewrite (gp_maps _ _ _ _ _ GPo). rewrite in_ivs_cons. rewrite (gp_noacc _ _ _ _ _ GPo) in Hz.
    destruct (kind_none kd); [rewrite in_ivs_cons in Hz; apply orb_prop in Hz as [Hz|Hz]; [rewrite Hz; reflexivity|]|];
      rewrite (Xnasub z Hz); apply orb_true_r.
  - (* [comment removed for export] *) apply Forall_cons.
    + cbn [am_kind amap_den am_base am_len]. intros Hk. rewrite (gp_noacc _ _ _ _ _ GPo).
      replace (kind_none kd) with true by (destruct Hk as [-> | ->]; reflexivity). left. unfold amap_den. cbn [am_base am_len]. rewrite Hbase, HneE. reflexivity.
    + apply Forall_forall. intros m Hm Hk. rewrite (gp_noacc _ _ _ _ _ GPo).
      pose proof (proj1 (Forall_forall _ _) Xnone m Hm Hk) as X. destruct (kind_none kd); [right|]; exact X.
  - (* [comment removed for export] *) apply Forall_cons.
    + cbn [am_kind am_base am_len]. intros Hk x Hx. subst kd. rewrite Hbase, HneE, Un in Hx. cbn in Hkind.
      rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). cbn [kind_none kind_lazy]. split.
      * exact (proj1 (proj2 (NEW x Hx))).
      * destruct (page_of_byte_in_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal ltac:(rewrite Z.add_mod, Hal, HnZal by lia; reflexivity) Hx) as [P1 P2].
        apply page_in_ranges_cons_in; unfold page_size; rewrite ?Un; lia.
    + apply Forall_forall. intros m Hm Hk x Hx.
      destruct (proj1 (Forall_forall _ _) Xkinds m Hm Hk x Hx) as [K1 K2].
      rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). split.
      * destruct (kind_none kd); [|exact K1]. rewrite in_ivs_cons. cbn [fst snd]. rewrite K1, Un.
        pose proof (Hapart m Hm ltac:(unfold is_fog; rewrite Hk; reflexivity)) as D.
        replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + nZ))%bool with false; [reflexivity|].
        symmetry. apply andb_false_iff. destruct D; [right; apply Z.ltb_ge | left; apply Z.leb_gt]; lia.
      * destruct (kind_lazy kd); [|exact K2]. rewrite page_in_ranges_cons, K2. apply orb_true_r.
  - (* [comment removed for export] *) rewrite (gp_res _ _ _ _ _ GPo), (gp_maps _ _ _ _ _ GPo).
    rewrite sum_sizes_app in *. cbn [sum_sizes snd]. rewrite Un. cbn [sum_sizes] in Xtotsz. lia.
  - (* [comment removed for export] *) rewrite (gp_isp _ _ _ _ _ GPo). exact (conj ISP1 ISP2).
  - (* [comment removed for export] *) rewrite (gp_brk _ _ _ _ _ GPo). exact Xbrk.
  - (* [comment removed for export] *) rewrite (gp_brk _ _ _ _ _ GPo), (gp_sbrk _ _ _ _ _ GPo). exact Xsbrk.
  - (* [comment removed for export] *) pose proof (grant_eager_le kd a n model model' GPo Xwf ltac:(rewrite Un; lia)) as EG. rewrite Hkind in EG.
    destruct eager; cbn [negb] in EG; [|lia]. rewrite Un in EG. lia.
  - (* [comment removed for export] *) exact Xabytes.
  - (* [comment removed for export] *) destruct Xminv as [N1 N2 N3 N4 N5]. constructor; rewrite ?(gp_mat _ _ _ _ _ GPo), ?(gp_limit _ _ _ _ _ GPo); try assumption.
    + intros p Hp. rewrite (gp_lazy _ _ _ _ _ GPo). destruct (kind_lazy kd); [rewrite page_in_ranges_cons, (N4 p Hp); apply orb_true_r | exact (N4 p Hp)].
    + pose proof (grant_eager_le kd a n model model' GPo Xwf ltac:(rewrite Un; lia)) as EG. rewrite Hkind in EG.
      destruct eager; cbn [negb] in EG; [|lia]. rewrite Un in EG. rewrite Xlimit. specialize (Hbudget eq_refl). lia.
  - (* [comment removed for export] *) intros x Hh Hm Hna Hlz Hgh.
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + nZ)) as [Hlt2|Hge2]].
    + rewrite (GM1 x) by lia. apply Xzero; [rewrite <- (HIDOUT x) by lia; exact Hh | | | | exact Hgh].
      * rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons in Hm. apply orb_prop in Hm as [Hm|Hm]; [|exact Hm].
        apply andb_prop in Hm as [Hm _]. apply Z.leb_le in Hm. cbn [fst] in Hm. lia.
      * rewrite (gp_noacc _ _ _ _ _ GPo) in Hna. destruct (kind_none kd); [rewrite in_ivs_cons in Hna; apply orb_false_iff in Hna as [_ Hna]|]; exact Hna.
      * rewrite (gp_lazy _ _ _ _ _ GPo) in Hlz. destruct (kind_lazy kd); [|exact Hlz].
        rewrite page_in_ranges_cons_out in Hlz; [exact Hlz | | rewrite Un; lia].
        pose proof (page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal ltac:(rewrite Z.add_mod, Hal, HnZal by lia; reflexivity) ltac:(lia)). unfold page_size. rewrite Un. lia.
    + (* [comment removed for export] *) rewrite (GM2 x) by (rewrite Un; lia).
      rewrite (gp_noacc _ _ _ _ _ GPo) in Hna. destruct (kind_none kd); [|reflexivity].
      rewrite in_ivs_cons in Hna. cbn [fst snd] in Hna. apply orb_false_iff in Hna as [Hna _].
      apply andb_false_iff in Hna as [Hna|Hna]; [apply Z.leb_gt in Hna | apply Z.ltb_ge in Hna; rewrite Un in Hna]; lia.
    + rewrite (GM1 x) by (rewrite Un; lia). apply Xzero; [rewrite <- (HIDOUT x) by lia; exact Hh | | | | exact Hgh].
      * rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons in Hm. apply orb_prop in Hm as [Hm|Hm]; [|exact Hm].
        apply andb_prop in Hm as [_ Hm]. apply Z.ltb_lt in Hm. cbn [fst snd] in Hm. rewrite Un in Hm. lia.
      * rewrite (gp_noacc _ _ _ _ _ GPo) in Hna. destruct (kind_none kd); [rewrite in_ivs_cons in Hna; apply orb_false_iff in Hna as [_ Hna]|]; exact Hna.
      * rewrite (gp_lazy _ _ _ _ _ GPo) in Hlz. destruct (kind_lazy kd); [|exact Hlz].
        rewrite page_in_ranges_cons_out in Hlz; [exact Hlz | | rewrite Un; lia].
        pose proof (page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal ltac:(rewrite Z.add_mod, Hal, HnZal by lia; reflexivity) ltac:(lia)). unfold page_size. rewrite Un. lia.
  - (* [comment removed for export] *) eapply SINV_frame; [|exact Xsinv]. intros x Hx. apply GM1. pose proof (argH_high _ _ Hx). rewrite Un. lia.
  - (* [comment removed for export] *) rewrite (gp_noacc _ _ _ _ _ GPo), Xhna. unfold RNA. cbn [am_kind am_base am_len].
    destruct kd; cbn [kind_noneb kind_none hreplay]; rewrite ?Hbase, ?HneE; reflexivity.
  - (* [comment removed for export] *) rewrite (gp_lazy _ _ _ _ _ GPo), Xhlz. unfold RLZ. cbn [am_kind am_base am_len].
    destruct kd; cbn [kind_lazyb kind_lazy hreplay]; rewrite ?Hbase, ?HneE; reflexivity.
  - (* [comment removed for export] *) intros Ht. rewrite (gp_tid _ _ _ _ _ GPo). exact (Xtidv Ht).
  - (* [comment removed for export] *)
    rewrite (gp_res _ _ _ _ _ GPo), (gp_maps _ _ _ _ _ GPo). apply Forall_cons; [|exact Xmres].
    rewrite region_free_app in Hrf. apply andb_prop in Hrf as [Hrf1 _].
    apply Forall_forall. intros [b s] Hin. unfold iv_disjoint. cbn [fst snd]. rewrite Un.
    pose proof (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.region_free_In _ a n b s Hrf1 Hin). rewrite Un in *. lia.
  - (* [comment removed for export] *)
    rewrite (gp_res _ _ _ _ _ GPo), (gp_kernel _ _ _ _ _ GPo),
      (vdso_top_eq _ _ (gp_mbase _ _ _ _ _ GPo) (gp_isp _ _ _ _ _ GPo)).
    exact Xvdso.
  - (* [comment removed for export] *)
    rewrite (gp_rdr _ _ _ _ _ GPo). exact Xrdr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition null_base (cs : acs) : expr := escale 4096 (EVar (nxt cs)).
Definition null_vlo (cs : acs) (nlo : Z) : Z := grant_vlo A (a_maps cs) nlo.
Definition null_vhi (nlo : Z) : Z := (TOPC - nlo) / 4096.
Definition null_kv (cs : acs) (ne : expr) (nlo : Z) : list kentry :=
  KRange (EVar (nxt cs)) (null_vlo cs nlo) (null_vhi nlo) :: null_kend (null_base cs) ne nlo ++ kn cs.
Definition null_kd (cs : acs) (ne : expr) : list kentry :=
  kdisj_fixed A rz (kn cs) (null_base cs) ne ++ kdisj_new (a_maps cs) (null_base cs) ne.
Definition null_kfacts (cs : acs) (ne : expr) (nlo : Z) : list kentry :=
  KRange (EVar (nxt cs)) (null_vlo cs nlo) (null_vhi nlo) :: null_kend (null_base cs) ne nlo
  ++ null_kd cs ne ++ flat_map (kdisj_shadow_twin A (null_kv cs ne nlo)) (null_kd cs ne).
Definition null_cs1 (cs : acs) (kd : mkind) (eager : bool) (ne : expr) (nlo nhi : Z) : acs :=
  add_entry cs (sr_upd (s_regs (a_ss cs)) 10 (null_base cs))
    (null_kfacts cs ne nlo ++ kn_grant_filter A (kn cs) (a_maps cs))
    (Datatypes.S (nxt cs)) (AM (null_base cs) ne kd) nhi eager (a_ylo cs).

(* [comment removed for export] *)
Lemma mmap_null_eq : forall (split : bool) cs kd (eager visible : bool),
  mmap_null A nx0 LIMIT rz split cs kd eager visible =
  match mmap_len cs with
  | Some (ne, nlo, nhi) =>
      if (fresh_ok nx0 cs && expr_vars_lt (nxt cs) ne
          && gap_ok A cs nhi && (negb eager || budget_ok LIMIT cs nhi)
          && no_holes (a_maps cs))%bool then
        let v := nxt cs in
        let cs1 := null_cs1 cs kd eager ne nlo nhi in
        let fin (c : acs) := if visible then vis_add A LIMIT c (null_base cs) ne ([KWr (SA (null_base cs) 0) ne; KZero (SA (null_base cs) 0) ne] ++ kn c) else Some c in
        let single := match fin cs1 with Some c => Some (contra_cs c, c) | None => None end in
        if negb (split && visible) then single else
        match first_run (a_maps cs) with
        | Some (lo, hi) =>
            let vtopL := (lo - nlo) / 4096 in
            let vbotH := zcdiv' hi 4096 in
            if (Z.leb vbotH (null_vlo cs nlo) || Z.ltb vtopL (null_vlo cs nlo))%bool then single
            else if Z.ltb (null_vhi nlo) vbotH then
              match fin (set_kn cs1 (KRange (EVar v) (null_vlo cs nlo) vtopL :: kn cs1)) with
              | Some c => Some (contra_cs c, c) | None => None end
            else
              match fin (set_kn cs1 (KRange (EVar v) (null_vlo cs nlo) vtopL :: kn cs1)),
                    fin (set_kn cs1 (KRange (EVar v) vbotH (null_vhi nlo) :: kn cs1)) with
              | Some cL, Some cH => Some (cL, cH)
              | _, _ => None
              end
        | None => single
        end
      else None
  | None => None
  end.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "p'0h01ci001ch12csh23cs1h35eagerh43finh52kdh66singleh75splith81vh95vbotHh:7visiblei017visibleh;5vtopLi022cHi032cLi042hii052loi062nei073nhii083nloi091pi0:2p0i0;1xp;2p;1p;3p;6p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;g009NR;p4p710R<p8p1009kp605611111000p100;1p4p741110R=p8p100;np605611111000R>P=p8p100=:p4p7210R?P7p8P?P8p8P?P9p8P?P6p8P?p100=fp4p710p8p100>mp605611111000R?P>p8P?P=p8p100@:p605611111000R>P?p8P>P=p8p100ADp6054111000R?p100BIp4p710R@p8P?P=p8P?p100CDp4p7511110RAp8p100DAp4p711RBP@p8PBp100E?p4p771111110p8PBPAp8p100FKp4p711RBP=p8PBp100G<p4p741110p8p100HBp4p70RBP7p8PBP8p8PBP9p8PBP6p8p100I8p6051000RBP8p8PBP9p8p100J<p4p70RBP>p8PBP?p8PBP@p8PBP=p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710RBp8P7P<p8P7P5p8P7P0p8p103WUR7p6051001R?P1p8P?P:p8P?P<p8P?P5p8P?P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7PBp8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P@p8P6P=p8P6PAp8p108BCp6051000RAP8p8PAP9p8g00N6R9j23Tg02NORAj1@Tg07eSj1MTg0;Y:j2DTg08Pdj1YTg02iUj2TTg00QTj21Tg0;Z=j3LTg01B8j18Tg0;[>j3ETg00VCj2>Tg08X8j19Tg0;\Bj1ATg0;]Ej6XTg0;^Jj1VTg08dTj2UTg08eYj2STg08f_j2RTg00^>j1QTg015aj32Tg07hQj15TP;j3PTg08JKj6KTg02O1j24Tg0;_Pj1ITg016Aj47Tg00bOj1FTg0;`Tj1GTg01iSj2HTg01g6j1JTg02E?j2CTg0;aXj2NTg0;bYj2OTg00O`j2BTg00Q7j2<Tg0;c^j16Tg0348j1=Tg0:CDj3:Tg0;dcj2?Tg00R2j2WTg00LPj1;Tf0R;#;#;p=0g00UcR8g02XCR6g03IB1366R=#@R@PAg02keR0g00T`R4'3R2/34P@f3R7#MP9P2P4P@P;P9P0P4P@f1R0P8P@p,3nx0f8R2'D%Y2RB/T0'1p,1AR3f2R17L2'1f6R?#8p,5LIMITR5?E21'>'1%92#A'1PBg02`ef9RBP2f7R<P1P0P7EXP6P8%@6R7P2P3P5P;f;#VR5f4R3g08jhR1g00n4,U5R5/S31R53%Q1521521%5;3PEK146;n0110100020000X06P7^06PAP6P@P;P0O1P6P6%I;P;C7,4=R7%F=R5n10110;00021010000P@P8P@f=/1B#8P;PA1344P@f<#9#GP9P4P4P@P;1H0<g00U>#0#0#0#0#0#0#JR9'CP41N09P4P8P@fA/OBR4,B;1<04'>f5P8P@%6B/<;PAP6P@P?%=2?:40%5<521,?<O1R4P7P5n10110;00021010000PAP6P@P4PAP6P@P<%=Bf:#67:0%52521,?2O1P6P6P0P;C7,4=P5n10110;00021010200P5n10110;00021010300n0100000020000n0100000020000b9b;n2001109000120105104P;n10110;00021010900n0100000020000b6b4b2b8P5n0100000020100n200110:000121106108n200110900012110:107P5n10110;00021110900'WX:8X38W5W1W7o"). Qed.

(* [comment removed for export] *)
Hypothesis HULL_lt : hull_lt A.

(* [comment removed for export] *)
Lemma null_kend_ok : forall E M base ne nlo (a n : word),
  edenot E base = a -> edenot E ne = n ->
  4096 <= bv_unsigned a -> nlo <= bv_unsigned n -> bv_unsigned a + bv_unsigned n <= TOPC ->
  know_ok SEGS E M (null_kend base ne nlo).
Proof.
  intros E M base ne nlo a n Hb Hn Hlo Hnlo HaC. unfold null_kend.
  pose proof (u64_range a) as Ra. pose proof (u64_range n) as Rn. unfold two64 in *.
  destruct ne; try (apply Forall_nil); apply Forall_cons; try apply Forall_nil;
    cbn [kentry_ok]; unfold eadd; rewrite AX2SK.mkAlu_denot; cbn [alu64 alu]; rewrite bv_add_unsigned, Hb, Hn;
    unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64)%Z;
    unfold TOPC in *; rewrite Z.mod_small by lia; lia.
Qed.
Lemma null_kend_pure : forall base ne nlo,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (null_kend base ne nlo).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "p'0h03ne1h13ne2h22opi002oph31ni011nh42nei022neh52sxi032sxh61Ki041Kh74baseh81ii051ih91ki061kh:2loi072loh;3nloh<1zi081zi091ai0:2a1i0;2a2i0<1bi0=1ci0>1ei0?2hii0@1mi0A2n1i0B2n2i0C1vi0D1wp;1p;2p;3p;4p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0g003HR4p4p710p8P0p1003iR5p4p710p8P0P5p4p7210p8P0p1004FR5p4p710R6p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R7p1006Np4p710R8p8P7p1006jp4p710R9p8P7p1007Hp4p7210R:p8P7p1007ep4p710R7p8p1008Cp4p710R;P8p8P;P7p8p1008`p4p70R<P2p8P<P8p8P<P9p8P<P:p8P<P7p8P<p1009Np4p710R<p8p1009kp605611111000p100;1p4p741110R=p8p100;np605611111000R>P=p8p100=:p4p7210R?P8p8P?P9p8P?P:p8P?P7p8P?p100=fp4p710p8p100>mp605611111000R?P>p8P?P=p8p100@:p605611111000R>P?p8P>P=p8p100ADp6054111000R?p100BIp4p710R@p8P?P=p8P?p100CDp4p7511110RAp8p100DAp4p711RBP@p8PBp100E?p4p771111110p8PBPAp8p100FKp4p711RBP=p8PBp100G<p4p741110p8p100HBp4p70RBP8p8PBP9p8PBP:p8PBP7p8p100I8p6051000RBP9p8PBP:p8p100J<p4p70RBP>p8PBP?p8PBP@p8PBP=p8P5p4p7210R5P8p8P5P7p8p100K7p4p7210P7p8p100KVp4p73110P7p8p103T5p6051000R8p1016ap4p710RBp8P8P<p8P8P6p8P8P0p8p103WUR8p6051001R?P1p8P?P;p8P?P<p8P?P6p8P?P0p8P8p60521000R8P1p8P8P5p8p103c\R5p6051001R8P1p8P8P3p8P8PBp8P8P0p8P5p60521000R5P2p8P5P7p8P5P0p8p100L2p4p710P7p8P0P7p8p105Eip6054111000R7P@p8P7P=p8P7PAp8p108BCp6051000RAP9p8PAP:p8g00NVj1ETg00^>j1DTg01g6j17Tg00PZj23Tg015aj34TP4j35Tg07P8j2;Tg0348j1:Tg037Mj38Tg038Qj39Tg03:`j3CTg03;dj3BTg03=\j4?Tg03>`j4=Tg0;h6j3>Tg00LPj16Tg0;edj2<Tg0:CDj3@Tg07PYj6ATf0R4#6#6p=2f2R:f1RA'<g0;i:7@4p=0g08jhR9f3R7P:PAg013JP4EAp=1g02keR=g00T`R@P=P9p-0P4g012QR0P0P0g012mP0P0P0P0P0P0n01104000:3010910D10C20109101301091011062010710?2010>10@3010>10710?201091014010:10A10;10B3010910110=20109101X69R0P=%E9P4%D9R5f4R2g00U>#2#2#2#2#2#2#7R8/3:RB70A=495f6R31382707=495R1P1P1P1f7f5,38702=495R1P1n01102000810108101013010010910<3010010910<3010010910<3010010910<4010310710110>40103106105101559PA1;90R1X<@P4O1g02`eR?P0%:4=02BP5P1C1W3P4O1g0305RBP0f8R2A8:A41383R330P5P1C1X1=X0=W2P:PAP4O3P0A9:A4=023P5P1C1X1=X0=X2BP:PAP4O3g031hRBP0AC:A4=023P5P1C1X1=X0=W2P:PAP4O3P0AB:A4=023P5P1C1X1=X0=X2BP:PAP4O3g00UcRBP0f:R3P7P:PAP4C?1382R230P5P1C1X4=X3?X:?W5P7P:PAP4O4P0P7P:PAP4C==032P5P1C1X3?X8@X9?X5BP7P:PAP4O4n0110>010810108101013010010910<3010010910<3010010910<3010010910<4010310710110>40103106105101A>:A49590eW;X4=W7o"). Qed.

Lemma escale_4096_denot : forall E v (a : word),
  ev E v = Z_to_bv 64 (bv_unsigned a / 4096) -> bv_unsigned a mod 4096 = 0 ->
  edenot E (escale 4096 (EVar v)) = a.
Proof.
  intros E v a Hv Hal. unfold escale. rewrite mkMd_denot. cbn [edenot]. rewrite Hv.
  pose proof (u64_range a) as Ra. apply bv_eq. rewrite u_mul64.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  rewrite !u64_lit by lia. rewrite Z.mod_small by lia. lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grant_hull_apart : forall model (a n : word) nZ,
  (exists rx : list (word * word),
     vm_reserved (m_vmmaps model) = segments_reserved SEGS ++ rx
     /\ Forall (resx_entry_ok A) rx
     /\ (length rx <= n_resx A)%nat
     /\ sum_sizes rx <= resx_bytes A) ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a n = true ->
  bv_unsigned n = nZ -> 0 < nZ ->
  bv_unsigned a + nZ <= img_lo A \/ img_hi A <= bv_unsigned a.
Proof.
  intros model a n nZ (rx & Hres & _ & _ & _) Hrf Un HnZ. pose proof HULL_lt as HL. unfold hull_lt in HL.
  rewrite region_free_app in Hrf. apply andb_prop in Hrf as [Hrf1 _].
  rewrite Hres, region_free_app in Hrf1. apply andb_prop in Hrf1 as [Hrf1 _].
  destruct (Z_lt_le_dec (bv_unsigned a) (img_hi A)) as [H1|H1]; [|right; lia].
  destruct (Z_lt_le_dec (img_lo A) (bv_unsigned a + nZ)) as [H2|H2]; [|left; lia].
  exfalso. set (z := Z.max (bv_unsigned a) (img_lo A)).
  pose proof (HULL_tiled z ltac:(unfold z; lia)) as T.
  rewrite (region_free_sem _ a n z Hrf1 ltac:(lia) ltac:(unfold z; lia)) in T. discriminate T.
Qed.

(* [comment removed for export] *)
Lemma alloc_top_eq : forall E cs R FULL model,
  CSOK E cs R FULL model -> alloc_top (m_vmmaps model) = uE E e_sp0 - 8388608.
Proof.
  intros E cs R FULL model HC. pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as [ISP _].
  unfold alloc_top, stack_max_size. rewrite ISP. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma alloc_top_utop : forall E cs R FULL model,
  CSOK E cs R FULL model -> utop E <= alloc_top (m_vmmaps model) < utop E + 4096.
Proof.
  intros E cs R FULL model HC. rewrite (alloc_top_eq E cs R FULL model HC). apply utop_bounds.
Qed.

Lemma le_utop : forall E cs R FULL model z,
  CSOK E cs R FULL model -> z mod 4096 = 0 -> z <= alloc_top (m_vmmaps model) -> z <= utop E.
Proof.
  intros E cs R FULL model z HC Hz Hle. rewrite (alloc_top_eq E cs R FULL model HC) in Hle.
  exact (le_utop_of_aligned E z Hz Hle).
Qed.

Lemma utop_le_TOPC : forall E cs R FULL model, CSOK E cs R FULL model -> utop E <= TOPC.
Proof.
  intros E cs R FULL model HC. pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as [_ [ISP _]]. pose proof (utop_bounds E).
  unfold TOPC, sp_window_hi in *. lia.
Qed.

Lemma isp_facts_of : forall E cs R FULL model, CSOK E cs R FULL model -> isp_facts E.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h01Eh14FULLh22HCh31Rh42csh55modelp;1p;2p;;p;3p;<p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8g00=:R>p4p7210R?P7p8P?P8p8P?P9p8P?P6p8P?p100=fp4p710p8p100>mp605611111000R?P=p8P?P<p8p100@:p605611111000R=P?p8P=P<p8p100ADp6054111000R?p100BIp4p710R@p8P?P<p8P?p100CDp4p7511110RAp8p100DAp4p711RBP@p8PBp100E?p4p771111110p8PBPAp8p100FKp4p711RBP<p8PBp100G<p4p741110p8p100HBp4p70RBP7p8PBP8p8PBP9p8PBP6p8p100I8p6051000RBP8p8PBP9p8p100J<p4p70RBP=p8PBP?p8PBP@p8PBP<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710RBp8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R?P1p8P?P:p8P?P;p8P?P5p8P?P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7PBp8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P@p8P6P<p8P6PAp8p108BCp6051000RAP8p8PAP9p8g00LPj10Tg00ePj1@Tg00M5j11Tg00MSj12TP>j2?Tg02NOj1;Tg07dSl;:Tg01IPj19Tg05bij18Tg00O6j27Tg07\Oj23Tg00TFj35Tg00[Qj24Tg00Z0j26Tg09UUj1>Tg0:\Ol<=Tg010[j3<Tg02bHg02XCg00U>#0R>#@#1%0>#0R>#0#0#0#1R9#2RA'?%1>#2#;\Ag01UDp,4SEGSRAp,1AR>p,5LIMITR8p,4SINVR6p,4argHR<p,3FS0R@f4R0f3R4f2R2f1R7f0RBM;:g00T`R3%97#8,79f5R9g09^\'3R135g09Ag/41g09_\,41'6g09`W,39%>1553'6PAP>P8P6P<P@P9P0P4P2P7PBM<=3<W2W5W1W3W4W0o"). Qed.

(* [comment removed for export] *)
Lemma grant_ok_na_pin_parts : forall model (a : word) nZ,
  grant_ok_na_pin model a nZ = true ->
  bv_unsigned a mod 4096 = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top (m_vmmaps model)
  /\ region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a (Z_to_bv 64 nZ) = true.
Proof.
  intros model a nZ Hg. unfold grant_ok_na_pin in Hg.
  apply andb_prop in Hg as [Hg Hrf]. apply andb_prop in Hg as [Hg Htop]. apply andb_prop in Hg as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop. unfold page_size in Hal.
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma null_grant_facts : forall E cs R FULL model (a : word) nZ,
  CSOK E cs R FULL model -> grant_ok_na_pin model a nZ = true -> 0 < nZ -> nZ mod 4096 = 0 ->   (* [comment removed for export] *)
  bv_unsigned a mod 4096 = 0 /\ 4096 <= bv_unsigned a
  /\ bv_unsigned a + nZ <= utop E /\ utop E <= TOPC /\ bv_unsigned (Z_to_bv 64 nZ) = nZ
  /\ region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a (Z_to_bv 64 nZ) = true
  /\ (bv_unsigned a + nZ <= img_lo A \/ img_hi A <= bv_unsigned a)
  /\ maps_apart E (a_maps cs) (bv_unsigned a) nZ.
Proof.
  intros E cs R FULL model a nZ HC Hg HnZ HnZal.
  destruct (grant_ok_na_pin_parts model a nZ Hg) as (Hal & Hpos & Htop0 & Hrf).
  assert (Htop : bv_unsigned a + nZ <= utop E).
  { eapply le_utop; [exact HC | rewrite Z.add_mod, Hal, HnZal by lia; reflexivity | exact Htop0]. }
  pose proof (utop_le_TOPC E cs R FULL model HC) as HT.
  pose proof (u64_range a) as Ra.
  assert (Un : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u64_lit; unfold TOPC in *; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H4096 : 4096 <= bv_unsigned a) by lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (grant_hull_apart model a (Z_to_bv 64 nZ) nZ (co_res _ _ _ _ _ _ _ _ _ _ _ HC) Hrf Un HnZ) as Hhull.
  pose proof (maps_apart_of_region_free E (a_maps cs) model a (Z_to_bv 64 nZ) (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hrf) as Hap.
  rewrite Un in Hap.
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma u_e_stk_len : forall E, isp_facts E -> uE E e_stk_len = 2 ^ 47 - utop E.
Proof.
  intros E [Hsp Hpg]. pose proof (utop_bounds E) as UB. unfold utop in UB |- *.
  unfold e_stk_len, esub, uE in *. rewrite mkAlu_denot, edenot_lit.
  rewrite u_sub64, u_lit64, Hpg. unfold two64, sp_window_lo, sp_window_hi in *.
  rewrite (Z.mod_small (2 ^ 47 + 8388608)) by lia. rewrite Z.mod_small; lia.
Qed.

(* [comment removed for export] *)
Lemma kdisj_new_ok : forall E M ms nb ne (lo n : Z),
  bv_unsigned (edenot E nb) = lo -> bv_unsigned (edenot E ne) = n -> maps_apart E ms lo n -> 0 < n ->
  Forall (kentry_ok SEGS E M) (kdisj_new ms nb ne).
Proof.
  intros E M ms nb ne lo n Hb Hn Hap HnZ. pose proof (u64_range (edenot E nb)) as Rb. rewrite Hb in Rb.
  unfold kdisj_new. apply Forall_app. split.
  - unfold kdisj_merged. apply Forall_flat_map. apply Forall_forall. intros [[rlo rn] k] Hin.
    destruct (Nat.leb 2 k); [|constructor]. constructor; [|constructor].
    pose proof (runs_apart_grant E ms lo n rlo rn k Hap HnZ Hin) as D.
    pose proof (PlaceLemmasK.runs_bounds ms rlo rn k Hin) as (B0 & B1 & B2). unfold two64 in B2.
    cbn [kentry_ok]. unfold estart, elenZ; cbn [a_base a_off]. rewrite !edenot_lit, Hb, Hn.
    rewrite !u64_lit by lia. lia.
  - unfold kdisj_new1. apply Forall_flat_map. apply Forall_forall. intros m Hm.
    destruct (is_fog m) eqn:Hfm; [constructor|]. constructor; [|constructor].
    pose proof (Hap m Hm Hfm) as D.
    cbn [kentry_ok]. unfold estart, elenZ; cbn [a_base a_off]. rewrite Hb, Hn. lia.
Qed.

Lemma kdisj_new_pure : forall ms nb ne,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (kdisj_new ms nb ne).
Proof.
  intros ms nb ne. unfold kdisj_new, kdisj_merged, kdisj_new1. apply Forall_app. split.
  - apply Forall_flat_map. apply Forall_forall. intros [[lo n] k] _. destruct (Nat.leb 2 k); repeat constructor.
  - apply Forall_flat_map. apply Forall_forall. intros m _. destruct (is_fog m); repeat constructor.
Qed.

(* [comment removed for export] *)
Lemma null_kfacts_ok : forall E cs R FULL model ne nlo nhi (a n : word) nZ M',
  CSOK E cs R FULL model ->
  mmap_len cs = Some (ne, nlo, nhi) ->
  ev E (nxt cs) = Z_to_bv 64 (bv_unsigned a / 4096) ->
  edenot E ne = n -> bv_unsigned n = nZ -> nlo <= nZ -> 0 < nZ -> nZ mod 4096 = 0 ->
  grant_ok_na_pin model a nZ = true ->
  know_ok SEGS E M' (null_kfacts cs ne nlo) /\ edenot E (null_base cs) = a
  /\ null_vlo cs nlo <= bv_unsigned a / 4096 <= null_vhi nlo.
Proof.
  intros E cs R FULL model ne nlo nhi a n nZ M' HC HML Hv Hne Un Hnlo HnZ HnZal Hg. pose proof HULL_lt as HL. unfold hull_lt in HL.
  destruct (null_grant_facts E cs R FULL model a nZ HC Hg HnZ HnZal) as (Hal & H4096 & Htop & HT & Un' & Hrf & Hhull & Hap).
  pose proof (u64_range a) as Ra. pose proof (u64_range n) as Rn.
  pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as [_ ISP]. pose proof (utop_bounds E) as UB.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK0.
  pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3).
  assert (Hbase : edenot E (null_base cs) = a) by (unfold null_base; apply escale_4096_denot; assumption).
  assert (VLH : null_vlo cs nlo <= bv_unsigned a / 4096 <= null_vhi nlo).
  { unfold null_vlo, null_vhi. split.
    - eapply (PlaceLemmasK.grant_vlo_sound A (a_maps cs) (bv_unsigned a) nZ nlo HnZ Hnlo H4096 Hal Hhull HU2).
      intros lo n0 k Hin. eapply runs_apart_grant; [exact Hap | exact HnZ | exact Hin].
    - apply Z.div_le_mono; lia. }
  split; [|exact (conj Hbase VLH)].
  assert (KR : forall M, kentry_ok SEGS E M (KRange (EVar (nxt cs)) (null_vlo cs nlo) (null_vhi nlo))).
  { intros M. cbn [kentry_ok edenot]. rewrite Hv.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite u64_lit by lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    exact VLH. }
  assert (KE : forall M, know_ok SEGS E M (null_kend (null_base cs) ne nlo)).
  { intros M. eapply null_kend_ok; [exact Hbase | exact Hne | exact H4096 | lia | lia]. }
  assert (KD : forall M, Forall (kentry_ok SEGS E M) (null_kd cs ne)).
  { intros M. unfold null_kd. apply Forall_app. split.
    - (* [comment removed for export] *)
      pose proof (u_e_top E ISP) as T. pose proof (u_e_stk_len E ISP) as L. unfold uE in T, L.
      unfold kdisj_fixed. apply Forall_app. split; [|apply Forall_app; split].
      + constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off].
        * rewrite !edenot_lit, !u64_lit by (unfold KHI in *; lia). rewrite Hbase, Hne, Un. lia.
        * rewrite Hbase, Hne, Un. right. unfold uE in UB. lia.
      + apply Forall_flat_map. apply Forall_forall. intros [[b off] len] _.
        destruct (lin_ge0 (kn cs) [(b, off)] [(e_top, 0%Z)]) eqn:G; [|constructor]. constructor; [|constructor].
        pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK0 G) as G'. cbn [xt_den] in G'. rewrite T in G'.
        cbn [kentry_ok]. unfold estart, elenZ; cbn [a_base a_off]. rewrite Hbase, Hne, Un. right. lia.
      + constructor; [|constructor]. cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off]. rewrite T, L, Hbase, Hne, Un.
        right. lia.
    - (* [comment removed for export] *)
      unfold kdisj_new. apply Forall_app. split.
      + unfold kdisj_merged. apply Forall_flat_map. apply Forall_forall. intros [[rlo rn] k] Hin.
        destruct (Nat.leb 2 k); [|constructor]. constructor; [|constructor].
        pose proof (runs_apart_grant E (a_maps cs) (bv_unsigned a) nZ rlo rn k Hap HnZ Hin) as D.
        pose proof (PlaceLemmasK.runs_bounds (a_maps cs) rlo rn k Hin) as (B0 & B1 & B2). unfold two64 in B2.
        cbn [kentry_ok]. unfold estart, elenZ; cbn [a_base a_off]. rewrite !edenot_lit, Hbase, Hne, Un.
        rewrite !u64_lit by lia. lia.
      + unfold kdisj_new1. apply Forall_flat_map. apply Forall_forall. intros m Hm.
        destruct (is_fog m) eqn:Hfm; [constructor|]. constructor; [|constructor].
        pose proof (Hap m Hm Hfm) as D.
        cbn [kentry_ok]. unfold estart, elenZ; cbn [a_base a_off]. rewrite Hbase, Hne, Un. lia. }
  unfold null_kfacts. apply Forall_cons; [exact (KR M')|]. apply Forall_app. split; [exact (KE M')|].
  apply Forall_app. split; [exact (KD M')|].
  apply (kdisj_shadow_twins_ok SEGS A SHADOW_ok' E (MR E cs model FULL)); [|exact (KD _)].
  (* [comment removed for export] *)
  unfold null_kv. apply Forall_cons; [exact (KR _)|]. apply Forall_app. split; [exact (KE _)|].
  exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.

Lemma kdisj_shadow_twin_pure : forall k K,
  Forall (fun K' => match K' with KImg _ _ => False | _ => True end) (kdisj_shadow_twin A k K).
Proof.
  intros k K. unfold kdisj_shadow_twin.
  destruct K as [| | | | | | |[b1 o1z] n1 [b2 o2z] n2| |]; try constructor.
  destruct o1z; try constructor. destruct o2z; try constructor.
  destruct (split_lit b1) as [c1 o1]. destruct (split_lit b2) as [c2 o2].
  destruct (shadow_of A k b1 n1) as [[sb1 sk1] sn1]. destruct (shadow_of A k b2 n2) as [[sb2 sk2] sn2].
  match goal with |- Forall _ (if ?c then _ else _) => destruct c; [|constructor] end.
  constructor; [exact I | constructor].
Qed.

Lemma null_kd_pure : forall cs ne,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (null_kd cs ne).
Proof.
  intros cs ne. unfold null_kd, kdisj_fixed, kdisj_new, kdisj_merged, kdisj_new1.
  apply Forall_app. split; [|apply Forall_app; split].
  - apply Forall_app. split; [repeat constructor|]. apply Forall_app. split; [|repeat constructor].
    apply Forall_flat_map. apply Forall_forall. intros [[b off] len] _. destruct (lin_ge0 _ _ _); repeat constructor.
  - apply Forall_flat_map. apply Forall_forall. intros [[lo n] k] _. destruct (Nat.leb 2 k); repeat constructor.
  - apply Forall_flat_map. apply Forall_forall. intros m _. destruct (is_fog m); repeat constructor.
Qed.

Lemma null_kfacts_pure : forall cs ne nlo,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (null_kfacts cs ne nlo).
Proof.
  intros cs ne nlo. unfold null_kfacts. apply Forall_cons; [exact I|]. apply Forall_app. split; [apply null_kend_pure|].
  apply Forall_app. split; [apply null_kd_pure|].
  apply Forall_flat_map. apply Forall_forall. intros K _. apply kdisj_shadow_twin_pure.
Qed.

Lemma mmap_null_cs1 : forall cs kd (eager : bool) ne nlo nhi E R FULL model (a : word) model' FULL',
  CSOK E cs R FULL model ->
  mmap_len cs = Some (ne, nlo, nhi) ->
  fresh_ok nx0 cs = true -> expr_vars_lt (nxt cs) ne = true ->
  (eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  no_holes (a_maps cs) = true ->
  let len := bv_unsigned (edenot E (reg cs 11)) in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  grant_ok_na_pin model a nZ = true ->
  grant_post kd a n model model' -> grant_mem kd a n FULL FULL' ->
  let v := nxt cs in
  let E' := ext1 E v (Z_to_bv 64 (bv_unsigned a / 4096)) in
  let cs1 := null_cs1 cs kd eager ne nlo nhi in
  CSOK E' cs1 (regupd R (Z_to_bv 5 (Z.of_nat 10)) a) FULL' model'
  /\ edenot E' (null_base cs) = a /\ edenot E' ne = n /\ bv_unsigned n = nZ
  /\ env_agree nx0 E E' /\ env_agree (nxt cs) E E'
  /\ ev E' v = Z_to_bv 64 (bv_unsigned a / 4096)
  /\ (bv_unsigned a mod 4096 = 0 /\ 4096 <= bv_unsigned a /\ bv_unsigned a + nZ <= utop E' /\ utop E' <= TOPC
      /\ nlo <= nZ <= nhi /\ 0 < nZ /\ nZ mod 4096 = 0 /\ null_vlo cs nlo <= bv_unsigned a / 4096 <= null_vhi nlo)
  /\ maps_apart E' (a_maps cs) (bv_unsigned a) nZ
  /\ (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
        in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model')) = true
        /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false
        /\ argH E' x = false /\ in_hull A (bv_unsigned x) = false /\ (utop E' <=? bv_unsigned x) = false).
Proof.
  intros cs kd eager ne nlo nhi E R FULL model a model' FULL' HC HML Hfresh Hnev Hbudget Hkind Hkfog Hnoh len nZ n Hg GPo GM v E' cs1.
  assert (Hnoholes : Forall (fun m => is_hole m = false) (a_maps cs)).
  { unfold no_holes in Hnoh. apply Forall_forall. intros m Hm. pose proof (proj1 (forallb_forall _ _) Hnoh m Hm) as X. apply negb_true_iff in X. exact X. }
  (* [comment removed for export] *)
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE).
  fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
  assert (HnZpos : 0 < nZ) by lia.
  pose proof (u64_range a) as Ra.
  pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3).
  (* [comment removed for export] *)
  pose proof (ext1_agree'' E v (Z_to_bv 64 (bv_unsigned a / 4096))) as Hag. fold E' in Hag.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fvis & Fbrk & Ffd & Fle). fold v in Fsr, Fkn, Fmaps, Fvis, Fbrk, Ffd, Fle.
  assert (HC' : CSOK E' cs R FULL model) by (eapply cs_ok_agree'; [exact Hag | exact Hfresh | exact HC]).
  assert (Hag0 : env_agree nx0 E E') by (eapply env_agree_le'; [exact Hag | exact Fle]).
  assert (Hv : ev E' v = Z_to_bv 64 (bv_unsigned a / 4096)) by apply ext1_at.
  assert (HneE' : edenot E' ne = n).
  { rewrite (HneE E'); [exact Hne|]. symmetry. eapply edenot_agree'; [exact Hag|]. unfold reg. apply nth_sr_vars_lt'; [exact Fsr | lia]. }
  (* [comment removed for export] *)
  destruct (null_grant_facts E' cs R FULL model a nZ HC' Hg HnZpos HnZal) as (Hal & H4096 & HaT & HT & Un & Hrf & Himg_a & Hapart).
  fold n in Un, Hrf.
  destruct (null_kfacts_ok E' cs R FULL model ne nlo nhi a n nZ (MR E' cs model' FULL') HC' HML Hv HneE' Un ltac:(lia) HnZpos HnZal Hg) as (KNEW & Hbase & VLH).
  pose proof (grant_new_facts E' cs R FULL model a n nZ HC' Hrf Un HnZpos Himg_a HaT) as NEW.
  (* [comment removed for export] *)
  destruct (grant_cs1_ok E' cs R FULL model kd a n nZ model' FULL'
              (sr_upd (s_regs (a_ss cs)) 10 (null_base cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) a)
              (null_kfacts cs ne nlo) (null_base cs) ne nhi eager (a_ylo cs) (Datatypes.S v)
              HC' Un HnZpos HnZal Hal Himg_a HaT Hrf GPo GM) as (HC1 & MROUT & MRSAME).
  - apply regs_ok_set_n'; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC') | lia | exact Hbase].
  - exact Hbase.
  - exact HneE'.
  - exact KNEW.
  - exact Hkind.
  - exact Hkfog.
  - lia.
  - exact Hbudget.
  - lia.
  - intros m Hm Hk. exfalso. pose proof (proj1 (Forall_forall _ _) Hnoholes m Hm) as X. congruence.
  - split; [exact HC1|]. split; [exact Hbase|]. split; [exact HneE'|]. split; [exact Un|]. split; [exact Hag0|]. split; [exact Hag|].
    split; [exact Hv|]. split; [destruct VLH; repeat split; lia|]. split; [exact Hapart|].
    intros x Hx. destruct (NEW x Hx) as (N0 & N1 & N2 & N3 & N4 & _).
    split; [|auto]. rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons. cbn [fst snd]. rewrite Un.
    apply orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
Lemma null_first_run : forall E ms lo n flo fhi,
  maps_apart E ms lo n -> 0 < n -> first_run ms = Some (flo, fhi) -> lo + n <= flo \/ fhi <= lo.
Proof.
  intros E ms lo n flo fhi Hap Hn Hfr.
  destruct (PlaceLemmasK.first_run_In ms flo fhi Hfr) as (rn & k & -> & Hin).
  eapply runs_apart_grant; eassumption.
Qed.

(* [comment removed for export] *)
Lemma null_low_fact : forall E v (a : word) nZ nlo lo vlo M,
  ev E v = Z_to_bv 64 (bv_unsigned a / 4096) -> vlo <= bv_unsigned a / 4096 ->
  bv_unsigned a + nZ <= lo -> nlo <= nZ ->
  kentry_ok SEGS E M (KRange (EVar v) vlo ((lo - nlo) / 4096)).
Proof.
  intros E v a nZ nlo lo vlo M Hv Hvlo Hlo Hnlo. pose proof (u64_range a) as Ra.
  cbn [kentry_ok edenot]. rewrite Hv.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  rewrite u64_lit by lia. split; [exact Hvlo|]. apply Z.div_le_mono; lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma null_high_fact : forall E v (a : word) hi vhi M,
  ev E v = Z_to_bv 64 (bv_unsigned a / 4096) -> bv_unsigned a / 4096 <= vhi ->
  hi <= bv_unsigned a -> bv_unsigned a mod 4096 = 0 ->
  kentry_ok SEGS E M (KRange (EVar v) (zcdiv' hi 4096) vhi).
Proof.
  intros E v a hi vhi M Hv Hvhi Hhi Hal. pose proof (u64_range a) as Ra.
  cbn [kentry_ok edenot]. rewrite Hv. unfold zcdiv'.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  rewrite u64_lit by lia. split; [|exact Hvhi]. lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
Lemma null_child_ok : forall E cs1 R FULL model K,
  CSOK E cs1 R FULL model -> (forall M, kentry_ok SEGS E M K) ->
  CSOK E (set_kn cs1 (K :: kn cs1)) R FULL model.
Proof.
  intros E cs1 R FULL model K HC HK. apply cs_ok_set_kn; [exact HC|].
  constructor; [apply HK | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC)].
Qed.

Lemma null_high_vbot : forall (a hi : Z), hi <= a -> a mod 4096 = 0 -> zcdiv' hi 4096 <= a / 4096.
Proof.
  intros a hi Hhi Hal. unfold zcdiv'.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma null_low_vtop : forall (a nZ nlo lo : Z), a + nZ <= lo -> nlo <= nZ -> 0 <= a -> a / 4096 <= (lo - nlo) / 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h02Hah19RES_len'0h27__arithh34__ffh44__p1h56__sat4h66__sat5h76__sat6h86__sat7h98__varmaph:5__with;4__x1h<4__x2h=4__x3h>4__x4h?4__x5h@4cstrhA5cstr0hB2H1hC2H2hD2H3hE1ahF2lohG2nZhH3nlohI1xhJ1yp;2p;1p;3p;<p;4p;6p;7p;5p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70RAP=p8PAP>p8PAP?p8PAP<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710RAp8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7PAp8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8p108BCp6051000R@P8p8P@P9p8g00PZj2KTg00[Qj21Tg01iSj2DTg00LPj15Tg01g6j1;Tg00M5j1\Tg00MSj1ZTg00N6j2XTg07jQj1STg01Nlj2MTg07kOj1LTg00TFj32j1ITg01OLR9j18Tg02f0j2fTg02fSj3eTg00R2j2>Tg02`@l<_Tg02^nj4]Tg01RTj1HTg07lOj1[Tg02M^j2GTg01Zhj2FTg00ePj17Tg01joj2YTg00\Mj2ATg01gTj2WTg01kWj3VTg07mPj1UTg00^>j1RTg00NVj1QTg00_<j1PTg00`8j1NTg00`Vj1OTg01l^j2CTg00adj4ETg00c1j2TTg00cSj2mTg00d?j3lTg00d^j4kTg01=3j1@Tg01=Rj2<Tg01>;j3JTg01>dj2jTg015aj3iTg00^^j2=Tg00_Zj4?Tg00aAj24Tg00bOj1dTg00f5j3bTg00gej6aTg00hIj7`Tg01l;j3cTg00Z0j2:Tg0<E2j5^Tg00gAj7gTg00hmj8hTg00n4R@f0R8'1p=0%58#5p=6f1R6g00j1R<g00jPR?P?g00k0R0P8g00kPFgp=3g00T`R4P6g00mMP8CEp=9f3R2P<P?P?P0f2R7P6P8Ghp=B1K27/181172f5RA#0R3f6f4R1,D2g00U>R>#5R5#5R;#6#6R:#6#6#6#;R=g02`eRB%\:#ZR:/X:p,4SEGS#S'MR:p,1ARC#LRD32%8:RE%8DRF524RGPBP4%IBP9%I4%86%88524A2B681f683eXJBXIBP:PE1>4EPDPF1>4FM<_p,8RES_len'C]RBPG%HDRD%0FRF%H:R:%0ERE%[CR9/G=RH%09%0=RI1F9=RJ#0[[RK%;5RL%75RM#7#7#7#;RN'YRO1A@L%0N1WLNRP,A@[[RQ%0LRRg012QRSAVLN6UW0RN%0P\S^0RRR%UCRC/G=RS%0C1FC=RP#0\I[RIg00laRL#RRT%QLRU%P4RV%N4RW%O4RXP41C4@RYg00nR1C4=CE'31TX0RZP8P7g00UcR[g00iQR\'>1m87=2[\dAl4@6CkR\b3b9b:1A@=P8b2b5b6b7b8bAb@b1PBPGPDPFP:PEPHPKPOPQPNPRPSPIp-0RIg01@4RS#@#@RR#@,<41<4R1<4S5J45J4g01@S'j=iLTPUP4P41=41P7P41=4APAPVC?C?P61=42C?PWPX%7>,44RW%5M,44RM'9,3X%d?RVPX144>R>=b4M1445R5'9,3XPVPXPXP<P?P?P0144;,9Y,3XPXP<P?P?P0f7R0EaF`PVAc45W,9>,3XCBCBCBPZP\b3b9b:X;4X<4X=4X>4X?4W411711K6A/171:301D1A,12[[[^;4^<4^=4^>4^?4^4IP8A24P@A24J@g08@<,19':':f=PCf<f;f>f9f:p,8HULL_ok'O9b2b5b6b7b8bAb@b1D^WDWCWBXF4XH4XG4XE4o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma kmem_ok : forall E M b ne (lo n : Z),
  estart E (SA b 0) = lo -> elenZ E ne = n -> 0 <= lo < 2 ^ 64 -> 0 <= n -> lo + n <= 2 ^ 64 ->
  (forall x : word, lo <= bv_unsigned x < lo + n -> M x = Some (Z_to_bv 8 0)) ->
  know_ok SEGS E M [KWr (SA b 0) ne; KZero (SA b 0) ne].
Proof.
  intros E M b ne lo n Hs Hn Hlo Hn0 Hhi BYTE.
  assert (Hfl : flat E (SA b 0) (elenZ E ne)) by (unfold flat; rewrite Hs, Hn; lia).
  constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; split; try exact Hfl; rewrite ?Hs, ?Hn.
  - intros d w Hd Hdw. destruct w as [|w']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia. unfold wview. rewrite (BYTE x) by lia. discriminate.
  - intros i Hi. apply BYTE. rewrite u64_lit by lia. lia.
Qed.

Lemma kimg_in_hull_pure : forall k,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) k -> kimg_in_hull A k.
Proof.
  intros k H. unfold kimg_in_hull. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) H K Hin) as HK. destruct K; try exact I. destruct HK.
Qed.

(* [comment removed for export] *)
Lemma grant_vis_add : forall E cs1 cs2 base ne R FULL model (a n : word) nZ,
  CSOK E cs1 R FULL model ->
  vis_add A LIMIT cs1 base ne ([KWr (SA base 0) ne; KZero (SA base 0) ne] ++ kn cs1) = Some cs2 ->
  kimg_in_hull A (kn cs1) ->
  edenot E base = a -> edenot E ne = n -> bv_unsigned n = nZ -> 0 <= nZ -> bv_unsigned a + nZ <= 2 ^ 64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
     in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model)) = true
     /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false
     /\ argH E x = false) ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ -> FULL x = Some (Z_to_bv 8 0)) ->
  CSOK E cs2 R FULL model.
Proof.
  intros E cs1 cs2 base ne R FULL model a n nZ HC1 Hva Hkh Hbase Hne Un HnZ Hhi NEW ZERO.
  pose proof (u64_range a) as Ra.
  eapply vis_add_sound'; [exact Hva | exact HC1 |].
  destruct (vis_add_inv cs1 base ne _ cs2 Hva) as (nhi & Hnhi & Ecs2).
  apply Forall_app. split.
  - (* [comment removed for export] *)
    eapply (kmem_ok E _ base ne (bv_unsigned a) nZ); [unfold estart; cbn [a_base a_off]; rewrite Hbase; lia | unfold elenZ; rewrite Hne; exact Un | lia | lia | lia |].
    intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3).
    unfold Mr, mrestrict, hid. rewrite N3. cbn [orb].
    unfold vis. rewrite N1, N2. cbn [negb andb].
    assert (Hal : in_allow A E cs2 (bv_unsigned x) = true).
    { unfold in_allow, in_vis. rewrite Ecs2. cbn [a_vis existsb fst snd]. unfold uE. rewrite Hbase, Hne, Un.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    rewrite Hal. rewrite !orb_true_r. cbn [negb]. apply ZERO. exact Hx.
  - (* [comment removed for export] *)
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
    eapply know_ok_unhide'; [apply H_off_segments_cs' | exact Hkh | | | exact HK1].
    + intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
    + intros y Hy. apply hid_hull'. exact Hy.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gap_weight_eq : forall nZ l, gap_weight nZ l = sum_sizes l + Z.of_nat (length l) * (nZ + 4095).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "p'0h04__x1h11lh21xh32Hah49RES_len'0h57__arithh64__ffh76__sat2h86__sat3h96__sat4h:8__varmaph;5__with<4__x2h=4__x3h>4__x4h?4cstrh@5cstr0hA1mhB1nhC1yhD1zhE2IHhF6__sat1hG6__sat5hH1ahI1bi001bhJ5cstr1hK2nZhL2szi011pp;1p;2p;<p;3p;4p;6p;5p;Bp;7p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6g007eR6p4p710R:p8p1008Cp4p710R;P7p8P;P:p8p1008`p4p70R<P2p8P<P7p8P<P8p8P<P9p8P<P:p8P<p1009Np4p710R<p8p1009kp605611111000p100;1p4p741110R=p8p100;np605611111000R>P=p8p100=:p4p7210R?P7p8P?P8p8P?P9p8P?P:p8P?p100=fp4p710p8p100>mp605611111000R?P>p8P?P=p8p100@:p605611111000R>P?p8P>P=p8p100ADp6054111000R?p100BIp4p710R@p8P?P=p8P?p100CDp4p7511110RAp8p100DAp4p711RBP@p8PBp100E?p4p771111110p8PBPAp8p100FKp4p711RBP=p8PBp100G<p4p741110p8p100HBp4p70RBP7p8PBP8p8PBP9p8PBP:p8p100I8p6051000RBP8p8PBP9p8p100J<p4p70RBP>p8PBP?p8PBP@p8PBP=p8P4p4p7210R4P7p8P4P:p8p100K7p4p7210P:p8p100KVp4p73110P:p8p103T5p6051000R7g016aRBp4p710R?p8P7P<p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P;p8P>P<p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7P?p8P7P0p8P4p60521000R4P2p8P4P:p8P4P0p8p100L2p4p710P:p8P0P:p8p105Eip6054111000R:P@p8P:P=p8P:PAp8p108BCp6051000RAP8p8PAP9p8g00LPj1@Tg00M5j1fTg00MSj1]Tg00N6R9j2zTg00NVj1OTg0=7kj26Tg013fj18Tg01Nlj25Tg01OLRAj11Tg00ePj1CTg01g6j1<Tg00PZR8j20Tg01OlR:j2;Tg00TFj1Mj39Tg03]^j1jTg00R2j2ITg02`@l<LTg07jQj1`Tg07kOj1_Tg02f0j2^Tg02fSj3\Tg02^nj4[Tg01RTj1GTg07lOj1ZTg02M^j2KTg01Zhj2JTg01joj2YTg00\Mj2STg01gTj2yTg01kWj3xTg07mPj1wTg00^>j1VTg00^^j2ATg00`8j1sTg00`Vj1pTg01l^j2HTg00aAj2>Tg01Taj3DTg00adj4UTg00c1j2oTg00cSj2nTg00d?j3mTg00d^j4lTg02_Uj4iTg015aj3PTg00O6j2FTg01=3j1TTg0=90j1hTg00_<j1kTg00_Zj4QTg02kAj1gTP6j6WTg016Aj4eTPBj5dTg03^<j4qTg02j\l<rTg03aelBXTg00[Qj2tTg00f5j3uTg00gAj7vTf0RB#@#@p==%CB#Cp=7g00T`R6f3R=f2R@f1R0/;B'039p=4g00n4R4=96Bp=BA960Bp=EP6P6g03c8PBCqp=N1I6Bp=:g02`eR2P6P6P6PAPAP=P@P0g01@4R7P4PBM<rp=cP6P6P6P6P6P6P:PBP0P@P:P=f4R:P4f5R?f6R3f7R1f8R>MBXp=bP6P6P6P6P6P6P8P1P3P?P8P:P4P4P=P@P0PBMBXp=a1t4Bp=2Au60Bp=3P0g00j1g00jPR8P8g00k0R8PBg00kPFvp=R1;0B,0@p=?g00U>R3#@R5#@R<#=#=R;#fRC#]RD/zDRE#ORFPE16@B%8BRG15EB#1RH%C3RI#7#7#7#7#7#<RJ,0@C4X1F%17R7100JRK';RL,04RM#B1;4KRN,04RO#BP6P6%M6RPPBX26RQPP1E0B#jXC6X26P4P41I64RRPMPOPQPQPQ100B#N#:XA6XB6PRPLPNPQPQPQ1;0B#N#:XA6XB6P7PQPQ%1BRQ#:X22PRCcPKPK%:KM9bGaM<Lp,4SEGS#`,5ERRp,1AR7#_RN592%1RRL%1NRO'ERMP2P6%M2PAPP%10/EQA920B1^0B3\XC2X22PRPL%:LPNPO%:OM<Lp,8RES_len'C[R2PM%GNRN%2ORO%GRRR%2LRL%Z7RQ%=;#=#=#<R;'KRP%2Q%2;RA1JQ;#2[[RQ%<5RS%75#7#<RT'YRU1S4S%2T1ySTRV,S4[[RW%2SRXg012QRYAxST0UW3RT%2V\Y^3XRX%w7R7/K;RY%271J7;#2\A[RAg00laR7#VR;%O7R71A60%s6RV%p6RSP61H64RZg01W2R[1>63R\1H6JR]'39D6Z,3ZCU'R1oS8R8PBP@g00UcRZg00iQR^'I1nB@=9Z^dAm640ClR^b6b:b;X0610BJ9?44#B^06PBf9R4O1b5bFb7b8b9b@b?b4Ci%VERZ,60%8Z15EZ#1PKC4eP9PDPD16:BPGPH10:JC4APE@0R9,6?%8915E9#110?JC4[^1FPB161BPGPH101JC4P6%80R115E0RH#1RG10>JR?3?R91FC=RZ/04/0JR_/0B%8@R`,0ZRZ15E@Ra#T#1104JR4C4XD6P6%hGRG%1aRb=?`4,0_PZPBP4C4XD6P2PM%Ga%2bPNPOPRPLPPPQPUPWPTPXPYPAP;P7P6P61A6:P@%k6CQP01A6=CQPVP61>65R5,3\/3]1>6IRI1>6<R<135]R55D6'3'3P[13\I%<3R3,H6,3<=D65'3CU,RSP8P^b6b:b;X06X<6X=6X>610B0/0JA?@=K'010B@10=3PKC4^06^<6^=6^>6PBf:RK,5E#1%8KfAf;,FCO4b5b7b8b9bGbJb@b?b41FC@RC/0>/0J/0910C1PGP?C4e%TH#1%gHEW16>0PBEWPDPDP=P@Ce=PE0R@,6>%8@15E@#1P?C4eWEX1FXLDXIDP0PBO2n2001101010121100100XHEPBDdW1XK6o"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gap_ok_sound : forall E cs R FULL model nhi nZ,
  CSOK E cs R FULL model -> gap_ok A cs nhi = true -> 0 < nZ <= nhi -> nZ mod page_size = 0 ->
  exists a : word, OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.grant_ok_na (Z_to_bv 64 0) model a nZ = true.
Proof.
  intros E cs R FULL model nhi nZ HC Hg HnZ HnZal. unfold gap_ok in Hg. apply Z.leb_le in Hg.
  pose proof (co_totsz _ _ _ _ _ _ _ _ _ _ _ HC) as T.
  (* [comment removed for export] *)
  assert (L : (length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= n_res A + n_resx A + length (a_maps cs))%nat).
  { destruct (co_res _ _ _ _ _ _ _ _ _ _ _ HC) as (rx & Hres & _ & Hlx & _).
    rewrite length_app, Hres, length_app, RES_len'. pose proof (maps_match_length E _ _ (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)). lia. }
  assert (GW : gw_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= a_totsz cs).
  { pose proof (gap_weight_sizes nZ (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) as G1.
    rewrite gap_weight_eq in G1. lia. }
  destruct (free_gap_of_totals (m_vmmaps model) nZ (a_totsz cs) ltac:(lia) GW) as (g & Hal & Hfl & Hc & Hfree & Hpl).
  { rewrite FLOOR_eq, CEIL_eq.
    assert (0 <= a_totsz cs).
    { assert (0 <= sum_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))); [|lia].
      clear. induction (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) as [|[b sz] l IH]; cbn; [lia|]. pose proof (u64_range sz). lia. }
    set (len1 := length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) in *.
    set (len2 := (n_res A + n_resx A + length (a_maps cs))%nat) in *.
    assert (Z.of_nat len1 * (nZ + 4095) <= Z.of_nat len2 * (nhi + 4095)) by nia. nia. }
  pose proof bottomup_floor_val as Hfv. pose proof alloc_ceiling_val as Hcv.
  assert (HnZ0 : 0 < nZ) by lia.
  assert (Hisp : init_sp_ok (m_vmmaps model))
    by exact (proj2 (proj2 (proj2 (co_wf _ _ _ _ _ _ _ _ _ _ _ HC)))).
  pose proof (alloc_ceiling_le_alloc_top _ Hisp) as HAT.
  destruct (Placement.linux_place_exists (m_vmmaps model) (kb_thp (m_kernel model)) (Z_to_bv 64 0) nZ HnZ0 HnZal)
    as (a & Hlp).
  { exists g. right. apply Placement.gap_fits_b_iff. unfold Placement.gap_fits_b.
    rewrite Hfree, (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.leb_le (g + nZ) _)) by lia.
    rewrite (proj2 (Z.leb_le _ g)); [reflexivity|].
    apply Z.le_trans with bottomup_floor; [|exact Hfl].
    vm_compute. intro Hc0. discriminate Hc0. }
  destruct (Placement.linux_place_admissible _ _ _ _ _ HnZ0 HnZal Hlp) as (Hal' & Hpos' & Hhi' & Hfree').
  pose proof (alloc_top_lt (m_vmmaps model)) as Hat. unfold two_pow_64 in Hat.
  exists (Z_to_bv 64 a).
  apply (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.grant_ok_na_of_place _ _ _ _ HnZ0 HnZal).
  apply (proj2 (Placement.linux_place_is_iff _ _ _ _ _ HnZ0 HnZal)).
  rewrite u64_lit by lia. exact Hlp.
Qed.

Lemma budget_slack : forall E cs R FULL model extra,
  CSOK E cs R FULL model -> budget_ok LIMIT cs extra = true ->
  vm_backing_used model + extra <= vm_limit (m_vmmaps model).
Proof.
  intros E cs R FULL model extra HC Hb. unfold budget_ok in Hb. apply Z.leb_le in Hb.
  pose proof (vm_backing_used_le (ALLOW E cs) model (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (A_wf_allowA' E cs)).
  pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ HC). pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ HC).
  rewrite (co_limit _ _ _ _ _ _ _ _ _ _ _ HC). lia.
Qed.

Lemma lazy_interior_fresh : forall (a n : word),
  bv_unsigned a mod 4096 = 0 -> bv_unsigned n mod 4096 = 0 -> 0 < bv_unsigned n ->
  bv_unsigned a + bv_unsigned n <= 2 ^ 64 -> lazy_interior a n = [(a, n)].
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h01ah11np;1p;2p;6p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70RAP=p8PAP>p8PAP?p8PAP<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710RAp8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7PAp8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8p108BCp6051000R@P8p8P@P9p8g00LPj12Tg00M5j1<Tg00MSj1;Tg00O6j21Tg01g6j15Tg01Zhj24Tg00\Mj28Tg00PZj27Tg01gTj2:Tg00[Qj26Tg0=J_j69Tg00TFj3=Tf0R9#2#2p=0g00T`g00n4R@7=9p=3g00U>#2R8#2#0#0R6#<R<#;R?f1R0,1<%06#0#0#5'4#3R4f2R2,1<,8@f4R7,1<RAf3R3,1<'7%58%56':R6'6f5R8P7P311<8R8g01V:R<'4#3eP214A<#3eP018@AeP9178A/66eE9UUV4UX1?W0o"). Qed.




(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma refuse_eq : forall cs,
  refuse cs = with_ss cs (mk_ss (pc cs + 4) (sr_upd (s_regs (a_ss cs)) 10 (ELit ENOMEM_RET)) (kn cs) (nxt cs)).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h02csp;1p;2p;3p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70RAP=p8PAP>p8PAP?p8PAP<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710RAp8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7PAp8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8p108BCp6051000R@P8p8P@P9p8g02SBj1>Tg00LPj12Tg01g6j14Tg00PZj23Tg08gej1=Tg08hdj1;Tg02h5j15Tg0<`dj36Tg07hQj17Tg08Pdj18Tg08ihj49Tg0=Khj2:Tg00R2j2<Tg01=3j11Tf0R9#1#1p=0g02XCR@%>9g00U>#2#2#4'3%=9#;g01@4#0#0#0#0#0g0=Lj#536%79%89C9,:9,<@W0o"). Qed.

Lemma refuse_pc : forall cs, pc (refuse cs) = pc cs + 4.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h02csp;1p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70RAP=p8PAP>p8PAP?p8PAP<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710RAp8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7PAp8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8p108BCp6051000R@P8p8P@P9p8g02SBj14Tg00LPj10Tg01g6j12Tg00PZj21Tg00R2j23Tg02XCg00T`f0#4g00U>#0#0#2'1'3W0o"). Qed.

Lemma refuse_nxt : forall cs, nxt (refuse cs) = nxt cs.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h02csp;1p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70RAP=p8PAP>p8PAP?p8PAP<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710RAp8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7PAp8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8p108BCp6051000R@P8p8P@P9p8g08Pdj11Tg00R2j20Tg02XCg02`ef0#1'0W0o"). Qed.

Lemma refuse_ok : forall E cs R FULL model,
  CSOK E cs R FULL model ->
  CSOK E (refuse cs) (regupd R (Z_to_bv 5 (Z.of_nat 10)) (errno_ret ENOMEM)) FULL model.
Proof.
  intros E cs R FULL model HC. rewrite refuse_eq.
  eapply cs_ok_frame'; [exact HC | apply same_but_materialized_refl | exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | intros; reflexivity].
  cbn [s_regs mk_ss]. apply regs_ok_set_n'; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia |].
  cbn [edenot]. rewrite errno_ret_ENOMEM. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma refuse_cont : forall cs E R FULL model TA,
  CSOK E cs R FULL model -> 0 <= pc cs -> pc cs + 4 < 2 ^ 64 ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' (refuse cs) R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS scfg (cfg R' (pc (refuse cs)) FULL' model') TA) ->
  srealizes SEGS scfg (mkCfg (mkst (regupd R 10 (errno_ret ENOMEM)) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) TA.
Proof.
  intros cs E R FULL model TA HC Hp0 Hp4 HKA.
  specialize (HKA E (regupd R (Z_to_bv 5 (Z.of_nat 10)) (errno_ret ENOMEM)) FULL model
                  (conj (env_agree_refl' _ _) (env_agree_refl' _ _)) (refuse_ok E cs R FULL model HC) eq_refl).
  unfold cfg_of in HKA. rewrite refuse_pc, <- bv5_10 in HKA. rewrite (v_addi_pc (pc cs) Hp0 Hp4). exact HKA.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_aligned_sound : forall E M k e,
  know_ok SEGS E M k -> page_aligned k e = true -> bv_unsigned (edenot E e) mod 4096 = 0.
Proof.
  intros E M k e HK H.
  assert (GEN : 12 <= ealign k e -> bv_unsigned (edenot E e) mod 4096 = 0).
  { intros Hle. destruct (ealign_sound SEGS E M k e HK) as [Hr [q Hq]]. rewrite Hq.
    replace (2 ^ ealign k e) with (2 ^ (ealign k e - 12) * 4096) by (rewrite <- (Z.pow_add_r 2 _ 12) by lia; f_equal; lia).
    rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
  unfold page_aligned in H. destruct e as [z| | | | | | |]; try (apply GEN; apply Z.leb_le; exact H).
  apply Z.eqb_eq in H. cbn [edenot]. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  rewrite Z.mod_mod_divide; [exact H | exists (2 ^ 52); reflexivity].
Qed.

Lemma fixed_args_sound : forall E cs R FULL model top b off ne nlo nhi,
  CSOK E cs R FULL model -> fixed_args A cs top = Some (b, off, ne, nlo, nhi) ->
  split_lit (reg cs 10) = (b, off) /\ mmap_len cs = Some (ne, nlo, nhi)
  /\ bv_unsigned (edenot E (reg cs 10)) mod 4096 = 0
  /\ 0 < bv_unsigned (edenot E (reg cs 10))
  /\ (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <= img_lo A \/ img_hi A <= bv_unsigned (edenot E (reg cs 10)))   (* [comment removed for export] *)
  /\ bv_unsigned (edenot E (reg cs 10)) + nhi <= top
  /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = edenot E (reg cs 10)
  /\ flat_x (kn cs) b off ne = true.
Proof.
  intros E cs R FULL model top b off ne nlo nhi HC H. unfold fixed_args in H. pose proof HULL_lt as HL. unfold hull_lt in HL.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK. pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3).
  destruct (split_lit (reg cs 10)) as [b0 off0] eqn:Hsp.
  destruct (mmap_len cs) as [[[ne0 nlo0] nhi0]|] eqn:HML; [|discriminate].
  destruct (xlo (kn cs) (reg cs 10)) as [alo|] eqn:Hxl; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [ahi|] eqn:Hxh; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hflat].
  injection H as -> -> -> -> ->.
  apply andb_prop in Hc as [Hc Htop]. apply andb_prop in Hc as [Hc Himg]. apply andb_prop in Hc as [Hpa Hpos].
  apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop.
  pose proof (xlo_sound SEGS E _ (kn cs) _ alo HK Hxl). pose proof (xhi_sound SEGS E _ (kn cs) _ ahi HK Hxh).
  assert (Hhull : bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <= img_lo A \/ img_hi A <= bv_unsigned (edenot E (reg cs 10))).
  { apply orb_prop in Himg as [Himg|Hoff].
    - apply Z.leb_le in Himg. right. lia.
    - unfold off_image_x in Hoff. pose proof (ranges_apart_x_sound SEGS E _ (kn cs) b off ne (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)) HK Hoff) as D.
      destruct (APSK.flat_x_sound SEGS E _ (kn cs) b off ne HK Hflat) as (F1 & F2 & F3).
      pose proof (APSK.u_of_split E (reg cs 10) b off Hsp ltac:(lia)) as U.
      unfold estart, elenZ in D. cbn [a_base a_off] in D. rewrite !edenot_lit in D. rewrite !u64_lit in D by (unfold KHI in *; lia).
      unfold estart in U. cbn [a_base a_off] in U. lia. }
  repeat split; try lia.
  - eapply page_aligned_sound; [exact HK | exact Hpa].
  - apply (reg_sound' E cs R FULL model); [exact HC | lia].
  - exact Hflat.
Qed.

(* [comment removed for export] *)
Lemma split_flat_estart : forall E M k e b off n,
  know_ok SEGS E M k -> split_lit e = (b, off) -> flat_x k b off n = true ->
  estart E (SA b off) = bv_unsigned (edenot E e)
  /\ estart E (SA b off) + bv_unsigned (edenot E n) <= 2 ^ 64 /\ 0 < bv_unsigned (edenot E n).
Proof.
  intros E M k e b off n HK Hsp Hfl.
  destruct (APSK.flat_x_sound SEGS E M k b off n HK Hfl) as (F1 & F2 & F3).
  pose proof (APSK.u_of_split E e b off Hsp ltac:(lia)). repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma region_free_of_apart : forall E cs R FULL model b off ne (lo n : word),
  CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  forallb (fun m => ranges_apart_x (kn cs) b off ne (am_base m) 0 (am_len m)) (a_maps cs) = true ->
  estart E (SA b off) = bv_unsigned lo -> elenZ E ne = bv_unsigned n ->
  (bv_unsigned lo + bv_unsigned n <= img_lo A \/ img_hi A <= bv_unsigned lo) ->   (* [comment removed for export] *)
  (* [comment removed for export] *)
  bv_unsigned lo + bv_unsigned n <= KHI ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) lo n = true.
Proof.
  intros E cs R FULL model b off ne lo n HC Hnf Hall Hs Hn Himg Hkhi.
  rewrite region_free_app. apply andb_true_intro. split.
  - apply reserved_free_hull_apart; [exact (co_res _ _ _ _ _ _ _ _ _ _ _ HC) | exact Himg | exact Hkhi].
  - rewrite (proj1 (maps_match_exact' E _ _ Hnf) (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)). apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.region_free_intro. intros bm sm Hin.
    apply in_map_iff in Hin as (m & Hm & Hinm). unfold amap_den in Hm. injection Hm as <- <-.
    pose proof (proj1 (forallb_forall _ _) Hall m Hinm) as Hap.
    pose proof (ranges_apart_x_sound SEGS E _ (kn cs) b off ne (am_base m) 0 (am_len m) (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hap) as D.
    unfold estart in D at 2 3. cbn [a_base a_off] in D. unfold elenZ in D, Hn. rewrite Hs, Hn in D. lia.
Qed.

Definition fixed_cs1 (cs : acs) (kd : mkind) (eager : bool) (ne : expr) (nhi : Z) : acs :=
  let k := kn cs in
  let m := AM (reg cs 10) ne kd in
  let ksh := if mkind_eqb kd KRWLAZY then flat_map (fun p => shadow_facts A k [m] (fst p) (snd p)) (a_vis cs) else [] in
  add_entry cs (s_regs (a_ss cs)) (ksh ++ kn_grant_filter A k (a_maps cs)) (nxt cs) m nhi eager (a_ylo cs).

(* [comment removed for export] *)
Lemma shadow_facts_new_ok : forall E cs R FULL model (a n : word) nZ ne model' FULL',
  CSOK E cs R FULL model ->
  bv_unsigned n = nZ -> edenot E ne = n -> bv_unsigned a + nZ <= CEIL -> edenot E (reg cs 10) = a ->
  grant_post KRWLAZY a n model model' -> grant_mem KRWLAZY a n FULL FULL' ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
     in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false /\ argH E x = false) ->
  know_ok SEGS E (MR E cs model' FULL')
    (flat_map (fun p => shadow_facts A (kn cs) [AM (reg cs 10) ne KRWLAZY] (fst p) (snd p)) (a_vis cs)).
Proof.
  intros E cs R FULL model a n nZ ne model' FULL' HC Un Hne HaC Hra GPo [GM1 GM2] NEW.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (u64_range a) as Ra. pose proof SHADOW_ok' as SO.
  unfold know_ok. apply Forall_flat_map. apply Forall_forall. intros p Hp.
  unfold shadow_facts.
  destruct (shadow_of A (kn cs) (fst p) (snd p)) as [[sb sk] sn] eqn:Hsh.
  match goal with |- Forall _ (if ?c then _ else _) => destruct c eqn:Hjust; [|constructor] end.
  unfold shadow_of in Hsh.
  destruct (split_lit (eadd (mkSrl (kn cs) (fst p) 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection Hsh as -> -> <-.
  (* [comment removed for export] *)
  destruct (APSK.shadow_facts_holder SEGS A HS XN XE XB SHADOW_ok 0%nat E _ (kn cs) [AM (reg cs 10) ne KRWLAZY] (fst p) (snd p) sb sk HK Hss Hjust)
    as (_ & m & Hmin & _ & _ & I1 & I2).
  destruct Hmin as [<-|[]]. cbn [am_base am_len] in I1, I2. rewrite Hne, Un in I2. rewrite Hra in I1, I2.
  pose proof HaC as HaC'. unfold CEIL in HaC'.
  (* [comment removed for export] *)
  assert (Usn : bv_unsigned (edenot E (mkSrl (kn cs) (snd p) 3)) = bv_unsigned (edenot E (snd p)) / 8).
  { rewrite (mkSrl_denot SEGS E _ (kn cs) (snd p) 3 (Z_to_bv 64 3) HK) by (rewrite u64_lit by lia; reflexivity).
    rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
  rewrite Usn in I2.
  set (S0 := bv_unsigned (edenot E sb) + sk) in *.
  pose proof (u64_range (edenot E (fst p))) as Rb. pose proof (u64_range (edenot E (snd p))) as Rn.
  pose proof (u64_range (edenot E (mkSrl (kn cs) (snd p) 3))) as Rsn.
  assert (HS0 : S0 = shadow_off A + bv_unsigned (edenot E (fst p)) / 8).
  { pose proof (APSK.split_lit_denot E _ sb sk Hss) as D. unfold eadd in D. rewrite mkAlu_denot in D. cbn [edenot] in D.
    apply (f_equal bv_unsigned) in D. rewrite u_add64 in D.
    rewrite (mkSrl_denot SEGS E _ (kn cs) (fst p) 3 (Z_to_bv 64 3) HK) in D by (rewrite u64_lit by lia; reflexivity).
    rewrite u_srl64 in D. fold S0 in D.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite !u64_lit in D by (unfold CEIL in *; lia).
    change (2 ^ (3 mod 64)) with 8 in D.
    rewrite (Z.mod_small (bv_unsigned (edenot E (fst p)) / 8 + shadow_off A)) in D by (unfold CEIL in *; lia).
    unfold CEIL in *. lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  (* [comment removed for export] *)
  assert (BYTE : forall y : word, S0 <= bv_unsigned y < S0 + bv_unsigned (edenot E (snd p)) / 8 ->
            MR E cs model' FULL' y = Some (Z_to_bv 8 0)).
  { intros y Hy.
    assert (Hya : bv_unsigned a <= bv_unsigned y < bv_unsigned a + nZ) by (clear -Hy I1 I2; lia).
    destruct (NEW y Hya) as [N1 N2].
    assert (Hsh2 : in_sh A E cs (bv_unsigned y) = true).
    { unfold in_sh. apply existsb_exists. exists p. split; [exact Hp|]. unfold sh_lo, sh_hi, uE.
      apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt].
      - lia.
      - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (V : VIS E cs model' y = true).
    { unfold vis. rewrite (gp_maps _ _ _ _ _ GPo), (gp_noacc _ _ _ _ _ GPo). cbn [kind_none].
      rewrite in_ivs_cons. cbn [fst snd]. rewrite Un, N1.
      rewrite (proj2 (Z.leb_le (bv_unsigned a) (bv_unsigned y))) by lia.
      rewrite (proj2 (Z.ltb_lt (bv_unsigned y) (bv_unsigned a + nZ))) by lia.
      unfold in_allow. rewrite Hsh2. rewrite !orb_true_r. cbn [andb orb negb]. rewrite ?orb_true_r. reflexivity. }
    unfold Mr, mrestrict, hid. rewrite N2, V. cbn [orb negb].
    rewrite (GM2 y) by (rewrite Un; exact Hya). reflexivity. }
  assert (Hfl : flat E (SA sb sk) (elenZ E (mkSrl (kn cs) (snd p) 3))).
  { unfold flat, estart, elenZ. cbn [a_base a_off]. fold S0. rewrite Usn. unfold CEIL in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; split; try exact Hfl;
    unfold estart, elenZ; cbn [a_base a_off]; fold S0; rewrite Usn.
  - intros d w Hd Hdw. destruct w as [|w']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by (unfold CEIL in *; lia); unfold CEIL in *; lia|].
    intros x Hx. rewrite u64_lit in Hx by (unfold CEIL in *; lia). unfold wview. rewrite (BYTE x) by lia. discriminate.
  - intros i Hi. apply BYTE. rewrite u64_lit by (unfold CEIL in *; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma fixed_pre : forall cs top b off ne nlo nhi E R FULL model,
  CSOK E cs R FULL model ->
  fixed_args A cs top = Some (b, off, ne, nlo, nhi) -> top <= CEIL ->
  let addr := edenot E (reg cs 10) in
  let len := bv_unsigned (edenot E (reg cs 11)) in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  edenot E ne = n /\ bv_unsigned n = nZ /\ estart E (SA b off) = bv_unsigned addr
  /\ bv_unsigned addr mod 4096 = 0 /\ 0 < bv_unsigned addr /\ (bv_unsigned addr + nZ <= img_lo A \/ img_hi A <= bv_unsigned addr)   (* [comment removed for export] *)
  /\ bv_unsigned addr + nZ <= top
  /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = addr /\ nZ mod 4096 = 0 /\ 0 < nZ <= nhi.
Proof.
  intros cs top b off ne nlo nhi E R FULL model HC HFA Htop addr len nZ n.
  destruct (fixed_args_sound E cs R FULL model top b off ne nlo nhi HC HFA) as (Hsp & HML & Hal & Hpos & Himg & HtopA & R10 & Hflat).
  fold addr in Hal, Hpos, Himg, HtopA, R10.
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE).
  fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal. fold n in Hne.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (split_flat_estart E _ (kn cs) (reg cs 10) b off ne HK Hsp Hflat) as (Hest & Hfl2 & Hfl3). fold addr in Hest.
  pose proof (u64_range addr) as Ra.
  assert (Un0 : bv_unsigned n = nZ).
  { subst n. apply u64_lit. split; [lia|]. pose proof (u64_range (Z_to_bv 64 nZ)) as Rn. unfold CEIL in Htop. lia. }
  split; [exact Hne|]. split; [exact Un0|]. split; [exact Hest|]. split; [exact Hal|]. split; [exact Hpos|].
  split; [rewrite Hne, Un0 in Himg; exact Himg|]. split; [lia|]. split; [exact R10|]. split; [exact HnZal | lia].
Qed.

(* [comment removed for export] *)
Lemma maps_match_unhole : forall E ms h l, maps_match E ms l <-> maps_match E (unhole ms h) l.
Proof.
  intros E ms h. unfold unhole. induction ms as [|m ms IH]; intros l; [cbn; tauto|].
  cbn [List.map maps_match].
  destruct (is_hole m && amap_eqb m h)%bool eqn:Hc.
  - apply andb_prop in Hc as [Hh _].
    assert (Hf : is_fog m = true) by (unfold is_fog, is_hole in *; destruct (am_kind m); cbn in Hh |- *; congruence).
    rewrite Hf. cbn [is_fog is_tok_kind am_kind am_len].
    split; (intros [H|(iv & l' & H1 & H2 & H3)]; [left; apply IH; exact H | right; exists iv, l'; split; [exact H1|]; split; [exact H2| apply IH; exact H3]]).
  - destruct (is_fog m).
    + split; (intros [H|(iv & l' & H1 & H2 & H3)]; [left; apply IH; exact H | right; exists iv, l'; split; [exact H1|]; split; [exact H2| apply IH; exact H3]]).
    + split; (intros (l' & H1 & H2); exists l'; split; [exact H1 | apply IH; exact H2]).
Qed.

(* [comment removed for export] *)
Lemma same_val_sound : forall E M k a b,
  know_ok SEGS E M k -> same_val k a b = true -> bv_unsigned (edenot E a) = bv_unsigned (edenot E b).
Proof.
  intros E M k a b HK H. unfold same_val in H.
  destruct (expr_eqb a b) eqn:He; [apply expr_eqb_eq in He; subst; reflexivity|].
  destruct (lin_ge0 k [(a, 0)] [(b, 0)]) eqn:H1; [|discriminate].
  pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as X1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H) as X2.
  cbn [xt_den] in X1, X2. lia.
Qed.

(* [comment removed for export] *)
Lemma find_hole_sound : forall E M k ms a ne h,
  know_ok SEGS E M k -> find_hole k ms a ne = Some h ->
  In h ms /\ is_hole h = true
  /\ uE E (am_base h) = bv_unsigned (edenot E a) /\ uE E (am_len h) = bv_unsigned (edenot E ne).
Proof.
  intros E M k ms a ne h HK H. unfold find_hole in H. apply find_some in H as [Hin Hc].
  apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hh H1].
  split; [exact Hin|]. split; [exact Hh|]. unfold uE.
  split; symmetry; [exact (same_val_sound E M k _ _ HK H1) | exact (same_val_sound E M k _ _ HK H2)].
Qed.

(* [comment removed for export] *)
Lemma cs_ok_unhole : forall E cs R FULL model h,
  CSOK E cs R FULL model -> CSOK E (with_maps0 cs (unhole (a_maps cs) h)) R FULL model.
Proof.
  intros E cs R FULL model h HC.
  assert (ELEM : forall m, In m (unhole (a_maps cs) h) ->
            In m (a_maps cs) \/ exists m0, In m0 (a_maps cs) /\ m = AM (am_base m0) (am_len m0) KFOG).
  { intros m Hm. unfold unhole in Hm. apply in_map_iff in Hm as (m0 & Hm0 & Hin).
    destruct (is_hole m0 && amap_eqb m0 h)%bool; [right; exists m0; split; [exact Hin | symmetry; exact Hm0] | left; subst; exact Hin]. }
  destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xhna Xhlz Xtidv Xmres Xvdso Xrdr].
  constructor; unfold with_maps0 in *;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn] in *; try assumption.
  - (* [comment removed for export] *) apply (proj1 (maps_match_unhole E _ h _)). exact Xmaps.
  - (* [comment removed for export] *) apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
      [exact (proj1 (Forall_forall _ _) Xholes m Hin Hk) | cbn in Hk; discriminate].
  - (* [comment removed for export] *) apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
      [exact (proj1 (Forall_forall _ _) Xnone m Hin Hk) | cbn in Hk; destruct Hk; discriminate].
  - (* [comment removed for export] *) apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
      [exact (proj1 (Forall_forall _ _) Xkinds m Hin Hk) | cbn in Hk; discriminate].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CEIL_le_utop : forall E cs R FULL model, CSOK E cs R FULL model -> CEIL <= utop E.
Proof.
  intros E cs R FULL model HC. pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as [_ [ISP _]].
  pose proof (utop_bounds E) as UB. pose proof (utop_mod E) as UM.
  pose proof (Z.div_mod (utop E) 4096 ltac:(lia)) as Du. rewrite UM in Du.
  unfold CEIL, sp_window_lo in *. lia.
Qed.

Lemma mmap_fixed_grant_cs1 : forall cs ms0 kd (eager : bool) top b off ne nlo nhi E R FULL model model' FULL',
  CSOK E cs R FULL model ->
  fixed_args A cs top = Some (b, off, ne, nlo, nhi) -> top <= CEIL ->
  CSOK E (with_maps0 cs ms0) R FULL model ->
  let addr := edenot E (reg cs 10) in
  let len := bv_unsigned (edenot E (reg cs 11)) in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  (forall m, In m ms0 -> is_hole m = true ->
     bv_unsigned addr + nZ <= uE E (am_base m) \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned addr) ->
  (eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  grant_post kd addr n model model' -> grant_mem kd addr n FULL FULL' ->
  CSOK E (fixed_cs1 (with_maps0 cs ms0) kd eager ne nhi) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr) FULL' model'
  /\ (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ ->
        in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model')) = true
        /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false /\ argH E x = false).
Proof.
  intros cs ms0 kd eager top b off ne nlo nhi E R FULL model model' FULL' HC HFA Htop HC0 addr len nZ n Hrf Hholes Hbudget Hkind Hkfog GPo GM.
  destruct (fixed_pre cs top b off ne nlo nhi E R FULL model HC HFA Htop) as (Hne & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
  fold addr len nZ n in Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  assert (HaC : bv_unsigned addr + nZ <= CEIL) by lia.
  pose proof (CEIL_le_utop E cs R FULL model HC) as CU.
  assert (HaT : bv_unsigned addr + nZ <= utop E) by lia.
  assert (HnZpos : 0 < nZ) by lia.
  pose proof Himg as Himg_a.
  pose proof (grant_new_facts E cs R FULL model addr n nZ HC Hrf Un HnZpos Himg_a HaT) as NEW.
  destruct (grant_cs1_ok E (with_maps0 cs ms0) R FULL model kd addr n nZ model' FULL'
              (s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)
              (if mkind_eqb kd KRWLAZY then flat_map (fun p => shadow_facts A (kn cs) [AM (reg cs 10) ne kd] (fst p) (snd p)) (a_vis cs) else [])
              (reg cs 10) ne nhi eager (a_ylo cs) (nxt cs)
              HC0 Un HnZpos HnZal Hal Himg_a HaT Hrf GPo GM) as (HC1 & MROUT & MRSAME).
  - apply regs_ok_regupd_same; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | exact R10].
  - reflexivity.
  - exact Hne.
  - destruct kd; cbn [mkind_eqb]; try constructor.
    change (MR E (with_maps0 cs ms0) model' FULL') with (MR E cs model' FULL').
    eapply shadow_facts_new_ok; [exact HC | exact Un | exact Hne | exact HaC | reflexivity | exact GPo | exact GM |].
    intros x Hx. destruct (NEW x Hx) as (_ & N1 & N2 & _). auto.
  - exact Hkind.
  - exact Hkfog.
  - lia.
  - exact Hbudget.
  - cbn [with_maps0 a_ylo]. lia.
  - cbn [with_maps0 a_maps]. exact Hholes.
  - split; [exact HC1|].
    intros x Hx. destruct (NEW x Hx) as (N0 & N1 & N2 & _). split; [|auto].
    rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons. cbn [fst snd]. rewrite Un.
    apply orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_old_facts : forall cs b off ne nlo nhi E R FULL model,
  CSOK E cs R FULL model ->
  fixed_args A cs (resx_clear cs) = Some (b, off, ne, nlo, nhi) ->   (* [comment removed for export] *)
  no_fog (a_maps cs) = true ->
  forallb (fun m => ranges_apart_x (kn cs) b off ne (am_base m) 0 (am_len m)) (a_maps cs) = true ->
  let addr := edenot E (reg cs 10) in
  let nZ := page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) in
  CSOK E (with_maps0 cs (a_maps cs)) R FULL model
  /\ region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr (Z_to_bv 64 nZ) = true
  /\ (forall m, In m (a_maps cs) -> is_hole m = true ->
        bv_unsigned addr + nZ <= uE E (am_base m) \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned addr).
Proof.
  intros cs b off ne nlo nhi E R FULL model HC HFA Hnf Hall addr nZ.
  destruct (fixed_pre cs (resx_clear cs) b off ne nlo nhi E R FULL model HC HFA
              ltac:(unfold resx_clear; pose proof (Z.le_min_l KHI (a_ylo cs)); unfold KHI, CEIL in *; lia))
    as (Hne & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
  unfold resx_clear in HtopA.
  fold addr nZ in Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  split; [|split].
  - destruct cs; exact HC.
  - eapply region_free_of_apart; [exact HC | exact Hnf | exact Hall | exact Hest | unfold elenZ; rewrite Hne; reflexivity | rewrite Un; exact Himg |].
    rewrite Un. pose proof (Z.le_min_l KHI (a_ylo cs)). lia.
  - intros m Hm Hk. exfalso. unfold no_fog in Hnf. pose proof (proj1 (forallb_forall _ _) Hnf m Hm) as X.
    apply negb_true_iff in X. unfold is_fog, is_hole in *. destruct (am_kind m); cbn in X, Hk; congruence.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_hole_facts : forall cs b off ne nlo nhi h E R FULL model,
  CSOK E cs R FULL model ->
  fixed_args A cs CEIL = Some (b, off, ne, nlo, nhi) ->
  find_hole (kn cs) (a_maps cs) (reg cs 10) ne = Some h ->
  forallb (fun m => negb (is_hole m) || ranges_apart_x (kn cs) b off ne (am_base m) 0 (am_len m)) (unhole (a_maps cs) h) = true ->
  let addr := edenot E (reg cs 10) in
  let nZ := page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) in
  CSOK E (with_maps0 cs (unhole (a_maps cs) h)) R FULL model
  /\ region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr (Z_to_bv 64 nZ) = true
  /\ (forall m, In m (unhole (a_maps cs) h) -> is_hole m = true ->
        bv_unsigned addr + nZ <= uE E (am_base m) \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned addr).
Proof.
  intros cs b off ne nlo nhi h E R FULL model HC HFA Hfh Hap addr nZ.
  destruct (fixed_pre cs CEIL b off ne nlo nhi E R FULL model HC HFA ltac:(lia)) as (Hne & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
  fold addr nZ in Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (find_hole_sound E _ (kn cs) (a_maps cs) (reg cs 10) ne h HK Hfh) as (Hin & Hh & Hhb & Hhn).
  fold addr in Hhb. rewrite Hne, Un in Hhn.
  destruct (proj1 (Forall_forall _ _) (co_holes _ _ _ _ _ _ _ _ _ _ _ HC) h Hin Hh) as [F1 F2].
  rewrite Hhb, Hhn in F1, F2.
  split; [apply cs_ok_unhole; exact HC|]. split.
  - apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.region_free_intro. intros b' s' Hin'. rewrite Un. destruct (F1 (b', s') Hin'); cbn [fst snd] in *; lia.
  - intros m Hm Hk. pose proof (proj1 (forallb_forall _ _) Hap m Hm) as X. cbn beta in X. rewrite Hk in X. cbn [negb orb] in X.
    pose proof (ranges_apart_x_sound SEGS E _ (kn cs) b off ne (am_base m) 0 (am_len m) HK X) as D.
    unfold estart in D at 2 3. cbn [a_base a_off] in D. unfold elenZ in D. rewrite Hest, Hne, Un in D. unfold uE. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma seps_map_disjoint : forall (f : amap -> word * word) ms m m',
  seps (map f ms) -> In m ms -> In m' ms -> m <> m' -> iv_disjoint (f m) (f m').
Proof.
  intros f ms. induction ms as [|h t IH]; intros m m' Hs Hm Hm' Hne; [destruct Hm|].
  cbn [map] in Hs. inversion Hs as [|p l Hf Hl]; subst.
  destruct Hm as [<-|Hm]; destruct Hm' as [<-|Hm'].
  - exfalso. exact (Hne eq_refl).
  - exact (proj1 (Forall_forall _ _) Hf (f m') (in_map f t m' Hm')).
  - pose proof (proj1 (Forall_forall _ _) Hf (f m) (in_map f t m Hm)) as D. unfold iv_disjoint in *. lia.
  - exact (IH m m' Hl Hm Hm' Hne).
Qed.

(* [comment removed for export] *)
Lemma maps_match_disjoint : forall E ms l m m',
  maps_match E ms l -> seps l -> In m ms -> In m' ms -> is_fog m = false -> is_fog m' = false -> m <> m' ->
  iv_disjoint (amap_den E m) (amap_den E m').
Proof.
  intros E ms. induction ms as [|h t IH]; intros l m m' HM Hs Hm Hm' Hf Hf' Hne; [destruct Hm|].
  cbn [maps_match] in HM. destruct (is_fog h) eqn:Hfh.
  - assert (Hmt : In m t) by (destruct Hm as [<-|Hm]; [congruence | exact Hm]).
    assert (Hmt' : In m' t) by (destruct Hm' as [<-|Hm']; [congruence | exact Hm']).
    destruct HM as [HM|(iv & l' & -> & _ & HM)].
    + exact (IH l m m' HM Hs Hmt Hmt' Hf Hf' Hne).
    + inversion Hs as [|p l0 Hfa Hl]; subst. exact (IH l' m m' HM Hl Hmt Hmt' Hf Hf' Hne).
  - destruct HM as (l' & -> & HM). inversion Hs as [|p l0 Hfa Hl]; subst.
    destruct Hm as [<-|Hm]; destruct Hm' as [<-|Hm'].
    + exfalso. exact (Hne eq_refl).
    + exact (proj1 (Forall_forall _ _) Hfa (amap_den E m') (maps_match_In E t l' m' HM Hm' Hf')).
    + pose proof (proj1 (Forall_forall _ _) Hfa (amap_den E m) (maps_match_In E t l' m HM Hm Hf)) as D. unfold iv_disjoint in *. lia.
    + exact (IH l' m m' HM Hl Hm Hm' Hf Hf' Hne).
Qed.

(* [comment removed for export] *)
Lemma overlap_sum_contained : forall l (b s : word) lo hi,
  seps l -> In (b, s) l -> bv_unsigned b <= lo -> hi <= bv_unsigned b + bv_unsigned s -> lo <= hi ->
  overlap_sum l lo hi <= hi - lo.
Proof.
  intros l b s lo hi Hs Hin H1 H2 Hlh. induction l as [|p l IH]; [destruct Hin|].
  inversion Hs as [|p' l' Hf Hl]; subst. rewrite overlap_sum_cons. destruct Hin as [->|Hin].
  - pose proof (iv_count_in_rng_le (b, s) lo hi Hlh).
    assert (Z0 : overlap_sum l lo hi = 0); [|lia].
    clear IH Hs. revert Hf Hl. induction l as [|q l IH2]; intros Hf Hl; [reflexivity|]. rewrite overlap_sum_cons.
    apply Forall_cons_iff in Hf as [Hq Hf']. inversion Hl; subst.
    rewrite (IH2 Hf' ltac:(assumption)). rewrite iv_count_in_rng_disjoint; [lia|].
    unfold iv_disjoint, B, S in *. cbn [fst snd] in Hq. lia.
  - pose proof (IH Hl Hin) as IH'. rewrite iv_count_in_rng_disjoint; [lia|].
    pose proof (proj1 (Forall_forall _ _) Hf (b, s) Hin) as D. unfold iv_disjoint, B, S in *. cbn [fst snd] in D. lia.
Qed.

Lemma rekind_den : forall E ms m, map (amap_den E) (rekind ms m) = map (amap_den E) ms.
Proof.
  intros E ms m. unfold rekind. rewrite map_map. apply map_ext. intros m'. destruct (amap_eqb m' m); reflexivity.
Qed.

Lemma in_rekind : forall ms m m', In m' (rekind ms m) ->
  exists m0, In m0 ms /\ ((m0 = m /\ m' = AM (am_base m) (am_len m) KRW) \/ (m0 <> m /\ m' = m0)).
Proof.
  intros ms m m' H. unfold rekind in H. apply in_map_iff in H as (m0 & Hm0 & Hin). exists m0. split; [exact Hin|].
  destruct (amap_eqb m0 m) eqn:He.
  - left. apply APSK.amap_eqb_eq in He. subst m0. auto.
  - right. split; [|symmetry; exact Hm0]. intros ->. rewrite amap_eqb_refl in He. discriminate.
Qed.

Lemma covered_maps_subtract : forall l lo hi x,
  ivs_wf l -> lo <= hi ->
  covered (maps_subtract l lo hi) x = (covered l x && negb (in_rng lo hi x))%bool.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmLibK ()) ["Nodes"] "h01xh11Ph22hih31lh42lop;1p;2p;3p;5p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70RAP=p8PAP>p8PAP?p8PAP<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p103T5p6051000R7p1016ap4p710RAp8P7P;p8P7P5p8P7P0p8p103WUR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p103c\R4p6051001R7P1p8P7P3p8P7PAp8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100L2p4p710P6p8P0P6p8p105Eip6054111000R6P?p8P6P<p8P6P@p8p108BCp6051000R@P8p8P@P9p8g00LPj10Tg00M5j1ATg00MSj1:Tg00N6j29Tg00NVj1@Tg01oCj13Tg00[Qj2;Tg020=j32Tg01Loj25Tg02ARj36Tg01B8j11Tg00QTj24Tg00TFj37Tg00SKj28Tg00Z0j2?Tg02@Mj5>Tg010[j3<j4=Tg00U>#0#0#0#0#0#0#A#:R9/99#@g00T`R9f3R@#3f2R8,;@g00UcR6\9f0R<f6R?f5R0f4R432R2'5f1R7P<O1A6?0<#1'4X09/5?579]1RA182<18?<A604<#1'4576^09R6A204@#31?A6P0P4P@P7P<D>3<P8C=UUX09X29W4W3o"). Qed.

Inductive slarm := SlE | SlF | SlG | SlM.

Definition sl_nn (s : slarm) : bool := match s with SlG => true | _ => false end.
Definition sl_charge (s : slarm) : bool := match s with SlE | SlM => true | _ => false end.

Record slice_post (s : slarm) (addr n : word) (model model' : Model) : Prop := SP {
  sp_maps : vm_maps (m_vmmaps model') = vm_maps (m_vmmaps model);
  sp_res : vm_reserved (m_vmmaps model') = vm_reserved (m_vmmaps model);
  sp_noacc : vm_noaccess (m_vmmaps model') =
             (if sl_nn s then [(addr, n)] else [])
               ++ maps_subtract (vm_noaccess (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n);
  sp_lazy : m_vm_lazy model' =
            match s with
            | SlM => m_vm_lazy model
            | SlF => (addr, n) :: maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
            | _ => maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
            end;
  sp_mat : m_vm_materialized model' =
           match s with
           | SlM => m_vm_materialized model
           | _ => List.filter (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model)
           end;
  sp_limit : vm_limit (m_vmmaps model') = vm_limit (m_vmmaps model);
  sp_brk : vm_brk (m_vmmaps model') = vm_brk (m_vmmaps model);
  sp_sbrk : vm_start_brk (m_vmmaps model') = vm_start_brk (m_vmmaps model);
  sp_mbase : vm_mmap_base (m_vmmaps model') = vm_mmap_base (m_vmmaps model);
  sp_halted : m_halted model' = m_halted model;
  sp_fds : m_fds model' = m_fds model;
  sp_fs : m_fs model' = m_fs model;
  sp_tid : m_tid model' = m_tid model;
  sp_isp : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model);  (* [comment removed for export] *)
  sp_kernel : m_kernel model' = m_kernel model;
  sp_rdr : m_channel_reader model' = m_channel_reader model }.

Definition slice_mem (s : slarm) (addr n : word) (FULL FULL' : word -> option byte) : Prop :=
  (forall x : word, bv_unsigned x < bv_unsigned addr \/ bv_unsigned addr + bv_unsigned n <= bv_unsigned x -> FULL' x = FULL x)
  /\ (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + bv_unsigned n ->
        FULL' x = if sl_nn s then None else Some (Z_to_bv 8 0)).

(* [comment removed for export] *)
Record slice_hyps (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model)
       (s : slarm) (m : amap) (addr n : word) (nZ : Z) (model' : Model) (FULL' : word -> option byte) : Prop := SH_ {
  sh_C : CSOK E cs R FULL model;
  sh_m : In m (a_maps cs);
  sh_nf : is_fog m = false;
  sh_Un : bv_unsigned n = nZ;
  sh_pos : 0 < nZ;
  sh_nal : nZ mod 4096 = 0;
  sh_al : bv_unsigned addr mod 4096 = 0;
  sh_in1 : bv_unsigned (edenot E (am_base m)) <= bv_unsigned addr;
  sh_in2 : bv_unsigned addr + nZ <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m));
  sh_post : slice_post s addr n model model';
  sh_mem : slice_mem s addr n FULL FULL';
  sh_F : s = SlF -> am_kind m = KRWLAZY;
  sh_nF : s <> SlF -> am_kind m <> KRWLAZY }.

Section Slice.
  Variables (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Variables (s : slarm) (m : amap) (addr n : word) (nZ : Z) (model' : Model) (FULL' : word -> option byte).
  Hypothesis SH : slice_hyps E cs R FULL model s m addr n nZ model' FULL'.
  Let HC := sh_C _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hm := sh_m _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hnf := sh_nf _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Un := sh_Un _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let HnZpos := sh_pos _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let HnZal := sh_nal _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hal := sh_al _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hin1 := sh_in1 _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hin2 := sh_in2 _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let SPo := sh_post _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let SM := sh_mem _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let HF := sh_F _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let HnF := sh_nF _ _ _ _ _ _ _ _ _ _ _ _ SH.

  Let lo := bv_unsigned addr.
  Let hi := bv_unsigned addr + nZ.

  (* [comment removed for export] *)
  Lemma sl_bounds : 0 < bv_unsigned (edenot E (am_len m)) /\ bv_unsigned (edenot E (am_base m)) mod 4096 = 0
                    /\ bv_unsigned (edenot E (am_len m)) mod 4096 = 0
                    /\ (bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= img_lo A
                        \/ img_hi A <= bv_unsigned (edenot E (am_base m)))
                    /\ bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= utop E.
  Proof.
    pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) as B.
    exact (proj1 (Forall_forall _ _) B (amap_den E m) (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf)).
  Qed.

  Lemma sl_lohi : (hi <= img_lo A \/ img_hi A <= lo) /\ hi <= utop E /\ lo < hi /\ hi <= 2 ^ 64 /\ lo mod 4096 = 0 /\ hi mod 4096 = 0.
  Proof.
    pose proof sl_bounds as (B1 & B2 & B3 & B4 & B5). pose proof (utop_le_TOPC _ _ _ _ _ HC) as UT. subst lo hi. unfold TOPC in *.
    repeat split; try lia. rewrite Z.add_mod, Hal, HnZal by lia. reflexivity.
  Qed.

  Lemma sl_in_maps : forall x : word, lo <= bv_unsigned x < hi -> in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model)) = true.
  Proof.
    intros x Hx. eapply in_ivs_maps_match; [exact (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hm | exact Hnf |]. subst lo hi. lia.
  Qed.

  Lemma sl_wf' : model_ivs_wf model'.
  Proof.
    pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & Wsp). pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
    assert (iv_wf (addr, n)) by (unfold iv_wf, B, S; cbn; subst lo hi; lia).
    unfold model_ivs_wf. rewrite (sp_maps _ _ _ _ _ SPo), (sp_noacc _ _ _ _ _ SPo), (sp_lazy _ _ _ _ _ SPo).
    split; [exact W1|]. split; [|split; [|unfold init_sp_ok in *; rewrite (sp_isp _ _ _ _ _ SPo); exact Wsp]].
    - apply ivs_wf_app; [destruct (sl_nn s); [apply ivs_wf_cons; [assumption | apply ivs_wf_nil] | apply ivs_wf_nil] |].
      apply maps_subtract_wf; [exact W2 | rewrite Un; lia].
    - destruct s; try exact W3; try (apply ivs_wf_cons; [assumption|]); apply maps_subtract_wf; try assumption; rewrite Un; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sl_noacc_out : forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x ->
    in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model')) = in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)).
  Proof.
    intros x Hx. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _).
    rewrite (sp_noacc _ _ _ _ _ SPo), in_ivs_app. rewrite !in_ivs_covered.
    rewrite covered_maps_subtract by (try exact W2; rewrite Un; lia). rewrite Un.
    replace (in_rng (bv_unsigned addr) (bv_unsigned addr + nZ) (bv_unsigned x)) with false
      by (symmetry; unfold in_rng; apply andb_false_iff; subst lo hi; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    destruct (sl_nn s); cbn [app]; [|rewrite andb_true_r; reflexivity].
    rewrite <- in_ivs_covered, in_ivs_cons. cbn [fst snd in_ivs existsb]. rewrite Un.
    replace ((bv_unsigned addr <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned addr + nZ))%bool with false
      by (symmetry; apply andb_false_iff; subst lo hi; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    cbn [orb]. rewrite andb_true_r. reflexivity.
  Qed.

  Lemma sl_noacc_in : forall x : word, lo <= bv_unsigned x < hi ->
    in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model')) = sl_nn s.
  Proof.
    intros x Hx. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _).
    rewrite (sp_noacc _ _ _ _ _ SPo), in_ivs_app. rewrite (in_ivs_covered _ (maps_subtract _ _ _)).
    rewrite covered_maps_subtract by (try exact W2; rewrite Un; lia). rewrite Un.
    replace (in_rng (bv_unsigned addr) (bv_unsigned addr + nZ) (bv_unsigned x)) with true
      by (symmetry; unfold in_rng; apply andb_true_intro; subst lo hi; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [negb]. rewrite andb_false_r, orb_false_r.
    destruct (sl_nn s); cbn [app in_ivs existsb fst snd]; [|reflexivity]. rewrite Un.
    rewrite (proj2 (Z.leb_le _ _)) by (subst lo; lia). rewrite (proj2 (Z.ltb_lt _ _)) by (subst hi; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sl_lazy_out : forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x ->
    page_in_ranges (page_base x) (m_vm_lazy model') = page_in_ranges (page_base x) (m_vm_lazy model).
  Proof.
    intros x Hx. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _). pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
    pose proof (page_of_byte_out_aligned x lo hi L5 L6 Hx) as P. subst lo hi.
    rewrite (sp_lazy _ _ _ _ _ SPo). destruct s; try reflexivity.
    - apply page_in_ranges_subtract_out; [exact W3 | rewrite Un; lia | unfold page_size; rewrite Un; lia].
    - rewrite page_in_ranges_cons_out; [| unfold page_size; rewrite Un; lia | rewrite Un; lia].
      apply page_in_ranges_subtract_out; [exact W3 | rewrite Un; lia | unfold page_size; rewrite Un; lia].
    - apply page_in_ranges_subtract_out; [exact W3 | rewrite Un; lia | unfold page_size; rewrite Un; lia].
  Qed.

  Lemma sl_lazy_in : forall x : word, lo <= bv_unsigned x < hi ->
    page_in_ranges (page_base x) (m_vm_lazy model') =
      match s with SlM => page_in_ranges (page_base x) (m_vm_lazy model) | SlF => true | _ => false end.
  Proof.
    intros x Hx. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _). pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
    destruct (page_of_byte_in_aligned x lo hi L5 L6 Hx) as [P1 P2]. subst lo hi.
    rewrite (sp_lazy _ _ _ _ _ SPo). destruct s; try reflexivity.
    - apply page_in_ranges_subtract_in; [exact W3 | rewrite Un; lia].
    - apply page_in_ranges_cons_in; unfold page_size; rewrite ?Un; lia.
    - apply page_in_ranges_subtract_in; [exact W3 | rewrite Un; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma sl_vis_out : forall cs1 (x : word), a_vis cs1 = a_vis cs -> (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
    VIS E cs1 model' x = VIS E cs model x.
  Proof.
    intros cs1 x Hv Hx. unfold vis. rewrite (sp_maps _ _ _ _ _ SPo), (sl_noacc_out x Hx), (sl_lazy_out x Hx), (in_allow_ext E cs cs1 Hv). reflexivity.
  Qed.

  Lemma sl_MR_out : forall cs1 (x : word), a_vis cs1 = a_vis cs -> (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
    MR E cs1 model' FULL' x = MR E cs model FULL x.
  Proof.
    intros cs1 x Hv Hx. unfold Mr, mrestrict, hid. rewrite (sl_vis_out cs1 x Hv Hx). rewrite (proj1 SM x) by (subst lo hi; rewrite Un; exact Hx). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sl_vis_in_E : s = SlE -> forall cs1 (x : word), lo <= bv_unsigned x < hi -> VIS E cs1 model' x = true.
  Proof.
    intros Hs cs1 x Hx. unfold vis. rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx), (sl_lazy_in x Hx). subst s.
    cbn. rewrite !orb_true_r. reflexivity.
  Qed.

  Lemma sl_vis_in_G : s = SlG -> forall cs1 (x : word), lo <= bv_unsigned x < hi -> argH E x = false -> VIS E cs1 model' x = false.
  Proof.
    intros Hs cs1 x Hx Ha. pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6). unfold vis.
    rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx). subst s. cbn [sl_nn negb andb].
    replace (in_hull A (bv_unsigned x)) with false by (symmetry; unfold in_hull; apply andb_false_iff; destruct L1; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    replace (utop E <=? bv_unsigned x) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  Lemma sl_vis_in_F : s = SlF -> forall cs1 (x : word), a_vis cs1 = a_vis cs -> lo <= bv_unsigned x < hi -> VIS E cs1 model' x = VIS E cs model x.
  Proof.
    intros Hs cs1 x Hv Hx. unfold vis.
    rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx), (sl_lazy_in x Hx), (in_allow_ext E cs cs1 Hv).
    destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) m Hm (HF Hs) x ltac:(subst lo hi; lia)) as [K1 K2].
    rewrite K1, K2. subst s. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sl_eager : eager_used model' <= eager_used model + (if sl_charge s then nZ else 0).
  Proof.
    pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf. pose proof Hwf as (W1 & W2 & W3 & _). pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
    rewrite (eager_used_sem model' sl_wf'), (eager_used_sem model Hwf). rewrite (sp_maps _ _ _ _ _ SPo).
    set (C := vm_noaccess (m_vmmaps model) ++ m_vm_lazy model).
    set (C' := vm_noaccess (m_vmmaps model') ++ m_vm_lazy model').
    assert (CEQ : forall x, covered C' x =
              ((sl_nn s && in_rng lo hi x)
               || (covered (vm_noaccess (m_vmmaps model)) x && negb (in_rng lo hi x))
               || match s with
                  | SlM => covered (m_vm_lazy model) x
                  | SlF => in_rng lo hi x || (covered (m_vm_lazy model) x && negb (in_rng lo hi x))
                  | _ => covered (m_vm_lazy model) x && negb (in_rng lo hi x)
                  end)%bool).
    { intros x. subst C'. rewrite (sp_noacc _ _ _ _ _ SPo), (sp_lazy _ _ _ _ _ SPo). rewrite !covered_app.
      rewrite covered_maps_subtract by (try exact W2; rewrite Un; lia). rewrite Un. fold hi. fold lo.
      assert (HD : covered (if sl_nn s then [(addr, n)] else []) x = (sl_nn s && in_rng lo hi x)%bool).
      { destruct (sl_nn s); cbn [covered existsb]; [|reflexivity]. unfold in_iv, B, S. cbn [fst snd]. rewrite Un. fold lo hi. apply orb_false_r. }
      rewrite HD. f_equal.
      assert (SC : lo <= hi) by (unfold lo, hi; lia).
      destruct s; cbn [sl_nn]; rewrite ?covered_maps_subtract by first [exact W3 | exact SC]; try reflexivity.
      unfold covered at 1. cbn [existsb]. fold (covered (maps_subtract (m_vm_lazy model) lo hi) x).
      rewrite covered_maps_subtract by first [exact W3 | exact SC]. unfold in_iv, B, S. cbn [fst snd]. rewrite Un. reflexivity. }
    assert (CC : forall x, covered C x = (covered (vm_noaccess (m_vmmaps model)) x || covered (m_vm_lazy model) x)%bool).
    { intros x. subst C. apply covered_app. }
    assert (MONO : sum_count (fun x => negb (covered C' x)) (vm_maps (m_vmmaps model))
                   <= sum_count (fun x => (negb (covered C x) || (in_rng lo hi x && sl_charge s))%bool) (vm_maps (m_vmmaps model))).
    { apply sum_count_mono. intros x Hx. apply negb_true_iff in Hx. rewrite CEQ in Hx. rewrite CC.
      destruct s; cbn [sl_nn sl_charge] in Hx |- *;
        destruct (in_rng lo hi x), (covered (vm_noaccess (m_vmmaps model)) x), (covered (m_vm_lazy model) x); cbn in Hx |- *; congruence. }
    pose proof (sum_count_or_le (fun x => negb (covered C x)) (fun x => (in_rng lo hi x && sl_charge s)%bool) (vm_maps (m_vmmaps model))) as OR.
    assert (CH : sum_count (fun x => (in_rng lo hi x && sl_charge s)%bool) (vm_maps (m_vmmaps model)) <= (if sl_charge s then nZ else 0)).
    { destruct (sl_charge s).
      - rewrite (sum_count_ext _ (in_rng lo hi)) by (intros; apply andb_true_r).
        pose proof (overlap_sum_contained (vm_maps (m_vmmaps model)) (edenot E (am_base m)) (edenot E (am_len m)) lo hi
                      (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf)
                      ltac:(unfold lo; lia) ltac:(unfold hi; lia) ltac:(unfold lo, hi; lia)) as OV.
        unfold overlap_sum in OV. unfold lo, hi in *. lia.
      - rewrite (sum_count_ext _ (fun _ => false)) by (intros; apply andb_false_r).
        clear. induction (vm_maps (m_vmmaps model)) as [|q l IH]; cbn; [lia|]. unfold iv_count. rewrite zcount_const_false. lia. }
    cbv beta in OR. lia.
  Qed.

  Lemma page_base_aligned : forall p : word, bv_unsigned p mod 4096 = 0 -> page_base p = p.
  Proof.
    intros p Hp. unfold page_base, page_base_of, page_size. apply bv_eq. pose proof (u64_range p).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite u64_lit; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition sl_hna (ae ne : expr) : list hop := (if sl_nn s then [HCons ae ne] else []) ++ HSub ae ne :: a_hna cs.
  Definition sl_hlz (ae ne : expr) : list hop :=
    match s with SlM => a_hlz cs | SlF => HCons ae ne :: HSub ae ne :: a_hlz cs | _ => HSub ae ne :: a_hlz cs end.

  Lemma slice_cs1_ok : forall sr' R' k' p nx nhi (ae ne : expr),
    regs_ok E sr' R' ->
    know_ok SEGS E (MR E cs model' FULL') k' ->
    nZ <= nhi ->
    (sl_charge s = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
    edenot E ae = addr -> edenot E ne = n ->
    CSOK E (ACS (mk_ss p sr' k' nx)
                (match s with SlF => a_maps cs | _ => rekind (a_maps cs) m end)
                (a_totsz cs) (a_ylo cs)
                (if sl_charge s then a_eager cs + nhi else a_eager cs)
                (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (sl_hna ae ne) (sl_hlz ae ne)) R' FULL' model'.
  Proof.
    intros sr' R' k' p nx nhi ae ne Hregs Hknow Hnhi Hbudget Hae HneX.
    assert (Es : exists s0, s0 = s) by (exists s; reflexivity). destruct Es as [s0 Es].
    pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf. pose proof Hwf as (W1 & W2 & W3 & _).
    pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6). pose proof sl_bounds as (B1 & B2 & B3 & B4 & B5).
    pose proof sl_wf' as Hwf'. pose proof sl_eager as EG.
    pose proof (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) as SEPS. pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) as MM.
    assert (DISJ := fun m' Hm' Hnf' Hne => maps_match_disjoint E (a_maps cs) _ m m' MM SEPS Hm Hm' Hnf Hnf' Hne).
    assert (DISJ' : forall m', In m' (a_maps cs) -> is_fog m' = false -> m <> m' ->
              bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) <= lo
              \/ hi <= bv_unsigned (edenot E (am_base m'))).
    { intros m' Hm' Hnf' Hne. pose proof (DISJ m' Hm' Hnf' Hne) as D. unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. unfold lo, hi. lia. }
    assert (KNF : forall m', am_kind m' = KNONE \/ am_kind m' = KNONELAZY \/ am_kind m' = KRWLAZY -> is_fog m' = false).
    { intros m' Hk. unfold is_fog. destruct Hk as [-> |[-> | ->]]; reflexivity. }
    (* [comment removed for export] *)
    assert (NONE : forall m', In m' (a_maps cs) -> m <> m' -> (am_kind m' = KNONE \/ am_kind m' = KNONELAZY) ->
              In (amap_den E m') (vm_noaccess (m_vmmaps model'))).
    { intros m' Hm' Hne Hk. rewrite (sp_noacc _ _ _ _ _ SPo). apply in_app_iff. right.
      assert (Hnf' : is_fog m' = false) by (apply KNF; tauto).
      pose proof (proj1 (Forall_forall _ _) (co_none _ _ _ _ _ _ _ _ _ _ _ HC) m' Hm' Hk) as X.
      pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) (amap_den E m')
                    (maps_match_In E _ _ m' MM Hm' Hnf')) as (Bm1 & _).
      unfold amap_den in *. apply maps_subtract_keeps; [rewrite Un; lia | exact Bm1 | exact X |].
      cbn [fst snd]. rewrite Un. pose proof (DISJ' m' Hm' Hnf' Hne). unfold lo, hi in *. lia. }
    (* [comment removed for export] *)
    assert (KINDS : forall m', In m' (a_maps cs) -> am_kind m' = KRWLAZY ->
              forall x : word, bv_unsigned (edenot E (am_base m')) <= bv_unsigned x < bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) ->
                in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model')) = false
                /\ page_in_ranges (page_base x) (m_vm_lazy model') = true).
    { intros m' Hm' Hk x Hx.
      destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) m' Hm' Hk x Hx) as [K1 K2].
      destruct (Z_lt_le_dec (bv_unsigned x) lo) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hlt2|Hge2]].
      - rewrite sl_noacc_out, sl_lazy_out by lia. auto.
      - (* [comment removed for export] *)
        assert (Hmm : m = m').
        { destruct (amap_eqb m m') eqn:He; [apply APSK.amap_eqb_eq in He; exact He|]. exfalso.
          assert (Hne : m <> m') by (intros ->; rewrite amap_eqb_refl in He; discriminate).
          pose proof (DISJ' m' Hm' ltac:(apply KNF; tauto) Hne). lia. }
        subst m'. rewrite sl_noacc_in, sl_lazy_in by lia.
        destruct s0; rewrite <- Es; cbn [sl_nn]; auto; exfalso; refine (HnF _ Hk); rewrite <- Es; discriminate.
      - rewrite sl_noacc_out, sl_lazy_out by lia. auto. }
    match goal with |- CSOK _ ?c _ _ _ => set (cs1 := c) end.
    assert (HIDOUT : forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x -> HID E cs1 model' x = HID E cs model x).
    { intros x Hx. unfold hid. rewrite (sl_vis_out cs1 x eq_refl Hx). reflexivity. }
    assert (HALLOW : ALLOW E cs1 = ALLOW E cs) by reflexivity.
    destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xhna Xhlz Xtidv Xmres Xvdso Xrdr].
    constructor; rewrite ?HALLOW; unfold cs1; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn s_regs s_log s_know s_next mk_ss]; fold cs1.
    - exact Hregs.
    - reflexivity.
    - unfold Mr. rewrite (hid_ext A argH E cs _ model') by reflexivity. exact Hknow.
    - rewrite (sp_halted _ _ _ _ _ SPo). exact Xhalt.
    - unfold fds_ok in *. rewrite (sp_fds _ _ _ _ _ SPo), (sp_fs _ _ _ _ _ SPo). exact Xfds.
    - rewrite (sp_fs _ _ _ _ _ SPo). exact Xfs.
    - rewrite (sp_tid _ _ _ _ _ SPo). exact Xtid.
    - rewrite (sp_res _ _ _ _ _ SPo). exact Xres.
    - rewrite (sp_limit _ _ _ _ _ SPo). exact Xlimit.
    - rewrite (sp_maps _ _ _ _ _ SPo).
      assert (RK : maps_match E (rekind (a_maps cs) m) (vm_maps (m_vmmaps model))).
      { unfold rekind. apply maps_match_rekind; [|exact Xmaps]. intros m0. destruct (amap_eqb m0 m) eqn:He; [|auto].
        apply APSK.amap_eqb_eq in He. subst m0. cbn [am_base am_len]. split; [reflexivity|]. split; [reflexivity|]. rewrite Hnf. reflexivity. }
      destruct s0; rewrite <- Es; first [exact RK | exact Xmaps].
    - (* [comment removed for export] *)
      rewrite (sp_maps _ _ _ _ _ SPo), (sp_res _ _ _ _ _ SPo).
      assert (RKH : Forall (hole_ok E (a_ylo cs) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) (rekind (a_maps cs) m)).
      { unfold rekind. apply Forall_forall. intros m0 HinR Hh. apply in_map_iff in HinR as (m1 & <- & HinR1).
        destruct (amap_eqb m1 m) eqn:He.
        - exfalso. unfold is_hole in Hh. cbn [am_kind] in Hh. discriminate.
        - exact (proj1 (Forall_forall _ _) Xholes m1 HinR1 Hh). }
      destruct s0; rewrite <- Es; first [exact RKH | exact Xholes].
    - rewrite (sp_maps _ _ _ _ _ SPo). exact Xseps.
    - exact Hwf'.
    - rewrite (sp_maps _ _ _ _ _ SPo). exact Xbounds.
    - (* [comment removed for export] *) rewrite (sp_lazy _ _ _ _ _ SPo).
      assert (SUB : Forall (fun iv : word * word => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))
                                               /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= utop E)   (* [comment removed for export] *)
                      (maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))).
      { apply Forall_forall. intros q Hq. destruct (maps_subtract_pieces _ _ _ q W3 Hq) as (r & Hr & R1 & R2 & _).
        pose proof (proj1 (Forall_forall _ _) Xlazyb r Hr) as [Y1 Y2]. lia. }
      destruct s0; rewrite <- Es; try exact SUB; try exact Xlazyb. apply Forall_cons; [cbn [fst snd]; unfold lo, hi in *; lia | exact SUB].
    - (* [comment removed for export] *) intros z Hz. rewrite (sp_maps _ _ _ _ _ SPo). rewrite (sp_noacc _ _ _ _ _ SPo), in_ivs_app in Hz.
      apply orb_prop in Hz as [Hz|Hz].
      + destruct (sl_nn s); [|discriminate]. rewrite in_ivs_cons in Hz. cbn [fst snd in_ivs existsb] in Hz. rewrite orb_false_r in Hz.
        apply andb_prop in Hz as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
        eapply in_ivs_maps_match; [exact Xmaps | exact Hm | exact Hnf |]. unfold lo, hi in *. lia.
      + apply Xnasub. rewrite in_ivs_covered in Hz |- *. rewrite covered_maps_subtract in Hz by (try exact W2; rewrite Un; lia).
        apply andb_prop in Hz as [Hz _]. exact Hz.
    - (* [comment removed for export] *) apply Forall_forall. intros m' Hm' Hk'. destruct s0; rewrite <- Es in Hm'.
      2: { apply NONE; [exact Hm' | | exact Hk']. intros <-. rewrite (HF (eq_sym Es)) in Hk'. destruct Hk'; discriminate. }
      all: destruct (in_rekind _ _ _ Hm') as (m0 & Hm0 & [[-> ->]|[Hne ->]]); [cbn in Hk'; destruct Hk'; discriminate|];
           apply NONE; [exact Hm0 | congruence | exact Hk'].
    - (* [comment removed for export] *) apply Forall_forall. intros m' Hm' Hk'. destruct s0; rewrite <- Es in Hm'.
      2: { apply KINDS; assumption. }
      all: destruct (in_rekind _ _ _ Hm') as (m0 & Hm0 & [[-> ->]|[Hne ->]]); [cbn in Hk'; discriminate|];
           apply KINDS; assumption.
    - rewrite (sp_res _ _ _ _ _ SPo), (sp_maps _ _ _ _ _ SPo). exact Xtotsz.
    - (* [comment removed for export] *) rewrite (sp_isp _ _ _ _ _ SPo). exact Xisp.
    - rewrite (sp_brk _ _ _ _ _ SPo). exact Xbrk.
    - rewrite (sp_brk _ _ _ _ _ SPo), (sp_sbrk _ _ _ _ _ SPo). exact Xsbrk.
    - (* [comment removed for export] *) destruct (sl_charge s); lia.
    - exact Xabytes.
    - (* [comment removed for export] *) destruct Xminv as [N1 N2 N3 N4 N5].
      assert (MAT : forall q, In q (m_vm_materialized model') -> In q (m_vm_materialized model)
                      /\ (s <> SlM -> bv_unsigned q < lo \/ hi <= bv_unsigned q)).
      { intros q Hq. pose proof (sp_mat _ _ _ _ _ SPo) as SMAT. destruct s0; rewrite <- Es in SMAT; rewrite SMAT in Hq; try (split; [exact Hq | congruence]).
        all: apply filter_In in Hq as [Hq Ho]; split; [exact Hq|]; intros _;
             unfold page_outside_range in Ho; apply negb_true_iff in Ho; apply andb_false_iff in Ho as [Ho|Ho];
             [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; unfold lo, hi; rewrite <- ?Un; lia. }
      constructor; rewrite ?(sp_limit _ _ _ _ _ SPo).
      + pose proof (sp_mat _ _ _ _ _ SPo) as SMAT. destruct s0; rewrite <- Es in SMAT; rewrite SMAT; try apply NoDup_filter; exact N1.
      + intros q Hq. apply N2. apply MAT. exact Hq.
      + intros q Hq. apply N3. apply MAT. exact Hq.
      + intros q Hq. destruct (MAT q Hq) as [Hq0 Hout]. pose proof (N4 q Hq0) as L0.
        pose proof (sl_lazy_out q) as LO. pose proof (sp_lazy _ _ _ _ _ SPo) as SL.
        destruct s0; rewrite <- Es in SL, Hout; [| | | rewrite SL; exact L0].
        all: specialize (Hout ltac:(discriminate)); rewrite <- (page_base_aligned q (N2 q Hq0)); rewrite LO by exact Hout;
             rewrite page_base_aligned by exact (N2 q Hq0); exact L0.
      + destruct (sl_charge s); [specialize (Hbudget eq_refl)|]; rewrite Xlimit in *; lia.
    - (* [comment removed for export] *) intros x Hh Hmx Hna Hlz Hgh.
      destruct (Z_lt_le_dec (bv_unsigned x) lo) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hlt2|Hge2]].
      + rewrite (proj1 SM x) by (unfold lo in *; lia). rewrite HIDOUT in Hh by lia. rewrite (sp_maps _ _ _ _ _ SPo) in Hmx.
        rewrite sl_noacc_out in Hna by lia. rewrite sl_lazy_out in Hlz by lia. exact (Xzero x Hh Hmx Hna Hlz Hgh).
      + rewrite sl_noacc_in in Hna by lia. rewrite (proj2 SM x) by (unfold lo, hi in *; rewrite Un; lia). rewrite Hna. reflexivity.
      + rewrite (proj1 SM x) by (unfold hi in *; rewrite Un; lia). rewrite HIDOUT in Hh by lia. rewrite (sp_maps _ _ _ _ _ SPo) in Hmx.
        rewrite sl_noacc_out in Hna by lia. rewrite sl_lazy_out in Hlz by lia. exact (Xzero x Hh Hmx Hna Hlz Hgh).
    - (* [comment removed for export] *) eapply SINV_frame; [|exact Xsinv]. intros x Hx. apply (proj1 SM). pose proof (argH_high _ _ Hx). pose proof (utop_bounds E). unfold hi in *. rewrite Un. lia.
    - (* [comment removed for export] *) rewrite (sp_noacc _ _ _ _ _ SPo), Xhna. unfold sl_hna, RNA.
      destruct s0; rewrite <- Es; cbn [sl_nn app hreplay]; unfold APSK.uE; rewrite Hae, HneX; reflexivity.
    - (* [comment removed for export] *) rewrite (sp_lazy _ _ _ _ _ SPo), Xhlz. unfold sl_hlz, RLZ.
      destruct s0; rewrite <- Es; cbn [hreplay]; unfold APSK.uE; rewrite ?Hae, ?HneX; reflexivity.
    - (* [comment removed for export] *) intros Ht. rewrite (sp_tid _ _ _ _ _ SPo). exact (Xtidv Ht).
    - (* [comment removed for export] *)
      rewrite (sp_maps _ _ _ _ _ SPo), (sp_res _ _ _ _ _ SPo). exact Xmres.
    - (* [comment removed for export] *)
      rewrite (sp_res _ _ _ _ _ SPo), (sp_kernel _ _ _ _ _ SPo),
        (vdso_top_eq _ _ (sp_mbase _ _ _ _ _ SPo) (sp_isp _ _ _ _ _ SPo)).
      exact Xvdso.
    - (* [comment removed for export] *)
      rewrite (sp_rdr _ _ _ _ _ SPo). exact Xrdr.
  Qed.

End Slice.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma kn_unfill_clip_ok : forall E M M' k b off ne,
  know_ok SEGS E M k ->
  (estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)) ->   (* [comment removed for export] *)
  (forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x -> M' x = M x) ->
  know_ok SEGS E M' (kimg_clip A (kn_unfill k b off ne)).
Proof.
  intros E M M' k b off ne HK Hhull Hout.
  pose proof (kimg_clip_in_hull' (kn_unfill k b off ne)) as Hh.
  unfold know_ok. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) Hh K Hin) as HKh.
  apply kimg_clip_incl in Hin. unfold kn_unfill in Hin. apply filter_In in Hin as [Hin Hkeep].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  eapply kentry_keep_sem'; [exact HKK | | exact Hout].
  apply orb_prop in Hkeep as [Himg|Hap].
  - destruct K; try discriminate. unfold kfoot_apart, kfoot. cbn in HKh. lia.
  - rewrite APSK.kentry_apart_bp_eq in Hap. eapply kentry_apart_b_sem'; [exact HK | exact Hap].
Qed.

(* [comment removed for export] *)
Lemma kn_rezero_ok_gen : forall E M M' k b off ne,
  know_ok SEGS E M k ->
  (estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)) ->   (* [comment removed for export] *)
  (forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x -> M' x = M x) ->
  (forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E ne -> M x <> None -> M' x = Some (Z_to_bv 8 0)) ->
  forall K, In K (kn_rezero k b off ne) ->
    match K with KImg lo hi => img_lo A <= lo /\ hi <= img_hi A | _ => True end ->
    kentry_ok SEGS E M' K.
Proof.
  intros E M M' k b off ne HK Hhull Hout Hin0 K Hin HKh.
  assert (DEF : forall x : word, M x <> None -> M' x <> None).
  { intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off))); [rewrite Hout by lia; exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off) + elenZ E ne)); [rewrite (Hin0 x ltac:(lia) Hx); discriminate | rewrite Hout by lia; exact Hx]. }
  assert (ZERO : forall x : word, M x = Some (Z_to_bv 8 0) -> M' x = Some (Z_to_bv 8 0)).
  { intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off))); [rewrite Hout by lia; exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off) + elenZ E ne)); [apply Hin0; [lia | rewrite Hx; discriminate] | rewrite Hout by lia; exact Hx]. }
  unfold kn_rezero in Hin. apply filter_In in Hin as [Hin Hkeep].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [[kb kk] w v|[kb kk] l|[kb kk] l bk|ilo ihi|e mm|e rlo rhi|[kb kk] l|a1 n1 a2 n2|[kb kk] l fc|[kb kk] l];
    try (rewrite APSK.kentry_apart_bp_eq in Hkeep; eapply kentry_keep_sem'; [exact HKK | eapply kentry_apart_b_sem'; [exact HK | exact Hkeep] | exact Hout]).
  - (* [comment removed for export] *) cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. apply ZERO. apply Hz. exact Hi.
  - (* [comment removed for export] *) eapply kentry_keep_sem'; [exact HKK | | exact Hout]. unfold kfoot_apart, kfoot. lia.
  - exact HKK.
  - exact HKK.
  - (* [comment removed for export] *) cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hs]. split; [exact Hfl|]. intros d mm Hd Hdm. eapply store_ok_mono; [exact DEF | apply Hs; assumption].
  - exact HKK.
  - (* [comment removed for export] *) cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. apply DEF. apply Hz. exact Hi.
Qed.

Lemma kn_rezero_clip_ok : forall E M M' k b off ne,
  know_ok SEGS E M k ->
  (estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)) ->   (* [comment removed for export] *)
  (forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x -> M' x = M x) ->
  (forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E ne -> M x <> None -> M' x = Some (Z_to_bv 8 0)) ->
  know_ok SEGS E M' (kimg_clip A (kn_rezero k b off ne)).
Proof.
  intros E M M' k b off ne HK Hhull Hout Hin0. pose proof (kimg_clip_in_hull' (kn_rezero k b off ne)) as Hh.
  unfold know_ok. apply Forall_forall. intros K Hin. pose proof (proj1 (Forall_forall _ _) Hh K Hin) as HKh.
  apply kimg_clip_incl in Hin. apply (kn_rezero_ok_gen E M M' k b off ne HK Hhull Hout Hin0 K Hin). destruct K; try exact I. exact HKh.
Qed.

Lemma kn_rezero_hull_ok : forall E M M' k b off ne,
  know_ok SEGS E M k -> kimg_in_hull A k ->
  (estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)) ->   (* [comment removed for export] *)
  (forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x -> M' x = M x) ->
  (forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E ne -> M x <> None -> M' x = Some (Z_to_bv 8 0)) ->
  know_ok SEGS E M' (kn_rezero k b off ne).
Proof.
  intros E M M' k b off ne HK Hh Hhull Hout Hin0.
  unfold know_ok. apply Forall_forall. intros K Hin.
  assert (Hin' : In K k) by (unfold kn_rezero in Hin; apply filter_In in Hin as [Hin _]; exact Hin).
  pose proof (proj1 (Forall_forall _ _) Hh K Hin') as HKh.
  apply (kn_rezero_ok_gen E M M' k b off ne HK Hhull Hout Hin0 K Hin). destruct K; try exact I. exact HKh.
Qed.

Lemma kimg_in_hull_cons2 : forall K1 K2 k,
  match K1 with KImg _ _ => False | _ => True end -> match K2 with KImg _ _ => False | _ => True end ->
  kimg_in_hull A k -> kimg_in_hull A (K1 :: K2 :: k).
Proof.
  intros K1 K2 k H1 H2 Hk. unfold kimg_in_hull in *. constructor; [destruct K1; tauto|]. constructor; [destruct K2; tauto | exact Hk].
Qed.

(* [comment removed for export] *)
Lemma vis_add_slice_ok : forall E cs1 cs2 (ea : expr) b off ne R FULL' model' (lo nZ : Z),
  CSOK E cs1 R FULL' model' ->
  vis_add A LIMIT cs1 ea ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) = Some cs2 ->
  kimg_in_hull A (kn cs1) ->
  uE E ea = lo -> estart E (SA b off) = lo -> elenZ E ne = nZ -> 0 <= lo -> 0 < nZ -> lo + nZ <= TOPC ->   (* [comment removed for export] *)
  (forall x : word, lo <= bv_unsigned x < lo + nZ ->
     in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model')) = true
     /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model')) = false
     /\ argH E x = false /\ FULL' x = Some (Z_to_bv 8 0)) ->
  CSOK E cs2 R FULL' model'.
Proof.
  intros E cs1 cs2 ea b off ne R FULL' model' lo nZ HC1 Hva Hkh Hea Hest Hne Hlo HnZ Hhi NEW.
  eapply vis_add_sound'; [exact Hva | exact HC1 |].
  destruct (vis_add_inv cs1 ea ne _ cs2 Hva) as (nhi & Hnhi & Ecs2).
  assert (BYTE : forall x : word, lo <= bv_unsigned x < lo + nZ -> MR E cs2 model' FULL' x = Some (Z_to_bv 8 0)).
  { intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3 & N4).
    unfold Mr, mrestrict, hid. rewrite N3. cbn [orb]. unfold vis. rewrite N1, N2. cbn [negb andb].
    assert (Hal : in_allow A E cs2 (bv_unsigned x) = true).
    { unfold in_allow, in_vis. rewrite Ecs2. cbn [a_vis existsb fst snd]. rewrite Hea. unfold uE. fold (elenZ E ne). rewrite Hne.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    rewrite Hal, !orb_true_r. cbn [negb]. exact N4. }
  assert (Hfl : flat E (SA b off) (elenZ E ne)) by (unfold flat; rewrite Hest, Hne; unfold TOPC in Hhi; lia).
  constructor; [|constructor].
  - cbn [kentry_ok]. split; [exact Hfl|]. rewrite Hest, Hne. intros d w' Hd Hdw. destruct w' as [|w'']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by (unfold TOPC in Hhi; lia); unfold TOPC in Hhi; lia|].
    intros x Hx. rewrite u64_lit in Hx by (unfold TOPC in Hhi; lia). unfold wview. rewrite (BYTE x) by lia. discriminate.
  - cbn [kentry_ok]. split; [exact Hfl|]. rewrite Hest, Hne. intros i Hi. apply BYTE. rewrite u64_lit by (unfold TOPC in Hhi; lia). lia.
  - pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
    eapply know_ok_unhide'; [apply H_off_segments_cs' | exact Hkh | | | exact HK1].
    + intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
    + intros y Hy. apply hid_hull'. exact Hy.
Qed.

(* [comment removed for export] *)
Lemma find_containing_sound : forall E M k ms kinds b off ne m,
  know_ok SEGS E M k -> find_containing k ms kinds b off ne = Some m ->
  In m ms /\ (In (am_kind m) kinds /\ is_fog m = false)
  /\ bv_unsigned (edenot E (am_base m)) <= estart E (SA b off)
  /\ estart E (SA b off) + elenZ E ne <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)).
Proof.
  intros E M k ms kinds b off ne m HK Hf. unfold find_containing in Hf. apply find_some in Hf as [Hin Hb].
  apply andb_prop in Hb as [Hk Hins]. apply andb_prop in Hk as [Hnf Hk]. apply negb_true_iff in Hnf.
  apply existsb_exists in Hk as (k0 & Hk0 & Hkk). apply APSK.mkind_eqb_eq in Hkk. subst k0.
  pose proof (xinside_sound SEGS E M k b off ne (am_base m) 0 (am_len m) HK Hins) as [I1 I2].
  unfold estart in I1, I2 |- *. cbn [a_base a_off] in *. unfold elenZ in *. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
Lemma slice_args : forall E cs R FULL model b off ne nlo nhi kinds m,
  CSOK E cs R FULL model ->
  fixed_args A cs TOPC = Some (b, off, ne, nlo, nhi) ->   (* [comment removed for export] *)
  find_containing (kn cs) (a_maps cs) kinds b off ne = Some m ->
  let addr := edenot E (reg cs 10) in
  let len := bv_unsigned (edenot E (reg cs 11)) in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  In m (a_maps cs) /\ (In (am_kind m) kinds /\ is_fog m = false)
  /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = addr /\ getr R (Z_to_bv 5 (Z.of_nat 11)) = Z_to_bv 64 len /\ 0 < len < 2 ^ 64
  /\ edenot E ne = n /\ bv_unsigned n = nZ /\ 0 < nZ /\ nZ <= nhi /\ nZ mod 4096 = 0
  /\ bv_unsigned addr mod 4096 = 0 /\ 0 < bv_unsigned addr /\ (bv_unsigned addr + nZ <= img_lo A \/ img_hi A <= bv_unsigned addr)   (* [comment removed for export] *)
  /\ estart E (SA b off) = bv_unsigned addr
  /\ bv_unsigned (edenot E (am_base m)) <= bv_unsigned addr
  /\ bv_unsigned addr + nZ <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m))
  /\ bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= utop E   (* [comment removed for export] *)
  /\ map_contains (vm_maps (m_vmmaps model)) addr n = true
  /\ region_free (vm_reserved (m_vmmaps model)) addr n = true
  /\ overlap_sum (vm_maps (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) <= nZ.
Proof.
  intros E cs R FULL model b off ne nlo nhi kinds m HC HFA Hf addr len nZ n.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (fixed_args_sound E cs R FULL model TOPC b off ne nlo nhi HC HFA) as (Hsp & HML & Hal & Hpos & Himg & Htop & R10 & _).
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & _).
  fold addr in Hal, Hpos, Himg, Htop, R10. fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal. fold n in Hne.
  destruct (find_containing_sound E _ (kn cs) (a_maps cs) kinds b off ne m HK Hf) as (Hm & [Hkind Hnf] & I1 & I2).
  pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) as HB.
  pose proof (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf) as HIN.
  pose proof (proj1 (Forall_forall _ _) HB (amap_den E m) HIN) as (B1 & B2 & B3 & B4 & B5). cbn [amap_den fst snd] in B1, B2, B3, B4, B5.
  pose proof (u64_range (edenot E (am_base m))) as Rb. pose proof (utop_le_TOPC _ _ _ _ _ HC) as UT.
  assert (Hest : bv_unsigned addr = estart E (SA b off)).
  { unfold addr. apply (APSK.u_of_split E (reg cs 10) b off Hsp). unfold elenZ in I2. pose proof (u64_range (edenot E ne)). unfold TOPC in UT. lia. }
  unfold elenZ in I2. rewrite Hne in I2.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
  assert (Un : bv_unsigned n = nZ).
  { unfold n. apply u64_lit. pose proof (u64_range (Z_to_bv 64 nZ)). fold n in H. unfold TOPC in *. lia. }
  rewrite Un in I2. rewrite Hne, Un in Himg.
  assert (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = true).
  { eapply map_contains_intro; [exact HIN | lia | rewrite Un; lia]. }
  split; [exact Hm|]. split; [split; [exact Hkind | exact Hnf]|].
  repeat (split; [first [assumption | lia | symmetry; assumption] |]).
  (* [comment removed for export] *)
  split; [apply (reserved_free_inside E cs R FULL model (amap_den E m) addr n HC HIN);
            unfold amap_den; cbn [fst snd]; rewrite ?Un, ?Hest; lia |].
  rewrite Un. pose proof (overlap_sum_contained (vm_maps (m_vmmaps model)) (edenot E (am_base m)) (edenot E (am_len m)) (bv_unsigned addr) (bv_unsigned addr + nZ)
    (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) HIN ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.



(* [comment removed for export] *)


End Nodes.
End AsanNodesMmLibK.
From Stdlib Require ZArith NArith List Lia Bool FunctionalExtensionality. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.
Module ArtBridge.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.Scfg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.KitNodesS.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BackingAlgebra. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Madvise.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.AsanNodesLibEK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.AsanNodesMmLibK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.AsanNodesMadvK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRuns.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_ArtBridge () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List:fold_rightC46Stdlib5Lists4List7existsbC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appc59OSSVerify5KrLib7Mh_01099KitNodesS?node_chk_ev_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg7node_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099KitNodesSEnode_chk_ev_gen_noaccC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00c59OSSVerify5KrLib7Mh_0109>AsanNodesLibEKAnode_chk_ev_noaccC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109>AsanNodesLibEK>node_chk_noaccC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109>AsanNodesLibEK9srz_casesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg5t_altC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg8srz_nodeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg8wr_indexC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlgFnode_ok_of_pnode_sysnoC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5Nodes6open_IC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg@node_ok_of_pnodeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib7Mh_0109>AsanNodesLibEK8Some_injC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes5tid_IC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:concat_mapC46Stdlib5Lists4List7map_mapc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKFA_bytes_flat_map_splitC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKAin_flat_map_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK>filter_map_extC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9fold_leftc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9srz_node1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK8some_injC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State>vm_backed_mapsC4ELinuxProcessSemantics?LinuxProcessSem5StateAmaps_subtract_allC4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesK47Corelib4Init5Logic2eq01C59OSSVerify5KrLib7Mh_00368AsanAcct:eager_usedC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedK47Corelib4Init9Datatypes4list01C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC59OSSVerify5KrLib7Mh_00368AsanAcctEvm_backing_used_splitC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeI46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingc59OSSVerify5KrLib7Mh_01099ArtBridge>eager_used_extC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge9vbu_nomatC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BA<model_ivs_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsc69OSSVerify5KrLib7Mh_01099ArtBridge2BA6ivs_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC59OSSVerify5KrLib7Mh_00238AsanCeil:init_sp_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsc69OSSVerify5KrLib7Mh_01099ArtBridge2BA;ivs_wf_consC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BA8live_msaC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BA9sum_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natc69OSSVerify5KrLib7Mh_01099ArtBridge2BA=zcount_le_lenC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BA6zcountC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes3sndc69OSSVerify5KrLib7Mh_01099ArtBridge2BA8iv_countC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BAJmaps_subtract_all_app_cutsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01c69OSSVerify5KrLib7Mh_01099ArtBridge2BA>live_bytes_appC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BAEmaps_subtract_all_appC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BAHmaps_subtract_all_cons_lC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BAEm_vm_lazy_with_vmmapsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BADm_vmmaps_with_vmmapsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BA7coveredC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbK46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega=RingMicromega3Op203c69OSSVerify5KrLib7Mh_01099ArtBridge2BA:ivs_wf_nilC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangec69OSSVerify5KrLib7Mh_01099ArtBridge2BA;overlap_sumC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BAHbacking_forget_commit_leC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:eq_le_inclC56Stdlib6ZArith6BinInt1Z8le_transc59OSSVerify5KrLib7Mh_01099ArtBridgeAeager_used_as_vbuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyc69OSSVerify5KrLib7Mh_01099ArtBridge2BAHbacking_recommit_lazy_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge=munmap_vmmapsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbc69OSSVerify5KrLib7Mh_01099ArtBridge2BA=ivs_wf_filterC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:map_removec69OSSVerify5KrLib7Mh_01099ArtBridge2BA@maps_subtract_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spc69OSSVerify5KrLib7Mh_01099ArtBridge2BAHmodel_ivs_wf_with_vmmapsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BALmodel_ivs_wf_vm_forget_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim<munmap_modelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge?munmap_model_eqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2Inc69OSSVerify5KrLib7Mh_01099ArtBridge2BA1BC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BA1SC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge?munmap_model_wfC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra9sum_countC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BAAmaps_subtract_semC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbc69OSSVerify5KrLib7Mh_01099ArtBridge2BA6in_rngC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra1BC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra1SC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z6leb_gtK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z6ltb_geK47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool;andb_true_rc69OSSVerify5KrLib7Mh_01099ArtBridge2BA;covered_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKCsum_count_filter_leC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BAIm_vm_lazy_vm_forget_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BAHm_vmmaps_vm_forget_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK>eager_used_semC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra7coveredC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes6option00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C59OSSVerify5KrLib7Mh_00387StoreOk>mem_grows_reflC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv3Sem3eff02C47Corelib4Init5Logic3notK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C47Corelib4Init5Logic9False_indK4ELinuxProcessSemantics5Riscv3Sem3eff03K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics5Riscv3Sem3eff04K4ELinuxProcessSemantics5Riscv3Sem3eff05K4ELinuxProcessSemantics5Riscv3Sem3eff06K4ELinuxProcessSemantics5Riscv3Sem3eff07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;width_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesK4ELinuxProcessSemantics5Riscv3Sem3eff08C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib7Mh_00387StoreOkBwrite_to_mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk?mem_grows_transC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7eff_indC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesI4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem3eff00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI47Corelib4Init5Logic5False00I47Corelib7Numbers7BinNums1N00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failurec59OSSVerify5KrLib7Mh_01099ArtBridgeIinterp_eff_accesses_growsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@fetch_byte_trapsC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_half_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics5Riscv3Sem4execI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv5Instr5instr00I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingc59OSSVerify5KrLib7Mh_01099ArtBridge>step_mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim:msteps_indC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge;art_ev_liveC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=fold_left_appc59OSSVerify5KrLib7Mh_01099ArtBridge8art_liveC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00357ArtRuns3aev00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge8art_costC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge<art_cost_sumC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib7Mh_00357ArtRuns8art_shloC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00357ArtRuns8art_shhiC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<flat_map_appc59OSSVerify5KrLib7Mh_01099ArtBridge;art_windowsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State4m_vmC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01c59OSSVerify5KrLib7Mh_01099ArtBridge9bmodel_rtC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01i59OSSVerify5KrLib7Mh_01099ArtBridge4BInv00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge4bhidC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC59OSSVerify5KrLib7Mh_00368AsanAcct=page_allowedbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentc59OSSVerify5KrLib7Mh_01099ArtBridge:bi_lazy_inC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00368AsanAcct>lazy_cover_mkHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct:lazy_coverC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge<in_shadow_rwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctKsame_but_materialized_frameC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State7m_pipesC4ELinuxProcessSemantics?LinuxProcessSem5State7m_stdinC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC59OSSVerify5KrLib7Mh_00368AsanAcct4A_wfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge6grantsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitc59OSSVerify5KrLib7Mh_01099ArtBridge7live_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge9window_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct7A_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge8live_sumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct3mkHC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_01099ArtBridge4BInv01C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7m_clockC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State=m_rlimit_coreI4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C59OSSVerify5KrLib7Mh_00368AsanAcct8restrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge5bstepC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge9binv_hoffC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge?bhid_lazy_coverC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge6bi_awfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge7bi_minvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge7bi_haltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct6hcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct:unrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctIrestrict_unrestrict_cleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct;munrestrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge8bi_shdefC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge@msteps_mem_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge8binv_sbmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>unrestrict_memC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge=bmodel_rt_sbmC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC59OSSVerify5KrLib7Mh_0036=AsanAcctShapeGsrz_msteps_restricted_TC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BA6fg_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim5zfillC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00357ArtRuns9art_zfillC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00C46Stdlib6ZArith:ZArith_dec8Z_le_decC46Stdlib6ZArith:ZArith_dec8Z_lt_decC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega7EnvRing5PExpr07c59OSSVerify5KrLib7Mh_01099ArtBridge4u64zC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK8zfill_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00357ArtRuns<art_zfill_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim9zfill_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00357ArtRuns=art_zfill_outC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega3Op204C59OSSVerify5KrLib7Mh_00387MmapSim6unfillC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00357ArtRuns9art_unmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00357ArtRuns:art_revealC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKGpage_of_byte_in_alignedC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC47Corelib4Init9Datatypes?andb_true_introK47Corelib4Init5Logic2ex01c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKCpage_in_ranges_trueC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKDmaps_subtract_piecesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKHpage_of_byte_out_alignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKDpage_in_ranges_falseC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKKpage_in_ranges_subtract_outC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKBpage_in_ranges_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge<forget_modelC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC46Stdlib5Lists4List<NoDup_filterC46Stdlib5Lists4List6filterC46Stdlib5Lists4List9filter_InC46Stdlib4Bool4Bool<orb_true_iffC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z9div_exactK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK59OSSVerify5KrLib7Mh_00368AsanAcct4MInv01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_app_orC4ELinuxProcessSemantics?LinuxProcessSem5State;iv_subtractc69OSSVerify5KrLib7Mh_01099ArtBridge2BA5iv_wfC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specK46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib7Mh_01099ArtBridge5bi_wfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge?lazy_forget_outC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge9bi_budgetC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge8bi_limitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge;minv_forgetC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BA:ivs_wf_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeil?init_sp_ok_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge7bi_resvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge6bi_topC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge8bi_noaccC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge<bi_noacc_posC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridgeAmaps_subtract_posC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool8orb_propc59OSSVerify5KrLib7Mh_01099ArtBridgeJpage_in_ranges_subtract_leC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>negb_false_iffc59OSSVerify5KrLib7Mh_01099ArtBridge7bi_zeroC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge:bi_windowsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge:bi_livesumC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK?page_base_factsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizec59OSSVerify5KrLib7Mh_01099ArtBridge6LSH_LOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge6LSH_HIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge6HSH_LOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge6HSH_HIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge4SHHIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge4SHLOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge;bs_resv_posC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge@bs_shrw_off_resvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodesAregion_free_introC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib7Mh_00357ArtRuns<art_at_ecallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00357ArtRuns=art_mmap_argsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00357ArtRuns3aev03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge8art_EVOKC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge?shadow_rw_factsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge7bs_ceilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00388AllocSimGpage_round_up_Z_alignedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bC4ELinuxProcessSemantics?LinuxProcessSem5State=lazy_interiorc69OSSVerify5KrLib7Mh_01099ArtBridge2BAElazy_interior_alignedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01c59OSSVerify5KrLib7Mh_0109>AsanNodesLibEK@fixedin_ok_modelC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_modc59OSSVerify5KrLib7Mh_01099ArtBridge8bs_sh_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge@bs_shrw_off_segsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge7bi_mapsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge=art_live_snocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge7bi_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge@art_windows_snocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridgeAart_cost_sum_snocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge7bi_costC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridgeAeager_recommit_leC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib4Bool4Bool<andb_false_rc59OSSVerify5KrLib7Mh_01099ArtBridge?page_allowed_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge;binv_forgetC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC35stdpp7tactics<f_equal_helpc59OSSVerify5KrLib7Mh_01099ArtBridgeGregion_free_resv_shadowC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsc59OSSVerify5KrLib7Mh_01099ArtBridge=bs_shrw_entryC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKBmap_contains_introC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKEvm_backing_used_limitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BAVmmap_fixed_rw_budget_ok_recommit_introC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge:view_zfillC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109>AsanNodesLibEKEsrz_mmap_fixedin_lazyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKEmmap_noreserve_b_4032C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge3toWC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKDmmap_flags_core_4032C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge6mm1_eqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BAHiv_count_in_rng_disjointC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BA@overlap_sum_consC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BA?overlap_sum_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge6ww_decC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BABiv_count_in_rng_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridgeBoverlap_sum_apart0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge3KN0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge9bs_res_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge8res_wordC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge=bs_maps_nodupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge=bs_maps_apartC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge?overlap_sum_oneC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_map_iffc59OSSVerify5KrLib7Mh_01099ArtBridge9live_wordC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6in_mapc59OSSVerify5KrLib7Mh_01099ArtBridge3ivZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BA?overlap_sum_appC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consK59OSSVerify5KrLib7Mh_00357ArtRuns3aev01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge>overlap_in_resC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge?eager_commit_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKJpage_in_ranges_subtract_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge?bs_res_off_resvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKBvm_backing_used_leC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01099ArtBridge2BATmmap_fixed_rw_budget_ok_commit_introC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKCmmap_noreserve_b_32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKBmmap_flags_core_32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge?filter_all_trueC1?~~~~~~~~~~~~~~~K46Stdlib5Lists4List5NoDup01K46Stdlib5Lists4List5NoDup02K59OSSVerify5KrLib7Mh_00357ArtRuns3aev04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge@maps0_apart_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge;bs_maps_posC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:bv_eqb_neqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:filter_appC59OSSVerify5KrLib7Mh_00357ArtRuns?art_munmap_argsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge?map_remove_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge>live_ok_filterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge?live_sum_filterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge>eager_unmap_leC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK=map_has_introC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge;view_unfillC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109>AsanNodesLibEK?srz_munmap_lazyC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z<eq_decidableC59OSSVerify5KrLib7Mh_0037=AsanPlacement8gw_sizesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appc59OSSVerify5KrLib7Mh_01099ArtBridge9bs_budgetC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge6bs_gapC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc59OSSVerify5KrLib7Mh_01099ArtBridge?gw_sizes_grantsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge<gw_sizes_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_mapC56Stdlib6ZArith6BinInt1ZBmul_le_mono_nonnegC59OSSVerify5KrLib7Mh_0037=AsanPlacementBfree_gap_of_totalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeilJalloc_ceiling_le_alloc_topC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqc59OSSVerify5KrLib7Mh_01099KitNodesS?grant_ok_na_pinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeilChint_placement_ok_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeil=alloc_ceilingC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC59OSSVerify5KrLib7Mh_00238AsanCeil>bottomup_floorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeilBbottomup_floor_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeilAalloc_ceiling_valC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=andb_true_iffC59OSSVerify5KrLib>AsanPlanSoundK4APSK6in_ivsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK>in_ivs_coveredC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK?region_free_semC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC59OSSVerify5KrLib7Mh_00387MmapSim:mmap_modelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge;grant_partsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes=Z_to_bv_u_eq'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes>region_free_InC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK?region_free_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge@apart_of_coveredC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge>aligned_pos_geC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge<window_factsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<in_ivs_true'C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool;orb_false_rC46Stdlib5Lists4List;existsb_appK59OSSVerify5KrLib7Mh_00357ArtRuns3aev02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge>eager_grant_leC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_appK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<A_bytes_app'C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=orb_false_iffC56Stdlib6ZArith6BinInt1Z7div_posC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismc59OSSVerify5KrLib7Mh_01099ArtBridge;bs_shrw_accC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge;view_revealC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge6art_GRC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00c59OSSVerify5KrLib7Mh_01099ArtBridge<grant_existsC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAwith_mmap_backingc59OSSVerify5KrLib7Mh_01099ArtBridge9binv_nullC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<srz_mmap_rw1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKCmmap_noreserve_b_22C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKBmmap_flags_core_22C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseEmadvise_dontneed_nextc59OSSVerify5KrLib7Mh_01099ArtBridge;sbm_madviseC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00357ArtRuns3aev05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00357ArtRuns@art_madvise_argsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge<minv_madviseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridgeAbinv_snoc_madviseC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseCmadvise_dontneed_okc59OSSVerify5KrLib7Mh_0109>AsanNodesMadvK@srz_madvise_lazyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge<in_ev_rangesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge5bhistC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocc59OSSVerify5KrLib7Mh_01099ArtBridge<art_ev_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge9art_ev_nrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_tranI59OSSVerify5KrLib7Mh_00357ArtRuns5aruns00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge?bmodel_rt_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge;bhist_step0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge=bridge_mstepsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge@restrict_eq_mkstC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge=restrict_mkstC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge?bhist_step_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge<bridge_fixedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge?bhist_step_nullC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge;bridge_nullC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge?bridge_fixed_nrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge=bridge_munmapC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge>bridge_madviseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00357ArtRuns9aruns_indC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge:bhist_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridgeAaruns_srealizes_hC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge4BINVC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge8binv_extC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module BA := BackingAlgebra.

Lemma eager_used_ext : forall m1 m2,
  m_vmmaps m1 = m_vmmaps m2 -> m_vm_lazy m1 = m_vm_lazy m2 -> eager_used m1 = eager_used m2.
Proof. intros m1 m2 H1 H2. unfold eager_used. rewrite H1, H2. reflexivity. Qed.

Lemma vbu_nomat : forall m, m_vm_materialized m = [] -> vm_backing_used m = eager_used m.
Proof. intros m H. rewrite vm_backing_used_split, H. cbn [length Z.of_nat]. lia. Qed.

Lemma eager_used_as_vbu : forall m,
  eager_used m = vm_backing_used (with_vm_backing (m_vm_lazy m) [] m).
Proof. intros m. rewrite vbu_nomat by reflexivity. apply eager_used_ext; reflexivity. Qed.

Lemma eager_grant_le : forall m (a n : word) h',
  BA.model_ivs_wf m ->
  bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  vm_maps h' = (a, n) :: vm_maps (m_vmmaps m) ->
  vm_noaccess h' = vm_noaccess (m_vmmaps m) ->
  eager_used (with_vmmaps h' m) <= eager_used m + bv_unsigned n.
Proof.
  intros m a n h' (Wm & Wn & Wl) Hend Hmaps Hna.
  unfold eager_used, vm_backed_maps. rewrite BA.m_vmmaps_with_vmmaps, BA.m_vm_lazy_with_vmmaps.
  rewrite Hmaps, Hna.
  rewrite BA.maps_subtract_all_cons_l, BA.maps_subtract_all_app, BA.live_bytes_app.
  match goal with |- ?x + ?y <= ?y' + ?nn => enough (x <= nn) by lia end.
  rewrite <- BA.maps_subtract_all_app_cuts.
  assert (W1 : BA.ivs_wf [(a, n)]) by (apply BA.ivs_wf_cons; [exact Hend|apply BA.ivs_wf_nil]).
  destruct (BA.live_msa (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) [(a, n)] W1) as [-> _].
  cbn [BA.sum_count]. unfold BA.iv_count, BA.B, BA.S. cbn [fst snd].
  pose proof (BA.zcount_le_len (fun x => negb (BA.covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (bv_unsigned a) (Z.to_nat (bv_unsigned n))) as Hz.
  pose proof (bv_unsigned_in_range 64 n). rewrite Z2Nat.id in Hz by lia. lia.
Qed.

Lemma eager_commit_le : forall m h' lo hi,
  BA.model_ivs_wf m -> lo <= hi ->
  vm_maps h' = vm_maps (m_vmmaps m) ->
  vm_noaccess h' = maps_subtract (vm_noaccess (m_vmmaps m)) lo hi ->
  eager_used (vm_forget_range lo hi (with_vmmaps h' m)) <= eager_used m + BA.overlap_sum (vm_maps (m_vmmaps m)) lo hi.
Proof.
  intros m h' lo hi Hwf Hlh Hmaps Hna.
  rewrite (eager_used_as_vbu m).
  pose proof (BA.backing_forget_commit_le (with_vm_backing (m_vm_lazy m) [] m) h' lo hi Hwf Hlh Hmaps Hna) as HB.
  eapply Z.le_trans; [|exact HB].
  rewrite vbu_nomat by reflexivity. apply Z.eq_le_incl. apply eager_used_ext; reflexivity.
Qed.

Lemma eager_recommit_le : forall m h' (a n : word),
  BA.model_ivs_wf m ->
  bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 ->
  0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  vm_maps h' = vm_maps (m_vmmaps m) ->
  vm_noaccess h' = maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n) ->
  eager_used (vm_add_lazy a n (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (with_vmmaps h' m)))
  <= eager_used m.
Proof.
  intros m h' a n Hwf Hal Hnl Hpos Hend Hmaps Hna.
  rewrite (eager_used_as_vbu m).
  pose proof (BA.backing_recommit_lazy_le (with_vm_backing (m_vm_lazy m) [] m) h' a n Hwf Hal Hnl Hpos Hend Hmaps Hna) as HB.
  eapply Z.le_trans; [|exact HB].
  rewrite vbu_nomat by reflexivity. apply Z.eq_le_incl. apply eager_used_ext; reflexivity.
Qed.

(* [comment removed for export] *)
Definition munmap_vmmaps (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h)
    (maps_subtract (vm_maps h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Lemma munmap_model_eq : forall a n m,
  munmap_model a n m = vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (with_vmmaps (munmap_vmmaps a n (m_vmmaps m)) m).
Proof. reflexivity. Qed.

Lemma munmap_model_wf : forall a n m, BA.model_ivs_wf m -> BA.model_ivs_wf (munmap_model a n m).
Proof.
  intros a n m Hwf. rewrite munmap_model_eq.
  pose proof (bv_unsigned_in_range 64 n) as Hn.
  apply BA.model_ivs_wf_vm_forget_range; [lia|].
  destruct Hwf as (Wm & Wn & Wl & Wsp).
  apply BA.model_ivs_wf_with_vmmaps; [repeat split; assumption | | | reflexivity].
  - cbn [munmap_vmmaps vm_maps]. apply BA.maps_subtract_wf; [exact Wm | lia].
  - cbn [munmap_vmmaps vm_noaccess]. apply BA.maps_subtract_wf; [exact Wn | lia].
Qed.

Lemma eager_unmap_le : forall m (a n : word),
  BA.model_ivs_wf m ->
  (forall q, In q (vm_maps (m_vmmaps m)) -> bv_eqb (fst q) a = false ->
     BA.B q + BA.S q <= bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= BA.B q) ->
  eager_used (munmap_model a n m) <= eager_used m.
Proof.
  intros m a n Hwf Hap.
  pose proof (munmap_model_wf a n m Hwf) as Hwf'.
  rewrite (eager_used_sem _ Hwf'), (eager_used_sem _ Hwf).
  rewrite munmap_model_eq. BA.model_proj. cbn [munmap_vmmaps vm_maps vm_noaccess].
  pose proof (bv_unsigned_in_range 64 n) as Hn.
  destruct Hwf as (Wm & Wn & Wl & Wsp).
  set (lo := bv_unsigned a). set (hi := lo + bv_unsigned n).
  destruct (BA.maps_subtract_sem _ lo hi Wn ltac:(subst hi; lia)) as (_ & _ & Cn).
  destruct (BA.maps_subtract_sem _ lo hi Wl ltac:(subst hi; lia)) as (_ & _ & Cl).
  destruct (BA.maps_subtract_sem _ lo hi Wm ltac:(subst hi; lia)) as (_ & Sm & _).
  rewrite Sm. apply BA.sum_count_mono. intros x Hx.
  apply andb_prop in Hx as [Hx1 Hx2]. apply negb_true_iff in Hx2.
  rewrite BA.covered_app, Cn, Cl, Hx2 in Hx1. cbn [negb] in Hx1.
  rewrite !andb_true_r in Hx1. rewrite BA.covered_app. exact Hx1.
Qed.

Section Grows.
Variable segs : list Segment.

Lemma interp_eff_accesses_grows : forall (t : Sem.eff) m c m' rs,
  interp_eff_accesses segs t m = MachineOk (@mkAccessReport _ (c, m') rs) -> StoreOk.mem_grows m m'.
Proof.
  intros t. induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH];
    intros m c m' rs Hi; cbn [interp_eff_accesses] in Hi; try discriminate.
  - injection Hi as <- <- <-. apply StoreOk.mem_grows_refl.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [| destruct (range_meets_vvar segs a (width_bytes n)); discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-. exact (IH _ m c1 m1 rs1 Hk).
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))) as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    eapply StoreOk.mem_grows_trans; [apply StoreOk.write_to_mem_grows | exact (IH _ c1 m1 rs1 Hk)].
Qed.

Lemma step_mem_grows : forall ms ms',
  RiscvSemantics.step segs ms = MachineOk ms' -> StoreOk.mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros ms ms' Hs. unfold RiscvSemantics.step, drop_access_report in Hs.
  destruct (step_accesses segs ms) as [[v rs]| |] eqn:Hsa; try discriminate. injection Hs as ->.
  unfold step_accesses in Hsa.
  assert (HD : forall w, decode_exec_accesses segs ms w = MachineOk (@mkAccessReport _ ms' rs) -> StoreOk.mem_grows (ms_mem ms) (ms_mem ms')).
  { intros w Hd. unfold decode_exec_accesses in Hd. destruct (is_ecall w).
    - injection Hd as <- <-. cbn. apply StoreOk.mem_grows_refl.
    - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
      match type of Hd with context [interp_eff_accesses segs ?t ?m] =>
        destruct (interp_eff_accesses segs t m) as [[[c1 m1] rs1]| |] eqn:Hint; try discriminate end.
      cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-. cbn [ms_mem].
      exact (interp_eff_accesses_grows _ _ c1 m1 rs1 Hint). }
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (HD w Hsa)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (HD w Hsa)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (HD w Hsa)|].
  exfalso. unfold fetch_failure in Hsa.
  (* [comment removed for export] *)
  lazymatch type of Hsa with
  | context [if ?c then MachineUnmodeled else _] => destruct c; [discriminate|]
  end.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
            || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
               | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
               | None => false end); discriminate.
Qed.

Lemma msteps_mem_grows : forall ms ms', msteps segs ms ms' -> StoreOk.mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 _ Hs _ IH]; [apply StoreOk.mem_grows_refl|].
  eapply StoreOk.mem_grows_trans; [exact (step_mem_grows _ _ Hs) | exact IH].
Qed.
End Grows.

Definition art_ev_live (ev : aev) (l : list (Z * Z)) : list (Z * Z) :=
  match ev with
  | AMmapNull len r => (r, len) :: l
  | AMunmap addr len => List.filter (fun p => negb (fst p =? addr)) l
  | _ => l
  end.
Definition art_live (log : list aev) : list (Z * Z) := fold_left (fun l ev => art_ev_live ev l) log [].

Lemma art_live_snoc : forall log ev, art_live (log ++ [ev]) = art_ev_live ev (art_live log).
Proof. intros. unfold art_live. rewrite fold_left_app. reflexivity. Qed.

Definition art_cost (ev : aev) : Z :=
  match ev with
  | AMmapFixed _ len => len
  | AMmapNull len _ => len + len / 8 + 8192
  | _ => 0
  end.
Definition art_cost_sum (log : list aev) : Z := fold_right (fun ev z => art_cost ev + z) 0 log.

Lemma art_cost_sum_snoc : forall log ev, art_cost_sum (log ++ [ev]) = art_cost_sum log + art_cost ev.
Proof. intros log ev. unfold art_cost_sum. induction log as [|e l IH]; cbn [app fold_right]; [lia | rewrite IH; lia]. Qed.

Definition art_windows (log : list aev) : list (Z * Z) :=
  flat_map (fun ev => match ev with AMmapNull len r => [(art_shlo r, art_shhi r len)] | _ => [] end) log.

Lemma art_windows_snoc : forall log ev,
  art_windows (log ++ [ev]) = art_windows log ++ match ev with AMmapNull len r => [(art_shlo r, art_shhi r len)] | _ => [] end.
Proof. intros. unfold art_windows. rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r. reflexivity. Qed.

Definition toW (p : Z * Z) : word * word := (Z_to_bv 64 (fst p), Z_to_bv 64 (snd p)).
Definition live_sum (L : list (Z * Z)) : Z := fold_right (fun p z => snd p + z) 0 L.

Definition SHLO : Z := 0x7fff7000.
Definition SHHI : Z := 0x10007fff8000.
Definition LSH_LO : Z := 0x7fff8000.      Definition LSH_HI : Z := 0x8fff7000.
Definition HSH_LO : Z := 0x02008fff7000.  Definition HSH_HI : Z := 0x10007fff8000.
Definition in_shadow_rw (x : Z) : Prop := LSH_LO <= x < LSH_HI \/ HSH_LO <= x < HSH_HI.

Section Seam.
Variable RES : list (Z * Z).
Variable KN0 : list (Z * Z).
Variable CEIL : Z.
Variable BUDGET : Z.
Variable LENMAX KMAX : Z.

Definition art_EVOK (log : list aev) (ev : aev) : Prop :=
  match ev with
  | AMmapFixed addr len =>
      addr mod 4096 = 0 /\ len mod 4096 = 0 /\ 0 < len
      /\ (exists R, In R RES /\ fst R <= addr /\ addr + len <= fst R + snd R)
      /\ art_cost_sum (log ++ [ev]) <= BUDGET
  | AMmapNull len _ =>
      0 < len /\ len mod 4096 = 0 /\ len <= LENMAX
      /\ Z.of_nat (length (art_live log)) < KMAX
      /\ art_cost_sum (log ++ [ev]) <= BUDGET
  | AMmapFixedNR addr len =>
      addr mod 4096 = 0 /\ len mod 4096 = 0 /\ 0 < len
      /\ (exists w, In w (art_windows log) /\ fst w <= addr /\ addr + len <= snd w)
  | AMunmap addr len => In (addr, len) (art_live log)
  | AMadvise addr len =>
      addr mod 4096 = 0 /\ len mod 4096 = 0 /\ 0 < len
      /\ (exists w, In w (art_windows log) /\ fst w <= addr /\ addr + len <= snd w)
  end.

Definition art_GR (log : list aev) (M : word -> option byte) (len r : Z) : Prop :=
  r mod 4096 = 0 /\ 4096 <= r /\ r + len <= CEIL /\ r + len <= 2 ^ 47
  /\ (r + len <= SHLO \/ SHHI <= r)
  /\ (forall q, In q KN0 -> r + len <= fst q \/ snd q <= r)
  /\ (forall p, In p (art_live log) -> r + len <= fst p \/ fst p + snd p <= r).
End Seam.

Section Bridge.
Context {fx : PropExec.FPState}.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hwx : wx_segs_nowrap segs.

Variable MAPS0 : list (word * word).
Variable RESV0 : list (word * word).
Variable NOACC0 : list (word * word).
Variable RES : list (Z * Z).
Variable CEIL BASE BUDGET : Z.
Variable LENMAX KMAX : Z.

Definition ivZ (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (fst e) + bv_unsigned (snd e)).
Definition KN0 : list (Z * Z) := map ivZ (RESV0 ++ MAPS0).

Record bridge_static : Prop := BS {
  bs_maps_wf : BA.ivs_wf MAPS0;
  bs_maps_pos : forall q, In q MAPS0 -> 0 < BA.S q;
  bs_resv_pos : forall b s, In (b, s) RESV0 -> 0 < bv_unsigned s;
  bs_maps_nodup : List.NoDup MAPS0;
  bs_maps_apart : forall q q', In q MAPS0 -> In q' MAPS0 -> q <> q' -> BA.B q + BA.S q <= BA.B q' \/ BA.B q' + BA.S q' <= BA.B q;
  bs_shrw_off_segs : forall x, in_shadow_rw x -> find_segment segs x 1 = None;
  bs_res_in : forall R, In R RES -> In (toW R) MAPS0 /\ 0 < fst R /\ 0 < snd R /\ fst R + snd R <= CEIL /\ fst R + snd R < 2 ^ 64;
  bs_res_off_resv : forall R b s, In R RES -> In (b, s) RESV0 ->
                      fst R + snd R <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= fst R;
  bs_sh_in : forall x, SHLO <= x < SHHI -> BA.covered MAPS0 x = true;
  bs_shrw_entry : forall lo hi, lo < hi -> ((LSH_LO <= lo /\ hi <= LSH_HI) \/ (HSH_LO <= lo /\ hi <= HSH_HI)) ->
                    exists b s, In (b, s) MAPS0 /\ bv_unsigned b <= lo /\ hi <= bv_unsigned b + bv_unsigned s;
  bs_shrw_off_resv : forall x b s, in_shadow_rw x -> In (b, s) RESV0 -> ~ (bv_unsigned b <= x < bv_unsigned b + bv_unsigned s);
  bs_shrw_acc : forall x, in_shadow_rw x -> BA.covered NOACC0 x = false;
  bs_gap : AsanCeil.bottomup_floor + LENMAX + (AsanPlacement.gw_sizes (RESV0 ++ MAPS0) + BUDGET)
           + (Z.of_nat (length (RESV0 ++ MAPS0)) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling;
  bs_ceil : SHHI <= CEIL /\ CEIL + stack_max_size < 2 ^ 64 /\ CEIL <= 2 ^ 47;
  bs_budget : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62
}.
Hypothesis STATIC : bridge_static.

Notation EVOK := (art_EVOK RES BUDGET LENMAX KMAX).
Notation GR := (art_GR KN0 CEIL).

Definition grants (log : list aev) : list (word * word) := map toW (art_live log).

Definition window_ok (w : Z * Z) : Prop :=
  fst w mod 4096 = 0 /\ snd w mod 4096 = 0 /\ fst w <= snd w
  /\ ((LSH_LO <= fst w /\ snd w <= LSH_HI) \/ (HSH_LO <= fst w /\ snd w <= HSH_HI)).

Definition bhid (A : list (Z * Z)) (m : Model) : word -> bool := mkH (m_vm_lazy m) A.

Definition live_ok (L : list (Z * Z)) : Prop :=
  (forall p, In p L -> 0 < fst p /\ 0 < snd p /\ fst p mod 4096 = 0 /\ snd p mod 4096 = 0 /\ fst p + snd p <= CEIL
                       /\ (fst p + snd p <= SHLO \/ SHHI <= fst p)
                       /\ (forall q, In q KN0 -> fst p + snd p <= fst q \/ snd q <= fst p))
  /\ List.NoDup (map fst L)
  /\ (forall p p', In p L -> In p' L -> fst p <> fst p' -> fst p + snd p <= fst p' \/ fst p' + snd p' <= fst p).

Record BInv (log : list aev) (A : list (Z * Z)) (M : word -> option byte) (model : Model) : Prop := BI {
  bi_halt : m_halted model = None;
  bi_awf : A_wf A;
  bi_minv : MInv A model;
  bi_wf : BA.model_ivs_wf model;
  bi_maps : vm_maps (m_vmmaps model) = grants log ++ MAPS0;
  bi_resv : vm_reserved (m_vmmaps model) = RESV0;
  bi_top : alloc_top (m_vmmaps model) = CEIL;
  bi_limit : BASE + BUDGET <= vm_limit (m_vmmaps model);
  bi_noacc : forall x, BA.covered (vm_noaccess (m_vmmaps model)) x = true -> BA.covered NOACC0 x = true;
  bi_noacc_pos : forall q, In q (vm_noaccess (m_vmmaps model)) -> 0 < bv_unsigned (snd q);
  bi_lazy_in : forall a : word, page_in_ranges (page_base a) (m_vm_lazy model) = true ->
                 BA.covered MAPS0 (bv_unsigned a) = true /\ find_segment segs (bv_unsigned a) 1 = None;
  bi_live : live_ok (art_live log);
  bi_zero : forall a : word, bhid A model a = true -> BA.covered (vm_noaccess (m_vmmaps model)) (bv_unsigned a) = false ->
              M a = Some (Z_to_bv 8 0);
  bi_shdef : forall a : word, in_shadow_rw (bv_unsigned a) -> M a <> None;
  bi_windows : forall w, In w (art_windows log) -> In w A /\ window_ok w;
  bi_budget : eager_used model + A_bytes A <= BASE + art_cost_sum log;
  bi_cost : art_cost_sum log <= BUDGET;
  bi_livesum : live_sum (art_live log) <= art_cost_sum log
}.

Definition bmodel_rt (m m' : Model) : Prop :=
  m' = mkModelOf (m_fd m) (m_vm m') (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m).
Lemma bmodel_rt_refl : forall m, bmodel_rt m m.
Proof. intros m. unfold bmodel_rt. destruct m; reflexivity. Qed.
Lemma bmodel_rt_trans : forall m1 m2 m3, bmodel_rt m1 m2 -> bmodel_rt m2 m3 -> bmodel_rt m1 m3.
Proof. unfold bmodel_rt. intros m1 m2 m3 -> ->. destruct m1; reflexivity. Qed.
Lemma bmodel_rt_sbm : forall m m', same_but_materialized m m' -> bmodel_rt m m'.
Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Definition bstep (A : list (Z * Z)) (M : word -> option byte) (model : Model)
                 (A' : list (Z * Z)) (M' : word -> option byte) (model' : Model) (lo hi : Z) (nr : bool) : Prop :=
  incl A A'
  /\ (forall x : word, bhid A' model' x = true -> bhid A model x = true /\ M' x = M x)
  /\ (forall x : word, bhid A model x = true -> bhid A' model' x = false -> lo <= bv_unsigned x < hi)
  /\ (forall w, In w A' -> In w A \/ w = (lo, hi))
  /\ (forall x : word, page_in_ranges (page_base x) (m_vm_lazy model') = true ->
        page_in_ranges (page_base x) (m_vm_lazy model) = true \/ (nr = true /\ lo <= bv_unsigned x < hi)).

Lemma binv_hoff : forall log A M model, BInv log A M model -> H_off_segments segs (bhid A model).
Proof.
  intros log A M model B a Ha. unfold bhid, mkH in Ha. apply andb_prop in Ha as [Hp _].
  exact (proj2 (bi_lazy_in _ _ _ _ B a Hp)).
Qed.

Lemma bhid_lazy_cover : forall A model, lazy_cover (bhid A model) (m_vm_lazy model) A.
Proof. intros. unfold bhid. apply lazy_cover_mkH. intros r Hr; exact Hr. Qed.

Lemma binv_sbm : forall log A M model M' model',
  BInv log A M model -> MInv A model' -> same_but_materialized model model' ->
  (forall a, bhid A model a = true -> M' a = M a) ->
  (forall a : word, in_shadow_rw (bv_unsigned a) -> M' a <> None) ->
  BInv log A M' model'.
Proof.
  intros log A M model M' model' B Hminv Hs Hhid Hdef.
  destruct (same_but_materialized_frame _ _ Hs) as (_ & Hvm & Hlz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hh & _).
  assert (Heu : eager_used model' = eager_used model) by (apply eager_used_ext; assumption).
  destruct B. constructor; rewrite ?Hvm, ?Hlz, ?Hh, ?Heu; try assumption.
  - destruct bi_wf0 as (W1 & W2 & W3 & W4). unfold BA.model_ivs_wf. rewrite Hvm, Hlz. repeat split; assumption.
  - intros a Ha Hna. unfold bhid in Ha. rewrite Hlz in Ha. rewrite (Hhid a Ha). apply bi_zero0; [exact Ha | exact Hna].
Qed.

Lemma bridge_msteps : forall log A ms model msr' K,
  BInv log A (ms_mem ms) model ->
  msteps segs (restrict (bhid A model) ms) msr' ->
  (forall ms' model', restrict (bhid A model') ms' = msr' -> BInv log A (ms_mem ms') model' -> bmodel_rt model model' ->
     bstep A (ms_mem ms) model A (ms_mem ms') model' 0 0 false ->
     srealizes segs scfg (mkCfg ms' model') K) ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros log A ms model msr' K B MS HK.
  apply (srz_msteps_restricted_T segs scfg (bhid A model) (binv_hoff _ _ _ _ B) Hwx A ms msr' model K
           (bhid_lazy_cover A model) (bi_awf _ _ _ _ B) (bi_minv _ _ _ _ B) (bi_halt _ _ _ _ B) MS).
  intros model' Hminv Hs Hcl.
  destruct (same_but_materialized_frame _ _ Hs) as (_ & _ & Hlz & _).
  assert (EH : bhid A model' = bhid A model) by (unfold bhid; rewrite Hlz; reflexivity).
  apply HK.
  - rewrite EH. apply restrict_unrestrict_clean. exact Hcl.
  - rewrite unrestrict_mem. apply (binv_sbm log A (ms_mem ms) model); [exact B | exact Hminv | exact Hs | |].
    + intros a Ha. unfold munrestrict. rewrite Ha. reflexivity.
    + intros a Ha. unfold munrestrict. destruct (bhid A model a) eqn:E; [exact (bi_shdef _ _ _ _ B a Ha)|].
      apply (msteps_mem_grows segs _ _ MS). cbn [restrict ms_mem]. unfold mrestrict. rewrite E.
      exact (bi_shdef _ _ _ _ B a Ha).
  - apply bmodel_rt_sbm. exact Hs.
  - split; [apply incl_refl|]. split; [|split; [|split]].
    + intros x Hx. rewrite EH in Hx. split; [exact Hx|]. rewrite unrestrict_mem. unfold munrestrict. rewrite Hx. reflexivity.
    + intros x Hx Hx'. rewrite EH, Hx in Hx'. discriminate.
    + intros w0 Hw0. left. exact Hw0.
    + intros x Hx. left. rewrite <- Hlz. exact Hx.
Qed.

Lemma restrict_eq_mkst : forall (H : word -> bool) ms regs pc Mv rom,
  restrict H ms = mkst regs pc Mv rom -> ms = mkst regs pc (ms_mem ms) rom /\ Mv = mrestrict H (ms_mem ms).
Proof.
  intros H ms regs pc Mv rom E. destruct ms. unfold restrict, mkst in *. cbn in *.
  injection E as -> -> -> -> -> -> <- ->. split; reflexivity.
Qed.

Lemma u64z : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. apply BA.fg_lit. assumption. Qed.

Lemma view_zfill : forall (H H' : word -> bool) M (r len : Z),
  0 <= r -> 0 <= len -> r + len <= 2 ^ 64 -> len < 2 ^ 64 ->
  (forall a : word, r <= bv_unsigned a < r + len -> H' a = false) ->
  (forall a : word, ~ (r <= bv_unsigned a < r + len) -> H' a = H a) ->
  mrestrict H' (zfill (Z_to_bv 64 r) (Z_to_bv 64 len) M) = art_zfill (mrestrict H M) r len.
Proof.
  intros H H' M r len Hr Hl Hend Hl64 Hin Hout. apply functional_extensionality. intro a.
  pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
  destruct (Z_lt_ge_dec r (2 ^ 64)) as [Hr64|Hr64].
  2:{
      rewrite art_zfill_out by lia. unfold mrestrict. rewrite (Hout a) by lia.
      destruct (H a); [reflexivity|]. apply zfill_out. rewrite (u64z len) by lia.
      assert (len = 0) by lia. subst len. pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 r)). lia. }
  destruct (Z_le_dec r (bv_unsigned a)) as [H1|H1]; [destruct (Z_lt_dec (bv_unsigned a) (r + len)) as [H2|H2]|].
  - rewrite art_zfill_in by lia. unfold mrestrict. rewrite (Hin a) by lia.
    apply zfill_in. rewrite (u64z r), (u64z len) by lia. lia.
  - rewrite art_zfill_out by lia. unfold mrestrict. rewrite (Hout a) by lia.
    destruct (H a); [reflexivity|]. apply zfill_out. rewrite (u64z r), (u64z len) by lia. lia.
  - rewrite art_zfill_out by lia. unfold mrestrict. rewrite (Hout a) by lia.
    destruct (H a); [reflexivity|]. apply zfill_out. rewrite (u64z r), (u64z len) by lia. lia.
Qed.

Lemma view_unfill : forall (H H' : word -> bool) M (r len : Z),
  0 <= r < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
  (forall a : word, ~ (r <= bv_unsigned a < r + len) -> H' a = H a) ->
  mrestrict H' (unfill (Z_to_bv 64 r) (Z_to_bv 64 len) M) = art_unmap (mrestrict H M) r len.
Proof.
  intros H H' M r len Hr Hl Hout. apply functional_extensionality. intro a.
  unfold mrestrict, unfill, art_unmap. rewrite (u64z r), (u64z len) by lia.
  destruct ((r <=? bv_unsigned a) && (bv_unsigned a <? r + len))%bool eqn:E.
  - destruct (H' a); reflexivity.
  - rewrite (Hout a); [reflexivity|]. intros [H1 H2].
    apply andb_false_iff in E as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; lia.
Qed.

Lemma view_reveal : forall (H H' : word -> bool) M (lo hi : Z),
  (forall a : word, lo <= bv_unsigned a < hi -> H' a = false /\ M a <> None /\ (H a = true -> M a = Some (Z_to_bv 8 0))) ->
  (forall a : word, ~ (lo <= bv_unsigned a < hi) -> H' a = H a) ->
  mrestrict H' M = art_reveal (mrestrict H M) lo hi.
Proof.
  intros H H' M lo hi Hin Hout. apply functional_extensionality. intro a.
  unfold art_reveal, mrestrict.
  destruct ((lo <=? bv_unsigned a) && (bv_unsigned a <? hi))%bool eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    destruct (Hin a ltac:(lia)) as (H1 & H2 & H3). rewrite H1.
    destruct (H a); [rewrite (H3 eq_refl); reflexivity|]. destruct (M a); [reflexivity | contradiction].
  - rewrite (Hout a); [reflexivity|]. intros [H1 H2].
    apply andb_false_iff in E as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; lia.
Qed.

Lemma page_allowed_in : forall A (w : Z * Z) (x : word),
  In w A -> fst w mod 4096 = 0 -> snd w mod 4096 = 0 -> fst w <= bv_unsigned x < snd w ->
  page_allowedb A (page_base x) = true.
Proof.
  intros A w x Hin H1 H2 Hx. unfold page_allowedb. apply existsb_exists. exists w. split; [exact Hin|].
  destruct (page_of_byte_in_aligned x (fst w) (snd w) H1 H2 Hx) as [P1 P2].
  unfold page_size. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma page_in_ranges_subtract_le : forall (p : word) l lo hi,
  BA.ivs_wf l -> page_in_ranges p (maps_subtract l lo hi) = true -> page_in_ranges p l = true.
Proof.
  intros p l lo hi Hwf H. apply page_in_ranges_true in H as (q & Hq & H1 & H2).
  destruct (maps_subtract_pieces l lo hi q Hwf Hq) as (r & Hr & R1 & R2 & _).
  apply page_in_ranges_true. exists r. split; [exact Hr|]. lia.
Qed.

Lemma lazy_forget_out : forall lazy (extra : list (word * word)) lo hi (x : word),
  BA.ivs_wf lazy -> lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= hi ->
  (forall q, In q extra -> lo <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= hi) ->
  ~ (lo <= bv_unsigned x < hi) ->
  page_in_ranges (page_base x) (extra ++ maps_subtract lazy lo hi) = page_in_ranges (page_base x) lazy.
Proof.
  intros lazy extra lo hi x Hwf Hlo Hhi Hle Hex Hx.
  destruct (page_of_byte_out_aligned x lo hi Hlo Hhi ltac:(lia)) as [P|P].
  - rewrite page_in_ranges_app.
    replace (page_in_ranges (page_base x) extra) with false.
    + cbn [orb]. apply page_in_ranges_subtract_out; [exact Hwf | exact Hle | unfold page_size; lia].
    + symmetry. apply page_in_ranges_false. intros q Hq [Q1 Q2]. destruct (Hex q Hq). unfold page_size in *. lia.
  - rewrite page_in_ranges_app.
    replace (page_in_ranges (page_base x) extra) with false.
    + cbn [orb]. apply page_in_ranges_subtract_out; [exact Hwf | exact Hle | unfold page_size; lia].
    + symmetry. apply page_in_ranges_false. intros q Hq [Q1 Q2]. destruct (Hex q Hq). unfold page_size in *. lia.
Qed.

Definition forget_model (extra : list (word * word)) (lo hi : Z) (h' : VmMaps) (m : Model) : Model :=
  with_vm_backing (extra ++ maps_subtract (m_vm_lazy m) lo hi)
                  (List.filter (page_outside_range lo hi) (m_vm_materialized m)) (with_vmmaps h' m).

Lemma minv_forget : forall A m extra lo hi h' delta,
  MInv A m -> BA.ivs_wf (m_vm_lazy m) -> lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= hi ->
  (forall q, In q extra -> lo <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= hi) ->
  vm_limit h' = vm_limit (m_vmmaps m) ->
  eager_used (forget_model extra lo hi h' m) <= eager_used m + delta ->
  eager_used m + delta + A_bytes A <= vm_limit (m_vmmaps m) ->
  MInv A (forget_model extra lo hi h' m).
Proof.
  intros A m extra lo hi h' delta [Hnd Hal Hall Hlz Hbud] Hwf Hlo Hhi Hle Hex Hlim He Hb.
  constructor.
  - cbn. apply NoDup_filter. exact Hnd.
  - intros p Hp. cbn in Hp. apply filter_In in Hp as [Hp _]. exact (Hal p Hp).
  - intros p Hp. cbn in Hp. apply filter_In in Hp as [Hp _]. exact (Hall p Hp).
  - intros p Hp. cbn in Hp. apply filter_In in Hp as [Hp Ho].
    change (m_vm_lazy (forget_model extra lo hi h' m)) with (extra ++ maps_subtract (m_vm_lazy m) lo hi).
    rewrite page_in_ranges_app. apply orb_true_iff. right.
    rewrite page_in_ranges_subtract_out; [exact (Hlz p Hp) | exact Hwf | exact Hle |].
    pose proof (Hal p Hp) as Hpa. unfold page_size in *.
    unfold page_outside_range in Ho. apply negb_true_iff in Ho. apply andb_false_iff in Ho as [Ho|Ho];
      [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; [left | right; lia].

    assert (E1 : bv_unsigned p = 4096 * (bv_unsigned p / 4096)) by (apply Z.div_exact; lia).
    assert (E2 : lo = 4096 * (lo / 4096)) by (apply Z.div_exact; lia).
    assert (bv_unsigned p / 4096 < lo / 4096) by (apply Z.div_lt_upper_bound; lia). lia.
  - change (vm_limit (m_vmmaps (forget_model extra lo hi h' m))) with (vm_limit h'). rewrite Hlim. lia.
Qed.

Lemma maps_subtract_pos : forall l lo hi,
  (forall q, In q l -> 0 < bv_unsigned (snd q)) -> BA.ivs_wf l -> lo <= hi ->
  forall q, In q (maps_subtract l lo hi) -> 0 < bv_unsigned (snd q).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hpos Hwf Hle q Hq; [destruct Hq|].
  cbn [maps_subtract] in Hq. apply in_app_or in Hq as [Hq|Hq].
  - pose proof (Hpos (a, sz) (or_introl eq_refl)) as Hs. cbn [snd] in Hs.
    pose proof (Hwf (a, sz) (or_introl eq_refl)) as Hw. unfold BA.iv_wf, BA.B, BA.S in Hw. cbn [fst snd] in Hw.
    pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
    unfold iv_subtract in Hq. apply in_app_or in Hq as [Hq|Hq].
    + destruct (bv_unsigned a <? lo) eqn:E; [|destruct Hq]. apply Z.ltb_lt in E. destruct Hq as [<-|[]]. cbn [snd].
      rewrite u64z by lia. lia.
    + destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct Hq]. apply Z.ltb_lt in E. destruct Hq as [<-|[]]. cbn [snd].
      rewrite u64z by lia. lia.
  - apply (IH lo hi); [intros q' Hq'; apply Hpos; right; exact Hq' | intros q' Hq'; apply Hwf; right; exact Hq' | exact Hle | exact Hq].
Qed.

Lemma binv_forget : forall log log' A M M' model extra lo hi h' delta,
  BInv log A M model ->
  lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= hi ->
  BA.ivs_wf extra ->
  (forall q, In q extra -> lo <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= hi) ->
  (forall a : word, page_in_ranges (page_base a) extra = true ->
     BA.covered MAPS0 (bv_unsigned a) = true /\ find_segment segs (bv_unsigned a) 1 = None) ->
  vm_maps h' = grants log' ++ MAPS0 -> BA.ivs_wf (vm_maps h') ->
  vm_reserved h' = vm_reserved (m_vmmaps model) -> vm_limit h' = vm_limit (m_vmmaps model) ->
  vm_init_sp h' = vm_init_sp (m_vmmaps model) ->
  vm_noaccess h' = maps_subtract (vm_noaccess (m_vmmaps model)) lo hi ->
  live_ok (art_live log') -> live_sum (art_live log') <= live_sum (art_live log) -> art_windows log' = art_windows log ->
  art_cost_sum log' = art_cost_sum log + delta -> 0 <= delta -> art_cost_sum log' <= BUDGET ->
  eager_used (forget_model extra lo hi h' model) <= eager_used model + delta ->
  (forall a : word, lo <= bv_unsigned a < hi -> bhid A (forget_model extra lo hi h' model) a = false) ->
  (forall a : word, lo <= bv_unsigned a < hi -> in_shadow_rw (bv_unsigned a) -> M' a <> None) ->
  (forall a : word, ~ (lo <= bv_unsigned a < hi) -> M' a = M a) ->
  BInv log' A M' (forget_model extra lo hi h' model)
  /\ (forall a : word, ~ (lo <= bv_unsigned a < hi) -> bhid A (forget_model extra lo hi h' model) a = bhid A model a)
  /\ bstep A M model A M' (forget_model extra lo hi h' model) lo hi (match extra with [] => false | _ => true end).
Proof.
  intros log log' A M M' model extra lo hi h' delta B Hlo Hhi Hle Wex Hex HexIn Hmaps Wmaps Hresv Hlim Hisp Hna
         Hlive Hls Hwin Hcost Hd Hcb He Hvis Hdef Hout.
  set (m' := forget_model extra lo hi h' model) in *.
  destruct (bi_wf _ _ _ _ B) as (W1 & W2 & W3 & W4).
  destruct (BA.maps_subtract_sem _ lo hi W2 Hle) as (Wn' & _ & Cn).
  assert (HOUT : forall a : word, ~ (lo <= bv_unsigned a < hi) -> bhid A m' a = bhid A model a).
  { intros a Ha. unfold bhid, mkH. change (m_vm_lazy m') with (extra ++ maps_subtract (m_vm_lazy model) lo hi).
    rewrite (lazy_forget_out _ extra lo hi a W3 Hlo Hhi Hle Hex Ha). reflexivity. }
  split; [|split; [exact HOUT|]].
  2:{ split; [apply incl_refl|]. split; [|split; [|split]].
      4:{ intros x Hx. change (m_vm_lazy m') with (extra ++ maps_subtract (m_vm_lazy model) lo hi) in Hx.
          rewrite page_in_ranges_app in Hx. apply orb_prop in Hx as [Hx|Hx].
          - right. split; [destruct extra; [discriminate Hx | reflexivity]|].
            apply page_in_ranges_true in Hx as (q & Hq & Q1 & Q2). destruct (Hex q Hq) as [E1 E2].
            destruct (page_base_facts x) as (P1 & P2 & P3). unfold page_size in Q2. lia.
          - left. exact (page_in_ranges_subtract_le _ _ lo hi W3 Hx). }
      - intros x Hx. assert (Hn : ~ (lo <= bv_unsigned x < hi)) by (intros Hin; rewrite (Hvis x Hin) in Hx; discriminate).
        split; [rewrite <- (HOUT x Hn); exact Hx | exact (Hout x Hn)].
      - intros x Hx Hx'. destruct (Z_le_dec lo (bv_unsigned x)) as [L|L]; [destruct (Z_lt_dec (bv_unsigned x) hi) as [U|U]|].
        + lia.
        + rewrite (HOUT x ltac:(lia)), Hx in Hx'. discriminate.
        + rewrite (HOUT x ltac:(lia)), Hx in Hx'. discriminate.
      - intros w0 Hw0. left. exact Hw0. }
  constructor.
  - change (m_halted m') with (m_halted model). exact (bi_halt _ _ _ _ B).
  - exact (bi_awf _ _ _ _ B).
  - apply (minv_forget A model extra lo hi h' delta (bi_minv _ _ _ _ B) W3 Hlo Hhi Hle Hex Hlim He).
    pose proof (bi_budget _ _ _ _ B). pose proof (bi_limit _ _ _ _ B). lia.
  - unfold BA.model_ivs_wf. change (m_vmmaps m') with h'. change (m_vm_lazy m') with (extra ++ maps_subtract (m_vm_lazy model) lo hi).
    rewrite Hna. split; [exact Wmaps|]. split; [exact Wn'|]. split.
    + apply BA.ivs_wf_app; [exact Wex | apply BA.maps_subtract_wf; assumption].
    + exact (AsanCeil.init_sp_ok_same _ _ Hisp W4).
  - change (m_vmmaps m') with h'. exact Hmaps.
  - change (m_vmmaps m') with h'. rewrite Hresv. exact (bi_resv _ _ _ _ B).
  - change (m_vmmaps m') with h'. unfold alloc_top. rewrite Hisp. exact (bi_top _ _ _ _ B).
  - change (m_vmmaps m') with h'. rewrite Hlim. exact (bi_limit _ _ _ _ B).
  - change (m_vmmaps m') with h'. intros x Hx. rewrite Hna, Cn in Hx. apply andb_prop in Hx as [Hx _].
    exact (bi_noacc _ _ _ _ B x Hx).
  - change (m_vmmaps m') with h'. rewrite Hna. apply maps_subtract_pos; [exact (bi_noacc_pos _ _ _ _ B) | exact W2 | exact Hle].
  - intros a Ha. change (m_vm_lazy m') with (extra ++ maps_subtract (m_vm_lazy model) lo hi) in Ha.
    rewrite page_in_ranges_app in Ha. apply orb_prop in Ha as [Ha|Ha]; [exact (HexIn a Ha)|].
    apply (bi_lazy_in _ _ _ _ B a). exact (page_in_ranges_subtract_le _ _ lo hi W3 Ha).
  - exact Hlive.
  - intros a Ha Hnoa.
    destruct (Z_le_dec lo (bv_unsigned a)) as [L|L]; [destruct (Z_lt_dec (bv_unsigned a) hi) as [U|U]|].
    + rewrite (Hvis a (conj L U)) in Ha. discriminate.
    + rewrite (Hout a) by lia. apply (bi_zero _ _ _ _ B a); [rewrite <- (HOUT a) by lia; exact Ha|].
      change (m_vmmaps m') with h' in Hnoa. rewrite Hna, Cn in Hnoa.
      destruct (BA.covered (vm_noaccess (m_vmmaps model)) (bv_unsigned a)); [|reflexivity].
      cbn [andb] in Hnoa. apply negb_false_iff in Hnoa. unfold BA.in_rng in Hnoa. apply andb_prop in Hnoa as [N1 N2].
      apply Z.leb_le in N1. apply Z.ltb_lt in N2. lia.
    + rewrite (Hout a) by lia. apply (bi_zero _ _ _ _ B a); [rewrite <- (HOUT a) by lia; exact Ha|].
      change (m_vmmaps m') with h' in Hnoa. rewrite Hna, Cn in Hnoa.
      destruct (BA.covered (vm_noaccess (m_vmmaps model)) (bv_unsigned a)); [|reflexivity].
      cbn [andb] in Hnoa. apply negb_false_iff in Hnoa. unfold BA.in_rng in Hnoa. apply andb_prop in Hnoa as [N1 N2].
      apply Z.leb_le in N1. apply Z.ltb_lt in N2. lia.
  - intros a Ha.
    destruct (Z_le_dec lo (bv_unsigned a)) as [L|L]; [destruct (Z_lt_dec (bv_unsigned a) hi) as [U|U]|].
    + exact (Hdef a (conj L U) Ha).
    + rewrite (Hout a) by lia. exact (bi_shdef _ _ _ _ B a Ha).
    + rewrite (Hout a) by lia. exact (bi_shdef _ _ _ _ B a Ha).
  - rewrite Hwin. exact (bi_windows _ _ _ _ B).
  - pose proof (bi_budget _ _ _ _ B). lia.
  - exact Hcb.
  - pose proof (bi_livesum _ _ _ _ B). lia.
Qed.

Lemma shadow_rw_facts : forall lo hi, lo < hi -> ((LSH_LO <= lo /\ hi <= LSH_HI) \/ (HSH_LO <= lo /\ hi <= HSH_HI)) ->
  0 < lo /\ hi <= SHHI /\ SHLO <= lo /\ (forall x, lo <= x < hi -> in_shadow_rw x).
Proof.
  intros lo hi Hlt H. unfold LSH_LO, LSH_HI, HSH_LO, HSH_HI, SHHI, SHLO, in_shadow_rw in *.
  repeat split; try lia. intros x Hx. unfold LSH_LO, LSH_HI, HSH_LO, HSH_HI. lia.
Qed.

Lemma region_free_resv_shadow : forall lo hi, 0 <= lo -> lo < hi -> hi < 2 ^ 64 -> (forall x, lo <= x < hi -> in_shadow_rw x) ->
  region_free RESV0 (Z_to_bv 64 lo) (Z_to_bv 64 (hi - lo)) = true.
Proof.
  intros lo hi H0 Hlt Hhi Hsh. apply region_free_intro. intros b s Hin.
  rewrite (u64z lo), (u64z (hi - lo)) by lia.
  destruct (Z_le_dec (lo + (hi - lo)) (bv_unsigned b)) as [L|L]; [left; exact L|].
  destruct (Z_le_dec (bv_unsigned b + bv_unsigned s) lo) as [R|R]; [right; exact R|].
  exfalso. pose proof (bv_unsigned_in_range 64 b) as Rb. pose proof (bv_unsigned_in_range 64 s) as Rs.
  pose proof (bs_resv_pos STATIC b s Hin) as Hs.
  apply (bs_shrw_off_resv STATIC (Z.max lo (bv_unsigned b)) b s); [apply Hsh; lia | exact Hin | lia].
Qed.

Lemma mm1_eq : Z_to_bv 64 (2 ^ 64 - 1) = Z_to_bv 64 (-1).
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

Lemma bridge_fixed_nr : forall log A regs pc M rom model addr len K,
  BInv log A M model -> art_at_ecall segs pc -> art_mmap_args regs addr len 16434 ->
  EVOK log (AMmapFixedNR addr len) ->
  (forall M' model', BInv (log ++ [AMmapFixedNR addr len]) A M' model' -> bmodel_rt model model' ->
     bstep A M model A M' model' addr (addr + len) true ->
     mrestrict (bhid A model') M' = art_zfill (mrestrict (bhid A model) M) addr len ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 addr)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model') K) ->
  srealizes segs scfg (mkCfg (mkst regs pc M rom) model) K.
Proof.
  intros log A regs pc M rom model addr len K B (w & HF & HE) (H17 & H10 & H11 & H12 & H13 & H14 & H15)
         (Hal & Hll & Hlen & (win & Hwin & W1 & W2)) HK.
  destruct (bi_windows _ _ _ _ B win Hwin) as [HwA (Wa & Wb & Wle & Wsh)].
  assert (Hsub : (LSH_LO <= addr /\ addr + len <= LSH_HI) \/ (HSH_LO <= addr /\ addr + len <= HSH_HI)) by lia.
  destruct (shadow_rw_facts addr (addr + len) ltac:(lia) Hsub) as (Hpos & Hhi & Hlo & Hsh).
  destruct (bs_ceil STATIC) as (Hc1 & Hc2 & Hc3).
  assert (Hend : addr + len < 2 ^ 64) by (unfold stack_max_size in Hc2; lia).
  set (aW := Z_to_bv 64 addr). set (nW := Z_to_bv 64 len). set (flags := Z_to_bv 64 16434).
  assert (Ua : bv_unsigned aW = addr) by (apply u64z; lia).
  assert (Un : bv_unsigned nW = len) by (apply u64z; lia).
  assert (Hpr : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia | exact Hll]).
  set (h := m_vmmaps model).
  set (h' := mmap_fixed_rw_next h aW nW).
  assert (Em : fixedin_ok_model 3 flags aW nW model = forget_model [(aW, nW)] addr (addr + len) h' model).
  { unfold fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. cbn [Z.eqb].
    replace (mmap_noreserve_b flags) with true by (symmetry; apply mmap_noreserve_b_4032).
    unfold vm_add_lazy. rewrite (BA.lazy_interior_aligned aW nW) by (rewrite ?Ua, ?Un; unfold page_size; lia).
    rewrite Ua, Un. reflexivity. }
  destruct (bi_wf _ _ _ _ B) as (Wm & Wn & Wl & Wsp).
  destruct (binv_forget log (log ++ [AMmapFixedNR addr len]) A M (zfill aW nW M) model [(aW, nW)] addr (addr + len) h' 0 B) as (B' & HOUT & HST).
  - exact Hal.
  - rewrite Z.add_mod, Hal, Hll by lia. reflexivity.
  - lia.
  - apply BA.ivs_wf_cons; [unfold BA.iv_wf, BA.B, BA.S; cbn [fst snd]; rewrite Ua, Un; lia | apply BA.ivs_wf_nil].
  - intros q [<-|[]]. cbn [fst snd]. rewrite Ua, Un. lia.
  - intros a Ha. apply page_in_ranges_true in Ha as (q & [<-|[]] & Q1 & Q2). cbn [fst snd] in Q1, Q2. rewrite ?Ua, ?Un in Q1, Q2.
    destruct (page_base_facts a) as (P1 & P2 & P3). unfold page_size in Q2.
    assert (Hin : addr <= bv_unsigned a < addr + len) by lia.
    split; [apply (bs_sh_in STATIC); lia|].
    exact (bs_shrw_off_segs STATIC (bv_unsigned a) (Hsh _ Hin)).
  - unfold h', mmap_fixed_rw_next, grants. cbn [vm_maps]. rewrite art_live_snoc. cbn [art_ev_live]. exact (bi_maps _ _ _ _ B).
  - unfold h', mmap_fixed_rw_next. cbn [vm_maps]. exact Wm.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold h', mmap_fixed_rw_next. cbn [vm_noaccess]. rewrite Ua, Un. reflexivity.
  - rewrite art_live_snoc. cbn [art_ev_live]. exact (bi_live _ _ _ _ B).
  - rewrite art_live_snoc. cbn [art_ev_live]. lia.
  - rewrite art_windows_snoc, app_nil_r. reflexivity.
  - rewrite art_cost_sum_snoc. cbn [art_cost]. reflexivity.
  - lia.
  - rewrite art_cost_sum_snoc. cbn [art_cost]. pose proof (bi_cost _ _ _ _ B). lia.
  - rewrite <- Em. unfold fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. cbn [Z.eqb].
    replace (mmap_noreserve_b flags) with true by (symmetry; apply mmap_noreserve_b_4032).
    rewrite Z.add_0_r.
    apply (eager_recommit_le model (mmap_fixed_rw_next h aW nW) aW nW (bi_wf _ _ _ _ B));
      [rewrite Ua; unfold page_size; lia | rewrite Un; unfold page_size; lia | rewrite Un; lia | rewrite Ua, Un; lia
      | reflexivity | reflexivity].
  - intros a Ha. unfold bhid, mkH. rewrite (page_allowed_in A win a HwA Wa Wb ltac:(lia)). apply andb_false_r.
  - intros a Ha _. rewrite zfill_in by (rewrite Ua, Un; lia). discriminate.
  - intros a Ha. apply zfill_out. rewrite Ua, Un. lia.
  -
    apply (srz_mmap_fixedin_lazy segs scfg Halloc regs pc M rom model w 3 flags aW len K HF HE (bi_halt _ _ _ _ B) H17
             (or_intror eq_refl) mmap_flags_core_4032 H10 ltac:(rewrite Ua; unfold page_size; exact Hal) ltac:(rewrite Ua; exact Hpos)
             H11 Hlen ltac:(rewrite Ua, Hpr, (bi_top _ _ _ _ B); lia) H12 H13 ltac:(rewrite H14; exact mm1_eq) H15).
    + rewrite Hpr. fold nW. rewrite (bi_resv _ _ _ _ B).
      replace nW with (Z_to_bv 64 (addr + len - addr)) by (unfold nW; f_equal; lia).
      apply region_free_resv_shadow; try lia. exact Hsh.
    + rewrite Hpr. fold nW. rewrite (bi_maps _ _ _ _ B).
      destruct (bs_shrw_entry STATIC addr (addr + len) ltac:(lia) Hsub) as (b & s & Hbs & B1 & B2).
      apply (map_contains_intro _ aW nW b s); [apply in_or_app; right; exact Hbs | rewrite Ua; exact B1 | rewrite Ua, Un; exact B2].
    + intros _. rewrite Hpr. fold nW.
      apply BA.mmap_fixed_rw_budget_ok_recommit_intro; rewrite ?Ua, ?Un; unfold page_size; try lia;
        [apply mmap_noreserve_b_4032 | exact (bi_wf _ _ _ _ B) | exact (vm_backing_used_limit A model (bi_minv _ _ _ _ B) (bi_awf _ _ _ _ B))].
    + rewrite Hpr. fold nW. cbn [Z.eqb]. rewrite Em.
      apply HK; [exact B' | rewrite <- Em; unfold bmodel_rt; destruct model as [fd [maps lazy mat] io fs proc lim tm]; reflexivity | exact HST |].
      apply view_zfill; try lia.
      * intros a Ha. unfold bhid, mkH. rewrite (page_allowed_in A win a HwA Wa Wb ltac:(lia)). apply andb_false_r.
      * exact HOUT.
Qed.

Lemma overlap_sum_apart0 : forall l lo hi,
  (forall q, In q l -> BA.B q + BA.S q <= lo \/ hi <= BA.B q) -> BA.overlap_sum l lo hi = 0.
Proof.
  induction l as [|q l IH]; intros lo hi H; [reflexivity|].
  rewrite BA.overlap_sum_cons, (BA.iv_count_in_rng_disjoint q lo hi (H q (or_introl eq_refl))).
  rewrite IH; [reflexivity | intros q' Hq'; apply H; right; exact Hq'].
Qed.

Lemma ww_dec : forall q r : word * word, q = r \/ q <> r.
Proof.
  intros [a b] [c d]. destruct (bv_eqb a c) eqn:E1; [destruct (bv_eqb b d) eqn:E2|].
  - left. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. reflexivity.
  - right. intros E. injection E as _ ->. rewrite bv_eqb_refl in E2. discriminate.
  - right. intros E. injection E as -> _. rewrite bv_eqb_refl in E1. discriminate.
Qed.

Lemma overlap_sum_one : forall l R lo hi,
  List.NoDup l -> lo <= hi ->
  (forall q, In q l -> q <> R -> BA.B q + BA.S q <= lo \/ hi <= BA.B q) ->
  BA.overlap_sum l lo hi <= hi - lo.
Proof.
  induction l as [|q l IH]; intros R lo hi Hnd Hle H; [rewrite BA.overlap_sum_nil; lia|].
  rewrite BA.overlap_sum_cons. inversion Hnd as [|q0 l0 Hnin Hnd']; subst.
  destruct (ww_dec q R) as [E|E].
  - subst q. rewrite (overlap_sum_apart0 l lo hi).
    + pose proof (BA.iv_count_in_rng_le R lo hi Hle). lia.
    + intros q' Hq'. apply H; [right; exact Hq' | intros E'; subst q'; exact (Hnin Hq')].
  - rewrite (BA.iv_count_in_rng_disjoint q lo hi (H q (or_introl eq_refl) E)).
    pose proof (IH R lo hi Hnd' Hle ltac:(intros q' Hq'; apply H; right; exact Hq')). lia.
Qed.

Lemma live_word : forall L p, live_ok L -> In p L ->
  BA.B (toW p) = fst p /\ BA.S (toW p) = snd p /\ 0 < fst p /\ 0 < snd p /\ fst p + snd p < 2 ^ 64.
Proof.
  intros L p (Hl & _ & _) Hp. destruct (Hl p Hp) as (H1 & H2 & _ & _ & H5 & _).
  destruct (bs_ceil STATIC) as (_ & Hc2 & _). unfold stack_max_size in Hc2.
  unfold BA.B, BA.S, toW. cbn [fst snd]. rewrite !u64z by lia. repeat split; lia.
Qed.

Lemma res_word : forall R, In R RES ->
  BA.B (toW R) = fst R /\ BA.S (toW R) = snd R.
Proof.
  intros R HR. destruct (bs_res_in STATIC R HR) as (_ & H1 & H2 & _ & H4).
  unfold BA.B, BA.S, toW. cbn [fst snd]. rewrite !u64z by lia. split; reflexivity.
Qed.

Lemma overlap_in_res : forall log R lo hi,
  live_ok (art_live log) -> In R RES -> fst R <= lo -> lo <= hi -> hi <= fst R + snd R ->
  BA.overlap_sum (grants log ++ MAPS0) lo hi <= hi - lo.
Proof.
  intros log R lo hi HL HR H1 Hle H2.
  destruct (bs_res_in STATIC R HR) as (HRin & _). destruct (res_word R HR) as (ER1 & ER2).
  rewrite BA.overlap_sum_app. rewrite (overlap_sum_apart0 (grants log)).
  - apply (overlap_sum_one MAPS0 (toW R) lo hi (bs_maps_nodup STATIC) Hle).
    intros q Hq Hne. destruct (bs_maps_apart STATIC q (toW R) Hq HRin Hne) as [A1|A1]; rewrite ?ER1, ?ER2 in A1; lia.
  - intros q Hq. unfold grants in Hq. apply in_map_iff in Hq as (p & <- & Hp).
    destruct (live_word _ p HL Hp) as (E1 & E2 & _). rewrite E1, E2.
    destruct HL as (Hl & _ & _). destruct (Hl p Hp) as (_ & _ & _ & _ & _ & _ & Hk).
    assert (Hkin : In (ivZ (toW R)) KN0) by (unfold KN0; apply in_map; apply in_or_app; right; exact HRin).
    destruct (Hk _ Hkin) as [K|K]; unfold ivZ in K; cbn [fst snd] in K;
      fold (BA.B (toW R)) in K; fold (BA.S (toW R)) in K; rewrite ?ER1, ?ER2 in K; lia.
Qed.

Lemma bridge_fixed : forall log A regs pc M rom model addr len K,
  BInv log A M model -> art_at_ecall segs pc -> art_mmap_args regs addr len 50 ->
  EVOK log (AMmapFixed addr len) ->
  (forall M' model', BInv (log ++ [AMmapFixed addr len]) A M' model' -> bmodel_rt model model' ->
     bstep A M model A M' model' addr (addr + len) false ->
     mrestrict (bhid A model') M' = art_zfill (mrestrict (bhid A model) M) addr len ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 addr)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model') K) ->
  srealizes segs scfg (mkCfg (mkst regs pc M rom) model) K.
Proof.
  intros log A regs pc M rom model addr len K B (w & HF & HE) (H17 & H10 & H11 & H12 & H13 & H14 & H15)
         (Hal & Hll & Hlen & (R & HR & R1 & R2) & Hcb) HK.
  destruct (bs_res_in STATIC R HR) as (HRin & Rp & Rs & Rc & R64).
  destruct (res_word R HR) as (ER1 & ER2).
  destruct (bs_ceil STATIC) as (Hc1 & Hc2 & Hc3).
  set (aW := Z_to_bv 64 addr). set (nW := Z_to_bv 64 len). set (flags := Z_to_bv 64 50).
  assert (Ua : bv_unsigned aW = addr) by (apply u64z; lia).
  assert (Un : bv_unsigned nW = len) by (apply u64z; lia).
  assert (Hpr : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia | exact Hll]).
  set (h := m_vmmaps model).
  set (h' := mmap_fixed_rw_next h aW nW).
  assert (Em : fixedin_ok_model 3 flags aW nW model = forget_model [] addr (addr + len) h' model).
  { unfold fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. cbn [Z.eqb].
    replace (mmap_noreserve_b flags) with false by (symmetry; apply mmap_noreserve_b_32).
    rewrite Ua, Un. reflexivity. }
  destruct (bi_wf _ _ _ _ B) as (Wm & Wn & Wl & Wsp).
  assert (Hov : BA.overlap_sum (vm_maps h) addr (addr + len) <= len).
  { unfold h. rewrite (bi_maps _ _ _ _ B).
    pose proof (overlap_in_res log R addr (addr + len) (bi_live _ _ _ _ B) HR R1 ltac:(lia) R2). lia. }
  assert (He : eager_used (forget_model [] addr (addr + len) h' model) <= eager_used model + len).
  { pose proof (eager_commit_le model h' (bv_unsigned aW) (bv_unsigned aW + bv_unsigned nW)
                  (bi_wf _ _ _ _ B) ltac:(rewrite Un; lia) eq_refl eq_refl) as HE'.
    rewrite Ua, Un in HE'. eapply Z.le_trans; [exact HE'|]. unfold h in Hov. lia. }
  destruct (binv_forget log (log ++ [AMmapFixed addr len]) A M (zfill aW nW M) model [] addr (addr + len) h' len B) as (B' & HOUT & HST).
  - exact Hal.
  - rewrite Z.add_mod, Hal, Hll by lia. reflexivity.
  - lia.
  - apply BA.ivs_wf_nil.
  - intros q [].
  - intros a Ha. cbn in Ha. discriminate.
  - unfold h', mmap_fixed_rw_next, grants. cbn [vm_maps]. rewrite art_live_snoc. cbn [art_ev_live]. exact (bi_maps _ _ _ _ B).
  - unfold h', mmap_fixed_rw_next. cbn [vm_maps]. exact Wm.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold h', mmap_fixed_rw_next. cbn [vm_noaccess]. rewrite Ua, Un. reflexivity.
  - rewrite art_live_snoc. cbn [art_ev_live]. exact (bi_live _ _ _ _ B).
  - rewrite art_live_snoc. cbn [art_ev_live]. lia.
  - rewrite art_windows_snoc, app_nil_r. reflexivity.
  - rewrite art_cost_sum_snoc. cbn [art_cost]. reflexivity.
  - lia.
  - exact Hcb.
  - exact He.
  - intros a Ha. unfold bhid, mkH. change (m_vm_lazy (forget_model [] addr (addr + len) h' model)) with (maps_subtract (m_vm_lazy model) addr (addr + len)).
    rewrite page_in_ranges_subtract_in; [reflexivity | exact Wl |].
    destruct (page_of_byte_in_aligned a addr (addr + len) Hal ltac:(rewrite Z.add_mod, Hal, Hll by lia; reflexivity) Ha) as [P1 P2]. lia.
  - intros a Ha _. rewrite zfill_in by (rewrite Ua, Un; lia). discriminate.
  - intros a Ha. apply zfill_out. rewrite Ua, Un. lia.
  -
    apply (srz_mmap_fixedin_lazy segs scfg Halloc regs pc M rom model w 3 flags aW len K HF HE (bi_halt _ _ _ _ B) H17
             (or_intror eq_refl) mmap_flags_core_32 H10 ltac:(rewrite Ua; unfold page_size; exact Hal) ltac:(rewrite Ua; lia)
             H11 Hlen ltac:(rewrite Ua, Hpr, (bi_top _ _ _ _ B); lia) H12 H13 ltac:(rewrite H14; exact mm1_eq) H15).
    + rewrite Hpr. fold nW. rewrite (bi_resv _ _ _ _ B). apply region_free_intro. intros b s Hbs. rewrite Ua, Un.
      destruct (bs_res_off_resv STATIC R b s HR Hbs); lia.
    + rewrite Hpr. fold nW. rewrite (bi_maps _ _ _ _ B).
      apply (map_contains_intro _ aW nW (fst (toW R)) (snd (toW R))).
      * apply in_or_app. right. destruct (toW R); exact HRin.
      * fold (BA.B (toW R)). rewrite ER1, Ua. exact R1.
      * fold (BA.B (toW R)). fold (BA.S (toW R)). rewrite ER1, ER2, Ua, Un. exact R2.
    + intros _. rewrite Hpr. fold nW.
      apply BA.mmap_fixed_rw_budget_ok_commit_intro; [apply mmap_noreserve_b_32 | exact (bi_wf _ _ _ _ B) |].
      rewrite Ua, Un. fold h.
      pose proof (vm_backing_used_le A model (bi_minv _ _ _ _ B) (bi_awf _ _ _ _ B)).
      pose proof (bi_budget _ _ _ _ B). pose proof (bi_limit _ _ _ _ B).
      rewrite art_cost_sum_snoc in Hcb. cbn [art_cost] in Hcb. unfold h in *. lia.
    + rewrite Hpr. fold nW. cbn [Z.eqb]. rewrite Em.
      apply HK; [exact B' | rewrite <- Em; unfold bmodel_rt; destruct model as [fd [maps lazy mat] io fs proc lim tm]; reflexivity | exact HST |].
      apply view_zfill; try lia.
      * intros a Ha. unfold bhid, mkH. change (m_vm_lazy (forget_model [] addr (addr + len) h' model)) with (maps_subtract (m_vm_lazy model) addr (addr + len)).
        rewrite page_in_ranges_subtract_in; [reflexivity | exact Wl |].
        destruct (page_of_byte_in_aligned a addr (addr + len) Hal ltac:(rewrite Z.add_mod, Hal, Hll by lia; reflexivity) Ha) as [P1 P2]. lia.
      * exact HOUT.
Qed.

Lemma filter_all_true : forall {T} (f : T -> bool) l, (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof.
  intros T f l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)).
  f_equal. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma live_sum_filter : forall (f : Z * Z -> bool) L, (forall p, In p L -> 0 <= snd p) -> live_sum (List.filter f L) <= live_sum L.
Proof.
  intros f L H. unfold live_sum. induction L as [|q L IH]; cbn [List.filter fold_right]; [lia|].
  pose proof (IH ltac:(intros p Hp; apply H; right; exact Hp)) as IH'. pose proof (H q (or_introl eq_refl)).
  destruct (f q); cbn [fold_right]; lia.
Qed.

Lemma live_ok_filter : forall (f : Z * Z -> bool) L, live_ok L -> live_ok (List.filter f L).
Proof.
  intros f L (H1 & H2 & H3). split; [|split].
  - intros p Hp. apply filter_In in Hp as [Hp _]. exact (H1 p Hp).
  - clear H1 H3. induction L as [|q L IH]; cbn; [constructor|]. inversion H2 as [|x l Hnin Hnd]; subst.
    destruct (f q); cbn; [constructor; [|exact (IH Hnd)] | exact (IH Hnd)].
    intros Hin. apply Hnin. apply in_map_iff in Hin as (p & E & Hp). apply filter_In in Hp as [Hp _].
    apply in_map_iff. exists p. split; assumption.
  - intros p p' Hp Hp'. apply filter_In in Hp as [Hp _]. apply filter_In in Hp' as [Hp' _]. exact (H3 p p' Hp Hp').
Qed.

Lemma maps0_apart_live : forall L p q, live_ok L -> In p L -> In q MAPS0 ->
  BA.B q + BA.S q <= fst p \/ fst p + snd p <= BA.B q.
Proof.
  intros L p q (Hl & _ & _) Hp Hq. destruct (Hl p Hp) as (_ & _ & _ & _ & _ & _ & Hk).
  assert (Hkin : In (ivZ q) KN0) by (unfold KN0; apply in_map; apply in_or_app; right; exact Hq).
  unfold BA.B, BA.S. destruct (Hk _ Hkin) as [K|K]; unfold ivZ in K; cbn [fst snd] in K; lia.
Qed.

Lemma map_remove_live : forall log addr len,
  live_ok (art_live log) -> In (addr, len) (art_live log) ->
  map_remove (grants log ++ MAPS0) (Z_to_bv 64 addr) = grants (log ++ [AMunmap addr len]) ++ MAPS0.
Proof.
  intros log addr len HL Hin. unfold map_remove, grants. rewrite filter_app, art_live_snoc. cbn [art_ev_live].
  destruct (live_word _ _ HL Hin) as (E1 & E2 & P1 & P2 & P3). cbn [fst snd] in *.
  f_equal.
  - apply filter_map_ext. intros p Hp. destruct (live_word _ _ HL Hp) as (F1 & _ & Q1 & Q2 & Q3).
    unfold toW. cbn [fst]. f_equal. unfold bv_eqb. rewrite !u64z by lia. reflexivity.
  - apply filter_all_true. intros q Hq. apply negb_true_iff. apply bv_eqb_neq. intros E.
    pose proof (maps0_apart_live _ _ q HL Hin Hq) as Hap. pose proof (bs_maps_pos STATIC q Hq) as Hs.
    unfold BA.B in Hap. rewrite E, (u64z addr) in Hap by lia. cbn [fst snd] in Hap. lia.
Qed.

Lemma live_fst_inj : forall L p p', live_ok L -> In p L -> In p' L -> fst p = fst p' -> p = p'.
Proof.
  intros L p p' (_ & Hnd & _) Hp Hp' Hfst. revert Hnd Hp Hp'.
  induction L as [|q L IH]; intros Hnd Hp Hp'; [destruct Hp|].
  cbn [map] in Hnd. apply NoDup_cons_iff in Hnd as [Hni Hnd].
  destruct Hp as [<-|Hp]; destruct Hp' as [<-|Hp'].
  - reflexivity.
  - exfalso. apply Hni. rewrite Hfst. apply in_map. exact Hp'.
  - exfalso. apply Hni. rewrite <- Hfst. apply in_map. exact Hp.
  - exact (IH Hnd Hp Hp').
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_live : forall log addr len,
  live_ok (art_live log) -> In (addr, len) (art_live log) ->
  maps_subtract (grants log ++ MAPS0) (bv_unsigned (Z_to_bv 64 addr))
    (bv_unsigned (Z_to_bv 64 addr) + bv_unsigned (Z_to_bv 64 len))
  = map_remove (grants log ++ MAPS0) (Z_to_bv 64 addr).
Proof.
  intros log addr len HL Hin.
  assert (HL' := HL). destruct HL' as (_ & _ & Hap0).
  destruct (live_word _ _ HL Hin) as (_ & _ & Hpos & Hlen0 & H64). cbn [fst snd] in *.
  assert (Ua : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply u64z; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 len) = len) by (apply u64z; lia).
  apply MmapSim.maps_subtract_exact.
  - rewrite Un. lia.
  - intros b s Hq. apply in_app_or in Hq as [Hq|Hq].
    + unfold grants in Hq. apply in_map_iff in Hq as (p & Ep & Hp).
      unfold toW in Ep. injection Ep as <- <-.
      destruct (live_word _ _ HL Hp) as (_ & _ & P1 & P2 & P3). cbn [fst snd] in *.
      rewrite (u64z (snd p)) by lia. exact P2.
    + pose proof (bs_maps_pos STATIC (b, s) Hq) as Hs. unfold BA.S in Hs. cbn [snd] in Hs. exact Hs.
  - intros b s Hq Eb. apply in_app_or in Hq as [Hq|Hq].
    + unfold grants in Hq. apply in_map_iff in Hq as (p & Ep & Hp).
      unfold toW in Ep. injection Ep as <- <-.
      destruct (live_word _ _ HL Hp) as (_ & _ & P1 & P2 & P3). cbn [fst snd] in *.
      assert (Efst : fst p = addr).
      { apply (f_equal bv_unsigned) in Eb. rewrite (u64z (fst p)) in Eb by lia.
        rewrite Ua in Eb. exact Eb. }
      rewrite (live_fst_inj _ p (addr, len) HL Hp Hin ltac:(cbn [fst]; exact Efst)). reflexivity.
    + exfalso. pose proof (maps0_apart_live _ _ (b, s) HL Hin Hq) as Hq'.
      pose proof (bs_maps_pos STATIC (b, s) Hq) as Hs.
      unfold BA.B, BA.S in Hq', Hs. cbn [fst snd] in Hq', Hs.
      rewrite Eb, Ua in Hq'. lia.
  - intros b s Hq Hne. rewrite Ua, Un. apply in_app_or in Hq as [Hq|Hq].
    + unfold grants in Hq. apply in_map_iff in Hq as (p & Ep & Hp).
      unfold toW in Ep. injection Ep as <- <-.
      destruct (live_word _ _ HL Hp) as (_ & _ & P1 & P2 & P3). cbn [fst snd] in *.
      rewrite (u64z (fst p)) by lia. rewrite (u64z (snd p)) by lia.
      assert (Hne' : fst p <> addr) by (intros E; apply Hne; rewrite E; reflexivity).
      destruct (Hap0 p (addr, len) Hp Hin ltac:(cbn [fst]; exact Hne')); cbn [fst snd] in *; lia.
    + pose proof (maps0_apart_live _ _ (b, s) HL Hin Hq) as Hq'.
      unfold BA.B, BA.S in Hq'. cbn [fst snd] in Hq'. lia.
Qed.

Lemma bridge_munmap : forall log A regs pc M rom model addr len K,
  BInv log A M model -> art_at_ecall segs pc -> art_munmap_args regs addr len ->
  EVOK log (AMunmap addr len) ->
  (forall M' model', BInv (log ++ [AMunmap addr len]) A M' model' -> bmodel_rt model model' ->
     bstep A M model A M' model' addr (addr + len) false ->
     mrestrict (bhid A model') M' = art_unmap (mrestrict (bhid A model) M) addr len ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model') K) ->
  srealizes segs scfg (mkCfg (mkst regs pc M rom) model) K.
Proof.
  intros log A regs pc M rom model addr len K B (w & HF & HE) (H17 & H10 & H11) Hlive HK.
  cbn [art_EVOK] in Hlive.
  pose proof (bi_live _ _ _ _ B) as HL.
  destruct (live_word _ _ HL Hlive) as (E1 & E2 & Hpos & Hlen & H64). cbn [fst snd] in *.
  destruct HL as (Hl & Hnd & Hap). destruct (Hl _ Hlive) as (_ & _ & Hal & Hll & Hce & Hsh & Hk). cbn [fst snd] in *.
  destruct (bs_ceil STATIC) as (Hc1 & Hc2 & Hc3).
  set (aW := Z_to_bv 64 addr). set (nW := Z_to_bv 64 len).
  assert (Ua : bv_unsigned aW = addr) by (apply u64z; lia).
  assert (Un : bv_unsigned nW = len) by (apply u64z; lia).
  assert (Hpr : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia | exact Hll]).
  set (h := m_vmmaps model).
  set (h' := munmap_vmmaps aW nW h).
  assert (Em : munmap_model aW nW model = forget_model [] addr (addr + len) h' model).
  { rewrite munmap_model_eq, Ua, Un. reflexivity. }
  destruct (bi_wf _ _ _ _ B) as (Wm & Wn & Wl & Wsp).
  assert (Hmaps' : vm_maps h' = grants (log ++ [AMunmap addr len]) ++ MAPS0).
  { unfold h', munmap_vmmaps, aW, nW. cbn [vm_maps]. unfold h. rewrite (bi_maps _ _ _ _ B).
    rewrite (maps_subtract_live log addr len (bi_live _ _ _ _ B) Hlive).
    apply map_remove_live; [exact (bi_live _ _ _ _ B) | exact Hlive]. }
  destruct (binv_forget log (log ++ [AMunmap addr len]) A M (unfill aW nW M) model [] addr (addr + len) h' 0 B) as (B' & HOUT & HST).
  - exact Hal.
  - rewrite Z.add_mod, Hal, Hll by lia. reflexivity.
  - lia.
  - apply BA.ivs_wf_nil.
  - intros q [].
  - intros a Ha. cbn in Ha. discriminate.
  - exact Hmaps'.
  - unfold h', munmap_vmmaps. cbn [vm_maps].
    apply BA.maps_subtract_wf; [unfold h; exact Wm | rewrite Un; lia].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold h', munmap_vmmaps. cbn [vm_noaccess]. rewrite Ua, Un. reflexivity.
  - rewrite art_live_snoc. cbn [art_ev_live]. apply live_ok_filter. exact (bi_live _ _ _ _ B).
  - rewrite art_live_snoc. cbn [art_ev_live]. apply live_sum_filter. intros p Hp. destruct (Hl p Hp) as (_ & Hp2 & _). lia.
  - rewrite art_windows_snoc, app_nil_r. reflexivity.
  - rewrite art_cost_sum_snoc. cbn [art_cost]. reflexivity.
  - lia.
  - rewrite art_cost_sum_snoc. cbn [art_cost]. pose proof (bi_cost _ _ _ _ B). lia.
  - rewrite <- Em, Z.add_0_r. apply eager_unmap_le; [exact (bi_wf _ _ _ _ B)|].
    intros q Hq Hne. rewrite (bi_maps _ _ _ _ B) in Hq. rewrite Ua, Un. apply in_app_or in Hq as [Hq|Hq].
    + unfold grants in Hq. apply in_map_iff in Hq as (p & <- & Hp).
      destruct (live_word _ _ (bi_live _ _ _ _ B) Hp) as (F1 & F2 & Q1 & Q2 & Q3). rewrite F1, F2.
      assert (Hne' : fst p <> addr).
      { intros E. unfold toW, aW in Hne. cbn [fst] in Hne. rewrite E, bv_eqb_refl in Hne. discriminate. }
      destruct (Hap p (addr, len) Hp Hlive Hne'); cbn [fst snd] in *; lia.
    + pose proof (maps0_apart_live _ _ q (bi_live _ _ _ _ B) Hlive Hq) as Hq'. cbn [fst snd] in Hq'. lia.
  - intros a Ha. unfold bhid, mkH. change (m_vm_lazy (forget_model [] addr (addr + len) h' model)) with (maps_subtract (m_vm_lazy model) addr (addr + len)).
    rewrite page_in_ranges_subtract_in; [reflexivity | exact Wl |].
    destruct (page_of_byte_in_aligned a addr (addr + len) Hal ltac:(rewrite Z.add_mod, Hal, Hll by lia; reflexivity) Ha) as [P1 P2]. lia.
  - intros a Ha Hs. exfalso. unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI, SHLO, SHHI in *. lia.
  - intros a Ha. unfold unfill. rewrite Ua, Un.
    destruct ((addr <=? bv_unsigned a) && (bv_unsigned a <? addr + len))%bool eqn:E; [|reflexivity].
    apply andb_prop in E as [E3 E4]. apply Z.leb_le in E3. apply Z.ltb_lt in E4. lia.
  -
    (* [comment removed for export] *)
    apply (AsanNodesLibEK.srz_munmap_lazy segs scfg Halloc regs pc M rom model w aW len K HF HE (bi_halt _ _ _ _ B) H17 H10
             ltac:(rewrite Ua; unfold page_size; exact Hal) H11 Hlen ltac:(rewrite Ua, Hpr; unfold TASK_SIZE; lia)).
    + rewrite Hpr. fold nW. rewrite (bi_maps _ _ _ _ B). apply map_has_intro. apply in_or_app. left.
      unfold grants. apply in_map_iff. exists (addr, len). split; [reflexivity | exact Hlive].
    + rewrite Hpr. fold nW. rewrite Em.
      apply HK; [exact B' | rewrite <- Em; unfold bmodel_rt; destruct model as [fd [maps lazy mat] io fs proc lim tm]; reflexivity | exact HST |].
      apply view_unfill; [lia | lia | exact HOUT].
Qed.

Lemma window_facts : forall r len,
  r mod 4096 = 0 -> len mod 4096 = 0 -> 0 < len -> 4096 <= r -> r + len <= 2 ^ 47 ->
  (r + len <= SHLO \/ SHHI <= r) ->
  window_ok (art_shlo r, art_shhi r len)
  /\ art_shhi r len - art_shlo r <= len / 8 + 8192
  /\ (forall x, art_shlo r <= x < art_shhi r len -> ~ (r <= x < r + len)).
Proof.
  intros r len Hr Hl Hlen H4 H47 Hsh. unfold window_ok, art_shlo, art_shhi, SHLO, SHHI, LSH_LO, LSH_HI, HSH_LO, HSH_HI in *.
  cbn [fst snd].
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  repeat split; try lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma gw_sizes_app : forall l1 l2, AsanPlacement.gw_sizes (l1 ++ l2) = AsanPlacement.gw_sizes l1 + AsanPlacement.gw_sizes l2.
Proof. induction l1 as [|q l1 IH]; intros l2; cbn [app AsanPlacement.gw_sizes]; [lia | rewrite IH; lia]. Qed.

Lemma gw_sizes_grants : forall L, live_ok L -> AsanPlacement.gw_sizes (map toW L) = live_sum L.
Proof.
  intros L HL. assert (H : forall p, In p L -> BA.S (toW p) = snd p) by (intros p Hp; apply (live_word L p HL Hp)).
  clear HL. unfold live_sum. induction L as [|q L IH]; cbn [map AsanPlacement.gw_sizes fold_right]; [reflexivity|].
  rewrite IH by (intros p Hp; apply H; right; exact Hp).
  pose proof (H q (or_introl eq_refl)) as Hq. unfold BA.S in Hq. rewrite Hq. reflexivity.
Qed.

Lemma grant_exists : forall log A M model len,
  BInv log A M model -> 0 < len <= LENMAX -> Z.of_nat (length (art_live log)) < KMAX ->
  exists a : word, grant_ok_na_pin model a len = true.
Proof.
  intros log A M model len B Hlen HK.
  destruct (bs_budget STATIC) as (HB0 & HK0 & HL0). pose proof (bs_gap STATIC) as Hgap.
  set (h := m_vmmaps model).
  assert (EL : vm_reserved h ++ vm_maps h = RESV0 ++ grants log ++ MAPS0)
    by (unfold h; rewrite (bi_resv _ _ _ _ B), (bi_maps _ _ _ _ B); reflexivity).
  assert (Hsz : AsanPlacement.gw_sizes (vm_reserved h ++ vm_maps h) <= AsanPlacement.gw_sizes (RESV0 ++ MAPS0) + BUDGET).
  { rewrite EL, !gw_sizes_app. unfold grants. rewrite (gw_sizes_grants _ (bi_live _ _ _ _ B)).
    pose proof (bi_livesum _ _ _ _ B). pose proof (bi_cost _ _ _ _ B). lia. }
  assert (Hlen' : Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= Z.of_nat (length (RESV0 ++ MAPS0)) + KMAX).
  { rewrite EL, !length_app. unfold grants. rewrite length_map. lia. }
  destruct (AsanPlacement.free_gap_of_totals h len (AsanPlacement.gw_sizes (RESV0 ++ MAPS0) + BUDGET) ltac:(lia) Hsz)
    as (g & Hal & Hfl & Hc & Hfree & _).
  { assert (Hm : Z.of_nat (length (vm_reserved h ++ vm_maps h)) * (len + 4095)
                 <= (Z.of_nat (length (RESV0 ++ MAPS0)) + KMAX) * (LENMAX + 4095)).
    { apply Z.mul_le_mono_nonneg; lia. }
    lia. }
  destruct (bi_wf _ _ _ _ B) as (_ & _ & _ & Wsp).
  pose proof (AsanCeil.alloc_ceiling_le_alloc_top h Wsp) as Htop.
  pose proof AsanCeil.bottomup_floor_val as Hfv. pose proof AsanCeil.alloc_ceiling_val as Hcv.
  exists (Z_to_bv 64 g). unfold grant_ok_na_pin. fold h. rewrite (u64z g) by lia.
  rewrite Hfree. unfold page_size in Hal |- *.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt 0 g)) by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_na : forall log A M model len,
  BInv log A M model -> 0 < len <= LENMAX -> len mod page_size = 0 -> Z.of_nat (length (art_live log)) < KMAX ->
  exists a : word, OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.grant_ok_na (Z_to_bv 64 0) model a len = true.
Proof.
  intros log A M model len B Hlen Hnal HK.
  destruct (bs_budget STATIC) as (HB0 & HK0 & HL0). pose proof (bs_gap STATIC) as Hgap.
  set (h := m_vmmaps model).
  assert (EL : vm_reserved h ++ vm_maps h = RESV0 ++ grants log ++ MAPS0)
    by (unfold h; rewrite (bi_resv _ _ _ _ B), (bi_maps _ _ _ _ B); reflexivity).
  assert (Hsz : AsanPlacement.gw_sizes (vm_reserved h ++ vm_maps h) <= AsanPlacement.gw_sizes (RESV0 ++ MAPS0) + BUDGET).
  { rewrite EL, !gw_sizes_app. unfold grants. rewrite (gw_sizes_grants _ (bi_live _ _ _ _ B)).
    pose proof (bi_livesum _ _ _ _ B). pose proof (bi_cost _ _ _ _ B). lia. }
  assert (Hlen' : Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= Z.of_nat (length (RESV0 ++ MAPS0)) + KMAX).
  { rewrite EL, !length_app. unfold grants. rewrite length_map. lia. }
  destruct (AsanPlacement.free_gap_of_totals h len (AsanPlacement.gw_sizes (RESV0 ++ MAPS0) + BUDGET) ltac:(lia) Hsz)
    as (g & Hal & Hfl & Hc & Hfree & _).
  { assert (Hm : Z.of_nat (length (vm_reserved h ++ vm_maps h)) * (len + 4095)
                 <= (Z.of_nat (length (RESV0 ++ MAPS0)) + KMAX) * (LENMAX + 4095)).
    { apply Z.mul_le_mono_nonneg; lia. }
    lia. }
  destruct (bi_wf _ _ _ _ B) as (_ & _ & _ & Wsp).
  pose proof (AsanCeil.alloc_ceiling_le_alloc_top h Wsp) as Htop.
  pose proof AsanCeil.bottomup_floor_val as Hfv. pose proof AsanCeil.alloc_ceiling_val as Hcv.
  assert (Hn0 : 0 < len) by lia.
  destruct (Placement.linux_place_exists h (kb_thp (m_kernel model)) (Z_to_bv 64 0) len Hn0 Hnal) as (a & Hpl).
  { exists g. right. apply Placement.gap_fits_b_iff. unfold Placement.gap_fits_b.
    rewrite Hfree, (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.leb_le (g + len) _)) by lia.
    rewrite (proj2 (Z.leb_le _ g)); [reflexivity|].
    apply Z.le_trans with AsanCeil.bottomup_floor; [|exact Hfl].
    vm_compute. intro Hc0. discriminate Hc0. }
  destruct (Placement.linux_place_admissible _ _ _ _ _ Hn0 Hnal Hpl) as (Hal' & Hpos' & Hhi' & Hfree').
  pose proof (alloc_top_lt h) as Hat. unfold two_pow_64 in Hat.
  exists (Z_to_bv 64 a).
  apply (grant_ok_na_of_place _ _ _ _ Hn0 Hnal).
  apply (proj2 (Placement.linux_place_is_iff _ _ _ _ _ Hn0 Hnal)).
  rewrite (u64z a) by lia. exact Hpl.
Qed.

Lemma aligned_pos_ge : forall r, r mod 4096 = 0 -> 0 < r -> 4096 <= r.
Proof.
  intros r H1 H2.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma grant_parts : forall model (a : word) n,
  grant_ok_na_pin model a n = true ->
  bv_unsigned a mod 4096 = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + n <= alloc_top (m_vmmaps model)
  /\ region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a (Z_to_bv 64 n) = true.
Proof.
  intros model a n H. unfold grant_ok_na_pin in H.
  apply andb_true_iff in H as [H Hrf]. apply andb_true_iff in H as [H Htop]. apply andb_true_iff in H as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop. unfold page_size in Hal. auto.
Qed.

Lemma apart_of_covered : forall l (a n : word) lo hi,
  region_free l a n = true -> 0 < bv_unsigned n -> lo < hi ->
  (forall x, lo <= x < hi -> BA.covered l x = true) ->
  bv_unsigned a + bv_unsigned n <= lo \/ hi <= bv_unsigned a.
Proof.
  intros l a n lo hi Hrf Hn Hlh Hcov.
  destruct (Z_le_dec (bv_unsigned a + bv_unsigned n) lo) as [L|L]; [left; exact L|].
  destruct (Z_le_dec hi (bv_unsigned a)) as [R|R]; [right; exact R|]. exfalso.
  set (x := Z.max (bv_unsigned a) lo).
  pose proof (Hcov x ltac:(unfold x; lia)) as Hc. rewrite <- in_ivs_covered in Hc.
  rewrite (region_free_sem l a n x Hrf Hn ltac:(unfold x; lia)) in Hc. discriminate.
Qed.

Lemma binv_null : forall log A M model len (a : word),
  BInv log A M model -> EVOK log (AMmapNull len 0) -> grant_ok_na_pin model a len = true ->
  let r := bv_unsigned a in
  let nW := Z_to_bv 64 len in
  let w := (art_shlo r, art_shhi r len) in
  let model' := mmap_model a nW model in
  GR log (mrestrict (bhid A model) M) len r
  /\ BInv (log ++ [AMmapNull len r]) (A ++ [w]) (zfill a nW M) model'
  /\ bmodel_rt model model'
  /\ mrestrict (bhid (A ++ [w]) model') (zfill a nW M)
     = art_reveal (art_zfill (mrestrict (bhid A model) M) r len) (art_shlo r) (art_shhi r len)
  /\ bstep A M model (A ++ [w]) (zfill a nW M) model' (art_shlo r) (art_shhi r len) false.
Proof.
  intros log A M model len a B (Hlen & Hll & Hmax & HKc & Hcb) Hg r nW w model'.
  destruct (grant_parts model a len Hg) as (Hal & Hpos & Htop & Hrf). fold r in Hal, Hpos, Htop.
  rewrite (bi_top _ _ _ _ B) in Htop. rewrite (bi_resv _ _ _ _ B), (bi_maps _ _ _ _ B) in Hrf.
  destruct (bs_ceil STATIC) as (Hc1 & Hc2 & Hc3). destruct (bs_budget STATIC) as (HB0 & HK0 & HL0).
  unfold stack_max_size in Hc2.
  assert (Un : bv_unsigned nW = len) by (apply u64z; lia).
  assert (Ea : Z_to_bv 64 r = a) by (apply Z_to_bv_u_eq'; reflexivity).
  fold nW in Hrf.

  assert (Hent : forall b s, In (b, s) (RESV0 ++ grants log ++ MAPS0) ->
            r + len <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= r).
  { intros b s Hin. pose proof (region_free_In _ a nW b s Hrf Hin) as H. rewrite Un in H. exact H. }
  assert (Hsh : r + len <= SHLO \/ SHHI <= r).
  { assert (Hrf0 : region_free MAPS0 a nW = true).
    { rewrite !region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf]. apply andb_prop in Hrf as [_ Hrf]. exact Hrf. }
    pose proof (apart_of_covered MAPS0 a nW SHLO SHHI Hrf0 ltac:(lia) ltac:(unfold SHLO, SHHI; lia) (bs_sh_in STATIC)) as H.
    rewrite Un in H. exact H. }
  pose proof (aligned_pos_ge r Hal Hpos) as H4k.
  destruct (window_facts r len Hal Hll Hlen H4k ltac:(lia) Hsh) as (Wok & Wsz & Wdis).
  destruct Wok as (Wa & Wb & Wle & Wsh). cbn [fst snd] in Wa, Wb, Wle, Wsh.
  assert (Hlive_ap : forall p, In p (art_live log) -> r + len <= fst p \/ fst p + snd p <= r).
  { intros p Hp. destruct (live_word _ _ (bi_live _ _ _ _ B) Hp) as (F1 & F2 & _).
    pose proof (Hent (fst (toW p)) (snd (toW p))) as H. fold (BA.B (toW p)) in H. fold (BA.S (toW p)) in H.
    rewrite F1, F2 in H. apply H. apply in_or_app. right. apply in_or_app. left. unfold grants.
    apply in_map_iff. exists p. split; [destruct (toW p); reflexivity | exact Hp]. }
  assert (Hkn_ap : forall q, In q KN0 -> r + len <= fst q \/ snd q <= r).
  { intros q Hq. unfold KN0 in Hq. apply in_map_iff in Hq as ([b s] & <- & Hin). unfold ivZ. cbn [fst snd].
    apply Hent. apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin | right; apply in_or_app; right; exact Hin]. }

  assert (Hnl : forall x : word, r <= bv_unsigned x < r + len -> page_in_ranges (page_base x) (m_vm_lazy model) = false).
  { intros x Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model)) eqn:E; [|reflexivity]. exfalso.
    destruct (bi_lazy_in _ _ _ _ B x E) as [Hcov _]. rewrite <- in_ivs_covered in Hcov.
    apply in_ivs_true' in Hcov as ([b s] & Hin & Hb). cbn [fst snd] in Hb.
    destruct (Hent b s ltac:(apply in_or_app; right; apply in_or_app; right; exact Hin)); lia. }
  assert (HW2 : forall x : word, ~ (art_shlo r <= bv_unsigned x < art_shhi r len) ->
                  bhid (A ++ [w]) model' x = bhid A model x).
  { intros x Hx. unfold bhid, mkH. change (m_vm_lazy model') with (m_vm_lazy model). f_equal. f_equal.
    unfold page_allowedb. rewrite existsb_app. cbn [existsb]. rewrite orb_false_r.
    replace ((fst w <=? bv_unsigned (page_base x)) && (bv_unsigned (page_base x) + page_size <=? snd w))%bool with false;
      [apply orb_false_r|].
    symmetry. apply andb_false_iff. unfold page_size, w. cbn [fst snd].
    destruct (page_of_byte_out_aligned x (art_shlo r) (art_shhi r len) Wa Wb ltac:(lia)) as [P|P];
      [left; apply Z.leb_gt; lia | right; apply Z.leb_gt; lia]. }
  assert (HW1 : forall x : word, art_shlo r <= bv_unsigned x < art_shhi r len -> bhid (A ++ [w]) model' x = false).
  { intros x Hx. unfold bhid, mkH.
    rewrite (page_allowed_in (A ++ [w]) w x); [apply andb_false_r | apply in_or_app; right; left; reflexivity | exact Wa | exact Wb | exact Hx]. }
  split; [|split; [|split; [|split]]].
  -   unfold art_GR. repeat split; try assumption; lia.
  -
    destruct (bi_wf _ _ _ _ B) as (Wm & Wn & Wl & Wsp).
    assert (Ecost : art_cost_sum (log ++ [AMmapNull len r]) = art_cost_sum log + (len + len / 8 + 8192))
      by (rewrite art_cost_sum_snoc; reflexivity).
    assert (Ecost0 : art_cost_sum (log ++ [AMmapNull len 0]) = art_cost_sum log + (len + len / 8 + 8192))
      by (rewrite art_cost_sum_snoc; reflexivity).
    assert (He : eager_used model' <= eager_used model + len).
    { rewrite <- Un. unfold model', mmap_model.
      apply (eager_grant_le model a nW); [exact (bi_wf _ _ _ _ B) | fold r; rewrite Un; lia | reflexivity | reflexivity]. }
    constructor.
    + exact (bi_halt _ _ _ _ B).
    + unfold A_wf. apply Forall_app. split; [exact (bi_awf _ _ _ _ B)|]. constructor; [|constructor].
      unfold w, page_size. cbn [fst snd]. repeat split; assumption.
    + destruct (bi_minv _ _ _ _ B) as [Hnd Hal' Hall Hlz Hbud]. constructor.
      * exact Hnd.
      * exact Hal'.
      * intros p Hp. unfold page_allowedb. rewrite existsb_app. apply orb_true_iff. left. exact (Hall p Hp).
      * exact Hlz.
      * rewrite A_bytes_app'. unfold w. cbn [A_bytes fst snd]. change (vm_limit (m_vmmaps model')) with (vm_limit (m_vmmaps model)).
        pose proof (bi_budget _ _ _ _ B). pose proof (bi_limit _ _ _ _ B). lia.
    + unfold BA.model_ivs_wf. change (m_vm_lazy model') with (m_vm_lazy model).
      split; [|split; [exact Wn | split; [exact Wl | exact Wsp]]].
      apply BA.ivs_wf_cons; [|exact Wm]. unfold BA.iv_wf, BA.B, BA.S. cbn [fst snd]. fold r. rewrite Un. lia.
    + change (vm_maps (m_vmmaps model')) with ((a, nW) :: vm_maps (m_vmmaps model)). rewrite (bi_maps _ _ _ _ B).
      unfold grants. rewrite art_live_snoc. cbn [art_ev_live map].
      change (toW (r, len)) with (Z_to_bv 64 r, nW). rewrite Ea. reflexivity.
    + exact (bi_resv _ _ _ _ B).
    + exact (bi_top _ _ _ _ B).
    + exact (bi_limit _ _ _ _ B).
    + exact (bi_noacc _ _ _ _ B).
    + exact (bi_noacc_pos _ _ _ _ B).
    + exact (bi_lazy_in _ _ _ _ B).
    + rewrite art_live_snoc. cbn [art_ev_live]. destruct (bi_live _ _ _ _ B) as (L1 & L2 & L3). split; [|split].
      * intros p [<-|Hp]; [cbn [fst snd]; repeat split; try assumption; lia | exact (L1 p Hp)].
      * cbn [map fst]. constructor; [|exact L2]. intros Hin. apply in_map_iff in Hin as (p & E & Hp).
        destruct (L1 p Hp) as (_ & P2 & _). destruct (Hlive_ap p Hp); lia.
      * intros p p' [<-|Hp] [<-|Hp'] Hne; cbn [fst snd] in *.
        -- contradiction.
        -- destruct (Hlive_ap p' Hp'); lia.
        -- destruct (Hlive_ap p Hp); lia.
        -- exact (L3 p p' Hp Hp' Hne).
    + intros x Hx Hna.
      assert (Hx0 : bhid A model x = true).
      { unfold bhid, mkH in Hx |- *. change (m_vm_lazy model') with (m_vm_lazy model) in Hx.
        apply andb_prop in Hx as [X1 X2]. rewrite X1. cbn [andb]. apply negb_true_iff. apply negb_true_iff in X2.
        unfold page_allowedb in X2 |- *. rewrite existsb_app in X2. apply orb_false_iff in X2 as [X2 _]. exact X2. }
      assert (Hout : ~ (r <= bv_unsigned x < r + len)).
      { intros Hin. unfold bhid, mkH in Hx0. rewrite (Hnl x Hin) in Hx0. discriminate. }
      rewrite zfill_out by (fold r; rewrite Un; lia). exact (bi_zero _ _ _ _ B x Hx0 Hna).
    + intros x Hx. destruct (Z_le_dec r (bv_unsigned x)) as [L|L]; [destruct (Z_lt_dec (bv_unsigned x) (r + len)) as [U|U]|].
      * rewrite zfill_in by (fold r; rewrite Un; lia). discriminate.
      * rewrite zfill_out by (fold r; rewrite Un; lia). exact (bi_shdef _ _ _ _ B x Hx).
      * rewrite zfill_out by (fold r; rewrite Un; lia). exact (bi_shdef _ _ _ _ B x Hx).
    + intros w0 Hw0. rewrite art_windows_snoc in Hw0. apply in_app_or in Hw0 as [Hw0|[<-|[]]].
      * destruct (bi_windows _ _ _ _ B w0 Hw0) as [H1 H2]. split; [apply in_or_app; left; exact H1 | exact H2].
      * split; [apply in_or_app; right; left; reflexivity|]. unfold window_ok. cbn [fst snd]. auto.
    + rewrite A_bytes_app'. unfold w. cbn [A_bytes fst snd]. pose proof (bi_budget _ _ _ _ B). lia.
    + lia.
    + rewrite art_live_snoc. cbn [art_ev_live]. unfold live_sum. cbn [fold_right snd]. fold (live_sum (art_live log)).
      pose proof (bi_livesum _ _ _ _ B). assert (0 <= len / 8) by (apply Z.div_pos; lia). lia.
  - unfold bmodel_rt, model', mmap_model. destruct model as [fd [maps lazy mat] io fs proc lim tm]. reflexivity.
  -
    set (H0 := bhid A model). set (H1 := bhid A model'). set (H2 := bhid (A ++ [w]) model').
    assert (E1 : mrestrict H1 (zfill a nW M) = art_zfill (mrestrict H0 M) r len).
    { rewrite <- Ea at 1. unfold nW. apply view_zfill; try lia.
      - intros x Hx. unfold H1, bhid, mkH. change (m_vm_lazy model') with (m_vm_lazy model). rewrite (Hnl x Hx). reflexivity.
      - intros x _. reflexivity. }
    rewrite <- E1. apply view_reveal.
    + intros x Hx.
      assert (Hxs : in_shadow_rw (bv_unsigned x)) by (unfold in_shadow_rw; lia).
      assert (Hxo : ~ (r <= bv_unsigned x < r + len)) by (apply Wdis; exact Hx).
      split; [|split].
      * unfold H2, bhid, mkH. rewrite (page_allowed_in (A ++ [w]) w x); [apply andb_false_r | apply in_or_app; right; left; reflexivity | exact Wa | exact Wb | exact Hx].
      * rewrite zfill_out by (fold r; rewrite Un; lia). exact (bi_shdef _ _ _ _ B x Hxs).
      * intros Hh. rewrite zfill_out by (fold r; rewrite Un; lia). apply (bi_zero _ _ _ _ B x Hh).
        destruct (BA.covered (vm_noaccess (m_vmmaps model)) (bv_unsigned x)) eqn:E; [|reflexivity].
        pose proof (bi_noacc _ _ _ _ B _ E) as E'. rewrite (bs_shrw_acc STATIC _ Hxs) in E'. discriminate.
    + intros x Hx. unfold H2, H1, bhid, mkH. f_equal. f_equal. unfold page_allowedb. rewrite existsb_app. cbn [existsb].
      rewrite orb_false_r.
      replace ((fst w <=? bv_unsigned (page_base x)) && (bv_unsigned (page_base x) + page_size <=? snd w))%bool with false;
        [apply orb_false_r|].
      symmetry. apply andb_false_iff. unfold page_size, w. cbn [fst snd].
      destruct (page_of_byte_out_aligned x (art_shlo r) (art_shhi r len) Wa Wb ltac:(lia)) as [P|P];
        [left; apply Z.leb_gt; lia | right; apply Z.leb_gt; lia].
  -
    split; [intros q Hq; apply in_or_app; left; exact Hq|]. split; [|split; [|split]].
    3:{ intros w0 Hw0. apply in_app_or in Hw0 as [Hw0|[<-|[]]]; [left; exact Hw0 | right; reflexivity]. }
    3:{ intros x Hx. left. exact Hx. }
    + intros x Hx.
      assert (Hnw : ~ (art_shlo r <= bv_unsigned x < art_shhi r len)) by (intros Hin; rewrite (HW1 x Hin) in Hx; discriminate).
      rewrite (HW2 x Hnw) in Hx. split; [exact Hx|].
      apply zfill_out. fold r. rewrite Un.
      destruct (Z_lt_dec (bv_unsigned x) r) as [L|L]; [left; exact L|].
      destruct (Z_le_dec (r + len) (bv_unsigned x)) as [U|U]; [right; exact U|].
      exfalso. unfold bhid, mkH in Hx. rewrite (Hnl x ltac:(lia)) in Hx. discriminate.
    + intros x Hx Hx'. destruct (Z_le_dec (art_shlo r) (bv_unsigned x)) as [L|L]; [destruct (Z_lt_dec (bv_unsigned x) (art_shhi r len)) as [U|U]|].
      * lia.
      * rewrite (HW2 x ltac:(lia)), Hx in Hx'. discriminate.
      * rewrite (HW2 x ltac:(lia)), Hx in Hx'. discriminate.
Qed.

Lemma bridge_null : forall log A regs pc M rom model len K,
  BInv log A M model -> art_at_ecall segs pc -> art_mmap_args regs 0 len 34 ->
  EVOK log (AMmapNull len 0) ->
  (forall r A' M' model', GR log (mrestrict (bhid A model) M) len r ->
     BInv (log ++ [AMmapNull len r]) A' M' model' -> bmodel_rt model model' ->
     bstep A M model A' M' model' (art_shlo r) (art_shhi r len) false ->
     mrestrict (bhid A' model') M'
       = art_reveal (art_zfill (mrestrict (bhid A model) M) r len) (art_shlo r) (art_shhi r len) ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 r)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model') K) ->
  srealizes segs scfg (mkCfg (mkst regs pc M rom) model) K.
Proof.
  intros log A regs pc M rom model len K B (w & HF & HE) (H17 & H10 & H11 & H12 & H13 & H14 & H15) Hev HK.
  pose proof Hev as (Hlen & Hll & Hmax & HKc & Hcb).
  destruct (bs_budget STATIC) as (HB0 & HK0 & HL0).
  assert (Hpr : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia | exact Hll]).
  (* [comment removed for export] *)
  apply (srz_mmap_rw1 segs scfg Halloc regs pc M rom model w len (Z_to_bv 64 34) K HF HE (bi_halt _ _ _ _ B) H17 H11
           ltac:(lia) H12 H13 mmap_flags_core_22 ltac:(rewrite H14; exact mm1_eq) H15
           ltac:(rewrite H10; apply place_declined_b_null)).
  - (* [comment removed for export] *)
    rewrite Hpr, H10.
    exact (grant_exists_na log A M model len B ltac:(lia)
             ltac:(first [exact Hll | unfold page_size; exact Hll | unfold page_size in Hll; exact Hll]) HKc).
  - rewrite Hpr. unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_22. apply Z.leb_le.
    pose proof (vm_backing_used_le A model (bi_minv _ _ _ _ B) (bi_awf _ _ _ _ B)).
    pose proof (bi_budget _ _ _ _ B). pose proof (bi_limit _ _ _ _ B).
    rewrite art_cost_sum_snoc in Hcb. cbn [art_cost] in Hcb.
    assert (0 <= len / 8) by (apply Z.div_pos; lia). lia.
  - rewrite Hpr. intros a Hg.
    destruct (binv_null log A M model len a B Hev Hg) as (HGR & B' & Hrt & Hview & HST).
    unfold with_mmap_backing. rewrite mmap_noreserve_b_22.
    pose proof (HK (bv_unsigned a) _ _ _ HGR B' Hrt HST Hview) as HK'.
    replace (Z_to_bv 64 (bv_unsigned a)) with a in HK' by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
    exact HK'.
Qed.

Lemma sbm_madvise : forall m (a n : word), same_but_materialized m (madvise_dontneed_next m a n).
Proof. intros m a n. unfold same_but_materialized, madvise_dontneed_next. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma minv_madvise : forall A m (a n : word), MInv A m -> MInv A (madvise_dontneed_next m a n).
Proof.
  intros A m a n [N1 N2 N3 N4 N5].
  destruct (same_but_materialized_frame _ _ (sbm_madvise m a n)) as (_ & Hvm & Hlz & _).
  assert (Hmat : m_vm_materialized (madvise_dontneed_next m a n)
                 = List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m)).
  { unfold madvise_dontneed_next. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. }
  constructor.
  - rewrite Hmat. apply NoDup_filter. exact N1.
  - intros p Hp. rewrite Hmat in Hp. apply filter_In in Hp as [Hp _]. exact (N2 p Hp).
  - intros p Hp. rewrite Hmat in Hp. apply filter_In in Hp as [Hp _]. exact (N3 p Hp).
  - intros p Hp. rewrite Hmat in Hp. apply filter_In in Hp as [Hp _]. rewrite Hlz. exact (N4 p Hp).
  - rewrite Hvm. rewrite (eager_used_ext (madvise_dontneed_next m a n) m) by assumption. exact N5.
Qed.

Lemma binv_snoc_madvise : forall log A M model addr len,
  BInv log A M model -> BInv (log ++ [AMadvise addr len]) A M model.
Proof.
  intros log A M model addr len B. destruct B. constructor; try assumption.
  - unfold grants. rewrite art_live_snoc. exact bi_maps0.
  - rewrite art_live_snoc. exact bi_live0.
  - intros w Hw. rewrite art_windows_snoc, app_nil_r in Hw. exact (bi_windows0 w Hw).
  - rewrite art_cost_sum_snoc. cbn [art_cost]. lia.
  - rewrite art_cost_sum_snoc. cbn [art_cost]. lia.
  - rewrite art_live_snoc, art_cost_sum_snoc. cbn [art_ev_live art_cost]. lia.
Qed.

Lemma bridge_madvise : forall log A regs pc M rom model addr len K,
  BInv log A M model -> art_at_ecall segs pc -> art_madvise_args regs addr len ->
  EVOK log (AMadvise addr len) ->
  (forall M' model', BInv (log ++ [AMadvise addr len]) A M' model' -> bmodel_rt model model' ->
     bstep A M model A M' model' addr (addr + len) false ->
     mrestrict (bhid A model') M' = art_zfill (mrestrict (bhid A model) M) addr len ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model') K) ->
  srealizes segs scfg (mkCfg (mkst regs pc M rom) model) K.
Proof.
  intros log A regs pc M rom model addr len K B (w & HF & HE) (H17 & H10 & H11 & H12)
         (Hal & Hll & Hlen & (win & Hwin & W1 & W2)) HK.
  destruct (bi_windows _ _ _ _ B win Hwin) as [HwA (Wa & Wb & Wle & Wsh)].
  assert (Hsub : (LSH_LO <= addr /\ addr + len <= LSH_HI) \/ (HSH_LO <= addr /\ addr + len <= HSH_HI)) by lia.
  destruct (shadow_rw_facts addr (addr + len) ltac:(lia) Hsub) as (Hpos & Hhi & Hlo & Hsh).
  destruct (bs_ceil STATIC) as (Hc1 & Hc2 & Hc3).
  assert (Hend : addr + len < 2 ^ 64) by (unfold stack_max_size in Hc2; lia).
  set (aW := Z_to_bv 64 addr). set (nW := Z_to_bv 64 len).
  assert (Ua : bv_unsigned aW = addr) by (apply u64z; lia).
  assert (Un : bv_unsigned nW = len) by (apply u64z; lia).
  set (model' := madvise_dontneed_next model aW nW).
  assert (Hs : same_but_materialized model model') by apply sbm_madvise.
  destruct (same_but_materialized_frame _ _ Hs) as (_ & _ & Hlz & _).
  assert (EH : bhid A model' = bhid A model) by (unfold bhid; rewrite Hlz; reflexivity).
  assert (Hvis : forall a : word, addr <= bv_unsigned a < addr + len -> bhid A model a = false).
  { intros a Ha. unfold bhid, mkH. rewrite (page_allowed_in A win a HwA Wa Wb ltac:(lia)). apply andb_false_r. }
  assert (B' : BInv (log ++ [AMadvise addr len]) A (zfill aW nW M) model').
  { apply binv_snoc_madvise. apply (binv_sbm log A M model); [exact B | apply minv_madvise; exact (bi_minv _ _ _ _ B) | exact Hs | |].
    - intros a Ha. apply zfill_out. rewrite Ua, Un.
      destruct (Z_lt_dec (bv_unsigned a) addr) as [L|L]; [left; exact L|].
      destruct (Z_le_dec (addr + len) (bv_unsigned a)) as [U|U]; [right; exact U|].
      exfalso. rewrite (Hvis a ltac:(lia)) in Ha. discriminate.
    - intros a Ha. destruct (Z_le_dec addr (bv_unsigned a)) as [L|L]; [destruct (Z_lt_dec (bv_unsigned a) (addr + len)) as [U|U]|].
      + rewrite zfill_in by (rewrite Ua, Un; lia). discriminate.
      + rewrite zfill_out by (rewrite Ua, Un; lia). exact (bi_shdef _ _ _ _ B a Ha).
      + rewrite zfill_out by (rewrite Ua, Un; lia). exact (bi_shdef _ _ _ _ B a Ha). }
  apply (srz_madvise_lazy segs scfg regs pc M rom model w aW len K HF HE (bi_halt _ _ _ _ B) H17 H10
           ltac:(rewrite Ua; unfold page_size; exact Hal) H11 Hlen Hll ltac:(rewrite Ua; exact Hend) H12).
  - fold nW. unfold madvise_dontneed_ok. apply andb_true_intro. split; [apply andb_true_intro; split|].
    + rewrite (bi_resv _ _ _ _ B).
      replace nW with (Z_to_bv 64 (addr + len - addr)) by (unfold nW; f_equal; lia).
      apply region_free_resv_shadow; try lia. exact Hsh.
    + rewrite (bi_maps _ _ _ _ B).
      destruct (bs_shrw_entry STATIC addr (addr + len) ltac:(lia) Hsub) as (b & s & Hbs & B1 & B2).
      apply (map_contains_intro _ aW nW b s); [apply in_or_app; right; exact Hbs | rewrite Ua; exact B1 | rewrite Ua, Un; exact B2].
    + apply region_free_intro. intros b s Hbs. rewrite Ua, Un.
      pose proof (bi_noacc_pos _ _ _ _ B (b, s) Hbs) as Hsp. cbn [snd] in Hsp.
      destruct (bi_wf _ _ _ _ B) as (_ & Wn & _). pose proof (Wn (b, s) Hbs) as Hwf. unfold BA.iv_wf, BA.B, BA.S in Hwf. cbn [fst snd] in Hwf.
      destruct (Z_le_dec (addr + len) (bv_unsigned b)) as [L|L]; [left; exact L|].
      destruct (Z_le_dec (bv_unsigned b + bv_unsigned s) addr) as [R|R]; [right; exact R|]. exfalso.

      set (x := Z.max (bv_unsigned b) addr).
      assert (Hx : addr <= x < addr + len) by (unfold x; lia).
      assert (Hcov : BA.covered (vm_noaccess (m_vmmaps model)) x = true).
      { rewrite <- in_ivs_covered. apply in_ivs_true'. exists (b, s). split; [exact Hbs | cbn [fst snd]; unfold x; lia]. }
      pose proof (bi_noacc _ _ _ _ B x Hcov) as E'. rewrite (bs_shrw_acc STATIC x (Hsh x Hx)) in E'. discriminate.
  - fold nW. fold model'.
    apply HK; [exact B' | apply bmodel_rt_sbm; exact Hs | |].
    { split; [apply incl_refl|]. split; [|split; [|split]]; [| |intros w0 Hw0; left; exact Hw0 | intros x Hx; left; rewrite <- Hlz; exact Hx].
      - intros x Hx. rewrite EH in Hx. split; [exact Hx|]. apply zfill_out. rewrite Ua, Un.
        destruct (Z_lt_dec (bv_unsigned x) addr) as [L|L]; [left; exact L|].
        destruct (Z_le_dec (addr + len) (bv_unsigned x)) as [U|U]; [right; exact U|].
        exfalso. rewrite (Hvis x ltac:(lia)) in Hx. discriminate.
      - intros x Hx Hx'. rewrite EH, Hx in Hx'. discriminate. }
    rewrite EH. apply view_zfill; try lia.
    + exact Hvis.
    + intros a _. reflexivity.
Qed.

Lemma restrict_mkst : forall (H : word -> bool) regs pc M rom,
  restrict H (mkst regs pc M rom) = mkst regs pc (mrestrict H M) rom.
Proof. intros. reflexivity. Qed.

Definition art_ev_range (ev : aev) : Z * Z :=
  match ev with
  | AMmapFixed a l => (a, a + l) | AMmapFixedNR a l => (a, a + l) | AMunmap a l => (a, a + l) | AMadvise a l => (a, a + l)
  | AMmapNull len r => (art_shlo r, art_shhi r len)
  end.
Definition in_ev_ranges (sfx : list aev) (x : Z) : Prop :=
  exists ev, In ev sfx /\ fst (art_ev_range ev) <= x < snd (art_ev_range ev).
Definition bhist (A0 : list (Z * Z)) (M0 : word -> option byte) (model0 : Model) (log0 : list aev)
                 (log : list aev) (A : list (Z * Z)) (M : word -> option byte) (model : Model) : Prop :=
  exists sfx, log = log0 ++ sfx /\ incl A0 A
  /\ (forall x : word, bhid A model x = true -> bhid A0 model0 x = true /\ M x = M0 x)
  /\ (forall x : word, bhid A0 model0 x = true -> bhid A model x = false -> in_ev_ranges sfx (bv_unsigned x))
  /\ (forall w, In w A -> In w A0 \/ exists len r, In (AMmapNull len r) sfx /\ w = (art_shlo r, art_shhi r len))

  /\ (forall x : word, page_in_ranges (page_base x) (m_vm_lazy model) = true ->
        page_in_ranges (page_base x) (m_vm_lazy model0) = true
        \/ exists a l, In (AMmapFixedNR a l) sfx /\ a <= bv_unsigned x < a + l).

Lemma bhist_refl : forall A M model log, bhist A M model log log A M model.
Proof.
  intros A M model log. exists []. rewrite app_nil_r. split; [reflexivity|]. split; [apply incl_refl|]. split; [|split; [|split]].
  - intros x Hx. split; [exact Hx | reflexivity].
  - intros x Hx Hx'. rewrite Hx in Hx'. discriminate.
  - intros w Hw. left. exact Hw.
  - intros x Hx. left. exact Hx.
Qed.

Lemma bhist_step0 : forall A0 M0 model0 log0 log A M model M' model',
  bhist A0 M0 model0 log0 log A M model -> bstep A M model A M' model' 0 0 false ->
  bhist A0 M0 model0 log0 log A M' model'.
Proof.
  intros A0 M0 model0 log0 log A M model M' model' (sfx & El & Hi & H2 & H3 & H4 & H5) (S1 & S2 & S3 & _ & S5).
  exists sfx. split; [exact El|]. split; [exact Hi|]. split; [|split; [|split; [exact H4|]]].
  3:{ intros x Hx. destruct (S5 x Hx) as [Hl|[Hc _]]; [exact (H5 x Hl) | discriminate Hc]. }
  - intros x Hx. destruct (S2 x Hx) as [Hx1 E1]. destruct (H2 x Hx1) as [Hx0 E0]. split; [exact Hx0 | rewrite E1; exact E0].
  - intros x Hx0 Hx'. destruct (bhid A model x) eqn:E.
    + pose proof (S3 x E Hx'). lia.
    + exact (H3 x Hx0 E).
Qed.

Definition art_ev_nr (ev : aev) : bool := match ev with AMmapFixedNR _ _ => true | _ => false end.
Lemma bhist_step_same : forall A0 M0 model0 log0 log A M model M' model' ev,
  bhist A0 M0 model0 log0 log A M model ->
  bstep A M model A M' model' (fst (art_ev_range ev)) (snd (art_ev_range ev)) (art_ev_nr ev) ->
  bhist A0 M0 model0 log0 (log ++ [ev]) A M' model'.
Proof.
  intros A0 M0 model0 log0 log A M model M' model' ev (sfx & El & Hi & H2 & H3 & H4 & H5) (S1 & S2 & S3 & _ & S5).
  exists (sfx ++ [ev]). split; [rewrite El, app_assoc; reflexivity|]. split; [exact Hi|]. split; [|split; [|split]].
  4:{ intros x Hx. destruct (S5 x Hx) as [Hl|[Hc Hr]].
      - destruct (H5 x Hl) as [H0|(a & l & Hin & Hal)]; [left; exact H0|].
        right. exists a, l. split; [apply in_or_app; left; exact Hin | exact Hal].
      - right. destruct ev as [a l|len r|a l|a l|a l]; try discriminate Hc. cbn [art_ev_range fst snd] in Hr.
        exists a, l. split; [apply in_or_app; right; left; reflexivity | exact Hr]. }
  - intros x Hx. destruct (S2 x Hx) as [Hx1 E1]. destruct (H2 x Hx1) as [Hx0 E0]. split; [exact Hx0 | rewrite E1; exact E0].
  - intros x Hx0 Hx'. destruct (bhid A model x) eqn:E.
    + exists ev. split; [apply in_or_app; right; left; reflexivity | exact (S3 x E Hx')].
    + destruct (H3 x Hx0 E) as (e & He & Hr). exists e. split; [apply in_or_app; left; exact He | exact Hr].
  - intros w Hw. destruct (H4 w Hw) as [Hw0|(len & r & Hin & Ew)]; [left; exact Hw0|].
    right. exists len, r. split; [apply in_or_app; left; exact Hin | exact Ew].
Qed.

Lemma bhist_step_null : forall A0 M0 model0 log0 log A M model A' M' model' len r,
  bhist A0 M0 model0 log0 log A M model ->
  bstep A M model A' M' model' (art_shlo r) (art_shhi r len) false ->
  bhist A0 M0 model0 log0 (log ++ [AMmapNull len r]) A' M' model'.
Proof.
  intros A0 M0 model0 log0 log A M model A' M' model' len r (sfx & El & Hi & H2 & H3 & H4 & H5) (S1 & S2 & S3 & S4 & S5).
  exists (sfx ++ [AMmapNull len r]). split; [rewrite El, app_assoc; reflexivity|]. split; [exact (incl_tran Hi S1)|]. split; [|split; [|split]].
  4:{ intros x Hx. destruct (S5 x Hx) as [Hl|[Hc _]]; [|discriminate Hc].
      destruct (H5 x Hl) as [H0|(a & l & Hin & Hal)]; [left; exact H0|].
      right. exists a, l. split; [apply in_or_app; left; exact Hin | exact Hal]. }
  - intros x Hx. destruct (S2 x Hx) as [Hx1 E1]. destruct (H2 x Hx1) as [Hx0 E0]. split; [exact Hx0 | rewrite E1; exact E0].
  - intros x Hx0 Hx'. destruct (bhid A model x) eqn:E.
    + exists (AMmapNull len r). split; [apply in_or_app; right; left; reflexivity | exact (S3 x E Hx')].
    + destruct (H3 x Hx0 E) as (e & He & Hr). exists e. split; [apply in_or_app; left; exact He | exact Hr].
  - intros w Hw. destruct (S4 w Hw) as [HwA|Ew].
    + destruct (H4 w HwA) as [Hw0|(len' & r' & Hin & Ew)]; [left; exact Hw0|].
      right. exists len', r'. split; [apply in_or_app; left; exact Hin | exact Ew].
    + right. exists len, r. split; [apply in_or_app; right; left; reflexivity | exact Ew].
Qed.

Theorem aruns_srealizes_h : forall (Q : list aev -> machine_state -> Prop) K model0 A0 M0 modelE log0,
  (forall log A ms model, BInv log A (ms_mem ms) model -> bmodel_rt model0 model ->
     bhist A0 M0 modelE log0 log A (ms_mem ms) model ->
     Q log (restrict (bhid A model) ms) -> srealizes segs scfg (mkCfg ms model) K) ->
  forall log s, aruns segs EVOK GR Q log s ->
  forall A ms model, restrict (bhid A model) ms = s -> BInv log A (ms_mem ms) model -> bmodel_rt model0 model ->
  bhist A0 M0 modelE log0 log A (ms_mem ms) model ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros Q K model0 A0 M0 modelE log0 HQ log s R. induction R as
    [ log s Hq
    | log s s' MS R IH
    | log regs pc pc' M rom addr len Hpc Epc Hargs Hev R IH
    | log regs pc pc' M rom len Hpc Epc Hargs Hev R IH
    | log regs pc pc' M rom addr len Hpc Epc Hargs Hev R IH
    | log regs pc pc' M rom addr len Hpc Epc Hargs Hev R IH
    | log regs pc pc' M rom addr len Hpc Epc Hargs Hev R IH ];
    intros A ms model Es B Hrt HH.
  - apply (HQ log A ms model B Hrt HH). rewrite Es. exact Hq.
  - subst s. apply (bridge_msteps log A ms model s' K B MS).
    intros ms' model' Es' B' Hrt' HST.
    exact (IH A ms' model' Es' B' (bmodel_rt_trans _ _ _ Hrt Hrt') (bhist_step0 _ _ _ _ _ _ _ _ _ _ HH HST)).
  - destruct (restrict_eq_mkst _ _ _ _ _ _ Es) as [Ems EM]. rewrite Ems. rewrite Ems in B, HH. cbn [ms_mem mkst] in B, HH.
    subst pc'. apply (bridge_fixed log A regs pc (ms_mem ms) rom model addr len K); try assumption.
    intros M' model' B' Hrt' HST Hview.
    apply (IH A (mkst (regupd regs 10 (Z_to_bv 64 addr)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model').
    + rewrite restrict_mkst, Hview, <- EM. reflexivity.
    + exact B'.
    + exact (bmodel_rt_trans _ _ _ Hrt Hrt').
    + exact (bhist_step_same _ _ _ _ _ _ _ _ _ _ (AMmapFixed addr len) HH HST).
  - destruct (restrict_eq_mkst _ _ _ _ _ _ Es) as [Ems EM]. rewrite Ems. rewrite Ems in B, HH. cbn [ms_mem mkst] in B, HH.
    subst pc'. apply (bridge_null log A regs pc (ms_mem ms) rom model len K); try assumption.
    intros r A' M' model' HGR B' Hrt' HST Hview.
    apply (IH r ltac:(rewrite EM; exact HGR) A' (mkst (regupd regs 10 (Z_to_bv 64 r)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model').
    + rewrite restrict_mkst, Hview, <- EM. reflexivity.
    + exact B'.
    + exact (bmodel_rt_trans _ _ _ Hrt Hrt').
    + exact (bhist_step_null _ _ _ _ _ _ _ _ _ _ _ len r HH HST).
  - destruct (restrict_eq_mkst _ _ _ _ _ _ Es) as [Ems EM]. rewrite Ems. rewrite Ems in B, HH. cbn [ms_mem mkst] in B, HH.
    subst pc'. apply (bridge_fixed_nr log A regs pc (ms_mem ms) rom model addr len K); try assumption.
    intros M' model' B' Hrt' HST Hview.
    apply (IH A (mkst (regupd regs 10 (Z_to_bv 64 addr)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model').
    + rewrite restrict_mkst, Hview, <- EM. reflexivity.
    + exact B'.
    + exact (bmodel_rt_trans _ _ _ Hrt Hrt').
    + exact (bhist_step_same _ _ _ _ _ _ _ _ _ _ (AMmapFixedNR addr len) HH HST).
  - destruct (restrict_eq_mkst _ _ _ _ _ _ Es) as [Ems EM]. rewrite Ems. rewrite Ems in B, HH. cbn [ms_mem mkst] in B, HH.
    subst pc'. apply (bridge_munmap log A regs pc (ms_mem ms) rom model addr len K); try assumption.
    intros M' model' B' Hrt' HST Hview.
    apply (IH A (mkst (regupd regs 10 (Z_to_bv 64 0)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model').
    + rewrite restrict_mkst, Hview, <- EM. reflexivity.
    + exact B'.
    + exact (bmodel_rt_trans _ _ _ Hrt Hrt').
    + exact (bhist_step_same _ _ _ _ _ _ _ _ _ _ (AMunmap addr len) HH HST).
  - destruct (restrict_eq_mkst _ _ _ _ _ _ Es) as [Ems EM]. rewrite Ems. rewrite Ems in B, HH. cbn [ms_mem mkst] in B, HH.
    subst pc'. apply (bridge_madvise log A regs pc (ms_mem ms) rom model addr len K); try assumption.
    intros M' model' B' Hrt' HST Hview.
    apply (IH A (mkst (regupd regs 10 (Z_to_bv 64 0)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model').
    + rewrite restrict_mkst, Hview, <- EM. reflexivity.
    + exact B'.
    + exact (bmodel_rt_trans _ _ _ Hrt Hrt').
    + exact (bhist_step_same _ _ _ _ _ _ _ _ _ _ (AMadvise addr len) HH HST).
Qed.

Theorem aruns_srealizes : forall (Q : list aev -> machine_state -> Prop) K model0,
  (forall log A ms model, BInv log A (ms_mem ms) model -> bmodel_rt model0 model ->
     Q log (restrict (bhid A model) ms) -> srealizes segs scfg (mkCfg ms model) K) ->
  forall log s, aruns segs EVOK GR Q log s ->
  forall A ms model, restrict (bhid A model) ms = s -> BInv log A (ms_mem ms) model -> bmodel_rt model0 model ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros Q K model0 HQ log s R A ms model Es B Hrt.
  apply (aruns_srealizes_h Q K model0 A (ms_mem ms) model log (fun log' A' ms' model' B' Hrt' _ Hq => HQ log' A' ms' model' B' Hrt' Hq)
           log s R A ms model Es B Hrt). apply bhist_refl.
Qed.

Lemma binv_ext : forall log A M m1 m2,
  BInv log A M m1 -> m_vmmaps m2 = m_vmmaps m1 -> m_vm_lazy m2 = m_vm_lazy m1 ->
  m_halted m2 = None -> MInv A m2 -> BInv log A M m2.
Proof.
  intros log A M m1 m2 B Hvm Hlz Hh Hminv.
  assert (Heu : eager_used m2 = eager_used m1) by (apply eager_used_ext; assumption).
  assert (EH : bhid A m2 = bhid A m1) by (unfold bhid; rewrite Hlz; reflexivity).
  destruct B. constructor; rewrite ?Hvm, ?Hlz, ?Heu, ?EH; try assumption.
  destruct bi_wf0 as (W1 & W2 & W3 & W4). unfold BA.model_ivs_wf. rewrite Hvm, Hlz. repeat split; assumption.
Qed.

Definition BINV (log : list aev) (A : list (Z * Z)) (M : word -> option byte) (h : VmMaps) (lz : list (word * word)) : Prop :=
  A_wf A /\ live_ok (art_live log)
  /\ forall model, m_vmmaps model = h -> m_vm_lazy model = lz -> m_halted model = None -> MInv A model -> BInv log A M model.

Lemma BINV_elim : forall log A M model,
  BINV log A M (m_vmmaps model) (m_vm_lazy model) -> m_halted model = None -> MInv A model -> BInv log A M model.
Proof. intros log A M model (_ & _ & H) Hh Hm. exact (H model eq_refl eq_refl Hh Hm). Qed.

Lemma BINV_intro : forall log A M model,
  BInv log A M model -> BINV log A M (m_vmmaps model) (m_vm_lazy model).
Proof.
  intros log A M model B. split; [exact (bi_awf _ _ _ _ B)|]. split; [exact (bi_live _ _ _ _ B)|].
  intros m2 Hvm Hlz Hh Hm. exact (binv_ext log A M model m2 B Hvm Hlz Hh Hm).
Qed.

Lemma BINV_awf : forall log A M h lz, BINV log A M h lz -> A_wf A.
Proof. intros log A M h lz (H & _). exact H. Qed.
Lemma BINV_live : forall log A M h lz, BINV log A M h lz -> live_ok (art_live log).
Proof. intros log A M h lz (_ & H & _). exact H. Qed.

End Bridge.
End ArtBridge.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.
Module DrvNodesLazyK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.AllocSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.AgentNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.SpecConsts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.LazyFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.LibWritev OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.LibWritevX.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_DrvNodesLazyK () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List:fold_rightC46Stdlib5Lists4List7existsbC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appc59OSSVerify5KrLib7Mh_01099KitNodesS?node_chk_ev_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg7node_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099KitNodesSEnode_chk_ev_gen_noaccC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00c59OSSVerify5KrLib7Mh_0109>AsanNodesLibEKAnode_chk_ev_noaccC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109>AsanNodesLibEK>node_chk_noaccC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109>AsanNodesLibEK9srz_casesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg5t_altC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg8srz_nodeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg8wr_indexC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlgFnode_ok_of_pnode_sysnoC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5Nodes6open_IC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg@node_ok_of_pnodeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib7Mh_0109>AsanNodesLibEK8Some_injC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes5tid_IC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:concat_mapC46Stdlib5Lists4List7map_mapc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKFA_bytes_flat_map_splitC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibKAin_flat_map_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK>filter_map_extC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9fold_leftc59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9srz_node1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK8some_injC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01099ArtBridge?filter_all_trueC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK:nolazy_rngC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib5Lists4List2InK47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z6of_natc59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK:acc_nolazyC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00C46Stdlib5Lists4List9in_app_orc59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK>nolazy_rng_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK>acc_nolazy_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK?acc_nolazy_consC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingC59OSSVerify5KrLib7Mh_00379LazyFrameBwith_vm_backing_idC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5StateDmaterialize_accessesC4ELinuxProcessSemantics?LinuxProcessSem5State>accesses_pagesC59OSSVerify5KrLib7Mh_00379LazyFrameAaccesses_pages_inC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltI47Corelib4Init5Logic2ex00C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib7Mh_00379LazyFrame@filter_all_falseC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateHnewly_materialized_pagesC59OSSVerify5KrLib7Mh_00379LazyFrameKmaterialize_accesses_no_newC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem5State8page_memC47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC47Corelib4Init9Datatypes4andbC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith4Znat5Nat2Z6inj_ltI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00C4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0094:AgentNodes5ependC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK47Corelib4Init5Logic4True01I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics5Riscv3Sem4core00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKFstepacc_ecall_epend_lzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00379LazyFrameDaccess_outside_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00379LazyFrameEaccesses_outside_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlgAsrz_step_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputK4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesc59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK@mat_id_of_nolazyC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg04C59OSSVerify5KrLib7Mh_00368ShapeAlgCsstep_cfg_svc_casesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic9False_indI4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00C59OSSVerify5KrLib7Mh_00368ShapeAlg7halt_evC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specK4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcK4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I47Corelib4Init5Logic4True00c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK<node_svc_matC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecs=check_syscallK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecsDcheck_syscall_ok_iffK47Corelib4Init5Logic2or01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecsEcheck_syscall_err_iffI6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03I4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK?node_chk_ev_matC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib4Init5Logic5proj2C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem3Run9refusal_bC49OSSVerify5KrLib5NodesDuniform_not_spuriousC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeEcheck_ret_only_ok_iffC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeKcheck_ret_only_no_unmodeledc59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK<node_det_matC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSimEapply_effect_no_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg;srz_silent1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeFcheck_ret_only_copyinsC4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeMcheck_ret_only_copyins_ok_iffC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeScheck_ret_only_copyins_no_unmodeledC4ELinuxProcessSemantics?LinuxProcessSem5State;eff_copyinsC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_writesC4ELinuxProcessSemantics?LinuxProcessSem5State>write_accessesC59OSSVerify5KrLib7Mh_00306CatSimMapply_effect_copyins_no_writeC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep04C59OSSVerify5KrLib7Mh_00437FileSimIcheck_open_result_copyinsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State8alloc_fdC59OSSVerify5KrLib7Mh_00264Scfg6fam_onC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5Nodes7open_nxC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00I47Corelib4Init6Specif3sig00K47Corelib4Init9Datatypes3sum01C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC59OSSVerify5KrLib7Mh_00437FileSimPcheck_open_result_copyins_ok_iffC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKIaccesses_with_copyins_retC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKBsstep_of_check_matC1?~~~~~~~~~~~~~~~K47Corelib4Init6Specif3sig01K47Corelib4Init9Datatypes3sum02K47Corelib4Init5Logic2or02C49OSSVerify5KrLib5Nodes=sstep_svc_invC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib7Mh_00437FileSimYcheck_open_result_copyins_never_unmodeledC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open=openat_errnosI47Corelib4Init9Datatypes3sum00c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK<node_open_lzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg8srz_alt2C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC59OSSVerify5KrLib7Mh_00437FileSimGENOMEM_in_openat_errnosC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_removeC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall4fd32C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs4Open;check_closeC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall7fd32_idC59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim@check_syscall_57C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes@with_fds_halted'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0094:AgentNodes=adv_set_ependC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKErz_ret_only_silent_lzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK:srz_sys_lzC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5EBADFC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5cmd32C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs5Ioctl;check_ioctlK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry03K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry04K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry05K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry07K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry08K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry09C59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes@check_syscall_29C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Ioctl@tty_only_requestC4ELinuxProcessSemantics?LinuxProcessSem5State6ENOTTYK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06I4ELinuxProcessSemantics?LinuxProcessSem5State9SockState00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry0:C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWrite:check_readC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C4ELinuxProcessSemantics?LinuxProcessSem5State7m_stdinC4ELinuxProcessSemantics?LinuxProcessSem5State7in_wmemC4ELinuxProcessSemantics?LinuxProcessSem5State>read_bytes_mapC4ELinuxProcessSemantics?LinuxProcessSem5State>rw_count_clampC4ELinuxProcessSemantics?LinuxProcessSem5State=stream_take_zC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z3lebC4ELinuxProcessSemantics?LinuxProcessSem5State;stream_takeC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude9listN_eqbC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude7wmem_okC47Corelib4Init9Datatypes3sndC4ELinuxProcessSemantics?LinuxProcessSem5State:with_stdinK4ELinuxProcessSemantics?LinuxProcessSem5State5event01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC45stdpp9bitvector;definitions6bv_addC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7UaccessDcheck_access_ok_zeroC4ELinuxProcessSemantics?LinuxProcessSem5State:net_take_zC4ELinuxProcessSemantics?LinuxProcessSem5State8net_takeK4ELinuxProcessSemantics?LinuxProcessSem5State9SockState04C4ELinuxProcessSemantics?LinuxProcessSem5State7m_pipesC4ELinuxProcessSemantics?LinuxProcessSem5State;pipe_lookupC4ELinuxProcessSemantics?LinuxProcessSem5State=pipe_end_liveC4ELinuxProcessSemantics?LinuxProcessSem5State9pipe_takeC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@delivered_writesC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:writes_eqbC4ELinuxProcessSemantics?LinuxProcessSem5State<pipe_consumeC4ELinuxProcessSemantics?LinuxProcessSem5State;pipe_insertC4ELinuxProcessSemantics?LinuxProcessSem5State:with_pipesC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWriteBcheck_read_urandomC4ELinuxProcessSemantics?LinuxProcessSem5State:access_okbC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC47Corelib4Init5Logic5proj1C59OSSVerify5KrLib7Mh_00948RefNodesCaccess_okb_intro_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0094:AgentNodes=ms_gpr_epend2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim@check_syscall_63C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9file_readC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@modeled_rw_rangeC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWriteJcheck_socket_pending_errorC4ELinuxProcessSemantics?LinuxProcessSem5State:ECONNRESETC4ELinuxProcessSemantics?LinuxProcessSem5State9ETIMEDOUTC4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEC4ELinuxProcessSemantics?LinuxProcessSem5State6EISDIRC4ELinuxProcessSemantics?LinuxProcessSem5State6EFAULTI4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02C4ELinuxProcessSemantics?LinuxProcessSem5State8ENOTCONNI4ELinuxProcessSemantics?LinuxProcessSem5State9NetStream00C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK>rz_read_dir_lzC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_00438AgentLibJread_bytes_map_of_store_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC56Stdlib6ZArith4Znat5Z2Nat2idC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@ms_writable_byteC59OSSVerify5KrLib7Mh_0094:AgentNodesFms_writable_byte_ependC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes?read_file_checkC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC47Corelib4Init3Nat3subC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC59OSSVerify5KrLib7Mh_00437FileSim@length_file_readC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK>acc_nolazy_oneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK@with_fds_vm_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes=adv_ret_ependC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes@adv_write1_ependC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK9rz_det_lzC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega=RingMicromega3Op201C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z7inj_minC4ELinuxProcessSemantics?LinuxProcessSem5StateCcstr_access_len_auxI47Corelib4Init5Peano2le00C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z8inj_succC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<ms_read_bytec59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKFcstr_access_len_aux_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim<open_copyinsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8path_maxC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:rdn_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSimHread_cstr_toolong_of_rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim3mrbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9read_cstrC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude=clear_copyinsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs4Open@check_openat_sepC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open>path_is_dirrefC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs4OpenAcheck_open_resultC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeCcheck_copyins_afterC59OSSVerify5KrLib7Mh_00437FileSimLcheck_copyins_after_ret_onlyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodesAopenat_check_headC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKMrz_ret_only_copyins_silent_lzC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<ENAMETOOLONGI4ELinuxProcessSemantics?LinuxProcessSem5State;cstr_result00K4ELinuxProcessSemantics?LinuxProcessSem5State;cstr_result02C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOENTc59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKCopen_copyins_nolazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes7path_atC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State;cstr_result01C59OSSVerify5KrLib7Mh_00948RefNodes<path_at_cstrC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenAopenat_plain_nameC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenJopenat_plain_name_nodirrefC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenIopenat_plain_name_noslashC59OSSVerify5KrLib7Mh_00437FileSim<path_eqb_neqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodesOcheck_copyins_after_open_resultC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenGpath_is_dirref_no_slashC59OSSVerify5KrLib7Mh_00948RefNodes@fam_on_openat_msC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK:rz_open_lzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKCrz_openat_dirref_lzC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi8dot_pathC56Stdlib6ZArith6BinInt1Z3mulC4ELinuxProcessSemantics?LinuxProcessSem5StateDcopy_iovecs_accessesC4ELinuxProcessSemantics?LinuxProcessSem5State@read_iovec_entryC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C45stdpp9bitvector;definitions7bv_wrapK46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions?bv_add_unsignedI46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr05I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C46Stdlib9micromega;ZifyClasses3injC46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterI4ELinuxProcessSemantics?LinuxProcessSem5State9iov_entry00I46Stdlib;setoid_ring<Ring_polynom3Mon00C56Stdlib6ZArith4Znat5Nat2Z2idC56Stdlib6ZArith6BinInt1Z3ltbC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKKcopy_iovecs_accesses_nolazyC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateFimport_iovecs_accessesC4ELinuxProcessSemantics?LinuxProcessSem5State7IOV_MAXC4ELinuxProcessSemantics?LinuxProcessSem5StateCiov_prefix_accessesC4ELinuxProcessSemantics?LinuxProcessSem6BvBaseCword_to_nat_boundedC56Stdlib5Arith8PeanoNat3Nat3eqbC4ELinuxProcessSemantics?LinuxProcessSem6BvBaseJword_to_nat_bounded_eq_minC59OSSVerify5KrLib7Mh_00949LibWritev9iov_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00949LibWritev;iov_bufs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00949LibWritev8iov_bufsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6concatC4ELinuxProcessSemantics?LinuxProcessSem5State:iovs_totalC59OSSVerify5KrLib7Mh_0094:LibWritevX=writev_checkXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKMimport_iovecs_accesses_nolazyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKJiov_prefix_accesses_nolazyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK>acc_nolazy_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg7wr_fullC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?addr_is_error_bC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeAaccess_ranges_eqbC56Stdlib6ZArith6BinInt1Z6ltb_geK46Stdlib9micromega7EnvRing5PExpr04C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeDaccess_ranges_eqb_eqC56Stdlib6ZArith6BinInt1Z6leb_leK4ELinuxProcessSemantics?LinuxProcessSem5State5event02C57Corelib7BinNums6PosDef3Pos6to_natC46Stdlib4Bool4Bool=andb_true_iffC59OSSVerify5KrLib7Mh_00949LibWritev>u64_roundtrip'C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib4Init6Specif9proj1_sigI4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C59OSSVerify5KrLib7Mh_00264Scfg?injected_arm_66C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib7Mh_00385Hoare3at_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare5at_atC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyKDrz_writev_pending_lzC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC47Corelib5Lists7ListDef5skipnC47Corelib4Init3Nat3addc59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK=rz_writev2_lzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00949LibWritev7rz_wallC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK=rz_writev1_lzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg:t_write_chC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State:iov_import01C4ELinuxProcessSemantics?LinuxProcessSem5State?copy_iovecs_auxC4ELinuxProcessSemantics?LinuxProcessSem5State?iovs_access_okbK4ELinuxProcessSemantics?LinuxProcessSem5State9iov_entry01C59OSSVerify5KrLib7Mh_00949LibWritev@access_okb_of_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00949LibWritevIread_iovec_entry_of_arrayC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State=import_iovecsC4ELinuxProcessSemantics?LinuxProcessSem5State6in_argC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs9ReadWrite<check_writevC4ELinuxProcessSemantics?LinuxProcessSem5State6in_memC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite8iovcnt32C4ELinuxProcessSemantics?LinuxProcessSem5State:cap_iovecsC4ELinuxProcessSemantics?LinuxProcessSem5State?writev_gatheredC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite>rw_pos_einvalbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite@modeled_file_gapC4ELinuxProcessSemantics?LinuxProcessSem2Fs:file_writeC4ELinuxProcessSemantics?LinuxProcessSem2Fs6fs_setC4ELinuxProcessSemantics?LinuxProcessSem5State7with_fsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs9ReadWrite>append_new_posC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall9w_is0_posC56Stdlib6ZArith6BinInt1Z5min_rC4ELinuxProcessSemantics?LinuxProcessSem5State>cap_iovecs_auxC59OSSVerify5KrLib7Mh_00437FileSim9in_mem_siC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim:in_arg2_siC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim:in_arg1_siC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00437FileSim:in_arg0_siC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoC59OSSVerify5KrLib7Mh_00437FileSim;in_sysno_siC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00949LibWritevDcheck_syscall_writevC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State:iov_import00K4ELinuxProcessSemantics?LinuxProcessSem5State:iov_import02C4ELinuxProcessSemantics?LinuxProcessSem5State<MAX_RW_COUNTK4ELinuxProcessSemantics?LinuxProcessSem5State:iov_import03C4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALC45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib7Mh_00368ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00307ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg8srz_exitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0109=DrvNodesLazyK=rz_exit_at_lzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0094:AgentNodes@bv_and_255_smallC1?~~~~~~~~~~~~~~~".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Common.Cfg Require RomBase.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nolazy_rng (L : list (word * word)) (a : word) (n : Z) : Prop :=
  forall k, (0 <= k < n)%Z -> page_in_ranges (page_base_of (bv_unsigned a + k)) L = false.

Definition acc_nolazy (L : list (word * word)) (accs : list (word * nat)) : Prop :=
  forall a n, In (a, n) accs -> nolazy_rng L a (Z.of_nat n).

Lemma nolazy_rng_sub : forall L a n m, nolazy_rng L a n -> (m <= n)%Z -> nolazy_rng L a m.
Proof.
ltac2:(KReplay.run1 (kr_t_DrvNodesLazyK ()) [] "h04__x1h14__x2h24__x3h31Hh42H0h52H1h62Hkh72Hmh81Lh97__arithh:4__ffh;8__varmaph<5__with=1ah>1kh?1mh@1np;1p;2p;3p;4p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp4p76111110p100;1p4p741110R<p8p100;np4p76111110R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp4p76111110R>P=p8P>P<p8p100@:p4p76111110R=P>p8P=P<p8p100ADp4p741110R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p4p710RAP8p8PAP9p8p100J<p4p70RAP=p8PAP>p8PAP?p8PAP<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p100L2p4p710R7p100MEp4p710RAp8P7P;p8P7P5p8P7P0p8p100MgR7p4p710R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p4p7210R7P1p8P7P4p8p100O5R4p4p710R7P1p8P7P3p8P7PAp8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100P@p4p710P6p8P0P6p8p100P^p4p741110R6P?p8P6P<p8P6P@p8p100Qdp4p710R@P8p8P@P9p8p100Rip4p710R9P1p8P9p100SoR1p4p710p8P9P1p4p7210p8P9PAp8P9P0p8g00TLj10Tg00U1j1RTg00UOj1ETg00V2j2ATg00VRj1=Tg00W2j3;Tg00X7j21Tg00XSj22Tg00XoR0j26Tg00YJj15Tg00Yij27Tg00ZRj3<Tg00[;j2>Tg00[gj1QTg00\Gj3PTg00\gj2:Tg00]Ej4OTg00]cj1NTg00^Aj1KTg00^lj29Tg00_Oj1GTg00`4j44Tg00`_j1DTg00aAj2FTg00adj7CTg00bHj2HTg00bjj2BTg00cDj2ITg00d0j3JTg00dJj3@Tg00dij4LTg00e[j7MTg00f?j8?Tf1R9g00fcRAg00gBR1P1g00gbR@f0R8g00hBFMp=3f3R6PAP1P1P@f2R<P9P8G?p=8g00hbR?#0R4#0#0#0#0#0#R#ER2/A2#=g00iGR7A;6<9119<g00ieR3/181286'6P6P9P01139R0f4R>,29113<f6R5,2<'6P81136R;f7R:,2>g00jCR=g00joRB#5RC#5#5,77177C177B5<75<7g00kN'>%Q=3P%==P71:7<P91:76CO%N7%K7R=P7197?RBg00l:RC%G?,97R?C4,3=%D1RDP=P71F73g00laREPBC4,3=RFPDP=P7P?PE1974R4C4,3=PDP=PAP1P1P@PFP7PBPCP4C4,3=FCC8C8C81H=@P8P<g00mHR=g00mhR@'B1I8<=J=@dA@739CLb:b;b<X07X17X27128<11>6126>,6;[\0[^07^17^27P8f9f:P5P9P<P:O6b9W5W4P9P8O2n2001000000121000000O2W6X>7f5?;><eW7W3X?7W@X=2W8o"). Qed.

Lemma acc_nolazy_nil : forall L, acc_nolazy L [].
Proof.
ltac2:(KReplay.run1 (kr_t_DrvNodesLazyK ()) [] "h01Hh11Lh21ah31np;1p;2p;4p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0g00nHR1p4p710R2p8P0p1002lR3p4p710R4p8P0P3p4p7210R3p8P0p1003Hp4p710p8P0p1003iR5p4p710p8P0P5p4p7210p8P0p1004FR5p4p710R6p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R7p1006Np4p710R8p8P7p1006jp4p710R9p8P7p1007Hp4p7210R:p8P7p1007ep4p710R7p8p1008Cp4p710R;P8p8P;P7p8p1008`p4p70R<P3p8P<P8p8P<P9p8P<P:p8P<P7p8P<p1009Np4p710R<p8p1009kp4p76111110p100;1p4p741110R=p8p100;np4p76111110R>P=p8p100=:p4p7210R?P8p8P?P9p8P?P:p8P?P7p8P?p100=fp4p710p8p100>mp4p76111110R?P>p8P?P=p8p100@:p4p76111110R>P?p8P>P=p8p100ADp4p741110R?p100BIp4p710R@p8P?P=p8P?p100CDp4p7511110RAp8p100DAp4p711RBP@p8PBp100E?p4p771111110p8PBPAp8p100FKp4p711RBP=p8PBp100G<p4p741110p8p100HBp4p70RBP8p8PBP9p8PBP:p8PBP7p8p100I8p4p710RBP9p8PBP:p8p100J<p4p70RBP>p8PBP?p8PBP@p8PBP=p8P5p4p7210R5P8p8P5P7p8p100K7p4p7210P7p8p100KVp4p73110P7p8p100L2p4p710R8p100MEp4p710RBp8P8P<p8P8P6p8P8P0p8p100MgR8p4p710R?P2p8P?P;p8P?P<p8P?P6p8P?P0p8P8p4p7210R8P2p8P8P5p8p100O5R5p4p710R8P2p8P8P4p8P8PBp8P8P0p8P5p4p7210R5P3p8P5P7p8P5P0p8p100P@p4p710P7p8P0P7p8p100P^p4p741110R7P@p8P7P=p8P7PAp8p100Qdp4p710RAP9p8PAP:p8p100Rip4p710R:P2p8P:p100SoR2p4p710p8P:P2p4p7210p8P:PBp8P:P0p8g00TLj10Tg00U1j1:Tg00UOj13Tg00V2j21Tg00VRj19Tg00n_j48Tg00[gj17TP1j34Tg00o?j15Tg00W2j36Tg00o_j22Tg00hb#0#0#0#0#0#0#:#3R1/11#9g010dR01110R:P1P0f1f0R0C8%7:R:34g011Cf4f3f2#536P0n010000000W0W3X21120:eW1o"). Qed.

Lemma acc_nolazy_cons : forall L a n accs, nolazy_rng L a (Z.of_nat n) -> acc_nolazy L accs -> acc_nolazy L ((a, n) :: accs).
Proof.
ltac2:(KReplay.run1 (kr_t_DrvNodesLazyK ()) [] "p'0h01Hh12a'h21eh32n'h41Eh52H1h62H2h73Hinh81Lh91ah:4accsh;1ni001ni011bi021pp;1p;2p;3p;6p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0g00nHR1p4p710R2p8P0p1002lR3p4p710R4p8P0P3p4p7210R3p8P0p1003Hp4p710p8P0p1003iR5p4p710p8P0P5p4p7210p8P0p1004FR5p4p710R6p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R7g006NR8p4p710R9p8P7g007HR:p4p710R;p8P7P:p4p7210R<p8P7p1007ep4p710R7p8p1008Cp4p710R=P9p8P=P7p8p1008`p4p70R>P3p8P>P9p8P>P;p8P>P<p8P>P7p8P>p1009Np4p710R>p8p1009kp4p76111110p100;1p4p741110R?p8p100;np4p76111110R@P?p8p100=:p4p7210RAP9p8PAP;p8PAP<p8PAP7p8PAp100=fp4p710p8p100>mp4p76111110RAP@p8PAP?p8p100@:p4p76111110R@PAp8P@P?p8p100ADp4p741110RAp100BIp4p710RBp8PAP?p8PAp100CDp4p7511110RCp8p100DAp4p711RDPBp8PDp100E?p4p771111110p8PDPCp8p100FKp4p711RDP?p8PDp100G<p4p741110p8p100HBp4p70RDP9p8PDP;p8PDP<p8PDP7p8p100I8p4p710RDP;p8PDP<p8p100J<p4p70RDP@p8PDPAp8PDPBp8PDP?p8P5p4p7210R5P9p8P5P7p8p100K7p4p7210P7p8p100KVp4p73110P7p8p100L2p4p710R9p100MEp4p710RDp8P9P>p8P9P6p8P9P0p8p100MgR9p4p710RAP2p8PAP=p8PAP>p8PAP6p8PAP0p8P9p4p7210R9P2p8P9P5p8p100O5R5p4p710R9P2p8P9P4p8P9PDp8P9P0p8P5p4p7210R5P3p8P5P7p8P5P0p8p100P@p4p710P7p8P0P7p8p100P^p4p741110R7PBp8P7P?p8P7PCp8p100Qdp4p710RCP;p8PCP<p8p100Rip4p710R<P2p8P<p100SoR2p4p710p8P<P2p4p7210p8P<PDp8P<P0p8g00TLj12Tg00U1j1>Tg00UOj1<Tg00V2R0j26Tg00VRj1:Tg00o?j14Tg00W2j33Tg00o_j28Tg00\Gj37TP1j35Tg00d0j31TP:j69TP8j6;Tg00n_j4=Tf2R8g010dR:f1R1f0R<C=p=0g00hb#2#2#2#2#2#2#>#<RD/6D#:16D:R2#:f3RC%41738f4R;/81A0D1<f6R7f5R?50D=72;552g011`f7RB=0D7A0D81R5512A525?f9R5%4873CP<f8R3=0DBA0DC8R9512P2P:P0PDP:P:P<P<n2001102000120101100X22A0D53A0D;CR4P<E9A1:3CP2PDP0PDP:PDP<P1n2001102000120101100X22f:R0=0D5A0D?;P1E9A1D0?f;R5=1D7PDf<RAA1:ABf?R6%43731[X1DA1:57P:PAf>%4<536X3:P0PBP<E;W0PBP<E;W0P<O1b0P<O1b0W4P<O1A5297P?P;PCP<O3W7P<O1n200100000021100010000W0X3:X1DA7248,8?eW6W5W:X;:X9DW8o"). Qed.

Lemma acc_nolazy_app : forall L l1 l2, acc_nolazy L l1 -> acc_nolazy L l2 -> acc_nolazy L (l1 ++ l2).
Proof.
ltac2:(KReplay.run1 (kr_t_DrvNodesLazyK ()) [] "h03Hinh12H1h22H2h31Lh41ah52l1h62l2h71np;1p;2p;4p;3p;5p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0g00nHR1p4p710R2p8P0p1002lR3p4p710R4p8P0P3p4p7210R3p8P0p1003Hp4p710p8P0p1003iR5p4p710p8P0P5p4p7210p8P0p1004FR5p4p710R6p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R7p1006Np4p710R8p8P7p1006jp4p710R9p8P7p1007Hp4p7210R:p8P7p1007ep4p710R7p8g012:R;p4p710R<P8p8P<P7p8p1008`p4p70R=P3p8P=P8p8P=P9p8P=P:p8P=P7p8P=g009NR=p4p710R>p8p1009kp4p76111110p100;1p4p741110R?p8p100;np4p76111110R@P?p8p100=:p4p7210RAP8p8PAP9p8PAP:p8PAP7p8PAp100=fp4p710p8p100>mp4p76111110RAP@p8PAP?p8p100@:p4p76111110R@PAp8P@P?p8p100ADp4p741110RAp100BIp4p710RBp8PAP?p8PAp100CDp4p7511110RCp8p100DAp4p711RDPBp8PDp100E?p4p771111110p8PDPCp8p100FKp4p711RDP?p8PDp100G<p4p741110p8p100HBp4p70RDP8p8PDP9p8PDP:p8PDP7p8p100I8p4p710RDP9p8PDP:p8p100J<p4p70RDP@p8PDPAp8PDPBp8PDP?p8P5p4p7210R5P8p8P5P7p8p100K7p4p7210P7p8p100KVp4p73110P7p8p100L2p4p710R8p100MEp4p710RDp8P8P>p8P8P6p8P8P0p8p100MgR8p4p710RAP2p8PAP<p8PAP>p8PAP6p8PAP0p8P8p4p7210R8P2p8P8P5p8p100O5R5p4p710R8P2p8P8P4p8P8PDp8P8P0p8P5p4p7210R5P3p8P5P7p8P5P0p8p100P@p4p710P7p8P0P7p8p100P^p4p741110R7PBp8P7P?p8P7PCp8p100Qdp4p710RCP9p8PCP:p8p100Rip4p710R:P2p8P:p100SoR2p4p710p8P:P2p4p7210p8P:PDp8P:P0p8g00TLj11Tg00U1j1<Tg00UOj1;Tg00V2j25Tg00VRj16Tg00o_j23Tg00n_j42TP=j34TP1j30TP;j5:Tg011`R;j27Tg00o?j18Tg00W2j39Tg00hb#1#1#1#1#1#1#<#;R1/51#6g010dR=,51R0#6R:f2RDf1R2'3f3RC/32P1P=P2f0R9C2f5R7f4R?540500P0f6RBP7P1P=PDP2C2R2P9D:A002BA0027'7P;P1P=PCPDC2R;f7R2500A00;Bf9%8C79?P9P1P=P?PCC2R;f8500P2P7P?P9O3W0P9O1A00;2PBP7P?P9O3W0P9O1n200100000021000010000b0W0X7=X41A40CD,3?eW2W1X6:W5W3o"). Qed.

Lemma acc_nolazy_one : forall L a n m, nolazy_rng L a m -> (Z.of_nat n <= m)%Z -> acc_nolazy L [(a, n)].
Proof.
ltac2:(KReplay.run1 (kr_t_DrvNodesLazyK ()) [] "h01Hh12Hmh21Lh31ah41mh51np;1p;2p;3p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp4p76111110p100;1p4p741110R<p8p100;np4p76111110R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp4p76111110R>P=p8P>P<p8p100@:p4p76111110R=P>p8P=P<p8p100ADp4p741110R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p4p710RAP8p8PAP9p8p100J<p4p70RAP=p8PAP>p8PAP?p8PAP<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p100L2p4p710R7p100MEp4p710RAp8P7P;p8P7P5p8P7P0p8p100MgR7p4p710R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p4p7210R7P1p8P7P4p8p100O5R4p4p710R7P1p8P7P3p8P7PAp8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100P@p4p710P6p8P0P6p8p100P^p4p741110R6P?p8P6P<p8P6P@p8p100Qdp4p710R@P8p8P@P9p8p100Rip4p710R9P1p8P9p100SoR1p4p710p8P9P1p4p7210p8P9PAp8P9P0p8g00TLj10Tg00U1j1;Tg00UOj14Tg00V2j22Tg00VRj1:Tg00W2j39Tg00o?j11Tg00X7j25Tg00[gj16Tg012Xj67Tg013aj13Tg014jj68Tg00hb#0#0#0#0#0#0#;#4R0/20#:g010dR9g00iGf3RAf2R1f0R@39%11f1R8'5f5R6f4R<PA1209#6P6P<P1%1AP8P@E7%36E8W1W0W4W5X30W2o"). Qed.

(* [comment removed for export] *)
Lemma mat_id_of_nolazy : forall m accs,
  acc_nolazy (m_vm_lazy m) accs -> materialize_model_accesses m accs = Some m.
Proof.
  intros m accs H. unfold materialize_model_accesses.
  rewrite (materialize_accesses_no_new (m_vm_lazy m) (m_vm_materialized m) _ _ accs).
  - rewrite with_vm_backing_id. reflexivity.
  - unfold newly_materialized_pages. apply filter_all_false. intros p Hp.
    destruct (accesses_pages_in accs [] p Hp) as [[] | (a & n & k & Hin & Hk & ->)].
    rewrite (H a n Hin (Z.of_nat k) ltac:(lia)). reflexivity.
Qed.

Lemma with_fds_vm_lazy : forall f m, m_vm_lazy (with_fds f m) = m_vm_lazy m.
Proof.
ltac2:(KReplay.run1 (kr_t_DrvNodesLazyK ()) [] "p'0h01fh12fdh23fsyh32ioh43limh51mi001mh62prh72tmh82vmi014m_fdi026m_fsysi034m_ioi045m_limi056m_proci066m_timei074m_vmp;1p;2p;3p;7p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8g01O?R;p4p70R<P2p8P<P7p8P<P8p8P<P9p8P<P6p8P<p1009Np4p710R<p8p1009kp4p76111110p100;1p4p741110R=p8p100;np4p76111110R>P=p8p100=:p4p7210R?P7p8P?P8p8P?P9p8P?P6p8P?p100=fp4p710p8p100>mp4p76111110R?P>p8P?P=p8p100@:p4p76111110R>P?p8P>P=p8p100ADp4p741110R?p100BIp4p710R@p8P?P=p8P?p100CDp4p7511110RAp8p100DAp4p711RBP@p8PBp100E?p4p771111110p8PBPAp8p100FKp4p711RBP=p8PBp100G<p4p741110p8p100HBp4p70RBP7p8PBP8p8PBP9p8PBP6p8p100I8p4p710RBP8p8PBP9p8p100J<p4p70RBP>p8PBP?p8PBP@p8PBP=p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p100L2p4p710R7p100MEp4p710RBp8P7P<p8P7P5p8P7P0p8p100MgR7p4p710R?P1p8P?P:p8P?P<p8P?P5p8P?P0p8P7p4p7210R7P1p8P7P4p8p100O5R4p4p710R7P1p8P7P3p8P7PBp8P7P0p8P4p4p7210R4P2p8P4P6p8P4P0p8p100P@p4p710P6p8P0P6p8p100P^p4p741110R6P@p8P6P=p8P6PAp8p100Qdp4p710RAP8p8PAP9p8p100Rip4p710R9P1p8P9p100SoR1p4p710p8P9P1p4p7210p8P9PBp8P9P0p8g00TLj10Tg00U1j19Tg00UOj14Tg00V2j22Tg00VRj13Tg01P7j28Tg0164j11Tg00d0j35Tg01Pnj76Tg00bjj27Tg00hb#0#0#0#0#0#0#9#4R0g01Qd'2#3g01NIR9P91200#3R0f2R9f0RB'8#1%1B35PBg01R\g01STg01TLg01UDg01V>g01W7f6R1f5RAf4R8f3R6P9f1R=PBF6#1,70W7W4W6X2;W3W8W1P1PAP8P6P9P=PBO7n01100000170101107103102105104106W5W0o"). Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stepacc_ecall_epend_lz : forall regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom)
  = MachineOk (@mkAccessReport machine_state (epend regs pc mem rom (getr regs 17)) []).
Proof.
  intros regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

Lemma srz_sys_lz : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  srealizes segs scfg (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply (srz_step_disjoint segs scfg _ model _ [] T Hh); [reflexivity | eapply stepacc_ecall_epend_lz; eassumption | | exact Hc].
  intros a n lo sz [].
Qed.


(* [comment removed for export] *)
Lemma node_svc_mat : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (effs i) (ms' i) (evs i))) ->
  (forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
       (exists i, eff = effs i /\ m' = ms' i /\ ev = evs i)
    \/ (spurious_refusal_cfg scfg (sys_input segs ms x8) model eff /\ m_halted m' = None)) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, acc_nolazy (m_vm_lazy (ms' i)) (syscall_effect_accesses (effs i))) ->
  node_ok segs scfg (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hns Hinv Hnu Hh' Hnl. split.
  - intros i.
    apply (sstep_cfg_syscall segs scfg ms model x8 (effs i) (ms' i) (ms' i) (evs i) Hh Hsvc
             (Hok i) (Hns i) (Hh' i)).
    apply mat_id_of_nolazy. exact (Hnl i).
  - intros e st Hss.
    destruct (sstep_cfg_svc_cases segs scfg ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hspec &
           [(Hnsp & Hh2 & [(m'' & -> & Hmat & ->) | (-> & Hmat & ->)]) | (code & Hh2 & -> & ->)])
         | (Hum & -> & ->)].
    + destruct (Hinv _ _ _ Hspec) as [(i & -> & -> & ->) | [Hsp _]]; [| exfalso; exact (Hnsp Hsp)].
      rewrite (mat_id_of_nolazy _ _ (Hnl i)) in Hmat.
      injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hspec) as [(i & -> & -> & ->) | [Hsp _]]; [| exfalso; exact (Hnsp Hsp)].
      rewrite (mat_id_of_nolazy _ _ (Hnl i)) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hspec) as [(i & -> & -> & ->) | [_ Hh3]];
        [rewrite Hh' in Hh2; discriminate | rewrite Hh3 in Hh2; discriminate].
    + exfalso. exact (Hnu Hum).
Qed.

Lemma node_chk_ev_mat : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, acc_nolazy (m_vm_lazy (ms' i)) (syscall_effect_accesses (effs i))) ->
  (forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
  node_ok segs scfg (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hnl Hns.
  apply (node_svc_mat ms model x8 I effs ms' evs Hh Hsvc).
  - intros i. apply check_syscall_ok_iff. apply Hok.
  - exact Hns.
  - intros eff m' ev Hspec. left. apply Hinv. apply check_syscall_ok_iff. exact Hspec.
  - intros Hum. apply (Hnu (mkEffect (Z_to_bv 64 0) [] [])). apply check_syscall_err_iff. exact Hum.
  - exact Hh'.
  - exact Hnl.
Qed.

Lemma node_det_mat : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  acc_nolazy (m_vm_lazy m0) (syscall_effect_accesses eff0) ->
  node_ok segs scfg (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hnl0.
  assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
            exists i : unit, eff = (fun _ => eff0) i /\ m' = (fun _ => m0) i /\ ev = (fun _ => evs0) i).
  { intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto. }
  apply (node_chk_ev_mat ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
  - intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
  - exact Hinv.
  - exact Hnu.
  - intros []; exact Hh0.
  - intros []; exact Hnl0.
  - apply (uniform_not_spurious segs scfg ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0)
             (refusal_b (sys_input segs ms x8) model (eff_ret eff0)) Hinv).
    intros []. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_ret_only_silent_lz : forall ms model x8 r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  RomBase.sys_rob segs (mkCfg ms model) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' []) ->
  m_halted m' = None ->
  srealizes segs scfg (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  srealizes segs scfg (mkCfg ms model) T.
Proof.
  intros ms model x8 r m' T Hh Hsvc Hrob Hchk Hh' Hc.
  eapply srz_silent1; [| exact Hrob | exact Hc].
  rewrite <- (apply_effect_no_write ms r).
  apply (node_det_mat ms model x8 (mkEffect r [] []) m' [] Hh Hsvc).
  - intros eff m'' evs'. rewrite Hchk. apply check_ret_only_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_no_unmodeled.
  - exact Hh'.
  - apply acc_nolazy_nil.
Qed.

(* [comment removed for export] *)
Lemma rz_ret_only_copyins_silent_lz : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  RomBase.sys_rob segs (mkCfg ms model) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' []) ->
  m_halted m' = None ->
  acc_nolazy (m_vm_lazy m') reads ->
  srealizes segs scfg (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  srealizes segs scfg (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hrob Hchk Hh' Hnl Hc.
  eapply srz_silent1; [| exact Hrob | exact Hc].
  rewrite <- (apply_effect_copyins_no_write ms r reads).
  apply (node_det_mat ms model x8 (with_copyins reads (mkEffect r [] [])) m' [] Hh Hsvc).
  - intros eff m'' evs'. rewrite Hchk. apply check_ret_only_copyins_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_copyins_no_unmodeled.
  - exact Hh'.
  - unfold syscall_effect_accesses. cbn. rewrite app_nil_r. exact Hnl.
Qed.

Lemma rz_det_lz : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  RomBase.sys_rob segs (mkCfg ms model) ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  acc_nolazy (m_vm_lazy m0) (syscall_effect_accesses eff0) ->
  srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  srealizes segs scfg (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hrob Hchk Hnu Hh0 Hnl0 Hc.
  eapply srz_silent1; [eapply node_det_mat; eassumption | exact Hrob | exact Hc].
Qed.


(* [comment removed for export] *)
Lemma sstep_of_check_mat : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  m_halted m' = None ->
  acc_nolazy (m_vm_lazy m') (syscall_effect_accesses eff) ->
  sstep segs (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hh' Hnl.
  apply (sstep_syscall segs ms model x8 eff m' m' evs Hh Hsvc).
  - apply check_syscall_ok_iff. exact Hc.
  - exact Hh'.
  - apply mat_id_of_nolazy. exact Hnl.
Qed.

Lemma accesses_with_copyins_ret : forall reads r,
  syscall_effect_accesses (with_copyins reads (mkEffect r [] [])) = reads.
Proof.
ltac2:(KReplay.run1 (kr_t_DrvNodesLazyK ()) ["FPX_1"; "WithSegs"] "h01rh15readsp;1p;2p;6p;3p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8g0367R:p4p710R;P7p8P;P6p8p1008`p4p70R<P2p8P<P7p8P<P8p8P<P9p8P<P6p8P<g009NR<p4p710R=p8p1009kp605611111000p100;1p4p741110R>p8p100;np605611111000R?P>p8p100=:p4p7210R@P7p8P@P8p8P@P9p8P@P6p8P@p100=fp4p710p8p100>mp605611111000R@P?p8P@P>p8p100@:p605611111000R?P@p8P?P>p8p100ADp6054111000R@p100BIp4p710RAp8P@P>p8P@p100CDp4p7511110RBp8p100DAp4p711RCPAp8PCp100E?p4p771111110p8PCPBp8p100FKp4p711RCP>p8PCp100G<p4p741110p8p100HBp4p70RCP7p8PCP8p8PCP9p8PCP6p8p100I8p6051000RCP8p8PCP9p8p100J<p4p70RCP?p8PCP@p8PCPAp8PCP>p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p100L2p6051000R7p100MEp4p710RCp8P7P=p8P7P5p8P7P0p8p100MgR7p6051001R@P1p8P@P;p8P@P=p8P@P5p8P@P0p8P7p60521000R7P1p8P7P4p8p100O5R4p6051001R7P1p8P7P3p8P7PCp8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100P@p4p710P6p8P0P6p8p100P^p6054111000R6PAp8P6P>p8P6PBp8p100Qdp6051000RBP8p8PBP9p8p100Rip6051000R9P1p8P9p100SoR1p4p710p8P9P1p4p7210p8P9PCp8P9P0p8p102]dp605611111000R0P>p8p102iLp605611111000R9P>p8P9P0p8g00TLj10Tg00U1j16Tg00UOj14Tg00V2j22Tg00VRj13TP:j2=Tg00[gj11Tg02c0j6<Tg037gj2;Tg03;Zj1:Tg03<Tj17Tg03=Mj18TP<j39Tg00d0j35Tg02Lmj1>Tg00hb#0#0#0R<#0#0#0#6#4R:g010d'2R0#3R9f1R>,=0f0%6<#4#3,2:#112::#1R<P<g02hT#1%10E<,;>R<#:%7<#8590=59>e%><=59>eX0:W1o"). Qed.

(* [comment removed for export] *)
Lemma node_open_lz : forall ms model x8 reads (mk : word -> Model),
  m_halted model = None ->
  acc_nolazy (m_vm_lazy model) reads ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = m_vm_lazy model) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  fam_on segs scfg ms ->
  node_ok segs scfg (mkCfg ms model) (open_I model) (fun _ => []) (open_nx ms model mk).
Proof.
  intros ms model x8 reads mk Hh Hnl Hsvc Hchk Hmk Hmklazy Hfree Hon.
  apply node_ok_of_pnode; [| exact Hon]. split.
  - intros [[e He] | []]; cbn [open_nx].
    + rewrite <- (apply_effect_copyins_no_write ms (errno_ret e) reads).
      apply (sstep_of_check_mat ms model x8); [exact Hh | exact Hsvc | | exact Hh | rewrite accesses_with_copyins_ret; exact Hnl].
      rewrite Hchk. apply check_open_result_copyins_ok_iff. left. exists e. auto.
    + rewrite <- (apply_effect_copyins_no_write ms (alloc_fd (m_fds model)) reads).
      apply (sstep_of_check_mat ms model x8); [exact Hh | exact Hsvc | | apply Hmk | rewrite accesses_with_copyins_ret, Hmklazy; exact Hnl].
      rewrite Hchk. apply check_open_result_copyins_ok_iff.
      right. exists (alloc_fd (m_fds model)). auto.
  - intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite accesses_with_copyins_ret, (mat_id_of_nolazy _ _ Hnl) in Hmat. injection Hmat as <-.
        exists (inl (exist _ er Her)). cbn [open_nx].
        rewrite apply_effect_copyins_no_write. split; reflexivity.
      * subst fd. rewrite accesses_with_copyins_ret, (mat_id_of_nolazy (mk _) reads) in Hmat by (rewrite Hmklazy; exact Hnl).
        injection Hmat as <-.
        exists (inr tt). cbn [open_nx]. rewrite apply_effect_copyins_no_write. split; reflexivity.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite accesses_with_copyins_ret, (mat_id_of_nolazy _ _ Hnl) in Hmat. discriminate.
      * rewrite accesses_with_copyins_ret, (mat_id_of_nolazy (mk _) reads) in Hmat by (rewrite Hmklazy; exact Hnl). discriminate.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * congruence.
      * rewrite Hmk in Hh2. discriminate.
    + exfalso. rewrite Hchk in Hc. exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hc).
Qed.

Lemma rz_open_lz : forall ms model x8 reads (mk : word -> Model) A B,
  m_halted model = None ->
  acc_nolazy (m_vm_lazy model) reads ->
  ms_svc_pending ms = Some x8 ->
  RomBase.sys_rob segs (mkCfg ms model) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = m_vm_lazy model) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  fam_on segs scfg ms ->
  (forall e, In e openat_errnos ->
     srealizes segs scfg (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  srealizes segs scfg (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                       (mk (alloc_fd (m_fds model)))) B ->
  srealizes segs scfg (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 reads mk A B Hh Hnl Hsvc Hrob Hchk Hmk Hmklazy Hfree Hon HA HB.
  apply (srz_alt2 segs scfg (mkCfg ms model) {e : Z | In e openat_errnos} unit
           (open_nx ms model mk) A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - eapply node_open_lz; eassumption.
  - exact Hrob.
  - intros [e He]. cbn [open_nx]. apply HA. exact He.
  - intros []. cbn [open_nx]. exact HB.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_close_lz : forall regs (pc : word) mem model w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 57 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs))
                       (with_fds (fd_remove (m_fds model) fd) model)) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd e K HF HE Hh H17 Hfd Hfd32 Hlk Hc.
  eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
  eapply rz_ret_only_silent_lz; [exact Hh | reflexivity | rob_mf H17 | | | rewrite adv_set_epend; exact Hc].
  - intros eff. rewrite (check_syscall_57 segs) by (rewrite H17; apply u64_lit; lia).
    unfold check_close. rewrite ms_gpr_epend0, Hfd, (fd32_id fd Hfd32), Hlk. reflexivity.
  - rewrite with_fds_halted'. exact Hh.
Qed.

Lemma rz_ioctl_winsz_lz : forall regs (pc : word) mem model w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 29 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  match e with FdDevNull _ _ => false | FdUrandom => false | _ => true end = true ->
  getr regs 11 = Z_to_bv 64 0x5413 ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem (seg_rom segs))
                       model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd e K HF HE Hh H17 Hfd Hfd32 Hlk Hnd H11 Hc.
  eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
  eapply rz_ret_only_silent_lz; [exact Hh | reflexivity
                                | eapply ioctl_tty_rob; [reflexivity | rewrite H17; apply u64_lit; lia
                                                        | rewrite ms_gpr_epend1, H11; reflexivity]
                                | | exact Hh | rewrite adv_set_epend; exact Hc].
  intros eff. rewrite check_syscall_29 by (rewrite H17; apply u64_lit; lia).
  unfold check_ioctl. rewrite ms_gpr_epend0, ms_gpr_epend1, Hfd, (fd32_id fd Hfd32), Hlk, H11.
  destruct e; first [reflexivity | discriminate Hnd].
Qed.

Lemma rz_read_dir_lz : forall regs (pc : word) mem model w fd K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  (bv_unsigned (getr regs 11) + bv_unsigned (getr regs 12) <= TASK_SIZE)%Z ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd K HF HE Hh H17 Hfd Hfd32 Hlk Hts Hc.
  eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
  eapply rz_ret_only_silent_lz; [exact Hh | reflexivity | rob_mf H17 | | exact Hh | rewrite adv_set_epend; exact Hc].
  intros eff. rewrite (check_syscall_63 segs _ _ eff model) by (rewrite H17; apply u64_lit; lia).
  unfold check_read. rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32), Hlk.
  rewrite (access_okb_intro_le _ _ (proj1 (bv_unsigned_in_range 64 (getr regs 12))) Hts).
  reflexivity.
Qed.

Lemma rz_read_dir_cnt_lz : forall regs (pc : word) mem model w fd (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  getr regs 12 = Z_to_bv 64 cnt -> (0 <= cnt)%Z ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd cnt K HF HE Hh H17 Hfd Hfd32 Hlk H12 Hc0 Hts Hc.
  eapply (rz_read_dir_lz regs pc mem model w fd K); try eassumption.
  rewrite H12, u64_lit; [exact Hts|]. unfold TASK_SIZE in Hts. pose proof (u64_range (getr regs 11)). lia.
Qed.

(* [comment removed for export] *)
Lemma rz_read_file_lz : forall regs (pc : word) mem model w fd p off data (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= 65536)%Z -> (cnt < 2 ^ 64)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  nolazy_rng (m_vm_lazy model) (getr regs 11) cnt ->
  let bs := file_read data off (getr regs 12) in
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
                              (wbytes mem (getr regs 11) bs) (seg_rom segs))
                       (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model)) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd p off data cnt K HF HE Hh H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hok Hts Hnl bs Hc.
  assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
  eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
  destruct (read_bytes_map_of_store_ok segs mem (getr regs 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
  rewrite Z2Nat.id in Hw by lia.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt).
  { unfold ms. rewrite ms_gpr_epend2, H12. apply u64_lit. lia. }
  destruct (read_file_check segs ms (getr regs 17) model fd p off data wv Hno
              ltac:(unfold ms; rewrite ms_gpr_epend0; exact Hfd) Hfd32 Hlk Hfs
              ltac:(unfold ms; rewrite ms_writable_byte_epend, ms_gpr_epend1, ms_gpr_epend2, H12; exact Hw)
              ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
              ltac:(rewrite Hu2; unfold ms; rewrite ms_gpr_epend1; apply access_okb_intro_le; lia)) as [Hchk Hnu].
  unfold ms in Hchk, Hnu. rewrite ms_gpr_epend1, ms_gpr_epend2 in Hchk.
  assert (Hlen : (Z.of_nat (length bs) <= cnt)%Z).
  { subst bs. rewrite length_file_read. unfold word_to_nat. rewrite H12, u64_lit by lia. lia. }
  subst bs. revert Hc Hchk Hlen.
  generalize (file_read data off (getr regs 12)) as bs. intros bs Hc Hchk Hlen.
  eapply (rz_det_lz _ model _ (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) [])
            (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model));
    [exact Hh | reflexivity | rob_mf H17 | exact Hchk | exact Hnu
    | rewrite with_fds_halted'; exact Hh | | ].
  - rewrite with_fds_vm_lazy. unfold syscall_effect_accesses. cbn [eff_copyins eff_writes app].
    destruct bs as [|b bsr]; cbn [delivered_writes write_accesses length]; [apply acc_nolazy_nil|].
    apply (acc_nolazy_one _ _ _ cnt Hnl Hlen).
  - destruct bs as [|b bsr]; cbn [delivered_writes].
    + unfold ms. rewrite adv_ret_epend. cbn [wbytes] in Hc. exact Hc.
    + unfold ms. rewrite adv_write1_epend. exact Hc.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cstr_access_len_aux_le : forall mp fuel a, (cstr_access_len_aux mp a fuel <= fuel)%nat.
Proof.
  intros mp fuel. induction fuel as [|f IH]; intros a; cbn [cstr_access_len_aux]; [lia|].
  (* [comment removed for export] *)
  destruct (negb (access_okb a 1)); [lia|].
  destruct (mp a) as [b|]; [|lia]. destruct (bv_eqb b (Z_to_bv 8 0)); [lia|]. specialize (IH (a + 1)). lia.
Qed.

Section OpenatLz.
  Variables (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (model : Model).
  Variable w : bv 32.
  Hypothesis HF : fetch_word segs pc = Some w.
  Hypothesis HE : is_ecall w = true.
  Hypothesis Hh : m_halted model = None.
  Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
  Hypothesis H10 : getr regs 10 = AT_FDCWD.
  Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.
  Hypothesis Hfs_on : sc_fs scfg = true.
  (* [comment removed for export] *)
  Hypothesis Hnl : nolazy_rng (m_vm_lazy model) (getr regs 11) 4096.

  Let ms := epend regs pc mem (seg_rom segs) (getr regs 17).
  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
  Let fds := m_fds model.

  Lemma open_copyins_nolazy : acc_nolazy (m_vm_lazy model) (open_copyins ms).
  Proof.
    unfold open_copyins. cbv delta [ms]. rewrite ms_gpr_epend1.
    eapply acc_nolazy_one; [exact Hnl|].
    pose proof (cstr_access_len_aux_le (ms_read_byte (epend regs pc mem (seg_rom segs) (getr regs 17))) path_max (getr regs 11)) as Hle.
    unfold path_max in Hle at 2. lia.
  Qed.

  Lemma rz_openat_toolong_lz : forall bs K,
    rdn segs mem (getr regs 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
    (* [comment removed for export] *)
    (bv_unsigned (getr regs 11) + 4096 <= TASK_SIZE)%Z ->
    srealizes segs scfg (mkCfg (post (errno_ret ENAMETOOLONG)) model) K ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros bs K Hrd Hnz Hts Hc. cbv delta [post] in *.
    pose proof (read_cstr_toolong_of_rdn segs mem (getr regs 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hts Hrd) as Hp.
    eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent_lz; [exact Hh | reflexivity | apply (openat_node_rob segs regs pc mem model H17); rewrite Hp; discriminate
                                         | | exact Hh | exact open_copyins_nolazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), Hp. apply check_copyins_after_ret_only.
  Qed.

  Lemma rz_openat_empty_lz : forall K,
    path_at segs regs mem [] ->
    srealizes segs scfg (mkCfg (post (errno_ret ENOENT)) model) K ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros K Hp Hc. cbv delta [post] in *.
    eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent_lz; [exact Hh | reflexivity | apply (openat_node_rob segs regs pc mem model H17); rewrite (path_at_cstr segs regs mem [] Hp); discriminate
                                         | | exact Hh | exact open_copyins_nolazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem [] Hp). apply check_copyins_after_ret_only.
  Qed.

  Lemma rz_openat_absent_lz : forall p K,
    path_at segs regs mem p -> p <> [] -> openat_plain_name p = true -> fs_lookup (m_fs model) p = None ->
    srealizes segs scfg (mkCfg (post (errno_ret ENOENT)) model) K ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros p K Hp Hne Hpl Hfs Hc. cbv delta [post] in *.
    eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent_lz; [exact Hh | reflexivity | apply (openat_node_rob segs regs pc mem model H17); rewrite (path_at_cstr segs regs mem p Hp); discriminate
                                         | | exact Hh | exact open_copyins_nolazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem p Hp).
    rewrite (path_eqb_neq _ _ Hne), (openat_plain_name_noslash _ Hpl), (openat_plain_name_nodirref _ Hpl), Hfs.
    apply check_copyins_after_ret_only.
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  Lemma rz_openat_dirref_lz : forall p KA KB,
    path_at segs regs mem p -> path_is_dirref p = true ->
    (forall e, In e openat_errnos -> srealizes segs scfg (mkCfg (post (errno_ret e)) model) KA) ->
    srealizes segs scfg (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros p KA KB Hp Hdr HA HB. cbv delta [post] in *.
    assert (Hne : p <> []) by (intros ->; discriminate Hdr).
    eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
    eapply rz_open_lz; [exact Hh | exact open_copyins_nolazy | reflexivity | apply (openat_node_rob segs regs pc mem model H17); rewrite (path_at_cstr segs regs mem _ Hp); discriminate
                       | | | | exact Hfree | exact (fam_on_openat_ms segs scfg regs pc mem H17 Hfs_on) | |].
    - intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem _ Hp).
      rewrite (path_eqb_neq _ _ Hne), (path_is_dirref_no_slash _ Hdr), Hdr.
      apply check_copyins_after_open_result.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. apply with_fds_vm_lazy.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.

  Lemma rz_openat_dot_lz : forall KA KB,
    path_at segs regs mem dot_path ->
    (forall e, In e openat_errnos -> srealizes segs scfg (mkCfg (post (errno_ret e)) model) KA) ->
    srealizes segs scfg (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
Proof.
ltac2:(KReplay.run1 (kr_t_DrvNodesLazyK ()) ["FPX_1"; "WithSegs"; "OpenatLz"] "h02Hph12KAh22KBp;4p;2p;5p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710R3p8P0P2p4p7210R2p8P0p1003Hp4p710p8P0p1003iR4p4p710p8P0P4p4p7210p8P0p1004FR4p4p710R5p8P0p1004cp4p7210p8P0p1005Bp4p710R0p8p1005^p4p70R6p1006Np4p710R7p8P6p1006jp4p710R8p8P6p1007Hp4p7210R9p8P6p1007ep4p710R6p8p1008Cp4p710R:P7p8P:P6p8p1008`p4p70R;P2p8P;P7p8P;P8p8P;P9p8P;P6p8P;p1009Np4p710R;p8p1009kp605611111000p100;1p4p741110R<p8p100;np605611111000R=P<p8p100=:p4p7210R>P7p8P>P8p8P>P9p8P>P6p8P>p100=fp4p710p8p100>mp605611111000R>P=p8P>P<p8p100@:p605611111000R=P>p8P=P<p8p100ADp6054111000R>p100BIp4p710R?p8P>P<p8P>p100CDp4p7511110R@p8p100DAp4p711RAP?p8PAp100E?p4p771111110p8PAP@p8p100FKp4p711RAP<p8PAp100G<p4p741110p8p100HBp4p70RAP7p8PAP8p8PAP9p8PAP6p8p100I8p6051000RAP8p8PAP9p8p100J<p4p70RAP=p8PAP>p8PAP?p8PAP<p8P4p4p7210R4P7p8P4P6p8p100K7p4p7210P6p8p100KVp4p73110P6p8p100L2p6051000R7p100MEp4p710RAp8P7P;p8P7P5p8P7P0p8p100MgR7p6051001R>P1p8P>P:p8P>P;p8P>P5p8P>P0p8P7p60521000R7P1p8P7P4p8p100O5R4p6051001R7P1p8P7P3p8P7PAp8P7P0p8P4p60521000R4P2p8P4P6p8P4P0p8p100P@p4p710P6p8P0P6p8p100P^p6054111000R6P?p8P6P<p8P6P@p8p100Qdp6051000R@P8p8P@P9p8p100Rip6051000R9P1p8P9p100SoR1p4p710p8P9P1p4p7210p8P9PAp8P9P0p8p102]dp605611111000R0P<p8p102iLp605611111000R9P<p8P9P0p8g05`]j42Tg00bjj21Tg05mdj50Tg02H0R0p,4segsp,4regsp,3memg05o2R9C2P9f2f1f0g00mHg00mh'1D0W0X20W1o"). Qed.

  Lemma rz_openat_file_lz : forall p d KA KB,
    path_at segs regs mem p -> p <> [] -> openat_plain_name p = true -> fs_lookup (m_fs model) p = Some d ->
    (forall e, In e openat_errnos -> srealizes segs scfg (mkCfg (post (errno_ret e)) model) KA) ->
    srealizes segs scfg (mkCfg (post (alloc_fd fds))
                         (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) model)) KB ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros p d KA KB Hp Hne Hpl Hfs HA HB. cbv delta [post] in *.
    eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
    eapply rz_open_lz; [exact Hh | exact open_copyins_nolazy | reflexivity | apply (openat_node_rob segs regs pc mem model H17); rewrite (path_at_cstr segs regs mem _ Hp); discriminate
                       | | | | exact Hfree | exact (fam_on_openat_ms segs scfg regs pc mem H17 Hfs_on) | |].
    - intros eff. fold ms. rewrite (openat_check_head segs regs pc mem model H17 H10 Hfl), (path_at_cstr segs regs mem p Hp).
      rewrite (path_eqb_neq _ _ Hne), (openat_plain_name_noslash _ Hpl), (openat_plain_name_nodirref _ Hpl), Hfs.
      apply check_copyins_after_open_result.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. apply with_fds_vm_lazy.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.
End OpenatLz.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma copy_iovecs_accesses_nolazy : forall L mp k (a0 : word),
  (bv_unsigned a0 + 16 * Z.of_nat k < 2 ^ 64)%Z ->
  nolazy_rng L a0 (16 * Z.of_nat k) ->
  acc_nolazy L (copy_iovecs_accesses mp a0 k).
Proof.
  intros L mp k. induction k as [|k IH]; intros a0 Hw Hnl; cbn [copy_iovecs_accesses]; [apply acc_nolazy_nil|].
  (* [comment removed for export] *)
  apply acc_nolazy_app.
  - assert (Hu8 : bv_unsigned (a0 + 8) = (bv_unsigned a0 + 8)%Z).
    { rewrite bv_add_unsigned. change (bv_unsigned (8 : word)) with 8%Z. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
      pose proof (u64_range a0). apply Z.mod_small. lia. }
    unfold iovec_entry_accesses.
    destruct (read_u64 mp (a0 + 8)); [|apply acc_nolazy_nil].
    destruct (read_u64 mp a0); (apply acc_nolazy_cons; [|apply acc_nolazy_nil]).
    + intros j Hj. apply Hnl. lia.
    + intros j Hj. rewrite Hu8. replace (bv_unsigned a0 + 8 + j)%Z with (bv_unsigned a0 + (8 + j))%Z by ring. apply Hnl. lia.
  - destruct (read_iovec_entry mp a0); try apply acc_nolazy_nil.
    assert (Hu : bv_unsigned (a0 + 16) = (bv_unsigned a0 + 16)%Z).
    { rewrite bv_add_unsigned. change (bv_unsigned (16 : word)) with 16%Z. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
      pose proof (u64_range a0). apply Z.mod_small. lia. }
    apply IH; [rewrite Hu; lia|].
    intros j Hj. rewrite Hu. replace (bv_unsigned a0 + 16 + j)%Z with (bv_unsigned a0 + (16 + j))%Z by ring. apply Hnl. lia.
Qed.

Lemma import_iovecs_accesses_nolazy : forall L mp (iov : word) (cnt : nat),
  (bv_unsigned iov + 16 * Z.of_nat cnt <= TASK_SIZE)%Z -> (cnt <= 1024)%nat ->
  nolazy_rng L iov (16 * Z.of_nat cnt) ->
  acc_nolazy L (import_iovecs_accesses mp iov (Z_to_bv 64 (Z.of_nat cnt))).
Proof.
  intros L mp iov cnt Hts Hc Hnl. unfold import_iovecs_accesses.
  assert (Hwn : word_to_nat (Z_to_bv 64 (Z.of_nat cnt)) = cnt).
  { unfold word_to_nat. rewrite u64_lit by lia. apply Nat2Z.id. }
  destruct (bv_eqb (Z_to_bv 64 (Z.of_nat cnt)) (Z_to_bv 64 1)) eqn:E1.
  - apply bv_eqb_eq in E1. apply (f_equal bv_unsigned) in E1. rewrite !u64_lit in E1 by lia.
    destruct (negb (access_okb iov 16)); [apply acc_nolazy_nil|].
    (* [comment removed for export] *)
    assert (Hu8 : bv_unsigned (iov + 8) = (bv_unsigned iov + 8)%Z).
    { rewrite bv_add_unsigned. change (bv_unsigned (8 : word)) with 8%Z. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
      pose proof (u64_range iov). apply Z.mod_small. unfold TASK_SIZE in Hts. lia. }
    unfold iovec_entry_accesses.
    destruct (read_u64 mp (iov + 8)); [|apply acc_nolazy_nil].
    destruct (read_u64 mp iov); (apply acc_nolazy_cons; [|apply acc_nolazy_nil]).
    + intros j Hj. apply Hnl. lia.
    + intros j Hj. rewrite Hu8. replace (bv_unsigned iov + 8 + j)%Z with (bv_unsigned iov + (8 + j))%Z by ring. apply Hnl. lia.
  - destruct (bv_eqb (Z_to_bv 64 (Z.of_nat cnt)) (Z_to_bv 64 0)); [apply acc_nolazy_nil|].
    destruct (IOV_MAX <? bv_unsigned (Z_to_bv 64 (Z.of_nat cnt)))%Z; [apply acc_nolazy_nil|].
    destruct (negb (access_okb iov (16 * bv_unsigned (Z_to_bv 64 (Z.of_nat cnt))))); [apply acc_nolazy_nil|].
    rewrite Hwn. apply copy_iovecs_accesses_nolazy; [unfold TASK_SIZE in Hts; lia | exact Hnl].
Qed.

Lemma iov_prefix_accesses_nolazy : forall L iovs left,
  Forall (fun bn => nolazy_rng L (fst bn) (bv_unsigned (snd bn))) iovs ->
  acc_nolazy L (iov_prefix_accesses iovs left).
Proof.
  intros L iovs. induction iovs as [|[b n] r IH]; intros left HF.
  - destruct left; apply acc_nolazy_nil.
  - inversion HF as [|x l Hb Hr]; subst. cbn [fst snd] in Hb.
    destruct left as [|l']; [apply acc_nolazy_nil|]. cbn [iov_prefix_accesses].
    destruct (Nat.eqb (word_to_nat_bounded n (S l')) 0); [apply IH; exact Hr|].
    apply acc_nolazy_cons; [|apply IH; exact Hr].
    apply (nolazy_rng_sub L b (bv_unsigned n) _ Hb).
    rewrite word_to_nat_bounded_eq_min. unfold word_to_nat. pose proof (u64_range n). lia.
Qed.

(* [comment removed for export] *)
Lemma rz_writev_pending_lz : forall ms x8 model (fd : Z) (iov : word) iovs bss (T : nat -> TSet),
  ms_rom ms = seg_rom segs ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd ->
  ms_gpr ms 1 = iov ->
  ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array segs (ms_mem ms) iov iovs ->
  iov_bufs_ok iovs ->
  iov_bufs segs (ms_mem ms) iovs bss ->
  nolazy_rng (m_vm_lazy model) iov (16 * Z.of_nat (length iovs)) ->
  Forall (fun bn => nolazy_rng (m_vm_lazy model) (fst bn) (bv_unsigned (snd bn))) iovs ->
  let bs := concat bss in
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length bs)%nat ->
     srealizes segs scfg (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))) model) (T k)) ->
  srealizes segs scfg (mkCfg ms model)
    (t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
  intros ms x8 model fd iov iovs bss T Hrom Hh Hsvc Hfd Hrdr Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs Hnl1 Hnl2 bs
         Ht1 Ht30 Hk.
  destruct (writev_checkX segs ms x8 model fd iov iovs bss Hrom Hfd Hrdr Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs
              Ht1 Ht30)
    as [Hlen Hchk]. fold bs in Hlen, Hchk.
  set (tot := iovs_total iovs) in *.
  set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
  assert (HnlA : forall k, acc_nolazy (m_vm_lazy model) (CA ++ iov_prefix_accesses iovs k)).
  { intros k. apply acc_nolazy_app; [apply import_iovecs_accesses_nolazy; [exact Hiok | lia | exact Hnl1] | apply iov_prefix_accesses_nolazy; exact Hnl2]. }
  assert (Hnb : (1 <= length bs)%nat) by lia.
  pose (effs := fun i : wr_index bs =>
          mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] []
                    (CA ++ iov_prefix_accesses iovs (proj1_sig i))).
  assert (Eacc : forall i, syscall_effect_accesses (effs i) = CA ++ iov_prefix_accesses iovs (proj1_sig i)).
  { intros i. unfold effs, syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses]. apply app_nil_r. }
  assert (Enx : forall i : wr_index bs,
    mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) model).
  { intros [k Hk']. cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (Z_to_bv 64 (Z.of_nat k)) (CA ++ iov_prefix_accesses iovs k)).
    reflexivity. }
  apply (srz_node segs scfg (mkCfg ms model) (wr_index bs)
           (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
           (fun i => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model)
           (fun i => T (proj1_sig i)) (wr_full bs Hnb)).
  3:{ intros [k [Hk1 Hk2]]. cbn [proj1_sig]. apply Hk; assumption. }
  2:{ assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs)))
        by (unfold iovcnt32, abi_low32; rewrite u64_lit by lia; rewrite Z.mod_small by lia; reflexivity).
      assert (Hcap : cap_iovecs iovs = iovs)
        by (unfold cap_iovecs; apply cap_iovecs_id; unfold MAX_RW_COUNT; try fold tot; lia).
      apply (writev_rob segs ms model x8 (Z_to_bv 64 fd) iovs (concat bss) Hsvc Hno).
      - rewrite H0, fd32_id by (rewrite u64_lit; lia). exact Hfd.
      - rewrite H1, H2, Hcnt32. exact (import_iovecs_of_array segs ms iovs iov Hrom Hcnt Hiok Harr Hbok).
      - rewrite Hcap. exact (gather_of_bufs segs ms iovs bss Hrom Hbufs). }
  assert (Hku : forall k, (k <= length bs)%nat -> bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k).
  { intros k Hk2. apply u64_lit. lia. }
  apply (node_ok_of_pnode_sysno segs scfg ms model x8 66%Z); [exact Hsvc | exact Hno | exact injected_arm_66 |].
  split.
  - intros i. rewrite Enx. apply (sstep_of_check_mat ms model x8); [exact Hh | exact Hsvc | | exact Hh | rewrite Eacc; apply HnlA].
    destruct i as [k [Hk1 Hk2]]. unfold effs. cbn [proj1_sig]. rewrite Hchk.
    rewrite (Hku k Hk2), Nat2Z.id.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
    replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat k))) with false
      by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite (Hku k Hk2); lia).
    rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
  - assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
              exists i : wr_index bs, eff = effs i /\ m' = model /\ ev = map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)).
    { intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate].
      destruct ((1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? tot)%Z && negb (addr_is_error_b ret))%bool eqn:Eb;
        [|discriminate].
      destruct (access_ranges_eqb ci (CA ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))) eqn:Eci;
        [|discriminate].
      injection Hc as <- <-.
      apply andb_true_iff in Eb as [Eb _]. apply andb_true_iff in Eb as [E1 E2].
      apply Z.leb_le in E1. apply Z.leb_le in E2. apply access_ranges_eqb_eq in Eci.
      assert (Hkr : (1 <= Z.to_nat (bv_unsigned ret))%nat /\ (Z.to_nat (bv_unsigned ret) <= length bs)%nat) by lia.
      exists (exist _ (Z.to_nat (bv_unsigned ret)) Hkr). cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
      rewrite Z2Nat.id by lia. rewrite u64_roundtrip'. subst ci. repeat split; reflexivity. }
    intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite Eacc, (mat_id_of_nolazy _ _ (HnlA _)) in Hmat. injection Hmat as <-.
      exists i. rewrite Enx. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite Eacc, (mat_id_of_nolazy _ _ (HnlA _)) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). congruence.
    + exfalso. rewrite Hchk in Hc. destruct eff as [ret ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct (_ && _)%bool; [destruct (access_ranges_eqb _ _)|]; discriminate.
Qed.

(* [comment removed for export] *)
Lemma rz_writev2_lz : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  nolazy_rng (m_vm_lazy model) iov 32 -> nolazy_rng (m_vm_lazy model) b1 (bv_unsigned n1) -> nolazy_rng (m_vm_lazy model) b2 (bv_unsigned n2) ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (T k)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
    (t_alt (fun i : wr_index (bs1 ++ bs2) =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (bs1 ++ bs2))) (T (proj1_sig i)))).
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE Hh Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Nl0 Nl1 Nl2 Ht1 Ht30 Hk.
  eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
  pose proof (u64_range n1). pose proof (u64_range n2).
  replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending_lz (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1); (b2, n2)] [bs1; bs2] T);
    [reflexivity | exact Hh | reflexivity | exact Hfd | exact Hrdr | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z; lia
    | | cbn [iov_bufs_ok]; repeat split; assumption |
    | change (16 * Z.of_nat (length [(b1, n1); (b2, n2)]))%Z with 32%Z; exact Nl0
    | repeat constructor; assumption
    | cbn [iovs_total]; lia
    | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend].
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
    2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
        rewrite at_at. reflexivity. }
    repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. repeat split; assumption.
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev1_lz : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  nolazy_rng (m_vm_lazy model) iov 16 -> nolazy_rng (m_vm_lazy model) b1 (bv_unsigned n1) ->
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (T k)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
    (t_alt (fun i : wr_index bs1 =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs1)) (T (proj1_sig i)))).
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 T HF HE Hh Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Nl0 Nl1 Ht1 Ht30 Hk.
  eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
  pose proof (u64_range n1).
  replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
  replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending_lz (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1)] [bs1] T);
    [reflexivity | exact Hh | reflexivity | exact Hfd | exact Hrdr | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1)])) with 1%Z; lia
    | | cbn [iov_bufs_ok]; split; [assumption | exact I] |
    | change (16 * Z.of_nat (length [(b1, n1)]))%Z with 16%Z; exact Nl0
    | repeat constructor; assumption
    | cbn [iovs_total]; lia
    | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend]. repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. split; [assumption | exact I].
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev2_wall_lz : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  nolazy_rng (m_vm_lazy model) iov 32 -> nolazy_rng (m_vm_lazy model) b1 (bv_unsigned n1) -> nolazy_rng (m_vm_lazy model) b2 (bv_unsigned n2) ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE Hh Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Nl0 Nl1 Nl2 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
  pose proof (u64_range n1). pose proof (u64_range n2).
  apply rz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
  eapply (rz_writev2_lz regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.

Lemma rz_writev1_wall_lz : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  nolazy_rng (m_vm_lazy model) iov 16 -> nolazy_rng (m_vm_lazy model) b1 (bv_unsigned n1) ->
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 K HF HE Hh Hfd Hrdr Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Nl0 Nl1 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
  apply rz_wall; [unfold word_to_nat in L1; lia | exact HK |].
  eapply (rz_writev1_lz regs pc mem model w fd iov b1 n1 bs1
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev2_ch_lz : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  nolazy_rng (m_vm_lazy model) iov 32 -> nolazy_rng (m_vm_lazy model) b1 (bv_unsigned n1) -> nolazy_rng (m_vm_lazy model) b2 (bv_unsigned n2) ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model) K) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_write_ch (Z_to_bv 64 fd) (bs1 ++ bs2) K).
Proof.
  intros. unfold t_write_ch.
  eapply (rz_writev2_lz regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 (fun _ => K)); eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_writev1_zero_lz : forall regs (pc : word) mem model w (fd : Z) (iov b1 : word) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 <= TASK_SIZE)%Z ->
  nolazy_rng (m_vm_lazy model) iov 16 ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd iov b1 K HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiok Hb1 Nl0 Hc.
  eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Harr : iov_array segs (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
  { cbn [iov_array ms_mem ms epend]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
  assert (Himp : import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 1) = ImpOk [(b1, Z_to_bv 64 0)]).
  { unfold import_iovecs. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    rewrite (read_iovec_entry_of_array segs ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr).
    rewrite u64_lit by lia. change (Z.min 0 MAX_RW_COUNT) with 0%Z.
    rewrite (access_okb_of_le b1 0) by lia. reflexivity. }
  assert (Hacc : import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1) = [(iov, 16%nat)]).
  { unfold import_iovecs_accesses. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    exact (iovec_entry_accesses_of_array segs ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr). }
  assert (Hrob : RomBase.sys_rob segs (mkCfg ms model)).
  { apply (writev_rob segs ms model (getr regs 17) (Z_to_bv 64 fd) [(b1, Z_to_bv 64 0)] [] eq_refl Hno).
    - unfold ms. rewrite ms_gpr_epend0, H10, fd32_id by (rewrite u64_lit; lia). exact Hfd.
    - unfold ms. rewrite ms_gpr_epend1, ms_gpr_epend2, H11, H12.
      change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). exact Himp.
    - reflexivity. }
  eapply (rz_ret_only_copyins_silent_lz ms model (getr regs 17) [(iov, 16%nat)] (Z_to_bv 64 0) model);
    [exact Hh | reflexivity | exact Hrob | | exact Hh | apply (acc_nolazy_one _ _ _ 16 Nl0); lia | unfold ms; rewrite adv_set_epend; exact Hc].
  intros eff.
  rewrite (check_syscall_writev (sys_input segs ms (getr regs 17)) eff model) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si.
  assert (G0 : ms_gpr ms 0 = Z_to_bv 64 fd) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (G1 : ms_gpr ms 1 = iov) by (unfold ms; rewrite ms_gpr_epend1; exact H11).
  assert (G2 : ms_gpr ms 2 = Z_to_bv 64 1) by (unfold ms; rewrite ms_gpr_epend2; exact H12).
  rewrite G0, G1, G2.
  rewrite fd32_id by (rewrite u64_lit; lia).
  unfold check_writev. rewrite Hfd.
  replace (w_is0 (Z_to_bv 64 fd)) with false by (symmetry; apply w_is0_pos; rewrite u64_lit; lia).
  change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
  rewrite in_mem_si, Himp, Hacc.
  (* [comment removed for export] *)
  unfold cap_iovecs. cbn [cap_iovecs_aux iovs_total].
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.min_r by (unfold MAX_RW_COUNT; lia).
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. cbv beta iota zeta.
  change ((0 + 0 =? 0)%Z) with true. cbv beta iota. reflexivity.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rz_exit_at_lz : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh H17 H10.
  eapply srz_sys_lz; [exact Hh | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply srz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

Lemma rz_exit_at_lit_lz : forall regs (pc : word) mem rom model w (code : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh H17 H10 Hc.
  rewrite <- (bv_and_255_small code Hc). eapply rz_exit_at_lz; eassumption.
Qed.

End WithSegs.
End FPX_1.
End DrvNodesLazyK.
