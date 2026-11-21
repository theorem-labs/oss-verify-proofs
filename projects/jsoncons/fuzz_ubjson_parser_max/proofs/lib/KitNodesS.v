(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: decodes eight encoded statements into plain Rocq lemmas, adds grant_ok_na with a linux_place_is placement conjunct, and adds grant_ok_na_pin_unpack, grant_ok_na_pin_of_na and grant_ok_na_place, replacing grant_ok_na_pin_eq, as in fuzz_bigint's copy; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/KitNodesS.v, 63 lines within its lines 11-250. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanCeil.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
SimInv ExitSim PropExec CatExec CatSim MmapSim AllocSim Scfg ShapeAlg SpinAlg Nodes RefNodes.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition alloc_enomem_sysno_b (n : Z) : bool :=
match injected_arm n with Some _ => true | None => false end.
Definition alloc_mm_sysno_b (n : Z) : bool := (n =? 222)%Z || (n =? 226)%Z.
Definition grant_ok_na_pin (m : Model) (a : word) (n : Z) : bool :=
(bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
&& (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
&& region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).
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
Lemma refusal_b_mmap_sys : forall ms x8 model r,
bv_unsigned x8 = 222%Z ->
refusal_b (sys_input segs ms x8) model r = errno_ret_in mmap_errnos r.
Proof.
intros ms x8 model r Hno. unfold refusal_b. cbn [in_sysno sys_input]. rewrite Hno. reflexivity.
Qed.
Section Alloc.
Hypothesis Halloc : sc_alloc scfg = false.
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
