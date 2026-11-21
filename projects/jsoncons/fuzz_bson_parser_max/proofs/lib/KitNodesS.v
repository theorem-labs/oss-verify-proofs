(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the reserved-interval ledger): changed grant_na_pin_not_errno, grant_ok_na_pin_of_grant_ok; added grant_ok_na, grant_ok_na_pin_of_na, grant_ok_na_pin_unpack and 1 more; removed grant_ok_na_pin_eq; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/KitNodesS.v, lines 11-17, 31-49, 55-103, 108-132; internal commit ids in comments replaced by public commits or removed. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.   (* [comment removed for export] *)
(* [hint_placement_ok_b] lives in [AsanCeil.v:49] and [grant_ok_na] below names
   it.  The mass port described below added that name to the body WITHOUT adding this require, so
   the file could not compile at all; the arity error above masked it.  No cycle:
   AsanCeil's only library require is PlacementSearch. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanCeil.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import
  SimInv ExitSim PropExec CatExec CatSim MmapSim AllocSim Scfg ShapeAlg SpinAlg Nodes RefNodes.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition alloc_enomem_sysno_b (n : Z) : bool :=
  match injected_arm n with Some _ => true | None => false end.
(* [comment removed for export] *)
Definition alloc_mm_sysno_b (n : Z) : bool := (n =? 222)%Z || (n =? 226)%Z.

(* [comment removed for export] *)
(* STATEMENT CHANGED, old beside new.  The RELEASED file was consistent; the
   breakage entered with the mass port of the model's 08b1429
   change into 48 copies, which did two things here:
     (a) added [hint] to this signature and updated only two of its four uses,
         leaving :46 and :49 below passing three arguments -- the arity error;
     (b) REPLACED the four-conjunct body with a single [linux_place_is] call.
   (b) is the one that matters: the pin stopped being the NON-placement part of
   the test and became only the placement part, while [grant_ok_na] (:39-44) now
   carries six conjuncts -- [linux_place_is], those same four, and
   [hint_placement_ok_b].  That is why :46's [reflexivity] could not hold in
   EITHER arity.

     OLD (released, origin/main, and the parent of that port)
       grant_ok_na_pin (m) (a) (n)  :=  the four conjuncts below
     THEN (the mass port)
       grant_ok_na_pin (hint) (m) (a) (n) := linux_place_is ... hint n a
     NEW
       the released three-argument form, restored verbatim.
   It needs no [hint] because NONE of the four conjuncts mentions placement. *)
Definition grant_ok_na_pin (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).

(* STATEMENT CHANGED with the definition: three arguments again, and proved from
   the conjuncts directly rather than through [linux_place_is_admissible], which
   is about the placement half this definition no longer carries. *)
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

(* STATEMENT CHANGED, old beside new:
     OLD  grant_ok_na_pin m a n = grant_ok_na hint m a n     (an EQUALITY)
     NEW  grant_ok_na hint m a n = true -> grant_ok_na_pin m a n = true
   The equality was true of the released bodies and is FALSE of the revision's:
   [grant_ok_na] gained [linux_place_is] and [hint_placement_ok_b]
   (75d69e00:theories/LinuxProcessSem/Checks/Placement.v's [linux_place_b] family,
   through the 08b1429 mmap-placement change), so it is now strictly stronger
   than the pin.  The implication IS still true, because [grant_ok_na] is a
   conjunction containing all four of the pin's conjuncts.
   This WEAKENS the statement to exactly what its one consumer needs, adds no
   premise, and moves nothing above it.  Consumers re-checked: the ONLY use of
   this lemma anywhere in the cone is [grant_ok_na_pin_of_grant_ok] immediately
   below, which used it LEFT-TO-RIGHT only (`rewrite (grant_ok_na_pin_eq hint)`
   on a goal `grant_ok_na_pin ... = true`); it now applies the implication
   instead. There is no second consumer wanting the other direction. *)
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
  (* [grant_ok] holds the pin's four conjuncts after [linux_place_is] and before the
     budget, so the pin is read off it directly ([grant_ok_na] here is this file's
     six-conjunct form, not RefNodes'). *)
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

(* STATEMENT CHANGED with the definition: three arguments again, matching both
   the released form and the ~20 call sites in AsanNodesMmLibK.v, which pass
   `model a nZ`.  The two numeric premises are kept rather than restored to the
   released single `0 <= n`: they are strictly more than the proof needs, so no
   caller is asked for anything new relative to the text being repaired. *)
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
