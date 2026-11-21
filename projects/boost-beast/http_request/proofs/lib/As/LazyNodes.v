(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  Scfg SimInv ExitSim PropExec CatSim MmapSim AllocSim RelSpec
  ShapeAlg Nodes AgentNodes Gap04 RefNodes SReach AllocNodes
  LazyRestrict LazyRestrictRun LazyRestrictAlg LazyLedger LazySR.
From OSSVerify.Proofs.boost_beast.http_request.lib.Common.Cfg Require RomBase.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma materialize_model_accesses_nil : forall m, materialize_model_accesses m [] = Some m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma with_vm_backing_self : forall m, with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
(* [comment removed for export] *)
Context {SC : StepCfg} {AF : AllocForced SC}.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_chk_ev_mat_cfg : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' ms'' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (effs i) (ms' i) (evs i))) ->
  (forall i, ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
     ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) -> m_halted m' = None) ->
  (~ syscall_spec (sys_input segs ms x8) model Unmodeled) ->
  (forall i, materialize_model_accesses (ms' i) (syscall_effect_accesses (effs i)) = Some (ms'' i)) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms'' i)).
Proof.
  intros ms model x8 I effs ms' ms'' evs Hh Hsvc Hok Hns Hinv Hnh Hnu Hmat. split.
  - intros i. apply (sstep_cfg_syscall segs the_scfg ms model x8 (effs i) (ms' i) (ms'' i) (evs i)
                       Hh Hsvc (Hok i) (Hns i) (Hnh _ _ _ (Hok i)) (Hmat i)).
  - intros e st Hss.
    destruct (sstep_cfg_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hs & Hm & ->)
                                     | [(Hh2 & -> & Hs & Hm & ->)
                                     | [(code & Hh2 & _ & -> & ->)
                                     | (sig & Hk & -> & ->)]]])
         | (Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc Hs) as (i & -> & -> & ->).
      rewrite (Hmat i) in Hm. injection Hm as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc Hs) as (i & -> & -> & ->). rewrite (Hmat i) in Hm. discriminate.
    + exfalso. rewrite (Hnh _ _ _ Hc) in Hh2. discriminate Hh2.
    + exfalso. rewrite (m_killed_of_m_halted_none _ (Hnh _ _ _ Hc)) in Hk. discriminate Hk.
    + exfalso. exact (Hnu Hc).
Qed.

(* [comment removed for export] *)
Lemma node_chk_ev_mat : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' ms'' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (effs i) (ms' i) (evs i))) ->
  (forall i, ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (~ syscall_spec (sys_input segs ms x8) model Unmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, materialize_model_accesses (ms' i) (syscall_effect_accesses (effs i)) = Some (ms'' i)) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms'' i)).
Proof.
  intros ms model x8 I effs ms' ms'' evs Hh Hsvc Hok Hns Hinv Hnu Hh' Hmat.
  apply (node_chk_ev_mat_cfg ms model x8 I effs ms' ms'' evs Hh Hsvc Hok Hns).
  - intros eff m' ev Hc _. exact (Hinv _ _ _ Hc).
  - intros eff m' ev Hc. destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). apply Hh'.
  - exact Hnu.
  - exact Hmat.
Qed.

(* [comment removed for export] *)
Lemma node_family_mat_cfg : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' ms'' : I -> Model) (evs : I -> list event)
    (R : outcome SyscallEffect -> Prop),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> R o) ->
  (forall i, R (Ok (effs i) (ms' i) (evs i))) ->
  (forall i, ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, R (Ok eff m' ev) ->
     ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff m' ev, R (Ok eff m' ev) -> m_halted m' = None) ->
  (~ R Unmodeled) ->
  (forall i, materialize_model_accesses (ms' i) (syscall_effect_accesses (effs i)) = Some (ms'' i)) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms'' i)).
Proof.
  intros ms model x8 I effs ms' ms'' evs R Hh Hsvc HR Hin Hns Hout Hnh Hnu Hmat.
  apply (node_chk_ev_mat_cfg ms model x8 I effs ms' ms'' evs Hh Hsvc).
  - intros i. apply HR. apply Hin.
  - exact Hns.
  - intros eff m' ev Hc Hs. apply HR in Hc. exact (Hout _ _ _ Hc Hs).
  - intros eff m' ev Hc. apply HR in Hc. exact (Hnh _ _ _ Hc).
  - intros Hc. apply HR in Hc. exact (Hnu Hc).
  - exact Hmat.
Qed.

(* [comment removed for export] *)
Lemma node_family_mat : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' ms'' : I -> Model) (evs : I -> list event)
    (R : outcome SyscallEffect -> Prop),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> R o) ->
  (forall i, R (Ok (effs i) (ms' i) (evs i))) ->
  (forall i, ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model (effs i)) ->
  (forall o, R o -> exists i, o = Ok (effs i) (ms' i) (evs i)) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, materialize_model_accesses (ms' i) (syscall_effect_accesses (effs i)) = Some (ms'' i)) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms'' i)).
Proof.
  intros ms model x8 I effs ms' ms'' evs R Hh Hsvc HR Hin Hns Hout Hh' Hmat.
  apply (node_family_mat_cfg ms model x8 I effs ms' ms'' evs R Hh Hsvc HR Hin Hns).
  - intros eff m' ev Hc _. destruct (Hout _ Hc) as (i & Hi). apply Ok_inj in Hi as (-> & -> & ->). exists i. auto.
  - intros eff m' ev Hc. destruct (Hout _ Hc) as (i & Hi). apply Ok_inj in Hi as (-> & -> & ->). apply Hh'.
  - intros Hc. destruct (Hout _ Hc) as (i & Hi). exact (Unmodeled_Ok _ _ _ Hi).
  - exact Hmat.
Qed.

(* [comment removed for export] *)
Lemma node_family_noacc_cfg : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event)
    (R : outcome SyscallEffect -> Prop),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> R o) ->
  (forall i, R (Ok (effs i) (ms' i) (evs i))) ->
  (forall i, ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, R (Ok eff m' ev) ->
     ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff m' ev, R (Ok eff m' ev) -> m_halted m' = None) ->
  (~ R Unmodeled) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs R Hh Hsvc HR Hin Hns Hout Hnh Hnu Hacc.
  apply (node_family_mat_cfg ms model x8 I effs ms' ms' evs R Hh Hsvc HR Hin Hns Hout Hnh Hnu).
  intros i. rewrite (Hacc i). apply materialize_model_accesses_nil.
Qed.

Lemma node_family_noacc : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event)
    (R : outcome SyscallEffect -> Prop),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> R o) ->
  (forall i, R (Ok (effs i) (ms' i) (evs i))) ->
  (forall i, ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model (effs i)) ->
  (forall o, R o -> exists i, o = Ok (effs i) (ms' i) (evs i)) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs R Hh Hsvc HR Hin Hns Hout Hh' Hacc.
  apply (node_family_mat ms model x8 I effs ms' ms' evs R Hh Hsvc HR Hin Hns Hout Hh').
  intros i. rewrite (Hacc i). apply materialize_model_accesses_nil.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_accesses_ecall_gen : forall ms w,
  fetch_word segs (ms_pc ms) = Some w -> is_ecall w = true ->
  step_accesses segs ms
  = MachineOk (@mkAccessReport _
      {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
         ms_svc_pending := Some (ms_reg ms 17); ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
         ms_mem := ms_mem ms; ms_rom := ms_rom ms |} []).
Proof.
  intros ms w HF HE. unfold step_accesses. rewrite HF. unfold decode_exec_accesses. rewrite HE.
  destruct ms; reflexivity.
Qed.

Lemma sreach_ecall_lazy : forall L S Zr ms msF mo w (Q : config -> Prop),
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = ms ->
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some w -> is_ecall w = true ->
  (forall msF', lzok segs L S Zr (mkCfg msF' mo) ->
      restrict L S msF' = {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
                             ms_svc_pending := Some (ms_reg ms 17); ms_resv := ms_resv ms;
                             ms_fcsr := ms_fcsr ms; ms_mem := ms_mem ms; ms_rom := ms_rom ms |} ->
      hid_same L S msF msF' ->
      sreach segs Q (mkCfg msF' mo)) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros L S Zr ms msF mo w Q Hok Hr Hsvc HF HE Hk.
  set (msF' := {| ms_regs := ms_regs msF; ms_fregs := ms_fregs msF; ms_pc_val := ms_pc_val msF;
                  ms_svc_pending := Some (ms_reg msF 17); ms_resv := ms_resv msF;
                  ms_fcsr := ms_fcsr msF; ms_mem := ms_mem msF; ms_rom := ms_rom msF |}).
  assert (Hacc : mi_account_step segs msF mo = MachineOk (msF', mo)).
  { unfold mi_account_step.
    assert (HF' : fetch_word segs (ms_pc msF) = Some w) by (rewrite <- Hr in HF; exact HF).
    rewrite (step_accesses_ecall_gen msF w HF' HE). cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }
  assert (HsvcF : ms_svc_pending msF = None) by (rewrite <- Hr in Hsvc; exact Hsvc).
  eapply sreach_silent1.
  - apply node_account; [exact (lzok_halted Hok) | exact HsvcF | exact Hacc].
  - apply RomBase.sys_rob_instr. exact HsvcF.
  - apply Hk.
    + destruct Hok as [HL Hinv Hh HZ]. split; cbn in *; assumption.
    + subst ms. destruct msF. reflexivity.
    + intros a Ha. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma restrict_mem_zfill : forall L S a n m,
  restrict_mem L S (zfill a n m)
  = fun x => if hiddenb L S x then None else zfill a n m x.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma restrict_mem_zfill_visible : forall L S a n m,
  (forall x, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)%Z -> hiddenb L S x = false) ->
  restrict_mem L S (zfill a n m) = zfill a n (restrict_mem L S m).
Proof.
  intros L S a n m Hvis. apply functional_extensionality. intros x.
  unfold restrict_mem, restrict_mem_by, zfill, zmem.
  destruct (hiddenb L S x) eqn:Eh; [|reflexivity].
  destruct ((bv_unsigned a <=? bv_unsigned x)%Z && (bv_unsigned x <? bv_unsigned a + bv_unsigned n)%Z) eqn:Ein; [|reflexivity].
  apply andb_true_iff in Ein. destruct Ein as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  rewrite (Hvis x) in Eh by lia. discriminate.
Qed.

Lemma restrict_mem_unfill : forall L S a n m,
  restrict_mem L S (unfill a n m) = unfill a n (restrict_mem L S m).
Proof.
  intros L S a n m. apply functional_extensionality. intros x.
  unfold restrict_mem, restrict_mem_by, unfill.
  destruct (hiddenb L S x), ((bv_unsigned a <=? bv_unsigned x)%Z && (bv_unsigned x <? bv_unsigned a + bv_unsigned n)%Z); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma map_contains_false_of_free : forall maps (addr n : word),
  (0 < bv_unsigned n)%Z ->
  region_free maps addr n = true -> map_contains maps addr n = false.
Proof.
  induction maps as [|[b s] maps IH]; intros addr n Hn Hf; [reflexivity|].
  cbn [region_free] in Hf. apply andb_true_iff in Hf. destruct Hf as [H1 H2].
  unfold map_contains. cbn [existsb fst snd]. fold (map_contains maps addr n).
  rewrite (IH addr n Hn H2). rewrite orb_false_r.
  unfold iv_overlap in H1. apply negb_true_iff in H1.
  apply Bool.not_true_is_false. intros Hc. apply andb_true_iff in Hc. destruct Hc as [C1 C2].
  apply Z.leb_le in C1. apply Z.leb_le in C2.
  apply andb_false_iff in H1. destruct H1 as [D | D]; apply Z.ltb_ge in D; lia.
Qed.

Lemma region_free_app_r : forall X1 X2 (a n : word),
  region_free (X1 ++ X2) a n = true -> region_free X2 a n = true.
Proof.
  induction X1 as [|[b s] X1 IH]; intros X2 a n H; [exact H|].
  cbn in H. apply andb_true_iff in H. apply IH. tauto.
Qed.

Lemma region_free_app_l : forall X1 X2 (a n : word),
  region_free (X1 ++ X2) a n = true -> region_free X1 a n = true.
Proof.
  induction X1 as [|[b s] X1 IH]; intros X2 a n H; [reflexivity|].
  cbn in H |- *. apply andb_true_iff in H. destruct H as [H1 H2]. rewrite H1. cbn. eapply IH; exact H2.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_rw_commit_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false ->
  mmap_fixed_rw_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ (mmap_fixed_rw_budget_ok flags m addr n = true
      /\ o = Ok (mkEffect addr [] [(addr, n)])
                (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next h addr n) m)) [])
  \/ (exists e, In e mmap_errnos
       /\ o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
                 (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) m) []).
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna Hfrw. cbv zeta.
  intros Hce Hal Hpos Hrf Hmc.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna, Hfrw. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrf, Hmc. cbn [andb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right; left. split; [assumption | reflexivity].
    + right; right. eexists; split; [eassumption|reflexivity].
  - intros [(e & He & ->) | [(Hb & ->) | (e & He & ->)]].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right; left. eexists _, _, _, _. split; [exists tt; split; [exact Hb | reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
    + right; right. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mmap_fixed_rw_fresh_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false ->
  mmap_fixed_rw_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h ++ vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ (mmap_noreserve_backed_ok flags m nZ = true
      /\ o = Ok (mkEffect addr [] [(addr, n)])
                (with_mmap_backing flags addr n
                   (with_vmmaps (mkVmMapsFull (vm_reserved h) ((addr, n) :: vm_maps h)
                      (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) []).
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna Hfrw. cbv zeta.
  intros Hce Hal Hpos Hrf.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  assert (HnZ : (0 < page_round_up_Z (bv_unsigned len))%Z).
  { pose proof (PlacementSearch.page_round_up_Z_ge (bv_unsigned len)). pose proof (word_unsigned_range len).
    assert (bv_unsigned len <> 0%Z).
    { intros E. unfold w_is0, bv_eqb in Hlen. rewrite E in Hlen. cbn in Hlen. discriminate. }
    lia. }
  assert (Hn : (0 < bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))%Z).
  { rewrite Z_to_bv_unsigned, bv_wrap_small; [exact HnZ|].
    change (bv_modulus 64) with (2^64)%Z. unfold two_pow_64 in *. lia. }
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (region_free_app_l _ _ _ _ Hrf) as Hrfr.
  pose proof (map_contains_false_of_free _ _ _ Hn Hrfm) as Hmc.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna, Hfrw. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrfr, Hmc, Hrf. cbn [andb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. split; [assumption | reflexivity].
  - intros [(e & He & ->) | (Hb & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [exists addr; split; [split; [reflexivity | exact Hb] | reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_noaccess_fresh_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h ++ vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ o = Ok (mkEffectU addr [] [] [(addr, n)] [] [])
            (with_mmap_backing flags addr n
               (with_vmmaps (mkVmMapsFull (vm_reserved h) ((addr, n) :: vm_maps h)
                  ((addr, n) :: vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna. cbv zeta.
  intros Hce Hal Hpos Hrf.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  assert (HnZ : (0 < page_round_up_Z (bv_unsigned len))%Z).
  { pose proof (PlacementSearch.page_round_up_Z_ge (bv_unsigned len)). pose proof (word_unsigned_range len).
    assert (bv_unsigned len <> 0%Z).
    { intros E. unfold w_is0, bv_eqb in Hlen. rewrite E in Hlen. cbn in Hlen. discriminate. }
    lia. }
  assert (Hn : (0 < bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))%Z).
  { rewrite Z_to_bv_unsigned, bv_wrap_small; [exact HnZ|].
    change (bv_modulus 64) with (2^64)%Z. unfold two_pow_64 in *. lia. }
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (region_free_app_l _ _ _ _ Hrf) as Hrfr.
  pose proof (map_contains_false_of_free _ _ _ Hn Hrfm) as Hmc.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrfr, Hmc, Hrf. cbn [andb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. reflexivity.
  - intros [(e & He & ->) | ->].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [exists addr; split; reflexivity|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_noreplace_rw_fresh_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false ->
  mmap_fixed_rw_b prot flags off = false ->
  mmap_noreplace_noaccess_b prot flags off = false ->
  mmap_noreplace_rw_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h ++ vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ (mmap_noreserve_backed_ok flags m nZ = true
      /\ o = Ok (mkEffect addr [] [(addr, n)])
                (with_mmap_backing flags addr n
                   (with_vmmaps (mkVmMapsFull (vm_reserved h) ((addr, n) :: vm_maps h)
                      (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) []).
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna Hfrw Hnna Hnrw. cbv zeta.
  intros Hce Hal Hpos Hrf.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna, Hfrw, Hnna, Hnrw. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrf. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. split; [assumption | reflexivity].
  - intros [(e & He & ->) | (Hb & ->)].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [exists addr; split; [split; [reflexivity | exact Hb] | reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma mmap_noreplace_noaccess_fresh_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false ->
  mmap_fixed_rw_b prot flags off = false ->
  mmap_noreplace_noaccess_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h ++ vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ o = Ok (mkEffectU addr [] [] [(addr, n)] [] [])
            (with_mmap_backing flags addr n
               (with_vmmaps (mkVmMapsFull (vm_reserved h) ((addr, n) :: vm_maps h)
                  ((addr, n) :: vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) [].
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna Hfrw Hnna. cbv zeta.
  intros Hce Hal Hpos Hrf.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna, Hfrw, Hnna. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrf. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. reflexivity.
  - intros [(e & He & ->) | ->].
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. eexists _, _, _, _. split; [exists addr; split; reflexivity|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kprot (na : bool) : Z := if na then 0 else 3.
Definition kflags (nr : bool) : Z := if nr then 16418 else 34.
(* [comment removed for export] *)
Definition fflags (nr : bool) : Z := if nr then 16434 else 50.

(* [comment removed for export] *)
Definition keff (na : bool) (a n : word) : SyscallEffect :=
  if na then mkEffectU a [] [] [(a, n)] [] [] else mkEffect a [] [(a, n)].

Lemma keff_ret : forall na a n, eff_ret (keff na a n) = a.
Proof. intros [|] a n; reflexivity. Qed.
Lemma keff_accesses : forall na a n, syscall_effect_accesses (keff na a n) = [].
Proof. intros [|] a n; reflexivity. Qed.

(* [comment removed for export] *)
(* LPS RETARGET WINDOW f1006fe8..08b1429, measured in rocq-linux-process-semantics:
     f1006fe8:theories/LinuxProcessSem/Run.v:191-197  advance_past_svc  ms_resv := ms_resv ms
     08b1429 :theories/LinuxProcessSem/Run.v:221-227  advance_past_svc  ms_resv := None
     75d69e00:theories/LinuxProcessSem/Run.v:221-227  advance_past_svc  ms_resv := None
   (identical at 08b1429 and 75d69e00, so the change is the retarget's, not the
   later head's; the same query found the definition at all three refs, so it runs.)
   An ecall now CLEARS the load-reserved reservation.  [sysret] is this tree's name
   for the state [advance_past_svc (apply_effect ms eff)] produces, so it must clear
   it too: with [ms_resv := ms_resv ms] the equation [restrict_sysret] below states is
   false, which is the farm's "Unable to unify sysret (restrict L S {...}) ... with
   restrict L' S' (advance_past_svc (apply_effect {...} eff))" at :572.
   [restrict] keeps [ms_resv] (LazyRestrict.v:41-54 via [with_mem]), so nothing else
   in the chain can supply the None.  OLD body, for the record:
     ms_resv := ms_resv ms
   Consumers carried in this commit, each the one place [sysret] is unfolded into an
   explicit machine-state literal:
     As/SecLazy.v:99, Bo/SecLazy.v:100   sysret_MSsvc's right-hand side
     and the POST-syscall [MS ... fc rv ...] literals those two feed
     (As/SecLazy.v:145,191,234; Bo/SecLazy.v:146,192,219;
      As/SecLazyMadvise.v:68; Bo/SecLazyMadvise.v:69).
   The PRE-syscall literals keep a generic [rv] - a reservation may be live when the
   ecall is taken; it is the return that drops it.  [sysret_epend]
   (As/LazyFdNodes.v:348-349) needs no change: [epend] already sets
   [ms_resv := None] (AgentNodes.v:22-26), as does [mkst] (PropExec.v:49-52). *)
Definition sysret (ms : machine_state) (r : word) (M : word -> option byte) : machine_state :=
  {| ms_regs := ms_regs (set_reg ms 10 r); ms_fregs := ms_fregs ms;
     ms_pc_val := ms_pc ms + Z_to_bv 64 4; ms_svc_pending := None;
     ms_resv := None; ms_fcsr := ms_fcsr ms; ms_mem := M; ms_rom := ms_rom ms |}.

Lemma restrict_sysret : forall L S L' S' msF eff,
  restrict L' S' (advance_past_svc (apply_effect msF eff))
  = sysret (restrict L S msF) (eff_ret eff)
      (restrict_mem L' S' (ms_mem (apply_effect msF eff))).
Proof. intros. destruct msF. reflexivity. Qed.

Lemma hid_frame_sysret : forall L S msF eff,
  (forall a, hiddenb L S a = true -> ms_mem (apply_effect msF eff) a = ms_mem msF a) ->
  hid_same L S msF (advance_past_svc (apply_effect msF eff)).
Proof. intros L S msF eff H a Ha. cbn. apply H. exact Ha. Qed.

(* [comment removed for export] *)
Lemma apply_effect_mem_zeros : forall ms a n,
  ms_mem (apply_effect ms (mkEffect a [] [(a, n)])) = zfill a n (ms_mem ms).
Proof.
  intros ms a n. cbn. apply functional_extensionality. intros x.
  unfold zfill, zmem, zeros_cover. cbn.
  destruct ((bv_unsigned a <=? bv_unsigned x)%Z && (bv_unsigned x <? bv_unsigned a + bv_unsigned n)%Z); reflexivity.
Qed.

Lemma apply_effect_mem_unmaps : forall ms r a n,
  ms_mem (apply_effect ms (mkEffectU r [] [] [(a, n)] [] [])) = unfill a n (ms_mem ms).
Proof.
  intros ms r a n. cbn. apply functional_extensionality. intros x.
  unfold unfill. cbn. 
  destruct ((bv_unsigned a <=? bv_unsigned x)%Z && (bv_unsigned x <? bv_unsigned a + bv_unsigned n)%Z); reflexivity.
Qed.



Lemma w_is0_false : forall (len : word), len <> Z_to_bv 64 0 -> w_is0 len = false.
Proof. intros len H. unfold w_is0. apply bv_eqb_neq. exact H. Qed.

Lemma in_arg1_sys_input' : forall ms x8, in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.
Lemma in_arg2_sys_input' : forall ms x8, in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.

Lemma kgates : forall (na nr : bool),
  mmap_off_aligned_b (Z_to_bv 64 0) = true
  /\ mmap_anon_b (Z_to_bv 64 (kflags nr)) = true
  /\ mmap_modeled_b (Z_to_bv 64 (kprot na)) (Z_to_bv 64 (kflags nr)) (Z_to_bv 64 0) = negb na
  /\ mmap_noaccess_b (Z_to_bv 64 (kprot na)) (Z_to_bv 64 (kflags nr)) (Z_to_bv 64 0) = na
  /\ mmap_noreserve_b (Z_to_bv 64 (kflags nr)) = nr.
Proof. intros [|] [|]; vm_compute; repeat split; reflexivity. Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__4 := Elimination for Corelib.Init.Logic.ex Sort Prop.

(* LPS #38 (75d69e00): THE OLD STATEMENT OF THIS LEMMA IS FALSE, so it is
   restated and its old right-hand side is kept beside it below.

   OLD (an iff whose right-hand side admitted EVERY free address):

     syscall_spec (sys_input segs ms x8) mo o <->
     mmap_err_out mo o
     \/ exists a, (bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a
                   /\ bv_unsigned a + nZ <= alloc_top h
                   /\ region_free (vm_reserved h ++ vm_maps h) a n = true
                   /\ (na = false -> mmap_noreserve_backed_ok ... = true))
                  /\ o = Ok (keff na a n) (grant_model ... ) []

   Since #38 the fresh-grant arms of [Mmap.mmap_spec] CHOOSE the address with
   [Checks.Placement.linux_place] (Sys/Mm/Mmap.v:1958-1961 rw, :1976-1978
   PROT_NONE), and [Checks.Placement.linux_place_is_admissible]
   (Placement.v:1038-1043) gives placement => the four facts above.  THE
   CONVERSE IS FALSE.  Countermodel, valid for arbitrary [kb_thp] because 4096
   is not a multiple of the 2 MiB pmd: maps = reserved = [], mmap_base = 4096,
   init_sp = stack_max_size + 8192, nZ = 4096, hint = 0, a = 4096.  All four
   old conjuncts hold and BOTH of [linux_place_exists]' windows are empty --
   top-down [4096, 4096) and bottom-up [0x2aaaaab000, 8192).

   NEW: the placement test is appended to the success predicate.  The four old
   conjuncts are KEPT (they are what every consumer reads), so a consumer's
   destructuring gains one name at the END and changes nowhere else.  No kernel
   field is pinned: the test names [kb_thp (m_kernel mo)] and the hint
   [ms_gpr ms 0] symbolically. *)
Lemma mmap_kernel_spec : forall (na nr : bool) ms mo x8 o,
  bv_unsigned x8 = 222%Z ->
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 (kprot na) -> ms_gpr ms 3 = Z_to_bv 64 (kflags nr) ->
  ms_gpr ms 5 = Z_to_bv 64 0 ->
  (* 727298f3 (#144/#146): the decline, tested outside the [alt] in BOTH
     freely-placed arms, so both branches of the [destruct na] below need it. *)
  place_declined_b (m_kernel mo) (m_vmmaps mo) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  syscall_spec (sys_input segs ms x8) mo o <->
  mmap_err_out mo o
  \/ exists a, ((bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
                /\ (bv_unsigned a + nZ <= alloc_top h)%Z
                /\ region_free (vm_reserved h ++ vm_maps h) a n = true
                /\ (na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (kflags nr)) mo nZ = true)
                /\ Placement.linux_place_is h (kb_thp (m_kernel mo)) (ms_gpr ms 0) nZ a = true)
               /\ o = Ok (keff na a n) (grant_model (Z_to_bv 64 (kflags nr)) a n na mo) [].
Proof.
  intros na nr ms mo x8 o Hno. cbv zeta. intros Hlen H2 H3 H5 Hdecl.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact Hlen).
  assert (HnPos : (0 < page_round_up_Z (bv_unsigned (ms_gpr ms 1)))%Z).
  { pose proof (page_round_up_Z_pos (bv_unsigned (ms_gpr ms 1)) (w_is0_false_pos _ E1)).
    unfold page_size in *. lia. }
  assert (HnAl : (page_round_up_Z (bv_unsigned (ms_gpr ms 1)) mod page_size = 0)%Z)
    by apply Placement.page_round_up_Z_aligned.
  rewrite (syscall_spec_222 _ mo o) by (rewrite ExitSim.in_sysno_sys_input; exact Hno).
  rewrite in_arg0_sys_input, in_arg1_sys_input', in_arg2_sys_input',
          in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input.
  rewrite H2, H3, H5.
  destruct na.
  - (* PROT_NONE: the noaccess arm *)
    destruct (kgates true nr) as (Goff & Ganon & Gmod & Gnacc & _).
    cbn [negb] in Gmod.
    rewrite (mmap_noaccess_outcome _ _ _ _ _ _ _ mo o Goff Ganon E1 Gmod Gnacc Hdecl).
    unfold keff, grant_model, grant_vmmaps. cbn [m_vmmaps].
    split.
    + intros [He | (a & Hpl & ->)]; [left; exact He | right].
      destruct (Placement.linux_place_is_admissible _ _ _ _ _ HnPos HnAl Hpl) as (G1 & G2 & G3 & G4).
      exists a. split; [|reflexivity].
      repeat split; try assumption. intro Hc. discriminate Hc.
    + intros [He | (a & (_ & _ & _ & _ & _ & Hpl) & ->)]; [left; exact He | right].
      exists a. split; [exact Hpl | reflexivity].
  - (* rw: the modeled arm *)
    destruct (kgates false nr) as (Goff & Ganon & Gmod & _ & _).
    cbn [negb] in Gmod.
    rewrite (mmap_rw_outcome _ _ _ _ _ _ _ mo o Goff Ganon E1 Gmod Hdecl).
    unfold keff, grant_model, grant_vmmaps. cbn [m_vmmaps].
    split.
    + intros [He | (a & (Hpl & Hnr) & ->)]; [left; exact He | right].
      destruct (Placement.linux_place_is_admissible _ _ _ _ _ HnPos HnAl Hpl) as (G1 & G2 & G3 & G4).
      exists a. split; [|reflexivity].
      repeat split; try assumption. intros _. exact Hnr.
    + intros [He | (a & (_ & _ & _ & _ & Hnr & Hpl) & ->)]; [left; exact He | right].
      exists a. split; [split; [exact Hpl | exact (Hnr eq_refl)] | reflexivity].
Qed.

(* [old beside new] WHAT SURVIVES OF THE OLD RIGHT-HAND SIDE: it is still
   NECESSARY, and that is the direction every consumer of the old shape used.
   Only the converse failed, which is why the lemma above had to be restated
   rather than reproved.  This is the old text, proved. *)
Lemma mmap_kernel_spec_old_rhs_necessary : forall (na nr : bool) ms mo x8 o,
  bv_unsigned x8 = 222%Z ->
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 (kprot na) -> ms_gpr ms 3 = Z_to_bv 64 (kflags nr) ->
  ms_gpr ms 5 = Z_to_bv 64 0 ->
  place_declined_b (m_kernel mo) (m_vmmaps mo) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  syscall_spec (sys_input segs ms x8) mo o ->
  mmap_err_out mo o
  \/ exists a, ((bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
                /\ (bv_unsigned a + nZ <= alloc_top h)%Z
                /\ region_free (vm_reserved h ++ vm_maps h) a n = true
                /\ (na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (kflags nr)) mo nZ = true))
               /\ o = Ok (keff na a n) (grant_model (Z_to_bv 64 (kflags nr)) a n na mo) [].
Proof.
  intros na nr ms mo x8 o Hno. cbv zeta. intros Hlen H2 H3 H5 Hdecl HS.
  apply (proj1 (mmap_kernel_spec na nr ms mo x8 o Hno Hlen H2 H3 H5 Hdecl)) in HS.
  destruct HS as [He | (a & (G1 & G2 & G3 & G4 & G5 & _) & Ho)]; [left; exact He | right].
  exists a. split; [repeat split; assumption | exact Ho].
Qed.

(* [comment removed for export] *)
(* #38: the grant now has to name Linux's address.  The placement test is the
   ONE new premise; the four old ones are unchanged and still required by the
   consumers, so this lemma's old text is its new text plus one line. *)
Lemma mmap_kernel_grant_ok : forall (na nr : bool) ms mo x8 (g : word),
  bv_unsigned x8 = 222%Z ->
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 (kprot na) -> ms_gpr ms 3 = Z_to_bv 64 (kflags nr) ->
  ms_gpr ms 5 = Z_to_bv 64 0 ->
  place_declined_b (m_kernel mo) (m_vmmaps mo) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  (bv_unsigned g mod page_size = 0)%Z -> (0 < bv_unsigned g)%Z -> (bv_unsigned g + nZ <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) g n = true ->
  (na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (kflags nr)) mo nZ = true) ->
  Placement.linux_place_is h (kb_thp (m_kernel mo)) (ms_gpr ms 0) nZ g = true ->
  syscall_spec (sys_input segs ms x8) mo (Ok (keff na g n) (grant_model (Z_to_bv 64 (kflags nr)) g n na mo) []).
Proof.
  intros na nr ms mo x8 g Hno. cbv zeta. intros Hlen H2 H3 H5 Hdecl G1 G2 G3 G4 G5 G6.
  apply (proj2 (mmap_kernel_spec na nr ms mo x8 _ Hno Hlen H2 H3 H5 Hdecl)). right. exists g. split; [|reflexivity].
  repeat split; assumption.
Qed.

(* THE BRIDGE THE REVISED CHAIN NEEDS.  A caller still holds only the old GAP
   witness [g] -- an admissible address, not Linux's.  Since #38 that is no
   longer enough, so the GAP carries ONE more conjunct, the weakest premise
   [Checks.Placement.linux_place_exists] consumes: [g] fits in one of Linux's
   two windows.  From it this lemma produces the address LINUX chooses,
   together with the same four admissibility facts the old witness carried, so
   every consumer downstream reads exactly what it read before.

   NO KERNEL FIELD IS PINNED: [linux_place_exists] answers for arbitrary [thp]
   and arbitrary hint, so [kb_thp], [kb_rseq], [kb_aslr], [kb_guard] and
   [kb_rnd_bits] all stay free.  The allocator supplies the RIGHT disjunct from
   its own invariant ([SecGap.gap_witness_fit_top_window] at [AHI_LO] =
   0x10007fff8000 > [task_unmapped_base] = 0x2aaaaab000). *)
Lemma mmap_kernel_grant_exists : forall (na nr : bool) ms mo x8 (g : word),
  bv_unsigned x8 = 222%Z ->
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 (kprot na) -> ms_gpr ms 3 = Z_to_bv 64 (kflags nr) ->
  ms_gpr ms 5 = Z_to_bv 64 0 ->
  place_declined_b (m_kernel mo) (m_vmmaps mo) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  (bv_unsigned g mod page_size = 0)%Z -> (0 < bv_unsigned g)%Z -> (bv_unsigned g + nZ <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) g n = true ->
  (bv_unsigned g + nZ <= mmap_top h \/ task_unmapped_base <= bv_unsigned g)%Z ->
  (na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (kflags nr)) mo nZ = true) ->
  exists a : word,
    (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
    /\ (bv_unsigned a + nZ <= alloc_top h)%Z
    /\ region_free (vm_reserved h ++ vm_maps h) a n = true
    /\ Placement.linux_place_is h (kb_thp (m_kernel mo)) (ms_gpr ms 0) nZ a = true
    /\ syscall_spec (sys_input segs ms x8) mo
         (Ok (keff na a n) (grant_model (Z_to_bv 64 (kflags nr)) a n na mo) []).
Proof.
  intros na nr ms mo x8 g Hno. cbv zeta. intros Hlen H2 H3 H5 Hdecl Gal Gpos Gtop Gfree GW Gnr.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact Hlen).
  assert (HnPos : (0 < page_round_up_Z (bv_unsigned (ms_gpr ms 1)))%Z).
  { pose proof (page_round_up_Z_pos (bv_unsigned (ms_gpr ms 1)) (w_is0_false_pos _ E1)).
    unfold page_size in *. lia. }
  assert (HnAl : (page_round_up_Z (bv_unsigned (ms_gpr ms 1)) mod page_size = 0)%Z)
    by apply Placement.page_round_up_Z_aligned.
  assert (Hgw : Z_to_bv 64 (bv_unsigned g) = g) by apply Z_to_bv_bv_unsigned.
  assert (HGF : gap_fits (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) page_size
                  (mmap_top (m_vmmaps mo)) (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) (bv_unsigned g)
                \/ gap_fits (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) task_unmapped_base
                     (alloc_top (m_vmmaps mo)) (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) (bv_unsigned g)).
  { destruct GW as [Hhi | Hlo].
    - left. unfold gap_fits. repeat split;
        [exact Gal | unfold page_size in *; lia | exact Hhi | rewrite Hgw; exact Gfree].
    - right. unfold gap_fits. repeat split;
        [exact Gal | exact Hlo | exact Gtop | rewrite Hgw; exact Gfree]. }
  destruct (Placement.linux_place_exists (m_vmmaps mo) (kb_thp (m_kernel mo)) (ms_gpr ms 0)
              (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) HnPos HnAl
              (ex_intro _ (bv_unsigned g) HGF)) as (aZ & Hpl).
  assert (Haw : bv_unsigned (Z_to_bv 64 aZ) = aZ).
  { destruct (Placement.linux_place_admissible _ _ _ _ _ HnPos HnAl Hpl) as (A1 & A2 & A3 & A4).
    apply bv_unsigned_Z_to_bv_u64.
    pose proof (Placement.alloc_top_lt_two_pow_64 (m_vmmaps mo)). unfold two_pow_64 in *. lia. }
  assert (Hpi : Placement.linux_place_is (m_vmmaps mo) (kb_thp (m_kernel mo)) (ms_gpr ms 0)
                  (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) (Z_to_bv 64 aZ) = true).
  { apply (Placement.linux_place_is_iff _ _ _ _ _ HnPos HnAl). rewrite Haw. exact Hpl. }
  exists (Z_to_bv 64 aZ).
  destruct (Placement.linux_place_is_admissible _ _ _ _ _ HnPos HnAl Hpi) as (B1 & B2 & B3 & B4).
  repeat split; try assumption.
  apply (proj2 (mmap_kernel_spec na nr ms mo x8 _ Hno Hlen H2 H3 H5 Hdecl)). right.
  exists (Z_to_bv 64 aZ). split; [|reflexivity]. repeat split; assumption.
Qed.


(* [comment removed for export] *)
Lemma region_free_not_in : forall maps (a n x : word),
  region_free maps a n = true ->
  (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)%Z ->
  in_rangesb x maps = false.
Proof.
  intros maps a n x Hf Hx. apply in_rangesb_false. intros lo sz Hin Hr.
  pose proof (State.region_free_In maps a n lo sz Hf Hin) as Hov.
  unfold iv_overlap in Hov. apply andb_false_iff in Hov.
  destruct Hov as [D | D]; apply Z.ltb_ge in D; lia.
Qed.

(* [comment removed for export] *)
Lemma lzok_after_grant : forall (na nr : bool) (flags : word) L S Zr msF mo (a n : word),
  lzok segs L S Zr (mkCfg msF mo) ->
  mmap_noreserve_b flags = nr ->
  let h := m_vmmaps mo in
  region_free (vm_maps h) a n = true ->
  (nr = true -> lazy_range_okb segs (a, n) = true) ->
  lazy_interior a n = [(a, n)] ->
  let mo' := grant_model flags a n na mo in
  (eager_used mo' + pages_total S * page_size <= vm_limit h)%Z ->
  let L' := (if nr then [(a, n)] else []) ++ L in
  let Zr' := (if nr && negb na then [(a, n)] else []) ++ Zr in
  let msF' := advance_past_svc (apply_effect msF (keff na a n)) in
  lzok segs L' S Zr' (mkCfg msF' mo')
  /\ restrict L' S msF'
     = sysret (restrict L S msF) a
         (if na || nr then unfill a n (ms_mem (restrict L S msF))
          else zfill a n (ms_mem (restrict L S msF)))
  /\ hid_same L S msF msF'.
Proof.
  intros na nr flags L S Zr msF mo a n Hok Hfl. cbv zeta. intros Hfree Hrok Hli Hbud.
  destruct Hok as [HL Hinv Hh HZ HSZ HZL HLM]. cbn in *.
  (* [comment removed for export] *)
  assert (Hnew : forall x, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)%Z ->
                 in_rangesb x L = false /\ in_rangesb x S = false /\ in_rangesb x Zr = false).
  { intros x Hx. pose proof (region_free_not_in _ a n x Hfree Hx) as HM.
    assert (HxL : in_rangesb x L = false).
    { destruct (in_rangesb x L) eqn:E; [|reflexivity]. rewrite (HLM x E) in HM. discriminate. }
    assert (HxZ : in_rangesb x Zr = false).
    { destruct (in_rangesb x Zr) eqn:E; [|reflexivity]. rewrite (HZL x E) in HxL. discriminate. }
    assert (HxS : in_rangesb x S = false).
    { destruct (in_rangesb x S) eqn:E; [|reflexivity]. rewrite (HSZ x E) in HxZ. discriminate. }
    auto. }
  assert (Hold : forall x, in_rangesb x L = true ->
                 ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)%Z).
  { intros x HxL Hx. destruct (Hnew x Hx) as (E & _). rewrite E in HxL. discriminate. }
  (* [comment removed for export] *)
  assert (Elazy : m_vm_lazy (grant_model flags a n na mo) = (if nr then [(a, n)] else []) ++ L).
  { rewrite grant_model_lazy, Hli, Hfl. rewrite (li_lazy _ _ _ Hinv). reflexivity. }
  assert (Emat : m_vm_materialized (grant_model flags a n na mo) = m_vm_materialized mo)
    by apply grant_model_materialized.
  assert (Emaps : m_vmmaps (grant_model flags a n na mo) = grant_vmmaps (m_vmmaps mo) a n na)
    by apply grant_model_vmmaps.
  (* [comment removed for export] *)
  assert (Emem : ms_mem (apply_effect msF (keff na a n))
                 = if na then unfill a n (ms_mem msF) else zfill a n (ms_mem msF)).
  { destruct na; [apply apply_effect_mem_unmaps | apply apply_effect_mem_zeros]. }
  assert (Hmem_old : forall x, ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)%Z ->
                     ms_mem (apply_effect msF (keff na a n)) x = ms_mem msF x).
  { intros x Hx. rewrite Emem. destruct na; [apply unfill_out | apply zfill_out]; lia. }
  split; [|split].
  - (* [comment removed for export] *) split; cbn.
    + destruct nr; [|exact HL]. cbn [app]. apply (proj2 (lazy_ranges_okb_cons segs (a, n) L)).
      split; [exact (Hrok eq_refl) | exact HL].
    + split.
      * exact Elazy.
      * rewrite Emat. exact (li_nodup _ _ _ Hinv).
      * rewrite Emat. exact (li_incl _ _ _ Hinv).
      * rewrite Emaps. cbn. exact Hbud.
    + unfold grant_model. destruct (with_mmap_backing_nonvm flags a n
          (with_vmmaps (grant_vmmaps (m_vmmaps mo) a n na) mo)) as (_ & _ & _ & Hp & _).
      unfold m_halted in *. rewrite Hp. cbn. exact Hh.
    + intros x Hx Hz. cbn [ms_mem advance_past_svc].
      destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge];
      [| destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + bv_unsigned n)) as [Hlt2|Hge2]].
      * (* [comment removed for export] *) rewrite Hmem_old by lia.
        assert (HxL : hiddenb L S x = true).
        { destruct nr; [|exact Hx]. cbn [app] in Hx. rewrite hiddenb_cons_lazy in Hx.
          apply orb_true_iff in Hx. destruct Hx as [Hx|Hx]; [|exact Hx].
          apply andb_true_iff in Hx. destruct Hx as [Hx _]. unfold zin_rangeb in Hx. cbn [fst snd] in Hx.
          apply andb_true_iff in Hx. destruct Hx as [Hx _]. apply Z.leb_le in Hx. lia. }
        apply HZ; [exact HxL|].
        destruct nr, na; cbn [andb negb app] in Hz; try exact Hz;
          rewrite in_rangesb_cons in Hz; apply orb_true_iff in Hz; destruct Hz as [Hz|Hz]; try exact Hz;
          unfold zin_rangeb in Hz; cbn [fst snd] in Hz; apply andb_true_iff in Hz; destruct Hz as [Hz _];
          apply Z.leb_le in Hz; lia.
      * (* [comment removed for export] *)
        destruct (Hnew x ltac:(lia)) as (ExL & ExS & ExZ).
        destruct nr, na; cbn [andb negb app] in Hz, Hx.
        -- rewrite ExZ in Hz. discriminate.
        -- rewrite Emem. unfold zfill, zmem.
           rewrite (proj2 (Z.leb_le _ _) Hge), (proj2 (Z.ltb_lt _ _) Hlt2). reflexivity.
        -- rewrite ExZ in Hz. discriminate.
        -- rewrite ExZ in Hz. discriminate.
      * (* [comment removed for export] *) rewrite Hmem_old by lia.
        assert (HxL : hiddenb L S x = true).
        { destruct nr; [|exact Hx]. cbn [app] in Hx. rewrite hiddenb_cons_lazy in Hx.
          apply orb_true_iff in Hx. destruct Hx as [Hx|Hx]; [|exact Hx].
          apply andb_true_iff in Hx. destruct Hx as [Hx _]. unfold zin_rangeb in Hx. cbn [fst snd] in Hx.
          apply andb_true_iff in Hx. destruct Hx as [_ Hx]. apply Z.ltb_lt in Hx. lia. }
        apply HZ; [exact HxL|].
        destruct nr, na; cbn [andb negb app] in Hz; try exact Hz;
          rewrite in_rangesb_cons in Hz; apply orb_true_iff in Hz; destruct Hz as [Hz|Hz]; try exact Hz;
          unfold zin_rangeb in Hz; cbn [fst snd] in Hz; apply andb_true_iff in Hz; destruct Hz as [_ Hz];
          apply Z.ltb_lt in Hz; lia.
    + (* [comment removed for export] *) destruct nr, na; cbn [andb negb app]; try exact HSZ. apply rsub_cons_r. exact HSZ.
    + (* [comment removed for export] *) destruct nr, na; cbn [andb negb app]; try exact HZL.
      * apply rsub_cons_r. exact HZL.
      * apply rsub_cons_2. exact HZL.
    + (* [comment removed for export] *) rewrite Emaps. cbn. destruct nr; cbn [app].
      * apply rsub_cons_2. exact HLM.
      * apply rsub_cons_r. exact HLM.
  - (* [comment removed for export] *)
    rewrite (restrict_sysret L S). rewrite keff_ret. f_equal.
    apply functional_extensionality. intros x. rewrite Emem.
    unfold restrict_mem, restrict_mem_by.
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge];
    [| destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + bv_unsigned n)) as [Hlt2|Hge2]].
    + (* [comment removed for export] *)
      assert (Ehid : hiddenb ((if nr then [(a, n)] else []) ++ L) S x = hiddenb L S x).
      { destruct nr; [|reflexivity]. cbn [app]. rewrite hiddenb_cons_lazy.
        unfold zin_rangeb. cbn [fst snd].
        replace (bv_unsigned a <=? bv_unsigned x)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
      rewrite Ehid. cbn [ms_mem restrict restrict_by with_mem restrict_mem_by].
      destruct na, nr; cbn [orb]; unfold unfill, zfill, zmem;
        replace (bv_unsigned a <=? bv_unsigned x)%Z with false by (symmetry; apply Z.leb_gt; lia); cbn [andb];
        reflexivity.
    + (* [comment removed for export] *)
      destruct (Hnew x ltac:(lia)) as (ExL & ExS & ExZ).
      cbn [ms_mem restrict restrict_by with_mem restrict_mem_by].
      destruct na, nr; cbn [orb app]; unfold unfill, zfill, zmem;
        rewrite ?hiddenb_cons_lazy; unfold zin_rangeb; cbn [fst snd];
        rewrite (proj2 (Z.leb_le _ _) Hge), (proj2 (Z.ltb_lt _ _) Hlt2), ?ExS; cbn [andb orb negb];
        try reflexivity.
      all: unfold hiddenb; rewrite ExL; reflexivity.
    + (* [comment removed for export] *)
      assert (Ehid : hiddenb ((if nr then [(a, n)] else []) ++ L) S x = hiddenb L S x).
      { destruct nr; [|reflexivity]. cbn [app]. rewrite hiddenb_cons_lazy.
        unfold zin_rangeb. cbn [fst snd].
        replace (bv_unsigned x <? bv_unsigned a + bv_unsigned n)%Z with false by (symmetry; apply Z.ltb_ge; lia).
        rewrite andb_false_r. reflexivity. }
      rewrite Ehid. cbn [ms_mem restrict restrict_by with_mem restrict_mem_by].
      destruct na, nr; cbn [orb]; unfold unfill, zfill, zmem;
        replace (bv_unsigned x <? bv_unsigned a + bv_unsigned n)%Z with false by (symmetry; apply Z.ltb_ge; lia);
        rewrite ?andb_false_r; reflexivity.
  - (* [comment removed for export] *) apply hid_frame_sysret. intros x Hx. apply Hmem_old.
    apply Hold. apply hiddenb_true_iff in Hx. tauto.
Qed.


Lemma ms_gpr_restrict : forall L S ms k, ms_gpr (restrict L S ms) k = ms_gpr ms k.
Proof. reflexivity. Qed.

Lemma grant_model_halted : forall flags a n na m, m_halted (grant_model flags a n na m) = m_halted m.
Proof.
  intros flags a n na m. unfold grant_model.
  destruct (with_mmap_backing_nonvm flags a n (with_vmmaps (grant_vmmaps (m_vmmaps m) a n na) m)) as (_ & _ & _ & Hp & _).
  unfold m_halted. rewrite Hp. destruct m; reflexivity.
Qed.

Lemma page_round_up_n_facts : forall (len : word),
  len <> Z_to_bv 64 0 ->
  let nZ := page_round_up_Z (bv_unsigned len) in
  (nZ < 2^64)%Z ->
  (0 < nZ)%Z /\ (nZ mod page_size = 0)%Z /\ bv_unsigned (Z_to_bv 64 nZ) = nZ.
Proof.
  intros len Hlen. cbv zeta. intros Hce.
  pose proof (PlacementSearch.page_round_up_Z_ge (bv_unsigned len)) as Hge. pose proof (word_unsigned_range len) as Hr.
  assert (bv_unsigned len <> 0%Z).
  { intros E. apply Hlen. apply bv_eq. rewrite E. reflexivity. }
  split; [lia|]. split; [apply PlacementSearch.page_round_up_Z_aligned|].
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.
Scheme kc__5 := Elimination for Corelib.Init.Specif.sig Sort Prop.

(* [comment removed for export] *)
Theorem sreach_mmap_kernel_lazy : forall (na nr : bool) L S Zr msF ms mo x8 (Q : config -> Prop),
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = ms ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 (kprot na) -> ms_gpr ms 3 = Z_to_bv 64 (kflags nr) ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (* 727298f3 (#144/#146): the decline, carried up to where the caller fixes
     the hint. *)
  place_declined_b (m_kernel mo) (m_vmmaps mo) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  entries_nowrap (vm_maps h) ->
  (na = false -> nr = false -> (eager_used mo + pages_total S * page_size + nZ <= vm_limit h)%Z) ->
  (* #38, THE ONE CONTRACT CHANGE IN THIS THEOREM: the GAP witness must also
     fit in one of Linux's two search windows.  Old text, unchanged, is the
     first four conjuncts; the fifth is new and is the weakest premise
     [Checks.Placement.linux_place_exists] consumes, so it pins no kernel
     field.  The CONTINUATION below is untouched, so no consumer of this
     theorem's conclusion changes. *)
  (exists g : word, (bv_unsigned g mod page_size = 0)%Z /\ (0 < bv_unsigned g)%Z
                    /\ (bv_unsigned g + nZ <= alloc_top h)%Z
                    /\ region_free (vm_reserved h ++ vm_maps h) g n = true
                    /\ ((bv_unsigned g + nZ <= mmap_top h)%Z \/ (task_unmapped_base <= bv_unsigned g)%Z)) ->
  (nr = true -> forall a : word, region_free (vm_reserved h) a n = true ->
                (bv_unsigned a + nZ <= alloc_top h)%Z -> lazy_range_okb segs (a, n) = true) ->
  (forall (a : word) (msF' : machine_state),
     (bv_unsigned a mod page_size = 0)%Z -> (0 < bv_unsigned a)%Z -> (bv_unsigned a + nZ <= alloc_top h)%Z ->
     region_free (vm_reserved h ++ vm_maps h) a n = true ->
     let mo' := grant_model (Z_to_bv 64 (kflags nr)) a n na mo in
     lzok segs ((if nr then [(a, n)] else []) ++ L) S ((if nr && negb na then [(a, n)] else []) ++ Zr)
          (mkCfg msF' mo') ->
     restrict ((if nr then [(a, n)] else []) ++ L) S msF'
       = sysret ms a (if na || nr then unfill a n (ms_mem ms) else zfill a n (ms_mem ms)) ->
     hid_same L S msF msF' ->
     (eager_used mo' <= eager_used mo + (if na || nr then 0 else nZ))%Z ->
     sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros na nr L S Zr msF ms mo x8 Q Hok Hr Hsvc Hno. cbv zeta.
  intros Hlen H2 H3 H4 H5 Hdecl Hnw Hbud (g & Hgal & Hgpos & Hgce & Hgfree & Hgwin) Hrok Hk.
  subst ms. rewrite restrict_svc in Hsvc. rewrite !ms_gpr_restrict in *.
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr msF 1))) in *.
  set (n := Z_to_bv 64 nZ) in *.
  pose proof (alloc_top_lt (m_vmmaps mo)) as Htop.
  destruct (page_round_up_n_facts (ms_gpr msF 1) Hlen ltac:(pose proof (word_unsigned_range g); unfold two_pow_64 in Htop; lia)) as (HnZpos & HnZal & Hun).
  fold nZ in HnZpos, HnZal, Hun. fold n in Hun.
  pose proof (lzok_backing_used_le segs L S Zr _ Hok) as Hbk. cbn [cfg_model] in Hbk.
  pose proof (li_budget _ _ _ (lzok_inv Hok)) as Hli. cbn [cfg_model] in Hli.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs msF x8)) = 222%Z) by (rewrite in_sysno_sys_input; exact Hno).
  (* [comment removed for export] *)
  assert (Hbk' : na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (kflags nr)) mo nZ = true).
  { intros ->. unfold mmap_noreserve_backed_ok. destruct (kgates false nr) as (_ & _ & _ & _ & ->).
    destruct nr; [reflexivity|]. specialize (Hbud eq_refl eq_refl). apply Z.leb_le. lia. }
  (* [comment removed for export] *)
  pose (I := {a : word | (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
                         /\ (bv_unsigned a + nZ <= alloc_top (m_vmmaps mo))%Z
                         /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a n = true
                         /\ (na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (kflags nr)) mo nZ = true)
                         /\ Placement.linux_place_is (m_vmmaps mo) (kb_thp (m_kernel mo)) (ms_gpr msF 0) nZ a = true}).
  pose (effs := fun i : I => keff na (proj1_sig i) n).
  pose (ms' := fun i : I => grant_model (Z_to_bv 64 (kflags nr)) (proj1_sig i) n na mo).
  (* #38: [I] now carries Linux's placement, so the address that inhabits it is
     no longer the caller's GAP witness [g] -- an admissible address is not
     Linux's -- but the one LINUX chooses for a request of this size.
     [mmap_kernel_grant_exists] produces it from [g] plus the new window
     conjunct, carrying the SAME four admissibility facts [g] carried, which is
     why everything below this point reads exactly what it read before. *)
  destruct (mmap_kernel_grant_exists na nr msF mo x8 g Hno Hlen H2 H3 H5 Hdecl
              Hgal Hgpos Hgce Hgfree Hgwin Hbk')
    as (g' & Hg'al & Hg'pos & Hg'ce & Hg'free & Hg'pl & Hg'sys).
  assert (Hg : (bv_unsigned g' mod page_size = 0)%Z /\ (0 < bv_unsigned g')%Z
               /\ (bv_unsigned g' + nZ <= alloc_top (m_vmmaps mo))%Z
               /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) g' n = true
               /\ (na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (kflags nr)) mo nZ = true)
               /\ Placement.linux_place_is (m_vmmaps mo) (kb_thp (m_kernel mo)) (ms_gpr msF 0) nZ g' = true).
  { repeat split; assumption. }
  assert (Hplace : forall a, (bv_unsigned a mod page_size = 0)%Z -> (0 < bv_unsigned a)%Z ->
                   (bv_unsigned a + nZ <= alloc_top (m_vmmaps mo))%Z ->
                   region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a n = true ->
                   refusal_b (sys_input segs msF x8) mo a = false).
  { intros a A1 A2 A3 A4. apply (place_not_refusal (sys_input segs msF x8) mo a nZ Hno'); [|lia].
    apply place_ok_intro; assumption. }
  assert (Hnode : node_ok segs (mkCfg msF mo) I (fun _ => [])
                    (fun i => mkCfg (advance_past_svc (apply_effect msF (effs i))) (ms' i))).
  { apply (node_family_noacc_cfg msF mo x8 I effs ms' (fun _ => []) _ (lzok_halted Hok) Hsvc
             (fun o => mmap_kernel_spec na nr msF mo x8 o Hno Hlen H2 H3 H5 Hdecl)).
    - intros [a Ha]. right. exists a. split; [exact Ha | reflexivity].
    - intros [a (A1 & A2 & A3 & A4 & A5 & A6)]. apply spurious_refusal_not_refusal. unfold effs. cbn [proj1_sig].
      rewrite keff_ret. apply Hplace; assumption.
    - intros eff m' ev [He | (a & Ha & E)] Hns.
      + exfalso. apply Hns. apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->).
        apply (alloc_refusal_spurious _ mo _ (keff na g' n) (grant_model (Z_to_bv 64 (kflags nr)) g' n na mo) []).
        * apply family_off_mmap_true. exact Hno'.
        * cbn [eff_ret]. apply errno_is_refusal_mmap. exact Hno'.
        * exact Hg'sys.
        * rewrite keff_ret. apply Hplace; assumption.
      + apply Ok_inj in E as (-> & -> & ->). exists (exist _ a Ha). auto.
    - intros eff m' ev [He | (a & _ & E)].
      + apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->). exact (lzok_halted Hok).
      + apply Ok_inj in E as (-> & -> & ->). rewrite grant_model_halted. exact (lzok_halted Hok).
    - intros [He | (a & _ & E)]; [apply mmap_err_out_enomem in He; discriminate He | discriminate E].
    - intros i. apply keff_accesses. }
  apply (sreach_node segs _ I _ (exist _ g' Hg) _ Hnode
           (RomBase.sys_rob_memfree segs msF mo x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_222))).
  intros [a (Hal & Hpos & Hce & Hfree & Ha5 & Ha6)]. cbn [proj1_sig].
  (* [comment removed for export] *)
  assert (Hli' : lazy_interior a n = [(a, n)]).
  { apply lazy_interior_aligned; [exact Hal | rewrite Hun; exact HnZal | rewrite Hun; exact HnZpos]. }
  assert (He : entry_nowrap (a, n)).
  { unfold entry_nowrap, hi. cbn [fst snd]. rewrite Hun. unfold two_pow_64 in Htop. lia. }
  assert (Heag : (eager_used (grant_model (Z_to_bv 64 (kflags nr)) a n na mo)
                  <= eager_used mo + (if na || nr then 0 else nZ))%Z).
  { destruct (kgates na nr) as (_ & _ & _ & _ & Gb).
    destruct na; [|destruct nr]; cbn [orb].
    - pose proof (eager_used_grant_covered_le (Z_to_bv 64 (kflags nr)) a n true mo Hnw He (or_introl eq_refl)). lia.
    - pose proof (eager_used_grant_covered_le (Z_to_bv 64 (kflags true)) a n false mo Hnw He (or_intror (conj Gb Hli'))). lia.
    - rewrite <- Hun. apply (eager_used_grant_rw_le (Z_to_bv 64 (kflags false)) a n mo Gb Hnw He). }
  assert (Hbud' : (eager_used (grant_model (Z_to_bv 64 (kflags nr)) a n na mo) + pages_total S * page_size
                   <= vm_limit (m_vmmaps mo))%Z).
  { destruct na; [|destruct nr]; cbn [orb] in Heag; [lia | lia |]. specialize (Hbud eq_refl eq_refl). lia. }
  destruct (lzok_after_grant na nr (Z_to_bv 64 (kflags nr)) L S Zr msF mo a n Hok (proj2 (proj2 (proj2 (proj2 (kgates na nr)))))
              (region_free_app_r _ _ _ _ Hfree)
              (fun Hnr => Hrok Hnr a (region_free_app_l _ _ _ _ Hfree) Hce) Hli' Hbud')
    as (Hok' & Hvis & Hhs).
  apply (Hk a _ Hal Hpos Hce Hfree Hok' Hvis Hhs Heag).
Qed.



(* [comment removed for export] *)
Definition nrflags (nr : bool) : Z := if nr then 1064994 else 1048610.

Lemma fgates : forall (na nr : bool),
  mmap_off_aligned_b (Z_to_bv 64 0) = true
  /\ mmap_anon_b (Z_to_bv 64 (fflags nr)) = true
  /\ mmap_modeled_b (Z_to_bv 64 (kprot na)) (Z_to_bv 64 (fflags nr)) (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 (kprot na)) (Z_to_bv 64 (fflags nr)) (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 (kprot na)) (Z_to_bv 64 (fflags nr)) (Z_to_bv 64 0) = na
  /\ mmap_fixed_rw_b (Z_to_bv 64 (kprot na)) (Z_to_bv 64 (fflags nr)) (Z_to_bv 64 0) = negb na
  /\ mmap_noreserve_b (Z_to_bv 64 (fflags nr)) = nr.
Proof. intros [|] [|]; vm_compute; repeat split; reflexivity. Qed.

Lemma nrgates : forall (na nr : bool),
  mmap_off_aligned_b (Z_to_bv 64 0) = true
  /\ mmap_anon_b (Z_to_bv 64 (nrflags nr)) = true
  /\ mmap_modeled_b (Z_to_bv 64 (kprot na)) (Z_to_bv 64 (nrflags nr)) (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 (kprot na)) (Z_to_bv 64 (nrflags nr)) (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 (kprot na)) (Z_to_bv 64 (nrflags nr)) (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 (kprot na)) (Z_to_bv 64 (nrflags nr)) (Z_to_bv 64 0) = false
  /\ mmap_noreplace_noaccess_b (Z_to_bv 64 (kprot na)) (Z_to_bv 64 (nrflags nr)) (Z_to_bv 64 0) = na
  /\ mmap_noreplace_rw_b (Z_to_bv 64 (kprot na)) (Z_to_bv 64 (nrflags nr)) (Z_to_bv 64 0) = negb na
  /\ mmap_noreserve_b (Z_to_bv 64 (nrflags nr)) = nr.
Proof. intros [|] [|]; vm_compute; repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_fresh_spec : forall (na nr : bool) ms mo x8 o,
  bv_unsigned x8 = 222%Z ->
  let addr := ms_gpr ms 0 in
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 (kprot na) -> ms_gpr ms 3 = Z_to_bv 64 (fflags nr) ->
  ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h ++ vm_maps h) addr n = true ->
  syscall_spec (sys_input segs ms x8) mo o <->
  mmap_err_out mo o
  \/ ((na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (fflags nr)) mo nZ = true)
      /\ o = Ok (keff na addr n) (grant_model (Z_to_bv 64 (fflags nr)) addr n na mo) []).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.outcome); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Logic.not); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.kprot); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.fflags); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.alloc_top); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.region_free); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Init.Datatypes.prod); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.fgates); constr:(@Corelib.Init.Logic.and); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_off_aligned_b); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_anon_b); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_modeled_b); constr:(@Corelib.Init.Datatypes.false); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noaccess_b); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_noaccess_b); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_rw_b); constr:(@Corelib.Init.Datatypes.negb); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noreserve_b); constr:(@kc__1); constr:(@Corelib.Init.Logic.iff); constr:(@LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.sys_input); constr:(segs); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.mmap_err_out); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noreserve_backed_ok); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.Ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.keff); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyLedger.grant_model); constr:(@Corelib.Init.Datatypes.nil); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.event); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_spec); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.in_arg); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.syscall_spec_222); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.in_sysno); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ExitSim.in_sysno_sys_input); constr:(@kc__2); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.MemCopy); constr:(@Corelib.Init.Datatypes.nat); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.with_mmap_backing); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.with_vmmaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkVmMapsFull); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_start_brk); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_brk); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_limit); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_mmap_base); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.mmap_fixed_noaccess_fresh_outcome); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.w_is0_false); constr:(@Corelib.Init.Logic.conj); constr:(@kc__3); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Logic.False_ind); constr:(@Corelib.Init.Logic.proj2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.mmap_fixed_rw_fresh_outcome); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MmapSim.in_arg5_sys_input); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MmapSim.in_arg4_sys_input); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MmapSim.in_arg3_sys_input); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.in_arg2_sys_input'); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.in_arg1_sys_input'); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ExitSim.in_arg0_sys_input); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.VmMaps)|] [|@lemma; @b; @Gfr; @Gfn; @Gn; @Gm; @H2; @He; @e; @H0; @H; @Ho; @Hb; @Gb; @Ga; @Go; @a; @Hfree; @Hpos; @Hal; @Hce; @H5; @H3; @Hlen; @h; @n; @nZ; @len; @addr; @Hno; @o; @x8; @mo; @ms; @nr; @na|] "#0W#W$e#Z##$'#}#H#F#b#k#M$1#L#K#$#1#B#J#6#A#N#3#9#=#E#2#D#5#:#>#C#I#.#7#;#?#G#O#P#(#0#4#@#W#S#*#/#<#Q#d#'#m#+#,#8#&#R#-$.#%$V#T#z$>$<$=#`#^#]#h#)#q#s#p#u#v#w#y#x$[#U#a#f#~$$$9$A$B$?$E$H$I$T$S$Z$Y$\$]$^$_#V$C$`$a$b$c$d$e$f#\#[#c#l$##i#o#e#n$2#r$5$*$+$,$)$F$4$:$($3$6$7$&$;$0$D$L$K$J$@#t#{#|$/#_$-$G$M$N$O$P$Q$R$%#g#j$8$U$W$XU$4&$5%$6%$7%$8$$9%$:$$;%$<$$='#[%$>&$?$$@$$A&$B&$C&$D,$E&$F%$G&$H($I&$J%$K&$L)$M+$N%$O'$P)$Q$$R$$S$$T&$U$$V($W'$X$$Y$$Z$$[$$\$$]$$^$$_$$`$$a$$b'$c&$d&ESSE#E#E#E#E#UST#USU#USbI(%OOSSE#O#O#O#O#E#USc##SB+#PJ&SC#$1SD#1$#USV#P'&S8#)S>$7##7%#P'&SW#'S>$<##<%#P'P#&S>##@#2&SEJ(s###&SE7(s#%#+#VSX&#AS>USY#VSZ%#&SFJ(s#,#VS[#S\#SB#SD&SJJ(s#0#VS]SD#VSOs#1s#1ASJB#C$WS^&$#&S1J&S1s#+(s#9#+#$s#;#WS_('##C#FVSdPS9USes#0#C#F'S9$s#B#N##C#F)P$s#F#9#'s#8#C#E5%)s#:#C#E1'+s#<#C#P.)-s#>/P#C$#00#C#S9%%#%)#%,#%/#%4#%9#'P$s#Y#N##C#F)S*$s#]#9#'s#O#C#E5%)s#Q#C#E1'+s#S#C#S*.)-s#U/S*#C$#00#C#P%%#%)#%,#%/#%4#%s#0#;LPS?D#S9S16S9S1#CS&E'S&$s#t#&S*s#h(s#v#+#3&P##C#Fk##*#&PJ&Ps#o(s#}#+#$s$##7S&'#'S*$s$&#8#*&S&S9QSf,I'$##s$(S1#%/#*9#-;#j##>#N+#C#F)S&$s$2#9#/s$$#C#E5%1s$&#C#E1'3s$(#C#S&.)5s$*/S&#C$#08#C#S*%%#%)#%,#%/#%4#'S:$s$D#N##C#F)S,$s$H#9#'s$:#C#E5%)s$<#C#E1'+s$>#C#S,.)-s$@/S,#C$#00#C#S:%%#%)#%,#%/#%4#'S,$s$Z#N##C#F)S#$s$^#9#'s$P#C#E5%)s$R#C#E1'+s$T#C#S#.)-s$V/S##C$#00#C#S,%%#%)#%,#%/#%4#;LS,S&D#S:S*6S:S*#CS2E'S2$s$t#&S#s$h(s$v#+#3&S,##C#Fk##*#&S,J&S,s$o(s$}#+#$s%##7S2'#'S#$s%&#8#*&S2S:,I&#s#^#s%'S*#%.#*8#-:#j##=#)S2$s%/#9#,s$}#C#E5%.s%##C#E1'0s%%#C#S2.)2s%'/S2#C$#05#C#S#%%#%)#%,#%/#Ns#)#C#F)S'$s%B#'SG$s%D#9%#s%6#C#E5'%s%8#C#E1)'s%:#C#S'.+)s%</S'#C$#0,#C#SG%%#%)#%,#%/#)S-$s%U#'S'$s%W#9%#s%I#C#E5'%s%K#C#E1)'s%M#C#S-.+)s%O/S-#C$#0,#C#S'%%#%)#%,#%/#;LS'S2D#SGS#6SGS##CS3E'S3$s%l#&S-s%`(s%n#+#3&S'##C#Fk##*#&S'J&S's%g(s%u#+#$s%w#7S3'#'S-$s%z#8#*&S3SG,I&#s$V#s%{S##%.#*8#-:#j##=#)S3$s&'#5#,s%u#C#E1%.s%w#C#S3.'0s%y/S3#C$#03#C#S-%%#%)#%,#)S@$s&5#9#s#(s&'#C#E)S($s&9#'S@$s&;#5%#s&-#C#E1'%s&/#C#S(.)'s&1/S(#C$#0*#C#S@%%#%)#%,#)S.$s&I#'S($s&K#5%#s&=#C#E1'%s&?#C#S..)'s&A/S.#C$#0*#C#S(%%#%)#%,#;LS(S3D#S@S-6S@S-#CS4E'S4$s&]#&S.s&Q(s&_#+#3&S(##C#Fk##*#&S(J&S(s&X(s&f#+#$s&h#7S4'#'S.$s&k#8#*&S4S@,I&#s%G#s&lS-#%.#*8#-:#j##=#)S4$s&t#1#,s&f#C#S4.%.s&h/S4#C$#01#C#S.%%#%)#)S;$s'##5#s#%s&q#C#E)S$$s''#'S;$s')#1%#s&w#C#S$.'%s&y/S$#C$#0(#C#S;%%#%)#)Q$s'4#'S$$s'6#1%#s'(#C#Q.'%s'*/Q#C$#0(#C#S$%%#%)#;LS$S4D#S;S.6S;S.#CS/E'S/$s'E#&Qs'9(s'G#+#3&S$##C#Fk##*#&S$J&S$s'@(s'N#+#$s'P#7S/'#'Q$s'S#8#*&S/S;,I&#s&/#s'TS.#%.#*8#-:#j##=#)S/$s'\#.#,s'N/S/#C$#0/#C#Q%%#)S+$s'd#1#Bs'V#C#S+)S)$s'h#'S+$s'j#.%#s'\/S)#C$#0&#C#S+%%#)H$s'r#'S)$s't#.%#s'f/H#C$#0&#C#S)%%#;LS)S/D#S+Q6S+Q#CS5E'S5$s($#&Hs't(s(&#+#3&S)##C#Fk##*#&S)J&S)s'{(s(-#+#$s(/#7S5'#'H$s(2#8#*&S5S+,I&#s&j#s(3Q#%.#*8#-:#j##=#0*#C#H)G$s(=#.#<s(//G#C$#'G$s(B#0##C#G;LGHD#S5S):$J:%s(;:&s(7:'s(3:(s(/:)s(/4('&%$#*S5S)-*#;LS0S5D#GH:$J:%s(E:&s(A:'s(=:(s(9:)s(94('&%$#*GH6GH#CNE'N$s([#&Rs(O(s(]#+#3&S0##C#Fk##*#&S0J&S0s(V(s(d#+#$s(f#7N'#'R$s(i#8#*&NG,I&#s'E#s(jH#%.#*8#VSPS<#]SQS<SKSRB;D$$#j#$s#%#(s(rD#SB#s(hj#%s(s#USgs#2WShLGH@s(vH%S+$#XSis#5S5S)#&GJ4Ds#*s#)s#(s#'s#&s#-GH-#/j#%s({#&Gs(p4>Ds#-s#,s#+s#*s#1GH-#3j#%s)##&Gs(o4BADs#0s#/s#.s#5GH-#7j#%s)'#&Gs(n&S0s(t4s#'s#&#Ds#4s#3s#:GH-#<j#%s),#&Gs(n&S0s(t4s#,s#+(#Ds#8s#?GH-#Aj#%s)1#&Gs(r&S0s(t4s#1s#0-(#Ds#DGH-#s#&j#%s)6#)R$s)9#&S0s(y4s#7s#6D.)#s#JGH-#s#,j#%s)<#'S0$s)?#)N$s)A#4s#>s#=#D0*s#QGH-#s#3j#%s)C#4s#As#@&s#:3Ds#TGH-#s#6j#%s)F#)D$s)I##s)IB#)O$s)L#9#s#Ps)>#C#E)SL$s)P#'M$s)R#5%#s)D#C#E)SH$s)V#'K$s)X#1%#s)J#C#SH)SC$s)\#'S%$s)^#.%#s)P/SC#C$#&S%J&S%s)V)S8$s)e#'S6$s)g#&S%s)L;LS%M4*)'%$s)[#KN6KN#CS8E'S7$s)n#&S6s)b(s)p#+#3&S%##C#Fk##*#(s)u4+#$s)w#7S88#849$S8K,I$#s(T#s)yN#%*#*4#-6#k#&@#k#'s#(#k#(s#/#k#)s#6#k#*s#;#j#%C#)F$s**##s**s#d#9$s#}s)y#C#E5&s$1s){#C#E1(s#<s)}#C#F.*s#8s*#/F#C$#&KJ&Ks*)&Ks)w;LKN4&%1s#9$s**#MR6MRUSTs*?USU#USj#VSOs*=#Q#Qs)l(s*A-+#$s*C#Gs*Cs*C1#2s)q#'QSkVSOs*FSlQ#<6,+&%#AMB#C$2s)y+#H&2s){-#I(J)K*L+M,=,*('&%$#>#M?s#Ws#$6#,I1#s)2#s*WR#*B#-s#$#4s#Xs#Ws#4s#Ss#Rs*Ms#QKNGs*\s*\s#Ys#D2s*.#@<s#[BA#;9AKB#C$2s*3(#H&2s*5*#I(J)K*L+M,=,*('&%$#>#K?s#ds#is#T#,I1#s)H#s*mN#*s#c##CFEk###s#]7Fs#os#Z8s#ks#ps#[FK,I$#s)O#s*tN#%'#*s#k#VSPS<#]SQS<SKSR@,D$$#j#$B#VSms#HGgSns#Js#Is#Us#}s#Hs*ns#GMRS(S'#SHSLOS+S/QS$%.1*s#r#k##s#(#3s#xKs#i#C#Fk##4#%#s#-*s#M#k###86S%M'SA$s+-#&S7s*}(s+/#+#3&S6##C#Fk##@#&S6J$s+5s#~Gs+5s+5$#2s*c#s#U<&s#Ws#V#s#Ps#NAS%B#C$2s*h(#H&2s*j*#I(J)K*L+M,=,*('&%$#>#S%?s$643#,I1#s)}#s+FM#%8#*A#j##s#9#6S6K'SI$s+N#&SAs+B(s+P#+#3&S7##C#Fk##s#A#&S7J$s+Vs#(Gs+Vs+V$#2s+(#s#v<&s#xs#w#s#qs#oAS6B#C$2s+-(#H&2s+/*#I(J)K*L+M,=,*('&%$#>#S6?s#<43#,I1#s*B#s+gK#%8#SA#Dj#+s#C#U#Dj##s$a#nC#$#%S<D#%#So#S`j#,C#ZSpCF#SqED'S=$s+s#&SIs+g(s+u#+#3&SA##C#FVSr#Dl#-+S`#j#.s#h#Rs#*5#DTs#35#j#/s#8#U#Dj##s#o#ZSMs$ts#ps#85#Dj#.s$*#*s#Zs#=j##s#c#Ss#;>Dj#+s#]#U#Dj##s${#WSss#7BDTs#@s###j#/s#D#U#Dj##s#m#ZSMs%%s#n,(#Dj#.s#h#Rs#ns#h0#7Fs$^s$P8s%6s$_s$QFM,I$#s*m#s,6R#%s#p#*s$^#-s$?#m#*#Vs#|s#z#j#&s$h#j#'s$l#j#(s$o#j#)s$r#j#*s$u#)E$s,D##s,Ds%~#9$s&;s,7#C#E5&s&Ks,9#C#E1(s%Vs,;#C#E.*s%Rs,=/E#C$#4s$xs$w-s%Os$vs,@s$uMR3s%PMs$l#C#F<s${s$qs$ks$ps$js$h=s$fs$ds$cs$as$`s$_s$^s$]>#M?s%Us$~s$p#,I&#s+0#s,UR#%)#*s$}#--#4s%Ws%V9s%Rs%Qs,Ls%PKN<s%Xs${s$\s$zs$ts$r=s$Zs$Xs$Ws$Us$Ts$Ss$Rs$Q>#K?s%Vs%[s%F#,I&#s+:#s,_N#%s$>#*s%V##CEEk###s%P7Es%bs%M8s%^s%cs%NEK,I$#s+B#s,gN#%'#*s%^#VSPS<#]SQS<SKSR4,D$$#j#$6#hSts%<s%;s#-s%os%:s,`s%9MRS(S's$QSHSLODS+S/QS$%-1*s%d#k##;#k##1s$O%#?*s%=#k###5k##5s$G<s$Fs%;s$Cs%:s%4s%2=s$As$?s$>s$<s$;s$:s$9s$8>#S%?s%ks$Is$H#,I&#s+V#s,{M#%)#*s$V#j##?#k##?s$0<s$/s%Es$,s%Ds%>s%<=s$*s$(s$'s$%s$$s$#s#~s#}>#S6?s$Zs$2s$1#,I&#s+`#s-)K#%)#Ss$?#Dj#+s$a#U#Dj##s&##%s%x2%s$^)6S7S%k##s#.s#v&SAJ$s-6s$CGs-6s-6$#2s,d#s%V<&s%X#s%Ws%Qs%OAS7B#C$2s,i(#H&I'J(K)L*M+=+)('&%$#>#S7?s$V32#,I0#s+}#s-FS%#%7#*9#j##;#&S=J&S=s-@(s-N#+#$s-P#Gs-Ps-P'#2s,~#s%p<)s%r#s%qs%ks%i'SN$s-U#ASIB#C$2s-)*#H&I'J(K)L*M+=+)('&%$#>#SI?/84#,I2#s,=#s-bS7#6S=SA'Su$s-g#&Sas-[(s-i#+#3&SN##C#Fk##s#g#&SNJ&SNs-b(s-p#+#$s-r#Gs-rs-r'#2s-D#s&6<)s&8#s&7s&1s&/'Sa$s-w#AS=B#C$2s-K*#H&I'J(K)L*M+=+)('&%$#>#S=?/84#,I2#s,_#s.(SA#%<#j#.s$&SLR>%#DTs#'%#j#/s#)#j#0s$r#V#ODj##s#H#j##s%_#Fs%`s#gs#G#Dj#.s#b#U#Dj##s$3#ZSMs'+s$4s#rs#f#Dj#.s$>#*s%ms#gj##s$(#Ss%Ns#hDj#+s%p#U#Dj##s'2#%s%Ks#V*s#l#j##s#t#3s#LSIs#R#C#Fk##s$?#3s#-S=s#3#C#F%#@UOSER%B#DTs#D%#j#/s#F#j#0*#V#ODj##s#e#j##s$-#Fs$.s$(1#Dj#.s$2#U#Dj##s$B#ZSMs'Hs$C<8#Dj#.s$?#Rs$Cs$?@#-s$]s$Am#$#7Es''s&u8s'[s'(s&vEM,I$#s-6#s.[R#%s$I#*s''#-s$e#m#*#Vs$Rs$Q#j#&s$s#j#'s$w#j#(s$z#j#)s$}#j#*s%$#XSvs'Bs%(#RY#QS9SFS8O@s.is.[s(%#s(9S;@s.js(.s()#s(DS$@s.ks(5s(1#s(IQWSwLGH@s.ms(=s(9$s)$#WSxLGH@s.os(Ds(@$s)'#WSyLGH@s.qs(Ks(G$s)*#VSzGH@s.ss(Qs(N$s)-#VS{GH@s.us(Ws(T$s)0#WS|LGH@s.ws(]s(Z$s)3#Vs(fs(_#j#1s)8#j#&s)=#V#ODj##s)D#j##s)e#Fs)fs)ds)H#Dj#.s)n#j#'s)y#V#ODj##s*##j##s*N#Fs*Os*Is*-#Dj#.s*V#j#(s*d#V#ODj##s*j#j##s+?#Fs+@s+7s*w#Dj#.s+G#j#)s+X#V#ODj##s+^#j##s,9#Fs,:s,.s+n#Dj#.s,A#j#2s,U#V#ODj##s,Y#j##s-<#Fs-=s-,s,l#Dj#.s-B#j#3s.[#V#ODj##s-[#j##s.^#Fs._s.2s-q#Dl#4s.bs.I#j#5s.d#j#6s.q#j#7s.u#j#8s.z#j#9s/(#j#:s/-#j#*s/3#j#;s/9#&SCJ&S8s/?+s)9$s/ND#s/NSHs/@USV#&SJs/?)S?$s/S##s/S%#&S1s/>'S?$s/W##s/W%#&S?s/<#s/Y#s/K(s/[SEVSX#SWUSYSCVSZ$#(s/_SFVS[#S\#SB#SD(s/bSJVS]SD#BS>CS>WS^s/6$#WS_#S1SE#C#F;LS:S*D#S&P6S&P#CS#E3s-IS:S1#C#Fk##%#7S#S?SF8s-uS?SFS#S&,I$#s.L#s/qP#%'#*,#-.#k##1#k##7#k##:#k##>#k##s###k##s#&#k##s#+#k##s#0#l#<s/YS}#l#=s#4s0##l#>s#6SB#l#?s#8s0%#l#@s#:s0&#m#s#<#j#As/y#j#Bs0(#j#Cs0*#j#DS~#j#ET##j#FC#j#GC##"). Qed.

(* [comment removed for export] *)
Lemma mmap_noreplace_fresh_spec : forall (na nr : bool) ms mo x8 o,
  bv_unsigned x8 = 222%Z ->
  let addr := ms_gpr ms 0 in
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 (kprot na) -> ms_gpr ms 3 = Z_to_bv 64 (nrflags nr) ->
  ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h ++ vm_maps h) addr n = true ->
  syscall_spec (sys_input segs ms x8) mo o <->
  mmap_err_out mo o
  \/ ((na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (nrflags nr)) mo nZ = true)
      /\ o = Ok (keff na addr n) (grant_model (Z_to_bv 64 (nrflags nr)) addr n na mo) []).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.outcome); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Logic.not); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.kprot); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.nrflags); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.alloc_top); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.region_free); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Init.Datatypes.prod); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.nrgates); constr:(@Corelib.Init.Logic.and); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_off_aligned_b); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_anon_b); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_modeled_b); constr:(@Corelib.Init.Datatypes.false); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noaccess_b); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_noaccess_b); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_rw_b); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noreplace_noaccess_b); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noreplace_rw_b); constr:(@Corelib.Init.Datatypes.negb); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noreserve_b); constr:(@kc__1); constr:(@Corelib.Init.Logic.iff); constr:(@LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.sys_input); constr:(segs); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.mmap_err_out); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noreserve_backed_ok); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.Ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.keff); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyLedger.grant_model); constr:(@Corelib.Init.Datatypes.nil); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.event); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_spec); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.in_arg); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.syscall_spec_222); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.in_sysno); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ExitSim.in_sysno_sys_input); constr:(@kc__2); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.MemCopy); constr:(@Corelib.Init.Datatypes.nat); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.with_mmap_backing); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.with_vmmaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkVmMapsFull); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_start_brk); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_brk); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_limit); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_mmap_base); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.mmap_noreplace_noaccess_fresh_outcome); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.w_is0_false); constr:(@Corelib.Init.Logic.conj); constr:(@kc__3); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Logic.False_ind); constr:(@Corelib.Init.Logic.proj2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.mmap_noreplace_rw_fresh_outcome); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MmapSim.in_arg5_sys_input); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MmapSim.in_arg4_sys_input); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MmapSim.in_arg3_sys_input); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.in_arg2_sys_input'); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.in_arg1_sys_input'); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ExitSim.in_arg0_sys_input); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.VmMaps)|] [|@lemma; @b; @Gnr; @Gnn; @Gfr; @Gfn; @Gn; @Gm; @H2; @He; @e; @H0; @H; @Ho; @Hb; @Gb; @Ga; @Go; @a; @Hfree; @Hpos; @Hal; @Hce; @H5; @H3; @Hlen; @h; @n; @nZ; @len; @addr; @Hno; @o; @x8; @mo; @ms; @nr; @na|] "#3L#a$q#d$1##$+#P#N#l#u#W$=#$#V#1#M#6#X#3#J#U#2#C#G#I#L#T#*#5#9#:#=#>#A#B#E#F#K#Q#.#4#7#;#?#O#Y#Z#(#0#H#a#]#'#/#8#<#@#D#[#n#w#+#,#S#R#\#)#-$:#%#&$c$d$b#^$($J$H$I#j#h#g#r#{#}#z$#$$$%$'$&$g#_#k#p$,$.$E$M$N$K$Q$T$U$`$_$f$e$h$i$j$k#`$O$l$m$n$o$p$q$r#f#e#m$-#v#s#y#x#o#|$>$6$7$A$8$5$4$@$3$R$?$F$2$B$C$<$0$G$;$P$X$W$V$L$9#~$)$*#i$S$Y$Z$[$\$]$^$/#q#t$D$aU$@&$A%$B%$C%$D$$E$$F%$G$$H%$I&$J$$K'$L$#e%$M&$N&$O&$P&$Q&$R%$S,$T&$U&$V($W&$X&$Y%$Z&$[)$\+$]%$^'$_)$`($a$$b$$c$$d$$e'$f$$g$$h$$i$$j$$k$$l$$m$$n$$o$$p'HS`H#H#H#H#H#USa#USb#USnI)%MQS`H#Q#Q#Q#Q#H#USo##SL+#RJ&SE#%1SM#1$#USc#R'&S@#(S,%7##7%#R'&SS#'S,%<##<%#R'R#&S,##@#2&SNJ)s###&SN7)s#%#*#VSd&#ES,USe#VSf%#&SOJ)s#,#VSg#Sh#SL#SM&STJ)s#0#VSiSM#VS\s#1s#1ESTF#G$WSj&$#&S8J&S8s#+)s#9#*#%s#;#WSk('##C#FVSpOSAUSqs#0#C#F'SA%s#B#P##C#F(O%s#F#<#'s#8#C#D8%)s#:#C#D4'+s#<#C#D2)-s#>#C#D1+/s#@#C#O,-1s#B-O#C$#/4#C#SA$%#$)#$,#$/#$2#$5#$:#$?#'O%s#_#P##C#F(S&%s#c#<#'s#U#C#D8%)s#W#C#D4'+s#Y#C#D2)-s#[#C#D1+/s#]#C#S&,-1s#_-S&#C$#/4#C#O$%#$)#$,#$/#$2#$5#$:#$s#<#;LOSF>#SAS86SAS8#CS#D'S#%s$$#&S&s#t)s$&#*#3&O##C#Fk##*#&OJ&Os#{)s$-#*#%s$/#9S#'#'S&%s$2#:#*&S#SASSr.I'$##s$4S8#$/#+9#0;#j##>#P+#C#F(S#%s$>#<#/s$0#C#D8%1s$2#C#D4'3s$4#C#D2)5s$6#C#D1+7s$8#C#S#,-9s$:-S##C$#/<#C#S&$%#$)#$,#$/#$2#$5#$:#'S9%s$V#P##C#F(S-%s$Z#<#'s$L#C#D8%)s$N#C#D4'+s$P#C#D2)-s$R#C#D1+/s$T#C#S-,-1s$V-S-#C$#/4#C#S9$%#$)#$,#$/#$2#$5#$:#'S-%s$r#P##C#F(Q%s$v#<#'s$h#C#D8%)s$j#C#D4'+s$l#C#D2)-s$n#C#D1+/s$p#C#Q,-1s$r-Q#C$#/4#C#S-$%#$)#$,#$/#$2#$5#$:#;LS-S#>#S9S&6S9S&#CS:D'S:%s%6#&Qs%*)s%8#*#3&S-##C#Fk##*#&S-J&S-s%1)s%?#*#%s%A#9S:'#'Q%s%D#:#*&S:S9.I&#s#p#s%ES&#$.#+8#0:#j##=#(S:%s%M#<#,s%?#C#D8%.s%A#C#D4'0s%C#C#D2)2s%E#C#D1+4s%G#C#S:,-6s%I-S:#C$#/9#C#Q$%#$)#$,#$/#$2#$5#Ps#/#C#F(S.%s%f#'SG%s%h#<%#s%Z#C#D8'%s%\#C#D4)'s%^#C#D2+)s%`#C#D1-+s%b#C#S.,/-s%d-S.#C$#/0#C#SG$%#$)#$,#$/#$2#$5#(S/%s&##'S.%s&%#<%#s%s#C#D8'%s%u#C#D4)'s%w#C#D2+)s%y#C#D1-+s%{#C#S/,/-s%}-S/#C$#/0#C#S.$%#$)#$,#$/#$2#$5#;LS.S:>#SGQ6SGQ#CS;D'S;%s&@#&S/s&4)s&B#*#3&S.##C#Fk##*#&S.J&S.s&;)s&I#*#%s&K#9S;'#'S/%s&N#:#*&S;SG.I&#s$z#s&OQ#$.#+8#0:#j##=#(S;%s&W#8#,s&I#C#D4%.s&K#C#D2'0s&M#C#D1)2s&O#C#S;,+4s&Q-S;#C$#/7#C#S/$%#$)#$,#$/#$2#(SH%s&k#<#s#.s&]#C#D(S0%s&o#'SH%s&q#8%#s&c#C#D4'%s&e#C#D2)'s&g#C#D1+)s&i#C#S0,-+s&k-S0#C$#/.#C#SH$%#$)#$,#$/#$2#(S1%s')#'S0%s'+#8%#s&y#C#D4'%s&{#C#D2)'s&}#C#D1+)s'##C#S1,-+s'%-S1#C$#/.#C#S0$%#$)#$,#$/#$2#;LS0S;>#SHS/6SHS/#CS<D'S<%s'C#&S1s'7)s'E#*#3&S0##C#Fk##*#&S0J&S0s'>)s'L#*#%s'N#9S<'#'S1%s'Q#:#*&S<SH.I&#s%}#s'RS/#$.#+8#0:#j##=#(S<%s'Z#4#,s'L#C#D2%.s'N#C#D1'0s'P#C#S<,)2s'R-S<#C$#/5#C#S1$%#$)#$,#$/#(SI%s'k#8#s#+s']#C#D(S2%s'o#'SI%s'q#4%#s'c#C#D2'%s'e#C#D1)'s'g#C#S2,+)s'i-S2#C$#/,#C#SI$%#$)#$,#$/#(S3%s(&#'S2%s((#4%#s'v#C#D2'%s'x#C#D1)'s'z#C#S3,+)s'|-S3#C$#/,#C#S2$%#$)#$,#$/#;LS2S<>#SIS16SIS1#CS'D'S'%s(=#&S3s(1)s(?#*#3&S2##C#Fk##*#&S2J&S2s(8)s(F#*#%s(H#9S''#'S3%s(K#:#*&S'SI.I&#s&w#s(LS1#$.#+8#0:#j##=#(S'%s(T#2#,s(F#C#D1%.s(H#C#S','0s(J-S'#C$#/3#C#S3$%#$)#$,#(SJ%s(b#4#s#(s(T#C#D(S4%s(f#'SJ%s(h#2%#s(Z#C#D1'%s(\#C#S4,)'s(^-S4#C$#/*#C#SJ$%#$)#$,#(S5%s(v#'S4%s(x#2%#s(j#C#D1'%s(l#C#S5,)'s(n-S5#C$#/*#C#S4$%#$)#$,#;LS4S'>#SJS36SJS3#CS(D'S(%s).#&S5s(~)s)0#*#3&S4##C#Fk##*#&S4J&S4s)))s)7#*#%s)9#9S('#'S5%s)<#:#*&S(SJ.I&#s'h#s)=S3#$.#+8#0:#j##=#(S(%s)E#1#,s)7#C#S(,%.s)9-S(#C$#/1#C#S5$%#$)#(SB%s)P#2#s#%s)B#C#D(S)%s)T#'SB%s)V#1%#s)H#C#S),'%s)J-S)#C$#/(#C#SB$%#$)#(S$%s)a#'S)%s)c#1%#s)U#C#S$,'%s)W-S$#C$#/(#C#S)$%#$)#;LS)S(>#SBS56SBS5#CS6D'S6%s)r#&S$s)f)s)t#*#3&S)##C#Fk##*#&S)J&S)s)m)s){#*#%s)}#9S6'#'S$%s*$#:#*&S6SB.I&#s(P#s*%S5#$.#+8#0:#j##=#(S6%s*-#,#,s){-S6#C$#//#C#S$$%#(S*%s*5#1#Bs*'#C#S*(P%s*9#'S*%s*;#,%#s*--P#C$#/&#C#S*$%#(H%s*C#'P%s*E#,%#s*7-H#C$#/&#C#P$%#;LPS6>#S*S$6S*S$#CS=D'S=%s*Q#&Hs*E)s*S#*#3&P##C#Fk##*#&PJ&Ps*L)s*Z#*#%s*\#9S='#'H%s*_#:#*&S=S*.I&#s)/#s*`S$#$.#+8#0:#j##=#/*#C#H(G%s*j#,#<s*\-G#C$#'G%s*o#/##C#G;LGH>#S=P=$J=%s*h=&s*d='s*`=(s*\=)s*\7('&%$#*S=P0*#;LS7S=>#GH=$J=%s*r=&s*n='s*j=(s*f=)s*f7('&%$#*GH6GH#CSPD'SP%s+,#&SQs*|)s+.#*#3&S7##C#Fk##*#&S7J&S7s+')s+5#*#%s+7#9SP'#'SQ%s+:#:#*&SPG.I&#s)f#s+;H#$.#+8#VS]SC#]S^SCSUS_B;E$$#j#$s#%#)s+CE#SL#s+9j#%s+D#USss#2WStLGHCs+GH%S*$#XSus#5S=P#&GJ7Es#*s#)s#(s#'s#&s#-GH0#/j#%s+L#&Gs+A7>Es#-s#,s#+s#*s#1GH0#3j#%s+P#&Gs+@7BAEs#0s#/s#.s#5GH0#7j#%s+T#&Gs+?&S7s+E7s#'s#&#Es#4s#3s#:GH0#<j#%s+Y#&Gs+?&S7s+E7s#,s#+(#Es#8s#?GH0#Aj#%s+^#&Gs+C&S7s+E7s#1s#0-(#Es#DGH0#s#&j#%s+c#(SQ%s+f#&S7s+J7s#7s#6E.)#s#JGH0#s#,j#%s+i#'S7%s+l#(SP%s+n#7s#>s#=#E0*s#QGH0#s#3j#%s+p#7s#As#@&s#:3Es#TGH0#s#6j#%s+s#(E%s+v##s+vB#(M%s+y#<#s#Ps+k#C#D(SV%s+}#'S+%s,##8%#s+q#C#D(SW%s,'#'S%%s,)#4%#s+w#C#D(SE%s,-#'N%s,/#2%#s+}#C#D(S@%s,3#'K%s,5#1%#s,'#C#S@(SS%s,9#'R%s,;#,%#s,--SS#C$#&RJ&Rs,3'S>%s,B#&Rs,';LRN7('s,0%$s,6#KS%6KS%#CS,D'S?%s,I#&S>s,=)s,K#*#3&R##C#Fk##*#)s,P2*#%s,R#9S,6#:47$S,K.I$#s+##s,TS%#$*#+4#06#k#&>#k#'s#&#k#(s#-#k#)s#4#k#*s#;#k#+s#B#k#,s#G#j#%C#(F%s,c##s,cs#p#<$s$-s,V#C#D8&s$=s,X#C#D4(s#Hs,Z#C#D2*s#Ds,\#C#D1,s#@s,^#C#F,.s#<s,`-F#C$#&KJ&Ks,f&Ks,X;LKS%7&%5s#=$s,g#NS+6NS+USas,|USb#USv#VS\s,z#S#Ss,M)s,~-*#%s-$#Is-$s-$1#5s,R#'SSwVS\s-'SxS#?6,+&%#ENF#G$5s,Z+#J&5s,\-#K(L)M*N+O,@,*('&%$#A#NBs#[s#$6#.I1#s+c#s-8S+#+B#0s#$#7s#\s#[s#8s#Ys#Xs-.s#WKS%Is-=s-=s#]s#J5s,k#@?s#_BA#;9EKF#G$5s,p(#J&5s,r*#K(L)M*N+O,@,*('&%$#A#KBs#js#ms#Z#.I1#s+y#s-NS%#+s#i##CFDk###s#c9Fs#ss#`:s#qs#ts#aFK.I$#s,$#s-US%#$'#+s#q#VS]SC#]S^SCSUS_@,E$$#j#$B#VSys#HSQi#8Szs#Js#Is#Ys$%s#Hs-Os#GNS+S(S'#S@SESWSVMHPS*S6$.1+s#x#k##s#(#3s#~Ks#o#C#Fk##4#$#s#-+s#M#k###86RN'SK%s-j#&S?s-^)s-l#*#3&S>##C#Fk##@#&S>J%s-rs$(Is-rs-r$#5s-D#s#U?&s#Ws#V#s#Ps#NERF#G$5s-I(#J&5s-K*#K(L)M*N+O,@,*('&%$#A#RBs$<43#.I1#s,R#s.'N#$8#+A#j##s#9#6S>K'SR%s./#&SKs.#)s.1#*#3&S?##C#Fk##s#A#&S?J%s.7s#(Is.7s.7$#5s-e#s#v?&s#xs#w#s#qs#oES>F#G$5s-j(#J&5s-l*#K(L)M*N+O,@,*('&%$#A#S>Bs#<43#.I1#s,s#s.HK#$8#WSXA#Ej#-s#C#U#Ej##s$g#nC#$#%SCE#%#S{#Slj#.C#ZS|CF#S}DE'SD%s.T#&SRs.H)s.V#*#3&SK##C#FVS~#El#/+Sl#j#0s#h#Ts#*5#EWSYs#35#j#1s#8#U#Ej##s#o#ZSZs$zs#ps#85#Ej#0s$*#+s#Zs#=j##s#c#WSXs#;>Ej#-s#]#U#Ej##s%%#WT#s#7BEWSYs#@s###j#1s#D#U#Ej##s#m#ZSZs%+s#n,(#Ej#0s#h#Ts#ns#h0#9Fs$^s$P:s%:s$_s$QFN.I$#s-B#s.sS+#$s#p#+s$^#0s$?#m#*#Vs#|s#z#j#&s$h#j#'s$l#j#(s$o#j#)s$r#j#*s$u#j#+s$x#j#,s${#(D%s/'##s/'s&4#<$s&Ms.v#C#D8&s&]s.x#C#D4(s%hs.z#C#D2*s%ds.|#C#D1,s%`s.~#C#D,.s%\s/$-D#C$#7s$~s$}1s%Ys$|s/'s${NS+3s%ZNs$r#C#F?s%%s$ws$qs$vs$ps$n@s$ls$js$is$gs$fs$es$ds$cA#NBs%_s%(s$v#.I&#s-g#s/<S+#$)#+s%'#0-#7s%as%`=s%^s%]s/3s%\KS%?s%bs%%s$bs%$s$zs$x@s$`s$^s$]s$[s$Zs$Ys$Xs$WA#KBs%bs%es%R#.I&#s-q#s/FS%#$s$D#+s%b##CDDk###s%\9Ds%ls%Y:s%js%ms%ZDK.I$#s-y#s/NS%#$'#+s%j#VS]SC#]S^SCSUS_4,E$$#j#$6#i#9T$s%Bs%As#1s%ys%@s/Gs%?NS+S(S's$WS@SESWSVMEHPS*S6$-1+s%p#k##;#k##1s$U$#?+s%C#k###5k##5s$M?s$Ls%As$Is%@s%:s%8@s$Gs$Es$Ds$Bs$As$@s$?s$>A#RBs%ws$Os$N#.I&#s.1#s/bN#$)#+s$\#j##?#k##?s$6?s$5s%Ks$2s%Js%Ds%B@s$0s$.s$-s$+s$*s$)s$(s$'A#S>Bs$`s$8s$7#.I&#s.;#s/lK#$)#WSXs$E#Ej#-s$g#U#Ej##s&/#$s&(2$s$d)6S?Rk##s#.s#|&SKJ%s/ys$IIs/ys/y$#5s/K#s%\?&s%^#s%]s%Ws%UES?F#G$5s/P(#J&K'L(M)N*O+@+)('&%$#A#S?Bs$\32#.I0#s.X#s0-R#$7#+9#j##;#&SDJ&SDs0')s05#*#%s07#Is07s07'#5s/e#s%v?)s%x#s%ws%qs%o'S[%s0<#ESRF#G$5s/l*#J&K'L(M)N*O+@+)('&%$#A#SRB/84#.I2#s.t#s0IS?#6SDSK'T%%s0N#&Sms0B)s0P#*#3&S[##C#Fk##s#g#&S[J&S[s0I)s0W#*#%s0Y#Is0Ys0Y'#5s0+#s&<?)s&>#s&=s&7s&5'Sm%s0^#ESDF#G$5s02*#J&K'L(M)N*O+@+)('&%$#A#SDB/84#.I2#s/:#s0kSK#$<#j#0s$&SVT>%#EWSYs#'%#j#1s#)#j#2s$x#V#MEj##s#H#j##s%e#Ds%fs#gs#G#Ej#0s#b#U#Ej##s$3#ZSZs'7s$4s#rs#f#Ej#0s$>#+s%ss#gj##s$(#WSXs%Ts#hEj#-s%v#U#Ej##s'>#$s%Qs#V+s#l#j##s#t#3s#LSRs#R#C#Fk##s$?#3s#-SDs#3#C#F$#@UMSNT%B#EWSYs#D%#j#1s#F#j#2*#V#MEj##s#e#j##s$-#Ds$.s$(1#Ej#0s$2#U#Ej##s$B#ZSZs'Ts$C<8#Ej#0s$?#Ts$Cs$?@#0s$]s$Am#$#9Ds'-s&{:s'es'.s&|DN.I$#s/m#s1BS+#$s$I#+s'-#0s$e#m#*#Vs$Rs$Q#j#&s$s#j#'s$w#j#(s$z#j#)s$}#j#*s%$#j#+s%'#j#,s%*#XT&s'Ns%.#SQ[#S$SGS9SASOS@MCs1Rs1Ds(=#s(QSBCs1Ss(Fs(A#s(\S)Cs1Ts(Ms(I#s(aS$WT'LGHCs1Vs(Us(Q$s)<#WT(LGHCs1Xs(\s(X$s)?#WT)LGHCs1Zs(cs(_$s)B#VT*GHCs1\s(is(f$s)E#VT+GHCs1^s(os(l$s)H#WT,LGHCs1`s(us(r$s)K#Vs(~s(w#j#3s)P#j#&s)U#V#MEj##s)\#j##s)}#Ds)~s)|s)`#Ej#0s**#j#'s*5#V#MEj##s*;#j##s*f#Ds*gs*as*E#Ej#0s*n#j#(s*|#V#MEj##s+&#j##s+W#Ds+Xs+Os+3#Ej#0s+_#j#)s+p#V#MEj##s+v#j##s,Q#Ds,Rs,Fs,*#Ej#0s,Y#j#*s,m#V#MEj##s,s#j##s-T#Ds-Us-Fs-*#Ej#0s-\#j#+s-s#V#MEj##s-y#j##s.`#Ds.as.Os.3#Ej#0s.h#j#4s/&#V#MEj##s/*#j##s/u#Ds/vs/_s/C#Ej#0s/{#j#5s1P#V#MEj##s0>#j##s1S#Ds1Ts0ws0Z#El#6s1Ws18#j#7s1Y#j#8s1f#j#9s1j#j#:s1o#j#;s1y#j#<s1~#j#,s2(#j#=s2.#&SEJ&S@s24*s)]%s2CE#s2CSWs25USc#&STs24(SF%s2H##s2H%#&S8s23'SF%s2L##s2L%#&SFs21#s2N#s2@)s2PSNVSd#SSUSeSEVSf$#)s2TSOVSg#Sh#SL#SM)s2WSTVSiSM#FS,GS,WSjs2+$#WSk#S8SN#C#F;LS9S&>#S#O6S#O#CQD3s/|S9S8#C#Fk##%#9QSFSO:s0RSFSOQS#.I$#s15#s2fO#$'#+,#0.#k##1#k##7#k##:#k##>#k##s###k##s#&#k##s#+#k##s#0#l#>s2NT-#l#?s#4s2t#l#@s#6SL#l#As#8s2v#l#Bs#:s2w#m#s#<#j#Cs2n#j#Ds2y#j#Es2{#j#FT.#j#GT/#j#HC#j#IC##"). Qed.

(* [comment removed for export] *)
Lemma sreach_mmap_at_fresh_lazy_gen : forall (na nr : bool) (flags : word) L S Zr msF ms mo x8 (Q : config -> Prop),
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = ms ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  let addr := ms_gpr ms 0 in
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  mmap_noreserve_b flags = nr ->
  (forall o, syscall_spec (sys_input segs msF x8) mo o <->
             mmap_err_out mo o
             \/ ((na = false -> mmap_noreserve_backed_ok flags mo nZ = true)
                 /\ o = Ok (keff na addr n) (grant_model flags addr n na mo) [])) ->
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h ++ vm_maps h) addr n = true ->
  entries_nowrap (vm_maps h) ->
  (na = false -> nr = false -> (eager_used mo + pages_total S * page_size + nZ <= vm_limit h)%Z) ->
  (nr = true -> lazy_range_okb segs (addr, n) = true) ->
  (forall msF' : machine_state,
     let mo' := grant_model flags addr n na mo in
     lzok segs ((if nr then [(addr, n)] else []) ++ L) S ((if nr && negb na then [(addr, n)] else []) ++ Zr)
          (mkCfg msF' mo') ->
     restrict ((if nr then [(addr, n)] else []) ++ L) S msF'
       = sysret ms addr (if na || nr then unfill addr n (ms_mem ms) else zfill addr n (ms_mem ms)) ->
     hid_same L S msF msF' ->
     (eager_used mo' <= eager_used mo + (if na || nr then 0 else nZ))%Z ->
     sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros na nr flags L S Zr msF ms mo x8 Q Hok Hr Hsvc Hno. cbv zeta.
  intros Hlen Gb Hspec Hce Hal Hpos Hfree Hnw Hbud Hrok Hk.
  subst ms. rewrite restrict_svc in Hsvc. rewrite !ms_gpr_restrict in *.
  set (addr := ms_gpr msF 0) in *.
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr msF 1))) in *.
  set (n := Z_to_bv 64 nZ) in *.
  pose proof (alloc_top_lt (m_vmmaps mo)) as Htop.
  destruct (page_round_up_n_facts (ms_gpr msF 1) Hlen ltac:(pose proof (word_unsigned_range addr); unfold two_pow_64 in Htop; lia)) as (HnZpos & HnZal & Hun).
  fold nZ in HnZpos, HnZal, Hun. fold n in Hun.
  pose proof (lzok_backing_used_le segs L S Zr _ Hok) as Hbkd. cbn [cfg_model] in Hbkd.
  pose proof (li_budget _ _ _ (lzok_inv Hok)) as Hli. cbn [cfg_model] in Hli.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs msF x8)) = 222%Z) by (rewrite in_sysno_sys_input; exact Hno).
  assert (Hbk : na = false -> mmap_noreserve_backed_ok flags mo nZ = true).
  { intros ->. unfold mmap_noreserve_backed_ok. rewrite Gb. destruct nr; [reflexivity|].
    specialize (Hbud eq_refl eq_refl). apply Z.leb_le. lia. }
  assert (Hplace : refusal_b (sys_input segs msF x8) mo addr = false).
  { apply (place_not_refusal (sys_input segs msF x8) mo addr nZ Hno'); [|lia]. apply place_ok_intro; assumption. }
  assert (Hnode : node_ok segs (mkCfg msF mo) unit (fun _ => [])
                    (fun _ => mkCfg (advance_past_svc (apply_effect msF (keff na addr n)))
                                    (grant_model flags addr n na mo))).
  { apply (node_family_noacc_cfg msF mo x8 unit (fun _ => keff na addr n)
             (fun _ => grant_model flags addr n na mo) (fun _ => []) _ (lzok_halted Hok) Hsvc Hspec).
    - intros []. right. split; [exact Hbk | reflexivity].
    - intros []. apply spurious_refusal_not_refusal. rewrite keff_ret. exact Hplace.
    - intros eff m' ev [He | [_ E]] Hns.
      + exfalso. apply Hns. apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->).
        apply (alloc_refusal_spurious _ mo _ (keff na addr n) (grant_model flags addr n na mo) []).
        * apply family_off_mmap_true. exact Hno'.
        * cbn [eff_ret]. apply errno_is_refusal_mmap. exact Hno'.
        * apply (proj2 (Hspec _)). right. split; [exact Hbk | reflexivity].
        * rewrite keff_ret. exact Hplace.
      + apply Ok_inj in E as (-> & -> & ->). exists tt. auto.
    - intros eff m' ev [He | [_ E]].
      + apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->). exact (lzok_halted Hok).
      + apply Ok_inj in E as (-> & -> & ->). rewrite grant_model_halted. exact (lzok_halted Hok).
    - intros [He | [_ E]]; [apply mmap_err_out_enomem in He; discriminate He | discriminate E].
    - intros []. apply keff_accesses. }
  apply (sreach_node segs _ unit _ tt _ Hnode
           (RomBase.sys_rob_memfree segs msF mo x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_222))). intros [].
  assert (Hli' : lazy_interior addr n = [(addr, n)]).
  { apply lazy_interior_aligned; [exact Hal | rewrite Hun; exact HnZal | rewrite Hun; exact HnZpos]. }
  assert (He : entry_nowrap (addr, n)).
  { unfold entry_nowrap, hi. cbn [fst snd]. rewrite Hun. unfold two_pow_64 in Htop. lia. }
  assert (Heag : (eager_used (grant_model flags addr n na mo)
                  <= eager_used mo + (if na || nr then 0 else nZ))%Z).
  { destruct na; [|destruct nr]; cbn [orb].
    - pose proof (eager_used_grant_covered_le flags addr n true mo Hnw He (or_introl eq_refl)). lia.
    - pose proof (eager_used_grant_covered_le flags addr n false mo Hnw He (or_intror (conj Gb Hli'))). lia.
    - rewrite <- Hun. apply (eager_used_grant_rw_le flags addr n mo Gb Hnw He). }
  assert (Hbud' : (eager_used (grant_model flags addr n na mo) + pages_total S * page_size
                   <= vm_limit (m_vmmaps mo))%Z).
  { destruct na; [|destruct nr]; cbn [orb] in Heag; [lia | lia |]. specialize (Hbud eq_refl eq_refl). lia. }
  destruct (lzok_after_grant na nr flags L S Zr msF mo addr n Hok Gb
              (region_free_app_r _ _ _ _ Hfree) Hrok Hli' Hbud')
    as (Hok' & Hvis & Hhs).
  apply (Hk _ Hok' Hvis Hhs Heag).
Qed.

(* [comment removed for export] *)
Theorem sreach_mmap_fixed_fresh_lazy : forall (na nr : bool) L S Zr msF ms mo x8 (Q : config -> Prop),
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = ms ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  let addr := ms_gpr ms 0 in
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 (kprot na) -> ms_gpr ms 3 = Z_to_bv 64 (fflags nr) ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h ++ vm_maps h) addr n = true ->
  entries_nowrap (vm_maps h) ->
  (na = false -> nr = false -> (eager_used mo + pages_total S * page_size + nZ <= vm_limit h)%Z) ->
  (nr = true -> lazy_range_okb segs (addr, n) = true) ->
  (forall msF' : machine_state,
     let mo' := grant_model (Z_to_bv 64 (fflags nr)) addr n na mo in
     lzok segs ((if nr then [(addr, n)] else []) ++ L) S ((if nr && negb na then [(addr, n)] else []) ++ Zr)
          (mkCfg msF' mo') ->
     restrict ((if nr then [(addr, n)] else []) ++ L) S msF'
       = sysret ms addr (if na || nr then unfill addr n (ms_mem ms) else zfill addr n (ms_mem ms)) ->
     hid_same L S msF msF' ->
     (eager_used mo' <= eager_used mo + (if na || nr then 0 else nZ))%Z ->
     sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros na nr L S Zr msF ms mo x8 Q Hok Hr Hsvc Hno. cbv zeta.
  intros Hlen H2 H3 H4 H5 Hce Hal Hpos Hfree Hnw Hbud Hrok Hk.
  destruct (fgates na nr) as (_ & _ & _ & _ & _ & _ & Gb).
  apply (sreach_mmap_at_fresh_lazy_gen na nr (Z_to_bv 64 (fflags nr)) L S Zr msF ms mo x8 Q Hok Hr Hsvc Hno Hlen Gb);
    try assumption.
  subst ms. rewrite !ms_gpr_restrict in *.
  intros o. exact (mmap_fixed_fresh_spec na nr msF mo x8 o Hno Hlen H2 H3 H5 Hce Hal Hpos Hfree).
Qed.

(* [comment removed for export] *)
Theorem sreach_mmap_noreplace_fresh_lazy : forall (na nr : bool) L S Zr msF ms mo x8 (Q : config -> Prop),
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = ms ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  let addr := ms_gpr ms 0 in
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 (kprot na) -> ms_gpr ms 3 = Z_to_bv 64 (nrflags nr) ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h ++ vm_maps h) addr n = true ->
  entries_nowrap (vm_maps h) ->
  (na = false -> nr = false -> (eager_used mo + pages_total S * page_size + nZ <= vm_limit h)%Z) ->
  (nr = true -> lazy_range_okb segs (addr, n) = true) ->
  (forall msF' : machine_state,
     let mo' := grant_model (Z_to_bv 64 (nrflags nr)) addr n na mo in
     lzok segs ((if nr then [(addr, n)] else []) ++ L) S ((if nr && negb na then [(addr, n)] else []) ++ Zr)
          (mkCfg msF' mo') ->
     restrict ((if nr then [(addr, n)] else []) ++ L) S msF'
       = sysret ms addr (if na || nr then unfill addr n (ms_mem ms) else zfill addr n (ms_mem ms)) ->
     hid_same L S msF msF' ->
     (eager_used mo' <= eager_used mo + (if na || nr then 0 else nZ))%Z ->
     sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros na nr L S Zr msF ms mo x8 Q Hok Hr Hsvc Hno. cbv zeta.
  intros Hlen H2 H3 H4 H5 Hce Hal Hpos Hfree Hnw Hbud Hrok Hk.
  destruct (nrgates na nr) as (_ & _ & _ & _ & _ & _ & _ & _ & Gb).
  apply (sreach_mmap_at_fresh_lazy_gen na nr (Z_to_bv 64 (nrflags nr)) L S Zr msF ms mo x8 Q Hok Hr Hsvc Hno Hlen Gb);
    try assumption.
  subst ms. rewrite !ms_gpr_restrict in *.
  intros o. exact (mmap_noreplace_fresh_spec na nr msF mo x8 o Hno Hlen H2 H3 H5 Hce Hal Hpos Hfree).
Qed.


Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma map_contains_In : forall maps (addr n : word),
  map_contains maps addr n = true ->
  exists e, In e maps /\ lo e <= bv_unsigned addr /\ bv_unsigned addr + bv_unsigned n <= hi e.
Proof.
  intros maps addr n H. unfold map_contains in H. apply existsb_exists in H.
  destruct H as (e & Hin & Hc). exists e. split; [exact Hin|].
  apply andb_true_iff in Hc. destruct Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  unfold lo, hi. lia.
Qed.

(* [comment removed for export] *)
Lemma lazy_ranges_okb_nowrap : forall L, lazy_ranges_okb segs L = true -> entries_nowrap L.
Proof.
  intros L H e He. pose proof (lazy_ranges_okb_In segs L e H He) as Hr.
  unfold lazy_range_okb, range_nowrapb in Hr. destruct e as [b s]. cbn [fst snd] in Hr.
  apply andb_true_iff in Hr. destruct Hr as [Hnw _]. apply Z.leb_le in Hnw.
  unfold entry_nowrap, hi. cbn [fst snd]. exact Hnw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma addr_not_refusal_mmap : forall i m (a : word),
  bv_unsigned (in_sysno i) = 222%Z ->
  (bv_unsigned a <= alloc_top (m_vmmaps m))%Z ->
  refusal_b i m a = false.
Proof.
  intros i m a Hno Ha. rewrite (refusal_b_mmap i m a Hno). apply bv_eqb_neq. intros E. subst a.
  rewrite (errno_ret_unsigned ENOMEM) in Ha by (unfold ENOMEM; lia).
  pose proof (word_unsigned_range (vm_init_sp (m_vmmaps m))).
  unfold ENOMEM, alloc_top, stack_max_size, two_pow_64 in *. lia.
Qed.

Lemma mmap_fixed_commit_spec : forall (nr : bool) ms mo x8 o,
  bv_unsigned x8 = 222%Z ->
  let addr := ms_gpr ms 0 in
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 3 -> ms_gpr ms 3 = Z_to_bv 64 (fflags nr) ->
  ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  syscall_spec (sys_input segs ms x8) mo o <->
  mmap_err_out mo o
  \/ (mmap_fixed_rw_budget_ok (Z_to_bv 64 (fflags nr)) mo addr n = true
      /\ o = Ok (mkEffect addr [] [(addr, n)]) (commit_model (Z_to_bv 64 (fflags nr)) addr n false mo) [])
  \/ (exists e, In e mmap_errnos
       /\ o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
                 (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) mo) []).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.outcome); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Logic.not); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.fflags); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.alloc_top); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.region_free); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved); constr:(@Corelib.Init.Datatypes.true); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.map_contains); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.fgates); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Logic.and); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_off_aligned_b); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_anon_b); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_modeled_b); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.kprot); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noaccess_b); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_noaccess_b); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_rw_b); constr:(@Corelib.Init.Datatypes.negb); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noreserve_b); constr:(@kc__1); constr:(@Corelib.Init.Logic.iff); constr:(@LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.sys_input); constr:(segs); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.mmap_err_out); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_rw_budget_ok); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.Ok); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.MemCopy); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyLedger.commit_model); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.event); constr:(@Corelib.Init.Logic.ex); constr:(@Stdlib.Lists.List.In); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_errnos); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.errno_ret); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.with_mmap_destroyed); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_destroyed_next); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_spec); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.in_arg); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.syscall_spec_222); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.in_sysno); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ExitSim.in_sysno_sys_input); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.with_mmap_replacement); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.with_vmmaps); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_rw_next); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.mmap_fixed_rw_commit_outcome); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.w_is0_false); constr:(@Corelib.Classes.RelationClasses.reflexivity); constr:(@Corelib.Classes.RelationClasses.iff_Reflexive); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyLedger.mmap_fixed_rw_commit_model); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MmapSim.in_arg5_sys_input); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MmapSim.in_arg4_sys_input); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MmapSim.in_arg3_sys_input); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.in_arg2_sys_input'); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.WithSegs.in_arg1_sys_input'); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.ExitSim.in_arg0_sys_input); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.VmMaps)|] [|@e; @lemma; @b; @m; @Gb; @Gfr; @H; @Gfn; @Gn; @Gm; @Ga; @Go; @a; @Hmc; @Hrf; @Hpos; @Hal; @Hce; @H5; @H3; @H2; @Hlen; @h; @n; @nZ; @len; @addr; @Hno; @o; @x8; @mo; @ms; @nr|] "#,T#L$O#O#r#I#G###Y#`#W#n#F$%#H#1#2#J#3#$#-#.#/#5#>#?#B#C#0#6#4#7#:#;#=#A#E#9#b#+#*#,#8#<#@#D#L#~#'#(#K#Q#U#S#R#[#]#)#e#g#d#i#j#k#m#l#p#o$<$=$E$D$C#V#q#t#w#{$-$0$1$3$5$6$7$>$A$B$?$G$F$H$I$J$K$L$M$N$O$P#&$Q#P#X#s#^#a#c#Z$&$)#f#|#z$*$/$.#y$:#h#x$;$@#v$$$#$'$($2$9$8$4#T#u#}#\#_$+$,H$+&$,%$-%$.%$/$$0%$1%$2'#O%$3$$4$$5&$6)$7'$8&$9&$:,$;$$<&$=%$>)$?&$@&$A&$B%$C'$D($E&$F'$G%$H$$I$$J($K$$L$$M$$N%ASDA#A#A#A#A#USE#USF#USYJ(%S#DSDA#D#D#D#D#A#USG##H+#EI%S@#&1S6#1$#USH#E'%SA#USG2&7##7%#E'%SI#'S8&<##<%#E'E#%S8##@#2%S7I(s###%S77(s#%#,#VSJ&#4S8USK#VSL%#%S9I(s#,#VSM#SN#H#S6%S$I(s#0#VSOS6#4S$USP#%S%I%S%s#((s#6#,#&s#8#WSQ('##C#K4S%USR#%S&I%S&s#1(s#?#,#&s#A#WSS('##C#KVSZDOUS[s#6#C#K'O&s#H#B##C#KUS\D&s#L#8#'s#>#C#D5%)s#@#C#D2'+s#B#C#D.)-s#DUS]D#C$#-0#C#O$%#$)#$,#$/#$4#$9#'P&s#_#B##C#K88%s#S#C#D5:'s#U#C#D2<)s#W#C#D.>+s#Y#C#7--#C#P$%#$(#$+#$.#$1#$s#-#9MPS,:#OS&;OS&'R&s#v#%PI%Ps#k(s#y#,#&s#{#<(O'##C#KUSEs$&USF#US^#Gs$$#F#Gs$&s$&0s$'s$'/+F$1%$#FS_Gs$+S`F#/5*&'%#=762DOFSa*J%$##s$0S&#$4#WSbHGScUSdG%RI%Rs$*(s$8#,#&s$:#0s$:s$:'#17#5/*96#424P>#+'?,(#P*J&#3#s$@S,#$1#j#$H#@H#)5#)s#1#+s#3#j##s#6#Bs#2#C#K8s#^s#4s$=#C#D5s#`s#6s$?#C#D2s#bs#8s$A#C#D.s#ds#:s$C#C#s#]-s#<#C#R$%#$(#$+#$.#$1#'S'&s$\#B##C#K8s#q%s$P#C#D5s#s's$R#C#D2s#u)s$T#C#D.s#w+s$V#C#s#p--#C#S'$%#$(#$+#$.#$1#'S-&s$o#B##C#K8s$(%s$c#C#D5s$*'s$e#C#D2s$,)s$g#C#D.s$.+s$i#C#s$'--#C#S-$%#$(#$+#$.#$1#9MS-S.:#S'R;S'R'S/&s%)#%S-I%S-s$z(s%,#,#&s%.#<(S''##C#K0s%0s%0)%1s#i#s#g/+s#k#s#hs#fs#d=-,(DS'*J$#s#c#s%4R#$)#%S/I%S/s%,(s%:#,#&s%<#0s%<s%<'#1s#u#s#s/s#hs#ws#t#s#rs#p4S->#+'?,(#S-*J&#s#q#s%BS.#$s#o#j#$H#@H#)3#)s#$#+s#&#j##s#)#8s$^s#%s%=#C#D5s$`s#'s%?#C#D2s$bs#)s%A#C#D.s$ds#+s%C#C#s$]-s#-#C#S/$%#$(#$+#$.#'S:&s%[#B##C#K'S5&s%_#8s$r#s%Q#C#D5s$t%s%S#C#D2s$v's%U#C#D.s$x)s%W#C#s$q-+#C#S5$%#$(#$+#$.#'S0&s%o#8s%&#s%a#C#D5s%(%s%c#C#D2s%*'s%e#C#D.s%,)s%g#C#s%%-+#C#S0$%#$(#$+#$.#9MS0S::#S5S/;S5S/'S1&s&&#%S0I%S0s%w(s&)#,#&s&+#<(S5'##C#K0s&-s&-)%1s$f#s$d/+s$h#s$es$cs$a=-,(DS5*J$#s$`#s&1S/#$)#%S1I%S1s&)(s&7#,#&s&9#0s&9s&9'#1s$r#s$p/s$es$ts$q#s$os$m4S0>#+'?,(#S0*J&#s$n#s&?S:#$s$l#j#$H#@H#)3#)s#$#+s#&#j##s#)#5s%[s#%s&:#C#D2s%]s#'s&<#C#D.s%_s#)s&>#C#s%X-s#+#C#S1$%#$(#$+#'S;&s&U#8s%h#s&G#C#D'S2&s&Y#5s%l#s&K#C#D2s%n%s&M#C#D.s%p's&O#C#s%i-)#C#S2$%#$(#$+#'S(&s&f#5s%y#s&X#C#D2s%{%s&Z#C#D.s%}'s&\#C#s%v-)#C#S($%#$(#$+#9MS(S;:#S2S1;S2S1'S)&s&v#%S(I%S(s&k(s&y#,#&s&{#<(S2'##C#K0s&}s&})%1s%Z#s%X/+s%\#s%Ys%Ws%U=-,(DS2*J$#s%T#s'%S1#$)#%S)I%S)s&y(s'+#,#&s'-#0s'-s'-'#1s%f#s%d/s%Ys%hs%e#s%cs%a4S(>#+'?,(#S(*J&#s%b#s'3S;#$s%`#j#$H#@H#)3#)s#$#+s#&#j##s#)#2s&Os#%s'.#C#D.s&Qs#'s'0#C#s&J-s#)#C#S)$%#$(#'S<&s'F#5s&Y#s'8#C#D'S3&s'J#2s&]#s'<#C#D.s&_%s'>#C#s&X-'#C#S3$%#$(#'S*&s'T#2s&g#s'F#C#D.s&i%s'H#C#s&b-'#C#S*$%#$(#9MS*S<:#S3S);S3S)'S+&s'a#%S*I%S*s'V(s'd#,#&s'f#<(S3'##C#K0s'hs'h)%1s&E#s&C/+s&G#s&Ds&Bs&@=-,(DS3*J$#s&?#s'lS)#$)#%S+I%S+s'd(s'r#,#&s't#0s'ts't'#1s&Q#s&O/s&Ds&Ss&P#s&Ns&L4S*>#+'?,(#S**J&#s&M#s'zS<#$s&K#j#$H#@H#)3#)s#$#+s#&#j##s#)#.s':s#%s'u#C#s'3-s#'#C#S+$%#'S=&s(.#2s'A#s'|#C#D'S4&s(2#.s'E#s($#C#s'>-%#C#S4$%#'L&s(9#.s'L#s(+#C#s'E-%#C#L$%#9MLS=:#S4S+;S4S+'F&s(C#%LI%Ls(8(s(F#,#&s(H#<(S4'##C#K0s(Js(J)%1s''#s'%/+s')#s'&s'$s&~=-,(DS4*J$#s&}#s(NS+#$)#%FI%Fs(F(s(T#,#&s(V#0s(Vs(V'#1s'3#s'1/s'&s'5s'2#s'0s'.4L>#+'?,(#L*J&#s'/#s(\S=#$s'-#j#$H#@H#)3#)s#$#+s#&#j##s#)#-s#%#C#F'N&s(i#.s'|#s([#C#s'u'E&s(m#-##C#E9MEF:#NL6$I6%s(f6&s(b6's(^6(s(Z6)s(Z3('&%$#*NL+*#9MQN:#EF6$I6%s(p6&s(l6's(h6(s(d6)s(d3('&%$#*EF;EF'SB&s))#%QI%Qs(z(s),#,#&s).#<(E'##C#K0s)0s)0)%1s'i#s'g/+s'k#s'hs'fs'd=-,(DE*J$#s'c#s)4F#$)#%SBI%SBs),(s):#,#&s)<#0s)<s)<'#1s'u#s's/s'hs'ws't#s'rs'p4Q>#+'?,(#Q*J&#s'q#s)BN#$s'o#j#$H#@H#)3#)s#$#VSeS>#]STS>S?SUs#.s#'G$$#j#%s#1#(s)MG#H#s)Cj#&s)N#USfs#>WSgMEF7s)QF%S4$#XShs#ANL#%EI3Gs#6s#5s#4s#3s#2s#9EF+#/j#&s)V#%Es)K3s#1Gs#9s#8s#7s#6s#=EF+#3j#&s)Z#%Es)J3s#5s#4Gs#<s#;s#:s#AEF+#7j#&s)^#%Es)I%Qs)O3s#:s#9#Gs#@s#?s#FEF+#<j#&s)c#%Es)I%Qs)O3s#?s#>(#Gs#Ds#KEF+#Aj#&s)h#%Es)M%Qs)O3s#Ds#C-(#Gs#PEF+#s#&j#&s)m#%Qs)R3s#Hs#GG,'#s#TEF+#s#*j#&s)q#'Q&s)t#3s#Ms#Ls)`G,(s#YEF+#s#/j#&s)v#3s#Ps#Os)cs#Q/Gs#\EF+#s#2j#&s)y#3s#)s#%s)f)8s)ls#iNL;NL(s)}s#',#&s*##<.Ns#.##C#K0s*%s*%s#0%1s(^#s(\/s#2s(`#s(]s([s(Y4NWSV#s#4)VSW#NXSX6s#6+#*J'#s([#s*,L#$,#/s(Ys(hs(es#\s(cs(a4E>#s#fs#b?s#gs#c#E*J&#s(b#s*3F#$s(`#j#$H#@H#),#)<#+>#3s#ps#os*'s#qs#/s*-s#|EFWSV.s#qs#mVSW#EXSXs#ts#ss#o#*Js#k#s(n#s*?F#$s#p#)#s#Z)s#{#]STS>S?SU+#Gs#Zs#Zs#Yj#%-#VSis#MS=i#8Sjs#Rs#Ns*3s#2s#As*9s$6NLS:S.#S,S9SAS#S<S)S(S2S;=s#3s#Ss#(DN*Js#uGs(x#s*IF#$s#z#)#s#d)s$)#+#s#dj#'SC#*Js#+*s)##s*PL#$s#0#)#>)s#7#XSkS>S?Sl#XSms#As#as#6N7SC1*$s#.#V53#7s*Ys*Ks#>#s#NS37s*Zs#Es#B#s#YS*7s*[s*Gs#H#s#^S+WSnMEF7s*]s#Rs#N$s$E#WSoMEF7s*_s#Ys#U$s$H#WSpMEF7s*as#`s#\$s$K#VSqEF7s*cs#fs#c$s$N#VSrEF7s*es#ls#i$s$Q#WSsMEF7s*gs#rs#o$s$T#Vs#{s#t#+s$W7m#$#j#(s$[#j#)s$`#V#S#Gj##s$f#j##s%7#Cs%8s%6s$j#Gj#*s%=#j#+s%E#V#S#Gj##s%K#j##s%~#Cs&#s%zs%R#Gj#*s&(#j#,s&3#V#S#Gj##s&9#j##s&r#Cs&ss&ks&C#Gj#*s&x#j#-s'*#V#S#Gj##s'0#j##s'o#Cs'ps'es'=#Gj#*s'u#j#.s(*#V#S#Gj##s(0#j##s(u#Cs(vs(hs(@#Gj#*s({#j#/s*G#V#S#Gj##s)5#j##s*J#Cs*Ks)}s)H#Gl#0s*Ns*5#j#1s*P#j#2s*Z#j#3s*d#j#4s*h#j#5s*m#j#6s*w#j#7s*|#j#8s+&#j#9s+,#%S@I%SAs+2,s$Q&s+AG#s+ASts+3USH#%S$s+2#s+D#s+0%S%s+/'S&&s+H##s+H%#%S&s+-#s+J#s+<(s+LS7VSJ#SIUSKS@VSL$#(s+PS9VSM#SN#H#S6(s+SS$VSOS6#USPS8WSQ#S%S7#C#KUSRS7WSS#S&S9#C#K9MS'R:#S.P;S.P<s)MS.S,S$#C#K0s+_s+_S,S$1s*<#s*:/S,s*>#s*;s*9s*7=s)RS,S$DS.*J$#s*6#s+cP#$)#0s+fs+fOS%1s*C#s*A/s*6s*Es*B#s*@s*>>S$OS%?OS%#S'*J%#s*>#s+kR#$s*<#j#$H#@H#)-#)7#+9#k##<#k##@#k##s#$#k##s#'#k##s#+#k##s#0#k##s#3#k##s#8#k##s#;#l#:s+WSu#l#;s#?s+}#l#<s#AH#l#=s#Cs,##l#>s#Es,$#m#s#G#j#?s+w#j#@s,&#j#As,(#j#BSC#j#CSv#j#DC##"). Qed.

(* [comment removed for export] *)
Lemma hiddenb_maps_subtract : forall L S l h x,
  entries_nowrap L -> 0 <= l -> l <= h ->
  hiddenb (maps_subtract L l h) S x = hiddenb L S x && negb (zinb l h (bv_unsigned x)).
Proof.
  intros L S l h x HL Hl Hlh. unfold hiddenb. rewrite !in_rangesb_zcovb, (zcovb_maps_subtract L l h _ HL Hl Hlh).
  destruct (zcovb L (bv_unsigned x)), (zinb l h (bv_unsigned x)), (zcovb S (bv_unsigned x)); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lzok_after_commit : forall (nr : bool) L S Zr msF mo (addr n : word),
  lzok segs L S Zr (mkCfg msF mo) ->
  let h := m_vmmaps mo in
  let l := bv_unsigned addr in
  let hh := bv_unsigned addr + bv_unsigned n in
  (hh <= 2 ^ 64)%Z ->
  entries_nowrap (vm_maps h) -> entries_nowrap (vm_noaccess h) ->
  lazy_interior addr n = [(addr, n)] ->
  (nr = false -> forall x : word, l <= bv_unsigned x < hh -> in_rangesb x Zr = false) ->
  (nr = true -> forall x : word, l <= bv_unsigned x < hh -> in_rangesb x Zr = true) ->
  (nr = true -> lazy_range_okb segs (addr, n) = true) ->
  let mo' := commit_model (Z_to_bv 64 (fflags nr)) addr n false mo in
  (eager_used mo' + pages_total S * page_size <= vm_limit h)%Z ->
  let L' := (if nr then [(addr, n)] else []) ++ maps_subtract L l hh in
  let msF' := advance_past_svc (apply_effect msF (mkEffect addr [] [(addr, n)])) in
  lzok segs L' S Zr (mkCfg msF' mo')
  /\ restrict L' S msF'
     = sysret (restrict L S msF) addr
         (if nr then (fun x => if zin_rangeb (bv_unsigned x) (addr, n) && in_rangesb x S
                              then Some (Z_to_bv 8 0) else ms_mem (restrict L S msF) x)
          else zfill addr n (ms_mem (restrict L S msF)))
  /\ hid_same L' S msF msF'
  /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 (fflags nr)) mo addr n = true.
Proof.
  intros nr L S Zr msF mo addr n Hok. cbv zeta. intros Hnw HX HNA Hli HZfree HZin Hrok Hbud.
  destruct Hok as [HL Hinv Hh HZ HSZ HZL HLM]. cbn in *.
  pose proof (lazy_ranges_okb_nowrap L HL) as HLnw.
  pose proof (word_unsigned_range addr) as Har. pose proof (word_unsigned_range n) as Hnr.
  destruct (fgates false nr) as (_ & _ & _ & _ & _ & _ & Gb).
  set (l := bv_unsigned addr) in *. set (hh := bv_unsigned addr + bv_unsigned n) in *.
  assert (Hlh : l <= hh) by (unfold l, hh; lia). assert (Hl0 : 0 <= l) by (unfold l; lia).
  (* [comment removed for export] *)
  assert (Elazy : m_vm_lazy (commit_model (Z_to_bv 64 (fflags nr)) addr n false mo)
                  = (if nr then [(addr, n)] else []) ++ maps_subtract L l hh).
  { rewrite commit_model_lazy, Gb, Hli, (li_lazy _ _ _ Hinv). destruct nr; reflexivity. }
  assert (Emat : m_vm_materialized (commit_model (Z_to_bv 64 (fflags nr)) addr n false mo)
                 = List.filter (page_outside_range l hh) (m_vm_materialized mo))
    by apply commit_model_materialized.
  assert (Emaps : m_vmmaps (commit_model (Z_to_bv 64 (fflags nr)) addr n false mo)
                  = commit_vmmaps (m_vmmaps mo) addr n false) by apply commit_model_vmmaps.
  assert (Emem : ms_mem (apply_effect msF (mkEffect addr [] [(addr, n)])) = zfill addr n (ms_mem msF))
    by apply apply_effect_mem_zeros.
  (* [comment removed for export] *)
  assert (Hhid' : forall x, hiddenb ((if nr then [(addr, n)] else []) ++ maps_subtract L l hh) S x
                            = if zinb l hh (bv_unsigned x) then (if nr then negb (in_rangesb x S) else false)
                              else hiddenb L S x).
  { intros x. destruct nr; cbn [app].
    - rewrite hiddenb_cons_lazy, (hiddenb_maps_subtract L S l hh x HLnw Hl0 Hlh).
      replace (zin_rangeb (bv_unsigned x) (addr, n)) with (zinb l hh (bv_unsigned x)) by reflexivity.
      destruct (zinb l hh (bv_unsigned x)), (in_rangesb x S), (hiddenb L S x); reflexivity.
    - rewrite (hiddenb_maps_subtract L S l hh x HLnw Hl0 Hlh).
      destruct (zinb l hh (bv_unsigned x)), (hiddenb L S x); reflexivity. }
  assert (HRL : nr = true -> forall x : word, l <= bv_unsigned x < hh -> in_rangesb x L = true).
  { intros Hn x Hx. apply HZL. apply (HZin Hn x Hx). }
  (* [comment removed for export] *)
  assert (Hlen : (Z.of_nat (length (List.filter (page_outside_range l hh) (m_vm_materialized mo)))
                  <= pages_total S)%Z).
  { rewrite <- all_pages_length. apply Nat2Z.inj_le.
    apply (NoDup_incl_length (l:=List.filter _ _) (l':=all_pages S)).
    - apply NoDup_filter. exact (li_nodup _ _ _ Hinv).
    - intros p Hp. apply filter_In in Hp. apply (li_incl _ _ _ Hinv). tauto. }
  assert (Elim : vm_limit (commit_vmmaps (m_vmmaps mo) addr n false) = vm_limit (m_vmmaps mo)) by reflexivity.
  assert (Hbok : mmap_fixed_rw_budget_ok (Z_to_bv 64 (fflags nr)) mo addr n = true).
  { unfold mmap_fixed_rw_budget_ok. rewrite mmap_fixed_rw_commit_model.
    unfold vm_backing_within_limit. apply Z.leb_le. rewrite vm_backing_used_split, Emat, Emaps, Elim.
    unfold page_size in *. nia. }
  (* [comment removed for export] *)
  assert (Hout : forall x, zinb l hh (bv_unsigned x) = false ->
                 ms_mem (apply_effect msF (mkEffect addr [] [(addr, n)])) x = ms_mem msF x).
  { intros x Hx. rewrite Emem. apply zfill_out. apply zinb_false in Hx. unfold l, hh in Hx. lia. }
  assert (Hin : forall x, zinb l hh (bv_unsigned x) = true ->
                ms_mem (apply_effect msF (mkEffect addr [] [(addr, n)])) x = Some (Z_to_bv 8 0)).
  { intros x Hx. rewrite Emem. apply zinb_true in Hx. unfold zfill, zmem. unfold l, hh in Hx.
    rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  split; [|split; [|split; [|exact Hbok]]].
  - (* [comment removed for export] *) split; cbn.
    + destruct nr; cbn [app].
      * apply (proj2 (lazy_ranges_okb_cons segs (addr, n) _)). split; [exact (Hrok eq_refl)|].
        apply lazy_ranges_okb_maps_subtract; [exact Hnw | exact HL].
      * apply lazy_ranges_okb_maps_subtract; [exact Hnw | exact HL].
    + split.
      * exact Elazy.
      * rewrite Emat. apply NoDup_filter. exact (li_nodup _ _ _ Hinv).
      * rewrite Emat. intros p Hp. apply filter_In in Hp. apply (li_incl _ _ _ Hinv). tauto.
      * rewrite Emaps, Elim. exact Hbud.
    + destruct (commit_model_nonvm (Z_to_bv 64 (fflags nr)) addr n false mo) as (_ & _ & _ & Hp & _).
      unfold m_halted in *. rewrite Hp. exact Hh.
    + intros x Hx Hz. cbn [ms_mem advance_past_svc]. rewrite Hhid' in Hx.
      destruct (zinb l hh (bv_unsigned x)) eqn:Ein.
      * apply Hin. exact Ein.
      * rewrite (Hout x Ein). apply HZ; assumption.
    + exact HSZ.
    + (* [comment removed for export] *) intros x Hx. rewrite in_rangesb_zcovb in *.
      destruct nr; cbn [app]; rewrite ?zcovb_cons, (zcovb_maps_subtract L l hh _ HLnw Hl0 Hlh).
      * replace (zin_rangeb (bv_unsigned x) (addr, n)) with (zinb l hh (bv_unsigned x)) by reflexivity.
        pose proof (HZL x) as HxL. rewrite !in_rangesb_zcovb in HxL. rewrite (HxL Hx).
        destruct (zinb l hh (bv_unsigned x)); reflexivity.
      * pose proof (HZL x) as HxL. rewrite !in_rangesb_zcovb in HxL. rewrite (HxL Hx). cbn [andb].
        destruct (zinb l hh (bv_unsigned x)) eqn:Ein; [|reflexivity].
        apply zinb_true in Ein. pose proof (HZfree eq_refl x Ein) as C. rewrite in_rangesb_zcovb in C.
        rewrite C in Hx. discriminate.
    + (* [comment removed for export] *) rewrite Emaps. cbn. intros x Hx. rewrite in_rangesb_zcovb in Hx |- *.
      destruct nr; cbn [app] in Hx; rewrite ?zcovb_cons, (zcovb_maps_subtract L l hh _ HLnw Hl0 Hlh) in Hx.
      * destruct (zin_rangeb (bv_unsigned x) (addr, n)) eqn:Ein.
        -- pose proof (HRL eq_refl x ltac:(apply zinb_true; exact Ein)) as HxL.
           rewrite <- in_rangesb_zcovb. apply HLM. exact HxL.
        -- cbn in Hx. apply andb_true_iff in Hx. rewrite <- in_rangesb_zcovb. apply HLM.
           rewrite in_rangesb_zcovb. tauto.
      * apply andb_true_iff in Hx. rewrite <- in_rangesb_zcovb. apply HLM. rewrite in_rangesb_zcovb. tauto.
  - (* [comment removed for export] *)
    rewrite (restrict_sysret L S). cbn [eff_ret]. f_equal.
    apply functional_extensionality. intros x.
    unfold restrict_mem, restrict_mem_by. rewrite Hhid'.
    cbn [ms_mem restrict restrict_by with_mem restrict_mem_by].
    destruct (zinb l hh (bv_unsigned x)) eqn:Ein.
    + rewrite (Hin x Ein). destruct nr.
      * replace (zin_rangeb (bv_unsigned x) (addr, n)) with (zinb l hh (bv_unsigned x)) by reflexivity.
        rewrite Ein. cbn [andb]. destruct (in_rangesb x S) eqn:ES; cbn [negb]; [reflexivity|].
        replace (hiddenb L S x) with true; [reflexivity|]. symmetry. apply hiddenb_true_iff.
        split; [apply (HRL eq_refl); apply zinb_true; exact Ein | exact ES].
      * unfold zfill, zmem. apply zinb_true in Ein. unfold l, hh in Ein.
        rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb]. reflexivity.
    + rewrite (Hout x Ein). destruct nr.
      * replace (zin_rangeb (bv_unsigned x) (addr, n)) with (zinb l hh (bv_unsigned x)) by reflexivity.
        rewrite Ein. cbn [andb]. reflexivity.
      * unfold zfill, zmem. apply zinb_false in Ein. unfold l, hh in Ein.
        destruct ((bv_unsigned addr <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned addr + bv_unsigned n)) eqn:E.
        -- apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
        -- destruct (hiddenb L S x); reflexivity.
  - (* [comment removed for export] *)
    intros x Hx. cbn [ms_mem advance_past_svc]. rewrite Hhid' in Hx.
    destruct (zinb l hh (bv_unsigned x)) eqn:Ein.
    + destruct nr; [|discriminate Hx]. rewrite (Hin x Ein). symmetry. apply HZ.
      * apply hiddenb_true_iff. split; [apply (HRL eq_refl); apply zinb_true; exact Ein|].
        destruct (in_rangesb x S); [discriminate Hx | reflexivity].
      * apply (HZin eq_refl). apply zinb_true. exact Ein.
    + apply Hout. exact Ein.
Qed.
Scheme kc__6 := Elimination for Corelib.Init.Datatypes.unit Sort Prop.
Scheme kc__7 := Elimination for Corelib.Init.Logic.False Sort Prop.


(* [comment removed for export] *)
Theorem sreach_mmap_fixed_commit_lazy : forall (nr : bool) L S Zr msF ms mo x8 (Q : config -> Prop),
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = ms ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  let addr := ms_gpr ms 0 in
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 3 -> ms_gpr ms 3 = Z_to_bv 64 (fflags nr) ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  entries_nowrap (vm_maps h) -> entries_nowrap (vm_noaccess h) -> nooverlap (vm_maps h) ->
  (nr = false -> forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ -> in_rangesb x Zr = false) ->
  (nr = true -> forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ -> in_rangesb x Zr = true) ->
  (nr = true -> lazy_range_okb segs (addr, n) = true) ->
  (nr = false -> (eager_used mo + pages_total S * page_size + nZ <= vm_limit h)%Z) ->
  (forall msF' : machine_state,
     let mo' := commit_model (Z_to_bv 64 (fflags nr)) addr n false mo in
     let L' := (if nr then [(addr, n)] else []) ++ maps_subtract L (bv_unsigned addr) (bv_unsigned addr + nZ) in
     lzok segs L' S Zr (mkCfg msF' mo') ->
     restrict L' S msF'
       = sysret ms addr
           (if nr then (fun x => if zin_rangeb (bv_unsigned x) (addr, n) && in_rangesb x S
                                then Some (Z_to_bv 8 0) else ms_mem ms x)
            else zfill addr n (ms_mem ms)) ->
     hid_same L' S msF msF' ->
     (eager_used mo' <= eager_used mo + (if nr then 0 else nZ))%Z ->
     sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros nr L S Zr msF ms mo x8 Q Hok Hr Hsvc Hno. cbv zeta.
  intros Hlen H2 H3 H4 H5 Hce Hal Hpos Hrf Hmc HX HNA Hno_ov HZfree HZin Hrok Hbud Hk.
  subst ms. rewrite restrict_svc in Hsvc. rewrite !ms_gpr_restrict in *.
  set (addr := ms_gpr msF 0) in *.
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr msF 1))) in *.
  set (n := Z_to_bv 64 nZ) in *.
  pose proof (alloc_top_lt (m_vmmaps mo)) as Htop.
  destruct (page_round_up_n_facts (ms_gpr msF 1) Hlen ltac:(pose proof (word_unsigned_range addr); unfold two_pow_64 in Htop; lia)) as (HnZpos & HnZal & Hun).
  fold nZ in HnZpos, HnZal, Hun. fold n in Hun.
  pose proof (li_budget _ _ _ (lzok_inv Hok)) as Hli. cbn [cfg_model] in Hli.
  pose proof (lazy_ranges_okb_nowrap L (lzok_ranges Hok)) as HLnw.
  destruct (fgates false nr) as (_ & _ & _ & _ & _ & _ & Gb).
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs msF x8)) = 222%Z) by (rewrite in_sysno_sys_input; exact Hno).
  assert (Hli' : lazy_interior addr n = [(addr, n)]).
  { apply lazy_interior_aligned; [exact Hal | rewrite Hun; exact HnZal | rewrite Hun; exact HnZpos]. }
  assert (Hhh : bv_unsigned addr + bv_unsigned n <= 2 ^ 64).
  { rewrite Hun. unfold two_pow_64 in Htop. lia. }
  assert (HLm : m_vm_lazy mo = L) by exact (li_lazy _ _ _ (lzok_inv Hok)).
  assert (Heag : (eager_used (commit_model (Z_to_bv 64 (fflags nr)) addr n false mo)
                  <= eager_used mo + (if nr then 0 else nZ))%Z).
  { destruct nr.
    - pose proof (eager_used_commit_covered_le (Z_to_bv 64 (fflags true)) addr n false mo HX HNA
                    ltac:(rewrite HLm; exact HLnw) (or_intror (conj Gb Hli'))). lia.
    - rewrite <- Hun. apply (eager_used_commit_rw_le (Z_to_bv 64 (fflags false)) addr n mo HX HNA
                    ltac:(rewrite HLm; exact HLnw) Hno_ov).
      destruct (map_contains_In _ _ _ Hmc) as (e0 & He0 & He1 & He2). exists e0.
      unfold lo, hi in *. cbn [fst snd]. auto. }
  assert (Hbud' : (eager_used (commit_model (Z_to_bv 64 (fflags nr)) addr n false mo) + pages_total S * page_size
                   <= vm_limit (m_vmmaps mo))%Z).
  { destruct nr.
    - replace (if true then 0 else nZ) with 0 in Heag by reflexivity. lia.
    - replace (if false then 0 else nZ) with nZ in Heag by reflexivity. specialize (Hbud eq_refl). lia. }
  rewrite <- Hun in HZfree, HZin.
  destruct (lzok_after_commit nr L S Zr msF mo addr n Hok Hhh HX HNA Hli' HZfree HZin Hrok Hbud')
    as (Hok' & Hvis & Hhs & Hbok).
  assert (Haddr : refusal_b (sys_input segs msF x8) mo addr = false).
  { apply (addr_not_refusal_mmap _ mo addr Hno'). lia. }
  pose proof (mmap_fixed_commit_spec nr msF mo x8) as Hspec. cbv zeta in Hspec.
  specialize (fun o => Hspec o Hno Hlen H2 H3 H5 Hce Hal Hpos Hrf Hmc) as Hsp. clear Hspec.
  fold nZ in Hsp. fold n in Hsp. fold addr in Hsp.
  assert (Hnode : node_ok segs (mkCfg msF mo) unit (fun _ => [])
                    (fun _ => mkCfg (advance_past_svc (apply_effect msF (mkEffect addr [] [(addr, n)])))
                                    (commit_model (Z_to_bv 64 (fflags nr)) addr n false mo))).
  { apply (node_family_noacc_cfg msF mo x8 unit (fun _ => mkEffect addr [] [(addr, n)])
             (fun _ => commit_model (Z_to_bv 64 (fflags nr)) addr n false mo) (fun _ => []) _ (lzok_halted Hok) Hsvc Hsp).
    - intros []. right; left. split; [exact Hbok | reflexivity].
    - intros []. apply spurious_refusal_not_refusal. cbn [eff_ret]. exact Haddr.
    - intros eff m' ev [He | [[_ E] | (e & He & E)]] Hns.
      + exfalso. apply Hns. apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->).
        eapply (alloc_refusal_spurious _ mo _ (mkEffect addr [] [(addr, n)]));
          [apply family_off_mmap_true; exact Hno' | cbn [eff_ret]; apply errno_is_refusal_mmap; exact Hno'
          | apply (proj2 (Hsp _)); right; left; split; [exact Hbok | reflexivity] | cbn [eff_ret]; exact Haddr].
      + apply Ok_inj in E as (-> & -> & ->). exists tt. auto.
      + exfalso. apply Hns. apply Ok_inj in E as (-> & -> & ->).
        unfold mmap_errnos in He. destruct He as [<- | []].
        eapply (alloc_refusal_spurious _ mo _ (mkEffect addr [] [(addr, n)]));
          [apply family_off_mmap_true; exact Hno' | cbn [eff_ret]; apply errno_is_refusal_mmap; exact Hno'
          | apply (proj2 (Hsp _)); right; left; split; [exact Hbok | reflexivity] | cbn [eff_ret]; exact Haddr].
    - intros eff m' ev [He | [[_ E] | (e & He & E)]].
      + apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->). exact (lzok_halted Hok).
      + apply Ok_inj in E as (-> & -> & ->). exact (lzok_halted Hok').
      + apply Ok_inj in E as (-> & -> & ->).
        unfold with_mmap_destroyed. rewrite vm_forget_range_halted, with_vmmaps_halted. exact (lzok_halted Hok).
    - intros [He | [[_ E] | (e & He & E)]]; [apply mmap_err_out_enomem in He; discriminate He | discriminate E | discriminate E].
    - intros []. reflexivity. }
  apply (sreach_node segs _ unit _ tt _ Hnode
           (RomBase.sys_rob_memfree segs msF mo x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_222))). intros [].
  rewrite Hun in Hok', Hvis, Hhs. apply (Hk _ Hok' Hvis Hhs Heag).
Qed.

Local Close Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma lzok_after_disjoint_op : forall L S Zr msF mo msF' mo' (l hh : Z),
  lzok segs L S Zr (mkCfg msF mo) ->
  0 <= l -> l <= hh -> hh <= 2 ^ 64 ->
  (forall x : word, l <= bv_unsigned x < hh -> in_rangesb x L = false) ->
  m_vm_lazy mo' = maps_subtract (m_vm_lazy mo) l hh ->
  (forall p, In p (m_vm_materialized mo') -> In p (m_vm_materialized mo)) ->
  List.NoDup (m_vm_materialized mo') ->
  vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) ->
  (eager_used mo' + pages_total S * page_size <= vm_limit (m_vmmaps mo))%Z ->
  m_halted mo' = None ->
  (forall x : word, in_rangesb x L = true -> in_rangesb x (vm_maps (m_vmmaps mo')) = true) ->
  (forall x : word, ~ (l <= bv_unsigned x < hh) -> ms_mem msF' x = ms_mem msF x) ->
  lzok segs (maps_subtract L l hh) S Zr (mkCfg msF' mo')
  /\ (forall x, hiddenb (maps_subtract L l hh) S x = hiddenb L S x)
  /\ hid_same L S msF msF'.
Proof.
  intros L S Zr msF mo msF' mo' l hh [HL Hinv Hh HZ HSZ HZL HLM] Hl0 Hlh Hnw HRL Elazy Hmat Hnd Elim Hbud Hh' HLM' Hmem.
  cbn in *. pose proof (lazy_ranges_okb_nowrap L HL) as HLnw.
  assert (Hhid : forall x, hiddenb (maps_subtract L l hh) S x = hiddenb L S x).
  { intros x. rewrite (hiddenb_maps_subtract L S l hh x HLnw Hl0 Hlh).
    destruct (zinb l hh (bv_unsigned x)) eqn:E; [|apply andb_true_r].
    apply zinb_true in E. unfold hiddenb. rewrite (HRL x E). reflexivity. }
  assert (Hcov : forall x, in_rangesb x (maps_subtract L l hh) = in_rangesb x L).
  { intros x. rewrite !in_rangesb_zcovb, (zcovb_maps_subtract L l hh _ HLnw Hl0 Hlh).
    destruct (zinb l hh (bv_unsigned x)) eqn:E; [|apply andb_true_r].
    apply zinb_true in E. pose proof (HRL x E) as C. rewrite in_rangesb_zcovb in C. rewrite C. reflexivity. }
  assert (Hhs : hid_same L S msF msF').
  { intros x Hx. apply Hmem. intros HxR. apply hiddenb_true_iff in Hx. destruct Hx as [HxL _].
    rewrite (HRL x HxR) in HxL. discriminate. }
  split; [|split; [exact Hhid | exact Hhs]].
  split; cbn.
  - apply lazy_ranges_okb_maps_subtract; [exact Hnw | exact HL].
  - split.
    + rewrite Elazy, (li_lazy _ _ _ Hinv). reflexivity.
    + exact Hnd.
    + intros p Hp. apply (li_incl _ _ _ Hinv). apply Hmat. exact Hp.
    + rewrite Elim. exact Hbud.
  - exact Hh'.
  - intros x Hx Hz. rewrite Hhid in Hx. rewrite (Hhs x Hx). exact (HZ x Hx Hz).
  - exact HSZ.
  - intros x Hx. rewrite Hcov. apply HZL. exact Hx.
  - intros x Hx. rewrite Hcov in Hx. apply HLM'. exact Hx.
Qed.
Scheme kc__8 := Elimination for Corelib.Init.Specif.sumbool Sort Prop.

(* [comment removed for export] *)
Theorem sreach_mmap_fixed_noaccess_lazy : forall L S Zr msF ms mo x8 (Q : config -> Prop),
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = ms ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  let addr := ms_gpr ms 0 in
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 0 -> ms_gpr ms 3 = Z_to_bv 64 50 ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  entries_nowrap (vm_maps h) -> entries_nowrap (vm_noaccess h) ->
  (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ -> in_rangesb x L = false) ->
  (forall msF' : machine_state,
     let mo' := fixed_noaccess_model addr n mo in
     lzok segs (maps_subtract L (bv_unsigned addr) (bv_unsigned addr + nZ)) S Zr (mkCfg msF' mo') ->
     restrict (maps_subtract L (bv_unsigned addr) (bv_unsigned addr + nZ)) S msF'
       = sysret ms addr (unfill addr n (ms_mem ms)) ->
     hid_same L S msF msF' ->
     (forall x, hiddenb (maps_subtract L (bv_unsigned addr) (bv_unsigned addr + nZ)) S x = hiddenb L S x) ->
     (eager_used mo' <= eager_used mo)%Z ->
     sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros L S Zr msF ms mo x8 Q Hok Hr Hsvc Hno. cbv zeta.
  intros Hlen H2 H3 H4 H5 Hce Hal Hpos Hrf Hmc HX HNA HRL Hk.
  subst ms. rewrite restrict_svc in Hsvc. rewrite !ms_gpr_restrict in *.
  set (addr := ms_gpr msF 0) in *.
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr msF 1))) in *.
  set (n := Z_to_bv 64 nZ) in *.
  pose proof (alloc_top_lt (m_vmmaps mo)) as Htop. unfold two_pow_64 in Htop.
  destruct (page_round_up_n_facts (ms_gpr msF 1) Hlen ltac:(pose proof (word_unsigned_range addr); lia)) as (HnZpos & HnZal & Hun).
  fold nZ in HnZpos, HnZal, Hun. fold n in Hun.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (word_unsigned_range (ms_gpr msF 1)) as Hlr.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs msF x8)) = 222%Z) by (rewrite in_sysno_sys_input; exact Hno).
  assert (Hlen1 : ms_gpr msF 1 = Z_to_bv 64 (bv_unsigned (ms_gpr msF 1))).
  { symmetry. apply Z_to_bv_bv_unsigned. }
  assert (Hlenpos : 0 < bv_unsigned (ms_gpr msF 1)).
  { destruct (Z.eq_dec (bv_unsigned (ms_gpr msF 1)) 0) as [E|]; [|lia].
    exfalso. apply Hlen. apply bv_eq. rewrite E. reflexivity. }
  assert (Hargs : mmap_fixed_args_ok msF) by (repeat split; assumption).
  pose proof (mmap_fixed_outcome_si segs msF x8 mo addr (bv_unsigned (ms_gpr msF 1)) Hno Hargs eq_refl Hlen1
                ltac:(unfold two_pow_64 in Hlr; lia) Hce Hal Hpos Hrf Hmc) as Hspec.
  fold nZ in Hspec. fold n in Hspec.
  pose proof (li_budget _ _ _ (lzok_inv Hok)) as Hli. cbn [cfg_model] in Hli.
  pose proof (lazy_ranges_okb_nowrap L (lzok_ranges Hok)) as HLnw.
  assert (HLm : m_vm_lazy mo = L) by exact (li_lazy _ _ _ (lzok_inv Hok)).
  assert (Emo : fixed_noaccess_model addr n mo = commit_model (Z_to_bv 64 50) addr n true mo) by reflexivity.
  assert (Heag : eager_used (fixed_noaccess_model addr n mo) <= eager_used mo).
  { rewrite Emo. apply (eager_used_commit_covered_le (Z_to_bv 64 50) addr n true mo HX HNA ltac:(rewrite HLm; exact HLnw)).
    left. reflexivity. }
  set (msF' := advance_past_svc (apply_effect msF (mkEffectU addr [] [] [(addr, n)] [] []))).
  assert (Emem : ms_mem msF' = unfill addr n (ms_mem msF)).
  { unfold msF'. cbn [ms_mem advance_past_svc]. apply apply_effect_mem_unmaps. }
  assert (Haddr : refusal_b (sys_input segs msF x8) mo addr = false).
  { apply (addr_not_refusal_mmap _ mo addr Hno'). lia. }
  rewrite <- Hun in HRL.
  destruct (lzok_after_disjoint_op L S Zr msF mo msF' (fixed_noaccess_model addr n mo)
              (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Hok ltac:(lia) ltac:(pose proof (word_unsigned_range n); lia)
              ltac:(lia) HRL) as (Hok' & Hhid & Hhs).
  - rewrite Emo, commit_model_lazy. replace (mmap_noreserve_b (Z_to_bv 64 50)) with false by (vm_compute; reflexivity). reflexivity.
  - intros p Hp. rewrite Emo, commit_model_materialized in Hp. apply filter_In in Hp. tauto.
  - rewrite Emo, commit_model_materialized. apply NoDup_filter. exact (li_nodup _ _ _ (lzok_inv Hok)).
  - rewrite Emo, commit_model_vmmaps. reflexivity.
  - lia.
  - rewrite Emo. destruct (commit_model_nonvm (Z_to_bv 64 50) addr n true mo) as (_ & _ & _ & Hp & _).
    unfold m_halted. rewrite Hp. exact (lzok_halted Hok).
  - rewrite Emo, commit_model_vmmaps. cbn. exact (lzok_LM Hok).
  - intros x Hx. rewrite Emem. apply unfill_out. lia.
  - assert (Hnode : node_ok segs (mkCfg msF mo) unit (fun _ => [])
                      (fun _ => mkCfg msF' (fixed_noaccess_model addr n mo))).
    { apply (node_family_noacc_cfg msF mo x8 unit (fun _ => mkEffectU addr [] [] [(addr, n)] [] [])
               (fun _ => fixed_noaccess_model addr n mo) (fun _ => []) _ (lzok_halted Hok) Hsvc Hspec).
      - intros []. right; left. reflexivity.
      - intros []. apply spurious_refusal_not_refusal. cbn [eff_ret]. exact Haddr.
      - intros eff m' ev [He | [E | E]] Hns.
        + exfalso. apply Hns. apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->).
          eapply (alloc_refusal_spurious _ mo _ (mkEffectU addr [] [] [(addr, n)] [] []));
            [apply family_off_mmap_true; exact Hno' | cbn [eff_ret]; apply errno_is_refusal_mmap; exact Hno'
            | apply (proj2 (Hspec _)); right; left; reflexivity | cbn [eff_ret]; exact Haddr].
        + apply Ok_inj in E as (-> & -> & ->). exists tt. auto.
        + exfalso. apply Hns. apply Ok_inj in E as (-> & -> & ->).
          eapply (alloc_refusal_spurious _ mo _ (mkEffectU addr [] [] [(addr, n)] [] []));
            [apply family_off_mmap_true; exact Hno' | cbn [eff_ret]; apply errno_is_refusal_mmap; exact Hno'
            | apply (proj2 (Hspec _)); right; left; reflexivity | cbn [eff_ret]; exact Haddr].
      - intros eff m' ev [He | [E | E]].
        + apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->). exact (lzok_halted Hok).
        + apply Ok_inj in E as (-> & -> & ->). exact (lzok_halted Hok').
        + apply Ok_inj in E as (-> & -> & ->). unfold fixed_destroyed_model. rewrite vm_forget_range_halted, with_vmmaps_halted.
          exact (lzok_halted Hok).
      - intros [He | [E | E]]; [apply mmap_err_out_enomem in He; discriminate He | discriminate E | discriminate E].
      - intros []. reflexivity. }
    apply (sreach_node segs _ unit _ tt _ Hnode
             (RomBase.sys_rob_memfree segs msF mo x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_222))). intros [].
    rewrite Hun in Hok', Hhid. apply (Hk msF' Hok'); [| exact Hhs | exact Hhid | exact Heag].
    unfold msF'. rewrite (restrict_sysret L S). cbn [eff_ret]. f_equal.
    rewrite apply_effect_mem_unmaps, restrict_mem_unfill.
    apply functional_extensionality. intros x. unfold unfill.
    destruct ((bv_unsigned addr <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned addr + bv_unsigned n)) eqn:E; [reflexivity|].
    unfold restrict_mem, restrict_mem_by. cbn [ms_mem restrict restrict_by with_mem restrict_mem_by].
    rewrite (Hhid x). reflexivity.
Qed.


(* [comment removed for export] *)
Lemma map_has_In : forall maps (a n : word), map_has maps a n = true -> In (a, n) maps.
Proof.
  intros maps a n H. unfold map_has in H. apply existsb_exists in H. destruct H as ([b s] & Hin & Hb).
  apply andb_true_iff in Hb. destruct Hb as [H1 H2]. cbn [fst snd] in H1, H2.
  unfold bv_eqb in H1, H2. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
  apply bv_eq in H1. apply bv_eq in H2. subst. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma nooverlap_In_disj : forall X e e',
  nooverlap X -> In e X -> In e' X -> e = e' \/ hi e <= lo e' \/ hi e' <= lo e.
Proof.
  induction X as [|x X IH]; intros e e' HX He He'; [destruct He|].
  destruct HX as [Hx HX]. destruct He as [<- | He], He' as [<- | He'].
  - left; reflexivity.
  - right. apply Hx. exact He'.
  - right. destruct (Hx e He); lia.
  - apply IH; assumption.
Qed.

Lemma rsub_map_remove : forall L maps (a n : word),
  nooverlap maps -> In (a, n) maps -> 0 < bv_unsigned n ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> in_rangesb x L = false) ->
  rsub L maps -> rsub L (map_remove maps a).
Proof.
  intros L maps a n Hno Hin Hn HRL HLM x Hx.
  pose proof (HLM x Hx) as Hm. apply in_rangesb_true in Hm. destruct Hm as (b & s & Hbs & Hr).
  apply in_rangesb_true. exists b, s. split; [|exact Hr].
  unfold map_remove. apply filter_In. split; [exact Hbs|]. cbn [fst].
  apply negb_true_iff. apply Bool.not_true_is_false. intros Heq.
  unfold bv_eqb in Heq. apply Z.eqb_eq in Heq.
  destruct (nooverlap_In_disj maps (a, n) (b, s) Hno Hin Hbs) as [E | [D | D]].
  - injection E as <- <-. rewrite (HRL x Hr) in Hx. discriminate.
  - unfold hi, lo in D. cbn [fst snd] in D. lia.
  - unfold hi, lo in D. cbn [fst snd] in D. lia.
Qed.

(* 75d69e00: the unmap CUTS the range out of [vm_maps] instead of removing the
   entry based at [a] ([Mmap.mmap_fixed_destroyed_next]); a lazy range avoids the
   cut range, so it still lies under the ledger.  [rsub_map_remove] above is kept
   beside this, unchanged and still proved. *)
Lemma rsub_maps_subtract : forall L maps (a n : word),
  entries_nowrap maps ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> in_rangesb x L = false) ->
  rsub L maps -> rsub L (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n)).
Proof.
  intros L maps a n HNW HRL HLM x Hx.
  pose proof (bv_unsigned_in_range _ a) as Ra. pose proof (bv_unsigned_in_range _ n) as Rn.
  rewrite in_rangesb_zcovb.
  rewrite zcovb_maps_subtract by (try exact HNW; lia).
  apply andb_true_iff. split.
  - rewrite <- in_rangesb_zcovb. exact (HLM x Hx).
  - apply negb_true_iff. apply zinb_false. intros Hin.
    rewrite (HRL x Hin) in Hx. discriminate.
Qed.

(* [comment removed for export] *)
Lemma page_round_up_n_facts64 : forall (len : word),
  len <> Z_to_bv 64 0 ->
  let nZ := page_round_up_Z (bv_unsigned len) in
  (nZ < 2 ^ 64)%Z ->
  (0 < nZ)%Z /\ (nZ mod page_size = 0)%Z /\ bv_unsigned (Z_to_bv 64 nZ) = nZ.
Proof.
  intros len Hlen. cbv zeta. intros Hce.
  pose proof (PlacementSearch.page_round_up_Z_ge (bv_unsigned len)) as Hge. pose proof (word_unsigned_range len) as Hr.
  assert (bv_unsigned len <> 0%Z).
  { intros E. apply Hlen. apply bv_eq. rewrite E. reflexivity. }
  split; [lia|]. split; [apply PlacementSearch.page_round_up_Z_aligned|].
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

(* 75d69e00 made the old
     [Lemma munmap_model_eqL : forall a n m, munmap_model a n m = munmap_modelL a n m.]
   FALSE: munmap's ledger effect became [maps_subtract (vm_maps h) lo hi] where
   [LazyLedger.munmap_vmmaps] still does whole-entry [map_remove].  It is not
   recoverable under any premise this tree can discharge - for a zero-size entry
   (b, 0) with b = a + n, [iv_subtract] returns [] (the [hi <? b + 0] test is
   [b <? b]) where [map_remove] keeps (b, 0) - and no entries-nonzero invariant
   exists in lazy_inv, LazyLedger, AllocSim, AMODELX/AMODEL or LPS's State.v.
   Kept beside the new equation: the exact still-true residue of the old one,
   [munmap_model_vm_maps_eqL_nz], which says the two builders differ by exactly
   those weightless entries. *)
Lemma munmap_model_eqD : forall a n m, munmap_model a n m = munmap_modelD a n m.
Proof. reflexivity. Qed.

Lemma munmap_model_vm_maps_eqL_nz : forall (a n : word) m,
  0 < bv_unsigned n -> nooverlap (vm_maps (m_vmmaps m)) -> In (a, n) (vm_maps (m_vmmaps m)) ->
  vm_maps (m_vmmaps (munmap_model a n m))
  = List.filter (nz_at (bv_unsigned a + bv_unsigned n)) (vm_maps (m_vmmaps (munmap_modelL a n m))).
Proof.
  intros a n m Hn Hno Hin.
  rewrite munmap_model_eqD, munmap_modelD_vmmaps, munmap_modelL_vmmaps.
  cbn [vm_maps munmap_vmmapsD munmap_vmmaps].
  apply maps_subtract_rm_nz; assumption.
Qed.

Theorem sreach_munmap_lazy : forall L S Zr msF ms mo x8 (Q : config -> Prop),
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = ms ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 215%Z ->
  let a := ms_gpr ms 0 in
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  (bv_unsigned a mod page_size = 0)%Z ->
  len <> Z_to_bv 64 0 ->
  (bv_unsigned a + nZ <= TASK_SIZE)%Z ->
  map_has (vm_maps h) a n = true ->
  nooverlap (vm_maps h) -> entries_nowrap (vm_maps h) -> entries_nowrap (vm_noaccess h) ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ -> in_rangesb x L = false) ->
  (forall msF' : machine_state,
     let mo' := munmap_model a n mo in
     lzok segs (maps_subtract L (bv_unsigned a) (bv_unsigned a + nZ)) S Zr (mkCfg msF' mo') ->
     restrict (maps_subtract L (bv_unsigned a) (bv_unsigned a + nZ)) S msF'
       = sysret ms (Z_to_bv 64 0) (unfill a n (ms_mem ms)) ->
     hid_same L S msF msF' ->
     (forall x, hiddenb (maps_subtract L (bv_unsigned a) (bv_unsigned a + nZ)) S x = hiddenb L S x) ->
     (eager_used mo' + rem (a, n) (cuts mo) <= eager_used mo)%Z ->
     sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros L S Zr msF ms mo x8 Q Hok Hr Hsvc Hno. cbv zeta.
  intros Hal Hlen Hnw2 Hhas Hno_ov HX HNA HRL Hk.
  subst ms. rewrite restrict_svc in Hsvc. rewrite !ms_gpr_restrict in *.
  set (a := ms_gpr msF 0) in *.
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr msF 1))) in *.
  set (n := Z_to_bv 64 nZ) in *.
  pose proof (word_unsigned_range a) as Har.
  assert (Hts : TASK_SIZE = 0x800000000000%Z) by reflexivity.
  destruct (page_round_up_n_facts64 (ms_gpr msF 1) Hlen ltac:(lia)) as (HnZpos & HnZal & Hun).
  fold nZ in HnZpos, HnZal, Hun. fold n in Hun.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs msF x8)) = 215%Z) by (rewrite in_sysno_sys_input; exact Hno).
  assert (Hpr : page_round_up (ms_gpr msF 1) = n) by reflexivity.
  assert (Hargs : munmap_args_ok msF mo).
  { split; [exact Hal|]. split; [exact Hlen|]. split; [exact Hnw2|]. rewrite Hpr. exact Hhas. }
  pose proof (munmap_outcome_si segs msF x8 mo) as Hspec0.
  pose proof (li_budget _ _ _ (lzok_inv Hok)) as Hli. cbn [cfg_model] in Hli.
  pose proof (lazy_ranges_okb_nowrap L (lzok_ranges Hok)) as HLnw.
  assert (HLm : m_vm_lazy mo = L) by exact (li_lazy _ _ _ (lzok_inv Hok)).
  pose proof (rem_bounds (a, n) (cuts mo)) as Hrb.
  assert (Heag : eager_used (munmap_model a n mo) + rem (a, n) (cuts mo) <= eager_used mo).
  { rewrite munmap_model_eqD. apply (eager_used_munmap_leD a n mo HX HNA ltac:(rewrite HLm; exact HLnw) Hno_ov
      (map_has_In _ _ _ Hhas) ltac:(lia)). }
  set (msF' := advance_past_svc (apply_effect msF (munmap_eff msF))).
  assert (Emem : ms_mem msF' = unfill a n (ms_mem msF)).
  { unfold msF', munmap_eff. rewrite Hpr. cbn [ms_mem advance_past_svc]. apply apply_effect_mem_unmaps. }
  rewrite <- Hun in HRL.
  destruct (lzok_after_disjoint_op L S Zr msF mo msF' (munmap_model a n mo)
              (bv_unsigned a) (bv_unsigned a + bv_unsigned n) Hok ltac:(lia) ltac:(pose proof (word_unsigned_range n); lia)
              ltac:(lia) HRL) as (Hok' & Hhid & Hhs).
  - rewrite munmap_model_eqD, munmap_modelD_lazy. reflexivity.
  - intros p Hp. rewrite munmap_model_eqD, munmap_modelD_materialized in Hp. apply filter_In in Hp. tauto.
  - rewrite munmap_model_eqD, munmap_modelD_materialized. apply NoDup_filter. exact (li_nodup _ _ _ (lzok_inv Hok)).
  - rewrite munmap_model_eqD, munmap_modelD_vmmaps. reflexivity.
  - lia.
  - rewrite munmap_model_halted. exact (lzok_halted Hok).
  - rewrite munmap_model_eqD, munmap_modelD_vmmaps. cbn.
    apply (rsub_maps_subtract L (vm_maps (m_vmmaps mo)) a n HX HRL (lzok_LM Hok)).
  - intros x Hx. rewrite Emem. apply unfill_out. lia.
  - assert (Hnode : node_ok segs (mkCfg msF mo) unit (fun _ => [])
                      (fun _ => mkCfg msF' (munmap_model a n mo))).
    { (* 75d69e00: munmap's exact arm now also admits an -ENOMEM refusal that
         changes nothing.  It is spurious at this alloc-forced configuration, so
         the config-filtered node keeps only the cut; same shape as the in-unit
         As/AsanNodesLibE.v:356-371 munmap node. *)
      apply (node_family_noacc_cfg msF mo x8 unit (fun _ => munmap_eff msF)
               (fun _ => munmap_model a n mo) (fun _ => []) _ (lzok_halted Hok) Hsvc
               (fun o => Hspec0 o Hno Hargs)).
      - intros []. right. try rewrite Hpr; reflexivity.
      - intros []. apply spurious_refusal_not_refusal.
        rewrite (refusal_b_munmap _ mo _ Hno'). apply munmap_eff_ret_not_ENOMEM.
      - intros eff m' ev [(e & HIn & E) | E] Hnsp; apply Ok_inj in E as (-> & -> & ->).
        + exfalso. apply Hnsp. exact (munmap_refusal_spurious segs msF mo x8 e Hno Hargs HIn).
        + exists tt. repeat split; try rewrite Hpr; reflexivity.
      - intros eff m' ev [(e & _ & E) | E]; apply Ok_inj in E as (_ & -> & _);
          [exact (lzok_halted Hok) | rewrite munmap_model_halted; exact (lzok_halted Hok)].
      - intros [(e & _ & E) | E]; discriminate E.
      - intros []. reflexivity. }
    apply (sreach_node segs _ unit _ tt _ Hnode
             (RomBase.sys_rob_memfree segs msF mo x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_215))). intros [].
    rewrite Hun in Hok', Hhid. apply (Hk msF' Hok'); [| exact Hhs | exact Hhid | exact Heag].
    unfold msF', munmap_eff. rewrite Hpr. rewrite (restrict_sysret L S). cbn [eff_ret]. f_equal.
    rewrite apply_effect_mem_unmaps, restrict_mem_unfill. fold a.
    apply functional_extensionality. intros x. unfold unfill.
    destruct ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + bv_unsigned n)) eqn:E; [reflexivity|].
    unfold restrict_mem, restrict_mem_by. cbn [ms_mem restrict restrict_by with_mem restrict_mem_by].
    rewrite (Hhid x). reflexivity.
Qed.


(* [comment removed for export] *)
Lemma lzok_after_eager_op : forall L S Zr msF mo msF' mo' (l hh : Z),
  lzok segs L S Zr (mkCfg msF mo) ->
  (forall x : word, l <= bv_unsigned x < hh -> in_rangesb x L = false) ->
  m_vm_lazy mo' = m_vm_lazy mo ->
  m_vm_materialized mo' = m_vm_materialized mo ->
  vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) ->
  (eager_used mo' + pages_total S * page_size <= vm_limit (m_vmmaps mo))%Z ->
  m_halted mo' = None ->
  rsub L (vm_maps (m_vmmaps mo')) ->
  (forall x : word, ~ (l <= bv_unsigned x < hh) -> ms_mem msF' x = ms_mem msF x) ->
  lzok segs L S Zr (mkCfg msF' mo') /\ hid_same L S msF msF'.
Proof.
  intros L S Zr msF mo msF' mo' l hh [HL Hinv Hh HZ HSZ HZL HLM] HRL Elazy Emat Elim Hbud Hh' HLM' Hmem.
  cbn in *.
  assert (Hhs : hid_same L S msF msF').
  { intros x Hx. apply Hmem. intros HxR. apply hiddenb_true_iff in Hx. destruct Hx as [HxL _].
    rewrite (HRL x HxR) in HxL. discriminate. }
  split; [|exact Hhs]. split; cbn; try assumption.
  - split.
    + rewrite Elazy. exact (li_lazy _ _ _ Hinv).
    + rewrite Emat. exact (li_nodup _ _ _ Hinv).
    + rewrite Emat. exact (li_incl _ _ _ Hinv).
    + rewrite Elim. exact Hbud.
  - intros x Hx Hz. rewrite (Hhs x Hx). exact (HZ x Hx Hz).
Qed.

(* [comment removed for export] *)
Theorem sreach_mprotect_lazy : forall L S Zr msF ms mo x8 (Q : config -> Prop),
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = ms ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 226%Z ->
  let addr := ms_gpr ms 0 in
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  (bv_unsigned addr mod page_size = 0)%Z ->
  len <> Z_to_bv 64 0 ->
  (bv_unsigned addr + nZ < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  (* 75d69e00: mprotect_outcome_si's exact arm now also asks that the range is
     clear of the launch's extra reserved intervals (the vDSO text and the vvar
     pages).  Same premise, same position, as the already-repaired in-unit
     As/AsanNodesMmLib.v:1054 and As/AllocNodes.v:447,485 nodes; a caller
     discharges it from co_vdso plus region_free (vm_reserved ...) through
     MmapSim.region_free_vdso_of_reserved.  No kernel field is pinned. *)
  region_free (vdso_reserved (m_kernel mo) (vdso_top h)) addr n = true ->
  map_contains (vm_noaccess h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  entries_nowrap (vm_maps h) -> entries_nowrap (vm_noaccess h) -> nooverlap (vm_maps h) ->
  (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ -> in_rangesb x L = false) ->
  (eager_used mo + pages_total S * page_size + nZ <= vm_limit h)%Z ->
  (forall msF' : machine_state,
     let mo' := mprotect_model addr n mo in
     lzok segs L S Zr (mkCfg msF' mo') ->
     restrict L S msF' = sysret ms (Z_to_bv 64 0) (zfill addr n (ms_mem ms)) ->
     hid_same L S msF msF' ->
     (eager_used mo' <= eager_used mo + nZ)%Z ->
     sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros L S Zr msF ms mo x8 Q Hok Hr Hsvc Hno. cbv zeta.
  intros Hal Hlen Hnw2 H2 Hrfv Hcna Hcm HX HNA Hno_ov HRL Hbud Hk.
  subst ms. rewrite restrict_svc in Hsvc. rewrite !ms_gpr_restrict in *.
  set (addr := ms_gpr msF 0) in *.
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr msF 1))) in *.
  set (n := Z_to_bv 64 nZ) in *.
  pose proof (word_unsigned_range addr) as Har.
  destruct (page_round_up_n_facts64 (ms_gpr msF 1) Hlen ltac:(unfold two_pow_64 in Hnw2; lia)) as (HnZpos & HnZal & Hun).
  fold nZ in HnZpos, HnZal, Hun. fold n in Hun.
  pose proof (word_unsigned_range (ms_gpr msF 1)) as Hlr.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs msF x8)) = 226%Z) by (rewrite in_sysno_sys_input; exact Hno).
  assert (Hlen1 : ms_gpr msF 1 = Z_to_bv 64 (bv_unsigned (ms_gpr msF 1))).
  { symmetry. apply Z_to_bv_bv_unsigned. }
  assert (Hlenpos : 0 < bv_unsigned (ms_gpr msF 1)).
  { destruct (Z.eq_dec (bv_unsigned (ms_gpr msF 1)) 0) as [E|]; [|lia].
    exfalso. apply Hlen. apply bv_eq. rewrite E. reflexivity. }
  pose proof (li_budget _ _ _ (lzok_inv Hok)) as Hli. cbn [cfg_model] in Hli.
  pose proof (lazy_ranges_okb_nowrap L (lzok_ranges Hok)) as HLnw.
  assert (HLm : m_vm_lazy mo = L) by exact (li_lazy _ _ _ (lzok_inv Hok)).
  pose proof (lzok_backing_used_le segs L S Zr _ Hok) as Hbk. cbn [cfg_model] in Hbk.
  assert (Emo : mprotect_model addr n mo = mprotect_model_next mo addr n) by reflexivity.
  assert (Heag : eager_used (mprotect_model addr n mo) <= eager_used mo + nZ).
  { rewrite Emo, <- Hun. apply (eager_used_mprotect_le addr n mo HX HNA ltac:(rewrite HLm; exact HLnw) Hno_ov).
    destruct (map_contains_In _ _ _ Hcm) as (e0 & He0 & He1 & He2). exists e0.
    unfold lo, hi in *. cbn [fst snd]. auto. }
  assert (Hbok : mprotect_budget_ok mo addr n = true).
  { unfold mprotect_budget_ok, vm_backing_within_limit. apply Z.leb_le. rewrite <- Emo.
    rewrite vm_backing_used_split.
    replace (m_vm_materialized (mprotect_model addr n mo)) with (m_vm_materialized mo) by reflexivity.
    replace (vm_limit (m_vmmaps (mprotect_model addr n mo))) with (vm_limit (m_vmmaps mo)) by reflexivity.
    rewrite vm_backing_used_split in Hbk. lia. }
  pose proof (mprotect_outcome_si segs msF x8 mo addr (bv_unsigned (ms_gpr msF 1)) Hno eq_refl Hlen1 H2
                Hlenpos ltac:(unfold two_pow_64 in Hnw2; exact Hnw2) Hal Hrfv Hcna Hcm) as Hspec.
  cbv zeta in Hspec. fold nZ in Hspec. fold n in Hspec.
  set (msF' := advance_past_svc (apply_effect msF (mkEffect (Z_to_bv 64 0) [] [(addr, n)]))).
  assert (Emem : ms_mem msF' = zfill addr n (ms_mem msF)).
  { unfold msF'. cbn [ms_mem advance_past_svc]. apply functional_extensionality. intros x.
    cbn. unfold zfill, zmem, zeros_cover. cbn.
    destruct ((bv_unsigned addr <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned addr + bv_unsigned n)); reflexivity. }
  rewrite <- Hun in HRL.
  destruct (lzok_after_eager_op L S Zr msF mo msF' (mprotect_model addr n mo)
              (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Hok HRL eq_refl eq_refl eq_refl
              ltac:(lia) (lzok_halted Hok) (lzok_LM Hok)) as (Hok' & Hhs).
  - intros x Hx. rewrite Emem. apply zfill_out. lia.
  - assert (Hnode : node_ok segs (mkCfg msF mo) unit (fun _ => [])
                      (fun _ => mkCfg msF' (mprotect_model addr n mo))).
    { apply (node_family_noacc_cfg msF mo x8 unit (fun _ => mkEffect (Z_to_bv 64 0) [] [(addr, n)])
               (fun _ => mprotect_model addr n mo) (fun _ => []) _ (lzok_halted Hok) Hsvc Hspec).
      - intros []. right. split; [exact Hbok | reflexivity].
      - intros []. apply spurious_refusal_not_refusal. cbn [eff_ret]. apply zero_not_refusal_mprotect. exact Hno'.
      - intros eff m' ev [He | (_ & E)] Hns.
        + exfalso. apply Hns. apply mprotect_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->).
          eapply (alloc_refusal_spurious _ mo _ (mkEffect (Z_to_bv 64 0) [] [(addr, n)]));
            [apply family_off_mprotect_true; exact Hno' | cbn [eff_ret]; apply errno_is_refusal_mprotect; exact Hno'
            | apply (proj2 (Hspec _)); right; split; [exact Hbok | reflexivity]
            | cbn [eff_ret]; apply zero_not_refusal_mprotect; exact Hno'].
        + apply Ok_inj in E as (-> & -> & ->). exists tt. auto.
      - intros eff m' ev [He | (_ & E)].
        + apply mprotect_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->). exact (lzok_halted Hok).
        + apply Ok_inj in E as (-> & -> & ->). exact (lzok_halted Hok').
      - intros [He | (_ & E)]; [apply mprotect_err_out_enomem in He; discriminate He | discriminate E].
      - intros []. reflexivity. }
    apply (sreach_node segs _ unit _ tt _ Hnode
             (RomBase.sys_rob_memfree segs msF mo x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_226))). intros [].
    apply (Hk msF' Hok'); [| exact Hhs | exact Heag].
    unfold msF'. rewrite (restrict_sysret L S). cbn [eff_ret]. f_equal.
    fold msF'. change (ms_mem (apply_effect msF (mkEffect (Z_to_bv 64 0) [] [(addr, n)]))) with (ms_mem msF').
    rewrite Emem. apply restrict_mem_zfill_visible.
    intros x Hx. apply hiddenb_outside_L. apply HRL. exact Hx.
Qed.

Local Close Scope Z_scope.


Local Open Scope Z_scope.

(* [comment removed for export] *)
Theorem sreach_brk_query_lazy : forall L S Zr msF ms mo x8 (Q : config -> Prop),
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = ms ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  ms_gpr ms 0 = Z_to_bv 64 0 ->
  (forall msF', lzok segs L S Zr (mkCfg msF' mo) ->
     restrict L S msF' = sysret ms (vm_brk (m_vmmaps mo)) (ms_mem ms) ->
     hid_same L S msF msF' ->
     sreach segs Q (mkCfg msF' mo)) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros L S Zr msF ms mo x8 Q Hok Hr Hsvc Hno H0 Hk.
  subst ms. rewrite restrict_svc in Hsvc. rewrite !ms_gpr_restrict in *.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs msF x8)) = 214%Z) by (rewrite in_sysno_sys_input; exact Hno).
  set (b := vm_brk (m_vmmaps mo)).
  assert (Hcases : forall r, brk_resolution_ok mo (ms_gpr msF 0) r <-> r = b).
  { intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
    unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
  set (eff := mkEffectU b [] (brk_zeros (ms_gpr msF 0) b b) (brk_unmaps b b) [] []).
  assert (Emo : brk_model (ms_gpr msF 0) b mo = mo).
  { unfold b. apply brk_model_keep. }
  assert (Hnode : node_ok segs (mkCfg msF mo) unit (fun _ => [])
                    (fun _ => mkCfg (advance_past_svc (apply_effect msF eff)) mo)).
  { apply (node_family_noacc msF mo x8 unit (fun _ => eff) (fun _ => mo) (fun _ => [])
             _ (lzok_halted Hok) Hsvc (fun o => brk_outcome_si segs msF x8 mo o Hno)).
    - intros []. exists b. split; [apply Hcases; reflexivity | rewrite Emo; reflexivity].
    - intros []. apply spurious_refusal_not_refusal. unfold eff. cbn [eff_ret].
      rewrite (refusal_b_brk _ mo b Hno'), in_arg0_sys_input, H0. reflexivity.
    - intros o (r & Hr & ->). apply Hcases in Hr. subst r. rewrite Emo. exists tt. reflexivity.
    - intros []. exact (lzok_halted Hok).
    - intros []. reflexivity. }
  apply (sreach_node segs _ unit _ tt _ Hnode
           (RomBase.sys_rob_memfree segs msF mo x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_214))). intros [].
  assert (Emem : ms_mem (apply_effect msF eff) = ms_mem msF).
  { unfold eff. rewrite brk_zeros_keep, brk_unmaps_keep. destruct msF; reflexivity. }
  assert (Hhs : hid_same L S msF (advance_past_svc (apply_effect msF eff))).
  { intros a Ha. cbn [ms_mem advance_past_svc]. rewrite Emem. reflexivity. }
  apply Hk.
  - eapply lzok_vm_frame; [exact Hok | reflexivity | exact (lzok_halted Hok) | exact Hhs].
  - rewrite (restrict_sysret L S). rewrite Emem. reflexivity.
  - exact Hhs.
Qed.
Scheme kc__9 := Elimination for LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state Sort Prop.

(* [comment removed for export] *)
Theorem sreach_brk_grow_lazy : forall L S Zr msF ms mo x8 (d : Z) (Q : config -> Prop),
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = ms ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  let h := m_vmmaps mo in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  ms_gpr ms 0 = Z_to_bv 64 (bv_unsigned b + d) ->
  entries_nowrap (vm_maps h) ->
  (eager_used mo + pages_total S * page_size + d <= vm_limit h)%Z ->   (* [comment removed for export] *)
  (forall msF',                                   (* [comment removed for export] *)
     Mmap.brk_grow_ok mo (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = false ->
     lzok segs L S Zr (mkCfg msF' mo) ->
     restrict L S msF' = sysret ms b (ms_mem ms) ->
     hid_same L S msF msF' ->
     sreach segs Q (mkCfg msF' mo)) ->
  (forall msF',                                   (* [comment removed for export] *)
     let mo' := with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                 (vm_noaccess h) (vm_start_brk h)
                                 (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo in
     Mmap.brk_grow_ok mo (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
     region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (d + page_size)) = true ->
     lzok segs L S Zr (mkCfg msF' mo') ->
     restrict L S msF' = sysret ms (Z_to_bv 64 (bv_unsigned b + d)) (zfill b (Z_to_bv 64 d) (ms_mem ms)) ->
     hid_same L S msF msF' ->
     (eager_used mo' <= eager_used mo + d)%Z ->
     sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros L S Zr msF ms mo x8 d Q Hok Hr Hsvc Hno. cbv zeta.
  intros Hbal Hdal Hd Hb0 Hnw Hs H0 HX Hroom Hkref Hkgr.
  subst ms. rewrite restrict_svc in Hsvc. rewrite !ms_gpr_restrict in *.
  set (h := m_vmmaps mo) in *. set (b := vm_brk h) in *.
  pose proof (word_unsigned_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs msF x8)) = 214%Z) by (rewrite in_sysno_sys_input; exact Hno).
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z).
  { unfold req. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
  assert (Hud : bv_unsigned (Z_to_bv 64 d) = d).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
  assert (Hcases : forall r, brk_resolution_ok mo (ms_gpr msF 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok mo req req = true))).
  { intros r. rewrite H0. apply brk_r_ok_grow_cases; fold h; fold b; rewrite ?Hureq; lia. }
  assert (Hneq : req <> b).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. lia. }
  assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
  assert (Hrfb : forall r, refusal_b (sys_input segs msF x8) mo r = bv_eqb r b).
  { intros r. rewrite (refusal_b_brk _ mo r Hno'), in_arg0_sys_input, H0.
    apply (brk_refusal_b_grow mo req r); fold h; fold b; rewrite ?Hureq; lia. }
  pose (E := fun r : word => mkEffectU r [] (brk_zeros (ms_gpr msF 0) r b) (brk_unmaps r b) [] []).
  assert (Hh' : forall r, r = b \/ r = req -> m_halted (brk_model (ms_gpr msF 0) r mo) = None).
  { intros r [-> | ->].
    - unfold b, h. rewrite brk_model_keep. exact (lzok_halted Hok).
    - rewrite H0. unfold req, b, h. rewrite (brk_model_grow_eq mo d) by assumption. exact (lzok_halted Hok). }
  destruct (Sumbool.sumbool_of_bool (Mmap.brk_grow_ok mo req req)) as [Hg | Hg].
  - (* [comment removed for export] *)
    assert (Hnode : node_ok segs (mkCfg msF mo) unit (fun _ => [])
                      (fun _ => mkCfg (advance_past_svc (apply_effect msF (E req))) (brk_model (ms_gpr msF 0) req mo))).
    { apply (node_family_noacc_cfg msF mo x8 unit (fun _ => E req) (fun _ => brk_model (ms_gpr msF 0) req mo) (fun _ => [])
               _ (lzok_halted Hok) Hsvc (fun o => brk_outcome_si segs msF x8 mo o Hno)).
      - intros []. exists req. split; [apply Hcases; right; auto | reflexivity].
      - intros []. apply spurious_refusal_not_refusal. unfold E. cbn [eff_ret]. rewrite Hrfb. apply bv_eqb_neq. exact Hneq.
      - intros eff m' ev (r & Hr0 & E0) Hns. apply Ok_inj in E0 as (-> & -> & ->).
        destruct (proj1 (Hcases r) Hr0) as [-> | [-> _]].
        + exfalso. apply Hns.
          eapply (alloc_refusal_spurious _ mo _ (E req));
            [apply family_off_brk_true; exact Hno'
            | cbn [eff_ret]; rewrite Hrfb; apply bv_eqb_refl
            | apply (proj2 (brk_outcome_si segs msF x8 mo _ Hno)); exists req; split; [apply Hcases; right; auto | reflexivity]
            | unfold E; cbn [eff_ret]; rewrite Hrfb; apply bv_eqb_neq; exact Hneq].
        + exists tt. auto.
      - intros eff m' ev (r & Hr0 & E0). apply Ok_inj in E0 as (-> & -> & ->).
        apply Hh'. destruct (proj1 (Hcases r) Hr0) as [-> | [-> _]]; auto.
      - intros (r & _ & E0). discriminate E0.
      - intros []. reflexivity. }
    apply (sreach_node segs _ unit _ tt _ Hnode
             (RomBase.sys_rob_memfree segs msF mo x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_214))). intros []. unfold E.
    assert (Hreq0 : req <> Z_to_bv 64 0).
    { intros E0. apply (f_equal bv_unsigned) in E0. rewrite Hureq in E0.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E0. lia. }
    rewrite H0. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
    unfold brk_page_range.
    rewrite (AllocSim.page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
    rewrite (AllocSim.page_round_up_Z_aligned (bv_unsigned req))
      by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
    rewrite (proj2 (Z.ltb_lt _ _) Hlt).
    replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
    rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
    unfold req. unfold b, h. rewrite (brk_model_grow_eq mo d) by assumption. fold h. fold b. fold req.
    (* [comment removed for export] *)
    assert (Hfree : region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (d + page_size)) = true).
    { unfold Mmap.brk_grow_ok in Hg. fold h b in Hg.
      rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt _ _) Hlt) in Hg. cbn [andb] in Hg.
      rewrite (AllocSim.page_round_up_Z_aligned (bv_unsigned b)) in Hg by (first [lia | exact Hbal]).
      rewrite (AllocSim.page_round_up_Z_aligned (bv_unsigned req)) in Hg
        by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
      rewrite (proj2 (Z.ltb_lt _ _) Hlt) in Hg.
      replace (Z_to_bv 64 (bv_unsigned b)) with b in Hg by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
      rewrite Hureq in Hg. replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z in Hg by lia.
      apply andb_true_iff in Hg. destruct Hg as [Hg _]. apply andb_true_iff in Hg. tauto. }
    assert (Htop : (bv_unsigned b + d <= alloc_top h)%Z).
    { unfold Mmap.brk_grow_ok in Hg. fold h b in Hg.
      rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt _ _) Hlt) in Hg. cbn [andb] in Hg.
      rewrite (AllocSim.page_round_up_Z_aligned (bv_unsigned b)) in Hg by (first [lia | exact Hbal]).
      rewrite (AllocSim.page_round_up_Z_aligned (bv_unsigned req)) in Hg
        by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
      rewrite (proj2 (Z.ltb_lt _ _) Hlt) in Hg.
      apply andb_true_iff in Hg. destruct Hg as [Hg _]. apply andb_true_iff in Hg. destruct Hg as [Hg _].
      apply Z.leb_le in Hg. rewrite Hureq in Hg. exact Hg. }
    pose proof (alloc_top_page_lt h) as Htp. unfold two_pow_64 in Htp.
    assert (Hudp : bv_unsigned (Z_to_bv 64 (d + page_size)) = (d + page_size)%Z).
    { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64). unfold page_size in *. lia. }
    assert (Hfree' : region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 d) = true).
    { apply (AllocSim.region_free_prefix _ b (Z_to_bv 64 d) (Z_to_bv 64 (d + page_size))); [|exact Hfree].
      rewrite Hud, Hudp. unfold page_size. lia. }
    assert (HRL : forall x : word, bv_unsigned b <= bv_unsigned x < bv_unsigned b + d -> in_rangesb x L = false).
    { intros x Hx. pose proof (region_free_not_in _ b (Z_to_bv 64 d) x (region_free_app_r _ _ _ _ Hfree') ltac:(rewrite Hud; lia)) as HM.
      destruct (in_rangesb x L) eqn:E0; [|reflexivity]. pose proof (lzok_LM Hok x E0) as HM2. cbn [cfg_model] in HM2.
      fold h in HM2. rewrite HM2 in HM. discriminate. }
    set (mo' := with_vmmaps _ mo).
    set (msF' := advance_past_svc (apply_effect msF (mkEffectU req [] [(b, Z_to_bv 64 d)] [] [] []))).
    assert (Emem : ms_mem msF' = zfill b (Z_to_bv 64 d) (ms_mem msF)).
    { unfold msF'. cbn [ms_mem advance_past_svc]. apply functional_extensionality. intros x.
      cbn. unfold zfill, zmem, zeros_cover. cbn.
      destruct ((bv_unsigned b <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned b + bv_unsigned (Z_to_bv 64 d))); reflexivity. }
    pose proof (li_budget _ _ _ (lzok_inv Hok)) as Hli. cbn [cfg_model] in Hli.
    pose proof (lzok_backing_used_le segs L S Zr _ Hok) as Hbk. cbn [cfg_model] in Hbk.
    assert (Heag : eager_used mo' <= eager_used mo + d).
    { unfold mo'. rewrite <- Hud at 2.
      apply (eager_used_with_vmmaps_cons_le mo (b, Z_to_bv 64 d)); [exact HX | | reflexivity | reflexivity].
      unfold entry_nowrap, hi. cbn [fst snd]. rewrite Hud. lia. }
    (* [comment removed for export] *)
    assert (Hbudg : (vm_backing_used mo + d <= vm_limit h)%Z).
    { unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok in Hg. fold h b in Hg.
      rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt _ _) Hlt) in Hg. cbn [andb] in Hg.
      apply andb_true_iff in Hg. destruct Hg as [_ Hg]. apply Z.leb_le in Hg.
      (* 75d69e00: the budget charges [brk_grow_bytes] = max 0 (page_round_up r
         - page_round_up brk), not [bv_unsigned (req - b)].  Both ends are page
         aligned here, so it is [d].  Same three lines as the already-repaired
         in-unit As/AsanNodesMmB.v:135-138 and As/AsanRefNodes.v:537-540. *)
      unfold Mmap.brk_grow_bytes in Hg. fold h b in Hg. rewrite Hureq in Hg.
      rewrite (page_round_up_Z_aligned (bv_unsigned b)) in Hg by (first [lia | exact Hbal]).
      rewrite (page_round_up_Z_aligned (bv_unsigned b + d)) in Hg
        by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
      lia. }
    destruct (lzok_after_eager_op L S Zr msF mo msF' mo' (bv_unsigned b) (bv_unsigned b + d) Hok HRL
                eq_refl eq_refl eq_refl) as (Hok' & Hhs).
    + unfold mo' in Heag |- *. unfold b, h, page_size in *. lia.
    + exact (lzok_halted Hok).
    + unfold mo'. cbn. apply rsub_cons_r. exact (lzok_LM Hok).
    + intros x Hx. rewrite Emem. apply zfill_out. rewrite Hud. lia.
    + apply (Hkgr msF' Hg Hfree Hok'); [| exact Hhs | exact Heag].
      unfold msF'. rewrite (restrict_sysret L S). cbn [eff_ret]. f_equal.
      fold msF'. change (ms_mem (apply_effect msF (mkEffectU req [] [(b, Z_to_bv 64 d)] [] [] []))) with (ms_mem msF').
      rewrite Emem. apply restrict_mem_zfill_visible.
      intros x Hx. apply hiddenb_outside_L. apply HRL. rewrite Hud in Hx. exact Hx.
  - (* [comment removed for export] *)
    assert (Hnode : node_ok segs (mkCfg msF mo) unit (fun _ => [])
                      (fun _ => mkCfg (advance_past_svc (apply_effect msF (E b))) (brk_model (ms_gpr msF 0) b mo))).
    { apply (node_family_noacc msF mo x8 unit (fun _ => E b) (fun _ => brk_model (ms_gpr msF 0) b mo) (fun _ => [])
               _ (lzok_halted Hok) Hsvc (fun o => brk_outcome_si segs msF x8 mo o Hno)).
      - intros []. exists b. split; [apply Hcases; left; reflexivity | reflexivity].
      - intros []. apply not_spurious_all_refusals. intros eff' m' evs' Hsp.
        apply (proj1 (brk_outcome_si segs msF x8 mo _ Hno)) in Hsp. destruct Hsp as (r & Hr0 & E0).
        apply Ok_inj in E0 as (-> & -> & ->). cbn [eff_ret]. rewrite Hrfb.
        destruct (proj1 (Hcases r) Hr0) as [-> | [-> Hg']]; [apply bv_eqb_refl | rewrite Hg in Hg'; discriminate Hg'].
      - intros o (r & Hr0 & ->). destruct (proj1 (Hcases r) Hr0) as [-> | [-> Hg']]; [exists tt; reflexivity | rewrite Hg in Hg'; discriminate Hg'].
      - intros []. apply Hh'. left. reflexivity.
      - intros []. reflexivity. }
    apply (sreach_node segs _ unit _ tt _ Hnode
             (RomBase.sys_rob_memfree segs msF mo x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_214))). intros []. unfold E.
    rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep. fold h. fold b.
    assert (Emem : ms_mem (apply_effect msF (mkEffectU b [] [] [] [] [])) = ms_mem msF) by (destruct msF; reflexivity).
    assert (Hhs : hid_same L S msF (advance_past_svc (apply_effect msF (mkEffectU b [] [] [] [] [])))).
    { intros a Ha. cbn [ms_mem advance_past_svc]. rewrite Emem. reflexivity. }
    apply Hkref.
    + exact Hg.
    + eapply lzok_vm_frame; [exact Hok | reflexivity | exact (lzok_halted Hok) | exact Hhs].
    + rewrite (restrict_sysret L S). rewrite Emem. reflexivity.
    + exact Hhs.
Qed.

Local Close Scope Z_scope.

End WithSegs.
