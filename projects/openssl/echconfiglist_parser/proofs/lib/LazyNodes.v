(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  Scfg SimInv ExitSim PropExec CatSim MmapSim AllocSim RelSpec
  ShapeAlg Nodes AgentNodes Gap04 RefNodes SReach AllocNodes
  LazyRestrict LazyRestrictRun LazyRestrictAlg LazyLedger LazySR.
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
Definition sysret (ms : machine_state) (r : word) (M : word -> option byte) : machine_state :=
  {| ms_regs := ms_regs (set_reg ms 10 r); ms_fregs := ms_fregs ms;
     ms_pc_val := ms_pc ms + Z_to_bv 64 4; ms_svc_pending := None;
     ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms; ms_mem := M; ms_rom := ms_rom ms |}.

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

(* [comment removed for export] *)
Lemma mmap_kernel_spec : forall (na nr : bool) ms mo x8 o,
  bv_unsigned x8 = 222%Z ->
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 (kprot na) -> ms_gpr ms 3 = Z_to_bv 64 (kflags nr) ->
  ms_gpr ms 5 = Z_to_bv 64 0 ->
  syscall_spec (sys_input segs ms x8) mo o <->
  mmap_err_out mo o
  \/ exists a, ((bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
                /\ (bv_unsigned a + nZ <= alloc_top h)%Z
                /\ region_free (vm_reserved h ++ vm_maps h) a n = true
                /\ (na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (kflags nr)) mo nZ = true))
               /\ o = Ok (keff na a n) (grant_model (Z_to_bv 64 (kflags nr)) a n na mo) [].
Proof.
  intros na nr ms mo x8 o Hno. cbv zeta. intros Hlen H2 H3 H5.
  destruct (kgates na nr) as (Go & Ga & Gm & Gn & Gb).
  rewrite (syscall_spec_222 _ mo o) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_sys_input, in_arg1_sys_input', in_arg2_sys_input',
          in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input.
  rewrite H2, H3, H5.
  destruct na.
  - rewrite (mmap_noaccess_outcome _ _ _ _ _ _ _ mo o Go Ga (w_is0_false _ Hlen) Gm Gn).
    unfold grant_model, grant_vmmaps, keff.
    split; (intros [He | (a & Hc & ->)]; [left; exact He | right; exists a; split; [|reflexivity]]);
      [destruct Hc as (C1 & C2 & C3 & C4); repeat split; auto; discriminate
      |destruct Hc as (C1 & C2 & C3 & C4 & _); repeat split; auto].
  - rewrite (mmap_rw_outcome _ _ _ _ _ _ _ mo o Go Ga (w_is0_false _ Hlen) Gm).
    unfold grant_model, grant_vmmaps, keff. cbn [negb].
    split; (intros [He | (a & Hc & ->)]; [left; exact He | right; exists a; split; [|reflexivity]]);
      [destruct Hc as (C1 & C2 & C3 & C4 & C5); repeat split; auto
      |destruct Hc as (C1 & C2 & C3 & C4 & C5); repeat split; auto].
Qed.

(* [comment removed for export] *)
Lemma mmap_kernel_grant_ok : forall (na nr : bool) ms mo x8 (g : word),
  bv_unsigned x8 = 222%Z ->
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  len <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 (kprot na) -> ms_gpr ms 3 = Z_to_bv 64 (kflags nr) ->
  ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned g mod page_size = 0)%Z -> (0 < bv_unsigned g)%Z -> (bv_unsigned g + nZ <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) g n = true ->
  (na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (kflags nr)) mo nZ = true) ->
  syscall_spec (sys_input segs ms x8) mo (Ok (keff na g n) (grant_model (Z_to_bv 64 (kflags nr)) g n na mo) []).
Proof.
  intros na nr ms mo x8 g Hno. cbv zeta. intros Hlen H2 H3 H5 G1 G2 G3 G4 G5.
  apply (proj2 (mmap_kernel_spec na nr ms mo x8 _ Hno Hlen H2 H3 H5)). right. exists g. split; [|reflexivity].
  repeat split; assumption.
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
  entries_nowrap (vm_maps h) ->
  (na = false -> nr = false -> (eager_used mo + pages_total S * page_size + nZ <= vm_limit h)%Z) ->
  (exists g : word, (bv_unsigned g mod page_size = 0)%Z /\ (0 < bv_unsigned g)%Z
                    /\ (bv_unsigned g + nZ <= alloc_top h)%Z
                    /\ region_free (vm_reserved h ++ vm_maps h) g n = true) ->
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
  intros Hlen H2 H3 H4 H5 Hnw Hbud (g & Hgal & Hgpos & Hgce & Hgfree) Hrok Hk.
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
                         /\ (na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (kflags nr)) mo nZ = true)}).
  pose (effs := fun i : I => keff na (proj1_sig i) n).
  pose (ms' := fun i : I => grant_model (Z_to_bv 64 (kflags nr)) (proj1_sig i) n na mo).
  assert (Hg : (bv_unsigned g mod page_size = 0)%Z /\ (0 < bv_unsigned g)%Z
               /\ (bv_unsigned g + nZ <= alloc_top (m_vmmaps mo))%Z
               /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) g n = true
               /\ (na = false -> mmap_noreserve_backed_ok (Z_to_bv 64 (kflags nr)) mo nZ = true)).
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
             (fun o => mmap_kernel_spec na nr msF mo x8 o Hno Hlen H2 H3 H5)).
    - intros [a Ha]. right. exists a. split; [exact Ha | reflexivity].
    - intros [a (A1 & A2 & A3 & A4 & A5)]. apply spurious_refusal_not_refusal. unfold effs. cbn [proj1_sig].
      rewrite keff_ret. apply Hplace; assumption.
    - intros eff m' ev [He | (a & Ha & E)] Hns.
      + exfalso. apply Hns. apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->).
        apply (alloc_refusal_spurious _ mo _ (keff na g n) (grant_model (Z_to_bv 64 (kflags nr)) g n na mo) []).
        * apply family_off_mmap_true. exact Hno'.
        * cbn [eff_ret]. apply errno_is_refusal_mmap. exact Hno'.
        * apply (mmap_kernel_grant_ok na nr msF mo x8 g Hno Hlen H2 H3 H5 Hgal Hgpos Hgce Hgfree Hbk').
        * rewrite keff_ret. apply Hplace; assumption.
      + apply Ok_inj in E as (-> & -> & ->). exists (exist _ a Ha). auto.
    - intros eff m' ev [He | (a & _ & E)].
      + apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->). exact (lzok_halted Hok).
      + apply Ok_inj in E as (-> & -> & ->). rewrite grant_model_halted. exact (lzok_halted Hok).
    - intros [He | (a & _ & E)]; [apply mmap_err_out_enomem in He; discriminate He | discriminate E].
    - intros i. apply keff_accesses. }
  apply (sreach_node segs _ I _ (exist _ g Hg) _ Hnode).
  intros [a (Hal & Hpos & Hce & Hfree & Ha5)]. cbn [proj1_sig].
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
  intros na nr ms mo x8 o Hno. cbv zeta. intros Hlen H2 H3 H5 Hce Hal Hpos Hfree.
  destruct (fgates na nr) as (Go & Ga & Gm & Gn & Gfn & Gfr & Gb).
  rewrite (syscall_spec_222 _ mo o) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_sys_input, in_arg1_sys_input', in_arg2_sys_input',
          in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input.
  rewrite H2, H3, H5.
  destruct na.
  - rewrite (mmap_fixed_noaccess_fresh_outcome _ _ _ _ _ _ _ mo o Go Ga (w_is0_false _ Hlen) Gm Gn Gfn Hce Hal Hpos Hfree).
    unfold grant_model, grant_vmmaps, keff.
    split; (intros [He | Ho]; [left; exact He | right]); [split; [discriminate | exact Ho] | exact (proj2 Ho)].
  - cbn [negb] in Gfr.
    rewrite (mmap_fixed_rw_fresh_outcome _ _ _ _ _ _ _ mo o Go Ga (w_is0_false _ Hlen) Gm Gn Gfn Gfr Hce Hal Hpos Hfree).
    unfold grant_model, grant_vmmaps, keff. cbn [negb].
    split; (intros [He | [Hb Ho]]; [left; exact He | right]); split; auto.
Qed.

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
  intros na nr ms mo x8 o Hno. cbv zeta. intros Hlen H2 H3 H5 Hce Hal Hpos Hfree.
  destruct (nrgates na nr) as (Go & Ga & Gm & Gn & Gfn & Gfr & Gnn & Gnr & Gb).
  rewrite (syscall_spec_222 _ mo o) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_sys_input, in_arg1_sys_input', in_arg2_sys_input',
          in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input.
  rewrite H2, H3, H5.
  destruct na.
  - rewrite (mmap_noreplace_noaccess_fresh_outcome _ _ _ _ _ _ _ mo o Go Ga (w_is0_false _ Hlen) Gm Gn Gfn Gfr Gnn Hce Hal Hpos Hfree).
    unfold grant_model, grant_vmmaps, keff.
    split; (intros [He | Ho]; [left; exact He | right]); [split; [discriminate | exact Ho] | exact (proj2 Ho)].
  - cbn [negb] in Gnr.
    rewrite (mmap_noreplace_rw_fresh_outcome _ _ _ _ _ _ _ mo o Go Ga (w_is0_false _ Hlen) Gm Gn Gfn Gfr Gnn Gnr Hce Hal Hpos Hfree).
    unfold grant_model, grant_vmmaps, keff. cbn [negb].
    split; (intros [He | [Hb Ho]]; [left; exact He | right]); split; auto.
Qed.

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
  apply (sreach_node segs _ unit _ tt _ Hnode). intros [].
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
  intros nr ms mo x8 o Hno. cbv zeta. intros Hlen H2 H3 H5 Hce Hal Hpos Hrf Hmc.
  destruct (fgates false nr) as (Go & Ga & Gm & Gn & Gfn & Gfr & Gb). cbn [negb kprot] in *.
  rewrite (syscall_spec_222 _ mo o) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_sys_input, in_arg1_sys_input', in_arg2_sys_input',
          in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input.
  rewrite H2, H3, H5.
  rewrite (mmap_fixed_rw_commit_outcome _ _ _ _ _ _ _ mo o Go Ga (w_is0_false _ Hlen) Gm Gn Gfn Gfr Hce Hal Hpos Hrf Hmc).
  rewrite mmap_fixed_rw_commit_model. reflexivity.
Qed.

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
  apply (sreach_node segs _ unit _ tt _ Hnode). intros [].
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
    apply (sreach_node segs _ unit _ tt _ Hnode). intros [].
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

Lemma munmap_model_eqL : forall a n m, munmap_model a n m = munmap_modelL a n m.
Proof. reflexivity. Qed.

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
  { rewrite munmap_model_eqL. apply (eager_used_munmap_le a n mo HX HNA ltac:(rewrite HLm; exact HLnw) Hno_ov).
    apply map_has_In. exact Hhas. }
  set (msF' := advance_past_svc (apply_effect msF (munmap_eff msF))).
  assert (Emem : ms_mem msF' = unfill a n (ms_mem msF)).
  { unfold msF', munmap_eff. rewrite Hpr. cbn [ms_mem advance_past_svc]. apply apply_effect_mem_unmaps. }
  rewrite <- Hun in HRL.
  destruct (lzok_after_disjoint_op L S Zr msF mo msF' (munmap_model a n mo)
              (bv_unsigned a) (bv_unsigned a + bv_unsigned n) Hok ltac:(lia) ltac:(pose proof (word_unsigned_range n); lia)
              ltac:(lia) HRL) as (Hok' & Hhid & Hhs).
  - rewrite munmap_model_eqL, munmap_modelL_lazy. reflexivity.
  - intros p Hp. rewrite munmap_model_eqL, munmap_modelL_materialized in Hp. apply filter_In in Hp. tauto.
  - rewrite munmap_model_eqL, munmap_modelL_materialized. apply NoDup_filter. exact (li_nodup _ _ _ (lzok_inv Hok)).
  - rewrite munmap_model_eqL, munmap_modelL_vmmaps. reflexivity.
  - lia.
  - rewrite munmap_model_halted. exact (lzok_halted Hok).
  - rewrite munmap_model_eqL, munmap_modelL_vmmaps. cbn.
    apply (rsub_map_remove L (vm_maps (m_vmmaps mo)) a n Hno_ov (map_has_In _ _ _ Hhas) ltac:(lia) HRL (lzok_LM Hok)).
  - intros x Hx. rewrite Emem. apply unfill_out. lia.
  - assert (Hnode : node_ok segs (mkCfg msF mo) unit (fun _ => [])
                      (fun _ => mkCfg msF' (munmap_model a n mo))).
    { apply (node_family_noacc msF mo x8 unit (fun _ => munmap_eff msF)
               (fun _ => munmap_model a n mo) (fun _ => []) _ (lzok_halted Hok) Hsvc
               (fun o => Hspec0 o Hno Hargs)).
      - intros []. rewrite Hpr. reflexivity.
      - intros []. apply not_spurious_none. rewrite Hno'. apply injected_arm_none_215.
      - intros o. rewrite Hpr. intros ->. exists tt. reflexivity.
      - intros []. exact (lzok_halted Hok').
      - intros []. reflexivity. }
    apply (sreach_node segs _ unit _ tt _ Hnode). intros [].
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
  intros Hal Hlen Hnw2 H2 Hcna Hcm HX HNA Hno_ov HRL Hbud Hk.
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
                Hlenpos ltac:(unfold two_pow_64 in Hnw2; exact Hnw2) Hal Hcna Hcm) as Hspec.
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
    apply (sreach_node segs _ unit _ tt _ Hnode). intros [].
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
  apply (sreach_node segs _ unit _ tt _ Hnode). intros [].
  assert (Emem : ms_mem (apply_effect msF eff) = ms_mem msF).
  { unfold eff. rewrite brk_zeros_keep, brk_unmaps_keep. destruct msF; reflexivity. }
  assert (Hhs : hid_same L S msF (advance_past_svc (apply_effect msF eff))).
  { intros a Ha. cbn [ms_mem advance_past_svc]. rewrite Emem. reflexivity. }
  apply Hk.
  - eapply lzok_vm_frame; [exact Hok | reflexivity | exact (lzok_halted Hok) | exact Hhs].
  - rewrite (restrict_sysret L S). rewrite Emem. reflexivity.
  - exact Hhs.
Qed.

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
    apply (sreach_node segs _ unit _ tt _ Hnode). intros []. unfold E.
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
      replace (bv_unsigned (req - b)) with d in Hg; [exact Hg|].
      rewrite bv_sub_unsigned, Hureq. rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2^64). lia. }
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
    apply (sreach_node segs _ unit _ tt _ Hnode). intros []. unfold E.
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
