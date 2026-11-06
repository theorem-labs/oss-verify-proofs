(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  SimInv ExitSim CatSim CatExec PropExec SeqExec Hoare ShapeAlg SpinAlg Nodes FileSim AgentLib AgentNodes
  LibWritev AsanAcct AsanAcctShape LazyFrame CxNodesBase CxNodesFs CxNodesWr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxAcctShape CxNodesLibE.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lazy_all_hidden (H : word -> bool) (m : Model) : Prop :=
  forall w, page_in_ranges (page_base w) (m_vm_lazy m) = true -> H w = true.

Lemma lazy_all_hidden_cover : forall H m,
  lazy_all_hidden H m -> lazy_cover H (m_vm_lazy m) [].
Proof.
  intros H m HL w Hp Hw. rewrite (HL w Hp) in Hw. discriminate.
Qed.

(* [comment removed for export] *)
Lemma lazy_all_hidden_same_lazy : forall H m m',
  m_vm_lazy m' = m_vm_lazy m -> lazy_all_hidden H m -> lazy_all_hidden H m'.
Proof. intros H m m' E HL w. rewrite E. apply HL. Qed.

(* [comment removed for export] *)
Lemma lazy_all_hidden_mkH : forall L m,
  incl (m_vm_lazy m) L -> lazy_all_hidden (mkH L []) m.
Proof.
  intros L m Hincl w Hp. unfold mkH.
  rewrite (page_in_ranges_incl _ _ _ Hincl Hp). reflexivity.
Qed.

Lemma materialize_nolazy : forall H m ranges,
  lazy_all_hidden H m -> ranges_avoid H ranges ->
  materialize_model_accesses m ranges = Some m.
Proof.
  intros H m ranges HL Hav.
  pose proof (new_pages_props H [] (m_vm_lazy m) (m_vm_materialized m) ranges
                (lazy_all_hidden_cover H m HL) Hav) as (_ & _ & _ & _ & Hallowed).
  assert (Hnil : newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) ranges = []).
  { destruct (newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) ranges) as [|p l] eqn:E;
      [reflexivity|].
    exfalso. specialize (Hallowed p (or_introl eq_refl)). cbn in Hallowed. discriminate. }
  unfold materialize_model_accesses, materialize_accesses. rewrite Hnil.
  rewrite with_vm_backing_id. reflexivity.
Qed.

(* [comment removed for export] *)
Definition lazyH (m : Model) : word -> bool := mkH (m_vm_lazy m) [].

Lemma lazy_all_hidden_lazyH : forall m, lazy_all_hidden (lazyH m) m.
Proof. intros m. apply lazy_all_hidden_mkH. intros r Hr. exact Hr. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mclean (H : word -> bool) (m : word -> option byte) : Prop :=
  forall a, H a = true -> m a = None.

Lemma mclean_mrestrict : forall H m, mclean H (mrestrict H m).
Proof. intros H m a Ha. unfold mrestrict. rewrite Ha. reflexivity. Qed.

Lemma mrestrict_clean_id : forall H m, mclean H m -> mrestrict H m = m.
Proof.
  intros H m Hc. apply functional_extensionality. intro a. unfold mrestrict.
  destruct (H a) eqn:E; [symmetry; exact (Hc a E) | reflexivity].
Qed.

Lemma hclean_mkst : forall H regs pc m rom,
  hclean H (mkst regs pc m rom) <-> mclean H m.
Proof. intros. unfold hclean, mclean. cbn. tauto. Qed.

Lemma munrestrict_visible : forall (H : word -> bool) F m a,
  H a = false -> munrestrict H F m a = m a.
Proof. intros H F m a Ha. unfold munrestrict. rewrite Ha. reflexivity. Qed.

Lemma munrestrict_hidden : forall (H : word -> bool) F m a,
  H a = true -> munrestrict H F m a = F a.
Proof. intros H F m a Ha. unfold munrestrict. rewrite Ha. reflexivity. Qed.

Lemma munrestrict_munrestrict_mem : forall (H : word -> bool) F G m,
  munrestrict H (munrestrict H F G) m = munrestrict H F m.
Proof.
  intros H F G m. apply functional_extensionality. intro x. unfold munrestrict.
  destruct (H x); reflexivity.
Qed.

Lemma restrict_mkst_munrestrict : forall H F regs pc m rom,
  mclean H m ->
  restrict H (mkst regs pc (munrestrict H F m) rom) = mkst regs pc m rom.
Proof.
  intros H F regs pc m rom Hc. rewrite restrict_mkst, mrestrict_munrestrict, (mrestrict_clean_id H m Hc).
  reflexivity.
Qed.

Lemma unrestrict_mkst : forall H F regs pc m rom,
  unrestrict H F (mkst regs pc m rom) = mkst regs pc (munrestrict H F m) rom.
Proof. reflexivity. Qed.

Lemma unrestrict_epend : forall H F regs pc m rom x8,
  unrestrict H F (epend regs pc m rom x8) = epend regs pc (munrestrict H F m) rom x8.
Proof. reflexivity. Qed.

Lemma restrict_epend : forall H regs pc m rom x8,
  restrict H (epend regs pc m rom x8) = epend regs pc (mrestrict H m) rom x8.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rdn_munrestrict_eq : forall segs (H : word -> bool) F n m a,
  range_avoids H a n ->
  rdn segs (munrestrict H F m) a n = rdn segs m a n.
Proof.
  intros segs H F n. induction n as [|n IH]; intros m a Hav; [reflexivity|].
  cbn [rdn]. unfold munrestrict at 1. rewrite (range_avoids_hd H a n Hav).
  rewrite (IH m (a + 1) (range_avoids_tl H a n Hav)). reflexivity.
Qed.

Lemma store_ok_munrestrict_eq : forall segs (H : word -> bool) F n m a,
  range_avoids H a n ->
  store_ok segs (munrestrict H F m) a n = store_ok segs m a n.
Proof.
  intros segs H F n. induction n as [|n IH]; intros m a Hav; [reflexivity|].
  cbn [store_ok].
  replace (wview segs (munrestrict H F m) a) with (wview segs m a)
    by (unfold wview, munrestrict; rewrite (range_avoids_hd H a n Hav); reflexivity).
  destruct (wview segs m a); [|reflexivity].
  exact (IH m (a + 1) (range_avoids_tl H a n Hav)).
Qed.

(* [comment removed for export] *)
Lemma rdn_clean_avoids : forall segs H m a n bs,
  H_off_segments segs H -> mclean H m ->
  rdn segs m a n = Some bs -> range_avoids H a n.
Proof.
  intros segs H m a n bs HH Hc Hr.
  rewrite <- (mrestrict_clean_id H m Hc) in Hr. rewrite <- ov_rdn in Hr.
  exact (proj2 (ov_read_bytes_restrict segs H HH n m a bs Hr)).
Qed.

Lemma store_ok_clean_avoids : forall segs H m a n,
  H_off_segments segs H -> mclean H m ->
  store_ok segs m a n = true -> range_avoids H a n.
Proof.
  intros segs H m a n HH Hc Hs.
  rewrite <- (mrestrict_clean_id H m Hc) in Hs.
  exact (proj2 (store_ok_restrict segs H HH n m a Hs)).
Qed.

(* [comment removed for export] *)
Lemma range_avoids_mono : forall H a n k,
  range_avoids H a n -> (k <= n)%nat -> range_avoids H a k.
Proof. intros H a n k Hr Hk i Hi. apply Hr. lia. Qed.

Lemma range_avoids_nil : forall H a, range_avoids H a 0.
Proof. intros H a k Hk. lia. Qed.

Lemma woff_Z : forall (z : Z) k,
  woff (Z_to_bv 64 z) k = Z_to_bv 64 (z + Z.of_nat k).
Proof.
  intros z k. unfold woff. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma woff_woff : forall a i k, woff (woff a i) k = woff a (i + k).
Proof.
  intros a i k. unfold woff at 2. rewrite woff_Z. unfold woff. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma range_avoids_split : forall H a n1 n2,
  range_avoids H a (n1 + n2) ->
  range_avoids H a n1 /\ range_avoids H (Z_to_bv 64 (bv_unsigned a + Z.of_nat n1)) n2.
Proof.
  intros H a n1 n2 Hr. split.
  - intros k Hk. apply Hr. lia.
  - intros k Hk. replace (Z_to_bv 64 (bv_unsigned a + Z.of_nat n1)) with (woff a n1) by reflexivity.
    rewrite woff_woff. apply Hr. lia.
Qed.

Lemma range_avoids_join : forall H a n1 n2,
  range_avoids H a n1 ->
  range_avoids H (Z_to_bv 64 (bv_unsigned a + Z.of_nat n1)) n2 ->
  range_avoids H a (n1 + n2).
Proof.
  intros H a n1 n2 H1 H2 k Hk.
  destruct (Nat.lt_ge_cases k n1) as [Hlt|Hge].
  - apply H1. exact Hlt.
  - replace k with (n1 + (k - n1))%nat by lia. rewrite <- woff_woff.
    change (woff a n1) with (Z_to_bv 64 (bv_unsigned a + Z.of_nat n1)). apply H2. lia.
Qed.

(* [comment removed for export] *)
Lemma range_avoids_sub : forall H (a : word) n (b : Z) k,
  range_avoids H a n ->
  (bv_unsigned a <= b)%Z -> (b + Z.of_nat k <= bv_unsigned a + Z.of_nat n)%Z ->
  range_avoids H (Z_to_bv 64 b) k.
Proof.
  intros H a n b k Hr Hlo Hhi i Hi.
  replace (Z_to_bv 64 b) with (woff a (Z.to_nat (b - bv_unsigned a))).
  2:{ unfold woff. f_equal. lia. }
  rewrite woff_woff. apply Hr. lia.
Qed.

(* [comment removed for export] *)
Lemma range_avoids_by_addr : forall (H : word -> bool) (a : Z) n,
  (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall w, H w = true -> ~ (a <= bv_unsigned w < a + Z.of_nat n)%Z) ->
  range_avoids H (Z_to_bv 64 a) n.
Proof.
  intros H a n Ha Hn Hout k Hk.
  destruct (H (woff (Z_to_bv 64 a) k)) eqn:E; [|reflexivity]. exfalso.
  apply (Hout _ E). rewrite woff_Z, Z_to_bv_unsigned.
  rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64)%Z; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma range_avoids_mkH_below : forall L A top (a : Z) n,
  ranges_from_b L top = true ->
  (0 <= a)%Z -> (a + Z.of_nat n <= top)%Z -> (top <= 2 ^ 64)%Z ->
  range_avoids (mkH L A) (Z_to_bv 64 a) n.
Proof.
  intros L A top a n HL Ha Hn Htop. apply range_avoids_by_addr; [lia | lia |].
  intros w Hw. pose proof (mkH_above L A top w HL Hw). lia.
Qed.

(* [comment removed for export] *)
Lemma find_segment_sub1 : forall segs lo n x,
  (lo <= x)%Z -> (x + 1 <= lo + n)%Z ->
  find_segment segs lo n <> None -> find_segment segs x 1 <> None.
Proof.
  induction segs as [|s l IH]; intros lo n x H1 H2 Hf; [exact Hf|].
  cbn [find_segment] in *.
  destruct (Z.leb (Z.of_N (seg_base s)) lo && Z.leb (lo + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E.
  - apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z
      with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
    discriminate.
  - destruct (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z;
      [discriminate | exact (IH lo n x H1 H2 Hf)].
Qed.

Definition window_in_seg_b (segs : list Segment) (lo hi : Z) : bool :=
  match find_segment segs lo (hi - lo) with Some _ => true | None => false end.

(* [comment removed for export] *)
Lemma range_avoids_in_window : forall segs H lo hi (a : Z) n,
  H_off_segments segs H ->
  window_in_seg_b segs lo hi = true -> (hi <= 2 ^ 64)%Z ->
  (lo <= a)%Z -> (a + Z.of_nat n <= hi)%Z ->
  range_avoids H (Z_to_bv 64 a) n.
Proof.
  intros segs H lo hi a n HH Hw Hhi Hlo Hn k Hk.
  destruct (H (woff (Z_to_bv 64 a) k)) eqn:E; [|reflexivity]. exfalso.
  pose proof (HH _ E) as Hnone. rewrite woff_Z, Z_to_bv_unsigned in Hnone.
  unfold window_in_seg_b in Hw. destruct (find_segment segs lo (hi - lo)) as [sg|] eqn:Ef; [|discriminate].
  assert (Hseg0 : find_segment segs lo (hi - lo) <> None) by (rewrite Ef; discriminate).
  assert (Hlo0 : (0 <= lo)%Z).
  { clear -Ef. revert Ef. generalize sg. induction segs as [|s l IH]; cbn [find_segment]; intros sg0 Ef; [discriminate|].
    destruct (Z.leb (Z.of_N (seg_base s)) lo && Z.leb (lo + (hi - lo)) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E2.
    - apply andb_true_iff in E2 as [E1 _]. apply Z.leb_le in E1. lia.
    - exact (IH _ Ef). }
  rewrite bv_wrap_small in Hnone by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  apply (find_segment_sub1 segs lo (hi - lo) (a + Z.of_nat k)); [lia | lia | exact Hseg0 | exact Hnone].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section NoLazy.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Theorem mi_account_step_nolazy : forall ms msr' model,
  lazy_all_hidden H model ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  mi_account_step segs ms model = MachineOk (unrestrict H (ms_mem ms) msr', model)
  /\ hclean H msr'.
Proof.
  intros ms msr' model HL Hs.
  destruct (step_restrict_sound segs H HH Hwx ms msr' Hs) as (rep & Hsa & Hv & Hrs & Hcl & _).
  unfold mi_account_step. rewrite Hsa, (materialize_nolazy H model _ HL Hrs), Hv.
  split; [reflexivity | exact Hcl].
Qed.

Theorem node_instr_nolazy : forall ms msr' model,
  lazy_all_hidden H model -> m_halted model = None -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  hclean H msr'
  /\ node_ok segs (mkCfg ms model) unit (fun _ => [])
             (fun _ => mkCfg (unrestrict H (ms_mem ms) msr') model).
Proof.
  intros ms msr' model HL Hh Hsvc Hs.
  destruct (mi_account_step_nolazy ms msr' model HL Hs) as [Hacc Hcl].
  split; [exact Hcl|]. split.
  - intros []. apply sstep_instr; [exact Hh | exact Hsvc | exact Hacc].
  - intros e st Hss. exists tt. exact (sstep_instr_det segs ms model _ _ e st Hsvc Hacc Hss).
Qed.

Theorem rz_step_nolazy : forall ms msr' model T,
  lazy_all_hidden H model -> m_halted model = None -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  realizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms msr' model T HL Hh Hsvc Hs Hk.
  destruct (node_instr_nolazy ms msr' model HL Hh Hsvc Hs) as [_ Hnode].
  exact (rz_silent1 segs _ _ T Hnode Hk).
Qed.

Lemma rz_msteps_nolazy_ind : forall msr0 msr',
  msteps segs msr0 msr' ->
  forall ms model T,
  msr0 = restrict H ms ->
  lazy_all_hidden H model -> m_halted model = None ->
  realizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros msr0 msr' Hms.
  induction Hms as [msr | msr msr1 msr2 Hsvc Hstep Hrest IH]; intros ms model T -> HL Hh Hk.
  - rewrite unrestrict_restrict in Hk. exact Hk.
  - rewrite restrict_svc_pending in Hsvc.
    destruct (node_instr_nolazy ms msr1 model HL Hh Hsvc Hstep) as [Hcl1 Hnode].
    apply (rz_silent1 segs _ _ T Hnode).
    apply (IH (unrestrict H (ms_mem ms) msr1) model T).
    + symmetry. apply restrict_unrestrict_clean. exact Hcl1.
    + exact HL.
    + exact Hh.
    + rewrite unrestrict_mem, unrestrict_munrestrict. exact Hk.
Qed.

(* [comment removed for export] *)
Theorem rz_msteps_nolazy : forall ms msr' model T,
  lazy_all_hidden H model -> m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  realizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms msr' model T HL Hh Hms Hk.
  exact (rz_msteps_nolazy_ind _ _ Hms ms model T eq_refl HL Hh Hk).
Qed.

(* [comment removed for export] *)
Theorem rz_msteps_R : forall F regs pc mr regs' pc' mr' rom model T,
  lazy_all_hidden H model -> m_halted model = None ->
  mclean H mr ->
  msteps segs (mkst regs pc mr rom) (mkst regs' pc' mr' rom) ->
  (mclean H mr' -> realizes segs (mkCfg (mkst regs' pc' (munrestrict H F mr') rom) model) T) ->
  realizes segs (mkCfg (mkst regs pc (munrestrict H F mr) rom) model) T.
Proof.
  intros F regs pc mr regs' pc' mr' rom model T HL Hh Hc Hms Hk.
  apply (rz_msteps_nolazy (mkst regs pc (munrestrict H F mr) rom) (mkst regs' pc' mr' rom) model T HL Hh).
  - rewrite (restrict_mkst_munrestrict H F regs pc mr rom Hc). exact Hms.
  - cbn [ms_mem mkst]. rewrite unrestrict_mkst, munrestrict_munrestrict_mem. apply Hk.
    apply (hclean_mkst H regs' pc' mr' rom).
    apply (msteps_hclean segs H HH Hwx _ _ Hms). apply (hclean_mkst H regs pc mr rom). exact Hc.
Qed.

(* [comment removed for export] *)
Theorem rz_sys_R : forall regs pc M rom model w T,
  lazy_all_hidden H model -> m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  realizes segs (mkCfg (epend regs pc M rom (getr regs 17)) model) T ->
  realizes segs (mkCfg (mkst regs pc M rom) model) T.
Proof.
  intros regs pc M rom model w T HL Hh HF HE Hk.
  apply (rz_step_nolazy (mkst regs pc M rom) (epend regs pc (mrestrict H M) rom (getr regs 17)) model T HL Hh eq_refl).
  - rewrite restrict_mkst. apply (step_ecall_epend segs regs pc (mrestrict H M) rom w HF HE).
  - cbn [ms_mem mkst]. rewrite unrestrict_epend, munrestrict_mrestrict. exact Hk.
Qed.

(* [comment removed for export] *)
Theorem rz_exit_at_R : forall regs (pc : word) M rom model w code,
  lazy_all_hidden H model -> m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  realizes segs (mkCfg (mkst regs pc M rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc M rom model w code HL Hh HF HE H17 H10.
  eapply rz_sys_R; [exact HL | exact Hh | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc M rom (getr regs 17)).
  eapply rz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H7|H7]; [right|left]; rewrite H7; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstep_of_check_mat : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  m_halted m' = None ->
  materialize_model_accesses m' (syscall_effect_accesses eff) = Some m' ->
  sstep segs (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hh' Hmat.
  apply (sstep_syscall segs ms model x8 eff m' m' evs Hh Hsvc).
  - apply check_syscall_ok_iff. exact Hc.
  - exact Hh'.
  - exact Hmat.
Qed.

Lemma node_chk_ev_mat : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, materialize_model_accesses (ms' i) (syscall_effect_accesses (effs i)) = Some (ms' i)) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hmat. split.
  - intros i. apply (sstep_of_check_mat ms model x8); auto.
  - intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hm & ->) | [(Hh2 & -> & Hm & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (Hmat i) in Hm. injection Hm as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite (Hmat i) in Hm. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite Hh' in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

Lemma rz_ret_only_copyins_silent_mat : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' []) ->
  m_halted m' = None ->
  materialize_model_accesses m' reads = Some m' ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hmat Hc.
  eapply rz_silent1; [|exact Hc].
  rewrite <- (apply_effect_copyins_no_write ms r reads).
  apply (node_chk_ev_mat ms model x8 unit (fun _ => with_copyins reads (mkEffect r [] []))
           (fun _ => m') (fun _ => []) Hh Hsvc).
  - intros []. rewrite Hchk. apply check_ret_only_copyins_ok_iff. auto.
  - intros eff m'' ev Hck. rewrite Hchk in Hck. apply check_ret_only_copyins_ok_iff in Hck as (-> & -> & ->).
    exists tt. auto.
  - intros eff. rewrite Hchk. apply check_ret_only_copyins_no_unmodeled.
  - intros []. exact Hh'.
  - intros []. unfold syscall_effect_accesses, with_copyins. cbn [eff_copyins eff_writes write_accesses].
    rewrite app_nil_r. exact Hmat.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma copy_iovecs_accesses_of_array : forall ms iovs iov,
  ms_rom ms = seg_rom segs ->
  iov_array segs (ms_mem ms) iov iovs ->
  copy_iovecs_accesses (ms_read_byte ms) iov (length iovs)
  = map (fun i => (Z_to_bv 64 (bv_unsigned iov + 16 * Z.of_nat i), 16%nat)) (seq 0 (length iovs)).
Proof.
  intros ms iovs. induction iovs as [|[b n] r IH]; intros iov Hrom Ha; [reflexivity|].
  destruct Ha as (Hb & Hn & Hlt & Hr).
  cbn [length copy_iovecs_accesses seq map]. unfold read_iovec_entry.
  rewrite (read_u64_rdn segs ms iov b Hrom Hb).
  rewrite bv_add_Zform. change (bv_unsigned (8 : word)) with 8%Z.
  rewrite (read_u64_rdn segs ms _ n Hrom Hn).
  rewrite (proj2 (Z.leb_gt _ _) Hlt).
  rewrite bv_add_Zform. change (bv_unsigned (16 : word)) with 16%Z.
  rewrite (IH _ Hrom Hr). f_equal.
  - f_equal. rewrite Z.mul_0_r, Z.add_0_r. symmetry. apply u64_roundtrip'.
  - rewrite <- seq_shift, map_map. apply map_ext. intros i. f_equal.
    apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma iov_prefix_accesses_avoid : forall iovs left,
  (forall b n, In (b, n) iovs -> range_avoids H b (word_to_nat n)) ->
  ranges_avoid H (iov_prefix_accesses iovs left).
Proof.
  induction iovs as [|[b n] r IH]; intros left Hall.
  - destruct left; cbn; apply ranges_avoid_nil.
  - destruct left as [|l'].
    + cbn. apply ranges_avoid_nil.
    + cbn [iov_prefix_accesses].
      set (k := word_to_nat_bounded n (S l')).
      assert (Hk : (k <= word_to_nat n)%nat) by (unfold k; rewrite word_to_nat_bounded_eq_min; lia).
      assert (Hr : ranges_avoid H (iov_prefix_accesses r (S l')) /\ forall x, ranges_avoid H (iov_prefix_accesses r x)).
      { split; [|intros x]; apply IH; intros b' n' Hin; apply Hall; right; exact Hin. }
      destruct (Nat.eqb k 0).
      * apply (proj2 Hr).
      * apply ranges_avoid_cons; [| apply (proj2 Hr)].
        apply (range_avoids_mono H b (word_to_nat n)); [apply Hall; left; reflexivity | exact Hk].
Qed.

Lemma range_avoids_join_Z : forall (a : word) (i : Z) n1 n2,
  (0 <= i)%Z ->
  range_avoids H (Z_to_bv 64 (bv_unsigned a + i)) n1 ->
  range_avoids H (Z_to_bv 64 (bv_unsigned a + (i + Z.of_nat n1))) n2 ->
  range_avoids H (Z_to_bv 64 (bv_unsigned a + i)) (n1 + n2).
Proof.
  intros a i n1 n2 Hi H1 H2 k Hk.
  destruct (Nat.lt_ge_cases k n1) as [Hlt|Hge]; [apply H1; exact Hlt|].
  rewrite woff_Z. replace (bv_unsigned a + i + Z.of_nat k)%Z
    with (bv_unsigned a + (i + Z.of_nat n1) + Z.of_nat (k - n1))%Z by lia.
  rewrite <- woff_Z. apply H2. lia.
Qed.

Lemma iov1_avoids : forall mr (iov : word) x0 x1,
  mclean H mr ->
  rdn segs mr iov 8%nat = Some x0 ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some x1 ->
  range_avoids H iov (16 * 1).
Proof.
  intros mr iov x0 x1 Hc R0 R1.
  rewrite <- (u64_roundtrip' iov). rewrite <- (Z.add_0_r (bv_unsigned iov)).
  apply (range_avoids_join_Z iov 0 8 8); [lia | |].
  - rewrite Z.add_0_r, u64_roundtrip'. exact (rdn_clean_avoids segs H mr _ _ _ HH Hc R0).
  - exact (rdn_clean_avoids segs H mr _ _ _ HH Hc R1).
Qed.

Lemma iov2_avoids : forall mr (iov : word) x0 x1 x2 x3,
  mclean H mr ->
  rdn segs mr iov 8%nat = Some x0 ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some x1 ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some x2 ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some x3 ->
  range_avoids H iov (16 * 2).
Proof.
  intros mr iov x0 x1 x2 x3 Hc R0 R1 R2 R3.
  rewrite <- (u64_roundtrip' iov). rewrite <- (Z.add_0_r (bv_unsigned iov)).
  apply (range_avoids_join_Z iov 0 8 24); [lia | |].
  { rewrite Z.add_0_r, u64_roundtrip'. exact (rdn_clean_avoids segs H mr _ _ _ HH Hc R0). }
  apply (range_avoids_join_Z iov 8 8 16); [lia | exact (rdn_clean_avoids segs H mr _ _ _ HH Hc R1) |].
  apply (range_avoids_join_Z iov (8 + Z.of_nat 8) 8 8); [lia | exact (rdn_clean_avoids segs H mr _ _ _ HH Hc R2) |].
  exact (rdn_clean_avoids segs H mr _ _ _ HH Hc R3).
Qed.

Lemma rdn_R : forall F mr a n bs,
  mclean H mr -> rdn segs mr a n = Some bs -> rdn segs (munrestrict H F mr) a n = Some bs.
Proof.
  intros F mr a n bs Hc Hr. rewrite (rdn_munrestrict_eq segs H F n mr a); [exact Hr|].
  exact (rdn_clean_avoids segs H mr a n bs HH Hc Hr).
Qed.

End NoLazy.

Section NoLazyS.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Theorem srz_step_nolazy : forall ms msr' model T,
  lazy_all_hidden H model -> m_halted model = None -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  crz segs (mkCfg (unrestrict H (ms_mem ms) msr') model) T ->
  crz segs (mkCfg ms model) T.
Proof.
  intros ms msr' model T HL Hh Hsvc Hs Hk.
  destruct (node_instr_nolazy segs H HH Hwx ms msr' model HL Hh Hsvc Hs) as [_ Hnode].
  exact (crz_silent1 segs _ _ T Hnode Hk).
Qed.

Lemma srz_msteps_nolazy_ind : forall msr0 msr',
  msteps segs msr0 msr' ->
  forall ms model T,
  msr0 = restrict H ms ->
  lazy_all_hidden H model -> m_halted model = None ->
  crz segs (mkCfg (unrestrict H (ms_mem ms) msr') model) T ->
  crz segs (mkCfg ms model) T.
Proof.
  intros msr0 msr' Hms.
  induction Hms as [msr | msr msr1 msr2 Hsvc Hstep Hrest IH]; intros ms model T -> HL Hh Hk.
  - rewrite unrestrict_restrict in Hk. exact Hk.
  - rewrite restrict_svc_pending in Hsvc.
    destruct (node_instr_nolazy segs H HH Hwx ms msr1 model HL Hh Hsvc Hstep) as [Hcl1 Hnode].
    apply (crz_silent1 segs _ _ T Hnode).
    apply (IH (unrestrict H (ms_mem ms) msr1) model T).
    + symmetry. apply restrict_unrestrict_clean. exact Hcl1.
    + exact HL.
    + exact Hh.
    + rewrite unrestrict_mem, unrestrict_munrestrict. exact Hk.
Qed.

(* [comment removed for export] *)
Theorem srz_msteps_nolazy : forall ms msr' model T,
  lazy_all_hidden H model -> m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  crz segs (mkCfg (unrestrict H (ms_mem ms) msr') model) T ->
  crz segs (mkCfg ms model) T.
Proof.
  intros ms msr' model T HL Hh Hms Hk.
  exact (srz_msteps_nolazy_ind _ _ Hms ms model T eq_refl HL Hh Hk).
Qed.

(* [comment removed for export] *)
Theorem srz_msteps_R : forall F regs pc mr regs' pc' mr' rom model T,
  lazy_all_hidden H model -> m_halted model = None ->
  mclean H mr ->
  msteps segs (mkst regs pc mr rom) (mkst regs' pc' mr' rom) ->
  (mclean H mr' -> crz segs (mkCfg (mkst regs' pc' (munrestrict H F mr') rom) model) T) ->
  crz segs (mkCfg (mkst regs pc (munrestrict H F mr) rom) model) T.
Proof.
  intros F regs pc mr regs' pc' mr' rom model T HL Hh Hc Hms Hk.
  apply (srz_msteps_nolazy (mkst regs pc (munrestrict H F mr) rom) (mkst regs' pc' mr' rom) model T HL Hh).
  - rewrite (restrict_mkst_munrestrict H F regs pc mr rom Hc). exact Hms.
  - cbn [ms_mem mkst]. rewrite unrestrict_mkst, munrestrict_munrestrict_mem. apply Hk.
    apply (hclean_mkst H regs' pc' mr' rom).
    apply (msteps_hclean segs H HH Hwx _ _ Hms). apply (hclean_mkst H regs pc mr rom). exact Hc.
Qed.

(* [comment removed for export] *)
Theorem srz_sys_R : forall regs pc M rom model w T,
  lazy_all_hidden H model -> m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  crz segs (mkCfg (epend regs pc M rom (getr regs 17)) model) T ->
  crz segs (mkCfg (mkst regs pc M rom) model) T.
Proof.
  intros regs pc M rom model w T HL Hh HF HE Hk.
  apply (srz_step_nolazy (mkst regs pc M rom) (epend regs pc (mrestrict H M) rom (getr regs 17)) model T HL Hh eq_refl).
  - rewrite restrict_mkst. apply (step_ecall_epend segs regs pc (mrestrict H M) rom w HF HE).
  - cbn [ms_mem mkst]. rewrite unrestrict_epend, munrestrict_mrestrict. exact Hk.
Qed.

(* [comment removed for export] *)
Theorem srz_exit_at_R : forall regs (pc : word) M rom model w code,
  lazy_all_hidden H model -> m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  crz segs (mkCfg (mkst regs pc M rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc M rom model w code HL Hh HF HE H17 H10.
  eapply srz_sys_R; [exact HL | exact Hh | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc M rom (getr regs 17)).
  eapply crz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H7|H7]; [right|left]; rewrite H7; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mat_id_writev2 : forall F mr model (iov b1 n1 b2 n2 : word) bs1 bs2,
  lazy_all_hidden H model -> mclean H mr ->
  rdn segs mr iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mr b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mr b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  forall k, mat_id model (import_iovecs_accesses (mrb segs (munrestrict H F mr)) iov (Z_to_bv 64 2)
                          ++ iov_prefix_accesses [(b1, n1); (b2, n2)] k).
Proof.
  intros F mr model iov b1 n1 b2 n2 bs1 bs2 HL Hc Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiov k.
  apply (materialize_nolazy H model _ HL). apply ranges_avoid_app.
  - intros a n Hin. pose proof (u64_range iov). unfold TASK_SIZE in Hiov.
    destruct (import_iovecs_accesses_sub (mrb segs (munrestrict H F mr)) iov (Z_to_bv 64 2)
                ltac:(change (bv_unsigned (Z_to_bv 64 2)) with 2%Z; lia) (a, n) Hin) as [H1 H2].
    cbn [fst snd] in H1, H2. change (bv_unsigned (Z_to_bv 64 2)) with 2%Z in H2.
    pose proof (iov2_avoids segs H HH mr iov _ _ _ _ Hc Rb1 Rn1 Rb2 Rn2) as Hav.
    apply (range_avoids_sub H iov (16 * 2) (bv_unsigned a) n) in Hav; [| lia | cbn; lia].
    rewrite u64_roundtrip' in Hav. exact Hav.
  - apply (iov_prefix_accesses_avoid H). intros b n [E|[E|[]]]; injection E as <- <-;
      [exact (rdn_clean_avoids segs H mr _ _ _ HH Hc Rs1) | exact (rdn_clean_avoids segs H mr _ _ _ HH Hc Rs2)].
Qed.

Lemma mat_id_writev1 : forall F mr model (iov b1 n1 : word) bs1,
  lazy_all_hidden H model -> mclean H mr ->
  rdn segs mr iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mr b1 (word_to_nat n1) = Some bs1 ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  forall k, mat_id model (import_iovecs_accesses (mrb segs (munrestrict H F mr)) iov (Z_to_bv 64 1)
                          ++ iov_prefix_accesses [(b1, n1)] k).
Proof.
  intros F mr model iov b1 n1 bs1 HL Hc Rb1 Rn1 Rs1 Hiov k.
  apply (materialize_nolazy H model _ HL). apply ranges_avoid_app.
  - intros a n Hin. pose proof (u64_range iov). unfold TASK_SIZE in Hiov.
    destruct (import_iovecs_accesses_sub (mrb segs (munrestrict H F mr)) iov (Z_to_bv 64 1)
                ltac:(change (bv_unsigned (Z_to_bv 64 1)) with 1%Z; lia) (a, n) Hin) as [H1 H2].
    cbn [fst snd] in H1, H2. change (bv_unsigned (Z_to_bv 64 1)) with 1%Z in H2.
    pose proof (iov1_avoids segs H HH mr iov _ _ Hc Rb1 Rn1) as Hav.
    apply (range_avoids_sub H iov (16 * 1) (bv_unsigned a) n) in Hav; [| lia | cbn; lia].
    rewrite u64_roundtrip' in Hav. exact Hav.
  - apply (iov_prefix_accesses_avoid H). intros b n [E|[]]; injection E as <- <-.
    exact (rdn_clean_avoids segs H mr _ _ _ HH Hc Rs1).
Qed.

Lemma srz_writev2_R : forall F regs (pc : word) mr model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lazy_all_hidden H model -> m_halted model = None -> mclean H mr ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mr iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mr b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mr b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) (munrestrict H F mr) (seg_rom segs)) model)
               (T k)) ->
  crz segs (mkCfg (mkst regs pc (munrestrict H F mr) (seg_rom segs)) model)
    (t_alt (fun i : wr_index (bs1 ++ bs2) =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (bs1 ++ bs2))) (T (proj1_sig i)))).
Proof.
  intros F regs pc mr model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE HL Hh Hc Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiov Hb1 Hb2 Ht1 Ht30 Hk.
  eapply (srz_writev2_mi segs regs pc (munrestrict H F mr) model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE Hh Hfd Hfdr H17 H10 H11 H12);
    try (apply (rdn_R segs H HH F mr); assumption); try assumption.
  apply (mat_id_writev2 F mr model iov b1 n1 b2 n2 bs1 bs2); assumption.
Qed.

Lemma srz_writev1_R : forall F regs (pc : word) mr model w (fd : Z) (iov b1 n1 : word) bs1 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lazy_all_hidden H model -> m_halted model = None -> mclean H mr ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mr iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mr b1 (word_to_nat n1) = Some bs1 ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) (munrestrict H F mr) (seg_rom segs)) model)
               (T k)) ->
  crz segs (mkCfg (mkst regs pc (munrestrict H F mr) (seg_rom segs)) model)
    (t_alt (fun i : wr_index bs1 =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs1)) (T (proj1_sig i)))).
Proof.
  intros F regs pc mr model w fd iov b1 n1 bs1 T HF HE HL Hh Hc Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiov Hb1 Ht1 Ht30 Hk.
  eapply (srz_writev1_mi segs regs pc (munrestrict H F mr) model w fd iov b1 n1 bs1 T HF HE Hh Hfd Hfdr H17 H10 H11 H12);
    try (apply (rdn_R segs H HH F mr); assumption); try assumption.
  apply (mat_id_writev1 F mr model iov b1 n1 bs1); assumption.
Qed.

Lemma srz_writev2_wall_R : forall F regs (pc : word) mr model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lazy_all_hidden H model -> m_halted model = None -> mclean H mr ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mr iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mr b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mr b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) (munrestrict H F mr) (seg_rom segs)) model)
               (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)) ->
  crz segs (mkCfg (mkst regs pc (munrestrict H F mr) (seg_rom segs)) model)
            (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).
Proof.
  intros F regs pc mr model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE HL Hh Hc Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiov Hb1 Hb2 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs mr _ _ _ Rs1) as L1. pose proof (rdn_length segs mr _ _ _ Rs2) as L2.
  pose proof (u64_range n1). pose proof (u64_range n2).
  apply crz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
  eapply (srz_writev2_R F regs pc mr model w fd iov b1 n1 b2 n2 bs1 bs2
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.

Lemma srz_writev1_wall_R : forall F regs (pc : word) mr model w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lazy_all_hidden H model -> m_halted model = None -> mclean H mr ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mr iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mr b1 (word_to_nat n1) = Some bs1 ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) (munrestrict H F mr) (seg_rom segs)) model)
               (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
  crz segs (mkCfg (mkst regs pc (munrestrict H F mr) (seg_rom segs)) model)
            (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).
Proof.
  intros F regs pc mr model w fd iov b1 n1 bs1 K HF HE HL Hh Hc Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiov Hb1 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs mr _ _ _ Rs1) as L1. pose proof (u64_range n1).
  apply crz_wall; [unfold word_to_nat in L1; lia | exact HK |].
  eapply (srz_writev1_R F regs pc mr model w fd iov b1 n1 bs1
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.

Lemma srz_writev1_zero_R : forall F regs (pc : word) mr model w (fd : Z) (iov b1 : word) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lazy_all_hidden H model -> m_halted model = None -> mclean H mr ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mr iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 <= TASK_SIZE)%Z ->
  crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (munrestrict H F mr) (seg_rom segs)) model) K ->
  crz segs (mkCfg (mkst regs pc (munrestrict H F mr) (seg_rom segs)) model) K.
Proof.
  intros F regs pc mr model w fd iov b1 K HF HE HL Hh Hc Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiov Hb1 Hk.
  eapply (srz_writev1_zero_mi segs regs pc (munrestrict H F mr) model w fd iov b1 K HF HE Hh Hfd Hfdr H17 H10 H11 H12);
    try (apply (rdn_R segs H HH F mr); assumption); try assumption.
  apply (materialize_nolazy H model _ HL). apply ranges_avoid_cons; [|apply ranges_avoid_nil].
  exact (iov1_avoids segs H HH mr iov _ _ Hc Rb1 Rn1).
Qed.

End NoLazyS.
