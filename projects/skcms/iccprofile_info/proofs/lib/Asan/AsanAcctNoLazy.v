(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  SimInv ExitSim CatSim CatExec PropExec SeqExec Hoare ShapeAlg Nodes FileSim AgentLib AgentNodes
  LibWritev AsanAcct AsanAcctShape.
Unset Nia Cache.  (* [comment removed for export] *)

Import ListNotations.
Unset Lia Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
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
Lemma import_iovecs_accesses_copy : forall mp (iov : word) k,
  (1 <= k <= 1024)%nat -> (bv_unsigned iov + 16 * Z.of_nat k <= TASK_SIZE)%Z ->
  import_iovecs_accesses mp iov (Z_to_bv 64 (Z.of_nat k)) = copy_iovecs_accesses mp iov k.
Proof.
  intros mp iov k Hk HT. unfold import_iovecs_accesses.
  assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k) by (apply u64_lit; lia).
  destruct (bv_eqb (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 1)) eqn:E1.
  - apply bv_eqb_eq in E1. assert (Ek : k = 1%nat).
    { apply (f_equal bv_unsigned) in E1. rewrite Hu in E1. change (bv_unsigned (Z_to_bv 64 1)) with 1%Z in E1. lia. }
    subst k. rewrite (access_okb_of_le iov 16) by lia. cbn [negb].
    cbn [copy_iovecs_accesses]. destruct (read_iovec_entry mp iov); reflexivity.
  - destruct (bv_eqb (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 0)) eqn:E0.
    { apply bv_eqb_eq in E0. apply (f_equal bv_unsigned) in E0. rewrite Hu in E0. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E0. lia. }
    rewrite Hu. replace (IOV_MAX <? Z.of_nat k)%Z with false by (symmetry; apply Z.ltb_ge; unfold IOV_MAX; lia).
    rewrite (access_okb_of_le iov (16 * Z.of_nat k)) by lia. cbn [negb].
    f_equal. unfold word_to_nat. rewrite Hu. apply Nat2Z.id.
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
    + cbn [iov_prefix_accesses]. rewrite word_to_nat_bounded_eq_min.   (* [comment removed for export] *)
      set (k := Nat.min (word_to_nat n) (S l')).
      assert (Hr : ranges_avoid H (iov_prefix_accesses r (S l')) /\ forall x, ranges_avoid H (iov_prefix_accesses r x)).
      { split; [|intros x]; apply IH; intros b' n' Hin; apply Hall; right; exact Hin. }
      destruct (Nat.eqb k 0).
      * apply (proj2 Hr).
      * apply ranges_avoid_cons; [| apply (proj2 Hr)].
        apply (range_avoids_mono H b (word_to_nat n)); [apply Hall; left; reflexivity | lia].
Qed.

(* [comment removed for export] *)
Lemma rz_writev_pending_R : forall ms x8 model (fd : Z) (iov : word) iovs bss (T : nat -> TSet),
  ms_rom ms = seg_rom segs ->
  lazy_all_hidden H model -> m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd ->
  ms_gpr ms 1 = iov ->
  ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->   (* [comment removed for export] *)
  iov_array segs (ms_mem ms) iov iovs ->
  iov_bufs_ok iovs ->                                                 (* [comment removed for export] *)
  iov_bufs segs (ms_mem ms) iovs bss ->
  range_avoids H iov (16 * length iovs) ->
  (forall b n, In (b, n) iovs -> range_avoids H b (word_to_nat n)) ->
  let bs := concat bss in
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length bs)%nat ->
     realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))) model) (T k)) ->
  realizes segs (mkCfg ms model)
    (t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
  intros ms x8 model fd iov iovs bss T Hrom HL Hh Hsvc Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs Haviov Havbuf
         bs Ht1 Htmax Ht30 Hk.
  destruct (writev_check segs ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs Ht1 Htmax Ht30)
    as [Hlen Hchk]. fold bs in Hlen, Hchk.
  set (tot := iovs_total iovs) in *.
  set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
  assert (HCA : ranges_avoid H CA).
  { subst CA. rewrite (import_iovecs_accesses_copy _ iov (length iovs) Hcnt Hiok).
    rewrite (copy_iovecs_accesses_of_array ms iovs iov Hrom Harr).
    intros a n Hin. apply in_map_iff in Hin as (i & E & Hi). injection E as <- <-.
    apply in_seq in Hi.
    replace (16 * Z.of_nat i)%Z with (Z.of_nat (16 * i)) by lia.
    apply (range_avoids_sub H iov (16 * length iovs)); [exact Haviov | lia | lia]. }
  assert (Hnb : (1 <= length bs)%nat) by lia.
  pose (effs := fun i : wr_index bs =>
          mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] []
                    (CA ++ iov_prefix_accesses iovs (proj1_sig i))).
  assert (Enx : forall i : wr_index bs,
    mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) model).
  { intros [k Hk']. cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (Z_to_bv 64 (Z.of_nat k)) (CA ++ iov_prefix_accesses iovs k)).
    reflexivity. }
  apply (rz_node segs (mkCfg ms model) (wr_index bs)
           (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
           (fun i => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model)
           (fun i => T (proj1_sig i)) (wr_full bs Hnb)).
  2:{ intros [k [Hk1 Hk2]]. cbn [proj1_sig]. apply Hk; assumption. }
  assert (Hku : forall k, (k <= length bs)%nat -> bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k).
  { intros k Hk2. apply u64_lit. lia. }
  assert (Hmat : forall i : wr_index bs,
            materialize_model_accesses model (syscall_effect_accesses (effs i)) = Some model).
  { intros [k Hk']. apply (materialize_nolazy H model _ HL).
    unfold effs, syscall_effect_accesses. cbn [proj1_sig eff_copyins eff_writes write_accesses].
    rewrite app_nil_r. apply ranges_avoid_app; [exact HCA | apply iov_prefix_accesses_avoid; exact Havbuf]. }
  assert (Hok : forall i : wr_index bs,
            check_syscall (sys_input segs ms x8) (effs i) model
            = CheckOk model (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))).
  { intros [k [Hk1 Hk2]]. unfold effs. cbn [proj1_sig]. rewrite Hchk.
    rewrite (Hku k Hk2), Nat2Z.id.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
    replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat k))) with false
      by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite (Hku k Hk2); lia).
    rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity. }
  split.
  - intros i. rewrite Enx. apply (sstep_of_check_mat ms model x8); [exact Hh | exact Hsvc | apply Hok | exact Hh | apply Hmat].
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
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hm & ->) | [(Hh2 & -> & Hm & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (Hmat i) in Hm. injection Hm as <-.
      exists i. rewrite Enx. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite (Hmat i) in Hm. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). congruence.
    + exfalso. rewrite Hchk in Hc. destruct eff as [ret ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct (_ && _)%bool; [destruct (access_ranges_eqb _ _)|]; discriminate.
Qed.


(* [comment removed for export] *)


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

Lemma rz_writev2_R : forall F regs (pc : word) mr model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (T : nat -> TSet),
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
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->                     (* [comment removed for export] *)
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) (munrestrict H F mr) (seg_rom segs)) model)
              (T k)) ->
  realizes segs (mkCfg (mkst regs pc (munrestrict H F mr) (seg_rom segs)) model)
    (t_alt (fun i : wr_index (bs1 ++ bs2) =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (bs1 ++ bs2))) (T (proj1_sig i)))).
Proof.
  intros F regs pc mr model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE HL Hh Hc Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Ht1 Htmax Ht30 HT0 HT1 HT2 Hk.
  eapply rz_sys_R; [exact HL | exact Hh | exact HF | exact HE |].
  pose proof (u64_range n1). pose proof (u64_range n2).
  replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending_R (epend regs pc (munrestrict H F mr) (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1); (b2, n2)] [bs1; bs2] T);
    [reflexivity | exact HL | exact Hh | reflexivity | exact Hfd | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | cbn [length]; lia | | cbn [iov_bufs_ok]; tauto | | | | cbn [iovs_total]; lia | cbn [iovs_total]; lia | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend].
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
    2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
        rewrite at_at. reflexivity. }
    repeat split; try (apply (rdn_R F mr); assumption); lia.
  - cbn [iov_bufs ms_mem epend]. repeat split; apply (rdn_R F mr); assumption.
  - cbn [length]. exact (iov2_avoids mr iov _ _ _ _ Hc Rb1 Rn1 Rb2 Rn2).
  - intros b n [E|[E|[]]]; injection E as <- <-;
      [exact (rdn_clean_avoids segs H mr _ _ _ HH Hc Rs1) | exact (rdn_clean_avoids segs H mr _ _ _ HH Hc Rs2)].
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

Lemma rz_writev1_R : forall F regs (pc : word) mr model w (fd : Z) (iov b1 n1 : word) bs1 (T : nat -> TSet),
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
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->                     (* [comment removed for export] *)
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) (munrestrict H F mr) (seg_rom segs)) model)
              (T k)) ->
  realizes segs (mkCfg (mkst regs pc (munrestrict H F mr) (seg_rom segs)) model)
    (t_alt (fun i : wr_index bs1 =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs1)) (T (proj1_sig i)))).
Proof.
  intros F regs pc mr model w fd iov b1 n1 bs1 T HF HE HL Hh Hc Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Ht1 Htmax Ht30 HT0 HT1 Hk.
  eapply rz_sys_R; [exact HL | exact Hh | exact HF | exact HE |].
  pose proof (u64_range n1).
  replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
  replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending_R (epend regs pc (munrestrict H F mr) (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1)] [bs1] T);
    [reflexivity | exact HL | exact Hh | reflexivity | exact Hfd | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | cbn [length]; lia | | cbn [iov_bufs_ok]; tauto | | | | cbn [iovs_total]; lia | cbn [iovs_total]; lia | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend]. repeat split; try (apply (rdn_R F mr); assumption); lia.
  - cbn [iov_bufs ms_mem epend]. split; [apply (rdn_R F mr); assumption | exact I].
  - cbn [length]. exact (iov1_avoids mr iov _ _ Hc Rb1 Rn1).
  - intros b n [E|[]]; injection E as <- <-. exact (rdn_clean_avoids segs H mr _ _ _ HH Hc Rs1).
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

Lemma rz_writev2_wall_R : forall F regs (pc : word) mr model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
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
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->                     (* [comment removed for export] *)
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) (munrestrict H F mr) (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)) ->
  realizes segs (mkCfg (mkst regs pc (munrestrict H F mr) (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).
Proof.
  intros F regs pc mr model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE HL Hh Hc Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Ht1 Htmax Ht30 HT0 HT1 HT2 HK Hk.
  pose proof (rdn_length segs mr _ _ _ Rs1) as L1. pose proof (rdn_length segs mr _ _ _ Rs2) as L2.
  pose proof (u64_range n1). pose proof (u64_range n2).
  apply rz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
  eapply (rz_writev2_R F regs pc mr model w fd iov b1 n1 b2 n2 bs1 bs2
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.

Lemma rz_writev1_wall_R : forall F regs (pc : word) mr model w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
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
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->                     (* [comment removed for export] *)
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) (munrestrict H F mr) (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
  realizes segs (mkCfg (mkst regs pc (munrestrict H F mr) (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).
Proof.
  intros F regs pc mr model w fd iov b1 n1 bs1 K HF HE HL Hh Hc Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Ht1 Htmax Ht30 HT0 HT1 HK Hk.
  pose proof (rdn_length segs mr _ _ _ Rs1) as L1. pose proof (u64_range n1).
  apply rz_wall; [unfold word_to_nat in L1; lia | exact HK |].
  eapply (rz_writev1_R F regs pc mr model w fd iov b1 n1 bs1
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev1_zero_R : forall F regs (pc : word) mr model w (fd : Z) (iov b1 : word) K,
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
  (0 <= 2 ^ 30)%Z ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->        (* [comment removed for export] *)
  (bv_unsigned b1 <= TASK_SIZE)%Z ->
  realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (munrestrict H F mr) (seg_rom segs)) model) K ->
  realizes segs (mkCfg (mkst regs pc (munrestrict H F mr) (seg_rom segs)) model) K.
Proof.
  intros F regs pc mr model w fd iov b1 K HF HE HL Hh Hc Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hmax HT0 HT1 Hk.
  eapply rz_sys_R; [exact HL | exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc (munrestrict H F mr) (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Harr : iov_array segs (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
  { cbn [iov_array ms_mem ms epend].
    refine (conj (rdn_R F mr _ _ _ Hc Rb1) (conj (rdn_R F mr _ _ _ Hc Rn1) (conj _ I))). rewrite u64_lit by lia. lia. }
  assert (Hbok : iov_bufs_ok [(b1, Z_to_bv 64 0)]).
  { cbn [iov_bufs_ok]. split; [|exact I]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia. }
  pose proof (import_iovecs_of_array segs ms [(b1, Z_to_bv 64 0)] iov eq_refl ltac:(cbn; lia) ltac:(cbn [length]; lia) Harr Hbok) as Himp.
  cbn [length] in Himp. change (Z_to_bv 64 (Z.of_nat 1)) with (Z_to_bv 64 1) in Himp.
  pose proof (copy_iovecs_accesses_of_array ms [(b1, Z_to_bv 64 0)] iov eq_refl Harr) as Hca.
  cbn [length seq map] in Hca. rewrite Z.mul_0_r, Z.add_0_r, u64_roundtrip' in Hca.
  assert (Hia : import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1) = [(iov, 16%nat)]).
  { change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat 1)).
    rewrite (import_iovecs_accesses_copy _ iov 1 ltac:(lia) ltac:(cbn; lia)). exact Hca. }
  eapply (rz_ret_only_copyins_silent_mat ms model (getr regs 17)
            (import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1)) (Z_to_bv 64 0) model);
    [exact Hh | reflexivity | | exact Hh | | unfold ms; rewrite adv_set_epend; exact Hk].
  2:{ rewrite Hia. apply (materialize_nolazy H model _ HL). apply ranges_avoid_cons; [|apply ranges_avoid_nil].
      exact (iov1_avoids mr iov _ _ Hc Rb1 Rn1). }
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
  rewrite in_mem_si. rewrite Himp.
  assert (Hcap : cap_iovecs [(b1, Z_to_bv 64 0)] = [(b1, Z_to_bv 64 0)]).
  { unfold cap_iovecs. apply cap_iovecs_id. cbn [iovs_total]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. unfold MAX_RW_COUNT. lia. }
  rewrite Hcap. cbn [iovs_total]. change (bv_unsigned (Z_to_bv 64 0) + 0)%Z with 0%Z. cbn [Z.eqb].
  destruct (check_ret_only_copyins (import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1)) eff (Z_to_bv 64 0) model []) eqn:E;
    [reflexivity | reflexivity | exfalso; exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ E)].
Qed.

End NoLazy.
End WithFP1.

