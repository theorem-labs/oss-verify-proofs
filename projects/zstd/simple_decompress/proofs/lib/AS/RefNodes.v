(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AS Require Import Gap04.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AS Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes SpecConsts.
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
From Stdlib Require Import Zify.
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker
        | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition t_alt3 (A B C : TSet) : TSet := t_alt2 A (t_alt2 B C).

Lemma t_alt2_idem : forall A, t_eq (t_alt2 A A) A.
Proof. intros A tr. unfold t_alt2. tauto. Qed.

Lemma t_alt3_idem : forall A, t_eq (t_alt3 A A A) A.
Proof. intros A tr. unfold t_alt3, t_alt2. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_fds_halted' : forall fds m, m_halted (with_fds fds m) = m_halted m.
Proof. intros fds m. reflexivity. Qed.

Lemma with_fds_lazy : forall fds m, m_vm_lazy (with_fds fds m) = m_vm_lazy m.
Proof. intros fds m. reflexivity. Qed.

Lemma with_tid_halted : forall t m, m_halted (with_tid t m) = m_halted m.
Proof. intros t m. reflexivity. Qed.

Lemma with_tid_lazy : forall t m, m_vm_lazy (with_tid t m) = m_vm_lazy m.
Proof. intros t m. reflexivity. Qed.

Lemma with_vmmaps_lazy' : forall h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. intros h m. reflexivity. Qed.

Lemma with_vmmaps_eta : forall m,
  with_vmmaps (m_vmmaps m) m = m.
Proof. intros m. destruct m as [? [? ? ?] ? ? ? ?]; reflexivity. Qed.

Lemma vmmaps_eta : forall h,
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) = h.
Proof. intros h. destruct h; reflexivity. Qed.

Lemma Z_to_bv_u_eq' : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma vm_forget_range_id : forall lo hi m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_forget_range lo hi m = m.
Proof.
  intros lo hi m Hl Hm. unfold vm_forget_range, with_vm_backing.
  rewrite Hl, Hm. cbn [maps_subtract List.filter].
  destruct m as [? [? l mt] ? ? ? ?]. cbn in Hl, Hm. subst. reflexivity.
Qed.

Lemma vm_forget_range_lazy_nil : forall lo hi m,
  m_vm_lazy m = [] -> m_vm_lazy (vm_forget_range lo hi m) = [].
Proof.
  intros lo hi m Hl. unfold vm_forget_range, with_vm_backing. cbn [m_vm_lazy]. rewrite Hl. reflexivity.
Qed.

Lemma vm_forget_range_halted : forall lo hi m,
  m_halted (vm_forget_range lo hi m) = m_halted m.
Proof. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma mmap_check : forall ms x8 model eff,
  bv_unsigned x8 = 222%Z ->
  check_syscall (sys_input segs ms x8) eff model
  = check_mmap (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 4) (ms_gpr ms 5) eff model.
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

Lemma munmap_check : forall ms x8 model eff,
  bv_unsigned x8 = 215%Z ->
  check_syscall (sys_input segs ms x8) eff model = check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model.
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive three : Type := T1 | T2 | T3.

Lemma rz_alt3 : forall c (nx : three -> config) (A B C : TSet),
  node_ok segs c three (fun _ => []) nx ->
  realizes segs (nx T1) A -> realizes segs (nx T2) B -> realizes segs (nx T3) C ->
  realizes segs c (t_alt3 A B C).
Proof.
  intros c nx A B C Hnode HA HB HC.
  apply (rz_conseq segs c (t_alt (fun i => match i with T1 => A | T2 => B | T3 => C end))).
  - apply (rz_cases segs c three nx _ T1 Hnode). intros [| |]; assumption.
  - intros tr. unfold t_alt3, t_alt2, t_alt. split.
    + intros [[| |] H]; tauto.
    + intros [H | [H | H]]; [exists T1 | exists T2 | exists T3]; exact H.
Qed.

(* [comment removed for export] *)
Lemma node_of_iff : forall c (I : Type) (evs : I -> list event) (nx : I -> config),
  (forall i, sstep_cfg segs ACFG c (evs i) (SNext (nx i))) ->
  (forall e st, sstep_cfg segs ACFG c e st -> exists i, e = evs i /\ st = SNext (nx i)) ->
  node_ok segs c I evs nx.
Proof.
  intros c I evs nx each_branch_steps steps_are_branches.
  exact (conj each_branch_steps steps_are_branches).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma adv_ret_epend : forall regs pc mem rom x8 r,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_eff_ret. Qed.

Lemma adv_zeros1_epend : forall regs pc mem rom x8 r a n,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [(a, n)] [] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (zfill a n mem) rom.
Proof.
  intros. unfold epend.
  assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
  { cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_copies].
  unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

Lemma adv_unmaps1_epend : forall regs pc mem rom x8 r a n,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [(a, n)] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (unfill a n mem) rom.
Proof.
  intros. unfold epend.
  assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) [] = unfill a n mem).
  { cbn [apply_writes apply_zeros].
    apply functional_extensionality. intro x.
    unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
    rewrite orb_false_r. reflexivity. }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
  unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

Lemma adv_write1_epend : forall regs pc mem rom x8 r buf data,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [(buf, data)] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (wbytes mem buf data) rom.
Proof. intros. unfold epend. rewrite adv_apply_write, write_to_mem_wbytes. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma munmap_model_simple : forall (a n : word) m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  munmap_model a n m
  = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (map_remove (vm_maps (m_vmmaps m)) a)
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof.
  intros a n m Hl Hm. unfold munmap_model, with_mmap_destroyed.
  apply vm_forget_range_id; [rewrite with_vmmaps_lazy'; exact Hl | exact Hm].
Qed.
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
Definition brk_res_acfg (m : Model) (req r : word) : Prop :=
  brk_resolution_ok m req r
  /\ (brk_refusal_b m req r = true ->
      forall r', brk_resolution_ok m req r' -> brk_refusal_b m req r' = true).
Lemma refusal_b_brk : forall ms x8 model r,
  bv_unsigned x8 = 214%Z ->
  refusal_b (sys_input segs ms x8) model r = brk_refusal_b model (ms_gpr ms 0) r.
Proof.
  intros ms x8 model r brk_no.
  assert (arg_first : in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0)
    by (apply in_arg_sys_input; lia).
  rewrite <- arg_first. apply refusal_b_214.
  rewrite in_sysno_sys_input. exact brk_no.
Qed.
Lemma brk_acfg_iff : forall ms x8 model eff model' evs,
  m_halted model = None ->
  bv_unsigned x8 = 214%Z ->
  (syscall_spec_acfg (sys_input segs ms x8) model (Ok eff model' evs) <->
   (eff = mkEffectU (eff_ret eff) []
            (brk_zeros (ms_gpr ms 0) (eff_ret eff) (vm_brk (m_vmmaps model)))
            (brk_unmaps (eff_ret eff) (vm_brk (m_vmmaps model))) [] []
    /\ evs = []
    /\ brk_res_acfg model (ms_gpr ms 0) (eff_ret eff)
    /\ model' = brk_model (ms_gpr ms 0) (eff_ret eff) model)).
Proof.
  intros ms x8 model eff model' evs not_halted brk_no.
  assert (refusal_here : forall r,
            refusal_b (sys_input segs ms x8) model r = brk_refusal_b model (ms_gpr ms 0) r)
    by (intros r; exact (refusal_b_brk ms x8 model r brk_no)).
  assert (family_off : injected_family_off ACFG (sys_input segs ms x8) = true).
  { apply acfg_family_off_214. rewrite in_sysno_sys_input. exact brk_no. }
  split.
  - intros [spec_holds guard].
    apply (brk_ok_iff segs ms x8 model eff model' evs brk_no) in spec_holds.
    destruct spec_holds as (eff_form & no_events & resolved & next_model).
    assert (honest : ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff).
    { apply guard. rewrite next_model, brk_model_halted. exact not_halted. }
    refine (conj eff_form (conj no_events (conj (conj resolved _) next_model))).
    intros refused other other_resolved.
    rewrite <- refusal_here in refused. rewrite <- refusal_here.
    exact (nonspurious_refusal_no_grant ACFG _ model eff honest family_off refused _ _ _
             (brk_ok_intro segs ms x8 model other brk_no other_resolved)).
  - intros (eff_form & no_events & [resolved all_refused] & next_model).
    split.
    + apply (brk_ok_iff segs ms x8 model eff model' evs brk_no).
      exact (conj eff_form (conj no_events (conj resolved next_model))).
    + intros _ (_ & refused & alt_eff & alt_model & alt_evs & alt_spec & alt_granted).
      apply (brk_ok_iff segs ms x8 model alt_eff alt_model alt_evs brk_no) in alt_spec.
      destruct alt_spec as (_ & _ & alt_resolved & _).
      rewrite refusal_here in refused. rewrite refusal_here in alt_granted.
      rewrite (all_refused refused (eff_ret alt_eff) alt_resolved) in alt_granted.
      discriminate alt_granted.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_brk : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  node_ok segs (mkCfg ms model)
    {r : word | brk_res_acfg model (ms_gpr ms 0) r}
    (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms
                       (mkEffectU (proj1_sig i) []
                          (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                          (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
                    (brk_model (ms_gpr ms 0) (proj1_sig i) model)).
Proof.
  intros ms model x8 not_halted no_lazy pending brk_no.
  pose (brk_eff := fun r : word =>
          {| eff_ret := r; eff_writes := [];
             eff_zeros := brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model));
             eff_unmaps := brk_unmaps r (vm_brk (m_vmmaps model));
             eff_copies := []; eff_copyins := [] |}).
  assert (never_unmodeled : forall eff,
            check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled).
  { intros eff unmodeled. apply (check_syscall_err_iff _ eff) in unmodeled.
    exact (brk_no_unmodeled segs ms x8 model brk_no unmodeled). }
  assert (next_live : forall r, m_halted (brk_model (ms_gpr ms 0) r model) = None)
    by (intros r; exact (eq_trans (brk_model_halted _ r model) not_halted)).
  assert (spec_of_res : forall r, brk_res_acfg model (ms_gpr ms 0) r ->
            syscall_spec (sys_input segs ms x8) model
              (Ok (brk_eff r) (brk_model (ms_gpr ms 0) r model) []))
    by (intros r [resolved _]; exact (brk_ok_intro segs ms x8 model r brk_no resolved)).
  assert (next_eager : forall i : {r : word | brk_res_acfg model (ms_gpr ms 0) r},
            m_vm_lazy (brk_model (ms_gpr ms 0) (proj1_sig i) model) = []).
  { intros [r res].
    destruct (brk_step_shape segs ms x8 model _ _ _ not_halted no_lazy brk_no (spec_of_res r res))
      as (_ & _ & _ & _ & lazy_kept).
    exact (eq_trans lazy_kept no_lazy). }
  assert (accepted : forall i : {r : word | brk_res_acfg model (ms_gpr ms 0) r},
            check_syscall (sys_input segs ms x8) (brk_eff (proj1_sig i)) model
            = CheckOk (brk_model (ms_gpr ms 0) (proj1_sig i) model) []).
  { intros [r res]. apply check_syscall_ok_iff. exact (spec_of_res r res). }
  assert (honest : forall i : {r : word | brk_res_acfg model (ms_gpr ms 0) r},
            ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (brk_eff (proj1_sig i))).
  { intros [r res].
    refine (acfg_outcome_ok_nonspurious _ _ _ (brk_model (ms_gpr ms 0) r model) [] _ (next_live r)).
    refine (proj2 (brk_acfg_iff ms x8 model (brk_eff r) _ [] not_halted brk_no) _).
    exact (conj eq_refl (conj eq_refl (conj res eq_refl))). }
  assert (only_these : forall eff m' evs,
            check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
            spec_step_ok (sys_input segs ms x8) model (Ok eff m' evs) ->
            exists i : {r : word | brk_res_acfg model (ms_gpr ms 0) r},
              eff = brk_eff (proj1_sig i)
              /\ m' = brk_model (ms_gpr ms 0) (proj1_sig i) model /\ evs = []).
  { intros eff m' evs checked step_ok.
    apply check_syscall_ok_iff in checked.
    destruct (proj1 (brk_acfg_iff ms x8 model eff m' evs not_halted brk_no) (conj checked step_ok))
      as (eff_form & no_events & res & next_model).
    exists (exist _ (eff_ret eff) res).
    exact (conj eff_form (conj next_model no_events)). }
  exact (node_chk segs ms model x8 _ (fun i => brk_eff (proj1_sig i))
           (fun i => brk_model (ms_gpr ms 0) (proj1_sig i) model)
           not_halted pending accepted honest only_these never_unmodeled
           (fun i => next_live (proj1_sig i)) next_eager).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma brk_r_ok_grow_cases : forall m req r,
  let h := m_vmmaps m in
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk h) <= bv_unsigned req)%Z ->
  brk_resolution_ok m req r <->
  (r = vm_brk h \/ (r = req /\ Mmap.brk_grow_ok m req req = true)).
Proof.
  intros m req r h Hpos Hs Hb.
  unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta. fold h.
  assert (E0 : w_is0 req = false).
  { unfold w_is0, bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
  rewrite E0. unfold min_brk.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [orb].
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  rewrite andb_true_iff, orb_true_iff, !bv_eqb_eq. split.
  - intros [[-> | ->] Hg]; [right; auto | left; reflexivity].
  - intros [-> | [-> Hg]]; split; [right; reflexivity | | left; reflexivity | exact Hg].
    unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok. fold h. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_model_keep : forall m req,
  brk_model req (vm_brk (m_vmmaps m)) m = m.
Proof.
  intros m req. unfold brk_model, with_brk_next. cbv zeta.
  rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next.
  rewrite Z.ltb_irrefl, andb_false_r, brk_grants_keep, brk_unmaps_keep.
  cbn [app maps_subtract_ranges fold_left]. rewrite vmmaps_eta. apply with_vmmaps_eta.
Qed.

(* [comment removed for export] *)
Lemma brk_model_grow_eq : forall m (d : Z),
  let h := m_vmmaps m in
  let b := vm_brk h in
  (0 < d)%Z -> (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z ->
  brk_model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) m
  = with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                   (vm_noaccess h) (vm_start_brk h)
                   (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m.
Proof.
  intros m d h b Hd Hb0 Hnw Hbal Hdal.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)).
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  unfold brk_model, with_brk_next. cbv zeta. fold h. fold b.
  rewrite (brk_unmaps_grow req b) by lia. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next. fold b.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned b))) by lia. rewrite andb_false_r.
  rewrite (brk_grants_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
  cbn [app maps_subtract_ranges fold_left].
  replace (req - b) with (Z_to_bv 64 d); [reflexivity|].
  apply bv_eq. rewrite bv_sub_unsigned, Hureq.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition noaccess_model (a n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                 ((a, n) :: vm_maps (m_vmmaps m))
                 ((a, n) :: vm_noaccess (m_vmmaps m))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

(* [comment removed for export] *)
Definition grant_ok_na (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).

Lemma grant_ok_grant_ok_na : forall hint m a n, grant_ok hint m a n = true -> grant_ok_na hint m a n = true.
Proof.
  intros hint m a n H. unfold grant_ok in H. unfold grant_ok_na.
  apply andb_true_iff in H as [H _]. exact H.
Qed.

Lemma grant_ok_na_unpack : forall hint m a n,
  grant_ok_na hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true /\ True.
Proof.
  intros hint m a n H. unfold grant_ok_na in H.
  rewrite !andb_true_iff in H. destruct H as [[[H1 H2] H3] H4].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. repeat split; assumption.
Qed.

Definition mmap_noaccess_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
  /\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

Lemma mmap_noaccess_check : forall ms x8 model eff,
  bv_unsigned x8 = 222%Z -> mmap_noaccess_args_ok ms ->
  check_syscall (sys_input segs ms x8) eff model
  = let n := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
    match eff with
    | mkEffectU r [] [] us [] [] =>
        (* [comment removed for export] *)
        if errno_ret_in mmap_errnos r
        then match us with [] => CheckOk model [] | _ => CheckReject end
        else if grant_ok_na (ms_gpr ms 0) model r n && listNN_eqb us [(r, Z_to_bv 64 n)]
             then CheckOk (noaccess_model r (Z_to_bv 64 n) model) []
             else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff Hno (H1 & H2 & H3 & H4 & H5).
  rewrite (mmap_check ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
  replace (mmap_anon_b (Z_to_bv 64 34)) with true by (vm_compute; reflexivity).
  replace (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with false
    by (vm_compute; reflexivity).
  replace (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with true
    by (vm_compute; reflexivity).
  cbn [negb]. cbv beta iota zeta.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
  destruct (errno_ret_in mmap_errnos r); [reflexivity|].
  unfold grant_ok_na, noaccess_model, with_mmap_backing.
  replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity).
  rewrite <- !andb_assoc. reflexivity.
Qed.

Lemma grant_na_not_errno : forall b hint model a n,
  (0 <= n)%Z -> grant_ok_na hint model a n = true -> errno_ret_in (mmap_errnos_when b) a = false.
Proof.
  intros b hint model a n Hn Hg. unfold grant_ok_na in Hg.
  apply andb_true_iff in Hg as [Hg _]. apply andb_true_iff in Hg as [Hg Hce]. apply Z.leb_le in Hce.
  apply errno_ret_in_below; [destruct b; reflexivity|].
  pose proof (alloc_top_room (m_vmmaps model)). unfold two_pow_64, stack_max_size in *. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mprotect_model (addr n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                 (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

Lemma mprotect_model_next_eq : forall m addr n, mprotect_model_next m addr n = mprotect_model addr n m.
Proof. reflexivity. Qed.

Lemma check_syscall_226 : forall ms x8 eff m,
  bv_unsigned x8 = 226%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_mprotect (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

Lemma mprotect_check : forall ms x8 model eff (addr : word) (len : Z),
  bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        (* [comment removed for export] *)
        if errno_ret_in mprotect_errnos r
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if mprotect_budget_ok model addr n && w_is0 r && listNN_eqb zs [(addr, n)]
             then CheckOk (mprotect_model addr n model) []
             else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; unfold two_pow_64 in Hlen'; lia).
  rewrite (check_syscall_226 ms x8 eff model Hno). unfold check_mprotect.
  rewrite H0, H2, Hu1.
  replace (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false by (vm_compute; reflexivity).
  replace (mprotect_modeled_b (Z_to_bv 64 3)) with true by (vm_compute; reflexivity).
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0, bv_eqb. rewrite Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
  rewrite E1. rewrite (proj2 (Z.leb_gt _ _)) by lia.
  cbv beta iota zeta. fold n. rewrite Hna, Hma. cbn [andb].
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct us; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
  destruct cs; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
  destruct ci; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
  reflexivity.
Qed.

Lemma ENOMEM_in_mprotect_errnos : In ENOMEM mprotect_errnos.
Proof. left. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fixed_noaccess_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                   ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

(* [comment removed for export] *)
Definition fixed_destroyed_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                   (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

Lemma fixed_noaccess_model_simple : forall addr n m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  fixed_noaccess_model addr n m
  = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                   ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof. intros. unfold fixed_noaccess_model. apply vm_forget_range_id; [rewrite with_vmmaps_lazy'|]; assumption. Qed.

Lemma fixed_destroyed_model_simple : forall addr n m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  fixed_destroyed_model addr n m
  = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                   (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof. intros. unfold fixed_destroyed_model. apply vm_forget_range_id; [rewrite with_vmmaps_lazy'|]; assumption. Qed.

Definition mmap_fixed_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
  /\ ms_gpr ms 3 = Z_to_bv 64 50 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma check_syscall_96 : forall ms x8 eff m,
  bv_unsigned x8 = 96%Z ->
  check_syscall (sys_input segs ms x8) eff m = check_set_tid_address eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

Definition tid_I : Type := { t : word | (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z }.

Lemma one_tid_ok : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z.
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.

Lemma node_set_tid : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  node_ok segs (mkCfg ms model) tid_I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)).
Proof.
  intros ms model x8 not_halted no_lazy pending tid_no tid_unset.
  assert (routed : forall eff,
            check_syscall (sys_input segs ms x8) eff model = check_set_tid_address eff model)
    by (intros eff; exact (check_syscall_96 ms x8 eff model tid_no)).
  assert (never_unmodeled : forall eff,
            check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled).
  { intros eff. rewrite routed. unfold check_set_tid_address. rewrite tid_unset.
    repeat match goal with
           | |- context [match ?scrut with _ => _ end] => destruct scrut
           end; discriminate. }
  assert (accepted : forall i : tid_I,
            check_syscall (sys_input segs ms x8) (mkEffect (proj1_sig i) [] []) model
            = CheckOk (with_tid (proj1_sig i) model) []).
  { intros [t [above_zero below_cap]]. rewrite routed. cbn [proj1_sig].
    unfold check_set_tid_address. rewrite tid_unset.
    rewrite (proj2 (Z.ltb_lt _ _) above_zero), (proj2 (Z.ltb_lt _ _) below_cap).
    reflexivity. }
  assert (only_these : forall eff m' evs,
            check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
            spec_step_ok (sys_input segs ms x8) model (Ok eff m' evs) ->
            exists i : tid_I,
              eff = mkEffect (proj1_sig i) [] [] /\ m' = with_tid (proj1_sig i) model /\ evs = []).
  { intros [ret writes zeros unmaps copies copyins] m' evs checked _.
    rewrite routed in checked. unfold check_set_tid_address in checked.
    destruct writes; [|discriminate checked]. destruct zeros; [|discriminate checked].
    destruct unmaps; [|discriminate checked]. destruct copies; [|discriminate checked].
    destruct copyins; [|discriminate checked].
    rewrite tid_unset in checked.
    destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z) eqn:in_range;
      [|discriminate checked].
    injection checked as next_model no_events.
    apply andb_true_iff in in_range as [above_zero below_cap].
    exists (exist _ ret (conj (proj1 (Z.ltb_lt _ _) above_zero) (proj1 (Z.ltb_lt _ _) below_cap))).
    cbn [proj1_sig]. rewrite <- next_model, <- no_events. auto. }
  assert (via_effect : node_ok segs (mkCfg ms model) tid_I (fun _ => [])
            (fun i => mkCfg (advance_past_svc (apply_effect ms (mkEffect (proj1_sig i) [] [])))
                            (with_tid (proj1_sig i) model))).
  { pose proof (acfg_nonspurious_no segs ms x8 96 model) as honest.
    exact (node_chk segs ms model x8 tid_I (fun i => mkEffect (proj1_sig i) [] [])
             (fun i => with_tid (proj1_sig i) model) not_halted pending accepted
             (fun i => honest _ tid_no eq_refl) only_these never_unmodeled
             (fun i => eq_trans (with_tid_halted _ model) not_halted)
             (fun i => eq_trans (with_tid_lazy _ model) no_lazy)). }
  destruct via_effect as [branch_steps branch_cover].
  apply node_of_iff.
  - intros i. cbv beta. rewrite <- apply_effect_no_write. exact (branch_steps i).
  - intros e st stepped.
    destruct (branch_cover e st stepped) as (i & events & next).
    exists i. split; [exact events|].
    rewrite next. cbv beta. rewrite apply_effect_no_write. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_exit_at : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  realizes segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply rz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_exit_at_lit : forall regs (pc : word) mem rom model w (code : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10 Hc.
  rewrite <- (bv_and_255_small code Hc). eapply rz_exit_at; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vm_backing_used_simple : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m = vm_backed_bytes (m_vmmaps m).
Proof.
  intros m Hl Hm. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat Z.mul]. unfold vm_backed_bytes. lia.
Qed.

Lemma vm_backed_bytes_no_noaccess : forall h,
  vm_noaccess h = [] -> vm_backed_bytes h = vm_live_bytes h.
Proof. intros h H. unfold vm_backed_bytes, vm_backed_maps. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_aligned_intro : forall m d,
  let h := m_vmmaps m in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z ->
  (bv_unsigned b + d <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (d + page_size)) = true ->
  (vm_backing_used m + d <= vm_limit h)%Z ->
  Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true.
Proof.
  intros m d h b Hbal Hdal Hd Hb0 Hce Hrf Hlive.
  pose proof (u64_range b) as Hbr. pose proof (alloc_top_lt_2_64 h) as Htop.
  assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = (bv_unsigned b + d)%Z) by (apply u64_lit; lia).
  unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok. fold h. fold b. rewrite Hureq.
  rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) by lia. cbn [andb].
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned b + d))
    by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
  replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z by lia. rewrite Hrf.
  replace (bv_unsigned (Z_to_bv 64 (bv_unsigned b + d) - b)) with d.
  2:{ rewrite bv_sub_unsigned, Hureq. rewrite bv_wrap_small by (unfold bv_modulus; lia). lia. }
  rewrite (proj2 (Z.leb_le _ _) Hlive). reflexivity.
Qed.

End WithSegs.

(* [comment removed for export] *)
Local Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_roundtrip : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma region_free_app : forall l1 l2 (lo n : word),
  region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
  induction l1 as [|[b s] l1 IH]; intros l2 lo n; [reflexivity|].
  cbn [region_free app]. rewrite IH, andb_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_In : forall l (lo n b s : word),
  region_free l lo n = true -> In (b, s) l ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo.
Proof.
  induction l as [|[b' s'] l IH]; intros lo n b s Hrf Hin; [destruct Hin|].
  apply region_free_cons in Hrf as [Hd Hrf].
  destruct Hin as [E | Hin]; [injection E as -> ->; exact Hd | exact (IH _ _ _ _ Hrf Hin)].
Qed.

Lemma region_free_intro : forall l (lo n : word),
  (forall b s, In (b, s) l ->
     bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
  region_free l lo n = true.
Proof.
  induction l as [|[b s] l IH]; intros lo n H; [reflexivity|].
  cbn [region_free]. rewrite IH by (intros b' s' Hin; apply H; right; exact Hin).
  rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap. apply andb_false_iff.
  destruct (H b s (or_introl eq_refl)) as [Hl | Hr]; [right | left]; apply Z.ltb_ge; lia.
Qed.

(* [comment removed for export] *)
Lemma map_has_head : forall (a n : word) l, map_has ((a, n) :: l) a n = true.
Proof. intros. unfold map_has. cbn [existsb fst snd]. rewrite !bv_eqb_refl. reflexivity. Qed.

Lemma map_has_cons : forall p (a n : word) l, map_has l a n = true -> map_has (p :: l) a n = true.
Proof. intros p a n l H. unfold map_has in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

Lemma map_contains_head : forall (a sz lo n : word) l,
  bv_unsigned a <= bv_unsigned lo ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned a + bv_unsigned sz ->
  map_contains ((a, sz) :: l) lo n = true.
Proof.
  intros a sz lo n l H1 H2. unfold map_contains. cbn [existsb fst snd].
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity.
Qed.

Lemma map_contains_cons : forall p (lo n : word) l,
  map_contains l lo n = true -> map_contains (p :: l) lo n = true.
Proof. intros p lo n l H. unfold map_contains in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

(* [comment removed for export] *)
Lemma map_remove_nil : forall (a : word), map_remove [] a = [].
Proof. reflexivity. Qed.

Lemma map_remove_head : forall (a n : word) l, map_remove ((a, n) :: l) a = map_remove l a.
Proof. intros. unfold map_remove. cbn [List.filter fst]. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma map_remove_skip : forall (b s a : word) l,
  b <> a -> map_remove ((b, s) :: l) a = (b, s) :: map_remove l a.
Proof. intros b s a l H. unfold map_remove. cbn [List.filter fst]. rewrite (bv_eqb_neq _ _ H). reflexivity. Qed.

Lemma map_remove_notin : forall l (a : word),
  (forall b s, In (b, s) l -> b <> a) -> map_remove l a = l.
Proof.
  induction l as [|[b s] l IH]; intros a H; [reflexivity|].
  rewrite map_remove_skip by (apply (H b s); left; reflexivity).
  rewrite IH by (intros b' s' Hin; apply (H b' s'); right; exact Hin). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma disjoint_base_ne : forall (lo n b s : word),
  0 < bv_unsigned n -> 0 < bv_unsigned s ->
  (bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
  b <> lo.
Proof. intros lo n b s Hn Hs Hd ->. lia. Qed.

(* [comment removed for export] *)
Lemma live_bytes_cons : forall (a n : word) l, live_bytes ((a, n) :: l) = bv_unsigned n + live_bytes l.
Proof. reflexivity. Qed.

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; [cbn; lia|]. cbn [live_bytes]. pose proof (u64_range n). lia. Qed.

Lemma live_bytes_map_remove_le : forall l (a : word), live_bytes (map_remove l a) <= live_bytes l.
Proof.
  induction l as [|[b s] l IH]; intros a; [cbn; lia|].
  unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [live_bytes];
    fold (map_remove l a); pose proof (IH a); pose proof (u64_range s); lia.
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_nil : forall (lo hi : Z), maps_subtract [] lo hi = [].
Proof. reflexivity. Qed.

Lemma maps_subtract_cons : forall (a sz : word) (lo hi : Z) l,
  maps_subtract ((a, sz) :: l) lo hi = iv_subtract a sz lo hi ++ maps_subtract l lo hi.
Proof. reflexivity. Qed.

Lemma maps_subtract_app : forall l1 l2 (lo hi : Z),
  maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof.
  induction l1 as [|[a sz] l1 IH]; intros l2 lo hi; [reflexivity|].
  cbn [maps_subtract app]. rewrite IH, app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_covered : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a + bv_unsigned sz <= hi ->
  iv_subtract a sz lo hi = [].
Proof.
  intros a sz lo hi H1 H2. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_ge _ _) H2). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_self : forall (a sz : word),
  iv_subtract a sz (bv_unsigned a) (bv_unsigned a + bv_unsigned sz) = [].
Proof. intros a sz. apply iv_subtract_covered; lia. Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : forall (a sz : word) (lo hi : Z),
  0 < bv_unsigned sz -> lo <= hi ->
  (hi <= bv_unsigned a \/ bv_unsigned a + bv_unsigned sz <= lo) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hsz Hlh Hd. unfold iv_subtract.
  destruct Hd as [Hd | Hd].
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
    rewrite Z.max_l by lia. rewrite u64_roundtrip.
    replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite u64_roundtrip. reflexivity.
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [app].
    rewrite Z.min_l by lia. rewrite u64_roundtrip. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_suffix : forall (a sz : word) (lo hi : Z),
  bv_unsigned a < lo -> lo <= bv_unsigned a + bv_unsigned sz ->
  bv_unsigned a + bv_unsigned sz <= hi ->
  iv_subtract a sz lo hi = [(a, Z_to_bv 64 (lo - bv_unsigned a))].
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.ltb_ge _ _) H3). cbn [app].
  rewrite Z.min_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_prefix : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a <= hi ->
  hi < bv_unsigned a + bv_unsigned sz ->
  iv_subtract a sz lo hi = [(Z_to_bv 64 hi, Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - hi))].
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_lt _ _) H3). cbn [app].
  rewrite Z.max_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_sizes : forall (a sz : word) (lo hi : Z) N,
  0 <= lo -> hi < 2 ^ 64 ->
  bv_unsigned sz <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi N Hlo Hhi Hs. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract. apply Forall_app. split.
  - destruct (bv_unsigned a <? lo) eqn:E; [|constructor].
    apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
    rewrite u64_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|constructor].
    apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
    rewrite u64_lit by lia. lia.
Qed.

Lemma maps_subtract_sizes : forall l (lo hi : Z) N,
  0 <= lo -> hi < 2 ^ 64 ->
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  Forall (fun p => bv_unsigned (snd p) <= N) (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi N Hlo Hhi H; [constructor|].
  inversion H as [|p l' Hp Hl]; subst. cbn [maps_subtract]. apply Forall_app. split.
  - apply iv_subtract_sizes; assumption.
  - apply IH; assumption.
Qed.

Lemma map_remove_sizes : forall l (a : word) N,
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  Forall (fun p => bv_unsigned (snd p) <= N) (map_remove l a).
Proof.
  intros l a N H. unfold map_remove. apply List.incl_Forall with (l1 := l); [|exact H].
  apply List.incl_filter.
Qed.

Lemma maps_subtract_length : forall l (lo hi : Z),
  (length (maps_subtract l lo hi) <= 2 * length l)%nat.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi; [cbn; lia|].
  cbn [maps_subtract]. rewrite length_app. cbn [length].
  assert (length (iv_subtract a sz lo hi) <= 2)%nat.
  { unfold iv_subtract. rewrite length_app.
    destruct (_ <? _); destruct (_ <? _); cbn; lia. }
  specialize (IH lo hi). lia.
Qed.

Lemma map_remove_length : forall l (a : word), (length (map_remove l a) <= length l)%nat.
Proof.
  induction l as [|[b s] l IH]; intros a; [cbn; lia|].
  unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [length];
    fold (map_remove l a); specialize (IH a); lia.
Qed.

(* [comment removed for export] *)
Lemma live_bytes_iv_subtract_le : forall (a sz : word) (lo hi : Z),
  lo <= hi ->
  live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros a sz lo hi Hlh. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract.
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
    cbn [app live_bytes];
    first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
    rewrite ?u64_lit by lia; lia.
Qed.

Lemma live_bytes_maps_subtract_le : forall l (lo hi : Z),
  lo <= hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh; [cbn; lia|].
  cbn [maps_subtract live_bytes]. rewrite live_bytes_app.
  pose proof (live_bytes_iv_subtract_le a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma maps_subtract_all_nil : forall maps, maps_subtract_all maps [] = maps.
Proof. reflexivity. Qed.

Lemma maps_subtract_all_cons : forall maps (a n : word) cuts,
  maps_subtract_all maps ((a, n) :: cuts)
  = maps_subtract_all (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) cuts.
Proof. reflexivity. Qed.

Lemma live_bytes_maps_subtract_all_le : forall cuts maps,
  live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; [cbn; lia|].
  rewrite maps_subtract_all_cons. etransitivity; [apply IH|].
  apply live_bytes_maps_subtract_le. pose proof (u64_range n). lia.
Qed.

(* [comment removed for export] *)
Lemma vm_backed_bytes_le_live : forall h, vm_backed_bytes h <= vm_live_bytes h.
Proof. intros h. unfold vm_backed_bytes, vm_backed_maps, vm_live_bytes. apply live_bytes_maps_subtract_all_le. Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le_live : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m <= vm_live_bytes (m_vmmaps m).
Proof.
  intros m Hl Hm. rewrite (vm_backing_used_simple m Hl Hm). apply vm_backed_bytes_le_live.
Qed.

Lemma grant_budget_intro : forall m n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_live_bytes (m_vmmaps m) + n <= vm_limit (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m).
Proof. intros m n Hl Hm H. pose proof (vm_backing_used_le_live m Hl Hm). lia. Qed.

(* [comment removed for export] *)
Lemma mprotect_budget_ok_intro : forall m addr n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_live_bytes (m_vmmaps m) <= vm_limit (m_vmmaps m) ->
  mprotect_budget_ok m addr n = true.
Proof.
  intros m addr n Hl Hm Hlive. unfold mprotect_budget_ok, vm_backing_within_limit.
  rewrite mprotect_model_next_eq. apply Z.leb_le.
  etransitivity; [apply vm_backing_used_le_live; [unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hl | exact Hm]|].
  unfold mprotect_model. rewrite with_vmmaps_vm. cbn [vm_live_bytes vm_maps vm_limit]. exact Hlive.
Qed.

(* [comment removed for export] *)
Lemma file_read_length_eq : forall data (off count : word),
  length (file_read data off count) = Nat.min (word_to_nat count) (length data - word_to_nat off).
Proof. intros. rewrite length_file_read. reflexivity. Qed.

Lemma file_read_length_le : forall data (off count : word),
  (length (file_read data off count) <= word_to_nat count)%nat
  /\ (length (file_read data off count) <= length data - word_to_nat off)%nat.
Proof. intros data off count. rewrite file_read_length_eq. split; lia. Qed.

