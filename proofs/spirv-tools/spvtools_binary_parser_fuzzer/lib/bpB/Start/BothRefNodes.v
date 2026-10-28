(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothCeil Bcfg BRelSpec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSimInv BExitSim BPropExec BCatExec BCatSim BSeqExec BStreamExec BMmapSim BAllocSim BFileSim BShapeAlg BNodes BStoreOk BAgentLib BAgentNodes BpecConsts.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition t_alt3 (A B C : TSet) : TSet := t_alt2 A (t_alt2 B C).

Lemma with_tid_halted : forall t m, m_halted (with_tid t m) = m_halted m.
Proof. intros t m. reflexivity. Qed.

Lemma with_vmmaps_eta : forall m,
  with_vmmaps (m_vmmaps m) m = m.
Proof. intros m. destruct m as [? [? ? ?] ? ? ? ?]; reflexivity. Qed.

Lemma vmmaps_eta : forall h,
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) = h.
Proof. intros h. destruct h; reflexivity. Qed.

Lemma Z_to_bv_u_eq' : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma vm_forget_range_halted : forall lo hi m,
  m_halted (vm_forget_range lo hi m) = m_halted m.
Proof. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.

Inductive three : Type := T1 | T2 | T3.

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
    unfold Mmap.brk_grow_ok. fold h. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

Lemma brk_model_keep : forall m req,
  brk_model req (vm_brk (m_vmmaps m)) m = m.
Proof.
  intros m req. unfold brk_model, with_brk_next. cbv zeta.
  rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next.
  rewrite Z.ltb_irrefl, andb_false_r, brk_grants_keep, brk_unmaps_keep.
  cbn [app maps_subtract_ranges fold_left]. rewrite vmmaps_eta. apply with_vmmaps_eta.
Qed.

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

Definition noaccess_model (a n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                 ((a, n) :: vm_maps (m_vmmaps m))
                 ((a, n) :: vm_noaccess (m_vmmaps m))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

Definition grant_ok_na_pin (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).
Definition grant_ok_na (hint : word) (m : Model) (a : word) (n : Z) : bool := grant_ok_na_pin m a n.

Lemma grant_ok_na_unpack : forall hint m a n,
  grant_ok_na hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\ (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z
  /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
  intros hint m a n H. unfold grant_ok_na, grant_ok_na_pin in H.
  apply andb_true_iff in H as [H Hrf]. apply andb_true_iff in H as [H Htop]. apply andb_true_iff in H as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop. auto.
Qed.

Lemma grant_na_pin_not_errno : forall m a n,
  (0 <= n)%Z -> grant_ok_na_pin m a n = true -> a <> errno_ret ENOMEM.
Proof.
  intros m a n Hn Hg. unfold grant_ok_na_pin in Hg.
  apply andb_true_iff in Hg as [Hg _]. apply andb_true_iff in Hg as [Hg Htop]. apply Z.leb_le in Htop.
  intros E. apply (f_equal bv_unsigned) in E.
  rewrite (errno_ret_unsigned ENOMEM) in E by (unfold ENOMEM; lia).
  alloc_top_bounds. unfold two_pow_64, ENOMEM in *. lia.
Qed.

Definition mmap_noaccess_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
  /\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

Lemma grant_na_not_errno : forall hint model a n,
  (0 <= n)%Z -> grant_ok_na hint model a n = true -> a <> errno_ret ENOMEM.
Proof. intros hint model a n Hn Hg. exact (grant_na_pin_not_errno model a n Hn Hg). Qed.

Definition mprotect_model (addr n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                 (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

Lemma mprotect_model_next_eq : forall m addr n, mprotect_model_next m addr n = mprotect_model addr n m.
Proof. reflexivity. Qed.

Lemma mprotect_outcome_si : forall ms x8 model (addr : word) (len : Z),
  bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    mprotect_err_out model o
    \/ (mprotect_budget_ok model addr n = true
        /\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model addr n model) []).
Proof.
  intros ms x8 model addr len Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma o.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; unfold two_pow_64 in Hlen'; lia).
  rewrite (syscall_spec_226 _ model o) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, H2.
  rewrite <- mprotect_model_next_eq.
  rewrite (mprotect_expose_outcome addr (ms_gpr ms 1) (Z_to_bv 64 3) _ model o); rewrite ?Hu1;
    [reflexivity | vm_compute; reflexivity | exact Hal
    | unfold w_is0; apply bv_eqb_neq; intros E; apply (f_equal bv_unsigned) in E; rewrite Hu1 in E;
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E; lia
    | exact Hnw | vm_compute; reflexivity | exact Hna | exact Hma].
Qed.

Definition fixed_noaccess_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                   ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

Definition fixed_destroyed_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                   (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

Definition mmap_fixed_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
  /\ ms_gpr ms 3 = Z_to_bv 64 50 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

Definition tid_I : Type := { t : word | (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z }.

Lemma one_tid_ok : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z.
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.

End WithSegs.

Local Open Scope Z_scope.

Lemma u64_roundtrip : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma region_free_app : forall l1 l2 (lo n : word),
  region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
  induction l1 as [|[b s] l1 IH]; intros l2 lo n; [reflexivity|].
  cbn [region_free app]. rewrite IH, andb_assoc. reflexivity.
Qed.

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

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.

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

Definition cand (N : Z) (j : nat) : Z := bottomup_floor + Z.of_nat j * (2 * N).

Definition zconflict (a n : Z) (p : word * word) : Prop :=
  a < bv_unsigned (fst p) + bv_unsigned (snd p) /\ bv_unsigned (fst p) < a + n.

Definition zconflictb (a n : Z) (p : word * word) : bool :=
  (a <? bv_unsigned (fst p) + bv_unsigned (snd p)) && (bv_unsigned (fst p) <? a + n).

