(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/openssl/bndiv/proofs/lib/Lib/LimSpec.v at commit 874e3397a35, with its module paths changed to libpcap/fuzz_pcap. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lim Require Import LimBase LimArms0 LimArms1 LimArms2 LimArms3 LimArms4 LimArms5 LimMm LimMmap LimMremap.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope sys_scope.

Definition mm_sysno (n : Z) : bool :=
  (n =? 214)%Z || (n =? 215)%Z || (n =? 216)%Z || (n =? 222)%Z || (n =? 226)%Z || (n =? 233)%Z.

Lemma lookup_arm_In : forall t n a, lookup_arm t n = Some a -> In a t /\ sa_no a = n.
Proof.
  induction t as [|x t IH]; intros n a H; [discriminate H|].
  cbn in H. destruct (Z.eqb (sa_no x) n) eqn:E.
  - injection H as <-. split; [left; reflexivity | apply Z.eqb_eq; exact E].
  - destruct (IH n a H) as [Hin Hno]. split; [right; exact Hin | exact Hno].
Qed.

Lemma spec_table_blind : Forall (fun a => mm_sysno (sa_no a) = false -> lim_blind (sa_spec a)) spec_table.
Proof.
  unfold spec_table.
  constructor; [intros _; exact arm_17|].
  constructor; [intros _; exact arm_19|].
  constructor; [intros _; exact arm_20|].
  constructor; [intros _; exact arm_21|].
  constructor; [intros _; exact arm_22|].
  constructor; [intros _; exact arm_23|].
  constructor; [intros _; exact arm_24|].
  constructor; [intros _; exact arm_25|].
  constructor; [intros _; exact arm_29|].
  constructor; [intros _; exact arm_32|].
  constructor; [intros _; exact arm_35|].
  constructor; [intros _; exact arm_46|].
  constructor; [intros _; exact arm_48|].
  constructor; [intros _; exact arm_56|].
  constructor; [intros _; exact arm_57|].
  constructor; [intros _; exact arm_59|].
  constructor; [intros _; exact arm_61|].
  constructor; [intros _; exact arm_62|].
  constructor; [intros _; exact arm_63|].
  constructor; [intros _; exact arm_64|].
  constructor; [intros _; exact arm_65|].
  constructor; [intros _; exact arm_66|].
  constructor; [intros _; exact arm_67|].
  constructor; [intros _; exact arm_68|].
  constructor; [intros _; exact arm_72|].
  constructor; [intros _; exact arm_73|].
  constructor; [intros _; exact arm_78|].
  constructor; [intros _; exact arm_79|].
  constructor; [intros _; exact arm_80|].
  constructor; [intros _; exact arm_82|].
  constructor; [intros _; exact arm_83|].
  constructor; [intros _; exact arm_85|].
  constructor; [intros _; exact arm_93|].
  constructor; [intros _; exact arm_94|].
  constructor; [intros _; exact arm_96|].
  constructor; [intros _; exact arm_98|].
  constructor; [intros _; exact arm_101|].
  constructor; [intros _; exact arm_113|].
  constructor; [intros _; exact arm_119|].
  constructor; [intros _; exact arm_123|].
  constructor; [intros _; exact arm_124|].
  constructor; [intros _; exact arm_130|].
  constructor; [intros _; exact arm_131|].
  constructor; [intros _; exact arm_132|].
  constructor; [intros _; exact arm_134|].
  constructor; [intros _; exact arm_135|].
  constructor; [intros _; exact arm_144|].
  constructor; [intros _; exact arm_146|].
  constructor; [intros _; exact arm_147|].
  constructor; [intros _; exact arm_149|].
  constructor; [intros _; exact arm_157|].
  constructor; [intros _; exact arm_158|].
  constructor; [intros _; exact arm_159|].
  constructor; [intros _; exact arm_160|].
  constructor; [intros _; exact arm_167|].
  constructor; [intros _; exact arm_169|].
  constructor; [intros _; exact arm_172|].
  constructor; [intros _; exact arm_174|].
  constructor; [intros _; exact arm_175|].
  constructor; [intros _; exact arm_176|].
  constructor; [intros _; exact arm_177|].
  constructor; [intros _; exact arm_178|].
  constructor; [intros _; exact arm_198|].
  constructor; [intros _; exact arm_199|].
  constructor; [intros _; exact arm_200|].
  constructor; [intros _; exact arm_201|].
  constructor; [intros _; exact arm_202|].
  constructor; [intros _; exact arm_203|].
  constructor; [intros _; exact arm_204|].
  constructor; [intros _; exact arm_205|].
  constructor; [intros _; exact arm_206|].
  constructor; [intros _; exact arm_207|].
  constructor; [intros _; exact arm_208|].
  constructor; [intros _; exact arm_209|].
  constructor; [intros _; exact arm_210|].
  constructor; [intros _; exact arm_211|].
  constructor; [intros _; exact arm_212|].
  constructor; [intros H; discriminate H|].
  constructor; [intros H; discriminate H|].
  constructor; [intros H; discriminate H|].
  constructor; [intros _; exact arm_220|].
  constructor; [intros H; discriminate H|].
  constructor; [intros H; discriminate H|].
  constructor; [intros H; discriminate H|].
  constructor; [intros _; exact arm_242|].
  constructor; [intros _; exact arm_260|].
  constructor; [intros _; exact arm_261|].
  constructor; [intros _; exact arm_278|].
  constructor; [intros _; exact arm_435|].
  constructor; [intros _; exact arm_439|].
  constructor.
Qed.

Lemma syscall_spec_blind : forall i m o,
  mm_sysno (bv_unsigned (in_sysno i)) = false ->
  syscall_spec i m o -> (forall L, syscall_spec i (setL L m) (omap L o)) /\ opres m o.
Proof.
  intros i m o Hn H. unfold syscall_spec, dispatch in *.
  destruct (lookup_arm spec_table (bv_unsigned (in_sysno i))) as [a|] eqn:E.
  - destruct (lookup_arm_In _ _ _ E) as [Hin Hno].
    pose proof (proj1 (Forall_forall _ _) spec_table_blind a Hin) as Hb. cbv beta in Hb. rewrite Hno in Hb.
    exact (Hb Hn i m o H).
  - exact (lim_blind_unmodeled i m o H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma within_limit_up : forall L X, (mlim X <= L)%Z -> vm_backing_within_limit X = true -> vm_backing_within_limit (setL L X) = true.
Proof.
  intros L X HL H. unfold vm_backing_within_limit in *. apply Z.leb_le in H. apply Z.leb_le.
  change (vm_backing_used (setL L X)) with (vm_backing_used X). change (vm_limit (m_vmmaps (setL L X))) with L.
  unfold mlim in HL. lia.
Qed.

Lemma brk_mark_up : forall L m req, (mlim m <= L)%Z ->
  brk_budget_refused_b m req = false -> brk_budget_refused_b (setL L m) req = false.
Proof.
  intros L m req HL H. unfold brk_budget_refused_b, min_brk in *. cbv zeta in *.
  change (m_vmmaps (setL L m)) with (setvl L (m_vmmaps m)).
  cbn [setvl vm_start_brk vm_brk].
  destruct (negb (w_is0 req || (bv_unsigned req <? bv_unsigned (vm_start_brk (m_vmmaps m)))%Z)
            && (0 <? bv_unsigned (vm_brk (m_vmmaps m)))%Z
            && (bv_unsigned (vm_brk (m_vmmaps m)) <? bv_unsigned req)%Z); [| reflexivity].
  cbn [andb] in *. apply negb_false_iff in H. apply negb_false_iff.
  unfold brk_budget_ok in *. cbv zeta in *. apply Z.leb_le in H. apply Z.leb_le.
  change (vm_backing_used (setL L m)) with (vm_backing_used m).
  change (vm_brk (m_vmmaps (setL L m))) with (vm_brk (m_vmmaps m)).
  change (vm_limit (m_vmmaps (setL L m))) with L. unfold mlim in HL. lia.
Qed.

Lemma mmap_noreserve_backed_ok_up : forall L flags m nZ, (mlim m <= L)%Z ->
  mmap_noreserve_backed_ok flags m nZ = true -> mmap_noreserve_backed_ok flags (setL L m) nZ = true.
Proof.
  intros L flags m nZ HL H. unfold mmap_noreserve_backed_ok in *.
  destruct (mmap_noreserve_b flags); [reflexivity|].
  apply Z.leb_le in H. apply Z.leb_le.
  change (vm_backing_used (setL L m)) with (vm_backing_used m). change (vm_limit (m_vmmaps (setL L m))) with L.
  unfold mlim in HL. lia.
Qed.
Lemma with_mmap_replacement_setL : forall L flags a n X, with_mmap_replacement flags a n (setL L X) = setL L (with_mmap_replacement flags a n X).
Proof. intros. unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma mlim_with_mmap_replacement : forall flags a n X, mlim (with_mmap_replacement flags a n X) = mlim X.
Proof. intros. unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma mmap_fixed_rw_budget_ok_up : forall L flags m addr n, (mlim m <= L)%Z ->
  mmap_fixed_rw_budget_ok flags m addr n = true -> mmap_fixed_rw_budget_ok flags (setL L m) addr n = true.
Proof.
  intros L flags m addr n HL H. unfold mmap_fixed_rw_budget_ok in *.
  change (with_vmmaps (mmap_fixed_rw_next (m_vmmaps (setL L m)) addr n) (setL L m))
    with (setL L (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr n) m)).
  rewrite with_mmap_replacement_setL. apply within_limit_up; [| exact H].
  rewrite mlim_with_mmap_replacement. exact HL.
Qed.
Lemma mmap_fixed_rw_span_budget_ok_up : forall L flags m addr n, (mlim m <= L)%Z ->
  mmap_fixed_rw_span_budget_ok flags m addr n = true -> mmap_fixed_rw_span_budget_ok flags (setL L m) addr n = true.
Proof.
  intros L flags m addr n HL H. unfold mmap_fixed_rw_span_budget_ok in *.
  change (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps (setL L m)) addr n) (setL L m))
    with (setL L (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps m) addr n) m)).
  rewrite with_mmap_replacement_setL. apply within_limit_up; [| exact H].
  rewrite mlim_with_mmap_replacement. exact HL.
Qed.

Lemma mmap_mark_up : forall L m addr len prot flags fd off, (mlim m <= L)%Z ->
  mmap_budget_refused_b addr len prot flags fd off m = false -> mmap_budget_refused_b addr len prot flags fd off (setL L m) = false.
Proof.
  intros L m addr len prot flags fd off HL. unfold mmap_budget_refused_b. cbv zeta.
  change (m_vmmaps (setL L m)) with (setvl L (m_vmmaps m)).
  change (alloc_top (setvl L (m_vmmaps m))) with (alloc_top (m_vmmaps m)).
  cbn [setvl vm_reserved vm_maps].
  set (nZ := page_round_up_Z (bv_unsigned len)). set (n := Z_to_bv 64 nZ). set (h := m_vmmaps m).
  repeat match goal with
  | |- (if ?b then _ else _) = false -> (if ?b then _ else _) = false => destruct b; [try (intros _; reflexivity)|]
  | |- false = false -> false = false => intros _; reflexivity
  end.
  all: try (intros _; reflexivity).
  all: intros H; apply negb_false_iff in H; apply negb_false_iff;
       first [ apply mmap_noreserve_backed_ok_up; assumption
             | apply mmap_fixed_rw_budget_ok_up; assumption
             | apply mmap_fixed_rw_span_budget_ok_up; assumption ].
Qed.

Lemma mprotect_mark_up : forall L m addr len prot, (mlim m <= L)%Z ->
  mprotect_budget_refused_b addr len prot m = false -> mprotect_budget_refused_b addr len prot (setL L m) = false.
Proof.
  intros L m addr len prot HL. unfold mprotect_budget_refused_b. cbv zeta.
  change (vm_noaccess (m_vmmaps (setL L m))) with (vm_noaccess (m_vmmaps m)).
  change (vm_maps (m_vmmaps (setL L m))) with (vm_maps (m_vmmaps m)).
  repeat match goal with
  | |- (if ?b then _ else _) = false -> (if ?b then _ else _) = false => destruct b; [try (intros _; reflexivity)|]
  end.
  all: try (intros _; reflexivity).
  intros H. apply negb_false_iff in H. apply negb_false_iff.
  unfold mprotect_budget_ok in *.
  change (mprotect_model_next (setL L m) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
    with (setL L (mprotect_model_next m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))).
  apply within_limit_up; [exact HL | exact H].
Qed.

Lemma mremap_mark_up : forall L m old old_size new_size flags, (mlim m <= L)%Z ->
  mremap_budget_refused_b old old_size new_size flags m = false -> mremap_budget_refused_b old old_size new_size flags (setL L m) = false.
Proof.
  intros L m old old_size new_size flags HL. unfold mremap_budget_refused_b. cbv zeta.
  change (mremap_source_b (m_vmmaps (setL L m))) with (mremap_source_b (m_vmmaps m)).
  change (mremap_backing_uniform_b (setL L m)) with (mremap_backing_uniform_b m).
  repeat match goal with
  | |- (if ?b then _ else _) = false -> (if ?b then _ else _) = false => destruct b; [try (intros _; reflexivity)|]
  end.
  all: try (intros _; reflexivity).
  intros H. apply negb_false_iff in H. apply negb_false_iff. apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split.
  - apply mremap_final_budget_b_up; assumption.
  - unfold mremap_move_budget_b in *. apply Z.leb_le in H2. apply Z.leb_le.
    change (mremap_move_charge (setL L m)) with (mremap_move_charge m). change (vm_limit (m_vmmaps (setL L m))) with L.
    unfold mlim in HL. lia.
Qed.

Lemma alloc_mark_up : forall L i m, (mlim m <= L)%Z ->
  alloc_budget_refused_b i m = false -> alloc_budget_refused_b i (setL L m) = false.
Proof.
  intros L i m HL. unfold alloc_budget_refused_b. cbv zeta.
  destruct (bv_unsigned (in_sysno i) =? 214)%Z; [apply brk_mark_up; exact HL|].
  destruct (bv_unsigned (in_sysno i) =? 216)%Z; [apply mremap_mark_up; exact HL|].
  destruct (bv_unsigned (in_sysno i) =? 222)%Z; [apply mmap_mark_up; exact HL|].
  destruct (bv_unsigned (in_sysno i) =? 226)%Z; [apply mprotect_mark_up; exact HL|].
  intros _. reflexivity.
Qed.

Lemma refusal_b_setL : forall L i m r, refusal_b i (setL L m) r = refusal_b i m r.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lookup_214 : lookup_arm spec_table 214 = Some (mkSpecArm 214 (fun i => brk_spec (in_arg i 0) i)).
Proof. reflexivity. Qed.
Lemma lookup_215 : lookup_arm spec_table 215 = Some (mkSpecArm 215 (fun i => munmap_spec (in_arg i 0) (in_arg i 1) i)).
Proof. reflexivity. Qed.
Lemma lookup_216 : lookup_arm spec_table 216 =
  Some (mkSpecArm 216 (fun i => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)).
Proof. reflexivity. Qed.
Lemma lookup_222 : lookup_arm spec_table 222 =
  Some (mkSpecArm 222 (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i)).
Proof. reflexivity. Qed.
Lemma lookup_226 : lookup_arm spec_table 226 =
  Some (mkSpecArm 226 (fun i => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)).
Proof. reflexivity. Qed.
Lemma lookup_233 : lookup_arm spec_table 233 =
  Some (mkSpecArm 233 (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i)).
Proof. reflexivity. Qed.

Lemma syscall_spec_214 : forall i m o, bv_unsigned (in_sysno i) = 214%Z ->
  (syscall_spec i m o <-> brk_spec (in_arg i 0) i m o).
Proof. intros i m o Hn. unfold syscall_spec, dispatch. rewrite Hn, lookup_214. reflexivity. Qed.
Lemma syscall_spec_215 : forall i m o, bv_unsigned (in_sysno i) = 215%Z ->
  (syscall_spec i m o <-> munmap_spec (in_arg i 0) (in_arg i 1) i m o).
Proof. intros i m o Hn. unfold syscall_spec, dispatch. rewrite Hn, lookup_215. reflexivity. Qed.
Lemma syscall_spec_216 : forall i m o, bv_unsigned (in_sysno i) = 216%Z ->
  (syscall_spec i m o <-> mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o).
Proof. intros i m o Hn. unfold syscall_spec, dispatch. rewrite Hn, lookup_216. reflexivity. Qed.
Lemma syscall_spec_222 : forall i m o, bv_unsigned (in_sysno i) = 222%Z ->
  (syscall_spec i m o <-> mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o).
Proof. intros i m o Hn. unfold syscall_spec, dispatch. rewrite Hn, lookup_222. reflexivity. Qed.
Lemma syscall_spec_226 : forall i m o, bv_unsigned (in_sysno i) = 226%Z ->
  (syscall_spec i m o <-> mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o).
Proof. intros i m o Hn. unfold syscall_spec, dispatch. rewrite Hn, lookup_226. reflexivity. Qed.
Lemma syscall_spec_233 : forall i m o, bv_unsigned (in_sysno i) = 233%Z ->
  (syscall_spec i m o <-> madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i m o).
Proof. intros i m o Hn. unfold syscall_spec, dispatch. rewrite Hn, lookup_233. reflexivity. Qed.

Lemma mark_214 : forall i m, bv_unsigned (in_sysno i) = 214%Z -> alloc_budget_refused_b i m = brk_budget_refused_b m (in_arg i 0).
Proof. intros i m Hn. unfold alloc_budget_refused_b. cbv zeta. rewrite Hn. reflexivity. Qed.
Lemma mark_216 : forall i m, bv_unsigned (in_sysno i) = 216%Z ->
  alloc_budget_refused_b i m = mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m.
Proof. intros i m Hn. unfold alloc_budget_refused_b. cbv zeta. rewrite Hn. reflexivity. Qed.
Lemma mark_222 : forall i m, bv_unsigned (in_sysno i) = 222%Z ->
  alloc_budget_refused_b i m = mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m.
Proof. intros i m Hn. unfold alloc_budget_refused_b. cbv zeta. rewrite Hn. reflexivity. Qed.
Lemma mark_226 : forall i m, bv_unsigned (in_sysno i) = 226%Z ->
  alloc_budget_refused_b i m = mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) m.
Proof. intros i m Hn. unfold alloc_budget_refused_b. cbv zeta. rewrite Hn. reflexivity. Qed.

(* [comment removed for export] *)
Theorem syscall_spec_at : forall L i m,
  alloc_budget_refused_b i m = false ->
  alloc_budget_refused_b i (setL L m) = false ->
  (bv_unsigned (in_sysno i) = 216%Z -> (mlim m <= L)%Z) ->
  lim_at L i m syscall_spec syscall_spec.
Proof.
  intros L i m R1 R2 H216 o Ho.
  destruct (mm_sysno (bv_unsigned (in_sysno i))) eqn:E.
  - unfold mm_sysno in E.
    repeat (apply orb_true_iff in E; destruct E as [E|E]); apply Z.eqb_eq in E.
    + rewrite (mark_214 _ _ E) in R1. rewrite (mark_214 _ _ E) in R2. apply (syscall_spec_214 _ _ _ E) in Ho.
      destruct (brk_at L i m _ R1 R2 o Ho) as [Ha Hb]. split; [apply (syscall_spec_214 _ _ _ E); exact Ha | exact Hb].
    + apply (syscall_spec_215 _ _ _ E) in Ho.
      destruct (munmap_at L i m _ _ o Ho) as [Ha Hb]. split; [apply (syscall_spec_215 _ _ _ E); exact Ha | exact Hb].
    + rewrite (mark_216 _ _ E) in R1. apply (syscall_spec_216 _ _ _ E) in Ho.
      destruct (mremap_at_up L i m _ _ _ _ (H216 E) R1 o Ho) as [Ha Hb]. split; [apply (syscall_spec_216 _ _ _ E); exact Ha | exact Hb].
    + rewrite (mark_222 _ _ E) in R1. rewrite (mark_222 _ _ E) in R2. apply (syscall_spec_222 _ _ _ E) in Ho.
      destruct (mmap_at L i m _ _ _ _ _ _ R1 R2 o Ho) as [Ha Hb]. split; [apply (syscall_spec_222 _ _ _ E); exact Ha | exact Hb].
    + rewrite (mark_226 _ _ E) in R1. rewrite (mark_226 _ _ E) in R2. apply (syscall_spec_226 _ _ _ E) in Ho.
      destruct (mprotect_at L i m _ _ _ R1 R2 o Ho) as [Ha Hb]. split; [apply (syscall_spec_226 _ _ _ E); exact Ha | exact Hb].
    + apply (syscall_spec_233 _ _ _ E) in Ho.
      destruct (madvise_at L i m _ _ _ o Ho) as [Ha Hb]. split; [apply (syscall_spec_233 _ _ _ E); exact Ha | exact Hb].
  - destruct (syscall_spec_blind i m o E Ho) as [Ha Hb]. split; [apply Ha | exact Hb].
Qed.

(* [comment removed for export] *)
Corollary syscall_spec_up : forall L i m o,
  (mlim m <= L)%Z -> alloc_budget_refused_b i m = false ->
  syscall_spec i m o -> syscall_spec i (setL L m) (omap L o) /\ opres m o.
Proof.
  intros L i m o HL R Ho.
  exact (syscall_spec_at L i m R (alloc_mark_up L i m HL R) (fun _ => HL) o Ho).
Qed.

(* [comment removed for export] *)
Corollary syscall_spec_down : forall L i m o,
  (L <= mlim m)%Z -> alloc_budget_refused_b i (setL L m) = false ->
  bv_unsigned (in_sysno i) <> 216%Z ->
  syscall_spec i m o -> syscall_spec i (setL L m) (omap L o) /\ opres m o.
Proof.
  intros L i m o HL R Hn Ho.
  assert (R1 : alloc_budget_refused_b i m = false).
  { rewrite <- (setL_id m). rewrite <- (setL_setL L (mlim m) m). apply alloc_mark_up; [rewrite mlim_setL; exact HL | exact R]. }
  exact (syscall_spec_at L i m R1 R (fun E => False_ind _ (Hn E)) o Ho).
Qed.

(* [comment removed for export] *)
Lemma mremap_has_outcome : forall old old_size new_size flags i m, exists o, mremap_spec old old_size new_size flags i m o.
Proof.
  intros old old_size new_size flags i m. unfold mremap_spec.
  destruct (negb (bv_unsigned flags =? MREMAP_MAYMOVE)%Z); [exists Unmodeled; reflexivity|].
  destruct (negb (bv_unsigned old mod page_size =? 0)%Z); [eexists; unfold err_ret, ret_only; reflexivity|].
  destruct (page_align_is0_b new_size); [eexists; unfold err_ret, ret_only; reflexivity|].
  destruct (page_align_is0_b old_size); [exists Unmodeled; reflexivity|].
  cbv zeta.
  match goal with |- exists o, bind get_model ?k i m o => 
    assert (H : exists o, k m i m o); [| destruct H as [o H]; exists o; apply bind_get_model; exact H] end.
  cbv beta.
  match goal with |- context [if ?b then _ else _] => destruct b end; [exists Unmodeled; reflexivity|].
  match goal with |- context [if ?b then _ else _] => destruct b end; [eexists; unfold ret_only; reflexivity|].
  exists (Ok (mkEffect (errno_ret ENOMEM) [] []) m []). left.
  exists ENOMEM, m, [], []. split; [exists ENOMEM; split; [left; reflexivity | reflexivity] |]. split; [unfold err_ret, ret_only; reflexivity | reflexivity].
Qed.

Lemma syscall_spec_216_has_outcome : forall i m, bv_unsigned (in_sysno i) = 216%Z -> exists o, syscall_spec i m o.
Proof.
  intros i m E. destruct (mremap_has_outcome (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m) as [o Ho].
  exists o. apply (syscall_spec_216 _ _ _ E). exact Ho.
Qed.
