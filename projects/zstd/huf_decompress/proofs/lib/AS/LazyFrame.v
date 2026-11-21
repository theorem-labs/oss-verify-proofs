(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (11 recorded proofs replaced by written proofs (filter_all_false, with_vm_backing_id, materialize_accesses_no_new and 8 more)). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import DivergeSim.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_LazyFrame () := "C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List6filterI47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2or02I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01C47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathI4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00K4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00K47Corelib7Numbers7BinNums8positive03C4ELinuxProcessSemantics?LinuxProcessSem5StateHnewly_materialized_pagesI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes3appK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem5StateDmaterialize_accessesI47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC4ELinuxProcessSemantics?LinuxProcessSem5State;page_insertC4ELinuxProcessSemantics?LinuxProcessSem5State8page_memC47Corelib4Init5Logic6eq_symK47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofK47Corelib4Init9Datatypes3nat02c59OSSVerify5KrLib2AS9LazyFrame>page_insert_inC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C47Corelib4Init9Datatypes7nat_indC4ELinuxProcessSemantics?LinuxProcessSem5State@access_pages_accI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses6mkapp2C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201C4ELinuxProcessSemantics?LinuxProcessSem5State>accesses_pagesC45stdpp9bitvector;definitions;bv_unsignedc59OSSVerify5KrLib2AS9LazyFrameCaccess_pages_acc_inC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib2AS9LazyFrameDaccess_outside_rangeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List>existsb_existsC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02C56Stdlib6ZArith6BinInt1Z7div_posC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3divK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr07C45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula03C46Stdlib4Bool4BoolAnot_true_is_falseK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init5Logic4True00K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib2AS9LazyFrameEaccesses_outside_lazyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9LazyFrameAaccesses_pages_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9LazyFrameFpage_in_ranges_outsideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9LazyFrame@filter_all_falseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9LazyFrameBwith_vm_backing_idC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitc59OSSVerify5KrLib2AS9LazyFrameKmaterialize_accesses_no_newC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC47Corelib4Init9Datatypes4negbI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02c59OSSVerify5KrLib2AS9LazyFrameSmaterialize_model_accesses_disjointC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepC59OSSVerify5KrLib2AS:DivergeSimKmi_account_step_of_accessesC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingc59OSSVerify5KrLib2AS9LazyFrameHmi_account_step_disjointC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:DivergeSim7to_spin01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS:DivergeSim7to_spin00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:DivergeSim7to_spin02C1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition access_outside_range (a : word) (n : nat) (lo sz : word) : Prop :=
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z /\
  (bv_unsigned a + Z.of_nat n <= bv_unsigned lo
   \/ bv_unsigned lo + bv_unsigned sz <= bv_unsigned a)%Z.

(* [comment removed for export] *)
Definition accesses_outside_lazy
    (accs : list (word * nat)) (lazy : list (word * word)) : Prop :=
  forall a n lo sz, In (a, n) accs -> In (lo, sz) lazy ->
    access_outside_range a n lo sz.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma filter_all_false {A} : forall (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = false) -> List.filter f l = [].
Proof.
  intros f l H; induction l as [|x l IH]; cbn; [reflexivity|].
  rewrite (H x (or_introl eq_refl)).
  apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

(* [comment removed for export] *)
Lemma with_vm_backing_id : forall m,
  with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof.
  intros [fd [maps lazy materialized] io fs proc lim tm]. reflexivity.
Qed.

Lemma materialize_accesses_no_new : forall lazy materialized used limit accs,
  newly_materialized_pages lazy materialized accs = [] ->
  materialize_accesses lazy materialized used limit accs = Some materialized.
Proof.
  intros lazy materialized used limit accs Hnew.
  unfold materialize_accesses. rewrite Hnew. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_insert_in : forall p q pages,
  In p (page_insert q pages) -> p = q \/ In p pages.
Proof.
  intros p q pages H. unfold page_insert in H.
  destruct (page_mem q pages); [right; exact H|].
  destruct H as [Hqp | H]; [left; symmetry; exact Hqp | right; exact H].
Qed.

(* [comment removed for export] *)
Lemma access_pages_acc_in : forall n base pages p,
  In p (access_pages_acc base n pages) ->
  In p pages
  \/ exists k, (k < n)%nat /\ p = page_base_of (base + Z.of_nat k)%Z.
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p H.
  - left; exact H.
  - destruct (IH (base + 1)%Z _ p H) as [Hin | (k & Hk & ->)].
    + destruct (page_insert_in _ _ _ Hin) as [-> | Hin'].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin'.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : forall accs pages p,
  In p (accesses_pages accs pages) ->
  In p pages
  \/ exists a n k, In (a, n) accs /\ (k < n)%nat /\
                   p = page_base_of (bv_unsigned a + Z.of_nat k)%Z.
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages];
    intros pages p H.
  - left; exact H.
  - destruct (IH _ p H) as [Hin | (a' & n' & k & Hin & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin)
        as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k.
        split; [left; reflexivity | split; assumption].
    + right. exists a', n', k.
      split; [right; exact Hin | split; assumption].
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_outside : forall lazy (a : word) (n k : nat),
  (k < n)%nat ->
  (forall lo sz, In (lo, sz) lazy -> access_outside_range a n lo sz) ->
  page_in_ranges (page_base_of (bv_unsigned a + Z.of_nat k)) lazy = false.
Proof.
  intros lazy a n k Hk Hout.
  set (z := (bv_unsigned a + Z.of_nat k)%Z).
  apply Bool.not_true_is_false. intro Htrue.
  unfold page_in_ranges in Htrue.
  apply existsb_exists in Htrue.
  destruct Htrue as ([lo sz] & Hin & Htest).
  cbn [fst snd] in Htest.
  apply andb_true_iff in Htest. destruct Htest as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  destruct (Hout lo sz Hin) as [Hnw Hdisj].
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  pose proof (bv_unsigned_in_range 64 lo) as Hlo_rg.
  pose proof (bv_unsigned_in_range 64 sz) as Hsz_rg.
  assert (Hz0 : (0 <= z)%Z) by (unfold z; lia).
  (* [comment removed for export] *)
  assert (Hq0 : (0 <= z / page_size)%Z)
    by (apply Z.div_pos; [exact Hz0 | unfold page_size; lia]).
  pose proof (Z.div_mod z page_size
                ltac:(unfold page_size; lia)) as Hdm.
  pose proof (Z.mod_pos_bound z page_size
                ltac:(unfold page_size; lia)) as Hmb.
  assert (Hpb : bv_unsigned (page_base_of z)
                = ((z / page_size) * page_size)%Z).
  { unfold page_base_of. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    change (bv_modulus 64) with (2 ^ 64)%Z.
    unfold page_size in *. unfold z in *. lia. }
  rewrite Hpb in Hlo, Hhi.
  (* [comment removed for export] *)
  unfold page_size in *. unfold z in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem materialize_model_accesses_disjoint : forall m accs,
  accesses_outside_lazy accs (m_vm_lazy m) ->
  materialize_model_accesses m accs = Some m.
Proof.
  intros m accs Hout.
  assert (Hnew : newly_materialized_pages
                   (m_vm_lazy m) (m_vm_materialized m) accs = []).
  { unfold newly_materialized_pages. apply filter_all_false.
    intros p Hp.
    destruct (accesses_pages_in accs [] p Hp)
      as [[] | (a & n & k & Hin & Hk & ->)].
    rewrite (page_in_ranges_outside (m_vm_lazy m) a n k Hk).
    - reflexivity.
    - intros lo sz Hlz. exact (Hout a n lo sz Hin Hlz). }
  unfold materialize_model_accesses.
  rewrite (materialize_accesses_no_new (m_vm_lazy m) (m_vm_materialized m)
             (vm_backing_used m) (vm_limit (m_vmmaps m)) accs Hnew).
  cbv iota beta.
  rewrite with_vm_backing_id. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mi_account_step_disjoint : forall segs ms model ms' ranges,
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  mi_account_step segs ms model = MachineOk (ms', model).
Proof.
  intros segs ms model ms' ranges Hstep Hout.
  rewrite (mi_account_step_of_accesses segs ms model ms' ranges Hstep).
  rewrite (materialize_model_accesses_disjoint model ranges Hout).
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ts_spin_disjoint : forall segs ms model ranges,
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  to_spin segs ms model.
Proof.
  intros segs ms model ranges Hsvc Hstep Hout.
  apply ts_spin; [exact Hsvc|].
  exact (mi_account_step_disjoint segs ms model ms ranges Hstep Hout).
Qed.

(* [comment removed for export] *)
Lemma ts_step_disjoint : forall segs ms model ms' ranges,
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  to_spin segs ms' model ->
  to_spin segs ms model.
Proof.
  intros segs ms model ms' ranges Hsvc Hstep Hout Hspin.
  exact (ts_step segs ms model ms' model Hsvc
           (mi_account_step_disjoint segs ms model ms' ranges Hstep Hout)
           Hspin).
Qed.
