(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (49 recorded proofs replaced by written proofs (filter_true, filter_and, filter_length_le and 46 more); brk_r_ok_X, check_brk_X, check_mmap_X restated for the revision's model; check_mprotect_X re-proved). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import AcctCore ModelX.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Placement.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MmXfer () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List6filterI47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4bool01C47Corelib4Init9Datatypes4andbI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith4Znat5Nat2Z8inj_succI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03C46Stdlib5Lists4List7existsbI46Stdlib5Lists4List5NoDup00C46Stdlib5Lists4List<NoDup_filterC46Stdlib5Lists4List4inclC46Stdlib5Lists4List2InI47Corelib4Init5Logic3and00C46Stdlib5Lists4List9filter_InC47Corelib4Init5Logic7and_indC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01c59OSSVerify5KrLib4LibA6MmXfer4relXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ModelX5stripC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4LibA6ModelX2MXC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic9False_indI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03C47Corelib4Init5Logic3iffC47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00c59OSSVerify5KrLib4LibA6MmXfer:strip_selfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXfer;filter_trueC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbc59OSSVerify5KrLib4LibA6MmXfer7relX_idC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAwith_mmap_backingI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCwith_mmap_destroyedC45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangec59OSSVerify5KrLib4LibA6MmXferDwith_mmap_backing_MXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ModelXBvm_forget_range_MXC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEwith_mmap_replacementc59OSSVerify5KrLib4LibA6MmXferEmat_with_mmap_backingC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferHvmmaps_with_mmap_backingC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectCmprotect_model_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseEmadvise_dontneed_nextC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingC59OSSVerify5KrLib4LibA6ModelX6MX_matC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@forget_vm_rangesc59OSSVerify5KrLib4LibA6MmXfer;ranges_keepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXfer:filter_andC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>brk_model_nextc59OSSVerify5KrLib4LibA6MmXferCforget_vm_ranges_MXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ModelX>with_vmmaps_MXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ModelX;m_vmmaps_MXC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap=with_brk_nextC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap:brk_unmapsc59OSSVerify5KrLib4LibA6MmXfer6robustC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3lebC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula09C46Stdlib4Bool4Bool>eq_true_iff_eqK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4LibA8AcctCore=nonlazy_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC59OSSVerify5KrLib4LibA8AcctCoreEvm_backing_used_splitC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib4LibA6MmXfer@filter_length_leC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitc59OSSVerify5KrLib4LibA6MmXfer9mat_boundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXfer:robust_lebC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferEvm_backing_used_canonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ModelXBvm_backing_used_MXC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateGvm_backing_within_limitc59OSSVerify5KrLib4LibA6MmXfer:mat_bound0C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextc59OSSVerify5KrLib4LibA6MmXferImat_with_mmap_replacementC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferLvmmaps_with_mmap_replacementC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferFbacking_within_limit_XC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferHwith_mmap_replacement_MXC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapLmmap_fixed_rw_span_budget_okc59OSSVerify5KrLib4LibA6MmXferFmprotect_model_next_MXC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_budget_okC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap7min_brkC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes3orbC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z:ltb_irreflC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap8brk_r_okC45stdpp9bitvector;definitions6bv_subC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freec59OSSVerify5KrLib4LibA6MmXferGstrip_with_mmap_backingC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:listNN_eqbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>munmap_free_okC4ELinuxProcessSemantics?LinuxProcessSem5State:map_removec59OSSVerify5KrLib4LibA6MmXfer=relX_ret_onlyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferIstrip_with_mmap_destroyedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXfer;relX_filterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferFwith_mmap_destroyed_MXC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap<check_munmapC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALC4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseBmadvise_dontneed_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseCmadvise_dontneed_okc59OSSVerify5KrLib4LibA6MmXferHmadvise_dontneed_next_MXC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm7Madvise=check_madviseC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectImprotect_grows_conflict_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_modeled_bC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<errno_ret_inc59OSSVerify5KrLib4LibA6MmXfer9relX_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferDmprotect_budget_ok_XC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm8Mprotect>check_mprotectC4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8Mprotect?mprotect_errnosC4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retc59OSSVerify5KrLib4LibA6MmXfer@with_brk_next_MXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferFforget_vm_ranges_stripC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXfer:brk_r_ok_XC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap9check_brkC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap9brk_zerosC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_off_aligned_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_pglen_ok_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_anon_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAmmap_plain_anon_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>mmap_modeled_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEmmap_fixed_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_fixed_rw_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_noreplace_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCmmap_noreplace_rw_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_fixed_destroyed_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapMmmap_fixed_noaccess_span_nextc59OSSVerify5KrLib4LibA6MmXferKstrip_with_mmap_replacementC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferIfixed_rw_span_budget_ok_XC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferDfixed_rw_budget_ok_XC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferEnoreserve_backed_ok_XC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap:check_mmapc59OSSVerify5KrLib4LibA6MmXferAstrip_with_vmmapsC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_errnosC4ELinuxProcessSemantics?LinuxProcessSem5State6EEXIST".
(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma filter_true : forall {A} (l : list A), List.filter (fun _ => true) l = l.
Proof. induction l; cbn; congruence. Qed.

Lemma filter_and : forall {A} (f g : A -> bool) (l : list A),
  List.filter f (List.filter g l) = List.filter (fun a => g a && f a) l.
Proof.
  induction l as [|x l IH]; cbn; [reflexivity|].
  destruct (g x); cbn; [|exact IH]. destruct (f x); cbn; congruence.
Qed.

Lemma filter_length_le : forall {A} (f : A -> bool) (l : list A), (length (List.filter f l) <= length l)%nat.
Proof. induction l as [|x l IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.

Lemma NoDup_filter' : forall {A} (f : A -> bool) (l : list A), List.NoDup l -> List.NoDup (List.filter f l).
Proof. intros. apply NoDup_filter. assumption. Qed.

Lemma incl_filter : forall {A} (f : A -> bool) (l : list A), List.incl (List.filter f l) l.
Proof. intros A f l x Hx. apply filter_In in Hx. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition relX (mo : Model) (mat : list word) (rX r : check_result) : Prop :=
  match rX, r with
  | CheckOk mX eX, CheckOk m e =>
      eX = e /\ strip m = with_vmmaps (m_vmmaps m) (strip mo) /\
      exists f, mX = MX m (List.filter f mat) /\ m_vm_materialized m = List.filter f (m_vm_materialized mo)
  | CheckReject, CheckReject => True
  | CheckUnmodeled, CheckUnmodeled => True
  | _, _ => False
  end.

(* [comment removed for export] *)
Lemma relX_ok_l : forall mo mat mX eX r,
  relX mo mat (CheckOk mX eX) r ->
  exists m f, r = CheckOk m eX /\ strip m = with_vmmaps (m_vmmaps m) (strip mo) /\
              mX = MX m (List.filter f mat) /\ m_vm_materialized m = List.filter f (m_vm_materialized mo).
Proof. intros mo mat mX eX [m e| |] H; cbn in H; try contradiction. destruct H as (-> & S & f & A & B). eauto 6. Qed.

Lemma relX_ok_r : forall mo mat rX m e,
  relX mo mat rX (CheckOk m e) ->
  strip m = with_vmmaps (m_vmmaps m) (strip mo) /\
  exists f, rX = CheckOk (MX m (List.filter f mat)) e /\ m_vm_materialized m = List.filter f (m_vm_materialized mo).
Proof. intros mo mat [mX eX| |] m e H; cbn in H; try contradiction. destruct H as (-> & S & f & -> & B). eauto. Qed.

Lemma relX_unmodeled : forall mo mat rX r, relX mo mat rX r -> (rX = CheckUnmodeled <-> r = CheckUnmodeled).
Proof. intros mo mat [| |] [| |] H; cbn in H; try contradiction; split; congruence. Qed.

(* [comment removed for export] *)
Lemma strip_self : forall mo, strip mo = with_vmmaps (m_vmmaps mo) (strip mo).
Proof. intros mo. reflexivity. Qed.

Lemma relX_id : forall mo mat e, relX mo mat (CheckOk (MX mo mat) e) (CheckOk mo e).
Proof.
  intros mo mat e. cbn. split; [reflexivity|]. split; [apply strip_self|]. exists (fun _ => true). rewrite !filter_true. auto.
Qed.

Lemma relX_filter : forall mo mat m f e,
  strip m = with_vmmaps (m_vmmaps m) (strip mo) ->
  m_vm_materialized m = List.filter f (m_vm_materialized mo) ->
  relX mo mat (CheckOk (MX m (List.filter f mat)) e) (CheckOk m e).
Proof. intros mo mat m f e S H. cbn. split; [reflexivity|]. split; [exact S|]. exists f. auto. Qed.

Lemma relX_same : forall mo mat m e,
  strip m = with_vmmaps (m_vmmaps m) (strip mo) ->
  m_vm_materialized m = m_vm_materialized mo ->
  relX mo mat (CheckOk (MX m mat) e) (CheckOk m e).
Proof.
  intros mo mat m e S H. cbn. split; [reflexivity|]. split; [exact S|]. exists (fun _ => true). rewrite !filter_true. auto.
Qed.

Lemma relX_reject : forall mo mat, relX mo mat CheckReject CheckReject.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h03math12mop;1g00DLj10Tg00V9j13Tg00VWj12Tg004kj11Tg00_Ag00OE#0#0#0#0#0#0#3#2#1g00e@W0W1o"). Qed.
Lemma relX_unm : forall mo mat, relX mo mat CheckUnmodeled CheckUnmodeled.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h03math12mop;1g00DLj10Tg00V9j13Tg00VWj12Tg004kj11Tg00_Ag00OE#0#0#0#0#0#0#3#2#1g00e@W0W1o"). Qed.

Lemma relX_ret_only : forall mo mat eff r e,
  relX mo mat (check_ret_only eff r (MX mo mat) e) (check_ret_only eff r mo e).
Proof.
  intros mo mat [ret ws zs us cs ci] r e. unfold check_ret_only.
  destruct ws; [|exact I]. destruct zs; [|exact I]. destruct us; [|exact I]. destruct cs; [|exact I]. destruct ci; [|exact I].
  destruct (bv_eqb ret r); [apply relX_id| exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_mmap_backing_MX : forall flags a n m mat,
  with_mmap_backing flags a n (MX m mat) = MX (with_mmap_backing flags a n m) mat.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma mat_with_mmap_backing : forall flags a n m,
  m_vm_materialized (with_mmap_backing flags a n m) = m_vm_materialized m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma vmmaps_with_mmap_backing : forall flags a n m,
  m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma with_mmap_destroyed_MX : forall a n h m mat,
  with_mmap_destroyed a n h (MX m mat) =
  MX (with_mmap_destroyed a n h m) (List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) mat).
Proof. intros. reflexivity. Qed.

Lemma mat_with_mmap_destroyed : forall a n h m,
  m_vm_materialized (with_mmap_destroyed a n h m) =
  List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m).
Proof. intros. reflexivity. Qed.

Lemma with_mmap_replacement_MX : forall flags a n m mat,
  with_mmap_replacement flags a n (MX m mat) =
  MX (with_mmap_replacement flags a n m) (List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) mat).
Proof. intros. unfold with_mmap_replacement. rewrite vm_forget_range_MX. apply with_mmap_backing_MX. Qed.

Lemma mat_with_mmap_replacement : forall flags a n m,
  m_vm_materialized (with_mmap_replacement flags a n m) =
  List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m).
Proof. intros. unfold with_mmap_replacement. rewrite mat_with_mmap_backing. reflexivity. Qed.

Lemma vmmaps_with_mmap_replacement : forall flags a n m,
  m_vmmaps (with_mmap_replacement flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_replacement. rewrite vmmaps_with_mmap_backing. reflexivity. Qed.

Lemma mprotect_model_next_MX : forall m mat a n,
  mprotect_model_next (MX m mat) a n = MX (mprotect_model_next m a n) mat.
Proof. intros. reflexivity. Qed.

Lemma mat_mprotect_model_next : forall m a n, m_vm_materialized (mprotect_model_next m a n) = m_vm_materialized m.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma madvise_dontneed_next_MX : forall m mat a n,
  madvise_dontneed_next (MX m mat) a n =
  MX (madvise_dontneed_next m a n) (List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) mat).
Proof. intros. reflexivity. Qed.

Lemma mat_madvise_dontneed_next : forall m a n,
  m_vm_materialized (madvise_dontneed_next m a n) =
  List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m).
Proof. intros. reflexivity. Qed.

Lemma vmmaps_madvise_dontneed_next : forall m a n, m_vmmaps (madvise_dontneed_next m a n) = m_vmmaps m.
Proof. intros. reflexivity. Qed.

Lemma madvise_dontneed_next_canon : forall m a n,
  m_vm_materialized m = [] -> madvise_dontneed_next m a n = m.
Proof.
  intros m a n H. unfold madvise_dontneed_next. rewrite H. cbn [List.filter].
  rewrite <- H. apply (MX_mat m).
Qed.

(* [comment removed for export] *)
Fixpoint ranges_keep (ranges : list (word * word)) (p : word) : bool :=
  match ranges with
  | [] => true
  | (a, n) :: rest => page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) p && ranges_keep rest p
  end.

Lemma forget_vm_ranges_MX : forall l m mat,
  forget_vm_ranges l (MX m mat) = MX (forget_vm_ranges l m) (List.filter (ranges_keep l) mat)
  /\ m_vm_materialized (forget_vm_ranges l m) = List.filter (ranges_keep l) (m_vm_materialized m)
  /\ m_vmmaps (forget_vm_ranges l m) = m_vmmaps m.
Proof.
  induction l as [|[a n] l IH]; intros m mat; cbn [forget_vm_ranges ranges_keep].
  - rewrite !filter_true. repeat split; reflexivity.
  - rewrite vm_forget_range_MX.
    destruct (IH (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m)
                 (List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) mat)) as (E1 & E2 & E3).
    rewrite E1, E2, E3, !filter_and.
    change (m_vm_materialized (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m))
      with (List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m)).
    rewrite filter_and. repeat split; reflexivity.
Qed.

Lemma forget_vm_ranges_strip : forall l m,
  strip (forget_vm_ranges l m) = with_vmmaps (m_vmmaps (forget_vm_ranges l m)) (strip m).
Proof.
  induction l as [|[a n] l IH]; intros m; cbn [forget_vm_ranges].
  - apply strip_self.
  - rewrite IH. reflexivity.
Qed.

Lemma with_brk_next_MX : forall m mat req r,
  with_brk_next (MX m mat) req r = MX (with_brk_next m req r) (List.filter (ranges_keep (brk_unmaps r (vm_brk (m_vmmaps m)))) mat)
  /\ m_vm_materialized (with_brk_next m req r) =
       List.filter (ranges_keep (brk_unmaps r (vm_brk (m_vmmaps m)))) (m_vm_materialized m).
Proof.
  intros m mat req r. unfold with_brk_next. rewrite m_vmmaps_MX, with_vmmaps_MX.
  destruct (forget_vm_ranges_MX (brk_unmaps r (vm_brk (m_vmmaps m))) (with_vmmaps (brk_model_next (m_vmmaps m) req r) m) mat)
    as (E1 & E2 & _).
  rewrite E1, E2. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Slack.
Variable NMAX : nat.

Definition robust (x lim : Z) : Prop := x + Z.of_nat NMAX * page_size <= lim \/ lim < x.

Lemma robust_leb : forall x lim d, robust x lim -> 0 <= d <= Z.of_nat NMAX * page_size ->
  (x + d <=? lim) = (x <=? lim).
Proof. intros x lim d [H|H] Hd; apply eq_true_iff_eq; rewrite !Z.leb_le; lia. Qed.

Lemma vm_backing_used_canon : forall m, m_vm_materialized m = [] -> vm_backing_used m = nonlazy_bytes m.
Proof. intros m H. rewrite vm_backing_used_split, H. cbn. lia. Qed.

Lemma mat_bound : forall (mat : list word) f, (length mat <= NMAX)%nat ->
  0 <= Z.of_nat (length (List.filter f mat)) * page_size <= Z.of_nat NMAX * page_size.
Proof. intros mat f H. pose proof (filter_length_le f mat). unfold page_size. nia. Qed.

Lemma mat_bound0 : forall (mat : list word), (length mat <= NMAX)%nat ->
  0 <= Z.of_nat (length mat) * page_size <= Z.of_nat NMAX * page_size.
Proof. intros mat H. unfold page_size. nia. Qed.

(* [comment removed for export] *)
Lemma backing_within_limit_X : forall m' mat f,
  m_vm_materialized m' = [] -> (length mat <= NMAX)%nat ->
  robust (nonlazy_bytes m') (vm_limit (m_vmmaps m')) ->
  vm_backing_within_limit (MX m' (List.filter f mat)) = vm_backing_within_limit m'.
Proof.
  intros m' mat f CAN LEN R. unfold vm_backing_within_limit.
  rewrite vm_backing_used_MX, m_vmmaps_MX, (vm_backing_used_canon m' CAN).
  apply robust_leb; [exact R| apply mat_bound; exact LEN].
Qed.

Lemma noreserve_backed_ok_X : forall flags mo mat nZ,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  (mmap_noreserve_b flags = true \/ robust (nonlazy_bytes mo + nZ) (vm_limit (m_vmmaps mo))) ->
  mmap_noreserve_backed_ok flags (MX mo mat) nZ = mmap_noreserve_backed_ok flags mo nZ.
Proof.
  intros flags mo mat nZ CAN LEN R. unfold mmap_noreserve_backed_ok.
  destruct (mmap_noreserve_b flags) eqn:E; [reflexivity|].
  destruct R as [R|R]; [congruence|].
  rewrite vm_backing_used_MX, m_vmmaps_MX, (vm_backing_used_canon mo CAN).
  replace (nonlazy_bytes mo + Z.of_nat (length mat) * page_size + nZ) with (nonlazy_bytes mo + nZ + Z.of_nat (length mat) * page_size) by lia.
  apply robust_leb; [exact R| apply mat_bound0; exact LEN].
Qed.

Lemma fixed_rw_budget_ok_X : forall flags mo mat addr n,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  robust (nonlazy_bytes (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) addr n) mo)))
         (vm_limit (m_vmmaps mo)) ->
  mmap_fixed_rw_budget_ok flags (MX mo mat) addr n = mmap_fixed_rw_budget_ok flags mo addr n.
Proof.
  intros flags mo mat addr n CAN LEN R. unfold mmap_fixed_rw_budget_ok.
  rewrite m_vmmaps_MX, with_vmmaps_MX, with_mmap_replacement_MX.
  apply backing_within_limit_X.
  - rewrite mat_with_mmap_replacement. change (m_vm_materialized (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) addr n) mo)) with (m_vm_materialized mo).
    rewrite CAN. reflexivity.
  - exact LEN.
  - rewrite vmmaps_with_mmap_replacement. exact R.
Qed.

(* [comment removed for export] *)
Lemma fixed_rw_span_budget_ok_X : forall flags mo mat addr n,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  robust (nonlazy_bytes (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps mo) addr n) mo)))
         (vm_limit (m_vmmaps mo)) ->
  mmap_fixed_rw_span_budget_ok flags (MX mo mat) addr n = mmap_fixed_rw_span_budget_ok flags mo addr n.
Proof.
  intros flags mo mat addr n CAN LEN R. unfold mmap_fixed_rw_span_budget_ok.
  rewrite m_vmmaps_MX, with_vmmaps_MX, with_mmap_replacement_MX.
  apply backing_within_limit_X.
  - rewrite mat_with_mmap_replacement. change (m_vm_materialized (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps mo) addr n) mo)) with (m_vm_materialized mo).
    rewrite CAN. reflexivity.
  - exact LEN.
  - rewrite vmmaps_with_mmap_replacement. exact R.
Qed.

Lemma mprotect_budget_ok_X : forall mo mat addr n,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  robust (nonlazy_bytes (mprotect_model_next mo addr n)) (vm_limit (m_vmmaps mo)) ->
  mprotect_budget_ok (MX mo mat) addr n = mprotect_budget_ok mo addr n.
Proof.
  intros mo mat addr n CAN LEN R. unfold mprotect_budget_ok. rewrite mprotect_model_next_MX.
  rewrite <- (filter_true mat). apply backing_within_limit_X; [exact CAN| exact LEN| exact R].
Qed.

Lemma brk_r_ok_X : forall mo mat req r,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  robust (nonlazy_bytes mo + brk_grow_bytes (m_vmmaps mo) req) (vm_limit (m_vmmaps mo)) ->
  brk_r_ok (MX mo mat) req r = brk_r_ok mo req r.
Proof.
  intros mo mat req r CAN LEN R.
  unfold brk_r_ok. cbv zeta.
  unfold brk_grow_ok. cbv zeta.
  unfold brk_budget_ok. cbv zeta.
  rewrite !m_vmmaps_MX.
  match goal with |- (if ?c then _ else _) = _ => destruct c end; [reflexivity|].
  match goal with |- (if ?c then _ else _) = _ => destruct c end; [reflexivity|].
  destruct (bv_eqb r req) eqn:Erq; cbn [orb andb].
  - apply bv_eqb_eq in Erq. subst r.
    match goal with |- (if ?c then _ else _) = _ => destruct c end; [|reflexivity].
    f_equal.
    rewrite vm_backing_used_MX, (vm_backing_used_canon mo CAN).
    replace (nonlazy_bytes mo + Z.of_nat (length mat) * page_size
             + brk_grow_bytes (m_vmmaps mo) req)
      with (nonlazy_bytes mo + brk_grow_bytes (m_vmmaps mo) req
            + Z.of_nat (length mat) * page_size) by lia.
    apply robust_leb; [exact R| apply mat_bound0; exact LEN].
  - match goal with |- (?c && _) = _ => destruct c eqn:Erb end; cbn [andb]; [|reflexivity].
    apply bv_eqb_eq in Erb. subst r.
    rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

End Slack.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma strip_with_vmmaps : forall h m, strip (with_vmmaps h m) = with_vmmaps h (strip m).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01hh11mp;1p;2g00Y9j12Tg00Zfj21Tg006Ej20Tg011Tg00_AR0f1f0#2'1,00W1W0o"). Qed.
Lemma vmmaps_strip : forall m, m_vmmaps (strip m) = m_vmmaps m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01mp;1p;2g00Yoj11Tg006Ej20Tg00_Ag011Tf0#1'0W0o"). Qed.
Lemma strip_vm_add_lazy : forall a n m, strip (vm_add_lazy a n m) = strip m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01ah11mh21np;1p;2g00DLj10Tg00V9j14Tg00VWj12Tg00Y9j11Tg006Ej23Tg00OE#0#0#0#0#0#0#4#2R0g00_AR1f0#1,31W1X20W0o"). Qed.
Lemma strip_vm_forget_range : forall lo hi m, strip (vm_forget_range lo hi m) = strip m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h02hih12loh21mp;1p;2g00Y9j11Tg006Ej20Tg00IRR0g00_AR1f0#1,01W2X00W1o"). Qed.
Lemma strip_with_mmap_backing : forall f a n m, strip (with_mmap_backing f a n m) = strip m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b f); reflexivity. Qed.
Lemma strip_with_mmap_destroyed : forall a n h m, strip (with_mmap_destroyed a n h m) = with_vmmaps h (strip m).
Proof. reflexivity. Qed.
Lemma strip_with_mmap_replacement : forall f a n m, strip (with_mmap_replacement f a n m) = strip m.
Proof. intros. unfold with_mmap_replacement. rewrite strip_with_mmap_backing. reflexivity. Qed.
Lemma strip_mprotect_model_next : forall m a n, strip (mprotect_model_next m a n) = with_vmmaps (m_vmmaps (mprotect_model_next m a n)) (strip m).
Proof. reflexivity. Qed.
Lemma strip_madvise_dontneed_next : forall m a n, strip (madvise_dontneed_next m a n) = strip m.
Proof. reflexivity. Qed.
Lemma with_vmmaps_idem : forall h h' m, with_vmmaps h (with_vmmaps h' m) = with_vmmaps h m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01hh12h'h21mp;2g00Zfj21Tg006Ej20Tg011TR0g00_AR1f2f0'1,01W2X10W0o"). Qed.
Lemma with_vmmaps_strip_vmmaps : forall m h, with_vmmaps (m_vmmaps (with_vmmaps h (strip m))) (strip m) = with_vmmaps h (strip m).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac strip_tac :=
  rewrite ?strip_with_mmap_replacement, ?strip_with_mmap_backing, ?strip_with_mmap_destroyed, ?strip_with_vmmaps,
          ?vmmaps_with_mmap_replacement, ?vmmaps_with_mmap_backing;
  first [ reflexivity | apply strip_self ].

(* [comment removed for export] *)
Ltac xfer_leaf :=
  first [ exact I
        | apply relX_id
        | apply relX_same; [ strip_tac | rewrite ?mat_with_mmap_backing; reflexivity ]
        | apply relX_filter; [ strip_tac | rewrite ?mat_with_mmap_replacement, ?mat_with_mmap_backing; reflexivity ]
        | apply relX_ret_only ].

(* [comment removed for export] *)
Ltac xfer_push :=
  progress (rewrite ?m_vmmaps_MX, ?with_vmmaps_MX, ?with_mmap_backing_MX, ?with_mmap_destroyed_MX,
                    ?with_mmap_replacement_MX, ?mprotect_model_next_MX).

Ltac xfer :=
  cbv zeta;
  repeat first
    [ xfer_leaf
    | lazymatch goal with
      | |- relX _ _ (match ?x with _ => _ end) (match ?x with _ => _ end) => destruct x
      end
    | xfer_push ].

Section Transfer.
Variable NMAX : nat.

Lemma check_munmap_X : forall addr len eff mo mat,
  relX mo mat (check_munmap addr len eff (MX mo mat)) (check_munmap addr len eff mo).
Proof.
  intros addr len eff mo mat. unfold check_munmap.
  rewrite !m_vmmaps_MX, !with_mmap_destroyed_MX.
  xfer.
Qed.

(* [comment removed for export] *)
Lemma check_madvise_X : forall addr len advice eff mo mat,
  relX mo mat (check_madvise addr len advice eff (MX mo mat)) (check_madvise addr len advice eff mo).
Proof.
  intros addr len advice eff mo mat. unfold check_madvise.
  rewrite !m_vmmaps_MX, !madvise_dontneed_next_MX.
  xfer;
    (apply relX_filter; [ rewrite strip_madvise_dontneed_next, vmmaps_madvise_dontneed_next; apply strip_self
                        | apply mat_madvise_dontneed_next ]).
Qed.

Lemma check_mprotect_X : forall addr len prot eff mo mat,
m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
robust NMAX (nonlazy_bytes (mprotect_model_next mo addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))))
(vm_limit (m_vmmaps mo)) ->
relX mo mat (check_mprotect addr len prot eff (MX mo mat)) (check_mprotect addr len prot eff mo).
Proof.
intros addr len prot eff mo mat CAN LEN R. unfold check_mprotect.
unfold mprotect_refusable. rewrite !(mprotect_budget_ok_X NMAX) by assumption.
rewrite !m_vmmaps_MX, !mprotect_model_next_MX.
try change (m_kernel (MX mo mat)) with (m_kernel mo).
xfer.
Qed.

Lemma check_brk_X : forall req eff mo mat,
m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
robust NMAX (nonlazy_bytes mo + brk_grow_bytes (m_vmmaps mo) req) (vm_limit (m_vmmaps mo)) ->
relX mo mat (check_brk req eff (MX mo mat)) (check_brk req eff mo).
Proof.
intros req eff mo mat CAN LEN R. unfold check_brk.
destruct eff as [r ws zs us cs ci].
destruct ws; [|exact I]. destruct cs; [|exact I]. destruct ci; [|exact I].
cbv beta iota. rewrite (brk_r_ok_X NMAX mo mat req r CAN LEN R), !m_vmmaps_MX.
match goal with |- relX _ _ (if ?c then _ else _) (if ?c then _ else _) => destruct c end; [|exact I].
destruct (with_brk_next_MX mo mat req r) as [E1 E2]. rewrite E1.
apply relX_filter; [|exact E2].
unfold with_brk_next. cbv zeta.
rewrite forget_vm_ranges_strip, strip_with_vmmaps, with_vmmaps_idem. reflexivity.
Qed.

Lemma check_mmap_X : forall addr len prot flags fd off eff mo mat,
m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
let nZ := page_round_up_Z (bv_unsigned len) in
(mmap_noreserve_b flags = true \/ robust NMAX (nonlazy_bytes mo + nZ) (vm_limit (m_vmmaps mo))) ->
robust NMAX (nonlazy_bytes (with_mmap_replacement flags addr (Z_to_bv 64 nZ)
(with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) addr (Z_to_bv 64 nZ)) mo)))
(vm_limit (m_vmmaps mo)) ->
robust NMAX (nonlazy_bytes (with_mmap_replacement flags addr (Z_to_bv 64 nZ)
(with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps mo) addr (Z_to_bv 64 nZ)) mo)))
(vm_limit (m_vmmaps mo)) ->
relX mo mat (check_mmap addr len prot flags fd off eff (MX mo mat)) (check_mmap addr len prot flags fd off eff mo).
Proof.
intros addr len prot flags fd off eff mo mat CAN LEN nZ R1 R2 R3. unfold check_mmap, check_mmap_fixed_overflow.
unfold mmap_grant_refusable, mmap_reserve_refusable, mmap_fixed_fresh_refusable, mmap_fixed_commit_refusable,
mmap_fixed_span_refusable.
rewrite !(noreserve_backed_ok_X NMAX) by assumption.
rewrite !(fixed_rw_budget_ok_X NMAX) by assumption.
rewrite !(fixed_rw_span_budget_ok_X NMAX) by assumption.
rewrite !m_vmmaps_MX, !with_vmmaps_MX, !with_mmap_backing_MX, !with_mmap_destroyed_MX, !with_mmap_replacement_MX.
try change (m_kernel (MX mo mat)) with (m_kernel mo).
rewrite ?m_fds_MX.
xfer.
Qed.

End Transfer.
