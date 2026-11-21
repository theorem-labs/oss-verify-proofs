(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (22 recorded proofs replaced by written proofs (vm_backing_used_split, ainv_len, ainv_within_limit and 19 more); same_but_mat_frame restated for the revision's model). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AcctCore () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdI46Stdlib5Lists4List5NoDup00C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib4LibA8AcctCore=nonlazy_bytesC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00i59OSSVerify5KrLib4LibA8AcctCore4ainv00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyI47Corelib4Init5Logic2eq00C46Stdlib5Lists4List2InI47Corelib4Init5Peano2le00I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC56Stdlib6ZArith6BinInt1Z2leC46Stdlib5Lists4List4inclC46Stdlib5Lists4ListANoDup_incl_lengthC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib4LibA8AcctCore8ainv_lenC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedK47Corelib7Numbers7BinNums1Z02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03c59OSSVerify5KrLib4LibA8AcctCoreEvm_backing_used_splitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_lec59OSSVerify5KrLib4LibA8AcctCoreAainv_within_limitC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateGvm_backing_within_limitk59OSSVerify5KrLib4LibA8AcctCore4ainv01C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8page_memI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or02C47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic2or01C47Corelib4Init5Logic6or_indC4ELinuxProcessSemantics?LinuxProcessSem5State;page_insertC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC46Stdlib5Lists4List7existsbC47Corelib4Init5Logic3iffC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4List>existsb_existsC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib7Classes?RelationClasses>iff_Transitivec59OSSVerify5KrLib4LibA8AcctCore;page_mem_InC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notK46Stdlib5Lists4List5NoDup02K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem5State@access_pages_accC4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofc59OSSVerify5KrLib4LibA8AcctCoreApage_insert_nodupC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC4ELinuxProcessSemantics?LinuxProcessSem5State>accesses_pagesC45stdpp9bitvector;definitions;bv_unsignedc59OSSVerify5KrLib4LibA8AcctCoreFaccess_pages_acc_nodupC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib4LibA8AcctCoreApage_insert_casesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib4LibA8AcctCoreCaccess_pages_acc_inC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01K4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01c59OSSVerify5KrLib4LibA8AcctCore<same_but_matC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedc59OSSVerify5KrLib4LibA8AcctCoreBsame_but_mat_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA8AcctCoreDsame_but_mat_nonlazyC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_app_orC47Corelib4Init5Logic7f_equalC47Corelib4Init9Datatypes3appc59OSSVerify5KrLib4LibA8AcctCore;accesses_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateHnewly_materialized_pagesC46Stdlib5Lists4List6filterC46Stdlib5Lists4List9filter_InC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes9andb_propC47Corelib4Init9Datatypes4negbK46Stdlib5Lists4List5NoDup01c59OSSVerify5KrLib4LibA8AcctCoreDaccesses_pages_nodupC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<NoDup_filterC47Corelib4Init5Logic7and_indc59OSSVerify5KrLib4LibA8AcctCore?NoDup_app_introC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib4LibA8AcctCoreAsame_but_mat_reflC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appC4ELinuxProcessSemantics?LinuxProcessSem5State>vm_backed_mapsC4ELinuxProcessSemantics?LinuxProcessSem5StateAmaps_subtract_allC4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01c59OSSVerify5KrLib4LibA8AcctCore:account_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_access".
(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nonlazy_bytes (m : Model) : Z :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m)).

Lemma vm_backing_used_split : forall m,
  vm_backing_used m = nonlazy_bytes m + Z.of_nat (List.length (m_vm_materialized m)) * page_size.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record ainv (lz : list (word * word)) (AL : word -> Prop) (N : nat) (m : Model) : Prop := mkAinv {
  ai_lazy  : m_vm_lazy m = lz;
  ai_nodup : List.NoDup (m_vm_materialized m);
  ai_allow : forall p, List.In p (m_vm_materialized m) -> AL p;
  ai_fin   : exists L, List.NoDup L /\ (List.length L <= N)%nat /\ forall p, AL p -> List.In p L;
  ai_room  : nonlazy_bytes m + Z.of_nat N * page_size <= vm_limit (m_vmmaps m)
}.

Lemma ainv_len : forall lz AL N m, ainv lz AL N m -> (List.length (m_vm_materialized m) <= N)%nat.
Proof.
  intros lz AL N m [_ ND AW (L & NDL & LEN & INL) _].
  assert (List.incl (m_vm_materialized m) L) by (intros p Hp; auto).
  pose proof (NoDup_incl_length ND H). lia.
Qed.

Lemma ainv_within_limit : forall lz AL N m, ainv lz AL N m -> vm_backing_used m <= vm_limit (m_vmmaps m).
Proof.
  intros lz AL N m H. pose proof (ainv_len _ _ _ _ H) as LEN. destruct H as [_ _ _ _ ROOM].
  rewrite vm_backing_used_split. unfold page_size in *. nia.
Qed.

Lemma ainv_within_limit_b : forall lz AL N m, ainv lz AL N m -> vm_backing_within_limit m = true.
Proof. intros lz AL N m H. unfold vm_backing_within_limit. apply Z.leb_le. eapply ainv_within_limit; eauto. Qed.

(* [comment removed for export] *)
Lemma ainv_weaken : forall lz (AL AL' : word -> Prop) (N N' : nat) m,
  ainv lz AL N m ->
  (forall p, AL p -> AL' p) ->
  (exists L', List.NoDup L' /\ (List.length L' <= N')%nat /\ forall p, AL' p -> List.In p L') ->
  nonlazy_bytes m + Z.of_nat N' * page_size <= vm_limit (m_vmmaps m) ->
  ainv lz AL' N' m.
Proof.
  intros lz AL AL' N N' m [LZ ND AW _ _] SUB FIN ROOM. constructor; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition page_ok (lz : list (word * word)) (AL : word -> Prop) (p : word) : Prop :=
  page_in_ranges p lz = false \/ AL p.

Definition accesses_ok (lz : list (word * word)) (AL : word -> Prop) (accs : list (word * nat)) : Prop :=
  forall p, List.In p (accesses_pages accs []) -> page_ok lz AL p.

Lemma page_insert_cases : forall p q pages, List.In p (page_insert q pages) -> p = q \/ List.In p pages.
Proof.
  intros p q pages. unfold page_insert. destruct (page_mem q pages); cbn; intuition.
Qed.

Lemma page_mem_In : forall p pages, page_mem p pages = true <-> List.In p pages.
Proof.
  intros p pages. unfold page_mem. rewrite existsb_exists. split.
  - intros (q & Hq & E). apply bv_eqb_eq in E. subst. exact Hq.
  - intros H. exists p. split; [exact H|]. apply bv_eqb_eq. reflexivity.
Qed.

Lemma page_insert_nodup : forall q pages, List.NoDup pages -> List.NoDup (page_insert q pages).
Proof.
  intros q pages ND. unfold page_insert. destruct (page_mem q pages) eqn:E; [exact ND|].
  constructor; [|exact ND]. intros Hin. apply (proj2 (page_mem_In q pages)) in Hin. congruence.
Qed.

Lemma access_pages_acc_nodup : forall n base pages,
  List.NoDup pages -> List.NoDup (access_pages_acc base n pages).
Proof.
  induction n as [|n IH]; intros base pages Hnd; cbn [access_pages_acc]; [exact Hnd|].
  apply IH. apply page_insert_nodup. exact Hnd.
Qed.

Lemma accesses_pages_nodup : forall accs pages,
  List.NoDup pages -> List.NoDup (accesses_pages accs pages).
Proof.
  induction accs as [|[a n] accs IH]; intros pages Hnd; cbn [accesses_pages]; [exact Hnd|].
  apply IH. apply access_pages_acc_nodup. exact Hnd.
Qed.

(* [comment removed for export] *)
Lemma access_pages_acc_in : forall n base pages p,
  List.In p (access_pages_acc base n pages) ->
  List.In p pages \/ exists k, (k < n)%nat /\ p = page_base_of (base + Z.of_nat k)%Z.
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p H.
  - left; exact H.
  - destruct (IH (base + 1)%Z _ p H) as [Hin | (k & Hk & ->)].
    + destruct (page_insert_cases _ _ _ Hin) as [-> | Hin'].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin'.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : forall accs pages p,
  List.In p (accesses_pages accs pages) ->
  List.In p pages \/ exists a n k, List.In (a, n) accs /\ (k < n)%nat /\ p = page_base_of (bv_unsigned a + Z.of_nat k)%Z.
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages]; intros pages p H.
  - left; exact H.
  - destruct (IH _ p H) as [Hin | (a' & n' & k & Hin & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin) as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k. split; [left; reflexivity | split; assumption].
    + right. exists a', n', k. split; [right; exact Hin | split; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition same_but_mat (m m' : Model) : Prop :=
  m' = with_vm_backing (m_vm_lazy m) (m_vm_materialized m') m.

Lemma same_but_mat_refl : forall a, same_but_mat a a.
Proof. intros a. unfold same_but_mat. destruct a as [fd [mp lzz mt] io fs pr lm tm]; reflexivity. Qed.

Lemma same_but_mat_trans : forall a b c, same_but_mat a b -> same_but_mat b c -> same_but_mat a c.
Proof.
  intros a b c -> ->. unfold same_but_mat.
  destruct a as [fd [mp lzz mt] io fs pr lm tm]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma same_but_mat_frame : forall m m', same_but_mat m m' ->
  m_fd m' = m_fd m /\ m_vmmaps m' = m_vmmaps m /\ m_vm_lazy m' = m_vm_lazy m /\
  m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m /\ m_lim m' = m_lim m /\
  m_time m' = m_time m.   (* [comment removed for export] *)
Proof.
  intros m m' ->. destruct m as [fd [mp lzz mt] io fs pr lm tm]; repeat split; reflexivity.
Qed.

Lemma same_but_mat_halted : forall mo mo', same_but_mat mo mo' -> m_halted mo' = m_halted mo.
Proof. intros mo mo' ->. destruct mo as [fd [mp lzz mt] io fs pr lm tm]; reflexivity. Qed.

Lemma same_but_mat_nonlazy : forall mo mo', same_but_mat mo mo' -> nonlazy_bytes mo' = nonlazy_bytes mo.
Proof. intros mo mo' ->. destruct mo as [fd [mp lzz mt] io fs pr lm tm]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma ainv_same_but_mat : forall lz AL N m m',
  same_but_mat m m' -> m_vm_materialized m' = m_vm_materialized m -> ainv lz AL N m -> ainv lz AL N m'.
Proof.
  intros lz AL N m m' SB EM [LZ ND AW FIN ROOM].
  pose proof (same_but_mat_frame _ _ SB) as (_ & VM & LZ' & _).
  constructor; rewrite ?EM, ?LZ', ?VM, ?(same_but_mat_nonlazy _ _ SB); auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma NoDup_app_intro : forall {A} (l1 l2 : list A),
  List.NoDup l1 -> List.NoDup l2 -> (forall x, List.In x l1 -> ~ List.In x l2) -> List.NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 N1 N2 D. induction l1 as [|x l1 IH]; cbn; [exact N2|].
  inversion N1; subst. constructor.
  - intros Hin. apply in_app_or in Hin as [Hin|Hin]; [contradiction|]. exact (D x (or_introl eq_refl) Hin).
  - apply IH; [assumption|]. intros y Hy. apply D. right; exact Hy.
Qed.

(* [comment removed for export] *)
Lemma account_ok : forall lz AL N m accs,
  ainv lz AL N m -> accesses_ok lz AL accs ->
  exists m', materialize_model_accesses m accs = Some m' /\ ainv lz AL N m' /\ same_but_mat m m'.
Proof.
  intros lz AL N m accs INV OK.
  destruct INV as [LZ ND AW FIN ROOM].
  unfold materialize_model_accesses, materialize_accesses.
  set (new := newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) accs).
  assert (NEWP : forall p, List.In p new -> List.In p (accesses_pages accs []) /\ page_in_ranges p lz = true
                                      /\ ~ List.In p (m_vm_materialized m) /\ AL p).
  { intros p Hp. unfold new, newly_materialized_pages in Hp. apply filter_In in Hp as [Hin Hf].
    apply andb_prop in Hf as [H1 H2]. rewrite LZ in H1.
    assert (~ List.In p (m_vm_materialized m)).
    { intros Hm. apply (proj2 (page_mem_In _ _)) in Hm. rewrite Hm in H2. discriminate. }
    repeat split; auto. destruct (OK p Hin) as [E|A]; [congruence|exact A]. }
  assert (NDnew : List.NoDup new).
  { unfold new, newly_materialized_pages. apply NoDup_filter. apply accesses_pages_nodup. constructor. }
  assert (NDall : List.NoDup (new ++ m_vm_materialized m)).
  { apply NoDup_app_intro; auto. intros x Hx. apply NEWP in Hx. tauto. }
  assert (LENall : (List.length (new ++ m_vm_materialized m) <= N)%nat).
  { destruct FIN as (L & NDL & LEN & INL).
    assert (List.incl (new ++ m_vm_materialized m) L).
    { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; apply INL; [apply NEWP in Hp; tauto| auto]. }
    pose proof (NoDup_incl_length NDall H). lia. }
  destruct new as [|p0 new'] eqn:En.
  - exists m. split; [|split; [constructor; auto| apply same_but_mat_refl]].
    destruct m as [fd [maps lazy mat] io fs proc lim tm sc sg]; reflexivity.
  - rewrite <- En in *.
    assert (FIT : (vm_backing_used m + Z.of_nat (List.length new) * page_size <=? vm_limit (m_vmmaps m)) = true).
    { apply Z.leb_le. rewrite vm_backing_used_split. rewrite length_app in LENall. unfold page_size in *. nia. }
    rewrite En. rewrite <- En. rewrite FIT.
    eexists. split; [reflexivity|]. split.
    + constructor; cbn.
      * destruct m as [fd [maps lazy mat] io fs proc lim tm sc sg]; cbn in *. exact LZ.
      * destruct m as [fd [maps lazy mat] io fs proc lim tm sc sg]; cbn in *. exact NDall.
      * destruct m as [fd [maps lazy mat] io fs proc lim tm sc sg]; cbn in *.
        intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [apply NEWP in Hp; tauto|auto].
      * exact FIN.
      * destruct m as [fd [maps lazy mat] io fs proc lim tm sc sg]; cbn in *. exact ROOM.
    + destruct m as [fd [maps lazy mat] io fs proc lim tm sc sg]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mi_account_step_ok : forall segs lz AL N ms mo ms' accs,
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' accs) ->
  ainv lz AL N mo -> accesses_ok lz AL accs ->
  exists mo', mi_account_step segs ms mo = MachineOk (ms', mo') /\ ainv lz AL N mo' /\ same_but_mat mo mo'.
Proof.
  intros segs lz AL N ms mo ms' accs Hs INV OK.
  destruct (account_ok lz AL N mo accs INV OK) as (mo' & Hm & INV' & SB).
  exists mo'. unfold mi_account_step. rewrite Hs. cbn. rewrite Hm. auto.
Qed.

(* [comment removed for export] *)
Lemma materialize_accesses_nonlazy : forall m accs,
  (forall p, List.In p (accesses_pages accs []) -> page_in_ranges p (m_vm_lazy m) = false) ->
  materialize_model_accesses m accs = Some m.
Proof.
  intros m accs NL. unfold materialize_model_accesses, materialize_accesses.
  replace (newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) accs) with (@nil word).
  - cbn. destruct m as [fd [maps lazy mat] io fs proc lim tm sc sg]; reflexivity.
  - unfold newly_materialized_pages. symmetry.
    assert (G : forall l, (forall p, List.In p l -> page_in_ranges p (m_vm_lazy m) = false) ->
              List.filter (fun p => page_in_ranges p (m_vm_lazy m) && negb (page_mem p (m_vm_materialized m))) l = []).
    { induction l as [|p l IH]; intros Hl; cbn; [reflexivity|].
      rewrite (Hl p (or_introl eq_refl)). cbn. apply IH. intros q Hq. apply Hl. right; exact Hq. }
    apply G. exact NL.
Qed.
