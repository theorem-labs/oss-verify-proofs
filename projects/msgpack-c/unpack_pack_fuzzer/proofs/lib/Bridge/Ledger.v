(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem State.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64.
Open Scope Z_scope.
Unset Lia Cache.

Section Table.

Variable holds : int -> list word -> (word -> option byte) -> Model -> Prop.
Variable fp : int -> list word -> list (Z * Z).
Hypothesis frame : forall id args m m' model,
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (fp id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  holds id args m model -> holds id args m' model.

Variable C0 : Z -> Prop.
Variable cov1 : int -> list word -> Z -> Prop.
Variable COVP : Model -> word -> Prop.
Variable NMAX : nat.

Definition lazy_shape (mo : Model) : Prop :=
  forall z, C0 z -> page_in_ranges (page_base_of z) (m_vm_lazy mo) = false.
Definition asan_minv (mo : Model) : Prop := m_halted mo = None /\ lazy_shape mo.

Variable ledgered : int -> bool.

Hypothesis H_led : forall id args m mo, ledgered id = true -> holds id args m mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).

Hypothesis H_cov : forall id args m mo z, holds id args m mo -> cov1 id args z ->
  ledgered id = true /\ (page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z)).

Hypothesis H_mat : forall id args m mo mo', holds id args m mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  holds id args m mo'.

Lemma asan_minv_halted : forall mo, asan_minv mo -> m_halted mo = None.
Proof. intros mo [H _]. exact H. Qed.

Lemma asan_minv_mat : forall mo mo', asan_minv mo -> same_but_mat mo mo' -> asan_minv mo'.
Proof.
  intros mo mo' [Hh Hl] SB. pose proof (same_but_mat_frame _ _ SB) as (_ & _ & LZ & _).
  split; [rewrite (same_but_mat_halted _ _ SB); exact Hh|]. intros z Hz. rewrite LZ. apply Hl. exact Hz.
Qed.

Lemma covered_pages_ok : forall (os : list St.oinst) m mo acc,
  asan_minv mo ->
  Forall (fun o => holds (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> St.cov_of C0 cov1 os (bv_unsigned a + j)) ->
  forall p, List.In p (accesses_pages acc []) ->
    page_in_ranges p (m_vm_lazy mo) = false \/ COVP mo p.
Proof.
  intros os m mo acc [_ LS] HO HC p Hp.
  destruct (accesses_pages_in acc [] p Hp) as [[]|(a & n & k & Hin & Hk & ->)].
  destruct (HC a n (Z.of_nat k) Hin ltac:(lia)) as [H0|H1].
  - left. apply LS. exact H0.
  - apply Exists_exists in H1 as (o & Ho & Hc).
    pose proof (proj1 (Forall_forall _ _) HO o Ho) as Hh.
    exact (proj2 (H_cov _ _ _ _ _ Hh Hc)).
Qed.

Lemma asan_acc : forall (os : list St.oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  asan_minv mo ->
  Forall (fun o => holds (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> St.cov_of C0 cov1 os (bv_unsigned a + j)) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ asan_minv mo' /\
              Forall (fun o => holds (fst o) (snd o) m mo') os.
Proof.
  intros os m mo acc MI HO HC.
  pose proof (covered_pages_ok os m mo acc MI HO HC) as POK.

  destruct (existsb (fun o : St.oinst => ledgered (fst o)) os) eqn:EL.
  - apply existsb_exists in EL as (o1 & Ho1 & L1).
    pose proof (proj1 (Forall_forall _ _) HO o1 Ho1) as Hh1.
    destruct (H_led _ _ _ _ L1 Hh1) as (A & INV & SUB).
    assert (OK : accesses_ok (m_vm_lazy mo) A acc).
    { intros p Hp. destruct (POK p Hp) as [NL|CP]; [left; exact NL| right; apply SUB; exact CP]. }
    destruct (account_ok _ _ _ _ _ INV OK) as (mo' & HM & INV' & SB).
    exists mo'. split; [exact HM|]. split; [eapply asan_minv_mat; eassumption|].

    assert (NEW : forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p).
    { intros p Hp. unfold materialize_model_accesses, materialize_accesses in HM.
      set (new := newly_materialized_pages (m_vm_lazy mo) (m_vm_materialized mo) acc) in *.
      assert (MAT' : m_vm_materialized mo' = m_vm_materialized mo \/ m_vm_materialized mo' = new ++ m_vm_materialized mo).
      { destruct new as [|p0 new'] eqn:En.
        - left. injection HM as <-. destruct mo as [fd [maps lz mat] io fs proc lim tm]; reflexivity.
        - right. destruct (vm_backing_used mo + Z.of_nat (length (p0 :: new')) * page_size <=? vm_limit (m_vmmaps mo)); [|discriminate].
          injection HM as <-. destruct mo as [fd [maps lz mat] io fs proc lim tm]; reflexivity. }
      destruct MAT' as [E|E]; rewrite E in Hp; [left; exact Hp|].
      apply in_app_or in Hp as [Hp|Hp]; [|left; exact Hp].
      unfold new, newly_materialized_pages in Hp. apply filter_In in Hp as [Hin Hf].
      apply andb_prop in Hf as [H1 _].
      destruct (POK p Hin) as [NL|CP]; [congruence| right; exact CP]. }
    apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HO o Ho) as Hh.
    eapply H_mat; [exact Hh | exact SB | exact (ai_nodup _ _ _ _ INV') | exact NEW].
  -
    assert (NL : forall p, List.In p (accesses_pages acc []) -> page_in_ranges p (m_vm_lazy mo) = false).
    { intros p Hp. destruct MI as [_ LS].
      destruct (accesses_pages_in acc [] p Hp) as [[]|(a & n & k & Hin & Hk & ->)].
      destruct (HC a n (Z.of_nat k) Hin ltac:(lia)) as [H0|H1]; [apply LS; exact H0|].
      apply Exists_exists in H1 as (o & Ho & Hc).
      pose proof (proj1 (Forall_forall _ _) HO o Ho) as Hh.
      destruct (H_cov _ _ _ _ _ Hh Hc) as [LD _].
      assert (X : existsb (fun o : St.oinst => ledgered (fst o)) os = true) by (apply existsb_exists; exists o; split; assumption).
      congruence. }
    exists mo. split; [apply materialize_accesses_nonlazy; exact NL|]. split; [exact MI| exact HO].
Qed.

Variable semv : int -> list word -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis H_sem : forall id args m mo z, holds id args m mo -> semv id args m mo z ->
  ledgered id = true /\ (page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z)).

Lemma asan_acc_user : forall (os : list St.oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  asan_minv mo ->
  Forall (fun o => holds (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n ->
     St.cov_of C0 cov1 os (bv_unsigned a + j) \/ Exists (fun o => semv (fst o) (snd o) m mo (bv_unsigned a + j)) os) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ asan_minv mo' /\
              Forall (fun o => holds (fst o) (snd o) m mo') os.
Proof.
  intros os m mo acc MI HO HC.

  assert (POK : forall p, List.In p (accesses_pages acc []) ->
            page_in_ranges p (m_vm_lazy mo) = false \/ (COVP mo p /\ existsb (fun o : St.oinst => ledgered (fst o)) os = true)).
  { intros p Hp. destruct MI as [_ LS].
    destruct (accesses_pages_in acc [] p Hp) as [[]|(a & n & k & Hin & Hk & ->)].
    assert (LED : forall o, In o os -> ledgered (fst o) = true -> existsb (fun o : St.oinst => ledgered (fst o)) os = true)
      by (intros o Ho Lo; apply existsb_exists; exists o; split; assumption).
    destruct (HC a n (Z.of_nat k) Hin ltac:(lia)) as [[H0|H1]|H2].
    - left. apply LS. exact H0.
    - apply Exists_exists in H1 as (o & Ho & Hc). pose proof (proj1 (Forall_forall _ _) HO o Ho) as Hh.
      destruct (H_cov _ _ _ _ _ Hh Hc) as [LD [NL|CP]]; [left; exact NL| right; split; [exact CP| exact (LED o Ho LD)]].
    - apply Exists_exists in H2 as (o & Ho & Hc). pose proof (proj1 (Forall_forall _ _) HO o Ho) as Hh.
      destruct (H_sem _ _ _ _ _ Hh Hc) as [LD [NL|CP]]; [left; exact NL| right; split; [exact CP| exact (LED o Ho LD)]]. }
  destruct (existsb (fun o : St.oinst => ledgered (fst o)) os) eqn:EL.
  - apply existsb_exists in EL as (o1 & Ho1 & L1).
    pose proof (proj1 (Forall_forall _ _) HO o1 Ho1) as Hh1.
    destruct (H_led _ _ _ _ L1 Hh1) as (A & INV & SUB).
    assert (OK : accesses_ok (m_vm_lazy mo) A acc).
    { intros p Hp. destruct (POK p Hp) as [NL|[CP _]]; [left; exact NL| right; apply SUB; exact CP]. }
    destruct (account_ok _ _ _ _ _ INV OK) as (mo' & HM & INV' & SB).
    exists mo'. split; [exact HM|]. split; [eapply asan_minv_mat; eassumption|].
    assert (NEW : forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p).
    { intros p Hp. unfold materialize_model_accesses, materialize_accesses in HM.
      set (new := newly_materialized_pages (m_vm_lazy mo) (m_vm_materialized mo) acc) in *.
      assert (MAT' : m_vm_materialized mo' = m_vm_materialized mo \/ m_vm_materialized mo' = new ++ m_vm_materialized mo).
      { destruct new as [|p0 new'] eqn:En.
        - left. injection HM as <-. destruct mo as [fd [maps lz mat] io fs proc lim tm]; reflexivity.
        - right. destruct (vm_backing_used mo + Z.of_nat (length (p0 :: new')) * page_size <=? vm_limit (m_vmmaps mo)); [|discriminate].
          injection HM as <-. destruct mo as [fd [maps lz mat] io fs proc lim tm]; reflexivity. }
      destruct MAT' as [E|E]; rewrite E in Hp; [left; exact Hp|].
      apply in_app_or in Hp as [Hp|Hp]; [|left; exact Hp].
      unfold new, newly_materialized_pages in Hp. apply filter_In in Hp as [Hin Hf].
      apply andb_prop in Hf as [H1 _].
      destruct (POK p Hin) as [NL|[CP _]]; [congruence| right; exact CP]. }
    apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HO o Ho) as Hh.
    eapply H_mat; [exact Hh | exact SB | exact (ai_nodup _ _ _ _ INV') | exact NEW].
  - assert (NL : forall p, List.In p (accesses_pages acc []) -> page_in_ranges p (m_vm_lazy mo) = false).
    { intros p Hp. destruct (POK p Hp) as [X|[_ X]]; [exact X| discriminate X]. }
    exists mo. split; [apply materialize_accesses_nonlazy; exact NL|]. split; [exact MI| exact HO].
Qed.

Definition asan_optable : St.optable :=
  St.OpTable holds fp frame asan_minv C0 cov1 asan_minv_halted asan_acc.

End Table.

Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64.
Open Scope Z_scope.
Unset Lia Cache.

Section Table.

Variable holds : int -> list word -> (word -> option byte) -> Model -> Prop.
Variable fp : int -> list word -> list (Z * Z).
Hypothesis frame : forall id args m m' model,
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (fp id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  holds id args m model -> holds id args m' model.

Variable C0 : Z -> Prop.
Variable cov1 : int -> list word -> Z -> Prop.
Variable COVP : Model -> word -> Prop.
Variable NMAX : nat.

Definition lazy_shape (mo : Model) : Prop :=
  forall z, C0 z -> page_in_ranges (page_base_of z) (m_vm_lazy mo) = false.
Definition asan_minv (mo : Model) : Prop := m_halted mo = None /\ lazy_shape mo.

Variable ledgered : int -> bool.

Hypothesis H_led : forall id args m mo, ledgered id = true -> holds id args m mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).

Hypothesis H_cov : forall id args m mo z, holds id args m mo -> cov1 id args z ->
  ledgered id = true /\ (page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z)).

Hypothesis H_mat : forall id args m mo mo', holds id args m mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  holds id args m mo'.

Lemma asan_minv_halted : forall mo, asan_minv mo -> m_halted mo = None.
Proof. intros mo [H _]. exact H. Qed.

Lemma asan_minv_mat : forall mo mo', asan_minv mo -> same_but_mat mo mo' -> asan_minv mo'.
Proof.
  intros mo mo' [Hh Hl] SB. pose proof (same_but_mat_frame _ _ SB) as (_ & _ & LZ & _).
  split; [rewrite (same_but_mat_halted _ _ SB); exact Hh|]. intros z Hz. rewrite LZ. apply Hl. exact Hz.
Qed.

Lemma covered_pages_ok : forall (os : list St.oinst) m mo acc,
  asan_minv mo ->
  Forall (fun o => holds (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> St.cov_of C0 cov1 os (bv_unsigned a + j)) ->
  forall p, List.In p (accesses_pages acc []) ->
    page_in_ranges p (m_vm_lazy mo) = false \/ COVP mo p.
Proof.
  intros os m mo acc [_ LS] HO HC p Hp.
  destruct (accesses_pages_in acc [] p Hp) as [[]|(a & n & k & Hin & Hk & ->)].
  destruct (HC a n (Z.of_nat k) Hin ltac:(lia)) as [H0|H1].
  - left. apply LS. exact H0.
  - apply Exists_exists in H1 as (o & Ho & Hc).
    pose proof (proj1 (Forall_forall _ _) HO o Ho) as Hh.
    exact (proj2 (H_cov _ _ _ _ _ Hh Hc)).
Qed.

Lemma asan_acc : forall (os : list St.oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  asan_minv mo ->
  Forall (fun o => holds (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> St.cov_of C0 cov1 os (bv_unsigned a + j)) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ asan_minv mo' /\
              Forall (fun o => holds (fst o) (snd o) m mo') os.
Proof.
  intros os m mo acc MI HO HC.
  pose proof (covered_pages_ok os m mo acc MI HO HC) as POK.

  destruct (existsb (fun o : St.oinst => ledgered (fst o)) os) eqn:EL.
  - apply existsb_exists in EL as (o1 & Ho1 & L1).
    pose proof (proj1 (Forall_forall _ _) HO o1 Ho1) as Hh1.
    destruct (H_led _ _ _ _ L1 Hh1) as (A & INV & SUB).
    assert (OK : accesses_ok (m_vm_lazy mo) A acc).
    { intros p Hp. destruct (POK p Hp) as [NL|CP]; [left; exact NL| right; apply SUB; exact CP]. }
    destruct (account_ok _ _ _ _ _ INV OK) as (mo' & HM & INV' & SB).
    exists mo'. split; [exact HM|]. split; [eapply asan_minv_mat; eassumption|].

    assert (NEW : forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p).
    { intros p Hp. unfold materialize_model_accesses, materialize_accesses in HM.
      set (new := newly_materialized_pages (m_vm_lazy mo) (m_vm_materialized mo) acc) in *.
      assert (MAT' : m_vm_materialized mo' = m_vm_materialized mo \/ m_vm_materialized mo' = new ++ m_vm_materialized mo).
      { destruct new as [|p0 new'] eqn:En.
        - left. injection HM as <-. destruct mo as [fd [maps lz mat] io fs proc lim tm]; reflexivity.
        - right. destruct (vm_backing_used mo + Z.of_nat (length (p0 :: new')) * page_size <=? vm_limit (m_vmmaps mo)); [|discriminate].
          injection HM as <-. destruct mo as [fd [maps lz mat] io fs proc lim tm]; reflexivity. }
      destruct MAT' as [E|E]; rewrite E in Hp; [left; exact Hp|].
      apply in_app_or in Hp as [Hp|Hp]; [|left; exact Hp].
      unfold new, newly_materialized_pages in Hp. apply filter_In in Hp as [Hin Hf].
      apply andb_prop in Hf as [H1 _].
      destruct (POK p Hin) as [NL|CP]; [congruence| right; exact CP]. }
    apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HO o Ho) as Hh.
    eapply H_mat; [exact Hh | exact SB | exact (ai_nodup _ _ _ _ INV') | exact NEW].
  -
    assert (NL : forall p, List.In p (accesses_pages acc []) -> page_in_ranges p (m_vm_lazy mo) = false).
    { intros p Hp. destruct MI as [_ LS].
      destruct (accesses_pages_in acc [] p Hp) as [[]|(a & n & k & Hin & Hk & ->)].
      destruct (HC a n (Z.of_nat k) Hin ltac:(lia)) as [H0|H1]; [apply LS; exact H0|].
      apply Exists_exists in H1 as (o & Ho & Hc).
      pose proof (proj1 (Forall_forall _ _) HO o Ho) as Hh.
      destruct (H_cov _ _ _ _ _ Hh Hc) as [LD _].
      assert (X : existsb (fun o : St.oinst => ledgered (fst o)) os = true) by (apply existsb_exists; exists o; split; assumption).
      congruence. }
    exists mo. split; [apply materialize_accesses_nonlazy; exact NL|]. split; [exact MI| exact HO].
Qed.

Variable semv : int -> list word -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis H_sem : forall id args m mo z, holds id args m mo -> semv id args m mo z ->
  ledgered id = true /\ (page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z)).

Lemma asan_acc_user : forall (os : list St.oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  asan_minv mo ->
  Forall (fun o => holds (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n ->
     St.cov_of C0 cov1 os (bv_unsigned a + j) \/ Exists (fun o => semv (fst o) (snd o) m mo (bv_unsigned a + j)) os) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ asan_minv mo' /\
              Forall (fun o => holds (fst o) (snd o) m mo') os.
Proof.
  intros os m mo acc MI HO HC.

  assert (POK : forall p, List.In p (accesses_pages acc []) ->
            page_in_ranges p (m_vm_lazy mo) = false \/ (COVP mo p /\ existsb (fun o : St.oinst => ledgered (fst o)) os = true)).
  { intros p Hp. destruct MI as [_ LS].
    destruct (accesses_pages_in acc [] p Hp) as [[]|(a & n & k & Hin & Hk & ->)].
    assert (LED : forall o, In o os -> ledgered (fst o) = true -> existsb (fun o : St.oinst => ledgered (fst o)) os = true)
      by (intros o Ho Lo; apply existsb_exists; exists o; split; assumption).
    destruct (HC a n (Z.of_nat k) Hin ltac:(lia)) as [[H0|H1]|H2].
    - left. apply LS. exact H0.
    - apply Exists_exists in H1 as (o & Ho & Hc). pose proof (proj1 (Forall_forall _ _) HO o Ho) as Hh.
      destruct (H_cov _ _ _ _ _ Hh Hc) as [LD [NL|CP]]; [left; exact NL| right; split; [exact CP| exact (LED o Ho LD)]].
    - apply Exists_exists in H2 as (o & Ho & Hc). pose proof (proj1 (Forall_forall _ _) HO o Ho) as Hh.
      destruct (H_sem _ _ _ _ _ Hh Hc) as [LD [NL|CP]]; [left; exact NL| right; split; [exact CP| exact (LED o Ho LD)]]. }
  destruct (existsb (fun o : St.oinst => ledgered (fst o)) os) eqn:EL.
  - apply existsb_exists in EL as (o1 & Ho1 & L1).
    pose proof (proj1 (Forall_forall _ _) HO o1 Ho1) as Hh1.
    destruct (H_led _ _ _ _ L1 Hh1) as (A & INV & SUB).
    assert (OK : accesses_ok (m_vm_lazy mo) A acc).
    { intros p Hp. destruct (POK p Hp) as [NL|[CP _]]; [left; exact NL| right; apply SUB; exact CP]. }
    destruct (account_ok _ _ _ _ _ INV OK) as (mo' & HM & INV' & SB).
    exists mo'. split; [exact HM|]. split; [eapply asan_minv_mat; eassumption|].
    assert (NEW : forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p).
    { intros p Hp. unfold materialize_model_accesses, materialize_accesses in HM.
      set (new := newly_materialized_pages (m_vm_lazy mo) (m_vm_materialized mo) acc) in *.
      assert (MAT' : m_vm_materialized mo' = m_vm_materialized mo \/ m_vm_materialized mo' = new ++ m_vm_materialized mo).
      { destruct new as [|p0 new'] eqn:En.
        - left. injection HM as <-. destruct mo as [fd [maps lz mat] io fs proc lim tm]; reflexivity.
        - right. destruct (vm_backing_used mo + Z.of_nat (length (p0 :: new')) * page_size <=? vm_limit (m_vmmaps mo)); [|discriminate].
          injection HM as <-. destruct mo as [fd [maps lz mat] io fs proc lim tm]; reflexivity. }
      destruct MAT' as [E|E]; rewrite E in Hp; [left; exact Hp|].
      apply in_app_or in Hp as [Hp|Hp]; [|left; exact Hp].
      unfold new, newly_materialized_pages in Hp. apply filter_In in Hp as [Hin Hf].
      apply andb_prop in Hf as [H1 _].
      destruct (POK p Hin) as [NL|[CP _]]; [congruence| right; exact CP]. }
    apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HO o Ho) as Hh.
    eapply H_mat; [exact Hh | exact SB | exact (ai_nodup _ _ _ _ INV') | exact NEW].
  - assert (NL : forall p, List.In p (accesses_pages acc []) -> page_in_ranges p (m_vm_lazy mo) = false).
    { intros p Hp. destruct (POK p Hp) as [X|[_ X]]; [exact X| discriminate X]. }
    exists mo. split; [apply materialize_accesses_nonlazy; exact NL|]. split; [exact MI| exact HO].
Qed.

Definition asan_optable : St.optable :=
  St.OpTable holds fp frame asan_minv C0 cov1 asan_minv_halted asan_acc.

End Table.
End TwinB.
