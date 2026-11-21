(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (48 recorded proofs replaced by written proofs (rng_sub, rng_sub', rng_bounds and 45 more)). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Exec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import AcctCore.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ExecF () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1c59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init5Logic3and01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01c59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib4LibA5ExecF7rng_subC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C47Corelib4Init5Logic8eq_ind_rC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Peano2le00I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib4LibA5ExecF6acc_inC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z6inj_leI47Corelib7Numbers7BinNums1N00C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op205c59OSSVerify5KrLib4LibA5ExecF;rng_acc_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indc59OSSVerify5KrLib4LibA5ExecF;rng_acc_varC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalc59OSSVerify5KrLib4LibA5ExecF6mstepFC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib4LibA5ExecF7mstepsF01C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib4LibA5ExecF7mstepsF02C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00i59OSSVerify5KrLib4LibA5ExecF7mstepsF00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF;mstepsF_indC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I47Corelib4Init9Datatypes4prod00I47Corelib5Lists7ListDef6Forall00c59OSSVerify5KrLib4LibA5ExecF9evtF_stepC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessc59OSSVerify5KrLib4LibA5ExecF=mstepsF_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF8evtF_cutC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;Forall_implc59OSSVerify5KrLib4LibA5ExecF=mstepF_weakenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF>mstepsF_weakenC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_step_accessesC47Corelib4Init5Logic5proj1c59OSSVerify5KrLib4LibA5ExecF;mstepF_stepC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI59OSSVerify5KrLib3Lib4Exec6msteps00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib4Exec6msteps01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF<mstepF_mstepC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib4Exec6msteps02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF>mstepsF_mstepsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib4LibA5ExecF5cstepC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib4LibA5ExecF6csteps01C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib4LibA5ExecF6csteps02C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00i59OSSVerify5KrLib4LibA5ExecF6csteps00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF:csteps_indC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C4ELinuxProcessSemantics?LinuxProcessSem3RunHmi_account_step_projectsc59OSSVerify5KrLib4LibA5ExecF4evtCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF<csteps_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF9evtC_doneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF8evtC_cutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF<footprint_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC4ELinuxProcessSemantics?LinuxProcessSem5State>accesses_pagesC46Stdlib5Lists4List2InC59OSSVerify5KrLib4LibA8AcctCoreAaccesses_pages_inC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib4LibA8AcctCore7page_okC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC59OSSVerify5KrLib4LibA8AcctCore;accesses_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofI47Corelib4Init5Logic5False00I59OSSVerify5KrLib4LibA8AcctCore4ainv00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecFHaccesses_ok_of_footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA8AcctCoreBmi_account_step_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA8AcctCore<same_but_matC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA8AcctCoreAsame_but_mat_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF;mstepF_liftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA8AcctCoreCsame_but_mat_haltedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA8AcctCoreBsame_but_mat_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF9evtF_liftC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesK47Corelib4Init5Logic2or01K47Corelib4Init9Datatypes4bool02C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib3Lib4Exec5mstepC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem3RunGmi_account_step_no_lazyC59OSSVerify5KrLib3Lib4Exec:msteps_indC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF5fp_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic4True00C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizec59OSSVerify5KrLib4LibA5ExecF=lazy_disjointC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecFBpage_base_of_rangeC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4BoolBnot_true_iff_falseC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7existsbC47Corelib4Init5Logic3iffC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsBsubrelation_properC46Stdlib5Lists4List>existsb_existsC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leK46Stdlib9micromega5Tauto8GFormula06C47Corelib7Classes>Morphisms_Prop@not_iff_morphismC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationc59OSSVerify5KrLib4LibA5ExecFPpage_in_ranges_false_of_disjointC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF9rng_fp_okC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition footprint := Z -> nat -> Prop.   (* [comment removed for export] *)

Definition acc_in (RNG : footprint) (acc : word * nat) : Prop :=
  RNG (bv_unsigned (fst acc)) (snd acc).

(* [comment removed for export] *)
Definition rng (RNG : footprint) (lo : Z) (len : Z) : Prop :=
  0 <= lo /\ lo + len <= 2^64 /\
  forall b (j : nat), lo <= b -> b + Z.of_nat j <= lo + len -> RNG b j.

Lemma rng_sub : forall RNG lo len lo' len',
  rng RNG lo len -> lo <= lo' -> lo' + len' <= lo + len -> rng RNG lo' len'.
Proof. intros RNG lo len lo' len' (A & B & H) Hlo Hhi. split; [lia|]. split; [lia|]. intros b j Hb Hj. apply H; lia. Qed.

(* [comment removed for export] *)
Lemma rng_sub' : forall RNG lo len lo' len',
  rng RNG lo len -> (lo <= lo' /\ lo' + len' <= lo + len) -> rng RNG lo' len'.
Proof. intros RNG lo len lo' len' H [A B]. eapply rng_sub; eauto. Qed.

Lemma rng_bounds : forall RNG lo len, rng RNG lo len -> 0 <= lo /\ lo + len <= 2^64.
Proof. intros RNG lo len (A & B & _). lia. Qed.

Lemma rng_nil : forall RNG lo, 0 <= lo <= 2^64 -> (forall j : nat, RNG lo 0%nat) -> rng RNG lo 0.
Proof.
  intros RNG lo H H0. split; [lia|]. split; [lia|]. intros b j Hb Hj.
  assert (j = 0%nat) by lia. assert (b = lo) by lia. subst. apply H0. exact 0%nat.
Qed.

(* [comment removed for export] *)
Lemma rng_acc_lit : forall RNG lo len E (n : nat),
  rng RNG lo len -> (1 <= n)%nat -> (lo <= E /\ E + Z.of_nat n <= lo + len) ->
  acc_in RNG (Z_to_bv 64 E, n).
Proof.
  intros RNG lo len E n (A & B & H) Hn [HE1 HE2]. unfold acc_in. cbn [fst snd].
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia). apply H; lia.
Qed.

Lemma rng_acc_var : forall RNG lo len (x : word) (n : nat),
  rng RNG lo len -> (lo <= bv_unsigned x /\ bv_unsigned x + Z.of_nat n <= lo + len) ->
  acc_in RNG (x, n).
Proof. intros RNG lo len x n (A & B & H) [H1 H2]. unfold acc_in. cbn [fst snd]. apply H; lia. Qed.

(* [comment removed for export] *)
Lemma rng_acc_litZ : forall RNG lo len E (n : nat) (nz : Z),
  rng RNG lo len -> Z.of_nat n = nz -> 1 <= nz -> (lo <= E /\ E + nz <= lo + len) ->
  acc_in RNG (Z_to_bv 64 E, n).
Proof. intros RNG lo len E n nz H <- Hn HE. eapply rng_acc_lit; eauto. lia. Qed.

Lemma rng_acc_varZ : forall RNG lo len (x : word) (n : nat) (nz : Z),
  rng RNG lo len -> Z.of_nat n = nz -> (lo <= bv_unsigned x /\ bv_unsigned x + nz <= lo + len) ->
  acc_in RNG (x, n).
Proof. intros RNG lo len x n nz H <- HE. eapply rng_acc_var; eauto. Qed.

(* [comment removed for export] *)
Lemma rng_acc_wrapZ : forall RNG lo len E (n : nat) (nz : Z),
  rng RNG lo len -> Z.of_nat n = nz -> (lo <= E mod 2^64 /\ E mod 2^64 + nz <= lo + len) ->
  acc_in RNG (Z_to_bv 64 E, n).
Proof.
  intros RNG lo len E n nz (A & B & H) <- [H1 H2]. unfold acc_in. cbn [fst snd].
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 E) with (E mod 2^64). apply H; lia.
Qed.

(* [comment removed for export] *)
Definition fp_union (R1 R2 : footprint) : footprint := fun b j => R1 b j \/ R2 b j.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mstepF (RNG : footprint) (ms ms' : machine_state) : Prop :=
  ms_svc_pending ms = None /\
  exists accs, RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' accs)
          /\ Forall (acc_in RNG) accs.

Inductive mstepsF (RNG : footprint) : machine_state -> machine_state -> Prop :=
| mstepsF_refl : forall ms, mstepsF RNG ms ms
| mstepsF_cons : forall ms ms1 ms2, mstepF RNG ms ms1 -> mstepsF RNG ms1 ms2 -> mstepsF RNG ms ms2.

Definition evtF (RNG : footprint) (Q : machine_state -> Prop) (ms : machine_state) : Prop :=
  exists ms', mstepsF RNG ms ms' /\ Q ms'.

Lemma mstepsF_one : forall RNG ms ms', mstepF RNG ms ms' -> mstepsF RNG ms ms'.
Proof. intros. econstructor; [eassumption| constructor]. Qed.

Lemma mstepsF_trans : forall RNG a b c, mstepsF RNG a b -> mstepsF RNG b c -> mstepsF RNG a c.
Proof. intros RNG a b c H; induction H; intros; [assumption|]. econstructor; eauto. Qed.

Lemma evtF_done : forall RNG (Q : machine_state -> Prop) ms, Q ms -> evtF RNG Q ms.
Proof. intros RNG Q ms H. exists ms. split; [constructor|exact H]. Qed.

Lemma evtF_step : forall RNG Q ms ms1, mstepF RNG ms ms1 -> evtF RNG Q ms1 -> evtF RNG Q ms.
Proof. intros RNG Q ms ms1 H (ms' & Hs & HQ). exists ms'. split; [econstructor; eauto|exact HQ]. Qed.

(* [comment removed for export] *)
Lemma evtF_step_acc : forall RNG Q ms ms1 accs,
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms1 accs) ->
  Forall (acc_in RNG) accs ->
  evtF RNG Q ms1 -> evtF RNG Q ms.
Proof. intros RNG Q ms ms1 accs Hs E F K. eapply evtF_step; [|exact K]. split; [exact Hs|]. eauto. Qed.

(* [comment removed for export] *)
Lemma evtF_cut : forall RNG (P Q : machine_state -> Prop) ms,
  evtF RNG P ms -> (forall ms', P ms' -> evtF RNG Q ms') -> evtF RNG Q ms.
Proof.
  intros RNG P Q ms (ms1 & H1 & HP) K. destruct (K ms1 HP) as (ms2 & H2 & HQ).
  exists ms2. split; [eapply mstepsF_trans; eauto|exact HQ].
Qed.

Lemma evtF_mono : forall RNG (P Q : machine_state -> Prop) ms,
  evtF RNG P ms -> (forall ms', P ms' -> Q ms') -> evtF RNG Q ms.
Proof. intros RNG P Q ms H K. eapply evtF_cut; [exact H|]. intros ms' HP. apply evtF_done, K, HP. Qed.

(* [comment removed for export] *)
Lemma evtF_eq : forall RNG Q ms ms', ms = ms' -> evtF RNG Q ms' -> evtF RNG Q ms.
Proof. intros; subst; assumption. Qed.

(* [comment removed for export] *)
Lemma mstepF_weaken : forall (R R' : footprint) ms ms',
  (forall b j, R b j -> R' b j) -> mstepF R ms ms' -> mstepF R' ms ms'.
Proof.
  intros R R' ms ms' W [Hs (accs & E & F)]. split; [exact Hs|]. exists accs. split; [exact E|].
  eapply Forall_impl; [|exact F]. intros [b j]; unfold acc_in; cbn; auto.
Qed.

Lemma mstepsF_weaken : forall (R R' : footprint) ms ms',
  (forall b j, R b j -> R' b j) -> mstepsF R ms ms' -> mstepsF R' ms ms'.
Proof.
  intros R R' ms ms' W Hs. induction Hs; [constructor|]. econstructor; [eapply mstepF_weaken; eauto| exact IHHs].
Qed.

Lemma evtF_weaken : forall (R R' : footprint) Q ms,
  (forall b j, R b j -> R' b j) -> evtF R Q ms -> evtF R' Q ms.
Proof.
  intros R R' Q ms W (ms' & Hs & HQ). exists ms'. split; [|exact HQ]. eapply mstepsF_weaken; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mstepF_step : forall RNG ms ms', mstepF RNG ms ms' -> RiscvSemantics.step segs ms = MachineOk ms'.
Proof.
  intros RNG ms ms' [_ (accs & E & _)].
  rewrite <- RiscvSemantics.drop_step_accesses. rewrite E. reflexivity.
Qed.

Lemma mstepF_mstep : forall RNG ms ms', mstepF RNG ms ms' -> mstep segs ms ms'.
Proof. intros RNG ms ms' H. split; [exact (proj1 H)| eapply mstepF_step; exact H]. Qed.

Lemma mstepsF_msteps : forall RNG ms ms', mstepsF RNG ms ms' -> msteps segs ms ms'.
Proof.
  intros RNG ms ms' H. induction H; [apply msteps_refl|]. eapply msteps_cons; [eapply mstepF_mstep; eauto| assumption].
Qed.

Lemma evtF_evt : forall RNG Q ms, evtF RNG Q ms -> evt segs Q ms.
Proof. intros RNG Q ms (ms' & H & HQ). exists ms'. split; [eapply mstepsF_msteps; eauto| exact HQ]. Qed.

(* [comment removed for export] *)
Lemma mstepF_det : forall R R' ms a b, mstepF R ms a -> mstepF R' ms b -> a = b.
Proof.
  intros R R' ms a b Ha Hb. apply (mstepF_step R) in Ha. apply (mstepF_step R') in Hb. congruence.
Qed.

Lemma mstepF_not_svc : forall R ms ms', mstepF R ms ms' -> ms_svc_pending ms = None.
Proof. intros R ms ms' [H _]; exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cstep (c c' : machine_state * Model) : Prop :=
  m_halted (snd c) = None /\ ms_svc_pending (fst c) = None /\
  mi_account_step segs (fst c) (snd c) = MachineOk c'.

Inductive csteps : machine_state * Model -> machine_state * Model -> Prop :=
| csteps_refl : forall c, csteps c c
| csteps_cons : forall c c1 c2, cstep c c1 -> csteps c1 c2 -> csteps c c2.

Lemma csteps_one : forall c c', cstep c c' -> csteps c c'.
Proof. intros. econstructor; [eassumption|constructor]. Qed.

Lemma csteps_trans : forall a b c, csteps a b -> csteps b c -> csteps a c.
Proof. intros a b c H; induction H; intros; [assumption|]. econstructor; eauto. Qed.

Lemma cstep_det : forall c a b, cstep c a -> cstep c b -> a = b.
Proof. intros c a b (_ & _ & Ha) (_ & _ & Hb). congruence. Qed.

Lemma cstep_sstep : forall ms mo ms' mo',
  cstep (ms, mo) (ms', mo') -> sstep segs (mkCfg ms mo) [] (SNext (mkCfg ms' mo')).
Proof. intros ms mo ms' mo' (Hh & Hs & Ha). cbn in *. eapply sstep_instr; eauto. Qed.

(* [comment removed for export] *)
Lemma cstep_step : forall ms mo ms' mo',
  cstep (ms, mo) (ms', mo') -> RiscvSemantics.step segs ms = MachineOk ms'.
Proof.
  intros ms mo ms' mo' (_ & _ & Ha). cbn in Ha. eapply mi_account_step_projects. exact Ha.
Qed.

(* [comment removed for export] *)
Definition evtC (Q : machine_state * Model -> Prop) (c : machine_state * Model) : Prop :=
  exists c', csteps c c' /\ Q c'.

Lemma evtC_done : forall (Q : _ -> Prop) c, Q c -> evtC Q c.
Proof. intros Q c H. exists c. split; [constructor| exact H]. Qed.

Lemma evtC_cut : forall (P Q : _ -> Prop) c,
  evtC P c -> (forall c', P c' -> evtC Q c') -> evtC Q c.
Proof.
  intros P Q c (c1 & H1 & HP) K. destruct (K c1 HP) as (c2 & H2 & HQ).
  exists c2. split; [eapply csteps_trans; eauto| exact HQ].
Qed.

Lemma evtC_mono : forall (P Q : _ -> Prop) c, evtC P c -> (forall c', P c' -> Q c') -> evtC Q c.
Proof. intros P Q c H K. eapply evtC_cut; [exact H|]. intros c' HP. apply evtC_done, K, HP. Qed.

(* [comment removed for export] *)
Definition footprint_ok (lz : list (word * word)) (AL : word -> Prop) (RNG : footprint) : Prop :=
  forall b (j k : nat), RNG b j -> (k < j)%nat -> 0 <= b < 2^64 -> page_ok lz AL (page_base_of (b + Z.of_nat k)).

Lemma footprint_ok_weaken : forall lz AL (R R' : footprint),
  footprint_ok lz AL R' -> (forall b j, R b j -> R' b j) -> footprint_ok lz AL R.
Proof. intros lz AL R R' H W b j k Hb Hk Hr. eapply H; eauto. Qed.

Lemma accesses_ok_of_footprint : forall lz AL RNG accs,
  footprint_ok lz AL RNG -> Forall (acc_in RNG) accs -> accesses_ok lz AL accs.
Proof.
  intros lz AL RNG accs FOK F p Hp.
  apply accesses_pages_in in Hp as [[]|(a & n & k & Hin & Hk & ->)].
  apply (FOK (bv_unsigned a) n k).
  - apply (proj1 (Forall_forall _ _) F (a, n) Hin).
  - exact Hk.
  - pose proof (bv_unsigned_in_range 64 a). change (bv_modulus 64) with (2^64)%Z in H. lia.
Qed.

(* [comment removed for export] *)
Lemma mstepF_lift : forall lz AL N RNG ms ms' mo,
  footprint_ok lz AL RNG -> ainv lz AL N mo -> m_halted mo = None ->
  mstepF RNG ms ms' ->
  exists mo', cstep (ms, mo) (ms', mo') /\ ainv lz AL N mo' /\ same_but_mat mo mo'.
Proof.
  intros lz AL N RNG ms ms' mo FOK INV Hh [Hs (accs & E & F)].
  destruct (mi_account_step_ok segs lz AL N ms mo ms' accs E INV (accesses_ok_of_footprint _ _ _ _ FOK F))
    as (mo' & Ha & INV' & SB).
  exists mo'. split; [|auto]. split; [exact Hh|]. split; [exact Hs|]. exact Ha.
Qed.

(* [comment removed for export] *)
Theorem evtF_lift : forall lz AL N RNG Q ms mo,
  footprint_ok lz AL RNG -> ainv lz AL N mo -> m_halted mo = None ->
  evtF RNG Q ms ->
  exists ms' mo', csteps (ms, mo) (ms', mo') /\ Q ms' /\ ainv lz AL N mo' /\ same_but_mat mo mo'.
Proof.
  intros lz AL N RNG Q ms mo FOK INV Hh (msf & RUN & HQ).
  revert mo INV Hh. induction RUN as [ms0|ms0 ms1 ms2 ST RUN IH]; intros mo INV Hh.
  - exists ms0, mo. split; [constructor|]. split; [exact HQ|]. split; [exact INV| apply same_but_mat_refl].
  - destruct (mstepF_lift lz AL N RNG ms0 ms1 mo FOK INV Hh ST) as (mo1 & C1 & INV1 & SB1).
    destruct (IH HQ mo1 INV1) as (ms' & mo' & CS & HQ' & INV' & SB').
    { rewrite (same_but_mat_halted _ _ SB1). exact Hh. }
    exists ms', mo'. split; [econstructor; eauto|]. split; [exact HQ'|]. split; [exact INV'|].
    eapply same_but_mat_trans; eauto.
Qed.

(* [comment removed for export] *)
Corollary evtF_lift_evtC : forall lz AL N RNG Q ms mo,
  footprint_ok lz AL RNG -> ainv lz AL N mo -> m_halted mo = None ->
  evtF RNG Q ms ->
  evtC (fun c' => Q (fst c') /\ ainv lz AL N (snd c') /\ same_but_mat mo (snd c')) (ms, mo).
Proof.
  intros lz AL N RNG Q ms mo FOK INV Hh EV.
  destruct (evtF_lift lz AL N RNG Q ms mo FOK INV Hh EV) as (ms' & mo' & CS & HQ & INV' & SB).
  exists (ms', mo'). split; [exact CS|]. cbn. auto.
Qed.

(* [comment removed for export] *)
Lemma footprint_ok_nolazy : forall AL RNG, footprint_ok [] AL RNG.
Proof. intros AL RNG b j k _ _ _. left. reflexivity. Qed.

Lemma evt_lift_nolazy : forall Q ms mo,
  m_vm_lazy mo = [] -> m_halted mo = None -> evt segs Q ms ->
  exists ms', csteps (ms, mo) (ms', mo) /\ Q ms'.
Proof.
  intros Q ms mo Hl Hh (ms' & RUN & HQ). exists ms'. split; [|exact HQ].
  induction RUN as [ms0|ms0 ms1 ms2 [Hs ST] RUN IH]; [constructor|].
  econstructor; [|exact (IH HQ)]. split; [exact Hh|]. split; [exact Hs|]. cbn.
  rewrite (mi_account_step_no_lazy segs ms0 mo Hl). rewrite ST. reflexivity.
Qed.

End WithSegs.

Arguments mstepF segs RNG ms ms' /.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fp_ok (lz : list (word * word)) (AL : word -> Prop) : footprint :=
  fun b j => forall k : nat, (k < j)%nat -> 0 <= b < 2^64 -> page_ok lz AL (page_base_of (b + Z.of_nat k)).

Lemma footprint_ok_fp_ok : forall lz AL, footprint_ok lz AL (fp_ok lz AL).
Proof. intros lz AL b j k H Hk Hb. exact (H k Hk Hb). Qed.

Lemma fp_ok_largest : forall lz AL RNG, footprint_ok lz AL RNG -> forall b j, RNG b j -> fp_ok lz AL b j.
Proof. intros lz AL RNG H b j Hr k Hk Hb. eapply H; eauto. Qed.

(* [comment removed for export] *)
Lemma rng_fp_ok : forall lz AL lo len,
  0 <= lo -> lo + len <= 2^64 ->
  (forall z, lo <= z < lo + len -> page_ok lz AL (page_base_of z)) ->
  rng (fp_ok lz AL) lo len.
Proof.
  intros lz AL lo len Hlo Hhi H. split; [lia|]. split; [lia|].
  intros b j Hb Hj k Hk _. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma page_base_of_range : forall z, 0 <= z < 2^64 ->
  bv_unsigned (page_base_of z) <= z < bv_unsigned (page_base_of z) + page_size.
Proof.
  intros z Hz. unfold page_base_of, page_size.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; Z.div_mod_to_equations; lia).
  Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Definition lazy_disjoint (lz : list (word * word)) (lo len : Z) : Prop :=
  Forall (fun r : word * word => lo + len <= bv_unsigned (fst r) \/ bv_unsigned (fst r) + bv_unsigned (snd r) <= lo) lz.

Lemma page_in_ranges_false_of_disjoint : forall lz lo len z,
  lazy_disjoint lz lo len -> lo <= z < lo + len -> 0 <= lo -> lo + len <= 2^64 ->
  page_in_ranges (page_base_of z) lz = false.
Proof.
  intros lz lo len z D Hz Hlo Hhi.
  pose proof (page_base_of_range z ltac:(lia)) as P.
  unfold page_in_ranges. apply Bool.not_true_iff_false. rewrite existsb_exists.
  intros ([a l] & Hin & Hb). cbn [fst snd] in Hb. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply (proj1 (Forall_forall _ _) D) in Hin. cbn [fst snd] in Hin. unfold page_size in *. lia.
Qed.

Lemma rng_fp_ok_disjoint : forall lz AL lo len,
  0 <= lo -> lo + len <= 2^64 -> lazy_disjoint lz lo len -> rng (fp_ok lz AL) lo len.
Proof.
  intros lz AL lo len Hlo Hhi D. apply rng_fp_ok; [lia|lia|].
  intros z Hz. left. eapply page_in_ranges_false_of_disjoint; eauto.
Qed.

(* [comment removed for export] *)
Lemma rng_fp_ok_allowed : forall lz AL lo len,
  0 <= lo -> lo + len <= 2^64 ->
  (forall p : word, (exists z, lo <= z < lo + len /\ p = page_base_of z) -> AL p) ->
  rng (fp_ok lz AL) lo len.
Proof.
  intros lz AL lo len Hlo Hhi H. apply rng_fp_ok; [lia|lia|].
  intros z Hz. right. apply H. exists z. auto.
Qed.
