(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the hand-off certificates at both values of the CONFIG_RSEQ flag). *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require AsanUbsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require AxSymExec3 AsanPlanCore AsanPlan AsanTablesB AsanStartupB StartupHSBoth StartupPlanBoth BothStartupCert.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require RT_iface RT_rep D_libiface L_libA TopA_iodefs RT_io TopA_start TopA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K Require TopLevelA.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import AsanUbsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanTablesB AsanStartupB
  StartupHSBoth StartupPlanBoth BothStartupCert.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.TopA_iodefs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_io.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.TopA_start.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.TopA.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K Require Import TopLevelA.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
(* LPS 75d69e00 (#38): [hs_all_ok] gained the run's CONFIG_RSEQ flag as its first
   argument ([TopA.v:45], through [hs_start_ok r]), so each recorded hand-off
   state is certified once per value of the flag and the two are joined.  The
   dumps themselves are unchanged.
   The flag reaches the SNAPSHOT as well, and that half was missed: #38 made each
   dump take the flag too ([StartupHSBoth.v:46], [HS_both_0 : Z -> acs]), so a bare
   [HS_both_0] is [Z -> acs] where an [acs] is wanted -- the error the farm printed
   at this line.  Which value to apply is not a choice: [HS_both r h] returns
   [Some (HS_both_0 r)] ([StartupHSBoth.v:62]), so the snapshot takes the SAME flag
   the checker does, and [HS_asan_ok] below quantifies [r] over both together.  The
   consumers fix it the same way -- in the [r = 0] branch ([:63-66]) [hs_if_some_ok]
   instantiates [c] to [HS_both_3000 0], so [hs_ok_3000_0] must be stated at 0. *)
Lemma hs_ok_0_0 : hs_all_ok 0 (HS_both_0 0) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_0_1 : hs_all_ok 1 (HS_both_0 1) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_1000_0 : hs_all_ok 0 (HS_both_1000 0) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_1000_1 : hs_all_ok 1 (HS_both_1000 1) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_2000_0 : hs_all_ok 0 (HS_both_2000 0) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_2000_1 : hs_all_ok 1 (HS_both_2000 1) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_3000_0 : hs_all_ok 0 (HS_both_3000 0) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_3000_1 : hs_all_ok 1 (HS_both_3000 1) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma hs_if_some_ok : forall (P : acs -> Prop) (b : bool) (s : acs) (r : option acs) (ch : acs),
  P s -> (r = Some ch -> P ch) -> (if b then Some s else r) = Some ch -> P ch.
Proof. intros P b s r ch Ps Pr H. destruct b; [injection H as <-; exact Ps | exact (Pr H)]. Qed.

(* LPS 75d69e00 (#38): [TopA.v:70] asks for this at EVERY [r].  [HS_both] is
   defined only at the two admissible flag values ([StartupHSBoth.v]), so the
   hypothesis [HS_both r h = Some ch] forces [r = 0] or [r = 1] and the two
   closed certificates above discharge it.  Nothing here pins [kb_rseq]. *)
Lemma HS_asan_ok : forall r h ch, HS_both r h = Some ch -> hs_all_ok r ch = true.
Proof.
  intros r h ch. unfold HS_both.
  destruct (Z.eqb r 0) eqn:E0; [apply Z.eqb_eq in E0; subst r|].
  - cbn [orb].
    apply (hs_if_some_ok (fun c => hs_all_ok 0 c = true)); [exact hs_ok_3000_0|].
    apply (hs_if_some_ok (fun c => hs_all_ok 0 c = true)); [exact hs_ok_2000_0|].
    apply (hs_if_some_ok (fun c => hs_all_ok 0 c = true)); [exact hs_ok_1000_0|].
    apply (hs_if_some_ok (fun c => hs_all_ok 0 c = true)); [exact hs_ok_0_0| discriminate].
  - destruct (Z.eqb r 1) eqn:E1; [apply Z.eqb_eq in E1; subst r|].
    + cbn [orb].
      apply (hs_if_some_ok (fun c => hs_all_ok 1 c = true)); [exact hs_ok_3000_1|].
      apply (hs_if_some_ok (fun c => hs_all_ok 1 c = true)); [exact hs_ok_2000_1|].
      apply (hs_if_some_ok (fun c => hs_all_ok 1 c = true)); [exact hs_ok_1000_1|].
      apply (hs_if_some_ok (fun c => hs_all_ok 1 c = true)); [exact hs_ok_0_1| discriminate].
    + cbn [orb]. discriminate.
Qed.

(* [comment removed for export] *)
Lemma startup_shape_holes : forall b : bool, holes_only (startup_shape (rseq_z b)) = true.
Proof. intros [|]; reflexivity. Qed.

(* [comment removed for export] *)
Theorem s3s_A : rt_contracts RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) -> fuzz_one_cps RTA LIB_A ->
  S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof.
  intros RC IOC FUZZ.
  exact (s3s_A_of IT0 IT0_ok HS_both startup_plan startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes HS_asan_ok RC IOC FUZZ).
Qed.

(* [comment removed for export] *)
Theorem s3s_A_rc : rt_contracts RTA -> fuzz_one_cps RTA LIB_A ->
  S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof. intros RC FUZZ. exact (s3s_A RC rta_io FUZZ). Qed.

(* [comment removed for export] *)
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Asan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanTablesA AsanStartup
  StartupHSAsan StartupPlanAsan AsanStartupCert.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import RT_iface RT_rep D_libiface L_libA TopA_iodefs RT_io TopA_start TopA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K Require Import TopLevelA.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
(* LPS 75d69e00 (#38): see the TwinB half above.  [hs_all_ok] takes the run's
   CONFIG_RSEQ flag first ([TopA.v:133]), so each dump is certified once per
   value and the two are joined.  The dumps themselves are unchanged, but they
   TAKE the flag now ([StartupHSAsan.v], [HS_asan_0 : Z -> acs]), so it is applied
   here as well -- [HS_asan r h] returns [Some (HS_asan_0 r)], the same r. *)
Lemma hs_ok_0_0 : hs_all_ok 0 (HS_asan_0 0) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_0_1 : hs_all_ok 1 (HS_asan_0 1) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_1000_0 : hs_all_ok 0 (HS_asan_1000 0) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_1000_1 : hs_all_ok 1 (HS_asan_1000 1) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_2000_0 : hs_all_ok 0 (HS_asan_2000 0) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_2000_1 : hs_all_ok 1 (HS_asan_2000 1) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_3000_0 : hs_all_ok 0 (HS_asan_3000 0) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_3000_1 : hs_all_ok 1 (HS_asan_3000 1) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma hs_if_some_ok : forall (P : acs -> Prop) (b : bool) (s : acs) (r : option acs) (ch : acs),
  P s -> (r = Some ch -> P ch) -> (if b then Some s else r) = Some ch -> P ch.
Proof. intros P b s r ch Ps Pr H. destruct b; [injection H as <-; exact Ps | exact (Pr H)]. Qed.

(* [TopA.v:156] asks for this at EVERY [r]; [HS_asan] is defined only at the two
   admissible flag values, so the hypothesis forces [r = 0] or [r = 1]. *)
Lemma HS_asan_ok : forall r h ch, HS_asan r h = Some ch -> hs_all_ok r ch = true.
Proof.
  intros r h ch. unfold HS_asan.
  destruct (Z.eqb r 0) eqn:E0; [apply Z.eqb_eq in E0; subst r|].
  - cbn [orb].
    apply (hs_if_some_ok (fun c => hs_all_ok 0 c = true)); [exact hs_ok_3000_0|].
    apply (hs_if_some_ok (fun c => hs_all_ok 0 c = true)); [exact hs_ok_2000_0|].
    apply (hs_if_some_ok (fun c => hs_all_ok 0 c = true)); [exact hs_ok_1000_0|].
    apply (hs_if_some_ok (fun c => hs_all_ok 0 c = true)); [exact hs_ok_0_0| discriminate].
  - destruct (Z.eqb r 1) eqn:E1; [apply Z.eqb_eq in E1; subst r|].
    + cbn [orb].
      apply (hs_if_some_ok (fun c => hs_all_ok 1 c = true)); [exact hs_ok_3000_1|].
      apply (hs_if_some_ok (fun c => hs_all_ok 1 c = true)); [exact hs_ok_2000_1|].
      apply (hs_if_some_ok (fun c => hs_all_ok 1 c = true)); [exact hs_ok_1000_1|].
      apply (hs_if_some_ok (fun c => hs_all_ok 1 c = true)); [exact hs_ok_0_1| discriminate].
    + cbn [orb]. discriminate.
Qed.

(* [comment removed for export] *)
Lemma startup_shape_holes : forall b : bool, holes_only (startup_shape (rseq_z b)) = true.
Proof. intros [|]; reflexivity. Qed.

(* [comment removed for export] *)
Theorem s3s_A : rt_contracts RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) -> fuzz_one_cps RTA LIB_A ->
  S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof.
  intros RC IOC FUZZ.
  exact (s3s_A_of IT0 IT0_ok HS_asan startup_plan startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes HS_asan_ok RC IOC FUZZ).
Qed.

(* [comment removed for export] *)
Theorem s3s_A_rc : rt_contracts RTA -> fuzz_one_cps RTA LIB_A ->
  S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof. intros RC FUZZ. exact (s3s_A RC rta_io FUZZ). Qed.

(* [comment removed for export] *)
