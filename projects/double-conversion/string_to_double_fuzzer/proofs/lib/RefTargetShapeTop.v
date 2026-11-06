(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec ShapeAlg Spec RefWorld RefTargetPre
  SymExec3 SymExec3Sound SymPlan SymPlanSoundA RefTargetShape.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SX2S. Import SP. Import SPSA.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition class_shape_ok0 (npos : bool) (s : shape) : bool :=
  forallb (fun cm => forallb (fun c => variant_ok npos s true c cm) [1; 2; 3; 4]%Z) [true; false].

Theorem class_shape_sound0 : forall E fs content s,
  ev E 5 = Z_to_bv 64 (hdr_cfglen content) ->
  ev E 7 = Z_to_bv 64 (hdr_b1 content) ->
  eb E 0 = content ->
  hdr_cfglen content = 0 ->
  (6 <= Z.of_nat (length content))%Z ->
  class_shape_ok0 (npos_of content) s = true ->
  t_eq (sd E fs s) (t_target content fs).
Proof.
  intros E fs content s E5 E7 EB C0 Hlen HC.
  pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1. change (bv_modulus 8) with 256%Z in B1.
  pose proof (bv_unsigned_in_range _ (nth 2 content (Z_to_bv 8 0))) as B2. change (bv_modulus 8) with 256%Z in B2.
  pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 content (Z_to_bv 8 0))) 4 ltac:(lia)) as M4.
  set (b2 := bv_unsigned (nth 2 content (Z_to_bv 8 0))) in *.
  set (c := (1 + b2 mod 4)%Z). set (cm := cm_of content).
  assert (V : variant_ok (npos_of content) s true c cm = true).
  { unfold class_shape_ok0 in HC. rewrite forallb_forall in HC.
    specialize (HC cm ltac:(destruct cm; cbn; auto)). rewrite forallb_forall in HC.
    apply HC. unfold c. cbn. lia. }
  unfold variant_ok in V. destruct (sresolve (tests_of true c cm) s) as [s'|] eqn:Hs; [|discriminate].
  assert (TT : Forall (ctest_ok E) (tests_of true c cm)).
  { unfold tests_of. pose proof (XC_denot E content EB ltac:(lia)) as XD. fold b2 in XD.
    repeat apply Forall_cons; try apply Forall_nil; unfold ctest_ok; cbn [edenot]; rewrite ?XD, ?E5, ?E7.
    - rewrite C0. reflexivity.
    - unfold c. f_equal. lia.
    - unfold c. f_equal. lia.
    - unfold c. f_equal. lia.
    - unfold cm, cm_of, hdr_b1. rewrite u_small by lia.
      destruct (Z.leb_spec 128 (bv_unsigned (nth 1 content (Z_to_bv 8 0)))); [apply Z.leb_gt | apply Z.leb_le]; lia. }
  eapply t_eq_trans; [exact (sresolve_sound E fs _ s s' TT Hs)|].
  eapply t_eq_trans; [exact (shape_equiv_sound E fs s' _ (sresolve_nocase _ _ _ Hs) (starget_nocase _ _ _) V)|].
  replace 1%nat with (calls_of content) by (unfold calls_of; rewrite C0; reflexivity).
  apply starget_sound. lia.
Qed.

(* [comment removed for export] *)
Definition class_shape_ok1 (npos : bool) (s : shape) : bool :=
  forallb (fun cm => forallb (fun c => variant_ok npos s false c cm) [1; 2; 3; 4]%Z) [true; false].

Theorem class_shape_sound1 : forall E fs content s,
  ev E 5 = Z_to_bv 64 (hdr_cfglen content) ->
  ev E 7 = Z_to_bv 64 (hdr_b1 content) ->
  eb E 0 = content ->
  (1 <= hdr_cfglen content)%Z ->
  (6 + hdr_cfglen content <= Z.of_nat (length content))%Z ->
  class_shape_ok1 (npos_of content) s = true ->
  t_eq (sd E fs s) (t_target content fs).
Proof.
  intros E fs content s E5 E7 EB C1 Hlen HC.
  assert (CR : (0 <= hdr_cfglen content < 32768)%Z) by (unfold hdr_cfglen; apply Z.mod_pos_bound; lia).
  pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1. change (bv_modulus 8) with 256%Z in B1.
  pose proof (bv_unsigned_in_range _ (nth 2 content (Z_to_bv 8 0))) as B2. change (bv_modulus 8) with 256%Z in B2.
  pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 content (Z_to_bv 8 0))) 4 ltac:(lia)) as M4.
  set (b2 := bv_unsigned (nth 2 content (Z_to_bv 8 0))) in *.
  set (c := (1 + b2 mod 4)%Z). set (cm := cm_of content).
  assert (V : variant_ok (npos_of content) s false c cm = true).
  { unfold class_shape_ok1 in HC. rewrite forallb_forall in HC.
    specialize (HC cm ltac:(destruct cm; cbn; auto)). rewrite forallb_forall in HC.
    apply HC. unfold c. cbn. lia. }
  unfold variant_ok in V. destruct (sresolve (tests_of false c cm) s) as [s'|] eqn:Hs; [|discriminate].
  assert (TT : Forall (ctest_ok E) (tests_of false c cm)).
  { unfold tests_of. pose proof (XC_denot E content EB ltac:(lia)) as XD. fold b2 in XD.
    repeat apply Forall_cons; try apply Forall_nil; unfold ctest_ok; cbn [edenot]; rewrite ?XD, ?E5, ?E7.
    - rewrite u_small by lia. apply Z.leb_gt. lia.
    - unfold c. f_equal. lia.
    - unfold c. f_equal. lia.
    - unfold c. f_equal. lia.
    - unfold cm, cm_of, hdr_b1. rewrite u_small by lia.
      destruct (Z.leb_spec 128 (bv_unsigned (nth 1 content (Z_to_bv 8 0)))); [apply Z.leb_gt | apply Z.leb_le]; lia. }
  eapply t_eq_trans; [exact (sresolve_sound E fs _ s s' TT Hs)|].
  eapply t_eq_trans; [exact (shape_equiv_sound E fs s' _ (sresolve_nocase _ _ _ Hs) (starget_nocase _ _ _) V)|].
  replace (Z.to_nat c) with (calls_of content).
  - apply starget_sound. exact Hlen.
  - unfold calls_of, c. destruct (Z.eqb_spec (hdr_cfglen content) 0); [lia|]. rewrite Z2Nat.inj_add by lia. reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
