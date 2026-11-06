(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__ClassifierRows () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.EquivalenceDefinition.Classifier."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.EquivalenceDefinition.FinInput."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ClassifierRows."], [["0C"; "1bool"; "1list"; "1true"; "2eq"; "3Z"; "4agree_s"; "4classifier_total_T_fo"; "4classifies_good_inputs_T_s"; "4classifies_patch_diff_T_s"; "4decides_fo"; "4good_input_s"; "5image_brk_satisfiable"; "5strong_universal_error_free_T_scfg"; "5trace_equiv"; "6FinProcInput"]; ["6to_proc_input"; "6valid_fin_input"; "7Image"; "7img_segments"; "8ExecEntry"; "8bh_traces"; "8run_scfg"; "8valid_entry"; "8valid_input"; "9ProcInput"; "9event"; "0O1"; "0O2"; ":always_accepts"; "0T"; "0T1"]; ["0T2"; "0T3"; "0X"; "0cfg"; "0en"; "0f"; "0inp"; "0lim"; "0spec"]]).
Definition always_accepts (C : Image) : Prop :=
forall f : FinProcInput,
valid_fin_input f ->
forall en,
valid_entry C en (to_proc_input f) ->
must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f).
Lemma total_of_always_accepts : ltac2:(TCodec.tc2 tcn__ClassifierRows "9'B&Mr1%211&7r2%211p041p281").
Proof.
intros C H f Hf en Hen. left. exact (H f Hf en Hen).
Qed.
Lemma decides_fo_of_always_true : ltac2:(TCodec.tc2 tcn__ClassifierRows "H'B'I!p021&Mr2%211'?&Ar1%211r4&@%118%311p051pR<91&:r3%2281p041p0?1pRBC1p2G1").
Proof.
intros C spec HA HS f Hf en Hen. split.
- split; intros _; [apply HS; exact Hf | exact (HA f Hf en Hen)].
- left. exact (HA f Hf en Hen).
Qed.
Lemma trace_equiv_refl : ltac2:(TCodec.tc2 tcn__ClassifierRows "9'2'J%211!p021&>r1%2211pQN41").
Proof. intros T tr. tauto. Qed.
Lemma trace_equiv_sym : ltac2:(TCodec.tc2 tcn__ClassifierRows ">'2'J%211!p021&>r2r1%3221r3%5241p031pR281pR091").
Proof. intros T1 T2 H tr. specialize (H tr). tauto. Qed.
Lemma trace_equiv_trans : ltac2:(TCodec.tc2 tcn__ClassifierRows "@'2'J%211!p021&>r3r2%3221r5%5214p031p041pR491pR2:1pR0;1").
Proof. intros T1 T2 T3 H12 H23 tr. specialize (H12 tr). specialize (H23 tr). tauto. Qed.
Section WithCfg.
Variable cfg : SpuriousCfg.
Lemma good_input_s_of_base : ltac2:(TCodec.tc2 tcn__ClassifierRows "B'B'I&=vQ3r3r2%43321&H%113&;r5r4%349218p051p081pR>>1pQJ@1pQHA1").
Proof.
intros O1 O2 inp Hb Hv en1 en2 H1 H2. exact (Hb en1 en2 inp H1 H2 Hv).
Qed.
Theorem ca_iff_of_base : ltac2:(TCodec.tc2 tcn__ClassifierRows "A'B&=vQ3r3r2%43321&M%113&8r5r4%349218p051p081p2>1pQJ?1pQH@1").
Proof.
intros O1 O2 C Hb HA. unfold classifies_good_inputs_T_s.
apply decides_fo_of_always_true; [exact HA|].
intros f Hf. apply good_input_s_of_base; [exact Hb | exact Hf].
Qed.
Lemma agree_s_self_of_uniform : ltac2:(TCodec.tc2 tcn__ClassifierRows "Q1'B'5'I'2'J%211!p021'D&Gr5r1r3%43321&>&E&FvQ3r6r2r4%5543;21%711%921;p0;1pR:A1&6%15:AA7?p031pQNF1pR>L1pR@N1pR6Q01").
Proof.
intros X lim inp T HU. unfold agree_s.
split.
- intros enX enY HX HY.
eapply trace_equiv_trans; [apply HU; exact HX | apply trace_equiv_sym; apply HU; exact HY].
- repeat split; intros H; exact H.
Qed.
Theorem cb_iff_of_base : ltac2:(TCodec.tc2 tcn__ClassifierRows "M'B&=vQ3r3r2%43321'4'1&<&Cr4%211%411(3%83721&M%116&9r7r6r5%46C33221p061p091p0:1p0D1p2J1pQJK1pQHL1").
Proof.
intros O1 O2 C Hb HS1 HS2 HA. unfold classifies_patch_diff_T_s.
apply decides_fo_of_always_true; [exact HA|].
intros f Hf. set (inp := to_proc_input f) in *.
assert (Hv : valid_input inp) by exact Hf.
destruct (image_brk_satisfiable_entry O1 inp Hv HS1) as [e1 He1].
destruct (image_brk_satisfiable_entry O2 inp Hv HS2) as [e2 He2].
split.
- apply (agree_s_self_of_uniform O1 source_alloc_limit inp
(bh_traces (run_scfg cfg O2 target_alloc_limit e2 inp))).
intros en Hen. exact (proj2 (proj2 (Hb en e2 inp Hen He2 Hv))).
- apply (agree_s_self_of_uniform O2 target_alloc_limit inp
(bh_traces (run_scfg cfg O1 source_alloc_limit e1 inp))).
intros en Hen. apply trace_equiv_sym. exact (proj2 (proj2 (Hb e1 en inp He1 Hen Hv))).
Qed.
End WithCfg.
