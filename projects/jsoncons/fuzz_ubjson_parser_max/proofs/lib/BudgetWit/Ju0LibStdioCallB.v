(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Ju0LibStdioCall.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: split_lit_denot and stdio_call_sound_fr_b lifted out of Section SE into plain lemmas, TCodec import dropped, and stdio_call_sound_fr_b and stdio_call_sound_b gain an m_channel_reader model = true premise, the same change as its plain-build twin Js0LibStdioCallB.v. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes AgentLib SpecConsts
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame
Hoare Ju0ExitBase Ju0StdioDefs Ju0StdioWrite.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Import SX2.
Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Ju0LibStdioCall.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit Require Import Ju0StdioWriteB SpinAlgB.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope Z_scope.
#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1.
Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Lemma inr_spec : (forall (lo : (@Corelib.Numbers.BinNums.Z)), (forall (n : (@Corelib.Numbers.BinNums.Z)), (forall (x : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Logic.iff (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.bool) (Ju0LibStdioCall.inr lo n x) (@Corelib.Init.Datatypes.true)) (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le lo (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) x)) (@Stdlib.ZArith.BinInt.Z.lt (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) x) (@Stdlib.ZArith.BinInt.Z.add lo n))))))).
Proof. intros lo n x. unfold Ju0LibStdioCall.inr. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.
Lemma inr_false : (forall (lo : (@Corelib.Numbers.BinNums.Z)), (forall (n : (@Corelib.Numbers.BinNums.Z)), (forall (x : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Logic.iff (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.bool) (Ju0LibStdioCall.inr lo n x) (@Corelib.Init.Datatypes.false)) (@Corelib.Init.Logic.not (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le lo (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) x)) (@Stdlib.ZArith.BinInt.Z.lt (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) x) (@Stdlib.ZArith.BinInt.Z.add lo n)))))))).
Proof. intros lo n x. rewrite <- inr_spec. destruct (Ju0LibStdioCall.inr lo n x); split; congruence. Qed.
Lemma know_ok_frame3 : (forall (E : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.env)), (forall (M : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (M' : (forall (x : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (kn : (@Corelib.Init.Datatypes.list (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.kentry))), (forall (b1 : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr)), (forall (o1 : (@Corelib.Numbers.BinNums.Z)), (forall (n1 : (@Corelib.Numbers.BinNums.Z)), (forall (b2 : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr)), (forall (o2 : (@Corelib.Numbers.BinNums.Z)), (forall (n2 : (@Corelib.Numbers.BinNums.Z)), (forall (b3 : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr)), (forall (o3 : (@Corelib.Numbers.BinNums.Z)), (forall (n3 : (@Corelib.Numbers.BinNums.Z)), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.know_ok (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) E M kn)), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.flat E (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.SA b1 o1) n1)), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.flat E (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.SA b2 o2) n2)), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.flat E (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.SA b3 o3) n3)), (forall (_ : (forall (x : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (forall (_ : (@Corelib.Init.Logic.not (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.estart E (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.SA b1 o1)) (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) x)) (@Stdlib.ZArith.BinInt.Z.lt (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) x) (@Stdlib.ZArith.BinInt.Z.add (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.estart E (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.SA b1 o1)) n1))))), (forall (_ : (@Corelib.Init.Logic.not (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.estart E (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.SA b2 o2)) (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) x)) (@Stdlib.ZArith.BinInt.Z.lt (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) x) (@Stdlib.ZArith.BinInt.Z.add (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.estart E (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.SA b2 o2)) n2))))), (forall (_ : (@Corelib.Init.Logic.not (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.estart E (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.SA b3 o3)) (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) x)) (@Stdlib.ZArith.BinInt.Z.lt (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) x) (@Stdlib.ZArith.BinInt.Z.add (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.estart E (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.SA b3 o3)) n3))))), (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))) (M' x) (M x))))))), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk.mem_grows M M')), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.know_ok (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) E M' (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibKnowFrame.kn_frame (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibKnowFrame.kn_frame (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibKnowFrame.kn_frame kn b1 o1 n1) b2 o2 n2) b3 o3 n3))))))))))))))))))))).
Proof.
intros E M M' kn b1 o1 n1 b2 o2 n2 b3 o3 n3 HK F1 F2 F3 Hout Hg.
set (a1 := estart E (SA b1 o1)) in *. set (a2 := estart E (SA b2 o2)) in *. set (a3 := estart E (SA b3 o3)) in *.
set (M1 := fun x : word => if (Ju0LibStdioCall.inr a2 n2 x || Ju0LibStdioCall.inr a3 n3 x)%bool then M x else M' x).
set (M2 := fun x : word => if Ju0LibStdioCall.inr a3 n3 x then M x else M' x).
assert (O1 : forall x : word, (bv_unsigned x < a1 \/ a1 + n1 <= bv_unsigned x)%Z -> M1 x = M x).
{ intros x Hx. unfold M1. destruct (Ju0LibStdioCall.inr a2 n2 x) eqn:E2; [reflexivity|]. destruct (Ju0LibStdioCall.inr a3 n3 x) eqn:E3; [reflexivity|].
cbn [orb]. apply inr_false in E2. apply inr_false in E3. apply Hout; [lia | exact E2 | exact E3]. }
assert (G1 : mem_grows M M1).
{ intros x Hx. unfold M1. destruct (Ju0LibStdioCall.inr a2 n2 x || Ju0LibStdioCall.inr a3 n3 x)%bool; [exact Hx | exact (Hg x Hx)]. }
assert (O2 : forall x : word, (bv_unsigned x < a2 \/ a2 + n2 <= bv_unsigned x)%Z -> M2 x = M1 x).
{ intros x Hx. unfold M1, M2. destruct (Ju0LibStdioCall.inr a3 n3 x) eqn:E3; [rewrite orb_true_r; reflexivity|].
destruct (Ju0LibStdioCall.inr a2 n2 x) eqn:E2; [|reflexivity]. apply inr_spec in E2. lia. }
assert (G2 : mem_grows M1 M2).
{ intros x Hx. unfold M1, M2 in *. destruct (Ju0LibStdioCall.inr a3 n3 x); [rewrite orb_true_r in Hx; exact Hx|].
destruct (Ju0LibStdioCall.inr a2 n2 x); cbn [orb] in Hx; [exact (Hg x Hx) | exact Hx]. }
assert (O3 : forall x : word, (bv_unsigned x < a3 \/ a3 + n3 <= bv_unsigned x)%Z -> M' x = M2 x).
{ intros x Hx. unfold M2. destruct (Ju0LibStdioCall.inr a3 n3 x) eqn:E3; [|reflexivity]. apply inr_spec in E3. lia. }
assert (G3 : mem_grows M2 M').
{ intros x Hx. unfold M2 in Hx. destruct (Ju0LibStdioCall.inr a3 n3 x); [exact (Hg x Hx) | exact Hx]. }
eapply know_ok_frame; [| exact F3 | exact O3 | exact G3].
eapply know_ok_frame; [| exact F2 | exact O2 | exact G2].
eapply know_ok_frame; [exact HK | exact F1 | exact O1 | exact G1].
Qed.
Lemma Forall_one' : forall {A} (P : A -> Prop) x, P x -> Forall P [x].
Proof. intros A P x H. constructor; [exact H | constructor]. Qed.
Lemma kimg_cut_sound : (forall (E : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.env)), (forall (M : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (k : (@Corelib.Init.Datatypes.list (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.kentry))), (forall (a : (@Corelib.Numbers.BinNums.Z)), (forall (n : (@Corelib.Numbers.BinNums.Z)), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.know_ok (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) E M k)), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.know_ok (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) E M (Ju0LibStdioCall.kimg_cut k a n)))))))).
Proof.
intros E M k a n HK. unfold Ju0LibStdioCall.kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
destruct K as [| | |lo hi| | | |]; cbn [Ju0LibStdioCall.kimg_cut1]; try (apply Forall_one'; exact HKK).
destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hap; [apply Forall_one'; exact HKK|].
apply Bool.orb_false_iff in Hap as [Hap1 Hap2]. apply Z.leb_gt in Hap1. apply Z.leb_gt in Hap2.
cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Himg).
apply Forall_app. split.
- destruct (Z.ltb lo a) eqn:E1; [|constructor]. apply Z.ltb_lt in E1. apply Forall_one'. cbn [kentry_ok].
split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
- destruct (Z.ltb (a + n) hi) eqn:E2; [|constructor]. apply Z.ltb_lt in E2. apply Forall_one'. cbn [kentry_ok].
split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
Qed.
Lemma u_lit0 : (forall (E : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.env)), (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.edenot E (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.ELit Z0))) Z0)).
Proof. intros E. cbn [edenot]. apply u64_lit. lia. Qed.
Lemma flat_abs0 : (forall (E : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.env)), (forall (off : (@Corelib.Numbers.BinNums.Z)), (forall (n : (@Corelib.Numbers.BinNums.Z)), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le Z0 off)), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le Z0 n)), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add off n) (@Stdlib.ZArith.BinInt.Z.pow (Zpos 2%positive) (Zpos 64%positive)))), (forall (_ : (@Stdlib.ZArith.BinInt.Z.lt off (@Stdlib.ZArith.BinInt.Z.pow (Zpos 2%positive) (Zpos 64%positive)))), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.flat E (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.SA (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.ELit Z0) off) n)))))))).
Proof. intros E off n H0 Hn Hnw Hlt. unfold flat, estart. cbn [a_base a_off]. rewrite u_lit0. lia. Qed.
Lemma split_lit_denot : (forall (E : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.env)), (forall (e : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr)), (forall (b : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr)), (forall (k : (@Corelib.Numbers.BinNums.Z)), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.prod (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr) (@Corelib.Numbers.BinNums.Z)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.split_lit e) (@Corelib.Init.Datatypes.pair (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr) (@Corelib.Numbers.BinNums.Z) b k))), (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.edenot E e) (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.edenot E b)) k)))))))).
Proof.
intros E.
intros e b k H.
assert (G : forall e' : expr, edenot E e' = Z_to_bv 64 (bv_unsigned (edenot E e') + 0)).
{ intros e'. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
unfold split_lit in H.
destruct e; try (injection H as <- <-; apply G).
- injection H as <- <-. cbn [edenot]. rewrite u64_lit by lia. rewrite Z.add_0_l. reflexivity.
- lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; apply G).
lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; apply G).
injection H as <- <-. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.
Lemma split_lit_vars : (forall (n : (@Corelib.Init.Datatypes.nat)), (forall (e : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr)), (forall (b : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr)), (forall (k : (@Corelib.Numbers.BinNums.Z)), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.prod (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr) (@Corelib.Numbers.BinNums.Z)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.split_lit e) (@Corelib.Init.Datatypes.pair (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr) (@Corelib.Numbers.BinNums.Z) b k))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.bool) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun.expr_vars_lt n e) (@Corelib.Init.Datatypes.true))), (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.bool) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun.expr_vars_lt n b) (@Corelib.Init.Datatypes.true)))))))).
Proof.
intros n e b k H Hv. unfold split_lit in H.
destruct e; try (injection H as <- <-; first [reflexivity | exact Hv]).
lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; exact Hv).
lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; exact Hv).
injection H as <- <-. cbn [expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. exact Hv.
Qed.
Lemma kindex_some : (forall (p : (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.kentry)), (@Corelib.Init.Datatypes.bool))), (forall (kn : (@Corelib.Init.Datatypes.list (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.kentry))), (forall (i : (@Corelib.Init.Datatypes.nat)), (forall (j : (@Corelib.Init.Datatypes.nat)), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.nat)) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDriveX.kindex p kn i) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.nat) j))), (@Corelib.Init.Logic.ex (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.kentry) (fun (K : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.kentry)) => (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.kentry)) (@Stdlib.Lists.List.nth_error (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.kentry) kn (@Corelib.Init.Nat.sub j i)) (@Corelib.Init.Datatypes.Some (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.kentry) K)) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.bool) (p K) (@Corelib.Init.Datatypes.true)) (@Corelib.Init.Peano.le i j)))))))))).
Proof.
intros p kn. induction kn as [|K rest IH]; intros i j H; cbn [kindex] in H; [discriminate|].
destruct (p K) eqn:HP.
- injection H as <-. exists K. rewrite Nat.sub_diag. cbn. auto.
- destruct (IH (S i) j H) as (K' & Hn & HP' & Hle). exists K'.
replace (j - i)%nat with (S (j - S i))%nat by lia. cbn [nth_error]. repeat split; try assumption. lia.
Qed.
Lemma ridx_lit : (forall (n : (@Corelib.Init.Datatypes.nat)), (forall (_ : (@Corelib.Init.Peano.lt n 32%nat)), (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.nat) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.ridx (@stdpp.bitvector.definitions.Z_to_bv (Npos 5%positive) (@Stdlib.ZArith.BinInt.Z.of_nat n))) n))).
Proof.
intros n Hn. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.
Lemma sr_get_nat : (forall (sr : (@Corelib.Init.Datatypes.list (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr))), (forall (n : (@Corelib.Init.Datatypes.nat)), (forall (_ : (@Corelib.Init.Logic.and (@Corelib.Init.Peano.lt (@Corelib.Init.Datatypes.O) n) (@Corelib.Init.Peano.lt n 32%nat))), (@Corelib.Init.Logic.eq (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.sr_get sr (@stdpp.bitvector.definitions.Z_to_bv (Npos 5%positive) (@Stdlib.ZArith.BinInt.Z.of_nat n))) (@Corelib.Lists.ListDef.nth (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr) n sr (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.ELit Z0)))))).
Proof.
intros sr n Hn. unfold sr_get.
assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
{ unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
rewrite Hnz, ridx_lit by lia. reflexivity.
Qed.
Lemma length_sr_upd : (forall (sr : (@Corelib.Init.Datatypes.list (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr))), (forall (n : (@Corelib.Init.Datatypes.nat)), (forall (e : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr)), (forall (_ : (@Corelib.Init.Peano.lt n (@Corelib.Init.Datatypes.length (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr) sr))), (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.nat) (@Corelib.Init.Datatypes.length (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.sr_upd sr n e)) (@Corelib.Init.Datatypes.length (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr) sr)))))).
Proof.
intros sr. induction sr as [|h t IH]; intros n e Hn; cbn [length] in Hn; [lia|].
destruct n; cbn [sr_upd length]; [reflexivity|]. rewrite IH by lia. reflexivity.
Qed.
Lemma nth_sr_upd_same : (forall (sr : (@Corelib.Init.Datatypes.list (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr))), (forall (n : (@Corelib.Init.Datatypes.nat)), (forall (e : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr)), (forall (_ : (@Corelib.Init.Peano.lt n (@Corelib.Init.Datatypes.length (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr) sr))), (@Corelib.Init.Logic.eq (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr) (@Corelib.Lists.ListDef.nth (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr) n (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.sr_upd sr n e) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.ELit Z0)) e))))).
Proof.
intros sr. induction sr as [|h t IH]; intros n e Hn; cbn [length] in Hn; [lia|].
destruct n; cbn [sr_upd nth]; [reflexivity|]. apply IH. lia.
Qed.
Lemma nth_sr_upd_other : (forall (sr : (@Corelib.Init.Datatypes.list (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr))), (forall (n : (@Corelib.Init.Datatypes.nat)), (forall (m : (@Corelib.Init.Datatypes.nat)), (forall (e : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr)), (forall (_ : (@Corelib.Init.Logic.not (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.nat) n m))), (@Corelib.Init.Logic.eq (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr) (@Corelib.Lists.ListDef.nth (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr) m (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.sr_upd sr n e) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.ELit Z0)) (@Corelib.Lists.ListDef.nth (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr) m sr (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.ELit Z0)))))))).
Proof.
intros sr. induction sr as [|h t IH]; intros n m e Hne.
- revert m Hne. induction n as [|n IHn]; intros m Hne; cbn [sr_upd].
+ destruct m; [lia | destruct m; reflexivity].
+ destruct m; [reflexivity|]. cbn [nth]. rewrite IHn by lia. destruct m; reflexivity.
- destruct n; destruct m; cbn [sr_upd nth]; try reflexivity; [lia|]. apply IH. lia.
Qed.
Lemma length_sr_after_call_j : (forall (sr : (@Corelib.Init.Datatypes.list (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr))), (forall (kept : (@Corelib.Init.Datatypes.list (@Corelib.Init.Datatypes.nat))), (forall (nv : (@Corelib.Init.Datatypes.nat)), (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.nat) (@Corelib.Init.Datatypes.length (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive.sr_after_call_j sr kept nv)) 32%nat)))).
Proof. intros. unfold sr_after_call_j. rewrite length_map, length_seq. reflexivity. Qed.
Section SE.
Theorem stdio_call_sound_fr_b :
forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
(R : bvmap 5 word) (M : word -> option byte) (model : Model) (res : Ju0LibStdioCall.stdio_res)
(pending extra : list byte) (K : TSet),
m_channel_reader model = true ->
let E := Env (vals_ev vals) ebs in
regs_ok E sr R -> know_ok RSEGS E M kn ->
Ju0LibStdioCall.stdio_call (length vals) sr kn = Some res ->
let wb := bv_unsigned (edenot E (Ju0LibStdioCall.sc_wb res)) in
let wp := bv_unsigned (edenot E (Ju0LibStdioCall.sc_wp res)) in
let s := edenot E (Ju0LibStdioCall.sc_s res) in
let l := edenot E (Ju0LibStdioCall.sc_l res) in
let su := bv_unsigned (edenot E (Ju0LibStdioCall.sc_sp res)) in
(wb <= wp)%Z -> (wp <= 2 ^ 47)%Z ->
(wp - wb = Z.of_nat (length pending))%Z ->
(bv_unsigned l = Z.of_nat (length extra))%Z ->
(Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
(wp <= su - 112 \/ su <= wb)%Z ->
(bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
(bv_unsigned s + bv_unsigned l <= 2 ^ 47)%Z ->
rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
rdn RSEGS M s (length extra) = Some extra ->
fd_lookup (m_fds model) (Z_to_bv 64 (Ju0LibStdioCall.sc_fd res)) = Some (FdChannel (Z_to_bv 64 (Ju0LibStdioCall.sc_fd res))) ->
m_halted model = None -> m_vm_lazy model = [] ->
K [] ->
(forall R' M',
regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (Ju0LibStdioCall.sc_sr res) R' ->
know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (Ju0LibStdioCall.sc_kn res) ->
sw_post M su (Ju0LibStdioCall.sc_f res) (edenot E (Ju0LibStdioCall.sc_bufp res)) (edenot E (Ju0LibStdioCall.sc_bufsz res)) M' ->
SpinAlgB.rzb RSEGS scfg (mkCfg (mkst R' (Z_to_bv 64 (Ju0LibStdioCall.sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
SpinAlgB.rzb RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x9ec8c) M (seg_rom RSEGS)) model)
(t_emit (map (WriteEv (Z_to_bv 64 (Ju0LibStdioCall.sc_fd res))) (pending ++ extra)) K).
Proof.
intros vals ebs sr kn R M model res pending extra K Hrdr E HR HK Hc.
cbv beta delta [Ju0LibStdioCall.stdio_call] in Hc. cbv zeta in Hc.
destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
destruct (Ju0LibStdioCall.lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
destruct (kread RSEGS kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
destruct (kread RSEGS kn (ELit 0) 0xb5f18 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
destruct (kblob_find kn (ELit 0) 0xe8f20) as [[canlen canb]|] eqn:Hcan; [|discriminate].
destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
cbn [Ju0LibStdioCall.sc_f Ju0LibStdioCall.sc_fd Ju0LibStdioCall.sc_ret Ju0LibStdioCall.sc_wb Ju0LibStdioCall.sc_wp Ju0LibStdioCall.sc_bufp Ju0LibStdioCall.sc_bufsz Ju0LibStdioCall.sc_s Ju0LibStdioCall.sc_l Ju0LibStdioCall.sc_sp Ju0LibStdioCall.sc_sr Ju0LibStdioCall.sc_kn].
intros Hwbwp Hwp47 Hlenp Hlene H30 Dw Ds Hsl Rpend Rextra Hfdlk Hh Hlz HKnil HCONT.
set (wb := bv_unsigned (edenot E wbe)) in *. set (wp := bv_unsigned (edenot E wpe)) in *.
set (s := edenot E (nth 11 sr (ELit 0))) in *. set (l := edenot E (nth 12 sr (ELit 0))) in *.
set (su := bv_unsigned (edenot E (nth 2 sr (ELit 0)))) in *.
apply andb_prop in Hcond as [Hcond Hlen32]. apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hsv].
apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
apply andb_prop in Hcond as [Hcond Hclen].
apply expr_eqb_eq in Hclen.
apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
apply andb_prop in Hcond as [Hcond Hcgv]. apply andb_prop in Hcond as [Hcond Hfd12].
apply andb_prop in Hcond as [Hf0 Hf232].
apply Z.leb_le in Hf0. apply Z.leb_le in Hf232. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
apply Z.eqb_eq in Hcgv. apply Nat.eqb_eq in Hlen32.
assert (Hretv : (ret mod 2 = 0 /\ 0 <= ret < two64)%Z).
{ unfold Ju0LibStdioCall.lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool eqn:Hb; [|discriminate]. injection Hret as ->.
apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2].
apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2. apply Z.ltb_lt in Hb3. lia. }
assert (RG : forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0))).
{ intros n Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))), sr_get_nat by exact Hn. reflexivity. }
assert (R1 : getr R 1 = Z_to_bv 64 ret).
{ replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite RG by lia.
unfold Ju0LibStdioCall.lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool; [|discriminate]. injection Hret as ->. reflexivity. }
assert (R10 : getr R 10 = Z_to_bv 64 f).
{ replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite RG by lia.
rewrite H10. reflexivity. }
assert (R2 : getr R 2 = edenot E (nth 2 sr (ELit 0))).
{ replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). apply RG. lia. }
assert (R11 : getr R 11 = s).
{ replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). apply RG. lia. }
assert (R12 : getr R 12 = l).
{ replace (12%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity). apply RG. lia. }
set (sp := edenot E (nth 2 sr (ELit 0))) in *.
pose proof (base_range_sound RSEGS E M kn qb blo bhi HK Hbr) as Hqbr.
pose proof (split_lit_denot E (nth 2 sr (ELit 0)) qb k0 Hsq) as Hsqd. fold sp in Hsqd.
assert (Hq : su = (bv_unsigned (edenot E qb) + k0)%Z).
{ subst su. rewrite Hsqd. apply u64_lit. lia. }
pose proof (u64_range sp) as Hspr2. fold su in Hspr2.
destruct (kindex_some _ _ _ _ Hki) as (KW & Hnth & HKW & _).
destruct KW as [| | | | | |[cb ck] clen|]; try discriminate. cbn [is_kwr_cov] in HKW.
apply andb_prop in HKW as [HKW Hc2]. apply andb_prop in HKW as [Hcb Hc1].
apply expr_eqb_eq in Hcb. subst cb. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
pose proof (kwr_store_ok RSEGS E M kn _ qb ck clen (k0 - 112) 112%nat HK Hnth Hc1 ltac:(cbn; lia)) as Wst.
assert (Wst' : store_ok RSEGS M (Z_to_bv 64 (su - 112)) 112 = true).
{ unfold adenot, v_addi in Wst. cbn [a_base a_off] in Wst.
replace (bv_unsigned (edenot E qb) + (k0 - 112))%Z with (su - 112)%Z in Wst by lia. exact Wst. }
assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
{ intros off n A B C. apply flat_abs0; lia. }
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 120) 4 (ELit fd) HK Hfd ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rfd.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 40) 8 wpe HK Hwp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwp.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 56) 8 wbe HK Hwb ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwb.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 88) 8 bufp HK Hbufp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufp.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 96) 8 bufsz HK Hbufsz ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufsz.
pose proof (kread_rdn RSEGS E M kn (ELit 0) 0xb5f18 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
pose proof (kblob_find_sound RSEGS E M kn (ELit 0) 0xe8f20 canlen canb HK Hcan) as Kcan.
pose proof (kblob_rdn RSEGS E M kn (ELit 0) 0xe8f20 canlen canb HK Hcan) as Rcan.
assert (Lcan : length (eb E canb) = 8%nat).
{ cbn [kentry_ok] in Kcan. destruct Kcan as (_ & Hl & _). rewrite Hclen in Hl. unfold elenZ in Hl. cbn [edenot] in Hl.
rewrite ?u64_lit, ?u_Z2bv in Hl by lia. lia. }
set (canw := Z_to_bv 64 (bytes_le_to_Z (eb E canb))).
rewrite Lcan, <- (word_to_le_bytes_of_lez 8 (eb E canb) Lcan ltac:(lia)) in Rcan. fold canw in Rcan.
rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
fold wp in Hwpr. fold wb in Hwbr.
replace (Z_to_bv 64 0x9ec8c) with (0x9ec8c%bv : word) by (apply bv_eq; reflexivity).
eapply (Ju0StdioWriteB.ref_stdio_write_b scfg R M model su f wb wp fd s l (edenot E bufp) (edenot E bufsz) canw (Z_to_bv 64 ret)
pending extra K).
- rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
- exact R10.
- exact R11.
- exact R12.
- exact R1.
- lia.
- lia.
- exact Wst'.
- lia.
- lia.
- constructor.
+ rewrite Rwp. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
+ rewrite Rwb. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
+ rewrite Rfd. cbn [edenot]. reflexivity.
+ exact Rbufp.
+ exact Rbufsz.
- split; [|exact Rcan]. rewrite Rcg. cbn [edenot]. f_equal. f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64 in Hcgv. rewrite Hcgv. reflexivity.
- apply orb_prop in Hfd12 as [H|H]; apply Z.eqb_eq in H; subst fd; lia.
- exact Hfdlk.
- exact Hrdr.
- exact Hh.
- exact Hlz.
- lia.
- exact Hwp47.
- exact Hlenp.
- exact Hlene.
- exact H30.
- exact Dw.
- exact Ds.
- exact Hsl.
- exact Rpend.
- exact Rextra.
- apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hretv; lia). lia.
- exact HKnil.
-
intros R' M' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
apply HCONT.
+
assert (HRj : regs_ok E' (sr_after_call_j sr Ju0LibStdioCall.SC_KEPT (length vals)) R').
{ apply (regs_after_call vals ebs sr R R' Ju0LibStdioCall.SC_KEPT Hsv HR).
- intros i Hi. unfold Ju0LibStdioCall.SC_KEPT in Hi. cbn [In] in Hi.
destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
(split; [lia|]);
lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (1%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G1, R1; reflexivity
| replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
| replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
| replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
| replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
| replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
| replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
| replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
| replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
| replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
| replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
| replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
| replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
| replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
| replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
| replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
end.
- unfold Ju0LibStdioCall.SC_KEPT. cbn [In]. lia. }
apply (regs_ok_ext E' (sr_after_call_j sr Ju0LibStdioCall.SC_KEPT (length vals)) _ R');
[ rewrite length_sr_upd by (rewrite length_sr_after_call_j; lia); reflexivity | | exact HRj ].
intros i Hi. rewrite length_sr_after_call_j in Hi.
destruct (Nat.eq_dec i 10) as [->|Hne].
* rewrite nth_sr_upd_same by (rewrite length_sr_after_call_j; lia).
unfold sr_after_call_j. rewrite nth_map_seq by lia. cbn [existsb Ju0LibStdioCall.SC_KEPT Nat.eqb orb].
change (edenot E' (EVar (length vals + 10))) with (vals_ev (vals ++ junk_vals R') (length vals + 10)).
rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite (nth_map_seq (fun i => getr R' (Z_to_bv 5 (Z.of_nat i)))) by lia.
replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10.
apply (edenot_agree (length vals)); [exact Hag|]. apply sr_vars_lt_nth. exact Hsv.
* rewrite nth_sr_upd_other by lia. reflexivity.
+
destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
assert (HK' : know_ok RSEGS E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
assert (HK0 : know_ok RSEGS E' M (Ju0LibStdioCall.kimg_cut (Ju0LibStdioCall.kimg_cut kn (f + 32) 16) (f + 56) 8)) by (apply kimg_cut_sound, kimg_cut_sound, HK').
assert (HK3 : know_ok RSEGS E' M'
(kn_frame (kn_frame (kn_frame (Ju0LibStdioCall.kimg_cut (Ju0LibStdioCall.kimg_cut kn (f + 32) 16) (f + 56) 8) qb (k0 - 112) 112)
(ELit 0) (f + 32) 16) (ELit 0) (f + 56) 8)).
{ assert (Eqb : edenot E' qb = edenot E qb).
{ symmetry. apply (edenot_agree (length vals)); [exact Hag|].
apply (split_lit_vars (length vals) (nth 2 sr (ELit 0)) qb k0 Hsq). apply sr_vars_lt_nth. exact Hsv. }
apply (know_ok_frame3 E' M M'); [exact HK0 | | apply flat_abs0; lia | apply flat_abs0; lia | | exact Pgrows].
- unfold flat, estart. cbn [a_base a_off]. rewrite Eqb. lia.
- intros x N1 N2 N3. apply Pagree.
+ unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. lia.
+ unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0 in N2. lia.
+ unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0 in N3. lia. }
assert (Xb : edenot E' bufp = edenot E bufp) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufp]).
assert (Xs : edenot E' bufsz = edenot E bufsz) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufsz]).
subst E'.
repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply flat_abs0; lia|]); rewrite adenot_lit0.
* rewrite mkAlu_denot. cbn [edenot]. fold E. rewrite alu_add, Xb, Xs. exact Pwend.
* rewrite Xb. exact Pwpos.
* rewrite Xb. exact Pwbase.
+ exact HPOST.
Qed.
End SE.
Theorem stdio_call_sound_b : (forall (vals : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 64%positive)))), (forall (ebs : (forall (_ : (@Corelib.Init.Datatypes.nat)), (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (sr : (@Corelib.Init.Datatypes.list (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.expr))), (forall (kn : (@Corelib.Init.Datatypes.list (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.kentry))), (forall (R : (@LinuxProcessSemantics.Riscv.Prelude.bvmap (Npos 5%positive) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))), (forall (M : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (model : (@LinuxProcessSemantics.LinuxProcessSem.State.Model)), (forall (res : (Ju0LibStdioCall.stdio_res)), (forall (pending : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))), (forall (extra : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))), (forall (K : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.TSet)),
m_channel_reader model = true -> (let E : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.env) := (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.Env (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun.vals_ev vals) ebs) in (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.regs_ok E sr R)), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.know_ok (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) E M kn)), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (Ju0LibStdioCall.stdio_res)) (Ju0LibStdioCall.stdio_call (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 64%positive)) vals) sr kn) (@Corelib.Init.Datatypes.Some (Ju0LibStdioCall.stdio_res) res))), (let wb : (@Corelib.Numbers.BinNums.Z) := (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.edenot E (Ju0LibStdioCall.sc_wb res))) in (let wp : (@Corelib.Numbers.BinNums.Z) := (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.edenot E (Ju0LibStdioCall.sc_wp res))) in (let s : (@stdpp.bitvector.definitions.bv (Npos 64%positive)) := (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.edenot E (Ju0LibStdioCall.sc_s res)) in (let l : (@stdpp.bitvector.definitions.bv (Npos 64%positive)) := (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.edenot E (Ju0LibStdioCall.sc_l res)) in (let su : (@Corelib.Numbers.BinNums.Z) := (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.edenot E (Ju0LibStdioCall.sc_sp res))) in (forall (_ : (@Stdlib.ZArith.BinInt.Z.le wb wp)), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le wp (@Stdlib.ZArith.BinInt.Z.pow (Zpos 2%positive) (Zpos 47%positive)))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@Stdlib.ZArith.BinInt.Z.sub wp wb) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) pending)))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) l) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) extra)))), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) pending)) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) extra))) (@Stdlib.ZArith.BinInt.Z.pow (Zpos 2%positive) (Zpos 30%positive)))), (forall (_ : (@Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le wp (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 112%positive))) (@Stdlib.ZArith.BinInt.Z.le su wb))), (forall (_ : (@Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) s) (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) l)) (@Stdlib.ZArith.BinInt.Z.sub su (Zpos 112%positive))) (@Stdlib.ZArith.BinInt.Z.le su (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) s)))), (forall (_ : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) s) (@stdpp.bitvector.definitions.bv_unsigned (Npos 64%positive) l)) (@Stdlib.ZArith.BinInt.Z.pow (Zpos 2%positive) (Zpos 47%positive)))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.rdn (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) M (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) wb) (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) pending)) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive))) pending))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive)))) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.rdn (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) M s (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv (Npos 8%positive)) extra)) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv (Npos 8%positive))) extra))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry)) (@LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup (@LinuxProcessSemantics.LinuxProcessSem.State.m_fds model) (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (Ju0LibStdioCall.sc_fd res))) (@Corelib.Init.Datatypes.Some (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry) (@LinuxProcessSemantics.LinuxProcessSem.State.FdChannel (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (Ju0LibStdioCall.sc_fd res)))))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 64%positive))) (@LinuxProcessSemantics.LinuxProcessSem.State.m_halted model) (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv (Npos 64%positive))))), (forall (_ : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.list (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))) (@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy model) (@Corelib.Init.Datatypes.nil (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv (Npos 64%positive)) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))))), (forall (_ : (K (@Corelib.Init.Datatypes.nil (@LinuxProcessSemantics.LinuxProcessSem.State.event)))), (forall (_ : (forall (R' : (@LinuxProcessSemantics.Riscv.Prelude.bvmap (Npos 5%positive) (@stdpp.bitvector.definitions.bv (Npos 64%positive)))), (forall (M' : (forall (_ : (@stdpp.bitvector.definitions.bv (Npos 64%positive))), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv (Npos 8%positive))))), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.regs_ok (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.Env (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun.vals_ev (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv (Npos 64%positive)) vals (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive.junk_vals R'))) ebs) (Ju0LibStdioCall.sc_sr res) R')), (forall (_ : (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S.know_ok (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2.Env (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun.vals_ev (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv (Npos 64%positive)) vals (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive.junk_vals R'))) ebs) M' (Ju0LibStdioCall.sc_kn res))), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit.SpinAlgB.rzb (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) scfg (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.mkst fx R' (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (Ju0LibStdioCall.sc_ret res)) M' (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.seg_rom (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments))) model) K)))))), (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit.SpinAlgB.rzb (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) scfg (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.mkst fx R (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (Zpos 650380%positive)) M (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec.seg_rom (@OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments))) model) (@OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg.t_emit (@Corelib.Lists.ListDef.map (@stdpp.bitvector.definitions.bv (Npos 8%positive)) (@LinuxProcessSemantics.LinuxProcessSem.State.event) (@LinuxProcessSemantics.LinuxProcessSem.State.WriteEv (@stdpp.bitvector.definitions.Z_to_bv (Npos 64%positive) (Ju0LibStdioCall.sc_fd res))) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv (Npos 8%positive)) pending extra)) K))))))))))))))))))))))))))))))))))))).
Proof.
intros vals ebs sr kn R M model res pending extra K Hrdr E HR HK Hc wb wp s l su
H1 H1' H2 H3 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 HCONT.
apply (stdio_call_sound_fr_b vals ebs sr kn R M model res pending extra K Hrdr HR HK Hc); try assumption.
intros R' M' A B C. apply HCONT; assumption.
Qed.
End FPX_1.
