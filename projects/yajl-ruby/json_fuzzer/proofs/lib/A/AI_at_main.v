(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec CatExec ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import
  AgentLib AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import AsanPlanImages5 HS2Asan A_MainFacts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require AImages AImageFacts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require InitMem Step Cells Mem Frame MState.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require AI_shadow AI_globals2 AI_lowshadow AM_syscalls AX_file AX_fini2 AX_unreg AX_Exit AYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require StdioBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition ls_facts : list kentry :=
  [KZero (SA (ELit 0) 0x7fffa000) (ELit 8708);
   KWord (SA (ELit 0) 0x7fffc204) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc205) (ELit 3) 249;
   KZero (SA (ELit 0) 0x7fffc208) (ELit 6);
   KWord (SA (ELit 0) 0x7fffc20e) 1 (ELit 1);
   KFill (SA (ELit 0) 0x7fffc20f) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc214) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc216) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc217) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc21c) (ELit 4);
   KWord (SA (ELit 0) 0x7fffc220) 1 (ELit 1);
   KFill (SA (ELit 0) 0x7fffc221) (ELit 7) 249;
   KZero (SA (ELit 0) 0x7fffc228) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc22a) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc22b) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc230) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc232) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc233) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc238) (ELit 4);
   KFill (SA (ELit 0) 0x7fffc23c) (ELit 4) 249;
   KZero (SA (ELit 0) 0x7fffc240) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc242) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc243) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc248) (ELit 8);
   KWord (SA (ELit 0) 0x7fffc250) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc251) (ELit 3) 249;
   KZero (SA (ELit 0) 0x7fffc254) (ELit 5);
   KWord (SA (ELit 0) 0x7fffc259) 1 (ELit 7);
   KFill (SA (ELit 0) 0x7fffc25a) (ELit 6) 249;
   KZero (SA (ELit 0) 0x7fffc260) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc262) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc263) (ELit 5) 249;
   KWord (SA (ELit 0) 0x7fffc268) 1 (ELit 7);
   KFill (SA (ELit 0) 0x7fffc269) (ELit 3) 249;
   KZero (SA (ELit 0) 0x7fffc26c) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc26d) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc26e) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc270) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc271) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc272) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc274) (ELit 34);
   KWord (SA (ELit 0) 0x7fffc296) 1 (ELit 7);
   KFill (SA (ELit 0) 0x7fffc297) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc29c) (ELit 6);
   KWord (SA (ELit 0) 0x7fffc2a2) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc2a3) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc2a8) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc2a9) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc2aa) (ELit 2) 249;
   KWord (SA (ELit 0) 0x7fffc2ac) 1 (ELit 4);
   KFill (SA (ELit 0) 0x7fffc2ad) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc2b0) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc2b1) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc2b4) 1 (ELit 4);
   KFill (SA (ELit 0) 0x7fffc2b5) (ELit 3) 249;
   KZero (SA (ELit 0) 0x7fffc2b8) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc2b9) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc2ba) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc2bc) (ELit 32);
   KFill (SA (ELit 0) 0x7fffc2dc) (ELit 8) 249;
   KZero (SA (ELit 0) 0x7fffc2e4) (ELit 8);
   KWord (SA (ELit 0) 0x7fffc2ec) 1 (ELit 4);
   KFill (SA (ELit 0) 0x7fffc2ed) (ELit 3) 249;
   KZero (SA (ELit 0) 0x7fffc2f0) (ELit 6);
   KWord (SA (ELit 0) 0x7fffc2f6) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc2f7) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc2fc) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc2fd) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc2fe) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc300) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc301) 1 (ELit 4);
   KFill (SA (ELit 0) 0x7fffc302) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc304) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc305) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc306) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc308) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc309) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc30a) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc30c) (ELit 2);
   KFill (SA (ELit 0) 0x7fffc30e) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc310) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc311) 1 (ELit 7);
   KFill (SA (ELit 0) 0x7fffc312) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc314) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc316) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc317) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc31c) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc31d) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc31e) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc320) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc321) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc322) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc324) (ELit 5);
   KWord (SA (ELit 0) 0x7fffc329) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc32a) (ELit 6) 249;
   KZero (SA (ELit 0) 0x7fffc330) (ELit 3);
   KWord (SA (ELit 0) 0x7fffc333) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc334) (ELit 4) 249;
   KZero (SA (ELit 0) 0x7fffc338) (ELit 31);
   KWord (SA (ELit 0) 0x7fffc357) 1 (ELit 4);
   KFill (SA (ELit 0) 0x7fffc358) (ELit 4) 249;
   KZero (SA (ELit 0) 0x7fffc35c) (ELit 6);
   KWord (SA (ELit 0) 0x7fffc362) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc363) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc368) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc369) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc36a) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc36c) (ELit 6);
   KWord (SA (ELit 0) 0x7fffc372) 1 (ELit 1);
   KFill (SA (ELit 0) 0x7fffc373) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc378) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc37a) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc37b) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc380) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc382) 1 (ELit 1);
   KFill (SA (ELit 0) 0x7fffc383) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc388) (ELit 4);
   KWord (SA (ELit 0) 0x7fffc38c) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc38d) (ELit 7) 249;
   KZero (SA (ELit 0) 0x7fffc394) (ELit 5);
   KWord (SA (ELit 0) 0x7fffc399) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc39a) (ELit 6) 249;
   KZero (SA (ELit 0) 0x7fffc3a0) (ELit 3);
   KWord (SA (ELit 0) 0x7fffc3a3) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc3a4) (ELit 4) 249;
   KZero (SA (ELit 0) 0x7fffc3a8) (ELit 4);
   KWord (SA (ELit 0) 0x7fffc3ac) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc3ad) (ELit 7) 249;
   KZero (SA (ELit 0) 0x7fffc3b4) (ELit 7);
   KFill (SA (ELit 0) 0x7fffc3bb) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc3c0) (ELit 6);
   KWord (SA (ELit 0) 0x7fffc3c6) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc3c7) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc3cc) (ELit 5);
   KWord (SA (ELit 0) 0x7fffc3d1) 1 (ELit 1);
   KFill (SA (ELit 0) 0x7fffc3d2) (ELit 6) 249;
   KZero (SA (ELit 0) 0x7fffc3d8) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc3d9) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc3da) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc3dc) (ELit 7);
   KWord (SA (ELit 0) 0x7fffc3e3) 1 (ELit 1);
   KFill (SA (ELit 0) 0x7fffc3e4) (ELit 4) 249;
   KZero (SA (ELit 0) 0x7fffc3e8) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc3ea) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc3eb) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc3f0) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc3f2) 1 (ELit 7);
   KFill (SA (ELit 0) 0x7fffc3f3) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc3f8) (ELit 8);
   KWord (SA (ELit 0) 0x7fffc400) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc401) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc404) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc405) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc408) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc409) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc40c) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc40d) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc410) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc411) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc414) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc415) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc418) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc419) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc41c) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc41d) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc420) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc421) (ELit 3) 249;
   KZero (SA (ELit 0) 0x7fffc424) (ELit 4);
   KWord (SA (ELit 0) 0x7fffc428) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc429) (ELit 7) 249;
   KZero (SA (ELit 0) 0x7fffc430) (ELit 6);
   KWord (SA (ELit 0) 0x7fffc436) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc437) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc43c) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc43e) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc43f) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc444) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc445) 1 (ELit 4);
   KFill (SA (ELit 0) 0x7fffc446) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc448) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc449) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc44a) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc44c) (ELit 69035);
   KFill (SA (ELit 0) 0x8000d1f7) (ELit 5) 249;
   KZero (SA (ELit 0) 0x8000d1fc) (ELit 4);
   KFill (SA (ELit 0) 0x8000d200) (ELit 4) 249;
   KZero (SA (ELit 0) 0x8000d204) (ELit 4);
   KFill (SA (ELit 0) 0x8000d208) (ELit 4) 249;
   KZero (SA (ELit 0) 0x8000d20c) (ELit 100);
   KFill (SA (ELit 0) 0x8000d270) (ELit 552) 249;
   KZero (SA (ELit 0) 0x8000d498) (ELit 700776)].

(* [comment removed for export] *)
Fixpoint lsf_cover (l : list kentry) (a : Z) : option Z :=
  match l with
  | [] => Some a
  | KZero (SA (ELit 0) b) (ELit n) :: l' => if (b =? a) && (0 <? n) then lsf_cover l' (a + n) else None
  | KWord (SA (ELit 0) b) w (ELit _) :: l' => if (b =? a) && (Nat.eqb w 1) then lsf_cover l' (a + 1) else None
  | KFill (SA (ELit 0) b) (ELit n) _ :: l' => if (b =? a) && (0 <? n) then lsf_cover l' (a + n) else None
  | _ => None
  end.
(* [comment removed for export] *)
Definition lsf_val (K : kentry) (x : Z) : Z :=
  match K with
  | KWord _ _ (ELit v) => v
  | KFill _ _ c => c
  | _ => 0
  end.
Fixpoint zr_all (f : Z -> bool) (a : Z) (n : nat) : bool :=
  match n with O => true | S k => f a && zr_all f (a + 1) k end.
Definition lsv (x : Z) : Z :=
  if (x <? 0x7fffc204) || (0x8000d498 <=? x) then 0 else AI_lowshadow.run_lookup AI_lowshadow.a_glob_shadow_runs x.
Lemma lsv_byte : forall x, AI_lowshadow.low_shadow_byte x = Z_to_bv 8 (lsv x).
Proof. intros x. unfold AI_lowshadow.low_shadow_byte, lsv. destruct (_ || _); reflexivity. Qed.
(* [comment removed for export] *)
Definition lsf_agree (K : kentry) : bool :=
  match K with
  | KZero (SA (ELit 0) b) (ELit n) => (b + n <=? 0x7fffc204) || (0x8000d498 <=? b) || zr_all (fun x => lsv x =? 0) b (Z.to_nat n)
  | KWord (SA (ELit 0) b) _ (ELit v) => (lsv b =? v) && (0 <=? v) && (v <? 256)
  | KFill (SA (ELit 0) b) (ELit n) c => zr_all (fun x => lsv x =? c) b (Z.to_nat n) && (0 <=? c) && (c <? 256)
  | _ => false
  end.

Lemma ls_facts_cover : lsf_cover ls_facts 0x7fffa000 = Some 0x800b8600.
Proof. vm_cast_no_check (@eq_refl (option Z) (Some 0x800b8600%Z)). Qed.
Lemma ls_facts_agree : forallb lsf_agree ls_facts = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
(* [comment removed for export] *)
Definition in_win (K : kentry) : bool :=
  match K with
  | KZero (SA (ELit 0) b) _ | KWord (SA (ELit 0) b) _ _ | KFill (SA (ELit 0) b) _ _ => (0x7fffa000 <=? b) && (b <? 0x800b8600)
  | _ => false
  end.
Definition hs_fact_win (K : kentry) : bool :=
  existsb (kentry_eqb K) (filter in_win (kn HS_s2_00)) && existsb (kentry_eqb K) (filter in_win (kn HS_s2_01))
  && existsb (kentry_eqb K) (filter in_win (kn HS_s2_10)) && existsb (kentry_eqb K) (filter in_win (kn HS_s2_11)).
Lemma existsb_filter_incl : forall {T} (f p : T -> bool) l, existsb f (filter p l) = true -> existsb f l = true.
Proof.
  intros T f p l. induction l as [|x l IH]; cbn; intros H; [exact H|].
  destruct (p x); cbn in H; [apply orb_prop in H as [H|H]; [rewrite H; reflexivity|]|]; rewrite (IH H); apply orb_true_r.
Qed.
Lemma hs_fact_win_sound : forall K, hs_fact_win K = true -> hs_fact K = true.
Proof.
  intros K H. unfold hs_fact_win in H. unfold hs_fact.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  rewrite (existsb_filter_incl _ _ _ H1), (existsb_filter_incl _ _ _ H2), (existsb_filter_incl _ _ _ H3), (existsb_filter_incl _ _ _ H4). reflexivity.
Qed.
Lemma forallb_impl : forall {T} (f g : T -> bool) l, (forall x, f x = true -> g x = true) -> forallb f l = true -> forallb g l = true.
Proof.
  intros T f g l Hfg. induction l as [|x l IH]; cbn; intros H; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (Hfg _ H1), (IH H2). reflexivity.
Qed.
Lemma ls_facts_known_win : forallb hs_fact_win ls_facts = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ls_facts_known : forallb hs_fact ls_facts = true.
Proof. exact (forallb_impl _ _ _ hs_fact_win_sound ls_facts_known_win). Qed.

Lemma zr_all_sound : forall f n a x, zr_all f a n = true -> a <= x < a + Z.of_nat n -> f x = true.
Proof.
  intros f n. induction n as [|n IH]; intros a x H Hx; [lia|]. cbn [zr_all] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec x a) as [->|NE]; [exact H1|]. apply (IH (a + 1)); [exact H2 | lia].
Qed.

(* [comment removed for export] *)
Lemma KI_1308633_1570824 : hs_fact (KImg 1309209 1571400) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_6162840_6162856 : hs_fact (KImg 6294360 6294376) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_6162860_6162864 : hs_fact (KImg 6294380 6294384) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_6162872_6162880 : hs_fact (KImg 6294392 6294400) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_6163144_6163408 : hs_fact (KImg 6294664 6294928) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_6163425_6163432 : hs_fact (KImg 6294945 6294952) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_6164480_6165608 : hs_fact (KImg 6296000 6298216) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_65536_681472 : hs_fact (KImg 65536 682088) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_681500_696960 : hs_fact (KImg 682116 697536) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_696969_697048 : hs_fact (KImg 697545 697624) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_714280_714296 : hs_fact (KImg 714856 714872) = true. Proof. vm_compute. reflexivity. Qed.
#[local] Hint Resolve KI_1308633_1570824 KI_6162840_6162856 KI_6162860_6162864 KI_6162872_6162880 KI_6163144_6163408 KI_6163425_6163432 KI_6164480_6165608 KI_65536_681472 KI_681500_696960 KI_696969_697048 KI_714280_714296 : kimg.
Section AtMain.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable hw : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable uid : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.
  Variable E : env.
  Variable R : bvmap 5 word.
  Variable FULL : word -> option byte.
  Variable model : Model.
  Variable hs : acs.
  Hypothesis Hhs : HS_MAIN hs.
  Hypothesis HC : cs_ok ASEGS ASAN5 LIM SINV argH fs E hs R FULL model.

  #[local] Notation MR := (Mr ASAN5 argH E hs model FULL).
  #[local] Notation FACT := (A_MainFacts.fact_sound sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC).
  #[local] Notation IMGW := (A_MainFacts.LibBridge.img_word_rw_cells sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs Hhs HC).
  #[local] Notation IMGU := (A_MainFacts.LibBridge.img_untouched_rw_cells sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs Hhs HC).
  #[local] Notation HIMRD := (A_MainFacts.high_mrd sp rdraw hw argv envp uid E FULL model hs).
  #[local] Notation IMGEW := (A_MainFacts.LibBridge.img_eword_rw_cells sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs Hhs HC).
  #[local] Notation RANGE := (A_MainFacts.range_fact sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC).
  (* [comment removed for export] *)
  Ltac ilia := unfold A_MainFacts.A_IMG_LO, A_MainFacts.A_IMG_HI; lia.

  (* [comment removed for export] *)
  Lemma z_fact : forall b n x, hs_fact (KZero (SA (ELit 0) b) (ELit n)) = true ->
    0 <= b -> 0 <= n -> b + n < 2^64 -> b <= x < b + n -> MR (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
  Proof.
    intros b n x HK Hb Hn Hbn Hx. pose proof (FACT _ HK) as [_ Hz]. unfold estart, elenZ in Hz. cbn [edenot a_base a_off] in Hz.
    rewrite !u64_lit in Hz by lia. replace x with (0 + b + (x - b)) by lia. apply Hz. lia.
  Qed.
  Lemma f_fact : forall b n c x, hs_fact (KFill (SA (ELit 0) b) (ELit n) c) = true ->
    0 <= b -> 0 <= n -> b + n < 2^64 -> b <= x < b + n -> MR (Z_to_bv 64 x) = Some (Z_to_bv 8 c).
  Proof.
    intros b n c x HK Hb Hn Hbn Hx. pose proof (FACT _ HK) as [_ Hz]. unfold estart, elenZ in Hz. cbn [edenot a_base a_off] in Hz.
    rewrite !u64_lit in Hz by lia. replace x with (0 + b + (x - b)) by lia. apply Hz. lia.
  Qed.
  Lemma w_fact : forall b v, hs_fact (KWord (SA (ELit 0) b) 1 (ELit v)) = true ->
    0x603000 <= b -> b < 2^64 -> 0 <= v < 256 -> MR (Z_to_bv 64 b) = Some (Z_to_bv 8 v).
  Proof.
    intros b v HK Hb Hb2 Hv. pose proof (FACT _ HK) as (_ & _ & Hr). unfold adenot in Hr. cbn [edenot a_base a_off] in Hr.
    unfold v_addi in Hr. rewrite u64_lit in Hr by lia. replace (0 + b) with b in Hr by lia.
    unfold word_to_le_bytes in Hr. cbn [Z_to_le_bytes] in Hr. rewrite u64_lit in Hr by lia.
    cbn [rdn] in Hr.
    replace (Common.PropExec.seg_rom ASEGS (Z_to_bv 64 b)) with (@None byte) in Hr
      by (symmetry; unfold Common.PropExec.seg_rom; rewrite AImageFacts.asan_memory_read_none by (cbn; rewrite ?u64_lit by lia; lia); reflexivity).
    destruct (MR (Z_to_bv 64 b)) as [bt|]; [|discriminate Hr]. injection Hr as <-. reflexivity.
  Qed.

  Lemma lsf_sound : forall l a e, lsf_cover l a = Some e -> forallb lsf_agree l = true -> forallb hs_fact l = true ->
    0x603000 <= a -> e < 2^64 ->
    forall x, a <= x < e -> MR (Z_to_bv 64 x) = Some (AI_lowshadow.low_shadow_byte x).
  Proof.
    induction l as [|K l IH]; intros a e CV AG HK Ha He x Hx.
    { cbn in CV. injection CV as <-. lia. }
    cbn [forallb] in AG, HK. apply andb_prop in AG as [AG1 AG]. apply andb_prop in HK as [HK1 HK].
    assert (MONO : forall l' a' e', lsf_cover l' a' = Some e' -> a' <= e').
    { clear. induction l' as [|K' l' IH']; intros a' e' CV'; cbn [lsf_cover] in CV'.
      - injection CV' as <-. lia.
      - destruct K' as [sa w v|sa n|sa n k|lo hi|e1 m1|e1 lo hi|sa n|a1 n1 a2 n2|sa n c|sa n]; try discriminate CV';
          destruct sa as [[z| | | | | | | ] off]; try discriminate CV'; destruct z; try discriminate CV';
          try (destruct v as [v| | | | | | | ]; try discriminate CV'); try (destruct n as [n| | | | | | | ]; try discriminate CV');
          match type of CV' with (if ?cnd then _ else _) = _ => destruct cnd eqn:EC; [|discriminate CV'] end;
          apply andb_prop in EC as [E1 E2]; apply Z.eqb_eq in E1; specialize (IH' _ _ CV');
          first [apply Z.ltb_lt in E2 | apply Nat.eqb_eq in E2]; lia. }
    cbn [lsf_cover] in CV.
    destruct K as [sa w v|sa n|sa n k|lo hi|e1 m1|e1 lo hi|sa n|a1 n1 a2 n2|sa n c|sa n]; try discriminate CV;
      destruct sa as [[z| | | | | | | ] off]; try discriminate CV; destruct z; try discriminate CV;
      try (destruct v as [v| | | | | | | ]; try discriminate CV); try (destruct n as [n| | | | | | | ]; try discriminate CV);
      match type of CV with (if ?cnd then _ else _) = _ => destruct cnd eqn:EC; [|discriminate CV] end;
      apply andb_prop in EC as [E1 E2]; apply Z.eqb_eq in E1; subst off; pose proof (MONO _ _ _ CV) as LE.
    - (* [comment removed for export] *) apply Nat.eqb_eq in E2. subst w. cbn [lsf_agree] in AG1.
      apply andb_prop in AG1 as [AG1 V2]. apply andb_prop in AG1 as [V0 V1]. apply Z.eqb_eq in V0. apply Z.leb_le in V1. apply Z.ltb_lt in V2.
      destruct (Z.eq_dec x a) as [->|NE].
      + rewrite lsv_byte, V0. apply w_fact; [exact HK1 | lia | lia | lia].
      + eapply IH; [exact CV | exact AG | exact HK | lia | lia | lia].
    - (* [comment removed for export] *) apply Z.ltb_lt in E2. cbn [lsf_agree] in AG1.
      destruct (Z_lt_dec x (a + n)) as [LT|GE].
      + rewrite lsv_byte. replace (lsv x) with 0; [apply (z_fact a n x HK1); lia|].
        apply orb_prop in AG1 as [AG1|AG1]; [apply orb_prop in AG1 as [AG1|AG1]|].
        * apply Z.leb_le in AG1. unfold lsv. destruct (Z.ltb_spec x 0x7fffc204); [reflexivity | exfalso; lia].
        * apply Z.leb_le in AG1. unfold lsv. destruct (Z.ltb_spec x 0x7fffc204); [reflexivity|]. destruct (Z.leb_spec 0x8000d498 x); [reflexivity | exfalso; lia].
        * symmetry. apply Z.eqb_eq. apply (zr_all_sound _ _ _ x AG1). rewrite Z2Nat.id by lia. lia.
      + eapply IH; [exact CV | exact AG | exact HK | lia | lia | lia].
    - (* [comment removed for export] *) apply Z.ltb_lt in E2. cbn [lsf_agree] in AG1.
      apply andb_prop in AG1 as [AG1 C2]. apply andb_prop in AG1 as [AG1 C1]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
      destruct (Z_lt_dec x (a + n)) as [LT|GE].
      + rewrite lsv_byte. replace (lsv x) with c; [apply (f_fact a n c x HK1); lia|].
        symmetry. apply Z.eqb_eq. apply (zr_all_sound _ _ _ x AG1). rewrite Z2Nat.id by lia. lia.
      + eapply IH; [exact CV | exact AG | exact HK | lia | lia | lia].
  Qed.

  Theorem at_main_low : AI_lowshadow.low_shadow_ok FULL.
  Proof.
    intros a Ha.
    pose proof (lsf_sound ls_facts _ _ ls_facts_cover ls_facts_agree ls_facts_known ltac:(lia) ltac:(lia) a Ha) as M.
    pose proof (HIMRD (Z_to_bv 64 a) _ ltac:(unfold A_MainFacts.A_IMG_HI; rewrite u64_lit by lia; lia) M) as [RD WV].
    unfold Mem.wa. split; [exact WV | exact RD].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rw_sub : forall m a bs k n,
    Step.rw_cells AImages.asegs m a [Cells.CB (length bs) bs] -> (k + n <= length bs)%nat ->
    Step.rw_cells AImages.asegs m (a + Z.of_nat k) [Cells.CB n (firstn n (skipn k bs))].
  Proof.
    intros m a bs k n [[WF (B0 & B1 & B2)] (W0 & W1 & W2)] LE. cbn [Cells.cells_bytes Cells.cbytes Cells.cells_size Cells.csize] in *.
    rewrite app_nil_r in B2, B1. rewrite Nat.add_0_r in W1, W2.
    assert (LEN : length (firstn n (skipn k bs)) = n) by (rewrite length_firstn, length_skipn; lia).
    split; [split; [cbn; exact (conj LEN I)|]|]; cbn [Cells.cells_bytes Cells.cbytes Cells.cells_size Cells.csize]; rewrite ?app_nil_r, ?Nat.add_0_r.
    - split; [lia|]. split; [rewrite LEN; lia|]. intros i Hi. rewrite LEN in Hi.
      rewrite <- Z.add_assoc, <- Nat2Z.inj_add, B2 by lia.
      rewrite nth_error_firstn. replace (Nat.ltb i n) with true by (symmetry; apply Nat.ltb_lt; lia).
      rewrite nth_error_skipn. reflexivity.
    - split; [lia|]. split; [lia|]. intros i Hi. replace (a + Z.of_nat k + i) with (a + (Z.of_nat k + i)) by lia. apply W2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
  Proof.
    induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate H; [reflexivity|].
    injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
  Qed.

  (* [comment removed for export] *)
  Ltac imgu lo hi a cs H :=
    let bs := eval vm_compute in (Cells.cells_bytes cs) in
    let n := eval vm_compute in (@length byte bs) in
    assert (H : Step.rw_cells AImages.asegs FULL a cs);
    [ eapply (InitMem.rw_cells_recast AImages.asegs FULL a [Cells.CB (length bs) bs] cs);
      [ apply (IMGU lo hi a bs); [first [solve [auto with kimg nocore] | vm_compute; reflexivity] | ilia | ilia | ilia | change (@length byte bs) with n; ilia | vm_compute; reflexivity]
      | cbn; repeat split; reflexivity
      | apply bytes_eq_of_unsigned; vm_compute; reflexivity
      | vm_compute; reflexivity ]
    | ].
  (* [comment removed for export] *)
  Ltac imgw a w v cs H :=
    assert (H : Step.rw_cells AImages.asegs FULL a cs);
    [ eapply (InitMem.rw_cells_recast AImages.asegs FULL a _ cs);
      [ apply (IMGW a w v); [vm_compute; reflexivity | ilia | cbn; ilia | vm_compute; reflexivity]
      | cbn; repeat split; reflexivity
      | apply bytes_eq_of_unsigned; vm_compute; reflexivity
      | vm_compute; reflexivity ]
    | ].
  (* [comment removed for export] *)
  Ltac imgws a w v k n cs H :=
    let H0 := fresh "HW" in
    pose proof (IMGW a w v ltac:(vm_compute; reflexivity) ltac:(ilia) ltac:(cbn; ilia) ltac:(vm_compute; reflexivity)) as H0;
    rewrite <- (CatExec.length_N_to_le_bytes w (Z_to_bv 64 v)) in H0 at 1;
    apply (rw_sub FULL a _ k n) in H0; [|rewrite CatExec.length_N_to_le_bytes; lia];
    assert (H : Step.rw_cells AImages.asegs FULL (a + Z.of_nat k) cs);
    [ eapply (InitMem.rw_cells_recast AImages.asegs FULL _ _ cs); [exact H0 | cbn; repeat split; reflexivity | apply bytes_eq_of_unsigned; vm_compute; reflexivity | vm_compute; reflexivity] | clear H0 ].

  (* [comment removed for export] *)
  Theorem at_main_icp : AI_shadow.icp_globals AImages.asegs FULL 0x7fff8000.   (* [comment removed for export] *)
  Proof.
    unfold AI_shadow.icp_globals, AI_shadow.A_GOT_SBPTR, AI_shadow.A_SBVAR, AI_shadow.A_GOT_RIC, AI_shadow.A_RIC,
      AI_shadow.A_REAL_MEMCPY, AI_shadow.A_REAL_MEMSET, AI_shadow.A_GOT_MIDBEG, AI_shadow.A_MIDBEG, AI_shadow.A_GOT_MIDEND,
      AI_shadow.A_MIDEND, AI_shadow.A_GOT_HIGHEND, AI_shadow.A_HIGHEND, AI_shadow.A_INITED, AI_shadow.A_MUSL_MEMCPY,
      AI_shadow.A_MUSL_MEMSET, AI_shadow.A_HIGHEND_VAL.
    imgu 65536 682088 0xa49b0 [Cells.C8 (Z_to_bv 64 0xadb78)] G1.
    imgw 0xadb78 8%nat 0x7fff8000 [Cells.C8 (Z_to_bv 64 0x7fff8000)] G2.
    imgu 65536 682088 0xa5518 [Cells.C8 (Z_to_bv 64 0xae859)] G3.
    imgw 0xae859 1%nat 1 [Cells.C1 (Z_to_bv 8 1)] G4.
    imgu 65536 682088 0xa6820 [Cells.C8 (Z_to_bv 64 0x9dcdc)] G5.
    imgu 65536 682088 0xa6828 [Cells.C8 (Z_to_bv 64 0x9e0e0)] G6.
    imgu 65536 682088 0xa49b8 [Cells.C8 (Z_to_bv 64 0xae868)] G7.
    imgu 714856 714872 0xae868 [Cells.C8 (Z_to_bv 64 0)] G8.
    imgu 65536 682088 0xa49c0 [Cells.C8 (Z_to_bv 64 0xae870)] G9.
    imgu 714856 714872 0xae870 [Cells.C8 (Z_to_bv 64 0)] G10.
    imgu 65536 682088 0xa49c8 [Cells.C8 (Z_to_bv 64 0xae860)] G11.
    imgw 0xae860 8%nat 0x7fffffffffff [Cells.C8 (Z_to_bv 64 0x7fffffffffff)] G12.
    imgw 0xae858 1%nat 1 [Cells.C1 (Z_to_bv 8 1)] G13.
    repeat (split; [assumption|]). lia.
  Qed.

  Theorem at_main_icp2 : AI_globals2.icp_globals2 AImages.asegs FULL.
  Proof.
    unfold AI_globals2.icp_globals2, AI_globals2.A_REAL_STRLEN, AI_globals2.A_MUSL_STRLEN, AI_globals2.A_REAL_READ, AI_globals2.A_MUSL_READ,
      AI_globals2.A_REAL_FWRITE, AI_globals2.A_MUSL_FWRITE, AI_globals2.A_REAL_VPRINTF, AI_globals2.A_MUSL_VPRINTF,
      AI_globals2.A_REAL_VFPRINTF, AI_globals2.A_MUSL_VFPRINTF, AI_globals2.A_REAL_STRNLEN, AI_globals2.A_MUSL_STRNLEN,
      AI_globals2.A_REAL_MEMCHR, AI_globals2.A_MUSL_MEMCHR, AI_globals2.A_GOT_CFLAGS, AI_globals2.A_CFLAGS,
      AI_globals2.A_CF_INTERCEPT_STRLEN, AI_globals2.A_CF_CHECK_PRINTF.
    imgu 65536 682088 0xa66c8 [Cells.C8 (Z_to_bv 64 0x9e32c)] G1.
    imgu 65536 682088 0xa66f8 [Cells.C8 (Z_to_bv 64 0xa33e0)] G2.
    imgu 65536 682088 0xa6700 [Cells.C8 (Z_to_bv 64 0x97d80)] G3.
    imgu 65536 682088 0xa6718 [Cells.C8 (Z_to_bv 64 0x9d588)] G4.
    imgu 65536 682088 0xa6720 [Cells.C8 (Z_to_bv 64 0x98008)] G5.
    imgu 65536 682088 0xa67d0 [Cells.C8 (Z_to_bv 64 0x9e568)] G6.
    imgu 65536 682088 0xa66e8 [Cells.C8 (Z_to_bv 64 0x9dbe0)] G7.
    imgu 65536 682088 0xa49a0 [Cells.C8 (Z_to_bv 64 0x13f6a8)] G8.
    imgws 0x13f7a0 8%nat 0x101010101010101 3%nat 1%nat [Cells.C1 (Z_to_bv 8 1)] G9.
    imgws 0x13f6f8 8%nat 0x100000000 4%nat 1%nat [Cells.C1 (Z_to_bv 8 1)] G10.
    change (0x13f7a0 + Z.of_nat 3) with 0x13f7a3 in G9. change (0x13f6f8 + Z.of_nat 4) with 0x13f6fc in G10.
    repeat (split; [assumption|]). exact I.
  Qed.

  (* [comment removed for export] *)
  Lemma rw_join : forall m A cs1 A2 cs2,
    Step.rw_cells AImages.asegs m A cs1 -> Step.rw_cells AImages.asegs m A2 cs2 -> A2 = A + Z.of_nat (Cells.cells_size cs1) ->
    Step.rw_cells AImages.asegs m A (cs1 ++ cs2).
  Proof.
    intros m A cs1 A2 cs2 [[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)] ->.
    pose proof (Cells.cells_bytes_length cs1 W1) as L1.
    split; [split|].
    - apply Cells.cells_wf_app. exact (conj W1 W2).
    - rewrite Cells.cells_bytes_app. apply Mem.bytes_at_app. split; [exact B1|]. rewrite L1. exact B2.
    - rewrite Cells.cells_size_app. split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (Cells.cells_size cs1))).
      + apply HW1. lia.
      + replace (A + i) with (A + Z.of_nat (Cells.cells_size cs1) + (i - Z.of_nat (Cells.cells_size cs1))) by lia. apply HW2. lia.
  Qed.
  Ltac join H1 H2 H := pose proof (rw_join _ _ _ _ _ H1 H2 ltac:(cbn; lia)) as H; cbn [app] in H; clear H1 H2.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma at_main_tid : exists t, Step.rw_cells AImages.asegs FULL 0x5e0a68 [Cells.C4 (Z_to_bv 64 t)] /\ 0 < t < 2^31.
  Proof.
    pose proof (IMGEW 0x5e0a68 4%nat (EVar 44) ltac:(vm_compute; reflexivity) ltac:(ilia) ltac:(cbn; ilia) ltac:(vm_compute; reflexivity)) as W.
    pose proof (RANGE (EVar 44) 1 4194303 ltac:(vm_compute; reflexivity)) as [R1 R2]. cbn [edenot] in R1, R2, W.
    set (t := bv_unsigned (ev E 44)) in *. exists t. split; [| lia].
    eapply (InitMem.rw_cells_recast AImages.asegs FULL); [exact W | cbn; exact (conj I I) | | reflexivity].
    cbn [Cells.cells_bytes Cells.cbytes]. unfold Mem.le4. subst t. rewrite MState.Z_to_bv_bv_unsigned. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma at_main_gtab : AX_unreg.globals_tab FULL.
  Proof.
    intros i Hi.
    do 69 (destruct i as [|i];
      [ lazymatch goal with |- exists sz nm md dy lc, Step.rw_cells _ _ ?addr _ =>
          let a := eval vm_compute in addr in
          let rr := eval vm_compute in (match RiscvSemantics.memory_read AImages.asegs (Z_to_bv 64 a) 64%N with Some l => l | None => @nil byte end) in
          let HR := fresh "HR" in
          pose proof (IMGU 682116 697536 a rr ltac:(first [solve [auto with kimg nocore] | vm_compute; reflexivity]) ltac:(ilia) ltac:(ilia) ltac:(ilia)
                        ltac:(change (@length byte rr) with 64%nat; ilia) ltac:(vm_compute; reflexivity)) as HR;
          exists (BvBase.le_bytes_to_word (firstn 8 (skipn 8 rr))), (BvBase.le_bytes_to_word (firstn 8 (skipn 24 rr))),
                 (BvBase.le_bytes_to_word (firstn 8 (skipn 32 rr))), (BvBase.le_bytes_to_word (firstn 8 (skipn 40 rr))),
                 (BvBase.le_bytes_to_word (firstn 8 (skipn 48 rr)));
          change addr with a;
          eapply (InitMem.rw_cells_recast AImages.asegs FULL); [exact HR | cbn; repeat split; reflexivity | apply bytes_eq_of_unsigned; vm_compute; reflexivity | vm_compute; reflexivity]
        end
      | ]).
    exfalso. lia.
  Qed.

  Theorem at_main_exit : exists t, AX_Exit.exit_statics FULL t.
  Proof.
    destruct at_main_tid as (t & TID & Ht). exists t. unfold AX_Exit.exit_statics.
    split; [exact TID|]. split; [exact Ht|].
    imgu 6294664 6294928 0x600d80 [Cells.C4 (Z_to_bv 64 0)] X1. split; [exact X1|].
    imgu 1309209 1571400 0x13fa20 [Cells.C1 (Z_to_bv 8 0)] X3. split; [exact X3|].
    split.
    { unfold AX_fini2.fini_statics.
      imgu 65536 682088 0xa5668 [Cells.C8 (Z_to_bv 64 0xa4448); Cells.C8 (Z_to_bv 64 0xa4438)] F1.
      imgu 65536 682088 0xa4438 [Cells.C8 (Z_to_bv 64 0x82450); Cells.C8 (Z_to_bv 64 0x31a78)] F2.
      imgu 65536 682088 0xa4980 [Cells.C8 (Z_to_bv 64 0x91bf4); Cells.C8 (Z_to_bv 64 0)] F3.
      imgu 65536 682088 0xa66c0 [Cells.C8 (Z_to_bv 64 0xa66c0)] F4.
      imgu 65536 682088 0xa5628 [Cells.C8 (Z_to_bv 64 0xa9380); Cells.C8 (Z_to_bv 64 0xaa4c0)] F5.
      exact (conj F1 (conj F2 (conj F3 (conj F4 F5)))). }
    split.
    { unfold AX_unreg.unreg_statics.
      imgu 65536 682088 0xa49a8 [Cells.C8 (Z_to_bv 64 0xab378)] U1.
      imgws 0xab390 8%nat 0x101010000000001 0%nat 4%nat [Cells.C4 (Z_to_bv 64 1)] U2. change (0xab390 + Z.of_nat 0) with 0xab390 in U2.
      imgu 65536 682088 0xa49b0 [Cells.C8 (Z_to_bv 64 0xadb78)] U3.
      imgw 0xadb78 8%nat 0x7fff8000 [Cells.C8 (Z_to_bv 64 0x7fff8000)] U4.
      imgu 65536 682088 0xa49b8 [Cells.C8 (Z_to_bv 64 0xae868)] U5.
      imgu 65536 682088 0xa49c0 [Cells.C8 (Z_to_bv 64 0xae870)] U6.
      imgu 65536 682088 0xa49c8 [Cells.C8 (Z_to_bv 64 0xae860)] U7.
      imgu 65536 682088 0xa49a0 [Cells.C8 (Z_to_bv 64 0x13f6a8)] U8.
      imgw 0x13f720 8%nat 18446744073709551615 [Cells.C8 (Z_to_bv 64 0xffffffffffffffff)] U9.
      imgu 65536 682088 0xa49d0 [Cells.C8 (Z_to_bv 64 0xa6828)] U10.
      imgu 65536 682088 0xa6828 [Cells.C8 (Z_to_bv 64 0x9e0e0)] U11.
      imgu 65536 682088 0xa4990 [Cells.C8 (Z_to_bv 64 0x13d620)] U12.
      imgw 0xae858 1%nat 1 [Cells.C1 (Z_to_bv 8 1)] U13.
      imgw 0xad3dc 1%nat 1 [Cells.C1 (Z_to_bv 8 1)] U14.
      repeat (split; [assumption|]). assumption. }
    split; [exact at_main_gtab|].
    imgu 697545 697624 0xaa510 [Cells.C1 (Z_to_bv 8 0)] X4. split; [exact X4|].
    imgw 0xaa4c0 8%nat 1 [Cells.C8 (Z_to_bv 64 1)] X5. split; [exact X5|].
    imgw 0xab430 8%nat 0 [Cells.C8 (Z_to_bv 64 0)] X6. exact X6.
  Qed.

  (* [comment removed for export] *)
  Theorem at_main_stdio : exists guard cdt thr sec tm1, AX_Exit.stdio_state FULL StdioBase.stdout_init guard cdt thr sec tm1.
  Proof.
    exists (ev E 61), (Z_to_bv 8 1), (Z_to_bv 8 0), (Z_to_bv 8 0), (Z_to_bv 64 0).
    unfold AX_Exit.stdio_state. split; [|split; [|split; [|split]]].
    - (* [comment removed for export] *)
      unfold AX_file.stdio_statics.
      imgw 0x600da0 1%nat 1 [Cells.C1 (Z_to_bv 8 1)] L1.
      imgu 6294945 6294952 0x600da1 [Cells.C1 (Z_to_bv 8 0); Cells.C1 (Z_to_bv 8 0); Cells.C1 (Z_to_bv 8 0); Cells.C4 (Z_to_bv 64 0)] L2.
      join L1 L2 L3.
      imgu 6296000 6298216 0x601208 [Cells.C8 (Z_to_bv 64 0)] O1.
      imgu 682116 697536 0xa9350 [Cells.C8 (Z_to_bv 64 0xa9268)] U1.
      imgu 682116 697536 0xa9260 [Cells.C8 (Z_to_bv 64 0xa9178)] U2.
      imgu 682116 697536 0xa9170 [Cells.C8 (Z_to_bv 64 0xa9088)] U3.
      exact (conj L3 (conj O1 (conj U1 (conj U2 U3)))).
    - (* [comment removed for export] *)
      unfold AX_file.stdin_file, AX_file.stdin_cells.
      imgu 682116 697536 0xa9268 AX_file.stdin_cells SI. exact SI.
    - (* [comment removed for export] *)
      unfold AX_file.stdout_file. cbn [StdioBase.so_active StdioBase.so_buf StdioBase.so_first StdioBase.so_lbf_nl StdioBase.stdout_init].
      exists (Z_to_bv 64 5), (Z_to_bv 64 0), (repeat (Z_to_bv 8 0) 80), (repeat (Z_to_bv 8 0) 1024).
      imgu 682116 697536 0xa9178 (AX_file.file_cells (Z_to_bv 64 5) 0 0 0 0x97ec8 0x601220 1024 1 (Z_to_bv 64 0) 10 (repeat (Z_to_bv 8 0) 80)) SO.
      imgu 6296000 6298216 0x601220 [Cells.CB 1024 (repeat (Z_to_bv 8 0) 1024)] SB.
      split; [exact SO|]. split; [reflexivity|]. split; [exact SB|]. split; [reflexivity|]. split; [unfold Prelim.zlength; cbn [length Z.of_nat]; lia|]. intros _; reflexivity.
    - (* [comment removed for export] *)
      unfold AX_file.stderr_wfile0.
      exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, 0, (repeat (Z_to_bv 8 0) 80).
      imgu 682116 697536 0xa9088 (AX_file.file_cells (Z_to_bv 64 5) 0 0 0 0x974c4 0x601218 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)) SER.
      split; [exact SER|]. split; [reflexivity|]. split; [left; reflexivity | lia].
    - (* [comment removed for export] *)
      unfold AX_file.ssp_cells, AM_syscalls.got_ssp, AM_syscalls.ssp_guard.
      imgu 65536 682088 0xa5638 [Cells.C8 (Z_to_bv 64 0x600b50)] G1.
      pose proof (IMGEW 0x600b50 8%nat (EVar 61) ltac:(vm_compute; reflexivity) ltac:(ilia) ltac:(cbn; ilia) ltac:(vm_compute; reflexivity)) as G2. cbn [edenot] in G2.
      assert (G2' : Step.rw_cells AImages.asegs FULL 0x600b50 [Cells.C8 (ev E 61)])
        by (eapply (InitMem.rw_cells_recast AImages.asegs FULL); [exact G2 | cbn; exact (conj I I) | reflexivity | reflexivity]).
      exact (conj G1 G2').
  Qed.

  (* [comment removed for export] *)
  Theorem at_main_yst : AYajlRep.ay_statics FULL.
  Proof.
    unfold AYajlRep.ay_statics, AYajlRep.AY_GOT_SHADOW, AYajlRep.AY_SHADOW_VAR, AYajlRep.AY_GOT_UAR, AYajlRep.AY_UAR_VAR, A_base.A_SB.
    imgu 65536 682088 0xa49b0 [Cells.C8 (Z_to_bv 64 0xadb78)] Y1.
    imgw 0xadb78 8%nat 0x7fff8000 [Cells.C8 (Z_to_bv 64 0x7fff8000)] Y2.
    imgu 65536 682088 0xa4a08 [Cells.C8 (Z_to_bv 64 0xadb80)] Y3.
    imgw 0xadb80 4%nat 1 [Cells.C4 (Z_to_bv 64 1)] Y4.
    exact (conj Y1 (conj Y2 (conj Y3 Y4))).
  Qed.

  Theorem at_main_ycl :
       Step.rw_cells AImages.asegs FULL AYajlRep.AY_CALLBACKS (RYajlRep.callbacks_cells AYajlRep.ayc)
    /\ Step.rw_cells AImages.asegs FULL AYajlRep.AY_BUF_ALLOC_ERROR (RYajlRep.buf_alloc_error_cells AYajlRep.ayc)
    /\ Step.rw_cells AImages.asegs FULL AYajlRep.AY_NOOP_ALLOCS AYajlRep.anoop_allocs_cells.
  Proof.
    unfold AYajlRep.AY_CALLBACKS, AYajlRep.AY_BUF_ALLOC_ERROR, AYajlRep.AY_NOOP_ALLOCS.
    imgu 682116 697536 0xa8f60 (RYajlRep.callbacks_cells AYajlRep.ayc) C1.
    imgu 682116 697536 0xa9020 (RYajlRep.buf_alloc_error_cells AYajlRep.ayc) C2.
    imgu 682116 697536 0xa8fe0 AYajlRep.anoop_allocs_cells C3.
    exact (conj C1 (conj C2 C3)).
  Qed.
End AtMain.
End RC__1.
