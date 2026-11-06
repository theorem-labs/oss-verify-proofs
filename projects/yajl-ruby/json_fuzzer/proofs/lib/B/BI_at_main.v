(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec CatExec ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AgentLib AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import AsanPlanImagesB HS2Both B_MainFacts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require AImages AImageFacts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require InitMem Step Cells Mem Frame MState.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require BI_shadow BI_globals2 BI_lowshadow BM_syscalls BX_file BX_fini2 BX_unreg BX_Exit BYajlRep.
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
  [KZero (SA (ELit 0) 0x7fffa000) (ELit 8716);
   KWord (SA (ELit 0) 0x7fffc20c) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc20d) (ELit 3) 249;
   KZero (SA (ELit 0) 0x7fffc210) (ELit 10);
   KWord (SA (ELit 0) 0x7fffc21a) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc21b) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc220) (ELit 4);
   KWord (SA (ELit 0) 0x7fffc224) 1 (ELit 1);
   KFill (SA (ELit 0) 0x7fffc225) (ELit 7) 249;
   KZero (SA (ELit 0) 0x7fffc22c) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc22e) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc22f) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc234) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc236) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc237) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc23c) (ELit 4);
   KFill (SA (ELit 0) 0x7fffc240) (ELit 4) 249;
   KZero (SA (ELit 0) 0x7fffc244) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc246) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc247) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc24c) (ELit 8);
   KWord (SA (ELit 0) 0x7fffc254) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc255) (ELit 3) 249;
   KZero (SA (ELit 0) 0x7fffc258) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc25a) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc25b) (ELit 5) 249;
   KWord (SA (ELit 0) 0x7fffc260) 1 (ELit 7);
   KFill (SA (ELit 0) 0x7fffc261) (ELit 3) 249;
   KZero (SA (ELit 0) 0x7fffc264) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc265) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc266) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc268) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc269) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc26a) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc26c) (ELit 34);
   KWord (SA (ELit 0) 0x7fffc28e) 1 (ELit 7);
   KFill (SA (ELit 0) 0x7fffc28f) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc294) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc295) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc296) (ELit 2) 249;
   KWord (SA (ELit 0) 0x7fffc298) 1 (ELit 4);
   KFill (SA (ELit 0) 0x7fffc299) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc29c) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc29d) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc2a0) 1 (ELit 4);
   KFill (SA (ELit 0) 0x7fffc2a1) (ELit 3) 249;
   KZero (SA (ELit 0) 0x7fffc2a4) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc2a5) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc2a6) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc2a8) (ELit 32);
   KFill (SA (ELit 0) 0x7fffc2c8) (ELit 8) 249;
   KWord (SA (ELit 0) 0x7fffc2d0) 1 (ELit 4);
   KFill (SA (ELit 0) 0x7fffc2d1) (ELit 3) 249;
   KZero (SA (ELit 0) 0x7fffc2d4) (ELit 9);
   KWord (SA (ELit 0) 0x7fffc2dd) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc2de) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc2e0) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc2e1) 1 (ELit 4);
   KFill (SA (ELit 0) 0x7fffc2e2) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc2e4) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc2e5) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc2e6) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc2e8) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc2e9) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc2ea) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc2ec) (ELit 2);
   KFill (SA (ELit 0) 0x7fffc2ee) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc2f0) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc2f1) 1 (ELit 7);
   KFill (SA (ELit 0) 0x7fffc2f2) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc2f4) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc2f6) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc2f7) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc2fc) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc2fd) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc2fe) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc300) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc301) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc302) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc304) (ELit 5);
   KWord (SA (ELit 0) 0x7fffc309) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc30a) (ELit 6) 249;
   KZero (SA (ELit 0) 0x7fffc310) (ELit 3);
   KWord (SA (ELit 0) 0x7fffc313) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc314) (ELit 4) 249;
   KZero (SA (ELit 0) 0x7fffc318) (ELit 31);
   KWord (SA (ELit 0) 0x7fffc337) 1 (ELit 4);
   KFill (SA (ELit 0) 0x7fffc338) (ELit 4) 249;
   KZero (SA (ELit 0) 0x7fffc33c) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc33d) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc33e) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc340) (ELit 6);
   KWord (SA (ELit 0) 0x7fffc346) 1 (ELit 1);
   KFill (SA (ELit 0) 0x7fffc347) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc34c) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc34e) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc34f) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc354) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc356) 1 (ELit 1);
   KFill (SA (ELit 0) 0x7fffc357) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc35c) (ELit 4);
   KWord (SA (ELit 0) 0x7fffc360) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc361) (ELit 7) 249;
   KZero (SA (ELit 0) 0x7fffc368) (ELit 5);
   KWord (SA (ELit 0) 0x7fffc36d) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc36e) (ELit 6) 249;
   KZero (SA (ELit 0) 0x7fffc374) (ELit 3);
   KWord (SA (ELit 0) 0x7fffc377) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc378) (ELit 4) 249;
   KZero (SA (ELit 0) 0x7fffc37c) (ELit 4);
   KWord (SA (ELit 0) 0x7fffc380) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc381) (ELit 7) 249;
   KZero (SA (ELit 0) 0x7fffc388) (ELit 7);
   KFill (SA (ELit 0) 0x7fffc38f) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc394) (ELit 6);
   KWord (SA (ELit 0) 0x7fffc39a) 1 (ELit 5);
   KFill (SA (ELit 0) 0x7fffc39b) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc3a0) (ELit 5);
   KWord (SA (ELit 0) 0x7fffc3a5) 1 (ELit 1);
   KFill (SA (ELit 0) 0x7fffc3a6) (ELit 6) 249;
   KZero (SA (ELit 0) 0x7fffc3ac) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc3ad) 1 (ELit 6);
   KFill (SA (ELit 0) 0x7fffc3ae) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc3b0) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc3b2) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc3b3) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc3b8) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc3ba) 1 (ELit 7);
   KFill (SA (ELit 0) 0x7fffc3bb) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc3c0) (ELit 8);
   KWord (SA (ELit 0) 0x7fffc3c8) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc3c9) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc3cc) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc3cd) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc3d0) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc3d1) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc3d4) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc3d5) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc3d8) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc3d9) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc3dc) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc3dd) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc3e0) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc3e1) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc3e4) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc3e5) (ELit 3) 249;
   KWord (SA (ELit 0) 0x7fffc3e8) 1 (ELit 2);
   KFill (SA (ELit 0) 0x7fffc3e9) (ELit 3) 249;
   KZero (SA (ELit 0) 0x7fffc3ec) (ELit 4);
   KWord (SA (ELit 0) 0x7fffc3f0) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc3f1) (ELit 7) 249;
   KZero (SA (ELit 0) 0x7fffc3f8) (ELit 2);
   KWord (SA (ELit 0) 0x7fffc3fa) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc3fb) (ELit 5) 249;
   KZero (SA (ELit 0) 0x7fffc400) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc401) 1 (ELit 4);
   KFill (SA (ELit 0) 0x7fffc402) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc404) (ELit 1);
   KWord (SA (ELit 0) 0x7fffc405) 1 (ELit 3);
   KFill (SA (ELit 0) 0x7fffc406) (ELit 2) 249;
   KZero (SA (ELit 0) 0x7fffc408) (ELit 69483);
   KFill (SA (ELit 0) 0x8000d373) (ELit 5) 249;
   KZero (SA (ELit 0) 0x8000d378) (ELit 4);
   KFill (SA (ELit 0) 0x8000d37c) (ELit 4) 249;
   KZero (SA (ELit 0) 0x8000d380) (ELit 4);
   KFill (SA (ELit 0) 0x8000d384) (ELit 4) 249;
   KZero (SA (ELit 0) 0x8000d388) (ELit 100);
   KFill (SA (ELit 0) 0x8000d3ec) (ELit 496) 249;
   KZero (SA (ELit 0) 0x8000d5dc) (ELit 700452)].

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
  if (x <? 0x7fffc20c) || (0x8000d5dc <=? x) then 0 else BI_lowshadow.run_lookup BI_lowshadow.a_glob_shadow_runs x.
Lemma lsv_byte : forall x, BI_lowshadow.low_shadow_byte x = Z_to_bv 8 (lsv x).
Proof. intros x. unfold BI_lowshadow.low_shadow_byte, lsv. destruct (_ || _); reflexivity. Qed.
(* [comment removed for export] *)
Definition lsf_agree (K : kentry) : bool :=
  match K with
  | KZero (SA (ELit 0) b) (ELit n) => (b + n <=? 0x7fffc20c) || (0x8000d5dc <=? b) || zr_all (fun x => lsv x =? 0) b (Z.to_nat n)
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
Lemma KI_1312153_1574344 : hs_fact (KImg 1311833 1574024) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_6166360_6166376 : hs_fact (KImg 6296984 6297000) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_6166380_6166384 : hs_fact (KImg 6297004 6297008) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_6166392_6166400 : hs_fact (KImg 6297016 6297024) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_6166664_6166928 : hs_fact (KImg 6297288 6297552) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_6166945_6166952 : hs_fact (KImg 6297569 6297576) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_6168000_6169128 : hs_fact (KImg 6298624 6300840) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_65536_685088 : hs_fact (KImg 65536 685128) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_685116_700480 : hs_fact (KImg 685156 700160) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_700489_700568 : hs_fact (KImg 700169 700248) = true. Proof. vm_compute. reflexivity. Qed.
Lemma KI_717800_717816 : hs_fact (KImg 717480 717496) = true. Proof. vm_compute. reflexivity. Qed.
#[local] Hint Resolve KI_1312153_1574344 KI_6166360_6166376 KI_6166380_6166384 KI_6166392_6166400 KI_6166664_6166928 KI_6166945_6166952 KI_6168000_6169128 KI_65536_685088 KI_685116_700480 KI_700489_700568 KI_717800_717816 : kimg.
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
  #[local] Notation SINV := (SINV0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 BPH sp rdraw argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.
  Variable E : env.
  Variable R : bvmap 5 word.
  Variable FULL : word -> option byte.
  Variable model : Model.
  Variable hs : acs.
  Hypothesis Hhs : HS_MAIN hs.
  Hypothesis HC : cs_ok BSEGS BOTH5 LIM SINV argH fs E hs R FULL model.

  #[local] Notation MR := (Mr BOTH5 argH E hs model FULL).
  #[local] Notation FACT := (B_MainFacts.fact_sound sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC).
  #[local] Notation IMGW := (B_MainFacts.LibBridge.img_word_rw_cells sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs Hhs HC).
  #[local] Notation IMGU := (B_MainFacts.LibBridge.img_untouched_rw_cells sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs Hhs HC).
  #[local] Notation HIMRD := (B_MainFacts.high_mrd sp rdraw hw argv envp uid E FULL model hs).
  #[local] Notation IMGEW := (B_MainFacts.LibBridge.img_eword_rw_cells sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs Hhs HC).
  #[local] Notation RANGE := (B_MainFacts.range_fact sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC).
  (* [comment removed for export] *)
  Ltac ilia := unfold B_MainFacts.A_IMG_LO, B_MainFacts.A_IMG_HI; lia.

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
    replace (Common.PropExec.seg_rom BSEGS (Z_to_bv 64 b)) with (@None byte) in Hr
      by (symmetry; unfold Common.PropExec.seg_rom; rewrite AImageFacts.both_memory_read_none by (cbn; rewrite ?u64_lit by lia; lia); reflexivity).
    destruct (MR (Z_to_bv 64 b)) as [bt|]; [|discriminate Hr]. injection Hr as <-. reflexivity.
  Qed.

  Lemma lsf_sound : forall l a e, lsf_cover l a = Some e -> forallb lsf_agree l = true -> forallb hs_fact l = true ->
    0x603000 <= a -> e < 2^64 ->
    forall x, a <= x < e -> MR (Z_to_bv 64 x) = Some (BI_lowshadow.low_shadow_byte x).
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
        * apply Z.leb_le in AG1. unfold lsv. destruct (Z.ltb_spec x 0x7fffc20c); [reflexivity | exfalso; lia].
        * apply Z.leb_le in AG1. unfold lsv. destruct (Z.ltb_spec x 0x7fffc20c); [reflexivity|]. destruct (Z.leb_spec 0x8000d5dc x); [reflexivity | exfalso; lia].
        * symmetry. apply Z.eqb_eq. apply (zr_all_sound _ _ _ x AG1). rewrite Z2Nat.id by lia. lia.
      + eapply IH; [exact CV | exact AG | exact HK | lia | lia | lia].
    - (* [comment removed for export] *) apply Z.ltb_lt in E2. cbn [lsf_agree] in AG1.
      apply andb_prop in AG1 as [AG1 C2]. apply andb_prop in AG1 as [AG1 C1]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
      destruct (Z_lt_dec x (a + n)) as [LT|GE].
      + rewrite lsv_byte. replace (lsv x) with c; [apply (f_fact a n c x HK1); lia|].
        symmetry. apply Z.eqb_eq. apply (zr_all_sound _ _ _ x AG1). rewrite Z2Nat.id by lia. lia.
      + eapply IH; [exact CV | exact AG | exact HK | lia | lia | lia].
  Qed.

  Theorem at_main_low : BI_lowshadow.low_shadow_ok FULL.
  Proof.
    intros a Ha.
    pose proof (lsf_sound ls_facts _ _ ls_facts_cover ls_facts_agree ls_facts_known ltac:(lia) ltac:(lia) a Ha) as M.
    pose proof (HIMRD (Z_to_bv 64 a) _ ltac:(unfold B_MainFacts.A_IMG_HI; rewrite u64_lit by lia; lia) M) as [RD WV].
    unfold Mem.wa. split; [exact WV | exact RD].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rw_sub : forall m a bs k n,
    Step.rw_cells AImages.bsegs m a [Cells.CB (length bs) bs] -> (k + n <= length bs)%nat ->
    Step.rw_cells AImages.bsegs m (a + Z.of_nat k) [Cells.CB n (firstn n (skipn k bs))].
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
    assert (H : Step.rw_cells AImages.bsegs FULL a cs);
    [ eapply (InitMem.rw_cells_recast AImages.bsegs FULL a [Cells.CB (length bs) bs] cs);
      [ apply (IMGU lo hi a bs); [first [solve [auto with kimg nocore] | vm_compute; reflexivity] | ilia | ilia | ilia | change (@length byte bs) with n; ilia | vm_compute; reflexivity]
      | cbn; repeat split; reflexivity
      | apply bytes_eq_of_unsigned; vm_compute; reflexivity
      | vm_compute; reflexivity ]
    | ].
  (* [comment removed for export] *)
  Ltac imgw a w v cs H :=
    assert (H : Step.rw_cells AImages.bsegs FULL a cs);
    [ eapply (InitMem.rw_cells_recast AImages.bsegs FULL a _ cs);
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
    assert (H : Step.rw_cells AImages.bsegs FULL (a + Z.of_nat k) cs);
    [ eapply (InitMem.rw_cells_recast AImages.bsegs FULL _ _ cs); [exact H0 | cbn; repeat split; reflexivity | apply bytes_eq_of_unsigned; vm_compute; reflexivity | vm_compute; reflexivity] | clear H0 ].

  (* [comment removed for export] *)
  Theorem at_main_icp : BI_shadow.icp_globals AImages.bsegs FULL 0x7fff8000.   (* [comment removed for export] *)
  Proof.
    unfold BI_shadow.icp_globals, BI_shadow.A_GOT_SBPTR, BI_shadow.A_SBVAR, BI_shadow.A_GOT_RIC, BI_shadow.A_RIC,
      BI_shadow.A_REAL_MEMCPY, BI_shadow.A_REAL_MEMSET, BI_shadow.A_GOT_MIDBEG, BI_shadow.A_MIDBEG, BI_shadow.A_GOT_MIDEND,
      BI_shadow.A_MIDEND, BI_shadow.A_GOT_HIGHEND, BI_shadow.A_HIGHEND, BI_shadow.A_INITED, BI_shadow.A_MUSL_MEMCPY,
      BI_shadow.A_MUSL_MEMSET, BI_shadow.A_HIGHEND_VAL.
    imgu 65536 685128 0xa55a0 [Cells.C8 (Z_to_bv 64 0xae5b8)] G1.
    imgw 0xae5b8 8%nat 0x7fff8000 [Cells.C8 (Z_to_bv 64 0x7fff8000)] G2.
    imgu 65536 685128 0xa6108 [Cells.C8 (Z_to_bv 64 0xaf299)] G3.
    imgw 0xaf299 1%nat 1 [Cells.C1 (Z_to_bv 8 1)] G4.
    imgu 65536 685128 0xa7400 [Cells.C8 (Z_to_bv 64 0x9e8cc)] G5.
    imgu 65536 685128 0xa7408 [Cells.C8 (Z_to_bv 64 0x9ecd0)] G6.
    imgu 65536 685128 0xa55a8 [Cells.C8 (Z_to_bv 64 0xaf2a8)] G7.
    imgu 717480 717496 0xaf2a8 [Cells.C8 (Z_to_bv 64 0)] G8.
    imgu 65536 685128 0xa55b0 [Cells.C8 (Z_to_bv 64 0xaf2b0)] G9.
    imgu 717480 717496 0xaf2b0 [Cells.C8 (Z_to_bv 64 0)] G10.
    imgu 65536 685128 0xa55b8 [Cells.C8 (Z_to_bv 64 0xaf2a0)] G11.
    imgw 0xaf2a0 8%nat 0x7fffffffffff [Cells.C8 (Z_to_bv 64 0x7fffffffffff)] G12.
    imgw 0xaf298 1%nat 1 [Cells.C1 (Z_to_bv 8 1)] G13.
    repeat (split; [assumption|]). lia.
  Qed.

  Theorem at_main_icp2 : BI_globals2.icp_globals2 AImages.bsegs FULL.
  Proof.
    unfold BI_globals2.icp_globals2, BI_globals2.A_REAL_STRLEN, BI_globals2.A_MUSL_STRLEN, BI_globals2.A_REAL_READ, BI_globals2.A_MUSL_READ,
      BI_globals2.A_REAL_FWRITE, BI_globals2.A_MUSL_FWRITE, BI_globals2.A_REAL_VPRINTF, BI_globals2.A_MUSL_VPRINTF,
      BI_globals2.A_REAL_VFPRINTF, BI_globals2.A_MUSL_VFPRINTF, BI_globals2.A_REAL_STRNLEN, BI_globals2.A_MUSL_STRNLEN,
      BI_globals2.A_REAL_MEMCHR, BI_globals2.A_MUSL_MEMCHR, BI_globals2.A_GOT_CFLAGS, BI_globals2.A_CFLAGS,
      BI_globals2.A_CF_INTERCEPT_STRLEN, BI_globals2.A_CF_CHECK_PRINTF.
    imgu 65536 685128 0xa72a8 [Cells.C8 (Z_to_bv 64 0x9ef1c)] G1.
    imgu 65536 685128 0xa72d8 [Cells.C8 (Z_to_bv 64 0xa3fd0)] G2.
    imgu 65536 685128 0xa72e0 [Cells.C8 (Z_to_bv 64 0x98970)] G3.
    imgu 65536 685128 0xa72f8 [Cells.C8 (Z_to_bv 64 0x9e178)] G4.
    imgu 65536 685128 0xa7300 [Cells.C8 (Z_to_bv 64 0x98bf8)] G5.
    imgu 65536 685128 0xa73b0 [Cells.C8 (Z_to_bv 64 0x9f158)] G6.
    imgu 65536 685128 0xa72c8 [Cells.C8 (Z_to_bv 64 0x9e7d0)] G7.
    imgu 65536 685128 0xa5590 [Cells.C8 (Z_to_bv 64 0x1400e8)] G8.
    imgws 0x1401e0 8%nat 0x101010101010101 3%nat 1%nat [Cells.C1 (Z_to_bv 8 1)] G9.
    imgws 0x140138 8%nat 0x100000000 4%nat 1%nat [Cells.C1 (Z_to_bv 8 1)] G10.
    change (0x1401e0 + Z.of_nat 3) with 0x1401e3 in G9. change (0x140138 + Z.of_nat 4) with 0x14013c in G10.
    repeat (split; [assumption|]). exact I.
  Qed.

  (* [comment removed for export] *)
  Lemma rw_join : forall m A cs1 A2 cs2,
    Step.rw_cells AImages.bsegs m A cs1 -> Step.rw_cells AImages.bsegs m A2 cs2 -> A2 = A + Z.of_nat (Cells.cells_size cs1) ->
    Step.rw_cells AImages.bsegs m A (cs1 ++ cs2).
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
  Lemma at_main_tid : exists t, Step.rw_cells AImages.bsegs FULL 0x5e14a8 [Cells.C4 (Z_to_bv 64 t)] /\ 0 < t < 2^31.
  Proof.
    pose proof (IMGEW 0x5e14a8 4%nat (EVar 44) ltac:(vm_compute; reflexivity) ltac:(ilia) ltac:(cbn; ilia) ltac:(vm_compute; reflexivity)) as W.
    pose proof (RANGE (EVar 44) 1 4194303 ltac:(vm_compute; reflexivity)) as [R1 R2]. cbn [edenot] in R1, R2, W.
    set (t := bv_unsigned (ev E 44)) in *. exists t. split; [| lia].
    eapply (InitMem.rw_cells_recast AImages.bsegs FULL); [exact W | cbn; exact (conj I I) | | reflexivity].
    cbn [Cells.cells_bytes Cells.cbytes]. unfold Mem.le4. subst t. rewrite MState.Z_to_bv_bv_unsigned. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma at_main_gtab : BX_unreg.globals_tab FULL.
  Proof.
    intros i Hi.
    do 62 (destruct i as [|i];
      [ lazymatch goal with |- exists sz nm md dy lc, Step.rw_cells _ _ ?addr _ =>
          let a := eval vm_compute in addr in
          let rr := eval vm_compute in (match RiscvSemantics.memory_read AImages.bsegs (Z_to_bv 64 a) 64%N with Some l => l | None => @nil byte end) in
          let HR := fresh "HR" in
          pose proof (IMGU 685156 700160 a rr ltac:(first [solve [auto with kimg nocore] | vm_compute; reflexivity]) ltac:(ilia) ltac:(ilia) ltac:(ilia)
                        ltac:(change (@length byte rr) with 64%nat; ilia) ltac:(vm_compute; reflexivity)) as HR;
          exists (BvBase.le_bytes_to_word (firstn 8 (skipn 8 rr))), (BvBase.le_bytes_to_word (firstn 8 (skipn 24 rr))),
                 (BvBase.le_bytes_to_word (firstn 8 (skipn 32 rr))), (BvBase.le_bytes_to_word (firstn 8 (skipn 40 rr))),
                 (BvBase.le_bytes_to_word (firstn 8 (skipn 48 rr)));
          change addr with a;
          eapply (InitMem.rw_cells_recast AImages.bsegs FULL); [exact HR | cbn; repeat split; reflexivity | apply bytes_eq_of_unsigned; vm_compute; reflexivity | vm_compute; reflexivity]
        end
      | ]).
    exfalso. lia.
  Qed.

  Theorem at_main_exit : exists t, BX_Exit.exit_statics FULL t.
  Proof.
    destruct at_main_tid as (t & TID & Ht). exists t. unfold BX_Exit.exit_statics.
    split; [exact TID|]. split; [exact Ht|].
    imgu 6297288 6297552 0x6017c0 [Cells.C4 (Z_to_bv 64 0)] X1. split; [exact X1|].
    imgu 1311833 1574024 0x140460 [Cells.C1 (Z_to_bv 8 0)] X3. split; [exact X3|].
    split.
    { unfold BX_fini2.fini_statics.
      imgu 65536 685128 0xa6258 [Cells.C8 (Z_to_bv 64 0xa5038); Cells.C8 (Z_to_bv 64 0xa5028)] F1.
      imgu 65536 685128 0xa5028 [Cells.C8 (Z_to_bv 64 0x822fc); Cells.C8 (Z_to_bv 64 0x31884)] F2.
      imgu 65536 685128 0xa5570 [Cells.C8 (Z_to_bv 64 0x927e4); Cells.C8 (Z_to_bv 64 0)] F3.
      imgu 65536 685128 0xa72a0 [Cells.C8 (Z_to_bv 64 0xa72a0)] F4.
      imgu 65536 685128 0xa6218 [Cells.C8 (Z_to_bv 64 0xa9f60); Cells.C8 (Z_to_bv 64 0xaaee0)] F5.
      exact (conj F1 (conj F2 (conj F3 (conj F4 F5)))). }
    split.
    { unfold BX_unreg.unreg_statics.
      imgu 65536 685128 0xa5598 [Cells.C8 (Z_to_bv 64 0xabdb8)] U1.
      imgws 0xabdd0 8%nat 0x101010000000001 0%nat 4%nat [Cells.C4 (Z_to_bv 64 1)] U2. change (0xabdd0 + Z.of_nat 0) with 0xabdd0 in U2.
      imgu 65536 685128 0xa55a0 [Cells.C8 (Z_to_bv 64 0xae5b8)] U3.
      imgw 0xae5b8 8%nat 0x7fff8000 [Cells.C8 (Z_to_bv 64 0x7fff8000)] U4.
      imgu 65536 685128 0xa55a8 [Cells.C8 (Z_to_bv 64 0xaf2a8)] U5.
      imgu 65536 685128 0xa55b0 [Cells.C8 (Z_to_bv 64 0xaf2b0)] U6.
      imgu 65536 685128 0xa55b8 [Cells.C8 (Z_to_bv 64 0xaf2a0)] U7.
      imgu 65536 685128 0xa5590 [Cells.C8 (Z_to_bv 64 0x1400e8)] U8.
      imgw 0x140160 8%nat 18446744073709551615 [Cells.C8 (Z_to_bv 64 0xffffffffffffffff)] U9.
      imgu 65536 685128 0xa55c0 [Cells.C8 (Z_to_bv 64 0xa7408)] U10.
      imgu 65536 685128 0xa7408 [Cells.C8 (Z_to_bv 64 0x9ecd0)] U11.
      imgu 65536 685128 0xa5580 [Cells.C8 (Z_to_bv 64 0x13e060)] U12.
      imgw 0xaf298 1%nat 1 [Cells.C1 (Z_to_bv 8 1)] U13.
      imgw 0xade1c 1%nat 1 [Cells.C1 (Z_to_bv 8 1)] U14.
      repeat (split; [assumption|]). assumption. }
    split; [exact at_main_gtab|].
    imgu 700169 700248 0xaaf50 [Cells.C1 (Z_to_bv 8 0)] X4. split; [exact X4|].
    imgw 0xaaf00 8%nat 1 [Cells.C8 (Z_to_bv 64 1)] X5. split; [exact X5|].
    imgw 0xabe70 8%nat 0 [Cells.C8 (Z_to_bv 64 0)] X6. exact X6.
  Qed.

  (* [comment removed for export] *)
  Theorem at_main_stdio : exists guard cdt thr sec tm1, BX_Exit.stdio_state FULL StdioBase.stdout_init guard cdt thr sec tm1.
  Proof.
    exists (ev E 61), (Z_to_bv 8 1), (Z_to_bv 8 0), (Z_to_bv 8 0), (Z_to_bv 64 0).
    unfold BX_Exit.stdio_state. split; [|split; [|split; [|split]]].
    - (* [comment removed for export] *)
      unfold BX_file.stdio_statics.
      imgw 0x6017e0 1%nat 1 [Cells.C1 (Z_to_bv 8 1)] L1.
      imgu 6297569 6297576 0x6017e1 [Cells.C1 (Z_to_bv 8 0); Cells.C1 (Z_to_bv 8 0); Cells.C1 (Z_to_bv 8 0); Cells.C4 (Z_to_bv 64 0)] L2.
      join L1 L2 L3.
      imgu 6298624 6300840 0x601c48 [Cells.C8 (Z_to_bv 64 0)] O1.
      imgu 685156 700160 0xa9f30 [Cells.C8 (Z_to_bv 64 0xa9e48)] U1.
      imgu 685156 700160 0xa9e40 [Cells.C8 (Z_to_bv 64 0xa9d58)] U2.
      imgu 685156 700160 0xa9d50 [Cells.C8 (Z_to_bv 64 0xa9c68)] U3.
      exact (conj L3 (conj O1 (conj U1 (conj U2 U3)))).
    - (* [comment removed for export] *)
      unfold BX_file.stdin_file, BX_file.stdin_cells.
      imgu 685156 700160 0xa9e48 BX_file.stdin_cells SI. exact SI.
    - (* [comment removed for export] *)
      unfold BX_file.stdout_file. cbn [StdioBase.so_active StdioBase.so_buf StdioBase.so_first StdioBase.so_lbf_nl StdioBase.stdout_init].
      exists (Z_to_bv 64 5), (Z_to_bv 64 0), (repeat (Z_to_bv 8 0) 80), (repeat (Z_to_bv 8 0) 1024).
      imgu 685156 700160 0xa9d58 (BX_file.file_cells (Z_to_bv 64 5) 0 0 0 0x98ab8 0x601c60 1024 1 (Z_to_bv 64 0) 10 (repeat (Z_to_bv 8 0) 80)) SO.
      imgu 6298624 6300840 0x601c60 [Cells.CB 1024 (repeat (Z_to_bv 8 0) 1024)] SB.
      split; [exact SO|]. split; [reflexivity|]. split; [exact SB|]. split; [reflexivity|]. split; [unfold Prelim.zlength; cbn [length Z.of_nat]; lia|]. intros _; reflexivity.
    - (* [comment removed for export] *)
      unfold BX_file.stderr_wfile0.
      exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, 0, (repeat (Z_to_bv 8 0) 80).
      imgu 685156 700160 0xa9c68 (BX_file.file_cells (Z_to_bv 64 5) 0 0 0 0x980b4 0x601c58 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)) SER.
      split; [exact SER|]. split; [reflexivity|]. split; [left; reflexivity | lia].
    - (* [comment removed for export] *)
      unfold BX_file.ssp_cells, BM_syscalls.got_ssp, BM_syscalls.ssp_guard.
      imgu 65536 685128 0xa6228 [Cells.C8 (Z_to_bv 64 0x601590)] G1.
      pose proof (IMGEW 0x601590 8%nat (EVar 61) ltac:(vm_compute; reflexivity) ltac:(ilia) ltac:(cbn; ilia) ltac:(vm_compute; reflexivity)) as G2. cbn [edenot] in G2.
      assert (G2' : Step.rw_cells AImages.bsegs FULL 0x601590 [Cells.C8 (ev E 61)])
        by (eapply (InitMem.rw_cells_recast AImages.bsegs FULL); [exact G2 | cbn; exact (conj I I) | reflexivity | reflexivity]).
      exact (conj G1 G2').
  Qed.

  (* [comment removed for export] *)
  Theorem at_main_yst : BYajlRep.ay_statics FULL.
  Proof.
    unfold BYajlRep.ay_statics, BYajlRep.AY_GOT_SHADOW, BYajlRep.AY_SHADOW_VAR, BYajlRep.AY_GOT_UAR, BYajlRep.AY_UAR_VAR, B_base.A_SB.
    imgu 65536 685128 0xa55a0 [Cells.C8 (Z_to_bv 64 0xae5b8)] Y1.
    imgw 0xae5b8 8%nat 0x7fff8000 [Cells.C8 (Z_to_bv 64 0x7fff8000)] Y2.
    imgu 65536 685128 0xa55f8 [Cells.C8 (Z_to_bv 64 0xae5c0)] Y3.
    imgw 0xae5c0 4%nat 1 [Cells.C4 (Z_to_bv 64 1)] Y4.
    exact (conj Y1 (conj Y2 (conj Y3 Y4))).
  Qed.

  Theorem at_main_ycl :
       Step.rw_cells AImages.bsegs FULL BYajlRep.AY_CALLBACKS (RYajlRep.callbacks_cells BYajlRep.ayc)
    /\ Step.rw_cells AImages.bsegs FULL BYajlRep.AY_BUF_ALLOC_ERROR (RYajlRep.buf_alloc_error_cells BYajlRep.ayc)
    /\ Step.rw_cells AImages.bsegs FULL BYajlRep.AY_NOOP_ALLOCS BYajlRep.anoop_allocs_cells.
  Proof.
    unfold BYajlRep.AY_CALLBACKS, BYajlRep.AY_BUF_ALLOC_ERROR, BYajlRep.AY_NOOP_ALLOCS.
    imgu 685156 700160 0xa9b40 (RYajlRep.callbacks_cells BYajlRep.ayc) C1.
    imgu 685156 700160 0xa9c00 (RYajlRep.buf_alloc_error_cells BYajlRep.ayc) C2.
    imgu 685156 700160 0xa9bc0 BYajlRep.anoop_allocs_cells C3.
    exact (conj C1 (conj C2 C3)).
  Qed.
End AtMain.
End RC__1.
