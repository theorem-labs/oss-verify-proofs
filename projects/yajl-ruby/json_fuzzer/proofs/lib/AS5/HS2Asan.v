(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the main phase's entry states computed in the build from the S2 run, per CONFIG_RSEQ value, in place of the recorded ones; the hand-off states collected in one run of the check, whose join collector the S2 plan, having no via, never calls; hs_argv_ok, the argument words at sp+8 and sp+16 of each entry state at its CONFIG_RSEQ value, with HS_s2a_argv and HS_s2b_argv). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanInit PlanRegen.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import AsanPlanImages5 A_Hooks5 PlanS2Asan CertS1Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* S2 runs from each S1 hand-off state (CertS1Asan.HS_s1) to the main phase's hand-offs 0 and 1.
   Its plan names fresh variables of the S1 run (EVar 374) and starts its own at the S1 hand-off
   states' counter, so it is renumbered by the S1 map. *)
Definition N2 : nat := vsh1 514.
Definition XN2 := A_Hooks5.XN5 ASEGS ASAN5 N2.
Definition IT2 : itab := mk_itab_ranges ASEGS s2_plan_ranges.
Definition s2_plan_k : plan := psh vsh1 s2_plan.
Definition s2_start (r : Z) (h : nat) : acs := hstate (fst (S1C r)) (init_acs_of r ASAN5) h.
Definition s2_run (r : Z) (h : nat) (H : nat -> option acs) : cres :=
  check ASEGS IT2 ASAN5 N2 AsanInit.LIMIT r XN2 XE0 XB0 H KC0 BFUEL FUEL None (s2_start r h) s2_plan_k.

Lemma HS_s1_start : forall r h ch, HS_s1 r h = Some ch -> s2_start r h = ch.
Proof.
  intros r h ch H. unfold s2_start, hstate.
  destruct h as [|[|h]]; cbn [HS_s1] in H; [rewrite H; reflexivity | rewrite H; reflexivity | discriminate H].
Qed.

(* the hand-off tables: [S2T_<r><a|b>] from S1 hand-off 0 (a) or 1 (b) at CONFIG_RSEQ value r.
   [s2_coll] is [s2_run]'s check written as [check_coll], which hands each state it reaches at a
   hand-off to [hvisit], so one run makes the map [collect_handoffs] makes in one run per state.
   The S2 plan has no via, so [check_coll]'s join collector is never called. *)
Definition s2_coll (r : Z) (h : nat) (bm : nat * list (nat * acs)) : cres * (nat * list (nat * acs)) :=
  check_coll ASEGS IT2 ASAN5 N2 AsanInit.LIMIT r XN2 XE0 XB0 KC0 BFUEL _ hvisit (fun _ _ _ m => m) (fun _ _ => None)
    FUEL None (s2_start r h) s2_plan_k bm.
Definition S2T_0a : list (nat * acs) := Eval vm_compute in collect_handoffs1 10 (s2_coll 0 0) [].
Definition S2T_0b : list (nat * acs) := Eval vm_compute in collect_handoffs1 10 (s2_coll 0 1) [].
Definition S2T_1a : list (nat * acs) := Eval vm_compute in collect_handoffs1 10 (s2_coll 1 0) [].
Definition S2T_1b : list (nat * acs) := Eval vm_compute in collect_handoffs1 10 (s2_coll 1 1) [].

(* the main phase's entry states: HS_s2_<S1 hand-off><S2 hand-off>, and R for CONFIG_RSEQ on *)
Definition HS_s2_00 : acs := Eval vm_compute in hstate S2T_0a (init_acs_of 0 ASAN5) 0.
Definition HS_s2_01 : acs := Eval vm_compute in hstate S2T_0a (init_acs_of 0 ASAN5) 1.
Definition HS_s2_10 : acs := Eval vm_compute in hstate S2T_0b (init_acs_of 0 ASAN5) 0.
Definition HS_s2_11 : acs := Eval vm_compute in hstate S2T_0b (init_acs_of 0 ASAN5) 1.
Definition HS_s2_00R : acs := Eval vm_compute in hstate S2T_1a (init_acs_of 1 ASAN5) 0.
Definition HS_s2_01R : acs := Eval vm_compute in hstate S2T_1a (init_acs_of 1 ASAN5) 1.
Definition HS_s2_10R : acs := Eval vm_compute in hstate S2T_1b (init_acs_of 1 ASAN5) 0.
Definition HS_s2_11R : acs := Eval vm_compute in hstate S2T_1b (init_acs_of 1 ASAN5) 1.

Definition HS_s2a (r : Z) (h : nat) : option acs :=
  match h with
  | 0%nat => Some (if Z.eqb r 1 then HS_s2_00R else HS_s2_00)
  | 1%nat => Some (if Z.eqb r 1 then HS_s2_01R else HS_s2_01)
  | _ => None
  end.
Definition HS_s2b (r : Z) (h : nat) : option acs :=
  match h with
  | 0%nat => Some (if Z.eqb r 1 then HS_s2_10R else HS_s2_10)
  | 1%nat => Some (if Z.eqb r 1 then HS_s2_11R else HS_s2_11)
  | _ => None
  end.

(* [comment removed for export] *)
Definition HS_MAIN (hs : acs) : Prop :=
  hs = HS_s2_00 \/ hs = HS_s2_01 \/ hs = HS_s2_10 \/ hs = HS_s2_11
  \/ hs = HS_s2_00R \/ hs = HS_s2_01R \/ hs = HS_s2_10R \/ hs = HS_s2_11R.

(* [HS_MAIN hs] split into its eight cases, [hs] replaced in each *)
Ltac hs_cases H := unfold HS_MAIN in H; destruct H as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]].

Lemma HS_s2a_main : forall r h ch, HS_s2a r h = Some ch -> HS_MAIN ch.
Proof.
  intros r h ch H. unfold HS_MAIN.
  destruct h as [|[|h]]; cbn [HS_s2a] in H; [| | discriminate H]; injection H as <-; destruct (Z.eqb r 1).
  - do 4 right. left. reflexivity.
  - left. reflexivity.
  - do 5 right. left. reflexivity.
  - right. left. reflexivity.
Qed.
Lemma HS_s2b_main : forall r h ch, HS_s2b r h = Some ch -> HS_MAIN ch.
Proof.
  intros r h ch H. unfold HS_MAIN.
  destruct h as [|[|h]]; cbn [HS_s2b] in H; [| | discriminate H]; injection H as <-; destruct (Z.eqb r 1).
  - do 6 right. left. reflexivity.
  - do 2 right. left. reflexivity.
  - do 7 right. reflexivity.
  - do 3 right. left. reflexivity.
Qed.

(* LPS 727298f3: the argument words main reads, at the run's own CONFIG_RSEQ value r.  The start state's word at
   sp+8 is argv[0]'s address [e_str0 r] and at sp+16 argv[1]'s ([e_argv1w r], or [e_str1 r] once the run has
   learnt argc >= 2); both move with the auxv's size [AUXSZ r], so an entry state of one value does not hold the
   other's words (the method of bzip2/bzip2_compress_target's K/A/HandoffArgv.v hs_argv_ok). *)
Definition hs_argv_ok (r : Z) (ch : acs) : bool :=
  (existsb (kentry_eqb (KWord (SA e_sp0 8) 8 (e_str0 r))) (kn ch)
   && (existsb (kentry_eqb (kw_argv1 (e_str1 r))) (kn ch) || existsb (kentry_eqb (kw_argv1 (e_argv1w r))) (kn ch)))%bool.

Lemma argv_ok_00 : hs_argv_ok 0 HS_s2_00 = true. Proof. vm_compute. reflexivity. Qed.
Lemma argv_ok_01 : hs_argv_ok 0 HS_s2_01 = true. Proof. vm_compute. reflexivity. Qed.
Lemma argv_ok_10 : hs_argv_ok 0 HS_s2_10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma argv_ok_11 : hs_argv_ok 0 HS_s2_11 = true. Proof. vm_compute. reflexivity. Qed.
Lemma argv_ok_00R : hs_argv_ok 1 HS_s2_00R = true. Proof. vm_compute. reflexivity. Qed.
Lemma argv_ok_01R : hs_argv_ok 1 HS_s2_01R = true. Proof. vm_compute. reflexivity. Qed.
Lemma argv_ok_10R : hs_argv_ok 1 HS_s2_10R = true. Proof. vm_compute. reflexivity. Qed.
Lemma argv_ok_11R : hs_argv_ok 1 HS_s2_11R = true. Proof. vm_compute. reflexivity. Qed.

(* the hand-off tables of the run at value [rseq_z b] give main entry states of that value *)
Lemma HS_s2a_argv : forall b h ch, HS_s2a (rseq_z b) h = Some ch -> hs_argv_ok (rseq_z b) ch = true.
Proof.
  intros [|] h ch H; destruct h as [|[|h]]; cbn [HS_s2a rseq_z Z.eqb Pos.eqb] in H; try discriminate H;
    injection H as <-.
  - exact argv_ok_00R.
  - exact argv_ok_01R.
  - exact argv_ok_00.
  - exact argv_ok_01.
Qed.
Lemma HS_s2b_argv : forall b h ch, HS_s2b (rseq_z b) h = Some ch -> hs_argv_ok (rseq_z b) ch = true.
Proof.
  intros [|] h ch H; destruct h as [|[|h]]; cbn [HS_s2b rseq_z Z.eqb Pos.eqb] in H; try discriminate H;
    injection H as <-.
  - exact argv_ok_10R.
  - exact argv_ok_11R.
  - exact argv_ok_10.
  - exact argv_ok_11.
Qed.
