(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the justification of A/AMainEntry.v's main-phase data, moved here from A/AMainEntry.v (its MainFactsAsan lemmas) and stated over the start-up's final hand-off states as AsanBoot computes them at both rseq values, each fact renamed by the start-up's final renumbering (MainShift.v). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan PlanRegen.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require AsanBoot.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import MainExport MainExportFast MainShift.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AMainEntry.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AMainEntry.MainFactsAsan.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AMainEntry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* The main phase's data names the start-up's fresh variables by the numbers the recorded run gave them; the
   start-up's final renumbering maps them to this run's (launch variables 0..12 stay), and the start-up hands the
   main phase its valuation composed with it. *)
Definition main_vsh : nat -> nat := PlanRegen.tshift AsanBoot.AsanStartupCertS2.T_S2.
Lemma main_vsh_launch : forall n, (n < 13)%nat -> main_vsh n = n.
Proof. intros n Hn. do 13 (destruct n as [|n]; [vm_compute; reflexivity|]). lia. Qed.

(* the start-up's final hand-off states: hand-off 1 and 2 at the run's rseq value *)
Definition HM (r w : bool) : acs := if w then AsanBoot.AsanStartupCertS2.HS2_1 r else AsanBoot.AsanStartupCertS2.HS2_2 r.
Lemma HS2_HM : forall r h ch, AsanBoot.AsanStartupCertS2.HS2 r h = Some ch ->
  (h = 1%nat /\ ch = HM r true) \/ (h = 2%nat /\ ch = HM r false).
Proof.
  intros r h ch H. unfold AsanBoot.AsanStartupCertS2.HS2 in H.
  destruct (Nat.eqb_spec h 1) as [->|N1]; [left; injection H as <-; split; reflexivity|].
  destruct (Nat.eqb_spec h 2) as [->|N2]; [right; injection H as <-; split; reflexivity| discriminate H].
Qed.

Lemma HM_regs : forall r w, s_regs (a_ss (HM r w)) = s_regs (a_ss (HM false true)).
Proof. intros [|] [|]; vm_compute; reflexivity. Qed.
Lemma HM_pc : forall r w, pc (HM r w) = OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AMainEntry.AM_MAIN.
Proof. intros [|] [|]; vm_compute; reflexivity. Qed.
Lemma HM_fd : forall r w, a_fd (HM r w) = FdStd.
Proof. intros [|] [|]; vm_compute; reflexivity. Qed.
Lemma HM_brk : forall r w, a_brk (HM r w) = EVar (main_vsh asan_vmbrk).
Proof. intros [|] [|]; vm_compute; reflexivity. Qed.

Lemma asan_mem_facts_justified : forall r w,
  forallb (mjustify (kn (HM r w)) (var_ranges (kn (HM r w))) 65536 6287360)
    (map (mfsh main_vsh) ((asan_mem_facts ++ asan_mem_facts_w w) ++ asan_mem_facts_r r)) = true.
Proof. intros [|] [|]; apply mjustify_fast_sound; vm_cast_no_check (eq_refl true). Qed.
Lemma asan_pure_facts_justified : forall r w,
  forallb (pjustify (kn (HM r w)) (var_ranges (kn (HM r w))))
    (map (pfsh main_vsh) ((asan_pure_facts ++ asan_pure_facts_w w) ++ asan_pure_facts_r r)) = true.
Proof. intros [|] [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma asan_vis_justified : forall r w,
  vis_match (var_ranges (kn (HM r w))) (a_vis (HM r w)) (map (pzsh main_vsh) asan_vis_app) = true
  /\ vis_match (var_ranges (kn (HM r w))) (a_ghost (HM r w)) (map (pzsh main_vsh) asan_ghost) = true.
Proof. intros [|] [|]; split; vm_compute; reflexivity. Qed.
Lemma asan_ledger_justified : forall r w,
  ledger_xmatch (var_ranges (kn (HM r w))) (a_maps (HM r w)) (map (lesh main_vsh) asan_ledger) = true.
Proof. intros [|] [|]; vm_compute; reflexivity. Qed.
Lemma asan_consts : forall r w,
  a_totsz (HM r w) = asan_totsz /\ a_ylo (HM r w) = asan_ylo /\ a_eager (HM r w) = asan_eager /\ a_abytes (HM r w) = asan_abytes.
Proof. intros [|] [|]; repeat split; vm_compute; reflexivity. Qed.
