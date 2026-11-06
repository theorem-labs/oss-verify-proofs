(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/plugin-hostd/fuzz_reply/lib/Reusable/YP0kM.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/plugin-hostd/fuzz_reply/lib/Reusable/YP0kM.v, with its module paths changed. *)
(* The run twins of YP0k.sym_run_soundP / sym_run_to_soundP that also export the run's access
   report (YK0x.msteps_acc) and that every access lies in the read window of the run's FIRST symbolic memory
   (YP09R.accs_in_rrange). The per-step fact is YP0kR.sym_step_soundR. The
   window stays the first one over the run because a step keeps the memory's skeleton (YP0k.sym_step_skeleton). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP00 YP0k YP09R YP0kR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YK0x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* The read window depends only on the skeleton (base, lo, hi, wlo, whi of each region). *)
Lemma in_rrange_skeleton : forall E rs rs' a,
  skeleton rs = skeleton rs' -> in_rrange E rs a -> in_rrange E rs' a.
Proof.
  intros E rs. induction rs as [|r rs IH]; intros rs' a Hsk (r0 & Hin & Hr0);
    destruct rs' as [|r' rs']; try (cbn in Hsk; discriminate); [destruct Hin|].
  pose proof (f_equal (@hd _ (skel r)) Hsk) as Hrr. pose proof (f_equal (@tl _) Hsk) as Hsk'.
  cbn [hd tl skeleton map] in Hrr, Hsk'. change (map skel rs = map skel rs') in Hsk'.
  destruct Hin as [<-|Hin].
  - exists r'. split; [left; reflexivity|].
    destruct r, r'. unfold skel in Hrr. cbn in Hrr, Hr0 |- *. inversion Hrr. subst. exact Hr0.
  - destruct (IH rs' a Hsk' (ex_intro _ r0 (conj Hin Hr0))) as (r1 & Hin1 & Hr1).
    exists r1. split; [right; exact Hin1 | exact Hr1].
Qed.

Lemma accs_in_rrange_skeleton : forall E rs rs' accs,
  skeleton rs = skeleton rs' -> accs_in_rrange E rs accs -> accs_in_rrange E rs' accs.
Proof. intros E rs rs' accs Hsk H a n k Hin Hk. exact (in_rrange_skeleton E rs rs' _ Hsk (H a n k Hin Hk)). Qed.

Lemma accs_in_rrange_app : forall E rs a1 a2,
  accs_in_rrange E rs a1 -> accs_in_rrange E rs a2 -> accs_in_rrange E rs (a1 ++ a2).
Proof. intros E rs a1 a2 H1 H2 a n k Hin Hk. apply in_app_or in Hin as [Hin|Hin]; [exact (H1 a n k Hin Hk) | exact (H2 a n k Hin Hk)]. Qed.

Lemma accs_in_rrange_nil : forall E rs, accs_in_rrange E rs [].
Proof. intros E rs a n k []. Qed.

Section d.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis Htbl : table_ok segs tbl.
Context {fx : FPState}.
Section g.
Variable P1 : env -> list sv -> bvmap 5 word -> Prop.
Variable P5 : list sv -> bv 32 -> Prop.
Local Notation st_okP := (st_okP segs P1 P5).
Local Notation st_okP_ecall := (st_okP_ecall segs P1 P5).

(* srrm-symsound's per-step soundness with the read window. *)
Let SOUND_R := sym_step_soundR segs tbl Htbl P1 P5.

(* An ecall step accesses no memory. *)
Lemma ecall_report_nil : forall E ss ss' ms,
  st_okP E ss ms -> sym_step segs tbl ss = SEcall ss' ->
  exists ms', msteps_acc segs ms ms' [] /\ st_okP_ecall E ss' ms' /\ ms_mem ms' = ms_mem ms /\ ss' = ss.
Proof.
  intros E ss ss' ms HS Hs.
  destruct (sym_step_ecallP segs tbl Htbl P1 P5 E ss ss' ms HS Hs) as (ms1 & Hstep & HS1 & Hm & Hss).
  unfold RiscvSemantics.step, drop_access_report in Hstep.
  destruct (step_accesses segs ms) as [[v rs]| |] eqn:Hsa; try discriminate. injection Hstep as <-.
  assert (Hp1 : ms_svc_pending v <> None) by (destruct HS1 as (_ & _ & Hp1 & _); rewrite Hp1; discriminate).
  destruct (step_accesses_ecall_shape segs ms v rs Hsa Hp1) as (Hrs & _). subst rs.
  exists v. split; [|split; [exact HS1 | split; [exact Hm | exact Hss]]].
  apply msteps_acc_one; [destruct HS as (_ & _ & Hp & _); exact Hp | exact Hsa].
Qed.

Theorem sym_run_soundM : forall fuel E ss ss' st ms,
  st_okP E ss ms -> sym_run segs tbl fuel ss = (ss', st) ->
  exists ms' accs, msteps_acc segs ms ms' accs /\
  match st with
  | RS_ecall => st_okP_ecall E ss' ms'
  | _ => st_okP E ss' ms'
  end /\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms')
  /\ accs_in_rrange E (ss_mem ss) accs.
Proof.
  induction fuel as [|fuel IH]; intros E ss ss' st ms HS H; cbn [sym_run] in H.
  - injection H as <- <-. exists ms, []. split; [apply msta_refl|]. split; [exact HS|].
    split; [reflexivity|]. split; [apply frame_of_refl | apply accs_in_rrange_nil].
  - destruct (sym_step segs tbl ss) as [ss1|ss1|why] eqn:Hs.
    + destruct (SOUND_R E ss ss1 ms HS Hs) as (ms1 & Hstep & HS1 & Hfr1 & rep & Hsa & Hv & Hw).
      pose proof (sym_step_skeleton segs tbl ss ss1 Hs) as Hsk1.
      destruct (IH E ss1 ss' st ms1 HS1 H) as (ms' & accs & Hms & HS' & Hsk & Hfr & Hw').
      destruct rep as [v rs]. cbn [access_value accessed_ranges] in Hv, Hw. subst v.
      exists ms', (rs ++ accs). split.
      { eapply msta_step; [destruct HS as (_ & _ & Hp & _); exact Hp | exact Hsa | exact Hms]. }
      split; [exact HS'|]. split; [congruence|]. split.
      { eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 | exact Hfr]. }
      apply accs_in_rrange_app; [exact Hw | exact (accs_in_rrange_skeleton E _ _ accs Hsk1 Hw')].
    + injection H as <- <-.
      destruct (ecall_report_nil E ss ss1 ms HS Hs) as (ms1 & Hms & HS1 & Hm & Hss). subst ss1.
      exists ms1, []. split; [exact Hms|]. split; [exact HS1|]. split; [reflexivity|].
      split; [rewrite Hm; apply frame_of_refl | apply accs_in_rrange_nil].
    + injection H as <- <-. exists ms, []. split; [apply msta_refl|]. split; [exact HS|].
      split; [reflexivity|]. split; [apply frame_of_refl | apply accs_in_rrange_nil].
Qed.

Theorem sym_run_to_soundM : forall fuel stop E ss ss' st ms,
  st_okP E ss ms -> sym_run_to segs tbl fuel stop ss = (ss', st) ->
  exists ms' accs, msteps_acc segs ms ms' accs /\
  match st with
  | RS_ecall => st_okP_ecall E ss' ms'
  | _ => st_okP E ss' ms'
  end /\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms')
  /\ accs_in_rrange E (ss_mem ss) accs.
Proof.
  induction fuel as [|fuel IH]; intros stop E ss ss' st ms HS H; cbn [sym_run_to] in H.
  - injection H as <- <-. exists ms, []. split; [apply msta_refl|]. split; [exact HS|].
    split; [reflexivity|]. split; [apply frame_of_refl | apply accs_in_rrange_nil].
  - destruct (ss_pc ss =? stop).
    { injection H as <- <-. exists ms, []. split; [apply msta_refl|]. split; [exact HS|].
      split; [reflexivity|]. split; [apply frame_of_refl | apply accs_in_rrange_nil]. }
    destruct (sym_step segs tbl ss) as [ss1|ss1|why] eqn:Hs.
    + destruct (SOUND_R E ss ss1 ms HS Hs) as (ms1 & Hstep & HS1 & Hfr1 & rep & Hsa & Hv & Hw).
      pose proof (sym_step_skeleton segs tbl ss ss1 Hs) as Hsk1.
      destruct (IH stop E ss1 ss' st ms1 HS1 H) as (ms' & accs & Hms & HS' & Hsk & Hfr & Hw').
      destruct rep as [v rs]. cbn [access_value accessed_ranges] in Hv, Hw. subst v.
      exists ms', (rs ++ accs). split.
      { eapply msta_step; [destruct HS as (_ & _ & Hp & _); exact Hp | exact Hsa | exact Hms]. }
      split; [exact HS'|]. split; [congruence|]. split.
      { eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 | exact Hfr]. }
      apply accs_in_rrange_app; [exact Hw | exact (accs_in_rrange_skeleton E _ _ accs Hsk1 Hw')].
    + injection H as <- <-.
      destruct (ecall_report_nil E ss ss1 ms HS Hs) as (ms1 & Hms & HS1 & Hm & Hss). subst ss1.
      exists ms1, []. split; [exact Hms|]. split; [exact HS1|]. split; [reflexivity|].
      split; [rewrite Hm; apply frame_of_refl | apply accs_in_rrange_nil].
    + injection H as <- <-. exists ms, []. split; [apply msta_refl|]. split; [exact HS|].
      split; [reflexivity|]. split; [apply frame_of_refl | apply accs_in_rrange_nil].
Qed.
End g.
End d.
