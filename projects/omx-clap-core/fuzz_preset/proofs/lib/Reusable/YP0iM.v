(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: lib/YP0iR.v, new, holds part of YP0i.v and YP09.v: sym_step_sh_soundP's
   shadow-arm proof steps (YP0i.v) and store_region's case split (YP09.v), reused in sym_step_sh_shadow_accs and
   store_region_in with the read-region bound accs_in_rrange (YP09R.v) added; new lemmas step_rep,
   step_accesses_on_fetch, sload_region_in, sstore_region_in, region_accs, accs_one, accs_two and
   sym_step_sh_soundR. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YP0iR.v; 99 of its 123 lines of code are new or changed and 158 lines of the source are left out. *)
(* The shadow-run twins of YP0i.sym_run_sh_soundP / sym_run_to_sh_soundP / msteps_run_sh /
   msteps_run_to_sh that also export the run's access report (YK0x.msteps_acc) and that every access lies in the read
   window of the run's first symbolic memory (YP09R.accs_in_rrange). The per-step fact is
   YP0iR.sym_step_sh_soundR. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK0o YK15.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP00 YP0k YP06 YP03 YP0i YP09R YP0kR YP0iR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YK0x YP0kM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section d.
Variable segs : list Segment.
Variable tbl : ctable.
Context {fx : FPState}.
Hypothesis Htbl : table_ok segs tbl.
Section e.
Variable P1 : env -> list sv -> bvmap 5 word -> Prop.
Variable P5 : list sv -> bv 32 -> Prop.
Local Notation st_okP := (st_okP segs P1 P5).
Local Notation st_okP_ecall := (st_okP_ecall segs P1 P5).

Lemma ecall_report_nil_sh : forall E ss ss' ms,
  st_okP E ss ms -> sym_step_sh segs tbl ss = SEcall ss' ->
  exists ms', msteps_acc segs ms ms' [] /\ st_okP_ecall E ss' ms' /\ ms_mem ms' = ms_mem ms /\ ss' = ss.
Proof.
  intros E ss ss' ms HS Hs.
  destruct (sym_step_sh_ecallP segs tbl Htbl P1 P5 E ss ss' ms HS Hs) as (ms1 & Hstep & HS1 & Hm & Hss).
  unfold RiscvSemantics.step, drop_access_report in Hstep.
  destruct (step_accesses segs ms) as [[v rs]| |] eqn:Hsa; try discriminate. injection Hstep as <-.
  assert (Hp1 : ms_svc_pending v <> None) by (destruct HS1 as (_ & _ & Hp1 & _); rewrite Hp1; discriminate).
  destruct (step_accesses_ecall_shape segs ms v rs Hsa Hp1) as (Hrs & _). subst rs.
  exists v. split; [|split; [exact HS1 | split; [exact Hm | exact Hss]]].
  apply msteps_acc_one; [destruct HS as (_ & _ & Hp & _); exact Hp | exact Hsa].
Qed.

Theorem sym_run_sh_soundM : forall fuel E ss ss' st ms,
  st_okP E ss ms -> sym_run_sh segs tbl fuel ss = (ss', st) ->
  exists ms' accs, msteps_acc segs ms ms' accs /\
  match st with
  | RS_ecall => st_okP_ecall E ss' ms'
  | _ => st_okP E ss' ms'
  end /\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms')
  /\ accs_in_rrange E (ss_mem ss) accs.
Proof.
  induction fuel as [|fuel IH]; intros E ss ss' st ms HS H; cbn [sym_run_sh] in H.
  - injection H as <- <-. exists ms, []. split; [apply msta_refl|]. split; [exact HS|].
    split; [reflexivity|]. split; [apply frame_of_refl | apply accs_in_rrange_nil].
  - destruct (sym_step_sh segs tbl ss) as [ss1|ss1|why] eqn:Hs.
    + destruct (sym_step_sh_soundR segs tbl Htbl P1 P5 E ss ss1 ms HS Hs)
        as (ms1 & Hstep & HS1 & Hfr1 & rep & Hsa & Hv & Hw).
      pose proof (sym_step_sh_skeleton segs tbl ss ss1 Hs) as Hsk1.
      destruct (IH E ss1 ss' st ms1 HS1 H) as (ms' & accs & Hms & HS' & Hsk & Hfr & Hw').
      destruct rep as [v rs]. cbn [access_value accessed_ranges] in Hv, Hw. subst v.
      exists ms', (rs ++ accs). split.
      { eapply msta_step; [destruct HS as (_ & _ & Hp & _); exact Hp | exact Hsa | exact Hms]. }
      split; [exact HS'|]. split; [congruence|]. split.
      { eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 | exact Hfr]. }
      apply accs_in_rrange_app; [exact Hw | exact (accs_in_rrange_skeleton E _ _ accs Hsk1 Hw')].
    + injection H as <- <-.
      destruct (ecall_report_nil_sh E ss ss1 ms HS Hs) as (ms1 & Hms & HS1 & Hm & Hss). subst ss1.
      exists ms1, []. split; [exact Hms|]. split; [exact HS1|]. split; [reflexivity|].
      split; [rewrite Hm; apply frame_of_refl | apply accs_in_rrange_nil].
    + injection H as <- <-. exists ms, []. split; [apply msta_refl|]. split; [exact HS|].
      split; [reflexivity|]. split; [apply frame_of_refl | apply accs_in_rrange_nil].
Qed.

Theorem sym_run_to_sh_soundM : forall fuel stop E ss ss' st ms,
  st_okP E ss ms -> sym_run_to_sh segs tbl fuel stop ss = (ss', st) ->
  exists ms' accs, msteps_acc segs ms ms' accs /\
  match st with
  | RS_ecall => st_okP_ecall E ss' ms'
  | _ => st_okP E ss' ms'
  end /\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms')
  /\ accs_in_rrange E (ss_mem ss) accs.
Proof.
  induction fuel as [|fuel IH]; intros stop E ss ss' st ms HS H; cbn [sym_run_to_sh] in H.
  - injection H as <- <-. exists ms, []. split; [apply msta_refl|]. split; [exact HS|].
    split; [reflexivity|]. split; [apply frame_of_refl | apply accs_in_rrange_nil].
  - destruct (ss_pc ss =? stop).
    { injection H as <- <-. exists ms, []. split; [apply msta_refl|]. split; [exact HS|].
      split; [reflexivity|]. split; [apply frame_of_refl | apply accs_in_rrange_nil]. }
    destruct (sym_step_sh segs tbl ss) as [ss1|ss1|why] eqn:Hs.
    + destruct (sym_step_sh_soundR segs tbl Htbl P1 P5 E ss ss1 ms HS Hs)
        as (ms1 & Hstep & HS1 & Hfr1 & rep & Hsa & Hv & Hw).
      pose proof (sym_step_sh_skeleton segs tbl ss ss1 Hs) as Hsk1.
      destruct (IH stop E ss1 ss' st ms1 HS1 H) as (ms' & accs & Hms & HS' & Hsk & Hfr & Hw').
      destruct rep as [v rs]. cbn [access_value accessed_ranges] in Hv, Hw. subst v.
      exists ms', (rs ++ accs). split.
      { eapply msta_step; [destruct HS as (_ & _ & Hp & _); exact Hp | exact Hsa | exact Hms]. }
      split; [exact HS'|]. split; [congruence|]. split.
      { eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 | exact Hfr]. }
      apply accs_in_rrange_app; [exact Hw | exact (accs_in_rrange_skeleton E _ _ accs Hsk1 Hw')].
    + injection H as <- <-.
      destruct (ecall_report_nil_sh E ss ss1 ms HS Hs) as (ms1 & Hms & HS1 & Hm & Hss). subst ss1.
      exists ms1, []. split; [exact Hms|]. split; [exact HS1|]. split; [reflexivity|].
      split; [rewrite Hm; apply frame_of_refl | apply accs_in_rrange_nil].
    + injection H as <- <-. exists ms, []. split; [apply msta_refl|]. split; [exact HS|].
      split; [reflexivity|]. split; [apply frame_of_refl | apply accs_in_rrange_nil].
Qed.
End e.

(* The st_ok instances (P1_pin / P5_pin), the forms YA0p's runners read. *)
Lemma msteps_run_shM : forall n E ss ss' st ms,
  st_ok segs E ss ms -> sym_runN_sh segs tbl n ss = (ss', st) ->
  exists ms' accs, msteps_acc segs ms ms' accs
  /\ match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end
  /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms')
  /\ accs_in_rrange E (ss_mem ss) accs.
Proof.
  intros n E ss ss' st ms HS Hrun.
  destruct (sym_run_sh_soundM P1_pin P5_pin (N.to_nat n) E ss ss' st ms HS Hrun)
    as (ms' & accs & Hms & HS' & _ & Hfr & Hw).
  exists ms', accs. auto.
Qed.

Lemma msteps_run_to_shM : forall n stop E ss ss' st ms,
  st_ok segs E ss ms -> sym_run_toN_sh segs tbl n stop ss = (ss', st) ->
  exists ms' accs, msteps_acc segs ms ms' accs
  /\ match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end
  /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms')
  /\ accs_in_rrange E (ss_mem ss) accs.
Proof.
  intros n stop E ss ss' st ms HS Hrun.
  destruct (sym_run_to_sh_soundM P1_pin P5_pin (N.to_nat n) stop E ss ss' st ms HS Hrun)
    as (ms' & accs & Hms & HS' & _ & Hfr & Hw).
  exists ms', accs. auto.
Qed.
End d.
