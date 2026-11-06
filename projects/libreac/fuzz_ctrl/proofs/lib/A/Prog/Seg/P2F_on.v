(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 134 of its 423 lines of code are new or changed and 107 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2F.v; 35 of its 89 lines of code are new or changed and 369 lines of the source are left out. *)
(* lib/A/Prog/Seg/P2F_on.v -- route (C) twin of Seg/P2F.v's footprint run of segment P2 (0x81b10 -> 0x81b14).
   Written by a Theorem Labs lane (piece W3a: P1, P1_70, P2, P4), with a Theorem Labs lane's 12:55Z consent for a
   `<S>F_on` twin of a run no other lane owns (P2F is in nobody's STARTED list).  Seg/P2F.v is UNCHANGED
   (blob 75f692c4dba, the file of record, on a working branch and on a Theorem Labs lane's fold a working branch
   4bae33fdf54; its rng table Seg/P2F.rng.tsv (a working note, not in this delivery) 672ea605af0 is unchanged too).
   rule 24: no function proved (a re-stated run of a transcribed segment).

   WHY.  a Theorem Labs lane's truth audit found the full-shadow `ctl_rt` FALSE at an AR state, so route (C) narrows the walk's
   cut to `A.ACtlRtC.ctl_rt_C B ly3 S3 mem3`, whose shadow part is `shadow_rw_on (cut_shadow B ly3 S3)` and
   `shadow_rw_on img_shadow`.  There is no converse of `ctl_rt_C_of_ctl_rt`, so a run that asks for the UNIVERSAL
   `A.AsanRT.shadow_rw mem` cannot be fed from a route-(C) cut.  `seg_P2_run_F` asks for it; this file states and
   proves the same run with the one shadow byte it needs instead.

   THE ONE CHANGE (a Theorem Labs lane's frozen form: `X_on`'s premise is `A.ShadowRwOn.shadow_rw_on X_shadow_R m`):
     `shadow_rw mem`  ->  `A.ShadowRwOn.shadow_rw_on (seg_P2_run_shadow_R fr) mem`,
   with `seg_P2_run_shadow_R fr := fun a => a = Sfr fr + 332`.  Every other binder, premise and post conjunct is
   `seg_P2_run_F`'s, character for character, and the proof is its proof with one step changed: the store's
   `store_ok` comes from the region at `Sfr fr + 332` instead of from the universal predicate.

   WHY THAT REGION IS EXACTLY RIGHT.  The segment is the single instruction `sb s2,332(s3)` with s3 = S(fr): it
   makes no instrumented check and no load, so the only shadow byte it touches is the one it STORES, and
   `p2_wv_store_ok` (Seg/P2.v:46) needs exactly that byte present and writable.  (Same reading as the auditor's
   rule for P1F, a Theorem Labs lane 11:45Z: R may name the bytes a store needs writable.)

   seg_P2_run_F_of_on recovers Seg/P2F.v's own statement from the twin through
   `A.ShadowRwOn.shadow_rw_on_of_shadow_rw`, and seg_P2_run_F_of_on_verbatim pins its type to
   `RF.seg_P2_run_F`'s by constr_eq, so the twin cannot drift from the file of record. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_b5 P1 P2.
(* the route-(C) leaf (A.ShadowRwOn.shadow_rw_on) and the run of record this file twins *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require P2F.
(* ExecF / StepF are REQUIRED here but imported only inside Module RFon below, as in Seg/P2F.v. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF StepF.
Import ListNotations.
(* Restore YK11.getr (the register read of the sl_run post-state) as the default, as P2.v and P2F.v do. *)
Import YK11.
Open Scope Z_scope.

Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.

Module RFon.
(* Inside this module only: StepF's step / finish (evtF goals) shadow the UL engine's (evt goals), then YK11
   restores getr, exactly as Seg/P2F.v's Module RF orders them. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.
Import YK11.
Open Scope Z_scope.

Section RunFOn.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}.

(* The one shadow byte the run touches: the frame-shadow byte `sb s2,332(s3)` stores, s3 = S(fr). *)
Definition seg_P2_run_shadow_R (fr : Z) : Z -> Prop := fun a => a = Sfr fr + 332.

(* ---- seg_P2: 0x81b10 -> 0x81b14.  sb s2,332(s3) with s3 = S(fr): the run writes the one frame-shadow byte
   [S(fr) + 332, S(fr) + 333).  Seg/P2F.v:76 with its `shadow_rw mem` premise narrowed. ---- *)
Lemma seg_P2_run_F_on : forall (regs : bvmap 5 word) (mem : word -> option byte) (fr : Z) (RNG : footprint),
  getr regs 19 = Z_to_bv 64 (Sfr fr) ->
  in_shadow (Sfr fr + 332) ->
  A.ShadowRwOn.shadow_rw_on (seg_P2_run_shadow_R fr) mem ->
  rng RNG (Sfr fr + 332) 1 ->
  evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x81b14 /\
        getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
        getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 26 = getr regs 26 /\
        getr R 19 = Z_to_bv 64 (Sfr fr) /\ getr R 27 = getr regs 27 /\
        getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
        exists bs, mem' = write_to_mem mem (wa (Sfr fr + 332)) bs /\ length bs = 1%nat))
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81b10) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem fr RNG Hr19 Hin332 Hshadow_rw Rsh.
  pose proof (in_shadow_range _ Hin332) as Hin332r.
  rewrite p2_mkR_of. rewrite Hr19. cbv [Frame.mkR].
  assert (HS : store_ok rsegs mem (wa (Sfr fr + 332)) 1 = true).
  { eapply (p2_wv_store_ok mem mem (Sfr fr + 332) 1); [ | apply wmono_refl | lia | lia ].
    intros i Hi. assert (i = 0) by lia. subst i. rewrite Z.add_0_r.
    exact (proj1 (Hshadow_rw _ eq_refl Hin332)). }
  step. finish.
  all: try reflexivity.
  all: eexists; split; [ reflexivity | first [ apply length_le1 | reflexivity ] ].
Qed.

(* Seg/P2F.v:76's own statement, back from the twin: the universal predicate gives every region. *)
Lemma seg_P2_run_F_of_on : forall (regs : bvmap 5 word) (mem : word -> option byte) (fr : Z) (RNG : footprint),
  getr regs 19 = Z_to_bv 64 (Sfr fr) ->
  in_shadow (Sfr fr + 332) ->
  shadow_rw mem ->
  rng RNG (Sfr fr + 332) 1 ->
  evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x81b14 /\
        getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
        getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 26 = getr regs 26 /\
        getr R 19 = Z_to_bv 64 (Sfr fr) /\ getr R 27 = getr regs 27 /\
        getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
        exists bs, mem' = write_to_mem mem (wa (Sfr fr + 332)) bs /\ length bs = 1%nat))
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81b10) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem fr RNG Hr19 Hin332 Hshadow_rw Rsh.
  exact (seg_P2_run_F_on regs mem fr RNG Hr19 Hin332
           (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ mem Hshadow_rw) Rsh).
Qed.

(* The statement above is Seg/P2F.v's, character for character (so the twin's post and premises cannot drift). *)
Check seg_P2_run_F_of_on.
Check P2F.RF.seg_P2_run_F.
Example seg_P2_run_F_of_on_verbatim : True.
Proof.
  lazymatch type of seg_P2_run_F_of_on with
  | ?T => lazymatch type of P2F.RF.seg_P2_run_F with ?U => constr_eq T U end
  end.
  exact I.
Qed.

End RunFOn.
End RFon.

(* The run lemma and its region, at this file's top level (Seg/P2F.v's convention). *)
Notation seg_P2_run_shadow_R := RFon.seg_P2_run_shadow_R.
Notation seg_P2_run_F_on := RFon.seg_P2_run_F_on.
Notation seg_P2_run_F_of_on := RFon.seg_P2_run_F_of_on.

Print Assumptions RFon.seg_P2_run_F_on.
