(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlanCore CatSim.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegProg SegExplore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjS1Ghost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP Require Import S1P_defs S1G_defs S1G_vcs S1G_cert S1G_ok.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Lemma S1G_vc_ok : forall d c, SG.gvc_list S1G_GV c = true -> SG.vc_holds SG (s1_gp d) c.
Proof. intros d c H. exact (SG.gvc_list_ok SG (s1_gp d) S1G_GV c (S1G_GV_ok d) H). Qed.

Theorem s1g_sound : forall d T E M rom ms, In T (SP.p_tm S1G ++ SP.p_xt S1G) -> SX.aw_genuine E (SP.p_A S1G) ->
  ST.tm_okF SG T E M rom ms -> SG.gholds (s1_gp d) E M (ST.t_ghost T) ->
  exists ms', ExecF.mstepsF SG (SX.fp_of (SP.p_A S1G) E) ms ms' /\ SP.prun_post SG (s1_gp d) S1G E M rom ms'.
Proof.
  intros d.
  exact (SP.pcheck_sound SG (s1_gp d) s1_gfp (SG.gvc_list S1G_GV) (s1_gp_frame d) (S1G_vc_ok d) S1G S1_IT 4000 true [] s1g_cert
           (SP.itab_ranges_sound SG _) ltac:(intros TA []) ltac:(intros Sm [])).
Qed.
Print Assumptions s1g_sound.

(* [comment removed for export] *)
Definition S1SUM : SP.summ := SP.SUMA (SP.p_G S1G) G0 (SP.p_ex S1G) (SP.p_W S1G) (SP.p_A S1G).

Theorem s1_summ_ok : forall d, SP.summ_ok SG (s1_gp d) S1SUM.
Proof.
  intros d.
  exact (SP.summ_of_pcheck SG (s1_gp d) s1_gfp (SG.gvc_list S1G_GV) (s1_gp_frame d) (S1G_vc_ok d) S1G S1_IT 4000 true [] G0 s1g_cert
           (SP.itab_ranges_sound SG _) ltac:(intros TA []) ltac:(intros Sm []) ltac:(left; reflexivity)).
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma G0_in : In G0 (SP.p_tm S1G ++ SP.p_xt S1G).
Proof. apply in_or_app. left. left. reflexivity. Qed.
Definition s1g_evt (d : list Z) :=
  SLib.prog_evt0 SG (s1_gp d) s1_gfp (SG.gvc_list S1G_GV) (s1_gp_frame d) (S1G_vc_ok d) S1G S1_IT 4000 true [] G0 s1g_cert
    (SP.itab_ranges_sound SG _) eq_refl (fun TA H => match H with end) (fun Sm H => match H with end)
    G0_in.
Check s1g_evt.
Print Assumptions s1_summ_ok.
