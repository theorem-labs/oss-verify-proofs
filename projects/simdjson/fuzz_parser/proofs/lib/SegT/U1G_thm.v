(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlanCore CatSim.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegProg SegExplore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjS1Ghost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegT Require Import U1G_defs U1G_vcs U1G_cert U1G_ok.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Lemma U1G_vc_ok : forall d c, SG.gvc_list U1G_GV c = true -> SG.vc_holds SG (s1_gp d) c.
Proof. intros d c H. exact (SG.gvc_list_ok SG (s1_gp d) U1G_GV c (U1G_GV_ok d) H). Qed.

Section S.
Variable d : list Z.

Theorem u1g_sound : forall T E M rom ms, In T (SP.p_tm U1G ++ SP.p_xt U1G) -> SX.aw_genuine E (SP.p_A U1G) ->
  ST.tm_okF SG T E M rom ms -> SG.gholds (s1_gp d) E M (ST.t_ghost T) ->
  exists ms', ExecF.mstepsF SG (SX.fp_of (SP.p_A U1G) E) ms ms' /\ SP.prun_post SG (s1_gp d) U1G E M rom ms'.
Proof.
  exact (SP.pcheck_sound SG (s1_gp d) s1_gfp (SG.gvc_list U1G_GV) (s1_gp_frame d) (U1G_vc_ok d) U1G U1G_IT 4000 true [] u1g_cert
           (SP.itab_ranges_sound SG _) ltac:(intros TA []) ltac:(intros Sm [])).
Qed.

(* [comment removed for export] *)
Definition U1GSUM : SP.summ := SP.SUMA (SP.p_G U1G) T0 (SP.p_ex U1G) (SP.p_W U1G) (SP.p_A U1G).
Theorem u1g_summ_ok : SP.summ_ok SG (s1_gp d) U1GSUM.
Proof.
  exact (SP.summ_of_pcheck SG (s1_gp d) s1_gfp (SG.gvc_list U1G_GV) (s1_gp_frame d) (U1G_vc_ok d) U1G U1G_IT 4000 true [] T0 u1g_cert
           (SP.itab_ranges_sound SG _) ltac:(intros TA []) ltac:(intros Sm []) ltac:(left; reflexivity)).
Qed.
End S.
Print Assumptions u1g_summ_ok.

(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma T0_in : In T0 (SP.p_tm U1G ++ SP.p_xt U1G).
Proof. apply in_or_app. left. left. reflexivity. Qed.
Definition u1g_evt (d : list Z) :=
  SLib.prog_evt0 SG (s1_gp d) s1_gfp (SG.gvc_list U1G_GV) (s1_gp_frame d) (U1G_vc_ok d) U1G U1G_IT 4000 true [] T0 u1g_cert
    (SP.itab_ranges_sound SG _) eq_refl (fun TA H => match H with end) (fun Sm H => match H with end)
    T0_in.
