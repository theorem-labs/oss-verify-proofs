(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlanCore CatSim.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import A2D_defs A2D_cert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition GP0a2d : nat -> list word -> (word -> option byte) -> Prop := fun _ _ _ => True.
Lemma GP0a2d_frame : SG.gp_frameP GP0a2d (fun _ _ => []). Proof. intros id args E M M' _ _. exact I. Qed.
Lemma GP0a2d_vc : forall c, (fun _ : SG.vc => false) c = true -> SG.vc_holds SG GP0a2d c. Proof. intros c H. discriminate H. Qed.

Theorem a2d_sound : forall T E M rom ms, In T (SP.p_tm A2D ++ SP.p_xt A2D) -> SX.aw_genuine E (SP.p_A A2D) ->
  ST.tm_okF SG T E M rom ms ->
  exists ms', ExecF.mstepsF SG (SX.fp_of (SP.p_A A2D) E) ms ms' /\ SP.prun_post SG GP0a2d A2D E M rom ms'.
Proof.
  intros T E M rom ms HinT HAG HT.
  exact (SP.pcheck_sound SG GP0a2d (fun _ _ => []) (fun _ => false) GP0a2d_frame GP0a2d_vc A2D A2D_IT 4000 false [] a2d_cert
           (SP.itab_ranges_sound SG _) ltac:(intros TA []) ltac:(intros Sm [])
           T E M rom ms HinT HAG HT ltac:(destruct HinT as [<-|[<-|[<-|[]]]]; constructor)).
Qed.
