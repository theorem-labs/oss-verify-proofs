(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the record-fact layer of the verbs_receive walk on image B
   (fuzz_command.asan-ubsan). The interface lib/B/Prog/verbs_receive_iface.v states the facts the segments take as
   named premises (vr_rec_cells, vr_ro_of_aro, vr_ro_in_img, vr_relro_img, vr_pg_not_ro, vr_prog_unowned,
   vr_blktail, vr_shadow_ok); here each one is discharged by `exact` from lib/B/Prog/CmdRecCells / CmdRecRo /
   CmdRecImg / CmdRecBase over the per-binary hypotheses HB and IMG, as the B SIDE ruling asks (never a local
   proof of a record fact). lib/B/Prog/verbs_receive_top.v takes these and the 32 segment lemmas.

   The one computation here is vrt_shr_chk: every literal and table the walk hands to a wrapper or reads under an
   inline check (verbs_receive_iface.v vr_shr: the 37 literals at 0x22500 .. 0x22a40 with their terminators, and
   g_instance_info_verbs 0xa5c40 over 160 bytes) passes both of the record's Boolean checkers, cmd_addr_b and
   cmd_hull_b (CmdChk.v), at its exact byte length, partial last granule included. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecCells CmdRecRo CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the two per-binary facts every record lemma rests on (a Theorem Labs lane's RULING-STMT.md §1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.

Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the interface's record-fact premises, by the per-binary lemmas of lib/B/Prog/CmdRec*.v *)
Definition VRF_RECC : vr_rec_cells B := cmd_rec_cells SEGS B LAWS HB IMG.
Definition VRF_ROA : vr_ro_of_aro B := cmd_ro_ok_of_aro SEGS B LAWS HB IMG.
Definition VRF_ROIN : vr_ro_in_img := cmd_ro_in_img SEGS B LAWS HB IMG.
Definition VRF_RRO : vr_relro_img := cif_relro_img _ _ IMG.
Definition VRF_RPG : vr_pg_not_ro := cif_prog_not_ro _ _ IMG.
Definition VRF_PROGU : vr_prog_unowned B := cmd_prog_unowned SEGS B LAWS HB IMG.

(* a byte of a live block is below the block's request size, so the core's word-visibility law applies *)
Lemma vrt_blktail : vr_blktail B.
Proof.
intros ly S W mem md p n x HAR Hin Hx.
apply (cmd_heap_tail_vis SEGS B LAWS HB ly S W mem md p n x HAR Hin).
unfold req_size. destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia].
Qed.

(* every object of vr_shr passes both Boolean checkers of the record, at its exact length *)
Lemma vrt_shr_chk : forallb (fun an => cmd_addr_b (fst an) (snd an) && cmd_hull_b (fst an) (snd an)) vr_shr = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vrt_shadow_ok : vr_shadow_ok B.
Proof.
intros ly S W mem md a n HAR Hin.
exact (proj1 (Forall_forall _ _) (cmd_lits_chk SEGS B LAWS HB vr_shr vrt_shr_chk ly S W mem md HAR) (a, n) Hin).
Qed.

Definition VRF_BLKT : vr_blktail B := vrt_blktail.
Definition VRF_SHOK : vr_shadow_ok B := vrt_shadow_ok.

End e.
End f.
End d.
