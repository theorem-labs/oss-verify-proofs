(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_element.images Require Import Asan.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanTablesA AsanSmear.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

#[local] Notation ASEGS := Asan.M.loaded_segments (only parsing).

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Lemma asan_xs_range : 0 <= x_sniff ASAN_A /\ x_sniff ASAN_A + 112 < 2 ^ 64.
Proof. cbn [x_sniff ASAN_A]. lia. Qed.

Lemma asan_xs_code : forall i, (i < 28)%nat -> fetch_word ASEGS (Z_to_bv 64 (x_sniff ASAN_A + 4 * Z.of_nat i)) = Some (sw i).
Proof. intros i Hi. do 28 (destruct i as [|i]; [vm_refl|]). lia. Qed.

Section Node.
Variable nx0 : nat.   Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.   Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap ASEGS.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull ASAN_A (bv_unsigned a) = false -> find_segment ASEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok ASAN_A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

Theorem asan_node_x_sound_XSniff : APS.x_stmt ASEGS ASAN_A nx0 LIMIT SINV argH FS0 XSniff.
Proof. eapply node_x_sound_XSniff; eauto using asan_xs_range, asan_xs_code. Qed.
End Node.
