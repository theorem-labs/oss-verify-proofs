(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Export LB_Inv LB_StmtA LB_Raw LB_Init.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc MSafe LB_WMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition raw_malloc_LQ := raw_malloc_L malloc_core_fq_proof.
Definition raw_free_LQ := raw_free_L.

Check (raw_malloc_LQ : forall X P n, 0 <= n ->
  mspec (fun s mo => QI X P s mo /\ ROOMX X P n /\ PHI P + R63X X + bigb n <= LBUDGET) (raw_malloc n)
       (fun r s mo => match r with
                        | Some p => QI ((p, n) :: X) P s mo /\ n < 2 ^ 63
                        | None => QI X P s mo
                        end)).
Check (raw_free_LQ : forall X P p n, mspec (QI ((p, n) :: X) P) (raw_free p) (fun _ => QI X P)).

(* [comment removed for export] *)
End RC__1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Nodes NodesMat.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import KLink LB_Kernel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma KL_with_tid' : forall L pbrk mo (t : word),
  (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z -> KL L pbrk mo -> KL L pbrk (with_tid t mo).
Proof.
  intros L pbrk mo t Ht HK.
  assert (Ev : m_vmmaps (with_tid t mo) = m_vmmaps mo) by (destruct mo; reflexivity).
  assert (Eh : m_halted (with_tid t mo) = m_halted mo) by (destruct mo; reflexivity).
  destruct HK. constructor; rewrite ?Ev, ?Eh, ?m_vm_materialized_with_tid; auto.
  apply minv_with_tid; assumption.
Qed.

Lemma QI_with_tid : forall X P s mo (t : word),
  (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z -> QI X P s mo -> QI X P s (with_tid t mo).
Proof.
  intros X P s mo t Ht [(st & L & BL & LS & Es & INV & SI & HAQ & HK & HL & HP & HLV) HB]. split; [| exact HB].
  exists st, L, BL, LS. split; [exact Es|]. split; [exact INV|]. split; [exact SI|]. split; [exact HAQ|].
  split; [apply KL_with_tid'; assumption|]. split; [| split; [exact HP| exact HLV]].
  unfold LI in *. replace (m_vmmaps (with_tid t mo)) with (m_vmmaps mo) by (destruct mo; reflexivity). exact HL.
Qed.
End RC__2.
