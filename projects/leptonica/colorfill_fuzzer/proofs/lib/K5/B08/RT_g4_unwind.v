(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Arr Walk Frame.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import Layout R_unwind_defs R_depot_unwind RT_iface RT_traces G4_chain RT_gaps_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma chain_ok_okW : forall W pc (m : mem) ras lo f lo0,
  chain_ok m lo f ras -> 0 <= lo0 <= lo -> (forall a, lo0 <= a -> disjoint_from W a 16) -> Forall (fun x => x <> pc) ras ->
  chain_okW W pc m lo f ras.
Proof.
  intros W pc m ras. induction ras as [|ra1 ras IH]; intros lo f lo0 HC Hlo HW HF.
  - exact HC.
  - cbn [chain_ok] in HC. destruct HC as (H1 & H2 & H3 & H4 & fp1 & H5 & H6 & H7). cbn [chain_okW].
    apply Forall_cons_iff in HF as [HF1 HF2]. unfold USTACK_TOP in H3.
    split; [lia|]. split; [exact H2|]. split; [lia|]. split; [exact H4|]. split; [exact HF1|].
    split; [apply HW; lia|]. exists fp1. split; [exact H5|]. split; [exact H6|].
    apply (IH f fp1 lo0 H7); [lia | exact HW | exact HF2].
Qed.

Theorem unwindC_trace : forall W pc (m : mem) (ra s0 sp : word) bot top,
  unwind_okC m ra s0 sp -> In pc ALLOC_PCS -> 4096 <= top -> top <= 2^63 ->
  (forall a, bv_unsigned sp <= a -> disjoint_from W a 16) ->
  exists ch tr, chain_cells W m (bv_unsigned s0) ch
    /\ unwind_trace pc 4096 bot top 30 (bv_unsigned sp) ((bv_unsigned ra, bv_unsigned s0) :: ch) = Some tr
    /\ In tr T_MAIN /\ (1 <= length tr <= 5)%nat /\ Forall rng64 tr.
Proof.
  intros W pc m ra s0 sp bot top (ras & CH & IN) Hpc Ht1 Ht2 HW.
  destruct (client_trace_facts _ IN) as (HL & HF). cbn [length] in HL. apply Forall_cons_iff in HF as [(Hra & Hnra) HFr].
  assert (Hne : bv_unsigned ra <> pc) by (intros E; apply Hnra; rewrite E; exact Hpc).
  assert (HFne : Forall (fun x => x <> pc) ras).
  { apply Forall_forall. intros x Hx E. pose proof (proj1 (Forall_forall _ _) HFr x Hx) as (_ & Hn). apply Hn. rewrite E. exact Hpc. }
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (chain_ok_okW W pc m ras (bv_unsigned sp) (bv_unsigned s0) (bv_unsigned sp) CH ltac:(lia) HW HFne) as CW.
  destruct (unwind_trace_chain W pc bot top m (bv_unsigned sp) (bv_unsigned ra) (bv_unsigned s0) ras CW Ht1 Ht2 ltac:(lia) Hne ltac:(lia))
    as (ch & tr & j & C1 & C2 & C3 & C4).
  exists ch, tr. split; [exact C1|]. split; [exact C2|].
  assert (TM : In tr T_MAIN) by (rewrite C4; apply (t_main_prefix pc (bv_unsigned ra :: ras) j Hpc IN); cbn [length]; lia).
  split; [exact TM|]. split; [exact (t_main_length tr TM)|]. exact (t_main_range tr TM).
Qed.

(* [comment removed for export] *)
Lemma unwind_okC_of_ok : forall (m : mem) ra s0 sp, unwind_ok ra s0 sp -> In [bv_unsigned ra] CLIENT_TRACES -> unwind_okC m ra s0 sp.
Proof.
  intros m ra s0 sp (_ & H) HIN. exists []. split; [|exact HIN]. cbn [chain_ok]. unfold link_invalid. lia.
Qed.

(* [comment removed for export] *)
Lemma alloc_ras_client : forall ra, In ra RT_iface.ALLOC_RAS -> In [ra] CLIENT_TRACES.
Proof. intros ra H. unfold RT_iface.ALLOC_RAS in H. repeat (destruct H as [<-|H]; [vm_compute; tauto|]). destruct H. Qed.
