(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_state RT_rep RT_facts0 RT_facts RT_artfacts RT_icfacts I_consts I_qck R_m2s I_memcpyw I_memsetw I_memchrw I_strnlenw
  R_isPoisoned I_lift I_lift2 RT_iclifts TopA_iodefs RT_io I_strcmp_spec I_strcmpw I_strcmp I_strcmp_lift.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rta_scmp : forall Σ m, ART RTA Σ m -> icells_scmp m.
Proof.
  intros Σ m HA.
  destruct (rta_ic Σ m HA) as (_ & _ & _ & (S1 & S2 & _ & _ & S5 & S6 & _) & _).
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & (_ & X2 & _)).
  pose proof (rta_io Σ m HA) as IO.
  unfold icells_scmp.
  split; [exact (ro_head _ _ _ _ S1)|]. split; [exact S2|]. split; [exact S5|]. split; [exact S6|]. split; [exact X2|].
  exact (io_ro_at m IO 0x1821e2 _ ltac:(io_in)).
Qed.

Theorem rta_strcmp : strcmp_icontract RTA.
Proof. exact (strcmp_lift RTA rta_art_facts rip_proof rta_ic rta_shw rta_scmp). Qed.
