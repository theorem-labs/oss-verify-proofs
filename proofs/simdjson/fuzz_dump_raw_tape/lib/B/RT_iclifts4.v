(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_state RT_rep RT_facts RT_artfacts RT_icfacts I_consts I_qck R_m2s R_isPoisoned I_memcpyw I_memchrw I_strnlenw I_memcmp I_lift4 RT_iclifts TopA_iodefs RT_cli.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Lemma rta_cmp : forall Σ m, ART RTA Σ m -> icells_cmp m /\ m2s_cells m.
Proof.
  intros Σ m HA. destruct (rta_ic Σ m HA) as (_ & _ & _ & ICS & M2S). split; [| exact M2S].
  destruct ICS as (GCF & G2 & _ & _ & SHC & AI & _).
  split; [exact (ro_cells_mid m 0x16e760 [] _ _ GCF)|].
  split; [exact G2|]. split; [exact (rta_cmp_real Σ m HA)|]. split; [exact SHC|]. split; [exact AI| exact (rta_cmp_flags Σ m HA)].
Qed.

Theorem rta_memcmp : memcmp_icontract RTA.
Proof. exact (memcmp_lift RTA rta_art_facts rip_proof rta_cmp rta_shw). Qed.

End GWIN.
