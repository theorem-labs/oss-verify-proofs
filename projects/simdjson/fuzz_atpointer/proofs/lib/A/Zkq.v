(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Mem Frame Cells Step Arr ImageA.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks Zm2 RT_rep Zjb Zi7 Zkl
  Zbo I_qck R_m2s Zn9 Zc5 Zc0 Zcj Zc1 Zby Zko Z11d RT_cli.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rta_cmp : forall Σ m, ART RTA Σ m -> icells_cmp m /\ m2s_cells m.
Proof.
  intros Σ m HA. destruct (rta_ic Σ m HA) as (_ & _ & _ & ICS & M2S). split; [| exact M2S].
  destruct ICS as (GCF & G2 & _ & _ & SHC & AI & _).
  split; [exact (ro_cells_mid m 0x10b1d0 [] _ _ GCF)|].
  split; [exact G2|]. split; [exact (rta_cmp_real Σ m HA)|]. split; [exact SHC|]. split; [exact AI| exact (rta_cmp_flags Σ m HA)].
Qed.

Theorem rta_memcmp : memcmp_icontract RTA.
Proof. exact (memcmp_lift RTA rta_art_facts rip_proof rta_cmp rta_shw). Qed.
