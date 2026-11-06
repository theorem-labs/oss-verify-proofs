(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, addresses and numbers changed; 976 of its 1075 lines of code are new or changed and 647 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_reject_clean_starved.v, with its module names and numbers changed; 714 of its 791 lines of code are new or changed and 998 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_as_written.v, with its module paths and module names changed; 295 of its 339 lines of code are new or changed and 747 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/CF/fuzz_free.v; 15 of its 28 lines of code are new or changed and 326 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import fuzz_alloc_most_c.
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Step.mem_after_store_opt ::= idtac.

Lemma fam_wfin : forall m o bs, 0 <= o -> o + Z.of_nat (length bs) <= 2^64 ->
  bytes_at rsegs (write_to_mem m (wa o) bs) o bs /\
  munch [(o, o + Z.of_nat (length bs))] m (write_to_mem m (wa o) bs) /\
  wmono rsegs m (write_to_mem m (wa o) bs).
Proof.
  intros m o bs H1 H2. split; [apply bytes_at_write_same; lia|]. split.
  - apply munch_write; [apply munch_refl | lia | lia | cbn; left; lia].
  - apply wmono_write, wmono_refl.
Qed.

(* The three instructions at 0x158e4: auipc a1, 0xf (a1 = 0x248e4); sd a0, -0x3bc(a1) (the 8 bytes of a0 at
   0x24528 = g_most); ret. *)
Theorem fuzz_alloc_most_holds : fuzz_alloc_most_contract.
Proof.
  unfold fuzz_alloc_most_contract, FUZZ_ALLOC_MOST.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m W.
  pose proof W as (Wo & Wn & _).
  assert (HS : store_ok rsegs m (wa (G_MOST + 0)) 8 = true) by (eapply wr_at_store_ok; [exact W | lia | lia]).
  unfold G_MOST in HS, W |- *.
  step. step. step.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  rewrite ?Z.add_0_r. apply fam_wfin; cbn [length]; rewrite ?length_le8; lia.
Qed.
