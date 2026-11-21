(* NEGATIVE CONTROL: a lemma about another input file.  It proves the
   premises of plain_halts on a file of seven bytes 01, but the instance file,
   input.bin, holds other bytes, so the wrapper, which defines the input from
   that file, does not type-check. *)
From Stdlib Require Import List.
From stdpp.bitvector Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.exit0 Require Images.
From OSSVerify.Tests.proofs.lib Require Import Exit0Instance.

Definition ones : list byte := repeat (Z_to_bv 8 1) 7.

Lemma plain_halts_instance :
  exists en, valid_entry Images.plain en (input reaches_harness ones)
    /\ valid_input (input reaches_harness ones)
    /\ ~ run_scfg_budget_refused forced_only_cfg Images.plain Budgets.Standard.lim_source en
           (input reaches_harness ones).
Proof. exact (halts_within_budget_premises _ _ launch_argv_reaches_harness). Qed.
