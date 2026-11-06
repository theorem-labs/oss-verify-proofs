(** fuzz_role's seeds through the model: for each of the 11 seeds of fuzz_role's corpus (the harness's own inputs,
    flags byte first) and the worked inputs, expect_role's answer [expect_model] and the parse's answer
    [parse_model] on buf, by computation. Every outcome the harness checks is reached: 0 (check_absent), 1 with
    MASTER and with SLAVE (check_role), -1 (check_malformed), and the NULL flag. Statement text and computation
    only. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Spa Nearest Role Sat.
Import ListNotations.
Open Scope Z_scope.

(** The harness's view of an input (fuzz_role.c:137-158): flags, then pod_build on the rest. *)
Definition run_seed (inp : list Z) : option role * Z * (option role * Z) * bool :=
  let fl := match inp with [] => 0 | f :: _ => f end in
  let r := fst (pod_build (bl (tl inp))) in
  (expect_model (Z.testbit fl 0) r, parse_model (buf r), corrupt r).

Definition near_role_keys := [0; 0; 1; 1; 4; 1; 7; 2; 1; 1; 0; 0; 0; 1; 0; 2; 1; 1; 0; 0; 0; 0].
Definition not_props_role := [0; 6; 1; 1; 2; 1; 1; 2; 1; 1; 0; 0; 0; 0].
Definition null_object := [1; 0; 1; 1; 2; 1; 1; 2; 1; 1; 0; 0; 0; 0].
Definition params_not_a_struct := [0; 0; 1; 17; 0].
Definition role_float_below_half := [2; 0; 1; 1; 2; 1; 1; 3; 1; 255; 255; 255; 62; 0].
Definition role_float_negative := [0; 0; 1; 1; 2; 1; 1; 3; 1; 51; 51; 51; 191; 0].
Definition role_master := [0; 0; 1; 1; 2; 1; 1; 2; 1; 0; 0; 0; 0; 0].
Definition role_nan := [0; 0; 1; 1; 2; 1; 1; 3; 1; 0; 0; 192; 127; 0].
Definition role_slave_float := [2; 0; 1; 1; 2; 1; 1; 3; 1; 0; 0; 128; 63; 0].
Definition role_string := [0; 0; 1; 1; 2; 1; 1; 5; 6; 109; 97; 115; 116; 101; 114; 0].
Definition role_two := [0; 0; 1; 1; 2; 1; 1; 2; 1; 2; 0; 0; 0; 0].

Lemma seeds_outcomes :
  run_seed near_role_keys = ((None, 0), (None, 0), false) /\
  run_seed not_props_role = ((None, -1), (None, -1), false) /\
  fst (fst (run_seed null_object)) = (None, -1) /\
  run_seed params_not_a_struct = ((None, 0), (None, 0), false) /\
  run_seed role_float_below_half = ((Some MASTER, 1), (Some MASTER, 1), false) /\
  run_seed role_float_negative = ((None, -1), (None, -1), false) /\
  run_seed role_master = ((Some MASTER, 1), (Some MASTER, 1), false) /\
  run_seed role_nan = ((None, -1), (None, -1), false) /\
  run_seed role_slave_float = ((Some SLAVE, 1), (Some SLAVE, 1), false) /\
  run_seed role_string = ((None, -1), (None, -1), false) /\
  run_seed role_two = ((None, -1), (None, -1), false).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** W2-W4 of the worked inputs: Int 1 is SLAVE, Float 0.5 reads 1 (SLAVE), a key "reac.cfg.role\0x\0" still keys
    the role; W8 is corrupted (the harness checks nothing there), and its parse still reads MASTER. *)
Lemma worked_outcomes :
  run_seed [0; 0; 1; 1; 2; 1; 1; 2; 2; 0] = ((Some SLAVE, 1), (Some SLAVE, 1), false) /\
  run_seed [0; 0; 1; 1; 2; 1; 1; 3; 4] = ((Some SLAVE, 1), (Some SLAVE, 1), false) /\
  run_seed [0; 0; 1; 1; 2; 131; 1; 2; 1; 0; 0] = ((Some MASTER, 1), (Some MASTER, 1), false) /\
  run_seed (0 :: map bv_unsigned W8) = ((Some MASTER, 1), (Some MASTER, 1), true) /\
  run_seed (0 :: map bv_unsigned W7) = ((None, 0), (None, 0), false).
Proof. vm_compute. repeat split; reflexivity. Qed.
