(** fuzz_headamp's inputs through the model: the premises of [parse_model_build] (pod_rec_wf, an uncorrupted record,
    0 <= cap <= 9) hold at real harness inputs, and at each of them expect_of's answer [expect_model] and the parse's
    answer [parse_model] on buf are computed and equal. Every branch the model has is reached: a cell of each param
    (phantom, pad, sens), each value kind (Bool, Int, Float through nearest), a refusal of each kind (BAD_KEY,
    OUT_OF_RANGE by channel, by value, by a value pod that is no number) with the first one kept, cap 0, cap 2 and
    cap 9 (the n >= cap break), keys without the prefix skipped, the odd channel texts pod.h writes (signs, blanks,
    leading zeros, 20-digit values that saturate strtol, no digit, a digit then not '.'), the views that answer -1 and
    0, and the NULL flag. Statement text and computation only. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Spa Sat Headamp.
Import ListNotations.
Open Scope Z_scope.

(** The harness's view of an input (fuzz_headamp.c:315-322, :333-340): null = byte 0 & 1, cap = byte 1 % 10, then
    pod_build on the rest; (expect_of, the parse on buf, corrupt). *)
Definition run_h (inp : list Z) : (Z * list cell * (Z * Z * Z)) * (Z * list cell * (Z * Z * Z)) * bool :=
  let '(nl, r1) := fuzz_u8 (bl inp) in
  let '(cp, r2) := fuzz_u8 r1 in
  let r := fst (pod_build r2) in
  (expect_model (Z.testbit nl 0) (cp mod 10) r, parse_model (buf r) (cp mod 10), corrupt r).

(** CR: a Props object, one params Struct of 7 pairs: "reac.headamp.3.phantom" = Bool 1; "reac.headamp.5.pad" = Int 0;
    "reac.headamp.7.sens" = Float 54.6 (nearest 55 = the last sens step); "reac.headamp.48.phantom" = Bool 1 (channel
    48: OUT_OF_RANGE, the first refusal); "reac.headamp.3.PAD" = Bool 1 (BAD_KEY); "reac.headamp.3.phantom" = Int 2
    (value OUT_OF_RANGE); "reac.headamp.1.pad" = Float 1.0. The bytes after (null, cap). *)
Definition CR_pod : list Z :=
  [0; 1; 1; 14; 0; 3; 0; 4; 1; 0; 5; 1; 2; 0; 0; 7; 2; 3; 28; 0; 48; 0; 4; 1; 0; 3; 3; 4; 1; 0; 3; 0; 2; 4;
   0; 1; 1; 3; 6; 0].
Definition CR_out : Z * list cell * (Z * Z * Z) :=
  (4, [(3, 0, 1); (5, 1, 0); (7, 2, 55); (1, 1, 1)], (4, 7, REFUSE_OUT_OF_RANGE)).

Lemma cr_premises :
  pod_rec_wf (fst (pod_build (bl CR_pod))) /\ corrupt (fst (pod_build (bl CR_pod))) = false /\
  run_h ([0; 9] ++ CR_pod) = (CR_out, CR_out, false).
Proof.
  split; [apply (pod_build_wf (bl CR_pod) _ (snd (pod_build (bl CR_pod)))); apply surjective_pairing|].
  vm_compute. split; reflexivity.
Qed.

(** The corollary's premises are met at CR with cap 9 (and so its conclusion holds there without computation). *)
Lemma cr_build : parse_model (buf (fst (pod_build (bl CR_pod)))) 9 = expect_model false 9 (fst (pod_build (bl CR_pod))).
Proof.
  apply (parse_model_build (bl CR_pod) _ (snd (pod_build (bl CR_pod)))); [apply surjective_pairing | | lia].
  vm_compute. reflexivity.
Qed.

(** cap 0: the first good cell stops the loop with keys 1 and nothing written; cap 2: the third good cell stops it. *)
Lemma cr_caps :
  run_h ([0; 0] ++ CR_pod) = ((0, [], (0, 1, REFUSE_NONE)), (0, [], (0, 1, REFUSE_NONE)), false) /\
  run_h ([0; 2] ++ CR_pod) =
    ((2, [(3, 0, 1); (5, 1, 0)], (2, 3, REFUSE_NONE)), (2, [(3, 0, 1); (5, 1, 0)], (2, 3, REFUSE_NONE)), false) /\
  run_h ([0; 19] ++ CR_pod) = (CR_out, CR_out, false).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** The NULL flag: expect_of is -1 with nothing seen. *)
Lemma cr_null : fst (fst (run_h ([1; 9] ++ CR_pod))) = (-1, [], (0, 0, REFUSE_NONE)).
Proof. vm_compute. reflexivity. Qed.

(** RO: BAD_KEY first ("reac.headamp.x.phantom", odd channel "x"), then OUT_OF_RANGE (channel 48): BAD_KEY is
    reported. *)
Definition RO_pod : list Z := [0; 1; 1; 4; 0; 202; 0; 4; 1; 0; 48; 0; 4; 1; 0].
Lemma ro_first_refusal :
  run_h ([0; 9] ++ RO_pod) = ((0, [], (0, 2, REFUSE_BAD_KEY)), (0, [], (0, 2, REFUSE_BAD_KEY)), false).
Proof. vm_compute. reflexivity. Qed.

(** ODD: one phantom key per odd channel text of pod.h (odd_ch[c mod 14], c >= 200), each = Bool 1:
    "-1" OOR, "+3" cell 3, " 7" cell 7, "07" cell 7, 20 nines OOR (strtol saturates), "" BAD, "x" BAD, "3a" BAD,
    "-0" cell 0, "\t5" cell 5, "48" OOR, "47" cell 47, "0x1" BAD, minus 20 nines OOR. *)
Definition ODD_pod : list Z :=
  [0; 1; 1; 28] ++ flat_map (fun c => [0; c; 0; 4; 1]) [210; 211; 212; 213; 200; 201; 202; 203; 204; 205; 206; 207; 208; 209]
  ++ [0].
Definition ODD_out : Z * list cell * (Z * Z * Z) :=
  (6, [(3, 0, 1); (7, 0, 1); (7, 0, 1); (0, 0, 1); (5, 0, 1); (47, 0, 1)], (6, 14, REFUSE_OUT_OF_RANGE)).
Lemma odd_channels : run_h ([0; 9] ++ ODD_pod) = (ODD_out, ODD_out, false).
Proof. vm_compute. reflexivity. Qed.

(** VAL: nine values for "reac.headamp.2.sens": Int 55 (cell), Int 56, Int -1, Int 256, Float 255.5 (nearest is
    256: none in [0, 255]), Float NaN, Bool 2 (true: cell 1), Bool 0 (cell 0), a String "" (no number). *)
Definition VAL_pod : list Z :=
  [0; 1; 1; 18] ++ flat_map (fun v => [0; 2; 2] ++ v) [[2; 14]; [2; 16]; [2; 6]; [2; 20]; [3; 26]; [3; 254]; [4; 2];
   [4; 0]; [5; 0]] ++ [0].
Definition VAL_out : Z * list cell * (Z * Z * Z) :=
  (3, [(2, 2, 55); (2, 2, 1); (2, 2, 0)], (3, 9, REFUSE_OUT_OF_RANGE)).
Lemma value_kinds : run_h ([0; 9] ++ VAL_pod) = (VAL_out, VAL_out, false).
Proof. vm_compute. reflexivity. Qed.

(** SKIP: "reac.cfg.role" = Int 0 and "reac.headamp" (12 bytes) = Bool 1 are not under the prefix; "reac.headamp."
    (vocab[2]) is, with no channel: BAD_KEY. *)
Definition SKIP_pod : list Z := [0; 1; 1; 6; 1; 1; 2; 0; 1; 6; 4; 1; 1; 2; 4; 1; 0].
Lemma prefix_skip :
  run_h ([0; 9] ++ SKIP_pod) = ((0, [], (0, 1, REFUSE_BAD_KEY)), (0, [], (0, 1, REFUSE_BAD_KEY)), false).
Proof. vm_compute. reflexivity. Qed.

(** The views: a Struct object (W5) and a PropInfo object (W6) answer -1; params as an Int (W7) and no params (W9)
    answer 0; T4 (every bound: 16 pairs of 45-byte keys "reac.headamp.-99999999999999999999.phantom.x") counts 16
    keys, all BAD_KEY (the name is "phantom.x"). *)
Lemma views_and_bounds :
  run_h (0 :: 9 :: map bv_unsigned W5) = ((-1, [], (0, 0, REFUSE_NONE)), (-1, [], (0, 0, REFUSE_NONE)), false) /\
  run_h (0 :: 9 :: map bv_unsigned W6) = ((-1, [], (0, 0, REFUSE_NONE)), (-1, [], (0, 0, REFUSE_NONE)), false) /\
  run_h (0 :: 9 :: map bv_unsigned W7) = ((0, [], (0, 0, REFUSE_NONE)), (0, [], (0, 0, REFUSE_NONE)), false) /\
  run_h (0 :: 9 :: map bv_unsigned W9) = ((0, [], (0, 0, REFUSE_NONE)), (0, [], (0, 0, REFUSE_NONE)), false) /\
  run_h (0 :: 9 :: map bv_unsigned T4) = ((0, [], (0, 16, REFUSE_BAD_KEY)), (0, [], (0, 16, REFUSE_BAD_KEY)), false).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A corrupted record (W8): the harness checks no expectation there; the parse's answer still meets
    [parse_model_total]'s count and validity (here: the role pair, no head-amp key). *)
Lemma corrupted_total : snd (run_h (0 :: 9 :: map bv_unsigned W8)) = true /\
  snd (fst (run_h (0 :: 9 :: map bv_unsigned W8))) = (0, [], (0, 0, REFUSE_NONE)).
Proof. vm_compute. split; reflexivity. Qed.
