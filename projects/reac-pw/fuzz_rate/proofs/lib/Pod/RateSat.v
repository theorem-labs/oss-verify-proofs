(** fuzz_rate's seeds through the model: for each of the 16 seeds of fuzz_rate's corpus (the harness's own inputs:
    flags, mask, buflen, the u32 other, then the pod) and 17 worked inputs, expect_rate's answer [expect_model] and
    the harness's parse [harness_parse] (NULL when flags & 1, else [parse_model] on buf), by computation, each as
    (written, rc) (Pod/Rate.v). Every branch of the two functions is reached at the real instance, as pod_build
    makes the record of the input after its 7 header bytes (fuzz_rate.c:236-244):
    - absent key, 0 (check_absent): near_keys (only near keys), key_no_value (a key with no pod after it);
    - no SPA_PROP_params, 0: no_params (a volume property only); its value not a Struct, 0: params_not_a_struct,
      params_int_first (the first params is the Int, a later params Struct holds the key);
    - Int, 1 and i (check_rate): rate_44100, rate_48000, rate_96000, rate_int_min, rate_int_max, rate_int_u32 (u32
      0xffffffff is -1), key_x (the key "reac.cfg.rate\0x\0" still keys the rate), rate_after_other_key (another
      key's pair first), two_rate_keys (flags 0: of two rate keys, 44100 then 96000, the first decides);
    - Float with a nearest in [INT32_MIN, INT32_MAX], 1 and that integer: rate_float_half (47999.5 is 48000),
      rate_float_negative (-0.7 is -1), rate_float_max (2147483520.0), rate_float_min (-2^31);
    - Float with none, -1 (check_malformed): rate_float_huge (-1e10, the seed: bits 0xd01502f9), rate_float_low
      (-1e10, floats[11]), rate_float_2p31 (2^31), rate_float_below_min (the float below -2^31), rate_nan,
      rate_float_infinite (+inf), rate_neg_inf;
    - another value, -1: rate_bool, rate_string;
    - not a Props object, -1: not_props_rate (a PropInfo object), struct_object (a Struct);
    - the NULL flag, -1 for both: rate_first_wins (flags 1: the harness passes NULL, reac_rate_cfg.c:117); the parse
      of its pod bytes is the first rate key's, 44100 ([rate_first_wins_pod]);
    - corrupted (the harness checks nothing): rate_corrupt (the bytes at 13..15, in the object header, written).
    Statement text and computation only. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Spa Nearest Rate Sat.
Import ListNotations.
Open Scope Z_scope.

(** The harness's view of an input (fuzz_rate.c:236-252): flags, 6 more header bytes, then pod_build on the rest;
    the parse gets NULL when flags & 1 (fuzz_rate.c:249). *)
Definition run_seed (inp : list Z) : option Z * Z * (option Z * Z) * bool :=
  let fl := match inp with [] => 0 | f :: _ => f end in
  let r := fst (pod_build (bl (skipn 7 inp))) in
  (expect_model (Z.testbit fl 0) r, harness_parse (Z.testbit fl 0) (buf r), corrupt r).

(** ** The seeds (fuzz_rate_seed_corpus.zip, file names with - as _) *)
Definition near_keys := [0; 7; 8; 0; 0; 0; 0; 0; 1; 1; 6; 1; 8; 2; 1; 128; 187; 0; 0; 1; 3; 2; 1; 1; 0; 0; 0; 1; 4; 2; 1; 1; 0; 0; 0; 0].
Definition not_props_rate := [0; 7; 8; 0; 0; 0; 0; 6; 1; 1; 2; 1; 0; 2; 1; 128; 187; 0; 0; 0].
Definition params_not_a_struct := [0; 7; 8; 0; 0; 0; 0; 0; 1; 17; 0].
Definition rate_44100 := [0; 7; 0; 68; 172; 0; 0; 0; 1; 1; 2; 1; 0; 2; 1; 68; 172; 0; 0; 0].
Definition rate_48000 := [0; 7; 3; 68; 172; 0; 0; 0; 1; 1; 2; 1; 0; 2; 1; 128; 187; 0; 0; 0].
Definition rate_96000 := [0; 7; 20; 0; 119; 1; 0; 0; 1; 1; 2; 1; 0; 2; 1; 0; 119; 1; 0; 0].
Definition rate_after_other_key := [0; 2; 8; 0; 0; 0; 0; 0; 1; 1; 4; 1; 5; 2; 1; 7; 0; 0; 0; 1; 0; 2; 1; 128; 187; 0; 0; 0].
Definition rate_bool := [0; 7; 8; 0; 0; 0; 0; 0; 1; 1; 2; 1; 0; 4; 1; 0].
Definition rate_first_wins := [1; 0; 1; 128; 187; 0; 0; 0; 1; 1; 4; 1; 0; 2; 1; 68; 172; 0; 0; 1; 0; 2; 1; 0; 119; 1; 0; 0].
Definition rate_float_half := [0; 3; 23; 0; 0; 0; 0; 0; 1; 1; 2; 1; 0; 3; 1; 128; 127; 59; 71; 0].
Definition rate_float_huge := [0; 7; 8; 0; 0; 0; 0; 0; 1; 1; 2; 1; 0; 3; 1; 249; 2; 21; 208; 0].
Definition rate_float_infinite := [0; 7; 8; 0; 0; 0; 0; 0; 1; 1; 2; 1; 0; 3; 1; 0; 0; 128; 127; 0].
Definition rate_float_negative := [0; 7; 8; 0; 0; 0; 0; 0; 1; 1; 2; 1; 0; 3; 1; 51; 51; 51; 191; 0].
Definition rate_not_drivable := [0; 5; 20; 1; 0; 0; 0; 0; 1; 1; 2; 1; 0; 2; 1; 128; 187; 0; 0; 0].
Definition rate_string := [0; 7; 8; 0; 0; 0; 0; 0; 1; 1; 2; 1; 0; 5; 5; 52; 56; 48; 48; 48; 0].
Definition slave_asks_48000 := [2; 7; 6; 128; 187; 0; 0; 0; 1; 1; 2; 1; 0; 2; 1; 128; 187; 0; 0; 0].

Lemma seeds_outcomes :
  run_seed near_keys = ((None, 0), (None, 0), false) /\
  run_seed not_props_rate = ((None, (-1)), (None, (-1)), false) /\
  run_seed params_not_a_struct = ((None, 0), (None, 0), false) /\
  run_seed rate_44100 = ((Some 44100, 1), (Some 44100, 1), false) /\
  run_seed rate_48000 = ((Some 48000, 1), (Some 48000, 1), false) /\
  run_seed rate_96000 = ((Some 96000, 1), (Some 96000, 1), false) /\
  run_seed rate_after_other_key = ((Some 48000, 1), (Some 48000, 1), false) /\
  run_seed rate_bool = ((None, (-1)), (None, (-1)), false) /\
  run_seed rate_first_wins = ((None, (-1)), (None, (-1)), false) /\
  run_seed rate_float_half = ((Some 48000, 1), (Some 48000, 1), false) /\
  run_seed rate_float_huge = ((None, (-1)), (None, (-1)), false) /\
  run_seed rate_float_infinite = ((None, (-1)), (None, (-1)), false) /\
  run_seed rate_float_negative = ((Some (-1), 1), (Some (-1), 1), false) /\
  run_seed rate_not_drivable = ((Some 48000, 1), (Some 48000, 1), false) /\
  run_seed rate_string = ((None, (-1)), (None, (-1)), false) /\
  run_seed slave_asks_48000 = ((Some 48000, 1), (Some 48000, 1), false).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** rate_first_wins's pod bytes, read by the parse itself (what a NULL flag hides): the first rate key decides. *)
Lemma rate_first_wins_pod : parse_model (buf (fst (pod_build (bl (skipn 7 rate_first_wins))))) = (Some 44100, 1).
Proof. vm_compute. reflexivity. Qed.

(** ** The worked inputs (header bytes 0) *)
Definition rate_nan := [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 2; 1; 0; 3; 254; 0].
Definition rate_neg_inf := [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 2; 1; 0; 3; 1; 0; 0; 128; 255; 0].
Definition rate_float_low := [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 2; 1; 0; 3; 22; 0].
Definition rate_float_2p31 := [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 2; 1; 0; 3; 32; 0].
Definition rate_float_max := [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 2; 1; 0; 3; 30; 0].
Definition rate_float_min := [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 2; 1; 0; 3; 34; 0].
Definition rate_float_below_min := [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 2; 1; 0; 3; 36; 0].
Definition rate_int_min := [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 2; 1; 0; 2; 24; 0].
Definition rate_int_max := [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 2; 1; 0; 2; 26; 0].
Definition rate_int_u32 := [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 2; 1; 0; 2; 1; 255; 255; 255; 255; 0].
Definition no_params := [0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0].
Definition struct_object := [0; 0; 0; 0; 0; 0; 0; 7; 2; 0; 0; 0].
Definition key_no_value := [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 0; 0].
Definition key_x := [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 2; 131; 0; 2; 10; 0].
Definition params_int_first := [0; 0; 0; 0; 0; 0; 0; 0; 3; 0; 17; 1; 2; 1; 0; 2; 10; 0].
Definition rate_corrupt := [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 2; 1; 0; 2; 0; 15; 5; 0; 3; 170; 187; 204].
Definition two_rate_keys := [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 4; 1; 0; 2; 1; 68; 172; 0; 0; 1; 0; 2; 1; 0; 119; 1; 0; 0].

Lemma worked_outcomes :
  run_seed rate_nan = ((None, (-1)), (None, (-1)), false) /\
  run_seed rate_neg_inf = ((None, (-1)), (None, (-1)), false) /\
  run_seed rate_float_low = ((None, (-1)), (None, (-1)), false) /\
  run_seed rate_float_2p31 = ((None, (-1)), (None, (-1)), false) /\
  run_seed rate_float_max = ((Some 2147483520, 1), (Some 2147483520, 1), false) /\
  run_seed rate_float_min = ((Some (-2147483648), 1), (Some (-2147483648), 1), false) /\
  run_seed rate_float_below_min = ((None, (-1)), (None, (-1)), false) /\
  run_seed rate_int_min = ((Some (-2147483648), 1), (Some (-2147483648), 1), false) /\
  run_seed rate_int_max = ((Some 2147483647, 1), (Some 2147483647, 1), false) /\
  run_seed rate_int_u32 = ((Some (-1), 1), (Some (-1), 1), false) /\
  run_seed no_params = ((None, 0), (None, 0), false) /\
  run_seed struct_object = ((None, (-1)), (None, (-1)), false) /\
  run_seed key_no_value = ((None, 0), (None, 0), false) /\
  run_seed key_x = ((Some 48000, 1), (Some 48000, 1), false) /\
  run_seed params_int_first = ((None, 0), (None, 0), false) /\
  run_seed rate_corrupt = ((Some 0, 1), (Some 0, 1), true) /\
  run_seed two_rate_keys = ((Some 44100, 1), (Some 44100, 1), false).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** The four views of Spa.v are reached by these inputs' buffers. *)
Definition is_vpods (v : spa_view) : bool := match v with VPods _ => true | _ => false end.
Lemma rate_views_reached :
  is_vpods (spa_view_of (buf (fst (pod_build (bl (skipn 7 rate_48000)))))) = true /\
  spa_view_of (buf (fst (pod_build (bl (skipn 7 not_props_rate))))) = VNotProps /\
  spa_view_of (buf (fst (pod_build (bl (skipn 7 no_params))))) = VNoParams /\
  spa_view_of (buf (fst (pod_build (bl (skipn 7 params_not_a_struct))))) = VParamsNotStruct.
Proof. vm_compute. repeat split; reflexivity. Qed.
