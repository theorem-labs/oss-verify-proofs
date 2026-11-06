From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandModel RecFacts RecModel
  sup_reply_code_c rec_code_declared_c check_reply_answer_c check_reply_c check_arity_c check_words_c
  check_round_trip_c verbs_receive_c.
Import ListNotations.
Open Scope Z_scope.

Definition hwords (D : list byte) : list (list byte) := Verbs.words (Verbs.line D).

Definition answer_ok_m (ans : option (list byte)) (xr : list byte) (n : Z) (w0 : list byte) : Prop :=
  match ans with
  | Some xa => xr = xa
  | None => reply_code xr < 0 \/ (n = 1 /\ w0 = S_QUIT)
  end.

Definition msg_props (R0 : rstate) (D : list byte) : Prop :=
  let ws := hwords D in
  let n := Z.of_nat (length ws) in
  let w0 := nth 0 ws [] in
  let '(R1, x, quit) := vr_run (rec_clear R0) D in
  let q := if quit then 1 else 0 in
  r_nreplies R1 = 1 /\ r_reply R1 = Some (x ++ [Z_to_bv 8 0]) /\ no0 x /\ (Z.of_nat (length x) <= 28)%Z /\
  answer_ok_m (r_answer R1) x n w0 /\
  reply_ok n w0 x /\
  arity_ok n w0 q (Z.of_nat (length (r_calls R1))) (fst (nth 0 (r_calls R1) (0, []))) /\
  words_prop R1 ws /\
  (reply_code x < 0 -> r_state R1 = r_state R0 /\ quit = false) /\
  rt_ok R1 q (r_state R0) (r_host R0) ws.

Definition harness_props : Prop :=
  forall (R0 : rstate) (D : list byte),
    (length D <= 8192)%nat ->
    0 <= r_state R0 < 2 ^ 64 -> 0 <= r_host R0 < 2 ^ 64 ->
    (r_refuse R0 <> 0 -> declared (r_code R0) = true) ->
    msg_props R0 D.
