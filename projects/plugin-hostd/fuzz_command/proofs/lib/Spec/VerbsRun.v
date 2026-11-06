From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
Import ListNotations.
Open Scope Z_scope.

Definition run_call (R : rstate) (c : Verbs.call) : rstate * list byte :=
  match c with
  | Verbs.sup_add u i p q => sup_add_m R (Some u) i p q
  | Verbs.descriptors_get u => descriptors_get_m R (Some u)
  | Verbs.descriptors_panel_get u => descriptors_panel_get_m R (Some u)
  | Verbs.sup_remove i => sup_remove_m R i
  | Verbs.sup_remove_all => sup_remove_all_m R
  | Verbs.sup_worker_list => sup_worker_list_m R
  | Verbs.sup_instance_info i => sup_instance_info_m R i
  | Verbs.sup_reset w => sup_reset_m R (Some w)
  | Verbs.sup_quarantine_clear w => sup_quarantine_clear_m R (Some w)
  | Verbs.sup_policy_set a b => sup_policy_set_m R (Some a) (Some b)
  | Verbs.sup_lv2_worker_set a b => sup_lv2_worker_set_m R (Some a) (Some b)
  | Verbs.sup_pool_config n x => sup_pool_config_m R (Some n) x
  | Verbs.sup_worker_env a b c => sup_worker_env_m R (Some a) (Some b) (Some c)
  | Verbs.sup_chain i ids => sup_chain_m R i ids
  | Verbs.sup_chain_clear i => sup_chain_clear_m R i
  | Verbs.sup_pin_accept u => sup_pin_accept_m R (Some u)
  | Verbs.sup_instance_verb ln led => sup_instance_verb_m R ln led
  | Verbs.sup_call i ln => sup_call_m R i ln
  | Verbs.sup_connect v ln a b => sup_connect_m R (Some v) ln (Some a) (Some b)
  end.

Definition pins_follow (R : rstate) (rc : Z) : rstate * list byte :=
  (if rc =? 0 then lv2_refusals_forget_m R None else R, resp rc).

Definition pin_set_run (R : rstate) (ln : list byte) (args : list (list byte)) : rstate * Z :=
  match Verbs.pin_set_words_m ln args with
  | Verbs.SPinSet u f l v => let '(R1, r) := pins_set_m R (Some u) (Some f) (Some l) v in (fst (pins_follow R1 r), r)
  | _ => (R, Verbs.err_invalid_operation)
  end.

Definition chain_run (R : rstate) (args : list (list byte)) : rstate * list byte :=
  match Verbs.chain_words_m args with
  | Verbs.SCall c => run_call R c
  | _ => sup_resp_m R Verbs.err_invalid_operation
  end.

Definition run_step (rcode : list byte -> Z) (R : rstate) (s : Verbs.step) : rstate * list byte * bool :=
  match s with
  | Verbs.SResp c => (R, resp c, false)
  | Verbs.SCall c => (run_call R c, false)
  | Verbs.SAdd u i p q =>
      let '(R1, x) := sup_add_m R (Some u) i p q in
      ((if 0 <=? rcode x then descriptors_add_m R1 (Some u) else R1), x, false)
  | Verbs.SPinSet u f l v => let '(R1, rc) := pins_set_m R (Some u) (Some f) (Some l) v in (pins_follow R1 rc, false)
  | Verbs.SPinClear u => let '(R1, rc) := pins_clear_m R (Some u) in (pins_follow R1 rc, false)
  | Verbs.SQuit => (R, resp 0, true)
  | Verbs.SBroadcast ln tk => let '(R1, x) := sup_broadcast_m R ln in (sup_host_setting_m R1 ln tk, x, false)
  end.

Definition run_receive (atoi rcode : list byte -> Z) (R : rstate) (D : list byte) : rstate * list byte * bool :=
  let '(st, af) := Verbs.receive atoi D in
  let '(R1, x, q) := run_step rcode R st in
  let R2 := fst (socket_send_m R1 (x ++ [Z_to_bv 8 0])) in
  let R3 := match af with Some (i, v) => sup_after_reply_m R2 i (Some v) | None => R2 end in
  (R3, x, q).
