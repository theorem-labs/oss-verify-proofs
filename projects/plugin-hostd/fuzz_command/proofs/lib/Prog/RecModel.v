From Stdlib Require Import String ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
Import ListNotations.
Open Scope Z_scope.

Definition rcall : Type := (Z * list (list byte))%type.

Record rstate := RState {
  r_refuse : Z;
  r_code : Z;
  r_calls : list rcall;
  r_spill : rcall;
  r_answer : option (list byte);
  r_nreplies : Z;
  r_reply : option (list byte);
  r_state : Z;
  r_host : Z }.

Definition set_calls (R : rstate) (cs : list rcall) : rstate :=
  RState (r_refuse R) (r_code R) cs (r_spill R) (r_answer R) (r_nreplies R) (r_reply R) (r_state R) (r_host R).

Definition set_spill (R : rstate) (c : rcall) : rstate :=
  RState (r_refuse R) (r_code R) (r_calls R) c (r_answer R) (r_nreplies R) (r_reply R) (r_state R) (r_host R).

Definition set_answer (R : rstate) (t : option (list byte)) : rstate :=
  RState (r_refuse R) (r_code R) (r_calls R) (r_spill R) t (r_nreplies R) (r_reply R) (r_state R) (r_host R).

Definition set_state (R : rstate) (h : Z) : rstate :=
  RState (r_refuse R) (r_code R) (r_calls R) (r_spill R) (r_answer R) (r_nreplies R) (r_reply R) h (r_host R).

Definition set_host (R : rstate) (h : Z) : rstate :=
  RState (r_refuse R) (r_code R) (r_calls R) (r_spill R) (r_answer R) (r_nreplies R) (r_reply R) (r_state R) h.

Definition set_reply (R : rstate) (n : Z) (x : option (list byte)) : rstate :=
  RState (r_refuse R) (r_code R) (r_calls R) (r_spill R) (r_answer R) n x (r_state R) (r_host R).

Definition rec_record (R : rstate) (fn : Z) (A : list (list byte)) : rstate :=
  if Nat.ltb (length (r_calls R)) 16 then set_calls R (r_calls R ++ [(fn, A)]) else set_spill R (fn, A).

Definition rec_mix (R : rstate) (c : rcall) : rstate := set_state R (mixcall (r_state R) (fst c) (snd c)).

Definition rec_mix_host (R : rstate) (c : rcall) : rstate := set_host R (mixcall (r_host R) (fst c) (snd c)).

Definition hand_back (R : rstate) (t : list byte) : rstate * list byte := (set_answer R (Some t), t).

Definition rec_answer (R : rstate) (c : rcall) (shape : list byte) (changes : bool) : rstate * list byte :=
  if r_refuse R =? 0
  then hand_back (if changes then rec_mix R c else R) (inst shape)
  else hand_back R (resp (r_code R)).

Definition rec_answer_code (R : rstate) (code : Z) : rstate * Z := (set_answer R (Some (resp code)), code).

Definition rec_socket_send (R : rstate) (x : list byte) : rstate :=
  set_reply R (r_nreplies R + 1) (match x with [] => None | _ :: _ => Some x end).

Definition rec_clear (R : rstate) : rstate :=
  RState (r_refuse R) (r_code R) [] (r_spill R) None 0 None (r_state R) (r_host R).

Definition sarg (p : option (list byte)) : list byte :=
  match p with Some x => x | None => bstr "(null)"%string end.

Definition darg (p : option (list byte)) (d : list byte) : list byte :=
  match p with Some x => x | None => d end.

Definition daemon_shape (verb : string) : list byte := shape_of (bstr verb).

Definition first_word (T : list byte) : list byte := match words T with [] => [] | w :: _ => w end.

Definition dec_list (ids : list Z) : list byte :=
  match ids with [] => [] | i :: r => dec i ++ concat (map (fun j => SPACE :: dec j) r) end.

Definition rec_stub (R : rstate) (fn : Z) (A : list (list byte)) (shape : list byte) (changes : bool)
    : rstate * list byte :=
  rec_answer (rec_record R fn A) (fn, A) shape changes.

Definition rec_stub_code (R : rstate) (fn : Z) (A : list (list byte)) : rstate * Z :=
  let R1 := rec_record R fn A in
  if r_refuse R1 =? 0 then rec_answer_code (rec_mix R1 (fn, A)) 0 else rec_answer_code R1 (r_code R1).

Definition rec_stub_mix (R : rstate) (fn : Z) (A : list (list byte)) : rstate :=
  rec_mix (rec_record R fn A) (fn, A).

Definition socket_send_m (R : rstate) (x : list byte) : rstate * Z :=
  (rec_socket_send R x, Z.of_nat (length x)).

Definition sup_resp_m (R : rstate) (code : Z) : rstate * list byte := (R, resp code).

Definition pins_set_m (R : rstate) (uri files layout verdict : option (list byte)) : rstate * Z :=
  rec_stub_code R REC_PINS_SET [sarg uri; sarg files; sarg layout; darg verdict (bstr "-"%string)].

Definition pins_clear_m (R : rstate) (uri : option (list byte)) : rstate * Z :=
  rec_stub_code R REC_PINS_CLEAR [sarg uri].

Definition lv2_refusals_forget_m (R : rstate) (uri : option (list byte)) : rstate :=
  rec_stub_mix R REC_LV2_REFUSALS_FORGET [darg uri (bstr "*"%string)].

Definition descriptors_add_m (R : rstate) (uri : option (list byte)) : rstate :=
  rec_stub_mix R REC_DESCRIPTORS_ADD [sarg uri].

Definition sup_chain_m (R : rstate) (id : Z) (ids : list Z) : rstate * list byte :=
  rec_stub R REC_CHAIN [dec id; dec (Z.of_nat (length ids)); dec_list ids] (daemon_shape "chain") true.

Definition sup_chain_clear_m (R : rstate) (id : Z) : rstate * list byte :=
  rec_stub R REC_CHAIN_CLEAR [dec id] (daemon_shape "chain_clear") true.

Definition sup_add_m (R : rstate) (uri : option (list byte)) (id : Z) (placement client : option (list byte))
    : rstate * list byte :=
  let A := [sarg uri; dec id; darg placement (bstr "-"%string); darg client (bstr "-"%string)] in
  let R1 := rec_record R REC_ADD A in
  if (id <? 0) || (10000 <=? id) then hand_back R1 (resp (-1))
  else if negb (r_refuse R1 =? 0) then hand_back R1 (resp (r_code R1))
  else hand_back (rec_mix R1 (REC_ADD, A)) (resp id).

Definition sup_call_m (R : rstate) (id : Z) (line : list byte) : rstate * list byte :=
  rec_stub R REC_CALL [dec id; canon line] REC_MOD_HOST_SHAPE true.

Definition sup_remove_m (R : rstate) (id : Z) : rstate * list byte :=
  rec_stub R REC_REMOVE [dec id] REC_MOD_HOST_SHAPE true.

Definition sup_remove_all_m (R : rstate) : rstate * list byte :=
  rec_stub R REC_REMOVE_ALL [] REC_MOD_HOST_SHAPE true.

Definition sup_connect_m (R : rstate) (verb : option (list byte)) (line : list byte) (port_a port_b : option (list byte))
    : rstate * list byte :=
  rec_stub R REC_CONNECT [sarg verb; canon line; sarg port_a; sarg port_b] REC_MOD_HOST_SHAPE true.

Definition sup_broadcast_m (R : rstate) (line : list byte) : rstate * list byte :=
  rec_stub R REC_BROADCAST [canon line] REC_MOD_HOST_SHAPE true.

Definition sup_host_setting_m (R : rstate) (line : list byte) (toks : list (list byte)) : rstate :=
  let A := [canon line; dec (Z.of_nat (length toks)); join_sp toks] in
  rec_mix_host (rec_record R REC_HOST_SETTING A) (REC_HOST_SETTING, A).

Definition sup_instance_verb_m (R : rstate) (line : list byte) (ledger : Z) : rstate * list byte :=
  rec_stub R REC_INSTANCE_VERB [canon line; dec ledger] (shape_of (first_word line)) true.

Definition sup_worker_list_m (R : rstate) : rstate * list byte :=
  rec_stub R REC_WORKER_LIST [] (daemon_shape "worker_list") false.

Definition sup_instance_info_m (R : rstate) (id : Z) : rstate * list byte :=
  rec_stub R REC_INSTANCE_INFO [dec id] (daemon_shape "instance_info") false.

Definition sup_reset_m (R : rstate) (which : option (list byte)) : rstate * list byte :=
  rec_stub R REC_RESET [sarg which] (daemon_shape "supervisor_reset") true.

Definition sup_quarantine_clear_m (R : rstate) (which : option (list byte)) : rstate * list byte :=
  rec_stub R REC_QUARANTINE_CLEAR [sarg which] (daemon_shape "quarantine_clear") true.

Definition sup_policy_set_m (R : rstate) (format place : option (list byte)) : rstate * list byte :=
  rec_stub R REC_POLICY_SET [sarg format; sarg place] (daemon_shape "policy_set") true.

Definition sup_pin_accept_m (R : rstate) (uri : option (list byte)) : rstate * list byte :=
  rec_stub R REC_PIN_ACCEPT [sarg uri] (daemon_shape "pin_accept") true.

Definition sup_pool_config_m (R : rstate) (name : option (list byte)) (max : Z) : rstate * list byte :=
  rec_stub R REC_POOL_CONFIG [sarg name; dec max] (daemon_shape "pool_config") true.

Definition sup_lv2_worker_set_m (R : rstate) (uri worker : option (list byte)) : rstate * list byte :=
  rec_stub R REC_LV2_WORKER_SET [sarg uri; sarg worker] (daemon_shape "lv2_worker_set") true.

Definition sup_worker_env_m (R : rstate) (format cpus nice : option (list byte)) : rstate * list byte :=
  rec_stub R REC_WORKER_ENV [sarg format; sarg cpus; sarg nice] (daemon_shape "worker_env") true.

Definition sup_after_reply_m (R : rstate) (id : Z) (verb : option (list byte)) : rstate :=
  rec_record R REC_AFTER_REPLY [dec id; sarg verb].

Definition descriptors_get_m (R : rstate) (uri : option (list byte)) : rstate * list byte :=
  rec_stub R REC_DESCRIPTORS_GET [sarg uri] (daemon_shape "descriptor_get") false.

Definition descriptors_panel_get_m (R : rstate) (uri : option (list byte)) : rstate * list byte :=
  rec_stub R REC_DESCRIPTORS_PANEL_GET [sarg uri] (daemon_shape "panel_get") false.

Lemma rec_record_calls : forall R fn A, (length (r_calls R) < 16)%nat ->
  rec_record R fn A = set_calls R (r_calls R ++ [(fn, A)]).
Proof. intros R fn A H. unfold rec_record. apply Nat.ltb_lt in H. rewrite H. reflexivity. Qed.

Lemma rec_record_spill : forall R fn A, length (r_calls R) = 16%nat ->
  rec_record R fn A = set_spill R (fn, A).
Proof. intros R fn A H. unfold rec_record. rewrite H. reflexivity. Qed.

Lemma rec_record_length : forall R fn A, (length (r_calls R) <= 16)%nat ->
  (length (r_calls (rec_record R fn A)) <= 16)%nat.
Proof.
  intros R fn A H. unfold rec_record. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L]; cbn [r_calls set_calls set_spill].
  - rewrite length_app. cbn [length]. lia.
  - exact H.
Qed.

Lemma rec_answer_text : forall R c shape changes,
  snd (rec_answer R c shape changes) = if r_refuse R =? 0 then inst shape else resp (r_code R).
Proof. intros. unfold rec_answer. destruct (r_refuse R =? 0); reflexivity. Qed.

Lemma rec_answer_answer : forall R c shape changes,
  r_answer (fst (rec_answer R c shape changes)) = Some (snd (rec_answer R c shape changes)).
Proof. intros. unfold rec_answer. destruct (r_refuse R =? 0); [destruct changes|]; reflexivity. Qed.

Lemma rec_answer_refused_state : forall R c shape changes, r_refuse R <> 0 ->
  r_state (fst (rec_answer R c shape changes)) = r_state R.
Proof. intros R c shape changes H. unfold rec_answer. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.
