(** fuzz_role's expectation and reac_role_prop_parse's answer over the pod bytes, the per-target part of the pod.h
    model (fuzz_rate and fuzz_headamp have their own). Statement text and the lemma that joins the two:
    [parse_model_encode]. No function of a binary is proved here.

    [parse_model bs] is reac_role_prop_parse(pod, &role) (src/reac_role_cfg.c:45-104) on the bytes bs of a pod, as
    (role written, rc): rc 1 writes MASTER or SLAVE, rc 0 and rc -1 write nothing. It reads the pod as SPA 1.6 does
    ([spa_view_of], Pod/Spa.v), takes the first (String key, value) pair whose key is "reac.cfg.role", and reads the
    value as value_pod_to_role_flag and the switch do (an Int, or a Float through reac_float_nearest(f, INT_MIN,
    INT_MAX), then 0 is MASTER, 1 is SLAVE, anything else -1). [nearest] (Pod/Nearest.v) stands for
    reac_float_nearest's result.

    [expect_model null r] is fuzz_role.c's expect_role(pp, null, &want) (fuzz_role.c:41-63) over the record r, as
    (want written, x), with pod_nearest(f, INT32_MIN, INT32_MAX) read as [nearest]. *)
From Stdlib Require Import String ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Tables Model Accessors Spa Nearest.
Import ListNotations.
Open Scope Z_scope.

(** enum reac_role (libreac reac_role.h): MASTER 0, SLAVE 1. *)
Inductive role := MASTER | SLAVE.
Definition role_z (r : role) : Z := match r with MASTER => 0 | SLAVE => 1 end.

(** "reac.cfg.role": REAC_CFG_ROLE_PROP (libreac reac_cfg.h:62; fuzz_role.c:48), which reac_role_cfg.h:62 renames
    REAC_CFG_PROP_ROLE (reac_role_cfg.c:90): the key, no NUL. *)
Definition ROLE_KEY : list byte := sbytes "reac.cfg.role".

(** The switch on the flag (reac_role_cfg.c:97-100, fuzz_role.c:57-60). *)
Definition flag_rc (v : Z) : option role * Z :=
  if v =? 0 then (Some MASTER, 1) else if v =? 1 then (Some SLAVE, 1) else (None, -1).

(** The first pair keyed "reac.cfg.role" decides; none gives 0. [vf] reads its value. *)
Definition role_of_pairs (vf : ent -> option role * Z) (ps : list (list byte * ent)) : option role * Z :=
  match find (fun ke => bytes_eqb (fst ke) ROLE_KEY) ps with
  | Some (_, v) => vf v
  | None => (None, 0)
  end.

(** value_pod_to_role_flag and the switch (reac_role_cfg.c:45-61, :94-101). *)
Definition spa_role_value (e : ent) : option role * Z :=
  match spa_get_int e with
  | Some i => flag_rc i
  | None =>
      match spa_get_float e with
      | Some b => match nearest b INT32_MIN INT32_MAX with Some n => flag_rc n | None => (None, -1) end
      | None => (None, -1)
      end
  end.

Definition parse_model (bs : list byte) : option role * Z :=
  match spa_view_of bs with
  | VNotProps => (None, -1)
  | VNoParams => (None, 0)
  | VParamsNotStruct => (None, 0)
  | VPods cs => role_of_pairs spa_role_value (pairs_by spa_get_string cs None)
  end.

(** expect_role's value rule (fuzz_role.c:50-60): pod_int, else pod_float and pod_nearest. *)
Definition expect_value (e : ent) : option role * Z :=
  match int_of e with
  | Some i => flag_rc i
  | None =>
      match float_of e with
      | Some b => match nearest b INT32_MIN INT32_MAX with Some n => flag_rc n | None => (None, -1) end
      | None => (None, -1)
      end
  end.

Definition expect_model (null : bool) (r : pod_rec) : option role * Z :=
  if null || negb (is_props r) then (None, -1)
  else if negb (params_struct r) then (None, 0)
  else role_of_pairs expect_value (pairs (ents r)).

(** ** The parse's answer on an uncorrupted pod is the expectation *)
Lemma spa_get_string_key_of : forall e, e_size e < SPA_POD_MAX_SIZE -> spa_get_string e = key_of e.
Proof. intros e H. unfold spa_get_string, key_of. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.
Lemma spa_get_int_int_of : forall e, e_size e < SPA_POD_MAX_SIZE -> spa_get_int e = int_of e.
Proof. intros e H. unfold spa_get_int, int_of. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.
Lemma spa_get_float_float_of : forall e, e_size e < SPA_POD_MAX_SIZE -> spa_get_float e = float_of e.
Proof. intros e H. unfold spa_get_float, float_of. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma spa_role_value_expect : forall e, e_size e < SPA_POD_MAX_SIZE -> spa_role_value e = expect_value e.
Proof.
  intros e H. unfold spa_role_value, expect_value. rewrite spa_get_int_int_of, spa_get_float_float_of by exact H.
  reflexivity.
Qed.

Lemma role_of_pairs_ext : forall vf vg ps, (forall k e, In (k, e) ps -> vf e = vg e) ->
  role_of_pairs vf ps = role_of_pairs vg ps.
Proof.
  intros vf vg ps H. unfold role_of_pairs.
  destruct (find (fun ke => bytes_eqb (fst ke) ROLE_KEY) ps) as [[k e]|] eqn:E; [|reflexivity].
  apply find_some in E as [Hin _]. exact (H k e Hin).
Qed.

Theorem parse_model_encode : forall r, pod_rec_wf r -> parse_model (pod_encode r) = expect_model false r.
Proof.
  intros r Hw. unfold parse_model. rewrite (spa_view_encode r Hw).
  unfold record_view, expect_model, params_struct, ents. cbn [orb].
  destruct (is_props r); cbn [negb]; [|reflexivity].
  destruct (first_params (p_props r)) as [[i|es]|] eqn:EF; cbn [negb]; try reflexivity.
  assert (Hes : Forall ent_wf es).
  { destruct Hw as (_ & _ & He & _). unfold first_params in EF.
    destruct (find (fun kv => fst kv =? POD_PROP_PARAMS) (p_props r)) as [kv|] eqn:F; [|discriminate].
    cbn [option_map] in EF. injection EF as EF. apply find_some in F as [Hin _].
    apply all_ents_Forall in He. rewrite Forall_forall in He. specialize (He kv Hin). rewrite EF in He. exact He. }
  assert (Hsz : forall e, In e es -> e_size e < SPA_POD_MAX_SIZE).
  { intros e Hin. rewrite Forall_forall in Hes. destruct (Hes e Hin) as (_ & _ & Hz). unfold SPA_POD_MAX_SIZE. lia. }
  rewrite (pairs_by_ext spa_get_string key_of es None) by (intros e Hin; apply spa_get_string_key_of; auto).
  apply role_of_pairs_ext. intros k e Hin. apply spa_role_value_expect. apply Hsz.
  eapply pairs_by_in. exact Hin.
Qed.

(** With the NULL flag, expect_role is -1, as the parse of NULL is (reac_role_cfg.c:65). *)
Lemma expect_model_null : forall r, expect_model true r = (None, -1).
Proof. reflexivity. Qed.

(** On every record pod_build makes and leaves uncorrupted. *)
Corollary parse_model_build : forall inp r rest, pod_build inp = (r, rest) -> corrupt r = false ->
  parse_model (buf r) = expect_model false r.
Proof.
  intros inp r rest H Hc. pose proof (pod_build_wf inp r rest H) as Hw. unfold buf, corrupt in *.
  destruct (p_corr r); [discriminate|]. apply parse_model_encode. exact Hw.
Qed.
