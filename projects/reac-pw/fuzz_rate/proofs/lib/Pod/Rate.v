(** fuzz_rate's expectation and reac_rate_prop_parse's answer over the pod bytes, the per-target part of the pod.h
    model (fuzz_role and fuzz_headamp have their own). Statement text and the lemma that joins the two:
    [parse_model_encode]. No function of a binary is proved here.

    An answer is (written, rc): rc is the int the function returns, and written is [Some v] when it writes v to its
    int out-parameter, [None] when it writes nothing. Both functions write exactly when rc is 1
    ([parse_model_shape], [expect_model_shape]), and v is then an int32 value. So in LLVMFuzzerTestOneInput
    (fuzz_rate.c:248-258), with [harness_parse null buf = (w, rc)] and [expect_model null r = (w', x)], where null is
    flags & 1: hz after the parse is [written_or 0x5a5a5a5a (w, rc)], want after expect_rate is
    [written_or 0 (w', x)], x = 0 selects check_absent(rc, hz), x = 1 check_rate(rc, hz, want), x = -1
    check_malformed(rc, hz). [harness_parse null bs] is the parse the harness makes (fuzz_rate.c:249): with
    flags & 1 it passes NULL and the parse is -1 with no write (reac_rate_cfg.c:117), else it passes the pod, and the
    answer is [parse_model bs]. On an uncorrupted pod it equals the expectation ([harness_parse_build]).

    [parse_model bs] is reac_rate_prop_parse(pod, &hz) (src/reac_rate_cfg.c:97-152) on the bytes bs of a pod. It reads
    the pod as SPA 1.6 does ([spa_view_of], Pod/Spa.v): not a Props object is -1 (:117-118); no SPA_PROP_params
    property, or one whose value is not a Struct, is 0 (:121-124); else the first (String key, value) pair whose key
    is "reac.cfg.rate" decides (:126-150), and none is 0 (:151). Its value is read as value_pod_to_hz does
    (:97-113): an Int i is 1 and i; a Float is 1 and reac_float_nearest(f, INT_MIN, INT_MAX)'s integer, or -1 when
    it has none; any other value is -1. [nearest] (Pod/Nearest.v) stands for reac_float_nearest's result: the readers'
    bounds INT_MIN and INT_MAX are [INT32_MIN] and [INT32_MAX], inside Nearest.v's (-2^53, 2^53) condition.

    [expect_model null r] is fuzz_rate.c's expect_rate(pp, null, &want) (fuzz_rate.c:63-87) over the record r: null
    or not is_props is -1; else the pod_next_pair loop over ent[] when params_struct, where the first pair keyed
    "reac.cfg.rate" decides: pod_int gives 1 and i, pod_float with pod_nearest(f, INT32_MIN, INT32_MAX) gives 1 and
    the integer (read as [nearest]: Nearest.v's [pod_nearest_exact_eq]), anything else -1; no such pair (or no params
    Struct) is 0. *)
From Stdlib Require Import String ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables Model Accessors Spa Nearest.
Import ListNotations.
Open Scope Z_scope.

(** "reac.cfg.rate": REAC_CFG_RATE_PROP (libreac reac_cfg.h; fuzz_rate.c:71), which reac_rate_cfg.h renames
    REAC_CFG_PROP_RATE (reac_rate_cfg.c:142): the key, no NUL. Both strcmp calls of each image compare with the
    NUL-terminated text at 0x1045e (Pod/RateImg.v: [rate_key_plain], [rate_key_ubsan]). *)
Definition RATE_KEY : list byte := sbytes "reac.cfg.rate".

(** The int the caller holds after a call that answered a, when it held d before. *)
Definition written_or (d : Z) (a : option Z * Z) : Z := match fst a with Some v => v | None => d end.

(** The first pair keyed "reac.cfg.rate" decides; none gives 0. [vf] reads its value. *)
Definition rate_of_pairs (vf : ent -> option Z * Z) (ps : list (list byte * ent)) : option Z * Z :=
  match find (fun ke => bytes_eqb (fst ke) RATE_KEY) ps with
  | Some (_, v) => vf v
  | None => (None, 0)
  end.

(** value_pod_to_hz (reac_rate_cfg.c:97-113) and the write of :146-149. *)
Definition spa_rate_value (e : ent) : option Z * Z :=
  match spa_get_int e with
  | Some i => (Some i, 1)
  | None =>
      match spa_get_float e with
      | Some b => match nearest b INT32_MIN INT32_MAX with Some n => (Some n, 1) | None => (None, -1) end
      | None => (None, -1)
      end
  end.

Definition parse_model (bs : list byte) : option Z * Z :=
  match spa_view_of bs with
  | VNotProps => (None, -1)
  | VNoParams => (None, 0)
  | VParamsNotStruct => (None, 0)
  | VPods cs => rate_of_pairs spa_rate_value (pairs_by spa_get_string cs None)
  end.

(** The parse the harness makes (fuzz_rate.c:249): reac_rate_prop_parse(flags & 1 ? NULL : pod, &hz). NULL is -1
    and writes nothing (reac_rate_cfg.c:117). *)
Definition harness_parse (null : bool) (bs : list byte) : option Z * Z :=
  if null then (None, -1) else parse_model bs.

(** expect_rate's value rule (fuzz_rate.c:76-84): pod_int, else pod_float and pod_nearest, else -1. *)
Definition expect_value (e : ent) : option Z * Z :=
  match int_of e with
  | Some i => (Some i, 1)
  | None =>
      match float_of e with
      | Some b => match nearest b INT32_MIN INT32_MAX with Some n => (Some n, 1) | None => (None, -1) end
      | None => (None, -1)
      end
  end.

Definition expect_model (null : bool) (r : pod_rec) : option Z * Z :=
  if null || negb (is_props r) then (None, -1)
  else if negb (params_struct r) then (None, 0)
  else rate_of_pairs expect_value (pairs (ents r)).

(** ** The parse's answer on an uncorrupted pod is the expectation *)
Lemma spa_get_string_key_of : forall e, e_size e < SPA_POD_MAX_SIZE -> spa_get_string e = key_of e.
Proof. intros e H. unfold spa_get_string, key_of. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.
Lemma spa_get_int_int_of : forall e, e_size e < SPA_POD_MAX_SIZE -> spa_get_int e = int_of e.
Proof. intros e H. unfold spa_get_int, int_of. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.
Lemma spa_get_float_float_of : forall e, e_size e < SPA_POD_MAX_SIZE -> spa_get_float e = float_of e.
Proof. intros e H. unfold spa_get_float, float_of. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma spa_rate_value_expect : forall e, e_size e < SPA_POD_MAX_SIZE -> spa_rate_value e = expect_value e.
Proof.
  intros e H. unfold spa_rate_value, expect_value. rewrite spa_get_int_int_of, spa_get_float_float_of by exact H.
  reflexivity.
Qed.

Lemma rate_of_pairs_ext : forall vf vg ps, (forall k e, In (k, e) ps -> vf e = vg e) ->
  rate_of_pairs vf ps = rate_of_pairs vg ps.
Proof.
  intros vf vg ps H. unfold rate_of_pairs.
  destruct (find (fun ke => bytes_eqb (fst ke) RATE_KEY) ps) as [[k e]|] eqn:E; [|reflexivity].
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
  apply rate_of_pairs_ext. intros k e Hin. apply spa_rate_value_expect. apply Hsz.
  eapply pairs_by_in. exact Hin.
Qed.

(** With the NULL flag, expect_rate is -1, as the parse of NULL is (reac_rate_cfg.c:117). *)
Lemma expect_model_null : forall r, expect_model true r = (None, -1).
Proof. reflexivity. Qed.

(** ** The shape of an answer: a write exactly on rc 1, of an int32 value *)
Definition answer_ok (a : option Z * Z) : Prop :=
  match a with
  | (Some v, rc) => rc = 1 /\ INT32_MIN <= v <= INT32_MAX
  | (None, rc) => rc = 0 \/ rc = -1
  end.

Lemma nearest_range : forall b n, nearest b INT32_MIN INT32_MAX = Some n -> INT32_MIN <= n <= INT32_MAX.
Proof.
  intros b n H. unfold nearest in H. destruct (near_f32 b) as [r|]; [|discriminate].
  destruct ((INT32_MIN <=? r) && (r <=? INT32_MAX)) eqn:E; [|discriminate].
  injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

Lemma s32_rd32_range : forall l, INT32_MIN <= s32 (rd32 l) <= INT32_MAX.
Proof. intros l. pose proof (s32_range (rd32 l) (rd32_range l)) as H. unfold INT32_MIN, INT32_MAX. lia. Qed.

Lemma spa_get_int_range : forall e i, spa_get_int e = Some i -> INT32_MIN <= i <= INT32_MAX.
Proof.
  intros e i H. unfold spa_get_int in H.
  destruct ((e_size e <? SPA_POD_MAX_SIZE) && (e_type e =? POD_INT) && (4 <=? e_size e)); [|discriminate].
  injection H as <-. apply s32_rd32_range.
Qed.

Lemma int_of_range : forall e i, int_of e = Some i -> INT32_MIN <= i <= INT32_MAX.
Proof.
  intros e i H. unfold int_of in H. destruct ((e_type e =? POD_INT) && (4 <=? e_size e)); [|discriminate].
  injection H as <-. apply s32_rd32_range.
Qed.

Lemma rate_of_pairs_ok : forall vf ps, (forall e, answer_ok (vf e)) -> answer_ok (rate_of_pairs vf ps).
Proof.
  intros vf ps H. unfold rate_of_pairs.
  destruct (find (fun ke => bytes_eqb (fst ke) RATE_KEY) ps) as [[k e]|]; [apply H | exact (or_introl eq_refl)].
Qed.

Lemma spa_rate_value_ok : forall e, answer_ok (spa_rate_value e).
Proof.
  intros e. unfold spa_rate_value.
  destruct (spa_get_int e) as [i|] eqn:Ei; [exact (conj eq_refl (spa_get_int_range e i Ei))|].
  destruct (spa_get_float e) as [b|]; [|exact (or_intror eq_refl)].
  destruct (nearest b INT32_MIN INT32_MAX) as [n|] eqn:N; [|exact (or_intror eq_refl)].
  exact (conj eq_refl (nearest_range b n N)).
Qed.

Lemma expect_value_ok : forall e, answer_ok (expect_value e).
Proof.
  intros e. unfold expect_value.
  destruct (int_of e) as [i|] eqn:Ei; [exact (conj eq_refl (int_of_range e i Ei))|].
  destruct (float_of e) as [b|]; [|exact (or_intror eq_refl)].
  destruct (nearest b INT32_MIN INT32_MAX) as [n|] eqn:N; [|exact (or_intror eq_refl)].
  exact (conj eq_refl (nearest_range b n N)).
Qed.

Lemma parse_model_shape : forall bs, answer_ok (parse_model bs).
Proof.
  intros bs. unfold parse_model. destruct (spa_view_of bs) as [| | |cs].
  - exact (or_intror eq_refl).
  - exact (or_introl eq_refl).
  - exact (or_introl eq_refl).
  - apply rate_of_pairs_ok. exact spa_rate_value_ok.
Qed.

Lemma expect_model_shape : forall null r, answer_ok (expect_model null r).
Proof.
  intros null r. unfold expect_model.
  destruct (null || negb (is_props r)); [exact (or_intror eq_refl)|].
  destruct (negb (params_struct r)); [exact (or_introl eq_refl)|].
  apply rate_of_pairs_ok. exact expect_value_ok.
Qed.

(** On every record pod_build makes and leaves uncorrupted. *)
Corollary parse_model_build : forall inp r rest, pod_build inp = (r, rest) -> corrupt r = false ->
  parse_model (buf r) = expect_model false r.
Proof.
  intros inp r rest H Hc. pose proof (pod_build_wf inp r rest H) as Hw. unfold buf, corrupt in *.
  destruct (p_corr r); [discriminate|]. apply parse_model_encode. exact Hw.
Qed.

(** The harness's parse, with or without the NULL flag, is expect_rate's answer on every uncorrupted record. *)
Corollary harness_parse_build : forall null inp r rest, pod_build inp = (r, rest) -> corrupt r = false ->
  harness_parse null (buf r) = expect_model null r.
Proof.
  intros null inp r rest H Hc. destruct null; [reflexivity | exact (parse_model_build inp r rest H Hc)].
Qed.
