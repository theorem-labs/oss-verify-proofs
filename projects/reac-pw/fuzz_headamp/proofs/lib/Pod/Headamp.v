(** fuzz_headamp's expectation and reac_headamp_prop_parse_result's answer over the pod bytes: the per-target part of
    the pod.h model (fuzz_role's twin is its Pod/Role.v). Statement text and the lemmas that join the two:
    [strtol_read_channel] (the harness's channel reading is musl strtol's) and [parse_model_encode] (on an uncorrupted
    pod the parse answers what expect_of expects). No function of a binary is proved here.

    [parse_model bs cap] is reac_headamp_prop_parse_result(pod, out, cap, &res) (reac-pw f86a30a3
    src/reac_headamp_prop.c:108-182) on the bytes bs of a pod, as (rc, the cells written to out[0..n) in order,
    (res.n, res.keys, res.refusal)). It reads the pod as SPA 1.6 does ([spa_view_of], Pod/Spa.v), pairs the params
    Struct's pods with spa_pod_get_string's key test ([pairs_by spa_get_string]), and folds the pairs: the prefix test,
    keys++, parse_key ([parse_key], strtol read as the released musl contract's s10_val / s10_end, Pod/Strtol.v),
    value_pod_to_byte ([parse_value]: spa_pod_get_bool, spa_pod_get_int, spa_pod_get_float read by
    reac_float_nearest(f, 0, 255) = [nearest] (Pod/Nearest.v)), value_in_range, the first refusal, and the n >= max
    break. The parse of NULL is (-1, [], (0, 0, NONE)) (reac_headamp_prop.c:115-121): [expect_model_null].

    [expect_model null cap r] is fuzz_headamp.c's expect_of(pp, null, cap, &x) (fuzz_headamp.c:109-157) over the
    record r, as (x.rc, x.cell[0..n), (x.n, x.keys, x.refusal)): pod_next_pair's pairs ([pairs], Pod/Accessors.v),
    read_channel (fuzz_headamp.c:67-90, with its acc > 1000000 'big' rule), the strcmp chain, cell_value
    (fuzz_headamp.c:94-107: pod_bool, pod_int, pod_float and pod_nearest(f, 0, 255) = [nearest]). *)
From Stdlib Require Import String ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import
  Cursor Model Accessors Spa Nearest SpaBool Strtol.
Import ListNotations.
Open Scope Z_scope.

(** ** The numbers *)
(** enum reac_headamp_refuse (reac-pw src/reac_headamp_state.h:68-75): NONE 0, NO_BOX 1, BOX_MASTER 2, NO_BASE 3,
    BAD_KEY 4, OUT_OF_RANGE 5. *)
Definition REFUSE_NONE : Z := 0.
Definition REFUSE_BAD_KEY : Z := 4.
Definition REFUSE_OUT_OF_RANGE : Z := 5.
(** enum reac_headamp_param (libreac include/reac/reac_ctrlblk.h:759-765: PHANTOM 0, PAD 1, SENS 2), which the
    parse returns (reac_headamp_prop.c:53-58); the harness's HA_PHANTOM / HA_PAD / HA_SENS (fuzz_headamp.c:46-48) are
    the same numbers. *)
Definition HA_PHANTOM : Z := 0.
Definition HA_PAD : Z := 1.
Definition HA_SENS : Z := 2.
(** The channel space: the parse's REAC_HEADAMP_MAX_CH 48 (libreac include/reac/reac_ctrlblk.h:784, included by
    reac/reac_ctrl.h:36; used at reac_headamp_prop.c:80) and the harness's HA_CHANNELS 0x30 (fuzz_headamp.c:42, from
    facts/reac_facts.h:1080 REAC_HEADAMP_CH_SPAN 0x30). *)
Definition REAC_HEADAMP_MAX_CH : Z := 48.
Definition HA_CHANNELS : Z := 0x30.
(** The last sens step: REAC_HEADAMP_SENS_MAX 0x37 (reac_ctrlblk.h:273 and facts/reac_facts.h:1074, the same value;
    used at reac_headamp_prop.c:96) and the harness's HA_SENS_MAX 0x37 (fuzz_headamp.c:44). *)
Definition REAC_HEADAMP_SENS_MAX : Z := 0x37.
Definition HA_SENS_MAX : Z := 0x37.

Local Open Scope string_scope.
(** REAC_HEADAMP_PROP_PREFIX (reac_headamp_prop.h:32) = HA_PREFIX (fuzz_headamp.c:39), no NUL; the param names
    (reac_headamp_prop.c:53-57 = fuzz_headamp.c:132-133). *)
Definition HA_PREFIX : list byte := sbytes "reac.headamp.".
Definition NAME_PHANTOM : list byte := sbytes "phantom".
Definition NAME_PAD : list byte := sbytes "pad".
Definition NAME_SENS : list byte := sbytes "sens".
Local Close Scope string_scope.

(** One setting: (ch, param, value), the three bytes of struct reac_headamp_setting (libreac
    include/reac/reac_headamp_tx.h:92-96) and of the harness's struct cell (fuzz_headamp.c:52-54). *)
Definition cell := (Z * Z * Z)%type.

(** ** What both read the same way *)
(** strncmp(k, prefix, strlen(prefix)) == 0 on the C string k (reac_headamp_prop.c:148, fuzz_headamp.c:120): the
    prefix has no NUL, so a shorter k differs at its NUL. *)
Definition ha_prefix (k : list byte) : bool := bytes_eqb (firstn (length HA_PREFIX) k) HA_PREFIX.

(** param_name_to_id (reac_headamp_prop.c:51-60) and the harness's strcmp chain (fuzz_headamp.c:132-133), on the C
    string name. *)
Definition param_of_name (name : list byte) : option Z :=
  if bytes_eqb name NAME_PHANTOM then Some HA_PHANTOM
  else if bytes_eqb name NAME_PAD then Some HA_PAD
  else if bytes_eqb name NAME_SENS then Some HA_SENS
  else None.

(** A key's verdict: BAD_KEY, OUT_OF_RANGE, or the cell address (channel, param). *)
Inductive key_dec := KBad | KRange | KCell (ch p : Z).

(** ** The parse (reac_headamp_prop.c) *)
(** parse_key(rest, &ch, &param) (reac_headamp_prop.c:70-85) on the C string rest = k + 13. strtol(rest, &dot, 10)
    returns c = [s10_val rest] and sets dot = rest + [s10_end rest] (the released musl strtol contract,
    Pod/Strtol.v); dot == rest exactly when s10_end rest = 0; *dot is byte s10_end of rest and its NUL. *)
Definition parse_key (rest : list byte) : key_dec :=
  let e := s10_end rest in
  if (e =? 0) || negb (bv_unsigned (nth (Z.to_nat e) rest NUL) =? 46) then KBad
  else match param_of_name (cstr (skipn (S (Z.to_nat e)) rest)) with
       | None => KBad
       | Some p =>
           let c := s10_val rest in
           if (c <? 0) || (REAC_HEADAMP_MAX_CH <=? c) then KRange else KCell c p
       end.

(** value_pod_to_byte(v, &value) (reac_headamp_prop.c:24-47): Some value for 0, None for -1. *)
Definition parse_value (e : ent) : option Z :=
  match spa_get_bool e with
  | Some b => Some (if b then 1 else 0)
  | None =>
      match spa_get_int e with
      | Some i => if (i <? 0) || (255 <? i) then None else Some i
      | None => match spa_get_float e with Some f => nearest f 0 255 | None => None end
      end
  end.

(** value_in_range(param, value) (reac_headamp_prop.c:89-100). *)
Definition value_in_range (p v : Z) : bool :=
  if (p =? HA_PHANTOM) || (p =? HA_PAD) then v <=? 1
  else if p =? HA_SENS then v <=? REAC_HEADAMP_SENS_MAX
  else false.

(** One pair whose key has the prefix (reac_headamp_prop.c:155-167): a refusal code, or the cell. *)
Definition parse_cell (k : list byte) (v : ent) : Z + cell :=
  match parse_key (skipn (length HA_PREFIX) k) with
  | KBad => inl REFUSE_BAD_KEY
  | KRange => inl REFUSE_OUT_OF_RANGE
  | KCell ch p =>
      match parse_value v with
      | Some b => if value_in_range p b then inr (ch, p, b) else inl REFUSE_OUT_OF_RANGE
      | None => inl REFUSE_OUT_OF_RANGE
      end
  end.

(** ** The harness (fuzz_headamp.c) *)
(** read_channel(s, &v, &big) (fuzz_headamp.c:67-90). *)
Definition rc_blank (b : byte) : bool :=                                 (* :70-71 *)
  let c := bv_unsigned b in (c =? 32) || (c =? 9) || (c =? 10) || (c =? 11) || (c =? 12) || (c =? 13).
Definition rc_digit (b : byte) : bool := (48 <=? bv_unsigned b) && (bv_unsigned b <=? 57).   (* :79 *)
Fixpoint rc_blanks (s : list byte) : nat :=
  match s with b :: s' => if rc_blank b then S (rc_blanks s') else O | [] => O end.
(** :74-75: neg, and the characters the sign takes. *)
Definition rc_sign (t : list byte) : bool * nat :=
  match t with
  | b :: _ => if (bv_unsigned b =? 43) || (bv_unsigned b =? 45) then (bv_unsigned b =? 45, 1%nat) else (false, 0%nat)
  | [] => (false, 0%nat)
  end.
(** :79-85: (acc, big, the digits read). *)
Fixpoint rc_digits (acc : Z) (big : bool) (s : list byte) : Z * bool * nat :=
  match s with
  | b :: s' =>
      if rc_digit b then
        let r := if 1000000 <? acc then rc_digits acc true s'
                 else rc_digits (acc * 10 + (bv_unsigned b - 48)) big s' in
        (fst (fst r), snd (fst r), S (snd r))
      else (acc, big, O)
  | [] => (acc, big, O)
  end.
(** (the value returned, *v, *big); with no digit it returns 0, leaves *v (expect_of's ch stays 0) and *big = 0. *)
Definition read_channel (s : list byte) : nat * Z * bool :=
  let i0 := rc_blanks s in
  let nk := rc_sign (skipn i0 s) in
  let d := (i0 + snd nk)%nat in
  let r := rc_digits 0 false (skipn d s) in
  if (snd r =? 0)%nat then (0%nat, 0, snd (fst r))
  else ((d + snd r)%nat, if fst nk then - fst (fst r) else fst (fst r), snd (fst r)).

(** fuzz_headamp.c:123-138 on rest = k + 13. *)
Definition expect_key (rest : list byte) : key_dec :=
  let '(used, ch, big) := read_channel rest in
  if (used =? 0)%nat || negb (bv_unsigned (nth used rest NUL) =? 46) then KBad
  else match param_of_name (cstr (skipn (S used) rest)) with
       | None => KBad
       | Some p => if big || (ch <? 0) || (HA_CHANNELS <=? ch) then KRange else KCell ch p
       end.

(** cell_value(e) (fuzz_headamp.c:94-107): the value, or -1. *)
Definition cell_value (e : ent) : Z :=
  match bool_of e with
  | Some b => if b then 1 else 0
  | None =>
      match int_of e with
      | Some i => if (0 <=? i) && (i <=? 255) then i else -1
      | None =>
          match float_of e with
          | Some f => match nearest f 0 255 with Some n => n | None => -1 end
          | None => -1
          end
      end
  end.

(** One pair whose key has the prefix (fuzz_headamp.c:123-148). *)
Definition expect_cell (k : list byte) (v : ent) : Z + cell :=
  match expect_key (skipn (length HA_PREFIX) k) with
  | KBad => inl REFUSE_BAD_KEY
  | KRange => inl REFUSE_OUT_OF_RANGE
  | KCell ch p =>
      let value := cell_value v in
      if (value <? 0) || ((if p =? HA_SENS then HA_SENS_MAX else 1) <? value) then inl REFUSE_OUT_OF_RANGE
      else inr (ch, p, value)
  end.

(** ** The pair loop both run (reac_headamp_prop.c:135-175, fuzz_headamp.c:119-155) *)
(** From (cells written, keys, refusal): a key without the prefix is skipped; else keys++; a refusal is kept when it is
    the first; a cell when the cells are full (n >= cap) stops the loop, else it is written. *)
Fixpoint ha_fold (cellf : list byte -> ent -> Z + cell) (cap : Z) (ps : list (list byte * ent))
    (cells : list cell) (keys rf : Z) : list cell * Z * Z :=
  match ps with
  | [] => (cells, keys, rf)
  | (k, v) :: ps' =>
      if negb (ha_prefix k) then ha_fold cellf cap ps' cells keys rf
      else
        match cellf k v with
        | inl bad => ha_fold cellf cap ps' cells (keys + 1) (if rf =? REFUSE_NONE then bad else rf)
        | inr c =>
            if cap <=? Z.of_nat (length cells) then (cells, keys + 1, rf)
            else ha_fold cellf cap ps' (cells ++ [c]) (keys + 1) rf
        end
  end.

Definition ha_result (o : list cell * Z * Z) : Z * list cell * (Z * Z * Z) :=
  let '(cells, keys, rf) := o in (Z.of_nat (length cells), cells, (Z.of_nat (length cells), keys, rf)).

Definition parse_model (bs : list byte) (cap : Z) : Z * list cell * (Z * Z * Z) :=
  match spa_view_of bs with
  | VNotProps => (-1, [], (0, 0, REFUSE_NONE))
  | VNoParams | VParamsNotStruct => (0, [], (0, 0, REFUSE_NONE))
  | VPods cs => ha_result (ha_fold parse_cell cap (pairs_by spa_get_string cs None) [] 0 REFUSE_NONE)
  end.

Definition expect_model (null : bool) (cap : Z) (r : pod_rec) : Z * list cell * (Z * Z * Z) :=
  if null || negb (is_props r) then (-1, [], (0, 0, REFUSE_NONE))
  else if negb (params_struct r) then (0, [], (0, 0, REFUSE_NONE))
  else ha_result (ha_fold expect_cell cap (pairs (ents r)) [] 0 REFUSE_NONE).

(** ** The two channel readings agree *)
Lemma rc_blank_c_space : forall b, rc_blank b = c_space b.
Proof.
  intros b. unfold rc_blank, c_space. set (c := bv_unsigned b).
  destruct (Z.eqb_spec c 32); [reflexivity|]. cbn [orb].
  destruct (Z.leb_spec 9 c), (Z.leb_spec c 13); cbn [andb];
    repeat match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y) end;
    cbn [orb]; try reflexivity; exfalso; lia.
Qed.

Lemma rc_digit_c_digit : forall b, rc_digit b = c_digit b.
Proof. reflexivity. Qed.

Lemma rc_blanks_skip : forall s,
  skipn (rc_blanks s) s = skip_space s /\ (rc_blanks s + length (skip_space s) = length s)%nat.
Proof.
  induction s as [|b s IH]; cbn [rc_blanks skip_space]; [split; reflexivity|].
  rewrite rc_blank_c_space. destruct (c_space b); cbn [skipn length].
  - destruct IH as [IH1 IH2]. split; [exact IH1 | lia].
  - split; reflexivity.
Qed.

Lemma rc_sign_split : forall t,
  sign_split t = (fst (rc_sign t), skipn (snd (rc_sign t)) t) /\ (snd (rc_sign t) <= length t)%nat.
Proof.
  intros [|b r]; [split; [reflexivity | cbn; lia]|]. unfold sign_split, rc_sign.
  destruct (bv_unsigned b =? 45) eqn:E45; destruct (bv_unsigned b =? 43) eqn:E43; cbn [orb fst snd skipn length];
    (split; [reflexivity | lia]).
Qed.

Lemma rc_digits_nd : forall s acc big, snd (rc_digits acc big s) = ndig s.
Proof.
  induction s as [|b s IH]; intros acc big; cbn [rc_digits ndig]; [reflexivity|].
  rewrite rc_digit_c_digit. destruct (c_digit b); [|reflexivity]. cbn [snd]. f_equal.
  destruct (1000000 <? acc); apply IH.
Qed.

Lemma rc_digits_true : forall s acc, snd (fst (rc_digits acc true s)) = true.
Proof.
  induction s as [|b s IH]; intros acc; cbn [rc_digits]; [reflexivity|].
  destruct (rc_digit b); [|reflexivity]. cbn [fst snd]. destruct (1000000 <? acc); apply IH.
Qed.

(** The 'big' rule: without it the reading is exact (and at most 10000009); with it the exact value is at least 10^7. *)
Lemma rc_digits_false : forall s acc, 0 <= acc <= 10000009 ->
  (snd (fst (rc_digits acc false s)) = false ->
     fst (fst (rc_digits acc false s)) = dval acc s /\ fst (fst (rc_digits acc false s)) <= 10000009) /\
  (snd (fst (rc_digits acc false s)) = true -> 10000000 <= dval acc s).
Proof.
  induction s as [|b s IH]; intros acc Ha; cbn [rc_digits dval].
  - cbn [fst snd]. split; [intros _; split; lia | intros H; discriminate H].
  - rewrite rc_digit_c_digit. destruct (c_digit b) eqn:Ed.
    2: { cbn [fst snd]. split; [intros _; split; lia | intros H; discriminate H]. }
    unfold c_digit in Ed. apply andb_prop in Ed as [D1 D2]. apply Z.leb_le in D1. apply Z.leb_le in D2.
    cbn [fst snd]. destruct (Z.ltb_spec 1000000 acc) as [Hb|Hb]; cbn [fst snd].
    + rewrite rc_digits_true. split; [intros H; discriminate H|]. intros _.
      pose proof (dval_mono s (10 * acc + (bv_unsigned b - 48)) ltac:(lia)). lia.
    + replace (10 * acc + (bv_unsigned b - 48)) with (acc * 10 + (bv_unsigned b - 48)) by lia. apply IH. lia.
Qed.

(** read_channel over strtol's parts: the blanks and the sign are skip_space and sign_split. *)
Lemma read_channel_alt : forall s,
  read_channel s =
  (let u := s10_rest s in
   let r := rc_digits 0 false u in
   if (snd r =? 0)%nat then (0%nat, 0, snd (fst r))
   else ((length s - length u + snd r)%nat, if s10_neg s then - fst (fst r) else fst (fst r), snd (fst r))).
Proof.
  intros s. unfold read_channel, s10_rest, s10_neg. cbv zeta.
  destruct (rc_blanks_skip s) as [E1 L1]. destruct (rc_sign_split (skip_space s)) as [E2 L2].
  rewrite E2. cbn [fst snd].
  rewrite <- E1 in L1, L2 |- *.
  set (i0 := rc_blanks s) in *. set (k := snd (rc_sign (skipn i0 s))) in *.
  rewrite skipn_skipn. replace (k + i0)%nat with (i0 + k)%nat by lia.
  rewrite length_skipn. rewrite length_skipn in L1, L2.
  replace (length s - (length s - (i0 + k)))%nat with (i0 + k)%nat by lia. reflexivity.
Qed.

(** [strtol_read_channel]: on every byte string, read_channel's characters read are strtol's end offset, and
    when there is a digit, its verdict (big, < 0, >= 48) is strtol's (c < 0, c >= 48), with the same channel. *)
Theorem strtol_read_channel : forall s,
  let '(used, v, big) := read_channel s in
  Z.of_nat used = s10_end s /\
  (used <> 0%nat ->
     (big || (v <? 0) || (HA_CHANNELS <=? v)) = ((s10_val s <? 0) || (REAC_HEADAMP_MAX_CH <=? s10_val s)) /\
     ((big || (v <? 0) || (HA_CHANNELS <=? v)) = false -> v = s10_val s)).
Proof.
  intros s. rewrite read_channel_alt. cbv zeta.
  pose proof (rc_digits_nd (s10_rest s) 0 false) as ND. fold (s10_nd s) in ND.
  pose proof (rc_digits_false (s10_rest s) 0 ltac:(lia)) as [RF RT]. fold (s10_mag s) in RF, RT.
  revert ND RF RT. destruct (rc_digits 0 false (s10_rest s)) as [[acc big] nd]. cbn [fst snd]. intros ND RF RT.
  subst nd. unfold s10_end. destruct (s10_nd s =? 0)%nat eqn:E0; cbv beta iota.
  - split; [reflexivity|]. intros H. exfalso. apply H. reflexivity.
  - split; [reflexivity|]. intros _.
    rewrite s10_val_lt0. rewrite (s10_val_ge s REAC_HEADAMP_MAX_CH) by (unfold REAC_HEADAMP_MAX_CH, LMIN; lia).
    pose proof (s10_mag_nonneg s) as Hm. unfold s10_signed.
    destruct big.
    + specialize (RT eq_refl). cbn [orb]. split; [|intros H; discriminate H].
      unfold REAC_HEADAMP_MAX_CH. destruct (s10_neg s).
      * symmetry. apply orb_true_iff. left. apply Z.ltb_lt. lia.
      * symmetry. apply orb_true_iff. right. apply Z.leb_le. lia.
    + destruct (RF eq_refl) as [Ea Hb]. subst acc. cbn [orb].
      unfold HA_CHANNELS, REAC_HEADAMP_MAX_CH. split; [reflexivity|]. intros _.
      symmetry. rewrite s10_val_small; [unfold s10_signed; reflexivity|].
      unfold s10_signed, LMIN. destruct (s10_neg s); lia.
Qed.

(** So the two key readings are one verdict, on every byte string. *)
Lemma parse_key_expect_key : forall rest, parse_key rest = expect_key rest.
Proof.
  intros rest. unfold parse_key, expect_key. cbv zeta. pose proof (strtol_read_channel rest) as H. revert H.
  destruct (read_channel rest) as [[used v] big]. cbv beta iota. intros [HE HR].
  rewrite <- HE. rewrite Nat2Z.id.
  assert (EQ : (Z.of_nat used =? 0) = (used =? 0)%nat) by (destruct used; reflexivity). rewrite EQ.
  destruct (used =? 0)%nat eqn:E0; cbn [orb]; [reflexivity|].
  apply Nat.eqb_neq in E0. destruct (HR E0) as [HD HV].
  destruct (bv_unsigned (nth used rest NUL) =? 46); cbn [negb]; [|reflexivity].
  destruct (param_of_name (cstr (skipn (S used) rest))) as [p|]; [|reflexivity].
  rewrite <- HD. destruct (big || (v <? 0) || (HA_CHANNELS <=? v)) eqn:EB; [reflexivity|].
  rewrite (HV eq_refl). reflexivity.
Qed.

(** ** The values agree on a pod whose size passes SPA_POD_IS_VALID (fuzz_role's Pod/Role.v:75-80 has the same three
    lemmas, in a role-only file) *)
Lemma spa_get_string_key_of : forall e, e_size e < SPA_POD_MAX_SIZE -> spa_get_string e = key_of e.
Proof. intros e H. unfold spa_get_string, key_of. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.
Lemma spa_get_int_int_of : forall e, e_size e < SPA_POD_MAX_SIZE -> spa_get_int e = int_of e.
Proof. intros e H. unfold spa_get_int, int_of. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.
Lemma spa_get_float_float_of : forall e, e_size e < SPA_POD_MAX_SIZE -> spa_get_float e = float_of e.
Proof. intros e H. unfold spa_get_float, float_of. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma nearest_range : forall f lo hi n, nearest f lo hi = Some n -> lo <= n <= hi.
Proof.
  intros f lo hi n H. unfold nearest in H. destruct (near_f32 f) as [r|]; [|discriminate H].
  destruct ((lo <=? r) && (r <=? hi)) eqn:E; [|discriminate H]. injection H as <-.
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

(** value_pod_to_byte is cell_value with -1 read as None. *)
Lemma parse_value_cell_value : forall e, e_size e < SPA_POD_MAX_SIZE ->
  parse_value e = (if cell_value e <? 0 then None else Some (cell_value e)).
Proof.
  intros e H. unfold parse_value, cell_value.
  rewrite spa_get_bool_bool_of, spa_get_int_int_of, spa_get_float_float_of by exact H.
  destruct (bool_of e) as [[|]|]; cbv beta iota; [reflexivity | reflexivity|].
  destruct (int_of e) as [i|]; cbv beta iota.
  - destruct ((0 <=? i) && (i <=? 255)) eqn:E; cbv beta iota.
    + apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
      replace ((i <? 0) || (255 <? i)) with false
        by (symmetry; apply orb_false_iff; split; apply Z.ltb_ge; lia).
      replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    + replace ((i <? 0) || (255 <? i)) with true; [reflexivity|].
      symmetry. apply orb_true_iff. apply andb_false_iff in E as [E|E]; apply Z.leb_gt in E.
      * left. apply Z.ltb_lt. lia.
      * right. apply Z.ltb_lt. lia.
  - destruct (float_of e) as [f|]; cbv beta iota; [|reflexivity].
    destruct (nearest f 0 255) as [n|] eqn:EN; cbv beta iota; [|reflexivity].
    apply nearest_range in EN. destruct (Z.ltb_spec n 0); [exfalso; lia | reflexivity].
Qed.

Lemma param_of_name_range : forall n p, param_of_name n = Some p -> p = HA_PHANTOM \/ p = HA_PAD \/ p = HA_SENS.
Proof.
  intros n p H. unfold param_of_name in H.
  destruct (bytes_eqb n NAME_PHANTOM); cbv beta iota in H; [injection H as <-; auto|].
  destruct (bytes_eqb n NAME_PAD); cbv beta iota in H; [injection H as <-; auto|].
  destruct (bytes_eqb n NAME_SENS); cbv beta iota in H; [injection H as <-; auto | discriminate H].
Qed.

Lemma parse_key_cell : forall rest ch p, parse_key rest = KCell ch p ->
  0 <= ch < REAC_HEADAMP_MAX_CH /\ (p = HA_PHANTOM \/ p = HA_PAD \/ p = HA_SENS).
Proof.
  intros rest ch p H. unfold parse_key in H. cbv zeta in H.
  destruct ((s10_end rest =? 0) || negb (bv_unsigned (nth (Z.to_nat (s10_end rest)) rest NUL) =? 46));
    cbv beta iota in H; [discriminate H|].
  destruct (param_of_name (cstr (skipn (S (Z.to_nat (s10_end rest))) rest))) as [q|] eqn:EP;
    cbv beta iota in H; [|discriminate H].
  destruct ((s10_val rest <? 0) || (REAC_HEADAMP_MAX_CH <=? s10_val rest)) eqn:ER;
    cbv beta iota in H; [discriminate H|].
  injection H as <- <-. apply orb_false_iff in ER as [R1 R2]. apply Z.ltb_ge in R1. apply Z.leb_gt in R2.
  split; [lia|]. eapply param_of_name_range. exact EP.
Qed.

Lemma value_in_range_top : forall p v, p = HA_PHANTOM \/ p = HA_PAD \/ p = HA_SENS ->
  value_in_range p v = negb ((if p =? HA_SENS then HA_SENS_MAX else 1) <? v).
Proof.
  intros p v Hp. unfold value_in_range, HA_PHANTOM, HA_PAD, HA_SENS, HA_SENS_MAX, REAC_HEADAMP_SENS_MAX in *.
  destruct Hp as [-> | [-> | ->]]; cbn [Z.eqb orb Pos.eqb]; rewrite Z.leb_antisym; reflexivity.
Qed.

Lemma parse_cell_expect_cell : forall k v, e_size v < SPA_POD_MAX_SIZE -> parse_cell k v = expect_cell k v.
Proof.
  intros k v H. unfold parse_cell, expect_cell. cbv zeta. rewrite <- parse_key_expect_key.
  destruct (parse_key (skipn (length HA_PREFIX) k)) as [| |ch p] eqn:EK; try reflexivity.
  apply parse_key_cell in EK as [_ Hp]. rewrite (parse_value_cell_value v H).
  destruct (cell_value v <? 0); cbv beta iota; cbn [orb]; [reflexivity|].
  rewrite (value_in_range_top p (cell_value v) Hp).
  destruct ((if p =? HA_SENS then HA_SENS_MAX else 1) <? cell_value v); reflexivity.
Qed.

(** ** The parse's answer on an uncorrupted pod is the expectation *)
Lemma ha_fold_ext : forall f g cap ps cells keys rf,
  (forall k v, In (k, v) ps -> f k v = g k v) -> ha_fold f cap ps cells keys rf = ha_fold g cap ps cells keys rf.
Proof.
  intros f g cap ps. induction ps as [|[k v] ps IH]; intros cells keys rf H; [reflexivity|]. cbn [ha_fold].
  rewrite (H k v (or_introl eq_refl)).
  assert (H' : forall k' v', In (k', v') ps -> f k' v' = g k' v') by (intros; apply H; right; assumption).
  destruct (negb (ha_prefix k)); [apply IH; exact H'|].
  destruct (g k v) as [bad|c]; [apply IH; exact H'|]. destruct (cap <=? Z.of_nat (length cells)); [reflexivity|].
  apply IH. exact H'.
Qed.

Theorem parse_model_encode_any : forall r cap, pod_rec_wf r -> parse_model (pod_encode r) cap = expect_model false cap r.
Proof.
  intros r cap Hw. unfold parse_model. rewrite (spa_view_encode r Hw).
  unfold record_view, expect_model, params_struct, ents. cbn [orb].
  destruct (is_props r); cbn [negb]; [|reflexivity].
  destruct (first_params (p_props r)) as [[i|es]|] eqn:EF; cbn [negb]; try reflexivity.
  assert (Hes : Forall ent_wf es).
  { destruct Hw as (_ & _ & He & _). unfold first_params in EF.
    destruct (find (fun kv => fst kv =? POD_PROP_PARAMS) (p_props r)) as [kv|] eqn:F; [|discriminate EF].
    cbn [option_map] in EF. injection EF as EF. apply find_some in F as [Hin _].
    apply all_ents_Forall in He. rewrite Forall_forall in He. specialize (He kv Hin). rewrite EF in He. exact He. }
  assert (Hsz : forall e, In e es -> e_size e < SPA_POD_MAX_SIZE).
  { intros e Hin. rewrite Forall_forall in Hes. destruct (Hes e Hin) as (_ & _ & Hz). unfold SPA_POD_MAX_SIZE. lia. }
  rewrite (pairs_by_ext spa_get_string key_of es None) by (intros e Hin; apply spa_get_string_key_of; auto).
  unfold pairs. f_equal. apply ha_fold_ext. intros k e Hin. apply parse_cell_expect_cell. apply Hsz.
  eapply pairs_by_in. exact Hin.
Qed.

(** The contract's form (the harness's cap is fuzz_u8 % 10). *)
Theorem parse_model_encode : forall r cap, pod_rec_wf r -> 0 <= cap <= 9 ->
  parse_model (pod_encode r) cap = expect_model false cap r.
Proof. intros r cap Hw _. apply parse_model_encode_any. exact Hw. Qed.

(** reac_headamp_prop_parse_result(props, out, cap, &res) with props NULL (None) or the pod bytes bs (Some bs):
    NULL is -1 with res = (0, 0, NONE) and no cell written (reac_headamp_prop.c:115-121); the harness passes NULL
    when the null flag is set (fuzz_headamp.c:333). *)
Definition parse_props (props : option (list byte)) (cap : Z) : Z * list cell * (Z * Z * Z) :=
  match props with None => (-1, [], (0, 0, REFUSE_NONE)) | Some bs => parse_model bs cap end.

Lemma parse_null : forall cap, parse_props None cap = (-1, [], (0, 0, REFUSE_NONE)).
Proof. reflexivity. Qed.

(** With the NULL flag, expect_of is -1 with nothing seen, as the parse of NULL is. *)
Lemma expect_model_null : forall cap r, expect_model true cap r = (-1, [], (0, 0, REFUSE_NONE)).
Proof. reflexivity. Qed.

(** The harness's call (fuzz_headamp.c:333-340): on an uncorrupted record, for either value of the null flag, the
    parse's answer is expect_of's. *)
Corollary parse_props_build : forall inp r rest cap (null : bool), pod_build inp = (r, rest) -> corrupt r = false ->
  0 <= cap <= 9 -> parse_props (if null then None else Some (buf r)) cap = expect_model null cap r.
Proof.
  intros inp r rest cap null H Hc Hcap. destruct null; [reflexivity|].
  cbn [parse_props]. pose proof (pod_build_wf inp r rest H) as Hw. unfold buf, corrupt in *.
  destruct (p_corr r); [discriminate Hc|]. apply parse_model_encode; assumption.
Qed.

(** On every record pod_build makes and leaves uncorrupted. *)
Corollary parse_model_build : forall inp r rest cap, pod_build inp = (r, rest) -> corrupt r = false -> 0 <= cap <= 9 ->
  parse_model (buf r) cap = expect_model false cap r.
Proof.
  intros inp r rest cap H Hc Hcap. pose proof (pod_build_wf inp r rest H) as Hw. unfold buf, corrupt in *.
  destruct (p_corr r); [discriminate Hc|]. apply parse_model_encode; assumption.
Qed.

(** ** On every byte string (corrupted pods too): what check_count and check_cells_valid read *)
(** cells_valid's test (fuzz_headamp.c:161-169) on one cell. *)
Definition cell_valid (c : cell) : Prop :=
  let '(ch, p, v) := c in
  0 <= ch < HA_CHANNELS /\ 0 <= p <= HA_SENS /\ 0 <= v <= (if p =? HA_SENS then HA_SENS_MAX else 1).

Lemma parse_value_range : forall v b, parse_value v = Some b -> 0 <= b <= 255.
Proof.
  intros v b EV. unfold parse_value in EV. destruct (spa_get_bool v) as [bb|]; cbv beta iota in EV.
  - injection EV as <-. destruct bb; lia.
  - destruct (spa_get_int v) as [i|]; cbv beta iota in EV.
    + destruct ((i <? 0) || (255 <? i)) eqn:E; cbv beta iota in EV; [discriminate EV|]. injection EV as <-.
      apply orb_false_iff in E as [E1 E2]. apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. lia.
    + destruct (spa_get_float v) as [f|]; cbv beta iota in EV; [|discriminate EV]. apply nearest_range in EV. exact EV.
Qed.

Lemma parse_cell_valid : forall k v c, parse_cell k v = inr c -> cell_valid c.
Proof.
  intros k v c H. unfold parse_cell in H.
  destruct (parse_key (skipn (length HA_PREFIX) k)) as [| |ch p] eqn:EK; cbv beta iota in H; try discriminate H.
  apply parse_key_cell in EK as [Hc Hp].
  destruct (parse_value v) as [b|] eqn:EV; cbv beta iota in H; [|discriminate H].
  destruct (value_in_range p b) eqn:ER; cbv beta iota in H; [|discriminate H]. injection H as <-.
  apply parse_value_range in EV.
  rewrite (value_in_range_top p b Hp) in ER. apply negb_true_iff in ER. apply Z.ltb_ge in ER.
  unfold cell_valid. cbv beta iota.
  unfold REAC_HEADAMP_MAX_CH, HA_CHANNELS in *.
  split; [lia|]. split; [unfold HA_PHANTOM, HA_PAD, HA_SENS in Hp |- *; destruct Hp as [-> | [-> | ->]]; lia|].
  split; [lia | exact ER].
Qed.

Lemma ha_fold_inv : forall cellf cap ps cells keys rf,
  (forall k v c, cellf k v = inr c -> cell_valid c) ->
  Z.of_nat (length cells) <= cap -> Z.of_nat (length cells) <= keys -> Forall cell_valid cells ->
  Z.of_nat (length (fst (fst (ha_fold cellf cap ps cells keys rf)))) <= cap /\
  Z.of_nat (length (fst (fst (ha_fold cellf cap ps cells keys rf)))) <= snd (fst (ha_fold cellf cap ps cells keys rf)) /\
  Forall cell_valid (fst (fst (ha_fold cellf cap ps cells keys rf))).
Proof.
  intros cellf cap ps. induction ps as [|[k v] ps IH]; intros cells keys rf Hf Hc Hk Hv; cbn [ha_fold].
  - cbn [fst snd]. split; [exact Hc | split; [exact Hk | exact Hv]].
  - destruct (negb (ha_prefix k)); [apply IH; assumption|].
    destruct (cellf k v) as [bad|c] eqn:E; [apply IH; try assumption; lia|].
    destruct (Z.leb_spec cap (Z.of_nat (length cells))) as [Hl|Hl].
    + cbn [fst snd]. split; [lia | split; [lia | exact Hv]].
    + apply IH; try assumption; rewrite ?length_app; cbn [length]; try lia.
      apply Forall_app. split; [exact Hv | constructor; [exact (Hf k v c E) | constructor]].
Qed.

(** What check_no_overrun / check_count / check_cells_valid need of an answer (rc, cells, (n, keys, refusal)) on every
    input: rc is -1 with nothing seen and no cell, or a count in [0, cap] that is the number of cells written and
    res.n, with keys >= rc; every cell written is valid. So -1 <= rc <= cap, and at most cap cells are written. *)
Definition answer_ok (cap : Z) (o : Z * list cell * (Z * Z * Z)) : Prop :=
  let '(rc, cells, (n, keys, rf)) := o in
  ((rc = -1 /\ cells = [] /\ n = 0 /\ keys = 0 /\ rf = REFUSE_NONE) \/
   (0 <= rc <= cap /\ rc = Z.of_nat (length cells) /\ n = rc /\ rc <= keys)) /\
  Forall cell_valid cells.

Theorem parse_model_total : forall bs cap, 0 <= cap -> answer_ok cap (parse_model bs cap).
Proof.
  intros bs cap Hcap. unfold parse_model.
  destruct (spa_view_of bs) as [| | |cs]; unfold answer_ok; cbv beta iota.
  - split; [left; repeat split; reflexivity | constructor].
  - split; [right; cbn; lia | constructor].
  - split; [right; cbn; lia | constructor].
  - pose proof (ha_fold_inv parse_cell cap (pairs_by spa_get_string cs None) [] 0 REFUSE_NONE parse_cell_valid
                  ltac:(cbn; lia) ltac:(cbn; lia) (Forall_nil _)) as HI.
    revert HI. destruct (ha_fold parse_cell cap (pairs_by spa_get_string cs None) [] 0 REFUSE_NONE) as [[cells keys] rf].
    unfold ha_result. cbv beta iota. cbn [fst snd]. intros (H1 & H2 & H3).
    split; [right; split; [lia|]; split; [reflexivity|]; split; [reflexivity | exact H2] | exact H3].
Qed.

Corollary parse_props_total : forall props cap, 0 <= cap -> answer_ok cap (parse_props props cap).
Proof.
  intros [bs|] cap Hcap; [apply parse_model_total; exact Hcap|].
  unfold parse_props, answer_ok. cbv beta iota. split; [left; repeat split; reflexivity | constructor].
Qed.

(** ** keys is bounded by the pod's length (a finding of the model's independent review): check_count reads res->keys as a signed 32-bit int
    (plain 0x146c8-0x146cc), so the walk needs keys < 2^31; with the pod's length <= 16384 this gives it. Each key
    counted is one pair, each pair takes at least one child, and the children are at most [length bs] (the fuel). *)
Lemma ha_fold_keys : forall f cap ps cells keys rf,
  keys <= snd (fst (ha_fold f cap ps cells keys rf)) <= keys + Z.of_nat (length ps).
Proof.
  intros f cap ps. induction ps as [|[k v] ps IH]; intros cells keys rf; cbn [ha_fold length]; [cbn; lia|].
  destruct (negb (ha_prefix k)); [specialize (IH cells keys rf); lia|].
  destruct (f k v) as [bad|c]; [specialize (IH cells (keys + 1) (if rf =? REFUSE_NONE then bad else rf)); lia|].
  destruct (cap <=? Z.of_nat (length cells)); [cbn; lia|]. specialize (IH (cells ++ [c]) (keys + 1) rf). lia.
Qed.

Lemma pairs_by_len : forall f es k, (length (pairs_by f es k) <= length es)%nat.
Proof.
  intros f es. induction es as [|e es IH]; intros k; cbn [pairs_by length]; [lia|].
  destruct k as [k|]; cbn [length]; [pose proof (IH None) | pose proof (IH (f e))]; lia.
Qed.

Lemma struct_children_len : forall bs body size iter fuel,
  (length (struct_children bs body size iter fuel) <= fuel)%nat.
Proof.
  intros bs body size iter fuel. revert iter. induction fuel as [|n IH]; intros iter; cbn [struct_children length]; [lia|].
  destruct (pod_is_inside bs body size iter); cbn [length]; [apply le_n_S, IH | cbn; lia].
Qed.

Theorem parse_model_keys : forall bs cap,
  let '(_, _, (_, keys, _)) := parse_model bs cap in 0 <= keys <= Z.of_nat (length bs).
Proof.
  intros bs cap. unfold parse_model.
  destruct (spa_view_of bs) as [| | |cs] eqn:EV; cbv beta iota; try lia.
  unfold spa_view_of in EV.
  destruct (negb (is_object_type bs POD_OBJECT_PROPS)); [discriminate EV|].
  destruct (find_prop bs (u32_at bs 0) POD_PROP_PARAMS 16 (length bs)) as [r|]; [|discriminate EV].
  destruct (negb (is_struct_at bs (r + 8))); [discriminate EV|]. injection EV as <-.
  pose proof (ha_fold_keys parse_cell cap (pairs_by spa_get_string (map (child_at bs) (struct_children bs (r + 16)
    (u32_at bs (r + 8)) (r + 16) (length bs))) None) [] 0 REFUSE_NONE) as HK.
  pose proof (pairs_by_len spa_get_string (map (child_at bs) (struct_children bs (r + 16) (u32_at bs (r + 8)) (r + 16)
    (length bs))) None) as HP.
  rewrite length_map in HP. pose proof (struct_children_len bs (r + 16) (u32_at bs (r + 8)) (r + 16) (length bs)) as HS.
  revert HK. destruct (ha_fold _ _ _ _ _ _) as [[cells keys] rf]. unfold ha_result. cbn [fst snd]. lia.
Qed.

Corollary parse_props_keys : forall props cap,
  let '(_, _, (_, keys, _)) := parse_props props cap in
  0 <= keys <= match props with Some bs => Z.of_nat (length bs) | None => 0 end.
Proof. intros [bs|] cap; [apply parse_model_keys | cbn; lia]. Qed.
