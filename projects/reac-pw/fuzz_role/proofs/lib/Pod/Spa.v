(** The reading of a Props object pod that the three reac-pw readers share (reac_role_prop_parse,
    reac_rate_prop_parse, reac_headamp_prop_parse_result): spa_pod_is_object_type(pod, Props),
    spa_pod_object_find_prop(obj, NULL, SPA_PROP_params), spa_pod_is_struct and SPA_POD_STRUCT_FOREACH, as SPA 1.6
    spa/pod/iter.h:31-61, :237-265, spa/pod/body.h:420-428, spa/pod/pod.h:20-39 and spa/utils/defs.h:295, :326-355
    write them, over the bytes bs of the pod. Statement text and its link to [pod_encode]: no function of a binary is
    proved here.

    Offsets are relative to the pod's address P. The C tests compare uintptr_t values; on offsets they are the same
    tests when P + len + 8 <= 2^64 (an iterator moves only past a pod found inside, so every offset compared is at
    most len + 7; fuzz_role's parse contract gives P + len <= lo < sp), and an alignment test (p & 3) == 0 is the
    same test on the offset when P mod 4 = 0 (P is a malloc block, P mod 16 = 0). Each word read is the
    little-endian u32 at that offset of bs.

    The two loops run on a fuel; [find_prop_fuel] and [struct_children_fuel] show that any fuel greater than the
    number of bytes left gives the same answer. When the top size word is length bs - 8 ([buf_header]; the parse
    contract's premise), fuel [length bs] is greater than both counts (a params value found inside has at most
    length bs - 16 bytes), so the reading is the C loop's. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Tables Model Accessors.
Import ListNotations.
Open Scope Z_scope.

Definition SPA_POD_MAX_SIZE : Z := 2^20.

(** The u32 at offset o of bs (0 for bytes past the end). *)
Definition u32_at (bs : list byte) (o : Z) : Z := rd32 (skipn (Z.to_nat o) bs).

(** spa_ptrinside(p1, s1, p2, s2, &remaining) (defs.h:326-339) and its remaining. *)
Definition ptrinside (p1 s1 p2 s2 : Z) : bool := (p1 <=? p2) && (s2 <=? s1) && (p2 - p1 <=? s1 - s2).
Definition ptr_remaining (p1 s1 p2 s2 : Z) : Z := (p1 + s1) - (p2 + s2).
(** spa_ptr_inside_and_aligned (defs.h:341-352); spa_ptr_type_inside passes sizeof and alignof of the type. *)
Definition ptr_type_inside (p1 s1 p2 sz al : Z) : bool := (p2 mod al =? 0) && ptrinside p1 s1 p2 sz.
(** spa_pod_is_inside(pod, size, iter) (iter.h:31-37): sizeof(struct spa_pod) = 8, alignof 4. *)
Definition pod_is_inside (bs : list byte) (pod size iter : Z) : bool :=
  ptr_type_inside pod size iter 8 4 && (u32_at bs iter <=? ptr_remaining pod size iter 8).
(** spa_pod_prop_is_inside(body, size, iter) (iter.h:49-56): sizeof(struct spa_pod_prop) = 16, alignof 4; the
    value size is at iter + 8. *)
Definition prop_is_inside (bs : list byte) (body size iter : Z) : bool :=
  ptr_type_inside body size iter 16 4 && (u32_at bs (iter + 8) <=? ptr_remaining body size iter 16).
(** SPA_ROUND_UP_N(n, 8) (defs.h:295), for n >= 1. *)
Definition round_up8 (n : Z) : Z := Z.lor (n - 1) 7 + 1.

(** spa_pod_is_object_type(pod, type) (iter.h:237-240): SPA_POD_CHECK(pod, Object, 8) then the object type. *)
Definition is_object_type (bs : list byte) (ty : Z) : bool :=
  (u32_at bs 0 <? SPA_POD_MAX_SIZE) && (u32_at bs 4 =? POD_OBJECT) && (8 <=? u32_at bs 0) && (u32_at bs 8 =? ty).

(** spa_pod_object_find_prop's first loop from res (iter.h:255-258): the object body is at 8 and its size is the
    pod size; the next prop is res + SPA_ROUND_UP_N(16 + value.size, 8) (spa_pod_prop_next, iter.h:58-61). The second
    loop (iter.h:260-263) runs from first to start, and start = first when the start argument is NULL. *)
Fixpoint find_prop (bs : list byte) (size key res : Z) (fuel : nat) : option Z :=
  match fuel with
  | O => None
  | S f =>
      if prop_is_inside bs 8 size res then
        if u32_at bs res =? key then Some res
        else find_prop bs size key (res + round_up8 (16 + u32_at bs (res + 8))) f
      else None
  end.

(** spa_pod_is_struct (body.h:420-423) of the pod at v. *)
Definition is_struct_at (bs : list byte) (v : Z) : bool :=
  (u32_at bs v <? SPA_POD_MAX_SIZE) && (u32_at bs (v + 4) =? POD_STRUCT).

(** SPA_POD_STRUCT_FOREACH (iter.h:98-104, SPA_POD_STRUCT_BODY pod.h:153) over a Struct body at [body] of [size] bytes: the offsets of
    the children, in order; the next child is iter + SPA_ROUND_UP_N(8 + size, 8) (spa_pod_next, iter.h:39-42). *)
Fixpoint struct_children (bs : list byte) (body size iter : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S f =>
      if pod_is_inside bs body size iter
      then iter :: struct_children bs body size (iter + round_up8 (8 + u32_at bs iter)) f
      else []
  end.

(** The child at c as an [ent]: its type, size and the size bytes of its body. *)
Definition child_at (bs : list byte) (c : Z) : ent :=
  Ent (u32_at bs (c + 4)) (u32_at bs c) (firstn (Z.to_nat (u32_at bs c)) (skipn (Z.to_nat (c + 8)) bs)).

(** What a reader of a Props object sees. *)
Inductive spa_view :=
  | VNotProps                (* not an Object of type Props: the readers return -1 *)
  | VNoParams                (* no SPA_PROP_params property: 0 *)
  | VParamsNotStruct         (* its value is not a Struct: 0 *)
  | VPods (cs : list ent).   (* the pods of that Struct, in order *)

Definition spa_view_of (bs : list byte) : spa_view :=
  if negb (is_object_type bs POD_OBJECT_PROPS) then VNotProps
  else
    match find_prop bs (u32_at bs 0) POD_PROP_PARAMS 16 (length bs) with
    | None => VNoParams
    | Some r =>
        if negb (is_struct_at bs (r + 8)) then VParamsNotStruct
        else VPods (map (child_at bs) (struct_children bs (r + 16) (u32_at bs (r + 8)) (r + 16) (length bs)))
    end.

(** The same view, from the record. *)
Definition record_view (r : pod_rec) : spa_view :=
  if negb (is_props r) then VNotProps
  else
    match first_params (p_props r) with
    | None => VNoParams
    | Some (PInt _) => VParamsNotStruct
    | Some (PStruct es) => VPods es
    end.

(** ** body.h's accessors on a child (body.h:163-238): SPA_POD_CHECK is IS_VALID (size < 2^20), the type, and the
    minimum size; spa_pod_body_get_string also needs the last body byte NUL. *)
Definition spa_get_string (e : ent) : option (list byte) :=
  if (e_size e <? SPA_POD_MAX_SIZE) && (e_type e =? POD_STRING) && (1 <=? e_size e) && (last_body_byte e =? 0)
  then Some (cstr (e_body e)) else None.
Definition spa_get_int (e : ent) : option Z :=
  if (e_size e <? SPA_POD_MAX_SIZE) && (e_type e =? POD_INT) && (4 <=? e_size e)
  then Some (s32 (rd32 (e_body e))) else None.
Definition spa_get_float (e : ent) : option Z :=
  if (e_size e <? SPA_POD_MAX_SIZE) && (e_type e =? POD_FLOAT) && (4 <=? e_size e)
  then Some (rd32 (e_body e)) else None.

(** ** Facts on the words and the iteration *)
Lemma u32_at_app_r : forall l1 l2 o, Z.of_nat (length l1) <= o ->
  u32_at (l1 ++ l2) o = u32_at l2 (o - Z.of_nat (length l1)).
Proof.
  intros l1 l2 o H. unfold u32_at.
  replace (Z.to_nat o) with (length l1 + Z.to_nat (o - Z.of_nat (length l1)))%nat by lia.
  rewrite skipn_app_len. reflexivity.
Qed.

Lemma u32_at_le32 : forall v l, u32_at (le32 v ++ l) 0 = v mod 2^32.
Proof. intros v l. unfold u32_at. cbn [Z.to_nat skipn]. apply rd32_le32. Qed.

Lemma u32_at_le32_small : forall v l, 0 <= v < 2^32 -> u32_at (le32 v ++ l) 0 = v.
Proof. intros v l H. rewrite u32_at_le32. apply Z.mod_small. exact H. Qed.

Lemma lor7 : forall x, 0 <= x -> Z.lor x 7 = 8 * (x / 8) + 7.
Proof.
  intros x Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases i 3) as [Hl|Hg].
  - assert (E7 : Z.testbit 7 i = true).
    { destruct (Z.eq_dec i 0) as [->|]; [reflexivity|]. destruct (Z.eq_dec i 1) as [->|]; [reflexivity|].
      replace i with 2 by lia. reflexivity. }
    rewrite E7, orb_true_r. symmetry.
    rewrite <- (Z.mod_pow2_bits_low (8 * (x / 8) + 7) 3 i) by lia.
    replace ((8 * (x / 8) + 7) mod 2^3) with 7; [exact E7|].
    change (2^3) with 8. rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia. reflexivity.
  - assert (E7 : Z.testbit 7 i = false) by (apply Z.bits_above_log2; [lia | cbn; lia]).
    rewrite E7, orb_false_r.
    replace i with ((i - 3) + 3) by lia. rewrite <- !Z.div_pow2_bits by lia. change (2^3) with 8.
    f_equal. rewrite Z.add_comm, Z.mul_comm, Z.div_add by lia. reflexivity.
Qed.

(** SPA_ROUND_UP_N(n, 8) is n rounded up to a multiple of 8. *)
Lemma round_up8_eq : forall n, 1 <= n -> round_up8 n = n + pad8 n.
Proof.
  intros n Hn. unfold round_up8. rewrite lor7 by lia. rewrite pad8_eq.
  pose proof (Z.div_mod (n - 1) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (n - 1) 8 ltac:(lia)) as M.
  rewrite <- (Z.div_unique (n + 7) 8 ((n - 1) / 8 + 1) ((n - 1) mod 8)) by lia. lia.
Qed.

Lemma pad8_add8 : forall n, pad8 (8 + n) = pad8 n.
Proof. intros n. unfold pad8. replace (8 + n) with (n + 1 * 8) by lia. rewrite Z.mod_add by lia. reflexivity. Qed.

Lemma round_up8_div8 : forall n, 1 <= n -> (8 | n) -> round_up8 n = n.
Proof.
  intros n Hn [c Hc]. rewrite round_up8_eq by lia. unfold pad8. subst n. rewrite Z.mod_mul by lia.
  replace ((8 - 0) mod 8) with 0 by reflexivity. lia.
Qed.

(** Any fuel greater than the bytes left gives the C loop's answer. *)
Lemma find_prop_fuel : forall bs size key res n m, 0 <= res ->
  (Z.to_nat (8 + size - res) < n)%nat -> (Z.to_nat (8 + size - res) < m)%nat ->
  find_prop bs size key res n = find_prop bs size key res m.
Proof.
  intros bs size key res n. revert res. induction n as [|n IH]; intros res m Hr Hn Hm; [lia|].
  destruct m as [|m]; [lia|]. cbn [find_prop].
  destruct (prop_is_inside bs 8 size res) eqn:E; [|reflexivity].
  destruct (u32_at bs res =? key); [reflexivity|].
  unfold prop_is_inside, ptr_type_inside, ptrinside, ptr_remaining in E.
  rewrite !andb_true_iff, !Z.leb_le in E. destruct E as [[_ [[E1 E2] E3]] E4].
  assert (V : 0 <= u32_at bs (res + 8)) by (unfold u32_at; apply rd32_nonneg).
  assert (R : 16 + u32_at bs (res + 8) <= round_up8 (16 + u32_at bs (res + 8))).
  { rewrite round_up8_eq by lia. pose proof (pad8_bound (16 + u32_at bs (res + 8))). lia. }
  apply IH; lia.
Qed.

Lemma struct_children_fuel : forall bs body size iter n m, 0 <= iter ->
  (Z.to_nat (body + size - iter) < n)%nat -> (Z.to_nat (body + size - iter) < m)%nat ->
  struct_children bs body size iter n = struct_children bs body size iter m.
Proof.
  intros bs body size iter n. revert iter. induction n as [|n IH]; intros iter m Hr Hn Hm; [lia|].
  destruct m as [|m]; [lia|]. cbn [struct_children].
  destruct (pod_is_inside bs body size iter) eqn:E; [|reflexivity]. f_equal.
  unfold pod_is_inside, ptr_type_inside, ptrinside, ptr_remaining in E.
  rewrite !andb_true_iff, !Z.leb_le in E. destruct E as [[_ [[E1 E2] E3]] E4].
  assert (V : 0 <= u32_at bs iter) by (unfold u32_at; apply rd32_nonneg).
  assert (R : 8 + u32_at bs iter <= round_up8 (8 + u32_at bs iter)).
  { rewrite round_up8_eq by lia. pose proof (pad8_bound (8 + u32_at bs iter)). lia. }
  apply IH; lia.
Qed.

(** ** The reading of [pod_encode r] is the record's view *)
Local Ltac bdec := rewrite ?andb_true_iff, ?Z.leb_le, ?Z.ltb_lt, ?Z.eqb_eq; repeat split; lia.

Lemma firstn_app_exact : forall (A B : list byte) n, n = length A -> firstn n (A ++ B) = A.
Proof.
  intros A B n ->. rewrite <- (Nat.add_0_r (length A)) at 1. rewrite firstn_app_len. cbn [firstn]. apply app_nil_r.
Qed.

Lemma flat_enc_pod_len_ge : forall es, Forall ent_wf es ->
  8 * Z.of_nat (length es) <= Z.of_nat (length (flat_map enc_pod es)).
Proof.
  intros es H. induction H as [|e es He Hs IH]; cbn [flat_map length]; [lia|].
  rewrite zlen_app, (zlen_enc_pod e He). pose proof (pad8_bound (e_size e)). destruct He as (_ & _ & Hz). lia.
Qed.

(** The pods of a Struct, written end to end and filling its body exactly, are read back one by one. *)
Lemma struct_children_encode : forall es pre post sb vs fuel bs,
  bs = pre ++ flat_map enc_pod es ++ post ->
  Forall ent_wf es ->
  sb <= Z.of_nat (length pre) -> (8 | Z.of_nat (length pre)) ->
  sb + vs = Z.of_nat (length pre) + Z.of_nat (length (flat_map enc_pod es)) ->
  (length es < fuel)%nat ->
  map (child_at bs) (struct_children bs sb vs (Z.of_nat (length pre)) fuel) = es.
Proof.
  induction es as [|e es IH]; intros pre post sb vs fuel bs Hbs Hw Hsb Ha Hend Hf;
    (destruct fuel as [|f]; [cbn [length] in Hf; lia|]); cbn [struct_children].
  - cbn [flat_map length] in Hend.
    destruct (pod_is_inside bs sb vs (Z.of_nat (length pre))) eqn:E; [|reflexivity].
    exfalso. unfold pod_is_inside, ptr_type_inside, ptrinside, ptr_remaining in E.
    rewrite !andb_true_iff, !Z.leb_le in E. destruct E as [[_ [[E1 E2] E3]] E4]. lia.
  - pose proof (Forall_inv Hw) as He. pose proof (Forall_inv_tail Hw) as Hw'.
    destruct e as [ty sz body]. pose proof (zlen_enc_pod _ He) as Le. pose proof (enc_pod_len_bound _ He) as [_ Ld].
    unfold ent_wf in He. cbn [e_type e_size e_body] in He, Le. destruct He as (Ht & Hb & Hs).
    pose proof (pad8_bound sz) as Pb.
    cbn [flat_map] in Hbs, Hend. rewrite zlen_app in Hend.
    remember (Z.of_nat (length pre)) as o eqn:Ho.
    assert (Eb : bs = pre ++ le32 sz ++ le32 ty ++ body ++ zeros (Z.to_nat (pad8 sz)) ++ flat_map enc_pod es ++ post).
    { rewrite Hbs. unfold enc_pod. cbn [e_type e_size e_body]. rewrite <- !app_assoc. reflexivity. }
    assert (Hc : u32_at bs o = sz).
    { rewrite Eb, u32_at_app_r by lia. replace (o - Z.of_nat (length pre)) with 0 by lia.
      apply u32_at_le32_small. lia. }
    assert (Hty : u32_at bs (o + 4) = ty).
    { rewrite Eb, app_assoc, u32_at_app_r by (rewrite zlen_app, zlen_le32; lia). rewrite zlen_app, zlen_le32.
      replace (o + 4 - (Z.of_nat (length pre) + 4)) with 0 by lia. apply u32_at_le32_small. exact Ht. }
    assert (Hbd : firstn (Z.to_nat sz) (skipn (Z.to_nat (o + 8)) bs) = body).
    { rewrite Eb, app_assoc, app_assoc.
      replace (Z.to_nat (o + 8)) with (length ((pre ++ le32 sz) ++ le32 ty) + 0)%nat
        by (rewrite !length_app, !length_le32; lia).
      rewrite skipn_app_len. cbn [skipn]. apply firstn_app_exact. symmetry. exact Hb. }
    assert (Hin : pod_is_inside bs sb vs o = true).
    { unfold pod_is_inside, ptr_type_inside, ptrinside, ptr_remaining. rewrite Hc. destruct Ha as [k Hk]. bdec. }
    rewrite Hin. cbn [map]. f_equal.
    + unfold child_at. rewrite Hty, Hc, Hbd. reflexivity.
    + rewrite Hc, round_up8_eq by lia. rewrite pad8_add8.
      replace (o + (8 + sz + pad8 sz)) with (Z.of_nat (length (pre ++ enc_pod (Ent ty sz body))))
        by (rewrite zlen_app; lia).
      apply (IH (pre ++ enc_pod (Ent ty sz body)) post sb vs f bs).
      * rewrite Hbs. rewrite <- !app_assoc. reflexivity.
      * exact Hw'.
      * rewrite zlen_app. lia.
      * rewrite zlen_app. rewrite <- Ho. apply Z.divide_add_r; [exact Ha | exact Ld].
      * rewrite zlen_app. lia.
      * cbn [length] in Hf. lia.
Qed.

(** The size word of a property's value pod. *)
Definition val_size (v : pval) : Z :=
  match v with PInt _ => 4 | PStruct es => Z.of_nat (length (flat_map enc_pod es)) end.

Lemma enc_val_facts : forall v l, pval_wf v -> Forall ent_wf (ents_of v) ->
  u32_at (enc_val v ++ l) 0 = val_size v /\
  round_up8 (16 + val_size v) = 8 + Z.of_nat (length (enc_val v)) /\
  0 <= val_size v <= Z.of_nat (length (enc_val v)) - 8 /\
  (8 | Z.of_nat (length (enc_val v))).
Proof.
  intros [i|es] l Hv He.
  - cbn [val_size enc_val]. unfold enc_pod. cbn [e_size e_type e_body]. rewrite <- app_assoc.
    rewrite u32_at_le32_small by lia.
    assert (E : length (le32 4 ++ le32 POD_INT ++ le32 i ++ zeros (Z.to_nat (pad8 4))) = 16%nat) by reflexivity.
    rewrite E. split; [reflexivity|]. split; [reflexivity|]. split; [lia | exists 2; reflexivity].
  - cbn [val_size enc_val ents_of pval_wf] in *. destruct (ents_len_bound es He) as [H1 [c Hc]].
    rewrite <- app_assoc. rewrite u32_at_le32_small by lia.
    rewrite !zlen_app, !zlen_le32. rewrite round_up8_div8 by (lia || (exists (c + 2); lia)).
    split; [reflexivity|]. split; [lia|]. split; [lia|]. exists (c + 1). lia.
Qed.

(** find_prop over properties written end to end, up to the end of the pod, finds the first SPA_PROP_params. *)
Lemma find_prop_encode : forall s ps pre fuel bs S,
  s <> 7 ->
  bs = pre ++ flat_map (prop_bytes s) ps ->
  Z.of_nat (length bs) = 8 + S ->
  Forall (fun kv => 0 <= fst kv < 2^32 /\ pval_wf (snd kv)) ps ->
  Forall ent_wf (all_ents ps) ->
  16 <= Z.of_nat (length pre) -> (8 | Z.of_nat (length pre)) ->
  (length ps < fuel)%nat ->
  match find (fun kv => fst kv =? POD_PROP_PARAMS) ps with
  | None => find_prop bs S POD_PROP_PARAMS (Z.of_nat (length pre)) fuel = None
  | Some kv => exists pre2 rest, bs = pre2 ++ prop_bytes s kv ++ rest /\ (8 | Z.of_nat (length pre2)) /\
               16 <= Z.of_nat (length pre2) /\
               find_prop bs S POD_PROP_PARAMS (Z.of_nat (length pre)) fuel = Some (Z.of_nat (length pre2))
  end.
Proof.
  intros s ps. induction ps as [|kv ps IH]; intros pre fuel bs S Hs Hbs Hl Hk He Hp Ha Hf;
    (destruct fuel as [|f]; [cbn [length] in Hf; lia|]); cbn [find find_prop].
  - cbn [flat_map] in Hbs. rewrite app_nil_r in Hbs. subst bs.
    destruct (prop_is_inside pre 8 S (Z.of_nat (length pre))) eqn:E; [|reflexivity].
    exfalso. unfold prop_is_inside, ptr_type_inside, ptrinside, ptr_remaining in E.
    rewrite !andb_true_iff, !Z.leb_le in E. destruct E as [[_ [[E1 E2] E3]] E4]. lia.
  - pose proof (Forall_inv Hk) as [Hkr Hv]. pose proof (Forall_inv_tail Hk) as Hk'.
    apply all_ents_Forall in He. pose proof (Forall_inv He) as Hev. pose proof (Forall_inv_tail He) as He'.
    apply all_ents_Forall in He'.
    destruct kv as [key v]. cbn [fst snd] in *.
    pose proof (enc_val_facts v (flat_map (prop_bytes s) ps) Hv Hev) as (Vs & Vr & Vb & Vd).
    cbn [flat_map] in Hbs.
    assert (Ep : prop_bytes s (key, v) = le32 key ++ le32 0 ++ enc_val v).
    { unfold prop_bytes. replace (s =? 7) with false by (symmetry; apply Z.eqb_neq; exact Hs). reflexivity. }
    remember (Z.of_nat (length pre)) as o eqn:Ho.
    assert (Lb : Z.of_nat (length bs)
                 = o + 8 + Z.of_nat (length (enc_val v)) + Z.of_nat (length (flat_map (prop_bytes s) ps))).
    { rewrite Hbs, Ep, !zlen_app, !zlen_le32. lia. }
    assert (Hkey : u32_at bs o = key).
    { rewrite Hbs, Ep, u32_at_app_r by lia. replace (o - Z.of_nat (length pre)) with 0 by lia.
      rewrite <- app_assoc. apply u32_at_le32_small. exact Hkr. }
    assert (Hvs : u32_at bs (o + 8) = val_size v).
    { rewrite Hbs, Ep.
      replace (pre ++ (le32 key ++ le32 0 ++ enc_val v) ++ flat_map (prop_bytes s) ps)
        with ((pre ++ le32 key ++ le32 0) ++ enc_val v ++ flat_map (prop_bytes s) ps)
        by (rewrite <- !app_assoc; reflexivity).
      rewrite u32_at_app_r by (rewrite !zlen_app, !zlen_le32; lia). rewrite !zlen_app, !zlen_le32.
      replace (o + 8 - (Z.of_nat (length pre) + (4 + 4))) with 0 by lia. exact Vs. }
    assert (Hin : prop_is_inside bs 8 S o = true).
    { unfold prop_is_inside, ptr_type_inside, ptrinside, ptr_remaining. rewrite Hvs. destruct Ha as [c Hc].
      pose proof (Zle_0_nat (length (flat_map (prop_bytes s) ps))). bdec. }
    rewrite Hin, Hkey.
    destruct (key =? POD_PROP_PARAMS) eqn:EK.
    + exists pre, (flat_map (prop_bytes s) ps). split; [exact Hbs|]. split; [rewrite <- Ho; exact Ha|].
      split; [lia|].
      rewrite Ho. reflexivity.
    + rewrite Hvs, Vr.
      replace (o + (8 + Z.of_nat (length (enc_val v)))) with (Z.of_nat (length (pre ++ prop_bytes s (key, v))))
        by (rewrite zlen_app, Ep, !zlen_app, !zlen_le32; lia).
      apply IH; try assumption.
      * rewrite Hbs. rewrite <- !app_assoc. reflexivity.
      * rewrite zlen_app. lia.
      * rewrite zlen_app, Ep, !zlen_app, !zlen_le32. destruct Ha as [c Hc], Vd as [d Hd]. exists (c + d + 1). lia.
      * cbn [length] in Hf. lia.
Qed.

Theorem spa_view_encode : forall r, pod_rec_wf r -> spa_view_of (pod_encode r) = record_view r.
Proof.
  intros [s ps co] (Hs & Hk & He & Hl & HL & _). cbn [p_shape p_props] in *.
  assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hk]; intros kv [_ ?]; auto).
  pose proof (pod_encode_len s ps co Hv He Hl) as (L1 & L2 & L3).
  unfold spa_view_of, record_view, is_props. cbn [p_shape p_props].
  unfold pod_encode in *. cbn [p_shape p_props] in *.
  set (B := body_bytes s ps) in *.
  set (bs := le32 (Z.of_nat (length B) - 4) ++ B) in *.
  assert (LB : Z.of_nat (length bs) = 4 + Z.of_nat (length B)) by (subst bs; rewrite zlen_app; reflexivity).
  assert (U4 : forall o, 4 <= o -> u32_at bs o = u32_at B (o - 4)).
  { intros o Ho. subst bs. rewrite u32_at_app_r by (rewrite zlen_le32; lia). rewrite zlen_le32. reflexivity. }
  destruct (Z.eq_dec s 7) as [E7|H7]; [|destruct (Z.eq_dec s 6) as [E6|H6]].
  - (* a Struct object: its type word is 14, not 15 *)
    assert (T : u32_at bs 4 = 14).
    { rewrite U4 by lia. subst B. unfold body_bytes, hdr_bytes. rewrite E7. cbn [Z.eqb Pos.eqb].
      replace (4 - 4) with 0 by lia. apply u32_at_le32_small. unfold POD_STRUCT. lia. }
    unfold is_object_type. rewrite T. replace (14 =? POD_OBJECT) with false by reflexivity.
    rewrite andb_false_r. cbn [andb negb]. rewrite E7. reflexivity.
  - (* a PropInfo object: its object type is 0x40001 *)
    assert (T : u32_at bs 8 = POD_OBJECT_PROPINFO).
    { rewrite U4 by lia. subst B. unfold body_bytes, hdr_bytes. rewrite E6. cbn [Z.eqb Pos.eqb].
      replace (8 - 4) with (Z.of_nat (length (le32 POD_OBJECT)) + 0) by reflexivity. rewrite <- !app_assoc.
      rewrite u32_at_app_r by lia. replace (Z.of_nat (length (le32 POD_OBJECT)) + 0 - Z.of_nat (length (le32 POD_OBJECT)))
        with 0 by lia.
      apply u32_at_le32_small. unfold POD_OBJECT_PROPINFO. lia. }
    unfold is_object_type. rewrite T. replace (POD_OBJECT_PROPINFO =? POD_OBJECT_PROPS) with false by reflexivity.
    rewrite andb_false_r. cbn [negb]. rewrite E6. reflexivity.
  - (* a Props object *)
    replace (negb (s =? 6) && negb (s =? 7)) with true
      by (rewrite (proj2 (Z.eqb_neq s 6) H6), (proj2 (Z.eqb_neq s 7) H7); reflexivity).
    cbn [negb].
    set (F := flat_map (prop_bytes s) ps) in *.
    set (S0 := Z.of_nat (length B) - 4).
    set (pre := le32 S0 ++ le32 POD_OBJECT ++ le32 POD_OBJECT_PROPS ++ le32 POD_PARAM_PROPS).
    assert (EB : B = (le32 POD_OBJECT ++ le32 POD_OBJECT_PROPS ++ le32 POD_PARAM_PROPS) ++ F).
    { subst B F. unfold body_bytes, hdr_bytes.
      rewrite (proj2 (Z.eqb_neq s 6) H6), (proj2 (Z.eqb_neq s 7) H7). reflexivity. }
    assert (LF : Z.of_nat (length B) = 12 + Z.of_nat (length F)) by (rewrite EB, zlen_app; reflexivity).
    assert (Ebs : bs = pre ++ F) by (subst bs pre; fold S0; rewrite EB; rewrite <- !app_assoc; reflexivity).
    assert (Lpre : Z.of_nat (length pre) = 16) by reflexivity.
    assert (W0 : u32_at bs 0 = S0).
    { subst bs. fold S0. apply u32_at_le32_small. lia. }
    assert (W4 : u32_at bs 4 = POD_OBJECT).
    { rewrite Ebs. subst pre. rewrite <- (app_assoc (le32 S0)), u32_at_app_r by (rewrite zlen_le32; lia).
      rewrite zlen_le32. replace (4 - 4) with 0 by lia. rewrite <- !app_assoc. apply u32_at_le32_small.
      unfold POD_OBJECT. lia. }
    assert (W8 : u32_at bs 8 = POD_OBJECT_PROPS).
    { rewrite Ebs. subst pre. rewrite <- !app_assoc.
      replace (le32 S0 ++ le32 POD_OBJECT ++ le32 POD_OBJECT_PROPS ++ le32 POD_PARAM_PROPS ++ F)
        with ((le32 S0 ++ le32 POD_OBJECT) ++ le32 POD_OBJECT_PROPS ++ le32 POD_PARAM_PROPS ++ F)
        by (rewrite <- app_assoc; reflexivity).
      rewrite u32_at_app_r by (rewrite zlen_app, !zlen_le32; lia). rewrite zlen_app, !zlen_le32.
      replace (8 - (4 + 4)) with 0 by lia. apply u32_at_le32_small. unfold POD_OBJECT_PROPS. lia. }
    unfold is_object_type. rewrite W0, W4, W8.
    replace ((S0 <? SPA_POD_MAX_SIZE) && (POD_OBJECT =? POD_OBJECT) && (8 <=? S0)
             && (POD_OBJECT_PROPS =? POD_OBJECT_PROPS)) with true
      by (symmetry; unfold SPA_POD_MAX_SIZE; bdec).
    cbn [negb].
    assert (Hfuel : (length ps < length bs)%nat) by lia.
    pose proof (find_prop_encode s ps pre (length bs) bs S0 H7 Ebs ltac:(lia) Hk He ltac:(lia)
                  ltac:(rewrite Lpre; exists 2; reflexivity) Hfuel) as FP.
    rewrite Lpre in FP. unfold first_params.
    destruct (find (fun kv => fst kv =? POD_PROP_PARAMS) ps) as [[key v]|] eqn:EF; cbn [option_map snd].
    + destruct FP as (pre2 & rest & Eb2 & Hd2 & H16 & EF2). rewrite EF2.
      apply find_some in EF as [Hin _]. rewrite Forall_forall in Hk. destruct (Hk _ Hin) as [Hkr Hpv].
      apply all_ents_Forall in He. rewrite Forall_forall in He. pose proof (He _ Hin) as Hev. cbn [snd] in Hpv, Hev.
      assert (Ep : prop_bytes s (key, v) = le32 key ++ le32 0 ++ enc_val v).
      { unfold prop_bytes. replace (s =? 7) with false by (symmetry; apply Z.eqb_neq; exact H7). reflexivity. }
      remember (Z.of_nat (length pre2)) as r eqn:Hr.
      assert (Ev : bs = (pre2 ++ le32 key ++ le32 0) ++ enc_val v ++ rest)
        by (rewrite Eb2, Ep; rewrite <- !app_assoc; reflexivity).
      assert (Lp2 : Z.of_nat (length (pre2 ++ le32 key ++ le32 0)) = r + 8)
        by (rewrite !zlen_app, !zlen_le32; lia).
      destruct v as [i|es].
      * (* the first params value is an Int: is_struct fails *)
        assert (T : u32_at bs (r + 8 + 4) = POD_INT).
        { rewrite Ev. unfold enc_val, enc_pod. cbn [e_size e_type e_body].
          replace ((pre2 ++ le32 key ++ le32 0) ++ (le32 4 ++ le32 POD_INT ++ le32 i ++ zeros (Z.to_nat (pad8 4))) ++ rest)
            with (((pre2 ++ le32 key ++ le32 0) ++ le32 4) ++ le32 POD_INT ++ (le32 i ++ zeros (Z.to_nat (pad8 4))) ++ rest)
            by (rewrite <- !app_assoc; reflexivity).
          rewrite u32_at_app_r by (rewrite zlen_app, Lp2, zlen_le32; lia). rewrite zlen_app, Lp2, zlen_le32.
          replace (r + 8 + 4 - (r + 8 + 4)) with 0 by lia. apply u32_at_le32_small. unfold POD_INT. lia. }
        unfold is_struct_at. rewrite T. replace (POD_INT =? POD_STRUCT) with false by reflexivity.
        rewrite andb_false_r. reflexivity.
      * (* a Struct: its pods are read back *)
        cbn [pval_wf ents_of] in Hpv, Hev. destruct (ents_len_bound es Hev) as [Hfl [c Hc]].
        set (FE := flat_map enc_pod es) in *.
        assert (Eenc : enc_val (PStruct es) = le32 (Z.of_nat (length FE)) ++ le32 POD_STRUCT ++ FE) by reflexivity.
        assert (T0 : u32_at bs (r + 8) = Z.of_nat (length FE)).
        { rewrite Ev, u32_at_app_r by lia. rewrite Lp2. replace (r + 8 - (r + 8)) with 0 by lia. rewrite Eenc.
          rewrite <- app_assoc. apply u32_at_le32_small. lia. }
        assert (T1 : u32_at bs (r + 8 + 4) = POD_STRUCT).
        { rewrite Ev, Eenc.
          replace ((pre2 ++ le32 key ++ le32 0) ++ (le32 (Z.of_nat (length FE)) ++ le32 POD_STRUCT ++ FE) ++ rest)
            with (((pre2 ++ le32 key ++ le32 0) ++ le32 (Z.of_nat (length FE))) ++ le32 POD_STRUCT ++ FE ++ rest)
            by (rewrite <- !app_assoc; reflexivity).
          rewrite u32_at_app_r by (rewrite zlen_app, Lp2, zlen_le32; lia). rewrite zlen_app, Lp2, zlen_le32.
          replace (r + 8 + 4 - (r + 8 + 4)) with 0 by lia. apply u32_at_le32_small. unfold POD_STRUCT. lia. }
        unfold is_struct_at. rewrite T0, T1.
        replace ((Z.of_nat (length FE) <? SPA_POD_MAX_SIZE) && (POD_STRUCT =? POD_STRUCT)) with true
          by (symmetry; unfold SPA_POD_MAX_SIZE; bdec).
        cbn [negb]. f_equal.
        set (pre3 := ((pre2 ++ le32 key ++ le32 0) ++ le32 (Z.of_nat (length FE))) ++ le32 POD_STRUCT).
        assert (Lp3 : Z.of_nat (length pre3) = r + 16)
          by (subst pre3; pose proof Lp2 as L'; rewrite !zlen_app, !zlen_le32 in L' |- *; lia).
        assert (Ebs3 : bs = pre3 ++ FE ++ rest) by (subst pre3; rewrite Ev, Eenc; rewrite <- !app_assoc; reflexivity).
        rewrite <- Lp3.
        apply (struct_children_encode es pre3 rest (Z.of_nat (length pre3)) (Z.of_nat (length FE)) (length bs) bs).
        -- exact Ebs3.
        -- exact Hev.
        -- lia.
        -- rewrite Lp3. destruct Hd2 as [d Hd]. exists (d + 2). lia.
        -- reflexivity.
        -- pose proof (flat_enc_pod_len_ge es Hev) as G. fold FE in G.
           assert (Z.of_nat (length bs) >= Z.of_nat (length FE) + 16) by (rewrite Ebs3, !zlen_app; lia). lia.
    + rewrite FP. reflexivity.
Qed.

(** ** The bytes a reader gets: the header survives the corruption *)
Lemma firstn8_overwrite : forall l off bs, (8 <= off)%nat -> (off <= length l)%nat ->
  firstn 8 (overwrite l off bs) = firstn 8 l.
Proof.
  intros l off bs H1 H2. unfold overwrite. rewrite firstn_app, length_firstn.
  replace (8 - Nat.min off (length l))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
  rewrite firstn_firstn. f_equal. lia.
Qed.

Lemma u32_at_firstn8 : forall l l' o, firstn 8 l = firstn 8 l' -> 0 <= o <= 4 -> u32_at l o = u32_at l' o.
Proof.
  intros l l' o H Ho. unfold u32_at, rd32.
  assert (E : forall m : list byte, firstn 4 (skipn (Z.to_nat o) m) = firstn 4 (skipn (Z.to_nat o) (firstn 8 m))).
  { intros m. rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia. }
  rewrite (E l), (E l'), H. reflexivity.
Qed.

(** The first 8 bytes (the top size word and the type) are the object's own, corrupted or not
    (pod.h:443: off >= 8). *)
Lemma buf_header : forall r, pod_rec_wf r ->
  length (buf r) = length (pod_encode r) /\ firstn 8 (buf r) = firstn 8 (pod_encode r) /\
  u32_at (buf r) 0 = Z.of_nat (length (buf r)) - 8 /\ 8 <= Z.of_nat (length (buf r)) <= 5440.
Proof.
  intros r Hw. pose proof Hw as (Hs & Hk & He & Hl & HL & Hc).
  assert (Hv : Forall (fun kv => pval_wf (snd kv)) (p_props r))
    by (eapply Forall_impl; [|exact Hk]; intros kv [_ ?]; auto).
  pose proof (pod_encode_len (p_shape r) (p_props r) (p_corr r) Hv He Hl) as (L1 & L2 & _).
  replace (PodRec (p_shape r) (p_props r) (p_corr r)) with r in L1, L2 by (destruct r; reflexivity).
  assert (H0 : u32_at (pod_encode r) 0 = Z.of_nat (length (pod_encode r)) - 8).
  { unfold pod_encode. rewrite u32_at_le32_small; rewrite ?zlen_app, ?zlen_le32; [lia|].
    unfold pod_encode in L1, L2. rewrite zlen_app, zlen_le32 in L1, L2. lia. }
  assert (HB : length (buf r) = length (pod_encode r) /\ firstn 8 (buf r) = firstn 8 (pod_encode r)).
  { unfold buf. destruct (p_corr r) as [[off bs]|]; [|split; reflexivity].
    destruct Hc as (Ho & Hb & _). split.
    - apply length_overwrite. lia.
    - apply firstn8_overwrite; lia. }
  destruct HB as [HB1 HB2]. split; [exact HB1|]. split; [exact HB2|].
  rewrite (u32_at_firstn8 (buf r) (pod_encode r) 0 HB2) by lia. rewrite HB1. split; [exact H0 | lia].
Qed.
