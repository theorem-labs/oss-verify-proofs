(** fuzz/pod.h's writer as a total function of the input (pod.h:173-449), shared by fuzz_role, fuzz_rate and
    fuzz_headamp. [pod_build inp] is the record of the object pod_build writes and the input it leaves, where inp is
    the input at the call (after the harness's own leading bytes).

    What is modelled exactly as written: the order of every cursor read, ent_build's ten kinds (with ent_text's
    95-byte clamp, the head-amp key's part clamp, kind 1's `n + 2 <= 96` test and kind 3's -inf arm), the property
    loop, the corruption step. Two guards are left out, because they never fire: the stop rule of the pod loop
    (pod.h:428, `len + 8 + 96 + 8 > 16384`) and pod_put's refusal (pod.h:177). [pod_build_wf] gives len <= 5440 and
    every body <= 45 bytes, so neither guard can fire; the cut lemmas at the end give the bound at each test.

    The record keeps the object's shape (input byte mod 8), its properties in order, and the corruption (offset and
    the bytes written). The bytes ([pod_encode], [buf]) and the C fields ([is_props], [has_params], [params_struct],
    [ents], [corrupt]) are functions of it. A property of a shape-7 object (a Struct, no keys) is kept as (0, PInt 0). *)
From Stdlib Require Import String Ascii ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables.
Import ListNotations.
Open Scope Z_scope.

(** ** SPA numbers (pod.h:46-64) *)
Definition POD_NONE : Z := 1.
Definition POD_BOOL : Z := 2.
Definition POD_ID : Z := 3.
Definition POD_INT : Z := 4.
Definition POD_LONG : Z := 5.
Definition POD_FLOAT : Z := 6.
Definition POD_DOUBLE : Z := 7.
Definition POD_STRING : Z := 8.
Definition POD_STRUCT : Z := 14.
Definition POD_OBJECT : Z := 15.
Definition POD_OBJECT_PROPINFO : Z := 0x40001.
Definition POD_OBJECT_PROPS : Z := 0x40002.
Definition POD_PARAM_PROPS : Z := 2.
Definition POD_PROP_PARAMS : Z := 0x80001.
Definition POD_PROP_VOLUME : Z := 0x10003.

(** ** One pod of the params Struct (struct pod_ent, pod.h:71-75) *)
(** The body is the first e_size bytes of the 96-byte array; the rest of the array is 0 (ent_build starts with
    memset(e, 0, 104)). *)
Record ent := Ent { e_type : Z; e_size : Z; e_body : list byte }.

(** ent_text(e, s, n, nul) on the n bytes s (pod.h:209-219). *)
Definition ent_text (s : list byte) (nul : bool) : ent :=
  let s' := firstn 95 s in
  let b := if nul then s' ++ [NUL] else s' in
  Ent POD_STRING (Z.of_nat (length b)) b.

(** The decimal text of v, 0 <= v < 100, no leading zero (pod.h:237-245, for v = c % 64). *)
Definition digit (d : Z) : byte := Z_to_bv 8 (48 + d).
Definition dec64 (v : Z) : list byte := if v <? 10 then [digit v] else [digit (v / 10); digit (v mod 10)].

(** The head-amp key's four parts joined (pod.h:254-260): a part that would reach 96 bytes is cut to 95 - n. *)
Definition join_part (t s : list byte) : list byte :=
  t ++ firstn (if (96 <=? length t + length s)%nat then (95 - length t)%nat else length s) s.
Definition join_parts (ps : list (list byte)) : list byte := fold_left join_part ps [].

(** ent_headamp_key (pod.h:224-262): c then p. *)
Definition ent_headamp_key (inp : list byte) : ent * list byte :=
  let '(c, r1) := fuzz_u8 inp in
  let '(p, r2) := fuzz_u8 r1 in
  let ch := if c <? 200 then dec64 (c mod 64) else nth (Z.to_nat (c mod 14)) odd_ch [] in
  let sep := if Z.testbit p 7 then [] else DOT in
  (ent_text (join_parts [HPFX; ch; sep; nth (Z.to_nat (p mod 8)) param []]) true, r2).

(** ent_build (pod.h:265-379): kind, then the reads of its case. *)
Definition ent_build (inp : list byte) : ent * list byte :=
  let '(kind, r) := fuzz_u8 inp in
  match Z.to_nat (kind mod 10) with
  | 0%nat => ent_headamp_key r
  | 1%nat =>
      let '(i, r') := fuzz_u8 r in
      let e := ent_text (nth (Z.to_nat (i mod 9)) vocab []) true in
      ((if Z.testbit kind 7 && (e_size e + 2 <=? 96)
        then Ent POD_STRING (e_size e + 2) (e_body e ++ [Z_to_bv 8 120; NUL]) else e), r')
  | 2%nat =>
      let '(m, r1) := fuzz_u8 r in
      let '(v, r2) := if Z.odd m then fuzz_u32 r1 else (nth (Z.to_nat ((m / 2) mod 14)) ints 0, r1) in
      (Ent POD_INT 4 (le32 v), r2)
  | 3%nat =>
      let '(m, r1) := fuzz_u8 r in
      let '(b, r2) :=
        if Z.odd m then fuzz_u32 r1
        else if m / 2 =? 127 then (0x7fc00000, r1)
        else if m / 2 =? 126 then ((if Z.testbit m 1 then 0xff800000 else 0x7f800000), r1)
        else (nth (Z.to_nat ((m / 2) mod 21)) float_bits 0, r1) in
      (Ent POD_FLOAT 4 (le32 b), r2)
  | 4%nat =>
      let '(v, r1) := fuzz_u8 r in
      (Ent POD_BOOL 4 (le32 (v mod 3)), r1)
  | 5%nat =>
      let '(n, r1) := fuzz_u8 r in
      let '(p, r2) := fuzz_take (Z.to_nat (n mod 32)) r1 in
      (ent_text p (negb (Z.testbit kind 7)), r2)
  | 6%nat =>
      let '(t, r1) := fuzz_u8 r in
      let ty := nth (Z.to_nat (t mod 4)) t6 0 in
      let sz := if ty =? POD_NONE then 0 else if ty =? POD_ID then 4 else 8 in
      let '(p, r2) := fuzz_take (Z.to_nat sz) r1 in
      (Ent ty sz (p ++ zeros (Z.to_nat sz - length p)), r2)
  | 7%nat =>
      let '(t, r1) := fuzz_u8 r in
      let '(s, r2) := fuzz_u8 r1 in
      let sz := s mod 12 in
      let '(p, r3) := fuzz_take (Z.to_nat sz) r2 in
      (Ent (t mod 21) sz (p ++ zeros (Z.to_nat sz - length p)), r3)
  | 8%nat =>
      let '(t, r1) := fuzz_u8 r in
      let ty := nth (Z.to_nat (t mod 4)) t8 0 in
      if ty =? POD_STRING then (Ent POD_STRING 0 [], r1)
      else let '(s, r2) := fuzz_u8 r1 in (Ent ty (s mod 4) (zeros (Z.to_nat (s mod 4))), r2)
  | _ => (Ent POD_STRUCT 24 (le32 14 ++ le32 POD_STRING ++ S9 ++ [NUL] ++ zeros 2), r)
  end.

(** ** The record *)
Inductive pval := PInt (v : Z) | PStruct (es : list ent).
Record pod_rec := PodRec { p_shape : Z; p_props : list (Z * pval); p_corr : option (Z * list byte) }.

(** The pods of a Struct (pod.h:425-433, the stop rule left out). *)
Fixpoint ents_loop (k : nat) (inp : list byte) : list ent * list byte :=
  match k with
  | O => ([], inp)
  | S k' => let '(e, r) := ent_build inp in let '(es, r') := ents_loop k' r in (e :: es, r')
  end.

(** One property (pod.h:399-438): sel, then (a params Struct) count and its pods. *)
Definition prop_step (shape : Z) (inp : list byte) : (Z * pval) * list byte :=
  let '(sel, r1) := fuzz_u8 inp in
  if shape =? 7 then ((0, PInt 0), r1)
  else if sel mod 4 =? 0 then ((POD_PROP_VOLUME, PInt 7), r1)
  else if Z.testbit sel 4 then ((POD_PROP_PARAMS, PInt 7), r1)
  else
    let '(c, r2) := fuzz_u8 r1 in
    let '(es, r3) := ents_loop (Z.to_nat (c mod 33)) r2 in
    ((POD_PROP_PARAMS, PStruct es), r3).

Fixpoint props_loop (shape : Z) (n : nat) (inp : list byte) : list (Z * pval) * list byte :=
  match n with
  | O => ([], inp)
  | S n' => let '(kv, r) := prop_step shape inp in let '(ps, r') := props_loop shape n' r in (kv :: ps, r')
  end.

(** ** The bytes *)
Definition pad8 (n : Z) : Z := (8 - n mod 8) mod 8.
(** pod_write_ent (pod.h:200-206) at an 8-aligned len: size, type, body, pad. *)
Definition enc_pod (e : ent) : list byte :=
  le32 (e_size e) ++ le32 (e_type e) ++ e_body e ++ zeros (Z.to_nat (pad8 (e_size e))).
Definition enc_val (v : pval) : list byte :=
  match v with
  | PInt i => enc_pod (Ent POD_INT 4 (le32 i))
  | PStruct es => let b := flat_map enc_pod es in le32 (Z.of_nat (length b)) ++ le32 POD_STRUCT ++ b
  end.
(** The object header after its size word (pod.h:389-394). *)
Definition hdr_bytes (shape : Z) : list byte :=
  if shape =? 7 then le32 POD_STRUCT
  else le32 POD_OBJECT ++ le32 (if shape =? 6 then POD_OBJECT_PROPINFO else POD_OBJECT_PROPS) ++ le32 POD_PARAM_PROPS.
Definition prop_bytes (shape : Z) (kv : Z * pval) : list byte :=
  if shape =? 7 then enc_val (snd kv) else le32 (fst kv) ++ le32 0 ++ enc_val (snd kv).
Definition body_bytes (shape : Z) (ps : list (Z * pval)) : list byte :=
  hdr_bytes shape ++ flat_map (prop_bytes shape) ps.
(** The object as written, before corruption: the top size word is len - 8 (pod.h:440). *)
Definition pod_encode (r : pod_rec) : list byte :=
  let b := body_bytes (p_shape r) (p_props r) in le32 (Z.of_nat (length b) - 4) ++ b.

(** The corruption step (pod.h:441-448), given len. *)
Definition corr_step (len : Z) (inp : list byte) : option (Z * list byte) * list byte :=
  let '(c, r1) := fuzz_u8 inp in
  if (c mod 16 =? 15) && (8 <? len) then
    let '(o, r2) := fuzz_u16 r1 in
    let '(n, r3) := fuzz_u8 r2 in
    let off := 8 + o mod (len - 8) in
    let '(bs, r4) := fuzz_u8s (Z.to_nat (Z.min (n mod 8) (len - off))) r3 in
    (Some (off, bs), r4)
  else (None, r1).

(** pod_build (pod.h:382-449). *)
Definition pod_build (inp : list byte) : pod_rec * list byte :=
  let '(s, r1) := fuzz_u8 inp in
  let '(np, r2) := fuzz_u8 r1 in
  let '(ps, r3) := props_loop (s mod 8) (Z.to_nat (np mod 4)) r2 in
  let '(co, r4) := corr_step (Z.of_nat (length (pod_encode (PodRec (s mod 8) ps None)))) r3 in
  (PodRec (s mod 8) ps co, r4).

(** ** The fields struct pod_props holds (pod.h:77-86) *)
Definition first_params (ps : list (Z * pval)) : option pval :=
  option_map snd (find (fun kv => fst kv =? POD_PROP_PARAMS) ps).
Definition is_props (r : pod_rec) : bool := negb (p_shape r =? 6) && negb (p_shape r =? 7).
Definition has_params (r : pod_rec) : bool :=
  match first_params (p_props r) with Some _ => true | None => false end.
Definition params_struct (r : pod_rec) : bool :=
  match first_params (p_props r) with Some (PStruct _) => true | _ => false end.
Definition ents (r : pod_rec) : list ent :=
  match first_params (p_props r) with Some (PStruct es) => es | _ => [] end.
Definition corrupt (r : pod_rec) : bool := match p_corr r with Some _ => true | None => false end.
(** bs written over l from offset off. *)
Definition overwrite (l : list byte) (off : nat) (bs : list byte) : list byte :=
  firstn off l ++ bs ++ skipn (off + length bs) l.
(** buf[0..len): the object, then the corruption. *)
Definition buf (r : pod_rec) : list byte :=
  match p_corr r with None => pod_encode r | Some (off, bs) => overwrite (pod_encode r) (Z.to_nat off) bs end.

(** ** Well-formed records *)
Definition ent_wf (e : ent) : Prop :=
  0 <= e_type e < 2^32 /\ length (e_body e) = Z.to_nat (e_size e) /\ 0 <= e_size e <= 45.
Definition all_ents (ps : list (Z * pval)) : list ent :=
  flat_map (fun kv => match snd kv with PStruct es => es | PInt _ => [] end) ps.
Definition pval_wf (v : pval) : Prop := match v with PStruct es => (length es <= 32)%nat | PInt _ => True end.
Definition corr_wf (len : Z) (co : option (Z * list byte)) : Prop :=
  match co with
  | None => True
  | Some (off, bs) => 8 <= off /\ off + Z.of_nat (length bs) <= len /\ (length bs <= 7)%nat
  end.
Definition pod_rec_wf (r : pod_rec) : Prop :=
  0 <= p_shape r < 8 /\
  Forall (fun kv => 0 <= fst kv < 2^32 /\ pval_wf (snd kv)) (p_props r) /\
  Forall ent_wf (all_ents (p_props r)) /\
  (length (p_props r) <= 3)%nat /\
  Z.of_nat (length (pod_encode r)) <= 5440 /\
  corr_wf (Z.of_nat (length (pod_encode r))) (p_corr r).

(** ** Lengths *)
Lemma pad8_bound : forall n, 0 <= pad8 n < 8.
Proof. intros n. unfold pad8. apply Z.mod_pos_bound. lia. Qed.

(** size + pad8 size is size rounded up to a multiple of 8. *)
Lemma pad8_eq : forall n, n + pad8 n = 8 * ((n + 7) / 8).
Proof.
  intros n. unfold pad8. pose proof (Z.div_mod n 8 ltac:(lia)) as Hn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hr.
  set (q := n / 8) in *. set (r := n mod 8) in *.
  destruct (Z.eq_dec r 0) as [E|E].
  - rewrite E. replace (8 - 0) with 8 by lia. rewrite Z.mod_same by lia.
    rewrite <- (Z.div_unique (n + 7) 8 q 7) by lia. lia.
  - rewrite (Z.mod_small (8 - r) 8) by lia.
    rewrite <- (Z.div_unique (n + 7) 8 (q + 1) (r - 1)) by lia. lia.
Qed.

Lemma zlen_app : forall (a b : list byte), Z.of_nat (length (a ++ b)) = Z.of_nat (length a) + Z.of_nat (length b).
Proof. intros a b. rewrite length_app. lia. Qed.
Lemma zlen_le32 : forall v, Z.of_nat (length (le32 v)) = 4.
Proof. reflexivity. Qed.
Lemma zlen_zeros : forall n, Z.of_nat (length (zeros n)) = Z.of_nat n.
Proof. intros n. rewrite length_zeros. reflexivity. Qed.

Lemma zlen_enc_pod : forall e, ent_wf e -> Z.of_nat (length (enc_pod e)) = 8 + e_size e + pad8 (e_size e).
Proof.
  intros e (_ & Hb & Hs). unfold enc_pod. rewrite !zlen_app, !zlen_le32, zlen_zeros, Hb.
  pose proof (pad8_bound (e_size e)). rewrite !Z2Nat.id by lia. lia.
Qed.

Lemma enc_pod_len_bound : forall e, ent_wf e ->
  Z.of_nat (length (enc_pod e)) <= 56 /\ (8 | Z.of_nat (length (enc_pod e))).
Proof.
  intros e He. rewrite (zlen_enc_pod e He). pose proof (pad8_eq (e_size e)) as E. destruct He as (_ & _ & Hs).
  split.
  - assert ((e_size e + 7) / 8 < 7) by (apply Z.div_lt_upper_bound; lia). lia.
  - exists (1 + (e_size e + 7) / 8). lia.
Qed.

Lemma flat_map_len_le : forall {A} (f : A -> list byte) (l : list A) (k : Z),
  Forall (fun x => Z.of_nat (length (f x)) <= k) l -> Z.of_nat (length (flat_map f l)) <= k * Z.of_nat (length l).
Proof.
  intros A f l k H. induction H as [|x l Hx Hl IH]; cbn [flat_map length]; [lia|].
  rewrite zlen_app. lia.
Qed.

Lemma flat_map_len_div8 : forall {A} (f : A -> list byte) (l : list A),
  Forall (fun x => (8 | Z.of_nat (length (f x)))) l -> (8 | Z.of_nat (length (flat_map f l))).
Proof.
  intros A f l H. induction H as [|x l Hx Hl IH]; cbn [flat_map length]; [exists 0; reflexivity|].
  rewrite zlen_app. apply Z.divide_add_r; assumption.
Qed.

Lemma ents_len_bound : forall es, Forall ent_wf es ->
  Z.of_nat (length (flat_map enc_pod es)) <= 56 * Z.of_nat (length es) /\ (8 | Z.of_nat (length (flat_map enc_pod es))).
Proof.
  intros es H. split.
  - apply flat_map_len_le. eapply Forall_impl; [|exact H]. intros e He. apply (enc_pod_len_bound e He).
  - apply flat_map_len_div8. eapply Forall_impl; [|exact H]. intros e He. apply (enc_pod_len_bound e He).
Qed.

Definition ents_of (v : pval) : list ent := match v with PStruct es => es | PInt _ => [] end.

Lemma all_ents_Forall : forall ps, Forall ent_wf (all_ents ps) <-> Forall (fun kv => Forall ent_wf (ents_of (snd kv))) ps.
Proof.
  induction ps as [|kv ps IH]; cbn [all_ents flat_map]; [split; constructor|].
  change (flat_map (fun kv => match snd kv with PStruct es => es | PInt _ => [] end) ps) with (all_ents ps).
  rewrite Forall_app, IH. split.
  - intros [H1 H2]. constructor; [exact H1 | exact H2].
  - intros H. inversion H; subst. split; assumption.
Qed.

Lemma enc_val_len : forall v, pval_wf v -> Forall ent_wf (ents_of v) ->
  Z.of_nat (length (enc_val v)) <= 1800 /\ (8 | Z.of_nat (length (enc_val v))).
Proof.
  intros [i|es] Hv He; cbn [enc_val].
  - assert (E : length (enc_pod (Ent POD_INT 4 (le32 i))) = 16%nat) by reflexivity.
    rewrite E. split; [lia | exists 2; reflexivity].
  - cbn [pval_wf ents_of] in Hv, He. destruct (ents_len_bound es He) as [H1 H2]. rewrite !zlen_app, !zlen_le32.
    split; [lia|]. destruct H2 as [c Hc]. exists (c + 1). lia.
Qed.

Lemma prop_bytes_len : forall s kv, pval_wf (snd kv) -> Forall ent_wf (ents_of (snd kv)) ->
  Z.of_nat (length (prop_bytes s kv)) <= 1808 /\ (8 | Z.of_nat (length (prop_bytes s kv))).
Proof.
  intros s kv Hv He. destruct (enc_val_len _ Hv He) as [H1 H2]. unfold prop_bytes. destruct (s =? 7).
  - split; [lia | exact H2].
  - rewrite !zlen_app, !zlen_le32. split; [lia|]. destruct H2 as [c Hc]. exists (c + 1). lia.
Qed.

(** len <= 5440 follows from the shape of the record. *)
Lemma pod_encode_len : forall s ps co,
  Forall (fun kv => pval_wf (snd kv)) ps -> Forall ent_wf (all_ents ps) -> (length ps <= 3)%nat ->
  Z.of_nat (length (pod_encode (PodRec s ps co))) <= 5440 /\ 8 <= Z.of_nat (length (pod_encode (PodRec s ps co))) /\
  (8 | Z.of_nat (length (pod_encode (PodRec s ps co)))).
Proof.
  intros s ps co Hv He Hl. apply all_ents_Forall in He.
  assert (HF : Forall (fun kv => Z.of_nat (length (prop_bytes s kv)) <= 1808) ps).
  { rewrite Forall_forall in Hv, He |- *. intros kv Hin. apply prop_bytes_len; auto. }
  assert (HD : Forall (fun kv => (8 | Z.of_nat (length (prop_bytes s kv)))) ps).
  { rewrite Forall_forall in Hv, He |- *. intros kv Hin. apply prop_bytes_len; auto. }
  pose proof (flat_map_len_le _ _ _ HF) as H1. pose proof (flat_map_len_div8 _ _ HD) as H2.
  unfold pod_encode, body_bytes, hdr_bytes. cbn [p_shape p_props].
  destruct H2 as [c Hc].
  destruct (s =? 7); rewrite !zlen_app, !zlen_le32; (split; [lia | split; [lia|]]).
  - exists (c + 1). lia.
  - exists (c + 2). lia.
Qed.

(** ** Every pod ent_build makes is well formed, with a body of at most 45 bytes *)
Lemma nth_Forall : forall {A} (P : A -> Prop) (l : list A) d n, Forall P l -> P d -> P (nth n l d).
Proof. intros A P l d n H Hd. revert n. induction H; intros [|n]; cbn; auto. Qed.

Lemma Forall_of_forallb : forall {A} (f : A -> bool) l, forallb f l = true -> Forall (fun x => f x = true) l.
Proof. intros A f l H. apply Forall_forall. intros x Hx. rewrite forallb_forall in H. auto. Qed.

Lemma nth_len_le : forall (l : list (list byte)) n k, forallb (fun s => (length s <=? k)%nat) l = true ->
  (length (nth n l []) <= k)%nat.
Proof.
  intros l n k H. apply Nat.leb_le. apply (nth_Forall (fun s => (length s <=? k)%nat = true)).
  - apply Forall_of_forallb. exact H.
  - reflexivity.
Qed.

Lemma ent_text_wf : forall (s : list byte) (nul : bool),
  (length s + (if nul then 1 else 0) <= 45)%nat -> ent_wf (ent_text s nul).
Proof.
  intros s nul H. unfold ent_text, ent_wf. cbn [e_type e_size e_body].
  split; [unfold POD_STRING; lia|]. rewrite Nat2Z.id. split; [reflexivity|].
  destruct nul; rewrite ?length_app, length_firstn; cbn [length]; lia.
Qed.

Lemma join_part_len : forall t s, (length (join_part t s) <= length t + length s)%nat.
Proof.
  intros t s. unfold join_part. rewrite length_app, length_firstn.
  destruct (96 <=? length t + length s)%nat; lia.
Qed.

Lemma join_parts4_len : forall a b c d,
  (length (join_parts [a; b; c; d]) <= length a + length b + length c + length d)%nat.
Proof.
  intros a b c d. unfold join_parts. cbn [fold_left].
  pose proof (join_part_len [] a). pose proof (join_part_len (join_part [] a) b).
  pose proof (join_part_len (join_part (join_part [] a) b) c).
  pose proof (join_part_len (join_part (join_part (join_part [] a) b) c) d). cbn [length] in *. lia.
Qed.

Lemma dec64_len : forall v, (length (dec64 v) <= 2)%nat.
Proof. intros v. unfold dec64. destruct (v <? 10); cbn; lia. Qed.

Lemma headamp_key_wf : forall inp, ent_wf (fst (ent_headamp_key inp)).
Proof.
  intros inp. unfold ent_headamp_key. destruct (fuzz_u8 inp) as [c r1]. destruct (fuzz_u8 r1) as [p r2]. cbn [fst].
  set (ch := if c <? 200 then dec64 (c mod 64) else nth (Z.to_nat (c mod 14)) odd_ch []).
  set (sep := if Z.testbit p 7 then [] else DOT).
  set (pa := nth (Z.to_nat (p mod 8)) param []).
  apply ent_text_wf. cbv beta iota. pose proof (join_parts4_len HPFX ch sep pa).
  assert (Hh : length HPFX = 13%nat) by reflexivity.
  assert (Hc : (length ch <= 21)%nat).
  { subst ch. destruct (c <? 200); [pose proof (dec64_len (c mod 64)); lia|]. apply nth_len_le. vm_compute. reflexivity. }
  assert (Hs : (length sep <= 1)%nat) by (subst sep; destruct (Z.testbit p 7); cbn; lia).
  assert (Hp : (length pa <= 9)%nat) by (subst pa; apply nth_len_le; vm_compute; reflexivity).
  lia.
Qed.

Lemma t6_range : forall n, 0 <= nth n t6 0 < 2^32.
Proof. intros n. apply (nth_Forall (fun v => 0 <= v < 2^32)); [repeat constructor; lia | lia]. Qed.
Lemma t8_range : forall n, 0 <= nth n t8 0 < 2^32.
Proof. intros n. apply (nth_Forall (fun v => 0 <= v < 2^32)); [repeat constructor; lia | lia]. Qed.

Lemma take_pad_len : forall (sz : Z) (r : list byte), 0 <= sz ->
  length (fst (fuzz_take (Z.to_nat sz) r) ++ zeros (Z.to_nat sz - length (fst (fuzz_take (Z.to_nat sz) r))))
  = Z.to_nat sz.
Proof.
  intros sz r Hs. cbn [fuzz_take fst]. rewrite length_app, length_zeros, length_firstn. lia.
Qed.

Lemma ent_build_wf : forall inp, ent_wf (fst (ent_build inp)).
Proof.
  intros inp. unfold ent_build. destruct (fuzz_u8 inp) as [kind r] eqn:Ek.
  destruct (Z.to_nat (kind mod 10)) as [|[|[|[|[|[|[|[|[|k]]]]]]]]].
  - apply headamp_key_wf.
  - destruct (fuzz_u8 r) as [i r'].
    assert (Hv : (length (nth (Z.to_nat (i mod 9)) vocab []) <= 18)%nat) by (apply nth_len_le; vm_compute; reflexivity).
    pose proof (ent_text_wf (nth (Z.to_nat (i mod 9)) vocab []) true ltac:(cbv beta iota; lia)) as He.
    set (e := ent_text (nth (Z.to_nat (i mod 9)) vocab []) true) in *.
    cbn [fst]. destruct (Z.testbit kind 7 && (e_size e + 2 <=? 96)) eqn:Eb; [|exact He].
    destruct He as (Ht & Hb & Hs). unfold ent_wf. cbn [e_type e_size e_body]. unfold POD_STRING.
    assert (Hn : (length (nth (Z.to_nat (i mod 9)) vocab []) + 1 <= 19)%nat) by lia.
    assert (Hz : e_size e <= 19).
    { subst e. unfold ent_text. cbn [e_size]. rewrite length_app, length_firstn. cbn [length]. lia. }
    rewrite length_app, Hb. cbn [length]. split; [lia|]. split; [lia|lia].
  - destruct (fuzz_u8 r) as [m r1]. destruct (Z.odd m); [destruct (fuzz_u32 r1) as [v r2]|];
      cbn [fst]; unfold ent_wf, POD_INT; cbn; lia.
  - destruct (fuzz_u8 r) as [m r1].
    destruct (Z.odd m); [destruct (fuzz_u32 r1) as [v r2]|];
      [|destruct (m / 2 =? 127); [|destruct (m / 2 =? 126)]];
      cbn [fst]; unfold ent_wf, POD_FLOAT; cbn; lia.
  - destruct (fuzz_u8 r) as [v r1]. cbn [fst]. unfold ent_wf, POD_BOOL; cbn; lia.
  - destruct (fuzz_u8 r) as [n r1]. cbn [fuzz_take fst]. apply ent_text_wf. rewrite length_firstn.
    assert (0 <= n mod 32 < 32) by (apply Z.mod_pos_bound; lia). destruct (negb (Z.testbit kind 7)); cbv beta iota; lia.
  - destruct (fuzz_u8 r) as [t r1].
    pose proof (t6_range (Z.to_nat (t mod 4))) as Ht.
    set (ty := nth (Z.to_nat (t mod 4)) t6 0) in *.
    set (sz := if ty =? POD_NONE then 0 else if ty =? POD_ID then 4 else 8).
    assert (Hsz : 0 <= sz <= 8) by (subst sz; destruct (ty =? POD_NONE); [|destruct (ty =? POD_ID)]; lia).
    pose proof (take_pad_len sz r1 ltac:(lia)) as Hl.
    destruct (fuzz_take (Z.to_nat sz) r1) as [p r2] eqn:Et. cbn [fst] in Hl |- *.
    unfold ent_wf. cbn [e_type e_size e_body]. split; [exact Ht|]. split; [exact Hl | lia].
  - destruct (fuzz_u8 r) as [t r1]. destruct (fuzz_u8 r1) as [s r2].
    assert (0 <= s mod 12 < 12) by (apply Z.mod_pos_bound; lia).
    assert (0 <= t mod 21 < 21) by (apply Z.mod_pos_bound; lia).
    pose proof (take_pad_len (s mod 12) r2 ltac:(lia)) as Hl.
    destruct (fuzz_take (Z.to_nat (s mod 12)) r2) as [p r3] eqn:Et. cbn [fst] in Hl |- *.
    unfold ent_wf. cbn [e_type e_size e_body]. split; [lia|]. split; [exact Hl | lia].
  - destruct (fuzz_u8 r) as [t r1]. pose proof (t8_range (Z.to_nat (t mod 4))) as Ht.
    destruct (nth (Z.to_nat (t mod 4)) t8 0 =? POD_STRING).
    + cbn [fst]. unfold ent_wf, POD_STRING. cbn. lia.
    + destruct (fuzz_u8 r1) as [s r2]. cbn [fst]. assert (0 <= s mod 4 < 4) by (apply Z.mod_pos_bound; lia).
      unfold ent_wf. cbn [e_type e_size e_body]. rewrite length_zeros. lia.
  - cbn [fst]. unfold ent_wf, POD_STRUCT. cbn [e_type e_size e_body]. split; [lia|]. split; [reflexivity | lia].
Qed.

Lemma ents_loop_wf : forall k inp, Forall ent_wf (fst (ents_loop k inp)) /\ length (fst (ents_loop k inp)) = k.
Proof.
  induction k as [|k IH]; intros inp; cbn [ents_loop]; [split; [constructor | reflexivity]|].
  pose proof (ent_build_wf inp) as He. destruct (ent_build inp) as [e r]. specialize (IH r).
  destruct (ents_loop k r) as [es r']. cbn [fst] in *. destruct IH as [H1 H2].
  split; [constructor; assumption | cbn; lia].
Qed.

Lemma prop_step_wf : forall s inp,
  let kv := fst (prop_step s inp) in
  (0 <= fst kv < 2^32 /\ pval_wf (snd kv)) /\ Forall ent_wf (ents_of (snd kv)).
Proof.
  intros s inp. unfold prop_step. destruct (fuzz_u8 inp) as [sel r1] eqn:E1.
  destruct (s =? 7); [cbn; repeat constructor; lia|].
  destruct (sel mod 4 =? 0); [cbn; unfold POD_PROP_VOLUME; repeat constructor; lia|].
  destruct (Z.testbit sel 4); [cbn; unfold POD_PROP_PARAMS; repeat constructor; lia|].
  destruct (fuzz_u8 r1) as [c r2] eqn:E2.
  assert (0 <= c mod 33 < 33) by (apply Z.mod_pos_bound; lia).
  pose proof (ents_loop_wf (Z.to_nat (c mod 33)) r2) as [Hw Hl].
  destruct (ents_loop (Z.to_nat (c mod 33)) r2) as [es r3]. cbn [fst snd pval_wf ents_of] in *.
  unfold POD_PROP_PARAMS. split; [split; [lia | lia] | exact Hw].
Qed.

Lemma props_loop_wf : forall s n inp,
  Forall (fun kv => 0 <= fst kv < 2^32 /\ pval_wf (snd kv)) (fst (props_loop s n inp)) /\
  Forall ent_wf (all_ents (fst (props_loop s n inp))) /\ length (fst (props_loop s n inp)) = n.
Proof.
  induction n as [|n IH]; intros inp; cbn [props_loop]; [split; [constructor | split; [constructor | reflexivity]]|].
  pose proof (prop_step_wf s inp) as Hk. destruct (prop_step s inp) as [kv r]. cbn [fst] in Hk.
  specialize (IH r). destruct (props_loop s n r) as [ps r']. cbn [fst] in *. destruct IH as (H1 & H2 & H3).
  destruct Hk as [Hk He]. split; [constructor; assumption|]. split; [|cbn; lia].
  apply all_ents_Forall. apply all_ents_Forall in H2. constructor; assumption.
Qed.

Lemma corr_step_wf : forall len inp, 8 <= len -> corr_wf len (fst (corr_step len inp)).
Proof.
  intros len inp Hl. unfold corr_step. destruct (fuzz_u8 inp) as [c r1].
  destruct ((c mod 16 =? 15) && (8 <? len)) eqn:Eb; [|exact I].
  apply andb_prop in Eb as [_ E]. apply Z.ltb_lt in E.
  destruct (fuzz_u16 r1) as [o r2]. destruct (fuzz_u8 r2) as [n r3].
  assert (0 <= o mod (len - 8) < len - 8) by (apply Z.mod_pos_bound; lia).
  assert (0 <= n mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  pose proof (fuzz_u8s_length (Z.to_nat (Z.min (n mod 8) (len - (8 + o mod (len - 8))))) r3) as HL.
  destruct (fuzz_u8s _ r3) as [bs r4]. cbn [fst] in *. cbn [corr_wf]. rewrite HL. lia.
Qed.

(** The record pod_build makes is well formed; in particular len <= 5440 and every body <= 45 bytes. *)
Theorem pod_build_wf : forall inp r rest, pod_build inp = (r, rest) -> pod_rec_wf r.
Proof.
  intros inp r rest H. unfold pod_build in H. destruct (fuzz_u8 inp) as [s r1] eqn:E1.
  destruct (fuzz_u8 r1) as [np r2] eqn:E2.
  pose proof (props_loop_wf (s mod 8) (Z.to_nat (np mod 4)) r2) as (Hk & He & Hl).
  destruct (props_loop (s mod 8) (Z.to_nat (np mod 4)) r2) as [ps r3] eqn:E3. cbn [fst] in Hk, He, Hl.
  assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hk]; intros kv [_ ?]; auto).
  assert (Hnp : 0 <= np mod 4 < 4) by (apply Z.mod_pos_bound; lia).
  assert (Hl3 : (length ps <= 3)%nat) by lia.
  pose proof (pod_encode_len (s mod 8) ps None Hv He Hl3) as (L1 & L2 & _).
  pose proof (corr_step_wf (Z.of_nat (length (pod_encode (PodRec (s mod 8) ps None)))) r3 L2) as Hc.
  destruct (corr_step _ r3) as [co r4] eqn:E4. injection H as <- <-. cbn [fst] in Hc.
  assert (EL : pod_encode (PodRec (s mod 8) ps co) = pod_encode (PodRec (s mod 8) ps None)) by reflexivity.
  unfold pod_rec_wf. cbn [p_shape p_props p_corr]. rewrite EL.
  split; [apply Z.mod_pos_bound; lia|]. split; [exact Hk|]. split; [exact He|]. split; [exact Hl3|].
  split; [lia | exact Hc].
Qed.

(** ** pod_build at its cuts *)
(** The step functions the walks of the inlined pod_build refine: [ent_build] (one pod of a Struct), [prop_step]
    (one property), [pc_close] (the end of a params Struct, pod.h:434-438) and [corr_step] (pod.h:441-448). A state at
    a cut is the shape, the properties written, and, inside a params Struct's pod loop, the pods of that Struct
    written so far. *)
Record pb_cut := PbCut { pc_shape : Z; pc_props : list (Z * pval); pc_open : option (list ent) }.

(** buf[0..len) at a cut: the top size word is still 0 (patched at pod.h:440) and an open Struct's size word is
    still 0 (patched at pod.h:434). *)
Definition open_bytes (o : option (list ent)) : list byte :=
  match o with
  | None => []
  | Some es => le32 POD_PROP_PARAMS ++ le32 0 ++ le32 0 ++ le32 POD_STRUCT ++ flat_map enc_pod es
  end.
Definition pc_buf (c : pb_cut) : list byte := le32 0 ++ body_bytes (pc_shape c) (pc_props c) ++ open_bytes (pc_open c).
(** The open Struct is the first SPA_PROP_params (pod.h:409's `first`): its pods are recorded in ent[]. *)
Definition pc_first (c : pb_cut) : bool := negb (existsb (fun kv => fst kv =? POD_PROP_PARAMS) (pc_props c)).
(** ent[0..n_ent) at a cut. *)
Definition pc_ents (c : pb_cut) : list ent :=
  match first_params (pc_props c) with
  | Some (PStruct es) => es
  | Some (PInt _) => []
  | None => match pc_open c with Some es => es | None => [] end
  end.
Definition pc_close (c : pb_cut) : pb_cut :=
  match pc_open c with
  | Some es => PbCut (pc_shape c) (pc_props c ++ [(POD_PROP_PARAMS, PStruct es)]) None
  | None => c
  end.

Lemma firstn_app_len : forall (A B : list byte) n, firstn (length A + n) (A ++ B) = A ++ firstn n B.
Proof. intros A B n. apply firstn_app_2. Qed.
Lemma skipn_app_len : forall (A B : list byte) n, skipn (length A + n) (A ++ B) = skipn n B.
Proof. induction A as [|a A IH]; intros B n; cbn; [reflexivity | apply IH]. Qed.

(** Writing one more property (its key, flags and value pod; a shape-7 object writes only the pod). *)
Lemma pc_buf_prop : forall s ps kv, pc_buf (PbCut s ps None) ++ prop_bytes s kv = pc_buf (PbCut s (ps ++ [kv]) None).
Proof.
  intros s ps kv. unfold pc_buf, body_bytes, open_bytes. cbn [pc_shape pc_props pc_open].
  rewrite flat_map_app. cbn [flat_map]. rewrite !app_nil_r, !app_assoc. reflexivity.
Qed.

(** Writing one more pod of the open Struct. *)
Lemma pc_buf_pod : forall s ps es e,
  pc_buf (PbCut s ps (Some es)) ++ enc_pod e = pc_buf (PbCut s ps (Some (es ++ [e]))).
Proof.
  intros s ps es e. unfold pc_buf, open_bytes. cbn [pc_shape pc_props pc_open].
  rewrite flat_map_app. cbn [flat_map]. rewrite !app_nil_r, !app_assoc. reflexivity.
Qed.

(** Opening a params Struct: key, flags, a size word 0 and the type (pod.h:407-408, :421-423). *)
Lemma pc_buf_open : forall s ps,
  pc_buf (PbCut s ps None) ++ le32 POD_PROP_PARAMS ++ le32 0 ++ le32 0 ++ le32 POD_STRUCT = pc_buf (PbCut s ps (Some [])).
Proof.
  intros s ps. unfold pc_buf, open_bytes. cbn [pc_shape pc_props pc_open flat_map]. rewrite !app_nil_r, !app_assoc.
  reflexivity.
Qed.

(** Closing it: the size word at `at` (8 bytes after the property start) becomes len - at - 8 (pod.h:434). *)
Lemma pc_buf_close : forall s ps es, s <> 7 ->
  overwrite (pc_buf (PbCut s ps (Some es))) (length (pc_buf (PbCut s ps None)) + 8)
            (le32 (Z.of_nat (length (pc_buf (PbCut s ps (Some es)))) - Z.of_nat (length (pc_buf (PbCut s ps None))) - 16))
  = pc_buf (pc_close (PbCut s ps (Some es))).
Proof.
  intros s ps es Hs. unfold pc_close. cbn [pc_open pc_shape pc_props].
  assert (E1 : pc_buf (PbCut s ps None) = le32 0 ++ body_bytes s ps).
  { unfold pc_buf, open_bytes. cbn [pc_shape pc_props pc_open]. rewrite app_nil_r. reflexivity. }
  assert (E2 : pc_buf (PbCut s ps (Some es)) = (le32 0 ++ body_bytes s ps) ++ le32 POD_PROP_PARAMS ++ le32 0
                 ++ le32 0 ++ le32 POD_STRUCT ++ flat_map enc_pod es).
  { unfold pc_buf, open_bytes. cbn [pc_shape pc_props pc_open]. rewrite <- !app_assoc. reflexivity. }
  assert (E3 : pc_buf (PbCut s (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None)
               = (le32 0 ++ body_bytes s ps) ++ le32 POD_PROP_PARAMS ++ le32 0
                 ++ le32 (Z.of_nat (length (flat_map enc_pod es))) ++ le32 POD_STRUCT ++ flat_map enc_pod es).
  { rewrite <- pc_buf_prop, E1. unfold prop_bytes. replace (s =? 7) with false by (symmetry; apply Z.eqb_neq; exact Hs).
    reflexivity. }
  rewrite E1, E2, E3. set (A := le32 0 ++ body_bytes s ps). set (F := flat_map enc_pod es).
  rewrite !zlen_app, !zlen_le32.
  replace (Z.of_nat (length A) + (4 + (4 + (4 + (4 + Z.of_nat (length F))))) - Z.of_nat (length A) - 16)
    with (Z.of_nat (length F)) by lia.
  unfold overwrite. rewrite firstn_app_len. rewrite length_le32.
  replace (length A + 8 + 4)%nat with (length A + 12)%nat by lia. rewrite skipn_app_len.
  rewrite <- !app_assoc. f_equal.
Qed.

(** The top size word at the end (pod.h:440): the object as [pod_encode] writes it. *)
Lemma pc_buf_top : forall s ps,
  overwrite (pc_buf (PbCut s ps None)) 0 (le32 (Z.of_nat (length (pc_buf (PbCut s ps None))) - 8))
  = pod_encode (PodRec s ps None).
Proof.
  intros s ps. unfold overwrite, pc_buf, pod_encode, open_bytes. cbn [pc_shape pc_props pc_open p_shape p_props].
  rewrite !app_nil_r. rewrite length_le32. rewrite zlen_app, zlen_le32.
  assert (E : skipn (0 + 4) (le32 0 ++ body_bytes s ps) = body_bytes s ps) by reflexivity. rewrite E.
  replace (4 + Z.of_nat (length (body_bytes s ps)) - 8) with (Z.of_nat (length (body_bytes s ps)) - 4) by lia.
  reflexivity.
Qed.

(** The recorded pods grow with the first params Struct's pods (pod.h:431-432). *)
Lemma pc_ents_pod : forall s ps es e, pc_first (PbCut s ps (Some es)) = true ->
  pc_ents (PbCut s ps (Some (es ++ [e]))) = pc_ents (PbCut s ps (Some es)) ++ [e].
Proof.
  intros s ps es e H. unfold pc_first in H. cbn [pc_props] in H. unfold pc_ents, first_params. cbn [pc_props pc_open].
  destruct (find (fun kv => fst kv =? POD_PROP_PARAMS) ps) as [kv|] eqn:E.
  - apply find_some in E as [Hin Hk]. exfalso. apply negb_true_iff in H.
    assert (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps = true) by (apply existsb_exists; eauto).
    congruence.
  - reflexivity.
Qed.

Lemma pc_ents_pod_other : forall s ps es e, pc_first (PbCut s ps (Some es)) = false ->
  pc_ents (PbCut s ps (Some (es ++ [e]))) = pc_ents (PbCut s ps (Some es)).
Proof.
  intros s ps es e H. unfold pc_first in H. cbn [pc_props] in H. apply negb_false_iff in H.
  apply existsb_exists in H as [kv [Hin Hk]].
  unfold pc_ents, first_params. cbn [pc_props pc_open].
  destruct (find (fun kv => fst kv =? POD_PROP_PARAMS) ps) as [kv'|] eqn:E; [reflexivity|].
  exfalso. pose proof (find_none _ _ E kv Hin) as Hn. cbn in Hn. congruence.
Qed.

(** Lengths and the stop rule. *)
Lemma pc_buf_len_none : forall s ps,
  Forall (fun kv => pval_wf (snd kv)) ps -> Forall ent_wf (all_ents ps) ->
  Z.of_nat (length (pc_buf (PbCut s ps None))) <= 16 + 1808 * Z.of_nat (length ps) /\
  (8 | Z.of_nat (length (pc_buf (PbCut s ps None)))).
Proof.
  intros s ps Hv He. apply all_ents_Forall in He.
  assert (HF : Forall (fun kv => Z.of_nat (length (prop_bytes s kv)) <= 1808) ps).
  { rewrite Forall_forall in Hv, He |- *. intros kv Hin. apply prop_bytes_len; auto. }
  assert (HD : Forall (fun kv => (8 | Z.of_nat (length (prop_bytes s kv)))) ps).
  { rewrite Forall_forall in Hv, He |- *. intros kv Hin. apply prop_bytes_len; auto. }
  pose proof (flat_map_len_le _ _ _ HF) as H1. pose proof (flat_map_len_div8 _ _ HD) as [c Hc].
  unfold pc_buf, body_bytes, hdr_bytes, open_bytes. cbn [pc_shape pc_props pc_open].
  destruct (s =? 7); rewrite !zlen_app, !zlen_le32; cbn [length Z.of_nat]; (split; [lia|]).
  - exists (c + 1). lia.
  - exists (c + 2). lia.
Qed.

Lemma pc_buf_len_open : forall s ps es,
  Forall (fun kv => pval_wf (snd kv)) ps -> Forall ent_wf (all_ents ps) -> Forall ent_wf es ->
  Z.of_nat (length (pc_buf (PbCut s ps (Some es)))) <= 32 + 1808 * Z.of_nat (length ps) + 56 * Z.of_nat (length es) /\
  (8 | Z.of_nat (length (pc_buf (PbCut s ps (Some es))))).
Proof.
  intros s ps es Hv He Hes. destruct (pc_buf_len_none s ps Hv He) as [H1 [c Hc]].
  destruct (ents_len_bound es Hes) as [H2 [d Hd]].
  assert (E : pc_buf (PbCut s ps (Some es))
              = pc_buf (PbCut s ps None) ++ le32 POD_PROP_PARAMS ++ le32 0 ++ le32 0 ++ le32 POD_STRUCT
                ++ flat_map enc_pod es).
  { unfold pc_buf, open_bytes. cbn [pc_shape pc_props pc_open]. rewrite !app_nil_r, !app_assoc. reflexivity. }
  rewrite E, !zlen_app, !zlen_le32. split; [lia|]. exists (c + d + 2). lia.
Qed.

(** pod.h:428's stop rule never fires: in the pod loop of the third property at most, before pod 32 at most. *)
Lemma pc_stop_never : forall s ps es,
  Forall (fun kv => pval_wf (snd kv)) ps -> Forall ent_wf (all_ents ps) -> Forall ent_wf es ->
  (length ps <= 2)%nat -> (length es <= 31)%nat ->
  Z.of_nat (length (pc_buf (PbCut s ps (Some es)))) + 8 + 96 + 8 <= 16384.
Proof.
  intros s ps es Hv He Hes Hp Hq. destruct (pc_buf_len_open s ps es Hv He Hes) as [H _]. lia.
Qed.

(** ** The loops one iteration at a time, forward (a walk's loop invariant after i iterations) *)
Lemma ents_loop_app : forall a b inp,
  ents_loop (a + b) inp = let '(es1, r1) := ents_loop a inp in let '(es2, r2) := ents_loop b r1 in (es1 ++ es2, r2).
Proof.
  induction a as [|a IH]; intros b inp.
  - cbn [Nat.add ents_loop]. destruct (ents_loop b inp). reflexivity.
  - cbn [Nat.add ents_loop]. destruct (ent_build inp) as [e r]. rewrite IH.
    destruct (ents_loop a r) as [es1 r1]. destruct (ents_loop b r1) as [es2 r2]. reflexivity.
Qed.

Lemma ents_loop_S_end : forall k inp,
  ents_loop (S k) inp =
  let '(es, r) := ents_loop k inp in let '(e, r') := ent_build r in (es ++ [e], r').
Proof.
  intros k inp. replace (S k) with (k + 1)%nat by lia. rewrite ents_loop_app.
  destruct (ents_loop k inp) as [es r]. cbn [ents_loop]. destruct (ent_build r) as [e r']. reflexivity.
Qed.

Lemma props_loop_app : forall s a b inp,
  props_loop s (a + b) inp
  = let '(ps1, r1) := props_loop s a inp in let '(ps2, r2) := props_loop s b r1 in (ps1 ++ ps2, r2).
Proof.
  intros s. induction a as [|a IH]; intros b inp.
  - cbn [Nat.add props_loop]. destruct (props_loop s b inp). reflexivity.
  - cbn [Nat.add props_loop]. destruct (prop_step s inp) as [kv r]. rewrite IH.
    destruct (props_loop s a r) as [ps1 r1]. destruct (props_loop s b r1) as [ps2 r2]. reflexivity.
Qed.

Lemma props_loop_S_end : forall s n inp,
  props_loop s (S n) inp =
  let '(ps, r) := props_loop s n inp in let '(kv, r') := prop_step s r in (ps ++ [kv], r').
Proof.
  intros s n inp. replace (S n) with (n + 1)%nat by lia. rewrite props_loop_app.
  destruct (props_loop s n inp) as [ps r]. cbn [props_loop]. destruct (prop_step s r) as [kv r']. reflexivity.
Qed.

(** ** The cursor only moves forward: each rest is a suffix skipn k of the input *)
Definition is_rest (r inp : list byte) : Prop := exists k, r = skipn k inp.

Lemma is_rest_refl : forall inp, is_rest inp inp.
Proof. intros inp. exists 0%nat. reflexivity. Qed.

Lemma is_rest_trans : forall a b c, is_rest a b -> is_rest b c -> is_rest a c.
Proof. intros a b c [k Hk] [j Hj]. exists (k + j)%nat. subst. rewrite skipn_skipn. reflexivity. Qed.

Lemma fuzz_u8_rest : forall inp, is_rest (snd (fuzz_u8 inp)) inp.
Proof. intros inp. exists 1%nat. rewrite fuzz_u8_spec. reflexivity. Qed.
Lemma fuzz_u32_rest' : forall inp, is_rest (snd (fuzz_u32 inp)) inp.
Proof. intros inp. exists 4%nat. apply fuzz_u32_rest. Qed.
Lemma fuzz_u16_rest' : forall inp, is_rest (snd (fuzz_u16 inp)) inp.
Proof. intros inp. exists 2%nat. apply fuzz_u16_rest. Qed.
Lemma fuzz_take_rest : forall n inp, is_rest (snd (fuzz_take n inp)) inp.
Proof. intros n inp. exists n. reflexivity. Qed.
Lemma fuzz_u8s_rest' : forall n inp, is_rest (snd (fuzz_u8s n inp)) inp.
Proof. intros n inp. exists n. apply fuzz_u8s_rest. Qed.

Local Ltac rest_step :=
  repeat match goal with
  | |- context [fuzz_u8 ?i] => let E := fresh in pose proof (fuzz_u8_rest i) as E;
       destruct (fuzz_u8 i) as [? ?]; cbn [snd] in E
  | |- context [fuzz_u16 ?i] => let E := fresh in pose proof (fuzz_u16_rest' i) as E;
       destruct (fuzz_u16 i) as [? ?]; cbn [snd] in E
  | |- context [fuzz_u32 ?i] => let E := fresh in pose proof (fuzz_u32_rest' i) as E;
       destruct (fuzz_u32 i) as [? ?]; cbn [snd] in E
  | |- context [fuzz_take ?n ?i] => let E := fresh in pose proof (fuzz_take_rest n i) as E;
       destruct (fuzz_take n i) as [? ?]; cbn [snd] in E
  end.

Lemma ent_build_rest : forall inp, is_rest (snd (ent_build inp)) inp.
Proof.
  intros inp. unfold ent_build, ent_headamp_key.
  pose proof (fuzz_u8_rest inp) as E0. destruct (fuzz_u8 inp) as [kind r]. cbn [snd] in E0.
  destruct (Z.to_nat (kind mod 10)) as [|[|[|[|[|[|[|[|[|k]]]]]]]]]; rest_step;
    repeat (match goal with |- context [if ?b then _ else _] => destruct b end; rest_step);
    cbn [snd]; eauto 6 using is_rest_trans.
Qed.

Lemma ents_loop_rest : forall k inp, is_rest (snd (ents_loop k inp)) inp.
Proof.
  induction k as [|k IH]; intros inp; cbn [ents_loop]; [apply is_rest_refl|].
  pose proof (ent_build_rest inp) as E. destruct (ent_build inp) as [e r]. specialize (IH r).
  destruct (ents_loop k r) as [es r']. cbn [snd] in *. eauto using is_rest_trans.
Qed.

Lemma prop_step_rest : forall s inp, is_rest (snd (prop_step s inp)) inp.
Proof.
  intros s inp. unfold prop_step. pose proof (fuzz_u8_rest inp) as E1. destruct (fuzz_u8 inp) as [sel r1].
  cbn [snd] in E1. destruct (s =? 7); [exact E1|]. destruct (sel mod 4 =? 0); [exact E1|].
  destruct (Z.testbit sel 4); [exact E1|]. pose proof (fuzz_u8_rest r1) as E2. destruct (fuzz_u8 r1) as [c r2].
  cbn [snd] in E2. pose proof (ents_loop_rest (Z.to_nat (c mod 33)) r2) as E3.
  destruct (ents_loop (Z.to_nat (c mod 33)) r2) as [es r3]. cbn [snd] in *. eauto using is_rest_trans.
Qed.

Lemma props_loop_rest : forall s n inp, is_rest (snd (props_loop s n inp)) inp.
Proof.
  intros s. induction n as [|n IH]; intros inp; cbn [props_loop]; [apply is_rest_refl|].
  pose proof (prop_step_rest s inp) as E. destruct (prop_step s inp) as [kv r]. specialize (IH r).
  destruct (props_loop s n r) as [ps r']. cbn [snd] in *. eauto using is_rest_trans.
Qed.

Lemma corr_step_rest : forall len inp, is_rest (snd (corr_step len inp)) inp.
Proof.
  intros len inp. unfold corr_step. pose proof (fuzz_u8_rest inp) as E1. destruct (fuzz_u8 inp) as [c r1].
  cbn [snd] in E1. destruct ((c mod 16 =? 15) && (8 <? len)); [|exact E1].
  pose proof (fuzz_u16_rest' r1) as E2. destruct (fuzz_u16 r1) as [o r2]. cbn [snd] in E2.
  pose proof (fuzz_u8_rest r2) as E3. destruct (fuzz_u8 r2) as [n r3]. cbn [snd] in E3.
  match goal with |- context [fuzz_u8s ?k r3] => pose proof (fuzz_u8s_rest' k r3) as E4; destruct (fuzz_u8s k r3) end.
  cbn [snd] in *. eauto 6 using is_rest_trans.
Qed.

(** pod_build leaves a suffix of its input: the cursor at its end is data + size - |rest|. *)
Lemma pod_build_rest : forall inp, is_rest (snd (pod_build inp)) inp.
Proof.
  intros inp. unfold pod_build. pose proof (fuzz_u8_rest inp) as E1. destruct (fuzz_u8 inp) as [sh r1].
  cbn [snd] in E1. pose proof (fuzz_u8_rest r1) as E2. destruct (fuzz_u8 r1) as [np r2]. cbn [snd] in E2.
  pose proof (props_loop_rest (sh mod 8) (Z.to_nat (np mod 4)) r2) as E3.
  destruct (props_loop (sh mod 8) (Z.to_nat (np mod 4)) r2) as [ps r3]. cbn [snd] in E3.
  match goal with |- context [corr_step ?l r3] => pose proof (corr_step_rest l r3) as E4; destruct (corr_step l r3) end.
  cbn [snd] in *. eauto 6 using is_rest_trans.
Qed.

(** At the end of the property loop, the recorded pods are the record's [ents]. *)
Lemma pc_ents_final : forall s ps co, pc_ents (PbCut s ps None) = ents (PodRec s ps co).
Proof. intros s ps co. unfold pc_ents, ents. cbn [pc_props pc_open p_props]. destruct (first_params ps) as [[]|]; reflexivity. Qed.

(** ** More facts on the record *)
Lemma length_overwrite : forall l off bs, (off + length bs <= length l)%nat -> length (overwrite l off bs) = length l.
Proof. intros l off bs H. unfold overwrite. rewrite !length_app, length_firstn, length_skipn. lia. Qed.

Lemma find_app : forall {A} (f : A -> bool) l1 l2,
  find f (l1 ++ l2) = match find f l1 with Some x => Some x | None => find f l2 end.
Proof. intros A f l1 l2. induction l1 as [|x l1 IH]; cbn; [reflexivity|]. destruct (f x); [reflexivity | exact IH]. Qed.

(** One more property: the first SPA_PROP_params stays, or this one becomes it (pod.h:409-418, :435-437). *)
Lemma first_params_app : forall ps kv, first_params (ps ++ [kv]) =
  match first_params ps with
  | Some v => Some v
  | None => if fst kv =? POD_PROP_PARAMS then Some (snd kv) else None
  end.
Proof.
  intros ps kv. unfold first_params. rewrite find_app. destruct (find _ ps) as [x|]; [reflexivity|].
  cbn [find]. destruct (fst kv =? POD_PROP_PARAMS); reflexivity.
Qed.

(** The recorded pods: at most 32, each well formed (n_ent <= 32, e_size <= 45). *)
Lemma ents_wf : forall r, pod_rec_wf r -> (length (ents r) <= 32)%nat /\ Forall ent_wf (ents r).
Proof.
  intros r (_ & Hk & He & _). unfold ents.
  destruct (first_params (p_props r)) as [[i|es]|] eqn:E; try (split; [cbn; lia | constructor]).
  unfold first_params in E. destruct (find _ _) as [kv|] eqn:F; [|discriminate]. cbn in E. injection E as E.
  apply find_some in F as [Hin _]. split.
  - rewrite Forall_forall in Hk. destruct (Hk kv Hin) as [_ Hv]. rewrite E in Hv. exact Hv.
  - apply all_ents_Forall in He. rewrite Forall_forall in He. specialize (He kv Hin). rewrite E in He. exact He.
Qed.
