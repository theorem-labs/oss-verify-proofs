(** The accessors fuzz/pod.h gives the harnesses over the record (pod.h:88-145): pod_string, pod_bool, pod_int,
    pod_float and the pairing of pod_next_pair. Shared by fuzz_role, fuzz_rate and fuzz_headamp. Statement text
    and computation only: no function of a binary is proved here. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables Model.
Import ListNotations.
Open Scope Z_scope.

(** The int32 value of a u32 pattern. *)
Definition s32 (z : Z) : Z := if z <? 2^31 then z else z - 2^32.

(** The byte body[size - 1] of the 96-byte array (the rest of the array is 0). *)
Definition last_body_byte (e : ent) : Z := bv_unsigned (nth (Z.to_nat (e_size e - 1)) (e_body e) NUL).

(** pod_string (pod.h:90-96): type String, size >= 1, last body byte NUL; the text is the body up to its first
    NUL (what strcmp reads). *)
Definition key_of (e : ent) : option (list byte) :=
  if (e_type e =? POD_STRING) && (1 <=? e_size e) && (last_body_byte e =? 0) then Some (cstr (e_body e)) else None.
(** pod_int / pod_float / pod_bool (pod.h:98-122): the first 4 body bytes. pod_float gives the bit pattern. *)
Definition int_of (e : ent) : option Z :=
  if (e_type e =? POD_INT) && (4 <=? e_size e) then Some (s32 (rd32 (e_body e))) else None.
Definition float_of (e : ent) : option Z :=
  if (e_type e =? POD_FLOAT) && (4 <=? e_size e) then Some (rd32 (e_body e)) else None.
Definition bool_of (e : ent) : option bool :=
  if (e_type e =? POD_BOOL) && (4 <=? e_size e) then Some (negb (rd32 (e_body e) =? 0)) else None.

(** The pairs of a Struct (pod.h:124-145): a pod in a key slot that is not a key ([kf] gives None) is skipped and
    the slot stays open; a key takes the slot; the next pod, whatever it is, is its value, and the pair is
    consumed. A key with no pod after it makes no pair. [kf] is the reader's key test. *)
Fixpoint pairs_by (kf : ent -> option (list byte)) (es : list ent) (k : option (list byte))
  : list (list byte * ent) :=
  match es with
  | [] => []
  | e :: es' =>
      match k with
      | None => pairs_by kf es' (kf e)
      | Some k' => (k', e) :: pairs_by kf es' None
      end
  end.

(** pod_next_pair's pairs, from the start of ent[] (its at = 0). *)
Definition pairs (es : list ent) : list (list byte * ent) := pairs_by key_of es None.

(** ** Facts *)
Lemma pairs_by_ext : forall f g es k, (forall e, In e es -> f e = g e) -> pairs_by f es k = pairs_by g es k.
Proof.
  intros f g es. induction es as [|e es IH]; intros k H; [reflexivity|]. cbn [pairs_by].
  destruct k as [k|].
  - f_equal. apply IH. intros x Hx. apply H. right. exact Hx.
  - rewrite (H e (or_introl eq_refl)). apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma pairs_by_in : forall f es k key e, In (key, e) (pairs_by f es k) -> In e es.
Proof.
  intros f es. induction es as [|x es IH]; intros k key e H; [destruct H|]. cbn [pairs_by] in H.
  destruct k as [k|].
  - destruct H as [H|H]; [injection H as _ <-; left; reflexivity|]. right. eapply IH. exact H.
  - right. eapply IH. exact H.
Qed.

Lemma s32_range : forall z, 0 <= z < 2^32 -> -2^31 <= s32 z < 2^31.
Proof. intros z Hz. unfold s32. destruct (Z.ltb_spec z (2^31)); lia. Qed.
