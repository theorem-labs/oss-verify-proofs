(** spa_pod_get_bool on a child of the params Struct, the accessor fuzz_headamp's reader adds to the three of
    Pod/Spa.v (spa_get_string / spa_get_int / spa_get_float), and its link to pod.h's pod_bool ([bool_of],
    Pod/Accessors.v). A shared addition to the Pod text (for review by its owner before a second unit uses
    it). Statement text and computation only: no function of a binary is proved here.

    SPA 1.6.10:
    - spa/pod/iter.h:131-134: spa_pod_get_bool(pod, value) = spa_pod_body_get_bool(pod, SPA_POD_BODY_CONST(pod), value);
    - spa/pod/body.h:134-147: spa_pod_is_bool(pod) = SPA_POD_CHECK(pod, SPA_TYPE_Bool, sizeof(int32_t)); then
      *value = !!(the int32 at the body) and 0, else -EINVAL;
    - spa/pod/pod.h:33-39: SPA_POD_CHECK(pod, type, size) = SPA_POD_IS_VALID(pod) (body size < SPA_POD_MAX_SIZE)
      && pod->type == type && pod->size >= size.
    The same SPA_POD_CHECK form as [spa_get_int]. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Accessors Spa.
Import ListNotations.
Open Scope Z_scope.

(** spa_pod_get_bool (iter.h:131-134, body.h:134-147): Some (the int32 body is not 0), or None for -EINVAL. *)
Definition spa_get_bool (e : ent) : option bool :=
  if (e_size e <? SPA_POD_MAX_SIZE) && (e_type e =? POD_BOOL) && (4 <=? e_size e)
  then Some (negb (rd32 (e_body e) =? 0)) else None.

(** On a pod whose size passes SPA_POD_IS_VALID (every pod pod_build writes: size <= 45), SPA's reading is pod.h's. *)
Lemma spa_get_bool_bool_of : forall e, e_size e < SPA_POD_MAX_SIZE -> spa_get_bool e = bool_of e.
Proof. intros e H. unfold spa_get_bool, bool_of. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

(** ** Satisfiability: each answer is reached *)
(** A Bool 1 (true), a Bool 0 (false), an Int 1 (wrong type: None), a Bool of size 3 (too short: None), and a Bool
    whose size word fails SPA_POD_IS_VALID (None, where pod.h's [bool_of] still reads it). *)
Lemma spa_get_bool_witnesses :
  spa_get_bool (Ent POD_BOOL 4 (le32 1)) = Some true /\
  spa_get_bool (Ent POD_BOOL 4 (le32 0)) = Some false /\
  spa_get_bool (Ent POD_INT 4 (le32 1)) = None /\
  spa_get_bool (Ent POD_BOOL 3 (firstn 3 (le32 1))) = None /\
  spa_get_bool (Ent POD_BOOL SPA_POD_MAX_SIZE (le32 1)) = None /\
  bool_of (Ent POD_BOOL SPA_POD_MAX_SIZE (le32 1)) = Some true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A Bool pod_build writes (kind 4: le32 (v mod 3), size 4) reads true for v mod 3 = 2. *)
Lemma spa_get_bool_kind4 : spa_get_bool (Ent POD_BOOL 4 (le32 2)) = Some true.
Proof. vm_compute. reflexivity. Qed.
