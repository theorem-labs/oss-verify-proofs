(** Satisfiability witnesses of the shared Pod texts, at the real instance: inputs of the reac-pw harnesses' own
    seeds and worked inputs, run through the model by computation. Each lemma shows that a premise a walk or a
    contract will take as given holds of a record pod_build really makes, so no text is vacuous:
    - [pod_rec_wf] / [pod_build_wf] (Model.v): the input T4 (298 bytes with the flags byte) reaches len 5440 and 32
      recorded pods of 45 bytes each, the largest the model allows; W1 is the `role-master` seed;
    - [pp_bytes] (Layout.v): 19744 bytes for T4 and W1;
    - [spa_view_encode] (Spa.v): each of the four views is reached (W1 VPods, W7 VParamsNotStruct, W5 VNotProps for a
      Struct object, W6 VNotProps for a PropInfo object, and VNoParams);
    - [buf_header] (Spa.v): holds of the corrupted W8 buffer;
    - the step functions (Model.v): W7 runs all three property kinds, W8 the corruption.
    The inputs are the bytes after the harness's flags byte. Statement text and computation only. *)
From Stdlib Require Import String ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables Model Accessors Spa Layout.
Import ListNotations.
Open Scope Z_scope.

Definition bl (l : list Z) : list byte := map (Z_to_bv 8) l.

(** W1, the `role-master` seed: Props, one params Struct ("reac.cfg.role", Int 0). *)
Definition W1 : list byte := bl [0; 1; 1; 2; 1; 1; 2; 1; 0; 0; 0; 0; 0].
(** W5: a Struct object (shape 7) with two Int-0 pods. *)
Definition W5 : list byte := bl [7; 2; 0; 0; 0; 0].
(** W6: a PropInfo object (shape 6) with the role pair. *)
Definition W6 : list byte := bl [6; 1; 1; 2; 1; 1; 2; 1; 0; 0].
(** W7: volume, then params Int 7, then a params Struct: the first params is the Int. *)
Definition W7 : list byte := bl [0; 3; 0; 17; 1; 2; 1; 1; 2; 1; 0; 0; 0].
(** W8: W1 with 3 bytes written at offset 8 + 5. *)
Definition W8 : list byte := bl [0; 1; 1; 2; 1; 1; 2; 0; 15; 5; 0; 3; 170; 187; 204].
(** A Props object with a volume property only: no SPA_PROP_params. *)
Definition W9 : list byte := bl [0; 1; 4; 0].
(** T4: 3 params Structs of 32 head-amp keys of 45 bytes ("reac.headamp.-99999999999999999999.phantom.x"). *)
Definition T4 : list byte := bl ([0; 3] ++ concat (repeat ([1; 32] ++ concat (repeat [0; 251; 126] 32)) 3) ++ [0]).

(** 297 bytes after the flags byte (298 with it). *)
Lemma T4_length : length T4 = 297%nat.
Proof. reflexivity. Qed.

(** ** pod_rec_wf: T4 is at every bound *)
Lemma T4_wf : pod_rec_wf (fst (pod_build T4)).
Proof. apply (pod_build_wf T4 _ (snd (pod_build T4))). apply surjective_pairing. Qed.

Lemma T4_bounds :
  let r := fst (pod_build T4) in
  Z.of_nat (length (pod_encode r)) = 5440 /\ length (ents r) = 32%nat /\
  forallb (fun e => (e_type e =? POD_STRING) && (e_size e =? 45)) (all_ents (p_props r)) = true /\
  length (all_ents (p_props r)) = 96%nat /\ corrupt r = false /\ snd (pod_build T4) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(** pod.h:428's stop rule needs len + 112 > 16384; T4's len is 5440. *)
Lemma T4_stop_far : Z.of_nat (length (pod_encode (fst (pod_build T4)))) + 8 + 96 + 8 <= 16384.
Proof. vm_compute. intros H. discriminate H. Qed.

Lemma W1_record :
  pod_build W1 = (PodRec 0 [(POD_PROP_PARAMS, PStruct [ent_text (sbytes "reac.cfg.role"%string) true; Ent POD_INT 4 (le32 0)])]
                    None, []).
Proof. vm_compute. reflexivity. Qed.

Lemma W1_wf : pod_rec_wf (fst (pod_build W1)).
Proof. apply (pod_build_wf W1 _ (snd (pod_build W1))). apply surjective_pairing. Qed.

(** The 72 bytes of W1: the Props header, the params property, its Struct header, the key String, the Int 0. *)
Lemma W1_bytes : map bv_unsigned (buf (fst (pod_build W1))) =
  [0x40;0;0;0; 0x0f;0;0;0; 2;0;4;0; 2;0;0;0; 1;0;8;0; 0;0;0;0; 0x28;0;0;0; 0x0e;0;0;0; 0x0e;0;0;0; 8;0;0;0;
      0x72;0x65;0x61;0x63;0x2e;0x63;0x66;0x67;0x2e;0x72;0x6f;0x6c;0x65;0;0;0; 4;0;0;0; 4;0;0;0; 0;0;0;0; 0;0;0;0].
Proof. vm_compute. reflexivity. Qed.

(** ** pp_bytes: 19744 bytes *)
Lemma T4_pp_length : Z.of_nat (length (pp_bytes (fst (pod_build T4)))) = PP_SIZE.
Proof. apply length_pp_bytes. exact T4_wf. Qed.
Lemma W1_pp_length : Z.of_nat (length (pp_bytes (fst (pod_build W1)))) = PP_SIZE.
Proof. apply length_pp_bytes. exact W1_wf. Qed.

(** ** spa_view_encode: the four views *)
Definition ent_key (e : ent) : Z * Z * list Z := (e_type e, e_size e, map bv_unsigned (e_body e)).
Definition view_pods (v : spa_view) : option (list (Z * Z * list Z)) :=
  match v with VPods cs => Some (map ent_key cs) | _ => None end.

Lemma views_reached :
  view_pods (spa_view_of (buf (fst (pod_build W1))))
    = Some [(8, 14, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 111; 108; 101; 0]); (4, 4, [0; 0; 0; 0])] /\
  spa_view_of (buf (fst (pod_build W7))) = VParamsNotStruct /\
  spa_view_of (buf (fst (pod_build W5))) = VNotProps /\
  spa_view_of (buf (fst (pod_build W6))) = VNotProps /\
  spa_view_of (buf (fst (pod_build W9))) = VNoParams.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma views_match :
  forallb (fun inp => let r := fst (pod_build inp) in
                      match spa_view_of (pod_encode r), record_view r with
                      | VNotProps, VNotProps | VNoParams, VNoParams | VParamsNotStruct, VParamsNotStruct => true
                      | VPods a, VPods b => (length a =? length b)%nat
                      | _, _ => false
                      end) [W1; W5; W6; W7; W8; W9; T4] = true.
Proof. vm_compute. reflexivity. Qed.

(** ** buf_header on a corrupted buffer *)
Lemma W8_header :
  let r := fst (pod_build W8) in
  corrupt r = true /\ option_map (fun ob => (fst ob, map bv_unsigned (snd ob))) (p_corr r) = Some (13, [170; 187; 204]) /\
  u32_at (buf r) 0 = Z.of_nat (length (buf r)) - 8 /\ Z.of_nat (length (buf r)) = 72 /\
  buf r <> pod_encode r.
Proof. vm_compute. repeat split; try reflexivity. discriminate. Qed.

(** ** The step functions *)
Lemma W7_props :
  fst (props_loop 0 3 (skipn 2 W7)) =
  [(POD_PROP_VOLUME, PInt 7); (POD_PROP_PARAMS, PInt 7);
   (POD_PROP_PARAMS, PStruct [ent_text (sbytes "reac.cfg.role"%string) true; Ent POD_INT 4 (le32 0)])].
Proof. vm_compute. reflexivity. Qed.

Lemma W7_fields :
  let r := fst (pod_build W7) in
  is_props r = true /\ has_params r = true /\ params_struct r = false /\ ents r = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(** The cut images compose to the final one on W7: properties one by one, then the top size word. *)
Lemma W7_cuts :
  let ps := fst (props_loop 0 3 (skipn 2 W7)) in
  overwrite (pc_buf (PbCut 0 ps None)) 0 (le32 (Z.of_nat (length (pc_buf (PbCut 0 ps None))) - 8))
  = buf (fst (pod_build W7)).
Proof. vm_compute. reflexivity. Qed.
