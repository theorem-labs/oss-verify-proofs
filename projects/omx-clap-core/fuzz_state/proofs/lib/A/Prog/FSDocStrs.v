(* FS_DOC_STRS: fuzz_state's harness document has only string and object values (i), and its strings are plain (ii).

   rule 24: no function proved. This file proves a model-level fact about one document value. It walks no binary
   function, and it restates no released proof of a function.

   Owner: the READER lane of the fuzz_state ASan port (a Theorem Labs lane), which holds the named hypothesis FS_DOC_STRS
   (internal path; second clause, STRUCTURE, added by a Theorem Labs lane via
   a Theorem Labs lane at 20:51Z). Written for a Theorem Labs lane on a working branch.
   Port-from: none. It is a new model-level lemma, and it consumes only the released plain results listed below.

   fs.c below is projects/omx-clap-core/fuzz_state/source/fuzz_state.c (git blob b883b8e11c5, sha256 c9a0a0b41dd9...;
   upstream FreeMixer/omx-clap-core 246923f0 fuzz/fuzz_state.c, unmodified). preset_file.h and preset_file.c are
   src/ of the same upstream commit (sha256 22fa3439... and 34d5664a...).

   THE DOCUMENT. round_trip_document builds it at fs.c:237-247 and writes it with pj_write at fs.c:248:
     {"format": PRESET_FORMAT_STATE, "carries": PRESET_CARRIES_STATE,
      "state": {"encoding": PRESET_ENCODING_BASE64, "context": PRESET_CONTEXT_PRESET, "bytes": text}}
   The root is pj_object(&doc) (fs.c:237) and the "state" value is pj_object(&state) (fs.c:238): type PJ_OBJECT
   (preset_file.c:433-437). Every other value is made by pj_string (fs.c:242-246): type PJ_STRING (preset_file.c:406-411).
   round_trip_document calls no pj_number, pj_array or other constructor. Any failed pj_string or pj_set aborts
   (fs.c:242-247), and the keys are distinct inside each object, so every pj_set appends one member
   (preset_file.c:373-391). The eleven strings, and where their bytes come from:
     keys    "format" (fs.c:242), "carries" (fs.c:243), "encoding" (fs.c:244), "context" (fs.c:245), "bytes" and
             "state" (fs.c:246): string literals of the harness itself, copied by pj_set's strdup (preset_file.c:384);
     values  PRESET_FORMAT_STATE = PRESET_FORMAT_PREFIX "2" = "org.openmixer.preset/2" (preset_file.h:38,40),
             PRESET_CARRIES_STATE = "state" (preset_file.h:45), PRESET_ENCODING_BASE64 = "base64" (preset_file.h:51),
             PRESET_CONTEXT_PRESET = "preset" (preset_file.h:48), copied by pj_string's strdup (preset_file.c:410);
     leaf    text (fs.c:246): round_trip_document's parameter (fs.c:229). check_round_trip passes it at fs.c:309, and
             there it is preset_base64_encode(body, len) (fs.c:280), checked equal to the harness's own encoding at
             fs.c:301.
   No string other than the leaf depends on the input, and no value depends on the input in its kind. A "string" here
   is what put_string writes: a member key (preset_file.c:546) or a string value (preset_file.c:535). put_string takes
   its plain path for a byte c exactly when c is not 0x22 (double quote), not 0x5c (backslash) and not below 0x20
   (preset_file.c:494), which is [plain_byte c] of lib/A/FSH_Gen.v:144, the narrow-form predicate the WRITER and the
   READER lanes share (one definition for the port; a Theorem Labs lane wrote it, FSH_Gen.v:135-156 holds it).

   THE MODEL. The document value is the released [crt_doc] (lib/Prog/check_round_trip_stages_b.v:48-49): [fs_doc es]
   below is [JObj (crt_doc es)], the tree for which crt_doc_ok (check_round_trip_stages_b.v:188-255) proves pj_wf, the
   ttrace length and the size bounds. [fs_doc_shape] shows by computation that this tree is the one the C text above
   builds, member for member, with each released byte list equal to its C literal. Its leaf is the encoder's text: for
   every [bs] with [bytes_ok bs] (lib/Prog/preset_base64_encode_c.v:43), the released plain post of
   preset_base64_encode (preset_base64_encode_contract, preset_base64_encode_c.v:35-67, proved by
   preset_base64_encode_holds, lib/Prog/preset_base64_encode.v:449) says that the bytes of the returned text are
   [b64_enc bs] and then its NUL (preset_base64_encode_c.v:66-67). So the document of input [bs] is
   [fs_doc (b64_enc bs)]. Clause (i) holds for [fs_doc es] for every [es] by the construction. In clause (ii), the ten
   constants are plain by computation ([fd_consts_plain]) and the leaf by the encoder's output alphabet
   ([b64_enc_alphabet], by induction over every [bs], not from an example).

   RELEASED RESULTS CONSUMED (blob shas; each file is byte-identical at c8557374ad2 (origin/ossv/recipes at the cut of
   a working branch, an ancestor of this branch), at origin/ossv/recipes a8831f7c5c2 and at release/pau-projects-recipes
   b6a0088adc):
     lib/Spec/PjTree.v                     180b25cdb3  jv
     lib/Prog/WriterSpec.v                 95b32834cf  special, b64c, b64_enc, bytes_ok
     lib/Prog/WriterSpecFacts.v            73cdcfb59a  list3_ind, bytes_ok_cons
     lib/Prog/check_round_trip_stages_b.v  1e67b34545  crt_doc, crt_st, K_ENCODING, V_BASE64, K_CONTEXT, V_PRESET
     lib/Prog/check_round_trip_st8.v       7148536bd3  CRT_FORMAT, CRT_CARRIES, CRT_FMT2
     lib/Prog/check_round_trip_runs.v      c24e4308c3  CRT_STATE, CRT_BYTES
   The source of the leaf, cited above and not imported: lib/Prog/preset_base64_encode_c.v f7f2dcea09 and
   lib/Prog/preset_base64_encode.v 36d0b221aa.

   NOT RELEASED, IMPORTED FOR ITS PREDICATES: lib/A/FSH_Gen.v:144-156 (plain_byte, plain_bytes, jv_plain; a Theorem Labs lane's
   text, moved there by the S0 base so the port has one copy). [plain_not_special] is restated here over FSH_Gen's
   [plain_byte] (same proof as lib/A/FSW_writer_model.v:19-26 of a working branch f995a01189d).

   STATEMENTS (no Admitted, no Axiom, no Parameter, no Section hypothesis):
     FS_DOC_STRS             for every [bs] with [bytes_ok bs]:
                               fs_doc_values  (fs_doc (b64_enc bs))   (i) STRUCTURE: the root and every value in the
                                                                      tree is a string or an object; never a number,
                                                                      true, false, null or array;
                             /\ fs_doc_strings (fs_doc (b64_enc bs))  (ii) CHARACTERS: every key and every string
                                                                      value is [plain_bytes]: no byte below 0x20, no
                                                                      0x22 and no 0x5c.
     FS_DOC_STRS_values      clause (i) alone, for every [es].
     FS_DOC_STRS_strings     clause (ii) alone.
     FS_DOC_STRS_special     clause (ii) in WriterSpec's escape test: [special c = false] for every byte.
     b64_enc_plain           the leaf alone: [plain_bytes (b64_enc bs)].
     fd_const_plain          each of the ten constant strings alone: [plain_bytes s].
     fs_doc_jv_plain         the two clauses in the WRITER's form: [jv_plain (fs_doc (b64_enc bs))], the premise of
                             a Theorem Labs lane's pj_write_spec.
     fs_doc_vals_list        the six values in write order, and fs_doc_strs_list the eleven strings in write order;
                             only the last string depends on the input. So neither clause is vacuous.
     fs_doc_shape            the tree written out from the C text. *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Strings.String Strings.Ascii.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree.
(* The released lib/Prog modules are Required, never Require Import'd, and their names are written qualified: a
   lib/Prog module loads lib/Lib.PropExec, whose getr / mkst / seg_rom differ from YK11's (a Theorem Labs lane, FSH_Fn_FORM.md
   top). This file names none of those three, but it keeps the port's one rule. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterSpecFacts
  check_round_trip_stages_b.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSH_Gen.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------- the two clauses *)

(* The values of a tree, every one at any depth: each member value and each array item, in write order. *)
Fixpoint jv_vals (t : jv) : list jv :=
  match t with
  | JArr items => flat_map (fun u => u :: jv_vals u) items
  | JObj members => flat_map (fun '(_, v) => v :: jv_vals v) members
  | _ => []
  end.

(* The strings of a tree: every member key and every string value, in write order. *)
Fixpoint jv_strs (t : jv) : list (list Z) :=
  match t with
  | JStr s => [s]
  | JArr items => flat_map jv_strs items
  | JObj members => flat_map (fun '(k, v) => k :: jv_strs v) members
  | _ => []
  end.

Definition str_or_obj (v : jv) : Prop :=
  match v with
  | JStr _ | JObj _ => True
  | _ => False
  end.

(* (i) STRUCTURE: the root and every value is a string or an object. *)
Definition fs_doc_values (t : jv) : Prop := forall v, In v (t :: jv_vals t) -> str_or_obj v.

(* (ii) CHARACTERS: every key and every string value is plain (FSH_Gen's plain_bytes). *)
Definition fs_doc_strings (t : jv) : Prop := forall s, In s (jv_strs t) -> plain_bytes s.

(* The document value: the released crt_doc (check_round_trip_stages_b.v:48-49). *)
Definition fs_doc (es : list Z) : jv := JObj (check_round_trip_stages_b.crt_doc es).

(* ---------------------------------------------------------------- the document, from the C text *)

Fixpoint zs (s : String.string) : list Z :=
  match s with
  | String.EmptyString => []
  | String.String a r => Z.of_N (Ascii.N_of_ascii a) :: zs r
  end.

Module FdText.
Import Stdlib.Strings.String.
Local Open Scope string_scope.
Definition k_format : string := "format".                                  (* fs.c:242 *)
Definition v_format : string := String.append "org.openmixer.preset/" "2". (* preset_file.h:38,40 *)
Definition k_carries : string := "carries".                                (* fs.c:243 *)
Definition v_carries : string := "state".                                  (* preset_file.h:45 *)
Definition k_state : string := "state".                                    (* fs.c:246 *)
Definition k_encoding : string := "encoding".                              (* fs.c:244 *)
Definition v_encoding : string := "base64".                                (* preset_file.h:51 *)
Definition k_context : string := "context".                                (* fs.c:245 *)
Definition v_context : string := "preset".                                 (* preset_file.h:48 *)
Definition k_bytes : string := "bytes".                                    (* fs.c:246 *)
End FdText.

Definition FD_K_FORMAT : list Z := zs FdText.k_format.
Definition FD_V_FORMAT : list Z := zs FdText.v_format.
Definition FD_K_CARRIES : list Z := zs FdText.k_carries.
Definition FD_V_CARRIES : list Z := zs FdText.v_carries.
Definition FD_K_STATE : list Z := zs FdText.k_state.
Definition FD_K_ENCODING : list Z := zs FdText.k_encoding.
Definition FD_V_ENCODING : list Z := zs FdText.v_encoding.
Definition FD_K_CONTEXT : list Z := zs FdText.k_context.
Definition FD_V_CONTEXT : list Z := zs FdText.v_context.
Definition FD_K_BYTES : list Z := zs FdText.k_bytes.

(* The "state" object (fs.c:238, 244-246) and the document (fs.c:237, 242-243, 246). *)
Definition fd_state (es : list Z) : jv :=
  JObj [(FD_K_ENCODING, JStr FD_V_ENCODING); (FD_K_CONTEXT, JStr FD_V_CONTEXT); (FD_K_BYTES, JStr es)].

(* The released tree is the one the C text builds: by computation, each released byte list is its C literal. *)
Lemma fs_doc_shape : forall es, fs_doc es =
  JObj [(FD_K_FORMAT, JStr FD_V_FORMAT); (FD_K_CARRIES, JStr FD_V_CARRIES); (FD_K_STATE, fd_state es)].
Proof. intros es. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------- (i) STRUCTURE *)

(* The six values of the document, in write order. *)
Lemma fs_doc_vals_list : forall es, jv_vals (fs_doc es) =
  [JStr FD_V_FORMAT; JStr FD_V_CARRIES; fd_state es; JStr FD_V_ENCODING; JStr FD_V_CONTEXT; JStr es].
Proof. intros es. rewrite fs_doc_shape. reflexivity. Qed.

Theorem FS_DOC_STRS_values : forall es, fs_doc_values (fs_doc es).
Proof.
  intros es v Hv. rewrite fs_doc_vals_list in Hv. rewrite fs_doc_shape in Hv.
  repeat (destruct Hv as [<-|Hv]; [exact I|]). destruct Hv.
Qed.

(* ---------------------------------------------------------------- (ii) CHARACTERS *)

(* The test of FSH_Gen's plain_byte, for the computation over the constants. *)
Definition plain_byteb (c : Z) : bool := (32 <=? c) && negb (c =? 34) && negb (c =? 92).

Lemma plain_byteb_ok : forall c, plain_byteb c = true -> plain_byte c.
Proof.
  intros c H. unfold plain_byteb in H. rewrite !andb_true_iff, !negb_true_iff in H.
  destruct H as [[H1 H2] H3]. apply Z.leb_le in H1. rewrite Z.eqb_neq in H2, H3. unfold plain_byte. lia.
Qed.

(* The ten constant strings, in write order. *)
Definition fd_consts : list (list Z) :=
  [FD_K_FORMAT; FD_V_FORMAT; FD_K_CARRIES; FD_V_CARRIES; FD_K_STATE; FD_K_ENCODING; FD_V_ENCODING; FD_K_CONTEXT;
   FD_V_CONTEXT; FD_K_BYTES].

(* The eleven strings of the document: the ten constants, then the leaf. *)
Lemma fs_doc_strs_list : forall es, jv_strs (fs_doc es) = fd_consts ++ [es].
Proof. intros es. rewrite fs_doc_shape. reflexivity. Qed.

(* The constants, by computation. *)
Lemma fd_consts_plain : forallb (forallb plain_byteb) fd_consts = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fd_const_plain : forall s, In s fd_consts -> plain_bytes s.
Proof.
  intros s Hs. pose proof fd_consts_plain as K. rewrite forallb_forall in K. specialize (K s Hs).
  rewrite forallb_forall in K. unfold plain_bytes. apply Forall_forall. intros c Hc.
  exact (plain_byteb_ok c (K c Hc)).
Qed.

(* The encoder's output alphabet: RFC 4648's 64 letters and the pad '='. *)
Definition b64_alpha (c : Z) : Prop :=
  65 <= c <= 90 \/ 97 <= c <= 122 \/ 48 <= c <= 57 \/ c = 43 \/ c = 47 \/ c = 61.

Lemma b64c_alpha : forall v, 0 <= v < 64 -> b64_alpha (WriterSpec.b64c v).
Proof.
  intros v Hv. unfold WriterSpec.b64c, b64_alpha.
  destruct (v <? 26) eqn:E1; [apply Z.ltb_lt in E1; lia | apply Z.ltb_ge in E1].
  destruct (v <? 52) eqn:E2; [apply Z.ltb_lt in E2; lia | apply Z.ltb_ge in E2].
  destruct (v <? 62) eqn:E3; [apply Z.ltb_lt in E3; lia | apply Z.ltb_ge in E3].
  destruct (v =? 62) eqn:E4; lia.
Qed.

Lemma alpha_b64c : forall v l, 0 <= v < 64 -> Forall b64_alpha l -> Forall b64_alpha (WriterSpec.b64c v :: l).
Proof. intros v l Hv Hl. apply Forall_cons; [apply b64c_alpha; exact Hv | exact Hl]. Qed.

Lemma alpha_pad : forall l, Forall b64_alpha l -> Forall b64_alpha (61 :: l).
Proof. intros l Hl. apply Forall_cons; [unfold b64_alpha; lia | exact Hl]. Qed.

(* Every text the encoder's post can give, for every body: b64_enc (WriterSpec.v:64-72) over any bytes. *)
Lemma b64_enc_alphabet : forall bs, WriterSpec.bytes_ok bs -> Forall b64_alpha (WriterSpec.b64_enc bs).
Proof.
  intros bs. induction bs as [|a|a b|a b c l IH] using WriterSpecFacts.list3_ind; intros Hb.
  - apply Forall_nil.
  - destruct (WriterSpecFacts.bytes_ok_cons _ _ Hb) as [Ha _]. cbn [WriterSpec.b64_enc].
    apply alpha_b64c; [Z.div_mod_to_equations; lia|].
    apply alpha_b64c; [Z.div_mod_to_equations; lia|].
    apply alpha_pad. apply alpha_pad. apply Forall_nil.
  - destruct (WriterSpecFacts.bytes_ok_cons _ _ Hb) as [Ha Hb1].
    destruct (WriterSpecFacts.bytes_ok_cons _ _ Hb1) as [Hb2 _]. cbn [WriterSpec.b64_enc].
    apply alpha_b64c; [Z.div_mod_to_equations; lia|].
    apply alpha_b64c; [Z.div_mod_to_equations; lia|].
    apply alpha_b64c; [Z.div_mod_to_equations; lia|].
    apply alpha_pad. apply Forall_nil.
  - destruct (WriterSpecFacts.bytes_ok_cons _ _ Hb) as [Ha Hb1].
    destruct (WriterSpecFacts.bytes_ok_cons _ _ Hb1) as [Hb2 Hb3].
    destruct (WriterSpecFacts.bytes_ok_cons _ _ Hb3) as [Hc Hl]. cbn [WriterSpec.b64_enc].
    apply alpha_b64c; [Z.div_mod_to_equations; lia|].
    apply alpha_b64c; [Z.div_mod_to_equations; lia|].
    apply alpha_b64c; [Z.div_mod_to_equations; lia|].
    apply alpha_b64c; [Z.div_mod_to_equations; lia|].
    exact (IH Hl).
Qed.

Lemma b64_alpha_plain : forall c, b64_alpha c -> plain_byte c.
Proof. intros c H. unfold b64_alpha, plain_byte in *. lia. Qed.

Lemma b64_enc_plain : forall bs, WriterSpec.bytes_ok bs -> plain_bytes (WriterSpec.b64_enc bs).
Proof.
  intros bs Hb. unfold plain_bytes.
  eapply Forall_impl; [exact b64_alpha_plain | exact (b64_enc_alphabet bs Hb)].
Qed.

Theorem FS_DOC_STRS_strings : forall bs, WriterSpec.bytes_ok bs -> fs_doc_strings (fs_doc (WriterSpec.b64_enc bs)).
Proof.
  intros bs Hb s Hs. rewrite fs_doc_strs_list in Hs. apply in_app_or in Hs as [Hs|Hs].
  - exact (fd_const_plain s Hs).
  - destruct Hs as [<-|[]]. exact (b64_enc_plain bs Hb).
Qed.

(* Clause (ii) in WriterSpec's escape test. [plain_not_special] as a Theorem Labs lane proved it, over FSH_Gen's plain_byte. *)
Lemma plain_not_special : forall c, plain_byte c -> WriterSpec.special c = false.
Proof.
  intros c (H32 & H34 & H92). unfold WriterSpec.special.
  apply orb_false_intro; [apply orb_false_intro|].
  - apply Z.eqb_neq. exact H34.
  - apply Z.eqb_neq. exact H92.
  - apply Z.ltb_ge. exact H32.
Qed.

Corollary FS_DOC_STRS_special : forall bs, WriterSpec.bytes_ok bs ->
  forall s, In s (jv_strs (fs_doc (WriterSpec.b64_enc bs))) -> Forall (fun c => WriterSpec.special c = false) s.
Proof.
  intros bs Hb s Hs. eapply Forall_impl; [|exact (FS_DOC_STRS_strings bs Hb s Hs)].
  exact plain_not_special.
Qed.

(* ---------------------------------------------------------------- FS_DOC_STRS *)

Theorem FS_DOC_STRS : forall bs, WriterSpec.bytes_ok bs ->
  fs_doc_values (fs_doc (WriterSpec.b64_enc bs)) /\ fs_doc_strings (fs_doc (WriterSpec.b64_enc bs)).
Proof. intros bs Hb. exact (conj (FS_DOC_STRS_values (WriterSpec.b64_enc bs)) (FS_DOC_STRS_strings bs Hb)). Qed.

(* The same document in the WRITER's form: [jv_plain] (FSH_Gen.v:146-156) over the whole tree, keys and values at any
   depth. This is the premise [jv_plain t] of a Theorem Labs lane's pj_write_spec (the writer's walk of pj_write over the
   harness document fs.c:237-248), discharged here for the document the harness builds. *)
Lemma fs_doc_jv_plain : forall bs, WriterSpec.bytes_ok bs -> jv_plain (fs_doc (WriterSpec.b64_enc bs)).
Proof.
  intros bs Hb. pose proof (FS_DOC_STRS_strings bs Hb) as H. unfold fs_doc_strings in H.
  rewrite fs_doc_strs_list in H. rewrite fs_doc_shape. unfold fd_state. cbn [jv_plain].
  repeat split; apply H; cbn; tauto.
Qed.
