(* omx-clap-core/fuzz_preset: the writer-side request bounds of the #102 harness. Nothing here is a function's proof
   (rule 24); kind: statement text.

   WHAT IS BOUNDED. #102 fuzz_preset.c:810 sets g_most = PJ_ALLOC_BOUND(size) = 256 size + 20480 (:62-63, PJ_SLOT =
   sizeof(struct pj) + sizeof(char * ) = 64) ONCE, from the input's size, and alloc.c refused(n) (:70-78) sets ran_out
   only for n <= g_most. So every allocator request of the checks that run after the parse - the writer's buffer, the
   read-back of the writer's text, the rewrite's pj_string / pj_set / pj_write / read-back - is judged against
   PJ_ALLOC_BOUND(|x|), x the input, not against the bound of the text it reads. The terms below are a Theorem Labs lane's (kit
   3438f3406f33, lib/A/PRH_FnCheck.v 37d8e4d0072e) with their bodies written out, sm for prh_jr_strtod:
     RQW t p          = rqw t p                   (WriterSpec.newcap 0 (|wdoc t p| + 1))
     RQ_pj_parse tl   = rq_read prh_jr_strtod tl  (prh_maxreq (snd (jr_run prh_jr_strtod tl [])))
     RQA_rtt t p      = rqa_rtt prh_jr_strtod t p
     RQA_crt t        = rqa_crt prh_jr_strtod t   (ck_crt_tree t = check_round_trip_c.crt_tree t: crt_tree_form)
   each by delta / beta / iota only.

   WHY THEY HOLD, t read from x (json_read sm x = Some t):
   - the reader on x: jr_esize_bound, every event's size <= 56 |x| + 448 (rq_read_bound).
   - the writer's last buffer: newcap 0 need <= max 4096 (2 need - 2) (newcap0_le), with |wdoc t false| <= 3 |x|
     (SlotSizes.wlen_false_read) and |wdoc t true| <= 56 |x| - 54 (SlotSizes.wlen_true_read). The pretty text indents
     each line 2 bytes per level, but the reader refuses past MAXD = 32 levels (the harness's JSON_DEPTH_MAX 32), so
     the indentation is at most 64 bytes a line and the text is linear in |x| (rqw_read).
   - the read-back of wdoc t p: PjRoundTrip.G9_trace makes its trace ttrace t for BOTH p, the trace of reading the
     compact text, so every size is at most 56 |wdoc t false| + 448 <= 168 |x| + 448 (rd_wdoc_esize): no whitespace
     of the pretty text reaches a request.
   - the rewrite: crt_tree t is well formed for the same sm (crt_wf_sm), its compact text is at most 36 bytes longer
     (crt_len_false), its pretty text 40 (check_round_trip_m.crt_len); pj_set's kids grow is 56 cap2 (members t) with
     2 members + 2 <= |x| (SlotSizes.s_read), pj_string's 21.
   Measured worst case (the internal file REQBOUND-WRITER.md): a 32-deep array of k zeros, |wdoc t true| = 33.5 |x|, so RQW t true
   < 67 |x| + 4096; the bound has a factor of about 3.8 to spare. The examples below pin that transliteration to the
   model. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjWriteHyp SlotSizes check_round_trip_c
  check_round_trip_m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ the terms, bodies written out *)

(* the writer's last buffer: 4096 doubled until it holds the text and its NUL (preset_file.c:460-464) *)
Definition rqw (t : jv) (p : bool) : Z := newcap 0 (Z.of_nat (length (wdoc t p)) + 1).

(* the largest single request of a granted reading of tl, in user bytes *)
Definition rq_read (sm : list Z -> Z * Z) (tl : list Z) : Z :=
  fold_right Z.max 0 (map (fun e => Z.of_nat (esize e)) (snd (jr_run sm tl []))).

Definition members (t : jv) : Z := match t with JObj ms => Z.of_nat (length ms) | _ => 0 end.
Definition cap2 (cap : Z) : Z := if cap =? 0 then 8 else 2 * cap.

(* round_trip_text (doc, p, _): the writer's buffer and the read-back (rendered()'s tx_put is the harness's own) *)
Definition rqa_rtt (sm : list Z -> Z * Z) (t : jv) (p : bool) : Z :=
  fold_right Z.max 0 [rqw t p; rq_read sm (wdoc t p)].

(* check_round_trip: both round_trip_text, pj_set's kids grow (cap = members), pj_string's strdup, the rewrite's
   writer and read-back *)
Definition rqa_crt (sm : list Z -> Z * Z) (t : jv) : Z :=
  fold_right Z.max 0
    [rqa_rtt sm t false; rqa_rtt sm t true; 56 * cap2 (members t); Z.of_nat (length check_round_trip_c.STAMP) + 1;
     rqw (check_round_trip_c.crt_tree t) true; rq_read sm (wdoc (check_round_trip_c.crt_tree t) true)].

Lemma crt_tree_form : forall t, check_round_trip_c.crt_tree t =
  match t with
  | JObj ms => JObj (pj_set_model ms [109; 111; 100; 105; 102; 105; 101; 100; 65; 116]
                       (JStr [50; 48; 50; 54; 45; 49; 48; 45; 50; 53; 84; 48; 48; 58; 48; 48; 58; 48; 48; 90]))
  | _ => t
  end.
Proof. intros t. destruct t; reflexivity. Qed.

(* ================================================================ arithmetic *)

Lemma dbl_le : forall f c need, 1 <= c -> dbl f c need <= Z.max c (2 * need - 2).
Proof.
  induction f as [|f IH]; intros c need Hc; cbn [dbl]; [lia|].
  destruct (need <=? c) eqn:E; [lia|].
  apply Z.leb_gt in E. specialize (IH (2 * c) need ltac:(lia)). lia.
Qed.

Lemma newcap0_le : forall need, newcap 0 need <= Z.max 4096 (2 * need - 2).
Proof. intros need. unfold newcap. rewrite Z.eqb_refl. apply dbl_le. lia. Qed.

Lemma maxreq_le : forall (tr : list ev) B, 0 <= B -> (forall e, In e tr -> Z.of_nat (esize e) <= B) ->
  fold_right Z.max 0 (map (fun e => Z.of_nat (esize e)) tr) <= B.
Proof.
  induction tr as [|e r IH]; intros B HB H; cbn [map fold_right]; [lia|].
  pose proof (H e (or_introl eq_refl)) as H1.
  pose proof (IH B HB (fun e' Hi => H e' (or_intror Hi))) as H2. lia.
Qed.

(* ================================================================ the reader on the input *)

Theorem rq_read_bound_56 : forall sm x, rq_read sm x <= 56 * Z.of_nat (length x) + 448.
Proof.
  intros sm x. unfold rq_read. apply maxreq_le; [lia|].
  intros e Hin. pose proof (jr_esize_bound sm x [] e Hin). lia.
Qed.

(* RQ_pj_parse x <= most and, for check_reject_clean_starved, RQ_pj_parse tb <= most *)
Theorem rq_read_bound : forall sm x, rq_read sm x <= 256 * Z.of_nat (length x) + 20480.
Proof. intros sm x. pose proof (rq_read_bound_56 sm x). lia. Qed.

(* ================================================================ the writer's buffer *)

Theorem rqw_false_read : forall sm x t, json_read sm x = Some t -> rqw t false <= Z.max 4096 (6 * Z.of_nat (length x)).
Proof.
  intros sm x t H. unfold rqw. pose proof (SlotSizes.wlen_false_read sm x t H) as W. unfold PjWriteHyp.wlen in W.
  pose proof (newcap0_le (Z.of_nat (length (wdoc t false)) + 1)). lia.
Qed.

Theorem rqw_true_read : forall sm x t, json_read sm x = Some t ->
  rqw t true <= Z.max 4096 (112 * Z.of_nat (length x) - 108).
Proof.
  intros sm x t H. unfold rqw. pose proof (SlotSizes.wlen_true_read sm x t H) as W. unfold PjWriteHyp.wlen in W.
  pose proof (newcap0_le (Z.of_nat (length (wdoc t true)) + 1)). lia.
Qed.

(* RQW t true <= most /\ RQW t false <= most (check_reject_clean_starved), and each round_trip_text's writer *)
Theorem rqw_read : forall sm x t p, json_read sm x = Some t -> rqw t p <= 256 * Z.of_nat (length x) + 20480.
Proof.
  intros sm x t [|] H; [pose proof (rqw_true_read sm x t H) | pose proof (rqw_false_read sm x t H)]; lia.
Qed.

(* ================================================================ the read-back of the writer's text *)

Theorem rd_wdoc_esize : forall sm x t p e, json_read sm x = Some t -> In e (snd (jr_run sm (wdoc t p) [])) ->
  Z.of_nat (esize e) <= 168 * Z.of_nat (length x) + 448.
Proof.
  intros sm x t p e H Hin.
  pose proof (wf_read sm x t H) as Hw.
  rewrite (G9_trace sm t Hw p), <- (G9_trace sm t Hw false) in Hin.
  pose proof (jr_esize_bound sm (wdoc t false) [] e Hin) as B.
  pose proof (SlotSizes.wlen_false_read sm x t H) as W. unfold PjWriteHyp.wlen in W. lia.
Qed.

Theorem rq_wdoc_read : forall sm x t p, json_read sm x = Some t ->
  rq_read sm (wdoc t p) <= 168 * Z.of_nat (length x) + 448.
Proof.
  intros sm x t p H. unfold rq_read. apply maxreq_le; [lia|].
  intros e Hin. exact (rd_wdoc_esize sm x t p e H Hin).
Qed.

(* RQA_rtt t p <= most *)
Theorem rqa_rtt_bound : forall sm x t p, json_read sm x = Some t ->
  rqa_rtt sm t p <= 256 * Z.of_nat (length x) + 20480.
Proof.
  intros sm x t p H. unfold rqa_rtt. cbn [fold_right].
  pose proof (rqw_read sm x t p H). pose proof (rq_wdoc_read sm x t p H). lia.
Qed.

(* ================================================================ the rewrite *)

Lemma crt_wf_sm : forall sm x t, json_read sm x = Some t -> PjRoundTrip.pj_wf sm (check_round_trip_c.crt_tree t).
Proof.
  intros sm x t H. destruct t as [| | | txt bits | s | items | ms]; cbn [check_round_trip_c.crt_tree];
    try (eapply wf_read; exact H).
  destruct (read_json sm x (JObj ms) H) as (_ & Hd & _).
  apply wf_set.
  - eapply wf_read. exact H.
  - apply wf_string. unfold check_round_trip_c.STAMP. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil.
  - unfold check_round_trip_c.MOD_AT. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil.
  - pose proof (check_round_trip_m.crtm_set_depth ms check_round_trip_c.MOD_AT (JStr check_round_trip_c.STAMP)) as D.
    change (depth (JStr check_round_trip_c.STAMP)) with 0%nat in D. unfold MAXD in *. lia.
Qed.

Lemma wdoc_false_len : forall u, length (wdoc u false) = length (concat (wvpieces u false 0)).
Proof. intros u. unfold wdoc, wdpieces. cbv beta iota. rewrite app_nil_r. reflexivity. Qed.

Lemma obj_len_false : forall ms, length (concat (wvpieces (JObj ms) false 0)) =
  (2 + length (concat (wgo_obj false 0 0 ms)))%nat.
Proof.
  intros ms. rewrite wv_obj, concat_cons, !concat_app, !length_app.
  destruct ms as [|m r]; cbn [length concat app wind]; lia.
Qed.

Lemma crt_len_false : forall t,
  (length (wdoc (check_round_trip_c.crt_tree t) false) <= length (wdoc t false) + 36)%nat.
Proof.
  intros t. destruct t as [| | | txt bits | s | items | ms]; cbn [check_round_trip_c.crt_tree]; try lia.
  rewrite !wdoc_false_len, !obj_len_false.
  pose proof (check_round_trip_m.crtm_wgo_set false 0 check_round_trip_c.MOD_AT (JStr check_round_trip_c.STAMP)
    ms 0%nat) as H.
  assert (L1 : length (concat (wind false (0 + 1))) = 0%nat) by reflexivity.
  assert (L2 : length (concat (spieces check_round_trip_c.MOD_AT)) = 12%nat) by reflexivity.
  assert (L3 : length (wsep false) = 1%nat) by reflexivity.
  assert (L4 : length (concat (wvpieces (JStr check_round_trip_c.STAMP) false (0 + 1))) = 22%nat) by reflexivity.
  rewrite L1, L2, L3, L4, check_round_trip_m.crtm_wcomma_len in H.
  destruct (Nat.eqb (0 + length ms) 0); lia.
Qed.

Theorem rd_crt_esize : forall sm x t e, json_read sm x = Some t ->
  In e (snd (jr_run sm (wdoc (check_round_trip_c.crt_tree t) true) [])) ->
  Z.of_nat (esize e) <= 168 * Z.of_nat (length x) + 2464.
Proof.
  intros sm x t e H Hin.
  pose proof (crt_wf_sm sm x t H) as Hw.
  rewrite (G9_trace sm _ Hw true), <- (G9_trace sm _ Hw false) in Hin.
  pose proof (jr_esize_bound sm _ [] e Hin) as B.
  pose proof (crt_len_false t) as C.
  pose proof (SlotSizes.wlen_false_read sm x t H) as W. unfold PjWriteHyp.wlen in W. lia.
Qed.

Theorem rq_crt_read : forall sm x t, json_read sm x = Some t ->
  rq_read sm (wdoc (check_round_trip_c.crt_tree t) true) <= 168 * Z.of_nat (length x) + 2464.
Proof.
  intros sm x t H. unfold rq_read. apply maxreq_le; [lia|].
  intros e Hin. exact (rd_crt_esize sm x t e H Hin).
Qed.

Theorem rqw_crt_read : forall sm x t, json_read sm x = Some t ->
  rqw (check_round_trip_c.crt_tree t) true <= Z.max 4096 (112 * Z.of_nat (length x) - 28).
Proof.
  intros sm x t H. unfold rqw.
  pose proof (check_round_trip_m.crt_len t) as C.
  pose proof (SlotSizes.wlen_true_read sm x t H) as W. unfold PjWriteHyp.wlen in W.
  pose proof (newcap0_le (Z.of_nat (length (wdoc (check_round_trip_c.crt_tree t) true)) + 1)). lia.
Qed.

Theorem set_grow_read : forall sm x t, json_read sm x = Some t ->
  56 * cap2 (members t) <= 56 * Z.of_nat (length x) + 448.
Proof.
  intros sm x t H. unfold cap2, members.
  destruct t as [| | | txt bits | s | items | ms]; try (cbn; lia).
  pose proof (SlotSizes.s_read sm x (JObj ms) H) as S.
  destruct (SlotSizes.szok_obj_inv _ _ S) as (Hn & _ & _).
  destruct (Z.of_nat (length ms) =? 0); lia.
Qed.

(* RQA_crt t <= most *)
Theorem rqa_crt_bound : forall sm x t, json_read sm x = Some t ->
  rqa_crt sm t <= 256 * Z.of_nat (length x) + 20480.
Proof.
  intros sm x t H. unfold rqa_crt. cbn [fold_right].
  pose proof (rqa_rtt_bound sm x t false H). pose proof (rqa_rtt_bound sm x t true H).
  pose proof (set_grow_read sm x t H). pose proof (rqw_crt_read sm x t H). pose proof (rq_crt_read sm x t H).
  change (Z.of_nat (length check_round_trip_c.STAMP)) with 20. lia.
Qed.

(* ================================================================ the measurement, pinned to the model *)

(* a strtod model that reads every text whole to +0.0 *)
Definition sm0 (txt : list Z) : Z * Z := (Z.of_nat (length txt), 0).

(* d nested arrays: the reader takes 32 (MAXD) and refuses 33 or more; refused, each of the 32 levels it opened asked
   56 * 8 = 448 for its kids. Row: |x|, read?, |wdoc t true|, rqw t true, rq_read sm0 x. *)
Definition nest_x (d : nat) : list Z := repeat 91 d ++ repeat 93 d.
Definition nest_row (d : nat) : Z * Z * Z * Z * Z :=
  let x := nest_x d in
  match json_read sm0 x with
  | Some t => (Z.of_nat (length x), 1, Z.of_nat (length (wdoc t true)), rqw t true, rq_read sm0 x)
  | None => (Z.of_nat (length x), 0, 0, 0, rq_read sm0 x)
  end.

Example nest_rows : map nest_row [1; 8; 32; 33; 64; 256]%nat =
  [(2, 1, 3, 4096, 0); (16, 1, 129, 4096, 448); (64, 1, 2049, 4096, 448);
   (66, 0, 0, 0, 448); (128, 0, 0, 0, 448); (512, 0, 0, 0, 448)].
Proof. vm_compute. reflexivity. Qed.

(* the worst family: 32 nested arrays, the deepest holding 100 zeros (each "0," of x is a 67-byte pretty line).
   Row: |x|, |wdoc t false|, |wdoc t true|, the writer's capacities (compact, pretty), rendered()'s last capacity
   (pretty), rq_read of the pretty text and of x. Against PJ_ALLOC_BOUND(263) = 87808. *)
Definition x_deep : list Z := repeat 91 32 ++ concat (repeat [48; 44] 99) ++ [48] ++ repeat 93 32.

Example deep_row :
  match json_read sm0 x_deep with
  | Some t => (Z.of_nat (length x_deep), Z.of_nat (length (wdoc t false)), Z.of_nat (length (wdoc t true)),
               PresetReqAt.wcaps t false, PresetReqAt.wcaps t true, last (PresetReqAt.rcaps t true) 0,
               rq_read sm0 (wdoc t true), rq_read sm0 x_deep)
  | None => (0, 0, 0, [], [], 0, 0, 0)
  end = (263, 263, 8811, [4096], [4096; 8192; 16384], 16388, 7168, 7168).
Proof. vm_compute. reflexivity. Qed.

(* an object of 100 members "":0, and its rewrite (modifiedAt appended): |x|, |wdoc t true|, rqw t true,
   rendered()'s last capacity (pretty), rq_read of the pretty text, |wdoc (crt_tree t) true|, its rqw and read-back,
   pj_set's kids grow. Against PJ_ALLOC_BOUND(501) = 148736. *)
Definition x_obj : list Z := [123] ++ concat (repeat [34; 34; 58; 48; 44] 99) ++ [34; 34; 58; 48; 125].

Example obj_row :
  match json_read sm0 x_obj with
  | Some t => (Z.of_nat (length x_obj), Z.of_nat (length (wdoc t true)), rqw t true,
               last (PresetReqAt.rcaps t true) 0, rq_read sm0 (wdoc t true),
               Z.of_nat (length (wdoc (check_round_trip_c.crt_tree t) true)), rqw (check_round_trip_c.crt_tree t) true,
               rq_read sm0 (wdoc (check_round_trip_c.crt_tree t) true), 56 * cap2 (members t))
  | None => (0, 0, 0, 0, 0, 0, 0, 0, 0)
  end = (501, 903, 4096, 1054, 7168, 943, 4096, 7168, 11200).
Proof. vm_compute. reflexivity. Qed.
