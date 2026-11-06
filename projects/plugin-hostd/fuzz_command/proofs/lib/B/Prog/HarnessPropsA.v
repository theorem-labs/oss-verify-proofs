(* The harness facts of one message (lib/Prog/HarnessProps.v:10-37), for any value of atoi.

   The released harness_props_holds (lib/Prog/HarnessPropsProof.v:1479-1485) is stated over the plain image's run
   vr_run, with musl's atoi value atoi_val (lib/Prog/verbs_receive_c.v:22-23), and the harness's own checks read that
   value too: the `#k` words of check_words (want, lib/Prog/check_words_c.v:51-58), the chain list
   (lib/Prog/check_words_chain_c.v:14-20) and the reply code (reply_code). The ASan image calls the atoi wrapper
   instead (atoi_a, lib/B/Prog/sup_reply_code_c.v:61), whose value differs from musl's for numbers of 19 or more
   digits, so the recorder state of such a message differs between the images.

   This file states the same facts with atoi a parameter: rcode_at (the reply code read with it), want_at,
   chain_items_at, chain_list_at, call_words_ok_at, words_prop_at, answer_ok_at, reply_ok_at, rt_ok_at, msg_props_at
   and harness_props_at, each the plain definition with atoi for atoi_val and rc for reply_code, and proves
   harness_props_at atoi (rcode_at atoi) for every atoi with the five properties the plain proof reads of atoi_val:
   it is an int, it reads a number_m word as its value, it reads back the "%d" text of
   a value in [0, 2^31), and the reply codes of the declared refusals and of the shapes are those of the plain
   image. The proof is the plain one; every lemma of it that reads no atoi value is used by Require. *)
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Strings.String Strings.Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun CType.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandModel RecFacts RecModel
  sup_reply_code_c rec_code_declared_c rec_shape_of_c check_reply_answer_c check_reply_c check_arity_c check_words_c
  check_words_add_c check_words_chain_c check_words_pin_set_c printf_facts_c atoi_c
  check_round_trip_c verbs_receive_c HarnessProps HarnessPropsProof.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import HarnessArgs HarnessPropsAPlan.
Import ListNotations.
Open Scope Z_scope.

(** * The statement *)

(* the plain reply_code (lib/Prog/sup_reply_code_c.v:33-36) with atoi: the "resp " prefix, then the number after it *)
Definition rcode_at (atoi : list byte -> Z) (x : list byte) : Z :=
  if list_eq_dec Z.eq_dec (map bv_unsigned (firstn 5 x)) [114; 101; 115; 112; 32]
  then atoi (skipn 5 x)
  else -999.

(* the plain want (lib/Prog/check_words_c.v:51-58): a `#k` item is the "%d" text of atoi of word k *)
Definition want_at (atoi : list byte -> Z) (r : Z) (ws : list (list byte)) (i : witem) : option (list byte) :=
  match i with
  | IStar => None
  | ILine => Some (join_sp ws)
  | IOpt k => if k <? r then Some (nth (Z.to_nat k) ws []) else None
  | INum k => if k <? r then Some (pf_bytes (pf_dec (atoi (nth (Z.to_nat k) ws [])))) else Some []
  | IWord k => if k <? r then Some (nth (Z.to_nat k) ws []) else Some []
  end.

(* the plain chain_items and chain_list (lib/Prog/check_words_chain_c.v:14-20) *)
Fixpoint chain_items_at (atoi : list byte -> Z) (k : nat) (n : nat) (ws : list (list byte)) : list Z :=
  match n with
  | O => []
  | S n' => (if Nat.eqb k 2 then [] else [32]) ++ pf_dec (atoi (nth k ws [])) ++ chain_items_at atoi (S k) n' ws
  end.

Definition chain_list_at (atoi : list byte -> Z) (r : Z) (ws : list (list byte)) : list Z :=
  chain_items_at atoi 2 (Z.to_nat (r - 2)) ws.

(* the plain call_words_ok and words_prop (lib/Prog/check_words_c.v:60-72) *)
Definition call_words_ok_at (atoi : list byte -> Z) (r : Z) (ws : list (list byte)) (c : rcall) : Prop :=
  (forall a i x, nth_error (snd c) a = Some x -> nth_error (call_items (fst c)) a = Some i ->
     forall y, want_at atoi r ws i = Some y -> x = y) /\
  (fst c = 0 -> length (snd c) = 4%nat /\
     nth 2 (snd c) [] = add_placement r (nth 3 ws []) /\
     nth 3 (snd c) [] = add_client r (nth 3 ws []) (nth 4 ws [])) /\
  (fst c = 17 -> length (snd c) = 3%nat /\
     nth 1 (snd c) [] = pf_bytes (pf_dec (r - 2)) /\ nth 2 (snd c) [] = pf_bytes (chain_list_at atoi r ws)) /\
  (fst c = 20 -> length (snd c) = 4%nat /\ nth 3 (snd c) [] = pin_verdict r (nth 4 ws [])).

Definition words_prop_at (atoi : list byte -> Z) (R : rstate) (ws : list (list byte)) : Prop :=
  let r := Z.min (Z.of_nat (length ws)) 64 in
  Forall (call_words_ok_at atoi r ws) (r_calls R).

(* the plain answer_ok_m (lib/Prog/HarnessProps.v:12-16) with the reply code rc *)
Definition answer_ok_at (rc : list byte -> Z) (ans : option (list byte)) (xr : list byte) (n : Z) (w0 : list byte)
  : Prop :=
  match ans with
  | Some xa => xr = xa
  | None => rc xr < 0 \/ (n = 1 /\ w0 = S_QUIT)
  end.

(* the plain reply_ok (lib/Prog/check_reply_c.v:29-32) with the reply code rc *)
Definition reply_ok_at (rc : list byte -> Z) (n : Z) (w0 xr : list byte) : Prop :=
  (rc xr < 0 -> declared (rc xr) = true /\ xr = refusal_text (rc xr)) /\
  (0 <= rc xr ->
     reply_matches (img_str (shape_addr n w0)) xr = true \/ reply_matches (img_str SHAPE_LIT) xr = true).

(* the plain rt_ok (lib/Prog/check_round_trip_c.v:26-30) over the run with atoi and rc *)
Definition rt_ok_at (atoi rc : list byte -> Z) (R : rstate) (q sb hb : Z) (ws : list (list byte)) : Prop :=
  ws <> [] -> acted_m R q = true ->
  let '(R2, _, quit2) := VerbsRun.run_receive atoi rc (rec_clear (set_host (set_state R sb) hb)) (join_sp ws) in
  r_calls R2 = r_calls R /\ r_reply R2 = r_reply R /\ (if quit2 then 1 else 0) = q /\
  r_state R2 = r_state R /\ r_host R2 = r_host R.

(* the plain msg_props and harness_props (lib/Prog/HarnessProps.v:18-37) over the run with atoi and rc *)
Definition msg_props_at (atoi rc : list byte -> Z) (R0 : rstate) (D : list byte) : Prop :=
  let ws := hwords D in
  let n := Z.of_nat (length ws) in
  let w0 := nth 0 ws [] in
  let '(R1, x, quit) := VerbsRun.run_receive atoi rc (rec_clear R0) D in
  let q := if quit then 1 else 0 in
  r_nreplies R1 = 1 /\ r_reply R1 = Some (x ++ [Z_to_bv 8 0]) /\ no0 x /\ (Z.of_nat (length x) <= 28)%Z /\
  answer_ok_at rc (r_answer R1) x n w0 /\
  reply_ok_at rc n w0 x /\
  arity_ok n w0 q (Z.of_nat (length (r_calls R1))) (fst (nth 0 (r_calls R1) (0, []))) /\
  words_prop_at atoi R1 ws /\
  (rc x < 0 -> r_state R1 = r_state R0 /\ quit = false) /\
  rt_ok_at atoi rc R1 q (r_state R0) (r_host R0) ws.

Definition harness_props_at (atoi rc : list byte -> Z) : Prop :=
  forall (R0 : rstate) (D : list byte),
    (length D <= 8192)%nat ->
    0 <= r_state R0 < 2 ^ 64 -> 0 <= r_host R0 < 2 ^ 64 ->
    (r_refuse R0 <> 0 -> declared (r_code R0) = true) ->
    msg_props_at atoi rc R0 D.

(* at musl's atoi value the word facts are the plain ones *)
Lemma chain_items_at_plain : forall n k ws, chain_items_at atoi_val k n ws = chain_items k n ws.
Proof.
  induction n as [|n IH]; intros k ws; [reflexivity|]. cbn [chain_items_at chain_items]. rewrite IH. reflexivity.
Qed.

Lemma chain_list_at_plain : forall r ws, chain_list_at atoi_val r ws = chain_list r ws.
Proof. intros r ws. apply chain_items_at_plain. Qed.

Lemma call_words_ok_at_plain : forall r ws c, call_words_ok_at atoi_val r ws c <-> call_words_ok r ws c.
Proof. intros r ws c. unfold call_words_ok_at, call_words_ok. rewrite chain_list_at_plain. reflexivity. Qed.

Lemma words_prop_at_plain : forall R ws, words_prop_at atoi_val R ws <-> words_prop R ws.
Proof.
  intros R ws. unfold words_prop_at, words_prop.
  split; apply Forall_impl; intros c; apply call_words_ok_at_plain.
Qed.

(** * The proof, for any atoi with the five properties *)

Section any_atoi.
Variable atoi : list byte -> Z.
(* the value is an int (plain atoi_range, HarnessPropsProof.v:260) *)
Hypothesis A_range : forall s, -2^31 <= atoi s < 2^31.
(* a word number_m accepts reads as its value (plain number_atoi, :291) *)
Hypothesis A_number : forall w v, Verbs.number_m w = Some v -> atoi w = v.
(* the "%d" text of a value in [0, 2^31) reads back as the value (plain atoi_val_dec, :464) *)
Hypothesis A_dec : forall v, 0 <= v < 2^31 -> atoi (dec v) = v.
(* the declared refusals' replies read back as their codes (the first half of plain decl_all, :330-333) *)
Hypothesis A_decl : forallb (fun c => rcode_at atoi (resp c) =? c) rec_codes = true.
(* the shapes' instances have a code of at least 0 (the first conjunct of plain sh_all, :381-385) *)
Hypothesis A_shapes : forallb (fun s => 0 <=? rcode_at atoi (inst s)) shape_set = true.

Local Notation RC := (rcode_at atoi).

(** ** Numbers and replies *)

Lemma dec_atoi_at : forall s, pf_bytes (pf_dec (atoi s)) = dec (atoi s).
Proof. intros s. apply dec_pf. apply A_range. Qed.

Lemma numbers_atoi_at : forall l ids, Verbs.numbers_m l = Some ids -> map atoi l = ids.
Proof.
  induction l as [|w l IH]; intros ids H; cbn [Verbs.numbers_m] in H.
  - injection H as <-. reflexivity.
  - destruct (Verbs.number_m w) as [v|] eqn:E1; [|discriminate].
    destruct (Verbs.numbers_m l) as [vs|] eqn:E2; [|discriminate]. injection H as <-.
    cbn [map]. rewrite (A_number w v E1), (IH vs eq_refl). reflexivity.
Qed.

Lemma resp_declared_at : forall c, declared c = true -> RC (resp c) = c /\ refusal_text c = resp c.
Proof.
  intros c H. split; [|exact (proj2 (resp_declared c H))].
  pose proof A_decl as A. rewrite forallb_forall in A. specialize (A c (declared_in c H)).
  apply Z.eqb_eq in A. exact A.
Qed.

Lemma reply_ok_neg_at : forall n w0 c, declared c = true -> reply_ok_at RC n w0 (resp c).
Proof.
  intros n w0 c H. destruct (resp_declared_at c H) as [E1 E2]. pose proof (declared_range c H) as Rg.
  unfold reply_ok_at. rewrite E1. split; [intros _; split; [exact H|symmetry; exact E2]|intros; lia].
Qed.

Lemma resp_declared_facts_at : forall c, declared c = true ->
  no0 (resp c) /\ Z.of_nat (length (resp c)) <= 28 /\ RC (resp c) = c /\ c < 0.
Proof.
  intros c H. destruct (resp_declared_facts c H) as (F1 & F2 & _ & F4).
  split; [exact F1|split; [exact F2|split; [exact (proj1 (resp_declared_at c H))|exact F4]]].
Qed.

Lemma shape_rc_at : forall s, In s shape_set -> 0 <= RC (inst s).
Proof.
  intros s Hs. pose proof A_shapes as A. rewrite forallb_forall in A. specialize (A s Hs).
  apply Z.leb_le in A. exact A.
Qed.

Lemma reply_ok_shape_at : forall n w, n <> 0 -> reply_ok_at RC n w (inst (shape_of w)).
Proof.
  intros n w Hn. destruct (shape_inst w) as (_ & M & _). pose proof (shape_rc_at _ (shape_of_in w)) as R.
  unfold reply_ok_at. split; [intros; lia|].
  intros _. left. unfold shape_addr. rewrite (proj2 (Z.eqb_neq n 0) Hn). rewrite img_shape. exact M.
Qed.

Lemma rc_resp : forall v, RC (resp v) = atoi (dec v).
Proof.
  intros v. unfold rcode_at.
  destruct (list_eq_dec Z.eq_dec (map bv_unsigned (firstn 5 (resp v))) [114; 101; 115; 112; 32]) as [_|NE].
  - reflexivity.
  - exfalso. apply NE. reflexivity.
Qed.

Lemma reply_code_pos_at : forall v, 0 <= v < 2^31 -> RC (resp v) = v.
Proof. intros v Hv. rewrite rc_resp. apply A_dec. exact Hv. Qed.

Lemma resp0_facts_at : RC (resp 0) = 0 /\ no0 (resp 0) /\ Z.of_nat (length (resp 0)) <= 28.
Proof. split; [apply reply_code_pos_at; lia | exact (proj2 resp0_facts)]. Qed.

Lemma reply_ok_resp0_at : forall n w, reply_ok_at RC n w (resp 0).
Proof.
  intros n w. unfold reply_ok_at. rewrite (proj1 resp0_facts_at). split; [intros; lia|].
  intros _. right. rewrite img_lit. vm_compute. reflexivity.
Qed.

Lemma resp_add_at : forall id, 0 <= id < 10000 ->
  RC (resp id) = id /\ reply_matches (shape_of Verbs.Lit.verb_add) (resp id) = true.
Proof. intros id H. split; [apply reply_code_pos_at; lia | apply reply_matches_add; lia]. Qed.

Lemma reply_ok_add_at : forall n id, n <> 0 -> 0 <= id < 10000 -> reply_ok_at RC n Verbs.Lit.verb_add (resp id).
Proof.
  intros n id Hn H. destruct (resp_add_at id H) as [E M]. unfold reply_ok_at. rewrite E. split; [intros; lia|].
  intros _. left. unfold shape_addr. rewrite (proj2 (Z.eqb_neq n 0) Hn). rewrite img_shape. exact M.
Qed.

(** ** The words check *)

Fixpoint items_ok_at (r : Z) (ws : list (list byte)) (A : list (list byte)) (its : list witem) : Prop :=
  match A, its with
  | x :: A', i :: its' =>
      (match want_at atoi r ws i with Some y => x = y | None => True end) /\ items_ok_at r ws A' its'
  | _, _ => True
  end.

Lemma items_ok_nth_at : forall r ws A its, items_ok_at r ws A its ->
  forall a x i y, nth_error A a = Some x -> nth_error its a = Some i -> want_at atoi r ws i = Some y -> x = y.
Proof.
  intros r ws A; induction A as [|x0 A IH]; intros its H a x i y Hx Hi Hy; [destruct a; discriminate|].
  destruct its as [|i0 its]; [destruct a; discriminate|]. destruct H as [H0 H].
  destruct a as [|a]; cbn in Hx, Hi.
  - injection Hx as <-. injection Hi as <-. rewrite Hy in H0. exact H0.
  - exact (IH its H a x i y Hx Hi Hy).
Qed.

Lemma cwo_intro_at : forall r ws fn A, items_ok_at r ws A (call_items fn) ->
  (fn = 0 -> length A = 4%nat /\ nth 2 A [] = add_placement r (nth 3 ws []) /\
     nth 3 A [] = add_client r (nth 3 ws []) (nth 4 ws [])) ->
  (fn = 17 -> length A = 3%nat /\ nth 1 A [] = pf_bytes (pf_dec (r - 2)) /\
     nth 2 A [] = pf_bytes (chain_list_at atoi r ws)) ->
  (fn = 20 -> length A = 4%nat /\ nth 3 A [] = pin_verdict r (nth 4 ws [])) ->
  call_words_ok_at atoi r ws (fn, A).
Proof.
  intros r ws fn A H H0 H17 H20. unfold call_words_ok_at.
  split; [|split; [exact H0|split; [exact H17|exact H20]]].
  cbn [fst snd]. intros a i x Hx Hi y Hy. exact (items_ok_nth_at r ws A (call_items fn) H a x i y Hx Hi Hy).
Qed.

(** ** Running one message *)

Arguments rcode_at : simpl never.
Arguments reply_ok_at : simpl never.
Arguments words_prop_at : simpl never.
Arguments call_words_ok_at : simpl never.

Definition run_out_at (R0 : rstate) (st : Verbs.step) (af : option (Z * list byte)) : rstate * list byte * bool :=
  let '(R1, x, q) := VerbsRun.run_step RC (rec_clear R0) st in (fin R1 x af, x, q).

Lemma vr_run_out_at : forall R0 D, VerbsRun.run_receive atoi RC (rec_clear R0) D =
  run_out_at R0 (fst (Verbs.receive atoi D)) (snd (Verbs.receive atoi D)).
Proof.
  intros R0 D. unfold VerbsRun.run_receive, run_out_at.
  destruct (Verbs.receive atoi D) as [st af]. cbn [fst snd].
  destruct (VerbsRun.run_step RC (rec_clear R0) st) as [[R1 x] q]. cbv beta iota zeta.
  rewrite ss_fst. reflexivity.
Qed.

Definition P4_at (R0 : rstate) (ws : list (list byte)) (R1 : rstate) (x : list byte) (quit : bool) : Prop :=
  r_nreplies R1 = 1 /\ r_reply R1 = Some (x ++ [Z_to_bv 8 0]) /\ no0 x /\ Z.of_nat (length x) <= 28 /\
  answer_ok_at RC (r_answer R1) x (Z.of_nat (length ws)) (nth 0 ws []) /\
  reply_ok_at RC (Z.of_nat (length ws)) (nth 0 ws []) x /\
  arity_ok (Z.of_nat (length ws)) (nth 0 ws []) (if quit then 1 else 0) (Z.of_nat (length (r_calls R1)))
    (fst (nth 0 (r_calls R1) (0, []))) /\
  words_prop_at atoi R1 ws /\
  (RC x < 0 -> r_state R1 = r_state R0 /\ quit = false).

Arguments P4_at : simpl never.

Lemma P4_intro_at : forall (R0 : rstate) (ws : list (list byte)) (R1 : rstate) (x : list byte) (q : bool)
    (af : option (Z * list byte)),
  (length (r_calls R1) < 16)%nat -> r_nreplies R1 = 0 -> no0 x -> Z.of_nat (length x) <= 28 ->
  answer_ok_at RC (r_answer R1) x (Z.of_nat (length ws)) (nth 0 ws []) ->
  reply_ok_at RC (Z.of_nat (length ws)) (nth 0 ws []) x ->
  arity_ok (Z.of_nat (length ws)) (nth 0 ws []) (if q then 1 else 0) (Z.of_nat (length (r_calls R1 ++ af_calls af)))
    (fst (nth 0 (r_calls R1 ++ af_calls af) (0, []))) ->
  Forall (call_words_ok_at atoi (Z.min (Z.of_nat (length ws)) 64) ws) (r_calls R1 ++ af_calls af) ->
  (RC x < 0 -> r_state R1 = r_state R0 /\ q = false) ->
  P4_at R0 ws (fin R1 x af) x q.
Proof.
  intros R0 ws R1 x q af L N Z0 LX A RP AR W RF.
  assert (C : r_calls (fin R1 x af) = r_calls R1 ++ af_calls af).
  { unfold fin. destruct af as [[i v]|]; [|cbn; rewrite app_nil_r; reflexivity].
    unfold sup_after_reply_m. rewrite rec_record_calls by (cbn; exact L). reflexivity. }
  assert (F : r_nreplies (fin R1 x af) = r_nreplies R1 + 1 /\ r_reply (fin R1 x af) = Some (x ++ [Z_to_bv 8 0]) /\
              r_answer (fin R1 x af) = r_answer R1 /\ r_state (fin R1 x af) = r_state R1).
  { unfold fin. destruct af as [[i v]|]; [unfold sup_after_reply_m, rec_record; destruct (Nat.ltb _ 16)|];
      cbn; repeat split. }
  destruct F as (F1 & F2 & F3 & F4).
  unfold P4_at, words_prop_at. cbv zeta. rewrite C, F1, F2, F3, F4, N.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Z0|]. split; [exact LX|].
  split; [exact A|]. split; [exact RP|]. split; [exact AR|]. split; [exact W|]. exact RF.
Qed.

Lemma shape_set_inst_at : forall s, In s shape_set ->
  0 <= RC (inst s) /\ no0 (inst s) /\ Z.of_nat (length (inst s)) <= 28.
Proof.
  intros s Hs. destruct (shape_set_inst s Hs) as (_ & S2 & S3).
  split; [exact (shape_rc_at s Hs) | split; assumption].
Qed.

Lemma P4_stub_at : forall R0 ws c af fn A shape changes,
  VerbsRun.run_call (rec_clear R0) c = rec_stub (rec_clear R0) fn A shape changes ->
  (r_refuse R0 <> 0 -> declared (r_code R0) = true) ->
  In shape shape_set ->
  reply_ok_at RC (Z.of_nat (length ws)) (nth 0 ws []) (inst shape) ->
  arity_ok (Z.of_nat (length ws)) (nth 0 ws []) 0 (Z.of_nat (S (length (af_calls af)))) fn ->
  Forall (call_words_ok_at atoi (Z.min (Z.of_nat (length ws)) 64) ws) ((fn, A) :: af_calls af) ->
  let '(R1, x, q) := run_out_at R0 (Verbs.SCall c) af in P4_at R0 ws R1 x q.
Proof.
  intros R0 ws c af fn A shape changes Hc Hd Hs Hr Ha Hw.
  destruct (shape_set_inst_at shape Hs) as (S1 & S2 & S3).
  unfold run_out_at. cbn [VerbsRun.run_step]. rewrite Hc. unfold rec_stub, rec_answer, hand_back. cbn.
  destruct (r_refuse R0 =? 0) eqn:Hr0.
  - destruct changes; cbn; apply P4_intro_at; cbn;
      first [lia | reflexivity | exact S2 | exact S3 | exact Hr | exact Ha | exact Hw | intros ?; exfalso; lia].
  - pose proof (decl_of R0 Hd Hr0) as Dc. destruct (resp_declared_facts_at _ Dc) as (D1 & D2 & D3 & D4).
    cbn. apply P4_intro_at; cbn;
      first [lia | reflexivity | exact D1 | exact D2 | (apply reply_ok_neg_at; exact Dc) | exact Ha | exact Hw
            | (intros _; split; reflexivity)].
Qed.

Lemma P4_rej_at : forall R0 ws, let '(R1, x, q) := run_out_at R0 Verbs.reject None in P4_at R0 ws R1 x q.
Proof.
  intros R0 ws. assert (D : declared (-902) = true) by reflexivity.
  destruct (resp_declared_facts_at _ D) as (D1 & D2 & D3 & D4).
  unfold run_out_at, Verbs.reject, Verbs.err_invalid_operation. cbn. apply P4_intro_at; cbn.
  - lia.
  - reflexivity.
  - exact D1.
  - exact D2.
  - left. rewrite D3. lia.
  - apply reply_ok_neg_at. exact D.
  - unfold arity_ok. right. left. split; reflexivity.
  - constructor.
  - intros _. split; reflexivity.
Qed.

Lemma P4_quit_at : forall R0,
  let '(R1, x, q) := run_out_at R0 Verbs.SQuit None in P4_at R0 [Verbs.Lit.verb_quit] R1 x q.
Proof.
  intros R0. destruct resp0_facts_at as (Q1 & Q2 & Q3).
  unfold run_out_at. cbn. apply P4_intro_at; cbn.
  - lia.
  - reflexivity.
  - exact Q2.
  - exact Q3.
  - right. split; [reflexivity|]. apply bl_eqb_eq. vm_compute. reflexivity.
  - apply reply_ok_resp0_at.
  - apply arity_of_b. vm_compute. reflexivity.
  - constructor.
  - intros H. rewrite Q1 in H. lia.
Qed.

Lemma P4_add_at : forall R0 ws u i p q,
  (r_refuse R0 <> 0 -> declared (r_code R0) = true) ->
  Z.of_nat (length ws) <> 0 -> nth 0 ws [] = Verbs.Lit.verb_add ->
  arity_ok (Z.of_nat (length ws)) Verbs.Lit.verb_add 0 1 0 ->
  arity_ok (Z.of_nat (length ws)) Verbs.Lit.verb_add 0 2 0 ->
  call_words_ok_at atoi (Z.min (Z.of_nat (length ws)) 64) ws (0, [u; dec (atoi i); darg p S_DASH; darg q S_DASH]) ->
  call_words_ok_at atoi (Z.min (Z.of_nat (length ws)) 64) ws (22, [u]) ->
  let '(R1, x, q') := run_out_at R0 (Verbs.SAdd u (atoi i) p q) None in P4_at R0 ws R1 x q'.
Proof.
  intros R0 ws u i p q Hd Hn H0 A1 A2 W1 W2.
  unfold run_out_at. cbn [VerbsRun.run_step]. unfold sup_add_m, hand_back. cbn.
  destruct ((atoi i <? 0) || (10000 <=? atoi i)) eqn:Hid.
  - assert (D : declared (-1) = true) by reflexivity.
    destruct (resp_declared_facts_at _ D) as (D1 & D2 & D3 & D4).
    cbn. rewrite D3. cbn. apply P4_intro_at; cbn.
    + lia.
    + reflexivity.
    + exact D1.
    + exact D2.
    + reflexivity.
    + apply reply_ok_neg_at. exact D.
    + rewrite H0. exact A1.
    + apply Forall_cons; [exact W1|apply Forall_nil].
    + intros _. split; reflexivity.
  - apply orb_false_iff in Hid as [Hid1 Hid2]. apply Z.ltb_ge in Hid1. apply Z.leb_gt in Hid2.
    destruct (r_refuse R0 =? 0) eqn:Hr0; cbn.
    + destruct (resp_add_at (atoi i) ltac:(lia)) as [E M]. rewrite E.
      replace (0 <=? atoi i) with true by (symmetry; apply Z.leb_le; lia). cbn.
      destruct (resp_add_facts (atoi i) ltac:(lia)) as [F1 F2].
      apply P4_intro_at; cbn.
      * lia.
      * reflexivity.
      * exact F1.
      * exact F2.
      * reflexivity.
      * rewrite H0. apply reply_ok_add_at; [exact Hn | lia].
      * rewrite H0. exact A2.
      * apply Forall_cons; [exact W1|apply Forall_cons; [exact W2|apply Forall_nil]].
      * rewrite E. intros H; exfalso; lia.
    + pose proof (decl_of R0 Hd Hr0) as Dc. destruct (resp_declared_facts_at _ Dc) as (D1 & D2 & D3 & D4).
      rewrite D3. replace (0 <=? r_code R0) with false by (symmetry; apply Z.leb_gt; lia). cbn.
      apply P4_intro_at; cbn.
      * lia.
      * reflexivity.
      * exact D1.
      * exact D2.
      * reflexivity.
      * apply reply_ok_neg_at. exact Dc.
      * rewrite H0. exact A1.
      * apply Forall_cons; [exact W1|apply Forall_nil].
      * intros _. split; reflexivity.
Qed.

Lemma cwo_forget_at : forall r ws A, call_words_ok_at atoi r ws (REC_LV2_REFUSALS_FORGET, A).
Proof.
  intros r ws A. apply cwo_intro_at; [|intros E; discriminate E ..].
  change (call_items REC_LV2_REFUSALS_FORGET) with [IStar].
  destruct A as [|x [|y A]]; cbn; repeat split.
Qed.

Lemma P4_pins_at : forall R0 ws st fn A,
  VerbsRun.run_step RC (rec_clear R0) st =
    (let '(R1, rc) := rec_stub_code (rec_clear R0) fn A in (VerbsRun.pins_follow R1 rc, false)) ->
  (r_refuse R0 <> 0 -> declared (r_code R0) = true) ->
  arity_ok (Z.of_nat (length ws)) (nth 0 ws []) 0 1 fn ->
  arity_ok (Z.of_nat (length ws)) (nth 0 ws []) 0 2 fn ->
  call_words_ok_at atoi (Z.min (Z.of_nat (length ws)) 64) ws (fn, A) ->
  let '(R1, x, q) := run_out_at R0 st None in P4_at R0 ws R1 x q.
Proof.
  intros R0 ws st fn A Hst Hd A1 A2 W. destruct resp0_facts_at as (Q1 & Q2 & Q3).
  unfold run_out_at. rewrite Hst. unfold rec_stub_code, rec_answer_code, VerbsRun.pins_follow,
    lv2_refusals_forget_m, rec_stub_mix. cbn.
  destruct (r_refuse R0 =? 0) eqn:Hr0; cbn.
  - apply P4_intro_at; cbn.
    + lia.
    + reflexivity.
    + exact Q2.
    + exact Q3.
    + reflexivity.
    + apply reply_ok_resp0_at.
    + exact A2.
    + apply Forall_cons; [exact W|apply Forall_cons; [apply cwo_forget_at|apply Forall_nil]].
    + rewrite Q1. intros H; exfalso; lia.
  - pose proof (decl_of R0 Hd Hr0) as Dc. destruct (resp_declared_facts_at _ Dc) as (D1 & D2 & D3 & D4).
    replace (r_code R0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn.
    apply P4_intro_at; cbn.
    + lia.
    + reflexivity.
    + exact D1.
    + exact D2.
    + reflexivity.
    + apply reply_ok_neg_at. exact Dc.
    + exact A1.
    + apply Forall_cons; [exact W|apply Forall_nil].
    + intros _. split; reflexivity.
Qed.

Lemma P4_bc_at : forall R0 ws ln tk,
  (r_refuse R0 <> 0 -> declared (r_code R0) = true) ->
  arity_ok (Z.of_nat (length ws)) (nth 0 ws []) 0 2 5 ->
  call_words_ok_at atoi (Z.min (Z.of_nat (length ws)) 64) ws (5, [canon ln]) ->
  call_words_ok_at atoi (Z.min (Z.of_nat (length ws)) 64) ws (6, [canon ln; dec (Z.of_nat (length tk)); join_sp tk]) ->
  let '(R1, x, q) := run_out_at R0 (Verbs.SBroadcast ln tk) None in P4_at R0 ws R1 x q.
Proof.
  intros R0 ws ln tk Hd A2 W1 W2. destruct resp0_facts_at as (Q1 & Q2 & Q3).
  unfold run_out_at. cbn [VerbsRun.run_step]. unfold sup_broadcast_m, sup_host_setting_m, rec_stub, rec_answer,
    hand_back, rec_mix_host. cbn.
  destruct (r_refuse R0 =? 0) eqn:Hr0; cbn.
  - rewrite inst_host. apply P4_intro_at; cbn.
    + lia.
    + reflexivity.
    + exact Q2.
    + exact Q3.
    + reflexivity.
    + apply reply_ok_resp0_at.
    + exact A2.
    + apply Forall_cons; [exact W1|apply Forall_cons; [exact W2|apply Forall_nil]].
    + rewrite Q1. intros H; exfalso; lia.
  - pose proof (decl_of R0 Hd Hr0) as Dc. destruct (resp_declared_facts_at _ Dc) as (D1 & D2 & D3 & D4).
    apply P4_intro_at; cbn.
    + lia.
    + reflexivity.
    + exact D1.
    + exact D2.
    + reflexivity.
    + apply reply_ok_neg_at. exact Dc.
    + exact A2.
    + apply Forall_cons; [exact W1|apply Forall_cons; [exact W2|apply Forall_nil]].
    + intros _. split; reflexivity.
Qed.

(** ** Words facts per verb *)

Lemma addw2_at : forall u i, add_part 3 [Verbs.Lit.verb_add; u; i] [u; dec (atoi i); S_DASH; S_DASH].
Proof.
  intros u i. destruct (add_pl_no 3 [] (or_intror (Z.le_refl 3))) as [P N].
  unfold add_part. cbn [length nth]. split; [reflexivity|split; [symmetry; exact P|]].
  unfold add_client. rewrite N. reflexivity.
Qed.

Lemma addw3p_at : forall u i x, Verbs.is_placement_m x = true ->
  add_part 4 [Verbs.Lit.verb_add; u; i; x] [u; dec (atoi i); x; S_DASH].
Proof.
  intros u i x H. destruct (add_pl_yes 4 x ltac:(lia) H) as [P N].
  unfold add_part. cbn [length nth]. split; [reflexivity|split; [symmetry; exact P|]].
  unfold add_client. rewrite N. reflexivity.
Qed.

Lemma addw3c_at : forall u i x, Verbs.is_placement_m x = false ->
  add_part 4 [Verbs.Lit.verb_add; u; i; x] [u; dec (atoi i); S_DASH; x].
Proof.
  intros u i x H. destruct (add_pl_no 4 x (or_introl H)) as [P N].
  unfold add_part. cbn [length nth]. split; [reflexivity|split; [symmetry; exact P|]].
  unfold add_client. rewrite N. reflexivity.
Qed.

Lemma addw4_at : forall u i x y, Verbs.is_placement_m x = true ->
  add_part 5 [Verbs.Lit.verb_add; u; i; x; y] [u; dec (atoi i); x; y].
Proof.
  intros u i x y H. destruct (add_pl_yes 5 x ltac:(lia) H) as [P N].
  unfold add_part. cbn [length nth]. split; [reflexivity|split; [symmetry; exact P|]].
  unfold add_client. rewrite N. reflexivity.
Qed.

Fixpoint ci_at (first : bool) (l : list (list byte)) : list Z :=
  match l with
  | [] => []
  | w :: l' => (if first then [] else [32]) ++ pf_dec (atoi w) ++ ci_at false l'
  end.

Lemma chain_items_ci_at : forall l k ws, (2 <= k)%nat ->
  (forall j, (j < length l)%nat -> nth (k + j) ws [] = nth j l []) ->
  chain_items_at atoi k (length l) ws = ci_at (Nat.eqb k 2) l.
Proof.
  induction l as [|w l IH]; intros k ws Hk H; [reflexivity|].
  cbn [length chain_items_at ci_at].
  pose proof (H 0%nat ltac:(cbn; lia)) as H0. rewrite Nat.add_0_r in H0. cbn [nth] in H0. rewrite H0.
  rewrite (IH (S k) ws ltac:(lia)).
  - replace (Nat.eqb (S k) 2) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
  - intros j Hj. replace (S k + j)%nat with (k + S j)%nat by lia. apply (H (S j)). cbn [length]. lia.
Qed.

Lemma ci_false_at : forall l, pf_bytes (ci_at false l) = concat (map (fun j => SPACE :: dec j) (map atoi l)).
Proof.
  induction l as [|w l IH]; [reflexivity|]. cbn [ci_at map concat].
  rewrite !pf_bytes_app, IH, dec_atoi_at. reflexivity.
Qed.

Lemma chain_ok_at : forall ws c a rest, c :: a :: rest = firstn 64 ws -> rest <> [] ->
  dec_list (map atoi rest) = pf_bytes (chain_list_at atoi (Z.of_nat (length (c :: a :: rest))) ws).
Proof.
  intros ws c a rest Hws Hne. unfold chain_list_at.
  replace (Z.to_nat (Z.of_nat (length (c :: a :: rest)) - 2)) with (length rest) by (cbn [length]; lia).
  rewrite (chain_items_ci_at rest 2 ws ltac:(lia)).
  - destruct rest as [|w rest']; [congruence|]. cbn [ci_at map Nat.eqb].
    rewrite !pf_bytes_app, ci_false_at, dec_atoi_at. reflexivity.
  - intros j Hj. rewrite (firstn64_nth ws (c :: a :: rest) (2 + j) Hws) by (cbn [length]; lia). reflexivity.
Qed.

Lemma after_cwo_at : forall ws tk, tk = firstn 64 ws ->
  Forall (call_words_ok_at atoi (Z.min (Z.of_nat (length ws)) 64) ws) (af_calls (Verbs.after atoi tk)).
Proof.
  intros ws tk Hws. destruct tk as [|v [|a rest]]; try apply Forall_nil.
  unfold Verbs.after.
  destruct (Verbs.verb_is_m v Verbs.Lit.fmt_preset_load || Verbs.verb_is_m v Verbs.Lit.fmt_patch_set);
    [|apply Forall_nil].
  cbn [af_calls]. apply Forall_cons; [|apply Forall_nil].
  destruct (ws_facts _ _ _ Hws) as (Hn0 & Hne & Hr). pose proof (ws_nth1 _ _ _ _ Hws) as Hn1.
  apply cwo_intro_at; [|intros E; discriminate E ..].
  change (call_items REC_AFTER_REPLY) with [INum 1; IWord 0]. cbn [items_ok_at want_at]. rewrite Hr.
  replace (1 <? Z.of_nat (length (v :: a :: rest))) with true by (symmetry; apply Z.ltb_lt; cbn [length]; lia).
  replace (0 <? Z.of_nat (length (v :: a :: rest))) with true by (symmetry; apply Z.ltb_lt; cbn [length]; lia).
  cbv beta iota. znat. rewrite Hn1, Hn0. split; [symmetry; apply dec_atoi_at | split; [reflexivity | exact I]].
Qed.

(** ** The four per-message checks *)

Ltac itac_at Hc := cbn; repeat apply conj; first [exact I | exact Hc | (symmetry; apply dec_atoi_at) | reflexivity].
Ltac c1_at Hc := apply cwo_intro_at; [itac_at Hc | intros E; discriminate E ..].
Ltac w1_at Hc := apply Forall_cons; [c1_at Hc | apply Forall_nil].
Ltac rdae_at := unfold daemon_shape; rewrite <- lit_bstr; apply reply_ok_shape_at; cbn; lia.
Ltac rhost_at := rewrite inst_host; apply reply_ok_resp0_at.
Ltac stubc_at Hd Hc := eapply P4_stub_at; [reflexivity | exact Hd | first [left; reflexivity | apply shape_of_in]
  | first [rhost_at | rdae_at] | arc | w1_at Hc].

Lemma P4_spec_at : forall R0 ws ln tk st af, pspec_at atoi ln tk st af -> tk = firstn 64 ws ->
  canon ln = join_sp ws -> first_word ln = nth 0 ws [] -> (r_refuse R0 <> 0 -> declared (r_code R0) = true) ->
  let '(R1, x, q) := run_out_at R0 st af in P4_at R0 ws R1 x q.
Proof.
  intros R0 ws ln tk st af HP.
  destruct HP as [tk|u i|u i x H|u i x H|u i x y H|a|a|a|a| |a| |a|a|a b|a b|a b|a b c
                 |a rest id ids H H0 H1|a id H|u f l|u f l vd H|a|a| |v args led H|v H|v a rest H|v a b H
                 |v a rest H]; intros Hws Hc Hf Hd.
  - (* reject *) apply P4_rej_at.
  - (* add u i *) fixws Hws. apply P4_add_at; [exact Hd | cbn; lia | reflexivity | arc | arc | | c1_at Hc].
    apply cwo_intro_at; [itac_at Hc | intros _; exact (addw2_at u i) | intros E; discriminate E ..].
  - (* add u i placement *) fixws Hws. apply P4_add_at; [exact Hd | cbn; lia | reflexivity | arc | arc | | c1_at Hc].
    apply cwo_intro_at; [itac_at Hc | intros _; exact (addw3p_at u i x H) | intros E; discriminate E ..].
  - (* add u i client *) fixws Hws. apply P4_add_at; [exact Hd | cbn; lia | reflexivity | arc | arc | | c1_at Hc].
    apply cwo_intro_at; [itac_at Hc | intros _; exact (addw3c_at u i x H) | intros E; discriminate E ..].
  - (* add u i placement client *) fixws Hws.
    apply P4_add_at; [exact Hd | cbn; lia | reflexivity | arc | arc | | c1_at Hc].
    apply cwo_intro_at; [itac_at Hc | intros _; exact (addw4_at u i x y H) | intros E; discriminate E ..].
  - (* descriptor_get *) fixws Hws. stubc_at Hd Hc.
  - (* panel_get *) fixws Hws. stubc_at Hd Hc.
  - (* remove all *) fixws Hws. stubc_at Hd Hc.
  - (* remove *) fixws Hws. stubc_at Hd Hc.
  - (* worker_list *) fixws Hws. stubc_at Hd Hc.
  - (* instance_info *) fixws Hws. stubc_at Hd Hc.
  - (* supervisor_reset *) fixws Hws. stubc_at Hd Hc.
  - (* supervisor_reset which *) fixws Hws. stubc_at Hd Hc.
  - (* quarantine_clear *) fixws Hws. stubc_at Hd Hc.
  - (* policy_set *) fixws Hws. stubc_at Hd Hc.
  - (* lv2_worker_set *) fixws Hws. stubc_at Hd Hc.
  - (* pool_config *) fixws Hws. stubc_at Hd Hc.
  - (* worker_env *) fixws Hws. stubc_at Hd Hc.
  - (* chain *)
    pose proof (A_number a id H0) as Ea. pose proof (Verbs.number_m_range a id H0) as Ra.
    pose proof (numbers_atoi_at rest ids H1) as Eids.
    destruct (ws_facts _ _ _ Hws) as (Hn0 & Hne & Hr). pose proof (ws_nth1 _ _ _ _ Hws) as Hn1.
    assert (Lr : (length rest <= 62)%nat)
      by (pose proof (f_equal (@length _) Hws) as L; rewrite length_firstn in L; cbn [length] in L; lia).
    subst id ids.
    eapply P4_stub_at; [reflexivity | exact Hd | apply shape_of_in | | | ].
    + rewrite Hn0. unfold daemon_shape. rewrite <- lit_bstr. apply reply_ok_shape_at. exact Hne.
    + rewrite Hn0. unfold arity_ok. right; right; right.
      replace (row_find Verbs.Lit.verb_chain parsed_rows) with (Some (2, UNB)) by (vm_compute; reflexivity).
      cbv beta iota. rewrite Hr. unfold UNB. destruct rest as [|r0 rest']; [congruence|]. cbn [length] in *. lia.
    + apply Forall_cons; [|apply Forall_nil]. apply cwo_intro_at.
      * change (call_items REC_CHAIN) with [INum 1; IStar; IStar]. cbn [items_ok_at want_at]. rewrite Hr.
        replace (1 <? Z.of_nat (length (Verbs.Lit.verb_chain :: a :: rest))) with true
          by (symmetry; apply Z.ltb_lt; cbn [length]; lia).
        cbv beta iota. znat. rewrite Hn1. split; [symmetry; apply dec_atoi_at | repeat split].
      * intros E; discriminate E.
      * intros _. split; [reflexivity|]. rewrite Hr. split.
        -- cbn [nth]. rewrite length_map.
           replace (Z.of_nat (length (Verbs.Lit.verb_chain :: a :: rest)) - 2) with (Z.of_nat (length rest))
             by (cbn [length]; lia).
           symmetry. apply dec_pf. lia.
        -- cbn [nth]. apply chain_ok_at; assumption.
      * intros E; discriminate E.
  - (* chain_clear *) pose proof (A_number a id H) as Ea. subst id. fixws Hws. stubc_at Hd Hc.
  - (* pin_set *) fixws Hws. eapply P4_pins_at; [reflexivity | exact Hd | arc | arc | ].
    apply cwo_intro_at; [itac_at Hc | intros E; discriminate E | intros E; discriminate E | intros _; split; reflexivity].
  - (* pin_set verdict *) fixws Hws. eapply P4_pins_at; [reflexivity | exact Hd | arc | arc | ].
    apply cwo_intro_at; [itac_at Hc | intros E; discriminate E | intros E; discriminate E | ].
    intros _. split; [reflexivity|]. cbn [nth darg]. unfold pin_verdict. rewrite (prefix_verdict vd H). reflexivity.
  - (* pin_accept *) fixws Hws. stubc_at Hd Hc.
  - (* pin_clear *) fixws Hws. eapply P4_pins_at; [reflexivity | exact Hd | arc | arc | c1_at Hc].
  - (* quit *) fixws Hws. apply P4_quit_at.
  - (* instance info verbs *)
    destruct (ws_facts _ _ _ Hws) as (Hn0 & Hne & Hr).
    eapply P4_stub_at; [reflexivity | exact Hd | apply shape_of_in | | | ].
    + rewrite Hf. apply reply_ok_shape_at. exact Hne.
    + rewrite Hn0. apply arity_row_none. exact (ledger_row_none v led H).
    + apply Forall_cons; [|exact (after_cwo_at ws (v :: args) Hws)].
      apply cwo_intro_at; [|intros E; discriminate E ..].
      change (call_items REC_INSTANCE_VERB) with [ILine; IStar]. cbn [items_ok_at want_at].
      split; [exact Hc | repeat split].
  - (* broadcast, one word *) fixws Hws.
    apply P4_bc_at; [exact Hd | apply arity_afree_gen; [lia | exact H] | c1_at Hc | c1_at Hc].
  - (* instance verbs *)
    destruct (ws_facts _ _ _ Hws) as (Hn0 & Hne & Hr). pose proof (ws_nth1 _ _ _ _ Hws) as Hn1.
    eapply P4_stub_at;
      [reflexivity | exact Hd | left; reflexivity | rhost_at | rewrite Hn0; apply arity_row_none; exact H | ].
    apply Forall_cons; [|exact (after_cwo_at ws _ Hws)].
    apply cwo_intro_at; [|intros E; discriminate E ..].
    change (call_items REC_CALL) with [INum 1; ILine]. cbn [items_ok_at want_at]. rewrite Hr.
    replace (1 <? Z.of_nat (length (v :: a :: rest))) with true by (symmetry; apply Z.ltb_lt; cbn [length]; lia).
    cbv beta iota. znat. rewrite Hn1. split; [symmetry; apply dec_atoi_at | split; [exact Hc | exact I]].
  - (* connect, disconnect *) fixws Hws. destruct H as [->| ->]; stubc_at Hd Hc.
  - (* broadcast *)
    destruct (ws_facts _ _ _ Hws) as (Hn0 & Hne & Hr).
    apply P4_bc_at; [exact Hd | rewrite Hn0; apply arity_afree_gen; [lia | exact H] | c1_at Hc | c1_at Hc].
Qed.

Lemma P4_holds_at : forall R0 D, (r_refuse R0 <> 0 -> declared (r_code R0) = true) ->
  let '(R1, x, q) := VerbsRun.run_receive atoi RC (rec_clear R0) D in P4_at R0 (hwords D) R1 x q.
Proof.
  intros R0 D Hd. rewrite vr_run_out_at.
  apply (P4_spec_at R0 (hwords D) (Verbs.line D) (Verbs.toks D));
    [apply receive_spec_at | apply toks_firstn | apply canon_line | apply first_word_line | exact Hd].
Qed.

(** ** The round trip *)

Lemma run_frame_at : forall R0 st af, let '(R1, x, q) := run_out_at R0 st af in
  r_refuse R1 = r_refuse R0 /\ r_code R1 = r_code R0 /\ r_spill R1 = r_spill R0.
Proof.
  intros R0 st af. unfold run_out_at. pose proof (step_frame_at RC R0 st) as F.
  destruct (VerbsRun.run_step RC (rec_clear R0) st) as [[R1 x] q].
  destruct F as (F1 & F2 & F3 & F4). destruct (fin_frame R1 x af ltac:(lia)) as (G1 & G2 & G3).
  cbv beta iota. rewrite G1, G2, G3. split; [exact F1|split; [exact F2|exact F3]].
Qed.

Lemma rt_holds_at : forall R0 D,
  let '(R1, x, q) := VerbsRun.run_receive atoi RC (rec_clear R0) D in
  rt_ok_at atoi RC R1 (if q then 1 else 0) (r_state R0) (r_host R0) (hwords D).
Proof.
  intros R0 D. rewrite vr_run_out_at.
  pose proof (run_frame_at R0 (fst (Verbs.receive atoi D)) (snd (Verbs.receive atoi D))) as Fr.
  destruct (run_out_at R0 (fst (Verbs.receive atoi D)) (snd (Verbs.receive atoi D))) as [[R1 x] q] eqn:Erun.
  destruct Fr as (F1 & F2 & F3).
  unfold rt_ok_at. intros Hne Hact.
  replace (rec_clear (set_host (set_state R1 (r_state R0)) (r_host R0))) with (rec_clear R0)
    by (unfold rec_clear, set_host, set_state; cbn; rewrite F1, F2, F3; reflexivity).
  rewrite vr_run_out_at.
  unfold Verbs.receive in *. rewrite toks_join, line_join.
  destruct (Verbs.toks D) as [|t tl] eqn:Et.
  { exfalso. apply Hne. apply firstn64_nil. rewrite <- toks_firstn. exact Et. }
  cbn [fst snd] in *.
  assert (Tk : forall t', In t' (t :: tl) -> tokp t').
  { intros t' Ht'. rewrite <- Et in Ht'. destruct (Verbs.toks_word D t' Ht') as [_ H].
    intros b Hb. destruct (H b Hb) as (H1 & H2 & _). split; assumption. }
  destruct (plan_ln atoi (Verbs.line D) (join_sp (hwords D)) (t :: tl)) as [Hrej|Heq].
  - rewrite canon_line, canon_join. reflexivity.
  - rewrite first_word_line, first_word_join. reflexivity.
  - apply join_le_line.
  - assert (Ha : Verbs.after atoi (t :: tl) = None).
    { destruct (Verbs.after atoi (t :: tl)) as [p|] eqn:Ea; [|reflexivity].
      exfalso. exact (after_some atoi (Verbs.line D) (t :: tl) p Tk Ea Hrej). }
    rewrite Hrej, Ha in Erun. unfold run_out_at, Verbs.reject in Erun. cbn in Erun.
    injection Erun as <- <- <-. unfold fin in Hact. cbn in Hact. discriminate Hact.
  - assert (E : run_out_at R0 (Verbs.plan atoi (join_sp (hwords D)) (t :: tl)) (Verbs.after atoi (t :: tl))
                = (R1, x, q)).
    { rewrite <- Erun. unfold run_out_at. rewrite Heq. reflexivity. }
    rewrite E. cbv beta iota. repeat split.
Qed.

(* the plain harness_props_holds (HarnessPropsProof.v:1479-1485) for this atoi *)
Theorem harness_props_at_holds : harness_props_at atoi RC.
Proof.
  intros R0 D _ _ _ Hd. pose proof (P4_holds_at R0 D Hd) as H1. pose proof (rt_holds_at R0 D) as H2.
  revert H1 H2. unfold msg_props_at. cbv zeta.
  destruct (VerbsRun.run_receive atoi RC (rec_clear R0) D) as [[R1 x] q]. intros H1 H2.
  destruct H1 as (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9).
  exact (conj h1 (conj h2 (conj h3 (conj h4 (conj h5 (conj h6 (conj h7 (conj h8 (conj h9 H2))))))))).
Qed.

End any_atoi.
