From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_text disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_json_c disco_json_lemmas slot_ser_pure slot_ser_tokb.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Open Scope Z_scope.

Definition jacc_add (count : Z) (acc : list jobj) (cur : jobj) : list jobj :=
  if count <? 9 then acc ++ [cur] else acc.

Section m.
Variable B : list Z.
Variable fin : Z * list jobj.

Definition jobjs_tail (i2 count : Z) (acc' : list jobj) (f : nat) : option (Z * list jobj) :=
  let i3 := json_ws B i2 in
  if at_byte B i3 44 then json_objs B (json_ws B (i3 + 1)) (count + 1) 9 acc' f
  else if at_byte B i3 93 then (if json_ws B (i3 + 1) =? jlen B then Some (count + 1, acc') else None)
  else None.

Definition jpairs_tail (i3 : Z) (c : jobj) (f : nat) : option (Z * jobj) :=
  if at_byte B i3 44 then json_pairs B (json_ws B (i3 + 1)) c f
  else if at_byte B i3 125 then Some (i3 + 1, c) else None.

Definition jslot_upd (kt vt : tokv) (cur : jobj) : option jobj :=
  match slot_of B kt with
  | Some k => if tv_kind (nth k cur tok_none) =? 0 then Some (set_nth k cur vt) else None
  | None => Some cur
  end.

Definition jobjs_from (i count : Z) (acc : list jobj) : Prop :=
  exists f, json_objs B i count 9 acc f = Some fin.

Definition jobjs_after (i2 count : Z) (acc : list jobj) (cur : jobj) : Prop :=
  exists f, jobjs_tail i2 count (jacc_add count acc cur) f = Some fin.

Definition jpairs_from (ip : Z) (cur : jobj) (count : Z) (acc : list jobj) : Prop :=
  exists f i2 c, json_pairs B ip cur f = Some (i2, c) /\ jobjs_after i2 count acc c.

Definition jpairs_cont (i3 : Z) (c : jobj) (count : Z) (acc : list jobj) : Prop :=
  exists f i2 c', jpairs_tail i3 c f = Some (i2, c') /\ jobjs_after i2 count acc c'.

Lemma json_pairs_S : forall i cur f,
  json_pairs B i cur (S f) =
  match jscalar B i with
  | None => None
  | Some (j, kk, ks, kl) =>
      if negb (kk =? 1) then None
      else if negb (at_byte B (json_ws B j) 58) then None
      else match jscalar B (json_ws B (json_ws B j + 1)) with
           | None => None
           | Some (j2, vk, vs, vl) =>
               match jslot_upd (kk, ks, kl) (vk, vs, vl) cur with
               | None => None
               | Some c => jpairs_tail (json_ws B j2) c f
               end
           end
  end.
Proof. intros i cur f. reflexivity. Qed.

Lemma jpairs_from_step : forall ip cur count acc,
  jpairs_from ip cur count acc ->
  exists j kk ks kl j2 vk vs vl c,
    jscalar B ip = Some (j, kk, ks, kl) /\ kk = 1 /\ at_byte B (json_ws B j) 58 = true /\
    jscalar B (json_ws B (json_ws B j + 1)) = Some (j2, vk, vs, vl) /\
    jslot_upd (kk, ks, kl) (vk, vs, vl) cur = Some c /\
    jpairs_cont (json_ws B j2) c count acc.
Proof.
  intros ip cur count acc (f & i2 & c & HP & HA).
  destruct f as [|f]; [discriminate|]. rewrite json_pairs_S in HP.
  destruct (jscalar B ip) as [[[[j kk] ks] kl]|] eqn:E1; [|discriminate].
  destruct (kk =? 1) eqn:E2; cbn [negb] in HP; [|discriminate].
  destruct (at_byte B (json_ws B j) 58) eqn:E3; cbn [negb] in HP; [|discriminate].
  destruct (jscalar B (json_ws B (json_ws B j + 1))) as [[[[j2 vk] vs] vl]|] eqn:E4; [|discriminate].
  destruct (jslot_upd (kk, ks, kl) (vk, vs, vl) cur) as [c0|] eqn:E5; [|discriminate].
  exists j, kk, ks, kl, j2, vk, vs, vl, c0. apply Z.eqb_eq in E2.
  repeat split; try reflexivity; try assumption.
  exists f, i2, c. split; assumption.
Qed.

Lemma jpairs_cont_step : forall i3 c count acc,
  jpairs_cont i3 c count acc ->
  (at_byte B i3 44 = true /\ jpairs_from (json_ws B (i3 + 1)) c count acc) \/
  (at_byte B i3 44 = false /\ at_byte B i3 125 = true /\ jobjs_after (i3 + 1) count acc c).
Proof.
  intros i3 c count acc (f & i2 & c' & HT & HA). unfold jpairs_tail in HT.
  destruct (at_byte B i3 44) eqn:E1.
  - left. split; [reflexivity|]. exists f, i2, c'. split; assumption.
  - destruct (at_byte B i3 125) eqn:E2; [|discriminate].
    injection HT as <- <-. right. split; [reflexivity|]. split; [reflexivity|]. exact HA.
Qed.

Lemma jobjs_from_step : forall i count acc,
  jobjs_from i count acc ->
  at_byte B i 123 = true /\
  ((at_byte B (json_ws B (i + 1)) 125 = true /\ jobjs_after (json_ws B (i + 1) + 1) count acc jobj_empty) \/
   (at_byte B (json_ws B (i + 1)) 125 = false /\ jpairs_from (json_ws B (i + 1)) jobj_empty count acc)).
Proof.
  intros i count acc (f & HO). destruct f as [|f]; [discriminate|]. cbn [json_objs] in HO.
  destruct (at_byte B i 123) eqn:E1; cbn [negb] in HO; [|discriminate].
  split; [reflexivity|].
  destruct (at_byte B (json_ws B (i + 1)) 125) eqn:E2.
  - left. split; [reflexivity|]. exists f. exact HO.
  - right. split; [reflexivity|].
    destruct (json_pairs B (json_ws B (i + 1)) jobj_empty (length B)) as [[i2 cur]|] eqn:E3; [|discriminate].
    exists (length B), i2, cur. split; [exact E3|]. exists f. exact HO.
Qed.

Lemma jscalar_in : forall i j k s l, jscalar B i = Some (j, k, s, l) -> i < jlen B.
Proof.
  intros i j k s l H. unfold jscalar in H. destruct (jlen B <=? i) eqn:E; [discriminate|]. apply Z.leb_gt in E. exact E.
Qed.

Lemma jobjs_from_lt : forall i count acc, jobjs_from i count acc -> i < jlen B.
Proof.
  intros i count acc H. destruct (jobjs_from_step i count acc H) as [H1 _]. unfold at_byte in H1.
  apply andb_true_iff in H1 as [H1 _]. apply Z.ltb_lt in H1. exact H1.
Qed.

Lemma jobjs_after_step : forall i2 count acc cur,
  jobjs_after i2 count acc cur ->
  (at_byte B (json_ws B i2) 44 = true /\
   jobjs_from (json_ws B (json_ws B i2 + 1)) (count + 1) (jacc_add count acc cur)) \/
  (at_byte B (json_ws B i2) 44 = false /\ at_byte B (json_ws B i2) 93 = true /\
   json_ws B (json_ws B i2 + 1) = jlen B /\ fin = (count + 1, jacc_add count acc cur)).
Proof.
  intros i2 count acc cur (f & HT). unfold jobjs_tail in HT.
  destruct (at_byte B (json_ws B i2) 44) eqn:E1.
  - left. split; [reflexivity|]. exists f. exact HT.
  - destruct (at_byte B (json_ws B i2) 93) eqn:E2; [|discriminate].
    destruct (json_ws B (json_ws B i2 + 1) =? jlen B) eqn:E3; [|discriminate].
    injection HT as <-. apply Z.eqb_eq in E3. right. repeat split; assumption.
Qed.

Lemma json_read_step : json_read B 9 = Some fin ->
  at_byte B (json_ws B 0) 91 = true /\
  ((at_byte B (json_ws B (json_ws B 0 + 1)) 93 = true /\
    json_ws B (json_ws B (json_ws B 0 + 1) + 1) = jlen B /\ fin = (0, [])) \/
   (at_byte B (json_ws B (json_ws B 0 + 1)) 93 = false /\ jobjs_from (json_ws B (json_ws B 0 + 1)) 0 [])).
Proof.
  intros H. unfold json_read in H. cbv zeta in H.
  destruct (at_byte B (json_ws B 0) 91) eqn:E1; cbn [negb] in H; [|discriminate].
  split; [reflexivity|].
  destruct (at_byte B (json_ws B (json_ws B 0 + 1)) 93) eqn:E2.
  - destruct (json_ws B (json_ws B (json_ws B 0 + 1) + 1) =? jlen B) eqn:E3; [|discriminate].
    injection H as <-. apply Z.eqb_eq in E3. left. repeat split; assumption.
  - right. split; [reflexivity|]. exists (length B). exact H.
Qed.

Lemma json_objs_count : forall f i count acc r os,
  json_objs B i count 9 acc f = Some (r, os) -> count < r.
Proof.
  induction f as [|f IH]; intros i count acc r os H; [discriminate|]. cbn [json_objs] in H.
  destruct (negb (at_byte B i 123)); [discriminate|].
  destruct (if at_byte B (json_ws B (i + 1)) 125 then Some (json_ws B (i + 1) + 1, jobj_empty)
            else json_pairs B (json_ws B (i + 1)) jobj_empty (length B)) as [[i2 cur]|]; [|discriminate].
  destruct (at_byte B (json_ws B i2) 44).
  - pose proof (IH _ _ _ _ _ H). lia.
  - destruct (at_byte B (json_ws B i2) 93); [|discriminate].
    destruct (json_ws B (json_ws B i2 + 1) =? jlen B); [|discriminate]. injection H as <- _. lia.
Qed.

Lemma jobjs_from_count : forall i count acc, jobjs_from i count acc -> count < fst fin.
Proof.
  intros i count acc (f & H). destruct fin as [r os]. cbn [fst]. exact (json_objs_count f i count acc r os H).
Qed.

Lemma jobjs_after_count : forall i2 count acc cur, jobjs_after i2 count acc cur -> count + 1 <= fst fin.
Proof.
  intros i2 count acc cur H. destruct (jobjs_after_step i2 count acc cur H) as [(_ & H2) | (_ & _ & _ & ->)].
  - pose proof (jobjs_from_count _ _ _ H2). lia.
  - cbn [fst]. lia.
Qed.

Lemma jpairs_from_count : forall ip cur count acc, jpairs_from ip cur count acc -> count + 1 <= fst fin.
Proof. intros ip cur count acc (f & i2 & c & _ & HA). exact (jobjs_after_count _ _ _ _ HA). Qed.

End m.

Definition jno_ws (B : list Z) : Prop := Forall (fun c => 33 <= c <= 255) B.

Lemma jno_ws_byte : forall B i, jno_ws B -> 0 <= i < jlen B -> 33 <= jbyte B i <= 255.
Proof.
  intros B i H Hi. unfold jno_ws, jbyte, jlen in *. rewrite Forall_forall in H. apply H. apply nth_In. lia.
Qed.

Lemma jno_ws_char : forall c, 33 <= c -> jws_char c = false.
Proof.
  intros c Hc. unfold jws_char.
  repeat rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
Qed.

Lemma json_ws_f_id : forall B f i, jno_ws B -> 0 <= i -> json_ws_f B i f = i.
Proof.
  intros B f i H Hi. destruct f as [|f]; [reflexivity|]. cbn [json_ws_f].
  destruct (Z.ltb_spec i (jlen B)) as [L|L]; [|reflexivity].
  rewrite (jno_ws_char _ (proj1 (jno_ws_byte B i H (conj Hi L)))). reflexivity.
Qed.

Lemma json_ws_id : forall B i, jno_ws B -> 0 <= i -> json_ws B i = i.
Proof. intros B i H Hi. unfold json_ws. apply json_ws_f_id; assumption. Qed.

Lemma at_byte_true : forall B i c, at_byte B i c = true -> i < jlen B /\ jbyte B i = c.
Proof.
  intros B i c H. unfold at_byte in H. apply andb_true_iff in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. split; assumption.
Qed.

Lemma at_byte_false : forall B i c, 0 <= i < jlen B -> jbyte B i <> c -> at_byte B i c = false.
Proof.
  intros B i c Hi Hc. unfold at_byte. apply andb_false_iff. right. apply Z.eqb_neq. exact Hc.
Qed.

Lemma at_byte_spec : forall B i c, 0 <= i < jlen B -> at_byte B i c = (jbyte B i =? c).
Proof.
  intros B i c Hi. unfold at_byte. replace (i <? jlen B) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma jdigits_gt : forall B f j, (0 < f)%nat -> jdig_at B j = true -> j < jdigits B j f.
Proof.
  intros B f j Hf H. destruct f as [|f]; [lia|]. cbn [jdigits]. unfold jdig_at in H. rewrite H.
  pose proof (slot_ser_tokb.jdigits_ge B f (j + 1)). lia.
Qed.

Lemma jfrac_ge : forall B j r, jfrac B j = Some r -> j <= r.
Proof.
  intros B j r H. unfold jfrac in H.
  destruct ((j <? jlen B) && (jbyte B j =? 46)); [|injection H as <-; lia].
  destruct (jdig_at B (j + 1)); [|discriminate]. injection H as <-.
  pose proof (slot_ser_tokb.jdigits_ge B (length B) (j + 1)). lia.
Qed.

Lemma jexp_ge : forall B j r, jexp B j = Some r -> j <= r.
Proof.
  intros B j r H. unfold jexp in H. cbv zeta in H.
  destruct ((j <? jlen B) && ((jbyte B j =? 101) || (jbyte B j =? 69))); [|injection H as <-; lia].
  match type of H with context [jdig_at B ?k] =>
    destruct (jdig_at B k); [|discriminate]; injection H as <-;
    pose proof (slot_ser_tokb.jdigits_ge B (length B) k) end.
  destruct ((j + 1 <? jlen B) && ((jbyte B (j + 1) =? 43) || (jbyte B (j + 1) =? 45))); lia.
Qed.

Lemma jscalar_lt : forall B i j k s l, 0 <= i -> jscalar B i = Some (j, k, s, l) -> i < j.
Proof.
  intros B i j k s l Hi H. unfold jscalar in H.
  destruct (jlen B <=? i) eqn:E0; [discriminate|]. apply Z.leb_gt in E0.
  destruct (jbyte B i =? 34) eqn:E1.
  - destruct (slot_ser_tokb.jstr_bnd B i (length B) (i + 1) _ H) as (jc & Hjc & Hr).
    injection Hr as -> _ _ _. lia.
  - destruct (jlit B i jlit_words) as [t|] eqn:E2.
    + injection H as H. subst t. unfold jlit_words in E2. cbn [jlit] in E2.
      repeat match type of E2 with context [if ?c then _ else _] => destruct c end;
        try discriminate; injection E2 as <- _ _ _; cbn [length Z.of_nat]; lia.
    + unfold jnum in H. cbv zeta in H.
      set (j0 := if jbyte B i =? 45 then i + 1 else i) in H.
      assert (Hj0 : i <= j0) by (subst j0; destruct (jbyte B i =? 45); lia).
      destruct (jdig_at B j0) eqn:E3; cbn [negb] in H; [|discriminate].
      assert (Hj1 : j0 < (if jbyte B j0 =? 48 then j0 + 1 else jdigits B j0 (length B))).
      { destruct (jbyte B j0 =? 48); [lia|]. apply jdigits_gt; [|exact E3].
        unfold jdig_at in E3. apply andb_true_iff in E3 as [E3 _]. apply Z.ltb_lt in E3. unfold jlen in E3. lia. }
      destruct (jfrac B _) as [j2|] eqn:E4; [|discriminate].
      destruct (jexp B j2) as [j3|] eqn:E5; [|discriminate].
      injection H as <- _ _ _. pose proof (jfrac_ge _ _ _ E4). pose proof (jexp_ge _ _ _ E5). lia.
Qed.

Definition jtext (T : list (bv 8)) (now : Z) : list Z := reac_disco_table_json_c.tj_text T now.

Lemma jtext_facts : forall (T : list (bv 8)) now, length T = 400%nat -> disco_table_c.table_ok T -> 0 <= now < 2 ^ 64 ->
  exists os, json_read (jtext T now) 9 = Some (disco_table_c.n_of T, os) /\
    0 <= disco_table_c.n_of T <= 8 /\ jno_ws (jtext T now) /\ (length (jtext T now) <= 969)%nat /\
    Forall (Forall (slot_ser_tokb.tok_inb (jtext T now))) os.
Proof.
  intros T now LT TOK Hnow.
  pose proof (slot_ser_pure.ser_tj_ok T LT TOK) as [TOK' WF].
  destruct (disco_json_lemmas.F1_2_json_read_table reac_disco_table_json_c.box_tok
              (reac_disco_table_json_c.tj_entries T) now slot_ser_pure.ser_tok_ok TOK' WF Hnow) as (os & JR & _).
  change (table_json_text reac_disco_table_json_c.box_tok (reac_disco_table_json_c.tj_entries T) now)
    with (jtext T now) in JR.
  rewrite slot_ser_pure.ser_tj_len in JR.
  pose proof TOK as (T1 & _). unfold disco_table_c.tbl_T1 in T1.
  rewrite Z2Nat.id in JR by lia.
  exists os. split; [exact JR|]. split; [destruct TOK' as (TL & _); rewrite slot_ser_pure.ser_tj_len in TL; lia|].
  split; [exact (slot_ser_pure.ser_text_g33 reac_disco_table_json_c.box_tok (reac_disco_table_json_c.tj_entries T) now
                   slot_ser_pure.ser_tok_ok WF Hnow)|].
  split; [exact (disco_json_lemmas.C7_text_bound reac_disco_table_json_c.box_tok (reac_disco_table_json_c.tj_entries T) now
                   slot_ser_pure.ser_tok_ok TOK' WF Hnow)|].
  exact (slot_ser_tokb.json_read_inb _ _ _ _ JR).
Qed.
