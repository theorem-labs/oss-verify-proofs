From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Strings.String Strings.Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition err_invalid_operation : Z := -902.
Definition success : Z := 0.
Definition line_max : Z := 4096.
Definition line_words_max : nat := 64%nat.
Definition ledger_none : Z := 0.
Definition ledger_replace : Z := 1.

Module Lit.
Import Stdlib.Strings.String Stdlib.Strings.Ascii.

Fixpoint lit (s : string) : list byte :=
  match s with
  | EmptyString => []
  | String a s' => Z_to_bv 8 (Z.of_nat (nat_of_ascii a)) :: lit s'
  end.

Local Open Scope string_scope.

Definition verb_add := lit "add".
Definition verb_descriptor_get := lit "descriptor_get".
Definition verb_panel_get := lit "panel_get".
Definition verb_worker_list := lit "worker_list".
Definition verb_instance_info := lit "instance_info".
Definition verb_supervisor_reset := lit "supervisor_reset".
Definition verb_quarantine_clear := lit "quarantine_clear".
Definition verb_policy_set := lit "policy_set".
Definition verb_lv2_worker_set := lit "lv2_worker_set".
Definition verb_pool_config := lit "pool_config".
Definition verb_worker_env := lit "worker_env".
Definition verb_chain := lit "chain".
Definition verb_chain_clear := lit "chain_clear".
Definition verb_pin_set := lit "pin_set".
Definition verb_pin_accept := lit "pin_accept".
Definition verb_pin_clear := lit "pin_clear".

Definition fmt_remove := lit "remove %i".
Definition fmt_quit := lit "quit".
Definition fmt_connect := lit "connect %s %s".
Definition fmt_disconnect := lit "disconnect %s %s".
Definition fmt_preset_load := lit "preset_load %i %s".
Definition fmt_patch_set := lit "patch_set %i %s %s".

Definition verb_remove := lit "remove".
Definition verb_quit := lit "quit".
Definition verb_connect := lit "connect".
Definition verb_disconnect := lit "disconnect".
Definition verb_preset_load := lit "preset_load".
Definition verb_patch_set := lit "patch_set".

Definition word_verdict := lit "verdict=".
Definition word_layout_unknown := lit "-".
Definition word_all := lit "all".
Definition place_own := lit "own".
Definition place_default := lit "default".
Definition place_pool_prefix := lit "pool:".

Definition instance_verb_formats : list (list byte) := map lit [
  "preset_load %i %s"; "preset_save %i %s %s %s"; "bypass %i %i"; "param_set %i %s %s"; "param_get %i %s";
  "param_monitor %i %s %s %f"; "patch_set %i %s %s"; "patch_get %i %s"; "licensee %i"; "monitor_output %i %s";
  "midi_learn %i %s %f %f"; "midi_map %i %s %i %i %f %f"; "midi_unmap %i %s";
  "cc_map %i %s %i %i %s %f %f %f %i %i %s %i ..."; "cc_unmap %i %s"; "cc_value_set %i %s %f";
  "cv_map %i %s %s %f %f %s"; "cv_unmap %i %s"].

Definition instance_verb_names : list (list byte) := map lit [
  "preset_load"; "preset_save"; "bypass"; "param_set"; "param_get"; "param_monitor"; "patch_set"; "patch_get";
  "licensee"; "monitor_output"; "midi_learn"; "midi_map"; "midi_unmap"; "cc_map"; "cc_unmap"; "cc_value_set";
  "cv_map"; "cv_unmap"].

Definition instance_info_verbs : list (list byte * Z) := [
  (lit "track_info", ledger_replace); (lit "remote_pages", ledger_none); (lit "remote_page_get", ledger_none);
  (lit "param_info", ledger_none); (lit "preset_list", ledger_none); (lit "preset_get", ledger_none);
  (lit "note_input", ledger_none); (lit "note_on", ledger_none); (lit "note_off", ledger_none);
  (lit "all_notes_off", ledger_none)].

End Lit.
Export Lit.

Definition is_sep (b : byte) : bool := (bv_unsigned b =? 32) || (bv_unsigned b =? 9).
Definition is_trail (b : byte) : bool := is_sep b || (bv_unsigned b =? 10) || (bv_unsigned b =? 13).
Definition is_space (b : byte) : bool := ((9 <=? bv_unsigned b) && (bv_unsigned b <=? 13)) || (bv_unsigned b =? 32).
Definition is_digit (b : byte) : bool := (48 <=? bv_unsigned b) && (bv_unsigned b <=? 57).

Fixpoint upto (p : byte -> bool) (l : list byte) : list byte :=
  match l with
  | [] => []
  | b :: l' => if p b then [] else b :: upto p l'
  end.

Fixpoint dropw (p : byte -> bool) (l : list byte) : list byte :=
  match l with
  | [] => []
  | b :: l' => if p b then dropw p l' else l
  end.

Definition upto0 (D : list byte) : list byte := upto (fun b => bv_unsigned b =? 0) D.
Definition trim (l : list byte) : list byte := rev (dropw is_trail (rev l)).
Definition line (D : list byte) : list byte := trim (upto0 D).

Fixpoint words_acc (cur l : list byte) : list (list byte) :=
  match l with
  | [] => match cur with [] => [] | _ :: _ => [cur] end
  | b :: l' =>
      if is_sep b then match cur with [] => words_acc [] l' | _ :: _ => cur :: words_acc [] l' end
      else words_acc (cur ++ [b]) l'
  end.

Definition words (l : list byte) : list (list byte) := words_acc [] l.
Definition toks (D : list byte) : list (list byte) := firstn line_words_max (words (line D)).

Fixpoint list_eqb (a b : list byte) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (bv_unsigned x =? bv_unsigned y) && list_eqb a' b'
  | _, _ => false
  end.

Definition vfirst (f : list byte) : list byte := upto (fun b => bv_unsigned b =? 32) f.
Definition tfirst (t : list byte) : list byte := upto is_sep t.
Definition verb_is_m (t f : list byte) : bool :=
  Nat.eqb (length (tfirst t)) (length (vfirst f)) && list_eqb (firstn (length (vfirst f)) t) (vfirst f).

Fixpoint digits_val (acc : Z) (l : list byte) : option Z :=
  match l with
  | [] => Some acc
  | b :: l' => if is_digit b then digits_val (10 * acc + (bv_unsigned b - 48)) l' else None
  end.

Definition digits_m (l : list byte) : option Z :=
  match l with
  | [] => None
  | _ :: _ => digits_val 0 l
  end.

Definition signed_digits (r : list byte) : option Z :=
  match r with
  | [] => None
  | b :: r' =>
      if bv_unsigned b =? 43 then digits_m r'
      else if bv_unsigned b =? 45 then option_map Z.opp (digits_m r')
      else digits_m r
  end.

Definition number_m (w : list byte) : option Z :=
  match signed_digits (dropw is_space w) with
  | Some v => if (-1000000 <=? v) && (v <=? 1000000) then Some v else None
  | None => None
  end.

Fixpoint numbers_m (ws : list (list byte)) : option (list Z) :=
  match ws with
  | [] => Some []
  | w :: ws' =>
      match number_m w, numbers_m ws' with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

Definition has_prefix (p w : list byte) : bool :=
  Nat.leb (length p) (length w) && list_eqb (firstn (length p) w) p.

Definition is_placement_m (w : list byte) : bool :=
  list_eqb w place_own || list_eqb w place_default || has_prefix place_pool_prefix w.

Inductive call : Type :=
| sup_add (uri : list byte) (id : Z) (placement client : option (list byte))
| descriptors_get (uri : list byte)
| descriptors_panel_get (uri : list byte)
| sup_remove (id : Z)
| sup_remove_all
| sup_worker_list
| sup_instance_info (id : Z)
| sup_reset (which : list byte)
| sup_quarantine_clear (w : list byte)
| sup_policy_set (a b : list byte)
| sup_lv2_worker_set (a b : list byte)
| sup_pool_config (name : list byte) (maximum : Z)
| sup_worker_env (a b c : list byte)
| sup_chain (id : Z) (ids : list Z)
| sup_chain_clear (id : Z)
| sup_pin_accept (uri : list byte)
| sup_instance_verb (ln : list byte) (ledger : Z)
| sup_call (id : Z) (ln : list byte)
| sup_connect (verb ln a b : list byte).

Inductive step : Type :=
| SResp (code : Z)
| SCall (c : call)
| SAdd (uri : list byte) (id : Z) (placement client : option (list byte))
| SPinSet (uri files layout : list byte) (verdict : option (list byte))
| SPinClear (uri : list byte)
| SQuit
| SBroadcast (ln : list byte) (tk : list (list byte)).

Definition reject : step := SResp err_invalid_operation.

Definition add_m (atoi : list byte -> Z) (args : list (list byte)) : step :=
  match args with
  | u :: i :: rest =>
      match rest with
      | [] => SAdd u (atoi i) None None
      | [x] => if is_placement_m x then SAdd u (atoi i) (Some x) None else SAdd u (atoi i) None (Some x)
      | [x; y] => if is_placement_m x then SAdd u (atoi i) (Some x) (Some y) else reject
      | _ => reject
      end
  | _ => reject
  end.

Definition chain_words_m (args : list (list byte)) : step :=
  match args with
  | a :: ((_ :: _) as rest) =>
      match number_m a, numbers_m rest with
      | Some id, Some ids => SCall (sup_chain id ids)
      | _, _ => reject
      end
  | _ => reject
  end.

Definition pin_set_words_m (ln : list byte) (args : list (list byte)) : step :=
  match args with
  | [u; fl; ly] =>
      if (line_max <? Z.of_nat (length ln)) || list_eqb ly word_layout_unknown then reject
      else SPinSet u fl ly None
  | [u; fl; ly; vd] =>
      if (line_max <? Z.of_nat (length ln)) || list_eqb ly word_layout_unknown then reject
      else if has_prefix word_verdict vd then SPinSet u fl ly (Some (skipn 8 vd)) else reject
  | _ => reject
  end.

Fixpoint ledger_of (v : list byte) (tbl : list (list byte * Z)) : option Z :=
  match tbl with
  | [] => None
  | (name, ledger) :: tbl' => if list_eqb v name then Some ledger else ledger_of v tbl'
  end.

Definition is_instance_verb (v : list byte) : bool := existsb (verb_is_m v) instance_verb_formats.

Definition plan (atoi : list byte -> Z) (ln : list byte) (tk : list (list byte)) : step :=
  match tk with
  | [] => reject
  | v :: args =>
    if list_eqb v verb_add then add_m atoi args else
    if list_eqb v verb_descriptor_get then
      match args with [a] => SCall (descriptors_get a) | _ => reject end else
    if list_eqb v verb_panel_get then
      match args with [a] => SCall (descriptors_panel_get a) | _ => reject end else
    if verb_is_m v fmt_remove then
      match args with
      | [a] => if atoi a =? -1 then SCall sup_remove_all else SCall (sup_remove (atoi a))
      | _ => reject
      end else
    if list_eqb v verb_worker_list then
      match args with [] => SCall sup_worker_list | _ => reject end else
    if list_eqb v verb_instance_info then
      match args with [a] => SCall (sup_instance_info (atoi a)) | _ => reject end else
    if list_eqb v verb_supervisor_reset then
      match args with
      | [] => SCall (sup_reset word_all)
      | [a] => SCall (sup_reset a)
      | _ => reject
      end else
    if list_eqb v verb_quarantine_clear then
      match args with [a] => SCall (sup_quarantine_clear a) | _ => reject end else
    if list_eqb v verb_policy_set then
      match args with [a; b] => SCall (sup_policy_set a b) | _ => reject end else
    if list_eqb v verb_lv2_worker_set then
      match args with [a; b] => SCall (sup_lv2_worker_set a b) | _ => reject end else
    if list_eqb v verb_pool_config then
      match args with [a; b] => SCall (sup_pool_config a (atoi b)) | _ => reject end else
    if list_eqb v verb_worker_env then
      match args with [a; b; c] => SCall (sup_worker_env a b c) | _ => reject end else
    if list_eqb v verb_chain then chain_words_m args else
    if list_eqb v verb_chain_clear then
      match args with
      | [a] => match number_m a with Some id => SCall (sup_chain_clear id) | None => reject end
      | _ => reject
      end else
    if list_eqb v verb_pin_set then pin_set_words_m ln args else
    if list_eqb v verb_pin_accept then
      match args with [a] => SCall (sup_pin_accept a) | _ => reject end else
    if list_eqb v verb_pin_clear then
      match args with [a] => SPinClear a | _ => reject end else
    if verb_is_m v fmt_quit then
      match args with [] => SQuit | _ => reject end else
    match ledger_of v instance_info_verbs with
    | Some ledger => SCall (sup_instance_verb ln ledger)
    | None =>
      match args with
      | [] => SBroadcast ln tk
      | a :: rest =>
        if is_instance_verb v then SCall (sup_call (atoi a) ln) else
        match rest with
        | [b] =>
          if verb_is_m v fmt_connect || verb_is_m v fmt_disconnect then SCall (sup_connect v ln a b)
          else SBroadcast ln tk
        | _ => SBroadcast ln tk
        end
      end
    end
  end.

Definition after (atoi : list byte -> Z) (tk : list (list byte)) : option (Z * list byte) :=
  match tk with
  | v :: a :: _ => if verb_is_m v fmt_preset_load || verb_is_m v fmt_patch_set then Some (atoi a, v) else None
  | _ => None
  end.

Definition receive (atoi : list byte -> Z) (D : list byte) : step * option (Z * list byte) :=
  match toks D with
  | [] => (SResp err_invalid_operation, None)
  | tk => (plan atoi (line D) tk, after atoi tk)
  end.

Lemma list_eqb_eq : forall a b, list_eqb a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b]; cbn [list_eqb]; try (split; intros; congruence).
  rewrite andb_true_iff, Z.eqb_eq, IH. split.
  - intros [E ->]. f_equal. apply bv_eq. exact E.
  - intros H. injection H as -> ->. split; reflexivity.
Qed.

Lemma sep_false : forall b, is_sep b = false <-> bv_unsigned b <> 32 /\ bv_unsigned b <> 9.
Proof. intros b. unfold is_sep. rewrite orb_false_iff, !Z.eqb_neq. tauto. Qed.

Lemma upto_in : forall p l b, In b (upto p l) -> In b l /\ p b = false.
Proof.
  intros p l b; induction l as [|x l IH]; cbn [upto]; [intros []|].
  destruct (p x) eqn:E; [intros []|].
  intros [<-|H]; [split; [left; reflexivity| exact E]|].
  destruct (IH H) as [H1 H2]. split; [right; exact H1| exact H2].
Qed.

Lemma upto_all : forall p l, (forall b, In b l -> p b = false) -> upto p l = l.
Proof.
  intros p l; induction l as [|x l IH]; intros H; cbn [upto]; [reflexivity|].
  rewrite (H x (or_introl eq_refl)). f_equal. apply IH. intros b Hb. apply H. right. exact Hb.
Qed.

Lemma dropw_in : forall p l b, In b (dropw p l) -> In b l.
Proof.
  intros p l b; induction l as [|x l IH]; cbn [dropw]; [intros []|].
  destruct (p x); [intros H; right; apply IH; exact H| intros H; exact H].
Qed.

Lemma line_nonul : forall D b, In b (line D) -> bv_unsigned b <> 0.
Proof.
  intros D b H. unfold line, trim in H. rewrite <- in_rev in H. apply dropw_in in H.
  rewrite <- in_rev in H. unfold upto0 in H. apply upto_in in H. destruct H as [_ H].
  apply Z.eqb_neq. exact H.
Qed.

Lemma words_acc_spec : forall (P : byte -> Prop) l cur,
  (forall b, In b cur -> P b /\ is_sep b = false) -> (forall b, In b l -> P b) ->
  forall w, In w (words_acc cur l) -> w <> [] /\ (forall b, In b w -> P b /\ is_sep b = false).
Proof.
  intros P l; induction l as [|x l IH]; intros cur Hc Hl w Hw; cbn [words_acc] in Hw.
  - destruct cur as [|y cur']; [destruct Hw|]. destruct Hw as [<-|[]]. split; [discriminate| exact Hc].
  - destruct (is_sep x) eqn:S.
    + destruct cur as [|y cur'].
      * apply (IH []); [intros b []| intros b Hb; apply Hl; right; exact Hb| exact Hw].
      * destruct Hw as [<-|Hw]; [split; [discriminate| exact Hc]|].
        apply (IH []); [intros b []| intros b Hb; apply Hl; right; exact Hb| exact Hw].
    + apply (IH (cur ++ [x])); [| intros b Hb; apply Hl; right; exact Hb| exact Hw].
      intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|[<-|[]]]; [exact (Hc b Hb)|].
      split; [apply Hl; left; reflexivity| exact S].
Qed.

Lemma words_word : forall l w, In w (words l) ->
  w <> [] /\ forall b, In b w -> bv_unsigned b <> 32 /\ bv_unsigned b <> 9.
Proof.
  intros l w Hw.
  destruct (words_acc_spec (fun _ => True) l [] (fun b H => False_ind _ H) (fun _ _ => I) w Hw) as [Hn Hb].
  split; [exact Hn|]. intros b H. destruct (Hb b H) as [_ S]. apply sep_false. exact S.
Qed.

Lemma toks_length : forall D, (length (toks D) <= 64)%nat.
Proof. intros D. unfold toks, line_words_max. apply firstn_le_length. Qed.

Lemma toks_in : forall D t, In t (toks D) -> In t (words (line D)).
Proof.
  intros D t H. unfold toks in H. rewrite <- (firstn_skipn line_words_max (words (line D))).
  apply in_or_app. left. exact H.
Qed.

Lemma toks_word : forall D t, In t (toks D) ->
  t <> [] /\ forall b, In b t -> bv_unsigned b <> 32 /\ bv_unsigned b <> 9 /\ bv_unsigned b <> 0.
Proof.
  intros D t H. apply toks_in in H.
  destruct (words_acc_spec (fun b => bv_unsigned b <> 0) (line D) [] (fun b H => False_ind _ H) (line_nonul D) t H)
    as [Hn Hb].
  split; [exact Hn|]. intros b Hi. destruct (Hb b Hi) as [Z0 S]. apply sep_false in S. destruct S as [S1 S2].
  split; [|split]; assumption.
Qed.

Lemma verb_is_m_token : forall t f, (forall b, In b t -> bv_unsigned b <> 32 /\ bv_unsigned b <> 9) ->
  verb_is_m t f = true <-> t = vfirst f.
Proof.
  intros t f Ht. assert (Tt : tfirst t = t) by (apply upto_all; intros b Hb; apply sep_false; exact (Ht b Hb)).
  unfold verb_is_m. rewrite Tt, andb_true_iff, Nat.eqb_eq, list_eqb_eq. split.
  - intros [L E]. rewrite <- L, firstn_all in E. exact E.
  - intros E. split; [rewrite E; reflexivity|]. rewrite <- E. apply firstn_all.
Qed.

Lemma number_m_nil : number_m [] = None.
Proof. reflexivity. Qed.

Lemma number_m_range : forall w v, number_m w = Some v -> -1000000 <= v <= 1000000.
Proof.
  intros w v. unfold number_m. destruct (signed_digits (dropw is_space w)) as [x|]; [|discriminate].
  destruct ((-1000000 <=? x) && (x <=? 1000000)) eqn:E; [|discriminate].
  intros H. injection H as <-. apply andb_true_iff in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

Lemma instance_verb_words : map vfirst instance_verb_formats = instance_verb_names.
Proof. reflexivity. Qed.

Lemma format_words :
  vfirst fmt_remove = verb_remove /\ vfirst fmt_quit = verb_quit /\ vfirst fmt_connect = verb_connect /\
  vfirst fmt_disconnect = verb_disconnect /\ vfirst fmt_preset_load = verb_preset_load /\
  vfirst fmt_patch_set = verb_patch_set.
Proof. repeat apply conj; reflexivity. Qed.
