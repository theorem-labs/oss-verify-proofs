From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
Import ListNotations.
Open Scope Z_scope.

Inductive vroute : Type :=
| RAdd | RDget | RPget | RRemove | RWlist | RIinfo | RReset | RQclear | RPolicy | RLv2 | RPool | REnv
| RChain | RChclear | RPinset | RPinacc | RPinclr | RQuit | RLedger (led : Z) | RInst | RConn | RBroad.

Definition route_cd (v : list byte) (args : list (list byte)) : vroute :=
  match args with
  | [_; _] => if verb_is_m v fmt_connect || verb_is_m v fmt_disconnect then RConn else RBroad
  | _ => RBroad
  end.

Definition route_conn (v : list byte) (args : list (list byte)) : vroute :=
  match args with
  | [] => RBroad
  | _ :: _ => if is_instance_verb v then RInst else route_cd v args
  end.

Definition route_tail (v : list byte) (args : list (list byte)) : vroute :=
  match ledger_of v instance_info_verbs with
  | Some led => RLedger led
  | None => route_conn v args
  end.

Definition route_mid (v : list byte) (args : list (list byte)) : vroute :=
  if list_eqb v verb_worker_list then RWlist else
  if list_eqb v verb_instance_info then RIinfo else
  if list_eqb v verb_supervisor_reset then RReset else
  if list_eqb v verb_quarantine_clear then RQclear else
  if list_eqb v verb_policy_set then RPolicy else
  if list_eqb v verb_lv2_worker_set then RLv2 else
  if list_eqb v verb_pool_config then RPool else
  if list_eqb v verb_worker_env then REnv else
  if list_eqb v verb_chain then RChain else
  if list_eqb v verb_chain_clear then RChclear else
  if list_eqb v verb_pin_set then RPinset else
  if list_eqb v verb_pin_accept then RPinacc else
  if list_eqb v verb_pin_clear then RPinclr else
  if verb_is_m v fmt_quit then RQuit else
  route_tail v args.

Definition route (tk : list (list byte)) : vroute :=
  match tk with
  | [] => RBroad
  | v :: args =>
    if list_eqb v verb_add then RAdd else
    if list_eqb v verb_descriptor_get then RDget else
    if list_eqb v verb_panel_get then RPget else
    if verb_is_m v fmt_remove then RRemove else
    route_mid v args
  end.

Definition route_pc (r : vroute) : Z :=
  match r with
  | RAdd => 0x176d4 | RDget => 0x176f0 | RPget => 0x17710 | RRemove => 0x177f8 | RWlist => 0x1778c
  | RIinfo => 0x177d4 | RReset => 0x1789c | RQclear => 0x178c0 | RPolicy => 0x178f8 | RLv2 => 0x17940
  | RPool => 0x17970 | REnv => 0x179ac | RChain => 0x179e8 | RChclear => 0x179f8 | RPinset => 0x17a28
  | RPinacc => 0x17a3c | RPinclr => 0x17a5c | RQuit => 0x176a0 | RLedger _ => 0x17bb4 | RInst => 0x17b8c
  | RConn => 0x17bf8 | RBroad => 0x17c2c
  end.

Definition plan_at (r : vroute) (atoi : list byte -> Z) (ln : list byte) (tk : list (list byte)) : step :=
  match tk with
  | [] => reject
  | v :: args =>
    match r with
    | RAdd => add_m atoi args
    | RDget => match args with [a] => SCall (descriptors_get a) | _ => reject end
    | RPget => match args with [a] => SCall (descriptors_panel_get a) | _ => reject end
    | RRemove =>
        match args with
        | [a] => if atoi a =? -1 then SCall sup_remove_all else SCall (sup_remove (atoi a))
        | _ => reject
        end
    | RWlist => match args with [] => SCall sup_worker_list | _ => reject end
    | RIinfo => match args with [a] => SCall (sup_instance_info (atoi a)) | _ => reject end
    | RReset =>
        match args with
        | [] => SCall (sup_reset word_all)
        | [a] => SCall (sup_reset a)
        | _ => reject
        end
    | RQclear => match args with [a] => SCall (sup_quarantine_clear a) | _ => reject end
    | RPolicy => match args with [a; b] => SCall (sup_policy_set a b) | _ => reject end
    | RLv2 => match args with [a; b] => SCall (sup_lv2_worker_set a b) | _ => reject end
    | RPool => match args with [a; b] => SCall (sup_pool_config a (atoi b)) | _ => reject end
    | REnv => match args with [a; b; c] => SCall (sup_worker_env a b c) | _ => reject end
    | RChain => chain_words_m args
    | RChclear =>
        match args with
        | [a] => match number_m a with Some id => SCall (sup_chain_clear id) | None => reject end
        | _ => reject
        end
    | RPinset => pin_set_words_m ln args
    | RPinacc => match args with [a] => SCall (sup_pin_accept a) | _ => reject end
    | RPinclr => match args with [a] => SPinClear a | _ => reject end
    | RQuit => match args with [] => SQuit | _ => reject end
    | RLedger led => SCall (sup_instance_verb ln led)
    | RInst => match args with a :: _ => SCall (sup_call (atoi a) ln) | [] => reject end
    | RConn => match args with [a; b] => SCall (sup_connect v ln a b) | _ => reject end
    | RBroad => SBroadcast ln tk
    end
  end.

Lemma plan_route : forall atoi ln tk, tk <> [] -> plan atoi ln tk = plan_at (route tk) atoi ln tk.
Proof.
  intros atoi ln [|v args] H; [congruence|]. unfold plan, route, route_mid, route_tail, route_conn, route_cd.
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b; [cbn [plan_at]; reflexivity|]
  end.
  destruct (ledger_of v instance_info_verbs) as [led|]; [reflexivity|].
  destruct args as [|a rest]; [reflexivity|].
  destruct (is_instance_verb v); [reflexivity|].
  destruct rest as [|b [|c rest]]; try reflexivity.
  destruct (verb_is_m v fmt_connect || verb_is_m v fmt_disconnect); reflexivity.
Qed.

Lemma words_acc_len : forall l cur w, In w (words_acc cur l) -> (length w <= length cur + length l)%nat.
Proof.
  induction l as [|x l IH]; intros cur w Hw; cbn [words_acc] in Hw.
  - destruct cur as [|y cur']; [destruct Hw|]. destruct Hw as [<-|[]]. cbn [length]. lia.
  - cbn [length]. destruct (is_sep x).
    + destruct cur as [|y cur'].
      * pose proof (IH [] w Hw) as L. cbn [length] in L. lia.
      * destruct Hw as [<-|Hw]; [lia|]. pose proof (IH [] w Hw) as L. cbn [length] in L. lia.
    + pose proof (IH (cur ++ [x]) w Hw) as L. rewrite length_app in L. cbn [length] in L. lia.
Qed.

Lemma dropw_len : forall p l, (length (dropw p l) <= length l)%nat.
Proof. intros p l; induction l as [|x l IH]; cbn [dropw length]; [lia|]. destruct (p x); cbn [length]; lia. Qed.

Lemma upto_len : forall p l, (length (upto p l) <= length l)%nat.
Proof. intros p l; induction l as [|x l IH]; cbn [upto length]; [lia|]. destruct (p x); cbn [length]; lia. Qed.

Lemma line_len : forall D, (length (line D) <= length D)%nat.
Proof.
  intros D. unfold line, trim, upto0. rewrite length_rev. pose proof (dropw_len is_trail (rev (upto (fun b => bv_unsigned b =? 0) D))) as L1.
  rewrite length_rev in L1. pose proof (upto_len (fun b => bv_unsigned b =? 0) D). lia.
Qed.

Lemma toks_len : forall D w, In w (toks D) -> (length w <= length D)%nat.
Proof.
  intros D w H. apply toks_in in H. unfold words in H. pose proof (words_acc_len (line D) [] w H) as L.
  pose proof (line_len D). cbn [length] in L. lia.
Qed.
