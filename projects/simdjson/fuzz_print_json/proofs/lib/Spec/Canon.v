(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition evw (fd : Z) (bs : list Z) : list event :=
  map (fun b => WriteEv (Z_to_bv 64 fd) (Z_to_bv 8 b)) bs.

Record ctrace : Type := mkCT { ct_fd : Z; ct_bytes : list Z; ct_code : Z }.

Definition ct_events (fs : Fs) (ct : ctrace) : list event :=
  evw (ct_fd ct) (ct_bytes ct) ++ [ExitEv (Z_to_bv 64 (ct_code ct)) fs].

Definition msg_usage (argv0 : list Z) : list Z := str "usage: " ++ argv0 ++ str " INPUT" ++ [10].
Definition msg_cannot_open (path : list Z) : list Z := str "cli: cannot open " ++ path ++ [10].
Definition msg_read_error (path : list Z) : list Z := str "cli: read error on " ++ path ++ [10].
Definition msg_too_big : list Z := str "cli: input >= 67108864 bytes, refused" ++ [10].
Definition msg_short_hdr : list Z := str "cli: input shorter than header" ++ [10].
Definition msg_cfg_overrun : list Z := str "cli: config_len overruns input" ++ [10].

Definition zeros_out (calls : nat) : list Z := concat (repeat [48; 10] calls).

Definition cfg_len (data : list Z) : Z := Z.land (znth data 0 + znth data 1 * 256) 0x7fff.

Definition cfg_calls (data : list Z) : nat :=
  let cfg := if 0 <? cfg_len data then znth data 2 else 0 in
  Z.to_nat (Z.land cfg 3 + 1).

Definition file_trace (data : list Z) : ctrace :=
  let len := zlength data in
  if 67108864 <=? len then mkCT 2 msg_too_big 2
  else if len <? 6 then mkCT 2 msg_short_hdr 2
  else if len <? 6 + cfg_len data then mkCT 2 msg_cfg_overrun 2
  else mkCT 1 (zeros_out (cfg_calls data)) 0.

Inductive oclass : Type := OCFail | OCDir | OCFile (data : list byte).

Definition open_class (path : list Z) (fs : Fs) : oclass :=
  let p := map (Z_to_bv 8) path in
  if (path_max <=? length p)%nat then OCFail
  else match p with
       | [] => OCFail
       | _ :: _ => if path_eqb p dot_path then OCDir
                   else match fs_lookup fs p with
                        | None => OCFail
                        | Some data => OCFile data
                        end
       end.

Definition ctrace_of (argv : list (list Z)) (fs : Fs) (ok : bool) : ctrace :=
  if negb (Z.of_nat (length argv) =? 2) then mkCT 2 (msg_usage (nth 0 argv [])) 2
  else
    let path := nth 1 argv [] in
    match (if ok then open_class path fs else OCFail) with
    | OCFail => mkCT 2 (msg_cannot_open path) 2
    | OCDir => mkCT 2 (msg_read_error path) 2
    | OCFile data => file_trace (map bv_unsigned data)
    end.

Definition canon_traces (argv : list (list Z)) (fs : Fs) : list ctrace :=
  [ctrace_of argv fs false; ctrace_of argv fs true].

Definition canonT (argv : list (list Z)) (fs : Fs) : list event -> Prop :=
  fun tr => exists ct, In ct (canon_traces argv fs) /\ is_prefix tr (ct_events fs ct).

Lemma canonT_iff : forall argv fs tr,
  canonT argv fs tr <-> exists ok, is_prefix tr (ct_events fs (ctrace_of argv fs ok)).
Proof.
  intros argv fs tr. split.
  - intros (ct & Hin & Hp). cbn in Hin. destruct Hin as [<-|[<-|[]]]; eauto.
  - intros ([|] & Hp); eexists; split; [|exact Hp| |exact Hp]; cbn; auto.
Qed.

Lemma canonT_nil : forall argv fs, canonT argv fs [].
Proof. intros. exists (ctrace_of argv fs false). split; [left; reflexivity| apply is_prefix_nil]. Qed.

Lemma canonT_pclosed : forall argv fs tr tr',
  canonT argv fs tr -> is_prefix tr' tr -> canonT argv fs tr'.
Proof.
  intros argv fs tr tr' (ct & Hin & Hp) Hp'. exists ct. split; [exact Hin|].
  eapply is_prefix_trans; eassumption.
Qed.

Lemma canonT_max : forall argv fs ok, canonT argv fs (ct_events fs (ctrace_of argv fs ok)).
Proof. intros argv fs ok. apply canonT_iff. exists ok. apply is_prefix_refl. Qed.

Lemma ctrace_of_fail : forall argv fs ok,
  Z.of_nat (length argv) = 2 -> open_class (nth 1 argv []) fs = OCFail ->
  ctrace_of argv fs ok = mkCT 2 (msg_cannot_open (nth 1 argv [])) 2.
Proof.
  intros argv fs ok Hl Hc. unfold ctrace_of. rewrite Hl. cbn [Z.eqb negb].
  destruct ok; [rewrite Hc|]; reflexivity.
Qed.

Lemma evw_app : forall fd l1 l2, evw fd (l1 ++ l2) = evw fd l1 ++ evw fd l2.
Proof. intros. unfold evw. apply map_app. Qed.

Lemma zeros_out_S : forall n, zeros_out (S n) = [48; 10] ++ zeros_out n.
Proof. reflexivity. Qed.

Example msg_usage_ex : msg_usage (str "prog") = str "usage: prog INPUT" ++ [10].
Proof. vm_compute. reflexivity. Qed.
Example msg_too_big_len : zlength msg_too_big = 38.
Proof. vm_compute. reflexivity. Qed.
Example file_trace_ex :
  file_trace [1; 0; 3; 0; 0; 0; 0] = mkCT 1 [48; 10; 48; 10; 48; 10; 48; 10] 0.
Proof. vm_compute. reflexivity. Qed.
Example file_trace_ex2 : file_trace [1; 0; 3; 0; 0] = mkCT 2 msg_short_hdr 2.
Proof. vm_compute. reflexivity. Qed.
Example file_trace_ex3 : file_trace [9; 0; 3; 0; 0; 0; 0] = mkCT 2 msg_cfg_overrun 2.
Proof. vm_compute. reflexivity. Qed.
