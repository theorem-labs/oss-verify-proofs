(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition evw (fd : Z) (bs : list Z) : list event :=
  map (fun b => WriteEv (Z_to_bv 64 fd) (Z_to_bv 8 b)) bs.

(* [comment removed for export] *)
Record ctrace : Type := mkCT { ct_fd : Z; ct_bytes : list Z; ct_code : Z }.

Definition ct_events (fs : Fs) (ct : ctrace) : list event :=
  evw (ct_fd ct) (ct_bytes ct) ++ [ExitEv (Z_to_bv 64 (ct_code ct)) fs].

(* [comment removed for export] *)

Definition msg_usage (argv0 : list Z) : list Z := str "usage: " ++ argv0 ++ str " INPUT" ++ [10].
Definition msg_cannot_open (path : list Z) : list Z := str "cli: cannot open " ++ path ++ [10].
Definition msg_read_error (path : list Z) : list Z := str "cli: read error on " ++ path ++ [10].
Definition msg_too_big : list Z := str "cli: input >= 67108864 bytes, refused" ++ [10].
Definition msg_short_hdr : list Z := str "cli: input shorter than header" ++ [10].
Definition msg_cfg_overrun : list Z := str "cli: config_len overruns input" ++ [10].

(* [comment removed for export] *)
Definition zeros_out (calls : nat) : list Z := concat (repeat [48; 10] calls).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cfg_len (data : list Z) : Z := Z.land (znth data 0 + znth data 1 * 256) 0x7fff.

(* [comment removed for export] *)
Definition cfg_calls (data : list Z) : nat :=
  let cfg := if 0 <? cfg_len data then znth data 2 else 0 in
  Z.to_nat (Z.land cfg 3 + 1).

Definition file_trace (data : list Z) : ctrace :=
  let len := zlength data in
  if 67108864 <=? len then mkCT 2 msg_too_big 2
  else if len <? 6 then mkCT 2 msg_short_hdr 2
  else if len <? 6 + cfg_len data then mkCT 2 msg_cfg_overrun 2
  else mkCT 1 (zeros_out (cfg_calls data)) 0.

(* [comment removed for export] *)
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

(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition canonT (argv : list (list Z)) (fs : Fs) : list event -> Prop :=
  fun tr => exists ct, In ct (canon_traces argv fs) /\ is_prefix tr (ct_events fs ct).

(* [comment removed for export] *)

Lemma canonT_iff : forall argv fs tr,
  canonT argv fs tr <-> exists ok, is_prefix tr (ct_events fs (ctrace_of argv fs ok)).
Proof.
  intros argv fs tr. split.
  - intros (ct & Hin & Hp). cbn in Hin. destruct Hin as [<-|[<-|[]]]; eauto.
  - intros ([|] & Hp); eexists; split; [|exact Hp| |exact Hp]; cbn; auto.
Qed.

Lemma canonT_nil : forall argv fs, canonT argv fs [].
Proof. intros. exists (ctrace_of argv fs false). split; [left; reflexivity| apply is_prefix_nil]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma evw_app : forall fd l1 l2, evw fd (l1 ++ l2) = evw fd l1 ++ evw fd l2.
Proof. intros. unfold evw. apply map_app. Qed.

Lemma zeros_out_S : forall n, zeros_out (S n) = [48; 10] ++ zeros_out n.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
