(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia List.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Frame StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.

(* [comment removed for export] *)
Ltac lia_rel :=
  first [ solve [ hide_disj_all; Lia.lia ]
        | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; Lia.lia ] end ].

Ltac tslia_rel := first [ exact I | solve [lia_rel] | split; [ solve [lia_rel] | tslia_rel ] ].

Ltac disjoint_goal_rel :=
  cbv [disjoint_from fst snd];
  simpl_sizes_goal;
  tslia_rel.

(* [comment removed for export] *)
Ltac tlia_rel :=
  first [ solve [lia_rel]
        | Zify.zify; xlia zchecker
        | sf_unhide;
          first [ zify_prune_neg; Zify.zify; xlia zchecker
                | zify_prune_plain; Zify.zify; xlia zchecker
                | zify_prune_rel2; Zify.zify; xlia zchecker
                | Zify.zify; xlia zchecker ] ].

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From Ltac2 Require Import Ltac2.
#[global] Set Default Proof Mode "Classic".
Ltac lia_rel_pin := first [ solve [clear_unpinned; lia_rel] | pinned_lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 rec lrr_bigpos (p : constr) (d : int) : bool :=
  match Constr.Unsafe.kind p with
  | Constr.Unsafe.App f args =>
      if Int.equal (Array.length args) 1 then
        (if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref f reference:(xI) then lrr_bigpos (Array.get args 0) (Int.add d 1)
         else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref f reference:(xO) then lrr_bigpos (Array.get args 0) (Int.add d 1) else false)
      else false
  | Constr.Unsafe.Constructor _ _ => if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref p reference:(xH) then Int.ge d 8 else false
  | _ => false
  end.
Ltac2 rec lrr_lits (acc : constr list) (t : constr) : constr list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      if (if Int.equal (Array.length args) 1 then (if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref f reference:(Zpos) then true else OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref f reference:(Zneg)) else false) then
        (if lrr_bigpos (Array.get args 0) 0 then (if List.exist (Constr.equal t) acc then acc else t :: acc) else acc)
      else Array.fold_left lrr_lits (lrr_lits acc f) args
  | Constr.Unsafe.Cast c _ _ => lrr_lits acc c
  | Constr.Unsafe.Prod b body => lrr_lits (lrr_lits acc (Constr.Binder.type b)) body
  | _ => acc
  end.
Ltac2 lrr_ranked () : ident list :=
  let cands := List.map_filter (fun h => let (id, _, ty) := h in if lp_is_or ty then Some (id, ty) else None) (List.rev (Control.hyps ())) in
  let gv := lp_vars [] (Control.goal ()) in
  let gl := lrr_lits [] (Control.goal ()) in
  let scored := List.map (fun p => let (id, ty) := p in
                  let xl := lrr_lits [] ty in
                  (id, Int.add (lp_count_shared gv ty) (List.fold_left (fun n z => if List.exist (Constr.equal z) xl then Int.add n 1 else n) 0 gl))) cands in
  let mx := List.fold_left (fun m p => let (_, k) := p in if Int.gt k m then k else m) 0 scored in
  let rec go k acc := if Int.lt k 0 then acc else
      go (Int.sub k 1) (List.append acc (List.map_filter (fun p => let (id, j) := p in if Int.equal j k then Some id else None) scored)) in
  go mx [].
(* [comment removed for export] *)
Ltac2 lrr_lia_rel () : unit :=
  if lp_try (fun () => ltac1:(solve [ hide_disj_all; Lia.lia ])) then () else
  let rec go (l : ident list) : unit :=
    match l with
    | [] => Control.zero (Tactic_failure None)
    | x :: r => if lp_try (fun () => if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zt_is_local x then ltac1:(h |- solve [ hide_disj_but h; Zify.zify; xlia zchecker ]) (Ltac1.of_ident x)
                                     else ltac1:(h |- solve [ hide_disj_but h; Lia.lia ]) (Ltac1.of_ident x)) then () else go r
    end in
  go (lrr_ranked ()).
Ltac lia_rel ::= ltac2:(Control.enter lrr_lia_rel).

(* [comment removed for export] *)
Ltac slia_rel := first [ exact I | solve [lia_rel] | Lia.lia | split; [ first [ solve [lia_rel] | Lia.lia ] | exact I ] ].

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia Stdlib.Lists.List.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.

(* [comment removed for export] *)
Ltac lia_rel :=
  first [ solve [ hide_disj_all; Lia.lia ]
        | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; Lia.lia ] end ].

Ltac tslia_rel := first [ exact I | solve [lia_rel] | split; [ solve [lia_rel] | tslia_rel ] ].

Ltac disjoint_goal_rel :=
  cbv [disjoint_from fst snd];
  simpl_sizes_goal;
  tslia_rel.

(* [comment removed for export] *)
Ltac tlia_rel :=
  first [ solve [lia_rel]
        | Zify.zify; xlia zchecker
        | sf_unhide;
          first [ zify_prune_neg; Zify.zify; xlia zchecker
                | zify_prune_plain; Zify.zify; xlia zchecker
                | zify_prune_rel2; Zify.zify; xlia zchecker
                | Zify.zify; xlia zchecker ] ].

(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Ltac lia_rel_pin := first [ solve [clear_unpinned; lia_rel] | pinned_lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 rec lrr_bigpos (p : constr) (d : int) : bool :=
  match Constr.Unsafe.kind p with
  | Constr.Unsafe.App f args =>
      if Int.equal (Array.length args) 1 then
        (if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref f reference:(xI) then lrr_bigpos (Array.get args 0) (Int.add d 1)
         else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref f reference:(xO) then lrr_bigpos (Array.get args 0) (Int.add d 1) else false)
      else false
  | Constr.Unsafe.Constructor _ _ => if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref p reference:(xH) then Int.ge d 8 else false
  | _ => false
  end.
Ltac2 rec lrr_lits (acc : constr list) (t : constr) : constr list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      if (if Int.equal (Array.length args) 1 then (if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref f reference:(Zpos) then true else OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref f reference:(Zneg)) else false) then
        (if lrr_bigpos (Array.get args 0) 0 then (if List.exist (Constr.equal t) acc then acc else t :: acc) else acc)
      else Array.fold_left lrr_lits (lrr_lits acc f) args
  | Constr.Unsafe.Cast c _ _ => lrr_lits acc c
  | Constr.Unsafe.Prod b body => lrr_lits (lrr_lits acc (Constr.Binder.type b)) body
  | _ => acc
  end.
Ltac2 lrr_ranked () : ident list :=
  let cands := List.map_filter (fun h => let (id, _, ty) := h in if lp_is_or ty then Some (id, ty) else None) (List.rev (Control.hyps ())) in
  let gv := lp_vars [] (Control.goal ()) in
  let gl := lrr_lits [] (Control.goal ()) in
  let scored := List.map (fun p => let (id, ty) := p in
                  let xl := lrr_lits [] ty in
                  (id, Int.add (lp_count_shared gv ty) (List.fold_left (fun n z => if List.exist (Constr.equal z) xl then Int.add n 1 else n) 0 gl))) cands in
  let mx := List.fold_left (fun m p => let (_, k) := p in if Int.gt k m then k else m) 0 scored in
  let rec go k acc := if Int.lt k 0 then acc else
      go (Int.sub k 1) (List.append acc (List.map_filter (fun p => let (id, j) := p in if Int.equal j k then Some id else None) scored)) in
  go mx [].
(* [comment removed for export] *)
Ltac2 lrr_lia_rel () : unit :=
  if lp_try (fun () => ltac1:(solve [ hide_disj_all; Lia.lia ])) then () else
  let rec go (l : ident list) : unit :=
    match l with
    | [] => Control.zero (Tactic_failure None)
    | x :: r => if lp_try (fun () => if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zt_is_local x then ltac1:(h |- solve [ hide_disj_but h; Zify.zify; xlia zchecker ]) (Ltac1.of_ident x)
                                     else ltac1:(h |- solve [ hide_disj_but h; Lia.lia ]) (Ltac1.of_ident x)) then () else go r
    end in
  go (lrr_ranked ()).
Ltac lia_rel ::= ltac2:(Control.enter lrr_lia_rel).

(* [comment removed for export] *)
Ltac slia_rel := first [ exact I | solve [lia_rel] | Lia.lia | split; [ first [ solve [lia_rel] | Lia.lia ] | exact I ] ].
End TwB.
