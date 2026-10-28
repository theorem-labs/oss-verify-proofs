(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Asn1Aux LiaTuning.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
Import ListNotations.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 FSet FMap.
Set Default Proof Mode "Classic".



(* [comment removed for export] *)
Ltac lia_t12 := first [ LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Ltac2 ff_is_local_id (id : ident) : bool := match Env.get [id] with None => true | Some _ => false end.
Ltac2 ff_is_or (ty : constr) : bool := lazy_match! ty with | _ \/ _ => true | _ => false end.
(* [comment removed for export] *)
Ltac2 ff_disj_ids () : ident list * ident list :=
  List.fold_left (fun acc h => let (l, s) := acc in let (id, body, ty) := h in
    if ff_is_or ty then
      (match body with
       | Some _ => (l, id :: s)
       | None => if ff_is_local_id id then (id :: l, s) else (l, id :: s)
       end)
    else acc)
    ([], []) (Control.hyps ()).
Ltac2 ff_revert_local_disjs () : unit :=
  let (l, _) := ff_disj_ids () in
  List.iter (fun id => match Control.case (fun () => Std.revert [id]) with Val _ => () | Err _ => () end) l.
(* [comment removed for export] *)
Ltac2 ff_clear_ids (ids : ident list) : unit :=
  List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Val _ => () | Err _ => () end) ids.
Ltac2 ff_solve (tac : unit -> unit) : unit := tac (); Control.enter (fun () => Control.zero (Tactic_failure None)).
Ltac2 rec ff_try_each (ids : ident list) (others : ident -> ident list) (tac : unit -> unit) : unit :=
  match ids with
  | [] => Control.zero (Tactic_failure (Some (Message.of_string "ff5: no single local disjunction proves it")))
  | id :: rest => Control.plus (fun () => Control.once (fun () => ff_clear_ids (others id); ff_solve tac))
                               (fun _ => ff_try_each rest others tac)
  end.
Ltac2 ff_attempts () : unit :=
  let (l, s) := ff_disj_ids () in
  let t12 () := ltac1:(lia_t12) in
  Control.plus (fun () => Control.once (fun () => ff_clear_ids (List.append l s); ff_solve t12))            (* [comment removed for export] *)
  (fun _ => Control.plus
    (fun () => ff_try_each (List.rev l) (fun id => List.append s (List.filter (fun j => Bool.neg (Ident.equal j id)) l)) t12)   (* [comment removed for export] *)
    (fun _ => match s with
              | [] => Control.zero (Tactic_failure (Some (Message.of_string "ff5: attempts exhausted")))
              | _ :: _ => Control.once (fun () => ff_clear_ids l; ff_solve t12)                           (* [comment removed for export] *)
              end)).
Ltac ff_revert_local_disjs := ltac2:(Control.enter ff_revert_local_disjs).
Ltac ff_attempts := ltac2:(Control.enter (fun () => Control.once ff_attempts)).
Ltac2 ff_clear_section_disjs () : unit := let (_, s) := ff_disj_ids () in ff_clear_ids s.
Ltac ff_clear_section_disjs := ltac2:(Control.enter ff_clear_section_disjs).
Ltac lia_dsel := ff_revert_local_disjs; LiaTuning.zify_prune; intros; ff_attempts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ff5_attemptA := ltac2:(Control.enter (fun () => let (l, s) := ff_disj_ids () in ff_clear_ids (List.append l s))); LiaTuning.zify_prune; lia_t12.
(* [comment removed for export] *)
Ltac2 ff_has_section_disj () : bool := let (_, s) := ff_disj_ids () in match s with [] => false | _ :: _ => true end.
Ltac ff5_pqlia :=
  first [ ltac2:(Control.enter (fun () => if ff_has_section_disj () then () else Control.zero (Tactic_failure None)));
          prune_disj; clear_mods; solve [ ff5_attemptA ]
        | prune_disj; clear_mods; lia ].


(* [comment removed for export] *)
Ltac ff5_rlia := clear_disj; repeat match goal with H : ~ _ |- _ => clear H end; clear_mods; LiaTuning.zify_prune; lia_t12.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ff5_overlap A2 n2 a len :=
  let b1 := base_of A2 in let b2 := base_of a in constr_eq b1 b2;
  assert_succeeds (assert (a < A2 + n2 /\ A2 < a + len) by (clear; Zify.zify; xlia zchecker)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 rec ffn_vars (acc : ident FSet.t) (t : constr) : ident FSet.t :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var id => FSet.add id acc
  | Constr.Unsafe.App h args => Array.fold_left ffn_vars (ffn_vars acc h) args
  | Constr.Unsafe.Cast c _ _ => ffn_vars acc c
  | _ => acc
  end.
Ltac2 ffn_keep_near (t : constr) : unit :=
  let seed := ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Some _ => acc
      | None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if Bool.and (LiaTuning.zf_plain_arith e ty) (Bool.neg (FSet.is_empty (FSet.inter seed (ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))))
             then (ids, cache) else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Val _ => ()
              | Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Val _ => () | Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t := let f := ltac2:(t |- ffn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac ff5_overlap_ctx A2 n2 a len :=
  assert_succeeds (assert (a < A2 + n2 /\ A2 < a + len)
    by (ff_keep_near constr:((A2, a)); clear_mods; first [ LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker ])).
(* [comment removed for export] *)
Ltac ff5_drop_if_overlap A2 n2 a len :=
  tryif ff5_overlap A2 n2 a len then fail 1 "ff5: overlap (context-free)"
  else tryif ff5_overlap_ctx A2 n2 a len then fail 1 "ff5: overlap (pruned context)"
  else fail.

(* [comment removed for export] *)
Ltac ff5_apart_cc A2 n2 a len :=
  first [ assumption
        | dt_apart_sb
        | solve [ clear; lia ]
        | tryif ff5_overlap A2 n2 a len then fail 1 "ff5: overlap (context-free)" else fail
        | let b1 := base_of A2 in let b2 := base_of a in lia_2bases b1 b2
        | pqlia ].

(* [comment removed for export] *)
Ltac ff5_solve_apart :=
  lazymatch goal with
  | |- ?A2 + ?n2 <= ?a \/ ?a + ?len <= ?A2 =>
      tryif store_is_shadow a
      then first [ tryif ff5_overlap A2 n2 a len then fail 1 else fail
                 | tryif base_is_shadow A2 then apart_ss A2 n2 a len else apart_cs A2 n2 a len ]
      else (tryif base_is_shadow A2
            then first [ tryif ff5_overlap A2 n2 a len then fail 1 else fail | apart_sc A2 n2 a len ]
            else ff5_apart_cc A2 n2 a len)
  end.
(* [comment removed for export] *)
Ltac ff5_solve_apart0 :=
  lazymatch goal with
  | |- ?n = 0 \/ ?A2 + _ <= ?a \/ _ + ?len <= _ =>
      tryif first [ store_is_shadow a | base_is_shadow A2 ]
      then first [ assumption
                 | right; solve_apart
                 | lazymatch n with
                   | context [length ?cs] => destruct cs; [ left; reflexivity | right; cbn [length] in *; solve_apart ]
                   end ]
      else first [ assumption
                 | solve [ clear; lia ]
                 | tryif ff5_overlap A2 n a len then fail 1 "ff5: overlap (context-free)" else fail
                 | let b1 := base_of A2 in let b2 := base_of a in lia_2bases b1 b2
                 | lazymatch n with context [length ?cs] => let b2 := base_of a in lia_2bases (length cs) b2 end
                 | pqlia
                 | right; solve_apart
                 | lazymatch n with
                   | context [length ?cs] => destruct cs; [ left; reflexivity | right; cbn [length] in *; solve_apart ]
                   end ]
  | |- _ => solve_apart
  end.
(* [comment removed for export] *)
Ltac ff5_solve_disjoint := cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; repeat split;
  lazymatch goal with
  | |- ?A2 + ?n2 <= ?lo \/ ?hi <= _ =>
      first [ assumption
            | solve [ clear; lia ]
            | ff5_drop_if_overlap A2 n2 lo (hi - lo)
            | let b1 := base_of A2 in let b2 := base_of lo in lia_2bases b1 b2
            | pqlia ]
  | |- _ => first [ assumption | solve [ clear; lia ] | pqlia ]
  end.

(* [comment removed for export] *)
Ltac ff5_sub_fp_one Hx :=
  let C := fresh "C" in
  intro C;
  let rec go H :=
    lazymatch type of H with
    | True => fail
    | _ /\ _ =>
        let N := fresh "N" in let H2 := fresh "Hx" in
        destruct H as [N H2];
        first [ exact (N C) | clear N; go H2 | apply N; clear N H2; split; ff5_rlia ]
    | _ => first [ exact (H C) | apply H; clear H; split; ff5_rlia ]
    end in
  go Hx.
Ltac ff5_sub_fp_conj Hx :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; [ ff5_sub_fp_one Hx | ff5_sub_fp_conj Hx ]
  | |- _ => ff5_sub_fp_one Hx
  end.
Ltac ff5_sub_fp :=
  unfold sub_fp; cbn [outside];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; ff5_sub_fp_conj Hx.

(* [comment removed for export] *)
Ltac ff5_transport_after_call segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport0 segs W m m' A2 bs2) in H;
              [ | exact MU
                | first [ right; solve_disjoint
                        | destruct bs2; [ left; reflexivity | right; cbn [length] in *; solve_disjoint ] ] ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | solve_disjoint ]
            | idtac "note: dropping stk across call (not provably disjoint from callee footprint):" H; clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ ff5_sub_fp | unfold sub_fp; cbn [outside]; intros; prune_disj; clear_mods; lia ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
