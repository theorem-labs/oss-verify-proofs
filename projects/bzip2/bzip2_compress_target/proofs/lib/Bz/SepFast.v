(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require SepLinT.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzdFast RelLia.
From Ltac2 Require Ltac2.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac sep_bounds := first [ tlia1 | sf_unhide; tlia1 ].

Ltac sep_tac_u :=
  lazymatch goal with |- (?e1 <= ?a \/ ?e2 <= ?A) =>
    let bA := sep_base A in let ba := sep_base a in
    match goal with
    | H : id (?b1 <= ?a2 \/ ?b2 <= ?a1) |- _ =>
        let c1 := sep_base a1 in let c2 := sep_base a2 in
        first [ sep_same c1 bA; sep_same c2 ba; apply (sep_use b1 a2 b2 a1 e1 a e2 A H); sep_bounds
              | sep_same c2 bA; sep_same c1 ba; apply (sep_use' b1 a2 b2 a1 e1 a e2 A H); sep_bounds ]
    end
  end.

(* [comment removed for export] *)
Ltac tlia_case := first [ solve [ zify_prune_plain; Zify.zify; xlia zchecker ] | solve [ Zify.zify; xlia zchecker ] ].
Module SD.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 candidates () : ident list :=
    let g := BzdFast.BF.atoms [] (Control.goal ()) in
    let scored := List.map_filter (fun h => let (id, body, ty) := h in
        match body with
        | Some _ => None
        | None =>
            lazy_match! ty with
            | _ \/ _ => let (sh, un) := BzdFast.BF.count_shared (BzdFast.BF.atoms [] ty) g 0 0 in
                        if Int.equal sh 0 then None else Some (id, sh, un)
            | _ => None
            end
        end) (Control.hyps ()) in
    let better (a : ident * int * int) (b : ident * int * int) : int :=
      let (_, s1, u1) := a in let (_, s2, u2) := b in
      if Int.gt s1 s2 then -1 else if Int.lt s1 s2 then 1 else Int.compare u1 u2 in
    List.map (fun x => let (id, _, _) := x in id) (List.sort better scored).
  Ltac2 targeted () : unit :=
    let ids := BzdFast.BF.firstn 2 (candidates ()) in
    Control.once (fun () => BzdFast.BF.try_each ids (fun id =>
      let h := Control.hyp id in
      ltac1:(h |- solve [ destruct h as [h|h]; tlia_case ]) (Ltac1.of_constr h))).
End SD.
Ltac tlia_targeted := ltac2:(Control.enter SD.targeted).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac tlia_dr := first [ solve [ SepLinT.sl_tslia ltac:(idtac; Zify.zify; xlia zchecker) ]
                      | RelLia.rel_prune; Zify.zify; xlia zchecker
                      | Zify.zify; xlia zchecker
                      | sf_unhide;
                        first [ tlia_targeted
                              | zify_prune_neg; Zify.zify; xlia zchecker
                              | zify_prune_plain; Zify.zify; xlia zchecker
                              | lia ] ].
