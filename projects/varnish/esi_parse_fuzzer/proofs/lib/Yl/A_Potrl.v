(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac keep_bundles :=
  let rec go acc :=
    match goal with
    | H : context [ (8 * (sh _ - 2147450880))%Z ] |- _ =>
        lazymatch acc with context [H] => fail | _ => idtac end;
        go constr:(conj H acc)
    | H : (17594064011264 <= sh alloc_ceiling)%Z |- _ =>
        lazymatch acc with context [H] => fail | _ => idtac end;
        go constr:(conj H acc)
    | H : (sh alloc_ceiling <= SHMAX)%Z |- _ =>
        lazymatch acc with context [H] => fail | _ => idtac end;
        go constr:(conj H acc)
    | _ => let rec gen t := lazymatch t with conj ?H ?r => generalize H; gen r | _ => idtac end in gen acc
    end in
  go constr:(I).
(* [comment removed for export] *)

(* [comment removed for export] *)
Section Plain.
  Context {Clg : Ceiling} (L : clayout) {AI : AsanAlloc L}.
  Lemma sh_top_le' : forall p n, 0 <= p -> 0 <= n -> p + n <= alloc_ceiling -> sh p + (n + 7) / 8 <= sh alloc_ceiling.
  Proof. intros p n Hp Hn H. pose proof alloc_ceiling_mod16 as M. unfold sh. Z.div_mod_to_equations. lia. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Plain.

(* [comment removed for export] *)
Ltac norm_divs H :=
  repeat match type of H with
  | context [ ((?a + 7) / 8)%Z ] =>
      lazymatch a with Z0 => idtac | Zpos _ => idtac end;
      let k := eval vm_compute in ((a + 7) / 8)%Z in change ((a + 7) / 8)%Z with k in H
  end.

(* [comment removed for export] *)
Ltac all_app_facts ::=
  lazymatch goal with
  | _ : v16K |- _ => idtac
  | |- _ => let M := fresh "V16M" in let K := fresh "V16K" in pose proof v16K_holds as M; pose proof M as K; unfold v16K in K;
            try (let C1 := fresh "V16C" in pose proof sh_ceiling_ge as C1; let C2 := fresh "V16C" in pose proof sh_ceiling_le_SHMAX as C2)
  end;
  repeat match goal with
  | H : app_range ?L ?p ?n /\ (?n <= 64512 -> ?hb <= ?p) /\ (_ -> ?ih <= ?p) |- _ =>
      (* [comment removed for export] *)
      let Hh := fresh H "_h" in let Ha := fresh H "_a" in let Hl := fresh H "_l" in let Hi := fresh H "_ih" in let sx := fresh "sx" in
      destruct H as (Ha & Hh & Hi);
      first [ specialize (Hh ltac:(clear; lia)); unfold kHighMemBeg in Hh; rename Hh into H; clear Hi;
              pose proof (app_lin_high L p n H Ha) as Hl;
              (let hi := eval lazy in (cl_image_hi L) in try change (cl_image_hi L) with hi in Hl);
              try (cbv delta [HFSIZE] in Hl); norm_divs Hl; app_lin_norm Hl n;
              change (app_rangeF L p n) in Ha
            | clear Hh; specialize (Hi ltac:(clear; lazy; lia));
              destruct (app_lin_img L p n Hi Ha) as (sx & H); clear Hi;
              (let hi := eval lazy in (cl_image_hi L) in try change (cl_image_hi L) with hi in H);
              try (cbv delta [HFSIZE] in H); norm_divs H; app_lin_norm H n;
              change (app_rangeF L p n) in Ha
            | clear Hi; rename Ha into H ]
  | H : app_range ?L ?p ?n /\ (?n <= 64512 -> ?hb <= ?p) |- _ =>
      (* [comment removed for export] *)
      let Hh := fresh H "_h" in let Ha := fresh H "_a" in let Hl := fresh H "_l" in
      destruct H as [Ha Hh];
      first [ specialize (Hh ltac:(clear; lia)); unfold kHighMemBeg in Hh; rename Hh into H;
              pose proof (app_lin_high L p n H Ha) as Hl;
              (let hi := eval lazy in (cl_image_hi L) in try change (cl_image_hi L) with hi in Hl);
              try (cbv delta [HFSIZE] in Hl); norm_divs Hl; app_lin_norm Hl n;
              change (app_rangeF L p n) in Ha
            | clear Hh; rename Ha into H ]
  | H : app_range ?L ?p ?n |- _ =>
      (* [comment removed for export] *)
      let Ha := fresh H "_a" in let ix := fresh "ix" in let sx := fresh "sx" in
      rename H into Ha;
      destruct (app_lin L p n Ha) as (ix & sx & H);
      (let lo := eval lazy in (cl_image_lo L) in let hi := eval lazy in (cl_image_hi L) in
       try change (cl_image_lo L) with lo in H; try change (cl_image_hi L) with hi in H);
      try (cbv delta [HFSIZE] in H); norm_divs H; app_lin_norm H n;
      change (app_rangeF L p n) in Ha
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac keep_bundles ::=
  let rec go acc :=
    match goal with
    | H : context [ (8 * (sh _ - 2147450880))%Z ] |- _ =>
        lazymatch acc with context [H] => fail | _ => idtac end; go constr:(conj H acc)
    | H : (17594064011264 <= sh alloc_ceiling)%Z |- _ =>
        lazymatch acc with context [H] => fail | _ => idtac end; go constr:(conj H acc)
    | H : (sh alloc_ceiling <= SHMAX)%Z |- _ =>
        lazymatch acc with context [H] => fail | _ => idtac end; go constr:(conj H acc)
    | _ => let rec gen t := lazymatch t with conj ?H ?r => generalize H; gen r | _ => idtac end in gen acc
    end in
  go constr:(I).
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Module KB2.
Import Ltac2.
Ltac2 is_c1 (t : constr) : bool := lazy_match! t with | context [ Z.mul 8 (Z.sub (sh _) 2147450880) ] => true | _ => false end.
Ltac2 is_c2 (t : constr) : bool := lazy_match! t with | Z.le 17594064011264 (sh alloc_ceiling) => true | _ => false end.
Ltac2 is_c3 (t : constr) : bool := lazy_match! t with | Z.le (sh alloc_ceiling) SHMAX => true | _ => false end.
Ltac2 gen_hyp (id : ident) : unit := let h := Control.hyp id in ltac1:(h |- generalize h) (Ltac1.of_constr h).
Ltac2 keep_bundles_fast () : unit :=
  let hs := Control.hyps () in
  let pick f := List.filter (fun h => let (_, _, ty) := h in f ty) hs in
  let c1 := pick is_c1 in let c2 := pick is_c2 in let c3 := pick is_c3 in
  List.iter (fun h => let (id, _, _) := h in gen_hyp id) c3;
  List.iter (fun h => let (id, _, _) := h in gen_hyp id) c2;
  List.iter (fun h => let (id, _, _) := h in gen_hyp id) c1.
End KB2.
Ltac keep_bundles ::= ltac2:(Ltac2.Control.enter KB2.keep_bundles_fast).
(* [comment removed for export] *)
Ltac unhide_app_conj :=
  repeat match goal with
  | K : context [akept _] |- _ => unfold akept in K
  end.
