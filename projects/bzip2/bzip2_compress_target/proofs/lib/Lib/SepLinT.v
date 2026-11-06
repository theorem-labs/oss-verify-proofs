(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require SepLin.
From Ltac2 Require Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac sl_tslia tac :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; sl_tslia tac
  | |- (_ <= _ \/ _ <= _)%Z => SepLin.sl_conj ltac:(idtac; fail) tac ltac:(idtac; fail)
  | |- (_ <= _)%Z => SepLin.sl_chain
  | |- (_ <= _ /\ _ <= _)%Z \/ _ => first [ left; split; SepLin.sl_chain | right; sl_tslia tac ]
  end.

(* [comment removed for export] *)
Lemma outside_sub : forall lo hi lo' hi' x : Z, (lo' <= lo)%Z -> (hi <= hi')%Z -> ~ (lo' <= x < hi')%Z -> ~ (lo <= x < hi)%Z.
Proof. intros lo hi lo' hi' x H1 H2 H3 H4. apply H3. lia. Qed.

Module SLT.
  Import Ltac2.
  Ltac2 gref (r : Std.reference) : constr := Env.instantiate r.
  Ltac2 mk_app (f : constr) (a : constr array) : constr := Constr.Unsafe.make (Constr.Unsafe.App f a).
  Ltac2 nope () := Control.zero (Tactic_failure None).
  (* [comment removed for export] *)
  Ltac2 neg_range (c_not : constr) (c_and : constr) (t : constr) : (constr * constr * constr) option :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App n nargs =>
        if (if Int.equal (Array.length nargs) 1 then Constr.equal n c_not else false) then
          match Constr.Unsafe.kind (Array.get nargs 0) with
          | Constr.Unsafe.App a aargs =>
              if (if Int.equal (Array.length aargs) 2 then Constr.equal a c_and else false) then
                match Constr.Unsafe.kind (Array.get aargs 0) with
                | Constr.Unsafe.App _ l =>
                    match Constr.Unsafe.kind (Array.get aargs 1) with
                    | Constr.Unsafe.App _ r =>
                        if (if Int.equal (Array.length l) 2 then Int.equal (Array.length r) 2 else false) then
                          (if Constr.equal (Array.get l 1) (Array.get r 0) then Some (Array.get l 0, Array.get l 1, Array.get r 1) else None)
                        else None
                    | _ => None
                    end
                | _ => None
                end
              else None
          | _ => None
          end
        else None
    | _ => None
    end.
  (* [comment removed for export] *)
  Ltac2 rec hyp_ranges (c_not : constr) (c_and : constr) (c_p1 : constr) (c_p2 : constr) (pf : constr) (ty : constr)
                       (acc : (constr * constr * constr * constr) list) : (constr * constr * constr * constr) list :=
    match Constr.Unsafe.kind ty with
    | Constr.Unsafe.App a args =>
        if (if Int.equal (Array.length args) 2 then Constr.equal a c_and else false) then
          (let p := Array.get args 0 in let q := Array.get args 1 in
           let acc := match neg_range c_not c_and p with
                      | Some r => let (lo, x, hi) := r in (lo, x, hi, mk_app c_p1 [| p; q; pf |]) :: acc
                      | None => acc
                      end in
           hyp_ranges c_not c_and c_p1 c_p2 (mk_app c_p2 [| p; q; pf |]) q acc)
        else acc
    | _ => acc
    end.
  Ltac2 sl_outside () : unit :=
    let x := SepLin.SL2.mk_cx () in
    let c_not := gref reference:(not) in let c_and := gref reference:(and) in
    let c_p1 := gref reference:(proj1) in let c_p2 := gref reference:(proj2) in
    let c_conj := gref reference:(conj) in let c_sub := gref reference:(outside_sub) in
    let s := SepLin.SL2.mk_st () in
    (* [comment removed for export] *)
    let cands := List.fold_left (fun acc h => let (id, body, ty) := h in
                   match body with
                   | Some _ => acc
                   | None =>
                       match Constr.Unsafe.kind ty with
                       | Constr.Unsafe.App a args =>
                           if (if Int.equal (Array.length args) 2 then Constr.equal a c_and else false) then
                             (match neg_range c_not c_and (Array.get args 0) with
                              | Some _ => hyp_ranges c_not c_and c_p1 c_p2 (Constr.Unsafe.make (Constr.Unsafe.Var id)) ty acc
                              | None => acc
                              end)
                           else acc
                       | _ => acc
                       end
                   end) [] (Control.hyps ()) in
    let le (l : constr) (r : constr) : constr option :=
      match SepLin.SL2.prove_le x s 0 l r with
      | SepLin.SL2.Proof p => Some p
      | _ => (match SepLin.SL2.prove_le x s 2 l r with SepLin.SL2.Proof p => Some p | _ => None end)
      end in
    let rec one (lo : constr) (v : constr) (hi : constr) (cs : (constr * constr * constr * constr) list) : constr :=
      match cs with
      | [] => nope ()
      | c :: r =>
          let (lo', v', hi', pf) := c in
          if Constr.equal v v' then
            (match le lo' lo with
             | Some p1 => (match le hi hi' with
                           | Some p2 => mk_app c_sub [| lo; hi; lo'; hi'; v; p1; p2; pf |]
                           | None => one lo v hi r
                           end)
             | None => one lo v hi r
             end)
          else one lo v hi r
      end in
    let rec build (g : constr) : constr :=
      match Constr.Unsafe.kind g with
      | Constr.Unsafe.App a args =>
          if (if Int.equal (Array.length args) 2 then Constr.equal a c_and else false) then
            (let p := Array.get args 0 in let q := Array.get args 1 in
             match neg_range c_not c_and p with
             | Some r => let (lo, v, hi) := r in mk_app c_conj [| p; q; one lo v hi cands; build q |]
             | None => nope ()
             end)
          else nope ()
      | _ => if Constr.equal g (gref reference:(True)) then gref reference:(I) else nope ()
      end in
    match cands with
    | [] => nope ()
    | _ :: _ => Std.exact_no_check (build (Control.goal ()))
    end.
  Ltac sl_outside_l := ltac2:(Control.enter sl_outside).
End SLT.
Ltac sl_outside := SLT.sl_outside_l.

