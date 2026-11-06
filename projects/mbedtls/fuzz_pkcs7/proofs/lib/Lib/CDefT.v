(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith.
From Ltac2 Require Import Ltac2 Constr Env Std String Char Int List Message Ident Control Array.

Ltac2 Type rstate := { src : string; mutable pos : int; globs : constr array; gpaths : string array; gcache : bool array;
                       ghyps : (ident * constr option * constr) list;
                       kxI : constr; kxO : constr; kxH : constr; kZ0 : constr; kZpos : constr; kZneg : constr;
                       kS : constr; kO : constr; kN0 : constr; kNpos : constr; kProp : constr; kSet : constr }.

Ltac2 fail (msg : string) : 'a := Control.throw (Invalid_argument (Some (Message.of_string msg))).

Ltac2 rec split_from (s : string) (sep : int) (i : int) (start : int) (acc : string list) : string list :=
  let n := String.length s in
  if Int.equal i n then List.rev (String.sub s start (Int.sub i start) :: acc)
  else if Int.equal (Char.to_int (String.get s i)) sep then
    split_from s sep (Int.add i 1) (Int.add i 1) (String.sub s start (Int.sub i start) :: acc)
  else split_from s sep (Int.add i 1) start acc.
Ltac2 split_on (s : string) (sep : int) : string list := split_from s sep 0 0 [].

Ltac2 global_of_path (p : string) : constr :=
  let ids := List.map (fun s => match Ident.of_string s with Some i => i | None => fail (String.app "CDefT: bad identifier in " p) end)
                      (split_on p 46) in
  match Env.get ids with
  | Some r => Env.instantiate r
  | None => fail (String.app "CDefT: no such global " p)
  end.

Ltac2 app1 (f : constr) (a : constr) : constr := Constr.Unsafe.make (Constr.Unsafe.App f (Array.of_list [a])).

Ltac2 peek (st : rstate) : int := Char.to_int (String.get (st.(src)) (st.(pos))).
Ltac2 adv (st : rstate) : unit := st.(pos) := Int.add (st.(pos)) 1.

Ltac2 rec digits (st : rstate) (acc : int list) : int list :=
  let c := peek st in
  adv st;
  if Int.equal c 46 then List.rev acc
  else if Bool.and (Int.le 48 c) (Int.le c 63) then digits st (Int.sub c 48 :: acc)
  else fail "CDefT: bad digit".

Ltac2 int_of_digits (ds : int list) : int := List.fold_left (fun acc d => Int.add (Int.mul acc 16) d) 0 ds.

(* [comment removed for export] *)
Ltac2 rec name_end (st : rstate) (i : int) : int :=
  if Int.equal (Char.to_int (String.get (st.(src)) i)) 44 then i else name_end st (Int.add i 1).
Ltac2 read_name (st : rstate) : ident option :=
  let i := st.(pos) in
  let j := name_end st i in
  st.(pos) := Int.add j 1;
  if Int.equal i j then None
  else match Ident.of_string (String.sub (st.(src)) i (Int.sub j i)) with
       | Some id => Some id
       | None => fail "CDefT: bad binder name"
       end.

Ltac2 pos_of_digits (st : rstate) (ds : int list) : constr :=
  let step (cur : constr option) (bit : bool) :=
    match cur with
    | None => if bit then Some (st.(kxH)) else None
    | Some c => Some (app1 (if bit then st.(kxI) else st.(kxO)) c)
    end in
  let dig (cur : constr option) (d : int) :=
    let cur := step cur (Int.equal (Int.land d 8) 8) in
    let cur := step cur (Int.equal (Int.land d 4) 4) in
    let cur := step cur (Int.equal (Int.land d 2) 2) in
    step cur (Int.equal (Int.land d 1) 1) in
  match List.fold_left dig None ds with
  | Some c => c
  | None => fail "CDefT: zero positive"
  end.

Ltac2 rec nat_chain (st : rstate) (n : int) (c : constr) : constr :=
  if Int.equal n 0 then c else nat_chain st (Int.sub n 1) (app1 (st.(kS)) c).

Ltac2 cdt_mk_id (s : string) : ident :=
  match Ident.of_string s with Some i => i | None => fail "cdt_port: bad identifier" end.

Ltac2 cdt_ids (l : string list) : ident list := List.map cdt_mk_id l.

Ltac2 rec cdt_pref_eq (pre : string list) (path : ident list) : bool :=
  match pre with
  | [] => true
  | s :: pre' =>
    match path with
    | [] => false
    | i :: path' => if Ident.equal (cdt_mk_id s) i then cdt_pref_eq pre' path' else false
    end
  end.

Ltac2 cdt_retag (old_ : string) (new_ : string) (i : ident) : ident :=
  let s := Ident.to_string i in
  let n := String.length old_ in
  let m := String.length s in
  if Int.lt m n then i
  else if Ident.equal (cdt_mk_id old_) (cdt_mk_id (String.sub s 0 n)) then
    (if Int.equal m n then cdt_mk_id new_
     else if Int.equal (Char.to_int (String.get s n)) 95
     then cdt_mk_id (String.app new_ (String.sub s n (Int.sub m n)))
     else i)
  else i.

Ltac2 cdt_lib_path () : string list := ["OSSVerify"; "Proofs"; "mbedtls"; "fuzz_pkcs7"; "lib"].

Ltac2 cdt_img_path (b : string) : string list := List.append ["OSSVerify"; "mbedtls"; "fuzz_pkcs7"; "images"] [b].

Ltac2 cdt_img (pre : string list) (old_mod : string) (new_mod : string)
             (path : ident list) : ident list option :=
  let whole := List.append pre [old_mod] in
  if cdt_pref_eq whole path
  then Some (List.append (cdt_ids (cdt_img_path new_mod))
               (List.map (cdt_retag old_mod new_mod) (List.skipn (List.length whole) path)))
  else None.

Ltac2 cdt_port (path : ident list) : ident list :=
  if cdt_pref_eq ["OSSVerify"; "KrLib"; "Proof"] path
  then List.append (cdt_ids (List.append (cdt_lib_path ()) ["Theorems"])) (List.skipn 3 path)
  else if cdt_pref_eq ["OSSVerify"; "KrLib"] path
  then List.append (cdt_ids (cdt_lib_path ())) (List.skipn 2 path)
  else
    match cdt_img ["OSSVerify"; "KrSpec"; "Problems"] "Src_mbedtls_fuzz_pkcs7_repro" "Plain" path with
    | Some p => p
    | None =>
      match cdt_img ["OSSVerify"; "KrImg"] "Tgt_fuzz_pkcs7_ubsan" "Ubsan" path with
      | Some p => p
      | None =>
        match cdt_img ["OSSVerify"; "KrImg"] "Tgt_fuzz_pkcs7_asan" "Asan" path with
        | Some p => p
        | None =>
          match cdt_img ["OSSVerify"; "KrImg"] "Tgt_fuzz_pkcs7_both" "AsanUbsan" path with
          | Some p => p
          | None =>
            path
          end
        end
      end
    end.

Ltac2 resolve_path0 (p : string) : constr :=
  let ids := List.map (fun s => match Ident.of_string s with Some i => i | None => fail (String.app "CDefT: bad identifier in " p) end)
                      (split_on p 46) in
  let ids := cdt_port ids in
  match Env.get ids with
  | Some r => Env.instantiate r
  | None =>
      match Env.expand ids with
      | r :: _ => Env.instantiate r
      | [] => fail (String.app "CDefT: cannot resolve " p)
      end
  end.
(* [comment removed for export] *)
Ltac2 glob (st : rstate) (i : int) : constr :=
  if Int.equal (Array.length (st.(gpaths))) 0 then Array.get (st.(globs)) i
  else if Array.get (st.(gcache)) i then Array.get (st.(globs)) i
  else (let c := resolve_path0 (Array.get (st.(gpaths)) i) in
        Array.set (st.(globs)) i c; Array.set (st.(gcache)) i true; c).

Ltac2 mkb (n : ident option) (ty : constr) : binder := Constr.Binder.unsafe_make n Constr.Binder.Relevant ty.

Ltac2 rec term (st : rstate) : constr :=
  let c := peek st in
  adv st;
  if Int.equal c 40 then                                   (* [comment removed for export] *)
    let f := glob st (int_of_digits (digits st [])) in
    let args := arglist st [] in
    Constr.Unsafe.make (Constr.Unsafe.App f (Array.of_list args))
  else if Int.equal c 36 then glob st (int_of_digits (digits st []))     (* [comment removed for export] *)
  else if Int.equal c 61 then st.(kZ0)                                                    (* [comment removed for export] *)
  else if Int.equal c 43 then app1 (st.(kZpos)) (pos_of_digits st (digits st []))         (* [comment removed for export] *)
  else if Int.equal c 45 then app1 (st.(kZneg)) (pos_of_digits st (digits st []))         (* [comment removed for export] *)
  else if Int.equal c 94 then pos_of_digits st (digits st [])                             (* [comment removed for export] *)
  else if Int.equal c 35 then nat_chain st (int_of_digits (digits st [])) (st.(kO))       (* [comment removed for export] *)
  else if Int.equal c 126 then st.(kN0)                                                  (* [comment removed for export] *)
  else if Int.equal c 38 then app1 (st.(kNpos)) (pos_of_digits st (digits st []))        (* [comment removed for export] *)
  else if Int.equal c 80 then                                                             (* [comment removed for export] *)
    let n := read_name st in let ty := term st in let b := term st in Constr.Unsafe.make (Constr.Unsafe.Prod (mkb n ty) b)
  else if Int.equal c 76 then                                                             (* [comment removed for export] *)
    let n := read_name st in let ty := term st in let b := term st in Constr.Unsafe.make (Constr.Unsafe.Lambda (mkb n ty) b)
  else if Int.equal c 90 then                                                             (* [comment removed for export] *)
    let n := read_name st in let ty := term st in let v := term st in let b := term st in
    Constr.Unsafe.make (Constr.Unsafe.LetIn (mkb n ty) v b)
  else if Int.equal c 82 then Constr.Unsafe.make (Constr.Unsafe.Rel (int_of_digits (digits st [])))   (* [comment removed for export] *)
  else if Int.equal c 65 then                                                             (* [comment removed for export] *)
    (let n := int_of_digits (digits st []) in
     let h := term st in
     let args := nterms st n [] in
     Constr.Unsafe.make (Constr.Unsafe.App h (Array.of_list args)))
  else if Int.equal c 79 then                                                             (* [comment removed for export] *)
    (let h := int_of_digits (digits st []) in
     let hs := st.(ghyps) in
     let n := List.length hs in
     match List.nth hs (Int.sub n h) with (id, _, _) => Constr.Unsafe.make (Constr.Unsafe.Var id) end)
  else if Int.equal c 86 then                                                             (* [comment removed for export] *)
    match read_name st with
    | Some id => Constr.Unsafe.make (Constr.Unsafe.Var id)
    | None => fail "CDefT: empty variable name"
    end
  else if Int.equal c 83 then                                                             (* [comment removed for export] *)
    (let k := peek st in adv st;
     if Int.equal k 112 then st.(kProp) else if Int.equal k 115 then st.(kSet)
     else if Int.equal k 116 then open_constr:(Type) else fail "CDefT: bad sort")
  else fail "CDefT: bad tag"
with arglist (st : rstate) (acc : constr list) : constr list :=
  if Int.equal (peek st) 41 then (adv st; List.rev acc)
  else let a := term st in arglist st (a :: acc)
with nterms (st : rstate) (n : int) (acc : constr list) : constr list :=
  if Int.equal n 0 then List.rev acc else let a := term st in nterms st (Int.sub n 1) (a :: acc).

Ltac2 decode_gen (table : constr list) (paths : string list) (body : string) : constr :=
  let globs := if Int.equal (List.length paths) 0 then Array.of_list table else Array.make (List.length paths) constr:(Prop) in
  let g := global_of_path in
  let st := { src := body; pos := 0; globs := globs; gpaths := Array.of_list paths; gcache := Array.make (List.length paths) false;
              ghyps := Control.hyps ();
              kxI := g "Corelib.Numbers.BinNums.xI"; kxO := g "Corelib.Numbers.BinNums.xO"; kxH := g "Corelib.Numbers.BinNums.xH";
              kZ0 := g "Corelib.Numbers.BinNums.Z0"; kZpos := g "Corelib.Numbers.BinNums.Zpos"; kZneg := g "Corelib.Numbers.BinNums.Zneg";
              kS := g "Corelib.Init.Datatypes.S"; kO := g "Corelib.Init.Datatypes.O";
              kN0 := g "Corelib.Numbers.BinNums.N0"; kNpos := g "Corelib.Numbers.BinNums.Npos";
              kProp := constr:(Prop); kSet := constr:(Set) } in
  let t := term st in
  if Int.equal (st.(pos)) (String.length body) then t else fail "CDefT: trailing characters".

Ltac2 decode (table : constr list) (body : string) : constr := decode_gen table [] body.

(* [comment removed for export] *)
Ltac2 build (table : constr list) (body : string) : unit :=
  let t := decode table body in
  Control.refine (fun () => t).

(* [comment removed for export] *)
Ltac2 buildp (paths : string list) (body : string) : unit :=
  let t := decode_gen [] paths body in
  Control.refine (fun () => t).

(* [comment removed for export] *)
