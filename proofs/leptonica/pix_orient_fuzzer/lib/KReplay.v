(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2 Constr.
From Ltac2 Require Pstring.
Import Constr.Unsafe.

(* [comment removed for export] *)
Ltac2 Type op := [ O0 | O1 | O2 | O3 | O4 | O5 | O6 | O7 | O8 | O9 | O10 | O11 | O12 | O13 | O14 | O15 | O16 | O17 | O18 | O19 | O20 | O21 | O22 | O23 | O24 | O25 | O26 | O27 | O28 | O29 | O30 | O31 | O32 | O33 | O34 | O35 | O36 | O37 | O38 | O39 | O40 | O41 | O42 | O43 | O44 | O45 | O46 | O47 | O48 | O49 | O50 | O51 | O52 | O53 | O54 | O55 | O56 | O57 | O58 | O59 | O60 | O61 | O62 | O63 | O64 | O65 | O66 | O67 | O68 | O69 | O70 | O71 | O72 | O73 | O74 | O75 | O76 | O77 | O78 | O79 | O80 | O81 | O82 | O83 | O84 | O85 | O86 | O87 | O88 | O89 | O90 | O91 | O92 | O93 | O94 | O95 | O96 | O97 | O98 | O99 | O100 | O101 | O102 | O103 | O104 | O105 | O106 | O107 | O108 | O109 | O110 | O111 | O112 | O113 | O114 | O115 | O116 | O117 | O118 | O119 | O120 | O121 | O122 | O123 | O124 | O125 | O126 | O127 ].
(* [comment removed for export] *)
Ltac2 @external sgo : string -> int -> op := "rocq-runtime.plugins.ltac2" "string_get".
Ltac2 @external sgi : string -> int -> int := "rocq-runtime.plugins.ltac2" "string_get".

Ltac2 kr_fail (m : string) := Control.throw (Tactic_failure (Some (Message.of_string m))).

Ltac2 kr_mk_id (s : string) : ident :=
  match Ident.of_string s with Some i => i | None => kr_fail "KReplay: bad identifier" end.

Ltac2 kr_ids (l : string list) : ident list := List.map kr_mk_id l.

Ltac2 kr_id_is (s : string) (i : ident) : bool := Ident.equal (kr_mk_id s) i.

Ltac2 rec kr_pref_eq (pre : string list) (path : ident list) : bool :=
  match pre with
  | [] => true
  | s :: pre' =>
    match path with
    | [] => false
    | i :: path' => if kr_id_is s i then kr_pref_eq pre' path' else false
    end
  end.

Ltac2 kr_retag (old_ : string) (new_ : string) (i : ident) : ident :=
  let s := Ident.to_string i in
  let n := String.length old_ in
  if Int.lt (String.length s) n then i
  else if Ident.equal (kr_mk_id old_) (kr_mk_id (String.sub s 0 n))
       then kr_mk_id (String.concat "" [new_; String.sub s n (Int.sub (String.length s) n)])
       else i.

Ltac2 kr_lib_path () : string list :=
  ["OssFuzzTheorems"; "Proofs"; "leptonica"; "pix_orient_fuzzer"; "lib"].

Ltac2 kr_img_path (b : string) : string list :=
  ["OssFuzzTheorems"; "leptonica"; "pix_orient_fuzzer"; "images"; b].

Ltac2 kr_img (pre : string list) (old_mod : string) (new_mod : string)
             (path : ident list) : ident list option :=
  let whole := List.append pre [old_mod] in
  if kr_pref_eq whole path
  then Some (List.append (kr_ids (kr_img_path new_mod))
               (List.map (kr_retag old_mod new_mod) (List.skipn (List.length whole) path)))
  else None.

Ltac2 kr_retag_all (i : ident) : ident :=
  kr_retag "Tgt_pix_orient_fuzzer_both" "AsanUbsan" (kr_retag "Tgt_pix_orient_fuzzer_ubsan" "Ubsan" (kr_retag "Tgt_pix_orient_fuzzer_asan" "Asan" (kr_retag "Src_leptonica_pix_orient_fuzzer_repro" "Plain" i))).

Ltac2 kr_port (path : ident list) : ident list :=
  if kr_pref_eq ["RocqVerifyHarness"; "AgentSubmission"] path
  then List.append (kr_ids (kr_lib_path ())) (List.map kr_retag_all (List.skipn 2 path))
  else
    let problems := ["RocqVerifyHarness"; "TaskSpecification"; "Problems"] in
    let oversight := ["RocqVerifyHarness"; "ProcessOversight"] in
    match kr_img problems "Src_leptonica_pix_orient_fuzzer_repro" "Plain" path with
    | Some p => p
    | None =>
      match kr_img oversight "Tgt_pix_orient_fuzzer_asan" "Asan" path with
      | Some p => p
      | None =>
        match kr_img oversight "Tgt_pix_orient_fuzzer_ubsan" "Ubsan" path with
        | Some p => p
        | None =>
          match kr_img oversight "Tgt_pix_orient_fuzzer_both" "AsanUbsan" path with
          | Some p => p
          | None =>
            path
          end
        end
      end
    end.

Ltac2 kr_unport_len (path : ident list) : int :=
  let n := List.length path in
  if kr_pref_eq (kr_lib_path ()) path then Int.sub n 3
  else if kr_pref_eq (kr_img_path "Plain") path then Int.sub n 1
  else if kr_pref_eq (kr_img_path "Asan") path then Int.sub n 2
  else if kr_pref_eq (kr_img_path "Ubsan") path then Int.sub n 2
  else if kr_pref_eq (kr_img_path "AsanUbsan") path then Int.sub n 2
  else n.

(* [comment removed for export] *)
Ltac2 kr_num1 (s : string) (p : int) : int := Int.sub (sgi s p) 48.
Ltac2 kr_num2 (s : string) (p : int) : int :=
  Int.add (Int.lsl (Int.sub (sgi s p) 48) 6) (Int.sub (sgi s (Int.add p 1)) 48).
Ltac2 kr_num3 (s : string) (p : int) : int :=
  Int.add (Int.lsl (kr_num2 s p) 6) (Int.sub (sgi s (Int.add p 2)) 48).
Ltac2 kr_num4 (s : string) (p : int) : int :=
  Int.add (Int.lsl (kr_num2 s p) 12) (kr_num2 s (Int.add p 2)).
Ltac2 kr_num5 (s : string) (p : int) : int :=
  Int.add (Int.lsl (kr_num3 s p) 12) (kr_num2 s (Int.add p 3)).

Ltac2 kr_ident (s : string) (p : int) (n : int) : ident :=
  match Ident.of_string (String.sub s p n) with Some i => i | None => kr_fail "KReplay: bad identifier" end.

(* [comment removed for export] *)
Ltac2 rec popn (n : int) (st : constr list) (acc : constr list) : constr list * constr list :=
  if Int.equal n 0 then (acc, st) else
    match st with
    | a :: r => popn (Int.sub n 1) r (a :: acc)
    | [] => kr_fail "KReplay: stack underflow"
    end.

(* [comment removed for export] *)
Ltac2 kr_holes (k : int) (down : bool) : constr array :=
  let a := Array.make k (make (Rel 1)) in
  let rec fill (i : int) :=
    if Int.ge i k then () else
      (Array.set a i (make (Rel (if down then Int.sub k i else Int.add i 1))); fill (Int.add i 1)) in
  fill 0; a.

Ltac2 kr_sort (c : int) : constr :=
  if Int.equal c 48 then 'Prop else if Int.equal c 49 then 'Set else if Int.equal c 50 then 'SProp
  else kr_fail "KReplay: bad sort".

Ltac2 kr_unknown (path : ident list) :=
  Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "KReplay: unknown global ")
    (List.fold_left (fun m i => Message.concat m (Message.concat (Message.of_string ".") (Message.of_ident i))) (Message.of_string "") path)))).

(* [comment removed for export] *)
Ltac2 kr_local (secs : ident list) (path : ident list) : Std.reference option :=
  let n := List.length path in
  let init := List.firstn (Int.sub n 1) path in
  let last := List.skipn (Int.sub n 1) path in
  let rec try_ (k : int) :=
    if Int.lt k 0 then None else
      match Env.get (List.append init (List.append (List.firstn k secs) last)) with
      | Some r => Some r
      | None => try_ (Int.sub k 1)
      end in
  try_ (List.length secs).

(* [comment removed for export] *)
Ltac2 kr_global (soft : bool) (secs : ident list) (s : string) (p : int) : constr * int :=
  let k := sgi s p in
  let nc := Int.sub (sgi s (Int.add p 1)) 48 in
  let rec rpath (i : int) (q : int) : ident list * int :=
    if Int.equal i 0 then ([], q) else
      (let n := Int.sub (sgi s q) 48 in
       let id := kr_ident s (Int.add q 1) n in
       let (l, q') := rpath (Int.sub i 1) (Int.add q (Int.add n 1)) in
       (id :: l, q')) in
  let (path, q) := rpath nc (Int.add p 2) in
  let path := kr_port path in
  let (k, r) :=
    if Int.lt k 96 then (k, Env.get path)
    else (Int.sub k 32, kr_local secs path) in
  let q' := if Int.equal k 67 (* [comment removed for export] *) then q else Int.add q 2 in
  match r with
  | None => if soft then (make (Rel 1), q') else kr_unknown path
  | Some r =>
    if Int.equal k 67 (* [comment removed for export] *) then (Env.instantiate r, q)
    else
      let i := Int.sub (sgi s q) 48 in
      let j := Int.sub (sgi s (Int.add q 1)) 48 in
      let ind0 := match r with Std.IndRef ind => ind | _ => kr_fail "KReplay: not an inductive" end in
      let ind := if Int.equal i 0 then ind0 else Ind.repr (Ind.get_block (Ind.data ind0) i) in
      if Int.equal k 73 (* [comment removed for export] *) then (Env.instantiate (Std.IndRef ind), Int.add q 2)
      else (Env.instantiate (Std.ConstructRef (Ind.get_constructor (Ind.data ind) (Int.sub j 1))), Int.add q 2)
  end.

(* [comment removed for export] *)
Ltac2 kr_usort (w : constr) (s : string) (p : int) : constr * int :=
  let n := Int.sub (sgi s p) 48 in
  let rec walk (c : constr) (i : int) (q : int) : constr :=
    if Int.equal i 0 then c else
      (let m := Int.sub (sgi s q) 48 in
       let c' := match kind c with
         | Prod b bd => if Int.equal m 0 then Binder.type b else bd
         | Lambda b bd => if Int.equal m 0 then Binder.type b else bd
         | LetIn b v bd => if Int.equal m 0 then Binder.type b else if Int.equal m 1 then v else bd
         | App f a => if Int.equal m 0 then f else Array.get a (Int.sub m 1)
         | Cast x _ t => if Int.equal m 0 then x else t
         | _ => c
         end in
       walk c' (Int.sub i 1) (Int.add q 1)) in
  let srt := walk w n (Int.add p 1) in
  (* [comment removed for export] *)
  let srt := match kind srt with Sort _ => srt | _ => make (Rel 1) end in
  (srt, Int.add p (Int.add n 1)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 rec kr_peel_all (c : constr) : constr :=
  match kind c with
  | Lambda _ b => kr_peel_all b
  | _ => c
  end.
Ltac2 rec kr_peel (n : int) (c : constr) : constr :=
  if Int.equal n 0 then c else
    match kind c with
    | Lambda _ b => kr_peel (Int.sub n 1) b
    | LetIn _ _ b => kr_peel (Int.sub n 1) b
    | _ => c
    end.
(* [comment removed for export] *)
Ltac2 kr_children (c : constr) : constr list :=
  match kind c with
  | Prod b bd => [Binder.type b; bd]
  | Lambda b bd => [Binder.type b; bd]
  | LetIn b v bd => [Binder.type b; v; bd]
  | App f a => f :: Array.to_list a
  | Cast x _ t => [x; t]
  | Case ci rc _ scr brs =>
    let (ret, _) := rc in
    let nd := Ind.constructor_ndecls (Ind.data (Constr.Unsafe.Case.inductive ci)) in
    let n := Array.length brs in
    let rec br (i : int) : constr list :=
      if Int.ge i n then [] else kr_peel (Array.get nd i) (Array.get brs i) :: br (Int.add i 1) in
    kr_peel_all ret :: scr :: br 0
  | Fix _ _ bis bds => List.append (List.map Binder.type (Array.to_list bis)) (Array.to_list bds)
  | CoFix _ bis bds => List.append (List.map Binder.type (Array.to_list bis)) (Array.to_list bds)
  | Proj _ _ x => [x]
  | _ => []
  end.
Ltac2 rec kr_dfs (c : constr) (k : int) : int * constr option :=
  match kind c with
  | Sort _ => if Int.equal k 0 then (0, Some c) else (Int.sub k 1, None)
  | _ =>
    let rec go (l : constr list) (k : int) : int * constr option :=
      match l with
      | [] => (k, None)
      | x :: l =>
        let (k, r) := kr_dfs x k in
        match r with Some _ => (k, r) | None => go l k end
      end in
    go (kr_children c) k
  end.
Ltac2 kr_gsort (s : string) (p : int) : constr * int :=
  match kr_dfs (Control.goal ()) (kr_num2 s p) with
  | (_, Some c) => (c, Int.add p 2)
  | _ => (make (Rel 1), Int.add p 2)
  end.

(* [comment removed for export] *)
Ltac2 rec kr_sorts (c : constr) (acc : constr list) : constr list :=
  match kind c with
  | Sort _ => c :: acc
  | _ => List.fold_left (fun acc x => kr_sorts x acc) acc (kr_children c)
  end.
Ltac2 rec kr_nth (l : constr list) (k : int) (d : constr) : constr :=
  match l with
  | [] => d
  | x :: l => if Int.equal k 0 then x else kr_nth l (Int.sub k 1) d
  end.
(* [comment removed for export] *)
Ltac2 kr_rsort (w : constr) (k : int) : constr :=
  kr_nth (kr_sorts w []) k (make (Rel 1)).

(* [comment removed for export] *)
Ltac2 kr_lsort (w : constr) (s : string) (p : int) : constr * int :=
  let dummy := make (Rel 1) in
  let body := Int.equal (sgi s p) 49 in
  let klen := Int.sub (sgi s (Int.add p 1)) 48 in
  let np := sgi s (Int.add p 2) in
  let (haspath, n) := if Int.equal np 126 then (false, 0) else (true, Int.sub np 48) in
  let pr := Int.add p (Int.add 3 n) in
  let hasrev := Bool.neg (Int.equal (sgi s pr) 126) in
  let q := Int.add pr 2 in
  let r := match kind w with
    | Constant c _ => Some (Std.ConstRef c)
    | Ind i _ => Some (Std.IndRef i)
    | Constructor c _ => Some (Std.ConstructRef c)
    | _ => None
    end in
  match r with
  | None => (dummy, q)
  | Some r =>
    let open_ := Int.gt (kr_unport_len (Env.path r)) klen in
    let t := if body then Std.eval_red w else Constr.type w in
    if open_ then
      (if hasrev then (kr_nth (kr_sorts t []) (kr_num2 s pr) dummy, q) else (dummy, q))
    else
      (if haspath then
         (let rec walk (c : constr) (i : int) (q : int) : constr :=
            if Int.equal i 0 then c else
              (let m := Int.sub (sgi s q) 48 in
               let c' := match kind c with
                 | Prod b bd => if Int.equal m 0 then Binder.type b else bd
                 | Lambda b bd => if Int.equal m 0 then Binder.type b else bd
                 | LetIn b v bd => if Int.equal m 0 then Binder.type b else if Int.equal m 1 then v else bd
                 | App f a => if Int.equal m 0 then f else Array.get a (Int.sub m 1)
                 | Cast x _ t => if Int.equal m 0 then x else t
                 | _ => c
                 end in
               walk c' (Int.sub i 1) (Int.add q 1)) in
          let srt := walk t n (Int.add p 3) in
          ((match kind srt with Sort _ => srt | _ => dummy end), q))
       else (dummy, q))
  end.

(* [comment removed for export] *)
Ltac2 kr_ucon (strict : bool) (a : constr) (b : constr) : unit :=
  match kind a with
  | Sort _ =>
    (match kind b with
     | Sort _ =>
       let t := if strict then make (Cast a Cast.default b)
                else make (Lambda (Binder.unsafe_make None Binder.Relevant a) (make (Cast (make (Rel 1)) Cast.default b))) in
       (match Constr.Unsafe.check t with _ => () end)
     | _ => ()
     end)
  | _ => ()
  end.

(* [comment removed for export] *)
Ltac2 kr_ann (n2 : ident option array array) (s : string) (p : int) (ty : constr) : binder :=
  let f := Int.sub (sgi s p) 48 in
  let nm := if Int.equal (Int.land f 1) 0 then None else Array.get (Array.get n2 (sgi s (Int.add p 1))) (sgi s (Int.add p 2)) in
  Binder.unsafe_make nm (if Int.lt f 2 then Binder.Relevant else Binder.Irrelevant) ty.

(* [comment removed for export] *)
Ltac2 kr_wrap (n2 : ident option array array) (s : string) (p : int) (n : int) (dummy : constr) (body : constr) : constr :=
  let rec go (i : int) (body : constr) :=
    if Int.lt i 0 then body else go (Int.sub i 1) (make (Lambda (kr_ann n2 s (Int.add p (Int.mul 3 i)) dummy) body)) in
  go (Int.sub n 1) body.

(* [comment removed for export] *)
Ltac2 kr_bindx (n2 : ident option array array) (s : string) (p : int) (st : constr list) : constr * constr list * int :=
  let k := Int.sub (sgi s p) 48 in
  match st with
  | b :: t :: r =>
    let bi := kr_ann n2 s (Int.add p 1) t in
    if Int.equal k 0 then (make (Lambda bi b), r, Int.add p 4)
    else if Int.equal k 1 then (make (Prod bi b), r, Int.add p 4)
    else match r with
         | v :: r => (make (LetIn bi v b), r, Int.add p 4)
         | [] => kr_fail "KReplay: stack underflow"
         end
  | _ => kr_fail "KReplay: stack underflow"
  end.

(* [comment removed for export] *)
Ltac2 kr_hole (ph : (evar * constr) list ref option) (c : constr) : constr :=
  match ph with
  | None => c
  | Some ph =>
    let h := open_constr:(_ : Corelib.Init.Logic.True) in
    let h := match kind h with Cast h' _ _ => h' | _ => h end in
    match kind h with
    | Evar e _ => ph.(contents) := (e, c) :: ph.(contents); h
    | _ => kr_fail "KReplay: placeholder"
    end
  end.

(* [comment removed for export] *)
Ltac2 kr_case (ph : (evar * constr) list ref option) (n2 : ident option array array) (s : string) (p : int) (st : constr list) : constr * constr list * int :=
  let prop := 'Prop in
  let npm := Int.sub (sgi s p) 48 in
  let pf := Int.add p 1 in                         (* [comment removed for export] *)
  let nn := Int.sub (sgi s (Int.add pf npm)) 48 in
  let pa := Int.add pf (Int.add npm 1) in          (* [comment removed for export] *)
  let prp := Int.add pa (Int.mul 3 nn) in          (* [comment removed for export] *)
  let rp := if Int.equal (sgi s prp) 48 then Binder.Relevant else Binder.Irrelevant in
  let pflag := sgi s (Int.add prp 1) in
  let nbr := kr_num2 s (Int.add prp 2) in
  let (brl, st) := popn nbr st [] in
  match st with
  | scr :: pbody :: st =>
    let (pml, st) := popn npm st [] in
    (match st with
     | indc :: st =>
       let ind := match kind indc with Ind i _ => i | _ => kr_fail "KReplay: case on a non-inductive" end in
       let nidx := Int.sub nn 1 in
       let pms := Array.of_list pml in
       let rec rpm (j : int) :=
         if Int.ge j npm then () else
           (let c := Array.get pms j in
            let c := if Int.equal (sgi s (Int.add pf j)) 48 then (if Int.equal nidx 0 then c else liftn nidx 1 c) else kr_hole ph c in
            Array.set pms j c; rpm (Int.add j 1)) in
       rpm 0;
       let selfty := if Int.equal npm 0 then indc else make (App indc pms) in
       let pbody := if Int.equal pflag 48 then pbody else kr_hole ph pbody in
       let retc := kr_wrap n2 s pa nidx prop (make (Lambda (kr_ann n2 s (Int.add pa (Int.mul 3 nidx)) selfty) pbody)) in
       let brs := Array.make nbr prop in
       let rec rbr (j : int) (q : int) (l : constr list) : int :=
         match l with
         | [] => q
         | bd :: l =>
           let nk := Int.sub (sgi s q) 48 in
           let bd := if Int.equal (sgi s (Int.add q 1)) 48 then bd else kr_hole ph bd in
           Array.set brs j (kr_wrap n2 s (Int.add q 2) nk prop bd);
           rbr (Int.add j 1) (Int.add q (Int.add 2 (Int.mul 3 nk))) l
         end in
       let q := rbr 0 (Int.add prp 4) brl in
       (make (Case (case ind) (retc, rp) NoInvert scr brs), st, q)
     | [] => kr_fail "KReplay: stack underflow"
     end)
  | _ => kr_fail "KReplay: stack underflow"
  end.

(* [comment removed for export] *)
Ltac2 kr_fix (n2 : ident option array array) (s : string) (p : int) (st : constr list) : constr * constr list * int :=
  let prop := 'Prop in
  let k := Int.sub (sgi s p) 48 in
  let i := Int.sub (sgi s (Int.add p 1)) 48 in
  let (l, st) := popn (Int.mul 2 k) st [] in
  let recs := Array.make k 0 in
  let bis := Array.make k (Binder.unsafe_make None Binder.Relevant prop) in
  let bds := Array.make k prop in
  let rec rf (j : int) (q : int) (l : constr list) : int :=
    match l with
    | ty :: bd :: l =>
      Array.set recs j (kr_num2 s q);
      Array.set bis j (kr_ann n2 s (Int.add q 2) ty);
      Array.set bds j bd;
      rf (Int.add j 1) (Int.add q 5) l
    | _ => q
    end in
  let q := rf 0 (Int.add p 2) l in
  (make (Fix recs i bis bds), st, q).

(* [comment removed for export] *)
Ltac2 kr_uint (s : string) (p : int) : constr :=
  let lo := kr_num5 s p in
  let mi := kr_num5 s (Int.add p 5) in
  let hi := Int.sub (sgi s (Int.add p 10)) 48 in
  make (Uint63 (Uint63.of_int (Int.lor lo (Int.lor (Int.lsl mi 30) (Int.lsl hi 60))))).

(* [comment removed for export] *)
Ltac2 kr_str (s : string) (p : int) : constr * int :=
  let n := kr_num3 s p in
  let rec pieces (i : int) (q : int) (acc : string list) : string list * int :=
    if Int.ge i n then (acc, q) else
      (if Int.equal (sgi s q) 114 (* [comment removed for export] *) then
         (let l := kr_num2 s (Int.add q 1) in
          pieces (Int.add i 1) (Int.add q (Int.add 3 l)) (String.sub s (Int.add q 3) l :: acc))
       else
         (let b := String.make 1 (Char.of_int (Int.add (Int.lsl (Int.sub (sgi s (Int.add q 1)) 48) 4) (Int.sub (sgi s (Int.add q 2)) 48))) in
          pieces (Int.add i 1) (Int.add q 3) (b :: acc))) in
  let (l, q) := pieces 0 (Int.add p 3) [] in
  match Pstring.of_string (String.concat "" (List.rev l)) with
  | Some ps => (make (String ps), q)
  | None => kr_fail "KReplay: string too long"
  end.

Ltac2 decode_ph (ph : (evar * constr) list ref option) (tab : string) (secs : ident list) (s : string) : constr :=
  let ad := Int.add in
  let sg := sgo in
  let si := sgi in
  let ag := Array.get in
  let as_ := Array.set in
  let sb := substnl in
  let mk := make in
  let bm := Binder.unsafe_make in
  let rl := Binder.Relevant in
  let dummy := make (Rel 1) in
  let t1 := Array.make 128 dummy in
  let t2 := Array.make 128 t1 in
  let d1 := Array.make 128 dummy in
  let t3 := Array.make 128 (Array.make 128 d1) in
  let tt1 := Array.make 128 dummy in
  let tt2 := Array.make 128 tt1 in
  let n1 := Array.make 128 None in
  let n2 := Array.make 128 n1 in
  let ra := Array.make 128 t1 in
  let rb := Array.make 128 t1 in
  let fl () := kr_fail "KReplay: stack underflow" in
  let rec go (p : int) (st : constr list) : constr :=
    match sg s p with
    | O35 (* [comment removed for export] *) =>
      match st with a1 :: r => go (ad p 2) (sb [a1] 0 (ag tt1 (si s (ad p 1))) :: r) | _ => fl () end
    | O36 (* [comment removed for export] *) =>
      match st with a1 :: r => go (ad p 3) (sb [a1] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: r) | _ => fl () end
    | O37 (* [comment removed for export] *) =>
      go (ad p 3) (sb [(ag t1 (si s (ad p 2)))] 0 (ag tt1 (si s (ad p 1))) :: st)
    | O38 (* [comment removed for export] *) =>
      go (ad p 4) (sb [(ag t1 (si s (ad p 3)))] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: st)
    | O39 (* [comment removed for export] *) =>
      match st with a2 :: a1 :: r => go (ad p 2) (sb [a2; a1] 0 (ag tt1 (si s (ad p 1))) :: r) | _ => fl () end
    | O43 (* [comment removed for export] *) =>
      match st with a2 :: a1 :: r => go (ad p 3) (sb [a2; a1] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: r) | _ => fl () end
    | O44 (* [comment removed for export] *) =>
      match st with a2 :: r => go (ad p 3) (sb [a2; (ag t1 (si s (ad p 2)))] 0 (ag tt1 (si s (ad p 1))) :: r) | _ => fl () end
    | O45 (* [comment removed for export] *) =>
      match st with a2 :: r => go (ad p 4) (sb [a2; (ag t1 (si s (ad p 3)))] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: r) | _ => fl () end
    | O47 (* [comment removed for export] *) =>
      match st with a1 :: r => go (ad p 3) (sb [(ag t1 (si s (ad p 2))); a1] 0 (ag tt1 (si s (ad p 1))) :: r) | _ => fl () end
    | O48 (* [comment removed for export] *) =>
      match st with a1 :: r => go (ad p 4) (sb [(ag t1 (si s (ad p 3))); a1] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: r) | _ => fl () end
    | O49 (* [comment removed for export] *) =>
      go (ad p 4) (sb [(ag t1 (si s (ad p 3))); (ag t1 (si s (ad p 2)))] 0 (ag tt1 (si s (ad p 1))) :: st)
    | O50 (* [comment removed for export] *) =>
      go (ad p 5) (sb [(ag t1 (si s (ad p 4))); (ag t1 (si s (ad p 3)))] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: st)
    | O51 (* [comment removed for export] *) =>
      match st with a3 :: a2 :: a1 :: r => go (ad p 2) (sb [a3; a2; a1] 0 (ag tt1 (si s (ad p 1))) :: r) | _ => fl () end
    | O52 (* [comment removed for export] *) =>
      match st with a3 :: a2 :: a1 :: r => go (ad p 3) (sb [a3; a2; a1] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: r) | _ => fl () end
    | O53 (* [comment removed for export] *) =>
      match st with a3 :: a2 :: r => go (ad p 3) (sb [a3; a2; (ag t1 (si s (ad p 2)))] 0 (ag tt1 (si s (ad p 1))) :: r) | _ => fl () end
    | O54 (* [comment removed for export] *) =>
      match st with a3 :: a2 :: r => go (ad p 4) (sb [a3; a2; (ag t1 (si s (ad p 3)))] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: r) | _ => fl () end
    | O55 (* [comment removed for export] *) =>
      match st with a3 :: a1 :: r => go (ad p 3) (sb [a3; (ag t1 (si s (ad p 2))); a1] 0 (ag tt1 (si s (ad p 1))) :: r) | _ => fl () end
    | O56 (* [comment removed for export] *) =>
      match st with a3 :: a1 :: r => go (ad p 4) (sb [a3; (ag t1 (si s (ad p 3))); a1] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: r) | _ => fl () end
    | O57 (* [comment removed for export] *) =>
      match st with a3 :: r => go (ad p 4) (sb [a3; (ag t1 (si s (ad p 3))); (ag t1 (si s (ad p 2)))] 0 (ag tt1 (si s (ad p 1))) :: r) | _ => fl () end
    | O58 (* [comment removed for export] *) =>
      match st with a3 :: r => go (ad p 5) (sb [a3; (ag t1 (si s (ad p 4))); (ag t1 (si s (ad p 3)))] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: r) | _ => fl () end
    | O59 (* [comment removed for export] *) =>
      match st with a2 :: a1 :: r => go (ad p 3) (sb [(ag t1 (si s (ad p 2))); a2; a1] 0 (ag tt1 (si s (ad p 1))) :: r) | _ => fl () end
    | O60 (* [comment removed for export] *) =>
      match st with a2 :: a1 :: r => go (ad p 4) (sb [(ag t1 (si s (ad p 3))); a2; a1] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: r) | _ => fl () end
    | O61 (* [comment removed for export] *) =>
      match st with a2 :: r => go (ad p 4) (sb [(ag t1 (si s (ad p 3))); a2; (ag t1 (si s (ad p 2)))] 0 (ag tt1 (si s (ad p 1))) :: r) | _ => fl () end
    | O62 (* [comment removed for export] *) =>
      match st with a2 :: r => go (ad p 5) (sb [(ag t1 (si s (ad p 4))); a2; (ag t1 (si s (ad p 3)))] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: r) | _ => fl () end
    | O63 (* [comment removed for export] *) =>
      match st with a1 :: r => go (ad p 4) (sb [(ag t1 (si s (ad p 3))); (ag t1 (si s (ad p 2))); a1] 0 (ag tt1 (si s (ad p 1))) :: r) | _ => fl () end
    | O64 (* [comment removed for export] *) =>
      match st with a1 :: r => go (ad p 5) (sb [(ag t1 (si s (ad p 4))); (ag t1 (si s (ad p 3))); a1] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: r) | _ => fl () end
    | O65 (* [comment removed for export] *) =>
      go (ad p 5) (sb [(ag t1 (si s (ad p 4))); (ag t1 (si s (ad p 3))); (ag t1 (si s (ad p 2)))] 0 (ag tt1 (si s (ad p 1))) :: st)
    | O66 (* [comment removed for export] *) =>
      go (ad p 6) (sb [(ag t1 (si s (ad p 5))); (ag t1 (si s (ad p 4))); (ag t1 (si s (ad p 3)))] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: st)
    | O67 (* [comment removed for export] *) =>
      match st with a4 :: a3 :: a2 :: a1 :: r => go (ad p 2) (sb [a4; a3; a2; a1] 0 (ag tt1 (si s (ad p 1))) :: r) | _ => fl () end
    | O68 (* [comment removed for export] *) =>
      match st with a5 :: a4 :: a3 :: a2 :: a1 :: r => go (ad p 2) (sb [a5; a4; a3; a2; a1] 0 (ag tt1 (si s (ad p 1))) :: r) | _ => fl () end
    | O69 (* [comment removed for export] *) =>
      match st with a6 :: a5 :: a4 :: a3 :: a2 :: a1 :: r => go (ad p 2) (sb [a6; a5; a4; a3; a2; a1] 0 (ag tt1 (si s (ad p 1))) :: r) | _ => fl () end
    | O70 (* [comment removed for export] *) =>
      match st with a7 :: a6 :: a5 :: a4 :: a3 :: a2 :: a1 :: r => go (ad p 2) (sb [a7; a6; a5; a4; a3; a2; a1] 0 (ag tt1 (si s (ad p 1))) :: r) | _ => fl () end
    | O71 (* [comment removed for export] *) =>
      match st with a8 :: a7 :: a6 :: a5 :: a4 :: a3 :: a2 :: a1 :: r => go (ad p 2) (sb [a8; a7; a6; a5; a4; a3; a2; a1] 0 (ag tt1 (si s (ad p 1))) :: r) | _ => fl () end
    | O72 (* [comment removed for export] *) =>
      match st with a4 :: a3 :: a2 :: a1 :: r => go (ad p 3) (sb [a4; a3; a2; a1] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: r) | _ => fl () end
    | O73 (* [comment removed for export] *) =>
      match st with a5 :: a4 :: a3 :: a2 :: a1 :: r => go (ad p 3) (sb [a5; a4; a3; a2; a1] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: r) | _ => fl () end
    | O74 (* [comment removed for export] *) =>
      match st with a6 :: a5 :: a4 :: a3 :: a2 :: a1 :: r => go (ad p 3) (sb [a6; a5; a4; a3; a2; a1] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: r) | _ => fl () end
    | O75 (* [comment removed for export] *) =>
      match st with a7 :: a6 :: a5 :: a4 :: a3 :: a2 :: a1 :: r => go (ad p 3) (sb [a7; a6; a5; a4; a3; a2; a1] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: r) | _ => fl () end
    | O76 (* [comment removed for export] *) =>
      match st with a8 :: a7 :: a6 :: a5 :: a4 :: a3 :: a2 :: a1 :: r => go (ad p 3) (sb [a8; a7; a6; a5; a4; a3; a2; a1] 0 (ag (ag tt2 (si s (ad p 1))) (si s (ad p 2))) :: r) | _ => fl () end
    | O77 (* [comment removed for export] *) =>
      let (l, r) := popn (Int.sub (si s (ad p 1)) 48) st [] in go (ad p 3) (sb l 0 (ag tt1 (si s (ad p 2))) :: r)
    | O78 (* [comment removed for export] *) =>
      let (l, r) := popn (Int.sub (si s (ad p 1)) 48) st [] in go (ad p 4) (sb l 0 (ag (ag tt2 (si s (ad p 2))) (si s (ad p 3))) :: r)
    | O79 (* [comment removed for export] *) =>
      let k := Int.sub (si s (ad p 1)) 48 in let (l, r) := popn k st [] in match r with f :: r => go (ad p 2) (mk (App f (Array.of_list l)) :: r) | _ => fl () end
    | O80 (* [comment removed for export] *) =>
      go (ad p 2) ((ag t1 (si s (ad p 1))) :: st)
    | O81 (* [comment removed for export] *) =>
      go (ad p 3) ((ag (ag t2 (si s (ad p 1))) (si s (ad p 2))) :: st)
    | O82 (* [comment removed for export] *) =>
      match st with a :: _ => as_ t1 (si s (ad p 1)) a; go (ad p 2) st | _ => fl () end
    | O83 (* [comment removed for export] *) =>
      match st with a :: _ => as_ (ag t2 (si s (ad p 1))) (si s (ad p 2)) a; go (ad p 3) st | _ => fl () end
    | O84 (* [comment removed for export] *) =>
      match st with _ :: r => go (ad p 1) r | _ => fl () end
    | O85 (* [comment removed for export] *) =>
      match st with b :: t :: r => go (ad p 1) (mk (Lambda (bm None rl t) b) :: r) | _ => fl () end
    | O86 (* [comment removed for export] *) =>
      match st with b :: r => go (ad p 2) (mk (Lambda (bm None rl (ag t1 (si s (ad p 1)))) b) :: r) | _ => fl () end
    | O87 (* [comment removed for export] *) =>
      match st with b :: t :: r => go (ad p 2) (mk (Lambda (bm (ag n1 (si s (ad p 1))) rl t) b) :: r) | _ => fl () end
    | O88 (* [comment removed for export] *) =>
      match st with b :: r => go (ad p 3) (mk (Lambda (bm (ag n1 (si s (ad p 1))) rl (ag t1 (si s (ad p 2)))) b) :: r) | _ => fl () end
    | O89 (* [comment removed for export] *) =>
      match st with b :: t :: r => go (ad p 3) (mk (Lambda (bm (ag (ag n2 (si s (ad p 1))) (si s (ad p 2))) rl t) b) :: r) | _ => fl () end
    | O90 (* [comment removed for export] *) =>
      match st with b :: r => go (ad p 4) (mk (Lambda (bm (ag (ag n2 (si s (ad p 1))) (si s (ad p 2))) rl (ag t1 (si s (ad p 3)))) b) :: r) | _ => fl () end
    | O91 (* [comment removed for export] *) =>
      match st with b :: t :: r => go (ad p 1) (mk (Prod (bm None rl t) b) :: r) | _ => fl () end
    | O92 (* [comment removed for export] *) =>
      match st with b :: r => go (ad p 2) (mk (Prod (bm None rl (ag t1 (si s (ad p 1)))) b) :: r) | _ => fl () end
    | O93 (* [comment removed for export] *) =>
      match st with b :: t :: r => go (ad p 2) (mk (Prod (bm (ag n1 (si s (ad p 1))) rl t) b) :: r) | _ => fl () end
    | O94 (* [comment removed for export] *) =>
      match st with b :: r => go (ad p 3) (mk (Prod (bm (ag n1 (si s (ad p 1))) rl (ag t1 (si s (ad p 2)))) b) :: r) | _ => fl () end
    | O95 (* [comment removed for export] *) =>
      match st with b :: t :: r => go (ad p 3) (mk (Prod (bm (ag (ag n2 (si s (ad p 1))) (si s (ad p 2))) rl t) b) :: r) | _ => fl () end
    | O96 (* [comment removed for export] *) =>
      match st with b :: r => go (ad p 4) (mk (Prod (bm (ag (ag n2 (si s (ad p 1))) (si s (ad p 2))) rl (ag t1 (si s (ad p 3)))) b) :: r) | _ => fl () end
    | O97 (* [comment removed for export] *) =>
      match st with b :: t :: v :: r => go (ad p 1) (mk (LetIn (bm None rl t) v b) :: r) | _ => fl () end
    | O98 (* [comment removed for export] *) =>
      match st with b :: t :: v :: r => go (ad p 2) (mk (LetIn (bm (ag n1 (si s (ad p 1))) rl t) v b) :: r) | _ => fl () end
    | O99 (* [comment removed for export] *) =>
      match st with b :: t :: v :: r => go (ad p 3) (mk (LetIn (bm (ag (ag n2 (si s (ad p 1))) (si s (ad p 2))) rl t) v b) :: r) | _ => fl () end
    | O100 (* [comment removed for export] *) =>
      match st with t :: c :: r => go (ad p 1) (mk (Cast c Cast.vm t) :: r) | _ => fl () end
    | O101 (* [comment removed for export] *) =>
      match st with t :: c :: r => go (ad p 1) (mk (Cast c Cast.default t) :: r) | _ => fl () end
    | O102 (* [comment removed for export] *) =>
      go (ad p 2) (mk (Rel (Int.sub (si s (ad p 1)) 47)) :: st)
    | O103 (* [comment removed for export] *) =>
      let (c, _) := kr_global false secs tab (kr_num4 s (ad p 1)) in go (ad p 5) (c :: st)
    | O104 (* [comment removed for export] *) =>
      let n := Int.sub (si s (ad p 2)) 48 in as_ n1 (si s (ad p 1)) (Ident.of_string (String.sub s (ad p 3) n)); go (ad p (ad n 3)) st
    | O105 (* [comment removed for export] *) =>
      let n := Int.sub (si s (ad p 3)) 48 in as_ (ag n2 (si s (ad p 1))) (si s (ad p 2)) (Ident.of_string (String.sub s (ad p 4) n)); go (ad p (ad n 4)) st
    | O106 (* [comment removed for export] *) =>
      match st with f :: _ => as_ tt1 (si s (ad p 2)) (mk (App f (ag ra (si s (ad p 1))))); go (ad p 3) st | _ => fl () end
    | O107 (* [comment removed for export] *) =>
      match st with f :: _ => as_ (ag tt2 (si s (ad p 2))) (si s (ad p 3)) (mk (App f (ag ra (si s (ad p 1))))); go (ad p 4) st | _ => fl () end
    | O108 (* [comment removed for export] *) =>
      match st with f :: _ => as_ tt1 (si s (ad p 2)) (mk (App f (ag rb (si s (ad p 1))))); go (ad p 3) st | _ => fl () end
    | O109 (* [comment removed for export] *) =>
      match st with f :: _ => as_ (ag tt2 (si s (ad p 2))) (si s (ad p 3)) (mk (App f (ag rb (si s (ad p 1))))); go (ad p 4) st | _ => fl () end
    | O110 (* [comment removed for export] *) =>
      let (c, r, q) := kr_case ph n2 s (ad p 1) st in go q (c :: r)
    | O111 (* [comment removed for export] *) =>
      match st with a :: _ => a | _ => fl () end
    | O112 (* [comment removed for export] *) =>
      let p := ad p 1 in
      (match sg s p with
       | O35 (* [comment removed for export] *) =>
         let (l, r) := popn (kr_num2 s (ad p 1)) st [] in go (ad p 5) (sb l 0 (ag (ag tt2 (si s (ad p 3))) (si s (ad p 4))) :: r)
       | O36 (* [comment removed for export] *) =>
         let k := kr_num2 s (ad p 1) in let (l, r) := popn k st [] in match r with f :: r => go (ad p 3) (mk (App f (Array.of_list l)) :: r) | _ => fl () end
       | O37 (* [comment removed for export] *) =>
         as_ t2 (si s (ad p 1)) (Array.make 128 dummy); go (ad p 2) st
       | O38 (* [comment removed for export] *) =>
         as_ tt2 (si s (ad p 1)) (Array.make 128 dummy); go (ad p 2) st
       | O39 (* [comment removed for export] *) =>
         as_ n2 (si s (ad p 1)) (Array.make 128 None); go (ad p 2) st
       | O43 (* [comment removed for export] *) =>
         go (ad p 4) (mk (Rel (kr_num3 s (ad p 1))) :: st)
       | O44 (* [comment removed for export] *) =>
         let n := Int.sub (si s (ad p 1)) 48 in go (ad p (ad n 2)) (mk (Var (kr_ident s (ad p 2) n)) :: st)
       | O45 (* [comment removed for export] *) =>
         go (ad p 2) (kr_sort (si s (ad p 1)) :: st)
       | O47 (* [comment removed for export] *) =>
         let (c, q) := kr_global false secs s (ad p 1) in go q (c :: st)
       | O48 (* [comment removed for export] *) =>
         let (c, q) := kr_global true secs s (ad p 1) in go q (c :: st)
       | O49 (* [comment removed for export] *) =>
         let (c, _) := kr_global true secs tab (kr_num4 s (ad p 1)) in go (ad p 5) (c :: st)
       | O50 (* [comment removed for export] *) =>
         let (c, q) := kr_gsort s (ad p 1) in go q (c :: st)
       | O51 (* [comment removed for export] *) =>
         match st with w :: r => go (ad p 3) (kr_rsort w (kr_num2 s (ad p 1)) :: r) | _ => fl () end
       | O52 (* [comment removed for export] *) =>
         match st with w :: r => go (ad p 1) ((match kind w with Rel _ => w | _ => Constr.type w end) :: r) | _ => fl () end
       | O53 (* [comment removed for export] *) =>
         match st with w :: r => go (ad p 1) ((match kind w with Rel _ => w | _ => Std.eval_red w end) :: r) | _ => fl () end
       | O54 (* [comment removed for export] *) =>
         match st with w :: r => let (c, q) := kr_lsort w s (ad p 1) in go q (c :: r) | _ => fl () end
       | O55 (* [comment removed for export] *) =>
         match st with w :: r => let (c, q) := kr_usort w s (ad p 1) in go q (c :: r) | _ => fl () end
       | O56 (* [comment removed for export] *) =>
         match st with b :: a :: r => kr_ucon false a b; go (ad p 1) r | _ => fl () end
       | O57 (* [comment removed for export] *) =>
         match st with b :: a :: r => kr_ucon true a b; go (ad p 1) r | _ => fl () end
       | O58 (* [comment removed for export] *) =>
         let n := kr_num2 s (ad p 3) in as_ (ag n2 (si s (ad p 1))) (si s (ad p 2)) (Ident.of_string (String.sub s (ad p 5) n)); go (ad p (ad n 5)) st
       | O59 (* [comment removed for export] *) =>
         let k := Int.sub (si s (ad p 1)) 48 in as_ ra (si s (ad p 1)) (kr_holes k true); as_ rb (si s (ad p 1)) (kr_holes k false); go (ad p 2) st
       | O60 (* [comment removed for export] *) =>
         match st with f :: _ => as_ (ag tt2 (si s (ad p 3))) (si s (ad p 4)) (mk (App f (kr_holes (kr_num2 s (ad p 1)) false))); go (ad p 5) st | _ => fl () end
       | O61 (* [comment removed for export] *) =>
         match st with a :: r => as_ tt1 (si s (ad p 1)) a; go (ad p 2) r | _ => fl () end
       | O62 (* [comment removed for export] *) =>
         match st with a :: r => as_ (ag tt2 (si s (ad p 1))) (si s (ad p 2)) a; go (ad p 3) r | _ => fl () end
       | O63 (* [comment removed for export] *) =>
         let (c, r, q) := kr_fix n2 s (ad p 1) st in go q (c :: r)
       | O64 (* [comment removed for export] *) =>
         go (ad p 12) (kr_uint s (ad p 1) :: st)
       | O65 (* [comment removed for export] *) =>
         let (c, q) := kr_str s (ad p 1) in go q (c :: st)
       | O66 (* [comment removed for export] *) =>
         let (c, r, q) := kr_bindx n2 s (ad p 1) st in go q (c :: r)
       | O67 (* [comment removed for export] *) =>
         go (ad p 4) ((ag (ag (ag t3 (si s (ad p 1))) (si s (ad p 2))) (si s (ad p 3))) :: st)
       | O68 (* [comment removed for export] *) =>
         match st with a :: _ => as_ (ag (ag t3 (si s (ad p 1))) (si s (ad p 2))) (si s (ad p 3)) a; go (ad p 4) st | _ => fl () end
       | O69 (* [comment removed for export] *) =>
         as_ t3 (si s (ad p 1)) (Array.make 128 d1); go (ad p 2) st
       | O70 (* [comment removed for export] *) =>
         as_ (ag t3 (si s (ad p 1))) (si s (ad p 2)) (Array.make 128 dummy); go (ad p 3) st
       | _ => kr_fail "KReplay: bad extended opcode"
       end)
    | _ => kr_fail "KReplay: bad opcode"
    end in
  go 0 [].

(* [comment removed for export] *)
Ltac2 kr_is_secvar (id : ident) : bool :=
  List.exist (fun r => match r with Std.VarRef _ => true | _ => false end) (Env.expand [id]).
Ltac2 kr_revert () : unit :=
  match Control.hyps () with
  | [] => ()
  | hs =>
    let ids := List.fold_right (fun (id, _, _) acc => if kr_is_secvar id then acc else id :: acc) hs [] in
    match ids with [] => () | _ => Std.revert ids end
  end.

(* [comment removed for export] *)
Ltac2 decode (secs : ident list) (s : string) : constr := decode_ph None "" secs s.

Ltac2 kr_secs (secs : string list) : ident list :=
  List.map (fun x => match Ident.of_string x with Some i => i | None => kr_fail "KReplay: bad section name" end) secs.

(* [comment removed for export] *)
Ltac2 run1 (tab : string) (secs : string list) (s : string) : unit :=
  kr_revert ();
  let ph := { contents := [] } in
  let c := decode_ph (Some ph) tab (kr_secs secs) s in
  Std.exact_no_check c;
  (* [comment removed for export] *)
  List.iter (fun (e, b) => Control.new_goal e; Control.enter (fun () => Std.exact_no_check b)) (ph.(contents)).
Ltac2 run (secs : string list) (s : string) : unit := run1 "" secs s.

(* [comment removed for export] *)
Ltac2 run1_chk (tab : string) (secs : string list) (s : string) : unit :=
  kr_revert ();
  let c := decode_ph None tab (kr_secs secs) s in
  match Constr.Unsafe.check c with
  | Val c => Std.exact_no_check c
  | Err e => Control.zero e
  end.
Ltac2 run_chk (secs : string list) (s : string) : unit := run1_chk "" secs s.
