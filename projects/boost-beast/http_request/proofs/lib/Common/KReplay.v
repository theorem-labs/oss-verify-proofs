(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr.

Ltac2 Type env := { s : string; memo : constr array; rt1 : constr array; rt2 : (constr array) array;
                    cls : int array; far3 : int array; ids : (ident option) array; cprop : constr;
                    hh : constr array; ha : int array; ocl : int array }.

Ltac2 d1 (s : string) (p : int) : int := Int.sub (Char.to_int (String.get s p)) 35.
Ltac2 d2 (s : string) (p : int) : int :=
  Int.add (Int.mul (Char.to_int (String.get s p)) 92) (Int.sub (Char.to_int (String.get s (Int.add p 1))) 3255).
Ltac2 d3 (s : string) (p : int) : int :=
  Int.add (Int.mul (d2 s p) 92) (Int.sub (Char.to_int (String.get s (Int.add p 2))) 35).

(* [comment removed for export] *)
Ltac2 op1 (e : env) (p : int) (cm : int) (k : constr -> int -> unit) : unit :=
  let c := Char.to_int (String.get (e.(s)) p) in
  match Array.get (e.(cls)) c with
  | 0 => k (Array.get (e.(memo)) (Int.sub cm c)) (Int.add p 1)
  | 1 => k (Array.get (e.(rt1)) c) (Int.add p 1)
  | 2 => k (Array.get (Array.get (e.(rt2)) c) (Char.to_int (String.get (e.(s)) (Int.add p 1)))) (Int.add p 2)
  | 3 => let d := Int.add (Array.get (e.(far3)) c)
                    (Int.add (Int.mul (Char.to_int (String.get (e.(s)) (Int.add p 1))) 92)
                             (Char.to_int (String.get (e.(s)) (Int.add p 2)))) in
         k (Array.get (e.(memo)) (Int.sub cm d)) (Int.add p 3)
  | _ => let s := e.(s) in
         let d := Int.add (Int.mul (d2 s (Int.add p 1)) 8464) (d2 s (Int.add p 3)) in
         k (Array.get (e.(memo)) (Int.sub (Int.sub cm 35) d)) (Int.add p 5)
  end.

(* [comment removed for export] *)
Ltac2 rec ops (e : env) (a : constr array) (i : int) (n : int) (p : int) (cm : int) (k : int -> unit) : unit :=
  match Int.equal i n with
  | true => k p
  | false =>
    let c := Char.to_int (String.get (e.(s)) p) in
    match Array.get (e.(cls)) c with
    | 0 => Array.set a i (Array.get (e.(memo)) (Int.sub cm c)); ops e a (Int.add i 1) n (Int.add p 1) cm k
    | 1 => Array.set a i (Array.get (e.(rt1)) c); ops e a (Int.add i 1) n (Int.add p 1) cm k
    | 2 => Array.set a i (Array.get (Array.get (e.(rt2)) c) (Char.to_int (String.get (e.(s)) (Int.add p 1))));
           ops e a (Int.add i 1) n (Int.add p 2) cm k
    | 3 => let d := Int.add (Array.get (e.(far3)) c)
                      (Int.add (Int.mul (Char.to_int (String.get (e.(s)) (Int.add p 1))) 92)
                               (Char.to_int (String.get (e.(s)) (Int.add p 2)))) in
           Array.set a i (Array.get (e.(memo)) (Int.sub cm d)); ops e a (Int.add i 1) n (Int.add p 3) cm k
    | _ => let s := e.(s) in
           let d := Int.add (Int.mul (d2 s (Int.add p 1)) 8464) (d2 s (Int.add p 3)) in
           Array.set a i (Array.get (e.(memo)) (Int.sub (Int.sub cm 35) d)); ops e a (Int.add i 1) n (Int.add p 5) cm k
    end
  end.

Ltac2 rec names (e : env) (p : int) (n : int) : (ident option) list :=
  match Int.equal n 0 with
  | true => []
  | false => Array.get (e.(ids)) (d2 (e.(s)) p) :: names e (Int.add p 2) (Int.sub n 1)
  end.

Ltac2 rec mk_lams (e : env) (nas : (ident option) list) (body : constr) : constr :=
  match nas with
  | [] => body
  | x :: r => Unsafe.make (Unsafe.Lambda (Binder.unsafe_make x Binder.Relevant (e.(cprop))) (mk_lams e r body))
  end.

Ltac2 rec mk_pred (e : env) (nas : (ident option) list) (selfty : constr) (body : constr) : constr :=
  match nas with
  | [] => body
  | x :: r =>
    match r with
    | [] => Unsafe.make (Unsafe.Lambda (Binder.unsafe_make x Binder.Relevant selfty) body)
    | _ => Unsafe.make (Unsafe.Lambda (Binder.unsafe_make x Binder.Relevant (e.(cprop))) (mk_pred e r selfty body))
    end
  end.

Ltac2 rec branches (e : env) (a : constr array) (i : int) (n : int) (p : int) (cm : int) (k : int -> unit) : unit :=
  match Int.equal i n with
  | true => k p
  | false =>
    let nn := d1 (e.(s)) p in
    let nas := names e (Int.add p 1) nn in
    op1 e (Int.add (Int.add p 1) (Int.mul 2 nn)) cm (fun b p =>
      Array.set a i (mk_lams e nas b);
      branches e a (Int.add i 1) n p cm k)
  end.

Ltac2 rec varint46 (s : string) (p : int) (acc : int) (k : int -> int -> unit) : unit :=
  let d := d1 s p in
  match Int.lt d 46 with
  | true => varint46 s (Int.add p 1) (Int.add (Int.mul acc 46) d) k
  | false => k (Int.add (Int.mul acc 46) (Int.sub d 46)) (Int.add p 1)
  end.

Ltac2 rec fill_int (a : int array) (i : int) (n : int) (f : int -> int) : unit :=
  match Int.equal i n with
  | true => ()
  | false => Array.set a i (f i); fill_int a (Int.add i 1) n f
  end.

Ltac2 rec fixes (e : env) (bs : binder array) (bds : constr array) (i : int) (n : int) (p : int) (cm : int)
                (k : int -> unit) : unit :=
  match Int.equal i n with
  | true => k p
  | false =>
    let na := Array.get (e.(ids)) (d2 (e.(s)) p) in
    op1 e (Int.add p 2) cm (fun ty p => op1 e p cm (fun bd p =>
      Array.set bs i (Binder.unsafe_make na Binder.Relevant ty);
      Array.set bds i bd;
      fixes e bs bds (Int.add i 1) n p cm k))
  end.

Ltac2 bad_payload () := Control.throw (Invalid_argument (Some (Message.of_string "KReplay: malformed payload"))).

(* [comment removed for export] *)
Ltac2 rec nodes (e : env) (cur : int) (n : int) (p : int) (k : int -> unit) : unit :=
  match Int.equal cur n with
  | true => k p
  | false =>
    let c := Char.to_int (String.get (e.(s)) p) in
    let cm := Int.add cur 34 in
    let next x p := Array.set (e.(memo)) cur x; nodes e (Int.add cur 1) n p k in
    match Array.get (e.(ocl)) c with
    | 1 =>
      let f := Array.get (e.(hh)) c in
      op1 e (Int.add p 1) cm (fun a p => next (Unsafe.make (Unsafe.App f (Array.make 1 a))) p)
    | 2 =>
      let f := Array.get (e.(hh)) c in
      op1 e (Int.add p 1) cm (fun a p => op1 e p cm (fun b p =>
        let arr := Array.make 2 a in
        Array.set arr 1 b;
        next (Unsafe.make (Unsafe.App f arr)) p))
    | 3 =>
      let f := Array.get (e.(hh)) c in
      op1 e (Int.add p 1) cm (fun a p => op1 e p cm (fun b p => op1 e p cm (fun d p =>
        let arr := Array.make 3 a in
        Array.set arr 1 b;
        Array.set arr 2 d;
        next (Unsafe.make (Unsafe.App f arr)) p)))
    | 4 =>
      let f := Array.get (e.(hh)) c in
      let na := Array.get (e.(ha)) c in
      let arr := Array.make na f in
      ops e arr 0 na (Int.add p 1) cm (fun p => next (Unsafe.make (Unsafe.App f arr)) p)
    | 5 =>
      op1 e (Int.add p 1) cm (fun f p => op1 e p cm (fun a p =>
        next (Unsafe.make (Unsafe.App f (Array.make 1 a))) p))
    | 6 =>
      op1 e (Int.add p 1) cm (fun f p => op1 e p cm (fun a p => op1 e p cm (fun b p =>
        let arr := Array.make 2 a in
        Array.set arr 1 b;
        next (Unsafe.make (Unsafe.App f arr)) p)))
    | 7 =>
      let na := Int.sub c 84 in
      op1 e (Int.add p 1) cm (fun f p =>
        let arr := Array.make na f in
        ops e arr 0 na p cm (fun p => next (Unsafe.make (Unsafe.App f arr)) p))
    | _ =>
      match Int.sub c 35 with
      | 70 =>
        let na := d2 (e.(s)) (Int.add p 1) in
        op1 e (Int.add p 3) cm (fun f p =>
          let a := Array.make na f in
          ops e a 0 na p cm (fun p => next (Unsafe.make (Unsafe.App f a)) p))
      | 71 =>
        let na := Array.get (e.(ids)) (d2 (e.(s)) (Int.add p 1)) in
        op1 e (Int.add p 3) cm (fun ty p => op1 e p cm (fun b p =>
          next (Unsafe.make (Unsafe.Lambda (Binder.unsafe_make na Binder.Relevant ty) b)) p))
      | 72 =>
        let na := Array.get (e.(ids)) (d2 (e.(s)) (Int.add p 1)) in
        op1 e (Int.add p 3) cm (fun ty p => op1 e p cm (fun b p =>
          next (Unsafe.make (Unsafe.Prod (Binder.unsafe_make na Binder.Relevant ty) b)) p))
      | 73 =>
        let na := Array.get (e.(ids)) (d2 (e.(s)) (Int.add p 1)) in
        op1 e (Int.add p 3) cm (fun v p => op1 e p cm (fun ty p => op1 e p cm (fun b p =>
          next (Unsafe.make (Unsafe.LetIn (Binder.unsafe_make na Binder.Relevant ty) v b)) p)))
      | 74 =>
        let ck := match d1 (e.(s)) (Int.add p 1) with | 0 => Cast.default | 1 => Cast.vm | _ => Cast.native end in
        op1 e (Int.add p 2) cm (fun t p => op1 e p cm (fun ty p =>
          next (Unsafe.make (Unsafe.Cast t ck ty)) p))
      | 75 =>
        op1 e (Int.add p 1) cm (fun indc p =>
          let ind := match Unsafe.kind indc with
                     | Unsafe.Ind i _ => i
                     | _ => bad_payload ()
                     end in
          let npar := d1 (e.(s)) p in
          let pms := Array.make npar indc in
          ops e pms 0 npar (Int.add p 1) cm (fun p =>
            let nnas := d1 (e.(s)) p in
            let nas := names e (Int.add p 1) nnas in
            op1 e (Int.add (Int.add p 1) (Int.mul 2 nnas)) cm (fun pbody p =>
              op1 e p cm (fun scrut p =>
                let lifted := match Int.equal nnas 1 with
                              | true => pms
                              | false => Array.map (fun c => Unsafe.liftn (Int.sub nnas 1) 1 c) pms
                              end in
                let selfty := match Int.equal npar 0 with
                              | true => indc
                              | false => Unsafe.make (Unsafe.App indc lifted)
                              end in
                let pred := mk_pred e nas selfty pbody in
                let nbr := d2 (e.(s)) p in
                let brs := Array.make nbr indc in
                branches e brs 0 nbr (Int.add p 2) cm (fun p =>
                  next (Unsafe.make (Unsafe.Case (Unsafe.case ind) (pred, Binder.Relevant) Unsafe.NoInvert scrut brs)) p)))))
      | 76 => varint46 (e.(s)) (Int.add p 1) 0 (fun v p => next (Unsafe.make (Unsafe.Uint63 (Uint63.of_int v))) p)
      | 77 =>
        let nf := d1 (e.(s)) (Int.add p 1) in
        let fi := d1 (e.(s)) (Int.add p 2) in
        let rec_ := Array.make nf 0 in
        fill_int rec_ 0 nf (fun j => d1 (e.(s)) (Int.add (Int.add p 3) j));
        let dummy := e.(cprop) in
        let bs := Array.make nf (Binder.unsafe_make None Binder.Relevant dummy) in
        let bds := Array.make nf dummy in
        fixes e bs bds 0 nf (Int.add (Int.add p 3) nf) cm (fun p =>
          next (Unsafe.make (Unsafe.Fix rec_ fi bs bds)) p)
      | _ => bad_payload ()
      end
    end
  end.

(* [comment removed for export] *)
Ltac2 rec fill_rt (s : string) (p : int) (i : int) (n : int) (nrel : int) (tab : constr array)
                  (sorts : constr array) (rt1 : constr array) (rt2 : (constr array) array) : unit :=
  match Int.equal i n with
  | true => ()
  | false =>
    let src := d2 s p in
    let c := match Int.lt src nrel with
             | true => Unsafe.make (Unsafe.Rel (Int.add src 1))
             | false => match Int.lt src (Int.add nrel 3) with
                        | true => Array.get sorts (Int.sub src nrel)
                        | false => Array.get tab (Int.sub (Int.sub src nrel) 3)
                        end
             end in
    (match Int.lt i 16 with
     | true => Array.set rt1 (Int.add i 67) c
     | false => let j := Int.sub i 16 in
                Array.set (Array.get rt2 (Int.add (Int.div j 92) 83)) (Int.add (Int.mod j 92) 35) c
     end);
    fill_rt s (Int.add p 2) (Int.add i 1) n nrel tab sorts rt1 rt2
  end.

Ltac2 rec fill_rows (a : (constr array) array) (i : int) (n : int) (dummy : constr) : unit :=
  match Int.equal i n with
  | true => ()
  | false => Array.set a i (Array.make 128 dummy); fill_rows a (Int.add i 1) n dummy
  end.

Ltac2 rec fill_ids (a : (ident option) array) (ids : ident array) (i : int) (n : int) : unit :=
  match Int.equal i n with
  | true => ()
  | false => Array.set a (Int.add i 1) (Some (Array.get ids i)); fill_ids a ids (Int.add i 1) n
  end.

Ltac2 rec fill_ht (s : string) (p : int) (i : int) (n : int) (rt1 : constr array) (rt2 : (constr array) array)
                  (hh : constr array) (ha : int array) (ocl : int array) : unit :=
  match Int.equal i n with
  | true => ()
  | false =>
    let h := d2 s p in
    let a := d1 s (Int.add p 2) in
    let c := match Int.lt h 16 with
             | true => Array.get rt1 (Int.add h 67)
             | false => let j := Int.sub h 16 in
                        Array.get (Array.get rt2 (Int.add (Int.div j 92) 83)) (Int.add (Int.mod j 92) 35)
             end in
    Array.set hh (Int.add i 35) c;
    Array.set ha (Int.add i 35) a;
    Array.set ocl (Int.add i 35) (match Int.lt a 4 with | true => a | false => 4 end);
    fill_ht s (Int.add p 3) (Int.add i 1) n rt1 rt2 hh ha ocl
  end.

Ltac2 decode (tab : constr array) (ids : ident array) (s : string) (k : constr -> unit) : unit :=
  let cp := constr:(Prop) in
  let sorts := Array.make 3 cp in
  Array.set sorts 1 constr:(Set);
  Array.set sorts 2 constr:(SProp);
  let n := d3 s 0 in
  let nrel := d2 s 3 in
  let nrt := d2 s 5 in
  let rt1 := Array.make 128 cp in
  let rt2 := Array.make 128 rt1 in
  (match Int.lt 16 nrt with
   | true => fill_rows rt2 83 (Int.add 84 (Int.div (Int.sub nrt 17) 92)) cp
   | false => ()
   end);
  fill_rt s 7 0 nrt nrel tab sorts rt1 rt2;
  (* [comment removed for export] *)
  let cls := Array.make 128 0 in
  fill_int cls 67 83 (fun _ => 1);
  fill_int cls 83 115 (fun _ => 2);
  fill_int cls 115 126 (fun _ => 3);
  Array.set cls 126 4;
  (* [comment removed for export] *)
  let far3 := Array.make 128 0 in
  fill_int far3 115 126 (fun c => Int.sub (Int.add 67 (Int.mul (Int.sub c 115) 8464)) 3255);
  let idt := Array.make (Int.add (Array.length ids) 1) None in
  fill_ids idt ids 0 (Array.length ids);
  (* [comment removed for export] *)
  let p0 := Int.add 7 (Int.mul 2 nrt) in
  let nht := d1 s p0 in
  let hh := Array.make 128 cp in
  let ha := Array.make 128 0 in
  let ocl := Array.make 128 0 in
  fill_ht s (Int.add p0 1) 0 nht rt1 rt2 hh ha ocl;
  Array.set ocl 85 5;
  Array.set ocl 86 6;
  fill_int ocl 87 105 (fun _ => 7);
  let e := { s := s; memo := Array.make (Int.add n 1) cp; rt1 := rt1; rt2 := rt2; cls := cls; far3 := far3;
             ids := idt; cprop := cp; hh := hh; ha := ha; ocl := ocl } in
  nodes e 0 n (Int.add (Int.add p0 1) (Int.mul 3 nht)) (fun p => op1 e p (Int.add n 34) (fun c _ => k c)).

Ltac2 run (tab : constr array) (ids : ident array) (s : string) : unit :=
  decode tab ids s (fun c => Std.exact_no_check c).

(* [comment removed for export] *)
Ltac2 runc (tab : constr array) (ids : ident array) (s : string) : unit :=
  decode tab ids s (fun c =>
    match Unsafe.check c with
    | Val c' => Std.exact_no_check c'
    | Err e => Control.throw e
    end).

(* [comment removed for export] *)
Ltac2 rec nav (c : constr) (p : int list) : constr :=
  match p with
  | [] => c
  | i :: r =>
    match Unsafe.kind c with
    | Unsafe.Prod b body => nav (match i with | 0 => Binder.type b | _ => body end) r
    | Unsafe.Lambda b body => nav (match i with | 0 => Binder.type b | _ => body end) r
    | Unsafe.LetIn b v body => nav (match i with | 0 => Binder.type b | 1 => v | _ => body end) r
    | Unsafe.App f args => nav (match i with | 0 => f | _ => Array.get args (Int.sub i 1) end) r
    | Unsafe.Cast t _ ty => nav (match i with | 0 => t | _ => ty end) r
    | _ => bad_payload ()
    end
  end.
Ltac2 sort_at (c : constr) (p : int list) : constr := nav (Constr.type c) p.

(* [comment removed for export] *)
Ltac2 app_hyps (c : constr) (hs : ident array) : constr :=
  Unsafe.make (Unsafe.App c (Array.map (fun h => Control.hyp h) hs)).
Ltac2 runh (hs : ident array) (tab : constr array) (ids : ident array) (s : string) : unit :=
  decode tab ids s (fun c => Std.exact_no_check (app_hyps c hs)).
Ltac2 runch (hs : ident array) (tab : constr array) (ids : ident array) (s : string) : unit :=
  decode tab ids s (fun c =>
    match Unsafe.check (app_hyps c hs) with
    | Val c' => Std.exact_no_check c'
    | Err e => Control.throw e
    end).
