(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import ITree.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Export PrintfModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Notation "'let?' x ':=' e 'in' k" :=
  (match e with Some x => k | None => None end)
  (at level 200, x pattern, e at level 100, k at level 200, only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition T_LONG : Z := 13.  Definition T_ULONG : Z := 14.
Definition LPRE : Z := 1.

(* [comment removed for export] *)
Definition PA_l (i : Z) : parg := PA_z (i mod 2^64).

(* [comment removed for export] *)
Definition conv_typex (t : Z) : option Z :=
  if t =? 99 then Some T_INT else conv_type t.
(* [comment removed for export] *)
Definition conv_type_l (t : Z) : option Z :=
  if (t =? 100) || (t =? 105) then Some T_LONG
  else if (t =? 117) || (t =? 120) || (t =? 88) then Some T_ULONG
  else None.
Definition conv_statex (s : list Z) : option (Z * Z * nat) :=
  match s with
  | [] => None
  | t :: s' =>
      if t =? 122 then                                                     (* [comment removed for export] *)
        match s' with
        | [] => None
        | t2 :: _ => let? ty := conv_type_z t2 in Some (ty, ZTPRE, 2%nat)
        end
      else if t =? 108 then                                                (* [comment removed for export] *)
        match s' with
        | [] => None
        | t2 :: _ => let? ty := conv_type_l t2 in Some (ty, LPRE, 2%nat)
        end
      else let? ty := conv_typex t in Some (ty, 0, 1%nat)
  end.
(* [comment removed for export] *)
Definition dir_psx (d : dir) : Z :=
  if d_ty d =? T_SIZET then ZTPRE else if (d_ty d =? T_LONG) || (d_ty d =? T_ULONG) then LPRE else 0.

(* [comment removed for export] *)
Definition stars : Type := (bool * bool)%type.
Definition nostars : stars := (false, false).

(* [comment removed for export] *)
Definition parse_dirx (s : list Z) : option (dir * stars * list Z) :=
  let positional := match s with
                    | c1 :: c2 :: _ => is_digit c1 && (c2 =? 36)
                    | [c1] => is_digit c1
                    | [] => false
                    end in
  if positional then None else
  let '(fl, s1) := parse_flags s 0 in
  match s1 with
  | [] => None
  | c1 :: s1' =>
    let wr : option (Z * bool * list Z) :=
      if c1 =? 42 then                                                     (* [comment removed for export] *)
        match s1' with
        | [] => None
        | c2 :: _ => if is_digit c2 then None else Some (0, true, s1')
        end
      else let? (w, s2) := getint s1 0 in Some (w, false, s2) in
    match wr with
    | None => None
    | Some (w, ws, s2) =>
      match s2 with
      | [] => None
      | c2 :: s2' =>
        let pxs : option (Z * bool * bool * list Z) :=                    (* [comment removed for export] *)
          if c2 =? 46 then                                                 (* [comment removed for export] *)
            match s2' with
            | [] => None
            | c3 :: s3' => if c3 =? 42 then                                (* [comment removed for export] *)
                             match s3' with
                             | [] => None
                             | c4 :: _ => if is_digit c4 then None          (* [comment removed for export] *)
                                          else Some (0, true, true, s3')
                             end
                           else let? (p, s3) := getint s2' 0 in Some (p, true, false, s3)
            end
          else Some (-1, false, false, s2) in
        match pxs with
        | None => None
        | Some (p, xp, ps, s3) =>
          let? (ty, pst, n) := conv_statex s3 in
          Some (mkDir fl w p xp (nth (n - 1)%nat s3 0) ty, (ws, ps), skipn n s3)
        end
      end
    end
  end.

(* [comment removed for export] *)
Definition dir_eff_w (d : dir) (ws : bool) (args : list parg) : option (dir * list parg) :=
  if ws then
    match args with
    | PA_i wv :: args' =>
        if (wv <? -2147483647) || (2147483647 <? wv) then None
        else Some (mkDir (if wv <? 0 then Z.lor (d_fl d) LEFT_ADJ else d_fl d) (Z.abs wv) (d_p d) (d_xp d) (d_t d) (d_ty d), args')
    | _ => None
    end
  else Some (d, args).
Definition dir_eff_p (d : dir) (ps : bool) (args : list parg) : option (dir * list parg) :=
  if ps then
    match args with
    | PA_i pv :: args' =>
        if (pv <? 0) || (2147483647 <? pv) then None
        else Some (mkDir (d_fl d) (d_w d) pv true (d_t d) (d_ty d), args')
    | _ => None
    end
  else Some (d, args).
Definition dir_eff (d : dir) (st : stars) (args : list parg) : option (dir * list parg) :=
  let? (d1, args1) := dir_eff_w d (fst st) args in dir_eff_p d1 (snd st) args1.

Section PrintfModelX.
  Context {St : Type}.
  Variable OUT : list Z -> M St unit.
  Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.

  (* [comment removed for export] *)
  Definition convx (cnt : Z) (d : dir) (a : parg) : M St Z :=
    let fl := if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD) in
    let w := d_w d in let p := d_p d in let xp := d_xp d in let t := d_t d in
    match a with
    | PA_s s =>                                                             (* [comment removed for export] *)
        if negb (d_ty d =? T_PTR) then munr else
        if (p <? 0) && (INT_MAX <=? zlength s) then munr else
        let n := if p <? 0 then zlength s else Z.min (zlength s) p in
        conv_tail OUT cnt (Z.land fl (Z.lnot ZERO_PAD)) w n [] (firstn (Z.to_nat n) s)
    | PA_sn =>                                                              (* [comment removed for export] *)
        if negb (d_ty d =? T_PTR) then munr else
        let s := NULLSTR in
        if (p <? 0) && (INT_MAX <=? zlength s) then munr else
        let n := if p <? 0 then zlength s else Z.min (zlength s) p in
        conv_tail OUT cnt (Z.land fl (Z.lnot ZERO_PAD)) w n [] (firstn (Z.to_nat n) s)
    | PA_i i =>                                                             (* [comment removed for export] *)
        if negb (d_ty d =? T_INT) then munr else
        if t =? 99 then conv_tail OUT cnt (Z.land fl (Z.lnot ZERO_PAD)) w 1 [] [i mod 256]
        else
        let argi := i mod 2^64 in
        let '(argi, prefix) :=
          if INTMAX_MAX <? argi then ((- argi) mod 2^64, [45])
          else if negb (Z.land fl MARK_POS =? 0) then (argi, [43])
          else if negb (Z.land fl PAD_POS =? 0) then (argi, [32])
          else (argi, []) in
        conv_int OUT cnt fl w p xp argi prefix (dec_digits argi)
    | PA_u u =>                                                             (* [comment removed for export] *)
        if negb (d_ty d =? T_UINT) then munr else
        if t =? 117 then conv_int OUT cnt fl w p xp u [] (dec_digits u)
        else
          let prefix := if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0)
                        then (if t =? 120 then [48; 120] else [48; 88]) else [] in
          conv_int OUT cnt fl w p xp u prefix (hex_digits (Z.land t 32) u)
    | PA_z u =>                                                             (* [comment removed for export] *)
        if (d_ty d =? T_SIZET) || (d_ty d =? T_ULONG) then
          (if t =? 117 then conv_int OUT cnt fl w p xp u [] (dec_digits u)
           else if (t =? 120) || (t =? 88) then
             let prefix := if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0)
                           then (if t =? 120 then [48; 120] else [48; 88]) else [] in
             conv_int OUT cnt fl w p xp u prefix (hex_digits (Z.land t 32) u)
           else munr)
        else if d_ty d =? T_LONG then
          let '(argi, prefix) :=
            if INTMAX_MAX <? u then ((- u) mod 2^64, [45])
            else if negb (Z.land fl MARK_POS =? 0) then (u, [43])
            else if negb (Z.land fl PAD_POS =? 0) then (u, [32])
            else (u, []) in
          conv_int OUT cnt fl w p xp argi prefix (dec_digits argi)
        else munr
    | PA_g dd =>                                                            (* [comment removed for export] *)
        if negb (d_ty d =? T_DBL) then munr else
        if xp && (p <? 0) then munr else
        if (1 <? w) || (2^20 <=? p) then munr else
        r <- OUTFP dd w p fl t ;;
        if (r <? 0) || (INT_MAX - cnt <? r) then munr else mret (cnt + r)
    end.

  Fixpoint printf_loopx (fuel : nat) (s : list Z) (args : list parg) (cnt : Z) {struct fuel} : M St Z :=
    match fuel with
    | O => munr
    | S fuel' =>
      match s with
      | [] => munr
      | c :: _ =>
        if c =? 0 then mret cnt else
        let lit := lit_run s in
        let l := zlength lit in
        let s1 := skipn (Datatypes.length lit) s in
        match s1 with
        | [] => munr
        | c1 :: s2 =>
          if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end
          then munr
          else if 0 <? l then
            (if INT_MAX - cnt <? l then munr
             else OUT lit ;;; printf_loopx fuel' s1 args (cnt + l))
          else
            match parse_dirx s2 with
            | Some (d0, st, s3) =>
                match dir_eff d0 st args with
                | Some (d, a :: args') =>
                    OUT [] ;;;
                    cnt' <- convx cnt d a ;;
                    printf_loopx fuel' s3 args' cnt'
                | _ => munr
                end
            | None => munr
            end
        end
      end
    end.

  Definition printf_modelx (fmt : list Z) (args : list parg) : M St Z :=
    printf_loopx (Datatypes.length fmt) fmt args 0.
End PrintfModelX.

Arguments convx {St} OUT OUTFP _ _ _.
Arguments printf_loopx {St} OUT OUTFP _ _ _ _.
Arguments printf_modelx {St} OUT OUTFP _ _.

Fixpoint fp_callsx (fuel : nat) (s : list Z) (args : list parg) {struct fuel} : list (Z * Z * Z * Z * Z) :=
  match fuel with
  | O => []
  | S fuel' =>
    match s with
    | [] => []
    | c :: _ =>
      if c =? 0 then [] else
      let lit := lit_run s in
      let s1 := skipn (Datatypes.length lit) s in
      if 0 <? zlength lit then fp_callsx fuel' s1 args
      else match s1 with
           | _ :: s2 =>
             match parse_dirx s2 with
             | Some (d0, st, s3) =>
                 match dir_eff d0 st args with
                 | Some (d, a :: args') =>
                     match a with
                     | PA_g dd =>
                         let fl := if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD) in
                         (dd, d_w d, d_p d, fl, d_t d) :: fp_callsx fuel' s3 args'
                     | _ => fp_callsx fuel' s3 args'
                     end
                 | _ => []
                 end
             | None => []
             end
           | _ => []
           end
    end
  end.

Definition pass1x_ok (fmt : list Z) : bool :=
  let lit := lit_run fmt in
  (zlength lit <=? INT_MAX) &&
  match skipn (Datatypes.length lit) fmt with
  | [] => false
  | c1 :: s2 =>
      if c1 =? 0 then true
      else match s2 with
           | [] => false
           | c2 :: _ => negb (c2 =? 37) && match parse_dirx s2 with Some _ => true | None => false end
           end
  end.

Definition conv_piecesx (cnt : Z) (d : dir) (a : parg) : option (list (list Z) * Z) :=
  let fl := if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD) in
  let w := d_w d in let p := d_p d in let xp := d_xp d in let t := d_t d in
  match a with
  | PA_s s =>
      if negb (d_ty d =? T_PTR) then None else
      if (p <? 0) && (INT_MAX <=? zlength s) then None else
      let n := if p <? 0 then zlength s else Z.min (zlength s) p in
      tail_pieces cnt (Z.land fl (Z.lnot ZERO_PAD)) w n [] (firstn (Z.to_nat n) s)
  | PA_sn =>
      if negb (d_ty d =? T_PTR) then None else
      let s := NULLSTR in
      if (p <? 0) && (INT_MAX <=? zlength s) then None else
      let n := if p <? 0 then zlength s else Z.min (zlength s) p in
      tail_pieces cnt (Z.land fl (Z.lnot ZERO_PAD)) w n [] (firstn (Z.to_nat n) s)
  | PA_i i =>
      if negb (d_ty d =? T_INT) then None else
      if t =? 99 then tail_pieces cnt (Z.land fl (Z.lnot ZERO_PAD)) w 1 [] [i mod 256]
      else
      let argi := i mod 2^64 in
      let '(argi, prefix) :=
        if INTMAX_MAX <? argi then ((- argi) mod 2^64, [45])
        else if negb (Z.land fl MARK_POS =? 0) then (argi, [43])
        else if negb (Z.land fl PAD_POS =? 0) then (argi, [32])
        else (argi, []) in
      int_pieces cnt fl w p xp argi prefix (dec_digits argi)
  | PA_u u =>
      if negb (d_ty d =? T_UINT) then None else
      if t =? 117 then int_pieces cnt fl w p xp u [] (dec_digits u)
      else
        let prefix := if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0)
                      then (if t =? 120 then [48; 120] else [48; 88]) else [] in
        int_pieces cnt fl w p xp u prefix (hex_digits (Z.land t 32) u)
  | PA_z u =>
      if (d_ty d =? T_SIZET) || (d_ty d =? T_ULONG) then
        (if t =? 117 then int_pieces cnt fl w p xp u [] (dec_digits u)
         else if (t =? 120) || (t =? 88) then
           let prefix := if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0)
                         then (if t =? 120 then [48; 120] else [48; 88]) else [] in
           int_pieces cnt fl w p xp u prefix (hex_digits (Z.land t 32) u)
         else None)
      else if d_ty d =? T_LONG then
        let '(argi, prefix) :=
          if INTMAX_MAX <? u then ((- u) mod 2^64, [45])
          else if negb (Z.land fl MARK_POS =? 0) then (u, [43])
          else if negb (Z.land fl PAD_POS =? 0) then (u, [32])
          else (u, []) in
        int_pieces cnt fl w p xp argi prefix (dec_digits argi)
      else None
  | PA_g _ => None
  end.

Fixpoint printf_piecesx_loop (fuel : nat) (s : list Z) (args : list parg) (cnt : Z) {struct fuel}
    : option (list (list Z) * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
    match s with
    | [] => None
    | c :: _ =>
      if c =? 0 then Some ([], cnt) else
      let lit := lit_run s in
      let l := zlength lit in
      let s1 := skipn (Datatypes.length lit) s in
      match s1 with
      | [] => None
      | c1 :: s2 =>
        if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end then None
        else if 0 <? l then
          (if INT_MAX - cnt <? l then None
           else let? (ps, r) := printf_piecesx_loop fuel' s1 args (cnt + l) in Some (lit :: ps, r))
        else
          match parse_dirx s2 with
          | Some (d0, st, s3) =>
              match dir_eff d0 st args with
              | Some (d, a :: args') =>
                  let? (ps1, cnt') := conv_piecesx cnt d a in
                  let? (ps, r) := printf_piecesx_loop fuel' s3 args' cnt' in
                  Some ([] :: ps1 ++ ps, r)
              | _ => None
              end
          | None => None
          end
      end
    end
  end.

Definition printf_piecesx (fmt : list Z) (args : list parg) : option (list (list Z) * Z) :=
  printf_piecesx_loop (Datatypes.length fmt) fmt args 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nstars (st : stars) : Z := (if fst st then 1 else 0) + (if snd st then 1 else 0).

(* [comment removed for export] *)
Fixpoint arg_covs (fuel : nat) (s : list Z) (args : list parg) {struct fuel} : list (option Z) :=
  match fuel with
  | O => []
  | S fuel' =>
    match s with
    | [] => []
    | c :: _ =>
      if c =? 0 then [] else
      let lit := lit_run s in
      let s1 := skipn (Datatypes.length lit) s in
      if 0 <? zlength lit then arg_covs fuel' s1 args
      else match s1 with
           | _ :: s2 =>
             match parse_dirx s2 with
             | Some (d0, st, s3) =>
                 match dir_eff d0 st args with
                 | Some (d, a :: args') =>
                     repeat None (Z.to_nat (nstars st)) ++ (if d_xp d then Some (d_p d) else None) :: arg_covs fuel' s3 args'
                 | _ => []
                 end
             | None => []
             end
           | _ => []
           end
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma conv_type_x : forall t ty, conv_type t = Some ty -> conv_typex t = Some ty /\ t <> 99.
Proof.
  intros t ty H. unfold conv_typex. destruct (Z.eqb_spec t 99) as [->|NE].
  - cbv in H. discriminate.
  - auto.
Qed.

Lemma conv_state_x : forall s ty ps n, conv_state s = Some (ty, ps, n) ->
  conv_statex s = Some (ty, ps, n) /\ nth (n - 1)%nat s 0 <> 99.
Proof.
  intros [|t s'] ty ps n H; [discriminate|]. cbn [conv_state conv_statex] in *.
  destruct (Z.eqb_spec t 122) as [->|NZ].
  - destruct s' as [|t2 s'']; [discriminate|]. destruct (conv_type_z t2) eqn:CZ; [|discriminate].
    injection H as <- <- <-. split; [reflexivity|]. cbn. unfold conv_type_z in CZ.
    destruct (Z.eqb_spec t2 117); [lia|discriminate].
  - destruct (conv_type t) as [ty0|] eqn:CT; [|discriminate]. injection H as <- <- <-.
    destruct (conv_type_x t ty0 CT) as [-> NE]. destruct (Z.eqb_spec t 108) as [->|NL].
    + cbv in CT. discriminate.
    + split; [reflexivity|]. cbn. exact NE.
Qed.

Lemma dir_eff_nostars : forall d args, dir_eff d nostars args = Some (d, args).
Proof. reflexivity. Qed.

Lemma parse_dir_x : forall s d rest, parse_dir s = Some (d, rest) ->
  parse_dirx s = Some (d, nostars, rest) /\ d_t d <> 99.
Proof.
  intros s d rest H. unfold parse_dir in H. unfold parse_dirx.
  destruct (match s with | [] => false | [c1] => is_digit c1 | c1 :: c2 :: _ => is_digit c1 && (c2 =? 36) end); [discriminate|].
  destruct (parse_flags s 0) as [fl s1]. destruct s1 as [|c1 s1']; [discriminate|].
  destruct (Z.eqb_spec c1 42) as [->|NS]; [discriminate|].
  destruct (getint (c1 :: s1') 0) as [[w s2]|]; [|discriminate]. cbn iota beta.
  destruct s2 as [|c2 s2']; [discriminate|].
  assert (PX : exists p xp s3, (if c2 =? 46 then match s2' with [] => None | c3 :: _ => if c3 =? 42 then None else let? (p, s3) := getint s2' 0 in Some (p, true, s3) end
                               else Some (-1, false, c2 :: s2')) = Some (p, xp, s3)
    /\ (if c2 =? 46 then match s2' with [] => None | c3 :: s3' => if c3 =? 42 then match s3' with [] => None | c4 :: _ => if is_digit c4 then None else Some (0, true, true, s3') end
                                                        else let? (p, s3) := getint s2' 0 in Some (p, true, false, s3) end
        else Some (-1, false, false, c2 :: s2')) = Some (p, xp, false, s3)).
  { destruct (c2 =? 46).
    - destruct s2' as [|c3 s3']; [discriminate|]. destruct (c3 =? 42); [discriminate|].
      destruct (getint (c3 :: s3') 0) as [[p s3]|]; [|discriminate]. exists p, true, s3. split; reflexivity.
    - exists (-1), false, (c2 :: s2'). split; reflexivity. }
  destruct PX as (p & xp & s3 & E1 & E2). rewrite E1 in H. rewrite E2.
  destruct (conv_state s3) as [[[ty ps] n]|] eqn:CS; [|discriminate].
  destruct (conv_state_x s3 ty ps n CS) as [-> NE].
  injection H as <- <-. split; [reflexivity | cbn; exact NE].
Qed.

Lemma pass1_ok_x : forall fmt, pass1_ok fmt = true -> pass1x_ok fmt = true.
Proof.
  intros fmt H. unfold pass1_ok in H. unfold pass1x_ok.
  destruct (zlength (lit_run fmt) <=? INT_MAX); [|discriminate]. cbn [andb] in *.
  destruct (skipn (Datatypes.length (lit_run fmt)) fmt) as [|c1 s2]; [discriminate|].
  destruct (c1 =? 0); [reflexivity|]. destruct s2 as [|c2 s2']; [discriminate|].
  destruct (c2 =? 37); [discriminate|]. cbn [negb andb] in *.
  destruct (parse_dir (c2 :: s2')) as [[d rest]|] eqn:PD; [|discriminate].
  rewrite (proj1 (parse_dir_x _ _ _ PD)). reflexivity.
Qed.

Lemma conv_pieces_x : forall cnt d a r, d_t d <> 99 -> conv_pieces cnt d a = Some r -> conv_piecesx cnt d a = Some r.
Proof.
  intros cnt d a r NT H. unfold conv_pieces in H. unfold conv_piecesx.
  destruct a as [s| |i|u|u|dd]; try exact H.
  - destruct (Z.eqb_spec (d_t d) 99); [lia|]. exact H.
  - destruct (Z.eqb_spec (d_ty d) T_SIZET) as [E|NE]; [|discriminate]. cbn [negb orb] in *.
    destruct (d_t d =? 117); [exact H | discriminate].
Qed.

Lemma printf_pieces_loop_x : forall fuel s args cnt r,
  printf_pieces_loop fuel s args cnt = Some r -> printf_piecesx_loop fuel s args cnt = Some r.
Proof.
  induction fuel as [|fuel IH]; intros s args cnt r H; [discriminate|].
  cbn [printf_pieces_loop printf_piecesx_loop] in *.
  destruct s as [|c s']; [discriminate|].
  destruct (c =? 0); [exact H|].
  destruct (skipn (Datatypes.length (lit_run (c :: s'))) (c :: s')) as [|c1 s2]; [discriminate|].
  destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end); [discriminate|].
  destruct (0 <? zlength (lit_run (c :: s'))).
  - destruct (INT_MAX - cnt <? zlength (lit_run (c :: s'))); [discriminate|].
    destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength (lit_run (c :: s')))) as [[ps r0]|] eqn:E; [|discriminate].
    rewrite (IH _ _ _ _ E). exact H.
  - destruct (parse_dir s2) as [[d s3]|] eqn:PD; [|discriminate].
    destruct (parse_dir_x _ _ _ PD) as [-> NT]. rewrite dir_eff_nostars.
    destruct args as [|a args']; [discriminate|].
    destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:CP; [|discriminate].
    rewrite (conv_pieces_x _ _ _ _ NT CP).
    destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps r0]|] eqn:E; [|discriminate].
    rewrite (IH _ _ _ _ E). exact H.
Qed.

Lemma printf_pieces_x : forall fmt args r, printf_pieces fmt args = Some r -> printf_piecesx fmt args = Some r.
Proof. intros fmt args r. apply printf_pieces_loop_x. Qed.

(* [comment removed for export] *)
Definition not_flt (a : parg) : Prop := match a with PA_g _ => False | _ => True end.
Lemma fp_callsx_nog : forall fuel s args, Forall not_flt args -> fp_callsx fuel s args = [].
Proof.
  induction fuel as [|fuel IH]; intros s args NA; [reflexivity|]. cbn [fp_callsx].
  destruct s as [|c s']; [reflexivity|]. destruct (c =? 0); [reflexivity|].
  destruct (0 <? zlength (lit_run (c :: s'))); [apply IH; exact NA|].
  destruct (skipn (Datatypes.length (lit_run (c :: s'))) (c :: s')) as [|c1 s2]; [reflexivity|].
  destruct (parse_dirx s2) as [[[d0 [ws ps]] s3]|]; [|reflexivity].
  destruct (dir_eff d0 (ws, ps) args) as [[d args1]|] eqn:DE; [|reflexivity].
  assert (NA1 : Forall not_flt args1).
  { unfold dir_eff in DE. cbn [fst snd] in DE.
    destruct (dir_eff_w d0 ws args) as [[d1 args0]|] eqn:DW; [|discriminate].
    assert (NA0 : Forall not_flt args0).
    { unfold dir_eff_w in DW. destruct ws.
      - destruct args as [|[| |wv| | |] args']; try discriminate.
        destruct ((wv <? -2147483647) || (2147483647 <? wv)); [discriminate|].
        injection DW as _ <-. inversion NA; assumption.
      - injection DW as _ <-. exact NA. }
    unfold dir_eff_p in DE. destruct ps.
    - destruct args0 as [|[| |pv| | |] args']; try discriminate.
      destruct ((pv <? 0) || (2147483647 <? pv)); [discriminate|].
      injection DE as _ <-. inversion NA0; assumption.
    - injection DE as _ <-. exact NA0. }
  destruct args1 as [|a args']; [reflexivity|]. inversion NA1; subst.
  destruct a; try (apply IH; assumption). cbn in H1. destruct H1.
Qed.
Lemma fp_calls_nog : forall fuel s args, Forall not_flt args -> fp_calls fuel s args = [].
Proof.
  induction fuel as [|fuel IH]; intros s args NA; [reflexivity|]. cbn [fp_calls].
  destruct s as [|c s']; [reflexivity|]. destruct (c =? 0); [reflexivity|].
  destruct (0 <? zlength (lit_run (c :: s'))); [apply IH; exact NA|].
  destruct (skipn (Datatypes.length (lit_run (c :: s'))) (c :: s')) as [|c1 s2]; [reflexivity|].
  destruct (parse_dir s2) as [[d s3]|]; [|reflexivity].
  destruct args as [|a args']; [reflexivity|]. inversion NA; subst.
  destruct a; try (apply IH; assumption). cbn in H1. destruct H1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Example ep10_F1 : printf_piecesx (str "%5ld:d=%-2d hl=%ld l=%4ld %s" ++ [0]) [PA_z 17; PA_i 3; PA_z 2; PA_z 123; PA_s (str "cons: ")]
  = Some ([[]; [32; 32; 32]; []; [49; 55]; str ":d="; []; []; [51]; [32]; str " hl="; []; []; [50]; str " l="; []; [32]; []; [49; 50; 51]; [32]; []; []; str "cons: "], 29).
Proof. vm_compute. reflexivity. Qed.
Example ep10_F1neg : printf_piecesx (str "%5ld|" ++ [0]) [PA_l (-17)] = Some ([[]; [32; 32]; [45]; [49; 55]; str "|"], 6).
Proof. vm_compute. reflexivity. Qed.
Example ep10_F8 : printf_piecesx (str "%*s" ++ [0]) [PA_i 0; PA_s []] = Some ([[]; []; []], 0).
Proof. vm_compute. reflexivity. Qed.
Example ep10_F15 : printf_piecesx (str "%*s%04x - " ++ [0]) [PA_i 0; PA_s []; PA_u 32] = Some ([[]; []; []; []; []; [48; 48]; [50; 48]; str " - "], 7).
Proof. vm_compute. reflexivity. Qed.
Example ep10_F16 : printf_piecesx (str "%02x%c" ++ [0]) [PA_u 171; PA_i 45] = Some ([[]; []; [97; 98]; []; []; [45]], 3).
Proof. vm_compute. reflexivity. Qed.
Example ep10_F14 : printf_piecesx (str "%019lu" ++ [0]) [PA_z 42] = Some ([[]; []; zrepeat 48 17; [52; 50]], 19).
Proof. vm_compute. reflexivity. Qed.
Example ep10_F7 : printf_piecesx (str "%-18s" ++ [0]) [PA_s (str "SEQUENCE")] = Some ([[]; []; str "SEQUENCE"; zrepeat 32 10], 18).
Proof. vm_compute. reflexivity. Qed.
Example ep10_F11 : printf_piecesx (str "%02X" ++ [0]) [PA_u 10] = Some ([[]; []; [48]; [65]], 2).
Proof. vm_compute. reflexivity. Qed.
Example ep10_Fstar_neg : printf_piecesx (str "%*d|" ++ [0]) [PA_i (-4); PA_i 7] = Some ([[]; []; [55]; [32; 32; 32]; str "|"], 5).
Proof. vm_compute. reflexivity. Qed.
Example ep10_pass1_F1 : pass1x_ok (str "%5ld:d=%-2d hl=%ld l=%4ld %s" ++ [0]) = true.
Proof. vm_compute. reflexivity. Qed.
Example ep10_pass1_F8 : pass1x_ok (str "%*s" ++ [0]) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Example ep16_C1 : printf_piecesx (str "%*sSigned Certificate Timestamp:" ++ [0]) [PA_i 4; PA_s []]
  = Some ([[]; zrepeat 32 4; []; []; str "Signed Certificate Timestamp:"], 33).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C2 : printf_piecesx ([10] ++ str "%*sVersion   : " ++ [0]) [PA_i 8; PA_s []]
  = Some ([[10]; []; zrepeat 32 8; []; []; str "Version   : "], 21).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C3 : printf_piecesx (str "unknown" ++ [10] ++ str "%*s" ++ [0]) [PA_i 20; PA_s []]
  = Some ([str "unknown" ++ [10]; []; zrepeat 32 20; []; []], 28).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C4 : printf_piecesx (str "v1 (0x0)" ++ [0]) [] = Some ([str "v1 (0x0)"], 8).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C8 : printf_piecesx (str "none" ++ [0]) [] = Some ([str "none"], 4).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C10a : printf_piecesx (str "%s" ++ [0]) [PA_s (str "ecdsa-with-SHA256")] = Some ([[]; []; str "ecdsa-with-SHA256"], 17).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C10b : printf_piecesx (str "%s" ++ [0]) [PA_s (str "sha256WithRSAEncryption")] = Some ([[]; []; str "sha256WithRSAEncryption"], 23).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C10c : printf_piecesx (str "%s" ++ [0]) [PA_s [10]] = Some ([[]; []; [10]], 1).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C11 : printf_piecesx ([10] ++ str "%*s            " ++ [0]) [PA_i 8; PA_s []]
  = Some ([[10]; []; zrepeat 32 8; []; []; zrepeat 32 12], 21).
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ep16_C12_w0 : printf_piecesx (str "%*s" ++ [0]) [PA_i 0; PA_s []] = Some ([[]; []; []], 0).
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ep16_C12 : printf_piecesx (str "%*s" ++ [0]) [PA_i 20; PA_s []] = Some ([[]; zrepeat 32 20; []; []], 20).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C13 : printf_piecesx (str "%02X:" ++ [0]) [PA_u 171] = Some ([[]; []; [65; 66]; str ":"], 3).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C13z : printf_piecesx (str "%02X:" ++ [0]) [PA_u 0] = Some ([[]; []; [48]; [48]; []; str ":"], 3).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C13s : printf_piecesx (str "%02X:" ++ [0]) [PA_u 7] = Some ([[]; []; [48]; [55]; str ":"], 3).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C14 : printf_piecesx ([10; 0]) [] = Some ([[10]], 1).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C15 : printf_piecesx (str "%02X" ++ [0]) [PA_u 255] = Some ([[]; []; [70; 70]], 2).
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ep16_C16 : printf_piecesx (str "%s %2d %02d:%02d:%02d.%.*s %d GMT" ++ [0])
    [PA_s (str "Jan"); PA_i 1; PA_i 0; PA_i 0; PA_i 7; PA_i 3; PA_s (str "123Z"); PA_i 1970]
  = Some ([[]; []; str "Jan"; str " "; []; [32]; []; [49]; str " "; []; []; [48]; [48]; []; str ":"; []; []; [48]; [48]; []; str ":"; []; []; [48]; [55];
           str "."; []; []; str "123"; str " "; []; []; str "1970"; str " GMT"], 28).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C16b : printf_piecesx (str "%s %2d %02d:%02d:%02d.%.*s %d GMT" ++ [0])
    [PA_s (str "Dec"); PA_i 31; PA_i 23; PA_i 59; PA_i 59; PA_i 3; PA_s (str "999Z"); PA_i 9999]
  = Some ([[]; []; str "Dec"; str " "; []; []; str "31"; str " "; []; []; str "23"; str ":"; []; []; str "59"; str ":"; []; []; str "59";
           str "."; []; []; str "999"; str " "; []; []; str "9999"; str " GMT"], 28).
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ep16_pstar_trunc : printf_piecesx (str "%.*s|" ++ [0]) [PA_i 2; PA_s (str "123Z")] = Some ([[]; []; str "12"; str "|"], 3).
Proof. vm_compute. reflexivity. Qed.
Example ep16_pstar_long : printf_piecesx (str "%.*s|" ++ [0]) [PA_i 9; PA_s (str "123Z")] = Some ([[]; []; str "123Z"; str "|"], 5).
Proof. vm_compute. reflexivity. Qed.
Example ep16_pstar_zero : printf_piecesx (str "%.*s|" ++ [0]) [PA_i 0; PA_s (str "123Z")] = Some ([[]; []; []; str "|"], 1).
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ep16_pstar_d : printf_piecesx (str "%.*d|" ++ [0]) [PA_i 3; PA_i 7] = Some ([[]; []; [48; 48]; [55]; str "|"], 4).
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ep16_wstar_pstar : printf_piecesx (str "%*.*s|" ++ [0]) [PA_i 6; PA_i 2; PA_s (str "123Z")] = Some ([[]; zrepeat 32 4; []; str "12"; str "|"], 7).
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ep16_pstar_neg : printf_piecesx (str "%.*s|" ++ [0]) [PA_i (-1); PA_s (str "123Z")] = None.
Proof. vm_compute. reflexivity. Qed.
Example ep16_pstar_digit : printf_piecesx (str "%.*1s|" ++ [0]) [PA_i 1; PA_s (str "123Z")] = None.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ep16_C17 : printf_piecesx (str "%04d%02d%02d%02d%02d%02dZ" ++ [0]) [PA_i 1970; PA_i 1; PA_i 1; PA_i 0; PA_i 0; PA_i 0]
  = Some ([[]; []; str "1970"; []; []; [48]; [49]; []; []; [48]; [49]; []; []; [48]; [48]; []; []; []; [48]; [48]; []; []; []; [48]; [48]; []; str "Z"], 15).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C17b : printf_piecesx (str "%04d%02d%02d%02d%02d%02dZ" ++ [0]) [PA_i 33; PA_i 12; PA_i 31; PA_i 23; PA_i 59; PA_i 59]
  = Some ([[]; []; [48; 48]; str "33"; []; []; str "12"; []; []; str "31"; []; []; str "23"; []; []; str "59"; []; []; str "59"; str "Z"], 15).
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ep16_C18 : printf_piecesx (str "%.14s.%03dZ" ++ [0]) [PA_s (str "20261003235959Z"); PA_i 7]
  = Some ([[]; []; str "20261003235959"; str "."; []; []; [48; 48]; [55]; str "Z"], 19).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C18b : printf_piecesx (str "%.14s.%03dZ" ++ [0]) [PA_s (str "20261003235959.123Z"); PA_i 999]
  = Some ([[]; []; str "20261003235959"; str "."; []; []; str "999"; str "Z"], 19).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C18null : printf_piecesx (str "%.14s.%03dZ" ++ [0]) [PA_sn; PA_i 42]
  = Some ([[]; []; str "(null)"; str "."; []; []; [48]; str "42"; str "Z"], 11).
Proof. vm_compute. reflexivity. Qed.
Example ep16_C18null0 : printf_piecesx (str "%.14s.%03dZ" ++ [0]) [PA_sn; PA_i 0]
  = Some ([[]; []; str "(null)"; str "."; []; []; [48; 48]; [48]; []; str "Z"], 11).
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ep16_ints : printf_piecesx (str "%2d|%02d|%03d|%04d|%d" ++ [0]) [PA_i 7; PA_i 7; PA_i 7; PA_i 7; PA_i 7]
  = Some ([[]; [32]; []; [55]; str "|"; []; []; [48]; [55]; str "|"; []; []; [48; 48]; [55]; str "|"; []; []; [48; 48; 48]; [55]; str "|"; []; []; [55]], 16).
Proof. vm_compute. reflexivity. Qed.
Example ep16_pass1_C16 : pass1x_ok (str "%s %2d %02d:%02d:%02d.%.*s %d GMT" ++ [0]) = true.
Proof. vm_compute. reflexivity. Qed.
Example ep16_pass1_C18 : pass1x_ok (str "%.14s.%03dZ" ++ [0]) = true.
Proof. vm_compute. reflexivity. Qed.
Example ep16_parse_pstar : parse_dirx (str ".*s %d GMT" ++ [0]) = Some (mkDir 0 0 0 true 115 T_PTR, (false, true), str " %d GMT" ++ [0]).
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Example ep16_covs_C16 : arg_covs 40 (str "%s %2d %02d:%02d:%02d.%.*s %d GMT" ++ [0])
    [PA_s (str "Jan"); PA_i 1; PA_i 0; PA_i 0; PA_i 7; PA_i 3; PA_s (str "123Z"); PA_i 1970]
  = [None; None; None; None; None; None; Some 3; None].
Proof. vm_compute. reflexivity. Qed.
Example ep16_covs_C18 : arg_covs 20 (str "%.14s.%03dZ" ++ [0]) [PA_s (str "20261003235959Z"); PA_i 7] = [Some 14; None].
Proof. vm_compute. reflexivity. Qed.
