(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac.
From Ltac2 Require Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sf_hide (P : Prop) := P.

Module SF2.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 rec plain_arith_o (neg : bool) (t : constr) : bool :=
    lazy_match! t with
    | Z.le _ _ => true | Z.lt _ _ => true | Z.ge _ _ => true | Z.gt _ _ => true
    | @eq _ _ _ => true
    | le _ _ => true | lt _ _ => true | ge _ _ => true | gt _ _ => true
    | N.le _ _ => true | N.lt _ _ => true | Z.divide _ _ => true
    | ?a /\ ?b => Bool.and (plain_arith_o neg a) (plain_arith_o neg b)
    | True => true | False => true
    | not ?a => Bool.and neg (plain_arith_o false a)
    | ?a -> False => Bool.and neg (plain_arith_o false a)
    | _ => false
    end.
  (* [comment removed for export] *)
  Ltac2 rec arith_logic_o (t : constr) : bool :=
    lazy_match! t with
    | ?a /\ ?b => Bool.and (arith_logic_o a) (arith_logic_o b)
    | ?a \/ ?b => Bool.and (arith_logic_o a) (arith_logic_o b)
    | ?a <-> ?b => Bool.and (arith_logic_o a) (arith_logic_o b)
    | not ?a => arith_logic_o a
    | ?a -> ?b => Bool.and (arith_logic_o a) (arith_logic_o b)
    | _ => plain_arith_o false t
    end.
  (* [comment removed for export] *)
  Ltac2 Type exn ::= [ SF2_Unknown ].
  Ltac2 unk () := Control.zero SF2_Unknown.
  Ltac2 isk (r : Std.reference) (k : constant) : bool := match r with Std.ConstRef k' => Constant.equal k k' | _ => false end.
  Ltac2 isi (r : Std.reference) (i : inductive) : bool := match r with Std.IndRef i' => Ind.equal i i' | _ => false end.
  Ltac2 is_False (c : constr) : bool :=
    match Constr.Unsafe.kind c with Constr.Unsafe.Ind i _ => isi reference:(False) i | _ => false end.
  Ltac2 rec fplain (neg : bool) (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f args =>
        let n := Array.length args in
        (match Constr.Unsafe.kind f with
         | Constr.Unsafe.Constant k _ =>
             if Int.equal n 2 then
               (if isk reference:(Z.le) k then true else if isk reference:(Z.lt) k then true
                else if isk reference:(Z.ge) k then true else if isk reference:(Z.gt) k then true
                else if isk reference:(lt) k then true else if isk reference:(ge) k then true
                else if isk reference:(gt) k then true else if isk reference:(N.le) k then true
                else if isk reference:(N.lt) k then true else if isk reference:(Z.divide) k then true
                else false)
             else if Int.equal n 1 then
               (if isk reference:(not) k then Bool.and neg (fplain false (Array.get args 0)) else false)
             else false
         | Constr.Unsafe.Ind i _ =>
             if Int.equal n 3 then isi reference:(eq) i
             else if Int.equal n 2 then
               (if isi reference:(le) i then true
                else if isi reference:(and) i then Bool.and (fplain neg (Array.get args 0)) (fplain neg (Array.get args 1))
                else false)
             else false
         | Constr.Unsafe.App _ _ => unk ()
         | Constr.Unsafe.Cast _ _ _ => unk ()
         | Constr.Unsafe.Evar _ _ => unk ()
         | _ => false
         end)
    | Constr.Unsafe.Ind i _ => if isi reference:(True) i then true else isi reference:(False) i
    | Constr.Unsafe.Prod b body => if is_False body then Bool.and neg (fplain false (Constr.Binder.type b)) else false
    | Constr.Unsafe.Cast _ _ _ => unk ()
    | Constr.Unsafe.Evar _ _ => unk ()
    | _ => false
    end.
  Ltac2 rec farith (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f args =>
        let n := Array.length args in
        (match Constr.Unsafe.kind f with
         | Constr.Unsafe.Ind i _ =>
             if Int.equal n 2 then
               (if isi reference:(and) i then Bool.and (farith (Array.get args 0)) (farith (Array.get args 1))
                else if isi reference:(or) i then Bool.and (farith (Array.get args 0)) (farith (Array.get args 1))
                else fplain false t)
             else fplain false t
         | Constr.Unsafe.Constant k _ =>
             if Int.equal n 2 then
               (if isk reference:(iff) k then Bool.and (farith (Array.get args 0)) (farith (Array.get args 1))
                else fplain false t)
             else if Int.equal n 1 then
               (if isk reference:(not) k then farith (Array.get args 0) else fplain false t)
             else fplain false t
         | _ => fplain false t
         end)
    | Constr.Unsafe.Prod b body =>
        if Constr.Unsafe.noccurn 1 body then Bool.and (farith (Constr.Binder.type b)) (farith body) else fplain false t
    | _ => fplain false t
    end.
  Ltac2 plain_arith (neg : bool) (t : constr) : bool :=
    match Control.case (fun () => fplain neg t) with Val (b, _) => b | Err _ => plain_arith_o neg t end.
  Ltac2 arith_logic (t : constr) : bool :=
    match Control.case (fun () => farith t) with Val (b, _) => b | Err _ => arith_logic_o t end.
  (* [comment removed for export] *)
  Ltac2 rec vars_of (acc : ident list) (c : constr) : ident list :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Var id => id :: acc
    | Constr.Unsafe.App f args => Array.fold_left vars_of (vars_of acc f) args
    | Constr.Unsafe.Prod b body => vars_of (vars_of acc (Constr.Binder.type b)) body
    | Constr.Unsafe.Lambda b body => vars_of (vars_of acc (Constr.Binder.type b)) body
    | Constr.Unsafe.LetIn b v body => vars_of (vars_of (vars_of acc (Constr.Binder.type b)) v) body
    | Constr.Unsafe.Cast c _ _ => vars_of acc c
    | _ => acc
    end.
  Ltac2 rec meets (xs : ident list) (ys : ident list) : bool :=
    match xs with
    | [] => false
    | x :: xs' => if List.exist (Ident.equal x) ys then true else meets xs' ys
    end.
  (* [comment removed for export] *)
  Ltac2 bad_heads () : constr list :=
    [constr:(Z.to_nat); constr:(Z.min); constr:(Z.max); constr:(Z.abs); constr:(Nat.sub); constr:(Nat.min);
     constr:(Nat.max); constr:(Z.div); constr:(Z.modulo); constr:(Z.quot); constr:(Z.rem); constr:(Nat.div);
     constr:(Nat.modulo); constr:(Z.pow_pos); constr:(Z.sgn)].
  Ltac2 rec clean_o (bad : constr list) (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args =>
        if List.exist (Constr.equal f) bad then false
        else if clean_o bad f then Array.fold_left (fun b a => if b then clean_o bad a else false) true args else false
    | Constr.Unsafe.Constant _ _ => if List.exist (Constr.equal c) bad then false else true
    | Constr.Unsafe.Prod b body => if clean_o bad (Constr.Binder.type b) then clean_o bad body else false
    | Constr.Unsafe.Lambda _ _ => false
    | Constr.Unsafe.Case _ _ _ _ _ => false
    | Constr.Unsafe.LetIn _ _ _ => false
    | _ => true
    end.
  (* [comment removed for export] *)
  Ltac2 rec sf_cchain (c : constr) : constr :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 1 then
          (match Constr.Unsafe.kind f with Constr.Unsafe.Constructor _ _ => sf_cchain (Array.get args 0) | _ => c end)
        else c
    | _ => c
    end.
  Ltac2 rec sclean (bad : constant FSet.t) (c0 : constr) : bool :=
    let c := sf_cchain c0 in
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args =>
        (match Constr.Unsafe.kind f with
         | Constr.Unsafe.Constant k _ => if FSet.mem k bad then false else Array.for_all (sclean bad) args
         | _ => if sclean bad f then Array.for_all (sclean bad) args else false
         end)
    | Constr.Unsafe.Constant k _ => if FSet.mem k bad then false else true
    | Constr.Unsafe.Prod b body => if sclean bad (Constr.Binder.type b) then sclean bad body else false
    | Constr.Unsafe.Lambda _ _ => false
    | Constr.Unsafe.Case _ _ _ _ _ => false
    | Constr.Unsafe.LetIn _ _ _ => false
    | _ => true
    end.
  Ltac2 bad_set (bad : constr list) : constant FSet.t option :=
    List.fold_left (fun acc b => match acc with
                                 | None => None
                                 | Some s => (match Constr.Unsafe.kind b with
                                              | Constr.Unsafe.Constant k _ => Some (FSet.add k s)
                                              | _ => None
                                              end)
                                 end) (Some (FSet.empty FSet.Tags.constant_tag)) bad.
  Ltac2 clean (bad : constr list) (c : constr) : bool :=
    match bad_set bad with Some s => sclean s c | None => clean_o bad c end.
  (* [comment removed for export] *)
  Ltac2 prune_with (keep : constr -> bool) : unit :=
    let hs := Control.hyps () in
    let ids := List.map_filter (fun h => let (id, body, ty) := h in
                  match body with
                  | Some _ => None
                  | None => if arith_logic ty then (if keep ty then None else Some id) else None
                  end) hs in
    match ids with [] => () | _ :: _ => Std.clear ids end.
  (* [comment removed for export] *)
  Ltac2 prune_plain () : unit := prune_with (fun ty => plain_arith false ty).
  (* [comment removed for export] *)
  Ltac2 prune_clean () : unit :=
    let bad := bad_heads () in prune_with (fun ty => if plain_arith false ty then clean bad ty else false).
  (* [comment removed for export] *)
  Ltac2 prune_rel () : unit :=
    let bad := bad_heads () in
    let gv := vars_of [] (Control.goal ()) in
    prune_with (fun ty => if plain_arith false ty then clean bad ty
                          else if plain_arith true ty then (if meets (vars_of [] ty) gv then clean bad ty else false)
                          else false).
  Ltac2 prune_plain1 () : unit := Control.enter prune_plain.
  Ltac2 prune_clean1 () : unit := Control.enter prune_clean.
  Ltac2 prune_neg () : unit := Control.enter prune_rel.
  Ltac zify_prune_plain := ltac2:(prune_plain1 ()).
  Ltac zify_prune_clean := ltac2:(prune_clean1 ()).
  Ltac zify_prune_neg := ltac2:(prune_neg ()).
  (* [comment removed for export] *)
  Ltac2 hide_poison () : unit :=
    let bad := bad_heads () in
    List.iter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => ()
      | None =>
          if arith_logic ty then
            (if (if plain_arith false ty then clean bad ty else false) then ()
             else let c := Control.hyp id in
                  ltac1:(c |- lazymatch type of c with ?T => change T with (sf_hide T) in c end) (Ltac1.of_constr c))
          else ()
      end) (Control.hyps ()).
  Ltac2 hide_poison1 () : unit := Control.enter hide_poison.
  Ltac sf_hide_poison := ltac2:(hide_poison1 ()).
End SF2.
Ltac zify_prune_neg := SF2.zify_prune_neg.
Ltac sf_hide_poison := SF2.sf_hide_poison.
(* [comment removed for export] *)
Module SF6.
  Import Ltac2.
  Ltac2 unhide () : unit :=
    let ids := List.map_filter (fun hy => let (id, _, ty) := hy in
        match Constr.Unsafe.kind ty with
        | Constr.Unsafe.App f args =>
            if Int.equal (Array.length args) 1 then
              (match Constr.Unsafe.kind f with
               | Constr.Unsafe.Constant k _ => (match reference:(sf_hide) with Std.ConstRef k' => if Constant.equal k k' then Some id else None | _ => None end)
               | _ => None
               end)
            else None
        | _ => None
        end) (Control.hyps ()) in
    match ids with
    | [] => ()
    | _ :: _ => Std.unfold [(reference:(sf_hide), Std.AllOccurrences)]
                  { Std.on_hyps := Some (List.map (fun id => (id, Std.AllOccurrences, Std.InHyp)) ids); Std.on_concl := Std.NoOccurrences }
    end.
  Ltac2 unhide1 () : unit := Control.enter unhide.
End SF6.
Ltac sf_unhide := ltac2:(SF6.unhide1 ()); repeat match goal with H : sf_hide _ |- _ => unfold sf_hide in H end.
Ltac zify_prune_plain := SF2.zify_prune_plain.
Ltac zify_prune_clean := SF2.zify_prune_clean.
Ltac lia3 := first [ zify_prune_plain; Zify.zify; xlia zchecker
                   | zify_prune_neg; Zify.zify; xlia zchecker
                   | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Module SF5.
  Import Ltac2.
  Ltac2 big_heads () : constant list :=
    List.map_filter (fun r => match r with Std.ConstRef k => Some k | _ => None end)
      [reference:(rw_cells); reference:(ro_cells); reference:(bytes_at); reference:(u8arr); reference:(u32arr);
       reference:(u64arr); reference:(u8ro); reference:(stk); reference:(munch); reference:(wmono); reference:(mem_inv)].
  Ltac2 clear_big () : unit :=
    let bs := big_heads () in
    let ids := List.map_filter (fun hy => let (id, body, ty) := hy in
        match body with
        | Some _ => None
        | None =>
            match Constr.Unsafe.kind ty with
            | Constr.Unsafe.App f _ =>
                (match Constr.Unsafe.kind f with
                 | Constr.Unsafe.Constant k _ => if List.exist (Constant.equal k) bs then Some id else None
                 | _ => None
                 end)
            | _ => None
            end
        end) (Control.hyps ()) in
    match ids with
    | [] => ()
    | _ :: _ =>
        match Control.case (fun () => Std.clear ids) with
        | Val _ => ()
        | Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with _ => () end) ids
        end
    end.
  Ltac2 clear_big1 () : unit := Control.enter clear_big.
End SF5.
Ltac sf_clear_big := ltac2:(SF5.clear_big1 ()).
Ltac tlia := sf_clear_big;
             first [ Zify.zify; xlia zchecker
                   | sf_unhide;
                     first [ zify_prune_neg; Zify.zify; xlia zchecker
                           | zify_prune_plain; Zify.zify; xlia zchecker
                           | Zify.zify; xlia zchecker ] ].
Ltac tslia := first [ exact I | tlia | split; [ tlia | exact I ] ].

Section WithSegs.
Variable segs : list Segment.

Lemma bytes_at_write_other_n : forall m a bs c cs (n : Z),
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  bytes_at segs m c cs ->
  (c + Z.of_nat (length cs) <= a \/ a + n <= c)%Z ->
  bytes_at segs (write_to_mem m (wa a) bs) c cs.
Proof. intros m a bs c cs n <- Ha Hl H Hd. apply bytes_at_write_other; assumption. Qed.

Lemma rw_cells_frame_n : forall m A cs (a : Z) bs (n : Z),
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  rw_cells segs m A cs ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z ->
  rw_cells segs (write_to_mem m (wa a) bs) A cs.
Proof. intros m A cs a bs n <- Ha Hl H Hd. apply rw_cells_frame; assumption. Qed.

Lemma ro_cells_frame_n : forall m A cs (a : Z) bs (n : Z),
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  ro_cells segs m A cs ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z ->
  ro_cells segs (write_to_mem m (wa a) bs) A cs.
Proof. intros m A cs a bs n <- Ha Hl H Hd. apply ro_cells_frame; assumption. Qed.

Lemma u8arr_frame_n : forall m A bs a xs (n : Z),
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u8arr segs m A bs ->
  (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z ->
  u8arr segs (write_to_mem m (wa a) xs) A bs.
Proof. intros m A bs a xs n <- Ha Hl H Hd. apply u8arr_frame; assumption. Qed.

Lemma u32arr_frame_n : forall m A ws a xs (n : Z),
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u32arr segs m A ws ->
  (A + 4 * Z.of_nat (length ws) <= a \/ a + n <= A)%Z ->
  u32arr segs (write_to_mem m (wa a) xs) A ws.
Proof. intros m A ws a xs n <- Ha Hl H Hd. apply u32arr_frame; assumption. Qed.

Lemma u64arr_frame_n : forall m A ws a xs (n : Z),
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u64arr segs m A ws ->
  (A + 8 * Z.of_nat (length ws) <= a \/ a + n <= A)%Z ->
  u64arr segs (write_to_mem m (wa a) xs) A ws.
Proof. intros m A ws a xs n <- Ha Hl H Hd. apply u64arr_frame; assumption. Qed.

Lemma u8ro_frame_n : forall m A bs a xs (n : Z),
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u8ro segs m A bs ->
  (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z ->
  u8ro segs (write_to_mem m (wa a) xs) A bs.
Proof. intros m A bs a xs n <- Ha Hl H Hd. apply u8ro_frame; assumption. Qed.

Lemma stk_write_n : forall m lo hi a bs (n : Z),
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  stk segs m lo hi -> stk segs (write_to_mem m (wa a) bs) lo hi.
Proof. intros m lo hi a bs n <- Ha Hl H. apply stk_write; assumption. Qed.

End WithSegs.

Lemma munch_write_n : forall W m0 m a bs (n : Z),
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  munch W m0 m -> inside W a n ->
  munch W m0 (write_to_mem m (wa a) bs).
Proof. intros W m0 m a bs n <- Ha Hl H Hin. apply munch_write; assumption. Qed.

(* [comment removed for export] *)
Ltac is_natlit n := lazymatch n with O => idtac | S ?k => is_natlit k end.
Ltac cells_spine_closed cs :=
  lazymatch cs with
  | nil => idtac
  | cons ?c ?tl =>
      lazymatch c with C8 _ => idtac | C4 _ => idtac | C2 _ => idtac | C1 _ => idtac | CB ?n _ => is_natlit n end;
      cells_spine_closed tl
  end.
(* [comment removed for export] *)
Ltac literal_cell_sizes :=
  repeat match goal with
  | |- context [cells_size ?cs] =>
      cells_spine_closed cs;
      let n := eval cbv [cells_size csize Nat.add] in (cells_size cs) in
      change (cells_size cs) with n
  end.
Ltac literal_cell_sizes_in H :=
  repeat match type of H with
  | context [cells_size ?cs] =>
      cells_spine_closed cs;
      let n := eval cbv [cells_size csize Nat.add] in (cells_size cs) in
      change (cells_size cs) with n in H
  end.

(* [comment removed for export] *)
Ltac simpl_sizes_goal :=
  literal_cell_sizes;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  try match goal with |- context [length (le8 _)] => rewrite !length_le8 end;
  try match goal with |- context [length (le4 _)] => rewrite !length_le4 end;
  try match goal with |- context [length (le2 _)] => rewrite !length_le2 end;
  try match goal with |- context [length (le1 _)] => rewrite !length_le1 end;
  try match goal with |- context [length (u32s _)] => rewrite !u32s_length end;
  try match goal with |- context [length (u64s _)] => rewrite !u64s_length end;
  try match goal with |- context [length (upd _ _ _)] => rewrite !upd_length end.

(* [comment removed for export] *)
Ltac store_facts a bs k :=
  let Hn := fresh "Hn_st" in let Ha := fresh "Ha_st" in let Hl := fresh "Hl_st" in
  let n0 := constr:(Z.of_nat (@length byte bs)) in
  let n1 := eval cbv [length app cbytes cells_bytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes
                      Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in n0 in
  let n := lazymatch n1 with Zpos _ => n1 | Z0 => n1 | _ => n0 end in
  first [ assert (Hn : Z.of_nat (@length byte bs) = n) by exact eq_refl
        | fail "store_facts: length of" bs "vs" n ];
  sf_hide_poison;
  first [ assert (Ha : (0 <= a)%Z) by tlia | sf_unhide; fail "store_facts: 0 <=" a ];
  first [ assert (Hl : (a + n <= 2^64)%Z)
            by first [ tlia | rewrite <- Hn; simpl_sizes; rewrite ?u32s_length, ?u64s_length, ?upd_length; tlia ]
        | sf_unhide; fail "store_facts:" a "+" n "<= 2^64" ];
  k n Hn Ha Hl;
  clear Hn Ha Hl; sf_unhide.

(* [comment removed for export] *)
Ltac transport_chunks_extra m a bs n Hn Ha Hl := idtac.
Ltac transport_call_extra segs W m m' MU WM := idtac.

(* [comment removed for export] *)


(* [comment removed for export] *)
Ltac disjoint_goal :=
  cbv [disjoint_from fst snd];
  simpl_sizes_goal;
  tslia.

Ltac transport_after_call_fast_orig segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  sf_hide_poison;
  (repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | disjoint_goal ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H;
              [ | eapply (munch_weaken W Wq m m');
                [ unfold sub_fp; cbn [outside];
                  (* [comment removed for export] *)
                  first [ intros; Zify.zify; xlia zchecker
                        | sf_unhide; zify_prune_plain; intros; Zify.zify; xlia zchecker
                        | intros; tslia ]
                | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end);
  transport_call_extra segs W m m' MU WM;
  sf_unhide.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zh_sep A sT A2 s2 k kfail :=
  lazymatch goal with
  | D : zsep A sT A2 s2 |- _ => k D
  | _ : znot (zsep A sT A2 s2) |- _ => kfail
  | _ => let D := fresh "zhD" in
         tryif assert (D : zsep A sT A2 s2) by (unfold zsep; simpl_sizes_goal; tslia)
         then (zh_settle D; k D)
         else (let N := fresh "zhN" in assert (N : znot (zsep A sT A2 s2)) by exact I; zh_settle N; kfail)
  end.

(* [comment removed for export] *)
Ltac zh_store1 K lem sz segs m a bs n Hn Ha Hl A sT kz H A2 p :=
  zh_worthy p;
  zh_get sz A2 p H ltac:(fun L S s =>
    change (K segs m A2 L) in H;
    zh_sep A sT A2 s
      ltac:(fun D =>
        first [ apply (lem segs m a bs n A2 L s Hn Ha Hl S) in H;
                [ change (K segs (write_to_mem m (wa a) bs) A2 p) in H; zh_trace_hit H
                | first [ exact (zsep_store A sT A2 s kz n D (@eq_refl bool true)) | simpl_sizes_goal; tslia ] ]
              | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
      ltac:(
        first [ apply (lem segs m a bs n A2 L s Hn Ha Hl S) in H;
                [ change (K segs (write_to_mem m (wa a) bs) A2 p) in H; zh_trace_hit H
                | simpl_sizes_goal; tslia ]
              | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])).

(* [comment removed for export] *)
Ltac zh_store1_plain K lem sz segs m a bs n Hn Ha Hl H A2 p :=
  zh_worthy p;
  zh_get sz A2 p H ltac:(fun L S s =>
    change (K segs m A2 L) in H;
    first [ apply (lem segs m a bs n A2 L s Hn Ha Hl S) in H;
            [ change (K segs (write_to_mem m (wa a) bs) A2 p) in H; zh_trace_hit H
            | simpl_sizes_goal; tslia ]
          | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]).

(* [comment removed for export] *)
Ltac zh_st K lem sz segs m a bs n Hn Ha Hl tgt H A2 p :=
  lazymatch tgt with
  | (?A, ?sT, ?kz) => zh_store1 K lem sz segs m a bs n Hn Ha Hl A sT kz H A2 p
  | tt => zh_store1_plain K lem sz segs m a bs n Hn Ha Hl H A2 p
  end.


Ltac transport_chunks_with segs m a bs n Hn Ha Hl :=
  let tgt := zh_tgt in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ zh_st bytes_at bytes_at_write_other_s zh_szB segs m a bs n Hn Ha Hl tgt H A2 bs2
            | apply (bytes_at_write_other_n segs m a bs A2 bs2 n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ zh_st rw_cells rw_cells_frame_s zh_szC segs m a bs n Hn Ha Hl tgt H A2 cs2
            | apply (rw_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ zh_st ro_cells ro_cells_frame_s zh_szC segs m a bs n Hn Ha Hl tgt H A2 cs2
            | apply (ro_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ zh_st u8arr u8arr_frame_s zh_szB segs m a bs n Hn Ha Hl tgt H A2 xs
            | apply (u8arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ zh_st u32arr u32arr_frame_s zh_sz4 segs m a bs n Hn Ha Hl tgt H A2 xs
            | apply (u32arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ zh_st u64arr u64arr_frame_s zh_sz8 segs m a bs n Hn Ha Hl tgt H A2 xs
            | apply (u64arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ zh_st u8ro u8ro_frame_s zh_szB segs m a bs n Hn Ha Hl tgt H A2 xs
            | apply (u8ro_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end;
  transport_chunks_extra m a bs n Hn Ha Hl.

(* [comment removed for export] *)
Ltac zh_ins Wq A sT k kfail :=
  lazymatch goal with
  | I : zins Wq A sT |- _ => k I
  | _ : znot (zins Wq A sT) |- _ => kfail
  | _ => let I := fresh "zhI" in
         tryif assert (I : zins Wq A sT) by (unfold zins; cbn [inside]; tslia)
         then (zh_settle I; k I)
         else (let N := fresh "zhN" in assert (N : znot (zins Wq A sT)) by exact I; zh_settle N; kfail)
  end.
(* [comment removed for export] *)
Ltac zh_munch_sc Wq mq m a bs Ha Hl MU :=
  store_ctx_of_facts false a bs Ha Hl ltac:(fail) ltac:(fun SC X b =>
      let D := wdesc_of X Wq in
      let n := size_lit constr:(Z.of_nat (@length byte bs)) in
      lazymatch eval vm_compute in (chk_inside D b n) with true => idtac end;
      let WDH := fresh "dWD" in
      assert (WDH : wds_ok X Wq D) by
        (cbv beta iota delta [wds_ok wd_ok opt_holds wd_l wd_h wd_lo wd_hi];
         repeat match goal with |- _ /\ _ => split end;
         first [ exact I | reflexivity | symmetry; apply Z.add_0_r ]);
      apply (munch_write_wd Wq mq m a bs X b D SC WDH) in MU; [ | exact (@eq_refl bool true) ];
      clear WDH).
Ltac footprint_after_store_with segs m a bs n Hn Ha Hl :=
  let tgt := zh_tgt in
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ lazymatch tgt with (?A, ?sT, ?kz) =>
                zh_ins Wq A sT
                  ltac:(fun I => apply (munch_write_n Wq mq m a bs n Hn Ha Hl) in MU;
                                 [ | exact (zins_store Wq A sT kz n I (@eq_refl bool true)) ])
                  ltac:(fail)
              end
            | zh_munch_sc Wq mq m a bs Ha Hl MU
            | apply (munch_write_n Wq mq m a bs n Hn Ha Hl) in MU; [ | cbn [inside]; tslia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write_n segs m loq hiq a bs n Hn Ha Hl) in STq
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* [comment removed for export] *)
Ltac transport_chunks_fast segs m a bs :=
  zh_gc;
  store_facts a bs ltac:(fun n Hn Ha Hl => transport_chunks_with segs m a bs n Hn Ha Hl).
Ltac footprint_after_store_fast segs m a bs :=
  store_facts a bs ltac:(fun n Hn Ha Hl => footprint_after_store_with segs m a bs n Hn Ha Hl).

(* [comment removed for export] *)
Ltac store_facts2 A kz HB a bs k :=
  let Hn := fresh "Hn_st" in let Ha := fresh "Ha_st" in let Hl := fresh "Hl_st" in
  let n0 := constr:(Z.of_nat (@length byte bs)) in
  let n1 := eval cbv [length app cbytes cells_bytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes
                      Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in n0 in
  let n := lazymatch n1 with Zpos _ => n1 | Z0 => n1 | _ => n0 end in
  first [ assert (Hn : Z.of_nat (@length byte bs) = n) by exact eq_refl
        | fail "store_facts: length of" bs "vs" n ];
  sf_hide_poison;
  first [ lazymatch type of HB with (0 <= A /\ A + ?sz <= 2 ^ 64)%Z =>
            pose proof (store_lb_of_bound A sz kz n HB (@eq_refl bool true) : (0 <= a)%Z) as Ha end
        | assert (Ha : (0 <= a)%Z) by tlia | sf_unhide; fail "store_facts: 0 <=" a ];
  first [ lazymatch type of HB with (0 <= A /\ A + ?sz <= 2 ^ 64)%Z =>
            pose proof (store_ub_of_bound A sz kz n HB (@eq_refl bool true) : (a + n <= 2^64)%Z) as Hl end
        | assert (Hl : (a + n <= 2^64)%Z)
            by first [ tlia | rewrite <- Hn; simpl_sizes; rewrite ?u32s_length, ?u64s_length, ?upd_length; tlia ]
        | sf_unhide; fail "store_facts:" a "+" n "<= 2^64" ];
  k n Hn Ha Hl;
  clear Hn Ha Hl; sf_unhide.

(* [comment removed for export] *)
Ltac mem_after_store_fast :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        zh_gc;
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          let kz := eval cbv in (Z.of_nat kn) in
          first
          [ (* [comment removed for export] *)
            zh_worthy cs;
            zh_get zh_szC A cs H ltac:(fun L S s =>
            zh_bound rw_cells_bound segs m rw_cells A cs L H ltac:(fun B sn =>
              pose proof (B : (0 <= A /\ A + Z.of_nat sn <= 2 ^ 64)%Z) as HB;
              change (rw_cells segs m A L) in H;
              try lazymatch goal with
              | HI : mem_inv segs m |- _ =>
                  apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
                  [ | exact I
                    | apply (rw_cells_store_ok segs m A L kn c0 _ H); [ exact (@eq_refl (option cell) (Some c0)) | reflexivity ] ]
              end;
              change bs with (cbytes c');
              let H' := fresh "CH" in
              pose proof (rw_cells_write segs m A L kn c0 c' H (@eq_refl (option cell) (Some c0)) (@eq_refl nat n) I) as H';
              clear H;
              let cs' := eval cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in (cell_upd cs kn c') in
              zh_succ A L constr:(cell_upd L kn c') s H' ltac:(fun L' S' =>
                change (rw_cells segs (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) A cs') in H';
                let T := fresh "zhT" in
                pose proof (I : ztgt A s kz) as T;
                store_facts2 A kz HB (A + Z.of_nat kn)%Z (cbytes c') ltac:(fun n' Hn Ha Hl =>
                  transport_chunks_with segs m (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl;
                  footprint_after_store_with segs m (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl);
                clear T;
                let m' := fresh "m" in
                gen_mem (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) m';
                clear HB; try clear m; try rename H' into H)))
          | (* [comment removed for export] *)
            pose proof (rw_cells_bound segs m A cs H) as HB; literal_cell_sizes_in HB; cbn [cells_size csize Nat.add] in HB;
            try lazymatch goal with
            | HI : mem_inv segs m |- _ =>
                apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
                [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
            end;
            change bs with (cbytes c');
            let H' := fresh "CH" in
            pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
            clear H;
            cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
            store_facts (A + Z.of_nat kn)%Z (cbytes c') ltac:(fun n' Hn Ha Hl =>
              transport_chunks_with segs m (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl;
              footprint_after_store_with segs m (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl);
            let m' := fresh "m" in
            gen_mem (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) m';
            clear HB; try clear m; try rename H' into H ]
        end
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zh_dis W A2 s2 k kfail :=
  lazymatch goal with
  | D : zdis W A2 s2 |- _ => k D
  | _ : znot (zdis W A2 s2) |- _ => kfail
  | _ => let D := fresh "zhW" in
         tryif assert (D : zdis W A2 s2) by (unfold zdis; disjoint_goal)
         then (zh_settle D; k D)
         else (let N := fresh "zhN" in assert (N : znot (zdis W A2 s2)) by exact I; zh_settle N; kfail)
  end.

Ltac zh_call1 K lem sz segs W m m' MU WM H A2 p :=
  zh_worthy p;
  zh_get sz A2 p H ltac:(fun L S s =>
    change (K segs m A2 L) in H;
    first [ zh_dis W A2 s
              ltac:(fun D => apply (lem segs W m m' A2 L s MU WM S) in H;
                             [ change (K segs m' A2 p) in H; zh_trace_hit H | exact D ])
              ltac:(fail)
          | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]).

Ltac transport_after_call_with segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ zh_call1 bytes_at bytes_at_transport_s zh_szB segs W m m' MU WM H A2 bs2
            | apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ zh_call1 rw_cells rw_cells_transport_s zh_szC segs W m m' MU WM H A2 cs2
            | apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ zh_call1 ro_cells ro_cells_transport_s zh_szC segs W m m' MU WM H A2 cs2
            | apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ zh_call1 u8arr u8arr_transport_s zh_szB segs W m m' MU WM H A2 xs
            | apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ zh_call1 u32arr u32arr_transport_s zh_sz4 segs W m m' MU WM H A2 xs
            | apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ zh_call1 u64arr u64arr_transport_s zh_sz8 segs W m m' MU WM H A2 xs
            | apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ zh_call1 u8ro u8ro_transport_s zh_szB segs W m m' MU WM H A2 xs
            | apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | disjoint_goal ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H;
              [ | eapply (munch_weaken W Wq m m');
                [ unfold sub_fp; cbn [outside];
                  first [ intros; Zify.zify; xlia zchecker
                        | sf_unhide; zify_prune_plain; intros; Zify.zify; xlia zchecker
                        | intros; tslia ]
                | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac transport_after_call_fast segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  zh_gc;
  sf_hide_poison;
  transport_after_call_with segs m m' MU WM;
  transport_call_extra segs W m m' MU WM;
  sf_unhide.
