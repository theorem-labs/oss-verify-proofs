(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMow. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoSL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqyb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qqyb.
From Ltac2 Require Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.

Definition sf_hide (P : Prop) := P.

Module SF2.
Import Ltac2.

Ltac2 rec plain_arith (neg : bool) (t : constr) : bool :=
lazy_match! t with
| Z.le _ _ => true | Z.lt _ _ => true | Z.ge _ _ => true | Z.gt _ _ => true
| @eq _ _ _ => true
| le _ _ => true | lt _ _ => true | ge _ _ => true | gt _ _ => true
| N.le _ _ => true | N.lt _ _ => true | Z.divide _ _ => true
| ?a /\ ?b => Bool.and (plain_arith neg a) (plain_arith neg b)
| True => true | False => true
| not ?a => Bool.and neg (plain_arith false a)
| ?a -> False => Bool.and neg (plain_arith false a)
| _ => false
end.

Ltac2 rec arith_logic (t : constr) : bool :=
lazy_match! t with
| ?a /\ ?b => Bool.and (arith_logic a) (arith_logic b)
| ?a \/ ?b => Bool.and (arith_logic a) (arith_logic b)
| ?a <-> ?b => Bool.and (arith_logic a) (arith_logic b)
| not ?a => arith_logic a
| ?a -> ?b => Bool.and (arith_logic a) (arith_logic b)
| _ => plain_arith false t
end.

Ltac2 Type sk := { s_zle : constr; s_zlt : constr; s_zge : constr; s_zgt : constr; s_eq : constr; s_le : constr; s_lt : constr;
s_ge : constr; s_gt : constr; s_nle : constr; s_nlt : constr; s_zdiv : constr; s_and : constr; s_or : constr;
s_iff : constr; s_not : constr; s_true : constr; s_false : constr }.
Ltac2 sk_mk () : sk := { s_zle := '@Z.le; s_zlt := '@Z.lt; s_zge := '@Z.ge; s_zgt := '@Z.gt; s_eq := '@eq; s_le := '@le; s_lt := '@lt;
s_ge := '@ge; s_gt := '@gt; s_nle := '@N.le; s_nlt := '@N.lt; s_zdiv := '@Z.divide; s_and := '@and; s_or := '@or;
s_iff := '@iff; s_not := '@not; s_true := 'True; s_false := 'False }.

Ltac2 rec plain_k (kk : sk) (neg : bool) (t : constr) : bool :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App h args =>
let n := Array.length args in
if Int.equal n 2 then
(if Constr.equal h (kk.(s_zle)) then true else if Constr.equal h (kk.(s_zlt)) then true
else if Constr.equal h (kk.(s_zge)) then true else if Constr.equal h (kk.(s_zgt)) then true
else if Constr.equal h (kk.(s_le)) then true else if Constr.equal h (kk.(s_lt)) then true
else if Constr.equal h (kk.(s_ge)) then true else if Constr.equal h (kk.(s_gt)) then true
else if Constr.equal h (kk.(s_nle)) then true else if Constr.equal h (kk.(s_nlt)) then true
else if Constr.equal h (kk.(s_zdiv)) then true
else if Constr.equal h (kk.(s_and)) then Bool.and (plain_k kk neg (Array.get args 0)) (plain_k kk neg (Array.get args 1))
else false)
else if Int.equal n 3 then Constr.equal h (kk.(s_eq))
else if Int.equal n 1 then (if Constr.equal h (kk.(s_not)) then Bool.and neg (plain_k kk false (Array.get args 0)) else false)
else false
| Constr.Unsafe.Ind _ _ => if Constr.equal t (kk.(s_true)) then true else Constr.equal t (kk.(s_false))
| Constr.Unsafe.Prod b body =>
if Constr.equal body (kk.(s_false)) then Bool.and neg (plain_k kk false (Constr.Binder.type b)) else false
| _ => false
end.

Ltac2 rec al_k (kk : sk) (t : constr) : bool :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App h args =>
let n := Array.length args in
if Int.equal n 2 then
(if Constr.equal h (kk.(s_and)) then Bool.and (al_k kk (Array.get args 0)) (al_k kk (Array.get args 1))
else if Constr.equal h (kk.(s_or)) then Bool.and (al_k kk (Array.get args 0)) (al_k kk (Array.get args 1))
else if Constr.equal h (kk.(s_iff)) then Bool.and (al_k kk (Array.get args 0)) (al_k kk (Array.get args 1))
else plain_k kk false t)
else if Int.equal n 1 then (if Constr.equal h (kk.(s_not)) then al_k kk (Array.get args 0) else plain_k kk false t)
else plain_k kk false t
| Constr.Unsafe.Prod b body =>
if Constr.Unsafe.noccurn 1 body then Bool.and (al_k kk (Constr.Binder.type b)) (al_k kk body) else plain_k kk false t
| _ => plain_k kk false t
end.

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

Ltac2 bad_heads () : constr list :=
[constr:(Z.to_nat); constr:(Z.min); constr:(Z.max); constr:(Z.abs); constr:(Nat.sub); constr:(Nat.min);
constr:(Nat.max); constr:(Z.div); constr:(Z.modulo); constr:(Z.quot); constr:(Z.rem); constr:(Nat.div);
constr:(Nat.modulo); constr:(Z.pow_pos); constr:(Z.sgn)].
Ltac2 rec clean (bad : constr list) (c : constr) : bool :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.App f args =>
if List.exist (Constr.equal f) bad then false
else if clean bad f then Array.fold_left (fun b a => if b then clean bad a else false) true args else false
| Constr.Unsafe.Constant _ _ => if List.exist (Constr.equal c) bad then false else true
| Constr.Unsafe.Prod b body => if clean bad (Constr.Binder.type b) then clean bad body else false
| Constr.Unsafe.Lambda _ _ => false
| Constr.Unsafe.Case _ _ _ _ _ => false
| Constr.Unsafe.LetIn _ _ _ => false
| _ => true
end.

Ltac2 prune_with (kk : sk) (keep : constr -> bool) : unit :=
let hs := Control.hyps () in
let ids := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None => if al_k kk ty then (if keep ty then None else Some id) else None
end) hs in
match ids with [] => () | _ :: _ => Std.clear ids end.

Ltac2 prune_plain () : unit := let kk := sk_mk () in prune_with kk (fun ty => plain_k kk false ty).

Ltac2 prune_clean () : unit :=
let bad := bad_heads () in let kk := sk_mk () in prune_with kk (fun ty => if plain_k kk false ty then clean bad ty else false).

Ltac2 prune_rel () : unit :=
let bad := bad_heads () in let kk := sk_mk () in
let gv := vars_of [] (Control.goal ()) in
prune_with kk (fun ty => if plain_k kk false ty then clean bad ty
else if plain_k kk true ty then (if meets (vars_of [] ty) gv then clean bad ty else false)
else false).
Ltac2 prune_plain1 () : unit := Control.enter prune_plain.
Ltac2 prune_clean1 () : unit := Control.enter prune_clean.
Ltac2 prune_neg () : unit := Control.enter prune_rel.
Ltac zify_prune_plain := ltac2:(prune_plain1 ()).
Ltac zify_prune_clean := ltac2:(prune_clean1 ()).
Ltac zify_prune_neg := ltac2:(prune_neg ()).

Ltac2 hide_poison () : unit :=
let bad := bad_heads () in let kk := sk_mk () in
List.iter (fun h => let (id, body, ty) := h in
match body with
| Some _ => ()
| None =>
if al_k kk ty then
(if (if plain_k kk false ty then clean bad ty else false) then ()
else let c := Control.hyp id in
ltac1:(c |- lazymatch type of c with ?T => change T with (sf_hide T) in c end) (Ltac1.of_constr c))
else ()
end) (Control.hyps ()).
Ltac2 hide_poison1 () : unit := Control.enter hide_poison.
Ltac sf_hide_poison := ltac2:(hide_poison1 ()).

Ltac2 unhide_rel () : unit :=
let gv := vars_of [] (Control.goal ()) in
let sfh := '@sf_hide in
List.iter (fun h => let (id, body, ty) := h in
match body with
| Some _ => ()
| None =>
match Constr.Unsafe.kind ty with
| Constr.Unsafe.App f args =>
if Constr.equal f sfh then
(if meets (vars_of [] (Array.get args 0)) gv then
let c := Control.hyp id in
ltac1:(c |- unfold sf_hide in c) (Ltac1.of_constr c)
else ())
else ()
| _ => ()
end
end) (Control.hyps ()).
Ltac2 unhide_rel1 () : unit := Control.enter unhide_rel.
Ltac sf_unhide_rel := ltac2:(unhide_rel1 ()).
End SF2.
Ltac zify_prune_neg := SF2.zify_prune_neg.
Ltac sf_hide_poison := SF2.sf_hide_poison. Ltac mkr__sf_hide_poison_0 := SF2.sf_hide_poison.
Ltac sf_unhide := repeat match goal with H : sf_hide _ |- _ => unfold sf_hide in H end.
Ltac zify_prune_plain := SF2.zify_prune_plain.
Ltac zify_prune_clean := SF2.zify_prune_clean.
Ltac lia3 := first [ Qo9G.term_slim ltac:(zify_prune_plain; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune_neg; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Ltac sf_unhide_rel := SF2.sf_unhide_rel.
Ltac tlia := first [ Qo9G.term_slim ltac:(Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(sf_unhide_rel; Zify.zify; xlia zchecker)
| sf_unhide;
first [ Qo9G.term_slim ltac:(zify_prune_neg; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ] ].
Ltac tslia := first [ exact I | tlia | split; [ tlia | exact I ] ]. Ltac mkr__tslia_1 := first [ exact I | tlia | split; [ tlia | exact I ] ].

Ltac tlia_nofat := first [ Qo9G.term_slim ltac:(Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(sf_unhide_rel; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(sf_unhide; zify_prune_neg; Zify.zify; xlia zchecker) ].
Ltac tslia_nofat := first [ exact I | tlia_nofat | split; [ tlia_nofat | exact I ] ].
Ltac transport_lia := tslia. Ltac mkr__transport_lia_2 := tslia.

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

Ltac is_natlit n := lazymatch n with O => idtac | S ?k => is_natlit k end.
Ltac cells_spine_closed cs :=
lazymatch cs with
| nil => idtac
| cons ?c ?tl =>
lazymatch c with C8 _ => idtac | C4 _ => idtac | C2 _ => idtac | C1 _ => idtac | CB ?n _ => is_natlit n end;
cells_spine_closed tl
end.

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

Ltac store_facts_hb HB a bs k :=
let Hn := fresh "Hn_st" in let Ha := fresh "Ha_st" in let Hl := fresh "Hl_st" in
let n0 := constr:(Z.of_nat (@length byte bs)) in
let n1 := eval cbv [length app cbytes cells_bytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes
Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in n0 in
let n := lazymatch n1 with Zpos _ => n1 | Z0 => n1 | _ => n0 end in
first [ assert (Hn : Z.of_nat (@length byte bs) = n) by exact eq_refl
| fail "store_facts: length of" bs "vs" n ];
first [ assert (Ha : (0 <= a)%Z) by (clear - HB; lia)
| sf_hide_poison; first [ assert (Ha : (0 <= a)%Z) by tlia | sf_unhide; fail "store_facts: 0 <=" a ]; sf_unhide ];
first [ assert (Hl : (a + n <= 2^64)%Z) by (clear - HB; lia)
| sf_hide_poison;
first [ assert (Hl : (a + n <= 2^64)%Z)
by first [ tlia | rewrite <- Hn; simpl_sizes; rewrite ?u32s_length, ?u64s_length, ?upd_length; tlia ]
| sf_unhide; fail "store_facts:" a "+" n "<= 2^64" ]; sf_unhide ];
sf_hide_poison;
k n Hn Ha Hl;
clear Hn Ha Hl; sf_unhide.

Ltac transport_chunks_extra m a bs n Hn Ha Hl := idtac.
Ltac transport_call_extra segs W m m' MU WM := idtac.

Ltac transport_chunks_with segs m a bs n Hn Ha Hl :=
(repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_write_other_n segs m a bs A2 bs2 n Hn Ha Hl) in H; [ | simpl_sizes_goal; transport_lia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; transport_lia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; transport_lia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ apply (u8arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; transport_lia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u32arr segs m ?A2 ?xs |- _ =>
first [ apply (u32arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; transport_lia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u64arr segs m ?A2 ?xs |- _ =>
first [ apply (u64arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; transport_lia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ apply (u8ro_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; transport_lia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
end);
transport_chunks_extra m a bs n Hn Ha Hl.

Ltac footprint_after_store_with segs m a bs n Hn Ha Hl :=
repeat match goal with
| MU : munch ?Wq ?mq m |- _ =>
first [ apply (munch_write_n Wq mq m a bs n Hn Ha Hl) in MU; [ | cbn [inside]; transport_lia ]
| fail 100 "store outside the declared footprint:" a ]
| WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
| STq : stk segs m ?loq ?hiq |- _ =>
first [ apply (stk_write_n segs m loq hiq a bs n Hn Ha Hl) in STq
| fail 100 "cannot transport stk hypothesis" STq ]
end.

Ltac transport_chunks_fast segs m a bs :=
store_facts a bs ltac:(fun n Hn Ha Hl => transport_chunks_with segs m a bs n Hn Ha Hl).

Ltac footprint_after_store_fast segs m a bs :=
store_facts a bs ltac:(fun n Hn Ha Hl => footprint_after_store_with segs m a bs n Hn Ha Hl).

Definition pk_sep (A sA A2 s2 : Z) : Prop := (A2 + s2 <= A \/ A + sA <= A2)%Z.
Definition pk_nosep (A sA A2 s2 : Z) : Prop := True.
Definition pk_inw (W : list (Z * Z)) (A sA : Z) : Prop := inside W A sA.
Definition pk_noinw (W : list (Z * Z)) (A sA : Z) : Prop := True.
Definition pk_seen (A sA : Z) : Prop := True.
Lemma pk_sep_sub : forall A sA A2 s2 k n, pk_sep A sA A2 s2 -> Z.leb 0 k = true -> Z.leb (k + n) sA = true ->
(A2 + s2 <= A + k \/ A + k + n <= A2)%Z.
Proof. unfold pk_sep; intros A sA A2 s2 k n H H1 H2. apply Z.leb_le in H1, H2. lia. Qed.
Lemma pk_inside_sub : forall W A sA k n, pk_inw W A sA -> Z.leb 0 k = true -> Z.leb 0 n = true -> Z.leb (k + n) sA = true ->
inside W (A + k) n.
Proof.
unfold pk_inw; intros W A sA k n H H1 H0 H2. apply Z.leb_le in H1, H0, H2.
induction W as [|[lo hi] W IH]; cbn in *; [exact H|]. destruct H as [H|H]; [left; lia| right; exact (IH H)].
Qed.
Lemma pk_ha : forall A sA k, (0 <= A /\ A + sA <= 2^64)%Z -> Z.leb 0 k = true -> (0 <= A + k)%Z.
Proof. intros A sA k [H1 H2] H. apply Z.leb_le in H. lia. Qed.
Lemma pk_hl : forall A sA k n, (0 <= A /\ A + sA <= 2^64)%Z -> Z.leb (k + n) sA = true -> (A + k + n <= 2^64)%Z.
Proof. intros A sA k n [H1 H2] H. apply Z.leb_le in H. lia. Qed.

Ltac pk_store_facts_lit HB A sA kn bs k :=
let Hn := fresh "Hn_st" in let Ha := fresh "Ha_st" in let Hl := fresh "Hl_st" in
let n0 := constr:(Z.of_nat (@length byte bs)) in
let n1 := eval cbv [length app cbytes cells_bytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes
Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in n0 in
let n := lazymatch n1 with Zpos _ => n1 | Z0 => n1 | _ => n0 end in
first [ assert (Hn : Z.of_nat (@length byte bs) = n) by exact eq_refl
| fail "store_facts: length of" bs "vs" n ];
first [ pose proof (pk_ha A sA (Z.of_nat kn) HB eq_refl) as Ha
| assert (Ha : (0 <= A + Z.of_nat kn)%Z) by (clear - HB; lia) ];
first [ pose proof (pk_hl A sA (Z.of_nat kn) n HB eq_refl) as Hl
| assert (Hl : (A + Z.of_nat kn + n <= 2^64)%Z) by (clear - HB; lia) ];
sf_hide_poison;
k n Hn Ha Hl;
clear Hn Ha Hl; sf_unhide.

Ltac pk_lit X := let Xl := eval cbv [cells_size csize length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul] in X in
lazymatch Xl with Zpos _ => Xl | Z0 => Xl end.

Ltac pk_sep_get A sA A2 X0 :=
tryif (let X := pk_lit X0 in idtac) then (
let X := pk_lit X0 in
first [ match goal with _ : pk_sep A sA A2 X |- _ => idtac end
| match goal with _ : pk_nosep A sA A2 X |- _ => idtac end
| match goal with _ : pk_seen A sA |- _ => idtac end;
first [ let HS := fresh "__pks" in assert (HS : pk_sep A sA A2 X) by (unfold pk_sep; transport_lia)
| let HS := fresh "__pkn" in pose proof (I : pk_nosep A sA A2 X) as HS ]
| idtac ]) else idtac. Ltac mkr__pk_sep_get_5 A sA A2 X0 := tryif (let X := pk_lit X0 in idtac) then (
let X := pk_lit X0 in
first [ match goal with _ : pk_sep A sA A2 X |- _ => idtac end
| match goal with _ : pk_nosep A sA A2 X |- _ => idtac end
| match goal with _ : pk_seen A sA |- _ => idtac end;
first [ let HS := fresh "__pks" in assert (HS : pk_sep A sA A2 X) by (unfold pk_sep; transport_lia)
| let HS := fresh "__pkn" in pose proof (I : pk_nosep A sA A2 X) as HS ]
| idtac ]) else idtac.

Ltac pk_side A sA kn n :=
first [ lazymatch goal with
| |- (?A2 + ?X0 <= A + Z.of_nat kn \/ A + Z.of_nat kn + n <= ?A2)%Z =>
let X := pk_lit X0 in
match goal with HS : pk_sep A sA A2 X |- _ => exact (pk_sep_sub A sA A2 X (Z.of_nat kn) n HS eq_refl eq_refl) end
end
| simpl_sizes_goal; transport_lia ]. Ltac mkr__pk_side_6 A sA kn n := first [ lazymatch goal with
| |- (?A2 + ?X0 <= A + Z.of_nat kn \/ A + Z.of_nat kn + n <= ?A2)%Z =>
let X := pk_lit X0 in
match goal with HS : pk_sep A sA A2 X |- _ => exact (pk_sep_sub A sA A2 X (Z.of_nat kn) n HS eq_refl eq_refl) end
end
| simpl_sizes_goal; transport_lia ].
Ltac transport_chunks_sep segs m A sA kn bs n Hn Ha Hl :=
let a := constr:((A + Z.of_nat kn)%Z) in
(repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
pk_sep_get A sA A2 constr:(Z.of_nat (length bs2));
first [ apply (bytes_at_write_other_n segs m a bs A2 bs2 n Hn Ha Hl) in H; [ | pk_side A sA kn n ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
pk_sep_get A sA A2 constr:(Z.of_nat (cells_size cs2));
first [ apply (rw_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | pk_side A sA kn n ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
pk_sep_get A sA A2 constr:(Z.of_nat (cells_size cs2));
first [ apply (ro_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | pk_side A sA kn n ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
pk_sep_get A sA A2 constr:(Z.of_nat (length xs));
first [ apply (u8arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | pk_side A sA kn n ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u32arr segs m ?A2 ?xs |- _ =>
pk_sep_get A sA A2 constr:((4 * Z.of_nat (length xs))%Z);
first [ apply (u32arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | pk_side A sA kn n ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u64arr segs m ?A2 ?xs |- _ =>
pk_sep_get A sA A2 constr:((8 * Z.of_nat (length xs))%Z);
first [ apply (u64arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | pk_side A sA kn n ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
pk_sep_get A sA A2 constr:(Z.of_nat (length xs));
first [ apply (u8ro_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | pk_side A sA kn n ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
end);
transport_chunks_extra m a bs n Hn Ha Hl.
Ltac pk_inw_get W A sA :=
first [ match goal with _ : pk_inw W A sA |- _ => idtac end
| match goal with _ : pk_noinw W A sA |- _ => idtac end
| match goal with _ : pk_seen A sA |- _ => idtac end;
first [ let HS := fresh "__pki" in assert (HS : pk_inw W A sA) by (unfold pk_inw; cbn [inside]; transport_lia)
| let HS := fresh "__pkj" in pose proof (I : pk_noinw W A sA) as HS ]
| idtac ].
Ltac footprint_after_store_sep segs m A sA kn bs n Hn Ha Hl :=
let a := constr:((A + Z.of_nat kn)%Z) in
repeat match goal with
| MU : munch ?Wq ?mq m |- _ =>
pk_inw_get Wq A sA;
first [ apply (munch_write_n Wq mq m a bs n Hn Ha Hl) in MU;
[ | first [ match goal with HS : pk_inw Wq A sA |- _ => exact (pk_inside_sub Wq A sA (Z.of_nat kn) n HS eq_refl eq_refl eq_refl) end
| cbn [inside]; transport_lia ] ]
| fail 100 "store outside the declared footprint:" a ]
| WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
| STq : stk segs m ?loq ?hiq |- _ =>
first [ apply (stk_write_n segs m loq hiq a bs n Hn Ha Hl) in STq
| fail 100 "cannot transport stk hypothesis" STq ]
end.

Ltac mem_after_store_fast :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
let ok := eval_cb_split_ok cs0 kn n in lazymatch ok with true => idtac end;
let cs := eval_cb_split cs0 kn n in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs0 H) as HB; literal_cell_sizes_in HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (pk_rw_cells_store_ok_split segs m A cs0 cs kn c0 n _ H eq_refl eq_refl); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (pk_rw_cells_write_split segs m A cs0 cs kn c0 c' n H eq_refl eq_refl ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
let sA0 := lazymatch type of HB with (_ /\ _ + ?s <= _)%Z => s end in
tryif (let sA := pk_lit sA0 in idtac)
then (let sA := pk_lit sA0 in
pk_store_facts_lit HB A sA kn (cbytes c') ltac:(fun n' Hn Ha Hl =>
transport_chunks_sep segs m A sA kn (cbytes c') n' Hn Ha Hl;
footprint_after_store_sep segs m A sA kn (cbytes c') n' Hn Ha Hl);
tryif (match goal with _ : pk_seen A sA |- _ => idtac end) then idtac
else (let HS := fresh "__pkm" in pose proof (I : pk_seen A sA) as HS))
else store_facts_hb HB (A + Z.of_nat kn)%Z (cbytes c') ltac:(fun n' Hn Ha Hl =>
transport_chunks_with segs m (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl;
footprint_after_store_with segs m (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl);
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; try rename H' into H
end
end
end.

Ltac disjoint_goal :=
cbv [disjoint_from fst snd];
simpl_sizes_goal;
lazymatch goal with
| |- _ /\ _ /\ _ /\ _ => repeat split; transport_lia
| |- _ => transport_lia
end. Ltac mkr__disjoint_goal_7 := cbv [disjoint_from fst snd];
simpl_sizes_goal;
lazymatch goal with
| |- _ /\ _ /\ _ /\ _ => repeat split; transport_lia
| |- _ => transport_lia
end.

Ltac transport_after_call_fast segs m m' MU WM :=
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

first [ Qo9G.term_slim ltac:(intros; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(sf_unhide; zify_prune_plain; intros; Zify.zify; xlia zchecker)
| intros; transport_lia ]
| exact MU ] ]
| fail 100 "callee footprint not inside caller footprint" ]
| H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
end);
transport_call_extra segs W m m' MU WM;
sf_unhide.
