(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg Lib.GwApply Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import ListNotations.
Open Scope bv_scope.

Definition ms_facts (A n i : Z) (k : nat) : Prop :=
(0 <= i /\ i + Z.of_nat k <= n /\ 0 <= A /\ A + n <= 2^64)%Z.

Lemma ms_store_ok : forall segs m A n bs i k a,
u8arr segs m A bs -> length bs = Z.to_nat n -> ms_facts A n i k -> a = wa (A + i) ->
store_ok segs m a k = true.
Proof.
intros segs m A n bs i k a ARR LEN (Hi & Hk & _) Ha.
eapply (u8arr_store_ok_n segs m A bs i k a ARR); [lia | rewrite LEN; lia | exact Ha].
Qed.

Lemma ms_store : forall segs m0 m A n bs cb (Q : Z -> Prop) i k a,
u8arr segs m A bs -> filled cb bs Q -> length bs = Z.to_nat n ->
mem_inv segs m -> munch [(A, A + n)]%Z m0 m -> wmono segs m0 m ->
ms_facts A n i k -> a = wa (A + i) ->
u8arr segs (write_to_mem m a (repeat cb k)) A (upd_bytes bs (Z.to_nat i) (repeat cb k)) /\
filled cb (upd_bytes bs (Z.to_nat i) (repeat cb k)) (fun j => Q j \/ (i <= j < i + Z.of_nat k)%Z) /\
length (upd_bytes bs (Z.to_nat i) (repeat cb k)) = Z.to_nat n /\
mem_inv segs (write_to_mem m a (repeat cb k)) /\ munch [(A, A + n)]%Z m0 (write_to_mem m a (repeat cb k)) /\
wmono segs m0 (write_to_mem m a (repeat cb k)).
Proof.
intros segs m0 m A n bs cb Q i k a ARR FIL LEN MI MU WM MF Ha.
assert (SOK : store_ok segs m a (length (repeat cb k)) = true).
{ rewrite repeat_length. eapply ms_store_ok; eauto. }
destruct MF as (Hi & Hk & A0 & An). subst a.
split; [|split; [|split; [|split; [|split]]]].
- apply (u8arr_write_bytes segs m A bs i _ ARR); [lia|]. rewrite repeat_length, LEN. lia.
- apply filled_updZ; [exact FIL | lia | rewrite LEN; lia].
- rewrite upd_bytes_length; [exact LEN|]. rewrite repeat_length, LEN. lia.
- apply mem_inv_store; assumption.
- apply munch_write; [exact MU | lia | rewrite repeat_length; lia |]. cbn [inside]. left. rewrite repeat_length. lia.
- apply wmono_write. exact WM.
Qed.

Ltac ms_arr_store MF bytes_tac :=
lazymatch goal with
| ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs ?Q, LEN : length ?bs = Z.to_nat ?n,
MI : mem_inv ?segs ?m, MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m
|- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
lazymatch type of MF with ms_facts _ _ ?i ?k =>
let xs := eval cbv beta iota delta [repeat] in (repeat cb k) in
let kz := eval vm_compute in (Z.of_nat k) in
replace (write_to_mem m a bs0) with (write_to_mem m (wa (A + i)%Z) xs)
by (apply (f_equal2 (write_to_mem m)); [ unfold wa; first [ reflexivity | f_equal; lia | rewrite ?Z.add_0_r; apply Z_to_bv_bv_unsigned ] | bytes_tac ]);
let ARR' := fresh "ARR" in let FIL' := fresh "FIL" in let LEN' := fresh "LEN" in
let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
destruct (ms_store segs m0 m A n bs cb Q i k _ ARR FIL LEN MI MU WM MF eq_refl)
as (ARR' & FIL' & LEN' & MI' & MU' & WM');
change (repeat cb k) with xs in ARR', FIL', LEN', MI', MU', WM';
change (repeat cb k) with xs;
cbv beta in FIL'; change (Z.of_nat k) with kz in FIL';
clear ARR FIL LEN MI MU WM MF;
repeat match goal with
| H : store_ok segs m _ _ = true |- _ => clear H
| H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
end;
let m' := fresh "m" in remember (write_to_mem m (wa (A + i)%Z) xs) as m' eqn:Heqm; clear Heqm; try clear m;
let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat i) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
rename ARR' into ARR; rename FIL' into FIL; rename LEN' into LEN;
rename MI' into MI; rename MU' into MU; rename WM' into WM
end
end.

Ltac mst i k bytes_tac :=
lazymatch goal with
| ARR : u8arr ?segs ?m ?A ?bs, LEN : length ?bs = Z.to_nat ?n |- _ =>
let MF := fresh "MF" in let SOK := fresh "SOK" in
assert (MF : ms_facts A n i k) by (unfold ms_facts; lia);
pose proof (ms_store_ok segs m A n bs i k (wa (A + i)) ARR LEN MF eq_refl) as SOK; unfold wa in SOK;
zstep; [ ms_arr_store MF bytes_tac | .. ]
end.

End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbVh QbrW QlEo_c1 QWxq_c1.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxOB Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QsjA QEpW QZDE QbVh QbrW QlEo_c1 QWxq_c1 Q5Rg QXup.

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

Ltac2 prune_with (keep : constr -> bool) : unit :=
let hs := Control.hyps () in
let ids := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None => if arith_logic ty then (if keep ty then None else Some id) else None
end) hs in
match ids with [] => () | _ :: _ => Std.clear ids end.

Ltac2 prune_plain () : unit := prune_with (fun ty => plain_arith false ty).

Ltac2 prune_clean () : unit :=
let bad := bad_heads () in prune_with (fun ty => if plain_arith false ty then clean bad ty else false).

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
Ltac sf_hide_poison := SF2.sf_hide_poison. Ltac mkr__sf_hide_poison_0 := SF2.sf_hide_poison.
Ltac sf_unhide := repeat match goal with H : sf_hide _ |- _ => unfold sf_hide in H end.
Ltac zify_prune_plain := SF2.zify_prune_plain.
Ltac zify_prune_clean := SF2.zify_prune_clean.
Ltac lia3 := Qo9G.term_slim ltac:(first [ zify_prune_plain; Zify.zify; xlia zchecker
| zify_prune_neg; Zify.zify; xlia zchecker
| Zify.zify; xlia zchecker ]).

Module SFS.
Import Ltac2.
Ltac2 subset (xs : ident list) (ys : ident list) : bool := List.for_all (fun x => List.exist (Ident.equal x) ys) xs.
Ltac2 prune_sub () : unit :=
let gv := SepCacheRel.vars_of [] (Control.goal ()) in
let hs := Control.hyps () in
let ids := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None => if QxOB.zt_plain_arith ty then None
else if Bool.and (QxOB.zt_is_local id) (QxOB.zt_is_prop ty) then
(if SepCacheRel.arith_logic ty then (if subset (SepCacheRel.vars_of [] ty) gv then None else Some id) else Some id)
else None
end) hs in
match ids with [] => () | _ :: _ => Std.clear ids end.
End SFS.
Ltac sf_prune_sub := ltac2:(Control.enter SFS.prune_sub).
Ltac sf_lia_sub := Qo9G.term_slim ltac:(Q6q3.rc_lia_prep; sf_prune_sub; QxOB.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker).
Ltac tlia := Qo9G.term_slim ltac:(first [ Zify.zify; xlia zchecker
| sf_unhide;
first [ sf_lia_sub
| sc_lia_rel
| zify_prune_neg; Zify.zify; xlia zchecker
| zify_prune_plain; Zify.zify; xlia zchecker
| Zify.zify; xlia zchecker ] ]).
Ltac tslia := first [ exact I | tlia | split; [ tlia | exact I ] ]. Ltac mkr__tslia_1 := first [ exact I | tlia | split; [ tlia | exact I ] ].

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma bytes_at_write_other_n : forall m a bs c cs (n : Z),
Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
bytes_at segs m c cs ->
(c + Z.of_nat (length cs) <= a \/ a + n <= c)%Z ->
bytes_at segs (write_to_mem m (wa a) bs) c cs.
Proof. intros m a bs c cs n <- Ha Hl H Hd. apply bytes_at_write_other; assumption. Qed.

#[using="Type"] Lemma rw_cells_frame_n : forall m A cs (a : Z) bs (n : Z),
Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
rw_cells segs m A cs ->
(A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z ->
rw_cells segs (write_to_mem m (wa a) bs) A cs.
Proof. intros m A cs a bs n <- Ha Hl H Hd. apply rw_cells_frame; assumption. Qed.

#[using="Type"] Lemma ro_cells_frame_n : forall m A cs (a : Z) bs (n : Z),
Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
ro_cells segs m A cs ->
(A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z ->
ro_cells segs (write_to_mem m (wa a) bs) A cs.
Proof. intros m A cs a bs n <- Ha Hl H Hd. apply ro_cells_frame; assumption. Qed.

#[using="Type"] Lemma u8arr_frame_n : forall m A bs a xs (n : Z),
Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
u8arr segs m A bs ->
(A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z ->
u8arr segs (write_to_mem m (wa a) xs) A bs.
Proof. intros m A bs a xs n <- Ha Hl H Hd. apply u8arr_frame; assumption. Qed.

#[using="Type"] Lemma u32arr_frame_n : forall m A ws a xs (n : Z),
Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
u32arr segs m A ws ->
(A + 4 * Z.of_nat (length ws) <= a \/ a + n <= A)%Z ->
u32arr segs (write_to_mem m (wa a) xs) A ws.
Proof. intros m A ws a xs n <- Ha Hl H Hd. apply u32arr_frame; assumption. Qed.

#[using="Type"] Lemma u64arr_frame_n : forall m A ws a xs (n : Z),
Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
u64arr segs m A ws ->
(A + 8 * Z.of_nat (length ws) <= a \/ a + n <= A)%Z ->
u64arr segs (write_to_mem m (wa a) xs) A ws.
Proof. intros m A ws a xs n <- Ha Hl H Hd. apply u64arr_frame; assumption. Qed.

#[using="Type"] Lemma u8ro_frame_n : forall m A bs a xs (n : Z),
Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
u8ro segs m A bs ->
(A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z ->
u8ro segs (write_to_mem m (wa a) xs) A bs.
Proof. intros m A bs a xs n <- Ha Hl H Hd. apply u8ro_frame; assumption. Qed.

#[using="Type"] Lemma stk_write_n : forall m lo hi a bs (n : Z),
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

Ltac transport_chunks_extra m a bs n Hn Ha Hl := idtac.
Ltac transport_call_extra segs W m m' MU WM := idtac.

Ltac transport_chunks_with segs m a bs n Hn Ha Hl :=
(repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_write_other_n segs m a bs A2 bs2 n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ apply (u8arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u32arr segs m ?A2 ?xs |- _ =>
first [ apply (u32arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u64arr segs m ?A2 ?xs |- _ =>
first [ apply (u64arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ apply (u8ro_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
end);
transport_chunks_extra m a bs n Hn Ha Hl.

Ltac footprint_after_store_with segs m a bs n Hn Ha Hl :=
repeat match goal with
| MU : munch ?Wq ?mq m |- _ =>
first [ apply (munch_write_n Wq mq m a bs n Hn Ha Hl) in MU; [ | cbn [inside]; tslia ]
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

Ltac mem_after_store_fast :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
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
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; try rename H' into H
end
end
end.

Ltac disjoint_goal :=
cbv [disjoint_from fst snd];
simpl_sizes_goal;
tslia. Ltac mkr__disjoint_goal_4 := cbv [disjoint_from fst snd];
simpl_sizes_goal;
tslia.

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
| intros; tslia ]
| exact MU ] ]
| fail 100 "callee footprint not inside caller footprint" ]
| H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
end);
transport_call_extra segs W m m' MU WM;
sf_unhide.
End Mq1.
From LinuxProcessSemantics.LinuxProcessSem Require Fs Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QlEo_c1.Mq0 QWxq_c1.Mq1.
Export Q5Rg.Mq0.
Import ListNotations.
Open Scope bv_scope.

Lemma evt_ecall : forall segs (Q : machine_state -> Prop) R F pc fc rv m ro w,
fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true ->
Q (MSsvc R F (Z_to_bv 64 pc) (reg_get R 17) fc rv m ro) ->
evt segs Q (MS R F (Z_to_bv 64 pc) fc rv m ro).
Proof.
intros segs Q R F pc fc rv m ro w Hf He HQ.
eapply evt_step; [|apply evt_done; exact HQ].
split; [reflexivity|]. rewrite (step_ecall_gen segs R F (Z_to_bv 64 pc) fc rv m ro w Hf He). reflexivity.
Qed.

Ltac step_ecall :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with
| Some ?w =>
apply (evt_ecall segs Q R F pc fc rv m ro w);
[ vm_compute; reflexivity | vm_compute; reflexivity | simp_regs ]
| None => fail "no instruction at" pc
end
end. Ltac mkr__step_ecall_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with
| Some ?w =>
apply (evt_ecall segs Q R F pc fc rv m ro w);
[ vm_compute; reflexivity | vm_compute; reflexivity | simp_regs ]
| None => fail "no instruction at" pc
end
end.

Lemma nret_MSsvc : forall R F pc x8 fc rv m ro r ws zs us cis,
nret (MSsvc R F pc x8 fc rv m ro) (mkEffectU r ws zs us [] cis)
= MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4) fc rv (apply_writes (apply_zeros (apply_unmaps m us) zs) ws) ro.
Proof. reflexivity. Qed.

Lemma nret_MSsvc_cs : forall R F pc x8 fc rv m ro r ws zs us cs cis,
nret (MSsvc R F pc x8 fc rv m ro) (mkEffectU r ws zs us cs cis)
= MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4) fc rv (apply_writes (apply_copies m (apply_zeros (apply_unmaps m us) zs) cs) ws) ro.
Proof. reflexivity. Qed.

Lemma mkR_set_a0 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 v,
bvmap_set 10 v (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
= mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
Proof. reflexivity. Qed.

Lemma apply_mem_none : forall m, apply_writes (apply_zeros (apply_unmaps m []) []) [] = m.
Proof. reflexivity. Qed.

Lemma apply_mem_write : forall m a bs, apply_writes (apply_zeros (apply_unmaps m []) []) [(a, bs)] = write_to_mem m a bs.
Proof. reflexivity. Qed.

Lemma apply_mem_delivered : forall m a bs,
apply_writes (apply_zeros (apply_unmaps m []) []) (delivered_writes a bs) = write_to_mem m a bs.
Proof. intros m a [|b bs]; reflexivity. Qed.

Definition in_range (a n : Z) (x : word) : bool :=
(a <=? bv_unsigned x)%Z && (bv_unsigned x <? a + n)%Z.

Lemma apply_zeros_spec : forall m a n x, (0 <= a < 2^64)%Z -> (0 <= n < 2^64)%Z -> (a + n <= 2^64)%Z ->
apply_zeros m [(wa a, Z_to_bv 64 n)] x = if in_range a n x then Some (Z_to_bv 8 0) else m x.
Proof.
intros m a n x Ha Hn Han. cbn [apply_zeros zeros_cover existsb fst snd]. unfold in_range.
rewrite wa_unsigned by lia. rewrite unsigned_lit by lia. rewrite orb_false_r. reflexivity.
Qed.

Lemma apply_unmaps_spec : forall m a n x, (0 <= a < 2^64)%Z -> (0 <= n < 2^64)%Z -> (a + n <= 2^64)%Z ->
apply_unmaps m [(wa a, Z_to_bv 64 n)] x = if in_range a n x then None else m x.
Proof.
intros m a n x Ha Hn Han. cbn [apply_unmaps zeros_cover existsb fst snd]. unfold in_range.
rewrite wa_unsigned by lia. rewrite unsigned_lit by lia. rewrite orb_false_r. reflexivity.
Qed.

Section MemEffects.
Variable segs : list Segment.

#[using="Type"] Lemma rw_cells_CB_prefix_write : forall m A n junk bs,
rw_cells segs m A [CB n junk] -> (length bs <= n)%nat ->
rw_cells segs (write_to_mem m (wa A) bs) A [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)].
Proof.
intros m A n junk bs [[Hwf Hb] Hw] Hlen. cbn in Hwf. destruct Hwf as [Hj _].
cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
split; [split|].
- cbn. repeat split; try reflexivity. rewrite skipn_length. lia.
- cbn [cells_bytes cbytes]. rewrite app_nil_r.
pose proof (bytes_at_write_inside segs m A junk 0 bs Hb ltac:(lia) ltac:(cbn; lia)) as W.
rewrite Z.add_0_r in W. unfold upd_bytes in W. cbn [firstn app Nat.add] in W. exact W.
- cbn [cells_size csize]. cbn [cells_size csize] in Hw. replace (length bs + (n - length bs + 0))%nat with (n + 0)%nat by lia.
apply wr_at_write. exact Hw.
Qed.

#[using="Type"] Lemma rw_cells_CB_store_ok : forall m A n junk k,
rw_cells segs m A [CB n junk] -> (k <= n)%nat -> store_ok segs m (wa A) k = true.
Proof.
intros m A n junk k [_ Hw] Hk. cbn [cells_size csize] in Hw.
rewrite <- (Z.add_0_r A). apply (wr_at_store_ok segs m A (Z.of_nat (n + 0))); [exact Hw|lia|lia].
Qed.

#[using="Type"] Lemma mem_inv_syswrite : forall m A n junk bs,
mem_inv segs m -> rw_cells segs m A [CB n junk] -> (length bs <= n)%nat ->
mem_inv segs (write_to_mem m (wa A) bs).
Proof.
intros. apply mem_inv_store; [assumption|]. eapply rw_cells_CB_store_ok; eauto.
Qed.

Section Zeros.
Variables (m : word -> option byte) (a n : Z).
Hypothesis Ha : (0 <= a < 2^64)%Z.
Hypothesis Hn : (0 <= n < 2^64)%Z.
Hypothesis Han : (a + n <= 2^64)%Z.
Let m' := apply_zeros m [(wa a, Z_to_bv 64 n)].

#[using="Ha Hn Han"] Lemma zeros_outside : forall x, (bv_unsigned x < a \/ a + n <= bv_unsigned x)%Z -> m' x = m x.
Proof.
intros x Hx. unfold m'. rewrite apply_zeros_spec by assumption. unfold in_range.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity. lia.
Qed.

#[using="Ha Hn Han"] Lemma zeros_inside : forall x, (a <= bv_unsigned x < a + n)%Z -> m' x = Some (Z_to_bv 8 0).
Proof.
intros x Hx. unfold m'. rewrite apply_zeros_spec by assumption. unfold in_range.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity; lia.
Qed.

#[using="Ha Hn Han"] Lemma wview_zeros_mono : forall x, wview segs m x <> None -> wview segs m' x <> None.
Proof.
intros x Hx. unfold wview in *. unfold m'. rewrite apply_zeros_spec by assumption.
destruct (in_range a n x); [discriminate| exact Hx].
Qed.

#[using="Ha Hn Han"] Lemma bytes_at_zeros_other : forall A bs,
bytes_at segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> bytes_at segs m' A bs.
Proof.
intros A bs (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros i Hi.
unfold mrd. rewrite zeros_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.

#[using="Ha Hn Han"] Lemma wr_at_zeros : forall A k, wr_at segs m A k -> wr_at segs m' A k.
Proof. intros A k (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. apply wview_zeros_mono, H, Hi. Qed.

#[using="Ha Hn Han"] Lemma rw_cells_zeros_other : forall A cs,
rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> rw_cells segs m' A cs.
Proof.
intros A cs [[Hwf Hb] Hw] Hd. split; [split; [exact Hwf|]|].
- apply bytes_at_zeros_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
- apply wr_at_zeros. exact Hw.
Qed.

#[using="Ha Hn Han"] Lemma ro_cells_zeros_other : forall A cs,
ro_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> ro_cells segs m' A cs.
Proof.
intros A cs [Hwf Hb] Hd. split; [exact Hwf|].
apply bytes_at_zeros_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
Qed.

#[using="Ha Hn Han"] Lemma stk_zeros : forall lo hi, stk segs m lo hi -> stk segs m' lo hi.
Proof.
intros lo hi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros x Hx.
destruct (H x Hx) as [Hw (b & Hb)]. split; [apply wview_zeros_mono; exact Hw|].
unfold mrd in *. unfold m'. rewrite apply_zeros_spec by assumption.
destruct (in_range a n (wa x)); [eexists; reflexivity|]. exists b. exact Hb.
Qed.

#[using="Ha Hn Han"] Lemma munch_zeros : forall W m0, munch W m0 m -> inside W a n -> munch W m0 m'.
Proof.
intros W m0 H Hin x Hx. pose proof (bv_unsigned_in_range 64 x).
rewrite zeros_outside. { apply H. exact Hx. }
destruct (Z.ltb_spec0 (bv_unsigned x) a); [lia|].
destruct (Z.leb_spec0 (a + n) (bv_unsigned x)); [lia|].
exfalso. eapply (inside_not_outside W a n (bv_unsigned x) Hin); [lia| exact Hx].
Qed.

#[using="Ha Hn Han"] Lemma wmono_zeros : forall m0, wmono segs m0 m -> wmono segs m0 m'.
Proof. intros m0 H x Hx. apply wview_zeros_mono, H, Hx. Qed.

#[using="Ha Hn Han"] Lemma mem_inv_zeros : mem_inv segs m -> (forall x : word, (a <= bv_unsigned x < a + n)%Z -> ro_addr segs x = false) -> mem_inv segs m'.
Proof.
intros Hinv Hro x b Hx. unfold m' in Hx. rewrite apply_zeros_spec in Hx by assumption.
unfold in_range in Hx.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb] in Hx;
try exact (Hinv _ _ Hx).
apply Hro. lia.
Qed.

#[using="Ha Hn Han"] Lemma bytes_at_zeros_new : bytes_at segs m' a (repeat (Z_to_bv 8 0) (Z.to_nat n)).
Proof.
split; [lia|]. rewrite repeat_length. split; [lia|]. intros i Hi.
unfold mrd. rewrite zeros_inside. 2:{ rewrite wa_unsigned by lia. lia. }
symmetry. apply nth_error_repeat. exact Hi.
Qed.

#[using="Ha Hn Han"] Lemma wr_at_zeros_new : wr_at segs m' a n.
Proof.
split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite zeros_inside; [discriminate|].
rewrite wa_unsigned by lia. lia.
Qed.

#[using="Ha Hn Han"] Lemma rw_cells_zeros_new : rw_cells segs m' a [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
Proof.
split; [split|].
- cbn. split; [apply repeat_length| exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_zeros_new.
- cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. apply wr_at_zeros_new.
Qed.

End Zeros.

Section Unmaps.
Variables (m : word -> option byte) (a n : Z).
Hypothesis Ha : (0 <= a < 2^64)%Z.
Hypothesis Hn : (0 <= n < 2^64)%Z.
Hypothesis Han : (a + n <= 2^64)%Z.
Let m' := apply_unmaps m [(wa a, Z_to_bv 64 n)].

#[using="Ha Hn Han"] Lemma unmaps_outside : forall x, (bv_unsigned x < a \/ a + n <= bv_unsigned x)%Z -> m' x = m x.
Proof.
intros x Hx. unfold m'. rewrite apply_unmaps_spec by assumption. unfold in_range.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity. lia.
Qed.

#[using="Ha Hn Han"] Lemma bytes_at_unmaps_other : forall A bs,
bytes_at segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> bytes_at segs m' A bs.
Proof.
intros A bs (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros i Hi.
unfold mrd. rewrite unmaps_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.

#[using="Ha Hn Han"] Lemma wr_at_unmaps_other : forall A k,
wr_at segs m A k -> (A + k <= a \/ a + n <= A)%Z -> wr_at segs m' A k.
Proof.
intros A k (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros i Hi.
unfold wview. rewrite unmaps_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.

#[using="Ha Hn Han"] Lemma rw_cells_unmaps_other : forall A cs,
rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> rw_cells segs m' A cs.
Proof.
intros A cs [[Hwf Hb] Hw] Hd. split; [split; [exact Hwf|]|].
- apply bytes_at_unmaps_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
- apply wr_at_unmaps_other; [exact Hw| exact Hd].
Qed.

#[using="Ha Hn Han"] Lemma ro_cells_unmaps_other : forall A cs,
ro_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> ro_cells segs m' A cs.
Proof.
intros A cs [Hwf Hb] Hd. split; [exact Hwf|].
apply bytes_at_unmaps_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
Qed.

#[using="Ha Hn Han"] Lemma stk_unmaps_other : forall lo hi, stk segs m lo hi -> (hi <= a \/ a + n <= lo)%Z -> stk segs m' lo hi.
Proof.
intros lo hi (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros x Hx.
destruct (H x Hx) as [Hw (b & Hb)].
assert (E : m' (wa x) = m (wa x)). { apply unmaps_outside. rewrite wa_unsigned by lia. lia. }
split. { unfold wview in *. rewrite E. exact Hw. } exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

#[using="Ha Hn Han"] Lemma munch_unmaps : forall W m0, munch W m0 m -> inside W a n -> munch W m0 m'.
Proof.
intros W m0 H Hin x Hx. pose proof (bv_unsigned_in_range 64 x).
rewrite unmaps_outside. { apply H. exact Hx. }
destruct (Z.ltb_spec0 (bv_unsigned x) a); [lia|].
destruct (Z.leb_spec0 (a + n) (bv_unsigned x)); [lia|].
exfalso. eapply (inside_not_outside W a n (bv_unsigned x) Hin); [lia| exact Hx].
Qed.

#[using="Ha Hn Han"] Lemma mem_inv_unmaps : mem_inv segs m -> mem_inv segs m'.
Proof.
intros Hinv x b Hx. unfold m' in Hx. rewrite apply_unmaps_spec in Hx by assumption.
destruct (in_range a n x); [discriminate|]. exact (Hinv _ _ Hx).
Qed.

End Unmaps.

#[using="Type"] Lemma apply_copy_spec : forall before mem (src dst len : Z) x,
(0 <= src < 2^64)%Z -> (0 <= dst < 2^64)%Z -> (0 <= len < 2^64)%Z ->
apply_copy before mem (mkCopy (wa src) (wa dst) (Z_to_bv 64 len)) x
= if in_range dst len x then before (wa (src + (bv_unsigned x - dst))) else mem x.
Proof.
intros before mem src dst len x Hs Hd Hl. unfold apply_copy, in_range. cbn [copy_src copy_dst copy_len].
rewrite !wa_unsigned by lia. rewrite ?unsigned_lit by lia. reflexivity.
Qed.

Section Move.
Variables (m : word -> option byte) (old on a nn : Z).
Hypothesis Hold : (0 <= old < 2^64)%Z.
Hypothesis Hon : (0 <= on)%Z.
Hypothesis Holdhi : (old + on <= 2^64)%Z.
Hypothesis Ha0 : (0 <= a < 2^64)%Z.
Hypothesis Hnn : (on < nn < 2^64)%Z.
Hypothesis Hahi : (a + nn <= 2^64)%Z.
Hypothesis DISJ : (old + on <= a \/ a + nn <= old)%Z.
Let m' := apply_copy m (apply_zeros (apply_unmaps m [(wa old, Z_to_bv 64 on)]) [(wa (a + on), Z_to_bv 64 (nn - on))])
(mkCopy (wa old) (wa a) (Z_to_bv 64 on)).

#[using="Hold Hon Holdhi Ha0 Hnn Hahi DISJ"] Lemma move_spec : forall x : word,
m' x = if in_range a on x then m (wa (old + (bv_unsigned x - a)))
else if in_range (a + on) (nn - on) x then Some (Z_to_bv 8 0)
else if in_range old on x then None else m x.
Proof.
intros x. unfold m'. rewrite apply_copy_spec by lia. rewrite apply_zeros_spec by lia. rewrite apply_unmaps_spec by lia.
destruct (in_range a on x); reflexivity.
Qed.

#[using="Hold Hon Holdhi Ha0 Hnn Hahi DISJ"] Lemma move_outside : forall x, (bv_unsigned x < a \/ a + nn <= bv_unsigned x)%Z ->
(bv_unsigned x < old \/ old + on <= bv_unsigned x)%Z -> m' x = m x.
Proof.
intros x H1 H2. rewrite move_spec. unfold in_range.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + on)); cbn [andb]; try lia;
destruct (Z.leb_spec0 (a + on) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + on + (nn - on))); cbn [andb]; try lia;
destruct (Z.leb_spec0 old (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (old + on)); cbn [andb]; try lia; reflexivity.
Qed.

#[using="Hold Hon Holdhi Ha0 Hnn Hahi DISJ"] Lemma move_copied : forall x, (a <= bv_unsigned x < a + on)%Z -> m' x = m (wa (old + (bv_unsigned x - a))).
Proof.
intros x Hx. rewrite move_spec. unfold in_range.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + on)); cbn [andb]; try lia. reflexivity.
Qed.

#[using="Hold Hon Holdhi Ha0 Hnn Hahi DISJ"] Lemma move_zeroed : forall x, (a + on <= bv_unsigned x < a + nn)%Z -> m' x = Some (Z_to_bv 8 0).
Proof.
intros x Hx. rewrite move_spec. unfold in_range.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + on)); cbn [andb]; try lia;
destruct (Z.leb_spec0 (a + on) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + on + (nn - on))); cbn [andb]; try lia; reflexivity.
Qed.

Definition move_other (A k : Z) : Prop := (A + k <= a \/ a + nn <= A)%Z /\ (A + k <= old \/ old + on <= A)%Z.

#[using="Hold Hon Holdhi Ha0 Hnn Hahi DISJ"] Lemma bytes_at_move_other : forall A bs,
bytes_at segs m A bs -> move_other A (Z.of_nat (length bs)) -> bytes_at segs m' A bs.
Proof.
intros A bs (H0 & H1 & H) [D1 D2]. split; [lia|]. split; [lia|]. intros i Hi.
unfold mrd. rewrite move_outside. { apply H. exact Hi. } all: rewrite wa_unsigned by lia; lia.
Qed.

#[using="Hold Hon Holdhi Ha0 Hnn Hahi DISJ"] Lemma wr_at_move_other : forall A k, wr_at segs m A k -> move_other A k -> wr_at segs m' A k.
Proof.
intros A k (H0 & H1 & H) [D1 D2]. split; [lia|]. split; [lia|]. intros i Hi.
unfold wview. rewrite move_outside. { apply H. exact Hi. } all: rewrite wa_unsigned by lia; lia.
Qed.

#[using="Hold Hon Holdhi Ha0 Hnn Hahi DISJ"] Lemma rw_cells_move_other : forall A cs,
rw_cells segs m A cs -> move_other A (Z.of_nat (cells_size cs)) -> rw_cells segs m' A cs.
Proof.
intros A cs [[Hwf Hb] Hw] Hd. split; [split; [exact Hwf|]|].
- apply bytes_at_move_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
- apply wr_at_move_other; [exact Hw| exact Hd].
Qed.

#[using="Hold Hon Holdhi Ha0 Hnn Hahi DISJ"] Lemma ro_cells_move_other : forall A cs,
ro_cells segs m A cs -> move_other A (Z.of_nat (cells_size cs)) -> ro_cells segs m' A cs.
Proof.
intros A cs [Hwf Hb] Hd. split; [exact Hwf|].
apply bytes_at_move_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
Qed.

#[using="Hold Hon Holdhi Ha0 Hnn Hahi DISJ"] Lemma stk_move_other : forall lo hi, stk segs m lo hi -> (hi <= a \/ a + nn <= lo)%Z -> (hi <= old \/ old + on <= lo)%Z ->
stk segs m' lo hi.
Proof.
intros lo hi (H0 & H1 & H) D1 D2. split; [lia|]. split; [lia|]. intros x Hx.
destruct (H x Hx) as [Hw (b & Hb)].
assert (E : m' (wa x) = m (wa x)) by (apply move_outside; rewrite wa_unsigned by lia; lia).
split. { unfold wview in *. rewrite E. exact Hw. } exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

#[using="Hold Hon Holdhi Ha0 Hnn Hahi DISJ"] Lemma munch_move : forall W m0, munch W m0 m -> inside W a nn -> inside W old on -> munch W m0 m'.
Proof.
intros W m0 H Hin1 Hin2 x Hx. pose proof (bv_unsigned_in_range 64 x).
rewrite move_outside. { apply H. exact Hx. }
- destruct (Z.ltb_spec0 (bv_unsigned x) a); [lia|]. destruct (Z.leb_spec0 (a + nn) (bv_unsigned x)); [lia|].
exfalso. eapply (inside_not_outside W a nn (bv_unsigned x) Hin1); [lia| exact Hx].
- destruct (Z.ltb_spec0 (bv_unsigned x) old); [lia|]. destruct (Z.leb_spec0 (old + on) (bv_unsigned x)); [lia|].
exfalso. eapply (inside_not_outside W old on (bv_unsigned x) Hin2); [lia| exact Hx].
Qed.

#[using="Hold Hon Holdhi Ha0 Hnn Hahi DISJ"] Lemma mem_inv_move : mem_inv segs m -> (forall x : word, (a <= bv_unsigned x < a + nn)%Z -> ro_addr segs x = false) ->
mem_inv segs m'.
Proof.
intros Hinv Hro x b Hx. pose proof (bv_unsigned_in_range 64 x) as R.
rewrite move_spec in Hx. unfold in_range in Hx.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + on)); cbn [andb] in Hx;
[apply Hro; lia| | |];
(destruct (Z.leb_spec0 (a + on) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + on + (nn - on))); cbn [andb] in Hx;
[apply Hro; lia| | |];
(destruct (Z.leb_spec0 old (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (old + on)); cbn [andb] in Hx;
[discriminate| exact (Hinv _ _ Hx)..])).
Qed.

#[using="Hold Hon Holdhi Ha0 Hnn Hahi DISJ"] Lemma bytes_at_move_copy : forall bs, bytes_at segs m old bs -> (Z.of_nat (length bs) <= on)%Z ->
(forall i, (i < length bs)%nat -> exists b, m (wa (old + Z.of_nat i)) = Some b) ->
bytes_at segs m' a bs.
Proof.
intros bs (H0 & H1 & H) Hl Hm. split; [lia|]. split; [lia|]. intros i Hi.
unfold mrd. rewrite move_copied by (rewrite wa_unsigned by lia; lia).
rewrite wa_unsigned by lia. replace (old + (a + Z.of_nat i - a))%Z with (old + Z.of_nat i)%Z by lia.
destruct (Hm i Hi) as [b Hb]. rewrite Hb. specialize (H i Hi). unfold mrd in H. rewrite Hb in H. exact H.
Qed.

#[using="Hold Hon Holdhi Ha0 Hnn Hahi DISJ"] Lemma bytes_at_move_zeros : bytes_at segs m' (a + on) (repeat (Z_to_bv 8 0) (Z.to_nat (nn - on))).
Proof.
split; [lia|]. rewrite repeat_length. split; [lia|]. intros i Hi.
unfold mrd. rewrite move_zeroed by (rewrite wa_unsigned by lia; lia). symmetry. apply nth_error_repeat. exact Hi.
Qed.

#[using="Hold Hon Holdhi Ha0 Hnn Hahi DISJ"] Lemma wr_at_move_new : (forall i, (0 <= i < on)%Z -> m (wa (old + i)) <> None) -> wr_at segs m' a nn.
Proof.
intros Hm. split; [lia|]. split; [lia|]. intros i Hi. unfold wview.
destruct (Z.ltb_spec0 i on).
- rewrite move_copied by (rewrite wa_unsigned by lia; lia). rewrite wa_unsigned by lia.
replace (old + (a + i - a))%Z with (old + i)%Z by lia.
destruct (m (wa (old + i))) eqn:E; [discriminate|]. exfalso. exact (Hm i ltac:(lia) E).
- rewrite move_zeroed by (rewrite wa_unsigned by lia; lia). discriminate.
Qed.

End Move.

End MemEffects.

Lemma rw_cells_wr_at : forall segs m A cs n,
rw_cells segs m A cs -> (n <= Z.of_nat (cells_size cs))%Z -> wr_at segs m A n.
Proof. intros segs m A cs n [_ (H0 & H1 & H)] Hn. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia. Qed.

Lemma rw_cells_bytes_at : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.

Lemma ro_cells_bytes_at : forall segs m A cs, ro_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [_ H]. exact H. Qed.

Ltac at_node_solve :=
at_node_red; split_spine;
first [ reflexivity | lia | assumption
| symmetry; apply Z_to_bv_bv_unsigned
| lazymatch goal with
| |- wr_at ?segs ?m ?A ?n =>
match goal with H : rw_cells segs m A ?cs |- _ =>
apply (rw_cells_wr_at segs m A cs n H); cbn [cells_size csize]; lia end
| |- bytes_at ?segs ?m ?A ?bs =>
match goal with
| H : rw_cells segs m A ?cs |- _ =>
apply (bytes_at_ext segs m A _ bs (rw_cells_bytes_at segs m A cs H));
cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
| H : ro_cells segs m A ?cs |- _ =>
apply (bytes_at_ext segs m A _ bs (ro_cells_bytes_at segs m A cs H));
cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
end
end
| idtac ].

Ltac sys_mem_write :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (Z_to_bv 64 ?B) ?bs) ?ro) =>
change (write_to_mem m (Z_to_bv 64 B) bs) with (write_to_mem m (wa B) bs);
lazymatch goal with
| H : rw_cells segs m B [CB ?n ?junk] |- _ =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m B _ H) as HB; cbn [cells_size csize Nat.add] in HB;
(try lazymatch goal with
| HI : mem_inv segs m |- _ =>
let HI' := fresh "MI" in
pose proof (mem_inv_syswrite segs m B n junk bs HI H ltac:(lia)) as HI'; clear HI; rename HI' into HI
end);
let H' := fresh "DST" in
pose proof (rw_cells_CB_prefix_write segs m B n junk bs H ltac:(lia)) as H';
clear H;
transport_chunks segs m B bs;
footprint_after_store segs m B bs;
let m' := fresh "m" in
remember (write_to_mem m (wa B) bs) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; rename H' into H
| _ => fail "sys_mem_write: no hypothesis rw_cells" segs m B "[CB _ _]"
end
end.

Lemma apply_mem_zeros : forall m z, apply_writes (apply_zeros (apply_unmaps m []) [z]) [] = apply_zeros m [z].
Proof. reflexivity. Qed.
Lemma apply_mem_unmaps : forall m u, apply_writes (apply_zeros (apply_unmaps m [u]) []) [] = apply_unmaps m [u].
Proof. reflexivity. Qed.

Ltac transport_zeros segs m a n Ha Hn Han :=
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_zeros_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_zeros segs m a n Ha Hn Han A2 n2) in H
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
| H : stk segs m ?lo ?hi |- _ => apply (stk_zeros segs m a n Ha Hn Han lo hi) in H
| H : munch ?W ?m0 m |- _ =>
first [ apply (munch_zeros m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
| fail 100 "zero-filled range not inside the declared footprint" ]
| H : wmono segs ?m0 m |- _ => apply (wmono_zeros segs m a n Ha Hn Han m0) in H
| H : mem_inv segs m |- _ =>
let H' := fresh "MI" in
assert (H' : mem_inv segs (apply_zeros m [(wa a, Z_to_bv 64 n)]))
by (apply (mem_inv_zeros segs m a n Ha Hn Han H); first [assumption | intros; shelve]);
clear H
end.

Ltac transport_unmaps segs m a n Ha Hn Han :=
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_unmaps_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ =>
first [ apply (wr_at_unmaps_other segs m a n Ha Hn Han A2 n2) in H; [|slia]
| idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
| H : stk segs m ?lo ?hi |- _ =>
first [ apply (stk_unmaps_other segs m a n Ha Hn Han lo hi) in H; [|slia]
| idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
| H : munch ?W ?m0 m |- _ =>
first [ apply (munch_unmaps m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
| fail 100 "unmapped range not inside the declared footprint" ]
| H : wmono segs ?m0 m |- _ => idtac "note: dropping wmono (not preserved by an unmap):" H; clear H
| H : mem_inv segs m |- _ => apply (mem_inv_unmaps segs m a n Ha Hn Han) in H
end.

Ltac sys_mem_zeros :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (apply_zeros ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
change (apply_zeros m [(A, Z_to_bv 64 n)]) with (apply_zeros m [(wa a, Z_to_bv 64 n)]);
let Ha := fresh "Hza" in let Hn := fresh "Hzn" in let Han := fresh "Hzan" in
assert (Ha : (0 <= a < 2^64)%Z) by lia;
assert (Hn : (0 <= n < 2^64)%Z) by lia;
assert (Han : (a + n <= 2^64)%Z) by lia;
transport_zeros segs m a n Ha Hn Han;
let Z' := fresh "ZNEW" in
pose proof (rw_cells_zeros_new segs m a n Ha Hn Han) as Z';
let m' := fresh "m" in
remember (apply_zeros m [(wa a, Z_to_bv 64 n)]) as m' eqn:Heqm;
clear Heqm Ha Hn Han; try clear m
end.

Ltac sys_mem_unmaps :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (apply_unmaps ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
change (apply_unmaps m [(A, Z_to_bv 64 n)]) with (apply_unmaps m [(wa a, Z_to_bv 64 n)]);
let Ha := fresh "Hua" in let Hn := fresh "Hun" in let Han := fresh "Huan" in
assert (Ha : (0 <= a < 2^64)%Z) by lia;
assert (Hn : (0 <= n < 2^64)%Z) by lia;
assert (Han : (a + n <= 2^64)%Z) by lia;
transport_unmaps segs m a n Ha Hn Han;
let m' := fresh "m" in
remember (apply_unmaps m [(wa a, Z_to_bv 64 n)]) as m' eqn:Heqm;
clear Heqm Ha Hn Han; try clear m
end.

Ltac sys_nret :=
rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
(lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
let p' := eval vm_compute in (p + 4)%Z in
replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
| _ => idtac
end);
first [ rewrite apply_mem_none
| rewrite apply_mem_delivered; sys_mem_write
| rewrite apply_mem_write; sys_mem_write
| rewrite apply_mem_zeros; sys_mem_zeros
| rewrite apply_mem_unmaps; sys_mem_unmaps
| idtac ]. Ltac mkr__sys_nret_1 := rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
(lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
let p' := eval vm_compute in (p + 4)%Z in
replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
| _ => idtac
end);
first [ rewrite apply_mem_none
| rewrite apply_mem_delivered; sys_mem_write
| rewrite apply_mem_write; sys_mem_write
| rewrite apply_mem_zeros; sys_mem_zeros
| rewrite apply_mem_unmaps; sys_mem_unmaps
| idtac ].

Notation errno_addr tp := (bv_unsigned tp + (-164))%Z (only parsing).

Definition sysret_val (r : word) : word :=
match errno_of r with Some _ => Z_to_bv 64 (-1) | None => r end.
Definition sysret_errno (r errv : word) : word :=
match errno_of r with Some e => Z_to_bv 64 e | None => errv end.

Lemma errno_of_big : forall r, (2^64 - 4096 < bv_unsigned r)%Z -> errno_of r = Some (2^64 - bv_unsigned r)%Z.
Proof. intros r H. unfold errno_of. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [reflexivity|lia]. Qed.

Lemma negw_errno : forall u, (2^64 - 4096 < u < 2^64)%Z -> bv_swrap 32 (0 - u) = (2^64 - u)%Z.
Proof.
intros u Hu. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
replace (0 - u + 2^31)%Z with ((2^64 - u + 2^31) + (- 2^32) * 2^32)%Z by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma swrap32_small : forall z, (-2^31 <= z < 2^31)%Z -> bv_swrap 32 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
rewrite Z.mod_small by lia. lia.
Qed.

Lemma swrap32_high : forall u, (2^64 - 2^31 <= u < 2^64)%Z -> bv_swrap 32 u = (u - 2^64)%Z.
Proof.
intros u Hu. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
replace (u + 2^31)%Z with ((u - 2^64 + 2^31) + 2^32 * 2^32)%Z by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma unsigned_errno_ret : forall e, (1 <= e <= 4095)%Z -> bv_unsigned (errno_ret e) = (2^64 - e)%Z.
Proof. intros. rewrite errno_ret_unsigned by lia. reflexivity. Qed.

Lemma Z_to_bv_minus_mod : forall z, Z_to_bv 64 (z - 2^64) = Z_to_bv 64 z.
Proof.
intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
replace (z - 2^64)%Z with (z + (-1) * 2^64)%Z by lia. apply Z.mod_add. lia.
Qed.

Lemma errno_ret_fold : forall e, Z_to_bv 64 (- e) = errno_ret e.
Proof. reflexivity. Qed.

Lemma sextw_errno : forall e, (1 <= e <= 2^31)%Z ->
Z_to_bv 64 (bv_swrap 32 (bv_unsigned (errno_ret e) + 0)) = errno_ret e.
Proof.
intros e He. unfold errno_ret. rewrite unsigned_lit_wrap.
replace ((- e) mod 2^64)%Z with (2^64 - e)%Z.
2:{ replace (-e)%Z with ((2^64 - e) + (-1) * 2^64)%Z by lia. rewrite Z.mod_add; [|lia]. rewrite Z.mod_small; [reflexivity|lia]. }
rewrite Z.add_0_r, swrap32_high by lia. f_equal. lia.
Qed.

Lemma sextw_small : forall z, (0 <= z < 2^31)%Z ->
Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + 0)) = Z_to_bv 64 z.
Proof. intros z Hz. rewrite unsigned_lit by lia. rewrite Z.add_0_r, swrap32_small by lia. reflexivity. Qed.

Lemma stk_lo_nonneg : forall segs m lo hi, stk segs m lo hi -> (0 <= lo)%Z.
Proof. intros segs m lo hi (H & _). exact H. Qed.

Ltac name_sp sp k :=
let sp1 := fresh "sp" in let E := fresh "Esp" in let H := fresh "Hsp" in
remember (Z_to_bv 64 (bv_unsigned sp + k)) as sp1 eqn:E;
assert (H : bv_unsigned sp1 = (bv_unsigned sp + k)%Z)
by (rewrite E; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *;
try match goal with ST : stk _ _ _ _ |- _ => pose proof (stk_lo_nonneg _ _ _ _ ST) end;
apply unsigned_lit; lia).

Ltac unname_sp :=
match goal with
| H : bv_unsigned ?sp1 = (bv_unsigned ?sp + ?k)%Z, E : ?sp1' = Z_to_bv 64 (bv_unsigned ?sp + ?k) |- _ =>
constr_eq sp1 sp1'; rewrite ?H in *; clear H; subst sp1
end.

Tactic Notation "call_sp" uconstr(SPEC) :=
lazymatch goal with
| |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
name_sp sp k; call SPEC; unname_sp
| |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
name_sp sp k; call SPEC; unname_sp
| _ => call SPEC
end.

Ltac sys_finish :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
hnf;
repeat (lazymatch goal with |- ex _ => eexists end);
lazymatch goal with
| |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
| |- _ = _ => cbv delta [mkR]; reflexivity
end;
repeat match goal with |- _ /\ _ => split end; try assumption.

Lemma impl_from_evt : forall {node : Type} segs (atn : node -> machine_state -> Prop) {R} (t : itree node R) Q ms,
evt segs (fun ms' => impl segs atn t Q ms') ms -> impl segs atn t Q ms.
Proof. intros node segs atn R t Q ms H. eapply impl_evt; [exact H|]. intros ms' H'; exact H'. Qed.

Ltac iprefix := apply impl_from_evt.
Ltac ihere := apply evt_done.

Tactic Notation "icall" uconstr(SPEC) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
first [ eapply SPEC
| eapply impl_epost_mono; [ eapply SPEC | ] ].

Ltac ipost segs :=
let a := fresh "ans" in let ms' := fresh "ms'" in let PO := fresh "POST" in
intros a ms' PO;
destruct_exs PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
destruct PO as [E [MUc [WMc PO]]];
first [ destruct PO as [MIc PO] | rename PO into MIc ];
subst ms';
lazymatch type of MUc with
| munch _ ?m ?m' =>
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try destruct_ands PO;
try (let MIname := fresh "MI" in
lazymatch goal with H : mem_inv segs _ |- _ => rename H into MIname; try rename MIname into MI end);

repeat match goal with
| |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Export QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
Import ListNotations.
Open Scope bv_scope.

Lemma carry_sym : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
((x + y) mod 18446744073709551616 <? x)%Z = ((x + y) mod 18446744073709551616 <? y)%Z.
Proof.
intros x y Hx Hy. change 18446744073709551616%Z with (2^64)%Z.
destruct (Z.lt_ge_cases (x + y) (2^64)).
- rewrite Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
- rewrite <- (Z.mod_add _ (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
Qed.
Lemma carry_sym' : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
((y + x) mod 18446744073709551616 <? x)%Z = ((x + y) mod 18446744073709551616 <? x)%Z.
Proof. intros. rewrite Z.add_comm. reflexivity. Qed.

Ltac zeq :=
first
[ reflexivity
| lazymatch goal with

| |- Z.lor ?a ?b = Z.lor _ _ => first [ f_equal; zeq | rewrite (Z.lor_comm a b); f_equal; zeq ]
| |- Z.land ?a ?b = Z.land _ _ => first [ f_equal; zeq | rewrite (Z.land_comm a b); f_equal; zeq ]
| |- Z.lxor ?a ?b = Z.lxor _ _ => first [ f_equal; zeq | rewrite (Z.lxor_comm a b); f_equal; zeq ]
| |- Z.add ?a ?b = Z.add _ _ => first [ f_equal; zeq | rewrite (Z.add_comm a b); f_equal; zeq ]
| |- Z.mul ?a ?b = Z.mul _ _ => first [ f_equal; zeq | rewrite (Z.mul_comm a b); f_equal; zeq ]

| |- Z.modulo _ ?m = Z.modulo _ ?m => f_equal; zeq
| |- Z.sub _ _ = Z.sub _ _ => f_equal; zeq
| |- Z.shiftr _ _ = Z.shiftr _ _ => f_equal; zeq
| |- Z.shiftl _ _ = Z.shiftl _ _ => f_equal; zeq
| |- Z.b2z _ = Z.b2z _ => f_equal; zeq
| |- (if ?c then _ else _) = (if ?d then _ else _) => replace d with c by (symmetry; zeq); f_equal; zeq

| |- Z.ltb ?a ?b = Z.ltb ?c ?d =>
first [ f_equal; zeq
| unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith ]
| |- Z.eqb ?a ?b = Z.eqb ?c ?d =>
first [ f_equal; zeq | rewrite (Z.eqb_sym a b); f_equal; zeq
| unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith ]
| |- Z.leb ?a ?b = Z.leb ?c ?d =>
first [ f_equal; zeq | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith ]
| |- negb _ = negb _ => f_equal; zeq
| |- @eq bool _ _ => zeq_boolarith
end
| lia ]

with unfold1 a := try (is_var a; cbv delta [a])

with zeq_boolarith :=
apply eq_true_iff_eq;
rewrite ?Bool.negb_true_iff, ?Z.ltb_lt, ?Z.eqb_eq, ?Z.leb_le, ?Z.ltb_ge, ?Z.eqb_neq, ?Z.leb_gt;
zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia.

Ltac zeq_fast :=
first
[ reflexivity
| lazymatch goal with
| |- Z.lor ?a ?b = Z.lor _ _ => first [ f_equal; zeq_fast | rewrite (Z.lor_comm a b); f_equal; zeq_fast ]
| |- Z.land ?a ?b = Z.land _ _ => first [ f_equal; zeq_fast | rewrite (Z.land_comm a b); f_equal; zeq_fast ]
| |- Z.lxor ?a ?b = Z.lxor _ _ => first [ f_equal; zeq_fast | rewrite (Z.lxor_comm a b); f_equal; zeq_fast ]
| |- Z.add ?a ?b = Z.add _ _ => first [ f_equal; zeq_fast | rewrite (Z.add_comm a b); f_equal; zeq_fast ]
| |- Z.mul ?a ?b = Z.mul _ _ => first [ f_equal; zeq_fast | rewrite (Z.mul_comm a b); f_equal; zeq_fast ]
| |- Z.modulo _ ?m = Z.modulo _ ?m => f_equal; zeq_fast
| |- Z.sub _ _ = Z.sub _ _ => f_equal; zeq_fast
| |- Z.shiftr _ _ = Z.shiftr _ _ => f_equal; zeq_fast
| |- Z.shiftl _ _ = Z.shiftl _ _ => f_equal; zeq_fast
| |- Z.b2z _ = Z.b2z _ => f_equal; zeq_fast
| |- (if ?c then _ else _) = (if ?d then _ else _) => replace d with c by (symmetry; zeq_fast); f_equal; zeq_fast
| |- Z.ltb ?a ?b = Z.ltb ?c ?d =>
first [ f_equal; zeq_fast
| unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
| |- Z.eqb ?a ?b = Z.eqb ?c ?d =>
first [ f_equal; zeq_fast | rewrite (Z.eqb_sym a b); f_equal; zeq_fast
| unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
| |- Z.leb ?a ?b = Z.leb ?c ?d =>
first [ f_equal; zeq_fast | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
| |- negb _ = negb _ => f_equal; zeq_fast
| |- @eq bool _ _ => zeq_boolarith_fast
end
| slim; lia ]
with zeq_boolarith_fast :=
apply eq_true_iff_eq;
rewrite ?Bool.negb_true_iff, ?Z.ltb_lt, ?Z.eqb_eq, ?Z.leb_le, ?Z.ltb_ge, ?Z.eqb_neq, ?Z.leb_gt;
slim; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia. Ltac mkr__zeq_fast_0 := first
[ reflexivity
| lazymatch goal with
| |- Z.lor ?a ?b = Z.lor _ _ => first [ f_equal; zeq_fast | rewrite (Z.lor_comm a b); f_equal; zeq_fast ]
| |- Z.land ?a ?b = Z.land _ _ => first [ f_equal; zeq_fast | rewrite (Z.land_comm a b); f_equal; zeq_fast ]
| |- Z.lxor ?a ?b = Z.lxor _ _ => first [ f_equal; zeq_fast | rewrite (Z.lxor_comm a b); f_equal; zeq_fast ]
| |- Z.add ?a ?b = Z.add _ _ => first [ f_equal; zeq_fast | rewrite (Z.add_comm a b); f_equal; zeq_fast ]
| |- Z.mul ?a ?b = Z.mul _ _ => first [ f_equal; zeq_fast | rewrite (Z.mul_comm a b); f_equal; zeq_fast ]
| |- Z.modulo _ ?m = Z.modulo _ ?m => f_equal; zeq_fast
| |- Z.sub _ _ = Z.sub _ _ => f_equal; zeq_fast
| |- Z.shiftr _ _ = Z.shiftr _ _ => f_equal; zeq_fast
| |- Z.shiftl _ _ = Z.shiftl _ _ => f_equal; zeq_fast
| |- Z.b2z _ = Z.b2z _ => f_equal; zeq_fast
| |- (if ?c then _ else _) = (if ?d then _ else _) => replace d with c by (symmetry; zeq_fast); f_equal; zeq_fast
| |- Z.ltb ?a ?b = Z.ltb ?c ?d =>
first [ f_equal; zeq_fast
| unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
| |- Z.eqb ?a ?b = Z.eqb ?c ?d =>
first [ f_equal; zeq_fast | rewrite (Z.eqb_sym a b); f_equal; zeq_fast
| unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
| |- Z.leb ?a ?b = Z.leb ?c ?d =>
first [ f_equal; zeq_fast | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
| |- negb _ = negb _ => f_equal; zeq_fast
| |- @eq bool _ _ => zeq_boolarith_fast
end
| slim; lia ].

Ltac getreg n :=
lazymatch goal with
| |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
let v := eval cbv beta iota delta [tget mkR] in (tget p R) in
lazymatch v with
| Some ?w => w
| _ => fail "getreg: register" n "not concrete"
end
end.

Ltac name_as_tac X e :=
set (X := e);
let RX := fresh "R" X in
first [ assert (RX : (0 <= X < 18446744073709551616)%Z) by (subst X; change (inr64 e); zrange)
| idtac "note: no range fact for" X ].
Tactic Notation "name_as" ident(X) constr(e) := name_as_tac X e.

Ltac name_reg_tac n X :=
let w := getreg n in
lazymatch w with
| Z_to_bv 64 ?e => name_as_tac X e
| _ => fail "name_reg: register" n "holds" w
end.
Tactic Notation "name_reg" constr(n) ident(X) := name_reg_tac n X.

Ltac model_reg_tac n X mexpr :=
let w := getreg n in
lazymatch w with
| Z_to_bv 64 ?e =>
first [ constr_eq e mexpr
| replace (Z_to_bv 64 e) with (Z_to_bv 64 mexpr)
by (first [ f_equal; zeq_fast
| rewrite Z_to_bv_land64; f_equal; zeq_fast
| f_equal; zeq
| rewrite Z_to_bv_land64; f_equal; zeq
| apply Z_to_bv_eqm; rewrite ?Z.mod_mod by lia; zeq
| apply Z_to_bv_eqm; slim; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia
| apply Z_to_bv_eqm; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia ]) ];
name_as_tac X mexpr
| _ => fail "model_reg: register" n "holds" w
end. Ltac mkr__model_reg_tac_1 n X mexpr := let w := getreg n in
lazymatch w with
| Z_to_bv 64 ?e =>
first [ constr_eq e mexpr
| replace (Z_to_bv 64 e) with (Z_to_bv 64 mexpr)
by (first [ f_equal; zeq_fast
| rewrite Z_to_bv_land64; f_equal; zeq_fast
| f_equal; zeq
| rewrite Z_to_bv_land64; f_equal; zeq
| apply Z_to_bv_eqm; rewrite ?Z.mod_mod by lia; zeq
| apply Z_to_bv_eqm; slim; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia
| apply Z_to_bv_eqm; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia ]) ];
name_as_tac X mexpr
| _ => fail "model_reg: register" n "holds" w
end.
Tactic Notation "model_reg" constr(n) ident(X) constr(mexpr) := model_reg_tac n X mexpr.

Lemma wrap64_lit : forall x, (x mod 2^64 = x mod 18446744073709551616)%Z.
Proof. reflexivity. Qed.

Ltac name_virtual_tac X e :=
set (X := e);
let EX := fresh "E" X in assert (EX : X = e) by reflexivity;
let RX := fresh "R" X in
first [ assert (RX : (0 <= X < 18446744073709551616)%Z) by (rewrite EX; change (inr64 e); zrange)
| idtac "note: no range fact for" X ].
Tactic Notation "name_virtual" ident(X) constr(e) := name_virtual_tac X e.
End Mq3.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).
Local Notation M64 := 18446744073709551616%Z.

Definition v4 (b0 b1 b2 b3 : byte) : Z :=
bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3.

Local Ltac br b := pose proof (byte_range b).

Lemma lw_u b0 b1 b2 b3 :
bv_unsigned (LW [b0;b1;b2;b3]) = v4 b0 b1 b2 b3 + (2^64 - 2^32) * (bv_unsigned b3 / 128).
Proof. rewrite lw_unsigned4. reflexivity. Qed.

Lemma lw_wrap32 b0 b1 b2 b3 : bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3])) = v4 b0 b1 b2 b3.
Proof.
rewrite lw_u, bv_wrap32_eq. br b0; br b1; br b2; br b3. unfold v4.
Z.div_mod_to_equations. lia.
Qed.

Lemma lw_mod32 b0 b1 b2 b3 : (bv_unsigned (LW [b0;b1;b2;b3])) mod 2^32 = v4 b0 b1 b2 b3.
Proof. rewrite <- bv_wrap32_eq. apply lw_wrap32. Qed.

Lemma swrap32_small x : 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros. rewrite bv_swrap32_eq. rewrite Z.mod_small; lia. Qed.
Lemma mod64_small x : 0 <= x < 2^64 -> x mod M64 = x.
Proof. intros. apply Z.mod_small. lia. Qed.
Lemma mod32_small x : 0 <= x < 2^32 -> x mod 2^32 = x.
Proof. intros. apply Z.mod_small. lia. Qed.

Lemma swrap32_mod32 x : (bv_swrap 32 x) mod 2^32 = x mod 2^32.
Proof. rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.

Lemma mod64_mod32 x : (x mod M64) mod 2^32 = x mod 2^32.
Proof. Z.div_mod_to_equations. lia. Qed.

Lemma lor_mod32 a b : (Z.lor a b) mod 2^32 = Z.lor (a mod 2^32) (b mod 2^32).
Proof. rewrite <- !Z.land_ones by lia. apply Z.land_lor_distr_l. Qed.

Lemma shl_mod32 x j : 0 <= j -> (Z.shiftl x j) mod 2^32 = ((x mod 2^32) * 2^j) mod 2^32.
Proof. intros. rewrite Z.shiftl_mul_pow2, <- Zmult_mod_idemp_l by lia. reflexivity. Qed.

Lemma le4_lit_of_mod32 z (bs : list byte) : length bs = 4%nat ->
(z mod M64) mod 2^32 = le_val (map bv_unsigned bs) -> le4 (Z_to_bv 64 z) = bs.
Proof.
intros Hl Hz. apply le4_of_mod32; [exact Hl|]. rewrite unsigned_lit_wrap. exact Hz.
Qed.
Lemma le1_lit_of_mod8 z (b : byte) :
(z mod M64) mod 2^8 = bv_unsigned b -> le1 (Z_to_bv 64 z) = [b].
Proof. intros Hz. apply le1_of_mod8. rewrite unsigned_lit_wrap. exact Hz. Qed.

Section merge.
Variables b0 b1 b2 b3 c0 c1 c2 c3 : byte.

#[using="Type"] Lemma lo24 : (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 24)) mod M64 mod 2^32 = bv_unsigned b3.
Proof.
rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
replace (_ / 2^24) with (bv_unsigned b3) by (Z.div_mod_to_equations; lia).
rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma lo16 : (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 16)) mod M64 mod 2^32 = bv_unsigned b2 + 256 * bv_unsigned b3.
Proof.
rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
replace (_ / 2^16) with (bv_unsigned b2 + 256 * bv_unsigned b3) by (Z.div_mod_to_equations; lia).
rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma lo8 : (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 8)) mod M64 mod 2^32 = bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3.
Proof.
rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
replace (_ / 2^8) with (bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3) by (Z.div_mod_to_equations; lia).
rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
Qed.

#[using="Type"] Lemma hi8 : (v4 c0 c1 c2 c3 * 2^8) mod 2^32 = 256 * bv_unsigned c0 + 65536 * bv_unsigned c1 + 16777216 * bv_unsigned c2.
Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma hi16 : (v4 c0 c1 c2 c3 * 2^16) mod 2^32 = 65536 * bv_unsigned c0 + 16777216 * bv_unsigned c1.
Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma hi24 : (v4 c0 c1 c2 c3 * 2^24) mod 2^32 = 16777216 * bv_unsigned c0.
Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.

#[using="Type"] Lemma hi_a j : 0 <= j -> ((bv_swrap 32 (Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) j)) mod M64) mod 2^32 = (v4 c0 c1 c2 c3 * 2^j) mod 2^32.
Proof. intros. rewrite mod64_mod32, swrap32_mod32, shl_mod32, lw_mod32 by lia. reflexivity. Qed.
#[using="Type"] Lemma hi_r j : 0 <= j -> ((Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) j) mod M64) mod 2^32 = (v4 c0 c1 c2 c3 * 2^j) mod 2^32.
Proof. intros. rewrite mod64_mod32, shl_mod32, lw_mod32 by lia. reflexivity. Qed.

Local Ltac merge_tac lo hi hik k :=
apply le4_lit_of_mod32; [reflexivity|];
rewrite mod64_mod32, lor_mod32, lo, hi, hik by lia; cbn [map le_val];
br b0; br b1; br b2; br b3; br c0; br c1; br c2; br c3;
first [ rewrite (lor_add' _ _ k); [ lia | lia | lia | Z.div_mod_to_equations; lia ]
| rewrite (lor_add _ _ k); [ lia | lia | lia | Z.div_mod_to_equations; lia ] ].

#[using="Type"] Lemma merge_a24 :
le4 (Z_to_bv 64 (Z.lor ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 24)) mod M64)
((bv_swrap 32 (Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 8)) mod M64)))
= [b3; c0; c1; c2].
Proof. merge_tac lo24 hi_a hi8 8%Z. Qed.
#[using="Type"] Lemma merge_a16 :
le4 (Z_to_bv 64 (Z.lor ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 16)) mod M64)
((bv_swrap 32 (Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 16)) mod M64)))
= [b2; b3; c0; c1].
Proof. merge_tac lo16 hi_a hi16 16%Z. Qed.
#[using="Type"] Lemma merge_a8 :
le4 (Z_to_bv 64 (Z.lor ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 8)) mod M64)
((bv_swrap 32 (Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 24)) mod M64)))
= [b1; b2; b3; c0].
Proof. merge_tac lo8 hi_a hi24 24%Z. Qed.

#[using="Type"] Lemma merge_r24 :
le4 (Z_to_bv 64 (Z.lor ((Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 8) mod M64)
((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 24)) mod M64)))
= [b3; c0; c1; c2].
Proof. merge_tac lo24 hi_r hi8 8%Z. Qed.
#[using="Type"] Lemma merge_r16 :
le4 (Z_to_bv 64 (Z.lor ((Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 16) mod M64)
((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 16)) mod M64)))
= [b2; b3; c0; c1].
Proof. merge_tac lo16 hi_r hi16 16%Z. Qed.
#[using="Type"] Lemma merge_r8 :
le4 (Z_to_bv 64 (Z.lor ((Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 24) mod M64)
((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 8)) mod M64)))
= [b1; b2; b3; c0].
Proof. merge_tac lo8 hi_r hi24 24%Z. Qed.

#[using="Type"] Lemma lwb0 : le1 (LW [b0;b1;b2;b3]) = [b0].
Proof.
apply le1_of_mod8. rewrite lw_u. br b0; br b1; br b2; br b3. unfold v4.
Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma lwb1 : le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (LW [b0;b1;b2;b3])) 8)) = [b1].
Proof.
apply le1_lit_of_mod8. rewrite lw_u, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
replace (_ / 2^8) with (bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3 + (2^56 - 2^24) * (bv_unsigned b3 / 128))
by (Z.div_mod_to_equations; lia).
rewrite mod64_small by lia. Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma lwb2 : le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (LW [b0;b1;b2;b3])) 16)) = [b2].
Proof.
apply le1_lit_of_mod8. rewrite lw_u, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
replace (_ / 2^16) with (bv_unsigned b2 + 256 * bv_unsigned b3 + (2^48 - 2^16) * (bv_unsigned b3 / 128))
by (Z.div_mod_to_equations; lia).
rewrite mod64_small by lia. Z.div_mod_to_equations. lia.
Qed.
End merge.
