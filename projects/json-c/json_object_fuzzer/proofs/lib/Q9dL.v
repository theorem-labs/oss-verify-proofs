(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith Bool List Lia.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC QKJh Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Import stdpp.gmap.
Import QCiC.Mq0 QKJh Q6sh.Mq1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope aprog_scope.

Inductive mtail : Type := TRes | TNext (i : N).

Inductive bsent : Type := BSUndef | BSNull | BSLocal (r : Z) | BSHeap (i : N).

Record sentry : Type := mkSE { se_override : Z; se_level : Z; se_isolate : Z; se_isolate_level : Z }.

Section Bidi.
Context {ptr : Type}.
Variable TAB : ftables.
Variable fuel : nat.

#[local] Notation FM := (@FM ptr).
#[local] Notation get_prev := (@get_prev ptr).
#[local] Notation get_next := (@get_next ptr).
#[local] Notation get_pos := (@get_pos ptr).
#[local] Notation get_len := (@get_len ptr).
#[local] Notation get_type := (@get_type ptr).
#[local] Notation get_level := (@get_level ptr).
#[local] Notation get_iso := (@get_iso ptr).
#[local] Notation get_btype := (@get_btype ptr).
#[local] Notation get_previ := (@get_previ ptr).
#[local] Notation get_nexti := (@get_nexti ptr).
#[local] Notation set_prev := (@set_prev ptr).
#[local] Notation set_next := (@set_next ptr).
#[local] Notation set_pos := (@set_pos ptr).
#[local] Notation set_len := (@set_len ptr).
#[local] Notation set_type := (@set_type ptr).
#[local] Notation set_level := (@set_level ptr).
#[local] Notation set_iso := (@set_iso ptr).
#[local] Notation set_btype := (@set_btype ptr).
#[local] Notation set_previ := (@set_previ ptr).
#[local] Notation set_nexti := (@set_nexti ptr).
#[local] Notation ptr_eq := (@ptr_eq ptr).
#[local] Notation add32 := (@add32 ptr).
#[local] Notation sub32 := (@sub32 ptr).
#[local] Notation free_run := (@free_run ptr).
#[local] Notation new_run := (@new_run ptr).
#[local] Notation new_run_list := (@new_run_list ptr).
#[local] Notation free_run_list := (@free_run_list ptr fuel).
#[local] Notation shadow_run_list := (@shadow_run_list ptr fuel).
#[local] Notation run_list_encode_bidi_types := (@run_list_encode_bidi_types ptr fuel).

Definition lread {A} (l : list A) (d : A) (i : Z) : FM A :=
if in_range i (zlength l) then aret (znth d l i) else aunr.
Definition lwrite {A} (l : list A) (i : Z) (v : A) : FM (list A) :=
if in_range i (zlength l) then aret (zupd l i v) else aunr.

Definition oread {A} (l : list (option A)) (i : Z) : FM A :=
if in_range i (zlength l) then match znth None l i with Some v => aret v | None => aunr end else aunr.

Definition merge_with_prev (second : nref) : FM nref :=
first <- get_prev second ;;
sn <- get_next second ;;
set_next first sn ;;;
fn <- get_next first ;;
set_prev fn first ;;;
fl <- get_len first ;; sl <- get_len second ;; v <- add32 fl sl ;;
set_len first v ;;;
sni <- get_nexti second ;;
(if negb (is_null sni) then
spi <- get_previ second ;; set_previ sni spi
else
sn' <- get_next second ;;
x <- get_previ sn' ;;
e <- ptr_eq x second ;;
if e then spi <- get_previ second ;; set_previ sn' spi else aret tt) ;;;
spi <- get_previ second ;;
(if negb (is_null spi) then sni' <- get_nexti second ;; set_nexti spi sni' else aret tt) ;;;
sni'' <- get_nexti second ;;
set_nexti first sni'' ;;;
free_run second ;;;
aret first.

Definition compact_list (list : nref) : FM unit :=
ln <- get_next list ;;
if is_null ln then aret tt
else
aloop fuel (fun l : nref =>
t <- get_type l ;;
if t =? TY_SENTINEL then aret (inr tt)
else
pv <- get_prev l ;;
pt <- get_type pv ;;
c <- (if pt =? t then
pl <- get_level pv ;; ll <- get_level l ;;
if pl =? ll then
pil <- get_iso pv ;; il <- get_iso l ;;
if pil =? il then
bt <- get_btype l ;;
if bt =? NO_BRACKET then
pbt <- get_btype pv ;; aret (pbt =? NO_BRACKET)
else aret false
else aret false
else aret false
else aret false) ;;
l' <- (if c then merge_with_prev l else aret l) ;;
nx <- get_next l' ;;
aret (inl nx))
ln ;;;
aret tt.

Definition compact_neutrals (list : nref) : FM unit :=
ln <- get_next list ;;
if is_null ln then aret tt
else
aloop fuel (fun l : nref =>
t <- get_type l ;;
if t =? TY_SENTINEL then aret (inr tt)
else
pv <- get_prev l ;;
pl <- get_level pv ;; ll <- get_level l ;;
c <- (if pl =? ll then
pil <- get_iso pv ;; il <- get_iso l ;;
if pil =? il then
pt <- get_type pv ;;
if (pt =? t) || (IS_NEUTRAL pt && IS_NEUTRAL t) then
bt <- get_btype l ;;
if bt =? NO_BRACKET then
pbt <- get_btype pv ;; aret (pbt =? NO_BRACKET)
else aret false
else aret false
else aret false
else aret false) ;;
l' <- (if c then merge_with_prev l else aret l) ;;
nx <- get_next l' ;;
aret (inl nx))
ln ;;;
aret tt.

Definition get_adjacent_run (list : nref) (forward skip_neutral : bool) : FM nref :=
ppp0 <- (if forward then get_nexti list else get_previ list) ;;
if is_null ppp0 then aret NSent
else
aloop fuel (fun ppp : nref =>
if is_null ppp then aret (inr ppp)
else
ppp_type <- get_type ppp ;;
if ppp_type =? TY_SENTINEL then aret (inr ppp)
else
pil <- get_iso ppp ;; lil <- get_iso list ;;
if (lil <? pil) || (forward && (ppp_type =? TY_PDI))
|| (skip_neutral && negb (IS_STRONG ppp_type))
then
nxt <- (if forward then get_nexti ppp else get_previ ppp) ;;
aret (inl (if is_null nxt then NSent else nxt))
else aret (inr ppp))
ppp0.

Definition adj_type (chg : bool) (ppp pp : nref) : FM Z :=
al <- get_level ppp ;; l <- get_level pp ;;
if al =? l then t <- get_type ppp ;; aret (if chg then CHANGE_NUMBER_TO_RTL t else t)
else aret (LEVEL_TO_DIR (zmax al l)).

Definition pairing_nodes_push (nodes : pref) (open close : nref) : FM pref :=
r <- amalloc PNODE_SIZEOF ;;
match r with
| None => aret PNull
| Some p =>
i <- fresh_id ;;
s <- aget ;;
match (f_pnodes s) !! i with
| Some _ => aunr
| None =>
aput (set_pnodes (<[ i := mkPN p open close nodes ]> (f_pnodes s)) s) ;;;
aret (PNode i)
end
end.

Definition front_back_split (source : pref) : FM (pref * pref) :=
c <- (if pis_null source then aret true else n <- pget_next source ;; aret (pis_null n)) ;;
if c then aret (source, PNull)
else
pfast0 <- pget_next source ;;
pslow <- aloop fuel (fun st : pref * pref =>
let '(pfast, pslow) := st in
if pis_null pfast then aret (inr pslow)
else
pfast' <- pget_next pfast ;;
if pis_null pfast' then aret (inl (pfast', pslow))
else
pfast'' <- pget_next pfast' ;;
pslow' <- pget_next pslow ;;
aret (inl (pfast'', pslow')))
(pfast0, source) ;;
back <- pget_next pslow ;;
pset_next pslow PNull ;;;
aret (source, back).

Definition tail_store (tail : mtail) (res : pref) (v : pref) : FM pref :=
match tail with
| TRes => aret v
| TNext i => pset_next (PNode i) v ;;; aret res
end.
Definition tail_of (p : pref) : mtail := match p with PNode i => TNext i | PNull => TRes end.

Definition sorted_merge (nodes1 nodes2 : pref) : FM pref :=
'(res, tail, n1, n2) <-
aloop fuel (fun st : pref * mtail * pref * pref =>
let '(res, tail, n1, n2) := st in
if pis_null n1 || pis_null n2 then aret (inr (res, tail, n1, n2))
else
o1 <- pget_open n1 ;; p1 <- get_pos o1 ;;
o2 <- pget_open n2 ;; p2 <- get_pos o2 ;;
if p1 <? p2 then
res' <- tail_store tail res n1 ;;
n1' <- pget_next n1 ;;
aret (inl (res', tail_of n1, n1', n2))
else
res' <- tail_store tail res n2 ;;
n2' <- pget_next n2 ;;
aret (inl (res', tail_of n2, n1, n2')))
(PNull, TRes, nodes1, nodes2) ;;
tail_store tail res (if pis_null n1 then n2 else n1).

Definition SORT_DEPTH : nat := 64%nat.

Fixpoint sort_pairing_nodes (k : nat) (nodes : pref) : FM pref :=
match k with
| O => aunr
| S k' =>
c <- (if pis_null nodes then aret true else n <- pget_next nodes ;; aret (pis_null n)) ;;
if c then aret nodes
else
'(front, back) <- front_back_split nodes ;;
front' <- sort_pairing_nodes k' front ;;
back' <- sort_pairing_nodes k' back ;;
sorted_merge front' back'
end.

Definition free_pairing_nodes (nodes : pref) : FM unit :=
aloop fuel (fun n : pref =>
if pis_null n then aret (inr tt)
else nx <- pget_next n ;; pn_free n ;;; aret (inl nx))
nodes.

Definition ph_base_dir (main : nref) (pbase : Z) : FM (Z * Z) :=
let base_level := DIR_TO_LEVEL pbase in
if IS_STRONG pbase then aret (base_level, pbase)
else
pp0 <- get_next main ;;
aloop fuel (fun st : nref * Z =>
let '(pp, vic) := st in
t <- get_type pp ;;
if t =? TY_SENTINEL then aret (inr (base_level, pbase))
else if t =? TY_PDI then
(let vic' := if 0 <? vic then vic - 1 else vic in
nx <- get_next pp ;; aret (inl (nx, vic')))
else if IS_ISOLATE t then
(vic' <- add32 vic 1 ;; nx <- get_next pp ;; aret (inl (nx, vic')))
else if (vic =? 0) && IS_LETTER t then
(let bl := DIR_TO_LEVEL t in aret (inr (bl, LEVEL_TO_DIR bl)))
else (nx <- get_next pp ;; aret (inl (nx, vic))))
(pp0, 0).

Record xst : Type := mkX {
x_pp : nref; x_level : Z; x_override : Z; x_new_level : Z; x_iso : Z;
x_ss : Z; x_op : Z; x_vic : Z; x_iof : Z; x_stack : list (option sentry) }.

Definition x_with_pp (v : nref) (st : xst) : xst :=
mkX v (x_level st) (x_override st) (x_new_level st) (x_iso st) (x_ss st) (x_op st) (x_vic st) (x_iof st) (x_stack st).
Definition x_with_level (v : Z) (st : xst) : xst :=
mkX (x_pp st) v (x_override st) (x_new_level st) (x_iso st) (x_ss st) (x_op st) (x_vic st) (x_iof st) (x_stack st).
Definition x_with_override (v : Z) (st : xst) : xst :=
mkX (x_pp st) (x_level st) v (x_new_level st) (x_iso st) (x_ss st) (x_op st) (x_vic st) (x_iof st) (x_stack st).
Definition x_with_new_level (v : Z) (st : xst) : xst :=
mkX (x_pp st) (x_level st) (x_override st) v (x_iso st) (x_ss st) (x_op st) (x_vic st) (x_iof st) (x_stack st).
Definition x_with_iso (v : Z) (st : xst) : xst :=
mkX (x_pp st) (x_level st) (x_override st) (x_new_level st) v (x_ss st) (x_op st) (x_vic st) (x_iof st) (x_stack st).
Definition x_with_ss (v : Z) (st : xst) : xst :=
mkX (x_pp st) (x_level st) (x_override st) (x_new_level st) (x_iso st) v (x_op st) (x_vic st) (x_iof st) (x_stack st).
Definition x_with_op (v : Z) (st : xst) : xst :=
mkX (x_pp st) (x_level st) (x_override st) (x_new_level st) (x_iso st) (x_ss st) v (x_vic st) (x_iof st) (x_stack st).
Definition x_with_vic (v : Z) (st : xst) : xst :=
mkX (x_pp st) (x_level st) (x_override st) (x_new_level st) (x_iso st) (x_ss st) (x_op st) v (x_iof st) (x_stack st).
Definition x_with_iof (v : Z) (st : xst) : xst :=
mkX (x_pp st) (x_level st) (x_override st) (x_new_level st) (x_iso st) (x_ss st) (x_op st) (x_vic st) v (x_stack st).
Definition x_with_stack (v : list (option sentry)) (st : xst) : xst :=
mkX (x_pp st) (x_level st) (x_override st) (x_new_level st) (x_iso st) (x_ss st) (x_op st) (x_vic st) (x_iof st) v.

Definition push_status (st : xst) (new_level new_override isolate : Z) : FM xst :=
aassert ((0 <=? x_level st) && (x_level st <=? MAX_EXPLICIT_LEVEL)) ;;;
if (x_op st =? 0) && (x_iof st =? 0) && (new_level <=? MAX_EXPLICIT_LEVEL) then
stk <- lwrite (x_stack st) (x_ss st) (Some (mkSE (x_override st) (x_level st) isolate (x_iso st))) ;;
ss' <- add32 (x_ss st) 1 ;;
aret (x_with_override new_override (x_with_level new_level (x_with_ss ss' (x_with_stack stk st))))
else if x_iof st =? 0 then
op' <- add32 (x_op st) 1 ;;
aret (x_with_op op' st)
else aret st.

Definition pop_status (st : xst) : FM xst :=
if negb (x_ss st =? 0) then
(if 0 <? x_op st then aret (x_with_op (x_op st - 1) st)
else
let ss' := x_ss st - 1 in
e <- oread (x_stack st) ss' ;;
aret (x_with_level (se_level e) (x_with_override (se_override e)
(x_with_iso (se_isolate_level e) (x_with_ss ss' st)))))
else aret st.

Definition top_is_isolate (st : xst) : FM bool :=
if x_ss st =? 0 then aret false
else e <- oread (x_stack st) (x_ss st - 1) ;; aret (negb (se_isolate e =? 0)).

Definition fsi_scan (pp : nref) (vic : Z) : FM Z :=
f0 <- get_next pp ;;
aloop fuel (fun st : nref * Z =>
let '(fp, ic) := st in
t <- get_type fp ;;
if t =? TY_SENTINEL then aret (inr 0)
else if t =? TY_PDI then
(ic' <- sub32 ic 1 ;;
if vic <? 0 then aret (inr 0)
else nx <- get_next fp ;; aret (inl (nx, ic')))
else if IS_ISOLATE t then
(ic' <- add32 ic 1 ;; nx <- get_next fp ;; aret (inl (nx, ic')))
else if (ic =? 0) && IS_LETTER t then aret (inr (DIR_TO_LEVEL t))
else (nx <- get_next fp ;; aret (inl (nx, ic))))
(f0, 0).

Definition delete_node (x : nref) : FM unit :=
xp <- get_prev x ;; xn <- get_next x ;; set_next xp xn ;;;
xn' <- get_next x ;; xp' <- get_prev x ;; set_prev xn' xp'.
Definition insert_node_before (x list : nref) : FM unit :=
lp <- get_prev list ;; set_prev x lp ;;;
lp' <- get_prev list ;; set_next lp' x ;;;
set_next x list ;;;
set_prev list x.
Definition move_node_before (x list : nref) : FM unit :=
xp <- get_prev x ;;
(if is_null xp then aret tt else delete_node x) ;;;
insert_node_before x list.

Definition x_new_level_explicit (level this_type : Z) : FM Z :=
aassert ((0 <=? level) && (level <=? MAX_EXPLICIT_LEVEL)) ;;;
let d := DIR_TO_LEVEL this_type in
let v := Z.land (level + d + 2) (-2) - d in
if in_s8 v then aret v else aunr.

Definition x_new_level_isolate (level : Z) (rtl : bool) : FM Z :=
aassert ((0 <=? level) && (level <=? MAX_EXPLICIT_LEVEL)) ;;;
let v := if rtl then level + 1 + Z.rem level 2 else level + 2 - Z.rem level 2 in
if in_s8 v then aret v else aunr.

Definition x_explicit_pushes (st : xst) (this_type new_override n : Z) : FM xst :=
aloop fuel (fun s : Z * xst =>
let '(i, st) := s in
if i =? 0 then aret (inr st)
else
nl <- x_new_level_explicit (x_level st) this_type ;;
st' <- push_status (x_with_new_level nl st) nl new_override 0 ;;
i' <- sub32 i 1 ;;
aret (inl (i', st')))
(n, st).

Definition x_pdf_pops (st : xst) (n : Z) : FM xst :=
aloop fuel (fun s : Z * xst =>
let '(i, st) := s in
if i =? 0 then aret (inr st)
else
b <- top_is_isolate st ;;
if b then aret (inr st)
else
st' <- pop_status st ;;
i' <- sub32 i 1 ;;
aret (inl (i', st')))
(n, st).

Definition x_pop_to_isolate (st : xst) : FM xst :=
aloop fuel (fun st : xst =>
if x_ss st =? 0 then aret (inr st)
else
b <- top_is_isolate st ;;
if b then aret (inr st)
else st' <- pop_status st ;; aret (inl st'))
st.

Definition x_pdi_loop (st : xst) (n : Z) : FM xst :=
aloop fuel (fun s : Z * xst =>
let '(i, st) := s in
if i =? 0 then aret (inr st)
else
let pp := x_pp st in
st' <- (if 0 <? x_iof st then
set_level pp (x_level st) ;;;
aret (x_with_iof (x_iof st - 1) st)
else if 0 <? x_vic st then
st1 <- x_pop_to_isolate st ;;
st2 <- pop_status (x_with_op 0 st1) ;;
let st3 := if 0 <? x_iso st2 then x_with_iso (x_iso st2 - 1) st2 else st2 in
let st4 := x_with_vic (x_vic st3 - 1) st3 in
set_level pp (x_level st4) ;;;
set_iso pp (x_iso st4) ;;;
aret st4
else
set_type pp TY_ON ;;;
set_level pp (x_level st) ;;;
aret st) ;;
i' <- sub32 i 1 ;;
aret (inl (i', st')))
(n, st).

Definition x_body (explicits : nref) (st : xst) : FM (xst + xst) :=
let pp := x_pp st in
this_type <- get_type pp ;;
set_iso pp (x_iso st) ;;;
if IS_EXPLICIT_OR_BN this_type then
st1 <- (if IS_STRONG this_type then
n <- get_len pp ;;
x_explicit_pushes st this_type (EXPLICIT_TO_OVERRIDE_DIR this_type) n
else if this_type =? TY_PDF then
n <- get_len pp ;;
x_pdf_pops st n
else aret st) ;;
set_level pp (-1) ;;;
nx <- get_next pp ;;
move_node_before pp explicits ;;;
aret (inl (x_with_pp nx st1))
else if this_type =? TY_PDI then
n <- get_len pp ;;
st1 <- x_pdi_loop st n ;;
nx <- get_next pp ;;
aret (inl (x_with_pp nx st1))
else if IS_ISOLATE this_type then
let new_override := TY_ON in
nl <- (if this_type =? TY_LRI then x_new_level_isolate (x_level st) false
else if this_type =? TY_RLI then x_new_level_isolate (x_level st) true
else if this_type =? TY_FSI then
fb <- fsi_scan pp (x_vic st) ;;
x_new_level_isolate (x_level st) (LEVEL_IS_RTL fb)
else aret (x_new_level st)) ;;
let st1 := x_with_new_level nl st in
set_level pp (x_level st1) ;;;
set_iso pp (x_iso st1) ;;;
let st2 := if x_iso st1 <? MAX_EXPLICIT_LEVEL - 1 then x_with_iso (x_iso st1 + 1) st1 else st1 in
(if negb (IS_NEUTRAL (x_override st2)) then set_type pp (x_override st2) else aret tt) ;;;
st3 <- (if nl <=? MAX_EXPLICIT_LEVEL then
vic' <- add32 (x_vic st2) 1 ;;
st' <- push_status (x_with_vic vic' st2) nl new_override 1 ;;
aret (x_with_level nl st')
else
iof' <- add32 (x_iof st2) 1 ;;
aret (x_with_iof iof' st2)) ;;
nx <- get_next pp ;;
aret (inl (x_with_pp nx st3))
else if this_type =? TY_BS then aret (inr st)
else
set_level pp (x_level st) ;;;
(if negb (IS_NEUTRAL (x_override st)) then set_type pp (x_override st) else aret tt) ;;;
nx <- get_next pp ;;
aret (inl (x_with_pp nx st)).

Definition ph_chains (main : nref) : FM unit :=
pp0 <- get_next main ;;
aloop fuel (fun st : nref * Z * list nref =>
let '(pp, prev, rpil) := st in
t <- get_type pp ;;
if t =? TY_SENTINEL then aret (inr tt)
else
il <- get_iso pp ;;
rpil <- (if il <? prev then
(if (0 <=? il + 1) && (prev + 1 <=? zlength rpil)
then aret (zfill rpil (il + 1) (prev - il) NNull) else aunr)
else aret rpil) ;;
let prev := il in
cur <- lread rpil NNull il ;;
(if negb (is_null cur) then set_nexti cur pp ;;; set_previ pp cur else aret tt) ;;;
rpil <- lwrite rpil il pp ;;
nx <- get_next pp ;;
aret (inl (nx, prev, rpil)))
(pp0, 0, zrepeat NNull MAX_RESOLVED_LEVELS) ;;;
aret tt.

Definition ph_explicit (main explicits : nref) (base_level : Z) : FM unit :=
pp0 <- get_next main ;;
let st0 := mkX pp0 base_level TY_ON 0 0 0 0 0 0 (zrepeat None MAX_RESOLVED_LEVELS) in
aloop fuel (fun st : xst =>
t <- get_type (x_pp st) ;;
if t =? TY_SENTINEL then aret (inr tt)
else
r <- x_body explicits st ;;
match r with
| inl st' => aret (inl st')
| inr _ => aret (inr tt)
end)
st0 ;;;
ph_chains main.

Definition ph_weak_a (main : nref) (base_dir : Z) : FM (Z * list (option Z)) :=
pp0 <- get_next main ;;
aloop fuel (fun st : nref * Z * list (option Z) =>
let '(pp, max_iso, lss) := st in
t <- get_type pp ;;
if t =? TY_SENTINEL then aret (inr (max_iso, lss))
else
ppp_prev <- get_adjacent_run pp false false ;;
ppp_next <- get_adjacent_run pp true false ;;
this_type <- get_type pp ;;
iso_level <- get_iso pp ;;
let max_iso := if max_iso <? iso_level then iso_level else max_iso in
prev_type <- adj_type false ppp_prev pp ;;
next_type <- adj_type false ppp_next pp ;;
lss <- (if IS_STRONG prev_type then lwrite lss iso_level (Some prev_type) else aret lss) ;;
if this_type =? TY_NSM then
(pv <- get_prev pp ;; pvt <- get_type pv ;;
(if IS_ISOLATE pvt then set_type pp TY_ON else aret tt) ;;;
al <- get_level ppp_prev ;; l <- get_level pp ;;
pp <- (if al =? l then
pv' <- get_prev pp ;; e <- ptr_eq ppp_prev pv' ;;
if e then merge_with_prev pp else aret pp
else set_type pp prev_type ;;; aret pp) ;;
pp <- (if prev_type =? next_type then
l' <- get_level pp ;; nx <- get_next pp ;; nl <- get_level nx ;;
if l' =? nl then
nx' <- get_next pp ;; e <- ptr_eq ppp_next nx' ;;
if e then (nx'' <- get_next pp ;; merge_with_prev nx'') else aret pp
else aret pp
else aret pp) ;;
nxt <- get_next pp ;;
aret (inl (nxt, max_iso, lss)))
else
(c <- (if this_type =? TY_EN then v <- oread lss iso_level ;; aret (v =? TY_AL) else aret false) ;;
(if c then
set_type pp TY_AN ;;;
(if next_type =? TY_NSM then set_type ppp_next TY_AN else aret tt)
else aret tt) ;;;
nxt <- get_next pp ;;
aret (inl (nxt, max_iso, lss))))
(pp0, 0, zupd (zrepeat None MAX_RESOLVED_LEVELS) 0 (Some base_dir)).

Definition ph_weak_b (main : nref) (base_dir : Z) (lss0 : list (option Z)) : FM unit :=
pp0 <- get_next main ;;
aloop fuel (fun st : nref * bool * Z * list (option Z) =>
let '(pp, w4, pto, lss) := st in
this_type <- get_type pp ;;
if this_type =? TY_SENTINEL then aret (inr tt)
else
iso_level <- get_iso pp ;;
ppp_prev <- get_adjacent_run pp false false ;;
ppp_next <- get_adjacent_run pp true false ;;
prev_type <- adj_type false ppp_prev pp ;;
next_type <- adj_type false ppp_next pp ;;
lss <- (if IS_STRONG prev_type then lwrite lss iso_level (Some prev_type) else aret lss) ;;
if this_type =? TY_AL then
(set_type pp TY_RTL ;;;
nxt <- get_next pp ;;
aret (inl (nxt, true, TY_ON, lss)))
else
(c4 <- (if w4 then
ln <- get_len pp ;;
aret ((ln =? 1) && IS_ES_OR_CS this_type && IS_NUMBER pto && (pto =? next_type)
&& ((pto =? TY_EN) || (this_type =? TY_CS)))
else aret false) ;;
this_type <- (if c4 then set_type pp prev_type ;;; get_type pp else aret this_type) ;;
let w4 := true in
'(this_type, w4) <- (if (this_type =? TY_ET) && ((pto =? TY_EN) || (next_type =? TY_EN))
then set_type pp TY_EN ;;; t' <- get_type pp ;; aret (t', false)
else aret (this_type, w4)) ;;
(if IS_NUMBER_SEPARATOR_OR_TERMINATOR this_type then set_type pp TY_ON else aret tt) ;;;
c7 <- (if this_type =? TY_EN then v <- oread lss iso_level ;; aret (v =? TY_LTR) else aret false) ;;
pto <- (if c7 then
set_type pp TY_LTR ;;;
l <- get_level pp ;; nx <- get_next pp ;; nl <- get_level nx ;;
aret (if l =? nl then TY_EN else TY_ON)
else
nx <- get_next pp ;;
np <- get_prev nx ;; npl <- get_level np ;; nl <- get_level nx ;;
if npl =? nl then (np' <- get_prev nx ;; get_type np')
else aret (LEVEL_TO_DIR (zmax npl nl))) ;;
nxt <- get_next pp ;;
aret (inl (nxt, w4, pto, lss))))
(pp0, true, TY_ON, zupd lss0 0 (Some base_dir)) ;;;
aret tt.

Definition bs_read (bstack : list bsent) (lbs : list (option nref)) (iso k : Z) : FM nref :=
e <- lread bstack BSUndef iso ;;
match e with
| BSLocal r => oread lbs (r * LOCAL_BRACKET_SIZE + k)
| BSHeap i =>
s <- aget ;;
match (f_rows s) !! i with
| Some row => oread (row_cells row) k
| None => aunr
end
| _ => aunr
end.

Definition bs_write (bstack : list bsent) (lbs : list (option nref)) (iso k : Z) (v : nref)
: FM (list (option nref)) :=
e <- lread bstack BSUndef iso ;;
match e with
| BSLocal r => lwrite lbs (r * LOCAL_BRACKET_SIZE + k) (Some v)
| BSHeap i =>
s <- aget ;;
match (f_rows s) !! i with
| Some row =>
cells <- lwrite (row_cells row) k (Some v) ;;
aput (set_rows (<[ i := mkRow (row_blk row) cells ]> (f_rows s)) s) ;;;
aret lbs
| None => aunr
end
| _ => aunr
end.

Definition n0_alloc_rows (num : Z) (bstack0 : list bsent) : FM (list bsent * bool) :=
aloop fuel (fun st : Z * list bsent =>
let '(iso, bstack) := st in
if negb (iso <? num) then aret (inr (bstack, false))
else
r <- amalloc ROW_SIZEOF ;;
match r with
| None =>
bstack <- lwrite bstack iso BSNull ;;
aret (inr (bstack, true))
| Some p =>
i <- fresh_id ;;
s <- aget ;;
match (f_rows s) !! i with
| Some _ => aunr
| None =>
aput (set_rows (<[ i := mkRow p (zrepeat None MAX_NESTED_BRACKET_PAIRS) ]> (f_rows s)) s) ;;;
bstack <- lwrite bstack iso (BSHeap i) ;;
aret (inl (iso + 1, bstack))
end
end)
(LOCAL_BRACKET_SIZE, bstack0).

Definition n0_st : Type := (nref * Z * Z * list (option Z) * list (option nref) * pref * bool)%type.

Definition n0_close_scan (bstack : list bsent) (lbs : list (option nref)) (bss : list (option Z))
(iso_level brack_prop : Z) (pp : nref) (pn : pref)
: FM (list (option Z) * pref * bool ) :=
sz <- oread bss iso_level ;;
aloop fuel (fun stack_idx : Z =>
if stack_idx <? 0 then aret (inr (bss, pn, false))
else
se <- bs_read bstack lbs iso_level stack_idx ;;
se_brack_prop <- get_btype se ;;
if BRACKET_ID se_brack_prop =? BRACKET_ID brack_prop then
(bss' <- lwrite bss iso_level (Some stack_idx) ;;
open <- bs_read bstack lbs iso_level stack_idx ;;
np <- pairing_nodes_push pn open pp ;;
if pis_null np then aret (inr (bss', pn, true))
else aret (inr (bss', np, false)))
else aret (inl (stack_idx - 1)))
(sz - 1).

Definition n0_pairs (main : nref) (bstack : list bsent) (bss0 : list (option Z)) (lbs0 : list (option nref)) (ok0 : bool)
: FM (pref * list (option Z) * list (option nref) * bool) :=
last_level0 <- get_level main ;;
pp0 <- get_next main ;;
aloop fuel (fun st : n0_st =>
let '(pp, last_level, last_iso, bss, lbs, pn, ok) := st in
t <- get_type pp ;;
if t =? TY_SENTINEL then aret (inr (pn, bss, lbs, ok))
else if negb ok then aret (inr (pn, bss, lbs, false))
else
level <- get_level pp ;;
iso_level <- get_iso pp ;;
brack_prop <- get_btype pp ;;
bss <- (if negb (level =? last_level) && (last_iso =? iso_level)
then lwrite bss last_iso (Some 0) else aret bss) ;;
t' <- get_type pp ;;
r <- (if negb (brack_prop =? NO_BRACKET) && (t' =? TY_ON) then
(if IS_BRACKET_OPEN brack_prop then
sz <- oread bss iso_level ;;
if sz =? MAX_NESTED_BRACKET_PAIRS then aret (inr (pn, bss, lbs, true))
else
lbs' <- bs_write bstack lbs iso_level sz pp ;;
bss' <- lwrite bss iso_level (Some (sz + 1)) ;;
aret (inl (bss', lbs', pn, true))
else
'(bss', pn', oom) <- n0_close_scan bstack lbs bss iso_level brack_prop pp pn ;;
aret (inl (bss', lbs, pn', negb oom)))
else aret (inl (bss, lbs, pn, true))) ;;
match r with
| inr res => aret (inr res)
| inl (bss, lbs, pn, ok) =>
nx <- get_next pp ;;
aret (inl (nx, level, iso_level, bss, lbs, pn, ok))
end)
(pp0, last_level0, 0, bss0, lbs0, PNull, ok0).

Definition AN_EN_AS_RTL (t : Z) : Z :=
if (t =? TY_AN) || (t =? TY_EN) || (t =? TY_RTL) then TY_RTL else t.

Definition imp_level (level this_type : Z) : Z :=
level + (if xorb (LEVEL_IS_RTL level) (IS_RTL this_type) then 1 else 0).
Definition dir_of_rem (x : Z) : Z := if Z.rem x 2 =? 0 then TY_LTR else TY_RTL.

Definition n0_set_pair (open close : nref) (v : Z) : FM unit :=
set_type close v ;;; set_type open v.

Definition n0_scan_b (open close : nref) (embedding_level : Z) : FM (option Z) :=
aloop fuel (fun ppn : nref =>
e <- ptr_eq ppn close ;;
if e then aret (inr None)
else
t <- get_type ppn ;;
let this_type := AN_EN_AS_RTL t in
l <- get_level ppn ;;
let this_level := imp_level l this_type in
if IS_STRONG this_type && (this_level =? embedding_level) then aret (inr (Some this_level))
else nx <- get_next ppn ;; aret (inl nx))
open.

Definition n0_scan_prec (open : nref) (embedding_level iso_level : Z) : FM Z :=
p0 <- get_prev open ;;
aloop fuel (fun ppn : nref =>
t <- get_type ppn ;;
if t =? TY_SENTINEL then aret (inr embedding_level)
else
let this_type := AN_EN_AS_RTL t in
il <- get_iso ppn ;;
if IS_STRONG this_type && (il =? iso_level) then
(l <- get_level ppn ;; aret (inr (imp_level l this_type)))
else pv <- get_prev ppn ;; aret (inl pv))
p0.

Definition n0_scan_c (open close : nref) (iso_level : Z) : FM bool :=
aloop fuel (fun ppn : nref =>
e <- ptr_eq ppn close ;;
if e then aret (inr false)
else
t <- get_type ppn ;;
let this_type := AN_EN_AS_RTL t in
il <- get_iso ppn ;;
if IS_STRONG this_type && (il =? iso_level) then aret (inr true)
else nx <- get_next ppn ;; aret (inl nx))
open.

Definition n0_resolve (pairing_nodes : pref) : FM unit :=
aloop fuel (fun ppairs : pref =>
if pis_null ppairs then aret (inr tt)
else
open <- pget_open ppairs ;;
embedding_level <- get_level open ;;
close <- pget_close ppairs ;;
fb <- n0_scan_b open close embedding_level ;;
(match fb with
| Some this_level => n0_set_pair open close (dir_of_rem this_level)
| None =>
iso_level <- get_iso open ;;
prec <- n0_scan_prec open embedding_level iso_level ;;
fc <- n0_scan_c open close iso_level ;;
if fc then n0_set_pair open close (dir_of_rem prec) else aret tt
end) ;;;
nx <- pget_next ppairs ;;
aret (inl nx))
pairing_nodes ;;;
aret tt.

Definition n0_free_rows (num : Z) (bstack : list bsent) : FM unit :=
if num <? LOCAL_BRACKET_SIZE then aret tt
else
aloop fuel (fun i : Z =>
if negb (i <? num) then aret (inr tt)
else
e <- lread bstack BSUndef i ;;
match e with
| BSHeap k =>
s <- aget ;;
match (f_rows s) !! k with
| Some row => aput (set_rows (delete k (f_rows s)) s) ;;; afree (row_blk row) ;;; aret (inl (i + 1))
| None => aunr
end
| BSNull => aret (inl (i + 1))
| _ => aunr
end)
LOCAL_BRACKET_SIZE ;;;
aret tt.

Definition n0_clear_btypes (main : nref) : FM unit :=
pp0 <- get_next main ;;
aloop fuel (fun pp : nref =>
t <- get_type pp ;;
if t =? TY_SENTINEL then aret (inr tt)
else set_btype pp NO_BRACKET ;;; nx <- get_next pp ;; aret (inl nx))
pp0 ;;;
aret tt.

Definition ph_n0 (main : nref) (max_iso_level : Z) : FM bool :=
aassert ((0 <=? max_iso_level) && (max_iso_level <? MAX_EXPLICIT_LEVEL)) ;;;
lv0 <- get_level main ;;
let num := max_iso_level + 1 in
let bstack0 := zrepeat BSNull num ++ zrepeat BSUndef (MAX_EXPLICIT_LEVEL - num) in
let bss0 := zrepeat (Some 0) num ++ zrepeat None (MAX_EXPLICIT_LEVEL - num) in
let bstack1 := map BSLocal (map Z.of_nat (seq 0 (Z.to_nat LOCAL_BRACKET_SIZE)))
++ skipn (Z.to_nat LOCAL_BRACKET_SIZE) bstack0 in
let lbs0 := zrepeat (@None nref) (MAX_EXPLICIT_LEVEL * LOCAL_BRACKET_SIZE) in
'(bstack, oom1) <- n0_alloc_rows num bstack1 ;;

'(pn, bss, lbs, ok) <- n0_pairs main bstack bss0 lbs0 (negb oom1) ;;
pn' <- sort_pairing_nodes SORT_DEPTH pn ;;
n0_resolve pn' ;;;
free_pairing_nodes pn' ;;;
n0_free_rows num bstack ;;;
n0_clear_btypes main ;;;
compact_neutrals main ;;;
aret (negb ok).

Definition ph_n1n2 (main : nref) : FM unit :=
pp0 <- get_next main ;;
aloop fuel (fun pp : nref =>
t <- get_type pp ;;
if t =? TY_SENTINEL then aret (inr tt)
else
ppp_prev <- get_adjacent_run pp false false ;;
ppp_next <- get_adjacent_run pp true false ;;
t' <- get_type pp ;;
let this_type := CHANGE_NUMBER_TO_RTL t' in
prev_type <- adj_type true ppp_prev pp ;;
next_type <- adj_type true ppp_next pp ;;
(if IS_NEUTRAL this_type then
(if prev_type =? next_type then set_type pp prev_type
else l <- get_level pp ;; set_type pp (LEVEL_TO_DIR l))
else aret tt) ;;;
nx <- get_next pp ;;
aret (inl nx))
pp0 ;;;
aret tt.

Definition ph_implicit (main : nref) (base_level : Z) : FM Z :=
pp0 <- get_next main ;;
aloop fuel (fun st : nref * Z =>
let '(pp, max_level) := st in
this_type <- get_type pp ;;
if this_type =? TY_SENTINEL then aret (inr max_level)
else
level <- get_level pp ;;
(if IS_NUMBER this_type then set_level pp (Z.land (level + 2) (-2))
else set_level pp (imp_level level this_type)) ;;;
l' <- get_level pp ;;
let max_level := if max_level <? l' then l' else max_level in
nx <- get_next pp ;;
aret (inl (nx, max_level)))
(pp0, base_level).

Definition ph_reinsert (main explicits : nref) (base_level : Z) : FM (nref * bool) :=
en <- get_next explicits ;;
e <- ptr_eq en explicits ;;
if e then aret (explicits, true)
else
stat <- shadow_run_list main explicits true ;;
if negb stat then aret (NNull, false)
else
p <- get_next main ;;
e1 <- ptr_eq p main ;;
(if negb e1 then
l <- get_level p ;;
if l =? -1 then set_level p base_level else aret tt
else aret tt) ;;;
p0 <- get_next main ;;
aloop fuel (fun p : nref =>
t <- get_type p ;;
if t =? TY_SENTINEL then aret (inr tt)
else
l <- get_level p ;;
(if l =? -1 then pv <- get_prev p ;; pl <- get_level pv ;; set_level p pl else aret tt) ;;;
nx <- get_next p ;;
aret (inl nx))
p0 ;;;
aret (NNull, true).

Definition l1_body (len base_dir base_level : Z) (list : nref) (st : Z * nref * bool * Z)
: FM ((Z * nref * bool * Z) + bool) :=
let '(j, q, state, pos) := st in
if j <? -1 then aret (inr true)
else
char_type <- (if 0 <=? j then types_at j else aret TY_ON) ;;
if negb state && IS_SEPARATOR char_type then
(j' <- sub32 j 1 ;; aret (inl (j', q, true, j)))
else if state && negb (IS_EXPLICIT_OR_SEPARATOR_OR_BN_OR_WS char_type || IS_ISOLATE char_type) then
(p <- new_run ;;
if is_null p then (free_run_list list ;;; aret (inr false))
else
v1 <- add32 j 1 ;; set_pos p v1 ;;;
v2 <- sub32 pos j ;; set_len p v2 ;;;
set_type p base_dir ;;;
set_level p base_level ;;;
move_node_before p q ;;;
j' <- sub32 j 1 ;;
aret (inl (j', p, false, pos)))
else (j' <- sub32 j 1 ;; aret (inl (j', q, state, pos))).

Definition ph_l1 (main : nref) (len base_dir base_level : Z) : FM bool :=
list <- new_run_list ;;
if is_null list then aret false
else
j0 <- sub32 len 1 ;;
ok <- aloop fuel (l1_body len base_dir base_level list) (j0, list, true, j0) ;;
if negb ok then aret false
else shadow_run_list main list false.

Definition ph_fill (main : nref) : FM unit :=
pp0 <- get_next main ;;
aloop fuel (fun st : nref * Z =>
let '(pp, pos) := st in
t <- get_type pp ;;
if t =? TY_SENTINEL then aret (inr tt)
else
level <- get_level pp ;;
l <- get_len pp ;;
levels_fill pos l level ;;;
pos' <- add32 pos l ;;
nx <- get_next pp ;;
aret (inl (nx, pos')))
(pp0, 0) ;;;
aret tt.

Definition par_out (status : bool) (main explicits : nref) (max_level pbase : Z) : FM (Z * Z) :=
(if is_null main then aret tt else free_run_list main) ;;;
(if is_null explicits then aret tt else free_run_list explicits) ;;;
(if status then (if in_s8 (max_level + 1) then aret (max_level + 1, pbase) else aunr)
else aret (0, pbase)).

Definition par_embedding_levels (len pbase : Z) : FM (Z * Z) :=
let max_level := 0 in
if len =? 0 then par_out true NNull NNull max_level pbase
else
main <- run_list_encode_bidi_types len ;;
if is_null main then par_out false NNull NNull max_level pbase
else
'(base_level, pbase) <- ph_base_dir main pbase ;;
let base_dir := LEVEL_TO_DIR base_level in

explicits <- new_run_list ;;
if is_null explicits then par_out false main NNull max_level pbase
else
ph_explicit main explicits base_level ;;;
compact_list main ;;;
'(max_iso_level, lss) <- ph_weak_a main base_dir ;;
ph_weak_b main base_dir lss ;;;
compact_neutrals main ;;;
oom <- ph_n0 main max_iso_level ;;
if oom then par_out false main explicits max_level pbase
else
ph_n1n2 main ;;;
compact_list main ;;;
max_level <- ph_implicit main base_level ;;
compact_list main ;;;
'(explicits, ok) <- ph_reinsert main explicits base_level ;;
if negb ok then par_out false main explicits max_level pbase
else
ok2 <- ph_l1 main len base_dir base_level ;;
if negb ok2 then par_out false main explicits max_level pbase
else
ph_fill main ;;;
par_out true main explicits max_level pbase.

End Bidi.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition S_ (c : Z) : Z := UNIT * size_class c.
Definition cmax (c : Z) : Z :=
if c <? 9 then small_cnt c 0 else halve_big 8 (med_cnt (Z.land c 3)) (S_ c).
Definition std_span (c : Z) : Z := cmax c * S_ c + UNIT.
Definition std_nested (c : Z) : bool := std_span c <=? PGSZ / 2.
Definition bighost (c : Z) : Z := if std_nested c then size_to_class (std_span c - IB) else -1.
Definition std_len (c : Z) : Z := round_up_pg (std_span c).

Definition classes : list Z := map Z.of_nat (seq 0 48).

Lemma In_classes c : 0 <= c < 48 <-> In c classes.
Proof.
unfold classes. rewrite in_map_iff. split.
- intros H. exists (Z.to_nat c). rewrite in_seq. split; lia.
- intros (n & <- & Hn). rewrite in_seq in Hn. lia.
Qed.

Lemma forallb_classes (f : Z -> bool) : forallb f classes = true -> forall c, 0 <= c < 48 -> f c = true.
Proof. intros H c Hc. rewrite forallb_forall in H. apply H. apply In_classes. exact Hc. Qed.

Ltac by_table f :=
let H := fresh in
assert (H : forallb f classes = true) by (vm_compute; reflexivity);
intros c Hc; pose proof (forallb_classes f H c Hc) as T; unfold f in T; cbn beta in T;
repeat (apply andb_prop in T as [T ?]);
repeat match goal with K : (_ =? _) = true |- _ => apply Z.eqb_eq in K | K : (_ <=? _) = true |- _ => apply Z.leb_le in K | K : (_ <? _) = true |- _ => apply Z.ltb_lt in K end.

Definition tab_basic (c : Z) : bool :=
(16 <=? S_ c) && (S_ c <=? 131056) && (8 <=? cmax c) && (cmax c <=? 32) && (std_span c <=? std_len c) && (std_len c <=? std_span c + 4095)
&& (std_len c <=? 1048576) && (Z.modulo (std_len c) PGSZ =? 0).

Definition tab_host (c : Z) : bool :=
if c <=? 6 then (std_nested c) && ((bighost c =? 15) || (bighost c =? 19) || (bighost c =? 23)) && (std_span c <=? S_ (bighost c)) && (c <? bighost c)
else negb (std_nested c) && (bighost c =? -1).

End Mq1.

From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma size_classes_length : length size_classes = 48%nat.
Proof. reflexivity. Qed.

Lemma size_classes_bounds : Forall (fun x => 1 <= x <= 8191) size_classes.
Proof.
apply Forall_forall. intros x Hx. unfold size_classes in Hx.
repeat (destruct Hx as [<-|Hx]; [lia|]). destruct Hx.
Qed.

Lemma size_class_bound sc : 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
intros H. unfold size_class.
apply (Forall_forall (fun x => 1 <= x <= 8191) size_classes); [apply size_classes_bounds|].
apply nth_In. rewrite size_classes_length. lia.
Qed.

