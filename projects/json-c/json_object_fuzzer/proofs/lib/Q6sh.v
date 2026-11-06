(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Bool Lia.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import QCiC.Mq1.
Import ListNotations.
Open Scope Z_scope.

Definition AEF_ALLOC_EXT_MAX : Z := 4096.

Record aef_st := mkAef {
a_armed : bool;
a_bits32 : Z;
a_ext : list Z;
a_n : Z
}.
Definition aef_init : aef_st := mkAef false 0 [] 0.

Definition aef_arm (bits : Z) (a : aef_st) : aef_st := mkAef true (u32 bits) (a_ext a) 0.

Definition aef_extend (bytes : list Z) (a : aef_st) : aef_st :=
mkAef (a_armed a) (a_bits32 a) (firstn (Z.to_nat AEF_ALLOC_EXT_MAX) bytes) (a_n a).

Definition aef_bit (a : aef_st) (i : Z) : bool :=
if i <? 32 then Z.testbit (a_bits32 a) i
else let k := (i - 32) / 8 in let j := (i - 32) mod 8 in
if zlength (a_ext a) <=? k then false else Z.testbit (znth (a_ext a) k) j.

Definition aef_deny (a : aef_st) : bool * aef_st :=
if a_armed a then (aef_bit a (a_n a), mkAef true (a_bits32 a) (a_ext a) (u32 (a_n a + 1)))
else (false, a).

Definition FLAGS_INIT : Z := 0x40303.

Record dglob := mkG {
g_aef : aef_st;
g_lflags : Z;
g_caprtl_built : bool;
g_desc_built : bool
}.
Definition set_aef (a : aef_st) (g : dglob) : dglob := mkG a (g_lflags g) (g_caprtl_built g) (g_desc_built g).
Definition set_lflags (v : Z) (g : dglob) : dglob := mkG (g_aef g) v (g_caprtl_built g) (g_desc_built g).
Definition set_caprtl_built (b : bool) (g : dglob) : dglob := mkG (g_aef g) (g_lflags g) b (g_desc_built g).
Definition set_desc_built (b : bool) (g : dglob) : dglob := mkG (g_aef g) (g_lflags g) (g_caprtl_built g) b.

Definition dglob_init : dglob := mkG aef_init FLAGS_INIT false false.
End Mq0.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKJh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Import stdpp.gmap.
Export QCiC.Mq1.
Import QCiC.Mq0 QKJh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope aprog_scope.

Definition znth {A} (d : A) (l : list A) (i : Z) : A :=
if i <? 0 then d else nth (Z.to_nat i) l d.
Fixpoint upd_nat {A} (l : list A) (i : nat) (v : A) : list A :=
match l, i with
| [], _ => []
| _ :: t, O => v :: t
| h :: t, S i' => h :: upd_nat t i' v
end.
Definition zupd {A} (l : list A) (i : Z) (v : A) : list A :=
if i <? 0 then l else upd_nat l (Z.to_nat i) v.
Definition zrepeat {A} (v : A) (n : Z) : list A := repeat v (Z.to_nat n).

Definition zfill {A} (l : list A) (i n : Z) (v : A) : list A :=
firstn (Z.to_nat i) l ++ repeat v (Z.to_nat n) ++ skipn (Z.to_nat (i + n)) l.
Definition in_range (i n : Z) : bool := (0 <=? i) && (i <? n).

Definition in_s32 (x : Z) : bool := (-2147483648 <=? x) && (x <=? 2147483647).
Definition in_s8 (x : Z) : bool := (-128 <=? x) && (x <=? 127).
Definition in_u32 (x : Z) : bool := (0 <=? x) && (x <=? 4294967295).

Definition MASK_RTL : Z := 0x1.
Definition MASK_ARABIC : Z := 0x2.
Definition MASK_STRONG : Z := 0x10.
Definition MASK_WEAK : Z := 0x20.
Definition MASK_NEUTRAL : Z := 0x40.
Definition MASK_SENTINEL : Z := 0x80.
Definition MASK_LETTER : Z := 0x100.
Definition MASK_NUMBER : Z := 0x200.
Definition MASK_NUMSEPTER : Z := 0x400.
Definition MASK_SPACE : Z := 0x800.
Definition MASK_EXPLICIT : Z := 0x1000.
Definition MASK_SEPARATOR : Z := 0x2000.
Definition MASK_OVERRIDE : Z := 0x4000.
Definition MASK_ISOLATE : Z := 0x8000.
Definition MASK_ES : Z := 0x10000.
Definition MASK_ET : Z := 0x20000.
Definition MASK_CS : Z := 0x40000.
Definition MASK_NSM : Z := 0x80000.
Definition MASK_BN : Z := 0x100000.
Definition MASK_BS : Z := 0x200000.
Definition MASK_SS : Z := 0x400000.
Definition MASK_WS : Z := 0x800000.
Definition MASK_FIRST : Z := 0x2000000.

Definition TY_LTR : Z := 0x110.
Definition TY_RTL : Z := 0x111.
Definition TY_AL : Z := 0x113.
Definition TY_LRE : Z := 0x1010.
Definition TY_RLE : Z := 0x1011.
Definition TY_LRO : Z := 0x5010.
Definition TY_RLO : Z := 0x5011.
Definition TY_PDF : Z := 0x1020.
Definition TY_EN : Z := 0x220.
Definition TY_AN : Z := 0x222.
Definition TY_ES : Z := 0x10420.
Definition TY_ET : Z := 0x20420.
Definition TY_CS : Z := 0x40420.
Definition TY_NSM : Z := 0x80020.
Definition TY_BN : Z := 0x100820.
Definition TY_BS : Z := 0x202840.
Definition TY_SS : Z := 0x402840.
Definition TY_WS : Z := 0x800840.
Definition TY_ON : Z := 0x40.
Definition TY_LRI : Z := 0x8040.
Definition TY_RLI : Z := 0x8041.
Definition TY_FSI : Z := 0x2008040.
Definition TY_PDI : Z := 0x8060.
Definition TY_SENTINEL : Z := 0x80.
Definition TY_WLTR : Z := 0x20.
Definition TY_WRTL : Z := 0x21.

Definition NO_BRACKET : Z := 0.
Definition BRACKET_OPEN_MASK : Z := 0x80000000.
Definition BRACKET_ID_MASK : Z := 0x7fffffff.
Definition MAX_EXPLICIT_LEVEL : Z := 125.
Definition MAX_RESOLVED_LEVELS : Z := 127.
Definition MAX_NESTED_BRACKET_PAIRS : Z := 63.
Definition LOCAL_BRACKET_SIZE : Z := 16.
Definition RUN_SIZEOF : Z := 56.
Definition PNODE_SIZEOF : Z := 24.
Definition ROW_SIZEOF : Z := 504.

Definition has (p mask : Z) : bool := negb (Z.land p mask =? 0).
Definition IS_RTL (p : Z) : bool := has p MASK_RTL.
Definition IS_STRONG (p : Z) : bool := has p MASK_STRONG.
Definition IS_NEUTRAL (p : Z) : bool := has p MASK_NEUTRAL.
Definition IS_LETTER (p : Z) : bool := has p MASK_LETTER.
Definition IS_NUMBER (p : Z) : bool := has p MASK_NUMBER.
Definition IS_NUMBER_SEPARATOR_OR_TERMINATOR (p : Z) : bool := has p MASK_NUMSEPTER.
Definition IS_EXPLICIT (p : Z) : bool := has p MASK_EXPLICIT.
Definition IS_ISOLATE (p : Z) : bool := has p MASK_ISOLATE.
Definition IS_SEPARATOR (p : Z) : bool := has p MASK_SEPARATOR.
Definition IS_OVERRIDE (p : Z) : bool := has p MASK_OVERRIDE.
Definition IS_ES_OR_CS (p : Z) : bool := has p (Z.lor MASK_ES MASK_CS).
Definition IS_EXPLICIT_OR_BN (p : Z) : bool := has p (Z.lor MASK_EXPLICIT MASK_BN).
Definition IS_EXPLICIT_OR_SEPARATOR_OR_BN_OR_WS (p : Z) : bool :=
has p (Z.lor (Z.lor MASK_EXPLICIT MASK_SEPARATOR) (Z.lor MASK_BN MASK_WS)).

Definition LEVEL_IS_RTL (lev : Z) : bool := Z.odd lev.
Definition LEVEL_TO_DIR (lev : Z) : Z := if Z.odd lev then TY_RTL else TY_LTR.
Definition DIR_TO_LEVEL (dir : Z) : Z := if IS_RTL dir then 1 else 0.
Definition CHANGE_NUMBER_TO_RTL (p : Z) : Z := if IS_NUMBER p then TY_RTL else p.
Definition EXPLICIT_TO_OVERRIDE_DIR (p : Z) : Z :=
if IS_OVERRIDE p then LEVEL_TO_DIR (DIR_TO_LEVEL p) else TY_ON.
Definition IS_BRACKET_OPEN (bt : Z) : bool := 0 <? Z.land bt BRACKET_OPEN_MASK.
Definition BRACKET_ID (bt : Z) : Z := Z.land bt BRACKET_ID_MASK.
Definition zmax (a b : Z) : Z := if b <? a then a else b.

Record ftables : Type := mkTables {
t_lin2type : Z -> Z;
t_biddat   : Z -> Z;
t_bididx   : Z -> Z;
t_brtidx   : Z -> Z;
t_brkidx   : Z -> Z;
t_brtdat   : Z -> Z;
t_brkdat   : Z -> Z
}.
Definition LIN2TYPE_LEN : Z := 23.
Definition BIDDAT_LEN : Z := 29952.
Definition BIDIDX_LEN : Z := 4352.
Definition BRTIDX_LEN : Z := 512.
Definition BRKIDX_LEN : Z := 1024.
Definition BRTDAT_LEN : Z := 1792.
Definition BRKDAT_LEN : Z := 1152.

Section Base.
Context {ptr : Type}.
Variable TAB : ftables.
Variable fuel : nat.

#[local] Notation FS := (FSt ptr).

Definition FM (A : Type) : Type := @AM ptr FS A.

Definition set_runs (m : gmap N (run_rec ptr)) (s : FS) : FS :=
mkF m (f_pnodes s) (f_rows s) (f_next s) (f_types s) (f_btypes s) (f_levels s).
Definition set_pnodes (m : gmap N (pnode_rec ptr)) (s : FS) : FS :=
mkF (f_runs s) m (f_rows s) (f_next s) (f_types s) (f_btypes s) (f_levels s).
Definition set_rows (m : gmap N (brow ptr)) (s : FS) : FS :=
mkF (f_runs s) (f_pnodes s) m (f_next s) (f_types s) (f_btypes s) (f_levels s).
Definition set_fnext (n : N) (s : FS) : FS :=
mkF (f_runs s) (f_pnodes s) (f_rows s) n (f_types s) (f_btypes s) (f_levels s).
Definition set_types (l : list Z) (s : FS) : FS :=
mkF (f_runs s) (f_pnodes s) (f_rows s) (f_next s) l (f_btypes s) (f_levels s).
Definition set_btypes (l : list Z) (s : FS) : FS :=
mkF (f_runs s) (f_pnodes s) (f_rows s) (f_next s) (f_types s) l (f_levels s).
Definition set_levels (l : list Z) (s : FS) : FS :=
mkF (f_runs s) (f_pnodes s) (f_rows s) (f_next s) (f_types s) (f_btypes s) l.

Definition tab_at (t : Z -> Z) (len : Z) (i : Z) : FM Z :=
if in_range i len then aret (t i) else aunr.

Definition fresh_id : FM N :=
s <- aget ;;
aput (set_fnext (N.succ (f_next s)) s) ;;;
aret (f_next s).

Definition run_lookup (i : N) : FM (run_rec ptr) :=
s <- aget ;;
match (f_runs s) !! i with Some rc => aret rc | None => aunr end.
Definition run_update (i : N) (f : run_rec ptr -> run_rec ptr) : FM unit :=
s <- aget ;;
match (f_runs s) !! i with
| Some rc => aput (set_runs (<[ i := f rc ]> (f_runs s)) s)
| None => aunr
end.

Definition upd_prev (v : nref) (rc : run_rec ptr) : run_rec ptr :=
mkRun (r_blk rc) v (r_next rc) (r_pos rc) (r_len rc) (r_type rc) (r_level rc) (r_iso rc) (r_btype rc) (r_previ rc) (r_nexti rc).
Definition upd_next (v : nref) (rc : run_rec ptr) : run_rec ptr :=
mkRun (r_blk rc) (r_prev rc) v (r_pos rc) (r_len rc) (r_type rc) (r_level rc) (r_iso rc) (r_btype rc) (r_previ rc) (r_nexti rc).
Definition upd_pos (v : Z) (rc : run_rec ptr) : run_rec ptr :=
mkRun (r_blk rc) (r_prev rc) (r_next rc) v (r_len rc) (r_type rc) (r_level rc) (r_iso rc) (r_btype rc) (r_previ rc) (r_nexti rc).
Definition upd_len (v : Z) (rc : run_rec ptr) : run_rec ptr :=
mkRun (r_blk rc) (r_prev rc) (r_next rc) (r_pos rc) v (r_type rc) (r_level rc) (r_iso rc) (r_btype rc) (r_previ rc) (r_nexti rc).
Definition upd_type (v : Z) (rc : run_rec ptr) : run_rec ptr :=
mkRun (r_blk rc) (r_prev rc) (r_next rc) (r_pos rc) (r_len rc) (Some v) (r_level rc) (r_iso rc) (r_btype rc) (r_previ rc) (r_nexti rc).
Definition upd_level (v : Z) (rc : run_rec ptr) : run_rec ptr :=
mkRun (r_blk rc) (r_prev rc) (r_next rc) (r_pos rc) (r_len rc) (r_type rc) v (r_iso rc) (r_btype rc) (r_previ rc) (r_nexti rc).
Definition upd_iso (v : Z) (rc : run_rec ptr) : run_rec ptr :=
mkRun (r_blk rc) (r_prev rc) (r_next rc) (r_pos rc) (r_len rc) (r_type rc) (r_level rc) v (r_btype rc) (r_previ rc) (r_nexti rc).
Definition upd_btype (v : Z) (rc : run_rec ptr) : run_rec ptr :=
mkRun (r_blk rc) (r_prev rc) (r_next rc) (r_pos rc) (r_len rc) (r_type rc) (r_level rc) (r_iso rc) (Some v) (r_previ rc) (r_nexti rc).
Definition upd_previ (v : nref) (rc : run_rec ptr) : run_rec ptr :=
mkRun (r_blk rc) (r_prev rc) (r_next rc) (r_pos rc) (r_len rc) (r_type rc) (r_level rc) (r_iso rc) (r_btype rc) v (r_nexti rc).
Definition upd_nexti (v : nref) (rc : run_rec ptr) : run_rec ptr :=
mkRun (r_blk rc) (r_prev rc) (r_next rc) (r_pos rc) (r_len rc) (r_type rc) (r_level rc) (r_iso rc) (r_btype rc) (r_previ rc) v.

Definition get_prev (r : nref) : FM nref :=
match r with NRun i => rc <- run_lookup i ;; aret (r_prev rc) | NSent => aret NNull | NNull => aunr end.
Definition get_next (r : nref) : FM nref :=
match r with NRun i => rc <- run_lookup i ;; aret (r_next rc) | NSent => aret NNull | NNull => aunr end.
Definition get_pos (r : nref) : FM Z :=
match r with NRun i => rc <- run_lookup i ;; aret (r_pos rc) | NSent => aret 0 | NNull => aunr end.
Definition get_len (r : nref) : FM Z :=
match r with NRun i => rc <- run_lookup i ;; aret (r_len rc) | NSent => aret 0 | NNull => aunr end.
Definition get_type (r : nref) : FM Z :=
match r with
| NRun i => rc <- run_lookup i ;; match r_type rc with Some t => aret t | None => aunr end
| NSent => aret TY_SENTINEL
| NNull => aunr
end.
Definition get_level (r : nref) : FM Z :=
match r with NRun i => rc <- run_lookup i ;; aret (r_level rc) | NSent => aret (-1) | NNull => aunr end.
Definition get_iso (r : nref) : FM Z :=
match r with NRun i => rc <- run_lookup i ;; aret (r_iso rc) | NSent => aret (-1) | NNull => aunr end.
Definition get_btype (r : nref) : FM Z :=
match r with
| NRun i => rc <- run_lookup i ;; match r_btype rc with Some t => aret t | None => aunr end
| NSent => aret NO_BRACKET
| NNull => aunr
end.
Definition get_previ (r : nref) : FM nref :=
match r with NRun i => rc <- run_lookup i ;; aret (r_previ rc) | NSent => aret NNull | NNull => aunr end.
Definition get_nexti (r : nref) : FM nref :=
match r with NRun i => rc <- run_lookup i ;; aret (r_nexti rc) | NSent => aret NNull | NNull => aunr end.

Definition set_prev (r : nref) (v : nref) : FM unit :=
match r with NRun i => run_update i (upd_prev v) | _ => aunr end.
Definition set_next (r : nref) (v : nref) : FM unit :=
match r with NRun i => run_update i (upd_next v) | _ => aunr end.
Definition set_pos (r : nref) (v : Z) : FM unit :=
match r with NRun i => if in_s32 v then run_update i (upd_pos v) else aunr | _ => aunr end.
Definition set_len (r : nref) (v : Z) : FM unit :=
match r with NRun i => if in_s32 v then run_update i (upd_len v) else aunr | _ => aunr end.
Definition set_type (r : nref) (v : Z) : FM unit :=
match r with NRun i => if in_u32 v then run_update i (upd_type v) else aunr | _ => aunr end.
Definition set_level (r : nref) (v : Z) : FM unit :=
match r with NRun i => if in_s8 v then run_update i (upd_level v) else aunr | _ => aunr end.
Definition set_iso (r : nref) (v : Z) : FM unit :=
match r with NRun i => if in_s8 v then run_update i (upd_iso v) else aunr | _ => aunr end.
Definition set_btype (r : nref) (v : Z) : FM unit :=
match r with NRun i => if in_u32 v then run_update i (upd_btype v) else aunr | _ => aunr end.
Definition set_previ (r : nref) (v : nref) : FM unit :=
match r with NRun i => run_update i (upd_previ v) | _ => aunr end.
Definition set_nexti (r : nref) (v : nref) : FM unit :=
match r with NRun i => run_update i (upd_nexti v) | _ => aunr end.

Definition is_null (r : nref) : bool := match r with NNull => true | _ => false end.

Definition resolvable (s : FS) (r : nref) : bool :=
match r with NRun i => match (f_runs s) !! i with Some _ => true | None => false end | _ => true end.

Definition ptr_eq (a b : nref) : FM bool :=
s <- aget ;;
if resolvable s a && resolvable s b then aret (nref_eqb a b) else aunr.

Definition pn_lookup (i : N) : FM (pnode_rec ptr) :=
s <- aget ;;
match (f_pnodes s) !! i with Some rc => aret rc | None => aunr end.
Definition pn_update (i : N) (f : pnode_rec ptr -> pnode_rec ptr) : FM unit :=
s <- aget ;;
match (f_pnodes s) !! i with
| Some rc => aput (set_pnodes (<[ i := f rc ]> (f_pnodes s)) s)
| None => aunr
end.
Definition pget_open (p : pref) : FM nref :=
match p with PNode i => rc <- pn_lookup i ;; aret (pn_open rc) | PNull => aunr end.
Definition pget_close (p : pref) : FM nref :=
match p with PNode i => rc <- pn_lookup i ;; aret (pn_close rc) | PNull => aunr end.
Definition pget_next (p : pref) : FM pref :=
match p with PNode i => rc <- pn_lookup i ;; aret (pn_next rc) | PNull => aunr end.
Definition pset_next (p : pref) (v : pref) : FM unit :=
match p with
| PNode i => pn_update i (fun rc => mkPN (pn_blk rc) (pn_open rc) (pn_close rc) v)
| PNull => aunr
end.
Definition pis_null (p : pref) : bool := match p with PNull => true | _ => false end.

Definition pn_free (p : pref) : FM unit :=
match p with
| PNode i =>
s <- aget ;;
match (f_pnodes s) !! i with
| Some rc => aput (set_pnodes (delete i (f_pnodes s)) s) ;;; afree (pn_blk rc)
| None => aunr
end
| PNull => aunr
end.

Definition types_at (i : Z) : FM Z :=
s <- aget ;; if in_range i (zlength (f_types s)) then aret (znth 0 (f_types s) i) else aunr.
Definition btypes_at (i : Z) : FM Z :=
s <- aget ;; if in_range i (zlength (f_btypes s)) then aret (znth 0 (f_btypes s) i) else aunr.
Definition types_set (i v : Z) : FM unit :=
s <- aget ;;
if in_range i (zlength (f_types s)) && in_u32 v then aput (set_types (zupd (f_types s) i v) s) else aunr.
Definition btypes_set (i v : Z) : FM unit :=
s <- aget ;;
if in_range i (zlength (f_btypes s)) && in_u32 v then aput (set_btypes (zupd (f_btypes s) i v) s) else aunr.

Definition levels_fill (pos n v : Z) : FM unit :=
s <- aget ;;
if (0 <=? pos) && (0 <=? n) && (pos + n <=? zlength (f_levels s)) && in_s8 v
then aput (set_levels (zfill (f_levels s) pos n v) s) else aunr.

Definition add32 (a b : Z) : FM Z := if in_s32 (a + b) then aret (a + b) else aunr.
Definition sub32 (a b : Z) : FM Z := if in_s32 (a - b) then aret (a - b) else aunr.

Definition bidi_type_of (ch : Z) : FM Z :=
lin <- (if ch <? 0x110000 then
l1 <- tab_at (t_bididx TAB) BIDIDX_LEN (ch / 256) ;;
tab_at (t_biddat TAB) BIDDAT_LEN (l1 + ch mod 256)
else aret 0) ;;
tab_at (t_lin2type TAB) LIN2TYPE_LEN lin.

Definition get_bidi_types (cps : list Z) (len : Z) : FM unit :=
aloop fuel (fun st : Z * Z =>
let '(i, k) := st in
if i =? 0 then aret (inr tt)
else
(if in_range k (zlength cps) then aret tt else aunr) ;;;
t <- bidi_type_of (znth 0 cps k) ;;
types_set k t ;;;
aret (inl (i - 1, k + 1)))
(len, 0) ;;;
aret tt.

Definition get_bracket (ch : Z) : FM Z :=
char_type <- (if ch <? 0x10000 then
l1 <- tab_at (t_brtidx TAB) BRTIDX_LEN (ch / 128) ;;
tab_at (t_brtdat TAB) BRTDAT_LEN (l1 + ch mod 128)
else aret 0) ;;
if char_type =? 0 then aret NO_BRACKET
else
l1 <- tab_at (t_brkidx TAB) BRKIDX_LEN (ch / 64) ;;
delta <- tab_at (t_brkdat TAB) BRKDAT_LEN (l1 + ch mod 64) ;;
let bt := (ch + delta) mod 2^31 in
aret (if has char_type 2 then Z.lor bt BRACKET_OPEN_MASK else bt).

Definition get_bracket_types (cps : list Z) (len : Z) : FM unit :=
aloop fuel (fun i : Z =>
if negb (i <? len) then aret (inr tt)
else
t <- types_at i ;;
b <- (if t =? TY_ON then
(if in_range i (zlength cps) then aret tt else aunr) ;;;
get_bracket (znth 0 cps i)
else aret NO_BRACKET) ;;
btypes_set i b ;;;
aret (inl (i + 1)))
0 ;;;
aret tt.

Definition new_run : FM nref :=
r <- amalloc RUN_SIZEOF ;;
match r with
| None => aret NNull
| Some p =>
i <- fresh_id ;;
s <- aget ;;
match (f_runs s) !! i with
| Some _ => aunr
| None =>
aput (set_runs (<[ i := mkRun p NNull NNull 0 0 None 0 0 None NNull NNull ]> (f_runs s)) s) ;;;
aret (NRun i)
end
end.

Definition free_run (r : nref) : FM unit :=
match r with
| NRun i =>
s <- aget ;;
match (f_runs s) !! i with
| Some rc => aput (set_runs (delete i (f_runs s)) s) ;;; afree (r_blk rc)
| None => aunr
end
| _ => aunr
end.

Definition new_run_list : FM nref :=
run <- new_run ;;
match run with
| NNull => aret NNull
| _ =>
set_type run TY_SENTINEL ;;;
set_level run (-1) ;;;
set_pos run (-1) ;;;
set_len run (-1) ;;;
set_next run run ;;;
set_prev run run ;;;
aret run
end.

Definition free_run_list (run_list : nref) : FM unit :=
if is_null run_list then aret tt
else
pv <- get_prev run_list ;;
set_next pv NNull ;;;
aloop fuel (fun pp : nref =>
if is_null pp then aret (inr tt)
else
nx <- get_next pp ;;
free_run pp ;;;
aret (inl nx))
run_list.

Definition encode_new_run (i char_type bracket_type : Z) (last : nref)
: FM ((Z * nref * nref) + (nref * nref)) :=
run <- new_run ;;
if is_null run then aret (inr (last, NNull))
else
set_type run char_type ;;;
set_pos run i ;;;
lp <- get_pos last ;;
set_len last (i - lp) ;;;
set_next last run ;;;
set_prev run last ;;;
set_btype run bracket_type ;;;
aret (inl (i + 1, run, run)).

Definition encode_body (len : Z) (st : Z * nref * nref) : FM ((Z * nref * nref) + (nref * nref)) :=
let '(i, last, run) := st in
if negb (i <? len) then aret (inr (last, run))
else
char_type <- types_at i ;;
bracket_type <- btypes_at i ;;
lt <- get_type last ;;
if negb (char_type =? lt) then encode_new_run i char_type bracket_type last
else if negb (bracket_type =? NO_BRACKET) then encode_new_run i char_type bracket_type last
else
lbt <- get_btype last ;;
if negb (lbt =? NO_BRACKET) || IS_ISOLATE char_type
then encode_new_run i char_type bracket_type last
else aret (inl (i + 1, last, run)).

Definition run_list_encode_bidi_types (len : Z) : FM nref :=
list <- new_run_list ;;
if is_null list then aret NNull
else
'(last, run) <- aloop fuel (encode_body len) (0, list, NNull) ;;
lp <- get_pos last ;;
set_len last (len - lp) ;;;
set_next last list ;;;
set_prev list last ;;;
if is_null run then (free_run_list list ;;; aret NNull)
else aret list.

Definition shadow_advance (le : bool) (bound : Z) (x0 : nref) : FM nref :=
aloop fuel (fun x : nref =>
nx <- get_next x ;;
t <- get_type nx ;;
if t =? TY_SENTINEL then aret (inr x)
else
np <- get_pos nx ;;
if (if le then np <=? bound else np <? bound) then aret (inl nx) else aret (inr x))
x0.

Definition shadow_free_between (p r : nref) : FM unit :=
s0 <- get_next p ;;
aloop fuel (fun s : nref =>
e <- ptr_eq s r ;;
if e then aret (inr tt)
else
nx <- get_next s ;;
free_run s ;;;
aret (inl nx))
s0.

Definition shadow_same (p : nref) (pos pos2 : Z) : FM (option (nref * nref)) :=
pp <- get_pos p ;; pl <- get_len p ;; e1 <- add32 pp pl ;;
ro <- (if pos2 <? e1 then
r <- new_run ;;
if is_null r then aret None
else
pn <- get_next p ;;
set_prev pn r ;;;
set_next r pn ;;;
lv <- get_level p ;; set_level r lv ;;;
il <- get_iso p ;; set_iso r il ;;;
ty <- get_type p ;; set_type r ty ;;;
pp' <- get_pos p ;; pl' <- get_len p ;; e1' <- add32 pp' pl' ;; v <- sub32 e1' pos2 ;;
set_len r v ;;;
set_pos r pos2 ;;;
aret (Some r)
else
r <- get_next p ;;
aret (Some r)) ;;
match ro with
| None => aret None
| Some r =>
pp <- get_pos p ;; pl <- get_len p ;; e2 <- add32 pp pl ;;
if pos <=? e2 then
(if pp <? pos then
v <- sub32 pos pp ;; set_len p v ;;; aret (Some (p, r))
else
p' <- get_prev p ;;
free_run p ;;;
aret (Some (p', r)))
else aret (Some (p, r))
end.

Definition shadow_other (p r : nref) (pos pos2 : Z) : FM (nref * nref) :=
pp <- get_pos p ;; pl <- get_len p ;; e1 <- add32 pp pl ;;
p <- (if pos <=? e1 then
(if pp <? pos then v <- sub32 pos pp ;; set_len p v ;;; aret p
else get_prev p)
else aret p) ;;
rp <- get_pos r ;; rl <- get_len r ;; e2 <- add32 rp rl ;;
r <- (if pos2 <? e2 then
rp' <- get_pos r ;; rl' <- get_len r ;; e2' <- add32 rp' rl' ;; v <- sub32 e2' pos2 ;;
set_len r v ;;;
set_pos r pos2 ;;;
aret r
else get_next r) ;;
shadow_free_between p r ;;;
aret (p, r).

Definition shadow_body (preserve : bool) (st : nref * nref * Z) : FM ((nref * nref * Z) + bool) :=
let '(q, p, pos) := st in
qt <- get_type q ;;
if qt =? TY_SENTINEL then aret (inr true)
else
ql <- get_len q ;;
skip <- (if ql =? 0 then aret true
else qp <- get_pos q ;; aret (qp <? pos)) ;;
if skip then (q' <- get_next q ;; aret (inl (q', p, pos)))
else
pos <- get_pos q ;;
p <- shadow_advance true pos p ;;
ql' <- get_len q ;; pos2 <- add32 pos ql' ;;
r <- shadow_advance false pos2 p ;;
(if preserve then rl <- get_len r ;; ql'' <- get_len q ;; v <- add32 rl ql'' ;; set_len r v else aret tt) ;;;
e <- ptr_eq p r ;;
pr <- (if e then shadow_same p pos pos2
else x <- shadow_other p r pos pos2 ;; aret (Some x)) ;;
match pr with
| None => aret (inr false)
| Some (p, r) =>
let t := q in
q <- get_prev q ;;

tp <- get_prev t ;; tn <- get_next t ;; set_next tp tn ;;;
tn' <- get_next t ;; tp' <- get_prev t ;; set_prev tn' tp' ;;;
set_next p t ;;;
set_prev t p ;;;
set_next t r ;;;
set_prev r t ;;;
q' <- get_next q ;;
aret (inl (q', p, pos))
end.

Definition shadow_run_list (base over : nref) (preserve : bool) : FM bool :=
q0 <- get_next over ;;
status <- aloop fuel (shadow_body preserve) (q0, base, 0) ;;
free_run_list over ;;;
aret status.

End Base.
End Mq1.

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition kRegionSize      : Z := 2^32.
Definition kUserMapSize     : Z := 262144.
Definition kFreeArrayMapSize: Z := 262144.
Definition kFreeArraySize   : Z := 536870912.
Definition kFreeArrayOffset : Z := 3758096384.
Definition kMaxSize         : Z := 65536.
Definition kNumClasses      : Z := 32.
Definition kBatchClass      : Z := 24.
Definition kBatchBytes      : Z := 8192.
Definition kBatchCount      : Z := 1021.
Definition kQMaxSize        : Z := 268435456.
Definition kQMinSize        : Z := 241591905.
Definition kQMaxCache       : Z := 1048576.
Definition kPtrArrBlock     : Z := 16384.
Definition kPtrArrBlockBytes: Z := 131072.
Definition kMaxNumChunks    : Z := 1048576.
Definition kShadowOffset    : Z := 2147450880.
Definition kClearShadowMmapThreshold : Z := 18446744073709551615.
Definition kPage            : Z := 4096.
Definition kMaxAllowedMalloc: Z := 2^40.
Definition kSecUserOff      : Z := 6144.

Record ALay := mkALay {
al_space_beg : Z;
al_ptrarr    : Z;
al_avoid     : list (Z * Z)
}.

Definition reg_beg (L : ALay) (c : Z) : Z := al_space_beg L + c * kRegionSize.
Definition fa_beg (L : ALay) (c : Z) : Z := reg_beg L c + kFreeArrayOffset.

Definition round_up (x a : Z) : Z := ((x + a - 1) / a) * a.
Definition round_down (x a : Z) : Z := (x / a) * a.

Definition rz_size (n : Z) : Z :=
if n <=? 48 then 16 else if n <=? 96 then 32 else if n <=? 448 then 64
else if n <=? 3968 then 128 else if n <=? 16128 then 256
else if n <=? 32256 then 512 else if n <=? 64512 then 1024 else 2048.

Definition used_size (n : Z) : Z := Z.max n 1.

Definition needed (n : Z) : Z := round_up (Z.max n 8) 8 + rz_size n.

Definition from_primary (n : Z) : bool := needed n <=? kMaxSize.

Definition class_id (s : Z) : Z :=
if s <=? 512 then (s + 31) / 32
else let l := Z.log2 s in
let hbits := Z.land (Z.shiftr s (l - 1)) 1 in
let lbits := Z.land s (Z.ones (l - 1)) in
16 + 2 * (l - 9) + hbits + (if 0 <? lbits then 1 else 0).

Definition class_size (c : Z) : Z :=
if c <=? 16 then 32 * c
else let c' := c - 16 in
let t := Z.shiftl 512 (Z.shiftr c' 1) in
t + Z.shiftr t 1 * Z.land c' 1.

Definition max_count (c : Z) : Z :=
let s := class_size c in
if s =? 0 then 0 else 2 * Z.max 1 (Z.min 8 (1024 / s)).

Definition class_of (n : Z) : Z := class_id (needed n).

Definition sec_map_size (n : Z) : Z := round_up (needed n + rz_size n) kPage + kPage.

Inductive aptr : Type :=
| APrim (id : N) (n : Z)
| ASec (map_beg : Z) (n : Z).

Definition aptr_req (p : aptr) : Z := match p with APrim _ n => n | ASec _ n => n end.
Definition aptr_used (p : aptr) : Z := used_size (aptr_req p).

Definition aptr_eqb (p q : aptr) : bool :=
match p, q with
| APrim i n, APrim j m => N.eqb i j && (n =? m)
| ASec a n, ASec b m => (a =? b) && (n =? m)
| _, _ => false
end.

#[global] Instance aptr_eq_dec : EqDecision aptr.
Proof. solve_decision. Defined.

Record cstate := mkC {
c_mapped_user : Z;
c_alloc_user  : Z;
c_num_freed   : Z;
c_mapped_fa   : Z;
c_count       : Z
}.
Definition cst0 : cstate := mkC 0 0 0 0 0.
Definition set_mapped_user (v : Z) (x : cstate) := mkC v (c_alloc_user x) (c_num_freed x) (c_mapped_fa x) (c_count x).
Definition set_alloc_user (v : Z) (x : cstate) := mkC (c_mapped_user x) v (c_num_freed x) (c_mapped_fa x) (c_count x).
Definition set_num_freed (v : Z) (x : cstate) := mkC (c_mapped_user x) (c_alloc_user x) v (c_mapped_fa x) (c_count x).
Definition set_mapped_fa (v : Z) (x : cstate) := mkC (c_mapped_user x) (c_alloc_user x) (c_num_freed x) v (c_count x).
Definition set_count (v : Z) (x : cstate) := mkC (c_mapped_user x) (c_alloc_user x) (c_num_freed x) (c_mapped_fa x) v.

Record batch := mkB {
b_chunks : list aptr;
b_count  : Z;
b_size   : Z
}.

Record qcache := mkQ { q_list : list batch; q_bytes : Z }.
Definition q0 : qcache := mkQ [] 0.

Record secent := mkSec { se_beg : Z; se_size : Z; se_req : Z }.

Record AState := mkAS {
as_cls          : gmap Z cstate;
as_cache_inited : bool;
as_next         : N;
as_reg          : list secent;
as_nres         : Z;
as_tq           : qcache;
as_gq           : qcache;
as_spent        : Z
}.
Definition astate0 : AState := mkAS ∅ false 0%N [] 0 q0 q0 0.

Definition cls (s : AState) (c : Z) : cstate := default cst0 (as_cls s !! c).
Definition set_cls (c : Z) (x : cstate) (s : AState) : AState :=
mkAS (<[c := x]> (as_cls s)) (as_cache_inited s) (as_next s) (as_reg s) (as_nres s) (as_tq s) (as_gq s) (as_spent s).
Definition upd_cls (c : Z) (f : cstate -> cstate) (s : AState) : AState := set_cls c (f (cls s c)) s.
Definition set_inited (s : AState) : AState :=
mkAS (as_cls s) true (as_next s) (as_reg s) (as_nres s) (as_tq s) (as_gq s) (as_spent s).
Definition set_next (v : N) (s : AState) : AState :=
mkAS (as_cls s) (as_cache_inited s) v (as_reg s) (as_nres s) (as_tq s) (as_gq s) (as_spent s).
Definition set_reg (v : list secent) (s : AState) : AState :=
mkAS (as_cls s) (as_cache_inited s) (as_next s) v (as_nres s) (as_tq s) (as_gq s) (as_spent s).
Definition set_nres (v : Z) (s : AState) : AState :=
mkAS (as_cls s) (as_cache_inited s) (as_next s) (as_reg s) v (as_tq s) (as_gq s) (as_spent s).
Definition set_tq (v : qcache) (s : AState) : AState :=
mkAS (as_cls s) (as_cache_inited s) (as_next s) (as_reg s) (as_nres s) v (as_gq s) (as_spent s).
Definition set_gq (v : qcache) (s : AState) : AState :=
mkAS (as_cls s) (as_cache_inited s) (as_next s) (as_reg s) (as_nres s) (as_tq s) v (as_spent s).
Definition add_spent (v : Z) (s : AState) : AState :=
mkAS (as_cls s) (as_cache_inited s) (as_next s) (as_reg s) (as_nres s) (as_tq s) (as_gq s) (as_spent s + v).

Inductive evA : Type :=
| EvMapAnon (len : Z) (avoid : list (Z * Z))
| EvMapFixed (addr len : Z)
| EvRemap (addr len : Z)
| EvMunmap (addr len : Z).

Inductive ansA : Type := AErr | AOk (a : Z).

Inductive unr_reason : Type :=
| UTooBig
| URegionExhausted
| UFreeArrayBig
| UCheck
| UEmptyPop
| UBadPtr.

Inductive res (R : Type) : Type := ROk (r : R) | RSpin | RUnr (why : unr_reason).
Arguments ROk {R} r.
Arguments RSpin {R}.
Arguments RUnr {R} why.

Definition T (R : Type) : Type := stree evA ansA (res R).

Definition tret {R} (r : R) : T R := SRet (ROk r).
Definition tspin {R} : T R := SRet RSpin.
Definition tunr {R} (w : unr_reason) : T R := SRet (RUnr w).
Definition tvis {R} (e : evA) (k : ansA -> T R) : T R := SVis e k.
Definition tbind {R S} (t : T R) (f : R -> T S) : T S :=
sbind t (fun x => match x with ROk r => f r | RSpin => SRet RSpin | RUnr w => SRet (RUnr w) end).

Declare Scope amodel_scope.
Notation "x <- c1 ;; c2" := (tbind c1 (fun x => c2))
(at level 100, c1 at next level, right associativity) : amodel_scope.
Notation "' pat <- c1 ;; c2" := (tbind c1 (fun x_pat => let 'pat := x_pat in c2))
(at level 100, pat pattern, c1 at next level, right associativity) : amodel_scope.
Notation "c1 ;;; c2" := (tbind c1 (fun _ => c2)) (at level 100, right associativity) : amodel_scope.
Local Open Scope amodel_scope.

Definition fixed_ok (a : ansA) : bool := match a with AOk _ => true | AErr => false end.

Section Model.
Variable L : ALay.

Definition ensure_fa (s : AState) (c : Z) (num_freed : Z) : T (bool * AState) :=
let x := cls s c in
let need := 4 * num_freed in
if need <=? c_mapped_fa x then tret (true, s)
else
let new_fa := round_up need kFreeArrayMapSize in
if kFreeArraySize <? new_fa then tunr UFreeArrayBig
else
tvis (EvMapFixed (fa_beg L c + c_mapped_fa x) (new_fa - c_mapped_fa x)) (fun a =>
if fixed_ok a then tret (true, set_cls c (set_mapped_fa new_fa x) s)
else tret (false, s)).

Definition populate (s : AState) (c : Z) (req : Z) : T (bool * AState) :=
let x := cls s c in
let size := class_size c in
let total := c_alloc_user x + req * size in
' (ok, s1) <-
(if c_mapped_user x <? total then
let msz := round_up (total - c_mapped_user x) kUserMapSize in
if kFreeArrayOffset <? c_mapped_user x + msz then tunr URegionExhausted
else
tvis (EvMapFixed (reg_beg L c + c_mapped_user x) msz) (fun a =>
if fixed_ok a then tret (true, set_cls c (set_mapped_user (c_mapped_user x + msz) x) s)
else tret (false, s))
else tret (true, s)) ;;
if negb ok then tret (false, s1)
else
let x1 := cls s1 c in
let new_chunks := (c_mapped_user x1 - c_alloc_user x1) / size in
let total_freed := c_num_freed x1 + new_chunks in
' (ok2, s2) <- ensure_fa s1 c total_freed ;;
if negb ok2 then tret (false, s2)
else
let x2 := cls s2 c in
tret (true, set_cls c (set_alloc_user (c_alloc_user x2 + new_chunks * size) (set_num_freed total_freed x2)) s2).

Definition get_from_allocator (s : AState) (c : Z) (k : Z) : T (bool * AState) :=
let x := cls s c in
' (ok, s1) <- (if c_num_freed x <? k then populate s c (k - c_num_freed x) else tret (true, s)) ;;
if negb ok then tret (false, s1)
else
let x1 := cls s1 c in
if c_num_freed x1 <? k then tunr UCheck
else tret (true, set_cls c (set_num_freed (c_num_freed x1 - k) x1) s1).

Definition refill (s : AState) (c : Z) : T (bool * AState) :=
let s0 := set_inited s in
let k := max_count c / 2 in
' (ok, s1) <- get_from_allocator s0 c k ;;
if negb ok then tret (false, s1)
else tret (true, upd_cls c (set_count k) s1).

Definition cache_alloc (s : AState) (c : Z) : T (bool * AState) :=
' (ok, s1) <- (if c_count (cls s c) =? 0 then refill s c else tret (true, s)) ;;
if negb ok then tret (false, s1)
else tret (true, upd_cls c (fun x => set_count (c_count x - 1) x) s1).

Definition return_to_allocator (s : AState) (c : Z) (k : Z) : T AState :=
let nf' := c_num_freed (cls s c) + k in
' (ok, s1) <- ensure_fa s c nf' ;;
if negb ok then tspin
else tret (upd_cls c (set_num_freed nf') s1).

Definition cache_dealloc (s : AState) (c : Z) : T AState :=
let s0 := set_inited s in
let x := cls s0 c in
s1 <- (if c_count x =? max_count c then
let k := max_count c / 2 in
return_to_allocator (upd_cls c (set_count (c_count x - k)) s0) c k
else tret s0) ;;
tret (upd_cls c (fun y => set_count (c_count y + 1) y) s1).

Definition shadow_of (a : Z) : Z := kShadowOffset + a / 8.

Definition remap_range (addr size : Z) : option (Z * Z) :=
if size / 8 <? kClearShadowMmapThreshold then None
else
let sb := shadow_of addr in
let se := sb + size / 8 in
let pb := round_up sb kPage in
let pe := round_down se kPage in
if pe <=? pb then None else Some (pb, pe - pb).

Definition clear_shadow (addr size : Z) : T unit :=
match remap_range addr size with
| None => tret tt
| Some (pb, len) =>
tvis (EvRemap pb len) (fun a => match a with AOk _ => tret tt | AErr => tspin end)

end.

Definition sec_cost (len : Z) : Z := 2 * len + kPage * (len / 32768 + 2).

Definition sec_iv (e : secent) : Z * Z := (se_beg e, se_beg e + se_size e).
Definition avoid_of (s : AState) : list (Z * Z) := al_avoid L ++ map sec_iv (as_reg s).

Definition large_alloc (s : AState) (n : Z) : T (option Z * AState) :=
let msz := sec_map_size n in
tvis (EvMapAnon msz (avoid_of s)) (fun a =>
match a with
| AErr => tret (None, s)
| AOk mb =>
let nch := Z.of_nat (length (as_reg s)) in
if kMaxNumChunks <=? nch then tunr UCheck
else
s1 <- (if nch =? as_nres s then
tvis (EvMapFixed (al_ptrarr L + 8 * as_nres s) kPtrArrBlockBytes) (fun a2 =>
match a2 with
| AOk _ => tret (set_nres (as_nres s + kPtrArrBlock) s)
| AErr => tunr UCheck
end)
else tret s) ;;
tret (Some mb, add_spent (sec_cost msz) (set_reg (as_reg s1 ++ [mkSec mb msz n]) s1))
end).

Fixpoint find_sec (a : Z) (l : list secent) (i : nat) : option (nat * secent) :=
match l with
| [] => None
| e :: l' => if se_beg e =? a then Some (i, e) else find_sec a l' (S i)
end.

Fixpoint list_upd {A} (l : list A) (i : nat) (v : A) : list A :=
match l, i with
| [], _ => []
| _ :: t, O => v :: t
| h :: t, S i' => h :: list_upd t i' v
end.

Definition swap_remove {A} (i : nat) (l : list A) : list A :=
match rev l with
| [] => []
| lst :: _ => removelast (list_upd l i lst)
end.

Definition large_dealloc (s : AState) (a : Z) : T AState :=
match find_sec a (as_reg s) 0 with
| None => tunr UBadPtr
| Some (i, e) =>
let s1 := set_reg (swap_remove i (as_reg s)) s in
clear_shadow (se_beg e) (se_size e) ;;;
tvis (EvMunmap (se_beg e) (se_size e)) (fun ans =>
match ans with AOk _ => tret s1 | AErr => tspin end)
end.

Definition too_big (n : Z) : bool :=
(n <? 0) || (kMaxAllowedMalloc <? needed n + (if from_primary n then 0 else rz_size n)).

Definition asan_malloc (s : AState) (n : Z) : T (option aptr * AState) :=
if too_big n then tunr UTooBig
else if from_primary n then
' (ok, s1) <- cache_alloc s (class_of n) ;;
if negb ok then tret (None, s1)
else tret (Some (APrim (as_next s1) n), set_next (N.succ (as_next s1)) s1)
else
' (r, s1) <- large_alloc s n ;;
match r with
| None => tret (None, s1)
| Some mb =>

clear_shadow (mb + kSecUserOff) (round_down (used_size n) 8) ;;;
tret (Some (ASec mb n), s1)
end.

Definition calloc_overflows (m k : Z) : bool := negb (k =? 0) && ((2^64 - 1) / k <? m).
Definition asan_calloc (s : AState) (m k : Z) : T (option aptr * AState) :=
if calloc_overflows m k then tret (None, s) else asan_malloc s (m * k).

Definition q_push_back (q : qcache) (b : batch) : qcache := mkQ (q_list q ++ [b]) (q_bytes q + b_size b).

Fixpoint split_last {A} (l : list A) : option (list A * A) :=
match l with
| [] => None
| x :: l' => match split_last l' with
| None => Some ([], x)
| Some (f, y) => Some (x :: f, y)
end
end.

Definition new_batch (s : AState) (p : aptr) (u : Z) : T AState :=
' (ok, s1) <- cache_alloc s kBatchClass ;;
if negb ok then tspin
else tret (set_tq (q_push_back (as_tq s1) (mkB [p] 1 (u + kBatchBytes))) s1).

Definition enqueue (s : AState) (p : aptr) : T AState :=
let u := aptr_used p in
let tq := as_tq s in
match split_last (q_list tq) with
| None => new_batch s p u
| Some (front, b) =>
if b_count b =? kBatchCount then new_batch s p u
else
let b' := mkB (b_chunks b ++ [p]) (b_count b + 1) (b_size b + u) in
tret (set_tq (mkQ (front ++ [b']) (q_bytes tq + u)) s)
end.

Fixpoint merge_loop (cur : batch) (rest : list batch) {struct rest} : list batch * list batch :=
match rest with
| [] => ([cur], [])
| nx :: rest' =>
if b_count cur + b_count nx <=? kBatchCount then
let cur' := mkB (b_chunks cur ++ b_chunks nx) (b_count cur + b_count nx)
(b_size cur + (b_size nx - kBatchBytes)) in
let '(l, ex) := merge_loop cur' rest' in
(l, mkB [] 0 kBatchBytes :: ex)
else
let '(l, ex) := merge_loop nx rest' in
(cur :: l, ex)
end.

Definition merge_batches (g : qcache) : qcache * list batch :=
match q_list g with
| [] => (g, [])
| b :: rest =>
let '(l, ex) := merge_loop b rest in
(mkQ l (q_bytes g - kBatchBytes * Z.of_nat (length ex)), ex)
end.

Fixpoint pop_loop (l : list batch) (bytes : Z) (tmp : list batch) {struct l} : option (qcache * list batch) :=
if kQMinSize <? bytes then
match l with
| [] => None
| b :: l' => pop_loop l' (bytes - b_size b) (tmp ++ [b])
end
else Some (mkQ l bytes, tmp).

Definition recycle_chunk (s : AState) (p : aptr) : T AState :=
match p with
| APrim _ n => cache_dealloc s (class_of n)
| ASec a _ => large_dealloc s a
end.

Fixpoint recycle_chunks (s : AState) (ps : list aptr) {struct ps} : T AState :=
match ps with
| [] => tret s
| p :: ps' => s1 <- recycle_chunk s p ;; recycle_chunks s1 ps'
end.

Fixpoint do_recycle (s : AState) (bs : list batch) {struct bs} : T AState :=
match bs with
| [] => tret s
| b :: bs' =>
s1 <- recycle_chunks s (b_chunks b) ;;
s2 <- cache_dealloc s1 kBatchClass ;;
do_recycle s2 bs'
end.

Definition recycle (s : AState) : T AState :=
let g := as_gq s in
let cache_size := q_bytes g in
let overhead := kBatchBytes * Z.of_nat (length (q_list g)) in
if cache_size <? overhead then tunr UCheck
else
let '(g1, tmp1) :=
(if (overhead <? cache_size) && (cache_size * 100 <? overhead * 200)
then merge_batches g else (g, [])) in
match pop_loop (q_list g1) (q_bytes g1) tmp1 with
| None => tunr UEmptyPop
| Some (g2, tmp) => do_recycle (set_gq g2 s) tmp
end.

Definition drain (s : AState) : T AState :=
let tq := as_tq s in
let g := as_gq s in
let g' := mkQ (q_list g ++ q_list tq) (q_bytes g + q_bytes tq) in
let s1 := set_gq g' (set_tq q0 s) in
if kQMaxSize <? q_bytes g' then recycle s1 else tret s1.

Definition asan_free (s : AState) (p : aptr) : T AState :=
s1 <- (if kQMaxSize <? aptr_used p
then recycle_chunk s p
else enqueue s p) ;;
if kQMaxCache <? q_bytes (as_tq s1) then drain s1 else tret s1.

Definition qroom (a : AState) (p : aptr) : Prop :=
q_bytes (as_gq a) + q_bytes (as_tq a) + aptr_used p + kBatchBytes <= kQMaxSize.

End Model.

Fixpoint trun {R} (t : T R) (ans : list ansA) {struct t} : list (evA * ansA) * option (res R) * list ansA :=
match t with
| SRet r => ([], Some r, ans)
| SVis e k =>
match ans with
| [] => ([], None, [])
| a :: ans' => let '(tr, r, rest) := trun (k a) ans' in ((e, a) :: tr, r, rest)
end
end.
