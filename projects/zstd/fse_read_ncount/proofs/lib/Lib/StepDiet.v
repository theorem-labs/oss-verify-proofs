(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem FP.
From Ltac2 Require Import Ltac2 Printf.
From Ltac2 Require Constr FSet Env.
Unset Lia Cache.
Unset Nia Cache.
Set Default Proof Mode "Classic".
Ltac2 mutable diet_debug : bool := false.
Ltac2 mutable diet_min_size : int := 6.
Ltac2 mutable diet_types : bool := true.
Ltac2 Type exn ::= [ Diet_skip | Diet_stuck ].
Ltac2 kof (r : Std.reference) : constant :=
match r with Std.ConstRef k => k | _ => Control.throw (Tactic_failure (Some (Message.of_string "diet: not a constant"))) end.
Ltac2 cof (r : Std.reference) : constructor :=
match r with Std.ConstructRef k => k | _ => Control.throw (Tactic_failure (Some (Message.of_string "diet: not a constructor"))) end.
Ltac2 head_args (c : constr) : constr * constr array :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.App f a => (f, a)
| _ => (c, Array.empty)
end.
Ltac2 is_constructor (k : constructor) (c : constr) : bool :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Constructor k' _ => Constructor.equal k k'
| _ => false
end.
Ltac2 is_constant (k : constant) (c : constr) : bool :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Constant k' _ => Constant.equal k k'
| _ => false
end.
Ltac2 rec is_pos_lit (c : constr) : bool :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Constructor _ _ => true
| Constr.Unsafe.App f a =>
match Constr.Unsafe.kind f with
| Constr.Unsafe.Constructor _ _ => if Int.equal (Array.length a) 1 then is_pos_lit (Array.get a 0) else false
| _ => false
end
| _ => false
end.
Ltac2 is_z_lit (kzpos : constructor) (kzneg : constructor) (kz0 : constructor) (c : constr) : bool :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Constructor k _ => Constructor.equal k kz0
| Constr.Unsafe.App f a =>
if Int.equal (Array.length a) 1 then
(if Bool.or (is_constructor kzpos f) (is_constructor kzneg f) then is_pos_lit (Array.get a 0) else false)
else false
| _ => false
end.
Ltac2 rec pos_bits (c : constr) : int :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.App _ a => Int.add 1 (pos_bits (Array.get a 0))
| _ => 1
end.
Ltac2 rec size_upto (cap : int) (c : constr) : int :=
if Int.le cap 0 then 0 else
match Constr.Unsafe.kind c with
| Constr.Unsafe.App f a =>
Array.fold_left (fun n x => if Int.ge n cap then n else Int.add n (size_upto (Int.sub cap n) x)) (Int.add 1 (size_upto cap f)) a
| Constr.Unsafe.Lambda b c1 => Int.add 1 (Int.add (size_upto cap (Constr.Binder.type b)) (size_upto cap c1))
| Constr.Unsafe.Prod b c1 => Int.add 1 (Int.add (size_upto cap (Constr.Binder.type b)) (size_upto cap c1))
| _ => 1
end.
Ltac2 Type diet_ctx := {
bad : constant FSet.t;
zbin : constant FSet.t;
k_ztobv : constant; k_unsigned : constant; k_sext : constant; k_zext : constant; k_lbw : constant; z_2p64 : constr; k_zadd : constant; k_zmod : constant; k_zshiftr : constant; k_mkR : constant list; k_MS : constant;
c_zpos : constructor; c_zneg : constructor; c_z0 : constructor; c_bv : constructor; c_xO : constructor;
c_tnode : constructor; c_some : constructor;
mutable ann : constr option }.
Ltac2 const_set (l : Std.reference list) : constant FSet.t :=
List.fold_left (fun s r => FSet.add (kof r) s) (FSet.empty FSet.Tags.constant_tag) l.
Ltac2 mkR_consts () : constant list :=
List.map_filter (fun r => match r with Std.ConstRef k => Some k | _ => None end) (Env.expand [@Frame; @mkR]).
Ltac2 mk_ctx () : diet_ctx := {
bad := List.fold_left (fun s k => FSet.add k s) (const_set [
reference:(bv_add); reference:(bv_sub); reference:(bv_mul); reference:(bv_and); reference:(bv_or); reference:(bv_xor);
reference:(bv_not); reference:(bv_opp); reference:(bv_shiftl); reference:(bv_shiftr); reference:(bv_ashiftr);
reference:(bv_concat); reference:(bv_zero_extend); reference:(bv_sign_extend);
reference:(bv_signed); reference:(bv_wrap); reference:(bv_swrap);
reference:(low32); reference:(alu64); reference:(alu32); reference:(mul_div);
reference:(w0); reference:(w1); reference:(ret_pc); reference:(nan_box); reference:(btgt); reference:(zxb);
reference:(v_addi); reference:(v_add); reference:(v_sub); reference:(v_mul); reference:(v_andi); reference:(v_ori); reference:(v_xori);
reference:(v_and); reference:(v_or); reference:(v_xor); reference:(v_slli); reference:(v_srli); reference:(v_srai);
reference:(v_sll); reference:(v_srl); reference:(v_sra); reference:(v_lui); reference:(v_auipc);
reference:(v_addiw); reference:(v_slliw); reference:(v_srliw); reference:(v_sraiw); reference:(v_addw); reference:(v_subw);
reference:(v_sllw); reference:(v_srlw); reference:(v_sraw); reference:(v_mulh); reference:(v_mulhsu); reference:(v_mulhu); reference:(v_mulw);
reference:(v_slt); reference:(v_sltu); reference:(v_slti); reference:(v_sltiu);
reference:(reg_get); reference:(bvmap_set); reference:(bvmap_get); reference:(tget); reference:(tset); reference:(is_x0);
reference:(lift_result); reference:(interp_eff); reference:(interp_eff_accesses); reference:(drop_access_report); reference:(access_value);
reference:(accessed_ranges); reference:(exec); reference:(with_pc); reference:(with_regs); reference:(with_fregs); reference:(with_fcsr);
reference:(with_resv); reference:(rget); reference:(rset); reference:(fget); reference:(fset); reference:(c_regs); reference:(c_fregs);
reference:(c_pc); reference:(c_fcsr); reference:(c_resv); reference:(MS_of_core); reference:(load_val); reference:(store_val);
reference:(branch_taken); reference:(inval_resv); reference:(width_bytes); reference:(accrue);
reference:(fari_d); reference:(fcmp_d); reference:(fari_s); reference:(fcmp_s);
reference:(ov_read_bytes); reference:(write_to_mem); reference:(Z_to_le_bytes) ]) (mkR_consts ());
zbin := const_set [ reference:(Z.add); reference:(Z.sub); reference:(Z.mul); reference:(Z.shiftl); reference:(Z.shiftr);
reference:(Z.land); reference:(Z.lor); reference:(Z.lxor); reference:(Z.modulo); reference:(Z.pow); reference:(Z.div) ];
k_ztobv := kof reference:(Z_to_bv); k_unsigned := kof reference:(bv_unsigned); k_sext := kof reference:(sext); k_zext := kof reference:(zext);
k_lbw := kof reference:(le_bytes_to_word); z_2p64 := constr:(18446744073709551616%Z); k_zadd := kof reference:(Z.add);
k_zmod := kof reference:(Z.modulo); k_zshiftr := kof reference:(Z.shiftr); k_mkR := mkR_consts (); k_MS := kof reference:(MS);
c_zpos := cof reference:(Zpos); c_zneg := cof reference:(Zneg); c_z0 := cof reference:(Z0); c_bv := cof reference:(BV);
c_xO := cof reference:(xO); c_tnode := cof reference:(TNode); c_some := cof reference:(Some); ann := None }.
Ltac2 zlit (x : diet_ctx) (c : constr) : bool := is_z_lit (x.(c_zpos)) (x.(c_zneg)) (x.(c_z0)) c.
Ltac2 head_is (k : constant) (c : constr) : bool := let (f, _) := head_args c in is_constant k f.
Ltac2 rec inert (x : diet_ctx) (c : constr) : bool :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Var _ => true
| Constr.Unsafe.Rel _ => true
| Constr.Unsafe.Constructor k _ => Bool.neg (Constructor.equal k (x.(c_bv)))
| Constr.Unsafe.Ind _ _ => true
| Constr.Unsafe.Sort _ => true
| Constr.Unsafe.Constant k _ => Bool.neg (FSet.mem k (x.(bad)))
| Constr.Unsafe.Lambda b c1 => if inert x (Constr.Binder.type b) then inert x c1 else false
| Constr.Unsafe.Prod b c1 => if inert x (Constr.Binder.type b) then inert x c1 else false
| Constr.Unsafe.App f a =>
match Constr.Unsafe.kind f with
| Constr.Unsafe.Constant k _ =>
if FSet.mem k (x.(bad)) then false
else if Constant.equal k (x.(k_unsigned)) then
(if Int.equal (Array.length a) 2 then
(let t := Array.get a 1 in if head_is (x.(k_ztobv)) t then false else Bool.and (inert x (Array.get a 0)) (inert x t))
else false)
else if Constant.equal k (x.(k_ztobv)) then
(if Int.equal (Array.length a) 2 then
(let n := Array.get a 0 in let t := Array.get a 1 in
if zlit x t then
(match Constr.Unsafe.kind t with
| Constr.Unsafe.App f' a' => if is_constructor (x.(c_zpos)) f' then Int.le (pos_bits (Array.get a' 0)) 64 else false
| _ => true end)
else if head_is (x.(k_unsigned)) t then
(let (_, ua) := head_args t in
if Int.equal (Array.length ua) 2 then
(let v := Array.get ua 1 in
if Constr.is_var v then
(let (_, ta) := head_args (Constr.type v) in
if Int.equal (Array.length ta) 1 then Bool.neg (Constr.equal (Array.get ta 0) n) else false)
else false)
else false)
else if head_is (x.(k_zmod)) t then
(let (_, ma) := head_args t in
if Int.equal (Array.length ma) 2 then
(let md := Array.get ma 1 in
if zlit x md then (if Constr.equal md (x.(z_2p64)) then false else Bool.and (inert x n) (inert x t)) else false)
else false)
else if Bool.neg (inert x n) then false
else inert x t)
else false)
else if Constant.equal k (x.(k_lbw)) then
(if Int.equal (Array.length a) 1 then Constr.is_var (Array.get a 0) else false)
else if Bool.or (Constant.equal k (x.(k_sext))) (Constant.equal k (x.(k_zext))) then
(if Array.for_all (inert x) a then
(let t := Array.get a (Int.sub (Array.length a) 1) in
if head_is (x.(k_ztobv)) t then (let (_, za) := head_args t in if Int.equal (Array.length za) 2 then Bool.neg (zlit x (Array.get za 1)) else false) else true)
else false)
else if FSet.mem k (x.(zbin)) then
(if Int.equal (Array.length a) 2 then
(let p := Array.get a 0 in let q := Array.get a 1 in
if Bool.and (zlit x p) (zlit x q) then false
else if Bool.and (Constant.equal k (x.(k_zadd))) (is_constructor (x.(c_z0)) q) then false
else if Bool.and (Constant.equal k (x.(k_zadd))) (Bool.and (zlit x q) (head_is (x.(k_zadd)) p)) then
(let (_, pa) := head_args p in
if Int.equal (Array.length pa) 2 then (if zlit x (Array.get pa 1) then false else Bool.and (inert x p) (inert x q)) else false)
else if Bool.and (Constant.equal k (x.(k_zshiftr))) (Bool.or (head_is (x.(k_zmod)) p) (head_is (kof reference:(Z.land)) p)) then false
else Bool.and (inert x p) (inert x q))
else false)
else Array.for_all (inert x) a
| Constr.Unsafe.Constructor k _ =>
if Constructor.equal k (x.(c_bv)) then false else
(let n := Array.length a in
let rec go (j : int) : bool :=
if Int.ge j n then true else
(let t := Array.get a j in
let ok :=
if Int.equal j 0 then
(match x.(ann) with
| Some t0 => if Constr.equal t0 t then true else inert x t
| None =>
if inert x t then
((match Constr.Unsafe.kind t with
| Constr.Unsafe.App h _ => (match Constr.Unsafe.kind h with Constr.Unsafe.Ind _ _ => (x.(ann) := Some t) | _ => () end)
| _ => () end); true)
else false end)
else inert x t in
if ok then go (Int.add j 1) else false) in
go 0)
| Constr.Unsafe.Ind _ _ => Array.for_all (inert x) a
| Constr.Unsafe.Var _ => Array.for_all (inert x) a
| Constr.Unsafe.Rel _ => Array.for_all (inert x) a
| _ => false
end
| _ => false
end.
Ltac2 rec find_bad (x : diet_ctx) (c : constr) : constr option :=
if inert x c then None else
match Constr.Unsafe.kind c with
| Constr.Unsafe.App _ a =>
let r := Array.fold_left (fun acc t => match acc with Some _ => acc | None => find_bad x t end) None a in
(match r with Some _ => r | None => Some c end)
| Constr.Unsafe.Lambda b c1 => (match find_bad x (Constr.Binder.type b) with Some r => Some r | None => (match find_bad x c1 with Some r => Some r | None => Some c end) end)
| Constr.Unsafe.Prod b c1 => (match find_bad x (Constr.Binder.type b) with Some r => Some r | None => (match find_bad x c1 with Some r => Some r | None => Some c end) end)
| _ => Some c
end.
Ltac2 z_to_int_opt (x : diet_ctx) (c : constr) : int option :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Constructor k _ => if Constructor.equal k (x.(c_z0)) then Some 0 else None
| Constr.Unsafe.App f a =>
if is_constructor (x.(c_zpos)) f then
(let rec go (p : constr) : int :=
match Constr.Unsafe.kind p with
| Constr.Unsafe.App g b =>
let r := go (Array.get b 0) in
if is_constructor (x.(c_xO)) g then Int.mul 2 r else Int.add (Int.mul 2 r) 1
| _ => 1
end in Some (go (Array.get a 0)))
else None
| _ => None
end.
Ltac2 instr_regs (x : diet_ctx) (i : constr) : int list :=
let (_, args) := head_args i in
Array.fold_left (fun acc a =>
match Constr.Unsafe.kind a with
| Constr.Unsafe.App f b =>
if Bool.and (is_constructor (x.(c_bv)) f) (Int.equal (Array.length b) 3) then
(match z_to_int_opt x (Array.get b 1) with
| Some r =>
(match Constr.Unsafe.kind (Array.get b 0) with
| Constr.Unsafe.App _ nb => if Int.equal (pos_bits (Array.get nb 0)) 3 then r :: acc else acc
| _ => acc end)
| None => acc end)
else acc
| _ => acc
end) [] args.
Ltac2 Type diet_st := {
avoid : constr option;
mutable made : ident list;
mutable tyv : (constr * constr) option;
mutable saved : int }.
Ltac2 diet_prefix () : ident := @dietR.
Ltac2 abstract_part (st : diet_st) (v : constr) : constr :=
let id := (if diet_debug then Control.time (Some "diet fresh") else (fun f => f ())) (fun () => Fresh.in_goal (diet_prefix ())) in
(if diet_debug then Control.time (Some "diet pose") else (fun f => f ())) (fun () => Std.pose (Some id) v);
st.(made) := id :: st.(made);
Constr.Unsafe.make (Constr.Unsafe.Var id).
Ltac2 rec occurs (c : constr) (t : constr) : bool :=
if Constr.equal c t then true else
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f a => if occurs c f then true else Array.exist (occurs c) a
| Constr.Unsafe.Lambda b c1 => if occurs c (Constr.Binder.type b) then true else occurs c c1
| Constr.Unsafe.Prod b c1 => if occurs c (Constr.Binder.type b) then true else occurs c c1
| _ => false
end.
Ltac2 hideable (x : diet_ctx) (st : diet_st) (v : constr) : bool :=
if inert x v then (match st.(avoid) with Some c => Bool.neg (occurs c v) | None => true end) else false.
Ltac2 try_abs (x : diet_ctx) (st : diet_st) (v : constr) : constr :=
if Constr.is_var v then v
else if Int.lt (size_upto (diet_min_size) v) (diet_min_size) then v
else if hideable x st v then abstract_part st v
else ((if diet_debug then (match find_bad x v with Some b => printf "diet: not inert: %t" b | None => printf "diet: part mentions the condition" end) else ()); v).
Ltac2 abs_ty (st : diet_st) (t : constr) : constr :=
if Bool.neg diet_types then t else
match st.(tyv) with
| Some p => let (body, var) := p in if Constr.equal body t then var else t
| None =>
if Constr.is_var t then t else
(let var := abstract_part st t in st.(tyv) := Some (t, var); var)
end.
Ltac2 abs_slot (x : diet_ctx) (st : diet_st) (is_active : bool) (o : constr) : constr :=
match Constr.Unsafe.kind o with
| Constr.Unsafe.App hs sa =>
if Bool.and (is_constructor (x.(c_some)) hs) (Int.equal (Array.length sa) 2) then
(let ty := abs_ty st (Array.get sa 0) in
let v := Array.get sa 1 in
let v' := if is_active then v else try_abs x st v in
Constr.Unsafe.make (Constr.Unsafe.App hs (Array.of_list [ty; v'])))
else o
| _ => o
end.
Ltac2 holds_active (active : int list) (key : int) (bit : int) : bool :=
List.exist (fun r => let k := Int.add r 1 in Bool.and (Int.equal (Int.mod k bit) key) (Int.ge k bit)) active.
Ltac2 rec abs_tree (x : diet_ctx) (st : diet_st) (active : int list) (key : int) (bit : int) (t : constr) : constr :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App h a =>
if Bool.and (is_constructor (x.(c_tnode)) h) (Int.equal (Array.length a) 4) then
(let on_path := holds_active active key bit in
if Bool.and (Bool.neg on_path) (hideable x st t) then abstract_part st t
else
(let l := Array.get a 1 in let o := Array.get a 2 in let r := Array.get a 3 in
let ty := if on_path then abs_ty st (Array.get a 0) else Array.get a 0 in
let o' := abs_slot x st (List.mem Int.equal (Int.sub (Int.add key bit) 1) active) o in
let l' := abs_tree x st active key (Int.mul 2 bit) l in
let r' := abs_tree x st active (Int.add key bit) (Int.mul 2 bit) r in
Constr.Unsafe.make (Constr.Unsafe.App h (Array.of_list [ty; l'; o'; r']))))
else t
| _ => t
end.
Ltac2 abs_regs (x : diet_ctx) (st : diet_st) (active : int list) (r : constr) : constr :=
let (h, a) := head_args r in
if Bool.and (List.exist (fun k => is_constant k h) (x.(k_mkR))) (Int.equal (Array.length a) 31) then
Constr.Unsafe.make (Constr.Unsafe.App h (Array.mapi (fun k v => if List.mem Int.equal (Int.add k 1) active then v else try_abs x st v) a))
else abs_tree x st active 0 1 r.
Ltac2 diet_open_gen (i : constr option) (avoid : constr option) : unit :=
let x := (if diet_debug then Control.time (Some "diet mk_ctx") else (fun f => f ())) (fun () => mk_ctx ()) in
let g := Control.goal () in
let (gh, ga) := head_args g in
let n := Array.length ga in
if Int.lt n 2 then Control.zero Diet_skip else
let ms := Array.get ga (Int.sub n 1) in
let (mh, ma) := head_args ms in
if Bool.neg (Bool.and (is_constant (x.(k_MS)) mh) (Int.equal (Array.length ma) 7)) then Control.zero Diet_skip else
let active := match i with Some i => instr_regs x i | None => [] end in
let st : diet_st := { avoid := avoid; made := []; tyv := None; saved := 0 } in
let r' := (if diet_debug then Control.time (Some "diet abs_regs") else (fun f => f ())) (fun () => abs_regs x st active (Array.get ma 0)) in
let q' := try_abs x st (Array.get ga (Int.sub n 2)) in
match st.(made) with
| [] => ()
| _ =>
let ma' := Array.copy ma in Array.set ma' 0 r';
let ga' := Array.copy ga in
Array.set ga' (Int.sub n 1) (Constr.Unsafe.make (Constr.Unsafe.App mh ma'));
Array.set ga' (Int.sub n 2) q';
let g' := Constr.Unsafe.make (Constr.Unsafe.App gh ga') in
(if diet_debug then printf "diet_open: %i parts, goal %i -> %i nodes" (List.length (st.(made))) (size_upto 1000000 g) (size_upto 1000000 g') else ());
(if diet_debug then Control.time (Some "diet open change") else (fun f => f ()))
(fun () => Std.change None (fun _ => g') { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences })
end.
Ltac2 rec subst_vars (m : (ident * constr) list) (c : constr) : constr :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Var id =>
(match List.find_opt (fun p => Ident.equal (fst p) id) m with Some p => subst_vars m (snd p) | None => c end)
| Constr.Unsafe.App f a => Constr.Unsafe.make (Constr.Unsafe.App (subst_vars m f) (Array.map (subst_vars m) a))
| Constr.Unsafe.Cast c1 k c2 => Constr.Unsafe.make (Constr.Unsafe.Cast (subst_vars m c1) k (subst_vars m c2))
| Constr.Unsafe.Prod b c1 => Constr.Unsafe.make (Constr.Unsafe.Prod (Constr.Binder.unsafe_make (Constr.Binder.name b) (Constr.Binder.relevance b) (subst_vars m (Constr.Binder.type b))) (subst_vars m c1))
| Constr.Unsafe.Lambda b c1 => Constr.Unsafe.make (Constr.Unsafe.Lambda (Constr.Binder.unsafe_make (Constr.Binder.name b) (Constr.Binder.relevance b) (subst_vars m (Constr.Binder.type b))) (subst_vars m c1))
| Constr.Unsafe.LetIn b c1 c2 => Constr.Unsafe.make (Constr.Unsafe.LetIn (Constr.Binder.unsafe_make (Constr.Binder.name b) (Constr.Binder.relevance b) (subst_vars m (Constr.Binder.type b))) (subst_vars m c1) (subst_vars m c2))
| Constr.Unsafe.Case ci ret iv c1 brs =>
let (retc, rel) := ret in
Constr.Unsafe.make (Constr.Unsafe.Case ci (subst_vars m retc, rel) iv (subst_vars m c1) (Array.map (subst_vars m) brs))
| Constr.Unsafe.Proj p r c1 => Constr.Unsafe.make (Constr.Unsafe.Proj p r (subst_vars m c1))
| Constr.Unsafe.Evar e a => Constr.Unsafe.make (Constr.Unsafe.Evar e (Array.map (subst_vars m) a))
| _ => c
end.
Ltac2 rec stuck (x : diet_ctx) (c : constr) : bool :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Fix _ _ _ _ => true
| Constr.Unsafe.Constant k _ => Bool.or (Constant.equal k (kof reference:(tget))) (Constant.equal k (kof reference:(tset)))
| Constr.Unsafe.App f a => if stuck x f then true else Array.exist (stuck x) a
| Constr.Unsafe.Case _ _ _ c1 brs => if stuck x c1 then true else Array.exist (stuck x) brs
| _ => false
end.
Ltac2 has_prefix (p : string) (s : string) : bool :=
let n := String.length p in
if Int.lt (String.length s) n then false else
let rec go (k : int) : bool := if Int.ge k n then true else if Char.equal (String.get p k) (String.get s k) then go (Int.add k 1) else false in
go 0.
Ltac2 diet_defs () : (ident * constr) list :=
List.map_filter (fun h => let (id, body, _) := h in
match body with
| Some b => if has_prefix "dietR" (Ident.to_string id) then Some (id, b) else None
| None => None end) (Control.hyps ()).
Ltac2 diet_close () : unit :=
let m := diet_defs () in
match m with
| [] => ()
| _ =>
let x := mk_ctx () in
let g := Control.goal () in
(let (_, ga) := head_args g in
let n := Array.length ga in
if Int.ge n 1 then
(let (_, ma) := head_args (Array.get ga (Int.sub n 1)) in
if Int.ge (Array.length ma) 1 then (if stuck x (Array.get ma 0) then Control.zero Diet_stuck else ()) else ())
else ());
let g' := subst_vars m g in
Std.change None (fun _ => g') { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences };
List.iter (fun p => let (id, _) := p in
match Control.case (fun () => Std.clear [id]) with
| Val _ => ()
| Err _ => ltac1:(x |- subst x) (Ltac1.of_ident id)
end) m
end.
Ltac2 diet_open_safe (i : constr option) (avoid : constr option) : unit :=
match Control.case (fun () => diet_open_gen i avoid) with
| Val _ => ()
| Err _ => ()
end.
Ltac diet_open i := let f := ltac2:(i |- Control.enter (fun () => diet_open_safe (Ltac1.to_constr i) None)) in f i.
Ltac diet_open_cond c := let f := ltac2:(c |- Control.enter (fun () => diet_open_safe None (Ltac1.to_constr c))) in f c.
Ltac diet_close := ltac2:(Control.enter (fun () => diet_close ())).
Ltac diet_rhs_open := lazymatch goal with |- @eq _ _ ?r => set (drhs_diet := r) | _ => idtac end.
Ltac2 diet_rhs_close () : unit :=
let m := List.map_filter (fun h => let (id, body, _) := h in
match body with
| Some b => if Ident.equal id @drhs_diet then Some (id, b) else None
| None => None end) (Control.hyps ()) in
match m with
| [] => ()
| _ =>
let g' := subst_vars m (Control.goal ()) in
Std.change None (fun _ => g') { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences };
Std.clear [@drhs_diet]
end.
Ltac diet_rhs_close := ltac2:(Control.enter (fun () => diet_rhs_close ())).
Ltac2 Type exn ::= [ Diet_captured ((constr * (ident * constr option * constr) list) list) ].
Ltac2 capture (t : unit -> unit) : ((constr * (ident * constr option * constr) list) list) option :=
match Control.case (fun () =>
t ();
let acc : (constr * (ident * constr option * constr) list) list ref := { contents := [] } in
Control.enter (fun () => acc.(contents) := (Control.goal (), Control.hyps ()) :: acc.(contents));
Control.zero (Diet_captured (List.rev (acc.(contents))))) with
| Val _ => None
| Err e => match e with Diet_captured l => Some l | _ => (if diet_debug then printf "diet capture: %a" (fun () m => m) (Message.of_exn e) else ()); None end
end.
Ltac2 hyp_equal (a : ident * constr option * constr) (b : ident * constr option * constr) : bool :=
let (i1, b1, t1) := a in let (i2, b2, t2) := b in
if Ident.equal i1 i2 then
(if Constr.equal t1 t2 then
(match b1 with
| Some x => (match b2 with Some y => Constr.equal x y | None => false end)
| None => (match b2 with Some _ => false | None => true end) end)
else false)
else false.
Ltac2 rec list_equal (f : 'a -> 'a -> bool) (l1 : 'a list) (l2 : 'a list) : bool :=
match l1 with
| [] => (match l2 with [] => true | _ => false end)
| a :: r1 => (match l2 with [] => false | b :: r2 => if f a b then list_equal f r1 r2 else false end)
end.
Ltac2 rec first_diff (l1 : (ident * constr option * constr) list) (l2 : (ident * constr option * constr) list) : message :=
match l1 with
| [] => (match l2 with [] => Message.of_string "(none)" | h :: _ => let (i, _, _) := h in Message.concat (Message.of_string "extra hyp in NEW: ") (Message.of_ident i) end)
| a :: r1 =>
(match l2 with
| [] => let (i, _, _) := a in Message.concat (Message.of_string "extra hyp in OLD: ") (Message.of_ident i)
| b :: r2 => if hyp_equal a b then first_diff r1 r2 else
(let (i, _, t1) := a in let (j, _, t2) := b in
Message.concat (Message.of_string "hyp differs: ")
(Message.concat (Message.of_ident i) (Message.concat (Message.of_string " : ")
(Message.concat (Message.of_constr t1) (Message.concat (Message.of_string "  VS  ")
(Message.concat (Message.of_ident j) (Message.concat (Message.of_string " : ") (Message.of_constr t2)))))))) end)
end.
Ltac2 diet_dual (old : unit -> unit) (new : unit -> unit) : unit :=
let r1 := capture old in
let r2 := capture new in
(match r1 with
| None => (match r2 with None => () | Some _ => printf "DIET-MISMATCH old engine fails, new succeeds" end)
| Some l1 =>
(match r2 with
| None => printf "DIET-MISMATCH new engine fails, old succeeds"
| Some l2 =>
if Bool.neg (Int.equal (List.length l1) (List.length l2)) then printf "DIET-MISMATCH number of goals %i vs %i" (List.length l1) (List.length l2)
else
List.iter2 (fun a b =>
let (g1, h1) := a in let (g2, h2) := b in
if Bool.neg (Constr.equal g1 g2) then printf "DIET-MISMATCH goal differs: OLD %t NEW %t" g1 g2
else if Bool.neg (list_equal hyp_equal h1 h2) then printf "DIET-MISMATCH %a" (fun () m => m) (first_diff h1 h2)
else printf "DIET-OK") l1 l2 end) end);
old ().
Ltac diet_dual old new := let f := ltac2:(o n |- diet_dual (fun () => Ltac1.run o) (fun () => Ltac1.run n)) in f old new.
Ltac2 is_closed_zlit (c : constr) : bool := is_z_lit (cof reference:(Zpos)) (cof reference:(Zneg)) (cof reference:(Z0)) c.
Ltac diet_is_zlit z :=
let f := ltac2:(z |- match Ltac1.to_constr z with
| Some c => if is_closed_zlit c then () else Control.zero (Tactic_failure None)
| None => Control.zero (Tactic_failure None) end) in f z.
Ltac2 Type exn ::= [ ExElim_skip ].
Ltac2 ex_elim_lemma (k : int) : constr option :=
let nm := Option.get (Ident.of_string (String.app "ex_elim_" (Message.to_string (Message.of_int k)))) in
match Env.expand [@ExElim; nm] with
| r :: _ => Some (Env.instantiate r)
| [] => None
end.
Ltac2 rec peel (j : int) (t : constr) (tys : constr list) (bs : binder list) : constr list * binder list * constr :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App h a =>
if Bool.and (Int.equal (Array.length a) 2)
(match Constr.Unsafe.kind h with Constr.Unsafe.Ind i _ => Ind.equal i (match reference:(ex) with Std.IndRef i' => i' | _ => Control.throw ExElim_skip end) | _ => false end) then
(match Constr.Unsafe.kind (Array.get a 1) with
| Constr.Unsafe.Lambda b body =>
let ty := Array.get a 0 in
if Constr.Unsafe.closedn 0 ty then peel (Int.add j 1) body (ty :: tys) (b :: bs)
else (tys, bs, t)
| _ => (tys, bs, t) end)
else (tys, bs, t)
| _ => (tys, bs, t)
end.
Ltac2 rec mk_lams (bs : binder list) (body : constr) : constr :=
match bs with
| [] => body
| b :: rest => mk_lams rest (Constr.Unsafe.make (Constr.Unsafe.Lambda b body))
end.
Ltac2 ex_elim_hyp (po : ident) : unit :=
let t := Constr.type (Control.hyp po) in
let t' := Std.eval_hnf t in
let (tys, bs, body) := peel 0 t' [] [] in
let k := List.length tys in
if Int.lt k 2 then Control.zero ExElim_skip else
match ex_elim_lemma k with
| None => Control.zero ExElim_skip
| Some lem =>
let g := Control.goal () in
let p := mk_lams bs body in
let args := List.append (List.rev tys) [p; g; Control.hyp po] in
let c0 := Constr.Unsafe.make (Constr.Unsafe.App lem (Array.of_list args)) in
let c := match Constr.Unsafe.check c0 with Val c' => c' | Err _ => Control.zero ExElim_skip end in
ltac1:(c |- apply c) (Ltac1.of_constr c);
Std.clear [po];
let rec intro_n (n : int) (acc : constr list) : constr list :=
if Int.le n 0 then acc else
(let x := Fresh.in_goal @x in Std.intros false [Std.IntroNaming (Std.IntroIdentifier x)];
intro_n (Int.sub n 1) (Control.hyp x :: acc)) in
let xs := intro_n k [] in
Std.intros false [Std.IntroNaming (Std.IntroIdentifier po)];
let ty := Constr.Unsafe.substnl xs 0 body in
Std.change None (fun _ => ty) { Std.on_hyps := Some [(po, Std.AllOccurrences, Std.InHypTypeOnly)]; Std.on_concl := Std.NoOccurrences }
end.
Ltac ex_elim_hyp po :=
let f := ltac2:(po |- Control.enter (fun () =>
match Ltac1.to_ident po with
| Some id => ex_elim_hyp id
| None =>
(match Ltac1.to_constr po with
| Some c => (match Constr.Unsafe.kind c with Constr.Unsafe.Var id => ex_elim_hyp id | _ => printf "ex_elim: not a var"; Control.zero ExElim_skip end)
| None =>
(match Ltac1.to_intro_pattern po with
| Some ip => (match ip with
| Std.IntroNaming n => (match n with Std.IntroIdentifier id => ex_elim_hyp id | _ => Control.zero ExElim_skip end)
| _ => Control.zero ExElim_skip end)
| None => Control.zero ExElim_skip end) end) end)) in f po.
Ltac diet_mode := constr:(1%nat).
Ltac diet_run plain windowed :=
let md := diet_mode in
lazymatch md with
| 0%nat => plain
| 1%nat => first [ windowed | plain ]
| _ => diet_dual plain windowed
end.
Ltac nc_beta_iota := lazymatch goal with |- ?G => let G' := eval cbv beta iota in G in lazymatch G' with G => idtac | _ => change_no_check G' end end.
Ltac nc_iota := lazymatch goal with |- ?G => let G' := eval cbv iota in G in lazymatch G' with G => idtac | _ => change_no_check G' end end.
