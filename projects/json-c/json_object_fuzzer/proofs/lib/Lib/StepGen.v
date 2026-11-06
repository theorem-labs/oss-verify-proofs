(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepFast.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.

From Ltac2 Require Import Ltac2 Printf.
From Ltac2 Require Import Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
#[local] Set Default Proof Mode "Classic".
Open Scope bv_scope.

Lemma sg_pc_seq : forall (b k sz t : Z), t = (k + sz)%Z ->
(Z_to_bv 64 (b + k) + Z_to_bv 64 sz : word) = Z_to_bv 64 (b + t).
Proof. intros b k sz t ->. rewrite lit_add_lit. f_equal. lia. Qed.

Lemma sg_btgt : forall (b k t : Z) (n : N) (imm : bv n), t = (k + bv_signed imm)%Z ->
(Z_to_bv 64 (b + k) + sext 64 imm : word) = Z_to_bv 64 (b + t).
Proof. intros b k t n imm ->. rewrite (sf_btgt (b + k) (b + (k + bv_signed imm)) n imm); [reflexivity | lia]. Qed.

Lemma sg_branch_pc : forall (c : bool) (b k t f sz : Z) (n : N) (imm : bv n),
t = (k + bv_signed imm)%Z -> f = (k + sz)%Z ->
(if c then Z_to_bv 64 (b + k) + sext 64 imm else Z_to_bv 64 (b + k) + Z_to_bv 64 sz : word) =
(if c then Z_to_bv 64 (b + t) else Z_to_bv 64 (b + f)).
Proof. intros c b k t f sz n imm Ht Hf. rewrite (sg_btgt b k t n imm Ht), (sg_pc_seq b k sz f Hf). reflexivity. Qed.

Definition gw_b4 (b : Z) : Prop := (b mod 4 = 0)%Z.
Definition gw_br (b n : Z) : Prop := (0 <= b /\ b + n <= 2^40)%Z.
Definition gw_anch (l r : Z) : Prop := l = r.

Definition gw_al (a k : Z) : Prop := (a mod k = 0)%Z.
Definition gw_le (a b : Z) : Prop := (a <= b)%Z.
Ltac gw_expose a :=
repeat match goal with
| H : gw_br a _ |- _ => unfold gw_br in H
| H : gw_al a _ |- _ => unfold gw_al in H
| H : gw_le a _ |- _ => unfold gw_le in H
| H : gw_le _ a |- _ => unfold gw_le in H
| H : gw_le (a + _) _ |- _ => unfold gw_le in H
| H : gw_le _ (a + _) |- _ => unfold gw_le in H
end.

Lemma ret_pc_base : forall (b n k : Z), gw_b4 b -> gw_br b n ->
((k mod 4 =? 0) && (0 <=? k) && (k <=? n))%Z = true ->
ret_pc (Z_to_bv 64 (b + k)) = Z_to_bv 64 (b + k).
Proof.
unfold gw_b4, gw_br. intros b n k H4 HR Hk. apply andb_true_iff in Hk. destruct Hk as [Hk Hk3]. apply andb_true_iff in Hk. destruct Hk as [Hk1 Hk2].
apply Z.eqb_eq in Hk1. apply Z.leb_le in Hk2. apply Z.leb_le in Hk3.
apply ret_pc_even; [ assert (2^40 < 2^64)%Z by reflexivity; lia | ].
rewrite Z.add_mod by lia. replace (b mod 2)%Z with 0%Z. 2:{ symmetry. Z.div_mod_to_equations. lia. }
replace (k mod 2)%Z with 0%Z. 2:{ symmetry. Z.div_mod_to_equations. lia. } reflexivity.
Qed.
Ltac g_ret_pc :=
lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 (?b + ?k)%Z)) _ _ _ _) =>
lazymatch goal with
| H4 : gw_b4 b, HR : gw_br b ?n |- _ => rewrite (ret_pc_base b n k H4 HR eq_refl)
| _ => fail "generic: ret_pc at a symbolic base needs BASE4 / BASER in the context"
end
| _ => idtac
end.

Ltac g_post_call segs m :=
let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO;
destruct_exs PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
destruct PO as [E [MUc [WMc PO]]];
first [ destruct PO as [MIc PO] | rename PO into MIc ];
subst ms';
lazymatch type of MUc with
| munch _ m ?m' =>
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try destruct_ands PO;
try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => is_Zlit n;
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end);
g_ret_pc.

Lemma sg_evt_pc : forall segs (Q : machine_state -> Prop) R F (pc pc' : word) fc rv (m ro : word -> option byte),
pc = pc' -> evt segs Q (MS R F pc' fc rv m ro) -> evt segs Q (MS R F pc fc rv m ro).
Proof. intros; subst; assumption. Qed.

Fixpoint code_atb (segs : list Segment) (base : Z) (ws : list Z) : bool :=
match ws with
| [] => true
| w :: ws' =>
match fetch_word segs (Z_to_bv 64 base) with
| Some w' => Z.eqb (bv_unsigned w') (bv_unsigned (Z_to_bv 32 w))
| None => false
end && code_atb segs (base + 4) ws'
end.
Lemma code_atb_sound : forall segs ws base, code_atb segs base ws = true -> code_at segs base ws.
Proof.
intros segs ws. induction ws as [|w ws IH]; intros base H; cbn in *; [exact I|].
apply andb_true_iff in H. destruct H as [H1 H2]. split; [|apply IH; exact H2].
destruct (fetch_word segs (Z_to_bv 64 base)) as [w'|]; [|discriminate]. f_equal. apply bv_eq. apply Z.eqb_eq. exact H1.
Qed.

Ltac code_at_vm := apply code_atb_sound; vm_compute; reflexivity.

Ltac g_anchor_rw_any :=
repeat match goal with
| H : gw_anch ?l ?r |- _ => progress (rewrite (H : l = r))
end. Ltac mkr__g_anchor_rw_any_0 := repeat match goal with
| H : gw_anch ?l ?r |- _ => progress (rewrite (H : l = r))
end.

Ltac gstep_core_old segs R F base off fc rv m ro :=
lazymatch goal with
| CODE : code_at segs base ?ws |- _ =>
let k := eval vm_compute in (Z.to_nat (off / 4)) in
let wo := eval vm_compute in (nth_error ws k) in
lazymatch wo with
| Some ?wz =>
let w := constr:(Z_to_bv 32 wz) in
let go i sz HE HD :=
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 (base + off)) fc rv m ro w i sz);
[ | replace (base + off)%Z with (base + 4 * Z.of_nat k)%Z by (cbn; lia);
exact (code_at_nth segs ws base k wz CODE eq_refl)
| HE | HD ];
exec_pre i;
exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
g_anchor_rw_any;
try solve_load; try solve_store;
reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt; post_step i ] in
lazymatch goal with
| HD : decode_any w = Some (?i, ?sz), HE : is_ecall w = false |- _ => go i sz ltac:(exact HE) ltac:(exact HD)
| _ => let d := eval vm_compute in (decode_any w) in
lazymatch d with
| Some (?i, ?sz) => go i sz ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
| _ => fail "generic: undecodable word at offset" off
end
end
| _ => fail "generic: no code word at offset" off
end
| _ => fail "generic: no [code_at" segs base "_] hypothesis in the context"
end.
Ltac gstep_old :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 (?base + ?off)%Z) ?fc ?rv ?m ?ro) => gstep_core_old segs R F base off fc rv m ro
| |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "generic: pc is not base + offset:" pc
end.
Ltac gzstep_old := gstep_old; zsimp.

Import StepFast.
Ltac2 sg_old (z : bool) : unit := if z then ltac1:(gzstep_old) else ltac1:(gstep_old).

Ltac2 sg_find_code (segs : constr) (base : constr) : constr * constr :=
let kc := kof reference:(code_at) in
let rec go (l : (ident * constr option * constr) list) :=
match l with
| [] => sf_fail "generic: no code_at hypothesis for this base"
| (id, _, ty) :: tl =>
match app_of_k kc ty with
| Some args =>
if Int.equal (Array.length args) 3 then
(if Constr.equal (sf_get args 0) segs then
(if Constr.equal (sf_get args 1) base then (Control.hyp id, sf_get args 2) else go tl)
else go tl)
else go tl
| None => go tl
end
end in
go (Control.hyps ()).

Ltac2 sg_find_decode (w : constr) : constr * constr * constr option * constr option :=
let hs := Control.hyps () in
let rec findd (l : (ident * constr option * constr) list) :=
match l with
| [] => sf_fail "generic: no decode hypothesis for a symbolic word"
| (id, _, ty) :: tl =>
(lazy_match! ty with
| decode_any ?w' = Some (?i, ?sz) => if Constr.equal w' w then (i, sz, Control.hyp id) else findd tl
| _ => findd tl
end)
end in
let rec finde (l : (ident * constr option * constr) list) :=
match l with
| [] => sf_fail "generic: no is_ecall hypothesis for a symbolic word"
| (id, _, ty) :: tl =>
(lazy_match! ty with
| is_ecall ?w' = false => if Constr.equal w' w then Control.hyp id else finde tl
| _ => finde tl
end)
end in
let (i, sz, dh) := findd hs in
let eh := finde hs in
(i, sz, Some eh, Some dh).

Ltac2 sg_fetch_proof (segs : constr) (ws : constr) (base : constr) (kn : constr) (wz : constr) (codeh : constr) : constr :=
let oz := '(option Z) in
let nthp := vm_eq oz (mk_app (gref reference:(nth_error)) [| 'Z; ws; kn |]) (mk_app (gref reference:(Some)) [| 'Z; wz |]) in
mk_app (gref reference:(code_at_nth)) [| segs; ws; base; kn; wz; codeh; nthp |].

Ltac2 sg_direct_pc (x : sf_ctx) (i : constr) (b : constr) (k : constr) (sz : constr) (pc1 : constr) : (constr * constr option) option :=
let ztobv := gref reference:(Z_to_bv) in
let n64 := x.(c_n64) in
let zrefl t := mk_app (gref reference:(eq_refl)) [| gref reference:(Z); t |] in
let mkpc t := mk_app ztobv [| n64; mk_app (gref reference:(Z.add)) [| b; t |] |] in
lazy_match! i with
| Jalr _ _ _ => None
| Jal _ ?imm =>
(match imm_signed imm with
| None => None
| Some _ =>
let t := zlit_add k (signed_lit imm) in
lazy_match! pc1 with
| @bv_add 64 (Z_to_bv 64 _) (@sext ?n 64 ?imm') =>
Some (mkpc t, Some (mk_app (gref reference:(sg_btgt)) [| b; k; t; n; imm'; zrefl t |]))
| _ => None
end
end)
| Branch _ _ _ ?imm =>
(match imm_signed imm with
| None => None
| Some _ =>
match Constr.Unsafe.kind pc1 with
| Constr.Unsafe.Case ci ret iv c brs =>
if Int.equal (Array.length brs) 2 then
lazy_match! (sf_get brs 0) with
| @bv_add 64 (Z_to_bv 64 _) (@sext ?n 64 ?imm') =>
lazy_match! (sf_get brs 1) with
| @bv_add 64 (Z_to_bv 64 _) (Z_to_bv 64 ?sz') =>
let t := zlit_add k (signed_lit imm) in
let f := zlit_add k sz in
let c' := subst_w0 (gref reference:(w0)) (mk_app ztobv [| n64; gref reference:(Z0) |]) c in
if bad x c' then None else
Some (Constr.Unsafe.make (Constr.Unsafe.Case ci ret iv c' [| mkpc t; mkpc f |]),
Some (mk_app (gref reference:(sg_branch_pc)) [| c'; b; k; t; f; sz'; n; imm'; zrefl t; zrefl f |]))
| _ => None
end
| _ => None
end
else None
| _ => None
end
end)
| _ =>
let t := zlit_add k sz in
lazy_match! pc1 with
| @bv_add 64 (Z_to_bv 64 _) (Z_to_bv 64 ?sz') =>
Some (mkpc t, Some (mk_app (gref reference:(sg_pc_seq)) [| b; k; sz'; t; zrefl t |]))
| _ => None
end
end.

Ltac2 sg_fix_pc () : unit :=
lazy_match! goal with
| [ |- evt ?s' ?q' (MS ?r' ?f' (@bv_add 64 (Z_to_bv 64 (Z.add ?b' ?k')) (Z_to_bv 64 ?sz')) ?fc' ?rv' ?m' ?ro') ] =>
let t := zlit_add k' sz' in
let pcr := '(@bv_add 64 (Z_to_bv 64 (Z.add $b' $k')) (Z_to_bv 64 $sz')) in
let pcn := '(Z_to_bv 64 (Z.add $b' $t)) in
let pf := mk_app (gref reference:(sg_pc_seq)) [| b'; k'; sz'; t; mk_app (gref reference:(eq_refl)) [| gref reference:(Z); t |] |] in
let kk := strip_cast open_constr:(_ : evt $s' $q' (MS $r' $f' $pcn $fc' $rv' $m' $ro')) in
let term := mk_app (gref reference:(sg_evt_pc)) [| s'; q'; r'; f'; pcr; pcn; fc'; rv'; m'; ro'; pf; kk |] in
match Constr.Unsafe.kind kk with
| Constr.Unsafe.Evar ev _ => Std.exact_no_check term; Control.new_goal ev
| _ => sf_fail "generic: pc fix continuation"
end
| [ |- _ ] => ()
end.

Ltac2 sg_step_ (ph : int ref) (z : bool) : unit :=
let stop (k : int) := ph.(contents) := k; stop k in
lazy_match! goal with
| [ |- evt ?segs ?q (MS ?r ?f (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) ] =>
stop 1;

let (gbase, goff) := lazy_match! pc with
| Z.add ?b ?k => (if is_zlit k then () else sf_fail "generic: the pc offset is not a numeral"); (b, k)
| _ => sf_fail "generic: pc is not of the form base + offset"
end in
let (codeh, ws) := sg_find_code segs gbase in
let kn := eval vm_compute in (Z.to_nat (Z.div $goff 4)) in
let wo := tm "fetch" (fun () => eval vm_compute in (@nth_error Z $ws $kn)) in
let wz := lazy_match! wo with Some ?wz => wz | _ => sf_fail "generic: no code word at this offset" end in
let w := mk_app (gref reference:(Z_to_bv)) [| '(32%N); wz |] in
let (i, sz, ecp_g, dcp_g) :=
if is_zlit wz then
(let ec := eval vm_compute in (is_ecall $w) in (lazy_match! ec with false => () | _ => sf_fail "ecall" end);
let d := tm "decode" (fun () => eval vm_compute in (decode_any $w)) in
let (i, sz) := lazy_match! d with Some (?i, ?sz) => (i, sz) | _ => sf_fail "undecodable" end in
(i, sz, None, None))
else sg_find_decode w in

let rd := lazy_match! i with
| OpImm _ ?rd _ _ => Some rd | ShiftImm _ ?rd _ _ => Some rd | Op _ ?rd _ _ => Some rd | OpImm32 ?rd _ _ => Some rd
| ShiftImm32 _ ?rd _ _ => Some rd | Op32 _ ?rd _ _ => Some rd | Lui ?rd _ => Some rd | Auipc ?rd _ => Some rd
| Mul _ ?rd _ _ => Some rd | Mul32 _ ?rd _ _ => Some rd | Jal ?rd _ => Some rd | Jalr ?rd _ _ => Some rd
| Load _ _ ?rd _ _ => Some rd
| Branch _ _ _ _ => None | Store _ _ _ _ => None
| _ => sf_fail "unsupported instruction"
end in
let rd := match rd with
| Some rd => (match reg_int rd with Some n => if Int.equal n 0 then None else Some rd | None => sf_fail "rd" end)
| None => None
end in
(if is_concrete_map r then () else sf_fail "symbolic register file");
stop 2;
let body := tm "exec_abs" (fun () => exec_abs sz i f pc fc rv) in
let ru := lazy_match! r with mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eval cbv beta iota delta [mkR] in $r | _ => r end in
(if sf_has_k (match reference:(slice_get) with Std.ConstRef k => k | _ => Control.throw Not_found end) ru
then sf_fail "slice_get in the register file (exec_pre frm rewrite)" else ());
let hit := { contents := false } in
let body := tm "resolve" (fun () => resolve (kof reference:(reg_get)) (kof reference:(bvmap_set)) ru 0 body hit) in
let rnew := if hit.(contents) then ru else r in
let body := Constr.Unsafe.substnl [rnew] 0 body in
stop 3;
let x := tm "mk_ctx" (fun () => mk_ctx z) in

let qchk := match Constr.Unsafe.kind q with Constr.Unsafe.Evar _ _ => [] | _ => [q] end in

let trig := { contents := [] } in
let bad_t (t : constr) : bool :=
let id0 := (x.(idioms_seen)).(contents) in
(x.(idioms_seen)).(contents) := false;
let r := bad x t in
(if (x.(idioms_seen)).(contents) then (if r then () else trig.(contents) := t :: trig.(contents))
else (x.(idioms_seen)).(contents) := id0);
(if id0 then (x.(idioms_seen)).(contents) := true else ());
r in
(x.(qmode)).(contents) := true;
(if tm "rest" (fun () => List.exist (fun t => if bad_t t then (if sf_debug then printf "STEPFAST-BADREST: %t@ CULPRIT: %t" t (bad_culprit x t) else ()); true else false)
qchk) then ((x.(qmode)).(contents) := false; sf_fail "rest not normal") else ());
(x.(qmode)).(contents) := false;
(if tm "rest" (fun () => List.exist (fun t => if bad_t t then (if sf_debug then printf "STEPFAST-BADREST: %t@ CULPRIT: %t" t (bad_culprit x t) else ()); true else false)
[f; fc; rv; m; ro]) then sf_fail "rest not normal" else ());

(if List.exist (fun t => let t' := eval cbv delta [mkR] in $t in if Constr.equal t t' then false else true) [f; fc; rv; m; ro; ru]
then sf_fail "mkR in state" else ());
let rdpath := match rd with Some rd => Some (key_path rd) | None => None end in
stop 4;
let dirty := tm "dirty" (fun () => List.rev (dirty_leaves x trig rdpath rnew [] [])) in
stop 5;

(match trig.(contents) with
| [] => ()
| tl =>
if z then
(if tm "idioms" (fun () => idioms_hit (List.fold_left (fun acc t => '(($acc, $t))) 'tt (List.rev tl)))
then sf_fail "idioms" else ())
else ()
end);

let ops := lazy_match! i with
| OpImm ALU_ADD _ ?a _ => [a] | Op ALU_ADD _ ?a ?b => [a; b]
| Jalr _ ?a _ => [a] | Load _ _ _ ?a _ => [a] | Store _ ?a _ _ => [a]
| _ => []
end in
let susp_op := List.exist (fun k => match reg_int k with
| Some 0 => false
| Some _ => let l := tree_get (key_path k) ru in suspicious x l
| None => true
end) ops in

(if (x.(uz_seen)).(contents) then
(if susp_op then
((if sf_debug then List.iter (fun k => match reg_int k with Some 0 => () | Some _ => printf "STEPFAST-SUSP: %t" (tree_get (key_path k) ru) | None => () end) ops else ());
sf_fail "suspicious operand")
else if List.exist (fun (_, l) => risky x l) dirty then sf_fail "risky dirty leaf" else ())
else ());
let dirty := List.map (fun (p, l) => (p, leaf_cbv l)) dirty in
let iv := Ltac1.of_constr i in
let (fwp, ecp, dcp) := tm "vmeqs" (fun () =>
let bv32 := mk_app (gref reference:(bv)) [| x.(c_n32) |] in
let obv32 := mk_app (gref reference:(option)) [| bv32 |] in
let iz := mk_app (gref reference:(prod)) [| gref reference:(instr); gref reference:(Z) |] in
(vm_eq obv32 (mk_app (gref reference:(fetch_word)) [| segs; mk_app (gref reference:(Z_to_bv)) [| x.(c_n64); pc |] |])
(mk_app (gref reference:(Some)) [| bv32; w |]),
vm_eq (gref reference:(bool)) (mk_app (gref reference:(is_ecall)) [| w |]) (gref reference:(false)),
vm_eq (mk_app (gref reference:(option)) [| iz |]) (mk_app (gref reference:(decode_any)) [| w |])
(mk_app (gref reference:(Some)) [| iz; mk_app (gref reference:(pair)) [| gref reference:(instr); gref reference:(Z); i; sz |] |]))) in

let fwp := sg_fetch_proof segs ws gbase kn wz codeh in
let ecp := match ecp_g with Some h => h | None => ecp end in
let dcp := match dcp_g with Some h => h | None => dcp end in
let mr := gref reference:(machine_state) in
let mrr := mk_app (gref reference:(machine_result)) [| mr |] in
let ok := gref reference:(MachineOk) in
let cms := gref reference:(MS) in
let wd := mk_app (gref reference:(bv)) [| x.(c_n64) |] in
let ty_mem := '(word -> option byte) in
let clear_hyps := { contents := [] } in

let joint (pass : unit -> unit) (l : (constr * constr) list) : constr list * constr :=
let (ty, t) := tup l in
let (h, tn) := tm "norm" (fun () => small_goal pass t ty) in
(if sf_timing then printf "NORMED %t ~> %t" t tn else ());
clear_hyps.(contents) := h :: clear_hyps.(contents);
(untup (List.length l) tn, Control.hyp h) in
let dpaths := List.map (fun (p, _) => p) dirty in
let draws := List.map (fun (_, l) => l) dirty in
stop 6;
let (eqp, ms1) := lazy_match! body with
| EDone (Core ?r1 ?f1 ?pc1 ?fc1 ?rv1) =>
(if Constr.equal f1 f then () else sf_fail "F changed");
(if Constr.equal fc1 fc then () else sf_fail "fcsr changed");
(if Constr.equal rv1 rv then () else sf_fail "resv changed");
let rdc := match rdpath with
| Some p => [(p, tree_get p r1)]
| None => (if Constr.equal r1 rnew then () else sf_fail "changed registers"); []
end in
let lcomps := List.append rdc dirty in
stop 61;
let dpc := tm "direct_pc" (fun () => sg_direct_pc x i gbase goff sz pc1) in
stop 62;
let pcsmall := match dpc with None => true | _ => false end in
let raws := List.append (List.map (fun (_, v) => v) lcomps) (if pcsmall then [pc1] else []) in
let k := List.length raws in
(match raws with [] => () | _ => () end);
let (norms, hj) := match raws with
| [] => ([], gref reference:(I))
| [v] =>
(match (lazy_match! i with OpImm ALU_ADD _ _ _ => tm "direct" (fun () => direct_addi x z v) | _ => None end) with
| Some (vn, pf) => ([vn], pf)
| None => joint (fun () => sf_passes x z i) [(wd, v)]
end)
| _ => joint (fun () => sf_passes x z i) (List.map (fun v => (wd, v)) raws)
end in
let lnorms := List.firstn (List.length lcomps) norms in
let pcn := match dpc with
| Some (pcn, _) => pcn
| None => List.last norms
end in
let r1n := List.fold_left2 (fun t (p, _) vn => tree_set p vn t) r1 lcomps lnorms in
let ms1 := mk_app cms [| r1n; f; pcn; fc; rv; m; ro |] in
stop 63;

let e1 :=
match raws with
| [] => None
| _ =>
let tys := List.map (fun _ => wd) raws in
let projs := tup_proj tys (mk_rel 1) in
let lprojs := List.firstn (List.length lcomps) projs in
let rh := List.fold_left2 (fun t (p, _) pr => tree_set p pr t) r1 lcomps lprojs in
let pch := if pcsmall then List.last projs else (match dpc with Some (_, None) => pcn | _ => pc1 end) in
let fn := mk_lam @t (tup_ty tys) (mk_app ok [| mr; mk_app cms [| rh; f; pch; fc; rv; m; ro |] |]) in
let (_, traw) := tup (List.map (fun v => (wd, v)) raws) in
let (_, tnorm) := tup (List.map (fun v => (wd, v)) norms) in
Some (mk_app (gref reference:(sf_congT)) [| tup_ty tys; fn; traw; tnorm; hj |], pch)
end in

let eqp := match dpc with
| Some (_, Some pf) =>
let fn2 := mk_lam @y wd (mk_app ok [| mr; mk_app cms [| r1n; f; mk_rel 1; fc; rv; m; ro |] |]) in
let e2 := mk_app (gref reference:(sf_cong1)) [| fn2; pc1; pcn; pf |] in
(match e1 with
| None => e2
| Some (e, _) =>
mk_app (gref reference:(sf_transMR)) [| mk_app ok [| mr; mk_app cms [| r1; f; pc1; fc; rv; m; ro |] |];
mk_app ok [| mr; mk_app cms [| r1n; f; pc1; fc; rv; m; ro |] |]; mk_app ok [| mr; ms1 |]; e; e2 |]
end)
| _ =>
(match e1 with
| None => mk_app (gref reference:(sf_refl)) [| mk_app ok [| mr; ms1 |] |]
| Some (e, _) => e
end)
end in
(eqp, ms1)
| ELoad ?n ?a ?kk =>

(let q' := eval cbv beta iota delta [tset mkR] in $q in if Constr.equal q q' then () else sf_fail "load: Q has mkR/redexes");
let rdv := match rd with Some rd => rd | None => sf_fail "load to x0" end in
let rp := match rdpath with Some p => p | None => sf_fail "load to x0" end in
let (r1, f1, pc1, fc1, rv1) := match Constr.Unsafe.kind kk with
| Constr.Unsafe.Lambda _ kb =>
lazy_match! kb with
| EDone (Core ?r1 ?f1 ?pc1 ?fc1 ?rv1) => (r1, f1, pc1, fc1, rv1)
| _ => sf_fail "load shape"
end
| _ => sf_fail "load shape"
end in

(if Constr.equal f1 f then () else sf_fail "F changed");
(if Constr.equal fc1 fc then () else sf_fail "fcsr changed");
(if Constr.equal rv1 rv then () else sf_fail "resv changed");
let fv := match Constr.Unsafe.kind r1 with
| Constr.Unsafe.App h args => if Int.equal (Array.length args) 5 then sf_get args 3 else sf_fail "load shape"
| _ => sf_fail "load shape"
end in
let nb := eval cbv beta iota delta [width_bytes] in (width_bytes $n) in
let ext := match Constr.Unsafe.kind '(fun bs : list byte => @bv_extract 64 0 $n (le_bytes_to_word bs)) with
| Constr.Unsafe.Lambda _ eb => eb
| _ => sf_fail "ext"
end in
let fl := mk_lam @bs '(list byte) (Constr.Unsafe.substnl [ext] 0 fv) in
let lg := mk_app (gref reference:(sf_load_goal)) [| segs; m; a; nb; fl |] in
let owd := mk_app (gref reference:(option)) [| wd |] in
let direct := match draws with [] => tm "directld" (fun () => sf_direct_load x z segs m a nb fl n) | _ => None end in
(if sf_timing then (match direct with Some _ => printf "DIRECT-LD yes" | None => printf "DIRECT-LD no %t draws %i" i (List.length draws) end) else ());
let (norms, hj) := match direct with
| Some (vl0, pf) => ([mk_app (gref reference:(Some)) [| wd; vl0 |]], pf)
| None =>
let vt := mk_vt x in
joint (fun () => sf_norm_load2 vt z i) ((owd, lg) :: List.map (fun v => (wd, v)) draws)
end in
let (vl, dnorms) := match norms with
| sv :: dn => (lazy_match! sv with Some ?e => e | _ => sf_fail "load result" end, dn)
| [] => sf_fail "load result"
end in
let pcn := pc1 in
let core_pair := mk_app (gref reference:(prod)) [| gref reference:(core); ty_mem |] in
let kt := mk_lam @x wd (mk_app ok [| core_pair;
mk_app (gref reference:(pair)) [| gref reference:(core); ty_mem;
mk_app (gref reference:(Core)) [| mk_app (gref reference:(bvmap_set)) [| '5%N; wd; rdv; mk_rel 1; rnew |]; f; pc1; fc; rv |]; m |] |]) in
let r1v := tree_set rp vl rnew in
let r1n := List.fold_left2 (fun t p vn => tree_set p vn t) r1v dpaths dnorms in
let ms1 := mk_app cms [| r1n; f; pcn; fc; rv; m; ro |] in
let (h1, ek) := match draws with
| [] => (hj, mk_app (gref reference:(sf_refl)) [| mk_app ok [| mr; ms1 |] |])
| _ =>
let tys := List.map (fun _ => wd) draws in
let tyl := tup_ty tys in
let (_, traw) := tup (List.map (fun v => (wd, v)) draws) in
let (_, tnorm) := tup (List.map (fun v => (wd, v)) dnorms) in
let sv := mk_app (gref reference:(Some)) [| wd; vl |] in
let h1 := pair_eq1 owd tyl lg sv traw tnorm hj in
let h2 := pair_eq2 owd tyl lg sv traw tnorm hj in
let projs := tup_proj tys (mk_rel 1) in
let rh := List.fold_left2 (fun t p pr => tree_set p pr t) r1v dpaths projs in
let fn := mk_lam @t tyl (mk_app ok [| mr; mk_app cms [| rh; f; pcn; fc; rv; m; ro |] |]) in
(h1, mk_app (gref reference:(sf_congT)) [| tyl; fn; traw; tnorm; h2 |])
end in
(mk_app (gref reference:(sf_install_load)) [| segs; ro; m; a; nb; fl; vl; kt; mk_app ok [| mr; ms1 |]; h1; ek |], ms1)
| EStore ?n ?a ?v (EDone (Core ?r1 ?f1 ?pc1 ?fc1 ?rv1)) =>
(if Constr.equal f1 f then () else sf_fail "F changed");
(if Constr.equal fc1 fc then () else sf_fail "fcsr changed");
(if Constr.equal rv1 rv then () else sf_fail "resv changed");
(if Constr.equal r1 rnew then () else sf_fail "store changed registers");
let nb := eval cbv beta iota delta [width_bytes] in (width_bytes $n) in
let bs := mk_app (gref reference:(Z_to_le_bytes)) [| nb; mk_app (gref reference:(bv_unsigned)) [| n; v |] |] in
let sg := mk_app (gref reference:(sf_store_goal)) [| segs; m; a; nb; bs |] in
let omem := mk_app (gref reference:(option)) [| ty_mem |] in
let direct := match draws with [] => tm "directst" (fun () => sf_direct_store x segs m a nb n v) | _ => None end in
(if sf_timing then (match direct with Some _ => printf "DIRECT-ST yes" | None => printf "DIRECT-ST no %t draws %i v %t" i (List.length draws) v end) else ());
let (norms, hj) := match direct with
| Some (mn0, pf) => ([mk_app (gref reference:(Some)) [| ty_mem; mn0 |]], pf)
| None =>
let vt := mk_vt x in
joint (fun () => sf_norm_store2 vt i) ((omem, sg) :: List.map (fun v => (wd, v)) draws)
end in
let (mn, dn1) := match norms with
| sm :: dn => (lazy_match! sm with Some ?e => e | _ => sf_fail "store result" end, dn)
| [] => sf_fail "store result"
end in

let (dnorms, hz) := match draws with
| [] => ([], None)
| _ => if z then
(let (dn2, h2) := joint (fun () => sf_zpasses x) (List.map (fun v => (wd, v)) dn1) in (dn2, Some (dn1, h2)))
else (dn1, None)
end in
let pcn := pc1 in
let core_pair := mk_app (gref reference:(prod)) [| gref reference:(core); ty_mem |] in
let kt := mk_lam @x ty_mem (mk_app ok [| core_pair;
mk_app (gref reference:(pair)) [| gref reference:(core); ty_mem; mk_app (gref reference:(Core)) [| rnew; f; pc1; fc; rv |]; mk_rel 1 |] |]) in
let r1n := List.fold_left2 (fun t p vn => tree_set p vn t) rnew dpaths dnorms in
let ms1 := mk_app cms [| r1n; f; pcn; fc; rv; mn; ro |] in
let (h1, ek) := match draws with
| [] => (hj, mk_app (gref reference:(sf_refl)) [| mk_app ok [| mr; ms1 |] |])
| _ =>
let tys := List.map (fun _ => wd) draws in
let tyl := tup_ty tys in
let (_, traw) := tup (List.map (fun v => (wd, v)) draws) in
let (_, tn1) := tup (List.map (fun v => (wd, v)) dn1) in
let (_, tnorm) := tup (List.map (fun v => (wd, v)) dnorms) in
let sm := mk_app (gref reference:(Some)) [| ty_mem; mn |] in
let h1 := pair_eq1 omem tyl sg sm traw tn1 hj in
let h2 := pair_eq2 omem tyl sg sm traw tn1 hj in
let h2 := match hz with
| None => h2
| Some (_, hz2) => mk_app (gref reference:(sf_trans)) [| tyl; traw; tn1; tnorm; h2; hz2 |]
end in
let projs := tup_proj tys (mk_rel 1) in
let rh := List.fold_left2 (fun t p pr => tree_set p pr t) rnew dpaths projs in
let fn := mk_lam @t tyl (mk_app ok [| mr; mk_app cms [| rh; f; pcn; fc; rv; mn; ro |] |]) in
(h1, mk_app (gref reference:(sf_congT)) [| tyl; fn; traw; tnorm; h2 |])
end in
(mk_app (gref reference:(sf_install_store)) [| segs; ro; m; a; nb; bs; mn; kt; mk_app ok [| mr; ms1 |]; h1; ek |], ms1)
| _ => sf_fail "raw shape"
end in
(if (x.(lit_delta)).(contents) then
(if has_litself x ms1 then sf_fail "litself delta-instance in Q and a syntactic instance in the new state" else ())
else ());
stop 7;
tm "install" (fun () =>
let k := tm "k" (fun () => strip_cast open_constr:(_ : evt $segs $q $ms1)) in
let term := mk_app (gref reference:(sf_evt_step)) [| segs; q; r; f; mk_app (gref reference:(Z_to_bv)) [| x.(c_n64); pc |]; fc; rv; m; ro; w; i; sz; ms1; fwp; ecp; dcp; eqp; k |] in
(if sf_check then
match Constr.Unsafe.check term with
| Val _ => ()
| Err e => printf "STEPFAST-ILLTYPED %a" (fun () e => Message.of_exn e) e; sf_fail "ill-typed"
end
else ());
match Constr.Unsafe.kind k with
| Constr.Unsafe.Evar ev _ => tm "exact" (fun () => Std.exact_no_check term; Control.new_goal ev)
| _ => sf_fail "install: continuation"
end);

sg_fix_pc ();
stop 8;
tm "clear" (fun () => Std.clear (clear_hyps.(contents)));
stop 9;

tm "post" (fun () => lazy_match! goal with
| [ |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) ] => ltac1:(iv |- mem_after_store_opt; post_step iv) iv
| [ |- _ ] => ()
end);
(if z then
lazy_match! goal with
| [ |- evt ?segs' ?q' (MS ?r' ?f' ?pc' ?fc' ?rv' ?m' ?ro') ] =>
if Constr.is_var m' then () else

let (h, mn) := small_goal (fun () => ltac1:(zsimp)) m' '(word -> option byte) in
let k := strip_cast open_constr:(_ : evt $segs' $q' (MS $r' $f' $pc' $fc' $rv' $mn $ro')) in
let term := mk_app '@sf_evt_mem [| segs'; q'; r'; f'; pc'; fc'; rv'; m'; mn; ro'; Control.hyp h; k |] in
match Constr.Unsafe.kind k with
| Constr.Unsafe.Evar ev _ => Std.exact_no_check term; Control.new_goal ev; Std.clear [h]
| _ => sf_fail "install: continuation"
end
end
else ())
| [ |- _ ] => sf_fail "goal shape"
end.

Ltac2 sg_step (z : bool) : unit :=
let ph := { contents := 0 } in
if Bool.neg sf_debug then sg_step_ ph z else
Control.plus (fun () => sg_step_ ph z)
(fun e => (if sf_debug then
(lazy_match! goal with
| [ |- evt _ _ (MS _ _ ?pc _ _ _ _) ] => printf "STEPGEN-PHASE %i at pc %t" (ph.(contents)) pc
| [ |- _ ] => printf "STEPGEN-PHASE %i" (ph.(contents))
end) else ()); Control.zero e).

Ltac2 sg_dual (z : bool) : unit :=
let g0 := Control.goal () in
let res := Control.case (fun () =>
sg_step z;
let g := Control.goal () in
let hs := Control.hyps () in
Control.zero (SF_Captured g hs)) in
match res with
| Val _ => sf_fail "impossible"
| Err e =>
match e with
| SF_Captured gf hf =>
sg_old z;
let go := Control.goal () in
let ho := Control.hyps () in
if Constr.equal gf go then
(if hyps_equal hf ho then printf "STEPGEN-OK" else
printf "STEPGEN-MISMATCH(hyps) at %t" g0)
else

let qev (g : constr) := match Constr.Unsafe.kind g with
| Constr.Unsafe.App f args =>
if Int.equal (Array.length args) 3 then (if is_k (kof reference:(evt)) f then Some (Array.get args 0, Array.get args 2) else None)
else None
| _ => None end in
match qev gf, qev go with
| Some (s1, ms1), Some (s2, ms2) =>
if Constr.equal s1 s2 then
(if Constr.equal ms1 ms2 then
(if hyps_equal hf ho then printf "STEPGEN-OK(evarQ)" else printf "STEPGEN-MISMATCH(hyps) at %t" g0)
else printf "STEPGEN-MISMATCH(goal) at %t@ FAST: %t@ OLD: %t" g0 gf go)
else printf "STEPGEN-MISMATCH(goal) at %t@ FAST: %t@ OLD: %t" g0 gf go
| _, _ => printf "STEPGEN-MISMATCH(goal) at %t@ FAST: %t@ OLD: %t" g0 gf go
end
| _ =>
printf "STEPGEN-FALLBACK %a" (fun () e => Message.of_exn e) e;
sg_old z
end
end.

Ltac g_cur_instr k :=
lazymatch goal with |- evt ?segs _ (MS _ _ (Z_to_bv 64 (?base + ?off)%Z) _ _ _ _) =>
lazymatch goal with CODE : code_at segs base ?ws |- _ =>
let kn := eval vm_compute in (Z.to_nat (off / 4)) in
let wo := eval vm_compute in (nth_error ws kn) in
lazymatch wo with
| Some ?wz =>
let w := constr:(Z_to_bv 32 wz) in
lazymatch goal with
| HD : decode_any w = Some (?i, _) |- _ => k i
| _ => let d := eval vm_compute in (decode_any w) in
lazymatch d with Some (?i, _) => k i end
end
end
end
end.
Ltac g_cur_mem_addr :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
g_cur_instr ltac:(fun i =>
lazymatch i with
| Load _ _ _ ?rs ?imm =>
let rz := eval vm_compute in (bv_unsigned rs) in
let immz := eval vm_compute in (bv_signed imm) in
let REG := Q9A7.reg_val rz in Q9A7.anorm REG immz
| Store _ ?rs _ ?imm =>
let rz := eval vm_compute in (bv_unsigned rs) in
let immz := eval vm_compute in (bv_signed imm) in
let REG := Q9A7.reg_val rz in Q9A7.anorm REG immz
end)
end.

Ltac g_amo_align AMO :=
try (rewrite AMO; cbv beta iota delta [negb]);
try (rewrite Z.eqb_refl; cbv iota).
Ltac g_amo_step AMO :=
g_ret_pc;
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 (?base + ?off)%Z) ?fc ?rv ?m ?ro) =>
lazymatch goal with
| CODE : code_at segs base ?ws |- _ =>
let k := eval vm_compute in (Z.to_nat (off / 4)) in
let wo := eval vm_compute in (nth_error ws k) in
lazymatch wo with
| Some ?wz =>
let w := constr:(Z_to_bv 32 wz) in
let d := eval vm_compute in (decode_any w) in
lazymatch d with
| Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 (base + off)) fc rv m ro w i sz);
[ | replace (base + off)%Z with (base + 4 * Z.of_nat k)%Z by (cbn; lia);
exact (code_at_nth segs ws base k wz CODE eq_refl)
| vm_compute; reflexivity | vm_compute; reflexivity ];
exec_cbv; simp_regs; g_amo_align AMO; exec_cbv; g_amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
try solve_load; try solve_store; reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt ]
end
end
end
end. Ltac mkr__g_amo_step_1 AMO := g_ret_pc;
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 (?base + ?off)%Z) ?fc ?rv ?m ?ro) =>
lazymatch goal with
| CODE : code_at segs base ?ws |- _ =>
let k := eval vm_compute in (Z.to_nat (off / 4)) in
let wo := eval vm_compute in (nth_error ws k) in
lazymatch wo with
| Some ?wz =>
let w := constr:(Z_to_bv 32 wz) in
let d := eval vm_compute in (decode_any w) in
lazymatch d with
| Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 (base + off)) fc rv m ro w i sz);
[ | replace (base + off)%Z with (base + 4 * Z.of_nat k)%Z by (cbn; lia);
exact (code_at_nth segs ws base k wz CODE eq_refl)
| vm_compute; reflexivity | vm_compute; reflexivity ];
exec_cbv; simp_regs; g_amo_align AMO; exec_cbv; g_amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
try solve_load; try solve_store; reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt ]
end
end
end
end.

Lemma ro_bytes_read : forall segs (m : word -> option byte) (G N : Z) (bs : list byte) (k : Z) (n : nat),
mem_inv segs m -> ro_bytes segs G bs -> gw_br G N ->
((0 <=? k) && (k + Z.of_nat n <=? Z.of_nat (length bs)) && (Z.of_nat (length bs) <=? N))%Z = true ->
ov_read_bytes segs m (wa (G + k)) n = Some (firstn n (skipn (Z.to_nat k) bs)).
Proof.
unfold gw_br. intros segs m G N bs k n MI ROM RNG Hb.
apply andb_true_iff in Hb. destruct Hb as [Hb H3]. apply andb_true_iff in Hb. destruct Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
assert (2^40 < 2^64)%Z by reflexivity.
apply bytes_at_read; [ apply ro_bytes_at; [exact MI | lia | lia | exact ROM] | lia | lia ].
Qed.
Ltac g_msize_bytes sz := lazymatch sz with SZ1 => constr:(1%nat) | SZ2 => constr:(2%nat) | SZ4 => constr:(4%nat) | SZ8 => constr:(8%nat) end.
Ltac g_rom_pose R m rs imm n :=
let rz := eval vm_compute in (bv_unsigned rs) in
let REG := Q9A7.reg_val rz in
lazymatch REG with
| Z_to_bv 64 ?E =>
lazymatch goal with
| ANCH : gw_anch (E + bv_signed imm)%Z ?T |- _ =>
let pose_at G k :=
lazymatch goal with
| ROM : ro_bytes ?segs G ?bs, RNG : gw_br G ?N, MI : mem_inv ?segs m |- _ =>
let RD := fresh "RDrom__" in
pose proof (ro_bytes_read segs m G N bs k n MI ROM RNG eq_refl) as RD;
(let kn := eval vm_compute in (Z.to_nat k) in change (Z.to_nat k) with kn in RD);
(lazymatch bs with _ :: _ => cbn [firstn skipn] in RD | _ => idtac end);
first [ rewrite Z.add_0_r in RD | idtac ]
| _ => idtac
end in
lazymatch T with
| (?G + ?k)%Z => pose_at G k
| ?G => pose_at G 0%Z
end
| _ => idtac
end
| _ => idtac
end.

Ltac g_rom_pose_lit R m rs imm n :=
let rz := eval vm_compute in (bv_unsigned rs) in
let REG := Q9A7.reg_val rz in
let immz := eval vm_compute in (bv_signed imm) in
lazymatch REG with
| Z_to_bv 64 ?E =>
first [ match goal with
| ROM : ro_bytes ?segs ?G ?bs, RNG : gw_br ?G ?N, MI : mem_inv ?segs m |- _ =>
let k0 := addr_diff E G in
let kk := eval vm_compute in (k0 + immz)%Z in
let RD := fresh "RDrom__" in
pose proof (ro_bytes_read segs m G N bs kk n MI ROM RNG eq_refl) as RD;
(let kn := eval vm_compute in (Z.to_nat kk) in change (Z.to_nat kk) with kn in RD);
(lazymatch bs with _ :: _ => cbn [firstn skipn] in RD | _ => idtac end);
first [ rewrite Z.add_0_r in RD | idtac ]
end
| idtac ]
| _ => idtac
end.
Ltac g_rom_pre :=
lazymatch goal with
| _ : ro_bytes ?segs _ _ |- evt ?segs _ (MS ?R _ (Z_to_bv 64 (_ + _)%Z) _ _ ?m _) =>
g_cur_instr ltac:(fun i =>
lazymatch i with
| Load ?sz _ _ ?rs ?imm => let n := g_msize_bytes sz in tryif is_var imm then g_rom_pose R m rs imm n else g_rom_pose_lit R m rs imm n
| FLoad FMT_D _ ?rs ?imm => tryif is_var imm then g_rom_pose R m rs imm 8%nat else g_rom_pose_lit R m rs imm 8%nat
| FLoad FMT_S _ ?rs ?imm => tryif is_var imm then g_rom_pose R m rs imm 4%nat else g_rom_pose_lit R m rs imm 4%nat
| _ => idtac
end)
| _ => idtac
end.
Ltac g_anchor_rw :=
repeat match goal with
| H : gw_anch ?l ?r |- evt _ _ _ => progress (rewrite (H : l = r))
end. Ltac mkr__g_anchor_rw_2 := repeat match goal with
| H : gw_anch ?l ?r |- evt _ _ _ => progress (rewrite (H : l = r))
end.

Ltac2 sg_is_generic () : bool :=
lazy_match! goal with
| [ |- evt _ _ (MS _ _ (Z_to_bv 64 (Z.add ?b ?k)) _ _ _ _) ] => if is_zlit k then (if is_zlit b then false else true) else false
| [ |- _ ] => false
end.

Ltac2 sg_core1 (z : bool) : unit :=
ltac1:(g_ret_pc);
ltac1:(g_rom_pre);
(if sg_is_generic () then
(if Int.equal sf_mode 0 then sg_old z
else if Int.equal sf_mode 1 then
Control.once (fun () =>
Control.plus (fun () => sg_step z)
(fun e => (if sf_debug then printf "STEPGEN-FALLBACK %a" (fun () e => Message.of_exn e) e else ()); sg_old z))
else sg_dual z)
else sf_core1 z);

Control.plus (fun () => Std.clear [@RDrom__]) (fun _ => ());
ltac1:(g_anchor_rw).
Ltac2 sg_core (z : bool) : unit := Control.enter (fun () => sg_core1 z).

Ltac sg_step_core := ltac2:(sg_core false). Ltac mkr__sg_step_core_3 := ltac2:(sg_core false).
Ltac sg_zstep := ltac2:(sg_core true). Ltac mkr__sg_zstep_4 := ltac2:(sg_core true).
