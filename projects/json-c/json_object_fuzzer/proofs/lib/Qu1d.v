(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0z1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsGW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsGW.
Import ListNotations.
Open Scope Z_scope.

Ltac norm_lit1 :=
match goal with
| |- context [zxb (Z_to_bv 8 ?c)] => is_Zlit c;
rewrite (zxb_b8 c); let v := eval vm_compute in (c mod 256)%Z in change (c mod 256)%Z with v
| |- context [sxb (Z_to_bv 8 ?c)] => is_Zlit c; rewrite (sxb_b8 c) by lia
| |- context [sx32 (Z_to_bv 64 ?c)] => is_Zlit c;
first [ rewrite (sx32_small c) by lia
| rewrite (sx32_u32_high c) by lia;
let v := eval vm_compute in (c - 2^32)%Z in change (c - 2^32)%Z with v ]
| |- context [zx32 (Z_to_bv 64 ?c)] => is_Zlit c; rewrite (zx32_small c) by lia
| |- context [Z.opp ?c] => is_Zlit c; let v := eval vm_compute in (Z.opp c) in change (Z.opp c) with v

| |- context [v_sltu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => is_Zlit a; is_Zlit b;
let t := constr:(v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b)) in
let v := eval vm_compute in (bv_unsigned t) in
replace t with (Z_to_bv 64 v) by (rewrite v_sltu_b2z; f_equal; vm_compute; reflexivity)
| |- context [v_slt (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => is_Zlit a; is_Zlit b;
let t := constr:(v_slt (Z_to_bv 64 a) (Z_to_bv 64 b)) in
let v := eval vm_compute in (bv_unsigned t) in
replace t with (Z_to_bv 64 v) by (rewrite v_slt_b2z; f_equal; vm_compute; reflexivity)
| |- context [v_sltiu (Z_to_bv 64 ?a) ?i] => is_Zlit a; is_Zlit i;
let t := constr:(v_sltiu (Z_to_bv 64 a) i) in
let v := eval vm_compute in (bv_unsigned t) in
replace t with (Z_to_bv 64 v) by (rewrite v_sltiu_b2z; f_equal; vm_compute; reflexivity)
| |- context [v_slti (Z_to_bv 64 ?a) ?i] => is_Zlit a; is_Zlit i;
let t := constr:(v_slti (Z_to_bv 64 a) i) in
let v := eval vm_compute in (bv_unsigned t) in
replace t with (Z_to_bv 64 v) by (rewrite v_slti_b2z; f_equal; vm_compute; reflexivity)
end.
Ltac lits := repeat norm_lit1; fold_closed_in_goal.

Ltac stf := step; fix_lit_store.
Ltac stp := step; fix_lit_store; lits.

Ltac post_call0 :=
let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO; destruct_exs PO;
let E := fresh "E" in destruct PO as [E PO]; subst ms';
try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).
Tactic Notation "call0" uconstr(SPEC) := eapply evt_cut; [ eapply SPEC | post_call0 ].

Lemma land_ldiff_distr_r x a b : Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x n), (Z.testbit a n), (Z.testbit b n); reflexivity. Qed.

Lemma land_pagemask x : (0 <= x < 2^64)%Z -> Z.land x 18446744073709547520 = (x - x mod 4096)%Z.
Proof.
intros Hx.
assert (E : 18446744073709547520%Z = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
rewrite land_ldiff_distr_r. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^12)%Z with 4096%Z. pose proof (Z.div_mod x 4096). lia.
Qed.

Lemma land_pagemask_l x : (0 <= x < 2^64)%Z -> Z.land 18446744073709547520 x = (x - x mod 4096)%Z.
Proof. intros Hx. rewrite Z.land_comm. apply land_pagemask. exact Hx. Qed.

Ltac not_Zlit e := lazymatch e with Z0 => fail | Zpos _ => fail | Zneg _ => fail | _ => idtac end.
Ltac cond_unsig :=
repeat match goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
match c with context [bv_unsigned (Z_to_bv 64 ?e)] =>
not_Zlit e; rewrite (unsigned_lit e) by lia end
end.
Ltac ifz := unfold_cond; cond_unsig; if_lit.

Ltac with_mem k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

Lemma land_mask18 x : (0 <= x < 2^64)%Z -> Z.land x 18446744073709289472 = (x - x mod 262144)%Z.
Proof.
intros Hx.
assert (E : 18446744073709289472%Z = Z.ldiff (Z.ones 64) (Z.ones 18)) by reflexivity. rewrite E.
rewrite land_ldiff_distr_r. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^18)%Z with 262144%Z. pose proof (Z.div_mod x 262144). lia.
Qed.

Lemma round_up18_eq x : (0 <= x)%Z -> (x + 262144 <= 2^64)%Z ->
Z.land (x + 262143) 18446744073709289472 = ((x + 262144 - 1) / 262144 * 262144)%Z.
Proof.
intros H0 H1. rewrite land_mask18 by lia. replace (x + 262144 - 1)%Z with (x + 262143)%Z by lia.
pose proof (Z.div_mod (x + 262143) 262144 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 262143) 262144 ltac:(lia)). lia.
Qed.

Definition hide (P : Prop) : Prop := P.
Lemma hideI (P : Prop) : P -> hide P. Proof. exact (fun p => p). Qed.
Lemma hideE (P : Prop) : hide P -> P. Proof. exact (fun p => p). Qed.
Ltac hide H := apply hideI in H.
Ltac unhide H := apply hideE in H.

Lemma sub_fp_nil' : forall W, sub_fp [] W.
Proof. intros W x _. exact I. Qed.

Lemma outside_In : forall W lo hi x, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof.
induction W as [|[a b] W IH]; intros lo hi x Ho Hin; [destruct Hin|].
cbn in Ho. destruct Ho as [H1 H2]. destruct Hin as [E|Hin]; [inversion E; subst; exact H1| exact (IH _ _ _ H2 Hin)].
Qed.

Lemma sub_fp_cons_in : forall lo hi lo' hi' W2 W,
In (lo', hi') W -> (lo' <= lo)%Z -> (hi <= hi')%Z -> sub_fp W2 W -> sub_fp ((lo, hi) :: W2) W.
Proof.
intros lo hi lo' hi' W2 W Hin H1 H2 HS x Ho. cbn. split; [| exact (HS x Ho)].
pose proof (outside_In W lo' hi' x Ho Hin). lia.
Qed.

Ltac in_pick k := lazymatch k with O => left; reflexivity | S ?k' => right; in_pick k' end.

Ltac sfp_idx lo hi W k :=
lazymatch W with
| (lo, hi) :: _ => k
| _ :: ?W' => sfp_idx lo hi W' (S k)
end.
Ltac sfp_cheap := first [ apply Z.le_refl | Qo9G.term_slim ltac:(zify_prune_plain; Zify.zify; xlia zchecker) ]. Ltac mkr__sfp_cheap_0 := first [ apply Z.le_refl | Qo9G.term_slim ltac:(zify_prune_plain; Zify.zify; xlia zchecker) ].

Ltac zbase_ t :=
lazymatch t with
| Z.add ?a _ => zbase_ a
| Z.sub ?a _ => zbase_ a
| Zpos _ => constr:(tt)
| Zneg _ => constr:(tt)
| Z0 => constr:(tt)
| ?f ?a => let b := zbase_ a in lazymatch b with tt => t | _ => constr:(f b) end
| _ => match goal with
| x := ?v |- _ => lazymatch t with x => zbase_ v end
| _ => t
end
end.
Ltac sfp_same lo hi W b k :=
lazymatch W with
| (?lk, _) :: ?W' =>
let bk := zbase_ lk in
first [ constr_eq b bk; eapply sub_fp_cons_in; [ in_pick k | sfp_cheap | sfp_cheap | ]
| sfp_same lo hi W' b (S k) ]
end.
Ltac sfp_head lo hi W :=
let Wn := eval cbv [app] in W in
first
[ let k := sfp_idx lo hi Wn O in eapply (sub_fp_cons_in lo hi lo hi); [ in_pick k | apply Z.le_refl | apply Z.le_refl | ]
| let b := zbase_ lo in sfp_same lo hi Wn b O
| let n := eval cbv in (length W) in
let rec try_cheap k :=
lazymatch (eval cbv in (Nat.ltb k n)) with
| true => first [ eapply sub_fp_cons_in; [ in_pick k | sfp_cheap | sfp_cheap | ] | try_cheap (S k) ]
| false => fail
end in
try_cheap O
| let n := eval cbv in (length W) in
let rec try_each k :=
lazymatch (eval cbv in (Nat.ltb k n)) with
| true => first [ eapply sub_fp_cons_in; [ in_pick k | lia | lia | ] | try_each (S k) ]
| false => fail 0 "sub_fp_solve: interval not inside the footprint:" lo hi
end in
try_each O ].
Ltac sub_fp_solve :=
lazymatch goal with
| |- sub_fp [] _ => apply sub_fp_nil'
| |- sub_fp ((?lo, ?hi) :: ?W2) ?W => sfp_head lo hi W; sub_fp_solve
end.

Ltac stk_top_ends W hi :=
first [ lazymatch W with context [pair _ hi] => idtac end
| match goal with H : bv_unsigned ?x = hi |- _ => lazymatch W with context [pair _ (bv_unsigned x)] => idtac end end ].
Ltac Q0z1.disjoint_goal ::=
lazymatch goal with
| |- disjoint_from ?W ?lo (?hi - ?lo) => tryif stk_top_ends W hi then fail "stk top ends a callee range" else idtac
| |- _ => idtac
end;
cbv [disjoint_from fst snd];
Q0z1.simpl_sizes_goal;
lazymatch goal with
| |- _ /\ _ /\ _ /\ _ => repeat split; Q0z1.transport_lia
| |- _ => Q0z1.transport_lia
end. Ltac mkr__disjoint_goal_1 := lazymatch goal with
| |- disjoint_from ?W ?lo (?hi - ?lo) => tryif stk_top_ends W hi then fail "stk top ends a callee range" else idtac
| |- _ => idtac
end;
cbv [disjoint_from fst snd];
Q0z1.simpl_sizes_goal;
lazymatch goal with
| |- _ /\ _ /\ _ /\ _ => repeat split; Q0z1.transport_lia
| |- _ => Q0z1.transport_lia
end.

Lemma munch_chain : forall W W2 m m0 m1,
munch W m m0 -> munch W2 m0 m1 -> sub_fp W2 W -> munch W m m1.
Proof. intros W W2 m m0 m1 A B S. eapply munch_trans; [exact A|]. eapply munch_weaken; [exact S| exact B]. Qed.

Ltac call_norm SPEC tac :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
eapply evt_cut;
[ eapply SPEC
| let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO; hnf in PO; tac PO; revert ms' PO; post_call segs m ]
end.

Ltac call_sp_norm SPEC tac :=
lazymatch goal with
| |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
name_sp sp k; call_norm SPEC tac; unname_sp
| |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
name_sp sp k; call_norm SPEC tac; unname_sp
| _ => call_norm SPEC tac
end.

Lemma munch_chain' : forall W2 m m1 W m0,
munch W2 m m1 -> munch W m0 m -> sub_fp W2 W -> munch W m0 m1.
Proof. intros W2 m m1 W m0 B A S. eapply munch_chain; [exact A| exact B| exact S]. Qed.

Ltac post_call_chain segs m :=
let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO;
destruct_exs PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
destruct PO as [E [MUc [WMc PO]]];
first [ destruct PO as [MIc PO] | rename PO into MIc ];
subst ms';
lazymatch type of MUc with
| munch _ m ?m' =>
repeat match goal with
| H : munch ?W ?m0 m |- _ =>
first [ apply (munch_chain' _ m m' W m0 MUc) in H; [| sub_fp_solve]
| fail 100 "callee footprint interval not inside the caller footprint (sub_fp_solve)" ]
end;
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try destruct_ands PO;
try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).

Ltac call_ch SPEC tac :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
eapply evt_cut;
[ eapply SPEC
| let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO; hnf in PO; tac PO; revert ms' PO; post_call_chain segs m ]
end.

Ltac call_sp_ch SPEC tac :=
lazymatch goal with
| |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
name_sp sp k; call_ch SPEC tac; unname_sp
| |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
name_sp sp k; call_ch SPEC tac; unname_sp
| _ => call_ch SPEC tac
end.

Lemma divu_word : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z ->
mul_div M_DIVU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a / b).
Proof.
intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia. replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
apply bv_eq_wrap. rewrite bv_divu_unsigned, (unsigned_lit a), (unsigned_lit b), Z_to_bv_unsigned by lia.
rewrite bv_wrap_bv_wrap by lia. reflexivity.
Qed.

Ltac enum_cases x lo hi :=
let rec go k :=
lazymatch (eval vm_compute in (Z.ltb hi k)) with
| true => exfalso; lia
| false => first [ replace x with k in * by lia | destruct (Z.eq_dec x k) as [->|?]; [| go (k + 1)%Z] ]
end in
go lo.

Ltac get_reg n k :=
lazymatch goal with
| |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let p := eval vm_compute in (Z.to_pos (n + 1)%Z) in
let v := eval cbv beta iota delta [tget] in (match tget p R with Some v => v | None => w0 end) in
k v
end.
