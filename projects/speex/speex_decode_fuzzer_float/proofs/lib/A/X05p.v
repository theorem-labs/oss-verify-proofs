(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1ct X1d5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma le1_lit : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2^64). rewrite <- Znumtheory.Zmod_div_mod; [reflexivity| lia| lia| exists (2^56); reflexivity].
Qed.
Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
rewrite (le1_lit z); mem_after_store
end).

Ltac is_Zlit_ x := lazymatch x with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac fold_lit_if_core :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
lazymatch c with
| negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) => is_Zlit_ x; is_Zlit_ y
| bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) => is_Zlit_ x; is_Zlit_ y
| negb (bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) => is_Zlit_ x; is_Zlit_ y
| bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) => is_Zlit_ x; is_Zlit_ y
| negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) => is_Zlit_ x; is_Zlit_ y
| bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) => is_Zlit_ x; is_Zlit_ y
end;
let v := eval vm_compute in c in
lazymatch v with
| true => change (evt segs Q (MS R F a fc rv m ro))
| false => change (evt segs Q (MS R F b fc rv m ro))
end
end.
Ltac fold_lit_if := first [ fold_lit_if_core | idtac ].
Ltac astep := zstep; fix_lit_store; fold_lit_if.

From Ltac2 Require Ltac2.
Module ChkL2.
Import Ltac2.
Ltac2 rec open_term (c : constr) : bool :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.App f args => if open_term f then true else Array.exist open_term args
| Constr.Unsafe.Cast c _ _ => open_term c
| Constr.Unsafe.Constant _ _ => false
| Constr.Unsafe.Ind _ _ => false
| Constr.Unsafe.Constructor _ _ => false
| Constr.Unsafe.Sort _ => false
| Constr.Unsafe.Uint63 _ => false
| _ => true
end.
Ltac2 assert_closed (c : constr) : unit :=
if open_term c then Control.zero (Tactic_failure (Some (Message.of_string "lit_if: the condition is not a closed term"))) else ().
End ChkL2.
Ltac assert_closed c := let f := ltac2:(c |- ChkL2.assert_closed (Option.get (Ltac1.to_constr c))) in f c.
Ltac lit_if :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
assert_closed c;
let v := eval vm_compute in c in
lazymatch v with
| true => change (evt segs Q (MS R F a fc rv m ro))
| false => change (evt segs Q (MS R F b fc rv m ro))
end
end.

Ltac alit_bin op a b := is_Zlit_ a; is_Zlit_ b; let v := eval vm_compute in (op a b) in change (op a b) with v.
Ltac alit1 :=
match goal with
| |- context [Z.b2z (Z.ltb ?a ?b)] => is_Zlit_ a; is_Zlit_ b; let v := eval vm_compute in (Z.b2z (Z.ltb a b)) in change (Z.b2z (Z.ltb a b)) with v
| |- context [Z.b2z (Z.eqb ?a ?b)] => is_Zlit_ a; is_Zlit_ b; let v := eval vm_compute in (Z.b2z (Z.eqb a b)) in change (Z.b2z (Z.eqb a b)) with v
| |- context [Z.sub ?a ?b] => alit_bin Z.sub a b
| |- context [Z.modulo ?a ?b] => alit_bin Z.modulo a b
| |- context [Z.land ?a ?b] => alit_bin Z.land a b
| |- context [Z.lor ?a ?b] => alit_bin Z.lor a b
| |- context [Z.shiftl ?a ?b] => alit_bin Z.shiftl a b
| |- context [Z.shiftr ?a ?b] => alit_bin Z.shiftr a b
| |- context [Z.mul ?a ?b] => alit_bin Z.mul a b
| |- context [Z.add ?a ?b] => alit_bin Z.add a b
| |- context [bv_swrap 32 ?a] => is_Zlit_ a; let v := eval vm_compute in (bv_swrap 32 a) in change (bv_swrap 32 a) with v
| |- context [bv_swrap 64 ?a] => is_Zlit_ a; let v := eval vm_compute in (bv_swrap 64 a) in change (bv_swrap 64 a) with v
end.
Ltac alits := repeat alit1.

Ltac show_pc_fail p := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 1 "ato" p ": stuck at" pc end.
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => idtac end.
Ltac at_if := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac end.
Ltac ato p := repeat (tryif at_pc p then fail else (tryif at_if then lit_if else astep)); first [ at_pc p | show_pc_fail p ].
Ltac show_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC" pc end.

Ltac show_regs :=
lazymatch goal with
| |- evt _ _ (MS ?R ?F ?pc _ _ _ _) =>
let r := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in
unify R r; idtac "PC" pc; idtac "REGS" r; idtac "FP" F
end.

Ltac addr_diff E A ::=
lazymatch E with
| A => constr:(0%Z)
| Z.add ?X ?c1 =>
lazymatch A with
| Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
| X => zlit c1
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
| _ =>
lazymatch A with
| Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
end.

Ltac addr_near k ::=
let inb := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 32768))%Z in
lazymatch inb with true => idtac end.

Definition sh_cur (P : Prop) : Prop := P.
Ltac chk_hint H := let T := type of H in pose proof (H : sh_cur T).

Ltac sh_base a :=
lazymatch a with
| Z.add ?x _ => sh_base x
| _ => a
end.

Ltac sh_rng := lia.

Ltac sh_mod := first [ assumption | lia | (Z.div_mod_to_equations; lia) ].
Ltac sh_gran :=
first [ apply al1_gran | lia | apply al4_gran; sh_mod | apply al8_gran; sh_mod | apply al2_gran; sh_mod ].

Ltac sh_is_base B := lazymatch B with SHB => idtac | 2147450880 => idtac end.

Ltac sh_find_obj segs mb a k :=
first
[ lazymatch goal with HC : sh_cur (aobj segs mb ?o ?n) |- _ => k HC o n end
| let o := sh_base a in
lazymatch goal with H : aobj segs mb o ?n |- _ => k H o n end ].

Ltac sh_free segs W mb o n H :=
match goal with
| SF : shfree W o n |- _ => constr:(SF)
| OF : offsh W |- _ => constr:(shfree_of_aobj segs W mb o n OF H)
end.

Ltac sh_with segs m a k :=
first
[ match goal with
| MU : munch ?W ?mb m |- _ =>
sh_find_obj segs mb a ltac:(fun H o n => let SF := sh_free segs W mb o n H in k W mb MU SF H o n)
end
| sh_find_obj segs m a ltac:(fun H o n => k (@nil ivl) m (munch_refl (@nil ivl) m) (shfree_nil o n) H o n) ].

Ltac sh_rewrite_load segs m a :=
sh_with segs m a ltac:(fun W mb MU SF H o n =>
first
[
lazymatch goal with
| AL : o mod 8 = 0 |- _ =>
lazymatch a with
| Z.add o ?d =>
let b := eval vm_compute in (fld_full d n) in
lazymatch b with true => rewrite (sh_rd0_fld segs W mb m o n d MU SF H AL (eq_refl true)) end
| o =>
let b := eval vm_compute in (fld_full 0 n) in
lazymatch b with true => rewrite (sh_rd0_fld0 segs W mb m o n MU SF H AL (eq_refl true)) end
end
end
|
rewrite (sh_rd segs W mb m o n a MU SF H ltac:(sh_rng)) ]).

Ltac sh_lit_addr_obj segs g k :=
match goal with
| H : aobj segs _ ?o ?n |- _ =>
is_Zlit_ o; is_Zlit_ n;
let inb := eval vm_compute in (andb (Z.leb o (g + 7)) (Z.ltb g (o + n))) in
lazymatch inb with
| true =>
let d := eval vm_compute in (Z.max 0 (g - o)) in
lazymatch d with
| Z0 => k constr:(o)
| _ => k constr:(o + d)
end
end
end.
Ltac sh_lit_addr :=
lazymatch goal with
| |- context [ov_read_bytes ?segs ?m (Z_to_bv 64 (?K + ?B)) 1%nat] =>

is_Zlit_ K; sh_is_base B;
let g := eval vm_compute in (8 * K) in
sh_lit_addr_obj segs g ltac:(fun a =>
change (ov_read_bytes segs m (Z_to_bv 64 (K + B)) 1%nat) with (ov_read_bytes segs m (Z_to_bv 64 (Z.shiftr a 3 + B)) 1%nat))
| |- context [ov_read_bytes ?segs ?m (Z_to_bv 64 ?L) 1%nat] =>
is_Zlit_ L;
let g := eval vm_compute in (8 * (L - SHB)) in
sh_lit_addr_obj segs g ltac:(fun a =>
change (ov_read_bytes segs m (Z_to_bv 64 L) 1%nat) with (ov_read_bytes segs m (Z_to_bv 64 (Z.shiftr a 3 + SHB)) 1%nat))
end.

Ltac solve_load_shadow :=
try sh_lit_addr;
lazymatch goal with
| |- context [ov_read_bytes ?segs ?m (Z_to_bv 64 (Z.shiftr ?a 3 + ?B)) 1%nat] =>
sh_is_base B; sh_rewrite_load segs m a; load_post;
rewrite ?sxb_z8, ?zxb_z8, ?sxb_shb
end.

Ltac solve_load ::= first [ solve_load_shadow | solve_load_base | solve_load_image ].

Ltac tree_abs R R1 x :=
lazymatch R with
| TNode ?l ?v ?r =>
lazymatch R1 with
| TNode ?l1 ?v1 ?r1 =>
let l' := tree_abs l l1 x in
let r' := tree_abs r r1 x in
let v' := lazymatch v with v1 => v | _ => constr:(Some x) end in
constr:(TNode l' v' r')
end
| _ => R
end.

Ltac tree_ndiff R R1 :=
lazymatch R with
| TNode ?l ?v ?r =>
lazymatch R1 with
| TNode ?l1 ?v1 ?r1 =>
let a := tree_ndiff l l1 in
let b := tree_ndiff r r1 in
let c := lazymatch v with v1 => constr:(0%nat) | _ => constr:(1%nat) end in
eval cbv in (a + b + c)%nat
end
| _ => constr:(0%nat)
end.

Ltac sh_cond :=
unfold_cond; rewrite ?sh_land7;
repeat match goal with |- context [Z.modulo ?a 8] =>
lazymatch goal with _ : 0 <= a mod 8 < 8 |- _ => fail | _ => pose proof (Z.mod_pos_bound a 8 ltac:(lia)) end end;
fold_lit_ux; rewrite ?signed_small64 by lia; rewrite ?unsigned_small64 by lia;
solve_cond_rec.
Ltac sh_if_true :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv_concl_iota| symmetry; sh_cond] end.
Ltac sh_if_false :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv_concl_iota| symmetry; sh_cond] end.
Ltac sh_if := first [ sh_if_true | sh_if_false ].

Ltac sh_if_first slow :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if negb _ then _ else _) _ _ _ _) =>
lazymatch slow with true => first [ sh_if_true | sh_if_false ] | false => first [ sh_if_false | sh_if_true ] end
| _ => lazymatch slow with true => first [ sh_if_false | sh_if_true ] | false => first [ sh_if_true | sh_if_false ] end
end.
Ltac sh_if_slow :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if negb _ then _ else _) _ _ _ _) => first [ sh_if_false | sh_if_true ]
| _ => first [ sh_if_true | sh_if_false ]
end.

Ltac sh_at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => idtac end.

Ltac sh_slow pj :=
tryif sh_at_pc pj then idtac
else (lazymatch goal with
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => sh_if_slow
| _ => astep
end; sh_slow pj).

Ltac sh_find_shb c :=
lazymatch c with
| context [shz ?segs ?mb ?a] => constr:((mb, a))
| context [shb ?segs ?mb ?a] => constr:((mb, a))
end.

Ltac chk_merge H N :=

first [ rename x into chk_merge_saved_x | idtac ];
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then Z_to_bv 64 ?pa else Z_to_bv 64 ?pb) ?fc ?rv ?m ?ro) =>
let pj := lazymatch c with negb _ => pb | _ => pa end in
let ma := sh_find_shb c in
lazymatch ma with
| (?mb, ?a) =>
lazymatch type of H with
| aobj _ mb ?o ?n =>
let SB := fresh "SB" in
pose proof (sh_fact segs mb o n a N H ltac:(sh_rng) ltac:(sh_rng) ltac:(lia) ltac:(sh_gran)) as SB;
let P := fresh "P" in
evar (P : Prop);
let CONT := fresh "CONT" in
cut P; subst P;
[ intro CONT; destruct SB as [SB|SB];
[
sh_if_first true; sh_slow pj;
lazymatch goal with
| |- evt _ _ (MS ?R1 _ _ _ _ _ _) =>
let nd := tree_ndiff R R1 in
lazymatch nd with
| 0%nat => exact CONT
| 1%nat =>
let T := constr:(forall x : word, evt segs Q (MS ltac:(let t := tree_abs R R1 x in exact t) F (Z_to_bv 64 pj) fc rv m ro)) in
let T' := eval cbv beta in T in
let TC := type of CONT in unify TC T'; apply CONT
| _ => fail 100 "chk_merge: the slow path changes more than one register"
end
end
| sh_if_first false; apply CONT ]
| clear SB;
first [ let v := fresh "chk_merge_new" in intro v;
first [ rename chk_merge_saved_x into x | idtac ];
let w := fresh "x" in rename v into w
| first [ rename chk_merge_saved_x into x | idtac ] ] ]
end
end
end.

Ltac tlia_one := olia ltac:(
sf_clear_big;
first [ Zify.zify; xlia zchecker
| match goal with H : hid (_ \/ _) |- _ => unfold hid in H; Zify.zify; xlia zchecker end
| unfold hid in *; sf_unhide;
first [ zify_prune_neg; Zify.zify; xlia zchecker | zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ]).
