(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__ArtRegs () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "stdpp.bitvector.definitions."], [["1list"; "1prod"; "2eq"; "2not"; "3bvmap"; "4rcanon"; "4rchain"; "4rins"; "5regupd"; "0base"; "0i"; "0l"; "0r"; "0regs"; "0rg"; "0rg'"]; ["0s"; "6bv"; "0v"; "0v'"; "0x"; "0y"]]).
Lemma tset_tset_same {A} : forall (p : positive) (x y : A) t, tset p y (tset p x t) = tset p y t.
Proof.
induction p; intros x y [|l v r]; cbn; try reflexivity; rewrite ?IHp; reflexivity.
Qed.
Lemma tset_tset_comm {A} : forall (p q : positive) (x y : A) t, p <> q -> tset p x (tset q y t) = tset q y (tset p x t).
Proof.
induction p; intros q x y t Hne; destruct q; destruct t as [|l v r]; cbn; try reflexivity;
try (rewrite IHp by congruence; reflexivity); try congruence.
Qed.
Lemma regupd_shadow : ltac2:(TCodec.tc2 tcn__ArtRegs "E&4y5'AyR0%211%5241%415'2&8r4r3r2%43321r1%63241%73652%93;21pQ<=1pQ:>1pJ=1pL?1").
Proof. intros. unfold regupd, bvmap_set. apply tset_tset_same. Qed.
Lemma regupd_comm : ltac2:(TCodec.tc2 tcn__ArtRegs "L&4y5'AyR0%211%5241%415&3'2r4r3%33521%511&8r6r2%33271r5%53218%63529%731;5%=3@31p0:1pQ<C1pQ:D1pQ2C1pJD1pLF1").
Proof.
intros regs r s x y Hne. unfold regupd, bvmap_set. apply tset_tset_comm.
intros E. apply Hne. apply bv_key_inj. exact E.
Qed.
Lemma regupd_eq3 : ltac2:(TCodec.tc2 tcn__ArtRegs "K&4y5'AyR0%211%5241%415'2r5r4%33521r3r2%63921&8r7%23187r6%431:7%<3>31p071p0;1pQ8B1pQ6C1pFB1pQ0D1pNE1").
Proof. intros; subst; reflexivity. Qed.
Ltac reg_index r := lazymatch r with Z_to_bv 5 ?z => z | @BV 5 ?z _ => z | _ => constr:(100%Z) end.
Ltac rnorm_raw :=
repeat match goal with
| |- context [regupd (regupd ?rg ?s ?y) ?r ?x] =>
first [ constr_eq r s; rewrite (regupd_shadow rg r y x)
| let zr := eval cbv in (bv_unsigned r) in
let zs := eval cbv in (bv_unsigned s) in
lazymatch (eval cbv in (Z.ltb zr zs)) with
| true => rewrite (regupd_comm rg r s x y) by (let E := fresh in intros E; discriminate E)
end ]
end.
Ltac rnorm_old :=
lazymatch goal with
| |- ?REL ?segs (?mk ?R ?pc ?M ?rom) ?B =>
let mx := fresh "mx" in let bx := fresh "bx" in
set (mx := M); set (bx := B); rnorm_raw; subst mx bx
| |- _ => rnorm_raw
end.
Fixpoint rchain (base : bvmap 5 word) (l : list (reg * word)) : bvmap 5 word :=
match l with nil => base | (r, v) :: l' => regupd (rchain base l') r v end.
Fixpoint rins (r : reg) (v : word) (s : list (reg * word)) : list (reg * word) :=
match s with
| nil => (cons (r, v) nil)
| (r', v') :: tl =>
match Z.compare (bv_unsigned r') (bv_unsigned r) with
| Lt => (r, v) :: s
| Eq => (r, v) :: tl
| Gt => (r', v') :: rins r v tl
end
end.
Definition rcanon (l : list (reg * word)) : list (reg * word) := fold_right (fun rv s => rins (fst rv) (snd rv) s) nil l.
Lemma rins_ok : ltac2:(TCodec.tc2 tcn__ArtRegs "L&4y5'AyR0%211%5241%415'0'1%1235%311'2&6r4&7r3r2r1%43321%7261&8%9284%23176%<3B41pQ2>1pQ6E1pJD1pDF1").
Proof.
intros base r v s. induction s as [|[r' v'] tl IH]; [reflexivity|].
cbn [rins]. destruct (Z.compare (bv_unsigned r') (bv_unsigned r)) eqn:E.
- apply Z.compare_eq in E. apply bv_eq in E. subst r'. cbn [rchain]. symmetry. apply regupd_shadow.
- reflexivity.
- cbn [rchain]. rewrite IH. symmetry. apply regupd_comm. intros ->. rewrite Z.compare_refl in E. discriminate E.
Qed.
Lemma rchain_canon : ltac2:(TCodec.tc2 tcn__ArtRegs "F&4y5'AyR0%211%5241'0'1%617%2215%411'2&6r2&5r1%211%5241%6253%83>21pH:1pD@1").
Proof.
intros base l. induction l as [|[r v] l IH]; [reflexivity|].
unfold rcanon. cbn [fold_right fst snd]. fold (rcanon l). rewrite rins_ok, IH. reflexivity.
Qed.
Ltac zr_plit p := lazymatch p with xH => idtac | xO ?q => zr_plit q | xI ?q => zr_plit q end.
Ltac zr_idx r :=
lazymatch r with
| @BV 5 ?z _ => lazymatch z with Z0 => constr:(z) | Zpos ?p => let _ := constr:(ltac:(zr_plit p; exact tt)) in constr:(z) end
| Z_to_bv 5 ?z => lazymatch z with Z0 => constr:(z) | Zpos ?p => let _ := constr:(ltac:(zr_plit p; exact tt)) in let z' := eval cbv in (bv_unsigned r) in constr:(z') end
end.
Ltac zr_ins r v z l :=
lazymatch l with
| nil => constr:(cons (z, (r, v)) nil)
| cons (?z', (?r', ?v')) ?tl =>
let c := eval cbv in (Z.compare z' z) in
lazymatch c with
| Lt => constr:(cons (z, (r, v)) l)
| Eq => lazymatch r with r' => constr:(cons (z, (r, v)) tl) end
| Gt => let tl' := zr_ins r v z tl in constr:(cons (z', (r', v')) tl')
end
end.
Ltac zr_sort R :=
lazymatch R with
| regupd ?R' ?r ?v => let l := zr_sort R' in let z := zr_idx r in zr_ins r v z l
| _ => constr:(@nil (Z * (reg * word)))
end.
Ltac zr_list R := lazymatch R with regupd ?R' ?r ?v => let l := zr_list R' in constr:(cons (r, v) l) | _ => constr:(@nil (reg * word)) end.
Ltac zr_base R := lazymatch R with regupd ?R' _ _ => zr_base R' | _ => R end.
Ltac zr_build base l := lazymatch l with nil => base | cons (_, (?r, ?v)) ?tl => let R0 := zr_build base tl in constr:(regupd R0 r v) end.
Ltac rnorm_one R :=
let base := zr_base R in
let ls := zr_sort R in
let R' := zr_build base ls in
lazymatch R' with
| R => fail
| _ => let l0 := zr_list R in
let e := constr:(rchain_canon base l0 : R' = R) in
rewrite <- e
end.
Ltac rnorm_bad :=
match goal with
| |- context [regupd (regupd _ ?s _) ?r _] =>
first [ let zr := zr_idx r in let zs := zr_idx s in
let c := eval cbv in (Z.ltb zs zr) in
lazymatch c with true => fail 1 | false => idtac end
| idtac ]
end.
Ltac rnorm_all :=
repeat match goal with
| |- context [regupd (regupd ?rg ?s ?y) ?r ?x] =>
let zr := zr_idx r in let zs := zr_idx s in
let c := eval cbv in (Z.leb zr zs) in
lazymatch c with true => rnorm_one constr:(regupd (regupd rg s y) r x) end
end.
Ltac rnorm_new R := try rnorm_one R; rnorm_all; tryif rnorm_bad then rnorm_raw else idtac.
Ltac rnorm :=
lazymatch goal with
| |- ?REL ?segs (?mk ?R ?pc ?M ?rom) ?B =>
let mx := fresh "mx" in let bx := fresh "bx" in
set (mx := M); set (bx := B); rnorm_new R; subst mx bx
| |- _ => rnorm_all; tryif rnorm_bad then rnorm_raw else idtac
end.
