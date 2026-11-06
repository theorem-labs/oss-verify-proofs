(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK0d.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1e YK0c.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Module AX2B.
Import AX2.
Create HintDb bceq discriminated.
Lemma p_aluop_eqb_eq : forall a b, aluop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
Lemma p_mulop_eqb_eq : forall a b, mulop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
Lemma p_expr_eqb_eq : forall x y, expr_eqb x y = true -> x = y.
Proof.
induction x; destruct y; cbn; intros H; try discriminate;
repeat match goal with
| H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
end;
repeat match goal with
| H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
| H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
| H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
| H : aluop_eqb _ _ = true |- _ => apply p_aluop_eqb_eq in H
| H : mulop_eqb _ _ = true |- _ => apply p_mulop_eqb_eq in H
| H : expr_eqb ?a _ = true, IH : forall y, expr_eqb ?a y = true -> _ |- _ => apply IH in H
end; subst; reflexivity.
Qed.
Fixpoint first_var (e : expr) : option nat :=
match e with
| ELit _ => None
| EVar n => Some n
| EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b =>
match first_var a with Some n => Some n | None => first_var b end
| EExt _ _ _ a => first_var a
| EBlob _ _ _ _ => None
end.
Definition vkey_of (e : expr) : option nat := first_var (fst (lit_strip e)).
Fixpoint lset {A : Type} (l : list (list A)) (n : nat) (x : A) {struct n} : list (list A) :=
match n, l with
| O, [] => [[x]]
| O, b :: rest => (x :: b) :: rest
| S m, [] => [] :: lset [] m x
| S m, b :: rest => b :: lset rest m x
end.
Definition lget {A : Type} (l : list (list A)) (n : nat) : list A := nth n l [].
Lemma lget_lset : forall (A : Type) (l : list (list A)) n x m,
lget (lset l n x) m = if Nat.eqb m n then x :: lget l m else lget l m.
Proof.
intros A l n. revert l. unfold lget. induction n as [|n IH]; intros l x m; destruct l as [|b rest]; destruct m as [|m]; cbn [lset nth Nat.eqb]; try reflexivity.
- destruct m; reflexivity.
- rewrite IH. destruct (Nat.eqb m n); destruct m; reflexivity.
- apply IH.
Qed.
Record rindex := RI { ri_vars : list (list kentry); ri_other : list kentry }.
Definition ri_bucket (ri : rindex) (k : option nat) : list kentry :=
match k with Some n => lget (ri_vars ri) n | None => ri_other ri end.
Fixpoint mk_ri (fk : list kentry) : rindex :=
match fk with
| [] => RI [] []
| K :: rest =>
let t := mk_ri rest in
match K with
| KRange e' _ _ =>
match vkey_of e' with
| Some n => RI (lset (ri_vars t) n K) (ri_other t)
| None => RI (ri_vars t) (K :: ri_other t)
end
| _ => t
end
end.
Definition find_rangeI (ri : rindex) (e : expr) : option (Z * Z) := find_range (ri_bucket ri (vkey_of e)) e.
Definition okey_eqb (a b : option nat) : bool :=
match a, b with Some x, Some y => Nat.eqb x y | None, None => true | _, _ => false end.
Lemma okey_eqb_spec : forall a b, reflect (a = b) (okey_eqb a b).
Proof.
intros [x|] [y|]; cbn; try (constructor; congruence).
destruct (Nat.eqb_spec x y); constructor; congruence.
Qed.
Lemma ri_bucket_cons : forall t K e' lo hi k,
K = KRange e' lo hi ->
ri_bucket (match vkey_of e' with
| Some n => RI (lset (ri_vars t) n K) (ri_other t)
| None => RI (ri_vars t) (K :: ri_other t)
end) k
= if okey_eqb k (vkey_of e') then K :: ri_bucket t k else ri_bucket t k.
Proof.
intros t K e' lo hi k ->. destruct (vkey_of e') as [n|] eqn:Ev; destruct k as [m|]; cbn [ri_bucket ri_vars ri_other okey_eqb]; try reflexivity.
apply lget_lset.
Qed.
Lemma find_rangeI_eq : forall fk e, find_rangeI (mk_ri fk) e = find_range fk e.
Proof.
intros fk e. unfold find_rangeI. induction fk as [|K rest IH].
- cbn [mk_ri]. destruct (vkey_of e) as [n|]; cbn; [unfold lget; destruct n; reflexivity | reflexivity].
- cbn [mk_ri]. destruct K as [a w v|a l|a l bk|lo hi|e1 m|e' lo hi|a n|a1 n1 a2 n2|a l c|a l];
cbn [find_range]; rewrite <- ?IH; try reflexivity.
rewrite (ri_bucket_cons (mk_ri rest) _ e' lo hi _ eq_refl).
destruct (okey_eqb_spec (vkey_of e) (vkey_of e')) as [EQ|NE].
+ cbn [find_range]. rewrite IH. reflexivity.
+ rewrite IH. destruct (expr_eqb e e') eqn:Ee.
* exfalso. apply NE. apply p_expr_eqb_eq in Ee. subst. reflexivity.
* destruct (lit_strip e) as [v c] eqn:Lx. destruct (lit_strip e') as [v' c'] eqn:Le'.
destruct (expr_eqb v v') eqn:Ev.
-- exfalso. apply NE. unfold vkey_of. rewrite Lx, Le'. cbn [fst]. apply p_expr_eqb_eq in Ev. subst. reflexivity.
-- destruct e; reflexivity.
Qed.
Record bctx : Type := BC {
bc_fk : list kentry;
bc_ffk : list kentry;
bc_fs : list sfact;
bc_ri : rindex
}.
Definition mkbc0 (fk : list kentry) (fs : list sfact) : bctx :=
BC fk (facts_of fk) fs (mk_ri (facts_of fk)).
Lemma lin_range_ext : forall r1 r2 c ts, (forall a, r1 a = r2 a) -> lin_range r1 c ts = lin_range r2 c ts.
Proof. intros r1 r2 c ts H. induction ts as [|[k a] rest IH]; [reflexivity|]. cbn [lin_range]. rewrite H, IH. reflexivity. Qed.
Ltac beq_crush rw :=
repeat (first [ reflexivity
| progress rw
| lazymatch goal with
| |- ?L = _ =>
lazymatch L with
| (if ?c then _ else _) => destruct c
| (match ?x with _ => _ end) => destruct x
end
end ]).
Fixpoint erange_fB (fuel : nat) (bc : bctx) (e : expr) {struct fuel} : option (Z * Z) :=
match fuel with
| O => None
| S fuel' =>
let erange := erange_fB fuel' in
match find_rangeI (bc_ri bc) e with
| Some r => Some (clampi r)
| None =>
match (let l := lin_of e in
if lin_trivial l then None
else match lin_range (erange bc) (fst l) (snd l) with
| Some (lo, hi) =>
let q := zdiv64 lo in
if Z.eqb q (zdiv64 hi) then Some ((lo - q * two64)%Z, (hi - q * two64)%Z) else None
| None => None
end) with
| Some r => Some r
| None =>
match e with
| ELit z => let v := zmod64 z in Some (v, v)
| EVar _ => None
| EAlu op a b =>
match op with
| ALU_ADD =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) =>
if Z.ltb (ah + bh) two64 then Some ((al + bl)%Z, (ah + bh)%Z)
else if Z.leb two64 (al + bl) then Some ((al + bl - two64)%Z, (ah + bh - two64)%Z)
else None
| _, _ => None
end
| ALU_SUB =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) =>
if Z.leb bh al then Some ((al - bh)%Z, (ah - bl)%Z)
else if Z.ltb ah bl then Some ((al - bh + two64)%Z, (ah - bl + two64)%Z)
else None
| _, _ => None
end
| ALU_AND =>
match (match b, erange bc a with
| ELit m, Some (al, ah) =>
let m' := (m mod two64)%Z in
let j := Z.log2 (m' + 1) in
if (Z.eqb (m' + 1) (2 ^ j) && Z.leb (al / 2 ^ j) (ah / 2 ^ j) && Z.eqb (al / 2 ^ j) (ah / 2 ^ j))%bool
then Some ((al mod 2 ^ j)%Z, (ah mod 2 ^ j)%Z)
else let jh := Z.log2 (two64 - m') in
if (Z.eqb (two64 - m') (2 ^ jh) && Z.ltb jh 64)%bool
then Some ((al - al mod 2 ^ jh)%Z, (ah - ah mod 2 ^ jh)%Z)
else None
| _, _ => None
end) with
| Some r => Some r
| None =>
match erange bc a, erange bc b with
| Some (_, ah), Some (_, bh) => Some (0%Z, Z.min ah bh)
| Some (_, ah), None => Some (0%Z, ah)
| None, Some (_, bh) => Some (0%Z, bh)
| None, None => None
end
end
| ALU_OR =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) => Some (Z.max al bl, mask_cover (Z.max ah bh))
| _, _ => None
end
| ALU_XOR =>
match erange bc a, erange bc b with
| Some (_, ah), Some (_, bh) => Some (0%Z, mask_cover (Z.max ah bh))
| _, _ => None
end
| ALU_SRL =>
match erange bc a, lit_shamt b with
| Some (al, ah), Some s => Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z)
| _, _ => None
end
| ALU_SRA =>
match erange bc a, lit_shamt b with
| Some (al, ah), Some s =>
if Z.ltb ah (2 ^ 63) then Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z) else None
| _, _ => None
end
| ALU_SLL =>
match erange bc a, lit_shamt b with
| Some (al, ah), Some s =>
if Z.ltb (ah * 2 ^ s) two64 then Some ((al * 2 ^ s)%Z, (ah * 2 ^ s)%Z) else None
| _, _ => None
end
| ALU_SLTU =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) =>
if Z.ltb ah bl then Some (1%Z, 1%Z)
else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z)
| _, _ => Some (0%Z, 1%Z)
end
| ALU_SLT =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) =>
if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool then
(if Z.ltb ah bl then Some (1%Z, 1%Z)
else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z))
else Some (0%Z, 1%Z)
| _, _ => Some (0%Z, 1%Z)
end
end
| EAluw op a b =>
match op with
| ALU_ADD =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) =>
let bl' := if Z.eqb bl bh then zsigned64 bl else bl in
let bh' := if Z.eqb bl bh then zsigned64 bh else bh in
if (Z.leb 0 (al + bl') && Z.ltb (ah + bh') (2 ^ 31))%bool
then Some ((al + bl')%Z, (ah + bh')%Z) else None
| _, _ => None
end
| ALU_SUB =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) =>
if (Z.leb bh al && Z.ltb (ah - bl) (2 ^ 31))%bool
then Some ((al - bh)%Z, (ah - bl)%Z) else None
| _, _ => None
end
| ALU_SLL =>
match erange bc a, lit_shamt b with
| Some (al, ah), Some s =>
let s' := (s mod 32)%Z in
if Z.ltb (ah * 2 ^ s') (2 ^ 31) then Some ((al * 2 ^ s')%Z, (ah * 2 ^ s')%Z) else None
| _, _ => None
end
| ALU_SRL =>
match erange bc a, lit_shamt b with
| Some (al, ah), Some s =>
let s' := (s mod 32)%Z in
if (Z.ltb ah (2 ^ 32) && (Z.ltb 0 s' || Z.ltb ah (2 ^ 31)))%bool
then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
| _, _ => None
end
| ALU_SRA =>
match erange bc a, lit_shamt b with
| Some (al, ah), Some s =>
let s' := (s mod 32)%Z in
if Z.ltb ah (2 ^ 31) then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
| _, _ => None
end
| _ => None
end
| EMd op a b =>
match op with
| M_MUL =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) =>
if (Z.leb 0 al && Z.leb 0 bl && Z.ltb (ah * bh) two64)%bool
then Some ((al * bl)%Z, (ah * bh)%Z) else None
| _, _ => None
end
| M_MULHU =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) =>
if (Z.leb 0 al && Z.leb 0 bl)%bool
then Some ((al * bl / two64)%Z, (ah * bh / two64)%Z) else None
| _, _ => None
end
| M_DIVU =>
match erange bc a, b with
| Some (al, ah), ELit d =>
let d' := (d mod two64)%Z in
if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
| _, _ => None
end
| M_REMU =>
match erange bc a, b with
| Some (al, ah), ELit d =>
let d' := (d mod two64)%Z in
if Z.ltb 0 d' then Some (0%Z, Z.min ah (d' - 1)) else None
| _, _ => None
end
| _ => None
end
| EMdw _ _ _ => None
| EExt sx lo n a =>
let w := (2 ^ (8 * Z.of_nat n))%Z in
if sx then
match lo, erange bc a with
| O, Some (al, ah) =>
if (Z.leb 0 al && Z.ltb ah (w / 2))%bool then Some (al, ah)
else if (Nat.leb 1 n && Nat.leb n 8 && Z.leb (w / 2) al && Z.ltb ah w)%bool
then Some ((two64 - w + al)%Z, (two64 - w + ah)%Z) else None
| _, _ => None
end
else
match lo, erange bc a with
| O, Some (al, ah) =>
if (Z.leb 0 al && Z.ltb ah w)%bool then Some (al, ah) else Some (0%Z, Z.min (w - 1) (two64 - 1))
| _, _ => Some (0%Z, Z.min (w - 1) (two64 - 1))
end
| EBlob sx k i n =>
if sx then Some (0%Z, two64m1) else Some (0%Z, Z.min (2 ^ (8 * Z.of_nat n) - 1) (two64 - 1))%Z
end
end
end
end.
Definition erange0B (bc : bctx) (e : expr) : option (Z * Z) := erange_fB erange_fuel bc e.
Definition erangeB (bc : bctx) (e : expr) : option (Z * Z) :=
let r := erange0B bc e in
let '(e', s) := deand e in
if Z.eqb s 0 then r else
match erange0B bc (unlin (lin_of e')) with
| Some (lo', hi') =>
if Z.leb s lo' then
match r with
| Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
| None => Some ((lo' - s)%Z, hi')
end
else r
| None => r
end.
Definition base_rangeB (bc : bctx) (e : expr) : option (Z * Z) :=
match e with ELit z => let v := (z mod two64)%Z in Some (v, v) | _ => erangeB bc e end.
Definition ealignB (bc : bctx) (e : expr) : Z := Z.max (ealign0 (bc_ffk bc) e) (pageup_align e).
Definition lin_nowrapB (bc : bctx) (e : expr) : bool :=
let l := lin_of e in
match lin_range (erangeB bc) (fst l) (snd l) with
| Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
| None => false
end.
Fixpoint srl_expandB (bc : bctx) (ts : list (Z * expr)) : Z * list (Z * expr) :=
match ts with
| [] => (0%Z, [])
| (k, a) :: rest =>
let '(c, ts') := srl_expandB bc rest in
let keep := (c, lins_e k a ts') in
match a with
| EAlu ALU_SRL e (ELit s) =>
let m := (2 ^ ((s mod two64) mod 64))%Z in
if (Z.eqb (k mod m)%Z 0%Z && lin_nowrapB bc e)%bool then
let q := (k / m)%Z in
let le := lin_of e in
if Z.leb ((s mod two64) mod 64) (ealignB bc e) then
((c + q * fst le)%Z, fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le))
else
((c + q * fst le)%Z,
lins_e (- q)%Z (srl_rem e m) (fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le)))
else keep
| EAlu ALU_AND e (ELit mk) =>
match highmask_s mk with
| Some s =>
if lin_nowrapB bc e then
let le := lin_of e in
((c + k * fst le)%Z,
lins_e (- k)%Z (srl_rem e (2 ^ s)) (fold_right (fun t acc => lins_e (k * fst t)%Z (snd t) acc) ts' (snd le)))
else keep
| None => keep
end
| _ => keep
end
end.
Definition fact_nowrapB (bc : bctx) (e : expr) (hi : Z) : bool :=
let l := lin_of e in
match lin_range (erangeB bc) (fst l) (snd l) with
| Some (a, b) => (Z.ltb b two64 && Z.ltb hi (a + two64))%bool
| None => false
end.
Definition sum_fact_xB (bc : bctx) (ts : list (Z * expr)) (lo hi : Z) : list sfact :=
let '(c2, ts2) := srl_expandB bc ts in
match ts2 with
| _ :: _ => if Z.eqb c2 0 then [] else [(ts2, ((lo - c2)%Z, (hi - c2)%Z))]
| [] => []
end.
Fixpoint sum_factsB (bc : bctx) (kn : list kentry) : list sfact :=
match kn with
| [] => []
| KRange e lo hi :: rest =>
match e with
| EVar _ => sum_factsB bc rest
| _ =>
match lin_of e with
| (c, (_ :: _ :: _) as ts) =>
if fact_nowrapB bc e hi then (ts, ((lo - c)%Z, (hi - c)%Z)) :: sum_fact_xB bc ts (lo - c)%Z (hi - c)%Z ++ sum_factsB bc rest
else sum_factsB bc rest
| _ => sum_factsB bc rest
end
end
| _ :: rest => sum_factsB bc rest
end.
Lemma bc_fk_mkbc0 : forall fk fs, bc_fk (mkbc0 fk fs) = fk. Proof. reflexivity. Qed.
Lemma bc_ffk_mkbc0 : forall fk fs, bc_ffk (mkbc0 fk fs) = facts_of fk. Proof. reflexivity. Qed.
Lemma find_rangeI_mkbc0 : forall fk fs, find_rangeI (bc_ri (mkbc0 fk fs)) = find_range (facts_of fk).
Proof. intros. apply functional_extensionality. intros e. apply find_rangeI_eq. Qed.
#[export] Hint Rewrite bc_fk_mkbc0 bc_ffk_mkbc0 find_rangeI_mkbc0 : bceq.
Ltac bcfe := repeat (apply functional_extensionality; intros ?).
Lemma erange_fB_eqf0 : forall fk fs fuel, erange_fB fuel (mkbc0 fk fs) = erange_f fuel (facts_of fk).
Proof.
intros fk fs fuel. induction fuel as [|f IH]; bcfe; [reflexivity|].
cbn [erange_fB erange_f]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite erange_fB_eqf0 : bceq.
Lemma erange0B_eqf0 : forall fk fs, erange0B (mkbc0 fk fs) = erange0 fk.
Proof. intros. bcfe. unfold erange0B, erange0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite erange0B_eqf0 : bceq.
Lemma erangeB_eqf0 : forall fk fs, erangeB (mkbc0 fk fs) = erange fk.
Proof. intros. bcfe. unfold erangeB, erange. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite erangeB_eqf0 : bceq.
Lemma base_rangeB_eqf0 : forall fk fs, base_rangeB (mkbc0 fk fs) = base_range fk.
Proof. intros. bcfe. unfold base_rangeB, base_range. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite base_rangeB_eqf0 : bceq.
Lemma ealignB_eqf0 : forall fk fs, ealignB (mkbc0 fk fs) = ealign fk.
Proof. intros. bcfe. unfold ealignB, ealign. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ealignB_eqf0 : bceq.
Lemma lin_nowrapB_eqf0 : forall fk fs, lin_nowrapB (mkbc0 fk fs) = lin_nowrap fk.
Proof. intros. bcfe. unfold lin_nowrapB, lin_nowrap. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_nowrapB_eqf0 : bceq.
Lemma srl_expandB_eqf0 : forall fk fs, srl_expandB (mkbc0 fk fs) = srl_expand fk.
Proof.
intros fk fs. apply functional_extensionality; intros ts.
induction ts as [|[k a] rest IH]; intros; bcfe; [reflexivity|].
cbn [srl_expandB srl_expand]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite srl_expandB_eqf0 : bceq.
Lemma fact_nowrapB_eqf0 : forall fk fs, fact_nowrapB (mkbc0 fk fs) = fact_nowrap fk.
Proof. intros. bcfe. unfold fact_nowrapB, fact_nowrap. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite fact_nowrapB_eqf0 : bceq.
Lemma sum_fact_xB_eqf0 : forall fk fs, sum_fact_xB (mkbc0 fk fs) = sum_fact_x fk.
Proof. intros. bcfe. unfold sum_fact_xB, sum_fact_x. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sum_fact_xB_eqf0 : bceq.
Lemma sum_factsB_eqf0 : forall fk fs, sum_factsB (mkbc0 fk fs) = sum_facts fk.
Proof.
intros fk fs. apply functional_extensionality; intros kn.
induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [sum_factsB sum_facts]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite sum_factsB_eqf0 : bceq.
Definition mkbc (fk : list kentry) : bctx := mkbc0 fk (sum_factsB (mkbc0 fk []) fk).
Lemma bc_fk_mkbc : forall fk, bc_fk (mkbc fk) = fk. Proof. reflexivity. Qed.
Lemma bc_ffk_mkbc : forall fk, bc_ffk (mkbc fk) = facts_of fk. Proof. reflexivity. Qed.
Lemma bc_fs_mkbc : forall fk, bc_fs (mkbc fk) = sum_facts fk fk.
Proof. intros. unfold mkbc. cbn [bc_fs mkbc0]. rewrite sum_factsB_eqf0. reflexivity. Qed.
Lemma find_rangeI_mkbc : forall fk, find_rangeI (bc_ri (mkbc fk)) = find_range (facts_of fk).
Proof. intros. unfold mkbc. apply find_rangeI_mkbc0. Qed.
#[export] Hint Rewrite bc_fk_mkbc bc_ffk_mkbc bc_fs_mkbc find_rangeI_mkbc : bceq.
Lemma erange_fB_eqf : forall fk fuel, erange_fB fuel (mkbc fk) = erange_f fuel (facts_of fk).
Proof. intros. unfold mkbc. apply erange_fB_eqf0. Qed.
#[export] Hint Rewrite erange_fB_eqf : bceq.
Lemma erange0B_eqf : forall fk, erange0B (mkbc fk) = erange0 fk.
Proof. intros. unfold mkbc. apply erange0B_eqf0. Qed.
#[export] Hint Rewrite erange0B_eqf : bceq.
Lemma erangeB_eqf : forall fk, erangeB (mkbc fk) = erange fk.
Proof. intros. unfold mkbc. apply erangeB_eqf0. Qed.
#[export] Hint Rewrite erangeB_eqf : bceq.
Lemma base_rangeB_eqf : forall fk, base_rangeB (mkbc fk) = base_range fk.
Proof. intros. unfold mkbc. apply base_rangeB_eqf0. Qed.
#[export] Hint Rewrite base_rangeB_eqf : bceq.
Lemma ealignB_eqf : forall fk, ealignB (mkbc fk) = ealign fk.
Proof. intros. unfold mkbc. apply ealignB_eqf0. Qed.
#[export] Hint Rewrite ealignB_eqf : bceq.
Lemma lin_nowrapB_eqf : forall fk, lin_nowrapB (mkbc fk) = lin_nowrap fk.
Proof. intros. unfold mkbc. apply lin_nowrapB_eqf0. Qed.
#[export] Hint Rewrite lin_nowrapB_eqf : bceq.
Lemma srl_expandB_eqf : forall fk, srl_expandB (mkbc fk) = srl_expand fk.
Proof. intros. unfold mkbc. apply srl_expandB_eqf0. Qed.
#[export] Hint Rewrite srl_expandB_eqf : bceq.
Lemma fact_nowrapB_eqf : forall fk, fact_nowrapB (mkbc fk) = fact_nowrap fk.
Proof. intros. unfold mkbc. apply fact_nowrapB_eqf0. Qed.
#[export] Hint Rewrite fact_nowrapB_eqf : bceq.
Lemma sum_fact_xB_eqf : forall fk, sum_fact_xB (mkbc fk) = sum_fact_x fk.
Proof. intros. unfold mkbc. apply sum_fact_xB_eqf0. Qed.
#[export] Hint Rewrite sum_fact_xB_eqf : bceq.
Lemma sum_factsB_eqf : forall fk, sum_factsB (mkbc fk) = sum_facts fk.
Proof. intros. unfold mkbc. apply sum_factsB_eqf0. Qed.
#[export] Hint Rewrite sum_factsB_eqf : bceq.
Definition lin_test_relB (bc : bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
match bc_fs bc with
| [] => false
| fs =>
match sum_subst fs ts 0 0 false with
| (ts', (lo0, hi0), true) =>
match lin_range (erangeB bc) c ts' with
| Some (lo, hi) => test (lo + lo0)%Z (hi + hi0)%Z
| None => false
end
| _ => false
end
end.
Definition lin_testB (bc : bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
match lin_range (erangeB bc) c ts with
| Some (lo, hi) => if test lo hi then true else lin_test_relB bc c ts test
| None => lin_test_relB bc c ts test
end.
Definition lin_srangeB (bc : bctx) (e : expr) : option (Z * Z) :=
let l := lin_of e in
let j := srl_scale_need (snd l) in
if (if Z.leb 0 j then Z.leb j 24 else false) then
let sc := (2 ^ j)%Z in
let ts := List.map (fun t => ((sc * fst t)%Z, snd t)) (snd l) in
let '(c2, t2) := srl_expandB bc ts in
let '(c3, t3) := (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) in
match lin_range (erangeB bc) (sc * fst l + c2 + c3)%Z t3 with
| Some (lo', hi') =>
let lo := zcdiv lo' sc in let hi := (hi' / sc)%Z in
if (if Z.leb 0 lo then (if Z.leb lo hi then Z.ltb hi two64 else false) else false) then Some (lo, hi) else None
| None => None
end
else None.
Definition lin_nowrapRB (bc : bctx) (e : expr) : bool :=
let l := lin_of e in
let '(c2, t2) := srl_expandB bc (snd l) in
if lin_testB bc (fst l + c2)%Z t2 (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%bool) then true
else
match lin_srangeB bc e with Some _ => true | None => false end.
Definition lin_apart0B (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
(lin_nowrapRB bc b1 && lin_nowrapRB bc b2 &&
let l1 := lin_of b1 in let l2 := lin_of b2 in
lin_testB bc (fst l2 + k2 - fst l1 - k1)%Z (lsub_e (snd l2) (snd l1))
(fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%bool))%bool.
Definition lin_apartB (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
if shares_var b1 b2 then lin_apart0B bc b1 k1 n1 b2 k2 n2 else false.
Definition lin_brangeB (bc : bctx) (e : expr) : option (Z * Z) :=
let l := lin_of e in
match bc_fs bc with
| [] => None
| fs =>
match sum_subst fs (snd l) 0 0 false with
| (ts', (lo0, hi0), true) =>
match lin_range (erangeB bc) (fst l) ts' with
| Some (lo, hi) =>
let lo' := (lo + lo0)%Z in let hi' := (hi + hi0)%Z in
if (Z.leb 0 lo' && Z.ltb hi' two64)%bool then Some (lo', hi') else None
| None => None
end
| _ => None
end
end.
Definition xloB (bc : bctx) (e : expr) : option Z :=
match e with
| ELit z => Some (zlit64 z)
| _ => match erangeB bc e with
| Some (lo, _) => Some lo
| None => match lin_brangeB bc e with
| Some (lo, _) => Some lo
| None => match lin_srangeB bc e with Some (lo, _) => Some lo | None => None end
end
end
end.
Definition xhiB (bc : bctx) (e : expr) : option Z :=
match e with
| ELit z => Some (zlit64 z)
| _ => match erangeB bc e with
| Some (_, hi) => Some hi
| None => match lin_brangeB bc e with
| Some (_, hi) => Some hi
| None => match lin_srangeB bc e with Some (_, hi) => Some hi | None => None end
end
end
end.
Fixpoint xt_nowrapB (bc : bctx) (ts : xterms) : bool :=
match ts with [] => true | (e, _) :: r => lin_nowrapRB bc e && xt_nowrapB bc r end.
Definition lin_ge0_scaledB (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
let j := srl_scale_need ts in
if (if Z.ltb 0 j then Z.leb j 24 else false) then
let sc := (2 ^ j)%Z in
let ts' := List.map (fun t => ((sc * fst t)%Z, snd t)) ts in
let '(c2, t2) := srl_expandB bc ts' in
let '(c3, t3) := (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) in
lin_testB bc (sc * c + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
else false.
Definition lin_ge0B (bc : bctx) (pos neg : xterms) : bool :=
(xt_nowrapB bc pos && xt_nowrapB bc neg &&
(if lin_testB bc (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) (fun lo _ => Z.leb 0 lo) then true
else let '(c2, t2) := srl_expandB bc (lsub_e (xt_lin pos) (xt_lin neg)) in
if lin_testB bc (xt_const pos - xt_const neg + c2)%Z t2 (fun lo _ => Z.leb 0 lo) then true
else
if (if has_srl t2 then
let '(c3, t3) := srl_expandB bc t2 in
lin_testB bc (xt_const pos - xt_const neg + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
else false) then true
else
lin_ge0_scaledB bc (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg))))%bool.
Definition xinside0B (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
if lin_ge0B bc [(b1, k1)] [(b2, k2)] then lin_ge0B bc [(b2, k2); (n2, 0%Z)] [(b1, k1); (n1, 0%Z)] else false.
Definition xinside_numB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
match xloB bc b2, xhiB bc b2 with
| Some lo2, Some hi2 =>
if Z.eqb lo2 hi2 then
match base_rangeB bc b1, xhiB bc n1, xloB bc n2 with
| Some (lo1, hi1), Some h1, Some l2 => Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2)
| _, _, _ => false
end
else false
| _, _ => false
end.
Definition xinsideB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
if shares_var b1 b2 then xinside0B bc b1 k1 n1 b2 k2 n2
else if novars b2 then xinside_numB bc b1 k1 n1 b2 k2 n2 else false.
Definition sub_itvB (bc : bctx) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
else false)
then true
else
if (Z.leb 0 n && Z.ltb n two64)%bool then xinsideB bc b k (ELit n) (a_base c) (a_off c) m else false.
Fixpoint kdisj_apartB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
match kn with
| [] => false
| KDisj c1 m1 c2 m2 :: rest =>
if (if sub_itvB bc b1 k1 n1 c1 m1 then sub_itvB bc b2 k2 n2 c2 m2 else false) then true
else if (if sub_itvB bc b1 k1 n1 c2 m2 then sub_itvB bc b2 k2 n2 c1 m1 else false) then true
else kdisj_apartB bc rest b1 k1 n1 b2 k2 n2
| _ :: rest => kdisj_apartB bc rest b1 k1 n1 b2 k2 n2
end.
Definition ranges_apartB (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
if (match base_rangeB bc b1, base_rangeB bc b2 with
| Some (lo1, hi1), Some (lo2, hi2) =>
(Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
| _, _ => false
end) then true
else if kdisj_apartB bc (bc_fk bc) b1 k1 n1 b2 k2 n2 then true
else lin_apartB bc b1 k1 n1 b2 k2 n2.
Definition sub_itv_xB (bc : bctx) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
xinsideB bc b k n (a_base c) (a_off c) m.
Fixpoint kdisj_apart_xB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
match kn with
| [] => false
| KDisj c1 m1 c2 m2 :: rest =>
if (if sub_itv_xB bc b1 k1 n1 c1 m1 then sub_itv_xB bc b2 k2 n2 c2 m2 else false) then true
else if (if sub_itv_xB bc b1 k1 n1 c2 m2 then sub_itv_xB bc b2 k2 n2 c1 m1 else false) then true
else kdisj_apart_xB bc rest b1 k1 n1 b2 k2 n2
| _ :: rest => kdisj_apart_xB bc rest b1 k1 n1 b2 k2 n2
end.
Definition end_hiB (bc : bctx) (b : expr) (k : Z) (n : expr) (lo1 hi1 h1 : Z) : option Z :=
match n with
| ELit _ => None
| _ => if (if Z.leb 0 (lo1 + k) then Z.ltb (hi1 + k + h1) two64 else false)
then match find_rangeI (bc_ri bc) (mkAlu ALU_ADD (mkAlu ALU_ADD b (ELit k)) n) with
| Some (_, ehi) => Some ehi
| None => None
end
else None
end.
Definition ranges_apart_xB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
match n1, n2 with
| ELit z1, ELit z2 => ranges_apartB bc b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)
| _, _ =>
if (match base_rangeB bc b1, base_rangeB bc b2, xhiB bc n1, xhiB bc n2 with
| Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
else
if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
| _, _, _, _ => false
end) then true
else if kdisj_apart_xB bc (bc_fk bc) b1 k1 n1 b2 k2 n2 then true
else if negb (shares_var b1 b2) then false
else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
end.
Fixpoint disj_sidesB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
match kn with
| [] => []
| KDisj c1 m1 c2 m2 :: rest =>
let r := disj_sidesB bc rest b1 k1 n1 in
let r1 := if sub_itvB bc b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
if sub_itvB bc b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
| _ :: rest => disj_sidesB bc rest b1 k1 n1
end.
Fixpoint disj_sides_xB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
match kn with
| [] => []
| KDisj c1 m1 c2 m2 :: rest =>
let r := disj_sides_xB bc rest b1 k1 n1 in
let r1 := if sub_itv_xB bc b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
if sub_itv_xB bc b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
| _ :: rest => disj_sides_xB bc rest b1 k1 n1
end.
Fixpoint in_sidesB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
match D with
| [] => false
| (c, m) :: r => if sub_itvB bc b2 k2 n2 c m then true else in_sidesB bc r b2 k2 n2
end.
Fixpoint in_sides_xB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
match D with
| [] => false
| (c, m) :: r => if sub_itv_xB bc b2 k2 n2 c m then true else in_sides_xB bc r b2 k2 n2
end.
Definition mk_sprepB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) : sprep :=
SPrep (base_rangeB bc b1) (xhiB bc n1)
(match n1 with ELit z1 => disj_sidesB bc (bc_fk bc) b1 k1 (zlit64 z1) | _ => [] end)
(disj_sides_xB bc (bc_fk bc) b1 k1 n1).
Definition ranges_apart_pB (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
(b2 : expr) (k2 : Z) (n2 : expr) : bool :=
match n1, n2 with
| ELit z1, ELit z2 =>
let m1 := zlit64 z1 in let m2 := zlit64 z2 in
if (match sp_rng sp, base_rangeB bc b2 with
| Some (lo1, hi1), Some (lo2, hi2) =>
(Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
| _, _ => false
end) then true
else if in_sidesB bc (sp_D sp) b2 k2 m2 then true
else lin_apartB bc b1 k1 m1 b2 k2 m2
| _, _ =>
if (match sp_rng sp, base_rangeB bc b2, sp_h1 sp, xhiB bc n2 with
| Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
else
if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
| _, _, _, _ => false
end) then true
else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
else if negb (shares_var b1 b2) then false
else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
end.
Lemma lin_test_relB_eqf : forall fk, lin_test_relB (mkbc fk) = lin_test_rel fk.
Proof. intros. bcfe. unfold lin_test_relB, lin_test_rel. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_test_relB_eqf : bceq.
Lemma lin_testB_eqf : forall fk, lin_testB (mkbc fk) = lin_test fk.
Proof. intros. bcfe. unfold lin_testB, lin_test. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_testB_eqf : bceq.
Lemma lin_srangeB_eqf : forall fk, lin_srangeB (mkbc fk) = lin_srange fk.
Proof. intros. bcfe. unfold lin_srangeB, lin_srange. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_srangeB_eqf : bceq.
Lemma lin_nowrapRB_eqf : forall fk, lin_nowrapRB (mkbc fk) = lin_nowrapR fk.
Proof. intros. bcfe. unfold lin_nowrapRB, lin_nowrapR. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_nowrapRB_eqf : bceq.
Lemma lin_apart0B_eqf : forall fk, lin_apart0B (mkbc fk) = lin_apart0 fk.
Proof. intros. bcfe. unfold lin_apart0B, lin_apart0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_apart0B_eqf : bceq.
Lemma lin_apartB_eqf : forall fk, lin_apartB (mkbc fk) = lin_apart fk.
Proof. intros. bcfe. unfold lin_apartB, lin_apart. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_apartB_eqf : bceq.
Lemma lin_brangeB_eqf : forall fk, lin_brangeB (mkbc fk) = lin_brange fk.
Proof. intros. bcfe. unfold lin_brangeB, lin_brange. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_brangeB_eqf : bceq.
Lemma xloB_eqf : forall fk, xloB (mkbc fk) = xlo fk.
Proof. intros. bcfe. unfold xloB, xlo. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xloB_eqf : bceq.
Lemma xhiB_eqf : forall fk, xhiB (mkbc fk) = xhi fk.
Proof. intros. bcfe. unfold xhiB, xhi. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xhiB_eqf : bceq.
Lemma xt_nowrapB_eqf : forall fk, xt_nowrapB (mkbc fk) = xt_nowrap fk.
Proof.
intros fk. apply functional_extensionality; intros ts.
induction ts as [|[e k] rest IH]; intros; bcfe; [reflexivity|].
cbn [xt_nowrapB xt_nowrap]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite xt_nowrapB_eqf : bceq.
Lemma lin_ge0_scaledB_eqf : forall fk, lin_ge0_scaledB (mkbc fk) = lin_ge0_scaled fk.
Proof. intros. bcfe. unfold lin_ge0_scaledB, lin_ge0_scaled. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_ge0_scaledB_eqf : bceq.
Lemma lin_ge0B_eqf : forall fk, lin_ge0B (mkbc fk) = lin_ge0 fk.
Proof. intros. bcfe. unfold lin_ge0B, lin_ge0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_ge0B_eqf : bceq.
Lemma xinside0B_eqf : forall fk, xinside0B (mkbc fk) = xinside0 fk.
Proof. intros. bcfe. unfold xinside0B, xinside0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xinside0B_eqf : bceq.
Lemma xinside_numB_eqf : forall fk, xinside_numB (mkbc fk) = xinside_num fk.
Proof. intros. bcfe. unfold xinside_numB, xinside_num. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xinside_numB_eqf : bceq.
Lemma xinsideB_eqf : forall fk, xinsideB (mkbc fk) = xinside fk.
Proof. intros. bcfe. unfold xinsideB, xinside. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite xinsideB_eqf : bceq.
Lemma sub_itvB_eqf : forall fk, sub_itvB (mkbc fk) = sub_itv fk.
Proof. intros. bcfe. unfold sub_itvB, sub_itv. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sub_itvB_eqf : bceq.
Lemma kdisj_apartB_eqf : forall fk, kdisj_apartB (mkbc fk) = kdisj_apart fk.
Proof.
intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2.
revert b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [kdisj_apartB kdisj_apart]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite kdisj_apartB_eqf : bceq.
Lemma ranges_apartB_eqf : forall fk, ranges_apartB (mkbc fk) = ranges_apart fk.
Proof. intros. bcfe. unfold ranges_apartB, ranges_apart. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ranges_apartB_eqf : bceq.
Lemma sub_itv_xB_eqf : forall fk, sub_itv_xB (mkbc fk) = sub_itv_x fk.
Proof. intros. bcfe. unfold sub_itv_xB, sub_itv_x. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sub_itv_xB_eqf : bceq.
Lemma kdisj_apart_xB_eqf : forall fk, kdisj_apart_xB (mkbc fk) = kdisj_apart_x fk.
Proof.
intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2.
revert b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [kdisj_apart_xB kdisj_apart_x]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite kdisj_apart_xB_eqf : bceq.
Lemma end_hiB_eqf : forall fk, end_hiB (mkbc fk) = end_hi fk.
Proof. intros. bcfe. unfold end_hiB, end_hi. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite end_hiB_eqf : bceq.
Lemma ranges_apart_xB_eqf : forall fk, ranges_apart_xB (mkbc fk) = ranges_apart_x fk.
Proof. intros. bcfe. unfold ranges_apart_xB, ranges_apart_x. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ranges_apart_xB_eqf : bceq.
Lemma disj_sidesB_eqf : forall fk, disj_sidesB (mkbc fk) = disj_sides fk.
Proof.
intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1.
revert b1 k1 n1. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [disj_sidesB disj_sides]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite disj_sidesB_eqf : bceq.
Lemma disj_sides_xB_eqf : forall fk, disj_sides_xB (mkbc fk) = disj_sides_x fk.
Proof.
intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1.
revert b1 k1 n1. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [disj_sides_xB disj_sides_x]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite disj_sides_xB_eqf : bceq.
Lemma in_sidesB_eqf : forall fk, in_sidesB (mkbc fk) = in_sides fk.
Proof.
intros fk. apply functional_extensionality; intros D. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2.
revert b2 k2 n2. induction D as [|[c m] rest IH]; intros; bcfe; [reflexivity|].
cbn [in_sidesB in_sides]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite in_sidesB_eqf : bceq.
Lemma in_sides_xB_eqf : forall fk, in_sides_xB (mkbc fk) = in_sides_x fk.
Proof.
intros fk. apply functional_extensionality; intros D. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2.
revert b2 k2 n2. induction D as [|[c m] rest IH]; intros; bcfe; [reflexivity|].
cbn [in_sides_xB in_sides_x]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite in_sides_xB_eqf : bceq.
Lemma mk_sprepB_eqf : forall fk, mk_sprepB (mkbc fk) = mk_sprep fk.
Proof. intros. bcfe. unfold mk_sprepB, mk_sprep. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mk_sprepB_eqf : bceq.
Lemma ranges_apart_pB_eqf : forall fk, ranges_apart_pB (mkbc fk) = ranges_apart_p fk.
Proof. intros. bcfe. unfold ranges_apart_pB, ranges_apart_p. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ranges_apart_pB_eqf : bceq.
Fixpoint coeffs_divkB (bc : bctx) (m : Z) (ts : list (Z * expr)) : bool :=
match ts with
| [] => true
| (k, a) :: rest => ((Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealignB bc a) mod m) 0) && coeffs_divkB bc m rest)%bool
end.
Definition lin_lowbits_knB (bc : bctx) (e : expr) (k : Z) : option Z :=
let l := lin_of e in
if coeffs_divkB bc (2 ^ k) (snd l) then Some ((fst l) mod 2 ^ k)%Z
else pageup_low e (2 ^ k).
Definition lin_nowrap_lB (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
match lin_range (erangeB bc) c ts with
| Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
| None => false
end.
Definition mkSrlB (bc : bctx) (a : expr) (s : Z) : expr :=
let l := lin_of a in
let m := (2 ^ s)%Z in
if (negb (lin_trivial l) && coeffs_div m (snd l) && lin_nowrapB bc a)%bool
then unlin ((fst l / m)%Z, ldiv_terms m (snd l))
else
match (if (negb (lin_trivial l) && lin_nowrapB bc a)%bool then lsplit_divc m (snd l) else ([], [])) with
| ((_ :: _) as dts, (_ :: _) as rts) =>
match (if lin_nowrap_lB bc (fst l) rts then erangeB bc (unlin (fst l, rts)) else None) with
| Some (lo, hi) =>
if Z.eqb (lo / m) (hi / m) then unlin ((lo / m)%Z, ldiv_terms m dts)
else mkAlu ALU_SRL a (ELit s)
| None => mkAlu ALU_SRL a (ELit s)
end
| _ => mkAlu ALU_SRL a (ELit s)
end.
Fixpoint lowbitsB (bc : bctx) (e : expr) (j : Z) {struct e} : option Z :=
let m := (2 ^ j)%Z in
let dflt := if Z.leb j (ealignB bc e) then Some 0%Z else lin_lowbits_knB bc e j in
match e with
| ELit z => Some ((z mod two64) mod m)%Z
| EAlu ALU_AND a (ELit c) =>
if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
match lowbitsB bc a j with Some v => Some (Z.land v ((c mod two64) mod m)) | None => dflt end
| EAlu ALU_OR a (ELit c) =>
match lowbitsB bc a j with Some v => Some (Z.lor v ((c mod two64) mod m)) | None => dflt end
| EAlu ALU_XOR a (ELit c) =>
match lowbitsB bc a j with Some v => Some (Z.lxor v ((c mod two64) mod m)) | None => dflt end
| EAlu ALU_ADD a b =>
match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some ((x + y) mod m)%Z | _, _ => dflt end
| EAlu ALU_SUB a b =>
match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some ((x - y) mod m)%Z | _, _ => dflt end
| EMd M_MUL (ELit c) a =>
if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
match lowbitsB bc a j with Some v => Some ((c * v) mod m)%Z | None => dflt end
| _ => dflt
end.
Fixpoint lsplit_divB (bc : bctx) (m : Z) (ts : list (Z * expr)) : list (Z * expr) * list (Z * expr) :=
match ts with
| [] => ([], [])
| (k, a) :: rest =>
let (d, r) := lsplit_divB bc m rest in
if (Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealignB bc a) mod m) 0)%bool then ((k, a) :: d, r) else (d, (k, a) :: r)
end.
Definition and_high_splitB (bc : bctx) (bk : expr) (j c : Z) (dts rts : list (Z * expr)) : expr :=
let m := (2 ^ j)%Z in
let cA := (c - c mod m)%Z in
let r := unlin ((c mod m)%Z, rts) in
match erangeB bc r with
| Some (lo, hi) =>
if Z.eqb (lo / m) (hi / m) then unlin ((cA + (lo / m) * m)%Z, dts)
else mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
| None => mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
end.
Definition and_low_splitB (bc : bctx) (bk : expr) (j c : Z) (rts : list (Z * expr)) : expr :=
let m := (2 ^ j)%Z in
let r := unlin ((c mod m)%Z, rts) in
match erangeB bc r with
| Some (lo, hi) =>
if Z.eqb (lo / m) (hi / m) then unlin ((c mod m - (lo / m) * m)%Z, rts)
else mkAlu ALU_AND r bk
| None => mkAlu ALU_AND r bk
end.
Definition narrow_maskB (bc : bctx) (a : expr) (k' : Z) : option Z :=
let i := ctz64 k' in
let m := (k' + 2 ^ i)%Z in
let j := Z.log2 m in
if (Z.ltb 0 k' && Z.eqb m (2 ^ j) && Z.ltb j 64)%bool then
match xhiB bc a with
| Some h => if Z.ltb h (2 ^ j) then Some (two64 - 2 ^ i)%Z else None
| None => None
end
else None.
Definition mkAnd0B (bc : bctx) (a b : expr) : expr :=
match b with
| ELit k =>
let k' := (k mod two64)%Z in
let j := Z.log2 (two64 - k') in
if (Z.eqb (two64 - k') (2 ^ j) && Z.ltb j 64)%bool then
(if Z.leb j (ealignB bc a) then a
else let l := lin_of a in
if (negb (lin_trivial l) && coeffs_divkB bc (2 ^ j) (snd l))%bool
then unlin ((fst l - (fst l) mod 2 ^ j)%Z, snd l)
else
match (if lin_trivial l then ([], snd l) else lsplit_divB bc (2 ^ j) (snd l)) with
| ((_ :: _) as dts, (_ :: _) as rts) => and_high_splitB bc b j (fst l) dts rts
| _ =>
mkMd M_MUL (ELit (2 ^ j)%Z) (mkSrlB bc a j)
end)
else
let j2 := Z.log2 (k' + 1) in
if (Z.eqb (k' + 1) (2 ^ j2) && Z.ltb j2 64)%bool then
(if Z.leb j2 (ealignB bc a) then ELit 0
else match lowbitsB bc a j2 with
| Some v => ELit v
| None =>
if lin_trivial (lin_of a) then mkAlu ALU_AND a b
else match lin_lowbits_knB bc a j2 with
| Some v => ELit v
| None =>
match lsplit_divB bc (2 ^ j2) (snd (lin_of a)) with
| (_ :: _, (_ :: _) as rts) => and_low_splitB bc b j2 (fst (lin_of a)) rts
| _ => mkAlu ALU_AND a b
end
end
end)
else
let j3 := (Z.log2 k' + 1)%Z in
if (Z.ltb 0 k' && Z.leb j3 64 && negb (lin_trivial (lin_of a)))%bool then
match lin_lowbits_knB bc a j3 with
| Some v => ELit (Z.land v k')
| None => mkAlu ALU_AND a b
end
else mkAlu ALU_AND a b
| _ => mkAlu ALU_AND a b
end.
Definition mkAndB (bc : bctx) (a b : expr) : expr :=
match b with
| ELit k =>
match narrow_maskB bc a (k mod two64)%Z with
| Some m => mkAnd0B bc a (ELit m)
| None => mkAnd0B bc a b
end
| _ => mkAnd0B bc a b
end.
Definition mkAndKB (bc : bctx) (a b : expr) : expr :=
match a, b with
| EAlu ALU_AND x (ELit m1), ELit k => mkAndB bc x (ELit (Z.land (m1 mod two64) (k mod two64))%Z)
| EMd M_MUL (ELit m) (EAlu ALU_SRL x (ELit i)), ELit k =>
let i' := ((i mod two64) mod 64)%Z in
if Z.eqb (m mod two64) (2 ^ i') then mkAndB bc x (ELit (Z.land (two64 - 2 ^ i') (k mod two64))%Z)
else mkAndB bc a b
| _, _ => mkAndB bc a b
end.
Definition or_disjointB (bc : bctx) (a b : expr) : bool :=
match erangeB bc b with
| Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi (2 ^ (ealignB bc a)))%bool
| None => false
end.
Definition mkOrB (bc : bctx) (a b : expr) : expr :=
match is_lit a, is_lit b with
| Some x, Some y => ELit (zalu ALU_OR x y)
| _, _ =>
if or_disjointB bc a b then mkAlu ALU_ADD a b
else if or_disjointB bc b a then mkAlu ALU_ADD a b
else
match b with
| ELit c => mkAlu ALU_ADD (mkAndKB bc a (ELit (Z.lnot (c mod two64)))) (ELit c)
| _ => match a with
| ELit c => mkAlu ALU_ADD (mkAndKB bc b (ELit (Z.lnot (c mod two64)))) (ELit c)
| _ => EAlu ALU_OR a b
end
end
end.
Fixpoint conc_tryB (bc : bctx) (e : expr) (cands : list expr) : option Z :=
match cands with
| [] => None
| s :: rest =>
if closedb s then conc_tryB bc e rest else
if negb (evalS_def s e) then conc_tryB bc e rest else
match erangeB bc s with
| Some (lo, hi) =>
if Z.leb (hi - lo) conc_limit then
match evalS s (wrap64 lo) e with
| Some v =>
if (if Z.ltb hi lo then true
else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
if all_eval_toS s e v lo (Z.to_nat (hi - lo + 1)) then Some v
else conc_tryB bc e rest
else conc_tryB bc e rest
| None => conc_tryB bc e rest
end
else conc_tryB bc e rest
| None => conc_tryB bc e rest
end
end.
Definition concretizeB (bc : bctx) (e : expr) : option Z :=
if closedb e then eval_closed e else conc_tryB bc e (nubE (subexprs e)).
Definition foldKB (bc : bctx) (e : expr) : expr :=
match e with
| ELit _ => e
| _ => match erangeB bc e with
| Some (lo, hi) => if Z.eqb lo hi then ELit lo
else match concretizeB bc e with Some v => ELit v | None => e end
| None => match concretizeB bc e with Some v => ELit v | None => e end
end
end.
Definition lin_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
let ltu := if lin_ge0B bc [(b, (-1)%Z)] [(a, 0%Z)] then Some true
else if lin_ge0B bc [(a, 0%Z)] [(b, 0%Z)] then Some false else None in
match c with
| BC_LTU => ltu
| BC_GEU => option_map negb ltu
| BC_LT | BC_GE =>
match erangeB bc a, erangeB bc b with
| Some (_, ah), Some (_, bh) =>
if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool
then match c with BC_LT => ltu | _ => option_map negb ltu end
else None
| _, _ => None
end
| BC_EQ | BC_NE =>
if (lin_ge0B bc [(b, (-1)%Z)] [(a, 0%Z)] || lin_ge0B bc [(a, (-1)%Z)] [(b, 0%Z)])%bool
then Some (match c with BC_EQ => false | _ => true end)
else
if (if lin_ge0B bc [(a, 0%Z)] [(b, 0%Z)] then lin_ge0B bc [(b, 0%Z)] [(a, 0%Z)] else false)
then Some (match c with BC_EQ => true | _ => false end)
else None
end.
Definition decide_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
match a, b with
| ELit x, ELit y => Some (lit_branch c x y)
| _, _ =>
if expr_eqb a b then Some (cond_on_eq c)
else match diff_branch c a b with
| Some t => Some t
| None =>
match (match erangeB bc a, erangeB bc b with
| Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
| _, _ => None
end) with
| Some t => Some t
| None => lin_branchB bc c a b
end
end
end.
Definition mkSltB (bc : bctx) (c : branch_cond) (op : aluop) (a b : expr) : expr :=
match a, b with
| ELit _, ELit _ => mkAlu op a b
| _, _ => match decide_branchB bc c a b with
| Some true => ELit 1
| Some false => ELit 0
| None => mkAlu op a b
end
end.
Definition mkAluK0B (bc : bctx) (op : aluop) (a b : expr) : expr :=
match op with
| ALU_SLTU => mkSltB bc BC_LTU ALU_SLTU a b
| ALU_SLT => mkSltB bc BC_LT ALU_SLT a b
| ALU_AND => match a, b with
| ELit _, ELit _ => mkAndB bc a b
| ELit _, _ => mkAndKB bc b a
| _, _ => mkAndKB bc a b
end
| ALU_OR => if expr_eqb a b then a else mkOrB bc a b
| ALU_XOR => if expr_eqb a b then ELit 0 else match is_lit a, b with
| None, ELit k => if Z.eqb (k mod two64) (two64 - 1) then mkAlu ALU_SUB (ELit (two64 - 1)) a
else mkAlu op a b
| _, _ => mkAlu op a b
end
| ALU_SRL => match is_lit a, shamt_of b 6 with
| None, Some s => mkSrlB bc a s
| _, _ => mkAlu op a b
end
| _ => mkAlu op a b
end.
Definition mkAluKB (bc : bctx) (op : aluop) (a b : expr) : expr :=
foldKB bc (mkAluK0B bc op a b).
Definition mkMdKB (bc : bctx) (op : mulop) (a b : expr) : expr :=
match is_lit a, op, b with
| None, M_REMU, ELit m =>
match pow2_log m with
| Some k => mkAluKB bc ALU_AND a (ELit (2 ^ k - 1))
| None => mkMd op a b
end
| None, M_DIVU, ELit m =>
match pow2_log m with
| Some k => mkAluKB bc ALU_SRL a (ELit k)
| None => mkMd op a b
end
| _, _, _ => mkMd op a b
end.
Definition zband32B (bc : bctx) (d : expr) : bool :=
let l := lin_of d in
match lin_range (erangeB bc) (fst l) (snd l) with
| Some (lo, hi) => (Z.ltb (- 2 ^ 31) lo && Z.ltb hi (2 ^ 31))%bool
| None => false
end.
Definition mkAluwK0B (bc : bctx) (op : aluop) (a b : expr) : expr :=
match op with
| ALU_ADD | ALU_SUB =>
let d := mkAlu op a b in
match is_lit d with
| Some v => ELit (zsx32 v)
| None => match erangeB bc d with
| Some (lo, hi) => if sx32_stable lo hi then d else if zband32B bc d then d else mkAluw op a b
| None => if zband32B bc d then d else mkAluw op a b
end
end
| _ => mkAluw op a b
end.
Definition mkAluwKB (bc : bctx) (op : aluop) (a b : expr) : expr :=
foldKB bc (mkAluwK0B bc op a b).
Definition extK0B (bc : bctx) (v : expr) : expr :=
match v with
| EExt sx O n e =>
if Nat.leb n 7 then
match erangeB bc e with
| Some (lo, hi) => if Z.ltb hi (if sx then 2 ^ (8 * Z.of_nat n) / 2 else 2 ^ (8 * Z.of_nat n)) then e else v
| None => v
end
else v
| _ => v
end.
Definition extKB (bc : bctx) (v : expr) : expr := foldKB bc (extK0B bc v).
Definition flat_scB (bc : bctx) (a : saddr) (n : nat) : list sidecond :=
match base_rangeB bc (a_base a) with
| Some (lo, hi) =>
if (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) (2 ^ 64))%bool
then [] else [SCFlat a (elen n)]
| None => [SCFlat a (elen n)]
end.
Fixpoint wr_coveredB (bc : bctx) (kn : list kentry) (a : saddr) (n : nat) : bool :=
match kn with
| [] => false
| KWr (SA kb kk) len :: rest =>
if (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
then match xloB bc len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end
else false)
then true
else if xinsideB bc (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len then true
else wr_coveredB bc rest a n
| _ :: rest => wr_coveredB bc rest a n
end.
Definition storeok_scB (bc : bctx) (a : saddr) (n : nat) : list sidecond :=
if wr_coveredB bc (bc_fk bc) a n then [] else [SCStoreOk a n].
Definition conc_exprB (bc : bctx) (e : expr) : expr :=
match e with
| ELit _ => e
| _ => match concretizeB bc e with Some v => ELit v | None => e end
end.
Definition enum_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
let '(e, pos) := cond_probe c a b in
match concretizeB bc e with
| Some v => let z := Z.eqb (v mod two64) 0 in Some (if pos then negb z else z)
| None => None
end.
Definition to_saddrKB (bc : bctx) (e : expr) (imm : Z) : saddr :=
match split_lit e with
| (ELit _, _) => to_saddr e imm
| _ => match concretizeB bc (mkAlu ALU_ADD e (ELit imm)) with
| Some v => SA (ELit 0) v
| None => to_saddr e imm
end
end.
Definition amo_alignedbB (bc : bctx) (e : expr) (wd : awidth) : bool :=
match lin_lowbits_knB bc e (match wd with AW => 2 | AD => 3 end) with
| Some r => Z.eqb r 0
| None => false
end.
Definition amo_newvalB (bc : bctx) (wd : awidth) (aop : option aluop) (old src : expr) : expr :=
match aop with
| None => src
| Some o => match wd with AW => mkAluwKB bc o old src | AD => mkAluKB bc o old src end
end.
Fixpoint log_lookupB (bc : bctx) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
(hints : list bool) (acc : list sidecond) : lres :=
match log with
| [] => LMiss acc hints
| SE (SA kb kk) w v :: rest =>
match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
| RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
| RDisjoint => log_lookupB bc rest rb rk n sx hints acc
| RPartial => match log_bytes_lit log rb rk n with
| Some bs => LHit (lit_of_bytes sx n bs) acc hints
| None => LStuck
end
| RUnknown =>
if ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w)
then log_lookupB bc rest rb rk n sx hints acc
else
match hints with
| false :: _ => LStuck
| _ => log_lookupB bc rest rb rk n sx (tl hints)
(SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
end
end
end.
Fixpoint know_lookupA0B (bc : bctx) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
(n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
let know_lookup := know_lookupA0B bc in
match kn with
| [] => LMiss acc hints
| K :: rest =>
match K with
| KWord (SA kb kk) w v =>
match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
| RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
| _ => know_lookup segs rest rb rk n sx hints acc
end
| KZero (SA kb kk) len =>
match len with
| ELit l0 =>
match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2^64)%Z with
| RInside _ => LHit (ELit 0) acc hints
| RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
| RUnknown =>
if xinsideB bc rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
match hints with
| true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
| false :: hs => know_lookup segs rest rb rk n sx hs acc
| [] => know_lookup segs rest rb rk n sx [] acc
end
end
| _ =>
if xinsideB bc rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
match hints with
| true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
| false :: hs => know_lookup segs rest rb rk n sx hs acc
| [] => know_lookup segs rest rb rk n sx [] acc
end
end
| KFill (SA kb kk) len c =>
let hit := fill_lit sx n c in
match len with
| ELit l0 =>
match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2^64)%Z with
| RInside _ => LHit hit acc hints
| RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
| RUnknown =>
if xinsideB bc rb rk (elen n) kb kk len then LHit hit acc hints else
match hints with
| true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
| false :: hs => know_lookup segs rest rb rk n sx hs acc
| [] => know_lookup segs rest rb rk n sx [] acc
end
end
| _ =>
if xinsideB bc rb rk (elen n) kb kk len then LHit hit acc hints else
match hints with
| true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
| false :: hs => know_lookup segs rest rb rk n sx hs acc
| [] => know_lookup segs rest rb rk n sx [] acc
end
end
| KUnk _ _ => know_lookup segs rest rb rk n sx hints acc
| KBlob (SA kb kk) len k =>
if expr_eqb rb kb then
if Z.leb kk rk then
match len with
| ELit l0 =>
if Z.leb (rk + Z.of_nat n) (kk + (l0 mod 2^64)%Z)
then LHit (EBlob sx k (rk - kk) n) acc hints
else if Z.leb (kk + (l0 mod 2^64)%Z) rk then know_lookup segs rest rb rk n sx hints acc
else LStuck
| _ =>
if match erangeB bc len with
| Some (lo, _) => Z.leb (rk + Z.of_nat n) (kk + lo)
| None => false
end
then LHit (EBlob sx k (rk - kk) n) acc hints
else
match hints with
| true :: hs => LHit (EBlob sx k (rk - kk) n)
(SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
| false :: hs => know_lookup segs rest rb rk n sx hs acc
| [] => know_lookup segs rest rb rk n sx [] acc
end
end
else know_lookup segs rest rb rk n sx hints acc
else know_lookup segs rest rb rk n sx hints acc
| KImg lo hi =>
match rb with
| ELit 0 =>
if (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%bool then
match img_bytes segs rk n with
| Some bs => LHit (lit_of_bytes sx n bs) acc hints
| None => LStuck
end
else know_lookup segs rest rb rk n sx hints acc
| _ => know_lookup segs rest rb rk n sx hints acc
end
| KAlign _ _ => know_lookup segs rest rb rk n sx hints acc
| KRange _ _ _ => know_lookup segs rest rb rk n sx hints acc
| KWr _ _ => know_lookup segs rest rb rk n sx hints acc
| KDisj _ _ _ _ => know_lookup segs rest rb rk n sx hints acc
end
end.
Definition know_lookupAB (bc : bctx) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
(n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
match know_lookupA0B bc segs kn rb rk n sx hints acc with
| LMiss acc' hints' =>
match know_bytes_lit segs kn rb rk n with
| Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
| None => LMiss acc' hints'
end
| r => r
end.
Definition sym_readB (segs : list Segment) (ss : sym_state) (bc : bctx) (scr : scripts)
(a : saddr) (n : nat) (sx' : bool)
: option (expr * list sidecond * scripts * nat) :=
match log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
| LStuck => None
| LHit v scs hints =>
Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
| LMiss scs hints =>
match know_lookupAB bc segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
| LStuck => None
| LHit v scs' hints' =>
Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
| LMiss scs' hints' =>
let i := s_next ss in
let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
end
end.
Definition sym_stepB (bc : bctx) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
let g r := sr_get (s_regs ss) r in
let p := s_pc ss in
match i with
| OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
| ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
| Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
| OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
| ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
| Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
| Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
| Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
| Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
| Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
| Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
| Jalr rd rs1 imm =>
match conc_exprB bc (g rs1) with
| ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
| _ => SStop
end
| Branch c rs1 rs2 imm =>
let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
let a := g rs1 in let b := g rs2 in
match match decide_branchB bc c a b with
| Some t => Some t
| None => match decide_branchB bc c (conc_exprB bc a) (conc_exprB bc b) with
| Some t => Some t
| None => enum_branchB bc c a b
end
end with
| Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
| None =>
match sc_dirs scr with
| [] => SStop
| t :: dirs' =>
SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
(SCR dirs' (sc_reads scr) (sc_hints scr))
end
end
| Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
| FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
| Load sz sx rd rs imm =>
let n := msize_bytes sz in
let sx' := match sz with SZ8 => false | _ => sx end in
let a := to_saddrKB bc (g rs) (bv_signed imm) in
match sym_readB segs ss bc scr a n sx' with
| None => SStop
| Some (v, scs, scr', nx') =>
SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
(s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
end
| Store sz rs1 rs2 imm =>
let n := msize_bytes sz in
let a := to_saddrKB bc (g rs1) (bv_signed imm) in
match resv_inval (s_resv ss) a with
| None => SStop
| Some r' =>
SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
(flat_scB bc a n ++ storeok_scB bc a n) scr
end
| Lr wd _ _ rd rs =>
let n := msize_bytes (amo_sz wd) in
let e := g rs in
if amo_alignedbB bc e wd then
let a := to_saddrKB bc e 0 in
match sym_readB segs ss bc scr a n (amo_sx wd) with
| None => SStop
| Some (v, scs, scr', nx') =>
SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
(s_log ss) (s_know ss) nx' (Some a)) scs scr'
end
else SStop
| Sc wd _ _ rd rs1 rs2 =>
let n := msize_bytes (amo_sz wd) in
let e := g rs1 in
if amo_alignedbB bc e wd then
let a := to_saddrKB bc e 0 in
match s_resv ss with
| Some r =>
if saddr_eqb r a then
SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
(SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
(flat_scB bc a n ++ storeok_scB bc a n) scr
else SStop
| None => SStop
end
else SStop
| Amo op wd _ _ rd rs1 rs2 =>
match amo_aluop op with
| None => SStop
| Some aop =>
let n := msize_bytes (amo_sz wd) in
let e := g rs1 in
if amo_alignedbB bc e wd then
let a := to_saddrKB bc e 0 in
match resv_inval (s_resv ss) a with
| None => SStop
| Some r' =>
match sym_readB segs ss bc scr a n (amo_sx wd) with
| None => SStop
| Some (vold, scs, scr', nx') =>
SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
(SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
(scs ++ storeok_scB bc a n) scr'
end
end
else SStop
end
| _ => SStop
end.
Definition know_lookupB (segs : list Segment) (bc : bctx) (rb : expr) (rk : Z)
(n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
know_lookupAB bc segs (bc_fk bc) rb rk n sx hints acc.
Local Open Scope Z_scope.
Definition gran (a : Z) : Z := Z.shiftr a 12.
Definition is_lit0 (e : expr) : bool := match e with ELit 0 => true | _ => false end.
Definition lit0_extent (K : kentry) : option (Z * Z) :=
match K with
| KWord (SA (ELit 0) kk) w _ => Some (kk, kk + Z.of_nat w)
| KZero (SA (ELit 0) kk) (ELit l0) => Some (kk, kk + zmod64 l0)
| KFill (SA (ELit 0) kk) (ELit l0) _ => Some (kk, kk + zmod64 l0)
| KBlob (SA (ELit 0) kk) (ELit l0) _ => Some (kk, kk + zmod64 l0)
| KImg lo hi => Some (lo, hi)
| _ => None
end.
Definition ext_fits (s e : Z) : bool := if Z.ltb s e then Z.leb (gran (e - 1) - gran s) 1 else false.
Definition ext_has (s e g : Z) : bool := if Z.eqb g (gran s) then true else Z.eqb g (gran (e - 1)).
Definition kx_wide0 (K : kentry) : bool :=
match lit0_extent K with
| Some (s, e) => negb (ext_fits s e)
| None =>
match K with
| KZero (SA kb _) _ | KFill (SA kb _) _ _ => true
| KBlob (SA kb _) _ _ => is_lit0 kb
| _ => false
end
end.
Definition kx_cand0 (g : Z) (K : kentry) : bool :=
match lit0_extent K with
| Some (s, e) => if ext_fits s e then ext_has s e g else true
| None => kx_wide0 K
end.
Definition kx_candf (K : kentry) : bool :=
match K with
| KWord (SA kb _) _ _ | KBlob (SA kb _) _ _ => negb (is_lit0 kb)
| KZero _ _ | KFill _ _ _ => true
| _ => false
end.
Definition kx_gkey (g : Z) : positive := match g with Z0 => xH | Zpos p => xO p | Zneg p => xI p end.
Record kix : Type := KX {
kx_kn : list kentry;
kx_w0 : list (positive * kentry);
kx_gran : ptree (list (positive * kentry));
kx_wf : list kentry
}.
Definition kx_bucket (t : ptree (list (positive * kentry))) (g : Z) : list (positive * kentry) :=
match pt_get t (kx_gkey g) with Some b => b | None => [] end.
Definition kx_add (g : Z) (x : positive * kentry) (t : ptree (list (positive * kentry))) : ptree (list (positive * kentry)) :=
pt_set (kx_gkey g) (x :: kx_bucket t g) t.
Fixpoint kx_build (kn : list kentry) (i : positive) : list (positive * kentry) * ptree (list (positive * kentry)) * list kentry :=
match kn with
| [] => ([], PTLeaf, [])
| K :: rest =>
let '(w0, gr, wf) := kx_build rest (Pos.succ i) in
let wf' := if kx_candf K then K :: wf else wf in
match lit0_extent K with
| Some (s, e) =>
if ext_fits s e then
let g1 := gran s in let g2 := gran (e - 1) in
let gr1 := kx_add g1 (i, K) gr in
(w0, (if Z.eqb g1 g2 then gr1 else kx_add g2 (i, K) gr1), wf')
else ((i, K) :: w0, gr, wf')
| None => if kx_wide0 K then ((i, K) :: w0, gr, wf') else (w0, gr, wf')
end
end.
Definition mk_kix (kn : list kentry) : kix :=
let r := kx_build kn xH in KX kn (fst (fst r)) (snd (fst r)) (snd r).
Fixpoint kx_merge (l1 : list (positive * kentry)) : list (positive * kentry) -> list kentry :=
match l1 with
| [] => fun l2 => List.map snd l2
| (p1, K1) :: r1 =>
fix go (l2 : list (positive * kentry)) : list kentry :=
match l2 with
| [] => K1 :: List.map snd r1
| (p2, K2) :: r2 => if Pos.ltb p1 p2 then K1 :: kx_merge r1 l2 else K2 :: go r2
end
end.
Definition kx_select (kx : kix) (rb : expr) (rk : Z) : list kentry :=
if is_lit0 rb then kx_merge (kx_bucket (kx_gran kx) (gran rk)) (kx_w0 kx)
else kx_wf kx.
Definition know_lookupA0I (bc : bctx) (kx : kix) (segs : list Segment) (rb : expr) (rk : Z)
(n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
match hints, n with
| [], S _ => know_lookupA0B bc segs (kx_select kx rb rk) rb rk n sx [] acc
| _, _ => know_lookupA0B bc segs (kx_kn kx) rb rk n sx hints acc
end.
Lemma gran_div : forall a, gran a = a / 4096.
Proof. intros a. unfold gran. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma gran_mono : forall a b, a <= b -> gran a <= gran b.
Proof. intros a b H. rewrite !gran_div. apply Z.div_le_mono; lia. Qed.
Lemma gran_between : forall s e x,
s <= x -> x < e -> ext_fits s e = true -> ext_has s e (gran x) = true.
Proof.
intros s e x Hs He Hf. unfold ext_fits, ext_has in *.
destruct (Z.ltb s e); [|discriminate]. apply Z.leb_le in Hf.
pose proof (gran_mono s x Hs) as A. pose proof (gran_mono x (e - 1) ltac:(lia)) as B.
destruct (Z.eqb_spec (gran x) (gran s)); [reflexivity|].
destruct (Z.eqb_spec (gran x) (gran (e - 1))); [reflexivity|]. exfalso. lia.
Qed.
Lemma kx_aluop_eqb_refl : forall a, aluop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma kx_mulop_eqb_refl : forall a, mulop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma kx_expr_eqb_refl : forall x, expr_eqb x x = true.
Proof.
induction x; cbn -[Z.eqb Nat.eqb]; rewrite ?kx_aluop_eqb_refl, ?kx_mulop_eqb_refl, ?IHx, ?IHx1, ?IHx2, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
Lemma rel_lit_same : forall rb rk rn kk kl,
rel_lit rb rk rn rb kk kl =
if (Z.leb kk rk && Z.leb (rk + rn) (kk + kl))%bool then RInside (rk - kk)
else if (Z.leb (rk + rn) kk || Z.leb (kk + kl) rk)%bool then RDisjoint else RPartial.
Proof. intros. unfold rel_lit. rewrite kx_expr_eqb_refl. reflexivity. Qed.
Lemma rel_lit_other : forall rb rk rn kb kk kl,
expr_eqb rb kb = false -> rel_lit rb rk rn kb kk kl = RUnknown.
Proof. intros rb rk rn kb kk kl H. unfold rel_lit. rewrite H. reflexivity. Qed.
Lemma is_lit0_eqb : forall rb kb, is_lit0 kb = true -> expr_eqb rb kb = is_lit0 rb.
Proof.
intros rb kb H. destruct kb as [z| | | | | | |]; try discriminate. cbn in H.
destruct z; try discriminate.
destruct rb as [z'| | | | | | |]; cbn; try reflexivity; destruct z'; reflexivity.
Qed.
Lemma expr_eqb_lit0_l : forall kb, expr_eqb (ELit 0) kb = is_lit0 kb.
Proof. intros kb. destruct kb as [z| | | | | | |]; cbn; try reflexivity; destruct z; reflexivity. Qed.
Lemma is_lit0_true : forall e, is_lit0 e = true -> e = ELit 0.
Proof. intros e H. destruct e as [z| | | | | | |]; try discriminate. cbn in H. destruct z; try discriminate. reflexivity. Qed.
Lemma know_lookupA0B_skip0 : forall bc segs K rest rk n sx acc,
kx_cand0 (gran rk) K = false ->
know_lookupA0B bc segs (K :: rest) (ELit 0) rk (S n) sx [] acc = know_lookupA0B bc segs rest (ELit 0) rk (S n) sx [] acc.
Proof.
intros bc segs K rest rk n sx acc HC.
cbn [know_lookupA0B].
unfold kx_cand0, kx_wide0 in HC.
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
cbn [lit0_extent] in HC; rewrite ?zmod64_eq in HC; try reflexivity.
-
destruct (is_lit0 kb) eqn:L.
+ apply is_lit0_true in L. subst kb. cbn [lit0_extent] in HC.
rewrite rel_lit_same.
destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + Z.of_nat w))%bool eqn:E.
* exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
destruct (ext_fits kk (kk + Z.of_nat w)) eqn:F; [|discriminate].
rewrite (gran_between kk (kk + Z.of_nat w) rk) in HC; [discriminate|lia|lia|exact F].
* destruct (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + Z.of_nat w) rk)%bool; reflexivity.
+ destruct kb as [z| | | | | | |]; try (rewrite rel_lit_other by reflexivity; reflexivity).
cbn in L. destruct z; try discriminate; rewrite rel_lit_other by reflexivity; reflexivity.
-
destruct (is_lit0 kb) eqn:L.
+ apply is_lit0_true in L. subst kb. destruct len as [l0| | | | | | |]; cbn [lit0_extent] in HC; rewrite ?zmod64_eq in HC; try discriminate.
rewrite rel_lit_same.
destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + l0 mod 2 ^ 64))%bool eqn:E.
* exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
destruct (ext_fits kk (kk + l0 mod 2 ^ 64)) eqn:F; [|discriminate].
rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
* destruct (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool; reflexivity.
+ destruct kb as [z| | | | | | |]; cbn [lit0_extent] in HC; try (destruct len; discriminate).
cbn in L. destruct z; try discriminate; destruct len; discriminate.
-
destruct (is_lit0 kb) eqn:L.
+ apply is_lit0_true in L. subst kb. destruct len as [l0| | | | | | |]; cbn [lit0_extent is_lit0] in HC; rewrite ?zmod64_eq in HC; try discriminate.
rewrite kx_expr_eqb_refl.
destruct (ext_fits kk (kk + l0 mod 2 ^ 64)) eqn:F; [|discriminate].
destruct (Z.leb_spec kk rk) as [H1|H1]; [|reflexivity].
destruct (Z.leb_spec (rk + Z.of_nat (S n)) (kk + (l0 mod 2 ^ 64))) as [H2|H2].
* exfalso. rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
* destruct (Z.leb_spec (kk + (l0 mod 2 ^ 64)) rk) as [H3|H3]; [reflexivity|].
exfalso. rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
+ rewrite expr_eqb_lit0_l, L. reflexivity.
-
destruct (ext_fits lo hi) eqn:F; [|discriminate].
destruct (Z.leb lo rk && Z.leb (rk + Z.of_nat (S n)) hi)%bool eqn:E; [|reflexivity].
exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
rewrite (gran_between lo hi rk) in HC; [discriminate|lia|lia|exact F].
-
destruct (is_lit0 kb) eqn:L.
+ apply is_lit0_true in L. subst kb. destruct len as [l0| | | | | | |]; cbn [lit0_extent] in HC; rewrite ?zmod64_eq in HC; try discriminate.
cbv zeta. rewrite rel_lit_same.
destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + l0 mod 2 ^ 64))%bool eqn:E.
* exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
destruct (ext_fits kk (kk + l0 mod 2 ^ 64)) eqn:F; [|discriminate].
rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
* destruct (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool; reflexivity.
+ destruct kb as [z| | | | | | |]; cbn [lit0_extent] in HC; try (destruct len; discriminate).
cbn in L. destruct z; try discriminate; destruct len; discriminate.
Qed.
Lemma know_lookupA0B_skipf : forall bc segs K rest rb rk n sx acc,
is_lit0 rb = false -> kx_candf K = false ->
know_lookupA0B bc segs (K :: rest) rb rk n sx [] acc = know_lookupA0B bc segs rest rb rk n sx [] acc.
Proof.
intros bc segs K rest rb rk n sx acc Hrb HC.
cbn [know_lookupA0B]. unfold kx_candf in HC.
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
try reflexivity; try discriminate.
-   destruct (is_lit0 kb) eqn:L; [|discriminate].
rewrite rel_lit_other; [reflexivity|]. rewrite (is_lit0_eqb rb kb L). exact Hrb.
-   destruct (is_lit0 kb) eqn:L; [|discriminate].
rewrite (is_lit0_eqb rb kb L), Hrb. reflexivity.
-   destruct rb as [z| | | | | | |]; try reflexivity. cbn in Hrb. destruct z; try reflexivity. discriminate.
Qed.
Lemma know_lookupA0B_filter0 : forall bc segs l rk n sx acc,
know_lookupA0B bc segs (List.filter (kx_cand0 (gran rk)) l) (ELit 0) rk (S n) sx [] acc
= know_lookupA0B bc segs l (ELit 0) rk (S n) sx [] acc.
Proof.
intros bc segs l rk n sx. induction l as [|K rest IH]; intros acc; [reflexivity|].
cbn [List.filter]. destruct (kx_cand0 (gran rk) K) eqn:HC.
-
cbn [know_lookupA0B]. rewrite !IH.
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity.
- rewrite know_lookupA0B_skip0 by exact HC. apply IH.
Qed.
Lemma know_lookupA0B_filterf : forall bc segs l rb rk n sx acc,
is_lit0 rb = false ->
know_lookupA0B bc segs (List.filter kx_candf l) rb rk n sx [] acc = know_lookupA0B bc segs l rb rk n sx [] acc.
Proof.
intros bc segs l rb rk n sx acc Hrb. revert acc. induction l as [|K rest IH]; intros acc; [reflexivity|].
cbn [List.filter]. destruct (kx_candf K) eqn:HC.
- cbn [know_lookupA0B]. rewrite !IH.
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity.
- rewrite know_lookupA0B_skipf by assumption. apply IH.
Qed.
Fixpoint tagged (kn : list kentry) (i : positive) : list (positive * kentry) :=
match kn with [] => [] | K :: rest => (i, K) :: tagged rest (Pos.succ i) end.
Definition all_gt (i : positive) (l : list (positive * kentry)) : Prop := Forall (fun t => (i < fst t)%positive) l.
Lemma filter_tagged_gt : forall P kn i j, (j < i)%positive -> all_gt j (List.filter P (tagged kn i)).
Proof.
intros P kn. induction kn as [|K rest IH]; intros i j Hj; cbn [tagged List.filter]; [constructor|].
destruct (P (i, K)).
- constructor; [cbn; lia|]. apply IH. lia.
- apply IH. lia.
Qed.
Lemma kx_merge_nil_l : forall l2, kx_merge [] l2 = List.map snd l2.
Proof. reflexivity. Qed.
Lemma kx_merge_cons_l : forall p K r1 l2,
all_gt p l2 -> kx_merge ((p, K) :: r1) l2 = K :: kx_merge r1 l2.
Proof.
intros p K r1 l2 H. destruct l2 as [|[p2 K2] r2]; cbn [kx_merge].
- destruct r1 as [|[? ?] ?]; reflexivity.
- apply Forall_inv in H. cbn in H. destruct (Pos.ltb_spec p p2); [reflexivity|lia].
Qed.
Lemma kx_merge_cons_r : forall p K l1 r2,
all_gt p l1 -> kx_merge l1 ((p, K) :: r2) = K :: kx_merge l1 r2.
Proof.
intros p K l1 r2 H. destruct l1 as [|[p1 K1] r1]; cbn [kx_merge List.map snd]; [reflexivity|].
apply Forall_inv in H. cbn in H. destruct (Pos.ltb_spec p1 p); [lia|reflexivity].
Qed.
Lemma kx_merge_filters : forall (P Q : kentry -> bool) kn i,
(forall K, P K = true -> Q K = false) ->
kx_merge (List.filter (fun t => P (snd t)) (tagged kn i)) (List.filter (fun t => Q (snd t)) (tagged kn i))
= List.filter (fun K => P K || Q K) kn.
Proof.
intros P Q kn. induction kn as [|K rest IH]; intros i HPQ; [reflexivity|].
cbn [tagged List.filter snd].
destruct (P K) eqn:HP.
- rewrite (HPQ K HP). cbn [orb]. rewrite kx_merge_cons_l; [rewrite IH; [reflexivity|exact HPQ]|].
apply filter_tagged_gt. lia.
- destruct (Q K) eqn:HQ; cbn [orb].
+ rewrite kx_merge_cons_r; [rewrite IH; [reflexivity|exact HPQ]|]. apply filter_tagged_gt. lia.
+ apply IH. exact HPQ.
Qed.
Definition narrow_in (g : Z) (K : kentry) : bool :=
match lit0_extent K with
| Some (s, e) => if ext_fits s e then ext_has s e g else false
| None => false
end.
Lemma kx_cand0_split : forall g K, kx_cand0 g K = (narrow_in g K || kx_wide0 K).
Proof.
intros g K. unfold kx_cand0, narrow_in, kx_wide0.
destruct (lit0_extent K) as [[s e]|]; [|reflexivity].
destruct (ext_fits s e); cbn [negb orb]; [rewrite Bool.orb_false_r|]; reflexivity.
Qed.
Lemma narrow_not_wide : forall g K, narrow_in g K = true -> kx_wide0 K = false.
Proof.
intros g K. unfold narrow_in, kx_wide0. destruct (lit0_extent K) as [[s e]|]; [|discriminate].
destruct (ext_fits s e); [reflexivity|discriminate].
Qed.
Lemma kx_gkey_inj : forall a b, kx_gkey a = kx_gkey b -> a = b.
Proof. intros [|a|a] [|b|b] H; cbn in H; congruence. Qed.
Lemma kx_bucket_add_same : forall g x t, kx_bucket (kx_add g x t) g = x :: kx_bucket t g.
Proof. intros. unfold kx_add, kx_bucket at 1. rewrite pt_gss. reflexivity. Qed.
Lemma kx_bucket_add_other : forall g g' x t, g <> g' -> kx_bucket (kx_add g' x t) g = kx_bucket t g.
Proof.
intros g g' x t H. unfold kx_add. unfold kx_bucket at 1. rewrite pt_gso; [reflexivity|].
intros E. apply H. apply kx_gkey_inj. exact E.
Qed.
Lemma kx_bucket_leaf : forall g, kx_bucket PTLeaf g = [].
Proof. intros. unfold kx_bucket. rewrite pt_get_leaf. reflexivity. Qed.
Lemma kx_build_spec : forall kn i w0 gr wf,
kx_build kn i = (w0, gr, wf) ->
w0 = List.filter (fun t => kx_wide0 (snd t)) (tagged kn i)
/\ (forall g, kx_bucket gr g = List.filter (fun t => narrow_in g (snd t)) (tagged kn i))
/\ wf = List.filter kx_candf kn.
Proof.
induction kn as [|K rest IH]; intros i w0 gr wf H.
- cbn in H. injection H as <- <- <-. split; [reflexivity|]. split; [intros g; rewrite kx_bucket_leaf; reflexivity | reflexivity].
- cbn [kx_build] in H. destruct (kx_build rest (Pos.succ i)) as [[w0' gr'] wf'] eqn:Hb.
destruct (IH (Pos.succ i) w0' gr' wf' Hb) as (A & B & C). clear IH.
cbn [tagged List.filter snd].
assert (NW : forall g, narrow_in g K = match lit0_extent K with Some (s, e) => if ext_fits s e then ext_has s e g else false | None => false end) by reflexivity.
assert (WD : kx_wide0 K = match lit0_extent K with
| Some (s, e) => negb (ext_fits s e)
| None => match K with
| KZero (SA kb _) _ | KFill (SA kb _) _ _ => true
| KBlob (SA kb _) _ _ => is_lit0 kb
| _ => false
end
end) by reflexivity.
destruct (lit0_extent K) as [[s e]|] eqn:HE.
+ destruct (ext_fits s e) eqn:HF.
*
match type of H with (_, ?G, _) = _ => set (gr1 := G) in H end.
injection H as <- <- <-. rewrite WD. cbn [negb]. split; [exact A|]. split; [|rewrite C; reflexivity].
intros g. rewrite NW.
assert (STEP : kx_bucket gr1 g = if ext_has s e g then (i, K) :: kx_bucket gr' g else kx_bucket gr' g).
{ subst gr1. unfold ext_has. destruct (Z.eqb_spec (gran s) (gran (e - 1))) as [EQ|NE].
- destruct (Z.eqb_spec g (gran s)) as [->|NE1].
+ rewrite kx_bucket_add_same. reflexivity.
+ rewrite kx_bucket_add_other by exact NE1. destruct (Z.eqb_spec g (gran (e - 1))); [congruence|reflexivity].
- destruct (Z.eqb_spec g (gran s)) as [->|NE1].
+ rewrite kx_bucket_add_other by exact NE. rewrite kx_bucket_add_same. reflexivity.
+ destruct (Z.eqb_spec g (gran (e - 1))) as [->|NE2].
* rewrite kx_bucket_add_same. rewrite kx_bucket_add_other by exact NE1. reflexivity.
* rewrite kx_bucket_add_other by exact NE2. rewrite kx_bucket_add_other by exact NE1. reflexivity. }
rewrite STEP, B. reflexivity.
*
injection H as <- <- <-. rewrite WD. cbn [negb]. split; [rewrite A; reflexivity|]. split; [|rewrite C; reflexivity].
intros g. rewrite NW, B. reflexivity.
+ clear WD. destruct (kx_wide0 K); injection H as <- <- <-.
* split; [rewrite A; reflexivity|]. split; [|rewrite C; reflexivity]. intros g. rewrite NW, B. reflexivity.
* split; [exact A|]. split; [|rewrite C; reflexivity]. intros g. rewrite NW, B. reflexivity.
Qed.
Lemma kx_select_eq : forall kn rb rk,
kx_select (mk_kix kn) rb rk = if is_lit0 rb then List.filter (kx_cand0 (gran rk)) kn else List.filter kx_candf kn.
Proof.
intros kn rb rk. unfold kx_select, mk_kix.
destruct (kx_build kn 1%positive) as [[w0 gr] wf] eqn:Hb. cbn [kx_gran kx_w0 kx_wf fst snd].
destruct (kx_build_spec kn 1%positive w0 gr wf Hb) as (A & B & C).
destruct (is_lit0 rb); [|exact C].
rewrite B, A. rewrite (kx_merge_filters (narrow_in (gran rk)) kx_wide0 kn 1%positive (narrow_not_wide (gran rk))).
apply filter_ext. intros K. symmetry. apply kx_cand0_split.
Qed.
Theorem know_lookupA0I_eq : forall bc kn segs rb rk n sx hints acc,
know_lookupA0I bc (mk_kix kn) segs rb rk n sx hints acc = know_lookupA0B bc segs kn rb rk n sx hints acc.
Proof.
intros bc kn segs rb rk n sx hints acc. unfold know_lookupA0I.
destruct hints as [|h hs]; [|reflexivity]. destruct n as [|n]; [reflexivity|].
rewrite kx_select_eq. destruct (is_lit0 rb) eqn:L.
- apply is_lit0_true in L. subst rb. apply know_lookupA0B_filter0.
- apply know_lookupA0B_filterf. exact L.
Qed.
Definition know_lookupABI (bc : bctx) (kx : kix) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
(n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
match know_lookupA0I bc kx segs rb rk n sx hints acc with
| LMiss acc' hints' =>
match know_bytes_lit segs kn rb rk n with
| Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
| None => LMiss acc' hints'
end
| r => r
end.
Lemma know_lookupABI_eq : forall bc kn segs,
know_lookupABI bc (mk_kix kn) segs kn = know_lookupAB bc segs kn.
Proof.
intros bc kn segs. bcfe. unfold know_lookupABI, know_lookupAB. rewrite know_lookupA0I_eq. reflexivity.
Qed.
Local Close Scope Z_scope.
Definition sym_readBI (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (scr : scripts)
(a : saddr) (n : nat) (sx' : bool)
: option (expr * list sidecond * scripts * nat) :=
match log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
| LStuck => None
| LHit v scs hints =>
Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
| LMiss scs hints =>
match know_lookupABI bc kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
| LStuck => None
| LHit v scs' hints' =>
Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
| LMiss scs' hints' =>
let i := s_next ss in
let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
end
end.
Definition sym_stepBI (bc : bctx) (kx : kix) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
let g r := sr_get (s_regs ss) r in
let p := s_pc ss in
match i with
| OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
| ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
| Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
| OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
| ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
| Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
| Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
| Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
| Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
| Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
| Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
| Jalr rd rs1 imm =>
match conc_exprB bc (g rs1) with
| ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
| _ => SStop
end
| Branch c rs1 rs2 imm =>
let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
let a := g rs1 in let b := g rs2 in
match match decide_branchB bc c a b with
| Some t => Some t
| None => match decide_branchB bc c (conc_exprB bc a) (conc_exprB bc b) with
| Some t => Some t
| None => enum_branchB bc c a b
end
end with
| Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
| None =>
match sc_dirs scr with
| [] => SStop
| t :: dirs' =>
SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
(SCR dirs' (sc_reads scr) (sc_hints scr))
end
end
| Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
| FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
| Load sz sx rd rs imm =>
let n := msize_bytes sz in
let sx' := match sz with SZ8 => false | _ => sx end in
let a := to_saddrKB bc (g rs) (bv_signed imm) in
match sym_readBI segs ss bc kx scr a n sx' with
| None => SStop
| Some (v, scs, scr', nx') =>
SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
(s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
end
| Store sz rs1 rs2 imm =>
let n := msize_bytes sz in
let a := to_saddrKB bc (g rs1) (bv_signed imm) in
match resv_inval (s_resv ss) a with
| None => SStop
| Some r' =>
SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
(flat_scB bc a n ++ storeok_scB bc a n) scr
end
| Lr wd _ _ rd rs =>
let n := msize_bytes (amo_sz wd) in
let e := g rs in
if amo_alignedbB bc e wd then
let a := to_saddrKB bc e 0 in
match sym_readBI segs ss bc kx scr a n (amo_sx wd) with
| None => SStop
| Some (v, scs, scr', nx') =>
SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
(s_log ss) (s_know ss) nx' (Some a)) scs scr'
end
else SStop
| Sc wd _ _ rd rs1 rs2 =>
let n := msize_bytes (amo_sz wd) in
let e := g rs1 in
if amo_alignedbB bc e wd then
let a := to_saddrKB bc e 0 in
match s_resv ss with
| Some r =>
if saddr_eqb r a then
SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
(SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
(flat_scB bc a n ++ storeok_scB bc a n) scr
else SStop
| None => SStop
end
else SStop
| Amo op wd _ _ rd rs1 rs2 =>
match amo_aluop op with
| None => SStop
| Some aop =>
let n := msize_bytes (amo_sz wd) in
let e := g rs1 in
if amo_alignedbB bc e wd then
let a := to_saddrKB bc e 0 in
match resv_inval (s_resv ss) a with
| None => SStop
| Some r' =>
match sym_readBI segs ss bc kx scr a n (amo_sx wd) with
| None => SStop
| Some (vold, scs, scr', nx') =>
SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
(SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
(scs ++ storeok_scB bc a n) scr'
end
end
else SStop
end
| _ => SStop
end.
Lemma sym_readBI_eqf : forall segs ss bc, sym_readBI segs ss bc (mk_kix (s_know ss)) = sym_readB segs ss bc.
Proof. intros. bcfe. unfold sym_readBI, sym_readB. rewrite know_lookupABI_eq. reflexivity. Qed.
Lemma sym_stepBI_eq : forall bc segs i ss scr,
sym_stepBI bc (mk_kix (s_know ss)) segs i ss scr = sym_stepB bc segs i ss scr.
Proof. intros. unfold sym_stepBI, sym_stepB. rewrite sym_readBI_eqf. reflexivity. Qed.
Lemma coeffs_divkB_eqf : forall fk, coeffs_divkB (mkbc fk) = coeffs_divk fk.
Proof.
intros fk. apply functional_extensionality; intros m. apply functional_extensionality; intros ts.
induction ts as [|[k a] rest IH]; intros; bcfe; [reflexivity|].
cbn [coeffs_divkB coeffs_divk]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite coeffs_divkB_eqf : bceq.
Lemma lin_lowbits_knB_eqf : forall fk, lin_lowbits_knB (mkbc fk) = lin_lowbits_kn fk.
Proof. intros. bcfe. unfold lin_lowbits_knB, lin_lowbits_kn. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_lowbits_knB_eqf : bceq.
Lemma lin_nowrap_lB_eqf : forall fk, lin_nowrap_lB (mkbc fk) = lin_nowrap_l fk.
Proof. intros. bcfe. unfold lin_nowrap_lB, lin_nowrap_l. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_nowrap_lB_eqf : bceq.
Lemma mkSrlB_eqf : forall fk, mkSrlB (mkbc fk) = mkSrl fk.
Proof. intros. bcfe. unfold mkSrlB, mkSrl. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkSrlB_eqf : bceq.
Lemma lowbitsB_eqf : forall fk, lowbitsB (mkbc fk) = lowbits fk.
Proof.
intros fk. apply functional_extensionality; intros e.
induction e; bcfe; cbn [lowbitsB lowbits]; rewrite ?IHe1, ?IHe2, ?IHe; autorewrite with bceq; reflexivity.
Qed.
#[export] Hint Rewrite lowbitsB_eqf : bceq.
Lemma lsplit_divB_eqf : forall fk, lsplit_divB (mkbc fk) = lsplit_div fk.
Proof.
intros fk. apply functional_extensionality; intros m. apply functional_extensionality; intros ts.
induction ts as [|[k a] rest IH]; intros; bcfe; [reflexivity|].
cbn [lsplit_divB lsplit_div]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite lsplit_divB_eqf : bceq.
Lemma and_high_splitB_eqf : forall fk, and_high_splitB (mkbc fk) = and_high_split fk.
Proof. intros. bcfe. unfold and_high_splitB, and_high_split. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite and_high_splitB_eqf : bceq.
Lemma and_low_splitB_eqf : forall fk, and_low_splitB (mkbc fk) = and_low_split fk.
Proof. intros. bcfe. unfold and_low_splitB, and_low_split. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite and_low_splitB_eqf : bceq.
Lemma narrow_maskB_eqf : forall fk, narrow_maskB (mkbc fk) = narrow_mask fk.
Proof. intros. bcfe. unfold narrow_maskB, narrow_mask. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite narrow_maskB_eqf : bceq.
Lemma mkAnd0B_eqf : forall fk, mkAnd0B (mkbc fk) = mkAnd0 fk.
Proof. intros. bcfe. unfold mkAnd0B, mkAnd0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAnd0B_eqf : bceq.
Lemma mkAndB_eqf : forall fk, mkAndB (mkbc fk) = mkAnd fk.
Proof. intros. bcfe. unfold mkAndB, mkAnd. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAndB_eqf : bceq.
Lemma mkAndKB_eqf : forall fk, mkAndKB (mkbc fk) = mkAndK fk.
Proof. intros. bcfe. unfold mkAndKB, mkAndK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAndKB_eqf : bceq.
Lemma or_disjointB_eqf : forall fk, or_disjointB (mkbc fk) = or_disjoint fk.
Proof. intros. bcfe. unfold or_disjointB, or_disjoint. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite or_disjointB_eqf : bceq.
Lemma mkOrB_eqf : forall fk, mkOrB (mkbc fk) = mkOr fk.
Proof. intros. bcfe. unfold mkOrB, mkOr. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkOrB_eqf : bceq.
Lemma conc_tryB_eqf : forall fk, conc_tryB (mkbc fk) = conc_try fk.
Proof.
intros fk. apply functional_extensionality; intros e. apply functional_extensionality; intros cands.
induction cands as [|s rest IH]; intros; bcfe; [reflexivity|].
cbn [conc_tryB conc_try]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite conc_tryB_eqf : bceq.
Lemma concretizeB_eqf : forall fk, concretizeB (mkbc fk) = concretize fk.
Proof. intros. bcfe. unfold concretizeB, concretize. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite concretizeB_eqf : bceq.
Lemma foldKB_eqf : forall fk, foldKB (mkbc fk) = foldK fk.
Proof. intros. bcfe. unfold foldKB, foldK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite foldKB_eqf : bceq.
Lemma lin_branchB_eqf : forall fk, lin_branchB (mkbc fk) = lin_branch fk.
Proof. intros. bcfe. unfold lin_branchB, lin_branch. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite lin_branchB_eqf : bceq.
Lemma decide_branchB_eqf : forall fk, decide_branchB (mkbc fk) = decide_branch fk.
Proof. intros. bcfe. unfold decide_branchB, decide_branch. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite decide_branchB_eqf : bceq.
Lemma mkSltB_eqf : forall fk, mkSltB (mkbc fk) = mkSlt fk.
Proof. intros. bcfe. unfold mkSltB, mkSlt. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkSltB_eqf : bceq.
Lemma mkAluK0B_eqf : forall fk, mkAluK0B (mkbc fk) = mkAluK0 fk.
Proof. intros. bcfe. unfold mkAluK0B, mkAluK0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAluK0B_eqf : bceq.
Lemma mkAluKB_eqf : forall fk, mkAluKB (mkbc fk) = mkAluK fk.
Proof. intros. bcfe. unfold mkAluKB, mkAluK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAluKB_eqf : bceq.
Lemma mkMdKB_eqf : forall fk, mkMdKB (mkbc fk) = mkMdK fk.
Proof. intros. bcfe. unfold mkMdKB, mkMdK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkMdKB_eqf : bceq.
Lemma zband32B_eqf : forall fk, zband32B (mkbc fk) = zband32 fk.
Proof. intros. bcfe. unfold zband32B, zband32. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite zband32B_eqf : bceq.
Lemma mkAluwK0B_eqf : forall fk, mkAluwK0B (mkbc fk) = mkAluwK0 fk.
Proof. intros. bcfe. unfold mkAluwK0B, mkAluwK0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAluwK0B_eqf : bceq.
Lemma mkAluwKB_eqf : forall fk, mkAluwKB (mkbc fk) = mkAluwK fk.
Proof. intros. bcfe. unfold mkAluwKB, mkAluwK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite mkAluwKB_eqf : bceq.
Lemma extK0B_eqf : forall fk, extK0B (mkbc fk) = extK0 fk.
Proof. intros. bcfe. unfold extK0B, extK0. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite extK0B_eqf : bceq.
Lemma extKB_eqf : forall fk, extKB (mkbc fk) = extK fk.
Proof. intros. bcfe. unfold extKB, extK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite extKB_eqf : bceq.
Lemma flat_scB_eqf : forall fk, flat_scB (mkbc fk) = flat_sc fk.
Proof. intros. bcfe. unfold flat_scB, flat_sc. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite flat_scB_eqf : bceq.
Lemma wr_coveredB_eqf : forall fk, wr_coveredB (mkbc fk) = wr_covered fk.
Proof.
intros fk. apply functional_extensionality; intros kn.
induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [wr_coveredB wr_covered]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite wr_coveredB_eqf : bceq.
Lemma storeok_scB_eqf : forall fk, storeok_scB (mkbc fk) = storeok_sc fk.
Proof. intros. bcfe. unfold storeok_scB, storeok_sc. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite storeok_scB_eqf : bceq.
Lemma conc_exprB_eqf : forall fk, conc_exprB (mkbc fk) = conc_expr fk.
Proof. intros. bcfe. unfold conc_exprB, conc_expr. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite conc_exprB_eqf : bceq.
Lemma enum_branchB_eqf : forall fk, enum_branchB (mkbc fk) = enum_branch fk.
Proof. intros. bcfe. unfold enum_branchB, enum_branch. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite enum_branchB_eqf : bceq.
Lemma to_saddrKB_eqf : forall fk, to_saddrKB (mkbc fk) = to_saddrK fk.
Proof. intros. bcfe. unfold to_saddrKB, to_saddrK. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite to_saddrKB_eqf : bceq.
Lemma amo_alignedbB_eqf : forall fk, amo_alignedbB (mkbc fk) = amo_alignedb fk.
Proof. intros. bcfe. unfold amo_alignedbB, amo_alignedb. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite amo_alignedbB_eqf : bceq.
Lemma amo_newvalB_eqf : forall fk, amo_newvalB (mkbc fk) = amo_newval fk.
Proof. intros. bcfe. unfold amo_newvalB, amo_newval. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite amo_newvalB_eqf : bceq.
Lemma log_lookupB_eqf : forall fk, log_lookupB (mkbc fk) = log_lookup fk.
Proof.
intros fk. apply functional_extensionality; intros log.
induction log as [|[[kb kk] w v] rest IH]; intros; bcfe; [reflexivity|].
cbn [log_lookupB log_lookup]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite log_lookupB_eqf : bceq.
Lemma know_lookupA0B_eqf : forall fk, know_lookupA0B (mkbc fk) = know_lookupA0 fk.
Proof.
intros fk. apply functional_extensionality; intros segs. apply functional_extensionality; intros kn.
induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [know_lookupA0B know_lookupA0]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite know_lookupA0B_eqf : bceq.
Lemma know_lookupAB_eqf : forall fk, know_lookupAB (mkbc fk) = know_lookupA fk.
Proof. intros. bcfe. unfold know_lookupAB, know_lookupA. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite know_lookupAB_eqf : bceq.
Lemma sym_readB_eqf : forall fk segs ss, sym_readB segs ss (mkbc fk) = sym_read segs ss fk.
Proof. intros. bcfe. unfold sym_readB, sym_read. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite sym_readB_eqf : bceq.
Lemma know_lookupB_eqf : forall fk segs, know_lookupB segs (mkbc fk) = know_lookup segs fk.
Proof. intros. bcfe. unfold know_lookupB, know_lookup. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite know_lookupB_eqf : bceq.
Lemma sym_stepB_eq : forall segs i ss scr,
sym_stepB (mkbc (facts_of (s_know ss))) segs i ss scr = sym_step segs i ss scr.
Proof. intros. unfold sym_stepB, sym_step. autorewrite with bceq. reflexivity. Qed.
Lemma sym_step_know : forall segs i ss scr ss' scs scr',
sym_step segs i ss scr = SOk ss' scs scr' -> s_know ss' = s_know ss.
Proof.
intros segs i ss scr ss' scs scr' H. unfold sym_step, sym_read in H.
destruct i; try discriminate;
repeat (lazymatch type of H with
| SOk _ _ _ = SOk _ _ _ => injection H as <- _ _
| (match ?x with _ => _ end) = _ => destruct x
| (let (_, _) := ?x in _) = _ => destruct x
| (if ?x then _ else _) = _ => destruct x
end); try discriminate; try reflexivity.
Qed.
Section u.
Variable segs : list Segment.
Definition zf_coversB (bc : bctx) (rb : expr) (rk : Z) (n : nat) (kb : expr) (kk : Z) (len : expr) : bool :=
(match len with
| ELit l0 => match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2 ^ 64)%Z with RInside _ => true | _ => false end
| _ => false
end) || xinsideB bc rb rk (elen n) kb kk len.
Definition kentry_overlayB (bc : bctx) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
match K with
| KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
zf_coversB bc rb rk n kb kk len
| _ => false
end.
Definition kentry_readableB (bc : bctx) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
match K with
| KWord (SA kb kk) w _ =>
match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with RInside _ => true | _ => false end
| _ => kentry_overlayB bc rb rk n K
end.
Definition kn_readableB (bc : bctx) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
existsb (kentry_readableB bc rb rk n) kn || know_bytes_cov segs true kn rb rk n.
Definition kn_overlayB (bc : bctx) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
existsb (kentry_overlayB bc rb rk n) kn || know_bytes_cov segs false kn rb rk n.
Definition x_dischargeableB (bc : bctx) (ss ss' : sym_state) (rb : option (saddr * nat * bool)) (sc : sidecond) : bool :=
let kn := s_know ss in
match sc with
| SCReadBase a n sx (EVar j) =>
(match rb with
| Some (a', n', sx') => saddr_eqb a' a && Nat.eqb n' n && Bool.eqb sx' sx
| None => false
end)
&& Nat.eqb j (s_next ss) && Nat.ltb j (s_next ss') && evars_lt (s_next ss) (a_base a)
&& Nat.leb 1 n && Nat.leb n 8 && kn_readable segs (bc_fk bc) kn (a_base a) (a_off a) n
| SCFlat a (ELit z) =>
Z.leb 1 z && Z.leb z 8 && kn_readable segs (bc_fk bc) kn (a_base a) (a_off a) (Z.to_nat z)
| SCStoreOk a n => Nat.leb 1 n && Nat.leb n 8 && kn_overlay segs (bc_fk bc) kn (a_base a) (a_off a) n
| _ => false
end%bool.
Definition x_filterB (bc : bctx) (ss ss' : sym_state) (scs : list sidecond) : list sidecond :=
match scs with
| [] => []
| _ => let rb := find_readbase (s_next ss) scs in
List.filter (fun sc => negb (x_dischargeableB bc ss ss' rb sc)) scs
end.
Definition sym_stepXB (bc : bctx) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
match sym_stepB bc segs i ss scr with
| SOk ss' scs scr' =>
if Nat.leb (s_next ss) (s_next ss')
then SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'
else SStop
| SStop => SStop
end.
Lemma zf_coversB_eqf : forall fk, zf_coversB (mkbc fk) = zf_covers fk.
Proof. intros. bcfe. unfold zf_coversB, zf_covers. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite zf_coversB_eqf : bceq.
Lemma kentry_overlayB_eqf : forall fk, kentry_overlayB (mkbc fk) = kentry_overlay fk.
Proof. intros. bcfe. unfold kentry_overlayB, kentry_overlay. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kentry_overlayB_eqf : bceq.
Lemma kentry_readableB_eqf : forall fk, kentry_readableB (mkbc fk) = kentry_readable fk.
Proof. intros. bcfe. unfold kentry_readableB, kentry_readable. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kentry_readableB_eqf : bceq.
Lemma kn_readableB_eqf : forall fk, kn_readableB (mkbc fk) = kn_readable segs fk.
Proof. intros. bcfe. unfold kn_readableB, kn_readable. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_readableB_eqf : bceq.
Lemma kn_overlayB_eqf : forall fk, kn_overlayB (mkbc fk) = kn_overlay segs fk.
Proof. intros. bcfe. unfold kn_overlayB, kn_overlay. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_overlayB_eqf : bceq.
Lemma x_dischargeableB_eq : forall ss ss' rb sc,
x_dischargeableB (mkbc (facts_of (s_know ss))) ss ss' rb sc = x_dischargeable segs ss ss' rb sc.
Proof. intros. unfold x_dischargeableB, x_dischargeable. autorewrite with bceq. reflexivity. Qed.
Lemma x_filterB_eq : forall ss ss' scs,
x_filterB (mkbc (facts_of (s_know ss))) ss ss' scs = x_filter segs ss ss' scs.
Proof.
intros. unfold x_filterB, x_filter. destruct scs as [|sc rest]; [reflexivity|].
erewrite filter_ext; [reflexivity|]. intros x. rewrite x_dischargeableB_eq. reflexivity.
Qed.
Lemma cap_rd_know : forall K i ss, s_know (cap_rd K i ss) = s_know ss.
Proof.
intros K i ss. unfold cap_rd. destruct K; [reflexivity|]. destruct (rd_of i) as [rd|]; [|reflexivity].
destruct (bv_eqb rd 0); [reflexivity|]. destruct (esize_le (sr_get (s_regs ss) rd) (S K)); reflexivity.
Qed.
Lemma sym_stepXB_eq : forall K i ss scr,
sym_stepXB (mkbc (facts_of (s_know ss))) K i ss scr = sym_stepX segs K i ss scr.
Proof.
intros. unfold sym_stepXB, sym_stepX. rewrite sym_stepB_eq.
destruct (sym_step segs i ss scr) as [ss' scs scr'|]; [|reflexivity]. rewrite x_filterB_eq. reflexivity.
Qed.
Lemma sym_stepX_know : forall K i ss scr ss' scs scr',
sym_stepX segs K i ss scr = SOk ss' scs scr' -> s_know ss' = s_know ss.
Proof.
intros K i ss scr ss' scs scr' H. unfold sym_stepX in H.
destruct (sym_step segs i ss scr) as [ss1 scs1 scr1|] eqn:E; [|discriminate].
destruct (Nat.leb (s_next ss) (s_next ss1)); [|discriminate]. injection H as <- _ _.
rewrite cap_rd_know. exact (sym_step_know _ _ _ _ _ _ _ E).
Qed.
Fixpoint sym_execTXB_go (bc : bctx) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
: sym_state :=
match fuel with
| O => if s_clean ss then ss else ck
| S f =>
if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
match itab_lookup t (s_pc ss) with
| None => if s_clean ss then ss else ck
| Some i =>
match sym_stepXB bc K i ss scr_nil with
| SOk ss' [] _ => sym_execTXB_go bc t K f false stops ss' (if s_clean ss' then ss' else ck)
| _ => if s_clean ss then ss else ck
end
end
end.
Definition sym_execTXB (bc : bctx) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
sym_execTXB_go bc t K fuel first stops (clr ss) (clr ss).
Lemma sym_execTXB_go_eq : forall t K fuel first stops ss ck,
sym_execTXB_go (mkbc (facts_of (s_know ss))) t K fuel first stops ss ck = sym_execTX_go segs t K fuel first stops ss ck.
Proof.
intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck; [reflexivity|].
cbn [sym_execTXB_go sym_execTX_go].
destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
rewrite sym_stepXB_eq. destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|reflexivity].
destruct scs; [|reflexivity].
rewrite <- (sym_stepX_know _ _ _ _ _ _ _ E). apply IH.
Qed.
Lemma sym_execTXB_eq : forall kn0 t K fuel first stops ss,
s_know ss = kn0 ->
sym_execTXB (mkbc (facts_of kn0)) t K fuel first stops ss = sym_execTX segs t K fuel first stops ss.
Proof.
intros kn0 t K fuel first stops ss <-. unfold sym_execTXB, sym_execTX.
replace (s_know ss) with (s_know (clr ss)) by (destruct ss; reflexivity).
apply sym_execTXB_go_eq.
Qed.
Lemma sym_execTX_go_know : forall t K fuel first stops ss ck,
s_know ck = s_know ss ->
s_know (sym_execTX_go segs t K fuel first stops ss ck) = s_know ss.
Proof.
intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck Hck.
- cbn. destruct (s_clean ss); [reflexivity|exact Hck].
- cbn [sym_execTX_go].
destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [destruct (s_clean ss); [reflexivity|exact Hck]|].
destruct (itab_lookup t (s_pc ss)) as [i|]; [|destruct (s_clean ss); [reflexivity|exact Hck]].
destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|destruct (s_clean ss); [reflexivity|exact Hck]].
destruct scs; [|destruct (s_clean ss); [reflexivity|exact Hck]].
pose proof (sym_stepX_know _ _ _ _ _ _ _ E) as HK.
rewrite IH; [exact HK|]. destruct (s_clean ss'); [reflexivity|]. rewrite Hck, HK. reflexivity.
Qed.
Lemma sym_execTX_know : forall t K fuel first stops ss,
s_know (sym_execTX segs t K fuel first stops ss) = s_know ss.
Proof.
intros. unfold sym_execTX. rewrite sym_execTX_go_know; [|reflexivity]. destruct ss; reflexivity.
Qed.
Definition sym_stepXBI (bc : bctx) (kx : kix) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
match sym_stepBI bc kx segs i ss scr with
| SOk ss' scs scr' =>
if Nat.leb (s_next ss) (s_next ss')
then SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'
else SStop
| SStop => SStop
end.
Lemma sym_stepXBI_eq : forall K i ss scr,
sym_stepXBI (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) K i ss scr = sym_stepX segs K i ss scr.
Proof.
intros. unfold sym_stepXBI. rewrite sym_stepBI_eq. fold (sym_stepXB (mkbc (facts_of (s_know ss))) K i ss scr). apply sym_stepXB_eq.
Qed.
Fixpoint sym_execTXBI_go (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
: sym_state :=
match fuel with
| O => if s_clean ss then ss else ck
| S f =>
if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
match itab_lookup t (s_pc ss) with
| None => if s_clean ss then ss else ck
| Some i =>
match sym_stepXBI bc kx K i ss scr_nil with
| SOk ss' [] _ => sym_execTXBI_go bc kx t K f false stops ss' (if s_clean ss' then ss' else ck)
| _ => if s_clean ss then ss else ck
end
end
end.
Definition sym_execTXBI (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
sym_execTXBI_go bc kx t K fuel first stops (clr ss) (clr ss).
Lemma sym_execTXBI_go_eq : forall t K fuel first stops ss ck,
sym_execTXBI_go (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) t K fuel first stops ss ck = sym_execTX_go segs t K fuel first stops ss ck.
Proof.
intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck; [reflexivity|].
cbn [sym_execTXBI_go sym_execTX_go].
destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
rewrite sym_stepXBI_eq. destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|reflexivity].
destruct scs; [|reflexivity].
rewrite <- (sym_stepX_know _ _ _ _ _ _ _ E). apply IH.
Qed.
Lemma sym_execTXBI_eq : forall kn0 t K fuel first stops ss,
s_know ss = kn0 ->
sym_execTXBI (mkbc (facts_of kn0)) (mk_kix kn0) t K fuel first stops ss = sym_execTX segs t K fuel first stops ss.
Proof.
intros kn0 t K fuel first stops ss <-. unfold sym_execTXBI, sym_execTX.
replace (s_know ss) with (s_know (clr ss)) by (destruct ss; reflexivity).
apply sym_execTXBI_go_eq.
Qed.
End u.
Definition kcutB (bc : bctx) (mk : saddr -> expr -> kentry) (wb : expr) (wk : Z) (wn : expr)
(kb : expr) (kk : Z) (len : expr) : list kentry :=
let ws := mkAlu ALU_ADD wb (ELit wk) in
let ks := mkAlu ALU_ADD kb (ELit kk) in
let low :=
if (if lin_ge0B bc [(kb, kk)] [(wb, wk)] then false
else if lin_ge0B bc [(wb, wk)] [(kb, kk)] then lin_ge0B bc [(kb, kk); (len, 0%Z)] [(wb, wk)] else false)
then [mk (SA kb kk) (mkAlu ALU_SUB ws ks)] else [] in
let high :=
if (if lin_ge0B bc [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]
then if lin_ge0B bc [(wb, wk); (wn, 0%Z)] [(kb, kk)]
then lin_ge0B bc [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]
else false
else false)
then let we := mkAlu ALU_ADD ws wn in
let '(hb, ho) := split_lit we in
let ha := if (lin_ge0B bc [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0B bc [(wb, wk); (wn, 0%Z)] [(hb, ho)])%bool
then SA hb ho else SA we 0%Z in
[mk ha (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)]
else [] in
low ++ high.
Definition kzero_cutB (bc : bctx) (wb : expr) (wk : Z) (wn : expr)
(kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc KZero wb wk wn kb kk len.
Definition kfill_cutB (bc : bctx) (c : Z) (wb : expr) (wk : Z) (wn : expr)
(kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc (fun a n => KFill a n c) wb wk wn kb kk len.
Definition kunk_cutB (bc : bctx) (wb : expr) (wk : Z) (wn : expr)
(kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc KUnk wb wk wn kb kk len.
Definition prune_zfB (bc : bctx) (mk : saddr -> expr -> kentry) (wb : expr) (k : Z) (w : nat)
(K : kentry) (kb : expr) (kk : Z) (len : expr) (apart : unit -> bool) (hints : list bool)
(diffbase : unit -> list kentry * list sidecond * list bool)
: list kentry * list sidecond * list bool :=
if expr_eqb kb wb then
match len with
| ELit l0 => (ktrim mk kb kk l0 k w, [], hints)
| _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints)
else (kcutB bc mk wb k (elen w) kb kk len, [], hints)
end
else if apart tt then ([K], [], hints)
else match kcutB bc mk wb k (elen w) kb kk len with
| [] => diffbase tt
| cut => (cut, [], hints)
end.
Definition prune1pB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
: list kentry * list sidecond * list bool :=
let k := a_off wa in
let diffbase (ka : saddr) (kl : expr) :=
let apart := ranges_apart_pB bc sp (a_base wa) k (elen w) (a_base ka) (a_off ka) kl in
if apart then ([K], [], hints) else
match hints with
| true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)
| false :: hs => ([], [], hs)
| [] => ([], [], [])
end in
match K with
| KAlign _ _ => ([K], [], hints)
| KRange _ _ _ => ([K], [], hints)
| KWr _ _ => ([K], [], hints)
| KDisj _ _ _ _ => ([K], [], hints)
| KImg lo hi =>
match a_base wa with
| ELit 0 =>
let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
let lo2 := Z.max lo (k + Z.of_nat w) in
let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
(r1 ++ r2, [], hints)
| _ => if Z.ltb (hi - lo) (2 ^ 64) then diffbase (SA (ELit 0) lo) (ELit (hi - lo))
else ([], [], hints)
end
| KZero (SA kb kk) len =>
prune_zfB bc KZero (a_base wa) k w K kb kk len
(fun _ => ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
| KFill (SA kb kk) len c =>
prune_zfB bc (fun a n => KFill a n c) (a_base wa) k w K kb kk len
(fun _ => ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
| KUnk (SA kb kk) len =>
prune_zfB bc KUnk (a_base wa) k w K kb kk len
(fun _ => ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
| KWord (SA kb kk) w' v =>
if expr_eqb kb (a_base wa) then
(if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints))
else if ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk (elen w') then ([K], [], hints)
else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
then ([K], [], hints)
else diffbase (SA kb kk) (elen w')
| KBlob (SA kb kk) len bk =>
if expr_eqb kb (a_base wa) then
match len with
| ELit l0 =>
let l := (l0 mod 2 ^ 64)%Z in
(if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool
then ([K], [], hints) else ([], [], hints))
| _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
end
else diffbase (SA kb kk) len
end.
Definition ranges_apart_pcB (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
(br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
match n1, n2 with
| ELit z1, ELit z2 =>
let m1 := zlit64 z1 in let m2 := zlit64 z2 in
if (match sp_rng sp, br2 with
| Some (lo1, hi1), Some (lo2, hi2) =>
(Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
| _, _ => false
end) then true
else if in_sidesB bc (sp_D sp) b2 k2 m2 then true
else lin_apartB bc b1 k1 m1 b2 k2 m2
| _, _ =>
if (match sp_rng sp, br2, sp_h1 sp, xhiB bc n2 with
| Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
else
if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
| _, _, _, _ => false
end) then true
else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
else if negb (shares_var b1 b2) then false
else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
end.
Definition prune1pcB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
(br2 : option (Z * Z)) : list kentry * list sidecond * list bool :=
let k := a_off wa in
let diffbase (ka : saddr) (kl : expr) :=
let apart := ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 (a_base ka) (a_off ka) kl in
if apart then ([K], [], hints) else
match hints with
| true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)
| false :: hs => ([], [], hs)
| [] => ([], [], [])
end in
match K with
| KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ | KImg _ _ => prune1pB bc sp wa w wv K hints
| KZero (SA kb kk) len =>
if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
else match kzero_cutB bc (a_base wa) k (elen w) kb kk len with
| [] => diffbase (SA kb kk) len
| cut => (cut, [], hints)
end
| KFill (SA kb kk) len c =>
if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
else match kfill_cutB bc c (a_base wa) k (elen w) kb kk len with
| [] => diffbase (SA kb kk) len
| cut => (cut, [], hints)
end
| KUnk (SA kb kk) len =>
if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
else match kunk_cutB bc (a_base wa) k (elen w) kb kk len with
| [] => diffbase (SA kb kk) len
| cut => (cut, [], hints)
end
| KWord (SA kb kk) w' v =>
if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk (elen w') then ([K], [], hints)
else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
then ([K], [], hints)
else diffbase (SA kb kk) (elen w')
| KBlob (SA kb kk) len bk =>
if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
else diffbase (SA kb kk) len
end.
Fixpoint prunepcB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
(cache : list (expr * option (Z * Z))) : list kentry * list sidecond * list bool :=
match kn with
| [] => ([], [], hints)
| K :: rest =>
let '(br2, cache') :=
match kbase K with
| Some kb => match br_lookup cache kb with
| Some r => (r, cache)
| None => let r := base_rangeB bc kb in (r, (kb, r) :: cache)
end
| None => (None, cache)
end in
let '(kept, scs1, hs1) := prune1pcB bc sp wa w wv K hints br2 in
let '(r, scs2, hs2) := prunepcB bc sp wa w wv rest hs1 cache' in
(kept ++ r, scs1 ++ scs2, hs2)
end.
Lemma kcutB_eqf : forall fk, kcutB (mkbc fk) = (fun mk => kcut mk fk).
Proof. intros. bcfe. unfold kcutB, kcut. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite kcutB_eqf : bceq.
Lemma kzero_cutB_eqf : forall fk, kzero_cutB (mkbc fk) = kzero_cut fk.
Proof. intros. bcfe. unfold kzero_cutB, kzero_cut. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite kzero_cutB_eqf : bceq.
Lemma kfill_cutB_eqf : forall fk, kfill_cutB (mkbc fk) = (fun c => kfill_cut c fk).
Proof. intros. bcfe. unfold kfill_cutB, kfill_cut. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite kfill_cutB_eqf : bceq.
Lemma kunk_cutB_eqf : forall fk, kunk_cutB (mkbc fk) = kunk_cut fk.
Proof. intros. bcfe. unfold kunk_cutB, kunk_cut. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite kunk_cutB_eqf : bceq.
Lemma prune_zfB_eqf : forall fk, prune_zfB (mkbc fk) = (fun mk => prune_zf mk fk).
Proof. intros. bcfe. unfold prune_zfB, prune_zf. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite prune_zfB_eqf : bceq.
Lemma prune1pB_eqf : forall fk, prune1pB (mkbc fk) = prune1p fk.
Proof. intros. bcfe. unfold prune1pB, prune1p. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite prune1pB_eqf : bceq.
Lemma ranges_apart_pcB_eqf : forall fk, ranges_apart_pcB (mkbc fk) = ranges_apart_pc fk.
Proof. intros. bcfe. unfold ranges_apart_pcB, ranges_apart_pc. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite ranges_apart_pcB_eqf : bceq.
Lemma prune1pcB_eqf : forall fk, prune1pcB (mkbc fk) = prune1pc fk.
Proof. intros. bcfe. unfold prune1pcB, prune1pc. autorewrite with bceq. reflexivity. Qed.
#[export] Hint Rewrite prune1pcB_eqf : bceq.
Lemma prunepcB_eqf : forall fk, prunepcB (mkbc fk) = prunepc fk.
Proof.
intros fk. apply functional_extensionality; intros sp. apply functional_extensionality; intros wa. apply functional_extensionality; intros w. apply functional_extensionality; intros wv. apply functional_extensionality; intros kn.
induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [prunepcB prunepc]. rewrite IH. autorewrite with bceq. reflexivity.
Qed.
#[export] Hint Rewrite prunepcB_eqf : bceq.
#[export] Hint Rewrite zf_coversB_eqf kentry_overlayB_eqf kentry_readableB_eqf kn_readableB_eqf kn_overlayB_eqf : bceq.
Lemma filter_nil_app : forall (l1 l2 : list kentry),
List.filter is_factb l1 = [] -> List.filter is_factb l2 = [] -> List.filter is_factb (l1 ++ l2) = [].
Proof. intros l1 l2 H1 H2. rewrite List.filter_app, H1, H2. reflexivity. Qed.
Lemma filter_if_single : forall (c : bool) K,
is_factb K = false -> List.filter is_factb (if c then [K] else []) = [].
Proof. intros c K H. destruct c; cbn; rewrite ?H; reflexivity. Qed.
Lemma kcut_nofacts : forall mk kn wb wk wn kb kk len,
(forall a n, is_factb (mk a n) = false) ->
List.filter is_factb (kcut mk kn wb wk wn kb kk len) = [].
Proof.
intros mk kn wb wk wn kb kk len H. unfold kcut.
apply filter_nil_app.
- apply filter_if_single. apply H.
- match goal with |- List.filter is_factb (if ?c then _ else _) = [] => destruct c; [|reflexivity] end.
destruct (split_lit (mkAlu ALU_ADD (mkAlu ALU_ADD wb (ELit wk)) wn)) as [hb ho].
cbn [List.filter]. rewrite H. reflexivity.
Qed.
Lemma ktrim_nofacts : forall mk kb kk l0 k w,
(forall a n, is_factb (mk a n) = false) ->
List.filter is_factb (ktrim mk kb kk l0 k w) = [].
Proof. intros. unfold ktrim. apply filter_nil_app; apply filter_if_single; apply H. Qed.
Lemma kword_cut_nofacts : forall kb kk w' v k w, List.filter is_factb (kword_cut kb kk w' v k w) = [].
Proof.
intros. unfold kword_cut. destruct v; try reflexivity.
apply filter_nil_app; apply filter_if_single; reflexivity.
Qed.
Lemma prune_zf_nofacts : forall mk allkn wb k w K kb kk len apart hints diffbase,
(forall a n, is_factb (mk a n) = false) -> is_factb K = false ->
List.filter is_factb (fst (fst (diffbase tt))) = [] ->
List.filter is_factb (fst (fst (prune_zf mk allkn wb k w K kb kk len apart hints diffbase))) = [].
Proof.
intros mk allkn wb k w K kb kk len apart hints diffbase Hm HK Hd. unfold prune_zf.
destruct (expr_eqb kb wb).
- destruct len; cbn [fst]; try (apply ktrim_nofacts; exact Hm);
(destruct (Z.leb (k + Z.of_nat w) kk); cbn [fst List.filter]; [rewrite HK; reflexivity | apply kcut_nofacts; exact Hm]).
- destruct (apart tt); cbn [fst List.filter]; [rewrite HK; reflexivity|].
destruct (kcut mk allkn wb k (elen w) kb kk len) as [|c cs] eqn:E; [exact Hd|].
cbn [fst]. rewrite <- E. apply kcut_nofacts. exact Hm.
Qed.
Ltac nfcrush :=
cbn [fst List.filter is_factb];
first [ reflexivity
| apply kword_cut_nofacts
| (apply filter_nil_app; apply filter_if_single; reflexivity)
| match goal with
| |- context [if ?c then _ else _] => destruct c; nfcrush
| |- context [match ?h with nil => _ | cons _ _ => _ end] => destruct h; nfcrush
| |- context [match ?h with ELit _ => _ | _ => _ end] => destruct h; nfcrush
| |- context [match ?h with Z0 => _ | _ => _ end] => destruct h; nfcrush
end ].
Lemma prune1p_facts : forall allkn sp wa w wv K hints,
List.filter is_factb (fst (fst (prune1p allkn sp wa w wv K hints))) = List.filter is_factb [K].
Proof.
intros allkn sp wa w wv K hints. unfold prune1p.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[kb kk] n|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; cbn [List.filter is_factb];
try reflexivity;
try (apply prune_zf_nofacts; [reflexivity|reflexivity|]); nfcrush.
Qed.
Lemma prune1pc_facts : forall allkn sp wa w wv K hints br2,
List.filter is_factb (fst (fst (prune1pc allkn sp wa w wv K hints br2))) = List.filter is_factb [K].
Proof.
intros allkn sp wa w wv K hints br2. unfold prune1pc.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[kb kk] n|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
try apply prune1p_facts.
- destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|]. nfcrush.
- destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|].
unfold kzero_cut. destruct (ranges_apart_pc _ _ _ _ _ _ _ _ _); [reflexivity|].
destruct (kcut KZero allkn (a_base wa) (a_off wa) (elen w) kb kk len) eqn:E; [nfcrush|].
cbn [fst]. rewrite <- E. apply kcut_nofacts. reflexivity.
- destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|]. nfcrush.
- destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|].
unfold kfill_cut. destruct (ranges_apart_pc _ _ _ _ _ _ _ _ _); [reflexivity|].
destruct (kcut (fun a n => KFill a n c) allkn (a_base wa) (a_off wa) (elen w) kb kk len) eqn:E; [nfcrush|].
cbn [fst]. rewrite <- E. apply kcut_nofacts. reflexivity.
- destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|].
unfold kunk_cut. destruct (ranges_apart_pc _ _ _ _ _ _ _ _ _); [reflexivity|].
destruct (kcut KUnk allkn (a_base wa) (a_off wa) (elen w) kb kk len) eqn:E; [nfcrush|].
cbn [fst]. rewrite <- E. apply kcut_nofacts. reflexivity.
Qed.
Lemma prunepc_facts : forall allkn sp wa w wv kn hints cache,
List.filter is_factb (fst (fst (prunepc allkn sp wa w wv kn hints cache))) = List.filter is_factb kn.
Proof.
intros allkn sp wa w wv kn. induction kn as [|K rest IH]; intros hints cache; [reflexivity|].
cbn [prunepc].
destruct (match kbase K with Some kb => match br_lookup cache kb with Some r => (r, cache) | None => (base_range allkn kb, (kb, base_range allkn kb) :: cache) end | None => (None, cache) end) as [br2 cache'].
destruct (prune1pc allkn sp wa w wv K hints br2) as [[kept scs1] hs1] eqn:E1.
destruct (prunepc allkn sp wa w wv rest hs1 cache') as [[r scs2] hs2] eqn:E2.
cbn [fst]. rewrite List.filter_app. pose proof (prune1pc_facts allkn sp wa w wv K hints br2) as H1. rewrite E1 in H1. cbn [fst] in H1.
rewrite H1. specialize (IH hs1 cache'). rewrite E2 in IH. cbn [fst] in IH. rewrite IH. cbn [List.filter]. destruct (is_factb K); reflexivity.
Qed.
Lemma carry_facts : forall log kn hints,
List.filter is_factb (fst (fst (carry log kn hints))) = List.filter is_factb kn.
Proof.
intros log kn hints. induction log as [|[a w v] older IH]; [reflexivity|].
cbn [carry]. destruct (carry older kn hints) as [[kn1 scs1] hs1]. cbn [fst] in IH.
destruct (prunepc _ _ _ _ _ kn1 hs1 []) as [[kn2 scs2] hs2] eqn:E.
cbn [fst List.filter is_factb]. pose proof (prunepc_facts (facts_of kn1) (mk_sprep (facts_of kn1) (a_base a) (a_off a) (elen w)) a w v kn1 hs1 []) as H.
rewrite E in H. cbn [fst] in H. rewrite H. exact IH.
Qed.
Fixpoint carryB (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
: list kentry * list sidecond * list bool :=
match log with
| [] => (kn, [], hints)
| SE a w v :: older =>
let '(kn1, scs1, hs1) := carryB bc older kn hints in
let '(kn2, scs2, hs2) := prunepcB bc (mk_sprepB bc (a_base a) (a_off a) (elen w)) a w v kn1 hs1 [] in
(KWord a w v :: kn2, scs1 ++ scs2, hs2)
end.
Lemma carryB_eq : forall log kn hints, carryB (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
intros log kn hints. induction log as [|[a w v] older IH]; [reflexivity|].
cbn [carryB carry]. rewrite IH.
pose proof (carry_facts older kn hints) as HF.
destruct (carry older kn hints) as [[kn1 scs1] hs1]. cbn [fst] in HF.
rewrite !facts_of_filter, <- HF, <- !facts_of_filter.
autorewrite with bceq. reflexivity.
Qed.
Lemma p_aluop_eqb_refl : forall a, aluop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma p_mulop_eqb_refl : forall a, mulop_eqb a a = true. Proof. intros []; reflexivity. Qed.
Lemma p_expr_eqb_refl : forall x, expr_eqb x x = true.
Proof.
induction x; cbn -[Z.eqb Nat.eqb]; rewrite ?p_aluop_eqb_refl, ?p_mulop_eqb_refl, ?IHx, ?IHx1, ?IHx2, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
Lemma p_prune1pc_eq : forall allkn sp wa w wv K hints br2,
match kbase K with Some kb => br2 = base_range allkn kb | None => True end ->
prune1pc allkn sp wa w wv K hints br2 = prune1p allkn sp wa w wv K hints.
Proof.
intros allkn sp wa w wv K hints br2 Hb.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
cbn [kbase] in Hb; try reflexivity; subst br2; unfold prune1pc, prune1p, prune_zf, kzero_cut, kfill_cut, kunk_cut;
destruct (expr_eqb kb (a_base wa)); reflexivity.
Qed.
Definition p_br_cache_ok (allkn : list kentry) (c : list (expr * option (Z * Z))) : Prop :=
Forall (fun p => snd p = base_range allkn (fst p)) c.
Lemma p_br_lookup_ok : forall allkn c b r, p_br_cache_ok allkn c -> br_lookup c b = Some r -> r = base_range allkn b.
Proof.
intros allkn c b r Hc. induction c as [|[b' r'] rest IH]; cbn; [discriminate|].
apply Forall_cons_iff in Hc as [H1 Hc]. cbn in H1.
destruct (expr_eqb b b') eqn:E.
- intros H. injection H as <-. apply p_expr_eqb_eq in E. subst b'. exact H1.
- apply IH. exact Hc.
Qed.
Lemma p_prunepc_eq : forall allkn sp wa w wv kn hints cache,
p_br_cache_ok allkn cache ->
prunepc allkn sp wa w wv kn hints cache = prunep allkn sp wa w wv kn hints.
Proof.
intros allkn sp wa w wv kn. induction kn as [|K rest IH]; intros hints cache Hc; [reflexivity|].
cbn [prunepc prunep].
destruct (kbase K) as [kb|] eqn:HK.
- destruct (br_lookup cache kb) as [r|] eqn:HL.
+ rewrite (p_prune1pc_eq allkn sp wa w wv K hints r) by (rewrite HK; exact (p_br_lookup_ok _ _ _ _ Hc HL)).
destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1]. rewrite (IH hs1 cache Hc). reflexivity.
+ rewrite (p_prune1pc_eq allkn sp wa w wv K hints (base_range allkn kb)) by (rewrite HK; reflexivity).
destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1].
rewrite (IH hs1 ((kb, base_range allkn kb) :: cache)) by (constructor; [reflexivity | exact Hc]). reflexivity.
- rewrite (p_prune1pc_eq allkn sp wa w wv K hints None) by (rewrite HK; exact I).
destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1]. rewrite (IH hs1 cache Hc). reflexivity.
Qed.
Definition g1 (fk : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) : list kentry :=
fst (fst (prune1p fk sp wa w wv K [])).
Ltac pk_crush :=
cbn [fst snd];
first [ reflexivity
| match goal with
| |- context [if ?c then _ else _] => destruct c; pk_crush
| |- context [match ?h with ELit _ => _ | _ => _ end] => destruct h; pk_crush
| |- context [match ?h with Z0 => _ | _ => _ end] => destruct h; pk_crush
| |- context [match ?h with nil => _ | cons _ _ => _ end] => destruct h; pk_crush
end ].
Lemma prune1p_nil : forall fk sp wa w wv K,
prune1p fk sp wa w wv K [] = (g1 fk sp wa w wv K, [], []).
Proof.
intros. unfold g1, prune1p, prune_zf.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len]; pk_crush.
Qed.
Lemma prunep_nil : forall fk sp wa w wv kn,
prunep fk sp wa w wv kn [] = (flat_map (g1 fk sp wa w wv) kn, [], []).
Proof.
intros fk sp wa w wv kn. induction kn as [|K rest IH]; [reflexivity|].
cbn [prunep flat_map]. rewrite prune1p_nil, IH. reflexivity.
Qed.
Inductive pk_res := PKeep | PRepl (l : list kentry).
Definition pk_list (K : kentry) (r : pk_res) : list kentry := match r with PKeep => [K] | PRepl l => l end.
Definition prune1pcK (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
(br2 : option (Z * Z)) : pk_res :=
let k := a_off wa in
let wb := a_base wa in
let zfK (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) :=
if same then
match len with
| ELit l0 => PRepl (ktrim mk kb kk l0 k w)
| _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mk wb k (elen w) kb kk len)
end
else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep
else match kcutB bc mk wb k (elen w) kb kk len with
| [] => if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep else PRepl []
| cut => PRepl cut
end in
match K with
| KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => PKeep
| KImg lo hi =>
match wb with
| ELit 0 =>
let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
let lo2 := Z.max lo (k + Z.of_nat w) in
let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
PRepl (r1 ++ r2)
| _ => if Z.ltb (hi - lo) (2 ^ 64) then
(if ranges_apart_pB bc sp wb k (elen w) (ELit 0) lo (ELit (hi - lo)) then PKeep else PRepl [])
else PRepl []
end
| KZero (SA kb kk) len => zfK KZero kb kk len
| KFill (SA kb kk) len c => zfK (fun a n => KFill a n c) kb kk len
| KUnk (SA kb kk) len => zfK KUnk kb kk len
| KWord (SA kb kk) w' v =>
if same then (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool then PKeep else PRepl (kword_cut kb kk w' v k w))
else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk (elen w') then PKeep
else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool then PKeep
else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk (elen w') then PKeep else PRepl []
| KBlob (SA kb kk) len bk =>
if same then
match len with
| ELit l0 => let l := (l0 mod 2 ^ 64)%Z in
if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool then PKeep else PRepl []
| _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl []
end
else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep else PRepl []
end.
Lemma prune1pcK_eq : forall fk sp wa w wv K br2 same,
(match kbase K with Some kb => same = expr_eqb kb (a_base wa) | None => True end) ->
pk_list K (prune1pcK (mkbc fk) sp wa w wv K same br2) = fst (fst (prune1pc fk sp wa w wv K [] br2)).
Proof.
intros fk sp wa w wv K br2 same H.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
cbn [kbase] in H; try subst same; unfold prune1pcK, prune1pc, prune1p, prune_zf, kzero_cut, kfill_cut, kunk_cut;
autorewrite with bceq; cbn [a_base a_off]; pk_crush.
Qed.
Definition bkey (e : expr) : option nat := first_var e.
Record binfo := BI { bi_base : expr; bi_br : option (Z * Z) }.
Record ntab := NT { nt_vars : list (list (expr * positive)); nt_other : list (expr * positive); nt_next : positive; nt_info : ptree binfo }.
Definition nt_empty : ntab := NT [] [] xH PTLeaf.
Fixpoint alookupE (l : list (expr * positive)) (b : expr) : option positive :=
match l with
| [] => None
| (b', id) :: rest => if expr_eqb b b' then Some id else alookupE rest b
end.
Definition nt_bucket (t : ntab) (k : option nat) : list (expr * positive) :=
match k with Some n => lget (nt_vars t) n | None => nt_other t end.
Definition nt_add (t : ntab) (k : option nat) (p : expr * positive) (bi : binfo) : ntab :=
match k with
| Some n => NT (lset (nt_vars t) n p) (nt_other t) (Pos.succ (nt_next t)) (pt_set (nt_next t) bi (nt_info t))
| None => NT (nt_vars t) (p :: nt_other t) (Pos.succ (nt_next t)) (pt_set (nt_next t) bi (nt_info t))
end.
Definition intern (bc : bctx) (t : ntab) (b : expr) : positive * binfo * ntab :=
let k := bkey b in
match alookupE (nt_bucket t k) b with
| Some id => (id, match pt_get (nt_info t) id with Some bi => bi | None => BI b (base_rangeB bc b) end, t)
| None => let id := nt_next t in
let bi := BI b (base_rangeB bc b) in
(id, bi, nt_add t k (b, id) bi)
end.
Definition NTI (bc : bctx) (t : ntab) : Prop :=
(forall k b id, In (b, id) (nt_bucket t k) ->
k = bkey b /\ pt_get (nt_info t) id = Some (BI b (base_rangeB bc b)) /\ (id < nt_next t)%positive)
/\ (forall k b id id', In (b, id) (nt_bucket t k) -> In (b, id') (nt_bucket t k) -> id = id').
Lemma nt_bucket_empty : forall k, nt_bucket nt_empty k = [].
Proof. intros [n|]; cbn; [unfold lget; destruct n; reflexivity | reflexivity]. Qed.
Lemma NTI_empty : forall bc, NTI bc nt_empty.
Proof. intros bc. split; intros; rewrite nt_bucket_empty in *; contradiction. Qed.
Lemma alookupE_Some : forall l b id, alookupE l b = Some id -> In (b, id) l.
Proof.
induction l as [|[b' id'] rest IH]; cbn; intros b id H; [discriminate|].
destruct (expr_eqb b b') eqn:E.
- injection H as <-. apply p_expr_eqb_eq in E. subst. left. reflexivity.
- right. apply IH. exact H.
Qed.
Lemma alookupE_None : forall l b id, alookupE l b = None -> ~ In (b, id) l.
Proof.
induction l as [|[b' id'] rest IH]; cbn; intros b id H; [tauto|].
destruct (expr_eqb b b') eqn:E; [discriminate|].
intros [X|X].
- injection X as -> ->. rewrite p_expr_eqb_refl in E. discriminate.
- exact (IH _ _ H X).
Qed.
Lemma nt_add_bucket : forall t k p bi k',
nt_bucket (nt_add t k p bi) k' = if okey_eqb k' k then p :: nt_bucket t k' else nt_bucket t k'.
Proof.
intros t [n|] p bi [m|]; cbn [nt_add nt_bucket nt_vars nt_other okey_eqb]; try reflexivity. apply lget_lset.
Qed.
Lemma nt_add_next : forall t k p bi, nt_next (nt_add t k p bi) = Pos.succ (nt_next t).
Proof. intros t [n|] p bi; reflexivity. Qed.
Lemma nt_add_info : forall t k p bi, nt_info (nt_add t k p bi) = pt_set (nt_next t) bi (nt_info t).
Proof. intros t [n|] p bi; reflexivity. Qed.
Lemma intern_ok : forall bc t b id bi t',
NTI bc t -> intern bc t b = (id, bi, t') ->
NTI bc t' /\ bi = BI b (base_rangeB bc b) /\ In (b, id) (nt_bucket t' (bkey b))
/\ (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)).
Proof.
intros bc t b id bi t' [HA HB] H. unfold intern in H.
destruct (alookupE (nt_bucket t (bkey b)) b) as [id0|] eqn:HL.
- injection H as <- <- <-. pose proof (alookupE_Some _ _ _ HL) as HIn.
destruct (HA _ _ _ HIn) as (_ & Hinfo & _). rewrite Hinfo.
split; [split; assumption|]. split; [reflexivity|]. split; [exact HIn|]. intros; assumption.
- injection H as <- <- <-.
split; [|split; [reflexivity|split]].
+ split.
* intros k b0 id0 HIn. rewrite nt_add_bucket in HIn. rewrite nt_add_info, nt_add_next.
destruct (okey_eqb_spec k (bkey b)) as [->|NE].
-- destruct HIn as [X|X].
++ injection X as <- <-. split; [reflexivity|]. rewrite pt_gss. split; [reflexivity|lia].
++ destruct (HA _ _ _ X) as (H1 & H2 & H3). split; [exact H1|].
rewrite pt_gso by lia. split; [exact H2|lia].
-- destruct (HA _ _ _ HIn) as (H1 & H2 & H3). split; [exact H1|]. rewrite pt_gso by lia. split; [exact H2|lia].
* intros k b0 id0 id0' H1 H2. rewrite nt_add_bucket in H1, H2.
destruct (okey_eqb_spec k (bkey b)) as [->|NE]; [|exact (HB _ _ _ _ H1 H2)].
destruct H1 as [X1|X1]; destruct H2 as [X2|X2].
-- congruence.
-- injection X1 as <- <-. exfalso. exact (alookupE_None _ _ _ HL X2).
-- injection X2 as <- <-. exfalso. exact (alookupE_None _ _ _ HL X1).
-- exact (HB _ _ _ _ X1 X2).
+ rewrite nt_add_bucket. destruct (okey_eqb_spec (bkey b) (bkey b)); [|congruence]. left. reflexivity.
+ intros k p HIn. rewrite nt_add_bucket. destruct (okey_eqb_spec k (bkey b)); [right|]; exact HIn.
Qed.
Lemma nt_same_eq : forall bc t b1 id1 b2 id2,
NTI bc t -> In (b1, id1) (nt_bucket t (bkey b1)) -> In (b2, id2) (nt_bucket t (bkey b2)) ->
Pos.eqb id1 id2 = expr_eqb b1 b2.
Proof.
intros bc t b1 id1 b2 id2 [HA HB] H1 H2.
destruct (HA _ _ _ H1) as (_ & I1 & _). destruct (HA _ _ _ H2) as (_ & I2 & _).
destruct (Pos.eqb_spec id1 id2) as [<-|NE].
- rewrite I1 in I2. injection I2 as <-. symmetry. apply p_expr_eqb_refl.
- destruct (expr_eqb b1 b2) eqn:E; [|reflexivity]. exfalso. apply NE.
apply p_expr_eqb_eq in E. subst b2. exact (HB _ _ _ _ H1 H2).
Qed.
Record stx := STX { sx_a : saddr; sx_w : nat; sx_v : expr; sx_sp : sprep; sx_bid : positive; sx_br : option (Z * Z) }.
Fixpoint mk_stxs (bc : bctx) (log : list sentry) (t : ntab) : list stx * ntab :=
match log with
| [] => ([], t)
| SE a w v :: older =>
let '(sxs, t1) := mk_stxs bc older t in
let '(r, t2) := intern bc t1 (a_base a) in
let '(bid, bi) := r in
(sxs ++ [STX a w v (mk_sprepB bc (a_base a) (a_off a) (elen w)) bid (bi_br bi)], t2)
end.
Definition obrB (bc : bctx) (K : kentry) : option (Z * Z) :=
match kbase K with Some kb => base_rangeB bc kb | None => None end.
Definition g1cB (bc : bctx) (sx : stx) (K : kentry) : list kentry :=
fst (fst (prune1pcB bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB bc K))).
Fixpoint chain_slow (bc : bctx) (sxs : list stx) (l : list kentry) : list kentry :=
match sxs with
| [] => l
| sx :: rest => chain_slow bc rest (flat_map (g1cB bc sx) l)
end.
Fixpoint chainK (bc : bctx) (sxs : list stx) (K : kentry) (same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
match sxs with
| [] => [K]
| sx :: rest =>
match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
| PKeep => chainK bc rest K same_of br2
| PRepl l => chain_slow bc rest l
end
end.
Fixpoint chainK2 (bc : bctx) (sxs : list stx) (K : kentry) (okb : option expr) (same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
match sxs with
| [] => [K]
| sx :: rest =>
match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
| PKeep => chainK2 bc rest K okb same_of br2
| PRepl l =>
match okb with
| Some kb =>
flat_map (fun K' => match kbase K' with
| Some kb' => if expr_eqb kb' kb then chainK2 bc rest K' okb same_of br2 else chain_slow bc rest [K']
| None => chain_slow bc rest [K']
end) l
| None => chain_slow bc rest l
end
end
end.
Fixpoint entriesV (bc : bctx) (sxs : list stx) (kn : list kentry) (t : ntab) : list kentry :=
match kn with
| [] => []
| K :: rest =>
match kbase K with
| Some kb => let '(r, t') := intern bc t kb in
let '(bid, bi) := r in
chainK2 bc sxs K (Some kb) (Pos.eqb bid) (bi_br bi) ++ entriesV bc sxs rest t'
| None => chainK2 bc sxs K None (fun _ => false) None ++ entriesV bc sxs rest t
end
end.
Fixpoint stores_part (bc : bctx) (sxs : list stx) : list kentry :=
match sxs with
| [] => []
| sx :: newer => stores_part bc newer ++ chainK2 bc newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx)
end.
Definition carryV (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
let '(sxs, t) := mk_stxs bc log nt_empty in
stores_part bc sxs ++ entriesV bc sxs kn t.
Definition carryK0 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
: list kentry * list sidecond * list bool :=
match log, hints with
| [], _ => (kn, [], hints)
| _, [] => (carryV bc log kn, [], [])
| _, _ => carryB bc log kn hints
end.
Definition FM (fk : list kentry) (s : sentry) (l : list kentry) : list kentry :=
match s with SE a w v => flat_map (g1 fk (mk_sprep fk (a_base a) (a_off a) (elen w)) a w v) l end.
Fixpoint chainRo (fk : list kentry) (sxo : list sentry) (l : list kentry) : list kentry :=
match sxo with [] => l | s :: newer => chainRo fk newer (FM fk s l) end.
Definition kw (s : sentry) : kentry := match s with SE a w v => KWord a w v end.
Fixpoint SPRo (fk : list kentry) (sxo : list sentry) : list kentry :=
match sxo with [] => [] | s :: newer => SPRo fk newer ++ chainRo fk newer [kw s] end.
Lemma flat_map_app' : forall (A B : Type) (f : A -> list B) l1 l2, flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof. intros. rewrite !flat_map_concat_map, map_app, concat_app. reflexivity. Qed.
Lemma FM_app : forall fk s l1 l2, FM fk s (l1 ++ l2) = FM fk s l1 ++ FM fk s l2.
Proof. intros fk [a w v] l1 l2. unfold FM. apply flat_map_app'. Qed.
Lemma chainRo_snoc : forall fk sxo s l, chainRo fk (sxo ++ [s]) l = FM fk s (chainRo fk sxo l).
Proof. intros fk sxo. induction sxo as [|x rest IH]; intros; [reflexivity|]. cbn [chainRo app]. apply IH. Qed.
Lemma chainRo_app : forall fk sxo l1 l2, chainRo fk sxo (l1 ++ l2) = chainRo fk sxo l1 ++ chainRo fk sxo l2.
Proof. intros fk sxo. induction sxo as [|x rest IH]; intros; [reflexivity|]. cbn [chainRo]. rewrite FM_app. apply IH. Qed.
Lemma SPRo_snoc : forall fk sxo s, SPRo fk (sxo ++ [s]) = kw s :: FM fk s (SPRo fk sxo).
Proof.
intros fk sxo s. induction sxo as [|x rest IH]; [destruct s; reflexivity|].
cbn [SPRo app]. rewrite IH, chainRo_snoc, FM_app. reflexivity.
Qed.
Lemma carry_vertical : forall log kn,
carry log kn [] = (SPRo (facts_of kn) (rev log) ++ chainRo (facts_of kn) (rev log) kn, [], []).
Proof.
intros log kn. induction log as [|[a w v] older IH]; [reflexivity|].
cbn [carry rev]. pose proof (carry_facts older kn []) as HF. rewrite IH in HF |- *. cbn [fst] in HF.
cbv beta iota zeta. rewrite !facts_of_filter in *. rewrite HF.
rewrite p_prunepc_eq by constructor. rewrite prunep_nil.
match goal with |- context [flat_map ?g ?l] => change (flat_map g l) with (FM (List.filter is_factb kn) (SE a w v) l) end.
rewrite FM_app, SPRo_snoc, chainRo_snoc. reflexivity.
Qed.
Definition strip (sx : stx) : sentry := SE (sx_a sx) (sx_w sx) (sx_v sx).
Definition SX_OK (bc : bctx) (t : ntab) (sx : stx) : Prop :=
In (a_base (sx_a sx), sx_bid sx) (nt_bucket t (bkey (a_base (sx_a sx))))
/\ sx_br sx = base_rangeB bc (a_base (sx_a sx))
/\ sx_sp sx = mk_sprepB bc (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)).
Lemma g1cB_eq : forall fk sx,
sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)) ->
flat_map (g1cB (mkbc fk) sx) = FM fk (strip sx).
Proof.
intros fk sx Hsp. apply functional_extensionality; intros l. unfold FM, strip. f_equal.
apply functional_extensionality; intros K. unfold g1cB, obrB. rewrite Hsp. autorewrite with bceq.
rewrite p_prune1pc_eq by (destruct (kbase K); reflexivity). rewrite prune1p_nil. reflexivity.
Qed.
Lemma chain_slow_eq : forall fk sxs l,
Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs ->
chain_slow (mkbc fk) sxs l = chainRo fk (map strip sxs) l.
Proof.
intros fk sxs. induction sxs as [|sx rest IH]; intros l HF; [reflexivity|].
apply Forall_cons_iff in HF as [H1 HF]. cbn [chain_slow chainRo map]. rewrite (g1cB_eq _ _ H1). apply IH. exact HF.
Qed.
Lemma chainK_eq : forall fk sxs K same_of br2,
Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs ->
match kbase K with
| Some kb => br2 = base_rangeB (mkbc fk) kb /\ Forall (fun sx => same_of (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs
| None => br2 = None
end ->
chainK (mkbc fk) sxs K same_of br2 = chain_slow (mkbc fk) sxs [K].
Proof.
intros fk sxs. induction sxs as [|sx rest IH]; intros K same_of br2 HS HK; [reflexivity|].
apply Forall_cons_iff in HS as [H1 HS]. cbn [chainK chain_slow flat_map]. rewrite app_nil_r.
unfold g1cB at 1.
assert (E : pk_list K (prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2)
= fst (fst (prune1pcB (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB (mkbc fk) K)))).
{ autorewrite with bceq. destruct (kbase K) as [kb|] eqn:HB.
- destruct HK as [-> HK]. apply Forall_cons_iff in HK as [HK1 HK].
unfold obrB. rewrite HB. apply prune1pcK_eq. rewrite HB. exact HK1.
- unfold obrB. rewrite HB. subst br2. apply prune1pcK_eq. rewrite HB. exact I. }
destruct (prune1pcK _ _ _ _ _ K _ br2) as [|l]; cbn [pk_list] in E.
- rewrite <- E. apply IH; [exact HS|]. destruct (kbase K) as [kb|]; [|exact HK].
destruct HK as [Hbr HK]. apply Forall_cons_iff in HK as [_ HK]. exact (conj Hbr HK).
- rewrite <- E. reflexivity.
Qed.
Lemma flat_map_flat_map : forall (A B C : Type) (f : A -> list B) (g : B -> list C) l,
flat_map g (flat_map f l) = flat_map (fun x => flat_map g (f x)) l.
Proof. intros. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite flat_map_app', IH. reflexivity. Qed.
Lemma chain_slow_flat_map : forall bc sxs l, chain_slow bc sxs l = flat_map (fun K => chain_slow bc sxs [K]) l.
Proof.
intros bc sxs. induction sxs as [|sx rest IH]; intros l.
- cbn. induction l as [|x r IHl]; [reflexivity|]. cbn. rewrite <- IHl. reflexivity.
- cbn [chain_slow]. rewrite IH. rewrite flat_map_flat_map.
f_equal. apply functional_extensionality. intros K. cbn [flat_map]. rewrite app_nil_r. rewrite <- IH. reflexivity.
Qed.
Lemma chainK2_eq : forall fk sxs K okb same_of br2,
Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs ->
okb = kbase K ->
match okb with
| Some kb => br2 = base_rangeB (mkbc fk) kb /\ Forall (fun sx => same_of (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs
| None => br2 = None
end ->
chainK2 (mkbc fk) sxs K okb same_of br2 = chain_slow (mkbc fk) sxs [K].
Proof.
intros fk sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 HS Hokb HK; [reflexivity|].
apply Forall_cons_iff in HS as [H1 HS]. cbn [chainK2 chain_slow flat_map]. rewrite app_nil_r.
unfold g1cB at 1.
assert (E : pk_list K (prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2)
= fst (fst (prune1pcB (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB (mkbc fk) K)))).
{ autorewrite with bceq. unfold obrB. rewrite <- Hokb. destruct okb as [kb|].
- destruct HK as [-> HK]. apply Forall_cons_iff in HK as [HK1 HK]. apply prune1pcK_eq. rewrite <- Hokb. exact HK1.
- subst br2. apply prune1pcK_eq. rewrite <- Hokb. exact I. }
destruct (prune1pcK _ _ _ _ _ K _ br2) as [|l]; cbn [pk_list] in E; rewrite <- E.
- apply IH; [exact HS|exact Hokb|]. destruct okb as [kb|]; [|exact HK].
destruct HK as [Hbr HK]. apply Forall_cons_iff in HK as [_ HK]. exact (conj Hbr HK).
- destruct okb as [kb|]; [|reflexivity]. rewrite (chain_slow_flat_map _ rest l).
f_equal. apply functional_extensionality. intros K'.
destruct (kbase K') as [kb'|] eqn:HB'; [|reflexivity].
destruct (expr_eqb kb' kb) eqn:EQ; [|reflexivity].
apply p_expr_eqb_eq in EQ. subst kb'.
apply IH; [exact HS|symmetry; exact HB'|].
destruct HK as [Hbr HK]. apply Forall_cons_iff in HK as [_ HK]. exact (conj Hbr HK).
Qed.
Lemma SX_OK_mono : forall bc t t' sx,
(forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)) -> SX_OK bc t sx -> SX_OK bc t' sx.
Proof. intros bc t t' sx Hm (H1 & H2 & H3). split; [apply Hm; exact H1|]. split; assumption. Qed.
Lemma mk_stxs_ok : forall fk log t sxs t',
NTI (mkbc fk) t -> mk_stxs (mkbc fk) log t = (sxs, t') ->
NTI (mkbc fk) t' /\ Forall (SX_OK (mkbc fk) t') sxs /\ map strip sxs = rev log
/\ (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)).
Proof.
intros fk log. induction log as [|[a w v] older IH]; intros t sxs t' HT H.
- cbn in H. injection H as <- <-. split; [exact HT|]. split; [constructor|]. split; [reflexivity|]. intros; assumption.
- cbn [mk_stxs] in H. destruct (mk_stxs (mkbc fk) older t) as [sxs0 t1] eqn:E0.
destruct (intern (mkbc fk) t1 (a_base a)) as [[bid bi] t2] eqn:EI.
injection H as <- <-.
destruct (IH t sxs0 t1 HT E0) as (HT1 & HS & Hmap & Hm1).
destruct (intern_ok _ _ _ _ _ _ HT1 EI) as (HT2 & -> & HIn & Hm2).
split; [exact HT2|]. split.
+ apply Forall_app. split.
* apply Forall_impl with (P := SX_OK (mkbc fk) t1); [|exact HS]. intros sx. apply SX_OK_mono. exact Hm2.
* constructor; [|constructor]. split; [exact HIn|]. split; reflexivity.
+ split; [rewrite map_app, Hmap; reflexivity|]. intros k p Hp. apply Hm2. apply Hm1. exact Hp.
Qed.
Lemma Forall_SX_sp : forall fk t sxs, Forall (SX_OK (mkbc fk) t) sxs ->
Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs.
Proof. intros fk t sxs H. apply Forall_impl with (P := SX_OK (mkbc fk) t); [|exact H]. intros sx (_ & _ & X). exact X. Qed.
Lemma Forall_SX_same : forall fk t sxs kb bid,
NTI (mkbc fk) t -> In (kb, bid) (nt_bucket t (bkey kb)) -> Forall (SX_OK (mkbc fk) t) sxs ->
Forall (fun sx => Pos.eqb bid (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs.
Proof.
intros fk t sxs kb bid HT HIn H. apply Forall_impl with (P := SX_OK (mkbc fk) t); [|exact H].
intros sx (H1 & _ & _). exact (nt_same_eq _ _ _ _ _ _ HT HIn H1).
Qed.
Lemma entriesV_eq : forall fk sxs kn t,
NTI (mkbc fk) t -> Forall (SX_OK (mkbc fk) t) sxs ->
entriesV (mkbc fk) sxs kn t = chainRo fk (map strip sxs) kn.
Proof.
intros fk sxs kn. induction kn as [|K rest IH]; intros t HT HS.
- cbn. clear. induction sxs as [|sx r IH]; [reflexivity|]. cbn. destruct (strip sx). exact IH.
- cbn [entriesV]. change (K :: rest) with ([K] ++ rest). rewrite chainRo_app.
destruct (kbase K) as [kb|] eqn:HB.
+ destruct (intern (mkbc fk) t kb) as [[bid bi] t'] eqn:EI.
destruct (intern_ok _ _ _ _ _ _ HT EI) as (HT' & -> & HIn & Hm).
assert (HS' : Forall (SX_OK (mkbc fk) t') sxs).
{ apply Forall_impl with (P := SX_OK (mkbc fk) t); [|exact HS]. intros sx. apply SX_OK_mono. exact Hm. }
rewrite (IH t' HT' HS'). f_equal.
rewrite chainK2_eq; [apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | symmetry; exact HB |].
cbn [bi_br]. split; [reflexivity|]. exact (Forall_SX_same _ _ _ _ _ HT' HIn HS').
+ rewrite (IH t HT HS). f_equal.
rewrite chainK2_eq; [apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | symmetry; exact HB |].
reflexivity.
Qed.
Lemma stores_part_eq : forall fk t sxs,
NTI (mkbc fk) t -> Forall (SX_OK (mkbc fk) t) sxs ->
stores_part (mkbc fk) sxs = SPRo fk (map strip sxs).
Proof.
intros fk t sxs HT. induction sxs as [|sx newer IH]; intros HS; [reflexivity|].
apply Forall_cons_iff in HS as [H1 HS]. cbn [stores_part SPRo map]. rewrite (IH HS). f_equal.
destruct H1 as (HIn & Hbr & _). destruct (sx_a sx) as [b o] eqn:Ea. cbn [a_base a_off] in HIn, Hbr.
rewrite chainK2_eq; [unfold kw, strip; rewrite Ea; apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | reflexivity |].
cbn [a_base]. split; [exact Hbr|]. exact (Forall_SX_same _ _ _ _ _ HT HIn HS).
Qed.
Lemma carryK0_eq : forall log kn hints,
carryK0 (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
intros log kn hints. unfold carryK0. destruct log as [|s older]; [reflexivity|].
destruct hints as [|h hs]; [|apply carryB_eq].
rewrite carry_vertical. unfold carryV.
destruct (mk_stxs (mkbc (facts_of kn)) (s :: older) nt_empty) as [sxs t] eqn:E.
destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT & HS & Hmap & _).
rewrite (stores_part_eq _ _ _ HT HS), (entriesV_eq _ _ _ _ HT HS), Hmap. reflexivity.
Qed.
Fixpoint pt_map {A B : Type} (f : A -> B) (t : ptree A) : ptree B :=
match t with
| PTLeaf => PTLeaf
| PTNode l o r => PTNode (pt_map f l) (match o with Some a => Some (f a) | None => None end) (pt_map f r)
end.
Lemma pt_get_map : forall (A B : Type) (f : A -> B) t k,
pt_get (pt_map f t) k = match pt_get t k with Some a => Some (f a) | None => None end.
Proof. intros A B f t. induction t as [|l IHl o r IHr]; intros k; [destruct k; reflexivity|]. destruct k; cbn; auto. Qed.
Definition kdescr (K : kentry) : option (expr * Z * option Z) :=
match K with
| KWord (SA kb kk) w _ => Some (kb, kk, Some (zlit64 (Z.of_nat w)))
| KZero (SA kb kk) len | KUnk (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
Some (kb, kk, match len with ELit z => Some (zlit64 z) | _ => None end)
| KImg lo hi => Some (ELit 0%Z, lo, if Z.ltb (hi - lo) (2 ^ 64) then Some (zlit64 (hi - lo)) else None)
| _ => None
end.
Record einfo := EI { ei_bid : positive; ei_gid : positive; ei_kb : expr; ei_br : option (Z * Z); ei_k : Z; ei_m : option Z }.
Definition gval : Type := (positive * option (Z * Z) * (Z * Z))%type.
Definition gtab := ptree gval.
Record gst := GST { gs_gid : ptree (ptree positive); gs_next : positive; gs_bnds : gtab }.
Definition gst_empty : gst := GST PTLeaf xH PTLeaf.
Definition gkey (kk : Z) : positive :=
let g := Z.shiftr kk 16 in Z.to_pos (if Z.leb 0 g then 2 * g + 1 else - (2 * g))%Z.
Definition ggroup (gs : gst) (bid : positive) (kk : Z) : positive * gst :=
let gk := gkey kk in
let inner := match pt_get (gs_gid gs) bid with Some i => i | None => PTLeaf end in
match pt_get inner gk with
| Some gid => (gid, gs)
| None => let gid := gs_next gs in
(gid, GST (pt_set bid (pt_set gk gid inner) (gs_gid gs)) (Pos.succ gid) (gs_bnds gs))
end.
Definition bnd_add (gs : gst) (gid bid : positive) (obr : option (Z * Z)) (lo hi : Z) : gst :=
GST (gs_gid gs) (gs_next gs)
(match pt_get (gs_bnds gs) gid with
| Some (b, o, (l, h)) => pt_set gid (b, o, (Z.min l lo, Z.max h hi)) (gs_bnds gs)
| None => pt_set gid (bid, obr, (lo, hi)) (gs_bnds gs)
end).
Fixpoint scan_entries (bc : bctx) (kn : list kentry) (t : ntab) (gs : gst) : list (option einfo) * ntab * gst :=
match kn with
| [] => ([], t, gs)
| K :: rest =>
match kdescr K with
| Some (kb, kk, om) =>
let '(r, t1) := intern bc t kb in
let '(bid, bi) := r in
let '(gid, gs1) := match om with
| Some m => let '(gid, gs0) := ggroup gs bid kk in (gid, bnd_add gs0 gid bid (bi_br bi) kk (kk + m)%Z)
| None => (xH, gs)
end in
let '(infos, t2, gs2) := scan_entries bc rest t1 gs1 in
(Some (EI bid gid kb (bi_br bi) kk om) :: infos, t2, gs2)
| None =>
let '(infos, t2, gs2) := scan_entries bc rest t gs in
(None :: infos, t2, gs2)
end
end.
Definition sx_m1 (sx : stx) : Z := zlit64 (Z.of_nat (sx_w sx)).
Definition verdict (sx : stx) (g : gval) : bool :=
match g with
| (b, obr, (glo, ghi)) =>
if Pos.eqb b (sx_bid sx) then false else
match sp_rng (sx_sp sx), obr with
| Some (lo1, hi1), Some (lo2, hi2) =>
(Z.leb (hi1 + a_off (sx_a sx) + sx_m1 sx - lo2) glo || Z.leb ghi (lo1 + a_off (sx_a sx) - hi2))%bool
| _, _ => false
end
end.
Fixpoint mk_fl (g : gval) (sxs : list stx) : list (stx * list stx) :=
match sxs with
| [] => []
| sx :: rest => if verdict sx g then mk_fl g rest else (sx, rest) :: mk_fl g rest
end.
Definition gfl : Type := (gval * list (stx * list stx))%type.
Definition mk_gl (bnds : gtab) (sxs : list stx) : ptree gfl := pt_map (fun g => (g, mk_fl g sxs)) bnds.
Definition obr_eqb (a b : option (Z * Z)) : bool :=
match a, b with
| Some (x1, y1), Some (x2, y2) => Z.eqb x1 x2 && Z.eqb y1 y2
| None, None => true
| _, _ => false
end%bool.
Definition inb (g : gval) (ei : einfo) : bool :=
match ei_m ei, g with
| Some m, (b, obr, (lo, hi)) =>
Pos.eqb b (ei_bid ei) && obr_eqb obr (ei_br ei) && Z.leb lo (ei_k ei) && Z.leb (ei_k ei + m) hi
| _, _ => false
end%bool.
Fixpoint chainKF (bc : bctx) (fl : list (stx * list stx)) (K : kentry) (okb : option expr) (same_of : positive -> bool)
(br2 : option (Z * Z)) : list kentry :=
match fl with
| [] => [K]
| (sx, rest) :: fl' =>
match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
| PKeep => chainKF bc fl' K okb same_of br2
| PRepl l =>
match okb with
| Some kb =>
flat_map (fun K' => match kbase K' with
| Some kb' => if expr_eqb kb' kb then chainK2 bc rest K' okb same_of br2 else chain_slow bc rest [K']
| None => chain_slow bc rest [K']
end) l
| None => chain_slow bc rest l
end
end
end.
Fixpoint entriesG (bc : bctx) (sxs : list stx) (gl : ptree gfl) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
match kn, infos with
| K :: rest, oi :: irest =>
(match oi with
| Some ei =>
let okb := kbase K in
let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
let br2 := match okb with Some _ => ei_br ei | None => None end in
match pt_get gl (ei_gid ei) with
| Some (g, fl) => if inb g ei then chainKF bc fl K okb same_of br2 else chainK2 bc sxs K okb same_of br2
| None => chainK2 bc sxs K okb same_of br2
end
| None => chainK2 bc sxs K None (fun _ => false) None
end) ++ entriesG bc sxs gl rest irest
| _, _ => []
end.
Definition carryG (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
let '(sxs, t0) := mk_stxs bc log nt_empty in
let '(r, gs) := scan_entries bc kn t0 gst_empty in
let '(infos, _) := r in
stores_part bc sxs ++ entriesG bc sxs (mk_gl (gs_bnds gs) sxs) kn infos.
Lemma zlit64_idem : forall z, zlit64 (zlit64 z) = zlit64 z.
Proof.
intros z. unfold zlit64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:E; [rewrite E; reflexivity|].
pose proof (Z.mod_pos_bound z two64 ltac:(unfold two64; lia)) as B.
replace (Z.leb 0 (z mod two64) && Z.ltb (z mod two64) two64)%bool with true; [reflexivity|].
symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.
Lemma kdescr_kbase : forall K kb kk om,
kdescr K = Some (kb, kk, om) -> kbase K = Some kb \/ (exists lo hi, K = KImg lo hi /\ kb = ELit 0%Z /\ kk = lo).
Proof.
intros K kb kk om H.
destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
cbn [kdescr kbase] in *; try discriminate; try (injection H as <- <- Hm); try (left; reflexivity).
right. exists lo, hi. repeat split; congruence.
Qed.
Lemma kdescr_None_kbase : forall K, kdescr K = None -> kbase K = None.
Proof.
intros K H. destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
cbn [kdescr kbase] in *; try discriminate; reflexivity.
Qed.
Lemma prune1pcK_keep_based : forall bc sp wa w wv K kb kk m lo1 hi1 lo2 hi2,
kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) ->
sp_rng sp = Some (lo1, hi1) -> base_rangeB bc kb = Some (lo2, hi2) ->
(hi1 + a_off wa + zlit64 (Z.of_nat w) <= lo2 + kk \/ hi2 + kk + m <= lo1 + a_off wa)%Z ->
prune1pcK bc sp wa w wv K false (base_rangeB bc kb) = PKeep.
Proof.
intros bc sp wa w wv K kb kk m lo1 hi1 lo2 hi2 HB HD Hsp Hbr Hnum.
destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
cbn [kbase kdescr] in HB, HD; try discriminate; injection HB as ->;
try (injection HD as <- <-); try (destruct len as [z| | | | | | |]; try discriminate; injection HD as <- <-);
unfold prune1pcK; cbn [a_base a_off]; unfold ranges_apart_pcB; cbn [elen]; rewrite Hsp, Hbr;
match goal with |- context [if ((?a <=? ?b) || (?c <=? ?d))%Z then _ else _] =>
replace ((a <=? b) || (c <=? d))%Z%bool with true; [reflexivity|];
symmetry; apply Bool.orb_true_iff; destruct Hnum as [H|H]; [left|right]; apply Z.leb_le; rewrite ?zlit64_idem; lia end.
Qed.
Lemma prune1pcK_keep_img : forall bc sp wa w wv lo hi m lo1 hi1 lo2 hi2 same br2,
kdescr (KImg lo hi) = Some (ELit 0%Z, lo, Some m) ->
expr_eqb (ELit 0%Z) (a_base wa) = false ->
sp_rng sp = Some (lo1, hi1) -> base_rangeB bc (ELit 0%Z) = Some (lo2, hi2) ->
(hi1 + a_off wa + zlit64 (Z.of_nat w) <= lo2 + lo \/ hi2 + lo + m <= lo1 + a_off wa)%Z ->
prune1pcK bc sp wa w wv (KImg lo hi) same br2 = PKeep.
Proof.
intros bc sp wa w wv lo hi m lo1 hi1 lo2 hi2 same br2 HD Hne Hsp Hbr Hnum.
cbn [kdescr] in HD. destruct (Z.ltb (hi - lo) (2 ^ 64)) eqn:Hlt; [|discriminate]. injection HD as <-.
unfold prune1pcK. destruct wa as [wb k]. cbn [a_base a_off] in *.
assert (STEP : (if ranges_apart_pB bc sp wb k (elen w) (ELit 0%Z) lo (ELit (hi - lo)) then PKeep else PRepl []) = PKeep).
{ unfold ranges_apart_pB. cbn [elen]. rewrite Hsp, Hbr.
match goal with |- context [if ((?a <=? ?b) || (?c <=? ?d))%Z then _ else _] =>
replace ((a <=? b) || (c <=? d))%Z%bool with true; [reflexivity|];
symmetry; apply Bool.orb_true_iff; destruct Hnum as [H|H]; [left|right]; apply Z.leb_le; rewrite ?zlit64_idem; lia end. }
rewrite Hlt. destruct wb as [z| | | | | | |]; try exact STEP.
destruct z; try exact STEP. cbn in Hne. discriminate.
Qed.
Definition EINF (bc : bctx) (t : ntab) (K : kentry) (oi : option einfo) : Prop :=
match oi with
| None => kdescr K = None
| Some ei => kdescr K = Some (ei_kb ei, ei_k ei, ei_m ei)
/\ In (ei_kb ei, ei_bid ei) (nt_bucket t (bkey (ei_kb ei)))
/\ ei_br ei = base_rangeB bc (ei_kb ei)
end.
Lemma EINF_mono : forall bc t t' K oi,
(forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)) -> EINF bc t K oi -> EINF bc t' K oi.
Proof. intros bc t t' K [ei|] Hm H; cbn [EINF] in *; [|exact H]. destruct H as (A & B & C). split; [exact A|]. split; [apply Hm; exact B| exact C]. Qed.
Lemma scan_entries_ok : forall fk kn t gs infos t' gs',
NTI (mkbc fk) t -> scan_entries (mkbc fk) kn t gs = (infos, t', gs') ->
NTI (mkbc fk) t'
/\ (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k))
/\ Forall2 (EINF (mkbc fk) t') kn infos.
Proof.
intros fk kn. induction kn as [|K rest IH]; intros t gs infos t' gs' HT H.
- cbn in H. injection H as <- <- <-. split; [exact HT|]. split; [intros; assumption|]. constructor.
- cbn [scan_entries] in H.
destruct (kdescr K) as [[[kb kk] om]|] eqn:HD.
+ destruct (intern (mkbc fk) t kb) as [[bid bi] t1] eqn:EI.
destruct (intern_ok _ _ _ _ _ _ HT EI) as (HT1 & Hbi & HIn & Hm1).
lazymatch type of H with (let '(_, _) := ?X in _) = _ => destruct X as [gid gs1] end.
destruct (scan_entries (mkbc fk) rest t1 _) as [[infos2 t2] gs2] eqn:ES.
injection H as <- <- <-.
destruct (IH _ _ _ _ _ HT1 ES) as (HT2 & Hm2 & HF).
split; [exact HT2|]. split; [intros k p Hp; apply Hm2; apply Hm1; exact Hp|].
constructor; [|exact HF]. cbn [EINF ei_kb ei_k ei_m ei_bid ei_br].
split; [exact HD|]. split; [apply Hm2; exact HIn|]. rewrite Hbi. reflexivity.
+ destruct (scan_entries (mkbc fk) rest t gs) as [[infos2 t2] gs2] eqn:ES.
injection H as <- <- <-.
destruct (IH _ _ _ _ _ HT ES) as (HT2 & Hm2 & HF).
split; [exact HT2|]. split; [exact Hm2|]. constructor; [exact HD | exact HF].
Qed.
Lemma chainKF_eq : forall bc g sxs K okb same_of br2,
(forall sx, In sx sxs -> verdict sx g = true ->
prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 = PKeep) ->
chainKF bc (mk_fl g sxs) K okb same_of br2 = chainK2 bc sxs K okb same_of br2.
Proof.
intros bc g sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 Hf; [reflexivity|].
cbn [mk_fl chainK2].
assert (IH' : chainKF bc (mk_fl g rest) K okb same_of br2 = chainK2 bc rest K okb same_of br2)
by (apply IH; intros; apply Hf; [right|]; assumption).
destruct (verdict sx g) eqn:Hv.
- rewrite (Hf sx (or_introl eq_refl) Hv). exact IH'.
- cbn [chainKF]. destruct (prune1pcK _ _ _ _ _ K _ br2); [exact IH'|reflexivity].
Qed.
Lemma verdict_inb_num : forall sx g ei m,
verdict sx g = true -> inb g ei = true -> ei_m ei = Some m ->
Pos.eqb (ei_bid ei) (sx_bid sx) = false
/\ exists lo1 hi1 lo2 hi2, sp_rng (sx_sp sx) = Some (lo1, hi1) /\ ei_br ei = Some (lo2, hi2)
/\ (hi1 + a_off (sx_a sx) + zlit64 (Z.of_nat (sx_w sx)) <= lo2 + ei_k ei \/ hi2 + ei_k ei + m <= lo1 + a_off (sx_a sx))%Z.
Proof.
intros sx [[b obr] [glo ghi]] ei m Hv Hi Hm. unfold verdict in Hv. unfold inb in Hi. rewrite Hm in Hi.
apply andb_prop in Hi as [Hi H4]. apply andb_prop in Hi as [Hi H3]. apply andb_prop in Hi as [H1 H2].
apply Pos.eqb_eq in H1. subst b. apply Z.leb_le in H3. apply Z.leb_le in H4.
destruct (Pos.eqb (ei_bid ei) (sx_bid sx)); [discriminate|]. split; [reflexivity|].
destruct (sp_rng (sx_sp sx)) as [[lo1 hi1]|]; [|discriminate].
destruct obr as [[lo2 hi2]|]; [|discriminate].
destruct (ei_br ei) as [[x2 y2]|]; [|discriminate]. cbn [obr_eqb] in H2. apply andb_prop in H2 as [X Y].
apply Z.eqb_eq in X. apply Z.eqb_eq in Y. subst x2 y2.
exists lo1, hi1, lo2, hi2. split; [reflexivity|]. split; [reflexivity|].
unfold sx_m1 in Hv. apply Bool.orb_prop in Hv. destruct Hv as [H|H]; apply Z.leb_le in H; lia.
Qed.
Lemma entriesG_eq : forall fk sxs bnds kn infos t1,
NTI (mkbc fk) t1 -> Forall (SX_OK (mkbc fk) t1) sxs -> Forall2 (EINF (mkbc fk) t1) kn infos ->
entriesG (mkbc fk) sxs (mk_gl bnds sxs) kn infos = chainRo fk (map strip sxs) kn.
Proof.
intros fk sxs bnds kn infos t1 HT HS HF. induction HF as [|K oi rest irest HK HF IH].
- cbn. clear. induction sxs as [|sx r IH]; [reflexivity|]. cbn. destruct (strip sx). exact IH.
- cbn [entriesG]. change (K :: rest) with ([K] ++ rest). rewrite chainRo_app, IH. f_equal.
rewrite <- (chain_slow_eq fk sxs [K] (Forall_SX_sp _ _ _ HS)).
pose proof (Forall_SX_sp _ _ _ HS) as HSP.
destruct oi as [ei|]; cbn [EINF] in HK.
+ destruct HK as (HD & HIn & Hbr).
assert (FULL : forall okb, okb = kbase K ->
chainK2 (mkbc fk) sxs K okb
(match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end)
(match okb with Some _ => ei_br ei | None => None end) = chain_slow (mkbc fk) sxs [K]).
{ intros okb Hokb. apply chainK2_eq; [exact HSP|exact Hokb|].
destruct okb as [kb|]; [|reflexivity].
destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & _ & _)]; [|cbn in Hokb; discriminate].
rewrite <- Hokb in HB. injection HB as ->.
split; [exact Hbr|]. exact (Forall_SX_same _ _ _ _ _ HT HIn HS). }
unfold mk_gl. rewrite pt_get_map.
destruct (pt_get bnds (ei_gid ei)) as [g|]; [|apply FULL; reflexivity].
destruct (inb g ei) eqn:Hinb; [|apply FULL; reflexivity].
rewrite <- (FULL (kbase K) eq_refl). apply chainKF_eq.
intros sx Hsx Hv.
assert (Hm : exists m, ei_m ei = Some m).
{ unfold inb in Hinb. destruct (ei_m ei) as [m|]; [exists m; reflexivity|discriminate]. }
destruct Hm as [m Hm].
destruct (verdict_inb_num _ _ _ _ Hv Hinb Hm) as (Hne & lo1 & hi1 & lo2 & hi2 & Hsp & Hbr2 & Hnum).
pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & SXbr & SXsp).
rewrite Hm in HD.
destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
* rewrite HB. rewrite Hne. rewrite Hbr. eapply prune1pcK_keep_based; [exact HB|exact HD|exact Hsp| | exact Hnum].
rewrite <- Hbr. exact Hbr2.
* cbn [kbase]. rewrite Hkb, Hk in *.
eapply prune1pcK_keep_img; [exact HD| |exact Hsp| rewrite <- Hbr; exact Hbr2 | exact Hnum].
rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne.
+ apply chainK2_eq; [exact HSP| symmetry; apply kdescr_None_kbase; exact HK | reflexivity].
Qed.
Lemma carryG_eq : forall log kn,
carryG (mkbc (facts_of kn)) log kn = SPRo (facts_of kn) (rev log) ++ chainRo (facts_of kn) (rev log) kn.
Proof.
intros log kn. unfold carryG.
destruct (mk_stxs (mkbc (facts_of kn)) log nt_empty) as [sxs t0] eqn:E.
destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & Hmap & _).
destruct (scan_entries (mkbc (facts_of kn)) kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
destruct (scan_entries_ok _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hm & HF).
assert (HS1 : Forall (SX_OK (mkbc (facts_of kn)) t1) sxs).
{ apply Forall_impl with (P := SX_OK (mkbc (facts_of kn)) t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hm. }
rewrite (stores_part_eq _ _ _ HT0 HS0), (entriesG_eq _ _ _ _ _ _ HT1 HS1 HF), Hmap. reflexivity.
Qed.
Definition carryK (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
: list kentry * list sidecond * list bool :=
match log, hints with
| [], _ => (kn, [], hints)
| _, [] => (carryG bc log kn, [], [])
| _, _ => carryB bc log kn hints
end.
Lemma carryK_eq : forall log kn hints,
carryK (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
intros log kn hints. unfold carryK. destruct log as [|s older]; [reflexivity|].
destruct hints as [|h hs]; [|apply carryB_eq].
rewrite carry_vertical, carryG_eq. reflexivity.
Qed.
End AX2B.
