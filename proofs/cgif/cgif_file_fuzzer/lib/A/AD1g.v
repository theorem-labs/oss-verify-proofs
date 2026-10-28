(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB12 AB1h AB13 AB01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG01 YG0f YG0v YG0n YG0r.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AF0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05 YD1h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Definition epg (v : nat) : expr := EMd M_MUL (ELit 4096) (EVar v).
Definition eP : expr := epg 255.
Definition eSp1 : expr := EAlu ALU_ADD eP (EMd M_MUL (ELit (-4096)) (EVar 256)).
Definition eSp : expr := EAlu ALU_ADD eSp1 (ELit 65536).
Definition eQ : expr := epg 273.    Definition eT : expr := epg 274.    Definition eC : expr := epg 275.
Definition eF : expr := epg 424.    Definition eNB : expr := epg 500.   Definition eSB : expr := epg 501.
Definition eGV : expr := epg 518.   Definition eD : expr := epg 357.    Definition e292 : expr := epg 292.
Definition e254 : expr := epg 254.  Definition e109 : expr := epg 109.
Definition eTop : expr := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EVar 391)).
Definition eSp0 : expr := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)).
Definition mk (b : expr) (len : Z) (k : mkind) : amap := {| am_base := b; am_len := ELit len; am_kind := k |}.
Definition TFIB_HEAD3 : list amap := [ mk eGV 4096 KRW; mk eSB 8388608 KRWLAZY; mk eNB 1048576 KRW ].
Definition TFIB_TAIL12 : list amap :=
[ mk eF 11571200 KRW; mk eD 4096 KRW; mk e292 4096 KRW; mk eC 65536 KRW; mk eT 4096 KRW; mk eQ 8388608 KNONELAZY;
mk eP 137439023104 KRW; mk e254 3727360 KRW; mk e109 65536 KRW;
mk (ELit 2201439137792) 15392894357504 KRWLAZY; mk (ELit 2415882240) 2199023255552 KNONELAZY; mk (ELit 2147446784) 268435456 KRWLAZY ].
Definition musl_maps (ch : acs) : list amap := firstn (length (a_maps ch) - 15) (skipn 3 (a_maps ch)).
Definition kn_range_within (ch : acs) (e : expr) (lo hi : Z) : bool :=
existsb (fun K => match K with KRange e' lo' hi' => expr_eqb e e' && (lo <=? lo') && (hi' <=? hi) | _ => false end)%bool (kn ch).
Definition eoff (b : expr) (o : Z) : expr := if o =? 0 then b else EAlu ALU_ADD b (ELit o).
Definition musl_map_ok (ch : acs) (m : amap) : bool :=
match am_kind m, am_base m, am_len m with
| (KRW | KNONE), EMd M_MUL (ELit c) (EVar v), ELit n => (c =? 4096) && kn_range_within ch (EVar v) 1 34359738367 && (0 <? n) && (n <=? 8192)
| KRW, EAlu ALU_ADD (EMd M_MUL (ELit c) (EVar v)) (ELit o), ELit n =>
(c =? 4096) && kn_range_within ch (EVar v) 1 34359738366 && (0 <? n) && (n <=? 4096) && (o =? 4096)
| _, _, _ => false
end%bool.
Lemma musl_map_not_fog : forall ch m, musl_map_ok ch m = true -> is_fog m = false.
Proof. intros ch m H. unfold musl_map_ok in H. unfold is_fog, is_tok_kind. destruct (am_kind m); first [reflexivity | discriminate H]. Qed.
Lemma musl_map_sound : forall ch m, musl_map_ok ch m = true ->
exists v n o, am_base m = eoff (epg v) o /\ am_len m = ELit n /\ 0 < n <= 8192 /\ kn_range_within ch (EVar v) 1 (34359738367 - o / 4096) = true
/\ (o = 0 \/ o = 4096).
Proof.
intros ch m X. unfold musl_map_ok in X.
destruct (am_base m) as [z|v0|op a b|op a b|op a b|op a b|sx lo k e|sx k i k2]; try (destruct (am_kind m); discriminate X).
-
destruct (am_kind m); try discriminate X; destruct op; try discriminate X;
(destruct a as [c0|v1|op1 a1 b1|op1 a1 b1|op1 a1 b1|op1 a1 b1|sx lo k e|sx k i k2]; try discriminate X);
(destruct op1; try discriminate X);
(destruct a1 as [c|v1|op2 a2 b2|op2 a2 b2|op2 a2 b2|op2 a2 b2|sx2 lo2 k3 e2|sx2 k3 i2 k4]; try discriminate X);
(destruct b1 as [c2|v|op2 a2 b2|op2 a2 b2|op2 a2 b2|op2 a2 b2|sx2 lo2 k3 e2|sx2 k3 i2 k4]; try discriminate X);
(destruct b as [o| | | | | | |]; try discriminate X);
(destruct (am_len m) as [n| | | | | | |]; try discriminate X).
apply andb_prop in X as [X X4]. apply andb_prop in X as [X X3]. apply andb_prop in X as [X X2]. apply andb_prop in X as [X0 X1].
apply Z.eqb_eq in X0. apply Z.eqb_eq in X4. apply Z.ltb_lt in X2. apply Z.leb_le in X3. subst c o.
exists v, n, 4096. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact X1 | right; reflexivity].
-
destruct (am_kind m); try discriminate X;
(destruct op; try discriminate X);
(destruct a as [c|v1|op1 a1 b1|op1 a1 b1|op1 a1 b1|op1 a1 b1|sx lo k e|sx k i k2]; try discriminate X);
(destruct b as [c2|v|op2 a2 b2|op2 a2 b2|op2 a2 b2|op2 a2 b2|sx2 lo2 k3 e2|sx2 k3 i2 k4]; try discriminate X);
(destruct (am_len m) as [n| | | | | | |]; try discriminate X).
all: apply andb_prop in X as [X X3]; apply andb_prop in X as [X X2]; apply andb_prop in X as [X0 X1].
all: apply Z.eqb_eq in X0; apply Z.ltb_lt in X2; apply Z.leb_le in X3; subst c.
all: exists v, n, 0.
all: split; [reflexivity|].
all: split; [reflexivity|].
all: split; [lia|].
all: split; [exact X1 | left; reflexivity].
Qed.
Definition TFIB_RANGES : list kentry :=
[ KRange (EVar 255) 4295491576 34326181871; KRange (EVar 256) 0 15;
KRange (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 256)) (EAlu ALU_AND (EMd M_MUL (ELit 4096) (EVar 255)) (ELit 65535))) 0 0;
KRange (EVar 273) 1531 34359734272; KRange (EVar 274) 1 34359736319; KRange (EVar 275) 1531 34359736304;
KRange (EVar 424) 1531 34359733495; KRange (EVar 500) 1531 34359736064; KRange (EVar 501) 1531 34359734272;
KRange (EVar 518) 1 34359736319; KRange (EVar 357) 1 34359736319; KRange (EVar 292) 1 34359736319;
KRange (EVar 254) 1531 34359735410; KRange (EVar 109) 1531 34359736304;
KRange (EVar 0) 4294901760 4294967295; KRange (EVar 6) 0 2047;
KRange eSp0 140735340871680 140737488355136;
KRange (EVar 358) 1 34359736319 ].
Definition eTopT : expr :=
EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 391))) (ELit 3935).
Definition TFIB_GHOST : list (expr * expr) := [(epg 358, ELit 4096)].
Definition BRK_GHOST : expr * expr := (epg 5, ELit 4096).
Definition BRK_BAND_DISJ : kentry := KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (epg 5) 0) (ELit 8192).
Definition RINFO_P : expr * expr := (EAlu ALU_ADD eSp1 (ELit 137439019008), ELit 4096).
Definition IMG_P : expr * expr := (ELit 65536, ELit 6205440).
Definition STK_P : expr * expr :=
(EAlu ALU_ADD eSp0 (ELit (-8388608)),
EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-32768)) (EVar 0)) (EMd M_MUL (ELit (-16)) (EVar 6))) (ELit 140737496743936)).
Definition sub_of_map (p : expr * expr) (m : amap) : bool :=
match am_base m, am_len m with
| ELit _, _ => false
| b, ELit L =>
(0 <=? L) && (L <? 2 ^ 64)
&& (pair_eqb p (b, ELit L)
|| match p with
| (EAlu ALU_ADD b' (ELit k), ELit n) => expr_eqb b' b && (0 <=? k) && (0 <=? n) && (k + n <=? L)
| _ => false
end)
| _, _ => false
end%bool.
Definition avis_ok (ch : acs) (p : expr * expr) : bool :=
(existsb (sub_of_map p) (a_maps ch) || pair_eqb p RINFO_P || pair_eqb p IMG_P || pair_eqb p STK_P)%bool.
Lemma sub_of_map_sound : forall p m, sub_of_map p m = true ->
match am_base m with ELit _ => False | _ => True end
/\ exists L, am_len m = ELit L /\ 0 <= L < 2 ^ 64
/\ (p = (am_base m, ELit L) \/ exists k n, p = (EAlu ALU_ADD (am_base m) (ELit k), ELit n) /\ 0 <= k /\ 0 <= n /\ k + n <= L).
Proof.
intros [pb pn] m H. unfold sub_of_map in H.
destruct (am_len m) as [L| | | | | | |]; try (destruct (am_base m); discriminate H).
assert (Hb : match am_base m with ELit _ => False | _ => True end) by (destruct (am_base m); [discriminate H | exact I ..]).
split; [exact Hb|]. exists L.
assert (H' : ((0 <=? L) && (L <? 2 ^ 64) &&
(pair_eqb (pb, pn) (am_base m, ELit L)
|| match pb, pn with
| EAlu ALU_ADD b' (ELit k), ELit n => expr_eqb b' (am_base m) && (0 <=? k) && (0 <=? n) && (k + n <=? L)
| _, _ => false end))%bool = true) by (destruct (am_base m); [exfalso; exact Hb | exact H ..]).
clear H. apply andb_prop in H' as [HL H']. apply andb_prop in HL as [HL1 HL2]. apply Z.leb_le in HL1. apply Z.ltb_lt in HL2.
split; [reflexivity|]. split; [lia|].
apply orb_prop in H' as [H'|H']; [left; exact (pair_eqb_eq _ _ H')| right].
destruct pb as [ | | op b1 b2 | | | | | ]; try discriminate H'. destruct op; try discriminate H'.
destruct b2 as [k| | | | | | |]; try discriminate H'. destruct pn as [n| | | | | | |]; try discriminate H'.
apply andb_prop in H' as [H' H3]. apply andb_prop in H' as [H' H2]. apply andb_prop in H' as [H' H1].
apply expr_eqb_eq in H'. subst b1. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
exists k, n. repeat split; try lia.
Qed.
Definition top_class (ch : acs) : bool :=
((kn_range_within ch (EVar 391) 0 0 && kn_range_within ch eTopT 0 4095)
|| (kn_range_within ch (EVar 391) 1 7 && kn_range_within ch eTopT 0 4095)
|| (kn_range_within ch (EVar 391) 8 8 && kn_range_within ch (EVar 6) 1803 2047))%bool.
Definition hole_chk (ch : acs) : bool :=
(list_eqb amap_eqb (a_maps ch) (TFIB_HEAD3 ++ musl_maps ch ++ TFIB_TAIL12))
&& (Nat.leb (length (musl_maps ch)) 2)
&& forallb (musl_map_ok ch) (musl_maps ch)
&& forallb (fun K => kn_mem K ch) TFIB_RANGES
&& kn_range_within ch (EVar 391) 0 8 && top_class ch
&& (list_eqb pair_eqb (a_ghost ch) TFIB_GHOST || (list_eqb pair_eqb (a_ghost ch) (TFIB_GHOST ++ [BRK_GHOST]) && kn_mem BRK_BAND_DISJ ch))
&& (match a_fd ch with FdStd => true | _ => false end)
&& (a_abytes ch <=? 2461292544) && (a_eager ch <=? 16515072) && (23112583966720 <=? a_ylo ch)
&& forallb (avis_ok ch) (a_vis ch) && existsb (pair_eqb STK_P) (a_vis ch)
&& kn_mem (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (epg 358) 0) (ELit 4096)) ch.
Lemma tfib_holes_chk : forallb hole_chk HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Section g.
Variable E : env.
#[local] Notation u := (uE E).
#[local] Notation V n := (bv_unsigned (ev E n)).
Lemma uE_bound : forall e, 0 <= u e < 2 ^ 64.
Proof. intros e. unfold uE. pose proof (bv_unsigned_in_range 64 (edenot E e)) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
Lemma eqm_small_eq : forall a b, eqm a b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof. intros a b [q Hq] Ha Hb. assert (q = 0) by nia. subst q. lia. Qed.
Lemma uE_litv : forall z, 0 <= z < 2 ^ 64 -> u (ELit z) = z.
Proof. intros z Hz. unfold uE. cbn [edenot]. rewrite u64_lit by lia. reflexivity. Qed.
Lemma uE_var : forall n, u (EVar n) = V n.
Proof. reflexivity. Qed.
Lemma uE_add : forall a b, u a + u b < 2 ^ 64 -> u (EAlu ALU_ADD a b) = u a + u b.
Proof.
intros a b H. pose proof (uE_bound a). pose proof (uE_bound b). pose proof (uE_bound (EAlu ALU_ADD a b)).
apply eqm_small_eq; [|lia|lia]. unfold uE. cbn [edenot]. apply u_add_eqm.
Qed.
Lemma uE_add_eqm : forall a b, eqm (u (EAlu ALU_ADD a b)) (u a + u b).
Proof. intros a b. unfold uE. cbn [edenot]. apply u_add_eqm. Qed.
Lemma uE_mul_lit : forall k a, 0 <= k -> k * u a < 2 ^ 64 -> u (EMd M_MUL (ELit k) a) = k * u a.
Proof.
intros k a Hk H. pose proof (uE_bound a). pose proof (uE_bound (EMd M_MUL (ELit k) a)).
assert (Hk' : k < 2 ^ 64 \/ u a = 0) by nia.
apply eqm_small_eq; [|lia|nia]. unfold uE. cbn [edenot].
eapply eqm_trans; [apply u_mul_eqm|]. fold (u a). destruct Hk' as [Hk'|Hz].
- rewrite u64_lit by lia. apply eqm_refl.
- rewrite Hz, !Z.mul_0_r. apply eqm_refl.
Qed.
Lemma uE_add_negmul : forall a k b, - 2 ^ 64 < k < 0 -> - k * u b <= u a -> u (EAlu ALU_ADD a (EMd M_MUL (ELit k) b)) = u a + k * u b.
Proof.
intros a k b Hk H. pose proof (uE_bound a). pose proof (uE_bound b). pose proof (uE_bound (EAlu ALU_ADD a (EMd M_MUL (ELit k) b))).
apply eqm_small_eq; [|lia|nia]. unfold uE. cbn [edenot].
eapply eqm_trans; [apply u_add_eqm|]. fold (u a). apply eqm_add; [apply eqm_refl|].
eapply eqm_trans; [apply u_mul_eqm|]. fold (u b). apply eqm_mul_r. apply eqm_u_lit.
Qed.
Lemma uE_add_neglit : forall a k, k < 0 -> - k <= u a -> u (EAlu ALU_ADD a (ELit k)) = u a + k.
Proof.
intros a k Hk H. pose proof (uE_bound a). pose proof (uE_bound (EAlu ALU_ADD a (ELit k))).
apply eqm_small_eq; [|lia|lia]. unfold uE. cbn [edenot].
eapply eqm_trans; [apply u_add_eqm|]. fold (u a). apply eqm_add; [apply eqm_refl|]. apply eqm_u_lit.
Qed.
Lemma uE_and_lit : forall a k, 0 <= k < 2 ^ 64 -> u (EAlu ALU_AND a (ELit k)) = Z.land (u a) k.
Proof.
intros a k Hk. unfold uE. cbn [edenot]. rewrite u_and64. f_equal. apply u64_lit. lia.
Qed.
End g.
Section s.
Lemma seps_cons_inv : forall p l, seps (p :: l) -> Forall (iv_disjoint p) l /\ seps l.
Proof. intros p l H. inversion H; subst; auto. Qed.
Lemma seps_app_inv : forall l1 l2, seps (l1 ++ l2) ->
seps l1 /\ seps l2 /\ (forall x y, In x l1 -> In y l2 -> iv_disjoint x y).
Proof.
induction l1 as [|p l1 IH]; intros l2 H; cbn in H.
- split; [constructor|]. split; [exact H|]. intros x y [].
- apply seps_cons_inv in H as [F S]. destruct (IH l2 S) as (S1 & S2 & X).
split; [constructor; [apply Forall_forall; intros q Hq; apply (proj1 (Forall_forall _ _) F); apply in_app_iff; left; exact Hq | exact S1]|].
split; [exact S2|]. intros x y [<-|Hx] Hy; [| exact (X x y Hx Hy)].
apply (proj1 (Forall_forall _ _) F). apply in_app_iff. right. exact Hy.
Qed.
Lemma iv_disjoint_sym : forall p q, iv_disjoint p q -> iv_disjoint q p.
Proof. intros p q H. unfold iv_disjoint in *. lia. Qed.
Lemma seps_In_disjoint : forall l x y, seps l -> In x l -> In y l -> x = y \/ iv_disjoint x y.
Proof.
induction l as [|p l IH]; intros x y S Hx Hy; [destruct Hx|].
apply seps_cons_inv in S as [F S]. destruct Hx as [<-|Hx], Hy as [<-|Hy].
- left; reflexivity.
- right. exact (proj1 (Forall_forall _ _) F y Hy).
- right. apply iv_disjoint_sym. exact (proj1 (Forall_forall _ _) F x Hx).
- exact (IH x y S Hx Hy).
Qed.
Lemma seps_pair : forall l, seps l -> forall i j x y, (i < j)%nat -> nth_error l i = Some x -> nth_error l j = Some y -> iv_disjoint x y.
Proof.
induction l as [|p l IH]; intros S i j x y Hij Hi Hj; [destruct i; discriminate Hi|].
apply seps_cons_inv in S as [F S]. destruct i as [|i], j as [|j]; try lia.
- cbn in Hi, Hj. injection Hi as <-. exact (proj1 (Forall_forall _ _) F y (nth_error_In _ _ Hj)).
- cbn in Hi, Hj. apply (IH S i j x y); [lia | exact Hi | exact Hj].
Qed.
Lemma seps_filter : forall (f : word * word -> bool) l, seps l -> seps (List.filter f l).
Proof.
induction l as [|p l IH]; intros S; cbn; [constructor|]. apply seps_cons_inv in S as [F S].
destruct (f p); [|exact (IH S)]. constructor; [|exact (IH S)].
apply Forall_forall. intros q Hq. apply filter_In in Hq as [Hq _]. exact (proj1 (Forall_forall _ _) F q Hq).
Qed.
Definition wzp (iv : word * word) : Z * Z := (bv_unsigned (fst iv), bv_unsigned (snd iv)).
Lemma seps_pairwise : forall l, seps l -> pairwise zdisjoint (map wzp l).
Proof.
induction l as [|p l IH]; intros S; cbn; [exact I|]. apply seps_cons_inv in S as [F S]. split; [|exact (IH S)].
apply Forall_map. apply Forall_forall. intros q Hq. pose proof (proj1 (Forall_forall _ _) F q Hq) as D.
unfold iv_disjoint in D. unfold zdisjoint, wzp. cbn [fst snd]. lia.
Qed.
Lemma pairwise_app {X} (Rr : X -> X -> Prop) : forall l1 l2,
pairwise Rr l1 -> pairwise Rr l2 -> (forall x y, In x l1 -> In y l2 -> Rr x y) -> pairwise Rr (l1 ++ l2).
Proof.
induction l1 as [|a l1 IH]; intros l2 P1 P2 HX; cbn; [exact P2|]. destruct P1 as [F P1]. split.
- apply Forall_app. split; [exact F|]. apply Forall_forall. intros y Hy. apply HX; [left; reflexivity | exact Hy].
- apply IH; [exact P1 | exact P2 |]. intros x y Hx Hy. apply HX; [right; exact Hx | exact Hy].
Qed.
End s.
Lemma pb_facts : forall a : word,
bv_unsigned (page_base a) <= bv_unsigned a /\ bv_unsigned a < bv_unsigned (page_base a) + 4096 /\ bv_unsigned (page_base a) mod 4096 = 0.
Proof.
intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
Qed.
Section t. Context {fx : YK11.FPState}.
Section a0.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
#[local] Notation SINV := (YA02.SINV0 TPH sp rdraw brk argv envp uid hw).
#[local] Notation argH := (YA02.argH0 TPH sp rdraw argv envp uid hw).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Hypothesis HE : forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 TPH sp rdraw brk argv envp uid hw) n.
Hypothesis HM : forall a, argH E a = true -> FULL a = wrap_mem TPH sp argv envp uid hw rdraw a.
#[local] Notation MR := (Mr TFIB TOP argH E ch model FULL).
#[local] Notation HID := (hid TFIB TOP argH E ch model).
#[local] Notation u := (uE E).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation V n := (bv_unsigned (ev E n)).
#[local] Notation vm := (vm_maps (m_vmmaps model)).
Lemma usp_window : sp_window_lo <= usp <= sp_window_hi.
Proof. pose proof Hsp as (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.
Context {rc : YM05.RunCeil}.
Hypothesis Hceil : YM05.ceil_of_top (usp - stack_max_size).
Lemma ceil_run : @alloc_ceiling rc = run_ceil usp.
Proof. exact Hceil. Qed.
Lemma ceil_le_TOP : ASAN_CEIL <= TOP.
Proof. unfold ASAN_CEIL. rewrite ceil_run. unfold run_ceil, YA02.TOP. change stack_max_size with 8388608. apply page_floor_le. Qed.
Lemma ceil_ge_TOP : TOP - 4095 <= ASAN_CEIL /\ ASAN_CEIL mod 4096 = 0.
Proof.
unfold ASAN_CEIL. rewrite ceil_run. unfold run_ceil, page_floor, YA02.TOP. change stack_max_size with 8388608.
split; [| apply Z_mod_mult]. pose proof (Z.div_mod (usp - 8388608) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (usp - 8388608) 4096 ltac:(lia)). lia.
Qed.
Lemma ceil_of_top : YM05.ceil_of_top (usp - stack_max_size).
Proof. exact Hceil. Qed.
Let TOPok : top_ok TOP := YA02.top_ok0 sp Hsp.
Let ARGH : forall E0 (a : word), argH E0 a = true -> TOP <= bv_unsigned a := YA02.argH0_high TPH sp rdraw argv envp uid hw Hsp Hva.
Lemma CHK : hole_chk ch = true.
Proof. exact (proj1 (forallb_forall _ _) tfib_holes_chk ch (HS_tfib_In h ch Hch)). Qed.
Lemma hole_facts :
a_maps ch = TFIB_HEAD3 ++ musl_maps ch ++ TFIB_TAIL12
/\ (length (musl_maps ch) <= 2)%nat /\ Forall (fun m => musl_map_ok ch m = true) (musl_maps ch)
/\ forallb (fun K => kn_mem K ch) TFIB_RANGES = true /\ (kn_range_within ch (EVar 391) 0 8 = true /\ top_class ch = true)
/\ (a_ghost ch = TFIB_GHOST \/ (a_ghost ch = TFIB_GHOST ++ [BRK_GHOST] /\ kn_mem BRK_BAND_DISJ ch = true)) /\ a_fd ch = FdStd
/\ a_abytes ch <= 2461292544 /\ a_eager ch <= 16515072 /\ 23112583966720 <= a_ylo ch
/\ forallb (avis_ok ch) (a_vis ch) = true /\ In STK_P (a_vis ch)
/\ kn_mem (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (epg 358) 0) (ELit 4096)) ch = true.
Proof.
pose proof CHK as H. unfold hole_chk in H.
apply andb_prop in H as [H H14]. apply andb_prop in H as [H H13]. apply andb_prop in H as [H H12]. apply andb_prop in H as [H H11].
apply andb_prop in H as [H H10]. apply andb_prop in H as [H H9]. apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7].
apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
apply andb_prop in H as [H1 H2].
split; [exact (list_eqb_eq amap_eqb amap_eqb_eq _ _ H1)|]. split; [exact (proj1 (Nat.leb_le _ _) H2)|].
split; [apply Forall_forall; exact (proj1 (forallb_forall _ _) H3)|]. split; [exact H4|]. split; [split; [exact H5 | exact H6]|].
split; [apply orb_prop in H7 as [H7|H7]; [left; exact (list_eqb_eq pair_eqb pair_eqb_eq _ _ H7) | right; apply andb_prop in H7 as [H7 H7b]; split; [exact (list_eqb_eq pair_eqb pair_eqb_eq _ _ H7) | exact H7b]]|].
split; [destruct (a_fd ch); [reflexivity | discriminate H8 | discriminate H8]|].
apply Z.leb_le in H9. apply Z.leb_le in H10. apply Z.leb_le in H11.
assert (H13c : In STK_P (a_vis ch)) by (apply existsb_exists in H13 as (q & Hq & Hqe); apply pair_eqb_eq in Hqe; rewrite Hqe; exact Hq).
repeat split; assumption.
Qed.
Lemma tfib_hole_avis : forallb (avis_ok ch) (a_vis ch) = true.   Proof. pose proof hole_facts; tauto. Qed.
Lemma tfib_hole_stk : In STK_P (a_vis ch).   Proof. pose proof hole_facts; tauto. Qed.
Lemma tfib_hole_ghostdisj : kn_mem (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (epg 358) 0) (ELit 4096)) ch = true.   Proof. pose proof hole_facts; tauto. Qed.
Lemma tfib_hole_maps : a_maps ch = TFIB_HEAD3 ++ musl_maps ch ++ TFIB_TAIL12.   Proof. exact (proj1 hole_facts). Qed.
Lemma tfib_hole_ranges : forallb (fun K => kn_mem K ch) TFIB_RANGES = true.   Proof. exact (proj1 (proj2 (proj2 (proj2 hole_facts)))). Qed.
Lemma tfib_hole_ghost : a_ghost ch = TFIB_GHOST \/ (a_ghost ch = TFIB_GHOST ++ [BRK_GHOST] /\ kn_mem BRK_BAND_DISJ ch = true).   Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 hole_facts)))))). Qed.
Lemma tfib_hole_fd : a_fd ch = FdStd.   Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 hole_facts))))))). Qed.
Definition rd : reader := hreader TSEGS MR.
Lemma rd_aview : rd = aview TSEGS HID FULL.
Proof. unfold rd, aview, hreader. rewrite Mr_is_mrestrict. reflexivity. Qed.
Let Hrange := ho_range TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC.
Let Hbyte := ho_read_byte TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC.
Definition rng_of (e : expr) : option (Z * Z) :=
match find (fun K => match K with KRange e' _ _ => expr_eqb e e' | _ => false end) TFIB_RANGES with
| Some (KRange _ lo hi) => Some (lo, hi) | _ => None end.
Lemma RNG : forall e lo hi, rng_of e = Some (lo, hi) -> lo <= u e <= hi.
Proof.
intros e lo hi H. unfold rng_of in H.
destruct (find _ TFIB_RANGES) as [K|] eqn:Hf; [|discriminate H].
apply find_some in Hf as [Hin HK]. destruct K as [| | | | |e' lo' hi'| | | |]; try discriminate H.
injection H as <- <-. apply expr_eqb_eq in HK. subst e'.
apply Hrange. exact (proj1 (forallb_forall _ _) tfib_hole_ranges _ Hin).
Qed.
#[local] Ltac rng e := let H := fresh in pose proof (RNG e _ _ eq_refl) as H; revert H.
Lemma range_within : forall e lo hi, kn_range_within ch e lo hi = true -> lo <= u e <= hi.
Proof.
intros e lo hi H. unfold kn_range_within in H. apply existsb_exists in H as (K & HK & Hb).
destruct K as [| | | | |e' lo' hi'| | | |]; try discriminate Hb.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2]. apply expr_eqb_eq in H1. subst e'.
apply Z.leb_le in H2. apply Z.leb_le in H3.
assert (X : lo' <= u e <= hi') by (apply Hrange; unfold kn_mem; apply existsb_exists; exists (KRange e lo' hi'); split; [exact HK | cbn [kentry_eqb]; rewrite kx_expr_eqb_refl, !Z.eqb_refl; reflexivity]).
lia.
Qed.
Lemma u391 : 0 <= V 391 <= 8.
Proof. rewrite <- uE_var. apply range_within. exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 hole_facts)))))). Qed.
Lemma tfib_top_class : top_class ch = true.   Proof. exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 hole_facts)))))). Qed.
Lemma u_epg : forall n lo hi, rng_of (EVar n) = Some (lo, hi) -> 0 <= lo -> hi <= 2 ^ 51 ->
u (epg n) = 4096 * V n /\ 4096 * lo <= u (epg n) <= 4096 * hi.
Proof.
intros n lo hi Hin Hlo Hhi. pose proof (RNG _ _ _ Hin) as Hr. rewrite uE_var in Hr.
assert (Hu : u (epg n) = 4096 * V n) by (unfold epg; rewrite uE_mul_lit; [rewrite uE_var; reflexivity | lia | rewrite uE_var; lia]).
rewrite Hu. lia.
Qed.
#[local] Ltac upg n := let H := fresh in pose proof (u_epg n _ _ eq_refl ltac:(lia) ltac:(lia)) as H; revert H.
Lemma uP : u eP = 4096 * V 255 /\ 4096 * 4295491576 <= u eP <= 4096 * 34326181871.    Proof. unfold eP. upg 255%nat. tauto. Qed.
Lemma uQ : u eQ = 4096 * V 273 /\ 4096 * 1531 <= u eQ <= 4096 * 34359734272.          Proof. unfold eQ. upg 273%nat. tauto. Qed.
Lemma uT : u eT = 4096 * V 274 /\ 4096 * 1 <= u eT <= 4096 * 34359736319.             Proof. unfold eT. upg 274%nat. tauto. Qed.
Lemma uC : u eC = 4096 * V 275 /\ 4096 * 1531 <= u eC <= 4096 * 34359736304.          Proof. unfold eC. upg 275%nat. tauto. Qed.
Lemma uD : u eD = 4096 * V 357 /\ 4096 * 1 <= u eD <= 4096 * 34359736319.             Proof. unfold eD. upg 357%nat. tauto. Qed.
Lemma uF : u eF = 4096 * V 424 /\ 4096 * 1531 <= u eF <= 4096 * 34359733495.          Proof. unfold eF. upg 424%nat. tauto. Qed.
Lemma uNB : u eNB = 4096 * V 500 /\ 4096 * 1531 <= u eNB <= 4096 * 34359736064.       Proof. unfold eNB. upg 500%nat. tauto. Qed.
Lemma uSB : u eSB = 4096 * V 501 /\ 4096 * 1531 <= u eSB <= 4096 * 34359734272.       Proof. unfold eSB. upg 501%nat. tauto. Qed.
Lemma uGV : u eGV = 4096 * V 518 /\ 4096 * 1 <= u eGV <= 4096 * 34359736319.          Proof. unfold eGV. upg 518%nat. tauto. Qed.
Lemma u292 : u e292 = 4096 * V 292 /\ 4096 * 1 <= u e292 <= 4096 * 34359736319.       Proof. unfold e292. upg 292%nat. tauto. Qed.
Lemma u254 : u e254 = 4096 * V 254 /\ 4096 * 1531 <= u e254 <= 4096 * 34359735410.    Proof. unfold e254. upg 254%nat. tauto. Qed.
Lemma u109 : u e109 = 4096 * V 109 /\ 4096 * 1531 <= u e109 <= 4096 * 34359736304.    Proof. unfold e109. upg 109%nat. tauto. Qed.
Lemma uSp1 : u eSp1 = u eP - u eP mod 65536.
Proof.
pose proof uP as [HP HPr]. pose proof (RNG (EVar 256) _ _ eq_refl) as H222. rewrite uE_var in H222.
pose proof (RNG (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 256)) (EAlu ALU_AND (EMd M_MUL (ELit 4096) (EVar 255)) (ELit 65535))) _ _ eq_refl) as HX.
assert (HA : u (EAlu ALU_AND (EMd M_MUL (ELit 4096) (EVar 255)) (ELit 65535)) = u eP mod 65536).
{ rewrite uE_and_lit by lia. change (EMd M_MUL (ELit 4096) (EVar 255)) with eP. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. reflexivity. }
assert (HMm : u (EMd M_MUL (ELit (-4096)) (EVar 256)) = (2 ^ 64 - 4096 * V 256) mod 2 ^ 64).
{ pose proof (uE_bound E (EMd M_MUL (ELit (-4096)) (EVar 256))) as Hb.
apply eqm_small_eq; [| exact Hb | apply Z.mod_pos_bound; lia].
eapply eqm_trans; [unfold uE; cbn [edenot]; apply u_mul_eqm|].
eapply eqm_trans; [apply eqm_mul_r; apply eqm_u_lit|]. eapply eqm_trans; [|apply eqm_sym; apply eqm_mod]. exists (-1). lia. }
assert (HS : (u (EMd M_MUL (ELit (-4096)) (EVar 256)) + u (EAlu ALU_AND (EMd M_MUL (ELit 4096) (EVar 255)) (ELit 65535))) mod 2 ^ 64 = 0).
{ pose proof (uE_bound E (EMd M_MUL (ELit (-4096)) (EVar 256))) as B1. pose proof (uE_bound E (EAlu ALU_AND (EMd M_MUL (ELit 4096) (EVar 255)) (ELit 65535))) as B2.
destruct HX as [_ HX].
pose proof (uE_add_eqm E (EMd M_MUL (ELit (-4096)) (EVar 256)) (EAlu ALU_AND (EMd M_MUL (ELit 4096) (EVar 255)) (ELit 65535))) as [q Hq].
pose proof (uE_bound E (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 256)) (EAlu ALU_AND (EMd M_MUL (ELit 4096) (EVar 255)) (ELit 65535)))) as B3.
assert (Hs : u (EMd M_MUL (ELit (-4096)) (EVar 256)) + u (EAlu ALU_AND (EMd M_MUL (ELit 4096) (EVar 255)) (ELit 65535)) = (- q) * 2 ^ 64) by lia.
rewrite Hs. apply Z_mod_mult. }
rewrite HA, HMm in HS.
assert (HEq : 4096 * V 256 = u eP mod 65536).
{ pose proof (Z.mod_pos_bound (u eP) 65536 ltac:(lia)).
destruct (Z.eq_dec (V 256) 0) as [Z0|NZ].
- rewrite Z0 in HS. rewrite Z.sub_0_r, Z.mod_same, Z.add_0_l in HS by lia. rewrite Z.mod_small in HS by lia. lia.
- rewrite (Z.mod_small (2 ^ 64 - 4096 * V 256)) in HS by lia.
replace (2 ^ 64 - 4096 * V 256 + u eP mod 65536) with ((u eP mod 65536 - 4096 * V 256) + 1 * 2 ^ 64) in HS by lia.
rewrite Z.mod_add in HS by lia.
destruct (Z.lt_ge_cases (u eP mod 65536 - 4096 * V 256) 0) as [Hn|Hp].
+ replace (u eP mod 65536 - 4096 * V 256) with ((u eP mod 65536 - 4096 * V 256 + 2 ^ 64) + (-1) * 2 ^ 64) in HS by lia.
rewrite Z.mod_add, Z.mod_small in HS by lia. lia.
+ rewrite Z.mod_small in HS by lia. lia. }
unfold eSp1. rewrite uE_add_negmul; [| lia | rewrite uE_var; pose proof (Z.mod_le (u eP) 65536); lia]. rewrite uE_var. fold eP. lia.
Qed.
Lemma uSp : u eSp = u eSp1 + 65536 /\ u eSp mod 65536 = 0 /\ u eP <= u eSp /\ u eSp <= u eP + 65536.
Proof.
pose proof uP as [_ HPr]. pose proof uSp1 as H1. pose proof (Z.mod_pos_bound (u eP) 65536 ltac:(lia)) as Hm.
assert (Hs : u eSp = u eSp1 + 65536) by (unfold eSp; rewrite uE_add; rewrite ?uE_litv; lia).
rewrite Hs, H1. split; [reflexivity|]. split; [|lia].
replace (u eP - u eP mod 65536 + 65536) with ((u eP - u eP mod 65536) + 1 * 65536) by lia. rewrite Z.mod_add by lia.
rewrite Zminus_mod_idemp_r. rewrite Z.sub_diag. reflexivity.
Qed.
Lemma uSp0 : u eSp0 = 32768 * V 0 + 16 * V 6 /\ 140735340871680 <= u eSp0 <= 140737488355136.
Proof.
rng (EVar 0). rng (EVar 6). rng eSp0. intros H3 H2 H1. rewrite !uE_var in *.
assert (Hu : u eSp0 = 32768 * V 0 + 16 * V 6).
{ unfold eSp0. rewrite uE_add; rewrite !uE_mul_lit; rewrite ?uE_var; lia. }
rewrite Hu in *. lia.
Qed.
Lemma uTop : u eTop = 32768 * V 0 + 4096 * V 391 /\ 140735340871680 <= u eTop /\ u eTop <= 2 ^ 47 /\ u eTop mod 4096 = 0.
Proof.
rng (EVar 0). pose proof u391 as H1. intros H3. rewrite !uE_var in *.
assert (Hu : u eTop = 32768 * V 0 + 4096 * V 391).
{ unfold eTop. rewrite uE_add; rewrite !uE_mul_lit; rewrite ?uE_var; lia. }
rewrite Hu. split; [reflexivity|]. split; [lia|]. split.
-   lia.
- replace (32768 * V 0 + 4096 * V 391) with ((8 * V 0 + V 391) * 4096) by lia. apply Z_mod_mult.
Qed.
Definition dmm (m : amap) : word * word := amap_den E m.
Definition dm (b : expr) (len : Z) (k : mkind) : word * word := dmm (mk b len k).
Lemma u_snd_dm : forall b len k, 0 <= len < 2 ^ 64 -> bv_unsigned (snd (dm b len k)) = len.
Proof. intros b len k H. unfold dm, dmm, amap_den. cbn [snd am_len mk edenot]. apply u64_lit. exact H. Qed.
Lemma u_fst_dm : forall b len k, bv_unsigned (fst (dm b len k)) = u b.
Proof. intros. reflexivity. Qed.
Lemma maps_match_exact : forall ms l, maps_match E ms l -> forallb (fun m => negb (is_fog m)) ms = true -> l = map dmm ms.
Proof.
induction ms as [|m ms IH]; intros l Hm Hf; cbn in Hm |- *; [exact Hm|].
apply andb_prop in Hf as [Hf1 Hf2]. destruct (is_fog m); [discriminate Hf1|].
destruct Hm as (l' & -> & Hm). rewrite (IH l' Hm Hf2). reflexivity.
Qed.
Definition ALLMAPS : list amap := TFIB_HEAD3 ++ musl_maps ch ++ TFIB_TAIL12.
Lemma vm_eq : vm = map dmm ALLMAPS.
Proof.
pose proof (ho_maps TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) as M. rewrite tfib_hole_maps in M.
apply (maps_match_exact _ _ M). unfold ALLMAPS. rewrite !forallb_app.
pose proof hole_facts as (_ & _ & MOK & _).
assert (X : forallb (fun m => negb (is_fog m)) (musl_maps ch) = true).
{ apply forallb_forall. intros m Hin. rewrite (musl_map_not_fog ch m (proj1 (Forall_forall _ _) MOK m Hin)). reflexivity. }
rewrite X. reflexivity.
Qed.
Lemma vm_In : forall m, In m ALLMAPS -> In (dmm m) vm.
Proof. intros m Hm. rewrite vm_eq. apply in_map. exact Hm. Qed.
Lemma musl_len : (length (musl_maps ch) <= 2)%nat.   Proof. pose proof hole_facts; tauto. Qed.
Let Hseps := ho_seps TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC.
Let Hbounds := ho_bounds TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC.
Lemma vm_bound : forall iv, In iv vm ->
0 < bv_unsigned (snd iv) /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
/\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= 0x10000 \/ 0x5fb000 <= bv_unsigned (fst iv))
/\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ASAN_CEIL.
Proof.
intros iv H. pose proof (proj1 (Forall_forall _ _) Hbounds iv H) as X. cbn beta in X.
change (img_lo TFIB) with 0x10000 in X. change (img_hi TFIB) with 0x5fb000 in X.
destruct X as (X1 & X2 & X3 & X4 & X5). repeat split; try assumption.
unfold ASAN_CEIL. rewrite ceil_run. apply page_floor_ge; [| exact X5]. rewrite Z.add_mod, X2, X3 by lia. reflexivity.
Qed.
Definition dLow := dm (ELit 2147446784) 268435456 KRWLAZY.
Definition dGap := dm (ELit 2415882240) 2199023255552 KNONELAZY.
Definition dHigh := dm (ELit 2201439137792) 15392894357504 KRWLAZY.
Lemma band_vals : wzp dLow = (2147446784, 268435456) /\ wzp dGap = (2415882240, 2199023255552) /\ wzp dHigh = (2201439137792, 15392894357504).
Proof. unfold wzp, dLow, dGap, dHigh. rewrite !u_fst_dm, !u_snd_dm by lia. rewrite !uE_litv by lia. repeat split; reflexivity. Qed.
Lemma nth_ALLMAPS_tail : forall i m, nth_error TFIB_TAIL12 i = Some m -> nth_error ALLMAPS (3 + length (musl_maps ch) + i) = Some m.
Proof.
intros i m H. unfold ALLMAPS. rewrite nth_error_app2 by (cbn; lia). change (length TFIB_HEAD3) with 3%nat.
rewrite nth_error_app2 by lia. replace (3 + length (musl_maps ch) + i - 3 - length (musl_maps ch))%nat with i by lia. exact H.
Qed.
Lemma vm_nth : forall i m, nth_error ALLMAPS i = Some m -> nth_error vm i = Some (dmm m).
Proof. intros i m H. rewrite vm_eq, nth_error_map, H. reflexivity. Qed.
Lemma vm_split : forall i m, nth_error ALLMAPS i = Some m ->
(i <> 3 + length (musl_maps ch) + 9)%nat -> (i <> 3 + length (musl_maps ch) + 10)%nat -> (i <> 3 + length (musl_maps ch) + 11)%nat ->
bv_unsigned (fst (dmm m)) + bv_unsigned (snd (dmm m)) <= 2147446784 \/ kHighMemBeg <= bv_unsigned (fst (dmm m)).
Proof.
intros i m Hi N1 N2 N3. pose proof band_vals as (VL & VG & VH). unfold wzp in VL, VG, VH.
apply (f_equal fst) in VL as L1; apply (f_equal snd) in VL as L2. apply (f_equal fst) in VG as G1; apply (f_equal snd) in VG as G2.
apply (f_equal fst) in VH as Y1; apply (f_equal snd) in VH as Y2. cbn [fst snd] in L1, L2, G1, G2, Y1, Y2.
pose proof (vm_nth _ _ Hi) as Hm.
pose proof (vm_nth _ _ (nth_ALLMAPS_tail 9 _ eq_refl)) as HH. pose proof (vm_nth _ _ (nth_ALLMAPS_tail 10 _ eq_refl)) as HG.
pose proof (vm_nth _ _ (nth_ALLMAPS_tail 11 _ eq_refl)) as HL.
change (dmm (mk (ELit 2201439137792) 15392894357504 KRWLAZY)) with dHigh in HH.
change (dmm (mk (ELit 2415882240) 2199023255552 KNONELAZY)) with dGap in HG.
change (dmm (mk (ELit 2147446784) 268435456 KRWLAZY)) with dLow in HL.
pose proof (proj1 (vm_bound (dmm m) (nth_error_In _ _ Hm))) as P0.
assert (DH : iv_disjoint (dmm m) dHigh).
{ destruct (Nat.lt_ge_cases i (3 + length (musl_maps ch) + 9)).
- exact (seps_pair _ Hseps _ _ _ _ H Hm HH).
- apply iv_disjoint_sym. exact (seps_pair _ Hseps (3 + length (musl_maps ch) + 9)%nat i _ _ ltac:(lia) HH Hm). }
assert (DG : iv_disjoint (dmm m) dGap).
{ destruct (Nat.lt_ge_cases i (3 + length (musl_maps ch) + 10)).
- exact (seps_pair _ Hseps _ _ _ _ H Hm HG).
- apply iv_disjoint_sym. exact (seps_pair _ Hseps (3 + length (musl_maps ch) + 10)%nat i _ _ ltac:(lia) HG Hm). }
assert (DL : iv_disjoint (dmm m) dLow).
{ destruct (Nat.lt_ge_cases i (3 + length (musl_maps ch) + 11)).
- exact (seps_pair _ Hseps _ _ _ _ H Hm HL).
- apply iv_disjoint_sym. exact (seps_pair _ Hseps (3 + length (musl_maps ch) + 11)%nat i _ _ ltac:(lia) HL Hm). }
unfold iv_disjoint in DH, DG, DL. rewrite L1, L2 in DL. rewrite G1, G2 in DG. rewrite Y1, Y2 in DH. unfold kHighMemBeg. lia.
Qed.
Lemma eSp0_e_sp0 : eSp0 = e_sp0.
Proof. reflexivity. Qed.
Lemma uS0 : u eSp0 = usp.
Proof.
pose proof (YA02.SINV0_sp0 TPH sp rdraw brk argv envp uid hw Hsp Hva Hve Hfit E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as X.
rewrite eSp0_e_sp0. unfold YA02.TOP in X. lia.
Qed.
Lemma usp_range : 140735340871680 <= usp <= 140737488355136 /\ usp mod 16 = 0.
Proof. pose proof uSp0 as [_ H]. rewrite uS0 in H. pose proof Hsp as (_ & _ & A). split; [exact H | exact A]. Qed.
Lemma map_facts : forall i m, nth_error ALLMAPS i = Some m -> match am_base m with ELit _ => False | _ => True end ->
bv_unsigned (fst (dmm m)) + bv_unsigned (snd (dmm m)) <= ASAN_CEIL
/\ (bv_unsigned (fst (dmm m)) + bv_unsigned (snd (dmm m)) <= 2147446784 \/ kHighMemBeg <= bv_unsigned (fst (dmm m)))
/\ 0 < bv_unsigned (snd (dmm m)).
Proof.
intros i m Hi Hb. pose proof (vm_bound (dmm m) (nth_error_In _ _ (vm_nth _ _ Hi))) as (P0 & _ & _ & _ & P4).
split; [exact P4|]. split; [|exact P0].
apply (vm_split i m Hi); intros ->;
[ rewrite (nth_ALLMAPS_tail 9 _ eq_refl) in Hi | rewrite (nth_ALLMAPS_tail 10 _ eq_refl) in Hi | rewrite (nth_ALLMAPS_tail 11 _ eq_refl) in Hi ];
injection Hi as <-; exact Hb.
Qed.
Lemma avis_sound : forall p, In p (a_vis ch) ->
(exists i m L, nth_error ALLMAPS i = Some m /\ match am_base m with ELit _ => False | _ => True end /\ am_len m = ELit L /\ 0 <= L < 2 ^ 64
/\ u (am_base m) <= u (fst p) /\ u (fst p) + u (snd p) <= u (am_base m) + L
/\ u (am_base m) + L <= ASAN_CEIL /\ (u (am_base m) + L <= 2147446784 \/ kHighMemBeg <= u (am_base m)) /\ 0 < L)
\/ p = RINFO_P \/ p = IMG_P \/ p = STK_P.
Proof.
intros p Hp. pose proof (proj1 (forallb_forall _ _) tfib_hole_avis p Hp) as Hok. unfold avis_ok in Hok.
apply orb_prop in Hok as [Hok|Hok]; [apply orb_prop in Hok as [Hok|Hok]; [apply orb_prop in Hok as [Hok|Hok]|]|].
- left. apply existsb_exists in Hok as (m & Hm0 & Hsub). rewrite tfib_hole_maps in Hm0. apply In_nth_error in Hm0 as (i & Hi). change (nth_error ALLMAPS i = Some m) in Hi.
destruct (sub_of_map_sound p m Hsub) as (Hb & L & HL & HLL & Hpp).
pose proof (map_facts i m Hi Hb) as (M1 & M2 & M3). unfold dmm, amap_den in M1, M2, M3. cbn [fst snd] in M1, M2, M3.
fold (u (am_base m)) in M1, M2, M3. fold (u (am_len m)) in M1, M2, M3. rewrite HL in M1, M2, M3. rewrite (uE_litv E L) in M1, M2, M3 by lia.
exists i, m, L. split; [exact Hi|]. split; [exact Hb|]. split; [exact HL|]. split; [exact HLL|].
assert (HR : u (am_base m) <= u (fst p) /\ u (fst p) + u (snd p) <= u (am_base m) + L).
{ destruct Hpp as [-> | (k & n & -> & Hk & Hn & Hkn)]; cbn [fst snd].
- rewrite (uE_litv E L) by lia. lia.
- pose proof ceil_le_TOP as CT. unfold YA02.TOP in CT. pose proof usp_range as [UU _].
rewrite (uE_litv E n) by lia. rewrite uE_add; rewrite (uE_litv E k) by lia; lia. }
destruct HR as [HR1 HR2]. repeat split; assumption.
- right. left. exact (pair_eqb_eq _ _ Hok).
- right. right. left. exact (pair_eqb_eq _ _ Hok).
- right. right. right. exact (pair_eqb_eq _ _ Hok).
Qed.
Lemma rinfo_val : u (fst RINFO_P) = u eSp1 + 137439019008 /\ u (snd RINFO_P) = 4096 /\ u eSp1 + 137439023104 <= ASAN_CEIL /\ u eP - 65535 <= u eSp1 <= u eP /\ kHighMemBeg <= u eP.
Proof.
pose proof uP as [_ HPr]. pose proof uSp1 as E1. pose proof (Z.mod_pos_bound (u eP) 65536 ltac:(lia)) as Hm. pose proof ceil_le_TOP as CT. unfold YA02.TOP in CT.
pose proof (map_facts (3 + length (musl_maps ch) + 6) (mk eP 137439023104 KRW) (nth_ALLMAPS_tail 6 _ eq_refl) I) as (X & _).
unfold dmm, amap_den in X. cbn [fst snd am_base am_len mk] in X. fold (u eP) in X. fold (u (ELit 137439023104)) in X. rewrite (uE_litv E 137439023104) in X by lia.
unfold RINFO_P. cbn [fst snd]. rewrite uE_add by (rewrite uE_litv; lia). rewrite !uE_litv by lia. unfold kHighMemBeg. lia.
Qed.
Lemma stk_val : u (fst STK_P) = usp - 8388608 /\ u (snd STK_P) = 140737496743936 - usp.
Proof.
pose proof uS0 as U0. pose proof usp_range as [UR _]. unfold STK_P. cbn [fst snd]. split; [rewrite uE_add_neglit; rewrite ?U0; lia|].
pose proof uSp0 as [F0 _]. rewrite U0 in F0. rng (EVar 0). rng (EVar 6). intros R6 R0. rewrite !uE_var in R0, R6.
set (e1 := EMd M_MUL (ELit (-32768)) (EVar 0)). set (e2 := EMd M_MUL (ELit (-16)) (EVar 6)).
assert (M1 : u e1 = (2 ^ 64 - 32768 * V 0) mod 2 ^ 64).
{ apply eqm_small_eq; [| apply uE_bound | apply Z.mod_pos_bound; lia]. subst e1. unfold uE. cbn [edenot].
eapply eqm_trans; [apply u_mul_eqm|]. eapply eqm_trans; [apply eqm_mul_r; apply eqm_u_lit|]. eapply eqm_trans; [|apply eqm_sym; apply eqm_mod]. exists (-1). lia. }
assert (M2 : u e2 = (2 ^ 64 - 16 * V 6) mod 2 ^ 64).
{ apply eqm_small_eq; [| apply uE_bound | apply Z.mod_pos_bound; lia]. subst e2. unfold uE. cbn [edenot].
eapply eqm_trans; [apply u_mul_eqm|]. eapply eqm_trans; [apply eqm_mul_r; apply eqm_u_lit|]. eapply eqm_trans; [|apply eqm_sym; apply eqm_mod]. exists (-1). lia. }
apply eqm_small_eq; [| apply uE_bound | lia].
eapply eqm_trans; [apply uE_add_eqm|]. eapply eqm_trans; [apply eqm_add; [apply uE_add_eqm | apply eqm_refl]|].
rewrite M1, M2, (uE_litv E 140737496743936) by lia. rewrite F0.
rewrite (Z.mod_small (2 ^ 64 - 32768 * V 0)) by lia.
destruct (Z.eq_dec (V 6) 0) as [Z6|Z6].
+ rewrite Z6, Z.mul_0_r, Z.sub_0_r, Z_mod_same_full. exists 1. lia.
+ rewrite (Z.mod_small (2 ^ 64 - 16 * V 6)) by lia. exists 2. lia.
Qed.
Lemma sliver_band : forall a, sliverb sp a = true ->
SHADOW_OFF + ASAN_CEIL / 8 <= bv_unsigned a < SHADOW_OFF + TOP / 8
/\ kHighShadowBeg <= bv_unsigned a < kHighShadowEnd /\ bv_unsigned a < TOP /\ TOP - 4095 <= ASAN_CEIL <= TOP.
Proof.
intros a H. unfold sliverb in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof usp_range as [U _]. pose proof ceil_le_TOP as C1. pose proof ceil_ge_TOP as [C2 _].
rewrite <- ceil_run in H1. unfold ASAN_CEIL, YA02.TOP in *.
unfold SHADOW_OFF, kHighShadowBeg, kHighShadowEnd in *. lia.
Qed.
Lemma sliver_not_allowed : forall a, sliverb sp a = true -> in_allow TFIB E ch (bv_unsigned a) = false.
Proof.
intros a Ha. pose proof (sliver_band a Ha) as (S1 & S2 & S3 & S4). set (z := bv_unsigned a) in *.
pose proof uP as [_ HPr]. pose proof uSp1 as E1. pose proof uSp as (Es & _ & Hs1 & Hs2). pose proof uS0 as U0. pose proof usp_range as [UR _].
pose proof (Z.mod_pos_bound (u eP) 65536 ltac:(lia)) as Hm.
assert (HPend : u eP + 137439023104 <= ASAN_CEIL).
{ pose proof (map_facts (3 + length (musl_maps ch) + 6) (mk eP 137439023104 KRW) (nth_ALLMAPS_tail 6 _ eq_refl) I) as (X & _).
unfold dmm, amap_den in X. cbn [fst snd am_base am_len mk] in X. fold (u eP) in X. change (edenot E (ELit 137439023104)) with (edenot E (ELit 137439023104)) in X.
pose proof (uE_litv E 137439023104 ltac:(lia)) as L. unfold uE in L. rewrite L in X. exact X. }
assert (NV : forall p, In p (a_vis ch) -> ~ (u (fst p) <= z < u (fst p) + u (snd p)) /\ ~ (sh_lo TFIB E p <= z < sh_hi TFIB E p)).
{ intros p Hp. pose proof (proj1 (forallb_forall _ _) tfib_hole_avis p Hp) as Hok. unfold avis_ok in Hok.
unfold sh_lo, sh_hi. change (shadow_off TFIB) with SHADOW_OFF.
apply orb_prop in Hok as [Hok|Hok]; [apply orb_prop in Hok as [Hok|Hok]; [apply orb_prop in Hok as [Hok|Hok]|]|].
-
apply existsb_exists in Hok as (m & Hm0 & Hsub). rewrite tfib_hole_maps in Hm0. apply In_nth_error in Hm0 as (i & Hi). change (nth_error ALLMAPS i = Some m) in Hi.
destruct (sub_of_map_sound p m Hsub) as (Hb & L & HL & HLL & Hpp).
pose proof (map_facts i m Hi Hb) as (M1 & M2 & M3). unfold dmm, amap_den in M1, M2, M3. cbn [fst snd] in M1, M2, M3.
fold (u (am_base m)) in M1, M2, M3. fold (u (am_len m)) in M1, M2, M3. rewrite HL in M1, M2, M3.
rewrite (uE_litv E L) in M1, M2, M3 by lia.
assert (HR : u (am_base m) <= u (fst p) /\ u (fst p) + u (snd p) <= u (am_base m) + L).
{ destruct Hpp as [-> | (k & n & -> & Hk & Hn & Hkn)]; cbn [fst snd].
- rewrite (uE_litv E L) by lia. lia.
- pose proof ceil_le_TOP as CT. unfold YA02.TOP in CT. pose proof usp_range as [UU _].
rewrite (uE_litv E n) by lia. rewrite uE_add; rewrite (uE_litv E k) by lia; lia. }
unfold kHighMemBeg, kHighShadowEnd, SHADOW_OFF in *. clear - S1 S2 M1 M2 M3 HR. split; [lia|].
intros [X1 X2]. assert (u (fst p) + u (snd p) <= ASAN_CEIL) by lia.
assert ((u (fst p) + u (snd p)) / 8 <= ASAN_CEIL / 8) by (apply Z.div_le_mono; lia). lia.
-
apply pair_eqb_eq in Hok. subst p. unfold RINFO_P. cbn [fst snd].
assert (L1 : u (EAlu ALU_ADD eSp1 (ELit 137439019008)) = u eSp1 + 137439019008).
{ pose proof ceil_le_TOP as CT; unfold YA02.TOP in CT. rewrite uE_add; rewrite uE_litv; lia. }
rewrite L1, (uE_litv E 4096) by lia.
unfold kHighMemBeg, kHighShadowEnd, SHADOW_OFF in *. clear - S1 S2 HPr E1 Hm HPend. split; [lia|].
intros [X1 X2]. assert ((u eSp1 + 137439019008 + 4096) / 8 <= ASAN_CEIL / 8) by (apply Z.div_le_mono; lia). lia.
-
apply pair_eqb_eq in Hok. subst p. unfold IMG_P. cbn [fst snd]. rewrite !uE_litv by lia. unfold kHighShadowBeg, SHADOW_OFF in S2 |- *. clear - S2. split; [lia|]. intros [X1 X2].
change ((65536 + 6205440) / 8) with 783872 in X2. lia.
-
apply pair_eqb_eq in Hok. subst p. unfold STK_P. cbn [fst snd].
assert (L1 : u (EAlu ALU_ADD eSp0 (ELit (-8388608))) = usp - 8388608) by (rewrite uE_add_neglit; rewrite ?U0; lia).
rewrite L1. unfold YA02.TOP in S1, S3. unfold SHADOW_OFF in S1 |- *. clear - S1 S3. split; [lia|]. intros [X1 X2]. lia. }
unfold in_allow, in_vis, in_sh. apply orb_false_intro; apply existsb_false_forall.
- intros p Hp. destruct (NV p Hp) as [N _]. apply andb_false_iff.
destruct (Z.leb_spec (u (fst p)) z); [right; apply Z.ltb_ge; lia | left; reflexivity].
- intros p Hp. destruct (NV p Hp) as [_ N]. apply andb_false_iff.
destruct (Z.leb_spec (sh_lo TFIB E p) z); [right; apply Z.ltb_ge; lia | left; reflexivity].
Qed.
Lemma sliver_high : forall a, sliverb sp a = true ->
in_ivs (bv_unsigned a) vm = true /\ in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false
/\ page_in_ranges (page_base a) (m_vm_lazy model) = true.
Proof.
intros a Ha. pose proof (sliver_band a Ha) as (_ & S2 & _). pose proof band_vals as (_ & _ & VH). unfold wzp in VH.
apply (f_equal fst) in VH as Y1. apply (f_equal snd) in VH as Y2. cbn [fst snd] in Y1, Y2.
assert (Hin : In (mk (ELit 2201439137792) 15392894357504 KRWLAZY) (a_maps ch)).
{ rewrite tfib_hole_maps. change (In (mk (ELit 2201439137792) 15392894357504 KRWLAZY) ALLMAPS). exact (nth_error_In _ _ (nth_ALLMAPS_tail 9 _ eq_refl)). }
pose proof (proj1 (Forall_forall _ _) (ho_kinds TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) _ Hin eq_refl a) as K.
cbn [am_base am_len mk] in K. change (edenot E (ELit 2201439137792)) with (fst dHigh) in K. change (edenot E (ELit 15392894357504)) with (snd dHigh) in K.
rewrite Y1, Y2 in K. unfold kHighShadowBeg, kHighShadowEnd in S2. destruct (K ltac:(lia)) as [K1 K2].
split; [| split; [exact K1 | exact K2]].
unfold in_ivs. apply existsb_exists. exists dHigh. split; [exact (vm_In _ (nth_error_In _ _ (nth_ALLMAPS_tail 9 _ eq_refl)))|].
rewrite Y1, Y2. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma sliver_hid : forall a, sliverb sp a = true -> HID a = true.
Proof.
intros a Ha. pose proof (sliver_band a Ha) as (_ & S2 & S3 & _). destruct (sliver_high a Ha) as (V1 & V2 & V3).
unfold hid. apply orb_true_intro. right. apply negb_true_iff. unfold vis.
rewrite V1, V2, V3, (sliver_not_allowed a Ha). cbn [negb andb orb].
replace (in_hull TFIB (bv_unsigned a)) with false
by (symmetry; unfold in_hull; change (img_lo TFIB) with 0x10000; change (img_hi TFIB) with 0x5fb000; unfold kHighShadowBeg in S2;
apply andb_false_iff; right; apply Z.ltb_ge; lia).
replace (TOP <=? bv_unsigned a) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.
Lemma tfib_band_not_ghost : forall z, 2147446784 <= z < 2147446784 + 17592186048512 -> in_ghost E ch z = false.
Proof.
intros z Hz. unfold in_ghost.
pose proof (ho_disj TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC _ _ _ _ tfib_hole_ghostdisj) as D.
unfold estart, elenZ in D. cbn [a_base a_off] in D. fold (u (ELit 2147446784)) in D. fold (u (ELit 17592186048512)) in D. fold (u (epg 358)) in D. fold (u (ELit 4096)) in D.
rewrite (uE_litv E 2147446784), (uE_litv E 17592186048512), (uE_litv E 4096) in D by lia.
assert (G1 : ((uE E (epg 358) <=? z) && (z <? uE E (epg 358) + uE E (ELit 4096)))%bool = false).
{ rewrite (uE_litv E 4096) by lia. apply andb_false_iff.
destruct (Z.leb_spec (u (epg 358)) z); [right; apply Z.ltb_ge; unfold u in *; lia | left; reflexivity]. }
destruct tfib_hole_ghost as [-> | [-> HB5]]; unfold TFIB_GHOST, BRK_GHOST; cbn [existsb app fst snd]; rewrite G1; cbn [orb]; [reflexivity|].
pose proof (ho_disj TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC _ _ _ _ HB5) as D5.
unfold estart, elenZ in D5. cbn [a_base a_off] in D5. fold (u (ELit 2147446784)) in D5. fold (u (ELit 17592186048512)) in D5. fold (u (epg 5)) in D5. fold (u (ELit 8192)) in D5.
rewrite (uE_litv E 2147446784), (uE_litv E 17592186048512), (uE_litv E 8192) in D5 by lia.
rewrite (uE_litv E 4096) by lia. apply orb_false_intro; [|reflexivity]. apply andb_false_iff.
destruct (Z.leb_spec (u (epg 5)) z); [right; apply Z.ltb_ge; unfold u in *; lia | left; reflexivity].
Qed.
Lemma sliver_zero : forall a, sliverb sp a = true -> FULL a = Some (Z_to_bv 8 0).
Proof.
intros a Ha. pose proof (sliver_band a Ha) as (_ & S2 & _). destruct (sliver_high a Ha) as (V1 & V2 & V3).
apply (ho_zero TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC a (sliver_hid a Ha) V1 V2 V3).
unfold kHighShadowBeg, kHighShadowEnd in S2. apply tfib_band_not_ghost. lia.
Qed.
Lemma sliver_allowed : forall a, sliverb sp a = true -> page_allowedb (allowA TFIB E ch) (page_base a) = true.
Proof.
intros a Ha. pose proof (sliver_band a Ha) as (S1 & S2 & S3 & S4). pose proof uS0 as U0. pose proof usp_range as [UR U16].
pose proof (pb_facts a) as (P1 & P2 & P3). pose proof ceil_ge_TOP as [_ CA].
unfold page_allowedb. apply existsb_exists. exists (pagedown (sh_lo TFIB E STK_P), pageup (sh_hi TFIB E STK_P)). split.
- unfold allowA. apply in_flat_map. exists STK_P. split; [apply in_app_iff; left; exact tfib_hole_stk|]. unfold allow1. right. left. reflexivity.
- cbn [fst snd]. unfold sh_lo, sh_hi. change (shadow_off TFIB) with SHADOW_OFF. unfold STK_P. cbn [fst snd].
assert (L1 : u (EAlu ALU_ADD eSp0 (ELit (-8388608))) = usp - 8388608) by (rewrite uE_add_neglit; rewrite ?U0; lia).
assert (L2 : u (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-32768)) (EVar 0)) (EMd M_MUL (ELit (-16)) (EVar 6))) (ELit 140737496743936)) = 140737496743936 - usp).
{ pose proof uSp0 as [F0 _]. rewrite U0 in F0. rng (EVar 0). rng (EVar 6). intros R6 R0. rewrite !uE_var in R0, R6.
set (e1 := EMd M_MUL (ELit (-32768)) (EVar 0)). set (e2 := EMd M_MUL (ELit (-16)) (EVar 6)).
assert (M1 : u e1 = (2 ^ 64 - 32768 * V 0) mod 2 ^ 64).
{ apply eqm_small_eq; [| apply uE_bound | apply Z.mod_pos_bound; lia]. subst e1. unfold uE. cbn [edenot].
eapply eqm_trans; [apply u_mul_eqm|]. eapply eqm_trans; [apply eqm_mul_r; apply eqm_u_lit|]. eapply eqm_trans; [|apply eqm_sym; apply eqm_mod]. exists (-1). lia. }
assert (M2 : u e2 = (2 ^ 64 - 16 * V 6) mod 2 ^ 64).
{ apply eqm_small_eq; [| apply uE_bound | apply Z.mod_pos_bound; lia]. subst e2. unfold uE. cbn [edenot].
eapply eqm_trans; [apply u_mul_eqm|]. eapply eqm_trans; [apply eqm_mul_r; apply eqm_u_lit|]. eapply eqm_trans; [|apply eqm_sym; apply eqm_mod]. exists (-1). lia. }
apply eqm_small_eq; [| apply uE_bound | lia].
eapply eqm_trans; [apply uE_add_eqm|]. eapply eqm_trans; [apply eqm_add; [apply uE_add_eqm | apply eqm_refl]|].
rewrite M1, M2, (uE_litv E 140737496743936) by lia. rewrite F0.
rewrite (Z.mod_small (2 ^ 64 - 32768 * V 0)) by lia.
destruct (Z.eq_dec (V 6) 0) as [Z6|Z6].
+ rewrite Z6, Z.mul_0_r, Z.sub_0_r, Z_mod_same_full. exists 1. lia.
+ rewrite (Z.mod_small (2 ^ 64 - 16 * V 6)) by lia. exists 2. lia. }
rewrite L1, L2. unfold pagedown, pageup. change page_size with 4096. unfold YA02.TOP in S1, S4.
pose proof (Z.div_mod (@ASAN_CEIL rc) 4096 ltac:(lia)) as DC. rewrite CA, Z.add_0_r in DC.
unfold SHADOW_OFF in *. clear - S1 S4 P1 P2 P3 DC UR. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.
Lemma sliver_where : forall a, sliverb sp a = true -> kHighShadowBeg <= bv_unsigned a < kHighShadowEnd /\ bv_unsigned a < TOP.
Proof. intros a Ha. pose proof (sliver_band a Ha) as (_ & S2 & S3 & _). split; [exact S2 | exact S3]. Qed.
Definition dP := dm eP 137439023104 KRW.       Definition dQ := dm eQ 8388608 KNONELAZY.   Definition dT := dm eT 4096 KRW.
Definition dF := dm eF 11571200 KRW.           Definition dNB := dm eNB 1048576 KRW.       Definition dSB := dm eSB 8388608 KRWLAZY.
Definition dGV := dm eGV 4096 KRW.   Definition dD := dm eD 4096 KRW.   Definition d292 := dm e292 4096 KRW.
Definition dC := dm eC 65536 KRW.    Definition d254 := dm e254 3727360 KRW. Definition d109 := dm e109 65536 KRW.
Definition HEAD3 : list (word * word) := [dGV; dSB; dNB].
Definition TAIL12 : list (word * word) := [dF; dD; d292; dC; dT; dQ; dP; d254; d109; dHigh; dGap; dLow].
Definition MUSL : list (word * word) := map dmm (musl_maps ch).
Lemma vm_shape : exists fog, (length fog <= 2)%nat /\ Forall (fun iv => bv_unsigned (snd iv) <= 8192) fog /\ vm = HEAD3 ++ fog ++ TAIL12.
Proof.
exists MUSL. pose proof hole_facts as (_ & ML & MOK & _). split; [unfold MUSL; rewrite length_map; exact ML|]. split.
- unfold MUSL. apply Forall_map. apply Forall_forall. intros m Hm.
destruct (musl_map_sound ch m (proj1 (Forall_forall _ _) MOK m Hm)) as (v & n & o & _ & Hl & Hn & _).
unfold dmm, amap_den. cbn [snd]. rewrite Hl. cbn [edenot]. rewrite u64_lit by lia. lia.
- rewrite vm_eq. unfold ALLMAPS. rewrite !map_app. reflexivity.
Qed.
Definition iv_eqb (a b : word * word) : bool := (bv_eqb (fst a) (fst b) && bv_eqb (snd a) (snd b))%bool.
Definition KNOWN : list (word * word) := [dP; dQ; dT; dF; dNB; dSB; dLow; dHigh; dGap; dC; dD].
Definition known (iv : word * word) : bool := existsb (iv_eqb iv) KNOWN.
Definition extra : list (Z * Z) := map wzp (List.filter (fun iv => negb (known iv)) vm).
Definition shz (z : Z * Z) : Z * Z := (shadow_addr (fst z), snd z / 8).
Definition VZ : list (Z * Z) := [(u eT, 4096); (u eC, 65536); (u eD, 4096); (u eSp + kRegionInfoOff, 4096)] ++ extra.
Definition VIS0 : list (Z * Z) := map shz VZ.
Definition HHc (ch0 : acs) : nat := if kn_mem (KWord (SA eNB 16) 8 (ELit (TFIB_HASH 0))) ch0 then 0%nat else 1%nat.
Definition HH : nat := HHc ch.
Definition TFIB_IMG : Z * Z := (0x10000, 0x5eb000).
Definition ly0 : alayout :=
ALayout (u eP) (u eSp) (u eQ) (u eT) (u eC) (u eF) (u eNB) (u eSB) (u eTop) ASAN_CEIL (2 ^ 47) TFIB_TSD (TFIB_TR0 HH) extra (u eD) VIS0 TFIB_IMG (fun _ => 0).
Lemma KNOWN_eq : KNOWN = [dP; dQ; dT; dF; dNB; dSB; dLow; dHigh; dGap; dC; dD].
Proof. reflexivity. Qed.
Lemma known_In : forall iv, In iv KNOWN -> known iv = true.
Proof.
intros iv H. unfold known. apply existsb_exists. exists iv. split; [exact H|]. unfold iv_eqb. rewrite !bv_eqb_refl. reflexivity.
Qed.
Lemma iv_eqb_eq : forall a b, iv_eqb a b = true -> a = b.
Proof.
intros [a1 a2] [b1 b2] H. unfold iv_eqb in H. cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
apply bv_eqb_eq in H1. apply bv_eqb_eq in H2. subst. reflexivity.
Qed.
Lemma known_false_neq : forall iv d, known iv = false -> In d KNOWN -> iv <> d.
Proof. intros iv d Hk Hd ->. rewrite (known_In d Hd) in Hk. discriminate Hk. Qed.
Lemma dm_vals :
wzp dP = (u eP, 137439023104) /\ wzp dQ = (u eQ, 8388608) /\ wzp dT = (u eT, 4096) /\ wzp dF = (u eF, 11571200)
/\ wzp dNB = (u eNB, 1048576) /\ wzp dSB = (u eSB, 8388608) /\ wzp dLow = (2147446784, 268435456)
/\ wzp dHigh = (2201439137792, 15392894357504) /\ wzp dGap = (2415882240, 2199023255552)
/\ wzp dGV = (u eGV, 4096) /\ wzp dD = (u eD, 4096) /\ wzp d292 = (u e292, 4096) /\ wzp dC = (u eC, 65536)
/\ wzp d254 = (u e254, 3727360) /\ wzp d109 = (u e109, 65536).
Proof.
unfold wzp, dP, dQ, dT, dF, dNB, dSB, dLow, dHigh, dGap, dGV, dD, d292, dC, d254, d109.
rewrite !u_fst_dm. rewrite !u_snd_dm by lia. rewrite !uE_litv by lia. repeat split; reflexivity.
Qed.
Lemma vm_In' : forall d, In d (HEAD3 ++ TAIL12) -> In d vm.
Proof.
intros d Hd. destruct vm_shape as (fog & _ & _ & ->). apply in_app_iff in Hd as [Hd|Hd]; apply in_app_iff; [left; exact Hd|].
right. apply in_app_iff. right. exact Hd.
Qed.
#[local] Ltac vin := apply vm_In'; cbn; tauto.
Lemma sep_tail : forall i j x y, (i < j)%nat -> nth_error TAIL12 i = Some x -> nth_error TAIL12 j = Some y -> iv_disjoint x y.
Proof.
intros i j x y Hij Hi Hj. destruct vm_shape as (fog & _ & _ & Hvm). pose proof Hseps as S0. rewrite Hvm in S0.
apply seps_app_inv in S0 as (_ & S0 & _). apply seps_app_inv in S0 as (_ & S0 & _). exact (seps_pair _ S0 i j x y Hij Hi Hj).
Qed.
Lemma sep_head_tail : forall x y, In x HEAD3 -> In y TAIL12 -> iv_disjoint x y.
Proof.
intros x y Hx Hy. destruct vm_shape as (fog & _ & _ & Hvm). pose proof Hseps as S0. rewrite Hvm in S0.
apply seps_app_inv in S0 as (_ & _ & X). apply X; [exact Hx|]. apply in_app_iff. right. exact Hy.
Qed.
Lemma sep_SB_NB : iv_disjoint dSB dNB.
Proof.
destruct vm_shape as (fog & _ & _ & Hvm). pose proof Hseps as S0. rewrite Hvm in S0.
apply seps_app_inv in S0 as (S0 & _ & _). exact (seps_pair _ S0 1 2 dSB dNB ltac:(lia) eq_refl eq_refl).
Qed.
Lemma statics_eq : static_extents ly0 = map wzp [dP; dQ; dT; dF; dNB; dSB] ++ [(u eC, 256); wzp dD; (ASAN_CEIL, 2 ^ 47 - ASAN_CEIL); TFIB_IMG].
Proof.
pose proof dm_vals as (VP & VQ & VT & VF & VNB & VSB & _ & _ & _ & _ & VD & _).
cbn [static_extents owned_extents ly0 ly_prim ly_Q ly_T ly_C ly_F ly_NB ly_SB ly_D ly_stk_lo ly_stk_hi ly_img map app].
rewrite VP, VQ, VT, VF, VNB, VSB, VD. reflexivity.
Qed.
Lemma zdisjoint_wzp : forall x y, iv_disjoint x y -> zdisjoint (wzp x) (wzp y).
Proof. intros x y H. exact H. Qed.
Lemma statics_disj : pairwise zdisjoint (static_extents ly0).
Proof.
pose proof ceil_le_TOP as CT. unfold YA02.TOP in CT.
rewrite statics_eq. apply pairwise_app.
- cbn [map pairwise]. pose proof sep_tail as ST. pose proof sep_head_tail as SHT.
repeat split; try exact I.
all: repeat (apply Forall_cons); try apply Forall_nil.
all: try (apply zdisjoint_wzp).
1: apply iv_disjoint_sym; apply (ST 5%nat 6%nat dQ dP); [lia|reflexivity|reflexivity].
1: apply iv_disjoint_sym; apply (ST 4%nat 6%nat dT dP); [lia|reflexivity|reflexivity].
1: apply iv_disjoint_sym; apply (ST 0%nat 6%nat dF dP); [lia|reflexivity|reflexivity].
1: apply iv_disjoint_sym; apply SHT; cbn; tauto.
1: apply iv_disjoint_sym; apply SHT; cbn; tauto.
1: apply iv_disjoint_sym; apply (ST 4%nat 5%nat dT dQ); [lia|reflexivity|reflexivity].
1: apply iv_disjoint_sym; apply (ST 0%nat 5%nat dF dQ); [lia|reflexivity|reflexivity].
1: apply iv_disjoint_sym; apply SHT; cbn; tauto.
1: apply iv_disjoint_sym; apply SHT; cbn; tauto.
1: apply iv_disjoint_sym; apply (ST 0%nat 4%nat dF dT); [lia|reflexivity|reflexivity].
1: apply iv_disjoint_sym; apply SHT; cbn; tauto.
1: apply iv_disjoint_sym; apply SHT; cbn; tauto.
1: apply iv_disjoint_sym; apply SHT; cbn; tauto.
1: apply iv_disjoint_sym; apply SHT; cbn; tauto.
1: apply iv_disjoint_sym; apply sep_SB_NB.
-   pose proof (vm_bound dC ltac:(vin)) as X. pose proof (vm_bound dD ltac:(vin)) as XD.
pose proof dm_vals as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VD & _ & VC & _).
pose proof (f_equal fst VC) as V1. pose proof (f_equal snd VC) as V2. cbn [fst snd wzp] in V1, V2.
pose proof (sep_tail 1%nat 3%nat dD dC ltac:(lia) eq_refl eq_refl) as DC. unfold iv_disjoint in DC. rewrite V1, V2 in DC.
rewrite V1, V2 in X. unfold TFIB_IMG.
cbn [pairwise map]. split; [| split; [| split; [| split; [apply Forall_nil | exact I]]]].
+ repeat (apply Forall_cons); try apply Forall_nil; unfold zdisjoint, wzp; cbn [fst snd]; clear - DC X; lia.
+ repeat (apply Forall_cons); try apply Forall_nil; unfold zdisjoint, wzp; cbn [fst snd]; clear - XD; lia.
+ repeat (apply Forall_cons); try apply Forall_nil; unfold zdisjoint; cbn [fst snd]. pose proof usp_range. pose proof ceil_ge_TOP as [CG _]. unfold YA02.TOP in CG. clear - CG H. lia.
- intros x y Hx Hy. apply in_map_iff in Hx as (d & <- & Hd).
assert (Hv : In d vm) by (destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; vin).
destruct Hy as [<-|[<-|[<-|[<-|[]]]]].
+
pose proof dm_vals as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VC & _).
assert (D : iv_disjoint d dC).
{ pose proof sep_tail as ST. pose proof sep_head_tail as SHT.
destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
- apply iv_disjoint_sym. apply (ST 3%nat 6%nat dC dP); [lia|reflexivity|reflexivity].
- apply iv_disjoint_sym. apply (ST 3%nat 5%nat dC dQ); [lia|reflexivity|reflexivity].
- apply iv_disjoint_sym. apply (ST 3%nat 4%nat dC dT); [lia|reflexivity|reflexivity].
- apply (ST 0%nat 3%nat dF dC); [lia|reflexivity|reflexivity].
- apply SHT; cbn; tauto.
- apply SHT; cbn; tauto. }
unfold iv_disjoint in D. pose proof (f_equal fst VC) as V1. pose proof (f_equal snd VC) as V2. cbn [fst snd wzp] in V1, V2. unfold zdisjoint, wzp. cbn [fst snd]. rewrite V1, V2 in D. lia.
+
assert (D : iv_disjoint d dD).
{ pose proof sep_tail as ST. pose proof sep_head_tail as SHT.
destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
- apply iv_disjoint_sym. apply (ST 1%nat 6%nat dD dP); [lia|reflexivity|reflexivity].
- apply iv_disjoint_sym. apply (ST 1%nat 5%nat dD dQ); [lia|reflexivity|reflexivity].
- apply iv_disjoint_sym. apply (ST 1%nat 4%nat dD dT); [lia|reflexivity|reflexivity].
- apply (ST 0%nat 1%nat dF dD); [lia|reflexivity|reflexivity].
- apply SHT; cbn; tauto.
- apply SHT; cbn; tauto. }
exact D.
+   pose proof (vm_bound d Hv). unfold zdisjoint, wzp. cbn [fst snd]. left. lia.
+   pose proof (vm_bound d Hv). unfold zdisjoint, wzp, TFIB_IMG. cbn [fst snd]. lia.
Qed.
#[local] Ltac kn_tac d := rewrite (known_In d) by (rewrite KNOWN_eq; cbn; tauto).
Lemma extra_len : (length extra <= 8)%nat.
Proof.
unfold extra. rewrite length_map. destruct vm_shape as (fog & Hlen & _ & ->).
rewrite !filter_app, !length_app.
assert (H1 : (length (List.filter (fun iv => negb (known iv)) HEAD3) <= 1)%nat).
{ unfold HEAD3. cbn [List.filter]. kn_tac dSB. kn_tac dNB. cbn [negb]. destruct (known dGV); cbn; lia. }
assert (H2 : (length (List.filter (fun iv => negb (known iv)) fog) <= 2)%nat).
{ pose proof (filter_length_le (fun iv => negb (known iv)) fog). lia. }
assert (H3 : (length (List.filter (fun iv => negb (known iv)) TAIL12) <= 3)%nat).
{ unfold TAIL12. cbn [List.filter]. kn_tac dF. kn_tac dD. kn_tac dC. kn_tac dT. kn_tac dQ. kn_tac dP. kn_tac dHigh. kn_tac dGap. kn_tac dLow. cbn [negb].
destruct (known d292), (known d254), (known d109); cbn; lia. }
lia.
Qed.
Lemma extra_In : forall e, In e extra -> exists iv, e = wzp iv /\ In iv vm /\ known iv = false.
Proof.
intros e H. unfold extra in H. apply in_map_iff in H as (iv & <- & Hiv). apply List.filter_In in Hiv as [H1 H2].
exists iv. split; [reflexivity|]. split; [exact H1|]. destruct (known iv); [discriminate H2 | reflexivity].
Qed.
Lemma unknown_small : forall iv, In iv vm -> known iv = false -> bv_unsigned (snd iv) <= 2 ^ 24 /\ 4096 <= bv_unsigned (fst iv).
Proof.
intros iv Hiv Hk. pose proof hole_facts as (_ & _ & MOK & _).
assert (NE : forall d, In d KNOWN -> iv <> d) by (intros d Hd; exact (known_false_neq iv d Hk Hd)).
pose proof uGV as [_ RGV]. pose proof u292 as [_ R292]. pose proof u254 as [_ R254]. pose proof u109 as [_ R109].
rewrite vm_eq in Hiv. unfold ALLMAPS in Hiv. rewrite !map_app in Hiv.
apply in_app_iff in Hiv as [Hh|Hiv]; [|apply in_app_iff in Hiv as [Hf|Ht]].
- cbn [map TFIB_HEAD3] in Hh. destruct Hh as [<-|[<-|[<-|[]]]].
+ change (dmm (mk eGV 4096 KRW)) with dGV. unfold dGV. rewrite u_snd_dm, u_fst_dm by lia. lia.
+ exfalso. apply (NE dSB); [rewrite KNOWN_eq; cbn; tauto | reflexivity].
+ exfalso. apply (NE dNB); [rewrite KNOWN_eq; cbn; tauto | reflexivity].
- apply in_map_iff in Hf as (m & <- & Hm). destruct (musl_map_sound ch m (proj1 (Forall_forall _ _) MOK m Hm)) as (v & n & o & Hb & Hl & Hn & Hr & Ho).
apply range_within in Hr. rewrite uE_var in Hr. unfold dmm, amap_den. cbn [fst snd]. rewrite Hb, Hl.
assert (Upg : u (epg v) = 4096 * V v) by (unfold epg; rewrite uE_mul_lit; rewrite ?uE_var; destruct Ho as [-> | ->]; change (0 / 4096) with 0 in Hr; change (4096 / 4096) with 1 in Hr; lia).
change (bv_unsigned (edenot E (ELit n))) with (u (ELit n)). rewrite (uE_litv E n) by lia.
change (bv_unsigned (edenot E (eoff (epg v) o))) with (u (eoff (epg v) o)).
destruct Ho as [-> | ->]; unfold eoff; cbn [Z.eqb]; change (0 / 4096) with 0 in Hr; change (4096 / 4096) with 1 in Hr.
+ lia.
+ rewrite uE_add; rewrite ?(uE_litv E 4096); lia.
- cbn [map TFIB_TAIL12] in Ht.
destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]];
first [ exfalso; apply (NE dF); [rewrite KNOWN_eq; cbn; tauto | reflexivity]
| exfalso; apply (NE dD); [rewrite KNOWN_eq; cbn; tauto | reflexivity]
| exfalso; apply (NE dC); [rewrite KNOWN_eq; cbn; tauto | reflexivity]
| exfalso; apply (NE dT); [rewrite KNOWN_eq; cbn; tauto | reflexivity]
| exfalso; apply (NE dQ); [rewrite KNOWN_eq; cbn; tauto | reflexivity]
| exfalso; apply (NE dP); [rewrite KNOWN_eq; cbn; tauto | reflexivity]
| exfalso; apply (NE dHigh); [rewrite KNOWN_eq; cbn; tauto | reflexivity]
| exfalso; apply (NE dGap); [rewrite KNOWN_eq; cbn; tauto | reflexivity]
| exfalso; apply (NE dLow); [rewrite KNOWN_eq; cbn; tauto | reflexivity]
| change (dmm (mk e292 4096 KRW)) with d292; unfold d292; rewrite u_snd_dm, u_fst_dm by lia; lia
| change (dmm (mk e254 3727360 KRW)) with d254; unfold d254; rewrite u_snd_dm, u_fst_dm by lia; lia
| change (dmm (mk e109 65536 KRW)) with d109; unfold d109; rewrite u_snd_dm, u_fst_dm by lia; lia ].
Qed.
Lemma extra_facts : Forall (fun e => YG0f.page_aligned (fst e) /\ 0 < snd e <= 2 ^ 24 /\ 4096 <= fst e /\ fst e + snd e <= ASAN_CEIL
/\ (fst e + snd e <= kLowShadowBeg \/ kHighMemBeg <= fst e)) extra.
Proof.
apply Forall_forall. intros e He. destruct (extra_In e He) as (iv & -> & Hiv & Hk).
pose proof (vm_bound iv Hiv) as (B1 & B2 & B3 & B4 & B5). destruct (unknown_small iv Hiv Hk) as [SZ LO].
assert (NE : forall d, In d KNOWN -> iv <> d) by (intros d Hd; exact (known_false_neq iv d Hk Hd)).
assert (BAND : bv_unsigned (fst iv) + bv_unsigned (snd iv) <= kLowShadowBeg \/ kHighMemBeg <= bv_unsigned (fst iv)).
{ assert (DL : iv_disjoint iv dLow).
{ destruct (seps_In_disjoint vm iv dLow Hseps Hiv ltac:(vin)) as [E0|D]; [exfalso; apply (NE dLow); [rewrite KNOWN_eq; cbn; tauto | exact E0] | exact D]. }
assert (DG : iv_disjoint iv dGap).
{ destruct (seps_In_disjoint vm iv dGap Hseps Hiv ltac:(vin)) as [E0|D]; [exfalso; apply (NE dGap); [rewrite KNOWN_eq; cbn; tauto | exact E0] | exact D]. }
assert (DH : iv_disjoint iv dHigh).
{ destruct (seps_In_disjoint vm iv dHigh Hseps Hiv ltac:(vin)) as [E0|D]; [exfalso; apply (NE dHigh); [rewrite KNOWN_eq; cbn; tauto | exact E0] | exact D]. }
unfold iv_disjoint in DL, DG, DH. unfold dLow, dGap, dHigh in DL, DG, DH.
rewrite !u_snd_dm in DL, DG, DH by lia. rewrite !u_fst_dm in DL, DG, DH. rewrite !uE_litv in DL, DG, DH by lia.
unfold kLowShadowBeg, kHighMemBeg. lia. }
unfold wzp, YG0f.page_aligned, kLowShadowBeg, kHighMemBeg in *. cbn [fst snd]. repeat split; lia.
Qed.
Lemma extra_disj : pairwise zdisjoint (extra ++ static_extents ly0).
Proof.
pose proof ceil_le_TOP as CT. unfold YA02.TOP in CT.
apply pairwise_app.
- unfold extra. apply seps_pairwise. apply seps_filter. exact Hseps.
- exact statics_disj.
- intros x y Hx Hy. destruct (extra_In x Hx) as (iv & -> & Hiv & Hk). rewrite statics_eq in Hy.
apply in_app_iff in Hy as [Hy|Hy].
+ apply in_map_iff in Hy as (d & <- & Hd).
assert (HdK : In d KNOWN) by (rewrite KNOWN_eq; cbn; cbn in Hd; tauto).
assert (Hdv : In d vm) by (destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; vin).
destruct (seps_In_disjoint vm iv d Hseps Hiv Hdv) as [E0|D]; [exfalso; exact (known_false_neq iv d Hk HdK E0)|].
exact D.
+ destruct Hy as [<-|[<-|[<-|[<-|[]]]]].
*
pose proof dm_vals as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VC & _).
destruct (seps_In_disjoint vm iv dC Hseps Hiv ltac:(vin)) as [E0|D]; [exfalso; exact (known_false_neq iv dC Hk ltac:(rewrite KNOWN_eq; cbn; tauto) E0)|].
unfold iv_disjoint in D. pose proof (f_equal fst VC) as V1. pose proof (f_equal snd VC) as V2. cbn [fst snd wzp] in V1, V2. rewrite V1, V2 in D. unfold zdisjoint, wzp. cbn [fst snd]. lia.
*
destruct (seps_In_disjoint vm iv dD Hseps Hiv ltac:(vin)) as [E0|D]; [exfalso; exact (known_false_neq iv dD Hk ltac:(rewrite KNOWN_eq; cbn; tauto) E0)|].
exact D.
* pose proof (vm_bound iv Hiv). unfold zdisjoint, wzp. cbn [fst snd]. left. lia.
* pose proof (vm_bound iv Hiv). unfold zdisjoint, wzp, TFIB_IMG. cbn [fst snd]. lia.
Qed.
Lemma VZ_facts : forall z, In z VZ -> In z (vis0_zones ly0) /\ fst z mod 8 = 0 /\ snd z mod 8 = 0 /\ 0 < snd z /\ 0 <= fst z.
Proof.
intros z Hz. pose proof uT as [HT HTr]. pose proof uC as [HCc HCr]. pose proof uD as [HD HDr]. pose proof uSp as (S1 & S2 & S3 & S4). pose proof uP as [_ HPr].
unfold VZ in Hz. apply in_app_iff in Hz as [Hz|Hz].
- destruct Hz as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd].
+ split; [unfold vis0_zones; cbn [ly0 ly_T]; left; reflexivity|]. rewrite HT. split; [replace (4096 * V 274) with ((512 * V 274) * 8) by lia; apply Z_mod_mult|]. repeat split; try reflexivity; lia.
+ split; [unfold vis0_zones; cbn [ly0 ly_C]; do 4 right; left; reflexivity|]. rewrite HCc. split; [replace (4096 * V 275) with ((512 * V 275) * 8) by lia; apply Z_mod_mult|]. repeat split; try reflexivity; lia.
+ split; [unfold vis0_zones; cbn [ly0 ly_D]; do 5 right; left; reflexivity|]. rewrite HD. split; [replace (4096 * V 357) with ((512 * V 357) * 8) by lia; apply Z_mod_mult|]. repeat split; try reflexivity; lia.
+ split; [unfold vis0_zones; cbn [ly0 ly_space]; do 7 right; left; reflexivity|]. unfold kRegionInfoOff.
split; [| repeat split; try reflexivity; lia]. apply Z.mod_divide in S2 as [q Hq]; [|lia]. rewrite Hq.
replace (q * 65536 + 2 ^ 37) with ((8192 * q + 2 ^ 34) * 8) by lia. apply Z_mod_mult.
- destruct (extra_In z Hz) as (iv & -> & Hiv & _). pose proof (vm_bound iv Hiv) as (B1 & B2 & B3 & B4 & B5). unfold wzp. cbn [fst snd].
split; [unfold vis0_zones; cbn [ly0 ly_extra]; apply in_app_iff; right; exact Hz|].
apply Z.mod_divide in B2 as [q Hq]; [|lia]. apply Z.mod_divide in B3 as [r Hr]; [|lia]. rewrite Hq, Hr.
split; [replace (q * 4096) with ((512 * q) * 8) by lia; apply Z_mod_mult|]. split; [replace (r * 4096) with ((512 * r) * 8) by lia; apply Z_mod_mult|].
pose proof (u64_range (fst iv)). lia.
Qed.
Lemma shz_cover : forall b len, b mod 8 = 0 -> len mod 8 = 0 -> 0 < len -> 0 <= b ->
shadow_addr b <= fst (shz (b, len)) /\ fst (shz (b, len)) + snd (shz (b, len)) <= shadow_addr (b + len - 1) + 1.
Proof.
intros b len Hb Hl Hp H0. unfold shz, shadow_addr. cbn [fst snd].
apply Z.mod_divide in Hb as [q Hq]; [|lia]. apply Z.mod_divide in Hl as [r Hr]; [|lia]. rewrite Hq, Hr.
replace (8 * q) with (q * 8) by lia. replace (8 * r) with (r * 8) by lia. rewrite !Z.div_mul by lia.
replace (q * 8 + r * 8 - 1) with ((q + r - 1) * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia.
Qed.
Lemma vis0_cover : Forall (fun v => Exists (fun z => shadow_addr (fst z) <= fst v /\ fst v + snd v <= shadow_addr (fst z + snd z - 1) + 1) (vis0_zones ly0)) (ly_vis0 ly0).
Proof.
cbn [ly_vis0 ly0]. unfold VIS0. apply Forall_forall. intros v Hv. apply in_map_iff in Hv as (z & <- & Hz).
destruct (VZ_facts z Hz) as (Hin & A1 & A2 & A3 & A4). apply Exists_exists. exists z. split; [exact Hin|].
destruct z as [b len]. exact (shz_cover b len A1 A2 A3 A4).
Qed.
Lemma uTopRel : usp - 160 <= u eTop <= usp + 3935 /\ ASAN_CEIL + 8388608 <= u eTop.
Proof.
pose proof uTop as (T1 & _). pose proof uSp0 as [S0 _]. rewrite uS0 in S0. pose proof ceil_le_TOP as CT. pose proof ceil_ge_TOP as [CG CA].
unfold YA02.TOP in CT, CG. rng (EVar 0). rng (EVar 6). pose proof u391 as R391. intros R6 R0. rewrite !uE_var in R0, R6.
pose proof (Z.div_mod (@ASAN_CEIL rc) 4096 ltac:(lia)) as DC. rewrite CA, Z.add_0_r in DC.
assert (TT : forall lo hi, kn_range_within ch eTopT lo hi = true -> 0 <= lo -> hi <= 4095 -> 0 <= 16 * V 6 - 4096 * V 391 + 3935 <= 4095).
{ intros lo hi Hk Hlo Hhi. apply range_within in Hk.
assert (Q : eqm (u eTopT) (16 * V 6 + (-4096) * V 391 + 3935)).
{ unfold eTopT. eapply eqm_trans; [apply uE_add_eqm|]. rewrite (uE_litv E 3935) by lia. apply eqm_add; [|apply eqm_refl].
eapply eqm_trans; [apply uE_add_eqm|]. apply eqm_add.
- rewrite uE_mul_lit by (rewrite ?uE_var; lia). rewrite uE_var. apply eqm_refl.
- unfold uE. cbn [edenot]. eapply eqm_trans; [apply u_mul_eqm|]. apply eqm_mul_r. apply eqm_u_lit. }
destruct Q as [q Hq]. pose proof (uE_bound E eTopT). assert (q = 0) by lia. subst q. lia. }
pose proof tfib_top_class as TC. unfold top_class in TC.
apply orb_prop in TC as [TC|TC]; [apply orb_prop in TC as [TC|TC]|];
apply andb_prop in TC as [TA TB]; apply range_within in TA; rewrite uE_var in TA.
- pose proof (TT 0 4095 TB ltac:(lia) ltac:(lia)). rewrite T1. lia.
- pose proof (TT 0 4095 TB ltac:(lia) ltac:(lia)). rewrite T1. lia.
- apply range_within in TB. rewrite uE_var in TB. rewrite T1. lia.
Qed.
Lemma tail_band : forall i m, nth_error TFIB_TAIL12 i = Some m -> (i < 9)%nat ->
bv_unsigned (fst (dmm m)) + bv_unsigned (snd (dmm m)) <= 2147446784 \/ kHighMemBeg <= bv_unsigned (fst (dmm m)).
Proof. intros i m Hi H9. apply (vm_split (3 + length (musl_maps ch) + i) m (nth_ALLMAPS_tail i m Hi)); lia. Qed.
Lemma head_band : forall i m, nth_error TFIB_HEAD3 i = Some m ->
bv_unsigned (fst (dmm m)) + bv_unsigned (snd (dmm m)) <= 2147446784 \/ kHighMemBeg <= bv_unsigned (fst (dmm m)).
Proof.
intros i m Hi. assert (i < 3)%nat by (destruct (Nat.lt_ge_cases i 3) as [?|G]; [assumption|]; rewrite (proj2 (nth_error_None _ _)) in Hi; [discriminate Hi | cbn; lia]).
apply (vm_split i m); [| lia | lia | lia]. unfold ALLMAPS. rewrite nth_error_app1 by (cbn; lia). exact Hi.
Qed.
Lemma tfib_layout_ok : layout_ok ly0.
Proof.
pose proof uP as [HP HPr]. pose proof uQ as [HQ HQr]. pose proof uT as [HT HTr]. pose proof uC as [HCc HCr].
pose proof uF as [HF HFr]. pose proof uNB as [HNB HNBr]. pose proof uSB as [HSB HSBr].
pose proof uSp as (S1 & S2 & S3 & S4). pose proof uTop as (T1 & T2 & T3 & T4). pose proof uD as [HD HDr]. pose proof uTopRel as [TR1 TR2].
pose proof ceil_le_TOP as CT. pose proof ceil_ge_TOP as [CG CA]. unfold YA02.TOP in CT, CG. pose proof usp_range as [UR _].
pose proof dm_vals as (VP & VQ & VT & VF & VNB & VSB & _ & _ & _ & _ & VD & _ & VC & _).
pose proof (sep_tail 3%nat 6%nat dC dP ltac:(lia) eq_refl eq_refl) as DCP. unfold iv_disjoint in DCP.
rewrite (f_equal fst VC : bv_unsigned (fst dC) = _), (f_equal snd VC : bv_unsigned (snd dC) = _), (f_equal fst VP : bv_unsigned (fst dP) = _), (f_equal snd VP : bv_unsigned (snd dP) = _) in DCP.
cbn [fst snd] in DCP.
pose proof (vm_bound dP ltac:(vin)) as BP. pose proof (vm_bound dQ ltac:(vin)) as BQ. pose proof (vm_bound dT ltac:(vin)) as BT.
pose proof (vm_bound dF ltac:(vin)) as BF. pose proof (vm_bound dNB ltac:(vin)) as BNB. pose proof (vm_bound dSB ltac:(vin)) as BSB.
pose proof (vm_bound dC ltac:(vin)) as BC. pose proof (vm_bound dD ltac:(vin)) as BD.
pose proof (tail_band 6 _ eq_refl ltac:(lia)) as AP. pose proof (tail_band 5 _ eq_refl ltac:(lia)) as AQ. pose proof (tail_band 4 _ eq_refl ltac:(lia)) as AT.
pose proof (tail_band 0 _ eq_refl ltac:(lia)) as AF. pose proof (tail_band 3 _ eq_refl ltac:(lia)) as AC. pose proof (tail_band 1 _ eq_refl ltac:(lia)) as AD.
pose proof (head_band 2 _ eq_refl) as ANB. pose proof (head_band 1 _ eq_refl) as ASB.
change (dmm (mk eP 137439023104 KRW)) with dP in AP. change (dmm (mk eQ 8388608 KNONELAZY)) with dQ in AQ. change (dmm (mk eT 4096 KRW)) with dT in AT.
change (dmm (mk eF 11571200 KRW)) with dF in AF. change (dmm (mk eC 65536 KRW)) with dC in AC. change (dmm (mk eD 4096 KRW)) with dD in AD.
change (dmm (mk eNB 1048576 KRW)) with dNB in ANB. change (dmm (mk eSB 8388608 KRWLAZY)) with dSB in ASB.
rewrite (f_equal fst VP : bv_unsigned (fst dP) = _), (f_equal snd VP : bv_unsigned (snd dP) = _) in BP, AP.
rewrite (f_equal fst VQ : bv_unsigned (fst dQ) = _), (f_equal snd VQ : bv_unsigned (snd dQ) = _) in BQ, AQ.
rewrite (f_equal fst VT : bv_unsigned (fst dT) = _), (f_equal snd VT : bv_unsigned (snd dT) = _) in BT, AT.
rewrite (f_equal fst VF : bv_unsigned (fst dF) = _), (f_equal snd VF : bv_unsigned (snd dF) = _) in BF, AF.
rewrite (f_equal fst VNB : bv_unsigned (fst dNB) = _), (f_equal snd VNB : bv_unsigned (snd dNB) = _) in BNB, ANB.
rewrite (f_equal fst VSB : bv_unsigned (fst dSB) = _), (f_equal snd VSB : bv_unsigned (snd dSB) = _) in BSB, ASB.
rewrite (f_equal fst VC : bv_unsigned (fst dC) = _), (f_equal snd VC : bv_unsigned (snd dC) = _) in BC, AC.
rewrite (f_equal fst VD : bv_unsigned (fst dD) = _), (f_equal snd VD : bv_unsigned (snd dD) = _) in BD, AD.
cbn [fst snd] in BP, BQ, BT, BF, BNB, BSB, BC, BD, AP, AQ, AT, AF, AC, AD, ANB, ASB.
assert (IA : Forall (fun e => in_app (fst e) (snd e)) (owned_extents ly0)).
{ unfold owned_extents, in_app, kLowShadowBeg, kHighMemBeg. cbn [ly0 ly_prim ly_Q ly_T ly_C ly_F ly_NB ly_SB ly_D].
unfold kPrimResvSize, kPtrArrayResv, kThreadObjSize, kFakeStackSize, kNodesBlockSize, kStoreBlockSize.
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
[ clear - BP AP HPr | clear - BQ AQ HQr | clear - BT AT HTr | clear - BF AF HFr | clear - BNB ANB HNBr | clear - BSB ASB HSBr
| clear - BC AC HCr | clear - BD AD HDr ]; unfold kHighMemBeg in *; lia. }
assert (LH : in_high (u eP) kPrimResvSize) by (unfold in_high, kHighMemBeg, kPrimResvSize; clear - BP HPr; lia).
clear AQ AT AF AC AD ANB ASB.
constructor; cbn [ly0 ly_prim ly_space ly_Q ly_T ly_C ly_F ly_NB ly_SB ly_top ly_stk_lo ly_stk_hi ly_tsd ly_tr0 ly_extra ly_D ly_vis0 ly_img ly_sec ly_bot
owned_extents fst snd];
unfold YG0f.page_aligned, in_high, kPrimResvSize, kSpaceSize, kPtrArrayResv, kThreadObjSize, kFakeStackSize,
kNodesBlockSize, kStoreBlockSize, kHighMemEnd, kStackSpan, TFIB_TSD, kCtxMapSize, TFIB_IMG.
- rewrite HP. rewrite Z.mul_comm. apply Z_mod_mult.
- exact S2.
- clear - S1 S2 S3 S4 HPr BP. lia.
- rewrite HQ. rewrite Z.mul_comm. apply Z_mod_mult.
- rewrite HT. rewrite Z.mul_comm. apply Z_mod_mult.
- rewrite HF. rewrite Z.mul_comm. apply Z_mod_mult.
- rewrite HNB. rewrite Z.mul_comm. apply Z_mod_mult.
- rewrite HSB. rewrite Z.mul_comm. apply Z_mod_mult.
- rewrite HCc. replace (4096 * V 275) with ((512 * V 275) * 8) by lia. apply Z_mod_mult.
- reflexivity.
-   exact LH.
-   exact IA.
-   unfold kImgLo, kImgEnd. cbn [fst snd]. clear. repeat split; try lia; try reflexivity; apply Z_mod_mult || (change 6205440 with (1482 * 4096); apply Z_mod_mult).
- exact statics_disj.
- unfold ly_bot. cbn [ly0 ly_top ly_stk_lo ly_stk_hi]. unfold kStackSpan, kHighMemBeg, kHighMemEnd. clear - TR1 TR2 T3 T4 CT CG CA UR. repeat split; try lia; try exact CA.
-   unfold HH, HHc. destruct (kn_mem _ ch); cbn; lia.
- split; [exact extra_len|]. split; [|exact extra_disj].
apply Forall_impl with (2 := extra_facts). clear. intros e He. unfold YG0f.page_aligned, kLowShadowBeg, kHighMemBeg in *. lia.
-   rewrite HD. rewrite Z.mul_comm. apply Z_mod_mult.
-   unfold zdisjoint. cbn [fst snd]. clear - DCP. lia.
-   exact vis0_cover.
-   clear. lia.
Qed.
Definition HS0 : word -> bool := fun a => (HID a && negb (sliverb sp a))%bool.
Lemma HS0_sub : hsub HS0 HID.
Proof. intros a Ha. unfold HS0 in Ha. apply andb_prop in Ha as [Ha _]. exact Ha. Qed.
Lemma HS0_off : H_off_segments TSEGS HS0.
Proof. intros a Ha. apply (ho_H_off TSEGS TFIB TOP argH tfib_in_hull TOPok tfib_hull_ok ARGH E ch model). exact (HS0_sub a Ha). Qed.
Definition rdS : reader := aview TSEGS HS0 FULL.
Lemma RDX : rd_ext rd rdS.
Proof. rewrite rd_aview. unfold rdS. apply aview_ext; [| exact HS0_sub]. exact (ho_H_off TSEGS TFIB TOP argH tfib_in_hull TOPok tfib_hull_ok ARGH E ch model). Qed.
Lemma rdS_sliver : forall z, sliverb sp (Z_to_bv 64 z) = true -> 0 <= z < 2 ^ 64 -> rdS z = Some 0.
Proof.
intros z Hs Hz. unfold rdS, aview, mbyte, mrestrict. unfold HS0. rewrite Hs. rewrite (sliver_hid _ Hs). cbn [andb negb].
rewrite (sliver_zero _ Hs). reflexivity.
Qed.
Lemma cell_ext : forall c, cell_holds B ly0 rd c -> cell_holds B ly0 rdS c.
Proof. intros c H. exact (proj1 (Forall_forall _ _) (Forall_cell_holds_ext B ly0 rd rdS _ RDX ltac:(constructor; [exact H | constructor])) c ltac:(left; reflexivity)). Qed.
Lemma rz_ext : forall r, range_zero B ly0 rd r -> range_zero B ly0 rdS r.
Proof. intros r H i Hi. exact (RDX _ _ (H i Hi)). Qed.
Lemma rv_ext : forall r, range_vis B ly0 rd r -> range_vis B ly0 rdS r.
Proof. intros r H i Hi X. destruct (rd (aeval B ly0 (fst r) + i)) as [v|] eqn:Ev; [| exact (H i Hi Ev)]. rewrite (RDX _ _ Ev) in X. discriminate X. Qed.
Definition xaddr (a : aexp) : option (expr * Z) :=
match a with
| ANum z => Some (ELit 0, z)
| ASp o => Some (eSp1, 65536 + o)
| AQ o => Some (eQ, o) | YG0f.AT o => Some (eT, o) | AC o => Some (eC, o) | AF o => Some (eF, o)
| ANB o => Some (eNB, o) | ASB o => Some (eSB, o) | ATop o => Some (eTop, o)
| ATsd o => Some (ELit 0, TFIB_TSD + o) | AInst o => Some (ELit 0, TFIB_INST + o) | ADepot o => Some (ELit 0, TFIB_DEPOT + o)
| AStore o => Some (ELit 0, TFIB_STORE + o) | ATp o => Some (ELit 0, TFIB_TP + o) | AIal o => Some (ELit 0, TFIB_IAL_LO + o)
| AD o => Some (eD, o)
| ASh (ANum z) => if 0 <=? z then Some (ELit 0, SHADOW_OFF + z / 8) else None
| ASh (AF o) => if ((0 <=? o) && (o mod 8 =? 0))%bool then Some (EMd M_MUL (ELit 512) (EVar 424), SHADOW_OFF + o / 8) else None
| _ => None
end.
Definition xval (v : aexp) : option expr :=
match v with
| ANum z => if ((0 <=? z) && (z <? 2 ^ 64))%bool then Some (ELit z) else None
| ASp o => if ((0 <=? 65536 + o) && (65536 + o <? 2 ^ 40))%bool then Some (EAlu ALU_ADD eSp1 (ELit (65536 + o))) else None
| AQ 0 => Some eQ | YG0f.AT 0 => Some eT | AC 0 => Some eC | AF 0 => Some eF | ANB 0 => Some eNB | ASB 0 => Some eSB
| ATop o => if o =? 0 then Some eTop else if ((- 2 ^ 40 <? o) && (o <? 0))%bool then Some (EAlu ALU_ADD eTop (ELit o)) else None
| ATsd 0 => Some (ELit TFIB_TSD)
| ATp 0 => Some (ELit TFIB_TP)
| AIal o => if ((0 <=? o) && (o <? 2 ^ 24))%bool then Some (ELit (TFIB_IAL_LO + o)) else None
| AD 0 => Some eD
| _ => None
end.
Definition xcell (ch0 : acs) (c : acell) : bool :=
match xaddr (c_at c), c_val c with
| Some (rb, rk), AV v =>
match xval v, kn_read TSEGS ch0 rb rk (c_w c) with
| Some e, Some e' => expr_eqb e' e
| _, _ => false
end
| _, _ => false
end.
Lemma xaddr_sound : forall a rb rk, xaddr a = Some (rb, rk) -> aeval B ly0 a = u rb + rk.
Proof.
pose proof uSp as (S1 & _). assert (L0 : u (ELit 0) = 0) by (apply uE_litv; lia).
intros a rb rk H; destruct a; cbn [xaddr] in H; try discriminate H;
try (injection H as <- <-; cbn [aeval ly0 ly_space ly_Q ly_T ly_C ly_F ly_NB ly_SB ly_top ly_tsd ly_D];
rewrite ?L0, ?(ts_inst B HB), ?(ts_depot B HB), ?(ts_store B HB), ?(ts_tp B HB), ?(ts_ial_lo B HB); lia).
destruct a; try discriminate H.
- destruct (0 <=? z) eqn:Hz; [|discriminate H]. injection H as <- <-. cbn [aeval]. unfold shadow_addr. rewrite L0. lia.
- destruct ((0 <=? off) && (off mod 8 =? 0))%bool eqn:Hb; [|discriminate H]. injection H as <- <-.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.eqb_eq in H2.
pose proof uF as [HF HFr]. cbn [aeval ly0 ly_F]. unfold shadow_addr. rewrite HF.
rewrite uE_mul_lit by (rewrite ?uE_var; lia). rewrite uE_var. apply Z.mod_divide in H2 as [q Hq]; [|lia]. rewrite Hq.
replace (4096 * V 424 + q * 8) with ((512 * V 424 + q) * 8) by lia. rewrite !Z.div_mul by lia. lia.
Qed.
Lemma xval_sound : forall v e, xval v = Some e -> aeval B ly0 v = u e.
Proof.
pose proof uSp as (S1 & _ & _ & _). pose proof uSp1 as P1. pose proof uP as [_ HP]. pose proof uTop as (_ & T1 & _ & _).
pose proof (Z.mod_pos_bound (u eP) 65536 ltac:(lia)) as Hm.
intros v e H; destruct v; cbn [xval] in H; try discriminate H.
- destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:Hb; [|discriminate H]. injection H as <-.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. cbn [aeval]. rewrite uE_litv by lia. reflexivity.
- destruct ((0 <=? 65536 + off) && (65536 + off <? 2 ^ 40))%bool eqn:Hb; [|discriminate H]. injection H as <-.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. cbn [aeval ly0 ly_space].
rewrite uE_add; rewrite ?uE_litv; lia.
- destruct off; try discriminate H. injection H as <-. cbn [aeval ly0 ly_Q]. lia.
- destruct off; try discriminate H. injection H as <-. cbn [aeval ly0 ly_T]. lia.
- destruct off; try discriminate H. injection H as <-. cbn [aeval ly0 ly_C]. lia.
- destruct off; try discriminate H. injection H as <-. cbn [aeval ly0 ly_F]. lia.
- destruct off; try discriminate H. injection H as <-. cbn [aeval ly0 ly_NB]. lia.
- destruct off; try discriminate H. injection H as <-. cbn [aeval ly0 ly_SB]. lia.
- cbn [aeval ly0 ly_top]. destruct (off =? 0) eqn:E0.
+ injection H as <-. apply Z.eqb_eq in E0. subst off. lia.
+ destruct ((- 2 ^ 40 <? off) && (off <? 0))%bool eqn:Hb; [|discriminate H]. injection H as <-.
apply andb_prop in Hb as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. rewrite uE_add_neglit; lia.
- destruct off; try discriminate H. injection H as <-. cbn [aeval ly0 ly_tsd]. rewrite uE_litv; [lia|]. unfold TFIB_TSD. lia.
- destruct off; try discriminate H. injection H as <-. cbn [aeval]. rewrite (ts_tp B HB). rewrite uE_litv; [lia|]. unfold TFIB_TP. lia.
- destruct ((0 <=? off) && (off <? 2 ^ 24))%bool eqn:Hb; [|discriminate H]. injection H as <-.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. cbn [aeval]. rewrite (ts_ial_lo B HB).
rewrite uE_litv; [lia|]. unfold TFIB_IAL_LO. lia.
- destruct off; try discriminate H. injection H as <-. cbn [aeval ly0 ly_D]. lia.
Qed.
Lemma le_byte_small : forall z w k, 0 <= z < 2 ^ (8 * Z.of_nat w) -> le_byte z w k = (z / 2 ^ (8 * Z.of_nat k)) mod 256.
Proof.
intros z w k Hz. unfold le_byte. rewrite (Z.mod_small z) by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma xcell_sound : forall c, xcell ch c = true -> cell_holds B ly0 rd c.
Proof.
intros [a w v] H. unfold xcell in H. cbn [c_at c_val c_w] in H.
destruct (xaddr a) as [[rb rk]|] eqn:Ha; [|discriminate H]. destruct v as [v|mask vv]; [|discriminate H].
destruct (xval v) as [e|] eqn:Hv; [|discriminate H]. destruct (kn_read TSEGS ch rb rk w) as [e'|] eqn:Hr; [|discriminate H].
apply expr_eqb_eq in H. subst e'.
unfold cell_holds. cbn [c_at c_val c_w]. intros k Hk.
rewrite (xaddr_sound _ _ _ Ha), (xval_sound _ _ Hv). unfold rd. rewrite (Hbyte _ _ _ _ Hr k Hk).
f_equal. symmetry. apply le_byte_small.
exact (ho_read_bound TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC _ _ _ _ Hr).
Qed.
Let Hzc := ho_zcover_range TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC TFIB_BSS tfib_bss_rom.
Let Hvis := ho_vis_range TSEGS TFIB LIM TOP SINV argH (in_fs inp) tfib_in_hull tfib_hull_ok E ch R FULL model HC.
Definition xzero (ch0 : acs) (r : aexp * Z) : bool :=
match xaddr (fst r) with
| Some (rb, rk) => ((0 <=? snd r) && (snd r <? 2 ^ 62) && (kn_zero ch0 rb rk (snd r) || kn_zcover TFIB_BSS ch0 rb rk (snd r)))%bool
| None => false
end.
Lemma xzero_sound : forall r, xzero ch r = true -> range_zero B ly0 rd r.
Proof.
intros [a len] H. unfold xzero in H. cbn [fst snd] in H.
destruct (xaddr a) as [[rb rk]|] eqn:Ha; [|discriminate H].
apply andb_prop in H as [Hl H]. apply andb_prop in Hl as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
intros i Hi. cbn [fst snd] in Hi |- *. rewrite (xaddr_sound _ _ _ Ha). unfold rd.
apply orb_prop in H as [H|H].
- exact (ho_zero_range TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC rb rk len ltac:(lia) H i Hi).
- exact (Hzc _ _ _ H i Hi).
Qed.
Definition ximg (rb : expr) (rk len : Z) : bool := (expr_eqb rb (ELit 0) && (0x9d000 <=? rk) && (rk + len <=? 0x5fb000))%bool.
Definition xvis (ch0 : acs) (r : aexp * Z) : bool :=
(xzero ch0 r || match xaddr (fst r) with
| Some (rb, rk) => kn_vis TFIB ch0 rb rk (snd r) || ximg rb rk (snd r)
| None => false
end)%bool.
Lemma ximg_sound : forall rb rk len, ximg rb rk len = true -> forall i, 0 <= i < len -> rd (u rb + rk + i) <> None.
Proof.
intros rb rk len H i Hi. unfold ximg in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply expr_eqb_eq in H1. subst rb. apply Z.leb_le in H2. apply Z.leb_le in H3. rewrite uE_litv by lia.
unfold rd. apply hreader_rom. apply tfib_rw_rom. lia.
Qed.
Lemma xvis_sound : forall r, xvis ch r = true -> range_vis B ly0 rd r.
Proof.
intros [a len] H. unfold xvis in H. apply orb_prop in H as [H|H].
- apply range_vis_of_zero. apply xzero_sound. exact H.
- cbn [fst snd] in H. destruct (xaddr a) as [[rb rk]|] eqn:Ha; [|discriminate H].
intros i Hi. cbn [fst snd] in Hi |- *. rewrite (xaddr_sound _ _ _ Ha).
apply orb_prop in H as [H|H].
+ unfold rd. exact (Hvis _ _ _ H i Hi).
+ exact (ximg_sound _ _ _ H i Hi).
Qed.
Definition IF_ZERO : list (aexp * Z) :=
[ (ASp kRegionInfoOff, 4096); (YG0f.AT t_qc, kThreadObjSize - t_qc); (AF 0, 88); (AF 96, kFakeFramesOff - 96);
(AIal 0, TFIB_IAL_HI - TFIB_IAL_LO); (ANum TFIB_IAL_FLAG, 2);
(AInst o_sec_reserved, 16); (AInst o_sec_mutex, 1); (AInst o_q_cmutex, 2); (AInst o_q_size, 32) ].
Definition IF_VIS : list (aexp * Z) :=
[ (YG0f.AT 0, kThreadObjSize); (AF 0, kFakeStackSize); (AInst 0, 3632); (ANum TFIB_OOM, 1); (ADepot d_nuniq, 32); (AStore 0, 32);
(ANB 0, kNodesBlockSize); (ASB 0, kStoreBlockSize); (ASh (AF kFakeFramesOff), (kFakeStackSize - kFakeFramesOff) / 8) ].
Definition IF_CELLS : list acell :=
[ z8 (AF 88) kStackSizeLog; z4 (ADepot d_nuniq) 1; c8 (ADepot d_map1) (ANB 0); c8 (AStore s_block0) (ASB 0); z4 (ANB 24) 0 ].
Definition TFIB_BUCKET (hh : nat) : Z := (TFIB_HASH hh) mod d_tab_words.
Definition IF_CELLS_H (hh : nat) : list acell :=
[ z8 (AStore s_total) (Z.of_nat (length (TFIB_TR0 hh)) + 1); z8 (ANB 16) (TFIB_HASH hh); z4 (ADepot (4 * TFIB_BUCKET hh)) 1 ].
Definition IF_ZERO_H (hh : nat) : list (aexp * Z) :=
[ (ADepot 0, 4 * TFIB_BUCKET hh); (ADepot (4 * TFIB_BUCKET hh + 4), 4 * (d_tab_words - TFIB_BUCKET hh - 1)) ].
Definition sh_range (r : Z * Z) : aexp * Z := (ANum (SHADOW_OFF + fst r / 8), snd r / 8).
Definition IF_ZSH_IMG : list (aexp * Z) := map sh_range Tfib_zero_shadow.
Definition TFIB_CONST : list acell := Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow.
Definition zcovered (z w : Z) : bool := existsb (fun r : Z * Z => (fst r <=? z) && (z + w <=? fst r + snd r))%bool Tfib_owned_static.
Definition zshcovered (z w : Z) : bool :=
existsb (fun r : Z * Z => (shadow_addr (fst r) <=? z) && (z + w <=? shadow_addr (fst r) + (snd r + 7) / 8))%bool Tfib_owned_static.
Definition xowned (c : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w c)) in
match c_at c with
| ANum z => zcovered z w || zshcovered z w
| ATp o => zcovered (TFIB_TP + o) w
| ATsd o => zcovered (TFIB_TSD + o) w
| AInst o => zcovered (TFIB_INST + o) w
| ADepot o => zcovered (TFIB_DEPOT + o) w
| AStore o => zcovered (TFIB_STORE + o) w
| YG0f.AT o => (0 <=? o) && (o + w <=? kThreadObjSize)
| AC o => (0 <=? o) && (o + w <=? 256)
| AQ o => (0 <=? o) && (o + w <=? kPtrArrayResv)
| ANB o => (0 <=? o) && (o + w <=? kNodesBlockSize)
| ASB o => (0 <=? o) && (o + w <=? kStoreBlockSize)
| AD o => (0 <=? o) && (o + w <=? 4096)
| _ => false
end%bool.
Definition STKZ_A : saddr := SA (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 2) (EVar 6))) 2146402304.
Definition STKZ_N : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-2)) (EVar 6))) (ELit 17592187092992).
Definition if_chk (ch0 : acs) : bool :=
forallb (xzero ch0) IF_ZERO && forallb (xvis ch0) IF_VIS && forallb (xcell ch0) IF_CELLS && forallb (xzero ch0) IF_ZSH_IMG
&& forallb (xcell ch0) (IF_CELLS_H (HHc ch0)) && forallb (xzero ch0) (IF_ZERO_H (HHc ch0))
&& forallb (xcell ch0) TFIB_CONST
&& kn_mem (KZero STKZ_A STKZ_N) ch0.
Lemma tfib_holes_if : forallb if_chk HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma xowned_all : forallb xowned TFIB_CONST = true.
Proof. vm_compute. reflexivity. Qed.
Lemma static_img_chk : forallb (fun r : Z * Z => (0x10000 <=? fst r) && (fst r + snd r <=? 0x10000 + 0x5eb000))%bool (Tfib_owned_static ++ Tfib_zero_shadow) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma zcovered_sound : forall z w k, zcovered z w = true -> 0 <= k < w -> Exists (in_zr (z + k)) (as_owned_static B).
Proof.
intros z w k H Hk. rewrite (ts_owned B HB). unfold zcovered in H. apply existsb_exists in H as (r & Hr & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
apply Exists_exists. exists r. split; [exact Hr|]. unfold in_zr. lia.
Qed.
Lemma zshcovered_sound : forall z w k, zshcovered z w = true -> 0 <= k < w ->
Exists (fun r => in_zr (z + k) (shadow_addr (fst r), (snd r + 7) / 8)) (as_owned_static B).
Proof.
intros z w k H Hk. rewrite (ts_owned B HB). unfold zshcovered in H. apply existsb_exists in H as (r & Hr & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
apply Exists_exists. exists r. split; [exact Hr|]. unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma xowned_sound : forall c, xowned c = true -> cell_owned B ly0 c.
Proof.
intros c H k Hk. unfold xowned in H. unfold owned_core.
destruct (c_at c) as [z|o|o|o|o|o|o|o|r o|o|o|o|o|o|o|o|o|o|e] eqn:Ea; cbn [aeval]; try discriminate H;
cbn [ly0 ly_Q ly_T ly_C ly_NB ly_SB ly_tsd ly_D];
first [ apply orb_prop in H as [H|H]; [left; apply (zcovered_sound _ _ k H Hk) | right; right; apply (zshcovered_sound _ _ k H Hk)]
| left; apply (zcovered_sound _ _ k H Hk)
| left; rewrite (ts_tp B HB); apply (zcovered_sound _ _ k H Hk)
| left; replace (TFIB_TSD + o + k) with (TFIB_TSD + o + k) by lia; apply (zcovered_sound _ _ k H Hk)
| left; rewrite (ts_inst B HB); apply (zcovered_sound _ _ k H Hk)
| left; rewrite (ts_depot B HB); apply (zcovered_sound _ _ k H Hk)
| left; rewrite (ts_store B HB); apply (zcovered_sound _ _ k H Hk)
| right; left; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2;
unfold core_extents; cbn [ly0 ly_Q ly_T ly_C ly_NB ly_SB ly_D]; unfold in_zr;
repeat (first [ apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl ]) ].
Qed.
Lemma tfib_const_eq : as_const B ly0 = TFIB_CONST.
Proof. rewrite (ts_const B HB ly0). reflexivity. Qed.
Lemma tfib_const_owned : Forall (cell_owned B ly0) (as_const B ly0).
Proof.
rewrite tfib_const_eq. apply Forall_forall. intros c Hc. apply xowned_sound. exact (proj1 (forallb_forall _ _) xowned_all c Hc).
Qed.
#[local] Ltac find_in := cbn; repeat (first [ left; reflexivity | right ]).
Lemma cell_rd32 : forall rdx a v, cell_holds B ly0 rdx (z4 a v) -> rd32 rdx (aeval B ly0 a) v.
Proof. intros rdx a v H k Hk. exact (H k Hk). Qed.
Lemma cell_rd64 : forall rdx a v, cell_holds B ly0 rdx (z8 a v) -> rd64 rdx (aeval B ly0 a) v.
Proof. intros rdx a v H k Hk. exact (H k Hk). Qed.
Lemma IFC : if_chk ch = true.
Proof. exact (proj1 (forallb_forall _ _) tfib_holes_if ch (HS_tfib_In h ch Hch)). Qed.
Lemma HH2 : (HH < 2)%nat.
Proof. unfold HH, HHc. destruct (kn_mem _ ch); lia. Qed.
Lemma HSZ : kn_mem (KZero STKZ_A STKZ_N) ch = true.
Proof. pose proof IFC as H. unfold if_chk in H. apply andb_prop in H as [_ H]. exact H. Qed.
Lemma stack_zero : zero_shadow rdS SHADOW_OFF ASAN_CEIL (2 ^ 47 - ASAN_CEIL).
Proof.
pose proof usp_range as [UR U16]. pose proof ceil_le_TOP as CT. pose proof ceil_ge_TOP as [CG CA]. unfold YA02.TOP in CT, CG.
pose proof (Z.div_mod (@ASAN_CEIL rc) 4096 ltac:(lia)) as DC. rewrite CA, Z.add_0_r in DC.
pose proof uSp0 as [F0 _]. rewrite uS0 in F0. rng (EVar 0). rng (EVar 6). intros R6 R0. rewrite !uE_var in R0, R6.
pose proof (ho_zero_at TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC _ _ HSZ) as KZ.
assert (EA : estart E STKZ_A = SHADOW_OFF + (usp - 8388608) / 8).
{ unfold estart, STKZ_A. cbn [a_base a_off]. fold (u (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 2) (EVar 6)))).
rewrite uE_add by (rewrite !uE_mul_lit; rewrite ?uE_var; lia). rewrite !uE_mul_lit by (rewrite ?uE_var; lia). rewrite !uE_var.
unfold SHADOW_OFF. rewrite F0. replace (32768 * V 0 + 16 * V 6 - 8388608) with ((4096 * V 0 + 2 * V 6 - 1048576) * 8) by lia.
rewrite Z.div_mul by lia. lia. }
assert (EN : elenZ E STKZ_N = 17592187092992 - usp / 8).
{ unfold elenZ, STKZ_N. fold (u STKZ_N). rewrite F0.
replace (32768 * V 0 + 16 * V 6) with ((4096 * V 0 + 2 * V 6) * 8) by lia. rewrite Z.div_mul by lia.
apply eqm_small_eq; [| apply uE_bound | lia].
unfold STKZ_N. eapply eqm_trans; [apply uE_add_eqm|]. rewrite (uE_litv E 17592187092992) by lia.
replace (17592187092992 - (4096 * V 0 + 2 * V 6)) with (((-4096) * V 0 + (-2) * V 6) + 17592187092992) by lia.
apply eqm_add; [|apply eqm_refl]. eapply eqm_trans; [apply uE_add_eqm|]. apply eqm_add;
(unfold uE; cbn [edenot]; eapply eqm_trans; [apply u_mul_eqm|]; apply eqm_mul_r; apply eqm_u_lit). }
intros i Hi. unfold shadow_of_addr.
set (z := SHADOW_OFF + ASAN_CEIL / 8 + i).
assert (Hz : SHADOW_OFF + ASAN_CEIL / 8 <= z < SHADOW_OFF + 2 ^ 47 / 8) by (subst z; unfold SHADOW_OFF in *; lia).
destruct (Z.lt_ge_cases z (SHADOW_OFF + (usp - 8388608) / 8)) as [Hlt|Hge].
-   apply rdS_sliver; [| unfold SHADOW_OFF in *; lia].
unfold sliverb. rewrite u64_lit by (unfold SHADOW_OFF in *; lia). rewrite <- ceil_run. change (@alloc_ceiling rc) with (@ASAN_CEIL rc).
apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
-   apply (RDX z 0). unfold rd, hreader, mbyte.
replace z with (estart E STKZ_A + (z - estart E STKZ_A)) by lia.
rewrite (KZ (z - estart E STKZ_A)) by (rewrite EN; unfold SHADOW_OFF in *; lia). reflexivity.
Qed.
Lemma tfib_init_facts : init_facts B ly0 rdS.
Proof.
pose proof IFC as H. unfold if_chk in H. apply andb_prop in H as [H _].
apply andb_prop in H as [H FK]. apply andb_prop in H as [H FZH]. apply andb_prop in H as [H FCH]. apply andb_prop in H as [H FS].
apply andb_prop in H as [H FC]. apply andb_prop in H as [FZ FV]. fold HH in FCH, FZH.
assert (Z0 : forall r, In r IF_ZERO -> range_zero B ly0 rdS r) by (intros r Hr; apply rz_ext; apply xzero_sound; exact (proj1 (forallb_forall _ _) FZ r Hr)).
assert (V0 : forall r, In r IF_VIS -> range_vis B ly0 rdS r) by (intros r Hr; apply rv_ext; apply xvis_sound; exact (proj1 (forallb_forall _ _) FV r Hr)).
assert (C0 : forall c, In c IF_CELLS -> cell_holds B ly0 rdS c) by (intros c Hc; apply cell_ext; apply xcell_sound; exact (proj1 (forallb_forall _ _) FC c Hc)).
assert (CH : forall c, In c (IF_CELLS_H HH) -> cell_holds B ly0 rdS c) by (intros c Hc; apply cell_ext; apply xcell_sound; exact (proj1 (forallb_forall _ _) FCH c Hc)).
assert (ZH : forall r, In r (IF_ZERO_H HH) -> range_zero B ly0 rdS r) by (intros r Hr; apply rz_ext; apply xzero_sound; exact (proj1 (forallb_forall _ _) FZH r Hr)).
pose proof (Z.mod_pos_bound (TFIB_HASH HH) d_tab_words ltac:(unfold d_tab_words; lia)) as HB1.
constructor.
- exact (ts_universe B HB).
- exact (ts_ok B HB).
- exact tfib_layout_ok.
- rewrite tfib_const_eq. apply Forall_forall. intros c Hc. apply cell_ext. apply xcell_sound. exact (proj1 (forallb_forall _ _) FK c Hc).
- exact tfib_const_owned.
- apply Z0. find_in.
- apply Z0. find_in.
- apply V0. find_in.
- apply Z0. find_in.
- apply Z0. find_in.
- apply C0. find_in.
- apply V0. find_in.
- rewrite (ts_ial_hi B HB), (ts_ial_lo B HB). apply Z0. find_in.
- rewrite (ts_ial_flag B HB). apply Z0. find_in.
- apply Z0. find_in.
- apply Z0. find_in.
- apply Z0. find_in.
- apply Z0. find_in.
- apply V0. find_in.
- rewrite (ts_oom B HB). apply V0. find_in.
- apply C0. find_in.
- apply C0. find_in.
- apply V0. find_in.
- cbn [ly_tr0 ly0]. apply CH. find_in.
- apply C0. find_in.
- apply V0. find_in.
- apply V0. find_in.
- apply V0. find_in.
-
exists (TFIB_BUCKET HH). cbn [ly_tr0 ly0]. rewrite (ts_hash B HB HH HH2). split; [exact HB1|]. split; [reflexivity|]. split.
+ pose proof (cell_rd32 rdS (ADepot (4 * TFIB_BUCKET HH)) 1 (CH (z4 (ADepot (4 * TFIB_BUCKET HH)) 1) ltac:(find_in))) as X. cbn [aeval] in X. exact X.
+ intros b Hb Hne k Hk. rewrite le_byte_0.
destruct (Z.lt_ge_cases b (TFIB_BUCKET HH)) as [Hl|Hg].
* pose proof (ZH (ADepot 0, 4 * TFIB_BUCKET HH) ltac:(find_in) (4 * b + Z.of_nat k) ltac:(cbn [snd]; lia)) as X.
cbn [fst aeval] in X. rewrite <- X. f_equal. lia.
* unfold TFIB_BUCKET in Hg, Hne.
pose proof (ZH (ADepot (4 * TFIB_BUCKET HH + 4), 4 * (d_tab_words - TFIB_BUCKET HH - 1)) ltac:(find_in)
(4 * b + Z.of_nat k - (4 * TFIB_BUCKET HH + 4)) ltac:(cbn [snd]; unfold TFIB_BUCKET; lia)) as X.
cbn [fst aeval] in X. rewrite <- X. f_equal. unfold TFIB_BUCKET. lia.
-
cbn [ly_tr0 ly_NB ly0]. rewrite (ts_hash B HB HH HH2). split.
+ pose proof (cell_rd64 rdS (ANB 16) (TFIB_HASH HH) (CH (z8 (ANB 16) (TFIB_HASH HH)) ltac:(find_in))) as X. cbn [aeval ly_NB ly0] in X. exact X.
+ pose proof (cell_rd32 rdS (ANB 24) 0 (C0 (z4 (ANB 24) 0) ltac:(find_in))) as X. cbn [aeval ly_NB ly0] in X.
replace (u eNB + 16 + 8) with (u eNB + 24) by lia. exact X.
-
apply Forall_forall. intros r Hr. destruct (ts_junk B HB ly0 r Hr) as (z & Hz & H1 & H2).
apply rv_ext. intros i Hi. destruct r as [ra rl]. cbn [fst snd] in Hz, Hi, H2 |- *. subst ra. cbn [aeval].
unfold rd. apply hreader_rom. apply tfib_rw_rom. lia.
-
unfold zshadow_ok, zero_shadow_ranges. rewrite (ts_zsh B HB). cbn [ly_stk_lo ly_stk_hi ly0].
apply Forall_cons; [exact stack_zero|].
apply Forall_forall. intros r Hr i Hi.
assert (Hx : xzero ch (sh_range r) = true).
{ apply (proj1 (forallb_forall _ _) FS). unfold IF_ZSH_IMG. apply in_map. exact Hr. }
pose proof (rz_ext _ (xzero_sound _ Hx) i Hi) as X. cbn [sh_range fst snd aeval] in X. unfold shadow_of_addr. exact X.
-   cbn [ly_tsd ly0]. rewrite (ts_tsd B HB). reflexivity.
-   apply V0. find_in.
-
rewrite (ts_owned B HB), (ts_zsh B HB). cbn [ly_img ly0]. unfold TFIB_IMG. apply Forall_forall. intros r Hr.
pose proof (proj1 (forallb_forall _ _) static_img_chk r Hr) as X. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2.
unfold zr_sub. cbn [fst snd]. lia.
Qed.
Theorem tfib_ARm : ARm B ly0 init_state rdS.
Proof. exact (ARm_init_intro B ly0 rdS tfib_init_facts). Qed.
End a0.
End t.
