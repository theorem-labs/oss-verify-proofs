(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvSK.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn7S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn7S.
Import ListNotations. Import AX2. Import AX2S. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition iv_of (K : kentry) : option (Z * Z * Z) :=
match K with
| KZero (SA (ELit 0) k) (ELit n) => Some (k, n, 0)
| KFill (SA (ELit 0) k) (ELit n) c => Some (k, n, c)
| KWord (SA (ELit 0) k) 1%nat (ELit v) => Some (k, 1, v)
| _ => None
end.

Fixpoint ivs_of (lo hi : Z) (kn : list kentry) : list (Z * Z * Z) :=
match kn with
| [] => []
| K :: r => match iv_of K with
| Some (a, n, c) => if (lo <=? a) && (a <? hi) then (a, n, c) :: ivs_of lo hi r else ivs_of lo hi r
| None => ivs_of lo hi r
end
end.

Lemma ivs_of_in : forall lo hi kn iv, In iv (ivs_of lo hi kn) -> exists K, In K kn /\ iv_of K = Some iv.
Proof.
intros lo hi kn iv. induction kn as [|K r IH]; intros H; [destruct H|]. cbn [ivs_of] in H.
destruct (iv_of K) as [[[a n] c]|] eqn:EK.
- destruct ((lo <=? a) && (a <? hi)).
+ destruct H as [<-|H]; [exists K; split; [left; reflexivity| exact EK]|]. destruct (IH H) as (K' & I' & E'). exists K'. split; [right; exact I'| exact E'].
+ destruct (IH H) as (K' & I' & E'). exists K'. split; [right; exact I'| exact E'].
- destruct (IH H) as (K' & I' & E'). exists K'. split; [right; exact I'| exact E'].
Qed.

Fixpoint regs_avoid (regs : list (Z * Z * Z)) (glo ghi : Z) : bool :=
match regs with
| [] => true
| (b, _, szr) :: r => ((8 * ghi <=? b) || (b + szr <=? 8 * glo)) && regs_avoid r glo ghi
end.

Fixpoint zr (a : Z) (n : nat) : list Z := match n with O => [] | S n' => a :: zr (a + 1) n' end.
Lemma zr_in : forall n a y, a <= y < a + Z.of_nat n -> In y (zr a n).
Proof.
induction n as [|n IH]; intros a y H; [lia|]. cbn [zr]. destruct (Z.eq_dec y a) as [->|NE]; [left; reflexivity|].
right. apply IH. lia.
Qed.

Definition rec_zero_ok (glo ghi : Z) (r : Z * Z * Z) : bool :=
let '(b, sz, szr) := r in
(8 * ghi <=? b) || (b + szr <=? 8 * glo) || (8 * Z.min ghi ((b + szr + 7) / 8) <=? b + sz).
Lemma recs_zero_sound : forall regs glo ghi g, forallb (rec_zero_ok glo ghi) regs = true -> glo <= g < ghi -> QZsi.img_shadow_val regs g = 0.
Proof.
induction regs as [|[[b sz] szr] r IH]; intros glo ghi g H Hg; [reflexivity|]. cbn [forallb] in H. apply andb_prop in H as [H1 H2].
cbn [QZsi.img_shadow_val]. destruct ((b <=? 8 * g) && (8 * g <? b + szr))%bool eqn:E; [| exact (IH glo ghi g H2 Hg)].
apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
unfold rec_zero_ok in H1. apply orb_prop in H1 as [H1|H1]; [apply orb_prop in H1 as [H1|H1]; apply Z.leb_le in H1; lia|].
apply Z.leb_le in H1.
assert (G1 : g + 1 <= Z.min ghi ((b + szr + 7) / 8)).
{ apply Z.min_glb; [lia|]. assert (8 * g + 8 <= 8 * ((b + szr + 7) / 8)) by (pose proof (Z.div_mod (b + szr + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (b + szr + 7) 8 ltac:(lia)); lia). lia. }
destruct (Z.leb_spec (8 * g + 8) (b + sz)) as [L|L]; [reflexivity | lia].
Qed.

Definition val_ok (regs : list (Z * Z * Z)) (sb a n c : Z) : bool :=
if c =? 0 then forallb (rec_zero_ok (a - sb) (a - sb + n)) regs
else forallb (fun x => QZsi.img_shadow_val regs (x - sb) =? c) (zr a (Z.to_nat n)).
Lemma val_ok_sound : forall regs sb a n c, val_ok regs sb a n c = true -> forall y, a <= y < a + n -> QZsi.img_shadow_val regs (y - sb) = c.
Proof.
intros regs sb a n c H y Hy. unfold val_ok in H. destruct (c =? 0) eqn:EC.
- apply Z.eqb_eq in EC. rewrite EC. apply (recs_zero_sound regs (a - sb) (a - sb + n)); [exact H| lia].
- rewrite forallb_forall in H. apply Z.eqb_eq. apply H. apply zr_in. rewrite Z2Nat.id by lia. exact Hy.
Qed.

Fixpoint walk (regs : list (Z * Z * Z)) (sb : Z) (ivs : list (Z * Z * Z)) (x hi : Z) (fuel : nat) : bool :=
if hi <=? x then true else
match fuel with
| O => false
| S f => match find (fun iv => fst (fst iv) =? x) ivs with
| Some (a, n, c) => (0 <? n) && (a + n <=? hi) && (0 <=? c) && (c <? 256) && val_ok regs sb a n c && walk regs sb ivs (a + n) hi f
| None => false
end
end.

Lemma walk_sound : forall regs sb ivs fuel x hi, walk regs sb ivs x hi fuel = true -> forall y, x <= y < hi ->
exists a n c, In (a, n, c) ivs /\ a <= y < a + n /\ a + n <= hi /\ 0 <= c < 256 /\ QZsi.img_shadow_val regs (y - sb) = c.
Proof.
intros regs sb ivs. induction fuel as [|f IH]; intros x hi H y Hy; cbn [walk] in H; destruct (Z.leb_spec hi x) as [L|L]; try lia; try discriminate.
destruct (find (fun iv => fst (fst iv) =? x) ivs) as [[[a n] c]|] eqn:EF; [|discriminate].
apply find_some in EF as [HIn Hx]. cbn [fst] in Hx. apply Z.eqb_eq in Hx. subst a.
apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.ltb_lt in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
destruct (Z.lt_ge_cases y (x + n)) as [Y|Y].
- exists x, n, c. split; [exact HIn|]. split; [lia|]. split; [exact H2|]. split; [lia|]. apply (val_ok_sound regs sb x n c H5). lia.
- apply (IH (x + n) hi H6 y). lia.
Qed.

Section Sound.
Variable segs : list Segment.
Variables (E : env) (base : word -> option byte) (kn : list kentry).
Hypothesis KN : know_ok segs E base kn.

Lemma iv_sound : forall K a n c, In K kn -> iv_of K = Some (a, n, c) -> 0 <= a -> a + n < 2^64 -> 0 <= c < 256 ->
forall i, 0 <= i < n -> QZDE.mrd segs base (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 c).
Proof.
intros K a n c HIn HK A0 A1 C i Hi.
pose proof (proj1 (Forall_forall _ _) KN K HIn) as OK.
destruct K as [sa w v| sa len | | | | | | | sa len cc |]; try discriminate.
-
destruct sa as [b k]. cbn [iv_of] in HK.
destruct b as [z| | | | | | |]; try discriminate. destruct z; try discriminate.
destruct w as [|[|w]]; try discriminate. destruct v as [vv| | | | | | |]; try discriminate. injection HK as Ea En Ec. subst k n vv.
cbn [kentry_ok] in OK. destruct OK as (_ & FL & RD).
pose proof (flat_u E _ _ FL) as FU. unfold estart in FU. cbn [a_base a_off edenot] in FU.
change (bv_unsigned (Z_to_bv 64 0)) with 0 in FU. rewrite Z.add_0_l in FU.
assert (i = 0) by lia. subst i. rewrite Z.add_0_r.
pose proof (rdn_mrd_c segs base 1 _ _ 0%nat RD ltac:(lia) ltac:(rewrite FU; cbn; lia)) as Rd. rewrite FU in Rd. cbn [Z.of_nat] in Rd. rewrite Z.add_0_r in Rd.
rewrite Rd. unfold word_to_le_bytes. cbn [edenot]. rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small by lia.
rewrite (nth_error_le_bytes 1 c 0 ltac:(lia) ltac:(lia)). change (8 * Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.div_1_r, Z.mod_small by lia. reflexivity.
-
destruct sa as [b k]. cbn [iv_of] in HK.
destruct b as [z| | | | | | |]; try discriminate. destruct z; try discriminate. destruct len as [nn| | | | | | |]; try discriminate. injection HK as Ea En Ec. subst k nn c.
cbn [kentry_ok] in OK. destruct OK as [_ OK]. unfold elenZ, estart in OK. cbn [edenot a_base a_off] in OK.
change (bv_unsigned (Z_to_bv 64 0)) with 0 in OK. rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small in OK by lia.
apply mrd_some. specialize (OK i ltac:(lia)). rewrite Z.add_0_l in OK. exact OK.
-
destruct sa as [b k]. cbn [iv_of] in HK.
destruct b as [z| | | | | | |]; try discriminate. destruct z; try discriminate. destruct len as [nn| | | | | | |]; try discriminate. injection HK as Ea En Ec. subst k nn cc.
cbn [kentry_ok] in OK. destruct OK as [_ OK]. unfold elenZ, estart in OK. cbn [edenot a_base a_off] in OK.
change (bv_unsigned (Z_to_bv 64 0)) with 0 in OK. rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small in OK by lia.
apply mrd_some. specialize (OK i ltac:(lia)). rewrite Z.add_0_l in OK. exact OK.
Qed.

Theorem img_shadow_closed : forall regs sb glo ghi fuel,
walk regs sb (ivs_of (glo + sb) (ghi + sb) kn) (glo + sb) (ghi + sb) fuel = true ->
0 <= glo + sb -> ghi + sb < 2^64 ->
forall g, glo <= g < ghi -> QZDE.bytes_at segs base (g + sb) [Z_to_bv 8 (QZsi.img_shadow_val regs g)].
Proof.
intros regs sb glo ghi fuel W B0 B1 g Hg.
destruct (walk_sound regs sb _ fuel _ _ W (g + sb) ltac:(lia)) as (a & n & c & HIn & Ha & Hn & Hc & V).
replace (g + sb - sb) with g in V by lia. rewrite V.
destruct (ivs_of_in _ _ _ _ HIn) as (K & KI & KE).
assert (A0 : glo + sb <= a).
{ clear - HIn. induction kn as [|K0 r IH]; [destruct HIn|]. cbn [ivs_of] in HIn. destruct (iv_of K0) as [[[a0 n0] c0]|]; [|exact (IH HIn)].
destruct ((glo + sb <=? a0) && (a0 <? ghi + sb)) eqn:EB; [|exact (IH HIn)].
destruct HIn as [HE|HIn]; [|exact (IH HIn)]. injection HE as -> _ _. apply andb_prop in EB as [EB _]. apply Z.leb_le in EB. exact EB. }
apply bytes_at_intro; [lia | cbn [length]; lia |].
intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat nth_error]. rewrite Z.add_0_r.
pose proof (iv_sound K a n c KI KE ltac:(lia) ltac:(lia) Hc (g + sb - a) ltac:(lia)) as Rd.
replace (a + (g + sb - a)) with (g + sb) in Rd by lia. exact Rd.
Qed.
End Sound.
