(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__FxKnownBits () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Instr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.FxKnownBits.KBF."; "Stdlib.ZArith.BinInt.Z."], [["0A"; "0B"; "0C"; "1Some"; "1bool"; "1fst"; "1nat"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2not"; "3Z"]; ["4ALU_ADD"; "4ALU_AND"; "4ALU_OR"; "4ALU_SLL"; "4ALU_SLTU"; "4ALU_SRL"; "4ALU_SUB"; "4ALU_XOR"; "4M_MUL"; "4aluop"; "4mulop"; "0M"; "0P"; "5all_eval_toS"; "5evalS"; "5expr"]; ["5expr_eqb"; "5land64"; "5probeS"; "5two64"; "5wrap64"; "5zfast"; "5zfastm"; "6a_add"; "6a_and"; "6a_mul"; "6a_or"; "6a_sll"; "6a_sltu"; "6a_srl"; "6a_sub"; "6a_xor"]; ["6ahi"; "6ak1"; "6alo"; "6aop"; "6av"; "6c_alu"; "6c_md"; "6cand"; "6cst"; "6eqbL"; "6fold1"; "6fold2"; "6gam"; "6in64b"; "6kb_const"; "6kb_mid"]; ["6kb_split"; "6kb_try"; "6kbc"; "6kbv"; "6lowcnt"; "6lowj"; "6lowk0"; "6lowk1"; "6mask_iv"; "6ones64"; "6pt"; "6reduce"; "6tz"; "7add"; "7div"; "7divide"]; ["7eqb"; "7land"; "7le"; "7log2"; "7lor"; "7lt"; "7lxor"; "7max"; "7modulo"; "7mul"; "7of_nat"; "7ones"; "7opp"; "7pow"; "7shiftl"; "7shiftr"]; ["7sub"; "7succ"; "7to_nat"; "0a"; "0b"; "0c"; "0cnt"; "0e"; "0f"; "0fuel"; "0h"; "0ha"; "0hb"; "0hi"; "0j"; "0k"]; ["0k0"; "0k1"; "0l"; "0la"; "0lb"; "0lo"; "0m"; "0n"; "0op"; "0p"; "0s"; "0t"; "0v"; "0w"; "0x"; "0x'"]; ["0y"; "0y'"; "0z"]]).
Module KBF.
Fixpoint eqbL (x y : expr) : bool :=
match x, y with
| ELit a, ELit b => Z.eqb a b
| EVar a, EVar b => Nat.eqb a b
| EAlu o a b, EAlu o' a' b' => if aluop_eqb o o' then (if eqbL a a' then eqbL b b' else false) else false
| EAluw o a b, EAluw o' a' b' => if aluop_eqb o o' then (if eqbL a a' then eqbL b b' else false) else false
| EMd o a b, EMd o' a' b' => if mulop_eqb o o' then (if eqbL a a' then eqbL b b' else false) else false
| EMdw o a b, EMdw o' a' b' => if mulop_eqb o o' then (if eqbL a a' then eqbL b b' else false) else false
| EExt s l n a, EExt s' l' n' a' =>
if Bool.eqb s s' then (if Nat.eqb l l' then (if Nat.eqb n n' then eqbL a a' else false) else false) else false
| EBlob s k i n, EBlob s' k' i' n' =>
if Bool.eqb s s' then (if Nat.eqb k k' then (if Z.eqb i i' then Nat.eqb n n' else false) else false) else false
| _, _ => false
end.
Lemma eqbL_eq : ltac2:(TCodec.tc2 tcn__FxKnownBits "<'O'<'4&QIr2r1%3221&Q0%1243%83731pX2:1pWN;1").
Proof.
induction x as [a|a|o a IHa b IHb|o a IHa b IHb|o a IHa b IHb|o a IHa b IHb|sx l n a IHa|sx k i n];
intros [a'|a'|o' a' b'|o' a' b'|o' a' b'|o' a' b'|sx' l' n' a'|sx' k' i' n']; try reflexivity; cbn [eqbL expr_eqb];
rewrite ?IHa, ?IHb.
- destruct (aluop_eqb o o'); [destruct (expr_eqb a a'); reflexivity|reflexivity].
- destruct (aluop_eqb o o'); [destruct (expr_eqb a a'); reflexivity|reflexivity].
- destruct (mulop_eqb o o'); [destruct (expr_eqb a a'); reflexivity|reflexivity].
- destruct (mulop_eqb o o'); [destruct (expr_eqb a a'); reflexivity|reflexivity].
- destruct (Bool.eqb sx sx'); [destruct (Nat.eqb l l'); [destruct (Nat.eqb n n'); reflexivity|reflexivity]|reflexivity].
- destruct (Bool.eqb sx sx'); [destruct (Nat.eqb k k'); [destruct (Z.eqb i i'); reflexivity|reflexivity]|reflexivity].
Qed.
Lemma two64_eq : ltac2:(TCodec.tc2 tcn__FxKnownBits "8'<'?&Q3&RM+2+R0%3221%73651"). Proof. reflexivity. Qed.
Lemma two64_pos : ltac2:(TCodec.tc2 tcn__FxKnownBits "4&REz&Q3%3221"). Proof. reflexivity. Qed.
Definition ones64 : Z := Z.ones 64.
Lemma ones64_eq : ltac2:(TCodec.tc2 tcn__FxKnownBits "8'<'?&R9&S0&Q3+1%3221%73651"). Proof. reflexivity. Qed.
Lemma land_le_l : ltac2:(TCodec.tc2 tcn__FxKnownBits "<'?&RBzr2%3221&RAr3%2214%7212p051pW0:1pV8;1").
Proof.
intros a k Ha.
assert (H : Z.ldiff (Z.land a k) a = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
destruct (Z.testbit a n), (Z.testbit k n); reflexivity. }
pose proof (Z.sub_nocarry_ldiff a (Z.land a k) H) as E.
assert (0 <= Z.ldiff a (Z.land a k)) by (apply Z.ldiff_nonneg; left; exact Ha). lia.
Qed.
Lemma land_nonneg_l : ltac2:(TCodec.tc2 tcn__FxKnownBits "<'?&RBzr2%3221&RAr3%2214%7261p051pW0:1pV8;1").
Proof. intros. apply Z.land_nonneg. left. assumption. Qed.
Lemma lor_lt_two64 : ltac2:(TCodec.tc2 tcn__FxKnownBits "E'?';&RBzr2%3221&RE&Q3%2241%8241&RDr4r3%3221%<2;1%9228%?221p081p091pV:C1pV8D1").
Proof.
intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
destruct (Z.eq_dec (Z.lor a b) 0) as [E|E]; [rewrite E; reflexivity|].
assert (0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
rewrite two64_eq. apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor by lia.
assert (La : Z.log2 a < 64). { destruct (Z.eq_dec a 0) as [->|]; [reflexivity|apply Z.log2_lt_pow2; [lia|rewrite <- two64_eq; lia]]. }
assert (Lb : Z.log2 b < 64). { destruct (Z.eq_dec b 0) as [->|]; [reflexivity|apply Z.log2_lt_pow2; [lia|rewrite <- two64_eq; lia]]. }
lia.
Qed.
Lemma lxor_lt_two64 : ltac2:(TCodec.tc2 tcn__FxKnownBits "E'?';&RBzr2%3221&RE&Q3%2241%8241&RFr4r3%3221%<2;1%9228%?221p081p091pV:C1pV8D1").
Proof.
intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|].
destruct (Z.eq_dec (Z.lxor a b) 0) as [E|E]; [rewrite E; reflexivity|].
assert (0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
rewrite two64_eq. apply Z.log2_lt_pow2; [lia|]. pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)).
assert (La : Z.log2 a < 64). { destruct (Z.eq_dec a 0) as [->|]; [reflexivity|apply Z.log2_lt_pow2; [lia|rewrite <- two64_eq; lia]]. }
assert (Lb : Z.log2 b < 64). { destruct (Z.eq_dec b 0) as [->|]; [reflexivity|apply Z.log2_lt_pow2; [lia|rewrite <- two64_eq; lia]]. }
lia.
Qed.
Lemma le_ones_sub : ltac2:(TCodec.tc2 tcn__FxKnownBits "J'?';&RBzr2%3221&RE&Q3%2241%8241'<&RAr4r3%3221%53?1<r5&S0&R9%2217%B241p061p0=1p0>1pW>H1pWNI1").
Proof.
intros x m Hx Hm H. pose proof (Z.add_lor_land x m) as E. rewrite H in E.
pose proof (lor_lt_two64 x m Hx Hm). rewrite ones64_eq. lia.
Qed.
Lemma ge_known1 : ltac2:(TCodec.tc2 tcn__FxKnownBits "@'?&RBzr2%3221'<&RAr3%2215%43916r4%:241p031p091pW0>1pWN?1").
Proof. intros x k Hx H. rewrite <- H. apply land_le_l. exact Hx. Qed.
Record av : Type := AV { alo : Z; ahi : Z; ak0 : Z; ak1 : Z }.
Definition gam (A : av) (x : Z) : Prop :=
0 <= x < two64 /\ alo A <= x <= ahi A /\ Z.land x (ak0 A) = 0 /\ Z.land x (ak1 A) = ak1 A.
Ltac tb H n := let Hb := fresh "Hb" in
pose proof (f_equal (fun t => Z.testbit t n) H) as Hb; cbn beta in Hb;
rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.lxor_spec, ?Z.bits_0 in Hb.
Ltac bcases := repeat match goal with
| H : context [Z.testbit ?a ?m] |- _ => destruct (Z.testbit a m)
| |- context [Z.testbit ?a ?m] => destruct (Z.testbit a m)
end; try discriminate; try reflexivity.
Lemma land_ones64_id : ltac2:(TCodec.tc2 tcn__FxKnownBits "B'?';&RBzr1%3221&RE&Q3%2241%8241'<&RAr2&R9%3221%53?13p071pWNA1").
Proof. intros x Hx. unfold ones64. rewrite Z.land_ones by lia. apply Z.mod_small. rewrite <- two64_eq. exact Hx. Qed.
Lemma land_compl : ltac2:(TCodec.tc2 tcn__FxKnownBits "D'?';&RBzr1%3221&RE&Q3%2241%8241'<&RAr2&RF&R9%2231%5241%73A1>p091pWNC1").
Proof.
intros x Hx. pose proof (land_ones64_id x Hx) as E. apply Z.bits_inj'. intros n Hn. tb E n.
rewrite Z.land_spec, Z.lxor_spec, Z.bits_0. bcases.
Qed.
Lemma hi_bits_eq : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q8'?&RBzr3%3221';r4r2%7221%8226%5221&>'<&RFr5%2219%43@1>%611&S1&RCr6%8217%311%511&REr1%22H1&RO%12>3r7%3215%C3O31%K261tVNQ1:1p0A1p0I1p0Q01pWNQ51pVLQ61pW<Q71").
Proof.
intros lo hi x Hlo Hx Hd j.
assert (Hd0 : 0 <= Z.lxor lo hi) by (apply Z.lxor_nonneg; lia).
assert (Hj : 0 < j) by (unfold j; pose proof (Z.log2_nonneg (Z.lxor lo hi)); lia).
split; [exact Hj|].
assert (E0 : Z.shiftr (Z.lxor lo hi) j = 0) by (apply Z.shiftr_eq_0; [exact Hd0|unfold j; lia]).
rewrite Z.shiftr_lxor in E0. apply Z.lxor_eq in E0.
rewrite !Z.shiftr_div_pow2 in * by lia.
assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
pose proof (Z.div_le_mono lo x (2 ^ j) ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono x hi (2 ^ j) ltac:(lia) ltac:(lia)). lia.
Qed.
Definition reduce (lo hi k0 k1 : Z) : option av :=
let lo1 := Z.max (Z.max lo 0) k1 in
let hi1 := Z.min hi (ones64 - Z.land k0 ones64) in
if Z.ltb hi1 lo1 then None else
let d := Z.lxor lo1 hi1 in
if Z.eqb d 0 then Some (AV lo1 lo1 (Z.lxor lo1 ones64) lo1)
else let j := Z.succ (Z.log2 d) in
Some (AV lo1 hi1 (Z.lor k0 (Z.shiftl (Z.shiftr (Z.lxor lo1 ones64) j) j)) (Z.lor k1 (Z.shiftl (Z.shiftr lo1 j) j))).
Lemma reduce_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q@'?'QD';&RBzr2%3221&RE&Q3%2241%8241r7r3%:221r6%<231%>231'<&RAr4%2216%43E1Ar5%5219%73H1:'7%11I&R;r:r9r8%44321D(3%12Q0;%A3831&QL%12FIp031p0>1p0B1p0H1p0O1p2Q91pWNQ;1pW4Q<1pW2Q=1pVLQ>1pW<Q?1").
Proof.
intros lo hi k0 k1 x A Hx Hi H0 H1. unfold reduce.
set (lo1 := Z.max (Z.max lo 0) k1). set (hi1 := Z.min hi (ones64 - Z.land k0 ones64)).
assert (L1 : lo1 <= x). { pose proof (ge_known1 x k1 ltac:(lia) H1). unfold lo1. lia. }
assert (L2 : x <= hi1).
{ assert (Hm : 0 <= Z.land k0 ones64 < two64).
{ unfold ones64. rewrite Z.land_ones by lia. rewrite two64_eq. apply Z.mod_pos_bound. reflexivity. }
pose proof (le_ones_sub x (Z.land k0 ones64) Hx Hm) as Q.
rewrite Z.land_assoc, H0, Z.land_0_l in Q. specialize (Q eq_refl). unfold hi1. lia. }
assert (L0 : 0 <= lo1) by (unfold lo1; lia).
destruct (Z.ltb hi1 lo1); [discriminate|].
destruct (Z.eqb (Z.lxor lo1 hi1) 0) eqn:Ed.
- apply Z.eqb_eq, Z.lxor_eq in Ed. intros Q. injection Q as <-. unfold gam. cbn [alo ahi ak0 ak1].
assert (x = lo1) by lia. subst x. repeat split; try lia; [apply land_compl; exact Hx|apply Z.land_diag].
- apply Z.eqb_neq in Ed. intros Q. injection Q as <-. unfold gam. cbn [alo ahi ak0 ak1].
destruct (hi_bits_eq lo1 hi1 x L0 (conj L1 L2) Ed) as [Hj Es]. set (j := Z.succ (Z.log2 (Z.lxor lo1 hi1))) in *.
assert (Hb : forall n, j <= n -> Z.testbit lo1 n = Z.testbit x n).
{ intros n Hn. replace n with ((n - j) + j) by lia. rewrite <- !Z.shiftr_spec by lia. rewrite Es. reflexivity. }
pose proof (land_ones64_id x Hx) as Eo.
repeat split; try lia.
+ rewrite Z.land_lor_distr_r, H0, Z.lor_0_l. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases n j) as [Hl|Hg].
* rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
* rewrite Z.shiftl_spec by lia. rewrite Z.shiftr_spec by lia. replace (n - j + j) with n by lia.
rewrite Z.lxor_spec, (Hb n Hg). tb Eo n. bcases.
+ rewrite Z.land_lor_distr_r, H1. f_equal. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
destruct (Z.lt_ge_cases n j) as [Hl|Hg].
* rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
* rewrite Z.shiftl_spec by lia. rewrite Z.shiftr_spec by lia. replace (n - j + j) with n by lia.
rewrite (Hb n Hg). apply andb_diag.
Qed.
Definition cst (c : Z) : av := AV c c (Z.lxor c ones64) c.
Lemma cst_gam : ltac2:(TCodec.tc2 tcn__FxKnownBits "A'?';&RBzr1%3221&RE&Q3%2241%8241&QL&QHr2%211%4212p061pV<@1").
Proof. intros c Hc. unfold gam, cst. cbn [alo ahi ak0 ak1]. repeat split; try lia; [apply land_compl; exact Hc|apply Z.land_diag]. Qed.
Fixpoint lowcnt (fuel : nat) (m : Z) : Z :=
match fuel with
| O => 0
| S f => if Z.odd m then Z.succ (lowcnt f (Z.div2 m)) else 0
end.
Lemma lowcnt_spec : ltac2:(TCodec.tc2 tcn__FxKnownBits "G'6'?';&RBz&R4r2r1%3221%6251&RJ%115%9241%;241'<&RA&RK%119%32;1%53B12%B271pW>D1pVBF1").
Proof.
induction f as [|f IH]; intros m; cbn [lowcnt].
- split; [lia|]. change (Z.ones 0) with 0. apply Z.land_0_r.
- destruct (Z.odd m) eqn:Eo.
+ destruct (IH (Z.div2 m)) as [[H1 H2] H3]. split; [lia|].
set (j := lowcnt f (Z.div2 m)) in *.
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
destruct (Z.eq_dec n 0) as [->|Hn0].
* rewrite Z.bit0_odd, Eo. reflexivity.
* tb H3 (n - 1). rewrite Z.div2_spec, Z.shiftr_spec in Hb by lia. replace (n - 1 + 1) with n in Hb by lia.
destruct (Z.lt_ge_cases n (Z.succ j)) as [Hl|Hg].
-- rewrite (Z.ones_spec_low (Z.succ j) n) by lia. rewrite (Z.ones_spec_low j (n - 1)) in Hb by lia. exact Hb.
-- rewrite Z.ones_spec_high by lia. apply andb_false_r.
+ split; [lia|]. change (Z.ones 0) with 0. apply Z.land_0_r.
Qed.
Lemma known_low : ltac2:(TCodec.tc2 tcn__FxKnownBits "J'?'<&RAr4r3%3221z%63721r5%7215%93:16&RD%1249%;219%=3>1:r7%>21=%?29>%A3B21p051p0:1p0>1pQHF1pW4G1pW2H1pWNI1").
Proof.
intros x k0 k1 M H0 H1 HM. apply Z.bits_inj'. intros n Hn. tb H0 n. tb H1 n. tb HM n.
rewrite !Z.land_spec. bcases.
Qed.
Lemma land_sub_mask : ltac2:(TCodec.tc2 tcn__FxKnownBits "@'?'<&RAr3r2%3221%53612r4%6214%7216%8267%:3;21p061pV:=1pV8>1pW>?1").
Proof. intros m a b H. apply Z.bits_inj'. intros n Hn. tb H n. rewrite !Z.land_spec. bcases. Qed.
Lemma lowbits_gam : ltac2:(TCodec.tc2 tcn__FxKnownBits "A'?';'<&RAr2r1%3221%4231%63812&RF%1254%8271z%;3=21%=261pQH?1pWL@1").
Proof.
intros w M. split; apply Z.bits_inj'; intros n Hn; rewrite ?Z.land_spec, ?Z.lxor_spec, ?Z.land_spec, ?Z.bits_0; bcases.
Qed.
Definition kmask (A : av) : Z := Z.lor (ak0 A) (ak1 A).
Definition lowj (A B : av) : Z := lowcnt 64 (Z.land (kmask A) (kmask B)).
Lemma lowj_spec : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q:'QD'?&QLr4r2%3221&R5r6r5%3221';&RBzr1%3221+R0%5231%7231'<&RH&RM+2%2219%42?1&QAr7%211%8215%:3K51%:2J7%61G%<219%>3O31%G251%H2A1tVNQ2J1p0O1p0Q01pX2Q51pWNQ61p4Q81p2Q91").
Proof.
intros A B x y (_ & _ & A0 & A1) (_ & _ & B0 & B1) j.
destruct (lowcnt_spec 64 (Z.land (kmask A) (kmask B))) as [Hj HM]. fold (lowj A B) in Hj, HM. fold j in Hj, HM.
split; [exact Hj|]. rewrite <- !Z.land_ones by lia.
unfold kmask in HM.
split; (eapply known_low; [eassumption|eassumption|]);
(apply Z.bits_inj'; intros n Hn; tb HM n; rewrite !Z.land_spec, ?Z.lor_spec; rewrite ?Z.lor_spec in Hb; bcases).
Qed.
Definition lowk1 (j c : Z) : Z := Z.land c (Z.ones j).
Definition lowk0 (j c : Z) : Z := Z.lxor (Z.ones j) (lowk1 j c).
Lemma lowk_gam : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q0'?&RBzr3%3221'<&RHr2&RM+2r4%3221%6251%72:2%93>21';&RA&R6r5%2219%42A1%@3E1C&R7%125=%82E1%D3I12%;251p0=1p0H1pWLM1pV<N1pVNO1").
Proof.
intros j c w Hj E. unfold lowk0, lowk1. rewrite <- !Z.land_ones in E by lia. rewrite <- E.
destruct (lowbits_gam w (Z.ones j)) as [Q1 Q2]. split; assumption.
Qed.
Lemma mod_mod_pow : ltac2:(TCodec.tc2 tcn__FxKnownBits "H'?';&RBzr1%3221+R0%5231%7231'<&RHr3&Q3%3221&RM+2r2%3221%8251%9282%;3D21p0=1pVNF1pV8G1").
Proof.
intros a j Hj. symmetry. apply Znumtheory.Zmod_div_mod.
- apply Z.pow_pos_nonneg; lia.
- exact two64_pos.
- exists (2 ^ (64 - j)). rewrite two64_eq, <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma land64_mod : ltac2:(TCodec.tc2 tcn__FxKnownBits ":'?'<&Q1r1%211&RH&Q3%2241%73841pX691").
Proof.
intros z. unfold land64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:E.
- apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. symmetry. apply Z.mod_small. lia.
- unfold ones64z. rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma wrap64_mod : ltac2:(TCodec.tc2 tcn__FxKnownBits ":'?'<&Q4r1%211&RH&Q3%2241%73841pX691").
Proof.
intros z. unfold wrap64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:E; [|reflexivity].
apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. symmetry. apply Z.mod_small. lia.
Qed.
Lemma mod64_range : ltac2:(TCodec.tc2 tcn__FxKnownBits "='?';&RBz&RHr1&Q3%3221%6251&RE%1234%:231pX6<1").
Proof. intros z. apply Z.mod_pos_bound. exact two64_pos. Qed.
Lemma wrap64_id : ltac2:(TCodec.tc2 tcn__FxKnownBits "A'?';&RBzr1%3221&RE&Q3%2241%8241'<&Q4r2%211%43>12p061pX6@1").
Proof. intros z Hz. rewrite wrap64_mod. apply Z.mod_small. exact Hz. Qed.
Lemma zadd_mod : ltac2:(TCodec.tc2 tcn__FxKnownBits "I'?';&RBzr2%3221&RE&Q3%2241%8241'<&Q5(@r4r3%43321&RH&R=%1254%321<%:3D51p0<1p0=1pX2G1pWNH1").
Proof.
intros x y Hx Hy. cbn [zfast]. destruct (Z.ltb (x + y) two64) eqn:E.
- apply Z.ltb_lt in E. symmetry. apply Z.mod_small. lia.
- apply Z.ltb_ge in E. apply Z.mod_unique with (q := 1); lia.
Qed.
Lemma zsub_mod : ltac2:(TCodec.tc2 tcn__FxKnownBits "I'?';&RBzr2%3221&RE&Q3%2241%8241'<&Q5(Fr4r3%43321&RH&S0%1254%321<%:3D51p0<1p0=1pX2G1pWNH1").
Proof.
intros x y Hx Hy. cbn [zfast]. destruct (Z.leb 0 (x - y)) eqn:E.
- apply Z.leb_le in E. symmetry. apply Z.mod_small. lia.
- apply Z.leb_gt in E. apply Z.mod_unique with (q := -1); lia.
Qed.
Lemma mod_iv_small : ltac2:(TCodec.tc2 tcn__FxKnownBits "K'?';&RBr2r3%3221r1%5231%7231zr4%9221&RE&Q3%2241%>241&RHr5%2215%A291%B22@%D221p071p0?1pVLH1pW<I1pWHJ1").
Proof. intros t lo hi H H0. rewrite Z.mod_small by exact H0. exact H. Qed.
Lemma mod_iv_wrap : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q1'?';&RBr2r3%3221r1%5231%7231&Q3%8216&REr5&RI+2%2216%5241&S0%1269&RHr6%221<%D241r4%721?%G241%I241p0;1p0B1p0E1pVLN1pW<O1pWHQ01").
Proof.
intros t lo hi H H0 H1. assert (E : t mod two64 = t - two64) by (symmetry; apply Z.mod_unique with (q := 1); lia).
rewrite E. lia.
Qed.
Lemma mod_iv_neg : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q1'?';&RBr2r3%3221r1%5231%7231&REz%2281&RL&Q3%211r5%>221&R=%1235&RHr6%2218%D241r4%721;%G241%I241p0;1p0A1p0E1pVLN1pW<O1pWHQ01").
Proof.
intros t lo hi H H0 H1. assert (E : t mod two64 = t + two64) by (symmetry; apply Z.mod_unique with (q := -1); lia).
rewrite E. lia.
Qed.
Lemma mod_iv_full : ltac2:(TCodec.tc2 tcn__FxKnownBits "='?';&RBz&RHr1&Q3%3221%6251&R9%8231%:231pWH<1").
Proof. intros t. pose proof (mod64_range t). rewrite ones64_eq. lia. Qed.
Definition a_add (A B : av) : option av :=
let lo := alo A + alo B in let hi := ahi A + ahi B in
let j := lowj A B in let c := ak1 A + ak1 B in
if Z.ltb hi two64 then reduce lo hi (lowk0 j c) (lowk1 j c)
else if Z.leb two64 lo then reduce (lo - two64) (hi - two64) (lowk0 j c) (lowk1 j c)
else reduce 0 ones64 (lowk0 j c) (lowk1 j c).
Lemma a_add_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "M'QD'?&QLr5r2%3221'<'7%118&Q7r7r6%3221(3%12>;%93731&Q5(@r4%332@1%B291p061p0A1p0B1pX2G1pWNH1p6J1p4K1p2L1").
Proof.
intros A B C x y GA GB. destruct (lowj_spec A B x y GA GB) as (Hj & Ex & Ey).
destruct GA as (Hx & Ix & _ & _). destruct GB as (Hy & Iy & _ & _).
rewrite (zadd_mod x y Hx Hy).
assert (Hm : ((x + y) mod two64) mod 2 ^ lowj A B = (ak1 A + ak1 B) mod 2 ^ lowj A B).
{ rewrite mod_mod_pow by exact Hj. rewrite Zplus_mod, Ex, Ey, <- Zplus_mod. reflexivity. }
destruct (lowk_gam _ _ _ (proj1 Hj) Hm) as [K0 K1]. clear Hm Ex Ey Hj.
pose proof (mod64_range (x + y)) as Hw.
unfold a_add. destruct (Z.ltb (ahi A + ahi B) two64) eqn:E1.
- apply Z.ltb_lt in E1. apply reduce_sound; try assumption. clear K0 K1 Hw. apply mod_iv_small; lia.
- apply Z.ltb_ge in E1. destruct (Z.leb two64 (alo A + alo B)) eqn:E2.
+ apply Z.leb_le in E2. apply reduce_sound; try assumption. clear K0 K1 Hw. apply mod_iv_wrap; lia.
+ apply reduce_sound; try assumption. apply mod_iv_full.
Qed.
Definition a_sub (A B : av) : option av :=
let lo := alo A - ahi B in let hi := ahi A - alo B in
let j := lowj A B in let c := ak1 A - ak1 B in
if Z.leb 0 lo then reduce lo hi (lowk0 j c) (lowk1 j c)
else if Z.ltb hi 0 then reduce (lo + two64) (hi + two64) (lowk0 j c) (lowk1 j c)
else reduce 0 ones64 (lowk0 j c) (lowk1 j c).
Lemma a_sub_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "M'QD'?&QLr5r2%3221'<'7%118&Q>r7r6%3221(3%12>;%93731&Q5(Fr4%332@1%B291p061p0A1p0B1pX2G1pWNH1p6J1p4K1p2L1").
Proof.
intros A B C x y GA GB. destruct (lowj_spec A B x y GA GB) as (Hj & Ex & Ey).
destruct GA as (Hx & Ix & _ & _). destruct GB as (Hy & Iy & _ & _).
rewrite (zsub_mod x y Hx Hy).
assert (Hm : ((x - y) mod two64) mod 2 ^ lowj A B = (ak1 A - ak1 B) mod 2 ^ lowj A B).
{ rewrite mod_mod_pow by exact Hj. rewrite Zminus_mod, Ex, Ey, <- Zminus_mod. reflexivity. }
destruct (lowk_gam _ _ _ (proj1 Hj) Hm) as [K0 K1]. clear Hm Ex Ey Hj.
pose proof (mod64_range (x - y)) as Hw.
unfold a_sub. destruct (Z.leb 0 (alo A - ahi B)) eqn:E1.
- apply Z.leb_le in E1. apply reduce_sound; try assumption. clear K0 K1 Hw. apply mod_iv_small; lia.
- apply Z.leb_gt in E1. destruct (Z.ltb (ahi A - alo B) 0) eqn:E2.
+ apply Z.ltb_lt in E2. apply reduce_sound; try assumption. clear K0 K1 Hw. apply mod_iv_neg; lia.
+ apply reduce_sound; try assumption. apply mod_iv_full.
Qed.
Definition tz (A : av) : Z := lowcnt 64 (ak0 A).
Lemma tz_spec : ltac2:(TCodec.tc2 tcn__FxKnownBits "I'QD'?&QLr2r1%3221';&RBz&R<r3%211%5241+R0%7231%9231&R?&RM+2%2218%421A%?261p0A1pWNF1p2H1").
Proof.
intros A x (_ & _ & A0 & _). destruct (lowcnt_spec 64 (ak0 A)) as [Ht HM]. fold (tz A) in Ht, HM.
split; [exact Ht|]. apply Z.mod_divide; [apply Z.pow_nonzero; lia|].
rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros n Hn. tb A0 n. tb HM n. rewrite Z.land_spec, Z.bits_0. bcases.
Qed.
Lemma mul_iv : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q6'?&RBzr6%3221';r8%6241r5%8231%5231%:235r4%<271%9231&RI&RG%12?;%22@?%4221r:r9%7221%F241r7%:21A%I241%F241p0>1p0C1p0J1p0K1pVJQ01pW:Q11pVHQ21pW8Q31pX2Q41pWNQ51").
Proof. intros. split; apply Z.mul_le_mono_nonneg; lia. Qed.
Lemma pow_split_divide : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q1'?&RBzr5%3221';&R=r7r6%3221%9271%6271&R?&RM+2%2217&RIr8%5241%32@1r4%827>%6221%7241%<291p0>1p0F1p0G1pX4L1pX0M1pWHN1pV:O1pV8Q01").
Proof.
intros a b t x' y' Ha Hb Ht. exists (2 ^ (a + b - t) * (x' * y')).
replace (2 ^ (a + b - t) * (x' * y') * 2 ^ t) with ((2 ^ (a + b - t) * 2 ^ t) * (x' * y')) by ring.
rewrite <- Z.pow_add_r by lia. replace (a + b - t + t) with (a + b) by lia.
rewrite Z.pow_add_r by lia. ring.
Qed.
Definition a_mul (A B : av) : option av :=
let hi := ahi A * ahi B in
let j := lowj A B in let c := ak1 A * ak1 B in
let t := Z.min 64 (tz A + tz B) in
let k0 := Z.lor (lowk0 j c) (Z.ones t) in
if Z.ltb hi two64 then reduce (Z.max 0 (alo A) * Z.max 0 (alo B)) hi k0 (lowk1 j c) else reduce 0 ones64 k0 (lowk1 j c).
Lemma a_mul_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "M'QD'?&QLr5r2%3221'<'7%118&Q9r7r6%3221(3%12>;%93731&Q6(Hr4%332@1%B291p061p0A1p0B1pX2G1pWNH1p6J1p4K1p2L1").
Proof.
intros A B C x y GA GB. destruct (lowj_spec A B x y GA GB) as (Hj & Ex & Ey).
destruct (tz_spec A x GA) as [HtA [x' Dx]]. destruct (tz_spec B y GB) as [HtB [y' Dy]].
destruct GA as (Hx & Ix & _ & _). destruct GB as (Hy & Iy & _ & _).
cbn [zfastm]. rewrite land64_mod.
assert (Hm : ((x * y) mod two64) mod 2 ^ lowj A B = (ak1 A * ak1 B) mod 2 ^ lowj A B).
{ rewrite mod_mod_pow by exact Hj. rewrite Zmult_mod, Ex, Ey, <- Zmult_mod. reflexivity. }
destruct (lowk_gam _ _ _ (proj1 Hj) Hm) as [K0 K1]. clear Hm Ex Ey Hj.
set (t := Z.min 64 (tz A + tz B)).
assert (Ht : 0 <= t <= 64) by (unfold t; lia).
assert (Kt : Z.land ((x * y) mod two64) (Z.ones t) = 0).
{ rewrite Z.land_ones by lia. rewrite mod_mod_pow by exact Ht.
apply Z.mod_divide; [apply Z.pow_nonzero; lia|]. rewrite Dx, Dy. apply pow_split_divide; unfold t; lia. }
assert (K0' : Z.land ((x * y) mod two64) (Z.lor (lowk0 (lowj A B) (ak1 A * ak1 B)) (Z.ones t)) = 0).
{ rewrite Z.land_lor_distr_r, K0, Kt. reflexivity. }
pose proof (mod64_range (x * y)) as Hw.
pose proof (mul_iv x y _ _ _ _ (proj1 Hx) (proj1 Hy) Ix Iy) as Hi.
unfold a_mul. fold t. destruct (Z.ltb (ahi A * ahi B) two64) eqn:E1.
- apply Z.ltb_lt in E1. apply reduce_sound; try assumption. clear K0 K1 Kt K0' Hw Dx Dy.
apply mod_iv_small; [exact Hi|]. split; [apply Z.mul_nonneg_nonneg; lia|lia].
- apply reduce_sound; try assumption. apply mod_iv_full.
Qed.
Lemma mod_block : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q2'?&REzr1%3221';&RBr5r4%3221r3%5231%7231'<&R>r6%2216%3297%53B21&RHr7%221=%327>%A221%52A@%C231%E231p091p0@1p0I1pWDN1pV:O1pWNQ01pV8Q11").
Proof.
intros a x b p Hp Hx E.
assert (Ex : x / p = a / p).
{ pose proof (Z.div_le_mono a x p Hp (proj1 Hx)). pose proof (Z.div_le_mono x b p Hp (proj2 Hx)). lia. }
rewrite !Z.mod_eq by lia. rewrite Ex, <- E. set (t := p * (a / p)). lia.
Qed.
Definition pt (A : av) : option Z := if Z.eqb (alo A) (ahi A) then Some (alo A) else None.
Lemma pt_gam : ltac2:(TCodec.tc2 tcn__FxKnownBits "E'QD'?&QLr3r2%3221'<'7%117&R:r4%211(3%12<9%83631%93>5<p021p0<1pV<A1pWNB1p2D1").
Proof.
intros A x c (_ & Ix & _ & _) H. unfold pt in H. destruct (Z.eqb (alo A) (ahi A)) eqn:E; [|discriminate].
injection H as <-. apply Z.eqb_eq in E. lia.
Qed.
Definition lowmask_k (m : Z) : option Z := let k := Z.log2 (m + 1) in if Z.eqb m (Z.ones k) then Some k else None.
Definition mask_iv (A : av) (m : Z) : option (Z * Z) :=
match lowmask_k m with
| Some k => if (if Z.leb 0 (alo A) then Z.eqb (Z.shiftr (alo A) k) (Z.shiftr (ahi A) k) else false)
then Some (Z.land (alo A) m, Z.land (ahi A) m) else None
| None => None
end.
Lemma mask_iv_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q3'QD'?&QLr5r3%3221'<'7'9%1288%311&R8r6%221:(3(8r2%24@@=1%4291%=3961';&RBr4&RA%12E<%4231%522F%7221p091p0H1pVFM1pW6N1pWNO1pW>Q01p2Q21").
Proof.
intros A m x l h (Hx & Ix & _ & _) H. unfold mask_iv, lowmask_k in H.
destruct (Z.eqb m (Z.ones (Z.log2 (m + 1)))) eqn:Em; [|discriminate]. apply Z.eqb_eq in Em.
set (k := Z.log2 (m + 1)) in *. assert (Hk : 0 <= k) by apply Z.log2_nonneg.
destruct (Z.leb 0 (alo A)) eqn:E0; [|discriminate]. destruct (Z.eqb (Z.shiftr (alo A) k) (Z.shiftr (ahi A) k)) eqn:E1; [|discriminate].
injection H as <- <-. apply Z.eqb_eq in E1. rewrite !Z.shiftr_div_pow2 in E1 by exact Hk.
rewrite Em, !Z.land_ones by exact Hk. apply mod_block; [apply Z.pow_pos_nonneg; lia|exact Ix|exact E1].
Qed.
Definition and_iv (A B : av) : Z * Z :=
match (match pt B with Some m => mask_iv A m | None => None end) with
| Some r => r
| None => match (match pt A with Some m => mask_iv B m | None => None end) with
| Some r => r
| None => (0, Z.min (ahi A) (ahi B))
end
end.
Definition a_and (A B : av) : option av :=
let r := and_iv A B in reduce (fst r) (snd r) (Z.lor (ak0 A) (ak0 B)) (Z.land (ak1 A) (ak1 B)).
Lemma a_and_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "M'QD'?&QLr5r2%3221'<'7%118&Q8r7r6%3221(3%12>;%93731&Q5(Ar4%332@1%B291p061p0A1p0B1pX2G1pWNH1p6J1p4K1p2L1").
Proof.
intros A B C x y GA GB. cbn [zfast]. unfold a_and.
assert (Hi : fst (and_iv A B) <= Z.land x y <= snd (and_iv A B)).
{ unfold and_iv.
destruct (match pt B with Some m => mask_iv A m | None => None end) as [[l h]|] eqn:E1.
- destruct (pt B) as [m|] eqn:EB; [|discriminate]. rewrite (pt_gam B y m GB EB). exact (mask_iv_sound A m x l h GA E1).
- destruct (match pt A with Some m => mask_iv B m | None => None end) as [[l h]|] eqn:E2.
+ destruct (pt A) as [m|] eqn:EA; [|discriminate]. rewrite (pt_gam A x m GA EA), Z.land_comm.
exact (mask_iv_sound B m y l h GB E2).
+ cbn [fst snd]. destruct GA as (Hx & Ix & _ & _). destruct GB as (Hy & Iy & _ & _).
pose proof (land_le_l x y (proj1 Hx)). pose proof (land_le_l y x (proj1 Hy)) as H2. rewrite Z.land_comm in H2.
pose proof (land_nonneg_l x y (proj1 Hx)). lia. }
destruct GA as (Hx & Ix & A0 & A1). destruct GB as (Hy & Iy & B0 & B1).
pose proof (land_le_l x y (proj1 Hx)). pose proof (land_nonneg_l x y (proj1 Hx)).
apply reduce_sound; try lia; try exact Hi.
- apply Z.bits_inj'. intros n Hn. tb A0 n. tb B0 n. rewrite !Z.land_spec, Z.lor_spec, Z.bits_0. bcases.
- apply Z.bits_inj'. intros n Hn. tb A1 n. tb B1 n. rewrite !Z.land_spec. bcases.
Qed.
Lemma lor_ge_l : ltac2:(TCodec.tc2 tcn__FxKnownBits "A'?&RBzr2%3221';r4&RDr3%2231%9241%:232%7221p091p0:1pX2?1pWN@1").
Proof.
intros x y Hx Hy. pose proof (Z.add_lor_land x y). pose proof (land_le_l x y Hx). pose proof (land_le_l y x Hy) as H2.
rewrite Z.land_comm in H2. lia.
Qed.
Definition a_or (A B : av) : option av :=
reduce (Z.max (alo A) (alo B)) ones64 (Z.land (ak0 A) (ak0 B)) (Z.lor (ak1 A) (ak1 B)).
Lemma a_or_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "M'QD'?&QLr5r2%3221'<'7%118&Q:r7r6%3221(3%12>;%93731&Q5(Br4%332@1%B291p061p0A1p0B1pX2G1pWNH1p6J1p4K1p2L1").
Proof.
intros A B C x y (Hx & Ix & A0 & A1) (Hy & Iy & B0 & B1). cbn [zfast]. unfold a_or.
pose proof (lor_lt_two64 x y Hx Hy). pose proof (lor_ge_l x y (proj1 Hx) (proj1 Hy)).
apply reduce_sound; try (rewrite ?ones64_eq; lia).
- apply Z.bits_inj'. intros n Hn. tb A0 n. tb B0 n. rewrite !Z.land_spec, Z.lor_spec, Z.bits_0. bcases.
- apply Z.bits_inj'. intros n Hn. tb A1 n. tb B1 n. rewrite Z.land_spec, !Z.lor_spec. bcases.
Qed.
Definition a_xor (A B : av) : option av :=
reduce 0 ones64 (Z.lor (Z.land (ak0 A) (ak0 B)) (Z.land (ak1 A) (ak1 B)))
(Z.lor (Z.land (ak1 A) (ak0 B)) (Z.land (ak0 A) (ak1 B))).
Lemma a_xor_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "M'QD'?&QLr5r2%3221'<'7%118&Q?r7r6%3221(3%12>;%93731&Q5(Gr4%332@1%B291p061p0A1p0B1pX2G1pWNH1p6J1p4K1p2L1").
Proof.
intros A B C x y (Hx & Ix & A0 & A1) (Hy & Iy & B0 & B1). cbn [zfast]. unfold a_xor.
pose proof (lxor_lt_two64 x y Hx Hy).
apply reduce_sound; try (rewrite ?ones64_eq; lia).
- apply Z.bits_inj'. intros n Hn. tb A0 n. tb B0 n. tb A1 n. tb B1 n.
rewrite !Z.land_spec, !Z.lor_spec, !Z.land_spec, Z.lxor_spec, Z.bits_0. bcases.
- apply Z.bits_inj'. intros n Hn. tb A0 n. tb B0 n. tb A1 n. tb B1 n.
rewrite !Z.land_spec, !Z.lor_spec, !Z.land_spec, Z.lxor_spec. bcases.
Qed.
Lemma known_point : ltac2:(TCodec.tc2 tcn__FxKnownBits "H'QD'?&QLr2r1%3221'<'4&R@&QBr3%211&Q@%113%6231(:%:3921r4%911%=3B91p041p0@1pX2E1p4G1").
Proof. intros B y (_ & Iy & _ & _) E. apply Z.eqb_eq in E. lia. Qed.
Lemma shamt_nonneg : ltac2:(TCodec.tc2 tcn__FxKnownBits "9'?&RBz&RAr1+QO%3221%6251pX281").
Proof. intros y. apply Z.land_nonneg. right. lia. Qed.
Definition a_srl (A B : av) : option av :=
if Z.eqb (alo B) (ahi B) then
let sh := Z.land (alo B) 63 in
reduce (Z.shiftr (alo A) sh) (Z.shiftr (ahi A) sh) (Z.shiftr (ak0 A) sh) (Z.shiftr (ak1 A) sh)
else None.
Lemma shiftr_mono : ltac2:(TCodec.tc2 tcn__FxKnownBits "B'?&RBzr1%3221r4r3%6221&ROr5%2214%3265%;221p061p0:1pW@?1pV:@1pV8A1").
Proof. intros a b n Hn H. rewrite !Z.shiftr_div_pow2 by exact Hn. apply Z.div_le_mono; [apply Z.pow_pos_nonneg; lia|exact H]. Qed.
Lemma shiftr_range : ltac2:(TCodec.tc2 tcn__FxKnownBits "F'?&RBzr1%3221';r3%6251&RE&Q3%2241%6241&ROr4%2218%>2=1%8227%<221p071p0?1pW@D1pWNE1").
Proof.
intros x n Hn Hx. split; [apply Z.shiftr_nonneg; lia|].
pose proof (shiftr_mono 0 x n Hn (proj1 Hx)). rewrite Z.shiftr_div_pow2 by exact Hn.
assert (0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
assert (x / 2 ^ n <= x) by (apply Z.div_le_upper_bound; [lia|nia]). lia.
Qed.
Lemma a_srl_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "M'QD'?&QLr5r2%3221'<'7%118&Q=r7r6%3221(3%12>;%93731&Q5(Er4%332@1%B291p061p0A1p0B1pX2G1pWNH1p6J1p4K1p2L1").
Proof.
intros A B C x y GA GB. unfold a_srl. destruct (Z.eqb (alo B) (ahi B)) eqn:E; [|discriminate].
rewrite <- (known_point B y GB E). destruct GA as (Hx & Ix & A0 & A1). cbn [zfast].
pose proof (shamt_nonneg y) as Hs. set (sh := Z.land y 63) in *.
apply reduce_sound.
- apply shiftr_range; assumption.
- split; apply shiftr_mono; lia.
- rewrite <- Z.shiftr_land, A0. apply Z.shiftr_0_l.
- rewrite <- Z.shiftr_land, A1. reflexivity.
Qed.
Definition a_sll (A B : av) : option av :=
if Z.eqb (alo B) (ahi B) then
let sh := Z.land (alo B) 63 in
let k0 := Z.lor (Z.land (Z.shiftl (ak0 A) sh) ones64) (Z.ones sh) in
let k1 := Z.land (Z.shiftl (ak1 A) sh) ones64 in
let hi := Z.shiftl (ahi A) sh in
if Z.ltb hi two64 then reduce (Z.shiftl (alo A) sh) hi k0 k1 else reduce 0 ones64 k0 k1
else None.
Lemma shiftl_mono : ltac2:(TCodec.tc2 tcn__FxKnownBits "B'?&RBzr1%3221r4r3%6221&RNr5%2214%3265%;221p061p0:1pW@?1pV:@1pV8A1").
Proof. intros a b n Hn H. rewrite !Z.shiftl_mul_pow2 by exact Hn. apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; lia|exact H]. Qed.
Lemma a_sll_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "M'QD'?&QLr5r2%3221'<'7%118&Q;r7r6%3221(3%12>;%93731&Q5(Cr4%332@1%B291p061p0A1p0B1pX2G1pWNH1p6J1p4K1p2L1").
Proof.
intros A B C x y GA GB. unfold a_sll. destruct (Z.eqb (alo B) (ahi B)) eqn:E; [|discriminate].
rewrite <- (known_point B y GB E). destruct GA as (Hx & Ix & A0 & A1). cbn [zfast].
pose proof (shamt_nonneg y) as Hs. set (sh := Z.land y 63) in *. rewrite land64_mod.
assert (Ew : Z.shiftl x sh mod two64 = Z.land (Z.shiftl x sh) ones64) by (unfold ones64; rewrite Z.land_ones by lia; reflexivity).
assert (K0 : Z.land (Z.shiftl x sh mod two64) (Z.lor (Z.land (Z.shiftl (ak0 A) sh) ones64) (Z.ones sh)) = 0).
{ rewrite Ew. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.lor_spec, Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases n sh) as [Hl|Hg].
- rewrite (Z.shiftl_spec_low x) by lia. reflexivity.
- rewrite !Z.shiftl_spec by lia. rewrite Z.ones_spec_high by lia. tb A0 (n - sh). bcases. }
assert (K1 : Z.land (Z.shiftl x sh mod two64) (Z.land (Z.shiftl (ak1 A) sh) ones64) = Z.land (Z.shiftl (ak1 A) sh) ones64).
{ rewrite Ew. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
destruct (Z.lt_ge_cases n sh) as [Hl|Hg].
- rewrite !Z.shiftl_spec_low by lia. reflexivity.
- rewrite !Z.shiftl_spec by lia. tb A1 (n - sh). bcases. }
pose proof (mod64_range (Z.shiftl x sh)) as Hw.
destruct (Z.ltb (Z.shiftl (ahi A) sh) two64) eqn:E1.
- apply Z.ltb_lt in E1. apply reduce_sound; try assumption. clear K0 K1 Ew Hw.
pose proof (shiftl_mono (alo A) x sh Hs (proj1 Ix)). pose proof (shiftl_mono x (ahi A) sh Hs (proj2 Ix)).
assert (0 <= Z.shiftl x sh) by (apply Z.shiftl_nonneg; lia).
apply mod_iv_small; lia.
- apply reduce_sound; try assumption. apply mod_iv_full.
Qed.
Definition a_sltu (A B : av) : option av :=
if Z.ltb (ahi A) (alo B) then Some (cst 1)
else if Z.leb (ahi B) (alo A) then Some (cst 0)
else reduce 0 1 (ones64 - 1) 0.
Lemma a_sltu_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "M'QD'?&QLr5r2%3221'<'7%118&Q<r7r6%3221(3%12>;%93731&Q5(Dr4%332@1%B291p061p0A1p0B1pX2G1pWNH1p6J1p4K1p2L1").
Proof.
intros A B C x y (Hx & Ix & _ & _) (Hy & Iy & _ & _). cbn [zfast]. unfold a_sltu.
assert (R0 : 0 <= 0 < two64) by (rewrite two64_eq; lia). assert (R1 : 0 <= 1 < two64) by (rewrite two64_eq; lia).
destruct (Z.ltb (ahi A) (alo B)) eqn:E1.
- apply Z.ltb_lt in E1. intros Q. injection Q as <-. assert (E : Z.ltb x y = true) by (apply Z.ltb_lt; lia).
rewrite E. apply cst_gam. exact R1.
- destruct (Z.leb (ahi B) (alo A)) eqn:E2.
+ apply Z.leb_le in E2. intros Q. injection Q as <-. assert (E : Z.ltb x y = false) by (apply Z.ltb_ge; lia).
rewrite E. apply cst_gam. exact R0.
+ destruct (Z.ltb x y); (apply reduce_sound; [assumption|lia|reflexivity|reflexivity]).
Qed.
Definition aop (op : aluop) (A B : av) : option av :=
match op with
| ALU_ADD => a_add A B | ALU_SUB => a_sub A B | ALU_AND => a_and A B | ALU_OR => a_or A B
| ALU_XOR => a_xor A B | ALU_SRL => a_srl A B | ALU_SLL => a_sll A B | ALU_SLTU => a_sltu A B
| _ => None
end.
Lemma aop_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q0'I'QD'?&QLr5r2%3221'<'7%118&QCr8r7r6%43321(3%12?<%:3831&Q5r9r4%332A1%C291p061p0B1p0C1pX2H1pWNI1p6K1p4L1p2M1pWBO1").
Proof.
intros op A B C x y GA GB H. destruct op; cbn [aop] in H; try discriminate;
eauto using a_add_sound, a_sub_sound, a_and_sound, a_or_sound, a_xor_sound, a_srl_sound, a_sll_sound, a_sltu_sound.
Qed.
Definition in64b (w : Z) : bool := if Z.leb 0 w then Z.ltb w two64 else false.
Lemma in64b_ok : ltac2:(TCodec.tc2 tcn__FxKnownBits "C'?'<'4&QMr1%211(:%63521';&RBzr2%3221&RE&Q3%2241%8241p0:1pWLB1").
Proof. intros w H. unfold in64b in H. destruct (Z.leb 0 w) eqn:E; [|discriminate]. apply Z.leb_le in E. apply Z.ltb_lt in H. lia. Qed.
Definition fold2 (f : Z -> Z -> Z) (A B : av) : option av :=
match pt A with
| Some x => match pt B with
| Some y => let w := f x y in if in64b w then Some (cst w) else None
| None => None
end
| None => None
end.
Lemma fold2_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q0'?p011p021'QD&QLr5r2%3221'<'7%117&QKr8r7r6%43321(3%12><%:3831r9r4%22@1%B281p051p0A1p0B1pX2J1pWNK1p6I1p4J1p2K1pVBM1").
Proof.
intros f A B C x y GA GB H. unfold fold2 in H.
destruct (pt A) as [x0|] eqn:EA; [|discriminate]. destruct (pt B) as [y0|] eqn:EB; [|discriminate].
rewrite (pt_gam A x x0 GA EA), (pt_gam B y y0 GB EB).
destruct (in64b (f x0 y0)) eqn:Ew; [|discriminate]. injection H as <-. apply cst_gam. apply in64b_ok. exact Ew.
Qed.
Definition fold1 (f : Z -> Z) (A : av) : option av :=
match pt A with
| Some x => let w := f x in if in64b w then Some (cst w) else None
| None => None
end.
Lemma fold1_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "J'?p011'QD&QLr3r1%3221'<'7%117&QJr5r4%3221(3%12=;%93731r6%11>%@271p041p0?1pWNF1p6E1p2F1pVBH1").
Proof.
intros f A C x GA H. unfold fold1 in H. destruct (pt A) as [x0|] eqn:EA; [|discriminate].
rewrite (pt_gam A x x0 GA EA). destruct (in64b (f x0)) eqn:Ew; [|discriminate]. injection H as <-.
apply cst_gam. apply in64b_ok. exact Ew.
Qed.
Definition c_alu (op : aluop) (A B : av) : option av :=
match fold2 (zfast op) A B with Some C => Some C | None => aop op A B end.
Lemma c_alu_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q0'I'QD'?&QLr5r2%3221'<'7%118&QEr8r7r6%43321(3%12?<%:3831&Q5r9r4%332A1%C291p061p0B1p0C1pX2H1pWNI1p6K1p4L1p2M1pWBO1").
Proof.
intros op A B C x y GA GB H. unfold c_alu in H. destruct (fold2 (zfast op) A B) as [C0|] eqn:E.
- injection H as <-. eapply fold2_sound; eassumption.
- eapply aop_sound; eassumption.
Qed.
Definition c_md (op : mulop) (A B : av) : option av :=
match fold2 (zfastm op) A B with
| Some C => Some C
| None => match op with M_MUL => a_mul A B | _ => None end
end.
Lemma c_md_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q0'J'QD'?&QLr5r2%3221'<'7%118&QFr8r7r6%43321(3%12?<%:3831&Q6r9r4%332A1%C291p061p0B1p0C1pX2H1pWNI1p6K1p4L1p2M1pWBO1").
Proof.
intros op A B C x y GA GB H. unfold c_md in H. destruct (fold2 (zfastm op) A B) as [C0|] eqn:E.
- injection H as <-. eapply fold2_sound; eassumption.
- destruct op; try discriminate. eapply a_mul_sound; eassumption.
Qed.
Fixpoint kbv (s : expr) (P : av) (e : expr) {struct e} : option av :=
if eqbL e s then Some P else
match e with
| ELit w => Some (cst (wrap64 w))
| EVar _ => None
| EAlu op a b =>
match kbv s P a with
| Some A => match kbv s P b with Some B => c_alu op A B | None => None end
| None => None
end
| EAluw op a b =>
match kbv s P a with
| Some A => match kbv s P b with Some B => fold2 (zfastw op) A B | None => None end
| None => None
end
| EMd op a b =>
match kbv s P a with
| Some A => match kbv s P b with Some B => c_md op A B | None => None end
| None => None
end
| EMdw op a b =>
match kbv s P a with
| Some A => match kbv s P b with Some B => fold2 (zmdw op) A B | None => None end
| None => None
end
| EExt sx l n a =>
match kbv s P a with
| Some A => fold1 (zext_fast sx l n) A
| None => None
end
| EBlob _ _ _ _ => None
end.
Section Sound.
Variables (s : expr) (P : av) (lo hi : Z).
Hypothesis P_ok : forall z, lo <= z <= hi -> gam P z.
Lemma kbv_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q9'O'QD'<'7%113&R3vSJvLr2%43321(3r1%22;1%;3941'?';&RBvSE%2217vS=%4291%6231'=%D19&Nr3r6%33E21%B2>A%K3621&QLr5%221E%B241qWLD1%=2E1p0?1pX6G1p0I1p2Q61pV@Q81").
Proof.
induction e as [w|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx l n a IHa|sx k i n];
intros A HA z Hz; cbn [kbv] in HA; cbn [evalS]; rewrite eqbL_eq in HA;
match goal with |- context [expr_eqb ?e0 s] => destruct (expr_eqb e0 s) end;
try (injection HA as <-; exists z; split; [reflexivity|apply P_ok; exact Hz]); try discriminate.
- injection HA as <-. eexists. split; [reflexivity|]. apply cst_gam. rewrite wrap64_mod. apply mod64_range.
- destruct (kbv s P a) as [A1|] eqn:Ka; [|discriminate]. destruct (kbv s P b) as [B1|] eqn:Kb; [|discriminate].
destruct (IHa A1 eq_refl z Hz) as (x & Ea & Ga). destruct (IHb B1 eq_refl z Hz) as (y & Eb & Gb).
rewrite Ea, Eb. eexists. split; [reflexivity|]. eapply c_alu_sound; eassumption.
- destruct (kbv s P a) as [A1|] eqn:Ka; [|discriminate]. destruct (kbv s P b) as [B1|] eqn:Kb; [|discriminate].
destruct (IHa A1 eq_refl z Hz) as (x & Ea & Ga). destruct (IHb B1 eq_refl z Hz) as (y & Eb & Gb).
rewrite Ea, Eb. eexists. split; [reflexivity|]. eapply fold2_sound; eassumption.
- destruct (kbv s P a) as [A1|] eqn:Ka; [|discriminate]. destruct (kbv s P b) as [B1|] eqn:Kb; [|discriminate].
destruct (IHa A1 eq_refl z Hz) as (x & Ea & Ga). destruct (IHb B1 eq_refl z Hz) as (y & Eb & Gb).
rewrite Ea, Eb. eexists. split; [reflexivity|]. eapply c_md_sound; eassumption.
- destruct (kbv s P a) as [A1|] eqn:Ka; [|discriminate]. destruct (kbv s P b) as [B1|] eqn:Kb; [|discriminate].
destruct (IHa A1 eq_refl z Hz) as (x & Ea & Ga). destruct (IHb B1 eq_refl z Hz) as (y & Eb & Gb).
rewrite Ea, Eb. eexists. split; [reflexivity|]. eapply fold2_sound; eassumption.
- destruct (kbv s P a) as [A1|] eqn:Ka; [|discriminate].
destruct (IHa A1 eq_refl z Hz) as (x & Ea & Ga).
rewrite Ea. eexists. split; [reflexivity|]. eapply fold1_sound; eassumption.
Qed.
End Sound.
Definition kb_mid (s : expr) (lo hi : Z) (e : expr) : option Z :=
match reduce lo hi 0 0 with
| Some P => match kbv s P e with
| Some A => if Z.eqb (alo A) (ahi A) then Some (alo A) else None
| None => None
end
| None => None
end.
Lemma kb_mid_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q;'O'?'<'7%113&QOr5r4r3r2%544321(3r1%22<1%<3:41&RBz%221;&RE&Q3%22>1';r8%821;r7%:2=1%5231&Nr:%231D5r6%D2N1%N3L31p071pX6Q11p0?1p0C1p0G1pWJQ51pV@Q71pVLQ71pW<Q81pWFQ:1").
Proof.
intros s lo hi e v H Hlo Hhi z Hz. unfold kb_mid in H.
destruct (reduce lo hi 0 0) as [P|] eqn:EP; [|discriminate].
destruct (kbv s P e) as [A|] eqn:EA; [|discriminate].
destruct (Z.eqb (alo A) (ahi A)) eqn:Eq; [|discriminate]. injection H as <-. apply Z.eqb_eq in Eq.
assert (P_ok : forall z0, lo <= z0 <= hi -> gam P z0).
{ intros z0 Hz0. eapply reduce_sound; [split; lia|exact Hz0|apply Z.land_0_r|apply Z.land_0_r|exact EP]. }
destruct (kbv_sound s P lo hi P_ok e A EA z Hz) as (w & Ew & _ & Iw & _). rewrite Ew. f_equal. lia.
Qed.
Lemma sweep_all : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q;'O'?'6';&RBr2r1%3221&RE&R=&RJr3%211%4281%6281%<281'<'7%11A&Nr7&Q4%11Ar6%53421(3r5%22J1%<3:41p0>1pX6M1'4&Mr4%25;81MG(:%D3521p071pW6Q51pV>Q51pWJQ71pV@Q91pWFQ:1").
Proof.
intros s e v. induction cnt as [|c IH]; intros l H; [reflexivity|]. cbn [all_eval_toS].
rewrite (H l) by lia. rewrite Z.eqb_refl. apply IH. intros z Hz. apply H. lia.
Qed.
Lemma kb_peel_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "QN'O'?&RBzr4%3221r5%5213&RE&RM+2+R0%3221%5271'<'7%11?&Nr8&Q4r7%211%5341@(3%12GD%;3931'4&Q2r9r6%3421H:(:%B3621&QOr:&R=+1%2291&S0%12E3%74631D%B2Q8<%L3J21&Mr;&S2%82B<%<21;%311%655OM?1%Q43H1Cp091p0D1p0L1p0Q91p0Q@1p0QC1pWJQH1pV@QJ1pVLQJ1pW<QK1pWFQM1").
Proof.
intros s lo hi e v Hlo Hle Hhi El Ph Hm. rewrite <- two64_eq in Hhi. apply sweep_all. intros z Hz.
rewrite Z2Nat.id in Hz by lia.
destruct (Z.eq_dec z lo) as [->|Nl]; [exact El|].
destruct (Z.eq_dec z hi) as [->|Nh].
- unfold probeS in Ph. destruct (evalS s (wrap64 hi) e) as [w|]; [|discriminate]. apply Z.eqb_eq in Ph. subst w. reflexivity.
- rewrite wrap64_id by lia. apply (kb_mid_sound s (lo + 1) (hi - 1) e v Hm); lia.
Qed.
Definition cand : Type := (expr * Z)%type.
Definition cand_of (e : expr) (r : option av) : option cand :=
match r with
| Some A => if Z.ltb 0 (alo A) then
(if Z.eqb (Z.log2 (alo A)) (Z.log2 (ahi A)) then None else Some (e, 2 ^ Z.log2 (ahi A)))
else None
| None => None
end.
Definition arith_op (op : aluop) : bool :=
match op with ALU_ADD | ALU_SUB | ALU_SRL | ALU_SLL => true | _ => false end.
Definition first_cand (a b c : option cand) : option cand :=
match a with Some x => Some x | None => match b with Some x => Some x | None => c end end.
Definition kbc2 (ra : option av * option cand) (rbf : unit -> option av * option cand)
(comb : av -> av -> option av) (mkc : option av -> option cand) : option av * option cand :=
match fst ra with
| Some A => let rb := rbf tt in
match fst rb with
| Some B => let r := comb A B in (r, first_cand (snd ra) (snd rb) (mkc r))
| None => (None, first_cand (snd ra) (snd rb) None)
end
| None => (None, snd ra)
end.
Lemma kbc2_fst : forall ra rbf comb mkc,
fst (kbc2 ra rbf comb mkc) = match fst ra with
| Some A => match fst (rbf tt) with Some B => comb A B | None => None end
| None => None
end.
Proof. intros ra rbf comb mkc. unfold kbc2. destruct (fst ra); [|reflexivity]. destruct (fst (rbf tt)); reflexivity. Qed.
Fixpoint kbc (s : expr) (P : av) (e : expr) {struct e} : option av * option cand :=
if eqbL e s then (Some P, cand_of e (Some P)) else
match e with
| ELit w => (Some (cst (wrap64 w)), None)
| EVar _ => (None, None)
| EAlu op a b => kbc2 (kbc s P a) (fun _ => kbc s P b) (c_alu op) (fun r => if arith_op op then cand_of e r else None)
| EAluw op a b => kbc2 (kbc s P a) (fun _ => kbc s P b) (fold2 (zfastw op)) (fun _ => None)
| EMd op a b => kbc2 (kbc s P a) (fun _ => kbc s P b) (c_md op) (fun r => match op with M_MUL => cand_of e r | _ => None end)
| EMdw op a b => kbc2 (kbc s P a) (fun _ => kbc s P b) (fold2 (zmdw op)) (fun _ => None)
| EExt sx l n a => let ra := kbc s P a in
(match fst ra with Some A => fold1 (zext_fast sx l n) A | None => None end, snd ra)
| EBlob _ _ _ _ => (None, None)
end.
Lemma kbc_fst : ltac2:(TCodec.tc2 tcn__FxKnownBits "D'O'QD'<'7%113&5&QG%411&R2r3r2r1%43321%83961&R3%13654%>3<31pV@A1pQJA1pWFC1").
Proof.
intros s P. induction e as [w|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx l n a IHa|sx k i n];
cbn [kbc kbv]; match goal with |- context [eqbL ?e0 s] => destruct (eqbL e0 s) end; try reflexivity;
try (rewrite kbc2_fst, IHa, IHb; reflexivity).
cbn [fst]. rewrite IHa. reflexivity.
Qed.
Definition kb_try (s : expr) (lo hi : Z) (e : expr) : option Z * option cand :=
match reduce lo hi 0 0 with
| Some P => let r := kbc s P e in
(match fst r with
| Some A => if Z.eqb (alo A) (ahi A) then Some (alo A) else None
| None => None
end, snd r)
| None => (None, None)
end.
Lemma kb_try_mid : ltac2:(TCodec.tc2 tcn__FxKnownBits "F'O'?'<'7%113&5&QG%411&R1r4r3r2r1%544321%93:71&QO%147654%?3=31pV@B1pVLB1pW<C1pWFE1").
Proof.
intros s lo hi e. unfold kb_try, kb_mid. destruct (reduce lo hi 0 0) as [P|]; [|reflexivity].
cbn [fst]. rewrite kbc_fst. reflexivity.
Qed.
Fixpoint bsearch (fuel : nat) (s g : expr) (T a b : Z) : Z :=
match fuel with
| O => b
| S f => if Z.leb (b - a) 1 then b
else let m := Z.div2 (a + b) in
match evalS s m g with
| Some w => if Z.leb T w then bsearch f s g T a m else bsearch f s g T m b
| None => b
end
end.
Definition split_at (s : expr) (lo hi : Z) (c : cand) : option Z :=
let '(g, T) := c in
match evalS s lo g with
| Some wl => match evalS s hi g with
| Some wh => if (if Z.ltb wl T then Z.leb T wh else false) then Some (bsearch 64 s g T lo hi) else None
| None => None
end
| None => None
end.
Fixpoint kb_split (fuel : nat) (s : expr) (lo hi : Z) (e : expr) {struct fuel} : option Z :=
let r := kb_try s lo hi e in
match fst r with
| Some v => Some v
| None =>
match fuel with
| O => None
| S f =>
match snd r with
| Some c =>
match split_at s lo hi c with
| Some z =>
if (if Z.ltb lo z then Z.leb z hi else false) then
match kb_split f s lo (z - 1) e with
| Some v1 => match kb_split f s z hi e with
| Some v2 => if Z.eqb v1 v2 then Some v1 else None
| None => None
end
| None => None
end
else None
| None => None
end
| None => None
end
end
end.
Lemma kb_split_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "Q='6'O'?'<'7%113&R0r6r5r3r2r4%6554321(3r1%22=1%=3;41&RBz%2218&RE&Q3%22;1';r7%821;%92<C%4221&Nr:r9%332E1%C2NI%N3L21p071pX6Q11p0>1p0B1p0F1pWJQ51pVLQ61pW<Q71pV@Q91pWFQ:1pVDQ<1").
Proof.
induction fuel as [|f IH]; intros s e lo hi v H Hlo Hhi z Hz; cbn [kb_split] in H;
rewrite kb_try_mid in H; destruct (kb_mid s lo hi e) as [v0|] eqn:E0;
try (injection H as <-; apply (kb_mid_sound s lo hi e v0 E0 Hlo Hhi z Hz)); try discriminate.
destruct (snd (kb_try s lo hi e)) as [c|]; [|discriminate].
destruct (split_at s lo hi c) as [z0|]; [|discriminate].
destruct (Z.ltb lo z0) eqn:E1; [|discriminate]. destruct (Z.leb z0 hi) eqn:E2; [|discriminate].
apply Z.ltb_lt in E1. apply Z.leb_le in E2.
destruct (kb_split f s lo (z0 - 1) e) as [v1|] eqn:K1; [|discriminate].
destruct (kb_split f s z0 hi e) as [v2|] eqn:K2; [|discriminate].
destruct (Z.eqb v1 v2) eqn:E3; [|discriminate]. injection H as <-. apply Z.eqb_eq in E3. subst v2.
destruct (Z.lt_ge_cases z z0) as [Hl|Hg].
- apply (IH s e lo (z0 - 1) v1 K1); lia.
- apply (IH s e z0 hi v1 K2); lia.
Qed.
Definition kb_const (s : expr) (lo hi : Z) (e : expr) : option Z := kb_split 3 s lo hi e.
Theorem kb_const_sound : ltac2:(TCodec.tc2 tcn__FxKnownBits "QB'O'?'<'7%113&QNr5r4r3r2%544321(3r1%22<1%<3:41&RBz%221;r6%421=&RE&RM+2+R0%3221%5271'4&Mr9r8&S2&R=&S0r7%2215+1%5221%711%;5:DQ091(:%Q63>21p0@1p0G1p0J1p0N1pWJQ<1pV@Q>1pVLQ>1pW<Q?1pWFQA1").
Proof.
intros s lo hi e v H Hlo Hle Hhi. rewrite <- two64_eq in Hhi. apply sweep_all. intros z Hz.
rewrite Z2Nat.id in Hz by lia. rewrite wrap64_id by lia.
apply (kb_split_sound 3 s e lo hi v H Hlo Hhi). lia.
Qed.
End KBF.
