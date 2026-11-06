(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q2qa Qy5Y Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import Q2qa.Mq2 Qy5Y.Mq2 Q2qa.Mq0 Qy5Y.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Local Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Definition f128_mul_entry := 0x11b2c%Z.

Section Model.
Variables a_lo a_hi b_lo b_hi : Z.
Let aExp := shr64 (shl64 a_hi 1) 49.
Let bExp := shr64 (shl64 b_hi 1) 49.
Let signHi := shl64 (shr64 (Z.lxor b_hi a_hi) 63) 63.
Let aSigHi := Z.land a_hi MASK48.
Let bSigHi := Z.land b_hi MASK48.
Let aAbsHi := Z.land a_hi ABS_HI.
Let bAbsHi := Z.land b_hi ABS_HI.

Definition FM_p2b (aSigHi1 aSigLo1 scale1 : Z) : Z :=
let '(bSigHi1, bSigLo1, scale2) :=
if shr64 bAbsHi 48 =? 0 then
let '(nbHi, nbLo, nbClz) := norm_denormal bSigHi b_lo in
(nbHi, nbLo, scale1 - nbClz + 16)
else (bSigHi, b_lo, scale1) in
mul_core signHi aExp bExp aSigHi1 aSigLo1 bSigHi1 bSigLo1 scale2.

Definition FM_p2 : Z :=
let '(aSigHi1, aSigLo1, scale1) :=
if shr64 aAbsHi 48 =? 0 then
let '(naHi, naLo, naClz) := norm_denormal aSigHi a_lo in
(naHi, naLo, 16 - naClz)
else (aSigHi, a_lo, 0) in
FM_p2b aSigHi1 aSigLo1 scale1.

Definition FM_inf : Z :=
if Z.lor (Z.lxor aAbsHi INF_HI) a_lo =? 0 then
(if negb (Z.lor b_lo bAbsHi =? 0) then mk128 (Z.lor signHi INF_HI) 0 else mk128 QNAN_HI 0)
else if Z.lor (Z.lxor bAbsHi INF_HI) b_lo =? 0 then
(if negb (Z.lor a_lo aAbsHi =? 0) then mk128 (Z.lor signHi INF_HI) 0 else mk128 QNAN_HI 0)
else if Z.lor a_lo aAbsHi =? 0 then mk128 signHi 0
else if Z.lor b_lo bAbsHi =? 0 then mk128 signHi 0
else FM_p2.

Definition FM_b : Z :=
let bIsNaN := if bAbsHi =? INF_HI then negb (b_lo =? 0) else negb (bAbsHi <? INF_HI) in
if bIsNaN then mk128 (Z.lor b_hi QUIET_HI) b_lo else FM_inf.

Definition FM_a : Z :=
let aIsNaN := if aAbsHi =? INF_HI then negb (a_lo =? 0) else negb (aAbsHi <? INF_HI) in
if aIsNaN then mk128 (Z.lor a_hi QUIET_HI) a_lo else FM_b.
Definition f128_mul_w : Z :=
let aExpM := add64 aExp 0xffffffffffff8001 in
let bExpM := add64 bExp 0xffffffffffff8001 in
if negb (orb (aExpM <? 0xffffffffffff8002) (bExpM <=? 0xffffffffffff8001))
then mul_core signHi aExp bExp aSigHi a_lo bSigHi b_lo 0
else FM_a.
End Model.

Lemma f128_mul_words : forall a_lo a_hi b_lo b_hi,
0 <= a_lo < 2^64 -> 0 <= a_hi < 2^64 -> 0 <= b_lo < 2^64 -> 0 <= b_hi < 2^64 ->
f128_mul (mk128 a_hi a_lo) (mk128 b_hi b_lo) = f128_mul_w a_lo a_hi b_lo b_hi.
Proof. intros. unfold f128_mul. rewrite !lo64_mk128, !hi64_mk128 by lia. reflexivity. Qed.

Lemma sgn_eq : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
Z.land (Z.shiftl (Z.shiftr (Z.lxor y x) 63) 63) 18446744073709551615 = Z.land (Z.lxor x y) 9223372036854775808.
Proof.
intros x y Hx Hy. rewrite (Z.lxor_comm y x).
apply Z.bits_inj'. intros i Hi.
rewrite !Z.land_spec.
change 9223372036854775808 with (2^63). rewrite Z.pow2_bits_eqb by lia.
change 18446744073709551615 with (Z.ones 64).
destruct (Z.lt_ge_cases i 63).
- rewrite Z.shiftl_spec_low by lia. rewrite (proj2 (Z.eqb_neq 63 i)) by lia.
rewrite andb_false_r. reflexivity.
- rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 63 + 63) with i by lia.
destruct (Z.eq_dec i 63) as [->|].
+ rewrite Z.ones_spec_low by lia. reflexivity.
+ rewrite (proj2 (Z.eqb_neq 63 i)) by lia. rewrite andb_false_r.
rewrite Z.ones_spec_high by lia. apply andb_false_r.
Qed.

Lemma lxor_b2z_1 : forall b, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof. intros [|]; reflexivity. Qed.

Lemma nd_hi_range : forall h l, 0 <= l < 2^64 -> 0 <= nd_hi h l < 2^64.
Proof.
intros h l Hl. unfold nd_hi, norm_denormal, shl128_mirror.
destruct (is_neg64 _).
- apply Z_lor_range. apply QZAi.wrap64_range. apply (zr_shiftr (Z.shiftr l 1)); [apply (zr_shiftr l 1); [exact Hl|lia] | apply Z.land_nonneg; right; lia].
- apply QZAi.wrap64_range.
Qed.
Lemma nd_lo_range : forall h l, 0 <= nd_lo h l < 2^64.
Proof.
intros h l. unfold nd_lo, norm_denormal, shl128_mirror.
apply (zr_land_r _ _). { unfold sra63, ONES64. destruct (is_neg64 _); lia. } apply QZAi.wrap64_range.
Qed.

Section Walk.
Variables (sp a0 a1 a2 a3 : word).

Definition saved (s5 s4 s3 s2 s1 s0 ra : word) (j : list byte) : list cell :=
[CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

End Walk.

End Mq0.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 QnDM_c1 QZAi QUZl Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition smear (s : Z) : Z :=
let m1 := Z.lor s (Z.shiftr s 1) in
let m2 := Z.lor m1 (Z.shiftr m1 2) in
Z.lor m2 (Z.shiftr m2 4).

#[using="Type"] Lemma fold_off_eq off slack :
fold_off off slack =
(if slack <? off then
let x := Z.land off (smear slack) in if slack <? x then x - (slack + 1) else x
else off).
Proof. reflexivity. Qed.

#[using="Type"] Lemma smear_nonneg s : 0 <= s -> 0 <= smear s.
Proof.
intros. unfold smear.
repeat (apply Z.lor_nonneg; split); repeat apply Z.shiftr_nonneg; repeat (apply Z.lor_nonneg; split);
repeat apply Z.shiftr_nonneg; try lia; repeat (apply Z.lor_nonneg; split); try apply Z.shiftr_nonneg; try lia.
all: try (apply Z.lor_nonneg; split); try apply Z.shiftr_nonneg; try lia.
Qed.

#[using="Type"] Lemma land_le_l a b : 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof.
intros. rewrite <- (Z.lor_ldiff_and a b) at 2.
assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; lia).
assert (0 <= Z.land a b) by (apply Z.land_nonneg; lia).
assert (Z.land (Z.ldiff a b) (Z.land a b) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor by assumption. lia.
Qed.

Definition zseq (a n : Z) : list Z := map Z.of_nat (seq (Z.to_nat a) (Z.to_nat n)).

Definition fold_fn1 (s off : Z) : bool :=
let x := Z.land off (smear s) in (negb (s <? x)) || (x - (s + 1) <=? s).
Definition fold_fn (s : Z) : bool := forallb (fold_fn1 s) (zseq 0 256).
Definition fold_check : bool := forallb fold_fn (zseq 0 128).

#[using="Type"] Lemma fold_check_true : forallb fold_fn (zseq 0 128) = true.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma forallb_zseq (f : Z -> bool) a n x : forallb f (zseq a n) = true -> 0 <= a -> a <= x < a + n -> f x = true.
Proof.
intros H Ha Hx. unfold zseq in H. rewrite forallb_forall in H. apply H.
apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

#[using="Type"] Lemma fold_assert_ok off slack : 0 <= off < 256 -> 0 <= slack ->
slack < Z.land off (smear slack) -> Z.land off (smear slack) - (slack + 1) <= slack.
Proof.
intros Ho Hs Hlt.
pose proof (smear_nonneg slack Hs) as Sm.
assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
destruct (Z.lt_ge_cases slack 128).
- pose proof (forallb_zseq fold_fn 0 128 slack fold_check_true ltac:(lia) ltac:(lia)) as H1. unfold fold_fn in H1.
pose proof (forallb_zseq (fold_fn1 slack) 0 256 off H1 ltac:(lia) ltac:(lia)) as H2. unfold fold_fn1 in H2. cbv zeta in H2.
apply orb_prop in H2. destruct H2 as [H2|H2].
+ apply negb_true_iff in H2. apply Z.ltb_ge in H2. lia.
+ apply Z.leb_le in H2. exact H2.
- lia.
Qed.

#[using="Type"] Lemma fold_off_range off slack : 0 <= off < 256 -> 0 <= slack -> 0 <= fold_off off slack <= Z.max slack off /\ fold_off off slack < 256.
Proof.
intros Ho Hs. rewrite fold_off_eq. pose proof (smear_nonneg slack Hs) as Sm.
assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
assert (LB : 0 <= Z.land off (smear slack)) by (apply Z.land_nonneg; lia).
destruct (Z.ltb_spec slack off); [|lia]. cbv zeta.
destruct (Z.ltb_spec slack (Z.land off (smear slack))); [|lia].
pose proof (fold_assert_ok off slack Ho Hs ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma fold_off_le_slack off slack : 0 <= off < 256 -> 0 <= slack -> 0 <= fold_off off slack <= slack.
Proof.
intros Ho Hs. rewrite fold_off_eq. pose proof (smear_nonneg slack Hs) as Sm.
assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
assert (LB : 0 <= Z.land off (smear slack)) by (apply Z.land_nonneg; lia).
destruct (Z.ltb_spec slack off); [|lia]. cbv zeta.
destruct (Z.ltb_spec slack (Z.land off (smear slack))); [|lia].
pose proof (fold_assert_ok off slack Ho Hs ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma land_126 y : Z.land y 126 = 2 * Z.land (Z.shiftr y 1) 63.
Proof.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.eq_dec i 0) as [->|].
- rewrite Z.testbit_even_0. change 126 with (2 * 63). rewrite Z.testbit_even_0. apply andb_false_r.
- replace i with (Z.succ (i - 1)) by lia. rewrite Z.testbit_even_succ by lia.
change 126 with (2 * 63). rewrite Z.testbit_even_succ by lia. rewrite Z.land_spec, Z.shiftr_spec by lia.
replace (i - 1 + 1) with i by lia. replace (Z.succ (i - 1)) with i by lia. reflexivity.
Qed.

#[using="Type"] Lemma mword_sc last_idx freeable sc maplen :
0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen ->
Z.land (Z.shiftr (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) 5) 126 = 2 * sc.
Proof.
intros. rewrite land_126. rewrite Z.shiftr_shiftr, !Z.shiftr_div_pow2 by lia. change (2 ^ (5 + 1)) with 64.
change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2^6) with 64.
replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) / 64) with (sc + 64 * maplen) by (Z.div_mod_to_equations; lia).
replace ((sc + 64 * maplen) mod 64) with sc by (Z.div_mod_to_equations; lia). reflexivity.
Qed.
End RC__1.

Ltac sdk :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
let E := addr_expr a in
(lazymatch a with
| wa _ => idtac
| Z_to_bv 64 _ => change (write_to_mem m a bs) with (write_to_mem m (wa E) bs)
| _ => replace (write_to_mem m a bs) with (write_to_mem m (wa E) bs) by (f_equal; addr_eq_tac)
end);
(try lazymatch goal with
| HI : mem_inv segs m, HS : store_ok segs m ?a' ?n = true |- _ =>
apply (mem_inv_store segs m (wa E) bs) in HI;
[ | first [ exact HS
| replace (wa E) with a' by (first [reflexivity | addr_eq_tac | symmetry; addr_eq_tac]);
first [ exact HS | simpl_sizes; exact HS ] ] ]
end);
transport_chunks segs m E bs;
repeat match goal with
| STq : stk segs m ?loq ?hiq |- _ =>
first [ apply (stk_write segs m loq hiq E bs) in STq; [ | lia | simpl_sizes; slia ]
| fail 100 "sdk: cannot transport stk hypothesis" STq ]
| MU : munch ?Wq ?mq m |- _ =>
first [ apply (munch_write Wq mq m E bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
| fail 100 "sdk: store outside the declared footprint" ]
| WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa E) bs) in WMo
end;
repeat match goal with
| H : store_ok segs m _ _ = true |- _ => clear H
| H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
end;
let m' := fresh "m" in let Eq := fresh "EQ" m' in
remember (write_to_mem m (wa E) bs) as m' eqn:Eq
end.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma le1_wz v : 0 <= v < 256 -> le1 (wz v) = [b8 v].
Proof. intros. cbn. rewrite (wz_unsigned v) by lia. reflexivity. Qed.

#[using="Type"] Lemma le1_neg32 : le1 (Z_to_bv 64 (-32)) = [b8 224].
Proof. cbn. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.

Definition enframe_tail_mem (m : word -> option byte) (P E n k q : Z) : word -> option byte :=
let m1 := write_to_mem m (wa (P - 2)) (le2 (wz q)) in
let m2 := write_to_mem m1 (wa (P - 3)) [b8 k] in
let r := E - P - n in
let m3 := if r =? 0 then m2 else write_to_mem m2 (wa (E - r)) [b8 0] in
let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 4)) (le4 (wz r))) (wa (E - 5)) [b8 0], 5) else (m3, r) in
write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)].

Definition enframe_off_mem (m : word -> option byte) (P0 off : Z) : word -> option byte :=
if off =? 0 then m
else write_to_mem (write_to_mem (write_to_mem m (wa (P0 - 2)) (le2 (wz off))) (wa (P0 - 3)) [b8 224])
(wa (P0 + 16 * off - 4)) [b8 0].

Section FASTMODEL.
Context {O : Type}.
Variable pans : O -> aptr -> Z -> Z -> Z.
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.
Let pupd : O -> ev -> Z -> O := fun o _ _ => o.
Local Notation prun := (prun pans pupd).

Definition rdv (o : O) (st : mstate) (q : aptr) : Z :=
match cell_read (get_shadow st (fst q)) (snd q) with
| Known v => v
| Unknown h => pans o q (conc st q) h
end.

#[using="Hpans"] Lemma rd8_oracle {R} o st q (k : Z -> M R) : prun o (rd8 st q k) = prun o (k (rdv o st q)).
Proof.
unfold rd8, rdv. destruct (cell_read _ _) as [v|h]; [reflexivity|].
unfold Q7S0.Mq0.prun. cbn [eruns psel].
pose proof (Hpans o q (conc st q) h).
replace (peek_answer_ok (pans o q (conc st q) h)) with true.
2:{ symmetry. unfold peek_answer_ok. apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
reflexivity.
Qed.

#[using="Hpans"] Lemma rd16_oracle {R} o st q (k : Z -> M R) :
prun o (rd16 st q k) = prun o (k (rdv o st q + 256 * rdv o st (aadd q 1))).
Proof. unfold rd16. rewrite rd8_oracle, rd8_oracle. reflexivity. Qed.

#[using="Type"] Lemma land_opp_pow2' k : 0 <= k -> Z.land (2 ^ k) (- 2 ^ k) = 2 ^ k.
Proof.
intros Hk. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
destruct (Z.eqb_spec k i); cbn [andb]; [|reflexivity].
subst. replace (i <? i) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? i); reflexivity.
Qed.
#[using="Type"] Lemma ctz32_pow2' k : 0 <= k -> ctz32 (2 ^ k) = k.
Proof. intros. unfold ctz32, lowbit. rewrite land_opp_pow2' by lia. apply Z.log2_pow2. lia. Qed.

#[using="Type"] Lemma get_meta_rec_upd_same st g f : get_meta_rec (upd_meta g f st) g = f (get_meta_rec st g).
Proof. unfold get_meta_rec at 1. unfold upd_meta, put_meta. cbn. rewrite lookup_insert_eq. reflexivity. Qed.

#[using="Type"] Lemma malloc_core_fast st n g k :
let sc := size_to_class n in
let mr := get_meta_rec st g in
size_overflows n = false -> n < MMAP_THRESHOLD ->
active st sc = Some g -> 0 < m_avail mr -> 0 <= k -> lowbit (m_avail mr) = 2 ^ k ->
malloc_core full_lay st n = ret (upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st, Some (g, k)).
Proof.
intros sc mr OV TH ACT AV K0 LB.
unfold malloc_core. rewrite OV. replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
unfold malloc_small_ctrl. fold sc. rewrite ACT. rewrite ACT. fold mr. rewrite LB.
assert (P : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
replace (2 ^ k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
rewrite ctz32_pow2' by lia. reflexivity.
Qed.

#[using="Hpans"] Lemma malloc_fast_model o st n g k :
let sc := size_to_class n in
let st1 := set_tick (N.succ (s_tick st)) st in
let mr := get_meta_rec st1 g in
let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1 in
let stride := get_stride mr in
let slack := (stride - IB - n) / UNIT in
let p0 := slot_start' mr k in
let ctr := c_mmap_counter (ctx st) in
let b3 := rdv o st2 (aadd p0 (-3)) in
let v16 := rdv o st2 (aadd p0 (-2)) + 256 * rdv o st2 (aadd (aadd p0 (-2)) 1) in
let off0 := (if b3 =? 0 then Z.land ctr 255 else Z.land (v16 + 1) 255) in
let off := fold_off off0 slack in
size_overflows n = false -> n < MMAP_THRESHOLD ->
active st sc = Some g -> 0 < m_avail mr -> 0 <= k -> lowbit (m_avail mr) = 2 ^ k ->
prun o (malloc st n) = SRet (o, (havoc (snd (enframe_at st2 g k n off)) n (fst (enframe_at st2 g k n off)),
Some (snd (enframe_at st2 g k n off)))).
Proof.
intros sc st1 mr st2 stride slack p0 ctr b3 v16 off0 off OV TH ACT AV K0 LB.
unfold malloc. fold st1.
rewrite (malloc_core_fast st1 n g k OV TH ACT AV K0 LB). unfold QUZl.ret. rewrite sbind_ret_l.
unfold enframe_full, enframe_read_off. fold st2. rewrite (get_meta_rec_upd_same st1 g). fold mr.
set (K := fun off' : Z => let '(st3, p) := enframe_at st2 g k n off' in @SRet ev Z _ (havoc p n st3, Some p)).
change (prun o (rd8 st2 (aadd p0 (-3)) (fun b => if negb (b =? 0)
then rd16 st2 (aadd p0 (-2)) (fun o16 => K (fold_off (Z.land (o16 + 1) 255) slack))
else K (fold_off (Z.land ctr 255) slack)))
= SRet (o, (havoc (snd (enframe_at st2 g k n off)) n (fst (enframe_at st2 g k n off)), Some (snd (enframe_at st2 g k n off))))).
rewrite rd8_oracle. cbv beta. fold b3.
assert (FIN : forall off', off' = off -> prun o (K off') = SRet (o, (havoc (snd (enframe_at st2 g k n off)) n (fst (enframe_at st2 g k n off)), Some (snd (enframe_at st2 g k n off))))).
{ intros off' ->. unfold K. destruct (enframe_at st2 g k n off) as [st3 p]. reflexivity. }
destruct (Z.eqb_spec b3 0) as [E|NE]; cbn [negb].
- apply FIN. unfold off, off0. replace (b3 =? 0) with true by (symmetry; apply Z.eqb_eq; exact E). reflexivity.
- rewrite rd16_oracle. cbv beta. apply FIN. unfold off, off0. replace (b3 =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
Qed.
End FASTMODEL.
End RC__2.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QytA.
Import Qy5Y.Mq6.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition fm_facts (st : mstate) (g : aptr) : Prop :=
forall head, c_free_meta_head (ctx st) = Some head ->
head <> g /\ meta_slot st head /\
exists pv, m_prev (get_meta_rec st head) = Some pv /\ pv <> g /\ meta_slot st pv.

#[using="Type"] Lemma meta_word_meta0 : meta_word meta0 = 0. Proof. reflexivity. Qed.

End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 QGeV.
Import QnDM_c1.Mq0 QytA.
Export Qy5Y.Mq4.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition HINV_from (resv : list (Z * Z)) (sec : Z) (st : mstate) (pbrk : Z) (LB : list block) : Prop :=
brk_link st pbrk /\ AREACH_from resv sec st LB.
End RC__1.
Notation HINV := (HINV_from agent_reserved 0).
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma HINV_from_init : forall resv sec pbrk, 0 <= sec < 2^64 -> HINV_from resv sec (minit sec resv) pbrk [].
Proof. intros. split; [exact I | apply areach_init; assumption]. Qed.

#[using="Type"] Lemma HINV_init : forall pbrk, HINV (minit 0 agent_reserved) pbrk [].
Proof. intros. apply HINV_from_init. lia. Qed.

Definition ps_init_s (sec : Z) (reserved : list (Z * Z)) : PState := mkPS (strip (minit sec reserved)) 0 tt tt.
#[using="Type"] Lemma ps_init_s_0 reserved : ps_init_s 0 reserved = ps_init reserved.
Proof. reflexivity. Qed.

#[using="Type"] Lemma brk_link_ps_iff : forall st s, brk_link_ps st s <-> brk_link st (ps_brk s).
Proof. intros st s. unfold brk_link_ps, brk_link. destruct (c_brk (ctx st)); tauto. Qed.

End RC__2.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QnDM_c1.Mq0 Qy5Y.Mq6.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition aor_st (st : mstate) (g : aptr) (i : Z) : mstate :=
upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st.

Definition act_st (st : mstate) (a : aptr) (act : Z) : mstate :=
upd_meta a (fun r => m_set_avail (Z.land (m_freed r) act) (m_set_freed (Z.ldiff (m_freed r) act) r)) st.
Definition act_of (st : mstate) (a : aptr) : Z :=
match m_mem (get_meta_rec st a) with
| Some _ => mask_upto (group_active_idx st (default (0%N, -1) (m_mem (get_meta_rec st a))))
| None => 0 end.

#[using="Type"] Lemma activate_group_eq {R} a st (k : mstate -> Z -> M R) bail :
m_avail (get_meta_rec st a) = 0 ->
activate_group a st k bail = k (act_st st a (act_of st a)) (Z.land (m_freed (get_meta_rec st a)) (act_of st a)).
Proof. intros H. unfold activate_group, guard, act_of, act_st. rewrite H. reflexivity. Qed.

Definition deq_mid (h : lhead) (g : aptr) (st : mstate) : mstate :=
let mr := get_meta_rec st g in
if negb (optr_eqb (m_next mr) (Some g)) then
let st1 := match m_prev mr with Some pv => upd_meta pv (m_set_next (m_next mr)) st | None => st end in
let st2 := match m_next mr with Some nx => upd_meta nx (m_set_prev (m_prev mr)) st1 | None => st1 end in
if optr_eqb (get_head st2 h) (Some g) then set_head h (m_next mr) st2 else st2
else set_head h None st.
Definition clr_links (r : meta) : meta := m_set_prev None (m_set_next None r).
#[using="Type"] Lemma dequeue_mid : forall h g st, dequeue h g st = upd_meta g clr_links (deq_mid h g st).
Proof. reflexivity. Qed.

Definition pd_st (an : bool) (st1 : mstate) (sc : Z) : mstate :=
if an then match active st1 sc with Some a => act_st st1 a (act_of st1 a) | None => st1 end else st1.

Definition grp_del (st : mstate) (g p : aptr) : mstate :=
del_slots p (get_stride (get_meta_rec st g)) (m_last_idx (get_meta_rec st g) + 1) (del_group p st).
Definition fg_usage_st (st : mstate) (g : aptr) : mstate :=
let mr := get_meta_rec st g in
if m_sizeclass mr <? 48 then set_usage (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) st else st.

End RC__1.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq3.
Import ListNotations. Unset Keyed Unification.
Local Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Definition saved_dc (bSigHiI : Z) (bLo s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) (j : list byte) : list cell :=
[C8 (Z_to_bv 64 bSigHiI); C8 bLo; CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Ltac sf_vocab ::=
cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
is_neg64 sra63 lt_s64 lo64 hi64 wrap64
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI IMPL3_HI SPEC_K HALF60 DQUIET
C_HW X_ADJ EXPK EXPK2];
rewrite ?b2z_Zb2z. Ltac mkr__sf_vocab_6 := cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
is_neg64 sra63 lt_s64 lo64 hi64 wrap64
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI IMPL3_HI SPEC_K HALF60 DQUIET
C_HW X_ADJ EXPK EXPK2];
rewrite ?b2z_Zb2z.

Ltac folded_check :=
lazymatch goal with
| |- (let x := ?b in _) = _ => fail 0 "fold_model_lets stuck at a let with body" b
| |- _ => idtac
end.

Lemma carry_gcc : forall r0c r1, 0 <= r0c < 2^64 -> 0 <= r1 < 2^64 ->
Z.b2z (Z.land (r0c + r1) 18446744073709551615 <? r0c)
= Z.land (Z.land (Z.b2z (Z.lxor r1 (Z.lxor r0c 18446744073709551615) =? 0) - 1) 18446744073709551615) (Z.b2z (Z.lxor r0c 18446744073709551615 <? r1)).
Proof.
intros r0c r1 H0 H1. rewrite zb_lxor_ones by lia.
rewrite zb_lxor_eqb0. rewrite !land_W64.
destruct (Z.eqb_spec r1 (18446744073709551615 - r0c)) as [E|NE].
- cbn [Z.b2z]. rewrite Z.land_0_l.
replace ((r0c + r1) mod 2^64 <? r0c) with false; [reflexivity|]. symmetry. apply Z.ltb_ge.
Z.div_mod_to_equations. lia.
- cbn [Z.b2z]. change ((0 - 1) mod 2 ^ 64) with 18446744073709551615.
rewrite land_ones_l by (destruct (_ <? _); cbv; split; congruence).
f_equal. apply eq_true_iff_eq. rewrite !Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.

Ltac carry_fix r0c r1 nr0c ltc eqx neMask :=
match goal with |- context [Z_to_bv 64 (Z.b2z (Z.land (r0c + r1) 18446744073709551615 <? r0c))] =>
replace (Z_to_bv 64 (Z.b2z (Z.land (r0c + r1) 18446744073709551615 <? r0c))) with (Z_to_bv 64 (Z.land neMask ltc))
by (f_equal; subst neMask eqx ltc nr0c; symmetry; apply carry_gcc; assumption)
end.

