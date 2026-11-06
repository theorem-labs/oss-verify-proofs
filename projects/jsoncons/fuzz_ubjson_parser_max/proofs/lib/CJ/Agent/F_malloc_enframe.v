(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_malloc_enframe () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_enframe.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1false"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "3Z"; "0RUNp"; "4fold_fn"; "4smear"]; ["4zseq"; "5b8"; "5wz"; "6le1"; "7M"; "7MMAP_THRESHOLD"; "7active"; "7aptr"; "7ctz32"; "7fold_off"; "7full_lay"; "7get_meta_rec"; "7lowbit"; "7m_avail"; "7m_set_avail"; "7malloc_core"]; ["7meta"; "7mstate"; "7optr"; "7ret"; "7size_overflows"; "7size_to_class"; "7upd_meta"; "8forallb"; "9add"; "9land"; "9le"; "9lt"; "9max"; "9mul"; "9opp"; "9pow"]; ["9shiftr"; "9sub"; "0a"; "0b"; "0f"; "0freeable"; "0g"; "0k"; "0last_idx"; "0maplen"; "0mr"; "0n"; "0off"; "0s"; "0sc"; "0slack"]; ["0st"; ":Z_to_bv"; ":bv"; "0v"; "0x"; "0y"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition smear (s : Z) : Z :=
let m1 := Z.lor s (Z.shiftr s 1) in
let m2 := Z.lor m1 (Z.shiftr m1 2) in
Z.lor m2 (Z.shiftr m2 4).
Lemma fold_off_eq off slack :
fold_off off slack =
(if slack <? off then
let x := Z.land off (smear slack) in if slack <? x then x - (slack + 1) else x
else off).
Proof. reflexivity. Qed.
Lemma smear_nonneg : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_enframe ";'<&Q:zr1%3221&?r2%211%7261p051pSL:1").
Proof. intros s.
intros. unfold smear.
repeat (apply Z.lor_nonneg; split); repeat apply Z.shiftr_nonneg; repeat (apply Z.lor_nonneg; split);
repeat apply Z.shiftr_nonneg; try lia; repeat (apply Z.lor_nonneg; split); try apply Z.shiftr_nonneg; try lia.
all: try (apply Z.lor_nonneg; split); try apply Z.shiftr_nonneg; try lia.
Qed.
Lemma land_le_l : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_enframe ">'<&Q:zr2%3221&Q9r4r3%3221%8213p061p071pS8<1pS6=1").
Proof. intros a b.
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
Lemma fold_check_true : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_enframe "<';'1&Q7'<&>&@z+T0%3221%73651(9%;3:21").
Proof. vm_compute. reflexivity. Qed.
Lemma forallb_zseq : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_enframe "Q2'<'1p021';&Q7r4&@r3r2%3221%63:51(9%93;21&Q:z%221:':r5%521;&Q;&Q8%124@%32?1%7251r7%11D%G3I1?p041p0=1p0A1pT:N1pSHO1pS6Q01pS:O1").
Proof. intros f a n x.
intros H Ha Hx. unfold zseq in H. rewrite forallb_forall in H. apply H.
apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.
Lemma fold_assert_ok : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_enframe "O'<':&Q:zr2%3221&Q;+X0%2241%8241r3&Q9r4&?%114%4231%:261&QAr5%617%9221&Q8+1%22;1%7241%G21=p0:1p0F1p0C1pT0M1pSJN1").
Proof. intros off slack.
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
Lemma fold_off_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_enframe "I'<':&Q:zr2%3221&Q;+X0%2241%8241&Ir4r3%3221%<2;1&Q<%1245%?241%A241%=26<%C221p0@1p0=1pT0G1pSJH1").
Proof. intros off slack.
intros Ho Hs. rewrite fold_off_eq. pose proof (smear_nonneg slack Hs) as Sm.
assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
assert (LB : 0 <= Z.land off (smear slack)) by (apply Z.land_nonneg; lia).
destruct (Z.ltb_spec slack off); [|lia]. cbv zeta.
destruct (Z.ltb_spec slack (Z.land off (smear slack))); [|lia].
pose proof (fold_assert_ok off slack Ho Hs ltac:(lia)). lia.
Qed.
Lemma fold_off_le_slack : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_enframe "E'<':&Q:zr2%3221&Q;+X0%2241%8241&Ir4r3%3221%<2;1%=223%?221p0<1p091pT0C1pSJD1").
Proof. intros off slack.
intros Ho Hs. rewrite fold_off_eq. pose proof (smear_nonneg slack Hs) as Sm.
assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
assert (LB : 0 <= Z.land off (smear slack)) by (apply Z.land_nonneg; lia).
destruct (Z.ltb_spec slack off); [|lia]. cbv zeta.
destruct (Z.ltb_spec slack (Z.land off (smear slack))); [|lia].
pose proof (fold_assert_ok off slack Ho Hs ltac:(lia)). lia.
Qed.
Lemma land_126 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_enframe "@'<';&Q9r1+SN%3221&Q=+2&Q@+1%2271+QO%:221%7261%=3>91pT<?1").
Proof. intros y.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.eq_dec i 0) as [->|].
- rewrite Z.testbit_even_0. change 126 with (2 * 63). rewrite Z.testbit_even_0. apply andb_false_r.
- replace i with (Z.succ (i - 1)) by lia. rewrite Z.testbit_even_succ by lia.
change 126 with (2 * 63). rewrite Z.testbit_even_succ by lia. rewrite Z.land_spec, Z.shiftr_spec by lia.
replace (i - 1 + 1) with i by lia. replace (Z.succ (i - 1)) with i by lia. reflexivity.
Qed.
Lemma mword_sc : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_enframe "Q>'<':&Q:zr4%3221&Q;+Q0%2241%8241+2%5271%;271+R0%82:1%>2:1';&Q9&Q@&Q8r8&Q=r7%22@1%5241r6%52=1%8231+TP0r5%9221%<241+5%?221+SN%B221%?2J;%E3Q521p0Q11p0H1p0L1p0Q01pSDQ:1pSNQ;1pS<Q<1pSBQ=1").
Proof. intros last_idx freeable sc maplen.
intros. rewrite land_126. rewrite Z.shiftr_shiftr, !Z.shiftr_div_pow2 by lia. change (2 ^ (5 + 1)) with 64.
change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2^6) with 64.
replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) / 64) with (sc + 64 * maplen) by (Z.div_mod_to_equations; lia).
replace ((sc + 64 * maplen) mod 64) with sc by (Z.div_mod_to_equations; lia). reflexivity.
Qed.
End CEIL_WRAP_1.
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
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Lemma le1_wz : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_enframe "N'<':&Q:zr1%3221&Q;+X0%2241%8241';'4'R2y8%211%411&C&Br2%211%411(2&A%115(5%11;%53<31%A3<71p0C1pT8M1").
Proof. intros v. intros. cbn. rewrite (wz_unsigned v) by lia. reflexivity. Qed.
Lemma le1_neg32 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_enframe "D';'4'R2y8%211%411&C&R1yR0-Q0%3221%511(2&A+W0%211(5%11=%63>31%C3>81").
Proof. cbn. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.
Definition enframe_tail_mem (m : word -> option byte) (P E n k q : Z) : word -> option byte :=
let m1 := write_to_mem m (wa (P - 2)) (le2 (wz q)) in
let m2 := write_to_mem m1 (wa (P - 3)) [b8 k] in
let r := E - P - n in
let m3 := if r =? 0 then m2 else write_to_mem m2 (wa (E - r)) [b8 0] in
let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 4)) (le4 (wz r))) (wa (E - 5)) [b8 0], 5) else (m3, r) in
write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)].
Definition en3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) (P E n k q : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 pw a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ m' = enframe_tail_mem m P E n k q
/\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).
Definition enframe_off_mem (m : word -> option byte) (P0 off : Z) : word -> option byte :=
if off =? 0 then m
else write_to_mem (write_to_mem (write_to_mem m (wa (P0 - 2)) (le2 (wz off))) (wa (P0 - 3)) [b8 224])
(wa (P0 + 16 * off - 4)) [b8 0].
Definition mfw_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) (G avail k P0 stride B n off : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 m3 m4 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P0 + 16 * off)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m1 /\ wmono asegs m m1
/\ m3 = write_to_mem m1 (wa (G + 24)) (le4 (wz (avail - 2 ^ k)))
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m3 m4 /\ wmono asegs m3 m4
/\ m' = enframe_tail_mem (enframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16)
/\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).
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
Lemma rd8_oracle {R} o st q (k : Z -> M R) : prun o (rd8 st q k) = prun o (k (rdv o st q)).
Proof.
unfold rd8, rdv. destruct (cell_read _ _) as [v|h]; [reflexivity|].
unfold MallocCtrl.prun. cbn [eruns psel].
pose proof (Hpans o q (conc st q) h).
replace (peek_answer_ok (pans o q (conc st q) h)) with true.
2:{ symmetry. unfold peek_answer_ok. apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
reflexivity.
Qed.
Lemma rd16_oracle {R} o st q (k : Z -> M R) :
prun o (rd16 st q k) = prun o (k (rdv o st q + 256 * rdv o st (aadd q 1))).
Proof. unfold rd16. rewrite rd8_oracle, rd8_oracle. reflexivity. Qed.
Lemma land_opp_pow2' : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_enframe "A'<&Q:zr1%3221';&Q9&Q?+2r2%3221&Q>%112%7231%93>14p0;1pS@@1").
Proof. intros k.
intros Hk. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
destruct (Z.eqb_spec k i); cbn [andb]; [|reflexivity].
subst. replace (i <? i) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? i); reflexivity.
Qed.
Lemma ctz32_pow2' : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_enframe "?'<&Q:zr1%3221';&H&Q?+2r2%3221%511%73<13p091pS@>1").
Proof. intros k. intros. unfold ctz32, lowbit. rewrite land_opp_pow2' by lia. apply Z.log2_pow2. lia. Qed.
Lemma get_meta_rec_upd_same : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_enframe "B'Q1&G'Q0p011';&K&Q6r2r1r3%43321%6214%7235%511%:3<31pS:<1pS>?1pT2A1").
Proof. intros st g f. unfold get_meta_rec at 1. unfold upd_meta, put_meta. cbn. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma malloc_core_fast : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_enframe "RD'Q1'<&G&Q5r3%211'Q0&Kr5%2215';'1&Q4%115(3%53421&Q;r6&E%3221&Q2&Fr8r4%3221(0%12H9%A3731z&M%117%?231&Q:r7%2261&L%71C%211&Q?+2%221B%O3Q841&D'8'6%22Q;Q<%211%42Q?1%611&Ov=&Jr<r;%544321&Q3(7&Q6r:&N&QA%Q01Lr9%I2H1%4231%611%9381>%;4R1R295%Q;2G1%=4R5G31%?2G1%QM3GA1p0O1p0Q71p0Q;1p0Q@1p0QI1p0QN1tSFR8R51tSNR>R:1pS@R?1pS>R?1pSHRA1pT2RC1").
Proof. intros st n g k.
intros sc mr OV TH ACT AV K0 LB.
unfold malloc_core. rewrite OV. replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
unfold malloc_small_ctrl. fold sc. rewrite ACT. rewrite ACT. fold mr. rewrite LB.
assert (P : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
replace (2 ^ k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
rewrite ctz32_pow2' by lia. reflexivity.
Qed.
Lemma malloc_fast_model o st n g k :
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
rewrite (malloc_core_fast st1 n g k OV TH ACT AV K0 LB). unfold Malloc.ret. rewrite sbind_ret_l.
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
End CEIL_WRAP_2.
