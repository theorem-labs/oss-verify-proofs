(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit MemsetLib As0StepLib Ja0MemIsZero Ja0RegionPoisoned
Ja0AsanMemset Ja0AsanMemcpy Ja0StrlenIcpt Ja0TlsGetAddr ArtMem JatPoison JatPoisonRun.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require JatPoison3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0HandleNoReturn () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0HandleNoReturn.FPX_1.HNR."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1andb"; "1bool"; "1length"; "1list"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "4bvmap"; "0M'"; "5wbytes"; "6msteps"; "7hnr_post"]; ["8getr"; "8mkst"; "9keeps_cs"; ":loaded_segments"; ";add"; ";land"; ";le"; ";leb"; ";lt"; ";ltb"; ";modulo"; ";of_nat"; ";pow"; ";sub"; ";testbit"; "0a"]; ["0addr"; "0bs"; "0fx"; "0i"; "0j"; "0k"; "0l"; "0m"; "0m1"; "0m2"; "0mem0"; "0ra"; "0regs"; "0regs'"; "0rom"; "0s"]; ["0sp"; "<BV"; "<Z_to_bv"; "<bv"; "<bv_unsigned"; "0tpv"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
Lemma testbit_mask : ltac2:(TCodec.tc2 tcn__Ja0HandleNoReturn "Q1':'6&Fzr2%3221r3%5231%7231'7'1&N&M&L+2r5%3221r4%5241%7231%921>&0&G%126A&I%12C:%5231%B3A71p0G1p0E1pR8N1pR:O1pR<Q01").
Proof.
intros k j i Hjk Hi.
replace (2 ^ k - 2 ^ j)%Z with (Z.ones (k - j) * 2 ^ j)%Z.
2:{ unfold Z.ones. rewrite Z.shiftl_1_l, <- Z.sub_1_r, Z.mul_sub_distr_r, <- Z.pow_add_r by lia. replace (k - j + j)%Z with k by lia. lia. }
destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
- rewrite Z.mul_pow2_bits_low by lia. symmetry. apply andb_false_intro1. apply Z.leb_gt. lia.
- rewrite Z.mul_pow2_bits by lia. replace (j <=? i)%Z with true by (symmetry; apply Z.leb_le; lia).
destruct (Z.lt_ge_cases i k) as [Hk|Hk].
+ rewrite Z.ones_spec_low by lia. symmetry. apply Z.ltb_lt. lia.
+ rewrite Z.ones_spec_high by lia. symmetry. apply Z.ltb_ge. lia.
Qed.
Lemma land_down : ltac2:(TCodec.tc2 tcn__Ja0HandleNoReturn "Q0':'6&Fzr2%3221r3%5231%7231&H&L+2r4%3221%52:1%>2:1'7&E&Mr5%:291%3218%52@1&J%12B;%72C1%:3J41p0<1p0D1pS>M1pR:N1pR<O1").
Proof.
intros k j x Hjk Hx.
assert (Hp : (0 < 2 ^ j)%Z) by (apply Z.pow_pos_nonneg; lia).
pose proof (Z.div_mod x (2 ^ j) ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x (2 ^ j) Hp) as Hm.
set (q := (x / 2 ^ j)%Z) in *. set (r := (x mod 2 ^ j)%Z) in *.
replace (x - r)%Z with (q * 2 ^ j)%Z by lia.
rewrite Hdm. replace (2 ^ j * q + r)%Z with (q * 2 ^ j + r)%Z by lia.
assert (Hq : (0 <= q)%Z) by lia.
assert (Hqk : (q * 2 ^ j < 2 ^ k)%Z) by lia.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_mask by lia.
destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
- replace (j <=? i)%Z with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
rewrite andb_false_r. symmetry. apply Z.mul_pow2_bits_low. lia.
- rewrite testbit_drop_low' by lia. replace (j <=? i)%Z with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
destruct (Z.lt_ge_cases i k) as [Hik|Hik].
+ replace (i <? k)%Z with true by (symmetry; apply Z.ltb_lt; lia). now rewrite andb_true_r.
+ replace (i <? k)%Z with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
symmetry. destruct (Z.eq_dec (q * 2 ^ j) 0) as [E|NE]; [rewrite E; apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|]. apply (Z.lt_le_trans _ (2 ^ k)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Section FPX_1. Context {fx : PropExec.FPState}.
#[local] Ltac rwH :=
repeat match goal with
| H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
end.
#[local] Ltac unorm :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
end.
#[local] Ltac cond :=
rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].
#[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
#[local] Ltac mldq F D z R :=
chain_step; [reflexivity
| eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F | reflexivity | exact D | maddr z; exact R | exact (bytes_le_to_Z_8 _)]
| step_simpl; vnorm].
#[local] Ltac stepsdq F D aa vv oktac :=
chain_step; [reflexivity
| eapply step_sd_at with (a := aa) (v := vv); [exact F | reflexivity | exact D | wval | gres; rwH; first [reflexivity | f_equal; lia] | oktac]
| step_simpl].
#[local] Ltac mlbq F D z R :=
chain_step; [reflexivity
| eapply step_lb; [exact F | reflexivity | exact D | maddr z; exact R]
| step_simpl; vnorm].
#[using="Type"] Lemma wbytes_out_any : ltac2:(TCodec.tc2 tcn__Ja0HandleNoReturn "QA'3'QCy8%211%411yR0%511'4%115p031&F&D&QDr2%2291&K&2r4%22?1%411%9261&L+2+R0%3221%?251'9&Hr3%A2H1%32@1r5%@2M1%B11%G251%I21E%:261'7&=r6%249G1<%:1=%53Q221p071p0C1pS>Q71pR2Q81pR@Q61pR4Q<1").
Proof.
intros bs m addr x Hnw [Hx|Hx]; [apply wbytes_below; assumption | apply wbytes_above; exact Hx].
Qed.
Section HNR.
Variable mem0 : word -> option byte.
Variable rom : word -> option byte.
Variables sp ra : word.
Variables s tpv key tsd ctx th top botth fs pu pat pg B n : Z.
Hypothesis Hs_def : bv_unsigned sp = s.
Hypothesis Hret : ret_ok ra.
Hypothesis Hs : (0x1000000 <= s - 4160)%Z /\ (s < 2 ^ 47)%Z.
Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 160)) 160%nat = true.
Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
Hypothesis Hth : (0 < th /\ th + 80 <= 2 ^ 64)%Z.
Hypothesis Htop : (botth < top)%Z /\ (0 <= botth)%Z /\ (top mod 8 = 0)%Z.
Hypothesis HB_def : B = (s - 4160 - (s - 4160) mod 4096)%Z.
Hypothesis Hn_def : n = (top - B)%Z.
Hypothesis Hn : (8 <= n < 2 ^ 26)%Z.
Hypothesis Hhigh : (kHighMemBeg <= B)%Z /\ (top <= kHighMemEnd + 1)%Z.
Hypothesis Hfs : (2 <= fs /\ fs + 97 < 2 ^ 64)%Z /\ (fs + 97 <= s - 160 \/ s <= fs + 96)%Z /\ (fs + 97 <= SB + B / 8 \/ SB + B / 8 + n / 8 <= fs + 96)%Z.
Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = true.
Hypothesis Hpu : (0 < pu < 2 ^ 64)%Z.
Hypothesis Hpat : (0 <= pat < 2 ^ 64)%Z.
Hypothesis Hpg : (0 <= pg /\ pg + 8 < 2 ^ 64)%Z /\ (pg + 8 <= s - 160 \/ s <= pg)%Z.
Hypothesis HL : art_layout mem0.
Hypothesis HWsh : wr ASEGS mem0 (SB + B / 8) (n / 8).
Hypothesis Hshdj : apart (SB + B / 8) (n / 8) (s - 160) 160.
Hypothesis HC : forall M', (forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) ->
rdn ASEGS M' (0x13b9d8 : word) 1%nat = Some [Z_to_bv 8 1] /\
rdn ASEGS M' (0x132678 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 pu)) /\
rdn ASEGS M' (0x10438 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 pat)) /\
rdn ASEGS M' (0x13a560 : word) 1%nat = Some [Z_to_bv 8 1] /\
rdn ASEGS M' (0x13a564 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\
rdn ASEGS M' (0x132618 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 pg)) /\
rdn ASEGS M' (Z_to_bv 64 pg) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)) /\
rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\
rdn ASEGS M' (Z_to_bv 64 (th + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 top)) /\
rdn ASEGS M' (Z_to_bv 64 (th + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 botth)) /\
rdn ASEGS M' (Z_to_bv 64 (th + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 fs)).
Hypothesis HCsh : forall M', (forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z ->
~ (SB + B / 8 <= bv_unsigned x < SB + B / 8 + n / 8)%Z -> M' x = mem0 x) ->
rdn ASEGS M' (0x13a560 : word) 1%nat = Some [Z_to_bv 8 1] /\
rdn ASEGS M' (0x13a564 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\
rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\
rdn ASEGS M' (Z_to_bv 64 (th + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 fs)).
Definition hnr_post (M' : word -> option byte) : Prop :=
exists MF : word -> option byte,
M' = Wn 1 MF (fs + 96) 1
/\ (forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> MF x = Wf mem0 (SB + B / 8) (Z.to_nat (n / 8)) 0 x)
/\ mem_grows mem0 MF.
#[using="Hs_def"] Lemma sp_sh : ltac2:(TCodec.tc2 tcn__Ja0HandleNoReturn "9'7'QCyR0%211vQ@&QBvQ?%2251%83541"). Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
#[using="Type"] Lemma wbytes_agree : ltac2:(TCodec.tc2 tcn__Ja0HandleNoReturn "N'3'QCy8%211%411yR0%511'4%115p031'7r4r1%211r3%113%63831&=r5r6r2%443721%54;832%=3?21p081pS>C1pR0D1pRDB1pRBC1pR>I1").
Proof.
assert (G : forall l (m1 m2 : word -> option byte) (a x : word), m1 x = m2 x -> wbytes m1 a l x = wbytes m2 a l x).
{ induction l as [|b l IH]; intros m1 m2 a x Hm; cbn [wbytes]; [exact Hm|].
apply IH. destruct (bv_eqb x a); [reflexivity | exact Hm]. }
exact G.
Qed.
#[local] Ltac hide_dj := try hide Hfs; try hide Hpg; try hide Hshdj.
Section SE.
Local Abbreviation SEC_T_hnr_run := (ltac2:(TCodec.tc2 tcn__Ja0HandleNoReturn "R4&;y5'QCyR0%211%5241'7&@r1(QA+4(5%33;21%6251&QBvQE%22=1%;3=41r2+2%;3C19%>231vQ@%A3C21r3+1%A3I1?%D231vQ;%G3I21'8'4y8%O11%311p0O1'6'>&C&AvQ2r6+`RT@%Q23Q81Q0/01Q8vQ:vQ>%8576321%958NDQ82%<3;21%Q;2Q0H%Q=3Q?1G&B%12<Q3&?%11Q?%D231%E261%F2Q31%G2:1qJI1%O2J1qRLQI1%Q12QJ1p0Q31p0Q:1p0QA1pRJQN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_hnr_run) 0%nat 0%nat).
Theorem hnr_run : ltac:(sec_stmt2 constr:(SEC_T_hnr_run) 1%nat 0%nat).
Proof using key tsd ctx th top botth pu pat pg Hs_def Hret Hs Hok Htp Hkey Htsd Hctx Hth Htop HB_def Hn_def Hn Hhigh Hfs Hwfs Hpu Hpat Hpg HL HWsh Hshdj HC HCsh regs.
hide_dj.
intros H4 H2 H1.
rewrite sp_sh in H2.
pose proof (Z.mod_pos_bound (s - 4160) 4096 ltac:(lia)) as HBm.
assert (HB : (s - 4160 - 4095 <= B <= s - 4160)%Z /\ (B mod 4096 = 0)%Z).
{ rewrite HB_def. split; [lia|]. rewrite Zminus_mod, Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity. }
unfold kHighMemBeg, kHighMemEnd in Hhigh.
assert (HB8 : (B mod 8 = 0)%Z).
{ destruct HB as [HB1 HB2]. pose proof (Z.div_mod B 4096 ltac:(lia)) as D. rewrite HB2, Z.add_0_r in D.
rewrite D. replace (4096 * (B / 4096))%Z with ((512 * (B / 4096)) * 8)%Z by lia. apply Z_mod_mult. }
assert (Hn8 : (n mod 8 = 0)%Z).
{ rewrite Hn_def, Zminus_mod. destruct Htop as (_ & _ & T8). rewrite T8, HB8. reflexivity. }
assert (ESB : SB = 2147450880%Z) by reflexivity.
assert (HshB : (0 <= SB + B / 8)%Z /\ (SB + B / 8 + n / 8 < 2 ^ 64)%Z).
{ rewrite ESB. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
assert (B / 8 <= 2 ^ 47 / 8)%Z by (apply Z.div_le_mono; lia). assert (n / 8 <= 2 ^ 26 / 8)%Z by (apply Z.div_le_mono; lia).
change (2 ^ 47 / 8)%Z with 17592186044416%Z in *. change (2 ^ 26 / 8)%Z with 8388608%Z in *. lia. }
assert (Hn8' : (0 < n / 8)%Z) by (apply Z.div_str_pos; lia).
unhide Hfs. destruct Hfs as (Fs1 & Fs2 & Fs3). hide Fs2. hide Fs3.
unhide Hpg. destruct Hpg as (Pg1 & Pg2). hide Pg2.
assert (Hra : ret_ok (0x808c4 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (Hrb : ret_ok (0x808dc : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (Hrc : ret_ok (0x80908 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (Hrd : ret_ok (0x809b0 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (Hre : ret_ok (0x809b4 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (Hrf : ret_ok (0x809d8 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
set (M5 := wbytes (wbytes (wbytes (wbytes (wbytes mem0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
(Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18))) (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19))).
set (M7 := wbytes (wbytes M5 (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x808c4))) (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 8))).
set (M9 := wbytes (wbytes M7 (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 pat))) (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 pat))).
#[local] Ltac oout := intros x Hx; pose proof (u64_range x);
destruct Hx as [Hx|Hx]; [rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | unorm; lia]
| rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]].
assert (O9 : forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> M9 x = mem0 x) by (unfold M9, M7, M5; oout).
assert (G9 : mem_grows mem0 M9) by (unfold M9, M7, M5; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
#[local] Ltac sok := apply (store_ok_mono _ _ mem0); [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); first [apply mem_grows_refl | assumption] |];
apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 160)) _ 160%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia].
destruct (HC M5 ltac:(unfold M5; oout)) as (A1 & _).
assert (O7 : forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> M7 x = mem0 x) by (unfold M7, M5; oout).
destruct (HC M7 O7) as (_ & A2 & B3 & _).
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x80890 : word) mem0 rom) (mkst r1 (0x82f8c : word) M9 rom)
/\ (getr r1 9 = Z_to_bv 64 0x13b9d8 /\ getr r1 4 = Z_to_bv 64 tpv /\ getr r1 2 = Z_to_bv 64 (s - 80) /\ getr r1 1 = (0x808dc : word)
/\ keeps_but [1; 2; 8; 9; 18; 19]%bv regs r1)).
{ unfold M9, M7, M5. eexists. split.
- stepiv (ltac:(oF' 0x80890%Z)) (ltac:(oD' 0x80890%Z)) (Z_to_bv 64 (s - 80)) ltac:(wval).
stepsd (ltac:(oF' 0x80894%Z)) (ltac:(oD' 0x80894%Z)) (Z_to_bv 64 (s - 8)) ra ltac:(sok).
stepsd (ltac:(oF' 0x80898%Z)) (ltac:(oD' 0x80898%Z)) (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok).
stepsd (ltac:(oF' 0x8089c%Z)) (ltac:(oD' 0x8089c%Z)) (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok).
stepsd (ltac:(oF' 0x808a0%Z)) (ltac:(oD' 0x808a0%Z)) (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok).
stepsd (ltac:(oF' 0x808a4%Z)) (ltac:(oD' 0x808a4%Z)) (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok).
stepn (ltac:(oF' 0x808a8%Z)) (ltac:(oD' 0x808a8%Z)).
stepn (ltac:(oF' 0x808ac%Z)) (ltac:(oD' 0x808ac%Z)).
mlb (ltac:(oF' 0x808b0%Z)) (ltac:(oD' 0x808b0%Z)) (0x13b9d8 : word) A1.
stepn (ltac:(oF' 0x808b4%Z)) (ltac:(oD' 0x808b4%Z)).
stepfence (ltac:(oF' 0x808b8%Z)) (ltac:(oD' 0x808b8%Z)).
stepb_ft (ltac:(oF' 0x808bc%Z)) (ltac:(oD' 0x808bc%Z)) ltac:(cond).
stepn (ltac:(oF' 0x808c0%Z)) (ltac:(oD' 0x808c0%Z)).
stepiv (ltac:(oF' 0x7b4a0%Z)) (ltac:(oD' 0x7b4a0%Z)) (Z_to_bv 64 (s - 160)) ltac:(wval).
stepsd (ltac:(oF' 0x7b4a4%Z)) (ltac:(oD' 0x7b4a4%Z)) (Z_to_bv 64 (s - 88)) (Z_to_bv 64 0x808c4) ltac:(sok).
stepsd (ltac:(oF' 0x7b4a8%Z)) (ltac:(oD' 0x7b4a8%Z)) (Z_to_bv 64 (s - 96)) (getr regs 8) ltac:(sok).
stepn (ltac:(oF' 0x7b4ac%Z)) (ltac:(oD' 0x7b4ac%Z)).
mld (ltac:(oF' 0x7b4b0%Z)) (ltac:(oD' 0x7b4b0%Z)) (0x132678 : word) A2.
stepb_tk (ltac:(oF' 0x7b4b4%Z)) (ltac:(oD' 0x7b4b4%Z)) ltac:(cond).
stepn (ltac:(oF' 0x7b55c%Z)) (ltac:(oD' 0x7b55c%Z)).
stepld (ltac:(oF' 0x7b560%Z)) (ltac:(oD' 0x7b560%Z)) (Z_to_bv 64 0x808c4) ltac:(maddr (s - 88)%Z; rewrite rdn_wbytes_out; [apply rdn_wbytes_hit8; unorm; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia]).
stepld (ltac:(oF' 0x7b564%Z)) (ltac:(oD' 0x7b564%Z)) (getr regs 8) ltac:(maddr (s - 96)%Z; apply rdn_wbytes_hit8; unorm; lia).
stepiv (ltac:(oF' 0x7b568%Z)) (ltac:(oD' 0x7b568%Z)) (Z_to_bv 64 (s - 80)) ltac:(wval).
stepret (ltac:(oF' 0x7b56c%Z)) (ltac:(oD' 0x7b56c%Z)) (0x808c4 : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
stepb_ft (ltac:(oF' 0x808c4%Z)) (ltac:(oD' 0x808c4%Z)) ltac:(cond).
stepn (ltac:(oF' 0x808c8%Z)) (ltac:(oD' 0x808c8%Z)).
mld (ltac:(oF' 0x808cc%Z)) (ltac:(oD' 0x808cc%Z)) (0x10438 : word) B3.
stepsd (ltac:(oF' 0x808d0%Z)) (ltac:(oD' 0x808d0%Z)) (Z_to_bv 64 (s - 48)) (Z_to_bv 64 pat) ltac:(sok).
stepsd (ltac:(oF' 0x808d4%Z)) (ltac:(oD' 0x808d4%Z)) (Z_to_bv 64 (s - 56)) (Z_to_bv 64 pat) ltac:(sok).
stepn (ltac:(oF' 0x808d8%Z)) (ltac:(oD' 0x808d8%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q9 & Q4 & Q2 & Q1 & K1).
destruct (get_current_thread_run r1 M9 rom (0x808dc : word) (s - 80) tpv key tsd ctx th Q2 Q4 Q1 Hrb ltac:(lia) ltac:(lia) Htp Hkey Htsd Hctx ltac:(lia)
ltac:(replace (s - 80 - 16)%Z with (s - 96)%Z by lia; unfold M9, M7, M5; sok)) as (r2 & RUN2 & T10 & T2 & T1 & K2).
{ intros M' HM'. assert (O' : forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x).
{ intros x Hx. rewrite (HM' x) by lia. apply O9. exact Hx. }
destruct (HC M' O') as (_ & _ & _ & C4 & C5 & C6 & C7 & C8 & _). repeat split; assumption. }
set (M10 := wbytes M9 (Z_to_bv 64 (s - 80 - 8)) (word_to_le_bytes 8 (0x808dc : word))) in RUN2.
assert (O10 : forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> M10 x = mem0 x).
{ intros x Hx. rewrite <- (O9 x Hx). unfold M10. revert x Hx. oout. }
destruct (HC M10 O10) as (_ & _ & _ & _ & _ & _ & _ & _ & D9 & D10 & D11 & D12 & D13 & _).
assert (T9 : getr r2 9 = Z_to_bv 64 0x13b9d8) by (rewrite (K2 9%bv) by (cbv; intuition discriminate); exact Q9).
assert (T4 : getr r2 4 = Z_to_bv 64 tpv) by (rewrite (K2 4%bv) by (cbv; intuition discriminate); exact Q4).
set (M12 := wbytes (wbytes M10 (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 top))) (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 B))).
assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x808dc : word) M10 rom) (mkst r3 (0x7a1e0 : word) M12 rom)
/\ (getr r3 10 = Z_to_bv 64 B /\ getr r3 11 = Z_to_bv 64 n /\ getr r3 12 = Z_to_bv 64 0 /\ getr r3 4 = Z_to_bv 64 tpv
/\ getr r3 2 = Z_to_bv 64 (s - 80) /\ getr r3 1 = (0x809b0 : word) /\ keeps_but [1; 2; 8; 9; 18; 19]%bv r2 r3)).
{ eexists. split.
- stepb_ft (ltac:(oF' 0x808dc%Z)) (ltac:(oD' 0x808dc%Z)) ltac:(cond).
stepn (ltac:(oF' 0x808e0%Z)) (ltac:(oD' 0x808e0%Z)).
mld (ltac:(oF' 0x808e4%Z)) (ltac:(oD' 0x808e4%Z)) (0x132618 : word) D9.
mldq (ltac:(oF' 0x808e8%Z)) (ltac:(oD' 0x808e8%Z)) pg D10.
stepb_tk (ltac:(oF' 0x808ec%Z)) (ltac:(oD' 0x808ec%Z)) ltac:(cond).
stepn (ltac:(oF' 0x80904%Z)) (ltac:(oD' 0x80904%Z)).
mlbq (ltac:(oF' 0x83150%Z)) (ltac:(oD' 0x83150%Z)) (th + 40)%Z D11.
stepfence (ltac:(oF' 0x83154%Z)) (ltac:(oD' 0x83154%Z)).
stepb_tk (ltac:(oF' 0x83158%Z)) (ltac:(oD' 0x83158%Z)) ltac:(rwH; cbn; cond).
mldq (ltac:(oF' 0x83190%Z)) (ltac:(oD' 0x83190%Z)) (th + 8)%Z D12.
mldq (ltac:(oF' 0x83194%Z)) (ltac:(oD' 0x83194%Z)) (th + 16)%Z D13.
stepov (ltac:(oF' 0x83198%Z)) (ltac:(oD' 0x83198%Z)) (Z_to_bv 64 1) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (botth <? top)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepn (ltac:(oF' 0x8319c%Z)) (ltac:(oD' 0x8319c%Z)).
stepov (ltac:(oF' 0x831a0%Z)) (ltac:(oD' 0x831a0%Z)) (Z_to_bv 64 top) ltac:(gres; rwH; unfold v_and; imm_norm; unorm; rewrite Z.land_comm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia).
stepret (ltac:(oF' 0x831a4%Z)) (ltac:(oD' 0x831a4%Z)) (0x80908 : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
stepiv (ltac:(oF' 0x80908%Z)) (ltac:(oD' 0x80908%Z)) (Z_to_bv 64 top) ltac:(wval).
stepsdq (ltac:(oF' 0x8090c%Z)) (ltac:(oD' 0x8090c%Z)) (Z_to_bv 64 (s - 56)) (Z_to_bv 64 top) ltac:(unfold M10, M9, M7, M5; sok).
stepiv (ltac:(oF' 0x80910%Z)) (ltac:(oD' 0x80910%Z)) (Z_to_bv 64 (s - 64)) ltac:(wval).
stepiv (ltac:(oF' 0x80914%Z)) (ltac:(oD' 0x80914%Z)) (Z_to_bv 64 (s - 4160)) ltac:(wval).
stepn (ltac:(oF' 0x80918%Z)) (ltac:(oD' 0x80918%Z)).
stepov (ltac:(oF' 0x8091c%Z)) (ltac:(oD' 0x8091c%Z)) (Z_to_bv 64 B)
ltac:(gres; rwH; unfold v_and; imm_norm; unorm; change 18446744073709547520%Z with (2 ^ 64 - 2 ^ 12)%Z; rewrite land_down by lia; rewrite HB_def; f_equal; change (2 ^ 12)%Z with 4096%Z; lia).
stepsdq (ltac:(oF' 0x80920%Z)) (ltac:(oD' 0x80920%Z)) (Z_to_bv 64 (s - 48)) (Z_to_bv 64 B) ltac:(unfold M10, M9, M7, M5; sok).
stepiv (ltac:(oF' 0x80924%Z)) (ltac:(oD' 0x80924%Z)) (Z_to_bv 64 n) ltac:(gres; rwH; unfold v_sub; unorm; rewrite Hn_def; reflexivity).
stepn (ltac:(oF' 0x80928%Z)) (ltac:(oD' 0x80928%Z)).
stepn (ltac:(oF' 0x8092c%Z)) (ltac:(oD' 0x8092c%Z)).
stepb_tk (ltac:(oF' 0x80930%Z)) (ltac:(oD' 0x80930%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x80994%Z)) (ltac:(oD' 0x80994%Z)) (Z_to_bv 64 (n + 7)) ltac:(wval).
stepn (ltac:(oF' 0x80998%Z)) (ltac:(oD' 0x80998%Z)).
stepn (ltac:(oF' 0x8099c%Z)) (ltac:(oD' 0x8099c%Z)).
stepov (ltac:(oF' 0x809a0%Z)) (ltac:(oD' 0x809a0%Z)) (Z_to_bv 64 n)
ltac:(gres; rwH; unfold v_and; imm_norm; unorm; change 268435448%Z with (2 ^ 28 - 2 ^ 3)%Z; rewrite land_down by lia; f_equal;
change (2 ^ 3)%Z with 8%Z; rewrite <- Zplus_mod_idemp_l, Hn8; replace ((0 + 7) mod 8)%Z with 7%Z by reflexivity; lia).
stepiv (ltac:(oF' 0x809a4%Z)) (ltac:(oD' 0x809a4%Z)) (Z_to_bv 64 B) ltac:(wval).
stepn (ltac:(oF' 0x809a8%Z)) (ltac:(oD' 0x809a8%Z)).
stepn (ltac:(oF' 0x809ac%Z)) (ltac:(oD' 0x809ac%Z)).
unfold M12. apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (match goal with |- ?g => check_closed_term g; apply bv_eq; vm_compute; reflexivity end). solve_keeps_but. }
destruct S3 as (r3 & RUN3 & U10 & U11 & U12 & U4 & U2 & U1 & K3).
assert (O12 : forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> M12 x = mem0 x).
{ intros x Hx. rewrite <- (O10 x Hx). unfold M12. revert x Hx. oout. }
assert (G12 : mem_grows mem0 M12).
{ unfold M12, M10. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). first [apply mem_grows_refl | exact G9]. }
assert (L12 : art_layout M12).
{ pose proof HL as L0. unfold art_layout, cell in L0 |- *.
rewrite !(rdn_ext ASEGS _ M12 mem0) by (first [cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | intros x Hx; apply O12; revert Hx; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; intros Hx; lia]).
exact L0. }
assert (W12 : wr ASEGS M12 (s - 80 - 64) 64).
{ intros d k Hd Hk. apply (store_ok_mono _ _ mem0 M12 _ G12).
apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 160)) _ 160%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat] in *; lia]. }
unhide Hshdj.
destruct (JatPoison3.art_poison3_run r3 M12 rom (0x809b0 : word) (s - 80) B n 0 U1 Hrd U2 U10 U11 U12 ltac:(lia) ltac:(lia) W12
ltac:(unfold apart; lia) ltac:(unfold apart; lia) L12 ltac:(right; unfold JatPoison3.art_poison_hi_ok, kHighMemBeg, kHighMemEnd; lia) HB8 Hn8 ltac:(lia) ltac:(lia)
ltac:(intros _; apply Z.div_lt_upper_bound; lia) ltac:(eapply wr_grows; [exact G12 | exact HWsh]))
as (r4 & RUN4 & P10 & P1 & P2 & P8 & P9 & P18 & P19 & P20 & P21 & PK).
match type of RUN4 with msteps _ _ (mkst _ _ ?m _) => set (M13 := m) in RUN4 end.
assert (APF : forall x : word, (bv_unsigned x < s - 160 \/ s - 80 <= bv_unsigned x)%Z ->
art_poison_frame M12 (s - 80) (bv_unsigned (0x809b0 : word)) (bv_unsigned (getr r3 8)) (bv_unsigned (getr r3 9)) (bv_unsigned (getr r3 18))
(bv_unsigned (getr r3 19)) (bv_unsigned (getr r3 20)) (bv_unsigned (getr r3 21)) x = M12 x).
{ intros x Hx. unfold art_poison_frame. rewrite !Wn_outside; first [reflexivity | lia | cbn [Z.of_nat Pos.to_nat]; lia]. }
assert (O13 : forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> ~ (SB + B / 8 <= bv_unsigned x < SB + B / 8 + n / 8)%Z -> M13 x = mem0 x).
{ intros x Hx Hnx. unfold M13, Wf. pose proof (u64_range x).
destruct (Z.lt_ge_cases (bv_unsigned x) (SB + B / 8)) as [L|G].
- rewrite wbytes_below; [| rewrite repeat_length; unorm; lia | unorm; lia]. rewrite APF by lia. apply O12. exact Hx.
- rewrite wbytes_above by (rewrite repeat_length; unorm; lia). rewrite APF by lia. apply O12. exact Hx. }
assert (G13 : mem_grows mem0 M13).
{ unfold M13. eapply mem_grows_trans; [|apply Wf_grows]. unfold art_poison_frame. do 7 (eapply mem_grows_trans; [|apply Wn_grows]). exact G12. }
assert (P4 : getr r4 4 = Z_to_bv 64 tpv) by (rewrite (PK 4%bv) by (unfold art_poison_kept; repeat split; discriminate); exact U4).
assert (S4 : exists r4b, msteps ASEGS (mkst r4 (0x809b0 : word) M13 rom) (mkst r4b (0x82f8c : word) M13 rom)
/\ (getr r4b 2 = Z_to_bv 64 (s - 80) /\ getr r4b 4 = Z_to_bv 64 tpv /\ getr r4b 1 = (0x809b4 : word) /\ keeps_but [1]%bv r4 r4b)).
{ eexists. split.
- stepn (ltac:(oF' 0x809b0%Z)) (ltac:(oD' 0x809b0%Z)). apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (match goal with |- ?g => check_closed_term g; apply bv_eq; vm_compute; reflexivity end). solve_keeps_but. }
destruct S4 as (r4b & RUN4b & Pb2 & Pb4 & Pb1 & K4b).
destruct (get_current_thread_run r4b M13 rom (0x809b4 : word) (s - 80) tpv key tsd ctx th Pb2 Pb4 Pb1 Hre ltac:(lia) ltac:(lia) Htp Hkey Htsd Hctx ltac:(lia)
ltac:(replace (s - 80 - 16)%Z with (s - 96)%Z by lia; apply (store_ok_mono _ _ mem0 M13 _ G13);
apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 160)) _ 160%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]))
as (r5 & RUN5 & V10 & V2 & V1 & K5).
{ intros M' HM'. destruct (HCsh M') as (C1 & C2 & C3 & C4 & C5 & _); [|repeat split; assumption].
intros x Hx Hnx. rewrite (HM' x) by lia. apply O13; assumption. }
set (M14 := wbytes M13 (Z_to_bv 64 (s - 80 - 8)) (word_to_le_bytes 8 (0x809b4 : word))) in RUN5.
assert (O14 : forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> ~ (SB + B / 8 <= bv_unsigned x < SB + B / 8 + n / 8)%Z -> M14 x = mem0 x).
{ intros x Hx Hnx. rewrite <- (O13 x Hx Hnx). unfold M14. pose proof (u64_range x).
destruct Hx as [Hx|Hx]; [rewrite wbytes_below; [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia]
| rewrite wbytes_above; [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia]]. }
destruct (HCsh M14 O14) as (_ & _ & _ & _ & _ & E6 & E7).
assert (G14 : mem_grows mem0 M14) by (unfold M14; eapply mem_grows_trans; [exact G13 | apply wbytes_grows]).
set (M15 := wbytes M14 (Z_to_bv 64 (fs + 96)) [Z_to_bv 8 1]).
unhide Fs2. unhide Fs3.
assert (SL : forall k v, (k = 8 /\ v = ra \/ k = 16 /\ v = getr regs 8 \/ k = 24 /\ v = getr regs 9 \/ k = 32 /\ v = getr regs 18 \/ k = 40 /\ v = getr regs 19)%Z ->
rdn ASEGS M15 (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v)).
{ intros k v Hk. assert (Hk' : (8 <= k <= 40)%Z) by lia.
rewrite (rdn_ext ASEGS 8 M15 M5); [| unorm; cbn; lia |].
- unfold M5. destruct Hk as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]];
repeat (rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ]);
apply rdn_wbytes_hit8; unorm; lia.
- intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. pose proof (u64_range x).
unfold M15. rewrite wbytes_out_any; [| cbn [length Z.of_nat Pos.to_nat]; unorm; lia | cbn [length Z.of_nat Pos.to_nat]; unorm; lia].
unfold M14. rewrite wbytes_above by (rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia).
unfold M13, Wf. rewrite wbytes_out_any; [| rewrite repeat_length; unorm; lia | rewrite repeat_length; unorm; unfold apart in Hshdj; lia].
rewrite APF by lia. unfold M12, M10, M9, M7.
rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]. }
eexists. exists M15. split.
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
eapply msteps_trans; [exact RUN4b|]. eapply msteps_trans; [exact RUN5|].
stepb_ft (ltac:(oF' 0x809b4%Z)) (ltac:(oD' 0x809b4%Z)) ltac:(cond).
mlbq (ltac:(oF' 0x809b8%Z)) (ltac:(oD' 0x809b8%Z)) (th + 40)%Z E6.
stepb_ft (ltac:(oF' 0x809bc%Z)) (ltac:(oD' 0x809bc%Z)) ltac:(rwH; cbn; cond).
mldq (ltac:(oF' 0x809c0%Z)) (ltac:(oD' 0x809c0%Z)) (th + 72)%Z E7.
stepiv (ltac:(oF' 0x809c4%Z)) (ltac:(oD' 0x809c4%Z)) (Z_to_bv 64 0) ltac:(gres; rwH; unfold v_sltiu; imm_norm; unorm; change (bv_wrap 64 2) with 2%Z; replace (fs <? 2)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
stepn (ltac:(oF' 0x809c8%Z)) (ltac:(oD' 0x809c8%Z)).
stepov (ltac:(oF' 0x809cc%Z)) (ltac:(oD' 0x809cc%Z)) (Z_to_bv 64 fs) ltac:(gres; rwH; unfold v_and; imm_norm; unorm; rewrite Z.land_comm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia).
stepb_ft (ltac:(oF' 0x809d0%Z)) (ltac:(oD' 0x809d0%Z)) ltac:(cond).
stepn (ltac:(oF' 0x809d4%Z)) (ltac:(oD' 0x809d4%Z)).
stepn (ltac:(oF' 0x5d0c8%Z)) (ltac:(oD' 0x5d0c8%Z)).
chain_step; [reflexivity | eapply (step_sb_at ASEGS) with (a := Z_to_bv 64 (fs + 96)) (b := Z_to_bv 8 1);
[exact (ltac:(oF' 0x5d0cc%Z)) | reflexivity | exact (ltac:(oD' 0x5d0cc%Z)) | wval | gres; reflexivity | apply bv_eq; vm_compute; reflexivity
| apply (store_ok_mono _ _ mem0 M14 _ G14); exact Hwfs ] | step_simpl; vnorm].
change (wbytes M14 (Z_to_bv 64 (fs + 96)) [Z_to_bv 8 1]) with M15.
stepret (ltac:(oF' 0x5d0d0%Z)) (ltac:(oD' 0x5d0d0%Z)) (0x809d8 : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
#[local] Ltac slv := first [left; split; reflexivity | right; left; split; reflexivity | right; right; left; split; reflexivity | right; right; right; left; split; reflexivity | right; right; right; right; split; reflexivity].
stepld (ltac:(oF' 0x809d8%Z)) (ltac:(oD' 0x809d8%Z)) ra ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 8)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x809dc%Z)) (ltac:(oD' 0x809dc%Z)) (getr regs 8) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 16)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x809e0%Z)) (ltac:(oD' 0x809e0%Z)) (getr regs 9) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 24)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x809e4%Z)) (ltac:(oD' 0x809e4%Z)) (getr regs 18) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 32)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x809e8%Z)) (ltac:(oD' 0x809e8%Z)) (getr regs 19) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 40)) by (symmetry; wval) end; apply SL; slv).
stepiv (ltac:(oF' 0x809ec%Z)) (ltac:(oD' 0x809ec%Z)) (Z_to_bv 64 s) ltac:(wval).
stepret (ltac:(oF' 0x809f0%Z)) (ltac:(oD' 0x809f0%Z)) ra ltac:(rwH; reflexivity).
apply mst_refl.
- split; [gres; symmetry; apply sp_sh|]. split; [gres; reflexivity|]. split.
+
assert (KP : keeps_but [1; 2; 8; 9; 18; 19]%bv r3 r4).
{ intros r Hr HnL. apply PK. clear -Hr. unfold art_poison_kept. cbv in Hr. repeat split; intros ->; intuition discriminate. }
assert (KB : keeps_but [1; 2; 8; 9; 18; 19]%bv regs r5).
{ eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [intros r Hr HnL; apply K2; [exact Hr | clear -HnL; cbv in HnL |- *; intuition]|].
eapply keeps_but_trans; [exact K3|]. eapply keeps_but_trans; [exact KP|].
eapply keeps_but_trans; [intros r Hr HnL; apply K4b; [exact Hr | clear -HnL; cbv in HnL |- *; intuition]|].
intros r Hr HnL; apply K5; [exact Hr | clear -HnL; cbv in HnL |- *; intuition]. }
intros r Hcs. destruct (decide (r = 1%bv)) as [->|Nq1]; [gres; rewrite H1; reflexivity|].
destruct (decide (r = 2%bv)) as [->|Nq2]; [gres; rewrite H2; reflexivity|].
destruct (decide (r = 8%bv)) as [->|Dq8]; [gres; reflexivity|]. destruct (decide (r = 9%bv)) as [->|Dq9]; [gres; reflexivity|].
destruct (decide (r = 18%bv)) as [->|Dq18]; [gres; reflexivity|]. destruct (decide (r = 19%bv)) as [->|Dq19]; [gres; reflexivity|].
repeat (rewrite getr_other; [| intros ->; first [match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end | clear -Hcs; cbv in Hcs; intuition discriminate]]).
apply KB; [exact Hcs|]. clear -Nq1 Nq2 Dq8 Dq9 Dq18 Dq19. cbv. intuition congruence.
+
exists M14. split; [unfold M15, Wn; reflexivity|]. split; [|exact G14].
intros x Hx. unfold M14. pose proof (u64_range x).
rewrite wbytes_out_any; [| rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
unfold M13, Wf. apply wbytes_agree. rewrite APF by lia. apply O12. exact Hx.
Qed.
End SE.
End HNR.
End FPX_1.
