(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib Jb0RegionPoisoned.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Jb0MemcpyBase.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0IntMemmove () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0IntMemmove."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0IntMemmove.FPX_1.ALL."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.muslA.Jb0MemcpyBase."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2ex"]; ["2or"; "3Z"; "4MachineOk"; "4fetch_word"; "4is_ecall"; "4machine_result"; "4machine_state"; "4step"; "4store_ok"; "5decode_any"; "6SZ1"; "6Store"; "6instr"; "7bvmap"; "8wbytes"; "9msteps"]; [":at_"; ":ret_ok"; "<memb"; "<mm_result"; ";wbrev"; "=getr"; "=mkst"; "=rdn"; "=v_addi"; ">keeps"; "?mem_grows"; "@b_"; "@memk"; "Aloaded_segments"; "Badd"; "Ble"]; ["Blt"; "Bof_nat"; "Bpow"; "Bsub"; "0a"; "0b"; "0bs"; "0dst"; "0fx"; "0imm"; "0j"; "0k"; "0k0"; "0m"; "0mem0"; "0n"]; ["0pc"; "0q"; "0regs"; "0regs'"; "0ret"; "0rom"; "0rs1"; "0rs2"; "0src"; "CBV"; "CZ_to_bv"; "Cbv"; "Cbv_signed"; "Cbv_unsigned"; "0v"; "0w"]; ["0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Fixpoint wbrev (m : word -> option byte) (a : word) (bs : list byte) : word -> option byte :=
match bs with
| [] => m
| b :: rest => wbytes (wbrev m (a + 1) rest) a [b]
end.
Lemma wbrev_out : ltac2:(TCodec.tc2 tcn__Jb0IntMemmove "QA'5'R;y8%211%411yR0%511'8%115p031&Q?&Q>&R=r2%2291&QA&4r4%22?1%411%9261&QB+2+R0%3221%?251'@&Q@r3%A2H1%32@1r5%@2M1%B11%G251%I21E%:261'>&Q4r6%249G1<%:1=%53Q221p071p0C1pU2Q71pS:Q81pSLQ61pS>Q<1").
Proof.
induction bs as [|b rest IH]; intros m a x Hnw Hx; [reflexivity|].
cbn [wbrev] in *. change (length (b :: rest)) with (S (length rest)) in *. rewrite Nat2Z.inj_succ in *.
pose proof (u64_range a). pose proof (u64_range x).
assert (STEP : wbytes (wbrev m (a + 1) rest) a [b] x = wbrev m (a + 1) rest x).
{ destruct Hx as [Hx|Hx].
- rewrite wbytes_below; [reflexivity | cbn [length Z.of_nat Pos.to_nat]; lia | lia].
- rewrite wbytes_above by (cbn [length Z.of_nat Pos.to_nat]; lia). reflexivity. }
rewrite STEP. destruct rest as [|b2 rest2]; [reflexivity|].
change (length (b2 :: rest2)) with (S (length rest2)) in *. rewrite Nat2Z.inj_succ in *.
assert (Ea1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (rewrite word_succ_at; apply at_u; lia).
apply IH; try change (length (b2 :: rest2)) with (S (length rest2)); rewrite ?Nat2Z.inj_succ; rewrite ?Ea1; lia.
Qed.
Lemma wbrev_grows : ltac2:(TCodec.tc2 tcn__Jb0IntMemmove "D'5'R;y8%211%411yR0%511'8%115p031&Q:r2&Q4r1r3%33421%6251pS:;1pSL91pS>?1").
Proof.
induction bs as [|b rest IH]; intros m a; cbn [wbrev]; [apply mem_grows_refl|].
eapply mem_grows_trans; [apply IH | apply wbytes_grows].
Qed.
Lemma wbrev_pw : ltac2:(TCodec.tc2 tcn__Jb0IntMemmove "Q7'5'R;y8%211%411yR0%511'8%115p031&Q?&Q>&R=r2%2291&QA&4r4%22?1%411%9261&QB+2+R0%3221%?251'>&Q4r3r5%34=21A&N%14?43C%73I31p091pU2M1pS:N1pSLL1pS>Q21").
Proof.
induction bs as [|b rest IH]; intros m a x Hnw; [reflexivity|].
change (length (b :: rest)) with (S (length rest)) in *. rewrite Nat2Z.inj_succ in *.
cbn [wbrev wbytes]. pose proof (u64_range a). pose proof (u64_range x).
destruct (bv_eqb x a) eqn:E.
-
apply (proj1 (Fs.bv_eqb_eq x a)) in E. subst x.
destruct rest as [|b2 rest2]; [cbn [wbrev wbytes]; rewrite bv_eqb_refl; reflexivity|].
change (length (b2 :: rest2)) with (S (length rest2)) in *. rewrite Nat2Z.inj_succ in *.
assert (Ea1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (rewrite word_succ_at; apply at_u; lia).
rewrite wbytes_below; [| try change (length (b2 :: rest2)) with (S (length rest2)); rewrite ?Nat2Z.inj_succ; rewrite ?Ea1; lia | rewrite Ea1; lia].
rewrite bv_eqb_refl. reflexivity.
- assert (IH' : wbrev m (a + 1) rest x = wbytes m (a + 1) rest x).
{ destruct rest as [|b2 rest2]; [reflexivity|].
change (length (b2 :: rest2)) with (S (length rest2)) in *. rewrite Nat2Z.inj_succ in *.
assert (Ea1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (rewrite word_succ_at; apply at_u; lia).
apply IH. try change (length (b2 :: rest2)) with (S (length rest2)). rewrite ?Nat2Z.inj_succ. rewrite ?Ea1. lia. }
rewrite IH'.
revert E. generalize (a + 1) as a1. intros a1 E.
assert (GEN : forall l (m1 m2 : word -> option byte) (c : word), (forall y, y <> a -> m1 y = m2 y) -> forall y, y <> a -> wbytes m1 c l y = wbytes m2 c l y).
{ induction l as [|b' l' IHl]; intros m1 m2 c Hm y Hy; cbn [wbytes]; [apply Hm; exact Hy|].
apply IHl; [|exact Hy]. intros z Hz. destruct (bv_eqb z c); [reflexivity | apply Hm; exact Hz]. }
apply GEN.
+ intros y Hy. rewrite (bv_eqb_neq _ _ Hy). reflexivity.
+ intros ->. rewrite bv_eqb_refl in E. discriminate.
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
Section ALL.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.
Hypothesis Hn63 : (n < 2 ^ 63)%Z.
#[local] Notation MK := (memk mem0 dst bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hlen : length bs = Z.to_nat n := Hlen _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.
Let Hdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z := Hdisj _ _ _ _ _ HOK.
Definition mm_result : word -> option byte :=
if (bv_unsigned dst <? bv_unsigned src)%Z then wbytes mem0 dst bs else wbrev mem0 dst bs.
Lemma mm_result_pw : ltac2:(TCodec.tc2 tcn__Jb0IntMemmove "B'R;yR0%211'>'8y8%611%311&Q3r1%211&NvQNvQGvQF%443216%=3961pU2?1").
Proof.
intros x. unfold mm_result. destruct (bv_unsigned dst <? bv_unsigned src)%Z; [reflexivity|].
apply wbrev_pw. rewrite Hlen. lia.
Qed.
Definition memb (k : Z) : word -> option byte := wbrev mem0 (at_ dst (n - k)) (skipn (Z.to_nat (n - k)) bs).
Lemma memb_0 : ltac2:(TCodec.tc2 tcn__Jb0IntMemmove ">'>'R;yR0%211'8y8%511%311p051&Q2z%211vQN%=3521").
Proof. unfold memb. rewrite Z.sub_0_r, skipn_all2 by (rewrite Hlen; lia). reflexivity. Qed.
Lemma memb_n : ltac2:(TCodec.tc2 tcn__Jb0IntMemmove "B'>'R;yR0%211'8y8%511%311p051&Q2vQO%211&Q4vQNvQGvQF%43321%A3961").
Proof. unfold memb. rewrite Z.sub_diag, at_0. reflexivity. Qed.
Lemma memb_out : ltac2:(TCodec.tc2 tcn__Jb0IntMemmove "Q7'A'R;yR0%211'=&Q?zr2%3221vQO%5231%7231'@&Q@&R=%12=8vQG%32?1%5231&Q>%123;%@216%:241'>'8y8%I11%311&Q2r4r3%3221vQN%113%;3731p0=1p0I1pU2Q21pSHQ61").
Proof.
intros k x Hk Hx. unfold memb. pose proof (u64_range dst).
apply wbrev_out; rewrite length_skipn, Hlen, at_u; lia.
Qed.
Lemma rdb_src1 : ltac2:(TCodec.tc2 tcn__Jb0IntMemmove "Q@'A'=&Q?zr2%3221vQO%5231%7231&Q>r3+1%3221%;217'>'8'5'R;y8%211%411%611&Q7&Q=&Q2r5%211&Q0vR8r4%3221u1%:49621(0(2&Q;vQF%2218(7%11D%63E31%82E1%L3E:1p0N1p0Q71p0Q51pSFQ>1pSHQ?1").
Proof.
intros k j Hk Hj Hj1. pose proof (u64_range src). pose proof (u64_range dst).
rewrite (rdn_ext RSEGS 1 (memb k) mem0); [| rewrite at_u; cbn; lia |].
- rewrite <- (memk_0 mem0 dst bs). apply (rd_src1 mem0 dst src n bs HOK); lia.
- intros x Hx. rewrite at_u in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. apply memb_out; lia.
Qed.
Lemma wrb_dst : ltac2:(TCodec.tc2 tcn__Jb0IntMemmove "Q2'A'=&Q?zr2%3221vQO%5231%7231&Q>r3+1%3221%;217'>'1&H&Q=&Q2r5%211&Q0vQGr4%3221u1%:49621(;%>3=21p0@1p0I1p0G1pSFQ01pSHQ11").
Proof.
intros k j Hk Hj Hj1. apply (store_ok_mono _ _ mem0 (memb k) _ ltac:(unfold memb; apply wbrev_grows)).
rewrite <- (memk_0 mem0 dst bs). apply (wr_dst mem0 dst src n bs HOK); lia.
Qed.
Lemma memb_extend1 : ltac2:(TCodec.tc2 tcn__Jb0IntMemmove "QB'A'R;y8%211&Q?zr2%3221&Q>r3+1%3221vQO%9221'>&Q;vQF&QCr4%2271%321:%6251%83C=1yR0%G11'8%11Gp031&N&Q2r5%211&Q0vQG%A2F4%B21I%4231(2(7%11Q4%33Q5F1%=3:51%Q22<Q0%>11%N3A31p0G1p0Q11p0Q81pS<Q=1pSHQA1").
Proof.
intros k b Hk Hk1 ->. unfold memb, b_.
replace (n - (k + 1))%Z with (n - k - 1)%Z by lia.
rewrite (skipn_nth bs (Z.to_nat (n - k - 1)) (Z_to_bv 8 0)) by (rewrite Hlen; lia).
cbn [wbrev]. f_equal. f_equal.
- rewrite word_succ_at, at_at. f_equal. lia.
- f_equal. lia.
Qed.
Lemma mb_lbu : forall regs pc w rd rs (imm : bv 12) k j0 j,
fetch_word RSEGS pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
(0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
RiscvSemantics.step RSEGS (mkst regs pc (memb k) rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (b_ bs j))) (v_addi pc 4) (memb k) rom).
Proof.
intros regs pc w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj0 Hj1.
eapply step_lbu; [exact Hf | exact He | exact Hd |].
rewrite Hrs, at_addi, Hj. apply rdb_src1; lia.
Qed.
Lemma mb_sb : ltac2:(TCodec.tc2 tcn__Jb0IntMemmove "SK&My5'R;yR0%211%5241yQ0%511%617y<%811'A'>'8%117&C&Q=r8%3221(0r7%22>1%:3841'1&D%118(3%?3421':'L%221C%B11&Ir9%211(9(K(Jr6%342FC1+4%64<N21%G2<1%O3<91&Q5r<%221=&Q0vQGr5%3221%Q73Q?51&Q>&R<%12Q=Q5%32A1&QCvQO%221Q6+1%4221%QA3QB61r>r:%D221%QE3QM1Ky8%R111&R:&R=%12R3QB%3251&Q;vQF%B2AQ9%C21@%4231%R13:61&Q?z%221Ar;%N21G%521J'E'F%211&G&Q6vQHrBrA&Q2%11Q@vR5%7565421%92R@1(B&Q8%128QK%Q@2QGQ9%911%>5=<318%62B1%RL3B81p0F1p0J1p0N1p0Q;1p0Q@1p0QK1p0R41p0RE1p0RK1pTNS>1pSJS81pSHS91pSDS;1pT@S>1pT>S?1pU0SA1pT2SE1pT6SE1").
Proof.
intros regs pc w rs1 rs2 imm k k0 v Hf He Hd Hrs1 Hk Hrs2 Hb Hk0 Hk1.
rewrite <- (memb_extend1 k (b_ bs (n - k - 1))) by (lia || reflexivity).
eapply MmapSim.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | exact Hb |].
- rewrite Hrs1, at_addi, Hk. reflexivity.
- apply wrb_dst; lia.
Qed.
Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.
Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
Ltac msb F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].
Ltac mblbu F D jj :=
chain_step; [reflexivity
| eapply mb_lbu with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | unfold v_add, at_; unorm; f_equal; lia] | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.
Ltac mbsb F D kk valtac :=
chain_step; [reflexivity
| eapply mb_sb with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | unfold v_add, at_; unorm; f_equal; lia] | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].
Ltac cond :=
rwH; rewrite ?at_addi; unfold at_, v_addi, v_add, c_eq, c_ltu, c_lts, bv_eqb, bv_ltu, bv_lts; imm_norm; unorm; rewrite ?signed64_small by lia;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Lemma floop_run : ltac2:(TCodec.tc2 tcn__Jb0IntMemmove "RJ'6&My5'R;yR0%211%5241'A&Q1r2%211'>&Q5r4(R9+1(<%33?21%6251r3%93?21r5+;%93E17%<231&Q0vR8%2218%A3G41r6+=%A3M1?%D231vQG%921E%H3N31r7+<%H3Q41F%K231vQO%@281%O3Q531&Q?z%221@&Q>&QAr:%211%42>1%521Q4%Q93Q=1<'?'='O&Q=&Q6vQHr;+a[\@%Q?3QI1Q=/01QI&Q<vQNvQFr9%443Q221vR5%<5;:721r1%847Q66O%?5>2H14%B3A41&Q9%12@5%F231qT8R71%I2R81p0K1p0Q31p0Q71p0Q?1p0QG1p0R01p0R;1pSHR?1pT:RB1pT6RB1pT4RI1").
Proof.
induction q as [|q IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hq;
pose proof (u64_range src); pose proof (u64_range dst).
- eexists. split.
+ mlbu (ltac:(oF' 0x8ad90%Z)) (ltac:(oD' 0x8ad90%Z)) k.
msb (ltac:(oF' 0x8ad94%Z)) (ltac:(oD' 0x8ad94%Z)) k ltac:(apply sb_val_plain).
stepn (ltac:(oF' 0x8ad98%Z)) (ltac:(oD' 0x8ad98%Z)).
stepn (ltac:(oF' 0x8ad9c%Z)) (ltac:(oD' 0x8ad9c%Z)).
stepb_ft (ltac:(oF' 0x8ada0%Z)) (ltac:(oD' 0x8ada0%Z)) ltac:(cond).
stepn (ltac:(oF' 0x8ada4%Z)) (ltac:(oD' 0x8ada4%Z)).
stepret (ltac:(oF' 0x8add4%Z)) (ltac:(oD' 0x8add4%Z)) ret ltac:(rwH; reflexivity).
replace (MK (k + 1)) with (MK n) by (f_equal; lia).
apply mst_refl.
+ post.
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x8ad90 : word) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = at_ dst n /\ keeps regs r)).
+ eexists. split.
* mlbu (ltac:(oF' 0x8ad90%Z)) (ltac:(oD' 0x8ad90%Z)) k.
msb (ltac:(oF' 0x8ad94%Z)) (ltac:(oD' 0x8ad94%Z)) k ltac:(apply sb_val_plain).
stepn (ltac:(oF' 0x8ad98%Z)) (ltac:(oD' 0x8ad98%Z)).
stepn (ltac:(oF' 0x8ad9c%Z)) (ltac:(oD' 0x8ad9c%Z)).
stepb_tk (ltac:(oF' 0x8ada0%Z)) (ltac:(oD' 0x8ada0%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.
Lemma bloop_run : ltac2:(TCodec.tc2 tcn__Jb0IntMemmove "S0'6&My5'R;yR0%211%5241'A&Q1r2%211'>&Q5r4(R9+1(<%33?21%6251r3%93?21r5+:%93E17%<231vQG%?3E21r6+;%?3K1=%B231vR8%E3K21r7+<%E3Q11C%H231&R:%12Q2G%L3Q231r8+=%L3Q81J%O231&QCvQO%221C%321Q0%;2Q<1%Q63Q<61&Q?z%221C&Q>&QAr;%211%42A1%521Q;%Q@3QD1>'?'='O&Q=&Q6vQHr<+a[]H%QF3R01QD/01R0&Q2r:%211vR5%:598521r1%61O%=5<2F14%@3?41&Q9%12>5%D231qT8R<1%G2R=1p0I1p0Q11p0Q51p0Q@1p0QH1p0QO1p0R61p0RA1pSHRE1pT:RH1pT6RH1pT4RO1").
Proof.
induction q as [|q IH]; intros regs ret k Hret H1 H10 H11 H12 H13 Hk Hq;
pose proof (u64_range src); pose proof (u64_range dst).
- eexists. split.
+ stepiv (ltac:(oF' 0x8adb8%Z)) (ltac:(oD' 0x8adb8%Z)) (at_ src (n - k - 1)) ltac:(gres; rwH; unfold v_add, at_; unorm; f_equal; lia).
mblbu (ltac:(oF' 0x8adbc%Z)) (ltac:(oD' 0x8adbc%Z)) (n - k - 1)%Z.
stepiv (ltac:(oF' 0x8adc0%Z)) (ltac:(oD' 0x8adc0%Z)) (at_ dst (n - k - 1)) ltac:(gres; rwH; unfold v_add, at_; unorm; f_equal; lia).
stepiv (ltac:(oF' 0x8adc4%Z)) (ltac:(oD' 0x8adc4%Z)) (Z_to_bv 64 (n - k)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).
stepn (ltac:(oF' 0x8adc8%Z)) (ltac:(oD' 0x8adc8%Z)).
mbsb (ltac:(oF' 0x8adcc%Z)) (ltac:(oD' 0x8adcc%Z)) k ltac:(apply sb_val_plain).
stepb_ft (ltac:(oF' 0x8add0%Z)) (ltac:(oD' 0x8add0%Z)) ltac:(cond).
stepret (ltac:(oF' 0x8add4%Z)) (ltac:(oD' 0x8add4%Z)) ret ltac:(rwH; reflexivity).
replace (memb (k + 1)) with (memb n) by (f_equal; lia).
apply mst_refl.
+ post.
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x8adb8 : word) (memb (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 1 /\ getr r 13 = Z_to_bv 64 (n - (k + 1) - 1) /\ keeps regs r)).
+ eexists. split.
* stepiv (ltac:(oF' 0x8adb8%Z)) (ltac:(oD' 0x8adb8%Z)) (at_ src (n - k - 1)) ltac:(gres; rwH; unfold v_add, at_; unorm; f_equal; lia).
mblbu (ltac:(oF' 0x8adbc%Z)) (ltac:(oD' 0x8adbc%Z)) (n - k - 1)%Z.
stepiv (ltac:(oF' 0x8adc0%Z)) (ltac:(oD' 0x8adc0%Z)) (at_ dst (n - k - 1)) ltac:(gres; rwH; unfold v_add, at_; unorm; f_equal; lia).
stepiv (ltac:(oF' 0x8adc4%Z)) (ltac:(oD' 0x8adc4%Z)) (Z_to_bv 64 (n - k)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).
stepiv (ltac:(oF' 0x8adc8%Z)) (ltac:(oD' 0x8adc8%Z)) (Z_to_bv 64 (n - (k + 1) - 1)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).
mbsb (ltac:(oF' 0x8adcc%Z)) (ltac:(oD' 0x8adcc%Z)) k ltac:(apply sb_val_plain).
stepb_tk (ltac:(oF' 0x8add0%Z)) (ltac:(oD' 0x8add0%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R10 & R11 & R12 & R13 & K1).
destruct (IH r1 ret (k + 1)%Z Hret R1 R10 R11 R12 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.
Section SE.
Local Abbreviation SEC_T_int_memmove_run := (ltac2:(TCodec.tc2 tcn__Jb0IntMemmove "R4&My5'R;yR0%211%5241&Q1r1%211'>&Q5r3(R9+1(<%33>21%6251r2%93>21r4+:%93D17%<231vQG%?3D21r5+;%?3J1=%B231vR8%E3J21r6+<%E3Q01C%H231&R:vQO%22Q21%M3Q241'?'='O&Q=&Q6vQHr8+a[\0%Q33Q<1Q1/01Q<vQNvR5%8576321r7&Q3%;5:Q?214%>3=41&Q9%12<QB%B231qT8QF1%E2QG1p0G1p0Q01p0Q71p0Q>1p0QI1pT:QN1pT6QN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_int_memmove_run) 0%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_int_memmove_run) 1%nat 0%nat).
Theorem int_memmove_run : ltac:(sec_stmt2 constr:(SEC_T_int_memmove_run) 2%nat 0%nat).
Proof.
intros Hret H1 H10 H11 H12.
pose proof (u64_range src) as Us; pose proof (u64_range dst) as Ud.
unfold mm_result.
destruct (Z.ltb_spec (bv_unsigned dst) (bv_unsigned src)) as [Hlt|Hge].
-
rewrite <- (memk_n mem0 dst src n bs HOK).
replace (mkst regs (0x8ad80 : word) mem0 rom) with (mkst regs (0x8ad80 : word) (MK 0) rom) by reflexivity.
destruct (Z.eq_dec n 0) as [Hz|Hz].
+ eexists. split.
* stepb_ft (ltac:(oF' 0x8ad80%Z)) (ltac:(oD' 0x8ad80%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x8ad84%Z)) (ltac:(oD' 0x8ad84%Z)) ltac:(cond).
stepret (ltac:(oF' 0x8add4%Z)) (ltac:(oD' 0x8add4%Z)) ret ltac:(rwH; reflexivity).
replace (MK 0) with (MK n) by (f_equal; lia).
apply mst_refl.
* post.
+ assert (Hq : exists q : nat, (Z.of_nat q + 1 = n)%Z) by (exists (Z.to_nat (n - 1)); rewrite Z2Nat.id; lia).
destruct Hq as (q & Hq).
eapply (runs_trans RSEGS _ (fun r => mkst r (0x8ad90 : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = at_ dst n /\ keeps regs r)).
* eexists. split.
-- stepb_ft (ltac:(oF' 0x8ad80%Z)) (ltac:(oD' 0x8ad80%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x8ad84%Z)) (ltac:(oD' 0x8ad84%Z)) ltac:(cond).
stepn (ltac:(oF' 0x8ad88%Z)) (ltac:(oD' 0x8ad88%Z)).
stepn (ltac:(oF' 0x8ad8c%Z)) (ltac:(oD' 0x8ad8c%Z)).
apply mst_refl.
-- cbv beta. post. all: rewrite ?at_0; try reflexivity. all: unfold v_add, at_; f_equal; unorm; lia.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (floop_run q r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
-
rewrite <- memb_n. rewrite <- memb_0.
destruct (Z.eq_dec n 0) as [Hz|Hz].
+ destruct (Z.eq_dec (bv_unsigned src) (bv_unsigned dst)) as [Heq|Hne].
* eexists. split.
-- stepb_tk (ltac:(oF' 0x8ad80%Z)) (ltac:(oD' 0x8ad80%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x8ada8%Z)) (ltac:(oD' 0x8ada8%Z)) ltac:(cond).
stepret (ltac:(oF' 0x8add4%Z)) (ltac:(oD' 0x8add4%Z)) ret ltac:(rwH; reflexivity).
replace (memb 0) with (memb n) by (f_equal; lia).
apply mst_refl.
-- post.
* eexists. split.
-- stepb_tk (ltac:(oF' 0x8ad80%Z)) (ltac:(oD' 0x8ad80%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x8ada8%Z)) (ltac:(oD' 0x8ada8%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x8adac%Z)) (ltac:(oD' 0x8adac%Z)) ltac:(cond).
stepret (ltac:(oF' 0x8add4%Z)) (ltac:(oD' 0x8add4%Z)) ret ltac:(rwH; reflexivity).
replace (memb 0) with (memb n) by (f_equal; lia).
apply mst_refl.
-- post.
+ assert (Hq : exists q : nat, (Z.of_nat q + 1 = n)%Z) by (exists (Z.to_nat (n - 1)); rewrite Z2Nat.id; lia).
destruct Hq as (q & Hq).
eapply (runs_trans RSEGS _ (fun r => mkst r (0x8adb8 : word) (memb 0) rom)
(fun r => getr r 1 = ret /\ getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 1 /\ getr r 13 = Z_to_bv 64 (n - 0 - 1) /\ keeps regs r)).
* eexists. split.
-- stepb_tk (ltac:(oF' 0x8ad80%Z)) (ltac:(oD' 0x8ad80%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x8ada8%Z)) (ltac:(oD' 0x8ada8%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x8adac%Z)) (ltac:(oD' 0x8adac%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x8adb0%Z)) (ltac:(oD' 0x8adb0%Z)) (Z_to_bv 64 (n - 0 - 1)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).
stepn (ltac:(oF' 0x8adb4%Z)) (ltac:(oD' 0x8adb4%Z)).
apply mst_refl.
-- cbv beta. post.
* cbv beta. intros r1 (R1 & R10 & R11 & R12 & R13 & K1).
destruct (bloop_run q r1 ret 0 Hret R1 R10 R11 R12 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.
End SE.
End ALL.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
