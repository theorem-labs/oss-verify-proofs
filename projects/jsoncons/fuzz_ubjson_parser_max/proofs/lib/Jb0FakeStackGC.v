(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib Jb0MemIsZero Jb0RegionPoisoned
Jb0AsanMemset Jb0AsanMemcpy Jb0StrlenIcpt Jb0TlsGetAddr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Jb0_code_r48448_48dd8 Jb0_code_r69818_698c8 Jb0_code_r69654_69674.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0FakeStackGC () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0FakeStackGC.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1false"; "1length"; "1list"; "1option"; "1pair"; "1prod"; "2I"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "4Segment"; "5MachineOk"]; ["5fetch_word"; "5is_ecall"; "5machine_result"; "5machine_state"; "5step"; "6decode_any"; "7ALU_SLL"; "7ALU_SRL"; "7ALU_SUB"; "7Op"; "7Op32"; "7instr"; "8bv_eqb"; "8bvmap"; "9wbytes"; ":gc_facts"]; [";getr"; ";mkst"; ";regupd"; ";v_addi"; ";v_sll"; ";v_srl"; ";v_subw"; "<add"; "<div"; "<le"; "<lt"; "<mul"; "<of_nat"; "<opp"; "<pow"; "0addr"]; ["0bs"; "0c"; "0frsz"; "0fx"; "0i"; "0k"; "0k1"; "0m"; "0mem"; "0nfr"; "0nlog"; "0pc"; "0rd"; "0regs"; "0rom"; "0rs1"]; ["0rs2"; "0segs"; "0sp"; "=BV"; "=Z_to_bv"; "=bv"; "=bv_swrap"; "=bv_unsigned"; "0t"; "0v"; "0w"; "0x"; "0z"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Lemma v_sll_lit : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGC "Q4'='9&Q9zr1%3221&Q:+R0%2241%8241r3%9281&Q>+2%2217%9251%?251':'R5yR0%211&Q4&R4r4%2251%326?%5221&Q;%@2?B%2261%82;1%>3;51p0@1p0H1pS<Q21pS:Q31").
Proof.
intros i k Hk Hi. unfold v_sll. rewrite !u_Z2bv by lia. rewrite (Z.mod_small k 64) by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma v_srl_lit : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGC "Q4'='9&Q9zr1%3221&Q:+R0%2241%8241r3%9281&Q>+2%2217%9251%?251':'R5yR0%211&Q5&R4r4%2251%326?%5221&Q8%@2?B%2261%82;1%>3;51p0@1p0H1pS<Q21pS:Q31").
Proof.
intros i k Hk Hi. unfold v_srl. rewrite !u_Z2bv by lia. rewrite (Z.mod_small k 64) by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma u_Z2bv8 : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGC "D'='9&Q9zr1%3221&Q:+X0%2241%8241':&R7y8&R4r2%2231%5241%73A13p091pTJC1").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256%Z. lia. Qed.
Lemma wbytes_out_any_gc : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGC "QA'4'R5y8%211%411yR0%511'5%115p031&Q9&Q7&R7r2%2291&Q<&3r4%22?1%411%9261&Q>+2+R0%3221%?251'<&Q:r3%A2H1%32@1r5%@2M1%B11%G251%I21E%:261':&Nr6%249G1<%:1=%53Q221p071p0C1pTHQ71pS0Q81pS@Q61pS2Q<1").
Proof.
intros bs m addr x Hnw [Hx|Hx]; [apply wbytes_below; assumption | apply wbytes_above; exact Hx].
Qed.
Section FPX_0. Context {fx : PropExec.FPState}.
Lemma step_sll_at : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGC "S4'4'>%211&My5'R5yR0%211%5241'5y8%611%311p061yQ0%:11%;1<':%913&@r:r8%3221(0r5%22:1%93841'1&Ar6%211(2%?3521'7'K'=%3221%L11&Er7%211(6(I(Fr4%342@E1+4%64=<21%I2<1%Q03<91&L(R3z(8%33QB21%53QC@1%Q73M1I&Q4&Q0r=%221E%322Q0%5221%Q>3QH1Q7'B'C%211&Dr?&Q1vQCr>r<r;%5543?21%8271(?&Q2r9%2381QB&Q3%12FQ3%=5<31:9%72B1%R33B91p0F1p0N1p0Q61p0QH1p0QO1pTDRC1pT2R;1pT0R<1pSJR=1pTFR?1pSNRB1pSBRC1pSHRJ1pSLRJ1pT4S11").
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_sll segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma step_srl_at : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGC "S4'4'>%211&My5'R5yR0%211%5241'5y8%611%311p061yQ0%:11%;1<':%913&@r:r8%3221(0r5%22:1%93841'1&Ar6%211(2%?3521'7'K'=%3221%L11&Er7%211(6(I(Gr4%342@E1+4%64=<21%I2<1%Q03<91&L(R3z(8%33QB21%53QC@1%Q73M1I&Q5&Q0r=%221E%322Q0%5221%Q>3QH1Q7'B'C%211&Dr?&Q1vQCr>r<r;%5543?21%8271(?&Q2r9%2381QB&Q3%12FQ3%=5<31:9%72B1%R33B91p0F1p0N1p0Q61p0QH1p0QO1pTDRC1pT2R;1pT0R<1pSJR=1pTFR?1pSNRB1pSBRC1pSHRJ1pSLRJ1pT4S11").
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_srl segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma step_subw_at : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGC "S4'4'>%211&My5'R5yR0%211%5241'5y8%611%311p061yQ0%:11%;1<':%913&@r:r8%3221(0r5%22:1%93841'1&Ar6%211(2%?3521'7'K'=%3221%L11&Er7%211(6(J(Hr4%342@E1+4%64=<21%I2<1%Q03<91&L(R3z(8%33QB21%53QC@1%Q73M1I&Q6&Q0r=%221E%322Q0%5221%Q>3QH1Q7'B'C%211&Dr?&Q1vQCr>r<r;%5543?21%8271(?&Q2r9%2381QB&Q3%12FQ3%=5<31:9%72B1%R33B91p0F1p0N1p0Q61p0QH1p0QO1pTDRC1pT2R;1pT0R<1pSJR=1pTFR?1pSNRB1pSBRC1pSHRJ1pSLRJ1pT4S11").
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_subw segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
End FPX_0.
Ltac stepsv F D vv tac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Op ALU_SLL _ _ _, _) => eapply step_sll_at with (v := vv)
| decode_any _ = Some (Op ALU_SRL _ _ _, _) => eapply step_srl_at with (v := vv)
| decode_any _ = Some (Op32 ALU_SUB _ _ _, _) => eapply step_subw_at with (v := vv)
end;
[ exact F | reflexivity | exact D | reflexivity | tac ]
| step_simpl ].
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
#[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try solve_keeps_but.
#[local] Ltac mlbq F D z R :=
chain_step; [reflexivity
| eapply step_lb; [exact F | reflexivity | exact D | maddr z; exact R]
| step_simpl; vnorm].
#[local] Ltac stepsdq F D aa vv oktac :=
chain_step; [reflexivity
| eapply step_sd_at with (a := aa) (v := vv); [exact F | reflexivity | exact D | wval | gres; rwH; first [reflexivity | f_equal; lia] | oktac]
| step_simpl].
Section INNER.
Variable M : word -> option byte.
Variable rom : word -> option byte.
Variables fs c nfr nlog frsz flb sparg bot : Z.
Variables flag rs : Z -> Z.
Hypothesis Hc : (0 <= c <= 10)%Z.
Hypothesis Hnlog : nlog = (14 - c)%Z.
Hypothesis Hnfr : nfr = (2 ^ nlog)%Z.
Hypothesis Hfrsz : frsz = (2 ^ (6 + c))%Z.
Hypothesis Hflb : flb = (fs + 4096 + 32768 - 2 * nfr)%Z.
Hypothesis Hfs : (0x693000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
Hypothesis Hsp : (0 <= sparg < 2 ^ 64)%Z /\ (0 <= bot < 2 ^ 64)%Z.
Hypothesis HL : rdn ASEGS M (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20)).
Hypothesis HF : forall i, (0 <= i < nfr)%Z -> rdn ASEGS M (Z_to_bv 64 (flb + i)) 1%nat = Some [Z_to_bv 8 (flag i)] /\ (0 <= flag i < 256)%Z.
Hypothesis HR : forall i, (0 <= i < nfr)%Z -> flag i <> 0%Z ->
rdn ASEGS M (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs i)))
/\ (0 <= rs i < 2 ^ 64)%Z /\ (rs i <= bot \/ sparg <= rs i)%Z.
Lemma nfr_facts : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGC "Q0'9&Q9+@vQI%3221+`P0%5231%7231+R0vQB%9221+RPP0%;231%=231':'=&Q;%12>8&Q>+2+D%3221%83751zvQJ%H221+>%J231%L231%M271%N2A1%O2H1").
Proof.
subst nlog nfr frsz. assert (E : (14 - c + (6 + c) = 20)%Z) by lia.
repeat split; try lia.
- change 16%Z with (2 ^ 4)%Z. apply Z.pow_le_mono_r; lia.
- change 16384%Z with (2 ^ 14)%Z. apply Z.pow_le_mono_r; lia.
- change 64%Z with (2 ^ 6)%Z. apply Z.pow_le_mono_r; lia.
- change 65536%Z with (2 ^ 16)%Z. apply Z.pow_le_mono_r; lia.
- rewrite <- Z.pow_add_r by lia. rewrite E. reflexivity.
Qed.
Definition gi_inv (rg : bvmap 5 word) (i : Z) : Prop :=
getr rg 27 = Z_to_bv 64 i /\ getr rg 24 = Z_to_bv 64 flb /\ getr rg 25 = Z_to_bv 64 fs /\ getr rg 20 = Z_to_bv 64 c
/\ getr rg 7 = Z_to_bv 64 1 /\ getr rg 8 = Z_to_bv 64 (fs + 4096) /\ getr rg 21 = Z_to_bv 64 (6 + c) /\ getr rg 18 = Z_to_bv 64 bot
/\ getr rg 9 = Z_to_bv 64 sparg /\ getr rg 19 = Z_to_bv 64 nlog.
Definition gi_keeps (regs regs' : bvmap 5 word) : Prop := forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 27%bv -> getr regs' r = getr regs r.
#[local] Ltac kp := intros r N10 N11 N12 N27; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.
End INNER.
Definition gc_facts (c nfr frsz k1 : Z) : Prop :=
nfr = (2 ^ (14 - c))%Z /\ frsz = (2 ^ (6 + c))%Z /\ (64 * 2 ^ c = frsz)%Z /\ (32 * k1 = 32768 - 2 * nfr)%Z /\ (0 <= k1 < 1024)%Z
/\ Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (18446744073709551615 * 2 ^ (10 - c)))) 1023) = Z_to_bv 64 k1.
Section SE.
Local Abbreviation SEC_T_gc_facts_all := (ltac2:(TCodec.tc2 tcn__Jb0FakeStackGC "G'='9&Q9zr1%3221+:%5231%7231';&Or5r3r2%44321:qS>?1%72@1qS6A1%92B1qSDC1%;2D1p0=1pS4F1")) (only parsing).
Variable c : ltac:(sec_ty2 constr:(SEC_T_gc_facts_all) 0%nat 0%nat).
Lemma gc_facts_all : ltac:(sec_stmt2 constr:(SEC_T_gc_facts_all) 1%nat 0%nat).
Proof.
intros Hc.
assert (E : (c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10)%Z) by lia.
exists (2 ^ (14 - c))%Z, (2 ^ (6 + c))%Z, (1024 - 2 ^ (10 - c))%Z. unfold gc_facts.
destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
repeat split; first [reflexivity | apply bv_eq; vm_compute; reflexivity | vm_compute; first [reflexivity | discriminate]].
Qed.
End SE.
Lemma swrap32_small : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGC "F'='9&Q9&Q=&Q>+2+O%3221%511r1%8221&Q:%1235%<231':&R6yQ0r2%3221%53C12p071pTJE1").
Proof.
intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z.
rewrite Z.mod_small; lia.
Qed.
Section CLASS.
Variable mem0 : word -> option byte.
Variable rom : word -> option byte.
Variables t fs sparg bot : Z.
Variables flag rs : Z -> Z -> Z.
Hypothesis Ht : (0x1000000 <= t - 160)%Z /\ (t < 2 ^ 64)%Z.
Hypothesis Hfs : (0x693000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= t - 160 \/ t <= fs)%Z.
Hypothesis Hsp : (0 <= sparg < 2 ^ 64)%Z /\ (0 <= bot < 2 ^ 64)%Z.
Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (t - 160)) 160%nat = true.
Hypothesis HCF : forall M, (forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M x = mem0 x) ->
rdn ASEGS M (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20))
/\ (forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z ->
rdn ASEGS M (Z_to_bv 64 (fs + 4096 + 32768 - 2 * 2 ^ (14 - c) + i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z)
/\ (forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z -> flag c i <> 0%Z ->
rdn ASEGS M (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * 2 ^ (6 + c) + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i)))
/\ (0 <= rs c i < 2 ^ 64)%Z /\ (rs c i <= bot \/ sparg <= rs c i)%Z).
Definition gcl_inv (rg : bvmap 5 word) (c : Z) : Prop :=
getr rg 20 = Z_to_bv 64 c /\ getr rg 25 = Z_to_bv 64 fs /\ getr rg 7 = Z_to_bv 64 1 /\ getr rg 8 = Z_to_bv 64 (fs + 4096)
/\ getr rg 18 = Z_to_bv 64 bot /\ getr rg 9 = Z_to_bv 64 sparg /\ getr rg 2 = Z_to_bv 64 (t - 144).
Definition gcl_keeps (regs regs' : bvmap 5 word) : Prop :=
forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 27%bv -> r <> 21%bv -> r <> 24%bv -> r <> 19%bv -> r <> 20%bv -> getr regs' r = getr regs r.
Definition out_gc (M : word -> option byte) : Prop := forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M x = mem0 x.
Definition slot32 (M M' : word -> option byte) : Prop := forall x : word, ~ (t - 112 <= bv_unsigned x < t - 104)%Z -> M' x = M x.
#[local] Ltac hide_dj := try hide Hfs.
#[local] Ltac kp8 := intros r; intros; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.
End CLASS.
Section WHOLE.
Variable mem0 : word -> option byte.
Variable rom : word -> option byte.
Variables sp ra : word.
Variables t fs sparg tpv key tsd ctx th top botth g48 g50 g58 g60 g40 g35 : Z.
Variables flag rs : Z -> Z -> Z.
Hypothesis Hs_def : bv_unsigned sp = t.
Hypothesis Hret : ret_ok ra.
Hypothesis Ht : (0x1000000 <= t - 160)%Z /\ (t < 2 ^ 64)%Z.
Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (t - 160)) 160%nat = true.
Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
Hypothesis Hth : (0 < th /\ th + 80 <= 2 ^ 64)%Z.
Hypothesis Htop : (botth < top)%Z /\ (0 <= botth)%Z /\ (top < 2 ^ 64)%Z /\ (botth <= sparg <= top)%Z.
Hypothesis Hfs : (0x693000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= t - 160 \/ t <= fs)%Z.
Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = true.
Hypothesis Hg : (0 <= g48 < 2 ^ 64)%Z /\ (0 <= g50 < 2 ^ 64)%Z /\ (0 <= g58 < 2 ^ 64)%Z /\ (0 <= g60 < 2 ^ 64)%Z /\ (0 <= g40 < 2 ^ 64)%Z /\ (0 <= g35 < 2 ^ 64)%Z.
Hypothesis HC : forall M', (forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M' x = mem0 x) ->
rdn ASEGS M' (0x13c2a0 : word) 1%nat = Some [Z_to_bv 8 1] /\
rdn ASEGS M' (0x13c2a4 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\
rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\
rdn ASEGS M' (Z_to_bv 64 (th + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 top)) /\
rdn ASEGS M' (Z_to_bv 64 (th + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 botth)) /\
rdn ASEGS M' (0x1343a0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g48)) /\
rdn ASEGS M' (0x1343a8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g50)) /\
rdn ASEGS M' (0x1343b0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g58)) /\
rdn ASEGS M' (0x1343b8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g60)) /\
rdn ASEGS M' (0x134398 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g40)) /\
rdn ASEGS M' (0x10370 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g35)) /\
rdn ASEGS M' (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20)) /\
(forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z ->
rdn ASEGS M' (Z_to_bv 64 (fs + 4096 + 32768 - 2 * 2 ^ (14 - c) + i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z) /\
(forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z -> flag c i <> 0%Z ->
rdn ASEGS M' (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * 2 ^ (6 + c) + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i)))
/\ (0 <= rs c i < 2 ^ 64)%Z /\ (rs c i <= botth \/ sparg <= rs c i)%Z).
#[local] Ltac hide_dj := try hide Hfs.
Lemma sp_sg : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGC "9':'R5yR0%211vR2&R4vR8%2251%83541"). Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Definition F13 (rg : bvmap 5 word) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
(Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ra))
(Z_to_bv 64 (t - 16)) (word_to_le_bytes 8 (getr rg 8)))
(Z_to_bv 64 (t - 24)) (word_to_le_bytes 8 (getr rg 9)))
(Z_to_bv 64 (t - 32)) (word_to_le_bytes 8 (getr rg 18)))
(Z_to_bv 64 (t - 40)) (word_to_le_bytes 8 (getr rg 19)))
(Z_to_bv 64 (t - 48)) (word_to_le_bytes 8 (getr rg 20)))
(Z_to_bv 64 (t - 56)) (word_to_le_bytes 8 (getr rg 21)))
(Z_to_bv 64 (t - 64)) (word_to_le_bytes 8 (getr rg 22)))
(Z_to_bv 64 (t - 72)) (word_to_le_bytes 8 (getr rg 23)))
(Z_to_bv 64 (t - 80)) (word_to_le_bytes 8 (getr rg 24)))
(Z_to_bv 64 (t - 88)) (word_to_le_bytes 8 (getr rg 25)))
(Z_to_bv 64 (t - 96)) (word_to_le_bytes 8 (getr rg 26)))
(Z_to_bv 64 (t - 104)) (word_to_le_bytes 8 (getr rg 27)).
End WHOLE.
End FPX_1.
