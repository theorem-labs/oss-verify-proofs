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
Jb0AsanMemset Jb0AsanMemcpy Jb0StrlenIcpt Jb0TlsGetAddr Jb0FakeStackGC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0FakeStackGCC () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0FakeStackGCC."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0FakeStackGCC.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0FakeStackGCC.FPX_1.CLASS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0FakeStackGCC.FPX_1.SETSH."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0FakeStackGCC.FPX_1.SLOT."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0FakeStackGCC.GCM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2False"; "2I"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3repeat"]; ["4Z"; "5word_to_le_bytes"; "6bvmap"; "0M"; "0M'"; "0M2"; "0Mf"; "0Mfr"; "0Mj"; "7wbytes"; "8msteps"; ";gcl2_inv"; ";gcl_keeps2"; "<ss_inv"; "<ss_keeps"; "<ssm"]; ["=frm"; "=gi2_inv"; "=gi_keeps2"; "=gs_keeps"; ":frm"; ">gcm"; "9gc_col"; "9gc_done_lt"; "9gc_fl"; "9gc_fr"; "9gc_post"; "9gc_postb"; "9gc_sh"; "9gc_shz_hi"; "9gc_shz_lo"; "9gc_valid"]; ["9gcm"; "?in_app"; "@getr"; "@mkst"; "@rdn"; "Akeeps_cs"; "Bmem_grows"; "Cloaded_segments"; "Dconcat"; "Eadd"; "Ele"; "Elt"; "Emul"; "Eof_nat"; "Epow"; "Esub"]; ["0a"; "0bot"; "0botth"; "0bs"; "0c"; "0c'"; "0c0"; "0col"; "0col'"; "0d"; "0d'"; "0flag"; "0fs"; "0fx"; "0g35"; "0gb"]; ["0hi"; "0hi'"; "0i"; "0i'"; "0i0"; "0k"; "0lo"; "0lo'"; "0mem0"; "0n"; "0nfr"; "0q"; "0r1"; "0r2"; "0r3"; "0ra"]; ["0regs"; "0regs'"; "0rom"; "0rs"; "0sh"; "0sp"; "0sparg"; "FBV"; "FZ_to_bv"; "Fbv"; "Fbv_unsigned"; "0t"; "0tpv"; "0w"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Definition gc_fl (fs c i : Z) : Z := (fs + 4096 + 32768 - 2 * 2 ^ (14 - c) + i)%Z.
Definition gc_fr (fs c i : Z) : Z := (fs + 4096 + 32768 + c * 2 ^ 20 + i * 2 ^ (6 + c))%Z.
Definition gc_sh (fs c i : Z) : Z := (SB + gc_fr fs c i / 8)%Z.
Definition gc_valid (c i : Z) : Prop := (0 <= c <= 10)%Z /\ (0 <= i < 2 ^ (14 - c))%Z.
Definition gc_insh (fs c i a : Z) : Prop := (gc_sh fs c i <= a < gc_sh fs c i + 2 ^ (3 + c))%Z.
Definition gc_col (sparg bot : Z) (flag rs : Z -> Z -> Z) (c i : Z) : Prop := flag c i <> 0%Z /\ (bot < rs c i < sparg)%Z.
Definition gc_shz_lo (fs : Z) : Z := (SB + (fs + 4096 + 32768) / 8)%Z.
Definition gc_shz_hi (fs : Z) : Z := (SB + (fs + 4096 + 32768 + 11 * 2 ^ 20) / 8)%Z.
Definition gc_outz (lo hi fs a : Z) : Prop :=
(a < lo \/ hi <= a)%Z /\ ~ (fs + 4096 <= a < fs + 4096 + 32768)%Z /\ ~ (gc_shz_lo fs <= a < gc_shz_hi fs)%Z.
Definition gc_done_lt (c i c' i' : Z) : Prop := (c' < c \/ (c' = c /\ i' < i))%Z.
Definition gc_postb (gb : Z) (mem0 Mf : word -> option byte) (lo hi fs : Z) (col : Z -> Z -> Prop) : Prop :=
mem_grows mem0 Mf
/\ (forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x)%Z -> bv_unsigned x <> (fs + 96)%Z ->
(forall c i, gc_valid c i -> col c i -> bv_unsigned x <> gc_fl fs c i /\ ~ gc_insh fs c i (bv_unsigned x)) -> Mf x = mem0 x)
/\ (forall c i, gc_valid c i -> col c i -> Mf (Z_to_bv 64 (gc_fl fs c i)) = Some (Z_to_bv 8 0))
/\ rdn ASEGS Mf (Z_to_bv 64 (fs + 96)) 1%nat = Some [Z_to_bv 8 gb].
Definition gc_post := gc_postb 0.
Section SE.
Local Abbreviation SEC_T_gc_pow_facts := (ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "QD'@'9&QJzr1%3221+:%5231%7231+@&QN+2&QO+>r2%3221%6251%?281+`P0%A231%C231+R0&QI+6%221:%?2>1%H251+RPP0%J231%L231+8+3%:21B%G2F1%Q0241+XP0%Q2231%Q4231':&QL%12H?+D%Q02O1%53Q;31%52;>%73Q=D1%Q=231%Q>2:1%Q?2C1%Q@2M1p0Q:1pT:QC1")) (only parsing).
Variable c : ltac:(sec_ty2 constr:(SEC_T_gc_pow_facts) 0%nat 0%nat).
Lemma gc_pow_facts : ltac:(sec_stmt2 constr:(SEC_T_gc_pow_facts) 1%nat 0%nat).
Proof.
intros Hc.
assert (E : (c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10)%Z) by lia.
destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; vm_compute; intuition discriminate.
Qed.
End SE.
Lemma gc_fl_range : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "H'@&Q?r2r1%3221'9&QJ&QIr4+TP0%3221&Q8r3%2351;%8241&QK+QPP0%:271%3251%>251p0@1pU6E1pT:F1pTJG1").
Proof. intros fs c i [Hc Hi]. pose proof (gc_pow_facts c Hc) as (P1 & _). unfold gc_fl. lia. Qed.
Lemma gc_fl_lt : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "I'@&Q?r4r3%3221r2%5231&QKr6%2217&Q8r8r7%33215r5%5341=%9231p081p0<1p0?1pU8D1pT<E1pU6F1pT:G1pTJH1").
Proof.
intros fs c i c' i' [Hc Hi] [Hc' Hi'] L. unfold gc_fl.
assert (P : (2 * 2 ^ (14 - c') <= 2 ^ (14 - c))%Z).
{ replace (2 * 2 ^ (14 - c'))%Z with (2 ^ (15 - c'))%Z by (replace (15 - c')%Z with (Z.succ (14 - c')) by lia; rewrite Z.pow_succ_r by lia; reflexivity).
apply Z.pow_le_mono_r; lia. }
lia.
Qed.
Lemma gc_fl_inj : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "K'@&Q?r4r3%3221r2%5231':&Q8r7r6r5%43321%534;:%73>21'9%93@75%:3A7?%3221p051p0>1p0A1pU8F1pT<G1pU6H1pT:I1pTJJ1").
Proof.
intros fs c i c' i' V V' E.
destruct (Z.lt_trichotomy c c') as [L|[->|L]].
- pose proof (gc_fl_lt fs c i c' i' V V' L). lia.
- split; [reflexivity|]. unfold gc_fl in E. lia.
- pose proof (gc_fl_lt fs c' i' c i V' V L). lia.
Qed.
Lemma gc_fr_range : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "Q3'@&Q?r2r1%3221'9&QJ&QIr4+TP0%3221+QPP0%5221&Q9r3%2371=%:241&QN+2+6%=216%4231%?271&QL+;+D%9281%4231%E2@1%G271%I2>1p0K1pU6Q01pT:Q11pTJQ21").
Proof.
intros fs c i [Hc Hi]. pose proof (gc_pow_facts c Hc) as (P1 & P2 & P3 & P4 & P5). unfold gc_fr.
assert (A : (0 <= i * 2 ^ (6 + c))%Z) by (apply Z.mul_nonneg_nonneg; lia).
assert (B : (i * 2 ^ (6 + c) + 2 ^ (6 + c) <= 2 ^ 20)%Z).
{ rewrite <- P4. replace (i * 2 ^ (6 + c) + 2 ^ (6 + c))%Z with ((i + 1) * 2 ^ (6 + c))%Z by ring. apply Z.mul_le_mono_nonneg_r; lia. }
assert (C : (0 <= c * 2 ^ 20 <= 10 * 2 ^ 20)%Z) by lia.
lia.
Qed.
Lemma gc_sh_range : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "M'@&Q?r2r1%3221'9&QJ&Q>r4%211&Q<r3%2341:%7241&QI&QN+2+3%4217%4231%6281&Q=%11>%A231%C2;1p0E1pU6J1pT:K1pTJL1").
Proof.
intros fs c i V. pose proof (gc_fr_range fs c i V) as [R1 R2]. destruct V as [Hc Hi].
pose proof (gc_pow_facts c Hc) as (P1 & P2 & P3 & P4 & P5). unfold gc_sh, gc_shz_lo, gc_shz_hi.
split.
- apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
- assert (E : ((gc_fr fs c i + 2 ^ (6 + c)) / 8 = gc_fr fs c i / 8 + 2 ^ (3 + c))%Z) by (rewrite P5; apply Z.div_add; lia).
assert (L : ((gc_fr fs c i + 2 ^ (6 + c)) / 8 <= (fs + 4096 + 32768 + 11 * 2 ^ 20) / 8)%Z) by (apply Z.div_le_mono; lia).
lia.
Qed.
Lemma gc_shz_facts : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "QJ'@&QJ+Vb\P0r1%3221&QK&QIr2+TP0%3221+QPP0%5221&QL+;&QN+2+D%3221%6251%=281+Q?%7261%A231'>r3%C21A%D21@%E219+QoonlP0%L221+`PQoooPP0%N217%9231'9&Q=r4%211%Q4212%Q023N%Q121M%Q221F&Q>%117%Q:231%E271+QoooPP0%Q=214%Q>25;+Q=%Q32Q21%Q=2>1%B241%C261%D291p0F1p0Q11p0QD1pTJQI1").
Proof.
intros fs F1 F2 A. unfold gc_shz_lo, gc_shz_hi, SB.
assert (D1 : (0 <= (fs + 4096 + 32768) / 8)%Z) by (apply Z.div_pos; lia).
assert (D2 : ((fs + 4096 + 32768) / 8 <= (fs + 4096 + 32768 + 11 * 2 ^ 20) / 8)%Z) by (apply Z.div_le_mono; lia).
assert (D3 : ((fs + 4096 + 32768 + 11 * 2 ^ 20) / 8 <= 2 ^ 47 / 8)%Z) by (apply Z.div_le_mono; lia).
change (2 ^ 47 / 8)%Z with 17592186044416%Z in D3.
repeat split; try lia.
Qed.
Lemma gc_fr_in_app : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "Q@'@&QJ+Vb\P0r3%3221&QK&QIr4+TP0%3221+QPP0%5221&QL+;&QN+2+D%3221%6251%=281+Q?%7261%A231'>r5%C21A%D21@%E219+QoonlP0%L221+`PQoooPP0%N217%9231&Q?%12:K&QA&Q9r7r6%3321?%511p071p0:1p0E1p0Q81pU6Q=1pT:Q>1pTJQ?1").
Proof.
intros fs c i F1 F2 A V. pose proof (gc_fr_range fs c i V) as [R1 R2]. destruct V as [Hc Hi]. pose proof (gc_pow_facts c Hc) as (_ & P2 & _).
unfold in_app, LOWEND, HIGHBEG, HIGHEND. lia.
Qed.
Lemma u64_lit : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "G'@'9&QJzr1%3221&QK&QN+2+R0%3221%5271%;271':&S:yR0&S8r2%2231%5241%73D13p091pT2F1").
Proof. intros a Ha. apply u_Z2bv; lia. Qed.
Lemma word_of_u : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "A'S9yR0%211'@':&S:r2%2261r1%53621r3&S8%12;6%93;31p051pT2<1pVN>1").
Proof. intros x a <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma len_concat_le8 : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "N'S9yR0%211'4':'@&QM&2y8%911&QH&?'3%114&Au8r2%3221r1%83621%:2;1%>2<1%@11&QL+8%C17%3221%G3F51pUDI1pVLK1").
Proof.
intros w n. induction n as [|n IH]; [reflexivity|]. cbn [repeat concat]. rewrite length_app, Nat2Z.inj_add, IH, length_N_to_le_bytes. lia.
Qed.
Section GCM.
Variable mem0 : word -> option byte.
Variables lo hi fs : Z.
Variable col : Z -> Z -> Prop.
Hypothesis Hfsb : (0 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 64)%Z.
Hypothesis Hzb : (0 <= gc_shz_lo fs)%Z /\ (gc_shz_hi fs < 2 ^ 64)%Z.
Hypothesis Hdj_fl_sh : (gc_shz_hi fs <= fs \/ fs + 4096 + 32768 + 11 * 2 ^ 20 <= gc_shz_lo fs)%Z.
Hypothesis Hdj_fr_fs : (hi <= fs \/ fs + 4096 + 32768 + 11 * 2 ^ 20 <= lo)%Z.
Hypothesis Hdj_fr_sh : (gc_shz_hi fs <= lo \/ hi <= gc_shz_lo fs)%Z.
Definition gcm (done : Z -> Z -> Prop) (M : word -> option byte) : Prop :=
mem_grows mem0 M
/\ (forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x)%Z ->
(forall c i, gc_valid c i -> done c i -> col c i -> bv_unsigned x <> gc_fl fs c i /\ ~ gc_insh fs c i (bv_unsigned x)) -> M x = mem0 x)
/\ (forall c i, gc_valid c i -> done c i -> col c i -> M (Z_to_bv 64 (gc_fl fs c i)) = Some (Z_to_bv 8 0)).
#[using="Type"] Lemma gcm_init : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "Q8'S9yR0%211'6y8%511%311p051&QFvRHr1%3221'>&QK&S:%12>5vRF%4221&QJvR@%2215%9241':r4r2%211%A12%53E21p071pVNK1&Q5'@'7q021q031r3%6221p081p0K1pQ8Q01").
Proof. intros M G O. split; [exact G|]. split; [intros x Hx _; apply O; exact Hx | intros c i _ []]. Qed.
#[using="Type"] Lemma gcm_equiv : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "Q3'@!p021p031'S9yR0%211'6y8%511%311p051&Q?r2r1%3221&<r5r3%2216r6%1238%6231p081pU6H1pT:I1&Q5r4%221?%322;p021p061pQ8E1pTFN1pTDO1").
Proof.
intros d d' M E (G & O & P). split; [exact G|]. split.
- intros x Hx Hn. apply O; [exact Hx|]. intros c i V D C. apply Hn; [exact V | apply E; assumption | exact C].
- intros c i V D C. apply P; [exact V | apply E; assumption | exact C].
Qed.
#[using="Type"] Lemma gcm_skip : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "QC'@!p021p031'S9yR0%211'6y8%511%311p051&=vR7r2r1%3221%511&Q?%1254&<r8r3%2219'>r9%124<'9':r6%23N81r5%43Q0B1%6231%:281%?2<1p0A1pU6Q51pT:Q61&Q5r7%221:%322=p021p061p0L1pU:Q>1pT>Q?1pQ8Q51pTFQ>1pTDQ?1").
Proof.
intros d d' M c0 i0 NC E (G & O & P). split; [exact G|]. split.
- intros x Hx Hn. apply O; [exact Hx|]. intros c i V D C. apply Hn; [exact V | apply E; [exact V | left; exact D] | exact C].
- intros c i V D C. apply E in D; [|exact V]. destruct D as [D|[-> ->]]; [apply P; assumption | contradiction].
Qed.
#[using="Hfsb Hdj_fr_fs"] Lemma gcm_frame : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "Q='@!p021p031'S9yR0%211'6y8%511%311p051&Q5r3r2%3221&QF%1243'>&QK&S:r1%22A1vRF%5221&QJvR@%2215%:241':r5%11Ar6%11C%53H31p071pVNN1r4%J261p031p0G1p0J1pQ:O1pQ8Q01pTDQ91").
Proof.
intros d M M' (G & O & P) G' O'. split; [eapply mem_grows_trans; eassumption|]. split.
- intros x Hx Hn. rewrite (O' x Hx). apply O; assumption.
- intros c i V D C. pose proof (P c i V D C) as P1. pose proof (gc_fl_range fs c i V) as FR.
rewrite O'; [exact P1 | rewrite u64_lit by lia; lia].
Qed.
#[using="Hdj_fl_sh"] Lemma gcm_out : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "QO'@!p021p031'S9yR0%211'6y8%511%311p051&Q5r2r1%3221'>&QK&S:%12>5vRF%4221&QJvR@%2215%9241&='9&QIvR<+TP0%3221%>2KC%;221+QPP0%7241%C241%:241%<11&Q>%11;r3%H2Q51%E231&Q=%11@%M241%D241%F11':r6r4%211vRH%113%63Q=31p081p0C1p0Q11pVNQE1p0Q=1pQ8QB1pTDQK1").
Proof.
intros d M (G & O & P) x Hx Nf Ns. apply O; [exact Hx|]. intros c i V _ _.
pose proof (gc_fl_range fs c i V) as FR. pose proof (gc_sh_range fs c i V) as [S1 S2]. unfold gc_insh. lia.
Qed.
#[using="Hfsb Hdj_fl_sh Hdj_fr_fs"] Lemma gcm_flag : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "Q9'@!p021p031'S9yR0%211'6y8%511%311p051&Q5r4r3%3221&Q?r2%2241&=r6%1287%311':&S8&Q8vR<r5%3321?%52H1%:11vRH%113%:3G31p0<1p0A1p0E1pU6Q51pT:Q61pQ8L1pTDQ51").
Proof.
intros d M c i (G & O & P) V ND. pose proof (gc_fl_range fs c i V) as FR.
apply O; [rewrite u64_lit by lia; lia|]. rewrite u64_lit by lia. intros c' i' V' D' C'. split.
- intros E. apply (gc_fl_inj fs c i c' i' V V') in E. destruct E as [-> ->]. contradiction.
- pose proof (gc_sh_range fs c' i' V') as [S1 S2]. unfold gc_insh. lia.
Qed.
#[using="Hfsb Hzb Hdj_fl_sh"] Lemma gcm_collect : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "RG'@!p021p031'S9yR0%211'6y8%511%311p051'3%114&Q?r3r2%3221vR7r4%2215':&QM&2%12?9%311&QN+2&QI+3r5%3221%6251%<3Q181r1%E2C1&<r;%12GF'>r<%12JI'9r9%G3Q<M1r8%I3Q>N1%5231%9271%=2;1p0?1pU6QC1pT:QD1&Q5r:%221:&I&S8&Q8vR<r7%332@1%52QI1(1z%82QI1(5%11QJ%53QK31%=3J71&Q<%13<J;%?2R31r6%B3521%F2E1p0E1p0I1p0Q=1p0QK1p0QO1pT8R41pU:RB1pT>RC1pQ8R91pTFRB1pTDRC1").
Proof.
intros d d' M c0 i0 bs V0 C0 Ln E (G & O & P).
pose proof (gc_fl_range fs c0 i0 V0) as FR0. pose proof (gc_sh_range fs c0 i0 V0) as [S01 S02].
pose proof (gc_pow_facts c0 (proj1 V0)) as (_ & _ & P3 & _).
set (M1 := wbytes M (Z_to_bv 64 (gc_fl fs c0 i0)) [Z_to_bv 8 0]).
assert (OUT2 : forall x : word, ~ gc_insh fs c0 i0 (bv_unsigned x) -> wbytes M1 (Z_to_bv 64 (gc_sh fs c0 i0)) bs x = M1 x).
{ intros x Hx. unfold gc_insh in Hx. apply wbytes_outside; rewrite Ln, u64_lit by lia; lia. }
assert (OUT1 : forall x : word, bv_unsigned x <> gc_fl fs c0 i0 -> M1 x = M x).
{ intros x Hx. unfold M1. apply wbytes_outside; cbn [length Z.of_nat Pos.to_nat]; rewrite u64_lit by lia; lia. }
assert (IN1 : M1 (Z_to_bv 64 (gc_fl fs c0 i0)) = Some (Z_to_bv 8 0)).
{ unfold M1. rewrite wbytes_inside by (cbn [length Z.of_nat Pos.to_nat]; rewrite ?u64_lit by lia; lia). rewrite Z.sub_diag. reflexivity. }
split; [eapply mem_grows_trans; [exact G|]; eapply mem_grows_trans; apply wbytes_grows|]. split.
- intros x Hx Hn.
destruct (Hn c0 i0 V0 ltac:(apply E; [exact V0 | right; split; reflexivity]) C0) as [N1 N2].
rewrite OUT2 by exact N2. rewrite OUT1 by exact N1. apply O; [exact Hx|].
intros c i Vv D C. apply Hn; [exact Vv | apply E; [exact Vv | left; exact D] | exact C].
- intros c i V D C. pose proof (gc_fl_range fs c i V) as FR. pose proof (gc_sh_range fs c0 i0 V0) as [S1 S2].
rewrite OUT2 by (unfold gc_insh; rewrite u64_lit by lia; lia).
destruct (Z.eq_dec (gc_fl fs c i) (gc_fl fs c0 i0)) as [Ef|Nf]; [rewrite Ef; exact IN1|].
rewrite OUT1 by (rewrite u64_lit by lia; exact Nf).
apply E in D; [|exact V]. destruct D as [D|[-> ->]]; [apply (P c i V D C) | contradiction Nf; reflexivity].
Qed.
End GCM.
Lemma gc_post_widen : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "QM'@'S9yR0%211'6y8%511%311p051!p0:1p0;1&Q;r:r8r7r4r3r2r1%877654321&QJr5%2281%3229&QFr<r;%3221'>&QK&S:%12N=%3216%=2E2%6221':r>%11Dr?%11F%53Q231p071pVNQ81r6%Q1768CBQ0N1p031p0C1p0H1p0J1p0N1pT@Q81pTJQD1pU4QE1pU@QF1pU2QG1pU>QH1pQ>QA1pQ<QB1pUBQC1pU0QL1").
Proof.
intros gb mem0 M2 Mf lo hi lo' hi' fs col (G & O & P & Q) L1 L2 G2 O2. split; [eapply mem_grows_trans; eassumption|]. split; [|split; [exact P | exact Q]].
intros x Hx N96 Hn. rewrite (O x) by (first [lia | assumption]). apply O2. exact Hx.
Qed.
Lemma gc_post_ext : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "Q<'@'S9yR0%211'6y8%511%311p051!p0:1p0;1&Q?r2r1%3221&<r4r3%2216r5%1238%6231p081pU6H1pT:I1&Q;r9r8r7r6%574321;>=r:%7716543=?p031p0:1pTBI1pT@J1pTJQ61pU2Q71pU>Q81pQ>Q11pUBQ21pU0Q;1").
Proof.
intros gb mem0 Mf lo hi fs col col' E (G & O & P & Q). split; [exact G|]. split; [|split; [|exact Q]].
- intros x Hx N96 Hn. apply O; [exact Hx | exact N96 |]. intros c i V C. apply Hn; [exact V | apply E; assumption].
- intros c i V C. apply P; [exact V | apply E; assumption].
Qed.
Lemma gc_post_rdn : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "S1'@'S9yR0%211'6y8%511%311p051!p0:1p0;1'4&Q;r9r8r7r6r5r4r3%877654321&QJz%2214&QI&QM%117%3291&QN+2+R0%3221%;251'>%91@%;2B1%?21G%@2GD%5221%>1F%@2H1+S0%B2L1%F231+S1%E2O1%I21N%>241%G1Q0%I2Q21+TP0%K2Q61%O231+QPP0%N231%Q221Q8%G241%Q01Q:%Q22Q<1&Q>r:%211%Q9241&Q=%114%Q<21QC%Q1241':'3%11R0%R311&QD&QGr>&S8%12R:QN%54431QNr?%74613R0%<3931p0>1p0I1p0Q31p0Q=1p0QD1p0QN1p0R21pUDR<1pT2RI1pT@R?1pTJRK1pU2RL1pU>RM1pQ>RF1pUBRG1pU0S01").
Proof.
intros gb mem0 Mf lo hi fs col a n (G & O & P & Q) A1 A2 D1 D2 D3 D4.
destruct n as [|n]; [reflexivity|].
apply rdn_ext; [rewrite u64_lit by lia; lia|]. intros x Hx. rewrite u64_lit in Hx by lia.
apply O; [lia | lia |]. intros c i V _. pose proof (gc_fl_range fs c i V) as FR. pose proof (gc_sh_range fs c i V) as [S1 S2]. unfold gc_insh. lia.
Qed.
Lemma gc_post_flag_keep : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "S1'@'S9yR0%211'6y8%511%311p051!p0:1p0;1&Q;r9r8r7r6r5r4r3%877654321&QJz%2216&QK&QI+TP0%22;1+QPP0%4221&QL+;&QN+2+D%3221%6251%<281+R0%7261%@231'>&Q=%11L%G21M%D2NC%E21B%F21;&Q>%11Q2%M231%:271%O2Q7Q6%L2Q7K%M21J%N21Cr:%Q4221%A261&Q?%12Q=Q<&=%QA2Q@Q?%211':'3%11QL%QO11&QD&QGr>&S8&Q8r;%231QMQL%42R91u1%948721r?%;4:143%@3=31p0B1p0F1p0I1p0Q11p0Q=1p0QO1p0R31pU6RH1pT:RI1pT@R?1pTJRK1pU2RL1pU>RM1pQ>RF1pUBRG1pU0S01").
Proof.
intros gb mem0 Mf lo hi fs col c i (G & O & P & Q) F1 F2 K3 K4 V NC. pose proof (gc_fl_range fs c i V) as FR.
apply rdn_ext; [rewrite u64_lit by lia; cbn [Z.of_nat Pos.to_nat]; lia|]. intros x Hx. rewrite u64_lit in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx.
apply O; [lia | lia |]. intros c' i' V' C'. split.
- intros E. replace (bv_unsigned x) with (gc_fl fs c i) in E by lia. apply (gc_fl_inj fs c i c' i' V V') in E. destruct E as [-> ->]. contradiction.
- pose proof (gc_sh_range fs c' i' V') as [S1 S2]. unfold gc_insh. lia.
Qed.
Lemma gc_post_flag_col : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "R?'@'S9yR0%211'6y8%511%311p051!p0:1p0;1&Q;r9r8r7r6r5r4r3%877654321&QJz%2216&QK&QI+TP0%22;1+QPP0%4221&QL+;&QN+2+D%3221%6251%<281+R0%7261%@231&Q?%12IH%L2KJ':'3%11Q8%Q;11&QD&QGr<&S8&Q8%13Q8Q6Q5%32QD1u1%847621(0(1%82QFQ5(5%11QG%43QH31%62A1%D3A81p0F1p0H1p0K1p0Q=1p0QA1pU6R61pT:R71pT@QM1pTJR91pU2R:1pU>R;1pQ>R41pUBR51pU0R>1").
Proof.
intros gb mem0 Mf lo hi fs col c i (G & O & P & Q) F1 F2 V C. pose proof (gc_fl_range fs c i V) as FR. pose proof (P c i V C) as P1.
change [Z_to_bv 8 0] with (repeat (Z_to_bv 8 0) 1). apply MemSplit.rdn_const; [rewrite u64_lit by lia; cbn [Z.of_nat Pos.to_nat]; lia|].
intros x Hx. rewrite u64_lit in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. rewrite (word_of_u x (gc_fl fs c i)) by lia. exact P1.
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
#[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try solve_keeps_but.
#[local] Ltac mlbq F D z R :=
chain_step; [reflexivity
| eapply step_lb; [exact F | reflexivity | exact D | maddr z; exact R]
| step_simpl; vnorm].
#[local] Ltac kbt := first [ solve [repeat first [left; reflexivity | right]]
| let HIn := fresh "HIn" in let E := fresh "E" in intros HIn; repeat (destruct HIn as [E|HIn]; [discriminate E|]); exact HIn ].
#[local] Ltac stepsdq F D aa vv oktac :=
chain_step; [reflexivity
| eapply step_sd_at with (a := aa) (v := vv); [exact F | reflexivity | exact D | wval | gres; rwH; first [reflexivity | f_equal; lia] | oktac]
| step_simpl].
Section SETSH.
Variable M : word -> option byte.
Variable rom : word -> option byte.
Variables c sh g35 : Z.
Hypothesis Hc : (0 <= c <= 6)%Z.
Hypothesis Hsh : (0 <= sh)%Z /\ (sh + 8 * 2 ^ c < 2 ^ 64)%Z.
Hypothesis Hok : store_ok ASEGS M (Z_to_bv 64 sh) (Z.to_nat (8 * 2 ^ c)) = true.
Definition ssm (k : Z) : word -> option byte := wbytes M (Z_to_bv 64 sh) (concat (repeat (word_to_le_bytes 8 (Z_to_bv 64 g35)) (Z.to_nat k))).
Definition ss_inv (rg : bvmap 5 word) (k : Z) : Prop :=
getr rg 10 = Z_to_bv 64 (k + 1) /\ getr rg 11 = Z_to_bv 64 (sh + 8 * k) /\ getr rg 23 = Z_to_bv 64 g35 /\ getr rg 20 = Z_to_bv 64 c.
Definition ss_keeps (regs regs' : bvmap 5 word) : Prop := forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr regs' r = getr regs r.
#[local] Ltac kp3 := intros r N10 N11 N12; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.
#[using="Hc"] Lemma pow_c_bounds : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC ";'9&QJ+1&QN+2vR4%3221%6251+R0%8231%:231").
Proof.
split; [change 1%Z with (2 ^ 0)%Z | change 64%Z with (2 ^ 6)%Z]; apply Z.pow_le_mono_r; lia.
Qed.
#[using="Hc Hsh"] Lemma ssm_step : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "Q>'@&QJzr1%3221&QKr2&QN+2vR4%3221%6251':'S9yR0%211'6y8%511%311p051&I&Or3%211&S8&QIvS4&QL+8%2217%5241%72B1&Au8vR>%;2F1%4231%A3>61+1%>2A1%C11%N3F41p0Q01p0Q81pU<Q=1").
Proof.
intros k Hk Hk2. unfold ssm.
replace (Z.to_nat (k + 1)) with (Z.to_nat k + 1)%nat by lia.
rewrite repeat_app, concat_app. cbn [repeat concat]. rewrite app_nil_r, wbytes_app. f_equal. unfold at_. rewrite len_concat_le8. f_equal.
destruct Hsh as [S1 S2]. rewrite u_Z2bv by lia. lia.
Qed.
#[using="Hc Hsh Hok"] Lemma gc_setshadow_loop : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "QN'4&By5'S9yR0%211%5241'@&Mr2r1%3221&QJz%2215':&QIr3&QMr5%211%5241+1%7221&QN+2vR4%3221%=3E51';'9'J&QG&QCvR=r6(S7+[dcL(8%33Q321/01Q3&O%11GvS2%;5:9421+[d^H%:3Q:18/01Q:%71E%@5?Q7216%C3B61&N%12AQ:%G231qV4Q@1%J2QA1p0L1p0Q;1p0Q?1pU<QD1pV2QF1pUHQM1").
Proof.
induction q as [|q IH]; intros regs k (H10 & H11 & H23 & H20) Hk Hq; pose proof pow_c_bounds as Pc; destruct Hsh as [S1 S2].
- assert (Hdiv : ((k + 1) / 2 ^ c = 1)%Z) by (replace (k + 1)%Z with (2 ^ c)%Z by lia; apply Z.div_same; lia).
eexists. split.
+ stepsdq (ltac:(oF' 0x5d27c%Z)) (ltac:(oD' 0x5d27c%Z)) (Z_to_bv 64 (sh + 8 * k)) (Z_to_bv 64 g35)
ltac:(apply (store_ok_mono _ _ M); [apply wbytes_grows|];
apply (store_ok_sub ASEGS M (Z_to_bv 64 sh) _ (Z.to_nat (8 * 2 ^ c))); [unorm; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia]).
rewrite (ssm_step k Hk ltac:(lia)).
stepsv (ltac:(oF' 0x5d280%Z)) (ltac:(oD' 0x5d280%Z)) (Z_to_bv 64 1) ltac:(gres; rwH; rewrite v_srl_lit by lia; rewrite Hdiv; reflexivity).
stepiv (ltac:(oF' 0x5d284%Z)) (ltac:(oD' 0x5d284%Z)) (Z_to_bv 64 (sh + 8 * (k + 1))) ltac:(wval).
stepiv (ltac:(oF' 0x5d288%Z)) (ltac:(oD' 0x5d288%Z)) (Z_to_bv 64 (k + 1 + 1)) ltac:(wval).
stepb_ft (ltac:(oF' 0x5d28c%Z)) (ltac:(oD' 0x5d28c%Z)) ltac:(cond).
stepn (ltac:(oF' 0x5d290%Z)) (ltac:(oD' 0x5d290%Z)).
replace (k + 1)%Z with (2 ^ c)%Z by lia.
apply mst_refl.
+ kp3.
- assert (Hdiv : ((k + 1) / 2 ^ c = 0)%Z) by (apply Z.div_small; lia).
assert (STEP : exists r1, msteps ASEGS (mkst regs (0x5d27c : word) (ssm k) rom) (mkst r1 (0x5d27c : word) (ssm (k + 1)) rom) /\ ss_inv r1 (k + 1) /\ ss_keeps regs r1).
{ eexists. split.
- stepsdq (ltac:(oF' 0x5d27c%Z)) (ltac:(oD' 0x5d27c%Z)) (Z_to_bv 64 (sh + 8 * k)) (Z_to_bv 64 g35)
ltac:(apply (store_ok_mono _ _ M); [apply wbytes_grows|];
apply (store_ok_sub ASEGS M (Z_to_bv 64 sh) _ (Z.to_nat (8 * 2 ^ c))); [unorm; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia]).
rewrite (ssm_step k Hk ltac:(lia)).
stepsv (ltac:(oF' 0x5d280%Z)) (ltac:(oD' 0x5d280%Z)) (Z_to_bv 64 0) ltac:(gres; rwH; rewrite v_srl_lit by lia; rewrite Hdiv; reflexivity).
stepiv (ltac:(oF' 0x5d284%Z)) (ltac:(oD' 0x5d284%Z)) (Z_to_bv 64 (sh + 8 * (k + 1))) ltac:(wval).
stepiv (ltac:(oF' 0x5d288%Z)) (ltac:(oD' 0x5d288%Z)) (Z_to_bv 64 (k + 1 + 1)) ltac:(wval).
stepb_tk (ltac:(oF' 0x5d28c%Z)) (ltac:(oD' 0x5d28c%Z)) ltac:(cond).
apply mst_refl.
- split; [unfold ss_inv; post | kp3]. }
destruct STEP as (r1 & RUN1 & INV1 & KP1).
destruct (IH r1 (k + 1)%Z INV1 ltac:(lia) ltac:(lia)) as (r2 & RUN2 & KP2).
exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
intros r N10 N11 N12. rewrite (KP2 r N10 N11 N12). apply KP1; assumption.
Qed.
End SETSH.
#[using="Type"] Lemma gc_kit : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "R9'@'9&QJ+Vb\P0r1%3221&QK&QI+TP0%2251+QPP0%4221&QL+;&QN+2+D%3221%6251%<281+Q?%7261%@231'>&QOr2+U0%3221%J291%K24I%7221%N291%O2K1%J28I%K21H%L21A+QoonlP0%Q3221+`PQoooPP0%Q521>%A231zr3%Q9221%Q522Q4%Q621Q3%Q721L+R0%Q22Q11%Q;231%QA271&Q>%11:%QC2<1&Q=%11=%QB218%QH241%QH23@%QI2=7%Q5221r4%QL21D%Q722Q5%QN2B1%Q:231%R1261%R22:1%R32B1p0M1p0Q61pTJR71pVHR81").
Proof.
intros t fs (F1 & F2 & F3) A. pose proof (gc_shz_facts fs F1 F2 A) as (Z1 & Z2 & Z3 & Z4). repeat split; lia.
Qed.
Section SLOT.
Variables mem0 Mfr : word -> option byte.
Variable rom : word -> option byte.
Variables t fs c nfr nlog frsz flb sparg bot g35 : Z.
Variables flag rs : Z -> Z -> Z.
Hypothesis Hc : (0 <= c <= 10)%Z.
Hypothesis Hnlog : nlog = (14 - c)%Z.
Hypothesis Hnfr : nfr = (2 ^ nlog)%Z.
Hypothesis Hfrsz : frsz = (2 ^ (6 + c))%Z.
Hypothesis Hflb : flb = (fs + 4096 + 32768 - 2 * nfr)%Z.
Hypothesis Ht : (0x1000000 <= t - 160)%Z /\ (t < 2 ^ 64)%Z.
Hypothesis Hfs : (0x693000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= t - 160 \/ t <= fs)%Z.
Hypothesis Happ : (fs + 4096 + 32768 + 11 * 2 ^ 20 <= 0x7fff7000 \/ 0x10007fff8000 <= fs)%Z.
Hypothesis Hshz : (gc_shz_hi fs <= t - 160 \/ t <= gc_shz_lo fs)%Z.
Hypothesis Hsp : (0 <= sparg < 2 ^ 64)%Z /\ (0 <= bot < 2 ^ 64)%Z.
Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.
Hypothesis HF0 : forall c i, gc_valid c i ->
rdn ASEGS mem0 (Z_to_bv 64 (gc_fl fs c i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z.
Hypothesis HCL : forall M', (forall x : word, gc_outz (t - 160) t fs (bv_unsigned x) -> M' x = mem0 x) ->
rdn ASEGS M' (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20))
/\ rt_layout_globs M'
/\ (forall c i, gc_valid c i -> flag c i <> 0%Z ->
rdn ASEGS M' (Z_to_bv 64 (gc_fr fs c i + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i))) /\ (0 <= rs c i < 2 ^ 64)%Z).
Hypothesis HFR : rdn ASEGS Mfr (Z_to_bv 64 (t - 120)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13d728))
/\ rdn ASEGS Mfr (Z_to_bv 64 (t - 128)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13d730))
/\ rdn ASEGS Mfr (Z_to_bv 64 (t - 136)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13d720)).
Hypothesis Hcol6 : forall c i, gc_valid c i -> gc_col sparg bot flag rs c i -> (c <= 6)%Z.
Hypothesis Hshok : forall c i, gc_valid c i -> gc_col sparg bot flag rs c i ->
store_ok ASEGS mem0 (Z_to_bv 64 (gc_sh fs c i)) (Z.to_nat (2 ^ (3 + c))) = true.
#[local] Abbreviation col := (gc_col sparg bot flag rs).
#[local] Abbreviation GCM := (gcm mem0 (t - 160) t fs col).
Definition frm (M : word -> option byte) : Prop :=
forall x : word, (t - 160 <= bv_unsigned x < t)%Z -> ~ (t - 112 <= bv_unsigned x < t - 104)%Z -> M x = Mfr x.
Definition gi2_inv (rg : bvmap 5 word) (i : Z) : Prop :=
getr rg 27 = Z_to_bv 64 i /\ getr rg 24 = Z_to_bv 64 flb /\ getr rg 25 = Z_to_bv 64 fs /\ getr rg 20 = Z_to_bv 64 c
/\ getr rg 7 = Z_to_bv 64 1 /\ getr rg 8 = Z_to_bv 64 (fs + 4096) /\ getr rg 21 = Z_to_bv 64 (6 + c) /\ getr rg 18 = Z_to_bv 64 bot
/\ getr rg 9 = Z_to_bv 64 sparg /\ getr rg 19 = Z_to_bv 64 nlog
/\ getr rg 26 = Z_to_bv 64 0 /\ getr rg 22 = Z_to_bv 64 0x13ca38 /\ getr rg 23 = Z_to_bv 64 g35 /\ getr rg 28 = Z_to_bv 64 6
/\ getr rg 2 = Z_to_bv 64 (t - 144).
Definition gs_keeps (regs regs' : bvmap 5 word) : Prop :=
forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r.
Section SE.
Local Abbreviation SEC_T_gi2_keeps := (ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "D&By5'S9yR0%211%5241'@&Q1r3r1%3221&Q3r4%2215%7226p021p061pU6;1pV4=1pV2>1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_gi2_keeps) 0%nat 0%nat).
Variable regs' : ltac:(sec_ty2 constr:(SEC_T_gi2_keeps) 1%nat 0%nat).
Variable i : ltac:(sec_ty2 constr:(SEC_T_gi2_keeps) 2%nat 0%nat).
Lemma gi2_keeps : ltac:(sec_stmt2 constr:(SEC_T_gi2_keeps) 3%nat 0%nat).
Proof using Type regs regs' i.
intros (H27 & H24 & H25 & H20 & H7 & H8 & H21 & H18 & H9 & H19 & H26 & H22 & H23 & H28 & H2) K.
unfold gi2_inv.
rewrite !K by (intros E; discriminate E). repeat split; assumption.
Qed.
End SE.
#[using="Type"] Lemma gs_keeps_trans : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "A&By5'S9yR0%211%5241&Q3r3r2%3221r5%5214p031p041pUN91pUL:1pUJ;1").
Proof. intros r1 r2 r3 K1 K2 r; intros. rewrite K2 by assumption. apply K1; assumption. Qed.
#[local] Ltac kp9 := intros r; intros; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.
Section SE.
Local Abbreviation SEC_T_gcc_slot_run := (ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "RH&By5'S9yR0%211%5241'6y8%611%311p061'@&Q1r3r1%3221'9&QJzr2%3221&QKvRJ%2241%8241&Q@vRH&QOvS;+U0%3221vR<&Q6vS6vR1vR;vS3%544321&Q7vR4%221Kr4%A7@<>;521&Q0r5%211';'J&QG&QCvR=r9(S7+[d_4(8%33QD21/01QDr8vS2%:598321+[d^H%93QJ17/01QJ%>5=Q<1QA5%A3@51&Q3%12?Q?&QIr7+1%3221%Q12Q01%Q?7Q>Q:Q<Q9Q31QJ%N1QK%QJ221%QK291%QL2<1qQ:R31%Q02R41qV4R:1%Q22R;1p0Q41p0Q81p0QK1p0R51pU6R:1pQ8R<1pV2RB1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_gcc_slot_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_gcc_slot_run) 1%nat 0%nat).
Variable i : ltac:(sec_ty2 constr:(SEC_T_gcc_slot_run) 2%nat 0%nat).
Lemma gcc_slot_run : ltac:(sec_stmt2 constr:(SEC_T_gcc_slot_run) 3%nat 0%nat).
Proof using frsz Hc Hnlog Hnfr Hfrsz Hflb Ht Hfs Happ Hshz Hsp Hwfs HF0 HCL HFR Hcol6 Hshok regs M i.
intros INV Hi GM FRM.
pose proof INV as (H27 & H24 & H25 & H20 & H7 & H8 & H21 & H18 & H9 & H19 & H26 & H22 & H23 & H28 & H2).
pose proof (gc_kit t fs Hfs Happ) as (K1 & K2 & K3 & K4).
destruct Hfs as (Fs1 & Fs2 & Fs3). destruct Hsp as [Sp1 Sp2]. destruct Ht as [Ta Tb].
pose proof (gc_pow_facts c Hc) as (P1 & P2 & P3 & P4 & P5).
assert (V : gc_valid c i) by (split; [exact Hc | rewrite <- Hnlog, <- Hnfr; exact Hi]).
assert (Efl : (flb + i)%Z = gc_fl fs c i) by (unfold gc_fl; rewrite Hflb, Hnfr, Hnlog; reflexivity).
assert (Eff : (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz)%Z = gc_fr fs c i) by (unfold gc_fr; rewrite Hfrsz; reflexivity).
pose proof (gc_fl_range fs c i V) as FLR. pose proof (gc_fr_range fs c i V) as [FRR1 FRR2]. pose proof (gc_sh_range fs c i V) as [SHR1 SHR2].
assert (Nfr : (16 <= nfr <= 16384)%Z) by (rewrite Hnfr, Hnlog; exact P1).
assert (Fb : (64 <= frsz <= 65536)%Z) by (rewrite Hfrsz; exact P2).
assert (Nl : (0 <= nlog <= 14)%Z) by lia.
destruct (HF0 c i V) as [Fi0 Bi].
assert (Fi : rdn ASEGS M (Z_to_bv 64 (flb + i)) 1%nat = Some [Z_to_bv 8 (flag c i)]).
{ rewrite Efl, <- Fi0. apply rdn_ext; [rewrite u64_lit by lia; cbn [Z.of_nat Pos.to_nat]; lia|].
intros x Hx. rewrite u64_lit in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx.
rewrite (word_of_u x (gc_fl fs c i)) by lia.
eapply (gcm_flag mem0 (t - 160) t fs col K1 K3 K4); [exact GM | exact V | unfold gc_done_lt; lia]. }
assert (OUTZ : forall x : word, gc_outz (t - 160) t fs (bv_unsigned x) -> M x = mem0 x).
{ intros x (O1 & O2 & O3). exact (gcm_out mem0 (t - 160) t fs col K3 _ M GM x O1 O2 O3). }
destruct (HCL M OUTZ) as (HL & HGL & HRS).
assert (EDONE : forall c' i', gc_valid c' i' -> (gc_done_lt c (i + 1) c' i' <-> gc_done_lt c i c' i' \/ (c' = c /\ i' = i))).
{ intros c' i' _. unfold gc_done_lt. lia. }
destruct (Z.eq_dec (flag c i) 0) as [F0|F1].
{
exists (regupd (regupd regs 11 (Z_to_bv 64 (flb + i))) 10 (Z_to_bv 64 0)), M. split; [|split; [kp9 | split; [|exact FRM]]].
- stepiv (ltac:(oF' 0x5d1e4%Z)) (ltac:(oD' 0x5d1e4%Z)) (Z_to_bv 64 (flb + i)) ltac:(wval).
chain_step; [reflexivity | eapply step_lbu; [exact (ltac:(oF' 0x5d1e8%Z)) | reflexivity | exact (ltac:(oD' 0x5d1e8%Z)) | maddr (flb + i)%Z; exact Fi] | step_simpl; vnorm].
stepb_tk (ltac:(oF' 0x5d1ec%Z)) (ltac:(oD' 0x5d1ec%Z)) ltac:(rewrite (u_Z2bv8 (flag c i)) by lia; cond).
rewrite F0. apply mst_refl.
- apply (gcm_skip mem0 (t - 160) t fs col (gc_done_lt c i) _ M c i); [|exact EDONE | exact GM].
intros (NZ & _). contradiction. }
destruct (HRS c i V F1) as (Ri0 & Bri).
assert (Ri : rdn ASEGS M (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i))))
by (rewrite Eff; exact Ri0).
#[local] Ltac runB Fi HL Ri flb i fs c frsz Hfrsz flagci :=
stepiv (ltac:(oF' 0x5d1e4%Z)) (ltac:(oD' 0x5d1e4%Z)) (Z_to_bv 64 (flb + i)) ltac:(wval);
(chain_step; [reflexivity | eapply step_lbu; [exact (ltac:(oF' 0x5d1e8%Z)) | reflexivity | exact (ltac:(oD' 0x5d1e8%Z)) | maddr (flb + i)%Z; exact Fi] | step_simpl; vnorm]);
stepb_ft (ltac:(oF' 0x5d1ec%Z)) (ltac:(oD' 0x5d1ec%Z)) ltac:(rewrite (u_Z2bv8 flagci) by lia; cond);
mldq (ltac:(oF' 0x5d1f0%Z)) (ltac:(oD' 0x5d1f0%Z)) (fs + 88)%Z HL;
stepn (ltac:(oF' 0x5d1f4%Z)) (ltac:(oD' 0x5d1f4%Z));
stepsv (ltac:(oF' 0x5d1f8%Z)) (ltac:(oD' 0x5d1f8%Z)) (Z_to_bv 64 (c * 2 ^ 20)) ltac:(gres; rwH; apply v_sll_lit; lia);
stepn (ltac:(oF' 0x5d1fc%Z)) (ltac:(oD' 0x5d1fc%Z));
stepiv (ltac:(oF' 0x5d200%Z)) (ltac:(oD' 0x5d200%Z)) (Z_to_bv 64 (fs + 4096 + c * 2 ^ 20)) ltac:(wval);
stepiv (ltac:(oF' 0x5d204%Z)) (ltac:(oD' 0x5d204%Z)) (Z_to_bv 64 (fs + 4096 + c * 2 ^ 20 + 32768)) ltac:(wval);
stepsv (ltac:(oF' 0x5d208%Z)) (ltac:(oD' 0x5d208%Z)) (Z_to_bv 64 (i * frsz)) ltac:(gres; rwH; rewrite v_sll_lit by lia; rewrite <- Hfrsz; reflexivity);
stepiv (ltac:(oF' 0x5d20c%Z)) (ltac:(oD' 0x5d20c%Z)) (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz)) ltac:(gres; rwH; unfold v_add; unorm; f_equal; nia);
mldq (ltac:(oF' 0x5d210%Z)) (ltac:(oD' 0x5d210%Z)) (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz + 24)%Z Ri.
destruct (Z.le_gt_cases (rs c i) bot) as [LE|GT].
{
eexists. exists M. split; [|split; [|split; [|exact FRM]]].
- runB Fi HL Ri flb i fs c frsz Hfrsz (flag c i).
stepb_tk (ltac:(oF' 0x5d214%Z)) (ltac:(oD' 0x5d214%Z)) ltac:(cond).
apply mst_refl.
- kp9.
- apply (gcm_skip mem0 (t - 160) t fs col (gc_done_lt c i) _ M c i); [|exact EDONE | exact GM].
intros (_ & NC). lia. }
destruct (Z.le_gt_cases sparg (rs c i)) as [GE|LT].
{
eexists. exists M. split; [|split; [|split; [|exact FRM]]].
- runB Fi HL Ri flb i fs c frsz Hfrsz (flag c i).
stepb_ft (ltac:(oF' 0x5d214%Z)) (ltac:(oD' 0x5d214%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x5d218%Z)) (ltac:(oD' 0x5d218%Z)) ltac:(cond).
apply mst_refl.
- kp9.
- apply (gcm_skip mem0 (t - 160) t fs col (gc_done_lt c i) _ M c i); [|exact EDONE | exact GM].
intros (_ & NC). lia. }
assert (COL : col c i) by (split; [exact F1 | lia]).
pose proof (Hcol6 c i V COL) as C6. pose proof (Hshok c i V COL) as SHOK.
destruct GM as (GMG & GMO & GMP).
set (M1 := wbytes M (Z_to_bv 64 (gc_fl fs c i)) [Z_to_bv 8 0]).
assert (G1 : mem_grows mem0 M1) by (unfold M1; eapply mem_grows_trans; [exact GMG | apply wbytes_grows]).
assert (OUTZ1 : forall x : word, gc_outz (t - 160) t fs (bv_unsigned x) -> M1 x = mem0 x).
{ intros x OZ. pose proof OZ as (O1 & O2 & O3). unfold M1. rewrite wbytes_outside; [apply OUTZ; exact OZ | |]; cbn [length Z.of_nat Pos.to_nat]; rewrite u64_lit by (clear - Bi F1 FLR Fb Fs1 Fs2 Fs3 Happ Hc Hfrsz Hfs Hshz K3 K4 Nl O1 O3 P5 SHR1 SHR2 Ta c flag frsz fs i nlog t x; lia); lia. }
destruct (HCL M1 OUTZ1) as (_ & (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8) & _). unfold SB in Y2. unfold HIGHEND in Y8.
assert (FR1 : forall a, (t - 160 <= a)%Z -> (a + 8 <= t)%Z -> (a + 8 <= t - 112 \/ t - 104 <= a)%Z ->
rdn ASEGS M1 (Z_to_bv 64 a) 8%nat = rdn ASEGS Mfr (Z_to_bv 64 a) 8%nat).
{ intros a A1 A2 A3. apply rdn_ext; [rewrite u64_lit by lia; cbn [Z.of_nat Pos.to_nat]; lia|].
intros x Hx. rewrite u64_lit in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx.
unfold M1. rewrite wbytes_outside; [apply FRM; lia | |]; cbn [length Z.of_nat Pos.to_nat]; rewrite u64_lit by lia; lia. }
destruct HFR as (HFR1 & HFR2 & HFR3).
rewrite <- (FR1 (t - 120)%Z) in HFR1 by lia. rewrite <- (FR1 (t - 128)%Z) in HFR2 by lia. rewrite <- (FR1 (t - 136)%Z) in HFR3 by lia.
assert (WFL : store_ok ASEGS M (Z_to_bv 64 (flb + i)) 1%nat = true).
{ apply (store_ok_mono _ _ mem0 M _ GMG).
apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 fs) _ (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20))); [rewrite u64_lit by lia; lia | exact Hwfs | rewrite !u64_lit by lia; lia | rewrite !u64_lit by lia; cbn [Z.of_nat Pos.to_nat]; lia]. }
assert (Esh : gc_sh fs c i = (2147450880 + gc_fr fs c i / 8)%Z) by reflexivity.
assert (E8 : (8 * 2 ^ c = 2 ^ (3 + c))%Z) by (rewrite Z.pow_add_r by lia; reflexivity).
assert (INAPP : in_app (gc_fr fs c i)) by (apply gc_fr_in_app; assumption).
assert (PRE : exists r1, msteps ASEGS (mkst regs (0x5d1e4 : word) M rom) (mkst r1 (0x5d27c : word) M1 rom)
/\ ss_inv c (gc_sh fs c i) g35 r1 0 /\ gs_keeps regs r1).
{ unfold in_app, LOWEND, HIGHBEG, HIGHEND in INAPP. destruct INAPP as [LOW|HIGH].
- eexists. split; [|split].
+ runB Fi HL Ri flb i fs c frsz Hfrsz (flag c i).
stepb_ft (ltac:(oF' 0x5d214%Z)) (ltac:(oD' 0x5d214%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x5d218%Z)) (ltac:(oD' 0x5d218%Z)) ltac:(cond).
chain_step; [reflexivity | eapply (step_sb_at ASEGS) with (a := Z_to_bv 64 (flb + i)) (b := Z_to_bv 8 0);
[exact (ltac:(oF' 0x5d21c%Z)) | reflexivity | exact (ltac:(oD' 0x5d21c%Z)) | wval | gres; rwH; reflexivity | apply bv_eq; vm_compute; reflexivity | exact WFL ] | step_simpl; vnorm].
rewrite Efl. change (wbytes M (Z_to_bv 64 (gc_fl fs c i)) [Z_to_bv 8 0]) with M1.
mld (ltac:(oF' 0x5d220%Z)) (ltac:(oD' 0x5d220%Z)) (0x13ca38 : word) Y2.
stepn (ltac:(oF' 0x5d224%Z)) (ltac:(oD' 0x5d224%Z)).
stepn (ltac:(oF' 0x5d228%Z)) (ltac:(oD' 0x5d228%Z)).
stepn (ltac:(oF' 0x5d22c%Z)) (ltac:(oD' 0x5d22c%Z)).
stepn (ltac:(oF' 0x5d230%Z)) (ltac:(oD' 0x5d230%Z)).
stepb_tk (ltac:(oF' 0x5d234%Z)) (ltac:(oD' 0x5d234%Z)) ltac:(rewrite Eff; cond).
stepb_ft (ltac:(oF' 0x5d26c%Z)) (ltac:(oD' 0x5d26c%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x5d270%Z)) (ltac:(oD' 0x5d270%Z)) (Z_to_bv 64 (gc_fr fs c i / 8)) ltac:(rewrite Eff; wval).
stepiv (ltac:(oF' 0x5d274%Z)) (ltac:(oD' 0x5d274%Z)) (Z_to_bv 64 (gc_sh fs c i + 8 * 0)) ltac:(rewrite Esh; wval).
stepn (ltac:(oF' 0x5d278%Z)) (ltac:(oD' 0x5d278%Z)).
apply mst_refl.
+ unfold ss_inv. post.
+ kp9.
- eexists. split; [|split].
+ runB Fi HL Ri flb i fs c frsz Hfrsz (flag c i).
stepb_ft (ltac:(oF' 0x5d214%Z)) (ltac:(oD' 0x5d214%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x5d218%Z)) (ltac:(oD' 0x5d218%Z)) ltac:(cond).
chain_step; [reflexivity | eapply (step_sb_at ASEGS) with (a := Z_to_bv 64 (flb + i)) (b := Z_to_bv 8 0);
[exact (ltac:(oF' 0x5d21c%Z)) | reflexivity | exact (ltac:(oD' 0x5d21c%Z)) | wval | gres; rwH; reflexivity | apply bv_eq; vm_compute; reflexivity | exact WFL ] | step_simpl; vnorm].
rewrite Efl. change (wbytes M (Z_to_bv 64 (gc_fl fs c i)) [Z_to_bv 8 0]) with M1.
mld (ltac:(oF' 0x5d220%Z)) (ltac:(oD' 0x5d220%Z)) (0x13ca38 : word) Y2.
stepn (ltac:(oF' 0x5d224%Z)) (ltac:(oD' 0x5d224%Z)).
stepn (ltac:(oF' 0x5d228%Z)) (ltac:(oD' 0x5d228%Z)).
stepn (ltac:(oF' 0x5d22c%Z)) (ltac:(oD' 0x5d22c%Z)).
stepn (ltac:(oF' 0x5d230%Z)) (ltac:(oD' 0x5d230%Z)).
stepb_ft (ltac:(oF' 0x5d234%Z)) (ltac:(oD' 0x5d234%Z)) ltac:(rewrite Eff; cond).
mldq (ltac:(oF' 0x5d238%Z)) (ltac:(oD' 0x5d238%Z)) (t - 120)%Z HFR1.
mld (ltac:(oF' 0x5d23c%Z)) (ltac:(oD' 0x5d23c%Z)) (0x13d728 : word) Y4.
mldq (ltac:(oF' 0x5d240%Z)) (ltac:(oD' 0x5d240%Z)) (t - 128)%Z HFR2.
mld (ltac:(oF' 0x5d244%Z)) (ltac:(oD' 0x5d244%Z)) (0x13d730 : word) Y6.
stepn (ltac:(oF' 0x5d248%Z)) (ltac:(oD' 0x5d248%Z)).
stepb_tk (ltac:(oF' 0x5d24c%Z)) (ltac:(oD' 0x5d24c%Z)) ltac:(rewrite Eff; cond).
mldq (ltac:(oF' 0x5d254%Z)) (ltac:(oD' 0x5d254%Z)) (t - 136)%Z HFR3.
mld (ltac:(oF' 0x5d258%Z)) (ltac:(oD' 0x5d258%Z)) (0x13d720 : word) Y8.
stepn (ltac:(oF' 0x5d25c%Z)) (ltac:(oD' 0x5d25c%Z)).
stepn (ltac:(oF' 0x5d260%Z)) (ltac:(oD' 0x5d260%Z)).
stepb_ft (ltac:(oF' 0x5d264%Z)) (ltac:(oD' 0x5d264%Z)) ltac:(rewrite Eff; cond).
stepb_ft (ltac:(oF' 0x5d268%Z)) (ltac:(oD' 0x5d268%Z)) ltac:(rewrite Eff; cond).
stepb_ft (ltac:(oF' 0x5d26c%Z)) (ltac:(oD' 0x5d26c%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x5d270%Z)) (ltac:(oD' 0x5d270%Z)) (Z_to_bv 64 (gc_fr fs c i / 8)) ltac:(rewrite Eff; wval).
stepiv (ltac:(oF' 0x5d274%Z)) (ltac:(oD' 0x5d274%Z)) (Z_to_bv 64 (gc_sh fs c i + 8 * 0)) ltac:(rewrite Esh; wval).
stepn (ltac:(oF' 0x5d278%Z)) (ltac:(oD' 0x5d278%Z)).
apply mst_refl.
+ unfold ss_inv. post.
+ kp9. }
destruct PRE as (r1 & RUN1 & SI & KP1).
destruct K2 as [K2a K2b].
assert (SHOK1 : store_ok ASEGS M1 (Z_to_bv 64 (gc_sh fs c i)) (Z.to_nat (8 * 2 ^ c)) = true)
by (rewrite E8; apply (store_ok_mono _ _ mem0 M1 _ G1); exact SHOK).
assert (Pc : (1 <= 2 ^ c)%Z) by (change 1%Z with (2 ^ 0)%Z; apply Z.pow_le_mono_r; lia).
destruct (gc_setshadow_loop M1 rom c (gc_sh fs c i) g35 ltac:(lia) ltac:(split; lia) SHOK1 (Z.to_nat (2 ^ c - 1)) r1 0%Z SI ltac:(lia) ltac:(lia))
as (r2 & RUN2 & KP2).
change (ssm M1 (gc_sh fs c i) g35 0) with M1 in RUN2.
exists r2, (ssm M1 (gc_sh fs c i) g35 (2 ^ c)). split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. split; [|split].
- intros r; intros. rewrite KP2 by assumption. apply KP1; assumption.
- assert (LN : Z.of_nat (length (concat (repeat (word_to_le_bytes 8 (Z_to_bv 64 g35)) (Z.to_nat (2 ^ c))))) = (2 ^ (3 + c))%Z)
by (rewrite len_concat_le8, Z2Nat.id by lia; exact E8).
unfold ssm, M1.
apply (gcm_collect mem0 (t - 160) t fs col K1 (conj K2a K2b) K3 (gc_done_lt c i) _ M c i _ V COL LN EDONE). split; [exact GMG | split; [exact GMO | exact GMP]].
- assert (LN : Z.of_nat (length (concat (repeat (word_to_le_bytes 8 (Z_to_bv 64 g35)) (Z.to_nat (2 ^ c))))) = (2 ^ (3 + c))%Z)
by (rewrite len_concat_le8, Z2Nat.id by lia; exact E8).
intros x Hx1 Hx2. unfold ssm, M1.
rewrite wbytes_outside; [rewrite wbytes_outside; [apply FRM; assumption | |] | |];
rewrite ?LN; cbn [length Z.of_nat Pos.to_nat]; rewrite u64_lit by lia; lia.
Qed.
End SE.
Definition gi_keeps2 (regs regs' : bvmap 5 word) : Prop :=
forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> 27%bv ->
getr regs' r = getr regs r.
#[local] Ltac kp10 := intros r; intros; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.
#[using="frsz Hc Hnlog Hnfr Hfrsz Hflb Ht Hfs Happ Hshz Hsp Hwfs HF0 HCL HFR Hcol6 Hshok"] Lemma gcc_inner_run : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "RO'4&By5'S9yR0%211%5241'6y8%611%311p061'@&Q1r3r1%3221&QJzr2%3221':&QI&QMr6%211%42<1+1%6221vRJ%93B21&Q@vRH&QOvS;+U0%3221vR<&Q6vS6vR1vR;vS3%544321&Q7vR4r4%3221r5%B7A=?<621&Q0%11K';'9'J&QG&QCvR=r:(S7+[d_4(8%33QJ21/01QJr9vS2%:598321+[d[D%93R017/01R0%>5=QC1QG5%A3@51%QK2QEQ;&Q2%12@QG%O2NQ>%Q=7Q<Q8Q:Q7Q11QM%K1QN%I221%J251%K281%L2:1qQ:R71%O2R81qV4R>1%Q12R?1p0Q31p0Q61p0QJ1p0R51p0R:1pU6R?1pQ8RA1pV2RG1pUHRN1").
Proof.
induction q as [|q IH]; intros regs M i INV Hi Hq GM FRM;
pose proof (gc_pow_facts c Hc) as (P1 & _);
assert (Nfr : (16 <= nfr <= 16384)%Z) by (rewrite Hnfr, Hnlog; exact P1);
assert (Nl : (0 <= nlog <= 14)%Z) by lia;
destruct (gcc_slot_run regs M i INV ltac:(lia) GM FRM) as (r1 & M1 & RUN1 & KP1 & GM1 & FRM1);
pose proof (gi2_keeps regs r1 i INV KP1) as (H27 & H24 & H25 & H20 & H7 & H8 & H21 & H18 & H9 & H19 & H26 & H22 & H23 & H28 & H2).
-
assert (Hdiv : ((i + 1) / 2 ^ nlog = 1)%Z) by (rewrite <- Hnfr; replace (i + 1)%Z with nfr by lia; apply Z.div_same; lia).
assert (TAIL : exists r2, msteps ASEGS (mkst r1 (0x5d1d8 : word) M1 rom) (mkst r2 (0x5d174 : word) M1 rom) /\ gi2_inv r2 nfr /\ gi_keeps2 r1 r2).
{ eexists. split; [|split].
- stepiv (ltac:(oF' 0x5d1d8%Z)) (ltac:(oD' 0x5d1d8%Z)) (Z_to_bv 64 (i + 1)) ltac:(wval).
stepsv (ltac:(oF' 0x5d1dc%Z)) (ltac:(oD' 0x5d1dc%Z)) (Z_to_bv 64 1) ltac:(gres; rwH; rewrite v_srl_lit by lia; rewrite Hdiv; reflexivity).
stepb_tk (ltac:(oF' 0x5d1e0%Z)) (ltac:(oD' 0x5d1e0%Z)) ltac:(cond).
apply mst_refl.
- unfold gi2_inv. post.
- kp10. }
destruct TAIL as (r2 & RUN2 & INV2 & KP2).
exists r2, M1. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. split; [exact INV2|]. split; [|split; [|exact FRM1]].
+ intros r; intros. rewrite KP2 by assumption. apply KP1; assumption.
+ replace nfr with (i + 1)%Z by lia. exact GM1.
- assert (Hdiv : ((i + 1) / 2 ^ nlog = 0)%Z) by (apply Z.div_small; rewrite <- Hnfr; lia).
assert (TAIL : exists r2, msteps ASEGS (mkst r1 (0x5d1d8 : word) M1 rom) (mkst r2 (0x5d1e4 : word) M1 rom) /\ gi2_inv r2 (i + 1) /\ gi_keeps2 r1 r2).
{ eexists. split; [|split].
- stepiv (ltac:(oF' 0x5d1d8%Z)) (ltac:(oD' 0x5d1d8%Z)) (Z_to_bv 64 (i + 1)) ltac:(wval).
stepsv (ltac:(oF' 0x5d1dc%Z)) (ltac:(oD' 0x5d1dc%Z)) (Z_to_bv 64 0) ltac:(gres; rwH; rewrite v_srl_lit by lia; rewrite Hdiv; reflexivity).
stepb_ft (ltac:(oF' 0x5d1e0%Z)) (ltac:(oD' 0x5d1e0%Z)) ltac:(cond).
apply mst_refl.
- unfold gi2_inv. post.
- kp10. }
destruct TAIL as (r2 & RUN2 & INV2 & KP2).
destruct (IH r2 M1 (i + 1)%Z INV2 ltac:(lia) ltac:(lia) GM1 FRM1) as (r3 & M3 & RUN3 & INV3 & KP3 & GM3 & FRM3).
exists r3, M3. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2 | exact RUN3]|].
split; [exact INV3|]. split; [|split; [exact GM3 | exact FRM3]].
intros r; intros. rewrite KP3 by assumption. rewrite KP2 by assumption. apply KP1; assumption.
Qed.
End SLOT.
Section CLASS.
Variables mem0 Mfr : word -> option byte.
Variable rom : word -> option byte.
Variables t fs sparg bot g35 : Z.
Variables flag rs : Z -> Z -> Z.
Hypothesis Ht : (0x1000000 <= t - 160)%Z /\ (t < 2 ^ 64)%Z.
Hypothesis Hfs : (0x693000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= t - 160 \/ t <= fs)%Z.
Hypothesis Happ : (fs + 4096 + 32768 + 11 * 2 ^ 20 <= 0x7fff7000 \/ 0x10007fff8000 <= fs)%Z.
Hypothesis Hshz : (gc_shz_hi fs <= t - 160 \/ t <= gc_shz_lo fs)%Z.
Hypothesis Hsp : (0 <= sparg < 2 ^ 64)%Z /\ (0 <= bot < 2 ^ 64)%Z.
Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (t - 160)) 160%nat = true.
Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.
Hypothesis HF0 : forall c i, gc_valid c i ->
rdn ASEGS mem0 (Z_to_bv 64 (gc_fl fs c i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z.
Hypothesis HCL : forall M', (forall x : word, gc_outz (t - 160) t fs (bv_unsigned x) -> M' x = mem0 x) ->
rdn ASEGS M' (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20))
/\ rt_layout_globs M'
/\ (forall c i, gc_valid c i -> flag c i <> 0%Z ->
rdn ASEGS M' (Z_to_bv 64 (gc_fr fs c i + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i))) /\ (0 <= rs c i < 2 ^ 64)%Z).
Hypothesis HFR : rdn ASEGS Mfr (Z_to_bv 64 (t - 120)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13d728))
/\ rdn ASEGS Mfr (Z_to_bv 64 (t - 128)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13d730))
/\ rdn ASEGS Mfr (Z_to_bv 64 (t - 136)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13d720)).
Hypothesis Hcol6 : forall c i, gc_valid c i -> gc_col sparg bot flag rs c i -> (c <= 6)%Z.
Hypothesis Hshok : forall c i, gc_valid c i -> gc_col sparg bot flag rs c i ->
store_ok ASEGS mem0 (Z_to_bv 64 (gc_sh fs c i)) (Z.to_nat (2 ^ (3 + c))) = true.
#[local] Abbreviation col := (gc_col sparg bot flag rs).
#[local] Abbreviation GCM := (gcm mem0 (t - 160) t fs col).
#[local] Abbreviation FRM := (frm Mfr t).
Definition gcl2_inv (rg : bvmap 5 word) (c : Z) : Prop :=
getr rg 20 = Z_to_bv 64 c /\ getr rg 25 = Z_to_bv 64 fs /\ getr rg 7 = Z_to_bv 64 1 /\ getr rg 8 = Z_to_bv 64 (fs + 4096)
/\ getr rg 18 = Z_to_bv 64 bot /\ getr rg 9 = Z_to_bv 64 sparg /\ getr rg 2 = Z_to_bv 64 (t - 144)
/\ getr rg 26 = Z_to_bv 64 0 /\ getr rg 22 = Z_to_bv 64 0x13ca38 /\ getr rg 23 = Z_to_bv 64 g35 /\ getr rg 28 = Z_to_bv 64 6.
Definition gcl_keeps2 (regs regs' : bvmap 5 word) : Prop :=
forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> 27%bv ->
r <> 21%bv -> r <> 24%bv -> r <> 19%bv -> r <> 20%bv -> getr regs' r = getr regs r.
#[local] Ltac kp14 := intros r; intros; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.
Section SE.
Local Abbreviation SEC_T_gcc_class_run := (ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "RI&By5'S9yR0%211%5241'6y8%611%311p061'@&Kr3r1%3221'9&QJzr2%3221+:%5231%7231&Q@vRH&QOvS;+U0%3221vR<&Q6vS6vR1vR;vS3%544321&Q7%12IDr4%@7?;=:421&Q4vGr5%332A1';'J&QG&QCvR=r9(S7+[d\0(8%33QC21/01QCr8vS2%:598321+[d[D%93QI17/01QI%>5=Q;1Q@5%A3@51r7%QE2Q>1&L%12AQ@&QI+1%2261%Q221QE%Q@7Q?Q;Q=Q:Q41QJ%Q03OQ>QK%QJ221%QK281%QL2;1%QM2>1qQ:R41%Q22R51qV4R;1%Q42R<1p0Q61p0Q;1p0QM1p0R61pT:R;1pQ8R=1pV2RC1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_gcc_class_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_gcc_class_run) 1%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_gcc_class_run) 2%nat 0%nat).
Lemma gcc_class_run : ltac:(sec_stmt2 constr:(SEC_T_gcc_class_run) 3%nat 0%nat).
Proof using Ht Hfs Happ Hshz Hsp Hok Hwfs HF0 HCL HFR Hcol6 Hshok regs M c.
intros (H20 & H25 & H7 & H8 & H18 & H9 & H2 & H26 & H22 & H23 & H28) Hc GM FR.
destruct (gc_facts_all c Hc) as (nfr & frsz & k1 & (Fn & Ff & Ff2 & Fk & Fk1 & Fand)).
pose proof (gc_pow_facts c Hc) as (P1 & P2 & _).
assert (Nb : (16 <= nfr <= 16384)%Z) by (rewrite Fn; exact P1).
assert (Fb : (64 <= frsz <= 65536)%Z) by (rewrite Ff; exact P2).
pose proof (gc_kit t fs Hfs Happ) as (K1 & K2 & K3 & K4).
destruct Hfs as (Fs1 & Fs2 & Fs3). destruct Ht as [Ta Tb]. destruct Hsp as [Sp1 Sp2].
assert (OUTZ : forall x : word, gc_outz (t - 160) t fs (bv_unsigned x) -> M x = mem0 x).
{ intros x (O1 & O2 & O3). exact (gcm_out mem0 (t - 160) t fs col K3 _ M GM x O1 O2 O3). }
destruct (HCL M OUTZ) as (CL & _).
pose proof GM as (GMG & _).
set (M' := wbytes M (Z_to_bv 64 (t - 112)) (word_to_le_bytes 8 (Z_to_bv 64 frsz))).
assert (OM' : forall x : word, ~ (t - 112 <= bv_unsigned x < t - 104)%Z -> M' x = M x).
{ intros x Hx. unfold M'. apply wbytes_outside; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; rewrite u64_lit by lia; lia. }
assert (GM' : GCM (gc_done_lt c 0) M').
{ apply (gcm_frame mem0 (t - 160) t fs col K1 K4 _ M M' GM); [unfold M'; apply wbytes_grows|]. intros x Hx. apply OM'. lia. }
assert (FR' : FRM M') by (intros x Hx1 Hx2; rewrite OM' by exact Hx2; apply FR; assumption).
assert (exists flb, flb = fs + 4096 + 32768 - 2 * nfr)%Z as (flb & Hflb) by (eexists; reflexivity).
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x5d180 : word) M rom) (mkst r1 (0x5d1e4 : word) M' rom)
/\ gi2_inv t fs c (14 - c) flb sparg bot g35 r1 0 /\ gcl_keeps2 regs r1).
{ eexists. split; [|split].
- stepn (ltac:(oF' 0x5d180%Z)) (ltac:(oD' 0x5d180%Z)).
mldq (ltac:(oF' 0x5d184%Z)) (ltac:(oD' 0x5d184%Z)) (fs + 88)%Z CL.
stepn (ltac:(oF' 0x5d188%Z)) (ltac:(oD' 0x5d188%Z)).
stepsv (ltac:(oF' 0x5d18c%Z)) (ltac:(oD' 0x5d18c%Z)) (Z_to_bv 64 (10 - c)) ltac:(gres; rwH; unfold v_subw; unorm; rewrite swrap32_small by lia; reflexivity).
stepiv (ltac:(oF' 0x5d190%Z)) (ltac:(oD' 0x5d190%Z)) (Z_to_bv 64 (6 + c)) ltac:(wval).
stepiv (ltac:(oF' 0x5d194%Z)) (ltac:(oD' 0x5d194%Z)) (Z_to_bv 64 18446744073709551615) ltac:(gres; apply bv_eq; vm_compute; reflexivity).
stepsv (ltac:(oF' 0x5d198%Z)) (ltac:(oD' 0x5d198%Z)) (Z_to_bv 64 (18446744073709551615 * 2 ^ (10 - c))) ltac:(gres; rwH; apply v_sll_lit; lia).
stepiv (ltac:(oF' 0x5d19c%Z)) (ltac:(oD' 0x5d19c%Z)) (Z_to_bv 64 k1) ltac:(gres; rwH; unfold v_andi; change (bv_wrap 64 1023) with 1023%Z; exact Fand).
stepn (ltac:(oF' 0x5d1a0%Z)) (ltac:(oD' 0x5d1a0%Z)).
stepiv (ltac:(oF' 0x5d1a4%Z)) (ltac:(oD' 0x5d1a4%Z)) (Z_to_bv 64 (20 - c)) ltac:(wval).
stepsv (ltac:(oF' 0x5d1a8%Z)) (ltac:(oD' 0x5d1a8%Z)) (Z_to_bv 64 (32 * k1)) ltac:(gres; rwH; rewrite v_sll_lit by lia; change (2 ^ 5)%Z with 32%Z; f_equal; lia).
stepiv (ltac:(oF' 0x5d1ac%Z)) (ltac:(oD' 0x5d1ac%Z)) (Z_to_bv 64 (14 - c)) ltac:(wval).
stepiv (ltac:(oF' 0x5d1b0%Z)) (ltac:(oD' 0x5d1b0%Z)) (Z_to_bv 64 flb) ltac:(wval).
stepn (ltac:(oF' 0x5d1b4%Z)) (ltac:(oD' 0x5d1b4%Z)).
stepsv (ltac:(oF' 0x5d1b8%Z)) (ltac:(oD' 0x5d1b8%Z)) (Z_to_bv 64 frsz) ltac:(gres; rwH; rewrite v_sll_lit by lia; rewrite Ff2; reflexivity).
stepsdq (ltac:(oF' 0x5d1bc%Z)) (ltac:(oD' 0x5d1bc%Z)) (Z_to_bv 64 (t - 112)) (Z_to_bv 64 frsz)
ltac:(apply (store_ok_mono _ _ mem0); [exact GMG|];
apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (t - 160)) _ 160%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).
change (wbytes M (Z_to_bv 64 (t - 112)) (word_to_le_bytes 8 (Z_to_bv 64 frsz))) with M'.
stepn (ltac:(oF' 0x5d1c0%Z)) (ltac:(oD' 0x5d1c0%Z)).
apply mst_refl.
- unfold gi2_inv. post.
- kp14. }
destruct S1 as (r1 & RUN1 & I1 & KS1).
destruct (gcc_inner_run mem0 Mfr rom t fs c nfr (14 - c) frsz flb sparg bot g35 flag rs Hc eq_refl Fn Ff Hflb (conj Ta Tb) (conj Fs1 (conj Fs2 Fs3)) Happ Hshz
(conj Sp1 Sp2) Hwfs HF0 HCL HFR Hcol6 Hshok (Z.to_nat (nfr - 1)) r1 M' 0%Z I1 ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) GM' FR')
as (r2 & M2 & RUN2 & I2 & KS2 & GM2 & FR2).
exists r2, M2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. split; [|split; [|split; [|exact FR2]]].
- destruct I2 as (J27 & J24 & J25 & J20 & J7 & J8 & J21 & J18 & J9 & J19 & J26 & J22 & J23 & J28 & J2). unfold gcl2_inv. repeat split; assumption.
- intros r; intros. rewrite KS2 by assumption. apply KS1; assumption.
- apply (gcm_equiv mem0 (t - 160) t fs col (gc_done_lt c nfr) _ M2); [|exact GM2].
intros c' i' [Vc Vi]. unfold gc_done_lt. rewrite Fn.
assert (c' = c -> (i' < 2 ^ (14 - c))%Z) by (intros ->; lia). lia.
Qed.
End SE.
#[using="Ht Hfs Happ Hshz Hsp Hok Hwfs HF0 HCL HFR Hcol6 Hshok"] Lemma gcc_classes_run : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "S<'4&By5'S9yR0%211%5241'6y8%611%311p061'@&Kr3r1%3221&QJzr2%3221':&QI&QMr6%211%42<1+:%73@21&Q@vRH&QOvS;+U0%3221vR<&Q6vS6vR1vR;vS3%544321&Q7r4%221Jr5%A7@<>;521&Q4vG%231AI';'9'J&QG&QCvR=r:(S7+[d\0(8%33QH21/01QHr9vS2%:598321+[djH%93QN17/01QN%>5=QA1QE5%A3@51&QB+I%?3R61=%32QF1&S8%12R7Q8%QG3R731+2%E3R<1C%92QL1+T@%QB2QA1%82R>1%QN3R>41&L%12MR2+;%Q=21R5%QK7QJQFQHQEQ?1R9%Q:3Q9QIR:%Q7221%Q8261%Q9291%Q:2A1%Q;2I1qQ:RD1%Q>2RE1qV4RK1%Q@2RL1p0QB1p0QF1p0R91p0RB1p0RG1pT:RL1pQ8RN1pV2S41pUHS;1").
Proof.
induction q as [|q IH]; intros regs M c HI Hc Hq GM FR;
destruct (gcc_class_run regs M c HI ltac:(lia) GM FR) as (r1 & M1 & RUN1 & I1 & KC1 & GM1 & FR1);
pose proof I1 as (H20 & H25 & H7 & H8 & H18 & H9 & H2 & H26 & H22 & H23 & H28).
- eexists. exists M1. split; [|split; [|split; [|split; [|split; [|exact FR1]]]]].
+ eapply msteps_trans; [exact RUN1|].
stepiv (ltac:(oF' 0x5d174%Z)) (ltac:(oD' 0x5d174%Z)) (Z_to_bv 64 11) ltac:(wval).
stepn (ltac:(oF' 0x5d178%Z)) (ltac:(oD' 0x5d178%Z)).
stepb_tk (ltac:(oF' 0x5d17c%Z)) (ltac:(oD' 0x5d17c%Z)) ltac:(cond).
apply mst_refl.
+ gres. exact H25.
+ gres. exact H2.
+ unfold gcl_keeps2. intros r; intros. repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]).
apply KC1; assumption.
+ replace 11%Z with (c + 1)%Z by lia. exact GM1.
- assert (S2 : exists r2, msteps ASEGS (mkst r1 (0x5d174 : word) M1 rom) (mkst r2 (0x5d180 : word) M1 rom)
/\ gcl2_inv r2 (c + 1) /\ gcl_keeps2 r1 r2).
{ eexists. split; [|split].
- stepiv (ltac:(oF' 0x5d174%Z)) (ltac:(oD' 0x5d174%Z)) (Z_to_bv 64 (c + 1)) ltac:(wval).
stepn (ltac:(oF' 0x5d178%Z)) (ltac:(oD' 0x5d178%Z)).
stepb_ft (ltac:(oF' 0x5d17c%Z)) (ltac:(oD' 0x5d17c%Z)) ltac:(cond).
apply mst_refl.
- unfold gcl2_inv. post.
- kp14. }
destruct S2 as (r2 & RUN2 & I2 & KC2).
destruct (IH r2 M1 (c + 1)%Z I2 ltac:(lia) ltac:(lia) GM1 FR1) as (r3 & M3 & RUN3 & J25 & J2 & KC3 & GM3 & FR3).
exists r3, M3. split; [|split; [exact J25 | split; [exact J2 | split; [|split; [exact GM3 | exact FR3]]]]].
+ eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2 | exact RUN3].
+ intros r; intros. rewrite KC3 by assumption. rewrite KC2 by assumption. apply KC1; assumption.
Qed.
End CLASS.
Section WHOLE.
Variable mem0 : word -> option byte.
Variable rom : word -> option byte.
Variables sp ra : word.
Variables t fs sparg tpv key tsd ctx th top botth g40 g35 : Z.
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
Hypothesis Happ : (fs + 4096 + 32768 + 11 * 2 ^ 20 <= 0x7fff7000 \/ 0x10007fff8000 <= fs)%Z.
Hypothesis Hshz : (gc_shz_hi fs <= t - 160 \/ t <= gc_shz_lo fs)%Z.
Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.
Hypothesis Hg : (0 <= g40 < 2 ^ 64)%Z.
Hypothesis HF0 : forall c i, gc_valid c i ->
rdn ASEGS mem0 (Z_to_bv 64 (gc_fl fs c i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z.
Hypothesis HCT : forall M', (forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M' x = mem0 x) ->
rdn ASEGS M' (0x13c2a0 : word) 1%nat = Some [Z_to_bv 8 1] /\
rdn ASEGS M' (0x13c2a4 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\
rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\
rdn ASEGS M' (Z_to_bv 64 (th + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 top)) /\
rdn ASEGS M' (Z_to_bv 64 (th + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 botth)) /\
rdn ASEGS M' (0x134398 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g40)) /\
rdn ASEGS M' (0x10370 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g35)).
Hypothesis HCL : forall M', (forall x : word, gc_outz (t - 160) t fs (bv_unsigned x) -> M' x = mem0 x) ->
rdn ASEGS M' (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20))
/\ rt_layout_globs M'
/\ (forall c i, gc_valid c i -> flag c i <> 0%Z ->
rdn ASEGS M' (Z_to_bv 64 (gc_fr fs c i + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i))) /\ (0 <= rs c i < 2 ^ 64)%Z).
Hypothesis Hcol6 : forall c i, gc_valid c i -> gc_col sparg botth flag rs c i -> (c <= 6)%Z.
Hypothesis Hshok : forall c i, gc_valid c i -> gc_col sparg botth flag rs c i ->
store_ok ASEGS mem0 (Z_to_bv 64 (gc_sh fs c i)) (Z.to_nat (2 ^ (3 + c))) = true.
#[local] Ltac hide_dj := try hide Hfs.
#[using="Hs_def"] Lemma sp_sgc : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "9':'S9yR0%211vS5&S8vS;%2251%83541"). Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
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
#[using="key tsd ctx th top g40 g35 Hs_def Hret Ht Hok Htp Hkey Htsd Hctx Hth Htop Hfs Happ Hshz Hwfs HF0 HCT HCL Hcol6 Hshok"] Theorem gc_collect_run : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "RO&By5'S9yR0%211%5241':&QBr1(S7+:(8%33;21%6251&S8vR<%22=1%;3=41r2+;%;3C19%>231vS6%92D1%B3D31r3+4%B3J1@%E231vS<%@2K1%I3K31r4+2%I3Q11G%L231vS5%O3Q121r5+1%O3Q71M%Q2231vRO%Q53Q721';'6y8%Q=11%311p0Q=1'9'J&QG&QCvR=r8+[dU@%Q@3QF1Q>/01QFvRHvS2%8576321%958Q<DQF2%<3;21%QI2Q>N%QK3QM1M%QK2Q@J%QM3QO1I&QE%12>QC&Q:&QOvS;+U0%3221&Q6vR2vR;vS3%44QI321%:6ER868R11%O2<1%Q02?1%Q12B1%Q22E1qQ>Q41%Q:2Q51qV4RB1%Q<2RC1p0Q>1p0QE1p0QL1p0R41p0R<1pV2RI1").
Proof.
assert (HCo : forall M', (forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M' x = mem0 x) ->
rdn ASEGS M' (0x13c2a0 : word) 1%nat = Some [Z_to_bv 8 1] /\
rdn ASEGS M' (0x13c2a4 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\
rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\
rdn ASEGS M' (Z_to_bv 64 (th + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 top)) /\
rdn ASEGS M' (Z_to_bv 64 (th + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 botth)) /\
rt_layout_globs M' /\
rdn ASEGS M' (0x134398 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g40)) /\
rdn ASEGS M' (0x10370 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g35))).
{ intros M' O. destruct (HCT M' O) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
destruct (HCL M') as (_ & LAY & _); [intros x (O1 & _); apply O; exact O1|].
exact (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj LAY (conj C9 C10)))))))))). }
hide_dj.
intros regs H10 H11 H4 H2 H1. rewrite sp_sgc in H2.
destruct Ht as [Ta Tb]. destruct Hth as [Th1 Th2]. destruct Htop as (Tp1 & Tp2 & Tp3 & Tp4).
unhide Hfs. destruct Hfs as (Fs1 & Fs2 & Fs3). hide Fs3.
assert (Hra : ret_ok (0x5d0f4 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
#[local] Ltac oout := intros x Hx; pose proof (u64_range x);
destruct Hx as [Hx|Hx]; [rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | unorm; lia]
| rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]].
#[local] Ltac sok := apply (store_ok_mono _ _ mem0); [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); first [apply mem_grows_refl | assumption] |];
apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (t - 160)) _ 160%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia].
assert (O13 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> F13 regs x = mem0 x) by (unfold F13; oout).
assert (G13 : mem_grows mem0 (F13 regs)) by (unfold F13; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x5d0b0 : word) mem0 rom) (mkst r1 (0x8325c : word) (F13 regs) rom)
/\ (getr r1 9 = Z_to_bv 64 sparg /\ getr r1 25 = Z_to_bv 64 fs /\ getr r1 4 = Z_to_bv 64 tpv /\ getr r1 2 = Z_to_bv 64 (t - 144)
/\ getr r1 1 = (0x5d0f4 : word) /\ keeps_but [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv regs r1)).
{ unfold F13. eexists. split.
- stepiv (ltac:(oF' 0x5d0b0%Z)) (ltac:(oD' 0x5d0b0%Z)) (Z_to_bv 64 (t - 144)) ltac:(wval).
stepsd (ltac:(oF' 0x5d0b4%Z)) (ltac:(oD' 0x5d0b4%Z)) (Z_to_bv 64 (t - 8)) ra ltac:(sok).
stepsd (ltac:(oF' 0x5d0b8%Z)) (ltac:(oD' 0x5d0b8%Z)) (Z_to_bv 64 (t - 16)) (getr regs 8) ltac:(sok).
stepsd (ltac:(oF' 0x5d0bc%Z)) (ltac:(oD' 0x5d0bc%Z)) (Z_to_bv 64 (t - 24)) (getr regs 9) ltac:(sok).
stepsd (ltac:(oF' 0x5d0c0%Z)) (ltac:(oD' 0x5d0c0%Z)) (Z_to_bv 64 (t - 32)) (getr regs 18) ltac:(sok).
stepsd (ltac:(oF' 0x5d0c4%Z)) (ltac:(oD' 0x5d0c4%Z)) (Z_to_bv 64 (t - 40)) (getr regs 19) ltac:(sok).
stepsd (ltac:(oF' 0x5d0c8%Z)) (ltac:(oD' 0x5d0c8%Z)) (Z_to_bv 64 (t - 48)) (getr regs 20) ltac:(sok).
stepsd (ltac:(oF' 0x5d0cc%Z)) (ltac:(oD' 0x5d0cc%Z)) (Z_to_bv 64 (t - 56)) (getr regs 21) ltac:(sok).
stepsd (ltac:(oF' 0x5d0d0%Z)) (ltac:(oD' 0x5d0d0%Z)) (Z_to_bv 64 (t - 64)) (getr regs 22) ltac:(sok).
stepsd (ltac:(oF' 0x5d0d4%Z)) (ltac:(oD' 0x5d0d4%Z)) (Z_to_bv 64 (t - 72)) (getr regs 23) ltac:(sok).
stepsd (ltac:(oF' 0x5d0d8%Z)) (ltac:(oD' 0x5d0d8%Z)) (Z_to_bv 64 (t - 80)) (getr regs 24) ltac:(sok).
stepsd (ltac:(oF' 0x5d0dc%Z)) (ltac:(oD' 0x5d0dc%Z)) (Z_to_bv 64 (t - 88)) (getr regs 25) ltac:(sok).
stepsd (ltac:(oF' 0x5d0e0%Z)) (ltac:(oD' 0x5d0e0%Z)) (Z_to_bv 64 (t - 96)) (getr regs 26) ltac:(sok).
stepsd (ltac:(oF' 0x5d0e4%Z)) (ltac:(oD' 0x5d0e4%Z)) (Z_to_bv 64 (t - 104)) (getr regs 27) ltac:(sok).
stepiv (ltac:(oF' 0x5d0e8%Z)) (ltac:(oD' 0x5d0e8%Z)) (Z_to_bv 64 sparg) ltac:(wval).
stepiv (ltac:(oF' 0x5d0ec%Z)) (ltac:(oD' 0x5d0ec%Z)) (Z_to_bv 64 fs) ltac:(wval).
stepn (ltac:(oF' 0x5d0f0%Z)) (ltac:(oD' 0x5d0f0%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q9 & Q25 & Q4 & Q2 & Q1 & K1).
destruct (get_current_thread_run r1 (F13 regs) rom (0x5d0f4 : word) (t - 144) tpv key tsd ctx th Q2 Q4 Q1 Hra ltac:(lia) ltac:(lia) Htp Hkey Htsd Hctx ltac:(lia)
ltac:(replace (t - 144 - 16)%Z with (t - 160)%Z by lia; unfold F13; sok)) as (r2 & RUN2 & T10 & T2 & T1 & K2).
{ intros M' HM'. assert (O' : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M' x = mem0 x).
{ intros x Hx. rewrite (HM' x) by lia. apply O13. exact Hx. }
destruct (HCo M' O') as (C1 & C2 & C3 & C4 & C5 & _). repeat split; assumption. }
set (M14 := wbytes (F13 regs) (Z_to_bv 64 (t - 144 - 8)) (word_to_le_bytes 8 (0x5d0f4 : word))) in RUN2.
assert (O14 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M14 x = mem0 x).
{ intros x Hx. rewrite <- (O13 x Hx). unfold M14. revert x Hx. oout. }
assert (G14 : mem_grows mem0 M14) by (unfold M14; eapply mem_grows_trans; [exact G13 | apply wbytes_grows]).
assert (T9 : getr r2 9 = Z_to_bv 64 sparg) by (rewrite (K2 9%bv) by kbt; exact Q9).
assert (T25 : getr r2 25 = Z_to_bv 64 fs) by (rewrite (K2 25%bv) by kbt; exact Q25).
assert (T4 : getr r2 4 = Z_to_bv 64 tpv) by (rewrite (K2 4%bv) by kbt; exact Q4).
destruct (HCo M14 O14) as (_ & _ & _ & _ & _ & D40 & D8 & D16 & (E48 & _ & E50 & _) & _).
set (M15 := wbytes M14 (Z_to_bv 64 (t - 120)) (word_to_le_bytes 8 (Z_to_bv 64 0x13d728))).
set (M16 := wbytes M15 (Z_to_bv 64 (t - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0x13d730))).
set (M17 := wbytes M16 (Z_to_bv 64 (t - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x13d720))).
set (M18 := wbytes M17 (Z_to_bv 64 (t - 144)) (word_to_le_bytes 8 (Z_to_bv 64 g40))).
assert (O15 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M15 x = mem0 x) by (intros x Hx; rewrite <- (O14 x Hx); unfold M15; revert x Hx; oout).
assert (O16 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M16 x = mem0 x) by (intros x Hx; rewrite <- (O15 x Hx); unfold M16; revert x Hx; oout).
assert (O17 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M17 x = mem0 x) by (intros x Hx; rewrite <- (O16 x Hx); unfold M17; revert x Hx; oout).
assert (O18 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M18 x = mem0 x) by (intros x Hx; rewrite <- (O17 x Hx); unfold M18; revert x Hx; oout).
assert (G18 : mem_grows mem0 M18) by (unfold M18, M17, M16, M15; do 4 (eapply mem_grows_trans; [|apply wbytes_grows]); exact G14).
destruct (HCo M15 O15) as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & E58 & _) & _).
destruct (HCo M16 O16) as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & E60 & _) & _).
destruct (HCo M17 O17) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E40 & _).
destruct (HCo M18 O18) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E35).
assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x5d0f4 : word) M14 rom) (mkst r3 (0x5d180 : word) M18 rom)
/\ (gcl2_inv t fs sparg botth g35 r3 0 /\ keeps_but [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv r2 r3)).
{ eexists. split.
- stepb_ft (ltac:(oF' 0x5d0f4%Z)) (ltac:(oD' 0x5d0f4%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x5d0f8%Z)) (ltac:(oD' 0x5d0f8%Z)) (Z_to_bv 64 th) ltac:(wval).
stepn (ltac:(oF' 0x5d0fc%Z)) (ltac:(oD' 0x5d0fc%Z)).
mlbq (ltac:(oF' 0x83420%Z)) (ltac:(oD' 0x83420%Z)) (th + 40)%Z D40.
stepfence (ltac:(oF' 0x83424%Z)) (ltac:(oD' 0x83424%Z)).
stepb_tk (ltac:(oF' 0x83428%Z)) (ltac:(oD' 0x83428%Z)) ltac:(rwH; cbn; cond).
mldq (ltac:(oF' 0x83460%Z)) (ltac:(oD' 0x83460%Z)) (th + 8)%Z D8.
mldq (ltac:(oF' 0x83464%Z)) (ltac:(oD' 0x83464%Z)) (th + 16)%Z D16.
stepov (ltac:(oF' 0x83468%Z)) (ltac:(oD' 0x83468%Z)) (Z_to_bv 64 1) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (botth <? top)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepn (ltac:(oF' 0x8346c%Z)) (ltac:(oD' 0x8346c%Z)).
stepov (ltac:(oF' 0x83470%Z)) (ltac:(oD' 0x83470%Z)) (Z_to_bv 64 top) ltac:(gres; rwH; unfold v_and; imm_norm; unorm; rewrite Z.land_comm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia).
stepret (ltac:(oF' 0x83474%Z)) (ltac:(oD' 0x83474%Z)) (0x5d100 : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
stepiv (ltac:(oF' 0x5d100%Z)) (ltac:(oD' 0x5d100%Z)) (Z_to_bv 64 top) ltac:(wval).
stepiv (ltac:(oF' 0x5d104%Z)) (ltac:(oD' 0x5d104%Z)) (Z_to_bv 64 th) ltac:(wval).
stepn (ltac:(oF' 0x5d108%Z)) (ltac:(oD' 0x5d108%Z)).
mlbq (ltac:(oF' 0x83478%Z)) (ltac:(oD' 0x83478%Z)) (th + 40)%Z D40.
stepfence (ltac:(oF' 0x8347c%Z)) (ltac:(oD' 0x8347c%Z)).
stepb_tk (ltac:(oF' 0x83480%Z)) (ltac:(oD' 0x83480%Z)) ltac:(rwH; cbn; cond).
mldq (ltac:(oF' 0x834b8%Z)) (ltac:(oD' 0x834b8%Z)) (th + 8)%Z D8.
mldq (ltac:(oF' 0x834bc%Z)) (ltac:(oD' 0x834bc%Z)) (th + 16)%Z D16.
stepov (ltac:(oF' 0x834c0%Z)) (ltac:(oD' 0x834c0%Z)) (Z_to_bv 64 1) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (botth <? top)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepn (ltac:(oF' 0x834c4%Z)) (ltac:(oD' 0x834c4%Z)).
stepov (ltac:(oF' 0x834c8%Z)) (ltac:(oD' 0x834c8%Z)) (Z_to_bv 64 botth) ltac:(gres; rwH; unfold v_and; imm_norm; unorm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_comm; rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia).
stepret (ltac:(oF' 0x834cc%Z)) (ltac:(oD' 0x834cc%Z)) (0x5d10c : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
stepb_ft (ltac:(oF' 0x5d10c%Z)) (ltac:(oD' 0x5d10c%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x5d110%Z)) (ltac:(oD' 0x5d110%Z)) (Z_to_bv 64 botth) ltac:(wval).
stepb_ft (ltac:(oF' 0x5d114%Z)) (ltac:(oD' 0x5d114%Z)) ltac:(cond).
stepn (ltac:(oF' 0x5d118%Z)) (ltac:(oD' 0x5d118%Z)).
stepn (ltac:(oF' 0x5d11c%Z)) (ltac:(oD' 0x5d11c%Z)).
stepn (ltac:(oF' 0x5d120%Z)) (ltac:(oD' 0x5d120%Z)).
stepn (ltac:(oF' 0x5d124%Z)) (ltac:(oD' 0x5d124%Z)).
stepn (ltac:(oF' 0x5d128%Z)) (ltac:(oD' 0x5d128%Z)).
stepn (ltac:(oF' 0x5d12c%Z)) (ltac:(oD' 0x5d12c%Z)).
stepn (ltac:(oF' 0x5d130%Z)) (ltac:(oD' 0x5d130%Z)).
stepn (ltac:(oF' 0x5d134%Z)) (ltac:(oD' 0x5d134%Z)).
stepiv (ltac:(oF' 0x5d138%Z)) (ltac:(oD' 0x5d138%Z)) (Z_to_bv 64 (fs + 4096)) ltac:(wval).
mld (ltac:(oF' 0x5d13c%Z)) (ltac:(oD' 0x5d13c%Z)) (0x1343a0 : word) E48.
mld (ltac:(oF' 0x5d140%Z)) (ltac:(oD' 0x5d140%Z)) (0x1343a8 : word) E50.
stepsdq (ltac:(oF' 0x5d144%Z)) (ltac:(oD' 0x5d144%Z)) (Z_to_bv 64 (t - 120)) (Z_to_bv 64 0x13d728) ltac:(unfold M14, F13; sok).
change (wbytes M14 (Z_to_bv 64 (t - 120)) (word_to_le_bytes 8 (Z_to_bv 64 0x13d728))) with M15.
mld (ltac:(oF' 0x5d148%Z)) (ltac:(oD' 0x5d148%Z)) (0x1343b0 : word) E58.
stepsdq (ltac:(oF' 0x5d14c%Z)) (ltac:(oD' 0x5d14c%Z)) (Z_to_bv 64 (t - 128)) (Z_to_bv 64 0x13d730) ltac:(unfold M15, M14, F13; sok).
change (wbytes M15 (Z_to_bv 64 (t - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0x13d730))) with M16.
mld (ltac:(oF' 0x5d150%Z)) (ltac:(oD' 0x5d150%Z)) (0x1343b8 : word) E60.
stepsdq (ltac:(oF' 0x5d154%Z)) (ltac:(oD' 0x5d154%Z)) (Z_to_bv 64 (t - 136)) (Z_to_bv 64 0x13d720) ltac:(unfold M16, M15, M14, F13; sok).
change (wbytes M16 (Z_to_bv 64 (t - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x13d720))) with M17.
mld (ltac:(oF' 0x5d158%Z)) (ltac:(oD' 0x5d158%Z)) (0x134398 : word) E40.
stepsdq (ltac:(oF' 0x5d15c%Z)) (ltac:(oD' 0x5d15c%Z)) (Z_to_bv 64 (t - 144)) (Z_to_bv 64 g40) ltac:(unfold M17, M16, M15, M14, F13; sok).
change (wbytes M17 (Z_to_bv 64 (t - 144)) (word_to_le_bytes 8 (Z_to_bv 64 g40))) with M18.
mld (ltac:(oF' 0x5d160%Z)) (ltac:(oD' 0x5d160%Z)) (0x10370 : word) E35.
stepn (ltac:(oF' 0x5d164%Z)) (ltac:(oD' 0x5d164%Z)).
stepn (ltac:(oF' 0x5d168%Z)) (ltac:(oD' 0x5d168%Z)).
stepn (ltac:(oF' 0x5d16c%Z)) (ltac:(oD' 0x5d16c%Z)).
stepn (ltac:(oF' 0x5d170%Z)) (ltac:(oD' 0x5d170%Z)).
apply mst_refl.
- split; [unfold gcl2_inv; post | solve_keeps_but]. }
destruct S3 as (r3 & RUN3 & I3 & K3).
assert (HFR' : rdn ASEGS M18 (Z_to_bv 64 (t - 120)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13d728))
/\ rdn ASEGS M18 (Z_to_bv 64 (t - 128)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13d730))
/\ rdn ASEGS M18 (Z_to_bv 64 (t - 136)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13d720))).
{ unfold M18, M17, M16, M15. repeat split;
repeat (rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ]);
apply rdn_wbytes_hit8; unorm; lia. }
unhide Fs3.
pose proof (gc_kit t fs (conj Fs1 (conj Fs2 Fs3)) Happ) as (KK1 & KK2 & KK3 & KK4).
assert (GM18 : gcm mem0 (t - 160) t fs (gc_col sparg botth flag rs) (gc_done_lt 0 0) M18).
{ apply (gcm_equiv mem0 (t - 160) t fs _ (fun _ _ => False)); [|apply gcm_init; [exact G18 | exact O18]].
intros c i [Vc Vi]. unfold gc_done_lt. lia. }
assert (FR18 : frm M18 t M18) by (intros x _ _; reflexivity).
assert (Hsp' : (0 <= sparg < 2 ^ 64)%Z /\ (0 <= botth < 2 ^ 64)%Z) by lia.
destruct (gcc_classes_run mem0 M18 rom t fs sparg botth g35 flag rs (conj Ta Tb) (conj Fs1 (conj Fs2 Fs3)) Happ Hshz Hsp' Hok Hwfs HF0 HCL HFR' Hcol6 Hshok
10%nat r3 M18 0%Z I3 ltac:(lia) eq_refl GM18 FR18) as (r4 & M4 & RUN4 & J25 & J2 & K4 & GM4 & FR4).
hide Fs3.
assert (Hwf96 : store_ok ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = true).
{ apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 fs) _ (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20))); [unorm; lia | exact Hwfs | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia]. }
assert (G4' : mem_grows mem0 M4) by (destruct GM4 as (X & _); exact X).
set (M5 := wbytes M4 (Z_to_bv 64 (fs + 96)) [Z_to_bv 8 0]).
assert (SL : forall k v, (k = 8 /\ v = ra \/ k = 16 /\ v = getr regs 8 \/ k = 24 /\ v = getr regs 9 \/ k = 32 /\ v = getr regs 18 \/ k = 40 /\ v = getr regs 19 \/ k = 48 /\ v = getr regs 20 \/ k = 56 /\ v = getr regs 21 \/ k = 64 /\ v = getr regs 22 \/ k = 72 /\ v = getr regs 23 \/ k = 80 /\ v = getr regs 24 \/ k = 88 /\ v = getr regs 25 \/ k = 96 /\ v = getr regs 26 \/ k = 104 /\ v = getr regs 27)%Z ->
rdn ASEGS M5 (Z_to_bv 64 (t - k)) 8%nat = Some (word_to_le_bytes 8 v)).
{ intros k v Hk. assert (Hk' : (8 <= k <= 104)%Z) by lia.
rewrite (rdn_ext ASEGS 8 M5 (F13 regs)); [| unorm; cbn; lia |].
- unfold F13. destruct Hk as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]]]]]]];
repeat (rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; (clear - t; lia) | cbn [Z.of_nat Pos.to_nat]; unorm; (clear - Ht t; lia) | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; (clear - Ht t; lia) ]);
apply rdn_wbytes_hit8; unorm; (clear - Ht t; lia).
- intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. pose proof (u64_range x).
unfold M5. rewrite wbytes_out_any_gc; [| cbn [length Z.of_nat Pos.to_nat]; unorm; lia | cbn [length Z.of_nat Pos.to_nat]; unorm; lia].
rewrite (FR4 x) by lia.
unfold M18, M17, M16, M15, M14. rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]. }
#[local] Ltac slv := first [split; reflexivity | left; split; reflexivity | right; slv].
eexists. exists M5. split.
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
chain_step; [reflexivity | eapply (step_sb_at ASEGS) with (a := Z_to_bv 64 (fs + 96)) (b := Z_to_bv 8 0);
[exact (ltac:(oF' 0x5d358%Z)) | reflexivity | exact (ltac:(oD' 0x5d358%Z)) | wval | gres; reflexivity | apply bv_eq; vm_compute; reflexivity
| apply (store_ok_mono _ _ mem0 M4 _ G4'); exact Hwf96 ] | step_simpl; vnorm].
change (wbytes M4 (Z_to_bv 64 (fs + 96)) [Z_to_bv 8 0]) with M5.
stepld (ltac:(oF' 0x5d35c%Z)) (ltac:(oD' 0x5d35c%Z)) (ra) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 8)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d360%Z)) (ltac:(oD' 0x5d360%Z)) (getr regs 8) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 16)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d364%Z)) (ltac:(oD' 0x5d364%Z)) (getr regs 9) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 24)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d368%Z)) (ltac:(oD' 0x5d368%Z)) (getr regs 18) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 32)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d36c%Z)) (ltac:(oD' 0x5d36c%Z)) (getr regs 19) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 40)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d370%Z)) (ltac:(oD' 0x5d370%Z)) (getr regs 20) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 48)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d374%Z)) (ltac:(oD' 0x5d374%Z)) (getr regs 21) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 56)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d378%Z)) (ltac:(oD' 0x5d378%Z)) (getr regs 22) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 64)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d37c%Z)) (ltac:(oD' 0x5d37c%Z)) (getr regs 23) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 72)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d380%Z)) (ltac:(oD' 0x5d380%Z)) (getr regs 24) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 80)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d384%Z)) (ltac:(oD' 0x5d384%Z)) (getr regs 25) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 88)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d388%Z)) (ltac:(oD' 0x5d388%Z)) (getr regs 26) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 96)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d38c%Z)) (ltac:(oD' 0x5d38c%Z)) (getr regs 27) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 104)) by (symmetry; wval) end; apply SL; slv).
stepiv (ltac:(oF' 0x5d390%Z)) (ltac:(oD' 0x5d390%Z)) (Z_to_bv 64 t) ltac:(wval).
stepret (ltac:(oF' 0x5d394%Z)) (ltac:(oD' 0x5d394%Z)) ra ltac:(rwH; reflexivity).
apply mst_refl.
- split; [gres; symmetry; apply sp_sgc|]. split; [gres; reflexivity|]. split.
{ intros r Hcs. cbv in Hcs.
destruct Hcs as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]; gres;
first [ reflexivity | rewrite H1; reflexivity | rewrite H2; reflexivity
| rewrite (K4 _) by (intros E; discriminate E); rewrite (K3 _) by kbt;
rewrite (K2 _) by kbt; rewrite (K1 _) by kbt; reflexivity ]. }
destruct GM4 as (G4 & O4 & P4).
assert (OUT5 : forall x : word, bv_unsigned x <> (fs + 96)%Z -> M5 x = M4 x).
{ intros x Hx. unfold M5. apply wbytes_outside; cbn [length Z.of_nat Pos.to_nat]; rewrite u64_lit by lia; lia. }
assert (DALL : forall c i, gc_valid c i -> gc_done_lt 11 0 c i) by (intros c i [Vc _]; unfold gc_done_lt; lia).
split; [eapply mem_grows_trans; [exact G4 | apply wbytes_grows]|]. split; [|split].
+ intros x Hx N96 Hn. rewrite OUT5 by exact N96. apply O4; [exact Hx|]. intros c i V _ C. apply Hn; assumption.
+ intros c i V C. pose proof (P4 c i V (DALL c i V) C) as QQ1. pose proof (gc_fl_range fs c i V) as FLR.
rewrite OUT5 by (rewrite u64_lit by lia; lia). exact QQ1.
+ unfold M5. apply (rdn_wbytes_hit ASEGS [Z_to_bv 8 0]). cbn [length Z.of_nat Pos.to_nat]. rewrite u64_lit by lia. lia.
Qed.
End WHOLE.
Section EARLY.
Variable mem0 : word -> option byte.
Variable rom : word -> option byte.
Variables sp ra : word.
Variables t fs sparg tpv key tsd ctx th top botth : Z.
Hypothesis Hs_def : bv_unsigned sp = t.
Hypothesis Hret : ret_ok ra.
Hypothesis Ht : (0x1000000 <= t - 160)%Z /\ (t < 2 ^ 64)%Z.
Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (t - 160)) 160%nat = true.
Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
Hypothesis Hth : (0 < th /\ th + 80 <= 2 ^ 64)%Z.
Hypothesis Htop : (botth < top)%Z /\ (0 <= botth)%Z /\ (top < 2 ^ 64)%Z /\ (top < sparg)%Z /\ (sparg < 2 ^ 64)%Z.
Hypothesis Hfsb : (0 <= fs < 2 ^ 64)%Z.
Hypothesis HCE : forall M', (forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M' x = mem0 x) ->
rdn ASEGS M' (0x13c2a0 : word) 1%nat = Some [Z_to_bv 8 1] /\
rdn ASEGS M' (0x13c2a4 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\
rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\
rdn ASEGS M' (Z_to_bv 64 (th + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 top)) /\
rdn ASEGS M' (Z_to_bv 64 (th + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 botth)).
#[using="Hs_def"] Lemma sp_sge : ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "9':'S9yR0%211vS5&S8vS;%2251%83541"). Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Definition F13e (rg : bvmap 5 word) : word -> option byte :=
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
Section SE.
Local Abbreviation SEC_T_gc_early_run := (ltac2:(TCodec.tc2 tcn__Jb0FakeStackGCC "S8&By5'S9yR0%211%5241':&QBr1(S7+:(8%33;21%6251&S8vR<%22=1%;3=41r2+;%;3C19%>231vS6%92D1%B3D31r3+4%B3J1@%E231vS<%@2K1%I3K31r4+2%I3Q11G%L231vS5%O3Q121r5+1%O3Q71M%Q2231vRO%Q53Q721';'6y8%Q=11%311p0Q=1'9'J&QG&QCvR=r8+[dU@%Q@3QF1Q>/01QFvRHvS2%8576321%958Q<DQF2%<3;21%QI2Q>N%QK3QM1M%QK2Q@J%QM3QO1I&QE%12>QC'>&QK&S:%12R6R1&QOvS;+U0%3221%7251&QJ%1257%;231%QI1R0%H1R1%R>3Q421p041pVNRB1&QF%12MR@%Q7231%Q82E1%Q92H1%Q:2K1%Q;2N1qQBQ=1%QC2Q>1qV4RK1%QE2RL1p0QG1p0QN1p0R51p0R=1p0RE1pV2S21")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_gc_early_run) 0%nat 0%nat).
Theorem gc_early_run : ltac:(sec_stmt2 constr:(SEC_T_gc_early_run) 1%nat 0%nat).
Proof using key tsd ctx th top botth Hs_def Hret Ht Hok Htp Hkey Htsd Hctx Hth Htop Hfsb HCE regs.
intros H10 H11 H4 H2 H1.
rewrite sp_sge in H2.
destruct Ht as [Ta Tb]. destruct Hth as [Th1 Th2]. destruct Htop as (Tp1 & Tp2 & Tp3 & Tp4 & Tp5).
assert (Hra : ret_ok (0x5d0f4 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
#[local] Ltac oout := intros x Hx; pose proof (u64_range x);
destruct Hx as [Hx|Hx]; [rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | unorm; lia]
| rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]].
#[local] Ltac sok := apply (store_ok_mono _ _ mem0); [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); first [apply mem_grows_refl | assumption] |];
apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (t - 160)) _ 160%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia].
assert (O13 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> F13e regs x = mem0 x) by (unfold F13e; oout).
assert (G13 : mem_grows mem0 (F13e regs)) by (unfold F13e; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x5d0b0 : word) mem0 rom) (mkst r1 (0x8325c : word) (F13e regs) rom)
/\ (getr r1 9 = Z_to_bv 64 sparg /\ getr r1 25 = Z_to_bv 64 fs /\ getr r1 4 = Z_to_bv 64 tpv /\ getr r1 2 = Z_to_bv 64 (t - 144)
/\ getr r1 1 = (0x5d0f4 : word) /\ keeps_but [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv regs r1)).
{ unfold F13e. eexists. split.
- stepiv (ltac:(oF' 0x5d0b0%Z)) (ltac:(oD' 0x5d0b0%Z)) (Z_to_bv 64 (t - 144)) ltac:(wval).
stepsd (ltac:(oF' 0x5d0b4%Z)) (ltac:(oD' 0x5d0b4%Z)) (Z_to_bv 64 (t - 8)) ra ltac:(sok).
stepsd (ltac:(oF' 0x5d0b8%Z)) (ltac:(oD' 0x5d0b8%Z)) (Z_to_bv 64 (t - 16)) (getr regs 8) ltac:(sok).
stepsd (ltac:(oF' 0x5d0bc%Z)) (ltac:(oD' 0x5d0bc%Z)) (Z_to_bv 64 (t - 24)) (getr regs 9) ltac:(sok).
stepsd (ltac:(oF' 0x5d0c0%Z)) (ltac:(oD' 0x5d0c0%Z)) (Z_to_bv 64 (t - 32)) (getr regs 18) ltac:(sok).
stepsd (ltac:(oF' 0x5d0c4%Z)) (ltac:(oD' 0x5d0c4%Z)) (Z_to_bv 64 (t - 40)) (getr regs 19) ltac:(sok).
stepsd (ltac:(oF' 0x5d0c8%Z)) (ltac:(oD' 0x5d0c8%Z)) (Z_to_bv 64 (t - 48)) (getr regs 20) ltac:(sok).
stepsd (ltac:(oF' 0x5d0cc%Z)) (ltac:(oD' 0x5d0cc%Z)) (Z_to_bv 64 (t - 56)) (getr regs 21) ltac:(sok).
stepsd (ltac:(oF' 0x5d0d0%Z)) (ltac:(oD' 0x5d0d0%Z)) (Z_to_bv 64 (t - 64)) (getr regs 22) ltac:(sok).
stepsd (ltac:(oF' 0x5d0d4%Z)) (ltac:(oD' 0x5d0d4%Z)) (Z_to_bv 64 (t - 72)) (getr regs 23) ltac:(sok).
stepsd (ltac:(oF' 0x5d0d8%Z)) (ltac:(oD' 0x5d0d8%Z)) (Z_to_bv 64 (t - 80)) (getr regs 24) ltac:(sok).
stepsd (ltac:(oF' 0x5d0dc%Z)) (ltac:(oD' 0x5d0dc%Z)) (Z_to_bv 64 (t - 88)) (getr regs 25) ltac:(sok).
stepsd (ltac:(oF' 0x5d0e0%Z)) (ltac:(oD' 0x5d0e0%Z)) (Z_to_bv 64 (t - 96)) (getr regs 26) ltac:(sok).
stepsd (ltac:(oF' 0x5d0e4%Z)) (ltac:(oD' 0x5d0e4%Z)) (Z_to_bv 64 (t - 104)) (getr regs 27) ltac:(sok).
stepiv (ltac:(oF' 0x5d0e8%Z)) (ltac:(oD' 0x5d0e8%Z)) (Z_to_bv 64 sparg) ltac:(wval).
stepiv (ltac:(oF' 0x5d0ec%Z)) (ltac:(oD' 0x5d0ec%Z)) (Z_to_bv 64 fs) ltac:(wval).
stepn (ltac:(oF' 0x5d0f0%Z)) (ltac:(oD' 0x5d0f0%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q9 & Q25 & Q4 & Q2 & Q1 & K1).
destruct (get_current_thread_run r1 (F13e regs) rom (0x5d0f4 : word) (t - 144) tpv key tsd ctx th Q2 Q4 Q1 Hra ltac:(lia) ltac:(lia) Htp Hkey Htsd Hctx ltac:(lia)
ltac:(replace (t - 144 - 16)%Z with (t - 160)%Z by lia; unfold F13e; sok)) as (r2 & RUN2 & T10 & T2 & T1 & K2).
{ intros M' HM'. assert (O' : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M' x = mem0 x).
{ intros x Hx. rewrite (HM' x) by lia. apply O13. exact Hx. }
destruct (HCE M' O') as (C1 & C2 & C3 & C4 & C5 & _). repeat split; assumption. }
set (M14 := wbytes (F13e regs) (Z_to_bv 64 (t - 144 - 8)) (word_to_le_bytes 8 (0x5d0f4 : word))) in RUN2.
assert (O14 : forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M14 x = mem0 x).
{ intros x Hx. rewrite <- (O13 x Hx). unfold M14. revert x Hx. oout. }
assert (G14 : mem_grows mem0 M14) by (unfold M14; eapply mem_grows_trans; [exact G13 | apply wbytes_grows]).
assert (T9 : getr r2 9 = Z_to_bv 64 sparg) by (rewrite (K2 9%bv) by kbt; exact Q9).
assert (T25 : getr r2 25 = Z_to_bv 64 fs) by (rewrite (K2 25%bv) by kbt; exact Q25).
assert (T4 : getr r2 4 = Z_to_bv 64 tpv) by (rewrite (K2 4%bv) by kbt; exact Q4).
destruct (HCE M14 O14) as (_ & _ & _ & _ & _ & D40 & D8 & D16).
assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x5d0f4 : word) M14 rom) (mkst r3 (0x5d35c : word) M14 rom)
/\ (getr r3 2 = Z_to_bv 64 (t - 144) /\ keeps_but [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv r2 r3)).
{ eexists. split.
- stepb_ft (ltac:(oF' 0x5d0f4%Z)) (ltac:(oD' 0x5d0f4%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x5d0f8%Z)) (ltac:(oD' 0x5d0f8%Z)) (Z_to_bv 64 th) ltac:(wval).
stepn (ltac:(oF' 0x5d0fc%Z)) (ltac:(oD' 0x5d0fc%Z)).
mlbq (ltac:(oF' 0x83420%Z)) (ltac:(oD' 0x83420%Z)) (th + 40)%Z D40.
stepfence (ltac:(oF' 0x83424%Z)) (ltac:(oD' 0x83424%Z)).
stepb_tk (ltac:(oF' 0x83428%Z)) (ltac:(oD' 0x83428%Z)) ltac:(rwH; cbn; cond).
mldq (ltac:(oF' 0x83460%Z)) (ltac:(oD' 0x83460%Z)) (th + 8)%Z D8.
mldq (ltac:(oF' 0x83464%Z)) (ltac:(oD' 0x83464%Z)) (th + 16)%Z D16.
stepov (ltac:(oF' 0x83468%Z)) (ltac:(oD' 0x83468%Z)) (Z_to_bv 64 1) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (botth <? top)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepn (ltac:(oF' 0x8346c%Z)) (ltac:(oD' 0x8346c%Z)).
stepov (ltac:(oF' 0x83470%Z)) (ltac:(oD' 0x83470%Z)) (Z_to_bv 64 top) ltac:(gres; rwH; unfold v_and; imm_norm; unorm; rewrite Z.land_comm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia).
stepret (ltac:(oF' 0x83474%Z)) (ltac:(oD' 0x83474%Z)) (0x5d100 : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
stepiv (ltac:(oF' 0x5d100%Z)) (ltac:(oD' 0x5d100%Z)) (Z_to_bv 64 top) ltac:(wval).
stepiv (ltac:(oF' 0x5d104%Z)) (ltac:(oD' 0x5d104%Z)) (Z_to_bv 64 th) ltac:(wval).
stepn (ltac:(oF' 0x5d108%Z)) (ltac:(oD' 0x5d108%Z)).
mlbq (ltac:(oF' 0x83478%Z)) (ltac:(oD' 0x83478%Z)) (th + 40)%Z D40.
stepfence (ltac:(oF' 0x8347c%Z)) (ltac:(oD' 0x8347c%Z)).
stepb_tk (ltac:(oF' 0x83480%Z)) (ltac:(oD' 0x83480%Z)) ltac:(rwH; cbn; cond).
mldq (ltac:(oF' 0x834b8%Z)) (ltac:(oD' 0x834b8%Z)) (th + 8)%Z D8.
mldq (ltac:(oF' 0x834bc%Z)) (ltac:(oD' 0x834bc%Z)) (th + 16)%Z D16.
stepov (ltac:(oF' 0x834c0%Z)) (ltac:(oD' 0x834c0%Z)) (Z_to_bv 64 1) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (botth <? top)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
stepn (ltac:(oF' 0x834c4%Z)) (ltac:(oD' 0x834c4%Z)).
stepov (ltac:(oF' 0x834c8%Z)) (ltac:(oD' 0x834c8%Z)) (Z_to_bv 64 botth) ltac:(gres; rwH; unfold v_and; imm_norm; unorm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_comm; rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia).
stepret (ltac:(oF' 0x834cc%Z)) (ltac:(oD' 0x834cc%Z)) (0x5d10c : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
stepb_tk (ltac:(oF' 0x5d10c%Z)) (ltac:(oD' 0x5d10c%Z)) ltac:(cond).
apply mst_refl.
- split; [gres; rwH; reflexivity | solve_keeps_but]. }
destruct S3 as (r3 & RUN3 & J2 & K3).
assert (SL : forall k v, (k = 8 /\ v = ra \/ k = 16 /\ v = getr regs 8 \/ k = 24 /\ v = getr regs 9 \/ k = 32 /\ v = getr regs 18 \/ k = 40 /\ v = getr regs 19 \/ k = 48 /\ v = getr regs 20 \/ k = 56 /\ v = getr regs 21 \/ k = 64 /\ v = getr regs 22 \/ k = 72 /\ v = getr regs 23 \/ k = 80 /\ v = getr regs 24 \/ k = 88 /\ v = getr regs 25 \/ k = 96 /\ v = getr regs 26 \/ k = 104 /\ v = getr regs 27)%Z ->
rdn ASEGS M14 (Z_to_bv 64 (t - k)) 8%nat = Some (word_to_le_bytes 8 v)).
{ intros k v Hk. assert (Hk' : (8 <= k <= 104)%Z) by lia.
unfold M14, F13e. destruct Hk as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]]]]]]];
repeat (rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; (clear - t; lia) | cbn [Z.of_nat Pos.to_nat]; unorm; (clear - Ht t; lia) | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; (clear - Ht t; lia) ]);
apply rdn_wbytes_hit8; unorm; (clear - Ht t; lia). }
#[local] Ltac slv := first [split; reflexivity | left; split; reflexivity | right; slv].
eexists. exists M14. split.
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
stepld (ltac:(oF' 0x5d35c%Z)) (ltac:(oD' 0x5d35c%Z)) (ra) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 8)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d360%Z)) (ltac:(oD' 0x5d360%Z)) (getr regs 8) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 16)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d364%Z)) (ltac:(oD' 0x5d364%Z)) (getr regs 9) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 24)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d368%Z)) (ltac:(oD' 0x5d368%Z)) (getr regs 18) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 32)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d36c%Z)) (ltac:(oD' 0x5d36c%Z)) (getr regs 19) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 40)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d370%Z)) (ltac:(oD' 0x5d370%Z)) (getr regs 20) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 48)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d374%Z)) (ltac:(oD' 0x5d374%Z)) (getr regs 21) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 56)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d378%Z)) (ltac:(oD' 0x5d378%Z)) (getr regs 22) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 64)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d37c%Z)) (ltac:(oD' 0x5d37c%Z)) (getr regs 23) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 72)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d380%Z)) (ltac:(oD' 0x5d380%Z)) (getr regs 24) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 80)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d384%Z)) (ltac:(oD' 0x5d384%Z)) (getr regs 25) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 88)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d388%Z)) (ltac:(oD' 0x5d388%Z)) (getr regs 26) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 96)) by (symmetry; wval) end; apply SL; slv).
stepld (ltac:(oF' 0x5d38c%Z)) (ltac:(oD' 0x5d38c%Z)) (getr regs 27) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 104)) by (symmetry; wval) end; apply SL; slv).
stepiv (ltac:(oF' 0x5d390%Z)) (ltac:(oD' 0x5d390%Z)) (Z_to_bv 64 t) ltac:(wval).
stepret (ltac:(oF' 0x5d394%Z)) (ltac:(oD' 0x5d394%Z)) ra ltac:(rwH; reflexivity).
apply mst_refl.
- split; [gres; symmetry; apply sp_sge|]. split; [gres; reflexivity|]. split; [|split; [exact O14 | exact G14]].
intros r Hcs. cbv in Hcs.
destruct Hcs as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]; gres;
first [ reflexivity | rewrite H1; reflexivity | rewrite H2; reflexivity
| rewrite (K3 _) by kbt; rewrite (K2 _) by kbt; rewrite (K1 _) by kbt; reflexivity ].
Qed.
End SE.
End EARLY.
End FPX_1.
