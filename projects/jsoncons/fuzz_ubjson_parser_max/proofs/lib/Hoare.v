(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Hoare () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare.WithFP1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0C"; "0C'"; "0C1"; "0C2"; "1O"; "1S"; "1Some"; "1length"; "1list"; "1nat"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"]; ["2or"; "3Z"; "0I"; "4Segment"; "5MachineOk"; "5machine_result"; "5machine_state"; "5step"; "6bvmap"; "0P"; "0P'"; "0Q"; "0Q'"; "0R"; "0R1"; "0R2"]; ["7wbytes"; "8msteps"; "8to_wexit"; "9assn"; "9at_"; "9frameable"; "9mem_agree"; "9memset"; "9proc"; "9ra_indep"; "9regs_agree"; "9regset"; "9ret_ok"; "9triple"; ":btgt"; ":getr"]; [":mkst"; ":rdn"; ":regupd"; ":v_addi"; ";add"; ";land"; ";le"; ";lt"; ";modulo"; ";of_nat"; "0W"; "0W'"; "0W1"; "0W2"; "0a"; "0b"]; ["0base"; "0bs"; "0bufs"; "0c"; "0callsite"; "0code"; "0d"; "0e"; "0entry"; "0fx"; "0hd"; "0i"; "0k"; "0m"; "0m'"; "0m1"]; ["0m2"; "0m3"; "0mem"; "0mem'"; "0n"; "0out"; "0r"; "0regs"; "0regs'"; "0regs1"; "0regs2"; "0regs3"; "0ret"; "0rom"; "0segs"; "<BV"]; ["<Z_to_bv"; "<bv"; "<bv_add"; "<bv_unsigned"; "0v"; "0x"; "0x0"; "0x1"; "0z"]]).
Section WithFP1.
Context {fx : FPState}.
Definition at_ (base : word) (d : Z) : word := Z_to_bv 64 (bv_unsigned base + d).
Lemma at_0 : ltac2:(TCodec.tc2 tcn__Hoare ":'S1yR0%211'=&Q4r1z%3221%53613pT271").
Proof.
intros base. unfold at_. rewrite Z.add_0_r. apply bv_eq.
rewrite Z_to_bv_unsigned. apply bv_wrap_small, bv_unsigned_in_range.
Qed.
Lemma at_addi : ltac2:(TCodec.tc2 tcn__Hoare "C'S1yR0%211'A'=&QC&Q4r3r2%3221r1%6221&QD%1253%8271%;3=41pT@=1pT>>1pT2@1").
Proof.
intros base d e. unfold at_, v_addi. apply bv_eq.
rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma at_btgt : ltac2:(TCodec.tc2 tcn__Hoare "C'S1yR0%211'A'=&Q>&Q4r3r2%3221r1%6221&QD%1253%8271%;3=41pT@=1pT>>1pT2@1").
Proof. intros. unfold btgt. apply at_addi. Qed.
Lemma at_lit : ltac2:(TCodec.tc2 tcn__Hoare "G'S1yR0%211'A'=&S0&QD&S3r3%2281r2%5221%72;1r1%:3<21&Q4r4%2219%>3@18p051pSNB1pT>B1pT2D1").
Proof. intros. assumption. Qed.
Lemma at_at : ltac2:(TCodec.tc2 tcn__Hoare "B'S1yR0%211'A'=&Q4r3r2%3221r1%5221&QD%1253%8271%:3<41pT@<1pT>=1pT2?1").
Proof. exact at_addi. Qed.
Lemma u_succ_shift : ltac2:(TCodec.tc2 tcn__Hoare "J'S1yR0%211'A'=&S0&QD&S3&S2r2(RO+1(;%33<21%63=51%82>1r1%;221%=2A1%<2B:%>294%?221%A2E1%C3E51pTHE1pSNG1").
Proof.
intros a i. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma at_self : ltac2:(TCodec.tc2 tcn__Hoare ">'S1yR0%211'=&S0&QD&S3r1%2271z%5221%72:1%93:15pSN;1").
Proof. intros a. exact (at_0 a). Qed.
Definition assn := bvmap 5 word -> (word -> option byte) -> (word -> option byte) -> Prop.
Definition regset := reg -> Prop.
Definition memset := word -> Prop.
Definition regs_agree (C : regset) (regs regs' : bvmap 5 word) : Prop :=
forall r, ~ C r -> getr regs' r = getr regs r.
Definition mem_agree (W : memset) (m m' : word -> option byte) : Prop :=
forall x, ~ W x -> m' x = m x.
Lemma regs_agree_refl : ltac2:(TCodec.tc2 tcn__Hoare "=&Q;&Hy5'S1yR0%211%5241&Q:r2r1%33211pU@51p2<1").
Proof. intros C regs r _. reflexivity. Qed.
Lemma mem_agree_refl : ltac2:(TCodec.tc2 tcn__Hoare "?&Q7'S1yR0%211':y8%511%311p051&Q6r2r1%33211pTL51pSF>1").
Proof. intros W m x _. reflexivity. Qed.
Lemma regs_agree_trans : ltac2:(TCodec.tc2 tcn__Hoare "F&Q;&Hy5'S1yR0%211%5241&Q:r4r3r2%43321r5%63143r6%83136p031p061pUH<1pUF=1pUD>1p2E1").
Proof. intros C r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.
Lemma mem_agree_trans : ltac2:(TCodec.tc2 tcn__Hoare "H&Q7'S1yR0%211':y8%511%311p051&Q6r4r3r2%43321r5%63143r6%83136p031p061pU4<1pU2=1pU0>1pSFG1").
Proof. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). apply H1, Hx. Qed.
Lemma regs_agree_mono : ltac2:(TCodec.tc2 tcn__Hoare "J&Q;&Hy5'S1yR0%211%5241%415r5r1%211r2%411p031pU>71&Q:r3%23916r4%43;13p031p071pUB@1pU@A1p4H1p2I1").
Proof. intros C C' regs regs' Hsub H r Hr. apply H. intro; apply Hr, Hsub; assumption. Qed.
Lemma mem_agree_mono : ltac2:(TCodec.tc2 tcn__Hoare "K&Q7'S1yR0%211':y8%511%311p051r5r1%211r2%411p031pV<<1&Q6r3%23916r4%43;13p031p071pTN?1pTL@1pSHI1pSFJ1").
Proof. intros W W' m m' Hsub H x Hx. apply H. intro; apply Hx, Hsub; assumption. Qed.
Lemma regs_agree_upd : ltac2:(TCodec.tc2 tcn__Hoare "K&Q;&Hy5'S1yR0%211%5241%415r5r2%211&Q:r6r4%33261r7&QBr3%23:51%83471p061p0;1pV:A1pU>@1pUBB1pU@C1p2J1").
Proof.
intros C regs regs' r v Hin H s Hs.
rewrite getr_other by (intro Heq; subst; contradiction).
apply H, Hs.
Qed.
Lemma mem_agree_wbytes : ltac2:(TCodec.tc2 tcn__Hoare "QC&Q7'S1yR0%211':y8%511%311p051'8%114'A'<&QFzr1%3221&QG&QI&7r2%22?1%411%6281%<281r7&S0&QD&S3r4%22L1%421;%62N1%811p0:1pTHH1&Q6r6r5%3321:&Q0r3%234=1%73B61p051p0:1pT4Q41pSNQ<1pTNQ81pTLQ91pSFQB1").
Proof.
intros W m m' a bs. revert m' a.
induction bs as [|b bs IH]; intros m' a Hin H; cbn [wbytes] in *; [exact H|].
assert (Ha : W a).
{ specialize (Hin 0%Z ltac:(cbn [length]; lia)). rewrite at_self in Hin. exact Hin. }
apply IH.
- intros i Hi. rewrite u_succ_shift. apply Hin. cbn [length] in *. lia.
- intros x Hx. cbn beta. destruct (bv_eqb x a) eqn:Heq.
+ exfalso. apply Hx. unfold bv_eqb in Heq. apply Z.eqb_eq, bv_eq in Heq.
subst x. exact Ha.
+ apply H, Hx.
Qed.
Definition triple (segs : list Segment)
(C : regset) (W : memset)
(P : assn) (a b : word) (Q : assn) : Prop :=
forall regs mem rom, P regs mem rom ->
exists regs' mem',
msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
/\ Q regs' mem' rom
/\ regs_agree C regs regs'
/\ mem_agree W mem mem'.
Lemma triple_intro : ltac2:(TCodec.tc2 tcn__Hoare "R3'8'C%211&Q;&Q7&Hy5'S1yR0%211%5241':y8%611%311p061!pV@21pV>31pV<91r7r3r2r1%43321'>'<'Q1r=&Q@vR9r6r9r5r4%6554321r8%857?1>3%;3:31%C3A@5&Q:r<%231;D&Q6r;%231<F%D241%E281%F2:1qU8Q21%I2Q31qUBQ91%K2Q:1p0M1pULQ71pU6Q81pU@Q>1&Q=%17FQ6KIHQ5Q4p031pQHQ91pT0QD1pSNQE1pQDQ<1pSFQL1p2QN1pUNR01").
Proof. intros; assumption. Qed.
Lemma triple_skip : ltac2:(TCodec.tc2 tcn__Hoare "E'8'C%211&Q;&Q7&Q3'S1yR0%211&Q=r5r4r3r2r1%675432112pSN81pQD<1pSF>1p2@1pUNB1").
Proof.
intros segs C W P a regs mem rom HP.
exists regs, mem. split; [apply mst_refl|].
split; [exact HP|]. split; [apply regs_agree_refl|apply mem_agree_refl].
Qed.
Lemma triple_seq : ltac2:(TCodec.tc2 tcn__Hoare "Q@'8'C%211&Q;&Q7&Q3'S1yR0%211&Q=r;r:r9r6r3r2r5%877654321r<r8%;72817654r=y5%A11'@r1%511%A12%4221qU>61%<15%D16%8221qV<I1%I7=51?BDEp0?1p0C1pT8M1pT0N1pSNO1pQLQ31pQHQ41pQDQ51pSLQ71p8Q91pSJQ91p6Q;1pUNQ=1").
Proof.
intros segs C1 W1 C2 W2 P Q R a b c H1 H2 regs mem rom HP.
destruct (H1 _ _ _ HP) as (regs1 & mem1 & Hst1 & HQ & Hr1 & Hm1).
destruct (H2 _ _ _ HQ) as (regs2 & mem2 & Hst2 & HR & Hr2 & Hm2).
exists regs2, mem2. split; [eapply msteps_trans; eassumption|].
split; [exact HR|]. split.
- eapply regs_agree_trans;
[ eapply regs_agree_mono; [|exact Hr1]
| eapply regs_agree_mono; [|exact Hr2] ]; auto.
- eapply mem_agree_trans;
[ eapply mem_agree_mono; [|exact Hm1]
| eapply mem_agree_mono; [|exact Hm2] ]; auto.
Qed.
Lemma triple_conseq : ltac2:(TCodec.tc2 tcn__Hoare "R<'8'C%211&Q;'S1y5%211!pV<21&Q7yR0%711pV<15&Q3&H%12:4':y8%>11%311p091pV@1>pV>21pV<81&Q=r;r:r8r6r2r1r4%877654321r9r3%23165%;3527p021pULB1pU6C1pU@I1%83:7<p071pULG1pU6H1pU@N1r>%11A%21Cp021pU>Q<1r=%11F%21Hp021pV<Q<1r@r<r7%Q373=2Q11OQ0p051p0;1p0A1p0G1p0Q01pT0QF1pSNQG1pQJQ<1pQHQG1pQFQ>1pQDQI1pSHQK1pSFQO1p4R11p2R71pUNR91").
Proof.
intros segs C C' W W' P P' Q Q' a b H HP HQ HC HW regs mem rom HP'.
destruct (H _ _ _ (HP _ _ _ HP')) as (regs' & mem' & Hst & HQ0 & Hr & Hm).
exists regs', mem'. split; [exact Hst|]. split; [apply HQ, HQ0|].
split; [eapply regs_agree_mono; eauto | eapply mem_agree_mono; eauto].
Qed.
Lemma triple_seq_same : ltac2:(TCodec.tc2 tcn__Hoare "Q1'8'C%211&Q;&Q7&Q3'S1yR0%211&Q=r9r8r7r6r3r2r5%877654321r:%:71986543r;%<713;:578p031p061pT8@1pT0A1pSNB1pQLF1pQHG1pQDH1pSFJ1p2L1pUNN1").
Proof.
intros segs C W P Q R a b c H1 H2 regs mem rom HP.
destruct (H1 _ _ _ HP) as (regs1 & mem1 & Hst1 & HQ & Hr1 & Hm1).
destruct (H2 _ _ _ HQ) as (regs2 & mem2 & Hst2 & HR & Hr2 & Hm2).
exists regs2, mem2. split; [eapply msteps_trans; eassumption|].
split; [exact HR|].
split; [eapply regs_agree_trans; eassumption | eapply mem_agree_trans; eassumption].
Qed.
Definition frameable (C : regset) (W : memset) (R : assn) : Prop :=
forall regs mem rom regs' mem',
regs_agree C regs regs' -> mem_agree W mem mem' ->
R regs mem rom -> R regs' mem' rom.
Lemma triple_frame : ltac2:(TCodec.tc2 tcn__Hoare "QF'8'C%211&Q;&Q7&Q3'S1yR0%211&Q=r8r7r6r5r2r1r4%877654321&Q5%13983r:r9&Hy5%221@':y8%E11%311p0E1'<r3%<31BA%G32CB%4221qUL61qU671qU@=1%A37HG%9216qUL;1qU6<1qU@B1%Q27GFQ16K<1p0I1p0L1pT0Q61pSNQ71pQLQ;1pQHQ<1pQDQ=1pSFQ?1p2QA1pUNQC1").
Proof.
intros segs C W P Q R a b H HR regs mem rom (HP & HRr).
destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & Hr & Hm).
exists regs', mem'. split; [exact Hst|].
split; [split; [exact HQ | eapply HR; eassumption]|].
split; assumption.
Qed.
Lemma frameable_and : ltac2:(TCodec.tc2 tcn__Hoare "Q6&Q;&Q7&Q3&Q5r4r3r2%43321r5%63153r6&Hy5'S1yR0%211%5241':y8%611%311p061'<r7r1%23DC1%@3ED2%5221qUL71qU681qU@>1%L3EG1p0G1p0J1pR0Q01pQNQ11pSFQ31p2Q51").
Proof. intros C W R1 R2 H1 H2 regs mem rom regs' mem' Hr Hm (A & B); split; eauto. Qed.
Lemma frameable_reg : ltac2:(TCodec.tc2 tcn__Hoare "Q4&Q;&Q7'S1y5%211yR0%411&?r4r2%211%411&Q5r5&H%12<9':y8%@11%311p0>1'=&Q?r3r6%3221%53D1=q071q081qU@>1%B3AF1p0D1pV:J1pU>M1pSFQ11p2Q31").
Proof.
intros C W r v Hnc regs mem rom regs' mem' Hr _ Hv.
rewrite (Hr r Hnc). exact Hv.
Qed.
Lemma frameable_rdn : ltac2:(TCodec.tc2 tcn__Hoare "R1'8'C%211&Q;&Q7'S1yR0%211'9y8%511%;11'A'<&QFzr1%3221&QG&QIr3%211%4261%:261&?r6&S0&QD&S3r5%22H1r2%5221%72K1%911%;11p0=1pTHI1&Q5&Hy5%221Q2':%11Q1p0Q51'=%41Q3&QAr:r7%342C1I(6%12Q9G%83731q0:1qU6;1q0?1%C3Q0L1p0E1pT4Q@1pU:QD1pSNQF1pSFQJ1p2QL1pUNQN1").
Proof.
intros segs C W a n bs Hdisj regs mem rom regs' mem' _ Hm Hrd.
rewrite <- Hrd. clear Hrd bs. revert a Hdisj.
induction n as [|n IH]; intros a Hdisj; [reflexivity|].
assert (Ha : ~ W a).
{ specialize (Hdisj 0%Z ltac:(lia)). rewrite at_self in Hdisj. exact Hdisj. }
cbn [rdn]. rewrite (Hm a Ha). rewrite IH; [reflexivity|].
intros i Hi. rewrite u_succ_shift. apply Hdisj. lia.
Qed.
Definition ret_ok (k : word) : Prop := v_jalr k 0 = k.
Lemma land_m2_even : ltac2:(TCodec.tc2 tcn__Hoare "?'A'=&QHr1+2%3221z%63721&QEr2-2%3221%;3<13p061pVB>1").
Proof.
intros z Hz.
assert (Hl : Z.land z 1 = 0%Z).
{ replace 1%Z with (Z.ones 1) by reflexivity. rewrite Z.land_ones by lia. exact Hz. }
replace (-2)%Z with (Z.lnot 1) by reflexivity.
rewrite <- Z.ldiff_land.
rewrite <- (Z.lor_ldiff_and z 1) at 2.
rewrite Hl, Z.lor_0_r. reflexivity.
Qed.
Lemma ret_ok_even : ltac2:(TCodec.tc2 tcn__Hoare "B'S1yR0%211'='A&QH&S3r1%2271+2%5221z%93821&Q<r2%211p041pTJ?1").
Proof.
intros k Hk. unfold ret_ok, v_jalr, jalr_tgtZ.
rewrite Z.add_0_r, land_m2_even by exact Hk.
apply bv_eq. rewrite Z_to_bv_unsigned.
apply bv_wrap_small, bv_unsigned_in_range.
Qed.
Definition proc (segs : list Segment) (C : regset) (W : memset)
(P : assn) (entry : word) (Q : assn) : Prop :=
forall k : word, ret_ok k ->
triple segs C W (fun regs mem rom => P regs mem rom /\ getr regs 1 = k) entry k Q.
Definition ra_indep (P : assn) : Prop :=
forall regs v mem rom, P regs mem rom -> P (regupd regs 1 v) mem rom.
Lemma triple_call : ltac2:(TCodec.tc2 tcn__Hoare "R='8'C%211&Q;&Q7&Q3'S1yR0%211&Hy5%2213':y8%811%311p081'='E'F%211&Gr;&Q@vR9r3r6r2r1%6554321%9281(D&QB(RO+1(;%33J21r4%63=21r5%A5@21=<%:2F1%I3F<1pULK1pU6L1pU@Q21&Q<%11D&Q9r7%211&Q8r:r9r8%46Q1321@6&Q=r<%QD1Q@'@%31Q0%Q<33Q1I%3221qU>51%8771<;?I:p0:1p0@1p0D1p0G1pUJQM1pTBQN1pT:QO1pQHR31pQDR41pSFR61p2R81pUNR:1").
Proof.
intros segs C W P Q callsite entry ret Hjal Hret HraP Hproc regs mem rom HP.
assert (Hpre : P (regupd regs 1 ret) mem rom
/\ getr (regupd regs 1 ret) 1 = ret).
{ split; [apply HraP, HP|]. apply getr_same. reg_neq_tac. }
destruct (Hproc ret Hret (regupd regs 1 ret) mem rom Hpre)
as (regs' & mem' & Hst & HQ & Hr & Hm).
exists regs', mem'. split.
- eapply mst_step; [reflexivity | apply Hjal | exact Hst].
- split; [exact HQ|]. split; [|exact Hm].
intros r Hr0.
assert (HnC : ~ C r) by tauto.
assert (Hne : r <> 1) by tauto.
rewrite (Hr r HnC), getr_other by exact Hne. reflexivity.
Qed.
Lemma triple_loop : ltac2:(TCodec.tc2 tcn__Hoare "Q;'8'C%211&Q;&Q7'9&Q3p021'S1yR0%211&Q=r8r7r6r5(5r1%211%411r4%614%;7:983221pTHB1(4%:11r3r2%A7@?>3821r:r9%B1>%E732D1BA<pU:L1p061p0<1pQHN1pU<K1pTFL1pQ6Q01pSFQ41p2Q61pUNQ81").
Proof.
intros segs C W I hd out Q Hbody Hexit n.
induction n as [|n IH]; [exact Hexit|].
eapply triple_seq_same; [apply Hbody | exact IH].
Qed.
Lemma triple_loop_measure : ltac2:(TCodec.tc2 tcn__Hoare "QN'8'C%211&Q;&Q7'9&Q3p021'S1yR0%211&Q=r9r8r7r6(5r1%211%411r5%614%;7:983221pTHB1(4%:11r4r3%A7@?>3821&Hy5%221E':y8%J11%311p0J1r2%G3;1E'>r<%14HE?>qU:Q51%42Q61p061pUL91pU6:1pU@@1r;r:%Q7721Q6HQ4Q3Np041p0H1p0N1pQDQ@1pQHQA1pU<Q>1pTFQ?1pQ6QC1pSFQG1p2QI1pUNQK1").
Proof.
intros segs C W I hd out Q P Hbody Hexit Hmeas regs mem rom HP.
destruct (Hmeas _ _ _ HP) as (n & HI).
exact (triple_loop segs C W I hd out Q Hbody Hexit n regs mem rom HI).
Qed.
Lemma triple_msteps : ltac2:(TCodec.tc2 tcn__Hoare "QI'8'C%211&Q;&Q7&Q3'S1yR0%211&Hy5%2213':y8%811%311p081&Q=r:r9r8r7r6r5r4%877654321r3r2%83421'>'<'Q1r>&Q@vR9%251>A=<r1%453:B1>%73631%C3<3@%:221qU8I1%=2J1qUBQ01%?2Q11p0A1p0E1pULO1pU6Q01pU@Q61pQHQ=1pT0Q;1pSNQ<1pQDQ@1pSFQB1p2QD1pUNQF1").
Proof.
intros segs C W P a b Q regs mem rom H HP.
destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & _ & _).
exists regs', mem'. split; assumption.
Qed.
Lemma triple_wexit : ltac2:(TCodec.tc2 tcn__Hoare "QN'8'C%211&Q;&Q7&Q3'S1yR0%211y8%411%;11%<11&Hy5%2217':%117p0:1&Q=r<r;r:r9r8r7r6%877654321r4r3r2%93321r1r5%<3421'Q2rA&Q@vR9%251:C9=%5441BAp071pU8H1pUBL1r?%857CH<A%;421FEp041p0A1p0F1pULQ01pU6Q11pU@Q51pT<Q=1pT6Q:1pQHQB1pT0Q@1pSNQA1pQDQE1pSFQG1p2QI1pUNQK1").
Proof.
intros segs C W P a b Q bufs code regs mem rom H HP Hcont.
destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & _ & _).
eapply msteps_to_wexit; [exact Hst | apply Hcont, HQ].
Qed.
End WithFP1.
