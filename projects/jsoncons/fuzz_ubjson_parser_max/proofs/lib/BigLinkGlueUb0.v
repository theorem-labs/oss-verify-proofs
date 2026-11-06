(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec SeqExec StoreOk AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun BigLinkBase.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__BigLinkGlueUb0 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3Sound.AX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymRun3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigLinkBase.BL."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigLinkGlueUb0.BGU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1O"; "1Some"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2not"; "2or"]; ["3add"; "4le"; "4lt"; "5map"; "5nth"; "5seq"; "6Z"; "0E"; "0E'"; "7word_to_le_bytes"; "8ALU_ADD"; "8M_MUL"; "9bvmap"; ":alu64"; ":mul_div"; "0M"]; ["0M'"; "0R"; "0R'"; ";ELit"; ";EVar"; ";KAlign"; ";KDisj"; ";KRange"; ";KUnk"; ";KWord"; ";KWr"; ";KZero"; ";SA"; ";adenot"; ";edenot"; ";env"]; [";ev"; ";evars_lt"; ";expr"; ";expr_eqb"; ";sr_get"; "<estart"; "<kentry_ok"; "<regs_ok"; "=env_agree"; "=expr_vars_lt"; ">uv"; ">za"; ">zcomp"; ">zden"; ">zeval"; "?E_R"]; ["?defined"; "?kept_ok"; "?slots"; "?slots_ok"; "?u64_at"; "?u8_at"; "?writable"; "@getr"; "@rdn"; "Amem_grows"; "Bloaded_segments"; "CIn"; "Ctl"; "Dadd"; "Dle"; "Dlt"]; ["Dmodulo"; "Dmul"; "Dof_nat"; "Dpow"; "0a"; "0a1"; "0a2"; "0b"; "0e"; "0ebs"; "0f"; "0hi"; "0hi1"; "0hi2"; "0i"; "0i0"]; ["0j"; "0j1"; "0j2"; "0k"; "0ks"; "0lo"; "0lo1"; "0lo2"; "0m"; "0n"; "0n1"; "0n1e"; "0n2"; "0n2e"; "0ne"; "0off"]; ["0off1"; "0off2"; "0ps_regs"; "0rest"; "0ro"; "0sr"; "EZ_to_bv"; "Ebv"; "Ebv_add"; "Ebv_unsigned"; "0t"; "0t1"; "0t2"; "0v"; "0w"; "0x"]; ["0z"]]).
Module BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition E_R (R : bvmap 5 word) (rest : nat -> word) (ebs : nat -> list byte) : env := Env (reg_ev R rest) ebs.
Lemma E_R_reg : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "Q6&Ly5'SGyR0%211%5241'6p013'5y8%811%311p061&Br1uQ0%3221'=&Q@&QOr5r4r3%43321r2%7221&R7&SF&RB%115%32M1%52;1%?3L71p0A1pUNL1pUDG1pW8M1pR4Q01").
Proof. intros R rest ebs i. intros. unfold E_R, reg_ev. cbn [ev]. destruct (Nat.ltb_spec i 32); auto. lia. Qed.
Lemma E_R_rest : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "Q1&Ly5'SGyR0%211%5241'6p013'5y8%811%311p061'AuQ0r1%3221'=&Q@&QOr5r4r3%43321r2%7221%512%:3G21p0<1pUNG1pUDB1pW8H1pR4K1").
Proof. intros R rest ebs i. intros. unfold E_R, reg_ev. cbn [ev]. destruct (Nat.ltb_spec i 32); auto. lia. Qed.
Fixpoint slots_ok (E : env) (R : bvmap 5 word) (sr : list expr) (i : nat) : Prop :=
match sr with
| [] => True
| e :: t => (match e with EVar j => (j = i)%nat \/ getr R (Z_to_bv 5 (Z.of_nat i)) = edenot E e
| _ => getr R (Z_to_bv 5 (Z.of_nat i)) = edenot E e end) /\ slots_ok E R t (S i)
end.
Lemma slots_ok_nth : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "QE'Q?&Ly5'SGyR0%211%5241'5'QB%211'6&R3r4r3r2r1%544321&B&4%12;7%3251'?'=&Dr5(Q3z%211%54D>41(Q4&@%12CA%311%;3I51&R7r6&SF&RB%117%32Q51%6251&Q>r7%221?%F3Q741%H2<1p0J1pUNQ51p0Q01pV0Q71pW<Q91pR4Q=1pQ@QD1").
Proof. intros E R sr.
induction sr as [|e t IH]; intros i0 H i Hi. exfalso; simpl in Hi; lia.
simpl in H. destruct H as [He Ht]. destruct i.
- rewrite Nat.add_0_r. cbn [nth]. destruct e; try (right; exact He). destruct He as [He|He]. left; subst; reflexivity. right; exact He.
- replace (i0 + S i)%nat with (S i0 + i)%nat by lia. cbn [nth]. apply IH; auto. simpl in Hi; lia.
Qed.
Lemma regs_ok_slots : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "Q8&Ly5'SGyR0%211%5241'6p013'5y8%811%311p061'QB%611'=&4r1%2251uQ0%53>21&R3&QOr5r4r3%43321r2(0%843621&QGr6%:3198%33182p051p0?1pW<F1pUDI1pW8O1pR4Q21").
Proof. intros R rest ebs sr.
intros Hl Hs r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot]. apply getr_zero.
- pose proof (ridx_range r) as Hr.
destruct (slots_ok_nth _ _ _ 0 Hs (ridx r) ltac:(lia)) as [E|E]; simpl in E.
+ rewrite E. cbn [edenot]. rewrite E_R_reg by auto. rewrite ridx_roundtrip. reflexivity.
+ rewrite ridx_roundtrip in E. exact E.
Qed.
Fixpoint slots (E : env) (R : bvmap 5 word) (sr : list expr) (i : nat) : Prop :=
match sr with
| [] => True
| e :: t => getr R (Z_to_bv 5 (Z.of_nat i)) = edenot E e /\ slots E R t (S i)
end.
Lemma slots_nth : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "Q@'Q?&Ly5'SGyR0%211%5241'5'QB%211'6&R2r4r3r2r1%544321&B&4%12;7%3251'=&R7r6&SF&RB&@%12?=%311%52K1%8271&Q>r7&Dr5(Q3z%211%54NH41%8271%C3Q3:1p0E1pUNQ01p0K1pV0Q21pW<Q41pR4Q81pQ@Q?1").
Proof. intros E R sr.
induction sr as [|e t IH]; intros i0 H i Hi. exfalso; simpl in Hi; lia.
simpl in H. destruct H as [He Ht]. destruct i.
- rewrite Nat.add_0_r. exact He.
- replace (i0 + S i)%nat with (S i0 + i)%nat by lia. cbn [nth]. apply IH; auto. simpl in Hi; lia.
Qed.
Lemma regs_ok_of_slots : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "Q1'Q?&Ly5'SGyR0%211%5241'5'QB%211'='6&4r1%2261uQ0%63521&R2r4r3&R<r2%22>1u1%746521&QGr5%23189p041p0=1pW<E1pR4I1pQ@Q01").
Proof. intros E R sr.
intros Hl Hs r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot]. apply getr_zero.
- pose proof (ridx_range r) as Hr.
assert (Hnz: ridx r <> 0%nat).
{ intros Z0. assert (r = 0%bv). { rewrite <- (ridx_roundtrip r). rewrite Z0. apply bv_eq. reflexivity. } subst r.
unfold bv_eqb in Hr0. rewrite Z.eqb_refl in Hr0. discriminate. }
destruct sr as [|e0 t]. simpl in Hl; lia. simpl in Hl. cbn [tl] in Hs.
pose proof (slots_nth E R t 1 Hs (ridx r - 1) ltac:(simpl; lia)) as X.
replace (1 + (ridx r - 1))%nat with (ridx r) in X by lia. rewrite ridx_roundtrip in X.
rewrite X. destruct (ridx r) eqn:E0. lia. replace (S n - 1)%nat with n by lia. reflexivity.
Qed.
Lemma reg_out : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "QK'5':'6'QB%3221%511&Ly5'SGyR0%211%5241'Q?&R;(9r2r1%34?>21r7%63?21'<&B(0r3%3221uQ0%5231%7231'=&R7&SF&RB%119%32J1%52@1&Q>r6%221F%:3L41%C2<1p0E1pUBQ61pUNQ81%M4Q9Q8DL%O3Q818r4%?11%A2Q81%C2<1r5%?21K%G3Q931p081p0;1pUBQC1pUNQE1pQBQ<1pR6Q>1pW6QE1").
Proof. intros ps_regs R' E' i e. intros H Hin. apply (H i e Hin). Qed.
Lemma edenot_kept : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "L'6'Q?'QB&QHr4r3r2%43321'='2&QIr5%2216(;%63521'SGyR0%211&Q>%12?>%229?%=3421p081p0@1pUBF1pQBH1pQ@I1pU@K1").
Proof. intros b E E' e. intros. symmetry. eapply edenot_agree; eauto. Qed.
Lemma sr_get_reg : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "O'5'QB%211'6'<&B(0r1%3221uQ0%5231%7231'=&QDr3&SFy5&RBr2%211%5241%8271&D(Q3z%211%44I8<1%?3J61p0A1pUNJ1pW<L1").
Proof. intros sr i.
intros Hi. unfold sr_get.
assert (R: ridx (Z_to_bv 5 (Z.of_nat i)) = i).
{ unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
destruct (bv_eqb (Z_to_bv 5 (Z.of_nat i)) 0) eqn:E.
- exfalso. unfold bv_eqb in E. apply Z.eqb_eq in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E.
change (bv_modulus 5) with 32 in E. rewrite Z.mod_small in E by lia. change (bv_unsigned (0%bv : bv 5)) with 0 in E. lia.
- rewrite R. reflexivity.
Qed.
Lemma kept_reg : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "R='Q?&Ly5'SGyR0%211%5241'5'QB%211'6&QGr8r4r6%43321&QHr3r9%33217'<&B(0%2216uQ0%4281%6231'='2&QC&D(Q3z%211%44JED1r7%64LG13%8231(;%<3;21&QIr5%<4Q21N9%32M1%A3@16&R7r:&SF&RB%11Q3%32Q@1%6251&Q>r<%H4Q>Q8Q:E%3221%M3QC51r;%:1G%<2QI1%?231%@282%Q33QI21p071p0D1p0J1p0Q81p0Q@1p0QE1pUNQK1pU@QL1pW:QN1pW<QO1pR6R31pR4R41pQBR;1pQ@R<1").
Proof. intros E E' R R' sr ro b i.
intros HR HA Hi He Hv HG. apply expr_eqb_eq in He. rewrite HG, He.
rewrite (edenot_kept b E E') by auto. rewrite (HR (Z_to_bv 5 (Z.of_nat i))). rewrite sr_get_reg by auto. reflexivity.
Qed.
Definition kept_ok (b : nat) (sr ro : list expr) (ks : list nat) : bool :=
forallb (fun i => (0 <? i)%nat && (i <? 32)%nat && expr_eqb (nth i ro (ELit 0)) (nth i sr (ELit 0)) && expr_vars_lt b (nth i sr (ELit 0)))%bool ks.
Definition kept_list (b : nat) (sr ro : list expr) : list nat :=
List.filter (fun i => expr_eqb (nth i ro (ELit 0)) (nth i sr (ELit 0)) && expr_vars_lt b (nth i sr (ELit 0)))%bool (seq 1 31).
Lemma in_psregs : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "Q6'5'QB%211'6'<&B(0r1%3221uQ0%5231%7231&R;':%12;=(9r2&Dr3(Q3z%211%54E641%84DF71&Cr4%94IC15%<4HJD1qUNI1&Eu1uO%3221%94NC51%F3D;1p0H1pUNQ11pW:Q31").
Proof. intros ro i. intros Hi. apply in_map_iff. exists i. split; auto. apply in_seq. lia. Qed.
Lemma kept_regs : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "RM'Q?&Ly5'SGyR0%211%5241'5'QB%211'6%411'='2&R1r2r4r3r1%544321(;%93821&QGr9r5r7%43321&QHr:%23=16&R;':%12FH(9%14HJC@&C&D(Q3z%211%44Q0FA1%84OQ1G1qUNQ01&Eu1uO%3221%<4Q5?51%B3@>1'<&B(0%221Q3uQ0%42Q51%6231&R7r;&SF&RB%11Q;%32QK1%6251&Q>r=%221QB%QF3QM41%B2<1p0D1pUBQM1pUNQL1r6%Q:3QNQF1%>1QJ%@2R81%C2B1r<%E213%R23R931p071pUNR61p0;1p0QE1p0QI1p0QO1pV:R:1pU@R<1pW:R>1pW<R?1pR6RC1pR4RD1pQBRK1pQ@RL1").
Proof. intros E E' R R' sr ro b ks.
intros HK HR HA HO i Hi. unfold kept_ok in HK. rewrite forallb_forall in HK. specialize (HK i Hi).
apply andb_prop in HK. destruct HK as [HK Hv]. apply andb_prop in HK. destruct HK as [HK He].
apply andb_prop in HK. destruct HK as [H0 H32]. apply Nat.ltb_lt in H0. apply Nat.ltb_lt in H32.
assert (Hi1 : (0 < i < 32)%nat) by (split; assumption).
exact (kept_reg E E' R R' sr ro b i HR HA Hi1 He Hv (proj2 (HO i (nth i ro (ELit 0)) (in_psregs ro i Hi1)))).
Qed.
Lemma out_reg : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "R7'5'QB%211'Q?&Ly5'SGyR0%211%5241'6&R;':%123<(9r2r1%347@21&C&Dr7(Q3z%211%54G841%;4?H91qUN@1&Eu1uO%3221%=4EB51%E3C?1'<&B(0r3%3221uQ0%5231%7231'=&R7r5&SF&RB%11:%32Q:1%6251&Q>r6%221Q4%;3Q<41%D2=1p0F1pUBQF1pUNQ>1%G2FQ:%H2Q;D%J221r4%C21>%Q;4QMJ<Q7%>2D1%G3QH31p061p0:1pUNQI1pR6QK1pQBR21pW:R41").
Proof. intros ro E' R' i.
intros HO Hi. exact (proj2 (HO i (nth i ro (ELit 0)) (in_psregs ro i Hi))).
Qed.
Lemma zeval_kept : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "Q7'6'Q?'QB'F&QHr5r4r3%43321'='2&QAr6%2216(;%63521'8%11>&QN&QJ%118%321?(1%12D@%?3731&SIyR0&Q>%12@G%4231%E3K1Hp071p0A1p0I1pX2O1pUBQ11pQBQ31pQ@Q41pU@Q61").
Proof. intros b E E' e z.
intros HA Hv Hz. apply BL.zeval_sound. rewrite <- Hz. apply BL.zeval_agree with (b := b); auto.
intros n Hn. unfold BL.uv. destruct HA as [HA _]. rewrite HA; auto.
Qed.
Lemma word_of_unsigned : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "A'SGyR0%211'F'=&SIr2%2261r1%53621r3&SF%12;6%93;31p051pX2<1pWN>1").
Proof. intros w z. intros H. apply bv_eq. rewrite Z_to_bv_unsigned. rewrite <- H. symmetry. apply bv_wrap_bv_unsigned. Qed.
Definition u64_at (M : word -> option byte) (a : Z) (v : Z) : Prop :=
rdn RSEGS M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)).
Definition writable (M : word -> option byte) (a n : Z) : Prop :=
forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok RSEGS M (Z_to_bv 64 (a + d)) k = true.
Definition defined (M : word -> option byte) (a n : Z) : Prop :=
forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) <> None.
Lemma estart_var : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "H'Q?'6'F'=&QEr3(Q<(Q4r2%211r1%5221%8271&R=&SIyR0&Q@%12<9%4231%6219%A3B81pW0C1pV2E1pQ@G1").
Proof. intros E j off. reflexivity. Qed.
Lemma kentry_KRange : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "Q>'Q?'SGyR0%211'8y8%511%311p051'QB'F'=%812&QN&QJr6%211r4%5221(1r1%22;1%;3:41'<&R>r2%2291r3%4231%6231&QF&R:r8r7(Q7r5%23E1C%746541p091p0A1pX2N1pUHO1pV<Q01pUBQ21pR0Q41pQ@Q=1").
Proof. intros E M e lo hi z. intros Hz Hr. cbn [kentry_ok]. rewrite (BL.zeval_sound E e z Hz). lia. Qed.
Lemma adenot_var : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "L'Q?'6'F'='SGyR0%211&Q=r3(Q<(Q4r2%211r1%5221%8271&SF&R=&SI&Q@%12<9%32@1%5219%72B1%E3B91pW0G1pV2I1pQ@K1").
Proof. intros E j off. reflexivity. Qed.
Lemma kentry_KRange_var : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "Q='Q?'SGyR0%211'8y8%511%311p051'6'F'=&SI&Q@r6r4%3221%52?1r1%83921'<&R>r2%2281r3%4231%6231&QF&R:r8r7(Q7(Q4%11Cr5%4321D%948761p0;1p0C1pU:M1pUHN1pV<O1pV2Q11pR0Q31pQ@Q<1").
Proof. intros E M j lo hi a. intros Ha Hr. cbn [kentry_ok edenot]. rewrite Ha. lia. Qed.
Lemma kentry_KRange_z : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "QD'Q?'SGyR0%211'8y8%511%311p051'QB'QK'F'=%913&QLr5%211(1r4%2291%83741&QM&QJr8%211%421:r2%?3@21'<&R>r3%22@1%322>%5221&QF&R:r:r9(Q7r6%23A1I%746541p091p0@1p0H1pX2Q21pUHQ31pV<Q41pWFQ61pUBQ81pR0Q:1pQ@QC1").
Proof. intros E M e t lo hi z. intros Ht Hz Hr. cbn [kentry_ok]. rewrite (BL.zcomp_sound E e t Ht), Hz. lia. Qed.
Lemma kentry_KAlign_var : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "Q='Q?'SGyR0%211'8y8%511%311p051'6'F'=&SI&Q@r5r3%3221%52?1r1%83921&R?z%2217&R@r4%22:1%?3@15&QF&R:r8r7(Q5(Q4r6%211%421E%948761p0;1p0@1p0D1pU:N1pVBO1pV2Q11pR0Q31pQ@Q<1").
Proof. intros E M j m a. intros Ha Hm H0. cbn [kentry_ok edenot]. rewrite Ha. auto. Qed.
Lemma kentry_KWr_z : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "RG'Q?'SGyR0%211'8y8%511%311p051'6'F'QB'QK'=&SI&Q@r8r6%3221%52A1r4%83;21%B1:&QL%114(1r3%22?1%?3641&QM&QJr:%211%421=%E3H18&R>z&R=r7%221G%5241'<&R?r5%2281&RC+2+R0%3221%7261%9261r9%?21E%@21Q4%C216&R6r=r;%E2K1%4331E&QF&R:r?r>(Q:(Q<(Q4%11;r<%4221%621Q7%;4:981p0=1p0C1p0H1p0Q31p0Q:1p0QA1p0QI1pVDR51pWFR41pVNR61pU:R81pW0R91pV2R;1pR0R=1pQ@RF1").
Proof. intros E M j off a ne t n.
intros Ha Ht Hn H1 H2 H3 Hw. cbn [kentry_ok]. unfold flat, elenZ. rewrite estart_var, Ha.
rewrite (BL.zcomp_sound E ne t Ht), Hn. split. lia. intros d m Hd Hm. apply Hw; lia.
Qed.
Lemma kentry_KDisj_z : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "RO'Q?'SGyR0%211'8y8%511%311p051'6'F'QB'QK'=&SI&Q@r>r<%3221%52A1r2%83;21r?r8%9221%;2G1%=3@16%G1?&QL%11<(1r;%22D1%D3641&QM&QJrA%211%421E%J3M18r9%=11%<2NC%N3@21rC%:11%<216%Q23Q51H'?&R>&R=%12L?%221Q4r7%421Q5%6231%622@%8216%:231&QF&R:rErD(Q6(Q<(Q4%11FrB%4221%41QEr=%7221%944Q41QG%>4=<;1p0@1p0L1p0Q11p0Q61p0Q=1p0QE1p0QK1pU>R71pU<R81pVJR91pWJR81pVLR:1pW4R<1pV6R>1pVFR>1pWHR=1pVHR?1pW2RA1pV4RC1pR0RE1pQ@RN1").
Proof. intros E M j1 off1 n1e t1 n1 j2 off2 n2e t2 n2 a1 a2.
intros Ha1 Ha2 Ht1 Hn1 Ht2 Hn2 Hd. cbn [kentry_ok]. unfold elenZ. rewrite !estart_var, Ha1, Ha2.
rewrite (BL.zcomp_sound E n1e t1 Ht1), Hn1, (BL.zcomp_sound E n2e t2 Ht2), Hn2. exact Hd.
Qed.
Definition u8_at (M : word -> option byte) (a : Z) (b : Z) : Prop :=
rdn RSEGS M (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 b].
Lemma word_to_le_bytes_1 : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "O'F'<&R>zr1%3221&R?+X0%2241%8241'='5'SGy8%211%411&Iu1&SFyR0r2%3221%6251(3%62;4(7%11<%43=31%B3=61p0D1pX2N1").
Proof. intros z.
intros Hz. unfold word_to_le_bytes. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. change (bv_modulus 64) with (2^64). rewrite (Z.mod_small z (2^64)) by lia. reflexivity.
Qed.
Lemma kentry_KWord1_lit : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "R8'Q?'SGyR0%211'8y8%511%311p051'6'F'=&SI&Q@r6r4%3221%52?1r2%83921&R>z&R=r3%2219%5241r5%52<1+1%7221&RC+2+R0%3221%>251'<%@2?E&R?+X0%22H1%5241&R5r9r7%F2N1%4331C&QF&R:r;r:(Q9(Q<(Q4%11;r8%4221u1(Q3%11Q<%93431%>4=<;1p0@1p0F1p0M1p0Q71p0Q>1pU@QH1pU:QI1pW0QJ1pV2QL1pR0QN1pQ@R71").
Proof. intros E M j off a b.
intros Ha H1 H2 Hb Hu. cbn [kentry_ok]. split. lia. split.
- unfold flat. rewrite estart_var, Ha. lia.
- rewrite adenot_var, Ha. cbn [edenot]. rewrite word_to_le_bytes_1 by auto. exact Hu.
Qed.
Lemma kentry_KWord_lit : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "R0'Q?'SGyR0%211'8y8%511%311p051'6'F'=&SI&Q@r6r4%3221%52?1r2%83921&R>z&R=r3%2219%5241r5%52<1+8%7221&RC+2+R0%3221%>251&R4r8%?2;G%3321G&QF&R:r:r9(Q9(Q<(Q4%11:r7%4221u8(Q3%11I%93431%>4=<;1p0@1p0E1p0O1p0Q61pWLQ@1pU:QA1pW0QB1pV2QD1pR0QF1pQ@QO1").
Proof. intros E M j off a v.
intros Ha H1 H2 Hu. cbn [kentry_ok]. split. lia. split.
- unfold flat. rewrite estart_var, Ha. lia.
- rewrite adenot_var, Ha. cbn [edenot]. exact Hu.
Qed.
Lemma kentry_KWord_z : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "RC'Q?'SGyR0%211'8y8%511%311p051'6'F'QB'QK'=&SI&Q@r8r6%3221%52A1r2%83;21%B1:&QLr5%211(1r4%22@1%@3741&QM&QJr:%211%421:r3%G3J21&R>z&R=%12@H%4231r9%42J1+8%6221&RC+2+R0%3221%=251&R4r<r7%?21F%4331Q6&QF&R:r>r=(Q9(Q<(Q4%11;r;%4221u8%7321Q3%<4;:91p0>1p0D1p0N1p0Q41p0Q<1p0QE1pWLR11pU:R21pWFR11pUBR31pW0R51pV2R71pR0R91pQ@RB1").
Proof. intros E M j off e t a v.
intros Ha Ht Hv H1 H2 Hu. cbn [kentry_ok]. split. lia. split.
- unfold flat. rewrite estart_var, Ha. lia.
- rewrite adenot_var, Ha. pose proof (BL.zcomp_sound E e t Ht) as S. rewrite Hv in S.
rewrite (word_of_unsigned _ _ S). exact Hu.
Qed.
Lemma u8_of_KWord1 : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "QI'Q?'SGyR0%211'8y8%511%311p051'6'F&QF&R:r6r5(Q9(Q<(Q4r4%211r3%5221u1(Q3r1%211%;3541%@4?>=1'=&SI&Q@r7%221B%42O1%63H1>'<&R>z%221B&R?+X0%22E1%7241&R5r8&R=%12Q0Q1%4331Mp061p0?1p0G1pU@Q91pU:Q:1pW0Q;1pV2Q=1pR0Q?1pQ@QH1").
Proof. intros E M j off a b.
intros K Ha Hb. cbn [kentry_ok] in K. destruct K as (_ & F & Rd). unfold u8_at.
rewrite adenot_var, Ha in Rd. cbn [edenot] in Rd. rewrite word_to_le_bytes_1 in Rd by auto. exact Rd.
Qed.
Lemma bv_add_lit : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "G'F'SGyR0%211'=&SIr2%2251r3%53921&SH&SF%12:6%33;51&R=r4%221:%62?1%>3?51p0:1pV8D1pWNB1pU:F1").
Proof. intros a w k.
intros Ha. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, Ha. unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma kentry_KWord_var : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "R5'Q?'SGyR0%211'8y8%511%311p051'6'F'=&SI&Q@r7r5%3221%52?1r2%83921r8r4%9221%;2E1%=3>16&R>z&R=r6%2281%5241%42@A+8%6221&RC+2+R0%3221%=251&R4r:%>2=E%3321K&QF&R:r<r;(Q9(Q<(Q4%11:r9%4221u8%51Q2%83321%=4<;:1p0?1p0D1p0M1p0Q41p0Q:1pWLQD1pU:QE1pV8QG1pW0QG1pV2QI1pR0QK1pQ@R41").
Proof. intros E M j off k a v.
intros Ha Hv H1 H2 Hu. cbn [kentry_ok]. split. lia. split.
- unfold flat. rewrite estart_var, Ha. lia.
- rewrite adenot_var, Ha. cbn [edenot]. rewrite (word_of_unsigned (ev E k) v Hv). exact Hu.
Qed.
Lemma kentry_KWr_var : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "R5'Q?'SGyR0%211'8y8%511%311p051'6'F'=&SI&Q@r6r4%3221%52?1r2%83921&R>z&R=r3%2219%5241'<&R?%1275&RC+2+R0%3221%62:1%8261r5%>21F%?21F%B216&R6r9r7%D2L1%43318&QF&R:r;r:(Q:(Q<(Q4%11;r8%4221(Q3%11Q9%8231%=4<;:1p0?1p0E1p0J1p0Q41p0Q;1pVDQE1pU:QF1pW0QG1pV2QI1pR0QK1pQ@R41").
Proof. intros E M j off a n.
intros Ha H1 H2 H3 Hw. cbn [kentry_ok]. unfold flat, elenZ. rewrite estart_var, Ha. cbn [edenot].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
split. lia. intros d m Hd Hm. apply Hw; lia.
Qed.
Lemma kentry_KUnk_var : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "R5'Q?'SGyR0%211'8y8%511%311p051'6'F'=&SI&Q@r6r4%3221%52?1r2%83921&R>z&R=r3%2219%5241'<&R?%1275&RC+2+R0%3221%62:1%8261r5%>21F%?21F%B216&R0r9r7%D2L1%43318&QF&R:r;r:(Q8(Q<(Q4%11;r8%4221(Q3%11Q9%8231%=4<;:1p0?1p0E1p0J1p0Q41p0Q;1pVDQE1pU:QF1pW0QG1pV2QI1pR0QK1pQ@R41").
Proof. intros E M j off a n.
intros Ha H1 H2 H3 Hd. cbn [kentry_ok]. unfold flat, elenZ. rewrite estart_var, Ha. cbn [edenot].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
split. lia. intros i Hi. apply Hd. lia.
Qed.
Lemma u64_of_KWord : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "QE'Q?'SGyR0%211'8y8%511%311p051'6'F'QB&QF&R:r7r6(Q9(Q<(Q4r5%211r4%5221u8r3%93321%>4=<;1'=&SI&Q@r8%221@%42N1%63G19&Q>r9%221A%92Q31%;3L1>&R4&R=%12FK%3371Ep051p0;1p0C1pX2Q41pU:Q51pUBQ51pW0Q71pV2Q91pR0Q;1pQ@QD1").
Proof. intros E M j off e a z.
intros K Ha Hz. cbn [kentry_ok] in K. destruct K as (_ & F & Rd). unfold u64_at.
rewrite adenot_var, Ha in Rd. rewrite <- (word_of_unsigned _ _ Hz). exact Rd.
Qed.
Lemma adenot_e : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "J'Q?'QB'F'='SGyR0%211&Q=r3(Q<r2r1%3221%6251&SF&R=&SI&Q>%12:8%32>1%5219%72@1%C3@91pW0E1pU@G1pQ@I1").
Proof. intros E b off. reflexivity. Qed.
Lemma kentry_KWord_e : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "R2'Q?'SGyR0%211'8y8%511%311p051'QB'F'=&SI&Q>r7r5%3221%52?1r2%83921r8r4%9221%;2E1%=3>16&R>z&R=r6%2281%5241%42@A+8%6221&RC+2+R0%3221%=251&R4r:%>2=E%3321K&QF&R:r<r;(Q9(Q<r9%22:1u8%5321Q0%:49871p0<1p0A1p0J1p0Q11p0Q71pWLQA1pU:QB1pUBQD1pW0QD1pU@QF1pR0QH1pQ@R11").
Proof. intros E M b off e a v.
intros Ha Hv H1 H2 Hu. cbn [kentry_ok]. split. lia. split.
- unfold flat, estart. cbn [a_base a_off]. rewrite Ha. lia.
- rewrite adenot_e, Ha. rewrite (word_of_unsigned _ _ Hv). exact Hu.
Qed.
Lemma u64_of_KWord_e : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "QA'Q?'SGyR0%211'8y8%511%311p051'QB'F&QF&R:r7r6(Q9(Q<r5r4%3221u8r3%73321%<4;:91'=&SI&Q>r8%221>%42K1%63D19r9%621?%82O1%:3H1=&R4&R=%12DH%3371Dp051p0:1p0B1pX2Q01pU:Q11pUBQ31pW0Q31pU@Q51pR0Q71pQ@Q@1").
Proof. intros E M b off e a z.
intros K Ha Hz. cbn [kentry_ok] in K. destruct K as (_ & F & Rd). unfold u64_at.
rewrite adenot_e, Ha in Rd. rewrite <- (word_of_unsigned _ _ Hz). exact Rd.
Qed.
Lemma rdn_of_bytes : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "R7'SGyR0%211'8y8%511%311p051'Fp014'6&R>zr1%3221&R=r2&RBr3%211%5241&RC+2+R0%3221%>251'<&R?r5%<11%32A1%52A1'=r8&SF%D27C%22Q31%411(1r7%115%32Q41%:3Q451p0<1pUNQ41'5%11Q9%Q<11&R8&R:r4%A2QB1%443=1H&C%Q51Q9%Q82K1%A11qV8Q?1&E(0%221Q0%84QCQH41%H2@1%O3@;1p0D1p0Q81p0QD1pU:QK1pVDQJ1pUFQL1pR0QO1").
Proof. intros M f.
induction n as [|n IH]; intros a Ha Hn H. reflexivity.
cbn [rdn seq map]. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. rewrite H0.
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1%bv : bv 64)) with 1.
unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity. }
rewrite (IH (a + 1)); try lia.
- rewrite Z.add_0_r. f_equal. f_equal. rewrite <- seq_shift, map_map. apply map_ext. intros k. f_equal. lia.
- intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply H. lia.
Qed.
Lemma u64_of_KZero_e : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "Q<'Q?'SGyR0%211'8y8%511%311p051'QB'F&QF&R:r5r4(Q;(Q<r3r2%3221(Q3+8%211%8241%=4<;:1'=&SI&Q>r6%221?%42L1%63E1=&R4&R=%12ADz%43821p061p0>1pU:M1pW0N1pU@Q01pR0Q21pQ@Q;1").
Proof. intros E M b off a.
intros K Ha. cbn [kentry_ok] in K. destruct K as [F Z0]. unfold flat, estart, elenZ in *. cbn [a_base a_off edenot] in *.
rewrite Ha in F, Z0. rewrite Z_to_bv_unsigned in F, Z0. change (bv_wrap 64 8) with 8 in F, Z0.
unfold u64_at. rewrite (rdn_of_bytes M (fun _ => Z_to_bv 8 0) 8 (a + off)); try lia.
- reflexivity.
- intros i Hi. apply Z0. simpl in Hi. lia.
Qed.
Lemma rdn_ext : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "QB'SGyR0%211'8y8%511%311p051'6'F'<&R>zr1%3221&R?&RBr3%211%4261%:261'=r5&SF&R=&SI%12I9r2%4221%62L1%811r6%113%<3K31p0>1pUNJ1'5%11Q0%Q311&R8&R:r4%3421?I%443E@J%G3621p0:1pU:Q<1pVDQ71pR2Q91pR0Q:1").
Proof. intros M M'.
induction n as [|n IH]; intros a H. reflexivity.
cbn [rdn]. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
replace (Z_to_bv 64 (bv_unsigned a)) with a in H0. 2:{ apply bv_eq. rewrite Z_to_bv_unsigned. symmetry; apply bv_wrap_bv_unsigned. }
rewrite H0. rewrite (IH (a + 1)%bv). reflexivity.
intros i Hi. pose proof (H (i + 1)) as Hi1.
assert (E1: forall m : word -> option byte, m (Z_to_bv 64 (bv_unsigned (a + 1)%bv + i)) = m (Z_to_bv 64 (bv_unsigned a + (i + 1)))).
{ intros m. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
replace (bv_unsigned (a + 1)%bv) with ((bv_unsigned a + 1) mod 2^64)%Z by (rewrite bv_add_unsigned; reflexivity).
unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z. rewrite Zplus_mod_idemp_l. f_equal. lia. }
rewrite !E1. apply Hi1. lia.
Qed.
Lemma u64_at_frame : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "QE'SGyR0%211'8y8%511%311p051'F&R>zr2%3221&R=r3+8%3221&RC+2+R0%3221%<251'<r1%?2>1&R?%123;%5231'=r7&SFr6%C21E%32Q01%511r8%113%93O31p0;1pUNO1&R4r5r4%33>21%43?=3p021p071p0J1p0Q41pWLQ91pU:Q:1pR2Q<1pR0Q=1").
Proof. intros M M' a v.
intros Ha Hb H Hu. unfold u64_at in *. rewrite <- Hu. apply rdn_ext. intros i Hi.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia. apply H. simpl in Hi. lia.
Qed.
Lemma defined_grows : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "H'SGyR0%211'8y8%511%311p051'F&R9r4r3%3221&R0r5r2%33251%43376p021p071pVD<1pU:=1pR2?1pR0@1").
Proof. intros M M' a n. intros G D i Hi. apply G. apply D. auto. Qed.
Lemma alu_add_lit : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "C'F'='SGyR0%211&M(J&SFr2%2261r1%4281%73631&R=%1264%82<1%?3<41pV8A1pU:B1").
Proof. intros a k. unfold alu64, alu. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Z.add_mod; [reflexivity|]. discriminate. Qed.
Lemma md_mul_lit : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "C'F'='SGyR0%211&N(K&SFr2%2261r1%4281%749631&RA%1264%82<1%?3<41pU@A1pU:B1").
Proof. intros a b. unfold mul_div. apply bv_eq. rewrite bv_mul_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Z.mul_mod; [reflexivity|discriminate]. Qed.
Lemma unsigned_lit : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "G'F'<&R>zr1%3221&R?&RC+2+R0%3221%5271%;271'=&SIyR0&SFr2%2231%5241%73D13p091pU:F1").
Proof. intros a. intros. rewrite Z_to_bv_unsigned. apply Z.mod_small. exact H. Qed.
Lemma writable_grows : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "H'SGyR0%211'8y8%511%311p051'F&R9r4r3%3221&R6r5r2%33251%43376p021p071pVD<1pU:=1pR2?1pR0@1").
Proof. intros M M' a n. intros G W d k Hd Hk. eapply store_ok_mono. exact G. apply W; auto. Qed.
Lemma u64_keep : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "QO'SGyR0%211'8y8%511%311p051'F&>'<&R>r5&SIr1%22>1%5241&R?r4%2241%:241%<11'=r7r2%211r8%113%63F31p081pX0L1zr3%F221&R=+8%22B1&RC+2+R0%3221%N251'?%92O8%Q121Er6%Q321Q2%5231&R4r:%2315Q6%332L6p021p061p0=1p0F1p0J1pWLQA1pU:QB1pUHQC1pV<QD1pR2QF1pR0QG1").
Proof. intros M M' lo hi a v.
intros HF Ha Hb Hd Hu. apply (u64_at_frame M M' a v Ha Hb). 2: exact Hu. intros i Hi. apply HF. rewrite unsigned_lit by lia. lia.
Qed.
Lemma u64_keep2 : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "R?'SGyR0%211'8y8%511%311p051'F&>'<&R>r7&SIr1%22>1%5241&R?r6%2241%:241%<11r2%:2F1%=261r5%9231%A231%C11'=r:r3%211r;%113%63M31p081p0@1pX0Q41z%M219&R=r4+8%3221&RC+2+R0%3221%Q6251'?%:2J8r9%Q:221r8%Q<21N%6231%@2Q7>%Q?214%Q@2Q?Q9%:221&R4r=%231QCQ=%332:QDp021p061p0;1p0C1p0M1p0Q01pWLQO1pU:R01pULR11pV@R21pUJR31pV>R41pR2R61pR0R71").
Proof. intros M M' lo1 hi1 lo2 hi2 a v.
intros HF Ha Hb Hd1 Hd2 Hu. apply (u64_at_frame M M' a v Ha Hb). 2: exact Hu. intros i Hi. apply HF; rewrite unsigned_lit by lia; lia.
Qed.
Lemma u8_at_frame : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "L'SGyR0%211'8y8%511%311p051'F'=r3&SFr2%22<1%411r4%113%83;31&R5r5%231:8%3326;p021p061pU@@1pU:A1pR2C1pR0D1").
Proof. intros M M' a b. unfold u8_at. cbn [rdn]. intros H Hu. rewrite H. exact Hu. Qed.
Lemma u8_keep : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "QN'SGyR0%211'8y8%511%311p051'F&>'<&R>r5&SIr1%22>1%5241&R?r4%2241%:241%<11'=r7r2%211r8%113%63F31p081pX0L1zr3%F221&RC+2+R0%3221%E261%M261'?&R=+1%22I1r6%Q2221%Q32Q2L%7221&R5r9%231Q6Q0%3327Q7p021p061p0?1p0I1pU@Q@1pU:QA1pUHQB1pV<QC1pR2QE1pR0QF1").
Proof. intros M M' lo hi a b. intros HF Ha Hd Hu. apply (u8_at_frame M M' a b). 2: exact Hu. apply HF. rewrite unsigned_lit by lia. lia. Qed.
Lemma u8_keep2 : ltac2:(TCodec.tc2 tcn__BigLinkGlueUb0 "R='SGyR0%211'8y8%511%311p051'F&>'<&R>r7&SIr1%22>1%5241&R?r6%2241%:241%<11r2%:2F1%=261r5%9231%A231%C11'=r:r3%211r;%113%63M31p081p0@1pX0Q41z%M219&RC+2+R0%3221%L2>1%Q4261'?&R=r4+1%3221r8%Q:221%Q;2Q:5%8221%82O6%Q>21Q=%Q?2Q8Q1%<221&R5r<%231Q<Q5%332QCQ=p021p061p0;1p0E1p0N1pU@QM1pU:QN1pULQO1pV@R01pUJR11pV>R21pR2R41pR0R51").
Proof. intros M M' lo1 hi1 lo2 hi2 a b. intros HF Ha Hd1 Hd2 Hu. apply (u8_at_frame M M' a b). 2: exact Hu. apply HF; rewrite unsigned_lit by lia; lia. Qed.
End BGU.
