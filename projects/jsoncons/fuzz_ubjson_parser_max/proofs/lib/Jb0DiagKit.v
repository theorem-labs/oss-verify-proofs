(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib L5Defs L5Kn L5KnA Jb0RegionPoisoned Jb0DiagChk.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0DiagKit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DiagKit.DK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1S"; "1Some"; "1app"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2and"; "2eq"; "2not"; "3add"; "4Z"]; ["0L"; "5store_ok"; "6bvmap"; "0M"; "0M'"; "0P"; "0R"; "0R'"; "7U"; "8keeps_but"; "9defined"; "9img_clear"; "9u32_at"; "9u64_at"; "9u8_at"; "9writable"]; [":zeros_at"; ";getr"; ";rdn"; "<callee_saved"; "<keeps_cs"; "=mem_grows"; ">loaded_segments"; "?In"; "@add"; "@le"; "@lt"; "@of_nat"; "@pow"; "0a"; "0a'"; "0b"]; ["0bs"; "0hi"; "0k"; "0l"; "0l1"; "0l2"; "0lo"; "0n"; "0n1"; "0n2"; "0r"; "AZ_to_bv"; "Abv"; "Abv_unsigned"; "0v"; "0w"]; ["0x"; "0z"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module DK.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)).
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "H&By5'QLyR0%211%5241'7';&Q9z&Hr2r1%3221%6251&Q:&Q<+2+R0%3221%5271%>271pS6@1pQ>B1"). Proof. intros R k. unfold U. pose proof (bv_unsigned_in_range _ (getr R (reg k))) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
Lemma U_of : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "Q9&By5'QLyR0%211%5241'7'?'<&Q1r3&QK&Q;r2%211%42>1%7261r1%72?1%;3?31';&Q9z%221:&Q:&Q<+2+R0%3221%52@1%:271&Hr5r4%3221%K3L1Ip061p0B1pT4O1pS6Q11pQ>Q31").
Proof. intros R k z. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
Lemma U_to : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "F&By5'QLyR0%211%5241'7'<&Q1r2&QK&Q;r1%211%42=1%7261&H%1285%82?1%<3?41pS6>1pQ>@1"). Proof. intros R k. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma pcw : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "A'?'QLyR0%211'<&QMr1%2251r2%53921&QKr3%22:1%93:15p051pT0<1pT4@1").
Proof. intros z w. intros <-. apply Z_to_bv_bv_unsigned. Qed.
Lemma rdn_ext_Z : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "QN'QLyR0%211'9y8%511%311p051'?'7&Q9zr2%3221&Q8r3&Q;%115%4231&Q<+2+R0%3221%=251';r5&QMr1%22K1%C241&Q:r4%@11%C281%4261%;261'<r7%11Jr8%11L%53Q331p071pT2Q91'6%11Q8%Q;11&Q2&Q6r6&QK%12QBJ%54431E%645@2F%B3821p0<1p0Q11p0Q<1pS6QA1pRLQC1pQ:QE1pQ8QF1").
Proof. intros M M' a k.
intros Ha Hk AG. destruct (Z.eq_dec (Z.of_nat k) 0) as [E|E]. { replace k with 0%nat by lia. reflexivity. }
apply rdn_ext; rewrite L5.unsigned_lit by lia; [lia | exact AG].
Qed.
Lemma u64_ext : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "QE'QLyR0%211'9y8%511%311pT251'?';&Q9r3&QMr1%22=1%5241&Q:&Q8+8%2281%4261%<261'<r5r2%211r6%113%63F31p081pT2L1z%F21Er4%A21@&Q<+2+R0%3221%M251&M&Q6r7%3421D:%4432BEp021p071p0?1p0B1pSNQ91pRLQ:1pQ:Q<1pQ8Q=1").
Proof. intros M M' a v. intros AG Ha Hb C. unfold L5.u64_at in *. rewrite <- C. apply rdn_ext_Z; [lia | cbn; lia | exact AG]. Qed.
Lemma u32_ext : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "QE'QLyR0%211'9y8%511%311pT251'?';&Q9r3&QMr1%22=1%5241&Q:&Q8+4%2281%4261%<261'<r5r2%211r6%113%63F31p081pT2L1z%F21Er4%A21@&Q<+2+R0%3221%M251&L&Q6r7%3421D:%4432BEp021p071p0?1p0B1pSNQ91pRLQ:1pQ:Q<1pQ8Q=1").
Proof. intros M M' a v. intros AG Ha Hb C. unfold L5.u32_at in *. rewrite <- C. apply rdn_ext_Z; [lia | cbn; lia | exact AG]. Qed.
Lemma u8_ext : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "QE'QLyR0%211'9y8%511%311pT251'?';&Q9r3&QMr1%22=1%5241&Q:&Q8+1%2281%4261%<261'<r5r2%211r6%113%63F31p081pT2L1z%F21Er4%A21@&Q<+2+R0%3221%M251&N&Q6r7%3421D:%4432BEp021p071p0?1p0B1pSNQ91pRLQ:1pQ:Q<1pQ8Q=1").
Proof. intros M M' a v. intros AG Ha Hb C. unfold L5.u8_at in *. rewrite <- C. apply rdn_ext_Z; [lia | cbn; lia | exact AG]. Qed.
Lemma rdn_xfer : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "R5'QLyR0%211'9y8%511%311p051'?'7'6%116';&Q9r4&QMr1%22@1%5241&Q:&Q8&Q;r3%211%42:1%6281%>281'<r6r2%211r7%113%63K31p081pT2Q11z%H21Gr5%B1I%D221&Q<+2+R0%3221%Q0251%Q;1Q3&Q2&Q6r8&QK%12QBG%54431>(2%12Q;Q8%L3931%62QGI%:4981M%52Q?D%Q03=21p051p0@1p0I1p0L1pS2QE1pS6QH1pRLQJ1pQ:QL1pQ8QM1").
Proof. intros M M' a k bs. intros AG Ha Hb C. rewrite <- C. apply rdn_ext_Z; assumption. Qed.
Lemma zeros_ext : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "QC'QLyR0%211'9y8%511%311pT251'?';&Q9r3&QMr1%22=1%5241&Q:&Q8r2%2281%4261%<261'<r5%116r6%118%53E31p071pT2K1z%E21Dr4%@21F&Q<+2+R0%3221%L251&Q0r7%231B9%332ACp021p061p0>1p0A1pS@Q71pRLQ81pQ:Q:1pQ8Q;1").
Proof. intros M M' a n. intros AG Ha Hb Z0 i Hi. rewrite AG; [apply Z0; exact Hi | rewrite L5.unsigned_lit by lia; lia]. Qed.
Lemma imgc_ext : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "Q@'QLyR0%211'9y8%511%311pT251'?';&Q9r3&QMr1%22=1%5241&Q:r2%2241%:241'<r5%115r6%117%53C31p071pT2I1z%C21B&Q<+2+R0%3221%H2G1&Kr7r4%332A1%433@Bp021p071p0=1p0@1pS4Q41pS>Q51pQ:Q71pQ8Q81").
Proof. intros M M' lo hi. intros AG Ha Hb Z0 i Hi. rewrite AG; [apply Z0; exact Hi | rewrite L5.unsigned_lit by lia; lia]. Qed.
Lemma defined_grows : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "H'QLyR0%211'9y8%511%311p051'?&Q5r4r3%3221&Jr5r2%33251%43376p021p071pS@<1pRL=1pQ:?1pQ8@1").
Proof. intros M M' a n. intros G D i Hi. apply G. apply D. exact Hi. Qed.
Lemma writable_grows : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "I'QLyR0%211'9y8%511%311p051'?&Q5r4r3%3221&O&Q6r5r2%443261%544387p021p081pS@=1pRL>1pQ:@1pQ8A1").
Proof. intros M M' a n. intros G W d k Hd Hk. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.
Lemma pw_ext : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "Q='QLyR0%211'9y8%511%311p051'?!p021r3&QMr1%22=1%411'<r5r2%211r6%113%63@31p081pT2F1r4%11<r7%11:(2%12I5%?3I31p061pT2O1%A1D%62NB%D3N81p031pT2Q41p061p0@1pS0Q41pQ<Q01pQ:Q41pQ8Q51").
Proof. intros M M' P b. intros AG H x Hx. rewrite AG by exact Hx. apply H. exact Hx. Qed.
Lemma store_ok_of_writable : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "Q3'QLyR0%211'9y8%511%311p051'?'7&O&Q6r4r3r2%544321'<&Q;%114%33;16'4&Ar6&QKr5%22H1%54?41=(:%<3821p0:1p0?1pS6F1pS@H1pRLI1pQ8K1").
Proof. intros M a n k. intros W E. specialize (W 0 k ltac:(lia) ltac:(lia)). rewrite Z.add_0_r in W. exact W. Qed.
Lemma store_ok_of_writable_sub : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "Q:'QLyR0%211'9y8%511%311p051'?'7&O&Q6r5r4r3%544321&Q9%1253&Q8&Q;%116%3281r6%521;%8231'<'4&Ar8&QK%12MB%44D31B(:%83721p0:1p0B1p0E1pS6L1pRNN1pS@O1pRLQ01pQ8Q21").
Proof. intros M a n a' k. intros W H1 H2. specialize (W (a' - a) k ltac:(lia) ltac:(lia)). replace (a + (a' - a)) with a' in W by lia. exact W. Qed.
Lemma regk : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "E'7'QLy5%211'<'?&QMr1%2261&Q;r2%211%83741&QKr3%611%32>1%=3>17p061pSF@1pS6D1").
Proof. intros k r. intros H. rewrite <- H. apply Z_to_bv_bv_unsigned. Qed.
Lemma getr_reg : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "N&By5'QLyR0%211%5241'7%516'<'?&QMr1%22;1&Q;r2%211%83741&Q1r4&QKr3%811%32E1%6251%726:%A3E21p0:1pSFD1pS6F1pQ>H1").
Proof. intros R k r. intros H. rewrite (regk k r H). reflexivity. Qed.
Lemma wlit : ltac2:(TCodec.tc2 tcn__Jb0DiagKit ";'QLyR0%211'<r1&QK&QM%1263%3271%63751pT081").
Proof. intros w. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Section SE.
Local Abbreviation SEC_T_keeps_cs_reg := (ltac2:(TCodec.tc2 tcn__Jb0DiagKit "R0&By5'QLyR0%211%5241'7&Q4r3r2%3221&Q7(5u1u2u3u4u8u9uBuCuDuEuFuGuHuIuJuK(8%11H%C3I31%D3J51%E3K71%F3L91%G3M;1%H3N=1%I3O?1%J3Q0A1%K3Q1C1%L3Q2E1%M3Q3G1%N3Q4I1%O3Q5K1%Q03Q6M1%Q13Q7O1%Q23Q8Q11%Q43Q9Q61'<&Q1r4&QK&Q;%11Q=%32QE1%6251r5%8213%:3QF31p0<1p0QB1pS6QG1pQ@QI1pQ>QJ1")) (only parsing).
Variable R : ltac:(sec_ty2 constr:(SEC_T_keeps_cs_reg) 0%nat 0%nat).
Variable R' : ltac:(sec_ty2 constr:(SEC_T_keeps_cs_reg) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_keeps_cs_reg) 2%nat 0%nat).
Lemma keeps_cs_reg : ltac:(sec_stmt2 constr:(SEC_T_keeps_cs_reg) 3%nat 0%nat).
Proof.
intros K Hk. cbn in Hk.
repeat (destruct Hk as [<-|Hk]; [ match goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?j)) = _ => let z := eval vm_compute in (Z.of_nat j) in
rewrite !(getr_reg _ j (@BV 5 z I) eq_refl) end; apply K; cbv; tauto |]). destruct Hk.
Qed.
End SE.
Lemma keeps_but_reg : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "Q@'6'QLy5%211%411&ByR0%611%3261'7&Ir5r4r3%43321'<'?&QMr2%22A1&Q;%118%73631&Q7&Q3%23F<1&=r8%53I@1%311&Q1r7&QKr6%>11%32Q11%6251%72:2%G3O21p0:1p0?1p0C1p0L1pSFQ81pS6Q31pQ@Q51pQ>Q61pQ2Q;1").
Proof. intros L R R' k r. intros K E Hc Hn. rewrite !(getr_reg _ k r E). apply K; assumption. Qed.
Lemma rdn_img : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "QH'QLyR0%211'9y8%511%311p051'?'7&Kr5r4r3%43321&Q9z%2216&Q<+2+R0%3221%72;1r7%921=&Q8r6&Q;%11A%4231%?217'<'6%11L%O11&Q2&Q6r:&QK%12Q6@%54431>(0%11Q5q0Q91%94815B%>3;51p0@1p0G1p0J1p0Q01p0Q41pS6Q:1pRLQ<1pS4Q=1pS>Q>1pQ8Q@1").
Proof. intros M lo hi a k.
intros IC Hlo Hhi Ha Hk. destruct (Z.eq_dec (Z.of_nat k) 0) as [E|E]. { replace k with 0%nat by lia. reflexivity. }
apply rdn_ext; rewrite L5.unsigned_lit by lia; [lia|]. intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply IC. lia.
Qed.
Lemma u64_of_zeros : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "Q3'QLyR0%211'9y8%511%311p051'?&Q0r2r1+8%43321&Q9z%2216&Q8r3%2217&Q<+2+R0%3221%:251&M&Q6r5r4%44321>p061p0?1p0C1pRLI1pQ8K1").
Proof. intros M a.
intros Z8 Ha Hn. unfold L5.u64_at. change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0 : byte) 8).
apply Jb0DiagChk.rdn_zeros. rewrite L5.unsigned_lit by lia. cbn. lia.
intros i Hi. rewrite L5.unsigned_lit by lia. apply Z8. cbn in Hi. lia.
Qed.
Lemma rdn_cons : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "R5'QLyR0%211'9y8%511%311p051'?'7'6%116&Q9zr4%3221&Q8r5+1%3221&Q;r3%211%7241&Q<+2+R0%3221%@251'<%K1C&Q2&Q6r7&QKr6%22Q31u1%746521(2(5(8%11Q5%33Q6J1%52Q11%@3?71r8%O2>M%>2Q?1%B4A31Q0%;2Q7Q4%F3E21r9%C2QD7(1%11D%I4H431%A3QDHQ8%C2Q?1%N3M31p091p0@1p0Q21p0Q@1pS8QE1pS6QH1pS0QM1pRLQK1pQ8QM1").
Proof. intros M a b k l.
intros Ha Hk R1 Rk. change (Datatypes.S k) with (1 + k)%nat. change (b :: l) with ([b] ++ l). apply SeqExec.rdn_app; [exact R1|].
replace ((Z_to_bv 64 a + nat_to_word 1)%bv) with (Z_to_bv 64 (a + 1)); [exact Rk|].
apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma rdn_app_Z : ltac2:(TCodec.tc2 tcn__Jb0DiagKit "R2'QLyR0%211'9y8%511%311p051'?'7'6%116&Q9zr5%3221&Q8r6&Q;%115%4231r4%411%7231&Q<+2+R0%3221%@251'<%K1C&Q2&Q6r8&QKr7%22Q31%64541D(2%12LB%;3:31r9%H17%K2:1%:2Q;1%>4=41L%A3@17r:%>2Q?7&>%12A?%D4C431&3%13Q@Q4Q7%@2Q;1%J3I41p0:1p0A1p0N1p0Q<1pS<QA1pS:QB1pSDQE1pSBQF1pRLQH1pQ8QJ1").
Proof. intros M a n1 n2 l1 l2.
intros Ha Hk R1 R2. apply SeqExec.rdn_app; [exact R1|].
replace ((Z_to_bv 64 a + nat_to_word n1)%bv) with (Z_to_bv 64 (a + Z.of_nat n1)); [exact R2|].
apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
Qed.
End DK.
Ltac dk_feed P tac :=
lazymatch type of P with
| ?A -> _ =>
let H := fresh "SC" in
first [ assert (H : A) by tac | fail 1 "feed: cannot prove premise" A ];
specialize (P H); clear H; dk_feed P tac
| _ => idtac
end.
Ltac dk_gmem :=
lazymatch goal with
| |- L5.u64_at ?sg ?M ?a ?v => match goal with H : L5.u64_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
| |- L5.u32_at ?sg ?M ?a ?v => match goal with H : L5.u32_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
| |- L5.u8_at ?sg ?M ?a ?v => match goal with H : L5.u8_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
| |- L5.defined ?M ?a ?n => match goal with H : L5.defined M ?b ?m |- _ => apply (L5.defined_sub M b m a n H); clear; lia end
| |- L5.writable ?sg ?M ?a ?n => match goal with H : L5.writable sg M ?b ?m |- _ => apply (L5.writable_sub sg M b m a n H); clear; lia end
| |- L5KA.zeros_at ?M ?a ?n => match goal with H : L5KA.zeros_at M ?b ?m |- _ => apply (L5KA.zeros_at_sub M b m a n H); clear; lia end
| |- L5.img_clear ?M _ _ => match goal with H : L5.img_clear M _ _ |- _ => exact H end
end.
Ltac dk_fpreg_in H :=
repeat match type of H with context [getr ?R (Z_to_bv 5 (Z.of_nat ?k))] =>
let z := eval vm_compute in (Z.of_nat k) in rewrite (DK.getr_reg R k (@BV 5 z I) eq_refl) in H end.
Ltac dk_fpreg :=
repeat match goal with |- context [getr ?R (Z_to_bv 5 (Z.of_nat ?k))] =>
let z := eval vm_compute in (Z.of_nat k) in rewrite (DK.getr_reg R k (@BV 5 z I) eq_refl) end.
Ltac dk_kb K :=
lazymatch goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
let z := eval vm_compute in (Z.of_nat k) in
apply (DK.keeps_but_reg _ _ _ k (@BV 5 z I) K eq_refl); [cbv; tauto | cbv; intuition discriminate] end.
Ltac dk_arith_shape :=
lazymatch goal with
| |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ <= _ <= _)%Z => idtac | |- (_ <= _ < _)%Z => idtac | |- (_ < _ <= _)%Z => idtac | |- (_ < _ < _)%Z => idtac
| |- @eq Z _ _ => idtac | |- (_ \/ _) => idtac | |- (~ _)%type => idtac | |- (_ /\ _) => idtac
| |- le _ _ => idtac | |- lt _ _ => idtac | |- @eq nat _ _ => idtac
end.
Ltac dk_arith_goal := first [ dk_arith_shape | red; dk_arith_shape ].
Ltac dk_norm H :=
lazymatch type of H with
| L5.u64_at _ _ ?a ?v => try (progress (ring_simplify a in H)); try (lazymatch type of H with L5.u64_at _ _ _ ?v' => progress (ring_simplify v' in H) end)
| L5.u32_at _ _ ?a ?v => try (progress (ring_simplify a in H))
| L5.u8_at _ _ ?a ?v => try (progress (ring_simplify a in H))
| getr _ _ = Z_to_bv 64 ?v => try (progress (ring_simplify v in H))
| _ => idtac
end.
Ltac dk_split H :=
lazymatch type of H with
| _ /\ _ => let A := fresh "Q" in let B := fresh "Q" in destruct H as [A B]; dk_norm A; dk_split B
| _ => dk_norm H
end.
Tactic Notation "dk_open" hyp(P) "as" ident(fx) ident(R) ident(M) ident(MG) ident(FR) ident(FZ) ident(MS) ident(KS) :=
let T := fresh "T" in
destruct P as (fx & R & M & MG & FR & FZ & (MS & KS & T)); dk_split T.
Ltac dk_exactv H tac :=
first [ exact H
| lazymatch goal with
| |- L5.u64_at _ _ _ ?v => lazymatch type of H with L5.u64_at _ _ _ ?vH => replace v with vH by tac; exact H end
| |- L5.u32_at _ _ _ ?v => lazymatch type of H with L5.u32_at _ _ _ ?vH => replace v with vH by tac; exact H end
| |- L5.u8_at _ _ _ ?v => lazymatch type of H with L5.u8_at _ _ _ ?vH => replace v with vH by tac; exact H end
end ].
Ltac dk_cell_with EXT tac H M Ms a v :=
match goal with
| AG : forall x : word, _ -> M x = Ms x |- _ => apply (EXT Ms M a v); [intros ? ?; apply AG; tac | tac | tac | dk_exactv H tac]
| AG : forall x : word, _ -> _ -> M x = Ms x |- _ => apply (EXT Ms M a v); [intros ? ?; apply AG; tac | tac | tac | dk_exactv H tac]
| AG : forall x : word, _ -> _ -> _ -> M x = Ms x |- _ => apply (EXT Ms M a v); [intros ? ?; apply AG; tac | tac | tac | dk_exactv H tac]
end.
Ltac dk_cell tac :=
lazymatch goal with
| |- L5.u64_at ?sg ?M ?a ?v =>
try (progress (ring_simplify a)); try (lazymatch goal with |- L5.u64_at _ _ _ ?v1 => progress (ring_simplify v1) end);
lazymatch goal with |- L5.u64_at _ _ ?a' ?v' =>
match goal with
| H : L5.u64_at sg M a' _ |- _ => dk_exactv H tac
| H : L5.u64_at sg ?Ms a' _ |- _ => dk_cell_with DK.u64_ext tac H M Ms a' v'
end end
| |- L5.u32_at ?sg ?M ?a ?v =>
try (progress (ring_simplify a));
lazymatch goal with |- L5.u32_at _ _ ?a' ?v' =>
match goal with
| H : L5.u32_at sg M a' _ |- _ => exact H
| H : L5.u32_at sg ?Ms a' _ |- _ => dk_cell_with DK.u32_ext tac H M Ms a' v'
end end
| |- L5.u8_at ?sg ?M ?a ?v =>
try (progress (ring_simplify a));
lazymatch goal with |- L5.u8_at _ _ ?a' ?v' =>
match goal with
| H : L5.u8_at sg M a' _ |- _ => exact H
| H : L5.u8_at sg ?Ms a' _ |- _ => dk_cell_with DK.u8_ext tac H M Ms a' v'
end end
end.
Ltac dk_greg :=
lazymatch goal with |- getr ?R ?x = ?rhs =>
match goal with H : getr R x = ?rhs' |- _ => first [ exact H | (rewrite H; f_equal; lia) ] end end.
Ltac dk_kept KS :=
lazymatch goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
rewrite (KS k) by (apply L5K.in_b; vm_compute; reflexivity) end.
Ltac dk_xf Ms AG tac :=
first [ dk_gmem
| (eapply (DK.u64_ext Ms); [intros ? ?; apply AG; tac | tac | tac | dk_gmem])
| (eapply (DK.u32_ext Ms); [intros ? ?; apply AG; tac | tac | tac | dk_gmem])
| (eapply (DK.u8_ext Ms); [intros ? ?; apply AG; tac | tac | tac | dk_gmem]) ].
Ltac dk_rk :=
first [ dk_greg
| match goal with K : forall x, In x _ -> getr ?Rb (Z_to_bv 5 (Z.of_nat x)) = getr _ (Z_to_bv 5 (Z.of_nat x)) |- getr ?Rb' (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
constr_eq Rb Rb'; rewrite (K k) by (first [apply L5K.in_b; vm_compute; reflexivity | cbn; tauto]); dk_rk end ].
Ltac dk_qlia := solve [L5FastLia.prune_arith; L5FastLia.lia_ne].
Ltac dk_export M tac :=
repeat match goal with
| H : L5.u64_at ?sg ?Ms ?a ?v |- _ =>
lazymatch Ms with M => fail | _ => idtac end;
first [ assert (L5.u64_at sg M a v) by (dk_cell_with DK.u64_ext tac H M Ms a v) | idtac ]; clear H
| H : L5.u32_at ?sg ?Ms ?a ?v |- _ =>
lazymatch Ms with M => fail | _ => idtac end;
first [ assert (L5.u32_at sg M a v) by (dk_cell_with DK.u32_ext tac H M Ms a v) | idtac ]; clear H
| H : L5.u8_at ?sg ?Ms ?a ?v |- _ =>
lazymatch Ms with M => fail | _ => idtac end;
first [ assert (L5.u8_at sg M a v) by (dk_cell_with DK.u8_ext tac H M Ms a v) | idtac ]; clear H
end.
