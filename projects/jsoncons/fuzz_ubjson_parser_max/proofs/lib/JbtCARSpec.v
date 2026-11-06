(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtAllocG JbtPoison JbtInitCache ArtRuns ArtRunsMem JbtClassId JbtCachePop JbtCombAlloc JbtCombAllocHit JbtRefill3 JbtPopulate1
JbtCls JbtFp JbtClsPop3 JbtClsRep JbtClsGfa2 JbtClsRefill JbtCellEx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtCARSpec () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCARSpec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCARSpec.Spec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInitCache."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3sub"]; ["4le"; "4lt"; "5nth"; "6Z"; "0EVOK"; "0GR"; "0HI"; "7machine_state"; "8bvmap"; "0M"; "0M'"; "0MX"; "0Q"; "9Wn"; "9apart"; "9cell"]; ["9wr"; ":aev"; ":aruns"; ";ret_ok"; "=art_ca_rspec"; "<art_ca_fp"; "<art_ca_pre"; "<art_cls_pop"; ">art_cache_rep"; ">art_cls"; ">art_cls_ok"; ">art_cls_rep"; ">art_pc_hdr"; ">art_refill_fp"; ">cl_cache"; ">cl_free"]; ["?art_agree"; "?art_gap"; "@art_ic_size"; "Agetr"; "Amkst"; "Bmem_grows"; "Cloaded_segments"; "DIn"; "Dlast"; "Dremovelast"; "Eadd"; "Ele"; "Elt"; "Emul"; "Eof_nat"; "Epow"]; ["Esub"; "0W"; "0b"; "0c"; "0ca"; "0cache"; "0cl"; "0clp"; "0cnt"; "0d"; "0fx"; "0j"; "0km"; "0l"; "0logE"; "0qs"]; ["0r"; "0rP"; "0raw"; "0regs"; "0regs'"; "0res"; "0ris"; "0rom"; "0sp"; "0spb"; "0st"; "FBV"; "FZ_to_bv"; "Fbv"; "Fbv_unsigned"; "0t"]; ["0v"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_ca_pre (c : Z) (cl : art_cls) : art_cls := match cl_cache cl with [] => art_cls_refill c cl | _ :: _ => cl end.
Definition art_ca_events (spb c : Z) (cl : art_cls) : list aev := match cl_cache cl with [] => art_refill_events spb c cl | _ :: _ => [] end.
Definition art_cls_pop (cl : art_cls) : art_cls := CLS (removelast (cl_cache cl)) (cl_free cl) (cl_au cl) (cl_mu cl) (cl_mfa cl) (cl_na cl) (cl_nfr cl).
Definition art_ca_cptr (c : Z) (cl : art_cls) : Z := last (cl_cache (art_ca_pre c cl)) 0.
Definition art_ca_result (spb c : Z) (cl : art_cls) : Z := spb + c * 2 ^ 32 + art_ca_cptr c cl * 16.
Definition art_ca_fp (sp t spb ris qs c km : Z) (x : Z) : Prop :=
(sp - 48 <= x < sp) \/ art_refill_fp (sp - 48) t spb ris qs c km x \/ (t + 208 + 2576 <= x < t + 208 + 2584).
Lemma art_removelast_length : ltac2:(TCodec.tc2 tcn__JbtCARSpec "G'3'C%211&>'<r1(5%116%43631%611'4&2&QIr2%22=1%42>1&?%62@4u1%3221%@3:51p0<1pTLD1").
Proof. intros l H. rewrite removelast_firstn_len. rewrite length_firstn. lia. Qed.
Lemma art_removelast_nth : ltac2:(TCodec.tc2 tcn__JbtCARSpec "I'3'C%211'4&Ar1&?&2r2%2281u1%5221%8271'<&B&QIr3%22@1z%54B;21%64C<42%83D21p0:1pTHD1pTLF1").
Proof. intros l j Hj. rewrite removelast_firstn_len, nth_firstn. replace (j <? Nat.pred (length l))%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. Qed.
Lemma art_last_nth : ltac2:(TCodec.tc2 tcn__JbtCARSpec "A'3'C%211'<&QHr1z%33621&B&?&2%12:6u1%4221%64=198%<3>81pTL>1").
Proof.
induction l as [|a l IH]; [reflexivity|]. destruct l as [|b l]; [reflexivity|].
change (last (a :: b :: l) 0) with (last (b :: l) 0). rewrite IH. cbn [length]. rewrite !Nat.sub_succ, !Nat.sub_0_r. reflexivity.
Qed.
Lemma art_cls_ok_pop : ltac2:(TCodec.tc2 tcn__JbtCARSpec "I'C'Q9&Q:r2r1%3221&>'<'3%119&Q>%118(5%11=%73531%911r4&Q7r3%211%B241p061p0A1pT>F1pT8H1").
Proof.
intros c cl OK Hne.
destruct OK as (Hlc & Hau & Hrem0 & Hmu & Hau' & Hmu3 & Hmfa & Hmfa' & Hnf4 & Hfor & Hnd).
unfold art_cls_ok, art_cls_pop. cbn [cl_cache cl_free cl_au cl_mu cl_mfa].
assert (E : cl_cache cl = removelast (cl_cache cl) ++ [last (cl_cache cl) 0]) by (apply app_removelast_last; exact Hne).
split; [rewrite art_removelast_length by exact Hne; lia|]. split; [exact Hau|]. split; [exact Hrem0|]. split; [exact Hmu|]. split; [exact Hau'|]. split; [exact Hmu3|].
split; [exact Hmfa|]. split; [exact Hmfa'|]. split; [exact Hnf4|].
rewrite E in Hfor, Hnd. rewrite <- app_assoc in Hfor, Hnd.
split.
- apply Forall_app in Hfor. destruct Hfor as [F1 F2]. apply Forall_app in F2. destruct F2 as [_ F3]. apply Forall_app. split; assumption.
- apply NoDup_ListNoDup. apply NoDup_ListNoDup in Hnd. cbn [app] in Hnd. eapply NoDup_remove_1. exact Hnd.
Qed.
Lemma art_ca_pre_cache_ne : ltac2:(TCodec.tc2 tcn__JbtCARSpec "N'C'Q9';&QK+1r2%3221+N%5231%7231&Q:r3%2217&>'<'3%11@&Q>&Q6r4%2219%411(5%11G%:3831%<11p0>1p0B1pT>K1pT8M1").
Proof.
intros c cl Hc OK. unfold art_ca_pre. destruct (cl_cache cl) eqn:E; [|rewrite E; discriminate].
rewrite art_cls_refill_eq. cbn [art_cls_take cl_cache]. pose proof (art_pre_take_enough c cl Hc OK) as Hen.
destruct (art_refill_need c Hc) as (_ & Hn). intros H. apply (f_equal (@length Z)) in H. rewrite length_skipn in H. cbn in H. lia.
Qed.
Lemma art_cache_rep_tr : ltac2:(TCodec.tc2 tcn__JbtCARSpec "R;'3'8'C%2211%411%513'RMyR0%211'6y8%511%311p051&QKzr5%3221&QL&QJr6+TP0%3221&QO+2+R0%3221%9251';+1%@21:+O%B2<1%5231'@&2%12Q2@u@%4221&Q@r:%231EI&QAr;&QM+R@r9%3221%M281+4%83721r<%827<%Q22:1+@%Q4221%>351O&Q8%147?B<r=%3419A>p031p061p0=1p0G1p0K1p0Q11p0Q81p0QC1pQFQH1pQDQI1pT<R21pT8R61pT:R71pT4R61").
Proof.
intros W ca c cache M M' Hca Hca' Hc Hl A G0 G16 [C0 CW]. split.
- apply (art_cell_tr W M M'); [exact A|exact G0|lia|cbn; lia|exact C0].
- intros j Hj. apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact G16|lia|cbn; lia]|lia|cbn; lia|exact (CW j Hj)].
Qed.
Lemma art_pc_hdr_tr : ltac2:(TCodec.tc2 tcn__JbtCARSpec "R4'3'8'C%2211%411'0'RMyR0%211'6y8%511%311p051&QKzr4%3221&QL&QJr5+TP0%3221&QO+2+R0%3221%9251&Q@r7r3%332?1';+1r1%E221+O%G231%6231&QAr:r9&QM+R@r2%3221%K251+4%M221+<%;3:21p0=1pT8QB1&Q<r8r6%332K1%43@32p021p071p0M1p0Q21p0Q=1pQFQB1pQDQC1pT6QL1pT:R01pT4QO1").
Proof.
intros W ca b M M' Hca Hca' A G PH c Hc. destruct (PH c Hc) as [P1 P2]. split.
- apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact (G c Hc)|lia|cbn; lia]|lia|cbn; lia|exact P1].
- apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact (G c Hc)|lia|cbn; lia]|lia|cbn; lia|exact P2].
Qed.
Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.
Definition art_ca_rspec : Prop :=
forall (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M rom : word -> option byte) (raw : word)
(sp HI t ctx tp key tsd spb ris qs s km : Z) (inited : bool) (cl : art_cls),
let c := AsanTab.class_id s in
getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp ->
getr regs 10 = Z_to_bv 64 1283032 -> getr regs 11 = Z_to_bv 64 (t + 208) -> getr regs 12 = Z_to_bv 64 s -> getr regs 13 = Z_to_bv 64 8 ->
1 <= s <= 65536 -> s mod 8 = 0 -> HI <= sp - 720 -> sp < 2 ^ 47 -> art_geo HI t ctx tp tsd spb ris qs ->
wrA M (sp - 720) 720 -> wrA M t 4096 ->
art_prim_consts spb ris M -> art_layout M -> art_tsd M tp key tsd ctx t ->
art_pc_hdr (t + 208) inited M -> art_cls_rep (t + 208) spb ris c cl M -> art_cls_ok c cl -> (cl_cache cl <> [] -> inited = true) -> cl_mu cl = 262144 * km ->
(cl_cache cl = [] -> art_cls_needs_populate c cl = true ->
cl_mu cl + 262144 <= 3758096384
/\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912
/\ wrA M (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km) 32768
/\ wrA M (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048) 67108864) ->
art_evok_list EVOK log (art_ca_events spb c cl) ->
(forall regs' (M' : word -> option byte),
getr regs' 10 = Z_to_bv 64 (art_ca_result spb c cl) -> getr regs' 2 = Z_to_bv 64 sp -> getr regs' 1 = raw ->
(forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
mem_grows M M' ->
(forall x : word, ~ art_ca_fp sp t spb ris qs c km (U x) -> M' x = M x) ->
art_pc_hdr (t + 208) true M' -> art_cls_rep (t + 208) spb ris c (art_cls_pop (art_ca_pre c cl)) M' -> art_cls_ok c (art_cls_pop (art_ca_pre c cl)) ->
art_cptr_ok (AsanTab.class_size c) (cl_au (art_ca_pre c cl)) (art_ca_cptr c cl) ->
(cl_cache cl = [] -> art_cls_needs_populate c cl = true ->
forall j, 0 <= j < 32768 -> cellA M' (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km + j) 1 250) ->
Q (log ++ art_ca_events spb c cl) (mkst regs' raw M' rom)) ->
aruns ASEGS EVOK GR Q log (mkst regs (0x5660c : word) M rom).
Section SE.
Local Abbreviation SEC_T_art_ca_finish := (ltac2:(TCodec.tc2 tcn__JbtCARSpec "\5'3'Q1%211'G!p021p041&Hy5'RMyR0%211%5241'6y8%611%311p061'C'Q9&QJr9+V@%3221&QN&2&Q>r2%211%42;1%611&Q3r>%211';&QK+1r8%3221+N%5231%7231&R0r?+f@%3221%;2>1&QLr@&QO+2+Q?%3221%6251'<&QM+RPP0r<%3221%53Q9K1+`PQoooPP0%J21B+Q5%>2=1%Q<2@1%;3Q?F1+TP0%Q?2C1rC%Q2221%Q3242rD%QD216rE%Q7221&N%QH2=:%244;61&>%R?1QM%QF1Q@(5%11R0%M3431%611'@%QL1Q;%QN2R51u@%4221+4&Q?%11Q<%R42R;1%R611%Q8251+M%Q@2Q?1%QO231&QErOrN%3221&Q5rMrKrJrIrHrGrF&RNr1%22S71%;8:9876541%Q511rQ1%11RJrQ2%11RL%R23S831p061pV4S?1&Q<rB(9rQ0%43321&Q;%16QMHGEQJ=&O&QF+8%RK2Q11u8%H2SM9%655B321rQ3+@%S12=1&QCrQ6(RK(:%23T8<1%5241%Q32T81%A5@:8=1rQ4+H%S<2Q21rQ7+9%;3TA1:%>231%Q<2TA1%J5I86F1rQ5+Q0%SE2Q91rQ8+B%D3TJ1C%G231%QE2TJ1%Q35Q286O1+Q8%SM2N1rQ9+C%L3U21K%O231%QM2U21%Q;5Q:Q06Q71+Q@%T52K1rQ:+D%Q43U:1Q3%Q7231%R52U:1%QC5QBN6Q?1+=%Q93U?1Q8%Q<281&RL%12U@QF%T53U@31rQ;%Q?3UET;Q>%QB221%TE2QBA%72UF1%T;3UF31rQ<+:%QF3UL1QE%QI231%=2ULS1%TA3UL21%UO1V0&QG(1+3%QN3V41QM%QO3V5SCQN+E%R13V71R0+F%R33V91R2+G%R53V;1R4%R63V<QOR5+I%R83V>1R7+J%R:3V@1R9+K%R<3VB1R;%T:1C%B3D21%C3E51%D3F81%E3G;1%F3H=1%G3I@1%H3JC1%I3KF1%J3LH1%L3MSE1rQ?%RK21V<rQ@%RM21V>%UD3VO31p061pV4Q41%S12VBQ9%QE2W4SH%UI3W421r3%S521QD%QI2W8Q@%UM3W821r4%S73W=VAS6%S:221rQ>%V23W=21%Q?3QAR7G%Q@3QBR@1%QA3QCRI1%QB3QDS31%QC3QES=1%QD3QFQA1%QE3QGQC1%QG3QHT@1r7%SF21W7rQF%SH21W9%V?3WJ31p061pU2QO1rQCr5%U7221rQArQ=%U682Q7F1R;RARMTL%V011%W:1WD%=1WE%VK3X121p041pV4X81rQD%UB21D&Q@'8%12X6X6(7+R@%W421RI%X82T51%44X;X;1V3+R`@%X;2T81%74X>X>1TL%V@19%RH3:21%RI3;61rQE%?321X0%U;3T6U9XA&Q7%11SHr:%U:6T2OR2QC21rQMrQL&QDvR:r;rQG%453WHQ>21%7261p091p0>1p0@1p0Q11p0Q41p0Q>1p0QB1p0R21p0R81p0R=1pQFY<1pU:YB1'Q2vDvErQB+ZioL%UF3YJ1UE/01YJ&Mu4%XA2Q>UD%YE2W51%Y02W5Y6%544QO21%YH2W8Q>&QB%11UJ%YK2VI1%:4V:541%Q45Q3S;<1T?%C7V?BAQ4@R71p0E1p0S81p0T>1p0TE1p0TL1p0U31p0U<1p0UE1p0UO1p0V91p0VE1p0VM1p0W01p0W61p0WK1p0X01p0X:1p0X@1p0XH1p0XL1p0Y11p0Y31p0Y81p0Y=1p0Y@1p0YG1p0YO1p0Z51p0Z>1tTBZNZB1tT:ZOZJ1pT@ZO1pU<[11pUF[21pTJ[31pT8[41pU0[51pU>[61pUD[71pV0[81pQ>[91pUB[:1pU6[B1pU@[=1pQH[>1pQD[?1pU4[E1pU8[F1pTN\11pQJ[N1")) (only parsing).
Variable Q : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 0%nat 0%nat).
Variable logE : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 2%nat 0%nat).
Variable rP : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 4%nat 0%nat).
Variable MX : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 5%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 6%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 7%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 8%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 9%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 10%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 11%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 12%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 13%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 14%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 15%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 16%nat 0%nat).
Variable res : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 17%nat 0%nat).
Variable clp : ltac:(sec_ty2 constr:(SEC_T_art_ca_finish) 18%nat 0%nat).
Lemma art_ca_finish : ltac:(sec_stmt2 constr:(SEC_T_art_ca_finish) 19%nat 0%nat).
Proof using Type Q logE regs rP M MX rom raw sp HI t spb ris qs c km st res clp.
intros ca cnt
Hret Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Hne Hl16 Hnf GX AXf PH CR F1 F8 F9 F18 F19 F20 P13 P2 P10 KP K.
assert (Eca : ca = t + 208) by reflexivity.
pose proof Atk as Xk. unfold apart in Xk.
assert (Hcnt : 1 <= cnt <= 16). { unfold cnt. destruct (cl_cache clp); [contradiction|]. cbn [length] in *. lia. }
set (M2 := Wn 8 (Wn 4 MX (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + art_ic_size c)).
assert (A2 : art_agree [(ca + 80 * c, 4); (ca + 2576, 8)] MX M2). { unfold M2. eapply art_agree_sub; [zagree|]. zsub. }
assert (G2 : mem_grows MX M2) by (unfold M2; zgrows).
assert (TF : forall a v, sp - 48 <= a -> a + 8 <= sp -> cellA MX a 8 v -> cellA M2 a 8 v).
{ intros a v Ha Ha' C. apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|exact C]. clear - Ha Ha' Eca HHI Hsp' Ht Ht' Hc. zarith_t. }
destruct (art_cache_pop_tail8 rP M2 rom (sp - 48) raw (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))
P13 P2 ltac:(lia) ltac:(lia)
ltac:(replace (sp - 48 + 40) with (sp - 8) by lia; apply TF; [lia|lia|exact F1]) Hret
ltac:(replace (sp - 48 + 32) with (sp - 16) by lia; apply TF; [lia|lia|exact F8])
ltac:(replace (sp - 48 + 24) with (sp - 24) by lia; apply TF; [lia|lia|exact F9])
ltac:(replace (sp - 48 + 16) with (sp - 32) by lia; apply TF; [lia|lia|exact F18])
ltac:(replace (sp - 48 + 8) with (sp - 40) by lia; apply TF; [lia|lia|exact F19])
ltac:(apply TF; [lia|lia|exact F20]))
as (rT & RUNT & T10 & T2 & T1 & T8 & T9 & T18 & T19 & T20 & KT).
eapply ar_steps; [exact RUNT|]. apply ar_done.
destruct CR as [[C0 CW] RR].
apply (K rT M2).
- rewrite T10. exact P10.
- rewrite T2. f_equal. lia.
- exact T1.
- intros x Hx. cbn [In] in Hx.
destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
first [ rewrite T8; apply Z_to_bv_bv_unsigned | rewrite T9; apply Z_to_bv_bv_unsigned | rewrite T18; apply Z_to_bv_bv_unsigned
| rewrite T19; apply Z_to_bv_bv_unsigned | rewrite T20; apply Z_to_bv_bv_unsigned
| rewrite KT by (unfold art_pop_kept; repeat split; intros E; discriminate E); apply KP; inl ].
- eapply mem_grows_trans; [exact GX|exact G2].
- intros x N. rewrite <- (AXf x N). apply A2. unfold art_ca_fp, art_refill_fp in N.
repeat match goal with H : ~ (_ \/ _) |- _ => apply Decidable.not_or in H; destruct H end.
cbn [art_out fst snd]. repeat split; lia.
- exact G2.
- exact A2.
- apply (art_pc_hdr_tr _ ca true MX M2 ltac:(lia) ltac:(lia) A2); [|exact PH]. intros c' Hc'. clear - Hc Hc' Eca Ht Ht' HHI Hsp'. zarith_t.
- split.
+ split.
* cbn [art_cls_pop cl_cache]. rewrite art_removelast_length by exact Hne.
replace (Z.of_nat (length (cl_cache clp) - 1)) with (cnt - 1) by (unfold cnt; lia). unfold M2.
apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_hit; [lia|cbn; lia].
* cbn [art_cls_pop cl_cache]. intros j Hj. rewrite art_removelast_length in Hj by exact Hne. rewrite art_removelast_nth by exact Hj.
apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|apply CW; lia]. clear - Hj Hl16 Hc Eca Ht Ht' HHI Hsp'. zarith_t.
+ pose proof RR as (Rmx & Rnf & _ & _ & _ & _ & _ & Rna & _).
apply (art_region_rep_upd spb ris c 0 0 clp (art_cls_pop clp) MX M2 [(ca + 80 * c, 4); (ca + 2576, 8)]); try reflexivity;
first [ lia | exact RR | exact G2 | exact A2 | (intros; reflexivity) | idtac ].
* clear - Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
* clear - Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
* cbn [art_cls_pop cl_free]. clear - Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht' Hnf. zarith_t.
* apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|exact Rmx]. clear - Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
* apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|exact Rnf]. clear - Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
* apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|exact Rna]. clear - Eca Hc Xk HHI Hsp' Hris Eris Hspb Espb Ht Ht'. zarith_t.
Qed.
End SE.
#[using="Type"] Lemma art_tcell_exists : ltac2:(TCodec.tc2 tcn__JbtCARSpec "R0'RMyR0%211'6y8%511%311p051'C&Nr2+TP0+RPP0&R0+Vb\P0%2213%746541&QKr3%2281&QL&QJr4%221<&QO+2+R0%3221%8251z%=218r5+8%<221%A21G&Q0&QFr8r7%44321L'=';r1%J2>1%H22A%4221&Or:r9%L21<u8%55?4219%;271qV2Q=1%>2Q>1p0@1p0F1p0K1p0N1p0Q81p0Q<1pTDQE1pV0QF1pQDQH1").
Proof.
intros M t d A Ht Ht' Hd Hd' W. unfold apart in A.
apply (art_cell_exists M (t + d) 8 ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)). cbn. eapply wr_sub; [exact W|lia|lia].
Qed.
#[using="Type"] Lemma art_refill_fp_out_frame : ltac2:(TCodec.tc2 tcn__JbtCARSpec "RD'C';&QK+1r3%3221+N%5231%7231r9&R0r:+f@%3221%<251'<r8&QM+RPP0r6%3221%63E51+`PQoooPP0%E21>&QJ&QO+2+Q5%3221%52B1%?3NE1+TP0%82E1r=%Q0221%Q1242r>%=216r?%Q5221z%Q721N+XPP0r;%K221+S`PPPP0%Q<221rC+Q@%Q7221%Q@217&QL%1295%QD231&>&Q=rD%Q?219rBrAr@r<%785432HJM1%911p0;1p0C1p0I1p0L1p0Q11p0Q31p0Q81p0Q@1p0QC1p0QK1p0R21pV4R;1pTJR<1pT8R=1pU0R>1pU>R?1pUDR@1pV0RA1pQ>RB1pUBRC1").
Proof.
intros sp HI t spb ris qs c km x Hc HHI Espb Hspb Eris Hris Ht Ht' Hkm Hkm' Hx F. unfold art_refill_fp in F.
destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]; try lia. destruct F as (c' & Hc' & F). lia.
Qed.
#[using="Type"] Lemma art_refill_fp_out_stat : ltac2:(TCodec.tc2 tcn__JbtCARSpec "S5'C';&QK+1r3%3221+N%5231%7231r9&R0r:+f@%3221%<251&QLr;&QO+2+Q?%3221%6251'<&QM+RPP0r7%3221%53KB1+`PQoooPP0%K21B&QJ+Q5%?2>1%32A1%<3Q2G1+TP0%62D1r>%Q4221%Q5242r?%;216r@%Q9221&N%?2=:%244;61rA+QoonlP0%Q72E1%643?21zr=%QC221+XPP0%Q021B+S`PPPP0%QG221rD+V@%N221+R`@%Q0221%QM21J+R`H%Q3251%QC2M1%R2241&>&Q=rG+Q@%QN221rErCrB%7843B21MQ2Q4%911p0;1p0F1p0K1p0O1p0Q41p0Q81p0Q=1p0Q?1p0QD1p0QJ1p0QM1p0R41p0R<1p0RC1pV4RL1pTJRM1pT8RN1pU0RO1pU>S01pUDS11pV0S21pQ>S31pUBS41").
Proof.
intros sp HI t spb ris qs c km x Hc HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Hkm Hkm' Hx F. unfold art_refill_fp in F. unfold apart in Atk, Ats.
destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]; try lia. destruct F as (c' & Hc' & F). lia.
Qed.
#[using="Type"] Lemma art_refill_fp_out_img : ltac2:(TCodec.tc2 tcn__JbtCARSpec "R;'C';&QK+1r3%3221+N%5231%7231r9&R0r:+f@%3221%<251+`PQoooPP0%>215'<&QM+RPP0r7%3221%53F=1&QJr;&QO+2+Q5%3221%6251%=3NC1+TP0r=%O221&Nr>+Vb\P0%K21B%4437C1z%Q621M%Q72FN&QL%12Q07%Q;231&>&Q=rC+Q@%Q7221rAr@r?r<%885432CF1N%:11p0<1p0A1p0D1p0J1p0N1p0Q=1p0Q81p0Q?1p0QB1p0QI1pV4R21pTJR31pT8R41pU0R51pU>R61pUDR71pV0R81pQ>R91pUBR:1").
Proof.
intros sp HI t spb ris qs c km x Hc HHI HHI' Espb Hspb Eris Ht Ati Hkm Hx F. unfold art_refill_fp in F. unfold apart in Ati.
destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]; try lia. destruct F as (c' & Hc' & F). lia.
Qed.
#[using="Type"] Theorem art_ca_rspec_holds : ltac2:(TCodec.tc2 tcn__JbtCARSpec "1&Q4").
Proof.
unfold art_ca_rspec.
intros Q log regs M rom raw sp HI t ctx tp key tsd spb ris qs s km inited cl
H1 Hret H2 H4 H10 H11 H12 H13 Hs Hs8 HHI Hsp' GEO W Wt PC L T PH RC OK Hin Emu Room EV K.
set (c := AsanTab.class_id s) in *.
pose proof (AsanTab.class_id_ok s Hs) as (Hc & _ & _). fold c in Hc.
pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
assert (At_i : apart t 4096 0x10000 (0x693000 - 0x10000)) by (unfold apart; clear - G9; lia).
assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
clear G9 G10 G15 G16.
pose proof OK as (Hl16 & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & Hfor & _).
assert (Hkm : 0 <= km) by lia.
set (ca := t + 208) in *. assert (Eca : ca = t + 208) by reflexivity.
pose proof G11 as X11. unfold apart in X11. pose proof G18 as X18. unfold apart in X18. pose proof At_i as Xi. unfold apart in Xi.
destruct (art_ca_entry8 regs M rom sp s H2 H12 H13 ltac:(lia) ltac:(lia) Hs ltac:(eapply wr_sub; [exact W|lia|lia])) as (r1 & RUN1 & Q2 & Q14 & Q12 & Q15 & K1).
set (M1 := art_ca_frame M sp (U (getr regs 1)) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))) in *.
assert (A1 : art_agree [(sp - 48, 48)] M M1). { unfold M1, art_ca_frame. eapply art_agree_sub; [zagree|]. zsub. }
assert (G1' : mem_grows M M1) by (unfold M1, art_ca_frame; zgrows).
assert (FC : cellA M1 (sp - 8) 8 (U raw) /\ cellA M1 (sp - 16) 8 (U (getr regs 8)) /\ cellA M1 (sp - 24) 8 (U (getr regs 9)) /\ cellA M1 (sp - 32) 8 (U (getr regs 18))
/\ cellA M1 (sp - 40) 8 (U (getr regs 19)) /\ cellA M1 (sp - 48) 8 (U (getr regs 20))).
{ rewrite <- H1. unfold M1, art_ca_frame. repeat split; zcell. }
destruct FC as (FC1 & FC8 & FC9 & FC18 & FC19 & FC20).
assert (STEP2 : exists r2, msteps ASEGS (mkst r1 (0x56690 : word) M1 rom) (mkst r2 (0x567a0 : word) M1 rom)
/\ getr r2 8 = Z_to_bv 64 c
/\ (forall rg : reg, rg <> 8%bv -> rg <> 12%bv -> rg <> 14%bv -> rg <> 15%bv -> rg <> 16%bv -> rg <> 17%bv -> rg <> 5%bv -> rg <> 6%bv ->
getr r2 rg = getr r1 rg)).
{ destruct (Z.le_gt_cases s 512) as [Hsm|Hbg].
- destruct (art_ca_small r1 M1 rom s Q14 Q12 ltac:(lia)) as (r2 & RUN2 & P8 & _ & K2).
exists r2. split; [exact RUN2|]. split.
+ rewrite P8. unfold c. rewrite class_id_small by lia. reflexivity.
+ intros rg N8 N12 N14 N15 N16 N17 N5 N6. apply K2; assumption.
- pose proof (art_ca_big r1 M1 rom s Q14 Q12 ltac:(lia)) as RUN2a.
destruct (art_classid_hi_run r1 M1 rom (Z_to_bv 64 s) Q14) as (r2 & RUN2b & P8 & K2).
exists r2. split; [eapply msteps_trans; [exact RUN2a | exact RUN2b]|]. split.
+ rewrite P8. rewrite art_cid_w_ok by lia. reflexivity.
+ intros rg N8 N12 N14 N15 N16 N17 N5 N6. apply K2. unfold art_cid_kept. repeat split; assumption. }
destruct STEP2 as (r2 & RUN2 & P8 & K2).
assert (KR2 : forall rg : reg, In rg [1; 3; 4; 10; 11; 13; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r2 rg = getr regs rg).
{ intros rg Hrg. cbn [In] in Hrg.
destruct Hrg as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]];
(rewrite K2 by (intros E; discriminate E); apply K1; unfold art_ca_entry_kept; repeat split; intros E; discriminate E). }
assert (R2_2 : getr r2 2 = Z_to_bv 64 (sp - 48)) by (rewrite K2 by (intros E; discriminate E); exact Q2).
eapply ar_steps; [eapply msteps_trans; [exact RUN1|exact RUN2]|].
destruct RC as [CR RR].
assert (PH1 : art_pc_hdr ca inited M1).
{ apply (art_pc_hdr_tr _ ca inited M M1 ltac:(lia) ltac:(lia) A1); [|exact PH]. intros c' Hc'. clear - Hc' Eca HHI G7 G8. zarith_t. }
assert (CR1 : art_cache_rep ca c (cl_cache cl) M1).
{ apply (art_cache_rep_tr _ ca c (cl_cache cl) M M1 ltac:(lia) ltac:(lia) ltac:(lia) Hl16 A1); [| |exact CR]; clear - Hc Eca HHI G7 G8; zarith_t. }
assert (RR1 : art_region_rep spb ris c 0 cl M1).
{ pose proof RR as (Rmx & Rnf & _ & _ & _ & _ & _ & Rna & _).
apply (art_region_rep_upd spb ris c 0 0 cl cl M M1 [(sp - 48, 48)]); try reflexivity;
first [ lia | exact RR | exact G1' | exact A1 | (intros; reflexivity) | idtac ].
- clear - HHI Hsp' G1 G2 G6 Eris G4 Espb Hc. zarith_t.
- clear - HHI Hsp' G1 G2 G6 Eris G4 Espb Hc. zarith_t.
- clear - HHI Hsp' G1 G2 G6 Eris G4 Espb Hc Hnf4 Hmfa1. zarith_t.
- apply (art_cell_tr1 _ M M1 _ _ _ A1); [|exact Rmx]. clear - HHI Hsp' G1 G2 G6 Eris G4 Espb Hc. zarith_t.
- apply (art_cell_tr1 _ M M1 _ _ _ A1); [|exact Rnf]. clear - HHI Hsp' G1 G2 G6 Eris G4 Espb Hc. zarith_t.
- apply (art_cell_tr1 _ M M1 _ _ _ A1); [|exact Rna]. clear - HHI Hsp' G1 G2 G6 Eris G4 Espb Hc. zarith_t. }
assert (PC1 : art_prim_consts spb ris M1). { eapply art_prim_consts_fp; [exact A1| |exact PC]. intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia. }
assert (Wt1 : wrA M1 t 4096) by (eapply wr_grows; [exact G1'|exact Wt]).
assert (Hcase : cl_cache cl = [] \/ cl_cache cl <> []) by (destruct (cl_cache cl); [left; reflexivity|right; discriminate]).
assert (Xi' : forall d, 0 <= d -> d + 8 <= 4096 -> apart (t + d) 8 (1283032 + 32) 8) by (intros d Hd Hd'; unfold apart; clear - Xi Hd Hd'; lia).
destruct Hcase as [Ecache|Hne].
-
assert (Epre : art_ca_pre c cl = art_cls_refill c cl) by (unfold art_ca_pre; rewrite Ecache; reflexivity).
assert (Eev : art_ca_events spb c cl = art_refill_events spb c cl) by (unfold art_ca_events; rewrite Ecache; reflexivity).
rewrite Eev in EV, K. unfold art_ca_result, art_ca_cptr in K. rewrite Epre in K.
pose proof CR1 as [C0 _]. rewrite Ecache in C0. cbn in C0.
pose proof (art_miss_a_fn r2 M1 rom c ca 1283032 8 P8 ltac:(rewrite KR2 by inl; exact H10) ltac:(rewrite KR2 by inl; exact H11) ltac:(rewrite KR2 by inl; exact H13)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) C0) as RUN3.
match type of RUN3 with msteps _ _ (mkst ?R _ _ _) => set (r3 := R) in RUN3 end.
eapply ar_steps; [exact RUN3|].
assert (L1 : art_layout M1). { eapply art_layout_fp; [exact A1| |exact L]. intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia. }
assert (T1 : art_tsd M1 tp key tsd ctx t).
{ eapply art_tsd_fp; [exact A1| | |exact G19|exact G20|exact G21|exact G22|exact T].
- intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia.
- intros z Hz. cbn. clear - Hz HHI G1 G13 G14. repeat split; lia. }
destruct (art_tcell_exists M1 t 2872 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) Wt1) as (m1 & _ & Cm1).
destruct (art_tcell_exists M1 t 2880 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) Wt1) as (m2 & _ & Cm2).
destruct (art_tcell_exists M1 t 2792 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) Wt1) as (sv & _ & Csv).
apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st H; exact H].
apply (art_refill_rspec_holds EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) log r3 M1 rom (0x568bc : bv 64)%bv (sp - 48) HI t ctx tp key tsd spb ris qs c km inited cl
ltac:(unfold r3; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold r3; gres; exact R2_2) ltac:(unfold r3; gres; rewrite KR2 by inl; exact H4)
ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity)
Hc ltac:(lia) ltac:(lia) GEO ltac:(eapply wr_grows; [exact G1'|]; eapply wr_sub; [exact W|lia|lia]) Wt1 PC1 L1 T1 PH1 (conj CR1 RR1) OK Ecache Emu
ltac:(exists m1, m2, sv; repeat split; [exact Cm1|exact Cm2|replace (t + 208 + 2584) with (t + 2792) by lia; exact Csv])
ltac:(intros NP; destruct (Room Ecache NP) as (R1 & R2 & R3 & R4); repeat split; first [assumption | eapply wr_grows; [exact G1'|assumption]]) EV).
intros rR MR R10 R2 R1 RK RG RA RPH RCR ROK RSH.
set (clr := art_cls_refill c cl) in *. set (n := art_refill_n c).
destruct (art_refill_need c Hc) as (_ & Hn). fold n in Hn.
pose proof (art_pre_take_enough c cl Hc OK) as Hen. fold n in Hen.
assert (Lc : length (cl_cache clr) = n). { unfold clr. rewrite art_cls_refill_eq. fold n. cbn [art_cls_take cl_cache]. rewrite length_skipn. lia. }
assert (Hne' : cl_cache clr <> []). { intros E. rewrite E in Lc. cbn in Lc. lia. }
pose proof ROK as (_ & (Hau0r & Haumur) & _ & _ & _ & Hmu3r & _ & (_ & Hmfa1r) & Hnf4r & Hforr & _).
pose proof RCR as [[D0 DW] DRR]. rewrite Lc in D0.
assert (WtR : wrA MR t 4096) by (eapply wr_grows; [exact RG|exact Wt1]).
pose proof (art_miss_b_fn rR MR rom (ca + 80 * c) (Z.of_nat n) 8 ca 1283032 R10
ltac:(rewrite RK by inl; unfold r3; gres; reflexivity) ltac:(rewrite RK by inl; unfold r3; gres; reflexivity)
ltac:(rewrite RK by inl; unfold r3; gres; reflexivity) ltac:(rewrite RK by inl; unfold r3; gres; reflexivity)
ltac:(lia) ltac:(lia) ltac:(lia) D0) as RUN4.
match type of RUN4 with msteps _ _ (mkst ?R _ _ _) => set (r4 := R) in RUN4 end.
destruct (art_tcell_exists MR t 2784 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) WtR) as (st & Hst & Cst).
destruct (RPH c ltac:(lia)) as [_ Pcsz]. cbn in Pcsz.
assert (PspbR : cellA MR (1283032 + 32) 8 spb).
{ destruct PC1 as (Pspb & _). apply (art_cell_agree _ M1 MR); [|lia|cbn; lia|exact Pspb]. intros x Hx. apply RA.
apply (art_refill_fp_out_img sp HI t spb ris qs c km (U x) Hc HHI G1 Espb G4 Eris G7 At_i Hkm). cbn in Hx. lia. }
assert (Hch : art_cptr_ok (AsanTab.class_size c) (cl_au clr) (last (cl_cache clr) 0)).
{ apply (proj1 (Forall_forall _ _) Hforr). apply in_or_app. left. rewrite (app_removelast_last 0 Hne') at 2. apply in_or_app. right. left. reflexivity. }
pose proof (art_class_size_facts c Hc) as (Hsz & _).
pose proof (art_cptr_lt (AsanTab.class_size c) (cl_au clr) (last (cl_cache clr) 0) ltac:(lia) ltac:(lia) Hch) as Hch'.
destruct (art_cache_pop50 r4 MR rom c ca 1283032 (Z.of_nat n) (art_ic_size c) (last (cl_cache clr) 0) st spb
ltac:(unfold r4; gres; rewrite RK by inl; unfold r3; gres; exact P8) ltac:(unfold r4; gres; rewrite RK by inl; unfold r3; gres; reflexivity)
ltac:(unfold r4; gres; reflexivity) ltac:(unfold r4; gres; reflexivity) ltac:(unfold r4; gres; reflexivity)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Eca, Et; replace (4096 * qt + 208) with ((512 * qt + 26) * 8) by lia; apply Z_mod_mult) ltac:(lia) ltac:(lia)
ltac:(lia) ltac:(pose proof (art_ic_size_pos c ltac:(lia)); lia) ltac:(lia) Hst ltac:(lia)
Pcsz ltac:(rewrite art_last_nth, Lc; replace (ca + 80 * c + 16 + 4 * (Z.of_nat n - 1)) with (ca + 80 * c + 16 + 4 * Z.of_nat (n - 1)) by lia; apply DW; lia)
ltac:(replace (ca + 2576) with (t + 2784) by lia; exact Cst) PspbR
ltac:(eapply (wr_wok _ _ _ _ WtR); [lia|cbn; lia]) ltac:(eapply (wr_wok _ _ _ _ WtR); [lia|cbn; lia])
ltac:(replace (ca + 80 * c) with (t + (208 + 80 * c)) by lia; pose proof (Xi' (208 + 80 * c) ltac:(lia) ltac:(lia)) as X; unfold apart in X |- *; lia)
ltac:(replace (ca + 2576) with (t + 2784) by lia; apply Xi'; lia))
as (rP & RUNP & P10 & KP).
eapply ar_steps; [eapply msteps_trans; [exact RUN4|exact RUNP]|].
assert (TFR : forall a v, sp - 48 <= a -> a + 8 <= sp -> cellA M1 a 8 v -> cellA MR a 8 v).
{ intros a v Ha Ha' C. apply (art_cell_agree _ M1 MR); [|lia|cbn; lia|exact C]. intros x Hx. apply RA.
apply (art_refill_fp_out_frame sp HI t spb ris qs c km (U x) Hc HHI Espb G4 Eris G6 G7 G8 Hkm ltac:(lia)). cbn in Hx. lia. }
replace (Z.of_nat n) with (Z.of_nat (length (cl_cache clr))) by (rewrite Lc; reflexivity).
apply (art_ca_finish Q (log ++ art_refill_events spb c cl) regs rP M MR rom raw sp HI t spb ris qs c km st (spb + c * 2 ^ 32 + last (cl_cache clr) 0 * 16) clr
Hret Hc HHI Hsp' Espb G4 Eris G6 G7 G8 G11 Hne' ltac:(lia) ltac:(lia) ltac:(eapply mem_grows_trans; [exact G1'|exact RG])).
+ intros x N. rewrite (RA x) by (intros F; apply N; unfold art_ca_fp; right; left; exact F).
apply A1. cbn. split; [|exact I]. intros H. apply N. unfold art_ca_fp. left. lia.
+ exact RPH.
+ exact RCR.
+ apply TFR; [lia|lia|exact FC1].
+ apply TFR; [lia|lia|exact FC8].
+ apply TFR; [lia|lia|exact FC9].
+ apply TFR; [lia|lia|exact FC18].
+ apply TFR; [lia|lia|exact FC19].
+ apply TFR; [lia|lia|exact FC20].
+ rewrite KP by (intros E; discriminate E). unfold r4; gres. reflexivity.
+ rewrite KP by (intros E; discriminate E). unfold r4; gres. exact R2.
+ exact P10.
+ intros x Hx. cbn [In] in Hx.
destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; (rewrite KP by (intros E; discriminate E); unfold r4; gres; rewrite RK by inl; unfold r3; gres; apply KR2; inl).
+ intros regs' M' S10 S2 S1 SK SG SA SGX SAX SPH SCR.
apply (K regs' M' S10 S2 S1 SK SG SA SPH SCR).
* apply art_cls_ok_pop; assumption.
* exact Hch.
* intros _ NP j Hj. pose proof (RSH NP j Hj) as C. pose proof At_s as Xs. unfold apart in Xs.
apply (art_cell_tr1 _ MR M' _ _ _ SAX); [|exact C]. clear - Hj Xs Eca Hc G4 Espb Hkm Emu Hmu3 G6 Eris G2 G7 G8. zarith_t.
-
assert (Epre : art_ca_pre c cl = cl) by (unfold art_ca_pre; destruct (cl_cache cl); [contradiction|reflexivity]).
assert (Eev : art_ca_events spb c cl = []) by (unfold art_ca_events; destruct (cl_cache cl); [contradiction|reflexivity]).
rewrite Eev in K. rewrite app_nil_r in K. unfold art_ca_result, art_ca_cptr in K. rewrite Epre in K.
pose proof (Hin Hne) as ->.
set (cnt := Z.of_nat (length (cl_cache cl))).
assert (Hcnt : 1 <= cnt <= 16). { unfold cnt. destruct (cl_cache cl); [contradiction|]. cbn [length] in *. lia. }
destruct (art_tcell_exists M1 t 2784 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) Wt1) as (st & Hst & Cst).
destruct CR1 as [C0 CW]. destruct (PH1 c ltac:(lia)) as [_ Pcsz]. cbn in Pcsz.
pose proof PC1 as (Pspb & _).
assert (Hch : art_cptr_ok (AsanTab.class_size c) (cl_au cl) (last (cl_cache cl) 0)).
{ apply (proj1 (Forall_forall _ _) Hfor). apply in_or_app. left. rewrite (app_removelast_last 0 Hne) at 2. apply in_or_app. right. left. reflexivity. }
pose proof (art_class_size_facts c Hc) as (Hsz & _).
pose proof (art_cptr_lt (AsanTab.class_size c) (cl_au cl) (last (cl_cache cl) 0) ltac:(lia) ltac:(lia) Hch) as Hch'.
destruct (art_cache_pop_core r2 M1 rom c ca 1283032 cnt (art_ic_size c) (last (cl_cache cl) 0) st spb P8
ltac:(rewrite KR2 by inl; exact H11) ltac:(rewrite KR2 by inl; exact H10)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Eca, Et; replace (4096 * qt + 208) with ((512 * qt + 26) * 8) by lia; apply Z_mod_mult) ltac:(lia) ltac:(lia)
Hcnt ltac:(pose proof (art_ic_size_pos c ltac:(lia)); lia) ltac:(lia) Hst ltac:(lia)
C0 Pcsz ltac:(rewrite art_last_nth; replace (ca + 80 * c + 16 + 4 * (cnt - 1)) with (ca + 80 * c + 16 + 4 * Z.of_nat (length (cl_cache cl) - 1)) by (unfold cnt; lia); apply CW; lia)
ltac:(replace (ca + 2576) with (t + 2784) by lia; exact Cst) Pspb
ltac:(eapply (wr_wok _ _ _ _ Wt1); [lia|cbn; lia]) ltac:(eapply (wr_wok _ _ _ _ Wt1); [lia|cbn; lia])
ltac:(replace (ca + 80 * c) with (t + (208 + 80 * c)) by lia; pose proof (Xi' (208 + 80 * c) ltac:(lia) ltac:(lia)) as X; unfold apart in X |- *; lia)
ltac:(replace (ca + 2576) with (t + 2784) by lia; apply Xi'; lia))
as (rP & RUNP & P10 & KP).
eapply ar_steps; [exact RUNP|].
apply (art_ca_finish Q log regs rP M M1 rom raw sp HI t spb ris qs c km st (spb + c * 2 ^ 32 + last (cl_cache cl) 0 * 16) cl
Hret Hc HHI Hsp' Espb G4 Eris G6 G7 G8 G11 Hne Hl16 ltac:(lia) G1').
+ intros x N. apply A1. cbn. split; [|exact I]. intros H. apply N. unfold art_ca_fp. left. lia.
+ exact PH1.
+ split; [split; [exact C0|exact CW]|exact RR1].
+ exact FC1.
+ exact FC8.
+ exact FC9.
+ exact FC18.
+ exact FC19.
+ exact FC20.
+ rewrite KP by (intros E; discriminate E). rewrite KR2 by inl. exact H13.
+ rewrite KP by (intros E; discriminate E). exact R2_2.
+ exact P10.
+ intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; (rewrite KP by (intros E; discriminate E); apply KR2; inl).
+ intros regs' M' R10 R2 R1 RK RG RA RGX RAX RPH RCR.
apply (K regs' M' R10 R2 R1 RK RG RA RPH RCR).
* apply art_cls_ok_pop; assumption.
* exact Hch.
* intros E. contradiction.
Qed.
End Spec.
