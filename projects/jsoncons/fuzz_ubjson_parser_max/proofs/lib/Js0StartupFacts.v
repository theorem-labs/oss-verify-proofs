(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
StartupTac ArgvEnv RefLayout Js0StartupDefs Js0Startup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0StartupFacts () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StartupDefs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StartupFacts.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1fst"; "1length"; "1list"; "1nat"; "1option"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2not"; "2or"; "3lt"]; ["4nth"; "5Z"; "0D"; "6Segment"; "7word_to_le_bytes"; "8ed_random"; "9D_main"; "9canary_w"; "9envp_w"; ":D_main_missb"; ":djw"; ":range_disjoint_b"; ";rdn"; "<add"; "<le"; "<lt"]; ["<of_nat"; "<pow"; "<to_nat"; "0a"; "0av"; "0bs"; "0c"; "0ev"; "0hw"; "0i"; "0j"; "0m"; "0mem"; "0n"; "0rdraw"; "0segs"]; ["0sp0"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0tid"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Plain.M.phdrs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Section FPX_1. Context {fx : PropExec.FPState}.
Definition D_main_cells : list (Z * nat) :=
[(0xc7b90%Z, 8%nat); (0xe7ef8%Z, 8%nat); (0xe7f58%Z, 8%nat); (0xe7f20%Z, 8%nat); (0xe7ee8%Z, 8%nat); (0xe7ee0%Z, 8%nat); (0xe7c88%Z, 8%nat); (0xe7c98%Z, 8%nat); (0xe7c90%Z, 8%nat); (0xe7f08%Z, 8%nat); (0xe7f10%Z, 8%nat); (0xc7c70%Z, 8%nat); (0xc7c58%Z, 8%nat); (0xc7b98%Z, 8%nat); (0xe7ef0%Z, 1%nat); (0xc7bc0%Z, 4%nat); (0xc7bb8%Z, 4%nat); (0xc7c30%Z, 8%nat); (0xc7c10%Z, 8%nat); (0xc7ba0%Z, 8%nat); (0xc7ba8%Z, 8%nat); (0xc7bb0%Z, 8%nat); (0xe7ed0%Z, 4%nat); (0xe7ed4%Z, 4%nat); (0xe7ed1%Z, 1%nat); (0xc7c50%Z, 8%nat); (0xb61e0%Z, 1%nat)].
Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.
Definition D_main_missb (a : Z) (n : nat) : bool :=
forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0xe9000)%Z.
Definition djw (P : Prop) : Prop := P.
Lemma range_disjoint_djw : ltac2:(TCodec.tc2 tcn__Js0StartupFacts "Q3'A'6'8%1232'<'2&Kr3r2r1%43321(:%83721&J'>&N&Mr4&Q0%11<%4231&3%13FE>%8231&9%13IHA%811%;251%=21;%?261%A11p0C1pR>M1pRLQ01pR8Q21").
Proof.
intros a n [c l] H. unfold range_disjoint_b in H. cbn [fst snd] in *.
apply orb_true_iff in H. unfold djw. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.
Section Facts.
Context {RE : RunEnv}.
Variable sp0 : word.
Variables av ev : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.
Variable tid : word.
Hypothesis Hva : valid_argv av.
Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
Let D := D_main sp0 av ev hw (ed_random rdraw) tid.
Local Notation RND := (ed_random rdraw) (only parsing).
Lemma len_av : ltac2:(TCodec.tc2 tcn__Js0StartupFacts "A';&N+1&Q0&4'5'QBy8%211%411vQ4%7221%911%<2;1+QP0%>231%@231").
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
Section SE.
Local Abbreviation SEC_T_D_main_miss := (ltac2:(TCodec.tc2 tcn__Js0StartupFacts "Q>'5'C%211'A'6'<'2&Ir2r1%3221(:%73621'7'QBy8%211%A11%511&Lr4&FvQ@vQ4vQ7vQ8&EvQ>%211vQD%96876521&QAyR0r3%3221%@4?51K%F14(0%11Fq031%E4D16Q0%Q43G61p0N1pRLQ71pR8Q91pS0Q;1")) (only parsing).
Variable segs : ltac:(sec_ty2 constr:(SEC_T_D_main_miss) 0%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_D_main_miss) 1%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_D_main_miss) 2%nat 0%nat).
Lemma D_main_miss : ltac:(sec_stmt2 constr:(SEC_T_D_main_miss) 3%nat 0%nat).
Proof.
intros Hb.
pose proof (u64_range tid). pose proof (u64_range hw).
unfold D_main_missb, D_main_cells in Hb. cbn [forallb] in Hb.
repeat match goal with
| H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
end.
repeat match goal with
| H : range_disjoint_b _ _ _ = true |- _ =>
apply range_disjoint_djw in H; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ] in H
| H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
| H : true = true |- _ => clear H
end.
cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
repeat (rewrite rdn_wbytes_out by
(rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; imm_norm; unorm;
lazymatch goal with
| |- (?A \/ ?B) => match goal with H : djw _ |- _ => exact H end
| |- _ => lia
end)).
reflexivity.
Qed.
End SE.
Ltac hitD :=
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc;
pose proof len_av;
peel; first [ apply rdn_wbytes_hit8; unorm; lia
| match goal with |- rdn _ (wbytes _ ?a ?bs) ?a _ = _ =>
rewrite <- (length_N_to_le_bytes 4) at 1; apply rdn_wbytes_hit; rewrite length_N_to_le_bytes; unorm; lia end ].
Lemma D_main_tid : ltac2:(TCodec.tc2 tcn__Js0StartupFacts "J'5'C%211'<'7'QBy8%211%811%511&Lr1vB&QAyR0+hnmH%3221u4%847621(1&DvQD%2251%42?1%E3?61pS0G1").
Proof.
intros segs. pose proof (u64_range tid). pose proof (u64_range hw). subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
Qed.
Lemma D_main_guard : ltac2:(TCodec.tc2 tcn__Js0StartupFacts "N'5'C%211'<'7'QBy8%211%811%511&Lr1vB&QAyR0+lof@%3221u8%847621(1&D&G&EvQ>%211%411%6291%82C1%I3C:1pS0K1").
Proof.
intros segs. pose proof (u64_range tid). pose proof (u64_range hw). subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
rewrite canary_bytes.
lazymatch goal with
| |- rdn _ (wbytes (wbytes (wbytes ?DD _ _) _ _) _ _) _ _ = _ =>
pose proof (rd_guard_at segs DD RND 0xe7ed0 ltac:(lia) ltac:(lia)) as HG;
cbn [Z.add Pos.add Pos.succ] in HG; exact HG
end.
Qed.
Section SE.
Local Abbreviation SEC_T_D_main_pagesize := (ltac2:(TCodec.tc2 tcn__Js0StartupFacts "K'5'C%211'<'7'QBy8%211%811%511&Lr1vB&QAyR0+loi0%3221u8%847621(1&D+TP0%9281%3261%52@1%F3@71pS0H1")) (only parsing).
Variable segs : ltac:(sec_ty2 constr:(SEC_T_D_main_pagesize) 0%nat 0%nat).
Lemma D_main_pagesize : ltac:(sec_stmt2 constr:(SEC_T_D_main_pagesize) 1%nat 0%nat).
Proof.
pose proof (u64_range tid). pose proof (u64_range hw). pose proof len_av. subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_D_main_hwcap := (ltac2:(TCodec.tc2 tcn__Js0StartupFacts "J'5'C%211'<'7'QBy8%211%811%511&Lr1vB&QAyR0+lojH%3221u8%847621(1&DvQ8%2251%42?1%E3?61pS0G1")) (only parsing).
Variable segs : ltac:(sec_ty2 constr:(SEC_T_D_main_hwcap) 0%nat 0%nat).
Lemma D_main_hwcap : ltac:(sec_stmt2 constr:(SEC_T_D_main_hwcap) 1%nat 0%nat).
Proof.
pose proof (u64_range tid). pose proof (u64_range hw). pose proof len_av. subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_D_main_environ := (ltac2:(TCodec.tc2 tcn__Js0StartupFacts "M'5'C%211'<'7'QBy8%211%811%511&Lr1vB&QAyR0+hnl@%3221u8%847621(1&D&HvQ@vQ4%3221%5281%72B1%H3B91pS0J1")) (only parsing).
Variable segs : ltac:(sec_ty2 constr:(SEC_T_D_main_environ) 0%nat 0%nat).
Lemma D_main_environ : ltac:(sec_stmt2 constr:(SEC_T_D_main_environ) 1%nat 0%nat).
Proof.
pose proof (u64_range tid). pose proof (u64_range hw). pose proof len_av. subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.
End SE.
Lemma D_main_self : ltac2:(TCodec.tc2 tcn__Js0StartupFacts "I'5'C%211'<'7'QBy8%211%811%511&Lr1vB&QAyR0+hnlH%3221u8%847621(1&D%1245%32>1%D3>51pS0F1").
Proof.
intros segs. pose proof (u64_range tid). pose proof (u64_range hw). subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.
Lemma D_main_locale : ltac2:(TCodec.tc2 tcn__Js0StartupFacts "K'5'C%211'<'7'QBy8%211%811%511&Lr1vB&QAyR0+hoQ@%3221u8%847621(1&D+loi8%9281%3261%52@1%F3@71pS0H1").
Proof.
intros segs. pose proof (u64_range tid). pose proof (u64_range hw). subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.
Lemma D_main_canary : ltac2:(TCodec.tc2 tcn__Js0StartupFacts "N'5'C%211'<'7'QBy8%211%811%511&Lr1vB&QAyR0+hoR@%3221u8%847621(1&D&G&EvQ>%211%411%6291%82C1%I3C:1pS0K1").
Proof.
intros segs. pose proof (u64_range tid). pose proof (u64_range hw). subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.
Section SE.
Local Abbreviation SEC_T_rdn_pointwise_ov := (ltac2:(TCodec.tc2 tcn__Js0StartupFacts "R<'5'C%211'QByR0%211'7y8%511%311pS<51'6%<14&?r1r4%3221&='<r6&QA&M&QC%12C8&Q0r2%211%6241%82H1%:11(0%11G%>3G31%@11p0B1pRFH1&Nr3%@2Q21%?1H%C221&Q1+2+R0%3221%9251%Q81Q2&Lr7r5%342OQ31(1%12Q8?%Q33731%Q92Q86r9%Q22QD8%Q421O%Q62QF1%411&@z%Q:2QG1%34QGQ6Q<1%=2QH1%Q?3QH61p0<1pRFQH1p0?1p0H1p0Q31pR<QK1pR8R31pRLQN1pRHR01pS0R91")) (only parsing).
Variable segs : ltac:(sec_ty2 constr:(SEC_T_rdn_pointwise_ov) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rdn_pointwise_ov) 1%nat 0%nat).
Lemma rdn_pointwise_ov : ltac:(sec_stmt2 constr:(SEC_T_rdn_pointwise_ov) 2%nat 0%nat).
Proof.
intros n.
induction n as [|n IH]; intros a bs Hdef Hnw Hr j Hj; [lia|].
cbn [rdn] in Hr. pose proof (u64_range a) as Ha.
pose proof (Hdef 0%nat ltac:(lia)) as H0. rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0.
destruct (m a) as [b|] eqn:Hm; [|exfalso; apply H0; reflexivity].
destruct (rdn segs m (a + 1) n) as [rest|] eqn:Hr'; [|discriminate]. injection Hr as <-.
destruct j as [|j].
+ rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned. exact Hm.
+ cbn [nth]. assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
replace (bv_unsigned a + Z.of_nat (S j))%Z with (bv_unsigned (a + 1) + Z.of_nat j)%Z by lia.
apply (IH (a + 1) rest); [ | lia | exact Hr' | lia].
intros k Hk. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat k)%Z with (bv_unsigned a + Z.of_nat (S k))%Z by lia.
apply Hdef. lia.
Qed.
End SE.
Ltac d_cover :=
repeat first
[ rewrite wbytes_inside by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia); discriminate
| rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ].
Ltac cover8 :=
let i := fresh "i" in let Hi := fresh "Hi" in
intros i Hi; pose proof (u64_range tid); pose proof (u64_range hw); pose proof len_av; subst D;
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc;
assert (C : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7)%Z) by lia;
destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
lazymatch goal with |- _ (Z_to_bv 64 ?z) <> None => let c := eval vm_compute in z in change z with c end;
d_cover.
Lemma D_cover_guard : ltac2:(TCodec.tc2 tcn__Js0StartupFacts "Q0'A';&Nzr1%3221&O+8%2241%8241&='<'7'QBy8%211%411vB&QAyR0&M+lof@r2%3221%6251%811(0%11<%A3<31%C11p0E1pRDO1").
Proof. cover8. Qed.
Lemma D_cover_canary : ltac2:(TCodec.tc2 tcn__Js0StartupFacts "Q0'A';&Nzr1%3221&O+8%2241%8241&='<'7'QBy8%211%411vB&QAyR0&M+hoR@r2%3221%6251%811(0%11<%A3<31%C11p0E1pRDO1").
Proof. cover8. Qed.
Lemma D_cover_hwcap : ltac2:(TCodec.tc2 tcn__Js0StartupFacts "Q0'A';&Nzr1%3221&O+8%2241%8241&='<'7'QBy8%211%411vB&QAyR0&M+lojHr2%3221%6251%811(0%11<%A3<31%C11p0E1pRDO1").
Proof. cover8. Qed.
Ltac pt8 Hcov Hrd :=
let i := fresh "i" in let Hi := fresh "Hi" in
intros i Hi;
lazymatch goal with |- D (Z_to_bv 64 (?a + i)) = Some _ =>
pose proof (rdn_pointwise_ov SEGS D 8 (Z_to_bv 64 a) _
ltac:(intros j Hj; rewrite u_Z2bv by lia; apply Hcov; lia)
ltac:(rewrite u_Z2bv by lia; lia) (Hrd SEGS) (Z.to_nat i) ltac:(lia)) as Hp;
rewrite u_Z2bv, Z2Nat.id in Hp by lia; exact Hp
end.
Lemma D_guard_pt : ltac2:(TCodec.tc2 tcn__Js0StartupFacts "Q;'A';&Nzr1%3221&O+8%2241%8241'<'7'QBy8%211%411vB&QAyR0&M+lof@r2%3221%6251%811(1&@&Q2%117&Du8&G&EvQ>%211%411%7261%D2HQ2%<4H:21%>2I1%N3I@1p0Q01pRDQ:1").
Proof. pt8 D_cover_guard D_main_guard. Qed.
Lemma D_canary_pt : ltac2:(TCodec.tc2 tcn__Js0StartupFacts "Q;'A';&Nzr1%3221&O+8%2241%8241'<'7'QBy8%211%411vB&QAyR0&M+hoR@r2%3221%6251%811(1&@&Q2%117&Du8&G&EvQ>%211%411%7261%D2HQ2%<4H:21%>2I1%N3I@1p0Q01pRDQ:1").
Proof. pt8 D_cover_canary D_main_canary. Qed.
Lemma D_hwcap_pt : ltac2:(TCodec.tc2 tcn__Js0StartupFacts "Q7'A';&Nzr1%3221&O+8%2241%8241'<'7'QBy8%211%411vB&QAyR0&M+lojHr2%3221%6251%811(1&@&Q2%117&Du8vQ8%3221%@2DN%84D621%:2E1%J3E<1p0L1pRDQ61").
Proof. pt8 D_cover_hwcap D_main_hwcap. Qed.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Hypothesis ME : main_entry sp0 av ev uid hw rdraw tid regs mem.
Lemma main_entry_rdn_image : ltac2:(TCodec.tc2 tcn__Js0StartupFacts "Q5'5'C%211'A'6'<'2&Ir2r1%3221(:%73621'7'QBy8%211%A11%511&Lr4vQ<&QAyR0r3%3221%74651B%=14(0%11=q031%<4;16G%K3>61p0E1pRLN1pR8Q01pS0Q21").
Proof.
intros segs a n Hb.
assert (Hr : (0 <= a /\ a + Z.of_nat n <= 0xe9000)%Z).
{ unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [_ H1].
apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME)
by (rewrite stack_max_size_val; unorm; lia).
apply D_main_miss. exact Hb.
Qed.
Lemma main_entry_tid : ltac2:(TCodec.tc2 tcn__Js0StartupFacts "J'5'C%211'<'7'QBy8%211%811%511&Lr1vQ<&QAyR0+hnmH%3221u4%847621(1&DvQD%2251%42?1%E3?61pS0G1").
Proof.
intros segs. rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME)
by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
Qed.
Lemma main_entry_guard : ltac2:(TCodec.tc2 tcn__Js0StartupFacts "N'5'C%211'<'7'QBy8%211%811%511&Lr1vQ<&QAyR0+lof@%3221u8%847621(1&D&G&EvQ>%211%411%6291%82C1%I3C:1pS0K1").
Proof.
intros segs. rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME)
by (rewrite stack_max_size_val; unorm; lia). apply D_main_guard.
Qed.
End Facts.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
