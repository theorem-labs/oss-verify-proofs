(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk StepTac ShapeAlg AgentLib Hoare RefLayout
AsanAcct AsanAcctShape.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanK AsanPlanSoundK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanNodesAuxK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanNodesAuxK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanNodesAuxK.NodesD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3SoundK.AX2SK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1O"; "1Some"; "1bool"; "1false"; "1fst"; "1list"; "1nat"; "1option"; "1prod"; "1snd"; "1true"; "2I"; "2and"; "2eq"; "2ex"]; ["2not"; "3lt"; "4Forall"; "5Z"; "0E"; "0E'"; "0FS0"; "0FULL"; "0H"; "0LIMIT"; "6Segment"; "7fetch_word"; "7store_ok"; "8Model"; "8m_vm_lazy"; "8page_base"]; ["8page_in_ranges"; "9bvmap"; "0M"; "0R"; "0R'"; ":A_wf"; ":H_off_segments"; ":lazy_cover"; ":mrestrict"; ":munrestrict"; "<Hv"; ";nb_lt"; "=a_ss"; "=acs"; "=atable"; "=kimg_cut"]; ["=kwritable"; "=len_eqb"; "=with_ss"; ">Mr"; ">allowA"; ">cs_ok"; ">hid"; ">in_hull"; ">utop"; "?SA"; "?edenot"; "?env"; "?ev"; "?expr"; "?kentry"; "?sr_upd"]; ["?sym_state"; "@estart"; "@know_ok"; "@regs_ok"; "Abtgt"; "Ac_eq"; "Agetr"; "Av_addi"; "Bmem_grows"; "0SEGS"; "0SINV"; "CIn"; "Dadd"; "Deqb"; "Dle"; "Dlt"]; ["Dmodulo"; "Dof_nat"; "Dpow"; "Dto_nat"; "0a"; "0allkn"; "0argH"; "0b"; "0cs"; "0e"; "0e1"; "0e2"; "0hi"; "0iv"; "0k"; "0l"]; ["0lo"; "0m"; "0model"; "0n"; "0n1"; "0n2"; "0off"; "0r"; "0r1"; "0r2"; "0s"; "0s1"; "0s2"; "0segs"; "0sr"; "EBV"]; ["EZ_to_bv"; "Ebv"; "Ebv_signed"; "Ebv_unsigned"; "0w"; "0x"; "0z"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Import AX2K. Import AX2SK. Import APK. Import APSK.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma u_lit : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "G'C'=&R>zr1%3221&R?&RB+2+R0%3221%5271%;271'>&SCyR0&S@r2%2231%5241%73D13p091pW>F1").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. Qed.
Lemma v_addi_lit : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "M'C'=&R>zr2%3221&R?&RB+2+R0%3221%5271%;271'>'SAyR0%211&R7&S@r3%2251%421A&R<%124C%6291%<3941p0>1pUNK1pU:L1").
Proof. intros a k Ha. unfold v_addi. rewrite u_lit by lia. reflexivity. Qed.
Lemma btgt_lit : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "M'C'=&R>zr2%3221&R?&RB+2+R0%3221%5271%;271'>'SAyR0%211&R4&S@r3%2251%421A&R<%124C%6291%<3941p0>1pUNK1pU:L1").
Proof. intros a k Ha. unfold btgt. apply v_addi_lit. exact Ha. Qed.
Lemma c_eq_lit : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "N'C'=&R>zr2%3221&R?&RB+2+R0%3221%5271%;271'>'3&R5&S@yR0r4%3221r3%5241%7231&R=%1264%<3;31p0>1p0?1pU@L1pU:M1").
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_lit by lia. reflexivity. Qed.
Lemma reg_neq : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "O'C'=&R>zr2%3221&R?+Q0%2241%8241&@'>r4r3%33>21%511'SAy5%211&S@r5%2241/014%426;%=3621%?11p0;1p0B1p0C1pU@M1pU:N1").
Proof.
intros a b Ha Hb Hne Heq. apply (f_equal bv_unsigned) in Heq.
rewrite !Z_to_bv_unsigned in Heq. unfold bv_wrap in Heq. change (bv_modulus 5) with 32 in Heq.
rewrite !Z.mod_small in Heq by lia. lia.
Qed.
Ltac rif :=
repeat match goal with
| |- context [if bv_eqb ?a ?b then ?u else ?v] =>
lazymatch a with
| @BV _ _ _ =>
lazymatch b with
| @BV _ _ _ =>
let c := eval vm_compute in (bv_eqb a b) in
lazymatch c with
| true => change (if bv_eqb a b then u else v) with u
| false => change (if bv_eqb a b then u else v) with v
end
end
end
end.
Ltac pc_is v :=
lazymatch goal with
| |- msteps _ (mkst _ (Z_to_bv 64 ?q) _ _) _ => first [constr_eq q v | replace q with v by lia]
end.
Lemma signed12_0 : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "='>'C&SBy<(S?z(<%33421'SA%116/031%9281%<3;17"). Proof. reflexivity. Qed.
Lemma signed12_1 : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "='>'C&SBy<(S?+1(<%33421'SA%116/031%9281%<3;17"). Proof. reflexivity. Qed.
Lemma len_eqb_sound : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "Q9'6'J%211'QK'SAyR0%211'8y8%511%311p051'QN%=11'QM&R2r6r5r4r3%544321'>'3&QAr2%23761(;%63521&QJr7%221<%322<%;3J21p061p0>1pV4E1pV8F1pUNH1pR6K1pQ:Q41pTDQ61").
Proof.
intros SEGS E M k n m HK H. unfold len_eqb in H. apply orb_prop in H as [H|H].
- apply expr_eqb_eq in H. subst. reflexivity.
- apply andb_prop in H as [H1 H2].
pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as A1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H2) as A2.
cbn [xt_den] in A1, A2. apply bv_eq. lia.
Qed.
Lemma kwritable_sound : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "R8'6'J%211'QK'SAyR0%211'8y8%511%311p051'QN%=11'QM'C&R2r8r7r6r5%544321r9%741653'>'3&Q@r4r3%35;:921(;%73621&R>z%2217'=&Lr<r:&S@&R1r;(QI%12IH%4231%62Q81&RC%11K%<4;:31%I3H1C%B2A6&R<%128Q0&RB+2+R0%3221%I251%G281%H2:1p0J1p0N1p0Q71p0Q:1pV8QA1pV>QB1pU@QD1pUNQF1pU<QG1pR6QJ1pQ:R31pVLR51").
Proof.
intros segs E M allkn k b off n Hall HK H Hn. induction k as [|K rest IH]; [discriminate|].
apply Forall_cons_iff in HK as [HKK Hrest]. cbn [kwritable] in H.
destruct K; try exact (IH Hrest H).
lazymatch type of HKK with kentry_ok _ _ _ (KWr ?a ?n) => destruct a as [wb wk]; rename n into wn end.
cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
bv_unsigned (edenot E b) + off + n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) (Z.to_nat n) = true
/\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + n <= 2 ^ 64).
{ intros A B. split; [|lia].
replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
apply Hs; [lia|]. rewrite Z2Nat.id by lia. lia. }
lazymatch type of H with (if ?c0 then _ else _) = _ => destruct c0 eqn:Hc0 end.
- destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
destruct (xlo allkn wn) as [wl|] eqn:Hx; [|discriminate]. apply Z.leb_le in Hc0.
pose proof (xlo_sound segs E M allkn wn wl Hall Hx) as Hwl. unfold elenZ in *. apply CORE; lia.
- lazymatch type of H with (if ?c1 then _ else _) = _ => destruct c1 eqn:Hc1; [|exact (IH Hrest H)] end.
apply andb_prop in Hc1 as [Hnn Hxi]. apply andb_prop in Hnn as [Hn0 Hn1].
apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. unfold two64 in Hn1.
destruct (xinside_sound segs E M allkn b off (ELit n) wb wk wn Hall Hxi) as [I1 I2].
unfold elenZ in I2 at 1. cbn [edenot] in I2. rewrite u64_lit in I2 by lia.
unfold estart in I1, I2. cbn [a_base a_off] in I1, I2. apply CORE; lia.
Qed.
Lemma kimg_cut_sound : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "Q1'6'J%211'QK'SAyR0%211'8y8%511%311p051'QN%=11'C&R2r6r5r4r3%544321r7&Q?r2%23651%:44981p061pV8=1pU:>1pUN@1pR6C1pQ:L1pVLN1").
Proof.
intros segs E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
unfold kimg_cut1. destruct K; try (apply Forall_one; exact HKK).
lazymatch goal with |- Forall _ (if _ then [KImg ?a ?b] else _) => rename a into lo; rename b into hi end.
destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hc; [apply Forall_one; exact HKK|].
apply orb_false_iff in Hc as [Hc1 Hc2]. apply Z.leb_gt in Hc1. apply Z.leb_gt in Hc2.
cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Hnone).
apply Forall_app. split.
- destruct (Z.ltb lo a) eqn:Hl; [|constructor]. apply Z.ltb_lt in Hl. apply Forall_one. cbn [kentry_ok].
split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
- destruct (Z.ltb (a + n) hi) eqn:Hh; [|constructor]. apply Z.ltb_lt in Hh. apply Forall_one. cbn [kentry_ok].
split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
Qed.
Lemma reg_lit5 : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "B'7&Ar1uQ0%3221'>'C&SCy5&S@&RAr2%211%4251%7261%:3913p0<1pV8A1").
Proof.
intros n Hn. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia.
Qed.
Lemma regs_ok_post2 : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "S0'QK'6'QM%211&Q1y5'SAyR0%211%5241'7%516&R3r:r9r8%43321'=&A(1r7%3221uQ0%5231%7231r5%8271%9225%;221&@'>r6%23FB1%411'C&SC%12OF&RA%11I%93531%52Q3D%41J%<3821&R6r=r;%3221&QJr@%221Q4%D3Q:41r>%921Q6rA%721Q7%I3Q?31r1%K3Q>16%M11r2r<%O3QB21%Q111rBr3%F221rC%H213%Q63QL31p071p0<1pV@QL1&QOr?%23;1N%331?QN%R03:1Lp061p0G1p0M1p0Q61p0Q:1p0QA1p0QG1p0QL1p0R51pUHRD1pVDR<1pV<R>1pUFRG1pVBR?1pV:RA1pR:RC1pR8RD1pVNRK1pQ:RO1").
Proof.
intros E sr R R' n1 r1 e1 n2 r2 e2 HR Hn1 Hn2 Hne U1 U2 G1 G2 Gr.
assert (E1 : r1 = Z_to_bv 5 (Z.of_nat n1)) by (apply bv_eq; rewrite reg_lit5 by lia; exact U1).
assert (E2 : r2 = Z_to_bv 5 (Z.of_nat n2)) by (apply bv_eq; rewrite reg_lit5 by lia; exact U2).
pose proof (regs_ok_set_n E _ _ n2 e2 (edenot E e2) (regs_ok_set_n E sr R n1 e1 (edenot E e1) HR Hn1 eq_refl) Hn2 eq_refl) as K.
rewrite <- E1, <- E2 in K.
assert (Z1 : r1 <> 0%bv) by (intros H0; apply (f_equal bv_unsigned) in H0; rewrite U1 in H0; change (bv_unsigned (0%bv : bv 5)) with 0 in H0; lia).
assert (Z2 : r2 <> 0%bv) by (intros H0; apply (f_equal bv_unsigned) in H0; rewrite U2 in H0; change (bv_unsigned (0%bv : bv 5)) with 0 in H0; lia).
assert (Z12 : r1 <> r2) by (intros H0; apply (f_equal bv_unsigned) in H0; lia).
intros r. rewrite <- (K r).
destruct (bv_eqb r r2) eqn:Q2.
{ unfold bv_eqb in Q2. apply Z.eqb_eq in Q2. apply bv_eq in Q2. subst r. rewrite getr_same by exact Z2. exact G2. }
assert (N2 : r <> r2) by (intros ->; rewrite bv_eqb_refl in Q2; discriminate).
rewrite (getr_other _ r2 _ r N2).
destruct (bv_eqb r r1) eqn:Q1.
{ unfold bv_eqb in Q1. apply Z.eqb_eq in Q1. apply bv_eq in Q1. subst r. rewrite getr_same by exact Z1. exact G1. }
assert (N1 : r <> r1) by (intros ->; rewrite bv_eqb_refl in Q1; discriminate).
rewrite (getr_other _ r1 _ r N1). apply Gr; assumption.
Qed.
Fixpoint nb_lt (b : nat) (e : expr) : bool :=
match e with
| ELit _ => true
| EVar n => Nat.ltb n b
| EAlu _ a c | EAluw _ a c | EMd _ a c | EMdw _ a c => nb_lt b a && nb_lt b c
| EExt _ _ _ a => nb_lt b a
| EBlob _ _ _ _ => false
end.
Lemma edenot_ev_agree : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "Q4'7'QK'QM'>'3&Q;r4r1%3221(;%73621&Ar6%2261'SAyR0%211&QLr2%2271r5%4213%C3631p0:1pV8H1&QJr3%2271%32F2%J3=21p061p0E1pUDN1pQ<Q01pQ:Q11pU@Q31").
Proof.
intros b E E' e. induction e; cbn [nb_lt edenot]; intros H Hag; try reflexivity;
try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1 Hag), (IHe2 H2 Hag); reflexivity).
- apply Hag. apply Nat.ltb_lt. exact H.
- rewrite (IHe H Hag). reflexivity.
- discriminate.
Qed.
Lemma fetch_lit : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "Q3'6'J%211'C'SAyR0%211yQ0%411'>&SCr2%2271r3%53;21'8%118&Kr5%2216(2%12=:%=3631r6&S@%12D7%9231%72C>%C3<21p071p0@1pW<G1pW:J1pW>N1pVLQ01").
Proof.
intros segs z w x Hw Hf. replace (Z_to_bv 64 z) with w; [exact Hf|].
apply bv_eq. rewrite Z_to_bv_unsigned, <- Hw. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma with_ss_idem : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK ">'Q='R0'>&QBr3r2%3221r1%5221%6252%83:21pVJ:1pVH;1pUB=1").
Proof. reflexivity. Qed.
Lemma a_ss_with_ss : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "<'Q='R0'>&Q<&QBr2r1%3221%511%73813pVF91pUB;1").
Proof. reflexivity. Qed.
Lemma page_base_le' : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "J'SAyR0%211'=&R>&SC&Or1%211%4281%5293%7221&R?&R<+TP0%2261%4261'>'C&R@%12;6z%53421%D271%E2=1pU:G1").
Proof.
intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma page_in_ranges_bounds' : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "QE'SAyR0%211'6'9%1233%311'C'B'=&R>r3&SC&5r1%23==1%42?1%7261&R<&:%13BB6%92D1%4261r2%>221%@281qULE1%C3F1@'>'3&Q0&Or5%211r4%5221(;%93821r6%K2Q61%N261+1%H231+SoO%J2Q11%Q3231%Q5261p0:1p0E1pUJQ:1pV2Q;1pV0Q=1pU:QB1").
Proof.
intros a l lo hi Hl Hp. unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hin Hb]].
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (proj1 (Forall_forall _ _) Hl iv Hin) as [L1 L2].
pose proof (page_base_le' a) as (P1 & P2 & P3). unfold page_size in H2. lia.
Qed.
Lemma A_wf_allowA' : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "='Q>'QK'Q=&Q5&QDr3r2r1%43321%611pUB81pQ::1p2<1").
Proof.
intros A E cs. unfold A_wf, allowA. apply Forall_forall. intros iv Hin.
apply in_flat_map in Hin as [p [_ Hin]]. unfold allow1 in Hin.
pose proof (u64_range (edenot E (snd p))) as Hn. pose proof (u64_range (edenot E (fst p))) as Hb.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; unfold page_size.
- pose proof (pagedown_le (uE E (fst p))). pose proof (pageup_ge (uE E (fst p) + uE E (snd p))). unfold uE in *.
split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
- pose proof (pagedown_le (sh_lo A E p)). pose proof (pageup_ge (sh_hi A E p)). unfold sh_lo, sh_hi, uE in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Section NodesD.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Definition Hv (E : env) (cs : acs) (model : Model) : word -> bool := fun a => negb (vis A E cs model a).
Lemma Hv_hid : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "K'QK'Q='M'SAyR0%211'>'3&Q:r4r3r2r1%544321(;%93821&QFv0vRFr5%46321;:9%?3>17p071pU:B1pV6F1pUBH1pQ:J1").
Proof. intros E cs model a H. unfold hid, Hv in *. rewrite H. apply orb_true_r. Qed.
Lemma Hv_high : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "L'QK'Q='M'SAyR0%211&R>&QHr4%211&SCr1%2281%7241'>'3&Q:r5r3r2%443<21(4%83721p0:1pU:C1pV6G1pUBI1pQ:K1").
Proof.
intros E cs model a Ha. unfold Hv, vis. apply negb_false_iff.
replace (utop E <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Ha).
rewrite orb_true_r. reflexivity.
Qed.
Lemma Hv_hull : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "M'QK'Q='M'SAyR0%211'>'3&QGv0&SCr1%2281%5241(;%93821&Q:r5r4r3r2%544321(4%A3@21p091pU:D1pV6H1pUBJ1pQ:L1").
Proof. intros E cs model a Ha. unfold Hv, vis. rewrite Ha. reflexivity. Qed.
Lemma page_in_ranges_In' : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "QE'SAyR0%211'6'9%1233%311'>'3&Q0&Or2%211r1%5221(;%93821'?'=&R;r3%23@81&R>&SC&5%13GG<%32I1r4%52K1%7231&R<+1%2241&:%13Q0Q0E%<2Q21%62:1%?251%L1;%@2Q61%B2>1+TP0%<231%E217%J241%K281%L2A1%M2J1qULQ;1%Q02Q<1p0Q21pV0Q=1pU:QB1").
Proof.
intros a l Hp. unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hin Hb]].
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (page_base_le' a) as (P1 & P2 & P3). unfold page_size in H2. exists iv. repeat split; try assumption; lia.
Qed.
Lemma lazy_cover_vis : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "Q:'QK'Q=&Q1y5'SAyR0%211%5241'8y8%611%311p061'M'QEvR9v0vIvR:vRFvFr5r4r3r2r1%<;;:987654321&Q7&Q:r6%23196&N%118&QD%13B5=%83531p0:1pV6H1pQ@J1pR8Q01pUBQ71pQ:Q91").
Proof.
intros E cs R FULL model HC w Hlz Hh. unfold Hv in Hh.
apply negb_false_iff in Hh. unfold vis in Hh. rename Hh into Hv0.
destruct (page_in_ranges_In' w _ Hlz) as (iv0 & Hin0 & B1 & B2 & B3 & B4).
pose proof (proj1 (Forall_forall _ _) (co_lazyb _ _ _ _ _ _ _ _ _ _ _ HC) iv0 Hin0) as [L1 L2].
pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (H0 & H1 & H2 & H3).
apply orb_prop in Hv0 as [Hv0|Hv0].
- apply orb_prop in Hv0 as [Hv0|Hv0].
+ unfold in_hull in Hv0. apply andb_prop in Hv0 as [Hv1 Hv0]. apply Z.leb_le in Hv1. apply Z.ltb_lt in Hv0. exfalso. lia.
+ apply Z.leb_le in Hv0. exfalso. lia.
- apply andb_prop in Hv0 as [_ Hv0]. rewrite Hlz in Hv0. cbn [negb orb] in Hv0.
pose proof (page_base_le' w) as (P1 & P2 & P3).
unfold page_allowedb, allowA. apply existsb_exists. unfold page_size.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
unfold in_allow in Hv0. apply orb_prop in Hv0 as [Hv0|Hv0].
+ unfold in_vis in Hv0. apply existsb_exists in Hv0 as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
exists (pagedown (uE E (fst p)), pageup (uE E (fst p) + uE E (snd p))). split.
* apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hin|]. left. reflexivity.
* cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
+ unfold in_sh in Hv0. apply existsb_exists in Hv0 as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
exists (pagedown (sh_lo A E p), pageup (sh_hi A E p)). split.
* apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hin|]. right. left. reflexivity.
* cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma lazy_cover_hid : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "Q:'QK'Q=&Q1y5'SAyR0%211%5241'8y8%611%311p061'M'QEvR9v0vIvR:vRFvFr5r4r3r2r1%<;;:987654321&Q7&QFr6%25>;196&N%118&QD%13B5=%83531p0:1pV6H1pQ@J1pR8Q01pUBQ71pQ:Q91").
Proof.
intros E cs R FULL model HC w Hlz Hh. apply (lazy_cover_vis E cs R FULL model HC w Hlz).
unfold Hv. unfold hid in Hh. apply orb_false_iff in Hh as [_ Hh]. exact Hh.
Qed.
Lemma H_off_segments_vis : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK ">'QK'Q='M&Q6vR9&Q:r3r2r1%43321%7261pV691pUB;1pQ:=1").
Proof.
intros E cs model a Hh. unfold Hv in Hh. apply negb_true_iff in Hh. unfold vis in Hh.
apply orb_false_iff in Hh as [Hh _]. apply orb_false_iff in Hh as [Hh _].
apply SEGS_in_hull. exact Hh.
Qed.
Lemma mrestrict_Hv_high : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "Q4'QK'Q='M'SAyR0%211'8y8%511%311p051&R>&QHr5%211&SCr1%22=1%7241'>&Q8&Q:r6r4%332;1r3r2%73321%312%:3D21p0<1pU:J1pQ@F1pV6O1pUBQ11pQ:Q31").
Proof. intros. unfold mrestrict. rewrite Hv_high by assumption. reflexivity. Qed.
Lemma Mr_grows_Hv : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "M'QK'Q='M'SAyR0%211'8y8%511%311p051&R8&QCv0vRFr4r3r2r1%76654321&Q8&Q:%13765%3215%=251pQ@?1pV6H1pUBJ1pQ:L1").
Proof.
intros E cs model FULL a. unfold Mr, mrestrict, hid, Hv.
destruct (argH E a), (vis A E cs model a); cbn; auto.
Qed.
Lemma munrestrict_mrestrict : ltac2:(TCodec.tc2 tcn__AsanNodesAuxK "D'SAyR0%211'3p021'8y8%711%311p071'>&Q9r2r1&Q8%1232%53431%73814pQ@91pQB?1").
Proof.
intros H FULL. apply functional_extensionality. intros a. unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.
End NodesD.
