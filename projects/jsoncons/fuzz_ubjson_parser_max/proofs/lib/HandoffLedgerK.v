(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec AgentLib AsanAcct BackingAlgebra AsanPlacement AxSymExec3K AxSymExec3SoundK AxSymRun3K
AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK HandoffBridgeK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__HandoffLedgerK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BackingAlgebra."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HandoffLedgerK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HandoffLedgerK.Ledger."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0BL"; "1None"; "1Some"; "1app"; "1bool"; "1false"; "1fst"; "1list"; "1option"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2ex"]; ["2not"; "2or"; "3Z"; "0E"; "0FS0"; "0FULL"; "0LIMIT"; "0LL"; "4Segment"; "5find_segment"; "6Model"; "6alloc_top"; "6iv_subtract"; "6m_vm_lazy"; "6m_vmmaps"; "6maps_subtract"]; ["6page_base"; "6page_in_ranges"; "6vm_maps"; "6vm_noaccess"; "7bvmap"; "0R"; "8mkH"; "9HCons"; "9KRWLAZY"; "9a_ghost"; "9a_hlz"; "9a_hna"; "9a_maps"; "9a_vis"; "9acs"; "9am_base"]; ["9am_kind"; "9am_len"; "9amap"; "9amap_eqb"; "9e_sp0"; "9hop"; "9kn"; "9mkind"; "9no_fog"; ":allowA"; ":cs_ok"; ":hreplay"; ":in_ivs"; ":seps"; ":uE"; ";ELit"]; [";edenot"; ";env"; ";expr"; "<B"; "<S"; "<covered"; ">SHB_LEN"; ">SHB_LO"; ">vis_off_band"; ">vis_sh_wr"; "=hops_in_maps"; "0SEGS"; "0SINV"; "?In"; "?NoDup"; "?existsb"]; ["?forallb"; "@add"; "@le"; "@lt"; "@pow"; "@sub"; "0a"; "0argH"; "0b"; "0cs"; "0h"; "0hi"; "0l"; "0lo"; "0m"; "0model"]; ["0ms"; "0n"; "0p"; "0q"; "0q'"; "AZ_to_bv"; "Abv"; "Abv_unsigned"; "0sz"; "0z"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma hl_covered_in_ivs : ltac2:(TCodec.tc2 tcn__HandoffLedgerK "C'8':'S6yR0%211%4211%611'B'>'5&R5r2r1%3221&QL%1234%83731pVD:1pUJ<1").
Proof. intros l z. unfold BackingAlgebra.covered, in_ivs. induction l as [|q l IH]; [reflexivity|]. cbn [existsb]. rewrite IH. reflexivity. Qed.
Lemma hl_seps_apart : ltac2:(TCodec.tc2 tcn__HandoffLedgerK "Q:'8':'S6yR0%211%4211%611'QMr1%211&R=r2r4%33821r5%53:41&@'>r3%23>71%411'A&RB&RA&R3%11;&R4%11=%5231%51A%8221%51C%9231%;218%=241p0?1p0E1p0H1pV:Q11pV8Q21p0O1pUJQ31").
Proof.
intros l Hs. induction Hs as [|p l Hp Hs IH]; intros q q' Hq Hq' Hne; [destruct Hq|].
unfold BackingAlgebra.B, BackingAlgebra.S in *.
destruct Hq as [<-|Hq]; destruct Hq' as [<-|Hq'].
- congruence.
- exact (proj1 (Forall_forall _ _) Hp q' Hq').
- pose proof (proj1 (Forall_forall _ _) Hp q Hq) as D. unfold iv_disjoint in D. lia.
- exact (IH q q' Hq Hq' Hne).
Qed.
Lemma hl_seps_nodup : ltac2:(TCodec.tc2 tcn__HandoffLedgerK "L'8':'S6yR0%211%4211%611'QMr1%211&R=r3%23741&RCz&S7&;r2%23>>1%42@1%7261p091pV8A1'R>%12C=p031p0A1pUJE1").
Proof.
intros l Hs. induction Hs as [|p l Hp Hs IH]; intros Hpos; [constructor|].
constructor.
- intros Hin. pose proof (proj1 (Forall_forall _ _) Hp p Hin) as D. unfold iv_disjoint in D.
pose proof (Hpos p (or_introl eq_refl)). lia.
- apply IH. intros q Hq. apply Hpos. right. exact Hq.
Qed.
Lemma hl_iv_subtract : ltac2:(TCodec.tc2 tcn__HandoffLedgerK "QF'S6yR0%211'B':%1233&RB&RA&S7r5%2291r4%42;1%6231&RD+2+R0%3221%<251&RCz%221;&R=r3&Lr7r6%3421B@%63G51'=&;%13MMD%H2O1%>2=1r8%K2Q21&7%13Q3Q3J%N2Q51%Q1241%Q1228%Q12Q8@%Q3271%Q5231%?251%@2<1p0B1p0J1p0N1pV8Q<1pUHQ?1pULQ@1pVBQB1pU>QC1").
Proof.
intros a sz lo hi q Hwf Hpos Hin. unfold iv_subtract in Hin.
pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
apply in_app_or in Hin as [Hin|Hin].
- destruct (bv_unsigned a <? lo) eqn:Hc; [|destruct Hin]. apply Z.ltb_lt in Hc.
destruct Hin as [<-|[]]. cbn [fst snd]. rewrite u64_lit by lia. lia.
- destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Hc; [|destruct Hin]. apply Z.ltb_lt in Hc.
destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.
Lemma hl_maps_subtract : ltac2:(TCodec.tc2 tcn__HandoffLedgerK "R5'8':'S6yR0%211%4211%611'B&R=r1r5%33621'=&RB&RA&S7&7r2%23>>1%42@1&;%13AA4%72C1%9241&RD+2+R0%3221%?251&RCz%2219%D241p0F1pV6M1&Or4r3%33L21%O3Q2F1%D3Q4Q43%J2Q61%=2<1'?r7%Q53Q8Q41%N3Q:Q:Q5%Q02Q<1%Q03Q<Q<<%Q22Q>1%Q5231%O3Q?Q??%Q52QA1%Q7241%Q23QBQBQ=%Q82QD1%Q:291%Q<241%Q>281%Q?2>1qV6QG1%B2QH1%QB2D1p0H1p0N1pV8QL1pUHQK1pULQL1pUJQN1").
Proof.
induction l as [|[a sz] l IH]; intros lo hi q Hl Hin; [destruct Hin|].
cbn [maps_subtract] in Hin. apply in_app_or in Hin as [Hin|Hin].
- destruct (Hl (a, sz) (or_introl eq_refl)) as [W P]. cbn [fst snd] in W, P.
destruct (hl_iv_subtract a sz lo hi q W P Hin) as (Q1 & Q2 & Q3).
split; [exact Q1|]. exists (a, sz). split; [left; reflexivity|]. cbn [fst snd]. lia.
- destruct (IH lo hi q (fun p Hp => Hl p (or_intror Hp)) Hin) as (Q1 & p & Hp & Q2 & Q3).
split; [exact Q1|]. exists p. split; [right; exact Hp|]. lia.
Qed.
Lemma hl_replay : ltac2:(TCodec.tc2 tcn__HandoffLedgerK "R>'R1'8'QE%211'R2&R=(Q7r2r1%3221r3%63921'=&RB&RA&QNr5%2217%322;%5221&RD+2+R0%3221%;251&RCz%2219%@241p0B1pV4J1pUBK1':'S6yR0%211%4211&QKr4%221M%Q334Q01&S7&;%1388Q4%32:1%D2C1&7%13<<Q8%72>1%Q3215%Q521K'?r6%Q@3QCQ<1r7%Q821Q@%:3EEB%@2G1%Q=231%A3HHE%C2J1%Q?241%Q?28QF%QA281%QC231%QE271%QF2=1qV4QO1%A2R01qUBR11%C2R21%QK2E1%QL2K1p0Q11pV8Q61p0Q<1pUFR91pQ8R=1").
Proof.
intros E h. induction h as [|hop h IH]; intros Hh q Hin; [destruct Hin|].
destruct hop as [b n|b n]; cbn [hreplay] in Hin.
- destruct Hin as [<-|Hin].
+ destruct (Hh b n (or_introl eq_refl)) as [W P]. cbn [fst snd]. unfold uE in *.
split; [exact P|]. split; [exact W|]. exists b, n. split; [left; reflexivity|]. lia.
+ destruct (IH (fun b' n' H' => Hh b' n' (or_intror H')) q Hin) as (Q1 & Q2 & b' & n' & Hb & Q3 & Q4).
split; [exact Q1|]. split; [exact Q2|]. exists b', n'. split; [right; exact Hb|]. lia.
- assert (IH' := IH (fun b' n' H' => Hh b' n' (or_intror H'))).
destruct (hl_maps_subtract (hreplay E h) _ _ q (fun p Hp => let '(conj P1 (conj P2 _)) := IH' p Hp in conj P2 P1) Hin) as (Q1 & p & Hp & Q2 & Q3).
destruct (IH' p Hp) as (P1 & P2 & b' & n' & Hb & P3 & P4).
split; [exact Q1|]. split; [lia|]. exists b', n'. split; [right; exact Hb|]. lia.
Qed.
Lemma hl_in_amapb : ltac2:(TCodec.tc2 tcn__HandoffLedgerK "C'QB'8%112'>'5&R?&QCr2%211r1%53:21(<%93821&R=r3%23?18p041pV2?1pUNB1").
Proof. intros m ms H. apply existsb_exists in H as (m' & Hin & Heq). apply amap_eqb_eq in Heq. subst m'. exact Hin. Qed.
Definition len_within (n len : expr) : bool :=
(expr_eqb len n || match n, len with ELit z, ELit L => (Z.ltb 0 z && Z.leb z L && Z.ltb L (2 ^ 64))%bool | _, _ => false end)%bool.
Definition hop_in_maps (ms : list amap) (hp : hop) : bool :=
match hp with
| HCons b n => existsb (fun m => negb (is_fog m) && expr_eqb (am_base m) b && len_within n (am_len m))%bool ms
| HSub _ _ => true
end.
Definition hops_in_maps (ms : list amap) (h : list hop) : bool := forallb (hop_in_maps ms) h.
Section Ledger.
Variable SEGS : list Segment.
Variable A : atable.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation HID := (hid A argH).
Let HSd : nat -> option acs := fun _ => None.
Let XNd : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let XEd : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let XBd : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
#[local] Notation PIRI := (page_in_ranges_In HSd XNd XEd XBd 0%nat).
#[local] Notation PBLE := (page_base_le HSd XNd XEd XBd 0%nat).
Lemma hl_alloc_top : ltac2:(TCodec.tc2 tcn__HandoffLedgerK "Q?'R1'Q>&Q4y5'S6yR0%211%5241'9y8%611%311p061'J'QJvR;v0vFvR<vRGvDr5r4r3r2r1%<;;:987654321'>'B&K&N%117%311&RE&QNr6&QD%3221+XPPP0%6221%=3<81p0?1pV0M1pQ<O1pR<Q51pUDQ<1pQ8Q>1").
Proof.
intros E cs R FULL model HC. destruct (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as (H1 & _). unfold alloc_top, stack_max_size. rewrite H1. reflexivity.
Qed.
Lemma hl_maps_pos : ltac2:(TCodec.tc2 tcn__HandoffLedgerK "R2'R1'Q>&Q4y5'S6yR0%211%5241'9y8%611%311p061'J':%1299'QJvR;v0vFvR<vRGvDr6r5r4r3r2%<;;:987654321&R=&Q2&N%116%311%53C71'=&RCz&S7&;%13Q2Q2>%32Q41%6251&RB&RA&7%13Q8Q8D%92Q:1%4217&RE&QNr8&QD%3221+XPPP0%6221%=281%F2?1p0H1p0O1pV8Q=1pV0Q@1pQ<QB1pR<QH1pUDQO1pQ8R11").
Proof.
intros E cs R FULL model q HC Hin.
pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) q Hin) as (P1 & _ & _ & _ & P5).
pose proof (utop_bounds E). split; [exact P1 | lia].
Qed.
Lemma hl_hop_in_maps : ltac2:(TCodec.tc2 tcn__HandoffLedgerK "RM'R1'Q>&Q4y5'S6yR0%211%5241'9y8%611%311p061'J'8'QE%211'QJvR;v0vFvR<vRGvDr6r5r4r3r2%<;;:987654321'>'5&QH&Q<%11:%311(<%73621&R:r7%711%321>%<3;16'R2&R=(Q7r1%22C1%43Q11H'?':%12Q=Q='=&Q2&Nr9%211%411%>37<1&7%13QFQF>&R0r=%221Q5%Q23QJ41&RCz&QN%126Q9%4231&RB&S7&;%13R3R3K%32R51%5271%H271%I2=1%J2D1qV8L1%O2M1p0Q11pV4Q71pUBQ81p0Q:1p0Q@1p0QI1pUFR71pV0R;1pQ<R=1pR<RC1pUDRJ1pQ8RL1").
Proof.
intros E cs R FULL model h HC Hnf Hh b n Hin.
pose proof (proj1 (forallb_forall _ _) Hh _ Hin) as Hb. cbn [hop_in_maps] in Hb.
apply existsb_exists in Hb as (m & Hm & Hb). apply andb_prop in Hb as [Hb Hn]. apply andb_prop in Hb as [_ Hb].
apply expr_eqb_eq in Hb. subst b.
assert (Hq : In (amap_den E m) (vm_maps (m_vmmaps model))).
{ rewrite (hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC Hnf). apply in_map_iff. exists m. split; [reflexivity | exact Hm]. }
exists (amap_den E m). split; [exact Hq|]. split; [reflexivity|].
pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) _ Hq) as (P1 & _).
unfold amap_den in *. cbn [fst snd] in *. unfold len_within in Hn. apply orb_prop in Hn as [Hn|Hn].
- apply expr_eqb_eq in Hn. rewrite <- Hn. unfold uE. lia.
- destruct n as [z|n0|o a1 a2|o a1 a2|o a1 a2|o a1 a2|sx lo0 n0 e0|sx k0 i0 n0]; try discriminate.
destruct (am_len m) as [L|n1|o b1 b2|o b1 b2|o b1 b2|o b1 b2|sx lo1 n1 e1|sx k1 i1 n1]; try discriminate.
apply andb_prop in Hn as [Hn H3]. apply andb_prop in Hn as [H1 H2]. apply Z.ltb_lt in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
unfold uE. cbn [edenot]. rewrite !u64_lit by lia. lia.
Qed.
Lemma hl_hops_ok : ltac2:(TCodec.tc2 tcn__HandoffLedgerK "R>'R1'Q>&Q4y5'S6yR0%211%5241'9y8%611%311p061'J'8'QE%211'QJvR;v0vFvR<vRGvDr6r5r4r3r2%<;;:987654321'>'5&QH&Q<%11:%311(<%73621&R:r7%711%321>%<3;16'R2&R=(Q7r1%22C1%43Q11H'=&RB&RA&QNr<%221K%322K%5221&RD+2+R0%3221%;251&RCz%2219%@241p0B1pV4H1pUBI1p0K1p0Q11p0Q:1pUFQH1pV0QL1pQ<QN1pR<R41pUDR;1pQ8R=1").
Proof.
intros E cs R FULL model h HC Hnf Hh b n Hin.
destruct (hl_hop_in_maps E cs R FULL model h HC Hnf Hh b n Hin) as (q & Hq & Hb & Hn).
destruct (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W & _).
pose proof (W _ Hq) as Wq. unfold BackingAlgebra.iv_wf, BackingAlgebra.B, BackingAlgebra.S in Wq. rewrite Hb in Wq. unfold uE in *. lia.
Qed.
Lemma hl_noacc_pos : ltac2:(TCodec.tc2 tcn__HandoffLedgerK "R3'R1'Q>&Q4y5'S6yR0%211%5241'9y8%611%311p061'J'QJvR;v0vFvR<vRGvDr5r4r3r2r1%<;;:987654321'>'5&QH&Q<%11:%311(<%73621&R:r6%711&Q;%113%5231%>3=18':%12Q5Q5&R=&Q3&N%11J%311%536H1&RCz&S7&;%13Q@Q@N%32QB1%6251p081pV8?1p0B1p0J1p0Q31pV0QA1pQ<QC1pR<QI1pUDR01pQ8R21").
Proof.
intros E cs R FULL model HC Hnf Hh q Hin. rewrite (co_hna _ _ _ _ _ _ _ _ _ _ _ HC) in Hin.
exact (proj1 (hl_replay E (a_hna cs) (hl_hops_ok E cs R FULL model _ HC Hnf Hh) q Hin)).
Qed.
Lemma hl_lazy_in : ltac2:(TCodec.tc2 tcn__HandoffLedgerK "R>'R1'Q>&Q4y5'S6yR0%211%5241'9y8%611%311p061'J'QJvR;v0vFvR<vRGvDr5r4r3r2r1%<;;:987654321'>'5&QH&Q<%11:%311(<%73621&R:r6%711&Q:%113%5231%>3=18&Q1&Q0%11C&M%11I%5231%E3D1?'=&QL&S7%12Q?L&Q2&N%11C%311%7251%O3N1I'H%QD11&I+1%23Q@;1(2%116%Q73631%B291p0D1pU>QO1p0M1p0Q51p0Q>1pV0QL1pQ<QN1pR<R41pUDR;1pQ8R=1").
Proof.
intros E cs R FULL model HC Hnf Hh a Hp.
destruct (PIRI a _ Hp) as (iv & Hiv & B1 & B2 & _ & _).
split.
- rewrite (co_hlz _ _ _ _ _ _ _ _ _ _ _ HC) in Hiv.
destruct (hl_replay E (a_hlz cs) (hl_hops_ok E cs R FULL model _ HC Hnf Hh) iv Hiv) as (_ & _ & b & n & Hb & Q1 & Q2).
destruct (hl_hop_in_maps E cs R FULL model _ HC Hnf Hh b n Hb) as (q & Hq & Hqb & Hqn).
unfold in_ivs. apply existsb_exists. exists q. split; [exact Hq|]. rewrite Hqb. unfold uE in *.
apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply SEGS_in_hull.
pose proof (proj1 (Forall_forall _ _) (co_lazyb _ _ _ _ _ _ _ _ _ _ _ HC) iv Hiv) as [L1 _].
unfold in_hull. destruct L1 as [L1|L1]; apply andb_false_iff; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
Qed.
Lemma hl_hidden_zero : ltac2:(TCodec.tc2 tcn__HandoffLedgerK "R?'R1'Q>&Q4y5'S6yR0%211%5241'9y8%611%311p061'J'QJvR;v0vFvR<vRGvDr5r4r3r2r1%<;;:987654321'>'5&QH&Q<%11:%311(<%73621&R:r6%711&Q:%113%5231%>3=18&Q6&M%11G&QIr9r8%33Q021%7351H%G3F1A&QL&S7%12Q@M&Q3&N%11D%311%7251(6%Q13Q021%>1Q6(3&S5z%22QH1%42QH1%Q83QH61p081p0C1pU>R01p0N1p0Q61p0Q?1pV0QM1pQ<QO1pR<R51pUDR<1pQ8R>1").
Proof.
intros E cs R FULL model HC Hnf Hh a Hm Hna. unfold mkH in Hm. apply andb_prop in Hm as [Hlz Hal]. apply negb_true_iff in Hal.
destruct (hl_lazy_in E cs R FULL model HC Hnf Hh a Hlz) as [Hin _].
assert (Hhid : HID E cs model a = true).
{ destruct (HID E cs model a) eqn:Hh'; [reflexivity|]. exfalso.
pose proof (lazy_cover_cs SEGS A LIMIT HSd XNd XEd XBd HULL_ok SINV argH FS0 0%nat E cs R FULL model HC a Hlz Hh') as Hc. congruence. }
apply (hb_zero SEGS A LIMIT SINV argH FS0 E cs R FULL model a HC Hhid Hin Hna Hlz).
destruct (in_ghost E cs (bv_unsigned a)) eqn:Hg; [exfalso | reflexivity].
unfold in_ghost in Hg. apply existsb_exists in Hg as [p [Hp Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
assert (Hc : page_allowedb (allowA A E cs) (page_base a) = true); [|congruence].
pose proof (PBLE a) as (P1 & P2 & P3).
unfold page_allowedb, allowA. apply existsb_exists.
exists (pagedown (uE E (fst p)), pageup (uE E (fst p) + uE E (snd p))). split.
- apply in_flat_map. exists p. split; [apply in_or_app; right; exact Hp|]. left. reflexivity.
- cbn [fst snd]. unfold page_size.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Definition SHB_LO : Z := 0x7fff7000.
Definition SHB_LEN : Z := 0x100000001000.
Definition vis_sh_wr (k : list kentry) (p : expr * expr) : bool :=
let '(sb, sk, sn) := shadow_of A k (fst p) (snd p) in
(Z.leb 3 (ealign k (fst p)) && flat_x k sb sk sn && existsb (kentry_eqb (KWr (SA sb sk) sn)) k)%bool.
Definition vis_off_band (k : list kentry) (p : expr * expr) : bool :=
let '(bb, bk) := split_lit (fst p) in
(flat_x k bb bk (snd p) && ranges_apart_x k (ELit SHB_LO) 0 (ELit SHB_LEN) bb bk (snd p))%bool.
Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis HULL_below : img_hi A <= SHB_LO.
Lemma hl_off_band : ltac2:(TCodec.tc2 tcn__HandoffLedgerK "R9'R1'Q>&Q4y5'S6yR0%211%5241'9y8%611%311p061'J':'R2%2211'B'QJvR;v0vFvR<vRGvDr7r6r5r4r3%<;;:987654321'>'5&R8&QF%11:%3217(<%73621'=&RB&QNr9&7%13MM@%4231%621A&RC&RA&;%13Q3Q3F%:291%4271%62H1%?281&@&R7%A21M&R6%;231%=2Q01%F241%711p091p0J1p0Q31pVDQA1pV6QC1pV0QG1pQ<QI1pR<QO1pUDR61pQ8R81").
Proof.
intros E cs R FULL model p z HC Hv Hz Hband. unfold vis_off_band in Hv.
destruct (split_lit (fst p)) as [bb bk] eqn:Hsp. apply andb_prop in Hv as [Hf Hap].
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
pose proof (flat_x_sound SEGS E _ (kn cs) bb bk (snd p) HK Hf) as (F1 & F2 & F3).
pose proof (split_lit_denot E _ bb bk Hsp) as Hd.
assert (Hb : uE E (fst p) = estart E (SA bb bk)).
{ unfold uE. rewrite Hd. unfold estart in *; cbn [a_base a_off] in *. pose proof (u64_range (edenot E (snd p))). rewrite u64_lit by lia. reflexivity. }
pose proof (ranges_apart_x_sound SEGS E _ (kn cs) _ _ _ _ _ _ HK Hap) as D.
unfold estart, elenZ in *. cbn [a_base a_off edenot] in *.
unfold SHB_LO, SHB_LEN in *. rewrite !u64_lit in D by lia. unfold uE in *. lia.
Qed.
Lemma hl_shadow_defined : ltac2:(TCodec.tc2 tcn__HandoffLedgerK "SO'R1'Q>&Q4y5'S6yR0%211%5241'9y8%611%311p061'J'QJvR;v0vFvR<vRGvDr5r4r3r2r1%<;;:987654321'>'5&QH&Q<%11:%311(<%73621&R@':'R2%2211&R9&QFr6%211%411&Q=%114%;3831%D3C1>&R8r7%:11%311&4%914&Q9%116%43B31%F3C61%O3N1I'QB'B&R=r;%Q111%335Q91'QG&Q@%11Q=(Q8%Q:3421&Q?%11QB(QO%11QC%Q?3Q531&QA%11Q3%QB3Q814&RB&R7%221Q7z%421Q9&RAr8%221Q4&R6%4281%:231'=r:&S7%12RGR3%?231&RCr9%=261%3251%9251&@rB%11R=(2%11RM%R=3RM31%611p081pU>S51p0D1p0K1p0N1p0Q21p0Q61p0Q<1p0QB1pQ@QG1p4QH1pUNQJ1p0QL1p0R81p0RF1p0RO1pV0S=1pQ<S?1pR<SE1pUDSL1pQ8SN1").
Proof.
intros E cs R FULL model HC Hnf Hwr Hoff m BL LL Hm Hk Hbase Hlen HB HL HBL a Ha.
unfold SHB_LO, SHB_LEN in *.
assert (Hden : bv_unsigned (edenot E (am_base m)) = BL /\ bv_unsigned (edenot E (am_len m)) = LL).
{ rewrite Hbase, Hlen. cbn [edenot]. rewrite !u64_lit by lia. auto. }
destruct Hden as [D1 D2].
destruct (hb_lazykind SEGS A LIMIT SINV argH FS0 E cs R FULL model m a HC Hm Hk ltac:(rewrite D1, D2; exact Ha)) as [Hna Hlz].
assert (Hin : in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true).
{ rewrite (hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC Hnf). unfold in_ivs. apply existsb_exists.
exists (amap_den E m). split; [apply in_map; exact Hm|]. unfold amap_den. cbn [fst snd]. rewrite D1, D2.
apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
pose proof (proj1 (forallb_forall _ _) Hoff) as Hoff'.
destruct (HID E cs model a) eqn:Hh.
-
assert (Hg : in_ghost E cs (bv_unsigned a) = false).
{ destruct (in_ghost E cs (bv_unsigned a)) eqn:Hg; [exfalso | reflexivity].
unfold in_ghost in Hg. apply existsb_exists in Hg as [p [Hp Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
apply (hl_off_band E cs R FULL model p (bv_unsigned a) HC (Hoff' p (in_or_app _ _ _ (or_intror Hp))) (conj Hb1 Hb2)).
unfold SHB_LO, SHB_LEN. lia. }
rewrite (hb_zero SEGS A LIMIT SINV argH FS0 E cs R FULL model a HC Hh Hin Hna Hlz Hg). discriminate.
-
rewrite hb_hid_unfold in Hh. apply orb_false_iff in Hh as [_ Hv]. apply negb_false_iff in Hv. unfold vis in Hv.
pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (HU0 & HU1 & HU2 & HU3).
destruct (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & (SPlo & _) & _).
pose proof (utop_bounds E) as UT. unfold sp_window_lo in SPlo.
apply orb_prop in Hv as [Hv|Hv].
{ exfalso. apply orb_prop in Hv as [Hv|Hv].
- unfold in_hull in Hv. apply andb_prop in Hv as [_ Hv]. apply Z.ltb_lt in Hv. lia.
- apply Z.leb_le in Hv. lia. }
apply andb_prop in Hv as [_ Hv]. rewrite Hlz in Hv. cbn [negb orb] in Hv. unfold in_allow in Hv.
apply orb_prop in Hv as [Hv|Hv].
{ exfalso. unfold in_vis in Hv. apply existsb_exists in Hv as [p [Hp Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
apply (hl_off_band E cs R FULL model p (bv_unsigned a) HC (Hoff' p (in_or_app _ _ _ (or_introl Hp))) (conj Hb1 Hb2)).
unfold SHB_LO, SHB_LEN. lia. }
unfold in_sh in Hv. apply existsb_exists in Hv as [p [Hp Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
pose proof (proj1 (forallb_forall _ _) Hwr p Hp) as Hw. unfold vis_sh_wr in Hw.
destruct (shadow_of A (kn cs) (fst p) (snd p)) as [[sb sk] sn] eqn:Hso.
apply andb_prop in Hw as [Hw Hkw]. apply andb_prop in Hw as [Hal Hfl]. apply Z.leb_le in Hal.
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
destruct (shadow_of_val SEGS A SHADOW_ok E _ (kn cs) (fst p) (snd p) sb sk sn HK Hso Hfl) as [S1 S2].
destruct (ealign_sound SEGS E _ (kn cs) (fst p) HK) as [[A0 A1] [q Hq]].
assert (H8 : exists q8, bv_unsigned (edenot E (fst p)) = 8 * q8).
{ exists (q * 2 ^ (ealign (kn cs) (fst p) - 3)). rewrite Hq.
replace (2 ^ ealign (kn cs) (fst p)) with (2 ^ (ealign (kn cs) (fst p) - 3) * 2 ^ 3) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
change (2 ^ 3) with 8. ring. }
destruct H8 as [q8 H8].
apply existsb_exists in Hkw as (K & HKin & HKeq). apply kentry_eqb_eq in HKeq. subst K.
pose proof (proj1 (Forall_forall _ _) HK _ HKin) as HKW. cbn [kentry_ok] in HKW. destruct HKW as [Hflat HKW].
pose proof (u64_range (edenot E (fst p))) as Rb. pose proof (u64_range (edenot E (snd p))) as Rn.
pose proof SHADOW_ok as SO; unfold shadow_ok in SO.
unfold sh_lo, sh_hi, uE in Hb1, Hb2. rewrite H8 in Hb1, Hb2, S1.
assert (E1 : 8 * q8 / 8 = q8) by (rewrite Z.mul_comm; apply Z.div_mul; lia).
assert (E2 : (8 * q8 + bv_unsigned (edenot E (snd p))) / 8 = q8 + bv_unsigned (edenot E (snd p)) / 8).
{ rewrite Z.add_comm, Z.mul_comm. rewrite Z.div_add by lia. lia. }
rewrite E1 in Hb1, S1. rewrite E2 in Hb2.
assert (Hq8 : 0 <= q8 < 2 ^ 61) by lia.
rewrite Z.mod_small in S1 by lia.
set (d := bv_unsigned a - estart E (SA sb sk)).
assert (Hd : 0 <= d /\ d + Z.of_nat 1 <= elenZ E sn) by (unfold d; rewrite S1, S2; lia).
pose proof (HKW d 1%nat (proj1 Hd) (proj2 Hd)) as Hst.
replace (Z_to_bv 64 (estart E (SA sb sk) + d)) with a in Hst
by (unfold d; replace (estart E (SA sb sk) + (bv_unsigned a - estart E (SA sb sk))) with (bv_unsigned a) by ring; symmetry; apply Z_to_bv_bv_unsigned).
destruct (hb_mr_store_ok SEGS A argH SEGS_in_hull HULL_ok argH_high E cs model FULL a 1 Hst) as [Hst' _].
cbn [store_ok] in Hst'. unfold wview in Hst'. intros Hnone. rewrite Hnone in Hst'.
rewrite (SEGS_in_hull a) in Hst'; [discriminate|].
unfold in_hull. apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.
End Ledger.
