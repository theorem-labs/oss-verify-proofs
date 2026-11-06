(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AgentLib AxSymExec3K AxSymExec3SoundK AsanPlanCoreK AsanPlanK AsanPlanSoundK HandoffLedgerK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__HandoffLazyK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1bool"; "1cons"; "1fst"; "1list"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "0E"; "4iv_subtract"; "4maps_subtract"]; ["4page_base"; "4page_in_ranges"; "5HCons"; "5HSub"; "5hop"; "6hreplay"; "6uE"; "7env"; "7expr"; "8In"; "9add"; "9le"; "9lt"; "9pow"; "0a"; "0b"]; ["0bS"; "0h1"; "0h2"; "0hi"; "0l"; "0lazy"; "0lo"; "0n"; "0nS"; "0p"; "0q"; ":bv"; ":bv_unsigned"; "0sz"; "0w"]]).
Lemma hl_iv_subtract_apart : ltac2:(TCodec.tc2 tcn__HandoffLazyK "Q<'Q;yR0%211'<'5%1233&K&J&Q<r5%2291r4%42;1%6231&M+2+R0%3221%<251&Ir2&>r6r3%342?=1%63D51';&3%13JJ5%E2L1&6%13MM8%H2O1%J241%L21I%M2H6%:221p0<1p0D1pRFQ21pR8Q51pR>Q61pRLQ81pQNQ91").
Proof.
intros a sz lo hi q Hwf Hin. unfold iv_subtract in Hin.
pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
apply in_app_or in Hin as [Hin|Hin].
- destruct (bv_unsigned a <? lo) eqn:Hc; [|destruct Hin]. apply Z.ltb_lt in Hc.
destruct Hin as [<-|[]]. cbn [fst snd]. rewrite u64_lit by lia. left. lia.
- destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Hc; [|destruct Hin]. apply Z.ltb_lt in Hc.
destruct Hin as [<-|[]]. cbn [fst snd]. rewrite (u64_lit (Z.max (bv_unsigned a) hi)) by lia. right. lia.
Qed.
Lemma hl_maps_subtract_apart : ltac2:(TCodec.tc2 tcn__HandoffLazyK "QB'4'5'Q;yR0%211%4211%611'<&Ir1r5%33621&K&J&Q<&3r2%23==1%42?1&6%13@@4%72B1%9241&M+2+R0%3221%?251p0A1pRDH1&?r4r3%33G21%J3MB1';%E3Q0Q04%G2Q21%C3Q2Q26%I2Q41%K231%M21O%N2;5%8221p0:1p0@1pRFQ91pR8Q81pR>Q91pR:Q;1").
Proof.
induction l as [|[a sz] l IH]; intros lo hi q Hl Hin; [destruct Hin|].
cbn [maps_subtract] in Hin. apply in_app_or in Hin as [Hin|Hin].
- exact (hl_iv_subtract_apart a sz lo hi q (Hl (a, sz) (or_introl eq_refl)) Hin).
- exact (IH lo hi q (fun p Hp => Hl p (or_intror Hp)) Hin).
Qed.
Lemma hl_replay_sub : ltac2:(TCodec.tc2 tcn__HandoffLazyK "RH'G'4'D%211'H&I(Br2r1%3221&0r6(2(Cr5r4%3221r3%63@21%93A81%?3B;1'8&K&J&Fr8%2219%322D%5221&M+2+R0%3221%;251&Lz%2219%@241p0B1pR@Q31pR0Q41r7%Q53Q8Q11';r9%E21L%F22Q7%H221%H247%K221%J26Q7%L231%N217%:241p0<1pR@QC1pR0QD1'5'Q;yR0%211%4211&E%QB2QDQA%QD3QN1QA%QG3QOH1%42Q91%QN36QK1&Q<&3%13::QO%32<1&6%13==R2%62?1%QD241%QF21L%QG2J6%Q3221p0<1pRFC1p0I1p0Q:1pR6R@1pRBR@1pR2RA1pR4RC1pLRG1").
Proof.
intros E h1 bS nS h2. induction h1 as [|hop h1 IH]; intros Hwf Hap q Hin.
- cbn [app hreplay] in Hin.
apply (hl_maps_subtract_apart (hreplay E h2) _ _ q); [|exact Hin].
intros p Hp. destruct (hl_replay E h2 (fun b n H => Hwf b n (or_intror H)) p Hp) as (_ & P2 & _). exact P2.
- assert (IH' := IH (fun b n H => Hwf b n (or_intror H)) (fun b n H => Hap b n (or_intror H))).
destruct hop as [b n|b n]; cbn [app hreplay] in Hin.
+ destruct Hin as [<-|Hin]; [|exact (IH' q Hin)]. cbn [fst snd]. exact (Hap b n (or_introl eq_refl)).
+ assert (WF : forall p, In p (hreplay E (h1 ++ HSub bS nS :: h2)) ->
0 < bv_unsigned (snd p) /\ bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64).
{ intros p Hp. destruct (hl_replay E _ (fun b' n' H => Hwf b' n' (or_intror H)) p Hp) as (P1 & P2 & _). auto. }
destruct (hl_maps_subtract (hreplay E (h1 ++ HSub bS nS :: h2)) _ _ q (fun p Hp => let '(conj P1 P2) := WF p Hp in conj P2 P1) Hin)
as (_ & p & Hp & Q2 & Q3).
destruct (IH' p Hp) as [X|X]; [left | right]; lia.
Qed.
Lemma hl_page_piece : ltac2:(TCodec.tc2 tcn__HandoffLazyK "Q>'Q;yR0%211'4'5%1233%311'9'1&A&@r2%211r1%5221(7%93821':'8&Ir3%23@81&K&Q<&3%13GG<%32I1r4%B11%62L1%8241&J+TP0%2241&6%13Q1Q1F%=2Q31%62;1%@251%E291%F2C1qRFQ41%I2Q51p0K1pR<Q61pRNQ;1").
Proof.
intros w lazy H. unfold page_in_ranges in H. apply existsb_exists in H as (q & Hq & Hb). apply andb_prop in Hb as [B1 B2].
apply Z.leb_le in B1. apply Z.leb_le in B2. exists q. unfold page_size in B2. auto.
Qed.
