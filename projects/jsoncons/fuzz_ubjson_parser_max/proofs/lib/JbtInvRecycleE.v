(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem JbtPoison ArtRuns JbtCls JbtFp ArtBridge
JbtRecycle1 JbtRecycle2C JbtRecycle5A JbtRecycle5I JbtRecycle5T JbtRecycle5C JbtInvRecycleA JbtInvRecycleD.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtInvRecycleE () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInvRecycleA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5T."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["0BUDGET"; "1app"; "1fst"; "1length"; "1list"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "2or"; "3le"; "4map"; "5Z"; "0KMAX"]; ["0LENMAX"; "0RESV"; "6art_EVOK"; "6art_cost_sum"; "6art_ev_range"; "6art_live"; "6art_windows"; "7AMadvise"; "7AMmapNull"; "7AMunmap"; "7aev"; "7art_shhi"; "7art_shlo"; "8art_evok_list"; "9art_rel_key"; ":SB"]; [";RES"; ";art_rel"; "<art_rels_events"; "=In"; "=NoDup"; ">add"; ">div"; ">le"; ">lt"; ">modulo"; "0a"; "0b1"; "0ev"; "0l"; "0l1"; "0l2"]; ["0len"; "0log"; "0m"; "0mb"; "0ms"; "0n"; "0r"; "0w"; "0work"; "0z"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Lemma art_live_in_log : ltac2:(TCodec.tc2 tcn__JbtInvRecycleE "G'4'J%211'>&Q3'6%1233(5r2r1%347721&Er3%211%:3841(H%1284r4%>3A21p051pS2A1pS>B1pS4D1").
Proof.
intros log. induction log as [|ev l IH] using rev_ind; intros r len H; [destruct H|]. rewrite art_live_snoc in H. apply in_or_app.
destruct ev as [a l0|l0 r0|a l0|a l0|a l0]; cbn [art_ev_live] in H; try (left; exact (IH r len H)).
- destruct H as [E|H]; [right; left; injection E as -> ->; reflexivity|left; exact (IH r len H)].
- apply filter_In in H. left. exact (IH r len (proj1 H)).
Qed.
Lemma art_log_window : ltac2:(TCodec.tc2 tcn__JbtInvRecycleE "K'4'J%211'>&Q3(Hr1r2%3221r3%63921'6%1299(5&L%116&K%128:%54??31&Fr4%211%B3:41p0=1pS2E1pS>F1pS4H1").
Proof. intros log r len H. unfold art_windows. apply in_flat_map. exists (AMmapNull len r). split; [exact H|left; reflexivity]. Qed.
Lemma art_windows_app : ltac2:(TCodec.tc2 tcn__JbtInvRecycleE "F'4'J%211'6'>%2211&Q3r1&Fr3%211%53641r2&1r4%23>16%811%;3<51p071pS@>1pS0B1pRNC1").
Proof. intros l1 l2 w H. unfold art_windows in *. rewrite flat_map_app. apply in_or_app. left. exact H. Qed.
Section Evok.
Variable RESV : list (Z * Z).
Variables BUDGET LENMAX KMAX : Z.
#[local] Abbreviation EVOK := (art_EVOK RESV BUDGET LENMAX KMAX).
#[using="Type"] Lemma art_rcy_evok : ltac2:(TCodec.tc2 tcn__JbtInvRecycleE "R1'4'Q1%211'J%411'>&Q3(Q0r5r4r3r2r1%6554321r7%93>21'8'6%12==(5r6%24@@1=&E%119%B3631'9&Q9+TP0%2281z%53I21%52G4%73K13&Q7%125>%226K%D221%E251%F281%G2?1p0I1pS<Q41pRHQ51pS6Q61pS:Q71pS8Q81'Q4&=&N%24Q@O1Q7%42Q01&M&BvAv0v@v?%544321&Q2%11QB%933QB1p0;1p0A1pS4QK1pSBQN1").
Proof.
induction work as [|e r IH]; intros log ALL ND; [exact I|]. change (art_rels_events (e :: r)) with (art_rel_events e ++ art_rels_events r).
cbn [map] in ND. inversion ND as [|? ? Hn NDr]; subst. apply art_evok_list_app. split.
- destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_events]; try exact I.
destruct (ALL mb ms m b1 n (or_introl eq_refl)) as (Hl & A1 & A2 & P1 & P2).
destruct (art_flush_range mb ms A1 A2 P1 P2) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
unfold art_flush_events. destruct (art_flush_beg mb <? art_flush_end mb ms) eqn:EL; cbn [app art_evok_list].
+ apply Z.ltb_lt in EL. split.
* cbn [art_EVOK]. split; [exact F1|]. split; [exact F3|]. split; [lia|]. exists (art_shlo mb, art_shhi mb ms). split; [exact (art_log_window log mb ms (art_live_in_log log mb ms Hl))|]. cbn [fst snd]. lia.
* split; [|exact I]. cbn [art_EVOK]. rewrite art_live_snoc. cbn [art_ev_live]. exact Hl.
+ split; [|exact I]. cbn [art_EVOK]. exact Hl.
- apply IH; [|exact NDr]. intros mb ms m b1 n Hin. destruct (ALL mb ms m b1 n (or_intror Hin)) as (Hl & REST). split; [|exact REST].
destruct e as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_events]; rewrite ?app_nil_r; try exact Hl.
rewrite art_live_app_unmap. apply filter_In. split; [exact Hl|]. cbn [fst]. apply negb_true_iff, Z.eqb_neq. intros E. apply Hn. cbn [art_rel_key]. rewrite <- E.
apply in_map_iff. exists (RES mb ms m b1 n). split; [reflexivity|exact Hin].
Qed.
End Evok.
Lemma art_rels_events_kinds : ltac2:(TCodec.tc2 tcn__JbtInvRecycleE "Q1'4'Q1%211'J&Q3r1&Q2r2%211%53641';':'>'9r4(G%129;%43>31qRL61%8271qRF81%:291(I%12@B%;3E:1qRL=1%?2>1qRF?1%A2@1%C281p0E1pRJL1pSBN1").
Proof.
intros work ev H. unfold art_rels_events in H. apply in_flat_map in H. destruct H as (e & _ & H).
destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_events] in H; try destruct H. apply in_app_or in H. destruct H as [H|[<-|[]]]; [|right; eexists; eexists; reflexivity].
unfold art_flush_events in H. destruct (art_flush_beg mb <? art_flush_end mb ms); [destruct H as [<-|[]]; left; eexists; eexists; reflexivity|destruct H].
Qed.
Lemma art_rels_events_cost : ltac2:(TCodec.tc2 tcn__JbtInvRecycleE "='4'Q1%211'9'>&C&Q2r1%211%411z%83721pSB:1").
Proof.
intros work. assert (H : forall l, (forall ev, In ev l -> art_cost ev = 0) -> art_cost_sum l = 0).
{ induction l as [|a r IH]; intros A; [reflexivity|]. cbn [art_cost_sum fold_right]. rewrite (A a (or_introl eq_refl)). unfold art_cost_sum in IH. rewrite IH; [reflexivity|]. intros ev Hev. apply A. right. exact Hev. }
apply H. intros ev Hev. destruct (art_rels_events_kinds work ev Hev) as [(a & l & ->)|(a & l & ->)]; reflexivity.
Qed.
Lemma art_live_rcy_len : ltac2:(TCodec.tc2 tcn__JbtInvRecycleE "H'4'Q1%211'J%411'<&3'6'>%2211&E&1r1&Q2r2%211%53=41%711%<291%917%>2;1%@231pS4B1pSBE1").
Proof.
induction work as [|e r IH]; intros log; [unfold art_rels_events; cbn [flat_map]; rewrite app_nil_r; lia|].
change (art_rels_events (e :: r)) with (art_rel_events e ++ art_rels_events r). rewrite app_assoc. specialize (IH (log ++ art_rel_events e)).
destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_events] in *; rewrite ?app_nil_r in *; try exact IH.
rewrite art_live_app_unmap in IH. pose proof (filter_length_le (fun p : Z * Z => negb (fst p =? mb)) (art_live log)). lia.
Qed.
Lemma art_rcy_ev_range : ltac2:(TCodec.tc2 tcn__JbtInvRecycleE "RH'4'Q1%211'J'>&Q3(Q0r5r4r3r2r1%6554321r8%93=21'8'9&Q9r6+TP0%3221z%63B21%62@4%83D13&Q7%1258%226D%=221%>251%?281p0A1pS<L1pRHM1pS6N1pS:O1pS8Q01&Q2%11N%Q23Q4N1&2&D%11Q2%33Q7Q71%C21Q3&Q8&7%13Q;Q;5%32Q71%Q2251':r;%Q?3QCQ81';r9%N2Q@1&Q5%12QBQA%=241%Q<241&O&Q6+8%22QH1%8241%Q821;%52QJ4%;231%G2>1%QF241%A2;1%QH2C1qS<R41%G2R51qRHR61%I2R71qS6R81%K2R91qS:R:1%M2R;1qS8R<1%O2R=1p0Q11p0Q<1p0Q@1pSDRA1pRJRC1pSBRE1").
Proof.
intros work ev z ALL Hev Hz. unfold art_rels_events in Hev. apply in_flat_map in Hev. destruct Hev as (e & He & Hev).
destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_events] in Hev; try destruct Hev. exists mb, ms, m, b1, n. split; [exact He|].
destruct (ALL mb ms m b1 n He) as (A1 & A2 & P1 & P2). destruct (art_flush_range mb ms A1 A2 P1 P2) as (F1 & F2 & F3 & F4 & F5 & F6 & _).
apply in_app_or in Hev. destruct Hev as [Hev|[<-|[]]]; [|left; cbn [art_ev_range fst snd] in Hz; exact Hz].
unfold art_flush_events in Hev. destruct (art_flush_beg mb <? art_flush_end mb ms); [|destruct Hev]. destruct Hev as [<-|[]]. cbn [art_ev_range fst snd] in Hz. right. lia.
Qed.
