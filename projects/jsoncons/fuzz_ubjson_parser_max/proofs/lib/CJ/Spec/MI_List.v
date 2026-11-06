(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc KInv MI_Inv MI_Kit.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_List () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_List.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1S"; "1Some"; "1app"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3N"]; ["3Z"; "0LS"; "4MR"; "4dll"; "4linked"; "5data_of"; "5fupd"; "5lists_ok"; "5queue_st"; "6aptr"; "6dequeue"; "6get_head"; "6get_stride"; "6lhead"; "6m_avail"; "6m_freeable"]; ["6m_freed"; "6m_last_idx"; "6m_maplen"; "6m_mem"; "6m_next"; "6m_prev"; "6m_set_next"; "6m_set_prev"; "6m_sizeclass"; "6meta"; "6mstate"; "6optr"; "6s_metas"; "6set_head"; "6upd_meta"; "7In"]; ["7last"; "7nth_error"; "7removelast"; "7tl"; "0a"; "0a'"; "0f"; "0g"; "0h"; "0h'"; "0hh"; "0k"; "0l"; "0l1"; "0l2"; "0m"]; ["0mr"; "0r"; "0r'"; "0rest"; "0s"; "0st"; "0st'"; "0st2"; "0st3"; "8lookup"; "9N_countable"; "9Z_countable"; "9prod_countable"; ":prod_eq_dec"; ";gmap"; ";gmap_lookup"]; ["<eq_dec"; "=eq_dec"; "0t"; "0v"; "0x"; "0y"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition q_link (st0 : mstate) (g head : aptr) : mstate :=
let hprev := m_prev (get_meta_rec st0 head) in
let st1 := upd_meta g (fun r => m_set_prev hprev (m_set_next (Some head) r)) st0 in
let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some g)) st1 | None => st1 end in
upd_meta head (m_set_prev (Some g)) st2.
Definition q_single (st0 : mstate) (h : lhead) (g : aptr) : mstate :=
set_head h (Some g) (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st0).
Definition queue_st (h : lhead) (g : aptr) (st0 : mstate) : mstate :=
match get_head st0 h with
| Some head => q_link st0 g head
| None => q_single st0 h g
end.
Lemma queue_eq {R} h g st0 (k : mstate -> M R) bail :
m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None ->
queue h g st0 k bail = k (queue_st h g st0).
Proof.
intros Hn Hp. unfold queue, guard. rewrite Hn, Hp. cbn [optr_eqb].
unfold queue_st, q_link, q_single. destruct (get_head st0 h); reflexivity.
Qed.
Definition fm_st (st : mstate) (g : aptr) : mstate := queue_st LFree g (put_meta g meta0 st).
Lemma free_meta_eq {R} st g (k : mstate -> M R) bail : free_meta g st k bail = k (fm_st st g).
Proof. unfold free_meta, fm_st. apply queue_eq; rewrite get_meta_rec_put_same; reflexivity. Qed.
Definition data_of (r : meta) : meta := m_set_prev None (m_set_next None r).
Lemma data_of_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "QA'Q9&<':&Er2%211r1%411%63831'9&Q;&Q3%118%217%<3421'@&N%11=%21<%A3421&Q0%11A%21@%E3821&Q1%11E%21D%I3<21&O%11I%21H%M3@21&Q8%11M%21L%Q13D21&Q2%11Q1%21Q0%Q53H21%O251%Q02:1%Q12?1%Q22D1%Q32I1%Q42O1%Q=2Q61pT6Q?1pT4Q@1").
Proof. intros r r'.
destruct r, r'; unfold data_of; cbn; split.
- intros H. inversion H. repeat split; reflexivity.
- intros (-> & -> & -> & -> & -> & -> & ->). reflexivity.
Qed.
Lemma data_of_set_prev : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "=&Q;'Q9':&E&Q7r2r1%3221%511%613%83921pT4:1pU8<1"). Proof. intros v r. reflexivity. Qed.
Lemma data_of_set_next : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "=&Q;'Q9':&E&Q6r2r1%3221%511%613%83921pT4:1pU8<1"). Proof. intros v r. reflexivity. Qed.
Lemma get_stride_data : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "A'Q9':&Er2%211r1%411%63731'@&Lr3%211%319%<3521p071pT6?1pT4@1").
Proof. intros r r'. intros H. apply data_of_eq in H. unfold get_stride. destruct H as (_ & _ & _ & -> & _ & -> & ->). reflexivity. Qed.
Section LINKED.
Variable st : mstate.
Local Notation R := (MR st).
Lemma linked_cons2 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "Q3&I'5%112&<&DvR5(4r3r2r1%43:21%53;41%8271'9':&Q;&Q4&B%12=;%311(2%12E=%83731&Q5%72C@%211%62JC%=3<21%H2GB%@221%A281%L2C1pU6N1pU<Q11pU:Q21").
Proof. intros x y t. cbn. tauto. Qed.
Lemma linked_app : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "J&I'5%112&<&DvR5&3r2(4r3r1%33;21%63<51%9281'9(7%11@%93A81%<3B;1%?2>1%@2?9%7221%C291pSNE1pSLF1pU:I1").
Proof. intros x l1 l2.
induction l1 as [|a l1 IH]; cbn.
- tauto.
- destruct l1 as [|b l1']; cbn in *.
+ tauto.
+ rewrite IH. tauto.
Qed.
Lemma linked_next : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "Q>'5&I%211&DvR5r1%3221'6':'8%119&QAr5r3%33=21(2r2%22@1%:3841r6(1r4%211%<3F41%@3>17'9&Q;&Q4&B%12I8%311%@2NB%H3621&Q5%62NE%211%E2Q3?%M3;21%=261p0?1p0F1pU<Q81pU:Q91pSHQ41p0Q61pSJQ;1").
Proof. intros l.
induction l as [|a l IH]; intros Hl k x y Hx Hy; [destruct k; discriminate|].
destruct l as [|b l']; [destruct k; cbn in Hy; [discriminate| destruct k; discriminate]|].
destruct Hl as (Hn & Hp & Hl'). destruct k as [|k]; cbn in Hx, Hy.
- inversion Hx; inversion Hy; subst. auto.
- eapply IH; eauto.
Qed.
Lemma linked_In_next : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "Q8'5&I%211&DvR5r2%3221&Q?&QBr3%2291%43:61';'9r1r5%93?21':&Q;&Q4&Br4%22B1%411(2%12H;%93831&Q5%82H>%211%62M9%>3=21%C261%D2A1qU<Q11%G2Q21p0I1p0O1pU:Q51pSJQ51").
Proof. intros l x.
induction l as [|a l IH]; intros Hl Hin; [destruct Hin|].
destruct l as [|b l']; [destruct Hin|].
destruct Hl as (Hn & Hp & Hl'). cbn [removelast] in Hin. destruct Hin as [<-|Hin].
- exists b. cbn. auto.
- destruct (IH Hl' Hin) as (y & Hy & H1 & H2). exists y. split; [right; exact Hy| auto].
Qed.
End LINKED.
Lemma linked_ext : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "Q<'Q:'5&I%211&Q?r1&QBr2%2261%53741':&Q;&Q4&Br4%2218%411r5%521;%711%:3941p0<1pU:D1&QCr3%22G1%F3HE1&Q5%11:r6%A21G%411%F3E41p071pU:Q01&D%12C<%22DGp021p051p0B1pSJQ61pT>Q:1pT<Q;1").
Proof. intros st st' l.
induction l as [|a l IH]; intros Hn Hp Hl; [exact I|].
destruct l as [|b l']; [exact I|].
destruct Hl as (H1 & H2 & Hl'). cbn [linked]. split; [|split].
- rewrite Hn; [exact H1|]. cbn. destruct l'; [left; reflexivity| left; reflexivity].
- rewrite Hp; [exact H2|]. left. reflexivity.
- apply IH; [| | exact Hl'].
+ intros x Hx. apply Hn. cbn [removelast]. destruct l' as [|c l'']; [destruct Hx| right; exact Hx].
+ intros x Hx. apply Hp. right. exact Hx.
Qed.
Record lists_ok (st : mstate) (LS : lhead -> list aptr) : Prop := mkLO {
lo_head : forall h, get_head st h = head_of (LS h);
lo_dll : forall h, dll st (LS h);
lo_nodup : forall h, NoDup (LS h);
lo_disj : forall h1 h2 m, In m (LS h1) -> In m (LS h2) -> h1 = h2;
lo_link : forall m, ((exists h, In m (LS h)) <-> m_next (MR st m) <> None)
/\ (m_next (MR st m) = None -> m_prev (MR st m) = None)
}.
#[export] Instance lhead_eq_dec : EqDecision lhead.
Proof. intros [a|] [b|]; try (right; discriminate); try (left; reflexivity).
destruct (decide (a = b)) as [->|NE]; [left; reflexivity| right; congruence]. Defined.
Definition fupd (LS : lhead -> list aptr) (h : lhead) (l : list aptr) : lhead -> list aptr :=
fun h' => if decide (h' = h) then l else LS h'.
Lemma fupd_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "?'M'5&I%211p041':&Fr3r2r1%443212%63812pSJ91pSB=1pQ4:1").
Proof. intros LS h l. unfold fupd. destruct (decide (h = h)); [reflexivity| congruence]. Qed.
Lemma fupd_ne : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "G'M'5&I%211p041&=':r1r3%33921%511&Fr5r4r2%443271%412%;3>21p081pSDC1pSJA1pSBE1pQ4B1").
Proof. intros LS h l h'. intros NE. unfold fupd. destruct (decide (h' = h)); [congruence| reflexivity]. Qed.
Section FACTS.
Variables (st : mstate) (LS : lhead -> list aptr).
Hypothesis LO : lists_ok st LS.
Local Notation R := (MR st).
Lemma lists_next_in : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "Q4'M&I&Q?r1vAr2%211%53641';'9r4%711%:3;91':&Q;&Q4&BvR5r3%3221%511(2%12EC%:3931&Q5%928F%211%62J9%?3>21%D261%E2B1qU<N1%H2O1p0J1pU:Q11pSBQ31").
Proof. intros h x.
intros Hin. pose proof (lo_dll _ _ LO h) as D. destruct (LS h) as [|a l] eqn:E; [destruct Hin|].
cbn [dll] in D. destruct (linked_In_next st _ x D) as (y & Hy & H1 & H2).
- rewrite removelast_app by discriminate. cbn. rewrite app_nil_r. exact Hin.
- exists y. split; [|auto]. apply in_app_iff in Hy. destruct Hy as [Hy|[<-|[]]]; [exact Hy| left; reflexivity].
Qed.
Lemma lists_prev_in : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "Q4'M&I&Q?r1vAr2%211%53641';'9r4%711%:3;91':&Q;&Q5&BvR5r3%3221%511(2%12EC%:3931&Q4%928F%211%62J9%?3>21%D261%E2B1qU<N1%H2O1p0J1pU:Q11pSBQ31").
Proof. intros h x.
intros Hin. pose proof (lo_dll _ _ LO h) as D. destruct (LS h) as [|a l] eqn:E; [destruct Hin|].
cbn [dll app] in D.
assert (H : forall l1 l2, a :: l ++ [a] = l1 ++ x :: l2 -> l1 <> [] -> exists y, In y (a :: l) /\ m_prev (R x) = Some y /\ m_next (R y) = Some x).
{ intros l1 l2 Heq Hne. destruct (@exists_last _ l1 Hne) as (l0 & y & ->).
rewrite <- app_assoc in Heq. cbn in Heq. rewrite Heq in D.
apply linked_app in D as [_ D]. destruct D as (H1 & H2 & _). exists y. split; [|auto].
assert (Hy : In y (a :: l ++ [a])) by (rewrite Heq; apply in_app_iff; right; left; reflexivity).
cbn in Hy. destruct Hy as [<-|Hy]; [left; reflexivity|]. apply in_app_iff in Hy. destruct Hy as [Hy|[<-|[]]]; [right; exact Hy| left; reflexivity]. }
destruct Hin as [Exa|Hin].
- subst x. apply (H (a :: l) []); [| discriminate]. cbn. reflexivity.
- destruct (in_split _ _ Hin) as (l1 & l2 & ->). apply (H (a :: l1) (l2 ++ [a])). { cbn. rewrite <- app_assoc. reflexivity. } discriminate.
Qed.
Lemma lists_in_next_some : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "G'M&I&Q?r1vAr2%211%53641&=':&Q;&Q4&BvR5%2219%411(0%11@%93831%;11p0=1pU:D1pSBF1").
Proof. intros h x. intros Hin. destruct (lists_next_in h x Hin) as (y & _ & -> & _). discriminate. Qed.
Lemma lists_notin : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "G&I':&Q;&Q4&BvR5r1%3221%511(0%11:%:3931'M&=&Q?r3vA%11;%43B31%611pSB81p0:1pT0F1").
Proof. intros m. intros Hn h Hin. exact (lists_in_next_some h m Hin Hn). Qed.
Lemma lists_head_prev : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "Q3'M&I'5%112':vAr3%211(4r2r1%33:21%83951'9&Q;&Q5&BvR5%221<%411(2&Q@%13E=@%32F1%D3:51&Q4%:294%211%82KF%I3?21%A261p0C1pSJM1pS:Q01pSBQ21").
Proof. intros h a l.
intros E. pose proof (lo_dll _ _ LO h) as D. rewrite E in D. cbn [dll] in D.
destruct l as [|b l'].
- cbn in D |- *. tauto.
- destruct (@exists_last _ (b :: l') ltac:(discriminate)) as (l0 & y & Ey). rewrite Ey in D |- *.
rewrite last_last.
replace ((a :: l0 ++ [y]) ++ [a]) with ((a :: l0) ++ y :: [a]) in D by (cbn; rewrite <- app_assoc; reflexivity).
apply (linked_app st y (a :: l0) [a]) in D as [_ D]. cbn in D. tauto.
Qed.
Lemma lists_singleton : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "O'M&I'5%112':vAr3%211(4r2r1%33:21%83951&<&Q;&Q4&BvR5%221<%411(2%12D?%B3831(7%11G%E3F@1%=241p0?1pSJI1pS:L1pSBN1").
Proof. intros h a l.
intros E. split.
- intros Hn. destruct l as [|b l']; [reflexivity|]. exfalso.
pose proof (lo_dll _ _ LO h) as D. rewrite E in D. cbn [dll app] in D. destruct D as (H1 & _). rewrite Hn in H1. inversion H1; subst.
pose proof (lo_nodup _ _ LO h) as ND. rewrite E in ND. apply NoDup_cons in ND as [NI _]. apply NI. apply list_elem_of_In. left. congruence.
- intros ->. pose proof (lo_dll _ _ LO h) as D. rewrite E in D. cbn in D. tauto.
Qed.
End FACTS.
Definition clr (r : meta) : meta := m_set_prev None (m_set_next None r).
Section DEQUEUE.
Variables (h : lhead) (m : aptr) (st : mstate).
Let mr := MR st m.
Let st' := dequeue h m st.
Let st1 := match m_prev mr with Some pv => upd_meta pv (m_set_next (m_next mr)) st | None => st end.
Let st2 := match m_next mr with Some nx => upd_meta nx (m_set_prev (m_prev mr)) st1 | None => st1 end.
Let st3 := if negb (optr_eqb (m_next mr) (Some m))
then (if optr_eqb (get_head st2 h) (Some m) then set_head h (m_next mr) st2 else st2)
else set_head h None st.
Lemma dequeue_unfold : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "B':'Q:vR6&Q>vQO'Q9&Q7(0&I%211&Q6r1%2231%7241qT491vR8%=3<21%A3@?1").
Proof. reflexivity. Qed.
Lemma st1_R x : MR st1 x = if optr_eqb (m_prev mr) (Some x) then m_set_next (m_next mr) (MR st x) else MR st x.
Proof.
subst st1. unfold MR. destruct (m_prev mr) as [p|]; cbn [optr_eqb]; [|reflexivity].
rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x p) as [E|NE]; destruct (aptr_eqb_spec p x) as [E2|NE2]; subst; try reflexivity; congruence.
Qed.
Lemma st2_R x : MR st2 x = if optr_eqb (m_next mr) (Some x) then m_set_prev (m_prev mr) (MR st1 x) else MR st1 x.
Proof.
subst st2. unfold MR. destruct (m_next mr) as [q|]; cbn [optr_eqb]; [|reflexivity].
rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x q) as [E|NE]; destruct (aptr_eqb_spec q x) as [E2|NE2]; subst; try reflexivity; congruence.
Qed.
Lemma st3_R x : MR st3 x = if optr_eqb (m_next mr) (Some m) then MR st x else MR st2 x.
Proof.
subst st3. unfold MR. destruct (optr_eqb (m_next mr) (Some m)); cbn [negb].
- rewrite get_meta_rec_set_head. reflexivity.
- destruct (optr_eqb (get_head st2 h) (Some m)); rewrite ?get_meta_rec_set_head; reflexivity.
Qed.
Lemma dequeue_data : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List ">&I':'Q9&E&BvR6r1%3221%511vR5%6214%811%;3:41pU:=1").
Proof. intros x.
rewrite dequeue_unfold. unfold MR at 1. rewrite get_meta_rec_upd. fold (MR st3 x). fold (MR st3 m).
assert (D3 : forall y, data_of (MR st3 y) = data_of (MR st y)).
{ intros y. rewrite st3_R. destruct (optr_eqb (m_next mr) (Some m)); [reflexivity|].
rewrite st2_R, st1_R. destruct (optr_eqb (m_next mr) (Some y)); destruct (optr_eqb (m_prev mr) (Some y)); reflexivity. }
destruct (aptr_eqb_spec x m) as [->|NE]; [|apply D3].
rewrite data_of_set_prev, data_of_set_next. apply D3.
Qed.
Lemma dequeue_next x : m_next (MR st' x) =
if aptr_eqb x m then None
else if optr_eqb (m_next mr) (Some m) then m_next (MR st x)
else if optr_eqb (m_prev mr) (Some x) then m_next mr else m_next (MR st x).
Proof.
rewrite dequeue_unfold. unfold MR at 1. rewrite get_meta_rec_upd. fold (MR st3 x). fold (MR st3 m).
destruct (aptr_eqb_spec x m) as [->|NE]; [reflexivity|].
rewrite st3_R. destruct (optr_eqb (m_next mr) (Some m)); [reflexivity|].
rewrite st2_R, st1_R. destruct (optr_eqb (m_next mr) (Some x)); destruct (optr_eqb (m_prev mr) (Some x)); reflexivity.
Qed.
Lemma dequeue_prev x : m_prev (MR st' x) =
if aptr_eqb x m then None
else if optr_eqb (m_next mr) (Some m) then m_prev (MR st x)
else if optr_eqb (m_next mr) (Some x) then m_prev mr else m_prev (MR st x).
Proof.
rewrite dequeue_unfold. unfold MR at 1. rewrite get_meta_rec_upd. fold (MR st3 x). fold (MR st3 m).
destruct (aptr_eqb_spec x m) as [->|NE]; [reflexivity|].
rewrite st3_R. destruct (optr_eqb (m_next mr) (Some m)); [reflexivity|].
rewrite st2_R, st1_R. destruct (optr_eqb (m_next mr) (Some x)); destruct (optr_eqb (m_prev mr) (Some x)); reflexivity.
Qed.
Lemma get_head_st2 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List ";'M':&Q;&KvR7r1%3221vR5%5213%83731pSD:1").
Proof. intros h'.
subst st2 st1. destruct (m_next mr); destruct (m_prev mr); rewrite ?get_head_upd_meta; reflexivity.
Qed.
Lemma dequeue_head h' : get_head st' h' =
if decide (h' = h) then
(if optr_eqb (m_next mr) (Some m) then None
else if optr_eqb (get_head st h) (Some m) then m_next mr else get_head st h)
else get_head st h'.
Proof.
rewrite dequeue_unfold. rewrite get_head_upd_meta. subst st3.
destruct (optr_eqb (m_next mr) (Some m)); cbn [negb].
- destruct (decide (h' = h)) as [->|NE]; [apply get_head_set_head| apply get_head_set_head_other; exact NE].
- rewrite get_head_st2. destruct (optr_eqb (get_head st h) (Some m)).
+ destruct (decide (h' = h)) as [->|NE]; [apply get_head_set_head| rewrite get_head_set_head_other by exact NE; apply get_head_st2].
+ destruct (decide (h' = h)) as [->|NE]; apply get_head_st2.
Qed.
Lemma set_head_metas : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "N'M&Q;'Q:':'R>&I&R='?&R@'@&RA%544321&R<&R:&R;%36872651'Q9%=4<621&Q<&Q=r3r2r1%43321%611%713%G3921pT:I1pU8K1pSFM1").
Proof. intros hh v s. destruct hh; reflexivity. Qed.
Lemma dequeue_keys : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "QF&I&=':'8'Q9%211&R9'R>&R='?&R@'@&RA%544321&R<&R:&R;%36872651%;4B51>&R?%14D73@r1&Q<vR6%211%C6IE7541(0%11G%J3G31%L11'>r2vR5%;11%L6Q2N@>31%Q13N18%Q311vQO%Q43Q671&Q;&Q5vR0%211(2%12Q<=%Q;3631&Q4%116%Q>3914%C241%D2<1%E2?1p0G1pU:QE1").
Proof. intros x.
rewrite dequeue_unfold. rewrite lookup_metas_upd.
destruct (aptr_eqb_spec x m) as [->|NE]; [intros _; right; left; reflexivity|].
subst st3 st2 st1. destruct (optr_eqb (m_next mr) (Some m)); cbn [negb].
- rewrite set_head_metas. auto.
- match goal with |- context [s_metas (if ?c then _ else _)] => destruct c end; rewrite ?set_head_metas.
all: destruct (m_next mr) as [q|]; destruct (m_prev mr) as [p'|]; rewrite ?lookup_metas_upd;
repeat match goal with |- context [if aptr_eqb ?a ?y then _ else _] => destruct (aptr_eqb_spec a y) as [<-|?] end; auto.
Qed.
Lemma dequeue_keys_mono : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "Q6&I&=':'8'Q9%211&R9'R>&R='?&R@'@&RA%544321&R<&R:&R;%36872651%;4B51>&R?%14D73@r1&Q<vR5%211%C6IE7541(0%11G%J3G31%L11r2vR6%:11%K6Q1M?=31%Q03M17%Q211p071pU:Q51").
Proof. intros x.
rewrite dequeue_unfold. rewrite lookup_metas_upd.
destruct (aptr_eqb_spec x m) as [->|NE]; [intros _; discriminate|].
subst st3 st2 st1. destruct (optr_eqb (m_next mr) (Some m)); cbn [negb].
- rewrite set_head_metas. auto.
- match goal with |- context [s_metas (if ?c then _ else _)] => destruct c end; rewrite ?set_head_metas.
all: destruct (m_next mr) as [q|]; destruct (m_prev mr) as [p'|]; rewrite ?lookup_metas_upd;
repeat match goal with |- context [if aptr_eqb ?a ?y then _ else _] => destruct (aptr_eqb_spec a y) as [<-|?] end; auto; intros; discriminate.
Qed.
Lemma dequeue_key_m : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "N&=':'8'Q9%211&R9&I'R>&R='?&R@'@&RA%544321&R<&R:&R;%36872651%;4<51?&R?%14>73AvQO&Q<vR6%211%D6CF7541(0%11H%K3H31%M11").
Proof. rewrite dequeue_unfold, lookup_metas_upd, aptr_eqb_refl. discriminate. Qed.
End DEQUEUE.
Section QUEUE.
Variables (h : lhead) (g : aptr) (st : mstate).
Let st' := queue_st h g st.
Lemma data_upd_links : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "M'Q:&I'Q9pU:11':&Er3r1%211%411%513%73921pT4:1&B&Q>r4r5%332;1r2%6221%?11%8253%A11%C3E31p0<1pU:H1pS>G1pT0J1pT:L1").
Proof. intros s m f x. intros Hf. unfold MR. rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x m) as [->|NE]; [apply Hf| reflexivity]. Qed.
Lemma queue_data : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List ">&I':'Q9&E&BvR6r1%3221%511vR5%6214%811%;3:41pU:=1").
Proof. intros x.
subst st'. unfold queue_st, q_link, q_single.
destruct (get_head st h) as [a|].
- rewrite data_upd_links by (intros; reflexivity).
destruct (m_prev (get_meta_rec st a)) as [z|]; rewrite ?data_upd_links by (intros; reflexivity); reflexivity.
- unfold MR. rewrite get_meta_rec_set_head. fold (MR (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st) x). fold (MR st x).
apply data_upd_links. intros; reflexivity.
Qed.
Lemma queue_next x : m_next (MR st' x) =
match get_head st h with
| Some a => if aptr_eqb x a then (if optr_eqb (m_prev (MR st a)) (Some a) then Some g else if aptr_eqb a g then Some a else m_next (MR st a))
else if optr_eqb (m_prev (MR st a)) (Some x) then Some g
else if aptr_eqb x g then Some a else m_next (MR st x)
| None => if aptr_eqb x g then Some g else m_next (MR st x)
end.
Proof.
subst st'. unfold queue_st, q_link, q_single, MR.
destruct (get_head st h) as [a|].
- rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x a) as [->|NE].
+ cbn [m_next m_set_prev]. destruct (m_prev (get_meta_rec st a)) as [z|]; cbn [optr_eqb].
* rewrite get_meta_rec_upd. destruct (aptr_eqb_spec a z) as [<-|NEz]; rewrite ?aptr_eqb_refl; [reflexivity|].
rewrite (aptr_eqb_neq z a) by congruence. rewrite get_meta_rec_upd. destruct (aptr_eqb a g); reflexivity.
* rewrite get_meta_rec_upd. destruct (aptr_eqb a g); reflexivity.
+ destruct (m_prev (get_meta_rec st a)) as [z|]; cbn [optr_eqb].
* rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x z) as [<-|NEz].
-- rewrite aptr_eqb_refl. reflexivity.
-- rewrite (aptr_eqb_neq z x) by congruence. rewrite get_meta_rec_upd. destruct (aptr_eqb x g); reflexivity.
* rewrite get_meta_rec_upd. destruct (aptr_eqb x g); reflexivity.
- rewrite get_meta_rec_set_head, get_meta_rec_upd. destruct (aptr_eqb x g); reflexivity.
Qed.
Lemma queue_prev x : m_prev (MR st' x) =
match get_head st h with
| Some a => if aptr_eqb x a then Some g
else if aptr_eqb x g then m_prev (MR st a)
else m_prev (MR st x)
| None => if aptr_eqb x g then Some g else m_prev (MR st x)
end.
Proof.
subst st'. unfold queue_st, q_link, q_single, MR.
destruct (get_head st h) as [a|].
- rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x a) as [->|NE]; [reflexivity|].
destruct (m_prev (get_meta_rec st a)) as [z|].
+ rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x z) as [<-|NEz].
* cbn [m_prev m_set_next]. rewrite get_meta_rec_upd. destruct (aptr_eqb x g); reflexivity.
* rewrite get_meta_rec_upd. destruct (aptr_eqb x g); reflexivity.
+ rewrite get_meta_rec_upd. destruct (aptr_eqb x g); reflexivity.
- rewrite get_meta_rec_set_head, get_meta_rec_upd. destruct (aptr_eqb x g); reflexivity.
Qed.
Lemma queue_head h' : get_head st' h' =
if decide (h' = h) then match get_head st h with Some a => Some a | None => Some g end else get_head st h'.
Proof.
subst st'. unfold queue_st, q_link, q_single.
destruct (get_head st h) as [a|] eqn:E.
- destruct (m_prev (get_meta_rec st a)); rewrite ?get_head_upd_meta; destruct (decide (h' = h)) as [->|]; rewrite ?E; reflexivity.
- destruct (decide (h' = h)) as [->|NE]; [apply get_head_set_head|]. rewrite get_head_set_head_other by exact NE. apply get_head_upd_meta.
Qed.
Lemma queue_keys : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "R1&I&=':'8'Q9%211&R9'R>&R='?&R@'@&RA%544321&R<&R:&R;%36872651%;4B51>&R?%14D73@r1&Q<vR6%211%C6IE7541(0%11G%J3G31%L11'>r2vR5%;11%L6Q2N@>31%Q13N18%Q311vQG%Q43Q671&Q;&KvQH%22:1(2%12Q<=%Q;3631';'9%52Q@K%Q?3:71&Q5&B%12DO%311r3%<2QG1%QF3A31%:281qS:QJ1%=2QK1%N2?1%O2G1%Q02J1p0Q21pU:R01").
Proof. intros x.
subst st'. unfold queue_st, q_link, q_single, MR.
destruct (get_head st h) as [a|].
- rewrite lookup_metas_upd. destruct (aptr_eqb_spec x a) as [->|NE]; [intros _; right; right; left; reflexivity|].
destruct (m_prev (get_meta_rec st a)) as [z|] eqn:Ez; rewrite ?lookup_metas_upd.
+ destruct (aptr_eqb_spec x z) as [->|NEz]; [intros _; right; right; right; exists a; auto|].
destruct (aptr_eqb_spec x g) as [->|NEg]; auto.
+ destruct (aptr_eqb_spec x g) as [->|NEg]; auto.
- rewrite set_head_metas, lookup_metas_upd. destruct (aptr_eqb_spec x g) as [->|NEg]; auto.
Qed.
Lemma queue_keys_mono : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "Q6&I&=':'8'Q9%211&R9'R>&R='?&R@'@&RA%544321&R<&R:&R;%36872651%;4B51>&R?%14D73@r1&Q<vR5%211%C6IE7541(0%11G%J3G31%L11r2vR6%:11%K6Q1M?=31%Q03M17%Q211p071pU:Q51").
Proof. intros x.
subst st'. unfold queue_st, q_link, q_single.
destruct (get_head st h) as [a|].
- rewrite lookup_metas_upd. destruct (aptr_eqb x a); [intros; discriminate|].
destruct (m_prev (get_meta_rec st a)) as [z|]; rewrite ?lookup_metas_upd; [destruct (aptr_eqb x z); [intros; discriminate|]|];
destruct (aptr_eqb x g); auto; intros; discriminate.
- rewrite set_head_metas, lookup_metas_upd. destruct (aptr_eqb x g); auto; intros; discriminate.
Qed.
Lemma queue_key_g : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "N&=':'8'Q9%211&R9&I'R>&R='?&R@'@&RA%544321&R<&R:&R;%36872651%;4<51?&R?%14>73AvQG&Q<vR6%211%D6CF7541(0%11H%K3H31%M11").
Proof.
subst st'. unfold queue_st, q_link, q_single.
destruct (get_head st h) as [a|].
- rewrite lookup_metas_upd. destruct (aptr_eqb g a); [discriminate|].
destruct (m_prev (get_meta_rec st a)) as [z|]; rewrite ?lookup_metas_upd; [destruct (aptr_eqb g z); [discriminate|]|];
rewrite aptr_eqb_refl; discriminate.
- rewrite set_head_metas, lookup_metas_upd, aptr_eqb_refl. discriminate.
Qed.
End QUEUE.
Lemma In_removelast {A} (x : A) l : In x (removelast l) -> In x l.
Proof.
induction l as [|a l IH]; cbn; [tauto|]. destruct l as [|b l']; [cbn; tauto|].
intros [<-|H]; [left; reflexivity| right; apply IH; exact H].
Qed.
Lemma In_tl {A} (x : A) l : In x (tl l) -> In x l.
Proof. destruct l; cbn; tauto. Qed.
Lemma NoDup_app_In {A} (l1 l2 : list A) x : NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros ND H1 H2. apply NoDup_app in ND as (_ & D & _). apply (D x); apply list_elem_of_In; assumption.
Qed.
Lemma NoDup_In_split {A} (l1 l2 : list A) x : NoDup (l1 ++ x :: l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
intros ND. apply NoDup_app in ND as (_ & D & ND2). apply NoDup_cons in ND2 as [N2 _]. split.
- intros H. apply (D x); [apply list_elem_of_In; exact H| left].
- intros H. apply N2. apply list_elem_of_In. exact H.
Qed.
Lemma linked_snoc : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "Q;'Q:'5&I%211&Dr4&3r3(4r2(7%119%43:31%73;61%:291':&Q;&Q4&Br5%221=%411(2%12E>%93831&Q5r6%921D%311%72KH%?3>21r7%H3NKE%I3O>1%L3Q081%O241p061p0=1p0H1pU<Q51pU:Q61pSJQ61pT<Q:1").
Proof. intros st l x y. intros Hl Hn Hp. apply (linked_app st x l [y]). split; [exact Hl|]. cbn. auto. Qed.
Lemma linked_prefix : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "Q='Q:'5&I%211&Dr5&3r4(4r3r2r1%43:21%53;41%83<71%;2:1'9r6(7%11A%<3B=1%?3C@1%B251':&Q;&Q4&B%12:D%311(2%12LE%83731&Q5%72@H%211%62Q1L%=3<21%E261%F2@1p0H1pU6Q51pU<Q71pU:Q81pSJQ81pT<Q<1").
Proof. intros st l x y t. intros H. apply linked_app in H as [H1 H2]. cbn in H2. tauto. Qed.
Lemma last_In {A} (l : list A) d : In (List.last l d) (d :: l).
Proof.
induction l as [|a l IH]; [left; reflexivity|].
cbn [List.last]. destruct l as [|b l']; [right; left; reflexivity|].
cbn in IH |- *. destruct IH as [IH|IH]; [left; exact IH| right; right; exact IH].
Qed.
Lemma dll_rot1 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "I'Q:&I'5%112&Dr3(4r2&3r1(7%11:%63;51%53<41%83=71%;2:1&Cr4%<3A=7%;3B<1%4231p061pT4C1pS:F1pT<H1").
Proof. intros st a r.
intros D. destruct r as [|b r']; cbn [dll app]; [exact D|].
cbn [app] in D. destruct D as (D1 & D2 & D3). rewrite <- app_assoc. cbn [app].
apply (linked_snoc st (b :: r') a b); assumption.
Qed.
Lemma dll_rot : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "B'Q:'5&I%211&Cr3&3r2r1%33721%6251r4%63:57%9221p041pSN<1pSL=1pT<A1").
Proof. intros st l1 l2.
revert l2. induction l1 as [|a l1 IH]; intros l2 D.
- rewrite app_nil_r. exact D.
- replace (l2 ++ a :: l1) with ((l2 ++ [a]) ++ l1) by (rewrite <- app_assoc; reflexivity).
apply IH. rewrite app_assoc. apply dll_rot1. cbn [app dll] in D. exact D.
Qed.
Lemma dll_linked : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "C'Q:&I'5%112&Cr3(4r2r1%33821%6251&Dr4%73<86%3221p051pT4=1pS:@1pT<B1").
Proof. intros st a r.
intros D. cbn [dll app] in D. change (a :: r ++ [a]) with ((a :: r) ++ [a]) in D.
destruct (@exists_last _ (a :: r) ltac:(discriminate)) as (l0 & z & Ez). rewrite Ez in D |- *.
rewrite <- app_assoc in D. cbn [app] in D. apply linked_prefix in D. tauto.
Qed.
Lemma last_In' {A} (l : list A) d : l <> [] -> In (List.last l d) l.
Proof.
induction l as [|a l IH]; intros H; [congruence|].
destruct l as [|b l']; [left; reflexivity|]. right. apply IH. discriminate.
Qed.
Lemma last_cons_eq {A} (a : A) r d : r <> [] -> List.last (a :: r) d = List.last r d.
Proof. intros H. destruct r; [congruence| reflexivity]. Qed.
Lemma dll_ends st a r : dll st (a :: r) ->
let q := match r with [] => a | b :: _ => b end in
let p := List.last r a in
m_next (MR st a) = Some q /\ m_prev (MR st q) = Some a /\ m_next (MR st p) = Some a /\ m_prev (MR st a) = Some p
/\ linked st (a :: r).
Proof.
intros D. cbn [dll app] in D. cbn zeta.
assert (H1 : m_next (MR st a) = Some match r with [] => a | b :: _ => b end /\ m_prev (MR st match r with [] => a | b :: _ => b end) = Some a).
{ destruct r as [|b r']; cbn in D; tauto. }
change (a :: r ++ [a]) with ((a :: r) ++ [a]) in D.
pose proof (app_removelast_last a (l:=a :: r) ltac:(discriminate)) as Er.
assert (El : List.last (a :: r) a = List.last r a) by (destruct r; reflexivity).
rewrite El in Er. rewrite Er, <- app_assoc in D. cbn [app] in D. apply linked_prefix in D as (D & D2 & D3).
rewrite <- Er in D. tauto.
Qed.
Section EVOL.
Variables (st : mstate) (LS : lhead -> list aptr).
Hypothesis LO : lists_ok st LS.
Local Notation R := (MR st).
Lemma lists_rotate : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "Q:'M&I'5%112':vAr4%211(4r3r2%33:21%83951&Q;&Q4&BvR5%221;%411(2%12C:%A3831'G&Q=r6%62H@%3321:&F&3r5(7%11N%H3O31%53Q0K1%73M:1%=291p0?1p0I1pS<Q51pT8Q41pS:Q71pSBQ91").
Proof. intros h a rest a'.
intros E Hn. pose proof (lo_dll _ _ LO h) as D. rewrite E in D. cbn [dll] in D.
assert (Ha' : head_of (rest ++ [a]) = Some a').
{ destruct rest as [|b r]; cbn in D |- *; [destruct D as (D1 & _)| destruct D as (D1 & _)]; rewrite Hn in D1; congruence. }
constructor.
- intros h'. destruct (decide (h' = h)) as [->|NE].
+ rewrite get_head_set_head, fupd_eq. symmetry. exact Ha'.
+ rewrite get_head_set_head_other, fupd_ne by exact NE. apply (lo_head _ _ LO).
- intros h'. assert (X : forall l, dll st l -> dll (set_head h (Some a') st) l).
{ intros [|b l] Hl; [exact I|]. cbn [dll] in Hl |- *. eapply linked_ext; [| | exact Hl]; intros; unfold MR; rewrite get_meta_rec_set_head; reflexivity. }
destruct (decide (h' = h)) as [->|NE].
+ rewrite fupd_eq. apply X. destruct rest as [|b r].
* cbn. exact D.
* cbn [dll app]. cbn [app] in D. destruct D as (D1 & D2 & D3).
rewrite <- app_assoc. cbn [app].
apply (linked_snoc st (b :: r) a b); [exact D3| exact D1| exact D2].
+ rewrite fupd_ne by exact NE. apply X. apply (lo_dll _ _ LO).
- intros h'. destruct (decide (h' = h)) as [->|NE].
+ rewrite fupd_eq. pose proof (lo_nodup _ _ LO h) as ND. rewrite E in ND.
apply NoDup_cons in ND as [N1 N2]. apply NoDup_app. split; [exact N2|]. split.
* intros x Hx Hx2. apply list_elem_of_singleton in Hx2. subst x. exact (N1 Hx).
* apply NoDup_singleton.
+ rewrite fupd_ne by exact NE. apply (lo_nodup _ _ LO).
- intros h1 h2 m H1 H2.
assert (M : forall h', In m (fupd LS h (rest ++ [a]) h') -> In m (LS h')).
{ intros h' Hm. destruct (decide (h' = h)) as [->|NE']; [| rewrite fupd_ne in Hm by exact NE'; exact Hm].
rewrite fupd_eq in Hm. rewrite E. apply in_app_iff in Hm. cbn in Hm |- *. tauto. }
apply (lo_disj _ _ LO _ _ m); apply M; assumption.
- intros m. unfold MR. rewrite !get_meta_rec_set_head. fold (R m).
destruct (lo_link _ _ LO m) as [L1 L2]. split; [|exact L2]. rewrite <- L1.
split; intros [h' Hm]; exists h'.
+ destruct (decide (h' = h)) as [->|NE']; [| rewrite fupd_ne in Hm by exact NE'; exact Hm].
rewrite fupd_eq in Hm. rewrite E. apply in_app_iff in Hm. cbn in Hm |- *. tauto.
+ destruct (decide (h' = h)) as [->|NE']; [| rewrite fupd_ne by exact NE'; exact Hm].
rewrite fupd_eq. rewrite E in Hm. apply in_app_iff. cbn in Hm |- *. tauto.
Qed.
Section SE.
Local Abbreviation SEC_T_lists_queue := (ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "Q0'M&I':&Q;&Q4&BvR5r1%3221%511(0%11:%:3931'G&Hr3r2%3321;&FvA&3%216(4(7%11G%33H91%63I51%938<1%?2;1p0A1pS@M1pSBO1")) (only parsing).
Variable h : ltac:(sec_ty2 constr:(SEC_T_lists_queue) 0%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_lists_queue) 1%nat 0%nat).
Lemma lists_queue : ltac:(sec_stmt2 constr:(SEC_T_lists_queue) 2%nat 0%nat).
Proof.
intros Hg. pose proof (lists_notin _ _ LO _ Hg) as Gn.
set (st' := queue_st h g st).
pose proof (queue_next h g st) as QN. pose proof (queue_prev h g st) as QP. pose proof (queue_head h g st) as QH.
fold st' in QN, QP, QH.
pose proof (lo_head _ _ LO h) as Hh.
destruct (LS h) as [|a rest] eqn:E.
-
cbn [head_of] in Hh. rewrite Hh in QN, QP, QH.
assert (EXT : forall l, ~ In g l -> dll st l -> dll st' l).
{ intros [|b l] Hgl Hl; [exact I|]. cbn [dll] in Hl |- *. eapply linked_ext; [| | exact Hl].
+ intros x Hx. rewrite QN. rewrite aptr_eqb_neq; [reflexivity|]. intros ->. apply Hgl. apply In_removelast in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
+ intros x Hx. rewrite QP. rewrite aptr_eqb_neq; [reflexivity|]. intros ->. apply Hgl. apply In_tl in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto. }
constructor.
+ intros h'. rewrite QH. destruct (decide (h' = h)) as [->|NE]; [rewrite fupd_eq; reflexivity|]. rewrite fupd_ne by exact NE. apply (lo_head _ _ LO).
+ intros h'. destruct (decide (h' = h)) as [->|NE].
* rewrite fupd_eq. cbn. rewrite QN, QP, aptr_eqb_refl. auto.
* rewrite fupd_ne by exact NE. apply EXT; [apply Gn| apply (lo_dll _ _ LO)].
+ intros h'. destruct (decide (h' = h)) as [->|NE]; [rewrite fupd_eq; apply NoDup_singleton| rewrite fupd_ne by exact NE; apply (lo_nodup _ _ LO)].
+ intros h1 h2 m H1 H2. destruct (decide (h1 = h)) as [->|N1], (decide (h2 = h)) as [->|N2]; try congruence.
* rewrite fupd_eq in H1. rewrite fupd_ne in H2 by exact N2. cbn in H1. destruct H1 as [<-|[]]. exfalso. exact (Gn _ H2).
* rewrite fupd_eq in H2. rewrite fupd_ne in H1 by exact N1. cbn in H2. destruct H2 as [<-|[]]. exfalso. exact (Gn _ H1).
* rewrite fupd_ne in H1 by exact N1. rewrite fupd_ne in H2 by exact N2. exact (lo_disj _ _ LO _ _ _ H1 H2).
+ intros m. rewrite QN, QP. destruct (aptr_eqb_spec m g) as [->|NE].
* split; [| intros; discriminate]. split; [intros; discriminate|]. intros _. exists h. rewrite fupd_eq. left. reflexivity.
* destruct (lo_link _ _ LO m) as [L1 L2]. split; [|exact L2]. rewrite <- L1. split; intros [h' Hm]; exists h'.
-- destruct (decide (h' = h)) as [->|NE']; [rewrite fupd_eq in Hm; cbn in Hm; destruct Hm as [->|[]]; congruence|].
rewrite fupd_ne in Hm by exact NE'. exact Hm.
-- destruct (decide (h' = h)) as [->|NE']; [rewrite E in Hm; destruct Hm|]. rewrite fupd_ne by exact NE'. exact Hm.
-
cbn [head_of] in Hh. rewrite Hh in QN, QP, QH.
destruct (lists_head_prev _ _ LO h a rest E) as [Pa Nz]. remember (List.last rest a) as z eqn:Ez.
rewrite Pa in QN. cbn [optr_eqb] in QN.
assert (Zin : In z (a :: rest)).
{ rewrite Ez. apply last_In. }
assert (Ga : a <> g) by (intros ->; apply (Gn h); rewrite E; left; reflexivity).
assert (Gz : z <> g) by (intros X; apply (Gn h); rewrite E, <- X; exact Zin).
rewrite (aptr_eqb_neq a g) in QN by exact Ga.
assert (QN' : forall x, m_next (MR st' x) = if aptr_eqb x z then Some g else if aptr_eqb x g then Some a else m_next (R x)).
{ intros x. rewrite QN.
repeat match goal with |- context [aptr_eqb ?u ?v] => destruct (aptr_eqb_spec u v) end; subst; try reflexivity; congruence. }
clear QN.
pose proof (lo_nodup _ _ LO h) as ND. rewrite E in ND.
assert (Hl1 : exists l1, a :: rest = l1 ++ [z] /\ ~ In z l1).
{ assert (Elz : List.last (a :: rest) a = z) by (rewrite Ez; destruct rest; reflexivity).
pose proof (app_removelast_last a (l:=a :: rest) ltac:(discriminate)) as Er. rewrite Elz in Er.
exists (removelast (a :: rest)). split; [exact Er|].
intros Hz. rewrite Er in ND. exact (proj1 (NoDup_In_split _ _ _ ND) Hz). }
destruct Hl1 as (l1 & El1 & Zl1).
assert (Al : ~ In a rest) by (apply NoDup_cons in ND as [N _]; intros X; apply N; apply list_elem_of_In; exact X).
assert (EXT : forall l, (forall x, In x l -> x <> a /\ x <> z /\ x <> g) -> dll st l -> dll st' l).
{ intros [|b l] Hx Hl; [exact I|]. cbn [dll] in Hl |- *. eapply linked_ext; [| | exact Hl].
+ intros x Hin. apply In_removelast in Hin. assert (In x (b :: l)) by (apply in_app_iff in Hin; cbn in Hin; cbn; tauto).
destruct (Hx x H) as (X1 & X2 & X3). rewrite QN'. rewrite !aptr_eqb_neq by assumption. reflexivity.
+ intros x Hin. apply In_tl in Hin. assert (In x (b :: l)) by (apply in_app_iff in Hin; cbn in Hin; cbn; tauto).
destruct (Hx x H) as (X1 & X2 & X3). rewrite QP. rewrite !aptr_eqb_neq by assumption. reflexivity. }
constructor.
+ intros h'. rewrite QH. destruct (decide (h' = h)) as [->|NE]; [rewrite fupd_eq; reflexivity|]. rewrite fupd_ne by exact NE. apply (lo_head _ _ LO).
+ intros h'. destruct (decide (h' = h)) as [->|NE].
* rewrite fupd_eq. cbn [dll app]. rewrite <- app_assoc. cbn [app].
assert (L0 : linked st' (a :: rest)).
{ pose proof (lo_dll _ _ LO h) as D. rewrite E in D. cbn [dll] in D. rewrite El1, <- app_assoc in D. cbn [app] in D.
apply linked_prefix in D as (D & _ & _). rewrite El1.
eapply linked_ext; [| | exact D].
- intros x Hx. rewrite removelast_app in Hx by discriminate. cbn in Hx. rewrite app_nil_r in Hx.
rewrite QN'. rewrite (aptr_eqb_neq x z) by (intros ->; exact (Zl1 Hx)).
rewrite (aptr_eqb_neq x g); [reflexivity|]. intros ->. apply (Gn h). rewrite E, El1. apply in_app_iff. left. exact Hx.
- intros x Hx. rewrite QP.
assert (Hx' : In x rest). { rewrite <- El1 in Hx. exact Hx. }
rewrite (aptr_eqb_neq x a) by (intros ->; exact (Al Hx')).
rewrite (aptr_eqb_neq x g); [reflexivity|]. intros ->. apply (Gn h). rewrite E. right. exact Hx'. }
change (a :: rest ++ [g; a]) with ((a :: rest) ++ [g; a]).
rewrite El1 in L0 |- *. rewrite <- app_assoc. cbn [app].
apply (linked_app st' z l1 [g; a]). split; [exact L0|]. cbn.
rewrite !QN', !QP, Pa.
repeat match goal with |- context [aptr_eqb ?u ?v] => destruct (aptr_eqb_spec u v) end; subst; try congruence; repeat split; congruence.
* rewrite fupd_ne by exact NE. apply EXT; [| apply (lo_dll _ _ LO)].
intros x Hx. repeat split; intros ->.
-- apply NE. eapply (lo_disj _ _ LO); [exact Hx| rewrite E; left; reflexivity].
-- apply NE. eapply (lo_disj _ _ LO); [exact Hx| rewrite E; exact Zin].
-- exact (Gn _ Hx).
+ intros h'. destruct (decide (h' = h)) as [->|NE]; [| rewrite fupd_ne by exact NE; apply (lo_nodup _ _ LO)].
rewrite fupd_eq. apply NoDup_app. split; [exact ND|]. split; [| apply NoDup_singleton].
intros x Hx Hx2. apply list_elem_of_singleton in Hx2. subst x. apply (Gn h). rewrite E. apply list_elem_of_In. exact Hx.
+ intros h1 h2 m H1 H2.
assert (M : forall h', In m (fupd LS h ((a :: rest) ++ [g]) h') -> In m (LS h') \/ (m = g /\ h' = h)).
{ intros h' Hm. destruct (decide (h' = h)) as [->|NE']; [| rewrite fupd_ne in Hm by exact NE'; auto].
rewrite fupd_eq in Hm. apply in_app_iff in Hm. destruct Hm as [Hm|[<-|[]]]; [left; rewrite E; exact Hm| right; auto]. }
destruct (M _ H1) as [M1|[Em1 Eh1]], (M _ H2) as [M2|[Em2 Eh2]]; subst; try reflexivity.
* exact (lo_disj _ _ LO _ _ _ M1 M2).
* exfalso. exact (Gn _ M1).
* exfalso. exact (Gn _ M2).
+ intros m. rewrite QN', QP. destruct (aptr_eqb_spec m z) as [->|NEz].
* split; [| intros; discriminate]. split; [intros; discriminate|]. intros _. exists h. rewrite fupd_eq. apply in_app_iff. left. exact Zin.
* destruct (aptr_eqb_spec m g) as [->|NEg].
-- split; [| intros; discriminate]. split; [intros; discriminate|]. intros _. exists h. rewrite fupd_eq. apply in_app_iff. right. left. reflexivity.
-- destruct (lo_link _ _ LO m) as [L1 L2]. split.
++ rewrite <- L1. split; intros [h' Hm]; exists h'.
** destruct (decide (h' = h)) as [->|NE']; [| rewrite fupd_ne in Hm by exact NE'; exact Hm].
rewrite fupd_eq in Hm. rewrite E. apply in_app_iff in Hm. destruct Hm as [Hm|[->|[]]]; [exact Hm| congruence].
** destruct (decide (h' = h)) as [->|NE']; [| rewrite fupd_ne by exact NE'; exact Hm].
rewrite fupd_eq. apply in_app_iff. left. rewrite E in Hm. exact Hm.
++ intros Hn. rewrite (aptr_eqb_neq m a); [exact (L2 Hn)|]. intros ->.
apply (lists_in_next_some _ _ LO h a); [rewrite E; left; reflexivity| exact Hn].
Qed.
End SE.
Lemma lists_dequeue : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_List "N'M&I'5%112':vAr4%211&3r2(4r3r1%33<21%63=51%;3<81'G&Jr5vR5%332>1&F%>3E;=%23B51%8241p0:1pSNG1pSLH1pT0K1pSBM1").
Proof. intros h m l1 l2.
intros E. set (st' := dequeue h m st).
pose proof (dequeue_next h m st) as DN. pose proof (dequeue_prev h m st) as DP. pose proof (dequeue_head h m st) as DH.
fold st' in DN, DP, DH.
pose proof (lo_nodup _ _ LO h) as ND. rewrite E in ND.
destruct (NoDup_In_split _ _ _ ND) as [N1 N2].
assert (Min : In m (LS h)) by (rewrite E; apply in_app_iff; right; left; reflexivity).
pose proof (lo_head _ _ LO h) as Hh. rewrite E in Hh.
pose proof (lo_dll _ _ LO h) as D. rewrite E in D.
apply dll_rot in D. cbn [app] in D. remember (l2 ++ l1) as rest eqn:Erest.
assert (NDr : NoDup (m :: rest)).
{ subst rest. apply NoDup_ListNoDup. apply (Permutation_NoDup (l:=l1 ++ m :: l2)).
- apply Permutation_sym. etransitivity; [| apply Permutation_middle]. apply perm_skip. apply Permutation_app_comm.
- apply NoDup_ListNoDup. exact ND. }
apply NoDup_cons in NDr as [Nmr NDr]. assert (Nmr' : ~ In m rest) by (intros X; apply Nmr; apply list_elem_of_In; exact X).
assert (Rin : forall x, In x rest <-> In x l1 \/ In x l2) by (intros x; subst rest; rewrite in_app_iff; tauto).
destruct (dll_ends st m rest D) as (Nm & Pq & Np & Pm & LK).
assert (MEM : forall h' x, In x (fupd LS h (l1 ++ l2) h') -> In x (LS h') /\ x <> m).
{ intros h' x Hx. destruct (decide (h' = h)) as [->|NE].
- rewrite fupd_eq in Hx. apply in_app_iff in Hx. split.
+ rewrite E. apply in_app_iff. cbn. tauto.
+ intros ->. tauto.
- rewrite fupd_ne in Hx by exact NE. split; [exact Hx|]. intros ->. apply NE. exact (lo_disj _ _ LO _ _ _ Hx Min). }
assert (MEM' : forall h' x, In x (LS h') -> x <> m -> In x (fupd LS h (l1 ++ l2) h')).
{ intros h' x Hx NE. destruct (decide (h' = h)) as [->|NE'].
- rewrite fupd_eq. rewrite E in Hx. apply in_app_iff in Hx. apply in_app_iff. cbn in Hx. destruct Hx as [?|[?|?]]; [tauto|congruence|tauto].
- rewrite fupd_ne by exact NE'. exact Hx. }
assert (ND12 : NoDup (l1 ++ l2)).
{ apply NoDup_app in ND as (A1 & A2 & A3). apply NoDup_cons in A3 as [_ A3].
apply NoDup_app. split; [exact A1|]. split; [| exact A3]. intros x Hx Hx2. apply (A2 x Hx). right. exact Hx2. }
destruct rest as [|q r].
-
cbn in Nm, Pm. rewrite Nm in DN, DP, DH. cbn [optr_eqb] in DN, DP, DH. rewrite aptr_eqb_refl in DN, DP, DH.
assert (E12 : l1 = [] /\ l2 = []) by (destruct l2; [destruct l1; [auto|discriminate]| discriminate]).
destruct E12 as [-> ->]. cbn [app] in *.
constructor.
+ intros h'. rewrite DH. destruct (decide (h' = h)) as [->|NE]; [rewrite fupd_eq; reflexivity|]. rewrite fupd_ne by exact NE. apply (lo_head _ _ LO).
+ intros h'. destruct (decide (h' = h)) as [->|NE]; [rewrite fupd_eq; exact I|]. rewrite fupd_ne by exact NE.
pose proof (lo_dll _ _ LO h') as D'. destruct (LS h') as [|c l] eqn:E'; [exact I|]. cbn [dll] in D' |- *.
eapply linked_ext; [| | exact D']; intros x Hx; [rewrite DN| rewrite DP]; rewrite aptr_eqb_neq; try reflexivity;
intros ->; apply NE; [apply In_removelast in Hx| apply In_tl in Hx]; apply in_app_iff in Hx; cbn in Hx;
(eapply (lo_disj _ _ LO); [| exact Min]); rewrite E'; cbn; tauto.
+ intros h'. destruct (decide (h' = h)) as [->|NE]; [rewrite fupd_eq; apply NoDup_nil_2| rewrite fupd_ne by exact NE; apply (lo_nodup _ _ LO)].
+ intros h1 h2 x H1 H2. apply MEM in H1 as [H1 _]. apply MEM in H2 as [H2 _]. exact (lo_disj _ _ LO _ _ _ H1 H2).
+ intros x. rewrite DN, DP. destruct (aptr_eqb_spec x m) as [->|NE].
* split; [| reflexivity]. split; [| congruence]. intros [h' Hx]. apply MEM in Hx as [_ Hx]. congruence.
* destruct (lo_link _ _ LO x) as [L1 L2]. split; [| exact L2]. rewrite <- L1. split; intros [h' Hx]; exists h'.
-- apply MEM in Hx. tauto.
-- apply MEM'; assumption.
-
cbn zeta in Nm, Pq. remember (List.last (q :: r) m) as p eqn:Ep.
assert (Qin : In q (q :: r)) by (left; reflexivity).
assert (Pin : In p (q :: r)) by (rewrite Ep; apply last_In'; discriminate).
assert (NEq : q <> m) by (intros ->; exact (Nmr' Qin)).
assert (NEp : p <> m) by (intros ->; exact (Nmr' Pin)).
rewrite Nm, Pm in DN. rewrite Nm in DP. rewrite Nm in DH. cbn [optr_eqb] in DN, DP, DH.
rewrite (aptr_eqb_neq q m) in DN, DP, DH by exact NEq.
assert (DN' : forall x, m_next (MR st' x) = if aptr_eqb x m then None else if aptr_eqb x p then Some q else m_next (R x)).
{ intros x. rewrite DN. destruct (aptr_eqb x m); [reflexivity|]. destruct (aptr_eqb_spec p x), (aptr_eqb_spec x p); subst; try reflexivity; congruence. }
assert (DP' : forall x, m_prev (MR st' x) = if aptr_eqb x m then None else if aptr_eqb x q then Some p else m_prev (R x)).
{ intros x. rewrite DP. destruct (aptr_eqb x m); [reflexivity|]. destruct (aptr_eqb_spec q x), (aptr_eqb_spec x q); subst; try reflexivity; congruence. }
clear DN DP.
assert (EXT : forall l, ~ In m l -> ~ In p (removelast l) -> ~ In q (tl l) -> linked st l -> linked st' l).
{ intros l Hm Hp Hq Hl. eapply linked_ext; [| | exact Hl].
- intros x Hx. rewrite DN'. rewrite (aptr_eqb_neq x m) by (intros ->; exact (Hm (In_removelast _ _ Hx))).
rewrite (aptr_eqb_neq x p) by (intros ->; exact (Hp Hx)). reflexivity.
- intros x Hx. rewrite DP'. rewrite (aptr_eqb_neq x m) by (intros ->; exact (Hm (In_tl _ _ Hx))).
rewrite (aptr_eqb_neq x q) by (intros ->; exact (Hq Hx)). reflexivity. }
assert (CYC : dll st' (q :: r)).
{ cbn [dll app]. cbn [linked] in LK. destruct LK as (_ & _ & LK).
pose proof (app_removelast_last m (l:=q :: r) ltac:(discriminate)) as Er.
rewrite <- Ep in Er.
change (q :: r ++ [q]) with ((q :: r) ++ [q]). rewrite Er, <- app_assoc. cbn [app].
apply linked_snoc.
- apply EXT.
+ intros Hm. rewrite <- Er in Hm. exact (Nmr' Hm).
+ rewrite removelast_app by discriminate. cbn. rewrite app_nil_r. intros Hp.
pose proof NDr as X. rewrite Er in X. exact (proj1 (NoDup_In_split _ _ _ X) Hp).
+ intros Hq. rewrite <- Er in Hq. cbn in Hq. apply NoDup_cons in NDr as [X _]. apply X. apply list_elem_of_In. exact Hq.
+ rewrite <- Er. exact LK.
- rewrite DN'. rewrite (aptr_eqb_neq p m) by exact NEp. rewrite aptr_eqb_refl. reflexivity.
- rewrite DP'. rewrite (aptr_eqb_neq q m) by exact NEq. rewrite aptr_eqb_refl. reflexivity. }
rewrite Erest in CYC. apply dll_rot in CYC.
constructor.
+ intros h'. rewrite DH. destruct (decide (h' = h)) as [->|NE]; [| rewrite fupd_ne by exact NE; apply (lo_head _ _ LO)].
rewrite fupd_eq, Hh. destruct l1 as [|c l1']; cbn [app head_of].
* rewrite optr_eqb_refl. rewrite app_nil_r in Erest. rewrite <- Erest. reflexivity.
* cbn [optr_eqb]. rewrite (aptr_eqb_neq c m) by (intros ->; apply N1; left; reflexivity). reflexivity.
+ intros h'. destruct (decide (h' = h)) as [->|NE]; [rewrite fupd_eq; exact CYC|]. rewrite fupd_ne by exact NE.
pose proof (lo_dll _ _ LO h') as D'. destruct (LS h') as [|c l] eqn:E'; [exact I|]. cbn [dll] in D' |- *.
apply EXT; [| | | exact D'].
* intros Hm. apply NE. eapply (lo_disj _ _ LO); [| exact Min]. rewrite E'. apply in_app_iff in Hm. cbn in Hm |- *. tauto.
* intros Hp. apply In_removelast in Hp. apply NE. eapply (lo_disj _ _ LO _ h p); [rewrite E'| rewrite E; apply in_app_iff; cbn; pose proof (proj1 (Rin p) Pin); tauto].
apply in_app_iff in Hp. cbn in Hp |- *. tauto.
* intros Hq. apply In_tl in Hq. apply NE. eapply (lo_disj _ _ LO _ h q); [rewrite E'| rewrite E; apply in_app_iff; cbn; pose proof (proj1 (Rin q) Qin); tauto].
apply in_app_iff in Hq. cbn in Hq |- *. tauto.
+ intros h'. destruct (decide (h' = h)) as [->|NE]; [rewrite fupd_eq; exact ND12| rewrite fupd_ne by exact NE; apply (lo_nodup _ _ LO)].
+ intros h1 h2 x H1 H2. apply MEM in H1 as [H1 _]. apply MEM in H2 as [H2 _]. exact (lo_disj _ _ LO _ _ _ H1 H2).
+ intros x. rewrite DN', DP'. destruct (aptr_eqb_spec x m) as [->|NE].
* split; [| reflexivity]. split; [| congruence]. intros [h' Hx]. apply MEM in Hx as [_ Hx]. congruence.
* destruct (aptr_eqb_spec x p) as [->|NEp'].
-- split; [| intros; discriminate]. split; [intros; discriminate|]. intros _. exists h. apply MEM'; [| exact NEp].
rewrite E. apply in_app_iff. cbn. pose proof (proj1 (Rin p) Pin). tauto.
-- destruct (lo_link _ _ LO x) as [L1 L2]. split.
++ rewrite <- L1. split; intros [h' Hx]; exists h'; [apply MEM in Hx; tauto| apply MEM'; assumption].
++ intros Hn. destruct (aptr_eqb_spec x q) as [->|NEq']; [| exact (L2 Hn)].
exfalso. refine (lists_in_next_some _ _ LO h q _ Hn). rewrite E. apply in_app_iff. cbn. pose proof (proj1 (Rin q) Qin). tauto.
Qed.
End EVOL.
End CEIL_WRAP_1.
