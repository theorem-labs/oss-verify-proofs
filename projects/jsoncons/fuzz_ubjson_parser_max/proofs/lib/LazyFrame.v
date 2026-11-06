(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import DivergeSim.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__LazyFrame () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DivergeSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LazyFrame."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1false"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2or"; "3lt"; "4Z"]; ["5Segment"; "6MachineOk"; "6access_report"; "6machine_result"; "6machine_state"; "6memory_access"; "6mkAccessReport"; "6ms_svc_pending"; "6step_accesses"; "7mi_account_step"; "8Model"; "8access_pages_acc"; "8accesses_pages"; "8m_vm_lazy"; "8m_vm_materialized"; "8materialize_accesses"]; ["8materialize_model_accesses"; "8newly_materialized_pages"; "8page_base_of"; "8page_in_ranges"; "8page_insert"; "8with_vm_backing"; "9to_spin"; ":access_outside_range"; ":accesses_outside_lazy"; ";In"; "<add"; "<of_nat"; "0a"; "0accs"; "0base"; "0k"]; ["0lazy"; "0limit"; "0lo"; "0m"; "0materialized"; "0model"; "0ms"; "0ms'"; "0n"; "0p"; "0pages"; "0q"; "0ranges"; "0segs"; "=bv"; "=bv_unsigned"]; ["0sz"; "0used"]]).
Definition access_outside_range (a : word) (n : nat) (lo sz : word) : Prop :=
(bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z /\
(bv_unsigned a + Z.of_nat n <= bv_unsigned lo
\/ bv_unsigned lo + bv_unsigned sz <= bv_unsigned a)%Z.
Definition accesses_outside_lazy
(accs : list (word * nat)) (lazy : list (word * word)) : Prop :=
forall a n lo sz, In (a, n) accs -> In (lo, sz) lazy ->
access_outside_range a n lo sz.
Lemma filter_all_false {A} : forall (f : A -> bool) (l : list A),
(forall x, In x l -> f x = false) -> List.filter f l = [].
Proof.
intros f l H; induction l as [|x l IH]; cbn; [reflexivity|].
rewrite (H x (or_introl eq_refl)).
apply IH. intros y Hy. apply H. right. exact Hy.
Qed.
Lemma with_vm_backing_id : ltac2:(TCodec.tc2 tcn__LazyFrame ";'J';&Q5&Mr1%211&N%113%63314%83915pS8:1").
Proof.
intros [fd [maps lazy materialized] io fs proc lim tm]. reflexivity.
Qed.
Lemma materialize_accesses_no_new : ltac2:(TCodec.tc2 tcn__LazyFrame "Q5'4'9'QNyR0%211%4211%611%713'?'5%9261%;11';&Q1r5r4r1%43321(6%11?%83=31'7%11?&Or6r3r2%453=<21(1%12F?%B3831p0;1pRLE1pS4I1pT4J1pS:L1pS2N1").
Proof.
intros lazy materialized used limit accs Hnew.
unfold materialize_accesses. rewrite Hnew. reflexivity.
Qed.
Lemma page_insert_in : ltac2:(TCodec.tc2 tcn__LazyFrame "F'QNyR0%211'4%112&Q9r3&Q4r2r1%3221%63951'=';r4%23=19%;3>28%5221p071pSF?1pSHB1pSDC1").
Proof.
intros p q pages H. unfold page_insert in H.
destruct (page_mem q pages); [right; exact H|].
destruct H as [Hqp | H]; [left; symmetry; exact Hqp | right; exact H].
Qed.
Lemma access_pages_acc_in : ltac2:(TCodec.tc2 tcn__LazyFrame "Q8'5'?'4'QNyR0%211%411&Q9r1&Kr3r4r2%43321%73961'=%93;46'<':&>r6%22=1';&Q2&Q:r5&Q;%11C%4231%611%83ID1%=2:1qS0Q01%@2Q11%C2B1p0E1pSDO1pSFO1pRNQ51pSBQ71").
Proof.
induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p H.
- left; exact H.
- destruct (IH (base + 1)%Z _ p H) as [Hin | (k & Hk & ->)].
+ destruct (page_insert_in _ _ _ Hin) as [-> | Hin'].
* right. exists 0%nat. split; [lia|]. f_equal. lia.
* left; exact Hin'.
+ right. exists (S k). split; [lia|]. f_equal. lia.
Qed.
Lemma accesses_pages_in : ltac2:(TCodec.tc2 tcn__LazyFrame "QB'4'9'QNyR0%211'5%5221%711%814&Q9r1&Lr3r2%3221%63;51'=%83=45'<':(8%14A@98r7%>3A21&>%12?<';r5&Q2&Q:&QO%12LC&Q;%11G%5231%711%:3Q091%B2<1%C2?1qS0Q21%F2Q31qSBQ41%H2Q51qRJQ71%J2Q81%M2L1p0O1pSDQ;1pSFQ81pRLQ:1").
Proof.
induction accs as [|[a n] accs IH]; cbn [accesses_pages];
intros pages p H.
- left; exact H.
- destruct (IH _ p H) as [Hin | (a' & n' & k & Hin & Hk & Hp)].
+ destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin)
as [Hp | (k & Hk & Hp)].
* left; exact Hp.
* right. exists a, n, k.
split; [left; reflexivity | split; assumption].
+ right. exists a', n', k.
split; [right; exact Hin | split; assumption].
Qed.
Lemma page_in_ranges_outside : ltac2:(TCodec.tc2 tcn__LazyFrame "Q='4'9'QNyR0%211%4211%611'5&>r1r2%3221&Q9(8%14::45r7%43;21&Q7r6r3%34521:p051pT2B1pS6C1';'2&Q3&Q2&Q:&QOr5%22L1&Q;%11>%6231%811%:21B(3%>3=21p0@1p0M1pS0Q21pSBQ31pRJQ71pS2Q61").
Proof.
intros lazy a n k Hk Hout.
set (z := (bv_unsigned a + Z.of_nat k)%Z).
apply Bool.not_true_is_false. intro Htrue.
unfold page_in_ranges in Htrue.
apply existsb_exists in Htrue.
destruct Htrue as ([lo sz] & Hin & Htest).
cbn [fst snd] in Htest.
apply andb_true_iff in Htest. destruct Htest as [Hlo Hhi].
apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
destruct (Hout lo sz Hin) as [Hnw Hdisj].
pose proof (bv_unsigned_in_range 64 a) as Ha.
pose proof (bv_unsigned_in_range 64 lo) as Hlo_rg.
pose proof (bv_unsigned_in_range 64 sz) as Hsz_rg.
assert (Hz0 : (0 <= z)%Z) by (unfold z; lia).
assert (Hq0 : (0 <= z / page_size)%Z)
by (apply Z.div_pos; [exact Hz0 | unfold page_size; lia]).
pose proof (Z.div_mod z page_size
ltac:(unfold page_size; lia)) as Hdm.
pose proof (Z.mod_pos_bound z page_size
ltac:(unfold page_size; lia)) as Hmb.
assert (Hpb : bv_unsigned (page_base_of z)
= ((z / page_size) * page_size)%Z).
{ unfold page_base_of. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
change (bv_modulus 64) with (2 ^ 64)%Z.
unfold page_size in *. unfold z in *. lia. }
rewrite Hpb in Hlo, Hhi.
unfold page_size in *. unfold z in *. lia.
Qed.
Theorem materialize_model_accesses_disjoint : ltac2:(TCodec.tc2 tcn__LazyFrame "K'J'4'9'QNyR0%211'5%5221%711&Q8r1&Mr2%211%5241';'7%11A&Q0r3%2218(1%12F3%83631p0:1pRLA1pS8J1").
Proof.
intros m accs Hout.
assert (Hnew : newly_materialized_pages
(m_vm_lazy m) (m_vm_materialized m) accs = []).
{ unfold newly_materialized_pages. apply filter_all_false.
intros p Hp.
destruct (accesses_pages_in accs [] p Hp)
as [[] | (a & n & k & Hin & Hk & ->)].
rewrite (page_in_ranges_outside (m_vm_lazy m) a n k Hk).
- reflexivity.
- intros lo sz Hlz. exact (Hout a n lo sz Hin Hlz). }
unfold materialize_model_accesses.
rewrite (materialize_accesses_no_new (m_vm_lazy m) (m_vm_materialized m)
(vm_backing_used m) (vm_limit (m_vmmaps m)) accs Hnew).
cbv iota beta.
rewrite with_vm_backing_id. reflexivity.
Qed.
Lemma mi_account_step_disjoint : ltac2:(TCodec.tc2 tcn__LazyFrame "Q='4'@%211'D'J&E%611';'C'B%117%311&Hr5r4%3221(A(Fr2r1%33A21%52;1%?3;71&Q8&M%11;%3281'9%12IH%E11&Ir7r6%3321D(8%14Q0OEF%D281%N3841p0<1p0A1pSJQ21pS@Q61pS<Q61pS>Q81pSLQ:1").
Proof.
intros segs ms model ms' ranges Hstep Hout.
rewrite (mi_account_step_of_accesses segs ms model ms' ranges Hstep).
rewrite (materialize_model_accesses_disjoint model ranges Hout).
reflexivity.
Qed.
Lemma ts_spin_disjoint : ltac2:(TCodec.tc2 tcn__LazyFrame "Q@'4'@%211'D'J&E%611';'7'QNyR0%211%411&Gr3%211(0%116%;3631'C'B%11B%311&Hr5r4%3221(A(Fr2%23K51%42:1%I3:61&Q8&M%11:%32F1'Q6r7r6%3321@p051p0:1p0I1pSJQ61pS<Q91pS>Q;1pSLQ=1").
Proof.
intros segs ms model ranges Hsvc Hstep Hout.
apply ts_spin; [exact Hsvc|].
exact (mi_account_step_disjoint segs ms model ms ranges Hstep Hout).
Qed.
Lemma ts_step_disjoint : ltac2:(TCodec.tc2 tcn__LazyFrame "QE'4'@%211'D'J&E%611';'7'QNyR0%211%411&Gr4%211(0%116%;3631'C'B%11B%311&Hr6r5%3221(A(Fr3r2%33L21%52;1%J3;71&Q8&M%11;%3281'Q6r8%231?@r9r7%53241p041p081p0=1p0M1pSJQ:1pS@Q>1pS<Q>1pS>Q@1pSLQB1").
Proof.
intros segs ms model ms' ranges Hsvc Hstep Hout Hspin.
exact (ts_step segs ms model ms' model Hsvc
(mi_account_step_disjoint segs ms model ms' ranges Hstep Hout)
Hspin).
Qed.
