(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase ARep ARepQ ARepFrame AHeapP AKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma size_of_class_24 : size_of_class K_BATCH_CLASS = 8192.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma batches_bytes_app : forall l1 l2, batches_bytes (l1 ++ l2) = batches_bytes l1 + batches_bytes l2.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0010=35114124364.5000001S".
induction l1 as [|b l1 IH]; intros l2; cbn; [reflexivity| rewrite IH; unfold batches_bytes; lia]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma batches_bytes_cons : forall b l, batches_bytes (b :: l) = b_size b + batches_bytes l.
Proof. reflexivity. Qed.
#[using="Type"] Lemma batches_bytes_nil : batches_bytes [] = 0.
Proof. reflexivity. Qed.
#[using="Type"] Lemma batches_bytes_lb : forall l, Forall (fun b => Q_BATCH_BYTES <= b_size b) l -> Q_BATCH_BYTES * Z.of_nat (length l) <= batches_bytes l.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=45721698669.256810311235.7000001008SS2IH2H1".
induction l as [|b l IH]; intros HF; cbn [length]; [rewrite batches_bytes_nil; lia|].
rewrite batches_bytes_cons. inversion HF; subst. specialize (IH ltac:(assumption)). unfold Q_BATCH_BYTES in *. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma batches_bytes_In : forall l b, Forall (fun b => Q_BATCH_BYTES <= b_size b) l -> In b l -> Q_BATCH_BYTES <= b_size b <= batches_bytes l.
Proof.
induction l as [|a l IH]; intros b HF Hin; [destruct Hin|].
rewrite batches_bytes_cons. inversion HF; subst. pose proof (batches_bytes_lb l ltac:(assumption)) as LB.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>2848992566.8  30916122756.1000000700>S2H12LBS2IH2H1".
destruct Hin as [<-|Hin]; [unfold Q_BATCH_BYTES in *; lia|]. specialize (IH b ltac:(assumption) Hin). unfold Q_BATCH_BYTES in *; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma qaddrs_app : forall L qs1 qs2, qaddrs L (qs1 ++ qs2) = qaddrs L qs1 ++ qaddrs L qs2.
Proof. intros. unfold qaddrs. apply map_app. Qed.
#[using="Type"] Lemma qlast_app1 : forall L qs q, qlast L (qs ++ [q]) = abatch_addr L (qb_slot q).
Proof. intros. unfold qlast. rewrite qaddrs_app. cbn [qaddrs map]. apply last_last. Qed.
#[using="Type"] Lemma qfirst_app : forall L qs1 qs2, qs1 <> [] -> qfirst L (qs1 ++ qs2) = qfirst L qs1.
Proof. intros L [|q qs1] qs2 NE; [congruence| reflexivity]. Qed.
#[using="Type"] Lemma last_app_ne : forall {A} (l1 l2 : list A) d, l2 <> [] -> last (l1 ++ l2) d = last l2 d.
Proof.
intros A l1 l2 d NE. rewrite (app_removelast_last d NE) at 1. rewrite app_assoc, last_last.
reflexivity.
Qed.
#[using="Type"] Lemma qlast_app : forall L qs1 qs2, qs2 <> [] -> qlast L (qs1 ++ qs2) = qlast L qs2.
Proof.
intros L qs1 qs2 NE. unfold qlast. rewrite qaddrs_app. apply last_app_ne.
unfold qaddrs. destruct qs2; [congruence| discriminate].
Qed.
#[using="Type"] Lemma qhdrs_length : forall L chs ks, length ks = length chs -> length (qhdrs L chs ks) = length chs.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0060=11524744599.816191166211.618148078718.824288070069.824930583282.324930583282.500000100600;00@00A00FFS3LENS3LENS3LENSS3LEN".
induction chs as [|ch chs IH]; intros [|k ks] LEN; cbn in *; try lia.
rewrite length_app, IH by lia. cbn. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma qhdrs_cons : forall L ch chs k ks, qhdrs L (ch :: chs) (k :: ks) = qhdrs L chs ks ++ [qhdr L ch k].
Proof. reflexivity. Qed.
#[using="Type"] Lemma qentries_app : forall bs1 qs1 bs2 qs2, length qs1 = length bs1 ->
qentries (bs1 ++ bs2) (qs1 ++ qs2) = qentries bs1 qs1 ++ qentries bs2 qs2.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0050=16135699603.925802875357.426893513338.728062073526.96266171465.6 00000100200700<00AFFS3LENS3LENS3LEN".
induction bs1 as [|b bs1 IH]; intros [|q qs1] bs2 qs2 LEN; cbn in *; try lia; [reflexivity|].
rewrite IH by lia. rewrite app_assoc. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma abatches_to_app : forall L m bs1 qs1 bs2 qs2 nxt, length qs1 = length bs1 ->
abatches_to L m (bs1 ++ bs2) (qs1 ++ qs2) nxt <-> abatches_to L m bs1 qs1 (hd nxt (qaddrs L qs2)) /\ abatches_to L m bs2 qs2 nxt.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>28062073526.1233754457640.7 39375445663.1043768290460.9 60748825868.1200000500600;00@00AS3LENFS3LENS3LENF".
induction bs1 as [|b bs1 IH]; intros [|q qs1] bs2 qs2 nxt LEN; cbn in *; try lia; [tauto|].
rewrite IH by lia. rewrite qaddrs_app.
assert (E : hd nxt (qaddrs L qs1 ++ qaddrs L qs2) = hd (hd nxt (qaddrs L qs2)) (qaddrs L qs1)).
{ destruct qs1; cbn; reflexivity. }
rewrite E. tauto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma disjoint_from_Forall : forall W A n,
Forall (fun iv => snd iv <= A \/ A + n <= fst iv) W -> disjoint_from W A n.
Proof. induction W as [|[lo hi] W IH]; intros A n HF; cbn; [exact I|]. inversion HF; subst. cbn in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010>68595136228.10000004S2H1".
split; [lia| apply IH; assumption]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section Frames.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
#[using="MU WM"] Lemma abatch_cells_frame : forall b q nx,
abatch_cells L m b q nx -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES -> abatch_cells L m' b q nx.
Proof.
intros b q nx (H1 & H2 & H3 & H4 & H5 & H6) D. unfold abatch_cells. cbv zeta. unfold Q_BATCH_BYTES, Q_BATCH in *.
split; [| split; [| split; [| split; [exact H4| split; [exact H5| exact H6]]]]].
- eapply cells_frame; [exact H1 | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. Local Ltac2 Set LiaHints.tbl := fun () => "0090>18148669563.1723860662149.1824501932274.1733666907028.1738177434207.1845738895041.1850532519924.1751456987883.1763361337103.1700000400;00?00C00J00N00R00Y00`S2H5S2H52HpS2H5S2H5S2H42H5S2H5S2H5S2H52H6S2H42H5".
eapply disjoint_from_sub; [exact D| lia| lia| lia].
- eapply u64arr_frame; [exact H2 | exact MU | exact WM |]. rewrite length_map, qhdrs_length by exact H5. rewrite <- H4.
eapply disjoint_from_sub; [exact D| lia| lia| lia].
- eapply junk_frame; [exact H3 | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D| lia| lia| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="MU WM"] Lemma abatches_to_frame : forall bs qs nxt,
abatches_to L m bs qs nxt -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches_to L m' bs qs nxt.
Proof.
induction bs as [|b bs IH]; intros [|q qs] nxt AB D; cbn in *; try tauto.
destruct AB as [AC AB]. split.
- eapply abatch_cells_frame; [exact AC| apply D; left; reflexivity].
- apply IH; [exact AB|]. intros q' Hq'. apply D. right. exact Hq'.
Qed.
#[using="MU WM"] Lemma abatches_frame : forall bs qs,
abatches L m bs qs -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches L m' bs qs.
Proof. intros. eapply abatches_to_frame; eassumption. Qed.
#[using="MU WM"] Lemma aqcache_frame : forall C bs qs bytes,
aqcache L m C bs qs bytes -> disjoint_from W C 32 ->
(forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> aqcache L m' C bs qs bytes.
Proof.
intros C bs qs bytes [QC AB] D DB. split.
- eapply cells_frame; [exact QC | exact MU | exact WM | exact D].
- eapply abatches_frame; [exact AB | exact DB].
Qed.
#[using="MU WM"] Lemma aintal_frame : forall ia,
aintal ia m -> disjoint_from W AIA_FLAG 4 -> disjoint_from W AIA_BASE AIA_SIZE -> aintal ia m'.
Proof.
intros ia (F & S & Z0) DF DB. unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in *. split; [| split].
- eapply cells_frame; [exact F | exact MU | exact WM | exact DF].
- eapply stk_transport_disjoint; [exact S | exact MU | exact WM |]. exact DB.
- intros Hia j Hj. eapply bytes_at_agree; [exact (Z0 Hia j Hj)|].
intros i Hi. apply MU. rewrite length_le8 in Hi. unfold AIA_MAP1, AIA_MAP1_LEN in *. cbn in Hj.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>66253720165.187104325793.18 00000700>S2Hj2HiS2Hj2Hi".
rewrite wa_unsigned by lia.
eapply disjoint_outside; [exact DB| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="MU WM"] Lemma aquar_glob_const_frame :
aquar_glob_const m -> disjoint_from W AQ_MAX 24 -> disjoint_from W AQ_MUTEX 4 -> aquar_glob_const m'.
Proof.
intros [A B] D1 D2. split.
- eapply cells_frame; [exact A | exact MU | exact WM | exact D1].
- eapply cells_frame; [exact B | exact MU | exact WM | exact D2].
Qed.
End Frames.
#[using="Type"] Lemma qcoupled_bslot_busy : forall L st X Q q,
qcoupled L st X Q -> In q (q_loc Q ++ q_glob Q) ->
exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = qb_slot q.
Proof.
intros L st X Q q (_ & _ & _ & _ & _ & BS & _) Hin. apply (proj1 (BS (qb_slot q))). apply in_map. exact Hin.
Qed.
#[using="Type"] Theorem AQUAR_frame_at : forall L st st' X X' Q m m' W,
AQUAR_at L st X Q m -> munch W m m' -> wmono bsegs m m' -> quar_untouched L X W -> quar_same st st' X X' ->
AQUAR_at L st' X' Q m'.
Proof.
intros L st st' X X' Q m m' W (GC & TC & GL & IA & CP & NUM) MU WM UT (E1 & E2 & E3 & E4 & E5 & FW & BW).
unfold AQUAR_at. rewrite E1, E2, E3, E4.
assert (DT : disjoint_from W (aq_tcache L) 32).
{ apply disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (A & _). unfold aq_tcache. cbn in A |- *. Local Ltac2 Set LiaHints.tbl := fun () => "0060>12584294218.3315132752779.2916515709918.2821144446923.2924957545227.2939149046922.3300000300600900<00?00BS1BS1AS1AS1AS1AS1A".
lia. }
assert (DG : disjoint_from W AQ_MAX 24 /\ disjoint_from W AQ_MUTEX 4 /\ disjoint_from W AQ_GCACHE 32).
{ unfold AQ_MAX, AQ_MUTEX, AQ_GCACHE, AINSTANCE in *.
repeat split; apply disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & A & _); unfold AINSTANCE in A; cbn in A |- *; lia. }
destruct DG as (DG1 & DG2 & DG3).
assert (DI1 : disjoint_from W AIA_FLAG 4 /\ disjoint_from W AIA_BASE AIA_SIZE).
{ unfold AIA_FLAG, AIA_BASE, AIA_SIZE in *.
split; apply disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & _ & A & B & _); cbn in A, B |- *; lia. }
destruct DI1 as [DF DB].
assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
{ intros q Hq. destruct (qcoupled_bslot_busy L st X Q q CP Hq) as (b & Hb & Sb & Cb & Kb).
apply disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (_ & _ & _ & _ & A).
specialize (A b Hb). rewrite Sb in A. unfold xb_alloc in A. rewrite Cb, Kb, size_of_class_24 in A.
unfold abatch_addr, Q_BATCH_BYTES. cbn. exact A. }
split; [| split; [| split; [| split; [| split]]]].
- eapply aquar_glob_const_frame; eassumption.
- eapply aqcache_frame; [exact MU | exact WM | exact TC | exact DT |]. intros q Hq. apply DQ. apply in_app_iff. left. exact Hq.
- eapply aqcache_frame; [exact MU | exact WM | exact GL | exact DG3 |]. intros q Hq. apply DQ. apply in_app_iff. right. exact Hq.
- eapply aintal_frame; eassumption.
-
destruct CP as (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN).
unfold qcoupled. cbv zeta. rewrite E1, E3.
split; [exact LN1|]. split; [exact LN2|]. split.
{ eapply Forall_impl; [| exact OK]. intros [ch k] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
destruct ch as [c n | mb ms n]; [| exact I]. destruct HOK as (b1 & ctx & Hin). exists b1, ctx.
specialize (FW _ Hin). cbn in FW. exact FW. }
split; [exact ND1|]. split; [exact ND2|]. split.
{ intros k. rewrite (BS k). split; intros (b & Hb & Sb & R); exists b; (split; [| split; [exact Sb| exact R]]).
- specialize (FW b Hb). rewrite Sb in FW. exact FW.
- specialize (BW b Hb). rewrite Sb in BW. exact BW. }
split; [| exact NN].
intros c k. rewrite (PS c k). split; intros (b & Hb & Sb & R); exists b; (split; [| split; [exact Sb| exact R]]).
+ specialize (FW b Hb). rewrite Sb in FW. exact FW.
+ specialize (BW b Hb). rewrite Sb in BW. exact BW.
- unfold qnum in *. rewrite E1, E2, E3, E4. exact NUM.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Theorem AQUAR_frame : forall L st st' X X' m m' W,
AQUAR L st X m -> munch W m m' -> wmono bsegs m m' -> quar_untouched L X W -> quar_same st st' X X' ->
AQUAR L st' X' m'.
Proof. intros L st st' X X' m m' W [Q AQ] MU WM UT QS. exists Q. exact (AQUAR_frame_at L st st' X X' Q m m' W AQ MU WM UT QS). Qed.
End CANSEC1.
