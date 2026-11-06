(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk HeapIface HeapIfaceA As0Tables ArtMem JatInitCache JatPopulate1 ArtRuns ArtRunsMem JatCls JatFp JatClsRep JatClsGfa2
JatClsRefill JatCARSpec JatAlloc3Pure JatDepotA JatDepot ArtBridge JatInv JatFxQ JatFxBatch2 JatFxBatch3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatInvFreePure () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFxQ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInvFreePure."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."], [["1Some"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1snd"; "1true"; "2and"; "2eq"]; ["2ex"; "2iff"; "2not"; "2or"; "3le"; "4map"; "5Z"; "0M"; "0M'"; "6cell"; "7art_qbatch"; "7art_qbytes"; "7art_qlist"; "8BATCH"; "8SEC"; "8art_batch"]; ["8art_batch_list"; "8art_batches_bytes"; "8art_in_batches"; "8art_nq"; "8art_sec"; "8bt_addr"; "8bt_items"; "8sc_map"; "8sc_msize"; "8sc_n"; "8sc_u"; "9art_bt_bytes"; "9art_free_newb"; "9art_lastb"; "9art_qb"; "9art_qt_add"]; ["9art_sec_quar"; ":loaded_segments"; ";In"; ";flat_map"; ";fold_right"; ";incl"; ";nth_error"; ";removelast"; "<add"; "<le"; "<lt"; "<mul"; "<of_nat"; "<pow"; "0a"; "0b"]; ["0b0"; "0b0'"; "0bn"; "0bs"; "0f"; "0h"; "0i"; "0it"; "0its"; "0j"; "0l"; "0lb"; "0lb'"; "0m"; "0qg"; "0qt"]; ["0r"; "0s"; "0s'"; "0si"; "=NoDup"; ">bv"; ">bv_unsigned"; "0x"; "0z"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_bt_bytes (b : art_batch) : Z := 8192 + fold_right (fun it z => snd it + z) 0 (bt_items b).
Definition art_qb (b : art_batch) : art_qbatch := (bt_addr b, map fst (bt_items b), art_bt_bytes b).
Lemma art_qhead_map : forall bs, art_qhead (map art_qb bs) = match bs with [] => 0 | b' :: _ => bt_addr b' end.
Proof. intros [|b r]; reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_art_batch_list_q := (ltac2:(TCodec.tc2 tcn__JatInvFreePure "N'REyR0%211':y8%511%311p051'7'O%211'F&A&Q0r4r3r2r1%544321&L&E&J&Q>%34>218%54:187%=271pTF?1pT:@1pT8B1pQ@F1")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_batch_list_q) 0%nat 0%nat).
Lemma art_batch_list_q : ltac:(sec_stmt2 constr:(SEC_T_art_batch_list_q) 1%nat 0%nat).
Proof.
intros bs.
induction bs as [|b r IH]; intros f l; cbn [art_batch_list art_qlist map]; [tauto|].
rewrite art_qhead_map. unfold art_qrec. cbn [art_qb qb_addr qb_items qb_size fst snd]. rewrite length_map. fold (art_bt_bytes b).
split.
- intros (E & Hl & C1 & C2 & CI & LK & R). split; [exact E|]. split.
{ split; [exact Hl|]. split; [exact C1|]. split; [exact C2|]. intros j it Hj. rewrite nth_error_map in Hj.
destruct (nth_error (bt_items b) j) as [it0|] eqn:Ej; cbn in Hj; [|discriminate]. injection Hj as <-. exact (CI j it0 Ej). }
destruct r as [|b' r']; cbn [map].
+ destruct LK as (El & C0). split; [exact El|]. split; [exact C0|]. apply IH. exact R.
+ split; [exact I|]. split; [exact LK|]. apply IH. exact R.
- intros (E & (Hl & C1 & C2 & CI) & LK & C0 & R). split; [exact E|]. split; [exact Hl|]. split; [exact C1|]. split; [exact C2|]. split.
{ intros j it Hj. apply (CI j (fst it)). rewrite nth_error_map, Hj. reflexivity. }
destruct r as [|b' r']; cbn [map] in *.
+ split; [split; [exact LK|exact C0]|]. apply IH. exact R.
+ split; [exact C0|]. apply IH. exact R.
Qed.
End SE.
Lemma art_batches_bytes_q : ltac2:(TCodec.tc2 tcn__JatInvFreePure "@'7'O%211'?'F&Q1r1%211&K&E&J&Q>%34;216%511%;3:71pT8=1").
Proof. induction bs as [|b r IH]; cbn [art_batches_bytes art_qbytes fold_right map]; [reflexivity|]. unfold art_batches_bytes in IH. rewrite IH. reflexivity. Qed.
Lemma art_batches_bytes_app : ltac2:(TCodec.tc2 tcn__JatInvFreePure "B'7'O%211'?'F&Q1&1r2r1%33821%511&QH%715%815%3221%<3;51pT0>1pSN?1").
Proof. intros a b. rewrite !art_batches_bytes_q, map_app. apply art_qbytes_app. Qed.
Lemma art_nq_app : ltac2:(TCodec.tc2 tcn__JatInvFreePure "B'7'O%211'?'F&Q3&1r2r1%33821%511&QH%715%815%3221%<3;51pT0>1pSN?1").
Proof. intros a b. unfold art_nq. induction a as [|x r IH]; cbn [app fold_right]; [lia|]. rewrite IH. lia. Qed.
Lemma art_nq_nonneg' : ltac2:(TCodec.tc2 tcn__JatInvFreePure ":'7'O%211&QIz&Q3r1%211%5241pT871").
Proof. induction bs as [|b r IH]; cbn [art_nq fold_right]; [lia|]. unfold art_nq in IH. lia. Qed.
Inductive art_fk : Type := FKP (c w : Z) | FKS (i : nat).
Definition art_lastb (bs : list art_batch) : art_batch := last bs (BATCH 0 []).
Definition art_free_newb (qt : list art_batch) : bool :=
art_enq_newb (Z.of_nat (length qt)) (Z.of_nat (length (bt_items (art_lastb qt)))).
Definition art_qt_add (qt : list art_batch) (b : Z) (it : Z * Z) : list art_batch :=
if art_free_newb qt then qt ++ [BATCH b [it]]
else removelast qt ++ [BATCH (bt_addr (art_lastb qt)) (bt_items (art_lastb qt) ++ [it])].
Fixpoint art_sec_quar (i : nat) (l : list art_sec) : list art_sec :=
match l, i with
| [], _ => []
| s :: r, O => SEC (sc_map s) (sc_msize s) (sc_u s) (sc_n s) true :: r
| s :: r, Datatypes.S j => s :: art_sec_quar j r
end.
Definition art_gs_free {FSG : Type} (G : art_gs FSG) (spb : Z) (k : art_fk) (u n : Z) (kb : nat) : art_gs FSG :=
let cl24 := g_cls FSG G 24 in
let newb := art_free_newb (g_qt FSG G) in
let wb := art_ca_cptr 24 cl24 in
GS FSG (g_log FSG G ++ art_enq_events newb spb cl24) (newb || g_inited FSG G)
(fun c0 => if c0 =? 24 then art_enq_cls newb cl24 else g_cls FSG G c0)
(fun c0 w0 => if newb && (c0 =? 24) && (w0 =? wb) then CBatch
else match k with FKP c w => if (c0 =? c) && (w0 =? w) then CQuar u n else g_st FSG G c0 w0 | FKS _ => g_st FSG G c0 w0 end)
(match k with FKP _ _ => g_sec FSG G | FKS i => art_sec_quar i (g_sec FSG G) end)
(g_sec_committed FSG G)
(art_qt_add (g_qt FSG G) (spb + 24 * 2 ^ 32 + 16 * wb) (u - 16, n))
(g_qg FSG G) kb true (g_fs FSG G).
Definition art_gs_drain {FSG : Type} (G : art_gs FSG) : art_gs FSG :=
GS FSG (g_log FSG G) (g_inited FSG G) (g_cls FSG G) (g_st FSG G) (g_sec FSG G) (g_sec_committed FSG G)
[] (g_qg FSG G ++ g_qt FSG G) (g_depot FSG G) (g_ia FSG G) (g_fs FSG G).
Lemma art_lastb_snoc : ltac2:(TCodec.tc2 tcn__JatInvFreePure "A'7'O%211'?&Q=&1r2(3r1(9%119%43:31%73;61%911%;3=16pT0>1pT8>1").
Proof. intros bs b. unfold art_lastb. apply last_last. Qed.
Lemma art_qt_split : ltac2:(TCodec.tc2 tcn__JatInvFreePure "F'7'O%211&B'?r1(9%116%43631%611r2&1&QG%12<3(3&Q=%116%33@1:%73A51%?3A91p0;1pU0C1").
Proof. intros qt H. unfold art_lastb. apply app_removelast_last. exact H. Qed.
Lemma art_free_newb_nil : ltac2:(TCodec.tc2 tcn__JatInvFreePure "9'?'2&Q<(9'O%211%411(=%83721").
Proof. reflexivity. Qed.
Lemma art_free_newb_false : ltac2:(TCodec.tc2 tcn__JatInvFreePure "Q2'7'O%211'?'2&Q<r1%211(4%63521'>&Br2(9%11=%<3=31%511'F&QL&6';%1244&Q6&Q=%11<%311%7251%911+oM%J3<21%C11%E2?1p0G1pU0O1").
Proof.
intros qt H. unfold art_free_newb, art_enq_newb in H. apply orb_false_iff in H. destruct H as (H1 & H2).
apply Z.eqb_neq in H1, H2. split; [|exact H2]. intros ->. apply H1. reflexivity.
Qed.
Lemma art_bt_bytes_add : ltac2:(TCodec.tc2 tcn__JatInvFreePure "M'F'7';%1233%311'?&Q;(Mr3&1r2(3r1(9%11;%43<31%73=61%:291%<11&QH%=2<:%?11&<%13GG;%5231%D3I71pT@G1pTBG1pSNL1").
Proof. intros a its it. unfold art_bt_bytes. cbn [bt_items]. induction its as [|x r IH]; cbn [app fold_right]; lia. Qed.
Lemma art_batches_bytes_one : ltac2:(TCodec.tc2 tcn__JatInvFreePure ">'O'?'F&Q1(3r1(9%117%43831%611&Q;%116%;3:31pT0=1").
Proof. intros b. unfold art_batches_bytes, art_bt_bytes. cbn [fold_right]. lia. Qed.
Lemma art_qt_add_bytes : forall qt b it,
art_batches_bytes (art_qt_add qt b it) = art_batches_bytes qt + snd it + (if art_free_newb qt then 8192 else 0).
Proof.
intros qt b it. unfold art_qt_add. destruct (art_free_newb qt) eqn:E.
- rewrite art_batches_bytes_app, art_batches_bytes_one. unfold art_bt_bytes. cbn [bt_items fold_right]. lia.
- destruct (art_free_newb_false qt E) as (NE & _). destruct (exists_last NE) as (r & lb & ->). rewrite removelast_last, art_lastb_snoc.
rewrite !art_batches_bytes_app, !art_batches_bytes_one. rewrite art_bt_bytes_add. unfold art_bt_bytes. cbn [bt_items]. lia.
Qed.
Lemma art_qt_add_nq : forall qt b it, art_nq (art_qt_add qt b it) = art_nq qt + 1 + (if art_free_newb qt then 1 else 0).
Proof.
intros qt b it. unfold art_qt_add. destruct (art_free_newb qt) eqn:E.
- rewrite art_nq_app. cbn [art_nq fold_right bt_items length]. lia.
- destruct (art_free_newb_false qt E) as (NE & _). destruct (exists_last NE) as (r & lb & ->). rewrite removelast_last, art_lastb_snoc. rewrite !art_nq_app.
cbn [art_nq fold_right bt_items]. rewrite length_app. cbn [length]. lia.
Qed.
Lemma art_qt_add_length : forall qt b it, Z.of_nat (length (art_qt_add qt b it)) = Z.of_nat (length qt) + (if art_free_newb qt then 1 else 0).
Proof.
intros qt b it. unfold art_qt_add. destruct (art_free_newb qt) eqn:E.
- rewrite length_app. cbn [length]. lia.
- destruct (art_free_newb_false qt E) as (NE & _). destruct (exists_last NE) as (r & lb & ->). rewrite removelast_last. rewrite !length_app. cbn [length]. lia.
Qed.
Section Open.
Variable FSG : Type.
Definition art_rt_quar_b (bound : Z) (rn : art_run) (G : art_gs FSG) (M : word -> option byte) : Prop :=
(exists f l, cellA M (rn_t rn + 80) 8 (Z.of_nat (length (g_qt FSG G))) /\ cellA M (rn_t rn + 88) 8 f /\ cellA M (rn_t rn + 96) 8 l
/\ cellA M (rn_t rn + 104) 8 (art_batches_bytes (g_qt FSG G)) /\ art_batch_list M (g_qt FSG G) f l)
/\ (exists f l, cellA M (0x137970 + 160) 8 (Z.of_nat (length (g_qg FSG G))) /\ cellA M (0x137970 + 168) 8 f /\ cellA M (0x137970 + 176) 8 l
/\ cellA M (0x137970 + 184) 8 (art_batches_bytes (g_qg FSG G)) /\ art_batch_list M (g_qg FSG G) f l)
/\ art_batches_bytes (g_qt FSG G) <= bound /\ art_batches_bytes (g_qg FSG G) <= 2 ^ 28
/\ cellA M (0x137970 + 152) 4 0
/\ NoDup (map bt_addr (g_qt FSG G ++ g_qg FSG G))
/\ (forall b, In b (g_qt FSG G ++ g_qg FSG G) -> bt_items b <> [])
/\ (forall b it, In b (g_qt FSG G ++ g_qg FSG G) -> In it (bt_items b) ->
(exists c w, 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w /\ g_st FSG G c w = CQuar (fst it + 16) (snd it))
\/ (exists s, In s (g_sec FSG G) /\ sc_quar s = true /\ sc_u s = fst it + 16 /\ sc_n s = snd it))
/\ NoDup (map fst (flat_map bt_items (g_qt FSG G ++ g_qg FSG G)))
/\ (forall b, In b (g_qt FSG G ++ g_qg FSG G) ->
exists w, bt_addr b = rn_spb rn + 24 * 2 ^ 32 + 16 * w /\ art_cptr_ok (AsanTab.class_size 24) (cl_au (g_cls FSG G 24)) w /\ g_st FSG G 24 w = CBatch).
Definition art_alloc_rep_b (bound : Z) (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M : word -> option byte) : Prop :=
art_run_ok rn /\ art_rt_statics rn M /\ art_rt_thread rn M /\ art_rt_primary FSG rn G M /\ art_rt_chunks FSG rn G LB M
/\ art_rt_sec FSG rn G LB M /\ art_rt_quar_b bound rn G M /\ art_rt_depot FSG rn G M /\ art_rt_ia FSG G M /\ art_rt_blocks FSG rn G LB
/\ art_rt_ghost FSG rn G M.
#[using="Type"] Lemma art_alloc_rep_b_closed : forall rn G LB M, art_alloc_rep_b (2 ^ 20) rn G LB M = art_alloc_rep FSG rn G LB M.
Proof. reflexivity. Qed.
#[using="Type"] Lemma art_alloc_rep_b_ghost : forall b rn G LB M, art_alloc_rep_b b rn G LB M -> art_rt_ghost FSG rn G M.
Proof. intros b rn G LB M (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GH). exact GH. Qed.
#[using="Type"] Lemma art_alloc_rep_b_mono : forall b b' rn G LB M, b <= b' -> art_alloc_rep_b b rn G LB M -> art_alloc_rep_b b' rn G LB M.
Proof.
intros b b' rn G LB M Hb (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7). split; [exact R0|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|].
split; [|exact R7]. destruct R6 as (Q1 & Q2 & Q3 & Q4). split; [exact Q1|]. split; [exact Q2|]. split; [lia|exact Q4].
Qed.
End Open.
Lemma art_qt_add_flat : ltac2:(TCodec.tc2 tcn__JatInvFreePure "K'7'O%211'F';%1222'?%712&QC&Q6&Q?r3r2r1%43321%74>:61&1%94@<86(3(9%11?%33@81%63A51%A3@81pT@C1pT0F1pU0H1").
Proof.
intros qt b it. unfold art_qt_add. destruct (art_free_newb qt) eqn:E.
- rewrite flat_map_app. cbn [flat_map bt_items app]. rewrite ?app_nil_r. reflexivity.
- destruct (art_free_newb_false qt E) as (NE & _). destruct (exists_last NE) as (r & lb & ->). rewrite removelast_last, art_lastb_snoc.
rewrite !flat_map_app. cbn [flat_map bt_items]. rewrite ?app_nil_r. rewrite app_assoc. reflexivity.
Qed.
Lemma art_qt_add_addrs : forall qt b it, map bt_addr (art_qt_add qt b it) = map bt_addr qt ++ (if art_free_newb qt then [b] else []).
Proof.
intros qt b it. unfold art_qt_add. destruct (art_free_newb qt) eqn:E.
- rewrite map_app. reflexivity.
- destruct (art_free_newb_false qt E) as (NE & _). destruct (exists_last NE) as (r & lb & ->). rewrite removelast_last, art_lastb_snoc.
rewrite !map_app. cbn [map bt_addr]. rewrite app_nil_r. reflexivity.
Qed.
Lemma art_qt_add_in : ltac2:(TCodec.tc2 tcn__JatInvFreePure "QI'7'O%211'F';%1222&QBr1&Q?r4r3r2%43321%73<61'C'>'?'2&Q<r5%211(=%63521(M(3(9%11E%33FA1%52C1%=3LB1%?281%I3ND<(4%A3@=1&B%:1Q2%D3Q2A1%311&Q5&Q=%11E%311&1&Q6%114%33Q81B%G251%O3Q>Q41%Q12;1%Q22@1%Q42C1%Q52E1p0Q71pT2QD1pT@QA1pT0QD1pU0QF1").
Proof.
intros qt b it b0 H. unfold art_qt_add in H. destruct (art_free_newb qt) eqn:E.
- apply in_app_or in H. destruct H as [H|[H|[]]]; [right; left; exact H|left; split; [reflexivity|symmetry; exact H]].
- destruct (art_free_newb_false qt E) as (NE & _). apply in_app_or in H. destruct H as [H|[H|[]]].
+ right; left. rewrite (art_qt_split qt NE). apply in_or_app. left. exact H.
+ right; right. split; [reflexivity|]. split; [exact NE|symmetry; exact H].
Qed.
Lemma art_qt_add_keep : ltac2:(TCodec.tc2 tcn__JatInvFreePure "Q5'7'O%211'F';%1222&QBr1r4%33821'@'>&Q?r6r5%33217%:3?91'?&Q5%11<r3%311%53C31&QE&Q6%115%21C%43F21%A261%B2=1qT4M1%E2N1p0G1pT2Q01pT@M1pT0Q01pU0Q21").
Proof.
intros qt b it b0 H. unfold art_qt_add. destruct (art_free_newb qt) eqn:E.
- exists b0. split; [apply in_or_app; left; exact H|]. split; [reflexivity|apply incl_refl].
- destruct (art_free_newb_false qt E) as (NE & _). rewrite (art_qt_split qt NE) in H. apply in_app_or in H. destruct H as [H|[H|[]]].
+ exists b0. split; [apply in_or_app; left; exact H|]. split; [reflexivity|apply incl_refl].
+ subst b0. eexists. split; [apply in_or_app; right; left; reflexivity|]. cbn [bt_addr bt_items]. split; [reflexivity|apply incl_appl, incl_refl].
Qed.
Lemma art_in_batches_add : ltac2:(TCodec.tc2 tcn__JatInvFreePure "L'7'O%211'F';%1222&Q2&1r6r5%33921r2r1%73321&Q?r7r4%33281%;3A1:r3%>3219p081pTLC1pT<D1pT@C1pT0F1pTNH1pU0I1").
Proof.
intros qt qg b it h m (b0 & Hb0 & Hi). apply in_app_or in Hb0. destruct Hb0 as [Hb0|Hb0].
- destruct (art_qt_add_keep qt b it b0 Hb0) as (b0' & H1 & _ & H3). exists b0'. split; [apply in_or_app; left; exact H1|apply H3; exact Hi].
- exists b0. split; [apply in_or_app; right; exact Hb0|exact Hi].
Qed.
Lemma art_in_batches_new : ltac2:(TCodec.tc2 tcn__JatInvFreePure "H'7'O%211'F';%1222&Q2&1&Q?r4r2r1%43321r3%73=21&5%13==5&<%13??7%=3531pT@?1pT0B1pTND1pU0E1").
Proof.
intros qt qg b it. unfold art_in_batches, art_qt_add. destruct (art_free_newb qt) eqn:E.
- exists (BATCH b [it]). split; [apply in_or_app; left; apply in_or_app; right; left; reflexivity|]. cbn [bt_items]. left. destruct it; reflexivity.
- eexists. split; [apply in_or_app; left; apply in_or_app; right; left; reflexivity|]. cbn [bt_items]. apply in_or_app. right. left. destruct it; reflexivity.
Qed.
Lemma art_batch_list_last : ltac2:(TCodec.tc2 tcn__JatInvFreePure "Q3'REyR0%211':y8%511%311p051'7'O%211'F&B'?r3(9%117%43731%611&Q0r5r4r2%443291&Q5&Q=%116%311%?3A>1p061p0<1pTFD1pT:E1pT8G1pQ@K1").
Proof.
intros M bs. induction bs as [|x r IH]; intros f l NE BL; [contradiction|]. cbn [art_batch_list] in BL. destruct BL as (_ & _ & _ & _ & _ & LK & R).
destruct r as [|y r']; [destruct LK as (El & _); exact El|]. unfold art_lastb. change (last (x :: y :: r') (BATCH 0 [])) with (last (y :: r') (BATCH 0 [])).
apply (IH (bt_addr y) l); [discriminate|exact R].
Qed.
Lemma art_nth_error_lt : forall (A : Type) (l : list A) j x, nth_error l j = Some x -> (j < length l)%nat.
Proof. intros A l j x H. apply nth_error_Some. rewrite H. discriminate. Qed.
Section SE.
Local Abbreviation SEC_T_art_batch_list_snoc := (ltac2:(TCodec.tc2 tcn__JatInvFreePure "S='REyR0%211':y8%511%311p051pU@62'7'O%211'F&B'?r4(9%117%43731%611'RD&E&Q5r5%34><21%52=1&Q0r8r6%34216>&QBr1%23F15'>&QIzr2%?11%4231&QJ&QH+XP0%2251&QM+2+R0%3221%8251%?2:1p0A1pT2Q81r:%F3Q:@1r3%Q011&RF%12QGD%G231%B24A%D231%K231%Q71Q>%Q@3QB1;%82QN:+8%I2>1%K231%Q2251%QG11r>%11QGr?%11QI%QK3R331p061p0?1p0H1pU@R;1pT2R41&I&QAr7u8%QM1QG%554Q1321r;(3%13R=6R6%R217%QO44211r<&1%63RBR1R;%23RC81%R81R3%R5452Q<1p071p0=1p0D1p0QA1p0R71p0R<1p0RC1pT6RM1pTFRL1pT:RM1pT8RO1pQBS31pQ@S51")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_batch_list_snoc) 0%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SEC_T_art_batch_list_snoc) 1%nat 0%nat).
Lemma art_batch_list_snoc : ltac:(sec_stmt2 constr:(SEC_T_art_batch_list_snoc) 2%nat 0%nat).
Proof.
intros bs.
induction bs as [|x r IH]; intros f l bn NE ND BL RNG EQ CL BN; [contradiction|].
cbn [art_batch_list] in BL. destruct BL as (Ef & Hl & C1 & C2 & CI & LK & R).
destruct (RNG x (or_introl eq_refl)) as (R0 & R1).
assert (TX : forall a (j : nat) v, bt_addr x + 8 <= a -> a + Z.of_nat j <= bt_addr x + 8192 -> cellA M a j v -> cellA M' a j v).
{ intros a j v Ha Hj C. apply (art_cell_agree _ M M'); [|lia|lia|exact C]. intros y Hy. apply (EQ x y (or_introl eq_refl)); [lia|]. intros (E & Y). lia. }
assert (TI : forall j it, nth_error (bt_items x) j = Some it -> cellA M' (bt_addr x + 24 + 8 * Z.of_nat j) 8 (fst it)).
{ intros j it Hj. pose proof (art_nth_error_lt _ _ _ _ Hj) as Hlt. apply TX; [lia|cbn; lia|exact (CI j it Hj)]. }
destruct r as [|y r'].
- destruct LK as (El & C0). cbn [app art_batch_list]. split; [exact Ef|]. split; [exact Hl|]. split; [apply TX; [lia|cbn; lia|exact C1]|]. split; [apply TX; [lia|cbn; lia|exact C2]|].
split; [exact TI|]. split; [rewrite <- El; exact CL|]. exact BN.
- assert (El : l = bt_addr (art_lastb (y :: r'))) by (apply (art_batch_list_last M (y :: r') (bt_addr y) l); [discriminate|exact R]).
assert (Nx : bt_addr x <> l).
{ rewrite El. intros E. cbn [map] in ND. inversion ND as [|a0 l0 Hni HND]; subst a0 l0. apply Hni. apply list_elem_of_In. rewrite E. change (bt_addr y :: map bt_addr r') with (map bt_addr (y :: r')). apply in_map. unfold art_lastb. apply JatFxQ.art_last_in. discriminate. }
change ((x :: y :: r') ++ [bn]) with (x :: y :: (r' ++ [bn])). cbn [art_batch_list]. split; [exact Ef|]. split; [exact Hl|]. split; [apply TX; [lia|cbn; lia|exact C1]|].
split; [apply TX; [lia|cbn; lia|exact C2]|]. split; [exact TI|].
split. { apply (art_cell_agree _ M M'); [|lia|cbn; lia|exact LK]. intros z Hz. apply (EQ x z (or_introl eq_refl)); [cbn in Hz; lia|]. intros (E & _). exact (Nx E). }
change (y :: (r' ++ [bn])) with ((y :: r') ++ [bn]). apply (IH (bt_addr y) l bn); [discriminate| | exact R | | | exact CL | exact BN].
+ cbn [map] in ND. inversion ND as [|a0 l0 Hni HND]; subst a0 l0. exact HND.
+ intros b0 Hb0. apply RNG. right. exact Hb0.
+ intros b0 z Hb0. apply EQ. right. exact Hb0.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_batch_list_upd_last := (ltac2:(TCodec.tc2 tcn__JatInvFreePure "U0'REyR0%211':y8%511%311p051pU@62'7'O%211'F&Q0r7&1r5(3r4(9%11:%43;31%73<61r2r1%<4;321'?&Q5%11:%21=%43B21&QBr8%@3GC=%C3H21%43I;1'>&QIz%<1@%3221&QJ&QH+XP0%2251&QM+2+R0%3221%8251%>2:1p0@1pT2Q:1r:%G3Q<O1r3%M11&RF%12QIQ3%F231%B24A%D231%J231r=%119r>%11;%Q93QM31p061p0?1pU@R41pT2QM1r9%Q>11%A2R9QB%Q6221+8%Q3241%Q5241%Q;241r<%11QJ%C1QK%QI3R=21p051pU@RC1'D&6';%12R=R=&Q6%11QK%5231uoM%8221&I&QA+@%QH2I1u8&QL%;1M%?2=1%311%958H651%R>1QD%R021N&QD&<%13S1S1RF%R421RFqUBS31qT@G1%G1QL%75S6I2R<1%R92R81%E5DQE:A1'8%SC1M&QF%N1QI%23Q01S2(0%12Q2S3%S23631rA%S31QM+H%RF221&QK%N1R;%22QG1%RJ241&5%13SJSJS?%Q85Q7:3Q41p0<1pT@Q@1pTDE1r?%SK3T2QLSH%SN3T3R<1r;%T24421RJp061p0M1p0Q:1p0QE1p0QO1p0R>1p0S21p0SI1p0SO1pTFT=1pT:T>1pTJTA1pTHTB1pU2TB1pQBTF1pQ@TH1")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_batch_list_upd_last) 0%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SEC_T_art_batch_list_upd_last) 1%nat 0%nat).
Lemma art_batch_list_upd_last : ltac:(sec_stmt2 constr:(SEC_T_art_batch_list_upd_last) 2%nat 0%nat).
Proof.
intros r.
induction r as [|x r IH]; intros lb lb' f l BL Ea RNG EQ EQL Hl' C1' C2' CI'.
- cbn [app art_batch_list] in BL |- *. destruct BL as (Ef & _ & _ & _ & _ & (El & C0) & _). destruct (RNG lb (or_introl eq_refl)) as (R0 & R1).
split; [rewrite Ea; exact Ef|]. split; [exact Hl'|]. split; [exact C1'|]. split; [exact C2'|]. split; [exact CI'|].
split; [|reflexivity]. split; [rewrite Ea; exact El|]. rewrite Ea. apply (art_cell_agree _ M M'); [|lia|cbn; lia|exact C0]. intros z Hz. apply EQL. cbn in Hz. lia.
- change ((x :: r) ++ [lb]) with (x :: (r ++ [lb])) in BL. change ((x :: r) ++ [lb']) with (x :: (r ++ [lb'])).
cbn [art_batch_list] in BL |- *. destruct BL as (Ef & Hl & C1 & C2 & CI & LK & R).
destruct (RNG x (or_introl eq_refl)) as (R0 & R1).
assert (TX : forall a (j : nat) v, bt_addr x <= a -> a + Z.of_nat j <= bt_addr x + 8192 -> cellA M a j v -> cellA M' a j v).
{ intros a j v Ha Hj C. apply (art_cell_agree _ M M'); [|lia|lia|exact C]. intros y Hy. apply (EQ x y (or_introl eq_refl)). lia. }
split; [exact Ef|]. split; [exact Hl|]. split; [apply TX; [lia|cbn; lia|exact C1]|]. split; [apply TX; [lia|cbn; lia|exact C2]|].
split. { intros j it Hj. pose proof (art_nth_error_lt _ _ _ _ Hj) as Hlt. apply TX; [lia|cbn; lia|exact (CI j it Hj)]. }
assert (Hd : match r ++ [lb'] with [] => 0 | b' :: _ => bt_addr b' end = match r ++ [lb] with [] => 0 | b' :: _ => bt_addr b' end).
{ destruct r as [|y r']; cbn [app]; [exact Ea|reflexivity]. }
split.
{ destruct (r ++ [lb]) as [|y0 t0] eqn:E0; [destruct r; discriminate|]. destruct (r ++ [lb']) as [|y1 t1] eqn:E1; [destruct r; discriminate|].
cbn in Hd. rewrite Hd. apply TX; [lia|cbn; lia|exact LK]. }
rewrite Hd. apply (IH lb lb' _ l R Ea); [intros b0 Hb0; apply RNG; right; exact Hb0|intros b0 z Hb0; apply EQ; right; exact Hb0|exact EQL|exact Hl'|exact C1'|exact C2'|exact CI'].
Qed.
End SE.
Lemma art_sec_quar_length : ltac2:(TCodec.tc2 tcn__JatInvFreePure "?'8'7'Q4%211'?&6&Q@r2r1%3221%5281%6293%83<21pTF:1pT>>1").
Proof. induction i as [|i IH]; intros [|s r]; cbn [art_sec_quar length]; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma art_sec_quar_nth_same : ltac2:(TCodec.tc2 tcn__JatInvFreePure "Q4'8'7'Q4%211'?':%114&QFr2r3%33821(0r1%22;1%:3841&Q@r4%2218%;3@12(N&Q7%11=&Q8%11?&Q:%11A&Q9%11C(=%:586421%C2L1%K3I=1p0B1pU4O1pTFO1pT>Q31").
Proof. induction i as [|i IH]; intros [|s0 r] s H; cbn [nth_error art_sec_quar] in *; try discriminate. - injection H as ->. reflexivity. - apply IH. exact H. Qed.
Lemma art_sec_quar_nth_other : ltac2:(TCodec.tc2 tcn__JatInvFreePure "H'8'7'Q4%211&B'?r1r3%33821%511':%119&QF&Q@r4%2218r2%53?21%63@;2%>3821p0;1pTDE1pTFC1pT>G1").
Proof.
induction i as [|i IH]; intros [|s0 r] j N; cbn [art_sec_quar]; try reflexivity.
- destruct j as [|j]; [contradiction|reflexivity].
- destruct j as [|j]; [reflexivity|]. cbn [nth_error]. apply IH. intros ->. apply N. reflexivity.
Qed.
Lemma art_sec_quar_in_other : ltac2:(TCodec.tc2 tcn__JatInvFreePure "Q4'8'7'Q4%211'?':%114&QFr3r4%33821(0r2%22;1%:3841&QB%13>47&B'F&Q:%11<%21<%B3421%611&Q@r7r6%3221%=3JC1p061p0>1p0A1pU4N1pU8O1pTFO1pT>Q31").
Proof.
induction i as [|i IH]; intros [|s0 r] si s H Hs N; cbn [nth_error art_sec_quar] in *; try discriminate.
- injection H as ->. destruct Hs as [->|Hs]; [contradiction|right; exact Hs].
- destruct Hs as [->|Hs]; [left; reflexivity|right; exact (IH r si s H Hs N)].
Qed.
Lemma art_sec_quar_in : ltac2:(TCodec.tc2 tcn__JatInvFreePure "Q='8'7'Q4%211&QBr1&Q@r3r2%3221%63851'C%83:45'@'>'?':%11?&QFr4r5%33C21(0%12EB%93731(N&Q7%11F&Q8%11H&Q:%11J&Q9%11L(=%:586421%E3Q2M1%G2=1qU4Q41%J2Q51%M2L1p0O1pU6Q81pTFQ81pT>Q<1").
Proof.
induction i as [|i IH]; intros [|s0 r] s' H; cbn [art_sec_quar] in H; try contradiction.
- destruct H as [<-|H]; [right; exists s0; split; reflexivity|left; right; exact H].
- destruct H as [<-|H]; [left; left; reflexivity|]. destruct (IH r s' H) as [X|(s & X1 & X2)]; [left; right; exact X|right; exists s; split; assumption].
Qed.
