(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem JatPoison JatInitCache JatPopulate1 ArtRuns JatCls JatFp JatClsRep JatSecAllocPost
JatRecycle2C JatRecycle3L JatRecycle4P JatRecycle4S JatRecycle5A JatRecycle5I JatRecycle5G.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatRecycle5T () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5G."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5I."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5T.Tr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1cons"; "1fst"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2iff"; "2or"; "3Forall"; "4Z"]; ["0G"; "0HI"; "0M"; "0M'"; "0M1"; "0M2"; "5cell"; "5wr"; "6aev"; "7cl_au"; "8art_agree"; "9art_rel"; "9art_rel_step"; "9art_rel_steps"; "9art_rel_zone"; "9art_rg"]; ["9rg_bl"; "9rg_cls"; ":art_bl_geo"; ":art_rel_geo"; ";art_rcy_inv"; ";art_rcy_prot"; ";art_rel_fp"; ";art_rel_mem"; ";art_rel_pre"; "<art_rcy_tr"; "<art_rcy_trx"; "<art_rel_pzone"; "<art_rel_static"; "<art_rels_events"; "<art_rels_fp"; "<art_rels_pre"]; ["<art_rels_sep"; "<art_zapart"; "<art_zsep"; "=mem_grows"; ">loaded_segments"; "?In"; "@add"; "@le"; "@lt"; "@of_nat"; "@pow"; "@sub"; "0a"; "0c"; "0ctx"; "0e"]; ["0e'"; "0es"; "0es'"; "0es1"; "0es2"; "0hi"; "0k"; "0key"; "0l1"; "0l2"; "0n"; "0nt"; "0parr"; "0qs"; "0ris"; "0sp1"]; ["0spb"; "Abv"; "0t"; "0tp"; "0tsd"; "0v"; "0x"; "0zlen"; "0zlo"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section Tr.
Variables (HI t ctx tp key tsd spb ris qs parr : Z).
Hypothesis GEO : art_geo HI t ctx tp tsd spb ris qs.
Fixpoint art_rels_pre (G : art_rg) (es : list art_rel) : Prop :=
match es with [] => True | e :: r => art_rel_pre G e /\ art_rels_pre (art_rel_step e G) r end.
Fixpoint art_rels_fp (sp1 : Z) (G : art_rg) (es : list art_rel) : list (Z * Z) :=
match es with [] => [] | e :: r => art_rel_fp t spb ris parr sp1 G e ++ art_rels_fp sp1 (art_rel_step e G) r end.
Definition art_rels_events (es : list art_rel) : list aev := flat_map art_rel_events es.
Definition art_zapart (e : art_rel) (zlo zlen : Z) : Prop := apart (fst (art_rel_zone spb e)) (snd (art_rel_zone spb e)) zlo zlen.
Fixpoint art_rels_sep (es : list art_rel) : Prop :=
match es with [] => True | e :: r => Forall (fun e' => art_zapart e (fst (art_rel_zone spb e')) (snd (art_rel_zone spb e'))) r /\ art_rels_sep r end.
#[using="Type"] Lemma art_rel_steps_app : ltac2:(TCodec.tc2 tcn__JatRecycle5T "B'3'K%211'O';&M&0r3r2%33821r1%6221%7252%8251%:3;31pQ2<1pT:>1pT8?1").
Proof. intros. unfold art_rel_steps. apply fold_left_app. Qed.
#[using="Type"] Lemma art_rels_fp_app : ltac2:(TCodec.tc2 tcn__JatRecycle5T "K'?'3'K%211'O';'8%1277%711&Q>r4r1&0r3r2%33=21%73651%83764&M%1268%;3:16%93>41%A3>61pQ2C1pT:E1pT8F1pU0J1").
Proof. intros sp1 es1. induction es1 as [|e r IH]; intros es2 G; cbn [app art_rels_fp art_rel_steps fold_left]; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.
#[using="Type"] Lemma art_rels_events_app : ltac2:(TCodec.tc2 tcn__JatRecycle5T "B'3'K%211';'H%511&Q=&0r2r1%33921%511%614%714%73:21%<3:41pT:>1pT8?1").
Proof. intros. unfold art_rels_events. apply flat_map_app. Qed.
#[using="Type"] Lemma art_rels_pre_app : ltac2:(TCodec.tc2 tcn__JatRecycle5T "F'3'K%211'O&<&Q?r1&0r3r2%33921%6251':%8275&M%1279%;217%5241%>271pQ2@1pT:B1pT8C1").
Proof. induction es1 as [|e r IH]; intros es2 G; cbn [app art_rels_pre art_rel_steps fold_left]; [tauto|]. rewrite IH. unfold art_rel_steps. tauto. Qed.
Definition art_rel_static (G : art_rg) (e : art_rel) : Prop :=
match e with
| REP c w d b1 n => 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (rg_cls G c)) w
/\ 0 <= d /\ d mod 16 = 0 /\ d + 16 + (n + 7) / 8 * 8 <= AsanTab.class_size c /\ 0 <= b1 < 256 /\ 0 <= n < 2 ^ 32
| RES mb ms m b1 n => In (mb, ms) (rg_bl G) /\ mb + 4096 <= m /\ m + 16 <= mb + ms /\ 0 <= b1 < 256 /\ 0 <= n < 2 ^ 32
| REB wb => art_cptr_ok 8192 (cl_au (rg_cls G 24)) wb
end.
#[using="Type"] Lemma art_rel_pre_static : ltac2:(TCodec.tc2 tcn__JatRecycle5T "<'O'K&Q8r2r1%3221&Q<r3%2215p041pT091pQ2;1").
Proof. intros G [c w d b1 n|mb ms m b1 n|wb]; cbn; tauto. Qed.
#[using="Type"] Lemma art_rel_step_au : ltac2:(TCodec.tc2 tcn__JatRecycle5T "C'K'O'?';&I&Q1&Lr3r2%3221r1%6221%811%8253%:11%<3=31pSL>1pQ2@1pT0B1").
Proof.
intros [c0 w d b1 n|mb ms m b1 n|wb] G c; cbn [art_rel_step rg_cls]; [|reflexivity|].
- unfold art_cls_upd. destruct (c =? c0) eqn:E; [|reflexivity]. apply Z.eqb_eq in E. subst. apply art_cls_dealloc_au.
- unfold art_cls_upd. destruct (c =? 24) eqn:E; [|reflexivity]. apply Z.eqb_eq in E. subst. apply art_cls_dealloc_au.
Qed.
#[using="Type"] Lemma art_rel_steps_au : ltac2:(TCodec.tc2 tcn__JatRecycle5T "E'3'K%211'O'?';&I&Q1&Mr3r2%3221r1%6221%811%8253%:11%<3=31pSL>1pQ2@1pT4B1").
Proof. induction es as [|e r IH]; intros G c; cbn [art_rel_steps fold_left]; [reflexivity|]. unfold art_rel_steps in IH. rewrite IH. apply art_rel_step_au. Qed.
#[using="Type"] Lemma art_rel_step_bl_in : ltac2:(TCodec.tc2 tcn__JatRecycle5T "D'K'O'8'?%2211&QEr1&Q0&Lr3r2%3221%511%83971%715%:3;51p031pU>=1pQ2A1pT0C1").
Proof. intros [c0 w d b1 n|mb ms m b1 n|wb] G x; cbn [art_rel_step rg_bl]; [tauto| |tauto]. apply art_swap_remove_in. Qed.
#[using="Type"] Lemma art_rel_static_back : ltac2:(TCodec.tc2 tcn__JatRecycle5T ">'K'O&Q<&Lr3r2%3221r1%6221%7254p021pT2;1pQ2;1pT0=1").
Proof.
intros e G [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_static]; rewrite ?art_rel_step_au; [tauto| |tauto].
intros (H1 & H2). split; [eapply art_rel_step_bl_in; exact H1|exact H2].
Qed.
#[using="Type"] Lemma art_rels_pre_static : ltac2:(TCodec.tc2 tcn__JatRecycle5T "@'3'K%211'O&Q?r1r2%3221'>&Q<%114r3%43;21p061pQ2;1pT4=1").
Proof.
induction es as [|e r IH]; intros G H; [constructor|]. destruct H as [H1 H2]. constructor; [apply art_rel_pre_static; exact H1|].
eapply Forall_impl; [|exact (IH _ H2)]. intros e'. apply art_rel_static_back.
Qed.
Definition art_rel_pzone (e : art_rel) : Z * Z :=
match e with REP c w _ _ _ => (spb + c * 2 ^ 32 + 16 * w, AsanTab.class_size c) | RES _ _ m _ _ => (m, 8) | REB wb => (spb + 24 * 2 ^ 32 + 16 * wb, 8192) end.
Section SE.
Local Abbreviation SEC_T_art_rel_static_prot := (ltac2:(TCodec.tc2 tcn__JatRecycle5T "R5'?'O'RAyR0%211'6y8%511%311p051'K&Q4vAvRBvQNvRCvR7vRDvR@vR>vR=vR<r4r3r2%>==<;:987654321&Q<%1253':&Q5r5&2&Q;%11:%33Q2Q21&9%13Q4Q43%84C731&QHz%2214&QAr1%23=C1r6%431FEp031pU@Q?1pUBQ@1&QG&N%12Q1L%E3QDQD1%421C&QF%12EC%E3QHQH5%3251%9231%O261%Q02<1%Q12E1%Q22I1p0Q41p0Q71pT0QG1pQ6QI1pQ2R21pTHR41")) (only parsing).
Variable nt : ltac:(sec_ty2 constr:(SEC_T_art_rel_static_prot) 0%nat 0%nat).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_rel_static_prot) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_rel_static_prot) 2%nat 0%nat).
Lemma art_rel_static_prot : ltac:(sec_stmt2 constr:(SEC_T_art_rel_static_prot) 3%nat 0%nat).
Proof using Type nt G M.
intros e (ICLS & _) ST.
destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_static art_rel_pzone art_rel_zone fst snd] in *.
- destruct ST as (Hc & (Hw0 & Hwsz & _) & _). destruct (ICLS c Hc) as (_ & OK & _). destruct OK as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _).
pose proof (art_class_size_facts c Hc) as (Hsz & _).
split; [left; exists c; split; [exact Hc|lia]|]. split; [lia|]. split; [tauto|]. lia.
- destruct ST as (Hin & H1 & H2 & _). split; [right; exists (mb, ms); cbn [fst snd]; split; [exact Hin|lia]|]. split; [lia|]. split; [tauto|]. lia.
- destruct ST as (Hw0 & Hwsz & _). destruct (ICLS 24 ltac:(lia)) as (_ & OK & _). destruct OK as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _).
split; [left; exists 24; split; [lia|lia]|]. split; [lia|]. split; [tauto|]. lia.
Qed.
End SE.
#[using="Type"] Lemma art_rel_mem_tr : ltac2:(TCodec.tc2 tcn__JatRecycle5T "QI'O'K'RAyR0%211'6y8%511%311p051&Q<r4r3%3221'?'4&QG&2&Q;r7%211%43771%621:&QF&QI%11=%32?1r8%:11%<3??1&9%13AA3%9231%A271&F&QDr5%352:1JIr6%554<13Lp031p081p0D1pU<M1pT>M1pSJO1&Q7vR@%231<Q5%332;Q6p021p061p0Q71pQ8Q<1pQ6Q=1pT0QF1pQ2QH1").
Proof.
intros G e M M' ST T MEM. destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_static art_rel_pzone art_rel_mem fst snd] in *; [| |exact I].
- destruct ST as (Hc & _ & Hd & _ & Hdsz & _ & Hn). destruct MEM as (C1 & C2 & C3).
assert (Hrs : 0 <= (n + 7) / 8 * 8). { pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as B. lia. }
split; [apply T; [lia|cbn; lia|exact C1]|]. split; [apply T; [lia|cbn; lia|exact C2]|]. intros NE. apply T; [lia|cbn; lia|exact (C3 NE)].
- destruct MEM as (C1 & C2). split; [apply T; [lia|cbn; lia|exact C1]|apply T; [lia|cbn; lia|exact C2]].
Qed.
#[using="Type"] Lemma art_rcy_prot_step : ltac2:(TCodec.tc2 tcn__JatRecycle5T "Q6'O'K'?&Q2vAvRBvQNvR@vR<r4%76654321&Q3r5%2214&QHzr3%3221&Q5r7%24=18;&QAr6%2341;&Lr8r9%3221%:4E196p061p0:1p0>1p0C1p0G1pU@Q01pUBQ11pT0Q31pQ2Q51").
Proof.
intros G e zlo zlen (ISG & _) RG Hz PROT AP. destruct PROT as [K|(b & Hb & Z1 & Z2)]; [left; exact K|]. right. exists b. split; [|split; assumption].
destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_step rg_bl]; [exact Hb| |exact Hb].
cbn [art_rel_geo] in RG. pose proof (art_bl_idx_nth (rg_bl G) mb ms RG (art_sec_geo_inj HI t ctx parr (rg_bl G) ISG)) as Hnth.
apply art_swap_remove_keeps; [apply nth_error_Some; rewrite Hnth; discriminate|exact Hb|].
rewrite (nth_error_nth _ _ (0, 0) Hnth). intros ->. unfold art_zapart, apart in AP. cbn [art_rel_zone fst snd] in *. lia.
Qed.
Definition art_rcy_tr (sp1 : Z) (G : art_rg) (es : list art_rel) (M M' : word -> option byte) : Prop :=
(forall x : word, sp1 <= U x -> M' x = M x)
/\ (forall a n, 0 <= a -> a + n < 2 ^ 64 -> (HI <= a \/ Forall (fun e => art_zapart e a n) es) -> wrA M a n -> wrA M' a n)
/\ (forall zlo zlen, 0 < zlen -> art_rcy_prot spb G zlo zlen -> Forall (fun e => art_zapart e zlo zlen) es ->
art_rcy_prot spb (art_rel_steps es G) zlo zlen
/\ forall a (k : nat) v, zlo <= a -> a + Z.of_nat k <= zlo + zlen -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M a k v -> cellA M' a k v)
/\ art_agree (art_rels_fp sp1 G es) M M'.
#[using="Type"] Lemma art_rcy_tr_nil : ltac2:(TCodec.tc2 tcn__JatRecycle5T "E'?'O'RAyR0%211'6y8%511%311p051&Q9r3r2(5'K%211r1%7565211pQ691pQ2B1pU0D1").
Proof.
intros sp1 G M. split; [intros; reflexivity|]. split; [intros; assumption|]. split; [|apply (art_agree_refl [])].
intros zlo zlen _ P _. split; [exact P|]. intros; assumption.
Qed.
#[using="tp tsd qs GEO"] Lemma art_rcy_tr_one : ltac2:(TCodec.tc2 tcn__JatRecycle5T "RF'?'O'K'RAyR0%211'6y8%511%311p051&Q3r4r3%3221&Q2vAvRBvQNvR@vR<r5%76654321&QG&QKr7+Z0%3221%52<1&QHr8&QJ+2+Q?%3221%6251&J&Q6vR>r9%37GE2D1:?r6%6321Ezr2%F221&QF%12Q23+R0%B2A1%E231'=%M2Q4Q8&QAr<%231Q;Q:%5241&G&QD%2415Q6Q?%3426CQ7p021p061p0=1p0C1pTFR11pSJR21&Q9r;r:(1(5%11R6%33R7Q21%75651Q<QAp091p0Q21p0Q:1p0QB1p0QI1p0R21pQ8R71pQ6R81pT0RA1pQ2RC1pU0RE1").
Proof.
intros sp1 G e M M' RG BG HHI Hsp' AG WT.
split. { intros x Hx. apply AG. eapply art_gap_out; [apply (art_rel_fp_above HI t ctx tp tsd spb ris qs parr GEO sp1 G e (U x) 1 RG BG HHI Hsp' Hx); lia|lia]. }
split; [intros a n Ha Hn Hh Wa; apply (WT a n Ha Hn); [destruct Hh as [H|H]; [left; exact H|right; exact (Forall_inv H)]|exact Wa]|]. split; [|cbn [art_rels_fp]; rewrite app_nil_r; exact AG].
intros zlo zlen Hz P Hf. apply Forall_inv in Hf. split.
- cbn [art_rel_steps fold_left]. apply art_rcy_prot_step; assumption.
- intros a k v Ha Hk Ha0 Hk' C. apply (art_cell_tr _ M M' a k v AG); [|exact Ha0|exact Hk'|exact C].
apply (art_rel_fp_prot HI t ctx tp tsd spb ris qs parr GEO sp1 G e zlo zlen a (Z.of_nat k) RG BG HHI Hsp' Hz P Hf Ha Hk). lia.
Qed.
#[using="Type"] Lemma art_rcy_tr_app : ltac2:(TCodec.tc2 tcn__JatRecycle5T "Q5'?'O'3'K%211'RAyR0%211'6y8%511%311p051&Q9r7r6r5r3r2%6554321r8&M%1278%:531765r9&0%13G<;%>5371;:p051p0:1pQ<B1pQ:C1pQ6D1pT:M1pT8N1pQ2Q21pU0Q41").
Proof.
intros sp1 G es1 es2 M M1 M2 (F1 & W1 & P1 & A1) (F2 & W2 & P2 & A2).
split; [intros x Hx; rewrite (F2 x Hx); apply F1; exact Hx|]. split.
{ intros a n Ha Hn Hh Wa. apply W2; [exact Ha|exact Hn|destruct Hh as [H|H]; [left; exact H|right; exact (proj2 (proj1 (Forall_app _ _ _) H))]|].
apply W1; [exact Ha|exact Hn|destruct Hh as [H|H]; [left; exact H|right; exact (proj1 (proj1 (Forall_app _ _ _) H))]|exact Wa]. }
split; [|rewrite art_rels_fp_app; eapply art_agree_trans; eassumption].
intros zlo zlen Hz P Hf. apply Forall_app in Hf. destruct Hf as [Hf1 Hf2].
destruct (P1 zlo zlen Hz P Hf1) as [P' T1]. destruct (P2 zlo zlen Hz P' Hf2) as [P'' T2].
split; [rewrite art_rel_steps_app; exact P''|]. intros a k v Ha Hk Ha0 Hk' C. apply T2; try assumption. apply T1; assumption.
Qed.
Definition art_rcy_trx (sp1 hi : Z) (G : art_rg) (es : list art_rel) (M M' : word -> option byte) : Prop :=
(forall x : word, hi <= U x -> M' x = M x)
/\ (forall a n, 0 <= a -> a + n < 2 ^ 64 -> (HI <= a \/ Forall (fun e => art_zapart e a n) es) -> wrA M a n -> wrA M' a n)
/\ (forall zlo zlen, 0 < zlen -> zlo + zlen <= HI -> art_rcy_prot spb G zlo zlen -> Forall (fun e => art_zapart e zlo zlen) es ->
art_rcy_prot spb (art_rel_steps es G) zlo zlen
/\ forall a (k : nat) v, zlo <= a -> a + Z.of_nat k <= zlo + zlen -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M a k v -> cellA M' a k v)
/\ art_agree (art_rels_fp sp1 G es ++ [(sp1, hi - sp1)]) M M'.
#[using="Type"] Lemma art_rcy_trx_of_tr : ltac2:(TCodec.tc2 tcn__JatRecycle5T "Q2'?'O'3'K%211'RAyR0%211'6y8%511%311p051&QGr6r5%3221&Q9r7r4r3r2%5547321&Q:r8%2617;:65p041p0;1pQ8@1pQ6A1pT4J1pQ2N1pT<Q01pU0Q11").
Proof.
intros sp1 hi G es M M' Hh (F & W & P & A). split; [intros x Hx; apply F; lia|]. split; [exact W|]. split; [intros zlo zlen Hz _ Pz Hf; exact (P zlo zlen Hz Pz Hf)|].
eapply art_agree_sub; [exact A|]. intros z Hz H. apply art_out_app in H. tauto.
Qed.
#[using="Type"] Lemma art_rcy_trx_own : ltac2:(TCodec.tc2 tcn__JatRecycle5T "Q@'?'O'RAyR0%211'6y8%511%311p051&QGvAr5%3221r6%5213&QCr4r3%3221&J(1'8%12GG(7r8&QKr7%2213%54MM41(5%118%;3931%=31E@&Q:r9'K%711%463=;1HJp061p0E1p0J1p0M1pQ8Q21pQ6Q31pQ2Q<1pT<Q>1pU0Q?1").
Proof.
intros sp1 hi G M M' HHI Hh GW A.
split. { intros x Hx. apply A. cbn [art_out fst snd]. split; [lia|exact I]. }
split; [intros a n _ _ _ Wa; eapply wr_grows; [exact GW|exact Wa]|].
split; [|cbn [art_rels_fp app]; exact A].
intros zlo zlen Hz Hzh Pz _. split; [exact Pz|]. intros a k v Ha Hk Ha0 Hk' C.
apply (art_cell_tr _ M M' a k v A); [cbn [art_gap fst snd]; split; [unfold apart; lia|exact I]|exact Ha0|exact Hk'|exact C].
Qed.
#[using="Type"] Lemma art_rcy_trx_app : ltac2:(TCodec.tc2 tcn__JatRecycle5T "Q7'?'O'3'K%211'RAyR0%211'6y8%511%311p051&Q:r8r7r6r5r3r2%76654321r9&M%1278%;63:1765r:&0%13H<;%?637>1;:p051p0:1pQ<C1pQ:D1pQ6E1pT:N1pT8O1pQ2Q31pT<Q51pU0Q61").
Proof.
intros sp1 hi G es1 es2 M M1 M2 (F1 & W1 & P1 & A1) (F2 & W2 & P2 & A2).
split; [intros x Hx; rewrite (F2 x Hx); apply F1; exact Hx|]. split.
{ intros a n Ha Hn Hh Wa. apply W2; [exact Ha|exact Hn|destruct Hh as [H|H]; [left; exact H|right; exact (proj2 (proj1 (Forall_app _ _ _) H))]|].
apply W1; [exact Ha|exact Hn|destruct Hh as [H|H]; [left; exact H|right; exact (proj1 (proj1 (Forall_app _ _ _) H))]|exact Wa]. }
split.
- intros zlo zlen Hz Hzh P Hf. apply Forall_app in Hf. destruct Hf as [Hf1 Hf2].
destruct (P1 zlo zlen Hz Hzh P Hf1) as [P' T1]. destruct (P2 zlo zlen Hz Hzh P' Hf2) as [P'' T2].
split; [rewrite art_rel_steps_app; exact P''|]. intros a k v Ha Hk Ha0 Hk' C. apply T2; try assumption. apply T1; assumption.
- eapply art_agree_sub; [eapply art_agree_trans; [exact A1|exact A2]|]. rewrite art_rels_fp_app. intros z Hz H.
rewrite !art_out_app in H. rewrite !art_out_app. tauto.
Qed.
Definition art_zsep (e e' : art_rel) : Prop := art_zapart e (fst (art_rel_zone spb e')) (snd (art_rel_zone spb e')).
#[using="Type"] Lemma art_rels_sep_app : ltac2:(TCodec.tc2 tcn__JatRecycle5T "H'3'K%211&<&Q@&0r2r1%33721%511':%715%815'>&QB%118%33?1:qT0@1%53A1<%9271%:291%B2<1pTDD1pTBE1").
Proof.
induction l1 as [|e r IH]; intros l2; cbn [app art_rels_sep].
- split; [intros H; split; [exact I|split; [exact H|constructor]]|tauto].
- rewrite IH. rewrite Forall_app. split.
+ intros ((A & B) & C & D & E). split; [split; assumption|]. split; [exact D|]. constructor; assumption.
+ intros ((A & C) & D & E). pose proof (Forall_inv E) as E1. pose proof (Forall_inv_tail E) as E2. tauto.
Qed.
Section SE.
Local Abbreviation SEC_T_art_rcy_prot_below := (ltac2:(TCodec.tc2 tcn__JatRecycle5T "K'O'?&Q2vAvRBvQNvR@vR<r3%76654321&Q5r4r2%347251':&QG+VbTP0%2216&QF%128;%521A%7241p091p0>1pU@G1pUBH1pQ2J1")) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_rcy_prot_below) 0%nat 0%nat).
Variable zlo : ltac:(sec_ty2 constr:(SEC_T_art_rcy_prot_below) 1%nat 0%nat).
Variable zlen : ltac:(sec_ty2 constr:(SEC_T_art_rcy_prot_below) 2%nat 0%nat).
Lemma art_rcy_prot_below : ltac:(sec_stmt2 constr:(SEC_T_art_rcy_prot_below) 3%nat 0%nat).
Proof using tp tsd ris qs GEO G zlo zlen.
intros ((_ & _ & _ & _ & _ & _ & GB & _) & _) P.
pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & _).
destruct P as [(c' & Hc' & Z1 & Z2)|(b & Hb & Z1 & Z2)]; [lia|]. destruct (GB _ Hb) as (_ & _ & _ & B0 & B1 & _). lia.
Qed.
End SE.
#[using="GEO"] Lemma art_rels_mem_trx : ltac2:(TCodec.tc2 tcn__JatRecycle5T "QO'?'O'3'K%211'RAyR0%211'6y8%511%311p051&Q4vAvRBvQNvRCvR7vRDvR@vR>vR=vR<r8r5r2%>==<;:987654321'>&Q<r6%211r4%53N21&QBr1%211%93Q217qT0Q31%;3Q419&Q:r:r9r7%4632D1C<&Q7%13J;3qT2Q<1%D3Q=15%E3Q>2Ip021p071p0=1p0D1p0K1pQ8Q;1pQ6Q<1pT6QE1pT4QF1pQ2QJ1pT<QL1pU0QM1pTHQN1").
Proof.
intros nt sp1 hi G es es' M M' INV ST SEP (_ & _ & P & _) MEM. apply Forall_forall. intros e' Hin.
pose proof (proj1 (Forall_forall _ _) ST e' Hin) as Se. pose proof (proj1 (Forall_forall _ _) MEM e' Hin) as Me.
destruct (art_rel_static_prot nt G M e' INV Se) as (Pz & Hz & _ & Z1 & Z2).
pose proof INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ISG & IBK & IPK).
destruct (art_rcy_prot_below G _ _ (conj ISG (conj IBK IPK)) Pz) as (Lo & Hi).
assert (Hf : Forall (fun e => art_zapart e (fst (art_rel_pzone e')) (snd (art_rel_pzone e'))) es).
{ apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) SEP e He) e' Hin) as Ap. unfold art_zsep, art_zapart, apart in *. lia. }
destruct (P _ _ Hz Hi Pz Hf) as (_ & T).
apply (art_rel_mem_tr G e' M M' Se); [|exact Me]. intros a k v Ha Hk C. apply T; [exact Ha|exact Hk|lia| |exact C].
pose proof GEO as (G1 & G2 & _). lia.
Qed.
End Tr.
