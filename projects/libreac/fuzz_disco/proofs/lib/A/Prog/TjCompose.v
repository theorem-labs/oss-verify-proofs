From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow PaStep DiscoSyms DiscoList DiscoAddr DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import TjSpec TjBase DiscoRo TjCuts TjLoopCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
Section h.
Variable B : asyms.
Variables STK EV EVB : Z.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Hypothesis HENTRY : tj_from0 B STK EV IMG ss_tj0 (INV_tj0 B 0) -> tj_specP B STK EV IMG.
Hypothesis HPRE : tj_fromX B STK EV IMG -> tj_fromC B STK EV EVB IMG ->
(forall i, tj_fromL B STK EV EVB IMG i) -> tj_from0 B STK EV IMG ss_tj0 (INV_tj0 B 0).
Hypothesis HEXIT : tj_fromX B STK EV IMG.
Hypothesis HCLOSE : tj_fromX B STK EV IMG -> tj_fromC B STK EV EVB IMG.
Hypothesis HMAC : tj_seg_mac B STK EV EVB IMG.
Hypothesis HROLE : tj_seg_role B STK EV EVB IMG.
Hypothesis HBOX : tj_seg_box B STK EV EVB IMG.
Hypothesis HUNK : tj_seg_unk B STK EV EVB IMG.
Hypothesis HTOK : tj_seg_tok B STK EV EVB IMG.
Hypothesis HTAIL : tj_seg_tail B STK EV EVB IMG.
Lemma tjc_fromL_ge8 : forall i, 8 <= i -> tj_fromL B STK EV EVB IMG i.
Proof.
intros i Hi. unfold tj_fromL, tj_from0.
intros cx E k ly3 S3 W3 ms3 md3 HBASE _ _ _ HINV _.
unfold tj_baseX in HBASE.
destruct HBASE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOK & _).
unfold disco_table_c.table_ok, disco_table_c.tbl_T1 in HOK.
destruct HOK as (HT1 & _).
unfold INV_tjL in HINV.
destruct HINV as (_ & _ & _ & _ & Hn & _).
exfalso. lia.
Qed.
Lemma tjc_body : forall i, tj_fromL B STK EV EVB IMG (i + 1) -> tj_fromL B STK EV EVB IMG i.
Proof.
intros i HL.
pose proof (HTAIL i HEXIT (HCLOSE HEXIT) HL) as HT.
exact (HMAC i HEXIT (HROLE i HEXIT (HBOX i (HUNK i HEXIT HT) (HTOK i HEXIT HT)))).
Qed.
Lemma tjc_loop_down : forall (n : nat) (i : Z), 8 - i <= Z.of_nat n -> tj_fromL B STK EV EVB IMG i.
Proof.
induction n as [|n IH]; intros i Hi.
- apply tjc_fromL_ge8. lia.
- destruct (Z_le_gt_dec 8 i) as [H8 | H8].
  + apply tjc_fromL_ge8. exact H8.
  + apply tjc_body. apply IH. lia.
Qed.
Theorem tj_loop_all : forall i, tj_fromL B STK EV EVB IMG i.
Proof.
intros i. apply (tjc_loop_down (Z.to_nat (8 - i))). lia.
Qed.
Theorem pb_reac_disco_table_json : tj_specP B STK EV IMG.
Proof.
exact (HENTRY (HPRE HEXIT (HCLOSE HEXIT) tj_loop_all)).
Qed.
End h.
End f.
End d.
