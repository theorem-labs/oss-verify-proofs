(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI0s YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj2 ACjm.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AChd ACjr ACj1 ACj0 ACjc ACje ACji.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation SB := YC81.SB.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section d.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TCMP : tcmp_spec B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Ltac env_agree32 HAE :=
lazymatch goal with
| |- env_agree 32 _ (ewset ?X ?n ?v) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YP03.env_agree_le 32 n); [lia | apply env_agree_ewset]]
| |- env_agree 32 _ (havoc ?X ?n ?ws) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YP03.env_agree_le 32 n); [lia | apply env_agree_havoc]]
| |- _ => exact HAE
end.
Section f.
Variables (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z)
(Wd Hd : Z).
Hypothesis HC : wctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Hypothesis HGEO : 1 <= Wd <= 65535 /\ 1 <= Hd <= 65535 /\ Nb = Wd * Hd /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 200) 8 Wd /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 208) 8 Hd.
Hypothesis HFIMG : val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 224) 8 fimg.
Let PDp := PD W memc fimg bimg gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Ltac wctx_names :=
pose proof HC as (HJc & Hfi & Hbi & HNb & Dfb & Hg & Hcf & Hbf & Hcb & Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx
& Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp & Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vsb & Vbfp);
pose proof HGEO as (RW & RH & HN & V200 & V112).
Ltac wprelude HJ :=
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 HJ) as HAR;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpres & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (WS : TCMP_STK = 4112) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Ltac rget R En :=
rewrite R; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact En.
Ltac run_ro_wkept HFr HG HARx WK WKn :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ _) (mrestrict _ _) =>
pose proof (wkept_trans B _ _ _ _ _ _ _ WK (wkept_of_run B LAWS Ef rs lyc Sc W _ _ _ sp1 HARx HFr HG
ltac:(let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros a (r & Hr & Hw); lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end; cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia|]); destruct Hr)
ltac:(lia) ltac:(lia) ltac:(pose proof WK as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WKn end.
Definition WKEPT5 : list (bv 5) := [2; 3; 4; 8; 9]%bv.
Definition s2o_regs := sr_set (sr_set (sr_set sr_atoms 12%bv (SOff 22 0)) 14%bv (SOff 22 1)) 27%bv (SLit 65535).
Definition s2o_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 88 96 88 88 [YP09.mkChunk 88 (CVal 8 (SOff 34 0))];
YP09.mkRegion (Some 9%nat) 152 160 152 160 [];
YP09.mkRegion (Some 9%nat) 160 168 160 160 [YP09.mkChunk 160 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 9%nat) 168 176 168 176 [];
YP09.mkRegion (Some 9%nat) 192 232 192 192 [YP09.mkChunk 200 (CVal 8 (SOff 11 0)); YP09.mkChunk 192 (CVal 8 (SOff 33 0));
YP09.mkChunk 224 (CVal 8 (SOff 36 0)); YP09.mkChunk 216 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 9%nat) 240 256 240 240 [YP09.mkChunk 240 (CVal 8 (SOff 6 0)); YP09.mkChunk 248 (CVal 8 (SOff 35 0))] ].
Definition s2o_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (11%nat, mkAF 1 65535 0); (22%nat, mkAF 1 65534 0);
(25%nat, HPTR 4); (24%nat, HPTR 3); (32%nat, HPTR 0); (36%nat, HPTR 0); (33%nat, mkAF 0 65533 0); (34%nat, mkAF 1 65534 0); (35%nat, HPTR 3) ] [] [].
Definition ss_s2o : sstate := mkSS 0x1c5c s2o_regs s2o_mem None s2o_facts.
Definition s2t_regs := sr_set sr_atoms 27%bv (SLit 65535).
Definition s2t_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 88 96 88 88 [YP09.mkChunk 88 (CVal 8 (SOff 34 0))];
YP09.mkRegion (Some 9%nat) 160 168 160 160 [YP09.mkChunk 160 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 9%nat) 168 176 168 168 [YP09.mkChunk 168 (CVal 8 (SOff 22 0))];
YP09.mkRegion (Some 9%nat) 192 232 192 192 [YP09.mkChunk 200 (CVal 8 (SOff 37 0)); YP09.mkChunk 192 (CVal 8 (SOff 33 0));
YP09.mkChunk 224 (CVal 8 (SOff 36 0)); YP09.mkChunk 216 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 9%nat) 240 256 240 240 [YP09.mkChunk 240 (CVal 8 (SOff 6 0)); YP09.mkChunk 248 (CVal 8 (SOff 35 0))] ].
Definition s2t_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (22%nat, mkAF 1 65534 0);
(25%nat, HPTR 4); (24%nat, HPTR 3); (32%nat, HPTR 0); (36%nat, HPTR 0); (33%nat, mkAF 0 65533 0); (34%nat, mkAF 1 65534 0); (35%nat, HPTR 3);
(37%nat, mkAF 1 65535 0) ] [] [].
Definition ss_s2t : sstate := mkSS 0x1d00 s2t_regs s2t_mem None s2t_facts.
Definition s2s_regs := sr_set sr_atoms 10%bv (SOff 19 0).
Definition s2s_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 88 96 88 96 [];
YP09.mkRegion (Some 9%nat) 160 168 160 168 [];
YP09.mkRegion (Some 9%nat) 192 216 192 200 [YP09.mkChunk 200 (CVal 8 (SOff 35 0)); YP09.mkChunk 208 (CVal 8 (SOff 15 0))] ].
Definition s2s_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (19%nat, mkAF 0 65534 0); (15%nat, mkAF 1 65535 0);
(21%nat, HPTR 4); (22%nat, HPTR 3); (35%nat, mkAF 1 65535 0) ] [] [].
Definition ss_s2s : sstate := mkSS 0x1c1c s2s_regs s2s_mem None s2s_facts.
End f.
End d.
End c.
End b.
