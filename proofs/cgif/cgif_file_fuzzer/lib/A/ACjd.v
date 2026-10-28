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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj2.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AChd ACjr ACj1 ACj0 ACjc.
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
Ltac tin_ctx_names H :=
destruct H as (HJ & Hpt & Hpawr & Hbi & HNb & HsepI & Hg & Hcf & Hbf & Hcb & HsepG & HsepC & HsepB
& Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx & Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp
& Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vtidx & Rtidx & Vsb & Vbfp & H26 & H27 & H21 & H22).
Ltac tin_prelude HJ :=
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 HJ) as HAR;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpres & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (WS : TCMP_STK = 4112) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Ltac env_agree32 HAE :=
lazymatch goal with
| |- env_agree 32 _ (ewset ?X ?n ?v) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YP03.env_agree_le 32 n); [lia | apply env_agree_ewset]]
| |- env_agree 32 _ (havoc ?X ?n ?ws) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YP03.env_agree_le 32 n); [lia | apply env_agree_havoc]]
| |- _ => exact HAE
end.
Ltac tctx_regs_of HK := let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; apply HK; cbv [TCTX_REGS In] in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr.
Definition TOUT_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 23; 24; 25; 28; 29; 30; 31]%bv.
Definition TOUT_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 21; 22; 26]%bv.
Lemma tout_clob_cases3 : forall r : bv 5, reg_in r TOUT_CLOB = false -> r = 0%bv \/ r = 27%bv \/ In r TOUT_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | right; left; reflexivity | vm_compute in Hr; discriminate | right; right; cbv; tauto] |]). destruct Hin.
Qed.
Lemma tout_tin_clob : forall r : bv 5, reg_in r TOUT_CLOB = false -> reg_in r TIN_CLOB = false.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [vm_compute in Hr; discriminate | vm_compute; reflexivity] |]). destruct Hin.
Qed.
Definition tout_regs := sr_set (sr_set sr_atoms 18%bv (SOff 19 0)) 27%bv (SLit 4294967295).
Definition tout_loc : YP09.region :=
YP09.mkRegion (Some 9%nat) 176 256 208 232
[YP09.mkChunk 176 (CVal 8 (SOff 32 0)); YP09.mkChunk 184 (CVal 8 (SOff 33 0)); YP09.mkChunk 192 (CVal 8 (SOff 20 0));
YP09.mkChunk 200 (CVal 8 (SOff 34 0)); YP09.mkChunk 232 (CVal 8 (SOff 35 0)); YP09.mkChunk 240 (CVal 8 (SOff 6 0));
YP09.mkChunk 248 (CVal 8 (SOff 36 0))].
Definition tout_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (32%nat, mkAF 281474976710656 18446744073709551615 0);
(20%nat, mkAF 1 65535 0); (19%nat, HPTR 0) ] [] [].
Definition ss_tout : sstate := mkSS 0x21f4 tout_regs [tout_loc] None tout_facts.
Definition totl_loc : YP09.region :=
YP09.mkRegion (Some 9%nat) 184 232 184 184
[YP09.mkChunk 184 (CVal 8 (SOff 32 0)); YP09.mkChunk 192 (CVal 8 (SOff 33 0)); YP09.mkChunk 200 (CVal 8 (SOff 34 0));
YP09.mkChunk 208 (CVal 8 (SOff 19 0)); YP09.mkChunk 216 (CVal 8 (SOff 35 0)); YP09.mkChunk 224 (CVal 8 (SOff 36 0))].
Definition totl_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (19%nat, HPTR 0); (32%nat, mkAF 1 65535 0); (33%nat, mkAF 1 65535 0);
(34%nat, mkAF 0 65535 0); (35%nat, mkAF 0 4294967295 0); (36%nat, mkAF 0 65534 0) ] [] [].
Definition ss_totl : sstate := mkSS 0x22a0 sr_atoms [totl_loc] None totl_facts.
Definition tout_ctx (W : world SEGS) (memc : word -> option byte) (sp1 w h top left Wd Nb : Z) : Prop :=
1 <= w <= 65535 /\ 1 <= h <= 65535 /\ 0 <= top /\ 0 <= left /\ left + w <= Wd /\ 0 <= Wd <= 65535 /\ (top + h) * Wd <= Nb /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 176) 8 (w * 2 ^ 48) /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 184) 8 h /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 192) 8 w /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 200) 8 Wd.
Lemma val_mem_frame8 : forall E rs (m m' : word -> option byte) a v lo hi,
frame_of E rs m m' -> (forall x, in_wrange E rs x -> lo <= x < hi) -> (a + 8 <= lo \/ hi <= a) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
val_mem SEGS m a 8 v -> val_mem SEGS m' a 8 v.
Proof.
intros E rs m m' a v lo hi HF Hw Hout Ha Ha8 Hv. apply (val_mem_frame E rs m m' a 8 v HF); [| exact Ha | cbn [Z.of_nat]; lia | exact Hv].
intros k Hk Hin. pose proof (Hw _ Hin). cbn [Z.of_nat] in Hk. lia.
Qed.
End d.
End c.
End b.
