(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YA00 YF0p.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFl4 AFem AFkv.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFeq AFew AFeu AFfg AFfu AFg3 AFg2 AFg6 AFg4 AFfz AFet AFg7 AFes AFg9.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition tfib_rchunk_sec_spec (B : asyms) : Prop :=
forall ly X k cbp (W : world tfibsegs) regs mem md r o,
rcc_pre B ly X k cbp W regs mem md -> ck_beg k = PSec r o ->
amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (rcc_leaf B ly X k W regs mem md).
Lemma tfib_rchunk_of_arms : forall B, TfibSyms B -> tfib_rchunk_sec_spec B -> tfib_rchunk_spec B.
Proof.
intros B TB SEC ly X k cbp W regs mem md PRE. pose proof PRE as ((M & _) & _ & Hk & _).
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd B ly X _ M); apply (ts_tsd _ TB)).
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ (am_wf B ly X _ M)) k Hk) as [_ CK].
destruct (ck_beg k) as [|off|r o|c q] eqn:Eb; try solve [destruct CK].
- exact (tfib_rchunk_prim B TB ly X k cbp W regs mem md off PRE Eb HTSD).
- exact (SEC ly X k cbp W regs mem md r o PRE Eb).
Qed.
Theorem afree_realizes_of : forall B, TfibSyms B -> tfib_unwind_spec -> tfib_depot_spec B -> tfib_refill_spec B ->
tfib_rchunk_sec_spec B -> afree_realizes tfibsegs B.
Proof.
intros B TB U1 D1 R1 SEC ly S W regs mem md p n ch PRE Hp Ha0 Htr.
rewrite (ts_code B TB) in Htr |- *. cbn [pc_free_ra0 pc_wrap_free Tfib_code] in Htr |- *.
pose proof PRE as ((M & _) & _). assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd B ly S _ M); apply (ts_tsd _ TB)).
assert (Q1 : forall nb, tfib_enqueue_spec_nb B nb) by (intros [|]; [exact (tfib_enqueue_nb B TB R1) | exact (tfib_enqueue_room B TB)]).
assert (D0 : tfib_drain_spec B) by exact (tfib_drain_ok B TB (tfib_dorecycle_ok B TB (tfib_rchunk_of_arms B TB SEC))).
destruct Hp as [-> | HBLK].
-   cbn [sptr_addr sptr_exp aeval] in Ha0. exact (afree_null B TB ly S W regs mem md n ch PRE Ha0 U1 HTSD).
- set (q := st_qthread S) in *.
destruct (Z_le_gt_dec (qc_bytes q + req_size n + (if need_new_batch q then kBatchBytes else 0)) kQuarantineCacheMax) as [ND|DR].
+
destruct (need_new_batch q) eqn:NB.
*
apply (afree_mid B TB ly S W regs mem md p n ch PRE HBLK Ha0 Htr); [subst q; rewrite NB; exact ND | exact tfib_ialloc_ok | exact U1 | exact D1 | apply Q1 | exact HTSD].
*
unfold need_new_batch in NB. destruct (rev (qc_list q)) as [|lastb initr] eqn:ER; [discriminate|]. apply Z.eqb_neq in NB.
assert (BL : Z.of_nat (length (b_items lastb)) < kBatchSlots).
{ pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ (am_wf B ly S _ M))) lastb) as H.
assert (IN : In lastb (all_batches S)) by (unfold all_batches; apply in_app_iff; left; subst q; apply in_rev; rewrite ER; left; reflexivity).
specialize (H IN). unfold kBatchSlots in *. lia. }
apply (afree_common B TB ly S W regs mem md p n ch lastb initr PRE HBLK Ha0 Htr); [| exact tfib_ialloc_ok | exact U1 | exact D1 | exact HTSD].
subst q. split; [exact ER | split; [exact BL | lia]].
+
apply (afree_drn B TB ly S W regs mem md p n ch PRE HBLK Ha0 Htr); [subst q; lia | exact tfib_ialloc_ok | exact U1 | exact D1 | apply Q1 | exact D0 | exact HTSD].
Qed.
Theorem afree_realizes_sec : forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
tfib_rchunk_sec_spec B -> afree_realizes tfibsegs B.
Proof.
intros B TS HD SEC. exact (afree_realizes_of B TS tfib_unwind_ok (tfib_depot_ok B TS HD) (tfib_refill_ok B TS) SEC).
Qed.
Theorem afree_realizes_all : forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
afree_realizes tfibsegs B.
Proof.
intros B TS HD. apply (afree_realizes_sec B TS HD). intros ly X k cbp W regs mem md r o PRE Hb. exact (tfib_rchunk_sec B TS ly X k cbp W regs mem md r o PRE Hb).
Qed.
End a.
