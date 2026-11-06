(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YA00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0g YF8y YF0f YF8m.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0o YF1a YF1p YF1y YF1x YF21 YF1z YF1u YF0n YF22 YF0m YF24.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac img_facts ::= lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F end.
Ltac img_lia ::=
first [ (img_goal_has_k; img_facts; lia)
| lia
| (img_inst; lia)
| (try img_inst;
first [ (img_local; img_local_unfold; img_unfold_all; lia)
| (img_arith_rel; first [ (img_facts; lia)
| (img_has_moddiv; img_case; img_unfold_all; lia)
| (first [ img_has_moddiv | img_has_match ]; img_concrete; img_unfold_all; lia) ]) ]) ].
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition tfx_rchunk_sec_spec {imgk : img} (B : asyms) : Prop :=
forall ly X k cbp (W : world tfxsegs) regs mem md r o,
rcc_pre B ly X k cbp W regs mem md -> ck_beg k = PSec r o ->
amreal tfxsegs (recycle_chunk k X) W (cfg_at tfxsegs A_RChunk regs mem md) (rcc_leaf B ly X k W regs mem md).
Lemma tfx_rchunk_of_arms {imgk : img} : forall B, TfxSyms B -> tfx_rchunk_sec_spec B -> tfx_rchunk_spec B.
Proof.
intros B TB SEC ly X k cbp W regs mem md PRE. pose proof PRE as ((M & _) & _ & Hk & _).
assert (HTSD : ly_tsd ly = TFX_TSD) by (img_try (rewrite (am_tsd B ly X _ M); img_apply (ts_tsd _ TB))).
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ (am_wf B ly X _ M)) k Hk) as [_ CK].
destruct (ck_beg k) as [|off|r o|c q] eqn:Eb; try solve [destruct CK].
- img_exact (tfx_rchunk_prim B TB ly X k cbp W regs mem md off PRE Eb HTSD).
- img_exact (SEC ly X k cbp W regs mem md r o PRE Eb).
Qed.
Theorem afree_realizes_of {imgk : img} : forall B, TfxSyms B -> tfx_unwind_spec -> tfx_depot_spec B -> tfx_refill_spec B ->
tfx_rchunk_sec_spec B -> afree_realizes tfxsegs B.
Proof.
intros B TB U1 D1 R1 SEC ly S W regs mem md p n ch PRE Hp Ha0 Htr.
rewrite (ts_code B TB) in Htr |- *. cbn [pc_free_ra0 pc_wrap_free Tfx_code] in Htr |- *.
pose proof PRE as ((M & _) & _). assert (HTSD : ly_tsd ly = TFX_TSD) by (img_try (rewrite (am_tsd B ly S _ M); img_apply (ts_tsd _ TB))).
assert (Q1 : forall nb, tfx_enqueue_spec_nb B nb) by (img_try (intros [|]; [img_try (img_exact (tfx_enqueue_nb B TB R1)) | img_try (img_exact (tfx_enqueue_room B TB))])).
assert (D0 : tfx_drain_spec B) by img_exact (tfx_drain_ok B TB (tfx_dorecycle_ok B TB (tfx_rchunk_of_arms B TB SEC))).
destruct Hp as [-> | HBLK].
-   cbn [sptr_addr sptr_exp aeval] in Ha0. img_exact (afree_null B TB ly S W regs mem md n ch PRE Ha0 U1 HTSD).
- set (q := st_qthread S) in *.
destruct (Z_le_gt_dec (qc_bytes q + req_size n + (if need_new_batch q then kBatchBytes else 0)) kQuarantineCacheMax) as [ND|DR].
+
destruct (need_new_batch q) eqn:NB.
*
img_apply (afree_mid B TB ly S W regs mem md p n ch PRE HBLK Ha0 Htr); [img_try ((subst q; cbv beta); rewrite NB; img_exact ND) | img_try (img_exact tfx_ialloc_ok) | img_try (img_exact U1) | img_try (img_exact D1) | img_try (img_apply Q1) | img_try (img_exact HTSD)].
*
unfold need_new_batch in NB. destruct (rev (qc_list q)) as [|lastb initr] eqn:ER; [img_try (discriminate)|]. apply Z.eqb_neq in NB.
assert (BL : Z.of_nat (length (b_items lastb)) < kBatchSlots).
{ pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ (am_wf B ly S _ M))) lastb) as H.
assert (IN : In lastb (all_batches S)) by (img_try (unfold all_batches; img_apply in_app_iff; left; (subst q; cbv beta); img_apply in_rev; rewrite ER; left; img_refl)).
specialize (H IN). unfold kBatchSlots in *. img_lia. }
img_apply (afree_common B TB ly S W regs mem md p n ch lastb initr PRE HBLK Ha0 Htr); [| img_try (img_exact tfx_ialloc_ok) | img_try (img_exact U1) | img_try (img_exact D1) | img_try (img_exact HTSD)].
(subst q; cbv beta). split; [img_try (img_exact ER) | img_try (split; [img_exact BL | img_lia])].
+
img_apply (afree_drn B TB ly S W regs mem md p n ch PRE HBLK Ha0 Htr); [img_try ((subst q; cbv beta); img_lia) | img_try (img_exact tfx_ialloc_ok) | img_try (img_exact U1) | img_try (img_exact D1) | img_try (img_apply Q1) | img_try (img_exact D0) | img_try (img_exact HTSD)].
Qed.
Theorem afree_realizes_sec {imgk : img} : forall B, TfxSyms B -> (forall t, as_dhash B t = tfx_dhash t) ->
tfx_rchunk_sec_spec B -> afree_realizes tfxsegs B.
Proof.
intros B TS HD SEC. img_exact (afree_realizes_of B TS tfx_unwind_ok (tfx_depot_ok B TS HD) (tfx_refill_ok B TS) SEC).
Qed.
Theorem afree_realizes_all {imgk : img} : forall B, TfxSyms B -> (forall t, as_dhash B t = tfx_dhash t) ->
afree_realizes tfxsegs B.
Proof.
intros B TS HD. img_apply (afree_realizes_sec B TS HD). intros ly X k cbp W regs mem md r o PRE Hb. img_exact (tfx_rchunk_sec B TS ly X k cbp W regs mem md r o PRE Hb).
Qed.
End a.
