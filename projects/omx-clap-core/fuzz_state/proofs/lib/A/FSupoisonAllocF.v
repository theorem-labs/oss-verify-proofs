(* fuzz_state: __interceptor_free (via __wrap_free) under ARU for ANY set UP of user-poisoned heads: afree_realizes_allU. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* The twin of the released cgif_file_fuzzer theorem afree_realizes_all (lib/A/AFfs.v:70), concluding
   FSupoisonU.afree_realizesU (premise: every UP range lies outside the freed block), plus its U = [] corollary.
   Port-from lib/A/AFfs.v:29-74, text unchanged except where UP is threaded; the walks are the FSupoisonAllocF*.v twins
   over FSupoisonAllocFK.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YA00 YF0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFl4 AFem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFeq AFew AFeu AFfg.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU FSupoisonAllocR FSupoisonAllocRt FSupoisonAllocFK.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require
FSupoisonAllocFcd FSupoisonAllocFrs FSupoisonAllocFdr FSupoisonAllocFdn FSupoisonAllocFeq FSupoisonAllocFnc FSupoisonAllocFmd.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocR.
Module FRt := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocRt.
Module FK := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFK.
Module Fcd := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFcd.
Module Frs := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFrs.
Module Fdr := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFdr.
Module Fdn := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFdn.
Module Feq := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFeq.
Module Fnc := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFnc.
Module Fmd := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFmd.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* lib/A/AFfs.v:29 tfib_rchunk_of_arms, any UP. *)
Lemma tfib_rchunk_of_armsU : forall B, AR_laws tfibsegs B -> TfibSyms B -> FK.tfib_rchunk_sec_specU B -> FK.tfib_rchunk_specU B.
Proof.
intros B LAWS TB SEC ly X k cbp UP W regs mem md PRE. pose proof PRE as (((M & _) & _ & Hk & _) & _).
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd B ly X _ M); apply (ts_tsd _ TB)).
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ (am_wf B ly X _ M)) k Hk) as [_ CK].
destruct (ck_beg k) as [|off|r o|c q] eqn:Eb; try solve [destruct CK].
- exact (Fcd.tfib_rchunk_primU B LAWS TB ly X k cbp UP W regs mem md off PRE Eb HTSD).
- exact (SEC ly X k cbp UP W regs mem md r o PRE Eb).
Qed.
(* lib/A/AFfs.v:38 afree_realizes_of, any UP. *)
Theorem afree_realizes_ofU : forall B, AR_laws tfibsegs B -> TfibSyms B -> tfib_unwind_spec -> tfib_depot_spec B ->
FAR.tfib_refill_specU B -> FK.tfib_rchunk_sec_specU B -> FSU.afree_realizesU tfibsegs B.
Proof.
intros B LAWS TB U1 D1 R1 SEC ly S UP W regs mem md p n ch PRE Hp Hout Ha0 Htr.
rewrite (ts_code B TB) in Htr |- *. cbn [pc_free_ra0 pc_wrap_free Tfib_code] in Htr |- *.
pose proof PRE as (((M & _) & _) & _). assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd B ly S _ M); apply (ts_tsd _ TB)).
assert (Q1 : forall nb, FK.tfib_enqueue_spec_nbU B nb) by (intros [|]; [exact (Feq.tfib_enqueue_nbU B LAWS TB R1) | exact (Feq.tfib_enqueue_roomU B LAWS TB)]).
assert (D0 : FK.tfib_drain_specU B)
  by exact (Fdn.tfib_drain_okU B LAWS TB (Fdr.tfib_dorecycle_okU B LAWS TB (tfib_rchunk_of_armsU B LAWS TB SEC) (Fcd.tfib_cdealloc_okU B LAWS TB))).
destruct Hp as [-> | HBLK].
- cbn [sptr_addr sptr_exp aeval] in Ha0. exact (Fnc.afree_nullU B LAWS TB ly S UP W regs mem md n ch PRE Ha0 U1 HTSD).
- set (q := st_qthread S) in *.
destruct (Z_le_gt_dec (qc_bytes q + req_size n + (if need_new_batch q then kBatchBytes else 0)) kQuarantineCacheMax) as [ND|DR].
+
destruct (need_new_batch q) eqn:NB.
*
apply (Fmd.afree_midU B LAWS TB ly S UP W regs mem md p n ch PRE HBLK Hout Ha0 Htr); [subst q; rewrite NB; exact ND | exact tfib_ialloc_ok | exact U1 | exact D1 | apply Q1 | exact HTSD].
*
unfold need_new_batch in NB. destruct (rev (qc_list q)) as [|lastb initr] eqn:ER; [discriminate|]. apply Z.eqb_neq in NB.
assert (BL : Z.of_nat (length (b_items lastb)) < kBatchSlots).
{ pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ (am_wf B ly S _ M))) lastb) as H.
assert (IN : In lastb (all_batches S)) by (unfold all_batches; apply in_app_iff; left; subst q; apply in_rev; rewrite ER; left; reflexivity).
specialize (H IN). unfold kBatchSlots in *. lia. }
apply (Fnc.afree_commonU B LAWS TB ly S UP W regs mem md p n ch lastb initr PRE HBLK Hout Ha0 Htr); [| exact tfib_ialloc_ok | exact U1 | exact D1 | exact HTSD].
subst q. split; [exact ER | split; [exact BL | lia]].
+
apply (Fmd.afree_drnU B LAWS TB ly S UP W regs mem md p n ch PRE HBLK Hout Ha0 Htr); [subst q; lia | exact tfib_ialloc_ok | exact U1 | exact D1 | apply Q1 | exact D0 | exact HTSD].
Qed.
(* lib/A/AFfs.v:65 afree_realizes_sec, any UP. *)
Theorem afree_realizes_secU : forall B, AR_laws tfibsegs B -> TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
FK.tfib_rchunk_sec_specU B -> FSU.afree_realizesU tfibsegs B.
Proof.
intros B LAWS TS HD SEC. exact (afree_realizes_ofU B LAWS TS tfib_unwind_ok (tfib_depot_ok B TS HD) (FRt.tfib_refill_okU B TS) SEC).
Qed.
(* lib/A/AFfs.v:70 afree_realizes_all, any UP. *)
Theorem afree_realizes_allU : forall B, AR_laws tfibsegs B -> TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
FSU.afree_realizesU tfibsegs B.
Proof.
intros B LAWS TS HD. exact (afree_realizes_secU B LAWS TS HD (Frs.tfib_rchunk_secU B LAWS TS)).
Qed.
(* The U = [] form: the released statement (YG0d.v afree_realizes), through FSupoisonU.afree_realizes_of_U. *)
Corollary afree_realizes_all_of_U : forall B, AR_laws tfibsegs B -> TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
afree_realizes tfibsegs B.
Proof. intros B LAWS TS HD. exact (FSU.afree_realizes_of_U tfibsegs B (afree_realizes_allU B LAWS TS HD)). Qed.
End a.
