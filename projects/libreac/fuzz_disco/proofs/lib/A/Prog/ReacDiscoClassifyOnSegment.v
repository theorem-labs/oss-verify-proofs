(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8c.v:168-170
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:371-373 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8a.v:360-365 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:341-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/put_dec.v, with its module paths and module names changed; 1355 of its 1430 lines of code are new or changed and 3265 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacPortsParse.v, with its module paths and module names changed; 50 of its 83 lines of code are new or changed and 1397 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ClassifyCore.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YP0m YP0l YP03 YP06.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC45.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TCLS : tclassify_core_spec B.

Definition treac_disco_classify_on_segment_spec : Prop :=
tcls_entry B (BASE + AF_reac_disco_classify_on_segment).

Theorem pb_reac_disco_classify_on_segment : treac_disco_classify_on_segment_spec.
Proof.
unfold treac_disco_classify_on_segment_spec, tcls_entry.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch lk f len u o FB U OB L
HJ HROD Hra Hra4 Hgp Htp H10 H11 H12 H13 H14 Hch Hal Hstk Hsp Htop Hdep Hlen LFB LU LOB HF HUr HUs HUg Ho Ho4 HOr HOg HOw HOst HL HOU HOF HLd.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env (@pa_val _ disco_listing PI) A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi (fx := fq) SEGS (@pa_val _ disco_listing PI) E (mkSS AF_reac_disco_classify_on_segment sr_atoms [] None (mkFacts [] [] []))
(restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_reac_disco_classify_on_segment)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. subst E.
apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
clear HE.
unfold cfg_at.
eapply (SRr_run_pi_AJ_call (fx := fq) B LAWS W FUEL E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS);
[vm_compute; reflexivity | exact HJ | intros a (r & Hr & _); destruct Hr |].
intros ms' mat' HS' HJ' HFr _ _.
assert (Em : ms_mem ms' = memc) by (apply functional_extensionality; intros x; apply HFr; intros (r & Hr & _); destruct Hr).
pose proof (regs_kept_of_st_ok SEGS E _ _ regs [] [1; 2; 3; 4; 8; 10; 11; 12; 13; 14]%bv HS' HAE ltac:(vm_compute; reflexivity)) as RK.
pose proof (aregs_preserved_of_st_ok SEGS (w_H W) E _ ms' regs [] HS' HAE ltac:(vm_compute; reflexivity)) as HPR.
cbn [ms_regs restrict] in RK.
pose proof (RK 1%bv ltac:(cbn; tauto)) as R1. pose proof (RK 2%bv ltac:(cbn; tauto)) as R2.
pose proof (RK 3%bv ltac:(cbn; tauto)) as R3. pose proof (RK 4%bv ltac:(cbn; tauto)) as R4.
pose proof (RK 8%bv ltac:(cbn; tauto)) as R8.
pose proof (RK 10%bv ltac:(cbn; tauto)) as Ga0. pose proof (RK 11%bv ltac:(cbn; tauto)) as Ga1.
pose proof (RK 12%bv ltac:(cbn; tauto)) as Ga2. pose proof (RK 13%bv ltac:(cbn; tauto)) as Ga3.
pose proof (RK 14%bv ltac:(cbn; tauto)) as Ga4. clear RK.
assert (Usp : spZ (ms_regs ms') = spZ regs) by (unfold spZ; rewrite R2; reflexivity).
assert (Us0 : s0Z (ms_regs ms') = s0Z regs) by (unfold s0Z; rewrite R8; reflexivity).
assert (Ura : raZ (ms_regs ms') = raZ regs) by (unfold raZ; rewrite R1; reflexivity).
assert (Hsig : pa_sigma DS_classify_core = BASE + AF_classify_core)
by (apply pa_xcalls; cbn [In disco_xcalls]; repeat (first [left; reflexivity | right])).
pmkst HS'. rewrite Em, Hsig. rewrite Em in HJ'.
eapply SRr_mono.
{ unfold tclassify_core_spec, tcls_entry in TCLS.
apply (TCLS fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc _ k (ms_regs ms') ch lk f len u o FB U OB L HJ' HROD);
rewrite ?R1, ?R3, ?R4, ?Ga0, ?Ga1, ?Ga2, ?Ga3, ?Ga4, ?Usp, ?Us0, ?Ura; assumption. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hc & Hfx & Hcs & HJ2 & HP2 & HPost).
exists fx', ly2, S2, regs2, mem2, md2. rewrite R1, Usp in *.
split; [exact Hc|]. split; [exact Hfx|]. split; [exact Hcs|].
split; [exact HJ2|]. split; [exact (aregs_preserved_trans _ _ _ HPR HP2) | exact HPost].
Qed.

End h.
End f.
End d.
