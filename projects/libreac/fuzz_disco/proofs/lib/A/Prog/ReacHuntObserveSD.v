(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 70 of its 99 lines of code are new or changed and 40 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YA0q YCbm YK06 YI0m YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoFrame DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC1i YC45 YC4b YC7k YC81 YC85 YC88 YCbw YCkd ACbf ACj1 DiscoACja DiscoACjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
ClassifyCore ReacDiscoClassifyOnSegment ReacDiscoTableObserve DiscoRo ReacFrameCleanLen ReacHuntObserve ReacHuntObserveSeg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_classify_c disco_table_c hunt_c reac_disco_table_observe_c reac_frame_clean_len_c reac_hunt_observe_c
HuntObsFacts HuntObsLib.
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
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis DRO : disco_ro_unowned B.

Lemma ho_seg_D : ho_seg_T_stmt B -> ho_seg_D_stmt B.
Proof.
intros HT. unfold ho_seg_D_stmt.
intros c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F HB H19 H23 H25 Hfsh Hret HOKc Hout.
pose proof HB as (Hpre & Hmid & Hsp1 & HFa & Hregs & Hsav).
pose proof Hmid as (HJ & Hfrm & Hfad & Hperm & HK & HGH & Hfl & HLH).
pose proof (paj_run_to (fx := c_fq c) B LAWS) as RUNTO.
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi (fx := c_fq c) SEGS VAL E (mkSS 0x719c sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst (fx := c_fq c) regs2 (Z_to_bv 64 (BASE + 0x719c)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - cbv; tauto.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS HOx [] E (mrestrict (w_H W2) mem2)) by constructor.
unfold ho_cfg.
paj_run_to_tok RUNTO HS HJ SHOK HOspan 0x71a0; [apply awr_ok_nil |].
lazymatch goal with HFm : frame_of _ _ mem2 (ms_mem ?m1) |- _ =>
  assert (Hm : ms_mem m1 = mem2)
  by (apply functional_extensionality; intros x; apply HFm; intros (r & Hr & _); cbn [ss_mem In] in Hr; destruct Hr) end.
prreg HS (20%bv : bv 5) R20.
prreg HS (2%bv : bv 5) R2. rewrite (EE 2%nat 2%bv eq_refl) in R2.
prreg HS (3%bv : bv 5) R3. rewrite (EE 3%nat 3%bv eq_refl) in R3.
prreg HS (4%bv : bv 5) R4. rewrite (EE 4%nat 4%bv eq_refl) in R4.
prreg HS (8%bv : bv 5) R8. rewrite (EE 8%nat 8%bv eq_refl) in R8.
prreg HS (9%bv : bv 5) R9. rewrite (EE 9%nat 9%bv eq_refl) in R9.
prreg HS (18%bv : bv 5) R18. rewrite (EE 18%nat 18%bv eq_refl) in R18.
prreg HS (22%bv : bv 5) R22. rewrite (EE 22%nat 22%bv eq_refl) in R22.
prreg HS (25%bv : bv 5) R25. rewrite (EE 25%nat 25%bv eq_refl) in R25.
prreg HS (26%bv : bv 5) R26. rewrite (EE 26%nat 26%bv eq_refl) in R26.
prreg HS (27%bv : bv 5) R27. rewrite (EE 27%nat 27%bv eq_refl) in R27.
pmkst HS. rewrite Hm in HJ |- *.
eapply (HT c fpos ly2 S2 W2 mem2 _ k2 (ms_regs ms) sp1 F (ho_Hcls c) (-1)).
- refine (conj Hpre (conj _ (conj Hsp1 (conj HFa (conj _ Hsav))))).
  + exact (conj HJ (conj Hfrm (conj Hfad (conj Hperm (conj HK (conj HGH (conj Hfl HLH))))))).
  + unfold ho_regs_mid. rewrite R2, R3, R4, R8, R9, R18, R22, R26, R27. exact Hregs.
- rewrite R20. apply bv_eq. reflexivity.
- left. reflexivity.
- rewrite R25. exact H25.
- exact Hfsh.
- exact HOKc.
- unfold tho_model. cbv zeta. split.
  + intros _. split; [reflexivity|]. split; [reflexivity | exact Hout].
  + intros H0. exfalso. exact (Hret H0).
Qed.

End h.
End f.
End d.
