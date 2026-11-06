(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_init on fuzz_grant.asan, written for libreac/fuzz_grant: the entry seat and the return are adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v, the __asan_memset call from proofs/cgif/cgif_file_fuzzer/lib/A/AC8y.v, the reseat after it from proofs/cgif/cgif_file_fuzzer/lib/A/ACbl.v, and further proof steps from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v and proofs/cgif/cgif_file_fuzzer/lib/A/AE6j.v; the contract is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxInit.v, with its module paths and module names changed; 223 of its 297 lines of code are new or changed and 113 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ReacDiscoGateInit.v, with its module names changed; 72 of its 111 lines of code are new or changed and 258 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ClassifyCore.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YP0m YP0l YP03 YP06.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC45.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TCLS : tclassify_core_spec B.

Definition treac_disco_classify_spec : Prop :=
forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
(f len u o : Z) (FB U OB : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 f -> getr regs 11 = w64 len -> getr regs 12 = w64 u -> getr regs 13 = w64 o ->
achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CLS_STK -> spZ regs <= sp0 ->
spZ regs + 32 <= ly_top lyc ->
Z.of_nat (length (frames Sc)) <= CLS_DEPTH ->
0 <= len < 2 ^ 64 ->
length FB = 50%nat -> length U = 6%nat -> length OB = 24%nat ->
(50 <= len -> 0 < f /\ cls_read W memc (spZ regs) f 50 /\ cls_sep B lyc Sc f 50 /\
garr8 SEGS (mrestrict (w_H W) memc) f (cls_bytes FB)) ->
cls_read W memc (spZ regs) u 6 -> cls_sep B lyc Sc u 6 ->
garr8 SEGS (mrestrict (w_H W) memc) u (cls_bytes U) ->
0 < o -> o mod 4 = 0 ->
cls_read W memc (spZ regs) o 24 ->
garr8 SEGS (mrestrict (w_H W) memc) o (cls_bytes OB) ->
cls_write B STK sp0 FP ly S lyc Sc own o 24 ->
o + 24 <= ly_stk_lo lyc \/ ly_stk_hi lyc <= o ->
(o + 24 <= u \/ u + 6 <= o) ->
(50 <= len -> o + 24 <= f \/ f + 50 <= o) ->
SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_disco_classify) regs memc mdc)
(tcls_post B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs 0 o len FB U OB None).

Theorem pb_reac_disco_classify : treac_disco_classify_spec.
Proof.
unfold treac_disco_classify_spec.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f len u o FB U OB
HJ HROD Hra Hra4 Hgp Htp H10 H11 H12 H13 Hch Hal Hstk Hsp Htop Hdep Hlen LFB LU LOB HF HUr HUs HUg Ho Ho4 HOr HOg HOw HOst HOU HOF.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env (@pa_val _ lib_both3_0_listing PI) A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi (fx := fq) SEGS (@pa_val _ lib_both3_0_listing PI) E (mkSS AF_both3_reac_disco_classify sr_atoms [] None (mkFacts [] [] []))
(restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_both3_reac_disco_classify)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. subst E.
apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
clear HE.
unfold cfg_at.
eapply (SRr_run_pi_AJ_call (fx := fq) B LAWS W FUEL E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS);
[vm_compute; reflexivity | exact HJ | intros a (r & Hr & _); destruct Hr |].
intros ms' mat' HS' HJ' HFr _ _.
assert (Em : ms_mem ms' = memc) by (apply functional_extensionality; intros x; apply HFr; intros (r & Hr & _); destruct Hr).
pose proof (regs_kept_of_st_ok SEGS E _ _ regs [] [1; 2; 3; 4; 8]%bv HS' HAE ltac:(vm_compute; reflexivity)) as RK.
pose proof (aregs_preserved_of_st_ok SEGS (w_H W) E _ ms' regs [] HS' HAE ltac:(vm_compute; reflexivity)) as HPR.
cbn [ms_regs restrict] in RK.
pose proof (RK 1%bv ltac:(cbn; tauto)) as R1. pose proof (RK 2%bv ltac:(cbn; tauto)) as R2.
pose proof (RK 3%bv ltac:(cbn; tauto)) as R3. pose proof (RK 4%bv ltac:(cbn; tauto)) as R4.
pose proof (RK 8%bv ltac:(cbn; tauto)) as R8. clear RK.
prreg HS' (10%bv : bv 5) Ga0. prreg HS' (11%bv : bv 5) Ga1. prreg HS' (12%bv : bv 5) Ga2.
prreg HS' (13%bv : bv 5) Ga3. prreg HS' (14%bv : bv 5) Ga4.
rewrite (proj1 HAE 10%nat ltac:(lia)), (ew_Ereg_nat regs [] 10 10%bv eq_refl) in Ga1.
rewrite (proj1 HAE 11%nat ltac:(lia)), (ew_Ereg_nat regs [] 11 11%bv eq_refl) in Ga2.
rewrite (proj1 HAE 12%nat ltac:(lia)), (ew_Ereg_nat regs [] 12 12%bv eq_refl) in Ga3.
rewrite (proj1 HAE 13%nat ltac:(lia)), (ew_Ereg_nat regs [] 13 13%bv eq_refl) in Ga4.
assert (Usp : spZ (ms_regs ms') = spZ regs) by (unfold spZ; rewrite R2; reflexivity).
assert (Us0 : s0Z (ms_regs ms') = s0Z regs) by (unfold s0Z; rewrite R8; reflexivity).
assert (Ura : raZ (ms_regs ms') = raZ regs) by (unfold raZ; rewrite R1; reflexivity).
assert (Hsig : pa_sigma AS_classify_core = BASE + AF_both3_classify_core)
by (apply pa_xcalls; cbn [In both3_xcalls]; repeat (first [left; reflexivity | right])).
pmkst HS'. rewrite Em, Hsig. rewrite Em in HJ'.
eapply SRr_mono.
{ unfold tclassify_core_spec, tcls_entry in TCLS.
apply (TCLS fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc _ k (ms_regs ms') ch 0 f len u o FB U OB None HJ' HROD);
rewrite ?R1, ?R3, ?R4, ?Ga0, ?Ga1, ?Ga2, ?Ga3, ?Ga4, ?Usp, ?Us0, ?Ura; first [assumption | reflexivity | exact I]. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hc & Hfxr & Hfxc & HJ2 & HP2 & HPost).
exists fx', ly2, S2, regs2, mem2, md2. rewrite R1, Usp in *.
split; [exact Hc|]. split; [exact Hfxr|]. split; [exact Hfxc|].
split; [exact HJ2|]. split; [exact (aregs_preserved_trans _ _ _ HPR HP2) | exact HPost].
Qed.

End h.
End f.
End d.
