From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YM05 YG00 YG0d YG0q YB1v YF0m YD2l.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI0w YI0z YI12 YC4a YCbj YE2s.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Lemma disco_y_bcmp_tfib_sigma : tfib_sigma AS___interceptor_trampoline_bcmp = 0x42a50.
Proof. vm_compute. reflexivity. Qed.
Section d. Context {rc : YM05.RunCeil}.
Lemma disco_y_bcmp_sigma : @pa_sigma _ lib_both3_0_listing PB_tfib AS___interceptor_trampoline_bcmp = 0x42a50.
Proof. exact disco_y_bcmp_tfib_sigma. Qed.
Theorem disco_y_abcmp : forall B, AR_laws tfibsegs B -> TfibSyms B ->
  forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) tfibsegs B
    (@pa_sigma _ lib_both3_0_listing PB_tfib AS___interceptor_trampoline_bcmp).
Proof.
intros B LAWS HB fq. rewrite disco_y_bcmp_sigma. exact (bcmp_icpt_contract (fx := fq) B LAWS HB).
Qed.
Corollary disco_y_abcmp_tfib : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) (@pa_segs _ lib_both3_0_listing PB_tfib) TfibB
    (@pa_sigma _ lib_both3_0_listing PB_tfib AS___interceptor_trampoline_bcmp).
Proof. exact (disco_y_abcmp TfibB (AR_laws_ok tfibsegs TfibB) TfibB_syms). Qed.
End d.
