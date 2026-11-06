From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YP0b YP0a YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0d YP0c YI0w YI0z YI12 YC4a YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YF0l YF0m YCej YCeg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYSites.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma dy_text : @pa_val _ lib_both3_0_listing PB_tfib A_TEXT = tfib_B0.
Proof. reflexivity. Qed.

Lemma dy_duniv_of_eqs : forall B : asyms,
  as_code B = Tfib_code -> as_universe B = Tfib_universe ->
  forall t, In t (d_sites B) -> In t (as_universe B).
Proof.
  intros B Hcode Huniv t Ht. rewrite Huniv. apply memZL_In.
  refine (allb_In (fun u => memZL u Tfib_universe) (d_sites B) t _ Ht).
  cbv [d_sites]. rewrite Hcode, dy_text. vm_compute. reflexivity.
Qed.

Lemma dy_duniv_syms : forall B : asyms, TfibSyms B -> as_universe B = Tfib_universe ->
  forall t, In t (d_sites B) -> In t (as_universe B).
Proof. intros B HB. exact (dy_duniv_of_eqs B (ts_code B HB)). Qed.

Theorem dy_duniv_lib : forall B : asyms, TfibLib B ->
  forall t, In t (d_sites B) -> In t (as_universe B).
Proof. intros B TL. exact (dy_duniv_of_eqs B (tl_code B TL) (tl_universe B TL)). Qed.

End a.
