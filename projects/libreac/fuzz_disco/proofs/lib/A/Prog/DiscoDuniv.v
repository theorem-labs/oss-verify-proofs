From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YM05 YG00 YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AF0l AF0m ACej ACeg AD2l.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable DiscoSyms DiscoList DiscoAddr DiscoPa DiscoImg DiscoSites.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma de_text : @pa_val _ disco_listing PB_disco A_TEXT = disco_text.
Proof. reflexivity. Qed.

Lemma de_duniv_of_eqs : forall B : asyms,
  as_code B = Tfib_code -> as_universe B = Tfib_universe ->
  forall t, In t (d_sites B) -> In t (as_universe B).
Proof.
  intros B Hcode Huniv t Ht. rewrite Huniv. apply memZL_In.
  refine (allb_In (fun u => memZL u Tfib_universe) (d_sites B) t _ Ht).
  cbv [d_sites]. rewrite Hcode, de_text. vm_compute. reflexivity.
Qed.

Lemma de_duniv_syms : forall B : asyms, TfibSyms B -> as_universe B = Tfib_universe ->
  forall t, In t (d_sites B) -> In t (as_universe B).
Proof. intros B HB. exact (de_duniv_of_eqs B (ts_code B HB)). Qed.

Lemma de_duniv_lib : forall B : asyms, TfibLib B ->
  forall t, In t (d_sites B) -> In t (as_universe B).
Proof. intros B TL. exact (de_duniv_of_eqs B (tl_code B TL) (tl_universe B TL)). Qed.

Theorem de_duniv : forall t, In t (d_sites TfibB) -> In t (as_universe TfibB).
Proof. exact (de_duniv_of_eqs TfibB eq_refl eq_refl). Qed.

End a.
