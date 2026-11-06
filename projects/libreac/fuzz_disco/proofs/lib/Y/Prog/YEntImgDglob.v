From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG00 YG0f YF0m YM05 YCbj YRoClose.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YD2l.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntryInv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition dglob_rc0 : RunCeil :=
  {| alloc_ceiling := 140735332483072; alloc_ceiling_val := ltac:(split; [lia | reflexivity]) |}.

Lemma tfib_dglob_cells_b :
  forallb (fun c => existsb (is_shv (fst c) (snd c)) Tfib_const_shadow) (@dglob_cells dglob_rc0 PB_tfib) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tfib_dglob_ranges_b :
  forallb (fun r => existsb (fun z => (fst z <=? fst r) && (fst r + snd r <=? fst z + snd z))%bool Tfib_zero_shadow)
    (@dglob_ranges dglob_rc0 PB_tfib) = true.
Proof. vm_compute. reflexivity. Qed.

Section d. Context {rc : RunCeil}.

Lemma tfib_dglob_const : @dglob_const rc PB_tfib YD2l.TfibB.
Proof.
intros ly c Hc. change (In c (@dglob_cells dglob_rc0 PB_tfib)) in Hc.
pose proof (proj1 (forallb_forall _ _) tfib_dglob_cells_b c Hc) as Hb. cbv beta in Hb.
apply existsb_exists in Hb as (x & Hx & Hv). apply is_shv_eq in Hv. subst x.
cbn [as_const YD2l.TfibB]. unfold Tfib_const. apply in_or_app. right. apply in_or_app. right. exact Hx.
Qed.

Lemma tfib_dglob_zshadow : @dglob_zshadow rc PB_tfib YD2l.TfibB.
Proof.
intros r Hr. change (In r (@dglob_ranges dglob_rc0 PB_tfib)) in Hr.
pose proof (proj1 (forallb_forall _ _) tfib_dglob_ranges_b r Hr) as Hb. cbv beta in Hb.
apply existsb_exists in Hb as (z & Hz & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
exists z. split; [exact Hz | split; assumption].
Qed.

End d.
