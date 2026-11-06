(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface D_libiface Fh_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition zz_inb (r : Z * Z) (l : list (Z * Z)) : bool := existsb (fun q => (fst q =? fst r) && (snd q =? snd r)) l.
Lemma zz_inb_sound : forall r l, zz_inb r l = true -> In r l.
Proof.
  intros [a n] l H. unfold zz_inb in H. apply existsb_exists in H as ([a' n'] & Hin & E). cbn [fst snd] in E.
  apply andb_true_iff in E as (E1 & E2). apply Z.eqb_eq in E1, E2. subst. exact Hin.
Qed.

Lemma ten_cases : forall i, 0 <= i < 10 -> i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9.
Proof. intros; lia. Qed.

(* [comment removed for export] *)
Lemma hm_name_lit_in : forall i, 0 <= i < 10 -> In (HM_NAME_LIT i, 8) ACC_LITS.
Proof.
  intros i Hi. destruct (ten_cases i Hi) as [E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]; subst i;
    apply zz_inb_sound; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hm_name_lit_ro : forall i, 0 <= i < 10 -> ro_bytes asegs (HM_NAME_LIT i) (hm_name (Z.to_nat i)).
Proof.
  intros i Hi. destruct (ten_cases i Hi) as [E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]; subst i;
    apply ro_bytes_b_sound; vm_compute; reflexivity.
Qed.

Lemma hm_name_shape : forall i, 0 <= i < 10 ->
  exists str, hm_name (Z.to_nat i) = str ++ [Z_to_bv 8 0] /\ length str = 7%nat /\ ~ In (Z_to_bv 8 0) str.
Proof.
  intros i Hi. destruct (ten_cases i Hi) as [E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]; subst i;
    (lazymatch goal with |- exists str, hm_name ?k = _ /\ _ /\ _ => exists (firstn 7 (hm_name k)) end;
     split; [vm_compute; reflexivity| split; [vm_compute; reflexivity|]];
     intros HIn; vm_compute in HIn;
     repeat (destruct HIn as [HIn|HIn]; [apply (f_equal bv_unsigned) in HIn; vm_compute in HIn; discriminate HIn|]); exact HIn).
Qed.

Lemma hm_name_lit_range : forall i, 0 <= i < 10 -> 0x10000 <= HM_NAME_LIT i /\ HM_NAME_LIT i + 8 <= SEGTOP_A /\ HM_NAME_LIT i mod 8 = 0.
Proof.
  intros i Hi. unfold HM_NAME_LIT, SEGTOP_A. repeat split; lia.
Qed.

Section FhStatics.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma rng_class_image : forall (Σ : rts RT) s n, 0x10000 <= s -> s + n <= SEGTOP_A -> rng_class RT Σ s n.
Proof. intros Σ s n H1 H2. right; right; right. split; assumption. Qed.

Lemma acc_lit : forall (Σ : rts RT) m a n, ART RT Σ m -> In (a, n) ACC_LITS -> acc asegs m a n.
Proof.
  intros Σ m a n A HIn. pose proof (af_acc_lits RT AF Σ m A) as F.
  exact (proj1 (Forall_forall _ _) F (a, n) HIn).
Qed.

Lemma fh_acc_namelits : forall (Σ : rts RT) m i, ART RT Σ m -> 0 <= i < 10 -> acc asegs m (HM_NAME_LIT i) 8.
Proof. intros Σ m i A Hi. apply (acc_lit Σ m _ _ A). apply hm_name_lit_in; exact Hi. Qed.

Lemma fh_class_namelits : forall (Σ : rts RT) i, 0 <= i < 10 -> rng_class RT Σ (HM_NAME_LIT i) 8.
Proof. intros Σ i Hi. destruct (hm_name_lit_range i Hi) as (H1 & H2 & _). apply rng_class_image; assumption. Qed.

(* [comment removed for export] *)
Lemma fh_acc_selnames : forall (Σ : rts RT) m, ART RT Σ m -> acc asegs m SEL_NAMES_AT 800.
Proof.
  intros Σ m A. apply (af_acc_static RT AF Σ m _ _ A); [unfold SEL_NAMES_AT, LIB_SEL_AT; lia|].
  intros i Hi. unfold SEL_NAMES_AT, LIB_SEL_AT. split; [split|lia].
  - exists 0xe83f0, 0xecf58. split; [cbn; tauto| lia].
  - intros (l & h & HIn & Hr). cbn in HIn.
    repeat (destruct HIn as [HIn|HIn]; [inversion HIn; subst l h; lia|]). exact HIn.
Qed.

Lemma fh_class_selnames : forall (Σ : rts RT) k n, 0 <= k < 10 -> 0 <= n <= 80 -> rng_class RT Σ (SEL_NAMES_AT + 80 * k) n.
Proof. intros Σ k n Hk Hn. apply rng_class_image; unfold SEL_NAMES_AT, LIB_SEL_AT, SEGTOP_A; lia. Qed.

End FhStatics.
