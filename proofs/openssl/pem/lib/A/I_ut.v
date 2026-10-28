(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint img_bytes_b (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' => match seg_rom asegs (wa A) with
                | Some b' => bv_eqb b b' && img_bytes_b (A + 1) bs'
                | None => false
                end
  end.

Lemma ut_bytes : forall (m : mem) bs A, img_untouched m -> img_bytes_b A bs = true ->
  IMG_UT_LO <= A -> A + Z.of_nat (length bs) <= IMG_UT_HI -> bytes_at asegs m A bs.
Proof.
  intros m bs A U HB LO HI.
  assert (R : 0 <= A /\ A + Z.of_nat (length bs) <= 2^64) by (unfold IMG_UT_LO, IMG_UT_HI in *; lia).
  split; [lia|]. split; [lia|].
  revert A HB LO HI R. induction bs as [|b bs IH]; intros A HB LO HI R i Hi; [cbn in Hi; lia|].
  cbn [img_bytes_b] in HB. destruct (seg_rom asegs (wa A)) as [b'|] eqn:E; [| discriminate].
  apply andb_prop in HB as [H1 H2]. unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b'.
  cbn [length] in HI, Hi, R. rewrite Nat2Z.inj_succ in HI, R.
  destruct i as [|i].
  - cbn [nth_error]. rewrite Z.add_0_r. unfold mrd. rewrite (U (wa A)); [exact E|].
    unfold wa. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
  - cbn [nth_error]. replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia.
    apply (IH (A + 1) H2); lia.
Qed.

Lemma ut_cells : forall (m : mem) A bs, img_untouched m -> img_bytes_b A bs = true ->
  IMG_UT_LO <= A -> A + Z.of_nat (length bs) <= IMG_UT_HI -> ro_cells asegs m A [CB (length bs) bs].
Proof.
  intros m A bs U HB LO HI. split; [cbn; split; [reflexivity| exact I]|].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. exact (ut_bytes m bs A U HB LO HI).
Qed.

(* [comment removed for export] *)
Lemma ut_ro_cells : forall (m : mem) A cs, img_untouched m -> cells_wf cs -> img_bytes_b A (cells_bytes cs) = true ->
  IMG_UT_LO <= A -> A + Z.of_nat (length (cells_bytes cs)) <= IMG_UT_HI -> ro_cells asegs m A cs.
Proof. intros m A cs U WF HB LO HI. split; [exact WF| exact (ut_bytes m _ A U HB LO HI)]. Qed.

(* [comment removed for export] *)
Definition ut_fp (W : list (Z * Z)) : Prop := forall x, IMG_UT_LO <= x < IMG_UT_HI -> outside W x.

Lemma ut_munch : forall W (m0 m : mem), img_untouched m0 -> munch W m0 m -> ut_fp W -> img_untouched m.
Proof. intros W m0 m U MU HW a Ha. rewrite (MU a (HW _ Ha)). exact (U a Ha). Qed.

Lemma ut_agree : forall (m0 m : mem), img_untouched m0 -> (forall a : word, IMG_UT_LO <= bv_unsigned a < IMG_UT_HI -> m a = m0 a) -> img_untouched m.
Proof. intros m0 m U AG a Ha. rewrite (AG a Ha). exact (U a Ha). Qed.

Lemma ut_fp_nil : ut_fp [].
Proof. intros x _. exact I. Qed.
Lemma ut_fp_cons : forall lo hi W, (hi <= IMG_UT_LO \/ IMG_UT_HI <= lo) -> ut_fp W -> ut_fp ((lo, hi) :: W).
Proof. intros lo hi W H HW x Hx. cbn [outside]. split; [lia| exact (HW x Hx)]. Qed.
Lemma ut_fp_app : forall W1 W2, ut_fp W1 -> ut_fp W2 -> ut_fp (W1 ++ W2).
Proof.
  intros W1 W2 H1 H2 x Hx. specialize (H1 x Hx). specialize (H2 x Hx). clear Hx.
  induction W1 as [|[lo hi] W1 IH]; [exact H2|]. cbn [app outside] in *. destruct H1 as [A B]. split; [exact A| exact (IH B)].
Qed.

(* [comment removed for export] *)
Ltac ut_fp_lia :=
  repeat first [ apply ut_fp_nil | apply ut_fp_app | apply ut_fp_cons; [unfold IMG_UT_LO, IMG_UT_HI in *; lia|] ].

(* [comment removed for export] *)
Ltac ut_now m :=
  lazymatch goal with
  | U : img_untouched m |- _ => constr:(U)
  | U : img_untouched ?m0, MU : munch ?W ?m0 m, HW : ut_fp ?W |- _ => constr:(ut_munch W m0 m U MU HW)
  end.

(* [comment removed for export] *)
Ltac solve_load_ut :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
      let E := addr_expr a in
      let Ez := zlit E in
      let U := ut_now m in
      let obs := eval vm_compute in (image_bytes segs Ez n) in
      lazymatch obs with
      | Some ?bs =>
          let RO := fresh "ROut" in
          assert (RO : ro_cells segs m Ez [CB n bs])
            by (apply (ut_cells m Ez bs U); [vm_compute; reflexivity | unfold IMG_UT_LO; lia | unfold IMG_UT_HI; cbn; lia]);
          rewrite (ro_cells_read_at segs m Ez [CB n bs] 0%nat (CB n bs) n a RO)
            by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          clear RO; load_post
      | None => fail "no image bytes at" Ez
      end
  end.
Ltac solve_load ::= first [ solve_load_base | solve_load_image | solve_load_ut ].
