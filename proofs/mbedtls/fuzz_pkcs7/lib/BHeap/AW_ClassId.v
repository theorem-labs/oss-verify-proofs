(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Ltac2 gd_tbl_AW_ClassId () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Stdlib.ZArith.BinInt.Z.lxor"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.shiftl"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.b2z"; "Stdlib.ZArith.BinInt.Z.ltb"].

Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Lemma Z_land_le_l : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof.
  intros a b Ha Hb.
  rewrite <- (Z2N.id a) at 1 2 by lia. rewrite <- (Z2N.id b) by lia.
  rewrite <- N2Z.inj_land. pose proof (N.land_le_l (Z.to_N a) (Z.to_N b)). lia.
Qed.
#[using="Type"] Lemma Z_land_le_r : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= b.
Proof. intros. rewrite Z.land_comm. apply Z_land_le_l; assumption. Qed.
#[using="Type"] Lemma Z_shiftr_le : forall a n, 0 <= a -> 0 <= n -> Z.shiftr a n <= a.
Proof.
  intros. rewrite Z.shiftr_div_pow2 by assumption.
  apply Z.div_le_upper_bound. { apply Z.pow_pos_nonneg; lia. }
  pose proof (Z.pow_pos_nonneg 2 n). nia.
Qed.

Definition classid_code (x : Z) : Z := ltac2:(CDefT.buildp (gd_tbl_AW_ClassId ()) "Ze1,$0.(1.O1.(2.O1.+1.))Ze2,$0.(1.R1.(2.R1.+2.))Ze3,$0.(1.R1.(2.R1.+4.))Ze4,$0.(1.R1.(2.R1.+8.))Ze5,$0.(1.R1.(2.R1.+10.))Ze6,$0.(1.R1.(2.R1.+20.))Zen,$0.(3.R1.+????????????????.)Zev,$0.(4.R1.(5.(2.R1.+1.)+5555555555555555.))Zer,$0.(6.(5.R1.+3333333333333333.)(5.(2.R1.+2.)+3333333333333333.))Zet,$0.(6.R1.(2.R1.+4.))Zlz,$0.(2.(7.(8.(5.R1.+?0?0?0?0?0?0?0?.)+101010101010101.)+10000000000000000.)+38.)(6.(6.(1.(3.(7.(9.R1.+1.)+10000000000000000.)+7>.)(5.(2.O1.(7.(7.(:.&20.(4.+3>.R1.))+10000000000000000.)+40.))+1.))(;.(<.=(5.O1.(3.(7.(:.&20.(9.+????????????????.(7.(7.(:.&20.(4.+3>.R1.))+10000000000000000.)+20.)))+10000000000000000.)+????????????????.)))))-2.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
Fixpoint zall (P : Z -> bool) (lo : Z) (n : nat) : bool :=
  match n with O => true | S k => P lo && zall P (lo + 1) k end.
#[using="Type"] Lemma zall_spec : forall P n lo, zall P lo n = true -> forall x, lo <= x < lo + Z.of_nat n -> P x = true.
Proof.
  induction n as [|n IH]; intros lo H x Hx; [lia|].
  cbn [zall] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec x lo) as [->|]; [exact H1|].
  apply (IH (lo + 1) H2). lia.
Qed.

#[using="Type"] Lemma classid_code_ok : forall x, 512 < x <= 0x10000 -> classid_code x = class_of x.
Proof.
  intros x Hx. apply Z.eqb_eq.
  apply (zall_spec (fun y => classid_code y =? class_of y) (Z.to_nat 65024) 513); [| lia].
  first [lazymatch goal with |- ?g0 => tryif has_evar g0 then fail else (let g := eval hnf in g0 in lazymatch g with _ = ?r => vm_cast_no_check (@eq_refl _ r) end) end | vm_compute; reflexivity]. (* [comment removed for export] *)
Qed.

#[using="Type"] Lemma class_of_small : forall x, 1 <= x <= 512 -> class_of x = (x + 31) / 32.
Proof. intros x Hx. unfold class_of. replace (x <=? 512) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

#[using="Type"] Lemma class_of_range : forall x, 1 <= x <= 0x10000 -> 1 <= class_of x <= 30.
Proof.
  intros x Hx. destruct (Z.le_gt_cases x 512).
  - rewrite class_of_small by lia. split. { apply Z.div_le_lower_bound; lia. } apply Z.div_le_upper_bound; lia.
  - pose proof (zall_spec (fun y => (1 <=? class_of y) && (class_of y <=? 30)) (Z.to_nat 65024) 513
                  ltac:(first [lazymatch goal with |- ?g0 => tryif has_evar g0 then fail else (let g := eval hnf in g0 in lazymatch g with _ = ?r => vm_cast_no_check (@eq_refl _ r) end) end | vm_compute; reflexivity]) x ltac:(lia)) as E.
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

End ARUN_1.
