(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_Footprint () : Init.string Init.list := ["region"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "rg_disj"; "covers"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Numbers.BinNums.Z"; "heap_rg"; "Corelib.Init.Logic.and"; "Corelib.Lists.ListDef.Forall"; "rg_wf"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.nth"; "Rg"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record region : Type := Rg { rg_lo : Z; rg_hi : Z }.

Definition rg_wf (r : region) : Prop :=
  0 <= rg_lo r /\ rg_lo r <= rg_hi r /\ rg_hi r <= 2 ^ 64.

(* [comment removed for export] *)
Definition covers (r : region) (a : word) (n : nat) : Prop :=
  rg_lo r <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= rg_hi r.

Definition rg_disj (r1 r2 : region) : Prop :=
  rg_hi r1 <= rg_lo r2 \/ rg_hi r2 <= rg_lo r1.

Lemma rg_disj_sym : forall r1 r2, rg_disj r1 r2 -> rg_disj r2 r1.
Proof. intros r1 r2 [H|H]; [right|left]; exact H. Qed.

(* [comment removed for export] *)
Lemma covers_mono : forall r r' a n,
  covers r a n -> rg_lo r' <= rg_lo r -> rg_hi r <= rg_hi r' -> covers r' a n.
Proof. intros r r' a n [H1 H2] Hl Hh. split; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma covers_nowrap : forall r a n,
  rg_wf r -> covers r a n -> bv_unsigned a + Z.of_nat n <= 2 ^ 64.
Proof. intros r a n (_ & _ & Hhi) (_ & H). lia. Qed.

(* [comment removed for export] *)
Lemma covers_disj : ltac2:(CDefT.buildp (gd_tbl_Footprint ()) "Pr1,$0.Pr2,$0.Pa1,(1.&40.)Pn1,$2.Pa2,(1.&40.)Pn2,$2.P,(3.R6.R5.)P,(4.R7.R5.R4.)P,(4.R7.R4.R3.)(5.(6.(7.(8.&40.R7.)(9.R6.))(8.&40.R5.))(6.(7.(8.&40.R5.)(9.R4.))(8.&40.R7.)))")
(* [comment removed for export] *).
Proof. intros r1 r2 a1 n1 a2 n2 [H|H] [H1 H2] [H3 H4]; [left|right]; lia. Qed.

(* [comment removed for export] *)
Lemma covers_same_disj : ltac2:(CDefT.buildp (gd_tbl_Footprint ()) "Pr,$0.Pa1,(1.&40.)Pn1,$2.Pa2,(1.&40.)Pn2,$2.P,(4.R5.R4.R3.)P,(4.R6.R3.R2.)P,(5.(6.(7.(8.&40.R6.)(9.R5.))(8.&40.R4.))(6.(7.(8.&40.R4.)(9.R3.))(8.&40.R6.)))(5.(6.(7.(8.&40.R7.)(9.R6.))(8.&40.R5.))(6.(7.(8.&40.R5.)(9.R4.))(8.&40.R7.)))")
(* [comment removed for export] *).
Proof. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stack_rg (sp : word) (below above : Z) : region :=
  Rg (bv_unsigned sp - below) (bv_unsigned sp + above).

(* [comment removed for export] *)
Definition seg_rg (lo hi : Z) : region := Rg lo hi.

(* [comment removed for export] *)
Definition heap_rg (base : word) (cur : Z) : region :=
  Rg (bv_unsigned base) (bv_unsigned base + cur).

Lemma heap_rg_bump : ltac2:(CDefT.buildp (gd_tbl_Footprint ()) "Pbase,(1.&40.)Pcur,$:.Pcur',$:.Pa,(1.&40.)Pn,$2.P,(6.R4.R3.)P,(4.(;.R6.R5.)R3.R2.)(4.(;.R7.R5.)R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros base cur cur' a n Hle H.
  apply (covers_mono (heap_rg base cur)); [exact H | cbn; lia | cbn; lia].
Qed.

(* [comment removed for export] *)
Definition layout_wf (rs : list region) : Prop := ltac2:(CDefT.buildp (gd_tbl_Footprint ()) "(<.(=.$0.$>.O1.)Pi,$2.Pj,$2.P,(?.R2.R1.)P,(?.R2.(10.$0.O1.))(3.(11.$0.R4.O1.(12.==))(11.$0.R3.O1.(12.==))))")
(* [comment removed for export] *).
