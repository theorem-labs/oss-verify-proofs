(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XSeqExec XStepTac XStoreOk.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bvhfbbv_unsigned37Corelib4Init9Datatypeskf6lengthkf6option46Stdlib6ZArith6BinInt1Zn93addn92len96of_natkf4Somekf4list37Corelib4Init5Logicr33andr32eq37Corelib5Lists7ListDeft23nth79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XCatExec~~~~~~uf6wbytesn92ltn93pown93subn96to_nathf7Z_to_bvr32or" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wbytes_inside : ltac2:(zQ "h30!h9!jc!k1!m7!n0!p1!p7!pc!q5!qc!s7!sd!u9!hid!hj6!hjb!hk1!hk7!hl0>2bs@1$9@1$1@1$0#8>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>1a@1$1@1$0#k0>1x@1$1@1$0#k0>0@2$6@2$5@2$2@1$0#k0^2@1$7@2$3@1$1@1$0#8^4@2$f+2+k0>0@2$a@2$6@2$2@1$0#k0^3@2$2@1$0#k0^2@2$e@2$2@1$0#k0^2@2$5@2$2@1$0#k0^3@1$7@2$3@1$1@1$0#8^5@3$b@1$4@1$1@1$0#8@4$d^5^4^6^3@2$8@1$1@1$0#8@4$c@1$1@1$0#8@1$h1@2$h0@2$2@1$0#k0^3@2$2@1$0#k0^4^6@2$h2@1$0#8Z").
Proof.
  induction bs as [|b rest IH]; intros m a x Hnw Hx; [cbn in Hx; lia|].
  cbn [wbytes length] in *.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  - assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Z.sub_diag. cbn [Z.to_nat nth].
    destruct rest as [|b' rest'].
    + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
    + cbn [length] in Hnw. rewrite wbytes_below.
      * rewrite bv_eqb_refl. reflexivity.
      * rewrite u_add1 by lia. cbn [length]. lia.
      * rewrite u_add1 by lia. lia.
  - assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
      by (apply u_add1; lia).
    rewrite (IH _ (a + 1)%bv) by (rewrite Hu1; lia).
    rewrite Hu1.
    replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
      with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
    reflexivity.
Qed.

Lemma wbytes_outside : ltac2:(zQ "e0!h9!jc!k1!m7!n0!p1!p7!pc!qc!sd!hla!hid!hj6!hjb>2bs@1$8@1$1@1$0#8>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>1a@1$1@1$0#k0>1x@1$1@1$0#k0>0@2$6@2$5@2$2@1$0#k0^2@1$7@2$3@1$1@1$0#8^4@2$d+2+k0>0@2$a@2$c@2$2@1$0#k0^2@2$2@1$0#k0^3@2$6@2$5@2$2@1$0#k0^3@1$7@2$3@1$1@1$0#8^5@2$2@1$0#k0^2@3$9@1$4@1$1@1$0#8@4$b^5^4^6^3@1^5^3").
Proof.
  intros bs m a x Hnw [Hlt|Hge].
  - apply wbytes_below; assumption.
  - apply wbytes_above; assumption.
Qed.

(* [comment removed for export] *)
