(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc6modulohc3lorhc6shiftrhc4lxorhc4landhc3subhc3addhc3mul04Npos35stdpp9bitvectorbdefinitionsn28bv_swraphc6shiftlhc3b2zhc3ltb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7CidBits~~~~~~qf3cb1qf4cb10qf4cb11qf4cb12qf4cb13qf4cb14qf4cb15qf4cb16qf3cb2qf3cb3qf3cb4qf3cb5qf3cb6qf3cb7qf3cb8qf3cb937Corelib4Init9Datatypeshl34boolqfcforall_rangehc6to_nathl34true37Corelib4Init5Logichp32eqhl33nathp33andhc2lehc2lthc6of_natqfdforall_rangeZqf3cf1qf3cf2qf3cf3qf3cf4qf3cf5qf3cf6qf3cf7qf3cf8qf3cf9qf4cf10qf4cf11qf4cf12qf4cf13qf4cf14qf4cf15qf4cf16qf7cidfast69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~ikf8class_idhc3eqbqf7cidbitshl34andbhc3lebikfaclass_size" s.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition cb1 : ltac2:(zQ "10!h9>4size$0$0") := ltac2:(zQ "40!j4!h9!jd!k3\4size$1@2$0@2$2^1@2$0@2$3^1+1+hggggggggggggggg0+hggggggggggggggg0").
Definition cb2 : ltac2:(zQ "10!h9>2e1$0$0") := ltac2:(zQ "40!j4!h9!jd!k3\2e1$1@2$0@2$2^1@2$0@2$3^1+2+hggggggggggggggg0+hggggggggggggggg0").
Definition cb3 : ltac2:(zQ "10!h9>2e2$0$0") := ltac2:(zQ "40!j4!h9!jd!k3\2e2$1@2$0@2$2^1@2$0@2$3^1+4+hggggggggggggggg0+hggggggggggggggg0").
Definition cb4 : ltac2:(zQ "10!h9>2e3$0$0") := ltac2:(zQ "40!j4!h9!jd!k3\2e3$1@2$0@2$2^1@2$0@2$3^1+8+hggggggggggggggg0+hggggggggggggggg0").
Definition cb5 : ltac2:(zQ "10!h9>2e4$0$0") := ltac2:(zQ "40!j4!h9!jd!k3\2e4$1@2$0@2$2^1@2$0@2$3^1+h0+hggggggggggggggg0+hggggggggggggggg0").
Definition cb6 : ltac2:(zQ "10!h9>2e5$0$0") := ltac2:(zQ "40!j4!h9!jd!k3\2e5$1@2$0@2$2^1@2$0@2$3^1+i0+hggggggggggggggg0+hggggggggggggggg0").
Definition cb7 : ltac2:(zQ "10!h9>2e6$0$0") := ltac2:(zQ "30!h9!kc!j4\2e6$0@2$2@2$1^1+vvvvvvvvvvvvvvvf+hggggggggggggggg0").
Definition cb8 : ltac2:(zQ "10!h9>2e7$0$0") := ltac2:(zQ "50!j4!h9!l3!k3!la\2e7$1@2$0@2$4^1@2$0@2$2@2$0@2$3^1+1+hggggggggggggggg0+lllllllllllllll5+hggggggggggggggg0+hggggggggggggggg0").
Definition cb9 : ltac2:(zQ "10!h9>2e8$0$0") := ltac2:(zQ "50!l3!j4!h9!m0!k3\2e8$2@2$1@2$3@2$0^1+jjjjjjjjjjjjjjj3@2$0@2$1@2$4^1+2+hggggggggggggggg0+jjjjjjjjjjjjjjj3+hggggggggggggggg0").
Definition cb10 : ltac2:(zQ "10!h9>2e9$0$0") := ltac2:(zQ "40!h9!m0!j4!k3\2e9$0@2$2@2$1^1@2$3^1+4+hggggggggggggggg0").
Definition cb11 : ltac2:(zQ "10!h9>3e10$0$0") := ltac2:(zQ "50!j4!h9!l3!m6!k3\3e10$1@2$0@2$4@2$0@2$3@2$0@2$2^1+vgvgvgvgvgvgvgf+hggggggggggggggg0+hghghghghghghg1+hggggggggggggggg0+j8+hggggggggggggggg0").
Definition cb12 : ltac2:(zQ "10!h9>3e11$0$0") := ltac2:(zQ "50!mc!h9!j4!la!of\3e11$1@2$2@2$4@1$0#i0@2$3+je^1+hggggggggggggggg0").
Definition cb13 : ltac2:(zQ "10!h9>4size$0>3e12$0$0") := ltac2:(zQ "30!h9!j4!k3\4size$0\3e12$0@2$1@2$2^2@2$1^1+k0+hggggggggggggggg0").
Definition cb14 : ltac2:(zQ "10!h9>3e12$0$0") := ltac2:(zQ "50!j4!mc!h9!pa!of\3e12$2@2$0@2$4@1$1#i0@2$3+vvvvvvvvvvvvvvvf@2$0^1+i0+hggggggggggggggg0").
Definition cb15 : ltac2:(zQ "10!h9>4size$0>3e14$0$0") := ltac2:(zQ "40!h9!j4!l3!kc\4size$0\3e14$0@2$1@2$2^2@2$1@2$3^1+vvvvvvvvvvvvvvvf+hggggggggggggggg0+hggggggggggggggg0").
Definition cb16 : ltac2:(zQ "10!h9>3e11$0>3e13$0>3e15$0$0") := ltac2:(zQ "90!j4!h9!m0!q3!l3!jd!q9!kc!pa\3e11$1\3e13$1\3e15$1@2$0@2$2@2$2@2$5@2$0@2$7@2$0@2$8^3+1+hggggggggggggggg0+ne+hggggggggggggggg0@2$0@2$4^2+1+hggggggggggggggg0@2$0@1$3@2$6@2$0Z+hggggggggggggggg0^1+hggggggggggggggg0-2+hggggggggggggggg0").

Definition cidbits : ltac2:(zQ "10!h9>4size$0$0") := ltac2:(zQ "h10!h9!uc!v2!v9!hg0!hg7!hge!hh5!hhc!hi3!hi9!hif!hj5!hjb!hk1!hk7!hkd\4size$0=2e1$0@1$1^1=2e2$0@1$9^1=2e3$0@1$a^1=2e4$0@1$b^1=2e5$0@1$c^1=2e6$0@1$d^1=2e7$0@1$e^1=2e8$0@1$f^1=2e9$0@1$h0^1=3e10$0@1$2^1=3e11$0@1$3^1=3e12$0@1$4^1=3e13$0@2$5^d^1=3e14$0@1$6^2=3e15$0@2$7^f^1=3e16$0@3$8^5^3^1^1").

(* [comment removed for export] *)
Fixpoint forall_range (f : Z -> bool) (a : Z) (n : nat) : bool :=
  match n with O => true | S k => if f a then forall_range f (a + 1) k else false end.
Definition forall_rangeZ : ltac2:(zQ "20!h9!hmb>1f>0$0$1>1a$0>1n$0$1") := ltac2:(zQ "40!h9!hmb!hn3!ho2\1f>0$0$1\1a$0\1n$0@3$2^3^2@1$3^1").
Lemma forall_range_spec : ltac2:(zQ "b0!hmb!h9!hob!hq7!hqd!hr4!hn3!m0!hrb!hs0!hs5>1f>0$1$0>1n$4>1a$1>1x$1>0@3$3$0@3$6^4^2^3$2>0@2$5@2$8^3^2@2$9^2@2$7^3@1$a^4@3$3$0@1^6^3$2").
Proof.
  intros f n. induction n as [|k IH]; intros a x H Hx; [cbn in Hx; lia|].
  cbn [forall_range] in H. destruct (f a) eqn:E; [|discriminate].
  destruct (Z.eq_dec x a) as [->|NE]; [exact E|]. eapply IH; [exact H|]. lia.
Qed.
Lemma forall_rangeZ_spec : ltac2:(zQ "90!h9!hmb!hob!hq7!hrb!hr4!hse!m0!hs0>1f>0$0$1>1a$0>1n$0>1x$0>0@3$3$1@3$6^4^3^2$2>0@2$4Z^3>0@2$5@2$4^5^3@2$8^3@2$7^5^4@3$3$1@1^7^4$2").
Proof. intros f a n x H Hn Hx. eapply forall_range_spec; [exact H|]. rewrite Z2Nat.id by exact Hn. exact Hx. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition M64 : Z := 18446744073709551615.
Lemma mod64_land : ltac2:(zQ "40!h9!hq7!l3!j4>1x$0@3$1$0@2$3^1+hggggggggggggggg0@2$2^1+vvvvvvvvvvvvvvvf").
Proof. intros x. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by (clear; lia). reflexivity. Qed.
Lemma mod6_land : ltac2:(zQ "40!h9!hq7!l3!j4>1x$0@3$1$0@2$3^1+k0@2$2^1+jf").
Proof. intros x. change 63 with (Z.ones 6). rewrite Z.land_ones by (clear; lia). reflexivity. Qed.
Lemma mod5_land : ltac2:(zQ "40!h9!hq7!l3!j4>1x$0@3$1$0@2$3^1+i0@2$2^1+hf").
Proof. intros x. change 31 with (Z.ones 5). rewrite Z.land_ones by (clear; lia). reflexivity. Qed.
Lemma swrap32_land : ltac2:(zQ "70!h9!hq7!mc!m0!l3!la!of>1z$0@3$1$0@2$6@1$2#i0^1@2$5@2$4@2$3^1+ogggggg0+vvvvvvvf+ogggggg0").
Proof.
  intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  change (4294967296 `div` 2) with 2147483648. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by (clear; lia). reflexivity.
Qed.

Definition cf1 : ltac2:(zQ "10!h9>4size$0$0") := ltac2:(zQ "40!l3!h9!jd!k3\4size$1@2$0@2$2^1@2$0@2$3^1+1+vvvvvvvvvvvvvvvf+vvvvvvvvvvvvvvvf").
Definition cf2 : ltac2:(zQ "10!h9>2e1$0$0") := ltac2:(zQ "40!l3!h9!jd!k3\2e1$1@2$0@2$2^1@2$0@2$3^1+2+vvvvvvvvvvvvvvvf+vvvvvvvvvvvvvvvf").
Definition cf3 : ltac2:(zQ "10!h9>2e2$0$0") := ltac2:(zQ "40!l3!h9!jd!k3\2e2$1@2$0@2$2^1@2$0@2$3^1+4+vvvvvvvvvvvvvvvf+vvvvvvvvvvvvvvvf").
Definition cf4 : ltac2:(zQ "10!h9>2e3$0$0") := ltac2:(zQ "40!l3!h9!jd!k3\2e3$1@2$0@2$2^1@2$0@2$3^1+8+vvvvvvvvvvvvvvvf+vvvvvvvvvvvvvvvf").
Definition cf5 : ltac2:(zQ "10!h9>2e4$0$0") := ltac2:(zQ "40!l3!h9!jd!k3\2e4$1@2$0@2$2^1@2$0@2$3^1+h0+vvvvvvvvvvvvvvvf+vvvvvvvvvvvvvvvf").
Definition cf6 : ltac2:(zQ "10!h9>2e5$0$0") := ltac2:(zQ "40!l3!h9!jd!k3\2e5$1@2$0@2$2^1@2$0@2$3^1+i0+vvvvvvvvvvvvvvvf+vvvvvvvvvvvvvvvf").
Definition cf7 : ltac2:(zQ "10!h9>2e6$0$0") := ltac2:(zQ "30!h9!l3!kc\2e6$0@2$1@2$2^1+vvvvvvvvvvvvvvvf+vvvvvvvvvvvvvvvf").
Definition cf8 : ltac2:(zQ "10!h9>2e7$0$0") := ltac2:(zQ "40!l3!h9!k3!la\2e7$1@2$0@2$3^1@2$0@2$0@2$0@2$2^1+1+vvvvvvvvvvvvvvvf+lllllllllllllll5+vvvvvvvvvvvvvvvf+vvvvvvvvvvvvvvvf").
Definition cf9 : ltac2:(zQ "10!h9>2e8$0$0") := ltac2:(zQ "40!l3!h9!m0!k3\2e8$1@2$0@2$2@2$0^1+jjjjjjjjjjjjjjj3@2$0@2$0@2$3^1+2+vvvvvvvvvvvvvvvf+jjjjjjjjjjjjjjj3+vvvvvvvvvvvvvvvf").
Definition cf10 : ltac2:(zQ "10!h9>2e9$0$0") := ltac2:(zQ "40!h9!m0!l3!k3\2e9$0@2$2@2$1^1@2$3^1+4+vvvvvvvvvvvvvvvf").
Definition cf11 : ltac2:(zQ "10!h9>3e10$0$0") := ltac2:(zQ "40!l3!h9!m6!k3\3e10$1@2$0@2$3@2$0@2$2@2$0@2$0^1+vgvgvgvgvgvgvgf+vvvvvvvvvvvvvvvf+hghghghghghghg1+vvvvvvvvvvvvvvvf+j8+vvvvvvvvvvvvvvvf").
Definition cf12 : ltac2:(zQ "10!h9>3e11$0$0") := ltac2:(zQ "40!l3!la!h9!m0\3e11$2@2$0@2$1@2$0@2$3@2$1+je^1+ogggggg0+vvvvvvvf+ogggggg0+vvvvvvvvvvvvvvvf").
Definition cf13 : ltac2:(zQ "10!h9>4size$0>3e12$0$0") := ltac2:(zQ "30!h9!l3!k3\4size$0\3e12$0@2$1@2$2^2@2$1^1+jf+vvvvvvvvvvvvvvvf").
Definition cf14 : ltac2:(zQ "10!h9>3e12$0$0") := ltac2:(zQ "50!l3!h9!m0!pa!la\3e12$1@2$0@2$4@2$0@2$2@2$3+vvvvvvvvvvvvvvvf@2$0^1+hf+ogggggg0+vvvvvvvf+ogggggg0+vvvvvvvvvvvvvvvf").
Definition cf15 : ltac2:(zQ "10!h9>4size$0>3e14$0$0") := ltac2:(zQ "30!l3!h9!kc\4size$1\3e14$1@2$0@2$0^2@2$0@2$2^1+vvvvvvvvvvvvvvvf+vvvvvvvvvvvvvvvf+vvvvvvvvvvvvvvvf").
Definition cf16 : ltac2:(zQ "10!h9>3e11$0>3e13$0>3e15$0$0") := ltac2:(zQ "80!l3!h9!m0!q3!jd!q9!kc!pa\3e11$1\3e13$1\3e15$1@2$0@2$2@2$2@2$4@2$0@2$6@2$0@2$7^3+1+vvvvvvvvvvvvvvvf+ne+vvvvvvvvvvvvvvvf@2$0@2$0^2+1+vvvvvvvvvvvvvvvf@2$0@1$3@2$5@2$0Z+vvvvvvvvvvvvvvvf^1+vvvvvvvvvvvvvvvf-2+vvvvvvvvvvvvvvvf").

Lemma cf1_eq : ltac2:(zQ "40!h9!hq7!uc!hte>1x$0@3$1$0@1$2^1@1$3^1"). Proof. intros. unfold cb1, cf1. rewrite !mod64_land. reflexivity. Qed.
Lemma cf2_eq : ltac2:(zQ "40!h9!hq7!hi3!hu4>1x$0@3$1$0@1$2^1@1$3^1"). Proof. intros. unfold cb2, cf2. rewrite !mod64_land. reflexivity. Qed.
Lemma cf3_eq : ltac2:(zQ "40!h9!hq7!hi9!hua>1x$0@3$1$0@1$2^1@1$3^1"). Proof. intros. unfold cb3, cf3. rewrite !mod64_land. reflexivity. Qed.
Lemma cf4_eq : ltac2:(zQ "40!h9!hq7!hif!hv0>1x$0@3$1$0@1$2^1@1$3^1"). Proof. intros. unfold cb4, cf4. rewrite !mod64_land. reflexivity. Qed.
Lemma cf5_eq : ltac2:(zQ "40!h9!hq7!hj5!hv6>1x$0@3$1$0@1$2^1@1$3^1"). Proof. intros. unfold cb5, cf5. rewrite !mod64_land. reflexivity. Qed.
Lemma cf6_eq : ltac2:(zQ "40!h9!hq7!hjb!hvc>1x$0@3$1$0@1$2^1@1$3^1"). Proof. intros. unfold cb6, cf6. rewrite !mod64_land. reflexivity. Qed.
Lemma cf7_eq : ltac2:(zQ "40!h9!hq7!hk1!ig2>1x$0@3$1$0@1$2^1@1$3^1"). Proof. intros. unfold cb7, cf7. rewrite !mod64_land. reflexivity. Qed.
Lemma cf8_eq : ltac2:(zQ "40!h9!hq7!hk7!ig8>1x$0@3$1$0@1$2^1@1$3^1"). Proof. intros. unfold cb8, cf8. rewrite !mod64_land. reflexivity. Qed.
Lemma cf9_eq : ltac2:(zQ "40!h9!hq7!hkd!ige>1x$0@3$1$0@1$2^1@1$3^1"). Proof. intros. unfold cb9, cf9. rewrite !mod64_land. reflexivity. Qed.
Lemma cf10_eq : ltac2:(zQ "40!h9!hq7!v2!ih4>1x$0@3$1$0@1$2^1@1$3^1"). Proof. intros. unfold cb10, cf10. rewrite !mod64_land. reflexivity. Qed.
Lemma cf11_eq : ltac2:(zQ "40!h9!hq7!v9!ihb>1x$0@3$1$0@1$2^1@1$3^1"). Proof. intros. unfold cb11, cf11. rewrite !mod64_land. reflexivity. Qed.
Lemma cf12_eq : ltac2:(zQ "40!h9!hq7!hg0!ii2>1x$0@3$1$0@1$2^1@1$3^1"). Proof. intros. unfold cb12, cf12. rewrite !mod64_land, swrap32_land. reflexivity. Qed.
Lemma cf13_eq : ltac2:(zQ "40!h9!hq7!hg7!ii9>1x$0>1y$0@3$1$0@2$2^2^1@2$3^2^1"). Proof. intros. unfold cb13, cf13. rewrite !mod64_land, mod6_land. reflexivity. Qed.
Lemma cf14_eq : ltac2:(zQ "40!h9!hq7!hge!ij0>1x$0@3$1$0@1$2^1@1$3^1"). Proof. intros. unfold cb14, cf14. rewrite !mod64_land, swrap32_land, mod5_land. reflexivity. Qed.
Lemma cf15_eq : ltac2:(zQ "40!h9!hq7!hh5!ij7>1x$0>1y$0@3$1$0@2$2^2^1@2$3^2^1"). Proof. intros. unfold cb15, cf15. rewrite !mod64_land. reflexivity. Qed.
Lemma cf16_eq : ltac2:(zQ "40!h9!hq7!hhc!ije>1x$0>1y$0>1z$0@3$1$0@3$2^3^2^1@3$3^3^2^1"). Proof. intros. unfold cb16, cf16. rewrite !mod64_land. reflexivity. Qed.

Definition cidfast : ltac2:(zQ "10!h9>4size$0$0") := ltac2:(zQ "h10!h9!hte!ih4!ihb!ii2!ii9!ij0!ij7!ije!hu4!hua!hv0!hv6!hvc!ig2!ig8!ige\4size$0=3e11$0@1$3@1$2@1$h0@1$f@1$e@1$d@1$c@1$b@1$a@1$9@1$1^1=3e12$0@1$4^1@3$8^2@2$5^3^1@2$7^3@1$6^1").

Lemma forall_range_ext : ltac2:(zQ "50!hmb!h9!hq7!hn3!hqd>1f>1x$1$0>1g>1x$1$0>1n$4>1a$1>0>1x$1@3$2$0@1^5^1@1^4^1@3$2$0@3$3^5^2^3@3$3^4^2^3").
Proof. intros f g n. induction n as [|k IH]; intros a E; [reflexivity|]. cbn [forall_range]. rewrite (E a), (IH (a + 1) E). reflexivity. Qed.
Lemma forall_rangeZ_ext : ltac2:(zQ "40!h9!hmb!hq7!hse>1f>1x$0$1>1g>1x$0$1>1a$0>1n$0>0>1x$0@3$2$1@1^5^1@1^4^1@3$2$1@3$3^5^3^2@3$3^4^3^2").
Proof. intros f g a n E. unfold forall_rangeZ. apply forall_range_ext. exact E. Qed.

Lemma cid_chkF_lo : ltac2:(zQ "80!hmb!hob!hq7!h9!ik5!hse!ip0!ipc@3$2$0@3$5\1s$3@2$7@1$4^1@1$6^1+ig1+nvg0$1").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma cid_chkF_hi : ltac2:(zQ "80!hmb!hob!hq7!h9!ik5!hse!ip0!ipc@3$2$0@3$5\1s$3@2$7@1$4^1@1$6^1+ohg1+nvg0$1").
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma cidbits_unfold : ltac2:(zQ "h37!uc!v2!v9!hi3!hi9!hif!hj5!hjb!hk1!hk7!hkd!h9!hg0!hq7!hg7!hge!hh5!hhc!iq2&@1$7@1$6@1$5@1$4@1$3@1$0^1&@1$8~0&@1$9~1&@1$a~2&@1$1~3&@1$2~4&@1$c~5>4size$b@3$d$b@1$h2^1@3$h1~5@2$e^1~6@2$h0^1@1$f~6").
Proof. intros size. reflexivity. Qed.

Lemma cidbits_fast : ltac2:(zQ "40!h9!hq7!iq2!ik5>4size$0@3$1$0@1$2^1@1$3^1").
Proof.
  intros size. rewrite cidbits_unfold. unfold cidfast.
  rewrite !cf16_eq, !cf15_eq, !cf14_eq, !cf13_eq, !cf12_eq, !cf11_eq, !cf10_eq, !cf9_eq, !cf8_eq, !cf7_eq, !cf6_eq, !cf5_eq, !cf4_eq, !cf3_eq, !cf2_eq, !cf1_eq.
  reflexivity.
Qed.
Lemma cid_chk_lo : ltac2:(zQ "80!hmb!hob!hq7!h9!iq2!hse!ip0!ipc@3$2$0@3$5\1s$3@2$7@1$4^1@1$6^1+ig1+nvg0$1").
Proof.
  rewrite (forall_rangeZ_ext _ (fun s => Z.eqb (cidfast s) (class_id s))); [exact cid_chkF_lo|].
  intros x. rewrite cidbits_fast. reflexivity.
Qed.
Lemma cid_chk_hi : ltac2:(zQ "80!hmb!hob!hq7!h9!iq2!hse!ip0!ipc@3$2$0@3$5\1s$3@2$7@1$4^1@1$6^1+ohg1+nvg0$1").
Proof.
  rewrite (forall_rangeZ_ext _ (fun s => Z.eqb (cidfast s) (class_id s))); [exact cid_chkF_hi|].
  intros x. rewrite cidbits_fast. reflexivity.
Qed.

Lemma cidbits_ok : ltac2:(zQ "h60!h9!hq7!hr4!uc!v2!v9!hg0!hg7!hge!hh5!hhc!hi3!hi9!hif!hj5!hjb!hk1!hk7!hkd!ip0!hrb!hs0>4size$0>2e1$0>2e2$0>2e3$0>2e4$0>2e5$0>2e6$0>2e7$0>2e8$0>2e9$0>3e10$0>3e11$0>3e12$0>3e13$0>3e14$0>3e15$0>3e16$0>0@2$2@2$h5+ig0^h1@2$h4^h1+hggg0>0@3$1$0^h1@1$3^h2>0@3$1$0^h1@1$b^h2>0@3$1$0^h1@1$c^h2>0@3$1$0^h1@1$d^h2>0@3$1$0^h1@1$e^h2>0@3$1$0^h1@1$f^h2>0@3$1$0^h1@1$h0^h2>0@3$1$0^h1@1$h1^h2>0@3$1$0^h1@1$h2^h2>0@3$1$0^h1@1$4^h2>0@3$1$0^h1@1$5^h2>0@3$1$0^h1@1$6^h2>0@3$1$0^h1@2$7^he^h2>0@3$1$0^h1@1$8^h3>0@3$1$0^h1@2$9^i0^h2>0@3$1$0^h1@3$a^h6^h4^h2@3$1$0^h2@1$h3^i2").
Proof.
  intros size e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 SZ He1 He2 He3 He4 He5 He6 He7 He8 He9 He10 He11 He12 He13 He14 He15 He16.
  assert (C : Z.eqb (cidbits size) (class_id size) = true).
  { destruct (Z.lt_ge_cases size 33025).
    - exact (forall_rangeZ_spec (fun s => Z.eqb (cidbits s) (class_id s)) 513 32512 size cid_chk_lo ltac:(lia) ltac:(lia)).
    - exact (forall_rangeZ_spec (fun s => Z.eqb (cidbits s) (class_id s)) 33025 32512 size cid_chk_hi ltac:(lia) ltac:(lia)). }
  apply Z.eqb_eq in C. rewrite cidbits_unfold in C. subst. exact C.
Qed.

(* [comment removed for export] *)
Lemma class_id_chk : ltac2:(zQ "90!ip0!iqc!hmb!hob!hq7!h9!hse!ir4!q9@3$4$2@3$6\1s$5@2$1@2$7+1@1$0^1@2$8@1$0^1+i0+1+hggg0$3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma class_id_range : ltac2:(zQ "50!hrb!hr4!ip0!h9!hs0>4size$3>0@2$1@2$0+1^1@2$0^1+hggg0@2$1@2$0+1@1$2^2@2$4@1$2^2+i0").
Proof.
  intros size Hs.
  pose proof (forall_rangeZ_spec (fun s => (1 <=? class_id s) && (class_id s <? 32)) 1 65536 size class_id_chk ltac:(lia) ltac:(lia)) as C.
  cbv beta in C. apply andb_prop in C. destruct C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. lia.
Qed.

(* [comment removed for export] *)
Lemma class_size_ge_chk : ltac2:(zQ "80!hmb!hob!hq7!h9!hse!ip0!ira!ir4@3$2$0@3$4\1s$3@2$7^1@1$6@1$5^1+1+hggg0$1").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma class_size_ge : ltac2:(zQ "50!hrb!hr4!h9!ip0!ira>4size$2>0@2$1@2$0+1^1@2$0^1+hggg0@2$0^2@1$4@1$3^2").
Proof.
  intros size Hs.
  pose proof (forall_rangeZ_spec (fun s => s <=? class_size (class_id s)) 1 65536 size class_size_ge_chk ltac:(lia) ltac:(lia)) as C.
  cbv beta in C. apply Z.leb_le in C. exact C.
Qed.
