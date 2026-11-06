(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~hc6astate46Stdlib6ZArith6BinInt1Zm63addhch4rg_mapped_free_arrayhcerg_mapped_userm63divhcaget_regionhc6regionm63mul79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAllocBudget~~~~~~sf4csumsf9reg_usagem63powm62le37Corelib4Init9Datatypeshie3nat37Corelib4Init5Logichkd3andm62ltm66of_nathkd2eqhie4boolm63eqbsf6pusagem63subm66modulohkd3nothie4listhcainit_statehcaas_regions" s.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition reg_usage : ltac2:(zQ "20!h9!ld>2st$1>1c$0$0") := ltac2:(zQ "90!ne!o4!pc!qd!h9!ld!r3!s0!s9\2st$5\1c$4=1r$7@2$6^2^1@2$0@2$0@1$2^1@1$1^1@2$8+qgg0@2$0@2$3@1$2^1+kggg0@2$3@1$1^1+kggg0").
Fixpoint csum (f : Z -> Z) (c : Z) (n : nat) : Z := match n with O => 0 | S k => f c + csum f (c + 1) k end.
Definition pusage : ltac2:(zQ "20!h9!ld>2st$1$0") := ltac2:(zQ "30!ld!hh0!hh7\2st$0@3$1@1$2^1+1Nhf").
Definition B_PRIM : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!hi3@2$0+2+i5").   (* [comment removed for export] *)

Lemma csum_le : ltac2:(zQ "80!h9!hi9!hh0!hk6!hm1!ne!hm8!hmd>1f>1x$0$0>1g>1x$0$0>1n$3>1c$0>0>1k$0>0@2$4@2$1^2^1@2$6^1@2$5^2@1$7^3@2$1@1^6^2@1^5^2@2$1@3$2^5^2^3@3$2^4^2^3").
Proof.
  intros f g n. induction n as [|n IH]; intros c H; cbn [csum]; [lia|].
  rewrite Nat2Z.inj_succ in H. pose proof (H c ltac:(lia)). pose proof (IH (c + 1) ltac:(intros k Hk; apply H; lia)). lia.
Qed.
Lemma csum_ext : ltac2:(zQ "90!h9!hn6!hh0!hk6!hm1!ne!hi9!hm8!hmd>1f>1x$0$0>1g>1x$0$0>1n$3>1c$0>0>1k$0>0@2$4@2$6^2^1@2$7^1@2$5^2@1$8^3@3$1$0@1^6^2@1^5^2@3$1$0@3$2^5^2^3@3$2^4^2^3").
Proof.
  intros f g n c H. pose proof (csum_le f g n c ltac:(intros k Hk; rewrite (H k Hk); lia)).
  pose proof (csum_le g f n c ltac:(intros k Hk; rewrite (H k Hk); lia)). lia.
Qed.
(* [comment removed for export] *)
Lemma csum_split : ltac2:(zQ "b0!h9!hnc!hh0!ne!hk6!hm1!hn6!ho4!hi9!hm8!hmd>1f>0$0$0>1n$4>1c$0>1k$0>0@2$5@2$8^2^1@2$9^1@2$3^2@1$a^3@3$6$0@3$2^5^3^4@2$3@1^5^2@3$2\1j$0M1\0$1$0@2$7^1^3Z@1^6^1^3^4").
Proof.
  intros f n. induction n as [|n IH]; intros c k Hk; cbn [csum]; [lia|]. rewrite Nat2Z.inj_succ in Hk.
  destruct (Z.eqb_spec c k) as [->|NE].
  - rewrite (csum_ext f (fun j => if j =? k then 0 else f j) n (k + 1)) by (intros j Hj; destruct (Z.eqb_spec j k); [lia| reflexivity]). lia.
  - rewrite (IH (c + 1) k) by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma pusage_ext : ltac2:(zQ "a0!h9!r3!hn6!hm1!ld!o4!pc!hoa!hi9!hm8>1a$4>1b$4>0>1c$0>0@2$3@2$8+1^1@2$9^1+i0@2$3@3$2$0@1$6@2$1^4^2@1$6@2$1^3^2@3$2$0@1$5@2$1^4^2@1$5@2$1^3^2@3$2$0@1$7^3@1$7^2").
Proof.
  intros a b H. unfold pusage. apply csum_ext. intros k Hk. change (1 + Z.of_nat 31) with 32 in Hk.
  unfold reg_usage. destruct (H k Hk) as [E1 E2]. rewrite E1, E2. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pusage_grow : ltac2:(zQ "h02!r3!o4!pc!h9!hn6!hp3!ne!hi9!hp9!hm1!ld!hoa!qd!hm8!hq2!s9&@2$5@1$2@2$0^a^9@1$2@2$0^b^9&@2$5@1$1@2$0^a^9@1$1@2$0^b^9>1a$a>1b$a>1c$3>0@2$9@2$7+1^1@2$d^1+i0>0>2c'$3>0@2$9@2$7+1^1@2$d^1+i0>0@1$e@3$4$3^2^4@2$9@3$4$3@1$2@2$0^6^3@1$2@2$0^7^3@3$4$3@1$1@2$0^6^3@1$1@2$0^7^3>0@3$4$3@2$8@1$2@2$0^5^3+kggg0Z>0@3$4$3@2$8@1$1@2$0^6^4+kggg0Z>0@3$4$3@2$8@2$5@1$2@2$0^6^5@1$2@2$0^7^5+kggg0Z>0@3$4$3@2$8@2$5@1$1@2$0^7^6@1$1@2$0^8^6+kggg0Z>0@2$7@1$2@2$0^9^7@1$2@2$0^8^7>0@2$7@1$1@2$0^a^8@1$1@2$0^9^8@3$4$3@1$b^a@2$6@2$6@2$6@1$b^b~0~1@2$f+qgg0@2$6@2$c~0+kggg0@2$c~1+kggg0").
Proof.
  intros a b c Hc OTH M1 M2 D1 D2 L1 L2. unfold pusage.
  rewrite (csum_split (reg_usage b) 31 1 c) by (change (1 + Z.of_nat 31) with 32; lia).
  rewrite (csum_split (reg_usage a) 31 1 c) by (change (1 + Z.of_nat 31) with 32; lia).
  rewrite (csum_ext (fun j => if j =? c then 0 else reg_usage b j) (fun j => if j =? c then 0 else reg_usage a j) 31 1).
  2:{ intros k Hk. change (1 + Z.of_nat 31) with 32 in Hk. destruct (Z.eqb_spec k c) as [->|NE]; [reflexivity|]. unfold reg_usage. destruct (OTH k Hk NE) as [E1 E2]. rewrite E1, E2. reflexivity. }
  unfold reg_usage. set (mb := rg_mapped_user (get_region b c)) in *. set (ma := rg_mapped_user (get_region a c)) in *.
  set (fb := rg_mapped_free_array (get_region b c)) in *. set (fa := rg_mapped_free_array (get_region a c)) in *.
  assert (E1 : mb / 262144 = ma / 262144 + (mb - ma) / 262144) by (Z.div_mod_to_equations; nia).
  assert (E2 : fb / 262144 = fa / 262144 + (fb - fa) / 262144) by (Z.div_mod_to_equations; nia).
  lia.
Qed.

(* [comment removed for export] *)
Lemma pusage_init : ltac2:(zQ "60!h9!hnc!hq9!hn6!hr1!hoa>2rb$0>2sb$0>2pa$0>3env@1$2$0>2ts$1@3$3$0@1$5@5$4^5^4^3^2^1Z").
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pusage_regions : ltac2:(zQ "70!hn6!hre!ld!hoa!hq9!h9!s0>1a$2>1b$2>0@3$0@1$4$6@1$1^2@1$1^1@3$0$5@1$3^3@1$3^2").
Proof. intros a b E. apply pusage_ext. intros c Hc. unfold get_region. rewrite E. split; reflexivity. Qed.
(* [comment removed for export] *)
