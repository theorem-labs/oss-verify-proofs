(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AllocWf.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc2eq69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~j5cas_space_begj56astatej5aregion_beg46Stdlib6ZArith6BinInt1Zpb3addpb3mulpb3powj5ffree_array_basej5h0kFreeArrayOffsetj5fcompact_to_addrj5h0kCompactPtrScalepb6shiftlpb2lehc3nothc2orhc3andj5akSpaceSizepb2ltj5dclass_of_addr37Corelib4Init9Datatypeshl24boolhl24truej5ain_primaryj5aclass_sizepb3subj5aget_regionj5bkNumClassesj5h1rg_allocated_userpb6modulo79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocKit~~~~~~ht36carved79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AllocWf~~~~~~ihb2WFj5drg_free_array36Stdlib5Lists4Listime2Inj56get_pcj59pc_chunks" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac hci :=
  try (lazymatch goal with HH : HeapCeil |- _ =>
         repeat (match goal with
                 | |- context [?X] => is_evar X; let T := type of X in constr_eq T HeapCeil; unify X HH
                 end)
       end).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_beg_eq : ltac2:(zQ "80!h9!j0!n6!o5!oe!r3!r9!rf>2st$3>1c$0@3$1$0@2$4^2^1@2$5@1$2^2@2$6^1@2$7+2+i0").
Proof. intros st c. unfold region_beg, kRegionSizeLog. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Lemma free_array_base_eq : ltac2:(zQ "70!h9!j0!o5!s5!t7!oe!r3>2st$2>1c$0@3$1$0@2$3^2^1@2$6@2$5^2^1$4").
Proof. reflexivity. Qed.

Lemma compact_to_addr_eq : ltac2:(zQ "70!h9!j0!o5!ub!oe!r3!r9>2st$2>1c$0>2cp$0@3$1$0@3$3^3^2^1@2$5@2$4^3^2@2$6^1+h0").
Proof. intros st c cp. unfold compact_to_addr, kCompactPtrScale. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. lia. Qed.

Lemma shiftl4 : ltac2:(zQ "50!h9!j0!vd!r9!hh1>2cp$0@3$1$0@2$4^1$2@2$3^1+h0").
Proof. intros cp. unfold kCompactPtrScale. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. lia. Qed.

(* [comment removed for export] *)
Lemma regions_disjoint : ltac2:(zQ "90!oe!hha!h9!r3!rf!j0!hhf!hi5!o5>2st$8>1c$2>2c'$2>0@2$1Z^2>0@2$1Z^2>0@1$6@3$5$2^4^3@2$7@2$1@2$3@2$0^6^5@2$4+2+i0@2$0^6^4@2$1@2$3@2$0^6^4@2$4+2+i0@2$0^6^5").
Proof. intros st c c' Hc Hc' Hne. rewrite !region_beg_eq. nia. Qed.

Lemma region_in_space : ltac2:(zQ "a0!hha!hia!n6!oe!r3!h9!o5!hj0!hjd!rf>2st$6>1c$5>0@2$1@2$0Z^1@2$8^1+i0@2$1@2$0@1$2^3@2$3^3^2@2$0@2$4@2$3^3^2@2$9+2+i0@2$4@1$2^3$7").
Proof. intros st c Hc. rewrite region_beg_eq. unfold kSpaceSize. nia. Qed.

Lemma class_of_addr_region : ltac2:(zQ "a0!h9!hia!hha!hjd!j0!o5!hk2!oe!r3!rf>2st$5>1c$0>3off$0>0@2$1@2$2Z^2@2$3^2+i0>0@2$1@2$2Z^2@2$3^2@2$9+2+i0@3$4$0@2$6^5@2$8@2$7^5^4^3^4").
Proof.
  intros st c off Hc Hoff. unfold class_of_addr, kRegionSizeLog. rewrite region_beg_eq.
  replace (as_space_beg st + c * 2^32 + off - as_space_beg st) with (off + c * 2^32) by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia.
  rewrite Z.add_0_l. rewrite Z.land_ones with (n := 5) by lia. change (Z.ones 5) with 31. apply Z.mod_small. lia.
Qed.

Lemma in_primary_region : ltac2:(zQ "c0!hia!h9!hha!hjd!hma!hn2!j0!o5!hna!oe!r3!rf>2st$7>1c$1>3off$1>0@2$0@2$2Z^2@2$3^2+i0>0@2$0@2$2Z^2@2$3^2@2$b+2+i0@3$6$4@2$8^5@2$a@2$9^5^4^3$5").
Proof.
  intros st c off Hc Hoff. unfold in_primary. pose proof (region_in_space st c Hc).
  apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition carved : ltac2:(zQ "20!h9!o5>2st$1>1c$0>1a$0P") := ltac2:(zQ "f0!hia!h9!ho7!oe!hha!hp4!j0!hhf!o5!hpa!hq7!hr5!r3!hjd!hsa\2st$8\1c$1\1a$1@2$0@2$0@2$4Z^2@2$d^2$a@2$0@1$7@3$6$1@1$2^2Z@2$0@2$4Z@2$5^1@2$3^3^2@2$0@3$6$1@2$e@2$5^1@2$3^3^2@1$2^2Z@2$4@2$c@2$5^1@2$3^3^2@1$2^2@1$b@2$9^3^2").

(* [comment removed for export] *)
Lemma carved_range : ltac2:(zQ "b0!hia!ho7!hha!h9!oe!r3!ih1!il8!o5!t7!hjd>2st$8>1c$3>1a$3>0@1$7^3>0@3$6^4^3^2@2$0@2$2@2$4^5^4^3@2$0@2$2@2$5^3@1$1^4@2$5@2$4^5^4$9@2$0@2$aZ@1$1^4@2$2@1$1^4+hggg0").
Proof.
  (intros st c a W nd_i1; ndestruct nd_i1 as (Hc & Hsz & H0 & Hm & Hle)). pose proof (WF_region st c W Hc) as RO.
  pose proof (ro_alloc_le _ _ RO). pose proof (ro_mapped_bound _ _ RO). pose proof (class_size_table_facts c Hc).
  unfold kUserMapSize in *. lia.
Qed.

(* [comment removed for export] *)
Lemma carved_sep : ltac2:(zQ "a0!h9!j0!hi5!ih1!ho7!r3!hha!hia!il8!o5>2st$9>1c$0>1a$0>2c'$0>2a'$0>0@1$8^5>0@3$3^6^5^4>0@3$3^7^4^3@2$2@2$7@3$1$0^7^5@3$1$0^6^4@2$2@2$6@2$5^6@1$4^7^4@2$6@2$5^4@1$4^5^6").
Proof.
  intros st c a c' a' W Ca Ca'.
  npose (carved_range st c a W Ca) as (R1 & R2 & R3). npose (carved_range st c' a' W Ca') as (R1' & R2' & R3').
  ndestruct Ca as (Hc & Hsz & H0 & Hm & Hle). ndestruct Ca' as (Hc' & Hsz' & H0' & Hm' & Hle').
  destruct (Z.eq_dec c c') as [<-|Hne].
  - destruct (Z.eq_dec a a') as [<-|Hna]; [left; auto| right].
    destruct (proj1 (Z.mod_divide (a - region_beg st c) (class_size c) Hsz) Hm) as [q Hq].
    destruct (proj1 (Z.mod_divide (a' - region_beg st c) (class_size c) Hsz) Hm') as [q' Hq'].
    assert (q <> q') by (intros ->; lia).
    destruct (Z.lt_ge_cases q q'); nia.
  - right. unfold kFreeArrayOffset in *.
    destruct (regions_disjoint st c c' ltac:(lia) ltac:(lia) Hne); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mult_below : ltac2:(zQ "60!h9!j0!hjd!hsa!r3!hha>1s$0>1x$0>1y$0>0@2$2Z^3>0@3$1$0@2$3^3^4Z>0@3$1$0@2$3^3^5Z>0@2$2^5^4@2$5@2$4^6^7^5").
Proof.
  intros s x y Hs Hx Hy Hlt.
  destruct (proj1 (Z.mod_divide x s ltac:(lia)) Hx) as [q ->].
  destruct (proj1 (Z.mod_divide y s ltac:(lia)) Hy) as [q' ->].
  assert (q < q') by nia. nia.
Qed.

Lemma carved_of_elem : ltac2:(zQ "h10!h9!j0!ho7!vd!hha!hjd!hh1!hia!hhf!ih1!il8!o5!ub!hpa!hq7!hr5!hsa>2st$b>1c$0>2cp$0>0@1$a^3>0@2$7@2$4Z^3@2$5^3$e>0@2$4Z^3>0@2$5@2$6^4$3@1$f@2$d^6^5>0@1$8@3$1$0@1$2^6Z>0@3$1$0@2$h0@2$6^6$3@1$2^7Z@3$9^9^8@3$c^9^8^7").
Proof.
  intros st c cp W Hc A B C D. rewrite shiftl4 in *. rewrite compact_to_addr_eq. unfold carved.
  replace (region_beg st c + cp * 16 - region_beg st c) with (cp * 16) by lia.
  pose proof (class_size_table_facts c Hc) as T. pose proof (ro_alloc_mod _ _ (WF_region st c W Hc) C) as AM.
  repeat split; try lia. apply mult_below; lia.
Qed.

Lemma carved_free : ltac2:(zQ "c0!h9!hia!ih1!il8!o5!ub!hpa!hq7!ile!io1!hha!hjd>2st$4>1c$0>2cp$0>0@1$3^3>0@2$1@2$aZ^3@2$b^3$7>0@3$9$0^3@1$8@2$6^5^4@3$2^6^5@3$5^6^5^4").
Proof.
  intros st c cp W Hc Hin. pose proof (ro_fa_elems _ _ (WF_region st c W Hc) cp Hin) as (A & B & C & D).
  apply carved_of_elem; assumption.
Qed.

Lemma carved_cache : ltac2:(zQ "c0!h9!hia!ih1!il8!o5!ub!io7!hq7!ip0!io1!hha!hjd>2st$4>1c$0>2cp$0>0@1$3^3>0@2$1@2$aZ^3@2$b^3$7>0@3$9$0^3@1$8@2$6^5^4@3$2^6^5@3$5^6^5^4").
Proof.
  intros st c cp W Hc Hin. pose proof (co_elems _ _ (WF_cache st c W Hc) cp Hin) as (A & B & C & D).
  apply carved_of_elem; assumption.
Qed.
