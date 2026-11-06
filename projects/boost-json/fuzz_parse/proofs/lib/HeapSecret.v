(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase StackLayout.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe4Npos3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutje9EntryDraw35stdpp9bitvectorbdefinitionsne2bv37Corelib5Lists7ListDefq05skipnjefat_random_bytesje9ed_randomhe1Z69OSSVerify6Proofsaboost_jsonafuzz_parse3libaHeapSecret~~~~~~u1cbytes_le_valu1h4secret_bytes_of_draw06length37Corelib4Init5Logichkd3and46Stdlib6ZArith6BinInt1Zhm82lehm82lthm83mulhm86of_nathm83pow03nathkd2equ1esecret_of_drawnebbv_unsignedu1aHeapSecretu1cmkHeapSecretu1h4secret_of_draw_rangeu1aword_range" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Class HeapSecret : Type := mkHeapSecret {
  hsecret : Z ;
  hsecret_range : 0 <= hsecret < 2^64 ;
  hcanary : Z ;
  hcanary_range : 0 <= hcanary < 2^64
}.

(* [comment removed for export] *)
Ltac hsb :=
  let K := fresh "HSECB" in
  pose proof (hsecret_range : 0 <= hsecret < 2^64) as K;
  let K2 := fresh "HCANB" in
  pose proof (hcanary_range : 0 <= hcanary < 2^64) as K2.

(* [comment removed for export] *)
Fixpoint bytes_le_val (bs : list byte) : Z :=
  match bs with
  | [] => 0
  | b :: bs' => bv_unsigned b + 256 * bytes_le_val bs'
  end.

Definition secret_bytes_of_draw : ltac2:(zQ "40!h8!j7!n2!pb>3rnd$2@1$0@1$3@1$1#8") := ltac2:(zQ "60!r7!j7!n2!rf!t1!pb\3rnd$2@3$0@1$5@1$1#8N8@1$3@1$4^1").

Definition secret_of_draw : ltac2:(zQ "20!td!n2>3rnd$1$0") := ltac2:(zQ "30!n2!hhe!hid\3rnd$0@1$1@1$2^1").

Lemma bytes_le_val_range : ltac2:(zQ "b0!j7!hhe!pb!hk5!h8!hm1!ho0!ho6!hoc!hp3!hpd>2bs@1$4@1$2@1$0#8@2$5@2$6Z@1$1^1@2$7@1$1^1@2$a+2@2$8+8@1$9@2$3@1$2@1$0#8^1").
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_val length]; [lia|].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  replace (8 * Z.of_nat (S (length bs))) with (8 + 8 * Z.of_nat (length bs)) by lia.
  rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. lia.
Qed.

Lemma length_secret_bytes_of_draw : ltac2:(zQ "70!hk5!hq4!hq9!j7!n2!hid!pb>3rnd$4@3$2$1@2$0@1$6@1$3#8@1$5^1N8").
Proof. intros rnd. reflexivity. Qed.

Lemma secret_of_draw_range : ltac2:(zQ "60!hqf!hm1!n2!ho0!ho6!hpd>3rnd$2@2$1@2$3Z@1$0^1@2$4@1$0^1@2$5+2+k0").
Proof.
  intros rnd. unfold secret_of_draw.
  pose proof (bytes_le_val_range (secret_bytes_of_draw rnd)) as R.
  rewrite length_secret_bytes_of_draw in R. exact R.
Qed.

(* [comment removed for export] *)
Lemma word_range : ltac2:(zQ "70!j7!hs0!hm1!ho0!ho6!hpd!pb>1w@1$6@1$0#k0@2$2@2$3Z@2$1@1$0#k0^1@2$4@2$1@1$0#k0^1@2$5+2+k0").
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. exact R. Qed.
Definition heap_secret_of_draw : ltac2:(zQ "40!j7!n2!hse!pb>3rnd$1>2cw@1$3@1$0#k0$2") := ltac2:(zQ "80!j7!n2!htb!hqf!hua!ig2!pb!hs0\3rnd$1\2cw@1$6@1$0#k0@4$2@1$3^2@1$4^2@2$7@1$0#k0^1@1$5^1").

Section Facts.
  Context {HSEC : HeapSecret}.
End Facts.
(* [comment removed for export] *)
