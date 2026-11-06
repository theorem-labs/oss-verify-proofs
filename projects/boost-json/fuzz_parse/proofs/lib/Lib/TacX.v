(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Export Tac CellsX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import SysStep.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos01Z35stdpp9bitvectorbdefinitionsi22bvi27Z_to_bv37Corelib4Init5Logicke3andke2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~md2wz46Stdlib6ZArith6BinInt1Zqd2leqd2ltqd3powi2bbv_unsignedmd2b879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~u83zxbu84zx16u84sx3237Corelib4Init9Datatypeshj64conshj64listhj63nilu83le1qd6modulo" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Definition wz : ltac2:(zQ "30!h9!hf!jf>1z$1@1$2@1$0#k0") := ltac2:(zQ "30!h9!hf!k4\1z$1@2$2@1$0#k0^1").
Definition b8 : ltac2:(zQ "30!h9!hf!jf>1z$1@1$2@1$0#8") := ltac2:(zQ "30!h9!hf!k4\1z$1@2$2@1$0#8^1").

Lemma wz_unsigned : ltac2:(zQ "90!hf!m2!m8!h9!q8!s5!sa!sf!t5>1x$0>0@2$1@2$5Z^1@2$6^1@2$7+2+k0@3$2$0@2$8@1$3#k0@1$4^2^2").
Proof. intros x. intros. unfold wz. apply unsigned_lit. lia. Qed.
Lemma b8_unsigned : ltac2:(zQ "80!hf!m2!m8!h9!u3!s5!sa!t5>1x$0>0@2$1@2$5Z^1@2$6^1+hg0@3$2$0@2$7@1$3#8@1$4^2^2").
Proof. intros x. intros. unfold b8. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn. apply Z.mod_small. lia. Qed.
Lemma zxb_b8 : ltac2:(zQ "a0!m2!m8!h9!hf!hi2!u3!q8!s5!sa!jf>1x$3>0@2$0@2$7Z^1@2$8^1+hg0@3$1@1$9@1$2#k0@1$4@1$5^2@1$6^2").
Proof. intros x. intros. unfold zxb, wz. rewrite b8_unsigned by lia. reflexivity. Qed.
Lemma zx16_wz : ltac2:(zQ "90!q8!m2!m8!h9!hf!hi8!s5!sa!jf>1x$4>0@2$1@2$6Z^1@2$7^1+hggg0@3$2@1$8@1$3#k0@1$5@1$0^2@1$0^2").
Proof. intros x. intros. unfold zx16, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma sx32_wz : ltac2:(zQ "a0!q8!m2!m8!h9!hf!hif!s5!sa!sf!jf>1x$4>0@2$1@2$6Z^1@2$7^1@2$8+2+hf@3$2@1$9@1$3#k0@1$5@1$0^2@1$0^2").
Proof. intros x. intros. unfold sx32, wz. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma le1_mod : ltac2:(zQ "b0!h9!jf!hke!hl6!hle!m8!hf!hm5!u3!hmb!k4>1z$6@3$5@1$3@1$1@1$0#8@1$7@2$a@1$0#k0^1@3$2@1$1@1$0#8@1$8@2$9^1+hg0@1$4@1$1@1$0#8").
Proof. intros z.
  unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (256 * 2^56).
  rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256), Z.mod_add, Z.mod_mod by lia. reflexivity.
Qed.
Lemma le1_lit : ltac2:(zQ "d0!h9!jf!hke!hl6!hle!m2!m8!hf!hm5!u3!s5!sa!k4>1z$7>0@2$5@2$aZ^1@2$b^1+hg0@3$6@1$3@1$1@1$0#8@1$8@2$c@1$0#k0^2@3$2@1$1@1$0#8@1$9^2@1$4@1$1@1$0#8").
Proof. intros z.
  intros Hz. unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned, (bv_wrap_small 64) by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           first [ change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]
                 | rewrite (le1_mod z) ]; mem_after_store
       end).

Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; fix_lit_store; try nrm.
(* [comment removed for export] *)
