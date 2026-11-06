(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac ZBridge Mem Arr SysStep CellsX Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe4Npos35stdpp9bitvectorbdefinitionsje2bv37Corelib4Init5Logicm02eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~n95asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~rc4cellrcbcells_bytesrcacells_size79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hha8rw_cells03nat06optionhe1Zrc8cells_wf06length3h5LinuxProcessSemanticsfLinuxProcessSem6BvBaseho5dZ_to_le_bytesho5dbytes_le_to_Zm03and46Stdlib6ZArith6BinInt1Zhtc2lehtc2lthtc3powho5h0le_bytes_to_word79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ihc3le804consrc2C8rc2CB" s.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rw_cells_rebytes : ltac2:(zQ "d0!h8!j7!lb!n4!r4!v8!vf!hgd!hl5!hm1!hm6!hme!hn2>1m>0@1$2@1$1#k0@1$a@1$2@1$1#8>1A$b>2cs@1$0$5>3cs'@1$0$5>0@4$8$4^4^3^2>0@1$c^2>0@3$3@1$0@1$2@1$1#8@1$6^3@1$6^4>0@3$3$9@1$7^4@1$7^5@4$8$4^8^7^5").
Proof.
  intros m A cs cs' [[WF BA] WR] WF' EB ES. split; [split; [exact WF'|]|].
  - rewrite EB. exact BA.
  - rewrite ES. exact WR.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_bytes_le_to_Z : ltac2:(zQ "70!j7!lb!h8!hnd!n4!hr4!hs5>2bs@1$2@1$1@1$0#8@3$4@1$2@1$1@1$0#8@2$5@2$3@1$1@1$0#8^1@1$6^1^1").
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8)%Z with 256%Z in Hb.
  pose proof (bytes_le_to_Z_nonneg bs) as Hn.
  assert (E1 : Z.shiftr (Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) 8 = bytes_le_to_Z bs).
  { rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_div_pow2 (bv_unsigned b) 8), Z.div_small by lia. apply Z.lor_0_l. }
  rewrite E1, IH. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with (2^8)%Z.
  rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
  rewrite (Z.land_ones (bv_unsigned b) 8), Z.mod_small by lia.
  replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z; [apply Z.lor_0_r|].
  symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.ltb_spec i 8).
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. apply Bool.andb_false_r.
Qed.

Lemma bytes_le_to_Z_bound8 : ltac2:(zQ "b0!j7!hs5!lb!hnd!h8!hm1!ht6!n4!hv4!hva!ig0>2bs@1$4@1$2@1$0#8>0@3$7$5@2$3@1$2@1$0#8^1N8@2$6@2$8Z@1$1^2@2$9@1$1^2@2$a+2+k0").
Proof.
  intros bs L. pose proof (bytes_le_to_Z_bound bs) as B. pose proof (bytes_le_to_Z_nonneg bs). rewrite L in B.
  change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in B. lia.
Qed.

Lemma le8_of_bytes : ltac2:(zQ "80!j7!lb!h8!n4!hnd!hm1!ig7!il6>2bs@1$2@1$1@1$0#8>0@3$3$5@2$4@1$1@1$0#8^1N8@3$3@1$2@1$1@1$0#8@1$7@1$6^2^2").
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_bound8 bs L) as B.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z. rewrite Z.mod_small by lia.
  rewrite <- L. apply Z_to_le_bytes_bytes_le_to_Z.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_bytes8 : ltac2:(zQ "f0!j7!lb!v8!ild!h8!r4!hl5!hnd!hm1!hm6!n4!hme!ig7!im3!im8>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1A$b>2bs@1$4@1$1@1$0#8>4rest@1$4$2>0@3$a$8@2$7@1$1@1$0#8^2N8>0@4$6$5^5^4@3$3$2@2$eN8^3^2@4$6$5^6^5@3$3$2@1$d@1$c^4^3").
Proof.
  intros m A bs rest L R. pose proof R as [[[_ WF] _] _].
  eapply rw_cells_rebytes; [exact R| cbn; split; [exact I| exact WF]| cbn [cells_bytes cbytes]; rewrite le8_of_bytes by exact L; reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
