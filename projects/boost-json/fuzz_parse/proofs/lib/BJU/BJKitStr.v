(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJKitW.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc6shiftr37Corelib4Init5Logicjd3andjd2eqhc3divhc2lehc2lthc3mulhc3powhc3add04Npos35stdpp9bitvectorbdefinitionso47Z_to_bvo4bbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU8BJKitStr~~~~~~r9achars_needhc3oppo42bvo49bv_signed37Corelib4Init9Datatypeshhc4boolhc3eqbr94xlen79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~hk97v_sltiuhc4landjd2orhhc4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hq74cellhq7bcells_byteshq7acells_size79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ig88rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~ikf5rsegshhc3nathhc6optionhq78cells_wfhhc6length3h5LinuxProcessSemanticsfLinuxProcessSem6BvBaseircdZ_to_le_bytesircdbytes_le_to_Zirch0le_bytes_to_word79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ji23le8hhc4conshq72C8hq72CB" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma div24_mulhu : ltac2:(zQ "90!h9!j4!l1!l7!lc!m2!m7!mc!n2>1x$0>0@2$2@2$5Z^1@2$6^1@2$8+2+k0@3$3$0@2$1@2$1@2$7^2+qqqqqqqqqqqqqqqb+k0+4@2$4^2+h8").
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
  change (2^64 * 2^4) with (2^68).
  pose proof (Z.div_mod x 24 ltac:(lia)) as HE. pose proof (Z.mod_pos_bound x 24 ltac:(lia)) as R.
  set (q := x / 24) in *. set (r := x mod 24) in *.
  replace (x * 12297829382473034411) with (q * 2^68 + (8 * q + r * 12297829382473034411)) by (rewrite HE; lia).
  rewrite Z.div_add_l by lia. rewrite (Z.div_small (8 * q + r * 12297829382473034411)); [lia|].
  assert (q < 2^60) by (subst q; apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* [comment removed for export] *)
Definition chars_need : ltac2:(zQ "10!h9>3cur$0>5chars$0>1n$0$0") := ltac2:(zQ "30!n8!h9!lc\3cur$1\5chars$1\1n$1@2$0@2$0@2$2@2$0@2$0^2^1+h7+h8^3+1").

Lemma need_calc : ltac2:(zQ "h00!ne!n8!q1!h9!m2!mc!j4!m7!n2!qb!l1!l7!v8!hg5!hgb!hh0>1B$3>3cur$3>5chars$3>1n$3>0@2$a@2$4Z^3@2$7^3@2$8+2+i8>0@2$4Z^3>0@2$4Z^3>0@2$7@2$1^5^4@2$8+2+hf@3$b@1$e@1$0#k0@2$2@1$0#k0@2$1@2$1@2$6@2$9@1$0#k0@2$2@1$0#k0@2$6@2$5@2$1@2$1^6^5+h7+qqqqqqqqqqqqqqqb+k0+4@2$5@2$9@1$0#k0@2$2@1$0#k0@2$6@2$f@1$0#k0@2$2@1$0#k0@2$1@2$1^8@2$5+h8^7@1$d^8+3+qqqqqqqqqqqqqqqb+1@2$2@1$0#k0@3$c^7^6^5").
Proof.
  intros B cur chars n Hc Hch Hn Hs.
  rewrite (unsigned_lit (Z.shiftr ((chars + n + 23) * 12297829382473034411) 64)).
  2:{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  rewrite div24_mulhu by lia.
  replace (B + 24 * cur + - B) with (24 * cur) by lia.
  rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn [Z.of_N N.sub Z.pow_pos Pos.iter Z.mul Pos.mul]. change (2 ^ 64 / 2) with (2^63). rewrite (Z.mod_small) by lia.
  replace (24 * cur + 2 ^ 63 - 2 ^ 63) with (24 * cur) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (24 * cur / 2 ^ 3) with (3 * cur) by (change (2^3) with 8; rewrite <- (Z.div_mul (3*cur) 8) by lia; f_equal; lia).
  rewrite unsigned_lit by lia.
  rewrite <- Z_to_bv_mod64. symmetry. rewrite <- Z_to_bv_mod64. f_equal. unfold chars_need.
  replace ((chars + n + 23) / 24 + 3 * cur * 12297829382473034411 + 1) with (((chars + n + 23) / 24 + cur + 1) + (2 * cur) * 2^64) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(* [comment removed for export] *)
Definition xlen : ltac2:(zQ "10!h9>5chars$0$0") := ltac2:(zQ "40!hj4!h9!n8!hjc\5chars$1M0\0$0$1@2$3^1ZZ@2$2^1+h8").

Lemma xlen_calc : ltac2:(zQ "d0!ne!q1!qb!h9!n8!l1!l7!hk2!ho8!hp3!m2!m7!n2>5chars$3>0@2$5@2$aZ^1@2$b^1@2$c+2+je@3$6$3@2$9@2$2@1$0#k0@2$1@1$0#k0@2$4@2$2@1$0#k0@2$8@2$1@1$0#k0^2+1-1@2$2@1$0#k0@2$1@1$0#k0@2$4^2+h8@1$7^2").
Proof.
  intros chars Hc. rewrite v_sltiu_b2z. rewrite (unsigned_lit chars) by lia.
  change (bv_wrap 64 1) with 1. rewrite (unsigned_lit (chars + 24)) by lia. unfold xlen.
  destruct (Z.ltb_spec chars 1); destruct (Z.eqb_spec chars 0); try lia; cbn [Z.b2z].
  - rewrite (unsigned_lit 1) by lia. rewrite unsigned_lit by lia. apply Z.land_0_l.
  - rewrite (unsigned_lit 0) by lia. rewrite unsigned_lit_wrap. change ((0 + -1) mod 2^64) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma xlen_bounds : ltac2:(zQ "80!h9!hk2!l1!l7!m2!hpa!n8!m7>5chars$0>0@2$4Z^1@2$2@2$4Z@1$1^2@2$5@3$3$0@1$1^2Z@2$2@2$7Z^2@3$3$0@1$1^2@2$6^2+h8").
Proof. intros chars Hc. unfold xlen. destruct (Z.eqb_spec chars 0); lia. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Arr SysStep CellsX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs.
Import ListNotations.

Lemma rw_cells_rebytes : ltac2:(zQ "d0!hpf!ne!hgb!l7!hu3!hub!hva!ik3!ioc!ip5!ipc!h9!iq6>1m>0@1$2@1$1#k0@1$a@1$2@1$1#8>1A$b>2cs@1$0$4>3cs'@1$0$4>0@4$7$8^4^3^2>0@1$c^2>0@3$3@1$0@1$2@1$1#8@1$5^3@1$5^4>0@3$3$9@1$6^4@1$6^5@4$7$8^8^7^5").
Proof.
  intros m A cs cs' [[WF BA] WR] WF' EB ES. split; [split; [exact WF'|]|].
  - rewrite EB. exact BA.
  - rewrite ES. exact WR.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_bytes_le_to_Z : ltac2:(zQ "70!ne!hgb!hpf!ir2!l7!iub!ivc>2bs@1$2@1$1@1$0#8@3$4@1$2@1$1@1$0#8@2$5@2$3@1$1@1$0#8^1@1$6^1^1").
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

Lemma bytes_le_to_Z_bound8 : ltac2:(zQ "b0!ne!ivc!hgb!ir2!hpf!ip5!l1!l7!m2!m7!n2>2bs@1$4@1$2@1$0#8>0@3$7$5@2$3@1$2@1$0#8^1N8@2$6@2$8Z@1$1^2@2$9@1$1^2@2$a+2+k0").
Proof.
  intros bs L. pose proof (bytes_le_to_Z_bound bs) as B. pose proof (bytes_le_to_Z_nonneg bs). rewrite L in B.
  change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in B. lia.
Qed.

Lemma le8_of_bytes : ltac2:(zQ "80!ne!hgb!hpf!l7!ir2!ip5!jgd!jlc>2bs@1$2@1$1@1$0#8>0@3$3$5@2$4@1$1@1$0#8^1N8@3$3@1$2@1$1@1$0#8@1$7@1$6^2^2").
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_bound8 bs L) as B.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z. rewrite Z.mod_small by lia.
  rewrite <- L. apply Z_to_le_bytes_bytes_le_to_Z.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_bytes8 : ltac2:(zQ "f0!ne!hgb!hu3!jm3!hpf!ik3!ioc!ir2!ip5!ipc!l7!h9!jgd!jmb!jn1>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1A$b>2bs@1$4@1$1@1$0#8>4rest@1$4$2>0@3$a$8@2$7@1$1@1$0#8^2N8>0@4$5$6^5^4@3$3$2@2$eN8^3^2@4$5$6^6^5@3$3$2@1$d@1$c^4^3").
Proof.
  intros m A bs rest L R. pose proof R as [[[_ WF] _] _].
  eapply rw_cells_rebytes; [exact R| cbn; split; [exact I| exact WF]| cbn [cells_bytes cbytes]; rewrite le8_of_bytes by exact L; reflexivity| reflexivity].
Qed.
(* [comment removed for export] *)
