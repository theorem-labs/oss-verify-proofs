(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr ZBridge CellsX TacX.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init5Logic02eq37Corelib7Numbers7BinNumsh81Z37Corelib4Init9Datatypesj54boolj54true03andh84Npos3h5LinuxProcessSemantics5Riscv5Instrm76awidth3h5LinuxProcessSemantics5Riscv3Semp4bamo_alignedp49amo_bytes46Stdlib6ZArith6BinInt1Zt02let02ltt06modulot03pow35stdpp9bitvectorbdefinitionshg17Z_to_bvhg1bbv_unsignedp45low323h5LinuxProcessSemanticsfLinuxProcessSem6BvBasehk0dZ_to_le_bytesj54listhg12bvt03mul79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hp33le4m77AMO_ADDp47amo_valt03addh82N0hk0h0le_bytes_to_wordhg1abv_extractt03lor79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ihc4cellj54consj53nilihc2C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~in38rw_cellsj56option3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeis37Segment" s.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma amo_aligned_lit : ltac2:(zQ "e0!h4!j1!kd!l4!lb!m0!ob!r6!s4!u8!ud!v2!vb!hhe>2wd$6>1P$1>0@3$0$1@2$b^1@1$8^2Z>0@2$4@2$9Z^2@2$a^2@2$c+2+k0@3$0$2@2$7^4@2$d@1$5#k0^3$3").
Proof. intros wd P H B. unfold amo_aligned. rewrite unsigned_lit by lia. rewrite H. reflexivity. Qed.

Lemma unsigned_lit32 : ltac2:(zQ "90!m0!j1!lb!h4!u8!ud!vb!hhe!hi9>1z$1>0@2$2@2$4Z^1@2$5^1@2$6+2+i0@3$3$1@2$8@1$0#i0@2$7@1$0#i0^2^2").
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact H. Qed.

Lemma low32_lit : ltac2:(zQ "a0!m0!j1!lb!h4!hj8!u8!ud!vb!hhe!hi9>1x$1>0@2$2@2$5Z^1@2$6^1@2$7+2+i0@3$3$1@2$9@1$0#i0@1$4@2$8@1$0#k0^2^2").
Proof.
  intros x Hx. unfold low32. rewrite bv_extract_unsigned, unsigned_lit by lia.
  cbn [N.add]. rewrite Z.shiftr_0_r. unfold bv_wrap. change (bv_modulus 32) with (2^32)%Z. apply Z.mod_small. lia.
Qed.

Lemma Z_to_le_bytes_4_mod32 : ltac2:(zQ "80!hmf!ho0!h4!m0!j1!v2!vb!ho7>1z$4@3$2@1$1@1$7@1$3#8@2$0N4@2$5^1@2$6+2+i0@2$0N4^1").
Proof. intros z. apply (Z_to_le_bytes_mod 4 z 32). cbn. lia. Qed.

Lemma mod_mod_mul : ltac2:(zQ "50!j1!v2!ud!h4!hod>1a$0>1n$0>1m$0>0@2$2Z^2>0@2$2Z^2@3$3$0@2$1@2$1^5@2$4^4^3^4@2$1^5^4").
Proof.
  intros a n m Hn Hm. rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm n), Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

Lemma le4_congr : ltac2:(zQ "90!m0!j1!h4!hsd!v2!vb!hhe!ho0!ho7>1a$1>1b$1>0@3$2$1@2$4^2@2$5+2+i0@2$4^1@2$5+2+i0@3$2@1$7@1$8@1$0#8@1$3@2$6@1$0#k0^3@1$3@2$6@1$0#k0^2").
Proof.
  intros a b H. unfold le4. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^32 * 2^32)%Z.
  rewrite <- (Z_to_le_bytes_4_mod32 (a mod _)), <- (Z_to_le_bytes_4_mod32 (b mod _)).
  rewrite !mod_mod_mul by lia. rewrite H. reflexivity.
Qed.

Lemma amo_val_add_d : ltac2:(zQ "80!m0!hhe!j1!h4!ht4!hte!hu8!ho7>1a$2>1b$2@3$3@1$7@1$0#k0@4$5@1$0#k0$4@2$1@1$0#k0^2@2$1@1$0#k0^1@2$1@1$0#k0@2$6^2^1").
Proof.
  intros a b. unfold amo_val. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma amoadd_w_bytes : ltac2:(zQ "e0!m0!ho7!hi9!hsd!ho0!h4!hue!hmf!hv3!ht4!hte!hu8!hhe!ig8>1X@1$1@1$0#k0>1s@1$1@1$0#i0@3$5@1$4@1$1@1$0#8@2$7N4@2$2@1$0#i0@4$a@1$0#i0$9@4$d@1$0#k0$6@1$0#i0@1$8@1$3^2^1@1$3@2$c@1$0#k0@2$b@2$2@1$0#k0^2@2$2@1$0#i0^1").
Proof.
  intros X s. unfold amo_val. rewrite bv_add_unsigned. rewrite bv_extract_unsigned.
  cbn [N.add]. rewrite Z.shiftr_0_r. rewrite le_bytes_to_word_le4.
  transitivity (Z_to_le_bytes 4 (bv_unsigned X + bv_unsigned s)).
  - rewrite <- (Z_to_le_bytes_4_mod32 (bv_unsigned X + bv_unsigned s)). f_equal.
    change (bv_modulus 32) with (2^32)%Z.
    unfold bv_wrap. change (bv_modulus 32) with (2^32)%Z.
    rewrite (Z.mod_small (_ mod 2^32) (2^32)) by (apply Z.mod_pos_bound; lia).
    rewrite Zplus_mod_idemp_l. reflexivity.
  - unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^32 * 2^32)%Z.
    rewrite <- (Z_to_le_bytes_4_mod32 (_ mod _)). rewrite mod_mod_mul by lia. rewrite Z_to_le_bytes_4_mod32. reflexivity.
Qed.

Lemma lor_lockbit : ltac2:(zQ "80!j1!lb!h4!hu8!u8!ih6!ud!vb>1v$0>0@2$1@2$4Z^1@2$6^1@2$7+2+hf@3$2$0@2$5^2+vvvvvvvvogggggg0@2$3^2+vvvvvvvvogggggg0").
Proof.
  intros v Hv.
  assert (D : Z.land v 18446744071562067968 = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec n 31).
    - replace (Z.testbit 18446744071562067968 n) with false; [apply Bool.andb_false_r|].
      change 18446744071562067968 with (8589934591 * 2^31). rewrite Z.mul_pow2_bits by lia.
      symmetry. apply Z.testbit_neg_r. lia.
    - destruct (Z.eq_dec v 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
      rewrite (Z.bits_above_log2 v n); [reflexivity|lia|].
      apply (Z.lt_le_trans _ 31); [|lia]. apply Z.log2_lt_pow2; lia. }
  rewrite <- Z.lxor_lor by exact D. rewrite Z.add_nocarry_lxor by exact D. reflexivity.
Qed.

Lemma lockword_mod : ltac2:(zQ "90!vb!j1!v2!lb!h4!hu8!u8!ih6!ud>1v$1>0@2$3@2$6Z^1@2$8^1@2$0+2+hf@3$4$1@2$2@2$7^2+vvvvvvvvogggggg0@2$0+2+i0@2$2@2$5^2@2$0+2+hf@2$0+2+i0").
Proof.
  intros v Hv. rewrite lor_lockbit by lia.
  change 18446744071562067968 with (2^31 + 4294967295 * 2^32).
  replace (v + (2^31 + 4294967295 * 2^32)) with ((v + 2^31) + 4294967295 * 2^32) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma C4_cell_congr : ltac2:(zQ "f1!m0!j1!il8!im0!im7!imd!iqe!v2!vb!hhe!ho7!ho0!ira!h4!iv8&@3$3$2@1$5@2$9@1$0#k0^3@1$4$2>4segs@1$b$e>1m>0@1$a@1$0#k0@1$c@1$a@1$0#8>1A$1>1a$1>1b$1>0@3$d$1@2$7^2@2$8+2+i0@2$7^1@2$8+2+i0>0@4$6^6^5^4~0@4$6^7^6^5~0").
Proof.
  intros segs m A a b H C. destruct C as [[Hwf Hb] Hw].
  split; [split|]; [exact Hwf| |exact Hw].
  revert Hb. cbn [cells_bytes cbytes app]. rewrite (le4_congr a b H). exact (fun x => x).
Qed.

(* [comment removed for export] *)
Lemma lock_cell : ltac2:(zQ "h20!m0!il8!im0!im7!j1!imd!iqe!vb!hhe!ho7!ho0!ira!lb!iv8!hu8!u8!ih6!ud>4segs@1$a$d>1m>0@1$9@1$0#k0@1$b@1$9@1$0#8>1A$4>1v$4>0@2$c@2$fZ^1@2$h1^1@2$7+2+hf>0@4$6^5^4^3@3$2$1@1$5@2$8@1$0#k0@2$h0^2+vvvvvvvvogggggg0@1$3$1@4$6^6^5^4@3$2$1@1$5@2$8@1$0#k0@2$e^3@2$7+2+hf@1$3$1").
Proof. intros segs m A v Hv C. eapply C4_cell_congr; [|exact C]. apply lockword_mod. exact Hv. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac astep_core segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_cbv; simp_is_x0; simp_regs;
          first [ rewrite amo_aligned_lit by (cbn [amo_bytes]; first [assumption | lia | (Z.div_mod_to_equations; lia)])
                | match goal with |- context [amo_aligned ?wd ?a] =>
                    fail 100 "astep: cannot prove the alignment of" a "(need: P mod 4|8 = 0 and 0 <= P < 2^64 in context, address as Z_to_bv 64 P)" end
                | fail 100 "astep: no lr/sc/amo at" pc ];
          cbv beta iota zeta delta [negb];
          try (rewrite Z.eqb_refl; cbv beta iota zeta);
          simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | simp_regs; vnorm_for i; try (rewrite amoadd_w_bytes; try rewrite unsigned_lit32 by lia); try rewrite amo_val_add_d; mem_after_store_opt ]
      | None => fail "undecodable instruction at" pc
      end
  | None => fail "no instruction at" pc
  end.

(* [comment removed for export] *)
Ltac astep :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => astep_core segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

