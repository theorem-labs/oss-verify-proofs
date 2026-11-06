(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16option3h5LinuxProcessSemantics5Riscv7Preludem25bvmap3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsp0dmachine_statek14Nonep0h3Build_machine_statek14Some3h5LinuxProcessSemantics5Riscv3Semvc4corevc6c_fcsrvc7c_fregsvc4c_pcvc6c_regsvc6c_resv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~hl12MSk14prod37Corelib4Init5Logichpb2eqp0ainterp_effp0emachine_resultvc3eff89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MStateaInterpEff0~~~~~~ht9binterp_eff0p0cMachineFaultp09MachineOkp0h0MachineUnmodeledhl1aMS_of_core01Z3h5LinuxProcessSemantics5Riscv5Instrin05instrk14boolk15falsek14listk14pair3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeira7Segmentp0afetch_wordp08is_ecallp04step3h5LinuxProcessSemantics5Riscv7DecodeCjh9adecode_anyvc4Corevc4exechl1binterp_eff0hl1blift_resulthf7Z_to_bvhpb1Ihf2BVhf4BvWfk14truevc5is_x0vc7reg_getvc2w0hl15MSsvcm29bvmap_sethpb3notvc2w146Stdlib6ZArith6BinInt1Zjt33addhf6bv_addhfbbv_unsignedhpb3andjt32lejt32ltjt33powjt36modulohf6bv_andhf6bv_nothl16ret_pc" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition Wrd64 : Type := bv 64.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition MS : ltac2:(zQ "51!h9!jc!l9!o8!s7&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1R@2$3@1$0#5@1$1@1$0#k0>1F@2$3@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>2fc@1$1@1$0#i0>2rv@1$2@1$1@1$0#k0>1m~0>2ro~0$4") := ltac2:(zQ "61!h9!jc!l9!o8!t7!te&>0@1$1@1$0#k0@1$2@1$1@1$0#8\1R@2$3@1$0#5@1$1@1$0#k0\1F@2$3@1$0#5@1$1@1$0#k0\2pc@1$1@1$0#k0\2fc@1$1@1$0#i0\2rv@1$2@1$1@1$0#k0\1m~0\2ro~0@8$5^7^6^5@1$4@1$1@1$0#k0^3^4^2^1").

Definition MSsvc : ltac2:(zQ "51!h9!jc!l9!o8!s7&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1R@2$3@1$0#5@1$1@1$0#k0>1F@2$3@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>2x8@1$1@1$0#k0>2fc@1$1@1$0#i0>2rv@1$2@1$1@1$0#k0>1m~0>2ro~0$4") := ltac2:(zQ "61!h9!jc!l9!o8!v5!te&>0@1$1@1$0#k0@1$2@1$1@1$0#8\1R@2$3@1$0#5@1$1@1$0#k0\1F@2$3@1$0#5@1$1@1$0#k0\2pc@1$1@1$0#k0\2x8@1$1@1$0#k0\2fc@1$1@1$0#i0\2rv@1$2@1$1@1$0#k0\1m~0\2ro~0@8$5^8^7^6@2$4@1$1@1$0#k0^5^3^4^2^1").

(* [comment removed for export] *)
Definition MS_of_core : ltac2:(zQ "51!h9!jc!l9!s7!hhe&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1c$4>1m~0>2ro~0$3") := ltac2:(zQ "a1!h9!jc!l9!hi5!hie!hj8!hjf!hk8!hhe!hoe&>0@1$1@1$0#k0@1$2@1$1@1$0#8\1c$8\1m~0\2ro~0@7$9@1$6^3@1$4^3@1$5^3@1$3^3@1$7^3^2^1").

(* [comment removed for export] *)

(* [comment removed for export] *)
Section InterpEff0.
Variable segs : ltac2:(zQ "20!iqc!iuf@1$0$1").
Fixpoint interp_eff0 (t : eff) (m : word -> option byte)
    : machine_result (core * (word -> option byte)) :=
  match t with
  | EDone c => MachineOk (c, m)
  | EEbreak _ | EFault _ | EDefinedIllegal _ => MachineFault   (* [comment removed for export] *)
  | EIllegal _ | EEcall _ => MachineUnmodeled
  | ELoad n a k =>
      match ov_read_bytes segs m a (width_bytes n) with
      | Some bs => interp_eff0 (k (bv_extract 0 n (le_bytes_to_word bs))) m
      | None => MachineFault
      end
  | EStore n a v k =>
      if store_ok segs m a (width_bytes n)
      then interp_eff0 k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))
      else MachineFault
  end.

Lemma interp_eff0_ok : ltac2:(zQ "a1!h9!jc!l9!hp4!hqf!hr5!hs2!hhe!ht3!ii1&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1t$8>1m~0@3$4@1$6@2$3$7~0@3$5?4segs^2^1@2$9^2^1").
Proof.
  unfold interp_eff. induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m; cbn; try reflexivity.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|reflexivity].
    rewrite <- IH. destruct (interp_eff_accesses segs _ m) as [[? ?]| |]; reflexivity.
  - destruct (store_ok segs m a (width_bytes n)); [|reflexivity].
    rewrite <- IH. destruct (interp_eff_accesses segs k _) as [[? ?]| |]; reflexivity.
Qed.
End InterpEff0.

Definition lift_result : ltac2:(zQ "71!h9!jc!l9!hs2!hp4!s7!hhe&>0@1$1@1$0#k0@1$2@1$1@1$0#8>2ro~0>1r@1$3@2$4$6~0@1$3$5") := ltac2:(zQ "b3!h9!jc!l9!hp4!hs2!s7!hhe!ij0!ijf!ikb!ilf&>0@1$1@1$0#k0@1$2@1$1@1$0#8&@2$3$6~0&@1$4~1\2ro~0\1r~2M4\1r~2@1$4$5^1\6result~1M3\6result~1@1$4$5^1\1c$6\2m'~0@2$8$5@3$a^2^1^5@1$7$5@1$9$5").

Lemma step_gen : ltac2:(zQ "ha1!h9!jc!l9!hqf!imd!ip4!v5!hp4!o8!ipd!iq4!iqc!ir3!iuf!iva!jg7!hs2!s7!jh2!jjf!jkd!jl4!hoe!jlb!jma!jn9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$b$d>1R@2$8@1$0#5@1$1@1$0#k0>1F@2$8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>2fc@1$1@1$0#i0>2rv@1$2@1$1@1$0#k0>1m~0>2ro~0>1w@1$1@1$0#i0>1i$5>2sz$4>0@3$3@1$2@1$1@1$0#i0@2$e^b^8@2$6@1$1@1$0#i0^3>0@3$3$9@1$f^4$a>0@3$3@1$2@2$7$5$4@1$h3^5@2$6@2$7$5$4@4$c$5$4^4^3@3$3@1$h0$h1@2$h2^e@7$h6^d^c^b^a^9^8^7@2$h8^7@3$h7^e@3$h5@2$h9@1$0#k0^4^5@5$h4^d^c^b^a^9^8").
Proof.
  intros segs R F pc fc rv m ro w i sz Hf He Hd.
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val MS]. rewrite Hf.
  unfold RiscvSemantics.drop_access_report, RiscvSemantics.decode_exec_accesses. rewrite He, Hd.
  cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom MS].
  rewrite <- interp_eff0_ok. unfold interp_eff.
  destruct (interp_eff_accesses segs (exec (Z_to_bv 64 sz) i _) m) as [[[c m'] acc]| |]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_ecall_gen : ltac2:(zQ "h82!h9!jc!l9!ipd!hqf!jo3!s7!o8!jo8!jod!v5!iqc!jp4!iuf!ijf!iva!jg7!hs2!jh2!jpb!jq3!jqd!hoe!jr2&>0@1$1@1$0#k0@1$2@1$1@1$0#8&@3$8@1$0#5+h1Kv$5@2$9@1$0#5+h1>4segs@1$b$d>1R@2$7@1$0#5@1$1@1$0#k0>1F@2$7@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>2fc@1$1@1$0#i0>2rv@1$2@1$1@1$0#k0>1m~0>2ro~0>1w@1$1@1$0#i0>0@3$4@1$2@1$1@1$0#i0@2$f^9^6@2$a@1$1@1$0#i0^1>0@3$4$3@1$h0^2$c@3$4@1$h1$6@2$h2^b@7$h6^a^9^8^7^6^5^4@2$e$6@8$h7^a^9^8M3\0$3@1$1@1$0#k0@1$h3~1$h5@2$h4^a~1^7^6^5^4").
Proof.
  intros segs R F pc fc rv m ro w Hf He.
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val MS]. rewrite Hf.
  unfold RiscvSemantics.drop_access_report, RiscvSemantics.decode_exec_accesses. rewrite He. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma reg_get_set_same : ltac2:(zQ "60!h9!jc!hqf!o8!jrb!jq3>1R@2$3@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>1v@1$1@1$0#k0@3$2@1$1@1$0#k0@2$5@5$4@1$0#5@1$1@1$0#k0^2^1^3^2^1").
Proof. intros. unfold reg_get. rewrite bvmap_get_set_same. reflexivity. Qed.

Lemma reg_get_set_other : ltac2:(zQ "70!h9!jc!hqf!jq3!js7!o8!jrb>1R@2$5@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>2r'@1$1@1$0#5>1v@1$1@1$0#k0>0@1$4@3$2@1$1@1$0#5^3^2@3$2@1$1@1$0#k0@2$3@5$6@1$0#5@1$1@1$0#k0^4^2^5^3@2$3^5^3").
Proof. intros. unfold reg_get. rewrite bvmap_get_set_other by assumption. reflexivity. Qed.

(* [comment removed for export] *)

Lemma w0_lit : ltac2:(zQ "50!h9!hqf!jqd!jn9!jc@3$1@1$4@1$0#k0$2@2$3@1$0#k0Z"). Proof. reflexivity. Qed.
Lemma w1_lit : ltac2:(zQ "50!h9!hqf!jse!jn9!jc@3$1@1$4@1$0#k0$2@2$3@1$0#k0+1"). Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lit_add_lit : ltac2:(zQ "70!h9!jn9!imd!jc!hqf!jub!jv2>1a$2>1b$2@3$4@1$3@1$0#k0Kd@3$6@1$0#k0@2$1@1$0#k0^2@2$1@1$0#k0^1@1$3@1$0#k0@2$1@1$0#k0@2$5^2^1").
Proof.
  intros. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma Z_to_bv_bv_unsigned : ltac2:(zQ "50!h9!jc!hqf!jn9!jvb>1x@1$1@1$0#k0@3$2@1$1@1$0#k0@2$3@1$0#k0@2$4@1$0#k0^1^1").
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma Z_to_bv_plus0 : ltac2:(zQ "60!h9!jc!hqf!jub!jn9!jvb>1x@1$1@1$0#k0@3$2@1$1@1$0#k0@2$4@1$0#k0@2$3@2$5@1$0#k0^1Z^1").
Proof. intros. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Lemma unsigned_lit : ltac2:(zQ "90!h9!imd!kg9!hqf!kh0!kh6!khc!jn9!jvb>1z$1>0@2$2@2$4Z^1@2$5^1@2$6+2+k0@3$3$1@2$8@1$0#k0@2$7@1$0#k0^2^2").
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact H. Qed.

Lemma unsigned_lit_wrap : ltac2:(zQ "70!h9!imd!hqf!ki3!khc!jn9!jvb>1z$1@3$2$1@2$6@1$0#k0@2$5@1$0#k0^1@2$3^1@2$4+2+k0").
Proof. intros. rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Definition ret_pc : ltac2:(zQ "20!h9!jc>2ra@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!jn9!jc!kid!kj6\2ra@1$2@1$0#k0@3$3@1$0#k0^1@2$4@1$0#k0@2$1@1$0#k0+1").

Lemma ret_pc_fold : ltac2:(zQ "70!h9!jc!hqf!kjf!jn9!kid!kj6>2ra@1$1@1$0#k0@3$2@1$1@1$0#k0@3$5@1$0#k0^1@2$6@1$0#k0@2$4@1$0#k0+1@1$3^1").
Proof. reflexivity. Qed.

Lemma ret_pc_even : ltac2:(zQ "b0!h9!hqf!imd!jn9!kg9!kjf!kh0!kh6!ki3!khc!jc>1z$2>0@2$4@2$6Z^1@2$7^1@2$9+2+k0>0@3$1$2@2$8^2+2Z@3$1@1$a@1$0#k0@1$5@2$3@1$0#k0^3@2$3@1$0#k0^3").
Proof.
  intros z Hz He. unfold ret_pc. apply bv_eq. rewrite bv_and_unsigned, bv_not_unsigned, !Z_to_bv_unsigned.
  rewrite !(bv_wrap_small 64 z) by (unfold bv_modulus; lia).
  change (bv_wrap 64 (Z.lnot (bv_wrap 64 1))) with (Z.ones 64 - 1)%Z.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0).
  - subst i. rewrite (Z.bit0_eqb z). replace (z mod 2)%Z with 0%Z by lia. cbn. reflexivity.
  - destruct (Z.ltb_spec0 i 64).
    + replace (Z.testbit (Z.ones 64 - 1) i) with true. { apply andb_true_r. }
      symmetry. change (Z.ones 64 - 1)%Z with (Z.shiftl (Z.ones 63) 1). rewrite Z.shiftl_spec by lia. apply Z.ones_spec_low. lia.
    + rewrite (Z.bits_above_log2 z i); [reflexivity| lia |].
      destruct (Z.eq_dec z 0). { subst. cbn. lia. }
      apply Z.lt_le_trans with 64%Z; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
(* [comment removed for export] *)
