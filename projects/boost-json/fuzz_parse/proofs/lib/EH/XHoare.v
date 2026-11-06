(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Z46Stdlib6ZArith6BinInt1Zk43addhf7Z_to_bvhfbbv_unsigned37Corelib4Init5Logicna2eq89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6XHoare7WithFP1~~~~~~p33at_79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~td6v_addi3h5LinuxProcessSemantics5Riscv7Preludehi55bvmapp36regsettd4getrna3notp3aregs_agreetd6regupd79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XSeqExec~~~~~~ho06v_jalrk44landk46modulop36ret_ok" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition at_ : ltac2:(zQ "30!h9!jc!k1>4base@1$1@1$0#k0>1d$2@1$1@1$0#k0") := ltac2:(zQ "60!h9!k1!lc!m2!jc!mc\4base@1$4@1$0#k0\1d$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2^1").

Lemma at_0 : ltac2:(zQ "40!h9!jc!oe!t7>4base@1$1@1$0#k0@3$2@1$1@1$0#k0@2$3^1Z^1").
Proof.
  intros base. unfold at_. rewrite Z.add_0_r. apply bv_eq.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma at_addi : ltac2:(zQ "70!h9!k1!t7!jc!oe!hhc!lc>4base@1$3@1$0#k0>1d$1>1e$1@3$4@1$3@1$0#k0@2$5@2$2^3^2^1@2$2^3@2$6^2^1").
Proof.
  intros base d e. unfold at_, v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma at_at : ltac2:(zQ "60!t7!h9!k1!jc!oe!lc>4base@1$3@1$1#k0>1d$2>1e$2@3$4@1$3@1$1#k0@2$0@2$0^3^2^1@2$0^3@2$5^2^1").
Proof. exact at_addi. Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition regset : ltac2:(zQ "00T") := ltac2:(zQ "20!h9!jc>0@1$1@1$0#5P").

Definition regs_agree : ltac2:(zQ "40!h9!hkb!jc!hl4>1C$3>4regs@2$1@1$0#5@1$2@1$0#k0>5regs'@2$1@1$0#5@1$2@1$0#k0P") := ltac2:(zQ "70!h9!jc!hkb!hld!oe!hm4!hl4\1C$6\4regs@2$2@1$0#5@1$1@1$0#k0\5regs'@2$2@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>0@1$5@1^4^1@3$4@1$1@1$0#k0@2$3^3^2@2$3^4^2").

Lemma regs_agree_refl : ltac2:(zQ "50!h9!hkb!hma!hl4!jc>1C$3>4regs@2$1@1$0#5@1$4@1$0#k0@3$2^2^1^1").
Proof. intros C regs r _. reflexivity. Qed.

Lemma regs_agree_trans : ltac2:(zQ "50!h9!hkb!hma!jc!hl4>1C$4>5regs1@2$1@1$0#5@1$3@1$0#k0>5regs2@2$1@1$0#5@1$3@1$0#k0>5regs3@2$1@1$0#5@1$3@1$0#k0>0@3$2^4^3^2>0@3$2^5^3^2@3$2^6^5^3").
Proof. intros C r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.

(* [comment removed for export] *)
Lemma regs_agree_upd : ltac2:(zQ "60!h9!jc!hkb!hma!hl4!hn7>1C$4>4regs@2$2@1$0#5@1$1@1$0#k0>5regs'@2$2@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>1v@1$1@1$0#k0>0@1^5^2>0@3$3^6^5^4@3$3^7^6@3$5^5^4^3").
Proof.
  intros C regs regs' r v Hin H s Hs.
  rewrite getr_other by (intro Heq; subst; contradiction).
  apply H, Hs.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ret_ok : ltac2:(zQ "20!h9!jc>1k@1$1@1$0#k0P") := ltac2:(zQ "40!h9!jc!oe!hre\1k@1$1@1$0#k0@3$2@1$1@1$0#k0@2$3^1Z^1").

Lemma land_m2_even : ltac2:(zQ "40!k1!oe!hs8!hsf>1z$0>0@3$1$0@2$3^1+2Z@3$1$0@2$2^2-2^2").
Proof.
  intros z Hz.
  assert (Hl : Z.land z 1 = 0%Z).
  { replace 1%Z with (Z.ones 1) by reflexivity. rewrite Z.land_ones by lia. exact Hz. }
  replace (-2)%Z with (Z.lnot 1) by reflexivity.
  rewrite <- Z.ldiff_land.
  rewrite <- (Z.lor_ldiff_and z 1) at 2.
  rewrite Hl, Z.lor_0_r. reflexivity.
Qed.

Lemma ret_ok_even : ltac2:(zQ "70!h9!oe!k1!ht8!hsf!jc!mc>1k@1$5@1$0#k0>0@3$1$2@2$4@2$6@1$0#k0^1+2Z@1$3^2").
Proof.
  intros k Hk. unfold ret_ok, v_jalr, jalr_tgtZ.
  rewrite Z.add_0_r, land_m2_even by exact Hk.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP1.

(* [comment removed for export] *)
