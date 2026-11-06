(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Z46Stdlib6ZArith6BinInt1Zk43addhf7Z_to_bvhfbbv_unsigned37Corelib4Init5Logicna2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Hoare4FPX1~~~~~~p33at_69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~t66v_addi37Corelib4Init9Datatypeshha6option3h5LinuxProcessSemantics5Riscv7Preludehjc5bvmapp36regsett64getrna3notp36memsetp3aregs_agreet66regupdp34assnhha4list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehqf7Segmentna3andna2ext64mkst69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~ig16mstepsp39mem_agree69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SeqExec~~~~~~il06v_jalrk44landk46modulop36ret_okna1Ip36triplehf2BVhf4BvWf" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition at_ : ltac2:(zQ "30!h9!jc!k1>4base@1$1@1$0#k0>1d$2@1$1@1$0#k0") := ltac2:(zQ "60!h9!k1!lc!m2!jc!mc\4base@1$4@1$0#k0\1d$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2^1").

Lemma at_0 : ltac2:(zQ "40!h9!jc!oe!t0>4base@1$1@1$0#k0@3$2@1$1@1$0#k0@2$3^1Z^1").
Proof.
  intros base. unfold at_. rewrite Z.add_0_r. apply bv_eq.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma at_addi : ltac2:(zQ "70!h9!k1!t0!jc!oe!hh1!lc>4base@1$3@1$0#k0>1d$1>1e$1@3$4@1$3@1$0#k0@2$5@2$2^3^2^1@2$2^3@2$6^2^1").
Proof.
  intros base d e. unfold at_, v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma at_at : ltac2:(zQ "60!t0!h9!k1!jc!oe!lc>4base@1$3@1$1#k0>1d$2>1e$2@3$4@1$3@1$1#k0@2$0@2$0^3^2^1@2$0^3@2$5^2^1").
Proof. exact at_addi. Qed.

(* [comment removed for export] *)

Lemma at_self : ltac2:(zQ "60!h9!jc!oe!lc!m2!mc>1a@1$1@1$0#k0@3$2@1$1@1$0#k0@2$4@1$0#k0@2$3@2$5@1$0#k0^1Z^1").
Proof. intros a. exact (at_0 a). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition assn : ltac2:(zQ "00T") := ltac2:(zQ "41!h9!jc!hj2!hm2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>0@2$3@1$0#5@1$1@1$0#k0>0~0>0~0P").

(* [comment removed for export] *)
Definition regset : ltac2:(zQ "00T") := ltac2:(zQ "20!h9!jc>0@1$1@1$0#5P").
Definition memset : ltac2:(zQ "00T") := ltac2:(zQ "20!h9!jc>0@1$1@1$0#k0P").

Definition regs_agree : ltac2:(zQ "40!h9!hm2!jc!hmb>1C$3>4regs@2$1@1$0#5@1$2@1$0#k0>5regs'@2$1@1$0#5@1$2@1$0#k0P") := ltac2:(zQ "70!h9!jc!hm2!hn4!oe!hnb!hmb\1C$6\4regs@2$2@1$0#5@1$1@1$0#k0\5regs'@2$2@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>0@1$5@1^4^1@3$4@1$1@1$0#k0@2$3^3^2@2$3^4^2").

Definition mem_agree : ltac2:(zQ "41!h9!jc!hj2!ho1&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1W$3>1m~0>2m'~0P") := ltac2:(zQ "61!h9!jc!hj2!oe!hnb!ho1&>0@1$1@1$0#k0@1$2@1$1@1$0#8\1W$5\1m~0\2m'~0>1x@1$1@1$0#k0>0@1$4@1^4^1@3$3@1$2@1$1@1$0#8@1^3^2@1^4^2").

Lemma regs_agree_refl : ltac2:(zQ "50!h9!hm2!hoa!hmb!jc>1C$3>4regs@2$1@1$0#5@1$4@1$0#k0@3$2^2^1^1").
Proof. intros C regs r _. reflexivity. Qed.

Lemma regs_agree_trans : ltac2:(zQ "50!h9!hm2!hoa!jc!hmb>1C$4>5regs1@2$1@1$0#5@1$3@1$0#k0>5regs2@2$1@1$0#5@1$3@1$0#k0>5regs3@2$1@1$0#5@1$3@1$0#k0>0@3$2^4^3^2>0@3$2^5^3^2@3$2^6^5^3").
Proof. intros C r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.

Lemma regs_agree_mono : ltac2:(zQ "50!h9!jc!hm2!hoa!hmb>1C$4>2C'$4>4regs@2$2@1$0#5@1$1@1$0#k0>5regs'@2$2@1$0#5@1$1@1$0#k0>0>1r@1$1@1$0#5>0@1^5^1@1^5^2>0@3$3^5^3^2@3$3^5^4^3").
Proof. intros C C' regs regs' Hsub H r Hr. apply H. intro; apply Hr, Hsub; assumption. Qed.

(* [comment removed for export] *)
Lemma regs_agree_upd : ltac2:(zQ "60!h9!jc!hm2!hoa!hmb!hp7>1C$4>4regs@2$2@1$0#5@1$1@1$0#k0>5regs'@2$2@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>1v@1$1@1$0#k0>0@1^5^2>0@3$3^6^5^4@3$3^7^6@3$5^5^4^3").
Proof.
  intros C regs regs' r v Hin H s Hs.
  rewrite getr_other by (intro Heq; subst; contradiction).
  apply H, Hs.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition triple : ltac2:(zQ "70!h9!hq0!jc!hq7!hu4!ho1!hmb>4segs@1$3$4>1C$6>1W$5>1P$1>1a@1$2@1$0#k0>1b@1$2@1$0#k0>1Q$1P") := ltac2:(zQ "f1!h9!jc!hj2!huf!hm2!hv5!hq0!hva!hq7!hu4!ija!ik4!ho1!hoa!hmb&>0@1$1@1$0#k0@1$2@1$1@1$0#8\4segs@1$8$9\1C$e\1W$c\1P$6\1a@1$1@1$0#k0\1b@1$1@1$0#k0\1Q$6>4regs@2$4@1$0#5@1$1@1$0#k0>3mem~0>3rom~0>0@3^7^3^2^1@2$5@2$4@1$0#5@1$1@1$0#k0\5regs'@2$4@1$0#5@1$1@1$0#k0@2$5~0\4mem'~0@2$3@3$a^d@5$7?2fx^6^9^5^4@5$7?2fx^2^8^1^4@2$3@3^7^2^1^4@2$3@3$d^c^6^2@3$b^b^5^1").

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
Definition ret_ok : ltac2:(zQ "20!h9!jc>1k@1$1@1$0#k0P") := ltac2:(zQ "40!h9!jc!oe!ioa\1k@1$1@1$0#k0@3$2@1$1@1$0#k0@2$3^1Z^1").

Lemma land_m2_even : ltac2:(zQ "40!k1!oe!ip4!ipb>1z$0>0@3$1$0@2$3^1+2Z@3$1$0@2$2^2-2^2").
Proof.
  intros z Hz.
  assert (Hl : Z.land z 1 = 0%Z).
  { replace 1%Z with (Z.ones 1) by reflexivity. rewrite Z.land_ones by lia. exact Hz. }
  replace (-2)%Z with (Z.lnot 1) by reflexivity.
  rewrite <- Z.ldiff_land.
  rewrite <- (Z.lor_ldiff_and z 1) at 2.
  rewrite Hl, Z.lor_0_r. reflexivity.
Qed.

Lemma ret_ok_even : ltac2:(zQ "70!h9!oe!k1!iq4!ipb!jc!mc>1k@1$5@1$0#k0>0@3$1$2@2$4@2$6@1$0#k0^1+2Z@1$3^2").
Proof.
  intros k Hk. unfold ret_ok, v_jalr, jalr_tgtZ.
  rewrite Z.add_0_r, land_m2_even by exact Hk.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Definition proc : ltac2:(zQ "70!hq0!hq7!h9!hu4!ho1!hmb!jc>4segs@1$1$3>1C$5>1W$4>1P$0>5entry@1$6@1$2#k0>1Q$0P") := ltac2:(zQ "h11!h9!jc!hj2!hq0!hq7!iqd!huf!oe!hu4!hm2!ho1!hmb!iq4!ir1!hn4!ira!irf&>0@1$1@1$0#k0@1$2@1$1@1$0#8\4segs@1$4$8\1C$b\1W$a\1P$3\5entry@1$1@1$0#k0\1Q$3>1k@1$1@1$0#k0>0@1$c^1@7$d^8^7^6\4regs@2$9@1$0#5@1$1@1$0#k0\3mem~0\3rom~0@2$6@3^8^3^2^1@3$7@1$1@1$0#k0@2$e^3@3$f@1$0#5+1Kv$5@2$h0@1$0#5+1^5^4^2^3").

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

End FPX1.
(* [comment removed for export] *)
