(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep CXXLib CXXLib2 AsObj AsWalk N8Kit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~jb6fframe37Corelib4Init5Logico13andjb7ff_addr46Stdlib6ZArith6BinInt1Zq53addq52leo12exjb8ff_classjb3fsz36Stdlib5Lists4Listte2Injb5block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5AsObj~~~~~~ve4aobj89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA6AXpres1K~~~~~~hk07inframehc4cons79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AsCXXHeap~~~~~~hp15fsobjjb6as_FSBjb7AFS_HDRjb8AFS_SIZE79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hv78AIMG_TOPjb6as_RFSjb3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~ikd4aappikd5aceiljb8blk_addro12orjb8as_RHEAPjb5as_Stjb8blk_sizejbdaclient_rangeikd3nshikd2shhc4prodhc3fsthc3snd37Corelib5Lists7ListDefiva6Forall79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As6CXXRep~~~~~~jhbdxclient_rangeikdbaddressablejhb5xpresjb5apreshc4pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsConst~~~~~~jof9aconst_okjbh0aclient_write_okjbcafs_write_okjb3asrjbcasan_rt_hyps" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section K.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!jvc$0").
  Hypothesis HH : ltac2:(zQ "10!kg2@2$0?5HCEIL?1H").

  Definition inframe : ltac2:(zQ "30!h9!j4!n8>2LF@1$1$2>1A$0>1n$0P") := ltac2:(zQ "b0!n8!p5!h9!pb!rd!s3!j4!s8!sd!t8!v1\2LF@1$6$0\1A$2\1n$2@2$7$0\1f$0@2$1@3$a$0^1^4@2$1@2$5@1$3^1^3@2$5@2$4^3^2@2$4@1$3^1@1$9@1$8^1").

  Lemma inframe_aobj : ltac2:(zQ "60!j4!h9!v6!n8!hj9!hnf>2LB@1$0$2>2LF@1$0$3>1A$1>1n$1>0@3$5^3^2^1@4$4^5^4^3^2").
  Proof. intros LB LF A n K. right. exact K. Qed.
  Lemma inframe_sub : ltac2:(zQ "60!h9!hnf!rd!s3!j4!n8>2LF@1$4$5>1A$0>1n$0>2A'$0>2n'$0>0@3$1^5^4^3>0@2$3^5^3>0@2$3@2$2^4^3@2$2^6^5@3$1^8^5^4").
  Proof. (intros LF A n A' n' nd_i1 L1 L2; ndestruct nd_i1 as (f & Hf & H1 & H2)). exists f. split; [exact Hf| lia]. Qed.
  Lemma inframe_LF_mono : ltac2:(zQ "50!n8!j4!h9!hnf!v1>2LF@1$1$0>3LF'@1$1$0>1A$2>1n$2>0@3$3^4^2^1>0>1f$0>0@3$4$0^1^6@3$4$0^2^6@3$3^5^4^3").
  Proof. (intros LF LF' A n nd_i2 HL; ndestruct nd_i2 as (f & Hf & H1 & H2)). exists f. split; [apply HL; exact Hf| lia]. Qed.
  Lemma inframe_cons : ltac2:(zQ "50!n8!h9!hnf!hoa!j4>2LF@1$4$0>1g$0>1A$1>1n$1>0@3$2^4^2^1@3$2@3$3$0^4^5^3^2").
  Proof. intros LF g A n K. eapply inframe_LF_mono; [exact K| intros; right; assumption]. Qed.
  Lemma inframe_fsobj : ltac2:(zQ "50!h9!j4!ht0!n8!hnf>2LF@1$1$3>1A$0>1n$0>0@3$4^3^2^1@4$2?1H^4^3^2").
  Proof. (intros LF A n nd_i3; ndestruct nd_i3 as (f & Hf & H1 & H2)). right. exists f. auto. Qed.

  (* [comment removed for export] *)
  Lemma inframe_range : ltac2:(zQ "f0!rd!p5!s3!ht9!h9!hu2!huc!j4!ij2!ije!n8!ik7!iob!ip3!hnf>2LF@1$7$a>2m1$b>1A$4>1n$4>0@3$9?1H^4^3>0@3$e^5^3^2@2$1@2$2@2$0$8$5^4@2$1@2$2@2$0^4^3@1$d?5HCEIL@2$1@2$2@2$0@1$3?1H$5^4@2$1@2$2@2$0^4^3@2$0@1$3?1H$6@3$c?5HCEIL@1$3?1H$6").
  Proof.
    (intros LF m1 A n RF nd_i4; ndestruct nd_i4 as (f & Hf & H1 & H2)).
    pose proof (proj2 (ah_RFS_range H HH _ _ RF) f Hf) as (K & Q1 & Q2 & Q3 & Q4). pose proof (proj1 (ah_RFS_range H HH _ _ RF)) as (F1 & F2 & F3 & F4).
    unfold AFS_HDR, AFS_SIZE in *. lia.
  Qed.
  Lemma inframe_aapp : ltac2:(zQ "80!h9!j4!ije!n8!ik7!iob!hnf!s3>2LF@1$1$3>2m1$4>1A$0>1n$0>0@3$2?1H^4^3>0@3$6^5^3^2>0@2$7Z^3@3$5?5HCEIL^5^4").
  Proof.
    intros LF m1 A n RF IFR Hn. pose proof (inframe_range _ _ _ _ RF IFR) as (R1 & R2 & R3 & R4 & R5).
    eapply aapp_sub; [exact R5| unfold AFS_HDR in *; lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma inframe_block_disjoint : ltac2:(zQ "f0!rd!v6!j4!h9!ipc!ik7!s3!iq7!ije!iqc!ir7!irf!n8!hnf!v1>1s@1$a?1H>2LB@1$2$1>1m$5>2LF@1$2$c>2m1$5>1A$3>1n$3>1b$1>0@4$9?1H^8^7^6>0@3$8?1H^6^5>0@3$d^7^5^4>0@3$e$1^4^a@2$7@2$6@2$0@2$0^7^6+h0@1$4^5@2$6@2$0@2$0@1$4^5@1$b^5+h0^7").
  Proof.
    (intros s LB m LF m1 A n b RH RF nd_i5 Hb; ndestruct nd_i5 as (f & Hf & H1 & H2)).
    pose proof (ah_blocks H HH _ _ _ b RH Hb) as (_ & _ & R3 & _ & _ & R6 & _).
    pose proof (proj2 (ah_RFS_range H HH _ _ RF) f Hf) as (K & Q1 & Q2 & Q3 & Q4).
    unfold AFS_HDR in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma aobj_sh_client_range : ltac2:(zQ "d0!h9!j4!ik7!isa!ije!iqc!ir7!v6!n8!hj9!ita!iu1!s3>1s@1$6?1H>2LB@1$1$7>1m$2>2LF@1$1$8>2m1$2>2SP$0>1A$0>1n$0>0@4$5?1H^8^7^6>0@3$4?1H^6^5>0@4$9^9^7^4^3>0@2$cZ^4@6$3?5HCEIL?1H^b^7@1$b^6@1$a^5").
  Proof.
    intros s LB m LF m1 SP A n RH RF AO Hn. destruct AO as [(b & Hb & H1 & H2)|(f & Hf & H1 & H2)].
    - right; right; right; left. exists b. split; [exact Hb|].
      pose proof (ah_blocks H HH _ _ _ b RH Hb) as (_ & R2 & R3 & R4 & R5 & _).
      split; [apply sh_mono; lia|]. unfold sh, nsh in *. Z.div_mod_to_equations. lia.
    - pose proof (proj2 (ah_RFS_range H HH _ _ RF) f Hf) as (K & R1 & R2 & R3 & R4); pose proof (proj1 (ah_RFS_range H HH _ _ RF)) as (F1 & F2 & F3).
      right; right; right; right; right; left. unfold AFS_HDR in *.
      split; [apply sh_mono; lia|]. unfold AFS_SIZE, sh, nsh in *. Z.div_mod_to_equations. lia.
  Qed.
  Lemma aobj_sh_xclient_range : ltac2:(zQ "h30!h9!j4!iu7!iu1!s3!ik7!ita!iue!iv4!iq7!jh1!ije!iqc!ir7!v6!n8!hj9!jl7!rd>1s@1$d?1H>2LB@1$1$e>1m$5>2LF@1$1$f>2m1$5>2SP$0>1X@1$1@2$2$0$0>1A$0>1n$0>0@4$c?1H^9^8^7>0@3$b?1H^7^6>0@4$h0^a^8^4^3>0@2$4Z^4>0@3$a@2$2$0$0\2iv@2$2$0$0@2$9@2$4@2$h2@1$3^7@1$6^6@3$7$0$0^1@2$4@3$8$0$0^1@1$3^7^7@7$h1?5HCEIL?1H^d^9^8@1$3^7@1$6^6").
  Proof. intros s LB m LF m1 SP X A n RH RF AO Hn FX. split; [eapply aobj_sh_client_range; eauto| exact FX]. Qed.

  (* [comment removed for export] *)
  Lemma aobj_xpres_addressable : ltac2:(zQ "h40!h9!ik7!j4!iu7!jm8!iu1!s3!iue!iv4!iq7!jh1!ije!iqc!ir7!v6!n8!hj9!ita!jn7!rd>1s@1$d?1H>2LB@1$2$e>2m0$1>2LF@1$2$f>2m1$1>2SP$0>1X@1$2@2$3$0$0>1m$1>2m'$1>1A$0>1n$0>0@4$c?1H^b^a^9>0@3$b?1H^9^8>0@4$h0^c^a^4^3>0@7$h2?5HCEIL?1H^d^9^8^7^6>0@3$4^8^6^5>0@3$a@2$3$0$0\2iv@2$3$0$0@2$9@2$6@2$h3@1$5^8@1$h1^7@3$7$0$0^1@2$6@3$8$0$0^1@1$5^8^a@3$4^9^8^7").
  Proof.
    intros s LB m0 LF m1 SP X m m' A n RH RF AO XP AD FX. pose proof AD as [Hn _].
    eapply xpres_addressable; [exact XP| exact AD|]. eapply aobj_sh_xclient_range; eauto.
  Qed.
  (* [comment removed for export] *)
  Lemma aobj_apres_addressable : ltac2:(zQ "b0!ik7!h9!j4!jm8!jo0!ije!iqc!ir7!v6!n8!hj9>1s@1$7?1H>2LB@1$2$8>2m0$0>2LF@1$2$9>2m1$0>2SP$1>1m$0>2m'$0>1A$1>1n$1>0@4$6?1H^a^9^8>0@3$5?1H^8^7>0@4$a^b^9^4^3>0@6$4?5HCEIL?1H^c^8^7^6>0@3$3^8^6^5@3$3^8^7^6").
  Proof.
    intros s LB m0 LF m1 SP m m' A n RH RF AO AP AD.
    eapply aobj_xpres_addressable with (X := []); [exact RH| exact RF| exact AO| apply xpres_of_apres; exact AP| exact AD| apply Forall_nil].
  Qed.

  Lemma inframe_window_ok : ltac2:(zQ "h00!h9!rd!jo8!j4!p5!ik7!s3!jsc!jt9!jud!ije!iqc!ir7!v6!n8!hnf>1s@1$c?1H>2LB@1$3$d>1m$5>2LF@1$3$e>2m1$5>1A$0>1n$0>1a$0>1k$0>0@4$b?1H^9^8^7>0@3$a?1H^7^6>0@3$f^8^6^5>0@2$6^7^5>0@2$6@2$1^6^5@2$1^8^7@2$4@4$8?5HCEIL?1H^d@4$2$0$0^7@2$1^7^6@2$4@3$9?1H^b@4$2$0$0^7@2$1^7^6@1$7@4$2$0$0^7@2$1^7^6").
  Proof.
    intros s LB m LF m1 A n a k RH RF IFR H1 H2.
    eapply aobj_write_ok; [exact HH| exact RH| exact RF|]. eapply aobj_sub; [apply inframe_aobj; exact IFR| lia| lia].
  Qed.
End K.
