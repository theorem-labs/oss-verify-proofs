(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XHoare XRefMemcpyLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XMemsetLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XAxSymExec3Sound XAxSymRun3 XAsanPlanCore XAsanPlan XSegLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XSegLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv36Stdlib5Lists4Listk12In3h5LinuxProcessSemantics5Riscv7Preludel95bvmap37Corelib4Init9Datatypeso74listo73nat89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XAsanPlan2AP~~~~~~qcccaller_saved89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~vd4ridx79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6XHoare~~~~~~hk9aregs_agree89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegLib4APSX~~~~~~hp37kept_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHaXMemsetLib~~~~~~hu07ms_clob79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHdXRefMemcpyLib~~~~~~iib5keeps37Corelib4Init5Logicin72eqin71I79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~ip64getrhf2BVhf4BvWfo76optionin73and01Zip64mkst46Stdlib6ZArith6BinInt1Zjg46to_nathf7Z_to_bvo74boolo74truein72ex37Corelib5Lists7ListDefjk46repeat3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjm58store_okvd5two6479OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XCatExec~~~~~~jr06wbytes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XCatSim~~~~~~jv86mstepshk96ret_okhu05cbytehu08ms_agreehp39fill_specjg43addjg42lejg42ltjg43powhfbbv_unsigned3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypekp37Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kept_ok_of_regs_agree : ltac2:(zQ "a0!h9!jc!l4!nf!pf!q6!ue!hk2!ho5!ht5>4clob@1$4@1$1@1$0#5>4regs@2$3@1$0#5@1$1@1$0#k0>5regs'@2$3@1$0#5@1$1@1$0#k0>0>1r@1$1@1$0#5>0@3$2@1$1@1$0#5^1^4@3$2$5@1$7^2$6>0@3$8\1r@1$1@1$0#5@3$2@1$1@1$0#5^1^5^3^2@2$9^4^3").
Proof. intros clob regs regs' Hsub Hag r Hr0 Hnin. apply Hag. intros Hin. apply Hnin. apply Hsub. exact Hin. Qed.

Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).

Ltac clob_sub :=
  let r := fresh "r" in let H := fresh "H" in
  intros r H; cbn [In] in H;
  repeat (destruct H as [<-|H]; [in_list|]); destruct H.

Lemma ms_clob_sub : ltac2:(zQ "70!h9!l4!jc!q6!ue!hk2!ii0>1r@1$2@1$0#5>0@3$1@1$2@1$0#5^1$6@3$1$3@1$5^2$4").
Proof. unfold ms_clob. clob_sub. Qed.

(* [comment removed for export] *)
Lemma kept_ok_of_keeps : ltac2:(zQ "50!h9!nf!jc!ime!ht5>4regs@2$1@1$0#5@1$2@1$0#k0>5regs'@2$1@1$0#5@1$2@1$0#k0>0@2$3^2^1@2$4^3^2").
Proof.
  intros regs regs' Hk r Hr0 Hnin. apply Hk.
  pose proof (AX2S.ridx_range r) as Hrr.
  assert (Hr : AX2.ridx r <> 0%nat).
  { intros X. apply Hr0. rewrite (APSX.reg_of_ridx r 0 X). apply bv_eq. reflexivity. }
  unfold AP.caller_saved in Hnin. cbn [In] in Hnin.
  assert (E : exists k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat /\ AX2.ridx r = k).
  { exists (AX2.ridx r). split; [|reflexivity]. cbn [In]. lia. }
  ndestruct E as (k & Hink & Hrk). rewrite (APSX.reg_of_ridx r k Hrk).
  cbn [In] in Hink. unfold callee_kept.
  repeat (destruct Hink as [<-|Hink]; [in_list|]). destruct Hink.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Derive.
Context {fx : XPropExec.FPState}.
Variable SEGS : ltac2:(zQ "20!pf!ks8@1$0$1").

(* [comment removed for export] *)
Lemma fill_spec_of_memset : ltac2:(zQ "hf3!h9!jc!iob!ip1!it5!itd!iu2!nf!iu9!iv2!iv9!ivc!jhc!ji6!jj0!jj7!jje!jlb!jpc!jq8!jue!kj5!kjf!kk9!kl2!kle!kmb!kn2!kn8!kne!ko5&>0@1$1@1$0#k0@1$8@1$1@1$0#8&@3$5@1$0#5+aKv$3@2$6@1$0#5+a&@2$4^1~1>5entry$a>0>4mem0~0>1d@1$1@1$0#k0>2cv@1$1@1$0#k0>3ret@1$1@1$0#k0>1n$a>3rom~0>0@2$hbZ^2>0@2$hc@2$ha@2$he@1$0#k0^6^3@2$hd+2+k0>0@3$2$e@4$h2?4SEGS^8^7@1$c^4$f>0@1$h6^6>4regs@2$7@1$0#5@1$1@1$0#k0>0@3$2@1$1@1$0#k0~2^a>0@3$2@1$1@1$0#k0@2$4^2@3$5@1$0#5+bKv$3@2$6@1$0#5+b^a>0@3$2@1$1@1$0#k0@2$4^3@3$5@1$0#5+cKv$3@2$6@1$0#5+c@2$d@1$0#k0^9>0@3$2@1$1@1$0#k0@2$4^4@3$5@1$0#5+1Kv$3@2$6@1$0#5+1^b@2$h0@2$7@1$0#5@1$1@1$0#k0\5regs'@2$7@1$0#5@1$1@1$0#k0@2$9@3$h5?4SEGS@5$b?2fx^6@2$d@1$0#k0^h1^h0^b@5$b?2fx^1^d@3$h4^h0^f@3$h1@1$1@1$0#8@1$h7^e@1$c^c^b@2$9@3$2@1$1@1$0#k0~2^f@2$h8^6^1@4$h9?2fx?4SEGS^2$h3").
Proof.
  intros entry SUM mem0 s c n regs ret Hn Hnw Hst Hc Hret R1 R10 R11 R12.
  ndestruct (SUM mem0 s c ret n (seg_rom SEGS) Hn Hnw Hst Hret regs R10 R11 R12 R1) as (regs' & Hms & H10 & Hag).
  exists regs'. split; [exact Hms|]. split; [|exact H10].
  eapply kept_ok_of_regs_agree; [apply ms_clob_sub | exact Hag].
Qed.
End Derive.

