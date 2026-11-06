(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import BothImages.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SumsLib BothIMemset BothIMemcpy BothMemIsZero.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import MemsetLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require BothMemset BothMemset_code BothMemcpyBase BothMemcpy.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanPlanSoundSums.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv36Stdlib5Lists4Listk12In3h5LinuxProcessSemantics5Riscv7Preludel95bvmap37Corelib4Init9Datatypeso74listo73nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~qcccaller_saved79OSSVerify6Proofsaboost_jsonafuzz_parse3libh1AsanPlanSoundSums4APSX~~~~~~v97kept_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~hkd4ridx69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Hoare~~~~~~hp6aregs_agree69OSSVerify6Proofsaboost_jsonafuzz_parse3libbBothIMemset~~~~~~htccimemset_clob69OSSVerify6Proofsaboost_jsonafuzz_parse3libbBothIMemcpy~~~~~~iiacimemcpy_clob69OSSVerify6Proofsaboost_jsonafuzz_parse3libdBothMemIsZero~~~~~~in8bmemisz_clob69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9MemsetLib~~~~~~is77ms_clob69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib~~~~~~jge5keeps37Corelib4Init5Logicjl62eqjl61I01Z69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~jn84getrhf2BVhf4BvWfhf7Z_to_bvhfbbv_unsignedo76optionjn84mkst46Stdlib6ZArith6BinInt1Zjv02ltjv06to_nato74boolo74truejl63andjl62exjl63not37Corelib5Lists7ListDefkja6repeat3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsklb8store_okv99fill_spechtc7align1569OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~kr56wbytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~kv96mstepshp66ret_okjv03addjv02lejv03powhkd5two64is75cbyteis78ms_agreev99copy_spec69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SumsLib~~~~~~lo44cpyHjv03subo74Someo74conso73niljl62orklbh0word_to_le_bytesv98miz_specjn83rdnqc9x_imemset69OSSVerify6Proofsaboost_jsonafuzz_parse3libaBothImages~~~~~~mha6BOTH_H69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~mm1floaded_segmentsqc8x_memsetqc9x_imemcpyqc8x_memcpyqcbx_memiszero3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypemte7Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Notation ASEGS := AsanUbsan.M.loaded_segments (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma kept_ok_of_regs_agree : ltac2:(zQ "a0!h9!jc!l4!nf!pf!q6!ua!hk3!hoe!hse>4clob@1$4@1$1@1$0#5>4regs@2$3@1$0#5@1$1@1$0#k0>5regs'@2$3@1$0#5@1$1@1$0#k0>0>1r@1$1@1$0#5>0@3$2@1$1@1$0#5^1^4@3$2$5@1$8^2$6>0@3$9\1r@1$1@1$0#5@3$2@1$1@1$0#5^1^5^3^2@2$7^4^3").
Proof. intros clob regs regs' Hsub Hag r Hr0 Hnin. apply Hag. intros Hin. apply Hnin. apply Hsub. exact Hin. Qed.
End FPX1.

#[local] Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).

#[local] Ltac clob_sub :=
  let r := fresh "r" in let H := fresh "H" in
  intros r H; cbn [In] in H;
  repeat (destruct H as [<-|H]; [in_list|]); destruct H.

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma imemset_clob_sub : ltac2:(zQ "70!h9!l4!jc!q6!ua!hoe!iha>1r@1$2@1$0#5>0@3$1@1$2@1$0#5^1$6@3$1$3@1$5^2$4").
Proof. unfold imemset_clob. clob_sub. Qed.
Lemma imemcpy_clob_sub : ltac2:(zQ "70!h9!l4!jc!q6!ua!hoe!im8>1r@1$2@1$0#5>0@3$1@1$2@1$0#5^1$6@3$1$3@1$5^2$4").
Proof. unfold imemcpy_clob. clob_sub. Qed.
Lemma memisz_clob_sub : ltac2:(zQ "70!h9!l4!jc!q6!ua!hoe!ir8>1r@1$2@1$0#5>0@3$1@1$2@1$0#5^1$6@3$1$3@1$5^2$4").
Proof. unfold memisz_clob. clob_sub. Qed.
Lemma ms_clob_sub : ltac2:(zQ "70!h9!l4!jc!q6!ua!hoe!jg3>1r@1$2@1$0#5>0@3$1@1$2@1$0#5^1$6@3$1$3@1$5^2$4").
Proof. unfold ms_clob. clob_sub. Qed.

(* [comment removed for export] *)
Lemma kept_ok_of_keeps : ltac2:(zQ "50!h9!nf!jc!hk3!jkd>4regs@2$1@1$0#5@1$2@1$0#k0>5regs'@2$1@1$0#5@1$2@1$0#k0>0@2$4^2^1@2$3^3^2").
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

End FPX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Derive.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable SEGS : ltac2:(zQ "20!pf!nh3@1$0$1").

(* [comment removed for export] *)
Lemma fill_spec_of_imemset : ltac2:(zQ "i11!h9!jc!jma!jn0!jn5!jr3!jrb!js0!nf!js7!jt1!jtf!ju8!kg8!kge!kh8!khf!ki6!kid!kj3!kl1!kp2!kpe!kqa!iha!kuf!lj2!hse!ljc!l4!lk6!lkd!ll3&>0@1$1@1$0#k0@1$b@1$1@1$0#8>6entryw@1$1@1$0#k0>5entry$4>0@3$2@1$1@1$0#k0@2$9@1$0#k0^1^2>0>4mem0~0>1s@1$1@1$0#k0>1c@1$1@1$0#k0>1n$4>3rom~0>4regs@2$8@1$0#5@1$1@1$0#k0>3ret@1$1@1$0#k0>0@2$hfZ^4>0@2$d@2$he@2$a@1$0#k0^7^5@2$i0+2+k0>0@3$2$f@4$h5?4SEGS^9^8@1$e^6$h0>0>0@3$2$4@2$h7^7^9Z>0@1$h3@3$2$4^8Z@2$d@2$a@1$0#k0^a+hg0>0@1$hc^5>0@3$2@1$1@1$0#k0@2$5^7@3$6@1$0#5+1Kv$3@2$7@1$0#5+1^6>0@3$2@1$1@1$0#k0@2$5^8@3$6@1$0#5+aKv$3@2$7@1$0#5+a^c>0@3$2@1$1@1$0#k0@2$5^9@3$6@1$0#5+bKv$3@2$7@1$0#5+b^c>0@3$2@1$1@1$0#k0@2$5^a@3$6@1$0#5+cKv$3@2$7@1$0#5+c@2$9@1$0#k0^c@2$h2@2$8@1$0#5@1$1@1$0#k0\5regs'@2$8@1$0#5@1$1@1$0#k0@2$h1@3$ha?4SEGS@5$c?2fx^c^h4^h1^d@5$c?2fx^1^b@3$h9^h1^h0@3$h4@1$1@1$0#8@2$9@1$0#8@2$a@1$0#k0^f@1$e^e^d@3$hb\1r@1$1@1$0#5@3$hd@1$1@1$0#5^1$h8^c^1@4$h6?2fx?4SEGS^3+hg0").
Proof.
  intros entryw entry He SUM mem0 s c n regs ret Hn Hnw Hst Hc Hret R1 R10 R11 R12.
  ndestruct (SUM mem0 s c n (seg_rom SEGS) regs ret Hn Hnw Hst ltac:(intros; exact Hc) Hret R1 R10 R11 R12) as (regs' & Hms & Hag).
  exists regs'. rewrite He. split; [exact Hms|]. split.
  - eapply kept_ok_of_regs_agree; [apply imemset_clob_sub | exact Hag].
  - rewrite <- R10. apply Hag. unfold imemset_clob. cbn. intros [H|[H|[H|[]]]]; discriminate.
Qed.

(* [comment removed for export] *)
Lemma fill_spec_of_memset : ltac2:(zQ "hf3!h9!jc!jma!jn0!jr3!jrb!js0!nf!jtf!ki6!jn5!ju8!kge!js7!kh8!khf!kid!kl1!kp2!kpe!lla!kuf!lj2!ljc!lm3!lmc!lk6!lkd!kg8!ll3!jt1&>0@1$1@1$0#k0@1$8@1$1@1$0#8&@3$5@1$0#5+aKv$3@2$6@1$0#5+a&@2$4^1~1>5entry$a>0>4mem0~0>1d@1$1@1$0#k0>2cv@1$1@1$0#k0>3ret@1$1@1$0#k0>1n$a>3rom~0>0@2$hbZ^2>0@2$hc@2$ha@2$he@1$0#k0^6^3@2$hd+2+k0>0@3$2$e@4$h2?4SEGS^8^7@1$c^4$f>0@1$h7^6>4regs@2$7@1$0#5@1$1@1$0#k0>0@3$2@1$1@1$0#k0~2^a>0@3$2@1$1@1$0#k0@2$4^2@3$5@1$0#5+bKv$3@2$6@1$0#5+b^a>0@3$2@1$1@1$0#k0@2$4^3@3$5@1$0#5+cKv$3@2$6@1$0#5+c@2$d@1$0#k0^9>0@3$2@1$1@1$0#k0@2$4^4@3$5@1$0#5+1Kv$3@2$6@1$0#5+1^b@2$h0@2$7@1$0#5@1$1@1$0#k0\5regs'@2$7@1$0#5@1$1@1$0#k0@2$9@3$h6?4SEGS@5$b?2fx^6@2$d@1$0#k0^h1^h0^b@5$b?2fx^1^d@3$h5^h0^f@3$h1@1$1@1$0#8@1$h8^e@1$c^c^b@2$9@3$2@1$1@1$0#k0~2^f@2$h9^6^1@4$h3?2fx?4SEGS^2$h4").
Proof.
  intros entry SUM mem0 s c n regs ret Hn Hnw Hst Hc Hret R1 R10 R11 R12.
  ndestruct (SUM mem0 s c ret n (seg_rom SEGS) Hn Hnw Hst Hret regs R10 R11 R12 R1) as (regs' & Hms & H10 & Hag).
  exists regs'. split; [exact Hms|]. split; [|exact H10].
  eapply kept_ok_of_regs_agree; [apply ms_clob_sub | exact Hag].
Qed.

(* [comment removed for export] *)
Lemma copy_spec_of_imemcpy : ltac2:(zQ "h71!h9!jc!jma!jn0!jr3!jrb!js0!nf!jtf!jn5!ju8!js7!pf!ki6!kid!ln8!im8!kuf!lj2!hse!ljc!lre!l4&>0@1$1@1$0#k0@1$8@1$1@1$0#8>6entryw@1$1@1$0#k0>5entry$9>0@3$2@1$1@1$0#k0@2$b@1$0#k0^1^2>0>4mem0~0>3dst@1$1@1$0#k0>3src@1$1@1$0#k0>1n$9>2bs@1$c@1$1@1$0#8>3rom~0>4regs@2$7@1$0#5@1$1@1$0#k0>3ret@1$1@1$0#k0>0@6$h5?4SEGS^8^7^6^5^4>0@1$h4^2>0@3$2@1$1@1$0#k0@2$4^4@3$5@1$0#5+1Kv$3@2$6@1$0#5+1^3>0@3$2@1$1@1$0#k0@2$4^5@3$5@1$0#5+aKv$3@2$6@1$0#5+a^a>0@3$2@1$1@1$0#k0@2$4^6@3$5@1$0#5+bKv$3@2$6@1$0#5+b^a>0@3$2@1$1@1$0#k0@2$4^7@3$5@1$0#5+cKv$3@2$6@1$0#5+c@2$b@1$0#k0^a@2$e@2$7@1$0#5@1$1@1$0#k0\5regs'@2$7@1$0#5@1$1@1$0#k0@2$d@3$h2?4SEGS@5$a?2fx^9^h2^f^a@5$a?2fx^1^8@3$h1^f^e^b^a@3$h3\1r@1$1@1$0#5@3$h6@1$1@1$0#5^1$h0^9^1@3$f?2fx?4SEGS^3").
Proof.
  intros entryw entry He SUM mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
  ndestruct (SUM mem0 dst src n bs (seg_rom SEGS) regs ret ltac:(constructor; assumption) Hret R1 R10 R11 R12) as (regs' & Hms & Hag).
  exists regs'. rewrite He. split; [exact Hms|]. split.
  - eapply kept_ok_of_regs_agree; [apply imemcpy_clob_sub | exact Hag].
  - rewrite <- R10. apply Hag. unfold imemcpy_clob. cbn. intros [H|[H|[H|[H|[]]]]]; discriminate.
Qed.

(* [comment removed for export] *)
Lemma miz_spec_of_summary : ltac2:(zQ "i54!h9!jc!jt1!jma!jn0!jr3!lkd!jrb!js0!ki6!js7!lk6!jtf!nf!ls6!pf!jn5!ju8!ll3!lsd!kh8!lt4!ltb!khf!kid!lu1!kp2!lu7!lvc!ir8!kuf!lj2!hse!ljc!mg7!l4!kg8&>0@1$1@1$0#k0@1$c@1$1@1$0#8&@3$7@1$0#5+1Kv$4@2$8@1$0#5+1&@3$7@1$0#5+2Kv$4@2$8@1$0#5+2&@3$7@1$0#5+aKv$4@2$8@1$0#5+a>6entryw@1$1@1$0#k0>5entry$h0>0@3$3@1$1@1$0#k0@2$a@1$0#k0^1^2>0>3mem~0>3beg@1$1@1$0#k0>2sp@1$1@1$0#k0>1N$h0>3rom~0>4regs@2$d@1$0#5@1$1@1$0#k0>3ret@1$1@1$0#k0>0@2$9@2$6Z^4@2$6^4@2$h2+2+i8>0@2$6@2$b@2$b@2$2@1$0#k0^7^5+8@2$h2+2+k0>0@2$6+h0@2$2@1$0#k0^7>0@3$3$h4@4$ha?4SEGS^a@2$a@1$0#k0@2$e@2$2@1$0#k0^8+8N8$h7>0@2$h9@2$6@2$b@2$2@1$0#k0^a^8@2$e@2$2@1$0#k0^9+8@2$6@2$2@1$0#k0^9@2$2@1$0#k0^a>0>1a@1$1@1$0#k0>0@2$9@2$6@2$2@1$0#k0^c@2$2@1$0#k0^1@2$i4@2$2@1$0#k0^1@2$b@2$2@1$0#k0^c^a@3$3@1$c@1$f@1$1@1$0#8@4$i2?4SEGS^e^2N1@2$h3@1$f@1$1@1$0#8@3$h5@1$1@1$0#8@2$a@1$0#8Z@1$h6@1$1@1$0#8>0@1$i1^7>0@3$3@1$1@1$0#k0@2$5^9~1^8>0@3$3@1$1@1$0#k0@2$5^a~2^d>0@3$3@1$1@1$0#k0@2$5^b~3^f>0@3$3@1$1@1$0#k0@2$5^c@3$7@1$0#5+bKv$4@2$8@1$0#5+b@2$a@1$0#k0^e@2$h8@2$d@1$0#5@1$1@1$0#k0\5regs'@2$d@1$0#5@1$1@1$0#k0@2$9@3$hf?4SEGS@5$h1?2fx^e^h6^h3^f@5$h1?2fx^1^d@3$he^h3@2$a@1$0#k0@2$e@2$2@1$0#k0^h1+8@2$hbN8^d^f@2$9@3$i0\1r@1$1@1$0#5@3$i3@1$1@1$0#5^1$hd^e^1@2$9@3$3@1$1@1$0#k0@2$5^1~3@2$a@1$0#k0+1@2$9@3$3@1$1@1$0#k0@2$5^1~2^h1@3$3@1$1@1$0#k0@2$5^1~1^d@3$hc?2fx?4SEGS^3").
Proof.
  intros entryw entry He SUM mem beg sp N regs ret HN Hnw Hsp Hst Hdisj Hz Hret R1 R2 R10 R11.
  ndestruct (SUM mem beg sp N (seg_rom SEGS) regs ret HN Hnw Hsp Hst Hdisj Hz Hret R1 R2 R10 R11) as (regs' & Hms & Hag & H10 & _ & _).
  exists regs'. rewrite He. split; [exact Hms|]. split; [|exact H10].
  eapply kept_ok_of_regs_agree; [apply memisz_clob_sub | exact Hag].
Qed.
End Derive.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX3. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma asan_fill_spec_imemset : ltac2:(zQ "40!mge!kpe!ml7!mpb@4$1?2fx$3@1$0$2+hg0").
Proof.
  apply (fill_spec_of_imemset _ asan_imemset_entry); [apply bv_eq; reflexivity|].
  exact asan_imemset.
Qed.

Lemma asan_fill_spec_memset : ltac2:(zQ "50!mqe!kpe!lla!ml7!mpb@4$1?2fx$4@1$0$3$2").
Proof.
  apply fill_spec_of_memset. intros mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1.
  exact (BothMemset.memset_summary mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1).
Qed.

Lemma asan_copy_spec_imemcpy : ltac2:(zQ "40!mr9!ln8!ml7!mpb@3$1?2fx$3@1$0$2").
Proof.
  apply (copy_spec_of_imemcpy _ asan_imemcpy_entry); [apply bv_eq; reflexivity|].
  exact asan_imemcpy.
Qed.

Lemma asan_copy_spec_memcpy : ltac2:(zQ "40!ms5!ln8!ml7!mpb@3$1?2fx$3@1$0$2").
Proof.
  intros mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
  pose proof (u64_range dst) as Hdr.
  assert (HOK : BothMemcpyBase.mcH mem0 dst src n bs) by (constructor; try assumption; lia).
  ndestruct (BothMemcpy.ref_memcpy mem0 dst src n bs (seg_rom ASEGS) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
  exists regs'. split; [replace (Z_to_bv 64 (AP.x_memcpy ASAN_H)) with (0x1a239c%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
  split; [apply kept_ok_of_keeps; exact Hk|].
  rewrite <- R10. apply Hk. unfold callee_kept. in_list.
Qed.

Lemma asan_miz_spec : ltac2:(zQ "40!mt0!lvc!ml7!mpb@3$1?2fx$3@1$0$2").
Proof.
  apply (miz_spec_of_summary _ asan_mem_is_zero_entry); [apply bv_eq; reflexivity|].
  exact asan_mem_is_zero.
Qed.

End FPX3.
(* [comment removed for export] *)
