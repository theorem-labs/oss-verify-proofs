(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import SumsLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanIMemset AsanIMemcpy AsanMemIsZero.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import MemsetLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require AsanMemset AsanMemset_code AsanMemcpyBase AsanMemcpy.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanPlanSoundSums.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_SumsAsanSpecs () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.ridx"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.caller_saved"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.regs_agree"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanPlanSoundSums.APSX.kept_ok"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "Stdlib.Lists.List.forallb"; "Corelib.Init.Datatypes.orb"; "Corelib.Init.Datatypes.negb"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_writable"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_readable"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanPlanSoundSums.APSX.segs_wr_ok"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.option"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanIMemset.align15"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.ret_ok"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.ABoot.CatSim.msteps"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.mkst"; "asanreflect_fx"; "RocqVerifyHarness.AgentSubmission.ABoot.CatExec.wbytes"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanIMemset.imemset_clob"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanPlanSoundSums.APSX.fill_spec"; "RocqVerifyHarness.AgentSubmission.ABoot.MemsetLib.cbyte"; "RocqVerifyHarness.AgentSubmission.ABoot.MemsetLib.ms_agree"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.two64"; "RocqVerifyHarness.AgentSubmission.ABoot.SumsLib.cpyH"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanIMemcpy.imemcpy_clob"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanPlanSoundSums.APSX.copy_spec"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMemIsZero.memisz_clob"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanPlanSoundSums.APSX.miz_spec"].


#[local] Notation ASEGS := AsanUbsan.M.loaded_segments (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kept_ok_of_regs_agree : ltac2:(CDefT.buildp (gd_tbl_SumsAsanSpecs ()) "Pclob,(0.(1.&5.))Pregs,(2.&5.(1.&40.))Pregs',(2.&5.(1.&40.))P,Pr,(1.&5.)P,(3.(1.&5.)R1.R4.)(3.$4.(5.R2.)$6.)P,(7.Lr,(1.&5.)(3.(1.&5.)R1.R5.)R3.R2.)(8.R4.R3.)")
(* [comment removed for export] *).
Proof. intros clob regs regs' Hsub Hag r Hr0 Hnin. apply Hag. intros Hin. apply Hnin. apply Hsub. exact Hin. Qed.

#[local] Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).

#[local] Ltac clob_sub :=
  let r := fresh "r" in let H := fresh "H" in
  intros r H; cbn [In] in H;
  repeat (destruct H as [<-|H]; [in_list|]); destruct H.

Lemma imemset_clob_sub : forall r, In r imemset_clob -> In (AX2.ridx r) AP.caller_saved.
Proof. unfold imemset_clob. clob_sub. Qed.
Lemma imemcpy_clob_sub : forall r, In r imemcpy_clob -> In (AX2.ridx r) AP.caller_saved.
Proof. unfold imemcpy_clob. clob_sub. Qed.
Lemma memisz_clob_sub : forall r, In r memisz_clob -> In (AX2.ridx r) AP.caller_saved.
Proof. unfold memisz_clob. clob_sub. Qed.
Lemma ms_clob_sub : forall r, In r ms_clob -> In (AX2.ridx r) AP.caller_saved.
Proof. unfold ms_clob. clob_sub. Qed.

(* [comment removed for export] *)
Lemma kept_ok_of_keeps : forall regs regs', keeps regs regs' -> APSX.kept_ok regs regs'.
Proof.
  intros regs regs' Hk r Hr0 Hnin. apply Hk.
  pose proof (AX2S.ridx_range r) as Hrr.
  assert (Hr : AX2.ridx r <> 0%nat).
  { intros X. apply Hr0. rewrite (APSX.reg_of_ridx r 0 X). apply bv_eq. reflexivity. }
  unfold AP.caller_saved in Hnin. cbn [In] in Hnin.
  assert (E : exists k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat /\ AX2.ridx r = k).
  { exists (AX2.ridx r). split; [|reflexivity]. cbn [In]. lia. }
  destruct E as (k & Hink & Hrk). rewrite (APSX.reg_of_ridx r k Hrk).
  cbn [In] in Hink. unfold callee_kept.
  repeat (destruct Hink as [<-|Hink]; [in_list|]). destruct Hink.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma segs_wr_of_forallb : ltac2:(CDefT.buildp (gd_tbl_SumsAsanSpecs ()) "Psegs,(0.$9.)P,(:.$;.(<.$9.Lseg,$9.(=.(>.(?.R1.))(10.R1.))R1.)$11.)(12.R2.)")
(* [comment removed for export] *).
Proof.
  intros segs H seg Hin Hw. pose proof (proj1 (forallb_forall _ _) H seg Hin) as Hs. cbn beta in Hs.
  rewrite Hw in Hs. exact Hs.
Qed.

Lemma asan_segs_wr : APSX.segs_wr_ok ASEGS.
Proof. apply segs_wr_of_forallb. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Derive.
Variable SEGS : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma fill_spec_of_imemset : ltac2:(CDefT.buildp (gd_tbl_SumsAsanSpecs ()) "Pentryw,(1.&40.)Pentry,$13.P,(:.(1.&40.)(14.&40.R1.)R2.)P,Pmem0,P,(1.&40.)(15.(1.&8.))Ps,(1.&40.)Pc,(1.&40.)Pn,$13.Prom,P,(1.&40.)(15.(1.&8.))Pregs,(2.&5.(1.&40.))Pret,(1.&40.)P,(16.=R4.)P,(17.(18.(19.&40.R7.)R5.)(1:.+2.+40.))P,(:.$;.(1;.VSEGS,R9.R8.(1<.R6.))$11.)P,P,(:.$13.(1=.R7.R9.)=)P,(1>.(:.$13.R8.=))(17.(19.&40.R:.)+100.)P,(1?.R5.)P,(:.(1.&40.)(20.R7.(21.&5.+1.$22.))R6.)P,(:.(1.&40.)(20.R8.(21.&5.+:.$22.))R<.)P,(:.(1.&40.)(20.R9.(21.&5.+;.$22.))R<.)P,(:.(1.&40.)(20.R:.(21.&5.+<.$22.))(14.&40.R<.))(23.(2.&5.(1.&40.))Lregs',(2.&5.(1.&40.))(24.(25.VSEGS,(26.$27.R<.R14.R11.R=.)(26.$27.R1.R;.(28.R11.R10.(29.(1.&8.)(14.&8.(19.&40.R?.))(1<.R>.)))R=.))(7.Lr,(1.&5.)(3.(1.&5.)R1.$2:.)R<.R1.)))(2;.VSEGS,R3.+100.)")
(* [comment removed for export] *).
Proof.
  intros entryw entry He SUM mem0 s c n regs ret Hn Hnw Hst Hc Hret R1 R10 R11 R12.
  destruct (SUM mem0 s c n (seg_rom SEGS) regs ret Hn Hnw Hst ltac:(intros; exact Hc) Hret R1 R10 R11 R12) as (regs' & Hms & Hag).
  exists regs'. rewrite He. split; [exact Hms|]. split.
  - eapply kept_ok_of_regs_agree; [apply imemset_clob_sub | exact Hag].
  - rewrite <- R10. apply Hag. unfold imemset_clob. cbn. intros [H|[H|[H|[]]]]; discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fill_spec_of_memset : ltac2:(CDefT.buildp (gd_tbl_SumsAsanSpecs ()) "Pentry,$13.P,Pmem0,P,(1.&40.)(15.(1.&8.))Pd,(1.&40.)Pcv,(1.&40.)Pret,(1.&40.)Pn,$13.Prom,P,(1.&40.)(15.(1.&8.))P,(16.=R2.)P,(17.(18.(19.&40.R6.)R3.)(1:.+2.+40.))P,(:.$;.(1;.VSEGS,R8.R7.(1<.R4.))$11.)P,(1?.R6.)Pregs,(2.&5.(1.&40.))P,(:.(1.&40.)(20.R1.(21.&5.+:.$22.))R:.)P,(:.(1.&40.)(20.R2.(21.&5.+;.$22.))R:.)P,(:.(1.&40.)(20.R3.(21.&5.+<.$22.))(14.&40.R9.))P,(:.(1.&40.)(20.R4.(21.&5.+1.$22.))R;.)(23.(2.&5.(1.&40.))Lregs',(2.&5.(1.&40.))(24.(25.VSEGS,(26.$27.R6.(14.&40.R11.)R10.R;.)(26.$27.R1.R=.(28.R10.R?.(29.(1.&8.)(2<.R>.)(1<.R<.)))R;.))(24.(:.(1.&40.)(20.R1.(21.&5.+:.$22.))R?.)(2=.R6.R1.))))(2;.VSEGS,R2.$2>.)")
(* [comment removed for export] *).
Proof.
  intros entry SUM mem0 s c n regs ret Hn Hnw Hst Hc Hret R1 R10 R11 R12.
  destruct (SUM mem0 s c ret n (seg_rom SEGS) Hn Hnw Hst Hret regs R10 R11 R12 R1) as (regs' & Hms & H10 & Hag).
  exists regs'. split; [exact Hms|]. split; [|exact H10].
  eapply kept_ok_of_regs_agree; [apply ms_clob_sub | exact Hag].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma copy_spec_of_imemcpy : ltac2:(CDefT.buildp (gd_tbl_SumsAsanSpecs ()) "Pentryw,(1.&40.)Pentry,$13.P,(:.(1.&40.)(14.&40.R1.)R2.)P,Pmem0,P,(1.&40.)(15.(1.&8.))Pdst,(1.&40.)Psrc,(1.&40.)Pn,$13.Pbs,(0.(1.&8.))Prom,P,(1.&40.)(15.(1.&8.))Pregs,(2.&5.(1.&40.))Pret,(1.&40.)P,(2?.VSEGS,R8.R7.R6.R5.R4.)P,(1?.R2.)P,(:.(1.&40.)(20.R4.(21.&5.+1.$22.))R3.)P,(:.(1.&40.)(20.R5.(21.&5.+:.$22.))R:.)P,(:.(1.&40.)(20.R6.(21.&5.+;.$22.))R:.)P,(:.(1.&40.)(20.R7.(21.&5.+<.$22.))(14.&40.R:.))(23.(2.&5.(1.&40.))Lregs',(2.&5.(1.&40.))(24.(25.VSEGS,(26.$27.R9.R12.R?.R:.)(26.$27.R1.R8.(28.R?.R>.R;.)R:.))(7.Lr,(1.&5.)(3.(1.&5.)R1.$30.)R9.R1.)))(31.VSEGS,R3.)")
(* [comment removed for export] *).
Proof.
  intros entryw entry He SUM mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
  destruct (SUM mem0 dst src n bs (seg_rom SEGS) regs ret ltac:(constructor; assumption) Hret R1 R10 R11 R12) as (regs' & Hms & Hag).
  exists regs'. rewrite He. split; [exact Hms|]. split.
  - eapply kept_ok_of_regs_agree; [apply imemcpy_clob_sub | exact Hag].
  - rewrite <- R10. apply Hag. unfold imemcpy_clob. cbn. intros [H|[H|[H|[H|[]]]]]; discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma miz_spec_of_summary : ltac2:(CDefT.buildp (gd_tbl_SumsAsanSpecs ()) "Pentryw,(1.&40.)Pentry,$13.P,(:.(1.&40.)(14.&40.R1.)R2.)P,Pmem,P,(1.&40.)(15.(1.&8.))Pbeg,(1.&40.)Psp,(1.&40.)PN,$13.Prom,P,(1.&40.)(15.(1.&8.))Pregs,(2.&5.(1.&40.))Pret,(1.&40.)P,(24.(16.=R4.)(16.R4.(1:.+2.+28.)))P,(16.(18.(18.(19.&40.R7.)R5.)+8.)(1:.+2.+40.))P,(16.+10.(19.&40.R7.))P,(:.$;.(1;.VSEGS,R:.(14.&40.(32.(19.&40.R8.)+8.))#8.)$11.)P,(33.(16.(18.(19.&40.R:.)R8.)(32.(19.&40.R9.)+8.))(16.(19.&40.R9.)(19.&40.R:.)))P,Pa,(1.&40.)P,(24.(16.(19.&40.R<.)(19.&40.R1.))(17.(19.&40.R1.)(18.(19.&40.R<.)R:.)))(:.(15.(0.(1.&8.)))(34.VSEGS,R>.R2.#1.)(35.(0.(1.&8.))(36.(1.&8.)(14.&8.=)(37.(1.&8.)))))P,(1?.R7.)P,(:.(1.&40.)(20.R9.(21.&5.+1.$22.))R8.)P,(:.(1.&40.)(20.R:.(21.&5.+2.$22.))R=.)P,(:.(1.&40.)(20.R;.(21.&5.+:.$22.))R?.)P,(:.(1.&40.)(20.R<.(21.&5.+;.$22.))(14.&40.R>.))(23.(2.&5.(1.&40.))Lregs',(2.&5.(1.&40.))(24.(25.VSEGS,(26.$27.R>.R16.R13.R?.)(26.$27.R1.R=.(28.R13.(14.&40.(32.(19.&40.R11.)+8.))(38.#8.R=.))R?.))(24.(7.Lr,(1.&5.)(3.(1.&5.)R1.$39.)R>.R1.)(24.(:.(1.&40.)(20.R1.(21.&5.+:.$22.))(14.&40.+1.))(24.(:.(1.&40.)(20.R1.(21.&5.+2.$22.))R11.)(:.(1.&40.)(20.R1.(21.&5.+1.$22.))R=.))))))(3:.VSEGS,R3.)")
(* [comment removed for export] *).
Proof.
  intros entryw entry He SUM mem beg sp N regs ret HN Hnw Hsp Hst Hdisj Hz Hret R1 R2 R10 R11.
  destruct (SUM mem beg sp N (seg_rom SEGS) regs ret HN Hnw Hsp Hst Hdisj Hz Hret R1 R2 R10 R11) as (regs' & Hms & Hag & H10 & _ & _).
  exists regs'. rewrite He. split; [exact Hms|]. split; [|exact H10].
  eapply kept_ok_of_regs_agree; [apply memisz_clob_sub | exact Hag].
Qed.
End Derive.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma asan_fill_spec_imemset : APSX.fill_spec ASEGS (AP.x_imemset AP.BOTH) 256.
Proof.
  apply (fill_spec_of_imemset _ asan_imemset_entry); [apply bv_eq; reflexivity|].
  exact asan_imemset.
Qed.

Lemma asan_fill_spec_memset : APSX.fill_spec ASEGS (AP.x_memset AP.BOTH) AX2.two64.
Proof.
  apply fill_spec_of_memset. intros mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1.
  exact (AsanMemset.memset_summary mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1).
Qed.

Lemma asan_copy_spec_imemcpy : APSX.copy_spec ASEGS (AP.x_imemcpy AP.BOTH).
Proof.
  apply (copy_spec_of_imemcpy _ asan_imemcpy_entry); [apply bv_eq; reflexivity|].
  exact asan_imemcpy.
Qed.

Lemma asan_copy_spec_memcpy : APSX.copy_spec ASEGS (AP.x_memcpy AP.BOTH).
Proof.
  intros mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
  pose proof (u64_range dst) as Hdr.
  assert (HOK : AsanMemcpyBase.mcH mem0 dst src n bs) by (constructor; try assumption; lia).
  destruct (AsanMemcpy.ref_memcpy mem0 dst src n bs (seg_rom ASEGS) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
  exists regs'. split; [replace (Z_to_bv 64 (AP.x_memcpy AP.BOTH)) with (0x0ea9c0%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
  split; [apply kept_ok_of_keeps; exact Hk|].
  rewrite <- R10. apply Hk. unfold callee_kept. in_list.
Qed.

Lemma asan_miz_spec : APSX.miz_spec ASEGS (AP.x_memiszero AP.BOTH).
Proof.
  apply (miz_spec_of_summary _ asan_mem_is_zero_entry); [apply bv_eq; reflexivity|].
  exact asan_mem_is_zero.
Qed.

